<#
.SYNOPSIS
  Loop-engineering driver: runs fresh headless Claude sessions (default model: haiku), one task per
  iteration, and keeps the repository monotonically green.

.DESCRIPTION
  Each iteration:
    1. feeds loop/PROMPT.md to `claude -p --model <Model>` (fresh context every time)
    2. restores any protected file the agent touched (harness/, loop/PROMPT.md, this script, CLAUDE.md)
    3. auto-commits leftover changes, then runs the full gate:
         python harness/check.py --gate --update-best
       - pass  -> baseline (harness/results/best.json) updated and committed
       - fail  -> the iteration's commits are saved on branch rejected/iter-NNN, HEAD is reset to the
                  pre-iteration commit, and loop/LAST_REJECTED.md explains why (next iteration reads it)
    4. stops after -MaxNoProgress iterations without a commit touching crates/, or when loop/STOP exists.

.EXAMPLE
  pwsh -File loop/run-loop.ps1                         # haiku, up to 100 iterations
  pwsh -File loop/run-loop.ps1 -MaxIterations 5 -IterationTimeoutMin 30
  New-Item loop/STOP                                   # graceful stop after the current iteration
#>
param(
    [int]$MaxIterations = 100,
    [string]$Model = "haiku",
    [int]$IterationTimeoutMin = 45,
    [int]$MaxNoProgress = 4,
    [double]$MaxBudgetUsdPerIter = 0,
    [switch]$NoGate
)

$ErrorActionPreference = "Continue"
$Root = Split-Path -Parent $PSScriptRoot
Set-Location $Root
$env:PATH = "$env:USERPROFILE\.cargo\bin;$env:PATH"
$env:PYTHONUTF8 = "1"
$Logs = Join-Path $Root "loop\logs"
New-Item -ItemType Directory -Force $Logs | Out-Null
$DriverLog = Join-Path $Logs "driver.log"
$PromptFile = Join-Path $Root "loop\PROMPT.md"
$Rejected = Join-Path $Root "loop\LAST_REJECTED.md"

# Paths the agent must never change (restored from the pre-iteration commit if touched).
$Protected = @(
    "harness/golden", "harness/golden_count", "harness/java-oracle/src", "harness/common.py",
    "harness/check.py", "harness/corpus.py", "harness/gen_golden.py", "harness/setup.py",
    "harness/corpus.json", "harness/quick.txt", "harness/SCHEMA.md",
    "loop/PROMPT.md", "loop/run-loop.ps1", "CLAUDE.md", ".claude/settings.json"
)

function Log([string]$m) {
    $line = "[{0}] {1}" -f (Get-Date -Format "yyyy-MM-dd HH:mm:ss"), $m
    Write-Host $line
    Add-Content -Path $DriverLog -Value $line -Encoding utf8
}

function Git([string[]]$a) { & git @a 2>&1 }

function Score() {
    $h = Join-Path $Root "harness\results\history.csv"
    if (-not (Test-Path $h)) { return "-" }
    $last = Get-Content $h | Where-Object { $_ -match ",full," } | Select-Object -Last 1
    if (-not $last) { return "-" }
    $c = $last.Split(",")
    return "parse $($c[4])/$($c[3]) commands $($c[5])/$($c[3]) verdict $($c[7])/$($c[6]) perf $($c[8])/$($c[6]) (rust $($c[9])s java $($c[10])s)"
}

function Restore-Protected([string]$base, [int]$iter) {
    $dirty = Git (@("status", "--porcelain", "--") + $Protected)
    $committed = Git (@("diff", "--name-only", $base, "HEAD", "--") + $Protected)
    if (-not $dirty -and -not $committed) { return }
    Log "iter ${iter}: agent touched protected files -> restoring: $($dirty) $($committed)"
    Git (@("restore", "--source=$base", "--staged", "--worktree", "--") + $Protected) | Out-Null
    Git (@("clean", "-fdq", "--") + $Protected) | Out-Null
    Git @("commit", "-qm", "loop: restore protected files changed in iteration $iter") | Out-Null
}

# ---- preflight -------------------------------------------------------------------------------
& python harness/setup.py
if ($LASTEXITCODE -ne 0) { Log "setup.py failed; aborting"; exit 1 }
if (Git @("status", "--porcelain")) {
    Git @("add", "-A") | Out-Null
    Git @("commit", "-qm", "loop: snapshot before driver start") | Out-Null
}
if (-not (Test-Path "harness\results\best.json") -and -not $NoGate) {
    Log "creating initial baseline"
    & python harness/check.py --update-best | Select-Object -First 12
    Git @("add", "-A") | Out-Null; Git @("commit", "-qm", "loop: initial baseline") | Out-Null
}
Log "driver start: model=$Model maxIter=$MaxIterations timeout=${IterationTimeoutMin}m score: $(Score)"

$noProgress = 0
for ($i = 1; $i -le $MaxIterations; $i++) {
    if (Test-Path (Join-Path $Root "loop\STOP")) { Log "loop/STOP found -> stopping"; break }
    $tag = "{0:D3}" -f $i
    $stamp = Get-Date -Format "yyyyMMdd-HHmmss"
    $out = Join-Path $Logs "iter-$tag-$stamp.jsonl"
    $err = Join-Path $Logs "iter-$tag-$stamp.stderr.txt"
    $before = (Git @("rev-parse", "HEAD")).Trim()
    Log "iter ${i}: start (HEAD $($before.Substring(0,8)))"

    $argList = @("-p", "--model", $Model, "--dangerously-skip-permissions", "--output-format", "stream-json", "--verbose")
    if ($MaxBudgetUsdPerIter -gt 0) { $argList += @("--max-budget-usd", "$MaxBudgetUsdPerIter") }
    $p = Start-Process -FilePath "claude" -ArgumentList $argList -RedirectStandardInput $PromptFile `
        -RedirectStandardOutput $out -RedirectStandardError $err -NoNewWindow -PassThru
    if (-not $p.WaitForExit($IterationTimeoutMin * 60 * 1000)) {
        Log "iter ${i}: TIMEOUT after $IterationTimeoutMin min -> killing"
        & taskkill /F /T /PID $p.Id | Out-Null
    }
    # summarize the agent's final message
    $res = Get-Content $out -ErrorAction SilentlyContinue | Where-Object { $_ -match '"type":"result"' } | Select-Object -Last 1
    if ($res) {
        try {
            $r = $res | ConvertFrom-Json
            $txt = ("" + $r.result) -replace "\s+", " "
            if ($txt.Length -gt 300) { $txt = $txt.Substring(0, 300) }
            Log "iter ${i}: agent done turns=$($r.num_turns) cost=`$$($r.total_cost_usd) :: $txt"
        } catch { Log "iter ${i}: could not parse result line" }
    } else { Log "iter ${i}: no result line (see $err)" }

    Restore-Protected $before $i
    if (Git @("status", "--porcelain")) {
        Git @("add", "-A") | Out-Null
        Git @("commit", "-qm", "loop: auto-commit leftovers of iteration $i") | Out-Null
    }

    if (-not $NoGate) {
        $gate = & python harness/check.py --gate --update-best 2>&1
        $gateRc = $LASTEXITCODE
        $build = ($gate | Select-String "BUILD FAILED") -ne $null
        if ($gateRc -ne 0 -or $build) {
            $branch = "rejected/iter-$tag"
            Git @("branch", "-f", $branch, "HEAD") | Out-Null
            Git @("reset", "-q", "--hard", $before) | Out-Null
            $body = @("# Last iteration was REJECTED and reverted by the driver",
                "Iteration $i ($stamp). Its commits are kept on branch ``$branch`` (inspect with ``git log $branch`` / ``git diff $before $branch``).",
                "Reason: " + $(if ($build) { "cargo build failed" } else { "regression vs harness/results/best.json" }),
                "", "Gate output (head):", '```') + ($gate | Select-Object -First 60) + @('```',
                "", "Read this, learn from it (see loop/NOTES.md), then delete this file in your iteration's commit.")
            Set-Content -Path $Rejected -Value $body -Encoding utf8
            Git @("add", "loop/LAST_REJECTED.md") | Out-Null
            Git @("commit", "-qm", "loop: iteration $i rejected (saved on $branch)") | Out-Null
            Log "iter ${i}: REJECTED (gate rc=$gateRc build_failed=$build) -> reset to $($before.Substring(0,8)), saved $branch"
        } else {
            if (Git @("status", "--porcelain")) {
                Git @("add", "-A") | Out-Null
                Git @("commit", "-qm", "loop: baseline after iteration $i") | Out-Null
            }
            Log "iter ${i}: gate OK :: $(Score)"
        }
    }

    $touched = Git @("diff", "--name-only", $before, "HEAD", "--", "crates")
    if ($touched) { $noProgress = 0 } else { $noProgress++ }
    if ($noProgress -ge $MaxNoProgress) {
        Log "no crates/ progress for $noProgress iterations -> stopping (inspect loop/logs, adjust TASKS.md, restart)"
        break
    }
}
Log "driver end :: $(Score)"
