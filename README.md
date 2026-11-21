# alloy-rs — Alloy Analyzer(Java) → Rust 재작성용 Loop Engineering 환경

Opus가 환경을 구축했고, 실제 포팅은 **별도의 Haiku 세션이 반복 루프로** 수행합니다.
판정 기준은 하나입니다: `python harness/check.py`의 점수 — Java Alloy 6.2.0과 **같은 답**, **더 느리지 않음**.

## 구성
```
reference/                    (git 제외, 읽기 전용)
  alloy-java/                 github.com/AlloyTools/org.alloytools.alloy  (포팅 대상 Java 소스)
  models/                     github.com/AlloyTools/models                (샘플 모델)
  bin/org.alloytools.alloy.dist.jar   Alloy 6.2.0 공식 릴리즈 (기준 실행기)
harness/                      심판 — 루프에서 수정 금지
  java-oracle/src/AlloyOracle.java   Alloy API로 각 명령을 실행해 정규화 JSON 출력
  corpus.json                 비교 대상 199개 .als (models 레포 + Alloy 내장 예제)
  golden/                     Java 결과(상태, SAT/UNSAT, 시간, 변수/절 수, 첫 인스턴스)
  golden_count/               대칭 제거 끈 상태(symmetry=0)의 해 개수 (최대 100) — M7 용
  check.py                    Rust 실행 → golden과 비교 → 점수판/회귀 검사
  quick.txt                   16개 스모크 세트
  SCHEMA.md                   Java/Rust 공통 JSON 프로토콜
crates/                       Rust 워크스페이스 (Haiku가 채움)
  alloy-core  kodkod  satsolver  alloy-translate  alloy-cli(→ target/release/alloy-rs.exe)
loop/
  PROMPT.md                   Haiku 1회 반복 절차 (수정 금지)
  TASKS.md                    마일스톤 M1~M9 작업 목록 (Haiku가 체크)
  PROGRESS.md / NOTES.md      반복 로그 / 지식 베이스 (세션 간 기억)
  run-loop.ps1                루프 드라이버
CLAUDE.md                     모든 세션이 자동으로 읽는 규칙
docs/JAVA_MAP.md              Java 파일 ↔ Rust 모듈 매핑
```

## 점수 단계 (check.py)
| 단계 | 기준 |
|---|---|
| parse | 파일 상태(ok / syntax_error / type_error)가 Java와 같음 |
| commands | 명령 목록(label, run/check, expect, `Command.toString()` 스코프 문자열 등)이 같음 |
| verdict | 명령별 SAT / UNSAT / ERROR가 같음 (465개 명령; Java 타임아웃 1개는 제외) |
| perf | verdict 일치 **그리고** `rust_ms ≤ 1.1 × java_ms + 20ms` |
| --count | (M7) symmetry=0에서 해 개수가 같음 |

## 현재 상태 (2026-11-22)
| 항목 | 결과 |
|---|---|
| parse / commands | 199/199, 199/199 |
| verdict | 465/465 (SAT/UNSAT/ERROR가 Java와 동일) |
| perf (순차 `--perf`) | 465/465, 총 시간 Rust 43.8s vs Java 285.7s (약 0.15배) |
| `--count` (symmetry=0) | 432/432 (Java 타임아웃 34개 제외) |
| 시간 논리(temporal, `var`/LTL/steps) | 구현 완료, 코퍼스의 temporal 명령 전부 일치 |

- `--gate`는 8개 명령을 병렬로 돌리므로 경계선 명령의 perf 점수가 부하에 따라 흔들립니다(409~465/465).
  속도는 순차 `python harness/check.py --perf`로 확인하세요.
- `--count` 모드에서 `check.py`가 출력하는 "REGRESSIONS vs best.json"은 Java가 타임아웃이라 count에서
  채점되지 않는 명령이 verdict용 best.json에는 있기 때문에 나오는 표시이며 실제 회귀가 아닙니다.
- 디버그 환경변수: `KTIME`, `KPROF`, `KSAT_CONFIGS`, `KSAT_STATS`, `KCOUNT`.

## 구현 메모: 시간 논리 (Alloy 6 temporal)
(`crates/alloy-translate/src/translate.rs`, `lib.rs`)
- 길이 k의 trace를 k = min..max steps(기본 1..10)로 차례로 풀고 처음 SAT에서 멈춥니다. `N..`처럼 상한이 없으면
  Java와 같은 ERROR("Bounded engines do not support complete model checking.").
- 시간 원자 `$time$i`를 각각 정확한(exact) 관계로 두고, 자유 관계 `$loop`(정확히 1개)가 loop 시작 상태를 가리킵니다.
  `var` sig/field는 마지막에 시간 열이 붙습니다.
- 모든 식은 시점 `Tp{level, state}`에서 번역됩니다. level 1 = 첫 통과, level 2 = loop 구간(loop 시작이 해당 상태 이전일 때만 도달).
  `always/eventually/after/before/historically/once/until/since/releases/triggered`는 도달 가능한 시점들에 대한 And/Or로 펼치고,
  `e'`는 마지막 상태에서 loop 목표들에 대한 ITE로 만듭니다. fact와 명령 식은 `Tp{1,0}`에서 평가하며,
  var sig/field 선언 제약과 sig-fact는 매 상태마다 걸립니다.
- 무작위 시간식 240개를 Java와 차분 테스트(until/since/releases/triggered 등가식 포함)해 불일치 0건이었습니다.

## 구현 메모: `--count` (해 열거)
(`alloy_translate::count_solutions`, `kodkod::translate::{count_all, count_projected, first_instance}`)
- 비시간 모델: 대칭 제거 없이 기본(primary)+skolem 변수를 막는 절을 추가하며 해를 하나씩 셉니다(상한 N, `count_capped`).
- 시간 모델은 Pardinus `next()` 의미를 따릅니다. 첫 해가 정적 관계를 고정하고, 이후 trace 길이를 늘려가며 서로 다른
  lasso trace만 셉니다(각 trace는 최소 prefix·최소 loop 주기로 한 번만 계산: `canonical_lasso`).
- Java의 개수는 첫 해(MiniSat의 false 우선)에 의존하므로, 정적 관계 변수는 사전식 최솟값이 되도록 고릅니다
  (`first_instance` + `SatSolver::solve_assuming`). 코퍼스에서는 Java와 모두 일치하지만 Java 솔버를 그대로 복제한 것은 아닙니다.

## Haiku 루프 실행 방법

### 방법 A — 헤드리스 드라이버 (권장)
반복마다 **새 컨텍스트**의 Haiku 세션을 띄워 작업 1개씩 수행합니다.
```powershell
cd D:\sw\alloytoolRS
pwsh -File loop/run-loop.ps1                          # 기본: --model haiku, 최대 100회, 반복당 45분
pwsh -File loop/run-loop.ps1 -MaxIterations 10 -IterationTimeoutMin 30 -MaxBudgetUsdPerIter 2
New-Item loop/STOP                                    # 현재 반복이 끝나면 정지
```
드라이버가 매 반복 후 하는 일:
1. 보호 파일(harness/, PROMPT.md, CLAUDE.md, 드라이버, settings) 변경 → 자동 원복
2. 커밋 안 된 잔여 변경 → 자동 커밋
3. **전체 gate 재실행** (`check.py --gate --update-best`)
   - 통과 → 기준선(best.json) 갱신·커밋
   - 빌드 실패/회귀 → 해당 반복 작업을 `rejected/iter-NNN` 브랜치에 보존하고 HEAD를 반복 전으로 되돌림,
     `loop/LAST_REJECTED.md`에 사유 기록 → 다음 반복이 읽고 교훈을 반영
4. `crates/` 변경 없는 반복이 4회 연속이면 정지 (막힘 감지)

로그: `loop/logs/driver.log` (요약), `loop/logs/iter-NNN-*.jsonl` (세션 전체 stream-json).
드라이버 자체 점검(Claude 호출 없음): `-Agent <가짜 에이전트.ps1>`로 대체 실행 가능.

### 방법 B — 대화형 Haiku 세션
```powershell
cd D:\sw\alloytoolRS
claude --model haiku --settings loop/haiku-settings.json
> /loop loop/PROMPT.md 를 읽고 그 절차대로 반복 1회를 수행해
```
한 세션에서 컨텍스트가 계속 쌓이므로(자동 요약 발생) 장시간 실행에는 방법 A가 낫습니다.
방법 B에서는 회귀 원복을 드라이버가 해주지 않으므로 가끔 `python harness/check.py --gate`를 직접 확인하세요.

## 진행 상황 보기
```powershell
python harness/check.py --no-build          # 현재 점수판 (빌드 생략)
Get-Content harness/results/history.csv     # 실행별 점수 이력
Get-Content loop/PROGRESS.md -Tail 30       # Haiku 작업 로그
git log --oneline | Select-Object -First 20
```

## 다시 만들기 / 점검
```powershell
python harness/setup.py                    # reference·jar·oracle·cargo 점검(없으면 자동 설치/빌드)
python harness/gen_golden.py --force       # golden 재생성 (약 8분, 순차 실행 = 정확한 타이밍)
python harness/gen_golden.py --count-mode --force -j 4
```

## 설계 메모
- **Java oracle**: 공식 CLI의 receipt.json에는 파싱 오류 위치, 변환 통계, 명령별 시간 분리가 없고, Windows의
  Java 런처가 `-c *`를 파일 glob으로 확장하는 문제가 있어서 Alloy API(`CompUtil.parseEverything_fromFile`,
  `TranslateAlloyToKodkod.execute_command`)를 직접 호출하는 oracle을 만들었습니다. 명령별 타임아웃 60초.
- **Rust 실행**: harness는 명령마다 별도 프로세스로 실행(크래시/무한루프 격리), 타임아웃 = `min(60s, max(3s, 5×Java+2s))`.
- **SAT solver**: Java 기본값 SAT4J에 대응해 순수 Rust `batsat`(MiniSat 계열)를 `satsolver` 트레이트 뒤에 둠.
  툴체인이 `x86_64-pc-windows-gnu`(C 컴파일러 없음)라 순수 Rust 의존성만 허용.
- **부정행위 방지**: Rust 코드가 golden을 읽거나 파일명 특수처리 금지(CLAUDE.md). 보호 파일은
  `loop/haiku-settings.json`의 deny 규칙(드라이버가 `--settings`로 Haiku에만 적용) + 드라이버의 자동 원복으로 이중 보호.
  대화형 세션(방법 B)에는 deny 규칙이 적용되지 않으니, 그 경우 `claude --model haiku --settings loop/haiku-settings.json`으로 실행하세요.
- 인스턴스(해) 자체는 SAT solver마다 달라질 수 있어 비교하지 않고, 대신 해 개수(symmetry=0)로 의미적 동일성을 검사(M7).
