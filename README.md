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

현재 기준선: 모두 0 (Rust는 모든 곳에서 `unsupported` 반환).

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

### 방법 B — 대화형 Haiku 세션
```powershell
cd D:\sw\alloytoolRS
claude --model haiku
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
- **부정행위 방지**: Rust 코드가 golden을 읽거나 파일명 특수처리 금지(CLAUDE.md), 보호 파일은 settings.json
  deny 규칙 + 드라이버 원복으로 이중 보호.
- 인스턴스(해) 자체는 SAT solver마다 달라질 수 있어 비교하지 않고, 대신 해 개수(symmetry=0)로 의미적 동일성을 검사(M7).
