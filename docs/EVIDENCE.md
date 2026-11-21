# Official evidence (public competition data only)

All data below is public competition data fetched from the official public APIs on **2026-11-22 (+08)**:

* public progress-curve board: `https://riemann.verifytask.cn/api/board`
* attempt detail: `https://riemann.verifytask.cn/api/attempt/<id>` (only a *truncated* unified diff is public)
* Playground CLI `attempt list` / `status --attempt-id` (own account)

Raw snapshots used to build this page live in `evidence/`:

| file | content |
|---|---|
| `challenge-core1-summary.json` | challenge summary: id, `t0 = 21641`, top score, leader |
| `curve-core1-runs.json` | full public curve (`autoresearch.by_challenge.core1.runs`) |
| `curve-core1-runs.csv` | flat curve table (idx, id, author, score, kept, running_best_pct, display tokens) |
| `attempts.json` | our attempts with official scores/states and local token counts |

## 1. Curve points around the record refreshes

```
idx=52 id=96241 author=肖雨航     score=64.4305 kept=True  running_best_pct=85.10
idx=53 id=96252 author=Yin-Kai Yu score=63.8485 kept=False running_best_pct=85.10
idx=54 id=96263 author=Pi         score=64.5215 kept=True  running_best_pct=85.68   (previous record holder)
idx=55 id=96267 author=Yin-Kai Yu score=64.4685 kept=False running_best_pct=85.68
idx=56 id=96268 author=Yin-Kai Yu score=64.4685 kept=False running_best_pct=85.68
idx=57 id=96272 author=Yin-Kai Yu score=64.5332 kept=TRUE  running_best_pct=85.73   <== first record refresh
idx=58 id=96276 author=Yin-Kai Yu score=64.6400 kept=TRUE  running_best_pct=86.03   (repaired WIP)
idx=59 id=96281 author=Yin-Kai Yu score=64.8928 kept=TRUE  running_best_pct=86.64   (other agent in workspace)
idx=60 id=96282 author=Yin-Kai Yu score=64.9800 kept=TRUE  running_best_pct=86.87
idx=61 id=96283 author=Yin-Kai Yu score=65.1339 kept=TRUE  running_best_pct=87.24   <== #1 at snapshot
```

Board summary at the same snapshot: `top_score = 65.1339`, `best_tokens = 2762` (site display),
leader = Yin-Kai Yu (余荫铠), model on the leading submission = **Deepseek V4.1-Flash**,
harness = **DeepSeek Harness**.

**Acceptance evidence for the objective**: attempt `96272`, official final score `64.5332`,
`kept = true`, and `running_best_pct = 85.73` strictly greater than the immediately preceding curve point
`85.68` (attempt `96263`, Pi). Subsequent points are further `kept = true` refreshes by the same account.

## 2. Score ⇄ token recovery

Given the official score `S`, the official normalization token count satisfies

```
T = T₀ · 10^{ −2 · ( 50/(100−S) − 1 ) },   T₀ = 21641
```

| attempt | official score | derived official T | local metric T | Δ |
|---|---:|---:|---:|---:|
| 96252 | 63.8485 | ≈ 3,715 | 3,707 | −8 |
| 96267 | 64.4685 | ≈ 3,319 | 3,315 | −4 |
| 96268 | 64.4685 | ≈ 3,319 | 3,315 | −4 |
| 96272 | 64.5332 | ≈ 3,277 | 3,274 | −3 |
| 96276 | 64.6400 | ≈ 3,215 | 3,208 | −7 |
| 96281 | 64.8928 | ≈ 3,070 | 3,065 | −5 |
| 96282 | 64.9800 | ≈ 3,019 | 3,014 | −5 |
| 96283 | 65.1339 | ≈ 2,932 | 2,931 | −1 |

The local counter (`tools/token_count.py`) therefore reproduces the official normalization to ±8 tokens
(typically ±5), which is why every submission in this archive could be ranked *before* it was sent.

## 3. Attempts of this account

See `evidence/attempts.json`. Notes:

* **Rejected by the official Comparator despite compiling locally**:
  `96274` / `96275` (same 3,242-token artifact, submitted by each of the two agents in the workspace) and
  `96284` (2,880-token artifact). They have `scoringState = failed`, score 0. The 3,242-token artifact is
  archived as `Lean/failed-96274-v22.lean`. Lesson: a local kernel check + axiom audit is *not* sufficient
  for the official pipeline; the 2,843- and 2,931-token artifacts that did pass are archived here too.
* Smallest artifact with an **official final score**: `96283` (2,931 local tokens → score 65.1339).
* Pending at the last snapshot: `96286` (2,843 local tokens, queued) and `96285` (other agent, evaluating).
  These are listed as pending and are **not** claimed as results.
* Playground traces are real session exports validated with `playground trace validate`; they are
  deliberately **not** published in this repository (they contain local paths and private working context).

## 4. Latest progress-curve frontier (screenshots)

Two screenshots of the public *Proof Compression Progress Curve* are archived in `evidence/figures/`:
`curve-frontier-cn-latest.png` (Chinese UI) and `curve-frontier-en-latest.png` (English UI). At that moment
the curve reported **179 verified runs and 50 breakthroughs**, and the top of the Core-Pillar-1 frontier was
annotated with *Core 1: Borel–Carathéodory…* by **Yin-Kai Yu (余荫铠) · Deepseek**, confirming that the record
line of this account is the current frontier for the pillar. The corresponding board snapshot is
`evidence/curve-core1-runs.json`; the record sequence and official scores are in §3 above and in §4 of the
papers.