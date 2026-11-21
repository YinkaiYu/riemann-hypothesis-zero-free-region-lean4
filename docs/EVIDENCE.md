# Official evidence (public data only)

All data below is public competition data fetched from the official public APIs on **2026-11-22 (+08)**:

* public progress-curve board: `https://riemann.verifytask.cn/api/board`
* attempt detail: `https://riemann.verifytask.cn/api/attempt/<id>` (only a *truncated* unified diff is public)
* Playground CLI `attempt list` / `status --attempt-id` (own account)

Raw snapshots used to build this page live in `evidence/`:

| file | content |
|---|---|
| `challenge-core1-summary.json` | challenge summary: id, `t0 = 21641`, top score, leader |
| `curve-core1-runs.json` | full public curve (`autoresearch.by_challenge.core1.runs`) |
| `curve-core1-runs.csv` | flat curve table (idx, id, author, score, kept, running_best_pct, tokens) |
| `attempts.json` | our attempts with official scores/states and local token counts |

## 1. Curve points around the record refreshes

```
idx=52 id=96241 author=肖雨航      score=64.4305 kept=True  running_best_pct=85.10
idx=53 id=96252 author=Yin-Kai Yu  score=63.8485 kept=False running_best_pct=85.10
idx=54 id=96263 author=Pi          score=64.5215 kept=True  running_best_pct=85.68  (tokens display 3099)
idx=55 id=96267 author=Yin-Kai Yu  score=64.4685 kept=False running_best_pct=85.68
idx=56 id=96268 author=Yin-Kai Yu  score=64.4685 kept=False running_best_pct=85.68
idx=57 id=96272 author=Yin-Kai Yu  score=64.5332 kept=TRUE  running_best_pct=85.73  (tokens display 3089)
idx=58 id=96276 author=Yin-Kai Yu  score=64.6400 kept=TRUE  running_best_pct=86.03  (tokens display 3024)
idx=59 id=96281 author=Yin-Kai Yu  score=64.8928 kept=TRUE  running_best_pct=86.64  (tokens display 2892)
```

**Acceptance evidence for the objective**: attempt `96272`, official final score `64.5332`,
`kept = true`, and `running_best_pct = 85.73` strictly greater than the immediately preceding curve point
`85.68` (attempt `96263`, Pi). The two later points are further record refreshes by the same account.

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

The local counter (`tools/token_count.py`) therefore reproduces the official normalization to ±8 tokens
(typically ±5), which is why every submission in this archive could be ranked *before* it was sent.

## 3. Attempts of this account

See `evidence/attempts.json`. Notes:

* `96274` / `96275` — the same 3,242-token artifact, submitted by each of the two agents in the workspace;
  both were **rejected by the official Comparator** (`scoringState = failed`, score 0) although the file
  compiles and passes a local axiom audit. The artifact is archived as `Lean/failed-96274-v22.lean`.
* Queued at archive time: `96282` (3,014), `96283` (2,931), `96284` (2,880), `96286` (2,843 local tokens);
  no official score was available yet, so they are listed as pending and are **not** claimed as results.
* Playground traces are real session exports and were validated with `playground trace validate`; they are
  deliberately **not** published in this repository (they contain local paths and private working context).
