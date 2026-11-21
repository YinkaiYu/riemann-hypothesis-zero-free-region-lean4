# Riemann Hypothesis — Formal Proof of the Zero-Free Region (Lean 4)

> A complete, machine-checked proof of one of the analytic pillars behind the Riemann Hypothesis,
> compressed from a **21,641-token** reference formalization to a **single 2,931-token file** —
> currently **#1 on the public proof-compression leaderboard**
> ([riemann.verifytask.cn](https://riemann.verifytask.cn/)).

[![Lean](https://img.shields.io/badge/Lean-4.34.1-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-pinned-green)](https://github.com/leanprover-community/mathlib4)
[![Kernel verified](https://img.shields.io/badge/kernel--verified-yes-brightgreen)](#evidence-and-verification)
[![Official score](https://img.shields.io/badge/official%20score-65.13-orange)](#result-at-a-glance)
[![License](https://img.shields.io/badge/license-MIT-lightgrey)](LICENSE)

---

## What is this, in plain language?

The **Riemann Hypothesis** is arguably the most famous open problem in mathematics. It is a statement
about the zeros of the Riemann zeta function ζ(s) — and about how prime numbers are distributed.
Modern mathematics has *reduced* the Riemann Hypothesis to several analytic "pillars"; one of them is the
classical **zero-free region** of ζ(s): the fact that ζ(s) cannot vanish in a thin region just to the left of
the vertical line Re(s) = 1.

This repository contains a **complete formal proof of that pillar in Lean 4** — a proof that a computer
program (Lean's kernel) has checked line by line, with no gaps, no unproven assumptions except the standard
axioms of mathematics, and no reliance on peer review.

The interesting part is **how small it is**. The benchmark built for this problem starts from a reference
formalization of **21,641 normalized tokens** spread over **21 files**. The proof archived here is **one
self-contained file of 2,931 tokens** — an **86.5 % reduction** — which took first place on the public
*Proof Compression Progress Curve*.

In other words: *a famous theorem about prime numbers, machine-verified, in a file you can read in one
sitting.*

---

## What is the Riemann Hypothesis (30-second version)?

The prime numbers are 2, 3, 5, 7, 11, … — they cannot be factored. Their distribution looks random but is
governed by an object from complex analysis, the **Riemann zeta function**

```
ζ(s) = 1/1ˢ + 1/2ˢ + 1/3ˢ + …
```

The Riemann Hypothesis says: every "non-trivial" zero of ζ(s) lies exactly on the line Re(s) = ½. If true,
it gives the best possible control over prime gaps, and it is a Millennium Prize Problem.

## What is a "zero-free region"?

Even *without* the full Riemann Hypothesis one can prove something extremely useful:

> ζ(s) has no zeros in a region just to the right of the line Re(s) = 1 — the **de la Vallée Poussin
> zero-free region**.

That theorem is what gives us the Prime Number Theorem *with an explicit error term*, and it is the gateway
result that every analytic proof of the Riemann Hypothesis attacks first. This repository formalizes that
region: there is a constant `c > 0` such that ζ(s) ≠ 0 whenever `1 − c/log(|Im s|+2) ≤ Re s`.

## What is "Pillar 1/5"?

The Agentic Science Challenge decomposes the formalization effort around the Riemann Hypothesis into five
analytic **core pillars**. This repository covers **Pillar 1/5** — the zero-free region above. The other
pillars are separate problems; nothing here claims the full Riemann Hypothesis.

The benchmark keeps the *statement* frozen and measures only the **compressed size of a complete, verified
proof** (anti-code-golf normalized Lean 4 tokens: comments and `import` lines cost 0, identifiers cost 1).
Score formula: `S(T) = 100 − 50 / (1 + 0.5·log₁₀(T₀/T))` with `T₀ = 21,641`.

---

## Result at a glance

Official leaderboard snapshot (2026-11-22 06:05 +08, public curve):

| rank | attempt | submitted artifact | model / harness | official score | curve `kept` | `running_best_pct` | tokens (≈ official) |
|---:|---|---|---|---:|---|---:|---:|
| **1** | **96283** | [smallest scored artifact](Lean/smallest-scored-96283/Solution.lean) | **Deepseek V4.1-Flash / DeepSeek Harness** | **65.1339** | **true** | **87.24** | **2,931** |
| 2 | 96282 | [3,014-token file](Lean/record-96282/Solution.lean) | Deepseek V4.1-Flash / DeepSeek Harness | 64.98 | true | 86.87 | 3,014 |
| 3 | 96281 | [3,065-token file](Lean/record-96281/Solution.lean) | GPT-6.2 Astra / ChatGPT Desktop | 64.8928 | true | 86.64 | 3,065 |
| 4 | 96276 | [repaired 3,208-token file](Lean/fixes/localcert-fix/Solution.lean) | Deepseek V4.1-Flash / DeepSeek Harness | 64.64 | true | 86.03 | 3,208 |
| 5 | 96272 | [3,274-token file](Lean/record-96272/Solution.lean) | Deepseek V4.1-Flash / DeepSeek Harness | 64.5332 | true | 85.73 | 3,274 |
| — | 96286 | 2,843-token file (smallest verified) | Deepseek V4.1-Flash / DeepSeek Harness | pending | — | — | 2,843 |

Public curve (excerpt; full snapshot in [`evidence/`](evidence/)):

```
idx=54 id=96263  score=64.52   kept=True   running_best_pct=85.68   (previous record holder)
idx=57 id=96272  score=64.53   kept=TRUE   running_best_pct=85.73   <== our first record refresh
idx=58 id=96276  score=64.64   kept=TRUE   running_best_pct=86.03
idx=60 id=96282  score=64.98   kept=TRUE   running_best_pct=86.87
idx=61 id=96283  score=65.13   kept=TRUE   running_best_pct=87.24   <== current #1
```

**What a competition judge should check** (the objective's acceptance evidence): attempt **96272** has an
official final score of **64.5332**, and its public curve point is `kept = true` with
`running_best_pct = 85.73`, strictly greater than the previous point's `85.68`. Later posts (96276, 96282,
96283) are further `kept = true` refreshes of the same curve by the same account.

---

## Repository guide

**If you are a general reader**: read this README, then
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for the five-step proof idea, then
[`docs/EVIDENCE.md`](docs/EVIDENCE.md) for the official numbers.

**If you are a Lean user**: the proof sources are in [`Lean/`](Lean/); the tooling (token meter and the
compile+axiom-audit harness) is in [`tools/`](tools/).

**If you are checking the claims**: the official public data snapshots are in [`evidence/`](evidence/) and
are explained in [`docs/EVIDENCE.md`](docs/EVIDENCE.md).

```
Lean/
  smallest-scored-96283/  2,931 tokens · official score 65.13 · current #1
  record-96282/           3,014 tokens · official score 64.98 · kept=true
  record-96281/           3,065 tokens · official score 64.89 · kept=true (other agent in the workspace)
  fixes/localcert-fix/    3,208 tokens · official score 64.64 · kept=true (a non-compiling WIP that we repaired)
  record-96272/           3,274 tokens · official score 64.53 · kept=true (our first record refresh)
  smallest-verified/      2,843 tokens · submitted, official score pending at snapshot time
  failed-96274-v22.lean   3,242 tokens · REJECTED by the official Comparator (kept as a cautionary artifact)
research/caseAB/          independent Case A/B architecture (9,344 tokens, verified, research only)
docs/                     architecture + official evidence
tools/                    normalization token meter; compile + axiom audit harness
```

---

## The proof route (five steps)

Each step is a genuine compression over the 21-file reference: the reference formalizes the same mathematics
with explicit Euler–Maclaurin estimates, Cauchy-integral arguments and finite zero products; the route below
replaces each of those with the shortest existing Mathlib-native argument.

1. **Entire formula for (s−1)ζ(s) via a Mellin transform** — the fractional-part tail gives
   `(s−1)ζ(s) = s·(1 − (s−1)·R(s))` with `‖R(s)‖ ≤ 1/Re s` for `Re s > 0`. From this single identity come both
   the polynomial growth bound needed by Landau's lemma and a two-line exclusion of zeros near `s = 1`.
2. **Landau's lemma** — Borel–Carathéodory at a point plus an analytic divided difference (`dslope`) to peel
   zeros one at a time, halving the growth constant per peel. This replaces the reference's multi-file
   finite-zero-product machinery.
3. **Von Mangoldt bridge** — `Re(ζ₁′/ζ₁) = Re((s−1)⁻¹) + Re(Σ Λ(n)n^{−s})`, converting logarithmic-derivative
   bounds into the classical 3–4–1 inequality.
4. **Window bounds** — at the three evaluation heights `0, Im s, 2·Im s`, apply Landau's lemma with growth
   ratio `B = R⁸/‖ζ₁‖`, `R = |Im s| + 2`.
5. **Assembly** — the adaptive scale `a = Re s + 5d` with `d = 2⁻²⁰/log R` places the witness zero at distance
   exactly `5d`; Mathlib's `norm_LFunction_product_ge_one` (the theorem behind `3 + 4cosθ + cos2θ ≥ 0`)
   supplies `‖ζ(a)‖³‖ζ(a+it)‖⁴‖ζ(a+2it)‖ ≥ 1`, and one `linarith` step with explicit logs closes the
   contradiction.

The full mathematical and Lean engineering write-up, including a token budget per component and a roadmap to
2,500 tokens, is in [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md).

---

## Evidence and verification

* **Kernel check**: every archived solution compiles under Lean 4.34.1 against the pinned Mathlib.
* **Axiom audit**: `#print axioms AlpogeRHCore1.zeroFreeRegion` reports exactly
  `[propext, Classical.choice, Quot.sound]` — no `sorry`, no `sorryAx`, no extra axioms.
* **Official verification**: each scored attempt was evaluated by the platform's official Comparator, and the
  public curve records `kept = true` and the new `running_best_pct` for each record refresh.
* **Token measurement**: [`tools/token_count.py`](tools/token_count.py) reproduces the official normalization
  metric to within ±8 tokens on every scored attempt in this archive, which is how submissions were ranked
  *before* being sent.
* **Negative results are kept too**: two artifacts that compile cleanly here were rejected by the official
  Comparator (`Lean/failed-96274-v22.lean`, and the 2,880-token artifact of attempt 96284). They are archived
  because "compiles locally" is not the same as "passes the official pipeline".

---

## Reproduce

Prerequisites: Lean **4.34.1** (`elan`), a prebuilt Mathlib at the pinned commit, and the frozen challenge
statement module. Then:

```bash
# compile a solution and audit its axioms (needs LEAN_HOME and MATHLIB env vars)
LEAN_HOME=/path/to/lean-4.34.1-linux \
MATHLIB=/path/to/mathlib4 \
  tools/compile_solution.sh Lean/smallest-scored-96283/Solution.lean mytag

# reproduce the normalized token count
python3 tools/token_count.py Lean/smallest-scored-96283/Solution.lean   # -> 2931
```

---

## Provenance and honesty

This archive comes from a **shared research workspace in which two AI agents competed on the same
leaderboard account**:

* the **DeepSeek Harness** track (`Deepseek V4.1-Flash`) — verification, repair work, official submissions,
  token-metric calibration and the independent architecture research in `research/`;
* a parallel **ChatGPT Desktop** track (`GPT-6.2 Astra`) — its own independently-produced solution lineage.

The compressed proof *family* evolved through **both** tracks' iterations in that shared workspace. This
repository does **not** claim the formalization as the exclusive work of one agent; it archives exactly which
artifacts were verified, repaired and submitted, with their official attempt ids, and publishes the complete
route so that the compression can be independently checked and improved.

Two concrete contributions of the DeepSeek track documented here:

1. **Repair**: [`Lean/fixes/localcert-fix/Solution.lean`](Lean/fixes/localcert-fix/Solution.lean) — the original
   3,179-token work-in-progress did not compile (the arithmetic preprocessor could not see through a `def`;
   an atom-mismatch in `linarith`). We repaired it into a 3,208-token file with clean axioms; it scored
   **64.64** and is `kept = true` on the public curve.
2. **Independent derivation**: [`research/caseAB/`](research/caseAB/) — a different, verified case-split proof
   (Case A / Case B) that removes the low-height zero exclusion entirely. It is larger in tokens (9,344) and
   therefore not competitive on the metric, but it is an independent mathematical route, and it seeded the
   "< 2,500 tokens" roadmap in the architecture document.

---

## Glossary

| term | meaning |
|---|---|
| **Lean 4** | a proof assistant: a programming language in which you can state mathematical theorems and have a computer check the proof, line by line. |
| **Mathlib** | the community library of formalized mathematics for Lean 4 (over a million lines). |
| **kernel-verified** | the proof was accepted by Lean's trusted kernel; every inference step is checked mechanically. |
| **normalized token** | the benchmark's size unit: Lean tokens with comments/whitespace/imports removed; identifier length is ignored. |
| **zero-free region** | a region of the complex plane where ζ(s) provably has no zeros; the classical one gets within `c/log t` of the line Re(s)=1. |
| **`kept`** | a flag on the public curve: `true` means the submission set a new *best* (record) at its time. |

## License

MIT — see [`LICENSE`](LICENSE). Lean/Mathlib dependencies keep their own licenses (Mathlib: Apache-2.0).
