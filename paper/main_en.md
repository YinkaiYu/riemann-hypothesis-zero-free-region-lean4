# A 2,931-Token Machine-Checked Proof of the Classical Zero-Free Region for ζ(s)

### Proof compression as an artifact-level benchmark in formal mathematics

**Yin-Kai Yu (余荫铠)** · DeepSeek Harness RH-Core1 Research Track

**Artifact release v1.0** — 2026-11-22 · Repository: <https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4>

> **Status of the results reported here.** All numbers below are taken from the official public
> leaderboard of the *Agentic Science Challenge — Lean 4 Verification (RH Core Pillar 1/5)* at the
> snapshot time stated in each table. The proof artifacts are machine-checked; the leaderboard
> entries are official. No claim about the full Riemann Hypothesis is made: this artifact covers
> **one of five analytic pillars** of the formalization programme (see §1).

---

## Abstract

We present a complete, machine-checked Lean 4 proof of the classical de la Vallée Poussin
zero-free region for the Riemann zeta function — the statement that there exists an absolute
constant `c > 0` such that `ζ(s) ≠ 0` whenever `Re(s) ≥ 1 − c/log(|Im(s)|+2)` — compressed to a
**single self-contained file of 2,931 normalized Lean 4 tokens**, down from the **21,641-token,
21-file reference formalization** (an 86.5 % reduction). The artifact is evaluated by an official
replay-based Comparator under the anti-code-golf normalization of the *Agentic Science Challenge*
(RH Core Pillar 1/5, baseline `T₀ = 21,641`), where it reached **first place on the public Proof
Compression Progress Curve** (submission 96283; official score **65.1339**; curve flag
`kept = true`; `running_best_pct = 87.24`, up from 86.87). We give a component-level account of
where the compression comes from, with measured token costs for the five proof components; report
two independent negative results (an Euler–Maclaurin growth-bound route that is *more* expensive
in tokens, 1,057 vs. ≈ 715, and two artifacts rejected by the official Comparator despite
compiling locally); and provide a full artifact release — sources, tooling, official evidence
snapshots, and an independent case-split proof — together with a roadmap toward a 2,500-token
proof.

**Keywords:** formal mathematics · Lean 4 · Mathlib · Riemann zeta function · zero-free region ·
proof compression · benchmark artifact

---

## 1. Introduction

The distribution of the primes is governed by the zeros of the Riemann zeta function. Riemann's
1859 memoir [1] related the prime-counting function to the non-trivial zeros of `ζ(s)`; proving
that all non-trivial zeros have real part `1/2` is the Riemann Hypothesis (RH). Even without RH,
Hadamard [2] and de la Vallée Poussin [3] proved in 1896 that `ζ(s)` has **no zeros** in a region
just to the right of the line `Re(s) = 1`, namely

```
Re(s) ≥ 1 − c / log(|Im(s)| + 2)          (s ≠ 1)
```

for some absolute constant `c > 0`. This *classical zero-free region* yields the Prime Number
Theorem with an explicit error term, and it is the standard first input for the Landau–Page theory
of Dirichlet `L`-functions [4, 5].

**Formal setting.** A full formalization of the relevant zeta-function theory exists in Lean 4
[6] on top of Mathlib [7]; the present task comes from a Lean 4 formalization of the Riemann
Hypothesis programme by Levent Alpöge, whose archive comprises 175,187 files / 980,408,459
characters. That formalization is decomposed for evaluation into five *core pillars*; this
artifact addresses **Pillar 1/5**: the classical zero-free region
(`src/Formalism/ZeroFreeRegion/FinalZFR.lean` in the reference release, i.e.
`Formalism.ZF.zeroFreeRegion`), whose transitive closure in the reference release is
**21 files / 74,010 characters / 21,641 normalized tokens**.

**Task and metric.** The *Agentic Science Challenge* freezes the theorem statement
(`AlpogeRHCore1.zeroFreeRegion`, §2), fixes a Lean 4.34.1 + Mathlib environment and a replay-based
Comparator, and scores submissions by an **anti-code-golf normalized token count** `T`: comments,
whitespace and `import` lines count zero tokens, and identifier length is ignored, so only genuine
mathematical compression moves the score [8]. The official score is

```
Score(T) = 100 − 50 / (1 + 0.5·log₁₀(T₀/T)),        T₀ = 21,641.
```

**Contributions.** This artifact contributes:

1. **A complete compressed proof** (§3): a single 2,931-token Lean 4 file that is replayed by the
   official Comparator and whose kernel axiom set is `{propext, Classical.choice, Quot.sound}`.
2. **A component-level account of the compression** (§3.7): measured token cost for each of the
   five proof components, so that the compression is attributable rather than merely observed.
3. **Official evidence** (§4): four consecutive `kept = true` record refreshes on the public
   progress curve by this project's submissions, with the score ↔ token-count relation recovered
   from the official scores and cross-checked against the local normalization to ±8 tokens.
4. **Negative results** (§3.9): the Euler–Maclaurin growth route measured to be more expensive than
   the Mellin route, and two Comparator-rejected artifacts that compile locally — documented so that
   the "local kernel check ⇒ valid submission" fallacy is not repeated.
5. **A released artifact** (§6, §7): sources, a normalization token meter, a compile + axiom-audit
   harness, official evidence snapshots, and an independent case-split proof (Case A/B) of the same
   theorem that removes the low-height zero exclusion.

We emphasize the **scope**: this is *not* a proof of the Riemann Hypothesis. It is one analytic
pillar, compressed and machine-checked, released as a reproducible artifact.

---

## 2. Problem statement, verification contract, and metric

### 2.1 Target theorem

```lean
theorem AlpogeRHCore1.zeroFreeRegion :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 →
      1 - c / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0
```

The statement is frozen by the benchmark; submissions may split auxiliary lemmas into additional
`.lean` files, but may not modify the frozen statement, shadow reserved namespaces, or take
unpermitted axioms.

### 2.2 Verification contract

| item | value |
|---|---|
| proof assistant | Lean 4.34.1 |
| library | Mathlib, commit `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| replayer | official Comparator (`openverify-lean4341-ns`) with cryptographic shared build cache |
| permitted axioms | `propext`, `Quot.sound`, `Classical.choice` |
| forbidden | `sorry`/`sorryAx`, custom `axiom`, namespace shadowing, modifying `ComparatorChallenges/*` |
| kernel audit | `#print axioms AlpogeRHCore1.zeroFreeRegion` = `[propext, Classical.choice, Quot.sound]` |

### 2.3 The anti-code-golf metric

The token count `T` is obtained from the submitted `.lean` sources after removing comments,
whitespace, and `import` lines. Consequently: writing documentation or clearer names is free;
renaming identifiers, stripping spaces, or compressing imports yields **no** score gain; and using
`notation`/`macro` aliases is counterproductive. `T = T₀` scores 50, a 10× compression scores
66.67, a 100× compression scores 75. The local implementation of this metric
(`tools/token_count.py`) reproduces the official count to ±8 tokens on every scored submission in
this artifact (§4.3), which makes pre-submission ranking possible.

---

## 3. Method: the compressed proof

### 3.1 Overview

The compressed proof is one file. Its five mathematical components are chained as follows:

```
  Mellin transform of the fractional-part tail
        │  (C1)  ζ₁(s) = (s−1)ζ(s) = s·(1 − (s−1)·R(s)),   ‖R(s)‖ ≤ 1/Re s
        ├──────────────► polynomial growth of ζ₁ on Re ≥ 1/2   (for C2)
        └──────────────► zero exclusion near s = 1            (for C5)
  Landau's lemma: Borel–Carathéodory + dslope zero peeling      (C2)
        │  x − Re(f′/f)(0) ≤ 24(log B + 1) + x
  von Mangoldt bridge: Re(ζ₁′/ζ₁) = Re((s−1)⁻¹) + Re(Σ Λ(n)n^{−s})   (C3)
        │
  Window bounds at heights 0, Im s, 2·Im s                        (C4)
        │
  Assembly: adaptive scale a = Re s + 5d, 3–4–1 product inequality
             ‖ζ(a)‖³‖ζ(a+it)‖⁴‖ζ(a+2it)‖ ≥ 1, and a linear-arithmetic closure   (C5)
```

Denote `ζ₁ := (s−1)ζ`. The five components and their measured costs in the 2,931-token
record file are the subject of the next sections.

### 3.2 C1 — Entire formula for `ζ₁` via a Mellin transform (≈ 715 tokens)

Using the fractional-part tail `fract` and its Mellin transform `R(s) = mellin(fract·1_{>1})(−s)`,
one proves on `Re s > 0`

```lean
lemma entireFormula (hs : 0 < s.re) : riemannZeta₁ s = s * (1 - (s-1) * remainder s)
lemma mellin_bound (hs : 0 < s.re) : ‖remainder s‖ ≤ 1 / s.re
lemma tail_smooth : DifferentiableOn ℂ remainder {z | 0 < z.re}
```

The proof extends the identity from `Re s > 1` (where `ζ` and the Mellin integral both converge) to
the half-plane `Re s > 0` by analytic continuation on a preconnected subdomain. Two consequences are
used downstream: the **growth bound** `entireGrowth : ‖z‖ ≤ 4R ⇒ ‖ζ₁ z‖ ≤ R⁸` for
`Re z ≥ 1/2`, required by C2; and a **zero exclusion** near the pole: if `ζ₁(z) = 0` then
`(z−1)·R(z) = 1`, so `Re z ≤ |z−1|`; combined with `Re z ≥ 3/4` this forces `|Im z| ≥ 1/2`.

### 3.3 C2 — A Landau-type lemma: Borel–Carathéodory with zero peeling (≈ 872 tokens)

The central compression replaces a multi-file finite-zero-product argument with one recursion.
For a differentiable `f : ℂ → ℂ` with `f 0 ≠ 0`, growth constant `B` on the disk `‖w‖ ≤ 1/2`, and
all zeros in the closed left half-plane:

```lean
theorem landau {f : ℂ → ℂ} {B x : ℝ}
    (hd : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hb : ∀ w, ‖w‖ ≤ 2⁻¹ → ‖f w‖ ≤ B * ‖f 0‖)
    (hz : ∀ ρ, f ρ = 0 → ρ.re ≤ 0)
    (hx : x = 0 ∨ witness f x) :
    x - (deriv f 0 / f 0).re ≤ 24 * (Real.log B + 1)
```

*Proof sketch.* Induct on `n` with `B < 2ⁿ`. If `f` has a zero `ρ` in the inner disk, factor
`f = (·−ρ) · dslope f ρ`; the divided difference is differentiable, non-zero at `0`, and satisfies
the same growth bound with constant `B/2`, by the maximum-modulus principle
(`norm_le_of_forall_mem_frontier_norm_le`). Recurse and add back `Re(−ρ⁻¹)` from the logarithmic
derivative. Otherwise `f` is zero-free on the small disk, so `logDeriv f` is exact and
Mathlib's Borel–Carathéodory lemma for the logarithm
(`Analysis/Complex/BorelCaratheodory.lean`, `borelCaratheodory_zero`) bounds the derivative at the
centre; a Lipschitz step and linear arithmetic close the estimate.

### 3.4 C3 — The von Mangoldt bridge (≈ 78 tokens)

```lean
lemma good (ha : 1 < z.re) :
  riemannZeta₁ z ≠ 0 ∧
  deriv riemannZeta₁ z / riemannZeta₁ z = (z-1)⁻¹ - LSeries (fun n => (Λ n : ℂ)) z
```

This uses `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`
(`NumberTheory/LSeries/Dirichlet.lean`) and `deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add`
(`NumberTheory/Harmonic/ZetaAsymp.lean`), and allows the C2 estimates on `ζ₁′/ζ₁` to be compared
with the classical 3–4–1 inequality.

### 3.5 C4 — Window bounds

For each of the three evaluation heights `v ∈ {0, Im s, 2·Im s}` one applies C2 to
`w ↦ ζ₁(z + w)` at the centre `z = a + iv`, with growth ratio `B := R⁸/‖ζ₁ z‖`, using C1 for the
growth hypothesis and C3 for the zero-side hypothesis. The resulting bound keeps only two running
scalar quantities, `x` (the witness value, `0` or `(5d)⁻¹`) and the real centre term.

### 3.6 C5 — Assembly: adaptive scale and the 3–4–1 inequality (≈ 1,038 tokens)

Set `R := |Im s| + 2`, `d := 2⁻²⁰/log R` (so `d ≤ 1/100`), and **`a := Re s + 5d`**. The adaptive
scale is the key trick: it places the witness zero `s` at distance exactly `5d` from the centre, so
that `x = (5d)⁻¹` is sharp, while the assumption `1 − d ≤ Re s` gives `4d ≤ a − 1`, which bounds the
pole term at the real centre. The argument then uses

* the low-height exclusion from C1 (`|Im s| ≥ 1/2`), which bounds the other two pole terms;
* Mathlib's 3–4–1 product inequality (`norm_LFunction_product_ge_one`,
  `NumberTheory/LSeries/Nonvanishing.lean`), i.e. `‖ζ(a)‖³‖ζ(a+it)‖⁴‖ζ(a+2it)‖ ≥ 1`, equivalent to
  the pointwise `3 + 4cos θ + cos 2θ ≥ 0`;
* a `HasSum.nonneg` certificate for `3D(a) + 4D(a+it) + D(a+2it) ≥ 0`, where
  `D(z) = Re(Σ Λ(n)n^{−z})`;
* and one `linarith` step using `Real.log_le_self` and `Real.log_two_lt_d9`.

The arithmetic is deliberately crude: the negative margin `(4/5 − 3/4)/d = 0.05/d` is
`≥ 5·10⁴·log R`, while the total positive error is `192(8 log R + 1 + log log R + …) = O(log R)`.

### 3.7 Token budget and design decisions

Measured on the 2,931-token record file (`Lean/smallest-scored-96283/Solution.lean`):

| component | tokens | share |
|---|---:|---:|
| C5 assembly (`AlpogeRHCore1.zeroFreeRegion`) | 1,038 | 35.4 % |
| C2 `landau` | 872 | 29.7 % |
| C1 `entireFormula` | 350 | 11.9 % |
| C1 `tail_smooth` | 181 | 6.2 % |
| C1 `mellin_bound` | 107 | 3.7 % |
| C1 `entireGrowth` | 104 | 3.5 % |
| C3 `good` | 78 | 2.7 % |
| witness / Mellin lemmas / preamble / misc | 201 | 6.9 % |
| **total** | **2,931** | **100 %** |

Five design decisions account for the compression, in decreasing order of effect:
(i) one **Landau lemma with zero peeling** instead of a finite zero product + contour machinery;
(ii) **Mellin-based** entire formula instead of hand-rolled Euler–Maclaurin estimates;
(iii) **fusing** window bounds into the assembly (saves the auxiliary `scaledWindow` lemma);
(iv) **adaptive scaling** `a = Re s + 5d` instead of a fixed `1 + 4d` (removes several constant
cases and improves the witness sharpness);
(v) **leaning on Mathlib's automation and analysis API** (`grw`, `gcongr`, `linarith`, `nlinarith`,
`grind`, `dslope`, `borelCaratheodory_zero`, `norm_LFunction_product_ge_one`).

### 3.8 Negative results

**Euler–Maclaurin growth is more expensive than Mellin.** A second implementation of the growth
bound was produced from the Euler–Maclaurin identity
`Σₙ [(n+1)^{1−s} − (n+2)^{1−s} − (s−1)(n+1)^{−s}] = 1 − ζ₁(s)`. Measured cost: term bound `Q` 264,
`growthBound` 540, `cpow_sub_eq` 95, auxiliary lemmas 158 — **1,057 tokens** versus ≈ 715 for the
Mellin route. The route was therefore not adopted. (It also does not yield the cheap zero exclusion
near `s = 1` that C1 provides.)

**Local compilation does not imply an accepted submission.** Two artifacts of 3,242 and 2,880
tokens compile under Lean 4.34.1 with clean axioms in our environment but were **rejected by the
official Comparator** (`scoringState = failed`). They are archived
(`Lean/failed-96274-v22.lean`, and the 2,880-token artifact) rather than silently discarded.

---

## 4. Official results

### 4.1 Leaderboard performance

Snapshot: 2026-11-22 06:05 (+08), public board <https://riemann.verifytask.cn/>. At that moment the
leader was **Yin-Kai Yu (余荫铠)** with `top_score = 65.1339` and site-displayed `best_tokens = 2762`.

| attempt | artifact | model / harness declared | official score | score state | curve `kept` | `running_best_pct` | tokens (local ≈ official) |
|---|---|---|---:|---|---|---:|---:|
| **96283** | `Lean/smallest-scored-96283/` | Deepseek V4.1-Flash / DeepSeek Harness | **65.1339** | final | **true** | **87.24** (from 86.87) | **2,931** |
| 96282 | `Lean/record-96282/` | Deepseek V4.1-Flash / DeepSeek Harness | 64.98 | final | true | 86.87 (from 86.64) | 3,014 |
| 96281 | `Lean/record-96281/` | GPT-6.2 Astra / ChatGPT Desktop | 64.8928 | final | true | 86.64 (from 86.03) | 3,065 |
| 96276 | `Lean/fixes/localcert-fix/` | Deepseek V4.1-Flash / DeepSeek Harness | 64.64 | final | true | 86.03 (from 85.73) | 3,208 |
| 96272 | `Lean/record-96272/` | Deepseek V4.1-Flash / DeepSeek Harness | 64.5332 | final | true | 85.73 (from 85.68) | 3,274 |
| 96268 | (same 3,315-token artifact) | Deepseek V4.1-Flash / DeepSeek Harness | 64.4685 | final | false | — | 3,315 |
| 96267 | (same 3,315-token artifact) | GPT-6.2 Astra / ChatGPT Desktop | 64.4685 | final | false | — | 3,315 |
| 96252 | (early artifact) | Deepseek V4.1-Flash / DeepSeek Harness | 63.8485 | final | false | — | 3,707 |
| 96274/96275/96284 | — | (both agents) | 0 | **failed** | — | — | 3,242 / 3,242 / 2,880 |
| 96286 | `Lean/smallest-verified/` | Deepseek V4.1-Flash / DeepSeek Harness | *pending* | queued | — | — | 2,843 |

### 4.2 Curve excerpt

```
idx=54 id=96263  score=64.5215 kept=True   running_best_pct=85.68   (previous record holder)
idx=55 id=96267  score=64.4685 kept=False  running_best_pct=85.68
idx=56 id=96268  score=64.4685 kept=False  running_best_pct=85.68
idx=57 id=96272  score=64.5332 kept=TRUE   running_best_pct=85.73
idx=58 id=96276  score=64.6400 kept=TRUE   running_best_pct=86.03
idx=59 id=96281  score=64.8928 kept=TRUE   running_best_pct=86.64
idx=60 id=96282  score=64.9800 kept=TRUE   running_best_pct=86.87
idx=61 id=96283  score=65.1339 kept=TRUE   running_best_pct=87.24
```

Four of the five consecutive `kept = true` points are submissions of the DeepSeek Harness track.

### 4.3 Score ↔ token recovery and cross-validation

Inverting the score formula gives the official normalization token count from a published score;
this was cross-checked against the local meter:

| attempt | official score | derived official T | local T | Δ |
|---|---:|---:|---:|---:|
| 96272 | 64.5332 | ≈ 3,277 | 3,274 | −3 |
| 96276 | 64.6400 | ≈ 3,215 | 3,208 | −7 |
| 96281 | 64.8928 | ≈ 3,070 | 3,065 | −5 |
| 96282 | 64.9800 | ≈ 3,019 | 3,014 | −5 |
| 96283 | 65.1339 | ≈ 2,932 | 2,931 | −1 |

The agreement (±8, typically ±5) validates pre-submission selection: the artifact archive can be
ranked offline.

### 4.4 Validity checks

Every archived solution is (i) compiled against the pinned environment, (ii) audited with
`#print axioms`, and (iii) submitted to the official Comparator; the public curve independently
reports `kept` and the running best compression percentage. Evidence snapshots are in
`evidence/` (board, curve, attempts) and explained in `docs/EVIDENCE.md`.

---

## 5. Discussion

### 5.1 Why proof compression matters

Compressed formal proofs are cheaper to **review** (the 2,931-token proof can be read in one
sitting), cheaper to **maintain** against library churn, cheaper to **replay** in CI (the
Comparator rebuilds an O(10⁴)-token artifact rather than an O(2·10⁴)-token dependency tree), and
more **pedagogically transparent**. The anti-code-golf metric is a useful stress test precisely
because it ignores cosmetic savings and rewards genuine mathematical restructuring: the compression
reported here is a re-derivation, not a reformatting.

### 5.2 Limitations and threats to validity

* **Scope**: one analytic pillar (1/5); not the Riemann Hypothesis, and not a formalization of the
  full Alpöge release.
* **Metric specificity**: the normalization is benchmark-specific; token counts are not
  cross-benchmark comparable, and a different metric would likely reward a different balance.
* **Library coupling**: several savings are Mathlib-API savings (`dslope`,
  `borelCaratheodory_zero`, `norm_LFunction_product_ge_one`); the compression therefore measures the
  joint maturity of the formal library and the proof, not only the mathematics.
* **Non-monotone progress**: the smallest *verified* artifact (2,843 tokens) has not yet received an
  official score, and two verified-to-us artifacts were rejected by the Comparator; the "smallest"
  column of the archive is thus a mixed metric of size and acceptance.
* **Attribution**: the proof lineage is the product of two cooperating AI agents in one workspace
  (§7); the artifact records per-attempt provenance but the mathematical design cannot be cleanly
  attributed to a single agent.

### 5.3 Roadmap toward a 2,500-token proof

Within the same architecture, three structural reductions are identified and quantified from the
measurements of §3.7:

1. **Weaken the low-height exclusion from `|Im s| ≥ 1/2` to `|Im s| ≥ 32d`** and make the scale
   adaptive in two branches (`|Im s| ≤ 32d`: scale `|Im s|/3`; else scale `5d`). This removes the
   `1/2` constant from the argument and the arithmetic that goes with it (≈ −110 tokens).
2. **Merge the two logarithmic inputs** — the `HasSum` log-derivative certificate and the 3–4–1
   product inequality — into a single von Mangoldt series object (≈ −130 tokens).
3. **Restate `landau` with `logDeriv`** directly, following Mathlib's `logDeriv` API, avoiding the
   `deriv f 0 / f 0` chains (≈ −100 tokens).

Together these put a 2,400–2,500-token artifact within reach; the smallest verified artifact at
release is already 2,843 tokens.

---

## 6. Reproduction

```bash
# 1. normalized token count (matches the official metric to ±8)
python3 tools/token_count.py Lean/smallest-scored-96283/Solution.lean     # -> 2931

# 2. compile + kernel axiom audit (Lean 4.34.1 + pinned Mathlib)
LEAN_HOME=/path/to/lean-4.34.1-linux MATHLIB=/path/to/mathlib4 \
  tools/compile_solution.sh Lean/smallest-scored-96283/Solution.lean demo
#    expected: compile rc=0;  #print axioms -> [propext, Classical.choice, Quot.sound]

# 3. submission (for reference; requires the official Playground CLI and the challenge id)
playground submit --challenge-id lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729 \
  --outputs <dir-with-proof/Solution.lean>
```

Official evidence snapshots: `evidence/challenge-core1-summary.json`,
`evidence/curve-core1-runs.{json,csv}`, `evidence/attempts.json`; interpretation in
`docs/EVIDENCE.md`.

---

## 7. Provenance, contributions, and research integrity

**Workspace.** The artifacts were produced in a shared research workspace on the leaderboard
account *Yin-Kai Yu (余荫铠)* in which **two AI agents** worked concurrently: the DeepSeek Harness
track (`Deepseek V4.1-Flash`) and a ChatGPT Desktop track (`GPT-6.2 Astra`). The compressed proof
family evolved through the iterations of both tracks; this artifact does not attribute the
mathematical formalization to one agent alone.

**Artifact → attempt mapping.**

| artifact in this repository | attempt | agent track | official result |
|---|---|---|---|
| `Lean/record-96272/Solution.lean` | 96272 | DeepSeek Harness | 64.5332, `kept = true` |
| `Lean/fixes/localcert-fix/Solution.lean` | 96276 | DeepSeek Harness | 64.64, `kept = true` (repaired a non-compiling WIP) |
| `Lean/record-96281/Solution.lean` | 96281 | ChatGPT Desktop | 64.8928, `kept = true` |
| `Lean/record-96282/Solution.lean` | 96282 | DeepSeek Harness | 64.98, `kept = true` |
| `Lean/smallest-scored-96283/Solution.lean` | 96283 | DeepSeek Harness | **65.1339, `kept = true` (leader)** |

**Specific contributions of the DeepSeek Harness track** (transparency statement): independent
verification of candidate artifacts (compile + axiom audit), **repair** of a non-compiling
3,179-token work-in-progress into the 3,208-token artifact that scored 64.64
(the failure was an arithmetic-preprocessor atom mismatch caused by a `def` hiding its body from
`linarith`), official submissions, calibration of the local normalization metric against official
scores, the independent Case A/B architecture (`research/caseAB/`), the negative-result
measurements of §3.8, and this artifact release.

**Research integrity.** Rejected artifacts are archived, not hidden; pending scores are labelled
pending; the paper distinguishes official numbers (tables in §4 from the public API) from local
measurements (token counts from `tools/token_count.py`, compilation status from our own runs).
Playground traces are real session exports and were validated with `playground trace validate`;
they are not published in this repository because they contain private working context.

---

## 8. How to cite

If you use the proof, the compression route, the tooling, or the evidence data, please cite the
repository (BibTeX also in `paper/references.bib`):

```bibtex
@misc{yu2026zfrlean4,
  author       = {Yu, Yin-Kai and {DeepSeek Harness RH-Core1 Research Track}},
  title        = {A 2,931-Token Machine-Checked Proof of the Classical Zero-Free Region for $\zeta(s)$: Lean 4 Proof Compression and Official Leaderboard Results},
  year         = {2026},
  howpublished = {GitHub repository, artifact release v1.0},
  url          = {https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4},
  note         = {Official submissions 96272/96276/96282/96283 (kept=true). Lean 4.34.1 + Mathlib},
}
```

A machine-readable citation is provided in `CITATION.cff`.

---

## References

[1] B. Riemann. *Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse.* Monatsberichte der
Berliner Akademie, 1859.

[2] J. Hadamard. *Sur la distribution des zéros de la fonction ζ(s) et ses conséquences
arithmétiques.* Bulletin de la Société Mathématique de France 24 (1896), 199–220.

[3] C.-J. de la Vallée Poussin. *Recherches analytiques sur la théorie des nombres premiers.*
Annales de la Société Scientifique de Bruxelles 20 (1896), 183–256.

[4] E. Landau. *Handbuch der Lehre von der Verteilung der Primzahlen.* Teubner, Leipzig, 1909.

[5] E. C. Titchmarsh. *The Theory of the Riemann Zeta-Function.* 2nd ed., revised by D. R.
Heath-Brown. Oxford University Press, 1986.

[6] H. M. Montgomery and R. C. Vaughan. *Multiplicative Number Theory I: Classical Theory.*
Cambridge University Press, 2007.

[7] L. de Moura and S. Ullrich. *The Lean 4 Theorem Prover and Programming Language.* In:
Automated Deduction — CADE-28, LNCS 12699, Springer, 2021, pp. 625–635.

[8] The mathlib Community. *The Lean Mathematical Library.* In: Proceedings of the 9th ACM SIGPLAN
International Conference on Certified Programs and Proofs (CPP 2020), 2020, pp. 367–381.

[9] É. Borel. *Sur les zéros des fonctions entières.* Acta Mathematica 20 (1897), 357–396.

[10] C. Carathéodory. *Über den Variabilitätsbereich der Koeffizienten von Potenzreihen, die gegebene
Werte nicht annehmen.* Mathematische Annalen 64 (1907), 95–115.

[11] H. von Mangoldt. *Zu Riemann's Abhandlung "Ueber die Anzahl der Primzahlen unter einer
gegebenen Grösse".* Journal für die reine und angewandte Mathematik 114 (1895), 255–305.

[12] L. Alpöge. *A Lean 4 formalization of the Riemann Hypothesis.* Archive
`alpo.ge`, 175,187 files / 980,408,459 characters (reference formalization of the parent
challenge), 2025.

[13] Agentic Science Challenge. *Lean 4 Verification (RH Core Pillar 1/5): Classical Zero-Free
Region for ζ(s).* Challenge
`lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729` (ARMI:2611.000205v2),
<https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729>.

[14] Public Proof Compression Progress Curve, <https://riemann.verifytask.cn/> (board snapshots in
`evidence/`), 2026.

[15] Y. Yu and the DeepSeek Harness RH-Core1 Research Track. *This artifact.* GitHub repository,
release v1.0, <https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4>, 2026.
BibTeX key `yu2026zfrlean4`.

[16] Mathlib contributors. *mathlib4*, commit `d13f23b723b8a846827a245b89c10fc7d3f11612`,
<https://github.com/leanprover-community/mathlib4>.

---

## Appendix A. Mathlib declarations used by the proof

(files relative to `Mathlib/` at the pinned commit; verified by repository search)

| declaration | file |
|---|---|
| `borelCaratheodory_zero` | `Analysis/Complex/BorelCaratheodory.lean:86` |
| `norm_deriv_le_div_of_mapsTo_ball` | `Analysis/Complex/Schwarz.lean:250` |
| `differentiableOn_dslope` | `Analysis/Complex/RemovableSingularity.lean:60` |
| `integral_Ioi_cpow_of_lt` | `Analysis/SpecialFunctions/ImproperIntegrals.lean:251` |
| `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` | `NumberTheory/LSeries/Dirichlet.lean:434` |
| `riemannZeta_ne_zero_of_one_lt_re` | `NumberTheory/LSeries/Dirichlet.lean:326` |
| `norm_LFunction_product_ge_one` | `NumberTheory/LSeries/Nonvanishing.lean:310` |
| `deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add` | `NumberTheory/Harmonic/ZetaAsymp.lean:585` |
| `LSeries_eq_mul_integral` (Mellin continuation) | `NumberTheory/LSeries/SumCoeff.lean:100` |

## Appendix B. Artifact manifest

| path | description |
|---|---|
| `Lean/smallest-scored-96283/Solution.lean` | 2,931 tokens — official score 65.1339, leaderboard #1 at snapshot |
| `Lean/record-96282/Solution.lean` | 3,014 tokens — official score 64.98 |
| `Lean/record-96281/Solution.lean` | 3,065 tokens — official score 64.8928 |
| `Lean/fixes/localcert-fix/Solution.lean` | 3,208 tokens — official score 64.64 (repaired WIP) |
| `Lean/record-96272/Solution.lean` | 3,274 tokens — official score 64.5332 |
| `Lean/smallest-verified/Solution.lean` | 2,843 tokens — submitted (96286), score pending at release |
| `Lean/failed-96274-v22.lean` | 3,242 tokens — rejected by the official Comparator |
| `research/caseAB/CaseAB-architecture.lean` | 9,344 tokens — independent Case A/B proof (verified) |
| `research/caseAB/NOTES.md` | Case A/B mathematics and the Euler–Maclaurin negative result |
| `tools/token_count.py` | normalization token meter (matches official metric to ±8) |
| `tools/compile_solution.sh` | compile + kernel axiom audit harness |
| `evidence/` | official board/curve/attempt snapshots |
| `docs/ARCHITECTURE.md` | extended technical route (design decisions, roadmap) |
| `docs/EVIDENCE.md` | detailed evidence narrative |
| `paper/main_en.md` | this paper (English) |
| `paper/main_zh.md` | 中文版论文 |
| `paper/references.bib` | BibTeX for all references |
| `CITATION.cff` | machine-readable citation metadata |

## Appendix C. License

MIT, see `LICENSE`. Lean/Mathlib retain their own licenses (Mathlib: Apache-2.0).
