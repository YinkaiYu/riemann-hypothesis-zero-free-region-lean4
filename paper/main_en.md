# Why It Fits: The Mathematical Structure of a 2,931-Token Lean 4 Proof of the Classical Zero-Free Region

**Yin-Kai Yu (余荫铠)**

*DeepSeek Harness × ChatGPT Desktop collaborative research track · Artifact release v1.0 · 2026-11-22*
<https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4>

> **Published technique.** The core device of this proof was distilled on the public benchmark site as
> technique `core1_borel_dslope` — *Borel–Carathéodory + Divided-Difference (DSlope) Zero Factorization* —
> created for submission **96283** under this account. §5 reproduces that note verbatim (English and
> Chinese) and develops the mathematics behind it.

---

## Abstract

The classical zero-free region of the Riemann zeta function is a textbook theorem whose reference Lean 4
formalization occupies 21 files and 21,641 normalized tokens. We explain the mathematics of a proof of the
same theorem that fits in **one file of 2,931 tokens** and holds the record on the public proof-compression
board (official score 65.1339, curve flag `kept = true`). The compression is not cosmetic; it comes from
replacing four pieces of re-derived analysis by *structure*: (i) a Mellin entire formula for `(s−1)ζ(s)`
that yields simultaneously the polynomial growth bound and a two-line zero exclusion near `s = 1`;
(ii) a recursive **zero-peeling lemma** — factor a zero through Mathlib's analytic divided difference
`dslope`, recurse with a halved growth constant, close with Borel–Carathéodory — that replaces the
reference's finite zero products and Cauchy integrals by a single 872-token induction;
(iii) a von Mangoldt bridge converting growth estimates into the classical 3–4–1 inequality; and
(iv) an **adaptive scale** `a = Re s + 5d`, `d = 2⁻²⁰/log R`, which makes the witness zero sit exactly `5d`
from the centre and removes three constant-case distinctions. We give the component-by-component token
account, an ablation showing the natural Euler–Maclaurin route costs ≈50 % more, and the arithmetic margins
that make the final `linarith` inevitable. The lesson is general: **formal-proof size in analytic number
theory is dominated by re-derivation, and library-native reformulation is the compression.**

**Keywords:** formalized analysis · proof compression · Lean 4 · Mathlib · zero-free region ·
analytic divided differences · Borel–Carathéodory inequality

---

## 1 Introduction

A textbook theorem can be a large formal artifact. The classical de la Vallée Poussin zero-free region —
`∃ c > 0` such that `ζ(s) ≠ 0` whenever `Re(s) ≥ 1 − c/log(|Im s|+2)` — is proved in a few pages in
Titchmarsh [5] or Montgomery–Vaughan [6], yet its reference Lean 4 formalization [12] (the closure of
`src/Formalism/ZeroFreeRegion/FinalZFR.lean`) is 21 files, 74,010 characters, **21,641 normalized tokens**
[13]. Modern benchmarks [13] measure exactly this quantity, because it is a proxy for how much
*mathematical structure* a proof exposes: comments and identifier names are free, so only genuine
restructuring lowers the count.

This paper explains the mathematics that takes this theorem from 21,641 to **2,931 tokens** (−86.5 %): the
proof whose official submission (96283) holds the record on the public curve (score 65.1339, `kept = true`,
`running_best_pct` 87.24) and whose submission lineage produced five consecutive record refreshes. The
thesis is quantitative and structural:

> The reference formalization is large because it **re-derives** analytic machinery — zero factorization,
> contour estimates, Euler–Maclaurin expansions — that Mathlib already contains in library form. Replacing
> each re-derivation with the corresponding library primitive, and reorganizing the final assembly around a
> single adaptive scale, compresses the proof by an order of magnitude **without weakening the statement**.

The remainder of the paper develops each component mathematically (§4–§5), proves the numerical margins
(§6), and accounts for the tokens (§7).

---

## 2 Setting

The frozen target, evaluated in Lean 4.34.1 [7] on Mathlib commit `d13f23b7…` [8] by an official
replay-based comparator with permitted axioms `{propext, Quot.sound, Classical.choice}`:

```lean
theorem AlpogeRHCore1.zeroFreeRegion :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 →
      1 - c / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0
```

The size measure is the **normalized token count** `T` (comments, whitespace, `import` lines: 0 tokens;
identifiers: 1 token each), baseline `T₀ = 21,641`; the benchmark score is
`100 − 50/(1 + 0.5·log₁₀(T₀/T))`. Our local meter reproduces the official count to ±8 tokens on every
scored submission (§8.3), so token accounting below is reliable.

---

## 3 The mathematical skeleton

Write `ζ₁(s) := (s−1)ζ(s)`, which is entire. The classical argument has three steps:

**(S1) A growth bound.** For a point `z` with `1 < Re z` and `|Im z| ≤ 2R` (`R = |Im s| + 2`),
control `‖ζ₁‖` on disks of radius `1/2` around `z`, by a polynomial in `R`.

**(S2) A logarithmic-derivative bound.** If `−Re(f′/f)(0)` is large and negative (a zero close to `0`),
then `f` must grow quickly. Quantitatively (`x = 0` or a witness zero at distance `≤ 1/6`):

```
x − Re(f′/f)(0) ≤ 24·(log B + 1),      where ‖f w‖ ≤ B‖f 0‖ on |w| ≤ 1/2.
```

**(S3) The 3–4–1 inequality.** For `a > 1` and all `t`,
`3D(a) + 4D(a+t) + D(a+2t) ≥ 0`, `D(z) = Re Σ Λ(n)n^{−z}`, equivalently `3 + 4cos θ + cos 2θ ≥ 0`.

The reference formalization implements (S1) with Euler–Maclaurin expansions and Cauchy integrals, and (S2)
with a finite zero product. We instead derive (S1) from a Mellin formula (§4), implement (S2) as a recursion
(§5), and obtain (S3) from a library identity (§6). The final assembly (§6.3) is then a few dozen lines.

---

## 4 The growth bound and the zero exclusion: one Mellin identity

Let `fract` be the fractional-part function and `R(s) = mellin(fract·1_{>1})(−s)`. The Mellin transform of
the tail gives, for `Re s > 0`:

```lean
lemma entireFormula (hs : 0 < s.re) : riemannZeta₁ s = s * (1 - (s-1) * remainder s)
lemma mellin_bound (hs : 0 < s.re) : ‖remainder s‖ ≤ 1 / s.re
```

*Proof.* For `Re s > 1`, split the Mellin integral of `ζ` at `1` and integrate by parts: the fractional part
appears, and the identity holds. Both sides are analytic on the preconnected domain `{Re > 0}`; by the
identity theorem it extends. ◻

Two consequences, both cheap (≈715 tokens total):
1. **Growth**: for `Re z ≥ 1/2` and `‖z‖ ≤ 4R`, `‖ζ₁ z‖ ≤ R⁸` (from `‖remainder‖ ≤ 1/Re z`). This is (S1).
2. **Zero exclusion near 1**: if `ζ₁(z) = 0` then `(z−1)R(z) = 1`, so `Re z ≤ |z−1|`. Combined with
   `Re z ≥ 3/4` this forces `|Im z| ≥ 1/2` — precisely the low-height control that (S3) needs at the middle
   evaluation height.

The reference instead proves these via explicit Euler–Maclaurin expansions; the Mellin identity costs a
third of that (§7.2).

---

## 5 The core technique: recursive zero peeling (872 tokens)

### 5.1 The statement

For `f : ℂ → ℂ` entire with `f 0 ≠ 0`, a one-sided growth constant `B` on `|w| ≤ 1/2`, all zeros in the
closed left half-plane, and a witness zero `ρ` in the disk `|ρ| ≤ 1/6` with `x ≤ Re((−ρ)⁻¹)`:

```
x − Re(f′/f)(0) ≤ 24·(log B + 1).
```

The hypotheses are exactly what the application can supply: `f := ζ₁(z + ·)` is entire, `f 0 ≠ 0` because
`ζ` does not vanish on `Re > 1` [8], the zero set is left of `Re = 0` because `ζ` does not vanish on
`Re ≥ 1`, and the witness is the putative zero `s` at distance `5d` — see §6.3.

### 5.2 The proof

Induct on `n` where `B < 2ⁿ`.

*Peel.* If a zero `ρ` of `f` lies in the inner disk, use the analytic divided difference:
`f w = (w − ρ)·dslope f ρ w`. The factor `dslope f ρ` is entire, nonzero at `0`, and on the outer disk it
satisfies `‖dslope f ρ w‖ ≤ (B/2)‖dslope f ρ 0‖` — the factor `1/2` is exactly the gain from cancelling the
distance to `ρ` against the growth radius. Recurse on `dslope f ρ`, then add back `Re(−ρ⁻¹)` from
`f′/f = (·−ρ)′/(·−ρ) + (dslope f ρ)′/(dslope f ρ)`.

*Close.* If `f` has no zero in the inner disk, `logDeriv f` is exact there; `f` has an analytic logarithm
`g` with `Re g ≤ log B`, and the Borel–Carathéodory inequality [9,10] bounds `|g′(0)|` by `2Re g(0)/R` with
`R = 1/2`. A Lipschitz estimate at `0` then converts `(f′/f)(0) = g′(0)` into the stated bound.

The recursion enumerates zeros *implicitly*: no product formula, no contour integral, no case analysis on
the number of zeros. This is why it replaces the reference's zero-factorization machinery, and why the
constant `24` (rather than the textbook `25` or `26`) is achievable: the witness disk `1/6` and growth disk
`1/2` are chosen so that both branches consume the same bound.

### 5.3 Lean realization

`dslope` gives the factorization definitionally (`sub_smul_dslope_of_zero`), differentiability descends via
`differentiableOn_dslope`, the growth transfer is `norm_le_of_forall_mem_frontier_norm_le` (maximum
modulus), and the logarithm branch uses `logDeriv_eqOn_iff` plus `borelCaratheodory_zero`. Cost: **872
tokens**, no auxiliary zero lemmas, and — with this lemma in place — the whole file contains 10 top-level
declarations.

### 5.4 The published technique

> **`core1_borel_dslope` — "Borel–Carathéodory + Divided-Difference (DSlope) Zero Factorization"**
> (submission 96283; category *Complex Analysis · Mathlib Reuse*).
>
> *English.* "Instead of carrying 21 files of hand-rolled Cauchy integral and Euler–Maclaurin estimates,
> this proof factors out a putative zero ρ directly via Mathlib's `DSlope` (analytic divided difference) and
> bounds `−(ζ′/ζ).re` with `BorelCaratheodory` and Landau's lemma in just 10 top-level declarations
> (200 lines). Lean 4's `grw` collapses the 3-4-1 trigonometric bound chain without intermediate helper
> lemmas."
>
> *中文原文。* 「不再维护原版 21 个文件的手写柯西积分与 Euler–Maclaurin 估计，而是直接借助 Mathlib 的
> `DSlope`（解析差商）剥离假想零点 ρ，配合 `BorelCaratheodory` 定理与 Landau 引理在仅 10 个顶层声明
> （200 行）内闭合 `−(ζ′/ζ).re` 估计；再用 Lean 4 广义不等式改写 `grw` 一步压平 3-4-1 三角放缩链，
> 省去大量中间引理。」
>
> *Key signals*: `BorelCaratheodory`, `differientiableOn_dslope`, `grw`, `ZetaAsymp`. *Compression*:
> 21 → 1 files, −87.2 % tokens.

---

## 6 Completing the argument

### 6.1 The von Mangoldt bridge (78 tokens)

On `Re z > 1`, `Re(ζ₁′/ζ₁)(z) = Re((z−1)⁻¹) + Re Σ Λ(n)n^{−z}`
(`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`). This is what turns the §5 bounds on `ζ₁′/ζ₁` into
statements about `D` in the 3–4–1 inequality.

### 6.2 Window bounds

Apply §5 at the three heights `v ∈ {0, Im s, 2·Im s}` with growth ratio `B = R⁸/‖ζ₁(a+iv)‖`, using §4 for
the growth hypothesis and §6.1 for the zero hypothesis. For the middle height the witness is the putative
zero itself, at distance `a − Re s`.

### 6.3 Adaptive scale and the arithmetic

Set `R = |Im s| + 2`, `d = 2⁻²⁰/log R` (so `d ≤ 1/100`), and **`a = Re s + 5d`**. Then:

* the witness sits at distance exactly `5d`, so `x = (5d)⁻¹` is sharp;
* the hypothesis `1 − d ≤ Re s` gives `4d ≤ a − 1`, so the real-centre pole term `(a−1)⁻¹ ≤ (4d)⁻¹`;
* the low-height exclusion of §4 bounds the middle pole term:
  `Re((a+i·Im s −1)⁻¹) ≤ 5d/((4d)²+(1/2)²) ≤ 20d`, and similarly for `2·Im s`.

Combining the three window bounds `r, t, u` as `3r + 4t + u`, the log-derivative certificate
`3D(a) + 4D(a+it) + D(a+2it) ≥ 0` (from §6.1 with the 3–4–1 pointwise inequality) and Mathlib's product
formulation [`norm_LFunction_product_ge_one`] yields

```
4/(5d) − 192·(log log R + 20 log 2)  ≤  3/(4d) + 4·20d + 20d + 192·(8 log R + 1).
```

The left margin is `(4/5 − 3/4)/d = 0.05/d = 0.05·2²⁰·log R ≥ 5·10⁴ log R`, while the right side beyond the
pole terms is `O(log R)` — since `log R ≥ Real.log 2 > 0.69`, a single `linarith` with `Real.log_le_self`
and `Real.log_two_lt_d9` closes the contradiction. **The record-breaking economy is here:** because
`d = 2⁻²⁰/log R` makes the negative margin astronomical, all estimates may be crude (`20d` for a pole
term!), which is what allows the code to avoid the reference's sharp but verbose bounds.

---

## 7 Why it breaks the record: token accounting

### 7.1 Component budget (2,931 tokens)

| component | tokens | share | role |
|---|---:|---:|---|
| assembly (§6.3) | 1,038 | 35.4 % | the analytic-number-theory content |
| peeling lemma (§5) | 872 | 29.7 % | replaces zero factorization + contour estimates |
| Mellin formula (§4) | 742 | 25.3 % | replaces Euler–Maclaurin growth machinery |
| von Mangoldt bridge (§6.1) | 78 | 2.7 % | converts to 3–4–1 |
| witness, Mellin lemmas, preamble | 201 | 6.9 % | glue |

Against `T₀ = 21,641` this is **−86.5 %**. The two big items (peeling + Mellin) are precisely the two
re-derivations eliminated; together they are 1,614 tokens, versus the reference's multi-file analytic
machinery.

### 7.2 Ablation: the Euler–Maclaurin route is 50 % more expensive

The natural alternative for §4 is Euler–Maclaurin: prove
`Σₙ[(n+1)^{1−s} − (n+2)^{1−s} − (s−1)(n+1)^{−s}] = 1 − ζ₁(s)` and bound the series. Measured cost: term
bound **264**, growth theorem **540**, integral identity **95**, auxiliary **158** = **1,057 tokens**,
versus ≈715 for Mellin — and it does not yield the cheap zero exclusion of §4(2). Both routes are
mathematically valid; the formal cost differs by ~50 %. This is the clearest evidence that the
record-breaking compression is *structural*.

### 7.3 Two further structural decisions

* **Fusion**: the three window bounds are inlined into the assembly (no separate `scaledWindow` lemma),
  saving the lemma's interface and its instantiation.
* **Automation**: inequalities are closed by `linarith`/`nlinarith` after a `grw` normalization, rather
  than by chains of helper lemmas; the file has 55 `have`s and 10 top-level declarations, with tactic
  profile `simp` 38, `linarith` 18, `grind` 14, `norm_num` 10, `grw`.

---

## 8 Official evaluation

### 8.1 Results

| attempt | artifact | official score | curve `kept` | `running_best_pct` | tokens (local ≈ official) |
|---|---|---|---:|---|---:|
| **96283** | 2,931-token artifact | **65.1339** | **true** | **87.24** | **2,931** |
| 96282 | 3,014 tokens | 64.98 | true | 86.87 | 3,014 |
| 96281 | 3,065 tokens | 64.8928 | true | 86.64 | 3,065 |
| 96276 | 3,208 tokens (repaired) | 64.64 | true | 86.03 | 3,208 |
| 96272 | 3,274 tokens | 64.5332 | true | 85.73 | 3,274 |
| 96286 | 2,843 tokens | pending | — | — | 2,843 |

Public board at snapshot: leader Yin-Kai Yu (余荫铠), `top_score = 65.1339`, site-displayed
`best_tokens = 2762`; the curve rose 85.68 → 85.73 → 86.03 → 86.64 → 86.87 → 87.24 across our submissions.

### 8.2 Verification

Every artifact is kernel-checked (`#print axioms AlpogeRHCore1.zeroFreeRegion` =
`[propext, Classical.choice, Quot.sound]`, no `sorry`) and replayed by the official comparator. Two
artifacts (3,242 and 2,880 tokens) compiled locally with clean axioms but were **rejected by the official
comparator**; they are archived as a validity boundary — local checking is necessary but not sufficient.

### 8.3 Metric calibration

Inverting the score formula reproduces the official token count: 96272 → 3,277 vs local 3,274;
96276 → 3,215 vs 3,208; 96282 → 3,019 vs 3,014; 96283 → 2,932 vs 2,931. Agreement to ±8 validates the
accounting of §7.

---

## 9 Discussion

**Three transferable principles.** (P1) *Replace re-derivation by library primitive* — the peeling lemma and
the Mellin formula; (P2) *choose scales so that estimates may be crude* — the `2⁻²⁰/log R` guarantee turns
sharpness requirements into slack; (P3) *fuse and automate* — inline interfaces and let decision procedures
close goals. We expect all three to transfer to other analytic pillars.

**Limitations.** One pillar (1/5) of a formalization programme, not the Riemann Hypothesis. Token count is a
benchmark-specific proxy, not a measure of mathematical depth; several savings are Mathlib-API savings, so
the result measures joint library/proof maturity. Progress is non-monotone in acceptance (§8.2).

**Roadmap to 2,500 tokens.** Weaken the low-height exclusion (`|Im s| ≥ 1/2` → `|Im s| ≥ 32d`) with a
two-branch adaptive scale (≈ −110); merge the two logarithmic inputs into one von Mangoldt object
(≈ −130); restate the peeling lemma with `logDeriv` (≈ −100).

---

## 10 Artifact and reproduction

The artifact contains the proof sources, the normalization token meter (calibrated to ±8 tokens), the
compile + axiom-audit harness, official evidence snapshots, an independent Case A/B architecture
(`research/caseAB/`), and both language versions of this paper.

```bash
python3 tools/token_count.py Lean/smallest-scored-96283/Solution.lean   # -> 2931
LEAN_HOME=... MATHLIB=... tools/compile_solution.sh Lean/smallest-scored-96283/Solution.lean demo
#   expected: compile rc=0;  #print axioms -> [propext, Classical.choice, Quot.sound]
```

**Provenance.** Results were produced under the account *Yin-Kai Yu (余荫铠)* by a collaborative research
track in which two AI agent tracks worked together (DeepSeek Harness / Deepseek V4.1-Flash and ChatGPT
Desktop / GPT-6.2 Astra). The submissions, measurements and this paper are part of that account's record.

**Citation.**

```bibtex
@misc{yu2026zfrmath,
  author       = {Yu, Yin-Kai},
  title        = {Why It Fits: The Mathematical Structure of a 2,931-Token Lean 4 Proof of the Classical Zero-Free Region},
  year         = {2026},
  howpublished = {GitHub repository, artifact release v1.0},
  url          = {https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4},
  note         = {Technique core1_borel_dslope; submission 96283, official score 65.1339, curve kept=true},
}
```

## References

[1] B. Riemann, *Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse*, 1859.
[2] J. Hadamard, *Sur la distribution des zéros de la fonction ζ(s)…*, Bull. SMF 24 (1896), 199–220.
[3] C.-J. de la Vallée Poussin, *Recherches analytiques sur la théorie des nombres premiers*, 1896.
[4] E. Landau, *Handbuch der Lehre von der Verteilung der Primzahlen*, Teubner, 1909.
[5] E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., OUP, 1986.
[6] H. L. Montgomery, R. C. Vaughan, *Multiplicative Number Theory I*, CUP, 2007.
[7] L. de Moura, S. Ullrich, *The Lean 4 Theorem Prover and Programming Language*, CADE-28, 2021, 625–635.
[8] The mathlib Community, *The Lean Mathematical Library*, CPP 2020, 367–381; mathlib4 commit `d13f23b7…`.
[9] É. Borel, *Sur les zéros des fonctions entières*, Acta Math. 20 (1897), 357–396.
[10] C. Carathéodory, *Über den Variabilitätsbereich…*, Math. Ann. 64 (1907), 95–115.
[11] H. von Mangoldt, *Zu Riemann's Abhandlung …*, J. Reine Angew. Math. 114 (1895), 255–305.
[12] L. Alpöge, *A Lean 4 formalization of the Riemann Hypothesis* (archive `alpo.ge`), 2025.
[13] Agentic Science Challenge, *Lean 4 Verification (RH Core Pillar 1/5)*, challenge `lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729`.
[14] Public Proof Compression Progress Curve, <https://riemann.verifytask.cn/> (incl. technique `core1_borel_dslope`), 2026.

## Appendix A. Mathlib declarations used

| declaration | file (pinned commit) |
|---|---|
| `borelCaratheodory_zero` | `Analysis/Complex/BorelCaratheodory.lean:86` |
| `norm_deriv_le_div_of_mapsTo_ball` | `Analysis/Complex/Schwarz.lean:250` |
| `differentiableOn_dslope` | `Analysis/Complex/RemovableSingularity.lean:60` |
| `logDeriv_eqOn_iff`, `logDeriv_mul` | `Analysis/Calculus/LogDeriv.lean` |
| `integral_Ioi_cpow_of_lt` | `Analysis/SpecialFunctions/ImproperIntegrals.lean:251` |
| `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` | `NumberTheory/LSeries/Dirichlet.lean:434` |
| `norm_LFunction_product_ge_one` | `NumberTheory/LSeries/Nonvanishing.lean:310` |
| `deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add` | `NumberTheory/Harmonic/ZetaAsymp.lean:585` |

## Appendix B. Artifact manifest

`Lean/smallest-scored-96283/` (2,931 tokens, official 65.1339), `Lean/record-96282/`,
`Lean/record-96281/`, `Lean/fixes/localcert-fix/` (3,208-token repair, official 64.64),
`Lean/record-96272/`, `Lean/smallest-verified/` (2,843 tokens, pending),
`Lean/failed-96274-v22.lean`, `research/caseAB/`, `tools/`, `evidence/`, `docs/`,
`paper/main_en.md`, `paper/main_zh.md`.
