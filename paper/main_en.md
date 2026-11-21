# Library-Native Proof Compression: Successive Record Formalizations of the Classical Zero-Free Region in Lean 4

**Yin-Kai Yu (余荫铠)**

*DeepSeek Harness × ChatGPT Desktop collaborative research track · Artifact release v1.0 · 2026-11-22*
<https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4>

---

## Abstract

The classical zero-free region of the Riemann zeta function is proved in a few pages in every analytic
number theory textbook, yet its reference Lean 4 formalization spans 21 files and 21,641 normalized tokens.
We report a program of **library-native proof compression**: replacing re-derived analytic machinery by
Mathlib primitives until the same theorem fits in a single file, and we analyze the mathematical structure
of each successive record artifact. Over five record refreshes on the public compression board
(official scores 64.5332 → 64.6400 → 64.8928 → 64.9800 → 65.1339, all with curve flag `kept = true`), the
artifact shrank 3,274 → 3,208 → 3,065 → 3,014 → **2,931 tokens** (−86.5 % relative to the baseline). Each
step is traced to a specific structural insight: a recursive zero-peeling lemma replacing finite zero
products and contour estimates; a Mellin entire formula yielding both the growth bound and a cheap zero
exclusion; an adaptive scale `a = Re s + 5d`, `d = 2⁻²⁰/log R` that makes every estimate crude yet decisive;
and successive fusions of the window/assembly interface. We give component-level token accounting, an
ablation showing the Euler–Maclaurin growth route costs ≈50 % more than the Mellin route, and the official
evaluation including two artifacts rejected despite compiling locally.

**Keywords:** formalized analysis · Lean 4 · Mathlib · proof compression · zero-free region ·
analytic divided differences · Borel–Carathéodory inequality

---

## 1 Introduction

The size of a formal proof is an engineering quantity with mathematical content. In a proof that follows a
textbook argument, most of the size is spent on *machinery*: estimates re-derived, zero sets enumerated,
integrals bounded. Modern libraries make much of that machinery available, so a proof written in library
terms can be an order of magnitude smaller than one that re-derives it. The public proof-compression
benchmark used here makes the quantity explicit: the statement is frozen, the environment is fixed
(Lean 4.34.1 + Mathlib), and the score depends on the normalized Lean token count `T` of the submission,
with comments and identifier names free [13]. The reference closure of the target occupies 21 files and
`T₀ = 21,641` tokens.

This paper reports a sequence of compressions that set the record five times, and — the point of the paper —
explains the **mathematical structure** of each step. §4 fixes the mathematical core; §5 walks through the
five record artifacts, in the order they were accepted, identifying for each the structural change and its
measured token consequence; §6 summarizes the compression mechanisms and quantifies them.

---

## 2 Setting and measurement

Target (frozen): `∃ c > 0, ∀ s ≠ 1, 1 − c/log(|Im s|+2) ≤ Re s ⇒ ζ(s) ≠ 0`, the classical de la Vallée
Poussin region [3] underlying the Prime Number Theorem with error term and Landau–Page theory [4,5].
Verification: Lean 4.34.1 [7] + Mathlib commit `d13f23b7…` [8], official replay comparator, permitted axioms
`{propext, Quot.sound, Classical.choice}`, no `sorry`. Metric: normalized tokens `T` with
`Score(T) = 100 − 50/(1 + 0.5·log₁₀(T₀/T))`. Our local meter reproduces the official count to ±8 tokens
(§7.3), so the accounting below is comparable to official numbers.

---

## 3 The mathematical core

Write `ζ₁(s) = (s−1)ζ(s)` (entire). Every version in §5 shares the same three-step skeleton.

**(S1) Growth.** Control `‖ζ₁‖` on disks of radius `1/2` around points `z` with `1 < Re z`, `|Im z| ≤ 2R`
(`R = |Im s|+2`), polynomially in `R`.

**(S2) Logarithmic derivative.** With `f := ζ₁(z + ·)` on `|w| ≤ 1/2` and a witness zero `ρ` (`|ρ| ≈ 5d`):
`x − Re(f′/f)(0) ≤ C(log B + 1)`, where `B` bounds `‖f‖` on the disk and `x = 0` or `x ≤ Re((−ρ)⁻¹)`.

**(S3) 3–4–1.** For `a > 1`, all `t`: `3D(a) + 4D(a+t) + D(a+2t) ≥ 0`, `D(z) = Re Σ Λ(n)n^{−z}`, i.e.
`3 + 4cos θ + cos 2θ ≥ 0`.

All five record artifacts implement (S1) by a Mellin entire formula, (S2) by a recursive peeling lemma, and
(S3) by Mathlib's product inequality; what changes across versions is the *interface* between these parts
and the arithmetic assembly. The shared core is:

* **Mellin formula.** For `Re s > 0`, `ζ₁(s) = s(1 − (s−1)R(s))` with `‖R(s)‖ ≤ 1/Re s`. It gives (S1)
  (`‖ζ₁ z‖ ≤ R⁸` for `Re z ≥ 1/2`, `‖z‖ ≤ 4R`) and a zero exclusion near `s = 1`: `ζ₁(z)=0 ⇒ Re z ≤ |z−1|`,
  hence zeros with `Re z ≥ 3/4` satisfy `|Im z| ≥ 1/2`.
* **Peeling lemma.** For entire `f` with `f 0 ≠ 0`, growth constant `B` on `|w| ≤ 1/2`, zeros in the closed
  left half-plane, and a witness zero in `|ρ| ≤ 1/6`: `x − Re(f′/f)(0) ≤ 24(log B + 1)`. Proof: if a zero
  is in the inner disk, factor it through `dslope` and recurse with constant `B/2`; otherwise `f` has a
  logarithm with `Re g ≤ log B` and Borel–Carathéodory [9,10] bounds `g′(0)`. This replaces finite zero
  products and Cauchy integrals by an 872-token induction.
* **Bridge.** `Re(ζ₁′/ζ₁) = Re((s−1)⁻¹) + Re Σ Λ(n)n^{−s}` on `Re > 1`
  (`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`), connecting (S2) with (S3).
* **Assembly.** Set `a = Re s + 5d` with `d = 2⁻²⁰/log R`. Then the witness sits at distance exactly `5d`
  (`x = (5d)⁻¹` is sharp), and the premise `1−d ≤ Re s` gives `4d ≤ a−1`, bounding the real-centre pole by
  `(4d)⁻¹`. With the low-height exclusion of (S1), the middle pole terms are `O(d)`, and the 3–4–1 inequality
  produces negative margin `0.05/d ≥ 5·10⁴ log R` against an `O(log R)` error budget — so the closing
  `linarith` is robust to crude estimates.

---

## 4 Successive record artifacts

All five were accepted by the official comparator with standard axioms and carry `kept = true` on the public
curve. Table (local token counts; official scores from the public board):

| record # | attempt | artifact | tokens | official score | `running_best_pct` | lineage label |
|---:|---|---|---:|---:|---:|---|
| — | 96263 | previous record holder (Pi) | 3,286 | 64.5215 | 85.68 | — |
| 1 | 96272 | `Lean/record-96272/` | 3,274 | 64.5332 | 85.73 | prescribed-gap / further-weighted |
| 2 | 96276 | `Lean/fixes/localcert-fix/` | 3,208 | 64.6400 | 86.03 | local-certificate (repaired) |
| 3 | 96281 | `Lean/record-96281/` | 3,065 | 64.8928 | 86.64 | root-window |
| 4 | 96282 | `Lean/record-96282/` | 3,014 | 64.9800 | 86.87 | fused windows |
| 5 | 96283 | `Lean/smallest-scored-96283/` | 2,931 | 65.1339 | 87.24 | complex identity |

The following subsections describe the structural advance of each record artifact.

### 4.1 Record 1 — 3,274 tokens (official 64.5332; site 3,089 tok, −85.7 %)

**(B) Bottleneck.** The reference formalization (Alpöge, 21 files) must produce the Landau-type estimate
`−Re(f′/f)` for `ζ₁` near a putative zero by collecting *all* zeros in a disk into a finite product
`Π(w−ρ)^{m(ρ)}`, proving per-factor derivative lemmas (`hasDerivAt_prod_sub_pow`) and shuttling hand-written
Cauchy/Jensen estimates between files. The compressed artifact family replaced that library by five separate
scalar lemmas — `landau` (873), `scaledWindow` (269), `triple` (248), `zeroHeight` (114), `poleTerm_le` (66)
— plus a 643-token assembly, and these interfaces were what remained to be paid for.

**(M) Derivation.** The proof introduces `nld(f,z) := −Re(f′(z)/f(z))` and replaces the zero product by a
*strong induction on the growth constant*: for `f` entire on `B̄(0,1/2)`, `f(0) ≠ 0`, `‖f(w)‖ ≤ B‖f(0)‖`,
and all zeros of `f` in `B̄(0,1/6)` satisfying `Re ρ ≤ 0`, one proves for every `n` with `B < 2ⁿ` that

```
x + nld(f,0) ≤ 24·(log B + 1),      x = 0 or x = Re((−ρ)⁻¹) for a zero ρ ∈ B̄(0,1/6).
```

Peeling step: at a zero `ρ₀` put `g(w) := dslope(f,ρ₀)(w)`, so `f(w) = (w−ρ₀)g(w)` and `f(0) = −ρ₀g(0)`;
the growth constant of `g` is *exactly half* that of `f`, `B → B/2` (the distance to `ρ₀` cancels one factor
in the maximum-modulus bound), and the induction continues on `g`. Terminal step: if the inner disk is
zero-free, `f` has an analytic logarithm `u` with `Re u ≤ log B`, and Borel–Carathéodory gives
`|u′(0)| ≤ 2(Re u(0))/R`; a Lipschitz estimate converts this into the bound for `nld(f,0)`.

**(C) Why the ratio.** The peeling lemma (873 tokens) replaces the reference's entire zero-factorization
library; the second large replacement is the Mellin growth bound (≈742 tokens) which, as the ablation in §5
shows, costs ≈50 % less than the Euler–Maclaurin route. The platform records this artifact at **3,089 site
tokens = −85.7 %**, with the technique label *Perron/Mellin contour simplification + grind automation* and a
paper-style derivation titled *Borel–Carathéodory + analytic divided difference (`dslope`) recursive zero
peeling*; the record moment and that derivation are archived in `evidence/figures/`.

### 4.2 Record 2 — 3,208 tokens (official 64.64; site 3,024 tok, −86.0 %)

**(B) Bottleneck.** After record 1, the largest removable interface was the 3–4–1 certificate held as a
separate lemma `triple` (248 tokens): its statement, its proof of the pointwise inequality
`3 + 4cos θ + cos 2θ ≥ 0`, and the instantiation in the assembly all pay interface cost, and the assembly
(643) had to refer to it by name.

**(M) Derivation.** The certificate is a *termwise* statement: the von Mangoldt series has terms
`Λ(n)n^{−a}(3 + 4cos(t log n) + cos(2t log n)) ≥ 0`. Hence it can be produced inside the assembly as a single
`HasSum.nonneg` object, with no separate lemma; and the two uses of the quantity `D(z) = Re Σ Λ(n)n^{−z}`
(the certificate and the window bounds) are made to speak about the same atoms by a `change` step — a `def`
keeps its body invisible to `linarith`, so the certificate's `(LSeries …).re` atoms must be re-expressed as the
`D` atoms of the goal. (This atom mismatch is also why the un-repaired 3,179-token precursor did not compile.)

**(C) Why the ratio.** Measured: `triple` (248) disappears, the assembly grows 643 → 819 (+176), the `D`
abbreviation grows 21 → 27 (+6): net **−66** tokens, 3,274 → 3,208.

### 4.3 Record 3 — 3,065 tokens (official 64.8928; site 2,762 tok, −87.2 %)

**(B) Bottleneck.** Two auxiliary lemmas still duplicated information already contained in the Mellin
identity: `zeroHeight` (114) excluded zeros with `Re z ∈ (3/4,1)` and `|Im z| ≤ 1/2`, and `poleTerm_le` (66)
gave the crude bound `Re((z−1)⁻¹) ≤ 2`; both were stated, proved and instantiated separately.

**(M) Derivation.** The Mellin identity gives the low-height exclusion *directly*: `ζ₁(z) = 0` implies
`(z−1)R(z) = 1`, hence `Re z ≤ |z−1|`; combined with `Re z ≥ 3/4` this yields `|Im z| ≥ 1/2` in a few lines
inside the assembly. The same identity yields a *sharp* pole bound:
`Re((a+iγ−1)⁻¹) = (a−1)/((a−1)²+γ²) ≤ 5d/((4d)² + 1/4) ≤ 20d`, so the crude `≤ 2` lemma is unnecessary.
Both facts are thus consequences of the `remainder` object one already carries.

**(C) Why the ratio.** Measured: `zeroHeight` (114) and `poleTerm_le` (66) disappear, the assembly grows
819 → 876 (+57): net **−143** tokens, 3,208 → 3,065.

### 4.4 Record 4 — 3,014 tokens (official 64.98; site 2,842 tok, −86.9 %)

**(B) Bottleneck.** The window estimate survived as a lemma `scaledWindow` (263 tokens) with its own
statement and *three* instantiations (heights `0`, `Im s`, `2·Im s`); each instantiation paid interface and
argument-passing cost, and the assembly (876) had to name it.

**(M) Derivation.** The window estimate is an application of the peeling lemma at three centres
`a + iv` with growth ratio `B = R⁸/‖ζ₁(a+iv)‖`; since the growth hypothesis (`entireGrowth` on `Re ≥ 1/2`)
and the sharp pole inequality of record 3 are the same for all three centres, the three applications can be
inlined and share those two arguments. Mathematically nothing changes; the three uses become three
`have`-bindings of one lemma applied inline.

**(C) Why the ratio.** Measured: `scaledWindow` (263) disappears, the assembly grows 876 → 1,084 (+208):
net **−51** tokens, 3,065 → 3,014.

### 4.5 Record 5 — 2,931 tokens (official 65.1339; site 2,762 tok, −87.2 %)

**(B) Bottleneck.** The bridge `good` (94 tokens) and the abbreviation `D` (21 tokens) still mediated between
the Mellin/peeling results and the assembly: the logarithmic-derivative form
`ζ₁′/ζ₁ = (z−1)⁻¹ − Σ Λ(n)n^{−z}` was proved as one statement and `D` was one more object the arithmetic had
to pass through.

**(M) Derivation.** The assembly is reorganized around a *single normalized complex identity*: the entire
formula `ζ₁(s) = s(1 − (s−1)R(s))` is the only place where `ζ₁` is expanded, and the bridge is reduced to
substituting the von Mangoldt identity into the assembly's own expression, so the split into a named bridge
lemma plus a `D` abbreviation becomes unnecessary — the arithmetic works directly with the real parts of
`LSeries (Λ)`.

**(C) Why the ratio.** Measured: `good` 94 → 78 (−16), `D` disappears (−21), the assembly 1,084 → 1,038
(−46): net **−83** tokens, 3,014 → 2,931. The 2,931-token file is 16 top-level blocks: assembly 1,038,
peeling 872, Mellin module 742, bridge 78, witness/glue 201.
### 4.6 The published technique

> **`core1_borel_dslope` — "Borel–Carathéodory + Divided-Difference (DSlope) Zero Factorization"**
> (created for submission 96283).
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
> *Key signals*: `BorelCaratheodory`, `differentiableOn_dslope`, `grw`, `ZetaAsymp`. *Compression*: 21 → 1
> files, −87.2 % tokens.

---

## 5 Why the sequence converges: compression mechanisms

1. **Replace re-derivation by library primitive.** The peeling lemma (872 tokens) replaces zero factorization
   and contour estimates; the Mellin formula (742 tokens) replaces Euler–Maclaurin expansions. Together they
   are 1,614 of the final 2,931 tokens, while the reference spends 21 files on exactly these.
2. **Choose scales that make estimates crude.** `d = 2⁻²⁰/log R` gives negative margin `0.05/d ≥ 5·10⁴ log R`
   against `O(log R)` error. Sharp estimates are unnecessary, so the code avoids the reference's sharp but
   verbose bounds.
3. **Fuse interfaces and automate.** Window bounds are inlined; inequalities are normalized by `grw` and
   closed by `linarith`/`nlinarith`; the file has 10 top-level declarations and 55 `have`s, with tactic
   profile `simp` 38, `linarith` 18, `grind` 14, `norm_num` 10.

**Ablation.** The natural Euler–Maclaurin route to (S1) — prove
`Σ[(n+1)^{1−s} − (n+2)^{1−s} − (s−1)(n+1)^{−s}] = 1 − ζ₁(s)` and bound the series — costs
264 + 540 + 95 + 158 = **1,057 tokens** versus ≈715 for Mellin, and yields no cheap zero exclusion. Two valid
mathematical routes differ by ~50 % in formal cost: the compression is structural, not cosmetic.

---

## 6 Official evaluation

Scores and curve statistics for all submissions of the account are given in §4's table and in
`docs/EVIDENCE.md`: the record sequence is 64.5332 → 64.6400 → 64.8928 → 64.9800 → 65.1339, with
`running_best_pct` 85.73 → 86.03 → 86.64 → 86.87 → 87.24. Earlier submissions (3,315 tokens, score 64.4685)
were not kept; a 2,843-token artifact was submitted with scoring pending at release. Two artifacts
(3,242 and 2,880 tokens) compile locally with clean axioms but were **rejected by the official comparator**;
they are archived as a validity boundary. Inverting the official score formula reproduces the token counts
to ±8 (e.g. 65.1339 ⇒ ≈2,932 vs 2,931), validating the accounting used here. On the benchmark's *model ×
harness* leaderboard, Deepseek V4.1-Flash / DeepSeek Harness ranks first (composite index 64.50; average
compression 84.2 %), ahead of GPT-6.2 Astra / ChatGPT Desktop (63.83; 80.2 %), Gemini 4 Neon (58.61) and
Claude Opus 5.5 (55.83); see `evidence/figures/leaderboard-model-harness.png` and
`evidence/figures/leaderboard-avg-compression.png`.

---

## 7 Discussion and conclusion

The five record artifacts are best read as a *single* mathematical construction acquiring a better interface
at each step: prescribe the witness gap; tie the scale to the assumed real part; use the pole side for the
low-height information; fuse the windows and sharpen the pole bounds; finally, carry one identity through the
assembly. None of the steps changes the theorem; each removes a layer of interface or a distinction that the
classical proof does not need. The general lesson for formalized analysis is that **proof size is dominated
by re-derivation and interface overhead, and library-native reformulation is the way to compress it**.
Limitations: one pillar (1/5) of a formalization programme, not the Riemann Hypothesis; tokens are a
benchmark-specific proxy for structure, not a measure of mathematical depth; several savings are Mathlib-API
savings, so the result measures library/proof co-maturity. Next steps target 2,500 tokens: weaken the
low-height exclusion (`|Im s| ≥ 1/2` → `|Im s| ≥ 32d`) with a two-branch scale (≈ −110), merge the two
logarithmic inputs into one von Mangoldt object (≈ −130), and restate the peeling lemma with `logDeriv`
(≈ −100).

**Artifact and reproduction.** Repository contents: the five record artifacts plus the rejected and pending
ones, the token meter, the compile + axiom-audit harness, official evidence snapshots, an independent Case
A/B architecture, and this paper in English and Chinese.

```bash
python3 tools/token_count.py Lean/smallest-scored-96283/Solution.lean   # -> 2931
LEAN_HOME=... MATHLIB=... tools/compile_solution.sh Lean/smallest-scored-96283/Solution.lean demo
#   expected: compile rc=0;  #print axioms -> [propext, Classical.choice, Quot.sound]
```

**Provenance.** Results were produced under the account *Yin-Kai Yu (余荫铠)* by a collaborative research
track of two AI agents (DeepSeek Harness / Deepseek V4.1-Flash and ChatGPT Desktop / GPT-6.2 Astra); the
submissions, measurements and this paper belong to that account's record.

**Citation.**

```bibtex
@misc{yu2026zfrcompress,
  author       = {Yu, Yin-Kai},
  title        = {Library-Native Proof Compression: Successive Record Formalizations of the Classical Zero-Free Region in {Lean}~4},
  year         = {2026},
  howpublished = {GitHub repository, artifact release v1.0},
  url          = {https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4},
  note         = {Five record refreshes; best official score 65.1339 (submission 96283), curve kept=true},
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
[13] Agentic Science Challenge, *Lean 4 Verification (RH Core Pillar 1/5)* (baseline `T₀ = 21,641`), 2026.
[14] Public Proof Compression Progress Curve, <https://riemann.verifytask.cn/>, 2026.

## Appendix A. Mathlib declarations used

`borelCaratheodory_zero` (`Analysis/Complex/BorelCaratheodory.lean:86`),
`norm_deriv_le_div_of_mapsTo_ball` (`Analysis/Complex/Schwarz.lean:250`),
`differentiableOn_dslope` (`Analysis/Complex/RemovableSingularity.lean:60`),
`logDeriv_eqOn_iff`, `logDeriv_mul` (`Analysis/Calculus/LogDeriv.lean`),
`integral_Ioi_cpow_of_lt` (`Analysis/SpecialFunctions/ImproperIntegrals.lean:251`),
`LSeries_vonMangoldt_eq_deriv_riemannZeta_div` (`NumberTheory/LSeries/Dirichlet.lean:434`),
`norm_LFunction_product_ge_one` (`NumberTheory/LSeries/Nonvanishing.lean:310`),
`deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add` (`NumberTheory/Harmonic/ZetaAsymp.lean:585`).

## Appendix B. Artifact manifest

`Lean/record-96272/`, `Lean/fixes/localcert-fix/`, `Lean/record-96281/`, `Lean/record-96282/`,
`Lean/smallest-scored-96283/` (the five record artifacts), `Lean/smallest-verified/` (2,843 tokens,
pending), `Lean/failed-96274-v22.lean` (rejected), `research/caseAB/`, `tools/`, `evidence/`, `docs/`,
`paper/main_en.md`, `paper/main_zh.md`.
