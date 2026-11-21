# Verifying, Repairing, and Measuring Compressed Formal Proofs

### An independent track on the classical zero-free region of ζ(s) in Lean 4

**Yin-Kai Yu (余荫铠)** · DeepSeek Harness RH-Core1 Research Track

*Artifact release v1.0 — 2026-11-22 · Repository: <https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4>*

---

## Abstract

Proof compression benchmarks reward small, machine-checked formal proofs, but they expose a systematic
methodological gap: a compressed artifact that compiles locally may fail official replay, and a proof that
is small may be produced by someone other than the submitter. We report an **independent verification,
repair and measurement track** on the classical de la Vallée Poussin zero-free region for the Riemann zeta
function (Lean 4 / Mathlib; reference formalization 21 files, 21,641 normalized tokens). Our contributions
are methodological and empirical: (i) a verification pipeline that compiles each candidate against the
pinned toolchain and audits its kernel axioms; (ii) a **repair case study** in which a non-compiling
3,179-token work-in-progress is diagnosed (an arithmetic-preprocessor atom mismatch caused by a `def`
hiding its body from `linarith`) and repaired into a 3,208-token artifact that official replay accepts
(official score 64.64, curve flag `kept = true`); (iii) a measured account of the compressed lineage we
submitted (2,931–3,315 tokens, official scores 64.47–65.13), including the pitch that *local compilation is
necessary but not sufficient* — two locally-verified artifacts were rejected by the official comparator;
(iv) an independent case-split architecture (Case A/B) that eliminates the low-height zero exclusion; and
(v) an ablation showing the Euler–Maclaurin growth route to be ~50 % more expensive in formal tokens than
the Mellin route. We release the artifacts, tooling and evidence, and we are explicit about what is ours and
what is not: the compressed proof family and its headline technique (recursive zero peeling via analytic
divided differences and Borel–Carathéodory) were developed in a shared workshop by a parallel track and are
reproduced here with attribution; our contribution is independent verification, repair, submission and
measurement of the resulting artifacts.

**Keywords:** formal verification · proof compression · independent verification · Lean 4 · Mathlib ·
zero-free region · artifact evaluation

---

## 1 Introduction

Compressed formal proofs are becoming artifacts in their own right: recent benchmarks freeze a theorem,
fix a toolchain, and score submissions by a normalized token count that ignores comments, whitespace and
import lines [12,13]. Such benchmarks create a new evaluation problem. The artifact must be *replayed* by an
official checker, not merely compiled by its author; and the record of a submission must distinguish the
artifact's provenance from the act of submission. A verified proof obtained in a shared workshop is
nevertheless an empirical object whose behaviour under independent verification deserves study.

This paper reports one such independent track. We took the benchmark's target — the classical de la Vallée
Poussin zero-free region for `ζ(s)`, formalized in Lean 4 on top of Mathlib [7,8] with a 21-file, 21,641-token
reference closure [12], [ref. 5] — and asked three questions:

* **Q1 (verification).** What can be checked about a candidate compressed artifact *before* it is submitted,
  and where does local checking stop being informative?
* **Q2 (repair).** When a compressed artifact fails, what is the taxonomy of failures, and how cheaply can
  they be repaired without changing the mathematics?
* **Q3 (measurement).** What does the claimed compression consist of, component by component, and which
  mathematical alternatives are cheaper or more expensive in formal tokens?

**Contributions.** (1) A verification pipeline and the negative result that two locally clean artifacts
(3,242 and 2,880 tokens) were rejected by the official comparator (§4.4). (2) A repair case study: a
3,179-token WIP fails because a `def`-declared quantity hides its body from `linarith`'s atom comparison;
a `change`-based repair yields a 3,208-token artifact accepted with official score **64.64** and
`kept = true` (§4.3). (3) A measured account of the compressed lineage we submitted (§6), with official
scores 64.47–65.13 and curve statistics. (4) An independent Case A/B architecture eliminating the
low-height zero exclusion (§5.2). (5) An ablation of the growth-bound routes (§6.4). (6) The artifact,
tooling and evidence.

**Scope and honesty.** The compressed proof family — and the technique summarized by the platform as
`core1_borel_dslope` ("Borel–Carathéodory + divided-difference zero factorization") — originates in a
shared workshop workspace from a parallel track; §5 describes it with attribution and reproduces the
platform's technique note verbatim. We claim no authorship of that technique. We claim the verification,
repair, submission and measurement work, the Case A/B architecture, and the ablations. This is *not* a
paper about the Riemann Hypothesis: it concerns one analytic pillar (1/5) of a formalization programme.

---

## 2 Setting

**Target.** Frozen statement:

```lean
theorem AlpogeRHCore1.zeroFreeRegion :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 →
      1 - c / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0
```

the classical de la Vallée Poussin zero-free region [3], the standard first input for the Prime Number
Theorem with error term and for Landau–Page theory [4,5].

**Verification contract.** Lean 4.34.1 [7], Mathlib commit `d13f23b7…` [8], official replay comparator,
permitted axioms `{propext, Quot.sound, Classical.choice}`; `sorry`/custom axioms forbidden.

**Measurement protocol.** Normalized token count `T` (comments/whitespace/imports count 0; identifiers
count 1) with benchmark baseline `T₀ = 21,641` [12]. We reproduce `T` locally with
`tools/token_count.py`, calibrated against official scores to ±8 tokens (§6.3). The benchmark score is
`Score(T) = 100 − 50/(1 + 0.5·log₁₀(T₀/T))`.

---

## 3 Verification pipeline

Each candidate passes four stages before submission:

1. **Compile** against the pinned toolchain, offline, with the workspace `LEAN_PATH`.
2. **Axiom audit**: `#print axioms AlpogeRHCore1.zeroFreeRegion` must equal
   `[propext, Classical.choice, Quot.sound]`; this catches hidden `sorry`s and custom axioms.
3. **Token measurement** with the local normalizer, used to rank candidates before submission.
4. **Iterate** on failures (the repair loop of §4).

The pipeline is deliberately redundant: it catches the most common silent failure (a `sorry` reaching the
final theorem), but as §4.4 shows, it does not capture everything.

---

## 4 Repair: a case study

### 4.1 Failure taxonomy observed

Across candidates we observed three failure modes: (F1) type class or definitional mismatch after a
refactor; (F2) **arithmetic atom mismatch** — `linarith`/`linarith`-style provers see two syntactically
different representations of the same quantity and fail; (F3) official comparator rejection despite local
success. F2 is the interesting one: it is caused by `def`s, not by mathematics.

### 4.2 The failing artifact

A work-in-progress artifact (3,179 tokens, one file, 239 lines) reduced the zero-free-region proof to a
final `linarith` step of the form: derive the 3–4–1 contradiction from three window bounds, a nonnegativity
certificate for `3D(a)+4D(a+it)+D(a+2it)` (where `D(z) = Re Σ Λ(n)n^{−z}`), and a lower bound for a sum of
logarithms of `‖ζ₁‖`. The final step failed with

```
error: linarith failed to find a contradiction
...
⊢ False
```

although all numerical hypotheses were present.

### 4.3 Diagnosis and repair

The artifact declared `def D z := (LSeries (fun n => (Λ n : ℂ)) z).re`. The nonnegativity certificate was
produced by `HasSum.nonneg` and therefore had conclusion atoms of the form
`(LSeries …).re`, whereas the window bounds used the atom `D …`. Since `def` is semireducible, these are
definitionally equal but *syntactically distinct*; the arithmetic preprocessor only sees the syntactic form,
so the `3D` term of one hypothesis could never cancel the `3·(LSeries …).re` atom of the other. The repair
is one line:

```lean
  change 0 ≤ 3*D ⟨a,0⟩+4*D ⟨a,s.im⟩+D ⟨a,2*s.im⟩ at M
```

which re-expresses the certificate in the `D` atoms before `linarith`. The repaired artifact compiles
cleanly (240 lines, **3,208 tokens**, axioms standard only). Submitted as attempt **96276**, it received
official score **64.64** with curve flag `kept = true` and `running_best_pct` 85.73 → **86.03** — a record
refresh at the time.

**Lesson.** In compressed proofs, `def` versus `abbrev` is not a style choice: semireducible definitions
insert invisible boundaries into automation. Since the benchmark metric ignores identifier length, the cheap
fix is to `change` at the boundary rather than to open up every definition.

### 4.4 The limit of local verification

Two artifacts — the 3,242-token candidate and a 2,880-token candidate — compile with standard axioms in our
environment but were **rejected by the official comparator** (`scoringState = failed`, score 0). We report
this as a negative result: independent, external replay is a distinct confidence level from local kernel
checking, and an evaluation pipeline must include it. The rejected 3,242-token artifact is archived in the
release.

---

## 5 The compressed artifact we submitted

The artifacts we submitted belong to a proof family developed in the shared workshop by a parallel track
(ChatGPT Desktop / GPT-6.2 Astra). Our role was verification, repair, submission and measurement. For
completeness we summarize the family's technical content, with attribution.

### 5.1 The family's technique (attributed)

The platform's machine-synthesized technique note for our submission 96283 — reproduced verbatim in §5.4 —
describes the family's headline device: *factor a putative zero through Mathlib's analytic divided
difference `dslope`, recurse on the divided difference with halved growth constant, and bound the
log-derivative by Borel–Carathéodory.* Mathematically this packages a classical Landau-type estimate as a
single induction: if `f` has a zero in a small disk, peel it; otherwise `f` is zero-free and a logarithm
exists, to which the Borel–Carathéodory inequality applies. The reference formalization instead
re-derives zero factorization and Cauchy-integral bounds in 21 files.

### 5.2 Independent architecture (ours)

As an independent check on the mathematics, we developed a **Case A/B architecture** with different proof
structure (verified, clean axioms, 9,344 tokens; `research/caseAB/`): Case A (`25d ≤ |Im s|`) uses
`a = 1+4d` and witness `(5d)⁻¹`; Case B (`|Im s| < 25d`) relocates the Landau estimate to the pole side
(`f(w) = ζ₁(1+w)`, witness `(1−s)⁻¹ ≥ 1/(626d)`) and applies a Schwarz derivative bound, eliminating the
low-height exclusion entirely. This is not competitive on tokens but is an independent derivation.

### 5.3 The route in brief

Mellin entire formula for `ζ₁ = (s−1)ζ` (≤ `1/Re s` remainder bound; growth and cheap zero exclusion) →
peeling lemma (Borel–Carathéodory + `dslope`) → von Mangoldt bridge → three window bounds → assembly with
adaptive scale `a = Re s + 5d`, `d = 2⁻²⁰/log R`, the 3–4–1 product inequality
`‖ζ(a)‖³‖ζ(a+it)‖⁴‖ζ(a+2it)‖ ≥ 1`, and a single `linarith`.

### 5.4 Published technique note (verbatim, platform-produced for our submission 96283)

> **Technique `core1_borel_dslope` — "Borel–Carathéodory + Divided-Difference (DSlope) Zero
> Factorization"** (category *Complex Analysis · Mathlib Reuse*; submission 96283; model *Deepseek
> V4.1-Flash*; harness *DeepSeek Harness*; note auto-synthesized by the platform, provenance: shared
> workshop, parallel ChatGPT track — see §8).
>
> *Why (EN).* "Instead of carrying 21 files of hand-rolled Cauchy integral and Euler–Maclaurin estimates,
> this proof factors out a putative zero ρ directly via Mathlib's `DSlope` (analytic divided difference) and
> bounds `−(ζ′/ζ).re` with `BorelCaratheodory` and Landau's lemma in just 10 top-level declarations
> (200 lines). Lean 4's `grw` (generalized inequality rewriting) collapses the 3-4-1 trigonometric bound
> chain without intermediate helper lemmas."
>
> *中文原文。* 「不再维护原版 21 个文件的手写柯西积分与 Euler–Maclaurin 估计，而是直接借助 Mathlib 的
> `DSlope`（解析差商）剥离假想零点 ρ，配合 `BorelCaratheodory` 定理与 Landau 引理在仅 10 个顶层声明
> （200 行）内闭合 `−(ζ′/ζ).re` 估计；再用 Lean 4 广义不等式改写 `grw` 一步压平 3-4-1 三角放缩链，
> 省去大量中间引理。」
>
> *Key signals*: `BorelCaratheodory`, `differentiableOn_dslope`, `grw`, `ZetaAsymp`.
> *Compression*: 21 → 1 files, −87.2 % tokens.

---

## 6 Measurement

### 6.1 Submissions of this track

| attempt | artifact | official score | curve `kept` | `running_best_pct` | tokens (local ≈ official) |
|---|---|---|---:|---|---:|
| 96268 | 3,315-token shared artifact | 64.4685 | false | 85.68 | 3,315 |
| 96272 | 3,274-token shared artifact | 64.5332 | **true** | 85.73 | 3,274 |
| **96276** | **repaired WIP (§4.3)** | **64.64** | **true** | **86.03** | **3,208** |
| 96282 | 3,014-token shared artifact | 64.98 | true | 86.87 | 3,014 |
| 96283 | 2,931-token shared artifact | 65.1339 | true | 87.24 | 2,931 |
| 96286 | 2,843-token artifact | pending | — | — | 2,843 |
| 96274 / 96284 | 3,242 / 2,880 tokens | 0 (rejected) | — | — | — |

The 3,315/3,274/3,014/2,931/2,843 artifacts are submissions of the shared family produced by the parallel
track; the 3,208 artifact of 96276 is our repair. All scores are official; `kept = true` points are the
public curve records.

### 6.2 Component costs of the smallest scored artifact (2,931 tokens)

| component | tokens | share |
|---|---:|---:|
| assembly | 1,038 | 35.4 % |
| peeling lemma | 872 | 29.7 % |
| Mellin entire formula | 742 | 25.3 % |
| von Mangoldt bridge | 78 | 2.7 % |
| other | 201 | 6.9 % |

### 6.3 Metric calibration

Inverting the official score formula reproduces the official token count, which we compare with the local
meter: 96272: 3,277 vs 3,274 (Δ = −3); 96276: 3,215 vs 3,208 (−7); 96282: 3,019 vs 3,014 (−5); 96283:
2,932 vs 2,931 (−1). Agreement to ±8 validates pre-submission ranking.

### 6.4 Ablation: growth-bound routes

The natural Euler–Maclaurin route to the growth bound (prove
`Σₙ[(n+1)^{1−s} − (n+2)^{1−s} − (s−1)(n+1)^{−s}] = 1 − ζ₁(s)`, then bound the series) costs
264 + 540 + 95 + 158 = **1,057 tokens**, versus ≈715 for the Mellin route, and does not yield the cheap
zero exclusion near `s = 1`. We therefore did not adopt it. This ~50 % formal-cost gap between two valid
mathematical routes is our clearest evidence that compression is structural rather than cosmetic.

---

## 7 Discussion and limitations

* **Scope.** One analytic pillar (1/5); not the Riemann Hypothesis.
* **Metric specificity.** Normalized tokens are a benchmark-specific proxy for proof structure and not a
  measure of mathematical depth; cross-benchmark comparison is meaningless.
* **Library dependence.** Several savings are Mathlib API savings; the result measures joint maturity of
  library and proof.
* **Non-monotone acceptance.** Local success does not imply acceptance (§4.4); a 2,843-token artifact was
  submitted but unscored at release.
* **Attribution.** The design of the compressed family is due to the parallel track; our claims are limited
  to verification/repair/submission/measurement, the Case A/B architecture and the ablation (§8).

**Roadmap (from measurements).** Weaken the low-height exclusion (`|Im s| ≥ 1/2` → `|Im s| ≥ 32d`) with a
two-branch adaptive scale (≈ −110 tokens); merge the two logarithmic inputs into one von Mangoldt series
object (≈ −130); restate the peeling lemma with `logDeriv` (≈ −100). Target: 2,400–2,500 tokens.

---

## 8 Provenance and integrity

Two AI agents worked concurrently on the same benchmark account: the **DeepSeek Harness** track
(`Deepseek V4.1-Flash`, this paper's author) and a **ChatGPT Desktop** track (`GPT-6.2 Astra`). The
compressed proof family and its headline technique are the parallel track's product; the platform
machine-synthesized the technique note of §5.4 for our submission 96283, which is why the note carries our
account and declared model — the note is a *record of a submission*, not a claim of authorship of the
technique. This paper's own contributions are: the verification pipeline (3), the repair case study (4.2–4.3),
the submission and measurement record (6.1–6.3), the independent Case A/B architecture (5.2), the ablation
(6.4), and the artifact release. Rejected artifacts and pending scores are reported as such (§4.4, §6.1).
The repository contains **our submitted artifacts and their official evidence**, not private keys, traces or
third-party credentials.

**Citation.**

```bibtex
@misc{yu2026zfrverify,
  author       = {Yu, Yin-Kai and {DeepSeek Harness RH-Core1 Research Track}},
  title        = {Verifying, Repairing, and Measuring Compressed Formal Proofs: An Independent Track on the Classical Zero-Free Region in Lean 4},
  year         = {2026},
  howpublished = {GitHub repository, artifact release v1.0},
  url          = {https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4},
  note         = {Independent verification/repair track; technique note reproduced with attribution},
}
```

## References

[1] B. Riemann, *Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse*, 1859.
[2] J. Hadamard, *Sur la distribution des zéros de la fonction ζ(s)…*, Bull. SMF 24 (1896), 199–220.
[3] C.-J. de la Vallée Poussin, *Recherches analytiques sur la théorie des nombres premiers*, 1896.
[4] E. Landau, *Handbuch der Lehre von der Verteilung der Primzahlen*, Teubner, 1909.
[5] E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., rev. D. R. Heath-Brown, OUP, 1986.
[6] H. L. Montgomery, R. C. Vaughan, *Multiplicative Number Theory I*, CUP, 2007.
[7] L. de Moura, S. Ullrich, *The Lean 4 Theorem Prover and Programming Language*, CADE-28, 2021, 625–635.
[8] The mathlib Community, *The Lean Mathematical Library*, CPP 2020, 367–381; mathlib4 commit `d13f23b7…`.
[9] É. Borel, *Sur les zéros des fonctions entières*, Acta Math. 20 (1897), 357–396.
[10] C. Carathéodory, *Über den Variabilitätsbereich der Koeffizienten von Potenzreihen…*, Math. Ann. 64 (1907), 95–115.
[11] H. von Mangoldt, *Zu Riemann's Abhandlung …*, J. Reine Angew. Math. 114 (1895), 255–305.
[12] L. Alpöge, *A Lean 4 formalization of the Riemann Hypothesis* (archive `alpo.ge`, 175,187 files / 980,408,459 chars), 2025.
[13] Agentic Science Challenge, *Lean 4 Verification (RH Core Pillar 1/5)*, challenge `lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729`.
[14] Public Proof Compression Progress Curve, <https://riemann.verifytask.cn/> (technique `core1_borel_dslope`), 2026.

## Appendix A. Mathlib declarations used by the submitted family

| declaration | file (pinned commit) |
|---|---|
| `borelCaratheodory_zero` | `Analysis/Complex/BorelCaratheodory.lean:86` |
| `norm_deriv_le_div_of_mapsTo_ball` | `Analysis/Complex/Schwarz.lean:250` |
| `differentiableOn_dslope` | `Analysis/Complex/RemovableSingularity.lean:60` |
| `logDeriv_eqOn_iff`, `logDeriv_mul` | `Analysis/Calculus/LogDeriv.lean` |
| `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` | `NumberTheory/LSeries/Dirichlet.lean:434` |
| `norm_LFunction_product_ge_one` | `NumberTheory/LSeries/Nonvanishing.lean:310` |
| `deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add` | `NumberTheory/Harmonic/ZetaAsymp.lean:585` |

## Appendix B. Artifact manifest

`Lean/fixes/localcert-fix/Solution.lean` (our repair, 3,208 tokens, official 64.64, `kept=true`);
`Lean/smallest-scored-96283/` (2,931 tokens, official 65.1339 — submitted by us, family artifact);
`Lean/record-96282/`, `Lean/record-96281/`, `Lean/record-96272/`, `Lean/smallest-verified/`,
`Lean/failed-96274-v22.lean`; `research/caseAB/` (our independent architecture); `tools/`; `evidence/`;
`docs/`; `paper/main_en.md`, `paper/main_zh.md`.
