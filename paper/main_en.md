# Library-Native Proof Compression: Successive Record Formalizations of the Classical Zero-Free Region in Lean 4

**Yin-Kai Yu (余荫铠)** — DeepSeek Harness × ChatGPT Desktop collaborative research track

*Artifact release v1.0 · 2026-11-22 · <https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4>*

## Abstract

The classical zero-free region is a few pages of textbook analysis, yet its reference Lean 4 formalization is
21 files / 21,641 normalized tokens. We report five successive record-breaking compressions of the same
theorem to a **single file of 2,931 tokens** and analyze each one by (B) the bottleneck it removed, (M) the
core derivation it introduced, and (C) the measured token delta. The resulting form is
$\zeta(s)\neq 0$ for $\mathrm{Re}(s)\ge 1-c/\log(|\mathrm{Im}(s)|+2)$, packaged as
$5+2+1=8$ declarations: a Mellin entire formula for $\zeta_1=(s-1)\zeta$, a recursive zero-peeling lemma
built from analytic divided differences (`dslope`) and Borel–Carathéodory, a von Mangoldt bridge into the
$3+4\cos\theta+\cos 2\theta\ge 0$ inequality, and an adaptive-scale assembly
$a=\mathrm{Re}(s)+5d$, $d=2^{-20}/\log R$. Official scores rise
$64.5332\to 64.6400\to 64.8928\to 64.9800\to 65.1339$ with curve flag `kept=true` throughout; an ablation
shows the natural Euler–Maclaurin growth route costs $\approx 50\%$ more tokens.

**Keywords:** formalized analysis · Lean 4 · Mathlib · proof compression · zero-free region ·
analytic divided differences · Borel–Carathéodory

## 1 Introduction

Formal proofs of analytic number theory are large mostly because they *re-derive* machinery — zero
factorization, contour estimates, Euler–Maclaurin expansions — that a modern library already provides. The
benchmark used here makes this measurable: the statement is frozen, the environment is fixed
(Lean 4.34.1 + Mathlib, replay-based comparator, permitted axioms
$\{\texttt{propext},\texttt{Quot.sound},\texttt{Classical.choice}\}$), and the score depends only on the
normalized Lean token count $T$ (comments, whitespace and `import` lines are free; identifier length is
ignored). We take the classical de la Vallée Poussin zero-free region, whose reference closure is
$T_0=21{,}641$ tokens over 21 files, and compress it successively. The paper's subject is the mathematics of
each step: why the replaced machinery was expensive, what replaces it, and what the replacements cost.

## 2 Setting

Target (frozen):

$$
\exists\,c>0:\quad \forall s\in\mathbb{C},\ s\neq 1,\quad
\mathrm{Re}(s)\ \ge\ 1-\frac{c}{\log\left(|\mathrm{Im}(s)|+2\right)}
\ \Longrightarrow\ \zeta(s)\neq 0 .
$$

Metric: normalized tokens $T$ with baseline $T_0=21{,}641$ and score

$$
S(T)\;=\;100-\frac{50}{1+\frac{1}{2}\log_{10}\left(T_0/T\right)} .
$$

Our local meter reproduces the official count to $\pm 8$ tokens, so the accounting below is comparable to
official numbers.

## 3 The mathematical core

Write $\zeta_1(s)=(s-1)\zeta(s)$, which is entire.

**Mellin entire formula.** For $\mathrm{Re}(s)>0$,

$$
\zeta_1(s)\;=\;s\left(1-(s-1)R(s)\right),\qquad
\lVert R(s)\rVert\ \le\ \frac{1}{\mathrm{Re}(s)} ,
$$

where $R$ is the Mellin transform of the fractional-part tail. It yields (i) the polynomial growth bound
$\lVert z\rVert\le 4R\Rightarrow \lVert\zeta_1(z)\rVert\le R^8$ on $\mathrm{Re}(z)\ge \frac{1}{2}$, and
(ii) a zero exclusion near $s=1$: if $\zeta_1(z)=0$ then $(z-1)R(z)=1$, hence
$\mathrm{Re}(z)\le |z-1|$, so zeros with $\mathrm{Re}(z)\ge \frac{3}{4}$ satisfy
$|\mathrm{Im}(z)|\ge \frac{1}{2}$.

**Recursive zero peeling.** Put $\mathrm{nld}(f,z):=-\mathrm{Re}\left(f'(z)/f(z)\right)$. For entire $f$
with $f(0)\neq 0$, growth $\lVert f(w)\rVert\le B\lVert f(0)\rVert$ on
$\overline{B}(0,\frac{1}{2})$, and all zeros of $f$ in $\overline{B}(0,\frac{1}{6})$ in the closed left
half-plane, one proves by strong induction on $n$ (for $B<2^n$) that

$$
x+\mathrm{nld}(f,0)\ \le\ 24\log B+24 ,
$$

where $x=0$, or $x=\mathrm{Re}\left((-\rho)^{-1}\right)$ for a zero
$\rho\in\overline{B}(0,\frac{1}{6})$. The peeling step at a zero $\rho_0$ is

$$
g(w):=\mathrm{dslope}(f,\rho_0)(w),\qquad
f(w)=(w-\rho_0)\,g(w),\qquad f(0)=-\rho_0\,g(0),
$$

and the growth constant of $g$ is exactly half that of $f$, $B\mapsto B/2$; the terminal branch (zero-free
inner disk) is the Borel–Carathéodory estimate for an analytic logarithm.

**Bridge and assembly.** On $\mathrm{Re}(z)>1$,
$\mathrm{Re}\left(\zeta_1'/\zeta_1\right)=\mathrm{Re}\left((z-1)^{-1}\right)+\mathrm{Re}\sum\Lambda(n)n^{-z}$,
which turns the peeling bounds into the classical inequality $3D(a)+4D(a+t)+D(a+2t)\ge 0$,
$D(z)=\mathrm{Re}\sum\Lambda(n)n^{-z}$ (equivalently $3+4\cos\theta+\cos 2\theta\ge 0$). With
$R=|\mathrm{Im}(s)|+2$, $d=2^{-20}/\log R$ and the adaptive scale $a:=\mathrm{Re}(s)+5d$, the witness zero
lies exactly $5d$ from the centre, so $x=(5d)^{-1}$ is sharp; $\mathrm{Re}(s)\ge 1-d$ gives $a-1\ge 4d$, and

$$
\mathrm{Re}\left((a+i\gamma-1)^{-1}\right)\;=\;\frac{a-1}{(a-1)^2+\gamma^2}
\;\le\;\frac{5d}{(4d)^2+\frac{1}{4}}\;\le\;20d .
$$

The negative margin of the 3–4–1 combination is therefore

$$
\left(\frac{4}{5}-\frac{3}{4}\right)\frac{1}{d}\;=\;\frac{0.05}{d}\;\ge\;5\cdot 10^{4}\log R ,
$$

against an error budget of $O(\log R)$; every estimate may be crude and one `linarith` closes the proof.

## 4 The five records

| # | attempt | tokens | official score | `running_best_pct` | artifact |
|---:|---|---:|---:|---:|---|
| — | 96263 | 3,286 | 64.5215 | 85.68 | previous holder |
| 1 | 96272 | 3,274 | 64.5332 | 85.73 | `Lean/record-96272/` |
| 2 | 96276 | 3,208 | 64.6400 | 86.03 | `Lean/fixes/localcert-fix/` |
| 3 | 96281 | 3,065 | 64.8928 | 86.64 | `Lean/record-96281/` |
| 4 | 96282 | 3,014 | 64.9800 | 86.87 | `Lean/record-96282/` |
| 5 | 96283 | **2,931** | **65.1339** | **87.24** | `Lean/smallest-scored-96283/` |

**(B) bottleneck, (M) derivation, (C) measured delta.**

**Record 1.** (B) The reference collects *all* zeros of the disk into a finite product
$\prod(w-\rho)^{m(\rho)}$ with per-factor derivative lemmas and hand-written Cauchy/Jensen estimates across
files; the artifact family still paid five separate interfaces (`landau` 873, `scaledWindow` 269,
`triple` 248, `zeroHeight` 114, `poleTerm_le` 66) plus a 643-token assembly.
(M) The peeling lemma above replaces the zero product by strong induction with $B\mapsto B/2$.
(C) One 873-token lemma replaces the factorization library; the Mellin formula ($\approx 742$) replaces the
Euler–Maclaurin growth machinery. Platform: $3{,}089$ site tokens, $-85.7\%$, technique label
*Perron/Mellin contour simplification + grind automation*.

**Record 2.** (B) The $3$–$4$–$1$ certificate was a separate lemma `triple` (248) with its own statement and
instantiation. (M) The certificate is termwise: each von Mangoldt term is
$\Lambda(n)n^{-a}\left(3+4\cos(t\log n)+\cos(2t\log n)\right)\ge 0$, so it can be produced *inside* the
assembly as one `HasSum.nonneg` object; the `def`-hidden atom mismatch is repaired by a `change` so that the
certificate and the window bounds speak about the same atoms. (C) `triple` disappears, the assembly grows
$643\to 819$: net $-66$ tokens.

**Record 3.** (B) `zeroHeight` (114) and `poleTerm_le` (66) duplicated information already in the identity.
(M) The exclusion $\zeta_1(z)=0\Rightarrow \mathrm{Re}(z)\le|z-1|\Rightarrow|\mathrm{Im}(z)|\ge\frac{1}{2}$
and the sharp bound
$\mathrm{Re}\left((a+i\gamma-1)^{-1}\right)\le (a-1)/\gamma^2\le 20d$ are both consequences of the same
remainder $R$. (C) Both lemmas disappear, assembly grows $819\to 876$: net $-143$ tokens.

**Record 4.** (B) `scaledWindow` (263) was instantiated at three heights, paying interface cost three times.
(M) The three applications share the growth hypothesis and the sharp pole inequality, so they can be inlined
as three `have`-bindings of one lemma. (C) `scaledWindow` disappears, assembly grows $876\to 1{,}084$: net
$-51$ tokens.

**Record 5.** (B) `good` (94) and the abbreviation `D` (21) still mediated between the results and the
assembly. (M) The assembly is reorganized around one normalized identity
$\zeta_1(s)=s\left(1-(s-1)R(s)\right)$, so the bridge reduces to a substitution and the arithmetic works
directly with $\mathrm{Re}$ parts of the von Mangoldt series. (C) `good` $94\to 78$, `D` disappears, assembly
$1{,}084\to 1{,}038$: net $-83$ tokens.

## 5 Mechanisms and ablation

Three principles explain the sequence: (P1) replace re-derivation by a library primitive; (P2) choose scales
so that estimates may be crude — the margin $0.05/d\ge 5\cdot 10^4\log R$ makes the closing arithmetic
robust; (P3) fuse interfaces and automate — $10$ top-level declarations, $55$ `have`s, tactic profile
`simp` $38$, `linarith` $18$, `grind` $14$, `norm_num` $10$.

**Ablation.** The natural Euler–Maclaurin route to the growth bound proves
$\sum_n\left[(n+1)^{1-s}-(n+2)^{1-s}-(s-1)(n+1)^{-s}\right]=1-\zeta_1(s)$ and bounds the series. Measured
cost: term bound $264$ + growth theorem $540$ + integral identity $95$ + auxiliary $158$ $=1{,}057$ tokens,
versus $\approx 715$ for Mellin, and it yields no cheap zero exclusion. Two valid routes differ by
$\approx 50\%$ in formal cost: the compression is structural, not cosmetic.

## 6 Official evaluation

The record sequence is the table of §4; `running_best_pct` rises
$85.73\to 86.03\to 86.64\to 86.87\to 87.24$. Inverting the score formula reproduces the token counts
($65.1339\Rightarrow \approx 2{,}932$ vs $2{,}931$ local), validating the accounting. Two artifacts
($3{,}242$ and $2{,}880$ tokens) compile locally with clean axioms but were rejected by the official
comparator; they are archived as a validity boundary. On the benchmark's model × harness leaderboard,
Deepseek V4.1-Flash / DeepSeek Harness ranks first (composite index $64.50$; average compression $84.2\%$);
evidence figures in `evidence/figures/`.

## 7 Discussion and conclusion

The five artifacts are one construction acquiring a better interface at each step: prescribe the witness gap;
inline the termwise certificate; read the low-height exclusion and sharp pole bound off the remainder; fuse
the three windows; carry one identity through the assembly. None changes the theorem; each removes an
interface the classical proof does not need. General lesson: **proof size is dominated by re-derivation and
interface overhead, and library-native reformulation compresses it.** Limitations: one pillar of a
formalization programme, not the Riemann Hypothesis; tokens are a benchmark-specific proxy for structure;
several savings are Mathlib-API savings. Roadmap to $2{,}500$ tokens: weaken the low-height exclusion to
$|\mathrm{Im}(s)|\ge 32d$ with a two-branch scale ($\approx-110$), merge the two logarithmic inputs
($\approx-130$), restate the peeling lemma with `logDeriv` ($\approx-100$).

## 8 Artifact and reproduction

```bash
python3 tools/token_count.py Lean/smallest-scored-96283/Solution.lean      # -> 2931
LEAN_HOME=... MATHLIB=... tools/compile_solution.sh Lean/smallest-scored-96283/Solution.lean demo
#   expected: compile rc=0;  #print axioms -> [propext, Classical.choice, Quot.sound]
```

**Provenance.** Results were produced under the account *Yin-Kai Yu (余荫铠)* by a collaborative track of two
AI agents (DeepSeek Harness / Deepseek V4.1-Flash and ChatGPT Desktop / GPT-6.2 Astra). Rejected artifacts
and pending scores are reported as such.

**Citation.**

```bibtex
@misc{yu2026zfrcompress,
  author = {Yu, Yin-Kai},
  title  = {Library-Native Proof Compression: Successive Record Formalizations of the Classical Zero-Free Region in {Lean}~4},
  year   = {2026},
  howpublished = {GitHub repository, artifact release v1.0},
  url    = {https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4},
}
```

## References

[1] B. Riemann, *Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse*, 1859. ·
[2] J. Hadamard, *Sur la distribution des zéros de la fonction ζ(s)*, Bull. SMF 24 (1896) 199–220. ·
[3] C.-J. de la Vallée Poussin, *Recherches analytiques sur la théorie des nombres premiers*, 1896. ·
[4] E. Landau, *Handbuch der Lehre von der Verteilung der Primzahlen*, Teubner, 1909. ·
[5] E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., OUP, 1986. ·
[6] H. L. Montgomery, R. C. Vaughan, *Multiplicative Number Theory I*, CUP, 2007. ·
[7] L. de Moura, S. Ullrich, *The Lean 4 Theorem Prover and Programming Language*, CADE-28, 2021, 625–635. ·
[8] The mathlib Community, *The Lean Mathematical Library*, CPP 2020, 367–381 (mathlib4 commit `d13f23b7`). ·
[9] É. Borel, *Sur les zéros des fonctions entières*, Acta Math. 20 (1897) 357–396. ·
[10] C. Carathéodory, *Über den Variabilitätsbereich*, Math. Ann. 64 (1907) 95–115. ·
[11] H. von Mangoldt, *Zu Riemann's Abhandlung*, J. Reine Angew. Math. 114 (1895) 255–305. ·
[12] L. Alpöge, *A Lean 4 formalization of the Riemann Hypothesis* (`alpo.ge`), 2025. ·
[13] Agentic Science Challenge, *Lean 4 Verification (RH Core Pillar 1/5)*, 2026. ·
[14] Public Proof Compression Progress Curve, <https://riemann.verifytask.cn/>, 2026.

## Appendix A. Mathlib declarations used

`borelCaratheodory_zero` (`Analysis/Complex/BorelCaratheodory.lean:86`) ·
`norm_deriv_le_div_of_mapsTo_ball` (`Analysis/Complex/Schwarz.lean:250`) ·
`differentiableOn_dslope` (`Analysis/Complex/RemovableSingularity.lean:60`) ·
`logDeriv_eqOn_iff`, `logDeriv_mul` (`Analysis/Calculus/LogDeriv.lean`) ·
`integral_Ioi_cpow_of_lt` (`Analysis/SpecialFunctions/ImproperIntegrals.lean:251`) ·
`LSeries_vonMangoldt_eq_deriv_riemannZeta_div` (`NumberTheory/LSeries/Dirichlet.lean:434`) ·
`norm_LFunction_product_ge_one` (`NumberTheory/LSeries/Nonvanishing.lean:310`) ·
`deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add` (`NumberTheory/Harmonic/ZetaAsymp.lean:585`).

## Appendix B. Artifact manifest

The five record artifacts in `Lean/` (`record-96272`, `fixes/localcert-fix`, `record-96281`,
`record-96282`, `smallest-scored-96283`); `smallest-verified` (2,843 tokens, pending);
`failed-96274-v22.lean` (rejected); `research/caseAB/`; `tools/`; `evidence/`; `docs/`; both papers.
