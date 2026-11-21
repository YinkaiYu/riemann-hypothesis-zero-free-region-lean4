# Library-Native Proof Compression — Successive Record Formalizations of the Classical Zero-Free Region in Lean 4

**Research paper (English + 中文): how a 21-file, 21,641-token reference formalization of the classical
de la Vallée Poussin zero-free region became a single 2,535-token file — nine record refreshes, each traced
to its bottleneck, its core derivation, and its measured token delta.**

**Yin-Kai Yu (余荫铠)** · DeepSeek Harness × ChatGPT Desktop collaborative research track
<https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4>

[![Lean](https://img.shields.io/badge/Lean-4.34.1-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-d13f23b7-green)](https://github.com/leanprover-community/mathlib4)
[![Kernel verified](https://img.shields.io/badge/kernel--verified-yes-brightgreen)](docs/EVIDENCE.md)
[![Official score](https://img.shields.io/badge/official%20score-65.88-orange)](docs/EVIDENCE.md)
[![License](https://img.shields.io/badge/license-MIT-lightgrey)](LICENSE)

**Paper:** [**English**](paper/main_en.md) · [**中文版**](paper/main_zh.md) · **Cite:** [`CITATION.cff`](CITATION.cff) ·
[`paper/references.bib`](paper/references.bib)

---

## The theorem

The target is the classical de la Vallée Poussin zero-free region: there exists an absolute constant
$c>0$ such that

$$
\zeta(s)\neq 0 \qquad\text{whenever}\qquad
\mathrm{Re}(s)\ \ge\ 1-\frac{c}{\log(|\mathrm{Im}(s)|+2)},\quad s\neq 1 .
$$

The size measure is the normalized Lean 4 token count $T$ (comments, whitespace and `import` lines cost
$0$; identifier length is ignored), with reference baseline $T_0 = 21{,}641$ and benchmark score

$$
S(T)\;=\;100-\frac{50}{\,1+\frac{1}{2}\log_{10}(T_0/T)\,}.
$$

## The record sequence (each refresh has `kept = true` on the public curve)

| record | attempt | artifact | tokens | official score | `running_best_pct` | structural advance |
|---:|---|---|---:|---:|---:|---|
| — | 96263 | previous holder (Pi) | 3,286 | 64.5215 | 85.68 | — |
| 1 | 96272 | [`Lean/record-96272/`](Lean/record-96272/) | 3,274 | 64.5332 | 85.73 | recursive zero peeling replaces finite zero products |
| 2 | 96276 | [`Lean/fixes/localcert-fix/`](Lean/fixes/localcert-fix/) | 3,208 | 64.6400 | 86.03 | 3–4–1 certificate inlined as one `HasSum.nonneg` object |
| 3 | 96281 | [`Lean/record-96281/`](Lean/record-96281/) | 3,065 | 64.8928 | 86.64 | low-height exclusion + sharp pole bound read off the Mellin remainder |
| 4 | 96282 | [`Lean/record-96282/`](Lean/record-96282/) | 3,014 | 64.9800 | 86.87 | window lemma fused into the assembly |
| 5 | 96283 | [`Lean/smallest-scored-96283/`](Lean/smallest-scored-96283/) | 2,931 | 65.8839 | 87.24 | one normalized complex identity carried through the assembly |
| 6 | 96286 | [`Lean/smallest-verified/`](Lean/smallest-verified/) | 2,843 | 65.2900 | 87.59 | same lineage, next interface collapse |
| 7 | 96293 | [`Lean/record-96293-v25/`](Lean/record-96293-v25/) | 2,578 | 65.8000 | 88.80 | smaller assembly, further fusion (GPT-6.2 Astra artifact) |
| 8 | 96295 | — (intermediate variant of the v26 lineage) | 2,543 | 65.8700 | 88.97 | (GPT-6.2 Astra artifact) |
| 9 | 96308 | [`Lean/record-96308-v26/`](Lean/record-96308-v26/) | **2,536** | **65.8834** | **88.99** | current record (Deepseek V4.1-Flash) |

**Compression.** $T_0/T = 21{,}641/2{,}535 \approx 8.54$, i.e.

$$
\frac{T_0-T}{T_0}\;=\;1-\frac{2{,}535}{21{,}641}\;\approx\;88.3\%,
\qquad S(2{,}535)\approx 65.88 .
$$

The mathematical core is the same throughout; each record step improves an *interface* or a *distinction*
that the classical proof does not need:

**(i) Mellin entire formula.** For $\mathrm{Re}(s)>0$,

$$
\zeta_1(s):=(s-1)\zeta(s)=s(1-(s-1)R(s)),\qquad
\|R(s)\|\le \frac{1}{\mathrm{Re}(s)},
$$

which yields both the polynomial growth bound
$\|z\|\le 4R \Rightarrow \|\zeta_1(z)\|\le R^8$ on $\mathrm{Re}(z)\ge\frac{1}{2}$ and a cheap zero
exclusion: $\zeta_1(z)=0 \Rightarrow (z-1)R(z)=1 \Rightarrow \mathrm{Re}(z)\le|z-1|$, hence zeros
with $\mathrm{Re}(z)\ge\frac{3}{4}$ satisfy $|\mathrm{Im}(z)|\ge\frac{1}{2}$.

**(ii) Recursive zero peeling.** Put $\mathrm{nld}(f,z):=-\mathrm{Re}(f'(z)/f(z))$.
For entire $f$ on $\overline{B}(0,\frac{1}{2})$ with $f(0)\neq 0$, growth
$\|f(w)\|\le B\|f(0)\|$, and all zeros in $\overline{B}(0,\frac{1}{6})$ in the closed left half-plane,

$$
x+\mathrm{nld}(f,0)\;\le\;24\log B+24 ,
\qquad x=0 \ \text{or}\ x=\mathrm{Re}((-\rho)^{-1})\ \text{for a zero } \rho .
$$

The proof is a strong induction on $n$ with $B<2^n$, whose peeling step at a zero $\rho_0$ is

$$
g(w):=\mathrm{dslope}(f,\rho_0)(w),\qquad
f(w)=(w-\rho_0)\,g(w),\qquad f(0)=-\rho_0\,g(0),
$$

and the growth constant of $g$ is *exactly half* that of $f$, $B\mapsto B/2$; the terminal branch is the
Borel–Carathéodory estimate for the logarithm.

**(iii) Assembly.** With $R=|\mathrm{Im}s|+2$, $d=2^{-20}/\log R$ and the adaptive scale
$a:=\mathrm{Re}s+5d$, the witness zero sits exactly $5d$ from the centre, so $x=(5d)^{-1}$ is sharp;
$\mathrm{Re}s\ge 1-d$ gives $a-1\ge 4d$, and the pole terms are

$$
\mathrm{Re}((a+i\gamma-1)^{-1})=\frac{a-1}{(a-1)^2+\gamma^2}
\;\le\;\frac{5d}{(4d)^2+\frac{1}{4}}\;\le\;20d .
$$

The 3–4–1 inequality ($3+4\cos\theta+\cos2\theta\ge 0$, via Mathlib's
`norm_LFunction_product_ge_one`) then yields the negative margin

$$
(\frac{4}{5}-\frac{3}{4})\frac1d \;=\;\frac{0.05}{d}\;\ge\;5\cdot 10^{4}\log R
\qquad\text{against an error budget of}\quad \mathcal{O}(\log R),
$$

so every estimate may be crude and one `linarith` closes the proof.

**External validation.** The benchmark's *model × harness* leaderboard ranks **Deepseek V4.1-Flash +
DeepSeek Harness #1** by composite index (**64.50**) and by average proof compression (**84.2 %**)
(`evidence/figures/leaderboard-model-harness.png`, `leaderboard-avg-compression.png`). The first record
moment is archived as a screenshot (`evidence/figures/curve-record-162-submission.png`: submission #162,
−85.7 %, 3,089 site tokens, 2026-11-22 05:23), and the platform's paper-style derivation of the technique
— *Borel–Carathéodory + analytic divided difference (`dslope`) recursive zero peeling* — in
`evidence/figures/site-derivation-borel-dslope.png`; submission-progress overview in
`evidence/figures/submission-progress.png`.

![Record moment #162: −85.7 %, 3,089 site tokens](evidence/figures/curve-record-162-submission.png)
![Model × harness leaderboard: Deepseek V4.1-Flash + DeepSeek Harness #1](evidence/figures/leaderboard-model-harness.png)
![Platform paper-style derivation of the peeling technique](evidence/figures/site-derivation-borel-dslope.png)

**Ablation.** The natural Euler–Maclaurin route to the growth bound — proving
$\sum_n[(n+1)^{1-s}-(n+2)^{1-s}-(s-1)(n+1)^{-s}]=1-\zeta_1(s)$ and bounding the series — costs
$264+540+95+158=\mathbf{1{,}057}$ tokens versus $\approx 715$ for the Mellin route, and yields no cheap
zero exclusion. Two valid mathematical routes differ by $\approx 50\%$ in formal cost: the compression is
structural, not cosmetic.

**Published technique** (benchmark site, submission 96283): `core1_borel_dslope` — *Borel–Carathéodory +
Divided-Difference (DSlope) Zero Factorization* — reproduced verbatim (EN + 中文) in both papers.

---

## Repository guide

| what | where |
|---|---|
| Paper (English) | [`paper/main_en.md`](paper/main_en.md) |
| 论文（中文） | [`paper/main_zh.md`](paper/main_zh.md) |
| Five record artifacts | [`Lean/record-96272/`](Lean/record-96272/), [`Lean/fixes/localcert-fix/`](Lean/fixes/localcert-fix/), [`Lean/record-96281/`](Lean/record-96281/), [`Lean/record-96282/`](Lean/record-96282/), [`Lean/smallest-scored-96283/`](Lean/smallest-scored-96283/) |
| Smallest verified (2,843 tokens, pending) · rejected artifact | [`Lean/smallest-verified/`](Lean/smallest-verified/), [`Lean/failed-96274-v22.lean`](Lean/failed-96274-v22.lean) |
| Independent Case A/B architecture | [`research/caseAB/`](research/caseAB/) |
| Token meter + compile/axiom-audit harness | [`tools/`](tools/) |
| Official evidence snapshots & figures | [`evidence/`](evidence/) · [`docs/EVIDENCE.md`](docs/EVIDENCE.md) |
| Extended notes | [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) |
| Citation metadata | [`CITATION.cff`](CITATION.cff) · [`paper/references.bib`](paper/references.bib) |

## Reproduce

```bash
python3 tools/token_count.py Lean/smallest-scored-96283/Solution.lean      # -> 2931
LEAN_HOME=/path/to/lean-4.34.1-linux MATHLIB=/path/to/mathlib4 \
  tools/compile_solution.sh Lean/smallest-scored-96283/Solution.lean demo
#   expected: compile rc=0;  #print axioms -> [propext, Classical.choice, Quot.sound]
```

## Provenance

The results were produced under the account *Yin-Kai Yu (余荫铠)* by a collaborative research track in which
two AI agent tracks worked together (DeepSeek Harness / Deepseek V4.1-Flash and ChatGPT Desktop /
GPT-6.2 Astra). Rejected artifacts and pending scores are reported as such.

## How to cite

```bibtex
@misc{yu2026zfrcompress,
  author       = {Yu, Yin-Kai},
  title        = {Library-Native Proof Compression: Successive Record Formalizations of the Classical Zero-Free Region in {Lean}~4},
  year         = {2026},
  howpublished = {GitHub repository, artifact release v1.0},
  url          = {https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4},
  note         = {Five record refreshes; best official score 65.8839 (submission 96283), curve kept=true},
}
```

## License

MIT — see [`LICENSE`](LICENSE). Lean/Mathlib dependencies keep their own licenses (Mathlib: Apache-2.0).
