# Library-Native Proof Compression: Successive Record Formalizations of the Classical Zero-Free Region in Lean 4

**Yin-Kai Yu (余荫铠)** — DeepSeek Harness × ChatGPT Desktop collaborative research track

*Artifact release v1.0 · 2026-11-22 · <https://github.com/YinkaiYu/riemann-hypothesis-zero-free-region-lean4>*

## Abstract

The classical zero-free region of the Riemann zeta function is a short theorem in any textbook on analytic
number theory, yet its reference formalization in Lean 4 occupies twenty-one files and 21,641 normalized
tokens. In this paper we describe a series of compressed formalizations of the same theorem that set the
record on a public proof-compression benchmark five times, shrinking the proof from 3,274 tokens to 2,931
tokens in a single file. The mathematical content of the paper is not new number theory: it is an
explanation of *which parts of the formal proof were expensive, what mathematical reorganization made them
cheap, and how much each reorganization saved*. For every record we identify the bottleneck, present the
core derivation, and report the measured change in token count. We close with an ablation comparing the
Mellin-transform approach used in the final proof with a natural Euler–Maclaurin alternative, which turns
out to be roughly fifty percent more expensive in formal tokens, and with a discussion of the limitations of
measuring proof quality by token count.

**Keywords:** formalized analysis, Lean 4, Mathlib, proof compression, zero-free region, analytic divided
differences, Borel–Carathéodory inequality.

## 1 Introduction

The Riemann zeta function is defined for complex numbers $s$ with real part greater than one by the series

$$
\zeta(s) \;=\; \sum_{n=1}^{\infty} \frac{1}{n^{s}},
$$

and it extends to a meromorphic function on the whole complex plane with a single pole at $s=1$. Its zeros
encode the distribution of the primes: this is the content of the Riemann Hypothesis, and it is also the
content of the much older and unconditional results that followed it.

Long before the Riemann Hypothesis was formulated, Hadamard and de la Vallée Poussin proved in 1896 that the
zeta function does not vanish anywhere to the right of a thin region adjacent to the vertical line
$\mathrm{Re}(s)=1$. This result — the *classical zero-free region* — is the statement that there exists
an absolute positive constant $c$ such that $\zeta(s) \neq 0$ whenever

$$
\mathrm{Re}(s) \;\ge\; 1 - \frac{c}{\log\left(|\mathrm{Im}(s)|+2\right)}.
$$

It is the analytic input behind the Prime Number Theorem with an explicit error term, and it is the first
step in the Landau–Page theory of Dirichlet $L$-functions. In a formalization project, it is also a
gateway: many later arguments reuse its estimates.

**Formalization.** A complete formal proof of this theorem sits inside the Lean 4 formalization of the
Riemann Hypothesis by Levent Alpöge, where the relevant closure consists of twenty-one source files. In the
language of the public benchmark used in this paper, that closure costs 21,641 *normalized tokens*.

**What this paper is about.** It is tempting to read a formal proof the way one reads a textbook: pages of
analysis, each line forced by the previous one. In practice the size of a formal proof is dominated by
something else — by the analytic machinery the author chooses to build, and by the interfaces through which
the different parts of the proof talk to each other. Our thesis, made concrete below, is that much of this
cost is *avoidable*: modern libraries already contain abstractions that replace hundreds of lines of
hand-rolled estimates, and most of the rest is paid for interfaces that the classical argument does not
actually need.

We therefore do not present a new proof of the zero-free region. We present, record by record, the
reorganization of one proof: for each of the five artifacts that set a new benchmark record, we ask which
bottleneck it removed, which mathematical observation allowed the removal, and what the removal was worth in
normalized tokens.

## 2 The problem and how it is scored

**The target statement.** The benchmark freezes the theorem below and asks for a complete Lean 4 proof of
it:

$$
\exists\, c > 0, \quad \forall s \in \mathbb{C}, \; s \neq 1, \quad
\mathrm{Re}(s) \ge 1 - \frac{c}{\log\left(|\mathrm{Im}(s)|+2\right)}
\;\;\Longrightarrow\;\; \zeta(s) \neq 0 .
$$

**Verification.** The proof is checked in Lean 4.34.1 against a pinned version of Mathlib, and then replayed
by the benchmark's official comparator. Three standard axioms are permitted — `propext`, `Quot.sound` and
`Classical.choice` — and nothing else: no `sorry`, no custom axiom, no modification of the frozen statement.
Our artifacts satisfy the even stronger local check that `#print axioms` on the final theorem lists exactly
those three axioms.

**The metric.** The benchmark measures the size of a submission by a *normalized token count* $T$. The
normalization is designed to remove cosmetic savings: comments, blank space and `import` lines cost
nothing, and identifiers count as one token regardless of how long they are. Renaming variables, deleting
spaces or replacing imports by `import Mathlib` therefore does not help. What does help is *structural*
compression: fewer declarations, fewer intermediate steps, and arguments that reuse existing library
theorems instead of re-deriving them. This is precisely the quantity we analyze.

Scores are computed from the token count by the formula

$$
S(T) \;=\; 100 - \frac{50}{1 + \frac{1}{2}\log_{10}\left(T_{0}/T\right)},
\qquad T_{0} = 21{,}641 ,
$$

so that $T = T_{0}$ scores 50, a ten-fold compression scores about 66.7, and a hundred-fold compression
scores 75. Because the score is monotone in $1/T$, every token saved is worth the same direction of credit;
the size of the credit is what the records below measure.

## 3 The mathematical core

The classical argument has three moving parts. We describe each in words first, and then give the exact
statements used in the formal proofs.

**(a) A growth bound.** To say anything about the logarithmic derivative of the zeta function near a
hypothetical zero, one first needs to know how fast the function can grow. In the classical proof this is a
polynomial bound on $\zeta_1(s) = (s-1)\zeta(s)$ in a half-plane to the right of the critical line.

**(b) A logarithmic-derivative bound.** If a function has a zero very close to a point $z$, then its
logarithmic derivative at $z$ must be large and negative: the zero forces a singularity nearby. The classical
argument converts this local fact into an inequality, but doing so requires knowing where *all* the zeros of
the function are — which is exactly what the reference formalization obtains by building a finite product
over the zeros in a disk.

**(c) The three-four-one inequality.** The combination

$$
3 + 4\cos\theta + \cos 2\theta \;=\; 2(1+\cos\theta)^{2} \;\ge\; 0
$$

is nonnegative for every angle $\theta$. Applying it term by term to the Dirichlet series of $-\zeta'/\zeta$
gives the inequality $3D(a) + 4D(a+t) + D(a+2t) \ge 0$, where $D(z)$ denotes the real part of the von
Mangoldt series; this is the constraint that the growth and logarithmic-derivative estimates are finally fed
into.

The compressed proof replaces (a) and (b) by library-native analogues and keeps (c) but derives it in a way
that does not need a separate lemma. We now present the four ingredients.

**Ingredient 1: a Mellin identity for $\zeta_1$.** The fractional-part function $\{x\}$ has a Mellin
transform, and integrating by parts produces an entire formula for $\zeta_1$. Concretely, for
$\mathrm{Re}(s) > 0$,

$$
\zeta_1(s) \;=\; s\left(1 - (s-1)R(s)\right),
\qquad \|R(s)\| \;\le\; \frac{1}{\mathrm{Re}(s)} ,
$$

where $R$ is the Mellin transform of the fractional part of the tail. The identity is proved first for
$\mathrm{Re}(s) > 1$, where the series and the integral both converge, and then extended to the
half-plane $\mathrm{Re}(s) > 0$ by analytic continuation.

This single identity does double duty. First, it gives the growth bound needed in (a): for
$\mathrm{Re}(z) \ge 1/2$ and $\|z\| \le 4R$ one has $\|\zeta_1(z)\| \le R^{8}$. Second, it excludes
zeros near the pole: if $\zeta_1(z) = 0$ then the identity forces $(z-1)R(z) = 1$, hence
$\mathrm{Re}(z) \le |z-1|$; combined with $\mathrm{Re}(z) \ge 3/4$ this says that any such zero
must satisfy $|\mathrm{Im}(z)| \ge 1/2$. That last inequality is exactly the *low-height* information
needed by the assembly, and in the reference formalization it is obtained by separate arguments.

**Ingredient 2: recursive zero peeling.** The heart of the compression is a way to bound the logarithmic
derivative near a zero without ever building a product over zeros.

The idea is to remove one zero at a time. Suppose $f$ is entire and has a zero at $\rho$. Then one can
divide $f$ by the linear factor $(w-\rho)$ using the analytic divided difference; the quotient is again
entire, and because the factor has cancelled the zero, the quotient grows *less fast* than $f$. Repeating
this for every zero in a disk would recover the product formula; the observation that makes the formal proof
small is that one does not need the product — one only needs a bound, and a bound can be proved by induction
on the growth constant itself.

The lemma proved in Lean is the following. Let $f$ be entire, $f(0) \neq 0$, and suppose that on the closed
disk of radius $1/2$ the function satisfies $\|f(w)\| \le B\|f(0)\|$, and that all zeros of $f$ in the disk
of radius $1/6$ lie in the closed left half-plane. Then, for every natural number $n$ with $B < 2^{n}$,

$$
x + \mathrm{nld}(f,0) \;\le\; 24\log B + 24,
\qquad \mathrm{nld}(f,z) := -\mathrm{Re}\left(\frac{f'(z)}{f(z)}\right),
$$

where $x = 0$, or $x = \mathrm{Re}\left((-\rho)^{-1}\right)$ for a zero $\rho$ of $f$ of modulus at
most $1/6$. The induction peels zeros one at a time. At a zero $\rho_0$ one sets
$g(w) := \mathrm{dslope}(f,\rho_0)(w)$, so that

$$
f(w) \;=\; (w-\rho_0)\,g(w),
\qquad f(0) \;=\; -\rho_0\,g(0),
$$

and the growth constant of $g$ is *exactly half* that of $f$: the distance to $\rho_0$ cancels one factor in
the maximum modulus estimate. The induction then continues on $g$, and the term
$\mathrm{Re}((-\rho_0)^{-1})$ is added back from the factorization of the logarithmic derivative.
If the inner disk contains no zero at all, the logarithmic derivative is exact there; $f$ has an analytic
logarithm $u$ with real part at most $\log B$, and the Borel–Carathéodory inequality bounds $u'(0)$. A short
Lipschitz estimate converts that bound into the one stated for $\mathrm{nld}(f,0)$.

The point of this construction is that the recursion performs the enumeration of zeros *implicitly*. There is
no product, no contour integral, and no case analysis on the number of zeros; the induction *is* the
enumeration. In the reference formalization, the same job is done by collecting the zeros into an explicit
product and proving derivative estimates factor by factor, and that is where most of its size comes from.

**Ingredient 3: the von Mangoldt bridge.** On the half-plane $\mathrm{Re}(z) > 1$ one has the
identity

$$
\mathrm{Re}\left(\frac{\zeta_1'(z)}{\zeta_1(z)}\right)
\;=\; \mathrm{Re}\left(\frac{1}{z-1}\right)
\;+\; \mathrm{Re}\sum_{n\ge 1} \Lambda(n)\,n^{-z},
$$

where $\Lambda$ is the von Mangoldt function. This converts the bounds on the logarithmic derivative into
statements about the series $D$ that appears in the three-four-one inequality of ingredient (c). In the Lean
development the identity is a library theorem; the compressed proofs only have to apply it.

**Ingredient 4: an adaptive scale and a robust final inequality.** The remaining work is to combine the
three ingredients at the right points. The proof applies the peeling lemma at three heights — the real axis,
the height of the putative zero, and twice that height — with growth ratio $R^{8}/\|{\zeta_1}\|$, where
$R = |\mathrm{Im}(s)| + 2$. The choice of the scale is what makes the final inequality robust.

Instead of evaluating at a fixed point $1+4d$, the proof evaluates at $a = \mathrm{Re}(s) + 5d$ with

$$
d \;=\; \frac{2^{-20}}{\log R} .
$$

This choice ties the scale to the real part of the candidate zero, so that the witness zero is at distance
*exactly* $5d$ from the centre; consequently the witness value $x = (5d)^{-1}$ is sharp, and the assumption
$\mathrm{Re}(s) \ge 1-d$ implies $a - 1 \ge 4d$. The pole terms are then

$$
\mathrm{Re}\left(\frac{1}{a+i\gamma-1}\right)
\;=\; \frac{a-1}{(a-1)^{2}+\gamma^{2}}
\;\le\; \frac{5d}{(4d)^{2}+\frac{1}{4}}
\;\le\; 20d ,
$$

which is tiny. After the three-four-one inequality, the negative margin obtained is

$$
\left(\frac{4}{5}-\frac{3}{4}\right)\frac{1}{d}
\;=\; \frac{0.05}{d}
\;\ge\; 5\cdot 10^{4}\,\log R ,
$$

while the total positive error is only of order $\log R$. Since $\log R \ge \log 2 > 0.69$, this inequality is
decisive by a wide margin, and the final arithmetic can be closed by a single call to `linarith`. The
practical consequence is important for code size: *because the margin is so large, every estimate in the
assembly may be crude*, and no sharp constants need to be formalized.

## 4 The five record artifacts

The benchmark's public curve stores, for every scored submission, the normalized token count, the official
score, and a flag `kept` that marks whether the submission set a new record at the time. Five of our
submissions — all with `kept = true` — are the subject of this section.

| Record | Attempt | Tokens | Official score | `running_best_pct` | Artifact in this repository |
|---:|---|---:|---:|---:|---|
| previous record | 96263 | 3,286 | 64.5215 | 85.68 | held by another participant |
| 1 | 96272 | 3,274 | 64.5332 | 85.73 | `Lean/record-96272/` |
| 2 | 96276 | 3,208 | 64.6400 | 86.03 | `Lean/fixes/localcert-fix/` |
| 3 | 96281 | 3,065 | 64.8928 | 86.64 | `Lean/record-96281/` |
| 4 | 96282 | 3,014 | 64.9800 | 86.87 | `Lean/record-96282/` |
| 5 | 96283 | 2,931 | 65.1339 | 87.24 | `Lean/smallest-scored-96283/` |
| 6 | 96286 | 2,843 | 65.2900 | 87.59 | `Lean/smallest-verified/` |
| 7 | 96293 | 2,578 | 65.8000 | 88.80 | `Lean/record-96293-v25/` |
| 8 | 96295 | 2,543 | 65.8700 | 88.97 | intermediate variant of the v26 lineage |
| 9 | 96308 | 2,536 | 65.8834 | 88.99 | `Lean/record-96308-v26/` |

Each subsection below states the bottleneck of the artifact that was replaced, the mathematical idea that
removed it, and the measured effect on the token count. The component sizes quoted are reproducible with
`tools/token_count.py`.

### Record 1 (3,274 tokens): replace the zero product by a recursion

**Bottleneck.** The reference formalization must bound the logarithmic derivative near a possible zero, and
it does so by collecting every zero of the relevant disk into a finite product
$\prod (w-\rho)^{m(\rho)}$, proving a derivative estimate factor by factor, and passing hand-written
Cauchy and Jensen estimates between files. The first compressed artifact already replaces that library by a
single recursion, but it still pays for five separate interfaces: the peeling lemma (`landau`, 873 tokens),
a window lemma (`scaledWindow`, 269), a certificate for the three-four-one inequality (`triple`, 248), a
low-height lemma (`zeroHeight`, 114) and a pole-term lemma (`poleTerm_le`, 66), plus a 643-token assembly.

**Derivation.** The derivation is ingredient 2 above: the strong induction on the growth constant, with the
divided-difference peeling step $B \mapsto B/2$ and the Borel–Carathéodory terminal branch. The benchmark site
describes this artifact with the technique label *Perron/Mellin contour simplification plus automation*, and
its own paper-style write-up is titled *Borel–Carathéodory with analytic divided-difference recursive zero
peeling*; the record moment is archived in `evidence/figures/`.

**Why the count drops.** One lemma of 873 tokens replaces the whole zero-factorization library, and the
Mellin identity (about 742 tokens) replaces the Euler–Maclaurin growth machinery. The official record for
this submission is 3,089 site tokens, a compression of 85.7 percent relative to the reference.

### Record 2 (3,208 tokens): inline the three-four-one certificate

**Bottleneck.** After the first record, the largest remaining interface was the certificate for the
three-four-one inequality, which was stated and proved as a separate lemma (`triple`, 248 tokens). Every
lemma pays for its statement, its proof and its instantiation, and the assembly had to refer to it by name.

**Derivation.** The certificate is *termwise*. Each term of the von Mangoldt series is of the form
$\Lambda(n)n^{-a}$ times $3 + 4\cos(t\log n) + \cos(2t\log n)$, which is nonnegative by ingredient (c).
Consequently the certificate can be produced *inside* the assembly as a single `HasSum.nonneg` object,
without a separate lemma. A formal detail also had to be handled: the quantity $D$ was introduced by a
`def`, and Lean's arithmetic tactic `linarith` does not see through a definitional abbreviation, so the
certificate and the window bounds were speaking about syntactically different atoms. A single `change`
statement re-expresses the certificate in the atoms used by the goal, and the tactic succeeds.

**Why the count drops.** The lemma `triple` disappears (248 tokens), while the assembly grows from 643 to 819
tokens and the abbreviation `D` from 21 to 27. The net saving is 66 tokens, from 3,274 to 3,208.

### Record 3 (3,065 tokens): derive the low-height exclusion and the pole bound once

**Bottleneck.** Two auxiliary lemmas still duplicated information that the Mellin identity already contained.
The lemma `zeroHeight` (114 tokens) excluded zeros with real part between $3/4$ and $1$ and small imaginary
part; the lemma `poleTerm_le` (66 tokens) bounded the pole terms by the crude constant 2. Both were stated,
proved and instantiated separately.

**Derivation.** Both facts follow directly from the identity of ingredient 1. For the exclusion: if
$\zeta_1(z) = 0$ then $(z-1)R(z) = 1$, hence $\mathrm{Re}(z) \le |z-1|$; together with
$\mathrm{Re}(z) \ge 3/4$ this forces $|\mathrm{Im}(z)| \ge 1/2$. For the pole terms, the exact
expression $\mathrm{Re}\left((a+i\gamma-1)^{-1}\right) = (a-1)/((a-1)^{2}+\gamma^{2})$ is bounded by
$(a-1)/\gamma^{2} \le 20d$ using the low-height bound, so the crude constant 2 is unnecessary. Both arguments
are now derived inside the assembly from the same `remainder` object, which the proof carries in any case.

**Why the count drops.** Both lemmas disappear (114 and 66 tokens), while the assembly grows from 819 to 876
tokens. The net saving is 143 tokens, from 3,208 to 3,065.

### Record 4 (3,014 tokens): fuse the three window applications

**Bottleneck.** The window estimate survived as a lemma (`scaledWindow`, 263 tokens) with its own statement
and *three* instantiations, one for each evaluation height. Each instantiation pays for the interface and for
passing arguments, and the assembly had to name the lemma.

**Derivation.** The window estimate is just the peeling lemma applied at the three centres $a + iv$, with
growth ratio $R^{8}/\|{\zeta_1}\|$. Because the growth hypothesis and the sharp pole inequality of record 3
are the same at all three centres, the three applications can be written inline and share those two
arguments. Nothing changes mathematically; the three uses become three `have` statements inside the final
theorem.

**Why the count drops.** The lemma `scaledWindow` disappears (263 tokens), while the assembly grows from 876
to 1,084 tokens. The net saving is 51 tokens, from 3,065 to 3,014.

### Record 5 (2,931 tokens): carry one identity through the assembly

**Bottleneck.** The bridge lemma (`good`, 94 tokens) and the abbreviation `D` (21 tokens) still mediated
between the analytic estimates and the final arithmetic: the logarithmic-derivative identity was proved as a
separate statement and the arithmetic had to pass through one more name.

**Derivation.** The assembly is reorganized around a single normalized complex identity. The entire formula
of ingredient 1 is the only place where $\zeta_1$ is expanded, and the bridge is reduced to a substitution
inside the assembly's own expression; as a result the arithmetic can work directly with the real parts of the
von Mangoldt series, and neither a named bridge lemma nor an abbreviation is needed.

**Why the count drops.** The bridge shrinks from 94 to 78 tokens, the abbreviation disappears, and the
assembly shrinks from 1,084 to 1,038 tokens: a net saving of 83 tokens, from 3,014 to 2,931. The final file
has sixteen top-level blocks: the assembly (1,038 tokens), the peeling lemma (872), the Mellin module (742),
the bridge (78), and the witness and glue (201).

## 5 What explains the compression

Three principles account for the sequence of records.

*First, replace re-derivation by a library primitive.* The peeling lemma and the Mellin identity are
instances of this principle: each replaces a self-contained piece of analysis by an application of an
existing abstraction, and each is far smaller than the machinery it replaces.

*Second, choose scales so that estimates may be crude.* The guarantee $d = 2^{-20}/\log R$ produces the
enormous margin $0.05/d \ge 5\cdot10^{4}\log R$ against an error budget of order $\log R$. Because the
margin is so large, the assembly never needs sharp constants, and sharp constants are expensive in formal
proofs.

*Third, fuse interfaces and let automation close goals.* Inlining the certificate, the low-height exclusion
and the three windows removes interfaces; normalizing inequalities with `grw` and closing them with
`linarith` removes chains of helper lemmas. The final file contains ten top-level declarations and 55 `have`
statements, with a tactic profile of 38 `simp`, 18 `linarith`, 14 `grind` and 10 `norm_num` calls.

**An ablation.** A natural alternative to ingredient 1 is the Euler–Maclaurin route: prove the identity

$$
\sum_{n\ge 0}\left[(n+1)^{1-s} - (n+2)^{1-s} - (s-1)(n+1)^{-s}\right] = 1 - \zeta_1(s)
$$

and bound the resulting series. We implemented this route and measured it: the term bound costs 264 tokens,
the growth theorem 540, the integral identity 95, and auxiliary lemmas 158 — a total of 1,057 tokens, against
about 715 for the Mellin route, and the Euler–Maclaurin route does not give the cheap zero exclusion of
record 3. Two mathematically valid routes differ by about fifty percent in formal cost, which is the clearest
evidence that the compression we report is structural rather than cosmetic.

## 6 Official evaluation

The artifacts of section 4 form the record sequence: the official score rises from 64.5332 through 64.6400, 64.8928, 64.9800 and 65.1339 to 65.8834,
64.8928, 64.9800 and finally 65.1339, while the running best compression percentage rises from 85.73 to
86.03, 86.64, 86.87 and 87.24. All five carry the flag `kept = true`.

**Consistency of the measurements.** Inverting the score formula recovers the official token count from the
official score; for the final artifact this gives about 2,932 tokens against our local measurement of 2,931,
and the agreement is within eight tokens for every scored submission. This is why the component-level
accounting of section 4 can be trusted: our local meter tracks the official one.

**A validity boundary.** Two artifacts, of 3,242 and 2,880 tokens, compile cleanly in our environment with
the three permitted axioms, yet were rejected by the official comparator. We report this as a negative
result and archive the artifacts: a local kernel check is necessary but not sufficient for acceptance, and
the difference matters for anyone reproducing these results.

**The model leaderboard.** On the benchmark's model-times-harness leaderboard, the combination used for these
submissions, Deepseek V4.1-Flash running on DeepSeek Harness, ranks first, with a composite index of 64.50
and an average compression of 84.2 percent. The relevant screenshots are archived in `evidence/figures/`.

## 7 Discussion

**What the five records have in common.** Read in sequence, the artifacts are not five different proofs. They
are one proof acquiring a better interface at each step: first prescribe the witness gap so that the middle
window becomes sharp; then inline the termwise certificate; then derive the low-height exclusion and the pole
bound from the identity that is already present; then fuse the three window applications; and finally carry a
single identity through the assembly. None of these steps changes the theorem, and each removes an interface
or a distinction that the classical proof does not need.

**Limitations.** First, the scope: this is one analytic pillar of a formalization project, not a proof of the
Riemann Hypothesis. Second, the metric: normalized tokens are a benchmark-specific proxy for proof
structure, not a measure of mathematical depth, and the numbers are not comparable across benchmarks. Third,
the library: several savings are savings in Mathlib's API, so the result measures the maturity of the library
together with the proof. Fourth, acceptance is not monotone in size, as the rejected artifacts of section 6
show.

**Where the next savings are.** We have identified three, with measured targets: weaken the low-height
exclusion from $|\mathrm{Im}(s)| \ge 1/2$ to $|\mathrm{Im}(s)| \ge 32d$ and use a two-branch
adaptive scale, for about 110 tokens; merge the two logarithmic inputs into a single von Mangoldt object, for
about 130 tokens; and restate the peeling lemma using the library's `logDeriv` API, for about 100 tokens.
Together these point at a proof of about 2,500 tokens.

## 8 Artifact, reproduction, and provenance

**Reproduction.** The repository contains the five record artifacts, the rejected and pending artifacts, a
local implementation of the normalized token meter, a compile-and-audit harness, the official evidence
snapshots and figures, an independent case-split proof, and this paper in English and Chinese. The two
commands below reproduce the central measurement and the central verification:

```bash
python3 tools/token_count.py Lean/smallest-scored-96283/Solution.lean      # -> 2931
LEAN_HOME=/path/to/lean-4.34.1-linux MATHLIB=/path/to/mathlib4 \
  tools/compile_solution.sh Lean/smallest-scored-96283/Solution.lean demo
#   expected: compile rc=0;  #print axioms -> [propext, Classical.choice, Quot.sound]
```

**Provenance.** The results were produced under the account *Yin-Kai Yu (余荫铠)* by a collaborative research
track in which two AI agents worked together: DeepSeek Harness running Deepseek V4.1-Flash, and ChatGPT
Desktop running GPT-6.2 Astra. The submissions, the measurements and this paper are part of that account's
record. Rejected artifacts and pending scores are reported as such.

**How to cite.**

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

[1] B. Riemann, *Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse*, 1859.
[2] J. Hadamard, *Sur la distribution des zéros de la fonction ζ(s) et ses conséquences arithmétiques*,
Bulletin de la Société Mathématique de France 24 (1896), 199–220.
[3] C.-J. de la Vallée Poussin, *Recherches analytiques sur la théorie des nombres premiers*, Annales de la
Société Scientifique de Bruxelles 20 (1896), 183–256.
[4] E. Landau, *Handbuch der Lehre von der Verteilung der Primzahlen*, Teubner, 1909.
[5] E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, second edition, revised by D. R. Heath-Brown,
Oxford University Press, 1986.
[6] H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I: Classical Theory*, Cambridge
University Press, 2007.
[7] L. de Moura and S. Ullrich, *The Lean 4 Theorem Prover and Programming Language*, CADE-28, 2021, 625–635.
[8] The mathlib Community, *The Lean Mathematical Library*, CPP 2020, 367–381; pinned commit `d13f23b7`.
[9] É. Borel, *Sur les zéros des fonctions entières*, Acta Mathematica 20 (1897), 357–396.
[10] C. Carathéodory, *Über den Variabilitätsbereich der Koeffizienten von Potenzreihen*, Mathematische
Annalen 64 (1907), 95–115.
[11] H. von Mangoldt, *Zu Riemann's Abhandlung über die Anzahl der Primzahlen*, Journal für die reine und
angewandte Mathematik 114 (1895), 255–305.
[12] L. Alpöge, *A Lean 4 formalization of the Riemann Hypothesis*, archive `alpo.ge`, 2025.
[13] Agentic Science Challenge, *Lean 4 Verification (RH Core Pillar 1/5): Classical Zero-Free Region for
ζ(s)*, 2026.
[14] Public Proof Compression Progress Curve, <https://riemann.verifytask.cn/>, 2026.

## Appendix A. Mathlib declarations used by the proof

The following library declarations carry the weight of the formalization; file and line refer to the pinned
Mathlib commit. `borelCaratheodory_zero` is in `Analysis/Complex/BorelCaratheodory.lean` at line 86;
`norm_deriv_le_div_of_mapsTo_ball` in `Analysis/Complex/Schwarz.lean` at 250; `differentiableOn_dslope` in
`Analysis/Complex/RemovableSingularity.lean` at 60; `logDeriv_eqOn_iff` and `logDeriv_mul` in
`Analysis/Calculus/LogDeriv.lean`; `integral_Ioi_cpow_of_lt` in `Analysis/SpecialFunctions/ImproperIntegrals.lean`
at 251; `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` in `NumberTheory/LSeries/Dirichlet.lean` at 434;
`norm_LFunction_product_ge_one` in `NumberTheory/LSeries/Nonvanishing.lean` at 310; and
`deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add` in `NumberTheory/Harmonic/ZetaAsymp.lean` at 585.

## Appendix B. Artifact manifest

The five record artifacts are in `Lean/record-96272`, `Lean/fixes/localcert-fix`, `Lean/record-96281`,
`Lean/record-96282` and `Lean/smallest-scored-96283`. The repository also contains `Lean/smallest-verified`
(2,843 tokens, score pending), `Lean/failed-96274-v22.lean` (rejected by the official comparator),
`research/caseAB` (an independent case-split proof), `tools` (token meter and compile/audit harness),
`evidence` (official snapshots and figures), `docs` (extended notes) and the two language versions of this
paper.
