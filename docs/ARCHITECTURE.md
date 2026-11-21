# SOTA route: from 21,641 baseline tokens to 2,843 tokens

Target: `∃ c > 0, ∀ s ≠ 1, 1 − c/log(|Im s|+2) ≤ Re s ⇒ ζ(s) ≠ 0` (de la Vallée Poussin zero-free region).

This document explains the mathematical route and the Lean engineering that takes the frozen statement from
Alpöge's 21-file / 21,641-token transitive closure to a single 2,843-token file.

## Scoring model

`T` = normalized Lean 4 tokens of all submitted `.lean` files, where comments, whitespace and `import` lines
count 0, and every identifier counts 1 regardless of length. Baseline `T₀ = 21,641`.
`S(T) = 100 − 50/(1 + 0.5·log₁₀(T₀/T))` for `T ≤ T₀`. Hence every 10× compression ≈ +16.7 score.

## Components

### 1. Entire Mellin formula for `ζ₁(s) = (s−1)ζ(s)`  (~615 tokens together)

```lean
abbrev frac : ℝ → ℂ := ofReal ∘ Int.fract
def tail := (Ioi 1).indicator frac
abbrev remainder (z : ℂ) := mellin tail (-z)

lemma tail_smooth : DifferentiableOn ℂ remainder {z | 0 < z.re}
lemma entireFormula (hs : 0 < s.re) : riemannZeta₁ s = s * (1-(s-1)*remainder s)
lemma mellin_bound (hs : 0 < s.re) : ‖remainder s‖ ≤ 1 / s.re
lemma entireGrowth (hR : 2 ≤ R) (hz : 1/2 ≤ z.re) (hn : ‖z‖ ≤ 4*R) : ‖riemannZeta₁ z‖ ≤ R^8
```

Why it compresses: instead of Alpöge's hand-rolled Cauchy-integral / Euler–Maclaurin estimates spread over
many files, the Mellin transform of the fractional-part tail gives `ζ₁` an explicit entire formula; from it
one gets both the polynomial growth bound needed by Landau's lemma and a two-line exclusion of zeros near
`s = 1` (`(s−1)·remainder(s) = 1` at a zero forces `Re s ≤ |s−1|`, contradicting `Re s ≥ 3/4`, `|Im s| ≤ 1/2`).

### 2. `landau` — Borel–Carathéodory + divided-difference zero peeling  (~850 tokens)

For `f` differentiable on `‖w‖ ≤ 1/2`, `f 0 ≠ 0`, `‖f w‖ ≤ B‖f 0‖` on the disk, and every zero of `f`
satisfying `Re ρ ≤ 0`:

```lean
theorem landau {f : ℂ → ℂ} {B x : ℝ}
    (hd : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hb : ∀ w, ‖w‖ ≤ 2⁻¹ → ‖f w‖ ≤ B * ‖f 0‖)
    (hz : ∀ ρ, f ρ = 0 → ρ.re ≤ 0)
    (hx : x = 0 ∨ witness f x) :
    x - (deriv f 0 / f 0).re ≤ 24 * (Real.log B + 1)
```

Proof: induction on `n` with `B < 2ⁿ`. If a zero `ρ` lies in the inner disk, write
`f = (·−ρ)·dslope f ρ`, show the divided difference again has growth constant `B/2` on the outer disk
(maximum modulus via `norm_le_of_forall_mem_frontier_norm_le`), recurse, and add back
`Re(−ρ⁻¹)`; otherwise `f` has no zeros on the small disk, so `logDeriv f` is exact there and
`borelCaratheodory_zero` (Mathlib) yields the bound, closed by `le_of_lip'` + `nlinarith`.

Why it compresses: the entire multi-file "finite zero product + Cauchy integral" machinery of the baseline
collapses to a single recursion with two branches.

### 3. Von Mangoldt bridge — `good`  (~75 tokens)

```lean
lemma good (ha : 1 < z.re) :
  riemannZeta₁ z ≠ 0 ∧
  deriv riemannZeta₁ z / riemannZeta₁ z = (z-1)⁻¹ - LSeries (fun n => (Λ n : ℂ)) z
```

Uses Mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` plus
`deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add`, so that the Landau estimates on `ζ₁′/ζ₁` can be compared with
the 3–4–1 inequality.

### 4. Window bounds — `scaledWindow` (or fused inline)

For a centre `z = a + i v` with `a ≈ 1`, `‖z‖ ≤ 3R`, `R ≥ 2`:

```lean
x + D z + 24*Real.log ‖riemannZeta₁ z‖ ≤ ((z-1)⁻¹).re + 24*(8*Real.log R + 1)
```

Applying `landau` to `w ↦ ζ₁(z+w)` with `B := R⁸/‖ζ₁ z‖` and using `entireGrowth` for growth on the half-plane
`Re ≥ 1/2`; `x` is either `0` or the sharp witness coming from a zero at distance `5d`.

### 5. Final assembly

* Put `R := |Im s| + 2`, `d := 2⁻²⁰ / log R` (so `d ≤ 1/100`), `a := Re s + 5d`.
  From the assumption `1 − d ≤ Re s` we get `4d ≤ a − 1`, hence `Re((a−1)⁺) ` is bounded and the real-centre
  pole term is harmless. `s` is a zero of `ζ₁`; if `Re s ≥ 3/4` then `|Im s| ≥ 1/2`
  (the low-height exclusion, itself a corollary of the Mellin formula).
* Apply the window bound at heights `0`, `Im s`, `2·Im s`; for the middle height the witness is the zero
  itself at distance `5d`, giving `x = (5d)⁻¹`.
* The product inequality `‖ζ(a)‖³‖ζ(a+it)‖⁴‖ζ(a+2it)‖ ≥ 1`
  (Mathlib `DirichletCharacter.norm_LFunction_product_ge_one`, equivalent to `3+4cosθ+cos2θ ≥ 0`)
  is converted with the `gap` estimate `‖ζ‖ ≤ d⁻¹‖ζ₁‖` into a lower bound for
  `3 log‖ζ₁(a)‖ + 4 log‖ζ₁(a+it)‖ + log‖ζ₁(a+2it)‖`.
* A `HasSum.nonneg` certificate for `3D(a) + 4D(a+it) + D(a+2it) ≥ 0` (termwise von Mangoldt series with the
  pointwise inequality `3 + 4cos θ + cos 2θ ≥ 0`) plus `Real.log_le_self` and `Real.log_two_lt_d9` close the
  arithmetic contradiction `linarith`: the negative margin is `(4/5 − 3/4)/d = 0.05/d ≥ 52428·log R`, while
  the positive error is only `192(8 log R + 1 + log log R …) = O(log R)`.

## Token-engineering notes (what actually moves `T`)

* `import` lines, comments, whitespace: **free** — write all documentation you want.
* Identifiers: 1 token each regardless of length — so use descriptive names, not golfed letters.
* Real savings come from: fewer intermediate `have`s, fewer helper declarations, stronger automation
  (`grind`, `linarith`, `nlinarith`, `gcongr`, `grw`, `field_simp`), and fusing window lemmas.
* Gotchas discovered the hard way:
  * `def D` vs `abbrev D`: a `def` hides its body from `linarith`'s atom comparison, so two syntactically
    different sides of the same fact cannot be cancelled (`M` stated with `LSeries …` vs goals using `D …`).
    This is why the original 3,179-token WIP failed; the published repair adds an explicit `change` line.
  * `grw [re_le_norm, norm_inv, ← abs_im_le_norm …]` produces positivity side-goals that must be discharged
    (`0 < |(a,2·Im s⟩−1).im|`), otherwise the whole rewrite fails.
  * Local compilation + `#print axioms` is **necessary but not sufficient**: two artifacts (3,242 tokens) were
    rejected by the official Comparator while compiling cleanly here.

## Roadmap to < 2,500 tokens

Top remaining blocks (from the 2,843 file): assembly ~1,030, `landau` ~850, growth ~715.

1. **Remove the 1/2 low-height constant** (~−110): replace `|Im s| ≥ 1/2` with `|Im s| ≥ 32d` and make the
   scale adaptive: `a := Re s + max(4d, |Im s|/3)`, split the pole-term arithmetic into `|Im s| ≤ 32d`
   (scale `|Im s|/3`, margin `≈1.7/|Im s|`) and `|Im s| > 32d` (scale `5d`, margin `0.05/d`).
2. **Merge the two log-derivative inputs** (~−130): derive the `3D(a)+4D(a+it)+D(a+2it) ≥ 0` certificate and
   the `3log‖ζ₁(a)‖+4log‖ζ₁(a+it)‖+log‖ζ₁(a+2it)‖` lower bound from a single von Mangoldt `HasSum` object.
3. **Restate `landau` with `logDeriv`** (~−100): `x + re(-logDeriv f 0) ≤ 25 log K + 25`, straight from
   Mathlib's `logDeriv` API, avoiding the `deriv f 0 / f 0` chains.
4. **Inline the window lemma** (~−60) and drop redundant `simp` hint lists.

Combined with the measured ~−3 tokens/min iteration rate of the shared workspace loop, these put a
2,400–2,500-token artifact within reach; the official displayed tokens for the current best are already
2,892 at score 64.89.
