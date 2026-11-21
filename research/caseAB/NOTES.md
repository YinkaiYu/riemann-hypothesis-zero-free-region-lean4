# Independent Case A / Case B architecture (research artifact)

`CaseAB-architecture.lean` is an **independent proof** of the frozen theorem, written from a different
architecture than the competitive SOTA route. It compiles under Lean 4.34.1 with clean axioms
(`#print axioms AlpogeRHCore1.zeroFreeRegion` ⇒ `[propext, Classical.choice, Quot.sound]`), but measures
**9,344 normalized tokens**, so it is *not* competitive on the compression metric. It is archived as a
verified alternative derivation and as the seed for the "< 2,500" roadmap in `docs/ARCHITECTURE.md`.

## Motivation: delete the `zeroHeight` helper

The standard route needs a *low-height exclusion* before applying the 3–4–1 inequality: for zeros with
`Re s ∈ (3/4, 1)` one must know `|Im s| ≥ 1/2`, otherwise the pole term
`Re(((a−1) + i·Im s)⁻¹)` at the middle evaluation height blows up (`≈ 1/(a−1)`).

This artifact replaces that exclusion with a **two-case scale choice**.

## Case A: `25·d ≤ |Im s|`

* Let `d := 1 − Re s`, `a := 1 + 4d`. The witness zero `s` then sits at distance `a − Re s = 5d`,
  so the Landau witness value is exactly `x = (5d)⁻¹`.
* Pole terms are controlled directly by the height assumption:
  * `P₀ = (a−1)⁻¹ = (4d)⁻¹`
  * `P₁ = Re(((a−1)+i·Im s)⁻¹) = 4d/(16d² + (Im s)²) ≤ 4/(641·d)`
  * `P₂ = Re(((a−1)+2i·Im s)⁻¹) ≤ 4/(2516·d)`
* The 3–4–1 combination then gives `4/(5d) ≤ 3/(4d) + 16/(641d) + 4/(2516d) + 192·(log-term)`
  whose margin `≈0.023/d` is unbeatable because `d ≤ 10⁻¹²/log R`, so `1/d ≥ 10¹²·log R`.

## Case B: `|Im s| < 25·d` (the hard case)

Here the zero is astronomically close to the real axis (`|Im s| < 2.5·10⁻¹¹`), so the Case A poles are useless.
Instead apply `landau` at the **centre 1**:

* `f(w) := ζ₁(1+w)`, `f(0) = ζ₁(1) = 1 ≠ 0`; growth on `‖w‖ ≤ 1/2` is a constant `B ≤ 25·Cg/4`
  (the Abel/Mellin growth bound on `Re ≥ 1/2`).
* every zero of `f` in the disk has negative real part (`ζ` has no zeros with `Re ≥ 1`), so the hypothesis
  `hz` of `landau` holds globally.
* the witness is `ρ := s − 1`, and
  `x := Re((1−s)⁻¹) = d/(d² + (Im s)²) ≥ 1/(626·d)` because `|Im s| < 25d`.
* `landau` then gives `x ≤ 24(log B + 1) + |ζ₁′(1)|`, where `|ζ₁′(1)| ≤ 2·(25·Cg/4 + 1)` by Schwarz
  (`norm_deriv_le_div_of_mapsTo_ball`). With `d ≤ 2·10⁻¹²` the left side is `≥ 5·10⁸` while the right side is
  `< 1200` — contradiction.

So the low-height exclusion is eliminated by *relocating* the Landau application to the pole side, at the
price of one extra branch and an explicit derivative bound.

## Experiment recorded here: Euler–Maclaurin growth is *more* expensive in Lean

A second independent experiment re-derived the polynomial growth of `ζ₁` from the Euler–Maclaurin/Abel
identity `∑ₙ [(n+1)^{1−s} − (n+2)^{1−s} − (s−1)(n+1)^{−s}] = 1 − ζ₁(s)` (the technique visible in a
competitor's public partial diff). Measured cost with our normalization metric:

| module | tokens |
|---|---:|
| `cpow_sub_eq` (interval-integral identity) | 95 |
| term bound `Q` | 264 |
| `growthBound` for `ζ` on `Re > 0` | 540 |
| auxiliary summable/telescoping lemmas | 158 |
| **total** | **1,057** |

versus **~715 tokens** for the Mellin route used by the SOTA file. Conclusion: the Euler–Maclaurin route is
mathematically elegant but loses on tokens; it was therefore not adopted, only documented.
