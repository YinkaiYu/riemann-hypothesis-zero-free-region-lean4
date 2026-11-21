import Mathlib

open Complex Filter Topology Metric Set ArithmeticFunction

noncomputable section

namespace ClassicalZFR

/-! ## Euler–Maclaurin growth bound for `(s-1)ζ(s)` on `Re s > 1/4` -/

abbrev cp (s : ℂ) (n : ℕ) : ℂ := ((n : ℂ) + 1) ^ (-s)
abbrev pw (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-5 / 4 : ℝ)
abbrev dz (s : ℂ) (n : ℕ) : ℂ := cp (s - 1) n - cp (s - 1) (n + 1) - (s - 1) * cp s n
abbrev Cg : ℝ := 1 + ∑' n, pw n

set_option maxHeartbeats 1000000 in
lemma termBound {s : ℂ} (hs : 4⁻¹ < s.re) (n : ℕ) : ‖dz s n‖ ≤ (‖s‖ + 1) ^ 2 * pw n := by
  let a : ℝ := n + 1
  have ha : 1 ≤ a := by simp [a]
  let G (x : ℝ) := ↑(a + 1 - x) * (s - 1) * ↑x ^ (-s) - ↑x ^ (1 - s)
  have hm := (convex_Icc a (a + 1)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := G) (f' := fun x => -↑(a + 1 - x) * (s - 1) * s * ↑x ^ (-s - 1))
    (fun x hx => by
      have hd c := ((hasDerivAt_id ↑x).cpow_const (c := c) (.inl (by simp; linarith [hx.left]))).comp_ofReal
      exact (((((hasDerivAt_id x).const_sub (a + 1)).ofReal_comp.mul_const (s - 1)).mul
        (hd (-s))).sub (hd (1 - s))).hasDerivWithinAt.congr_deriv (by simp [sub_sub_cancel_left]; ring))
    (fun x hx => by
      have hx1 := ha.trans hx.left
      simp only [norm_mul, norm_neg, norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hx.right),
        norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hx1), sub_re, neg_re, one_re]
      grw [show a + 1 - x ≤ 1 by linarith [hx.left],
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : -s.re - 1 ≤ -5 / 4),
        Real.rpow_le_rpow_of_nonpos (by positivity) hx.left (by norm_num)])
    ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩
  simp [show G (a + 1) - G a = dz s n by simp [G, dz, cp, a]; ring_nf] at hm
  exact hm.trans (by rw [sq]; gcongr; exacts [by simpa using norm_sub_le s 1, by linarith])

lemma summable_pw : Summable pw := by
  have h := (summable_nat_add_iff 1).mpr
    ((Real.summable_nat_rpow (p := (-5 / 4 : ℝ))).mpr (by norm_num))
  refine h.congr fun n => ?_
  simp [pw, Nat.cast_add, Nat.cast_one]

lemma summable_cp {w : ℂ} (hw : 1 < w.re) : Summable (cp w) := by
  have h0 : Summable (fun n : ℕ => 1 / (n : ℂ) ^ w) :=
    (Complex.summable_one_div_nat_cpow (p := w)).mpr hw
  have h1 : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ w) := by
    have h2 := (summable_nat_add_iff 1).mpr h0
    refine h2.congr fun n => ?_
    norm_cast
  refine h1.congr fun n => ?_
  simp [cp, one_div, Complex.cpow_neg]

lemma sum_pw_le : (∑' n, pw n) ≤ 5 := by
  have h := ZetaAsymptotics.zeta_limit_aux1 (s := 5 / 4) (by norm_num)
  have h2 : 0 ≤ ZetaAsymptotics.termTSum (5 / 4) :=
    tsum_nonneg fun n => ZetaAsymptotics.term_nonneg (n + 1) (5 / 4)
  have E (n : ℕ) : pw n = 1 / ((n : ℝ) + 1) ^ (5 / 4 : ℝ) := by
    rw [pw, show (-5 / 4 : ℝ) = -(5 / 4) by norm_num,
      Real.rpow_neg (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity) (5 / 4), one_div]
  have h' : (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (5 / 4 : ℝ)) - 1 / (5 / 4 - 1) =
      1 - 5 / 4 * ZetaAsymptotics.termTSum (5 / 4) := by
    simpa only [Nat.cast_add, Nat.cast_one] using h
  simp_rw [E]
  linarith

lemma Cg_ge_one : 1 ≤ Cg := by
  have h : 0 ≤ ∑' n, pw n := tsum_nonneg fun n => by positivity
  simp only [Cg]; linarith

lemma Cg_le_six : Cg ≤ 6 := by have := sum_pw_le; simp only [Cg]; linarith

set_option maxHeartbeats 2000000 in
theorem zeta_one_growth {s : ℂ} (hs : 4⁻¹ < s.re) :
    ‖riemannZeta₁ s‖ ≤ Cg * (‖s‖ + 1) ^ 2 := by
  have hU : IsOpen {z : ℂ | 4⁻¹ < z.re} := isOpen_lt continuous_const continuous_re
  have hS : Summable pw := summable_pw
  have hfun : AnalyticOnNhd ℂ (fun z => 1 - ∑' n, dz z n) {z : ℂ | 4⁻¹ < z.re} := by
    intro s0 hs0
    have hV := hU.inter (isOpen_ball (x := s0) (ε := 1))
    exact analyticAt_const.sub ((differentiableOn_tsum_of_summable_norm (hS.mul_left ((‖s0‖ + 2) ^ 2))
      (fun n => Differentiable.differentiableOn fun z => by fun_prop (disch := left; norm_cast; positivity))
      hV fun n z hz' => (termBound hz'.1 n).trans (by
        grw [show ‖z‖ + 1 ≤ ‖s0‖ + 2 by linarith [norm_sub_norm_le z s0, mem_ball_iff_norm.mp hz'.2]])).analyticAt
      (hV.mem_nhds ⟨hs0, by simp⟩))
  have hev : riemannZeta₁ =ᶠ[𝓝 (3 : ℂ)] fun z => 1 - ∑' n, dz z n := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num : 2 < (3 : ℂ).re)]
      with w hw
    have hw1 : 1 < w.re := by linarith
    have hsum : Summable (cp w) := summable_cp hw1
    have hsum2 : Summable (fun n : ℕ => cp (w - 1) n) := by
      refine summable_cp ?_
      simp only [sub_re, one_re]
      linarith
    have hrec : (∑' n : ℕ, cp (w - 1) (n + 1)) = (∑' n : ℕ, cp (w - 1) n) - cp (w - 1) 0 := by
      have h := hsum2.tsum_eq_zero_add
      rw [h]; ring
    have htel : HasSum (fun n : ℕ => cp (w - 1) n - cp (w - 1) (n + 1)) 1 := by
      have h := hsum2.hasSum.sub (hsum2.comp_injective (Nat.succ_injective)).hasSum
      simp only [Function.comp_apply] at h
      rw [hrec] at h
      simpa [cp] using h
    have hcp : HasSum (cp w) (riemannZeta w) := by
      have hts : riemannZeta w = ∑' n : ℕ, cp w n := by
        rw [zeta_eq_tsum_one_div_nat_add_one_cpow hw1]
        exact tsum_congr fun n => by simp [cp, one_div, Complex.cpow_neg]
      rw [hts]
      exact hsum.hasSum
    have hdz := htel.sub (hcp.mul_left (w - 1))
    have hdz' : HasSum (fun n : ℕ => dz w n) (1 - (w - 1) * riemannZeta w) := by
      simpa [dz] using hdz
    rw [hdz'.tsum_eq]
    have hne : w - 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    have hone : w ≠ 1 := by intro h; exact hne (by simp [h])
    rw [show (w - 1) * riemannZeta w = riemannZeta₁ w by
      rw [riemannZeta_eq_inv_sub_mul hone, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]]
    ring
  have hEq : ∀ z : ℂ, 4⁻¹ < z.re → riemannZeta₁ z = 1 - ∑' n, dz z n := fun z hz =>
    (differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
      hfun (convex_halfSpace_re_gt 4⁻¹).isPreconnected
      (show (3 : ℂ) ∈ {z : ℂ | 4⁻¹ < z.re} by norm_num) hev hz
  have hbnd : ‖1 - ∑' n, dz s n‖ ≤ Cg * (‖s‖ + 1) ^ 2 := by
    have hsp : Summable (fun n : ℕ => ‖dz s n‖) :=
      (hS.mul_left ((‖s‖ + 1) ^ 2)).of_nonneg_of_le (fun n => norm_nonneg _) (fun n => termBound hs n)
    have hP : 0 ≤ ∑' n, pw n := tsum_nonneg fun n => by positivity
    have hsum_le : ‖∑' n, dz s n‖ ≤ ∑' n, ‖dz s n‖ := norm_tsum_le_tsum_norm hsp
    have hterm : (∑' n : ℕ, ‖dz s n‖) ≤ ∑' n : ℕ, (‖s‖ + 1) ^ 2 * pw n :=
      hsp.tsum_le_tsum (fun n => termBound hs n) (hS.mul_left _)
    have hX : 1 ≤ (‖s‖ + 1) ^ 2 := by nlinarith [norm_nonneg s]
    have hfin : (∑' n : ℕ, (‖s‖ + 1) ^ 2 * pw n) = (‖s‖ + 1) ^ 2 * ∑' n, pw n := tsum_mul_left
    rw [hfin] at hterm
    simp only [Cg]
    calc ‖1 - ∑' n, dz s n‖ ≤ 1 + ‖∑' n, dz s n‖ := by
          simpa using norm_sub_le (1 : ℂ) (∑' n, dz s n)
      _ ≤ 1 + ∑' n, ‖dz s n‖ := by linarith
      _ ≤ 1 + (‖s‖ + 1) ^ 2 * ∑' n, pw n := by linarith
      _ ≤ (1 + ∑' n, pw n) * (‖s‖ + 1) ^ 2 := by nlinarith
  rw [hEq s hs]
  exact hbnd

/-! ## Landau's lemma: analytic divided-difference peeling + Borel–Carathéodory -/

abbrev disk (r : ℝ) := closedBall (0 : ℂ) r⁻¹
abbrev U := ball (0 : ℂ) 6⁻¹

abbrev witness (f : ℂ → ℂ) (x : ℝ) := ∃ ρ ∈ disk 6, f ρ = 0 ∧ x ≤ ((-ρ)⁻¹).re

theorem landau {f : ℂ → ℂ} {B x : ℝ}
    (hd : DifferentiableOn ℂ f (disk 2)) (h0 : f 0 ≠ 0)
    (hb : ∀ w ∈ disk 2, ‖f w‖ ≤ B * ‖f 0‖)
    (hz : ∀ ρ ∈ disk 6, f ρ = 0 → ρ.re ≤ 0)
    (hx : x = 0 ∨ witness f x) :
    x - (deriv f 0 / f 0).re ≤ 24 * (Real.log B + 1) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B one_lt_two
  induction n generalizing f B x <;> have hB : 1 ≤ B := by nlinarith [hb 0 (by simp [disk]), norm_pos_iff.mpr h0]
  case zero => simp [hB.not_gt] at hn
  case succ n ih =>
    by_cases has : witness f x
    · obtain ⟨ρ, hr, hzero, hxρ⟩ := has
      let g := dslope f ρ
      have eqf w : f w = (w - ρ) * g w := (sub_smul_dslope_of_zero hzero w).symm
      have hρ : ρ ≠ 0 := by grind
      have hg0 := right_ne_zero_of_mul (eqf 0 ▸ h0)
      have hg : DifferentiableOn ℂ g _ :=
        (differentiableOn_dslope (closedBall_mem_nhds_of_mem (closedBall_subset_ball (by norm_num) hr))).mpr hd
      have grow w (hw : w ∈ disk 2) : ‖g w‖ ≤ B / 2 * ‖g 0‖ := by
        apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
          (hg.diffContOnCl_ball subset_rfl) _ (by rwa [closure_ball _ (by norm_num)])
        intro u hu
        simp [frontier_ball] at hu
        have h := hb u (mem_closedBall_zero_iff.mpr hu.le)
        simp [eqf u, eqf 0] at h
        nlinarith [norm_sub_norm_le u ρ, mem_closedBall_zero_iff.mp hr, norm_nonneg (g u), norm_pos_iff.mpr hρ]
      have ih0 := ih hg hg0 grow
        (fun w hw _ => hz w hw (by grind)) (Or.inl rfl) (by rw [pow_succ] at hn; linarith)
      have he := logDeriv_mul 0 (f := (· - ρ)) (by simpa) hg0 (by fun_prop)
        (hg.differentiableAt (closedBall_mem_nhds _ (by norm_num)))
      simp [← show f = (· - ρ) * g from funext eqf, logDeriv_apply] at he
      simp only [inv_neg] at hxρ
      rw [he, add_re]
      rw [Real.log_div (by linarith) (by norm_num)] at ih0; linarith [Real.log_pos one_lt_two]
    · obtain rfl := hx.resolve_right has
      have hs : U ⊆ disk 2 := ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
      have nonzero z (hz' : z ∈ U) : f z ≠ 0 := fun hf => has ⟨z, ball_subset_closedBall hz', hf, by
        simpa [inv_re] using div_nonpos_of_nonpos_of_nonneg (hz z (ball_subset_closedBall hz') hf) (normSq_nonneg z)⟩
      have diff := hd.mono hs
      grw [zero_sub, neg_le_abs, abs_re_le_norm]
      obtain ⟨g, hgz, hg⟩ := ((diff.deriv isOpen_ball).div diff nonzero).isExactOn_ball.with_val_at 0 0
      have hgd : DifferentiableOn ℂ g U := fun z hz => (hg z hz).differentiableAt.differentiableWithinAt
      let A := Real.log B + 1
      have hm : 0 < A := add_pos_of_nonneg_of_pos (Real.log_nonneg hB) zero_lt_one
      obtain ⟨c, hc, hfg⟩ := (logDeriv_eqOn_iff diff hgd.cexp isOpen_ball (convex_ball _ _).isPreconnected
        (by simp) nonzero).mp (by
          intro z hz'
          simp [logDeriv_apply, (hg z hz').cexp.deriv, exp_ne_zero])
      have hr z (hz' : z ∈ U) : (g z).re ≤ A := by
        have h := hb z (hs hz')
        simp [hfg hz', hfg (by simp [U] : 0 ∈ U), hgz, norm_exp] at h
        apply le_add_of_le_of_nonneg ((Real.le_log_iff_exp_le (by linarith)).2 ?_) zero_le_one
        nlinarith [norm_pos_iff.mpr hc]
      apply (hg 0 (by simp)).le_of_lip' (by positivity)
      filter_upwards [ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 12⁻¹)] with z hz'
      simp only [hgz, sub_zero]
      have hn := mem_ball_zero_iff.mp hz'
      have h := borelCaratheodory_zero hm hgd hr (by norm_num) (ball_subset_ball (by norm_num) hz') hgz
      rw [le_div_iff₀ (by linarith)] at h
      nlinarith [mul_nonneg (norm_nonneg (g z)) (sub_nonneg.mpr hn.le)]

/-! ## Log-derivative bookkeeping -/

abbrev J (z : ℂ) := (deriv riemannZeta₁ z / riemannZeta₁ z).re
def D (z : ℂ) := -(deriv riemannZeta z / riemannZeta z).re

lemma zeta₁_eq_mul {z : ℂ} (hz : z ≠ 1) : riemannZeta₁ z = (z - 1) * riemannZeta z := by
  rw [riemannZeta_eq_inv_sub_mul hz, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hz), one_mul]

lemma good {z : ℂ} (ha : 1 < z.re) : riemannZeta₁ z ≠ 0 ∧ D z = ((z - 1)⁻¹).re - J z := by
  have hn : z ≠ 1 := by rintro rfl; norm_num at ha
  have hf := riemannZeta_ne_zero_of_one_lt_re ha
  refine ⟨by grind [riemannZeta_eq_inv_sub_mul], ?_⟩
  have h : deriv riemannZeta z / riemannZeta z = -(z - 1)⁻¹ + deriv riemannZeta₁ z / riemannZeta₁ z := by
    grind [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add, riemannZeta_eq_inv_sub_mul]
  simp [D, h, sub_eq_add_neg, J, add_comm]

lemma triple {a : ℝ} (ha : 1 < a) (t : ℝ) :
    0 ≤ 3 * D ⟨a, 0⟩ + 4 * D ⟨a, t⟩ + D ⟨a, 2 * t⟩ := by
  let w (n : ℕ) := Λ n * Real.exp (-a * Real.log n)
  have S (v : ℝ) : HasSum (fun n : ℕ => w n * Real.cos (v * Real.log n)) (D ⟨a, v⟩) := by
    have h := (LSeriesSummable_vonMangoldt (s := ⟨a, v⟩) ha).LSeriesHasSum
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div ha, neg_div] at h
    apply (Complex.reCLM.hasSum h).congr_fun
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [w]
    rw [reCLM_apply, LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← cpow_neg, re_ofReal_mul,
      cpow_def_of_ne_zero (by exact_mod_cast hn), exp_re]
    simp [w, mul_re, mul_im, log_re, log_im, mul_comm, mul_assoc]
  apply HasSum.nonneg _ (((S 0).mul_left 3).add ((S t).mul_left 4) |>.add (S (2 * t)))
  intro n
  simp only [zero_mul, Real.cos_zero, mul_one, mul_assoc, Real.cos_two_mul]
  nlinarith [mul_nonneg (mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le : 0 ≤ w n)
    (sq_nonneg (1 + Real.cos (t * Real.log n)))]

set_option maxHeartbeats 4000000 in
theorem _root_.AlpogeRHCore1.zeroFreeRegion :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 →
      1 - c / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0 := by
  refine ⟨1 / 1000000000000, by norm_num, fun s hs1 hs hz => ?_⟩
  let R : ℝ := |s.im| + 2
  let d : ℝ := 1 - s.re
  have hR : 2 ≤ R := by dsimp [R]; linarith [abs_nonneg s.im]
  have hlogR : 1 / 2 ≤ Real.log R := by
    linarith [Real.log_two_gt_d9, Real.log_le_log (by norm_num) hR]
  have hlogR0 : 0 < Real.log R := by linarith
  have hd0 : 0 < d := by
    by_contra h
    push_neg at h
    exact (riemannZeta_ne_zero_of_one_le_re (by dsimp [d] at h; linarith)) hz
  have hdR : d * Real.log R ≤ 1 / 1000000000000 := by
    have h1 : 1 - 1 / 1000000000000 / Real.log R ≤ s.re := hs
    have h2 : d ≤ 1 / 1000000000000 / Real.log R := by dsimp [d]; linarith
    calc d * Real.log R ≤ (1 / 1000000000000 / Real.log R) * Real.log R :=
          mul_le_mul_of_nonneg_right h2 (le_of_lt hlogR0)
      _ = 1 / 1000000000000 := by field_simp
  have hd_small : d ≤ 2 / 1000000000000 := by nlinarith [hdR, hlogR, hd0]
  have hinv : (500000000000 : ℝ) ≤ 1 / d := by
    rw [le_div_iff₀ hd0]; nlinarith [hd_small]
  have hCg1 : 1 ≤ Cg := Cg_ge_one
  have hCg6 : Cg ≤ 6 := Cg_le_six
  have hCg0 : 0 < Cg := by linarith
  by_cases hcase : 25 * d ≤ |s.im|
  · -- ===== Case A: the zero is not too close to the real axis =====
    have hγ2 : 625 * d ^ 2 ≤ s.im ^ 2 := by nlinarith [hcase, abs_nonneg s.im, sq_abs s.im]
    let a : ℝ := 1 + 4 * d
    have ha : 1 < a := by dsimp [a]; linarith
    have hW {v x : ℝ} (hv : |v| ≤ 2 * R)
        (hx : x = 0 ∨ witness (fun w => riemannZeta₁ (⟨a, v⟩ + w)) x) :
        x + D ⟨a, v⟩ + 24 * Real.log ‖riemannZeta ⟨a, v⟩‖ ≤
          (((⟨a, v⟩ : ℂ) - 1)⁻¹).re + 24 * (Real.log (16 * Cg * R ^ 2) + 1 - Real.log (4 * d)) := by
      let z : ℂ := ⟨a, v⟩
      have hz1 : 1 < z.re := by dsimp [z, a]; linarith
      have hne : z ≠ 1 := by intro h; rw [h] at hz1; norm_num at hz1
      have hz1nz : riemannZeta₁ z ≠ 0 := (good hz1).1
      have hζnz : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz1
      have hnorm : ‖z‖ ≤ 3 * R := by
        have h1 := Complex.norm_le_abs_re_add_abs_im z
        change ‖z‖ ≤ |z.re| + |z.im| at h1
        have h2 : |z.re| = a := by rw [abs_of_pos]; dsimp [z, a]; linarith
        have h3 : |z.im| = |v| := rfl
        rw [h2, h3] at h1
        have h4 : a ≤ R := by dsimp [a]; linarith [hd_small, hR]
        linarith
      have hb : ∀ w ∈ disk 2, ‖riemannZeta₁ (z + w)‖ ≤
          (16 * Cg * R ^ 2 / ‖riemannZeta₁ z‖) * ‖riemannZeta₁ z‖ := by
        intro w hw
        have hw' : ‖w‖ ≤ 1 / 2 := by simpa [disk, mem_closedBall, one_div] using hw
        have hwr : -(1 / 2) ≤ w.re := (abs_le.mp ((abs_re_le_norm w).trans hw')).1
        have hre : 4⁻¹ < (z + w).re := by
          simp only [z, add_re, Complex.ofReal_re]
          dsimp [a]; linarith
        have hb1 : ‖riemannZeta₁ (z + w)‖ ≤ Cg * (‖z + w‖ + 1) ^ 2 := zeta_one_growth hre
        have hb2 : ‖z + w‖ + 1 ≤ 4 * R := by
          linarith [norm_add_le z w, hnorm, hw', hR]
        have hb3 : Cg * (‖z + w‖ + 1) ^ 2 ≤ 16 * Cg * R ^ 2 := by
          have h2 : (‖z + w‖ + 1) ^ 2 ≤ 16 * R ^ 2 := by
            nlinarith [hb2, hR, norm_nonneg (z + w)]
          nlinarith [hCg0]
        have hb4 : 16 * Cg * R ^ 2 / ‖riemannZeta₁ z‖ * ‖riemannZeta₁ z‖ = 16 * Cg * R ^ 2 :=
          div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz1nz)
        rw [hb4]
        exact hb1.trans hb3
      have hzero : ∀ ρ ∈ disk 6, (fun w => riemannZeta₁ (z + w)) ρ = 0 → ρ.re ≤ 0 := by
        intro ρ hρ hρ0
        by_contra hp
        push_neg at hp
        have h1 : 1 ≤ (z + ρ).re := by
          simp only [z, add_re, Complex.ofReal_re]
          dsimp [a]; linarith
        have hne2 : z + ρ ≠ 1 := by
          intro h
          have h2 := congrArg Complex.re h
          simp only [z, add_re, Complex.ofReal_re, Complex.one_re] at h2
          dsimp [a] at h2; linarith
        have hq : riemannZeta₁ (z + ρ) = 0 := hρ0
        have h3 : riemannZeta (z + ρ) = 0 := by
          rw [riemannZeta_eq_inv_sub_mul hne2, hq, mul_zero]
        exact riemannZeta_ne_zero_of_one_le_re h1 h3
      have h := landau (f := fun w => riemannZeta₁ (z + w))
        (B := 16 * Cg * R ^ 2 / ‖riemannZeta₁ z‖) (by fun_prop) (by simpa using hz1nz)
        (by simpa using hb) hzero hx
      have hgap : 4 * d ≤ ‖z - 1‖ := by
        have h1 := re_le_norm (z - 1)
        simp only [z, sub_re, Complex.ofReal_re, Complex.one_re] at h1
        dsimp [a] at h1
        linarith
      have hlog1 : Real.log ‖riemannZeta₁ z‖ = Real.log ‖z - 1‖ + Real.log ‖riemannZeta z‖ := by
        rw [zeta₁_eq_mul hne, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))
          (norm_ne_zero_iff.mpr hζnz)]
      have hlog2 : Real.log (4 * d) ≤ Real.log ‖z - 1‖ :=
        Real.log_le_log (by positivity) hgap
      have hspl : Real.log (16 * Cg * R ^ 2 / ‖riemannZeta₁ z‖) =
          Real.log (16 * Cg * R ^ 2) - Real.log ‖riemannZeta₁ z‖ :=
        Real.log_div (by positivity) (norm_ne_zero_iff.mpr hz1nz)
      have h' : x - (deriv (fun w => riemannZeta₁ (z + w)) 0 / riemannZeta₁ z).re ≤
          24 * (Real.log (16 * Cg * R ^ 2 / ‖riemannZeta₁ z‖) + 1) := by
        simpa using h
      rw [hspl] at h'
      have hJ : -((deriv (fun w => riemannZeta₁ (z + w)) 0 / riemannZeta₁ z).re) =
          D z - ((z - 1)⁻¹).re := by
        have e : deriv (fun w => riemannZeta₁ (z + w)) 0 = deriv riemannZeta₁ z := by
          simpa using deriv_comp_const_add (f := riemannZeta₁) (x := (0 : ℂ)) (a := z)
        rw [e, (good hz1).2]; ring
      linarith [h', hlog1, hlog2, hJ]
    have hP0 : (((⟨a, 0⟩ : ℂ) - 1)⁻¹).re = (4 * d)⁻¹ := by
      rw [Complex.inv_re, Complex.normSq_apply]
      simp [a]
    have hP1 : (((⟨a, s.im⟩ : ℂ) - 1)⁻¹).re ≤ 4 / (641 * d) := by
      rw [Complex.inv_re, Complex.normSq_apply]
      have hb1 : ((⟨a, s.im⟩ : ℂ) - 1).re = 4 * d := by simp [a]
      have hb2 : ((⟨a, s.im⟩ : ℂ) - 1).im = s.im := by simp
      rw [hb1, hb2,
        div_le_iff₀ (by nlinarith [sq_pos_of_pos hd0, sq_nonneg s.im] :
          (0 : ℝ) < 4 * d * (4 * d) + s.im * s.im),
        div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < 641 * d)]
      nlinarith [hγ2, hd0]
    have hP1b : 4 * (((⟨a, s.im⟩ : ℂ) - 1)⁻¹).re ≤ 16 * (641 * d)⁻¹ := by
      have h := mul_le_mul_of_nonneg_left hP1 (by norm_num : (0 : ℝ) ≤ 4)
      refine h.trans_eq ?_
      rw [div_eq_mul_inv]
      ring
    have hP2 : (((⟨a, 2 * s.im⟩ : ℂ) - 1)⁻¹).re ≤ 4 / (2516 * d) := by
      rw [Complex.inv_re, Complex.normSq_apply]
      have hb1 : ((⟨a, 2 * s.im⟩ : ℂ) - 1).re = 4 * d := by simp [a]
      have hb2 : ((⟨a, 2 * s.im⟩ : ℂ) - 1).im = 2 * s.im := by simp
      rw [hb1, hb2,
        div_le_iff₀ (by nlinarith [sq_pos_of_pos hd0, sq_nonneg s.im] :
          (0 : ℝ) < 4 * d * (4 * d) + 2 * s.im * (2 * s.im)),
        div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < 2516 * d)]
      nlinarith [hγ2, hd0]
    have hP2b : (((⟨a, 2 * s.im⟩ : ℂ) - 1)⁻¹).re ≤ 4 * (2516 * d)⁻¹ := by
      simpa only [div_eq_mul_inv] using hP2
    have hprod : 1 ≤ ‖riemannZeta ⟨a, 0⟩‖ ^ 3 * ‖riemannZeta ⟨a, s.im⟩‖ ^ 4 *
        ‖riemannZeta ⟨a, 2 * s.im⟩‖ := by
      simpa [DirichletCharacter.LFunctionTrivChar, Complex.mk_eq_add_mul_I, mul_comm, mul_left_comm,
        mul_assoc] using
        (1 : DirichletCharacter ℂ 1).norm_LFunction_product_ge_one (sub_pos.mpr ha) s.im
    have hlogprod : 0 ≤ 3 * Real.log ‖riemannZeta ⟨a, 0⟩‖ + 4 * Real.log ‖riemannZeta ⟨a, s.im⟩‖ +
        Real.log ‖riemannZeta ⟨a, 2 * s.im⟩‖ := by
      have h := Real.log_nonneg hprod
      simp (disch := simp [riemannZeta_ne_zero_of_one_lt_re (s := ⟨a, _⟩) ha]) [Real.log_mul,
        Real.log_pow] at h
      linarith
    have r := hW (v := 0) (x := 0) (by simp; linarith) (Or.inl rfl)
    have t := hW (v := s.im) (x := (5 * d)⁻¹) (by dsimp [R]; linarith [abs_nonneg s.im])
      (Or.inr ⟨-((5 * d : ℝ) : ℂ), by
        rw [disk, mem_closedBall_zero_iff, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0 : ℝ) < 5 * d)]
        norm_num
        nlinarith [hd_small],
        by
        show riemannZeta₁ ((⟨a, s.im⟩ : ℂ) + -((5 * d : ℝ) : ℂ)) = 0
        have h5 : ((⟨a, s.im⟩ : ℂ) + -((5 * d : ℝ) : ℂ)) = s := by
          apply Complex.ext <;> simp [a, d] <;> ring
        rw [h5, zeta₁_eq_mul hs1, hz, mul_zero],
        by
        show (5 * d)⁻¹ ≤ ((-(-((5 * d : ℝ) : ℂ)))⁻¹).re
        rw [show (-(-((5 * d : ℝ) : ℂ))) = ((5 * d : ℝ) : ℂ) by ring]
        simp⟩)
    have u := hW (v := 2 * s.im) (x := 0) (by simp [abs_mul]; dsimp [R]; linarith [abs_nonneg s.im])
      (Or.inl rfl)
    have M := triple ha s.im
    have q0 : 4 * (5 * d)⁻¹ ≤ 3 * (4 * d)⁻¹ + 16 * (641 * d)⁻¹ + 4 * (2516 * d)⁻¹ +
        192 * (Real.log (16 * Cg * R ^ 2) + 1 - Real.log (4 * d)) := by
      have hp := hlogprod
      have key : 3 * (0 + D ⟨a, 0⟩ + 24 * Real.log ‖riemannZeta ⟨a, 0⟩‖) +
          4 * ((5 * d)⁻¹ + D ⟨a, s.im⟩ + 24 * Real.log ‖riemannZeta ⟨a, s.im⟩‖) +
          (0 + D ⟨a, 2 * s.im⟩ + 24 * Real.log ‖riemannZeta ⟨a, 2 * s.im⟩‖) ≤
          3 * (((⟨a, 0⟩ : ℂ) - 1)⁻¹).re + 4 * (((⟨a, s.im⟩ : ℂ) - 1)⁻¹).re +
            (((⟨a, 2 * s.im⟩ : ℂ) - 1)⁻¹).re +
            192 * (Real.log (16 * Cg * R ^ 2) + 1 - Real.log (4 * d)) := by
        linarith [r, t, u]
      have key2 : 4 * (5 * d)⁻¹ ≤ 3 * (((⟨a, 0⟩ : ℂ) - 1)⁻¹).re +
          4 * (((⟨a, s.im⟩ : ℂ) - 1)⁻¹).re + (((⟨a, 2 * s.im⟩ : ℂ) - 1)⁻¹).re +
          192 * (Real.log (16 * Cg * R ^ 2) + 1 - Real.log (4 * d)) := by
        linarith [key, M, hp]
      have key3 : 4 * (5 * d)⁻¹ ≤ 3 * (4 * d)⁻¹ + 16 * (641 * d)⁻¹ + 4 * (2516 * d)⁻¹ +
          192 * (Real.log (16 * Cg * R ^ 2) + 1 - Real.log (4 * d)) := by
        linarith [key2, hP0, hP1b, hP2b]
      linarith [key3]
    have hlog16CgR : Real.log (16 * Cg * R ^ 2) = Real.log 16 + Real.log Cg + 2 * Real.log R := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow]
      ring
    have hlog16 : Real.log 16 ≤ 16 := (Real.log_le_self (by norm_num)).trans (by norm_num)
    have hlogCg : Real.log Cg ≤ 6 := (Real.log_le_self (le_of_lt hCg0)).trans hCg6
    have hlogRle : Real.log R ≤ 1 / 1000000000000 / d := by
      rw [le_div_iff₀ hd0]; linarith [hdR]
    have hlogT : Real.log ((4 * d)⁻¹) ≤ (4 * d)⁻¹ / 8000 := by
      have harg : (0 : ℝ) < (4 * d)⁻¹ := by positivity
      have hT : (256000000 : ℝ) ≤ (4 * d)⁻¹ := by
        rw [show (4 * d)⁻¹ = 1 / (4 * d) by rw [inv_eq_one_div], le_div_iff₀ (by positivity)]
        nlinarith [hd_small]
      have h1 : Real.log (4 * d)⁻¹ ≤ 2 * Real.sqrt (4 * d)⁻¹ := by
        have h := Real.log_le_rpow_div (x := (4 * d)⁻¹) (le_of_lt harg) (by norm_num : (0 : ℝ) < 1 / 2)
        rwa [show ((4 * d)⁻¹) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * Real.sqrt ((4 * d)⁻¹) by
          rw [Real.sqrt_eq_rpow]; ring] at h
      have h2 : 2 * Real.sqrt (4 * d)⁻¹ ≤ (4 * d)⁻¹ / 8000 := by
        have h4 : 16000 ≤ Real.sqrt (4 * d)⁻¹ := by
          calc (16000 : ℝ) = Real.sqrt ((16000 : ℝ) ^ 2) := by rw [Real.sqrt_sq (by norm_num)]
            _ ≤ Real.sqrt (4 * d)⁻¹ := Real.sqrt_le_sqrt (by linarith [hT])
        nlinarith [Real.sq_sqrt (le_of_lt harg)]
      linarith
    have hdL : d * (Real.log 16 + Real.log Cg + 2 * Real.log R + 1 - Real.log (4 * d)) ≤
        23 * d + 2 / 1000000000000 + 1 / 32000 := by
      have hneg : Real.log ((4 * d)⁻¹) = -Real.log (4 * d) := Real.log_inv _
      have h1 : d * Real.log ((4 * d)⁻¹) ≤ 1 / 32000 := by
        have h2 := mul_le_mul_of_nonneg_left hlogT (le_of_lt hd0)
        calc d * Real.log ((4 * d)⁻¹) ≤ d * ((4 * d)⁻¹ / 8000) := h2
          _ = 1 / 32000 := by field_simp; ring
      have h3 : d * Real.log R ≤ 1 / 1000000000000 := hdR
      have h4 : d * Real.log 16 ≤ 16 * d := by nlinarith [hlog16, hd0]
      have h5 : d * Real.log Cg ≤ 6 * d := by nlinarith [hlogCg, hd0]
      have hgoal : d * (Real.log 16 + Real.log Cg + 2 * Real.log R + 1 - Real.log (4 * d))
          = d * (Real.log 16 + Real.log Cg + 2 * Real.log R + 1 + Real.log ((4 * d)⁻¹)) := by
        rw [hneg]; ring
      rw [hgoal]
      nlinarith [h1, h3, h4, h5]
    have hL : 192 * (Real.log (16 * Cg * R ^ 2) + 1 - Real.log (4 * d)) * d ≤
        4416 * d + 384 / 1000000000000 + 3 / 500 := by
      rw [hlog16CgR]
      have h := mul_le_mul_of_nonneg_left hdL (by norm_num : (0 : ℝ) ≤ 192)
      nlinarith [h]
    have hmul := mul_le_mul_of_nonneg_left q0 (le_of_lt hd0)
    have hmul2 : 4 * (5 * d)⁻¹ * d ≤ 3 * (4 * d)⁻¹ * d + 16 * (641 * d)⁻¹ * d +
        4 * (2516 * d)⁻¹ * d + 192 * (Real.log (16 * Cg * R ^ 2) + 1 - Real.log (4 * d)) * d := by
      nlinarith [hmul]
    have e1 : 4 * (5 * d)⁻¹ * d = 4 / 5 := by field_simp
    have e2 : 3 * (4 * d)⁻¹ * d = 3 / 4 := by field_simp
    have e3 : 16 * (641 * d)⁻¹ * d = 16 / 641 := by field_simp
    have e4 : 4 * (2516 * d)⁻¹ * d = 4 / 2516 := by field_simp
    rw [e1, e2, e3, e4] at hmul2
    have hfin : (4 / 5 : ℝ) ≤ 3 / 4 + 16 / 641 + 4 / 2516 + 4416 * d +
        384 / 1000000000000 + 3 / 500 := by linarith [hmul2, hL]
    nlinarith [hfin, hd_small]
  · -- ===== Case B: the zero is extremely close to the real axis =====
    push_neg at hcase
    have hγ2' : s.im ^ 2 ≤ 625 * d ^ 2 := by nlinarith [hcase, abs_nonneg s.im, sq_abs s.im]
    have hζ1z : riemannZeta₁ s = 0 := by rw [zeta₁_eq_mul hs1, hz, mul_zero]
    let B2 : ℝ := 25 * Cg / 4
    have hB2pos : 0 < B2 := by dsimp [B2]; positivity
    have hB2 : B2 ≤ 25 * 6 / 4 := by dsimp [B2]; nlinarith
    have hb : ∀ w ∈ disk 2, ‖riemannZeta₁ (1 + w)‖ ≤ B2 * ‖riemannZeta₁ 1‖ := by
      intro w hw
      have hw' : ‖w‖ ≤ 1 / 2 := by simpa [disk, mem_closedBall, one_div] using hw
      have hwr : -(1 / 2) ≤ w.re := (abs_le.mp ((abs_re_le_norm w).trans hw')).1
      have hre : 4⁻¹ < (1 + w).re := by
        simp only [add_re, Complex.one_re]; linarith
      have h1 : ‖riemannZeta₁ (1 + w)‖ ≤ Cg * (‖1 + w‖ + 1) ^ 2 := zeta_one_growth hre
      have h2 : ‖1 + w‖ ≤ 3 / 2 := by
        have h := norm_add_le (1 : ℂ) w
        rw [norm_one] at h
        linarith
      have h3 : Cg * (‖1 + w‖ + 1) ^ 2 ≤ B2 := by
        have h5 : (‖1 + w‖ + 1) ^ 2 ≤ (5 / 2) ^ 2 := by nlinarith [norm_nonneg (1 + w)]
        dsimp [B2]
        nlinarith [hCg1, h5]
      calc ‖riemannZeta₁ (1 + w)‖ ≤ Cg * (‖1 + w‖ + 1) ^ 2 := h1
        _ ≤ B2 := h3
        _ = B2 * ‖riemannZeta₁ 1‖ := by rw [riemannZeta₁_one, norm_one, mul_one]
    have hzero : ∀ ρ ∈ disk 6, (fun w => riemannZeta₁ (1 + w)) ρ = 0 → ρ.re ≤ 0 := by
      intro ρ hρ hρ0
      by_contra hp
      push_neg at hp
      have h1 : 1 ≤ (1 + ρ).re := by simp only [add_re, Complex.one_re]; linarith
      have hne : 1 + ρ ≠ 1 := by
        intro h
        have h2 := congrArg Complex.re h
        simp only [add_re, Complex.one_re] at h2
        linarith
      have hq : riemannZeta₁ (1 + ρ) = 0 := hρ0
      have h3 : riemannZeta (1 + ρ) = 0 := by rw [riemannZeta_eq_inv_sub_mul hne, hq, mul_zero]
      exact riemannZeta_ne_zero_of_one_le_re h1 h3
    have hmem : s - 1 ∈ disk 6 := by
      have hsq : ‖s - 1‖ ^ 2 = d ^ 2 + s.im ^ 2 := by
        rw [show s - 1 = (⟨-d, s.im⟩ : ℂ) by
          apply Complex.ext <;> simp [d]]
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp
        ring
      rw [disk, mem_closedBall_zero_iff]
      norm_num
      nlinarith [hsq, hd_small, hγ2', hd0]
    have hwit : witness (fun w => riemannZeta₁ (1 + w)) (626 * d)⁻¹ := by
      refine ⟨s - 1, hmem, ?_, ?_⟩
      · show riemannZeta₁ (1 + (s - 1)) = 0
        rw [show (1 : ℂ) + (s - 1) = s by ring]
        exact hζ1z
      · show (626 * d)⁻¹ ≤ ((-(s - 1))⁻¹).re
        have hinv2 : ((-(s - 1))⁻¹).re = d / (d ^ 2 + s.im ^ 2) := by
          have h1 : -(s - 1) = (⟨d, -s.im⟩ : ℂ) := by
            apply Complex.ext <;> simp [d]
          rw [h1, Complex.inv_re, Complex.normSq_apply]
          simp
          ring
        rw [hinv2, show (626 * d)⁻¹ = 1 / (626 * d) by rw [inv_eq_one_div],
          div_le_iff₀ (by positivity : (0 : ℝ) < 626 * d),
          div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < d ^ 2 + s.im ^ 2)]
        nlinarith [hγ2', hd0]
    have h := landau (f := fun w => riemannZeta₁ (1 + w)) (B := B2) (by fun_prop)
      (by simpa using riemannZeta₁_one) (by simpa using hb) hzero (Or.inr hwit)
    have hball : ∀ w ∈ ball (0 : ℂ) (1 / 2),
        dist (riemannZeta₁ (1 + w)) (riemannZeta₁ (1 + 0)) ≤ 25 * Cg / 4 + 1 := by
      intro w hw
      have hw' : ‖w‖ < 1 / 2 := by simpa [mem_ball, dist_eq_norm] using hw
      have hwr : -(1 / 2) ≤ w.re := (abs_le.mp ((abs_re_le_norm w).trans hw'.le)).1
      have hre : 4⁻¹ < (1 + w).re := by simp only [add_re, Complex.one_re]; linarith
      have h1 : ‖riemannZeta₁ (1 + w)‖ ≤ Cg * (‖1 + w‖ + 1) ^ 2 := zeta_one_growth hre
      have h2 : ‖1 + w‖ ≤ 3 / 2 := by
        have h := norm_add_le (1 : ℂ) w
        rw [norm_one] at h
        linarith
      have h3 : Cg * (‖1 + w‖ + 1) ^ 2 ≤ 25 * Cg / 4 := by
        have h5 : (‖1 + w‖ + 1) ^ 2 ≤ (5 / 2) ^ 2 := by nlinarith [norm_nonneg (1 + w)]
        nlinarith [hCg1, h5]
      have hb1 : ‖riemannZeta₁ (1 + w)‖ ≤ 25 * Cg / 4 := h1.trans h3
      have h4 := norm_sub_le (riemannZeta₁ (1 + w)) 1
      rw [norm_one] at h4
      rw [show riemannZeta₁ (1 + 0) = 1 by rw [add_zero, riemannZeta₁_one], dist_eq_norm]
      linarith
    have hderiv : ‖deriv (fun w => riemannZeta₁ (1 + w)) 0‖ ≤ 25 * Cg / 2 + 2 := by
      have h1 := Complex.norm_deriv_le_div_of_mapsTo_ball (f := fun w => riemannZeta₁ (1 + w))
        (c := 0) (R₁ := 1 / 2) (R₂ := 25 * Cg / 4 + 1) (by fun_prop) ?_ (by norm_num)
      · rwa [show (25 * Cg / 4 + 1) / (1 / 2) = 25 * Cg / 2 + 2 by ring] at h1
      · intro w hw
        exact hball w hw
    have hmain : (626 * d)⁻¹ - (deriv (fun w => riemannZeta₁ (1 + w)) 0 / riemannZeta₁ (1 + 0)).re ≤
        24 * (Real.log B2 + 1) := h
    have hupper : (626 * d)⁻¹ ≤ 1200 := by
      have h1 : ((deriv (fun w => riemannZeta₁ (1 + w)) 0 / riemannZeta₁ (1 + 0)).re) ≤
          25 * Cg / 2 + 2 := by
        have h5 : (deriv (fun w => riemannZeta₁ (1 + w)) 0 / riemannZeta₁ (1 + 0)).re =
            (deriv (fun w => riemannZeta₁ (1 + w)) 0).re := by
          rw [show riemannZeta₁ (1 + 0) = 1 by rw [add_zero, riemannZeta₁_one], div_one]
        rw [h5]
        linarith [re_le_norm (deriv (fun w => riemannZeta₁ (1 + w)) 0), hderiv]
      have h2 : Real.log B2 + 1 ≤ 25 * 6 / 4 + 1 := by
        linarith [Real.log_le_self (le_of_lt hB2pos), hB2]
      linarith
    have hlower : (1000000 : ℝ) ≤ (626 * d)⁻¹ := by
      rw [show (626 * d)⁻¹ = 1 / (626 * d) by rw [inv_eq_one_div], le_div_iff₀ (by positivity)]
      nlinarith [hd_small]
    linarith
