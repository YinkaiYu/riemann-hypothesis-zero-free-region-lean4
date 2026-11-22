import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.LogDeriv
set_option autoImplicit true

/- The entire completion of (s−1)ζ(s) allows all three logarithmic derivatives
   to be estimated with the same disk lemma, including the real center. -/
open Complex hiding log
open Metric Set Filter MeasureTheory Asymptotics ArithmeticFunction Real Int LSeries DirichletCharacter Iff Or DifferentiableOn
noncomputable section
abbrev frac := ofReal ∘ fract
abbrev tail := (Ioi 1).indicator frac

lemma frac_bound x : ‖frac x‖ ≤ 1 := by
  simpa [frac,abs_fract] using (fract_lt_one x).le
abbrev remainder (z:ℂ) := ∫ x in Ioi (1:ℝ), (x:ℂ)^(-z-1)*frac x
lemma tail_smooth (hs : s.re<0) : DifferentiableAt ℂ (mellin tail) s := by
  have hb x : ‖tail x‖ ≤ 1 := (norm_indicator_le_norm_self frac x).trans (frac_bound x)
  apply mellin_differentiableAt_of_isBigO_rpow (a:=0) (b:=s.re-1)
  · exact (locallyIntegrableOn_const (1:ℂ)).mono (by measurability) (by simpa using Eventually.of_forall hb)
  · exact isBigO_of_le _ (by simpa using hb)
  · assumption
  · apply IsBigO.of_bound'
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)] with x (hx:x<1)
    simp [tail,hx.not_gt]
  · linarith

lemma remainder_eq : remainder = fun z => mellin tail (-z) := by
  funext z; rw [mellin,tail,←indicator_smul,setIntegral_indicator measurableSet_Ioi];simp;rfl

lemma entireFormula (hs : 0 < s.re) : riemannZeta₁ s = s * (1-(s-1)*remainder s) := by
  apply (differentiable_riemannZeta₁.differentiableOn.analyticOnNhd (isOpen_re_gt 0)).eqOn_of_preconnected_of_eventuallyEq
    (DifferentiableOn.analyticOnNhd (by intro z hz; have := tail_smooth (s:=-z) (by simpa using hz); rw [remainder_eq]; fun_prop) (isOpen_re_gt 0))
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by norm_num) _ hs
  filter_upwards [(isOpen_re_gt 1).mem_nhds (x:=2) (by norm_num)] with z hz
  have h := LSeries_eq_mul_integral' 1 zero_le_one hz (by simp; rfl)
  simp [LSeries_one_eq_riemannZeta hz] at h
  have hi := integral_Ioi_cpow_of_lt (a := -z) (by simpa) zero_lt_one
  simp [← neg_sub z 1,neg_add_eq_sub,-neg_sub] at hi
  suffices riemannZeta z = z*((z-1)⁻¹-remainder z) by
    have hn : z≠1 := by grind [one_re]
    grind [riemannZeta_eq_inv_sub_mul hn]
  rw [h, ← hi, ← integral_sub
    (integrableOn_Ioi_cpow_of_lt (by simpa) zero_lt_one)
    ((integrableOn_Ioi_cpow_of_lt (by simp;linarith) zero_lt_one).mul_bdd
      (by fun_prop : Measurable frac).aestronglyMeasurable (.of_forall frac_bound))]
  congr 1; refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0<x := zero_lt_one.trans hx
  have hxC := ofReal_ne_zero.mpr hx0.ne'
  simp [frac, fract, ← natCast_floor_eq_floor hx0.le,
    neg_add_eq_sub,cpow_neg, cpow_sub _ _ hxC]; field [hxC]

lemma mellin_bound (hs : 0 < s.re) : ‖remainder s‖ ≤ 1 / s.re := by
  have he : -s.re - 1 < -1 := by linarith
  refine (norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt he zero_lt_one) ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    grw [norm_mul,frac_bound]
    simp [norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx)]
  · simp [integral_Ioi_rpow_of_lt he zero_lt_one]

lemma growth (h : 1/2≤s.re) : ‖riemannZeta₁ s‖≤(2*‖s‖+2)^2 := by
  have hp : 0<s.re := by linarith
  grw [entireFormula hp,norm_mul,norm_sub_le,norm_mul,norm_sub_le,mellin_bound hp,←h];norm_num
  nlinarith [norm_nonneg s]

abbrev U : Set ℂ := ball 0 6⁻¹

abbrev hasZero (f : ℂ → ℂ) x := ∃ q, norm q ≤ 6⁻¹ ∧ f q = 0 ∧ x ≤ -re q⁻¹

lemma landau {f B x}
    (hd : DifferentiableOn ℂ f <| closedBall 0 2⁻¹) (h0 : f 0 ≠ 0)
    (hb : ∀ w, norm w ≤ 2⁻¹ → ‖f w‖ ≤ B * ‖f 0‖)
    (hz : ∀ q, f q = 0 → re q ≤ 0)
    (hx : x = 0 ∨ hasZero f x) :
    x - re (logDeriv f 0) ≤ 24 * (log B + 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt <| 2 * B
  induction n generalizing f B x <;> have hB := one_le_of_le_mul_right₀ (mpr norm_pos_iff h0) <| hb 0 <| by simp
  case zero => grind
  case succ n ih =>
    rcases em (hasZero f x) with ⟨q, hr, hzero, hxq⟩ | has
    obtain ⟨g, hg, rfl⟩ : ∃ g, DifferentiableOn ℂ g _ ∧ (· - q) * g = f :=
      ⟨_, mpr (differentiableOn_dslope <| closedBall_mem_nhds_of_mem <| by simp; linarith) hd,
      funext <| sub_smul_dslope_of_zero hzero⟩
    simp at h0 hz
    have ih0 := ih (B := B / 2) hg h0.right (fun w hw => norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (diffContOnCl_ball hg subset_rfl) (fun u hu => by
        simp [frontier_ball] at hu hb
        nlinarith [hb u hu.le, norm_sub_norm_le u q, norm_nonneg (g u), mpr norm_pos_iff h0.left])
      (by simpa [closure_ball])) (by grind) (inl rfl) <| by grind
    have := differentiableAt hg <| closedBall_mem_nhds 0 <| by norm_num
    rw [logDeriv_mul] <;> first | fun_prop | simp_all [logDeriv_apply]
    grw [half_le_self <| le_trans zero_le_one hB] at ih0; linarith
    obtain rfl := resolve_right hx has
    have nonzero z (hz' : z ∈ U) hf := has ⟨z, by simp at hz'; linarith, hf, by
      simpa [inv_re] using div_nonpos_of_nonpos_of_nonneg (hz z hf) <| normSq_nonneg z⟩
    have h0U : 0 ∈ U := by simp
    have diff := mono hd (s := U) fun z h => by simp at h ⊢; linarith
    obtain ⟨g, hgz, hg⟩ := div (diff.deriv isOpen_ball) diff nonzero |>.isExactOn_ball.with_val_at 0 0
    have hgd : DifferentiableOn ℂ g U := fun z hz => hg z hz |>.differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hfg⟩ := mp (logDeriv_eqOn_iff diff hgd.cexp isOpen_ball isPreconnected_ball
      (by simp) nonzero) <| fun z hz' => by simp [logDeriv_apply, hg z hz' |>.cexp.deriv]
    grw [zero_sub, neg_le_abs, abs_re_le_norm, logDeriv, ← hg 0 h0U |>.deriv,
      norm_deriv_le_of_forall_mem_sphere_norm_le (R := 12⁻¹) (C := 2 * (log B + 1)) (by norm_num)
      (diffContOnCl_ball hgd <| closedBall_subset_ball <| by norm_num) fun z hz => by
        simp at hz
        grw [borelCaratheodory_zero (M := log B + 1) (by linarith [log_nonneg hB]) hgd (fun z hz' => by
          have h := hb z <| by simp at hz'; linarith
          simp [hfg hz', hfg h0U, hgz, norm_exp, mul_comm B, mpr norm_pos_iff hc,
            ← le_log_iff_exp_le <| lt_of_lt_of_le zero_lt_one hB] at h
          dsimp; linarith)
          (by norm_num) (by simp; linarith) hgz]
        norm_num [hz]]
    grind

lemma good (ha : 1 < s.re) : riemannZeta₁ s ≠ 0 ∧ deriv riemannZeta₁ s / riemannZeta₁ s =
    (s-1)⁻¹ - LSeries (fun n => (Λ n : ℂ)) s := by
  have := riemannZeta_ne_zero_of_one_lt_re ha
  have hn : s ≠ 1 := by grind [one_re]
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div ha]
  grind [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add,riemannZeta_eq_inv_sub_mul]

theorem _root_.AlpogeRHCore1.zeroFreeRegion :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 → 1-c/(|s.im|+2).log ≤ s.re → riemannZeta s ≠ 0 := by
  refine ⟨1/2^20,by positivity,fun s hn hs hz => ?_⟩
  let R := |s.im|+2
  have hL := log_two_gt_d9.trans_le (log_le_log zero_lt_two (by simp [R]:2≤R))
  have hpos : 0<R.log := by linarith
  let d := 1/2^20 / R.log
  have hd : 0<d := by positivity
  have tiny : d≤1/100 := (div_le_iff₀ hpos).2 (by linarith)
  change 1-d≤s.re at hs
  have bad : riemannZeta₁ s=0 := by grind [riemannZeta_eq_inv_sub_mul]
  have hht : 1/2≤|s.im| := by
    have hp : 0 < s.re := by linarith
    have eq : remainder s = (s-1)⁻¹ := by grind [entireFormula hp, zero_re]
    have h := mellin_bound hp
    simp [eq,one_div,inv_le_inv₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hn)) hp] at h
    have hb := norm_le_abs_re_add_abs_im (s-1)
    simp at hb
    grind [abs_eq_max_neg]
  let a := s.re+5*d
  have hgap : 2^2*d≤a-1 := by grind
  have ha : 1<a := by linarith
  have K v := good (s:=⟨a,v⟩) ha
  have W v x (hv:|v|≤2*|s.im|) := landau (f:=fun w => riemannZeta₁ (⟨a,v⟩+w)) (B:=(2^4*R)^2/‖riemannZeta₁ ⟨a,v⟩‖) (x:=x)
    (by fun_prop) (by simpa using (K v).1) (fun w hw => by
      simp [(K v).1]
      grw [growth (by grind [add_re,abs_re_le_norm w,abs_eq_max_neg]),norm_add_le,norm_le_abs_re_add_abs_im (⟨a,v⟩:ℂ)]
      gcongr
      grind [abs_eq_max_neg,riemannZeta_ne_zero_of_one_le_re])
    (fun w he => by grind [good (s:=⟨a,v⟩+w),add_re])
  have r := W 0 0 (by simp) (.inl rfl)
  have t := W s.im (5*d)⁻¹ (by linarith) (.inr ⟨-(5*d),by
    simp [abs_of_pos hd];linarith,by convert bad using 2;simp [Complex.ext_iff,a],by simp⟩)
  have u := W (2*s.im) 0 (by simp [abs_mul]) (.inl rfl)
  have hp := (1:DirichletCharacter ℂ 1).norm_LFunction_product_ge_one (sub_pos.mpr ha) s.im
  have gap v := hgap.trans (re_le_norm ((⟨a,v⟩:ℂ)-1))
  simp (disch := grind [one_re]) [LFunctionTrivChar,show ∀ x y:ℂ, x+y=⟨_,_⟩ from fun _ _ => rfl,ofReal_def,riemannZeta_eq_inv_sub_mul] at hp
  repeat grw [←gap] at hp
  apply log_nonneg at hp
  simp (disch:=first | positivity | simp [hpos.ne',(K _).1]) [-inv_re,logDeriv_apply,deriv_comp_const_add,(K _).2,Real.log_div,Real.log_mul,log_pow,d] at hp r t u
  simp [inv_re,normSq_apply] at r
  have pole := inv_anti₀ (by positivity) hgap
  have negt := inv_anti₀ (by positivity) hht
  grw [re_le_norm,norm_inv,←abs_im_le_norm ((⟨a,_⟩:ℂ)-1)] at t u <;> try (simp;grind)
  simp [d,abs_mul,div_eq_mul_inv,mul_inv_rev] at t u pole negt
  -- The trigonometric square supplies positivity at all three heights.
  have S v := hasSum_re (LSeriesSummable_vonMangoldt (s:=⟨a,v⟩) ha).LSeriesHasSum
  have M := HasSum.nonneg (fun n => by
    simp [term_def₀,cpow_def]
    split_ifs <;> simp_all [exp_re,mul_re,mul_im,log_re,log_im,mul_comm (Real.log _),mul_assoc,Real.cos_two_mul]
    linear_combination (2*Λ n*Real.exp _) * sq_nonneg (1+Real.cos _)) (((S 0).mul_left 3).add ((S s.im).mul_left 4) |>.add (S (2*s.im)))
  linarith [log_le_self hpos.le,log_two_lt_d9]

