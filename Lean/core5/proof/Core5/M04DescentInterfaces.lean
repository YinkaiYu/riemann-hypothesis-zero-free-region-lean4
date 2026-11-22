import Mathlib
import Core5.M03DifferentialIdeals

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

universe u v
noncomputable section
-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SmoothComponentsDisjoint
section

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

def IrreducibleComponentsDisjointOfSmooth : Prop :=
  ∀ (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)),
    Smooth p →
    ∀ C₁ ∈ irreducibleComponents ↥X, ∀ C₂ ∈ irreducibleComponents ↥X,
      C₁ ≠ C₂ → Disjoint C₁ C₂

theorem irreducibleComponentsDisjointOfSmooth : IrreducibleComponentsDisjointOfSmooth.{u} := by
  intro k _ X p hp C₁ h₁ C₂ h₂ hne
  have : Smooth p := hp
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  exact hne
    (irreducibleComponents_eq_of_stalk_isDomain X
      (fun y => isDomain_stalk_of_smooth p y) h₁ h₂ hx₁ hx₂)

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplitting
section
open AlgebraicGeometry CategoryTheory


namespace FunctorialResolution.EmbeddedResolution

variable {X : Scheme.{u}}

def IsMonomialIn (E : List X.IdealSheafData) (M : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ a : Fin E.length → ℕ,
    M.comap U.ι = ∏ i : Fin E.length, (E.get i).comap U.ι ^ a i

structure IsMonomialSplitting (E : List X.IdealSheafData) (I M N : X.IdealSheafData) :
    Prop where
  eq_mul : I = M * N
  monomial_support : (M.support : Set X) ⊆ ⋃ D ∈ E, (D.support : Set X)
  monomial : IsMonomialIn E M
  transversal : ∀ D ∈ E, ∀ C : Set X, IsIrreducible C → C ⊆ (D.support : Set X) →
    (∀ C' : Set X, IsIrreducible C' → C' ⊆ (D.support : Set X) → C ⊆ C' → C' ⊆ C) →
    ¬ C ⊆ (N.support : Set X)

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupChartCongruence
section
open CategoryTheory AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution


section

variable {B A : Type u} [CommRing B] [CommRing A]

def eqModIdealSet (f g : B →+* A) (J : Ideal A) : Set B := {b | f b - g b ∈ J}

section
variable (f g : B →+* A) (J : Ideal A)

private theorem one_mem_eqModIdealSet_consolidated166 :
    (1 : B) ∈ eqModIdealSet f g J := by
  show f 1 - g 1 ∈ J
  rw [map_one, map_one, sub_self]
  exact J.zero_mem

private theorem zero_mem_eqModIdealSet_consolidated166 :
    (0 : B) ∈ eqModIdealSet f g J := by
  show f 0 - g 0 ∈ J
  rw [map_zero, map_zero, sub_self]
  exact J.zero_mem

private theorem add_mem_eqModIdealSet_consolidated166 {x y : B}
    (hx : x ∈ eqModIdealSet f g J) (hy : y ∈ eqModIdealSet f g J) : x + y ∈ eqModIdealSet f g J := by
  show f (x + y) - g (x + y) ∈ J
  rw [map_add, map_add]
  have hrw : f x + f y - (g x + g y) = (f x - g x) + (f y - g y) := by ring
  rw [hrw]
  exact J.add_mem hx hy

private theorem neg_mem_eqModIdealSet_consolidated166 {x : B}
    (hx : x ∈ eqModIdealSet f g J) : -x ∈ eqModIdealSet f g J := by
  show f (-x) - g (-x) ∈ J
  rw [map_neg, map_neg]
  have hrw : -f x - -g x = -(f x - g x) := by ring
  rw [hrw]
  exact J.neg_mem hx

private theorem mul_mem_eqModIdealSet_consolidated166 {x y : B}
    (hx : x ∈ eqModIdealSet f g J) (hy : y ∈ eqModIdealSet f g J) : x * y ∈ eqModIdealSet f g J := by
  show f (x * y) - g (x * y) ∈ J
  rw [map_mul, map_mul]
  have hrw : f x * f y - g x * g y = f x * (f y - g y) + (f x - g x) * g y := by ring
  rw [hrw]
  exact J.add_mem (J.mul_mem_left _ hy) (J.mul_mem_right _ hx)


end

def eqModIdealSubring (f g : B →+* A) (J : Ideal A) : Subring B where
  carrier := eqModIdealSet f g J
  one_mem' := one_mem_eqModIdealSet_consolidated166 f g J
  zero_mem' := zero_mem_eqModIdealSet_consolidated166 f g J
  add_mem' := add_mem_eqModIdealSet_consolidated166 f g J
  neg_mem' := neg_mem_eqModIdealSet_consolidated166 f g J
  mul_mem' := mul_mem_eqModIdealSet_consolidated166 f g J

theorem sub_mem_ideal_of_subring_closure_eq_top (f g : B →+* A) (J : Ideal A) (S : Set B)
    (hS : Subring.closure S = ⊤) (hmem : ∀ b ∈ S, f b - g b ∈ J) (b : B) :
    f b - g b ∈ J := by
  have hsub : Subring.closure S ≤ eqModIdealSubring f g J :=
    Subring.closure_le.mpr (fun x hx => hmem x hx)
  rw [hS] at hsub
  exact hsub (Subring.mem_top b)

end

section
variable {M : Type u} [CommRing M]

private theorem eq_mul_pow_zero_consolidated166 (x c : M) : x = x * c ^ 0 := by ring

private theorem mul_add_mul_eq_add_mul_consolidated166 (x y c : M) :
    x * c + y * c = (x + y) * c := by ring

private theorem self_sub_self_eq_zero_consolidated166 (x : M) : x - x = 0 := by ring


end

private theorem localization_mk_eq_mk_one_of_eq_mul_consolidated166 {M : Type u} [CommMonoid M] {S : Submonoid M}
    (x y d : M) (hd : d ∈ S) (h : x = d * y) :
    Localization.mk x ⟨d, hd⟩ = Localization.mk y (1 : ↥S) := by
  rw [Localization.mk_eq_mk_iff]
  refine Localization.r_of_eq ?_
  simp [h]

section

variable {R : Type u} [CommRing R]

section
variable (I : Ideal R) (a : I)

private theorem val_chartRingHom_consolidated166 (t : R) :
    HomogeneousLocalization.val (Blowup.chartRingHom I a t)
      = Localization.mk (↑(Blowup.reesDegreeZeroEquiv I t) : ↥(reesAlgebra I))
          (1 : ↥(Submonoid.powers (Blowup.reesGenerator I a))) := by
  rw [Blowup.chartRingHom_apply]
  rfl

private theorem exists_pow_mul_eq_consolidated166 (z : HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) :
    ∃ (n : ℕ) (r : R), r ∈ I ^ n ∧
      z * Blowup.chartRingHom I a (a : R) ^ n = Blowup.chartRingHom I a r := by
  obtain ⟨m, hm⟩ := HomogeneousLocalization.den_mem z
  have hden : HomogeneousLocalization.den z = Blowup.reesGenerator I a ^ m := hm.symm
  have hdencoe : ((HomogeneousLocalization.den z : ↥(reesAlgebra I)) : Polynomial R)
      = Polynomial.monomial m ((a : R) ^ m) := by
    rw [hden, SubmonoidClass.coe_pow, Blowup.reesGenerator_coe, Polynomial.monomial_pow, one_mul]
  have hpow : (Blowup.chartRingHom I a) ((a : R) ^ m) = (Blowup.chartRingHom I a) (a : R) ^ m :=
    map_pow (Blowup.chartRingHom I a) (a : R) m
  by_cases hdeg : HomogeneousLocalization.deg z = m
  · have hnum : HomogeneousLocalization.num z ∈ Blowup.reesGrading I m := by
      rw [← hdeg]
      exact HomogeneousLocalization.num_mem_deg z
    obtain ⟨s, hs, hseq⟩ :=
      (Blowup.mem_reesGrading_iff_monomial I m (HomogeneousLocalization.num z)).mp hnum
    refine ⟨m, s, hs, ?_⟩
    have key : (HomogeneousLocalization.num z)
          * (↑(Blowup.reesDegreeZeroEquiv I ((a : R) ^ m)) : ↥(reesAlgebra I))
        = (HomogeneousLocalization.den z) * (↑(Blowup.reesDegreeZeroEquiv I s) : ↥(reesAlgebra I)) := by
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, hseq, hdencoe, Blowup.reesDegreeZeroEquiv_coe_coe]
      rw [mul_comm (Polynomial.monomial m s) (Polynomial.C ((a : R) ^ m)),
        Polynomial.C_mul_monomial,
        mul_comm (Polynomial.monomial m ((a : R) ^ m)) (Polynomial.C s),
        Polynomial.C_mul_monomial, mul_comm ((a : R) ^ m) s]
    rw [← hpow]
    apply HomogeneousLocalization.val_injective (Submonoid.powers (Blowup.reesGenerator I a))
    rw [HomogeneousLocalization.val_mul, val_chartRingHom_consolidated166, val_chartRingHom_consolidated166,
      HomogeneousLocalization.eq_num_div_den z, Localization.mk_mul, mul_one]
    exact localization_mk_eq_mk_one_of_eq_mul_consolidated166 _ _ _ _ key
  · have hzero : (a : R) ^ m = 0 := by
      have h1 := (Blowup.mem_reesGrading_iff_coeff I (HomogeneousLocalization.deg z)
        (HomogeneousLocalization.den z)).mp (HomogeneousLocalization.den_mem_deg z) m
        (fun h => hdeg h.symm)
      rw [hdencoe] at h1
      simpa using h1
    refine ⟨m, 0, Ideal.zero_mem _, ?_⟩
    rw [← hpow, hzero, map_zero]
    exact mul_zero z

private theorem exists_mem_closure_chartRingHom_eq_mul_pow_consolidated166 (n : ℕ) :
    ∀ r ∈ I ^ n, ∃ w ∈ Subring.closure
        (Set.range ⇑(Blowup.chartRingHom I a) ∪ Set.range (Blowup.chartFraction I a)),
      Blowup.chartRingHom I a r = w * Blowup.chartRingHom I a (a : R) ^ n := by
  induction n with
  | zero =>
    intro r _
    refine ⟨Blowup.chartRingHom I a r, Subring.subset_closure (Or.inl ⟨r, rfl⟩), ?_⟩
    exact eq_mul_pow_zero_consolidated166 (M := HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) _ _
  | succ n ih =>
    intro r hr
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro s hs b hb
      obtain ⟨w, hw, hweq⟩ := ih s hs
      have hbb : Blowup.chartRingHom I a b
          = Blowup.chartFraction I a ⟨b, hb⟩ * Blowup.chartRingHom I a (a : R) :=
        Blowup.chartRingHom_coe_eq_chartFraction_mul I a ⟨b, hb⟩
      refine ⟨w * Blowup.chartFraction I a ⟨b, hb⟩,
        Subring.mul_mem _ hw (Subring.subset_closure (Or.inr ⟨⟨b, hb⟩, rfl⟩)), ?_⟩
      rw [map_mul, hweq, hbb]
      ring
    · rintro x y ⟨wx, hwx, hx⟩ ⟨wy, hwy, hy⟩
      refine ⟨wx + wy, Subring.add_mem _ hwx hwy, ?_⟩
      rw [map_add, hx, hy]
      exact mul_add_mul_eq_add_mul_consolidated166 wx wy _

theorem closure_chartRingHom_union_chartFraction_eq_top :
    Subring.closure
        (Set.range ⇑(Blowup.chartRingHom I a) ∪ Set.range (Blowup.chartFraction I a)) = ⊤ := by
  rw [Subring.eq_top_iff']
  intro z
  obtain ⟨n, r, hr, hz⟩ := exists_pow_mul_eq_consolidated166 I a z
  obtain ⟨w, hw, hweq⟩ := exists_mem_closure_chartRingHom_eq_mul_pow_consolidated166 I a n r hr
  have e1 : (z - w) * Blowup.chartRingHom I a (a : R) ^ n
      = z * Blowup.chartRingHom I a (a : R) ^ n - w * Blowup.chartRingHom I a (a : R) ^ n :=
    sub_mul z w _
  have h0 : (z - w) * Blowup.chartRingHom I a (a : R) ^ n = 0 := by
    rw [e1, hz, ← hweq]
    exact self_sub_self_eq_zero_consolidated166
      (M := HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) _
  have hnzd : Blowup.chartRingHom I a (a : R) ^ n
      ∈ nonZeroDivisors (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) :=
    pow_mem (Blowup.chartRingHom_mem_nonZeroDivisors I a) n
  have hzw : z - w = 0 := (mem_nonZeroDivisors_iff.mp hnzd).2 _ h0
  have hzeq : z = w := sub_eq_zero.mp hzw
  rw [hzeq]
  exact hw


end

theorem chartFraction_sub_mem_of_congr {A : Type u} [CommRing A] (I : Ideal R) (a : I)
    (φ φ' : HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a) →+* A)
    (σ σ' : R →+* A) (𝔟 : Ideal A)
    (hφ : ∀ r : R, φ (Blowup.chartRingHom I a r) = σ r)
    (hφ' : ∀ r : R, φ' (Blowup.chartRingHom I a r) = σ' r)
    (hcongr : ∀ r : R, σ r - σ' r ∈ Ideal.span {σ (a : R)} * 𝔟)
    (hnzd : σ (a : R) ∈ nonZeroDivisors A)
    (u : A) (hu : σ' (a : R) = u * σ (a : R)) (b : I) :
    φ (Blowup.chartFraction I a b) - φ' (Blowup.chartFraction I a b) ∈ 𝔟 := by
  obtain ⟨c, hc, hcEq⟩ := Ideal.mem_span_singleton_mul.mp (hcongr (a : R))
  obtain ⟨d, hd, hdEq⟩ := Ideal.mem_span_singleton_mul.mp (hcongr (b : R))
  have hone : (1 : A) - u ∈ 𝔟 := by
    have h1 : σ (a : R) - σ' (a : R) = σ (a : R) * c := hcEq.symm
    rw [hu] at h1
    have h0 : ((1 : A) - u - c) * σ (a : R) = 0 := by linear_combination h1
    have h2 := (mem_nonZeroDivisors_iff.mp hnzd).2 _ h0
    have h3 : (1 : A) - u = c := by linear_combination h2
    rw [h3]
    exact hc
  have hb1 : σ (b : R) = φ (Blowup.chartFraction I a b) * σ (a : R) := by
    rw [← hφ (b : R), ← hφ (a : R), ← map_mul, Blowup.chartRingHom_coe_eq_chartFraction_mul I a b]
  have hb2 : σ' (b : R) = φ' (Blowup.chartFraction I a b) * σ' (a : R) := by
    rw [← hφ' (b : R), ← hφ' (a : R), ← map_mul, Blowup.chartRingHom_coe_eq_chartFraction_mul I a b]
  have h2 : σ (b : R) - σ' (b : R) = σ (a : R) * d := hdEq.symm
  rw [hb1, hb2, hu] at h2
  have h0 : (φ (Blowup.chartFraction I a b) - u * φ' (Blowup.chartFraction I a b) - d) * σ (a : R) = 0 := by
    linear_combination h2
  have h3 := (mem_nonZeroDivisors_iff.mp hnzd).2 _ h0
  have hfin : φ (Blowup.chartFraction I a b) - φ' (Blowup.chartFraction I a b)
      = d - (1 - u) * φ' (Blowup.chartFraction I a b) := by linear_combination h3
  rw [hfin]
  exact 𝔟.sub_mem hd (𝔟.mul_mem_right _ hone)

end

section

variable {R : Type u} [CommRing R]

private theorem sectionsRingHom_comp_consolidated166 {A : Type u} [CommRing A] {Z W : Scheme.{u}} (p : Z ⟶ W)
    (ρ : W ⟶ Spec (CommRingCat.of A)) (V : W.Opens) (V' : Z.Opens)
    (hle : V' ≤ (Opens.map p.base).obj V) (r : A) :
    Blowup.sectionsRingHom (p ≫ ρ) V' r
      = (CommRingCat.Hom.hom (Scheme.Hom.appLE p V V' hle)) (Blowup.sectionsRingHom ρ V r) := by
  rw [Blowup.sectionsRingHom_apply, Blowup.sectionsRingHom_apply]
  conv_rhs => rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

section
variable {W : Scheme.{u}} (𝔞 : W.IdealSheafData) (V : W.affineOpens)

private theorem mem_ideal_of_app_subschemeι_eq_zero_consolidated166 (x : ↥(W.presheaf.obj (Opposite.op (V : W.Opens))))
    (hx : (CommRingCat.Hom.hom (Scheme.Hom.app 𝔞.subschemeι (V : W.Opens))) x = 0) :
    x ∈ 𝔞.ideal V := by
  rw [Scheme.IdealSheafData.subschemeι_app 𝔞 V, CommRingCat.comp_apply] at hx
  have h2 := congrArg (CommRingCat.Hom.hom (𝔞.subschemeObjIso V).hom) hx
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id] at h2
  simpa [Ideal.Quotient.eq_zero_iff_mem] using h2

private theorem app_subschemeι_eq_zero_of_mem_ideal_consolidated166 {x : ↥(W.presheaf.obj (Opposite.op (V : W.Opens)))}
    (hx : x ∈ 𝔞.ideal V) :
    (CommRingCat.Hom.hom (Scheme.Hom.app 𝔞.subschemeι (V : W.Opens))) x = 0 := by
  rw [Scheme.IdealSheafData.subschemeι_app 𝔞 V, CommRingCat.comp_apply]
  simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]


end

section
variable {X Y : Scheme.{u}}

private theorem appLE_top_top_consolidated166 (f : X ⟶ Y)
    (e : (⊤ : X.Opens) ≤ (Opens.map f.base).obj ⊤) :
    Scheme.Hom.appLE f ⊤ ⊤ e = Scheme.Hom.appTop f :=
  Scheme.Hom.appLE_eq_app (f := f)

private theorem appLE_congr_hom_consolidated166 {f g : X ⟶ Y} (hfg : f = g)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ (Opens.map f.base).obj U)
    (e' : V ≤ (Opens.map g.base).obj U) :
    Scheme.Hom.appLE f U V e = Scheme.Hom.appLE g U V e' := by
  subst hfg
  rfl


end

theorem sectionsRingHom_sub_mem_ideal {A : Type u} [CommRing A] {W : Scheme.{u}}
    (ρ ρ' : W ⟶ Spec (CommRingCat.of A)) (𝔞 : W.IdealSheafData)
    (hagree : 𝔞.subschemeι ≫ ρ = 𝔞.subschemeι ≫ ρ')
    (V : W.affineOpens) (r : A) :
    Blowup.sectionsRingHom ρ (V : W.Opens) r - Blowup.sectionsRingHom ρ' (V : W.Opens) r ∈ 𝔞.ideal V := by
  apply mem_ideal_of_app_subschemeι_eq_zero_consolidated166
  have h1 : Blowup.sectionsRingHom (𝔞.subschemeι ≫ ρ)
        ((Opens.map 𝔞.subschemeι.base).obj (V : W.Opens)) r
      = Blowup.sectionsRingHom (𝔞.subschemeι ≫ ρ')
        ((Opens.map 𝔞.subschemeι.base).obj (V : W.Opens)) r := by
    rw [hagree]
  rw [sectionsRingHom_comp_consolidated166 𝔞.subschemeι ρ (V : W.Opens) _ le_rfl r,
    sectionsRingHom_comp_consolidated166 𝔞.subschemeι ρ' (V : W.Opens) _ le_rfl r] at h1
  rw [Scheme.Hom.app_eq_appLE, map_sub, h1]
  exact sub_self _

section
variable (I : Ideal R) {W : Scheme.{u}}

private theorem appTop_lift_affineBlowupChart_apply_consolidated166 (k : W ⟶ Blowup.affineBlowup I) (a : I)
    {T : Scheme.{u}} (p : T ⟶ W) (V : W.Opens)
    (hk : V ≤ (Opens.map k.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤))
    (hψ : (⊤ : T.Opens) ≤ (Opens.map p.base).obj V)
    (hrange : Set.range ⇑(p ≫ k).base ⊆ Set.range ⇑(Blowup.affineBlowupChart I a).base)
    (z : HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) :
    (CommRingCat.Hom.hom (Scheme.Hom.appTop
        (IsOpenImmersion.lift (Blowup.affineBlowupChart I a) (p ≫ k) hrange)))
      ((CommRingCat.Hom.hom (Scheme.ΓSpecIso
        (CommRingCat.of (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).inv) z)
      = (CommRingCat.Hom.hom (Scheme.Hom.appLE p V ⊤ hψ))
          (Blowup.chartSectionsRingHom I k a V hk z) := by
  have hchartle : (⊤ : (Spec (CommRingCat.of
        (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).Opens)
      ≤ (Opens.map (Blowup.affineBlowupChart I a).base).obj
        ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) :=
    fun x _ => ⟨x, trivial, rfl⟩
  have hsec : (CommRingCat.Hom.hom (Scheme.Hom.appLE (Blowup.affineBlowupChart I a)
        ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) ⊤ hchartle))
        ((CommRingCat.Hom.hom (Blowup.chartSectionsIso I a).hom) z)
      = (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
          (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).inv) z := by
    rw [Blowup.chartSectionsIso_hom_apply, ← CommRingCat.comp_apply,
      show Scheme.Hom.appLE (Blowup.affineBlowupChart I a)
          ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) ⊤ hchartle
        = (Scheme.Hom.appIso (Blowup.affineBlowupChart I a) ⊤).hom from
          (Scheme.Hom.appIso_hom' (Blowup.affineBlowupChart I a) ⊤).symm,
      Iso.inv_hom_id, CommRingCat.id_apply]
  have hlift := IsOpenImmersion.lift_fac (Blowup.affineBlowupChart I a) (p ≫ k) hrange
  have etop : (⊤ : T.Opens)
      ≤ (Opens.map (IsOpenImmersion.lift (Blowup.affineBlowupChart I a) (p ≫ k) hrange).base).obj ⊤ := by
    simp
  have hmain : Scheme.Hom.appLE (Blowup.affineBlowupChart I a)
        ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) ⊤ hchartle
        ≫ Scheme.Hom.appLE (IsOpenImmersion.lift (Blowup.affineBlowupChart I a) (p ≫ k) hrange) ⊤ ⊤ etop
      = Scheme.Hom.appLE k ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) V hk
        ≫ Scheme.Hom.appLE p V ⊤ hψ := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr_hom_consolidated166 hlift _ _ _ _
  rw [appLE_top_top_consolidated166 _ etop] at hmain
  have happ := congrArg (fun m : _ ⟶ _ =>
      (CommRingCat.Hom.hom m) ((CommRingCat.Hom.hom (Blowup.chartSectionsIso I a).hom) z)) hmain
  simp only [CommRingCat.comp_apply] at happ
  rw [hsec, ← Blowup.chartSectionsRingHom_apply] at happ
  exact happ

theorem comp_eq_of_chartSectionsRingHom_sub_mem (h h' : W ⟶ Blowup.affineBlowup I) (a : I) (𝔟 : W.IdealSheafData) (V : W.affineOpens)
    (hV : (V : W.Opens) ≤ (Opens.map h.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤))
    (hV' : (V : W.Opens) ≤ (Opens.map h'.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤))
    (hcongr : ∀ z : HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a),
      Blowup.chartSectionsRingHom I h a (V : W.Opens) hV z - Blowup.chartSectionsRingHom I h' a (V : W.Opens) hV' z
        ∈ 𝔟.ideal V) :
    Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟.subschemeι ≫ h
      = Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟.subschemeι ≫ h' := by
  rw [← Category.assoc, ← Category.assoc]
  have hψ : (⊤ : (Scheme.Opens.toScheme
        ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))).Opens)
      ≤ (Opens.map (Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))
            ≫ 𝔟.subschemeι).base).obj (V : W.Opens) := by
    intro x _
    simp
  have hι : (⊤ : (Scheme.Opens.toScheme
        ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))).Opens)
      ≤ (Opens.map (Scheme.Opens.ι
          ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))).base).obj
        ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) := by
    intro x _
    simp
  have hrange : ∀ (k : W ⟶ Blowup.affineBlowup I),
      (V : W.Opens) ≤ (Opens.map k.base).obj
        ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) →
      Set.range ⇑((Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))
          ≫ 𝔟.subschemeι) ≫ k).base ⊆ Set.range ⇑(Blowup.affineBlowupChart I a).base := by
    intro k hk
    rintro y ⟨x, rfl⟩
    have h3 : k.base (𝔟.subschemeι.base x.1)
        ∈ Scheme.Hom.opensRange (Blowup.affineBlowupChart I a) := by
      rw [← Scheme.Hom.image_top_eq_opensRange]
      exact hk x.2
    obtain ⟨q, hq⟩ := h3
    exact ⟨q, hq⟩
  have hkill : ∀ x ∈ 𝔟.ideal V,
      (CommRingCat.Hom.hom (Scheme.Hom.appLE
        (Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟.subschemeι)
        (V : W.Opens) ⊤ hψ)) x = 0 := by
    intro x hx
    have hcomp : Scheme.Hom.appLE 𝔟.subschemeι (V : W.Opens)
          ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) le_rfl
        ≫ Scheme.Hom.appLE (Scheme.Opens.ι
            ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)))
            ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) ⊤ hι
        = Scheme.Hom.appLE (Scheme.Opens.ι
            ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟.subschemeι)
            (V : W.Opens) ⊤ hψ := by
      rw [Scheme.Hom.appLE_comp_appLE]
    have h2 := congrArg (fun m : _ ⟶ _ => (CommRingCat.Hom.hom m) x) hcomp
    simp only [CommRingCat.comp_apply] at h2
    rw [Scheme.Hom.appLE_eq_app, app_subschemeι_eq_zero_of_mem_ideal_consolidated166 𝔟 V hx, map_zero] at h2
    exact h2.symm
  have happ : Scheme.Hom.appTop (IsOpenImmersion.lift (Blowup.affineBlowupChart I a) _ (hrange h hV))
      = Scheme.Hom.appTop (IsOpenImmersion.lift (Blowup.affineBlowupChart I a) _ (hrange h' hV')) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro y
    have hy : (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
          (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).inv)
        ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
          (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).hom) y) = y := by
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
    obtain ⟨z, rfl⟩ : ∃ z, (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
        (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).inv) z = y :=
      ⟨_, hy⟩
    rw [appTop_lift_affineBlowupChart_apply_consolidated166 I h a (Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))
        ≫ 𝔟.subschemeι) (V : W.Opens) hV hψ (hrange h hV) z,
      appTop_lift_affineBlowupChart_apply_consolidated166 I h' a (Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))
        ≫ 𝔟.subschemeι) (V : W.Opens) hV' hψ (hrange h' hV') z]
    have hz := hkill _ (hcongr z)
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz
  have hfin : IsOpenImmersion.lift (Blowup.affineBlowupChart I a) _ (hrange h hV)
      = IsOpenImmersion.lift (Blowup.affineBlowupChart I a) _ (hrange h' hV') := by
    have hcomp : IsOpenImmersion.lift (Blowup.affineBlowupChart I a) _ (hrange h hV)
          ≫ (Spec (CommRingCat.of
              (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).toSpecΓ
        = IsOpenImmersion.lift (Blowup.affineBlowupChart I a) _ (hrange h' hV')
          ≫ (Spec (CommRingCat.of
              (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).toSpecΓ := by
      rw [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, happ]
    exact (cancel_mono _).mp hcomp
  rw [← IsOpenImmersion.lift_fac (Blowup.affineBlowupChart I a) _ (hrange h hV),
    ← IsOpenImmersion.lift_fac (Blowup.affineBlowupChart I a) _ (hrange h' hV'), hfin]

private theorem sectionsRingHom_sub_mem_span_mul_of_agree_consolidated166 (ρ ρ' : W ⟶ Spec (CommRingCat.of R)) (𝔞 𝔟₁ : W.IdealSheafData) (V : W.affineOpens)
    (hagree : 𝔞.subschemeι ≫ ρ = 𝔞.subschemeι ≫ ρ')
    (hfac : (Blowup.specIdealSheaf I).comap ρ * 𝔟₁ = 𝔞)
    (s : ↥(W.presheaf.obj (Opposite.op (V : W.Opens))))
    (hspan : ((Blowup.specIdealSheaf I).comap ρ).ideal V = Ideal.span {s})
    (r : R) :
    Blowup.sectionsRingHom ρ (V : W.Opens) r - Blowup.sectionsRingHom ρ' (V : W.Opens) r
      ∈ Ideal.span {s} * 𝔟₁.ideal V := by
  have h1 := sectionsRingHom_sub_mem_ideal ρ ρ' 𝔞 hagree V r
  rw [← hfac] at h1
  rw [← hspan]
  exact h1

private theorem chartSectionsRingHom_sub_mem_consolidated166 (h h' : W ⟶ Blowup.affineBlowup I) (𝔟₁ : W.IdealSheafData) (a : I) (V : W.affineOpens)
    (hV : (V : W.Opens) ≤ (Opens.map h.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤))
    (hV' : (V : W.Opens) ≤ (Opens.map h'.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤))
    (hnzd : Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)
      ∈ nonZeroDivisors ↥(W.presheaf.obj (Opposite.op (V : W.Opens))))
    (u : ↥(W.presheaf.obj (Opposite.op (V : W.Opens))))
    (hu : Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)
      = u * Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R))
    (hcongr : ∀ r : R, Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) r
        - Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) r
      ∈ Ideal.span {Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)}
          * 𝔟₁.ideal V)
    (z : HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) :
    Blowup.chartSectionsRingHom I h a (V : W.Opens) hV z - Blowup.chartSectionsRingHom I h' a (V : W.Opens) hV' z
      ∈ 𝔟₁.ideal V := by
  refine sub_mem_ideal_of_subring_closure_eq_top (Blowup.chartSectionsRingHom I h a (V : W.Opens) hV)
    (Blowup.chartSectionsRingHom I h' a (V : W.Opens) hV') (𝔟₁.ideal V)
    (Set.range ⇑(Blowup.chartRingHom I a) ∪ Set.range (Blowup.chartFraction I a))
    (closure_chartRingHom_union_chartFraction_eq_top I a) ?_ z
  rintro b (⟨r, rfl⟩ | ⟨b0, rfl⟩)
  · rw [Blowup.chartSectionsRingHom_chartRingHom, Blowup.chartSectionsRingHom_chartRingHom]
    exact (Ideal.mem_inf.mp (Ideal.mul_le_inf (hcongr r))).2
  · exact chartFraction_sub_mem_of_congr I a (Blowup.chartSectionsRingHom I h a (V : W.Opens) hV)
      (Blowup.chartSectionsRingHom I h' a (V : W.Opens) hV')
      (Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens))
      (Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens)) (𝔟₁.ideal V)
      (Blowup.chartSectionsRingHom_chartRingHom I h a (V : W.Opens) hV)
      (Blowup.chartSectionsRingHom_chartRingHom I h' a (V : W.Opens) hV')
      hcongr hnzd u hu b0

theorem comp_eq_on_chart_of_mul_eq_of_agree (h h' : W ⟶ Blowup.affineBlowup I) (𝔞 𝔟₁ : W.IdealSheafData) (a : I) (V : W.affineOpens)
    (hagree : 𝔞.subschemeι ≫ (h ≫ Blowup.AffineBlowup.toSpec I)
      = 𝔞.subschemeι ≫ (h' ≫ Blowup.AffineBlowup.toSpec I))
    (hpull : (Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)
      = (Blowup.specIdealSheaf I).comap (h' ≫ Blowup.AffineBlowup.toSpec I))
    (hfac : (Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I) * 𝔟₁ = 𝔞)
    (hV : (V : W.Opens) ≤ (Opens.map h.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤))
    (hV' : (V : W.Opens) ≤ (Opens.map h'.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤))
    (hnzd : Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)
      ∈ nonZeroDivisors ↥(W.presheaf.obj (Opposite.op (V : W.Opens))))
    (hspan : ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)).ideal V
      = Ideal.span {Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)}) :
    Scheme.Opens.ι ((Opens.map 𝔟₁.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟₁.subschemeι ≫ h
      = Scheme.Opens.ι ((Opens.map 𝔟₁.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟₁.subschemeι ≫ h' := by
  have hmem : Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)
      ∈ Ideal.span {Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)} := by
    rw [← hspan, hpull, Blowup.comap_specIdealSheaf_ideal_eq_span I h' a V hV']
    exact Ideal.mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hmem
  refine comp_eq_of_chartSectionsRingHom_sub_mem I h h' a 𝔟₁ V hV hV' (fun z => ?_)
  refine chartSectionsRingHom_sub_mem_consolidated166 I h h' 𝔟₁ a V hV hV' hnzd u hu.symm (fun r => ?_) z
  exact sectionsRingHom_sub_mem_span_mul_of_agree_consolidated166 I (h ≫ Blowup.AffineBlowup.toSpec I) (h' ≫ Blowup.AffineBlowup.toSpec I) 𝔞 𝔟₁ V
    hagree hfac (Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)) hspan r

theorem exists_common_chart_affineOpen (h h' : W ⟶ Blowup.affineBlowup I) (𝔞 𝔟₁ : W.IdealSheafData)
    (hagree : 𝔞.subschemeι ≫ (h ≫ Blowup.AffineBlowup.toSpec I)
      = 𝔞.subschemeι ≫ (h' ≫ Blowup.AffineBlowup.toSpec I))
    (hpull : (Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)
      = (Blowup.specIdealSheaf I).comap (h' ≫ Blowup.AffineBlowup.toSpec I))
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)))
    (hfac : (Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I) * 𝔟₁ = 𝔞)
    (w : ↥W) :
    ∃ (a : I) (V V' : W.affineOpens),
      w ∈ (V : W.Opens) ∧
      (Opens.map 𝔟₁.subschemeι.base).obj (V' : W.Opens)
        = (Opens.map 𝔟₁.subschemeι.base).obj (V : W.Opens) ∧
      (V' : W.Opens) ≤ (Opens.map h.base).obj
        ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) ∧
      (V' : W.Opens) ≤ (Opens.map h'.base).obj
        ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) ∧
      Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V' : W.Opens) (a : R)
        ∈ nonZeroDivisors ↥(W.presheaf.obj (Opposite.op (V' : W.Opens))) ∧
      ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)).ideal V'
        = Ideal.span {Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V' : W.Opens) (a : R)} := by
  obtain ⟨a, V, hwV, hVchart, hnzdV⟩ := Blowup.exists_chart_affineOpen_mem_nonZeroDivisors I h hcart w
  have hspanV : ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)).ideal V
      = Ideal.span {Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)} :=
    Blowup.comap_specIdealSheaf_ideal_eq_span I h a V hVchart
  have hsub := sectionsRingHom_sub_mem_ideal (h ≫ Blowup.AffineBlowup.toSpec I)
    (h' ≫ Blowup.AffineBlowup.toSpec I) 𝔞 hagree V (a : R)
  have hmul : ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I) * 𝔟₁).ideal V
      = ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)).ideal V * 𝔟₁.ideal V := rfl
  rw [← hfac, hmul, hspanV] at hsub
  obtain ⟨c, hc, hceq⟩ := Ideal.mem_span_singleton_mul.mp hsub
  set f : ↥(W.presheaf.obj (Opposite.op (V : W.Opens))) := 1 - c with hfdef
  have hf'' : Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)
      = Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R) * f := by
    rw [hfdef]
    linear_combination hceq
  have hle : W.basicOpen f ≤ (V : W.Opens) := W.basicOpen_le f
  have haff : IsAffineOpen (W.basicOpen f) := V.2.basicOpen f
  have hlechart : W.basicOpen f ≤ (Opens.map h.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) := le_trans hle hVchart
  have hsp : ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)).ideal
        ⟨W.basicOpen f, haff⟩
      = Ideal.span {Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (W.basicOpen f) (a : R)} :=
    Blowup.comap_specIdealSheaf_ideal_eq_span I h a ⟨W.basicOpen f, haff⟩ hlechart
  have hresσ : Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (W.basicOpen f) (a : R)
      = (CommRingCat.Hom.hom (W.presheaf.map (homOfLE hle).op))
          (Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)) :=
    Blowup.sectionsRingHom_restrict (h ≫ Blowup.AffineBlowup.toSpec I) hle (a : R)
  have hresσ' : Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (W.basicOpen f) (a : R)
      = (CommRingCat.Hom.hom (W.presheaf.map (homOfLE hle).op))
          (Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)) :=
    Blowup.sectionsRingHom_restrict (h' ≫ Blowup.AffineBlowup.toSpec I) hle (a : R)
  have hloc : IsLocalization.Away f ↥(W.presheaf.obj (Opposite.op (W.basicOpen f))) :=
    V.2.isLocalization_basicOpen f
  have hunit : IsUnit ((CommRingCat.Hom.hom (W.presheaf.map (homOfLE hle).op)) f) :=
    IsLocalization.map_units
      (S := ↥(W.presheaf.obj (Opposite.op (W.basicOpen f))))
      (M := Submonoid.powers f) ⟨f, Submonoid.mem_powers f⟩
  have hnzdres : algebraMap ↥(W.presheaf.obj (Opposite.op (V : W.Opens)))
        ↥(W.presheaf.obj (Opposite.op (W.basicOpen f)))
        (Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R))
      ∈ nonZeroDivisors ↥(W.presheaf.obj (Opposite.op (W.basicOpen f))) := by
    have hcomap := IsLocalization.nonZeroDivisors_le_comap (M := Submonoid.powers f)
      (S := ↥(W.presheaf.obj (Opposite.op (W.basicOpen f))))
    exact hcomap hnzdV
  have hnzdfinal : Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (W.basicOpen f) (a : R)
      ∈ nonZeroDivisors ↥(W.presheaf.obj (Opposite.op (W.basicOpen f))) := by
    rw [hresσ]
    exact hnzdres
  have hcart' : Blowup.IsLocallyGeneratedByNonZeroDivisor
      ((Blowup.specIdealSheaf I).comap (h' ≫ Blowup.AffineBlowup.toSpec I)) := by
    rw [← hpull]
    exact hcart
  have hspanbo' : ((Blowup.specIdealSheaf I).comap (h' ≫ Blowup.AffineBlowup.toSpec I)).ideal
        ⟨W.basicOpen f, haff⟩
      = Ideal.span {Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (W.basicOpen f) (a : R)} := by
    rw [← hpull, hsp, hresσ, hresσ', hf'', map_mul]
    exact (Ideal.span_singleton_mul_right_unit hunit _).symm
  have hpre : (Opens.map 𝔟₁.subschemeι.base).obj (W.basicOpen f)
      = (Opens.map 𝔟₁.subschemeι.base).obj (V : W.Opens) := by
    rw [Scheme.preimage_basicOpen]
    have happ : (CategoryTheory.ConcreteCategory.hom
        (Scheme.Hom.app 𝔟₁.subschemeι (V : W.Opens))) f = 1 := by
      show (CommRingCat.Hom.hom (Scheme.Hom.app 𝔟₁.subschemeι (V : W.Opens))) f = 1
      rw [hfdef, map_sub, map_one, app_subschemeι_eq_zero_of_mem_ideal_consolidated166 𝔟₁ V hc, sub_zero]
    rw [happ, Scheme.basicOpen_one]
  refine ⟨a, V, ⟨W.basicOpen f, haff⟩, hwV, hpre, hlechart, ?_, hnzdfinal, hsp⟩
  intro x hx
  have hmemrange := Blowup.mem_opensRange_affineBlowupChart_of_ideal_eq_span I h' hcart' x a
    ⟨⟨W.basicOpen f, haff⟩, hx, hspanbo'⟩
  rw [← Scheme.Hom.image_top_eq_opensRange] at hmemrange
  exact hmemrange

theorem subschemeι_comp_eq_of_affineBlowup_lifts (ρ ρ' : W ⟶ Spec (CommRingCat.of R)) (𝔞 𝔟₁ : W.IdealSheafData)
    (h h' : W ⟶ Blowup.affineBlowup I)
    (hagree : 𝔞.subschemeι ≫ ρ = 𝔞.subschemeι ≫ ρ')
    (hpull : (Blowup.specIdealSheaf I).comap ρ = (Blowup.specIdealSheaf I).comap ρ')
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor ((Blowup.specIdealSheaf I).comap ρ))
    (hfac : (Blowup.specIdealSheaf I).comap ρ * 𝔟₁ = 𝔞)
    (hh : h ≫ Blowup.AffineBlowup.toSpec I = ρ)
    (hh' : h' ≫ Blowup.AffineBlowup.toSpec I = ρ') :
    𝔟₁.subschemeι ≫ h = 𝔟₁.subschemeι ≫ h' := by
  subst hh
  subst hh'
  choose a V V' hw hpre hVh hVh' hn hs using
    exists_common_chart_affineOpen I h h' 𝔞 𝔟₁ hagree hpull hcart hfac
  have hcov : ∀ z : ↥(𝔟₁.subscheme), ∃ (w : ↥W)
      (y : ↥((Opens.map 𝔟₁.subschemeι.base).obj ((V w : W.Opens)))),
      (Scheme.Opens.ι ((Opens.map 𝔟₁.subschemeι.base).obj ((V w : W.Opens)))).base y = z := by
    intro z
    exact ⟨𝔟₁.subschemeι.base z, ⟨z, hw (𝔟₁.subschemeι.base z)⟩, rfl⟩
  refine Scheme.Cover.hom_ext
    (Scheme.Cover.mkOfCovers (↥W)
      (fun w => Scheme.Opens.toScheme
        ((Opens.map 𝔟₁.subschemeι.base).obj ((V w : W.Opens))))
      (fun w => Scheme.Opens.ι
        ((Opens.map 𝔟₁.subschemeι.base).obj ((V w : W.Opens)))) hcov) _ _ ?_
  intro w
  show Scheme.Opens.ι ((Opens.map 𝔟₁.subschemeι.base).obj ((V w : W.Opens)))
        ≫ (𝔟₁.subschemeι ≫ h)
      = Scheme.Opens.ι ((Opens.map 𝔟₁.subschemeι.base).obj ((V w : W.Opens)))
        ≫ (𝔟₁.subschemeι ≫ h')
  rw [← hpre w]
  exact comp_eq_on_chart_of_mul_eq_of_agree I h h' 𝔞 𝔟₁ (a w) (V' w) hagree hpull hfac
    (hVh w) (hVh' w) (hn w) (hs w)


end

end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderUnderStalkIsomorphism
section

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

section
variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] (f : R →+* S) (g : S →+* R) (hgf : g.comp f = RingHom.id R)
include hgf

theorem map_maximalIdeal_le_maximalIdeal_of_retraction :
    Ideal.map f (IsLocalRing.maximalIdeal R) ≤ IsLocalRing.maximalIdeal S := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply hx
  have h3 : g (f x) = x := by
    rw [← RingHom.comp_apply, hgf, RingHom.id_apply]
  have h2 := hu.map g
  rwa [h3] at h2

theorem idealOrder_map_eq_of_comp_eq_id (hfg : f.comp g = RingHom.id S) (I : Ideal R) :
    idealOrder (Ideal.map f I) = idealOrder I := by
  have hf := map_maximalIdeal_le_maximalIdeal_of_retraction f g hgf
  have hg := map_maximalIdeal_le_maximalIdeal_of_retraction g f hfg
  have h1 := idealOrder_le_idealOrder_map f hf I
  have h3 := idealOrder_le_idealOrder_map g hg (Ideal.map f I)
  rw [Ideal.map_map, hgf, Ideal.map_id] at h3
  exact le_antisymm h3 h1


end

theorem orderAt_comap_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (J : Y.IdealSheafData)
    (x : X) [IsIso (f.stalkMap x)] :
    orderAt (J.comap f) x = orderAt J (f.base x) := by
  have hgf : ((inv (f.stalkMap x)).hom).comp ((f.stalkMap x).hom) = RingHom.id _ := by
    have h := congrArg CommRingCat.Hom.hom (IsIso.hom_inv_id (f.stalkMap x))
    rwa [CommRingCat.hom_comp, CommRingCat.hom_id] at h
  have hfg : ((f.stalkMap x).hom).comp ((inv (f.stalkMap x)).hom) = RingHom.id _ := by
    have h := congrArg CommRingCat.Hom.hom (IsIso.inv_hom_id (f.stalkMap x))
    rwa [CommRingCat.hom_comp, CommRingCat.hom_id] at h
  simp only [orderAt_eq_idealOrder]
  rw [stalkIdeal_comap]
  exact idealOrder_map_eq_of_comp_eq_id _ _ hgf hfg _

theorem isIso_stalkMap_of_isBlowupAlongIdealSheaf {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData)
    (h : Blowup.IsBlowupAlongIdealSheaf π Z) (x : X₁) (hx : π.base x ∉ Z.support) :
    IsIso (π.stalkMap x) := by
  have h1 := h.restrict Z.support.compl
  rw [Blowup.comap_ι_support_compl_eq_top Z] at h1
  have hiso : IsIso (π ∣_ Z.support.compl) := h1.isIso_of_top
  have hoi : IsOpenImmersion (π ∣_ Z.support.compl) := IsOpenImmersion.of_isIso _
  have hxV : x ∈ π ⁻¹ᵁ Z.support.compl := hx
  let y : ↥((π ⁻¹ᵁ Z.support.compl).toScheme) := ⟨x, hxV⟩
  have hs2 : IsIso ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).stalkMap y) := inferInstance
  have hoi2 : IsOpenImmersion
      ((π ∣_ Z.support.compl) ≫ Scheme.Opens.ι Z.support.compl) := inferInstance
  have hB : IsIso (((π ∣_ Z.support.compl) ≫ Scheme.Opens.ι Z.support.compl).stalkMap y) :=
    inferInstance
  have hcomp : Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl) ≫ π
      = (π ∣_ Z.support.compl) ≫ Scheme.Opens.ι Z.support.compl :=
    (morphismRestrict_ι π Z.support.compl).symm
  have hA : IsIso ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl) ≫ π).stalkMap y) := by
    rw [hcomp]
    exact hB
  have e2 : (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl) ≫ π).stalkMap y
      = π.stalkMap ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).base y)
        ≫ (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).stalkMap y := Scheme.Hom.stalkMap_comp _ _ _
  have hC : IsIso (π.stalkMap ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).base y)
      ≫ (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).stalkMap y) := by
    rw [e2] at hA
    exact hA
  have hr : π.stalkMap ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).base y)
      = (π.stalkMap ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).base y)
          ≫ (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).stalkMap y)
        ≫ inv ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).stalkMap y) := by
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hfin : IsIso (π.stalkMap ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).base y)) := by
    rw [hr]
    infer_instance
  exact hfin

namespace OrderLocusBlowup

theorem orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (A : X.IdealSheafData) (A₁ : X₁.IdealSheafData)
    (μ : ℕ) (hA : Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π)
    (hZ : (Z.support : Set ↥X) ⊆ orderAtLeastLocus A μ) :
    orderAtLeastLocus A₁ μ ⊆ (⇑π.base) ⁻¹' orderAtLeastLocus A μ := by
  intro x hx
  by_cases hxZ : π.base x ∈ Z.support
  · exact hZ hxZ
  · have := isIso_stalkMap_of_isBlowupAlongIdealSheaf π Z hπ x hxZ
    have hle : stalkIdeal (A.comap π) x ≤ stalkIdeal A₁ x := by
      rw [← hA, stalkIdeal_mul]
      exact le_trans Ideal.mul_le_inf inf_le_right
    have h2 : orderAt A₁ x ≤ orderAt (A.comap π) x := idealOrder_le_of_le hle
    have h3 : orderAt (A.comap π) x = orderAt A (π.base x) :=
      orderAt_comap_of_isIso_stalkMap π A x
    show (μ : ℕ∞) ≤ orderAt A (π.base x)
    calc (μ : ℕ∞) ≤ orderAt A₁ x := hx
      _ ≤ orderAt (A.comap π) x := h2
      _ = orderAt A (π.base x) := h3

end OrderLocusBlowup

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.StrictNormalCrossingsMoveToFront
section

open CategoryTheory AlgebraicGeometry

section
namespace FunctorialResolution.EmbeddedResolution

variable {α : Type*}

def moveToFront (E : List α) (j : ℕ) : List α :=
  match E[j]? with
  | some a => a :: E.eraseIdx j
  | none => E

section
variable (E : List α) (j : ℕ) (hj : j < E.length)
include hj

theorem moveToFront_eq_cons :
    moveToFront E j = (E[j]'hj) :: E.eraseIdx j := by
  simp [moveToFront, List.getElem?_eq_getElem hj]

theorem length_moveToFront :
    (moveToFront E j).length = E.length := by
  rw [moveToFront_eq_cons E j hj, List.length_cons,
    List.length_eraseIdx_add_one hj]


end

def indexBeforeMoveToFront (j : ℕ) : ℕ → ℕ
  | 0 => j
  | (i + 1) => if i < j then i else i + 1

theorem indexBeforeMoveToFront_zero (j : ℕ) : indexBeforeMoveToFront j 0 = j := rfl

theorem indexBeforeMoveToFront_succ (j i : ℕ) : indexBeforeMoveToFront j (i + 1) = if i < j then i else i + 1 := rfl

theorem indexBeforeMoveToFront_injective (j : ℕ) : Function.Injective (indexBeforeMoveToFront j) := by
  intro a b hab
  cases a with
  | zero =>
    cases b with
    | zero => rfl
    | succ i =>
      exfalso
      simp only [indexBeforeMoveToFront] at hab
      split_ifs at hab <;> omega
  | succ i =>
    cases b with
    | zero =>
      exfalso
      simp only [indexBeforeMoveToFront] at hab
      split_ifs at hab <;> omega
    | succ i' =>
      simp only [indexBeforeMoveToFront] at hab
      split_ifs at hab <;> omega

section
variable (E : List α) (j : ℕ) (hj : j < E.length) (i : ℕ)
include hj

theorem indexBeforeMoveToFront_lt_length (hi : i < E.length) : indexBeforeMoveToFront j i < E.length := by
  cases i with
  | zero => exact hj
  | succ n =>
    show (if n < j then n else n + 1) < E.length
    split <;> omega

theorem getElem_moveToFront (hi : i < (moveToFront E j).length) :
    (moveToFront E j)[i]'hi =
      E[indexBeforeMoveToFront j i]'(indexBeforeMoveToFront_lt_length E j hj i (by
        rw [length_moveToFront E j hj] at hi; exact hi)) := by
  have hi' : i < E.length := by rw [length_moveToFront E j hj] at hi; exact hi
  have hlt : indexBeforeMoveToFront j i < E.length := indexBeforeMoveToFront_lt_length E j hj i hi'
  have key : (moveToFront E j)[i]? = E[indexBeforeMoveToFront j i]? := by
    rw [moveToFront_eq_cons E j hj]
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero, indexBeforeMoveToFront_zero, List.getElem?_eq_getElem hj]
    | succ m =>
      rw [List.getElem?_cons_succ, indexBeforeMoveToFront_succ]
      by_cases hm : m < j
      · rw [if_pos hm]
        simp [List.getElem?_eraseIdx_of_lt, hm]
      · rw [if_neg hm]
        have hm' : j ≤ m := by omega
        simp [List.getElem?_eraseIdx_of_ge, hm']
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hlt] at key
  exact Option.some.inj key


end

def indexInMoveToFront (j : ℕ) (i : ℕ) : ℕ := if i = j then 0 else if i < j then i + 1 else i

section
variable (j : ℕ)

theorem indexInMoveToFront_self : indexInMoveToFront j j = 0 := by
  simp [indexInMoveToFront]

theorem indexInMoveToFront_injective : Function.Injective (indexInMoveToFront j) := by
  intro a b hab
  simp only [indexInMoveToFront] at hab
  split_ifs at hab <;> omega


end

section
variable (E : List α) (j : ℕ) (hj : j < E.length)
include hj

theorem indexInMoveToFront_lt_length (i : ℕ) (hi : i < E.length) :
    indexInMoveToFront j i < (moveToFront E j).length := by
  rw [length_moveToFront E j hj]
  show (if i = j then 0 else if i < j then i + 1 else i) < E.length
  split_ifs <;> omega

theorem getElem_eq_getElem_moveToFront (i : ℕ)
    (hi : i < E.length) :
    E[i]'hi = (moveToFront E j)[indexInMoveToFront j i]'(indexInMoveToFront_lt_length E j hj i hi) := by
  rcases lt_trichotomy i j with h | h | h
  · have hb : indexInMoveToFront j i = i + 1 := by
      simp only [indexInMoveToFront]
      split_ifs <;> omega
    simp [moveToFront_eq_cons E j hj, hb, List.getElem_eraseIdx_of_lt, h]
  · subst h
    simp only [moveToFront_eq_cons E _ hj, indexInMoveToFront_self, List.getElem_cons_zero]
  · have hb : indexInMoveToFront j i = i := by
      simp only [indexInMoveToFront]
      split_ifs <;> omega
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hjk : j ≤ k := by omega
    simp [moveToFront_eq_cons E j hj, hb, List.getElem_eraseIdx_of_ge, hjk]

theorem mem_of_mem_moveToFront (D : α)
    (hD : D ∈ moveToFront E j) : D ∈ E := by
  rw [moveToFront_eq_cons E j hj] at hD
  rcases List.mem_cons.mp hD with h1 | h2
  · subst h1
    simp
  · exact List.mem_of_mem_eraseIdx h2


end

section
variable {X : Scheme.{u}} {k : Type u} [Field k]

theorem chartAssignment_comp_of_injective {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
    (E E' : List X.IdealSheafData) (σ : ℕ → ℕ)
    (hinj : Function.Injective σ)
    (hlt : ∀ i, i < E'.length → σ i < E.length)
    (hEq : ∀ i, ∀ h : i < E'.length, (E'[i]'h) = E[σ i]'(hlt i h))
    (hainj : ∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j)
    (hnone : ∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤)
    (hsome : ∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
      restrictIdeal (E[i]'h) U = c.coordIdeal {t}) :
    (∀ i < E'.length, ∀ j < E'.length, ∀ t : Fin m,
        (a ∘ σ) i = some t → (a ∘ σ) j = some t → i = j) ∧
      (∀ i, ∀ h : i < E'.length, (a ∘ σ) i = none → restrictIdeal (E'[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < E'.length, ∀ t : Fin m, (a ∘ σ) i = some t →
        restrictIdeal (E'[i]'h) U = c.coordIdeal {t}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj t hit hjt
    simp only [Function.comp_apply] at hit hjt
    exact hinj (hainj (σ i) (hlt i hi) (σ j) (hlt j hj) t hit hjt)
  · intro i h hn
    simp only [Function.comp_apply] at hn
    rw [hEq i h]
    exact hnone (σ i) (hlt i h) hn
  · intro i h t ht
    simp only [Function.comp_apply] at ht
    rw [hEq i h]
    exact hsome (σ i) (hlt i h) t ht

theorem inStrictNormalCrossingPosition_moveToFront (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (j : ℕ)
    (hj : j < E.length) (hE : InStrictNormalCrossingPosition p E) :
    InStrictNormalCrossingPosition p (moveToFront E j) := by
  refine ⟨?_, ?_⟩
  · intro D hD
    exact hE.1 D (mem_of_mem_moveToFront E j hj D hD)
  · intro x
    obtain ⟨U, hxU, m, c, a, h1, h2, h3⟩ := hE.2 x
    have hlen : (moveToFront E j).length = E.length := length_moveToFront E j hj
    have hlt : ∀ i, i < (moveToFront E j).length → indexBeforeMoveToFront j i < E.length := by
      intro i hi
      refine indexBeforeMoveToFront_lt_length E j hj i ?_
      rw [hlen] at hi
      exact hi
    have hEq : ∀ i, ∀ h : i < (moveToFront E j).length,
        ((moveToFront E j)[i]'h) = E[indexBeforeMoveToFront j i]'(hlt i h) :=
      fun i h => getElem_moveToFront E j hj i h
    obtain ⟨k1, k2, k3⟩ := chartAssignment_comp_of_injective c a E (moveToFront E j) (indexBeforeMoveToFront j)
      (indexBeforeMoveToFront_injective j) hlt hEq h1 h2 h3
    exact ⟨U, hxU, m, c, a ∘ indexBeforeMoveToFront j, k1, k2, k3⟩

theorem hasStrictNormalCrossingsWith_of_moveToFront (p : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData)
    (E : List X.IdealSheafData) (j : ℕ) (hj : j < E.length)
    (hZ : HasStrictNormalCrossingsWith p Z (moveToFront E j)) :
    HasStrictNormalCrossingsWith p Z E := by
  intro x hx
  obtain ⟨U, hxU, m, c, a, S, h1, h2, h3, h4⟩ := hZ x hx
  have hlt : ∀ i, i < E.length → indexInMoveToFront j i < (moveToFront E j).length :=
    fun i hi => indexInMoveToFront_lt_length E j hj i hi
  have hEq : ∀ i, ∀ h : i < E.length,
      (E[i]'h) = (moveToFront E j)[indexInMoveToFront j i]'(hlt i h) :=
    fun i h => getElem_eq_getElem_moveToFront E j hj i h
  obtain ⟨k1, k2, k3⟩ := chartAssignment_comp_of_injective c a (moveToFront E j) E (indexInMoveToFront j)
    (indexInMoveToFront_injective j) hlt hEq h1 h2 h3
  exact ⟨U, hxU, m, c, a ∘ indexInMoveToFront j, S, k1, k2, k3, h4⟩


end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphAlgebra
section

namespace FunctorialResolution.EmbeddedResolution

variable {R : Type u} [CommRing R] {σ τ : Type u}

section
def GraphAlgebra (_f : τ → MvPolynomial σ R) : Type u := MvPolynomial σ R

instance instCommRingGraphAlgebra (f : τ → MvPolynomial σ R) : CommRing (GraphAlgebra f) :=
  inferInstanceAs (CommRing (MvPolynomial σ R))

instance instAlgebraGraphAlgebra (f : τ → MvPolynomial σ R) : Algebra R (GraphAlgebra f) :=
  inferInstanceAs (Algebra R (MvPolynomial σ R))

def graphAlgebraEquiv (f : τ → MvPolynomial σ R) : MvPolynomial σ R ≃ₐ[R] GraphAlgebra f :=
  AlgEquiv.refl

def aevalGraphAlgebra (f : τ → MvPolynomial σ R) : MvPolynomial τ R →ₐ[R] GraphAlgebra f :=
  (graphAlgebraEquiv f).toAlgHom.comp (MvPolynomial.aeval f)

instance instAlgebraBaseGraphAlgebra (f : τ → MvPolynomial σ R) :
    Algebra (MvPolynomial τ R) (GraphAlgebra f) :=
  (aevalGraphAlgebra f).toRingHom.toAlgebra

section
variable (f : τ → MvPolynomial σ R)

theorem algebraMap_graphAlgebra (p : MvPolynomial τ R) :
    algebraMap (MvPolynomial τ R) (GraphAlgebra f) p = graphAlgebraEquiv f (MvPolynomial.aeval f p) :=
  rfl

private theorem algebraMap_graphAlgebra_eq_algebraMap_mvPolynomial_consolidated28 (r : R) :
    algebraMap R (GraphAlgebra f) r
      = algebraMap (MvPolynomial τ R) (GraphAlgebra f) (algebraMap R (MvPolynomial τ R) r) := by
  rw [algebraMap_graphAlgebra, AlgHom.commutes, AlgEquiv.commutes]


end

instance instIsScalarTowerGraphAlgebra (f : τ → MvPolynomial σ R) :
    IsScalarTower R (MvPolynomial τ R) (GraphAlgebra f) :=
  IsScalarTower.of_algebraMap_eq (algebraMap_graphAlgebra_eq_algebraMap_mvPolynomial_consolidated28 f)

def graphRelation (f : τ → MvPolynomial σ R) (i : τ) : MvPolynomial σ (MvPolynomial τ R) :=
  MvPolynomial.C (MvPolynomial.X i)
    - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (f i)

abbrev graphRelationIdeal (f : τ → MvPolynomial σ R) : Ideal (MvPolynomial σ (MvPolynomial τ R)) :=
  Ideal.span (Set.range (graphRelation f))

def graphAlgebraAeval (f : τ → MvPolynomial σ R) :
    MvPolynomial σ (MvPolynomial τ R) →ₐ[MvPolynomial τ R] GraphAlgebra f :=
  MvPolynomial.aeval (fun i : σ => graphAlgebraEquiv f (MvPolynomial.X i))

section
variable (f : τ → MvPolynomial σ R)

theorem graphAlgebraAeval_X (i : σ) :
    graphAlgebraAeval f (MvPolynomial.X i) = graphAlgebraEquiv f (MvPolynomial.X i) :=
  MvPolynomial.aeval_X _ i

private theorem graphAlgebraAeval_C_consolidated28 (a : MvPolynomial τ R) :
    graphAlgebraAeval f (MvPolynomial.C a) = graphAlgebraEquiv f (MvPolynomial.aeval f a) := by
  have h : graphAlgebraAeval f (MvPolynomial.C a)
      = algebraMap (MvPolynomial τ R) (GraphAlgebra f) a := by
    simp [graphAlgebraAeval]
  rw [h, algebraMap_graphAlgebra]

private theorem graphAlgebraAeval_map_C_consolidated28 (p : MvPolynomial σ R) :
    graphAlgebraAeval f (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) p)
      = graphAlgebraEquiv f p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp only [MvPolynomial.map_C, graphAlgebraAeval_C_consolidated28, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, MvPolynomial.map_X, hp, graphAlgebraAeval_X]

theorem graphAlgebraAeval_graphRelation (i : τ) :
    graphAlgebraAeval f (graphRelation f i) = 0 := by
  simp only [graphRelation, map_sub, graphAlgebraAeval_C_consolidated28, graphAlgebraAeval_map_C_consolidated28, MvPolynomial.aeval_X, sub_self]

private theorem graphAlgebraAeval_map_C_graphAlgebraEquiv_symm_consolidated28 (x : GraphAlgebra f) :
    graphAlgebraAeval f (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
      ((graphAlgebraEquiv f).symm x)) = x := by
  rw [graphAlgebraAeval_map_C_consolidated28, AlgEquiv.apply_symm_apply]


end

private def graphSubstitutionHom_consolidated28 (f : τ → MvPolynomial σ R) :
    MvPolynomial σ (MvPolynomial τ R) →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.aeval f : MvPolynomial τ R →ₐ[R] MvPolynomial σ R).toRingHom)
    MvPolynomial.X

section
variable (f : τ → MvPolynomial σ R)

private theorem graphSubstitutionHom_C_consolidated28 (a : MvPolynomial τ R) :
    graphSubstitutionHom_consolidated28 f (MvPolynomial.C a) = MvPolynomial.aeval f a := by
  simp [graphSubstitutionHom_consolidated28]

private theorem graphSubstitutionHom_X_consolidated28 (i : σ) :
    graphSubstitutionHom_consolidated28 f (MvPolynomial.X i) = MvPolynomial.X i := by
  simp [graphSubstitutionHom_consolidated28]

private theorem graphAlgebraAeval_eq_graphAlgebraEquiv_graphSubstitutionHom_consolidated28 (p : MvPolynomial σ (MvPolynomial τ R)) :
    graphAlgebraAeval f p = graphAlgebraEquiv f (graphSubstitutionHom_consolidated28 f p) := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [graphAlgebraAeval_C_consolidated28, graphSubstitutionHom_C_consolidated28]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X q i hq => simp only [map_mul, hq, graphAlgebraAeval_X, graphSubstitutionHom_X_consolidated28]

private theorem C_sub_map_C_aeval_mem_graphRelationIdeal_consolidated28 (a : MvPolynomial τ R) :
    MvPolynomial.C a - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
      (MvPolynomial.aeval f a) ∈ graphRelationIdeal f := by
  induction a using MvPolynomial.induction_on with
  | C r =>
      have key : (MvPolynomial.C (MvPolynomial.C r : MvPolynomial τ R) :
            MvPolynomial σ (MvPolynomial τ R))
          - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
            (MvPolynomial.aeval f (MvPolynomial.C r : MvPolynomial τ R)) = 0 := by
        simp [MvPolynomial.algebraMap_eq]
      rw [key]
      exact Ideal.zero_mem _
  | add p q hp hq =>
      have key : (MvPolynomial.C (p + q) : MvPolynomial σ (MvPolynomial τ R))
          - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
            (MvPolynomial.aeval f (p + q))
          = (MvPolynomial.C p - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
              (MvPolynomial.aeval f p))
            + (MvPolynomial.C q - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
              (MvPolynomial.aeval f q)) := by
        simp only [map_add]
        ring
      rw [key]
      exact Ideal.add_mem _ hp hq
  | mul_X p j hp =>
      have hrel : graphRelation f j ∈ graphRelationIdeal f := Ideal.subset_span ⟨j, rfl⟩
      have key : (MvPolynomial.C (p * MvPolynomial.X j) : MvPolynomial σ (MvPolynomial τ R))
          - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
            (MvPolynomial.aeval f (p * MvPolynomial.X j))
          = MvPolynomial.C p * graphRelation f j
            + (MvPolynomial.C p - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
                (MvPolynomial.aeval f p))
              * MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (f j) := by
        simp only [graphRelation, map_mul, MvPolynomial.aeval_X]
        ring
      rw [key]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hrel) (Ideal.mul_mem_right _ _ hp)

private theorem sub_map_C_mem_graphRelationIdeal_consolidated28 (p : MvPolynomial σ (MvPolynomial τ R)) :
    p - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (graphSubstitutionHom_consolidated28 f p)
      ∈ graphRelationIdeal f := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [graphSubstitutionHom_C_consolidated28]
      exact C_sub_map_C_aeval_mem_graphRelationIdeal_consolidated28 f a
  | add p q hp hq =>
      have key : p + q
          - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (graphSubstitutionHom_consolidated28 f (p + q))
          = (p - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (graphSubstitutionHom_consolidated28 f p))
            + (q - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
                (graphSubstitutionHom_consolidated28 f q)) := by
        simp only [map_add]
        ring
      rw [key]
      exact Ideal.add_mem _ hp hq
  | mul_X q i hq =>
      have key : q * MvPolynomial.X i
          - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
              (graphSubstitutionHom_consolidated28 f (q * MvPolynomial.X i))
          = (q - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (graphSubstitutionHom_consolidated28 f q))
            * MvPolynomial.X i := by
        simp only [map_mul, graphSubstitutionHom_X_consolidated28, MvPolynomial.map_X]
        ring
      rw [key]
      exact Ideal.mul_mem_right _ _ hq


end

def graphAlgebraGenerators (f : τ → MvPolynomial σ R) :
    Algebra.Generators (MvPolynomial τ R) (GraphAlgebra f) σ where
  val := fun i => graphAlgebraEquiv f (MvPolynomial.X i)
  σ' := fun x =>
    MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) ((graphAlgebraEquiv f).symm x)
  aeval_val_σ' := graphAlgebraAeval_map_C_graphAlgebraEquiv_symm_consolidated28 f

section
variable (f : τ → MvPolynomial σ R)

private theorem mem_ker_graphAlgebraGenerators_iff_consolidated28 (p : MvPolynomial σ (MvPolynomial τ R)) :
    p ∈ (graphAlgebraGenerators f).ker ↔ graphAlgebraAeval f p = 0 := Iff.rfl

private theorem span_range_graphRelation_eq_ker_consolidated28 :
    Ideal.span (Set.range (graphRelation f)) = (graphAlgebraGenerators f).ker := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    simp only [SetLike.mem_coe]
    exact (mem_ker_graphAlgebraGenerators_iff_consolidated28 f _).2 (graphAlgebraAeval_graphRelation f i)
  · intro p hp
    have hp' : graphAlgebraAeval f p = 0 := (mem_ker_graphAlgebraGenerators_iff_consolidated28 f p).1 hp
    have h0 : graphSubstitutionHom_consolidated28 f p = 0 := by
      have h1 := graphAlgebraAeval_eq_graphAlgebraEquiv_graphSubstitutionHom_consolidated28 f p
      rw [hp'] at h1
      have h2 : graphAlgebraEquiv f (graphSubstitutionHom_consolidated28 f p) = graphAlgebraEquiv f 0 := by
        rw [← h1, map_zero]
      exact (graphAlgebraEquiv f).injective h2
    have hmem := sub_map_C_mem_graphRelationIdeal_consolidated28 f p
    rwa [h0, map_zero, sub_zero] at hmem


end

def graphPresentation (f : τ → MvPolynomial σ R) :
    Algebra.Presentation (MvPolynomial τ R) (GraphAlgebra f) σ τ where
  toGenerators := graphAlgebraGenerators f
  relation := graphRelation f
  span_range_relation_eq_ker := span_range_graphRelation_eq_ker_consolidated28 f

def graphPreSubmersivePresentation (f : τ → MvPolynomial σ R) (v : τ → σ)
    (hv : Function.Injective v) :
    Algebra.PreSubmersivePresentation (MvPolynomial τ R) (GraphAlgebra f) σ τ where
  toPresentation := graphPresentation f
  map := v
  map_inj := hv

section
variable (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v)

@[simp] theorem graphPreSubmersivePresentation_relation :
    (graphPreSubmersivePresentation f v hv).relation = graphRelation f :=
  rfl

@[simp] theorem graphPreSubmersivePresentation_map :
    (graphPreSubmersivePresentation f v hv).map = v :=
  rfl


end

def graphJacobianMinorMatrix (f : τ → MvPolynomial σ R) (v : τ → σ) : Matrix τ τ (MvPolynomial σ R) :=
  Matrix.of fun i j => MvPolynomial.pderiv (v i) (f j)

theorem graphJacobianMinorMatrix_apply (f : τ → MvPolynomial σ R) (v : τ → σ) (i j : τ) :
    graphJacobianMinorMatrix f v i j = MvPolynomial.pderiv (v i) (f j) :=
  rfl

section
variable [Fintype τ] [DecidableEq τ] (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v)

theorem graphPreSubmersivePresentation_jacobiMatrix :
    (graphPreSubmersivePresentation f v hv).jacobiMatrix
      = -((graphJacobianMinorMatrix f v).map
          (fun p => MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) p)) := by
  ext i j
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  simp only [graphPreSubmersivePresentation_relation, graphPreSubmersivePresentation_map,
    graphRelation, map_sub, MvPolynomial.pderiv_C, MvPolynomial.pderiv_map, zero_sub,
    Matrix.neg_apply, Matrix.map_apply, graphJacobianMinorMatrix_apply]

theorem graphPreSubmersivePresentation_jacobian :
    (graphPreSubmersivePresentation f v hv).jacobian
      = (-1 : GraphAlgebra f) ^ Fintype.card τ * graphAlgebraEquiv f (graphJacobianMinorMatrix f v).det := by
  have hmap : ((graphJacobianMinorMatrix f v).map
      (fun p => MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) p)).det
      = MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (graphJacobianMinorMatrix f v).det :=
    (RingHom.map_det (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R))
      (graphJacobianMinorMatrix f v)).symm
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    graphPreSubmersivePresentation_jacobiMatrix, Matrix.det_neg, hmap, map_mul, map_pow,
    map_neg, map_one]
  congr 1
  exact graphAlgebraAeval_map_C_consolidated28 f _


end

end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IrreducibleComponentsFlatPreimage
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem apply_mem_irreducibleComponent_iff_of_generalizingMap
    (hf : GeneralizingMap (fun x : ↥X => f x))
    {C : Set ↥Y} (hC : C ∈ irreducibleComponents ↥Y) (x : ↥X) :
    (fun x : ↥X => f x) x ∈ C ↔
      ∃ C' : Set ↥X, C' ∈ irreducibleComponents ↥X ∧ x ∈ C' ∧
        closure ((fun x : ↥X => f x) '' C') = C := by
  have hcont : Continuous (fun x : ↥X => f x) := f.base.hom.continuous
  constructor
  · intro hx
    obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
    have hη' : closure ({η} : Set ↥Y) = C := hη
    have hxmem : (fun x : ↥X => f x) x ∈ closure ({η} : Set ↥Y) := by
      rw [hη']
      exact hx
    have hspec : η ⤳ (fun x : ↥X => f x) x := specializes_iff_mem_closure.mpr hxmem
    obtain ⟨x', hx'spec, hfx'⟩ := hf hspec
    refine ⟨irreducibleComponent x', irreducibleComponent_mem_irreducibleComponents x',
      ?_, ?_⟩
    · have hsub : closure ({x'} : Set ↥X) ⊆ irreducibleComponent x' :=
        closure_minimal (Set.singleton_subset_iff.2 mem_irreducibleComponent)
          isClosed_irreducibleComponent
      exact hsub (specializes_iff_mem_closure.mp hx'spec)
    · have hsub : C ⊆ closure ((fun x : ↥X => f x) '' irreducibleComponent x') := by
        rw [← hη']
        refine closure_minimal (Set.singleton_subset_iff.2 ?_) isClosed_closure
        exact subset_closure ⟨x', mem_irreducibleComponent, hfx'⟩
      have hirr : IsIrreducible (closure ((fun x : ↥X => f x) '' irreducibleComponent x')) :=
        (isIrreducible_irreducibleComponent.image (fun x : ↥X => f x)
          hcont.continuousOn).closure
      exact Set.Subset.antisymm (hC.2 hirr hsub) hsub
  · rintro ⟨C', -, hxC', rfl⟩
    exact subset_closure ⟨x, hxC', rfl⟩

theorem apply_mem_irreducibleComponent_iff_of_flat
    [Flat f]
    {C : Set ↥Y} (hC : C ∈ irreducibleComponents ↥Y) (x : ↥X) :
    (fun x : ↥X => f x) x ∈ C ↔
      ∃ C' : Set ↥X, C' ∈ irreducibleComponents ↥X ∧ x ∈ C' ∧
        closure ((fun x : ↥X => f x) '' C') = C := by
  have hf : GeneralizingMap (fun x : ↥X => f x) :=
    AlgebraicGeometry.Flat.generalizingMap (f := f)
  exact apply_mem_irreducibleComponent_iff_of_generalizingMap f hf hC x


end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StandardSmoothLift
section
set_option maxSynthPendingDepth 1

open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution
namespace StandardSmoothLift


section

variable {S R B : Type u} [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] {ι σ : Type} [Finite σ]
  (hsurj : Function.Surjective (algebraMap S R))
  (P : Algebra.SubmersivePresentation R B ι σ)

noncomputable def liftedRelation (j : σ) : MvPolynomial ι S :=
  Function.surjInv (MvPolynomial.map_surjective (algebraMap S R) hsurj) (P.relation j)

theorem map_liftedRelation (j : σ) :
    MvPolynomial.map (algebraMap S R) (liftedRelation hsurj P j) = P.relation j :=
  Function.surjInv_eq (MvPolynomial.map_surjective (algebraMap S R) hsurj) (P.relation j)

abbrev LiftedQuotient : Type u :=
  MvPolynomial ι S ⧸ Ideal.span (Set.range (liftedRelation hsurj P))

private theorem aeval_mk_X_liftedQuotient_surjective_consolidated30 :
    Function.Surjective
      ⇑(MvPolynomial.aeval (fun i : ι =>
          Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) (MvPolynomial.X i)) :
        MvPolynomial ι S →ₐ[S] LiftedQuotient hsurj P) := by
  have hEq : (MvPolynomial.aeval (fun i : ι =>
      Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) (MvPolynomial.X i)) :
        MvPolynomial ι S →ₐ[S] LiftedQuotient hsurj P) =
      Ideal.Quotient.mkₐ S (Ideal.span (Set.range (liftedRelation hsurj P))) :=
    MvPolynomial.algHom_ext (fun i => by simp)
  have h : ∀ q : MvPolynomial ι S,
      (MvPolynomial.aeval (fun i : ι =>
        Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) (MvPolynomial.X i)) :
        MvPolynomial ι S →ₐ[S] LiftedQuotient hsurj P) q =
      Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) q := by
    intro q
    rw [hEq]
    rfl
  intro x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨q, h q⟩

noncomputable def liftedGenerators : Algebra.Generators S (LiftedQuotient hsurj P) ι where
  val i := Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) (MvPolynomial.X i)
  σ' := Function.surjInv (aeval_mk_X_liftedQuotient_surjective_consolidated30 hsurj P)
  aeval_val_σ' := Function.surjInv_eq (aeval_mk_X_liftedQuotient_surjective_consolidated30 hsurj P)

private theorem span_range_liftedRelation_eq_ker_consolidated30 :
    Ideal.span (Set.range (liftedRelation hsurj P)) = (liftedGenerators hsurj P).ker := by
  have hval : (liftedGenerators hsurj P).val =
      fun i : ι => Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P)))
        (MvPolynomial.X i) := rfl
  have h : (MvPolynomial.aeval (liftedGenerators hsurj P).val :
        MvPolynomial ι S →ₐ[S] LiftedQuotient hsurj P) =
      Ideal.Quotient.mkₐ S (Ideal.span (Set.range (liftedRelation hsurj P))) :=
    MvPolynomial.algHom_ext fun i => by
      simp [hval]
  have hq : ∀ q : MvPolynomial ι S,
      (MvPolynomial.aeval (liftedGenerators hsurj P).val) q =
        Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) q :=
    fun q => DFunLike.congr_fun h q
  refine Ideal.ext fun q => ?_
  have hmem : q ∈ (liftedGenerators hsurj P).ker ↔
      (MvPolynomial.aeval (liftedGenerators hsurj P).val) q = 0 := Iff.rfl
  rw [hmem, hq q, Ideal.Quotient.eq_zero_iff_mem]

noncomputable def liftedPresentation : Algebra.Presentation S (LiftedQuotient hsurj P) ι σ where
  toGenerators := liftedGenerators hsurj P
  relation := liftedRelation hsurj P
  span_range_relation_eq_ker := span_range_liftedRelation_eq_ker_consolidated30 hsurj P

noncomputable def liftedPreSubmersivePresentation :
    Algebra.PreSubmersivePresentation S (LiftedQuotient hsurj P) ι σ where
  toPresentation := liftedPresentation hsurj P
  map := P.map
  map_inj := P.map_inj

@[simp] theorem liftedPreSubmersivePresentation_relation (j : σ) :
    (liftedPreSubmersivePresentation hsurj P).relation j = liftedRelation hsurj P j := rfl

@[simp] theorem liftedPreSubmersivePresentation_map :
    (liftedPreSubmersivePresentation hsurj P).map = P.map := rfl

abbrev LiftedAlgebra : Type u := Localization.Away (liftedPreSubmersivePresentation hsurj P).jacobian

private theorem isUnit_jacobian_localizationAway_comp_consolidated30 :
    IsUnit (Algebra.PreSubmersivePresentation.comp
      (Algebra.PreSubmersivePresentation.localizationAway (S := LiftedAlgebra hsurj P)
        (liftedPreSubmersivePresentation hsurj P).jacobian) (liftedPreSubmersivePresentation hsurj P)).jacobian := by
  rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    Algebra.smul_def]
  exact (IsLocalization.Away.algebraMap_isUnit (S := LiftedAlgebra hsurj P)
      (liftedPreSubmersivePresentation hsurj P).jacobian).mul
    (Algebra.SubmersivePresentation.localizationAway (S := LiftedAlgebra hsurj P)
      (liftedPreSubmersivePresentation hsurj P).jacobian).jacobian_isUnit

noncomputable def liftedSubmersivePresentation :
    Algebra.SubmersivePresentation S (LiftedAlgebra hsurj P) (Unit ⊕ ι) (Unit ⊕ σ) where
  toPreSubmersivePresentation :=
    Algebra.PreSubmersivePresentation.comp
      (Algebra.PreSubmersivePresentation.localizationAway (S := LiftedAlgebra hsurj P)
        (liftedPreSubmersivePresentation hsurj P).jacobian) (liftedPreSubmersivePresentation hsurj P)
  jacobian_isUnit := isUnit_jacobian_localizationAway_comp_consolidated30 hsurj P

noncomputable def mvPolynomialToBaseChange :
    MvPolynomial ι R →ₐ[R] R ⊗[S] LiftedAlgebra hsurj P :=
  MvPolynomial.aeval fun i : ι =>
    (1 : R) ⊗ₜ[S] (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P)
      (Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) (MvPolynomial.X i)))

private theorem mvPolynomialToBaseChange_map_consolidated30 (f : MvPolynomial ι S) :
    mvPolynomialToBaseChange hsurj P (MvPolynomial.map (algebraMap S R) f) =
      (1 : R) ⊗ₜ[S] (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P)
        (Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) f)) := by
  induction f using MvPolynomial.induction_on
  next a =>
    have hI : Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P)))
        (MvPolynomial.C a) = algebraMap S (LiftedQuotient hsurj P) a := by
      rw [← MvPolynomial.algebraMap_eq]
      exact (Ideal.Quotient.mkₐ S (Ideal.span (Set.range (liftedRelation hsurj P)))).commutes a
    have hL : mvPolynomialToBaseChange hsurj P (MvPolynomial.map (algebraMap S R) (MvPolynomial.C a))
        = algebraMap S (R ⊗[S] LiftedAlgebra hsurj P) a := by
      rw [MvPolynomial.map_C]
      simp only [mvPolynomialToBaseChange, MvPolynomial.aeval_C]
      rw [← IsScalarTower.algebraMap_apply S R (R ⊗[S] LiftedAlgebra hsurj P) a]
    rw [hL, hI, ← IsScalarTower.algebraMap_apply S (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) a,
      Algebra.algebraMap_eq_smul_one a, Algebra.algebraMap_eq_smul_one a,
      Algebra.TensorProduct.one_def, TensorProduct.tmul_smul]
  next p q hp hq =>
    simp [hp, hq, TensorProduct.tmul_add]
  next p i hp =>
    have hX : mvPolynomialToBaseChange hsurj P (MvPolynomial.X i)
        = (1 : R) ⊗ₜ[S] (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P)
            (Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P)))
              (MvPolynomial.X i))) := by
      simp [mvPolynomialToBaseChange]
    simp [hp, hX, Algebra.TensorProduct.tmul_mul_tmul]

private theorem mvPolynomialToBaseChange_relation_eq_zero_consolidated30 (j : σ) :
    mvPolynomialToBaseChange hsurj P (P.relation j) = 0 := by
  have hz : Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P)))
      (liftedRelation hsurj P j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j))
  have h := mvPolynomialToBaseChange_map_consolidated30 hsurj P (liftedRelation hsurj P j)
  rw [map_liftedRelation hsurj P j, hz] at h
  simpa using h

private theorem mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero_consolidated30 (q : MvPolynomial ι R)
    (hq : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B) q = 0) :
    mvPolynomialToBaseChange hsurj P q = 0 := by
  have hmem : q ∈ Ideal.span (Set.range P.relation) := by
    rw [P.span_range_relation_eq_ker, Algebra.Generators.ker_eq_ker_aeval_val]
    simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hq
  have hsub : Ideal.span (Set.range P.relation) ≤
      RingHom.ker (mvPolynomialToBaseChange hsurj P : MvPolynomial ι R →+* R ⊗[S] LiftedAlgebra hsurj P) := by
    rw [Ideal.span_le]
    rintro x ⟨j, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.coe_toRingHom]
    exact mvPolynomialToBaseChange_relation_eq_zero_consolidated30 hsurj P j
  simpa only [RingHom.mem_ker, AlgHom.coe_toRingHom] using hsub hmem

private theorem mvPolynomialToBaseChange_section_one_consolidated30 :
    mvPolynomialToBaseChange hsurj P (P.σ' 1) = 1 := by
  have h1 : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B) (P.σ' (1 : B) - 1) = 0 := by
    rw [map_sub, map_one, P.aeval_val_σ' 1, sub_self]
  have h0 := mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero_consolidated30 hsurj P _ h1
  rw [map_sub, map_one] at h0
  linear_combination h0

private theorem mvPolynomialToBaseChange_section_mul_consolidated30 (x y : B) :
    mvPolynomialToBaseChange hsurj P (P.σ' (x * y)) =
      mvPolynomialToBaseChange hsurj P (P.σ' x) * mvPolynomialToBaseChange hsurj P (P.σ' y) := by
  have hker : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B)
      (P.σ' (x * y) - P.σ' x * P.σ' y) = 0 := by
    simp [P.aeval_val_σ']
  have h := mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero_consolidated30 hsurj P _ hker
  rw [map_sub, map_mul] at h
  linear_combination h

private theorem mvPolynomialToBaseChange_section_zero_consolidated30 :
    mvPolynomialToBaseChange hsurj P (P.σ' 0) = 0 := by
  have h0 : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B) (P.σ' (0 : B)) = 0 :=
    P.aeval_val_σ' 0
  exact mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero_consolidated30 hsurj P _ h0

private theorem mvPolynomialToBaseChange_section_add_consolidated30 (x y : B) :
    mvPolynomialToBaseChange hsurj P (P.σ' (x + y)) =
      mvPolynomialToBaseChange hsurj P (P.σ' x) + mvPolynomialToBaseChange hsurj P (P.σ' y) := by
  have h1 : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B)
      (P.σ' (x + y) - (P.σ' x + P.σ' y)) = 0 := by
    rw [map_sub, map_add, P.aeval_val_σ' (x + y), P.aeval_val_σ' x, P.aeval_val_σ' y, sub_self]
  have h0 := mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero_consolidated30 hsurj P _ h1
  rw [map_sub, map_add] at h0
  linear_combination h0

private theorem mvPolynomialToBaseChange_section_algebraMap_consolidated30 (r : R) :
    mvPolynomialToBaseChange hsurj P (P.σ' (algebraMap R B r)) =
      algebraMap R (R ⊗[S] LiftedAlgebra hsurj P) r := by
  have h1 : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B)
      (P.σ' (algebraMap R B r) - MvPolynomial.C r) = 0 := by
    rw [map_sub, P.aeval_val_σ' (algebraMap R B r), MvPolynomial.aeval_C, sub_self]
  have h0 := mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero_consolidated30 hsurj P _ h1
  have hC : mvPolynomialToBaseChange hsurj P (MvPolynomial.C r) =
      algebraMap R (R ⊗[S] LiftedAlgebra hsurj P) r := by
    have hcom := (mvPolynomialToBaseChange hsurj P).commutes r
    rwa [MvPolynomial.algebraMap_eq] at hcom
  rw [map_sub, hC] at h0
  linear_combination h0

noncomputable def invBaseChangeHom : B →ₐ[R] R ⊗[S] LiftedAlgebra hsurj P where
  toFun b := mvPolynomialToBaseChange hsurj P (P.σ' b)
  map_one' := mvPolynomialToBaseChange_section_one_consolidated30 hsurj P
  map_mul' := mvPolynomialToBaseChange_section_mul_consolidated30 hsurj P
  map_zero' := mvPolynomialToBaseChange_section_zero_consolidated30 hsurj P
  map_add' := mvPolynomialToBaseChange_section_add_consolidated30 hsurj P
  commutes' := mvPolynomialToBaseChange_section_algebraMap_consolidated30 hsurj P

theorem invBaseChangeHom_aeval (q : MvPolynomial ι R) :
    invBaseChangeHom hsurj P (MvPolynomial.aeval P.val q) = mvPolynomialToBaseChange hsurj P q := by
  have hker : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B)
      (P.σ' ((MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B) q) - q) = 0 := by
    rw [map_sub, P.aeval_val_σ', sub_self]
  have h := mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero_consolidated30 hsurj P _ hker
  rw [map_sub] at h
  have hf : invBaseChangeHom hsurj P ((MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B) q)
      = mvPolynomialToBaseChange hsurj P
          (P.σ' ((MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B) q)) := rfl
  rw [hf]
  linear_combination h

section

variable [Algebra S B] [IsScalarTower S R B]

theorem aeval_eq_zero_of_mem_span_liftedRelation (q : MvPolynomial ι S)
    (hq : q ∈ Ideal.span (Set.range (liftedRelation hsurj P))) :
    (MvPolynomial.aeval P.val : MvPolynomial ι S →ₐ[S] B) q = 0 := by
  have hsub : Ideal.span (Set.range (liftedRelation hsurj P)) ≤
      RingHom.ker (MvPolynomial.aeval P.val : MvPolynomial ι S →ₐ[S] B).toRingHom := by
    rw [Ideal.span_le]
    rintro x ⟨j, rfl⟩
    have hmem : P.relation j ∈ Ideal.span (Set.range P.relation) :=
      Ideal.subset_span ⟨j, rfl⟩
    rw [P.span_range_relation_eq_ker, Algebra.Generators.ker_eq_ker_aeval_val] at hmem
    have h0 : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B) (P.relation j) = 0 := by
      simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hmem
    have h1 : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B)
        (MvPolynomial.map (algebraMap S R) (liftedRelation hsurj P j)) =
          (MvPolynomial.aeval P.val : MvPolynomial ι S →ₐ[S] B) (liftedRelation hsurj P j) := by
      rw [MvPolynomial.aeval_map_algebraMap]
    rw [map_liftedRelation hsurj P j] at h1
    have h2 : (MvPolynomial.aeval P.val : MvPolynomial ι S →ₐ[S] B)
        (liftedRelation hsurj P j) = 0 := by
      rw [← h1]
      exact h0
    simpa only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] using h2
  simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hsub hq

noncomputable def liftedQuotientHom : LiftedQuotient hsurj P →ₐ[S] B :=
  Ideal.Quotient.liftₐ (Ideal.span (Set.range (liftedRelation hsurj P)))
    (MvPolynomial.aeval P.val : MvPolynomial ι S →ₐ[S] B)
    (aeval_eq_zero_of_mem_span_liftedRelation hsurj P)

@[simp] theorem liftedQuotientHom_mk (q : MvPolynomial ι S) :
    liftedQuotientHom hsurj P
        (Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) q) =
      (MvPolynomial.aeval P.val : MvPolynomial ι S →ₐ[S] B) q := rfl

private theorem isUnit_liftedQuotientHom_jacobian_consolidated30 :
    IsUnit ((liftedQuotientHom hsurj P).toRingHom (liftedPreSubmersivePresentation hsurj P).jacobian) := by
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  have hval : (liftedPreSubmersivePresentation hsurj P).val =
      fun i : ι => Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P)))
        (MvPolynomial.X i) := rfl
  have hmk : ∀ q : MvPolynomial ι S,
      (MvPolynomial.aeval (liftedPreSubmersivePresentation hsurj P).val) q =
        Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) q := by
    have h : (MvPolynomial.aeval (liftedPreSubmersivePresentation hsurj P).val :
          MvPolynomial ι S →ₐ[S] LiftedQuotient hsurj P) =
        Ideal.Quotient.mkₐ S (Ideal.span (Set.range (liftedRelation hsurj P))) :=
      MvPolynomial.algHom_ext fun i => by simp [hval]
    exact fun q => DFunLike.congr_fun h q
  have hmat : ∀ a b : σ,
      MvPolynomial.map (algebraMap S R) ((liftedPreSubmersivePresentation hsurj P).jacobiMatrix a b)
        = P.jacobiMatrix a b := by
    intro a b
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
      Algebra.PreSubmersivePresentation.jacobiMatrix_apply, liftedPreSubmersivePresentation_map,
      liftedPreSubmersivePresentation_relation, ← MvPolynomial.pderiv_map, map_liftedRelation]
  have h1 : (liftedPreSubmersivePresentation hsurj P).jacobiMatrix.map
      (MvPolynomial.map (algebraMap S R)) = P.jacobiMatrix := by
    refine Matrix.ext fun a b => ?_
    rw [Matrix.map_apply]
    exact hmat a b
  have hdet : MvPolynomial.map (algebraMap S R)
      ((liftedPreSubmersivePresentation hsurj P).jacobiMatrix.det) = P.jacobiMatrix.det := by
    calc MvPolynomial.map (algebraMap S R) ((liftedPreSubmersivePresentation hsurj P).jacobiMatrix.det)
        = ((liftedPreSubmersivePresentation hsurj P).jacobiMatrix.map
            (MvPolynomial.map (algebraMap S R))).det := RingHom.map_det ..
      _ = P.jacobiMatrix.det := by rw [h1]
  have hjS : (liftedPreSubmersivePresentation hsurj P).jacobian =
      Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P)))
        ((liftedPreSubmersivePresentation hsurj P).jacobiMatrix.det) := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    exact hmk _
  have hjR : P.jacobian =
      (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B) P.jacobiMatrix.det := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      Algebra.Generators.algebraMap_apply]
  have h2 : IsUnit (liftedQuotientHom hsurj P ((liftedPreSubmersivePresentation hsurj P).jacobian)) := by
    have hkey : liftedQuotientHom hsurj P ((liftedPreSubmersivePresentation hsurj P).jacobian) = P.jacobian := by
      rw [hjS, liftedQuotientHom_mk, hjR, ← hdet]
      simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
      rw [← IsScalarTower.algebraMap_eq S R B]
    rw [hkey]
    exact P.jacobian_isUnit
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using h2

private theorem awayLift_jacobian_algebraMap_eq_consolidated30 (s : S) :
    ((IsLocalization.Away.lift (liftedPreSubmersivePresentation hsurj P).jacobian
        (isUnit_liftedQuotientHom_jacobian_consolidated30 hsurj P) : LiftedAlgebra hsurj P →+* B))
      (algebraMap S (LiftedAlgebra hsurj P) s) = algebraMap S B s := by
  have h : ∀ x : LiftedQuotient hsurj P,
      ((IsLocalization.Away.lift (liftedPreSubmersivePresentation hsurj P).jacobian
          (isUnit_liftedQuotientHom_jacobian_consolidated30 hsurj P) : LiftedAlgebra hsurj P →+* B))
        (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) x) =
        (liftedQuotientHom hsurj P).toRingHom x := by
    intro x
    exact IsLocalization.lift_eq ..
  rw [IsScalarTower.algebraMap_apply S (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) s, h]
  exact (liftedQuotientHom hsurj P).commutes s

noncomputable def liftedAlgebraHom : LiftedAlgebra hsurj P →ₐ[S] B :=
  { (IsLocalization.Away.lift (liftedPreSubmersivePresentation hsurj P).jacobian
      (isUnit_liftedQuotientHom_jacobian_consolidated30 hsurj P) : LiftedAlgebra hsurj P →+* B) with
    commutes' := awayLift_jacobian_algebraMap_eq_consolidated30 hsurj P }

theorem liftedAlgebraHom_algebraMap (x : LiftedQuotient hsurj P) :
    liftedAlgebraHom hsurj P (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) x) =
      liftedQuotientHom hsurj P x := by
  have h : liftedAlgebraHom hsurj P (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) x) =
      (IsLocalization.Away.lift (liftedPreSubmersivePresentation hsurj P).jacobian
        (isUnit_liftedQuotientHom_jacobian_consolidated30 hsurj P) : LiftedAlgebra hsurj P →+* B)
        (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) x) := rfl
  rw [h]
  simp only [IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

theorem liftedAlgebraHom_surjective : Function.Surjective (liftedAlgebraHom hsurj P) := by
  intro b
  obtain ⟨p, hp⟩ := MvPolynomial.map_surjective (algebraMap S R) hsurj (P.σ' b)
  have h1 : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B)
      (MvPolynomial.map (algebraMap S R) p) =
        (MvPolynomial.aeval P.val : MvPolynomial ι S →ₐ[S] B) p := by
    rw [MvPolynomial.aeval_map_algebraMap]
  refine ⟨algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P)
    (Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) p), ?_⟩
  rw [liftedAlgebraHom_algebraMap, liftedQuotientHom_mk, ← h1, hp]
  exact P.aeval_val_σ' b

noncomputable def baseChangeHom : (R ⊗[S] LiftedAlgebra hsurj P) →ₐ[R] B :=
  Algebra.TensorProduct.lift (Algebra.ofId R B) (liftedAlgebraHom hsurj P)
    (fun _ _ => Commute.all _ _)

private theorem invBaseChangeHom_liftedQuotientHom_consolidated30 (q : LiftedQuotient hsurj P) :
    invBaseChangeHom hsurj P (liftedQuotientHom hsurj P q) =
      (1 : R) ⊗ₜ[S] (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) q) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  have h1 : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B)
      (MvPolynomial.map (algebraMap S R) p) =
        (MvPolynomial.aeval P.val : MvPolynomial ι S →ₐ[S] B) p := by
    rw [MvPolynomial.aeval_map_algebraMap]
  rw [liftedQuotientHom_mk, ← h1, invBaseChangeHom_aeval]
  exact mvPolynomialToBaseChange_map_consolidated30 hsurj P p

private theorem invBaseChangeHom_liftedAlgebraHom_consolidated30 (x : LiftedAlgebra hsurj P) :
    invBaseChangeHom hsurj P (liftedAlgebraHom hsurj P x) = (1 : R) ⊗ₜ[S] x := by
  have key : (invBaseChangeHom hsurj P).toRingHom.comp (liftedAlgebraHom hsurj P).toRingHom =
      (Algebra.TensorProduct.includeRight :
        LiftedAlgebra hsurj P →ₐ[S] R ⊗[S] LiftedAlgebra hsurj P).toRingHom := by
    refine IsLocalization.ringHom_ext
      (Submonoid.powers (liftedPreSubmersivePresentation hsurj P).jacobian) ?_
    refine RingHom.ext fun q => ?_
    have h := invBaseChangeHom_liftedQuotientHom_consolidated30 hsurj P q
    rw [← liftedAlgebraHom_algebraMap hsurj P q] at h
    exact h
  exact DFunLike.congr_fun key x

theorem baseChangeHom_bijective : Function.Bijective (baseChangeHom hsurj P) := by
  constructor
  · have hleft : Function.LeftInverse (invBaseChangeHom hsurj P) (baseChangeHom hsurj P) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul r x =>
        have h1 : baseChangeHom hsurj P (r ⊗ₜ[S] x)
            = algebraMap R B r * liftedAlgebraHom hsurj P x := by
          simp only [baseChangeHom, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
        have h2 : invBaseChangeHom hsurj P (algebraMap R B r)
            = r ⊗ₜ[S] (1 : LiftedAlgebra hsurj P) := (invBaseChangeHom hsurj P).commutes r
        rw [h1, map_mul, h2, invBaseChangeHom_liftedAlgebraHom_consolidated30,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      | add a b ha hb =>
        rw [map_add, map_add, ha, hb]
    exact hleft.injective
  · intro b
    obtain ⟨x, hx⟩ := liftedAlgebraHom_surjective hsurj P b
    refine ⟨(1 : R) ⊗ₜ[S] x, ?_⟩
    rw [← hx]
    simp only [baseChangeHom, Algebra.TensorProduct.lift_tmul, map_one, one_mul]

noncomputable def baseChangeEquiv : (R ⊗[S] LiftedAlgebra hsurj P) ≃ₐ[R] B :=
  AlgEquiv.ofBijective (baseChangeHom hsurj P) (baseChangeHom_bijective hsurj P)

theorem baseChangeEquiv_one_tmul (b' : LiftedAlgebra hsurj P) :
    baseChangeEquiv hsurj P (1 ⊗ₜ[S] b') = liftedAlgebraHom hsurj P b' := by
  have h : baseChangeEquiv hsurj P (1 ⊗ₜ[S] b')
      = (Algebra.ofId R B) (1 : R) * liftedAlgebraHom hsurj P b' := rfl
  rw [h, map_one, one_mul]

end

end

end StandardSmoothLift
end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceGlobalSections
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

abbrev affineSpaceIsoSpecMvPolynomial (k : Type u) [Field k] (v : Type u) :
    affineSpaceIndexedBy k v ≅ Spec (CommRingCat.of (MvPolynomial v k)) :=
  AffineSpace.SpecIso v (CommRingCat.of k)

def mvPolynomialToGlobalSections (k : Type u) [Field k] (v : Type u) :
    MvPolynomial v k →+* Γ(affineSpaceIndexedBy k v, ⊤) :=
  ((affineSpaceIsoSpecMvPolynomial k v).hom.appTop).hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv).hom

def globalSectionsToMvPolynomial (k : Type u) [Field k] (v : Type u) :
    Γ(affineSpaceIndexedBy k v, ⊤) →+* MvPolynomial v k :=
  ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).hom).hom.comp
    ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop).hom

section
variable {X Y : Scheme.{u}} (e : X ≅ Y)

private theorem appTop_inv_hom_apply_consolidated50 (s : Γ(Y, ⊤)) :
    e.inv.appTop (e.hom.appTop s) = s := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.inv_hom_id]
  simp

private theorem appTop_hom_inv_apply_consolidated50 (s : Γ(X, ⊤)) :
    e.hom.appTop (e.inv.appTop s) = s := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.hom_inv_id]
  simp


end

section
variable (k : Type u) [Field k] (v : Type u)

private theorem mvPolynomialToGlobalSections_apply_consolidated50 (p : MvPolynomial v k) :
    mvPolynomialToGlobalSections k v p =
      (affineSpaceIsoSpecMvPolynomial k v).hom.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv p) := rfl

private theorem globalSectionsToMvPolynomial_apply_consolidated50 (s : Γ(affineSpaceIndexedBy k v, ⊤)) :
    globalSectionsToMvPolynomial k v s =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).hom
        ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop s) := rfl

theorem leftInverse_globalSectionsToMvPolynomial :
    Function.LeftInverse ⇑(globalSectionsToMvPolynomial k v) ⇑(mvPolynomialToGlobalSections k v) := by
  intro p
  rw [mvPolynomialToGlobalSections_apply_consolidated50, globalSectionsToMvPolynomial_apply_consolidated50, appTop_inv_hom_apply_consolidated50]
  simp

theorem rightInverse_globalSectionsToMvPolynomial :
    Function.RightInverse ⇑(globalSectionsToMvPolynomial k v) ⇑(mvPolynomialToGlobalSections k v) := by
  intro s
  rw [globalSectionsToMvPolynomial_apply_consolidated50, mvPolynomialToGlobalSections_apply_consolidated50, Iso.hom_inv_id_apply,
    appTop_hom_inv_apply_consolidated50]


end

def mvPolynomialEquivGlobalSections (k : Type u) [Field k] (v : Type u) :
    MvPolynomial v k ≃+* Γ(affineSpaceIndexedBy k v, ⊤) where
  toFun := mvPolynomialToGlobalSections k v
  invFun := globalSectionsToMvPolynomial k v
  left_inv := leftInverse_globalSectionsToMvPolynomial k v
  right_inv := rightInverse_globalSectionsToMvPolynomial k v
  map_mul' := map_mul (mvPolynomialToGlobalSections k v)
  map_add' := map_add (mvPolynomialToGlobalSections k v)

section
variable (k : Type u) [Field k] (v : Type u)

theorem mvPolynomialEquivGlobalSections_apply (p : MvPolynomial v k) :
    mvPolynomialEquivGlobalSections k v p =
      (affineSpaceIsoSpecMvPolynomial k v).hom.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv p) := rfl

theorem mvPolynomialEquivGlobalSections_symm_apply (s : Γ(affineSpaceIndexedBy k v, ⊤)) :
    (mvPolynomialEquivGlobalSections k v).symm s =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).hom
        ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop s) := rfl

private theorem affineSpaceIsoSpecMvPolynomial_inv_appTop_coord_consolidated50 (i : v) :
    (affineSpaceIsoSpecMvPolynomial k v).inv.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv (MvPolynomial.X i) := by
  rw [AlgebraicGeometry.AffineSpace.SpecIso_inv_appTop_coord]


end

@[simp]
theorem mvPolynomialEquivGlobalSections_X (k : Type u) [Field k] (v : Type u) (i : v) :
    mvPolynomialEquivGlobalSections k v (MvPolynomial.X i) = AffineSpace.coord (Spec (CommRingCat.of k)) i := by
  rw [mvPolynomialEquivGlobalSections_apply, ← affineSpaceIsoSpecMvPolynomial_inv_appTop_coord_consolidated50 k v i, appTop_hom_inv_apply_consolidated50]

@[simp]
theorem mvPolynomialEquivGlobalSections_symm_coord (k : Type u) [Field k] (v : Type u) (i : v) :
    (mvPolynomialEquivGlobalSections k v).symm (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
      MvPolynomial.X i := by
  rw [← mvPolynomialEquivGlobalSections_X k v i, RingEquiv.symm_apply_apply]

section
variable (k : Type u) [Field k] (v : Type u)

theorem mvPolynomialEquivGlobalSections_C (c : k) :
    mvPolynomialEquivGlobalSections k v (MvPolynomial.C c) =
      (affineSpaceIndexedByToSpec k v).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
  rw [mvPolynomialEquivGlobalSections_apply]
  have h2 : (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial v k)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial v k))).appTop :=
    Scheme.ΓSpecIso_inv_naturality _
  have key : (affineSpaceIsoSpecMvPolynomial k v).inv.appTop
      ((affineSpaceIndexedByToSpec k v).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv (MvPolynomial.C c) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    simp
    rw [← CommRingCat.comp_apply, ← h2, CommRingCat.comp_apply]
    simp
  rw [← key, appTop_hom_inv_apply_consolidated50]

theorem mvPolynomialEquivGlobalSections_basicOpen (p : MvPolynomial v k) :
    (affineSpaceIndexedBy k v).basicOpen (mvPolynomialEquivGlobalSections k v p) =
      (affineSpaceIsoSpecMvPolynomial k v).hom ⁻¹ᵁ
        (Spec (CommRingCat.of (MvPolynomial v k))).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv p) := by
  rw [mvPolynomialEquivGlobalSections_apply, Scheme.preimage_basicOpen]
  rfl

theorem mvPolynomialEquivGlobalSections_basicOpen_primeSpectrum (p : MvPolynomial v k) :
    (affineSpaceIndexedBy k v).basicOpen (mvPolynomialEquivGlobalSections k v p) =
      (affineSpaceIsoSpecMvPolynomial k v).hom ⁻¹ᵁ
        (PrimeSpectrum.basicOpen p : Opens (PrimeSpectrum (MvPolynomial v k))) := by
  rw [mvPolynomialEquivGlobalSections_basicOpen, basicOpen_eq_of_affine]


end

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphAlgebraStandardSmooth
section

namespace FunctorialResolution.EmbeddedResolution

variable {R : Type u} [CommRing R] {σ τ : Type u}

section
abbrev graphJacobianMinorDet [Fintype τ] [DecidableEq τ] (f : τ → MvPolynomial σ R) (v : τ → σ) :
    GraphAlgebra f :=
  graphAlgebraEquiv f (graphJacobianMinorMatrix f v).det

abbrev GraphAlgebraAway [Fintype τ] [DecidableEq τ] (f : τ → MvPolynomial σ R) (v : τ → σ) : Type u :=
  Localization.Away (graphJacobianMinorDet f v)

section
variable [Fintype τ] [DecidableEq τ] (f : τ → MvPolynomial σ R) (v : τ → σ)

theorem isUnit_algebraMap_graphJacobianMinorDet :
    IsUnit (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v) (graphJacobianMinorDet f v)) :=
  IsLocalization.map_units (M := Submonoid.powers (graphJacobianMinorDet f v)) (GraphAlgebraAway f v)
    ⟨graphJacobianMinorDet f v, Submonoid.mem_powers _⟩

theorem isUnit_algebraMap_jacobian_graphPreSubmersive (hv : Function.Injective v) :
    IsUnit (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)
      (graphPreSubmersivePresentation f v hv).jacobian) := by
  rw [graphPreSubmersivePresentation_jacobian, map_mul, map_pow, map_neg, map_one]
  exact ((isUnit_one.neg).pow _).mul (isUnit_algebraMap_graphJacobianMinorDet f v)


end

private def graphAlgebraAwayLocalizationPresentation_consolidated53 [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    Algebra.SubmersivePresentation (GraphAlgebra f) (GraphAlgebraAway f v) Unit Unit :=
  Algebra.SubmersivePresentation.localizationAway (S := GraphAlgebraAway f v) (r := graphJacobianMinorDet f v)

private def graphAlgebraAwayPreSubmersivePresentation_consolidated53 [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Algebra.PreSubmersivePresentation (MvPolynomial τ R) (GraphAlgebraAway f v) (Unit ⊕ σ) (Unit ⊕ τ) :=
  Algebra.PreSubmersivePresentation.comp (graphAlgebraAwayLocalizationPresentation_consolidated53 f v).toPreSubmersivePresentation
    (graphPreSubmersivePresentation f v hv)

private theorem isUnit_jacobian_presentation_graphAlgebraAway_consolidated53 [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    IsUnit (graphAlgebraAwayPreSubmersivePresentation_consolidated53 f v hv).jacobian := by
  rw [graphAlgebraAwayPreSubmersivePresentation_consolidated53,
    Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    Algebra.smul_def]
  exact (isUnit_algebraMap_jacobian_graphPreSubmersive f v hv).mul (graphAlgebraAwayLocalizationPresentation_consolidated53 f v).jacobian_isUnit

private def graphAlgebraAwaySubmersivePresentation_consolidated53 [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Algebra.SubmersivePresentation (MvPolynomial τ R) (GraphAlgebraAway f v)
      (Unit ⊕ Fin (Fintype.card σ)) (Unit ⊕ Fin (Fintype.card τ)) :=
  Algebra.SubmersivePresentation.reindex
    { toPreSubmersivePresentation := graphAlgebraAwayPreSubmersivePresentation_consolidated53 f v hv
      jacobian_isUnit := isUnit_jacobian_presentation_graphAlgebraAway_consolidated53 f v hv }
    (Equiv.sumCongr (Equiv.refl Unit) (Fintype.equivFin σ).symm)
    (Equiv.sumCongr (Equiv.refl Unit) (Fintype.equivFin τ).symm)

theorem isStandardSmooth_graphAlgebraAway [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Algebra.IsStandardSmooth (MvPolynomial τ R) (GraphAlgebraAway f v) := by
  constructor
  exact ⟨Unit ⊕ Fin (Fintype.card σ), Unit ⊕ Fin (Fintype.card τ), inferInstance, inferInstance,
    ⟨graphAlgebraAwaySubmersivePresentation_consolidated53 f v hv⟩⟩

end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StandardSmoothLiftRelativeDimension
section

open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution

namespace StandardSmoothLift

section

variable {S R B : Type u} [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] {ι σ : Type} [Finite ι] [Finite σ]
  (hsurj : Function.Surjective (algebraMap S R))
  (P : Algebra.SubmersivePresentation R B ι σ)

theorem liftedSubmersivePresentation_dimension :
    (liftedSubmersivePresentation hsurj P).dimension = P.dimension := by
  have hu : Nat.card Unit = 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_unit]
  have h1 : Nat.card (Unit ⊕ ι) = Nat.card ι + 1 := by
    rw [Nat.card_sum, hu]
    omega
  have h2 : Nat.card (Unit ⊕ σ) = Nat.card σ + 1 := by
    rw [Nat.card_sum, hu]
    omega
  show Nat.card (Unit ⊕ ι) - Nat.card (Unit ⊕ σ) = Nat.card ι - Nat.card σ
  rw [h1, h2]
  omega

end

end StandardSmoothLift

section

variable (S R B : Type u) [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] [Algebra S B] [IsScalarTower S R B]

theorem exists_lift_of_isStandardSmoothOfRelativeDimension (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r R B]
    (hsurj : Function.Surjective (algebraMap S R)) :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra S B') (f : B' →ₐ[S] B),
      Algebra.IsStandardSmoothOfRelativeDimension r S B' ∧ Function.Surjective f ∧
        ∃ e : (R ⊗[S] B') ≃ₐ[R] B, ∀ b' : B', e (1 ⊗ₜ[S] b') = f b' := by
  have hinst : Algebra.IsStandardSmoothOfRelativeDimension r R B := ‹_›
  obtain ⟨ι, σ, hσ, hι, P, hdim⟩ := hinst.out
  have : Finite ι := hι
  have : Finite σ := hσ
  refine ⟨StandardSmoothLift.LiftedAlgebra hsurj P, inferInstance, inferInstance,
    StandardSmoothLift.liftedAlgebraHom hsurj P, ?_,
    StandardSmoothLift.liftedAlgebraHom_surjective hsurj P,
    StandardSmoothLift.baseChangeEquiv hsurj P,
    StandardSmoothLift.baseChangeEquiv_one_tmul hsurj P⟩
  exact ⟨⟨Unit ⊕ ι, Unit ⊕ σ, inferInstance, inferInstance,
    StandardSmoothLift.liftedSubmersivePresentation hsurj P,
    (StandardSmoothLift.liftedSubmersivePresentation_dimension hsurj P).trans hdim⟩⟩

end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphAlgebraSpecSmooth
section

namespace FunctorialResolution.EmbeddedResolution

open CategoryTheory AlgebraicGeometry

variable {R : Type u} [CommRing R] {σ τ : Type u} [Fintype τ] [DecidableEq τ]

theorem smooth_specMap_algebraMap_graphAlgebraAway [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  have : Algebra.IsStandardSmooth (MvPolynomial τ R) (GraphAlgebraAway f v) :=
    isStandardSmooth_graphAlgebraAway f v hv
  show @Algebra.Smooth _ _ _ _ (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)).toAlgebra
  have h : (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)).toAlgebra =
      (inferInstance : Algebra (MvPolynomial τ R) (GraphAlgebraAway f v)) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  rw [h]
  refine ⟨?_, ?_⟩ <;> infer_instance

theorem isOpenImmersion_specMap_algebraMap_graphAlgebraAway
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)))) := by
  have : IsLocalization.Away (graphJacobianMinorDet f v) (GraphAlgebraAway f v) := inferInstance
  exact IsOpenImmersion.of_isLocalization (graphJacobianMinorDet f v) ..

instance instIsOpenImmersionSpecMapGraphAway
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)))) :=
  isOpenImmersion_specMap_algebraMap_graphAlgebraAway f v

section
variable (f : τ → MvPolynomial σ R) (v : τ → σ)

theorem range_specMap_algebraMap_graphAlgebraAway
    :
    Set.range ⇑(Spec.map
        (CommRingCat.ofHom (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)))).base =
      (PrimeSpectrum.basicOpen (graphJacobianMinorDet f v) : Set (PrimeSpectrum (GraphAlgebra f))) := by
  have h := PrimeSpectrum.localization_away_comap_range (R := GraphAlgebra f)
    (GraphAlgebraAway f v) (graphJacobianMinorDet f v)
  exact h

theorem algebraMap_graphAlgebraAway_eq_comp
    :
    (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)) =
      (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)).comp
        (algebraMap (MvPolynomial τ R) (GraphAlgebra f)) :=
  IsScalarTower.algebraMap_eq (MvPolynomial τ R) (GraphAlgebra f) (GraphAlgebraAway f v)

theorem specMap_algebraMap_graphAlgebraAway_eq_comp
    :
    Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v))) =
      Spec.map (CommRingCat.ofHom (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial τ R) (GraphAlgebra f))) := by
  rw [algebraMap_graphAlgebraAway_eq_comp f v, CommRingCat.ofHom_comp, Spec.map_comp]


end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IdealSheafFlatComapInjective
section

open CategoryTheory AlgebraicGeometry TensorProduct

namespace FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf

variable {W Y : Scheme.{u}}

private theorem one_mem_map_colon_of_mem_map_consolidated77 {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : RingHom.Flat φ) (L : Ideal R) (a : R) (h : φ a ∈ L.map φ) :
    (1 : S) ∈ Ideal.map φ (Submodule.comap (LinearMap.lsmul R R a) L) := by
  let _ : Algebra R S := φ.toAlgebra
  have : Module.Flat R S := hφ
  have halg : (algebraMap R S) = φ := rfl
  have hex : Function.Exact (Submodule.subtype (Submodule.comap (LinearMap.lsmul R R a) L))
      ((L.mkQ).comp (LinearMap.lsmul R R a)) := by
    rw [LinearMap.exact_iff, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.range_subtype]
  have hex2 := Module.Flat.lTensor_exact (M := S) hex
  have key : ∀ s : S, s ∈ L.map φ → s ⊗ₜ[R] (L.mkQ (1 : R)) = 0 := by
    intro s hs
    let ψ : S →ₗ[S] S ⊗[R] (R ⧸ L) :=
      { toFun := fun t => t ⊗ₜ[R] (L.mkQ (1 : R))
        map_add' := fun x y => TensorProduct.add_tmul x y _
        map_smul' := fun c x => TensorProduct.smul_tmul' c x _ }
    have hψ : ∀ t : S, ψ t = t ⊗ₜ[R] (L.mkQ (1 : R)) := fun _ => rfl
    have hsub : L.map φ ≤ LinearMap.ker ψ := by
      rw [Ideal.map_le_iff_le_comap]
      intro l hl
      have h0 : l • (L.mkQ (1 : R)) = 0 := by
        rw [← map_smul]
        simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul, mul_one]
        exact hl
      simp only [Ideal.mem_comap, LinearMap.mem_ker, hψ]
      rw [show φ l = l • (1 : S) from by rw [Algebra.smul_def, halg, mul_one],
        TensorProduct.smul_tmul, h0, TensorProduct.tmul_zero]
    have hker := LinearMap.mem_ker.mp (hsub hs)
    rwa [hψ] at hker
  have hzero : (LinearMap.lTensor S ((L.mkQ).comp (LinearMap.lsmul R R a)))
      ((1 : S) ⊗ₜ[R] (1 : R)) = 0 := by
    rw [LinearMap.lTensor_tmul]
    show (1 : S) ⊗ₜ[R] (L.mkQ (a * (1 : R))) = 0
    rw [mul_one]
    have h1 : (L.mkQ a) = a • (L.mkQ (1 : R)) := by
      rw [← map_smul]; simp
    rw [h1, ← TensorProduct.smul_tmul,
      show a • (1 : S) = φ a from by rw [Algebra.smul_def, halg, mul_one]]
    exact key _ h
  obtain ⟨v, hv⟩ := (hex2 ((1 : S) ⊗ₜ[R] (1 : R))).mp hzero
  have hrange : ∀ u : S ⊗[R] (Submodule.comap (LinearMap.lsmul R R a) L),
      (TensorProduct.rid R S) (LinearMap.lTensor S
        (Submodule.subtype (Submodule.comap (LinearMap.lsmul R R a) L)) u)
      ∈ Ideal.map φ (Submodule.comap (LinearMap.lsmul R R a) L) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul s c =>
        rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Algebra.smul_def, halg]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem φ c.2)
    | add u₁ u₂ h₁ h₂ =>
        rw [map_add, map_add]
        exact Submodule.add_mem _ h₁ h₂
  have hfin := hrange v
  rw [hv, TensorProduct.rid_tmul, one_smul] at hfin
  exact hfin

section
variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
include hU

private theorem exists_not_mem_basicOpen_of_ne_top_consolidated77 (C : Ideal Γ(X, U)) (hC : C ≠ ⊤) :
    ∃ x ∈ U, ∀ c ∈ C, x ∉ X.basicOpen c := by
  obtain ⟨m, hm, hCm⟩ := C.exists_le_maximal hC
  let p : PrimeSpectrum Γ(X, U) := ⟨m, hm.isPrime⟩
  refine ⟨hU.fromSpec.base p, ?_, ?_⟩
  · have hr : hU.fromSpec.base p ∈ Set.range hU.fromSpec.base := ⟨p, rfl⟩
    rw [hU.range_fromSpec] at hr
    exact hr
  · intro c hc hmem
    have h1 : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen c := hmem
    rw [hU.fromSpec_preimage_basicOpen] at h1
    have h2 : c ∉ m := h1
    exact h2 (hCm hc)

private theorem exists_mem_basicOpen_of_span_eq_top_consolidated77 (s : Set Γ(X, U)) (hs : Ideal.span s = ⊤) (x : X) (hx : x ∈ U) :
    ∃ c ∈ s, x ∈ X.basicOpen c := by
  have hxr : x ∈ Set.range hU.fromSpec.base := by
    rw [hU.range_fromSpec]; exact hx
  obtain ⟨p, hp⟩ := hxr
  by_contra hcon
  push Not at hcon
  have hsub : s ⊆ (p.asIdeal : Set Γ(X, U)) := by
    intro c hcs
    have h1 : ¬ (p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen c) := by
      intro hmem
      exact hcon c hcs (by rw [← hp]; exact hmem)
    rw [hU.fromSpec_preimage_basicOpen] at h1
    have h2 : c ∈ p.asIdeal := by
      by_contra hcc
      exact h1 hcc
    simpa using h2
  have hle := Ideal.span_le.mpr hsub
  rw [hs] at hle
  exact p.2.ne_top (top_le_iff.mp hle)


end

private theorem flat_appLE_consolidated77 (g : W ⟶ Y) [Flat g] (U : Y.affineOpens)
    (V : W.affineOpens) (e : (V : W.Opens) ≤ g ⁻¹ᵁ (U : Y.Opens)) :
    RingHom.Flat (g.appLE (U : Y.Opens) (V : W.Opens) e).hom := by
  apply AlgebraicGeometry.HasRingHomProperty.appLE (P := @Flat)
  all_goals assumption

section
variable (g : W ⟶ Y) [Flat g] [AlgebraicGeometry.Surjective g] (I J : Y.IdealSheafData)

private theorem colon_eq_top_of_comap_le_consolidated77 (h : I.comap g ≤ J.comap g) (U : Y.affineOpens) (a : Γ(Y, (U : Y.Opens)))
    (ha : a ∈ I.ideal U) (C : Ideal Γ(Y, (U : Y.Opens)))
    (hCdef : C = Submodule.comap
      (LinearMap.lsmul Γ(Y, (U : Y.Opens)) Γ(Y, (U : Y.Opens)) a) (J.ideal U)) :
    C = ⊤ := by
  by_contra hCtop
  obtain ⟨x, hxU, hx⟩ := exists_not_mem_basicOpen_of_ne_top_consolidated77 U.2 C hCtop
  obtain ⟨w, hw⟩ := AlgebraicGeometry.Surjective.surj (f := g) x
  have hwU : w ∈ g ⁻¹ᵁ (U : Y.Opens) := by
    show g.base w ∈ (U : Y.Opens)
    rw [hw]; exact hxU
  obtain ⟨V, hV, hwV, hVU⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp W.isBasis_affineOpens) hwU
  have hV' : IsAffineOpen V := hV
  have hcomap0 := Scheme.IdealSheafData.le_def.mp h ⟨V, hV'⟩
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I g U ⟨V, hV'⟩ hVU,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE J g U ⟨V, hV'⟩ hVU] at hcomap0
  have hcomap : Ideal.map (g.appLE (U : Y.Opens) V hVU).hom (I.ideal U) ≤
      Ideal.map (g.appLE (U : Y.Opens) V hVU).hom (J.ideal U) := hcomap0
  have hflat : RingHom.Flat (g.appLE (U : Y.Opens) V hVU).hom := flat_appLE_consolidated77 g U ⟨V, hV'⟩ hVU
  have hone := one_mem_map_colon_of_mem_map_consolidated77 (g.appLE (U : Y.Opens) V hVU).hom hflat (J.ideal U) a
    (hcomap (Ideal.mem_map_of_mem _ ha))
  rw [← hCdef] at hone
  have htop : Ideal.map (g.appLE (U : Y.Opens) V hVU).hom C = ⊤ :=
    (Ideal.eq_top_iff_one _).mpr hone
  have hspan : Ideal.span (((g.appLE (U : Y.Opens) V hVU).hom) ''
      (C : Set Γ(Y, (U : Y.Opens)))) = ⊤ := by
    rw [← Ideal.map_span, Ideal.span_eq]
    exact htop
  obtain ⟨f, hf, hwf⟩ := exists_mem_basicOpen_of_span_eq_top_consolidated77 hV' _ hspan w hwV
  obtain ⟨c, hc, hcf⟩ := hf
  have hwb : w ∈ W.basicOpen ((g.appLE (U : Y.Opens) V hVU).hom c) := by
    rw [hcf]; exact hwf
  have hbeta : W.basicOpen ((g.appLE (U : Y.Opens) V hVU).hom c) ≤ g ⁻¹ᵁ (Y.basicOpen c) := by
    rw [Scheme.preimage_basicOpen]
    simp [Scheme.Hom.appLE]
  have hmem := hbeta hwb
  exact hx c hc (by rw [← hw]; exact hmem)

theorem le_of_comap_le (h : I.comap g ≤ J.comap g) : I ≤ J := by
  rw [Scheme.IdealSheafData.le_def]
  intro U a ha
  have hC := colon_eq_top_of_comap_le_consolidated77 g I J h U a ha _ rfl
  have h1 : (1 : Γ(Y, (U : Y.Opens))) ∈ Submodule.comap
      (LinearMap.lsmul Γ(Y, (U : Y.Opens)) Γ(Y, (U : Y.Opens)) a) (J.ideal U) := by
    rw [hC]; exact Submodule.mem_top
  have h2 : a * (1 : Γ(Y, (U : Y.Opens))) ∈ J.ideal U := h1
  simpa using h2

theorem eq_of_comap_eq (h : I.comap g = J.comap g) : I = J :=
  le_antisymm (le_of_comap_le g I J (le_of_eq h)) (le_of_comap_le g J I (le_of_eq h.symm))


end

end FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothAffineLiftRelativeDimension
section

open CategoryTheory AlgebraicGeometry

open scoped TensorProduct

section
namespace FunctorialResolution.EmbeddedResolution

namespace SmoothChartRelativeDimension

private def tensorProductLiftRingHom_consolidated86 {S R C T : Type u} [CommRing S] [CommRing R] [CommRing C]
    [CommRing T] [Algebra S R] [Algebra S C] (a : R →+* T) (b : C →+* T)
    (hab : ∀ s : S, a (algebraMap S R s) = b (algebraMap S C s)) : (R ⊗[S] C) →+* T :=
  letI : Algebra S T := (a.comp (algebraMap S R)).toAlgebra
  letI : Algebra R T := a.toAlgebra
  haveI : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom S R T)
      ({ toRingHom := b, commutes' := fun s => (hab s).symm } : C →ₐ[S] T)).toRingHom

private theorem tensorProductLiftRingHom_tmul_consolidated86 {S R C T : Type u} [CommRing S] [CommRing R] [CommRing C]
    [CommRing T] [Algebra S R] [Algebra S C] (a : R →+* T) (b : C →+* T)
    (hab : ∀ s : S, a (algebraMap S R s) = b (algebraMap S C s)) (x : R) (y : C) :
    tensorProductLiftRingHom_consolidated86 a b hab (x ⊗ₜ[S] y) = a x * b y := by
  let _ : Algebra S T := (a.comp (algebraMap S R)).toAlgebra
  let _ : Algebra R T := a.toAlgebra
  have : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Algebra.TensorProduct.productMap_apply_tmul (IsScalarTower.toAlgHom S R T)
    ({ toRingHom := b, commutes' := fun s => (hab s).symm } : C →ₐ[S] T) x y

theorem exists_affineOpen_isStandardSmoothOfRelativeDimension {X Y : Scheme.{u}}
    [IsAffine X] (r : ℕ) (h : Y ⟶ X)
    [SmoothOfRelativeDimension r h] (y : ↥Y) :
    ∃ (V : Y.Opens) (_ : y ∈ V) (_ : IsAffineOpen V),
      RingHom.IsStandardSmoothOfRelativeDimension r
        (CommRingCat.Hom.hom ((V.ι ≫ h).appTop)) := by
  obtain ⟨U, hU, V, hV, hyV, e, hss⟩ := ‹SmoothOfRelativeDimension r h›.1 y
  have hmemU : h.base y ∈ U := e hyV
  obtain ⟨f₀, hf₀le, hf₀mem⟩ :=
    (isAffineOpen_top X).exists_basicOpen_le (⟨h.base y, hmemU⟩ : ↥U) (by trivial)
  set g : Γ(X, U) :=
    (ConcreteCategory.hom (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)) f₀ with hgdef
  set s : Γ(Y, V) := (ConcreteCategory.hom (h.appLE U V e)) g with hsdef
  have hsg : s = (CommRingCat.Hom.hom (h.appLE U V e)) g := rfl
  have hbg : X.basicOpen g = U ⊓ X.basicOpen f₀ :=
    Scheme.basicOpen_res X f₀ (homOfLE (le_top : U ≤ ⊤)).op
  have hbgf : X.basicOpen g = X.basicOpen f₀ := hbg.trans (inf_eq_right.mpr hf₀le)
  have hbs : Y.basicOpen s = V ⊓ h ⁻¹ᵁ X.basicOpen g :=
    Scheme.basicOpen_appLE h V U e g
  have hyW : y ∈ Y.basicOpen s := by
    rw [hbs]
    refine ⟨hyV, ?_⟩
    show h.base y ∈ X.basicOpen g
    rw [hbgf]
    exact hf₀mem
  have hWaff : IsAffineOpen (Y.basicOpen s) := hV.basicOpen s
  have hle₂ : Y.basicOpen s ≤ h ⁻¹ᵁ X.basicOpen g := by
    rw [hbs]; exact inf_le_right
  have hle₃ : Y.basicOpen s ≤ h ⁻¹ᵁ (⊤ : X.Opens) := by
    intro z hz; trivial
  have hbgU : X.basicOpen g ≤ U := X.basicOpen_le g
  have hWV : Y.basicOpen s ≤ V := Y.basicOpen_le s
  have hmm : Submonoid.map (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g)
      = Submonoid.powers s := by
    ext x
    constructor
    · rintro ⟨y', ⟨n, rfl⟩, rfl⟩
      exact ⟨n, by rw [map_pow, hsg]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨g ^ n, ⟨n, rfl⟩, by rw [map_pow, hsg]⟩
  have hlocX : IsLocalization (Submonoid.powers g) (Γ(X, X.basicOpen g) : Type u) :=
    hU.isLocalization_basicOpen g
  have hlocY : IsLocalization
      (Submonoid.map (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g))
      (Γ(Y, Y.basicOpen s) : Type u) := by
    rw [hmm]
    exact hV.isLocalization_basicOpen s
  have hloc := RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves r
    (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g)
    (Γ(X, X.basicOpen g) : Type u) (Γ(Y, Y.basicOpen s) : Type u) hss
  have hle_sub : Submonoid.powers g ≤ Submonoid.comap (CommRingCat.Hom.hom (h.appLE U V e))
      (Submonoid.map (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g)) :=
    fun x hx => ⟨x, hx, rfl⟩
  have hloc2 : RingHom.IsStandardSmoothOfRelativeDimension r
      (IsLocalization.map (Γ(Y, Y.basicOpen s) : Type u)
        (CommRingCat.Hom.hom (h.appLE U V e)) hle_sub) := hloc
  have arrow : h.appLE U V e ≫ Y.presheaf.map (homOfLE hWV).op
      = X.presheaf.map (homOfLE hbgU).op ≫ h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂ := by
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have key : IsLocalization.map (Γ(Y, Y.basicOpen s) : Type u)
        (CommRingCat.Hom.hom (h.appLE U V e)) hle_sub
      = CommRingCat.Hom.hom (h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers g) ?_
    rw [IsLocalization.map_comp]
    exact congrArg CommRingCat.Hom.hom arrow
  have hP : RingHom.IsStandardSmoothOfRelativeDimension r
      (CommRingCat.Hom.hom (h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂)) := by
    rw [← key]
    exact hloc2
  let _ : Algebra (Γ(X, ⊤) : Type u) (Γ(X, X.basicOpen g) : Type u) :=
    (CommRingCat.Hom.hom
      (X.presheaf.map (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op)).toAlgebra
  have : IsLocalization.Away f₀ (Γ(X, X.basicOpen g) : Type u) :=
    (isAffineOpen_top X).isLocalization_of_eq_basicOpen f₀
      (homOfLE (le_top : X.basicOpen g ≤ ⊤)) hbgf
  have hsrc :=
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway r).1
  have hcomp0 : RingHom.IsStandardSmoothOfRelativeDimension r
      ((CommRingCat.Hom.hom (h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂)).comp
        (algebraMap (Γ(X, ⊤) : Type u) (Γ(X, X.basicOpen g) : Type u))) :=
    hsrc _ f₀ _ hP
  have hmap : X.presheaf.map (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op ≫
      h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂ = h.appLE ⊤ (Y.basicOpen s) hle₃ :=
    Scheme.Hom.map_appLE h hle₂ (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op
  have hcomp : RingHom.IsStandardSmoothOfRelativeDimension r
      (CommRingCat.Hom.hom (h.appLE ⊤ (Y.basicOpen s) hle₃)) := by
    rw [← hmap, CommRingCat.hom_comp]
    exact hcomp0
  have hA : ((Y.basicOpen s).ι ''ᵁ ⊤) ≤ (⊤ : Y.Opens) := le_top
  have hBeq : ((Y.basicOpen s).ι ''ᵁ ⊤) = Y.basicOpen s := by simp
  have hB : Y.basicOpen s ≤ ((Y.basicOpen s).ι ''ᵁ ⊤) := le_of_eq hBeq.symm
  have hclean : h.appTop ≫ (Y.presheaf.map (homOfLE hA).op ≫ Y.presheaf.map (homOfLE hB).op)
      = h.appLE (⊤ : X.Opens) (Y.basicOpen s) hle₃ := by
    rw [← Functor.map_comp]
    rfl
  have hiso : ((Y.basicOpen s).ι ≫ h).appTop ≫ (Y.basicOpen s).topIso.hom
      = h.appLE ⊤ (Y.basicOpen s) hle₃ := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.Opens.topIso_hom, Scheme.Opens.ι_appTop]
    exact hclean
  have hgoal : ((Y.basicOpen s).ι ≫ h).appTop
      = h.appLE ⊤ (Y.basicOpen s) hle₃ ≫ (Y.basicOpen s).topIso.inv :=
    (Iso.eq_comp_inv _).mpr hiso
  refine ⟨Y.basicOpen s, hyW, hWaff, ?_⟩
  rw [hgoal]
  exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := r)).1 _
    (Y.basicOpen s).topIso.symm.commRingCatIsoToRingEquiv hcomp

theorem exists_lift_isPushout_of_isStandardSmoothOfRelativeDimension {S R B : CommRingCat.{u}}
    (ι : S ⟶ R) (hι : Function.Surjective ⇑(CommRingCat.Hom.hom ι)) (φ : R ⟶ B) (r : ℕ)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom φ)) :
    ∃ (B' : CommRingCat.{u}) (σ : S ⟶ B') (ψ : B' ⟶ B),
      RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom σ) ∧
        Function.Surjective ⇑(CommRingCat.Hom.hom ψ) ∧
        CategoryTheory.IsPushout ι σ φ ψ := by
  let _ : Algebra (S : Type u) (R : Type u) := (CommRingCat.Hom.hom ι).toAlgebra
  let _ : Algebra (R : Type u) (B : Type u) := (CommRingCat.Hom.hom φ).toAlgebra
  let _ : Algebra (S : Type u) (B : Type u) :=
    ((CommRingCat.Hom.hom φ).comp (CommRingCat.Hom.hom ι)).toAlgebra
  have : IsScalarTower (S : Type u) (R : Type u) (B : Type u) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsStandardSmoothOfRelativeDimension r (R : Type u) (B : Type u) := hφ
  obtain ⟨C, hCring, hCalg, f, hss, hfs, e, he⟩ :=
    FunctorialResolution.EmbeddedResolution.exists_lift_of_isStandardSmoothOfRelativeDimension (S : Type u) (R : Type u)
      (B : Type u) r hι
  have : Algebra.IsStandardSmoothOfRelativeDimension r (S : Type u) C := hss
  have hcond : ι ≫ φ = CommRingCat.ofHom (algebraMap (S : Type u) C) ≫
      CommRingCat.ofHom f.toRingHom := by
    refine CommRingCat.hom_ext (RingHom.ext fun s => ?_)
    exact (f.commutes s).symm
  have hcc : ∀ (c : CategoryTheory.Limits.PushoutCocone ι
        (CommRingCat.ofHom (algebraMap (S : Type u) C))) (s : (S : Type u)),
      (CommRingCat.Hom.hom c.inl) (algebraMap (S : Type u) (R : Type u) s)
        = (CommRingCat.Hom.hom c.inr) (algebraMap (S : Type u) C s) := fun c s =>
    congrArg (fun t : S ⟶ c.pt => (CommRingCat.Hom.hom t) s) c.condition
  have facR : ∀ c : CategoryTheory.Limits.PushoutCocone ι
      (CommRingCat.ofHom (algebraMap (S : Type u) C)),
      CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom
          ((tensorProductLiftRingHom_consolidated86 (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)).comp
            e.symm.toAlgHom.toRingHom) = c.inr := by
    intro c
    refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
    show tensorProductLiftRingHom_consolidated86 (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)
        (e.symm (f z)) = (CommRingCat.Hom.hom c.inr) z
    rw [show e.symm (f z) = (1 : (R : Type u)) ⊗ₜ[(S : Type u)] z from
      e.symm_apply_eq.mpr (he z).symm, tensorProductLiftRingHom_tmul_consolidated86, map_one, one_mul]
  refine ⟨CommRingCat.of C, CommRingCat.ofHom (algebraMap (S : Type u) C),
    CommRingCat.ofHom f.toRingHom, ?_, ?_, ?_⟩
  · exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap r).mpr hss
  · exact hfs
  · refine CategoryTheory.IsPushout.of_isColimit' ⟨hcond⟩
      (CategoryTheory.Limits.PushoutCocone.IsColimit.mk hcond
        (fun c => CommRingCat.ofHom
          ((tensorProductLiftRingHom_consolidated86 (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)).comp
            e.symm.toAlgHom.toRingHom)) ?_ facR ?_)
    · intro c
      refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      obtain ⟨s, rfl⟩ := hι x
      have key : ι ≫ (φ ≫ CommRingCat.ofHom
          ((tensorProductLiftRingHom_consolidated86 (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)).comp
            e.symm.toAlgHom.toRingHom)) = ι ≫ c.inl := by
        rw [← Category.assoc, hcond, Category.assoc, facR c, ← c.condition]
      exact congrArg (fun t : S ⟶ c.pt => (CommRingCat.Hom.hom t) s) key
    · intro c m h₁ h₂
      refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
      obtain ⟨z, rfl⟩ := hfs b
      exact congrArg (fun t : CommRingCat.of C ⟶ c.pt => (CommRingCat.Hom.hom t) z)
        (h₂.trans (facR c).symm)

end SmoothChartRelativeDimension

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SubordinateAffineCover
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution


private def affineOpensLePreimageCover_consolidated81 {X' X : Scheme.{u}} (φ : X' ⟶ X) {ι : Type u}
    (U : ι → X.Opens) : Set X'.Opens :=
  {W : X'.Opens | IsAffineOpen W ∧ ∃ i, W ≤ φ ⁻¹ᵁ (U i)}

section
variable {X' X : Scheme.{u}}

private theorem mem_affineOpensLePreimageCover_consolidated81 (φ : X' ⟶ X) {ι : Type u}
    (U : ι → X.Opens) {W : X'.Opens} :
    W ∈ affineOpensLePreimageCover_consolidated81 φ U ↔ IsAffineOpen W ∧ ∃ i, W ≤ φ ⁻¹ᵁ (U i) :=
  Iff.rfl

theorem exists_finite_affine_cover_subordinate [CompactSpace X']
    (φ : X' ⟶ X) {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    ∃ (κ : Type u) (_ : Finite κ) (V : κ → X'.Opens) (β : κ → ι),
      (∀ a, IsAffineOpen (V a)) ∧ (∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) ∧ iSup V = ⊤ := by
  classical
  have hSmem : ∀ W : affineOpensLePreimageCover_consolidated81 φ U,
      IsAffineOpen (W : X'.Opens) ∧ ∃ i, (W : X'.Opens) ≤ φ ⁻¹ᵁ (U i) :=
    fun W => (mem_affineOpensLePreimageCover_consolidated81 φ U).mp W.2
  have hcov : ∀ x : X', ∃ W : affineOpensLePreimageCover_consolidated81 φ U, x ∈ ((W : X'.Opens) : Set X') := by
    intro x
    obtain ⟨i, hi⟩ : ∃ i, x ∈ (φ ⁻¹ᵁ (U i) : X'.Opens) := by
      have hx : φ.base x ∈ (⊤ : X.Opens) := by simp
      rw [← hU] at hx
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨i, hi⟩
    obtain ⟨W, hW, hxW, hWle⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X') hi
    have hW' : IsAffineOpen W := hW
    exact ⟨⟨W, (mem_affineOpensLePreimageCover_consolidated81 φ U).mpr ⟨hW', i, hWle⟩⟩, hxW⟩
  have hcomp : IsCompact (Set.univ : Set X') := isCompact_univ
  obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover
      (fun W : affineOpensLePreimageCover_consolidated81 φ U => ((W : X'.Opens) : Set X'))
      (fun W => (W : X'.Opens).isOpen) (fun x _ => Set.mem_iUnion.mpr (hcov x))
  refine ⟨{W : affineOpensLePreimageCover_consolidated81 φ U // W ∈ t}, inferInstance, fun a => (a.1 : X'.Opens),
    fun a => (hSmem a.1).2.choose, fun a => (hSmem a.1).1,
    fun a => (hSmem a.1).2.choose_spec, ?_⟩
  refine SetLike.coe_injective ?_
  rw [TopologicalSpace.Opens.coe_top]
  refine Set.eq_univ_of_forall fun x => ?_
  have hx := ht (Set.mem_univ x)
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨W, hWt, hxW⟩ := hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hWt⟩, hxW⟩


end

noncomputable def opensCoprodMapOfRefinement {X' X : Scheme.{u}} (φ : X' ⟶ X) {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    sigmaOpens X' V ⟶ sigmaOpens X U :=
  Sigma.desc fun a =>
    φ.resLE (U (β a)) (V a) (hβ a) ≫ Sigma.ι (fun i => (U i).toScheme) (β a)

@[simp]
theorem sigmaι_opensCoprodMapOfRefinement {X' X : Scheme.{u}} (φ : X' ⟶ X) {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) (a : κ) :
    Sigma.ι (fun a => (V a).toScheme) a ≫ opensCoprodMapOfRefinement φ U V β hβ =
      φ.resLE (U (β a)) (V a) (hβ a) ≫ Sigma.ι (fun i => (U i).toScheme) (β a) := by
  simp [opensCoprodMapOfRefinement]

section
variable {X' X : Scheme.{u}} (φ : X' ⟶ X)

theorem opensCoprodMapOfRefinement_comp_sigmaOpensDesc {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    opensCoprodMapOfRefinement φ U V β hβ ≫ sigmaOpensDesc X U = sigmaOpensDesc X' V ≫ φ := by
  refine Limits.Sigma.hom_ext _ _ fun a => ?_
  rw [← Category.assoc, sigmaι_opensCoprodMapOfRefinement, Category.assoc, sigma_ι_sigmaOpensDesc,
    sigma_ι_sigmaOpensDesc_assoc]
  simp

private theorem resLE_eq_homOfLE_comp_restrict_consolidated81 (U : X.Opens) (V : X'.Opens) (e : V ≤ φ ⁻¹ᵁ U) :
    φ.resLE U V e = X'.homOfLE e ≫ φ ∣_ U := by
  rw [← cancel_mono U.ι]
  simp

private theorem smooth_resLE_consolidated81 [Smooth φ]
    (U : X.Opens) (V : X'.Opens) (e : V ≤ φ ⁻¹ᵁ U) :
    Smooth (φ.resLE U V e) := by
  rw [resLE_eq_homOfLE_comp_restrict_consolidated81]
  infer_instance

theorem smooth_opensCoprodMapOfRefinement [Smooth φ] {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    Smooth (opensCoprodMapOfRefinement φ U V β hβ) := by
  show Smooth (Sigma.desc fun a => φ.resLE (U (β a)) (V a) (hβ a) ≫
      Sigma.ι (fun i => (U i).toScheme) (β a))
  refine smooth_sigmaDesc _ fun a => ?_
  have := smooth_resLE_consolidated81 φ (U (β a)) (V a) (hβ a)
  infer_instance


end

instance instSmoothOpensCoprodRefine {X' X : Scheme.{u}} (φ : X' ⟶ X) [Smooth φ] {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    Smooth (opensCoprodMapOfRefinement φ U V β hβ) :=
  smooth_opensCoprodMapOfRefinement φ U V β hβ

theorem locallyOfFiniteType_opensCoprodMapOfRefinement {X' X : Scheme.{u}} (φ : X' ⟶ X)
    [LocallyOfFiniteType φ] {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    LocallyOfFiniteType (opensCoprodMapOfRefinement φ U V β hβ) := by
  have h1 : LocallyOfFiniteType (sigmaOpensDesc X' V ≫ φ) := inferInstance
  have h2 : LocallyOfFiniteType (opensCoprodMapOfRefinement φ U V β hβ ≫ sigmaOpensDesc X U) := by
    rw [opensCoprodMapOfRefinement_comp_sigmaOpensDesc]
    exact h1
  exact locallyOfFiniteType_of_comp _ (sigmaOpensDesc X U)

instance instLocallyOfFiniteTypeOpensCoprodRefine {X' X : Scheme.{u}} (φ : X' ⟶ X)
    [LocallyOfFiniteType φ] {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    LocallyOfFiniteType (opensCoprodMapOfRefinement φ U V β hβ) :=
  locallyOfFiniteType_opensCoprodMapOfRefinement φ U V β hβ

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SupportFlatPullback
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private theorem generalizingMap_of_flat_consolidated64 [Flat f] :
    GeneralizingMap (fun x : ↥X => f x) :=
  AlgebraicGeometry.Flat.generalizingMap f

theorem closure_image_mem_irreducibleComponents_of_generalizingMap
    (hf : GeneralizingMap (fun x : ↥X => f x))
    {C : Set ↥X} (hC : C ∈ irreducibleComponents ↥X) :
    closure ((fun x : ↥X => f x) '' C) ∈ irreducibleComponents ↥Y := by
  have hcont : Continuous (fun x : ↥X => f x) := f.continuous
  have hCirr : IsIrreducible C := hC.1
  have hCmax : ∀ ⦃b : Set ↥X⦄, IsIrreducible b → C ≤ b → b ≤ C := hC.2
  have hCcl : closure C = C :=
    subset_antisymm (hCmax hCirr.closure subset_closure) subset_closure
  have hCclosed : IsClosed C := by rw [← hCcl]; exact isClosed_closure
  obtain ⟨η, hη⟩ := QuasiSober.sober hCirr hCclosed
  have hη' : closure ({η} : Set ↥X) = C := hη
  have hηC : η ∈ C := by rw [← hη']; exact subset_closure rfl
  have key : closure ((fun x : ↥X => f x) '' C) = closure ({f η} : Set ↥Y) := by
    have h1 : (fun x : ↥X => f x) '' C ⊆ closure ({f η} : Set ↥Y) := by
      rw [← hη']
      intro w hw
      have hw2 := image_closure_subset_closure_image hcont hw
      rwa [Set.image_singleton] at hw2
    have h2 : ({f η} : Set ↥Y) ⊆ (fun x : ↥X => f x) '' C :=
      Set.singleton_subset_iff.mpr (Set.mem_image_of_mem _ hηC)
    exact subset_antisymm (closure_minimal h1 isClosed_closure) (closure_mono h2)
  have hmax : ∀ y : ↥Y, y ⤳ f η → y = f η := by
    intro y hy
    obtain ⟨x', hx'η, hfx'⟩ := hf hy
    have h1 : η ∈ closure ({x'} : Set ↥X) := specializes_iff_mem_closure.mp hx'η
    have h2 : C ⊆ closure ({x'} : Set ↥X) := by
      rw [← hη']
      exact closure_minimal (Set.singleton_subset_iff.mpr h1) isClosed_closure
    have h3 : closure ({x'} : Set ↥X) ⊆ C := hCmax isIrreducible_singleton.closure h2
    have hx'C : x' ∈ C := h3 (subset_closure rfl)
    have hηx' : η ⤳ x' := specializes_iff_mem_closure.mpr (by rw [hη']; exact hx'C)
    have hA : nhds x' ≤ nhds η := hx'η
    have hB : nhds η ≤ nhds x' := hηx'
    have hins : Inseparable x' η := le_antisymm hA hB
    have hxx : x' = η := hins.eq
    rw [← hfx', hxx]
  rw [key]
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro Z hZ hsub
  have hZ' : IsIrreducible Z := hZ
  have hsub' : closure ({f η} : Set ↥Y) ⊆ Z := hsub
  obtain ⟨z, hz⟩ := QuasiSober.sober hZ'.closure isClosed_closure
  have hz' : closure ({z} : Set ↥Y) = closure Z := hz
  have h1 : f η ∈ closure ({z} : Set ↥Y) := by
    rw [hz']
    exact subset_closure (hsub' (subset_closure rfl))
  have h2 : z = f η := hmax z (specializes_iff_mem_closure.mpr h1)
  show Z ⊆ closure ({f η} : Set ↥Y)
  intro w hw
  rw [← h2, hz']
  exact subset_closure hw

theorem support_comap (I : Y.IdealSheafData) :
    ((I.comap f).support : Set ↥X) = (fun x : ↥X => f x) ⁻¹' (I.support : Set ↥Y) := by
  rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap I f]
  rfl


end

namespace NonzeroOnComponents

section
variable {X Y : Scheme.{u}} {I : Y.IdealSheafData} (hI : NonzeroOnComponents I) (f : X ⟶ Y)
include hI

theorem comap_of_generalizingMap (hf : GeneralizingMap (fun x : ↥X => f x)) :
    NonzeroOnComponents (I.comap f) := by
  intro T hT hsub
  have hsub' : closure ((fun x : ↥X => f x) '' T) ⊆ (I.support : Set ↥Y) := by
    refine closure_minimal ?_ I.support.2
    rintro _ ⟨x, hxT, rfl⟩
    have hx : x ∈ ((I.comap f).support : Set ↥X) := hsub hxT
    rw [support_comap f I] at hx
    exact hx
  exact hI _ (closure_image_mem_irreducibleComponents_of_generalizingMap f hf hT) hsub'

theorem comap_of_flat [Flat f] :
    NonzeroOnComponents (I.comap f) :=
  hI.comap_of_generalizingMap f (generalizingMap_of_flat_consolidated64 f)

theorem comap_of_isOpenImmersion [IsOpenImmersion f] :
    NonzeroOnComponents (I.comap f) :=
  hI.comap_of_generalizingMap f f.isOpenEmbedding.generalizingMap


end

end NonzeroOnComponents

theorem closure_image_mem_irreducibleComponents_of_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {C : Set ↥X} (hC : C ∈ irreducibleComponents ↥X) :
    closure ((fun x : ↥X => f x) '' C) ∈ irreducibleComponents ↥Y :=
  closure_image_mem_irreducibleComponents_of_generalizingMap f (generalizingMap_of_flat_consolidated64 f) hC

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.OpenRestriction
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

namespace OpenImmersionRestriction

section
variable {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] (D : W.IdealSheafData)

private theorem exists_subschemeMap_isOpenImmersion_consolidated146 :
    ∃ g : (D.comap f).subscheme ⟶ D.subscheme,
      IsOpenImmersion g ∧ g ≫ D.subschemeι = (D.comap f).subschemeι ≫ f := by
  have h₁ : IsOpenImmersion (Limits.pullback.snd f D.subschemeι) := inferInstance
  have h₂ : IsOpenImmersion (D.comapIso f).hom := inferInstance
  refine ⟨(D.comapIso f).hom ≫ Limits.pullback.snd f D.subschemeι, inferInstance, ?_⟩
  rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]

theorem isOpenImmersion_subschemeMap (g : (D.comap f).subscheme ⟶ D.subscheme)
    (hg : g ≫ D.subschemeι = (D.comap f).subschemeι ≫ f) :
    IsOpenImmersion g := by
  obtain ⟨g', hg', hg'fac⟩ := exists_subschemeMap_isOpenImmersion_consolidated146 f D
  have : Mono D.subschemeι := inferInstance
  have heq : g = g' := by
    refine (cancel_mono D.subschemeι).mp ?_
    rw [hg, hg'fac]
  rw [heq]
  exact hg'


end

theorem isSmoothDivisor_comap {V W : Scheme.{u}} {k : Type u} [Field k]
    (f : V ⟶ W) [IsOpenImmersion f] (p : W ⟶ Spec (CommRingCat.of k))
    (D : W.IdealSheafData) (hD : IsSmoothDivisor p D) :
    IsSmoothDivisor (f ≫ p) (D.comap f) := by
  obtain ⟨g, hg, hgfac⟩ := exists_subschemeMap_isOpenImmersion_consolidated146 f D
  refine ⟨hD.1.comap_of_isOpenImmersion f, ?_⟩
  have : IsOpenImmersion g := hg
  have : Smooth g := inferInstance
  have hsm : Smooth (D.subschemeι ≫ p) := hD.2
  have hcomp : (D.comap f).subschemeι ≫ f ≫ p = g ≫ D.subschemeι ≫ p := by
    rw [← Category.assoc, ← hgfac, Category.assoc]
  rw [hcomp]
  infer_instance

end OpenImmersionRestriction

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IdealSheafFlatDescent
section

open CategoryTheory Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

section
variable {X Y : Scheme.{u}}

private theorem map_eq_ker_consolidated108 (I : X.IdealSheafData) (f : X ⟶ Y) :
    I.map f = (I.subschemeι ≫ f).ker := rfl

private theorem comap_eq_ker_pullback_fst_consolidated108 (I : Y.IdealSheafData) (f : X ⟶ Y) :
    I.comap f = (pullback.fst f I.subschemeι).ker := rfl


end

theorem comap_map_eq_map_comap_of_isPullback {W X X' W' : Scheme.{u}} {f : W ⟶ X} {g : X' ⟶ X}
    {g' : W' ⟶ W} {f' : W' ⟶ X'} (H : IsPullback g' f' f g)
    [QuasiCompact f] [Flat g] (I : W.IdealSheafData) :
    (I.map f).comap g = (I.comap g').map f' := by
  have hqc : QuasiCompact (I.subschemeι ≫ f) := inferInstance
  have S : IsPullback (pullback.snd g' I.subschemeι) (pullback.fst g' I.subschemeι ≫ f')
      (I.subschemeι ≫ f) g := (IsPullback.of_hasPullback g' I.subschemeι).flip.paste_vert H
  have hqc' : QuasiCompact (pullback.fst g' I.subschemeι ≫ f') := quasiCompact_of_isPullback S
  have h1 := ker_eq_comap_ker_of_isPullback_of_flat S
  rw [map_eq_ker_consolidated108, ← h1, Scheme.Hom.ker_comp, comap_eq_ker_pullback_fst_consolidated108]

theorem comap_map_eq_self_of_isPullback {W X Q : Scheme.{u}} (γ : W ⟶ X)
    [QuasiCompact γ] [Flat γ] {p q : Q ⟶ W} (H : IsPullback p q γ γ)
    (I : W.IdealSheafData) (hI : I.comap p = I.comap q) :
    (I.map γ).comap γ = I := by
  have key := comap_map_eq_map_comap_of_isPullback H I
  rw [hI] at key
  rw [key]
  obtain ⟨s, hsq⟩ : ∃ s : W ⟶ Q, s ≫ q = 𝟙 W :=
    ⟨H.lift (𝟙 W) (𝟙 W) rfl, H.lift_snd _ _ _⟩
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_map_comap I q)
  have h1 := Scheme.IdealSheafData.comap_map_le (I.comap q) q
  have h2 : (((I.comap q).map q).comap q).comap s ≤ ((I.comap q).comap s) :=
    Scheme.IdealSheafData.comap_mono s h1
  rwa [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hsq,
    Scheme.IdealSheafData.comap_id, Scheme.IdealSheafData.comap_id] at h2

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothAffinePullbackPresentation
section

open CategoryTheory AlgebraicGeometry

section
namespace FunctorialResolution.EmbeddedResolution

namespace PresentedSmoothChart

theorem smooth_specMap_comp_isoSpec_inv {A : Scheme.{u}} [IsAffine A]
    {B' : CommRingCat.{u}} (σ : Γ(A, ⊤) ⟶ B')
    (hσ : RingHom.IsStandardSmooth (CommRingCat.Hom.hom σ)) :
    Smooth (Spec.map σ ≫ A.isoSpec.inv) := by
  have hs : RingHom.Smooth (CommRingCat.Hom.hom σ) := by
    let := (CommRingCat.Hom.hom σ).toAlgebra
    have : Algebra.IsStandardSmooth ↥Γ(A, ⊤) ↥B' := hσ
    exact ⟨inferInstance, inferInstance⟩
  have h1 : Smooth (Spec.map σ) :=
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @Smooth)).mpr hs
  have h2 : Smooth A.isoSpec.inv := inferInstance
  exact MorphismProperty.comp_mem (@Smooth) _ _ h1 h2

theorem exists_affineOpen_isPullback_specMap {A X Y : Scheme.{u}}
    [IsAffine A] [IsAffine X]
    (i : X ⟶ A) [IsClosedImmersion i] (r : ℕ) (h : Y ⟶ X)
    [SmoothOfRelativeDimension r h] (y : ↥Y) :
    ∃ (V : Y.Opens) (_ : y ∈ V) (_ : IsAffineOpen V) (B' : CommRingCat.{u})
      (σ : Γ(A, ⊤) ⟶ B') (j : (V : Scheme.{u}) ⟶ Spec B'),
      RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom σ) ∧
        IsClosedImmersion j ∧
        CategoryTheory.IsPullback j (V.ι ≫ h) (Spec.map σ ≫ A.isoSpec.inv) i := by
  obtain ⟨V, hyV, hV, hsm⟩ :=
    SmoothChartRelativeDimension.exists_affineOpen_isStandardSmoothOfRelativeDimension r h y
  have : IsAffine (V : Scheme.{u}) := hV
  obtain ⟨B', σ, ψ, hσ, hψ, hpo⟩ :=
    SmoothChartRelativeDimension.exists_lift_isPushout_of_isStandardSmoothOfRelativeDimension
      (Scheme.Hom.appTop i)
      (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine i).2
      (Scheme.Hom.appTop (V.ι ≫ h)) r hsm
  have S1 : CategoryTheory.IsPullback (Spec.map ψ)
      (Spec.map (Scheme.Hom.appTop (V.ι ≫ h))) (Spec.map σ)
      (Spec.map (Scheme.Hom.appTop i)) := hpo.op.map Scheme.Spec
  have L : CategoryTheory.IsPullback (V : Scheme.{u}).isoSpec.hom (V.ι ≫ h)
      (Spec.map (Scheme.Hom.appTop (V.ι ≫ h))) X.isoSpec.hom :=
    CategoryTheory.IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality (V.ι ≫ h)⟩
  have C1 := L.paste_horiz S1
  rw [Scheme.isoSpec_hom_naturality i] at C1
  refine ⟨V, hyV, hV, B', σ, (V : Scheme.{u}).isoSpec.hom ≫ Spec.map ψ, hσ, ?_, ?_⟩
  · have := AlgebraicGeometry.IsClosedImmersion.spec_of_surjective ψ hψ
    infer_instance
  · have t : CategoryTheory.IsPullback (𝟙 (Spec B')) (Spec.map σ ≫ A.isoSpec.inv)
        (Spec.map σ) A.isoSpec.hom :=
      CategoryTheory.IsPullback.of_horiz_isIso ⟨by simp⟩
    have p : ((V : Scheme.{u}).isoSpec.hom ≫ Spec.map ψ) ≫ (Spec.map σ ≫ A.isoSpec.inv)
        = (V.ι ≫ h) ≫ i := by
      rw [← Category.assoc, C1.w]
      simp
    have s : CategoryTheory.IsPullback
        (((V : Scheme.{u}).isoSpec.hom ≫ Spec.map ψ) ≫ 𝟙 (Spec B')) (V.ι ≫ h)
        (Spec.map σ) (i ≫ A.isoSpec.hom) := by
      rw [Category.comp_id]
      exact C1
    exact CategoryTheory.IsPullback.of_right s p t

end PresentedSmoothChart

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothPullbackLocalAmbientEmbedding
section

open CategoryTheory AlgebraicGeometry

section
namespace FunctorialResolution.EmbeddedResolution

def SmoothPullbackHasLocalAmbientEmbedding : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X Y A : Scheme.{u})
    (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of k))
    (pA : A ⟶ Spec (CommRingCat.of k)) [IsAffine A] [Smooth pA]
    [LocallyOfFiniteType pA] [QuasiCompact pA]
    (i : X ⟶ A) [IsClosedImmersion i], i ≫ pA = pX →
    ∀ (M c : ℕ) (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) [IsClosedImmersion ρ],
      ρ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) = pA →
      HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))) ρ c →
    ∀ (r : ℕ) (h : Y ⟶ X) [SmoothOfRelativeDimension r h], h ≫ pX = pY →
    ∀ y : Y,
      ∃ (V : Y.Opens) (_ : y ∈ V) (_ : IsAffineOpen V)
        (A' : Scheme.{u}) (pA' : A' ⟶ Spec (CommRingCat.of k)),
        IsAffine A' ∧ Smooth pA' ∧ LocallyOfFiniteType pA' ∧ QuasiCompact pA' ∧
        ∃ g : A' ⟶ A, Smooth g ∧ g ≫ pA = pA' ∧
          ∃ j : V.toScheme ⟶ A', IsClosedImmersion j ∧
            IsPullback j (V.ι ≫ h) g i ∧
            ∃ N₀ : ℕ, r ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
              ∃ σ : A' ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin (M + N))),
                IsClosedImmersion σ ∧
                σ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin (M + N))) = pA' ∧
                HasSmoothCoordCodim
                  (affineSpaceIndexedByToSpec k (ULift.{u} (Fin (M + N)))) σ (c + (N - r))

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.VanishingIdealOfComponents
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

variable {α : Type*} [TopologicalSpace α]

private theorem radical_ringHom_ker_eq_consolidated109 {R S : Type*} [CommRing R] [CommRing S] [_root_.IsReduced S]
    (φ : R →+* S) : (RingHom.ker φ).radical = RingHom.ker φ := by
  refine le_antisymm ?_ Ideal.le_radical
  rintro x ⟨n, hn⟩
  rw [RingHom.mem_ker] at hn ⊢
  have hx : φ x ^ n = 0 := by rw [← map_pow]; exact hn
  exact IsNilpotent.eq_zero ⟨n, hx⟩

theorem isClosed_sUnion_irreducibleComponents [NoetherianSpace α]
    {S : Set (Set α)} (hS : S ⊆ irreducibleComponents α) :
    IsClosed (⋃₀ S) := by
  have hfin : S.Finite :=
    Set.Finite.subset (by apply NoetherianSpace.finite_irreducibleComponents) hS
  rw [Set.sUnion_eq_biUnion]
  refine hfin.isClosed_biUnion ?_
  intro s hs
  apply isClosed_of_mem_irreducibleComponents
  exact hS hs

theorem isOpen_compl_sUnion_irreducibleComponents_sdiff [NoetherianSpace α]
    (S : Set (Set α)) :
    IsOpen ((⋃₀ (irreducibleComponents α \ S))ᶜ) :=
  (isClosed_sUnion_irreducibleComponents Set.sdiff_subset).isOpen_compl

theorem compl_sUnion_irreducibleComponents_sdiff_subset (S : Set (Set α)) :
    (⋃₀ (irreducibleComponents α \ S))ᶜ ⊆ ⋃₀ S := by
  intro x hx
  rw [Set.mem_compl_iff] at hx
  have hmem : x ∈ irreducibleComponent x := by apply mem_irreducibleComponent
  have hcomp : irreducibleComponent x ∈ irreducibleComponents α := by
    apply irreducibleComponent_mem_irreducibleComponents
  by_cases hC : irreducibleComponent x ∈ S
  · exact ⟨irreducibleComponent x, hC, hmem⟩
  · exact (hx ⟨irreducibleComponent x, ⟨hcomp, hC⟩, hmem⟩).elim

theorem closure_compl_sUnion_irreducibleComponents_sdiff [NoetherianSpace α]
    {S : Set (Set α)} (hS : S ⊆ irreducibleComponents α) :
    closure ((⋃₀ (irreducibleComponents α \ S))ᶜ) = ⋃₀ S := by
  have hZcl : IsClosed (⋃₀ (irreducibleComponents α \ S)) :=
    isClosed_sUnion_irreducibleComponents Set.sdiff_subset
  apply Set.Subset.antisymm
  · exact closure_minimal (compl_sUnion_irreducibleComponents_sdiff_subset S)
      (isClosed_sUnion_irreducibleComponents hS)
  · rintro x ⟨C, hCS, hxC⟩
    have hCcomp : C ∈ irreducibleComponents α := hS hCS
    have hCirr : IsIrreducible C := hCcomp.1
    have hnot : ¬ C ⊆ ⋃₀ (irreducibleComponents α \ S) := by
      intro hsub
      have hfin : (irreducibleComponents α \ S).Finite :=
        Set.Finite.subset (by apply NoetherianSpace.finite_irreducibleComponents)
          Set.sdiff_subset
      obtain ⟨D, hD, hCsubD⟩ := isIrreducible_iff_sUnion_isClosed.mp hCirr hfin.toFinset
        (fun z hz => isClosed_of_mem_irreducibleComponents z (hfin.mem_toFinset.mp hz).1)
        (by rwa [hfin.coe_toFinset])
      have hD' : D ∈ irreducibleComponents α \ S := hfin.mem_toFinset.mp hD
      have hDsubC : D ⊆ C := hCcomp.2 hD'.1.1 hCsubD
      exact hD'.2 (by rw [Set.Subset.antisymm hDsubC hCsubD]; exact hCS)
    obtain ⟨y, hyC, hyZ⟩ := Set.not_subset.mp hnot
    rw [mem_closure_iff]
    intro o ho hxo
    obtain ⟨z, hz, hzo, hzZ⟩ := hCirr.2 o (⋃₀ (irreducibleComponents α \ S))ᶜ ho
      hZcl.isOpen_compl ⟨x, hxC, hxo⟩ ⟨y, hyC, hyZ⟩
    exact ⟨z, hzo, hzZ⟩

theorem vanishingIdeal_congr {X : Scheme.{u}} {Z₁ Z₂ : Closeds ↥X}
    (h : (Z₁ : Set ↥X) = (Z₂ : Set ↥X)) :
    Scheme.IdealSheafData.vanishingIdeal Z₁ = Scheme.IdealSheafData.vanishingIdeal Z₂ := by
  have hZ : Z₁ = Z₂ := SetLike.coe_injective h
  rw [hZ]

def complSUnionOtherComponents (X : Scheme.{u}) [NoetherianSpace ↥X] (S : Set (Set ↥X)) : X.Opens :=
  ⟨(⋃₀ (irreducibleComponents ↥X \ S))ᶜ,
    isOpen_compl_sUnion_irreducibleComponents_sdiff S⟩

@[simp]
theorem coe_complSUnionOtherComponents (X : Scheme.{u}) [NoetherianSpace ↥X] (S : Set (Set ↥X)) :
    (complSUnionOtherComponents X S : Set ↥X) = (⋃₀ (irreducibleComponents ↥X \ S))ᶜ :=
  rfl

section
variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsReduced X]

private theorem radical_scheme_ker_eq_consolidated109 :
    (Scheme.Hom.ker g).radical = Scheme.Hom.ker g := by
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_radical _)
  show (Scheme.Hom.ker g).radical ≤
    Scheme.IdealSheafData.ofIdeals fun U => RingHom.ker (CommRingCat.Hom.hom (g.app U.1))
  refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr ?_
  intro U
  have := AlgebraicGeometry.IsReduced.component_reduced (X := X) (g ⁻¹ᵁ U.1)
  have hle : (Scheme.Hom.ker g).ideal U ≤ RingHom.ker (CommRingCat.Hom.hom (g.app U.1)) := by
    unfold AlgebraicGeometry.Scheme.Hom.ker
    exact Scheme.IdealSheafData.ideal_ofIdeals_le _ U
  rw [Scheme.IdealSheafData.radical_ideal]
  calc ((Scheme.Hom.ker g).ideal U).radical
      ≤ (RingHom.ker (CommRingCat.Hom.hom (g.app U.1))).radical := Ideal.radical_mono hle
    _ = RingHom.ker (CommRingCat.Hom.hom (g.app U.1)) := radical_ringHom_ker_eq_consolidated109 _

private theorem ker_eq_vanishingIdeal_of_support_consolidated109 {Z : Closeds ↥Y}
    (hZ : ((Scheme.Hom.ker g).support : Set ↥Y) = (Z : Set ↥Y)) :
    Scheme.Hom.ker g = Scheme.IdealSheafData.vanishingIdeal Z := by
  rw [← vanishingIdeal_congr hZ, Scheme.IdealSheafData.vanishingIdeal_support,
    radical_scheme_ker_eq_consolidated109 g]


end

theorem comap_vanishingIdeal_sUnion {X X' : Scheme.{u}} (f : X' ⟶ X)
    [IsReduced X] [IsReduced X']
    [NoetherianSpace ↥X] [NoetherianSpace ↥X'] [Flat f]
    {S : Set (Set ↥X)} (hS : S ⊆ irreducibleComponents ↥X)
    {Z : Closeds ↥X} (hZ : (Z : Set ↥X) = ⋃₀ S)
    {Z' : Closeds ↥X'} (hZ' : (Z' : Set ↥X') = f.base ⁻¹' (⋃₀ S)) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap f =
      Scheme.IdealSheafData.vanishingIdeal Z' := by
  have hq1 : QuasiCompact (complSUnionOtherComponents X S).ι :=
    ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hq2 : QuasiCompact (f ⁻¹ᵁ complSUnionOtherComponents X S).ι :=
    ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hclU : closure ((complSUnionOtherComponents X S : X.Opens) : Set ↥X) = (Z : Set ↥X) := by
    rw [coe_complSUnionOtherComponents, hZ]
    exact closure_compl_sUnion_irreducibleComponents_sdiff hS
  have h1 : (complSUnionOtherComponents X S).ι.ker = Scheme.IdealSheafData.vanishingIdeal Z := by
    apply ker_eq_vanishingIdeal_of_support_consolidated109
    rw [Scheme.Hom.support_ker, ← hclU]
    congr 1
    exact Scheme.Opens.range_ι _
  have hclU' :
      closure ((f ⁻¹ᵁ complSUnionOtherComponents X S : X'.Opens) : Set ↥X') = (Z' : Set ↥X') := by
    have hcl : IsClosed (⇑f.base ⁻¹' (⋃₀ S)) := by
      rw [← hZ']; exact Z'.2
    rw [hZ']
    show closure (⇑f.base ⁻¹' ((⋃₀ (irreducibleComponents ↥X \ S))ᶜ))
        = ⇑f.base ⁻¹' (⋃₀ S)
    apply Set.Subset.antisymm
    · exact closure_minimal
        (Set.preimage_mono (compl_sUnion_irreducibleComponents_sdiff_subset S)) hcl
    · intro x' hx'
      have hx'' : f.base x' ∈ ⋃₀ S := hx'
      obtain ⟨C, hCS, hfx⟩ := hx''
      have hCcomp : C ∈ irreducibleComponents ↥X := hS hCS
      obtain ⟨η, hη⟩ :=
        QuasiSober.sober hCcomp.1 (isClosed_of_mem_irreducibleComponents C hCcomp)
      have hηU : η ∈ (⋃₀ (irreducibleComponents ↥X \ S))ᶜ := by
        rintro ⟨D, ⟨hDcomp, hDS⟩, hηD⟩
        have hCsubD : C ⊆ D := by
          rw [← hη]
          exact (isClosed_of_mem_irreducibleComponents D hDcomp).closure_subset_iff.mpr
            (Set.singleton_subset_iff.mpr hηD)
        have hDsubC : D ⊆ C := hCcomp.2 hDcomp.1 hCsubD
        exact hDS (Set.Subset.antisymm hCsubD hDsubC ▸ hCS)
      have hspec : η ⤳ f.base x' := by
        rw [specializes_iff_mem_closure, hη]
        exact hfx
      obtain ⟨y', hy'spec, hy'eq⟩ := AlgebraicGeometry.Flat.generalizingMap f hspec
      have hy'mem : f.base y' ∈ ((⋃₀ (irreducibleComponents ↥X \ S))ᶜ) := by
        rw [hy'eq]; exact hηU
      have hy'mem2 : y' ∈ (⇑f.base ⁻¹' ((⋃₀ (irreducibleComponents ↥X \ S))ᶜ)) := hy'mem
      exact closure_mono (Set.singleton_subset_iff.mpr hy'mem2)
        (specializes_iff_mem_closure.mp hy'spec)
  have h2 : (f ⁻¹ᵁ complSUnionOtherComponents X S).ι.ker = Scheme.IdealSheafData.vanishingIdeal Z' := by
    apply ker_eq_vanishingIdeal_of_support_consolidated109
    rw [Scheme.Hom.support_ker, ← hclU']
    congr 1
    exact Scheme.Opens.range_ι _
  have hpb := isPullback_morphismRestrict f (complSUnionOtherComponents X S)
  have h4 := ker_eq_comap_ker_of_isPullback_of_flat hpb
  rw [← h1, ← h2, h4]

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

mutual

inductive PrincipalizationCertificate {k : Type u} [Field k] :
    ∀ (W : Scheme.{u}), (W ⟶ Spec (CommRingCat.of k)) → W.IdealSheafData → ℕ →
      Set ↥W → W.IdealSheafData → Prop
  | memory {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (h : (Z.support : Set ↥W) ⊆ Mem) :
      PrincipalizationCertificate W p I m Mem Z
  | large {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (hm : 2 ≤ m) :
      PrincipalizationCertificate W p I m Mem Z
  | toOrder {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (M N : W.IdealSheafData) (μ : ℕ)
      (hI : I = M * N)
      (hM : (M.support : Set ↥W) ⊆ Mem)
      (hmu : m ≤ μ)
      (hZ : (Z.support : Set ↥W) ⊆ orderAtLeastLocus N μ)
      (hcert : OrderCertificate W p N μ Mem Z) :
      PrincipalizationCertificate W p I m Mem Z
  | localize {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
      (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
      (hcert : ∀ (z : ↥W) (hz : z ∈ Z.support),
        PrincipalizationCertificate (U z hz).toScheme ((U z hz).ι ≫ p) (I.comap (U z hz).ι) m
          ((U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)) :
      PrincipalizationCertificate W p I m Mem Z

inductive OrderCertificate {k : Type u} [Field k] :
    ∀ (W : Scheme.{u}), (W ⟶ Spec (CommRingCat.of k)) → W.IdealSheafData → ℕ →
      Set ↥W → W.IdealSheafData → Prop
  | memory {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (h : (Z.support : Set ↥W) ⊆ Mem) :
      OrderCertificate W p N μ Mem Z
  | large {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (hmu : 2 ≤ μ) :
      OrderCertificate W p N μ Mem Z
  | localize {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
      (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
      (hcert : ∀ (z : ↥W) (hz : z ∈ Z.support),
        OrderCertificate (U z hz).toScheme ((U z hz).ι ≫ p) (N.comap (U z hz).ι) μ
          ((U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)) :
      OrderCertificate W p N μ Mem Z
  | descend {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
      (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
      (H : ∀ (z : ↥W) (hz : z ∈ Z.support), (U z hz).toScheme.IdealSheafData)
      (hH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        IsSmoothDivisor ((U z hz).ι ≫ p) (H z hz))
      (hNsubH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        (((N.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
          ((H z hz).support : Set ↥(U z hz).toScheme))
      (hZH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
          ((H z hz).support : Set ↥(U z hz).toScheme))
      (J : ∀ (z : ↥W) (hz : z ∈ Z.support), Option ((H z hz).subscheme.IdealSheafData))
      (hJnone : ∀ (z : ↥W) (hz : z ∈ Z.support), J z hz = none →
        IsOpen ((H z hz).subschemeι.base ⁻¹'
          (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme))))
      (hJcomp : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = some Jz → NonzeroOnComponents Jz)
      (hJloc : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = some Jz →
        ∀ x : ↥(H z hz).subscheme,
          ((H z hz).subschemeι ≫ (U z hz).ι).base x ∉ Mem →
          ∃ V : (H z hz).subscheme.Opens, x ∈ V ∧
            Jz.comap V.ι =
              (((N.comap (U z hz).ι).comap (H z hz).subschemeι)).comap V.ι)
      (hJcert : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = some Jz →
        PrincipalizationCertificate (H z hz).subscheme ((H z hz).subschemeι ≫ (U z hz).ι ≫ p) Jz μ
          (((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
          ((Z.comap (U z hz).ι).comap (H z hz).subschemeι)) :
      OrderCertificate W p N μ Mem Z

end

section
variable {k : Type u} [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))

theorem PrincipalizationCertificate.of_two_le (I : W.IdealSheafData) (m : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) (hm : 2 ≤ m) :
    PrincipalizationCertificate W p I m Mem Z :=
  PrincipalizationCertificate.large hm

theorem OrderCertificate.of_two_le (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) (hmu : 2 ≤ μ) :
    OrderCertificate W p N μ Mem Z :=
  OrderCertificate.large hmu


end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.RestrictionToOpens
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

abbrev VanishingAssignment := ∀ X : Scheme.{u}, Closeds ↥X → X.IdealSheafData

structure IrreducibleClosedPair (W : Scheme.{u}) where
  S1 : Set ↥W
  S2 : Set ↥W
  xi1 : ↥W
  xi2 : ↥W
  pt : ↥W
  closed1 : IsClosed S1
  closed2 : IsClosed S2
  irred1 : IsIrreducible S1
  irred2 : IsIrreducible S2
  generic1 : IsGenericPoint xi1 S1
  generic2 : IsGenericPoint xi2 S2
  mem_first_closed : pt ∈ S1
  mem_second_closed : pt ∈ S2

def AgreeNear {W : Scheme.{u}} (I J : W.IdealSheafData) (x : ↥W) : Prop :=
  ∃ U : W.Opens, x ∈ U ∧ I.comap U.ι = J.comap U.ι

section
variable {W : Scheme.{u}}

theorem agreeNear_iff (I J : W.IdealSheafData) (x : ↥W) :
    AgreeNear I J x ↔ ∃ U : W.Opens, x ∈ U ∧ I.comap U.ι = J.comap U.ι := Iff.rfl

theorem agreeNear_symm {I J : W.IdealSheafData} {x : ↥W}
    (h : AgreeNear I J x) : AgreeNear J I x := by
  obtain ⟨U, hU, hEq⟩ := h
  exact ⟨U, hU, hEq.symm⟩


end

structure IdealSheafGeometryHypotheses (V : VanishingAssignment.{u}) : Prop where
  agreeNear_comap : ∀ (W : Scheme.{u}) (U : W.Opens) (I J : W.IdealSheafData)
      (y : ↥(U.toScheme)), AgreeNear I J (U.ι.base y) →
      AgreeNear (I.comap U.ι) (J.comap U.ι) y
  agreeNear_trans : ∀ (W : Scheme.{u}) (I J K : W.IdealSheafData) (x : ↥W),
      AgreeNear I J x → AgreeNear J K x → AgreeNear I K x
  comap_mul : ∀ (W X : Scheme.{u}) (f : X ⟶ W) (I J : W.IdealSheafData),
      (I * J).comap f = I.comap f * J.comap f
  base_comp : ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (x : ↥X),
      (f ≫ g).base x = g.base (f.base x)
  isClosed_support : ∀ (W : Scheme.{u}) (I : W.IdealSheafData),
      IsClosed (I.support : Set ↥W)
  isClosedEmbedding_subschemeι : ∀ (W : Scheme.{u}) (I : W.IdealSheafData),
      Topology.IsClosedEmbedding ⇑I.subschemeι.base
  isEmbedding_ι : ∀ (W : Scheme.{u}) (U : W.Opens), Topology.IsEmbedding ⇑U.ι.base
  isOpen_opens : ∀ (W : Scheme.{u}) (U : W.Opens), IsOpen (U : Set ↥W)
  orderAt_comap : ∀ (W : Scheme.{u}) (U : W.Opens) (I : W.IdealSheafData)
      (y : ↥(U.toScheme)), orderAt (I.comap U.ι) y = orderAt I (U.ι.base y)
  orderAt_congr : ∀ (W : Scheme.{u}) (I J : W.IdealSheafData) (x : ↥W),
      AgreeNear I J x → orderAt I x = orderAt J x
  orderAt_vanishing_eq_one : ∀ (k : Type u) [Field k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens) (D : (U.toScheme).IdealSheafData),
      IsSmoothDivisor (U.ι ≫ p) D →
      ∀ (T : Closeds ↥(D.subscheme)) (y : ↥(D.subscheme)),
        IsGenericPoint y (T : Set ↥(D.subscheme)) →
        (T : Set ↥(D.subscheme)) ∉ irreducibleComponents ↥(D.subscheme) →
        orderAt (V D.subscheme T) y = 1
  range_ι : ∀ (W : Scheme.{u}) (U : W.Opens), Set.range ⇑U.ι.base = (U : Set ↥W)
  range_subschemeι : ∀ (W : Scheme.{u}) (I : W.IdealSheafData),
      Set.range ⇑I.subschemeι.base = (I.support : Set ↥W)
  support_mul : ∀ (W : Scheme.{u}) (I J : W.IdealSheafData),
      ((I * J).support : Set ↥W) = (I.support : Set ↥W) ∪ (J.support : Set ↥W)
  not_subset_support_of_nonzeroOnComponents : ∀ (W : Scheme.{u}) (I : W.IdealSheafData),
      NonzeroOnComponents I →
      ∀ T ∈ irreducibleComponents ↥W, ¬ T ⊆ (I.support : Set ↥W)
  support_vanishing : ∀ (W : Scheme.{u}) (T : Closeds ↥W),
      ((V W T).support : Set ↥W) = (T : Set ↥W)
  top_mul : ∀ (W : Scheme.{u}) (I : W.IdealSheafData), (⊤ : W.IdealSheafData) * I = I
  agreeNear_vanishing_restrict : ∀ (W : Scheme.{u}) (I : W.IdealSheafData) (U : W.Opens)
      (D : (U.toScheme).IdealSheafData) (T : Closeds ↥W) (T' : Closeds ↥(D.subscheme))
      (y : ↥(D.subscheme)),
      (T' : Set ↥(D.subscheme)) = (D.subschemeι ≫ U.ι).base ⁻¹' (T : Set ↥W) →
      (U.ι.base ⁻¹' (T : Set ↥W)) ⊆ (D.support : Set ↥(U.toScheme)) →
      AgreeNear I (V W T) ((D.subschemeι ≫ U.ι).base y) →
      AgreeNear ((I.comap U.ι).comap D.subschemeι) (V D.subscheme T') y
  comap_vanishing : ∀ (W : Scheme.{u}) (T : Closeds ↥W) (U : W.Opens)
      (T' : Closeds ↥(U.toScheme)),
      (T' : Set ↥(U.toScheme)) = U.ι.base ⁻¹' (T : Set ↥W) →
      (V W T).comap U.ι = V U.toScheme T'

theorem mem_support_iff_of_agreeNear {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    {W : Scheme.{u}} {I J : W.IdealSheafData} {x : ↥W} (h : AgreeNear I J x) :
    x ∈ (I.support : Set ↥W) ↔ x ∈ (J.support : Set ↥W) := by
  have h1 := hV.orderAt_congr W I J x h
  constructor
  · intro hx
    have hx' : (1 : ℕ∞) ≤ orderAt I x := (one_le_orderAt_iff_mem_support I x).2 hx
    refine (one_le_orderAt_iff_mem_support J x).1 ?_
    rw [← h1]
    exact hx'
  · intro hx
    have hx' : (1 : ℕ∞) ≤ orderAt J x := (one_le_orderAt_iff_mem_support J x).2 hx
    refine (one_le_orderAt_iff_mem_support I x).1 ?_
    rw [h1]
    exact hx'

def OrderOneCentersIsolated (V : VanishingAssignment.{u}) {k : Type u} [Field k] (W : Scheme.{u})
    (_p : W ⟶ Spec (CommRingCat.of k)) (I : W.IdealSheafData) (m : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) : Prop :=
  ∀ C : IrreducibleClosedPair W, m = 1 → C.S1 ⊆ (Z.support : Set ↥W) →
    C.xi2 ∉ (Z.support : Set ↥W) → C.xi1 ∉ Mem → C.xi2 ∉ Mem →
    AgreeNear I (V W ⟨C.S1, C.closed1⟩) C.xi1 → orderAt I C.xi1 = 1 →
    C.xi2 ∈ (I.support : Set ↥W) → False

section
variable {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V) (W : Scheme.{u}) (U : W.Opens) (D : (U.toScheme).IdealSheafData)
include hV

theorem isInducing_subschemeι_comp_ι :
    Topology.IsInducing ⇑(D.subschemeι ≫ U.ι).base := by
  have h1 : Topology.IsInducing ⇑D.subschemeι.base :=
    (hV.isClosedEmbedding_subschemeι U.toScheme D).toIsEmbedding.toIsInducing
  have h2 : Topology.IsInducing ⇑U.ι.base := (hV.isEmbedding_ι W U).toIsInducing
  have hfun : ⇑(D.subschemeι ≫ U.ι).base = ⇑U.ι.base ∘ ⇑D.subschemeι.base := by
    funext y
    exact hV.base_comp _ _ _ D.subschemeι U.ι y
  rw [hfun]
  exact h2.comp h1

theorem isGenericPoint_preimage_subschemeι_comp_ι (T : Set ↥W)
    (ξ : ↥W) (hξ : IsGenericPoint ξ T) (y : ↥(D.subscheme))
    (hy : (D.subschemeι ≫ U.ι).base y = ξ) :
    IsGenericPoint y ((D.subschemeι ≫ U.ι).base ⁻¹' T) :=
  isGenericPoint_preimage_of_isInducing (isInducing_subschemeι_comp_ι hV W U D) hξ hy

theorem isClosed_preimage_subschemeι_comp_ι (T : Set ↥W)
    (hT : IsClosed T) :
    IsClosed ((D.subschemeι ≫ U.ι).base ⁻¹' T) :=
  hT.preimage (isInducing_subschemeι_comp_ι hV W U D).continuous

theorem exists_subschemeι_comp_ι_apply_eq_of_mem (T : Set ↥W)
    (hT : U.ι.base ⁻¹' T ⊆ (D.support : Set ↥(U.toScheme)))
    (x : ↥W) (hxU : x ∈ (U : Set ↥W)) (hxT : x ∈ T) :
    ∃ y : ↥(D.subscheme), (D.subschemeι ≫ U.ι).base y = x := by
  have hx : x ∈ Set.range ⇑U.ι.base := by
    rw [hV.range_ι W U]
    exact hxU
  obtain ⟨y₀, hy₀⟩ := hx
  have hy₀T : y₀ ∈ (D.support : Set ↥(U.toScheme)) := by
    refine hT ?_
    have h' : U.ι.base y₀ ∈ T := by
      rw [hy₀]
      exact hxT
    exact h'
  have hy₀r : y₀ ∈ Set.range ⇑D.subschemeι.base := by
    rw [hV.range_subschemeι U.toScheme D]
    exact hy₀T
  obtain ⟨y, hy⟩ := hy₀r
  refine ⟨y, ?_⟩
  rw [hV.base_comp _ _ _ D.subschemeι U.ι y, hy, hy₀]


end

theorem false_of_isOpen_preimage_support {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (W : Scheme.{u}) (N Z : W.IdealSheafData) (C : IrreducibleClosedPair W) (U : W.Opens)
    (H : (U.toScheme).IdealSheafData)
    (hptU : C.pt ∈ (U : Set ↥W)) (hptZ : C.pt ∈ (Z.support : Set ↥W))
    (hZH : ((Z.comap U.ι).support : Set ↥(U.toScheme)) ⊆ (H.support : Set ↥(U.toScheme)))
    (hNsubH : ((N.comap U.ι).support : Set ↥(U.toScheme)) ⊆ (H.support : Set ↥(U.toScheme)))
    (hopen : IsOpen (H.subschemeι.base ⁻¹' ((Z.comap U.ι).support : Set ↥(U.toScheme))))
    (hxi2Z : C.xi2 ∉ (Z.support : Set ↥W))
    (hxi2N : C.xi2 ∈ (N.support : Set ↥W)) : False := by
  have hopenU : IsOpen ((U : Set ↥W)) := hV.isOpen_opens W U
  have hxi2U : C.xi2 ∈ (U : Set ↥W) :=
    (C.generic2.mem_open_set_iff hopenU).mpr ⟨C.pt, C.mem_second_closed, hptU⟩
  have hZsub : ⇑U.ι.base ⁻¹' (Z.support : Set ↥W) ⊆ (H.support : Set ↥(U.toScheme)) := by
    rw [← support_comap_eq]
    exact hZH
  have hNsub : ⇑U.ι.base ⁻¹' (N.support : Set ↥W) ⊆ (H.support : Set ↥(U.toScheme)) := by
    rw [← support_comap_eq]
    exact hNsubH
  obtain ⟨y0, hy0⟩ := exists_subschemeι_comp_ι_apply_eq_of_mem hV W U H (Z.support : Set ↥W) hZsub C.pt hptU hptZ
  obtain ⟨y2, hy2⟩ := exists_subschemeι_comp_ι_apply_eq_of_mem hV W U H (N.support : Set ↥W) hNsub C.xi2 hxi2U hxi2N
  have hgen2 : IsGenericPoint y2 ((H.subschemeι ≫ U.ι).base ⁻¹' C.S2) :=
    isGenericPoint_preimage_subschemeι_comp_ι hV W U H C.S2 C.xi2 C.generic2 y2 hy2
  have hclosedA : IsClosed (⇑H.subschemeι.base ⁻¹'
      ((Z.comap U.ι).support : Set ↥(U.toScheme))) :=
    (hV.isClosed_support U.toScheme (Z.comap U.ι)).preimage
      (hV.isClosedEmbedding_subschemeι U.toScheme H).continuous
  have hA : IsClopen (⇑H.subschemeι.base ⁻¹'
      ((Z.comap U.ι).support : Set ↥(U.toScheme))) := ⟨hclosedA, hopen⟩
  have hirr : IsIrreducible ((H.subschemeι ≫ U.ι).base ⁻¹' C.S2) := by
    rw [← hgen2.def]
    exact isIrreducible_singleton.closure
  have hy0A : y0 ∈ ⇑H.subschemeι.base ⁻¹' ((Z.comap U.ι).support : Set ↥(U.toScheme)) := by
    rw [support_comap_eq]
    show U.ι.base (H.subschemeι.base y0) ∈ (Z.support : Set ↥W)
    rw [← hV.base_comp _ _ _ H.subschemeι U.ι y0, hy0]
    exact hptZ
  have hy0S : y0 ∈ (H.subschemeι ≫ U.ι).base ⁻¹' C.S2 := by
    show (H.subschemeι ≫ U.ι).base y0 ∈ C.S2
    rw [hy0]
    exact C.mem_second_closed
  have hsub := hirr.isPreirreducible.isPreconnected.subset_isClopen hA ⟨y0, hy0S, hy0A⟩
  have hy2A : y2 ∈ ⇑H.subschemeι.base ⁻¹' ((Z.comap U.ι).support : Set ↥(U.toScheme)) :=
    hsub hgen2.mem
  apply hxi2Z
  rw [support_comap_eq] at hy2A
  have h' : U.ι.base (H.subschemeι.base y2) ∈ (Z.support : Set ↥W) := hy2A
  rw [← hV.base_comp _ _ _ H.subschemeι U.ι y2, hy2] at h'
  exact h'

section
variable {V : VanishingAssignment.{u}} {k : Type u} [Field k] {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} (I : W.IdealSheafData) (m : ℕ) {Mem : Set ↥W} {Z : W.IdealSheafData}

private theorem orderOneCentersIsolated_of_support_subset_consolidated106 (h : (Z.support : Set ↥W) ⊆ Mem) :
    OrderOneCentersIsolated V W p I m Mem Z := by
  intro C _ hS1 _ hxi1M _ _ _ _
  exact hxi1M (h (hS1 C.generic1.mem))

private theorem orderOneCentersIsolated_of_two_le_consolidated106 (hm : 2 ≤ m) :
    OrderOneCentersIsolated V W p I m Mem Z := by
  intro _ hm1 _ _ _ _ _ _ _
  omega


end

section
variable {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V) {k : Type u} [Field k] {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
include hV

private theorem orderOneCentersIsolated_of_eq_mul_of_subset_orderAtLeastLocus_consolidated106 (M N : W.IdealSheafData) (μ : ℕ) (hI : I = M * N)
    (hM : (M.support : Set ↥W) ⊆ Mem) (hmu : m ≤ μ)
    (hZ : (Z.support : Set ↥W) ⊆ orderAtLeastLocus N μ)
    (ih : OrderOneCentersIsolated V W p N μ Mem Z) : OrderOneCentersIsolated V W p I m Mem Z := by
  intro C hm1 hS1 hxi2Z hxi1M hxi2M hagree hord hxi2I
  have hxi1S : C.xi1 ∈ C.S1 := C.generic1.mem
  have hM1 : C.xi1 ∉ (M.support : Set ↥W) := fun hh => hxi1M (hM hh)
  have hM2 : C.xi2 ∉ (M.support : Set ↥W) := fun hh => hxi2M (hM hh)
  obtain ⟨Uc, hUcmem, hUctop⟩ : ∃ Uc : W.Opens, C.xi1 ∈ Uc ∧ M.comap Uc.ι = ⊤ :=
    ⟨⟨(M.support : Set ↥W)ᶜ, (hV.isClosed_support W M).isOpen_compl⟩, hM1,
      comap_ι_eq_top_of_disjoint M _ disjoint_compl_left⟩
  have hAIN : AgreeNear I N C.xi1 :=
    ⟨Uc, hUcmem, by rw [hI, hV.comap_mul, hUctop, hV.top_mul]⟩
  have hAN : AgreeNear N (V W ⟨C.S1, C.closed1⟩) C.xi1 :=
    hV.agreeNear_trans W N I (V W ⟨C.S1, C.closed1⟩) C.xi1 (agreeNear_symm hAIN) hagree
  have hM0 : orderAt M C.xi1 = 0 := (orderAt_eq_zero_iff_not_mem_support M C.xi1).2 hM1
  have hle : orderAt N C.xi1 ≤ 1 := by
    have h2 := add_orderAt_le_orderAt_mul M N C.xi1
    rw [hM0, zero_add, ← hI, hord] at h2
    exact h2
  have hmu1 : (μ : ℕ∞) ≤ orderAt N C.xi1 := (mem_orderAtLeastLocus_iff N μ C.xi1).1 (hZ (hS1 hxi1S))
  have hμle : μ ≤ 1 := by exact_mod_cast le_trans hmu1 hle
  have hμ1 : μ = 1 := by omega
  have hordN : orderAt N C.xi1 = 1 := by
    refine le_antisymm hle ?_
    rw [hμ1] at hmu1
    exact_mod_cast hmu1
  have hxi2Nmem : C.xi2 ∈ (N.support : Set ↥W) := by
    rw [hI, hV.support_mul] at hxi2I
    rcases (Set.mem_union _ _ _).1 hxi2I with h' | h'
    · exact absurd h' hM2
    · exact h'
  exact ih C hμ1 hS1 hxi2Z hxi1M hxi2M hAN hordN hxi2Nmem

private theorem false_of_orderOneCentersIsolated_comap_opens_consolidated106 (U₀ : W.Opens) (C : IrreducibleClosedPair W) (hptU : C.pt ∈ (U₀ : Set ↥W))
    (key : OrderOneCentersIsolated V U₀.toScheme (U₀.ι ≫ p) (I.comap U₀.ι) m (⇑U₀.ι.base ⁻¹' Mem)
      (Z.comap U₀.ι))
    (hm1 : m = 1) (hS1 : C.S1 ⊆ (Z.support : Set ↥W)) (hxi2Z : C.xi2 ∉ (Z.support : Set ↥W))
    (hxi1M : C.xi1 ∉ Mem) (hxi2M : C.xi2 ∉ Mem)
    (hagree : AgreeNear I (V W ⟨C.S1, C.closed1⟩) C.xi1) (hord : orderAt I C.xi1 = 1)
    (hxi2I : C.xi2 ∈ (I.support : Set ↥W)) : False := by
  have hopenU : IsOpen ((U₀ : Set ↥W)) := hV.isOpen_opens W U₀
  have hxi1U : C.xi1 ∈ (U₀ : Set ↥W) :=
    (C.generic1.mem_open_set_iff hopenU).mpr ⟨C.pt, C.mem_first_closed, hptU⟩
  have hxi2U : C.xi2 ∈ (U₀ : Set ↥W) :=
    (C.generic2.mem_open_set_iff hopenU).mpr ⟨C.pt, C.mem_second_closed, hptU⟩
  have hrange : Set.range ⇑U₀.ι.base = (U₀ : Set ↥W) := hV.range_ι W U₀
  obtain ⟨x1, hx1⟩ : ∃ y, U₀.ι.base y = C.xi1 := by
    rw [← Set.mem_range, hrange]; exact hxi1U
  obtain ⟨x2, hx2⟩ : ∃ y, U₀.ι.base y = C.xi2 := by
    rw [← Set.mem_range, hrange]; exact hxi2U
  obtain ⟨x0, hx0⟩ : ∃ y, U₀.ι.base y = C.pt := by
    rw [← Set.mem_range, hrange]; exact hptU
  have hcont : Continuous ⇑U₀.ι.base := (hV.isEmbedding_ι W U₀).continuous
  have hg1 : IsGenericPoint x1 (⇑U₀.ι.base ⁻¹' C.S1) :=
    isGenericPoint_preimage_of_isInducing (hV.isEmbedding_ι W U₀).toIsInducing C.generic1 hx1
  have hg2 : IsGenericPoint x2 (⇑U₀.ι.base ⁻¹' C.S2) :=
    isGenericPoint_preimage_of_isInducing (hV.isEmbedding_ι W U₀).toIsInducing C.generic2 hx2
  refine key
    { S1 := ⇑U₀.ι.base ⁻¹' C.S1
      S2 := ⇑U₀.ι.base ⁻¹' C.S2
      xi1 := x1
      xi2 := x2
      pt := x0
      closed1 := C.closed1.preimage hcont
      closed2 := C.closed2.preimage hcont
      irred1 := by
        rw [← hg1.def]
        exact isIrreducible_singleton.closure
      irred2 := by
        rw [← hg2.def]
        exact isIrreducible_singleton.closure
      generic1 := hg1
      generic2 := hg2
      mem_first_closed := by
        show U₀.ι.base x0 ∈ C.S1
        rw [hx0]; exact C.mem_first_closed
      mem_second_closed := by
        show U₀.ι.base x0 ∈ C.S2
        rw [hx0]; exact C.mem_second_closed }
    hm1 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [support_comap_eq]
    exact Set.preimage_mono hS1
  · rw [support_comap_eq]
    intro hcon
    apply hxi2Z
    have h' : U₀.ι.base x2 ∈ (Z.support : Set ↥W) := hcon
    rwa [hx2] at h'
  · intro hcon
    apply hxi1M
    have h' : U₀.ι.base x1 ∈ Mem := hcon
    rwa [hx1] at h'
  · intro hcon
    apply hxi2M
    have h' : U₀.ι.base x2 ∈ Mem := hcon
    rwa [hx2] at h'
  · have h1 : AgreeNear I (V W ⟨C.S1, C.closed1⟩) (U₀.ι.base x1) := by
      rw [hx1]; exact hagree
    have h2 := hV.agreeNear_comap W U₀ I (V W ⟨C.S1, C.closed1⟩) x1 h1
    rw [hV.comap_vanishing W ⟨C.S1, C.closed1⟩ U₀
      ⟨⇑U₀.ι.base ⁻¹' C.S1, C.closed1.preimage hcont⟩ rfl] at h2
    exact h2
  · show orderAt (I.comap U₀.ι) x1 = 1
    rw [hV.orderAt_comap W U₀ I x1, hx1]
    exact hord
  · show x2 ∈ ((I.comap U₀.ι).support : Set ↥(U₀.toScheme))
    rw [support_comap_eq]
    show U₀.ι.base x2 ∈ (I.support : Set ↥W)
    rw [hx2]
    exact hxi2I

private theorem orderOneCentersIsolated_of_forall_opens_consolidated106 (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support),
      OrderOneCentersIsolated V (U z hz).toScheme ((U z hz).ι ≫ p) (I.comap (U z hz).ι) m
        (⇑(U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)) :
    OrderOneCentersIsolated V W p I m Mem Z := by
  intro C hm1 hS1 hxi2Z hxi1M hxi2M hagree hord hxi2I
  have hz : C.pt ∈ Z.support := hS1 C.mem_first_closed
  exact false_of_orderOneCentersIsolated_comap_opens_consolidated106 hV (U C.pt hz) C (hU C.pt hz) (ih C.pt hz) hm1 hS1 hxi2Z
    hxi1M hxi2M hagree hord hxi2I


end

section
variable {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V) {k : Type u} [Field k] {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
include hV

private theorem false_of_isSmoothDivisor_of_orderOneCentersIsolated_consolidated106 {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
    (C : IrreducibleClosedPair W) (U₀ : W.Opens) (H₀ : (U₀.toScheme).IdealSheafData)
    (Jz : (H₀.subscheme).IdealSheafData)
    (hptU : C.pt ∈ (U₀ : Set ↥W))
    (hH : IsSmoothDivisor (U₀.ι ≫ p) H₀)
    (hNsubH : ((N.comap U₀.ι).support : Set ↥(U₀.toScheme)) ⊆
      (H₀.support : Set ↥(U₀.toScheme)))
    (hZH : ((Z.comap U₀.ι).support : Set ↥(U₀.toScheme)) ⊆
      (H₀.support : Set ↥(U₀.toScheme)))
    (hcomp : NonzeroOnComponents Jz)
    (hloc : ∀ x : ↥(H₀.subscheme), (H₀.subschemeι ≫ U₀.ι).base x ∉ Mem →
      ∃ V' : (H₀.subscheme).Opens, x ∈ V' ∧
        Jz.comap V'.ι = ((N.comap U₀.ι).comap H₀.subschemeι).comap V'.ι)
    (key : OrderOneCentersIsolated V H₀.subscheme (H₀.subschemeι ≫ (U₀.ι ≫ p)) Jz μ
      (⇑(H₀.subschemeι ≫ U₀.ι).base ⁻¹' Mem) ((Z.comap U₀.ι).comap H₀.subschemeι))
    (hm1 : μ = 1) (hS1 : C.S1 ⊆ (Z.support : Set ↥W)) (hxi2Z : C.xi2 ∉ (Z.support : Set ↥W))
    (hxi1M : C.xi1 ∉ Mem) (hxi2M : C.xi2 ∉ Mem)
    (hagree : AgreeNear N (V W ⟨C.S1, C.closed1⟩) C.xi1) (_hord : orderAt N C.xi1 = 1)
    (hxi2N : C.xi2 ∈ (N.support : Set ↥W)) : False := by
  have hptZ : C.pt ∈ (Z.support : Set ↥W) := hS1 C.mem_first_closed
  have hopenU : IsOpen ((U₀ : Set ↥W)) := hV.isOpen_opens W U₀
  have hxi1U : C.xi1 ∈ (U₀ : Set ↥W) :=
    (C.generic1.mem_open_set_iff hopenU).mpr ⟨C.pt, C.mem_first_closed, hptU⟩
  have hxi2U : C.xi2 ∈ (U₀ : Set ↥W) :=
    (C.generic2.mem_open_set_iff hopenU).mpr ⟨C.pt, C.mem_second_closed, hptU⟩
  have hZsub : ⇑U₀.ι.base ⁻¹' (Z.support : Set ↥W) ⊆ (H₀.support : Set ↥(U₀.toScheme)) := by
    rw [← support_comap_eq]
    exact hZH
  have hNsub : ⇑U₀.ι.base ⁻¹' (N.support : Set ↥W) ⊆ (H₀.support : Set ↥(U₀.toScheme)) := by
    rw [← support_comap_eq]
    exact hNsubH
  obtain ⟨y1, hy1⟩ := exists_subschemeι_comp_ι_apply_eq_of_mem hV W U₀ H₀ (Z.support : Set ↥W) hZsub C.xi1 hxi1U
    (hS1 C.generic1.mem)
  obtain ⟨y0, hy0⟩ := exists_subschemeι_comp_ι_apply_eq_of_mem hV W U₀ H₀ (Z.support : Set ↥W) hZsub C.pt hptU hptZ
  obtain ⟨y2, hy2⟩ := exists_subschemeι_comp_ι_apply_eq_of_mem hV W U₀ H₀ (N.support : Set ↥W) hNsub C.xi2 hxi2U
    hxi2N
  have hgen1 : IsGenericPoint y1 ((H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1) :=
    isGenericPoint_preimage_subschemeι_comp_ι hV W U₀ H₀ C.S1 C.xi1 C.generic1 y1 hy1
  have hgen2 : IsGenericPoint y2 ((H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S2) :=
    isGenericPoint_preimage_subschemeι_comp_ι hV W U₀ H₀ C.S2 C.xi2 C.generic2 y2 hy2
  have hcl1 : IsClosed ((H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1) :=
    isClosed_preimage_subschemeι_comp_ι hV W U₀ H₀ C.S1 C.closed1
  have hcl2 : IsClosed ((H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S2) :=
    isClosed_preimage_subschemeι_comp_ι hV W U₀ H₀ C.S2 C.closed2
  have hA1 : AgreeNear Jz ((N.comap U₀.ι).comap H₀.subschemeι) y1 := by
    refine hloc y1 ?_
    rw [hy1]
    exact hxi1M
  have hA2 : AgreeNear ((N.comap U₀.ι).comap H₀.subschemeι)
      (V H₀.subscheme ⟨(H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1, hcl1⟩) y1 := by
    refine hV.agreeNear_vanishing_restrict W N U₀ H₀ ⟨C.S1, C.closed1⟩
      ⟨(H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1, hcl1⟩ y1 rfl ?_ ?_
    · exact fun a ha => hZsub (Set.preimage_mono hS1 ha)
    · rw [hy1]
      exact hagree
  have hA3 : AgreeNear Jz (V H₀.subscheme ⟨(H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1, hcl1⟩) y1 :=
    hV.agreeNear_trans H₀.subscheme Jz ((N.comap U₀.ι).comap H₀.subschemeι)
      (V H₀.subscheme ⟨(H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1, hcl1⟩) y1 hA1 hA2
  have hy1mem : y1 ∈ (Jz.support : Set ↥(H₀.subscheme)) := by
    refine (mem_support_iff_of_agreeNear hV hA3).2 ?_
    rw [hV.support_vanishing]
    exact hgen1.mem
  have hnotcomp : ((H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1) ∉
      irreducibleComponents ↥(H₀.subscheme) := by
    intro hmem
    refine hV.not_subset_support_of_nonzeroOnComponents H₀.subscheme Jz hcomp _ hmem ?_
    rw [← hgen1.def]
    exact (hV.isClosed_support H₀.subscheme Jz).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hy1mem)
  have hordV : orderAt (V H₀.subscheme ⟨(H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1, hcl1⟩) y1 = 1 :=
    hV.orderAt_vanishing_eq_one k W p U₀ H₀ hH
      ⟨(H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1, hcl1⟩ y1 hgen1 hnotcomp
  have hordJ : orderAt Jz y1 = 1 := by
    rw [hV.orderAt_congr H₀.subscheme Jz
      (V H₀.subscheme ⟨(H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1, hcl1⟩) y1 hA3]
    exact hordV
  have hA2' : AgreeNear Jz ((N.comap U₀.ι).comap H₀.subschemeι) y2 := by
    refine hloc y2 ?_
    rw [hy2]
    exact hxi2M
  have hy2mem : y2 ∈ (Jz.support : Set ↥(H₀.subscheme)) := by
    refine (mem_support_iff_of_agreeNear hV hA2').2 ?_
    rw [support_comap_eq, support_comap_eq]
    show U₀.ι.base (H₀.subschemeι.base y2) ∈ (N.support : Set ↥W)
    rw [← hV.base_comp _ _ _ H₀.subschemeι U₀.ι y2, hy2]
    exact hxi2N
  refine key
    { S1 := (H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1
      S2 := (H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S2
      xi1 := y1
      xi2 := y2
      pt := y0
      closed1 := hcl1
      closed2 := hcl2
      irred1 := by
        rw [← hgen1.def]
        exact isIrreducible_singleton.closure
      irred2 := by
        rw [← hgen2.def]
        exact isIrreducible_singleton.closure
      generic1 := hgen1
      generic2 := hgen2
      mem_first_closed := by
        show (H₀.subschemeι ≫ U₀.ι).base y0 ∈ C.S1
        rw [hy0]; exact C.mem_first_closed
      mem_second_closed := by
        show (H₀.subschemeι ≫ U₀.ι).base y0 ∈ C.S2
        rw [hy0]; exact C.mem_second_closed }
    hm1 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [support_comap_eq, support_comap_eq]
    intro a ha
    show U₀.ι.base (H₀.subschemeι.base a) ∈ (Z.support : Set ↥W)
    rw [← hV.base_comp _ _ _ H₀.subschemeι U₀.ι a]
    exact hS1 ha
  · rw [support_comap_eq, support_comap_eq]
    intro hcon
    apply hxi2Z
    have h' : U₀.ι.base (H₀.subschemeι.base y2) ∈ (Z.support : Set ↥W) := hcon
    rw [← hV.base_comp _ _ _ H₀.subschemeι U₀.ι y2, hy2] at h'
    exact h'
  · intro hcon
    apply hxi1M
    have h' : (H₀.subschemeι ≫ U₀.ι).base y1 ∈ Mem := hcon
    rwa [hy1] at h'
  · intro hcon
    apply hxi2M
    have h' : (H₀.subschemeι ≫ U₀.ι).base y2 ∈ Mem := hcon
    rwa [hy2] at h'
  · exact hA3
  · exact hordJ
  · exact hy2mem

private theorem orderOneCentersIsolated_of_isSmoothDivisor_consolidated106 {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
    (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (H : ∀ (z : ↥W) (hz : z ∈ Z.support), ((U z hz).toScheme).IdealSheafData)
    (hH : ∀ (z : ↥W) (hz : z ∈ Z.support), IsSmoothDivisor ((U z hz).ι ≫ p) (H z hz))
    (hNsubH : ∀ (z : ↥W) (hz : z ∈ Z.support),
      ((N.comap (U z hz).ι).support : Set ↥((U z hz).toScheme)) ⊆
        ((H z hz).support : Set ↥((U z hz).toScheme)))
    (hZH : ∀ (z : ↥W) (hz : z ∈ Z.support),
      ((Z.comap (U z hz).ι).support : Set ↥((U z hz).toScheme)) ⊆
        ((H z hz).support : Set ↥((U z hz).toScheme)))
    (J : ∀ (z : ↥W) (hz : z ∈ Z.support), Option (((H z hz)).subscheme).IdealSheafData)
    (hJnone : ∀ (z : ↥W) (hz : z ∈ Z.support), J z hz = none →
      IsOpen (⇑(H z hz).subschemeι.base ⁻¹'
        ((Z.comap (U z hz).ι).support : Set ↥((U z hz).toScheme))))
    (hJcomp : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : ((H z hz).subscheme).IdealSheafData),
      J z hz = some Jz → NonzeroOnComponents Jz)
    (hJloc : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : ((H z hz).subscheme).IdealSheafData),
      J z hz = some Jz → ∀ x : ↥((H z hz).subscheme),
        ((H z hz).subschemeι ≫ (U z hz).ι).base x ∉ Mem →
        ∃ V' : ((H z hz).subscheme).Opens, x ∈ V' ∧
          Jz.comap V'.ι = ((N.comap (U z hz).ι).comap (H z hz).subschemeι).comap V'.ι)
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : ((H z hz).subscheme).IdealSheafData),
      J z hz = some Jz →
      OrderOneCentersIsolated V ((H z hz).subscheme) ((H z hz).subschemeι ≫ ((U z hz).ι ≫ p)) Jz μ
        (⇑((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
        ((Z.comap (U z hz).ι).comap (H z hz).subschemeι)) :
    OrderOneCentersIsolated V W p N μ Mem Z := by
  intro C hm1 hS1 hxi2Z hxi1M hxi2M hagree hord hxi2N
  have hz : C.pt ∈ Z.support := hS1 C.mem_first_closed
  have hptZ : C.pt ∈ (Z.support : Set ↥W) := hS1 C.mem_first_closed
  rcases hJJ : J C.pt hz with _ | Jz
  · exact false_of_isOpen_preimage_support hV W N Z C (U C.pt hz) (H C.pt hz) (hU C.pt hz) hptZ
      (hZH C.pt hz) (hNsubH C.pt hz) (hJnone C.pt hz hJJ) hxi2Z hxi2N
  · exact false_of_isSmoothDivisor_of_orderOneCentersIsolated_consolidated106 hV C (U C.pt hz) (H C.pt hz) Jz (hU C.pt hz) (hH C.pt hz)
      (hNsubH C.pt hz) (hZH C.pt hz) (hJcomp C.pt hz Jz hJJ) (hJloc C.pt hz Jz hJJ)
      (ih C.pt hz Jz hJJ) hm1 hS1 hxi2Z hxi1M hxi2M hagree hord hxi2N

theorem orderOneCentersIsolated_of_principalizationCertificate {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
    (h : PrincipalizationCertificate W p I m Mem Z) : OrderOneCentersIsolated V W p I m Mem Z := by
  refine PrincipalizationCertificate.rec
    (motive_1 := fun W' p' I' m' Mem' Z' _ => OrderOneCentersIsolated V W' p' I' m' Mem' Z')
    (motive_2 := fun W' p' N' μ' Mem' Z' _ => OrderOneCentersIsolated V W' p' N' μ' Mem' Z')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro W' p' I' m' Mem' Z' hmem
    exact orderOneCentersIsolated_of_support_subset_consolidated106 I' m' hmem
  · intro W' p' I' m' Mem' Z' hm
    exact orderOneCentersIsolated_of_two_le_consolidated106 I' m' hm
  · intro W' p' I' m' Mem' Z' M' N' μ' hI' hM' hmu' hZ' hcert' ihc
    exact orderOneCentersIsolated_of_eq_mul_of_subset_orderAtLeastLocus_consolidated106 hV M' N' μ' hI' hM' hmu' hZ' ihc
  · intro W' p' I' m' Mem' Z' U' hU' hcert' ihc
    exact orderOneCentersIsolated_of_forall_opens_consolidated106 hV U' hU' ihc
  · intro W' p' N' μ' Mem' Z' hmem
    exact orderOneCentersIsolated_of_support_subset_consolidated106 N' μ' hmem
  · intro W' p' N' μ' Mem' Z' hmu
    exact orderOneCentersIsolated_of_two_le_consolidated106 N' μ' hmu
  · intro W' p' N' μ' Mem' Z' U' hU' hcert' ihc
    exact orderOneCentersIsolated_of_forall_opens_consolidated106 hV U' hU' ihc
  · intro W' p' N' μ' Mem' Z' U' hU' H' hH' hNH' hZH' J' hJnone' hJcomp' hJloc' hJcert' ihc
    exact orderOneCentersIsolated_of_isSmoothDivisor_consolidated106 hV U' hU' H' hH' hNH' hZH' J' hJnone' hJcomp' hJloc' ihc


end

end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.SmoothOrderOneCenters
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

structure PointedIrreducibleClosed (W : Scheme.{u}) where
  S : Set ↥W
  xi : ↥W
  pt : ↥W
  closedS : IsClosed S
  irredS : IsIrreducible S
  genericXi : IsGenericPoint xi S
  memPt : pt ∈ S

structure SmoothVanishingHypotheses (V : VanishingAssignment.{u}) : Prop where
  orderAt_vanishing_eq_one : ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)), Smooth p →
      ∀ T : Closeds ↥W, IsIrreducible (T : Set ↥W) →
      Smooth ((V W T).subschemeι ≫ p) →
      (∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ (T : Set ↥W)) →
      ∀ x ∈ (T : Set ↥W), orderAt (V W T) x = 1
  smooth_opens_ι_comp : ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens), Smooth p → Smooth (U.ι ≫ p)
  smooth_vanishing_hypersurface : ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens) (H : (U.toScheme).IdealSheafData),
      IsSmoothDivisor (U.ι ≫ p) H →
      ∀ (T : Closeds ↥W) (S : Closeds ↥(H.subscheme)),
        (S : Set ↥(H.subscheme)) = (H.subschemeι ≫ U.ι).base ⁻¹' (T : Set ↥W) →
        (U.ι.base ⁻¹' (T : Set ↥W)) ⊆ (H.support : Set ↥(U.toScheme)) →
        Smooth ((V W T).subschemeι ≫ p) →
        Smooth ((V H.subscheme S).subschemeι ≫ (H.subschemeι ≫ (U.ι ≫ p)))
  smooth_vanishing_opens : ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens) (T : Closeds ↥W)
      (S : Closeds ↥(U.toScheme)),
      (S : Set ↥(U.toScheme)) = U.ι.base ⁻¹' (T : Set ↥W) →
      Smooth ((V W T).subschemeι ≫ p) →
      Smooth ((V U.toScheme S).subschemeι ≫ (U.ι ≫ p))

def SmoothOrderOneCentersIsolated (V : VanishingAssignment.{u}) {k : Type u} [Field k] [CharZero k]
    (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k)) (I : W.IdealSheafData) (m : ℕ)
    (Mem : Set ↥W) (Z : W.IdealSheafData) : Prop :=
  ∀ C : PointedIrreducibleClosed W, Smooth p → m = 1 →
    Smooth ((V W ⟨C.S, C.closedS⟩).subschemeι ≫ p) →
    (∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ C.S) →
    C.xi ∉ (Z.support : Set ↥W) →
    Disjoint C.S Mem →
    (∀ x ∈ C.S, AgreeNear I (V W ⟨C.S, C.closedS⟩) x) →
    C.pt ∈ (Z.support : Set ↥W) → False

section
variable {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V) (W : Scheme.{u})
include hV

theorem subset_support_of_agreeNear (N : W.IdealSheafData) (T : Set ↥W) (hT : IsClosed T)
    (hagree : ∀ x ∈ T, AgreeNear N (V W ⟨T, hT⟩) x) :
    T ⊆ (N.support : Set ↥W) := by
  intro x hx
  rw [mem_support_iff_of_agreeNear hV (hagree x hx), hV.support_vanishing W ⟨T, hT⟩]
  exact hx

private theorem irreducibleComponents_opens_not_subset_preimage_consolidated143 (U : W.Opens) (T : Set ↥W) (hT : IsClosed T)
    (hcomp : ∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ T) :
    ∀ E ∈ irreducibleComponents ↥(U.toScheme), ¬ E ⊆ U.ι.base ⁻¹' T := by
  intro E hE hsub
  have hEirr : IsIrreducible E := hE.1
  have hrange := hV.range_ι W U
  have hcont : Continuous ⇑U.ι.base := (hV.isEmbedding_ι W U).continuous
  have hmemU : ∀ y : ↥(U.toScheme), U.ι.base y ∈ (U : Set ↥W) := by
    intro y
    rw [← hrange]
    exact Set.mem_range_self y
  obtain ⟨y0, hy0⟩ := hEirr.nonempty
  have himg : IsIrreducible (U.ι.base '' E) := hEirr.image _ hcont.continuousOn
  obtain ⟨Zc, hZpre, hAZ, hZmax⟩ :=
    exists_preirreducible (closure (U.ι.base '' E)) himg.closure.2
  have hZirr : IsIrreducible Zc := ⟨himg.closure.1.mono hAZ, hZpre⟩
  have hZmem : Zc ∈ irreducibleComponents ↥W :=
    ⟨hZirr, fun u hu hZu => (hZmax u hu.2 hZu).le⟩
  have hEZ : E ⊆ U.ι.base ⁻¹' Zc := by
    intro y hy
    exact hAZ (subset_closure ⟨y, hy, rfl⟩)
  have hZU : (Zc ∩ (U : Set ↥W)).Nonempty := ⟨U.ι.base y0, hEZ hy0, hmemU y0⟩
  have hZUirr : IsIrreducible (Zc ∩ (U : Set ↥W)) :=
    FunctorialResolution.EmbeddedResolution.isIrreducible_inter_open hZirr (hV.isOpen_opens W U) hZU
  have hsubr : (Zc ∩ (U : Set ↥W)) ⊆ Set.range ⇑U.ι.base := by
    rw [hrange]
    exact Set.inter_subset_right
  have hPirr : IsIrreducible (U.ι.base ⁻¹' (Zc ∩ (U : Set ↥W))) :=
    FunctorialResolution.EmbeddedResolution.isIrreducible_preimage_of_isEmbedding (hV.isEmbedding_ι W U) hZUirr hsubr
  have hPeq : U.ι.base ⁻¹' (Zc ∩ (U : Set ↥W)) = U.ι.base ⁻¹' Zc := by
    ext y
    constructor
    · intro hy
      exact hy.1
    · intro hy
      exact ⟨hy, hmemU y⟩
  rw [hPeq] at hPirr
  have hpreimageSub : U.ι.base ⁻¹' Zc ⊆ E := hE.2 hPirr hEZ
  have hZT : Zc ∩ (U : Set ↥W) ⊆ T := by
    rintro x ⟨hxZ, hxU⟩
    rw [← hrange] at hxU
    obtain ⟨y, rfl⟩ := hxU
    exact hsub (hpreimageSub hxZ)
  have hZcl : IsClosed Zc := isClosed_of_mem_irreducibleComponents Zc hZmem
  refine hcomp Zc hZmem ?_
  rw [← FunctorialResolution.EmbeddedResolution.closure_inter_open_eq hZcl hZirr (hV.isOpen_opens W U) hZU]
  exact closure_minimal hZT hT


end

section
variable {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V) (hG : SmoothVanishingHypotheses V) {k : Type u} [Field k] [CharZero k] {W : Scheme.{u}}
include hV hG

private theorem orderAt_eq_one_of_agreeNear_consolidated143 {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} (C : PointedIrreducibleClosed W)
    (hp : Smooth p)
    (hsm : Smooth ((V W ⟨C.S, C.closedS⟩).subschemeι ≫ p))
    (hcomp : ∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ C.S)
    (hagree : ∀ x ∈ C.S, AgreeNear I (V W ⟨C.S, C.closedS⟩) x)
    {x : ↥W} (hx : x ∈ C.S) : orderAt I x = 1 := by
  rw [hV.orderAt_congr W I (V W ⟨C.S, C.closedS⟩) x (hagree x hx)]
  exact hG.orderAt_vanishing_eq_one k W p hp ⟨C.S, C.closedS⟩ C.irredS hsm hcomp x hx

theorem false_of_smoothOrderOneCentersIsolated_opens (p : W ⟶ Spec (CommRingCat.of k)) (I Z : W.IdealSheafData) (m : ℕ) (Mem : Set ↥W)
    (C : PointedIrreducibleClosed W) (U : W.Opens) (hptU : C.pt ∈ (U : Set ↥W))
    (hIso : SmoothOrderOneCentersIsolated V U.toScheme (U.ι ≫ p) (I.comap U.ι) m
      (U.ι.base ⁻¹' Mem) (Z.comap U.ι))
    (hp : Smooth p) (hm : m = 1)
    (hsm : Smooth ((V W ⟨C.S, C.closedS⟩).subschemeι ≫ p))
    (hcomp : ∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ C.S)
    (hxi : C.xi ∉ (Z.support : Set ↥W))
    (hdisj : Disjoint C.S Mem)
    (hagree : ∀ x ∈ C.S, AgreeNear I (V W ⟨C.S, C.closedS⟩) x)
    (hpt : C.pt ∈ (Z.support : Set ↥W)) : False := by
  have hcont : Continuous ⇑U.ι.base := (hV.isEmbedding_ι W U).continuous
  have hrange := hV.range_ι W U
  have hxiU : C.xi ∈ (U : Set ↥W) :=
    (C.genericXi.mem_open_set_iff (hV.isOpen_opens W U)).mpr ⟨C.pt, C.memPt, hptU⟩
  have hxiR : C.xi ∈ Set.range ⇑U.ι.base := by
    rw [hrange]
    exact hxiU
  have hptR : C.pt ∈ Set.range ⇑U.ι.base := by
    rw [hrange]
    exact hptU
  obtain ⟨y0, hy0⟩ := hxiR
  obtain ⟨y1, hy1⟩ := hptR
  have hS'closed : IsClosed (U.ι.base ⁻¹' C.S) := C.closedS.preimage hcont
  have hgen' : IsGenericPoint y0 (U.ι.base ⁻¹' C.S) :=
    FunctorialResolution.EmbeddedResolution.isGenericPoint_preimage_of_isInducing (hV.isEmbedding_ι W U).toIsInducing
      C.genericXi hy0
  have hirr' : IsIrreducible (U.ι.base ⁻¹' C.S) := by
    rw [← hgen']
    exact isIrreducible_singleton.closure
  have hmemPt : y1 ∈ U.ι.base ⁻¹' C.S := by
    show U.ι.base y1 ∈ C.S
    rw [hy1]
    exact C.memPt
  refine hIso ⟨U.ι.base ⁻¹' C.S, y0, y1, hS'closed, hirr', hgen', hmemPt⟩
    (hG.smooth_opens_ι_comp k W p U hp) hm
    (hG.smooth_vanishing_opens k W p U ⟨C.S, C.closedS⟩ ⟨U.ι.base ⁻¹' C.S, hS'closed⟩ rfl hsm)
    (irreducibleComponents_opens_not_subset_preimage_consolidated143 hV W U C.S C.closedS hcomp) ?_ ?_ ?_ ?_
  · intro hmem
    apply hxi
    have h1 : (1 : ℕ∞) ≤ orderAt (Z.comap U.ι) y0 :=
      (one_le_orderAt_iff_mem_support (Z.comap U.ι) y0).mpr hmem
    rw [hV.orderAt_comap W U Z y0, hy0] at h1
    exact (one_le_orderAt_iff_mem_support Z C.xi).mp h1
  · rw [Set.disjoint_left]
    intro y hy hy2
    exact (Set.disjoint_left.mp hdisj hy) hy2
  · intro y hy
    have h1 := hV.agreeNear_comap W U I (V W ⟨C.S, C.closedS⟩) y (hagree _ hy)
    rw [hV.comap_vanishing W ⟨C.S, C.closedS⟩ U ⟨U.ι.base ⁻¹' C.S, hS'closed⟩ rfl] at h1
    exact h1
  · have h1 : (1 : ℕ∞) ≤ orderAt Z C.pt := (one_le_orderAt_iff_mem_support Z C.pt).mpr hpt
    rw [← hy1, ← hV.orderAt_comap W U Z y1] at h1
    exact (one_le_orderAt_iff_mem_support (Z.comap U.ι) y1).mp h1

private theorem false_of_isSmoothDivisor_of_smoothOrderOneCentersIsolated_consolidated143 (p : W ⟶ Spec (CommRingCat.of k)) (N Z : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W)
    (C : PointedIrreducibleClosed W) (U : W.Opens) (H : (U.toScheme).IdealSheafData)
    (hptU : C.pt ∈ (U : Set ↥W))
    (hH : IsSmoothDivisor (U.ι ≫ p) H)
    (hNsubH : ((N.comap U.ι).support : Set ↥(U.toScheme)) ⊆ (H.support : Set ↥(U.toScheme)))
    (hZH : ((Z.comap U.ι).support : Set ↥(U.toScheme)) ⊆ (H.support : Set ↥(U.toScheme)))
    (J : Option ((H.subscheme).IdealSheafData))
    (hJnone : J = none →
      IsOpen (H.subschemeι.base ⁻¹' ((Z.comap U.ι).support : Set ↥(U.toScheme))))
    (hJcomp : ∀ Jz, J = some Jz → NonzeroOnComponents Jz)
    (hJloc : ∀ Jz, J = some Jz → ∀ x : ↥(H.subscheme),
      (H.subschemeι ≫ U.ι).base x ∉ Mem →
      ∃ V' : (H.subscheme).Opens, x ∈ V' ∧
        Jz.comap V'.ι = ((N.comap U.ι).comap H.subschemeι).comap V'.ι)
    (ih : ∀ Jz, J = some Jz →
      SmoothOrderOneCentersIsolated V H.subscheme (H.subschemeι ≫ (U.ι ≫ p)) Jz μ
        ((H.subschemeι ≫ U.ι).base ⁻¹' Mem) ((Z.comap U.ι).comap H.subschemeι))
    (hp : Smooth p) (hm : μ = 1)
    (hsm : Smooth ((V W ⟨C.S, C.closedS⟩).subschemeι ≫ p))
    (hcomp : ∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ C.S)
    (hxi : C.xi ∉ (Z.support : Set ↥W))
    (hdisj : Disjoint C.S Mem)
    (hagree : ∀ x ∈ C.S, AgreeNear N (V W ⟨C.S, C.closedS⟩) x)
    (hpt : C.pt ∈ (Z.support : Set ↥W)) : False := by
  have hxiS : C.xi ∈ C.S := C.genericXi.mem
  have hordxi : orderAt N C.xi = 1 :=
    orderAt_eq_one_of_agreeNear_consolidated143 hV hG C hp hsm hcomp hagree hxiS
  have hxiN : C.xi ∈ (N.support : Set ↥W) :=
    (one_le_orderAt_iff_mem_support N C.xi).mp (le_of_eq hordxi.symm)
  cases hJ : J with
  | none =>
    exact false_of_isOpen_preimage_support hV W N Z
      ⟨C.S, C.S, C.xi, C.xi, C.pt, C.closedS, C.closedS, C.irredS, C.irredS, C.genericXi,
        C.genericXi, C.memPt, C.memPt⟩ U H hptU hpt hZH hNsubH (hJnone hJ) hxi hxiN
  | some Jz =>
    have hIH := ih Jz hJ
    have hxiU : C.xi ∈ (U : Set ↥W) :=
      (C.genericXi.mem_open_set_iff (hV.isOpen_opens W U)).mpr ⟨C.pt, C.memPt, hptU⟩
    have hCsubN : C.S ⊆ (N.support : Set ↥W) :=
      subset_support_of_agreeNear hV W N C.S C.closedS hagree
    have hsubH : (U.ι.base ⁻¹' C.S) ⊆ (H.support : Set ↥(U.toScheme)) := by
      intro y hy
      apply hNsubH
      rw [FunctorialResolution.EmbeddedResolution.support_comap_eq]
      exact hCsubN hy
    obtain ⟨y0, hy0⟩ := exists_subschemeι_comp_ι_apply_eq_of_mem hV W U H C.S hsubH C.xi hxiU hxiS
    obtain ⟨y1, hy1⟩ := exists_subschemeι_comp_ι_apply_eq_of_mem hV W U H C.S hsubH C.pt hptU C.memPt
    have hS'closed : IsClosed ((H.subschemeι ≫ U.ι).base ⁻¹' C.S) :=
      isClosed_preimage_subschemeι_comp_ι hV W U H C.S C.closedS
    have hgen' : IsGenericPoint y0 ((H.subschemeι ≫ U.ι).base ⁻¹' C.S) :=
      isGenericPoint_preimage_subschemeι_comp_ι hV W U H C.S C.xi C.genericXi y0 hy0
    have hirr' : IsIrreducible ((H.subschemeι ≫ U.ι).base ⁻¹' C.S) := by
      rw [← hgen']
      exact isIrreducible_singleton.closure
    have hmemPt : y1 ∈ (H.subschemeι ≫ U.ι).base ⁻¹' C.S := by
      show (H.subschemeι ≫ U.ι).base y1 ∈ C.S
      rw [hy1]
      exact C.memPt
    have hagree' : ∀ x ∈ (H.subschemeι ≫ U.ι).base ⁻¹' C.S,
        AgreeNear Jz (V H.subscheme ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, hS'closed⟩) x := by
      intro x hx
      have h1 : AgreeNear ((N.comap U.ι).comap H.subschemeι)
          (V H.subscheme ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, hS'closed⟩) x :=
        hV.agreeNear_vanishing_restrict W N U H ⟨C.S, C.closedS⟩
          ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, hS'closed⟩ x rfl hsubH (hagree _ hx)
      have h2 : AgreeNear Jz ((N.comap U.ι).comap H.subschemeι) x :=
        hJloc Jz hJ x (Set.disjoint_left.mp hdisj hx)
      exact hV.agreeNear_trans H.subscheme Jz ((N.comap U.ι).comap H.subschemeι)
        (V H.subscheme ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, hS'closed⟩) x h2 h1
    have hS'J : ((H.subschemeι ≫ U.ι).base ⁻¹' C.S) ⊆ (Jz.support : Set ↥(H.subscheme)) :=
      subset_support_of_agreeNear hV H.subscheme Jz ((H.subschemeι ≫ U.ι).base ⁻¹' C.S)
        hS'closed hagree'
    have hcomp' : ∀ E ∈ irreducibleComponents ↥(H.subscheme),
        ¬ E ⊆ (H.subschemeι ≫ U.ι).base ⁻¹' C.S := by
      intro E hE hEsub
      exact hV.not_subset_support_of_nonzeroOnComponents H.subscheme Jz (hJcomp Jz hJ) E hE
        (hEsub.trans hS'J)
    have hsupp : ∀ x : ↥(H.subscheme),
        x ∈ ((((Z.comap U.ι).comap H.subschemeι)).support : Set ↥(H.subscheme)) ↔
          (H.subschemeι ≫ U.ι).base x ∈ (Z.support : Set ↥W) := by
      intro x
      constructor
      · intro hx
        have h1 : (H.subschemeι.base x) ∈ ((Z.comap U.ι).support : Set ↥(U.toScheme)) := by
          rw [FunctorialResolution.EmbeddedResolution.support_comap_eq] at hx
          exact hx
        have h2 : (U.ι.base (H.subschemeι.base x)) ∈ (Z.support : Set ↥W) := by
          rw [FunctorialResolution.EmbeddedResolution.support_comap_eq] at h1
          exact h1
        rw [hV.base_comp]
        exact h2
      · intro hx
        rw [hV.base_comp] at hx
        have h1 : (H.subschemeι.base x) ∈ ((Z.comap U.ι).support : Set ↥(U.toScheme)) := by
          rw [FunctorialResolution.EmbeddedResolution.support_comap_eq]
          exact hx
        rw [FunctorialResolution.EmbeddedResolution.support_comap_eq]
        exact h1
    have hxi' : y0 ∉ ((((Z.comap U.ι).comap H.subschemeι)).support : Set ↥(H.subscheme)) := by
      intro hmem
      apply hxi
      have h1 := (hsupp y0).mp hmem
      rw [hy0] at h1
      exact h1
    have hpt' : y1 ∈ ((((Z.comap U.ι).comap H.subschemeι)).support : Set ↥(H.subscheme)) := by
      refine (hsupp y1).mpr ?_
      rw [hy1]
      exact hpt
    have hdisj' : Disjoint ((H.subschemeι ≫ U.ι).base ⁻¹' C.S)
        ((H.subschemeι ≫ U.ι).base ⁻¹' Mem) := by
      rw [Set.disjoint_left]
      intro x hx hx2
      exact (Set.disjoint_left.mp hdisj hx) hx2
    have hsmooth : Smooth (H.subschemeι ≫ (U.ι ≫ p)) :=
      ((isSmoothDivisor_iff (U.ι ≫ p) H).mp hH).2
    have hsmV : Smooth ((V H.subscheme
        ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, hS'closed⟩).subschemeι ≫
        (H.subschemeι ≫ (U.ι ≫ p))) :=
      hG.smooth_vanishing_hypersurface k W p U H hH ⟨C.S, C.closedS⟩
        ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, hS'closed⟩ rfl hsubH hsm
    exact hIH ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, y0, y1, hS'closed, hirr', hgen', hmemPt⟩
      hsmooth hm hsmV hcomp' hxi' hdisj' hagree' hpt'

theorem smoothOrderOneCentersIsolated_of_principalizationCertificate {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z) :
    SmoothOrderOneCentersIsolated V W p I m Mem Z := by
  refine PrincipalizationCertificate.rec
    (motive_1 := fun W p I m Mem Z _ => SmoothOrderOneCentersIsolated V W p I m Mem Z)
    (motive_2 := fun W p N μ Mem Z _ => SmoothOrderOneCentersIsolated V W p N μ Mem Z)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro W p I m Mem Z hZM C hp hm hsm hcomp hxi hdisj hagree hpt
    exact (Set.disjoint_left.mp hdisj C.memPt) (hZM hpt)
  · intro W p I m Mem Z hm2 C hp hm hsm hcomp hxi hdisj hagree hpt
    omega
  · intro W p I m Mem Z M N μ hI hM hmu hZc hcert ih C hp hm hsm hcomp hxi hdisj hagree hpt
    have hIN : ∀ x ∈ C.S, AgreeNear I N x := by
      intro x hx
      have hxM : x ∉ (M.support : Set ↥W) := fun hmm =>
        (Set.disjoint_left.mp hdisj hx) (hM hmm)
      obtain ⟨Uc, hUcx, hUcdisj⟩ :
          ∃ Uc : W.Opens, x ∈ Uc ∧ Disjoint ((Uc : Set ↥W)) (M.support : Set ↥W) :=
        ⟨⟨(M.support : Set ↥W)ᶜ, (hV.isClosed_support W M).isOpen_compl⟩, hxM,
          disjoint_compl_left⟩
      refine ⟨Uc, hUcx, ?_⟩
      have hMtop : M.comap Uc.ι = ⊤ := FunctorialResolution.EmbeddedResolution.comap_ι_eq_top_of_disjoint M Uc hUcdisj
      rw [hI, hV.comap_mul W Uc.toScheme Uc.ι M N, hMtop, hV.top_mul]
    have hagreeN : ∀ x ∈ C.S, AgreeNear N (V W ⟨C.S, C.closedS⟩) x := fun x hx =>
      hV.agreeNear_trans W N I (V W ⟨C.S, C.closedS⟩) x (agreeNear_symm (hIN x hx)) (hagree x hx)
    rcases Nat.lt_or_ge μ 2 with h2 | h2
    · have hmu1 : μ = 1 := by omega
      exact ih C hp hmu1 hsm hcomp hxi hdisj hagreeN hpt
    · have hord : orderAt N C.pt = 1 :=
        orderAt_eq_one_of_agreeNear_consolidated143 hV hG C hp hsm hcomp hagreeN C.memPt
      have hmem : C.pt ∈ orderAtLeastLocus N μ := hZc hpt
      rw [FunctorialResolution.EmbeddedResolution.mem_orderAtLeastLocus_iff, hord] at hmem
      have hle : μ ≤ 1 := by exact_mod_cast hmem
      omega
  · intro W p I m Mem Z U hU hcert ih C hp hm hsm hcomp hxi hdisj hagree hpt
    have hz : C.pt ∈ Z.support := hpt
    exact false_of_smoothOrderOneCentersIsolated_opens hV hG p I Z m Mem C (U C.pt hz) (hU C.pt hz)
      (ih C.pt hz) hp hm hsm hcomp hxi hdisj hagree hpt
  · intro W p N μ Mem Z hZM C hp hm hsm hcomp hxi hdisj hagree hpt
    exact (Set.disjoint_left.mp hdisj C.memPt) (hZM hpt)
  · intro W p N μ Mem Z hmu2 C hp hm hsm hcomp hxi hdisj hagree hpt
    omega
  · intro W p N μ Mem Z U hU hcert ih C hp hm hsm hcomp hxi hdisj hagree hpt
    have hz : C.pt ∈ Z.support := hpt
    exact false_of_smoothOrderOneCentersIsolated_opens hV hG p N Z μ Mem C (U C.pt hz) (hU C.pt hz)
      (ih C.pt hz) hp hm hsm hcomp hxi hdisj hagree hpt
  · intro W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert ih C hp hm hsm hcomp hxi
      hdisj hagree hpt
    have hz : C.pt ∈ Z.support := hpt
    exact false_of_isSmoothDivisor_of_smoothOrderOneCentersIsolated_consolidated143 hV hG p N Z μ Mem C (U C.pt hz) (H C.pt hz) (hU C.pt hz) (hH C.pt hz)
      (hNsubH C.pt hz) (hZH C.pt hz) (J C.pt hz) (hJnone C.pt hz) (hJcomp C.pt hz)
      (hJloc C.pt hz) (fun Jz hJ => ih C.pt hz Jz hJ) hp hm hsm hcomp hxi hdisj hagree hpt


end

end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealAssignment
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

noncomputable def vanishingIdealAssignment : VanishingAssignment.{u} :=
  fun _ T => Scheme.IdealSheafData.vanishingIdeal T

theorem vanishingIdealAssignment_apply (X : Scheme.{u}) (T : Closeds ↥X) :
    vanishingIdealAssignment X T = Scheme.IdealSheafData.vanishingIdeal T := rfl

def VanishingOrderOneOnSmoothDivisor : Prop :=
  ∀ (k : Type u) [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))
    (U : W.Opens) (D : (U.toScheme).IdealSheafData),
    IsSmoothDivisor (U.ι ≫ p) D →
    ∀ (T : Closeds ↥(D.subscheme)) (y : ↥(D.subscheme)),
      IsGenericPoint y (T : Set ↥(D.subscheme)) →
      (T : Set ↥(D.subscheme)) ∉ irreducibleComponents ↥(D.subscheme) →
      orderAt (vanishingIdealAssignment D.subscheme T) y = 1

def AgreeNearVanishingComapSubscheme : Prop :=
  ∀ (W : Scheme.{u}) (N : W.IdealSheafData) (U : W.Opens)
    (H : (U.toScheme).IdealSheafData) (T : Closeds ↥W) (S : Closeds ↥(H.subscheme))
    (x : ↥(H.subscheme)),
    (S : Set ↥(H.subscheme)) = (H.subschemeι ≫ U.ι).base ⁻¹' (T : Set ↥W) →
    (U.ι.base ⁻¹' (T : Set ↥W)) ⊆ (H.support : Set ↥(U.toScheme)) →
    AgreeNear N (vanishingIdealAssignment W T) ((H.subschemeι ≫ U.ι).base x) →
    AgreeNear ((N.comap U.ι).comap H.subschemeι) (vanishingIdealAssignment H.subscheme S) x

def VanishingComapOpens : Prop :=
  ∀ (W : Scheme.{u}) (T : Closeds ↥W) (V : W.Opens) (S : Closeds ↥(V.toScheme)),
    (S : Set ↥(V.toScheme)) = V.ι.base ⁻¹' (T : Set ↥W) →
    (vanishingIdealAssignment W T).comap V.ι = vanishingIdealAssignment V.toScheme S

def OrderAtEqOfAgreeNear : Prop :=
  ∀ (W : Scheme.{u}) (I J : W.IdealSheafData) (x : ↥W),
    AgreeNear I J x → orderAt I x = orderAt J x

private theorem comap_opens_eq_of_le_consolidated173 {W : Scheme.{u}} {I J : W.IdealSheafData} {U U' : W.Opens}
    (h : U' ≤ U) (hEq : I.comap U.ι = J.comap U.ι) :
    I.comap U'.ι = J.comap U'.ι := by
  have hι : W.homOfLE h ≫ U.ι = U'.ι := by simp
  rw [← hι, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hEq]

section
variable (W : Scheme.{u}) (V : W.Opens)

theorem agreeNear_comap_ι (I J : W.IdealSheafData)
    (y : ↥(V.toScheme)) (h : AgreeNear I J (V.ι.base y)) :
    AgreeNear (I.comap V.ι) (J.comap V.ι) y := by
  obtain ⟨U, hU, hEq⟩ := (agreeNear_iff I J (V.ι.base y)).mp h
  refine (agreeNear_iff _ _ _).mpr ⟨V.ι ⁻¹ᵁ U, hU, ?_⟩
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    ← morphismRestrict_ι V.ι U, Scheme.IdealSheafData.comap_comp,
    Scheme.IdealSheafData.comap_comp, hEq]

theorem orderAt_comap_ι (I : W.IdealSheafData)
    (y : ↥(V.toScheme)) :
    orderAt (I.comap V.ι) y = orderAt I (V.ι.base y) :=
  FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isOpenImmersion V.ι I y


end

theorem orderAtEqOfAgreeNear : OrderAtEqOfAgreeNear.{u} := by
  intro W I J x h
  obtain ⟨U, hxU, hEq⟩ := (agreeNear_iff I J x).mp h
  obtain ⟨y, hy⟩ : ∃ y : ↥(U.toScheme), U.ι.base y = x := by
    have hx : x ∈ Set.range ⇑U.ι.base := by simpa using hxU
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy⟩
  rw [← hy, ← orderAt_comap_ι W U I y, ← orderAt_comap_ι W U J y, hEq]

section
variable (h1 : VanishingOrderOneOnSmoothDivisor.{u}) (h2 : AgreeNearVanishingComapSubscheme.{u}) (h3 : VanishingComapOpens.{u})
include h1 h2 h3

theorem idealSheafGeometryHypotheses_of_orderAtEqOfAgreeNear
    (h4 : OrderAtEqOfAgreeNear.{u}) :
    IdealSheafGeometryHypotheses vanishingIdealAssignment.{u} :=
  { agreeNear_comap := agreeNear_comap_ι
    agreeNear_trans := by
      intro W I J K x hIJ hJK
      obtain ⟨U1, hx1, e1⟩ := (agreeNear_iff I J x).mp hIJ
      obtain ⟨U2, hx2, e2⟩ := (agreeNear_iff J K x).mp hJK
      exact (agreeNear_iff I K x).mpr
        ⟨U1 ⊓ U2, ⟨hx1, hx2⟩,
          (comap_opens_eq_of_le_consolidated173 inf_le_left e1).trans (comap_opens_eq_of_le_consolidated173 inf_le_right e2)⟩
    comap_mul := fun W X f I J => Scheme.IdealSheafData.comap_mul I J f
    base_comp := fun X Y Z f g x => by simp
    isClosed_support := fun W I => I.support.isClosed
    isClosedEmbedding_subschemeι := fun W I =>
      IsClosedImmersion.isClosedEmbedding (f := I.subschemeι)
    isEmbedding_ι := fun W U => U.ι.isOpenEmbedding.toIsEmbedding
    isOpen_opens := fun W U => U.2
    orderAt_comap := orderAt_comap_ι
    orderAt_congr := h4
    orderAt_vanishing_eq_one := h1
    range_ι := fun W U => by simp
    range_subschemeι := fun W I => by simp
    support_mul := fun W I J => by
      rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup]
    not_subset_support_of_nonzeroOnComponents := fun W I h => (nonzeroOnComponents_iff I).mp h
    support_vanishing := fun W T => by simp [vanishingIdealAssignment]
    top_mul := fun W I => by simp
    agreeNear_vanishing_restrict := h2
    comap_vanishing := h3 }

theorem idealSheafGeometryHypotheses_of_vanishingOrderOneOnSmoothDivisor
    :
    IdealSheafGeometryHypotheses vanishingIdealAssignment.{u} :=
  idealSheafGeometryHypotheses_of_orderAtEqOfAgreeNear h1 h2 h3 orderAtEqOfAgreeNear


end

end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealOrderOne
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

section
variable (X : Scheme.{u})

private theorem exists_affineOpens_mem_consolidated194 (x : ↥X) :
    ∃ U : X.affineOpens, x ∈ U.1.1 := by
  have hx : x ∈ (⨆ U : X.affineOpens, (U : X.Opens)) := by
    rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
    trivial
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨U, hU⟩

theorem maximalIdeal_stalk_ne_bot_of_specializes
    (x y : ↥X) (h : y ⤳ x) (hne : y ≠ x) :
    IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) ≠ ⊥ := by
  intro hbot
  obtain ⟨U, hxU0⟩ := exists_affineOpens_mem_consolidated194 X x
  have hxU : x ∈ U.1 := hxU0
  have hU : IsAffineOpen U.1 := U.2
  have hmem : x ∈ closure ({y} : Set ↥X) := specializes_iff_mem_closure.mp h
  have hyU : y ∈ U.1 := by
    have hopen : IsOpen ((U.1 : Set ↥X)) := U.1.2
    obtain ⟨z, hzU, hzy⟩ := (mem_closure_iff.mp hmem) ((U.1 : Set ↥X)) hopen hxU
    rw [Set.mem_singleton_iff] at hzy
    have hy2 : y ∈ ((U.1 : Set ↥X)) := by rw [← hzy]; exact hzU
    exact hy2
  have hind : Topology.IsInducing (⇑(hU.fromSpec)) :=
    (hU.fromSpec).isOpenEmbedding.toIsEmbedding.toIsInducing
  have e1 : (⇑(hU.fromSpec)) (hU.primeIdealOf ⟨x, hxU⟩) = x :=
    hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have e2 : (⇑(hU.fromSpec)) (hU.primeIdealOf ⟨y, hyU⟩) = y :=
    hU.fromSpec_primeIdealOf ⟨y, hyU⟩
  have hspec : hU.primeIdealOf ⟨y, hyU⟩ ⤳ hU.primeIdealOf ⟨x, hxU⟩ := by
    apply hind.specializes_iff.mp
    rw [e1, e2]
    exact h
  have hqp : (hU.primeIdealOf ⟨y, hyU⟩).asIdeal ≤ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    have h2 := specializes_iff_mem_closure.mp hspec
    rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.mem_zeroLocus] at h2
    exact fun z hz => h2 hz
  have hne' : (hU.primeIdealOf ⟨y, hyU⟩).asIdeal ≠ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    intro heq
    apply hne
    have hpe : hU.primeIdealOf ⟨y, hyU⟩ = hU.primeIdealOf ⟨x, hxU⟩ := PrimeSpectrum.ext heq
    exact e2.symm.trans (by rw [hpe]; exact e1)
  obtain ⟨a, hap, haq⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hqp hne')
  let _ : Algebra Γ(X, U.1) ↑(X.presheaf.stalk x) := (X.presheaf.germ U.1 x hxU).hom.toAlgebra
  have hloc : IsLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      ↑(X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hxU⟩
  have hmax : Ideal.map (algebraMap Γ(X, U.1) ↑(X.presheaf.stalk x))
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
      = IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal ..
  have hmapmem : (algebraMap Γ(X, U.1) ↑(X.presheaf.stalk x)) a
      ∈ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) := by
    rw [← hmax]
    exact Ideal.mem_map_of_mem _ hap
  have h0 : (algebraMap Γ(X, U.1) ↑(X.presheaf.stalk x)) a = 0 := by
    rw [hbot] at hmapmem
    simpa using hmapmem
  have h1 : (algebraMap Γ(X, U.1) ↑(X.presheaf.stalk x)) a
      = (algebraMap Γ(X, U.1) ↑(X.presheaf.stalk x)) 0 := by
    rw [h0, map_zero]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl ↑(X.presheaf.stalk x)).mp h1
  have hca : (c : Γ(X, U.1)) * a = 0 := by
    rw [mul_zero] at hc
    exact hc
  have hcp : (c : Γ(X, U.1)) ∉ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := c.2
  have hcq : (c : Γ(X, U.1)) ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := fun hc0 => hcp (hqp hc0)
  have hmem0 : (c : Γ(X, U.1)) * a ∈ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
    rw [hca]
    exact Submodule.zero_mem _
  rcases (hU.primeIdealOf ⟨y, hyU⟩).isPrime.mem_or_mem hmem0 with hcc | haa
  · exact hcq hcc
  · exact haq haa

theorem orderAt_vanishingIdeal_eq_one_of_not_mem_irreducibleComponents
    [IsLocallyNoetherian X] (S : Closeds ↥X) (x : ↥X)
    (hx : IsGenericPoint x (S : Set ↥X))
    (hS : (S : Set ↥X) ∉ irreducibleComponents ↥X) :
    FunctorialResolution.EmbeddedResolution.orderAt (Scheme.IdealSheafData.vanishingIdeal S) x = 1 := by
  have hx' : closure ({x} : Set ↥X) = (S : Set ↥X) := hx
  have hSirr : IsIrreducible (S : Set ↥X) := by
    rw [← hx']
    exact isIrreducible_singleton.closure
  have hxS : x ∈ (S : Set ↥X) := by
    rw [← hx']
    exact subset_closure (Set.mem_singleton x)
  have hMax : Maximal (fun s : Set ↥X => IsIrreducible s ∧ s ⊆ (S : Set ↥X)) (S : Set ↥X) := by
    constructor
    · exact ⟨hSirr, subset_rfl⟩
    · intro b hb _
      exact hb.2
  obtain ⟨t, htpre, hSt, hmaxt⟩ := exists_preirreducible (S : Set ↥X) hSirr.2
  have htirr : IsIrreducible t := ⟨⟨x, hSt hxS⟩, htpre⟩
  have htclosed : IsClosed t := by
    have h1 : closure t = t := hmaxt (closure t) htpre.closure subset_closure
    rw [← h1]
    exact isClosed_closure
  have htmem : t ∈ irreducibleComponents ↥X := by
    constructor
    · exact htirr
    · intro u hu htu
      exact (hmaxt u hu.2 htu).le
  have hSnet : (S : Set ↥X) ≠ t := by
    intro hEq
    exact hS (hEq ▸ htmem)
  obtain ⟨y, hy⟩ := QuasiSober.sober htirr htclosed
  have hy' : closure ({y} : Set ↥X) = t := hy
  have hyx : y ⤳ x := by
    rw [specializes_iff_mem_closure, hy']
    exact hSt hxS
  have hyne : y ≠ x := by
    intro hEq
    apply hSnet
    rw [← hx', ← hEq]
    exact hy'
  have hbot : IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) ≠ ⊥ :=
    maximalIdeal_stalk_ne_bot_of_specializes X x y hyx hyne
  exact _root_.FunctorialResolution.EmbeddedResolution.orderAt_vanishingIdeal_eq_one S x (S : Set ↥X) hMax hx hbot


end

theorem isLocallyNoetherian_subscheme_of_isSmoothDivisor
    (k : Type u) [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))
    (U : W.Opens) (D : (U.toScheme).IdealSheafData)
    (hD : IsSmoothDivisor (U.ι ≫ p) D) :
    IsLocallyNoetherian D.subscheme := by
  obtain ⟨_, hsm⟩ := hD
  have : Smooth (D.subschemeι ≫ U.ι ≫ p) := hsm
  have : LocallyOfFiniteType (D.subschemeι ≫ U.ι ≫ p) := inferInstance
  have : IsNoetherianRing (CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  exact AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian (D.subschemeι ≫ U.ι ≫ p)

theorem vanishingOrderOneOnSmoothDivisor : VanishingOrderOneOnSmoothDivisor.{u} := by
  intro k hk W p U D hD T y hy hT
  have : IsLocallyNoetherian D.subscheme :=
    isLocallyNoetherian_subscheme_of_isSmoothDivisor k W p U D hD
  rw [vanishingIdealAssignment_apply]
  exact orderAt_vanishingIdeal_eq_one_of_not_mem_irreducibleComponents D.subscheme T y hy hT

end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CertificateOpenRestriction
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

noncomputable def comapSubscheme {V W : Scheme.{u}} (f : V ⟶ W) (D : W.IdealSheafData) :
    (D.comap f).subscheme ⟶ D.subscheme :=
  Scheme.IdealSheafData.subschemeMap (D.comap f) D f (D.le_map_comap f)

theorem comapSubscheme_comp {V W : Scheme.{u}} (f : V ⟶ W) (D : W.IdealSheafData) :
    comapSubscheme f D ≫ D.subschemeι = (D.comap f).subschemeι ≫ f := by
  simp [comapSubscheme]

theorem comapSubscheme_comp_assoc {V W T : Scheme.{u}} (f : V ⟶ W) (D : W.IdealSheafData)
    (g : W ⟶ T) :
    comapSubscheme f D ≫ D.subschemeι ≫ g = (D.comap f).subschemeι ≫ f ≫ g := by
  rw [← Category.assoc, comapSubscheme_comp, Category.assoc]

structure OpenImmersionStability (k : Type u) [Field k] : Prop where
  comap_nonzeroOnComponents :
    ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] (J : W.IdealSheafData),
      NonzeroOnComponents J → NonzeroOnComponents (J.comap f)
  isOpenImmersion_comapSubscheme :
    ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] (D : W.IdealSheafData),
      IsOpenImmersion (comapSubscheme f D)
  comap_isSmoothDivisor :
    ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f]
      (p : W ⟶ Spec (CommRingCat.of k)) (D : W.IdealSheafData),
      IsSmoothDivisor p D → IsSmoothDivisor (f ≫ p) (D.comap f)

private theorem coe_support_comap_consolidated175 {V W : Scheme.{u}} (f : V ⟶ W) (Z : W.IdealSheafData) :
    ((Z.comap f).support : Set ↥V) = ⇑f.base ⁻¹' ((Z.support : Set ↥W)) := by
  rw [Scheme.IdealSheafData.support_comap]; rfl

private theorem preimage_base_comp_consolidated175 {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (S : Set ↥C) :
    ⇑(a ≫ b).base ⁻¹' S = ⇑a.base ⁻¹' (⇑b.base ⁻¹' S) := by
  ext w
  exact Iff.rfl

private theorem preimage_base_preimage_base_of_comp_eq_consolidated175 {A B C D : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C}
    {d : C ⟶ D} (e : a ≫ b = c ≫ d) (S : Set ↥D) :
    ⇑a.base ⁻¹' (⇑b.base ⁻¹' S) = ⇑c.base ⁻¹' (⇑d.base ⁻¹' S) := by
  rw [← preimage_base_comp_consolidated175, ← preimage_base_comp_consolidated175, e]

section
variable {k : Type u} [Field k] {A : Scheme.{u}} {p₁ p₂ : A ⟶ Spec (CommRingCat.of k)}

private theorem principalizationCertificate_congr_consolidated175 {I₁ I₂ : A.IdealSheafData} {m : ℕ}
    {Mem₁ Mem₂ : Set ↥A} {Z₁ Z₂ : A.IdealSheafData}
    (h : PrincipalizationCertificate A p₁ I₁ m Mem₁ Z₁) (hp : p₁ = p₂) (hI : I₁ = I₂) (hM : Mem₁ = Mem₂)
    (hZ : Z₁ = Z₂) : PrincipalizationCertificate A p₂ I₂ m Mem₂ Z₂ := by
  subst hp; subst hI; subst hM; subst hZ; exact h

private theorem orderCertificate_congr_consolidated175 {N₁ N₂ : A.IdealSheafData} {μ : ℕ}
    {Mem₁ Mem₂ : Set ↥A} {Z₁ Z₂ : A.IdealSheafData}
    (h : OrderCertificate A p₁ N₁ μ Mem₁ Z₁) (hp : p₁ = p₂) (hN : N₁ = N₂) (hM : Mem₁ = Mem₂)
    (hZ : Z₁ = Z₂) : OrderCertificate A p₂ N₂ μ Mem₂ Z₂ := by
  subst hp; subst hN; subst hM; subst hZ; exact h


end

private def IsPrincipalizationCertificateOnOpens_consolidated175 {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (I : W.IdealSheafData) (m : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) : Prop :=
  ∀ (V : Scheme.{u}) (f : V ⟶ W), IsOpenImmersion f →
    PrincipalizationCertificate V (f ≫ p) (I.comap f) m (⇑f.base ⁻¹' Mem) (Z.comap f)

private def IsOrderCertificateOnOpens_consolidated175 {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) : Prop :=
  ∀ (V : Scheme.{u}) (f : V ⟶ W), IsOpenImmersion f →
    OrderCertificate V (f ≫ p) (N.comap f) μ (⇑f.base ⁻¹' Mem) (Z.comap f)

section
variable {k : Type u} [Field k] {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}

private theorem comapPrincipalizationCertificate_of_support_subset_consolidated175 {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (h : ((Z.support : Set ↥W)) ⊆ Mem) :
    IsPrincipalizationCertificateOnOpens_consolidated175 W p I m Mem Z := by
  intro V f _hf
  refine PrincipalizationCertificate.memory ?_
  rw [coe_support_comap_consolidated175]
  exact Set.preimage_mono h

private theorem comapOrderCertificate_of_support_subset_consolidated175 {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (h : ((Z.support : Set ↥W)) ⊆ Mem) :
    IsOrderCertificateOnOpens_consolidated175 W p N μ Mem Z := by
  intro V f _hf
  refine OrderCertificate.memory ?_
  rw [coe_support_comap_consolidated175]
  exact Set.preimage_mono h

private theorem comapPrincipalizationCertificate_of_two_le_consolidated175 {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (hm : 2 ≤ m) : IsPrincipalizationCertificateOnOpens_consolidated175 W p I m Mem Z := by
  intro V f _hf
  exact PrincipalizationCertificate.large hm

private theorem comapOrderCertificate_of_two_le_consolidated175 {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (hmu : 2 ≤ μ) : IsOrderCertificateOnOpens_consolidated175 W p N μ Mem Z := by
  intro V f _hf
  exact OrderCertificate.large hmu

private theorem comapPrincipalizationCertificate_of_mul_of_order_consolidated175 {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (M N : W.IdealSheafData) (μ : ℕ) (hI : I = M * N)
    (hM : ((M.support : Set ↥W)) ⊆ Mem) (hmu : m ≤ μ)
    (hZ : ((Z.support : Set ↥W)) ⊆ orderAtLeastLocus N μ) (ih : IsOrderCertificateOnOpens_consolidated175 W p N μ Mem Z) :
    IsPrincipalizationCertificateOnOpens_consolidated175 W p I m Mem Z := by
  intro V f hf
  refine PrincipalizationCertificate.toOrder (M.comap f) (N.comap f) μ ?_ ?_ hmu ?_ (ih V f hf)
  · rw [hI, Scheme.IdealSheafData.comap_mul]
  · rw [coe_support_comap_consolidated175]
    exact Set.preimage_mono hM
  · rw [coe_support_comap_consolidated175]
    intro y hy
    rw [mem_orderAtLeastLocus_iff]
    exact le_trans ((mem_orderAtLeastLocus_iff N μ (f.base y)).mp (hZ hy))
      (orderAt_le_orderAt_comap f N y)

private theorem comapPrincipalizationCertificate_of_open_cover_consolidated175 {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support),
      IsPrincipalizationCertificateOnOpens_consolidated175 (U z hz).toScheme ((U z hz).ι ≫ p) (I.comap (U z hz).ι) m
        (⇑(U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)) :
    IsPrincipalizationCertificateOnOpens_consolidated175 W p I m Mem Z := by
  intro V f hf
  have : IsOpenImmersion f := hf
  have hsup : ∀ (y : ↥V), y ∈ (Z.comap f).support → f.base y ∈ Z.support := by
    intro y hy
    have h1 : y ∈ ((Z.comap f).support : Set ↥V) := hy
    rw [coe_support_comap_consolidated175] at h1
    exact h1
  refine PrincipalizationCertificate.localize (fun y hy => f ⁻¹ᵁ U (f.base y) (hsup y hy))
    (fun y hy => hU _ _) ?_
  intro y hy
  have e1 : (f ∣_ U (f.base y) (hsup y hy)) ≫ (U (f.base y) (hsup y hy)).ι
      = (f ⁻¹ᵁ U (f.base y) (hsup y hy)).ι ≫ f := morphismRestrict_ι ..
  refine principalizationCertificate_congr_consolidated175 (ih (f.base y) (hsup y hy) _ (f ∣_ U (f.base y) (hsup y hy))
    inferInstance) ?_ ?_ ?_ ?_
  · rw [← Category.assoc, e1, Category.assoc]
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, e1]
  · exact preimage_base_preimage_base_of_comp_eq_consolidated175 e1 Mem
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, e1]

private theorem comapOrderCertificate_of_open_cover_consolidated175 {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support),
      IsOrderCertificateOnOpens_consolidated175 (U z hz).toScheme ((U z hz).ι ≫ p) (N.comap (U z hz).ι) μ
        (⇑(U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)) :
    IsOrderCertificateOnOpens_consolidated175 W p N μ Mem Z := by
  intro V f hf
  have : IsOpenImmersion f := hf
  have hsup : ∀ (y : ↥V), y ∈ (Z.comap f).support → f.base y ∈ Z.support := by
    intro y hy
    have h1 : y ∈ ((Z.comap f).support : Set ↥V) := hy
    rw [coe_support_comap_consolidated175] at h1
    exact h1
  refine OrderCertificate.localize (fun y hy => f ⁻¹ᵁ U (f.base y) (hsup y hy))
    (fun y hy => hU _ _) ?_
  intro y hy
  have e1 : (f ∣_ U (f.base y) (hsup y hy)) ≫ (U (f.base y) (hsup y hy)).ι
      = (f ⁻¹ᵁ U (f.base y) (hsup y hy)).ι ≫ f := morphismRestrict_ι ..
  refine orderCertificate_congr_consolidated175 (ih (f.base y) (hsup y hy) _ (f ∣_ U (f.base y) (hsup y hy))
    inferInstance) ?_ ?_ ?_ ?_
  · rw [← Category.assoc, e1, Category.assoc]
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, e1]
  · exact preimage_base_preimage_base_of_comp_eq_consolidated175 e1 Mem
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, e1]


end

private theorem isSmoothDivisor_comap_morphismRestrict_consolidated175 {k : Type u} [Field k] (hin : OpenImmersionStability k)
    {V W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} (f : V ⟶ W) [IsOpenImmersion f]
    (U' : W.Opens) (Hd : U'.toScheme.IdealSheafData)
    (h : IsSmoothDivisor (U'.ι ≫ p) Hd) :
    IsSmoothDivisor ((f ⁻¹ᵁ U').ι ≫ (f ≫ p)) (Hd.comap (f ∣_ U')) := by
  have e1 : (f ∣_ U') ≫ U'.ι = (f ⁻¹ᵁ U').ι ≫ f := morphismRestrict_ι ..
  have h2 := hin.comap_isSmoothDivisor (f ∣_ U') (U'.ι ≫ p) Hd h
  have e4 : (f ∣_ U') ≫ (U'.ι ≫ p) = (f ⁻¹ᵁ U').ι ≫ (f ≫ p) := by
    rw [← Category.assoc, e1, Category.assoc]
  rwa [e4] at h2

section
variable {V W : Scheme.{u}} (f : V ⟶ W) (U' : W.Opens) (Hd : U'.toScheme.IdealSheafData) (K : W.IdealSheafData)

private theorem support_comap_morphismRestrict_subset_consolidated175 (h : ((K.comap U'.ι).support : Set ↥U'.toScheme) ⊆ ((Hd.support : Set ↥U'.toScheme))) :
    ((((K.comap f).comap (f ⁻¹ᵁ U').ι).support : Set ↥(f ⁻¹ᵁ U').toScheme)) ⊆
      (((Hd.comap (f ∣_ U')).support : Set ↥(f ⁻¹ᵁ U').toScheme)) := by
  have e1 : (f ∣_ U') ≫ U'.ι = (f ⁻¹ᵁ U').ι ≫ f := morphismRestrict_ι ..
  have e5 : (K.comap f).comap (f ⁻¹ᵁ U').ι = (K.comap U'.ι).comap (f ∣_ U') := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, e1]
  rw [e5, coe_support_comap_consolidated175 (f ∣_ U') (K.comap U'.ι), coe_support_comap_consolidated175 (f ∣_ U') Hd]
  exact Set.preimage_mono h

private theorem isOpen_preimage_support_comap_morphismRestrict_consolidated175 (h : IsOpen (⇑Hd.subschemeι.base ⁻¹'
      (((K.comap U'.ι).support : Set ↥U'.toScheme)))) :
    IsOpen (⇑(Hd.comap (f ∣_ U')).subschemeι.base ⁻¹'
      ((((K.comap f).comap (f ⁻¹ᵁ U').ι).support : Set ↥(f ⁻¹ᵁ U').toScheme))) := by
  have e1 : (f ∣_ U') ≫ U'.ι = (f ⁻¹ᵁ U').ι ≫ f := morphismRestrict_ι ..
  have e5 : (K.comap f).comap (f ⁻¹ᵁ U').ι = (K.comap U'.ι).comap (f ∣_ U') := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, e1]
  rw [e5, coe_support_comap_consolidated175 (f ∣_ U') (K.comap U'.ι),
    preimage_base_preimage_base_of_comp_eq_consolidated175 (comapSubscheme_comp (f ∣_ U') Hd).symm
      (((K.comap U'.ι).support : Set ↥U'.toScheme))]
  exact h.preimage (comapSubscheme (f ∣_ U') Hd).base.hom.continuous


end

private theorem nonzeroOnComponents_comap_comapSubscheme_consolidated175 {k : Type u} [Field k] (hin : OpenImmersionStability k)
    {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] (U' : W.Opens)
    (Hd : U'.toScheme.IdealSheafData) (Jz : Hd.subscheme.IdealSheafData)
    (h : NonzeroOnComponents Jz) :
    NonzeroOnComponents (Jz.comap (comapSubscheme (f ∣_ U') Hd)) := by
  have : IsOpenImmersion (comapSubscheme (f ∣_ U') Hd) :=
    hin.isOpenImmersion_comapSubscheme (f ∣_ U') Hd
  exact hin.comap_nonzeroOnComponents (comapSubscheme (f ∣_ U') Hd) Jz h

private theorem exists_isOpen_comap_eq_comap_morphismRestrict_consolidated175 {V W : Scheme.{u}} (f : V ⟶ W) (U' : W.Opens)
    (Hd : U'.toScheme.IdealSheafData) (N : W.IdealSheafData) (Mem : Set ↥W)
    (Jz : Hd.subscheme.IdealSheafData)
    (h : ∀ x : ↥Hd.subscheme, (Hd.subschemeι ≫ U'.ι).base x ∉ Mem →
      ∃ V₀ : Hd.subscheme.Opens, x ∈ V₀ ∧
        Jz.comap V₀.ι = ((N.comap U'.ι).comap Hd.subschemeι).comap V₀.ι)
    (x : ↥(Hd.comap (f ∣_ U')).subscheme)
    (hx : ((Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι).base x ∉ ⇑f.base ⁻¹' Mem) :
    ∃ V₁ : (Hd.comap (f ∣_ U')).subscheme.Opens, x ∈ V₁ ∧
      (Jz.comap (comapSubscheme (f ∣_ U') Hd)).comap V₁.ι =
        (((N.comap f).comap (f ⁻¹ᵁ U').ι).comap
          (Hd.comap (f ∣_ U')).subschemeι).comap V₁.ι := by
  have e1 : (f ∣_ U') ≫ U'.ι = (f ⁻¹ᵁ U').ι ≫ f := morphismRestrict_ι ..
  have e2 : comapSubscheme (f ∣_ U') Hd ≫ Hd.subschemeι
      = (Hd.comap (f ∣_ U')).subschemeι ≫ (f ∣_ U') := comapSubscheme_comp ..
  have e3 : comapSubscheme (f ∣_ U') Hd ≫ Hd.subschemeι ≫ U'.ι
      = (Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι ≫ f := by
    rw [← Category.assoc, e2, Category.assoc, e1]
  have h9 : (Hd.subschemeι ≫ U'.ι).base ((comapSubscheme (f ∣_ U') Hd).base x)
      = f.base (((Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι).base x) :=
    congrArg (fun t : (Hd.comap (f ∣_ U')).subscheme ⟶ W => t.base x) e3
  have hx' : (Hd.subschemeι ≫ U'.ι).base ((comapSubscheme (f ∣_ U') Hd).base x) ∉ Mem := by
    intro hmem
    apply hx
    show f.base (((Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι).base x) ∈ Mem
    rw [← h9]
    exact hmem
  obtain ⟨V₀, hxV₀, hV₀⟩ := h _ hx'
  refine ⟨(comapSubscheme (f ∣_ U') Hd) ⁻¹ᵁ V₀, hxV₀, ?_⟩
  have hc := congrArg (fun K => Scheme.IdealSheafData.comap K
      ((comapSubscheme (f ∣_ U') Hd) ∣_ V₀)) hV₀
  have e7 : ((comapSubscheme (f ∣_ U') Hd) ⁻¹ᵁ V₀).ι ≫ comapSubscheme (f ∣_ U') Hd
      = ((comapSubscheme (f ∣_ U') Hd) ∣_ V₀) ≫ V₀.ι := (morphismRestrict_ι ..).symm
  have e8 : ((comapSubscheme (f ∣_ U') Hd) ⁻¹ᵁ V₀).ι ≫ (Hd.comap (f ∣_ U')).subschemeι ≫
        (f ⁻¹ᵁ U').ι ≫ f
      = ((comapSubscheme (f ∣_ U') Hd) ∣_ V₀) ≫ V₀.ι ≫ Hd.subschemeι ≫ U'.ι := by
    rw [← e3, ← Category.assoc, e7, Category.assoc]
  simp only [← Scheme.IdealSheafData.comap_comp] at hc ⊢
  rw [e7, e8]
  exact hc

private theorem principalizationCertificate_comapSubscheme_of_isOpenImmersion_consolidated175 {k : Type u} [Field k] (hin : OpenImmersionStability k)
    {V W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} (f : V ⟶ W) [IsOpenImmersion f]
    (U' : W.Opens) (Hd : U'.toScheme.IdealSheafData) (Z : W.IdealSheafData) (μ : ℕ)
    (Mem : Set ↥W) (Jz : Hd.subscheme.IdealSheafData)
    (h : IsPrincipalizationCertificateOnOpens_consolidated175 Hd.subscheme (Hd.subschemeι ≫ (U'.ι ≫ p)) Jz μ
      (⇑(Hd.subschemeι ≫ U'.ι).base ⁻¹' Mem) ((Z.comap U'.ι).comap Hd.subschemeι)) :
    PrincipalizationCertificate (Hd.comap (f ∣_ U')).subscheme
      ((Hd.comap (f ∣_ U')).subschemeι ≫ ((f ⁻¹ᵁ U').ι ≫ (f ≫ p)))
      (Jz.comap (comapSubscheme (f ∣_ U') Hd)) μ
      (⇑((Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι).base ⁻¹' (⇑f.base ⁻¹' Mem))
      (((Z.comap f).comap (f ⁻¹ᵁ U').ι).comap (Hd.comap (f ∣_ U')).subschemeι) := by
  have hq : IsOpenImmersion (comapSubscheme (f ∣_ U') Hd) :=
    hin.isOpenImmersion_comapSubscheme (f ∣_ U') Hd
  have e1 : (f ∣_ U') ≫ U'.ι = (f ⁻¹ᵁ U').ι ≫ f := morphismRestrict_ι ..
  have e2 : comapSubscheme (f ∣_ U') Hd ≫ Hd.subschemeι
      = (Hd.comap (f ∣_ U')).subschemeι ≫ (f ∣_ U') := comapSubscheme_comp ..
  have e3 : comapSubscheme (f ∣_ U') Hd ≫ Hd.subschemeι ≫ U'.ι
      = (Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι ≫ f := by
    rw [← Category.assoc, e2, Category.assoc, e1]
  have e3' : comapSubscheme (f ∣_ U') Hd ≫ (Hd.subschemeι ≫ U'.ι)
      = ((Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι) ≫ f := by
    rw [Category.assoc]; exact e3
  refine principalizationCertificate_congr_consolidated175 (h _ (comapSubscheme (f ∣_ U') Hd) hq) ?_ rfl ?_ ?_
  · have h5 := congrArg (fun t : (Hd.comap (f ∣_ U')).subscheme ⟶ W => t ≫ p) e3
    simpa only [Category.assoc] using h5
  · exact preimage_base_preimage_base_of_comp_eq_consolidated175 e3' Mem
  · simp only [← Scheme.IdealSheafData.comap_comp]
    rw [e3]

section
variable {k : Type u} [Field k] (hin : OpenImmersionStability k) {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
include hin

private theorem comapOrderCertificate_of_smoothDivisor_cover_consolidated175 {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData}
    (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (H : ∀ (z : ↥W) (hz : z ∈ Z.support), (U z hz).toScheme.IdealSheafData)
    (hH : ∀ (z : ↥W) (hz : z ∈ Z.support), IsSmoothDivisor ((U z hz).ι ≫ p) (H z hz))
    (hNsubH : ∀ (z : ↥W) (hz : z ∈ Z.support),
      (((N.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
        (((H z hz).support : Set ↥(U z hz).toScheme)))
    (hZH : ∀ (z : ↥W) (hz : z ∈ Z.support),
      (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
        (((H z hz).support : Set ↥(U z hz).toScheme)))
    (J : ∀ (z : ↥W) (hz : z ∈ Z.support), Option (H z hz).subscheme.IdealSheafData)
    (hJnone : ∀ (z : ↥W) (hz : z ∈ Z.support), J z hz = none →
      IsOpen (⇑(H z hz).subschemeι.base ⁻¹'
        (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme))))
    (hJcomp : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = some Jz → NonzeroOnComponents Jz)
    (hJloc : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = some Jz → ∀ x : ↥(H z hz).subscheme,
        ((H z hz).subschemeι ≫ (U z hz).ι).base x ∉ Mem →
        ∃ V₀ : (H z hz).subscheme.Opens, x ∈ V₀ ∧
          Jz.comap V₀.ι = ((N.comap (U z hz).ι).comap (H z hz).subschemeι).comap V₀.ι)
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = some Jz →
      IsPrincipalizationCertificateOnOpens_consolidated175 (H z hz).subscheme ((H z hz).subschemeι ≫ ((U z hz).ι ≫ p)) Jz μ
        (⇑((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
        ((Z.comap (U z hz).ι).comap (H z hz).subschemeι)) :
    IsOrderCertificateOnOpens_consolidated175 W p N μ Mem Z := by
  intro V f hf
  have : IsOpenImmersion f := hf
  have hsup : ∀ (y : ↥V), y ∈ (Z.comap f).support → f.base y ∈ Z.support := by
    intro y hy
    have h1 : y ∈ ((Z.comap f).support : Set ↥V) := hy
    rw [coe_support_comap_consolidated175] at h1
    exact h1
  refine OrderCertificate.descend (fun y hy => f ⁻¹ᵁ U (f.base y) (hsup y hy))
    (fun y hy => hU _ _)
    (fun y hy => (H (f.base y) (hsup y hy)).comap (f ∣_ U (f.base y) (hsup y hy)))
    (fun y hy => isSmoothDivisor_comap_morphismRestrict_consolidated175 hin f (U (f.base y) (hsup y hy))
      (H (f.base y) (hsup y hy)) (hH _ _))
    (fun y hy => support_comap_morphismRestrict_subset_consolidated175 f (U (f.base y) (hsup y hy)) (H (f.base y) (hsup y hy)) N
      (hNsubH _ _))
    (fun y hy => support_comap_morphismRestrict_subset_consolidated175 f (U (f.base y) (hsup y hy)) (H (f.base y) (hsup y hy)) Z
      (hZH _ _))
    (fun y hy => (J (f.base y) (hsup y hy)).map (fun Jz =>
      Jz.comap (comapSubscheme (f ∣_ U (f.base y) (hsup y hy)) (H (f.base y) (hsup y hy)))))
    ?_ ?_ ?_ ?_
  · intro y hy hnone
    have hJn : J (f.base y) (hsup y hy) = none := by
      cases hJ : J (f.base y) (hsup y hy) with
      | none => rfl
      | some Jz =>
          rw [hJ] at hnone
          simp at hnone
    exact isOpen_preimage_support_comap_morphismRestrict_consolidated175 f (U (f.base y) (hsup y hy)) (H (f.base y) (hsup y hy)) Z
      (hJnone _ _ hJn)
  · intro y hy Jz' hsome
    cases hJ : J (f.base y) (hsup y hy) with
    | none =>
        rw [hJ] at hsome
        simp at hsome
    | some Jz =>
        rw [hJ] at hsome
        have hJz : Jz.comap (comapSubscheme (f ∣_ U (f.base y) (hsup y hy))
            (H (f.base y) (hsup y hy))) = Jz' := Option.some.inj hsome
        subst hJz
        exact nonzeroOnComponents_comap_comapSubscheme_consolidated175 hin f (U (f.base y) (hsup y hy))
          (H (f.base y) (hsup y hy)) Jz (hJcomp _ _ Jz hJ)
  · intro y hy Jz' hsome x hx
    cases hJ : J (f.base y) (hsup y hy) with
    | none =>
        rw [hJ] at hsome
        simp at hsome
    | some Jz =>
        rw [hJ] at hsome
        have hJz : Jz.comap (comapSubscheme (f ∣_ U (f.base y) (hsup y hy))
            (H (f.base y) (hsup y hy))) = Jz' := Option.some.inj hsome
        subst hJz
        exact exists_isOpen_comap_eq_comap_morphismRestrict_consolidated175 f (U (f.base y) (hsup y hy)) (H (f.base y) (hsup y hy)) N Mem Jz
          (hJloc _ _ Jz hJ) x hx
  · intro y hy Jz' hsome
    cases hJ : J (f.base y) (hsup y hy) with
    | none =>
        rw [hJ] at hsome
        simp at hsome
    | some Jz =>
        rw [hJ] at hsome
        have hJz : Jz.comap (comapSubscheme (f ∣_ U (f.base y) (hsup y hy))
            (H (f.base y) (hsup y hy))) = Jz' := Option.some.inj hsome
        subst hJz
        exact principalizationCertificate_comapSubscheme_of_isOpenImmersion_consolidated175 hin f (U (f.base y) (hsup y hy)) (H (f.base y) (hsup y hy)) Z μ Mem
          Jz (ih _ _ Jz hJ)

private theorem comapPrincipalizationCertificate_of_principalizationCertificate_consolidated175 {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z) :
    IsPrincipalizationCertificateOnOpens_consolidated175 W p I m Mem Z :=
  PrincipalizationCertificate.rec (motive_1 := fun W p I m Mem Z _ => IsPrincipalizationCertificateOnOpens_consolidated175 W p I m Mem Z)
    (motive_2 := fun W p N μ Mem Z _ => IsOrderCertificateOnOpens_consolidated175 W p N μ Mem Z)
    (fun h => comapPrincipalizationCertificate_of_support_subset_consolidated175 h)
    (fun hm => comapPrincipalizationCertificate_of_two_le_consolidated175 hm)
    (fun M N μ hI hM hmu hZ _ ih => comapPrincipalizationCertificate_of_mul_of_order_consolidated175 M N μ hI hM hmu hZ ih)
    (fun U hU _ ih => comapPrincipalizationCertificate_of_open_cover_consolidated175 U hU ih)
    (fun h => comapOrderCertificate_of_support_subset_consolidated175 h)
    (fun hmu => comapOrderCertificate_of_two_le_consolidated175 hmu)
    (fun U hU _ ih => comapOrderCertificate_of_open_cover_consolidated175 U hU ih)
    (fun U hU H hH hNsubH hZH J hJnone hJcomp hJloc _ ih =>
      comapOrderCertificate_of_smoothDivisor_cover_consolidated175 hin U hU H hH hNsubH hZH J hJnone hJcomp hJloc ih)
    h

private theorem comapOrderCertificate_of_orderCertificate_consolidated175 {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : OrderCertificate W p N μ Mem Z) :
    IsOrderCertificateOnOpens_consolidated175 W p N μ Mem Z :=
  OrderCertificate.rec (motive_1 := fun W p I m Mem Z _ => IsPrincipalizationCertificateOnOpens_consolidated175 W p I m Mem Z)
    (motive_2 := fun W p N μ Mem Z _ => IsOrderCertificateOnOpens_consolidated175 W p N μ Mem Z)
    (fun h => comapPrincipalizationCertificate_of_support_subset_consolidated175 h)
    (fun hm => comapPrincipalizationCertificate_of_two_le_consolidated175 hm)
    (fun M N μ hI hM hmu hZ _ ih => comapPrincipalizationCertificate_of_mul_of_order_consolidated175 M N μ hI hM hmu hZ ih)
    (fun U hU _ ih => comapPrincipalizationCertificate_of_open_cover_consolidated175 U hU ih)
    (fun h => comapOrderCertificate_of_support_subset_consolidated175 h)
    (fun hmu => comapOrderCertificate_of_two_le_consolidated175 hmu)
    (fun U hU _ ih => comapOrderCertificate_of_open_cover_consolidated175 U hU ih)
    (fun U hU H hH hNsubH hZH J hJnone hJcomp hJloc _ ih =>
      comapOrderCertificate_of_smoothDivisor_cover_consolidated175 hin U hU H hH hNsubH hZH J hJnone hJcomp hJloc ih)
    h

theorem PrincipalizationCertificate.comap_of_openImmersionStability {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z)
    {V : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] :
    PrincipalizationCertificate V (f ≫ p) (I.comap f) m (f.base ⁻¹' Mem) (Z.comap f) :=
  comapPrincipalizationCertificate_of_principalizationCertificate_consolidated175 hin h V f inferInstance

theorem OrderCertificate.comap_of_isOpenImmersion {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : OrderCertificate W p N μ Mem Z)
    {V : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] :
    OrderCertificate V (f ≫ p) (N.comap f) μ (f.base ⁻¹' Mem) (Z.comap f) :=
  comapOrderCertificate_of_orderCertificate_consolidated175 hin h V f inferInstance


end

theorem OrderCertificate.restrict {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : OrderCertificate W p N μ Mem Z)
    (hin : OpenImmersionStability k) (U : W.Opens) :
    OrderCertificate U.toScheme (U.ι ≫ p) (N.comap U.ι) μ (U.ι.base ⁻¹' Mem) (Z.comap U.ι) :=
  h.comap_of_isOpenImmersion hin U.ι

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificateMonotone
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

section
variable {k : Type u} [Field k] {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}

private theorem forall_principalizationCertificate_of_subset_consolidated107 {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z) :
    ∀ Mem' : Set ↥W, Mem ⊆ Mem' → PrincipalizationCertificate W p I m Mem' Z := by
  refine PrincipalizationCertificate.rec
    (motive_1 := fun W p I m Mem Z _ =>
      ∀ Mem' : Set ↥W, Mem ⊆ Mem' → PrincipalizationCertificate W p I m Mem' Z)
    (motive_2 := fun W p N μ Mem Z _ =>
      ∀ Mem' : Set ↥W, Mem ⊆ Mem' → OrderCertificate W p N μ Mem' Z)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro W p I m Mem Z hmem Mem' hsub
    exact PrincipalizationCertificate.memory (Set.Subset.trans hmem hsub)
  · intro W p I m Mem Z hm Mem' _
    exact PrincipalizationCertificate.large hm
  · intro W p I m Mem Z M N μ hI hM hmu hZ _ ih Mem' hsub
    exact PrincipalizationCertificate.toOrder M N μ hI (Set.Subset.trans hM hsub) hmu hZ (ih Mem' hsub)
  · intro W p I m Mem Z U hU _ ih Mem' hsub
    refine PrincipalizationCertificate.localize U hU ?_
    intro z hz
    exact ih z hz ((U z hz).ι.base ⁻¹' Mem') (Set.preimage_mono hsub)
  · intro W p N μ Mem Z hmem Mem' hsub
    exact OrderCertificate.memory (Set.Subset.trans hmem hsub)
  · intro W p N μ Mem Z hmu Mem' _
    exact OrderCertificate.large hmu
  · intro W p N μ Mem Z U hU _ ih Mem' hsub
    refine OrderCertificate.localize U hU ?_
    intro z hz
    exact ih z hz ((U z hz).ι.base ⁻¹' Mem') (Set.preimage_mono hsub)
  · intro W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc _ ih Mem' hsub
    refine OrderCertificate.descend U hU H hH hNsubH hZH J hJnone hJcomp ?_ ?_
    · intro z hz Jz hJz x hx
      exact hJloc z hz Jz hJz x fun hmem => hx (hsub hmem)
    · intro z hz Jz hJz
      exact ih z hz Jz hJz (((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem')
        (Set.preimage_mono hsub)

theorem principalizationCertificate_mono_of_subset {I : W.IdealSheafData} {m : ℕ}
    {Mem Mem' : Set ↥W} {Z : W.IdealSheafData} (hsub : Mem ⊆ Mem')
    (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W p I m Mem' Z :=
  forall_principalizationCertificate_of_subset_consolidated107 h Mem' hsub

private theorem forall_orderCertificate_of_subset_consolidated107 {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : OrderCertificate W p N μ Mem Z) :
    ∀ Mem' : Set ↥W, Mem ⊆ Mem' → OrderCertificate W p N μ Mem' Z := by
  refine @OrderCertificate.rec k ‹Field k›
    (fun W p I m Mem Z _ => ∀ Mem' : Set ↥W, Mem ⊆ Mem' → PrincipalizationCertificate W p I m Mem' Z)
    (fun W p N μ Mem Z _ => ∀ Mem' : Set ↥W, Mem ⊆ Mem' → OrderCertificate W p N μ Mem' Z)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ W p N μ Mem Z h
  · intro W p I m Mem Z hmem Mem' hs
    exact PrincipalizationCertificate.memory (Set.Subset.trans hmem hs)
  · intro W p I m Mem Z hm Mem' _
    exact PrincipalizationCertificate.large hm
  · intro W p I m Mem Z M N μ hI hM hmu hZ _ ih Mem' hs
    exact PrincipalizationCertificate.toOrder M N μ hI (Set.Subset.trans hM hs) hmu hZ (ih Mem' hs)
  · intro W p I m Mem Z U hU _ ih Mem' hs
    exact PrincipalizationCertificate.localize U hU fun z hz =>
      ih z hz ((U z hz).ι.base ⁻¹' Mem') (Set.preimage_mono hs)
  · intro W p N μ Mem Z hmem Mem' hs
    exact OrderCertificate.memory (Set.Subset.trans hmem hs)
  · intro W p N μ Mem Z hmu Mem' _
    exact OrderCertificate.large hmu
  · intro W p N μ Mem Z U hU _ ih Mem' hs
    exact OrderCertificate.localize U hU fun z hz =>
      ih z hz ((U z hz).ι.base ⁻¹' Mem') (Set.preimage_mono hs)
  · intro W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc _ ih Mem' hs
    refine OrderCertificate.descend U hU H hH hNsubH hZH J hJnone hJcomp ?_ ?_
    · intro z hz Jz hJ x hx
      exact hJloc z hz Jz hJ x fun hm => hx (hs hm)
    · intro z hz Jz hJ
      exact ih z hz Jz hJ (((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem')
        (Set.preimage_mono hs)

theorem orderCertificate_mono_of_subset {N : W.IdealSheafData} {μ : ℕ}
    {Mem Mem' : Set ↥W} {Z : W.IdealSheafData} (hsub : Mem ⊆ Mem')
    (h : OrderCertificate W p N μ Mem Z) :
    OrderCertificate W p N μ Mem' Z :=
  forall_orderCertificate_of_subset_consolidated107 h Mem' hsub


end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
section
section


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

section
namespace FunctorialResolution.EmbeddedResolution

structure SequenceOfBlowups (X : Scheme.{u}) : Type (u + 1) where
  length : ℕ
  tower : ℕᵒᵖ ⥤ Scheme.{u}
  isoZero : tower.obj (op 0) ≅ X
  center : ∀ i : ℕ, (tower.obj (op i)).IdealSheafData
  isBlowup : ∀ i : ℕ, i < length →
    Blowup.IsBlowupAlongIdealSheaf (tower.map (homOfLE (Nat.le_succ i)).op) (center i)

namespace SequenceOfBlowups

variable {X : Scheme.{u}}

abbrev schemeAt (s : SequenceOfBlowups X) (i : ℕ) : Scheme.{u} := s.tower.obj (op i)

def transitionMap (s : SequenceOfBlowups X) {i i' : ℕ} (h : i ≤ i') : s.schemeAt i' ⟶ s.schemeAt i :=
  s.tower.map (homOfLE h).op

def transitionMapSucc (s : SequenceOfBlowups X) (i : ℕ) : s.schemeAt (i + 1) ⟶ s.schemeAt i :=
  s.transitionMap (Nat.le_succ i)

def projectionToBase (s : SequenceOfBlowups X) (i : ℕ) : s.schemeAt i ⟶ X :=
  s.transitionMap (Nat.zero_le i) ≫ s.isoZero.hom

abbrev lastObj (s : SequenceOfBlowups X) : Scheme.{u} := s.schemeAt s.length

def lastStructMap (s : SequenceOfBlowups X) : s.lastObj ⟶ X := s.projectionToBase s.length

theorem transitionMap_comp_projectionToBase (s : SequenceOfBlowups X) {i i' : ℕ} (h : i ≤ i') :
    s.transitionMap h ≫ s.projectionToBase i = s.projectionToBase i' :=
  Eq.trans (Category.assoc (s.transitionMap h) (s.transitionMap (Nat.zero_le i)) s.isoZero.hom).symm
    (congrArg (fun g => g ≫ s.isoZero.hom)
      (show s.transitionMap h ≫ s.transitionMap (Nat.zero_le i) = s.transitionMap (Nat.zero_le i') from
        (s.tower.map_comp (homOfLE h).op (homOfLE (Nat.zero_le i)).op).symm))

def pullbackTransitionMap (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) {i i' : ℕ} (h : i ≤ i') :
    pullback φ (s.projectionToBase i') ⟶ pullback φ (s.projectionToBase i) :=
  pullback.map φ (s.projectionToBase i') φ (s.projectionToBase i) (𝟙 X') (s.transitionMap h) (𝟙 X)
    ((Category.comp_id φ).trans (Category.id_comp φ).symm)
    ((Category.comp_id (s.projectionToBase i')).trans (s.transitionMap_comp_projectionToBase h).symm)

def CentersLieOver (s : SequenceOfBlowups X) (S : Set X) : Prop :=
  ∀ i : ℕ, i < s.length → ∀ x ∈ (s.center i).support, (s.projectionToBase i).base x ∈ S

end SequenceOfBlowups

def smoothLocusComplement {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    TopologicalSpace.Closeds X :=
  ⟨(f.smoothLocus : Set X)ᶜ, isClosed_compl_iff.mpr f.smoothLocus.isOpen⟩

def reducedInverseImage {X X' : Scheme.{u}} (f : X' ⟶ X) (S : TopologicalSpace.Closeds X) :
    X'.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨f.base ⁻¹' (S : Set X), IsClosed.preimage f.base.hom.continuous S.2⟩

def IsRegularParameterSystem (R : Type v) [CommRing R] [IsLocalRing R] (n : ℕ)
    (x : Fin n → R) : Prop :=
  Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R ∧ (n : WithBot ℕ∞) = ringKrullDim R

def IsStrictNormalCrossingsDivisor {Y : Scheme.{u}} (D : Y.IdealSheafData) : Prop :=
  ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) ∧
    ∃ (U : Y.affineOpens) (hy : y ∈ U.1) (n : ℕ) (f : Fin n → Γ(Y, U.1)) (J : Finset (Fin n)),
      IsRegularParameterSystem (Y.presheaf.stalk y) n
          (fun i => Y.presheaf.germ U.1 y hy (f i)) ∧
        D.ideal U = Ideal.span {∏ i ∈ J, f i}

def IsPullbackBlowupSequence {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : SequenceOfBlowups X') (s : SequenceOfBlowups X) :
    Prop :=
  ∃ (r : ℕ → ℕ)
    (e : ∀ i, i ≤ s'.length →
      @CategoryTheory.Iso Scheme.{u} _ (s'.schemeAt i) (pullback φ (s.projectionToBase (r i)))),
    (∀ i, i < s'.length → r i < s.length) ∧
    (∀ i j, j ≤ s'.length → i < j → r i < r j) ∧
    r s'.length = s.length ∧
    (∀ i, i < s.length →
      ((∃ x, x ∈ ((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support) ↔
        ∃ j, j < s'.length ∧ r j = i)) ∧
    (∀ i, ∀ hi : i ≤ s'.length,
      (e i hi).hom ≫ pullback.fst φ (s.projectionToBase (r i)) = s'.projectionToBase i) ∧
    (∀ i, ∀ hi : i < s'.length, ∀ hr : r i ≤ r (i + 1),
      s'.transitionMapSucc i ≫ (e i hi.le).hom = (e (i + 1) hi).hom ≫ s.pullbackTransitionMap φ hr) ∧
    (∀ i, ∀ hi : i < s'.length,
      s'.center i
        = (s.center (r i)).comap ((e i hi.le).hom ≫ pullback.snd φ (s.projectionToBase (r i))))

abbrev specMapAlgebraMap (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

abbrev baseChange {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
    (K : Type u) [Field K] [Algebra k K] : Scheme.{u} :=
  pullback p (specMapAlgebraMap k K)

abbrev baseChangeProjection {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
    (K : Type u) [Field K] [Algebra k K] : baseChange p K ⟶ X :=
  pullback.fst p (specMapAlgebraMap k K)

abbrev baseChangeToSpec {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (K : Type u) [Field K] [Algebra k K] :
    baseChange p K ⟶ Spec (CommRingCat.of K) :=
  pullback.snd p (specMapAlgebraMap k K)

abbrev ResolutionRule : Type (u + 1) :=
  ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsReduced X],
    SequenceOfBlowups X

def IsStrongResolutionRule (R : ResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsReduced X],
    Smooth ((R k X f).lastStructMap ≫ f) ∧
    IsProper (R k X f).lastStructMap ∧
    CategoryTheory.IsIso
      (AlgebraicGeometry.morphismRestrict (R k X f).lastStructMap f.smoothLocus) ∧
    Dense ((R k X f).lastStructMap.base ⁻¹' (f.smoothLocus : Set X)) ∧
    (R k X f).CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds X) : Set X) ∧
    IsStrictNormalCrossingsDivisor (reducedInverseImage (R k X f).lastStructMap (smoothLocusComplement f))

def IsCompatibleWithSmoothMorphisms (R : ResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X X' : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    [IsReduced X]
    [LocallyOfFiniteType f'] [QuasiCompact f']
    [IsReduced X']
    (φ : X' ⟶ X) (r : ℕ) [SmoothOfRelativeDimension r φ],
    φ ≫ f = f' → IsPullbackBlowupSequence φ (R k X' f') (R k X f)

def IsCompatibleWithFieldExtension (R : ResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsReduced X]
    (K : Type u) [Field K] [CharZero K] [Algebra k K]
    [IsReduced (baseChange f K)],
    IsPullbackBlowupSequence (baseChangeProjection f K)
      (R K (baseChange f K) (baseChangeToSpec f K)) (R k X f)

def StrongResolutionOfSingularitiesCharZero : Prop :=
  ∃ R : ResolutionRule.{u},
    IsStrongResolutionRule R ∧ IsCompatibleWithSmoothMorphisms R ∧ IsCompatibleWithFieldExtension R

end FunctorialResolution.EmbeddedResolution

end

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartFiberProduct
section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

abbrev affineSpaceCoord (k : Type u) [Field k] (m : ℕ) (j : Fin m) :=
  AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m))

section

variable {X : Scheme.{u}} {k : Type u} [Field k] {q : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}

@[reducible] def EtaleChart.coordTop (c : EtaleChart q U m) (j : Fin m) :
    U.toScheme.presheaf.obj (op ⊤) :=
  c.map.appTop.hom (affineSpaceCoord k m j)

end

def pointOfMem {P : Scheme.{u}} (V : P.Opens) (p : ↥P) (hp : p ∈ V) : ↥(V.toScheme) :=
  ⟨p, hp⟩

def specResidueFieldPoint {X : Scheme.{u}} (x : ↥X) : ↥(Spec (X.residueField x)) :=
  (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.residueField x))

section

variable {P : Scheme.{u}} {k : Type u} [Field k] {q : P ⟶ Spec (CommRingCat.of k)}
  {V : P.Opens} {n : ℕ}

abbrev chartPullback (c₁ c₂ : EtaleChart q V n) : Scheme.{u} := pullback c₁.map c₂.map

abbrev chartPullbackFst (c₁ c₂ : EtaleChart q V n) : chartPullback c₁ c₂ ⟶ P :=
  pullback.fst c₁.map c₂.map ≫ V.ι

abbrev chartPullbackSnd (c₁ c₂ : EtaleChart q V n) : chartPullback c₁ c₂ ⟶ P :=
  pullback.snd c₁.map c₂.map ≫ V.ι

theorem etale_pullback_fst_map (c₁ c₂ : EtaleChart q V n) :
    Etale (pullback.fst c₁.map c₂.map) := by
  have : Etale c₂.map := c₂.isEtale
  infer_instance

instance instEtalePullbackFstChart (c₁ c₂ : EtaleChart q V n) :
    Etale (pullback.fst c₁.map c₂.map) :=
  etale_pullback_fst_map c₁ c₂

theorem etale_pullback_snd_map (c₁ c₂ : EtaleChart q V n) :
    Etale (pullback.snd c₁.map c₂.map) := by
  have h1 : Etale c₁.map := c₁.isEtale
  have h2 : Etale c₂.map := c₂.isEtale
  exact inferInstance

instance instEtalePullbackSndChart (c₁ c₂ : EtaleChart q V n) :
    Etale (pullback.snd c₁.map c₂.map) :=
  etale_pullback_snd_map c₁ c₂

private theorem etale_comp_consolidated61 {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : Etale f) (hg : Etale g) :
    Etale (f ≫ g) := by
  have := hf
  have := hg
  infer_instance

theorem etale_chartPullbackFst (c₁ c₂ : EtaleChart q V n) :
    Etale (chartPullbackFst c₁ c₂) := by
  have h₁ : Etale (pullback.fst c₁.map c₂.map) :=
    etale_pullback_fst_map c₁ c₂
  have h₂ : Etale V.ι := inferInstance
  show Etale (pullback.fst c₁.map c₂.map ≫ V.ι)
  exact etale_comp_consolidated61 _ _ h₁ h₂

instance instEtaleChartPairFst (c₁ c₂ : EtaleChart q V n) :
    Etale (chartPullbackFst c₁ c₂) :=
  etale_chartPullbackFst c₁ c₂

theorem etale_chartPullbackSnd (c₁ c₂ : EtaleChart q V n) :
    Etale (chartPullbackSnd c₁ c₂) := by
  have h₁ : Etale (pullback.snd c₁.map c₂.map) :=
    etale_pullback_snd_map c₁ c₂
  have h₂ : Etale V.ι := inferInstance
  show Etale (pullback.snd c₁.map c₂.map ≫ V.ι)
  exact etale_comp_consolidated61 _ _ h₁ h₂

instance instEtaleChartPairSnd (c₁ c₂ : EtaleChart q V n) :
    Etale (chartPullbackSnd c₁ c₂) :=
  etale_chartPullbackSnd c₁ c₂

private theorem appTop_comp_apply_consolidated61 {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (x : C.presheaf.obj (op ⊤)) :
    (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := rfl

section
variable (c₁ c₂ : EtaleChart q V n)

theorem chartPullback_coordTop_eq (j : Fin n) :
    (pullback.fst c₁.map c₂.map).appTop.hom (c₁.coordTop j) =
      (pullback.snd c₁.map c₂.map).appTop.hom (c₂.coordTop j) := by
  have h : (pullback.fst c₁.map c₂.map ≫ c₁.map).appTop.hom (affineSpaceCoord k n j)
      = (pullback.snd c₁.map c₂.map ≫ c₂.map).appTop.hom (affineSpaceCoord k n j) := by
    rw [pullback.condition]
  rw [appTop_comp_apply_consolidated61, appTop_comp_apply_consolidated61] at h
  exact h

theorem chartPullbackFst_comp_eq_chartPullbackSnd_comp :
    chartPullbackFst c₁ c₂ ≫ q = chartPullbackSnd c₁ c₂ ≫ q := by
  have h : (pullback.fst c₁.map c₂.map ≫ c₁.map) ≫ affineSpaceFinToSpec k n
      = (pullback.snd c₁.map c₂.map ≫ c₂.map) ≫ affineSpaceFinToSpec k n := by
    rw [pullback.condition]
  rw [Category.assoc, Category.assoc] at h
  rw [c₁.comp_struct, c₂.comp_struct] at h
  simpa only [Category.assoc] using h

theorem chartPullback_comap_coordIdeal_eq (S : Finset (Fin n)) :
    (c₁.coordIdeal S).comap (pullback.fst c₁.map c₂.map) =
      (c₂.coordIdeal S).comap (pullback.snd c₁.map c₂.map) := by
  rw [c₁.coordIdeal_eq_comap_coordSubspaceIdeal S, c₂.coordIdeal_eq_comap_coordSubspaceIdeal S, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, pullback.condition]


end

abbrev ChartsAgreeAt (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V) : Prop :=
  V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ c₁.map =
    V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ c₂.map

def chartPullbackLift (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    Spec (V.toScheme.residueField (pointOfMem V p hp)) ⟶ chartPullback c₁ c₂ :=
  pullback.lift (V.toScheme.fromSpecResidueField (pointOfMem V p hp))
    (V.toScheme.fromSpecResidueField (pointOfMem V p hp)) h

section
variable (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V) (h : ChartsAgreeAt c₁ c₂ p hp)

@[simp] theorem chartPullbackLift_fst :
    chartPullbackLift c₁ c₂ p hp h ≫ pullback.fst c₁.map c₂.map =
      V.toScheme.fromSpecResidueField (pointOfMem V p hp) :=
  pullback.lift_fst _ _ _

@[simp] theorem chartPullbackLift_snd :
    chartPullbackLift c₁ c₂ p hp h ≫ pullback.snd c₁.map c₂.map =
      V.toScheme.fromSpecResidueField (pointOfMem V p hp) :=
  pullback.lift_snd _ _ _


end

@[simp] theorem chartPullbackLift_fst_assoc {W : Scheme.{u}} (c₁ c₂ : EtaleChart q V n) (p : ↥P)
    (hp : p ∈ V) (h : ChartsAgreeAt c₁ c₂ p hp) (g : V.toScheme ⟶ W) :
    chartPullbackLift c₁ c₂ p hp h ≫ pullback.fst c₁.map c₂.map ≫ g =
      V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ g := by
  rw [← Category.assoc, chartPullbackLift_fst]

@[simp] theorem chartPullbackLift_snd_assoc {W : Scheme.{u}} (c₁ c₂ : EtaleChart q V n) (p : ↥P)
    (hp : p ∈ V) (h : ChartsAgreeAt c₁ c₂ p hp) (g : V.toScheme ⟶ W) :
    chartPullbackLift c₁ c₂ p hp h ≫ pullback.snd c₁.map c₂.map ≫ g =
      V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ g := by
  rw [← Category.assoc, chartPullbackLift_snd]

def chartPullbackPoint (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) : ↥(chartPullback c₁ c₂) :=
  (chartPullbackLift c₁ c₂ p hp h).base (specResidueFieldPoint (pointOfMem V p hp))

theorem chartPullbackFst_base_chartPullbackPoint (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    (chartPullbackFst c₁ c₂).base (chartPullbackPoint c₁ c₂ p hp h) = p := by
  have hfs : (V.toScheme.fromSpecResidueField (pointOfMem V p hp)).base
      (specResidueFieldPoint (pointOfMem V p hp)) = pointOfMem V p hp := by
    simp
  have e : (chartPullbackLift c₁ c₂ p hp h ≫ pullback.fst c₁.map c₂.map).base
      (specResidueFieldPoint (pointOfMem V p hp)) = pointOfMem V p hp := by
    rw [chartPullbackLift_fst]
    exact hfs
  have key : (pullback.fst c₁.map c₂.map).base (chartPullbackPoint c₁ c₂ p hp h)
      = pointOfMem V p hp := e
  have key2 : V.ι.base ((pullback.fst c₁.map c₂.map).base (chartPullbackPoint c₁ c₂ p hp h))
      = V.ι.base (pointOfMem V p hp) := by rw [key]
  exact key2

private theorem comp_base_apply_consolidated61 {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (x : ↥A) : (f ≫ g).base x = g.base (f.base x) := rfl

theorem chartPullbackSnd_base_chartPullbackPoint (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    (chartPullbackSnd c₁ c₂).base (chartPullbackPoint c₁ c₂ p hp h) = p := by
  have key := chartPullbackLift_snd_assoc c₁ c₂ p hp h V.ι
  have e1 : (V.toScheme.fromSpecResidueField (pointOfMem V p hp)).base
      (specResidueFieldPoint (pointOfMem V p hp)) = pointOfMem V p hp := by
    simp
  have e2 : V.ι.base (pointOfMem V p hp) = p := rfl
  have hA := comp_base_apply_consolidated61 (chartPullbackLift c₁ c₂ p hp h)
      (pullback.snd c₁.map c₂.map ≫ V.ι) (specResidueFieldPoint (pointOfMem V p hp))
  have hB := comp_base_apply_consolidated61
      (V.toScheme.fromSpecResidueField (pointOfMem V p hp)) V.ι
      (specResidueFieldPoint (pointOfMem V p hp))
  have h3 : (chartPullbackLift c₁ c₂ p hp h ≫ pullback.snd c₁.map c₂.map ≫ V.ι).base
        (specResidueFieldPoint (pointOfMem V p hp))
      = (V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ V.ι).base
        (specResidueFieldPoint (pointOfMem V p hp)) := by
    rw [key]
  exact hA.symm.trans (h3.trans (hB.trans ((congrArg (fun z => V.ι.base z) e1).trans e2)))

private theorem affineSpaceFin_hom_ext_consolidated61 {K : Type u} [Field K] {m : ℕ} {Z : Scheme.{u}}
    (f g : Z ⟶ affineSpaceFin K m)
    (h₁ : f ≫ affineSpaceFinToSpec K m = g ≫ affineSpaceFinToSpec K m)
    (h₂ : ∀ i : ULift.{u} (Fin m),
      f.appTop.hom (AffineSpace.coord (Spec (CommRingCat.of K)) i) =
        g.appTop.hom (AffineSpace.coord (Spec (CommRingCat.of K)) i)) :
    f = g := by
  apply AffineSpace.hom_ext
  · exact h₁
  · exact h₂

private theorem not_isUnit_of_mem_maximalIdeal_consolidated61 {R : Type u} [CommRing R] [IsLocalRing R] {a : R}
    (ha : a ∈ IsLocalRing.maximalIdeal R) : ¬ IsUnit a :=
  (IsLocalRing.mem_maximalIdeal a).mp ha

section
variable {X : Scheme.{u}} (x : ↥X)

private theorem specResidueField_eq_zero_of_not_isUnit_consolidated61 (t : Γ(Spec (X.residueField x), ⊤)) (ht : ¬ IsUnit t) : t = 0 := by
  have h2 : (Scheme.ΓSpecIso (X.residueField x)).inv.hom
      ((Scheme.ΓSpecIso (X.residueField x)).hom.hom t) = t := by
    have e1 := congrArg CommRingCat.Hom.hom
      (Iso.hom_inv_id (Scheme.ΓSpecIso (X.residueField x)))
    rw [CommRingCat.hom_comp, CommRingCat.hom_id] at e1
    exact DFunLike.congr_fun e1 t
  by_contra hne
  have hne0 : (Scheme.ΓSpecIso (X.residueField x)).hom.hom t ≠ 0 := by
    intro h0
    apply hne
    rw [← h2, h0]
    exact map_zero _
  have hu : IsUnit ((Scheme.ΓSpecIso (X.residueField x)).hom.hom t) :=
    isUnit_iff_ne_zero.mpr hne0
  have hu2 : IsUnit ((Scheme.ΓSpecIso (X.residueField x)).inv.hom
      ((Scheme.ΓSpecIso (X.residueField x)).hom.hom t)) :=
    hu.map (Scheme.ΓSpecIso (X.residueField x)).inv.hom
  rw [h2] at hu2
  exact ht hu2

private theorem fromSpecResidueField_appTop_eq_zero_consolidated61 (hx : x ∈ (⊤ : X.Opens)) (s : Γ(X, ⊤))
    (hs : (X.presheaf.germ ⊤ x hx).hom s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    (X.fromSpecResidueField x).appTop.hom s = 0 := by
  have hxb : x ∉ X.basicOpen s := fun hmem =>
    not_isUnit_of_mem_maximalIdeal_consolidated61 hs ((X.mem_basicOpen_top s x).1 hmem)
  have hy : (X.fromSpecResidueField x).base (specResidueFieldPoint x) = x := by simp
  have hynot : specResidueFieldPoint x ∉ (Spec (X.residueField x)).basicOpen
      ((X.fromSpecResidueField x).appTop.hom s) := by
    intro hmem
    have h1 : specResidueFieldPoint x ∈ (X.fromSpecResidueField x) ⁻¹ᵁ (X.basicOpen s) := by
      rw [Scheme.preimage_basicOpen]
      exact hmem
    have h2 : (X.fromSpecResidueField x).base (specResidueFieldPoint x) ∈ X.basicOpen s := h1
    rw [hy] at h2
    exact hxb h2
  have hnu : ¬ IsUnit ((X.fromSpecResidueField x).appTop.hom s) := by
    intro hu
    apply hynot
    rw [Scheme.mem_basicOpen_top]
    exact hu.map
      ((Spec (X.residueField x)).presheaf.germ ⊤ (specResidueFieldPoint x) (by trivial)).hom
  exact specResidueField_eq_zero_of_not_isUnit_consolidated61 x _ hnu


end

theorem chartsAgreeAt_of_germ_sub_mem_maximalIdeal (c₁ c₂ : EtaleChart q V n) (p : ↥P)
    (hp : p ∈ V)
    (h : ∀ j : Fin n,
      (V.toScheme.presheaf.germ ⊤ (pointOfMem V p hp) (by trivial)).hom
          (c₁.coordTop j - c₂.coordTop j) ∈
        IsLocalRing.maximalIdeal (V.toScheme.presheaf.stalk (pointOfMem V p hp))) :
    ChartsAgreeAt c₁ c₂ p hp := by
  have hover : (V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ c₁.map) ≫
        affineSpaceFinToSpec k n =
      (V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ c₂.map) ≫
        affineSpaceFinToSpec k n := by
    rw [Category.assoc, Category.assoc, c₁.comp_struct, c₂.comp_struct]
  refine affineSpaceFin_hom_ext_consolidated61 _ _ hover ?_
  rintro ⟨j⟩
  have h0 := fromSpecResidueField_appTop_eq_zero_consolidated61 (pointOfMem V p hp) (by trivial)
    (c₁.coordTop j - c₂.coordTop j) (h j)
  rw [map_sub, sub_eq_zero] at h0
  rw [appTop_comp_apply_consolidated61, appTop_comp_apply_consolidated61]
  exact h0

end

section

variable {P : Scheme.{u}} {k : Type u} [Field k] {q : P ⟶ Spec (CommRingCat.of k)}
  {V : P.Opens} {n : ℕ}

def chartPullbackFstStalkMap (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    P.presheaf.stalk p ⟶ (chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ p hp h) :=
  eqToHom (congrArg (fun y : ↥P => P.presheaf.stalk y)
      (chartPullbackFst_base_chartPullbackPoint c₁ c₂ p hp h).symm) ≫
    (chartPullbackFst c₁ c₂).stalkMap (chartPullbackPoint c₁ c₂ p hp h)

def chartPullbackSndStalkMap (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    P.presheaf.stalk p ⟶ (chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ p hp h) :=
  eqToHom (congrArg (fun y : ↥P => P.presheaf.stalk y)
      (chartPullbackSnd_base_chartPullbackPoint c₁ c₂ p hp h).symm) ≫
    (chartPullbackSnd c₁ c₂).stalkMap (chartPullbackPoint c₁ c₂ p hp h)

section
variable (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V) (h : ChartsAgreeAt c₁ c₂ p hp)

theorem chartPullbackFstStalkMap_eq :
    chartPullbackFstStalkMap c₁ c₂ p hp h =
      eqToHom (congrArg (fun y : ↥P => P.presheaf.stalk y)
          (chartPullbackFst_base_chartPullbackPoint c₁ c₂ p hp h).symm) ≫
        (chartPullbackFst c₁ c₂).stalkMap (chartPullbackPoint c₁ c₂ p hp h) := rfl

theorem chartPullbackSndStalkMap_eq :
    chartPullbackSndStalkMap c₁ c₂ p hp h =
      eqToHom (congrArg (fun y : ↥P => P.presheaf.stalk y)
          (chartPullbackSnd_base_chartPullbackPoint c₁ c₂ p hp h).symm) ≫
        (chartPullbackSnd c₁ c₂).stalkMap (chartPullbackPoint c₁ c₂ p hp h) := rfl


end

end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

theorem isAffineOpen_preimage_subschemeι {X : Scheme.{u}} (Z : X.IdealSheafData) {U : X.Opens}
    (hU : IsAffineOpen U) : IsAffineOpen (Z.subschemeι ⁻¹ᵁ U) :=
  hU.preimage Z.subschemeι

private theorem card_compl_eq_sub_consolidated141 (m : ℕ) (S : Finset (Fin m)) : Sᶜ.card = m - S.card := by
  rw [Finset.card_compl, Fintype.card_fin]

def complOrderEmb (m : ℕ) (S : Finset (Fin m)) : Fin (m - S.card) ↪o Fin m :=
  Sᶜ.orderEmbOfFin (card_compl_eq_sub_consolidated141 m S)

section
variable (m : ℕ) (S : Finset (Fin m))

theorem complOrderEmb_notMem (i : Fin (m - S.card)) :
    complOrderEmb m S i ∉ S :=
  Finset.mem_compl.mp (Finset.orderEmbOfFin_mem Sᶜ (card_compl_eq_sub_consolidated141 m S) i)

theorem exists_complOrderEmb_eq {j : Fin m} (hj : j ∉ S) :
    ∃ i : Fin (m - S.card), complOrderEmb m S i = j := by
  have hmem : j ∈ (↑(Sᶜ) : Set (Fin m)) := Finset.mem_coe.mpr (Finset.mem_compl.mpr hj)
  rw [← Finset.range_orderEmbOfFin Sᶜ (card_compl_eq_sub_consolidated141 m S)] at hmem
  obtain ⟨i, hi⟩ := hmem
  exact ⟨i, hi⟩


end

def mvPolynomialCoordIdeal (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    Ideal (MvPolynomial (ULift.{u} (Fin m)) k) :=
  Ideal.span ((fun j : Fin m => MvPolynomial.X (ULift.up.{u} j)) '' (S : Set (Fin m)))

section
variable (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))

theorem mvPolynomialCoordIdeal_eq_span :
    mvPolynomialCoordIdeal k m S =
      Ideal.span ((fun j : Fin m => MvPolynomial.X (ULift.up.{u} j)) '' (S : Set (Fin m))) :=
  rfl

theorem X_mem_mvPolynomialCoordIdeal {j : Fin m}
    (hj : j ∈ S) :
    MvPolynomial.X (ULift.up.{u} j) ∈ mvPolynomialCoordIdeal k m S :=
  Ideal.subset_span ⟨j, Finset.mem_coe.mpr hj, rfl⟩


end

def renameCompl (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    MvPolynomial (ULift.{u} (Fin (m - S.card))) k →ₐ[k] MvPolynomial (ULift.{u} (Fin m)) k :=
  MvPolynomial.aeval fun i : ULift.{u} (Fin (m - S.card)) =>
    MvPolynomial.X (ULift.up.{u} (complOrderEmb m S i.down))

section
variable (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))

@[simp] theorem renameCompl_X (i : Fin (m - S.card)) :
    renameCompl k m S (MvPolynomial.X (ULift.up.{u} i)) =
      MvPolynomial.X (ULift.up.{u} (complOrderEmb m S i)) :=
  MvPolynomial.aeval_X _ _

theorem renameCompl_C (a : k) :
    renameCompl k m S (MvPolynomial.C a) = MvPolynomial.C a := by
  show MvPolynomial.aeval
      (fun i : ULift.{u} (Fin (m - S.card)) => MvPolynomial.X (ULift.up.{u} (complOrderEmb m S i.down)))
      (MvPolynomial.C a) = MvPolynomial.C a
  simp


end

private def substZeroOnFinset_consolidated141 (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))
    (j : ULift.{u} (Fin m)) : MvPolynomial (ULift.{u} (Fin (m - S.card))) k :=
  if h : j.down ∈ S then 0
  else MvPolynomial.X (ULift.up.{u} (Classical.choose (exists_complOrderEmb_eq m S h)))

def setCoordsZero (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    MvPolynomial (ULift.{u} (Fin m)) k →ₐ[k] MvPolynomial (ULift.{u} (Fin (m - S.card))) k :=
  MvPolynomial.aeval (substZeroOnFinset_consolidated141 k m S)

section
variable (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))

theorem setCoordsZero_X_of_mem {j : Fin m}
    (hj : j ∈ S) : setCoordsZero k m S (MvPolynomial.X (ULift.up.{u} j)) = 0 := by
  have h1 : setCoordsZero k m S (MvPolynomial.X (ULift.up.{u} j)) = substZeroOnFinset_consolidated141 k m S (ULift.up.{u} j) :=
    MvPolynomial.aeval_X _ _
  rw [h1]
  exact dif_pos hj

theorem setCoordsZero_X_complOrderEmb (i : Fin (m - S.card)) :
    setCoordsZero k m S (MvPolynomial.X (ULift.up.{u} (complOrderEmb m S i))) =
      MvPolynomial.X (ULift.up.{u} i) := by
  have hnot : complOrderEmb m S i ∉ S := complOrderEmb_notMem m S i
  have h1 : setCoordsZero k m S (MvPolynomial.X (ULift.up.{u} (complOrderEmb m S i)))
      = substZeroOnFinset_consolidated141 k m S (ULift.up.{u} (complOrderEmb m S i)) := MvPolynomial.aeval_X _ _
  have h2 : substZeroOnFinset_consolidated141 k m S (ULift.up.{u} (complOrderEmb m S i))
      = MvPolynomial.X (ULift.up.{u} (Classical.choose (exists_complOrderEmb_eq m S hnot))) :=
    dif_neg hnot
  have h3 : Classical.choose (exists_complOrderEmb_eq m S hnot) = i :=
    (complOrderEmb m S).injective (Classical.choose_spec (exists_complOrderEmb_eq m S hnot))
  rw [h1, h2, h3]

theorem setCoordsZero_eq_zero_of_mem {q : MvPolynomial (ULift.{u} (Fin m)) k} (hq : q ∈ mvPolynomialCoordIdeal k m S) :
    setCoordsZero k m S q = 0 := by
  have hker : mvPolynomialCoordIdeal k m S ≤ RingHom.ker ((setCoordsZero k m S).toRingHom) := by
    rw [mvPolynomialCoordIdeal_eq_span, Ideal.span_le]
    rintro x ⟨j, hj, rfl⟩
    have hx : (setCoordsZero k m S).toRingHom (MvPolynomial.X (ULift.up.{u} j)) = 0 :=
      setCoordsZero_X_of_mem k m S (Finset.mem_coe.mp hj)
    exact RingHom.mem_ker.mpr hx
  have h : q ∈ RingHom.ker ((setCoordsZero k m S).toRingHom) := hker hq
  have h2 : (setCoordsZero k m S).toRingHom q = 0 := RingHom.mem_ker.mp h
  exact h2


end

open scoped TensorProduct in
theorem etale_quotientMap {P A : Type u} [CommRing P] [CommRing A] {f : P →+* A}
    (hf : f.Etale) (I : Ideal P) :
    (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).Etale := by
  let instPA : Algebra P A := f.toAlgebra
  have hfA : Algebra.Etale P A := hf
  let instQuot : Algebra (P ⧸ I) (A ⧸ Ideal.map f I) :=
    (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).toAlgebra
  have hqm : ∀ x : P, algebraMap (P ⧸ I) (A ⧸ Ideal.map f I) (Ideal.Quotient.mk I x)
      = Ideal.Quotient.mk (Ideal.map f I) (f x) := by
    intro x
    show Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map (Ideal.Quotient.mk I x) = _
    rw [Ideal.quotientMap_mk]
  have hst : IsScalarTower P (P ⧸ I) (A ⧸ Ideal.map f I) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    show Ideal.Quotient.mk (Ideal.map f I) (f x)
      = algebraMap (P ⧸ I) (A ⧸ Ideal.map f I) (algebraMap P (P ⧸ I) x)
    rw [Ideal.Quotient.algebraMap_eq, hqm x]
  have hcomm : ∀ x : P, (1 : P ⧸ I) ⊗ₜ[P] (f x) = (Ideal.Quotient.mk I x) ⊗ₜ[P] (1 : A) := by
    intro x
    have h1 : (Algebra.TensorProduct.includeRight : A →ₐ[P] ((P ⧸ I) ⊗[P] A)) (f x)
        = algebraMap P ((P ⧸ I) ⊗[P] A) x :=
      AlgHom.commutes (Algebra.TensorProduct.includeRight : A →ₐ[P] ((P ⧸ I) ⊗[P] A)) x
    have h2 : (Algebra.TensorProduct.includeLeft : (P ⧸ I) →ₐ[P] ((P ⧸ I) ⊗[P] A))
        (Ideal.Quotient.mk I x) = algebraMap P ((P ⧸ I) ⊗[P] A) x :=
      AlgHom.commutes (Algebra.TensorProduct.includeLeft : (P ⧸ I) →ₐ[P] ((P ⧸ I) ⊗[P] A)) x
    have h3 : (Algebra.TensorProduct.includeRight : A →ₐ[P] ((P ⧸ I) ⊗[P] A)) (f x)
        = (1 : P ⧸ I) ⊗ₜ[P] (f x) := rfl
    have h4 : (Algebra.TensorProduct.includeLeft : (P ⧸ I) →ₐ[P] ((P ⧸ I) ⊗[P] A))
        (Ideal.Quotient.mk I x) = (Ideal.Quotient.mk I x) ⊗ₜ[P] (1 : A) := rfl
    rw [← h3, ← h4, h1, h2]
  have hb : ∀ (x : P) (a : A),
      (1 : P ⧸ I) ⊗ₜ[P] (f x * a) = (Ideal.Quotient.mk I x) ⊗ₜ[P] a := by
    intro x a
    have e1 : ((1 : P ⧸ I) ⊗ₜ[P] (f x)) * ((1 : P ⧸ I) ⊗ₜ[P] a)
        = (1 : P ⧸ I) ⊗ₜ[P] (f x * a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have e2 : ((Ideal.Quotient.mk I x) ⊗ₜ[P] (1 : A)) * ((1 : P ⧸ I) ⊗ₜ[P] a)
        = (Ideal.Quotient.mk I x) ⊗ₜ[P] a := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [← e1, ← e2, hcomm]
  obtain ⟨φ, hφ⟩ : ∃ φ : ((P ⧸ I) ⊗[P] A) →ₐ[P ⧸ I] (A ⧸ Ideal.map f I),
      ∀ (q : P ⧸ I) (a : A), φ (q ⊗ₜ[P] a)
        = algebraMap (P ⧸ I) (A ⧸ Ideal.map f I) q * Ideal.Quotient.mk (Ideal.map f I) a :=
    ⟨Algebra.TensorProduct.lift (Algebra.ofId (P ⧸ I) (A ⧸ Ideal.map f I))
        (Ideal.Quotient.mkₐ P (Ideal.map f I)) (fun _ _ => Commute.all _ _),
      fun q a => by
        simp [Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Ideal.Quotient.mkₐ_eq_mk]⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (A ⧸ Ideal.map f I) →+* ((P ⧸ I) ⊗[P] A),
      ∀ a : A, ψ (Ideal.Quotient.mk (Ideal.map f I) a) = (1 : P ⧸ I) ⊗ₜ[P] a := by
    have hzero : ∀ a ∈ Ideal.map f I,
        (Algebra.TensorProduct.includeRight : A →ₐ[P] ((P ⧸ I) ⊗[P] A)).toRingHom a = 0 := by
      have hle : Ideal.map f I ≤ RingHom.ker
          (Algebra.TensorProduct.includeRight : A →ₐ[P] ((P ⧸ I) ⊗[P] A)).toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap, RingHom.mem_ker]
        show (1 : P ⧸ I) ⊗ₜ[P] (f x) = 0
        rw [hcomm, Ideal.Quotient.eq_zero_iff_mem.mpr hx, TensorProduct.zero_tmul]
      intro a ha
      exact RingHom.mem_ker.mp (hle ha)
    exact ⟨Ideal.Quotient.lift (Ideal.map f I)
      (Algebra.TensorProduct.includeRight : A →ₐ[P] ((P ⧸ I) ⊗[P] A)).toRingHom hzero,
      fun _ => rfl⟩
  have hleft : ∀ t : ((P ⧸ I) ⊗[P] A), ψ (φ t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul q a =>
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [hφ, hqm, ← map_mul (Ideal.Quotient.mk (Ideal.map f I)), hψ]
      exact hb x a
    | add u v hu hv =>
      rw [map_add, map_add, hu, hv]
  have hsurj : Function.Surjective φ := by
    intro b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨(1 : P ⧸ I) ⊗ₜ[P] a, by rw [hφ, map_one, one_mul]⟩
  have e : ((P ⧸ I) ⊗[P] A) ≃ₐ[P ⧸ I] (A ⧸ Ideal.map f I) :=
    AlgEquiv.ofBijective φ ⟨Function.LeftInverse.injective hleft, hsurj⟩
  have hbc : Algebra.Etale (P ⧸ I) ((P ⧸ I) ⊗[P] A) := inferInstance
  have hfe : Algebra.FormallyEtale (P ⧸ I) ((P ⧸ I) ⊗[P] A) := hbc.formallyEtale
  have hfp : Algebra.FinitePresentation (P ⧸ I) ((P ⧸ I) ⊗[P] A) := hbc.finitePresentation
  show Algebra.Etale (P ⧸ I) (A ⧸ Ideal.map f I)
  exact ⟨Algebra.FormallyEtale.of_equiv e, hfp.equiv e⟩

section
variable (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))

private theorem setCoordsZero_renameCompl_consolidated141 (q : MvPolynomial (ULift.{u} (Fin (m - S.card))) k) :
    setCoordsZero k m S (renameCompl k m S q) = q := by
  have h : (setCoordsZero k m S).comp (renameCompl k m S) = AlgHom.id k _ := by
    refine MvPolynomial.algHom_ext fun i => ?_
    obtain ⟨i⟩ := i
    rw [AlgHom.comp_apply, renameCompl_X, setCoordsZero_X_complOrderEmb, AlgHom.id_apply]
  exact DFunLike.congr_fun h q

private theorem quotientMk_renameCompl_setCoordsZero_consolidated141 (p : MvPolynomial (ULift.{u} (Fin m)) k) :
    Ideal.Quotient.mk (mvPolynomialCoordIdeal k m S) (renameCompl k m S (setCoordsZero k m S p))
      = Ideal.Quotient.mk (mvPolynomialCoordIdeal k m S) p := by
  have h : (Ideal.Quotient.mkₐ k (mvPolynomialCoordIdeal k m S)).comp
        ((renameCompl k m S).comp (setCoordsZero k m S))
      = Ideal.Quotient.mkₐ k (mvPolynomialCoordIdeal k m S) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    obtain ⟨j⟩ := j
    by_cases hj : j ∈ S
    · rw [AlgHom.comp_apply, AlgHom.comp_apply, setCoordsZero_X_of_mem k m S hj, map_zero, map_zero]
      symm
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact X_mem_mvPolynomialCoordIdeal k m S hj
    · obtain ⟨i, rfl⟩ := exists_complOrderEmb_eq m S hj
      rw [AlgHom.comp_apply, AlgHom.comp_apply, setCoordsZero_X_complOrderEmb, renameCompl_X]
  exact DFunLike.congr_fun h p

private theorem bijective_quotientMk_comp_renameCompl_consolidated141 :
    Function.Bijective
      ((Ideal.Quotient.mk (mvPolynomialCoordIdeal k m S)).comp (renameCompl k m S).toRingHom) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro q hq
    have hq' : renameCompl k m S q ∈ mvPolynomialCoordIdeal k m S :=
      (Ideal.Quotient.eq_zero_iff_mem).1 hq
    have h0 := setCoordsZero_eq_zero_of_mem k m S hq'
    rwa [setCoordsZero_renameCompl_consolidated141] at h0
  · intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨setCoordsZero k m S p, ?_⟩
    show Ideal.Quotient.mk (mvPolynomialCoordIdeal k m S) (renameCompl k m S (setCoordsZero k m S p))
        = Ideal.Quotient.mk (mvPolynomialCoordIdeal k m S) p
    exact quotientMk_renameCompl_setCoordsZero_consolidated141 k m S p

theorem etale_quotientMk_comp_renameCompl {A : Type u} [CommRing A] (f : MvPolynomial (ULift.{u} (Fin m)) k →+* A)
    (hf : f.Etale) (J : Ideal A) (hJ : J = Ideal.map f (mvPolynomialCoordIdeal k m S)) :
    (((Ideal.Quotient.mk J).comp f).comp (renameCompl k m S).toRingHom).Etale := by
  subst hJ
  have hcomp : ((Ideal.Quotient.mk (Ideal.map f (mvPolynomialCoordIdeal k m S))).comp f).comp
        (renameCompl k m S).toRingHom
      = (Ideal.quotientMap (Ideal.map f (mvPolynomialCoordIdeal k m S)) f Ideal.le_comap_map).comp
        ((Ideal.Quotient.mk (mvPolynomialCoordIdeal k m S)).comp (renameCompl k m S).toRingHom) :=
    RingHom.ext fun q => by
      simp only [RingHom.comp_apply, Ideal.quotientMap_mk]
  rw [hcomp]
  apply RingHom.Etale.stableUnderComposition
  · apply RingHom.Etale.of_bijective
    exact bijective_quotientMk_comp_renameCompl_consolidated141 k m S
  · exact etale_quotientMap hf (mvPolynomialCoordIdeal k m S)


end

theorem EtaleChart.coord_restrict {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U V : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (hVU : V ≤ U) (j : Fin m) :
    (c.restrict hVU).coord j = (X.presheaf.map (homOfLE hVU).op).hom (c.coord j) := by
  have key : ∀ {A B C D : (Opens ↥X)ᵒᵖ} {R : CommRingCat.{u}} (f : R ⟶ X.presheaf.obj A)
      (α : A ⟶ B) (β : B ⟶ D) (γ : A ⟶ C) (δ : C ⟶ D) (z : R),
      (X.presheaf.map β).hom ((f ≫ X.presheaf.map α).hom z)
        = (X.presheaf.map δ).hom ((X.presheaf.map γ).hom (f.hom z)) := by
    intro A B C D R f α β γ δ z
    have h : X.presheaf.map α ≫ X.presheaf.map β = X.presheaf.map γ ≫ X.presheaf.map δ :=
      (X.presheaf.map_comp α β).symm.trans
        ((congrArg X.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))).trans
          (X.presheaf.map_comp γ δ))
    exact congrArg (fun g : X.presheaf.obj A ⟶ X.presheaf.obj D => g.hom (f.hom z)) h
  simp [EtaleChart.restrict, EtaleChart.coord]
  all_goals
    first
      | rfl
      | exact key _ _ _ _ _ _

variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}

theorem EtaleChart.map_mvPolynomialCoordIdeal_eq_ideal (c : EtaleChart p U m) (hU : IsAffineOpen U)
    (Z : X.IdealSheafData) (S : Finset (Fin m)) (h : restrictIdeal Z U = c.coordIdeal S) :
    Ideal.map c.coordRingHom (mvPolynomialCoordIdeal k m S) = Z.ideal ⟨U, hU⟩ := by
  have hfun : (fun j : Fin m => c.coordRingHom (MvPolynomial.X (ULift.up.{u} j))) = c.coord :=
    funext fun j => c.coordRingHom_X j
  rw [c.ideal_eq_span_coord hU Z S h, mvPolynomialCoordIdeal_eq_span, Ideal.map_span]
  congr 1
  rw [Set.image_image]
  exact congrArg (fun g => g '' (S : Set (Fin m))) hfun

def EtaleChart.restrictToSubschemeCoords (c : EtaleChart p U m) (Z : X.IdealSheafData)
    (S : Finset (Fin m)) (i : ULift.{u} (Fin (m - S.card))) :
    Γ((Z.subschemeι ⁻¹ᵁ U).toScheme, ⊤) :=
  (Z.subschemeι ⁻¹ᵁ U).topIso.inv.hom
    ((Z.subschemeι.appLE U (Z.subschemeι ⁻¹ᵁ U) le_rfl).hom (c.coord (complOrderEmb m S i.down)))

private theorem appTop_comp_hom_apply_consolidated141 {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (x : Γ(C, ⊤)) :
    ((f ≫ g).appTop).hom x = (f.appTop).hom ((g.appTop).hom x) := rfl

section
variable {A B : CommRingCat.{u}} (e : A ≅ B)

private theorem commRingCatIso_inv_hom_apply_consolidated141 (x : A) :
    e.inv.hom (e.hom.hom x) = x := by
  simp

private theorem commRingCatIso_hom_inv_apply_consolidated141 (x : B) :
    e.hom.hom (e.inv.hom x) = x := by
  simp

private theorem bijective_commRingCatIso_inv_consolidated141 :
    Function.Bijective e.inv.hom := by
  constructor
  · intro x y hxy
    have h := congrArg e.hom.hom hxy
    rwa [commRingCatIso_hom_inv_apply_consolidated141, commRingCatIso_hom_inv_apply_consolidated141] at h
  · intro x
    exact ⟨e.hom.hom x, commRingCatIso_inv_hom_apply_consolidated141 e x⟩


end

private theorem iso_hom_appTop_inv_appTop_apply_consolidated141 {A B : Scheme.{u}} (e : A ≅ B) (x : Γ(A, ⊤)) :
    (e.hom.appTop).hom ((e.inv.appTop).hom x) = x := by
  have h1 : ((e.hom ≫ e.inv).appTop).hom x
      = ((CategoryTheory.CategoryStruct.id A : A ⟶ A).appTop).hom x := by rw [e.hom_inv_id]
  rw [appTop_comp_hom_apply_consolidated141] at h1
  rw [h1]
  simp

section
variable (K : Type u) [Field K] (n : ℕ)

private theorem affineSpaceGlobalSectionsHom_apply_consolidated141 (x : MvPolynomial (ULift.{u} (Fin n)) K) :
    affineSpaceGlobalSectionsHom K n x =
      ((AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).hom.appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv.hom x) :=
  rfl

private theorem affineSpaceGlobalSectionsHom_X_eq_coord_consolidated141 (i : ULift.{u} (Fin n)) :
    affineSpaceGlobalSectionsHom K n (MvPolynomial.X i) =
      AffineSpace.coord (Spec (CommRingCat.of K)) i := by
  have h := AffineSpace.SpecIso_inv_appTop_coord (CommRingCat.of K) i
  rw [affineSpaceGlobalSectionsHom_apply_consolidated141, ← h]
  exact iso_hom_appTop_inv_appTop_apply_consolidated141
    (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)) _

private theorem affineSpaceGlobalSectionsHom_C_consolidated141 (a : K) :
    affineSpaceGlobalSectionsHom K n (MvPolynomial.C a) =
      ((affineSpaceFinToSpec K n).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) := by
  have hov : (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).inv ≫
      affineSpaceFinToSpec K n =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin n)) K)) :=
    AffineSpace.SpecIso_inv_over ..
  have hmor : (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).hom ≫
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin n)) K))
      = affineSpaceFinToSpec K n := by
    rw [← hov, Iso.hom_inv_id_assoc]
  have h1 : ((Scheme.ΓSpecIso
        (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv).hom (MvPolynomial.C a)
      = ((Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin n)) K))).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) := by
    have hnat := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin n)) K))
    show ((CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin n)) K)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv).hom a = _
    conv_lhs => rw [hnat]
    rfl
  rw [affineSpaceGlobalSectionsHom_apply_consolidated141, h1, ← appTop_comp_hom_apply_consolidated141, hmor]


end

private theorem etale_specMap_of_etale_consolidated141 {R T : CommRingCat.{u}} (φ : R ⟶ T) (hφ : φ.hom.Etale) :
    Etale (Spec.map φ) := by
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @Etale)]
  exact hφ

section
variable {Wsch : Scheme.{u}}

private theorem etale_homOfVector_of_appTop_etale_consolidated141 [IsAffine Wsch]
    {K : Type u} [Field K]
    {n : ℕ} (q : Wsch ⟶ Spec (CommRingCat.of K)) (v : ULift.{u} (Fin n) → Γ(Wsch, ⊤))
    (hv : (((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv ≫
      (AffineSpace.homOfVector q v ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).hom).appTop).hom).Etale) :
    Etale (AffineSpace.homOfVector q v) := by
  set f := AffineSpace.homOfVector q v
  set e := AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)
  set φ := (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv ≫
      (f ≫ e.hom).appTop with hφ
  have hφe : φ.hom.Etale := hv
  have nat : (f ≫ e.hom) ≫
      (Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).toSpecΓ
      = Wsch.toSpecΓ ≫ Spec.map (f ≫ e.hom).appTop := Scheme.toSpecΓ_naturality _
  have key : f = Wsch.toSpecΓ ≫ Spec.map φ ≫ e.inv := by
    rw [hφ, Spec.map_comp]
    calc f = ((f ≫ e.hom) ≫
        (Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).toSpecΓ) ≫
          Spec.map (Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv ≫ e.inv := by simp
      _ = (Wsch.toSpecΓ ≫ Spec.map (f ≫ e.hom).appTop) ≫
          Spec.map (Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv ≫ e.inv := by rw [nat]
      _ = Wsch.toSpecΓ ≫ (Spec.map (f ≫ e.hom).appTop ≫
          Spec.map (Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv) ≫ e.inv := by
            simp [Category.assoc]
  have : Etale (Spec.map φ) := etale_specMap_of_etale_consolidated141 φ hφe
  rw [key]
  infer_instance

private theorem appTop_comp_specIso_eq_affineSpaceGlobalSectionsHom_consolidated141 {K : Type u} [Field K] {n : ℕ}
    (F : Wsch ⟶ affineSpaceFin K n) (x : MvPolynomial (ULift.{u} (Fin n)) K) :
    (((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv ≫
        (F ≫ (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).hom).appTop).hom) x
      = (F.appTop).hom (affineSpaceGlobalSectionsHom K n x) := by
  rw [affineSpaceGlobalSectionsHom_apply_consolidated141]
  show ((F ≫ (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).hom).appTop).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv.hom x) = _
  rw [appTop_comp_hom_apply_consolidated141]


end

private theorem subschemeι_appLE_apply_consolidated141 (Zd : X.IdealSheafData) (Uo : X.Opens)
    (hUo : IsAffineOpen Uo) (z : Γ(X, Uo)) :
    (Zd.subschemeι.appLE Uo (Zd.subschemeι ⁻¹ᵁ Uo) le_rfl).hom z
      = (Zd.subschemeObjIso ⟨Uo, hUo⟩).inv.hom
          (Ideal.Quotient.mk (Zd.ideal ⟨Uo, hUo⟩) z) := by
  have hh : Zd.subschemeι.app Uo
      = CommRingCat.ofHom (Ideal.Quotient.mk (Zd.ideal ⟨Uo, hUo⟩)) ≫
        (Zd.subschemeObjIso ⟨Uo, hUo⟩).inv :=
    Scheme.IdealSheafData.subschemeι_app Zd ⟨Uo, hUo⟩
  have h2 : Zd.subschemeι.appLE Uo (Zd.subschemeι ⁻¹ᵁ Uo) le_rfl = Zd.subschemeι.app Uo := by
    simp [Scheme.Hom.appLE]
  rw [h2]
  conv_lhs => rw [hh]
  rfl

private theorem coordRingHom_apply_consolidated141 (c : EtaleChart p U m)
    (x : MvPolynomial (ULift.{u} (Fin m)) k) :
    c.coordRingHom x = U.topIso.hom.hom (c.map.appTop.hom (affineSpaceGlobalSectionsHom k m x)) :=
  rfl

private theorem subschemeι_appLE_topIso_hom_appTop_apply_consolidated141 {Wsch Ysch : Scheme.{u}} (q : Wsch ⟶ Ysch)
    (Zd : Wsch.IdealSheafData) (Uo : Wsch.Opens) (x : Γ(Ysch, ⊤)) :
    (Zd.subschemeι ⁻¹ᵁ Uo).topIso.inv.hom
        ((Zd.subschemeι.appLE Uo (Zd.subschemeι ⁻¹ᵁ Uo) le_rfl).hom
          (Uo.topIso.hom.hom (((Uo.ι ≫ q).appTop).hom x)))
      = (((Zd.subschemeι ⁻¹ᵁ Uo).ι ≫ (Zd.subschemeι ≫ q)).appTop).hom x := by
  have htop1 : q ⁻¹ᵁ (⊤ : Ysch.Opens) = ⊤ := by simp
  have htop2 : (Zd.subschemeι ≫ q) ⁻¹ᵁ (⊤ : Ysch.Opens) = ⊤ := by simp
  have e1 : Uo ≤ q ⁻¹ᵁ (⊤ : Ysch.Opens) := le_top.trans htop1.ge
  have e2 : (Zd.subschemeι ⁻¹ᵁ Uo) ≤ (Zd.subschemeι ≫ q) ⁻¹ᵁ (⊤ : Ysch.Opens) :=
    le_top.trans htop2.ge
  have hq : (Uo.ι ≫ q).appTop = q.appLE ⊤ Uo e1 ≫ Uo.topIso.inv :=
    (appLE_top_comp_topIso_inv q Uo e1).symm
  have hq2 : (Zd.subschemeι ≫ q).appLE ⊤ (Zd.subschemeι ⁻¹ᵁ Uo) e2 ≫
        (Zd.subschemeι ⁻¹ᵁ Uo).topIso.inv
      = ((Zd.subschemeι ⁻¹ᵁ Uo).ι ≫ (Zd.subschemeι ≫ q)).appTop :=
    appLE_top_comp_topIso_inv (Zd.subschemeι ≫ q) (Zd.subschemeι ⁻¹ᵁ Uo) e2
  have key : (Uo.ι ≫ q).appTop ≫ Uo.topIso.hom ≫
        Zd.subschemeι.appLE Uo (Zd.subschemeι ⁻¹ᵁ Uo) le_rfl ≫
          (Zd.subschemeι ⁻¹ᵁ Uo).topIso.inv
      = ((Zd.subschemeι ⁻¹ᵁ Uo).ι ≫ (Zd.subschemeι ≫ q)).appTop := by
    rw [hq, ← hq2, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc,
      Scheme.Hom.appLE_comp_appLE]
  show ((Uo.ι ≫ q).appTop ≫ Uo.topIso.hom ≫
      Zd.subschemeι.appLE Uo (Zd.subschemeι ⁻¹ᵁ Uo) le_rfl ≫
        (Zd.subschemeι ⁻¹ᵁ Uo).topIso.inv).hom x = _
  rw [key]

section
variable (c : EtaleChart p U m) (hU : IsAffineOpen U) (Z : X.IdealSheafData) (S : Finset (Fin m))
include hU

private theorem appTop_homOfVector_restrictToSubschemeCoords_eq_consolidated141 :
    (((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin (m - S.card))) k))).inv ≫
        (AffineSpace.homOfVector ((Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p))
            (c.restrictToSubschemeCoords Z S) ≫
          (AffineSpace.SpecIso (ULift.{u} (Fin (m - S.card)))
            (CommRingCat.of k)).hom).appTop).hom)
      = ((((Z.subschemeι ⁻¹ᵁ U).topIso.inv.hom).comp
            ((Z.subschemeObjIso ⟨U, hU⟩).inv.hom)).comp
          (((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)).comp c.coordRingHom).comp
            (renameCompl k m S).toRingHom)) := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · have hover : AffineSpace.homOfVector ((Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p))
        (c.restrictToSubschemeCoords Z S) ≫ affineSpaceFinToSpec k (m - S.card)
        = (Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p) := AffineSpace.homOfVector_over ..
    rw [appTop_comp_specIso_eq_affineSpaceGlobalSectionsHom_consolidated141, affineSpaceGlobalSectionsHom_C_consolidated141, ← appTop_comp_hom_apply_consolidated141, hover]
    show _ = (Z.subschemeι ⁻¹ᵁ U).topIso.inv.hom
      ((Z.subschemeObjIso ⟨U, hU⟩).inv.hom
        (Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)
          (c.coordRingHom (renameCompl k m S (MvPolynomial.C a)))))
    rw [renameCompl_C, coordRingHom_apply_consolidated141, affineSpaceGlobalSectionsHom_C_consolidated141, ← appTop_comp_hom_apply_consolidated141,
      c.comp_struct, ← subschemeι_appLE_apply_consolidated141 Z U hU, subschemeι_appLE_topIso_hom_appTop_apply_consolidated141]
  · obtain ⟨i⟩ := i
    rw [appTop_comp_specIso_eq_affineSpaceGlobalSectionsHom_consolidated141, affineSpaceGlobalSectionsHom_X_eq_coord_consolidated141, AffineSpace.homOfVector_appTop_coord]
    show (Z.subschemeι ⁻¹ᵁ U).topIso.inv.hom
        ((Z.subschemeι.appLE U (Z.subschemeι ⁻¹ᵁ U) le_rfl).hom (c.coord (complOrderEmb m S i)))
      = (Z.subschemeι ⁻¹ᵁ U).topIso.inv.hom
        ((Z.subschemeObjIso ⟨U, hU⟩).inv.hom
          (Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)
            (c.coordRingHom (renameCompl k m S (MvPolynomial.X (ULift.up.{u} i))))))
    rw [renameCompl_X, EtaleChart.coordRingHom_X, ← subschemeι_appLE_apply_consolidated141 Z U hU]

theorem EtaleChart.etale_homOfVector_restrictToSubschemeCoords (h : restrictIdeal Z U = c.coordIdeal S) :
    Etale (AffineSpace.homOfVector ((Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p))
      (c.restrictToSubschemeCoords Z S)) := by
  have hVa : IsAffine (Z.subschemeι ⁻¹ᵁ U).toScheme := isAffineOpen_preimage_subschemeι Z hU
  refine etale_homOfVector_of_appTop_etale_consolidated141 _ _ ?_
  rw [appTop_homOfVector_restrictToSubschemeCoords_eq_consolidated141 c hU Z S]
  apply RingHom.Etale.stableUnderComposition
  · exact etale_quotientMk_comp_renameCompl k m S c.coordRingHom (c.coordRingHom_etale hU) (Z.ideal ⟨U, hU⟩)
      (c.map_mvPolynomialCoordIdeal_eq_ideal hU Z S h).symm
  · apply RingHom.Etale.of_bijective
    exact (bijective_commRingCatIso_inv_consolidated141 (Z.subschemeι ⁻¹ᵁ U).topIso).comp
      (bijective_commRingCatIso_inv_consolidated141 (Z.subschemeObjIso ⟨U, hU⟩))


end

def EtaleChart.restrictToSubscheme (c : EtaleChart p U m) (hU : IsAffineOpen U)
    (Z : X.IdealSheafData) (S : Finset (Fin m)) (h : restrictIdeal Z U = c.coordIdeal S) :
    EtaleChart (Z.subschemeι ≫ p) (Z.subschemeι ⁻¹ᵁ U) (m - S.card) :=
  EtaleChart.ofCoords (Z.subschemeι ≫ p) (Z.subschemeι ⁻¹ᵁ U) (c.restrictToSubschemeCoords Z S)
    (c.etale_homOfVector_restrictToSubschemeCoords hU Z S h)

theorem EtaleChart.restrictToSubscheme_coord (c : EtaleChart p U m) (hU : IsAffineOpen U)
    (Z : X.IdealSheafData) (S : Finset (Fin m)) (h : restrictIdeal Z U = c.coordIdeal S)
    (i : Fin (m - S.card)) :
    (c.restrictToSubscheme hU Z S h).coord i =
      (Z.subschemeι.appLE U (Z.subschemeι ⁻¹ᵁ U) le_rfl).hom (c.coord (complOrderEmb m S i)) := by
  have hmapeq : (c.restrictToSubscheme hU Z S h).map =
      AffineSpace.homOfVector ((Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p))
        (c.restrictToSubschemeCoords Z S) :=
    EtaleChart.ofCoords_map (Z.subschemeι ≫ p) (Z.subschemeι ⁻¹ᵁ U)
      (c.restrictToSubschemeCoords Z S) (c.etale_homOfVector_restrictToSubschemeCoords hU Z S h)
  have hcoord : ((c.restrictToSubscheme hU Z S h).map.appTop).hom
      (AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up i : ULift.{u} (Fin (m - S.card))))
      = (Z.subschemeι ⁻¹ᵁ U).topIso.inv.hom
          ((Z.subschemeι.appLE U (Z.subschemeι ⁻¹ᵁ U) le_rfl).hom
            (c.coord (complOrderEmb m S i))) := by
    rw [hmapeq]
    apply AffineSpace.homOfVector_appTop_coord
  rw [EtaleChart.coord_def (c.restrictToSubscheme hU Z S h) i, hcoord]
  exact commRingCatIso_hom_inv_apply_consolidated141 _ _

section
variable {W : Scheme.{u}}

private theorem presheaf_map_comp_eq_consolidated141 {A B C : (Opens ↥W)ᵒᵖ}
    (α : A ⟶ B) (β : B ⟶ C) (γ : A ⟶ C) :
    W.presheaf.map α ≫ W.presheaf.map β = W.presheaf.map γ :=
  (W.presheaf.map_comp α β).symm.trans
    (congrArg W.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))

private theorem opens_ι_appLE_top_eq_topIso_inv_consolidated141 (V : W.Opens)
    (e : (⊤ : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ e = V.topIso.inv := by
  simp [Scheme.Hom.appLE]
  exact presheaf_map_comp_eq_consolidated141 _ _ _


end

section
variable (c : EtaleChart p U m) (hU : IsAffineOpen U) (Z : X.IdealSheafData) (S : Finset (Fin m)) (h : restrictIdeal Z U = c.coordIdeal S) (i : Fin (m - S.card))

private theorem restrictToSubscheme_map_appTop_coord_consolidated141 :
    ((c.restrictToSubscheme hU Z S h).map.appTop).hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) =
      (Z.subschemeι ⁻¹ᵁ U).topIso.inv.hom
        ((Z.subschemeι.appLE U (Z.subschemeι ⁻¹ᵁ U) le_rfl).hom (c.coord (complOrderEmb m S i))) := by
  simp [EtaleChart.restrictToSubscheme, EtaleChart.ofCoords_map,
    EtaleChart.restrictToSubschemeCoords]

theorem EtaleChart.restrictToSubscheme_coordIdeal_singleton (E : X.IdealSheafData)
    (hE : restrictIdeal E U = c.coordIdeal {complOrderEmb m S i}) :
    restrictIdeal (E.comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U) =
      (c.restrictToSubscheme hU Z S h).coordIdeal {i} := by
  have hVaff : IsAffineOpen (Z.subschemeι ⁻¹ᵁ U) := isAffineOpen_preimage_subschemeι Z hU
  have hVa : IsAffine (Z.subschemeι ⁻¹ᵁ U).toScheme := hVaff
  have hAa : IsAffine (affineSpaceFin k (m - S.card)) := inferInstance
  have e1 : (⊤ : ((Z.subschemeι ⁻¹ᵁ U).toScheme).Opens) ≤
      (Z.subschemeι ⁻¹ᵁ U).ι ⁻¹ᵁ (Z.subschemeι ⁻¹ᵁ U) := by simp
  have hL1 : (restrictIdeal (E.comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U)).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.map ((Z.subschemeι ⁻¹ᵁ U).ι.appLE (Z.subschemeι ⁻¹ᵁ U) ⊤ e1).hom
        ((E.comap Z.subschemeι).ideal ⟨Z.subschemeι ⁻¹ᵁ U, hVaff⟩) :=
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE (E.comap Z.subschemeι)
      (Z.subschemeι ⁻¹ᵁ U).ι ⟨Z.subschemeι ⁻¹ᵁ U, hVaff⟩ ⟨⊤, isAffineOpen_top _⟩ e1
  have hL2 : (E.comap Z.subschemeι).ideal ⟨Z.subschemeι ⁻¹ᵁ U, hVaff⟩ =
      Ideal.map (Z.subschemeι.appLE U (Z.subschemeι ⁻¹ᵁ U) le_rfl).hom (E.ideal ⟨U, hU⟩) :=
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE E Z.subschemeι ⟨U, hU⟩
      ⟨Z.subschemeι ⁻¹ᵁ U, hVaff⟩ le_rfl
  have hL3 : E.ideal ⟨U, hU⟩ = Ideal.span {c.coord (complOrderEmb m S i)} := by
    rw [c.ideal_eq_span_coord hU E {complOrderEmb m S i} hE, Finset.coe_singleton,
      Set.image_singleton]
  have hR1 : ((c.restrictToSubscheme hU Z S h).coordIdeal {i}).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.map ((c.restrictToSubscheme hU Z S h).map.appTop).hom
        ((coordSubspaceIdeal k (m - S.card) {i}).ideal ⟨⊤, isAffineOpen_top _⟩) := by
    rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
    exact Scheme.IdealSheafData.comap_ideal_top_eq_map_appTop _ _
  have hR2 : (coordSubspaceIdeal k (m - S.card) {i}).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)} := by
    rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, Scheme.IdealSheafData.ofIdealTop_ideal_top, Finset.coe_singleton,
      Set.image_singleton]
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  show (restrictIdeal (E.comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U)).ideal
      ⟨⊤, isAffineOpen_top _⟩ =
    ((c.restrictToSubscheme hU Z S h).coordIdeal {i}).ideal ⟨⊤, isAffineOpen_top _⟩
  rw [hL1, hL2, hL3, hR1, hR2]
  simp only [Ideal.map_span, Set.image_singleton]
  rw [restrictToSubscheme_map_appTop_coord_consolidated141, opens_ι_appLE_top_eq_topIso_inv_consolidated141]


end

theorem restrictIdeal_comap_subschemeι_eq_top {X : Scheme.{u}} (Z : X.IdealSheafData)
    (U : X.Opens) (E : X.IdealSheafData) (hE : restrictIdeal E U = ⊤) :
    restrictIdeal (E.comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U) = ⊤ := by
  rw [restrictIdeal_eq_comap_ι] at hE
  rw [restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
    ← morphismRestrict_ι Z.subschemeι U, Scheme.IdealSheafData.comap_comp, hE,
    Scheme.IdealSheafData.comap_top]

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateQuotient
section

namespace FunctorialResolution.EmbeddedResolution

noncomputable def etaleChartCoordIdeal (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] (J : Finset (Fin m)) : Ideal S :=
  Ideal.span (etaleChartCoord k m S '' (J : Set (Fin m)))

section
variable (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S] (J : Finset (Fin m))

theorem etaleChartCoordIdeal_eq_span_image :
    etaleChartCoordIdeal k m S J = Ideal.span (etaleChartCoord k m S '' (J : Set (Fin m))) :=
  rfl

theorem etaleChartCoordIdeal_le (I : Ideal S)
    (hI : ∀ j ∈ J, etaleChartCoord k m S j ∈ I) : etaleChartCoordIdeal k m S J ≤ I := by
  refine Ideal.span_le.mpr ?_
  rintro x ⟨j, hj, rfl⟩
  exact hI j (Finset.mem_coe.mp hj)

theorem map_mvPolynomialCoordIdeal_eq_etaleChartCoordIdeal :
    Ideal.map (algebraMap (CoordPolynomialRing k m) S) (mvPolynomialCoordIdeal k m J) =
      etaleChartCoordIdeal k m S J := by
  rw [etaleChartCoordIdeal_eq_span_image, mvPolynomialCoordIdeal_eq_span, Ideal.map_span, Set.image_image]
  rfl


end

@[reducible] noncomputable def algebraQuotientCoordIdeal (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S] (J : Finset (Fin m)) :
    Algebra (MvPolynomial (ULift.{u} (Fin (m - J.card))) k) (S ⧸ etaleChartCoordIdeal k m S J) :=
  RingHom.toAlgebra
    (((Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)).comp
      (algebraMap (CoordPolynomialRing k m) S)).comp (renameCompl k m J).toRingHom)

private theorem etale_algebraMap_coordPolynomialRing_consolidated160 (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S] :
    (algebraMap (CoordPolynomialRing k m) S).Etale := by
  have hiff : (algebraMap (CoordPolynomialRing k m) S).toAlgebra
      = (inferInstance : Algebra (CoordPolynomialRing k m) S) :=
    Algebra.algebra_ext _ _ fun r => rfl
  show @Algebra.Etale _ _ _ _ (algebraMap (CoordPolynomialRing k m) S).toAlgebra
  rw [hiff]
  infer_instance

section
variable (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A] [Algebra S A] [IsLocalization q.primeCompl A]

theorem isRegularLocalRing_quotient_map_etaleChartCoordIdeal (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q) :
    IsRegularLocalRing
      (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J)) := by
  classical
  have hIq : etaleChartCoordIdeal k m S J ≤ q := etaleChartCoordIdeal_le k m S J q hJ
  have hq' : (Ideal.map (Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)) q).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hIq)
  let algQuotient : Algebra (CoordPolynomialRing k (m - J.card)) (S ⧸ etaleChartCoordIdeal k m S J) :=
    algebraQuotientCoordIdeal k m S J
  have : Algebra.Etale (CoordPolynomialRing k (m - J.card)) (S ⧸ etaleChartCoordIdeal k m S J) :=
    etale_quotientMk_comp_renameCompl k m J (algebraMap (CoordPolynomialRing k m) S)
      (etale_algebraMap_coordPolynomialRing_consolidated160 k m S) (etaleChartCoordIdeal k m S J)
      (map_mvPolynomialCoordIdeal_eq_etaleChartCoordIdeal k m S J).symm
  have h2 : Submonoid.map (Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)) q.primeCompl
      = (Ideal.map (Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)) q).primeCompl := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨b, hb, hba⟩ hcon
      refine hb ((Ideal.mem_quotient_iff_mem hIq).mp ?_)
      rw [hba]
      exact hcon
    · intro ha
      exact ⟨a, fun hq => ha ((Ideal.mem_quotient_iff_mem hIq).mpr hq), rfl⟩
  have hloc : IsLocalization
      (Submonoid.map (Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)) q.primeCompl)
      (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J)) :=
    inferInstanceAs (IsLocalization
      (Algebra.algebraMapSubmonoid (S ⧸ etaleChartCoordIdeal k m S J) q.primeCompl)
      (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J)))
  have : IsLocalization (Ideal.map (Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)) q).primeCompl
      (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J)) := h2 ▸ hloc
  exact isRegularLocalRing_of_isLocalization_etale k (m - J.card)
    (S ⧸ etaleChartCoordIdeal k m S J)
    (Ideal.map (Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)) q)
    (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J))

private theorem algebraMap_etaleChartCoord_notMem_maximalIdeal_sq_sup_consolidated160 [IsLocalRing A] (J' : Finset (Fin m))
    (hJ' : ∀ i ∈ J', etaleChartCoord k m S i ∈ q) (j : Fin m) (hj : j ∉ J') :
    algebraMap S A (etaleChartCoord k m S j) ∉
      IsLocalRing.maximalIdeal A ^ 2 ⊔ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J') := by
  classical
  let algebraKS : Algebra k S := ((algebraMap (CoordPolynomialRing k m) S).comp
    (algebraMap k (CoordPolynomialRing k m))).toAlgebra
  have : IsScalarTower k (CoordPolynomialRing k m) S := IsScalarTower.of_algebraMap_eq' rfl
  let algebraKA : Algebra k A := ((algebraMap S A).comp (algebraMap k S)).toAlgebra
  have : IsScalarTower k S A := IsScalarTower.of_algebraMap_eq' rfl
  let D : Derivation k S S :=
    EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) S (ULift.up.{u} j)
  let DA : Derivation k A A := D.mapToLocalization q.primeCompl
  have hderivAlgebraMap : ∀ s : S, DA (algebraMap S A s) = algebraMap S A (D s) :=
    Derivation.mapToLocalization_algebraMap D q.primeCompl
  have hDx : D (etaleChartCoord k m S j) = 1 :=
    EtaleCoordinates.partialDeriv_coord_self k (ULift.{u} (Fin m)) S (ULift.up.{u} j)
  have hDne : ∀ i : Fin m, i ≠ j → D (etaleChartCoord k m S i) = 0 := by
    intro i hne
    have hup : (ULift.up.{u} j) ≠ ULift.up.{u} i := fun h => hne (congrArg ULift.down h).symm
    exact EtaleCoordinates.partialDeriv_coord_of_ne k (ULift.{u} (Fin m)) S
      (ULift.up.{u} j) (ULift.up.{u} i) hup
  have hmapeq : Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J')
      = Ideal.span ((fun i : Fin m => algebraMap S A (etaleChartCoord k m S i)) ''
        (J' : Set (Fin m))) := by
    rw [etaleChartCoordIdeal_eq_span_image, Ideal.map_span, Set.image_image]
  have hspan_le : Ideal.span ((fun i : Fin m => algebraMap S A (etaleChartCoord k m S i)) ''
      (J' : Set (Fin m))) ≤ IsLocalRing.maximalIdeal A := by
    refine Ideal.span_le.mpr ?_
    rintro x ⟨i, hi, rfl⟩
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A q (etaleChartCoord k m S i)
      inferInstance).mpr (hJ' i (Finset.mem_coe.mp hi))
  intro hmem
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  have hsq : IsLocalRing.maximalIdeal A ^ 2
      = IsLocalRing.maximalIdeal A * IsLocalRing.maximalIdeal A := sq _
  rw [hsq] at ha
  have hDa : DA a ∈ IsLocalRing.maximalIdeal A := by
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro p hp r hr
      rw [DA.leibniz, smul_eq_mul, smul_eq_mul]
      exact add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_right _ _ hr)
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy
  rw [hmapeq] at hb
  have hDb : DA b ∈ IsLocalRing.maximalIdeal A := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
    · rintro z ⟨i, hi, rfl⟩
      rw [hderivAlgebraMap, hDne i (by rintro rfl; exact hj (Finset.mem_coe.mp hi)), map_zero]
      exact zero_mem _
    · rw [map_zero]
      exact zero_mem _
    · intro x y hx hy px py
      rw [map_add]
      exact add_mem px py
    · intro c x hx px
      have hxm : x ∈ IsLocalRing.maximalIdeal A := hspan_le hx
      rw [smul_eq_mul, DA.leibniz, smul_eq_mul, smul_eq_mul]
      exact add_mem (Ideal.mul_mem_left _ _ px) (Ideal.mul_mem_right _ _ hxm)
  have hone : DA (algebraMap S A (etaleChartCoord k m S j)) = 1 := by
    rw [hderivAlgebraMap, hDx, map_one]
  rw [← hab, map_add] at hone
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← hone]
    exact add_mem hDa hDb
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem ringKrullDim_quotient_map_etaleChartCoordIdeal_add_card (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q) :
    ringKrullDim (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J)) +
        (J.card : WithBot ℕ∞) = ringKrullDim A := by
  classical
  have : IsRegularLocalRing A := isRegularLocalRing_of_isLocalization_etale k m S q A
  revert hJ
  induction J using Finset.induction_on with
  | empty =>
      intro _
      have h0 : Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S (∅ : Finset (Fin m))) = ⊥ := by
        rw [etaleChartCoordIdeal_eq_span_image]
        simp
      have hker : (⊥ : Ideal A) = RingHom.ker (RingHom.id A) := by
        ext a
        simp [RingHom.mem_ker]
      have e : (A ⧸ (⊥ : Ideal A)) ≃+* A :=
        (Ideal.quotEquivOfEq hker).trans
          (RingHom.quotientKerEquivOfSurjective
            (show Function.Surjective (RingHom.id A) from fun a => ⟨a, rfl⟩))
      rw [h0, ringKrullDim_eq_of_ringEquiv e]
      simp
  | @insert j J' hjJ ih =>
      intro hJ
      have hJ' : ∀ i ∈ J', etaleChartCoord k m S i ∈ q := fun i hi =>
        hJ i (Finset.mem_insert_of_mem hi)
      have hjq : etaleChartCoord k m S j ∈ q := hJ j (Finset.mem_insert_self _ _)
      set I' := Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J') with hI'
      have hR : IsRegularLocalRing (A ⧸ I') :=
        isRegularLocalRing_quotient_map_etaleChartCoordIdeal k m S q A J' hJ'
      set y : A := algebraMap S A (etaleChartCoord k m S j) with hy
      have hins : Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S (insert j J'))
          = I' ⊔ Ideal.span {y} := by
        rw [hI', hy, etaleChartCoordIdeal_eq_span_image, etaleChartCoordIdeal_eq_span_image, Finset.coe_insert,
          Set.image_insert_eq, Ideal.span_insert, Ideal.map_sup, Ideal.map_span, Ideal.map_span,
          Set.image_singleton]
        exact sup_comm _ _
      have hspan : Ideal.map (Ideal.Quotient.mk I') (Ideal.span {y})
          = Ideal.span {Ideal.Quotient.mk I' y} := by
        rw [Ideal.map_span, Set.image_singleton]
      have e := (Ideal.quotEquivOfEq hspan.symm).trans
        (DoubleQuot.quotQuotEquivQuotSup I' (Ideal.span {y}))
      have hdim1 : ringKrullDim
          (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S (insert j J')))
          = ringKrullDim ((A ⧸ I') ⧸ Ideal.span {Ideal.Quotient.mk I' y}) := by
        rw [hins]
        exact (ringKrullDim_eq_of_ringEquiv e).symm
      have hmaxR : IsLocalRing.maximalIdeal (A ⧸ I')
          = Ideal.map (Ideal.Quotient.mk I') (IsLocalRing.maximalIdeal A) :=
        (IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I')
          Ideal.Quotient.mk_surjective).symm
      have hy1 : Ideal.Quotient.mk I' y ∈ IsLocalRing.maximalIdeal (A ⧸ I') := by
        rw [hmaxR, hy]
        exact Ideal.mem_map_of_mem _
          ((IsLocalization.AtPrime.to_map_mem_maximal_iff A q (etaleChartCoord k m S j)
            inferInstance).mpr hjq)
      have hy2 : Ideal.Quotient.mk I' y ∉ IsLocalRing.maximalIdeal (A ⧸ I') ^ 2 := by
        rw [hmaxR, ← Ideal.map_pow]
        intro hcon
        have hcon2 : y ∈ Ideal.comap (Ideal.Quotient.mk I')
            (Ideal.map (Ideal.Quotient.mk I') (IsLocalRing.maximalIdeal A ^ 2)) := hcon
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
          ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hcon2
        rw [hy, hI'] at hcon2
        exact algebraMap_etaleChartCoord_notMem_maximalIdeal_sq_sup_consolidated160 k m S q A J' hJ' j hjJ hcon2
      have hstep :=
        IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hy1 hy2
      rw [hdim1, Finset.card_insert_of_notMem hjJ]
      have hcard : (((J'.card + 1 : ℕ)) : WithBot ℕ∞) = 1 + (J'.card : WithBot ℕ∞) := by
        push_cast
        ring
      rw [hcard, ← add_assoc, hstep]
      exact ih hJ'


end

private theorem exists_span_eq_maximalIdeal_card_eq_ringKrullDim_consolidated160 (Q : Type u) [CommRing Q] [IsRegularLocalRing Q] :
    ∃ (n : ℕ) (z : Fin n → Q), Ideal.span (Set.range z) = IsLocalRing.maximalIdeal Q ∧
      (n : WithBot ℕ∞) = ringKrullDim Q := by
  classical
  have : IsLocalRing Q := inferInstance
  have : IsNoetherianRing Q := inferInstance
  have : Module.Finite (IsLocalRing.ResidueField Q) (IsLocalRing.CotangentSpace Q) :=
    inferInstance
  have hsurjres : Function.Surjective (algebraMap Q (IsLocalRing.ResidueField Q)) := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨y, rfl⟩
  set b := Module.finBasis (IsLocalRing.ResidueField Q) (IsLocalRing.CotangentSpace Q) with hb
  have hsurj : Function.Surjective (IsLocalRing.maximalIdeal Q).toCotangent :=
    Ideal.toCotangent_surjective _
  choose w hw using fun i => hsurj (b i)
  have hspanQ : Submodule.span Q (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span (IsLocalRing.ResidueField Q) (Set.range b) := by
      rw [b.span_eq]
      trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact Submodule.subset_span hy
    · exact zero_mem _
    · intro y z _ _ hy hz
      exact add_mem hy hz
    · intro c y _ hy
      obtain ⟨c', rfl⟩ := hsurjres c
      rw [algebraMap_smul]
      exact Submodule.smul_mem _ _ hy
  have himg : ⇑(IsLocalRing.maximalIdeal Q).toCotangent '' (Set.range w) = Set.range b := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hw)
  have hMtop : Submodule.span Q (Set.range w) = ⊤ := by
    refine IsLocalRing.CotangentSpace.map_eq_top_iff.mp ?_
    rw [Submodule.map_span, himg]
    exact hspanQ
  refine ⟨Module.finrank (IsLocalRing.ResidueField Q) (IsLocalRing.CotangentSpace Q),
    fun i => ((w i : Q)), ?_, ?_⟩
  · have h1 : Submodule.map (IsLocalRing.maximalIdeal Q).subtype
        (Submodule.span Q (Set.range w)) = Ideal.span (Set.range fun i => ((w i : Q))) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [← h1, hMtop, Submodule.map_subtype_top]
  · exact (IsRegularLocalRing.iff_finrank_cotangentSpace Q).mp ‹_›

theorem exists_regularSystemOfParameters_containing_etaleChartCoords (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] [IsLocalRing A] (J₀ : Finset (Fin m))
    (hJ₀ : ∀ j ∈ J₀, etaleChartCoord k m S j ∈ q) :
    ∃ (d : ℕ) (x : Fin d → S),
      (∀ i, x i ∈ q) ∧
      (∀ j ∈ J₀, ∃ i, x i = etaleChartCoord k m S j) ∧
      Ideal.span (Set.range fun i => algebraMap S A (x i)) = IsLocalRing.maximalIdeal A ∧
      (d : WithBot ℕ∞) = ringKrullDim A := by
  classical
  set I := Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J₀) with hIdef
  have hreg : IsRegularLocalRing (A ⧸ I) :=
    isRegularLocalRing_quotient_map_etaleChartCoordIdeal k m S q A J₀ hJ₀
  have : IsLocalRing (A ⧸ I) := inferInstance
  obtain ⟨n, z, hzspan, hzdim⟩ := exists_span_eq_maximalIdeal_card_eq_ringKrullDim_consolidated160 (A ⧸ I)
  have hIle : I ≤ IsLocalRing.maximalIdeal A := by
    rw [hIdef]
    refine Ideal.map_le_iff_le_comap.mpr ?_
    intro s hs
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A q s inferInstance).mpr
      (etaleChartCoordIdeal_le k m S J₀ q hJ₀ hs)
  have hmaxQ : IsLocalRing.maximalIdeal (A ⧸ I)
      = Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal A) :=
    (IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective).symm
  choose a ha using fun i : Fin n => Ideal.Quotient.mk_surjective (z i)
  have hamem : ∀ i, a i ∈ IsLocalRing.maximalIdeal A := by
    intro i
    refine (Ideal.mem_quotient_iff_mem hIle).mp ?_
    rw [← hmaxQ, ha i, ← hzspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  choose rt hrt using fun i : Fin n => IsLocalization.surj (M := q.primeCompl) (a i)
  have hsq : ∀ i : Fin n, (rt i).1 ∈ q := by
    intro i
    refine (IsLocalization.AtPrime.to_map_mem_maximal_iff A q (rt i).1 inferInstance).mp ?_
    rw [← hrt i]
    exact Ideal.mul_mem_right _ _ (hamem i)
  refine ⟨J₀.card + n,
    Fin.append
      (fun i : Fin J₀.card => etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
      (fun i : Fin n => (rt i).1), ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]
      exact hJ₀ _ (J₀.equivFin.symm i).2
    · rw [Fin.append_right]
      exact hsq i
  · intro j hj
    refine ⟨Fin.castAdd n (J₀.equivFin ⟨j, hj⟩), ?_⟩
    rw [Fin.append_left, Equiv.symm_apply_apply]
  · have hxq : ∀ i : Fin (J₀.card + n),
        Fin.append
          (fun i : Fin J₀.card =>
            etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
          (fun i : Fin n => (rt i).1) i ∈ q := by
      intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left]
        exact hJ₀ _ (J₀.equivFin.symm i).2
      · rw [Fin.append_right]
        exact hsq i
    have hTle : Ideal.span (Set.range fun i =>
        algebraMap S A (Fin.append
          (fun i : Fin J₀.card =>
            etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
          (fun i : Fin n => (rt i).1) i)) ≤ IsLocalRing.maximalIdeal A := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A q _ inferInstance).mpr (hxq i)
    have hIT : I ≤ Ideal.span (Set.range fun i =>
        algebraMap S A (Fin.append
          (fun i : Fin J₀.card =>
            etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
          (fun i : Fin n => (rt i).1) i)) := by
      rw [hIdef, etaleChartCoordIdeal_eq_span_image, Ideal.map_span, Set.image_image]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨j, hj, rfl⟩
      refine Ideal.subset_span ⟨Fin.castAdd n (J₀.equivFin ⟨j, Finset.mem_coe.mp hj⟩), ?_⟩
      refine congrArg (algebraMap S A) ?_
      rw [Fin.append_left, Equiv.symm_apply_apply]
    refine le_antisymm hTle ?_
    intro y hy
    refine (Ideal.mem_quotient_iff_mem hIT).mp ?_
    have hz : ∀ i : Fin n, z i ∈ Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range fun i =>
        algebraMap S A (Fin.append
          (fun i : Fin J₀.card =>
            etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
          (fun i : Fin n => (rt i).1) i))) := by
      intro i
      have hunit : IsUnit (Ideal.Quotient.mk I (algebraMap S A ((rt i).2 : S))) :=
        (IsLocalization.map_units A ((rt i).2)).map (Ideal.Quotient.mk I)
      obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hunit
      have hmem : Ideal.Quotient.mk I (algebraMap S A ((rt i).1))
          ∈ Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range fun i =>
            algebraMap S A (Fin.append
              (fun i : Fin J₀.card =>
                etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
              (fun i : Fin n => (rt i).1) i))) := by
        refine Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨Fin.natAdd J₀.card i, ?_⟩)
        exact congrArg (algebraMap S A) (Fin.append_right _ _ i)
      have heq : Ideal.Quotient.mk I (algebraMap S A ((rt i).1))
          = z i * Ideal.Quotient.mk I (algebraMap S A ((rt i).2 : S)) := by
        rw [← hrt i, map_mul, ha i]
      have hzi : z i = Ideal.Quotient.mk I (algebraMap S A ((rt i).1)) * v := by
        rw [heq, mul_assoc, hv, mul_one]
      rw [hzi]
      exact Ideal.mul_mem_right _ _ hmem
    have hmq : IsLocalRing.maximalIdeal (A ⧸ I) ≤ Ideal.map (Ideal.Quotient.mk I)
        (Ideal.span (Set.range fun i =>
          algebraMap S A (Fin.append
            (fun i : Fin J₀.card =>
              etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
            (fun i : Fin n => (rt i).1) i))) := by
      rw [← hzspan]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact hz i
    refine hmq ?_
    rw [hmaxQ]
    exact Ideal.mem_map_of_mem _ hy
  · have h2 := ringKrullDim_quotient_map_etaleChartCoordIdeal_add_card k m S q A J₀ hJ₀
    rw [← hIdef] at h2
    rw [← h2, ← hzdim, Nat.cast_add]
    exact add_comm _ _

end FunctorialResolution.EmbeddedResolution
end
end
