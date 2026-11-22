import Mathlib
import Core5.M11ResolutionData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicGeometry
universe u v w
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometryHypotheses
section


section

def MaxContactHypersurfacesEtaleEquivalent : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (P : Scheme.{u})
      (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p]
      [LocallyOfFiniteType p] [QuasiCompact p]
      (A : P.IdealSheafData) (μ : ℕ), 1 ≤ μ →
    IsMaxContactInvariant k p A μ →
    (∀ x : ↥P, orderAt A x ≤ (μ : ℕ∞)) →
    ∀ (N : List P.IdealSheafData) (H₁ H₂ : P.IdealSheafData),
      InStrictNormalCrossingPosition p (H₁ :: N) → InStrictNormalCrossingPosition p (H₂ :: N) →
      IsMaxContactHypersurface k p A μ H₁ → IsMaxContactHypersurface k p A μ H₂ →
      ∃ (V : Scheme.{u}) (ψ₁ ψ₂ : V ⟶ P) (_ : Etale ψ₁)
        (_ : Etale ψ₂)
        (_ : QuasiCompact (ψ₁ ≫ p))
        (hft : LocallyOfFiniteType (ψ₁ ≫ p)),
        ψ₁ ≫ p = ψ₂ ≫ p ∧
        orderAtLeastLocus A μ ⊆ Set.range ψ₁.base ∧
        orderAtLeastLocus A μ ⊆ Set.range ψ₂.base ∧
        A.comap ψ₁ = A.comap ψ₂ ∧
        H₁.comap ψ₁ = H₂.comap ψ₂ ∧
        N.map (fun D => D.comap ψ₁) = N.map (fun D => D.comap ψ₂) ∧
        (@maxContactIdeal k _ _ V (ψ₁ ≫ p) hft (A.comap ψ₁) μ).subschemeι ≫ ψ₁ =
          (@maxContactIdeal k _ _ V (ψ₁ ≫ p) hft (A.comap ψ₁) μ).subschemeι ≫ ψ₂

def ExistsMaxContactControlledTransforms : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (V : Scheme.{u})
      (q : V ⟶ Spec (CommRingCat.of k)) [Smooth q]
      [LocallyOfFiniteType q]
      (A' : V.IdealSheafData) (μ : ℕ), 1 ≤ μ →
    ∀ (E' : List V.IdealSheafData) (u : MarkedSequenceOfBlowups q A' μ E'),
      (∀ i : ℕ, i ≤ u.length → IsLocallyNoetherian (u.schemeAt i)) →
      (∀ i : ℕ, i < u.length → ∀ J : (u.schemeAt i).IdealSheafData,
        (((u.center i).support : Set ↥(u.schemeAt i)) ⊆ ((J.support : Set ↥(u.schemeAt i)))) →
        J ≤ u.center i) →
      ∃ c : ∀ i : ℕ, (u.schemeAt i).IdealSheafData,
        c 0 = (maxContactIdeal k q A' μ).comap u.isoZero.hom ∧
        (∀ i : ℕ, i < u.length →
          Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i) * c (i + 1) =
            (c i).comap (u.transitionMapSucc i)) ∧
        (∀ i : ℕ, i < u.length → c i ≤ u.center i)

namespace OrderReduction

structure OrderReductionHypotheses : Prop where
  maxContactChain : ExistsMaxContactControlledTransforms.{u}
  center_mem_coSupport : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ),
    i < s.length → ∀ x : ↥(s.schemeAt i),
      x ∈ (((s.center i).support : Set ↥(s.schemeAt i))) →
      (s.projectionToBase i).base x ∈ orderAtLeastLocus T.ideal T.mult
  dBalanced_comap : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
      ∀ [LocallyOfFiniteType T.structMap]
        [LocallyOfFiniteType q],
      IsDerivBalanced T.base T.structMap T.ideal T.mult →
      IsDerivBalanced T.base q (T.ideal.comap h) T.mult
  schemeDim_le_of_etale : ∀ (V P : Scheme.{u}) (f : V ⟶ P) [Etale f]
      [IsLocallyNoetherian P],
      topologicalKrullDim ↥P < ⊤ → krullDimSucc V ≤ krullDimSucc P
  isLocallyNoetherian_obj : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ),
    i ≤ s.length → IsLocallyNoetherian (s.schemeAt i)
  lifting : BlowupLiftEqOnControlledTransform.{u}
  smooth_center_radical : ∀ (k : Type u) [Field k] (X : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData),
      Smooth (Z.subschemeι ≫ p) →
      ∀ J : X.IdealSheafData,
        (((Z.support : Set ↥X)) ⊆ ((J.support : Set ↥X))) → J ≤ Z
  etaleEqualization : MaxContactHypersurfacesEtaleEquivalent.{u}
  isStrictPullbackSeq : ∀ (X' X : Scheme.{u}) (φ : X' ⟶ X) (s' : SequenceOfBlowups X')
      (s : SequenceOfBlowups X), IsPullbackBlowupSequence φ s' s →
      (∀ i : ℕ, i < s.length → (((s.center i).support : Set ↥(s.schemeAt i))).Nonempty) →
      (∀ i : ℕ, i < s.length → ∀ x ∈ (((s.center i).support : Set ↥(s.schemeAt i))),
        (s.projectionToBase i).base x ∈ Set.range φ.base) →
      IsStrictPullbackBlowupSeq φ s' s
  valid_pullbackAlong : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h] [QuasiCompact q],
      h ≫ T.structMap = q → (T.pullbackAlong Y q h).IsAdmissible

end OrderReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IndependenceOfHypersurface
section



namespace DivisorReductionIndependence

private theorem toSequenceOfBlowups_eq_of_heq_consolidated283 {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I₁ I₂ : X.IdealSheafData} {m₁ m₂ : ℕ}
    {E₁ E₂ : List X.IdealSheafData} (s₁ : MarkedSequenceOfBlowups p I₁ m₁ E₁)
    (s₂ : MarkedSequenceOfBlowups p I₂ m₂ E₂) (hI : I₁ = I₂) (hm : m₁ = m₂) (hE : E₁ = E₂)
    (h : HEq s₁ s₂) : s₁.toSequenceOfBlowups = s₂.toSequenceOfBlowups := by
  subst hI
  subst hm
  subst hE
  rw [eq_of_heq h]

theorem subschemeι_comap_comp_comp_eq {A B C : Scheme.{u}} (e : A ⟶ B) (J : B.IdealSheafData)
    (f g : B ⟶ C) (h : J.subschemeι ≫ f = J.subschemeι ≫ g) :
    (J.comap e).subschemeι ≫ (e ≫ f) = (J.comap e).subschemeι ≫ (e ≫ g) := by
  have : IsClosedImmersion (Limits.pullback.fst e J.subschemeι) := inferInstance
  have hker : J.comap e = Scheme.Hom.ker (Limits.pullback.fst e J.subschemeι) := rfl
  have hc := Limits.pullback.condition (f := e) (g := J.subschemeι)
  have key : Limits.pullback.fst e J.subschemeι ≫ (e ≫ f)
      = Limits.pullback.fst e J.subschemeι ≫ (e ≫ g) := by
    calc Limits.pullback.fst e J.subschemeι ≫ (e ≫ f)
        = (Limits.pullback.fst e J.subschemeι ≫ e) ≫ f := by rw [Category.assoc]
      _ = (Limits.pullback.snd e J.subschemeι ≫ J.subschemeι) ≫ f := by rw [hc]
      _ = Limits.pullback.snd e J.subschemeι ≫ (J.subschemeι ≫ f) := by rw [Category.assoc]
      _ = Limits.pullback.snd e J.subschemeι ≫ (J.subschemeι ≫ g) := by rw [h]
      _ = (Limits.pullback.snd e J.subschemeι ≫ J.subschemeι) ≫ g := by rw [Category.assoc]
      _ = (Limits.pullback.fst e J.subschemeι ≫ e) ≫ g := by rw [hc]
      _ = Limits.pullback.fst e J.subschemeι ≫ (e ≫ g) := by rw [Category.assoc]
  rw [hker, ← kerSubschemeIso_hom_comp (Limits.pullback.fst e J.subschemeι), Category.assoc,
    Category.assoc, key]

theorem le_center_of_center_support_subset (hin : OrderReduction.OrderReductionHypotheses.{u}) (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups)
    (i : ℕ) (hi : i < s.length) (J : (s.schemeAt i).IdealSheafData)
    (hJ : (((s.center i).support : Set ↥(s.schemeAt i))) ⊆ ((J.support : Set ↥(s.schemeAt i)))) :
    J ≤ s.center i :=
  hin.smooth_center_radical T.base (s.schemeAt i) (s.projectionToBase i ≫ T.structMap) (s.center i)
    (s.center_smooth i hi) J hJ

section
variable (hin : OrderReduction.OrderReductionHypotheses.{u}) (P : ℕ → Prop) (hPdown : ∀ a b : ℕ, a ≤ b → P b → P a) (A B : PrincipalizationAssignment.{u}) (hspec : IsBoundaryDivisorReduction P 0 A B) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : P T.krullDimSucc) (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) (hD : ∀ hft : LocallyOfFiniteType T.structMap, T.IsBalanced hft)
include hin hPdown hspec hV hP hO hD

theorem isAdmissible_and_isStrictPullbackBlowupSeq_of_etale
    (hlen : 0 < T.boundary.length)
    (V : Scheme.{u}) (q : V ⟶ Spec (CommRingCat.of T.base)) (ψ : V ⟶ T.scheme)
    (hψ : Etale ψ) (hq : QuasiCompact q)
    (hcomp : ψ ≫ T.structMap = q)
    (hcov : orderAtLeastLocus T.ideal T.mult ⊆ Set.range ψ.base) :
    (T.pullbackAlong V q ψ).IsAdmissible ∧
      IsStrictPullbackBlowupSeq ψ (A (T.pullbackAlong V q ψ)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by
  have := hV.charZero
  have hft : LocallyOfFiniteType T.structMap := hV.locallyOfFiniteType
  have : QuasiCompact T.structMap := hV.quasiCompact
  have : Smooth T.structMap := hV.smooth
  have : Etale ψ := hψ
  have : QuasiCompact q := hq
  have : Smooth ψ := inferInstance
  have := hV.isNoetherian
  have : IsLocallyNoetherian T.scheme := inferInstance
  have hVal : (T.pullbackAlong V q ψ).IsAdmissible := hin.valid_pullbackAlong T hV V q ψ hcomp
  have hftq : LocallyOfFiniteType q := hVal.locallyOfFiniteType
  have hOT : T.IsOrderBoundedByMult := (T.isOrderBoundedByMult_iff).2 hO
  have hP' : P (T.pullbackAlong V q ψ).krullDimSucc := by
    refine hPdown _ _ ?_ hP
    exact hin.schemeDim_le_of_etale V T.scheme ψ hV.topologicalKrullDim_lt_top
  have hO' : (T.pullbackAlong V q ψ).IsOrderBoundedByMult := by
    rw [MarkedIdealWithBoundary.isOrderBoundedByMult_iff]
    intro x
    exact le_of_eq_of_le (orderAt_comap T.base T.structMap ψ T.ideal x) (hO _)
  have hderivBal : IsDerivBalanced T.base T.structMap T.ideal T.mult := hD hft
  have hDB' : IsDerivBalanced T.base q (T.ideal.comap ψ) T.mult :=
    hin.dBalanced_comap T hV V q ψ hcomp hderivBal
  have hD' : ∀ hft2 : LocallyOfFiniteType (T.pullbackAlong V q ψ).structMap,
      (T.pullbackAlong V q ψ).IsBalanced hft2 := fun _ => hDB'
  have hj' : 0 < (T.pullbackAlong V q ψ).boundary.length := by
    change 0 < (T.boundary.map (fun D => D.comap ψ)).length
    rw [List.length_map]
    exact hlen
  have hpull : IsPullbackBlowupSequence ψ (A (T.pullbackAlong V q ψ)).toSequenceOfBlowups (A T).toSequenceOfBlowups :=
    hspec.isPullbackBlowupSequence_of_smooth T hV hP hOT (hD _) hlen V q ψ hcomp hVal hP' hO' (hD' _) hj'
  refine ⟨hVal, hin.isStrictPullbackSeq V T.scheme ψ _ _ hpull ?_ ?_⟩
  · intro i hi
    exact hspec.center_nonempty T hV hP hOT (hD _) hlen i hi
  · intro i hi x hx
    exact hcov (hin.center_mem_coSupport T hV (A T) i hi x hx)

theorem isomorphic_withBoundary_cons_of_isMaxContactHypersurface
    (hMC : ∀ [LocallyOfFiniteType T.structMap],
      IsMaxContactInvariant T.base T.structMap T.ideal T.mult)
    (N : List T.scheme.IdealSheafData) (H₁ H₂ : T.scheme.IdealSheafData)
    (hbd : T.boundary = H₁ :: N)
    (hV₂ : (T.withBoundary (H₂ :: N)).IsAdmissible)
    (hH₁ : ∀ [LocallyOfFiniteType T.structMap],
      IsMaxContactHypersurface T.base T.structMap T.ideal T.mult H₁)
    (hH₂ : ∀ [LocallyOfFiniteType T.structMap],
      IsMaxContactHypersurface T.base T.structMap T.ideal T.mult H₂) :
    (A T).toSequenceOfBlowups.Isomorphic (A (T.withBoundary (H₂ :: N))).toSequenceOfBlowups := by
  have := hV.charZero
  have hft : LocallyOfFiniteType T.structMap := hV.locallyOfFiniteType
  have : QuasiCompact T.structMap := hV.quasiCompact
  have : Smooth T.structMap := hV.smooth
  have hsnc₁ : InStrictNormalCrossingPosition T.structMap (H₁ :: N) := by
    rw [← hbd]; exact hV.snc
  have hsnc₂ : InStrictNormalCrossingPosition T.structMap (H₂ :: N) := hV₂.snc
  obtain ⟨V, ψ₁, ψ₂, hψ₁, hψ₂, hqc, hftq, hcompeq, hcov₁, hcov₂, hidl, hHH, hNN, hmax⟩ :=
    hin.etaleEqualization T.base T.scheme T.structMap T.ideal T.mult hV.one_le_mult hMC hO
      N H₁ H₂ hsnc₁ hsnc₂ hH₁ hH₂
  have : Etale ψ₁ := hψ₁
  have : Etale ψ₂ := hψ₂
  have : QuasiCompact (ψ₁ ≫ T.structMap) := hqc
  have hcomp₂ : ψ₂ ≫ (T.withBoundary (H₂ :: N)).structMap = ψ₁ ≫ T.structMap := hcompeq.symm
  obtain ⟨hVal₁, hstr₁⟩ :=
    isAdmissible_and_isStrictPullbackBlowupSeq_of_etale hin P hPdown A B hspec T hV hP hO hD
      (by simp [hbd]) V (ψ₁ ≫ T.structMap) ψ₁ hψ₁ hqc rfl hcov₁
  obtain ⟨hVal₂, hstr₂⟩ :=
    isAdmissible_and_isStrictPullbackBlowupSeq_of_etale hin P hPdown A B hspec (T.withBoundary (H₂ :: N)) hV₂
      (by rw [MarkedIdealWithBoundary.withBoundary_dim]; exact hP) (fun x => hO x) (fun h2 => hD h2)
      (Nat.succ_pos N.length)
      V (ψ₁ ≫ T.structMap) ψ₂ hψ₂ hqc hcomp₂ hcov₂
  have : Smooth (ψ₁ ≫ T.structMap) := hVal₁.smooth
  have : LocallyOfFiniteType (ψ₁ ≫ T.structMap) := hftq
  have hbdy : List.map (fun D : T.scheme.IdealSheafData => D.comap ψ₁) T.boundary
      = List.map (fun D : T.scheme.IdealSheafData => D.comap ψ₂) (H₂ :: N) := by
    rw [hbd]
    simp only [List.map_cons]
    rw [hHH, hNN]
  have hTT : T.pullbackAlong V (ψ₁ ≫ T.structMap) ψ₁
      = (T.withBoundary (H₂ :: N)).pullbackAlong V (ψ₁ ≫ T.structMap) ψ₂ := by
    show MarkedIdealWithBoundary.mk T.base V (ψ₁ ≫ T.structMap) (T.ideal.comap ψ₁) T.mult
        (List.map (fun D : T.scheme.IdealSheafData => D.comap ψ₁) T.boundary)
      = MarkedIdealWithBoundary.mk T.base V (ψ₁ ≫ T.structMap) (T.ideal.comap ψ₂) T.mult
        (List.map (fun D : T.scheme.IdealSheafData => D.comap ψ₂) (H₂ :: N))
    rw [hidl, hbdy]
  have hDeq : (A (T.pullbackAlong V (ψ₁ ≫ T.structMap) ψ₁)).toSequenceOfBlowups
      = (A ((T.withBoundary (H₂ :: N)).pullbackAlong V (ψ₁ ≫ T.structMap) ψ₂)).toSequenceOfBlowups :=
    toSequenceOfBlowups_eq_of_heq_consolidated283 _ _ hidl rfl hbdy (congr_arg_heq A hTT)
  rw [← hDeq] at hstr₂
  obtain ⟨c, hc0, hcsucc, hcle⟩ :=
    hin.maxContactChain T.base V (ψ₁ ≫ T.structMap) (T.ideal.comap ψ₁) T.mult hV.one_le_mult
      (List.map (fun D : T.scheme.IdealSheafData => D.comap ψ₁) T.boundary)
      (A (T.pullbackAlong V (ψ₁ ≫ T.structMap) ψ₁))
      (fun i hi => hin.isLocallyNoetherian_obj (T.pullbackAlong V (ψ₁ ≫ T.structMap) ψ₁) hVal₁
        (A (T.pullbackAlong V (ψ₁ ≫ T.structMap) ψ₁)) i hi)
      (fun i hi J hJ => le_center_of_center_support_subset hin (T.pullbackAlong V (ψ₁ ≫ T.structMap) ψ₁)
        (A (T.pullbackAlong V (ψ₁ ≫ T.structMap) ψ₁)) i hi J hJ)
  refine SequenceOfBlowups.isomorphic_of_isStrictPullback_same_source (A T).toSequenceOfBlowups
    (A (T.withBoundary (H₂ :: N))).toSequenceOfBlowups hin.lifting hstr₁ hstr₂ ?_ ?_ ?_ ?_ c ?_ hcsucc hcle
  · intro i hi x hx
    exact hcov₁ (hin.center_mem_coSupport T hV (A T) i hi x hx)
  · intro i hi x hx
    exact hcov₂ (hin.center_mem_coSupport (T.withBoundary (H₂ :: N)) hV₂
      (A (T.withBoundary (H₂ :: N))) i hi x hx)
  · intro i hi J hJ
    exact le_center_of_center_support_subset hin T (A T) i hi J (SetLike.coe_subset_coe.mpr hJ)
  · intro i hi J hJ
    exact le_center_of_center_support_subset hin (T.withBoundary (H₂ :: N)) (A (T.withBoundary (H₂ :: N))) i hi J
      (SetLike.coe_subset_coe.mpr hJ)
  · rw [hc0]
    exact subschemeι_comap_comp_comp_eq _ _ ψ₁ ψ₂ hmax


end

end DivisorReductionIndependence

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
section

open CategoryTheory.Limits

open scoped Classical

section

namespace MaxContactReduction

def emptyMarkedSeq (T : MarkedIdealWithBoundary.{u}) : T.SequenceOfBlowups :=
  (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).toMarkedSequenceOfBlowups

def IsMaxContactCoord (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ) {U : X.Opens} {n : ℕ}
    (c : EtaleChart p U n) (j : Fin n) : Prop :=
  c.coordIdeal {j} ≤ restrictIdeal (maxContactIdeal k p I m) U

structure FiniteOpenCoverWithIdeals (T : MarkedIdealWithBoundary.{u}) : Type (u + 1) where
  idx : Type u
  finiteIdx : Finite idx
  opens : idx → T.scheme.Opens
  localIdeal : (i : idx) → (opens i).toScheme.IdealSheafData

instance instFiniteCoverIdx {T : MarkedIdealWithBoundary.{u}} (D : FiniteOpenCoverWithIdeals T) : Finite D.idx :=
  D.finiteIdx

structure IsMaxContactCover (T : MarkedIdealWithBoundary.{u}) (D : FiniteOpenCoverWithIdeals T)
    (hft : LocallyOfFiniteType T.structMap) (W : T.scheme.IdealSheafData) (μ : ℕ) : Prop where
  covers : iSup D.opens = ⊤
  isAffine : ∀ i : D.idx, IsAffineOpen (D.opens i)
  dichotomy : ∀ i : D.idx,
    (Disjoint (orderAtLeastLocus W μ) ((D.opens i : T.scheme.Opens) : Set ↥T.scheme) ∧
      D.localIdeal i = ⊤) ∨
    (∃ (n : ℕ) (c : EtaleChart T.structMap (D.opens i) n) (j : Fin n),
      D.localIdeal i = c.coordIdeal {j} ∧
        @IsMaxContactCoord T.base _ T.scheme T.structMap hft W μ (D.opens i) n c j)

def trivialCover (T : MarkedIdealWithBoundary.{u}) : FiniteOpenCoverWithIdeals T where
  idx := PUnit.{u + 1}
  finiteIdx := inferInstance
  opens := fun _ => ⊤
  localIdeal := fun _ => ⊤

def maxContactCover (T : MarkedIdealWithBoundary.{u}) (hft : LocallyOfFiniteType T.structMap)
    (W : T.scheme.IdealSheafData) (μ : ℕ) : FiniteOpenCoverWithIdeals T :=
  if h : ∃ D : FiniteOpenCoverWithIdeals T, IsMaxContactCover T D hft W μ then h.choose else trivialCover T

def FiniteOpenCoverWithIdeals.disjointUnion {T : MarkedIdealWithBoundary.{u}} (D : FiniteOpenCoverWithIdeals T) : Scheme.{u} :=
  sigmaOpens T.scheme D.opens

def FiniteOpenCoverWithIdeals.disjointUnionMap {T : MarkedIdealWithBoundary.{u}} (D : FiniteOpenCoverWithIdeals T) : D.disjointUnion ⟶ T.scheme :=
  sigmaOpensDesc T.scheme D.opens

def FiniteOpenCoverWithIdeals.ι {T : MarkedIdealWithBoundary.{u}} (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    (D.opens i).toScheme ⟶ D.disjointUnion :=
  Sigma.ι (fun i => (D.opens i).toScheme) i

def FiniteOpenCoverWithIdeals.iInfImageIdeal {T : MarkedIdealWithBoundary.{u}} (D : FiniteOpenCoverWithIdeals T) : D.disjointUnion.IdealSheafData :=
  ⨅ i : D.idx, imageIdealSheaf (D.ι i) (D.localIdeal i)

def FiniteOpenCoverWithIdeals.markedTriple {T : MarkedIdealWithBoundary.{u}} (D : FiniteOpenCoverWithIdeals T) (W : T.scheme.IdealSheafData)
    (μ : ℕ) : MarkedIdealWithBoundary.{u} where
  base := T.base
  instField := T.instField
  scheme := D.disjointUnion
  structMap := D.disjointUnionMap ≫ T.structMap
  ideal := W.comap D.disjointUnionMap
  mult := μ
  boundary := T.boundary.map (fun Dv => Dv.comap D.disjointUnionMap)

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def iteratedStrictTransform (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) :
    (i : ℕ) → (s.obj i).IdealSheafData
  | 0 => H.comap s.isoZero.hom
  | i + 1 => Blowup.strictTransform (s.map i) (s.center i) (iteratedStrictTransform s H i)

section
variable (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData)

theorem iteratedStrictTransform_zero :
    iteratedStrictTransform s H 0 = H.comap s.isoZero.hom := rfl

theorem iteratedStrictTransform_succ (i : ℕ) :
    iteratedStrictTransform s H (i + 1) =
      Blowup.strictTransform (s.map i) (s.center i) (iteratedStrictTransform s H i) := rfl


end

def strictTransformAtLength (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) :
    (s.obj s.length).IdealSheafData :=
  iteratedStrictTransform s H s.length

theorem strictTransformAtLength_eq (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) :
    strictTransformAtLength s H = iteratedStrictTransform s H s.length := rfl

def asMarkedData (s : MarkedBlowupSequenceData p I m E) (d : BlowupSequenceData (s.obj s.length)) :
    Option (MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length)) :=
  if h : d.IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) then
    some (d.toMarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) h)
  else
    none

def concatOfIsMarked (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (d : BlowupSequenceData (s.obj s.length)) : MarkedBlowupSequenceData p I m E :=
  match asMarkedData s d with
  | some t => s.append t hinv
  | none => s

end

def tunedIdeal (S : MarkedIdealWithBoundary.{u}) (hft : LocallyOfFiniteType S.structMap) :
    S.scheme.IdealSheafData :=
  @balancedTunedSheaf S.base _ _ S.scheme S.structMap hft S.ideal S.mult

def tunedTriple (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) : MarkedIdealWithBoundary.{u} where
  base := S.base
  instField := S.instField
  scheme := s.obj s.length
  structMap := s.proj s.length ≫ S.structMap
  ideal :=
    @balancedTunedSheaf S.base _ _ (s.obj s.length) (s.proj s.length ≫ S.structMap) hft
      (s.ideal s.length) S.mult
  mult := tuningExponent S.mult
  boundary := extra ++ (s.boundary s.length).drop keep

def appendLowerDimReduction (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups)
    (S : MarkedIdealWithBoundary.{u}) (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) (n : ℕ) :
    MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary :=
  if hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap) then
    if hdim : (tunedTriple S s hft extra keep).krullDimSucc ≤ T.krullDimSucc then
      concatOfIsMarked hinv s
        (BlowupSequenceData.ofSequenceOfBlowups (resolveLower (tunedTriple S s hft extra keep) hdim n).toSequenceOfBlowups)
    else s
  else s

def separateBoundary (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary.{u}) :
    ℕ → MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary
  | 0 => emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary
  | j + 1 => appendLowerDimReduction hinv T resolveLower S (separateBoundary hinv T resolveLower S j) [] 0 j

def reduceAlongHypersurface (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary.{u})
    (H : S.scheme.IdealSheafData) : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary :=
  appendLowerDimReduction hinv T resolveLower S (separateBoundary hinv T resolveLower S S.boundary.length)
    [strictTransformAtLength (separateBoundary hinv T resolveLower S S.boundary.length) H] S.boundary.length 0

def descendStrictPullback (T S : MarkedIdealWithBoundary.{u}) (φ : S.scheme ⟶ T.scheme)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) :
    Option (BlowupSequenceData T.scheme) :=
  if h : ∃ d : BlowupSequenceData T.scheme,
      IsStrictPullbackBlowupSeq φ s.toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups then
    some h.choose
  else
    none

def asMarkedSeq (T : MarkedIdealWithBoundary.{u}) (d : BlowupSequenceData T.scheme) : T.SequenceOfBlowups :=
  if h : d.IsMarked T.structMap T.ideal T.mult T.boundary then
    (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary h).toMarkedSequenceOfBlowups
  else
    emptyMarkedSeq T

def dropTrivialBoundary (T : MarkedIdealWithBoundary.{u}) : MarkedIdealWithBoundary.{u} :=
  T.withBoundary (T.boundary.filter (fun D => decide (D ≠ ⊤)))

section
variable (T : MarkedIdealWithBoundary.{u})

theorem dropTrivialBoundary_def :
    dropTrivialBoundary T = T.withBoundary (T.boundary.filter (fun D => decide (D ≠ ⊤))) := rfl

@[simp] theorem dropTrivialBoundary_baseField : (dropTrivialBoundary T).base = T.base := rfl

@[simp] theorem dropTrivialBoundary_scheme : (dropTrivialBoundary T).scheme = T.scheme := rfl

@[simp] theorem dropTrivialBoundary_structureMorphism : (dropTrivialBoundary T).structMap = T.structMap := rfl

@[simp] theorem dropTrivialBoundary_ideal : (dropTrivialBoundary T).ideal = T.ideal := rfl

@[simp] theorem dropTrivialBoundary_mult : (dropTrivialBoundary T).mult = T.mult := rfl

@[simp] theorem dropTrivialBoundary_dim : (dropTrivialBoundary T).krullDimSucc = T.krullDimSucc := rfl

theorem dropTrivialBoundary_boundary :
    (dropTrivialBoundary T).boundary = T.boundary.filter (fun D => decide (D ≠ ⊤)) := rfl


end

def reduceOrderOfValid (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (hv : T.IsAdmissible) : T.SequenceOfBlowups :=
  have hft : LocallyOfFiniteType (dropTrivialBoundary T).structMap := hv.locallyOfFiniteType
  let W := tunedIdeal (dropTrivialBoundary T) hft
  let μ := tuningExponent (dropTrivialBoundary T).mult
  let D := maxContactCover (dropTrivialBoundary T) hft W μ
  let S := D.markedTriple W μ
  match descendStrictPullback (dropTrivialBoundary T) S D.disjointUnionMap (reduceAlongHypersurface hinv (dropTrivialBoundary T) resolveLower S D.iInfImageIdeal) with
  | some d => asMarkedSeq T d
  | none => emptyMarkedSeq T

def reduceOrder (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) : T.SequenceOfBlowups :=
  if hv : T.IsAdmissible then
    if orderAtLeastLocus T.ideal T.mult = ∅ then emptyMarkedSeq T else reduceOrderOfValid hinv T resolveLower hv
  else
    emptyMarkedSeq T

theorem reduceOrder_of_orderAtLeastLocus_eq_empty (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (hv : T.IsAdmissible)
    (h : orderAtLeastLocus T.ideal T.mult = ∅) : reduceOrder hinv T resolveLower = emptyMarkedSeq T := by
  unfold reduceOrder
  rw [dif_pos hv, if_pos h]

end MaxContactReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
section


open scoped Classical


namespace MaxContactCoverData

noncomputable def balancedTunedIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) : T.scheme.IdealSheafData :=
  @balancedTunedSheaf T.base _ _ T.scheme T.structMap hv.locallyOfFiniteType T.ideal T.mult

abbrev tunedMult (T : MarkedIdealWithBoundary.{u}) : ℕ := tuningExponent T.mult

noncomputable def chosenCoverData (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    MaxContactReduction.FiniteOpenCoverWithIdeals T :=
  MaxContactReduction.maxContactCover T hv.locallyOfFiniteType (balancedTunedIdeal T hv) (tunedMult T)

section
variable (T : MarkedIdealWithBoundary.{u})

theorem isMaxContactCover_maxContactCover (hft : LocallyOfFiniteType T.structMap) (W : T.scheme.IdealSheafData) (μ : ℕ)
    (h : ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T, MaxContactReduction.IsMaxContactCover T D hft W μ) :
    MaxContactReduction.IsMaxContactCover T (MaxContactReduction.maxContactCover T hft W μ) hft W μ := by
  have he : MaxContactReduction.maxContactCover T hft W μ = h.choose := dif_pos h
  rw [he]
  exact h.choose_spec

theorem isMaxContactCover_chosenCoverData (hv : T.IsAdmissible)
    (h : ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T,
      MaxContactReduction.IsMaxContactCover T D hv.locallyOfFiniteType (balancedTunedIdeal T hv) (tunedMult T)) :
    MaxContactReduction.IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType
      (balancedTunedIdeal T hv) (tunedMult T) :=
  isMaxContactCover_maxContactCover T hv.locallyOfFiniteType (balancedTunedIdeal T hv) (tunedMult T) h


end

@[reducible] noncomputable def coverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (chosenCoverData T hv).disjointUnion ⟶ T.scheme :=
  (chosenCoverData T hv).disjointUnionMap

theorem coverMap_eq_sigmaOpensDesc (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    coverMap T hv = sigmaOpensDesc T.scheme (chosenCoverData T hv).opens := rfl

theorem etale_coverMap_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    Etale (coverMap T hv) := by
  rw [coverMap_eq_sigmaOpensDesc]
  exact etale_sigmaOpensDesc T.scheme (chosenCoverData T hv).opens

instance instEtaleCoverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    Etale (coverMap T hv) :=
  etale_coverMap_of_isAdmissible T hv

theorem smooth_coverMap_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    Smooth (coverMap T hv) := by
  have : Etale (coverMap T hv) := etale_coverMap_of_isAdmissible T hv
  infer_instance

instance instSmoothCoverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    Smooth (coverMap T hv) :=
  smooth_coverMap_of_isAdmissible T hv

theorem flat_coverMap_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    Flat (coverMap T hv) := by
  have : Etale (coverMap T hv) := etale_coverMap_of_isAdmissible T hv
  infer_instance

instance instFlatCoverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    Flat (coverMap T hv) :=
  flat_coverMap_of_isAdmissible T hv

theorem locallyOfFiniteType_coverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    LocallyOfFiniteType (coverMap T hv) := by
  rw [coverMap_eq_sigmaOpensDesc]
  exact locallyOfFiniteType_sigmaOpensDesc T.scheme (chosenCoverData T hv).opens

instance instLocallyOfFiniteTypeCoverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    LocallyOfFiniteType (coverMap T hv) :=
  locallyOfFiniteType_coverMap T hv

@[reducible] noncomputable def coverMaxContactIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (chosenCoverData T hv).disjointUnion.IdealSheafData :=
  (chosenCoverData T hv).iInfImageIdeal

noncomputable def coverTriple (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) : MarkedIdealWithBoundary.{u} :=
  (chosenCoverData T hv).markedTriple (balancedTunedIdeal T hv) (tunedMult T)

section
variable (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)

@[simp] theorem coverTriple_scheme :
    (coverTriple T hv).scheme = (chosenCoverData T hv).disjointUnion := rfl

@[simp] theorem coverTriple_baseField :
    (coverTriple T hv).base = T.base := rfl

@[simp] theorem coverTriple_structureMorphism :
    (coverTriple T hv).structMap = coverMap T hv ≫ T.structMap := rfl

@[simp] theorem coverTriple_ideal :
    (coverTriple T hv).ideal = (balancedTunedIdeal T hv).comap (coverMap T hv) := rfl

@[simp] theorem coverTriple_mult :
    (coverTriple T hv).mult = tunedMult T := rfl

@[simp] theorem coverTriple_boundary :
    (coverTriple T hv).boundary = T.boundary.map (fun D => D.comap (coverMap T hv)) := rfl

@[simp] theorem coverTriple_dim :
    (coverTriple T hv).krullDimSucc = krullDimSucc (chosenCoverData T hv).disjointUnion := rfl


end

noncomputable def coverMarkedBlowupData (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hinv : ComapIsoInvariance.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) :
    MarkedBlowupSequenceData (coverTriple T hv).structMap (coverTriple T hv).ideal
      (coverTriple T hv).mult (coverTriple T hv).boundary :=
  MaxContactReduction.reduceAlongHypersurface hinv T rc (coverTriple T hv) (coverMaxContactIdeal T hv)






section
variable {T S : MarkedIdealWithBoundary.{u}} (φ : S.scheme ⟶ T.scheme) (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)

theorem isStrictPullbackBlowupSeq_of_descendStrictPullback_eq_some {d : BlowupSequenceData T.scheme}
    (hd : MaxContactReduction.descendStrictPullback T S φ s = some d) :
    IsStrictPullbackBlowupSeq φ s.toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups := by
  by_cases hex : ∃ e : BlowupSequenceData T.scheme, IsStrictPullbackBlowupSeq φ s.toBlowupSequenceData.toSequenceOfBlowups e.toSequenceOfBlowups
  · have he : MaxContactReduction.descendStrictPullback T S φ s = some hex.choose := dif_pos hex
    rw [he] at hd
    have h2 : hex.choose = d := Option.some.inj hd
    exact h2 ▸ hex.choose_spec
  · have he : MaxContactReduction.descendStrictPullback T S φ s = none := dif_neg hex
    rw [he] at hd
    simp at hd

theorem exists_descendStrictPullback_eq_some (h : ∃ d : BlowupSequenceData T.scheme, IsStrictPullbackBlowupSeq φ s.toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups) :
    ∃ d : BlowupSequenceData T.scheme, MaxContactReduction.descendStrictPullback T S φ s = some d :=
  ⟨h.choose, dif_pos h⟩


end

section
variable (T : MarkedIdealWithBoundary.{u}) (d : BlowupSequenceData T.scheme) (h : d.IsMarked T.structMap T.ideal T.mult T.boundary)
include h

theorem asMarkedSeq_eq_toMarkedSequence_of_isMarked :
    MaxContactReduction.asMarkedSeq T d =
      (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary h).toMarkedSequenceOfBlowups :=
  dif_pos h

theorem asMarkedSeq_toSequenceOfBlowups :
    (MaxContactReduction.asMarkedSeq T d).toSequenceOfBlowups = d.toSequenceOfBlowups := by
  rw [asMarkedSeq_eq_toMarkedSequence_of_isMarked T d h,
    BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]


end

section
variable (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (hv : T.IsAdmissible) (hne : orderAtLeastLocus T.ideal T.mult ≠ ∅) (htrim : (MaxContactReduction.dropTrivialBoundary T).IsAdmissible) (d : BlowupSequenceData T.scheme) (hd : MaxContactReduction.descendStrictPullback (MaxContactReduction.dropTrivialBoundary T) (coverTriple (MaxContactReduction.dropTrivialBoundary T) htrim) (coverMap (MaxContactReduction.dropTrivialBoundary T) htrim) (coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) htrim hinv rc) = some d)
include hv hne hd

theorem reduceOrder_eq_asMarkedSeq :
    MaxContactReduction.reduceOrder hinv T rc = MaxContactReduction.asMarkedSeq T d := by
  have key : MaxContactReduction.reduceOrderOfValid hinv T rc hv = MaxContactReduction.asMarkedSeq T d := by
    show (match MaxContactReduction.descendStrictPullback (MaxContactReduction.dropTrivialBoundary T)
            (coverTriple (MaxContactReduction.dropTrivialBoundary T) htrim)
            (coverMap (MaxContactReduction.dropTrivialBoundary T) htrim)
            (coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) htrim hinv rc) with
          | some e => MaxContactReduction.asMarkedSeq T e
          | none => MaxContactReduction.emptyMarkedSeq T) = MaxContactReduction.asMarkedSeq T d
    rw [hd]
  unfold MaxContactReduction.reduceOrder
  rw [dif_pos hv, if_neg hne, key]

theorem reduceOrder_eq_toMarkedSequence (hm : d.IsMarked T.structMap T.ideal T.mult T.boundary) :
    MaxContactReduction.reduceOrder hinv T rc =
      (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hm).toMarkedSequenceOfBlowups := by
  rw [reduceOrder_eq_asMarkedSeq hinv T rc hv hne htrim d hd, asMarkedSeq_eq_toMarkedSequence_of_isMarked T d hm]


end

@[simp] theorem emptyMarkedSeq_length (T : MarkedIdealWithBoundary.{u}) :
    (MaxContactReduction.emptyMarkedSeq T).length = 0 :=
  emptyMarkedBlowupSequenceData_toMarkedSequence_length T.structMap T.ideal T.mult T.boundary

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

theorem asMarkedData_eq_some_of_isMarked (s : MarkedBlowupSequenceData p I m E) (d : BlowupSequenceData (s.obj s.length))
    (h : d.IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length)) :
    MaxContactReduction.asMarkedData s d =
      some (d.toMarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) h) :=
  dif_pos h

theorem concatOfIsMarked_eq_append_of_isMarked (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (d : BlowupSequenceData (s.obj s.length))
    (h : d.IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length)) :
    MaxContactReduction.concatOfIsMarked hinv s d =
      s.append (d.toMarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m
        (s.boundary s.length) h) hinv := by
  have hr := asMarkedData_eq_some_of_isMarked s d h
  show (match MaxContactReduction.asMarkedData s d with
        | some t => s.append t hinv
        | none => s) = _
  rw [hr]

end

noncomputable def derivedTriple (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) : MarkedIdealWithBoundary.{u} :=
  MaxContactReduction.tunedTriple S s hft extra keep

section
variable (S : MarkedIdealWithBoundary.{u}) (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap)) (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)

@[simp] theorem derivedTriple_scheme :
    (derivedTriple S s hft extra keep).scheme = s.obj s.length := rfl

@[simp] theorem derivedTriple_mult :
    (derivedTriple S s hft extra keep).mult = tuningExponent S.mult := rfl

@[simp] theorem derivedTriple_boundary :
    (derivedTriple S s hft extra keep).boundary = extra ++ (s.boundary s.length).drop keep := rfl

theorem derivedTriple_structureMorphism :
    (derivedTriple S s hft extra keep).structMap = s.proj s.length ≫ S.structMap := rfl


end

section
variable (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary.{u})

theorem appendLowerDimReduction_eq_concatOfIsMarked (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) (n : ℕ)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hdim : (derivedTriple S s hft extra keep).krullDimSucc ≤ T.krullDimSucc) :
    MaxContactReduction.appendLowerDimReduction hinv T rc S s extra keep n =
      MaxContactReduction.concatOfIsMarked hinv s
        (BlowupSequenceData.ofSequenceOfBlowups (rc (derivedTriple S s hft extra keep) hdim n).toSequenceOfBlowups) := by
  unfold MaxContactReduction.appendLowerDimReduction
  rw [dif_pos hft]
  exact dif_pos hdim

theorem appendLowerDimReduction_of_not_locallyOfFiniteType (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) (n : ℕ)
    (hft : ¬ LocallyOfFiniteType (s.proj s.length ≫ S.structMap)) :
    MaxContactReduction.appendLowerDimReduction hinv T rc S s extra keep n = s := by
  unfold MaxContactReduction.appendLowerDimReduction
  exact dif_neg hft

@[simp] theorem separateBoundary_zero :
    MaxContactReduction.separateBoundary hinv T rc S 0 =
      emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary := rfl

theorem separateBoundary_succ (j : ℕ) :
    MaxContactReduction.separateBoundary hinv T rc S (j + 1) =
      MaxContactReduction.appendLowerDimReduction hinv T rc S (MaxContactReduction.separateBoundary hinv T rc S j) [] 0 j := rfl

theorem reduceAlongHypersurface_eq_appendLowerDimReduction (H : S.scheme.IdealSheafData) :
    MaxContactReduction.reduceAlongHypersurface hinv T rc S H =
      MaxContactReduction.appendLowerDimReduction hinv T rc S
        (MaxContactReduction.separateBoundary hinv T rc S S.boundary.length)
        [MaxContactReduction.strictTransformAtLength (MaxContactReduction.separateBoundary hinv T rc S S.boundary.length) H]
        S.boundary.length 0 := rfl


end

end MaxContactCoverData

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.WeakTransform
section


section

def MaxContactIdealComapLeControlled : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X X₁ : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
      [LocallyOfFiniteType p]
      (π : X₁ ⟶ X) (Z : X.IdealSheafData) (E : List X.IdealSheafData),
      HasStrictNormalCrossingsWith p Z E → Blowup.IsBlowupAlongIdealSheaf π Z →
      ∀ [IsLocallyNoetherian X₁] [Smooth (π ≫ p)]
        [LocallyOfFiniteType (π ≫ p)]
        (A : X.IdealSheafData) (μ : ℕ), 1 ≤ μ → A ≤ Z ^ μ →
      ∀ A₁ : X₁.IdealSheafData,
        Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π →
        (maxContactIdeal k p A μ).comap π ≤
          Blowup.exceptionalIdeal π Z * maxContactIdeal k (π ≫ p) A₁ μ

theorem smooth_projectionToBase_comp {k : Type u} [Field k] {V : Scheme.{u}}
    {q : V ⟶ Spec (CommRingCat.of k)} [Smooth q] {A : V.IdealSheafData}
    {μ : ℕ} {E : List V.IdealSheafData} (u : MarkedSequenceOfBlowups q A μ E) (i : ℕ)
    (hi : i ≤ u.length) : Smooth (u.projectionToBase i ≫ q) := by
  revert hi
  induction i with
  | zero =>
    intro _
    have h0 : u.projectionToBase 0 ≫ q = u.isoZero.hom ≫ q := by
      rw [SequenceOfBlowups.projectionToBase_zero]
    rw [h0]
    infer_instance
  | succ j ih =>
    intro hj1
    have hj : j < u.length := hj1
    have := ih hj.le
    have hsucc : u.projectionToBase (j + 1) ≫ q = u.transitionMapSucc j ≫ (u.projectionToBase j ≫ q) := by
      rw [SequenceOfBlowups.projectionToBase_succ, Category.assoc]
    rw [hsucc]
    exact smooth_comp_of_isBlowupAlongIdealSheaf (u.center_snc j hj) (u.isBlowupAlongIdealSheaf_blowupMorphism j hj)

private theorem le_pow_one_of_le_consolidated297 {X : Scheme.{u}} {b Z : X.IdealSheafData} (h : b ≤ Z) :
    b ≤ Z ^ 1 := by
  rw [pow_one]; exact h

private theorem maxContactIdeal_congr_consolidated297 {k : Type u} [Field k] {X : Scheme.{u}}
    (p p' : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [LocallyOfFiniteType p']
    (hp : p = p') (I J : X.IdealSheafData) (hI : I = J) (m : ℕ) :
    maxContactIdeal k p I m = maxContactIdeal k p' J m := by
  subst hp
  subst hI
  rfl

namespace MarkedSequenceOfBlowups

def weakTransform {k : Type u} [Field k] {V : Scheme.{u}}
    {q : V ⟶ Spec (CommRingCat.of k)} {A : V.IdealSheafData} {μ : ℕ}
    {E : List V.IdealSheafData} (u : MarkedSequenceOfBlowups q A μ E)
    (hN : ∀ j : ℕ, j ≤ u.length → IsLocallyNoetherian (u.schemeAt j))
    (i : ℕ) (hi : i < u.length) (b : (u.schemeAt i).IdealSheafData) (hb : b ≤ u.center i) :
    (u.schemeAt (i + 1)).IdealSheafData :=
  haveI : IsLocallyNoetherian (u.schemeAt (i + 1)) := hN (i + 1) hi
  controlledTransform (u.transitionMapSucc i) (u.center i) b 1 (u.isBlowupAlongIdealSheaf_blowupMorphism i hi)
    (le_pow_one_of_le_consolidated297 hb)

section
variable {k : Type u} [Field k] {V : Scheme.{u}} {q : V ⟶ Spec (CommRingCat.of k)} {A : V.IdealSheafData} {μ : ℕ} {E : List V.IdealSheafData} (u : MarkedSequenceOfBlowups q A μ E) (hN : ∀ j : ℕ, j ≤ u.length → IsLocallyNoetherian (u.schemeAt j)) (i : ℕ) (hi : i < u.length) (b : (u.schemeAt i).IdealSheafData) (hb : b ≤ u.center i)

theorem exceptionalIdeal_mul_weakTransform :
    Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i) * u.weakTransform hN i hi b hb =
      b.comap (u.transitionMapSucc i) := by
  have : IsLocallyNoetherian (u.schemeAt (i + 1)) := hN (i + 1) hi
  have h := exceptionalIdeal_pow_mul_controlledTransform (u.transitionMapSucc i) (u.center i) b 1
    (u.isBlowupAlongIdealSheaf_blowupMorphism i hi) (le_pow_one_of_le_consolidated297 hb)
  rw [pow_one] at h
  exact h

theorem weakTransform_unique (c : (u.schemeAt (i + 1)).IdealSheafData)
    (hc : Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i) * c = b.comap (u.transitionMapSucc i)) :
    c = u.weakTransform hN i hi b hb := by
  have : IsLocallyNoetherian (u.schemeAt (i + 1)) := hN (i + 1) hi
  have h : Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i) ^ 1 * c = b.comap (u.transitionMapSucc i) := by
    rw [pow_one]; exact hc
  exact eq_controlledTransform_of_mul_eq_comap (u.transitionMapSucc i) (u.center i) b 1 (u.isBlowupAlongIdealSheaf_blowupMorphism i hi)
    (le_pow_one_of_le_consolidated297 hb) c h


end

theorem weakTransform_le_maxContactIdeal {k : Type u} [Field k] [CharZero k]
    {V : Scheme.{u}} {q : V ⟶ Spec (CommRingCat.of k)} {A : V.IdealSheafData} {μ : ℕ}
    {E : List V.IdealSheafData} (hstep : MaxContactIdealComapLeControlled.{u})
    (u : MarkedSequenceOfBlowups q A μ E) (hμ : 1 ≤ μ)
    (hN : ∀ j : ℕ, j ≤ u.length → IsLocallyNoetherian (u.schemeAt j))
    (i : ℕ) (hi : i < u.length)
    [Smooth (u.projectionToBase i ≫ q)]
    [LocallyOfFiniteType (u.projectionToBase i ≫ q)]
    [Smooth (u.projectionToBase (i + 1) ≫ q)]
    [LocallyOfFiniteType (u.projectionToBase (i + 1) ≫ q)]
    (b : (u.schemeAt i).IdealSheafData) (hb : b ≤ u.center i)
    (hbm : b ≤ maxContactIdeal k (u.projectionToBase i ≫ q) (u.ideal i) μ) :
    u.weakTransform hN i hi b hb ≤
      maxContactIdeal k (u.projectionToBase (i + 1) ≫ q) (u.ideal (i + 1)) μ := by
  have : IsLocallyNoetherian (u.schemeAt (i + 1)) := hN (i + 1) hi
  have hassoc : u.transitionMapSucc i ≫ (u.projectionToBase i ≫ q) = u.projectionToBase (i + 1) ≫ q := by
    rw [← Category.assoc, ← SequenceOfBlowups.projectionToBase_succ]
  have : Smooth (u.transitionMapSucc i ≫ (u.projectionToBase i ≫ q)) := by
    rw [hassoc]; infer_instance
  have : LocallyOfFiniteType (u.transitionMapSucc i ≫ (u.projectionToBase i ≫ q)) := by
    rw [hassoc]; infer_instance
  have hAle : u.ideal i ≤ u.center i ^ μ :=
    le_pow_of_hasStrictNormalCrossingsWith (u.projectionToBase i ≫ q) (u.center i) (u.ideal i) (u.boundary i)
      (u.center_snc i hi) μ (u.center_order i hi)
  have hstep' := hstep k (u.schemeAt i) (u.schemeAt (i + 1)) (u.projectionToBase i ≫ q) (u.transitionMapSucc i)
    (u.center i) (u.boundary i) (u.center_snc i hi) (u.isBlowupAlongIdealSheaf_blowupMorphism i hi)
    (u.ideal i) μ hμ hAle (u.ideal (i + 1)) (u.ideal_succ i hi)
  have hM : maxContactIdeal k (u.transitionMapSucc i ≫ (u.projectionToBase i ≫ q)) (u.ideal (i + 1)) μ =
      maxContactIdeal k (u.projectionToBase (i + 1) ≫ q) (u.ideal (i + 1)) μ :=
    maxContactIdeal_congr_consolidated297 _ _ hassoc _ _ rfl μ
  rw [hM] at hstep'
  have h1 : Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i) * u.weakTransform hN i hi b hb =
      b.comap (u.transitionMapSucc i) := exceptionalIdeal_mul_weakTransform u hN i hi b hb
  have hF : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i)) :=
    ((isSmoothDivisor_iff (u.transitionMapSucc i ≫ (u.projectionToBase i ≫ q)) _).1
      (isSmoothDivisor_exceptionalIdeal (u.center_snc i hi) (u.isBlowupAlongIdealSheaf_blowupMorphism i hi))).1
  refine hF.le_of_mul_le_mul ?_
  rw [h1]
  exact le_trans (Scheme.IdealSheafData.comap_mono (u.transitionMapSucc i) hbm) hstep'

end MarkedSequenceOfBlowups

private def strictTransformMaxContactIdeal_consolidated297 {k : Type u} [Field k] {V : Scheme.{u}}
    {q : V ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType q]
    {A' : V.IdealSheafData} {μ : ℕ} {E' : List V.IdealSheafData}
    (u : MarkedSequenceOfBlowups q A' μ E')
    (hN : ∀ i : ℕ, i ≤ u.length → IsLocallyNoetherian (u.schemeAt i)) :
    ∀ i : ℕ, (u.schemeAt i).IdealSheafData := fun i =>
  Nat.rec (motive := fun j => (u.schemeAt j).IdealSheafData)
    ((maxContactIdeal k q A' μ).comap u.isoZero.hom)
    (fun j cj =>
      if h : j + 1 ≤ u.length then
        @idealSheafColon (u.schemeAt (j + 1)) (hN (j + 1) h) (cj.comap (u.transitionMapSucc j))
          (Blowup.exceptionalIdeal (u.transitionMapSucc j) (u.center j))
      else ⊤) i

private theorem strictTransformMaxContactIdeal_succ_consolidated297 {k : Type u} [Field k] {V : Scheme.{u}}
    {q : V ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType q]
    {A' : V.IdealSheafData} {μ : ℕ} {E' : List V.IdealSheafData}
    (u : MarkedSequenceOfBlowups q A' μ E')
    (hN : ∀ i : ℕ, i ≤ u.length → IsLocallyNoetherian (u.schemeAt i)) (i : ℕ) :
    strictTransformMaxContactIdeal_consolidated297 u hN (i + 1) =
      if h : i + 1 ≤ u.length then
        @idealSheafColon (u.schemeAt (i + 1)) (hN (i + 1) h)
          ((strictTransformMaxContactIdeal_consolidated297 u hN i).comap (u.transitionMapSucc i))
          (Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i))
      else ⊤ := rfl

private def maxContactIdealAt_consolidated297 {k : Type u} [Field k] {V : Scheme.{u}}
    {q : V ⟶ Spec (CommRingCat.of k)} [Smooth q]
    {A' : V.IdealSheafData} {μ : ℕ} {E' : List V.IdealSheafData}
    (u : MarkedSequenceOfBlowups q A' μ E') (i : ℕ) (hi : i ≤ u.length) : (u.schemeAt i).IdealSheafData :=
  haveI := smooth_projectionToBase_comp u i hi
  maxContactIdeal k (u.projectionToBase i ≫ q) (u.ideal i) μ

theorem existsMaxContactControlledTransforms_of_comapLeControlled (h : MaxContactIdealComapLeControlled.{u}) :
    ExistsMaxContactControlledTransforms.{u} := by
  intro k _ _ V q _ _ A' μ hμ E' u hN hcen
  have sm : ∀ i : ℕ, i ≤ u.length → Smooth (u.projectionToBase i ≫ q) :=
    fun i hi => smooth_projectionToBase_comp u i hi
  have hcart : ∀ i : ℕ, i < u.length →
      Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i)) := by
    intro i hi
    have := sm i hi.le
    exact ((isSmoothDivisor_iff (u.transitionMapSucc i ≫ (u.projectionToBase i ≫ q)) _).1
      (isSmoothDivisor_exceptionalIdeal (u.center_snc i hi) (u.isBlowupAlongIdealSheaf_blowupMorphism i hi))).1
  have hcen' : ∀ i : ℕ, (hi : i < u.length) →
      strictTransformMaxContactIdeal_consolidated297 u hN i ≤ maxContactIdealAt_consolidated297 u i hi.le → strictTransformMaxContactIdeal_consolidated297 u hN i ≤ u.center i := by
    intro i hi hM
    have := sm i hi.le
    refine hcen i hi (strictTransformMaxContactIdeal_consolidated297 u hN i) ?_
    have h1 : (((u.center i).support : Set ↥(u.schemeAt i))) ⊆ orderAtLeastLocus (u.ideal i) μ :=
      u.center_order i hi
    have h2 : (((maxContactIdealAt_consolidated297 u i hi.le).support : Set ↥(u.schemeAt i))) = orderAtLeastLocus (u.ideal i) μ := by
      show (((maxContactIdeal k (u.projectionToBase i ≫ q) (u.ideal i) μ).support :
        Set ↥(u.schemeAt i))) = _
      rw [maxContactIdeal_eq_derivIdealSheafIterate]
      exact support_derivIdealSheafIterate_eq_orderAtLeastLocus k (u.projectionToBase i ≫ q) (u.ideal i) hμ
    have h3 : (((maxContactIdealAt_consolidated297 u i hi.le).support : Set ↥(u.schemeAt i))) ⊆
        (((strictTransformMaxContactIdeal_consolidated297 u hN i).support : Set ↥(u.schemeAt i))) := by
      exact_mod_cast Scheme.IdealSheafData.support_antitone hM
    rw [h2] at h3
    exact fun x hx => h3 (h1 hx)
  have heq' : ∀ i : ℕ, i < u.length → strictTransformMaxContactIdeal_consolidated297 u hN i ≤ u.center i →
      Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i) * strictTransformMaxContactIdeal_consolidated297 u hN (i + 1) =
        (strictTransformMaxContactIdeal_consolidated297 u hN i).comap (u.transitionMapSucc i) := by
    intro i hi hb
    have hi' : i + 1 ≤ u.length := hi
    have : IsLocallyNoetherian (u.schemeAt (i + 1)) := hN (i + 1) hi'
    have hI : (strictTransformMaxContactIdeal_consolidated297 u hN i).comap (u.transitionMapSucc i) ≤
        Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i) ^ 1 :=
      comap_le_exceptionalIdeal_pow (u.transitionMapSucc i) (le_pow_one_of_le_consolidated297 hb)
    rw [pow_one] at hI
    have hc : strictTransformMaxContactIdeal_consolidated297 u hN (i + 1) =
        @idealSheafColon (u.schemeAt (i + 1)) (hN (i + 1) hi')
          ((strictTransformMaxContactIdeal_consolidated297 u hN i).comap (u.transitionMapSucc i))
          (Blowup.exceptionalIdeal (u.transitionMapSucc i) (u.center i)) := by
      rw [strictTransformMaxContactIdeal_succ_consolidated297, dif_pos hi']
    rw [hc]
    exact (hcart i hi).mul_idealSheafColon hI
  have main : ∀ i : ℕ, (hi : i ≤ u.length) → strictTransformMaxContactIdeal_consolidated297 u hN i ≤ maxContactIdealAt_consolidated297 u i hi := by
    intro i
    induction i with
    | zero =>
      intro hi
      have := sm 0 hi
      have : Smooth u.isoZero.hom := inferInstance
      have : Smooth (u.isoZero.hom ≫ q) := inferInstance
      show strictTransformMaxContactIdeal_consolidated297 u hN 0 ≤ maxContactIdeal k (u.projectionToBase 0 ≫ q) (u.ideal 0) μ
      have e1 : maxContactIdeal k (u.projectionToBase 0 ≫ q) (u.ideal 0) μ =
          maxContactIdeal k (u.isoZero.hom ≫ q) (A'.comap u.isoZero.hom) μ :=
        maxContactIdeal_congr_consolidated297 _ _ (by rw [SequenceOfBlowups.projectionToBase_zero]) _ _ u.ideal_zero μ
      have e2 : maxContactIdeal k (u.isoZero.hom ≫ q) (A'.comap u.isoZero.hom) μ =
          (maxContactIdeal k q A' μ).comap u.isoZero.hom := by
        simp only [maxContactIdeal_eq_derivIdealSheafIterate]
        exact derivIdealSheafIterate_comap k q u.isoZero.hom (μ - 1) A'
      rw [e1, e2]
      exact le_rfl
    | succ j ih =>
      intro hj1
      have hj : j < u.length := hj1
      have ihj := ih hj.le
      have hb := hcen' j hj ihj
      have hw : strictTransformMaxContactIdeal_consolidated297 u hN (j + 1) = u.weakTransform hN j hj (strictTransformMaxContactIdeal_consolidated297 u hN j) hb :=
        MarkedSequenceOfBlowups.weakTransform_unique u hN j hj (strictTransformMaxContactIdeal_consolidated297 u hN j) hb
          (strictTransformMaxContactIdeal_consolidated297 u hN (j + 1)) (heq' j hj hb)
      have := sm j hj.le
      have := sm (j + 1) hj1
      rw [hw]
      exact MarkedSequenceOfBlowups.weakTransform_le_maxContactIdeal h u hμ hN j hj
        (strictTransformMaxContactIdeal_consolidated297 u hN j) hb ihj
  exact ⟨strictTransformMaxContactIdeal_consolidated297 u hN, rfl, fun i hi => heq' i hi (hcen' i hi (main i hi.le)),
    fun i hi => hcen' i hi (main i hi.le)⟩


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverMapSurjective
section



namespace MaxContactCoverData

theorem surjective_coverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (h : ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T,
      MaxContactReduction.IsMaxContactCover T D hv.locallyOfFiniteType (balancedTunedIdeal T hv) (tunedMult T)) :
    Surjective (coverMap T hv) := by
  have hc := (isMaxContactCover_chosenCoverData T hv h).covers
  rw [coverMap_eq_sigmaOpensDesc]
  exact surjective_sigmaOpensDesc T.scheme (chosenCoverData T hv).opens hc

end MaxContactCoverData

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
section

open CategoryTheory.Limits


namespace MaxContactFunctoriality

@[reducible] def lowerDimensionalFamily (A : ℕ → PrincipalizationAssignment.{u}) (T : MarkedIdealWithBoundary.{u}) :
    ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups :=
  fun S _ j => A j S

noncomputable def maxContactPrincipalization (hinv : ComapIsoInvariance.{u}) (A : ℕ → PrincipalizationAssignment.{u}) :
    PrincipalizationAssignment.{u} :=
  fun T => MaxContactReduction.reduceOrder hinv T (lowerDimensionalFamily A T)

@[simp] theorem maxContactPrincipalization_apply (hinv : ComapIsoInvariance.{u}) (A : ℕ → PrincipalizationAssignment.{u})
    (T : MarkedIdealWithBoundary.{u}) :
    maxContactPrincipalization hinv A T = MaxContactReduction.reduceOrder hinv T (lowerDimensionalFamily A T) := rfl

structure OrderReductionHypotheses (P : ℕ → Prop) (T : MarkedIdealWithBoundary.{u}) : Prop where
  dim_prop : P T.krullDimSucc
  orderLE : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)
  coSupport_nonempty : (orderAtLeastLocus T.ideal T.mult).Nonempty
  valid : T.IsAdmissible

theorem OrderReductionHypotheses.orderAtLeastLocus_ne_empty {P : ℕ → Prop} {T : MarkedIdealWithBoundary.{u}} (h : OrderReductionHypotheses P T) :
    orderAtLeastLocus T.ideal T.mult ≠ ∅ :=
  h.coSupport_nonempty.ne_empty

def IsLocalIsomorphism {W' W : Scheme.{u}} (g : W' ⟶ W) : Prop :=
  ∀ x : ↥W', ∃ U : W'.Opens, x ∈ U ∧ IsOpenImmersion (U.ι ≫ g)

noncomputable abbrev coverBlowupSequence (hinv : ComapIsoInvariance.{u}) (A : ℕ → PrincipalizationAssignment.{u})
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    MarkedBlowupSequenceData (MaxContactCoverData.coverTriple T hv).structMap
      (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.coverTriple T hv).mult
      (MaxContactCoverData.coverTriple T hv).boundary :=
  MaxContactCoverData.coverMarkedBlowupData T hv hinv (lowerDimensionalFamily A T)

structure CoverSequenceProperties (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment.{u}) : Prop where
  center_ne_top : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T),
    ∀ i < (coverBlowupSequence hinv A T h.valid).length,
      (coverBlowupSequence hinv A T h.valid).center i ≠ ⊤
  cert : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T), T.mult = 1 →
    ∀ i < (coverBlowupSequence hinv A T h.valid).length,
      OrderCertificate ((coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.schemeAt i)
        ((coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.projectionToBase i ≫
          (MaxContactCoverData.coverTriple T h.valid).structMap)
        ((coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.ideal i) 1
        ((coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.boundaryLocus i)
        ((coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.center i)
  descends : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T),
    ∃ d : BlowupSequenceData T.scheme,
      IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
        (coverBlowupSequence hinv A T h.valid).toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups
  hypersurface : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T), T.boundary = [] → T.mult = 1 →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (e : Y ⟶ T.scheme)
      [IsClosedImmersion e], e ≫ T.structMap = q →
      IsSmoothDivisor T.structMap (Scheme.Hom.ker e) →
    ∀ J : Y.IdealSheafData,
      (T.withSchemeIdealBoundary Y q J ([] : List Y.IdealSheafData)).IsAdmissible →
      T.ideal = imageIdealSheaf e J →
      IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
        (coverBlowupSequence hinv A T h.valid).toBlowupSequenceData.toSequenceOfBlowups
        (A 0 (T.withBoundary [Scheme.Hom.ker e])).toSequenceOfBlowups
  resolves : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T),
    orderAtLeastLocus ((coverBlowupSequence hinv A T h.valid).ideal (coverBlowupSequence hinv A T h.valid).length)
      (MaxContactCoverData.tunedMult T) = ∅

structure DescentHypotheses (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u}) : Prop where
  tuning : IsMarkedIffBalancedTunedSheaf.{u}
  cert_descend : ∀ (k : Type u) [Field k] (W' W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (g : W' ⟶ W),
      IsLocalIsomorphism g → AlgebraicGeometry.Surjective g →
    ∀ (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W) (Z : W.IdealSheafData),
      OrderCertificate W' (g ≫ p) (N.comap g) μ (g.base ⁻¹' Mem) (Z.comap g) →
      OrderCertificate W p N μ Mem Z
  base_change : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.baseChange L f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
      ((T.baseChange L f).withBoundary E').IsAdmissible →
      P ((T.baseChange L f).withBoundary E').krullDimSucc →
      (∀ x : ↥((T.baseChange L f).withBoundary E').scheme,
        orderAt ((T.baseChange L f).withBoundary E').ideal x ≤ (T.mult : ℕ∞)) →
      IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (maxContactPrincipalization hinv A ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups
        (maxContactPrincipalization hinv A T).toSequenceOfBlowups
  base_change_strict : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.baseChange L f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
      ((T.baseChange L f).withBoundary E').IsAdmissible →
      P ((T.baseChange L f).withBoundary E').krullDimSucc →
      (∀ x : ↥((T.baseChange L f).withBoundary E').scheme,
        orderAt ((T.baseChange L f).withBoundary E').ideal x ≤ (T.mult : ℕ∞)) →
      IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (maxContactPrincipalization hinv A ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups
        (maxContactPrincipalization hinv A T).toSequenceOfBlowups
  comp_openImmersion : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T) (d : BlowupSequenceData T.scheme)
      (D : StrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
        (coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
      (i : ℕ) (hi : i ≤ (coverBlowupSequence hinv A T h.valid).length),
      IsLocalIsomorphism
        (D.comp i ((coverBlowupSequence hinv A T h.valid).le_toSequenceOfBlowups_length hi))
  locallyNoetherian : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T) (d : BlowupSequenceData T.scheme),
      IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
        (coverBlowupSequence hinv A T h.valid).toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups →
      (∀ i ≤ d.length, IsLocallyNoetherian (d.obj i)) ∧
      (∀ i ≤ (coverBlowupSequence hinv A T h.valid).length,
        IsLocallyNoetherian ((coverBlowupSequence hinv A T h.valid).obj i))
  isMarked : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T) (d : BlowupSequenceData T.scheme),
      IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
        (coverBlowupSequence hinv A T h.valid).toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups →
      d.IsMarked T.structMap (MaxContactCoverData.balancedTunedIdeal T h.valid)
        (MaxContactCoverData.tunedMult T) T.boundary
  isMarked_of_trim : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (d : BlowupSequenceData T.scheme) (I : T.scheme.IdealSheafData) (m : ℕ),
      d.IsMarked T.structMap I m (MaxContactReduction.dropTrivialBoundary T).boundary →
      d.IsMarked T.structMap I m T.boundary
  order_le : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
    ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.length →
      ∀ x : ↥(s.toSequenceOfBlowups.schemeAt i), orderAt (s.ideal i) x ≤ (T.mult : ℕ∞)
  smooth_pullback : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (g : Y ⟶ T.scheme)
      [Smooth g], g ≫ T.structMap = q →
    ∀ E' : List Y.IdealSheafData,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q g).boundary E' →
      ((T.pullbackAlong Y q g).withBoundary E').IsAdmissible →
      P ((T.pullbackAlong Y q g).withBoundary E').krullDimSucc →
      (∀ x : ↥((T.pullbackAlong Y q g).withBoundary E').scheme,
        orderAt ((T.pullbackAlong Y q g).withBoundary E').ideal x ≤ (T.mult : ℕ∞)) →
      IsPullbackBlowupSequence g
        (maxContactPrincipalization hinv A ((T.pullbackAlong Y q g).withBoundary E')).toSequenceOfBlowups
        (maxContactPrincipalization hinv A T).toSequenceOfBlowups
  smooth_pullback_strict : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (g : Y ⟶ T.scheme)
      [Smooth g] [AlgebraicGeometry.Surjective g], g ≫ T.structMap = q →
    ∀ E' : List Y.IdealSheafData,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q g).boundary E' →
      ((T.pullbackAlong Y q g).withBoundary E').IsAdmissible →
      P ((T.pullbackAlong Y q g).withBoundary E').krullDimSucc →
      (∀ x : ↥((T.pullbackAlong Y q g).withBoundary E').scheme,
        orderAt ((T.pullbackAlong Y q g).withBoundary E').ideal x ≤ (T.mult : ℕ∞)) →
      IsStrictPullbackBlowupSeq g
        (maxContactPrincipalization hinv A ((T.pullbackAlong Y q g).withBoundary E')).toSequenceOfBlowups
        (maxContactPrincipalization hinv A T).toSequenceOfBlowups
  flat_coverMap : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T),
      Flat (MaxContactCoverData.coverMap T h.valid)
  surjective_coverMap : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T),
      AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap T h.valid)
  valid_subst_ker : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (e : Y ⟶ T.scheme)
      [IsClosedImmersion e], e ≫ T.structMap = q →
    ∀ J : Y.IdealSheafData, (T.withSchemeIdealBoundary Y q J ([] : List Y.IdealSheafData)).IsAdmissible →
    ∀ (ε : Y ⟶ (Scheme.Hom.ker e).subscheme),
      ε ≫ (Scheme.Hom.ker e).subschemeι = e →
      (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
          ((Scheme.Hom.ker e).subschemeι ≫ T.structMap) (imageIdealSheaf ε J)
          ([] : List (Scheme.Hom.ker e).subscheme.IdealSheafData)).IsAdmissible ∧
      (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
          ((Scheme.Hom.ker e).subschemeι ≫ T.structMap) (imageIdealSheaf ε J)
          ([] : List (Scheme.Hom.ker e).subscheme.IdealSheafData)).krullDimSucc =
        (T.withSchemeIdealBoundary Y q J ([] : List Y.IdealSheafData)).krullDimSucc
  tunedIdeal_of_mult_one : ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible), T.mult = 1 →
      MaxContactCoverData.balancedTunedIdeal T hv = T.ideal
  valid_trim : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → (MaxContactReduction.dropTrivialBoundary T).IsAdmissible
  valid_withDivisor : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → T.boundary = [] →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (e : Y ⟶ T.scheme)
      [IsClosedImmersion e], e ≫ T.structMap = q →
      IsSmoothDivisor T.structMap (Scheme.Hom.ker e) →
      (T.withBoundary [Scheme.Hom.ker e]).IsAdmissible

end MaxContactFunctoriality

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.DisjointUnionCover
section

open CategoryTheory.Limits

section

namespace MaxContactReduction

namespace FiniteOpenCoverWithIdeals

variable {T : MarkedIdealWithBoundary.{u}}

abbrev piece (D : FiniteOpenCoverWithIdeals T) (i : D.idx) : Scheme.{u} := (D.opens i).toScheme

abbrev summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) : D.piece i ⟶ D.disjointUnion :=
  Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i

theorem isOpenImmersion_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    IsOpenImmersion (D.summandι i) := by
  show IsOpenImmersion (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i)
  infer_instance

instance instIsOpenImmersionSummandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    IsOpenImmersion (D.summandι i) :=
  isOpenImmersion_summandι D i

theorem isClosedImmersion_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    IsClosedImmersion (D.summandι i) := by
  show IsClosedImmersion (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i)
  infer_instance

instance instIsClosedImmersionSummandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    IsClosedImmersion (D.summandι i) :=
  isClosedImmersion_summandι D i

theorem quasiCompact_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    QuasiCompact (D.summandι i) := by
  show QuasiCompact (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i)
  infer_instance

instance instQuasiCompactSummandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    QuasiCompact (D.summandι i) :=
  quasiCompact_summandι D i

section
variable (D : FiniteOpenCoverWithIdeals T) (i : D.idx)

theorem summandι_comp_disjointUnionMap :
    D.summandι i ≫ D.disjointUnionMap = (D.opens i).ι :=
  sigma_ι_sigmaOpensDesc T.scheme D.opens i

theorem disjointUnionMap_summandι_mem (y : D.piece i) :
    D.disjointUnionMap.base ((D.summandι i).base y) ∈ D.opens i := by
  have hmem : D.disjointUnionMap.base ((D.summandι i).base y) ∈ Set.range (D.opens i).ι.base := by
    rw [← summandι_comp_disjointUnionMap D i]
    exact ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι] at hmem
  exact hmem

private theorem comap_imageIdealSheaf_summandι_consolidated349 :
    (imageIdealSheaf (D.summandι i) (D.localIdeal i)).comap (D.summandι i) = D.localIdeal i :=
  FunctorialResolution.EmbeddedResolution.comap_ker_subschemeι_comp (D.localIdeal i) (D.summandι i)


end

private theorem imageIdealSheaf_eq_ker_consolidated349 {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (I : X.IdealSheafData) : imageIdealSheaf f I = Scheme.Hom.ker (I.subschemeι ≫ f) := rfl

private theorem subsingleton_sections_bot_consolidated349 (Z : Scheme.{u}) :
    Subsingleton ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens))) := by
  have ht : CategoryTheory.Limits.IsTerminal (Z.presheaf.obj (Opposite.op (⊥ : Z.Opens))) :=
    TopCat.Sheaf.isTerminalOfEmpty Z.sheaf
  refine ⟨fun a b => ?_⟩
  have h := ht.hom_ext
    (CommRingCat.ofHom (RingHom.fst ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens)))
      ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens)))))
    (CommRingCat.ofHom (RingHom.snd ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens)))
      ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens)))))
  exact congrArg (fun m => (CommRingCat.Hom.hom m) (a, b)) h

private theorem ideal_ker_eq_top_of_disjoint_consolidated349 {Y Z : Scheme.{u}} (g : Z ⟶ Y) [QuasiCompact g]
    (U : Y.affineOpens) (hdisj : ∀ z : ↥Z, g.base z ∉ (U.1 : Set ↥Y)) :
    (Scheme.Hom.ker g).ideal U = ⊤ := by
  have hempty : g ⁻¹ᵁ U.1 = ⊥ := by
    refine TopologicalSpace.Opens.ext ?_
    rw [TopologicalSpace.Opens.coe_bot]
    exact Set.eq_empty_iff_forall_notMem.mpr fun z hz => hdisj z hz
  have hsub : Subsingleton ↥(Z.presheaf.obj (Opposite.op (g ⁻¹ᵁ U.1))) := by
    rw [hempty]
    exact subsingleton_sections_bot_consolidated349 Z
  rw [Scheme.Hom.ker_apply]
  refine (Ideal.eq_top_iff_one _).mpr ?_
  rw [RingHom.mem_ker, map_one]
  exact Subsingleton.elim _ _

section
variable (D : FiniteOpenCoverWithIdeals T)

private theorem ideal_imageIdealSheaf_eq_top_of_ne_consolidated349 {i j : D.idx} (hij : j ≠ i)
    (W : D.disjointUnion.Opens) (hW : IsAffineOpen W)
    (hsub : ∀ y ∈ (W : Set ↥D.disjointUnion), y ∈ Set.range (D.summandι i).base) :
    (imageIdealSheaf (D.summandι j) (D.localIdeal j)).ideal ⟨W, hW⟩ = ⊤ := by
  rw [imageIdealSheaf_eq_ker_consolidated349]
  refine ideal_ker_eq_top_of_disjoint_consolidated349 ((D.localIdeal j).subschemeι ≫ D.summandι j) ⟨W, hW⟩ ?_
  intro z hz
  obtain ⟨v, hv⟩ := hsub _ hz
  have hcomp : ((D.localIdeal j).subschemeι ≫ D.summandι j).base z
      = (D.summandι j).base ((D.localIdeal j).subschemeι.base z) := rfl
  exact Blowup.sigmaι_base_ne (fun t : D.idx => (D.opens t).toScheme) hij
    ((D.localIdeal j).subschemeι.base z) v (hcomp.symm.trans hv.symm)

theorem comap_iInfImageIdeal_summandι (i : D.idx) :
    D.iInfImageIdeal.comap (D.summandι i) = D.localIdeal i := by
  have hglue : D.iInfImageIdeal
      = ⨅ j : D.idx, imageIdealSheaf (D.summandι j) (D.localIdeal j) := rfl
  refine le_antisymm ?_ ?_
  · rw [hglue]
    exact le_trans (Scheme.IdealSheafData.comap_mono (D.summandι i) (iInf_le _ i))
      (le_of_eq (comap_imageIdealSheaf_summandι_consolidated349 D i))
  · rw [Scheme.IdealSheafData.le_def]
    intro V
    have hW : IsAffineOpen ((D.summandι i) ''ᵁ V.1) :=
      V.2.image_of_isOpenImmersion (D.summandι i)
    have hle : V.1 ≤ (D.summandι i) ⁻¹ᵁ ((D.summandι i) ''ᵁ V.1) := fun x hx => ⟨x, hx, rfl⟩
    have hsub : ∀ y ∈ ((((D.summandι i) ''ᵁ V.1) : D.disjointUnion.Opens) : Set ↥D.disjointUnion),
        y ∈ Set.range (D.summandι i).base := by
      rintro y ⟨v, hv, rfl⟩
      exact ⟨v, rfl⟩
    have h1 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE D.iInfImageIdeal (D.summandι i)
      ⟨_, hW⟩ V hle
    have h2 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE
      (imageIdealSheaf (D.summandι i) (D.localIdeal i)) (D.summandι i) ⟨_, hW⟩ V hle
    have h3 : D.iInfImageIdeal.ideal ⟨_, hW⟩
        = (imageIdealSheaf (D.summandι i) (D.localIdeal i)).ideal ⟨_, hW⟩ := by
      rw [hglue]
      simp only [Scheme.IdealSheafData.ideal_iInf, iInf_apply]
      refine le_antisymm (iInf_le _ i) (le_iInf fun j => ?_)
      by_cases hj : j = i
      · rw [hj]
      · rw [ideal_imageIdealSheaf_eq_top_of_ne_consolidated349 D hj _ hW hsub]
        exact le_top
    have h4 : (D.iInfImageIdeal.comap (D.summandι i)).ideal V = (D.localIdeal i).ideal V := by
      rw [h1, h3, ← h2, comap_imageIdealSheaf_summandι_consolidated349 D i]
    exact le_of_eq h4.symm


end

abbrev summandOpen (D : FiniteOpenCoverWithIdeals T) (i : D.idx) : D.disjointUnion.Opens :=
  (D.summandι i).opensRange

theorem range_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    Set.range (D.summandι i).base = Set.range (D.summandOpen i).ι.base :=
  (Scheme.Opens.range_ι (D.summandOpen i)).symm

abbrev summandIso (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    D.piece i ≅ (D.summandOpen i).toScheme :=
  IsOpenImmersion.isoOfRangeEq (D.summandι i) (D.summandOpen i).ι (range_summandι D i)

theorem summandOpen_ι_comp_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    (D.summandOpen i).ι ≫ D.disjointUnionMap = (D.summandIso i).inv ≫ (D.opens i).ι := by
  have h : (D.summandIso i).inv ≫ D.summandι i = (D.summandOpen i).ι := by
    simp [FiniteOpenCoverWithIdeals.summandIso]
  rw [← h, Category.assoc, summandι_comp_disjointUnionMap]

section
variable (D : FiniteOpenCoverWithIdeals T) (x : ↥D.disjointUnion)

theorem exists_summandι_base_eq :
    ∃ (i : D.idx) (y : D.piece i), (D.summandι i).base y = x := by
  obtain ⟨⟨i, y⟩, hx⟩ := (sigmaMk fun j : D.idx => (D.opens j).toScheme).surjective x
  refine ⟨i, y, ?_⟩
  show (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i).base y = x
  simpa using hx

theorem exists_mem_summandOpen :
    ∃ i : D.idx, x ∈ D.summandOpen i := by
  obtain ⟨i, y, hy⟩ := D.exists_summandι_base_eq x
  refine ⟨i, ?_⟩
  have hmem : x ∈ Set.range (D.summandι i).base := ⟨y, hy⟩
  exact hmem


end

section
variable (D : FiniteOpenCoverWithIdeals T) (i : D.idx)

theorem isAffineOpen_summandOpen (h : IsAffineOpen (D.opens i)) :
    IsAffineOpen (D.summandOpen i) := by
  have hA : IsAffine ((D.opens i).toScheme) := h
  exact isAffineOpen_opensRange (D.summandι i)

theorem restrictIdeal_summandOpen (J : D.disjointUnion.IdealSheafData) :
    restrictIdeal J (D.summandOpen i) = (J.comap (D.summandι i)).comap (D.summandIso i).inv := by
  have h : (D.summandIso i).inv ≫ D.summandι i = (D.summandOpen i).ι := by
    simp [FiniteOpenCoverWithIdeals.summandIso]
  rw [restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp, h]

theorem restrictIdeal_iInfImageIdeal_summandOpen :
    restrictIdeal D.iInfImageIdeal (D.summandOpen i) =
      (D.localIdeal i).comap (D.summandIso i).inv := by
  rw [restrictIdeal_summandOpen D i D.iInfImageIdeal, comap_iInfImageIdeal_summandι D i]





theorem restrictIdeal_comap_disjointUnionMap_summandOpen (J : T.scheme.IdealSheafData) :
    restrictIdeal (J.comap D.disjointUnionMap) (D.summandOpen i) =
      (restrictIdeal J (D.opens i)).comap (D.summandIso i).inv := by
  rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, summandOpen_ι_comp_disjointUnionMap]


end

section
variable (D : FiniteOpenCoverWithIdeals T) (i : D.idx) {n : ℕ} (c : EtaleChart T.structMap (D.opens i) n)

private theorem summandIso_inv_comp_map_comp_affineSpaceFinToSpec_consolidated349 :
    ((D.summandIso i).inv ≫ c.map) ≫ affineSpaceFinToSpec T.base n =
      (D.summandOpen i).ι ≫ (D.disjointUnionMap ≫ T.structMap) := by
  rw [Category.assoc, c.comp_struct, ← Category.assoc, ← summandOpen_ι_comp_disjointUnionMap,
    Category.assoc]

private theorem etale_summandIso_inv_comp_map_consolidated349 :
    Etale ((D.summandIso i).inv ≫ c.map) := by
  have h1 : Etale c.map := c.isEtale
  have h4 : Etale ((D.summandIso i).inv) := inferInstance
  infer_instance


end

def summandEtaleChart (D : FiniteOpenCoverWithIdeals T) (i : D.idx) {n : ℕ}
    (c : EtaleChart T.structMap (D.opens i) n) :
    EtaleChart (D.disjointUnionMap ≫ T.structMap) (D.summandOpen i) n where
  map := (D.summandIso i).inv ≫ c.map
  comp_struct := summandIso_inv_comp_map_comp_affineSpaceFinToSpec_consolidated349 D i c
  isEtale := etale_summandIso_inv_comp_map_consolidated349 D i c

section
variable (D : FiniteOpenCoverWithIdeals T) (i : D.idx) {n : ℕ} (c : EtaleChart T.structMap (D.opens i) n)

theorem summandEtaleChart_map :
    (D.summandEtaleChart i c).map = (D.summandIso i).inv ≫ c.map := rfl

theorem summandEtaleChart_coordIdeal (S : Finset (Fin n)) :
    (D.summandEtaleChart i c).coordIdeal S = (c.coordIdeal S).comap (D.summandIso i).inv := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, summandEtaleChart_map,
    ← Scheme.IdealSheafData.comap_comp]


end

private theorem eq_of_map_eq_of_bijective_consolidated349 {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hinj : Function.Injective φ) (hsurj : Function.Surjective φ)
    {I I' : Ideal A} (h : Ideal.map φ I = Ideal.map φ I') : I = I' := by
  ext x
  constructor
  · intro hx
    have hmem : φ x ∈ Ideal.map φ I' := by
      rw [← h]
      exact Ideal.mem_map_of_mem φ hx
    obtain ⟨a, ha, hax⟩ := (Ideal.mem_map_iff_of_surjective (f := φ) hsurj).mp hmem
    have hax' : a = x := hinj hax
    rw [hax'] at ha
    exact ha
  · intro hx
    have hmem : φ x ∈ Ideal.map φ I := by
      rw [h]
      exact Ideal.mem_map_of_mem φ hx
    obtain ⟨a, ha, hax⟩ := (Ideal.mem_map_iff_of_surjective (f := φ) hsurj).mp hmem
    have hax' : a = x := hinj hax
    rw [hax'] at ha
    exact ha

section
variable {X : Scheme.{u}}

private theorem top_le_preimage_opens_consolidated349 (V : X.Opens) :
    (⊤ : V.toScheme.Opens) ≤ (TopologicalSpace.Opens.map V.ι.base).obj V := by
  intro y _
  exact y.2

private theorem appLE_ι_eq_topIso_inv_consolidated349 (V : X.Opens) :
    V.ι.appLE V ⊤ (top_le_preimage_opens_consolidated349 V) = V.topIso.inv := by
  simp
  rfl

private theorem ideal_eq_of_comap_ι_eq_consolidated349 {I J : X.IdealSheafData}
    (V : X.Opens) (hV : IsAffineOpen V) (h : I.comap V.ι = J.comap V.ι) :
    I.ideal ⟨V, hV⟩ = J.ideal ⟨V, hV⟩ := by
  have : IsAffine V.toScheme := hV
  have key1 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE I V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_preimage_opens_consolidated349 V)
  have key2 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE J V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_preimage_opens_consolidated349 V)
  rw [h] at key1
  have hinj : Function.Injective
      (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_preimage_opens_consolidated349 V))) := by
    rw [appLE_ι_eq_topIso_inv_consolidated349 V]
    exact V.topIso.symm.commRingCatIsoToRingEquiv.injective
  have hsurj : Function.Surjective
      (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_preimage_opens_consolidated349 V))) := by
    rw [appLE_ι_eq_topIso_inv_consolidated349 V]
    exact V.topIso.symm.commRingCatIsoToRingEquiv.surjective
  exact eq_of_map_eq_of_bijective_consolidated349 _ hinj hsurj (key1.symm.trans key2)

private theorem ext_of_comap_ι_eq_of_iSup_eq_top_consolidated349 {ι : Type u} (U : ι → X.Opens)
    (hU : iSup U = ⊤) {I J : X.IdealSheafData}
    (h : ∀ i : ι, I.comap (U i).ι = J.comap (U i).ι) : I = J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := {W : X.affineOpens // ∃ i : ι, (W.1 : X.Opens) ≤ U i})
    (fun W => W.1) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ iSup U := by
      rw [hU]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨V, hV, hxV, hVU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hi
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, i, hVU⟩, hxV⟩
  · rintro ⟨⟨W, hW⟩, i, hWU⟩
    refine ideal_eq_of_comap_ι_eq_consolidated349 W hW ?_
    have e1 : I.comap W.ι = (I.comap (U i).ι).comap (X.homOfLE hWU) := by
      rw [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]
    have e2 : J.comap W.ι = (J.comap (U i).ι).comap (X.homOfLE hWU) := by
      rw [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]
    rw [e1, e2, h i]


end

theorem ext_of_comap_summandι (D : FiniteOpenCoverWithIdeals T) {J J' : D.disjointUnion.IdealSheafData}
    (h : ∀ i : D.idx, J.comap (D.summandι i) = J'.comap (D.summandι i)) : J = J' := by
  refine ext_of_comap_ι_eq_of_iSup_eq_top_consolidated349 (fun i : D.idx => D.summandOpen i) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := D.exists_mem_summandOpen x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    have h1 := restrictIdeal_summandOpen D i J
    have h2 := restrictIdeal_summandOpen D i J'
    rw [h i] at h1
    exact h1.trans h2.symm

private theorem ideal_le_of_map_le_of_bijective_consolidated349 {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hinj : Function.Injective φ) (hsurj : Function.Surjective φ)
    {I I' : Ideal A} (h : Ideal.map φ I ≤ Ideal.map φ I') : I ≤ I' := by
  intro a ha
  have h1 : φ a ∈ Ideal.map φ I' := h (Ideal.mem_map_of_mem φ ha)
  obtain ⟨b, hb, hba⟩ := (Ideal.mem_map_iff_of_surjective (f := φ) hsurj).mp h1
  have hba' : b = a := hinj hba
  rwa [hba'] at hb

section
variable {Y : Scheme.{u}} {J J' : Y.IdealSheafData}

private theorem ideal_le_of_comap_ι_le_consolidated349 (V : Y.Opens) (hV : IsAffineOpen V) (h : J.comap V.ι ≤ J'.comap V.ι) :
    J.ideal ⟨V, hV⟩ ≤ J'.ideal ⟨V, hV⟩ := by
  have : IsAffine V.toScheme := hV
  have k1 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE J V.ι ⟨V, hV⟩
    ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_preimage_opens_consolidated349 V)
  have k2 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE J' V.ι ⟨V, hV⟩
    ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_preimage_opens_consolidated349 V)
  have hle := Scheme.IdealSheafData.le_def.mp h ⟨⊤, isAffineOpen_top V.toScheme⟩
  rw [k1, k2, appLE_ι_eq_topIso_inv_consolidated349 V] at hle
  have hinj : Function.Injective (CommRingCat.Hom.hom V.topIso.inv) :=
    V.topIso.symm.commRingCatIsoToRingEquiv.injective
  have hsurj : Function.Surjective (CommRingCat.Hom.hom V.topIso.inv) :=
    V.topIso.symm.commRingCatIsoToRingEquiv.surjective
  exact ideal_le_of_map_le_of_bijective_consolidated349 _ hinj hsurj hle

private theorem le_of_ideal_le_locally_consolidated349 (V : ↥Y → Y.Opens) (hmem : ∀ y : ↥Y, y ∈ V y)
    (hloc : ∀ (y : ↥Y) (W : Y.Opens) (hW : IsAffineOpen W), W ≤ V y →
      J.ideal ⟨W, hW⟩ ≤ J'.ideal ⟨W, hW⟩) :
    J ≤ J' := by
  have key : J ⊓ J' = J := by
    refine Scheme.IdealSheafData.ext_of_iSup_eq_top
      (ι := {W : Y.affineOpens // ∃ y : ↥Y, (W.1 : Y.Opens) ≤ V y})
      (fun W => W.1) ?_ ?_
    · rw [eq_top_iff]
      intro x _
      obtain ⟨W, hW, hxW, hWV⟩ :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (hmem x)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, x, hWV⟩, hxW⟩
    · rintro ⟨⟨W, hW⟩, y, hWV⟩
      show (J ⊓ J').ideal ⟨W, hW⟩ = J.ideal ⟨W, hW⟩
      simp only [Scheme.IdealSheafData.ideal_inf, Pi.inf_apply, inf_eq_left]
      exact hloc y W hW hWV
  exact inf_eq_left.mp key


end

section
variable (D : FiniteOpenCoverWithIdeals T)

theorem le_of_comap_summandι_le {J J' : D.disjointUnion.IdealSheafData}
    (h : ∀ i : D.idx, J.comap (D.summandι i) ≤ J'.comap (D.summandι i)) : J ≤ J' := by
  classical
  choose idxf hidxf using D.exists_mem_summandOpen
  refine le_of_ideal_le_locally_consolidated349 (fun y => D.summandOpen (idxf y)) hidxf ?_
  intro y W hW hWle
  refine ideal_le_of_comap_ι_le_consolidated349 W hW ?_
  have hrange : Set.range W.ι.base ⊆ Set.range (D.summandι (idxf y)).base := by
    rw [Scheme.Opens.range_ι, range_summandι D (idxf y), Scheme.Opens.range_ι]
    exact hWle
  have hg : IsOpenImmersion.lift (D.summandι (idxf y)) W.ι hrange ≫ D.summandι (idxf y)
      = W.ι :=
    IsOpenImmersion.lift_fac (D.summandι (idxf y)) W.ι hrange
  have e1 : J.comap W.ι
      = (J.comap (D.summandι (idxf y))).comap
        (IsOpenImmersion.lift (D.summandι (idxf y)) W.ι hrange) := by
    rw [← Scheme.IdealSheafData.comap_comp, hg]
  have e2 : J'.comap W.ι
      = (J'.comap (D.summandι (idxf y))).comap
        (IsOpenImmersion.lift (D.summandι (idxf y)) W.ι hrange) := by
    rw [← Scheme.IdealSheafData.comap_comp, hg]
  rw [e1, e2]
  exact Scheme.IdealSheafData.comap_mono _ (h (idxf y))

theorem etale_disjointUnionMap : Etale D.disjointUnionMap :=
  etale_sigmaOpensDesc T.scheme D.opens


end

instance instEtaleTotalMap (D : FiniteOpenCoverWithIdeals T) : Etale D.disjointUnionMap :=
  etale_disjointUnionMap D

theorem smooth_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) : Smooth D.disjointUnionMap := by
  have het : Etale D.disjointUnionMap := etale_disjointUnionMap D
  infer_instance

instance instSmoothTotalMap (D : FiniteOpenCoverWithIdeals T) : Smooth D.disjointUnionMap :=
  smooth_disjointUnionMap D

section
variable (D : FiniteOpenCoverWithIdeals T)

theorem flat_disjointUnionMap : Flat D.disjointUnionMap := by
  have he : Etale D.disjointUnionMap := etale_disjointUnionMap D
  have hs : Smooth D.disjointUnionMap := inferInstance
  infer_instance

theorem locallyOfFiniteType_disjointUnionMap : LocallyOfFiniteType D.disjointUnionMap :=
  locallyOfFiniteType_sigmaOpensDesc T.scheme D.opens


end

instance instLocallyOfFiniteTypeTotalMap (D : FiniteOpenCoverWithIdeals T) : LocallyOfFiniteType D.disjointUnionMap :=
  locallyOfFiniteType_disjointUnionMap D

section
variable (D : FiniteOpenCoverWithIdeals T)

theorem surjective_disjointUnionMap (h : iSup D.opens = ⊤) :
    Surjective D.disjointUnionMap :=
  surjective_sigmaOpensDesc T.scheme D.opens h

theorem isAffine_disjointUnion (h : ∀ i : D.idx, IsAffineOpen (D.opens i)) :
    IsAffine D.disjointUnion :=
  isAffine_sigmaOpens T.scheme D.opens h


end

private theorem subsingleton_spec_consolidated349 (k : Type u) [Field k] :
    Subsingleton ↥(Spec (CommRingCat.of k)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

section
variable (D : FiniteOpenCoverWithIdeals T)

theorem quasiCompact_disjointUnionMap_comp (h : ∀ i : D.idx, IsAffineOpen (D.opens i)) :
    QuasiCompact (D.disjointUnionMap ≫ T.structMap) := by
  have haff : IsAffine D.disjointUnion := isAffine_disjointUnion D h
  have hcs : CompactSpace ↥D.disjointUnion := inferInstance
  have hsub : Subsingleton ↥(Spec (CommRingCat.of T.base)) := subsingleton_spec_consolidated349 T.base
  exact AlgebraicGeometry.quasiCompact_of_compactSpace_of_subsingleton
    (D.disjointUnionMap ≫ T.structMap)

theorem isSmoothDivisor_iInfImageIdeal_of_exists_etaleChart (h : ∀ i : D.idx, ∃ (n : ℕ) (c : EtaleChart T.structMap (D.opens i) n),
      D.localIdeal i = ⊤ ∨ ∃ j : Fin n, D.localIdeal i = c.coordIdeal {j}) :
    IsSmoothDivisor (D.disjointUnionMap ≫ T.structMap) D.iInfImageIdeal := by
  refine FunctorialResolution.EmbeddedResolution.isSmoothDivisor_of_locally_coordIdeal D.iInfImageIdeal ?_
  intro x
  obtain ⟨i, hi⟩ := D.exists_mem_summandOpen x
  obtain ⟨n, c, hc⟩ := h i
  refine ⟨D.summandOpen i, hi, n, D.summandEtaleChart i c, ?_⟩
  rcases hc with htop | ⟨j, hj⟩
  · left
    rw [restrictIdeal_iInfImageIdeal_summandOpen D i, htop]
    simp
  · right
    refine ⟨j, ?_⟩
    rw [restrictIdeal_iInfImageIdeal_summandOpen D i, hj]
    exact (summandEtaleChart_coordIdeal D i c {j}).symm

theorem isSmoothDivisor_iInfImageIdeal_of_forall_eq_top_or_coordIdeal (halt : ∀ i : D.idx, D.localIdeal i = ⊤ ∨
      ∃ (n : ℕ) (c : EtaleChart T.structMap (D.opens i) n) (j : Fin n),
        D.localIdeal i = c.coordIdeal {j})
    (hchart : ∀ i : D.idx, ∃ n : ℕ, Nonempty (EtaleChart T.structMap (D.opens i) n)) :
    IsSmoothDivisor (D.disjointUnionMap ≫ T.structMap) D.iInfImageIdeal := by
  refine isSmoothDivisor_iInfImageIdeal_of_exists_etaleChart D ?_
  intro i
  rcases halt i with htop | ⟨n, c, j, hj⟩
  · obtain ⟨m, ⟨c⟩⟩ := hchart i
    exact ⟨m, c, Or.inl htop⟩
  · exact ⟨n, c, Or.inr ⟨j, hj⟩⟩


end

end FiniteOpenCoverWithIdeals

end MaxContactReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.MaximalContactCover
section

open CategoryTheory.Limits

section

abbrev markedTripleOfIdeal (k : Type u) [Field k] (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of k)) (J : Y.IdealSheafData) : MarkedIdealWithBoundary.{u} :=
  { base := k, scheme := Y, structMap := q, ideal := J, mult := 1, boundary := [] }

section
variable (k : Type u) [Field k] (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of k)) (J : Y.IdealSheafData)

@[simp] theorem markedTripleOfIdeal_scheme :
    (markedTripleOfIdeal k Y q J).scheme = Y := rfl

@[simp] theorem markedTripleOfIdeal_structureMorphism :
    (markedTripleOfIdeal k Y q J).structMap = q := rfl

@[simp] theorem markedTripleOfIdeal_ideal :
    (markedTripleOfIdeal k Y q J).ideal = J := rfl


end

def HasLocalEtaleCharts {X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) : Prop :=
  ∀ x : X', ∃ (W : X'.Opens) (_ : x ∈ W) (n : ℕ), Nonempty (EtaleChart p W n)

private theorem ofIdealTop_mono_consolidated381 {X : Scheme.{u}} {I J : Ideal Γ(X, ⊤)} (h : I ≤ J) :
    AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop I ≤
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop J := by
  intro U
  exact Ideal.map_mono h

theorem EtaleChart.coordIdeal_mono {Y : Scheme.{u}} {k : Type u} [Field k]
    {p : Y ⟶ Spec (CommRingCat.of k)} {U : Y.Opens} {m : ℕ} (ch : EtaleChart p U m)
    {S S' : Finset (Fin m)} (h : S ⊆ S') :
    ch.coordIdeal S ≤ ch.coordIdeal S' := by
  simp only [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_eq_ofIdealTop_span_coord]
  apply Scheme.IdealSheafData.comap_mono
  apply ofIdealTop_mono_consolidated381
  apply Ideal.span_mono
  rintro x ⟨i, hi, rfl⟩
  exact ⟨i, Finset.mem_coe.mpr (h (Finset.mem_coe.mp hi)), rfl⟩

section
variable {X X' : Scheme.{u}} (τ : X ⟶ X') [IsClosedImmersion τ]

private theorem coe_support_ker_eq_range_consolidated381 :
    (↑(Scheme.Hom.ker τ).support : Set X') = Set.range τ.base := by
  have h1 : ∀ z, ((FunctorialResolution.EmbeddedResolution.kerSubschemeIso τ).hom ≫ τ).base z
      = (Scheme.Hom.ker τ).subschemeι.base z := by
    intro z
    rw [FunctorialResolution.EmbeddedResolution.kerSubschemeIso_hom_comp τ]
  have h2 : ∀ x, ((FunctorialResolution.EmbeddedResolution.kerSubschemeIso τ).inv ≫ (Scheme.Hom.ker τ).subschemeι).base x
      = τ.base x := by
    intro x
    rw [FunctorialResolution.EmbeddedResolution.kerSubschemeIso_inv_comp τ]
  rw [← Scheme.IdealSheafData.range_subschemeι]
  apply Set.Subset.antisymm
  · rintro y ⟨z, rfl⟩
    exact ⟨(FunctorialResolution.EmbeddedResolution.kerSubschemeIso τ).hom.base z, h1 z⟩
  · rintro y ⟨x, rfl⟩
    exact ⟨(FunctorialResolution.EmbeddedResolution.kerSubschemeIso τ).inv.base x, h2 x⟩

theorem restrictIdeal_ker_eq_top_of_not_mem (U : X'.Opens) (h : ∀ x : X, τ.base x ∉ U) :
    restrictIdeal τ.ker U = ⊤ := by
  rw [restrictIdeal_eq_comap_ι, Scheme.IdealSheafData.eq_top_iff_support_eq_empty, support_comap_eq,
    coe_support_ker_eq_range_consolidated381 τ]
  refine Set.subset_empty_iff.mp ?_
  rintro y ⟨x, hx⟩
  refine absurd ?_ (h x)
  rw [hx]
  exact y.2


end

structure AdaptedEtaleChart {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X') (c : ℕ) : Type u where
  opens : X'.Opens
  isAffine : IsAffineOpen opens
  coordCount : ℕ
  chart : EtaleChart p opens coordCount
  idxSet : Finset (Fin coordCount)
  card_idxSet : idxSet.card = c
  coord : Fin coordCount
  coord_mem : coord ∈ idxSet
  restrictIdeal_ker : restrictIdeal τ.ker opens = chart.coordIdeal idxSet

private theorem coordIdeal_restrict_consolidated381 {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U V : X.Opens} {m : ℕ} (ch : EtaleChart p U m)
    (h : V ≤ U) (S : Finset (Fin m)) :
    (ch.restrict h).coordIdeal S = (ch.coordIdeal S).comap (X.homOfLE h) := by
  simp only [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.restrict_map]
  rw [Scheme.IdealSheafData.comap_comp]

theorem exists_adaptedEtaleChart {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X') (c : ℕ) (hc : 1 ≤ c)
    (hcodim : HasEtaleCoordCodim p τ c) :
    ∀ x : X, ∃ A : AdaptedEtaleChart p τ c, τ.base x ∈ A.opens := by
  intro x
  obtain ⟨U, hxU, m, ch, S, hcard, hker⟩ := hcodim x
  obtain ⟨V, hxV, hVU⟩ := AlgebraicGeometry.Scheme.exists_affineOpens_mem_le hxU
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  obtain ⟨j, hj⟩ := hSne
  refine ⟨⟨(V : X'.Opens), V.2, m, ch.restrict hVU, S, hcard, j, hj, ?_⟩, hxV⟩
  rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal (Scheme.Hom.ker τ) hVU, hker,
    coordIdeal_restrict_consolidated381 ch hVU S]

structure DisjointEtaleChart {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X') : Type u where
  opens : X'.Opens
  isAffine : IsAffineOpen opens
  coordCount : ℕ
  chart : EtaleChart p opens coordCount
  not_mem : ∀ x : X, τ.base x ∉ opens

theorem exists_disjointEtaleChart {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X') [IsClosedImmersion τ]
    (hcharts : HasLocalEtaleCharts p) (y : X') (hy : ∀ x : X, τ.base x ≠ y) :
    ∃ F : DisjointEtaleChart p τ, y ∈ F.opens := by
  obtain ⟨W, hyW, n, ⟨ch⟩⟩ := hcharts y
  have hclosed : IsClosed (Set.range τ.base) := by
    rw [← coe_support_ker_eq_range_consolidated381 τ]
    exact (Scheme.Hom.ker τ).support.2
  have hopen : IsOpen ((W : Set X') ∩ (Set.range τ.base)ᶜ) :=
    W.isOpen.inter hclosed.isOpen_compl
  have hynot : y ∉ Set.range τ.base := by
    rintro ⟨x, hx⟩
    exact hy x hx
  set O : X'.Opens := ⟨(W : Set X') ∩ (Set.range τ.base)ᶜ, hopen⟩
  have hyO : y ∈ O := Set.mem_inter hyW hynot
  obtain ⟨U, hyU, hUO⟩ := AlgebraicGeometry.Scheme.exists_affineOpens_mem_le hyO
  have hUW : (U : X'.Opens) ≤ W := by
    intro z hz
    exact (hUO hz).1
  refine ⟨⟨(U : X'.Opens), U.2, n, ch.restrict hUW, ?_⟩, hyU⟩
  intro x hx
  exact (hUO hx).2 ⟨x, rfl⟩

def coverOpens {X X' : Scheme.{u}} {k : Type u} [Field k]
    {p : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} {c : ℕ} {α : Type v} {β : Type w}
    (A : α → AdaptedEtaleChart p τ c) (B : β → DisjointEtaleChart p τ) : α ⊕ β → X'.Opens
  | Sum.inl a => (A a).opens
  | Sum.inr b => (B b).opens

section
variable {X X' : Scheme.{u}} {k : Type u} [Field k] {p : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} {c : ℕ} {α : Type v} {β : Type w} (A : α → AdaptedEtaleChart p τ c) (B : β → DisjointEtaleChart p τ)

@[simp] theorem coverOpens_inl (a : α) :
    coverOpens A B (Sum.inl a) = (A a).opens := rfl

@[simp] theorem coverOpens_inr (b : β) :
    coverOpens A B (Sum.inr b) = (B b).opens := rfl


end

def coverHypersurfaceIdeal {X X' : Scheme.{u}} {k : Type u} [Field k]
    {p : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} {c : ℕ} {α : Type v} {β : Type w}
    (A : α → AdaptedEtaleChart p τ c) (B : β → DisjointEtaleChart p τ) :
    (i : α ⊕ β) → (coverOpens A B i).toScheme.IdealSheafData
  | Sum.inl a => (A a).chart.coordIdeal {(A a).coord}
  | Sum.inr _ => ⊤











structure MaximalContactCover {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X') (I : X.IdealSheafData) (c : ℕ) :
    Type (u + 1) where
  toCoverData : MaxContactReduction.FiniteOpenCoverWithIdeals (markedTripleOfIdeal k X' p (imageIdealSheaf τ I))
  covers : iSup toCoverData.opens = ⊤
  isAffine : ∀ i : toCoverData.idx, IsAffineOpen (toCoverData.opens i)
  hasChart : ∀ i : toCoverData.idx, ∃ n : ℕ,
    Nonempty (EtaleChart p (toCoverData.opens i) n)
  hypersurface : ∀ i : toCoverData.idx, toCoverData.localIdeal i = ⊤ ∨
    ∃ (n : ℕ) (ch : EtaleChart p (toCoverData.opens i) n) (j : Fin n),
      toCoverData.localIdeal i = ch.coordIdeal {j}
  adapted : ∀ i : toCoverData.idx,
    (toCoverData.localIdeal i = ⊤ ∧ ∀ x : X, τ.base x ∉ toCoverData.opens i) ∨
    ∃ (n : ℕ) (ch : EtaleChart p (toCoverData.opens i) n) (S : Finset (Fin n)) (j : Fin n),
      S.card = c ∧ j ∈ S ∧
        restrictIdeal τ.ker (toCoverData.opens i) = ch.coordIdeal S ∧
        toCoverData.localIdeal i = ch.coordIdeal {j}

theorem nonempty_maximalContactCover {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) [QuasiCompact p]
    (τ : X ⟶ X') [IsClosedImmersion τ] (I : X.IdealSheafData) (c : ℕ) (hc : 1 ≤ c)
    (hcodim : HasEtaleCoordCodim p τ c) (hcharts : HasLocalEtaleCharts p) :
    Nonempty (MaximalContactCover p τ I c) := by
  classical
  have hSpec : IsCompact (Set.univ : Set ↥(Spec (CommRingCat.of k))) := by
    have h := (AlgebraicGeometry.isAffineOpen_top (Spec (CommRingCat.of k))).isCompact
    rwa [TopologicalSpace.Opens.coe_top] at h
  have hX'c : IsCompact (Set.univ : Set ↥X') := by
    have h := AlgebraicGeometry.QuasiCompact.isCompact_preimage (f := p) Set.univ isOpen_univ hSpec
    rwa [Set.preimage_univ] at h
  have hcover : ∀ y : ↥X', ∃ q : AdaptedEtaleChart p τ c ⊕ DisjointEtaleChart p τ,
      y ∈ coverOpens (fun a : AdaptedEtaleChart p τ c => a) (fun b : DisjointEtaleChart p τ => b) q := by
    intro y
    by_cases hy : ∃ x : ↥X, τ.base x = y
    · obtain ⟨x, hx⟩ := hy
      obtain ⟨A, hA⟩ := exists_adaptedEtaleChart p τ c hc hcodim x
      refine ⟨Sum.inl A, ?_⟩
      rw [← hx]
      exact hA
    · have hy' : ∀ x : X, τ.base x ≠ y := fun x hx => hy ⟨x, hx⟩
      obtain ⟨F, hF⟩ := exists_disjointEtaleChart p τ hcharts y hy'
      exact ⟨Sum.inr F, hF⟩
  have hsub : (Set.univ : Set ↥X') ⊆
      ⋃ q : AdaptedEtaleChart p τ c ⊕ DisjointEtaleChart p τ,
        ((coverOpens (fun a : AdaptedEtaleChart p τ c => a) (fun b : DisjointEtaleChart p τ => b) q :
          X'.Opens) : Set ↥X') := by
    intro y _
    obtain ⟨q, hq⟩ := hcover y
    exact Set.mem_iUnion.2 ⟨q, hq⟩
  obtain ⟨t, ht⟩ := hX'c.elim_finite_subcover
    (fun q : AdaptedEtaleChart p τ c ⊕ DisjointEtaleChart p τ =>
      ((coverOpens (fun a : AdaptedEtaleChart p τ c => a) (fun b : DisjointEtaleChart p τ => b) q :
        X'.Opens) : Set ↥X'))
    (fun q => (coverOpens (fun a : AdaptedEtaleChart p τ c => a) (fun b : DisjointEtaleChart p τ => b) q).isOpen)
    hsub
  refine ⟨⟨⟨{ q : AdaptedEtaleChart p τ c ⊕ DisjointEtaleChart p τ // q ∈ t }, inferInstance,
    fun q => coverOpens (fun a : AdaptedEtaleChart p τ c => a) (fun b : DisjointEtaleChart p τ => b) q.1,
    fun q => coverHypersurfaceIdeal (fun a : AdaptedEtaleChart p τ c => a)
      (fun b : DisjointEtaleChart p τ => b) q.1⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨q, hqt, hq⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact Set.mem_iUnion.2 ⟨⟨q, hqt⟩, hq⟩
  · rintro ⟨A | F, _⟩
    · exact A.isAffine
    · exact F.isAffine
  · rintro ⟨A | F, _⟩
    · exact ⟨A.coordCount, ⟨A.chart⟩⟩
    · exact ⟨F.coordCount, ⟨F.chart⟩⟩
  · rintro ⟨A | F, _⟩
    · exact Or.inr ⟨A.coordCount, A.chart, A.coord, rfl⟩
    · exact Or.inl rfl
  · rintro ⟨A | F, _⟩
    · exact Or.inr ⟨A.coordCount, A.chart, A.idxSet, A.coord, A.card_idxSet, A.coord_mem,
        A.restrictIdeal_ker, rfl⟩
    · exact Or.inl ⟨rfl, F.not_mem⟩

namespace MaximalContactCover

variable {X X' : Scheme.{u}} {k : Type u} [Field k] {p : X' ⟶ Spec (CommRingCat.of k)}
  {τ : X ⟶ X'} {I : X.IdealSheafData} {c : ℕ}

abbrev projection (C : MaximalContactCover p τ I c) : C.toCoverData.disjointUnion ⟶ X' :=
  C.toCoverData.disjointUnionMap

section
variable (C : MaximalContactCover p τ I c)

@[simp] theorem projection_eq :
    C.projection = C.toCoverData.disjointUnionMap := rfl

theorem isAffine_disjointUnion : IsAffine C.toCoverData.disjointUnion :=
  MaxContactReduction.FiniteOpenCoverWithIdeals.isAffine_disjointUnion C.toCoverData C.isAffine


end

instance instIsAffineTotal (C : MaximalContactCover p τ I c) : IsAffine C.toCoverData.disjointUnion :=
  C.isAffine_disjointUnion

theorem quasiCompact_projection_comp (C : MaximalContactCover p τ I c) :
    QuasiCompact (C.projection ≫ p) :=
  MaxContactReduction.FiniteOpenCoverWithIdeals.quasiCompact_disjointUnionMap_comp C.toCoverData C.isAffine

instance instQuasiCompactProjComp (C : MaximalContactCover p τ I c) :
    QuasiCompact (C.projection ≫ p) :=
  C.quasiCompact_projection_comp

theorem smooth_projection_comp (C : MaximalContactCover p τ I c) [Smooth p] :
    Smooth (C.projection ≫ p) := by
  have h : Smooth C.toCoverData.disjointUnionMap :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.smooth_disjointUnionMap C.toCoverData
  exact MorphismProperty.comp_mem (@Smooth) C.toCoverData.disjointUnionMap p h
    inferInstance

instance instSmoothProjComp (C : MaximalContactCover p τ I c) [Smooth p] :
    Smooth (C.projection ≫ p) :=
  C.smooth_projection_comp

theorem locallyOfFiniteType_projection_comp (C : MaximalContactCover p τ I c)
    [LocallyOfFiniteType p] :
    LocallyOfFiniteType (C.projection ≫ p) := by
  have h1 : LocallyOfFiniteType C.projection :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.locallyOfFiniteType_disjointUnionMap C.toCoverData
  exact MorphismProperty.comp_mem (@LocallyOfFiniteType) C.projection p h1
    inferInstance

instance instLocallyOfFiniteTypeProjComp (C : MaximalContactCover p τ I c)
    [LocallyOfFiniteType p] :
    LocallyOfFiniteType (C.projection ≫ p) :=
  C.locallyOfFiniteType_projection_comp

section
variable (C : MaximalContactCover p τ I c)

theorem isSmoothDivisor_iInfImageIdeal :
    IsSmoothDivisor (C.projection ≫ p) C.toCoverData.iInfImageIdeal :=
  MaxContactReduction.FiniteOpenCoverWithIdeals.isSmoothDivisor_iInfImageIdeal_of_forall_eq_top_or_coordIdeal C.toCoverData C.hypersurface C.hasChart

theorem surjective_projection :
    AlgebraicGeometry.Surjective C.projection :=
  MaxContactReduction.FiniteOpenCoverWithIdeals.surjective_disjointUnionMap C.toCoverData C.covers


end

abbrev pullbackFiber (C : MaximalContactCover p τ I c) : Scheme.{u} :=
  Limits.pullback τ C.projection

abbrev pullbackFiberToTotal (C : MaximalContactCover p τ I c) : C.pullbackFiber ⟶ C.toCoverData.disjointUnion :=
  Limits.pullback.snd τ C.projection

abbrev pullbackFiberToBase (C : MaximalContactCover p τ I c) : C.pullbackFiber ⟶ X :=
  Limits.pullback.fst τ C.projection

section
variable (C : MaximalContactCover p τ I c)

theorem isPullback_pullbackFiber :
    IsPullback C.pullbackFiberToBase C.pullbackFiberToTotal τ C.projection :=
  IsPullback.of_hasPullback τ C.projection

theorem isClosedImmersion_pullbackFiberToTotal [IsClosedImmersion τ] :
    IsClosedImmersion C.pullbackFiberToTotal := by
  have h : IsClosedImmersion τ := inferInstance
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsClosedImmersion) C.isPullback_pullbackFiber h


end

instance instIsClosedImmersionStarEmb (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    IsClosedImmersion C.pullbackFiberToTotal :=
  C.isClosedImmersion_pullbackFiberToTotal

theorem flat_pullbackFiberToBase (C : MaximalContactCover p τ I c) :
    Flat C.pullbackFiberToBase := by
  have h : Flat C.projection :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.flat_disjointUnionMap C.toCoverData
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Flat) C.isPullback_pullbackFiber.flip h

instance instFlatStarToBase (C : MaximalContactCover p τ I c) :
    Flat C.pullbackFiberToBase :=
  C.flat_pullbackFiberToBase

theorem smooth_pullbackFiberToBase (C : MaximalContactCover p τ I c) :
    Smooth C.pullbackFiberToBase := by
  have h : Smooth C.projection :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.smooth_disjointUnionMap C.toCoverData
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Smooth) C.isPullback_pullbackFiber.flip h

instance instSmoothStarToBase (C : MaximalContactCover p τ I c) :
    Smooth C.pullbackFiberToBase :=
  C.smooth_pullbackFiberToBase

theorem surjective_pullbackFiberToBase (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.Surjective C.pullbackFiberToBase := by
  have h : AlgebraicGeometry.Surjective C.projection := C.surjective_projection
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Surjective) C.isPullback_pullbackFiber.flip h

instance instSurjectiveStarToBase (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.Surjective C.pullbackFiberToBase :=
  C.surjective_pullbackFiberToBase

section
variable (C : MaximalContactCover p τ I c) [IsClosedImmersion τ]

theorem ker_pullbackFiberToTotal :
    Scheme.Hom.ker C.pullbackFiberToTotal = τ.ker.comap C.projection := by
  have hq : QuasiCompact τ := inferInstance
  have hq' : QuasiCompact C.pullbackFiberToTotal :=
    quasiCompact_of_isPullback C.isPullback_pullbackFiber
  have hf : Flat C.projection :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.flat_disjointUnionMap C.toCoverData
  exact ker_eq_comap_ker_of_isPullback_of_flat C.isPullback_pullbackFiber

theorem exists_factor_pullbackFiberToTotal :
    ∃ f : C.pullbackFiber ⟶ C.toCoverData.iInfImageIdeal.subscheme,
      f ≫ C.toCoverData.iInfImageIdeal.subschemeι = C.pullbackFiberToTotal := by
  have hle : C.toCoverData.iInfImageIdeal ≤ Scheme.Hom.ker C.pullbackFiberToTotal := by
    have hker : Scheme.Hom.ker C.pullbackFiberToTotal
        = (Scheme.Hom.ker τ).comap C.toCoverData.disjointUnionMap := C.ker_pullbackFiberToTotal
    rw [hker]
    refine MaxContactReduction.FiniteOpenCoverWithIdeals.le_of_comap_summandι_le C.toCoverData ?_
    intro i
    have e1 : C.toCoverData.iInfImageIdeal.comap (C.toCoverData.summandι i)
        = C.toCoverData.localIdeal i :=
      MaxContactReduction.FiniteOpenCoverWithIdeals.comap_iInfImageIdeal_summandι C.toCoverData i
    have e2 : ((Scheme.Hom.ker τ).comap C.toCoverData.disjointUnionMap).comap
          (C.toCoverData.summandι i)
        = restrictIdeal (Scheme.Hom.ker τ) (C.toCoverData.opens i) := by
      rw [← Scheme.IdealSheafData.comap_comp,
        MaxContactReduction.FiniteOpenCoverWithIdeals.summandι_comp_disjointUnionMap, restrictIdeal_eq_comap_ι]
    rw [e1, e2]
    rcases C.adapted i with ⟨htop, hnot⟩ | ⟨n, ch, S, j, hcard, hjS, hrestrict, hloc⟩
    · exact le_of_eq (htop.trans (restrictIdeal_ker_eq_top_of_not_mem τ _ hnot).symm)
    · rw [hloc, hrestrict]
      exact ch.coordIdeal_mono (Finset.singleton_subset_iff.mpr hjS)
  have hle' : Scheme.Hom.ker C.toCoverData.iInfImageIdeal.subschemeι
      ≤ Scheme.Hom.ker C.pullbackFiberToTotal := by
    rwa [Scheme.IdealSheafData.ker_subschemeι]
  exact ⟨IsClosedImmersion.lift C.toCoverData.iInfImageIdeal.subschemeι C.pullbackFiberToTotal hle',
    IsClosedImmersion.lift_fac C.toCoverData.iInfImageIdeal.subschemeι C.pullbackFiberToTotal hle'⟩


end

def pullbackFiberToHypersurface (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    C.pullbackFiber ⟶ C.toCoverData.iInfImageIdeal.subscheme :=
  (C.exists_factor_pullbackFiberToTotal).choose

section
variable (C : MaximalContactCover p τ I c) [IsClosedImmersion τ]

theorem pullbackFiberToHypersurface_comp_subschemeι :
    C.pullbackFiberToHypersurface ≫ C.toCoverData.iInfImageIdeal.subschemeι = C.pullbackFiberToTotal :=
  (C.exists_factor_pullbackFiberToTotal).choose_spec

theorem pullbackFiberToHypersurface_comp_subschemeι_assoc {Z : Scheme.{u}} (h : C.toCoverData.disjointUnion ⟶ Z) :
    C.pullbackFiberToHypersurface ≫ C.toCoverData.iInfImageIdeal.subschemeι ≫ h = C.pullbackFiberToTotal ≫ h := by
  rw [← Category.assoc, C.pullbackFiberToHypersurface_comp_subschemeι]

private theorem isClosedImmersion_pullbackFiberToHypersurface_comp_subschemeι_consolidated381 :
    IsClosedImmersion (C.pullbackFiberToHypersurface ≫ C.toCoverData.iInfImageIdeal.subschemeι) := by
  rw [C.pullbackFiberToHypersurface_comp_subschemeι]
  infer_instance

theorem isClosedImmersion_pullbackFiberToHypersurface :
    IsClosedImmersion C.pullbackFiberToHypersurface := by
  have := isClosedImmersion_pullbackFiberToHypersurface_comp_subschemeι_consolidated381 C
  exact AlgebraicGeometry.IsClosedImmersion.of_comp C.pullbackFiberToHypersurface
    C.toCoverData.iInfImageIdeal.subschemeι


end

instance instIsClosedImmersionStarFactor (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    IsClosedImmersion C.pullbackFiberToHypersurface :=
  C.isClosedImmersion_pullbackFiberToHypersurface

def comapImageIdealSheaf (C : MaximalContactCover p τ I c) : C.toCoverData.disjointUnion.IdealSheafData :=
  (imageIdealSheaf τ I).comap C.projection

theorem comapImageIdealSheaf_eq (C : MaximalContactCover p τ I c) :
    C.comapImageIdealSheaf = (imageIdealSheaf τ I).comap C.projection := rfl

def idealOnHypersurface (C : MaximalContactCover p τ I c) :
    C.toCoverData.iInfImageIdeal.subscheme.IdealSheafData :=
  C.comapImageIdealSheaf.comap C.toCoverData.iInfImageIdeal.subschemeι

theorem idealOnHypersurface_eq_comap (C : MaximalContactCover p τ I c) :
    C.idealOnHypersurface = C.comapImageIdealSheaf.comap C.toCoverData.iInfImageIdeal.subschemeι := rfl

section
variable (C : MaximalContactCover p τ I c) [IsClosedImmersion τ]

private theorem localIdeal_le_restrictIdeal_ker_consolidated381 (i : C.toCoverData.idx) :
    C.toCoverData.localIdeal i ≤ restrictIdeal (Scheme.Hom.ker τ) (C.toCoverData.opens i) := by
  rcases C.adapted i with ⟨htop, hnot⟩ | ⟨n, ch, S, j, hcard, hjS, hker, hloc⟩
  · have h1 := restrictIdeal_ker_eq_top_of_not_mem τ (C.toCoverData.opens i) hnot
    rw [htop]
    exact h1.ge
  · rw [hloc, hker]
    exact ch.coordIdeal_mono (Finset.singleton_subset_iff.mpr hjS)

private theorem iInfImageIdeal_le_comap_ker_consolidated381 :
    C.toCoverData.iInfImageIdeal ≤ (Scheme.Hom.ker τ).comap C.toCoverData.disjointUnionMap := by
  refine MaxContactReduction.FiniteOpenCoverWithIdeals.le_of_comap_summandι_le C.toCoverData ?_
  intro i
  rw [MaxContactReduction.FiniteOpenCoverWithIdeals.comap_iInfImageIdeal_summandι,
    ← Scheme.IdealSheafData.comap_comp,
    MaxContactReduction.FiniteOpenCoverWithIdeals.summandι_comp_disjointUnionMap]
  exact localIdeal_le_restrictIdeal_ker_consolidated381 C i

theorem comapImageIdealSheaf_eq_imageIdealSheaf_idealOnHypersurface :
    C.comapImageIdealSheaf = imageIdealSheaf C.toCoverData.iInfImageIdeal.subschemeι C.idealOnHypersurface := by
  have hG : Scheme.Hom.ker C.toCoverData.iInfImageIdeal.subschemeι = C.toCoverData.iInfImageIdeal := by
    simp
  have hle : Scheme.Hom.ker C.toCoverData.iInfImageIdeal.subschemeι ≤ C.comapImageIdealSheaf := by
    rw [hG, C.comapImageIdealSheaf_eq]
    exact le_trans (iInfImageIdeal_le_comap_ker_consolidated381 C)
      (Scheme.IdealSheafData.comap_mono C.projection (ker_le_map_idealSheaf τ I))
  have h2 := ker_subschemeι_comp_eq_of_ker_le C.toCoverData.iInfImageIdeal.subschemeι C.comapImageIdealSheaf hle
    C.idealOnHypersurface C.idealOnHypersurface_eq_comap
  exact h2.symm

theorem idealOnHypersurface_eq_imageIdealSheaf :
    C.idealOnHypersurface = imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase) := by
  have hqc : QuasiCompact τ := inferInstance
  have hflat : Flat C.projection :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.flat_disjointUnionMap C.toCoverData
  have h1 : (imageIdealSheaf τ I).comap C.projection
      = imageIdealSheaf C.pullbackFiberToTotal (I.comap C.pullbackFiberToBase) :=
    comap_map_eq_map_comap_of_isPullback C.isPullback_pullbackFiber I
  have h2 : imageIdealSheaf C.pullbackFiberToTotal (I.comap C.pullbackFiberToBase)
      = imageIdealSheaf C.toCoverData.iInfImageIdeal.subschemeι
          (imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase)) := by
    have h := Scheme.IdealSheafData.map_comp (I.comap C.pullbackFiberToBase) C.pullbackFiberToHypersurface
      C.toCoverData.iInfImageIdeal.subschemeι
    rw [C.pullbackFiberToHypersurface_comp_subschemeι] at h
    exact h
  have h3 : (imageIdealSheaf C.toCoverData.iInfImageIdeal.subschemeι
        (imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase))).comap
        C.toCoverData.iInfImageIdeal.subschemeι
      = imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase) :=
    Blowup.comap_map_of_isClosedImmersion
      C.toCoverData.iInfImageIdeal.subschemeι (imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase))
  rw [C.idealOnHypersurface_eq_comap, C.comapImageIdealSheaf_eq, h1, h2, h3]


end

end MaximalContactCover


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.TotalTransform
section

open TopologicalSpace

section

theorem mem_support_restrictIdeal_iff {Y : Scheme.{u}} (K : Y.IdealSheafData) (V : Y.Opens)
    (v : ↥V.toScheme) :
    v ∈ (restrictIdeal K V).support ↔ V.ι v ∈ K.support := by
  rw [restrictIdeal_eq_comap_ι]
  have h : (↑(K.comap V.ι).support : Set ↥V.toScheme) = ⇑V.ι ⁻¹' (↑K.support : Set ↥Y) :=
    support_comap_eq V.ι K
  exact Set.ext_iff.mp h v

theorem exists_opens_totalTransform_eq_of_notMem_support {X X₁ : Scheme.{u}}
    [IsLocallyNoetherian X₁] (π : X₁ ⟶ X) (Z D : X.IdealSheafData) (x₁ : ↥X₁)
    (hx₁ : π x₁ ∉ Z.support) :
    ∃ V : X₁.Opens, x₁ ∈ V ∧
      restrictIdeal (D.comap π) V =
        restrictIdeal (Blowup.strictTransform π Z D) V * restrictIdeal (Blowup.exceptionalIdeal π Z) V ^ 1 := by
  refine ⟨π ⁻¹ᵁ Z.support.compl, hx₁, ?_⟩
  rw [restrictIdeal_strictTransform_eq_comap_of_le_compl π Z D _ le_rfl,
    restrictIdeal_exceptionalIdeal_eq_top_of_le_compl π Z _ le_rfl, pow_one,
    Scheme.IdealSheafData.mul_top]

section
variable {X : Scheme.{u}} {k : Type u} [Field k]

theorem inter_support_subset_support_of_mem_coordIdeal (p : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (Z D : X.IdealSheafData) (S : Finset (Fin m)) (j : Fin m) (hj : j ∈ S)
    (hZ : restrictIdeal Z U = c.coordIdeal S)
    (hD : restrictIdeal D U = c.coordIdeal {j}) :
    (↑Z.support : Set ↥X) ∩ (U : Set ↥X) ⊆ (↑D.support : Set ↥X) := by
  have hle : restrictIdeal D U ≤ restrictIdeal Z U := by
    rw [hD, hZ]
    exact c.coordIdeal_mono (Finset.singleton_subset_iff.mpr hj)
  intro x hx
  obtain ⟨v, hv⟩ : ∃ v : ↥U.toScheme, U.ι v = x := ⟨⟨x, hx.2⟩, rfl⟩
  have h1 : v ∈ (restrictIdeal Z U).support := by
    rw [mem_support_restrictIdeal_iff, hv]
    exact hx.1
  have h2 : v ∈ (restrictIdeal D U).support := Scheme.IdealSheafData.support_antitone hle h1
  rw [mem_support_restrictIdeal_iff, hv] at h2
  exact h2

theorem not_inter_support_subset_support_of_notMem_coordIdeal [NoetherianSpace ↥X] (p : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens}
    (hU : IsAffineOpen U) {m : ℕ} (c : EtaleChart p U m) (Z D : X.IdealSheafData)
    (S : Finset (Fin m)) (j : Fin m) (hj : j ∉ S)
    (hZ : restrictIdeal Z U = c.coordIdeal S)
    (hD : restrictIdeal D U = c.coordIdeal {j})
    (x : ↥X) (hxU : x ∈ U) (hxZ : x ∈ Z.support) :
    ¬ ((↑Z.support : Set ↥X) ∩ (U : Set ↥X) ⊆ (↑D.support : Set ↥X)) := by
  intro hsub
  obtain ⟨i, hi⟩ := exists_complOrderEmb_eq m S hj
  have hD' : restrictIdeal D U = c.coordIdeal {complOrderEmb m S i} := by
    rw [hi]; exact hD
  have hG : restrictIdeal (D.comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U)
      = (c.restrictToSubscheme hU Z S hZ).coordIdeal {i} :=
    c.restrictToSubscheme_coordIdeal_singleton hU Z S hZ i D hD'
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (restrictIdeal (D.comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U)) := by
    refine isLocallyGeneratedByNonZeroDivisor_of_locally_coordIdeal
      (p := (Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p)) _ ?_
    intro y
    refine ⟨⊤, trivial, m - S.card, (c.restrictToSubscheme hU Z S hZ).restrictOpens ⊤,
      Or.inr ⟨i, ?_⟩⟩
    rw [hG]
    exact (c.restrictToSubscheme hU Z S hZ).restrictIdeal_coordIdeal ⊤ {i}
  have hall : ∀ y : ↥(Z.subschemeι ⁻¹ᵁ U).toScheme,
      y ∈ (restrictIdeal (D.comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U)).support := by
    intro y
    rw [mem_support_restrictIdeal_iff]
    have hyU : Z.subschemeι ((Z.subschemeι ⁻¹ᵁ U).ι y) ∈ (U : Set ↥X) := y.2
    have hyZ : Z.subschemeι ((Z.subschemeι ⁻¹ᵁ U).ι y) ∈ (↑Z.support : Set ↥X) := by
      rw [← Scheme.IdealSheafData.range_subschemeι Z]
      exact Set.mem_range_self _
    have hmem : Z.subschemeι ((Z.subschemeι ⁻¹ᵁ U).ι y) ∈ (↑D.support : Set ↥X) :=
      hsub ⟨hyZ, hyU⟩
    have h2 : ((Z.subschemeι ⁻¹ᵁ U).ι y) ∈
        (↑(D.comap Z.subschemeι).support : Set ↥Z.subscheme) := by
      rw [support_comap_eq Z.subschemeι D]
      exact hmem
    exact h2
  obtain ⟨z, hz⟩ : ∃ z : ↥Z.subscheme, Z.subschemeι z = x := by
    have hxr : x ∈ Set.range (⇑Z.subschemeι) := by
      rw [Scheme.IdealSheafData.range_subschemeι Z]
      exact hxZ
    exact hxr
  have hzU : z ∈ Z.subschemeι ⁻¹ᵁ U := by
    show Z.subschemeι z ∈ U
    rw [hz]
    exact hxU
  obtain ⟨y₀, -⟩ : ∃ y₀ : ↥(Z.subschemeι ⁻¹ᵁ U).toScheme, (Z.subschemeι ⁻¹ᵁ U).ι y₀ = z :=
    ⟨⟨z, hzU⟩, rfl⟩
  exact hcart.not_irreducibleComponent_subset_support
    (irreducibleComponent_mem_irreducibleComponents y₀) (fun w _ => hall w)


end

theorem comap_eq_strictTransform_mul_exceptionalIdeal_pow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ Z : T.scheme.IdealSheafData,
      Smooth (Z.subschemeι ≫ T.structMap) →
      HasStrictNormalCrossingsWith T.structMap Z T.boundary →
      ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
      ∀ D ∈ T.boundary, ∀ x' : ↥X',
        ∃ (U' : X'.Opens) (ε : ℕ), x' ∈ U' ∧ (ε = 0 ∨ ε = 1) ∧
          (ε = 1 ↔ ∃ V : T.scheme.Opens, π x' ∈ V ∧
            ((↑Z.support : Set ↥T.scheme) ∩ (V : Set ↥T.scheme)) ⊆ (↑D.support : Set ↥T.scheme)) ∧
          (D.comap π).comap U'.ι =
            (Blowup.strictTransform π Z D).comap U'.ι * ((Blowup.exceptionalIdeal π Z).comap U'.ι) ^ ε := by
  intro T hV Z _hZsm hsnc X' π hπ D hD x'
  have : IsNoetherian T.scheme := hV.isNoetherian
  have : NoetherianSpace ↥T.scheme := inferInstance
  have : IsNoetherian X' := isNoetherian_of_isBlowupAlongIdealSheaf hπ
  have : IsLocallyNoetherian X' := inferInstance
  by_cases hx : π x' ∈ Z.support
  · obtain ⟨U, hxU, m, c, a, S, _hinj, hnone, hsome, hZU⟩ := hsnc.exists_etaleChart hx
    obtain ⟨i, hi, hDi⟩ := List.mem_iff_getElem.mp hD
    have hx'U : x' ∈ π ⁻¹ᵁ U := hxU
    obtain ⟨s, hs, B, hx'B⟩ :
        ∃ (s : Fin m) (_ : s ∈ S) (B : BlowupChart π c S s), x' ∈ B.domain := by
      obtain ⟨s, hs, hmem⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZU x' hx'U
      exact ⟨s, hs, _, hmem⟩
    cases hai : a i with
    | none =>
      have hDtop : restrictIdeal D U = ⊤ := by
        have h1 := hnone i hi hai
        rwa [hDi] at h1
      refine ⟨B.domain, 0, hx'B, Or.inl rfl, ?_, ?_⟩
      · refine ⟨fun h0 => absurd h0 (by omega), fun hV' => ?_⟩
        obtain ⟨V, hxV, hsubV⟩ := hV'
        exact absurd (hsubV ⟨hx, hxV⟩)
          (notMem_support_of_restrictIdeal_eq_top D U _ hxU hDtop)
      · show restrictIdeal (D.comap π) B.domain =
          restrictIdeal (Blowup.strictTransform π Z D) B.domain *
            restrictIdeal (Blowup.exceptionalIdeal π Z) B.domain ^ 0
        rw [B.restrictIdeal_comap_top D hDtop, B.restrictIdeal_strictTransform_of_eq_top Z D hDtop,
          pow_zero, mul_one]
    | some t =>
      have hDU : restrictIdeal D U = c.coordIdeal {t} := by
        have h1 := hsome i hi t hai
        rwa [hDi] at h1
      by_cases htS : t ∈ S
      · have hcrit : ∃ V : T.scheme.Opens, π x' ∈ V ∧
            ((↑Z.support : Set ↥T.scheme) ∩ (V : Set ↥T.scheme)) ⊆
              (↑D.support : Set ↥T.scheme) :=
          ⟨U, hxU,
            inter_support_subset_support_of_mem_coordIdeal T.structMap c Z D S t htS hZU hDU⟩
        refine ⟨B.domain, 1, hx'B, Or.inr rfl, ⟨fun _ => hcrit, fun _ => rfl⟩, ?_⟩
        show restrictIdeal (D.comap π) B.domain =
          restrictIdeal (Blowup.strictTransform π Z D) B.domain *
            restrictIdeal (Blowup.exceptionalIdeal π Z) B.domain ^ 1
        by_cases hts : t = s
        · rw [hts] at hDU
          rw [B.restrictIdeal_comap_coordIdeal_self D hDU,
            B.restrictIdeal_strictTransform_coordIdeal_self Z D hs hZU hDU,
            B.restrictIdeal_exceptionalIdeal Z hs hZU, pow_one,
            Scheme.IdealSheafData.top_mul]
        · rw [B.restrictIdeal_comap_coordIdeal_of_mem D t htS hts hDU,
            B.restrictIdeal_strictTransform_of_mem_of_ne Z D hs hZU t htS hts hDU,
            B.restrictIdeal_exceptionalIdeal Z hs hZU, pow_one]
      · refine ⟨B.domain, 0, hx'B, Or.inl rfl, ?_, ?_⟩
        · refine ⟨fun h0 => absurd h0 (by omega), fun hV' => ?_⟩
          exfalso
          obtain ⟨V, hxV, hsubV⟩ := hV'
          obtain ⟨W, hxW, hWle⟩ :
              ∃ W : T.scheme.affineOpens, π x' ∈ W.1 ∧ W.1 ≤ U ⊓ V := by
            apply Scheme.exists_affineOpens_mem_le
            exact (⟨hxU, hxV⟩ : π x' ∈ U ⊓ V)
          have hWU : W.1 ≤ U := hWle.trans inf_le_left
          have hWV : W.1 ≤ V := hWle.trans inf_le_right
          have hZW := restrictIdeal_eq_restrict_coordIdeal_of_le hWU c Z S hZU
          have hDW := restrictIdeal_eq_restrict_coordIdeal_of_le hWU c D {t} hDU
          refine not_inter_support_subset_support_of_notMem_coordIdeal T.structMap W.2
            (c.restrict hWU) Z D S t htS hZW hDW (π x') hxW hx ?_
          intro w hw
          exact hsubV ⟨hw.1, SetLike.coe_subset_coe.mpr hWV hw.2⟩
        · show restrictIdeal (D.comap π) B.domain =
            restrictIdeal (Blowup.strictTransform π Z D) B.domain *
              restrictIdeal (Blowup.exceptionalIdeal π Z) B.domain ^ 0
          rw [B.restrictIdeal_comap_coordIdeal_of_not_mem D t htS hDU,
            B.restrictIdeal_strictTransform_coordIdeal_of_notMem Z D hs hZU t htS hDU, pow_zero, mul_one]
  · obtain ⟨V, hxV, hVeq⟩ := exists_opens_totalTransform_eq_of_notMem_support π Z D x' hx
    refine ⟨V, 1, hxV, Or.inr rfl, ?_, hVeq⟩
    refine ⟨fun _ => ⟨Z.support.compl, hx, ?_⟩, fun _ => rfl⟩
    intro y hy
    exact absurd hy.1 hy.2


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.HypersurfaceFiberCodim
section


section

private theorem comap_subschemeι_self_consolidated412 {W : Scheme.{u}} (J : W.IdealSheafData) :
    J.comap J.subschemeι = ⊥ := by
  simp [Scheme.IdealSheafData.comap]

theorem card_complEmbPreimage (m : ℕ) (S : Finset (Fin m)) (a : Fin m) (ha : a ∈ S) :
    (complEmbPreimage m S a).card = S.card - 1 := by
  classical
  rw [← Finset.card_erase_of_mem ha]
  refine Finset.card_bij (fun t _ => complOrderEmb m ({a} : Finset (Fin m)) t) ?_ ?_ ?_
  · intro t ht
    rw [mem_complEmbPreimage] at ht
    refine Finset.mem_erase.mpr ⟨?_, ht⟩
    intro hcontra
    exact (complOrderEmb_notMem m {a} t) (by rw [hcontra]; exact Finset.mem_singleton_self a)
  · intro t₁ _ t₂ _ hEq
    exact (complOrderEmb m ({a} : Finset (Fin m))).injective hEq
  · intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_erase.mp hb
    obtain ⟨t, ht⟩ := exists_complOrderEmb_eq m ({a} : Finset (Fin m)) (by simpa using hb1)
    exact ⟨t, mem_complEmbPreimage_of_complOrderEmb_eq m S a hb2 ht, ht⟩

namespace MaximalContactCover

variable {X X' : Scheme.{u}} {k : Type u} [Field k] {p : X' ⟶ Spec (CommRingCat.of k)}
  {τ : X ⟶ X'} {I : X.IdealSheafData} {c : ℕ}

section
variable (C : MaximalContactCover p τ I c)

theorem comap_iInfImageIdeal_subschemeι_eq_bot :
    C.toCoverData.iInfImageIdeal.comap C.toCoverData.iInfImageIdeal.subschemeι = ⊥ :=
  comap_subschemeι_self_consolidated412 C.toCoverData.iInfImageIdeal

theorem ker_pullbackFiberToHypersurface [IsClosedImmersion τ] :
    Scheme.Hom.ker C.pullbackFiberToHypersurface =
      (Scheme.Hom.ker C.pullbackFiberToTotal).comap C.toCoverData.iInfImageIdeal.subschemeι := by
  have h := Scheme.Hom.ker_comp C.pullbackFiberToHypersurface C.toCoverData.iInfImageIdeal.subschemeι
  rw [C.pullbackFiberToHypersurface_comp_subschemeι] at h
  rw [h, Blowup.comap_map_of_isClosedImmersion]

theorem hasEtaleCoordCodim_pullbackFiberToHypersurface [IsClosedImmersion τ] :
    HasEtaleCoordCodim (C.toCoverData.iInfImageIdeal.subschemeι ≫ C.projection ≫ p) C.pullbackFiberToHypersurface
      (c - 1) := by
  intro x
  obtain ⟨i, y, hy⟩ :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.exists_summandι_base_eq C.toCoverData (C.pullbackFiberToTotal.base x)
  have hmemU : C.pullbackFiberToTotal.base x ∈ C.toCoverData.summandOpen i := by
    rw [← hy]
    exact Set.mem_range_self y
  have hprojmem : C.toCoverData.disjointUnionMap.base (C.pullbackFiberToTotal.base x) ∈ C.toCoverData.opens i := by
    rw [← hy]
    exact MaxContactReduction.FiniteOpenCoverWithIdeals.disjointUnionMap_summandι_mem C.toCoverData i y
  have h1 : τ.base (C.pullbackFiberToBase.base x)
      = C.toCoverData.disjointUnionMap.base (C.pullbackFiberToTotal.base x) := by
    have h0 : C.pullbackFiberToBase ≫ τ = C.pullbackFiberToTotal ≫ C.projection := Limits.pullback.condition
    have h2 := congrArg (fun f : C.pullbackFiber ⟶ X' => f.base x) h0
    simpa using h2
  rcases C.adapted i with ⟨-, hfar⟩ | ⟨n, ch, S, j, hcard, hjS, hker, hloc⟩
  · exfalso
    refine hfar (C.pullbackFiberToBase.base x) ?_
    rw [h1]
    exact hprojmem
  · have hUaff : IsAffineOpen (C.toCoverData.summandOpen i) :=
      MaxContactReduction.FiniteOpenCoverWithIdeals.isAffineOpen_summandOpen C.toCoverData i (C.isAffine i)
    have hkse : Scheme.Hom.ker C.pullbackFiberToTotal
        = (Scheme.Hom.ker τ).comap C.toCoverData.disjointUnionMap := C.ker_pullbackFiberToTotal
    have hH : restrictIdeal C.toCoverData.iInfImageIdeal (C.toCoverData.summandOpen i) =
        (C.toCoverData.summandEtaleChart i ch).coordIdeal {j} := by
      rw [MaxContactReduction.FiniteOpenCoverWithIdeals.restrictIdeal_iInfImageIdeal_summandOpen C.toCoverData i,
        MaxContactReduction.FiniteOpenCoverWithIdeals.summandEtaleChart_coordIdeal C.toCoverData i ch {j}, hloc]
    have h2 := MaxContactReduction.FiniteOpenCoverWithIdeals.restrictIdeal_comap_disjointUnionMap_summandOpen
      C.toCoverData i (Scheme.Hom.ker τ)
    have h3 := MaxContactReduction.FiniteOpenCoverWithIdeals.summandEtaleChart_coordIdeal C.toCoverData i ch S
    have hZ : restrictIdeal (Scheme.Hom.ker C.pullbackFiberToTotal) (C.toCoverData.summandOpen i) =
        (C.toCoverData.summandEtaleChart i ch).coordIdeal S := by
      rw [hkse, h3]
      exact h2.trans (by rw [hker])
    have hb : C.toCoverData.iInfImageIdeal.subschemeι.base (C.pullbackFiberToHypersurface.base x)
        = C.pullbackFiberToTotal.base x := by
      have h4 := congrArg (fun f : C.pullbackFiber ⟶ C.toCoverData.disjointUnion => f.base x)
        C.pullbackFiberToHypersurface_comp_subschemeι
      simpa using h4
    refine ⟨C.toCoverData.iInfImageIdeal.subschemeι ⁻¹ᵁ C.toCoverData.summandOpen i, ?_,
      n - ({j} : Finset (Fin n)).card,
      (C.toCoverData.summandEtaleChart i ch).restrictToSubscheme hUaff C.toCoverData.iInfImageIdeal {j} hH,
      complEmbPreimage n S j, ?_, ?_⟩
    · show C.toCoverData.iInfImageIdeal.subschemeι.base (C.pullbackFiberToHypersurface.base x) ∈
        C.toCoverData.summandOpen i
      rw [hb]
      exact hmemU
    · rw [card_complEmbPreimage n S j hjS, hcard]
    · rw [C.ker_pullbackFiberToHypersurface]
      exact restrictIdeal_comap_subschemeι_eq_coordIdeal (C.toCoverData.summandEtaleChart i ch)
        hUaff (Scheme.Hom.ker C.pullbackFiberToTotal) C.toCoverData.iInfImageIdeal S j hZ hH

theorem isIso_pullbackFiberToHypersurface_of_eq_one [IsClosedImmersion τ] (hc : c = 1) :
    IsIso C.pullbackFiberToHypersurface := by
  have hkse : Scheme.Hom.ker C.pullbackFiberToTotal
      = (Scheme.Hom.ker τ).comap C.toCoverData.disjointUnionMap := C.ker_pullbackFiberToTotal
  have hkey : Scheme.Hom.ker C.pullbackFiberToTotal = C.toCoverData.iInfImageIdeal := by
    rw [hkse]
    refine MaxContactReduction.FiniteOpenCoverWithIdeals.ext_of_comap_summandι C.toCoverData (fun i => ?_)
    have e1 : C.toCoverData.iInfImageIdeal.comap (C.toCoverData.summandι i)
        = C.toCoverData.localIdeal i :=
      MaxContactReduction.FiniteOpenCoverWithIdeals.comap_iInfImageIdeal_summandι C.toCoverData i
    have e2 : ((Scheme.Hom.ker τ).comap C.toCoverData.disjointUnionMap).comap
          (C.toCoverData.summandι i)
        = restrictIdeal (Scheme.Hom.ker τ) (C.toCoverData.opens i) := by
      rw [← Scheme.IdealSheafData.comap_comp,
        MaxContactReduction.FiniteOpenCoverWithIdeals.summandι_comp_disjointUnionMap C.toCoverData i]
    rw [e1, e2]
    rcases C.adapted i with ⟨hloc, hfar⟩ | ⟨n, ch, S, j, hcard, hjS, hker, hloc⟩
    · rw [hloc]
      exact restrictIdeal_ker_eq_top_of_not_mem τ (C.toCoverData.opens i) hfar
    · have hS : S = {j} := by
        have h1 : S.card = 1 := by rw [hcard, hc]
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
        subst ha
        rw [Finset.mem_singleton] at hjS
        rw [hjS]
      rw [hker, hloc, hS]
  have hker0 : Scheme.Hom.ker C.pullbackFiberToHypersurface = ⊥ := by
    rw [C.ker_pullbackFiberToHypersurface, hkey, C.comap_iInfImageIdeal_subschemeι_eq_bot]
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker0


end

end MaximalContactCover


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.HypersurfaceScheme
section

open CategoryTheory.Limits

section

private def chartOnOpenSubscheme_consolidated411 {Y : Scheme.{u}} {k : Type u} [Field k] {q : Y ⟶ Spec (CommRingCat.of k)}
    {V : Y.Opens} {m : ℕ} (c : EtaleChart q V m)
    (hEt : Etale ((⊤ : V.toScheme.Opens).ι ≫ c.map)) :
    EtaleChart (V.ι ≫ q) (⊤ : V.toScheme.Opens) m where
  map := (⊤ : V.toScheme.Opens).ι ≫ c.map
  comp_struct := by rw [Category.assoc, c.comp_struct]
  isEtale := hEt

private theorem restrictIdeal_top_coordIdeal_consolidated411 {Y : Scheme.{u}} {k : Type u} [Field k]
    {q : Y ⟶ Spec (CommRingCat.of k)} {V : Y.Opens} {m : ℕ} (c : EtaleChart q V m)
    (hEt : Etale ((⊤ : V.toScheme.Opens).ι ≫ c.map))
    (S : Finset (Fin m)) :
    restrictIdeal (c.coordIdeal S) (⊤ : V.toScheme.Opens) = (chartOnOpenSubscheme_consolidated411 c hEt).coordIdeal S := by
  simp only [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  exact (Scheme.IdealSheafData.comap_comp _ _ _).symm

private theorem false_of_forall_mem_support_of_coordIdeal_singleton_consolidated411 {Z : Scheme.{u}} {k : Type u} [Field k]
    (p : Z ⟶ Spec (CommRingCat.of k)) (hZ : IsAffineOpen (⊤ : Z.Opens)) {m : ℕ}
    (c : EtaleChart p (⊤ : Z.Opens) m) (j : Fin m) (D : Z.IdealSheafData)
    (hD : restrictIdeal D (⊤ : Z.Opens) = c.coordIdeal {j})
    (hsupp : ∀ y : ↥Z, y ∈ D.support) (y₀ : ↥Z) : False := by
  have hnzd := coord_mem_nonZeroDivisors hZ c j
  have hno : ∀ y : ↥Z, y ∉ Z.basicOpen (c.coord j) := by
    intro y hy
    have hu := (Z.mem_basicOpen (c.coord j) y trivial).mp hy
    have h1 : stalkIdeal D y ≠ ⊤ := (mem_support_iff_stalkIdeal_ne_top D y).mp (hsupp y)
    apply h1
    rw [stalkIdeal_eq_span_germ_coord p hZ c j D hD y trivial, Ideal.span_singleton_eq_top]
    exact hu
  have hnil : IsNilpotent (c.coord j) := by
    rw [Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hZ.isCompact]
    refine le_antisymm ?_ bot_le
    intro y hy
    exact absurd hy (hno y)
  obtain ⟨n, hn⟩ := hnil
  have hone : (1 : ↑(Z.presheaf.obj (Opposite.op (⊤ : Z.Opens)))) = 0 :=
    (mem_nonZeroDivisors_iff.mp (pow_mem hnzd n)).2 1 (by rw [one_mul, hn])
  have h1 : stalkIdeal D y₀ ≠ ⊤ := (mem_support_iff_stalkIdeal_ne_top D y₀).mp (hsupp y₀)
  apply h1
  rw [stalkIdeal_eq_span_germ_coord p hZ c j D hD y₀ trivial, Ideal.eq_top_iff_one]
  have hstalk1 : (1 : ↑(Z.presheaf.stalk y₀)) = 0 := by
    have h := congrArg (CommRingCat.Hom.hom (Z.presheaf.germ (⊤ : Z.Opens) y₀ trivial)) hone
    simp at h
  rw [hstalk1]
  exact Submodule.zero_mem _

theorem nonzeroOnComponents_of_locally_eq_coordIdeal {Y : Scheme.{u}} {k : Type u} [Field k]
    (q : Y ⟶ Spec (CommRingCat.of k)) (K : Y.IdealSheafData)
    (hfin : (irreducibleComponents ↥Y).Finite)
    (hloc : ∀ y : ↥Y, y ∈ K.support → ∃ (U : Y.Opens) (_ : y ∈ U) (m : ℕ)
      (ch : EtaleChart q U m) (S : Finset (Fin m)),
      S.Nonempty ∧ restrictIdeal K U = ch.coordIdeal S) :
    NonzeroOnComponents K := by
  rw [nonzeroOnComponents_iff]
  intro T hT hTsub
  have hTirr : IsIrreducible T := hT.1
  have hOfin : (irreducibleComponents ↥Y \ {T}).Finite := hfin.subset Set.sdiff_subset
  have hOclosed : IsClosed (⋃₀ (irreducibleComponents ↥Y \ {T})) := by
    rw [Set.sUnion_eq_biUnion]
    exact Set.Finite.isClosed_biUnion hOfin
      (fun s hs => isClosed_of_mem_irreducibleComponents s hs.1)
  have hOsub : ∀ z : ↥Y, z ∉ (⋃₀ (irreducibleComponents ↥Y \ {T})) → z ∈ T := by
    intro z hz
    by_cases hEq : irreducibleComponent z = T
    · rw [← hEq]
      exact mem_irreducibleComponent
    · exact (hz (Set.mem_sUnion.mpr ⟨irreducibleComponent z,
        ⟨irreducibleComponent_mem_irreducibleComponents z,
          fun hmem => hEq (Set.mem_singleton_iff.mp hmem)⟩,
        mem_irreducibleComponent⟩)).elim
  obtain ⟨x, hxT, hxO⟩ :
      ∃ x : ↥Y, x ∈ T ∧ x ∉ (⋃₀ (irreducibleComponents ↥Y \ {T})) := by
    by_contra hcon
    push Not at hcon
    have hsub : T ⊆ ⋃₀ ((hOfin.toFinset : Finset (Set ↥Y)) : Set (Set ↥Y)) := by
      intro t ht
      rw [Set.Finite.coe_toFinset]
      exact hcon t ht
    obtain ⟨C, hCmem, hTsubC⟩ := isIrreducible_iff_sUnion_isClosed.mp hTirr hOfin.toFinset
      (fun C hC => isClosed_of_mem_irreducibleComponents C (hOfin.mem_toFinset.mp hC).1) hsub
    have hC := hOfin.mem_toFinset.mp hCmem
    exact hC.2 (Set.mem_singleton_iff.mpr (Set.Subset.antisymm (hT.2 hC.1.1 hTsubC) hTsubC))
  obtain ⟨U, hxU, m, ch, S, hSne, hKU⟩ := hloc x (hTsub hxT)
  obtain ⟨j, hjS⟩ := hSne
  have hWopen : IsOpen ((U : Set ↥Y) ∩ (⋃₀ (irreducibleComponents ↥Y \ {T}))ᶜ) :=
    U.isOpen.inter hOclosed.isOpen_compl
  obtain ⟨V, hVaff, hxV, hVle⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⟨(U : Set ↥Y) ∩ (⋃₀ (irreducibleComponents ↥Y \ {T}))ᶜ, hWopen⟩ : Y.Opens) from
      ⟨hxU, hxO⟩)
  have hVsub : (V : Set ↥Y) ⊆ ((U : Set ↥Y) ∩ (⋃₀ (irreducibleComponents ↥Y \ {T}))ᶜ) := hVle
  have hVU : V ≤ U := fun z hz => (hVsub hz).1
  have hVdisj : ∀ z : ↥Y, z ∈ V → z ∉ (⋃₀ (irreducibleComponents ↥Y \ {T})) :=
    fun z hz => (hVsub hz).2
  have hKV : restrictIdeal K V = (ch.restrict hVU).coordIdeal S :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU ch K S hKU
  have : IsAffine V.toScheme := hVaff
  have haffineTop : IsAffineOpen (⊤ : V.toScheme.Opens) := isAffineOpen_top V.toScheme
  have hEt : Etale ((⊤ : V.toScheme.Opens).ι ≫ (ch.restrict hVU).map) := by
    have : Etale (ch.restrict hVU).map := (ch.restrict hVU).isEtale
    infer_instance
  have hmemV : ∀ y : ↥V.toScheme, (V.ι).base y ∈ V := by
    intro y
    have h : ((V.ι).base y) ∈ (V : Set ↥Y) := by
      rw [← Scheme.Opens.range_ι V]
      exact ⟨y, rfl⟩
    exact h
  have hsupp : ∀ y : ↥V.toScheme,
      y ∈ ((ch.restrict hVU).coordIdeal ({j} : Finset (Fin m))).support := by
    intro y
    have hyV : (V.ι).base y ∈ V := hmemV y
    have hyT : (V.ι).base y ∈ T := hOsub _ (hVdisj _ hyV)
    have hmem : (V.ι).base y ∈ (K.support : Set ↥Y) := hTsub hyT
    have h2 : y ∈ ((K.comap V.ι).support : Set ↥V.toScheme) := by
      rw [support_comap_eq V.ι K]
      exact hmem
    have h3 : y ∈ ((ch.restrict hVU).coordIdeal S).support := by
      rw [← hKV, restrictIdeal_eq_comap_ι]
      exact h2
    rw [← one_le_orderAt_iff_mem_support] at h3 ⊢
    exact le_trans h3 (orderAt_le_of_le
      ((ch.restrict hVU).coordIdeal_mono (Finset.singleton_subset_iff.mpr hjS)) y)
  have y₀ : ↥V.toScheme := (⟨x, hxV⟩ : ↥V)
  exact false_of_forall_mem_support_of_coordIdeal_singleton_consolidated411 (V.ι ≫ q) haffineTop (chartOnOpenSubscheme_consolidated411 (ch.restrict hVU) hEt) j
    ((ch.restrict hVU).coordIdeal ({j} : Finset (Fin m)))
    (restrictIdeal_top_coordIdeal_consolidated411 (ch.restrict hVU) hEt ({j} : Finset (Fin m))) hsupp y₀

namespace MaximalContactCover

variable {X X' : Scheme.{u}} {k : Type u} [Field k] {p : X' ⟶ Spec (CommRingCat.of k)}
  {τ : X ⟶ X'} {I : X.IdealSheafData} {c : ℕ}

abbrev hypersurfaceScheme (C : MaximalContactCover p τ I c) : Scheme.{u} :=
  C.toCoverData.iInfImageIdeal.subscheme

abbrev hypersurfaceStructureMap (C : MaximalContactCover p τ I c) :
    C.hypersurfaceScheme ⟶ Spec (CommRingCat.of k) :=
  C.toCoverData.iInfImageIdeal.subschemeι ≫ C.projection ≫ p

section
variable (C : MaximalContactCover p τ I c)

theorem smooth_hypersurfaceStructureMap :
    Smooth C.hypersurfaceStructureMap :=
  ((isSmoothDivisor_iff (C.projection ≫ p) C.toCoverData.iInfImageIdeal).mp
    C.isSmoothDivisor_iInfImageIdeal).2

theorem isAffine_hypersurfaceScheme : IsAffine C.hypersurfaceScheme := by
  have : IsAffine C.toCoverData.disjointUnion := C.isAffine_disjointUnion
  exact isAffine_of_isAffineHom C.toCoverData.iInfImageIdeal.subschemeι


end

instance instIsAffineHypScheme (C : MaximalContactCover p τ I c) : IsAffine C.hypersurfaceScheme :=
  C.isAffine_hypersurfaceScheme

theorem isAffine_pullbackFiber (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    IsAffine C.pullbackFiber := by
  have : IsAffine C.toCoverData.disjointUnion := C.isAffine_disjointUnion
  have := C.isClosedImmersion_pullbackFiberToTotal
  exact isAffine_of_isAffineHom C.pullbackFiberToTotal

instance instIsAffineStarFiber (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    IsAffine C.pullbackFiber :=
  C.isAffine_pullbackFiber

section
variable (C : MaximalContactCover p τ I c)

theorem nonzeroOnComponents_iInfImageIdeal [TopologicalSpace.NoetherianSpace ↥C.toCoverData.disjointUnion] :
    NonzeroOnComponents C.toCoverData.iInfImageIdeal := by
  refine nonzeroOnComponents_of_locally_eq_coordIdeal (C.projection ≫ p) C.toCoverData.iInfImageIdeal
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents ?_
  intro y hy
  obtain ⟨i, hi⟩ := C.toCoverData.exists_mem_summandOpen y
  rcases C.hypersurface i with htop | ⟨n, ch, j, hch⟩
  · exfalso
    have h1 : restrictIdeal C.toCoverData.iInfImageIdeal (C.toCoverData.summandOpen i) = ⊤ := by
      rw [MaxContactReduction.FiniteOpenCoverWithIdeals.restrictIdeal_iInfImageIdeal_summandOpen, htop]
      simp
    exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top _ _ h1 y hi hy
  · refine ⟨C.toCoverData.summandOpen i, hi, n, C.toCoverData.summandEtaleChart i ch, {j},
      ⟨j, Finset.mem_singleton_self j⟩, ?_⟩
    rw [MaxContactReduction.FiniteOpenCoverWithIdeals.restrictIdeal_iInfImageIdeal_summandOpen, hch,
      MaxContactReduction.FiniteOpenCoverWithIdeals.summandEtaleChart_coordIdeal]

theorem ker_pullbackFiberToHypersurface_le_idealOnHypersurface [IsClosedImmersion τ] :
    Scheme.Hom.ker C.pullbackFiberToHypersurface ≤ C.idealOnHypersurface := by
  rw [C.idealOnHypersurface_eq_imageIdealSheaf]
  exact ker_le_map_idealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase)

theorem support_idealOnHypersurface_subset_support_ker [IsClosedImmersion τ] :
    (C.idealOnHypersurface.support : Set ↥C.hypersurfaceScheme) ⊆
      ((Scheme.Hom.ker C.pullbackFiberToHypersurface).support : Set ↥C.hypersurfaceScheme) := by
  intro x hx
  have hx' : x ∈ C.idealOnHypersurface.support := hx
  rw [mem_support_iff_stalkIdeal_ne_top] at hx'
  show x ∈ (Scheme.Hom.ker C.pullbackFiberToHypersurface).support
  rw [mem_support_iff_stalkIdeal_ne_top]
  intro hker
  have h1 := stalkIdeal_mono (ker_pullbackFiberToHypersurface_le_idealOnHypersurface C) x
  rw [hker, top_le_iff] at h1
  exact hx' h1


end

section
variable (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] [TopologicalSpace.NoetherianSpace ↥C.hypersurfaceScheme] (hloc : ∀ x : ↥C.pullbackFiber, ∃ (W : C.hypersurfaceScheme.Opens) (_ : C.pullbackFiberToHypersurface.base x ∈ W) (m : ℕ) (ch : EtaleChart C.hypersurfaceStructureMap W m) (S : Finset (Fin m)), S.Nonempty ∧ restrictIdeal (Scheme.Hom.ker C.pullbackFiberToHypersurface) W = ch.coordIdeal S)
include hloc

theorem nonzeroOnComponents_ker_pullbackFiberToHypersurface :
    NonzeroOnComponents (Scheme.Hom.ker C.pullbackFiberToHypersurface) := by
  refine nonzeroOnComponents_of_locally_eq_coordIdeal C.hypersurfaceStructureMap (Scheme.Hom.ker C.pullbackFiberToHypersurface)
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents ?_
  intro y hy
  obtain ⟨x, hx⟩ : ∃ x : ↥C.pullbackFiber, C.pullbackFiberToHypersurface.base x = y := by
    have hr : ((Scheme.Hom.ker C.pullbackFiberToHypersurface).support : Set ↥C.hypersurfaceScheme)
        = Set.range (⇑C.pullbackFiberToHypersurface) := by
      rw [Scheme.Hom.support_ker]
      exact (AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding
        C.pullbackFiberToHypersurface).isClosed_range.closure_eq
    have hy' : y ∈ Set.range (⇑C.pullbackFiberToHypersurface) := by
      rw [← hr]; exact hy
    exact hy'
  obtain ⟨W, hW, m, ch, S, hS, hres⟩ := hloc x
  exact ⟨W, hx ▸ hW, m, ch, S, hS, hres⟩

theorem nonzeroOnComponents_idealOnHypersurface :
    NonzeroOnComponents C.idealOnHypersurface := by
  have hker := C.nonzeroOnComponents_ker_pullbackFiberToHypersurface hloc
  rw [nonzeroOnComponents_iff] at hker ⊢
  intro T hT hTsub
  exact hker T hT (hTsub.trans (C.support_idealOnHypersurface_subset_support_ker))


end

theorem krullDimSucc_hypersurfaceScheme_lt (C : MaximalContactCover p τ I c)
    [LocallyOfFiniteType p]
    [TopologicalSpace.NoetherianSpace ↥C.toCoverData.disjointUnion]
    [Nonempty ↥C.hypersurfaceScheme] :
    krullDimSucc C.hypersurfaceScheme < krullDimSucc C.toCoverData.disjointUnion := by
  have : LocallyOfFiniteType (C.projection ≫ p) := C.locallyOfFiniteType_projection_comp
  have : QuasiCompact (C.projection ≫ p) := C.quasiCompact_projection_comp
  have hker : NonzeroOnComponents (Scheme.Hom.ker C.toCoverData.iInfImageIdeal.subschemeι) := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact C.nonzeroOnComponents_iInfImageIdeal
  exact krullDimSucc_lt_of_isClosedImmersion_of_nonzeroOnComponents (C.projection ≫ p)
    C.toCoverData.iInfImageIdeal.subschemeι hker

end MaximalContactCover


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverDescent
section

open TopologicalSpace


variable {A B C : Scheme.{u}}

def rangeOpens (γ : A ⟶ B) (W : A.Opens) (h : IsOpenImmersion (W.ι ≫ γ)) : B.Opens :=
  ⟨Set.range ⇑(W.ι ≫ γ).base, by
    have := h
    exact IsOpenImmersion.isOpen_range _⟩

section
variable (γ : A ⟶ B) (W : A.Opens) (h : IsOpenImmersion (W.ι ≫ γ))

theorem mem_rangeOpens_iff (b : ↥B) : b ∈ rangeOpens γ W h ↔ ∃ w : W.toScheme, (W.ι ≫ γ).base w = b :=
  Iff.rfl

theorem range_ι_comp_eq_range_rangeOpens_ι :
    Set.range ⇑(W.ι ≫ γ).base = Set.range ⇑(rangeOpens γ W h).ι.base :=
  (Scheme.Opens.range_ι (rangeOpens γ W h)).symm


end

noncomputable def isoRangeOpens (γ : A ⟶ B) (W : A.Opens) (h : IsOpenImmersion (W.ι ≫ γ)) :
    W.toScheme ≅ (rangeOpens γ W h).toScheme :=
  letI : IsOpenImmersion (W.ι ≫ γ) := h
  IsOpenImmersion.isoOfRangeEq (W.ι ≫ γ) (rangeOpens γ W h).ι (range_ι_comp_eq_range_rangeOpens_ι γ W h)

section
variable (γ : A ⟶ B) (W : A.Opens) (h : IsOpenImmersion (W.ι ≫ γ))

theorem isoRangeOpens_hom_ι :
    (isoRangeOpens γ W h).hom ≫ (rangeOpens γ W h).ι = W.ι ≫ γ := by
  have : IsOpenImmersion (W.ι ≫ γ) := h
  have hsub : Set.range ⇑(W.ι ≫ γ).base ⊆ Set.range ⇑(rangeOpens γ W h).ι.base := by
    intro x hx
    rw [← range_ι_comp_eq_range_rangeOpens_ι γ W h]
    exact hx
  exact IsOpenImmersion.lift_fac (rangeOpens γ W h).ι (W.ι ≫ γ) hsub

theorem isoRangeOpens_inv_comp :
    (isoRangeOpens γ W h).inv ≫ W.ι ≫ γ = (rangeOpens γ W h).ι := by
  have : IsOpenImmersion (W.ι ≫ γ) := h
  show (IsOpenImmersion.isoOfRangeEq (W.ι ≫ γ) (rangeOpens γ W h).ι
      (range_ι_comp_eq_range_rangeOpens_ι γ W h)).inv ≫ W.ι ≫ γ = (rangeOpens γ W h).ι
  simp

theorem isoRangeOpens_hom_ι_assoc (f : B ⟶ C) :
    (isoRangeOpens γ W h).hom ≫ (rangeOpens γ W h).ι ≫ f = W.ι ≫ γ ≫ f := by
  rw [← Category.assoc, isoRangeOpens_hom_ι, Category.assoc]

theorem isoRangeOpens_inv_comp_assoc (f : B ⟶ C) :
    (isoRangeOpens γ W h).inv ≫ W.ι ≫ γ ≫ f = (rangeOpens γ W h).ι ≫ f := by
  have key : (isoRangeOpens γ W h).inv ≫ W.ι ≫ γ = (rangeOpens γ W h).ι := by
    rw [← isoRangeOpens_hom_ι γ W h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hassoc : (isoRangeOpens γ W h).inv ≫ W.ι ≫ γ ≫ f
      = ((isoRangeOpens γ W h).inv ≫ W.ι ≫ γ) ≫ f := by
    simp only [Category.assoc]
  rw [hassoc, key]


end

theorem exists_mem_rangeOpens (γ : A ⟶ B)
    (hγ : MaxContactFunctoriality.IsLocalIsomorphism γ) [AlgebraicGeometry.Surjective γ]
    (b : ↥B) :
    ∃ (U : A.Opens) (hU : IsOpenImmersion (U.ι ≫ γ)), b ∈ rangeOpens γ U hU := by
  obtain ⟨a, ha⟩ := AlgebraicGeometry.Surjective.surj (f := γ) b
  obtain ⟨U, haU, hU⟩ := hγ a
  have hmem : a ∈ Set.range ⇑U.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact haU
  obtain ⟨w, hw⟩ := hmem
  refine ⟨U, hU, (mem_rangeOpens_iff γ U hU b).mpr ⟨w, ?_⟩⟩
  have h1 : (U.ι ≫ γ).base w = γ.base (U.ι.base w) := by simp
  rw [h1, hw, ha]

private theorem le_of_map_le_of_leftInverse_consolidated348 {R S : Type u} [CommRing R] [CommRing S]
    (ψ : R →+* S) (ψ' : S →+* R) (hinv : ∀ x, ψ' (ψ x) = x) {A C : Ideal R}
    (hle : A.map ψ ≤ C.map ψ) : A ≤ C := by
  intro a ha
  have h1 : ψ a ∈ C.map ψ := hle (Ideal.mem_map_of_mem ψ ha)
  have h2 : ψ' (ψ a) ∈ (C.map ψ).map ψ' := Ideal.mem_map_of_mem ψ' h1
  rw [hinv a, Ideal.map_map] at h2
  have h3 : ψ'.comp ψ = RingHom.id R := RingHom.ext hinv
  rw [h3, Ideal.map_id] at h2
  exact h2

section
variable {X : Scheme.{u}}

private theorem span_eq_top_of_forall_mem_basicOpen_consolidated348 {V : X.Opens}
    (hV : IsAffineOpen V) (S : Set Γ(X, V))
    (hcov : ∀ x : ↥X, x ∈ V → ∃ f ∈ S, x ∈ X.basicOpen f) :
    Ideal.span S = ⊤ := by
  rw [← hV.iSup_basicOpen_eq_self_iff]
  refine le_antisymm (iSup_le fun f => X.basicOpen_le (f : Γ(X, V))) ?_
  intro x hx
  obtain ⟨f, hfS, hxf⟩ := hcov x hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hfS⟩, hxf⟩

private theorem comap_ι_le_comap_ι_of_le_consolidated348 {I J : X.IdealSheafData}
    {V W : X.Opens} (hVW : V ≤ W) (hIJ : I.comap W.ι ≤ J.comap W.ι) :
    I.comap V.ι ≤ J.comap V.ι := by
  have hsub : Set.range ⇑V.ι.base ⊆ Set.range ⇑W.ι.base := by
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact hVW
  have hfac : IsOpenImmersion.lift W.ι V.ι hsub ≫ W.ι = V.ι :=
    IsOpenImmersion.lift_fac W.ι V.ι hsub
  have h1 : (I.comap W.ι).comap (IsOpenImmersion.lift W.ι V.ι hsub) = I.comap V.ι := by
    rw [← Scheme.IdealSheafData.comap_comp, hfac]
  have h2 : (J.comap W.ι).comap (IsOpenImmersion.lift W.ι V.ι hsub) = J.comap V.ι := by
    rw [← Scheme.IdealSheafData.comap_comp, hfac]
  rw [← h1, ← h2]
  exact Scheme.IdealSheafData.comap_mono _ hIJ

private theorem ideal_le_ideal_of_comap_ι_le_consolidated348 {I J : X.IdealSheafData}
    (V : X.affineOpens)
    (hc : I.comap (V : X.Opens).ι ≤ J.comap (V : X.Opens).ι) :
    I.ideal V ≤ J.ideal V := by
  have : IsAffine (V : X.Opens).toScheme := V.2
  have haffine : IsAffineOpen ((V : X.Opens).ι ''ᵁ (⊤ : (V : X.Opens).toScheme.Opens)) := by
    rw [Scheme.Opens.ι_image_top]
    exact V.2
  have e : (⊤ : (V : X.Opens).toScheme.Opens)
      ≤ (V : X.Opens).ι ⁻¹ᵁ ((V : X.Opens).ι ''ᵁ (⊤ : (V : X.Opens).toScheme.Opens)) :=
    fun x hx => ⟨x, hx, rfl⟩
  have hV : V = (⟨(V : X.Opens).ι ''ᵁ (⊤ : (V : X.Opens).toScheme.Opens), haffine⟩ : X.affineOpens) :=
    Subtype.ext (Scheme.Opens.ι_image_top _).symm
  have hI := Scheme.IdealSheafData.comap_ideal_eq_map_appLE I (V : X.Opens).ι
      ⟨(V : X.Opens).ι ''ᵁ (⊤ : (V : X.Opens).toScheme.Opens), haffine⟩
      ⟨⊤, isAffineOpen_top (V : X.Opens).toScheme⟩ e
  have hJ := Scheme.IdealSheafData.comap_ideal_eq_map_appLE J (V : X.Opens).ι
      ⟨(V : X.Opens).ι ''ᵁ (⊤ : (V : X.Opens).toScheme.Opens), haffine⟩
      ⟨⊤, isAffineOpen_top (V : X.Opens).toScheme⟩ e
  have hle : (I.comap (V : X.Opens).ι).ideal ⟨⊤, isAffineOpen_top (V : X.Opens).toScheme⟩
      ≤ (J.comap (V : X.Opens).ι).ideal ⟨⊤, isAffineOpen_top (V : X.Opens).toScheme⟩ :=
    hc ⟨⊤, isAffineOpen_top (V : X.Opens).toScheme⟩
  rw [hI, hJ] at hle
  have happ : ((V : X.Opens).ι).appLE
        ((V : X.Opens).ι ''ᵁ (⊤ : (V : X.Opens).toScheme.Opens))
        (⊤ : (V : X.Opens).toScheme.Opens) e
      = (((V : X.Opens).ι).appIso (⊤ : (V : X.Opens).toScheme.Opens)).hom :=
    (Scheme.Hom.appIso_hom' _ _).symm
  rw [happ] at hle
  rw [hV]
  refine le_of_map_le_of_leftInverse_consolidated348 _
    ((((V : X.Opens).ι).appIso (⊤ : (V : X.Opens).toScheme.Opens)).inv.hom) ?_ hle
  intro x
  have hxx : ((V : X.Opens).ι.appIso (⊤ : (V : X.Opens).toScheme.Opens)).hom ≫
      ((V : X.Opens).ι.appIso (⊤ : (V : X.Opens).toScheme.Opens)).inv = 𝟙 _ :=
    Iso.hom_inv_id _
  have h2 : (((V : X.Opens).ι.appIso (⊤ : (V : X.Opens).toScheme.Opens)).hom ≫
      ((V : X.Opens).ι.appIso (⊤ : (V : X.Opens).toScheme.Opens)).inv).hom x = x := by
    rw [hxx]; simp
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  exact h2

private theorem exists_pow_smul_mem_of_map_mem_consolidated348 (V : X.affineOpens)
    (C : Ideal Γ(X, (V : X.Opens))) (f a : Γ(X, (V : X.Opens)))
    (hmem : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom a ∈
      Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom C) :
    ∃ n : ℕ, f ^ n • a ∈ C := by
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := V.2.isLocalization_basicOpen f
  have halg : (algebraMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen f))
      = (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom := rfl
  rw [← halg] at hmem
  rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f)] at hmem
  obtain ⟨⟨⟨c, hc⟩, ⟨m, hm⟩⟩, heq⟩ := hmem
  obtain ⟨k, hk⟩ := hm
  have hk' : f ^ k = m := hk
  have heq' : (algebraMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen f)) (a * m)
      = (algebraMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen f)) c := by
    simpa using heq
  obtain ⟨d, hd⟩ :=
    (IsLocalization.eq_iff_exists (Submonoid.powers f) Γ(X, X.basicOpen f)).mp heq'
  obtain ⟨j, hj⟩ := d.2
  have hj' : f ^ j = (d : Γ(X, (V : X.Opens))) := hj
  refine ⟨j + k, ?_⟩
  have hmul : f ^ (j + k) * a = (d : Γ(X, (V : X.Opens))) * c := by
    rw [pow_add, hj', hk', mul_assoc, mul_comm m a]
    exact hd
  rw [smul_eq_mul, hmul]
  exact Ideal.mul_mem_left _ _ hc


end

theorem le_of_forall_comap_ι_le {ι : Type v} (U : ι → B.Opens)
    (hU : ∀ b : ↥B, ∃ i, b ∈ U i) (J K : B.IdealSheafData)
    (h : ∀ i, J.comap (U i).ι ≤ K.comap (U i).ι) : J ≤ K := by
  show ∀ V : B.affineOpens, J.ideal V ≤ K.ideal V
  intro V a ha
  have hVaff : IsAffineOpen (V : B.Opens) := V.2
  have hspan : Ideal.span {f : Γ(B, (V : B.Opens)) | ∃ i, B.basicOpen f ≤ U i} = ⊤ := by
    refine span_eq_top_of_forall_mem_basicOpen_consolidated348 hVaff _ ?_
    intro x hx
    obtain ⟨i, hi⟩ := hU x
    obtain ⟨f, hfle, hxf⟩ :=
      AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le hVaff (⟨x, hi⟩ : ↥(U i)) hx
    exact ⟨f, ⟨i, hfle⟩, hxf⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (K.ideal V) _ hspan a ?_
  rintro ⟨f, i, hfle⟩
  have hcomap : J.comap (B.basicOpen f).ι ≤ K.comap (B.basicOpen f).ι :=
    comap_ι_le_comap_ι_of_le_consolidated348 hfle (h i)
  have hideal : J.ideal (B.affineBasicOpen f) ≤ K.ideal (B.affineBasicOpen f) :=
    ideal_le_ideal_of_comap_ι_le_consolidated348 (B.affineBasicOpen f) hcomap
  have ha' : (B.presheaf.map (homOfLE (B.basicOpen_le f)).op).hom a
      ∈ J.ideal (B.affineBasicOpen f) := by
    rw [← J.map_ideal_basicOpen V f]
    exact Ideal.mem_map_of_mem _ ha
  have ha'' := hideal ha'
  rw [← K.map_ideal_basicOpen V f] at ha''
  exact exists_pow_smul_mem_of_map_mem_consolidated348 V (K.ideal V) f a ha''

private theorem comap_inv_comap_hom_consolidated348 {X Y : Scheme.{u}} (e : X ≅ Y) (I : Y.IdealSheafData) :
    (I.comap e.hom).comap e.inv = I := by
  rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]

theorem le_of_comap_le (γ : A ⟶ B)
    (hγ : MaxContactFunctoriality.IsLocalIsomorphism γ) [AlgebraicGeometry.Surjective γ]
    (J K : B.IdealSheafData) (h : J.comap γ ≤ K.comap γ) : J ≤ K := by
  refine le_of_forall_comap_ι_le
    (fun p : { U : A.Opens // IsOpenImmersion (U.ι ≫ γ) } => rangeOpens γ p.1 p.2) ?_ J K ?_
  · intro b
    obtain ⟨U, hU, hb⟩ := exists_mem_rangeOpens γ hγ b
    exact ⟨⟨U, hU⟩, hb⟩
  · rintro ⟨W, hW⟩
    show J.comap (rangeOpens γ W hW).ι ≤ K.comap (rangeOpens γ W hW).ι
    have key : ∀ L : B.IdealSheafData,
        (L.comap (rangeOpens γ W hW).ι).comap (isoRangeOpens γ W hW).hom
          = (L.comap γ).comap W.ι := by
      intro L
      rw [← Scheme.IdealSheafData.comap_comp, isoRangeOpens_hom_ι,
        ← Scheme.IdealSheafData.comap_comp]
    have h1 : (J.comap (rangeOpens γ W hW).ι).comap (isoRangeOpens γ W hW).hom
        ≤ (K.comap (rangeOpens γ W hW).ι).comap (isoRangeOpens γ W hW).hom := by
      rw [key J, key K]
      exact Scheme.IdealSheafData.comap_mono W.ι h
    have h2 : ((J.comap (rangeOpens γ W hW).ι).comap (isoRangeOpens γ W hW).hom).comap
          (isoRangeOpens γ W hW).inv
        ≤ ((K.comap (rangeOpens γ W hW).ι).comap (isoRangeOpens γ W hW).hom).comap
          (isoRangeOpens γ W hW).inv :=
      Scheme.IdealSheafData.comap_mono (isoRangeOpens γ W hW).inv h1
    rwa [comap_inv_comap_hom_consolidated348, comap_inv_comap_hom_consolidated348] at h2

private theorem smooth_ι_comp_consolidated348 {X Y : Scheme.{u}} (U : X.Opens) (g : X ⟶ Y)
    (hg : Smooth g) : Smooth (U.ι ≫ g) := by
  have : Smooth g := hg
  infer_instance

private theorem smooth_of_smooth_iso_hom_comp_consolidated348 {X Y Z : Scheme.{u}} (e : X ≅ Y) (k : Y ⟶ Z)
    (hk : Smooth (e.hom ≫ k)) : Smooth k := by
  have : Smooth (e.hom ≫ k) := hk
  have h2 : Smooth (e.inv ≫ e.hom ≫ k) := inferInstance
  rwa [← Category.assoc, e.inv_hom_id, Category.id_comp] at h2

theorem smooth_of_smooth_comp_of_isLocalIsomorphism {S : Scheme.{u}} (γ : A ⟶ B) (f : B ⟶ S)
    [IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{u})]
    [AlgebraicGeometry.Surjective γ]
    (hγ : MaxContactFunctoriality.IsLocalIsomorphism γ)
    (h : Smooth (γ ≫ f)) : Smooth f := by
  choose U hU hmem using fun b : ↥B => exists_mem_rangeOpens γ hγ b
  have htop : (⨆ b : ↥B, rangeOpens γ (U b) (hU b)) = ⊤ := by
    refine le_antisymm le_top ?_
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hmem x⟩
  have hsm : ∀ b : ↥B, Smooth ((rangeOpens γ (U b) (hU b)).ι ≫ f) := by
    intro b
    refine smooth_of_smooth_iso_hom_comp_consolidated348 (isoRangeOpens γ (U b) (hU b))
      ((rangeOpens γ (U b) (hU b)).ι ≫ f) ?_
    rw [isoRangeOpens_hom_ι_assoc γ (U b) (hU b) f]
    exact smooth_ι_comp_consolidated348 (U b) (γ ≫ f) h
  exact IsZariskiLocalAtSource.of_iSup_eq_top _ htop hsm

private theorem isLocalIsomorphism_pullback_snd_consolidated348 {X Y W : Scheme.{u}} (g : X ⟶ Y)
    (hg : MaxContactFunctoriality.IsLocalIsomorphism g) (t : W ⟶ Y) :
    MaxContactFunctoriality.IsLocalIsomorphism (Limits.pullback.snd g t) := by
  intro x
  obtain ⟨V, hxV, hV⟩ := hg ((Limits.pullback.fst g t).base x)
  have : IsOpenImmersion (V.ι ≫ g) := hV
  refine ⟨(Limits.pullback.fst g t) ⁻¹ᵁ V, hxV, ?_⟩
  have hsq : CategoryTheory.IsPullback
      (Limits.pullback.fst g t ∣_ V)
      (((Limits.pullback.fst g t) ⁻¹ᵁ V).ι ≫ Limits.pullback.snd g t)
      (V.ι ≫ g) t :=
    (AlgebraicGeometry.isPullback_morphismRestrict (Limits.pullback.fst g t) V).paste_vert
      (CategoryTheory.IsPullback.of_hasPullback g t)
  rw [← hsq.isoPullback_hom_snd]
  infer_instance

theorem smooth_subschemeι_comp_of_smooth_comap_comp {S : Scheme.{u}} (γ : A ⟶ B) (f : B ⟶ S)
    (Z : B.IdealSheafData)
    [IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{u})]
    [AlgebraicGeometry.Surjective γ]
    (hγ : MaxContactFunctoriality.IsLocalIsomorphism γ)
    (h : Smooth ((Z.comap γ).subschemeι ≫ γ ≫ f)) :
    Smooth (Z.subschemeι ≫ f) := by
  have h1 : Smooth (Limits.pullback.fst γ Z.subschemeι ≫ γ ≫ f) := by
    refine smooth_of_smooth_iso_hom_comp_consolidated348 (Z.comapIso γ)
      (Limits.pullback.fst γ Z.subschemeι ≫ γ ≫ f) ?_
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst Z γ]
    exact h
  have h2 : Smooth
      (Limits.pullback.snd γ Z.subschemeι ≫ Z.subschemeι ≫ f) := by
    rw [← Category.assoc, ← Limits.pullback.condition, Category.assoc]
    exact h1
  exact smooth_of_smooth_comp_of_isLocalIsomorphism (Limits.pullback.snd γ Z.subschemeι) (Z.subschemeι ≫ f)
    (isLocalIsomorphism_pullback_snd_consolidated348 γ hγ Z.subschemeι) h2

section
variable {X Y : Scheme.{u}} {k : Type u} [Field k] (q : Y ⟶ Spec (CommRingCat.of k)) (γ : X ⟶ Y) {V W : X.Opens} (hWV : W ≤ V) (hW : IsOpenImmersion (W.ι ≫ γ)) {m : ℕ} (c : EtaleChart (γ ≫ q) V m)

private theorem isoRangeOpens_inv_comp_map_comp_affineSpaceFinToSpec_consolidated348 :
    ((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV ≫ c.map) ≫ affineSpaceFinToSpec k m
      = (rangeOpens γ W hW).ι ≫ q := by
  have h1 : (X.homOfLE hWV ≫ c.map) ≫ affineSpaceFinToSpec k m = W.ι ≫ γ ≫ q := by
    calc (X.homOfLE hWV ≫ c.map) ≫ affineSpaceFinToSpec k m
        = X.homOfLE hWV ≫ c.map ≫ affineSpaceFinToSpec k m := Category.assoc _ _ _
      _ = X.homOfLE hWV ≫ V.ι ≫ γ ≫ q := by rw [c.comp_struct]
      _ = (X.homOfLE hWV ≫ V.ι) ≫ γ ≫ q := (Category.assoc _ _ _).symm
      _ = W.ι ≫ γ ≫ q := by rw [Scheme.homOfLE_ι]
  calc ((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV ≫ c.map) ≫ affineSpaceFinToSpec k m
      = (isoRangeOpens γ W hW).inv ≫ (X.homOfLE hWV ≫ c.map) ≫ affineSpaceFinToSpec k m := by
        simp only [Category.assoc]
    _ = (isoRangeOpens γ W hW).inv ≫ W.ι ≫ γ ≫ q := by rw [h1]
    _ = (rangeOpens γ W hW).ι ≫ q := isoRangeOpens_inv_comp_assoc γ W hW q

private theorem etale_isoRangeOpens_inv_comp_map_consolidated348 :
    Etale ((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV ≫ c.map) := by
  have : Etale c.map := c.isEtale
  have : IsOpenImmersion (isoRangeOpens γ W hW).inv := inferInstance
  infer_instance


end

private noncomputable def etaleChartOnRangeOpens {X Y : Scheme.{u}} {k : Type u} [Field k]
    (q : Y ⟶ Spec (CommRingCat.of k)) (γ : X ⟶ Y) {V W : X.Opens} (hWV : W ≤ V)
    (hW : IsOpenImmersion (W.ι ≫ γ)) {m : ℕ} (c : EtaleChart (γ ≫ q) V m) :
    EtaleChart q (rangeOpens γ W hW) m where
  map := (isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV ≫ c.map
  comp_struct := isoRangeOpens_inv_comp_map_comp_affineSpaceFinToSpec_consolidated348 q γ hWV hW c
  isEtale := etale_isoRangeOpens_inv_comp_map_consolidated348 q γ hWV hW c

section
variable {X Y : Scheme.{u}}

private theorem coordIdeal_etaleChartOnRangeOpens_consolidated348 {k : Type u} [Field k]
    (q : Y ⟶ Spec (CommRingCat.of k)) (γ : X ⟶ Y) {V W : X.Opens} (hWV : W ≤ V)
    (hW : IsOpenImmersion (W.ι ≫ γ)) {m : ℕ} (c : EtaleChart (γ ≫ q) V m)
    (T : Finset (Fin m)) :
    (etaleChartOnRangeOpens q γ hWV hW c).coordIdeal T
      = ((c.coordIdeal T).comap (X.homOfLE hWV)).comap (isoRangeOpens γ W hW).inv := by
  have e1 : ((c.coordIdeal T).comap (X.homOfLE hWV)).comap (isoRangeOpens γ W hW).inv
      = (c.coordIdeal T).comap ((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) := by
    rw [← Scheme.IdealSheafData.comap_comp]
  have e2 : (c.coordIdeal T).comap ((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV)
      = (coordSubspaceIdeal k m T).comap
          (((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) ≫ c.map) := by
    rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, ← Scheme.IdealSheafData.comap_comp]
  have e3 : (coordSubspaceIdeal k m T).comap
        (((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) ≫ c.map)
      = (etaleChartOnRangeOpens q γ hWV hW c).coordIdeal T :=
    congrArg (fun g => (coordSubspaceIdeal k m T).comap g)
      (Category.assoc (isoRangeOpens γ W hW).inv (X.homOfLE hWV) c.map)
  exact ((e1.trans e2).trans e3).symm

private theorem restrictIdeal_rangeOpens_consolidated348 (γ : X ⟶ Y) {V W : X.Opens}
    (hWV : W ≤ V) (hW : IsOpenImmersion (W.ι ≫ γ)) (J : Y.IdealSheafData) :
    restrictIdeal J (rangeOpens γ W hW)
      = ((restrictIdeal (J.comap γ) V).comap (X.homOfLE hWV)).comap
          (isoRangeOpens γ W hW).inv := by
  have hcomp : (((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) ≫ V.ι) ≫ γ
      = (rangeOpens γ W hW).ι := by
    calc (((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) ≫ V.ι) ≫ γ
        = (isoRangeOpens γ W hW).inv ≫ (X.homOfLE hWV ≫ V.ι) ≫ γ := by
          simp only [Category.assoc]
      _ = (isoRangeOpens γ W hW).inv ≫ W.ι ≫ γ := by rw [Scheme.homOfLE_ι]
      _ = (rangeOpens γ W hW).ι := isoRangeOpens_inv_comp γ W hW
  have e1 : (((J.comap γ).comap V.ι).comap (X.homOfLE hWV)).comap (isoRangeOpens γ W hW).inv
      = ((J.comap γ).comap V.ι).comap ((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) := by
    rw [← Scheme.IdealSheafData.comap_comp]
  have e2 : ((J.comap γ).comap V.ι).comap ((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV)
      = (J.comap γ).comap (((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) ≫ V.ι) := by
    rw [← Scheme.IdealSheafData.comap_comp]
  have e3 : (J.comap γ).comap (((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) ≫ V.ι)
      = J.comap ((((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) ≫ V.ι) ≫ γ) := by
    rw [← Scheme.IdealSheafData.comap_comp]
  have e4 : J.comap ((((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) ≫ V.ι) ≫ γ)
      = J.comap (rangeOpens γ W hW).ι := by rw [hcomp]
  show J.comap (rangeOpens γ W hW).ι
      = (((J.comap γ).comap V.ι).comap (X.homOfLE hWV)).comap (isoRangeOpens γ W hW).inv
  exact ((e1.trans e2).trans (e3.trans e4)).symm


end

section
variable {k : Type u} [Field k]

theorem hasStrictNormalCrossingsWith_of_comap (p : B ⟶ Spec (CommRingCat.of k))
    (γ : A ⟶ B) [AlgebraicGeometry.Surjective γ]
    (hγ : MaxContactFunctoriality.IsLocalIsomorphism γ)
    (Z : B.IdealSheafData) (L : List B.IdealSheafData)
    (h : HasStrictNormalCrossingsWith (γ ≫ p) (Z.comap γ) (L.map (fun D => D.comap γ))) :
    HasStrictNormalCrossingsWith p Z L := by
  intro x hx
  obtain ⟨a, ha⟩ := AlgebraicGeometry.Surjective.surj (f := γ) x
  have haZ : a ∈ (Z.comap γ).support := by
    rw [← one_le_orderAt_iff_mem_support]
    refine le_trans ?_ (orderAt_le_orderAt_comap γ Z a)
    rw [ha]
    exact (one_le_orderAt_iff_mem_support Z x).mpr hx
  obtain ⟨V, haV, m, c, af, S, hinj, hnone, hsome, hZV⟩ := h a haZ
  obtain ⟨U0, haU0, hU0⟩ := hγ a
  have hU0γ : IsOpenImmersion (U0.ι ≫ γ) := hU0
  have hWV : V ⊓ U0 ≤ V := inf_le_left
  have hWU : V ⊓ U0 ≤ U0 := inf_le_right
  have haW : a ∈ V ⊓ U0 := ⟨haV, haU0⟩
  have hWι : (V ⊓ U0).ι ≫ γ = A.homOfLE hWU ≫ U0.ι ≫ γ := by
    calc (V ⊓ U0).ι ≫ γ = (A.homOfLE hWU ≫ U0.ι) ≫ γ := by rw [Scheme.homOfLE_ι]
      _ = A.homOfLE hWU ≫ U0.ι ≫ γ := Category.assoc _ _ _
  have hW : IsOpenImmersion ((V ⊓ U0).ι ≫ γ) := by
    rw [hWι]
    infer_instance
  have hmem : a ∈ Set.range ⇑(V ⊓ U0).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact haW
  obtain ⟨w, hw⟩ := hmem
  have hxP : x ∈ rangeOpens γ (V ⊓ U0) hW := by
    refine (mem_rangeOpens_iff γ (V ⊓ U0) hW x).mpr ⟨w, ?_⟩
    have hc : ((V ⊓ U0).ι ≫ γ).base w = γ.base ((V ⊓ U0).ι.base w) := by simp
    rw [hc, hw, ha]
  have hlen : (L.map (fun D => D.comap γ)).length = L.length := by simp
  refine ⟨rangeOpens γ (V ⊓ U0) hW, hxP, m, etaleChartOnRangeOpens p γ hWV hW c, af, S,
    ?_, ?_, ?_, ?_⟩
  · intro i hi j hj t hti htj
    exact hinj i (by rw [hlen]; exact hi) j (by rw [hlen]; exact hj) t hti htj
  · intro i hi hni
    have hi' : i < (L.map (fun D => D.comap γ)).length := by rw [hlen]; exact hi
    have h2 : (L.map (fun D => D.comap γ))[i]'hi' = (L[i]'hi).comap γ := by simp
    have h1 := hnone i hi' hni
    rw [h2] at h1
    rw [restrictIdeal_rangeOpens_consolidated348 γ hWV hW (L[i]'hi), h1, Scheme.IdealSheafData.comap_top,
      Scheme.IdealSheafData.comap_top]
  · intro i hi t hti
    have hi' : i < (L.map (fun D => D.comap γ)).length := by rw [hlen]; exact hi
    have h2 : (L.map (fun D => D.comap γ))[i]'hi' = (L[i]'hi).comap γ := by simp
    have h1 := hsome i hi' t hti
    rw [h2] at h1
    rw [restrictIdeal_rangeOpens_consolidated348 γ hWV hW (L[i]'hi), h1, coordIdeal_etaleChartOnRangeOpens_consolidated348]
  · rw [restrictIdeal_rangeOpens_consolidated348 γ hWV hW Z, hZV, coordIdeal_etaleChartOnRangeOpens_consolidated348]

private theorem smooth_markedBlowupSequenceData_projectionToBase_comp_consolidated348 {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} [Smooth p]
    (t : MarkedBlowupSequenceData p I m E) :
    ∀ i : ℕ, i ≤ t.length → Smooth (t.proj i ≫ p) := by
  intro i
  induction i with
  | zero =>
      intro _
      rw [t.proj_zero]
      infer_instance
  | succ j ih =>
      intro hi
      have hj : j < t.length := hi
      have := ih (le_of_lt hj)
      have he : t.proj (j + 1) ≫ p = t.map j ≫ t.proj j ≫ p := by
        rw [t.proj_succ j, Category.assoc]
      rw [he]
      exact smooth_comp_of_isBlowupAlongIdealSheaf (t.center_snc j hj) (t.isBlowup j hj)

private theorem strictPullbackComparisonMap_comp_projectionToBase_consolidated348 {X X' : Scheme.{u}}
    {q : X' ⟶ Spec (CommRingCat.of k)} {g : X' ⟶ X} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} {d : BlowupSequenceData X}
    (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups) :
    ∀ (i : ℕ) (hi : i ≤ t.length), t.strictPullbackComparisonMap D i hi ≫ d.projectionToBase i = t.proj i ≫ g := by
  intro i
  induction i with
  | zero =>
      intro hi
      rw [BlowupSequenceData.projectionToBase_zero, t.proj_zero]
      exact t.strictPullbackComparisonMap_zero D
  | succ j ih =>
      intro hi
      have hj : j < t.length := hi
      have h1 : t.strictPullbackComparisonMap D (j + 1) hi ≫ d.map j = t.map j ≫ t.strictPullbackComparisonMap D j (le_of_lt hj) :=
        t.strictPullbackComparisonMap_comp_blowupMorphism D j hj
      have h2 : t.strictPullbackComparisonMap D j (le_of_lt hj) ≫ d.projectionToBase j = t.proj j ≫ g := ih (le_of_lt hj)
      calc t.strictPullbackComparisonMap D (j + 1) hi ≫ d.projectionToBase (j + 1)
          = t.strictPullbackComparisonMap D (j + 1) hi ≫ d.map j ≫ d.projectionToBase j := by rw [BlowupSequenceData.projectionToBase_succ]
        _ = (t.strictPullbackComparisonMap D (j + 1) hi ≫ d.map j) ≫ d.projectionToBase j := (Category.assoc _ _ _).symm
        _ = (t.map j ≫ t.strictPullbackComparisonMap D j (le_of_lt hj)) ≫ d.projectionToBase j := by rw [h1]
        _ = t.map j ≫ t.strictPullbackComparisonMap D j (le_of_lt hj) ≫ d.projectionToBase j := Category.assoc _ _ _
        _ = t.map j ≫ t.proj j ≫ g := by rw [h2]
        _ = (t.map j ≫ t.proj j) ≫ g := (Category.assoc _ _ _).symm
        _ = t.proj (j + 1) ≫ g := by rw [t.proj_succ j]


end

section
variable {k : Type u} [Field k] [CharZero k] {X X' : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {g : X' ⟶ X} [Smooth p] [Smooth g] [Flat g] [AlgebraicGeometry.Surjective g] {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} {d : BlowupSequenceData X} (t : MarkedBlowupSequenceData (g ≫ p) (I.comap g) m (E.map fun A => A.comap g)) (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)

private theorem controlledTransform_le_center_pow_consolidated348 (hcomp : ∀ (i : ℕ) (hi : i ≤ t.length),
      MaxContactFunctoriality.IsLocalIsomorphism (D.comp i (t.le_toSequenceOfBlowups_length hi)))
    (i : ℕ) (hi : i < t.length)
    (hmt : t.ideal i = (d.controlledTransform I m i).comap (t.strictPullbackComparisonMap D i (le_of_lt hi))) :
    d.controlledTransform I m i ≤ d.center i ^ m := by
  have : Smooth (t.proj i ≫ g ≫ p) := smooth_markedBlowupSequenceData_projectionToBase_comp_consolidated348 t i (le_of_lt hi)
  have hup : t.ideal i ≤ t.center i ^ m :=
    le_pow_of_hasStrictNormalCrossingsWith (t.proj i ≫ g ≫ p) (t.center i) (t.ideal i) (t.boundary i)
      (t.center_snc i hi) m (t.center_order i hi)
  have : AlgebraicGeometry.Surjective (t.strictPullbackComparisonMap D i (le_of_lt hi)) :=
    t.surjective_strictPullbackComparisonMap D i (le_of_lt hi)
  have hc : (d.center i).comap (t.strictPullbackComparisonMap D i (le_of_lt hi)) = t.center i :=
    (t.center_eq_comap_strictPullbackComparisonMap D i hi).symm
  refine le_of_comap_le (t.strictPullbackComparisonMap D i (le_of_lt hi)) (hcomp i (le_of_lt hi)) _ _ ?_
  calc (d.controlledTransform I m i).comap (t.strictPullbackComparisonMap D i (le_of_lt hi))
      = t.ideal i := hmt.symm
    _ ≤ t.center i ^ m := hup
    _ = ((d.center i).comap (t.strictPullbackComparisonMap D i (le_of_lt hi))) ^ m := by rw [hc]
    _ = (d.center i ^ m).comap (t.strictPullbackComparisonMap D i (le_of_lt hi)) :=
        (Scheme.IdealSheafData.comap_pow (d.center i) (t.strictPullbackComparisonMap D i (le_of_lt hi)) m).symm

private theorem ideal_eq_comap_controlledTransform_consolidated348 (hNd : ∀ i ≤ d.length, IsLocallyNoetherian (d.obj i))
    (hcomp : ∀ (i : ℕ) (hi : i ≤ t.length),
      MaxContactFunctoriality.IsLocalIsomorphism (D.comp i (t.le_toSequenceOfBlowups_length hi))) :
    ∀ (i : ℕ) (hi : i ≤ t.length),
      t.ideal i = (d.controlledTransform I m i).comap (t.strictPullbackComparisonMap D i hi) := by
  have hlen : t.length = d.length := t.length_eq_of_strictPullbackBlowupSeq D
  intro i
  induction i with
  | zero =>
      intro hi
      have h0 : t.strictPullbackComparisonMap D 0 hi ≫ d.isoZero.hom = t.isoZero.hom ≫ g := t.strictPullbackComparisonMap_zero D
      calc t.ideal 0 = (I.comap g).comap t.isoZero.hom := t.ideal_zero
        _ = I.comap (t.isoZero.hom ≫ g) := by rw [← Scheme.IdealSheafData.comap_comp]
        _ = I.comap (t.strictPullbackComparisonMap D 0 hi ≫ d.isoZero.hom) := by rw [h0]
        _ = (I.comap d.isoZero.hom).comap (t.strictPullbackComparisonMap D 0 hi) := by
              rw [Scheme.IdealSheafData.comap_comp]
        _ = (d.controlledTransform I m 0).comap (t.strictPullbackComparisonMap D 0 hi) := by rw [BlowupSequenceData.controlledTransform_zero]
  | succ j ih =>
      intro hi
      have hj : j < t.length := hi
      have hmj : t.ideal j = (d.controlledTransform I m j).comap (t.strictPullbackComparisonMap D j (le_of_lt hj)) :=
        ih (le_of_lt hj)
      have hle : d.controlledTransform I m j ≤ d.center j ^ m :=
        controlledTransform_le_center_pow_consolidated348 t D hcomp j hj hmj
      have hjd : j < d.length := by rw [← hlen]; exact hj
      have hjd1 : j + 1 ≤ d.length := hjd
      have : IsLocallyNoetherian (d.obj (j + 1)) := hNd (j + 1) hjd1
      obtain ⟨B, hB, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map j) (d.center j)
        (d.controlledTransform I m j) m (d.isBlowup j hjd) hle
      have hdivj : Blowup.exceptionalIdeal (d.map j) (d.center j) ^ m * d.controlledTransform I m (j + 1)
          = (d.controlledTransform I m j).comap (d.map j) := d.pow_exceptionalIdeal_mul_controlledTransform_succ I m j ⟨B, hB⟩
      have hcm : t.strictPullbackComparisonMap D (j + 1) hi ≫ d.map j = t.map j ≫ t.strictPullbackComparisonMap D j (le_of_lt hj) :=
        t.strictPullbackComparisonMap_comp_blowupMorphism D j hj
      have hexc : Blowup.exceptionalIdeal (t.map j) (t.center j)
          = (Blowup.exceptionalIdeal (d.map j) (d.center j)).comap (t.strictPullbackComparisonMap D (j + 1) hi) :=
        t.exceptionalIdeal_eq_comap_strictPullbackComparisonMap D j hj
      have key : Blowup.exceptionalIdeal (t.map j) (t.center j) ^ m * t.ideal (j + 1)
          = Blowup.exceptionalIdeal (t.map j) (t.center j) ^ m *
              (d.controlledTransform I m (j + 1)).comap (t.strictPullbackComparisonMap D (j + 1) hi) := by
        calc Blowup.exceptionalIdeal (t.map j) (t.center j) ^ m * t.ideal (j + 1)
            = (t.ideal j).comap (t.map j) := t.ideal_succ j hj
          _ = ((d.controlledTransform I m j).comap (t.strictPullbackComparisonMap D j (le_of_lt hj))).comap (t.map j) := by
              rw [hmj]
          _ = (d.controlledTransform I m j).comap (t.map j ≫ t.strictPullbackComparisonMap D j (le_of_lt hj)) := by
              rw [← Scheme.IdealSheafData.comap_comp]
          _ = (d.controlledTransform I m j).comap (t.strictPullbackComparisonMap D (j + 1) hi ≫ d.map j) := by rw [hcm]
          _ = ((d.controlledTransform I m j).comap (d.map j)).comap (t.strictPullbackComparisonMap D (j + 1) hi) := by
              rw [Scheme.IdealSheafData.comap_comp]
          _ = (Blowup.exceptionalIdeal (d.map j) (d.center j) ^ m *
                d.controlledTransform I m (j + 1)).comap (t.strictPullbackComparisonMap D (j + 1) hi) := by rw [hdivj]
          _ = (Blowup.exceptionalIdeal (d.map j) (d.center j) ^ m).comap (t.strictPullbackComparisonMap D (j + 1) hi) *
                (d.controlledTransform I m (j + 1)).comap (t.strictPullbackComparisonMap D (j + 1) hi) :=
              Scheme.IdealSheafData.comap_mul _ _ _
          _ = ((Blowup.exceptionalIdeal (d.map j) (d.center j)).comap (t.strictPullbackComparisonMap D (j + 1) hi)) ^ m *
                (d.controlledTransform I m (j + 1)).comap (t.strictPullbackComparisonMap D (j + 1) hi) := by
              rw [Scheme.IdealSheafData.comap_pow]
          _ = Blowup.exceptionalIdeal (t.map j) (t.center j) ^ m *
                (d.controlledTransform I m (j + 1)).comap (t.strictPullbackComparisonMap D (j + 1) hi) := by rw [hexc]
      exact eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul
        (isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal (t.isBlowup j hj)) m key


end

private theorem isMarked_of_strictPullbackBlowupSeq_consolidated348 {k : Type u} [Field k] [CharZero k]
    {X X' : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) (g : X' ⟶ X)
    [Smooth p] [Smooth g]
    [Flat g] [AlgebraicGeometry.Surjective g]
    [IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{u})]
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (d : BlowupSequenceData X)
    (t : MarkedBlowupSequenceData (g ≫ p) (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (hNd : ∀ i ≤ d.length, IsLocallyNoetherian (d.obj i))
    (hNt : ∀ i ≤ t.length, IsLocallyNoetherian (t.obj i))
    (hcomp : ∀ (i : ℕ) (hi : i ≤ t.length),
      MaxContactFunctoriality.IsLocalIsomorphism (D.comp i (t.le_toSequenceOfBlowups_length hi))) :
    d.IsMarked p I m E := by
  have hlen : t.length = d.length := t.length_eq_of_strictPullbackBlowupSeq D
  have hmatch : ∀ (i : ℕ) (hi : i ≤ t.length),
      t.ideal i = (d.controlledTransform I m i).comap (t.strictPullbackComparisonMap D i hi) :=
    ideal_eq_comap_controlledTransform_consolidated348 t D hNd hcomp
  have hle : ∀ i : ℕ, i < t.length → d.controlledTransform I m i ≤ d.center i ^ m := by
    intro i hi
    exact controlledTransform_le_center_pow_consolidated348 t D hcomp i hi (hmatch i (le_of_lt hi))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hid
    have hi : i < t.length := by rw [hlen]; exact hid
    have hid1 : i + 1 ≤ d.length := hid
    have : IsLocallyNoetherian (d.obj (i + 1)) := hNd (i + 1) hid1
    obtain ⟨B, hB, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map i) (d.center i)
      (d.controlledTransform I m i) m (d.isBlowup i hid) (hle i hi)
    exact ⟨B, hB⟩
  · intro i hid
    have hi : i < t.length := by rw [hlen]; exact hid
    exact support_subset_orderAtLeastLocus_of_le_pow (d.center i) (d.controlledTransform I m i) m (hle i hi)
  · intro i hid
    have hi : i < t.length := by rw [hlen]; exact hid
    have : AlgebraicGeometry.Surjective (t.strictPullbackComparisonMap D i (le_of_lt hi)) :=
      t.surjective_strictPullbackComparisonMap D i (le_of_lt hi)
    refine smooth_subschemeι_comp_of_smooth_comap_comp (t.strictPullbackComparisonMap D i (le_of_lt hi)) (d.projectionToBase i ≫ p) (d.center i)
      (hcomp i (le_of_lt hi)) ?_
    have hc : (d.center i).comap (t.strictPullbackComparisonMap D i (le_of_lt hi)) = t.center i :=
      (t.center_eq_comap_strictPullbackComparisonMap D i hi).symm
    have hpr : t.strictPullbackComparisonMap D i (le_of_lt hi) ≫ d.projectionToBase i ≫ p = t.proj i ≫ g ≫ p := by
      rw [← Category.assoc, strictPullbackComparisonMap_comp_projectionToBase_consolidated348 t D i (le_of_lt hi), Category.assoc]
    rw [hc, hpr]
    exact t.center_smooth i hi
  · intro i hid
    have hi : i < t.length := by rw [hlen]; exact hid
    have : AlgebraicGeometry.Surjective (t.strictPullbackComparisonMap D i (le_of_lt hi)) :=
      t.surjective_strictPullbackComparisonMap D i (le_of_lt hi)
    refine hasStrictNormalCrossingsWith_of_comap (d.projectionToBase i ≫ p) (t.strictPullbackComparisonMap D i (le_of_lt hi))
      (hcomp i (le_of_lt hi)) (d.center i) (d.boundaryFrom E i) ?_
    have hc : (d.center i).comap (t.strictPullbackComparisonMap D i (le_of_lt hi)) = t.center i :=
      (t.center_eq_comap_strictPullbackComparisonMap D i hi).symm
    have hb : (d.boundaryFrom E i).map (fun A => A.comap (t.strictPullbackComparisonMap D i (le_of_lt hi))) = t.boundary i :=
      (t.boundary_eq_comap_strictPullbackComparisonMap D hNd hNt i (le_of_lt hi)).symm
    have hpr : t.strictPullbackComparisonMap D i (le_of_lt hi) ≫ d.projectionToBase i ≫ p = t.proj i ≫ g ≫ p := by
      rw [← Category.assoc, strictPullbackComparisonMap_comp_projectionToBase_consolidated348 t D i (le_of_lt hi), Category.assoc]
    rw [hc, hb, hpr]
    exact t.center_snc i hi

theorem isMarked_balancedTunedIdeal_of_isStrictPullbackBlowupSeq (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (Afam : ℕ → PrincipalizationAssignment.{u}) (T : MarkedIdealWithBoundary.{u})
    (h : MaxContactFunctoriality.OrderReductionHypotheses P T)
    [CharZero T.base]
    [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap]
    [Smooth (MaxContactCoverData.coverMap T h.valid)]
    [AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap T h.valid)]
    [IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{u})]
    (_hoi : MaxContactFunctoriality.IsLocalIsomorphism (MaxContactCoverData.coverMap T h.valid))
    (_hmult : 1 ≤ MaxContactCoverData.tunedMult T)
    (d : BlowupSequenceData T.scheme)
    (hpb : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
      (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups)
    (hNd : ∀ i ≤ d.length, IsLocallyNoetherian (d.obj i))
    (hNt : ∀ i ≤ (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).length,
      IsLocallyNoetherian ((MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).obj i))
    (hcomp : ∀ D : StrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
        (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups,
      ∀ (i : ℕ) (hi : i ≤ (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).length),
        MaxContactFunctoriality.IsLocalIsomorphism
          (D.comp i ((MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).le_toSequenceOfBlowups_length hi))) :
    d.IsMarked T.structMap (MaxContactCoverData.balancedTunedIdeal T h.valid)
      (MaxContactCoverData.tunedMult T) T.boundary := by
  have : Flat (MaxContactCoverData.coverMap T h.valid) := inferInstance
  have D : StrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
      (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups :=
    hpb.toStrictPullbackBlowupSeq
  exact isMarked_of_strictPullbackBlowupSeq_consolidated348 T.structMap (MaxContactCoverData.coverMap T h.valid)
    (MaxContactCoverData.balancedTunedIdeal T h.valid) (MaxContactCoverData.tunedMult T) T.boundary d
    (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid) D hNd hNt (hcomp D)

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactResolution
section



theorem orderAtLeastLocus_eq_empty_of_comap_eq_empty {A B : Scheme.{u}} (f : A ⟶ B)
    [AlgebraicGeometry.Surjective f] (J : B.IdealSheafData) (μ : ℕ)
    (h : orderAtLeastLocus (J.comap f) μ = ∅) : orderAtLeastLocus J μ = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨y, rfl⟩ := f.surjective x
  have hmem : y ∈ orderAtLeastLocus (J.comap f) μ := by
    rw [mem_orderAtLeastLocus_iff]
    exact le_trans ((mem_orderAtLeastLocus_iff J μ (f.base y)).mp hx)
      (orderAt_le_orderAt_comap f J y)
  rw [h] at hmem
  simp at hmem

namespace MaxContactFunctoriality

theorem OrderReductionHypotheses.dropTrivialBoundary {P : ℕ → Prop} {T : MarkedIdealWithBoundary.{u}} (h : OrderReductionHypotheses P T)
    {hinv : ComapIsoInvariance.{u}} {A : ℕ → PrincipalizationAssignment.{u}} {B : PrincipalizationAssignment.{u}}
    (hd : DescentHypotheses hinv P A B) : OrderReductionHypotheses P (MaxContactReduction.dropTrivialBoundary T) := by
  refine ⟨?_, ?_, ?_, hd.valid_trim T h.valid⟩
  · have hdim := h.dim_prop
    rwa [← MaxContactReduction.dropTrivialBoundary_dim T] at hdim
  · intro x
    exact h.orderLE x
  · exact h.coSupport_nonempty

section

variable (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})
  (B : PrincipalizationAssignment.{u})

theorem isMarked_balancedTunedIdeal_iff_and_orderAtLeastLocus_eq (hd : DescentHypotheses hinv P A B) (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T)
    (d : BlowupSequenceData T.scheme) :
    (d.IsMarked T.structMap T.ideal T.mult T.boundary ↔
      d.IsMarked T.structMap (MaxContactCoverData.balancedTunedIdeal T h.valid)
        (MaxContactCoverData.tunedMult T) T.boundary) ∧
    (d.IsMarked T.structMap T.ideal T.mult T.boundary →
      ∀ i ≤ d.length,
        orderAtLeastLocus (d.controlledTransform (MaxContactCoverData.balancedTunedIdeal T h.valid)
            (MaxContactCoverData.tunedMult T) i) (MaxContactCoverData.tunedMult T) =
          orderAtLeastLocus (d.controlledTransform T.ideal T.mult i) T.mult) := by
  have := h.valid.charZero
  have := h.valid.smooth
  have := h.valid.locallyOfFiniteType
  have h2 := hd.tuning
  unfold IsMarkedIffBalancedTunedSheaf at h2
  have key := h2 T.base T.scheme T.structMap T.ideal T.mult h.valid.one_le_mult
    ⟨(orderLE_iff T.ideal T.mult).mpr h.orderLE, h.coSupport_nonempty⟩ T.boundary d
  exact ⟨key.1, key.2.1⟩

theorem exists_blowupSequenceData_isStrictPullback_cover (hstar : CoverSequenceProperties hinv P A)
    (hd : DescentHypotheses hinv P A B) (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T) :
    ∃ (d : BlowupSequenceData T.scheme)
      (hm : d.IsMarked T.structMap T.ideal T.mult T.boundary),
      IsStrictPullbackBlowupSeq
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid)
          (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid hinv
            (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toBlowupSequenceData.toSequenceOfBlowups
          d.toSequenceOfBlowups ∧
        maxContactPrincipalization hinv A T =
          (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hm).toMarkedSequenceOfBlowups := by
  obtain ⟨d0, hpb0⟩ := hstar.descends (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd)
  obtain ⟨d, hdesc⟩ :
      ∃ e : BlowupSequenceData (MaxContactReduction.dropTrivialBoundary T).scheme,
        MaxContactReduction.descendStrictPullback (MaxContactReduction.dropTrivialBoundary T)
            (MaxContactCoverData.coverTriple (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid)
            (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid)
            (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid hinv
              (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))) = some e :=
    MaxContactCoverData.exists_descendStrictPullback_eq_some _ _ ⟨d0, hpb0⟩
  have hpb : IsStrictPullbackBlowupSeq
      (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid)
      (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid hinv
        (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups :=
    MaxContactCoverData.isStrictPullbackBlowupSeq_of_descendStrictPullback_eq_some _ _ hdesc
  have hm0 : d.IsMarked (MaxContactReduction.dropTrivialBoundary T).structMap
      (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid)
      (MaxContactCoverData.tunedMult (MaxContactReduction.dropTrivialBoundary T))
      (MaxContactReduction.dropTrivialBoundary T).boundary :=
    hd.isMarked (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd) d hpb
  have hm1 : d.IsMarked T.structMap T.ideal T.mult (MaxContactReduction.dropTrivialBoundary T).boundary :=
    ((isMarked_balancedTunedIdeal_iff_and_orderAtLeastLocus_eq hinv P A B hd (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd) d).1).mpr hm0
  have hm : d.IsMarked T.structMap T.ideal T.mult T.boundary :=
    hd.isMarked_of_trim T h.valid d T.ideal T.mult hm1
  refine ⟨d, hm, hpb, ?_⟩
  exact MaxContactCoverData.reduceOrder_eq_toMarkedSequence hinv T (lowerDimensionalFamily A T) h.valid
    h.orderAtLeastLocus_ne_empty (h.dropTrivialBoundary hd).valid d hdesc hm

theorem length_eq_zero_of_orderAtLeastLocus_eq_empty (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (_hdim : P T.krullDimSucc)
    (_hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (hemp : orderAtLeastLocus T.ideal T.mult = ∅) :
    (maxContactPrincipalization hinv A T).length = 0 := by
  have h1 : MaxContactReduction.reduceOrder hinv T (lowerDimensionalFamily A T) = MaxContactReduction.emptyMarkedSeq T :=
    MaxContactReduction.reduceOrder_of_orderAtLeastLocus_eq_empty hinv T (lowerDimensionalFamily A T) hv hemp
  rw [maxContactPrincipalization_apply, h1, MaxContactCoverData.emptyMarkedSeq_length]

theorem center_support_nonempty (hstar : CoverSequenceProperties hinv P A) (hd : DescentHypotheses hinv P A B)
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hdim : P T.krullDimSucc)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (i : ℕ) (hi : i < (maxContactPrincipalization hinv A T).length) :
    (↑((maxContactPrincipalization hinv A T).center i).support :
      Set ↥((maxContactPrincipalization hinv A T).schemeAt i)).Nonempty := by
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  · exfalso
    have hb : maxContactPrincipalization hinv A T = MaxContactReduction.emptyMarkedSeq T :=
      MaxContactReduction.reduceOrder_of_orderAtLeastLocus_eq_empty hinv T (lowerDimensionalFamily A T) hv hemp
    rw [hb, MaxContactCoverData.emptyMarkedSeq_length] at hi
    exact Nat.not_lt_zero i hi
  · have h : OrderReductionHypotheses P T := ⟨hdim, hord, Set.nonempty_iff_ne_empty.mpr hemp, hv⟩
    obtain ⟨d, hm, hpb, heq⟩ := exists_blowupSequenceData_isStrictPullback_cover hinv P A B hstar hd T h
    have hstarseq : ∀ j : ℕ,
        j < (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid hinv
              (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toBlowupSequenceData.toSequenceOfBlowups.length →
        (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid hinv
              (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toBlowupSequenceData.toSequenceOfBlowups.center j ≠ ⊤ := by
      intro j hj
      rw [BlowupSequenceData.toSequenceOfBlowups_length] at hj
      exact hstar.center_ne_top (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd) j hj
    have hdseq := hpb.center_ne_top_of_forall_center_ne_top hstarseq
    rw [heq] at hi ⊢
    rw [BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups] at hi ⊢
    exact (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mpr (hdseq i hi)

private theorem orderAtLeastLocus_controlledTransform_eq_empty_of_flat_surjective_consolidated347 {k : Type u} [Field k] {X' X : Scheme.{u}}
    {q : X' ⟶ Spec (CommRingCat.of k)} {g : X' ⟶ X}
    (hflat : Flat g) (hsurj : AlgebraicGeometry.Surjective g)
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} {d : BlowupSequenceData X}
    (t : MarkedBlowupSequenceData q (I.comap g) m (List.map (fun Z => Z.comap g) E))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (hdiv : ∀ i < d.length, ∃ Bb,
      Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * Bb = (d.controlledTransform I m i).comap (d.map i))
    (hres : orderAtLeastLocus (t.ideal t.length) m = ∅) :
    orderAtLeastLocus (d.controlledTransform I m d.length) m = ∅ := by
  have := hflat
  have := hsurj
  have : AlgebraicGeometry.Surjective (t.strictPullbackComparisonMap D t.length le_rfl) :=
    MarkedBlowupSequenceData.surjective_strictPullbackComparisonMap t D t.length le_rfl
  have hid : t.ideal t.length
      = (d.controlledTransform I m t.length).comap (t.strictPullbackComparisonMap D t.length le_rfl) :=
    MarkedBlowupSequenceData.ideal_eq_comap_controlledTransform t D hdiv t.length le_rfl
  have hlen : t.length = d.length := MarkedBlowupSequenceData.length_eq_of_strictPullbackBlowupSeq t D
  have h0 : orderAtLeastLocus ((d.controlledTransform I m t.length).comap (t.strictPullbackComparisonMap D t.length le_rfl)) m = ∅ := by
    rw [← hid]
    exact hres
  have h1 := orderAtLeastLocus_eq_empty_of_comap_eq_empty (t.strictPullbackComparisonMap D t.length le_rfl)
    (d.controlledTransform I m t.length) m h0
  rwa [hlen] at h1

theorem isResolution_of_orderAt_le_mult (hstar : CoverSequenceProperties hinv P A) (hd : DescentHypotheses hinv P A B)
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hdim : P T.krullDimSucc)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) :
    (maxContactPrincipalization hinv A T).IsResolution := by
  rw [MarkedSequenceOfBlowups.isResolution_iff, MarkedSequenceOfBlowups.lastIdeal_eq]
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  · have h1 : MaxContactReduction.reduceOrder hinv T (lowerDimensionalFamily A T) = MaxContactReduction.emptyMarkedSeq T :=
      MaxContactReduction.reduceOrder_of_orderAtLeastLocus_eq_empty hinv T (lowerDimensionalFamily A T) hv hemp
    rw [maxContactPrincipalization_apply, h1, MaxContactCoverData.emptyMarkedSeq_length, MarkedSequenceOfBlowups.ideal_zero,
      hinv.coSupport_comap, hemp, Set.preimage_empty]
  · have h : OrderReductionHypotheses P T := ⟨hdim, hord, Set.nonempty_iff_ne_empty.mpr hemp, hv⟩
    have h' : OrderReductionHypotheses P (MaxContactReduction.dropTrivialBoundary T) := h.dropTrivialBoundary hd
    obtain ⟨d, hm, hpb, heq⟩ := exists_blowupSequenceData_isStrictPullback_cover hinv P A B hstar hd T h
    rw [heq]
    simp only [MarkedBlowupSequenceData.toMarkedSequence_ideal, MarkedBlowupSequenceData.toMarkedSequence_length,
      BlowupSequenceData.toMarkedBlowupSequenceData_ideal, BlowupSequenceData.toMarkedBlowupSequenceData_length]
    have hm0 : d.IsMarked (MaxContactReduction.dropTrivialBoundary T).structMap
        (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) h'.valid)
        (MaxContactCoverData.tunedMult (MaxContactReduction.dropTrivialBoundary T))
        (MaxContactReduction.dropTrivialBoundary T).boundary :=
      hd.isMarked (MaxContactReduction.dropTrivialBoundary T) h' d hpb
    have htc := (isMarked_balancedTunedIdeal_iff_and_orderAtLeastLocus_eq hinv P A B hd (MaxContactReduction.dropTrivialBoundary T) h' d).2
      ((isMarked_balancedTunedIdeal_iff_and_orderAtLeastLocus_eq hinv P A B hd (MaxContactReduction.dropTrivialBoundary T) h' d).1.mpr hm0) d.length le_rfl
    have D : StrictPullbackBlowupSeq (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) h'.valid)
        (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) h'.valid hinv
          (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups := by
      rw [MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups]
      exact hpb.toStrictPullbackBlowupSeq
    have key : orderAtLeastLocus (d.controlledTransform
        (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) h'.valid)
        (MaxContactCoverData.tunedMult (MaxContactReduction.dropTrivialBoundary T)) d.length)
        (MaxContactCoverData.tunedMult (MaxContactReduction.dropTrivialBoundary T)) = ∅ :=
      orderAtLeastLocus_controlledTransform_eq_empty_of_flat_surjective_consolidated347 (hd.flat_coverMap (MaxContactReduction.dropTrivialBoundary T) h')
        (hd.surjective_coverMap (MaxContactReduction.dropTrivialBoundary T) h')
        (I := MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) h'.valid)
        (m := MaxContactCoverData.tunedMult (MaxContactReduction.dropTrivialBoundary T))
        (E := (MaxContactReduction.dropTrivialBoundary T).boundary) (d := d)
        (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) h'.valid hinv
          (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T)))
        D hm0.divisible (hstar.resolves (MaxContactReduction.dropTrivialBoundary T) h')
    exact htc.symm.trans key

theorem orderAt_ideal_le_mult (hd : DescentHypotheses hinv P A B) (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (_hdim : P T.krullDimSucc) (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (i : ℕ) (hi : i ≤ (maxContactPrincipalization hinv A T).length)
    (x : ↥((maxContactPrincipalization hinv A T).schemeAt i)) :
    orderAt ((maxContactPrincipalization hinv A T).ideal i) x ≤ (T.mult : ℕ∞) :=
  hd.order_le T hv hord (maxContactPrincipalization hinv A T) i hi x

end

end MaxContactFunctoriality

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderCertificate
section



section
variable {k : Type u} [Field k]

private theorem orderCertificate_congr_mult_consolidated377 {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ μ' : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : μ = μ')
    (c : OrderCertificate W p N μ Mem Z) : OrderCertificate W p N μ' Mem Z := by
  subst h
  exact c

private theorem orderCertificate_congr_map_consolidated377 {W : Scheme.{u}}
    {p p' : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : p = p')
    (c : OrderCertificate W p N μ Mem Z) : OrderCertificate W p' N μ Mem Z := by
  subst h
  exact c

private theorem boundaryLocus_eq_iUnion_support_consolidated377 {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedSequenceOfBlowups p I m E) (t : ℕ) :
    MarkedSequenceOfBlowups.boundaryLocus s t
      = ⋃ D ∈ s.boundary t, (↑D.support : Set ↥(s.schemeAt t)) := by
  ext x
  rw [MarkedSequenceOfBlowups.mem_boundaryLocus_iff]
  constructor
  · rintro ⟨D, hD, hx⟩
    exact Set.mem_iUnion₂.2 ⟨D, hD, hx⟩
  · intro hx
    obtain ⟨D, hD, hx⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨D, hD, hx⟩


end

section
variable {k : Type u} [Field k] {X' X : Scheme.{u}} {q : X' ⟶ Spec (CommRingCat.of k)} {g : X' ⟶ X} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} {d : BlowupSequenceData X} (hf : Flat g)
include hf

private theorem boundary_eq_map_comap_strictPullbackComparisonMap_of_flat_consolidated377 (s : MarkedBlowupSequenceData q (I.comap g) m (List.map (fun A => A.comap g) E))
    (D : StrictPullbackBlowupSeq g s.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (hNd : ∀ i ≤ d.length, IsLocallyNoetherian (d.obj i))
    (hNt : ∀ i ≤ s.length, IsLocallyNoetherian (s.obj i))
    (i : ℕ) (hi : i ≤ s.length) :
    s.boundary i = List.map (fun A => A.comap (s.strictPullbackComparisonMap D i hi)) (d.boundaryFrom E i) := by
  have := hf
  exact MarkedBlowupSequenceData.boundary_eq_comap_strictPullbackComparisonMap s D hNd hNt i hi

private theorem surjective_strictPullbackComparisonMap_of_flat_of_surjective_consolidated377 (hs : AlgebraicGeometry.Surjective g)
    (s : MarkedBlowupSequenceData q (I.comap g) m (List.map (fun A => A.comap g) E))
    (D : StrictPullbackBlowupSeq g s.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (i : ℕ) (hi : i ≤ s.length) :
    AlgebraicGeometry.Surjective (s.strictPullbackComparisonMap D i hi) := by
  have := hf
  have := hs
  exact MarkedBlowupSequenceData.surjective_strictPullbackComparisonMap s D i hi


end

theorem iUnion_support_comap_eq_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (l : List Y.IdealSheafData) :
    (⋃ J ∈ l.map (fun D => D.comap f), (↑J.support : Set ↥X)) =
      (⇑f) ⁻¹' (⋃ J ∈ l, (↑J.support : Set ↥Y)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨J, hJ, hx⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hJ
    exact Set.mem_preimage.2 (Set.mem_iUnion₂.2
      ⟨D, hD, (AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap ..).mp hx⟩)
  · intro hx
    obtain ⟨D, hD, hx⟩ := Set.mem_iUnion₂.1 (Set.mem_preimage.1 hx)
    exact Set.mem_iUnion₂.2
      ⟨D.comap f, List.mem_map.2 ⟨D, hD, rfl⟩,
        (AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap ..).mpr hx⟩

namespace MaxContactFunctoriality

private theorem mem_boundary_of_forall_mem_consolidated377 {X : Scheme.{u}} (d : BlowupSequenceData X)
    (E E' : List X.IdealSheafData) (hEE : ∀ D ∈ E, D ∈ E') :
    ∀ (t : ℕ) (D : (d.obj t).IdealSheafData), D ∈ d.boundaryFrom E t → D ∈ d.boundaryFrom E' t := by
  intro t
  induction t with
  | zero =>
      intro D hD
      rw [BlowupSequenceData.boundary_zero] at hD ⊢
      obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hD
      exact List.mem_map.2 ⟨A, hEE A hA, rfl⟩
  | succ t ih =>
      intro D hD
      rw [BlowupSequenceData.boundary_succ] at hD ⊢
      rcases List.mem_append.1 hD with hmem | hmem
      · obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hmem
        exact List.mem_append.2 (Or.inl (List.mem_map.2 ⟨A, ih A hA, rfl⟩))
      · exact List.mem_append.2 (Or.inr hmem)

theorem mem_boundary_of_mem_boundary_dropTrivialBoundary (T : MarkedIdealWithBoundary.{u}) (d : BlowupSequenceData T.scheme) (t : ℕ)
    (D : (d.obj t).IdealSheafData)
    (hD : D ∈ d.boundaryFrom (MaxContactReduction.dropTrivialBoundary T).boundary t) :
    D ∈ d.boundaryFrom T.boundary t := by
  refine mem_boundary_of_forall_mem_consolidated377 d _ _ ?_ t D hD
  intro A hA
  rw [MaxContactReduction.dropTrivialBoundary_boundary] at hA
  exact (List.mem_filter.1 hA).1

section

variable (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})
  (B : PrincipalizationAssignment.{u})

section
variable (hstar : CoverSequenceProperties hinv P A) (hd : DescentHypotheses hinv P A B) (T : MarkedIdealWithBoundary.{u})
include hstar hd

theorem orderCertificate_of_isStrictPullbackBlowupSeq (h : OrderReductionHypotheses P T) (hone : T.mult = 1)
    (d : BlowupSequenceData T.scheme)
    (hmk : d.IsMarked T.structMap T.ideal T.mult T.boundary)
    (hpb : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
      (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toSequenceOfBlowups d.toSequenceOfBlowups)
    (t : ℕ) (ht : t < d.length) :
    OrderCertificate ((d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.schemeAt t)
      (MarkedSequenceOfBlowups.projectionToSpec
        (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups t)
      ((d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.ideal t)
      T.mult
      (MarkedSequenceOfBlowups.boundaryLocus
        (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups t)
      ((d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.center t) := by
  classical
  have hflat := hd.flat_coverMap T h
  have hsurjc := hd.surjective_coverMap T h
  have htun : MaxContactCoverData.balancedTunedIdeal T h.valid = T.ideal :=
    hd.tunedIdeal_of_mult_one T h.valid hone
  have hmul : MaxContactCoverData.tunedMult T = T.mult := by
    show tuningExponent T.mult = T.mult
    rw [hone]
    exact tuningExponent_one
  have hstrictPullback : StrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
      (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      d.toSequenceOfBlowups := hpb.toStrictPullbackBlowupSeq
  have hlen : (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).length = d.length :=
    MarkedBlowupSequenceData.length_eq_of_strictPullbackBlowupSeq _ hstrictPullback
  have htu : t ≤ (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).length := by omega
  have htlt : t < (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).length := by omega
  have hN := hd.locallyNoetherian T h d hpb
  have hdiv : ∀ i < d.length, ∃ B',
      Blowup.exceptionalIdeal (d.map i) (d.center i) ^ (MaxContactCoverData.tunedMult T) * B' =
        (d.controlledTransform (MaxContactCoverData.balancedTunedIdeal T h.valid) (MaxContactCoverData.tunedMult T) i).comap
          (d.map i) := by
    rw [htun, hmul]
    exact hmk.1
  have hid := MarkedBlowupSequenceData.ideal_eq_comap_controlledTransform
    (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)) hstrictPullback hdiv t htu
  have hctr := MarkedBlowupSequenceData.center_eq_comap_strictPullbackComparisonMap
    (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)) hstrictPullback t htlt
  have hbd := boundary_eq_map_comap_strictPullbackComparisonMap_of_flat_consolidated377 hflat
    (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)) hstrictPullback hN.1 hN.2 t htu
  have hstr := isPullback_projectionToBase_of_isPullback_blowupMorphism (MaxContactCoverData.coverMap T h.valid)
    (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups
    (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.toSequenceOfBlowups.length
    (fun i hi => hstrictPullback.comp i hi) hstrictPullback.comp_zero (fun i hi => hstrictPullback.pullback i hi) t
    (MarkedBlowupSequenceData.le_toSequenceOfBlowups_length _ htu)
  have hw : (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.projectionToBase t ≫
      MaxContactCoverData.coverMap T h.valid =
      hstrictPullback.comp t (MarkedBlowupSequenceData.le_toSequenceOfBlowups_length _ htu) ≫ d.projectionToBase t := by
    rw [← BlowupSequenceData.toSequenceOfBlowups_projectionToBase]
    exact hstr.w.symm
  have hw' : (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.projectionToBase t ≫
      MaxContactCoverData.coverMap T h.valid =
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).strictPullbackComparisonMap hstrictPullback t htu) ≫
        d.projectionToBase t := hw
  have hcs := MaxContactCoverData.coverTriple_structureMorphism T h.valid
  have e1 : (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.projectionToBase t ≫
      (MaxContactCoverData.coverTriple T h.valid).structMap =
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).strictPullbackComparisonMap hstrictPullback t htu) ≫
        (d.projectionToBase t ≫ T.structMap) :=
    (congrArg (fun φ =>
        (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.projectionToBase t ≫ φ)
        hcs).trans
      (((Category.assoc _ _ _).symm).trans
        ((congrArg (fun φ => φ ≫ T.structMap) hw').trans (Category.assoc _ _ _)))
  have hci : d.controlledTransform (MaxContactCoverData.balancedTunedIdeal T h.valid)
      (MaxContactCoverData.coverTriple T h.valid).mult t = d.controlledTransform T.ideal T.mult t := by
    rw [htun, MaxContactCoverData.coverTriple_mult, hmul]
  have e2 : (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.ideal t =
      (((d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.ideal t).comap
        ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).strictPullbackComparisonMap hstrictPullback t htu)) := by
    simp only [MarkedBlowupSequenceData.toMarkedSequence_ideal, BlowupSequenceData.toMarkedBlowupSequenceData_ideal]
    exact hid.trans (congrArg (fun J => J.comap
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).strictPullbackComparisonMap hstrictPullback t htu)) hci)
  have e3 : (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.center t =
      (((d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.center t).comap
        ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).strictPullbackComparisonMap hstrictPullback t htu)) := by
    simp only [MarkedBlowupSequenceData.toMarkedSequence_center, BlowupSequenceData.toMarkedBlowupSequenceData_center]
    exact hctr
  have e4 : MarkedSequenceOfBlowups.boundaryLocus
      (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups t =
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).strictPullbackComparisonMap hstrictPullback t htu) ⁻¹'
        MarkedSequenceOfBlowups.boundaryLocus
          (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups t := by
    simp only [boundaryLocus_eq_iUnion_support_consolidated377, MarkedBlowupSequenceData.toMarkedSequence_boundary,
      BlowupSequenceData.toMarkedBlowupSequenceData_boundary]
    rw [hbd]
    exact iUnion_support_comap_eq_preimage _ _
  have hp : MarkedSequenceOfBlowups.projectionToSpec
      (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups t
      = d.projectionToBase t ≫ T.structMap := by
    simp only [MarkedSequenceOfBlowups.projectionToSpec_eq, MarkedBlowupSequenceData.toMarkedSequence_projectionToBase,
      BlowupSequenceData.toMarkedBlowupSequenceData_projectionToBase]
    rfl
  refine orderCertificate_congr_map_consolidated377 hp.symm ?_
  refine hd.cert_descend T.base
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).obj t) _ _
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).strictPullbackComparisonMap hstrictPullback t htu) ?_ ?_
      _ _ _ _ ?_
  · exact hd.comp_openImmersion T h d hstrictPullback t htu
  · exact surjective_strictPullbackComparisonMap_of_flat_of_surjective_consolidated377 hflat hsurjc
      (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)) hstrictPullback t htu
  · have hc : OrderCertificate
        ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.schemeAt t)
        ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.projectionToBase t ≫
          (MaxContactCoverData.coverTriple T h.valid).structMap)
        ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.ideal t) 1
        (MarkedSequenceOfBlowups.boundaryLocus
          (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups t)
        ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.center t) :=
      hstar.cert T h hone t htlt
    rw [e1, e2, e3, e4] at hc
    exact orderCertificate_congr_mult_consolidated377 hone.symm hc

theorem orderCertificate_of_orderAt_le_mult (hv : T.IsAdmissible) (hdim : P T.krullDimSucc)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (t : ℕ) (ht : t < (maxContactPrincipalization hinv A T).length) :
    OrderCertificate ((maxContactPrincipalization hinv A T).schemeAt t)
      (MarkedSequenceOfBlowups.projectionToSpec (maxContactPrincipalization hinv A T) t)
      ((maxContactPrincipalization hinv A T).ideal t)
      T.mult
      (MarkedSequenceOfBlowups.boundaryLocus (maxContactPrincipalization hinv A T) t)
      ((maxContactPrincipalization hinv A T).center t) := by
  classical
  rcases Nat.lt_or_ge T.mult 2 with hm2 | hm2
  · have hone : T.mult = 1 := le_antisymm (by omega) hv.one_le_mult
    by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
    · have h0 := length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P A T hv hdim hord hemp
      omega
    · have hyp : OrderReductionHypotheses P T := ⟨hdim, hord, Set.nonempty_iff_ne_empty.2 hemp, hv⟩
      obtain ⟨d, hm', hpb', heq⟩ := exists_blowupSequenceData_isStrictPullback_cover hinv P A B hstar hd T hyp
      have honeT : (MaxContactReduction.dropTrivialBoundary T).mult = 1 := by
        rw [MaxContactReduction.dropTrivialBoundary_mult]; exact hone
      have htrim : OrderReductionHypotheses P (MaxContactReduction.dropTrivialBoundary T) := hyp.dropTrivialBoundary hd
      have hmk0 := hd.isMarked (MaxContactReduction.dropTrivialBoundary T) htrim d hpb'
      have htun : MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrim.valid =
          (MaxContactReduction.dropTrivialBoundary T).ideal :=
        hd.tunedIdeal_of_mult_one (MaxContactReduction.dropTrivialBoundary T) htrim.valid honeT
      have hmul : MaxContactCoverData.tunedMult (MaxContactReduction.dropTrivialBoundary T)
          = (MaxContactReduction.dropTrivialBoundary T).mult := by
        show tuningExponent (MaxContactReduction.dropTrivialBoundary T).mult = (MaxContactReduction.dropTrivialBoundary T).mult
        rw [honeT]
        exact tuningExponent_one
      rw [htun, hmul] at hmk0
      have htlen : t < d.length := by
        rw [heq] at ht
        rw [MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length] at ht
        exact ht
      have hcert := orderCertificate_of_isStrictPullbackBlowupSeq hinv P A B hstar hd (MaxContactReduction.dropTrivialBoundary T) htrim honeT d
        hmk0 hpb' t htlen
      have hsub : MarkedSequenceOfBlowups.boundaryLocus
          (d.toMarkedBlowupSequenceData (MaxContactReduction.dropTrivialBoundary T).structMap (MaxContactReduction.dropTrivialBoundary T).ideal
            (MaxContactReduction.dropTrivialBoundary T).mult (MaxContactReduction.dropTrivialBoundary T).boundary hmk0).toMarkedSequenceOfBlowups t ⊆
          MarkedSequenceOfBlowups.boundaryLocus
            (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hm').toMarkedSequenceOfBlowups t := by
        simp only [boundaryLocus_eq_iUnion_support_consolidated377, MarkedBlowupSequenceData.toMarkedSequence_boundary,
          BlowupSequenceData.toMarkedBlowupSequenceData_boundary]
        intro x hx
        obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.1 hx
        exact Set.mem_iUnion₂.2 ⟨D, mem_boundary_of_mem_boundary_dropTrivialBoundary T d t D hD, hxD⟩
      have hfin := orderCertificate_mono_of_subset hsub hcert
      rw [heq]
      exact orderCertificate_congr_mult_consolidated377 (MaxContactReduction.dropTrivialBoundary_mult T) hfin
  · exact OrderCertificate.of_two_le _ _ _ _ _ _ hm2


end

end

end MaxContactFunctoriality

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderCertificateDescent
section

open TopologicalSpace


variable {A B C : Scheme.{u}}

section
variable (γ : A ⟶ B) (W : A.Opens) (h : IsOpenImmersion (W.ι ≫ γ))

theorem comap_isoRangeOpens_inv (J : B.IdealSheafData) :
    ((J.comap γ).comap W.ι).comap (isoRangeOpens γ W h).inv = J.comap (rangeOpens γ W h).ι := by
  simp [← isoRangeOpens_inv_comp γ W h]

theorem preimage_isoRangeOpens_inv (S : Set ↥B) :
    (isoRangeOpens γ W h).inv.base ⁻¹' (W.ι.base ⁻¹' (γ.base ⁻¹' S))
      = (rangeOpens γ W h).ι.base ⁻¹' S := by
  ext x
  simp [← isoRangeOpens_inv_comp γ W h]

theorem rangeOpens_ι_comp (f : B ⟶ C) :
    (rangeOpens γ W h).ι ≫ f = (isoRangeOpens γ W h).inv ≫ W.ι ≫ γ ≫ f :=
  (isoRangeOpens_inv_comp_assoc γ W h f).symm


end

theorem exists_opens_orderCertificate_of_isLocalIsomorphism
    (hopen : ∀ (k : Type u) [Field k], OpenImmersionStability k)
    {k : Type u} [Field k] {W W' : Scheme.{u}} (p : W ⟶ Spec (CommRingCat.of k))
    (g : W' ⟶ W) (hg : MaxContactFunctoriality.IsLocalIsomorphism g)
    [AlgebraicGeometry.Surjective g]
    (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W) (Z : W.IdealSheafData)
    (hcert : OrderCertificate W' (g ≫ p) (N.comap g) μ (g.base ⁻¹' Mem) (Z.comap g))
    (x : ↥W) :
    ∃ V : W.Opens, x ∈ V ∧
      OrderCertificate V.toScheme (V.ι ≫ p) (N.comap V.ι) μ (V.ι.base ⁻¹' Mem) (Z.comap V.ι) := by
  obtain ⟨U, hU, hxU⟩ := exists_mem_rangeOpens g hg x
  refine ⟨rangeOpens g U hU, hxU, ?_⟩
  have hres := hcert.restrict (hopen k) U
  have htr := OrderCertificate.comap_iso_of_eq_iso_hom_comp (isoRangeOpens g U hU).symm
    (rangeOpens_ι_comp g U hU p) hres
  simp only [Iso.symm_hom, comap_isoRangeOpens_inv, preimage_isoRangeOpens_inv] at htr
  exact htr

def OrderCertificateLocalToGlobal : Prop :=
  ∀ (k : Type u) [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))
    (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W) (Z : W.IdealSheafData),
    (∀ x : ↥W, ∃ V : W.Opens, x ∈ V ∧
      OrderCertificate V.toScheme (V.ι ≫ p) (N.comap V.ι) μ (V.ι.base ⁻¹' Mem) (Z.comap V.ι)) →
    OrderCertificate W p N μ Mem Z

theorem orderCertificate_of_comap_of_isLocalIsomorphism
    (hopen : ∀ (k : Type u) [Field k], OpenImmersionStability k)
    (hglue : OrderCertificateLocalToGlobal.{u})
    (k : Type u) [Field k] (W W' : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))
    (g : W' ⟶ W) (hg : MaxContactFunctoriality.IsLocalIsomorphism g)
    [AlgebraicGeometry.Surjective g]
    (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W) (Z : W.IdealSheafData)
    (hcert : OrderCertificate W' (g ≫ p) (N.comap g) μ (g.base ⁻¹' Mem) (Z.comap g)) :
    OrderCertificate W p N μ Mem Z :=
  hglue k W p N μ Mem Z
    (fun x => exists_opens_orderCertificate_of_isLocalIsomorphism hopen p g hg N μ Mem Z hcert x)

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SmoothDivisorReduction
section



private theorem coe_support_eq_range_subschemeι_consolidated379 {X : Scheme.{u}} (I : X.IdealSheafData) :
    (↑I.support : Set ↥X) = Set.range (⇑I.subschemeι.base) := by
  simp

private theorem isEmpty_subscheme_top_consolidated379 (X : Scheme.{u}) :
    IsEmpty ↥((⊤ : X.IdealSheafData).subscheme) := by
  have h2 : (↑(⊤ : X.IdealSheafData).support : Set ↥X) = ∅ :=
    (Scheme.IdealSheafData.eq_top_iff_support_eq_empty (⊤ : X.IdealSheafData)).mp rfl
  rw [coe_support_eq_range_subschemeι_consolidated379] at h2
  exact Set.range_eq_empty_iff.mp h2

theorem eq_top_of_imageIdealSheaf_eq_top {S X : Scheme.{u}} (σ : S ⟶ X) (J : S.IdealSheafData)
    (h : imageIdealSheaf σ J = ⊤) : J = ⊤ := by
  have hker : (J.subschemeι ≫ σ).ker = ⊤ := by
    rw [← imageIdealSheaf_eq_ker]
    exact h
  have hle : (⊤ : X.IdealSheafData).subschemeι.ker ≤ (J.subschemeι ≫ σ).ker :=
    le_of_eq (by rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι, hker])
  have hZ : IsEmpty ↥J.subscheme := by
    refine ⟨fun z => ?_⟩
    exact (isEmpty_subscheme_top_consolidated379 X).elim
      ((IsClosedImmersion.lift (⊤ : X.IdealSheafData).subschemeι (J.subschemeι ≫ σ) hle).base z)
  rw [Scheme.IdealSheafData.eq_top_iff_support_eq_empty, coe_support_eq_range_subschemeι_consolidated379,
    Set.range_eq_empty_iff]
  exact hZ

section
variable (T : MarkedIdealWithBoundary.{u})

private theorem boundary_dropTrivialBoundary_of_eq_nil_consolidated379 (h : T.boundary = []) :
    (MaxContactReduction.dropTrivialBoundary T).boundary = [] := by
  unfold MaxContactReduction.dropTrivialBoundary
  simp [h] <;> rfl

private theorem isBalanced_of_mult_eq_one_consolidated379 (hft : LocallyOfFiniteType T.structMap) (h : T.mult = 1) :
    T.IsBalanced hft := by
  unfold MarkedIdealWithBoundary.IsBalanced
  simp only [h]
  apply isDerivBalanced_one


end

private theorem toSequenceOfBlowups_heq_of_eq_consolidated379 {S₁ S₂ : MarkedIdealWithBoundary.{u}} (h : S₁ = S₂)
    (L : PrincipalizationAssignment.{u}) : HEq (L S₁).toSequenceOfBlowups (L S₂).toSequenceOfBlowups := by
  cases h
  rfl

namespace MaxContactFunctoriality

theorem isPushforward_of_isSmoothDivisor
    (hinv : ComapIsoInvariance.{u}) (P Q : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})
    (L L' : PrincipalizationAssignment.{u})
    (hstar : CoverSequenceProperties hinv P A)
    (hdes : DescentHypotheses hinv P A L)
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) L)
    (hlow : IsMaxOrderReduction Q L L')
    (hdimlink : ∀ a b : ℕ, a < b → P b → Q a)
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hP : P T.krullDimSucc) (hord : T.IsOrderBoundedByMult)
    (hbdry : T.boundary = []) (hmult : T.mult = 1)
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (e : Y ⟶ T.scheme)
    [IsClosedImmersion e] (hq : e ≫ T.structMap = q)
    (hsm : IsSmoothDivisor T.structMap (Scheme.Hom.ker e))
    (J : Y.IdealSheafData) (hJvalid : (T.withSchemeIdealBoundary Y q J []).IsAdmissible)
    (hJdim : (T.withSchemeIdealBoundary Y q J []).krullDimSucc < T.krullDimSucc)
    (hJideal : T.ideal = imageIdealSheaf e J) :
    IsPushforwardBlowupSeq e (L (T.withSchemeIdealBoundary Y q J [])).toSequenceOfBlowups
      (maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
  have hord' : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞) :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hord
  have hQdim : Q (T.withSchemeIdealBoundary Y q J []).krullDimSucc := hdimlink _ _ hJdim hP
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  · have hlen0 : (maxContactPrincipalization hinv A T).length = 0 :=
      length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P A T hv hP hord' hemp
    have h1 : orderAtLeastLocus T.ideal 1 = ∅ := by
      rw [← hmult]
      exact hemp
    have hsupp : (↑T.ideal.support : Set ↥T.scheme) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hx1 : x ∈ orderAtLeastLocus T.ideal 1 := (mem_orderAtLeastLocus_one_iff T.ideal x).mpr hx
      rw [h1] at hx1
      exact hx1
    have htop : T.ideal = ⊤ :=
      (Scheme.IdealSheafData.eq_top_iff_support_eq_empty T.ideal).mpr hsupp
    have hJtop : J = ⊤ := by
      refine eq_top_of_imageIdealSheaf_eq_top e J ?_
      rw [← hJideal]
      exact htop
    have hS : (L (T.withSchemeIdealBoundary Y q J [])).length = 0 := by
      refine hlow.trivial_of_coSupport_empty (T.withSchemeIdealBoundary Y q J []) hJvalid hQdim ?_
      rw [MarkedIdealWithBoundary.withSchemeIdealBoundary_ideal, MarkedIdealWithBoundary.withSchemeIdealBoundary_mult, hJtop, hmult]
      exact orderAtLeastLocus_top_eq_empty 1 le_rfl
    exact IsPushforwardBlowupSeq.of_length_eq_zero e _ _ hS hlen0
  · have hne : (orderAtLeastLocus T.ideal T.mult).Nonempty := Set.nonempty_iff_ne_empty.mpr hemp
    have hH : OrderReductionHypotheses P T := ⟨hP, hord', hne, hv⟩
    have hdropHyp : OrderReductionHypotheses P (MaxContactReduction.dropTrivialBoundary T) := hH.dropTrivialBoundary hdes
    have hSb : (MaxContactReduction.dropTrivialBoundary T).boundary = [] := boundary_dropTrivialBoundary_of_eq_nil_consolidated379 T hbdry
    have hmultOne : (MaxContactReduction.dropTrivialBoundary T).mult = 1 := hmult
    have hSq : e ≫ (MaxContactReduction.dropTrivialBoundary T).structMap = q := hq
    have hSsm : IsSmoothDivisor (MaxContactReduction.dropTrivialBoundary T).structMap (Scheme.Hom.ker e) := hsm
    have hSsub : ((MaxContactReduction.dropTrivialBoundary T).withSchemeIdealBoundary Y q J []).IsAdmissible := hJvalid
    have hSideal : (MaxContactReduction.dropTrivialBoundary T).ideal = imageIdealSheaf e J := hJideal
    have hci : @IsClosedImmersion Y (MaxContactReduction.dropTrivialBoundary T).scheme e :=
      inferInstanceAs (IsClosedImmersion e)
    have hhyp : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) hdropHyp.valid)
        (coverBlowupSequence hinv A (MaxContactReduction.dropTrivialBoundary T) hdropHyp.valid).toSequenceOfBlowups
        (A 0 ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e])).toSequenceOfBlowups :=
      hstar.hypersurface (MaxContactReduction.dropTrivialBoundary T) hdropHyp hSb hmultOne Y q e hSq hSsm J hSsub hSideal
    obtain ⟨d, hm, hpb, hmain⟩ := exists_blowupSequenceData_isStrictPullback_cover hinv P A L hstar hdes T hH
    have hflat := hdes.flat_coverMap (MaxContactReduction.dropTrivialBoundary T) hdropHyp
    have hsurj := hdes.surjective_coverMap (MaxContactReduction.dropTrivialBoundary T) hdropHyp
    have hequiv : d.toSequenceOfBlowups.Isomorphic
        (A 0 ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e])).toSequenceOfBlowups :=
      @IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic _ _ _ hflat hsurj _ _ _ _ hpb hhyp (SequenceOfBlowups.isomorphic_refl _)
    have hmainseq : (maxContactPrincipalization hinv A T).toSequenceOfBlowups = d.toSequenceOfBlowups := by
      rw [hmain, ← MaxContactCoverData.asMarkedSeq_eq_toMarkedSequence_of_isMarked T d hm]
      exact MaxContactCoverData.asMarkedSeq_toSequenceOfBlowups T d hm
    have hequiv2 :
        (A 0 ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e])).toSequenceOfBlowups.Isomorphic
          (maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
      rw [hmainseq]
      exact hequiv.symm
    have hεe : (kerSubschemeIso e).inv ≫ (Scheme.Hom.ker e).subschemeι = e :=
      kerSubschemeIso_inv_comp e
    have hsmInv : Smooth ((kerSubschemeIso e).inv) := inferInstance
    have hsuInv : AlgebraicGeometry.Surjective ((kerSubschemeIso e).inv) := inferInstance
    have hkerdata := hdes.valid_subst_ker T hv Y q e hq J hJvalid (kerSubschemeIso e).inv hεe
    have hT'valid : ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e]).IsAdmissible :=
      hdes.valid_withDivisor T hv hbdry Y q e hq hsm
    have hT'P : P ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e]).krullDimSucc := by
      rw [MarkedIdealWithBoundary.withBoundary_dim]
      exact hP
    have hT'ord : ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e]).IsOrderBoundedByMult := by
      rw [MarkedIdealWithBoundary.isOrderBoundedByMult_iff]
      exact hord'
    have hT'ft : LocallyOfFiniteType
        ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e]).structMap :=
      hT'valid.locallyOfFiniteType
    have hT'm : ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e]).mult = 1 := by
      rw [MarkedIdealWithBoundary.withBoundary_mult]
      exact hmultOne
    have hT'db : ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e]).IsBalanced hT'ft :=
      isBalanced_of_mult_eq_one_consolidated379 _ hT'ft hT'm
    have hT'j : 0 < ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e]).boundary.length := by
      rw [MarkedIdealWithBoundary.withBoundary_boundary]
      exact Nat.zero_lt_one
    have hVsub : (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
        (imageIdealSheaf (kerSubschemeIso e).inv J) []).IsAdmissible := hkerdata.1
    have hDsub : (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
        (imageIdealSheaf (kerSubschemeIso e).inv J) []).krullDimSucc < T.krullDimSucc := by
      rw [hkerdata.2]
      exact hJdim
    have hIdsub : T.ideal
        = imageIdealSheaf (Scheme.Hom.ker e).subschemeι
            (imageIdealSheaf (kerSubschemeIso e).inv J) := by
      have h1 := imageIdealSheaf_comp_comap_of_isIso (kerSubschemeIso e).inv
        (Scheme.Hom.ker e).subschemeι (imageIdealSheaf (kerSubschemeIso e).inv J)
      rw [comap_imageIdealSheaf, hεe] at h1
      rw [hJideal]
      exact h1
    have hpushD : IsPushforwardBlowupSeq (Scheme.Hom.ker e).subschemeι
        (L (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
            ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
            (imageIdealSheaf (kerSubschemeIso e).inv J) [])).toSequenceOfBlowups
        (A 0 ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e])).toSequenceOfBlowups :=
      (hdiv 0).pushforward ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e]) hT'valid
        hT'P hT'ord hT'db hT'j hT'm (imageIdealSheaf (kerSubschemeIso e).inv J) hVsub hDsub hIdsub
    have hS₂Q : Q (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
        (imageIdealSheaf (kerSubschemeIso e).inv J) []).krullDimSucc := hdimlink _ _ hDsub hP
    have hqε : (kerSubschemeIso e).inv ≫ (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
        (imageIdealSheaf (kerSubschemeIso e).inv J) []).structMap = q := by
      have h0 : (kerSubschemeIso e).inv
          ≫ ((Scheme.Hom.ker e).subschemeι ≫ T.structMap) = q := by
        rw [← Category.assoc, hεe]
        exact hq
      exact h0
    have htripleeq : ((T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
        (imageIdealSheaf (kerSubschemeIso e).inv J) []).pullbackAlong Y q
          (kerSubschemeIso e).inv).withBoundary []
        = T.withSchemeIdealBoundary Y q J [] := by
      show T.withSchemeIdealBoundary Y q
          ((imageIdealSheaf (kerSubschemeIso e).inv J).comap (kerSubschemeIso e).inv) []
        = T.withSchemeIdealBoundary Y q J []
      rw [comap_imageIdealSheaf]
    have hbe : MarkedIdealWithBoundary.SameNontrivialBoundary
        ((T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
          ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
          (imageIdealSheaf (kerSubschemeIso e).inv J) []).pullbackAlong Y q
            (kerSubschemeIso e).inv).boundary [] :=
      MarkedIdealWithBoundary.SameNontrivialBoundary.refl []
    have hvalid' : (((T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
        (imageIdealSheaf (kerSubschemeIso e).inv J) []).pullbackAlong Y q
          (kerSubschemeIso e).inv).withBoundary []).IsAdmissible := by
      rw [htripleeq]
      exact hJvalid
    have hQ' : Q (((T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
        (imageIdealSheaf (kerSubschemeIso e).inv J) []).pullbackAlong Y q
          (kerSubschemeIso e).inv).withBoundary []).krullDimSucc := by
      rw [htripleeq]
      exact hQdim
    have hstrict := @IsMaxOrderReduction.smooth_pullback_strict Q L L' hlow
      (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
        (imageIdealSheaf (kerSubschemeIso e).inv J) []) hVsub hS₂Q Y q ((kerSubschemeIso e).inv)
      hsmInv hsuInv hqε [] hbe hvalid' hQ'
    have hLeq : (L (((T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
        (imageIdealSheaf (kerSubschemeIso e).inv J) []).pullbackAlong Y q
          (kerSubschemeIso e).inv).withBoundary [])).toSequenceOfBlowups
        = (L (T.withSchemeIdealBoundary Y q J [])).toSequenceOfBlowups :=
      eq_of_heq (toSequenceOfBlowups_heq_of_eq_consolidated379 htripleeq L)
    have hstrict2 : IsStrictPullbackBlowupSeq ((kerSubschemeIso e).inv)
        (L (T.withSchemeIdealBoundary Y q J [])).toSequenceOfBlowups
        (L (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
            ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
            (imageIdealSheaf (kerSubschemeIso e).inv J) [])).toSequenceOfBlowups := by
      rw [← hLeq]
      exact hstrict
    have hpushY : IsPushforwardBlowupSeq e (L (T.withSchemeIdealBoundary Y q J [])).toSequenceOfBlowups
        (A 0 ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e])).toSequenceOfBlowups :=
      IsPushforwardBlowupSeq.isIso_comp (kerSubschemeIso e).inv (Scheme.Hom.ker e).subschemeι e
        hεe.symm hstrict2 hpushD
    exact IsPushforwardBlowupSeq.of_isomorphic e hpushY hequiv2

end MaxContactFunctoriality

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactOrderReduction
section



namespace MaxContactFunctoriality

section
variable (hinv : ComapIsoInvariance.{u})

theorem isOrderReduction_maxContact_of_descentHypotheses
    (P Q : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})
    (L L' : PrincipalizationAssignment.{u})
    (hdimlink : ∀ a b : ℕ, a < b → P b → Q a)
    (hlow : IsMaxOrderReduction Q L L')
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) L)
    (hstar : CoverSequenceProperties hinv P A)
    (hdes : DescentHypotheses hinv P A L) :
    IsOrderReduction P (maxContactPrincipalization hinv A) L := by
  refine
    { cert := ?_, base_change := ?_, base_change_strict := ?_, pushforward := ?_,
      order_le := ?_, center_nonempty := ?_, resolves := ?_, smooth_pullback := ?_,
      smooth_pullback_strict := ?_, trivial_of_coSupport_empty := ?_ }
  · intro T hv hdim hO i hi
    exact orderCertificate_of_orderAt_le_mult hinv P A L hstar hdes T hv hdim
      ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) i hi
  · intro T hv hdim hO K _ _ f E' hBE hV' hP' hO'
    have hord : ∀ x : ↥((T.baseChange K f).withBoundary E').scheme,
        orderAt ((T.baseChange K f).withBoundary E').ideal x ≤ (T.mult : ℕ∞) := by
      intro x
      have h := (MarkedIdealWithBoundary.isOrderBoundedByMult_iff ((T.baseChange K f).withBoundary E')).mp hO' x
      rwa [MarkedIdealWithBoundary.withBoundary_mult, MarkedIdealWithBoundary.baseChange_mult] at h
    exact hdes.base_change T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) K f E' hBE hV'
      hP' hord
  · intro T hv hdim hO K _ _ f E' hBE hV' hP' hO'
    have hord : ∀ x : ↥((T.baseChange K f).withBoundary E').scheme,
        orderAt ((T.baseChange K f).withBoundary E').ideal x ≤ (T.mult : ℕ∞) := by
      intro x
      have h := (MarkedIdealWithBoundary.isOrderBoundedByMult_iff ((T.baseChange K f).withBoundary E')).mp hO' x
      rwa [MarkedIdealWithBoundary.withBoundary_mult, MarkedIdealWithBoundary.baseChange_mult] at h
    exact hdes.base_change_strict T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) K f E' hBE
      hV' hP' hord
  · intro T hv hdim hO hbdry hmult Y q e _ hq hsm J hJv hJd hJi
    exact isPushforward_of_isSmoothDivisor hinv P Q A L L' hstar hdes hdiv hlow hdimlink T hv hdim hO
      hbdry hmult Y q e hq hsm J hJv hJd hJi
  · intro T hv hdim hO i hi x
    exact orderAt_ideal_le_mult hinv P A L hdes T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) i hi x
  · intro T hv hdim hO i hi
    exact center_support_nonempty hinv P A L hstar hdes T hv hdim
      ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) i hi
  · intro T hv hdim hO
    exact isResolution_of_orderAt_le_mult hinv P A L hstar hdes T hv hdim
      ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO)
  · intro T hv hdim hO Y q g _ hq E' hBE hV' hP' hO'
    have hm : ((T.pullbackAlong Y q g).withBoundary E').mult = T.mult :=
      (MarkedIdealWithBoundary.withBoundary_mult (T.pullbackAlong Y q g) E').trans
        (T.pullbackAlong_mult Y q g)
    have hord : ∀ x : ↥((T.pullbackAlong Y q g).withBoundary E').scheme,
        orderAt ((T.pullbackAlong Y q g).withBoundary E').ideal x ≤ (T.mult : ℕ∞) := by
      intro x
      have h := (MarkedIdealWithBoundary.isOrderBoundedByMult_iff ((T.pullbackAlong Y q g).withBoundary E')).mp hO' x
      rwa [hm] at h
    exact hdes.smooth_pullback T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) Y q g hq E' hBE
      hV' hP' hord
  · intro T hv hdim hO Y q g _ _ hq E' hBE hV' hP' hO'
    have hm : ((T.pullbackAlong Y q g).withBoundary E').mult = T.mult :=
      (MarkedIdealWithBoundary.withBoundary_mult (T.pullbackAlong Y q g) E').trans
        (T.pullbackAlong_mult Y q g)
    have hord : ∀ x : ↥((T.pullbackAlong Y q g).withBoundary E').scheme,
        orderAt ((T.pullbackAlong Y q g).withBoundary E').ideal x ≤ (T.mult : ℕ∞) := by
      intro x
      have h := (MarkedIdealWithBoundary.isOrderBoundedByMult_iff ((T.pullbackAlong Y q g).withBoundary E')).mp hO' x
      rwa [hm] at h
    exact hdes.smooth_pullback_strict T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) Y q g hq
      E' hBE hV' hP' hord
  · intro T hv hdim hO hemp
    exact length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P A T hv hdim
      ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) hemp

theorem isOrderReduction_maxContact_dim_le_of_descentHypotheses
    (n : ℕ) (A : ℕ → PrincipalizationAssignment.{u})
    (L L' : PrincipalizationAssignment.{u})
    (hlow : IsMaxOrderReduction (fun d => d < n) L L')
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L)
    (hstar : CoverSequenceProperties hinv (fun d => d ≤ n) A)
    (hdes : DescentHypotheses hinv (fun d => d ≤ n) A L) :
    IsOrderReduction (fun d => d ≤ n) (maxContactPrincipalization hinv A) L :=
  isOrderReduction_maxContact_of_descentHypotheses hinv (fun d => d ≤ n) (fun d => d < n) A L L'
    (fun _ _ hab hb => lt_of_lt_of_le hab hb) hlow hdiv hstar hdes


end

end MaxContactFunctoriality

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MaxOrder
section


section

section

variable {X : Scheme.{u}}

section
variable (N : X.IdealSheafData) {B : ℕ} (hB : ∀ x : ↥X, orderAt N x ≤ (B : ℕ∞))
include hB

theorem bddAbove_setOf_le_orderAt :
    BddAbove {n : ℕ | ∃ x : ↥X, (n : ℕ∞) ≤ orderAt N x} := by
  refine ⟨B, ?_⟩
  intro n hn
  obtain ⟨x, hx⟩ := hn
  have hnB : (n : ℕ∞) ≤ (B : ℕ∞) := le_trans hx (hB x)
  exact_mod_cast hnB

theorem orderAt_le_maxOrder (x : ↥X) :
    orderAt N x ≤ ((maxOrder N : ℕ) : ℕ∞) := by
  have hxB : orderAt N x ≤ (B : ℕ∞) := hB x
  have hBtop : (B : ℕ∞) ≠ ⊤ := by simp
  have hne : orderAt N x ≠ ⊤ := by
    intro h
    rw [h] at hxB
    exact hBtop (top_le_iff.mp hxB)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
  have hmem : ∃ y : ↥X, (m : ℕ∞) ≤ orderAt N y := ⟨x, hm.le⟩
  have hle : m ≤ maxOrder N := le_csSup (bddAbove_setOf_le_orderAt N hB) hmem
  rw [← hm]
  exact_mod_cast hle


end

section
variable [Nonempty ↥X] (N : X.IdealSheafData) {B : ℕ} (hB : ∀ x : ↥X, orderAt N x ≤ (B : ℕ∞))
include hB

theorem exists_orderAt_eq_maxOrder :
    ∃ x : ↥X, orderAt N x = ((maxOrder N : ℕ) : ℕ∞) := by
  have hbdd : BddAbove {n : ℕ | ∃ x : ↥X, (n : ℕ∞) ≤ orderAt N x} := bddAbove_setOf_le_orderAt N hB
  have hnonempty : {n : ℕ | ∃ x : ↥X, (n : ℕ∞) ≤ orderAt N x}.Nonempty := by
    obtain ⟨x₀⟩ := ‹Nonempty ↥X›
    exact ⟨0, x₀, by simp⟩
  obtain ⟨x, hx⟩ := Nat.sSup_mem hnonempty hbdd
  have hdef : maxOrder N = sSup {n : ℕ | ∃ x : ↥X, (n : ℕ∞) ≤ orderAt N x} := rfl
  refine ⟨x, ?_⟩
  rw [hdef]
  refine le_antisymm ?_ hx
  have hordle : orderAt N x ≤ (B : ℕ∞) := hB x
  have hne_top : orderAt N x ≠ ⊤ := by
    intro h
    rw [h] at hordle
    simp at hordle
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne_top
  have hmemn : n ∈ {n : ℕ | ∃ x : ↥X, (n : ℕ∞) ≤ orderAt N x} := ⟨x, le_of_eq hn⟩
  have hle : n ≤ sSup {n : ℕ | ∃ x : ↥X, (n : ℕ∞) ≤ orderAt N x} := le_csSup hbdd hmemn
  calc orderAt N x = (n : ℕ∞) := hn.symm
    _ ≤ ((sSup {n : ℕ | ∃ x : ↥X, (n : ℕ∞) ≤ orderAt N x} : ℕ) : ℕ∞) := by exact_mod_cast hle

theorem orderAtLeastLocus_maxOrder_nonempty :
    (orderAtLeastLocus N (maxOrder N)).Nonempty := by
  obtain ⟨x, hx⟩ := exists_orderAt_eq_maxOrder N hB
  exact ⟨x, (mem_orderAtLeastLocus_iff N (maxOrder N) x).mpr hx.ge⟩


end

section
variable (N : X.IdealSheafData) {B : ℕ}

theorem orderAt_lt_of_maxOrder_lt (hB : ∀ x : ↥X, orderAt N x ≤ (B : ℕ∞)) {c : ℕ} (hc : maxOrder N < c) (x : ↥X) :
    orderAt N x < (c : ℕ∞) := by
  have h1 : orderAt N x ≤ ((maxOrder N : ℕ) : ℕ∞) := orderAt_le_maxOrder N hB x
  have h2 : ((maxOrder N : ℕ) : ℕ∞) < (c : ℕ∞) := by exact_mod_cast hc
  exact lt_of_le_of_lt h1 h2

theorem maxOrder_lt_of_orderAtLeastLocus_eq_empty (_hB : ∀ x : ↥X, orderAt N x ≤ (B : ℕ∞)) {c : ℕ} (hc : 1 ≤ c)
    (h : orderAtLeastLocus N c = ∅) :
    maxOrder N < c := by
  have key : maxOrder N ≤ c - 1 := by
    show sSup {n : ℕ | ∃ x : ↥X, (n : ℕ∞) ≤ orderAt N x} ≤ c - 1
    refine csSup_le' ?_
    intro n hn
    obtain ⟨x, hx⟩ := hn
    have hlt : ¬ ((c : ℕ∞) ≤ orderAt N x) := by
      intro hcon
      have hmem : x ∈ orderAtLeastLocus N c := (mem_orderAtLeastLocus_iff N c x).mpr hcon
      rw [h] at hmem
      simp at hmem
    have hnc : n < c := by
      by_contra hcon
      have hcon' : c ≤ n := Nat.le_of_not_lt hcon
      have hcast : (c : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hcon'
      exact hlt (le_trans hcast hx)
    omega
  omega


end

end

section

variable {X : Scheme.{u}}

section
variable (N : X.IdealSheafData) {B : ℕ} (hB : ∀ x : ↥X, orderAt N x ≤ (B : ℕ∞)) (S : Set ↥X)
include hB

theorem bddAbove_setOf_le_orderAt_of_mem :
    BddAbove {n : ℕ | ∃ x ∈ S, (n : ℕ∞) ≤ orderAt N x} := by
  refine ⟨B, ?_⟩
  intro n hn
  obtain ⟨x, _, hx⟩ := hn
  have hnB : (n : ℕ∞) ≤ (B : ℕ∞) := le_trans hx (hB x)
  exact_mod_cast hnB

theorem orderAt_le_maxOrderOn {x : ↥X} (hx : x ∈ S) :
    orderAt N x ≤ ((maxOrderOn N S : ℕ) : ℕ∞) := by
  have hxB : orderAt N x ≤ (B : ℕ∞) := hB x
  have hne : orderAt N x ≠ ⊤ := by
    intro h
    rw [h] at hxB
    simp at hxB
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
  have hmem : m ∈ {n : ℕ | ∃ y ∈ S, (n : ℕ∞) ≤ orderAt N y} := ⟨x, hx, hm.le⟩
  have hle : m ≤ maxOrderOn N S := le_csSup (bddAbove_setOf_le_orderAt_of_mem N hB S) hmem
  rw [← hm]
  exact_mod_cast hle


end

section
variable (N : X.IdealSheafData) {B : ℕ}

theorem maxOrderOn_lt_of_forall_lt (_hB : ∀ x : ↥X, orderAt N x ≤ (B : ℕ∞)) (S : Set ↥X) {c : ℕ} (hc : 1 ≤ c)
    (h : ∀ x ∈ S, orderAt N x < (c : ℕ∞)) :
    maxOrderOn N S < c := by
  have key : maxOrderOn N S ≤ c - 1 := by
    show sSup {n : ℕ | ∃ x ∈ S, (n : ℕ∞) ≤ orderAt N x} ≤ c - 1
    refine csSup_le' ?_
    intro n hn
    obtain ⟨x, hxS, hx⟩ := hn
    have hlt : (n : ℕ∞) < (c : ℕ∞) := lt_of_le_of_lt hx (h x hxS)
    have hnc : n < c := by exact_mod_cast hlt
    omega
  omega

theorem maxOrderOn_eq_zero_iff (hB : ∀ x : ↥X, orderAt N x ≤ (B : ℕ∞)) (S : Set ↥X) :
    maxOrderOn N S = 0 ↔ ∀ x ∈ S, orderAt N x = 0 := by
  constructor
  · intro h x hx
    have h1 : orderAt N x ≤ ((maxOrderOn N S : ℕ) : ℕ∞) :=
      orderAt_le_maxOrderOn N hB S hx
    rw [h] at h1
    have h2 : orderAt N x ≤ (0 : ℕ∞) := by exact_mod_cast h1
    exact nonpos_iff_eq_zero.mp h2
  · intro h
    have hub : (0 : ℕ) ∈ upperBounds {n : ℕ | ∃ x ∈ S, (n : ℕ∞) ≤ orderAt N x} := by
      intro n hn
      obtain ⟨x, hxS, hx⟩ := hn
      rw [h x hxS] at hx
      have hn0 : (n : ℕ∞) = 0 := nonpos_iff_eq_zero.mp hx
      have hn1 : n = 0 := by exact_mod_cast hn0
      omega
    have key : maxOrderOn N S ≤ 0 := by
      show sSup {n : ℕ | ∃ x ∈ S, (n : ℕ∞) ≤ orderAt N x} ≤ 0
      exact csSup_le' hub
    omega


end

end

section

variable {X : Scheme.{u}}

theorem orderAtLeastLocus_sup (A J : X.IdealSheafData) (c : ℕ) :
    orderAtLeastLocus (A ⊔ J) c = orderAtLeastLocus A c ∩ orderAtLeastLocus J c := by
  ext x
  simp only [Set.mem_inter_iff, mem_orderAtLeastLocus_iff, orderAt_sup, le_min_iff]

section
variable (k : Type u) [Field k] [CharZero k] (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (N I : X.IdealSheafData)
include p

theorem orderAt_pow_sup_pow (m s : ℕ) (x : ↥X) :
    orderAt (N ^ m ⊔ I ^ s) x
      = min ((m : ℕ∞) * orderAt N x) ((s : ℕ∞) * orderAt I x) := by
  rw [orderAt_sup, orderAt_pow k p, orderAt_pow k p]

theorem orderAtLeastLocus_pow_sup_pow {m s : ℕ} (hm : 1 ≤ m) (hs : 1 ≤ s) :
    orderAtLeastLocus (N ^ m ⊔ I ^ s) (m * s) = orderAtLeastLocus N s ∩ orderAtLeastLocus I m := by
  rw [orderAtLeastLocus_sup, orderAtLeastLocus_pow_mul k p N hm s, mul_comm m s,
    orderAtLeastLocus_pow_mul k p I hs m]

theorem orderAt_pow_sup_pow_le (m s : ℕ)
    (h : ∀ x ∈ orderAtLeastLocus I m, orderAt N x ≤ (s : ℕ∞)) (x : ↥X) :
    orderAt (N ^ m ⊔ I ^ s) x ≤ ((m * s : ℕ) : ℕ∞) := by
  rw [orderAt_pow_sup_pow k p N I m s x]
  by_cases hx : x ∈ orderAtLeastLocus I m
  · refine le_trans (min_le_left _ _) ?_
    have h1 : orderAt N x ≤ (s : ℕ∞) := h x hx
    calc (m : ℕ∞) * orderAt N x ≤ (m : ℕ∞) * (s : ℕ∞) := by gcongr
      _ = ((m * s : ℕ) : ℕ∞) := by rw [Nat.cast_mul]
  · refine le_trans (min_le_right _ _) ?_
    have hle : orderAt I x ≤ (m : ℕ∞) :=
      le_of_lt (not_le.mp (fun hc => hx ((mem_orderAtLeastLocus_iff I m x).mpr hc)))
    calc (s : ℕ∞) * orderAt I x ≤ (s : ℕ∞) * (m : ℕ∞) := by gcongr
      _ = ((m * s : ℕ) : ℕ∞) := by rw [Nat.cast_mul]; exact mul_comm _ _

theorem orderAtLeastLocus_pow_sup_pow_eq_empty_iff {m s : ℕ} (hm : 1 ≤ m) (hs : 1 ≤ s) :
    orderAtLeastLocus (N ^ m ⊔ I ^ s) (m * s) = ∅ ↔ ∀ x ∈ orderAtLeastLocus I m, orderAt N x < (s : ℕ∞) := by
  rw [orderAtLeastLocus_pow_sup_pow k p N I hm hs]
  constructor
  · intro h x hx
    by_contra hcon
    have hcon' : (s : ℕ∞) ≤ orderAt N x := not_lt.mp hcon
    have hmem : x ∈ orderAtLeastLocus N s ∩ orderAtLeastLocus I m :=
      ⟨(mem_orderAtLeastLocus_iff N s x).mpr hcon', hx⟩
    rw [h] at hmem
    exact hmem.elim
  · intro h
    ext x
    constructor
    · intro hx
      exact absurd ((mem_orderAtLeastLocus_iff N s x).mp hx.1) (not_le.mpr (h x hx.2))
    · intro hx
      exact hx.elim


end

end

section

variable {X Y : Scheme.{u}}

theorem image_orderAtLeastLocus_comap_subset (k : Type u) [Field k] [CharZero k]
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (h : Y ⟶ X) [Smooth h] (N : X.IdealSheafData) (c : ℕ) :
    ⇑h.base '' orderAtLeastLocus (N.comap h) c ⊆ orderAtLeastLocus N c := by
  rw [orderAtLeastLocus_comap k p h N c]
  exact Set.image_preimage_subset _ _

end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.PrincipalizationCenter
section


section

namespace MarkedSchemeWithCenter

variable {k : Type u} [Field k]

def boundarySupport (D : MarkedSchemeWithCenter.{u} k) : Set ↥D.ambient :=
  {x : ↥D.ambient | ∃ J ∈ D.boundary, x ∈ (↑J.support : Set ↥D.ambient)}

theorem mem_boundarySupport_iff (D : MarkedSchemeWithCenter.{u} k) (x : ↥D.ambient) :
    x ∈ D.boundarySupport ↔ ∃ J ∈ D.boundary, x ∈ (↑J.support : Set ↥D.ambient) :=
  Iff.rfl

end MarkedSchemeWithCenter

theorem mem_comap_support_iff_base_mem_support {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) (x : ↥X) :
    x ∈ (J.comap f).support ↔ f.base x ∈ J.support := by
  simp only [Scheme.IdealSheafData.support_comap]
  exact Iff.rfl

namespace MarkedSchemeWithCenter

variable {k : Type u} [Field k]

theorem boundarySupport_transport (D : MarkedSchemeWithCenter.{u} k) {A : Scheme.{u}} (e : A ≅ D.ambient) :
    (D.transport e).boundarySupport = e.hom.base ⁻¹' D.boundarySupport := by
  ext x
  constructor
  · rintro ⟨J, hJ, hx⟩
    obtain ⟨K, hK, rfl⟩ := List.mem_map.1 hJ
    exact ⟨K, hK, (mem_comap_support_iff_base_mem_support e.hom K x).1 hx⟩
  · rintro ⟨K, hK, hx⟩
    exact ⟨K.comap e.hom, List.mem_map.2 ⟨K, hK, rfl⟩,
      (mem_comap_support_iff_base_mem_support e.hom K x).2 hx⟩

end MarkedSchemeWithCenter

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

theorem boundarySupport_dataAt (s : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    (s.dataAt i).boundarySupport = s.toMarkedSequenceOfBlowups.boundaryLocus i := by
  ext x
  refine Iff.trans (MarkedSchemeWithCenter.mem_boundarySupport_iff (s.dataAt i) x) ?_
  exact (MarkedSequenceOfBlowups.mem_boundaryLocus_iff s.toMarkedSequenceOfBlowups i x).symm

end MarkedBlowupSequenceData

structure HasPrincipalizationCenter {k : Type u} [Field k] (μ : ℕ) (D : MarkedSchemeWithCenter.{u} k) : Prop where
  center_nonempty : (↑D.center.support : Set ↥D.ambient).Nonempty
  cert : PrincipalizationCertificate D.ambient D.structMap D.ideal μ D.boundarySupport D.center

theorem isInvariantUnderIso_hasPrincipalizationCenter {k : Type u} [Field k] (hT : OrderCertificateIsoInvariantOfMaxContact.{u}) (μ : ℕ) :
    IsInvariantUnderIso (fun D : MarkedSchemeWithCenter.{u} k => HasPrincipalizationCenter μ D) := by
  intro D A e hD
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hD.center_nonempty
    refine ⟨e.inv.base x, ?_⟩
    have key : e.hom.base (e.inv.base x) = x := by
      simp
    have hmem : e.hom.base (e.inv.base x) ∈ D.center.support := by
      rw [key]; exact hx
    exact (mem_comap_support_iff_base_mem_support e.hom D.center (e.inv.base x)).2 hmem
  · have hcert := PrincipalizationCertificate.comap_iso hT e hD.cert
    rw [MarkedSchemeWithCenter.boundarySupport_transport]
    exact hcert

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

theorem nonempty_center_and_certificate_of_hasPrincipalizationCenter (s : MarkedBlowupSequenceData p I m E) (μ : ℕ)
    (hs : ∀ i < s.toBlowupSequenceData.length, HasPrincipalizationCenter μ (s.dataAt i)) :
    (∀ i < s.toMarkedSequenceOfBlowups.length,
        (↑(s.toMarkedSequenceOfBlowups.center i).support : Set ↥(s.toMarkedSequenceOfBlowups.schemeAt i)).Nonempty) ∧
      (∀ i < s.toMarkedSequenceOfBlowups.length,
        PrincipalizationCertificate (s.toMarkedSequenceOfBlowups.schemeAt i) (s.toMarkedSequenceOfBlowups.projectionToSpec i) (s.toMarkedSequenceOfBlowups.ideal i) μ
          (s.toMarkedSequenceOfBlowups.boundaryLocus i) (s.toMarkedSequenceOfBlowups.center i)) := by
  constructor
  · intro i hi
    have hi' : i < s.toBlowupSequenceData.length := by
      rw [← s.toMarkedSequence_length]; exact hi
    exact (hs i hi').center_nonempty
  · intro i hi
    have hi' : i < s.toBlowupSequenceData.length := by
      rw [← s.toMarkedSequence_length]; exact hi
    have h := (hs i hi').cert
    rw [s.boundarySupport_dataAt i] at h
    rw [toMarkedSequence_projectionToSpec]
    exact h

end MarkedBlowupSequenceData


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequencePrefix
section


section

private theorem comap_eqToHom_self_consolidated276 {X : Scheme.{u}} (h : X = X) (J : X.IdealSheafData) :
    J.comap (eqToHom h) = J := by
  simp

private theorem comap_eqToHom_trans_consolidated276 {X Y Z : Scheme.{u}} (h1 : X = Y) (h2 : Y = Z)
    (J : Z.IdealSheafData) :
    (J.comap (eqToHom h2)).comap (eqToHom h1) = J.comap (eqToHom (h1.trans h2)) := by
  subst h1
  subst h2
  simp

private theorem map_comap_eqToHom_self_consolidated276 {X : Scheme.{u}} (h : X = X) (L : List X.IdealSheafData) :
    List.map (fun D => D.comap (eqToHom h)) L = L := by
  induction L with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, ih, comap_eqToHom_self_consolidated276]

private theorem map_comap_eqToHom_trans_consolidated276 {X Y Z : Scheme.{u}} (h1 : X = Y) (h2 : Y = Z)
    (L : List Z.IdealSheafData) :
    List.map (fun D => D.comap (eqToHom h1)) (List.map (fun D => D.comap (eqToHom h2)) L)
      = List.map (fun D => D.comap (eqToHom (h1.trans h2))) L := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, ih, comap_eqToHom_trans_consolidated276]

private theorem eq_eqToHom_comp_of_eq_eqToHom_symm_comp_consolidated276 {A B C : Scheme.{u}} (f : A ⟶ C) (g : B ⟶ C) (h : A = B)
    (hg : g = eqToHom h.symm ≫ f) : f = eqToHom h ≫ g := by
  subst h
  simp only [eqToHom_refl, Category.id_comp] at hg ⊢
  exact hg.symm

section
variable {X : Scheme.{u}} {d d' : BlowupSequenceData X} (hd : d = d') (i : ℕ)
include hd

private theorem blowupSequenceData_center_eq_comap_eqToHom_consolidated276 (hobj : d.obj i = d'.obj i) :
    d.center i = (d'.center i).comap (eqToHom hobj) := by
  subst hd
  exact (comap_eqToHom_self_consolidated276 hobj _).symm

private theorem blowupSequenceData_blowupMorphism_comp_eqToHom_consolidated276 (h0 : d.obj i = d'.obj i) (h1 : d.obj (i + 1) = d'.obj (i + 1)) :
    d.map i ≫ eqToHom h0 = eqToHom h1 ≫ d'.map i := by
  subst hd
  simp


end

private theorem comp_eqToHom_eq_eqToHom_comp_of_eqToHom_conj_consolidated276 {A B A' B' A'' B'' : Scheme.{u}}
    (f : A ⟶ B) (M : A'' ⟶ B'') (N : A' ⟶ B')
    (c0 : B'' = B') (c1 : A'' = A') (a : A' = A) (b : B = B')
    (hi0 : B = B'') (hi1 : A = A'')
    (key0 : M ≫ eqToHom c0 = eqToHom c1 ≫ N)
    (L : N = eqToHom a ≫ f ≫ eqToHom b) :
    f ≫ eqToHom hi0 = eqToHom hi1 ≫ M := by
  subst b
  subst c0
  subst a
  subst c1
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at key0 L ⊢
  exact L.symm.trans key0.symm

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

structure IsPrefix (s t : MarkedBlowupSequenceData p I m E) : Prop where
  length_le : s.length ≤ t.length
  obj_eq : ∀ i ≤ s.length, s.obj i = t.obj i
  proj_eq : ∀ (i : ℕ) (hi : i ≤ s.length), s.proj i = eqToHom (obj_eq i hi) ≫ t.proj i
  ideal_eq : ∀ (i : ℕ) (hi : i ≤ s.length),
    s.ideal i = (t.ideal i).comap (eqToHom (obj_eq i hi))
  boundary_eq : ∀ (i : ℕ) (hi : i ≤ s.length),
    s.boundary i = List.map (fun D => D.comap (eqToHom (obj_eq i hi))) (t.boundary i)
  center_eq : ∀ (i : ℕ) (hi : i < s.length),
    s.center i = (t.center i).comap (eqToHom (obj_eq i (Nat.le_of_lt hi)))
  map_eq : ∀ (i : ℕ) (hi : i < s.length),
    s.map i ≫ eqToHom (obj_eq i (Nat.le_of_lt hi)) =
      eqToHom (obj_eq (i + 1) (Nat.succ_le_of_lt hi)) ≫ t.map i

theorem IsPrefix.refl (s : MarkedBlowupSequenceData p I m E) : s.IsPrefix s := by
  refine ⟨le_rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp
  · intro i hi
    exact (comap_eqToHom_self_consolidated276 _ _).symm
  · intro i hi
    exact (map_comap_eqToHom_self_consolidated276 _ _).symm
  · intro i hi
    exact (comap_eqToHom_self_consolidated276 _ _).symm
  · intro i hi
    simp

theorem IsPrefix.trans {s t r : MarkedBlowupSequenceData p I m E} (h : s.IsPrefix t)
    (h' : t.IsPrefix r) : s.IsPrefix r := by
  have hlen : s.length ≤ t.length := h.length_le
  have hobj : ∀ i ≤ s.length, s.obj i = r.obj i := fun i hi =>
    (h.obj_eq i hi).trans (h'.obj_eq i (hi.trans hlen))
  refine ⟨hlen.trans h'.length_le, hobj, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [h.proj_eq i hi, h'.proj_eq i (hi.trans hlen), ← Category.assoc, eqToHom_trans]
  · intro i hi
    rw [h.ideal_eq i hi, h'.ideal_eq i (hi.trans hlen), comap_eqToHom_trans_consolidated276]
  · intro i hi
    rw [h.boundary_eq i hi, h'.boundary_eq i (hi.trans hlen), map_comap_eqToHom_trans_consolidated276]
  · intro i hi
    rw [h.center_eq i hi, h'.center_eq i (lt_of_lt_of_le hi hlen), comap_eqToHom_trans_consolidated276]
  · intro i hi
    have hi' : i < t.length := lt_of_lt_of_le hi hlen
    rw [← eqToHom_trans (h.obj_eq i (Nat.le_of_lt hi)) (h'.obj_eq i (Nat.le_of_lt hi')),
      ← eqToHom_trans (h.obj_eq (i + 1) (Nat.succ_le_of_lt hi))
        (h'.obj_eq (i + 1) (Nat.succ_le_of_lt hi')),
      ← Category.assoc, h.map_eq i hi, Category.assoc, h'.map_eq i hi', ← Category.assoc]

theorem isPrefix_append (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (hinv : ComapIsoInvariance.{u}) : s.IsPrefix (s.append t hinv) := by
  have hobj : ∀ i ≤ s.length, s.obj i = (s.append t hinv).obj i := fun i hi =>
    (s.append_schemeAt_of_le_length t hinv hi).symm
  have hbd : (s.append t hinv).toBlowupSequenceData = s.appendToBlowupSequenceData t := s.append_toBlowupSequenceData t hinv
  refine ⟨?_, hobj, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MarkedBlowupSequenceData.append_length]
    exact Nat.le_add_right _ _
  · intro i hi
    have key : (s.append t hinv).proj i = eqToHom (hobj i hi).symm ≫ s.proj i := by
      rw [s.append_projectionToBase t hinv i]
      exact s.appendProjectionToBase_of_le_length t hi
    exact eq_eqToHom_comp_of_eq_eqToHom_symm_comp_consolidated276 (s.proj i) ((s.append t hinv).proj i) (hobj i hi) key
  · intro i hi
    have key : (s.append t hinv).ideal i = (s.ideal i).comap (eqToHom (hobj i hi).symm) := by
      rw [s.append_ideal t hinv i]
      exact s.appendIdeal_of_le_length t hi
    rw [key, comap_eqToHom_trans_consolidated276, comap_eqToHom_self_consolidated276]
  · intro i hi
    have key : (s.append t hinv).boundary i =
        List.map (fun D => D.comap (eqToHom (hobj i hi).symm)) (s.boundary i) := by
      rw [s.append_boundary t hinv i]
      exact s.appendBoundary_of_le_length t hi
    rw [key, map_comap_eqToHom_trans_consolidated276, map_comap_eqToHom_self_consolidated276]
  · intro i hi
    rw [blowupSequenceData_center_eq_comap_eqToHom_consolidated276 hbd i (congrArg (fun d => BlowupSequenceData.obj d i) hbd),
      s.appendToBlowupSequenceData_center_of_lt_length t hi, comap_eqToHom_trans_consolidated276, comap_eqToHom_trans_consolidated276, comap_eqToHom_self_consolidated276]
  · intro i hi
    have c0 : (s.append t hinv).obj i = (s.appendToBlowupSequenceData t).obj i :=
      congrArg (fun d => BlowupSequenceData.obj d i) hbd
    have c1 : (s.append t hinv).obj (i + 1) = (s.appendToBlowupSequenceData t).obj (i + 1) :=
      congrArg (fun d => BlowupSequenceData.obj d (i + 1)) hbd
    exact comp_eqToHom_eq_eqToHom_comp_of_eqToHom_conj_consolidated276 (s.map i) ((s.append t hinv).map i) ((s.appendToBlowupSequenceData t).map i)
      c0 c1 _ _ _ _ (blowupSequenceData_blowupMorphism_comp_eqToHom_consolidated276 hbd i c0 c1) (s.appendToBlowupSequenceData_blowupMorphism_of_lt_length t hi)

end MarkedBlowupSequenceData

section

def lastNonMonomialPart (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    (s.obj s.length).IdealSheafData :=
  nonMonomialPart (s.boundary s.length) (s.ideal s.length)

def maxOrderNonMonomial (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) : ℕ :=
  maxOrder (lastNonMonomialPart T s)

def NonMonomialOrderReductionContinues (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) : Prop :=
  T.mult ≤ maxOrderNonMonomial T s ∧
    (orderAtLeastLocus (lastNonMonomialPart T s) (maxOrderNonMonomial T s)).Nonempty

theorem nonMonomialOrderReductionContinues_iff (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    NonMonomialOrderReductionContinues T s ↔
      T.mult ≤ maxOrderNonMonomial T s ∧
        (orderAtLeastLocus (lastNonMonomialPart T s) (maxOrderNonMonomial T s)).Nonempty :=
  Iff.rfl

def maxOrderNonMonomialOnOrderLocus (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) : ℕ :=
  maxOrderOn (lastNonMonomialPart T s) (orderAtLeastLocus (s.ideal s.length) T.mult)

def CompanionIdealReductionContinues (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) : Prop :=
  1 ≤ maxOrderNonMonomialOnOrderLocus T s

theorem companionIdealReductionContinues_iff (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    CompanionIdealReductionContinues T s ↔ 1 ≤ maxOrderNonMonomialOnOrderLocus T s :=
  Iff.rfl

def companionIdeal (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    (s.obj s.length).IdealSheafData :=
  lastNonMonomialPart T s ^ T.mult ⊔ s.ideal s.length ^ maxOrderNonMonomialOnOrderLocus T s

theorem tripleAtLength_dim (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ) :
    (tripleAtLength T s J μ).krullDimSucc = krullDimSucc (s.obj s.length) :=
  rfl

end

section

def principalizationSeqAtEnd (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (hd : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc) :
    MarkedSequenceOfBlowups (s.proj s.length ≫ T.structMap) J μ (s.boundary s.length) :=
  rc (tripleAtLength T s J μ) hd

section
variable (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (J : (s.obj s.length).IdealSheafData) (μ : ℕ) (hd : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc)

theorem appendRecursivePrincipalization_eq_appendIfMarked :
    appendRecursivePrincipalization hinv T rc s J μ = appendIfMarked hinv s J μ (principalizationSeqAtEnd T rc s J μ hd) := by
  unfold appendRecursivePrincipalization principalizationSeqAtEnd
  rw [dif_pos hd]

theorem appendRecursivePrincipalization_eq_append (hm : (MarkedBlowupSequenceData.ofMarkedSequence (principalizationSeqAtEnd T rc s J μ hd)).toBlowupSequenceData.IsMarked
      (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length)) :
    appendRecursivePrincipalization hinv T rc s J μ =
      s.append
        ((MarkedBlowupSequenceData.ofMarkedSequence (principalizationSeqAtEnd T rc s J μ hd)).toBlowupSequenceData.toMarkedBlowupSequenceData
          (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length) hm)
        hinv := by
  have hr : markedDataOfSeq s J μ (principalizationSeqAtEnd T rc s J μ hd) =
      some ((MarkedBlowupSequenceData.ofMarkedSequence (principalizationSeqAtEnd T rc s J μ hd)).toBlowupSequenceData.toMarkedBlowupSequenceData
        (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length) hm) := by
    unfold markedDataOfSeq
    exact dif_pos hm
  rw [appendRecursivePrincipalization_eq_appendIfMarked hinv T rc s J μ hd]
  unfold appendIfMarked
  rw [hr]


end

end

section

variable (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
  (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)

def extendByNonMonomialPart (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
  appendRecursivePrincipalization hinv T rc s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)

def extendByCompanionIdeal (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
  appendRecursivePrincipalization hinv T rc s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)

theorem nonMonomialOrderReductionIter_zero :
    nonMonomialOrderReductionIter hinv T rc 0 = emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
  rfl

theorem nonMonomialOrderReductionIter_succ_of_continues (f : ℕ) (h : NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T rc f)) :
    nonMonomialOrderReductionIter hinv T rc (f + 1) = extendByNonMonomialPart hinv T rc (nonMonomialOrderReductionIter hinv T rc f) := by
  rw [nonMonomialOrderReductionIter]
  exact if_pos h

section
variable (f : ℕ) (h : ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T rc f))
include h

theorem nonMonomialOrderReductionIter_succ_of_not_continues :
    nonMonomialOrderReductionIter hinv T rc (f + 1) = nonMonomialOrderReductionIter hinv T rc f := by
  rw [nonMonomialOrderReductionIter]
  exact if_neg h

theorem nonMonomialOrderReductionIter_eq_of_not_continues :
    ∀ g, f ≤ g → nonMonomialOrderReductionIter hinv T rc g = nonMonomialOrderReductionIter hinv T rc f := by
  intro g hg
  induction g, hg using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have hn' : ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T rc n) := by
      rw [ih]
      exact h
    rw [nonMonomialOrderReductionIter_succ_of_not_continues hinv T rc n hn']
    exact ih


end

theorem nonMonomialOrderReduction_eq :
    nonMonomialOrderReduction hinv T rc =
      nonMonomialOrderReductionIter hinv T rc (maxOrder (nonMonomialPart T.boundary T.ideal) + 1) :=
  rfl

section
variable (s₀ : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)

theorem companionIdealReductionIter_zero :
    companionIdealReductionIter hinv T rc s₀ 0 = s₀ :=
  rfl

theorem companionIdealReductionIter_succ_of_continues (f : ℕ) (h : CompanionIdealReductionContinues T (companionIdealReductionIter hinv T rc s₀ f)) :
    companionIdealReductionIter hinv T rc s₀ (f + 1) =
      extendByCompanionIdeal hinv T rc (companionIdealReductionIter hinv T rc s₀ f) := by
  rw [companionIdealReductionIter]
  exact if_pos h

theorem companionIdealReductionIter_succ_of_not_continues
    (f : ℕ) (h : ¬ CompanionIdealReductionContinues T (companionIdealReductionIter hinv T rc s₀ f)) :
    companionIdealReductionIter hinv T rc s₀ (f + 1) = companionIdealReductionIter hinv T rc s₀ f := by
  rw [companionIdealReductionIter]
  exact if_neg h

theorem companionIdealReductionIter_eq_of_not_continues
    (f : ℕ) (h : ¬ CompanionIdealReductionContinues T (companionIdealReductionIter hinv T rc s₀ f)) :
    ∀ g, f ≤ g → companionIdealReductionIter hinv T rc s₀ g = companionIdealReductionIter hinv T rc s₀ f := by
  intro g hg
  induction g, hg using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have hn' : ¬ CompanionIdealReductionContinues T (companionIdealReductionIter hinv T rc s₀ n) := by
      rw [ih]
      exact h
    rw [companionIdealReductionIter_succ_of_not_continues hinv T rc s₀ n hn']
    exact ih


end

theorem companionIdealReduction_eq :
    companionIdealReduction hinv T rc =
      companionIdealReductionIter hinv T rc (nonMonomialOrderReduction hinv T rc)
        (maxOrderNonMonomialOnOrderLocus T (nonMonomialOrderReduction hinv T rc) + 1) :=
  rfl

theorem orderReductionData_eq :
    orderReductionData hinv T rc =
      (companionIdealReduction hinv T rc).append
        (MarkedBlowupSequenceData.ofMarkedSequence
          (monomialPrincipalization hinv
            (tripleAtLength T (companionIdealReduction hinv T rc)
              ((companionIdealReduction hinv T rc).ideal (companionIdealReduction hinv T rc).length) T.mult)))
        hinv :=
  rfl

theorem orderReductionSeq_eq_of_nonempty (h : (orderAtLeastLocus T.ideal T.mult).Nonempty) :
    orderReductionSeq hinv T rc = (orderReductionData hinv T rc).toMarkedSequenceOfBlowups := by
  unfold orderReductionSeq
  rw [if_neg h.ne_empty]

end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialBlowupIteration
section


section

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def monomialBlowupStep (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) :=
  ofSingleBlowup (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length)
    (centerAtLast s) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
theorem monomialBlowupStep_length (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).length = 1 :=
  ofSingleBlowup_length h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
theorem monomialBlowupStep_schemeAt_zero (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).obj 0 = s.obj s.length :=
  ofSingleBlowup_schemeAt_zero h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
theorem monomialBlowupStep_schemeAt_succ (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) (i : ℕ) :
    (monomialBlowupStep s h).obj (i + 1) = Blowup.blowup (centerAtLast s) :=
  ofSingleBlowup_schemeAt_succ h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 i

@[simp]
theorem monomialBlowupStep_center_zero (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).center 0 = centerAtLast s :=
  ofSingleBlowup_center_zero h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
theorem monomialBlowupStep_projectionToBase_one (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).proj 1 = Blowup.blowup.proj (centerAtLast s) :=
  ofSingleBlowup_projectionToBase_one h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
theorem monomialBlowupStep_ideal_one (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).ideal 1 =
      residualByPow ((s.ideal s.length).comap (Blowup.blowup.proj (centerAtLast s)))
        ((centerAtLast s).comap (Blowup.blowup.proj (centerAtLast s))) m :=
  ofSingleBlowup_ideal_one h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
theorem monomialBlowupStep_boundary_one (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).boundary 1 =
      List.map (Blowup.strictTransform (Blowup.blowup.proj (centerAtLast s)) (centerAtLast s))
          (s.boundary s.length) ++
        [Blowup.exceptionalIdeal (Blowup.blowup.proj (centerAtLast s)) (centerAtLast s)] :=
  ofSingleBlowup_boundary_one h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem monomialBlowupStep_isoObjZero_inv (s : MarkedBlowupSequenceData p I m E) (h : IsAdmissibleCenter s) :
    (monomialBlowupStep s h).isoZero.inv = eqToHom (monomialBlowupStep_schemeAt_zero s h).symm :=
  rfl

section
variable (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)

theorem blowupAtCenter_eq_append (h : IsAdmissibleCenter s) :
    blowupAtCenter hinv s = s.append (monomialBlowupStep s h) hinv := by
  unfold blowupAtCenter monomialBlowupStep
  rw [dif_pos h]

theorem blowupAtCenter_length (h : IsAdmissibleCenter s) :
    (blowupAtCenter hinv s).length = s.length + 1 := by
  rw [blowupAtCenter_eq_append hinv s h, append_length, monomialBlowupStep_length]

theorem isStationaryAt_iff_not_isAdmissibleCenter (n : ℕ) :
    IsStationaryAt hinv s n ↔ ¬ IsAdmissibleCenter (monomialBlowupIterate hinv s n) := by
  constructor
  · intro h hstep
    have hl := blowupAtCenter_length hinv (monomialBlowupIterate hinv s n) hstep
    have h' : (blowupAtCenter hinv (monomialBlowupIterate hinv s n)).length
        = (monomialBlowupIterate hinv s n).length := h
    rw [hl] at h'
    omega
  · intro h
    show (blowupAtCenter hinv (monomialBlowupIterate hinv s n)).length
        = (monomialBlowupIterate hinv s n).length
    unfold blowupAtCenter
    rw [dif_neg h]

theorem blowupAtCenter_schemeAt_succ (h : IsAdmissibleCenter s) :
    (blowupAtCenter hinv s).obj (s.length + 1) = Blowup.blowup (centerAtLast s) := by
  have hlt : s.length < s.length + 1 := Nat.lt_succ_self s.length
  rw [blowupAtCenter_eq_append hinv s h, append_schemeAt_of_length_lt s (monomialBlowupStep s h) hinv hlt]
  have he : s.length + 1 - s.length = 0 + 1 := by omega
  rw [he, monomialBlowupStep_schemeAt_succ s h 0]

theorem blowupAtCenter_ideal_succ (h : IsAdmissibleCenter s) :
    (blowupAtCenter hinv s).ideal (s.length + 1) =
      (residualByPow ((s.ideal s.length).comap (Blowup.blowup.proj (centerAtLast s)))
          ((centerAtLast s).comap (Blowup.blowup.proj (centerAtLast s))) m).comap
        (eqToHom (blowupAtCenter_schemeAt_succ hinv s h)) := by
  have key : ∀ d : MarkedBlowupSequenceData p I m E, d = s.append (monomialBlowupStep s h) hinv →
      ∀ hobj : d.obj (s.length + 1) = Blowup.blowup (centerAtLast s),
        d.ideal (s.length + 1) =
          (residualByPow ((s.ideal s.length).comap (Blowup.blowup.proj (centerAtLast s)))
              ((centerAtLast s).comap (Blowup.blowup.proj (centerAtLast s))) m).comap (eqToHom hobj) := by
    rintro d rfl hobj
    rewrite [append_ideal, appendIdeal_length_succ, monomialBlowupStep_ideal_one]
    rfl
  exact key (blowupAtCenter hinv s) (blowupAtCenter_eq_append hinv s h)
    (blowupAtCenter_schemeAt_succ hinv s h)

private theorem boundary_succ_of_eq_append_consolidated301 (h : IsAdmissibleCenter s) (d : MarkedBlowupSequenceData p I m E)
    (hd : d = s.append (monomialBlowupStep s h) hinv)
    (e : d.obj (s.length + 1) = Blowup.blowup (centerAtLast s)) :
    d.boundary (s.length + 1) =
      List.map (fun D => D.comap (eqToHom e))
        (List.map (Blowup.strictTransform (Blowup.blowup.proj (centerAtLast s)) (centerAtLast s))
            (s.boundary s.length) ++
          [Blowup.exceptionalIdeal (Blowup.blowup.proj (centerAtLast s)) (centerAtLast s)]) := by
  subst hd
  refine Eq.trans (append_boundary s (monomialBlowupStep s h) hinv (s.length + 1)) ?_
  refine Eq.trans (appendBoundary_length_succ s (monomialBlowupStep s h)) ?_
  exact congrArg
    (List.map (fun D : (Blowup.blowup (centerAtLast s)).IdealSheafData => D.comap (eqToHom e)))
    (monomialBlowupStep_boundary_one s h)

theorem blowupAtCenter_boundary_succ (h : IsAdmissibleCenter s) :
    (blowupAtCenter hinv s).boundary (s.length + 1) =
      List.map (fun D => D.comap (eqToHom (blowupAtCenter_schemeAt_succ hinv s h)))
        (List.map (Blowup.strictTransform (Blowup.blowup.proj (centerAtLast s)) (centerAtLast s))
            (s.boundary s.length) ++
          [Blowup.exceptionalIdeal (Blowup.blowup.proj (centerAtLast s)) (centerAtLast s)]) :=
  boundary_succ_of_eq_append_consolidated301 hinv s h (blowupAtCenter hinv s)
    (blowupAtCenter_eq_append hinv s h) (blowupAtCenter_schemeAt_succ hinv s h)


end

private theorem appendProjectionToBase_of_lt_consolidated301 (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (i j : ℕ) (hi : s.length < i) (hj : i - s.length = j)
    (hobj : (s.appendToBlowupSequenceData t).obj i = t.obj j) :
    s.appendProjectionToBase t i = eqToHom hobj ≫ t.proj j ≫ s.proj s.length := by
  subst hj
  exact appendProjectionToBase_of_length_lt s t hi

theorem blowupAtCenter_projectionToBase_succ (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (h : IsAdmissibleCenter s) :
    (blowupAtCenter hinv s).proj (s.length + 1) =
      eqToHom (blowupAtCenter_schemeAt_succ hinv s h) ≫ Blowup.blowup.proj (centerAtLast s) ≫ s.proj s.length := by
  have key : ∀ d : MarkedBlowupSequenceData p I m E, d = s.append (monomialBlowupStep s h) hinv →
      ∀ hobj : d.obj (s.length + 1) = Blowup.blowup (centerAtLast s),
        d.proj (s.length + 1) =
          eqToHom hobj ≫ Blowup.blowup.proj (centerAtLast s) ≫ s.proj s.length := by
    rintro d rfl hobj
    rewrite [append_projectionToBase,
      appendProjectionToBase_of_lt_consolidated301 s (monomialBlowupStep s h) (s.length + 1) 1 (by omega) (by omega)
        (appendToBlowupSequenceData_schemeAt_length_succ s (monomialBlowupStep s h)),
      monomialBlowupStep_projectionToBase_one]
    rfl
  exact key (blowupAtCenter hinv s) (blowupAtCenter_eq_append hinv s h)
    (blowupAtCenter_schemeAt_succ hinv s h)

end MarkedBlowupSequenceData

section

variable {k : Type u} [Field k] {X : Scheme.{u}}

def monomialStallIndex (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) : ℕ :=
  sInf {n : ℕ | MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) n}

section
variable (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData)

theorem isStationaryAt_monomialStallIndex (hex : ∃ n : ℕ, MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) n) :
    MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) (monomialStallIndex hinv p I m E) := by
  exact Nat.sInf_mem hex

theorem isAdmissibleCenter_of_lt_monomialStallIndex (n : ℕ) (hn : n < monomialStallIndex hinv p I m E) :
    MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) := by
  have hn' : n < sInf {j : ℕ | MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) j} := hn
  have hstall : ¬ MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) n := by
    intro hmem
    have hle : sInf {j : ℕ | MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) j} ≤ n :=
      Nat.sInf_le hmem
    exact absurd hle (not_le.mpr hn')
  by_contra hstep
  exact hstall
    ((MarkedBlowupSequenceData.isStationaryAt_iff_not_isAdmissibleCenter hinv (emptyMarkedBlowupSequenceData p I m E) n).mpr hstep)

theorem monomialStallIndex_eq_of_isStationaryAt (n : ℕ)
    (hstall : MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) n)
    (hstep : ∀ j < n, MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) j)) :
    monomialStallIndex hinv p I m E = n := by
  have hne : ∃ j : ℕ, MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) j := ⟨n, hstall⟩
  have h1 : monomialStallIndex hinv p I m E ≤ n := Nat.sInf_le hstall
  refine le_antisymm h1 ?_
  by_contra hlt
  have hlt' : monomialStallIndex hinv p I m E < n := lt_of_not_ge hlt
  have hmem : MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E)
      (monomialStallIndex hinv p I m E) := Nat.sInf_mem hne
  exact ((MarkedBlowupSequenceData.isStationaryAt_iff_not_isAdmissibleCenter hinv _ _).mp hmem) (hstep _ hlt')

theorem monomialBlowupSeq_eq_monomialBlowupIterate :
    monomialBlowupSeq hinv p I m E =
      MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E)
        (monomialStallIndex hinv p I m E) :=
  rfl


end

private theorem monomialBlowupIterate_length_consolidated301 {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u})
    (s : MarkedBlowupSequenceData p I m E) (n : ℕ) :
    (∀ j < n, MarkedBlowupSequenceData.IsAdmissibleCenter (MarkedBlowupSequenceData.monomialBlowupIterate hinv s j)) →
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv s n).length = s.length + n := by
  induction n with
  | zero =>
      intro _
      rw [MarkedBlowupSequenceData.monomialBlowupIterate_zero, Nat.add_zero]
  | succ n ih =>
      intro hstep
      have h2 : MarkedBlowupSequenceData.IsAdmissibleCenter (MarkedBlowupSequenceData.monomialBlowupIterate hinv s n) :=
        hstep n (Nat.lt_succ_self n)
      have h1 := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
      have e1 : (MarkedBlowupSequenceData.monomialBlowupIterate hinv s (n + 1)).length
          = (MarkedBlowupSequenceData.monomialBlowupIterate hinv s n).length + 1 := by
        rw [MarkedBlowupSequenceData.monomialBlowupIterate_succ,
          MarkedBlowupSequenceData.blowupAtCenter_length hinv _ h2]
      omega

theorem monomialBlowupSeq_length (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) :
    (monomialBlowupSeq hinv p I m E).length = monomialStallIndex hinv p I m E := by
  have h := monomialBlowupIterate_length_consolidated301 hinv (emptyMarkedBlowupSequenceData p I m E)
    (monomialStallIndex hinv p I m E)
    (fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j hj)
  rw [monomialBlowupSeq_eq_monomialBlowupIterate, h, emptyMarkedBlowupSequenceData_length, Nat.zero_add]

section
variable {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u}) (d : MarkedBlowupSequenceData p I m E)

private theorem blowupAtCenter_schemeAt_of_le_consolidated301 (i : ℕ) (hi : i ≤ d.length) :
    (MarkedBlowupSequenceData.blowupAtCenter hinv d).obj i = d.obj i := by
  by_cases h : MarkedBlowupSequenceData.IsAdmissibleCenter d
  · rw [MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv d h]
    exact MarkedBlowupSequenceData.append_schemeAt_of_le_length d (MarkedBlowupSequenceData.monomialBlowupStep d h) hinv hi
  · have hs : MarkedBlowupSequenceData.blowupAtCenter hinv d = d := by
      unfold MarkedBlowupSequenceData.blowupAtCenter
      rw [dif_neg h]
    rw [hs]

private theorem length_le_blowupAtCenter_length_consolidated301 :
    d.length ≤ (MarkedBlowupSequenceData.blowupAtCenter hinv d).length := by
  by_cases h : MarkedBlowupSequenceData.IsAdmissibleCenter d
  · rw [MarkedBlowupSequenceData.blowupAtCenter_length hinv d h]
    omega
  · have hs : MarkedBlowupSequenceData.blowupAtCenter hinv d = d := by
      unfold MarkedBlowupSequenceData.blowupAtCenter
      rw [dif_neg h]
    exact le_of_eq (by rw [hs])

private theorem monomialBlowupIterate_length_le_and_schemeAt_eq_consolidated301 (j : ℕ) :
    d.length ≤ (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).length ∧
      ∀ i ≤ d.length, (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).obj i = d.obj i := by
  induction j with
  | zero =>
      refine ⟨?_, ?_⟩
      · exact le_of_eq (by rw [MarkedBlowupSequenceData.monomialBlowupIterate_zero])
      · intro i _
        rw [MarkedBlowupSequenceData.monomialBlowupIterate_zero]
  | succ j ih =>
      refine ⟨?_, ?_⟩
      · refine le_trans ih.1 ?_
        rw [MarkedBlowupSequenceData.monomialBlowupIterate_succ]
        exact length_le_blowupAtCenter_length_consolidated301 hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j)
      · intro i hi
        rw [MarkedBlowupSequenceData.monomialBlowupIterate_succ,
          blowupAtCenter_schemeAt_of_le_consolidated301 hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j) i
            (le_trans hi ih.1)]
        exact ih.2 i hi

private theorem monomialBlowupIterate_add_consolidated301 (a b : ℕ) :
    MarkedBlowupSequenceData.monomialBlowupIterate hinv d (a + b) =
      MarkedBlowupSequenceData.monomialBlowupIterate hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv d a) b := by
  induction b with
  | zero => rw [Nat.add_zero, MarkedBlowupSequenceData.monomialBlowupIterate_zero]
  | succ b ih =>
      rw [← Nat.add_assoc, MarkedBlowupSequenceData.monomialBlowupIterate_succ,
        MarkedBlowupSequenceData.monomialBlowupIterate_succ, ih]


end

theorem monomialBlowupSeq_schemeAt (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (n : ℕ)
    (hn : n ≤ monomialStallIndex hinv p I m E) :
    (monomialBlowupSeq hinv p I m E).obj n =
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).obj
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length := by
  have hlen : (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length = n := by
    have h := monomialBlowupIterate_length_consolidated301 hinv (emptyMarkedBlowupSequenceData p I m E) n
      (fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j (lt_of_lt_of_le hj hn))
    rw [emptyMarkedBlowupSequenceData_length, Nat.zero_add] at h
    exact h
  rw [hlen]
  have hsplit : monomialStallIndex hinv p I m E = n + (monomialStallIndex hinv p I m E - n) := by
    omega
  rw [monomialBlowupSeq_eq_monomialBlowupIterate, hsplit, monomialBlowupIterate_add_consolidated301 hinv (emptyMarkedBlowupSequenceData p I m E) n
    (monomialStallIndex hinv p I m E - n)]
  exact (monomialBlowupIterate_length_le_and_schemeAt_eq_consolidated301 hinv
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)
    (monomialStallIndex hinv p I m E - n)).2 n (le_of_eq hlen.symm)

private theorem comap_eqToHom_comap_eqToHom_symm_consolidated301 {V W : Scheme.{u}} (h : V = W)
    (J : W.IdealSheafData) :
    (J.comap (eqToHom h)).comap (eqToHom h.symm) = J := by
  subst h
  simp

section
variable {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

private theorem isPrefix_monomialBlowupIterate_succ_consolidated301 (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E) (j : ℕ) :
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv s j).IsPrefix
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv s (j + 1)) := by
  by_cases h : MarkedBlowupSequenceData.IsAdmissibleCenter (MarkedBlowupSequenceData.monomialBlowupIterate hinv s j)
  · rw [MarkedBlowupSequenceData.monomialBlowupIterate_succ,
      MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv _ h]
    exact MarkedBlowupSequenceData.isPrefix_append _ _ hinv
  · have hs : MarkedBlowupSequenceData.blowupAtCenter hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv s j)
        = MarkedBlowupSequenceData.monomialBlowupIterate hinv s j := by
      unfold MarkedBlowupSequenceData.blowupAtCenter
      rw [dif_neg h]
    rw [MarkedBlowupSequenceData.monomialBlowupIterate_succ, hs]
    exact MarkedBlowupSequenceData.IsPrefix.refl _

private theorem isPrefix_monomialBlowupIterate_of_le_consolidated301 (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E) {i j : ℕ} (hij : i ≤ j) :
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv s i).IsPrefix
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv s j) := by
  induction j with
  | zero =>
      obtain rfl : i = 0 := Nat.le_zero.mp hij
      exact MarkedBlowupSequenceData.IsPrefix.refl _
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le hij with h | h
      · subst h
        exact MarkedBlowupSequenceData.IsPrefix.refl _
      · exact (ih (Nat.lt_succ_iff.mp h)).trans (isPrefix_monomialBlowupIterate_succ_consolidated301 hinv s n)

private theorem ideal_eq_comap_of_isPrefix_consolidated301 (A B : MarkedBlowupSequenceData p I m E) (n : ℕ) (hlen : A.length = n)
    (hpre : A.IsPrefix B) (hobj : B.obj n = A.obj A.length) :
    B.ideal n = (A.ideal A.length).comap (eqToHom hobj) := by
  subst hlen
  rw [hpre.ideal_eq A.length le_rfl]
  exact (comap_eqToHom_comap_eqToHom_symm_consolidated301 (hpre.obj_eq A.length le_rfl) (B.ideal A.length)).symm


end

theorem monomialBlowupSeq_ideal (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (n : ℕ)
    (hn : n ≤ monomialStallIndex hinv p I m E) :
    (monomialBlowupSeq hinv p I m E).ideal n =
      ((MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).ideal
          (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length).comap
        (eqToHom (monomialBlowupSeq_schemeAt hinv p I m E n hn)) := by
  have hstep : ∀ j < n, MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) j) :=
    fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j (lt_of_lt_of_le hj hn)
  have hlen : (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length = n := by
    rw [monomialBlowupIterate_length_consolidated301 hinv (emptyMarkedBlowupSequenceData p I m E) n hstep,
      emptyMarkedBlowupSequenceData_length, Nat.zero_add]
  have hpre : (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).IsPrefix
      (monomialBlowupSeq hinv p I m E) := by
    rw [monomialBlowupSeq_eq_monomialBlowupIterate]
    exact isPrefix_monomialBlowupIterate_of_le_consolidated301 hinv (emptyMarkedBlowupSequenceData p I m E) hn
  exact ideal_eq_comap_of_isPrefix_consolidated301
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)
    (monomialBlowupSeq hinv p I m E) n hlen hpre (monomialBlowupSeq_schemeAt hinv p I m E n hn)

section
variable {Y : Scheme.{u}} (q : Y = Y)

private theorem comap_eqToHom_self_consolidated301 (Z : Y.IdealSheafData) :
    Z.comap (eqToHom q) = Z := by
  simp

private theorem map_comap_eqToHom_self_consolidated301 (L : List Y.IdealSheafData) :
    List.map (fun D => D.comap (eqToHom q)) L = L := by
  induction L with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, ih, comap_eqToHom_self_consolidated301]


end

section
variable {A B C : Scheme.{u}} (hAB : A = B) (hBC : B = C) (hAC : A = C)

private theorem comap_eqToHom_comp_consolidated301 (D : C.IdealSheafData) :
    (D.comap (eqToHom hBC)).comap (eqToHom hAB) = D.comap (eqToHom hAC) := by
  cases hAB
  cases hBC
  simp only [comap_eqToHom_self_consolidated301]

private theorem map_comap_eqToHom_comp_consolidated301 (L : List C.IdealSheafData) :
    List.map (fun D : B.IdealSheafData => D.comap (eqToHom hAB))
        (List.map (fun D : C.IdealSheafData => D.comap (eqToHom hBC)) L)
      = List.map (fun D : C.IdealSheafData => D.comap (eqToHom hAC)) L := by
  induction L with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, ih, comap_eqToHom_comp_consolidated301 hAB hBC hAC]


end

section
variable (hinv : ComapIsoInvariance.{u}) {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (s : MarkedBlowupSequenceData p I m E)

private theorem blowupAtCenter_boundary_of_le_consolidated301 (h : MarkedBlowupSequenceData.IsAdmissibleCenter s) (i : ℕ) (hi : i ≤ s.length)
    (ho : (MarkedBlowupSequenceData.blowupAtCenter hinv s).obj i = s.obj i) :
    (MarkedBlowupSequenceData.blowupAtCenter hinv s).boundary i =
      List.map (fun D => D.comap (eqToHom ho)) (s.boundary i) := by
  have key : ∀ d : MarkedBlowupSequenceData p I m E,
      d = s.append (MarkedBlowupSequenceData.monomialBlowupStep s h) hinv →
      ∀ ho' : d.obj i = s.obj i,
        d.boundary i = List.map (fun D => D.comap (eqToHom ho')) (s.boundary i) := by
    rintro d rfl ho'
    refine Eq.trans
      (MarkedBlowupSequenceData.append_boundary s (MarkedBlowupSequenceData.monomialBlowupStep s h) hinv i) ?_
    exact MarkedBlowupSequenceData.appendBoundary_of_le_length s (MarkedBlowupSequenceData.monomialBlowupStep s h) hi
  exact key (MarkedBlowupSequenceData.blowupAtCenter hinv s)
    (MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv s h) ho

private theorem monomialBlowupIterate_boundary_of_le_consolidated301 (i : ℕ) (hi : i ≤ s.length) (d : ℕ) :
    (∀ j < d, MarkedBlowupSequenceData.IsAdmissibleCenter (MarkedBlowupSequenceData.monomialBlowupIterate hinv s j)) →
      ∀ ho : (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).obj i = s.obj i,
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).boundary i =
          List.map (fun D => D.comap (eqToHom ho)) (s.boundary i) := by
  induction d with
  | zero =>
      intro _ ho
      exact (map_comap_eqToHom_self_consolidated301 ho (s.boundary i)).symm
  | succ d ih =>
      intro hstep ho
      have h2 : MarkedBlowupSequenceData.IsAdmissibleCenter (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d) :=
        hstep d (Nat.lt_succ_self d)
      have hlen : (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).length = s.length + d :=
        monomialBlowupIterate_length_consolidated301 hinv s d (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
      have hi' : i ≤ (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).length := by omega
      have hobj1 : (MarkedBlowupSequenceData.blowupAtCenter hinv
            (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d)).obj i
          = (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).obj i :=
        blowupAtCenter_schemeAt_of_le_consolidated301 hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d) i hi'
      have hobj2 : (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).obj i = s.obj i :=
        Eq.trans hobj1.symm ho
      have hstep1 := blowupAtCenter_boundary_of_le_consolidated301 hinv
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d) h2 i hi' hobj1
      have hprev := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj)) hobj2
      exact Eq.trans hstep1
        (Eq.trans (congrArg (List.map (fun D => D.comap (eqToHom hobj1))) hprev)
          (map_comap_eqToHom_comp_consolidated301 hobj1 hobj2 ho (s.boundary i)))


end

private theorem boundary_eq_map_comap_of_index_eq_consolidated301
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (d t : MarkedBlowupSequenceData p I m E) (n L : ℕ) (hL : L = n)
    (hb : ∀ ho : d.obj n = t.obj n,
      d.boundary n = List.map (fun D => D.comap (eqToHom ho)) (t.boundary n))
    (H : d.obj n = t.obj L) :
    d.boundary n = List.map (fun D => D.comap (eqToHom H)) (t.boundary L) := by
  subst hL
  exact hb H

theorem monomialBlowupSeq_boundary (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (n : ℕ)
    (hn : n ≤ monomialStallIndex hinv p I m E) :
    (monomialBlowupSeq hinv p I m E).boundary n =
      List.map (fun D => D.comap (eqToHom (monomialBlowupSeq_schemeAt hinv p I m E n hn)))
        ((MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).boundary
          (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length) := by
  have hsteps0 : ∀ j < n, MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) j) :=
    fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j (lt_of_lt_of_le hj hn)
  have hlen : (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length = n := by
    rw [monomialBlowupIterate_length_consolidated301 hinv (emptyMarkedBlowupSequenceData p I m E) n hsteps0,
      emptyMarkedBlowupSequenceData_length, Nat.zero_add]
  have h1 : n + (monomialStallIndex hinv p I m E - n) = monomialStallIndex hinv p I m E := by omega
  have hseq : monomialBlowupSeq hinv p I m E =
      MarkedBlowupSequenceData.monomialBlowupIterate hinv
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)
        (monomialStallIndex hinv p I m E - n) := by
    have h2 : MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E)
        (n + (monomialStallIndex hinv p I m E - n))
        = MarkedBlowupSequenceData.monomialBlowupIterate hinv
            (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)
            (monomialStallIndex hinv p I m E - n) :=
      monomialBlowupIterate_add_consolidated301 hinv (emptyMarkedBlowupSequenceData p I m E) n (monomialStallIndex hinv p I m E - n)
    rw [h1] at h2
    exact Eq.trans (monomialBlowupSeq_eq_monomialBlowupIterate hinv p I m E) h2
  have hstepsn : ∀ j < monomialStallIndex hinv p I m E - n, MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) j) := by
    intro j hj
    have h3 : MarkedBlowupSequenceData.monomialBlowupIterate hinv
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) j
        = MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) (n + j) :=
      (monomialBlowupIterate_add_consolidated301 hinv (emptyMarkedBlowupSequenceData p I m E) n j).symm
    rw [h3]
    exact isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E (n + j) (by omega)
  have key : ∀ d : MarkedBlowupSequenceData p I m E,
      d = MarkedBlowupSequenceData.monomialBlowupIterate hinv
            (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)
            (monomialStallIndex hinv p I m E - n) →
      ∀ ho : d.obj n = (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).obj n,
        d.boundary n = List.map (fun D => D.comap (eqToHom ho))
          ((MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).boundary n) := by
    rintro d rfl ho
    exact monomialBlowupIterate_boundary_of_le_consolidated301 hinv
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) n (by omega)
      (monomialStallIndex hinv p I m E - n) hstepsn ho
  exact boundary_eq_map_comap_of_index_eq_consolidated301 (monomialBlowupSeq hinv p I m E)
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) n
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length hlen
    (key (monomialBlowupSeq hinv p I m E) hseq) (monomialBlowupSeq_schemeAt hinv p I m E n hn)

private theorem append_center_eq_appendToBlowupSequenceData_center_consolidated301 {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (hinv : ComapIsoInvariance.{u}) (i : ℕ) :
    (s.append t hinv).center i = (s.appendToBlowupSequenceData t).center i :=
  rfl

section
variable {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (hinv : ComapIsoInvariance.{u}) (d : MarkedBlowupSequenceData p I m E)

private theorem blowupAtCenter_center_of_lt_consolidated301 (i : ℕ) (hi : i < d.length)
    (e : (MarkedBlowupSequenceData.blowupAtCenter hinv d).obj i = d.obj i) :
    (MarkedBlowupSequenceData.blowupAtCenter hinv d).center i = (d.center i).comap (eqToHom e) := by
  by_cases h : MarkedBlowupSequenceData.IsAdmissibleCenter d
  · have key : ∀ D : MarkedBlowupSequenceData p I m E,
        D = d.append (MarkedBlowupSequenceData.monomialBlowupStep d h) hinv →
        ∀ eD : D.obj i = d.obj i, D.center i = (d.center i).comap (eqToHom eD) := by
      rintro D rfl eD
      refine Eq.trans
        (append_center_eq_appendToBlowupSequenceData_center_consolidated301 d (MarkedBlowupSequenceData.monomialBlowupStep d h) hinv i) ?_
      exact MarkedBlowupSequenceData.appendToBlowupSequenceData_center_of_lt_length d (MarkedBlowupSequenceData.monomialBlowupStep d h) hi
    exact key (MarkedBlowupSequenceData.blowupAtCenter hinv d)
      (MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv d h) e
  · have hs : MarkedBlowupSequenceData.blowupAtCenter hinv d = d := by
      unfold MarkedBlowupSequenceData.blowupAtCenter
      rw [dif_neg h]
    have key : ∀ D : MarkedBlowupSequenceData p I m E, D = d →
        ∀ eD : D.obj i = d.obj i, D.center i = (d.center i).comap (eqToHom eD) := by
      rintro D rfl eD
      exact (comap_eqToHom_self_consolidated301 eD _).symm
    exact key (MarkedBlowupSequenceData.blowupAtCenter hinv d) hs e

private theorem monomialBlowupIterate_center_of_lt_consolidated301 (i : ℕ) (hi : i < d.length) (j : ℕ) :
    ∀ e : (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).obj i = d.obj i,
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).center i = (d.center i).comap (eqToHom e) := by
  induction j with
  | zero =>
      intro e
      exact (comap_eqToHom_self_consolidated301 e (d.center i)).symm
  | succ j ih =>
      intro e
      have e2 : (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).obj i = d.obj i :=
        (monomialBlowupIterate_length_le_and_schemeAt_eq_consolidated301 hinv d j).2 i (le_of_lt hi)
      have hij : i < (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).length :=
        lt_of_lt_of_le hi (monomialBlowupIterate_length_le_and_schemeAt_eq_consolidated301 hinv d j).1
      have e1 : (MarkedBlowupSequenceData.blowupAtCenter hinv
            (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j)).obj i
          = (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).obj i :=
        blowupAtCenter_schemeAt_of_le_consolidated301 hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j) i (le_of_lt hij)
      refine Eq.trans
        (blowupAtCenter_center_of_lt_consolidated301 hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j) i hij e1) ?_
      rw [ih e2]
      exact comap_eqToHom_comp_consolidated301 e1 e2 e (d.center i)

private theorem blowupAtCenter_center_of_eq_length_consolidated301 (h : MarkedBlowupSequenceData.IsAdmissibleCenter d) (i : ℕ) (hi : i = d.length)
    (e : (MarkedBlowupSequenceData.blowupAtCenter hinv d).obj i = d.obj d.length) :
    (MarkedBlowupSequenceData.blowupAtCenter hinv d).center i =
      (MarkedBlowupSequenceData.centerAtLast d).comap (eqToHom e) := by
  subst hi
  have key : ∀ D : MarkedBlowupSequenceData p I m E,
      D = d.append (MarkedBlowupSequenceData.monomialBlowupStep d h) hinv →
      ∀ eD : D.obj d.length = d.obj d.length,
        D.center d.length = (MarkedBlowupSequenceData.centerAtLast d).comap (eqToHom eD) := by
    rintro D rfl eD
    have hc : (d.appendToBlowupSequenceData (MarkedBlowupSequenceData.monomialBlowupStep d h)).obj d.length
        = d.obj d.length :=
      MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_of_le_length d (MarkedBlowupSequenceData.monomialBlowupStep d h) (le_refl d.length)
    have e3 : (d.appendToBlowupSequenceData (MarkedBlowupSequenceData.monomialBlowupStep d h)).obj d.length
        = (MarkedBlowupSequenceData.monomialBlowupStep d h).obj 0 :=
      hc.trans (MarkedBlowupSequenceData.monomialBlowupStep_schemeAt_zero d h).symm
    have s1 : (d.append (MarkedBlowupSequenceData.monomialBlowupStep d h) hinv).center d.length
        = (((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0).comap
            (MarkedBlowupSequenceData.monomialBlowupStep d h).isoZero.inv).comap (eqToHom hc) :=
      MarkedBlowupSequenceData.appendToBlowupSequenceData_center_length d (MarkedBlowupSequenceData.monomialBlowupStep d h)
    have s2 : (((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0).comap
            (MarkedBlowupSequenceData.monomialBlowupStep d h).isoZero.inv).comap (eqToHom hc)
        = (((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0).comap
            (eqToHom (MarkedBlowupSequenceData.monomialBlowupStep_schemeAt_zero d h).symm)).comap (eqToHom hc) := by
      rw [MarkedBlowupSequenceData.monomialBlowupStep_isoObjZero_inv]
    have s3 : (((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0).comap
            (eqToHom (MarkedBlowupSequenceData.monomialBlowupStep_schemeAt_zero d h).symm)).comap (eqToHom hc)
        = ((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0).comap (eqToHom e3) :=
      comap_eqToHom_comp_consolidated301 hc (MarkedBlowupSequenceData.monomialBlowupStep_schemeAt_zero d h).symm e3
        ((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0)
    have s4 : ((MarkedBlowupSequenceData.monomialBlowupStep d h).center 0).comap (eqToHom e3)
        = (MarkedBlowupSequenceData.centerAtLast d).comap (eqToHom eD) := by
      rw [MarkedBlowupSequenceData.monomialBlowupStep_center_zero]
      rfl
    exact s1.trans (s2.trans (s3.trans s4))
  exact key (MarkedBlowupSequenceData.blowupAtCenter hinv d)
    (MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv d h) e

private theorem center_monomialBlowupIterate_blowupAtCenter_eq_consolidated301 (n : ℕ) (hlen : d.length = n)
    (h : MarkedBlowupSequenceData.IsAdmissibleCenter d) (r : ℕ) (D : MarkedBlowupSequenceData p I m E)
    (hD : D = MarkedBlowupSequenceData.monomialBlowupIterate hinv (MarkedBlowupSequenceData.blowupAtCenter hinv d) r)
    (eD : D.obj n = d.obj d.length) :
    D.center n = (MarkedBlowupSequenceData.centerAtLast d).comap (eqToHom eD) := by
  subst hD
  have hl1 : (MarkedBlowupSequenceData.blowupAtCenter hinv d).length = n + 1 := by
    rw [MarkedBlowupSequenceData.blowupAtCenter_length hinv d h, hlen]
  have hn1 : n < (MarkedBlowupSequenceData.blowupAtCenter hinv d).length := by omega
  have e1 : (MarkedBlowupSequenceData.monomialBlowupIterate hinv
        (MarkedBlowupSequenceData.blowupAtCenter hinv d) r).obj n
      = (MarkedBlowupSequenceData.blowupAtCenter hinv d).obj n :=
    (monomialBlowupIterate_length_le_and_schemeAt_eq_consolidated301 hinv (MarkedBlowupSequenceData.blowupAtCenter hinv d) r).2 n
      (le_of_lt hn1)
  have ejunc : (MarkedBlowupSequenceData.blowupAtCenter hinv d).obj n = d.obj d.length :=
    (blowupAtCenter_schemeAt_of_le_consolidated301 hinv d n (le_of_eq hlen.symm)).trans (congrArg d.obj hlen.symm)
  rw [monomialBlowupIterate_center_of_lt_consolidated301 hinv (MarkedBlowupSequenceData.blowupAtCenter hinv d) n hn1 r e1,
    blowupAtCenter_center_of_eq_length_consolidated301 hinv d h n hlen.symm ejunc]
  exact comap_eqToHom_comp_consolidated301 e1 ejunc eD (MarkedBlowupSequenceData.centerAtLast d)


end

theorem monomialBlowupSeq_center (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (n : ℕ)
    (hn : n < monomialStallIndex hinv p I m E) :
    (monomialBlowupSeq hinv p I m E).center n =
      (MarkedBlowupSequenceData.centerAtLast
          (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)).comap
        (eqToHom (monomialBlowupSeq_schemeAt hinv p I m E n (Nat.le_of_lt hn))) := by
  have hlen : (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length = n := by
    have h := monomialBlowupIterate_length_consolidated301 hinv (emptyMarkedBlowupSequenceData p I m E) n
      (fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j (lt_trans hj hn))
    rw [emptyMarkedBlowupSequenceData_length, Nat.zero_add] at h
    exact h
  have hstep : MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) :=
    isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E n hn
  have hsplit : monomialStallIndex hinv p I m E
      = (n + 1) + (monomialStallIndex hinv p I m E - (n + 1)) := by
    omega
  have h1 : MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E)
        (monomialStallIndex hinv p I m E)
      = MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E)
          ((n + 1) + (monomialStallIndex hinv p I m E - (n + 1))) := by
    rw [← hsplit]
  have hseq : monomialBlowupSeq hinv p I m E =
      MarkedBlowupSequenceData.monomialBlowupIterate hinv
        (MarkedBlowupSequenceData.blowupAtCenter hinv
          (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n))
        (monomialStallIndex hinv p I m E - (n + 1)) := by
    rw [monomialBlowupSeq_eq_monomialBlowupIterate, h1,
      monomialBlowupIterate_add_consolidated301 hinv (emptyMarkedBlowupSequenceData p I m E) (n + 1)
        (monomialStallIndex hinv p I m E - (n + 1)),
      MarkedBlowupSequenceData.monomialBlowupIterate_succ]
  exact center_monomialBlowupIterate_blowupAtCenter_eq_consolidated301 hinv
    (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) n
    hlen hstep (monomialStallIndex hinv p I m E - (n + 1)) (monomialBlowupSeq hinv p I m E) hseq
    (monomialBlowupSeq_schemeAt hinv p I m E n (Nat.le_of_lt hn))

end

namespace MarkedBlowupSequenceData

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def monomialStallIndex (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E) : ℕ :=
  sInf {n : ℕ | IsStationaryAt hinv s n}

theorem monomialStallIndex_eq_zero_of_not_isAdmissibleCenter (hinv : ComapIsoInvariance.{u})
    (s : MarkedBlowupSequenceData p I m E) (h : ¬ IsAdmissibleCenter s) : monomialStallIndex hinv s = 0 := by
  have h0 : IsStationaryAt hinv s 0 := (isStationaryAt_iff_not_isAdmissibleCenter hinv s 0).mpr h
  show sInf {n : ℕ | IsStationaryAt hinv s n} = 0
  exact Nat.le_zero.mp (Nat.sInf_le h0)

end

end MarkedBlowupSequenceData

section

variable {k : Type u} [Field k] {X : Scheme.{u}}

theorem monomialStallIndex_eq_monomialStallIndex_empty (hinv : ComapIsoInvariance.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) :
    monomialStallIndex hinv p I m E =
      MarkedBlowupSequenceData.monomialStallIndex hinv (emptyMarkedBlowupSequenceData p I m E) :=
  rfl

end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
section

open TopologicalSpace

open scoped Classical

section

namespace BlowupSequenceData

def prependSchemeAt {X : Scheme.{u}} (d : BlowupSequenceData X) : ℕ → Scheme.{u}
  | 0 => X
  | (n + 1) => d.obj n

def prependMap {X : Scheme.{u}} (d : BlowupSequenceData X) :
    (i : ℕ) → d.prependSchemeAt (i + 1) ⟶ d.prependSchemeAt i
  | 0 => d.isoZero.hom
  | (n + 1) => d.map n

def prependCenter {X : Scheme.{u}} (d : BlowupSequenceData X) (Z : X.IdealSheafData) :
    (i : ℕ) → (d.prependSchemeAt i).IdealSheafData
  | 0 => Z
  | (n + 1) => d.center n

theorem isBlowupAlongIdealSheaf_prependMap {X : Scheme.{u}} (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (d : BlowupSequenceData X) (i : ℕ) (hi : i < d.length + 1) :
    Blowup.IsBlowupAlongIdealSheaf (d.prependMap i) (d.prependCenter Z i) := by
  cases i with
  | zero =>
      have h := hZ.iso_hom_comp d.isoZero
      rw [Category.comp_id] at h
      exact h
  | succ n =>
      exact d.isBlowup n (by omega)

def prepend {X : Scheme.{u}} (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z)
    (d : BlowupSequenceData X) : BlowupSequenceData X where
  length := d.length + 1
  obj := d.prependSchemeAt
  map := d.prependMap
  isoZero := Iso.refl X
  center := d.prependCenter Z
  isBlowup := fun i hi => isBlowupAlongIdealSheaf_prependMap Z hZ d i hi

section

variable {X : Scheme.{u}} (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (d : BlowupSequenceData X)

@[simp] theorem prepend_length : (prepend Z hZ d).length = d.length + 1 := rfl

@[simp] theorem prepend_schemeAt_zero : (prepend Z hZ d).obj 0 = X := rfl

@[simp] theorem prepend_schemeAt_succ (n : ℕ) : (prepend Z hZ d).obj (n + 1) = d.obj n := rfl

@[simp] theorem prepend_blowupMorphism_zero : (prepend Z hZ d).map 0 = d.isoZero.hom := rfl

@[simp] theorem prepend_blowupMorphism_succ (n : ℕ) : (prepend Z hZ d).map (n + 1) = d.map n := rfl

@[simp] theorem prepend_isoObjZero : (prepend Z hZ d).isoZero = Iso.refl X := rfl

@[simp] theorem prepend_center_zero : (prepend Z hZ d).center 0 = Z := rfl

@[simp] theorem prepend_center_succ (n : ℕ) : (prepend Z hZ d).center (n + 1) = d.center n := rfl

end

def CentersContainNoComponent {S : Scheme.{u}} (d : BlowupSequenceData S) : Prop :=
  ∀ i, i < d.length → ∀ W ∈ irreducibleComponents ↥(d.obj i),
    ¬ W ⊆ ((d.center i).support : Set ↥(d.obj i))

end BlowupSequenceData

namespace DivisorReduction

noncomputable def containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    T.scheme.IdealSheafData :=
  if h : IsOpen {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
      connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult} then
    Scheme.Hom.ker
      (@AlgebraicGeometry.Scheme.Opens.ι (T.boundary.get ⟨j, hj⟩).subscheme
          ⟨{x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
              connectedComponent x ⊆
                ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}, h⟩ ≫
        (T.boundary.get ⟨j, hj⟩).subschemeι)
  else ⊤

section
variable (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)

theorem containedComponentsIdeal_eq_ker (h : IsOpen {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
      connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}) :
    containedComponentsIdeal T j hj =
      Scheme.Hom.ker
        (@AlgebraicGeometry.Scheme.Opens.ι (T.boundary.get ⟨j, hj⟩).subscheme
            ⟨{x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
                connectedComponent x ⊆
                  ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}, h⟩ ≫
          (T.boundary.get ⟨j, hj⟩).subschemeι) := dif_pos h

theorem containedComponentsIdeal_eq_top_of_not_isOpen (h : ¬ IsOpen {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
      connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}) :
    containedComponentsIdeal T j hj = ⊤ := by
  exact dif_neg h


end

noncomputable def restrictToBoundaryDivisor (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData) : MarkedIdealWithBoundary.{u} :=
  T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
    ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
    (I₀.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
    (((E₀.eraseIdx j).take (T.boundary.length - 1)).map
      (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι))

noncomputable def liftSeqFromDivisor (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (pre : BlowupSequenceData T.scheme → BlowupSequenceData T.scheme) : T.SequenceOfBlowups :=
  if hdn : (restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < T.krullDimSucc ∧
      IsNoetherian T.scheme then
    letI := hdn.2
    if hpr : (MarkedBlowupSequenceData.ofMarkedSequence
        (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdn.1)).toBlowupSequenceData.CentersContainNoComponent then
      if hmk : (pre (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdn.1)).toBlowupSequenceData
          hres hno hpr)).IsMarked T.structMap T.ideal T.mult T.boundary then
        ((pre (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
            (MarkedBlowupSequenceData.ofMarkedSequence (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdn.1)).toBlowupSequenceData
            hres hno hpr)).toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups
      else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
    else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
  else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary

theorem liftSeqFromDivisor_eq_toMarkedSequence (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (pre : BlowupSequenceData T.scheme → BlowupSequenceData T.scheme)
    [IsNoetherian T.scheme]
    (hdim : (restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < T.krullDimSucc)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence
      (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdim)).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (pre (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdim)).toBlowupSequenceData
        hres hno hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    liftSeqFromDivisor hres hno T alg j hj I₀ E₀ pre =
      ((pre (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdim)).toBlowupSequenceData
          hres hno hpr)).toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups := by
  have h1 : (restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < T.krullDimSucc ∧
      IsNoetherian T.scheme := ⟨hdim, inferInstance⟩
  exact (dif_pos h1).trans ((dif_pos hpr).trans (dif_pos hmk))

noncomputable def divisorReductionSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) : T.SequenceOfBlowups :=
  if hj : j < T.boundary.length then
    if orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme) then
      emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
    else
      if containedComponentsIdeal T j hj = ⊤ then
        liftSeqFromDivisor hres hno T alg j hj (T.ideal.comap (𝟙 T.scheme))
          (T.boundary.map (fun D => D.comap (𝟙 T.scheme))) id
      else
        if hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj) then
          liftSeqFromDivisor hres hno T alg j hj
            (residualByPow ((T.ideal.comap (𝟙 T.scheme)).comap (𝟙 T.scheme))
              (Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.mult)
            ((T.boundary.map (fun D => D.comap (𝟙 T.scheme))).map
                (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) ++
              [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)])
            (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb)
        else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
  else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u}) (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) (hj : j < T.boundary.length)
include hj

theorem divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty (hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)) :
    divisorReductionSeq hres hno T alg j = emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary := by
  unfold divisorReductionSeq
  rw [dif_pos hj, if_pos hcs]

theorem divisorReductionSeq_eq_liftSeqFromDivisor_of_eq_top (hcs : orderAtLeastLocus T.ideal T.mult ≠ (∅ : Set ↥T.scheme))
    (hZ : containedComponentsIdeal T j hj = ⊤) :
    divisorReductionSeq hres hno T alg j =
      liftSeqFromDivisor hres hno T alg j hj (T.ideal.comap (𝟙 T.scheme))
        (T.boundary.map (fun D => D.comap (𝟙 T.scheme))) id := by
  unfold divisorReductionSeq
  rw [dif_pos hj, if_neg hcs, if_pos hZ]

theorem divisorReductionSeq_eq_liftSeqFromDivisor_prepend (hcs : orderAtLeastLocus T.ideal T.mult ≠ (∅ : Set ↥T.scheme))
    (hZ : containedComponentsIdeal T j hj ≠ ⊤) (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj)) :
    divisorReductionSeq hres hno T alg j =
      liftSeqFromDivisor hres hno T alg j hj
        (residualByPow ((T.ideal.comap (𝟙 T.scheme)).comap (𝟙 T.scheme))
          (Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.mult)
        ((T.boundary.map (fun D => D.comap (𝟙 T.scheme))).map
            (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) ++
          [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)])
        (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb) := by
  unfold divisorReductionSeq
  rw [dif_pos hj, if_neg hcs, if_neg hZ, dif_pos hb]


end

end DivisorReduction

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Prepend
section


section

namespace SequenceOfBlowupsPullback

variable {X X' : Scheme.{u}}

def prependIndex (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | (n + 1) => f n + 1

section
variable (f : ℕ → ℕ)

@[simp] theorem prependIndex_zero : prependIndex f 0 = 0 := rfl

@[simp] theorem prependIndex_succ (n : ℕ) : prependIndex f (n + 1) = f n + 1 := rfl


end

def succIndex (f : ℕ → ℕ) : ℕ → ℕ := fun j => f j + 1

@[simp] theorem succIndex_apply (f : ℕ → ℕ) (j : ℕ) : succIndex f j = f j + 1 := rfl

private theorem prepend_schemeAt_zero_consolidated274 (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z)
    (d : BlowupSequenceData X) : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt 0 = X :=
  (BlowupSequenceData.toSequenceOfBlowups_schemeAt (BlowupSequenceData.prepend Z hZ d) 0).trans
    (BlowupSequenceData.prepend_schemeAt_zero Z hZ d)

section
variable (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (d : BlowupSequenceData X)

private theorem prepend_schemeAt_succ_consolidated274 (n : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt (n + 1) = d.toSequenceOfBlowups.schemeAt n :=
  (BlowupSequenceData.toSequenceOfBlowups_schemeAt (BlowupSequenceData.prepend Z hZ d) (n + 1)).trans
    ((BlowupSequenceData.prepend_schemeAt_succ Z hZ d n).trans (BlowupSequenceData.toSequenceOfBlowups_schemeAt d n).symm)

private theorem prepend_length_consolidated274 :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length = d.toSequenceOfBlowups.length + 1 := by
  rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.prepend_length, BlowupSequenceData.toSequenceOfBlowups_length]

private theorem le_length_of_succ_le_prepend_length_consolidated274 (n : ℕ)
    (h : n + 1 ≤ (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length) : n ≤ d.toSequenceOfBlowups.length := by
  rw [prepend_length_consolidated274] at h
  omega


end

private def prependMapOfLELength_consolidated274 {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) :
    ∀ j : ℕ, j ≤ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length →
      ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.schemeAt j ⟶
        (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt (prependIndex c.idx j))
  | 0, _ =>
      eqToHom (prepend_schemeAt_zero_consolidated274 (Z.comap φ) hZ' d') ≫ φ ≫
        eqToHom (prepend_schemeAt_zero_consolidated274 Z hZ d).symm
  | (n + 1), h =>
      eqToHom (prepend_schemeAt_succ_consolidated274 (Z.comap φ) hZ' d' n) ≫
        c.map n (le_length_of_succ_le_prepend_length_consolidated274 (Z.comap φ) hZ' d' n h) ≫
        eqToHom (prepend_schemeAt_succ_consolidated274 Z hZ d (c.idx n)).symm

section
variable {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X} (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)

private theorem prependIndex_length_eq_prepend_length_consolidated274 (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) :
    prependIndex c.idx (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length =
      (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length := by
  rw [prepend_length_consolidated274, prepend_length_consolidated274, prependIndex_succ, c.idx_length]

private theorem prependIndex_lt_prepend_length_consolidated274 (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (j : ℕ)
    (hj : j < (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    prependIndex c.idx j < (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length := by
  have hlen' := prepend_length_consolidated274 (Z.comap φ) hZ' d'
  have hlen := prepend_length_consolidated274 Z hZ d
  rw [hlen'] at hj
  rw [hlen]
  cases j with
  | zero =>
      simp only [prependIndex_zero]
      omega
  | succ n =>
      have hn : n < d'.toSequenceOfBlowups.length := by omega
      have hc := c.idx_lt n hn
      simp only [prependIndex_succ]
      omega

private theorem prependIndex_lt_prependIndex_succ_consolidated274 (_hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (j : ℕ)
    (hj : j < (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    prependIndex c.idx j < prependIndex c.idx (j + 1) := by
  cases j with
  | zero =>
      simp only [prependIndex_zero, prependIndex_succ]
      omega
  | succ n =>
      have hn : n < d'.toSequenceOfBlowups.length := by
        rw [prepend_length_consolidated274] at hj
        omega
      have hstep : c.idx n < c.idx (n + 1) := c.idx_strictMono n hn
      simp only [prependIndex_succ]
      omega


end

section
variable {Y : Scheme.{u}} (Z : Y.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y)

private theorem prepend_projectionToBase_succ_consolidated274 (n : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).projectionToBase (n + 1) = d.projectionToBase n := by
  induction n with
  | zero =>
      rw [BlowupSequenceData.projectionToBase_succ (BlowupSequenceData.prepend Z hZ d) 0,
        BlowupSequenceData.prepend_blowupMorphism_zero Z hZ d,
        BlowupSequenceData.projectionToBase_zero (BlowupSequenceData.prepend Z hZ d)]
      exact (Category.comp_id _).trans (BlowupSequenceData.projectionToBase_zero d).symm
  | succ m ih =>
      rw [BlowupSequenceData.projectionToBase_succ (BlowupSequenceData.prepend Z hZ d) (m + 1),
        BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d m, ih]
      exact (BlowupSequenceData.projectionToBase_succ d m).symm

private theorem prepend_toSequenceOfBlowups_projectionToBase_zero_consolidated274 :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase 0 = 𝟙 Y :=
  (BlowupSequenceData.toSequenceOfBlowups_projectionToBase (BlowupSequenceData.prepend Z hZ d) 0).trans
    ((BlowupSequenceData.projectionToBase_zero (BlowupSequenceData.prepend Z hZ d)).trans rfl)

private theorem prepend_toSequenceOfBlowups_projectionToBase_succ_consolidated274 (n : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (n + 1) = d.toSequenceOfBlowups.projectionToBase n :=
  (BlowupSequenceData.toSequenceOfBlowups_projectionToBase (BlowupSequenceData.prepend Z hZ d) (n + 1)).trans
    ((prepend_projectionToBase_succ_consolidated274 Z hZ d n).trans (BlowupSequenceData.toSequenceOfBlowups_projectionToBase d n).symm)


end

private theorem eqToHom_comp_comp_eqToHom_refl_consolidated274 {A B : Scheme.{u}} (f : A ⟶ B) (h1 : A = A)
    (h2 : B = B) : eqToHom h1 ≫ f ≫ eqToHom h2 = f := by
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

section
variable {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X} (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ))

private theorem prependComparisonMap_zero_consolidated274 (hj : 0 ≤ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    prependMapOfLELength_consolidated274 c Z hZ hZ' 0 hj = φ := by
  show 𝟙 X' ≫ φ ≫ 𝟙 X = φ
  simp

private theorem prependComparisonMap_succ_consolidated274 (n : ℕ)
    (h : n + 1 ≤ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length)
    (hn : n ≤ d'.toSequenceOfBlowups.length) :
    prependMapOfLELength_consolidated274 c Z hZ hZ' (n + 1) h = c.map n hn := by
  show eqToHom (prepend_schemeAt_succ_consolidated274 (Z.comap φ) hZ' d' n) ≫
      c.map n (le_length_of_succ_le_prepend_length_consolidated274 (Z.comap φ) hZ' d' n h) ≫
      eqToHom (prepend_schemeAt_succ_consolidated274 Z hZ d (c.idx n)).symm = c.map n hn
  exact eqToHom_comp_comp_eqToHom_refl_consolidated274 (c.map n hn) (prepend_schemeAt_succ_consolidated274 (Z.comap φ) hZ' d' n)
    (prepend_schemeAt_succ_consolidated274 Z hZ d (c.idx n)).symm

private theorem isPullback_prependComparisonMap_zero_consolidated274 (hj : 0 ≤ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    IsPullback (prependMapOfLELength_consolidated274 c Z hZ hZ' 0 hj)
      ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.projectionToBase 0)
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (prependIndex c.idx 0)) φ := by
  have key : IsPullback φ (𝟙 X') (𝟙 X) φ := (IsPullback.of_horiz_isIso ⟨by simp⟩).flip
  have h1 : prependMapOfLELength_consolidated274 c Z hZ hZ' 0 hj = φ := prependComparisonMap_zero_consolidated274 c Z hZ hZ' hj
  have h2 : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.projectionToBase 0 = 𝟙 X' :=
    prepend_toSequenceOfBlowups_projectionToBase_zero_consolidated274 (Z.comap φ) hZ' d'
  have h3 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (prependIndex c.idx 0) = 𝟙 X :=
    prepend_toSequenceOfBlowups_projectionToBase_zero_consolidated274 Z hZ d
  rw [h1, h2, h3]
  exact key

private theorem isPullback_prependComparisonMap_succ_consolidated274 (n : ℕ)
    (hj : n + 1 ≤ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    IsPullback (prependMapOfLELength_consolidated274 c Z hZ hZ' (n + 1) hj)
      ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.projectionToBase (n + 1))
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (prependIndex c.idx (n + 1))) φ := by
  have h1 : prependMapOfLELength_consolidated274 c Z hZ hZ' (n + 1) hj =
      c.map n (le_length_of_succ_le_prepend_length_consolidated274 (Z.comap φ) hZ' d' n hj) :=
    prependComparisonMap_succ_consolidated274 c Z hZ hZ' n hj (le_length_of_succ_le_prepend_length_consolidated274 (Z.comap φ) hZ' d' n hj)
  have h2 : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.projectionToBase (n + 1) =
      d'.toSequenceOfBlowups.projectionToBase n := prepend_toSequenceOfBlowups_projectionToBase_succ_consolidated274 (Z.comap φ) hZ' d' n
  have h3 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (prependIndex c.idx (n + 1)) =
      d.toSequenceOfBlowups.projectionToBase (c.idx n) := prepend_toSequenceOfBlowups_projectionToBase_succ_consolidated274 Z hZ d (c.idx n)
  rw [h1, h2, h3]
  exact c.isPullback n (le_length_of_succ_le_prepend_length_consolidated274 (Z.comap φ) hZ' d' n hj)

private theorem isPullback_prependComparisonMap_consolidated274 (j : ℕ)
    (hj : j ≤ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    IsPullback (prependMapOfLELength_consolidated274 c Z hZ hZ' j hj)
      ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.projectionToBase j)
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (prependIndex c.idx j)) φ := by
  cases j with
  | zero => exact isPullback_prependComparisonMap_zero_consolidated274 c Z hZ hZ' _
  | succ n => exact isPullback_prependComparisonMap_succ_consolidated274 c Z hZ hZ' n _


end

private theorem comp_eq_comp_of_heq_consolidated274 {A' B' A B Y' Y V' V : Scheme.{u}}
    (e0' : A' = Y') (e1' : B' = V') (e0 : A = Y) (e1 : B = V)
    {s' : V' ⟶ Y'} {ψ : Y' ⟶ Y} {m : V' ⟶ V} {s : V ⟶ Y}
    (hw : m ≫ s = s' ≫ ψ)
    {L1 : B' ⟶ A'} {L2 : A' ⟶ A} {R1 : B' ⟶ B} {R2 : B ⟶ A}
    (hL1 : HEq L1 s') (hL2 : HEq L2 ψ) (hR1 : HEq R1 m) (hR2 : HEq R2 s) :
    L1 ≫ L2 = R1 ≫ R2 := by
  subst e0'
  subst e1'
  subst e0
  subst e1
  have h1 : L1 = s' := eq_of_heq hL1
  have h2 : L2 = ψ := eq_of_heq hL2
  have h3 : R1 = m := eq_of_heq hR1
  have h4 : R2 = s := eq_of_heq hR2
  rw [h1, h2, h3, h4, hw]

section
variable {Y : Scheme.{u}} (Z : Y.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y)

private theorem prepend_blowupMorphism_succ_consolidated274 (n : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMapSucc (n + 1) = d.toSequenceOfBlowups.transitionMapSucc n := by
  rw [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.prepend_blowupMorphism_succ]

private theorem prepend_blowupMorphism_zero_eq_projectionToBase_consolidated274 :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMapSucc 0 = d.toSequenceOfBlowups.projectionToBase 0 := by
  rw [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.prepend_blowupMorphism_zero, SequenceOfBlowups.projectionToBase_zero,
    BlowupSequenceData.toSequenceOfBlowups_isoObjZero]

private theorem prepend_transitionMap_zero_consolidated274 (m : ℕ) (h : 0 ≤ m) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap h =
      (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase m := by
  rw [SequenceOfBlowups.projectionToBase_def, BlowupSequenceData.toSequenceOfBlowups_isoObjZero, BlowupSequenceData.prepend_isoObjZero,
    Iso.refl_hom]
  exact (Category.comp_id _).symm

private theorem prepend_transitionMap_succ_self_consolidated274 (n : ℕ) (h : n + 1 ≤ n + 1 + 1)
    (h' : n ≤ n + 1) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap h = d.toSequenceOfBlowups.transitionMap h' :=
  ((SequenceOfBlowups.blowupMorphism_eq_transitionMap (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups (n + 1)).symm.trans
      (prepend_blowupMorphism_succ_consolidated274 Z hZ d n)).trans
    (SequenceOfBlowups.blowupMorphism_eq_transitionMap d.toSequenceOfBlowups n)

private theorem prepend_transitionMap_succ_succ_consolidated274 {a b : ℕ} (hab : a ≤ b)
    (h : a + 1 ≤ b + 1) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap h = d.toSequenceOfBlowups.transitionMap hab := by
  revert h
  induction b, hab using Nat.le_induction with
  | base =>
      intro h
      exact (SequenceOfBlowups.transitionMap_self (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups h).trans
        (SequenceOfBlowups.transitionMap_self d.toSequenceOfBlowups (le_refl a)).symm
  | succ m hm ih =>
      intro h
      have e1 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap (Nat.add_le_add_right hm 1) =
          d.toSequenceOfBlowups.transitionMap hm := ih (Nat.add_le_add_right hm 1)
      have e2 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap (Nat.le_succ (m + 1)) =
          d.toSequenceOfBlowups.transitionMap (Nat.le_succ m) :=
        prepend_transitionMap_succ_self_consolidated274 Z hZ d m (Nat.le_succ (m + 1)) (Nat.le_succ m)
      have e3 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap h =
          (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap (Nat.le_succ (m + 1)) ≫
            (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap (Nat.add_le_add_right hm 1) :=
        (SequenceOfBlowups.transitionMap_trans (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups
          (Nat.add_le_add_right hm 1) (Nat.le_succ (m + 1))).symm
      rw [e3, e1, e2]
      exact SequenceOfBlowups.transitionMap_trans d.toSequenceOfBlowups hm (Nat.le_succ m)


end

private theorem blowupMorphism_comp_prependComparisonMap_consolidated274 {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (j : ℕ)
    (hj : j < (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.transitionMapSucc j ≫
        prependMapOfLELength_consolidated274 c Z hZ hZ' j (le_of_lt hj) =
      prependMapOfLELength_consolidated274 c Z hZ hZ' (j + 1) hj ≫
        (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap
          (le_of_lt (prependIndex_lt_prependIndex_succ_consolidated274 c Z hZ hZ' j hj)) := by
  cases j with
  | zero =>
      have hlen : 0 ≤ d'.toSequenceOfBlowups.length := Nat.zero_le _
      refine comp_eq_comp_of_heq_consolidated274 (prepend_schemeAt_zero_consolidated274 (Z.comap φ) hZ' d')
        (prepend_schemeAt_succ_consolidated274 (Z.comap φ) hZ' d' 0)
        (prepend_schemeAt_zero_consolidated274 Z hZ d)
        (prepend_schemeAt_succ_consolidated274 Z hZ d (c.idx 0))
        ((c.isPullback 0 hlen).w) ?_ ?_ ?_ ?_
      · exact heq_of_eq (prepend_blowupMorphism_zero_eq_projectionToBase_consolidated274 (Z.comap φ) hZ' d')
      · exact heq_of_eq (prependComparisonMap_zero_consolidated274 c Z hZ hZ' (le_of_lt hj))
      · exact heq_of_eq (prependComparisonMap_succ_consolidated274 c Z hZ hZ' 0 hj hlen)
      · exact heq_of_eq ((prepend_transitionMap_zero_consolidated274 Z hZ d (c.idx 0 + 1) (Nat.zero_le _)).trans
          (prepend_toSequenceOfBlowups_projectionToBase_succ_consolidated274 Z hZ d (c.idx 0)))
  | succ n =>
      have hn : n < d'.toSequenceOfBlowups.length := by
        have hlen := prepend_length_consolidated274 (Z.comap φ) hZ' d'
        omega
      refine comp_eq_comp_of_heq_consolidated274 (prepend_schemeAt_succ_consolidated274 (Z.comap φ) hZ' d' n)
        (prepend_schemeAt_succ_consolidated274 (Z.comap φ) hZ' d' (n + 1))
        (prepend_schemeAt_succ_consolidated274 Z hZ d (c.idx n))
        (prepend_schemeAt_succ_consolidated274 Z hZ d (c.idx (n + 1)))
        ((c.step n hn).symm) ?_ ?_ ?_ ?_
      · exact heq_of_eq (prepend_blowupMorphism_succ_consolidated274 (Z.comap φ) hZ' d' n)
      · exact heq_of_eq (prependComparisonMap_succ_consolidated274 c Z hZ hZ' n (le_of_lt hj) (le_of_lt hn))
      · exact heq_of_eq (prependComparisonMap_succ_consolidated274 c Z hZ hZ' (n + 1) hj hn)
      · exact heq_of_eq (prepend_transitionMap_succ_succ_consolidated274 Z hZ d (le_of_lt (c.idx_strictMono n hn))
          (Nat.add_le_add_right (le_of_lt (c.idx_strictMono n hn)) 1))

private theorem comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq_consolidated274 {A A' B B' : Scheme.{u}} (hA : A' = A) (hB : B = B')
    (g : A ⟶ B) (J : B.IdealSheafData) (K : A.IdealSheafData) (hK : K = J.comap g)
    (J' : A'.IdealSheafData) (Jb : B'.IdealSheafData)
    (hJb : HEq Jb J) (hJ' : HEq J' K) :
    J' = Jb.comap (eqToHom hA ≫ g ≫ eqToHom hB) := by
  subst hA
  subst hB
  have e1 : Jb = J := eq_of_heq hJb
  have e2 : J' = K := eq_of_heq hJ'
  rw [e1, e2, hK]
  simp

section
variable {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X} (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
include c

private theorem prepend_center_eq_comap_prependIndex_consolidated274 (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (j : ℕ)
    (hj : j < (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center j =
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (prependIndex c.idx j)).comap
        (prependMapOfLELength_consolidated274 c Z hZ hZ' j (le_of_lt hj)) := by
  cases j with
  | zero =>
      refine comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq_consolidated274 (prepend_schemeAt_zero_consolidated274 (Z.comap φ) hZ' d')
        (prepend_schemeAt_zero_consolidated274 Z hZ d).symm φ Z (Z.comap φ) rfl
        ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center 0)
        ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center 0) ?_ ?_
      · exact heq_of_eq ((BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend Z hZ d) 0).trans
          (BlowupSequenceData.prepend_center_zero Z hZ d))
      · exact heq_of_eq
          ((BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend (Z.comap φ) hZ' d') 0).trans
            (BlowupSequenceData.prepend_center_zero (Z.comap φ) hZ' d'))
  | succ n =>
      have hlen : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length
          = d'.toSequenceOfBlowups.length + 1 := prepend_length_consolidated274 (Z.comap φ) hZ' d'
      have hn' : n < d'.toSequenceOfBlowups.length := by omega
      refine comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq_consolidated274 (prepend_schemeAt_succ_consolidated274 (Z.comap φ) hZ' d' n)
        (prepend_schemeAt_succ_consolidated274 Z hZ d (c.idx n)).symm (c.map n (le_of_lt hn'))
        (d.toSequenceOfBlowups.center (c.idx n)) (d'.toSequenceOfBlowups.center n) (c.center_comap n hn')
        ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center (n + 1))
        ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (c.idx n + 1)) ?_ ?_
      · exact heq_of_eq
          ((BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend Z hZ d) (c.idx n + 1)).trans
            ((BlowupSequenceData.prepend_center_succ Z hZ d (c.idx n)).trans
              (BlowupSequenceData.toSequenceOfBlowups_center d (c.idx n)).symm))
      · exact heq_of_eq
          ((BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend (Z.comap φ) hZ' d') (n + 1)).trans
            ((BlowupSequenceData.prepend_center_succ (Z.comap φ) hZ' d' n).trans
              (BlowupSequenceData.toSequenceOfBlowups_center d' n).symm))

private theorem prepend_center_ne_top_consolidated274 (_hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (hne : Z.comap φ ≠ ⊤) (j : ℕ)
    (hj : j < (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center j ≠ ⊤ := by
  have hlen : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length = d'.toSequenceOfBlowups.length + 1 :=
    prepend_length_consolidated274 (Z.comap φ) hZ' d'
  cases j with
  | zero =>
      have h0 : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center 0 = Z.comap φ :=
        (BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend (Z.comap φ) hZ' d') 0).trans
          (BlowupSequenceData.prepend_center_zero (Z.comap φ) hZ' d')
      intro htop
      exact hne (h0.symm.trans htop)
  | succ n =>
      have hn : n < d'.toSequenceOfBlowups.length := by omega
      have h1 : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center (n + 1) =
          d'.toSequenceOfBlowups.center n :=
        (BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend (Z.comap φ) hZ' d') (n + 1)).trans
          ((BlowupSequenceData.prepend_center_succ (Z.comap φ) hZ' d' n).trans
            (BlowupSequenceData.toSequenceOfBlowups_center d' n).symm)
      intro htop
      exact c.center_ne_top n hn (h1.symm.trans htop)


end

private theorem prepend_center_succ_consolidated274 {Y : Scheme.{u}} (Z : Y.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y) (n : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (n + 1) = d.toSequenceOfBlowups.center n :=
  (BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend Z hZ d) (n + 1)).trans
    ((BlowupSequenceData.prepend_center_succ Z hZ d n).trans (BlowupSequenceData.toSequenceOfBlowups_center d n).symm)

private theorem ne_projectionToBase_of_forall_prependIndex_ne_consolidated274 {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (i : ℕ)
    (hi : i < (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length)
    (hmiss : ∀ j : ℕ, j < (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length →
      prependIndex c.idx j ≠ i)
    (z : ↥((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt i))
    (hz : z ∈ ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center i).support) (x' : ↥X') :
    φ.base x' ≠ ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase i).base z := by
  have hlen' : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length = d'.toSequenceOfBlowups.length + 1 :=
    prepend_length_consolidated274 (Z.comap φ) hZ' d'
  have hlen : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length = d.toSequenceOfBlowups.length + 1 :=
    prepend_length_consolidated274 Z hZ d
  have h0 : prependIndex c.idx 0 ≠ i := hmiss 0 (by omega)
  rw [prependIndex_zero] at h0
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = n + 1 := ⟨i - 1, by omega⟩
  have hn : n < d.toSequenceOfBlowups.length := by omega
  have hmiss' : ∀ m : ℕ, m < d'.toSequenceOfBlowups.length → c.idx m ≠ n := by
    intro m hm hmn
    exact hmiss (m + 1) (by omega) (by rw [prependIndex_succ, hmn])
  have hzc : z ∈ (d.toSequenceOfBlowups.center n).support := by
    have hz2 := hz
    rw [prepend_center_succ_consolidated274 Z hZ d n] at hz2
    exact hz2
  intro heq
  refine c.omitted n hn hmiss' z hzc x' ?_
  rw [← prepend_toSequenceOfBlowups_projectionToBase_succ_consolidated274 Z hZ d n]
  exact heq

def prepend {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (hne : Z.comap φ ≠ ⊤) :
    SequenceOfBlowupsPullback φ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups
      (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups where
  idx := prependIndex c.idx
  map := prependMapOfLELength_consolidated274 c Z hZ hZ'
  idx_length := prependIndex_length_eq_prepend_length_consolidated274 c Z hZ hZ'
  idx_lt := prependIndex_lt_prepend_length_consolidated274 c Z hZ hZ'
  idx_strictMono := prependIndex_lt_prependIndex_succ_consolidated274 c Z hZ hZ'
  isPullback := isPullback_prependComparisonMap_consolidated274 c Z hZ hZ'
  step := blowupMorphism_comp_prependComparisonMap_consolidated274 c Z hZ hZ'
  center_comap := prepend_center_eq_comap_prependIndex_consolidated274 c Z hZ hZ'
  center_ne_top := prepend_center_ne_top_consolidated274 c Z hZ hZ' hne
  omitted := ne_projectionToBase_of_forall_prependIndex_ne_consolidated274 c Z hZ hZ'

private def mapToPrependSuccIndex_consolidated274 {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (j : ℕ) (hj : j ≤ d'.toSequenceOfBlowups.length) :
    d'.toSequenceOfBlowups.schemeAt j ⟶ (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt (succIndex c.idx j) :=
  c.map j hj ≫ eqToHom (prepend_schemeAt_succ_consolidated274 Z hZ d (c.idx j)).symm

section
variable {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X} (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)

private theorem succIndex_length_eq_prepend_length_consolidated274 (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) :
    succIndex c.idx d'.toSequenceOfBlowups.length = (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length := by
  rw [succIndex_apply, prepend_length_consolidated274, c.idx_length]

private theorem succIndex_lt_prepend_length_consolidated274 (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (j : ℕ) (hj : j < d'.toSequenceOfBlowups.length) :
    succIndex c.idx j < (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length := by
  have hlen : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length = d.toSequenceOfBlowups.length + 1 :=
    prepend_length_consolidated274 Z hZ d
  have hc : c.idx j < d.toSequenceOfBlowups.length := c.idx_lt j hj
  rw [hlen, succIndex_apply]
  omega

private theorem succIndex_lt_succIndex_succ_consolidated274 (_hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (j : ℕ) (hj : j < d'.toSequenceOfBlowups.length) :
    succIndex c.idx j < succIndex c.idx (j + 1) := by
  have h : c.idx j < c.idx (j + 1) := c.idx_strictMono j hj
  simp only [succIndex_apply]
  omega

private theorem isPullback_comparisonMapOfComapEqTop_consolidated274 (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (j : ℕ) (hj : j ≤ d'.toSequenceOfBlowups.length) :
    IsPullback (mapToPrependSuccIndex_consolidated274 c Z hZ j hj) (d'.toSequenceOfBlowups.projectionToBase j)
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (succIndex c.idx j)) φ := by
  have h1 : mapToPrependSuccIndex_consolidated274 c Z hZ j hj = c.map j hj := by
    show c.map j hj ≫ 𝟙 (d.toSequenceOfBlowups.schemeAt (c.idx j)) = c.map j hj
    simp
  have h2 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (succIndex c.idx j) =
      d.toSequenceOfBlowups.projectionToBase (c.idx j) := prepend_toSequenceOfBlowups_projectionToBase_succ_consolidated274 Z hZ d (c.idx j)
  rw [h1, h2]
  exact c.isPullback j hj


end

private theorem comp_eqToHom_refl_consolidated274 {A B : Scheme.{u}} (f : A ⟶ B) (h : B = B) :
    f ≫ eqToHom h = f := by
  rw [eqToHom_refl, Category.comp_id]

section
variable {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X} (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (j : ℕ)

private theorem comparisonMapOfComapEqTop_eq_map_consolidated274 (hj : j ≤ d'.toSequenceOfBlowups.length) :
    mapToPrependSuccIndex_consolidated274 c Z hZ j hj = c.map j hj :=
  comp_eqToHom_refl_consolidated274 (c.map j hj) (prepend_schemeAt_succ_consolidated274 Z hZ d (c.idx j)).symm

private theorem blowupMorphism_comp_comparisonMapOfComapEqTop_consolidated274 (hj : j < d'.toSequenceOfBlowups.length) :
    d'.toSequenceOfBlowups.transitionMapSucc j ≫ mapToPrependSuccIndex_consolidated274 c Z hZ j (le_of_lt hj) =
      mapToPrependSuccIndex_consolidated274 c Z hZ (j + 1) hj ≫
        (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap
          (le_of_lt (succIndex_lt_succIndex_succ_consolidated274 c Z hZ j hj)) := by
  have h1 : mapToPrependSuccIndex_consolidated274 c Z hZ j (le_of_lt hj) = c.map j (le_of_lt hj) :=
    comparisonMapOfComapEqTop_eq_map_consolidated274 c Z hZ j (le_of_lt hj)
  have h2 : mapToPrependSuccIndex_consolidated274 c Z hZ (j + 1) hj = c.map (j + 1) hj :=
    comparisonMapOfComapEqTop_eq_map_consolidated274 c Z hZ (j + 1) hj
  have hdown : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap
        (le_of_lt (succIndex_lt_succIndex_succ_consolidated274 c Z hZ j hj)) =
      d.toSequenceOfBlowups.transitionMap (le_of_lt (c.idx_strictMono j hj)) :=
    prepend_transitionMap_succ_succ_consolidated274 Z hZ d (le_of_lt (c.idx_strictMono j hj))
      (le_of_lt (succIndex_lt_succIndex_succ_consolidated274 c Z hZ j hj))
  rw [h1, h2, hdown]
  exact c.step j hj


end

private theorem comap_eq_comap_comp_eqToHom_of_heq_consolidated274 {A B B' : Scheme.{u}} (hB : B = B') (g : A ⟶ B)
    (J : B.IdealSheafData) (J' : B'.IdealSheafData) (K : A.IdealSheafData)
    (hK : K = J.comap g) (hJ : HEq J' J) :
    K = J'.comap (g ≫ eqToHom hB) := by
  subst hB
  have h1 : J' = J := eq_of_heq hJ
  subst h1
  rw [hK]
  simp

section
variable {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X} (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups)
include c

private theorem center_eq_comap_prepend_center_succIndex_consolidated274 (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (j : ℕ) (hj : j < d'.toSequenceOfBlowups.length) :
    d'.toSequenceOfBlowups.center j =
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (succIndex c.idx j)).comap
        (mapToPrependSuccIndex_consolidated274 c Z hZ j (le_of_lt hj)) := by
  have hc : d'.toSequenceOfBlowups.center j =
      (d.toSequenceOfBlowups.center (c.idx j)).comap (c.map j (le_of_lt hj)) := c.center_comap j hj
  have hJ : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (c.idx j + 1) =
      d.toSequenceOfBlowups.center (c.idx j) :=
    (BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend Z hZ d) (c.idx j + 1)).trans
      ((BlowupSequenceData.prepend_center_succ Z hZ d (c.idx j)).trans
        (BlowupSequenceData.toSequenceOfBlowups_center d (c.idx j)).symm)
  show d'.toSequenceOfBlowups.center j =
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (c.idx j + 1)).comap
        (c.map j (le_of_lt hj) ≫ eqToHom (prepend_schemeAt_succ_consolidated274 Z hZ d (c.idx j)).symm)
  exact comap_eq_comap_comp_eqToHom_of_heq_consolidated274 (prepend_schemeAt_succ_consolidated274 Z hZ d (c.idx j)).symm
    (c.map j (le_of_lt hj)) (d.toSequenceOfBlowups.center (c.idx j))
    ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (c.idx j + 1))
    (d'.toSequenceOfBlowups.center j) hc (heq_of_eq hJ)

private theorem center_ne_top_of_prepend_comap_eq_top_consolidated274 (_Z : X.IdealSheafData)
    (_hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) _Z) (j : ℕ) (hj : j < d'.toSequenceOfBlowups.length) :
    d'.toSequenceOfBlowups.center j ≠ ⊤ := c.center_ne_top j hj

private theorem ne_projectionToBase_of_forall_succIndex_ne_consolidated274 (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (htop : Z.comap φ = ⊤) (i : ℕ)
    (hi : i < (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length)
    (hmiss : ∀ j : ℕ, j < d'.toSequenceOfBlowups.length → succIndex c.idx j ≠ i)
    (z : ↥((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt i))
    (hz : z ∈ ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center i).support) (x' : ↥X') :
    φ.base x' ≠ ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase i).base z := by
  have hlen : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length = d.toSequenceOfBlowups.length + 1 :=
    prepend_length_consolidated274 Z hZ d
  cases i with
  | zero =>
      intro heq
      have hc0 : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center 0 = Z :=
        (BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend Z hZ d) 0).trans
          (BlowupSequenceData.prepend_center_zero Z hZ d)
      have hzZ : z ∈ Z.support := by
        rw [hc0] at hz
        exact hz
      have hst : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase 0 = 𝟙 X :=
        prepend_toSequenceOfBlowups_projectionToBase_zero_consolidated274 Z hZ d
      have hb : φ.base x' ∈ Z.support := by
        rw [heq, hst]
        exact hzZ
      have hmem : x' ∈ (Z.comap φ).support :=
        AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.mpr hb
      exact AlgebraicGeometry.Scheme.IdealSheafData.ne_top_of_mem_support
        (Z.comap φ) x' hmem htop
  | succ n =>
      have hn : n < d.toSequenceOfBlowups.length := by omega
      have hmiss' : ∀ m : ℕ, m < d'.toSequenceOfBlowups.length → c.idx m ≠ n := by
        intro m hm hmn
        exact hmiss m hm (by rw [succIndex_apply, hmn])
      have hzc : z ∈ (d.toSequenceOfBlowups.center n).support := by
        have hz2 := hz
        rw [prepend_center_succ_consolidated274 Z hZ d n] at hz2
        exact hz2
      intro heq
      refine c.omitted n hn hmiss' z hzc x' ?_
      rw [← prepend_toSequenceOfBlowups_projectionToBase_succ_consolidated274 Z hZ d n]
      exact heq


end

def prependOfComapEqTop {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (htop : Z.comap φ = ⊤) :
    SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups where
  idx := succIndex c.idx
  map := mapToPrependSuccIndex_consolidated274 c Z hZ
  idx_length := succIndex_length_eq_prepend_length_consolidated274 c Z hZ
  idx_lt := succIndex_lt_prepend_length_consolidated274 c Z hZ
  idx_strictMono := succIndex_lt_succIndex_succ_consolidated274 c Z hZ
  isPullback := isPullback_comparisonMapOfComapEqTop_consolidated274 c Z hZ
  step := blowupMorphism_comp_comparisonMapOfComapEqTop_consolidated274 c Z hZ
  center_comap := center_eq_comap_prepend_center_succIndex_consolidated274 c Z hZ
  center_ne_top := center_ne_top_of_prepend_comap_eq_top_consolidated274 c Z hZ
  omitted := ne_projectionToBase_of_forall_succIndex_ne_consolidated274 c Z hZ htop

end SequenceOfBlowupsPullback

section
variable {X X' : Scheme.{u}} {φ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X} (h : IsPullbackBlowupSequence φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z)
include h

theorem IsPullbackBlowupSequence.prepend_of_comap_ne_top (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (hne : Z.comap φ ≠ ⊤) :
    IsPullbackBlowupSequence φ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups
      (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups := by
  obtain ⟨c⟩ := h.nonempty_sequenceOfBlowupsPullback
  exact (c.prepend Z hZ hZ' hne).isPullbackSequenceOfBlowups

theorem IsPullbackBlowupSequence.prepend_of_comap_eq_top (htop : Z.comap φ = ⊤) :
    IsPullbackBlowupSequence φ d'.toSequenceOfBlowups (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups := by
  obtain ⟨c⟩ := h.nonempty_sequenceOfBlowupsPullback
  exact (c.prependOfComapEqTop Z hZ htop).isPullbackSequenceOfBlowups


end

private def prependMapOfLevelwise_consolidated274 {X X' : Scheme.{u}} (φ : X' ⟶ X) {d' : BlowupSequenceData X'}
    {d : BlowupSequenceData X} (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z)
    (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ))
    (σ : ∀ i : ℕ, i ≤ d'.toSequenceOfBlowups.length → (d'.toSequenceOfBlowups.schemeAt i ⟶ d.toSequenceOfBlowups.schemeAt i)) :
    ∀ i : ℕ, i ≤ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length →
      ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.schemeAt i ⟶
        (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt i)
  | 0, _ =>
      eqToHom (SequenceOfBlowupsPullback.prepend_schemeAt_zero_consolidated274 (Z.comap φ) hZ' d') ≫ φ ≫
        eqToHom (SequenceOfBlowupsPullback.prepend_schemeAt_zero_consolidated274 Z hZ d).symm
  | (n + 1), h =>
      eqToHom (SequenceOfBlowupsPullback.prepend_schemeAt_succ_consolidated274 (Z.comap φ) hZ' d' n) ≫
        σ n (SequenceOfBlowupsPullback.le_length_of_succ_le_prepend_length_consolidated274 (Z.comap φ) hZ' d' n h) ≫
        eqToHom (SequenceOfBlowupsPullback.prepend_schemeAt_succ_consolidated274 Z hZ d n).symm

section
variable {X X' : Scheme.{u}} (φ : X' ⟶ X) {d' : BlowupSequenceData X'} {d : BlowupSequenceData X} (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) (σ : ∀ i : ℕ, i ≤ d'.toSequenceOfBlowups.length → (d'.toSequenceOfBlowups.schemeAt i ⟶ d.toSequenceOfBlowups.schemeAt i))

private theorem strictPrependComparisonMap_zero_consolidated274 (h : 0 ≤ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length) :
    prependMapOfLevelwise_consolidated274 φ Z hZ hZ' σ 0 h = φ := by
  show 𝟙 X' ≫ φ ≫ 𝟙 X = φ
  simp

private theorem strictPrependComparisonMap_succ_consolidated274 (n : ℕ)
    (h : n + 1 ≤ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length)
    (hn : n ≤ d'.toSequenceOfBlowups.length) :
    prependMapOfLevelwise_consolidated274 φ Z hZ hZ' σ (n + 1) h = σ n hn := by
  show 𝟙 (d'.toSequenceOfBlowups.schemeAt n) ≫ σ n hn ≫ 𝟙 (d.toSequenceOfBlowups.schemeAt n) = σ n hn
  simp


end

private theorem prepend_isoObjZero_hom_consolidated274 {Y : Scheme.{u}} (Z : Y.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.isoZero.hom = 𝟙 Y := by
  rw [BlowupSequenceData.toSequenceOfBlowups_isoObjZero, BlowupSequenceData.prepend_isoObjZero, Iso.refl_hom]

private theorem eqToHom_conj_comp_eq_comp_of_heq_id_consolidated274 {A B P Q : Scheme.{u}} (eP : P = A) (eQ : Q = B)
    (ψ : A ⟶ B) (I : Q ⟶ B) (J : P ⟶ A) (hI : HEq I (𝟙 B)) (hJ : HEq J (𝟙 A)) :
    (eqToHom eP ≫ ψ ≫ eqToHom eQ.symm) ≫ I = J ≫ ψ := by
  subst eP
  subst eQ
  have h1 := eq_of_heq hI
  have h2 := eq_of_heq hJ
  rw [h1, h2]
  simp

section
variable {Y : Scheme.{u}} (Z : Y.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y)

private theorem prepend_blowupMorphism_zero_consolidated274 :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMapSucc 0 = d.toSequenceOfBlowups.isoZero.hom := by
  rw [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.prepend_blowupMorphism_zero, BlowupSequenceData.toSequenceOfBlowups_isoObjZero]

private theorem prepend_center_zero_consolidated274 :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center 0 = Z :=
  (BlowupSequenceData.toSequenceOfBlowups_center (BlowupSequenceData.prepend Z hZ d) 0).trans
    (BlowupSequenceData.prepend_center_zero Z hZ d)


end

private theorem isPullback_congr_consolidated274 {P Q R S : Scheme.{u}} {f f' : P ⟶ Q} {g g' : P ⟶ R}
    {h h' : Q ⟶ S} {k k' : R ⟶ S} (hf : f = f') (hg : g = g') (hh : h = h') (hk : k = k')
    (H : IsPullback f' g' h' k') : IsPullback f g h k := by
  rw [hf, hg, hh, hk]
  exact H

theorem IsStrictPullbackBlowupSeq.prepend {X X' : Scheme.{u}} {φ : X' ⟶ X} {d' : BlowupSequenceData X'}
    {d : BlowupSequenceData X} (h : IsStrictPullbackBlowupSeq φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X') (Z.comap φ)) :
    IsStrictPullbackBlowupSeq φ (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups
      (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups := by
  obtain ⟨hlen, σ, h0, hpb, hcen⟩ := h
  refine ⟨?_, prependMapOfLevelwise_consolidated274 φ Z hZ hZ' σ, ?_, ?_, ?_⟩
  · rw [SequenceOfBlowupsPullback.prepend_length_consolidated274 (Z.comap φ) hZ' d',
      SequenceOfBlowupsPullback.prepend_length_consolidated274 Z hZ d, hlen]
  · exact eqToHom_conj_comp_eq_comp_of_heq_id_consolidated274
      (SequenceOfBlowupsPullback.prepend_schemeAt_zero_consolidated274 (Z.comap φ) hZ' d')
      (SequenceOfBlowupsPullback.prepend_schemeAt_zero_consolidated274 Z hZ d) φ
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.isoZero.hom)
      ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.isoZero.hom)
      (heq_of_eq (prepend_isoObjZero_hom_consolidated274 Z hZ d))
      (heq_of_eq (prepend_isoObjZero_hom_consolidated274 (Z.comap φ) hZ' d'))
  · intro i hi
    cases i with
    | zero =>
        have hz : (0 : ℕ) ≤ d'.toSequenceOfBlowups.length := Nat.zero_le _
        have hsq : IsPullback (σ 0 hz) d'.toSequenceOfBlowups.isoZero.hom d.toSequenceOfBlowups.isoZero.hom φ :=
          (IsPullback.of_horiz_isIso ⟨h0.symm⟩).flip
        exact isPullback_congr_consolidated274 (strictPrependComparisonMap_succ_consolidated274 φ Z hZ hZ' σ 0 hi hz)
          (prepend_blowupMorphism_zero_consolidated274 (Z.comap φ) hZ' d') (prepend_blowupMorphism_zero_consolidated274 Z hZ d)
          (strictPrependComparisonMap_zero_consolidated274 φ Z hZ hZ' σ hi.le) hsq
    | succ n =>
        have hlen' : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length
            = d'.toSequenceOfBlowups.length + 1 := SequenceOfBlowupsPullback.prepend_length_consolidated274 (Z.comap φ) hZ' d'
        have hn : n < d'.toSequenceOfBlowups.length := by omega
        exact isPullback_congr_consolidated274 (strictPrependComparisonMap_succ_consolidated274 φ Z hZ hZ' σ (n + 1) hi hn)
          (SequenceOfBlowupsPullback.prepend_blowupMorphism_succ_consolidated274 (Z.comap φ) hZ' d' n)
          (SequenceOfBlowupsPullback.prepend_blowupMorphism_succ_consolidated274 Z hZ d n)
          (strictPrependComparisonMap_succ_consolidated274 φ Z hZ hZ' σ n hi.le hn.le) (hpb n hn)
  · intro i hi
    cases i with
    | zero =>
        exact SequenceOfBlowupsPullback.comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq_consolidated274
          (SequenceOfBlowupsPullback.prepend_schemeAt_zero_consolidated274 (Z.comap φ) hZ' d')
          (SequenceOfBlowupsPullback.prepend_schemeAt_zero_consolidated274 Z hZ d).symm φ Z (Z.comap φ) rfl
          ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center 0)
          ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center 0)
          (heq_of_eq (prepend_center_zero_consolidated274 Z hZ d))
          (heq_of_eq (prepend_center_zero_consolidated274 (Z.comap φ) hZ' d'))
    | succ n =>
        have hlen' : (BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.length
            = d'.toSequenceOfBlowups.length + 1 := SequenceOfBlowupsPullback.prepend_length_consolidated274 (Z.comap φ) hZ' d'
        have hn : n < d'.toSequenceOfBlowups.length := by omega
        exact SequenceOfBlowupsPullback.comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq_consolidated274
          (SequenceOfBlowupsPullback.prepend_schemeAt_succ_consolidated274 (Z.comap φ) hZ' d' n)
          (SequenceOfBlowupsPullback.prepend_schemeAt_succ_consolidated274 Z hZ d n).symm (σ n hn.le)
          (d.toSequenceOfBlowups.center n) (d'.toSequenceOfBlowups.center n) (hcen n hn)
          ((BlowupSequenceData.prepend (Z.comap φ) hZ' d').toSequenceOfBlowups.center (n + 1))
          ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (n + 1))
          (heq_of_eq (SequenceOfBlowupsPullback.prepend_center_succ_consolidated274 Z hZ d n))
          (heq_of_eq (SequenceOfBlowupsPullback.prepend_center_succ_consolidated274 (Z.comap φ) hZ' d' n))


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
section

open TopologicalSpace

section

def EffectiveCartierSupportContainsNoComponent : Prop :=
  ∀ (X : Scheme.{u}) (D : X.IdealSheafData), Blowup.IsLocallyGeneratedByNonZeroDivisor D →
    ∀ C ∈ irreducibleComponents (X : Type u), ¬ C ⊆ (D.support : Set (X : Type u))

theorem effectiveCartierSupportContainsNoComponent : EffectiveCartierSupportContainsNoComponent.{u} :=
  fun _ _ hD _ hC => hD.not_irreducibleComponent_subset_support hC

theorem nonzeroOnComponents_comap_iso_hom {X Y : Scheme.{u}} (f : X ≅ Y) (I : Y.IdealSheafData)
    (h : NonzeroOnComponents I) : NonzeroOnComponents (I.comap f.hom) :=
  PrincipalizationIsoTransport.nonzeroOnComponents_comap_iso f I h

section
variable {α : Type u}

private theorem isPreirreducible_inter_of_isOpen_consolidated298 [TopologicalSpace α] {T U : Set α}
    (hT : IsPreirreducible T) (hU : IsOpen U) : IsPreirreducible (T ∩ U) := by
  intro V W hV hW hVne hWne
  obtain ⟨a, haTU, haV⟩ := hVne
  obtain ⟨b, hbTU, hbW⟩ := hWne
  obtain ⟨x, hxT, hx1, hx2⟩ :=
    hT (V ∩ U) (W ∩ U) (hV.inter hU) (hW.inter hU)
      ⟨a, haTU.1, haV, haTU.2⟩ ⟨b, hbTU.1, hbW, hbTU.2⟩
  exact ⟨x, ⟨hxT, hx1.2⟩, hx1.1, hx2.1⟩

private theorem isPreirreducible_preimage_val_consolidated298 [TopologicalSpace α] {U V : Set α}
    (hVU : V ⊆ U) (hV : IsPreirreducible V) :
    IsPreirreducible ((Subtype.val : U → α) ⁻¹' V) := by
  intro O₁ O₂ hO₁ hO₂ h₁ h₂
  obtain ⟨G₁, hG₁, rfl⟩ := isOpen_induced_iff.mp hO₁
  obtain ⟨G₂, hG₂, rfl⟩ := isOpen_induced_iff.mp hO₂
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  obtain ⟨x, hxV, hx1, hx2⟩ := hV G₁ G₂ hG₁ hG₂ ⟨a.1, ha.1, ha.2⟩ ⟨b.1, hb.1, hb.2⟩
  exact ⟨⟨x, hVU hxV⟩, hxV, hx1, hx2⟩

private theorem exists_irreducibleComponent_subset_of_section_consolidated298 {β : Type u}
    [TopologicalSpace α] [TopologicalSpace β]
    (f : α → β) (hf : Continuous f) (Uc : Set β) (hUc : IsOpen Uc)
    (g : ↥Uc → α) (hgc : Continuous g) (hgf : ∀ y, f (g y) = (y : β))
    (hgs : ∀ x, f x ∈ Uc → ∃ y, g y = x)
    (C : Set α) (hC : C ∈ irreducibleComponents α) (x₀ : α) (hx₀ : x₀ ∈ C) (hx₀U : f x₀ ∈ Uc)
    (K : Set β) (hK : IsClosed K) (hCK : C ⊆ f ⁻¹' K) :
    ∃ T ∈ irreducibleComponents β, T ⊆ K := by
  have hCirr : IsIrreducible C := hC.1
  have hVcOpen : IsOpen (f ⁻¹' Uc) := hUc.preimage hf
  have hWne : (C ∩ f ⁻¹' Uc).Nonempty := ⟨x₀, hx₀, hx₀U⟩
  have hWirr : IsIrreducible (C ∩ f ⁻¹' Uc) :=
    ⟨hWne, isPreirreducible_inter_of_isOpen_consolidated298 hCirr.2 hVcOpen⟩
  have hImIrr : IsIrreducible (f '' (C ∩ f ⁻¹' Uc)) := hWirr.image f hf.continuousOn
  obtain ⟨T, hT, hTsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hImIrr
  have hTirr : IsIrreducible T := hT.1
  have hy₀T : f x₀ ∈ T := hTsub ⟨x₀, ⟨hx₀, hx₀U⟩, rfl⟩
  have hSne : (T ∩ Uc).Nonempty := ⟨f x₀, hy₀T, hx₀U⟩
  have hSirr : IsIrreducible (T ∩ Uc) := ⟨hSne, isPreirreducible_inter_of_isOpen_consolidated298 hTirr.2 hUc⟩
  have hpre : IsIrreducible ((Subtype.val : ↥Uc → β) ⁻¹' (T ∩ Uc)) :=
    ⟨⟨⟨f x₀, hx₀U⟩, hy₀T, hx₀U⟩, isPreirreducible_preimage_val_consolidated298 (fun y hy => hy.2) hSirr.2⟩
  have hVeq : f ⁻¹' (T ∩ Uc) = g '' ((Subtype.val : ↥Uc → β) ⁻¹' (T ∩ Uc)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hgs x hx.2
      refine ⟨y, ?_, hy⟩
      have h3 : f (g y) = (y : β) := hgf y
      rw [hy] at h3
      show (y : β) ∈ T ∩ Uc
      rw [← h3]
      exact hx
    · rintro ⟨y, hy, rfl⟩
      show f (g y) ∈ T ∩ Uc
      rw [hgf y]
      exact hy
  have hVirr : IsIrreducible (f ⁻¹' (T ∩ Uc)) := by
    rw [hVeq]
    exact hpre.image g hgc.continuousOn
  have hWV : C ∩ f ⁻¹' Uc ⊆ f ⁻¹' (T ∩ Uc) := fun x hx => ⟨hTsub ⟨x, hx, rfl⟩, hx.2⟩
  have hCcl : C ⊆ closure (C ∩ f ⁻¹' Uc) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen hCirr.2 hVcOpen hWne
  have hVC : f ⁻¹' (T ∩ Uc) ⊆ C :=
    subset_closure.trans (hC.2 hVirr.closure (hCcl.trans (closure_mono hWV)))
  have hVW : f ⁻¹' (T ∩ Uc) ⊆ C ∩ f ⁻¹' Uc := fun x hx => ⟨hVC hx, hx.2⟩
  have hTUK : T ∩ Uc ⊆ K := by
    intro y hy
    have hx : g ⟨y, hy.2⟩ ∈ C ∩ f ⁻¹' Uc := by
      refine hVW ?_
      show f (g ⟨y, hy.2⟩) ∈ T ∩ Uc
      rw [hgf ⟨y, hy.2⟩]
      exact hy
    have h5 : f (g ⟨y, hy.2⟩) ∈ K := hCK hx.1
    rw [hgf ⟨y, hy.2⟩] at h5
    exact h5
  refine ⟨T, hT, ?_⟩
  have hd : T ⊆ closure (T ∩ Uc) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen hTirr.2 hUc hSne
  exact hd.trans (closure_minimal hTUK hK)


end

private theorem coe_support_comap_eq_preimage_consolidated298 {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData) :
    ((I.comap f).support : Set ↥X) = ⇑f.base ⁻¹' (I.support : Set ↥Y) := by
  ext x
  simp [Scheme.IdealSheafData.support_comap]

private theorem exists_section_off_center_consolidated298 {X X' : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    ∃ g : ↥(((Z.support : Set ↥X))ᶜ) → ↥X', Continuous g ∧
      (∀ y, ⇑π.base (g y) = (y : ↥X)) ∧
      (∀ x : ↥X', ⇑π.base x ∈ ((Z.support : Set ↥X))ᶜ → ∃ y, g y = x) := by
  have := Blowup.blowupIsIsoOffCenter X X' π Z hπ
  have hinvhom : ∀ (A B : Scheme.{u}) (f : A ≅ B) (z : ↥B), f.hom.base (f.inv.base z) = z := by
    intro A B f z
    simp
  have hhominv : ∀ (A B : Scheme.{u}) (f : A ≅ B) (z : ↥A), f.inv.base (f.hom.base z) = z := by
    intro A B f z
    simp
  let e := asIso (π ∣_ Z.support.compl)
  have hmem : ∀ y : ↥(((Z.support : Set ↥X))ᶜ), (y : ↥X) ∈ Z.support.compl := fun y => y.2
  have hcont : Continuous (⇑e.inv.base) := e.inv.continuous
  refine ⟨fun y => (e.inv.base ⟨(y : ↥X), hmem y⟩).1, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp
      (hcont.comp (continuous_subtype_val.subtype_mk hmem))
  · intro y
    have h1 : e.hom.base (e.inv.base ⟨(y : ↥X), hmem y⟩) = ⟨(y : ↥X), hmem y⟩ :=
      hinvhom _ _ e _
    have h2 := morphismRestrict_base_coe π Z.support.compl (e.inv.base ⟨(y : ↥X), hmem y⟩)
    show ⇑π.base (e.inv.base ⟨(y : ↥X), hmem y⟩).1 = (y : ↥X)
    rw [← h2]
    exact congrArg Subtype.val h1
  · intro x hx
    have hx' : x ∈ π ⁻¹ᵁ Z.support.compl := hx
    refine ⟨⟨⇑π.base x, hx⟩, ?_⟩
    have hb : e.hom.base (⟨x, hx'⟩ : ↥(π ⁻¹ᵁ Z.support.compl).toScheme)
        = ⟨⇑π.base x, hmem ⟨⇑π.base x, hx⟩⟩ :=
      Subtype.ext (morphismRestrict_base_coe π Z.support.compl ⟨x, hx'⟩)
    have hc : e.inv.base (e.hom.base (⟨x, hx'⟩ : ↥(π ⁻¹ᵁ Z.support.compl).toScheme))
        = ⟨x, hx'⟩ := hhominv _ _ e _
    rw [hb] at hc
    exact congrArg Subtype.val hc

theorem nonzeroOnComponents_of_pow_mul_eq_comap (hcart : EffectiveCartierSupportContainsNoComponent.{u})
    {X X' : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (m : ℕ)
    (I : X.IdealSheafData) (I' : X'.IdealSheafData)
    (htr : (Z.comap π) ^ m * I' = I.comap π)
    (hI : NonzeroOnComponents I) : NonzeroOnComponents I' := by
  rw [nonzeroOnComponents_iff] at hI ⊢
  intro C hC hsub
  have hsub2 : C ⊆ ((I.comap π).support : Set ↥X') := by
    intro x hx
    have h1 : stalkIdeal I' x ≠ ⊤ := (mem_support_iff_stalkIdeal_ne_top I' x).mp (hsub hx)
    refine (mem_support_iff_stalkIdeal_ne_top (I.comap π) x).mpr ?_
    rw [← htr, stalkIdeal_mul]
    intro hcon
    have hle : stalkIdeal ((Z.comap π) ^ m) x * stalkIdeal I' x ≤ stalkIdeal I' x :=
      le_trans Ideal.mul_le_inf inf_le_right
    rw [hcon] at hle
    exact h1 (top_le_iff.mp hle)
  obtain ⟨x₀, hx₀C, hx₀E⟩ := Set.not_subset.mp (hcart X' (Z.comap π) hπ.1 C hC)
  have hx₀U : ⇑π.base x₀ ∈ ((Z.support : Set ↥X))ᶜ := by
    intro hmem
    refine hx₀E ?_
    rw [coe_support_comap_eq_preimage_consolidated298 π Z]
    exact hmem
  have hCK : C ⊆ ⇑π.base ⁻¹' ((I.support : Set ↥X)) := by
    rw [← coe_support_comap_eq_preimage_consolidated298 π I]
    exact hsub2
  obtain ⟨g, hgc, hgf, hgs⟩ := exists_section_off_center_consolidated298 π Z hπ
  obtain ⟨T, hTcomp, hTK⟩ :=
    exists_irreducibleComponent_subset_of_section_consolidated298 (⇑π.base) π.continuous (((Z.support : Set ↥X))ᶜ)
      (Z.support.2.isOpen_compl) g hgc hgf hgs C hC x₀ hx₀C hx₀U
      ((I.support : Set ↥X)) I.support.2 hCK
  exact hI T hTcomp hTK

namespace MarkedSequenceOfBlowups

section
variable (hcart : EffectiveCartierSupportContainsNoComponent.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (s : T.SequenceOfBlowups)
include hcart hT

theorem nonzeroOnComponents_ideal_of_isAdmissible :
    ∀ t : ℕ, t ≤ s.toSequenceOfBlowups.length → NonzeroOnComponents (s.ideal t) := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [s.ideal_zero]
    exact nonzeroOnComponents_comap_iso_hom s.toSequenceOfBlowups.isoZero T.ideal hT.nonzeroOnComponents
  | succ n ih =>
    intro hn
    have hlt : n < s.toSequenceOfBlowups.length := hn
    refine nonzeroOnComponents_of_pow_mul_eq_comap hcart (s.toSequenceOfBlowups.transitionMapSucc n)
      (s.toSequenceOfBlowups.center n) (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt) T.mult
      (s.ideal n) (s.ideal (n + 1)) ?_ (ih (Nat.le_of_lt hlt))
    have he : Blowup.exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc n) (s.toSequenceOfBlowups.center n)
        = (s.toSequenceOfBlowups.center n).comap (s.toSequenceOfBlowups.transitionMapSucc n) := s.exceptionalDivisor_eq n
    rw [← he]
    exact s.ideal_succ n hlt

theorem centersContainNoComponent_ofMarkedSequence :
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent := by
  intro i hi W hW hsub
  have hlt : i < s.toSequenceOfBlowups.length := hi
  have hnz := nonzeroOnComponents_ideal_of_isAdmissible hcart hT s i (Nat.le_of_lt hlt)
  rw [nonzeroOnComponents_iff] at hnz
  refine hnz W hW (hsub.trans ?_)
  intro x hx
  have h2 : x ∈ orderAtLeastLocus (s.ideal i) T.mult := s.center_order i hlt hx
  exact (mem_orderAtLeastLocus_one_iff (s.ideal i) x).mp
    (orderAtLeastLocus_subset_of_le (s.ideal i) hT.one_le_mult h2)


end

end MarkedSequenceOfBlowups


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
section


section

theorem inStrictNormalCrossingPosition_comap_iso {k : Type u} [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) (L : List Y.IdealSheafData)
    (h : InStrictNormalCrossingPosition q L) :
    InStrictNormalCrossingPosition (e.hom ≫ q) (L.map (fun D => D.comap e.hom)) := by
  rw [inStrictNormalCrossingPosition_iff] at h ⊢
  refine ⟨?_, ?_⟩
  · intro D hD
    rw [List.mem_map] at hD
    obtain ⟨D', hD', rfl⟩ := hD
    exact PrincipalizationIsoTransport.isSmoothDivisor_comap_iso q e D' (h.1 D' hD')
  · intro x
    obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := h.2 (e.hom.base x)
    refine ⟨(TopologicalSpace.Opens.map e.hom.base).obj U, hxU, m,
      EtaleChart.ofIso q e c, a, ?_, ?_, ?_⟩
    · intro i hi j hj t hti htj
      exact hinj i (by simpa using hi) j (by simpa using hj) t hti htj
    · intro i hi ha
      have hi' : i < L.length := by simpa using hi
      simp only [List.getElem_map]
      rw [restrictIdeal_comap, hnone i hi' ha, Scheme.IdealSheafData.comap_top]
    · intro i hi t ht
      have hi' : i < L.length := by simpa using hi
      simp only [List.getElem_map]
      rw [restrictIdeal_comap, hsome i hi' t ht, EtaleChart.ofIso_coordIdeal]

namespace MarkedSequenceOfBlowups

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

section
variable (s : MarkedSequenceOfBlowups p I m E)

theorem projectionToSpec_zero :
    s.projectionToSpec 0 = s.toSequenceOfBlowups.isoZero.hom ≫ p := by
  rw [MarkedSequenceOfBlowups.projectionToSpec_eq, MarkedSequenceOfBlowups.projectionToBase_zero]

theorem projectionToSpec_succ (i : ℕ) :
    s.projectionToSpec (i + 1) = s.toSequenceOfBlowups.transitionMapSucc i ≫ s.projectionToSpec i := by
  have h : s.toSequenceOfBlowups.transitionMapSucc i ≫ s.toSequenceOfBlowups.projectionToBase i
      = s.toSequenceOfBlowups.projectionToBase (i + 1) := by
    rw [s.toSequenceOfBlowups.blowupMorphism_eq_transitionMap i]
    exact s.toSequenceOfBlowups.transitionMap_comp_projectionToBase (Nat.le_succ i)
  rw [MarkedSequenceOfBlowups.projectionToSpec_eq, MarkedSequenceOfBlowups.projectionToSpec_eq, ← h, Category.assoc]


end

theorem isNoetherian_schemeAt (_hcart : EffectiveCartierSupportContainsNoComponent.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length) :
    IsNoetherian (s.toSequenceOfBlowups.schemeAt i) := by
  induction i with
  | zero =>
      have : IsNoetherian T.scheme := hT.isNoetherian
      exact isNoetherian_of_iso s.toSequenceOfBlowups.isoZero.symm
  | succ n ih =>
      have hn : n < s.toSequenceOfBlowups.length := hi
      have : IsNoetherian (s.toSequenceOfBlowups.schemeAt n) := ih (le_of_lt hn)
      exact isNoetherian_of_isBlowupAlongIdealSheaf (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn)

end MarkedSequenceOfBlowups

private theorem smooth_and_inStrictNormalCrossingPosition_projectionToSpec_consolidated314 (hcart : EffectiveCartierSupportContainsNoComponent.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) :
    ∀ i : ℕ, i ≤ s.toSequenceOfBlowups.length →
      Smooth (s.projectionToSpec i) ∧ InStrictNormalCrossingPosition (s.projectionToSpec i) (s.boundary i) := by
  intro i
  induction i with
  | zero =>
      intro _
      have : Smooth T.structMap := hT.smooth
      refine ⟨?_, ?_⟩
      · rw [MarkedSequenceOfBlowups.projectionToSpec_zero]
        infer_instance
      · rw [MarkedSequenceOfBlowups.projectionToSpec_zero, s.boundary_zero]
        exact inStrictNormalCrossingPosition_comap_iso T.structMap s.toSequenceOfBlowups.isoZero T.boundary hT.snc
  | succ n ih =>
      intro hn
      have hn' : n < s.toSequenceOfBlowups.length := hn
      obtain ⟨hsm, hsnc⟩ := ih (le_of_lt hn')
      have : Smooth (s.projectionToSpec n) := hsm
      have : IsNoetherian (s.toSequenceOfBlowups.schemeAt (n + 1)) :=
        MarkedSequenceOfBlowups.isNoetherian_schemeAt hcart hT s (n + 1) hn
      have : TopologicalSpace.NoetherianSpace ↥(s.toSequenceOfBlowups.schemeAt (n + 1)) := inferInstance
      have hπ := s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn'
      have hZE : HasStrictNormalCrossingsWith (s.projectionToSpec n) (s.toSequenceOfBlowups.center n) (s.boundary n) := by
        rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
        exact s.center_snc n hn'
      refine ⟨?_, ?_⟩
      · rw [MarkedSequenceOfBlowups.projectionToSpec_succ]
        exact smooth_comp_of_isBlowupAlongIdealSheaf hZE hπ
      · rw [MarkedSequenceOfBlowups.projectionToSpec_succ, s.boundary_succ n hn']
        exact inStrictNormalCrossingPosition_strictTransform_append (s.projectionToSpec n) (s.toSequenceOfBlowups.transitionMapSucc n)
          (s.toSequenceOfBlowups.center n) (s.boundary n) hπ hsnc hZE

namespace MarkedSequenceOfBlowups

section
variable (hcart : EffectiveCartierSupportContainsNoComponent.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length)
include hcart hT hi

theorem smooth_projectionToSpec :
    Smooth (s.projectionToSpec i) :=
  (smooth_and_inStrictNormalCrossingPosition_projectionToSpec_consolidated314 hcart hT s i hi).1

theorem inStrictNormalCrossingPosition_projectionToSpec_boundary :
    InStrictNormalCrossingPosition (s.projectionToSpec i) (s.boundary i) :=
  (smooth_and_inStrictNormalCrossingPosition_projectionToSpec_consolidated314 hcart hT s i hi).2


end

end MarkedSequenceOfBlowups

def DimensionNonincreasingAlongBlowups : Prop :=
  ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
    krullDimSucc (s.toSequenceOfBlowups.schemeAt i) ≤ T.krullDimSucc

namespace MarkedIdealWithBoundary

def transformAt (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) : MarkedIdealWithBoundary.{u} where
  base := T.base
  instField := T.instField
  scheme := s.toSequenceOfBlowups.schemeAt i
  structMap := s.projectionToSpec i
  ideal := s.ideal i
  mult := T.mult
  boundary := s.boundary i

@[simp]
theorem transformAt_structureMorphism (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) :
    (T.transformAt s i).structMap = s.projectionToSpec i := rfl

@[simp]
theorem transformAt_boundary (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) :
    (T.transformAt s i).boundary = s.boundary i := rfl

@[simp]
theorem transformAt_dim (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) :
    (T.transformAt s i).krullDimSucc = EmbeddedResolution.krullDimSucc (s.toSequenceOfBlowups.schemeAt i) := rfl

theorem IsAdmissible.transformAt (hcart : EffectiveCartierSupportContainsNoComponent.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length) :
    (T.transformAt s i).IsAdmissible := by
  obtain ⟨hsm, hsnc⟩ := smooth_and_inStrictNormalCrossingPosition_projectionToSpec_consolidated314 hcart hT s i hi
  have : Smooth (s.projectionToSpec i) := hsm
  have : IsNoetherian (s.toSequenceOfBlowups.schemeAt i) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt hcart hT s i hi
  have : TopologicalSpace.NoetherianSpace ↥(s.toSequenceOfBlowups.schemeAt i) := inferInstance
  refine
    { charZero := hT.charZero
      locallyOfFiniteType := ?_
      nonzeroOnComponents := MarkedSequenceOfBlowups.nonzeroOnComponents_ideal_of_isAdmissible hcart hT s i hi
      one_le_mult := hT.one_le_mult
      quasiCompact := ?_
      smooth := hsm
      snc := hsnc }
  · show LocallyOfFiniteType (s.projectionToSpec i)
    infer_instance
  · show QuasiCompact (s.projectionToSpec i)
    exact ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩

theorem transformAt_dim_le (hdim : DimensionNonincreasingAlongBlowups.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length) :
    (T.transformAt s i).krullDimSucc ≤ T.krullDimSucc :=
  hdim T hT s i hi

end MarkedIdealWithBoundary


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.DimensionNonincreasing
section


section

private theorem krullDimSucc_eq_krullDimSucc_of_iso_consolidated334 {X Y : Scheme.{u}} (e : X ≅ Y) :
    krullDimSucc X = krullDimSucc Y := by
  have f : ↥X ≃ₜ ↥Y := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, topologicalKrullDim_eq_of_homeomorph f]

theorem dimensionNonincreasingAlongBlowups : DimensionNonincreasingAlongBlowups.{u} := by
  intro T hT s i
  induction i with
  | zero =>
      intro _
      exact le_of_eq (krullDimSucc_eq_krullDimSucc_of_iso_consolidated334 s.toSequenceOfBlowups.isoZero)
  | succ n ih =>
      intro hi
      have hlt : n < s.toSequenceOfBlowups.length := hi
      have hn : n ≤ s.toSequenceOfBlowups.length := Nat.le_of_lt hlt
      have hvalid := MarkedIdealWithBoundary.IsAdmissible.transformAt effectiveCartierSupportContainsNoComponent hT s n hn
      have hft : LocallyOfFiniteType (s.projectionToSpec n) :=
        hvalid.locallyOfFiniteType
      have hqc : QuasiCompact (s.projectionToSpec n) :=
        hvalid.quasiCompact
      have hsnc : HasStrictNormalCrossingsWith (s.projectionToSpec n) (s.toSequenceOfBlowups.center n) (s.boundary n) := by
        rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
        exact s.center_snc n hlt
      have hb : krullDimSucc (s.toSequenceOfBlowups.schemeAt (n + 1)) ≤ krullDimSucc (s.toSequenceOfBlowups.schemeAt n) :=
        krullDimSucc_le_of_blowup_strictNormalCrossings (s.projectionToSpec n) (s.toSequenceOfBlowups.transitionMapSucc n)
          (s.toSequenceOfBlowups.center n) (s.boundary n) hsnc
          (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt)
      exact le_trans hb (ih hn)

private theorem nontrivialPart_eq_filterNeTop_consolidated334 {X : Scheme.{u}} (E : List X.IdealSheafData) :
    MarkedIdealWithBoundary.nontrivialPart E = filterNeTop E := by
  unfold MarkedIdealWithBoundary.nontrivialPart filterNeTop
  apply List.filter_congr
  intro D _
  simp

namespace MarkedIdealWithBoundary

theorem validOfSameNontrivialBoundary : MarkedIdealWithBoundary.AdmissibleUnderBoundaryReplacement.{u} := by
  intro T E hV hEq
  have hsm : Smooth T.structMap := hV.smooth
  have h : filterNeTop T.boundary = filterNeTop E := by
    rw [← nontrivialPart_eq_filterNeTop_consolidated334, ← nontrivialPart_eq_filterNeTop_consolidated334]
    exact (MarkedIdealWithBoundary.sameNontrivialBoundary_iff T.boundary E).mp hEq
  exact ⟨hV.charZero, hV.locallyOfFiniteType, hV.nonzeroOnComponents, hV.one_le_mult,
    hV.quasiCompact, hV.smooth,
    inStrictNormalCrossingPosition_of_filterNeTop_eq T.structMap T.boundary E h hV.snc⟩

end MarkedIdealWithBoundary


end
end
end FunctorialResolution.EmbeddedResolution
end
