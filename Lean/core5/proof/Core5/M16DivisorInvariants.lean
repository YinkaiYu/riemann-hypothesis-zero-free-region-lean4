import Mathlib
import Core5.M15MarkedOrderReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicGeometry
universe u v
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.ControlledMonomialTransform
section


section

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {J : X.IdealSheafData} {μ : ℕ} {E : List X.IdealSheafData}

def MarkedSequenceOfBlowups.controlledNonMonomialTransform (t : MarkedSequenceOfBlowups p J μ E) (N : X.IdealSheafData) (c : ℕ) :
    ∀ i : ℕ, (t.schemeAt i).IdealSheafData
  | 0 => N.comap t.isoZero.hom
  | i + 1 =>
      residualByPow ((MarkedSequenceOfBlowups.controlledNonMonomialTransform t N c i).comap (t.transitionMapSucc i)) (t.exceptionalDivisor i) c

@[simp]
theorem MarkedSequenceOfBlowups.controlledNonMonomialTransform_zero (t : MarkedSequenceOfBlowups p J μ E) (N : X.IdealSheafData)
    (c : ℕ) : MarkedSequenceOfBlowups.controlledNonMonomialTransform t N c 0 = N.comap t.isoZero.hom :=
  rfl

@[simp]
theorem MarkedSequenceOfBlowups.controlledNonMonomialTransform_succ (t : MarkedSequenceOfBlowups p J μ E) (N : X.IdealSheafData)
    (c i : ℕ) :
    MarkedSequenceOfBlowups.controlledNonMonomialTransform t N c (i + 1) =
      residualByPow ((MarkedSequenceOfBlowups.controlledNonMonomialTransform t N c i).comap (t.transitionMapSucc i)) (t.exceptionalDivisor i) c :=
  rfl

def MarkedSequenceOfBlowups.controlledMonomialTransform (t : MarkedSequenceOfBlowups p J μ E) (M : X.IdealSheafData) (a c : ℕ) :
    ∀ i : ℕ, (t.schemeAt i).IdealSheafData
  | 0 => M.comap t.isoZero.hom
  | i + 1 =>
      residualByPow ((MarkedSequenceOfBlowups.controlledMonomialTransform t M a c i).comap (t.transitionMapSucc i) * t.exceptionalDivisor i ^ c)
        (t.exceptionalDivisor i) a

@[simp]
theorem MarkedSequenceOfBlowups.controlledMonomialTransform_zero (t : MarkedSequenceOfBlowups p J μ E) (M : X.IdealSheafData)
    (a c : ℕ) : MarkedSequenceOfBlowups.controlledMonomialTransform t M a c 0 = M.comap t.isoZero.hom :=
  rfl

@[simp]
theorem MarkedSequenceOfBlowups.controlledMonomialTransform_succ (t : MarkedSequenceOfBlowups p J μ E) (M : X.IdealSheafData)
    (a c i : ℕ) :
    MarkedSequenceOfBlowups.controlledMonomialTransform t M a c (i + 1) =
      residualByPow ((MarkedSequenceOfBlowups.controlledMonomialTransform t M a c i).comap (t.transitionMapSucc i) * t.exceptionalDivisor i ^ c)
        (t.exceptionalDivisor i) a :=
  rfl

end

section

theorem isAdmissible_withIdealAndMult_pow_sup_pow {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    {N : T.scheme.IdealSheafData} {s : ℕ} (hs : 1 ≤ s)
    (hord : ∀ x ∈ orderAtLeastLocus T.ideal T.mult, orderAt N x ≤ (s : ℕ∞)) :
    (T.withIdealAndMult (N ^ T.mult ⊔ T.ideal ^ s) (T.mult * s)).IsAdmissible ∧
      ∀ x : ↥T.scheme, orderAt (N ^ T.mult ⊔ T.ideal ^ s) x ≤ ((T.mult * s : ℕ) : ℕ∞) := by
  have hcz : CharZero T.base := hT.charZero
  have hsm : Smooth T.structMap := hT.smooth
  have hle : ∀ x : ↥T.scheme,
      orderAt (N ^ T.mult ⊔ T.ideal ^ s) x ≤ ((T.mult * s : ℕ) : ℕ∞) := fun x =>
    orderAt_pow_sup_pow_le T.base T.structMap N T.ideal T.mult s hord x
  have hsub : (↑(N ^ T.mult ⊔ T.ideal ^ s).support : Set ↥T.scheme) ⊆
      (↑T.ideal.support : Set ↥T.scheme) := by
    intro x hx
    by_contra hc
    have h0 : orderAt T.ideal x = 0 := (orderAt_eq_zero_iff_not_mem_support T.ideal x).2 hc
    have h1 : (1 : ℕ∞) ≤ orderAt (N ^ T.mult ⊔ T.ideal ^ s) x :=
      (one_le_orderAt_iff_mem_support (N ^ T.mult ⊔ T.ideal ^ s) x).2 hx
    rw [orderAt_pow_sup_pow T.base T.structMap N T.ideal T.mult s x] at h1
    have h2 : (1 : ℕ∞) ≤ (s : ℕ∞) * orderAt T.ideal x := le_trans h1 (min_le_right _ _)
    rw [h0, mul_zero] at h2
    simp at h2
  have hnz : NonzeroOnComponents (N ^ T.mult ⊔ T.ideal ^ s) := by
    rw [nonzeroOnComponents_iff]
    intro Z hZ hZsub
    exact (nonzeroOnComponents_iff T.ideal).1 hT.nonzeroOnComponents Z hZ (hZsub.trans hsub)
  have hmult : 1 ≤ T.mult * s := by
    have h := Nat.mul_le_mul hT.one_le_mult hs
    simpa using h
  exact ⟨{ charZero := hT.charZero
           locallyOfFiniteType := hT.locallyOfFiniteType
           nonzeroOnComponents := hnz
           one_le_mult := hmult
           quasiCompact := hT.quasiCompact
           smooth := hT.smooth
           snc := hT.snc }, hle⟩

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) {M N : T.scheme.IdealSheafData} (hsplit : IsMonomialSplitting T.boundary T.ideal M N) {s : ℕ} (hs : 1 ≤ s) (hord : ∀ x ∈ orderAtLeastLocus T.ideal T.mult, orderAt N x ≤ (s : ℕ∞)) (t : MarkedSequenceOfBlowups T.structMap (N ^ T.mult ⊔ T.ideal ^ s) (T.mult * s) T.boundary) (i : ℕ)
include hG hT hsplit hs hord

theorem isMonomialSplitting_controlledTransform_of_le_length (hi : i ≤ t.length) :
    t.ideal i =
        MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i ^ T.mult ⊔
          MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i ^ s ∧
      IsMonomialSplitting (t.boundary i) (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i)
        (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s i) (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) ∧
      ∀ x ∈ orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) T.mult,
        orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) x ≤ (s : ℕ∞) := by
  have := hT.charZero
  have := hT.smooth
  have hECNC : EffectiveCartierSupportContainsNoComponent.{u} := effectiveCartierSupportContainsNoComponent
  have hgeom : OrderAtComapOffExceptionalLocus.{u} :=
    orderAtComapOffExceptionalLocus_of_monomialGeometryHypotheses hG.monomialInputs
  have hm : 1 ≤ T.mult := hT.one_le_mult
  have hT' := (isAdmissible_withIdealAndMult_pow_sup_pow hT hs hord).1
  have key : ∀ j : ℕ, j ≤ t.length →
      (t.ideal j = MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s j ^ T.mult ⊔
          MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult j ^ s ∧
        IsMonomialSplitting (t.boundary j) (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult j)
          (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s j) (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s j) ∧
        ∀ x ∈ orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult j) T.mult,
          orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s j) x ≤ (s : ℕ∞)) := by
    intro j
    induction j with
    | zero =>
        intro _
        refine ⟨?_, ?_, ?_⟩
        · rw [t.ideal_zero, MarkedSequenceOfBlowups.controlledNonMonomialTransform_zero, MarkedSequenceOfBlowups.controlledTransform_zero,
            Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.comap_pow,
            Scheme.IdealSheafData.comap_pow]
        · rw [t.boundary_zero, MarkedSequenceOfBlowups.controlledTransform_zero, MarkedSequenceOfBlowups.controlledMonomialTransform_zero,
            MarkedSequenceOfBlowups.controlledNonMonomialTransform_zero]
          exact hsplit.comap_iso t.isoZero
        · intro x hx
          have h1 : (T.mult : ℕ∞) ≤ orderAt (T.ideal.comap t.isoZero.hom) x :=
            (mem_orderAtLeastLocus_iff _ _ _).1 hx
          rw [orderAt_comap_of_isIso] at h1
          have h2 := hord _ ((mem_orderAtLeastLocus_iff _ _ _).2 h1)
          show orderAt (N.comap t.isoZero.hom) x ≤ (s : ℕ∞)
          rw [orderAt_comap_of_isIso]
          exact h2
    | succ n ih =>
        intro hn
        have hn' : n < t.length := hn
        obtain ⟨ih1, ih2, ih3⟩ := ih (le_of_lt hn')
        have hbl : Blowup.IsBlowupAlongIdealSheaf (t.transitionMapSucc n) (t.center n) := t.isBlowupAlongIdealSheaf_blowupMorphism n hn'
        have hexc : Blowup.exceptionalIdeal (t.transitionMapSucc n) (t.center n) = t.exceptionalDivisor n := by
          rw [MarkedSequenceOfBlowups.exceptionalDivisor_eq, Blowup.exceptionalIdeal_eq_comap]
        have hFcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (t.exceptionalDivisor n) := by
          rw [← hexc]
          exact isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hbl
        have hTn := MarkedIdealWithBoundary.IsAdmissible.transformAt hECNC hT' t n (le_of_lt hn')
        have : Smooth (MarkedSequenceOfBlowups.projectionToSpec t n) :=
          MarkedSequenceOfBlowups.smooth_projectionToSpec hECNC hT' t n (le_of_lt hn')
        have : Smooth (MarkedSequenceOfBlowups.projectionToSpec t (n + 1)) :=
          MarkedSequenceOfBlowups.smooth_projectionToSpec hECNC hT' t (n + 1) hn
        have : IsNoetherian (t.schemeAt (n + 1)) :=
          MarkedSequenceOfBlowups.isNoetherian_schemeAt hECNC hT' t (n + 1) hn
        have hsmn : Smooth
            ((t.center n).subschemeι ≫ MarkedSequenceOfBlowups.projectionToSpec t n) := by
          rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
          exact t.center_smooth n hn'
        have hsncn : HasStrictNormalCrossingsWith (MarkedSequenceOfBlowups.projectionToSpec t n) (t.center n) (t.boundary n) := by
          rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
          exact t.center_snc n hn'
        have hcos : orderAtLeastLocus (t.ideal n) (T.mult * s)
            = orderAtLeastLocus (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n) s ∩
              orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n) T.mult := by
          rw [ih1]
          exact orderAtLeastLocus_pow_sup_pow T.base (MarkedSequenceOfBlowups.projectionToSpec t n) _ _ hm hs
        have hZord : ∀ x ∈ (t.center n).support,
            orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n) x = (s : ℕ∞) := by
          intro x hx
          have hx1 := t.center_order n hn' hx
          rw [hcos] at hx1
          exact le_antisymm (ih3 x hx1.2) ((mem_orderAtLeastLocus_iff _ _ _).1 hx1.1)
        have hZP : (↑(t.center n).support : Set ↥(t.schemeAt n))
            ⊆ orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n) T.mult := by
          intro x hx
          have hx1 := t.center_order n hn' hx
          rw [hcos] at hx1
          exact hx1.2
        have hPle : MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n ≤ t.center n ^ T.mult :=
          le_pow_of_hasStrictNormalCrossingsWith (MarkedSequenceOfBlowups.projectionToSpec t n) (t.center n) _ (t.boundary n)
            hsncn T.mult hZP
        have hAle : MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n ≤ t.center n ^ s := by
          refine le_pow_of_hasStrictNormalCrossingsWith (MarkedSequenceOfBlowups.projectionToSpec t n) (t.center n) _
            (t.boundary n) hsncn s ?_
          intro x hx
          exact (mem_orderAtLeastLocus_iff _ _ _).2 (le_of_eq (hZord x hx).symm)
        have hPdiv : ∃ B : (t.schemeAt (n + 1)).IdealSheafData, t.exceptionalDivisor n ^ T.mult * B
            = (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n).comap (t.transitionMapSucc n) := by
          refine (hFcart.pow T.mult).exists_mul_eq ?_
          rw [← hexc]
          exact comap_le_exceptionalIdeal_pow (t.transitionMapSucc n) hPle
        have hAdiv : ∃ B : (t.schemeAt (n + 1)).IdealSheafData, t.exceptionalDivisor n ^ s * B
            = (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n).comap (t.transitionMapSucc n) := by
          refine (hFcart.pow s).exists_mul_eq ?_
          rw [← hexc]
          exact comap_le_exceptionalIdeal_pow (t.transitionMapSucc n) hAle
        have hPtw : t.exceptionalDivisor n ^ T.mult *
            MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult (n + 1)
            = (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n).comap (t.transitionMapSucc n) := by
          rw [MarkedSequenceOfBlowups.controlledTransform_succ]
          exact pow_mul_residualByPow _ _ _ hPdiv
        have hAtw : t.exceptionalDivisor n ^ s * MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s (n + 1)
            = (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n).comap (t.transitionMapSucc n) := by
          rw [MarkedSequenceOfBlowups.controlledNonMonomialTransform_succ]
          exact pow_mul_residualByPow _ _ _ hAdiv
        have hPtw' : Blowup.exceptionalIdeal (t.transitionMapSucc n) (t.center n) ^ T.mult *
            MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult (n + 1)
            = (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n).comap (t.transitionMapSucc n) := by
          rw [hexc]
          exact hPtw
        have hAtw' : Blowup.exceptionalIdeal (t.transitionMapSucc n) (t.center n) ^ s *
            MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s (n + 1)
            = (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n).comap (t.transitionMapSucc n) := by
          rw [hexc]
          exact hAtw
        have hCdiv : ∃ Cc : (t.schemeAt (n + 1)).IdealSheafData,
            Blowup.exceptionalIdeal (t.transitionMapSucc n) (t.center n) ^ T.mult * Cc
              = (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s n).comap (t.transitionMapSucc n) *
                Blowup.exceptionalIdeal (t.transitionMapSucc n) (t.center n) ^ s :=
          exists_exceptionalIdeal_pow_mul_eq_comap_mul_pow hG _ hTn (t.center n) hsmn hsncn _
            (t.transitionMapSucc n) hbl _ _ _ T.mult s ih2 hZP hZord _ hPtw' _ hAtw'
        have hCtw : t.exceptionalDivisor n ^ T.mult * MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s (n + 1)
            = (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s n).comap (t.transitionMapSucc n) *
              t.exceptionalDivisor n ^ s := by
          rw [MarkedSequenceOfBlowups.controlledMonomialTransform_succ]
          refine pow_mul_residualByPow _ _ _ ?_
          obtain ⟨Cc, hCc⟩ := hCdiv
          refine ⟨Cc, ?_⟩
          rw [← hexc]
          exact hCc
        have hCtw' : Blowup.exceptionalIdeal (t.transitionMapSucc n) (t.center n) ^ T.mult *
            MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s (n + 1)
            = (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s n).comap (t.transitionMapSucc n) *
              Blowup.exceptionalIdeal (t.transitionMapSucc n) (t.center n) ^ s := by
          rw [hexc]
          exact hCtw
        refine ⟨?_, ?_, ?_⟩
        · have hidsucc : t.exceptionalDivisor n ^ (T.mult * s) * t.ideal (n + 1)
              = (t.ideal n).comap (t.transitionMapSucc n) := by
            rw [← hexc]
            exact t.ideal_succ n hn'
          have hcancel : t.exceptionalDivisor n ^ (T.mult * s) * t.ideal (n + 1)
              = t.exceptionalDivisor n ^ (T.mult * s) *
                (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s (n + 1) ^ T.mult ⊔
                  MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult (n + 1) ^ s) := by
            rw [hidsucc, ih1, Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.comap_pow,
              Scheme.IdealSheafData.comap_pow, ← hAtw, ← hPtw, mul_pow, mul_pow, ← pow_mul,
              ← pow_mul, Scheme.IdealSheafData.mul_inf, Nat.mul_comm s T.mult]
          exact (hFcart.pow (T.mult * s)).eq_of_mul_eq_mul hcancel
        · rw [t.boundary_succ n hn']
          exact isMonomialSplitting_of_isBlowupAlongIdealSheaf hG _ hTn (t.center n) hsmn hsncn _
            (t.transitionMapSucc n) hbl _ _ _ T.mult s ih2 hZP hZord _ hPtw' _ hAtw' _ hCtw'
        · intro x hx
          by_cases hxE : x ∈ (Blowup.exceptionalIdeal (t.transitionMapSucc n) (t.center n)).support
          · exact hG.controlledTransform_orderAt_le _ hTn (t.center n) hsmn hsncn _
              (t.transitionMapSucc n) hbl _ s hZord _ hAtw' x hxE
          · have hcs : orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult (n + 1)) T.mult
                ⊆ ⇑(t.transitionMapSucc n) ⁻¹'
                  orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n) T.mult :=
              orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf hgeom _ hTn (t.center n) _ (t.transitionMapSucc n)
                hbl _ T.mult hZP _ hPtw' T.mult le_rfl
            have hxP : (t.transitionMapSucc n) x ∈
                orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n) T.mult := hcs hx
            have hord2 := ih3 _ hxP
            have hoff := hG.monomialInputs.orderAt_comap_off_exceptional _ hTn _
              (t.transitionMapSucc n) (t.center n) hbl x hxE (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n)
            have hoff' : orderAt ((MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n).comap (t.transitionMapSucc n)) x
                = orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n) ((t.transitionMapSucc n) x) := hoff
            have hx0 : orderAt (t.exceptionalDivisor n) x = 0 := by
              rw [← hexc]
              exact (orderAt_eq_zero_iff_not_mem_support _ _).2 hxE
            have hsplit2 :
                orderAt ((MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n).comap (t.transitionMapSucc n)) x
                  = orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s (n + 1)) x := by
              rw [← hAtw, orderAt_mul T.base (MarkedSequenceOfBlowups.projectionToSpec t (n + 1)),
                orderAt_pow T.base (MarkedSequenceOfBlowups.projectionToSpec t (n + 1)), hx0, mul_zero, zero_add]
            rw [← hsplit2, hoff']
            exact hord2
  exact key i hi

theorem exists_exceptionalDivisor_pow_mul_eq_comap_of_lt_length (hi : i < t.length) :
    (∀ x ∈ (t.center i).support,
        orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) x = (s : ℕ∞)) ∧
      (↑(t.center i).support : Set ↥(t.schemeAt i)) ⊆
        orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) T.mult ∧
      (∃ A : (t.schemeAt (i + 1)).IdealSheafData,
        t.exceptionalDivisor i ^ T.mult * A =
          (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i).comap (t.transitionMapSucc i)) ∧
      (∃ B : (t.schemeAt (i + 1)).IdealSheafData,
        t.exceptionalDivisor i ^ s * B =
          (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i).comap (t.transitionMapSucc i)) ∧
      (∃ C : (t.schemeAt (i + 1)).IdealSheafData,
        t.exceptionalDivisor i ^ T.mult * C =
          (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s i).comap (t.transitionMapSucc i) *
            t.exceptionalDivisor i ^ s) := by
  classical
  have hECNC : EffectiveCartierSupportContainsNoComponent.{u} := effectiveCartierSupportContainsNoComponent
  have hadm : (T.withIdealAndMult (N ^ T.mult ⊔ T.ideal ^ s) (T.mult * s)).IsAdmissible :=
    (isAdmissible_withIdealAndMult_pow_sup_pow hT hs hord).1
  have hlevel : ((T.withIdealAndMult (N ^ T.mult ⊔ T.ideal ^ s) (T.mult * s)).transformAt t i).IsAdmissible :=
    MarkedIdealWithBoundary.IsAdmissible.transformAt hECNC hadm t i (le_of_lt hi)
  have hchar : CharZero T.base := hT.charZero
  have hsmooth : Smooth (t.projectionToSpec i) :=
    MarkedSequenceOfBlowups.smooth_projectionToSpec hECNC hadm t i (le_of_lt hi)
  have hnoeth : IsNoetherian (t.schemeAt (i + 1)) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt hECNC hadm t (i + 1) hi
  obtain ⟨hideal_i, hsplit_i, hord_i⟩ :=
    isMonomialSplitting_controlledTransform_of_le_length hG hT hsplit hs hord t i (le_of_lt hi)
  have hexc : t.exceptionalDivisor i = Blowup.exceptionalIdeal (t.transitionMapSucc i) (t.center i) := by
    rw [MarkedSequenceOfBlowups.exceptionalDivisor_eq, Blowup.exceptionalIdeal_eq_comap]
  have hbl : Blowup.IsBlowupAlongIdealSheaf (t.transitionMapSucc i) (t.center i) := t.isBlowupAlongIdealSheaf_blowupMorphism i hi
  have hsncc : HasStrictNormalCrossingsWith (t.projectionToSpec i) (t.center i) (t.boundary i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact t.center_snc i hi
  have hsm : Smooth ((t.center i).subschemeι ≫ t.projectionToSpec i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact t.center_smooth i hi
  have key : ∀ x ∈ (t.center i).support,
      orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) x = (s : ℕ∞) ∧
        (T.mult : ℕ∞) ≤ orderAt (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) x := by
    intro x hx
    have hx0 : ((T.mult * s : ℕ) : ℕ∞) ≤ orderAt (t.ideal i) x :=
      (mem_orderAtLeastLocus_iff _ _ _).1 (t.center_order i hi hx)
    rw [hideal_i, orderAt_pow_sup_pow T.base (t.projectionToSpec i) _ _ _ _ x, le_min_iff,
      Nat.cast_mul] at hx0
    obtain ⟨h1, h2⟩ := hx0
    have h1' : (s : ℕ∞) ≤ orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) x :=
      (natCast_mul_le_mul_iff hT.one_le_mult s _).1 h1
    have h2' : (T.mult : ℕ∞) ≤ orderAt (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) x := by
      refine (natCast_mul_le_mul_iff hs T.mult _).1 ?_
      rwa [mul_comm ((s : ℕ∞)) ((T.mult : ℕ∞))]
    exact ⟨le_antisymm (hord_i x ((mem_orderAtLeastLocus_iff _ _ _).2 h2')) h1', h2'⟩
  have hZP : (↑(t.center i).support : Set ↥(t.schemeAt i)) ⊆
      orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) T.mult := by
    intro x hx
    exact (mem_orderAtLeastLocus_iff _ _ _).2 (key x hx).2
  have hZord : (↑(t.center i).support : Set ↥(t.schemeAt i)) ⊆
      orderAtLeastLocus (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) s := by
    intro x hx
    exact (mem_orderAtLeastLocus_iff _ _ _).2 (le_of_eq (key x hx).1.symm)
  have hPle : MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i ≤ t.center i ^ T.mult :=
    le_pow_of_hasStrictNormalCrossingsWith (t.projectionToSpec i) (t.center i)
      (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) (t.boundary i) hsncc T.mult hZP
  have hAle : MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i ≤ t.center i ^ s :=
    le_pow_of_hasStrictNormalCrossingsWith (t.projectionToSpec i) (t.center i)
      (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) (t.boundary i) hsncc s hZord
  obtain ⟨B', hB', -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (t.transitionMapSucc i) (t.center i)
    (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) T.mult hbl hPle
  obtain ⟨A', hA', -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (t.transitionMapSucc i) (t.center i)
    (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) s hbl hAle
  obtain ⟨C', hC'⟩ := exists_exceptionalIdeal_pow_mul_eq_comap_mul_pow hG _ hlevel
    (t.center i) hsm hsncc (t.schemeAt (i + 1)) (t.transitionMapSucc i) hbl
    (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i)
    (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s i)
    (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) T.mult s hsplit_i hZP
    (fun x hx => (key x hx).1) B' hB' A' hA'
  refine ⟨fun x hx => (key x hx).1, hZP, ⟨B', ?_⟩, ⟨A', ?_⟩, ⟨C', ?_⟩⟩
  · rw [hexc]
    exact hB'
  · rw [hexc]
    exact hA'
  · rw [hexc]
    exact hC'


end

section
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {J : X.IdealSheafData} {μ : ℕ} {E : List X.IdealSheafData} (s : MarkedSequenceOfBlowups p J μ E) (I : X.IdealSheafData) (m i : ℕ)

private theorem controlledTransform_eq_ofMarkedSequence_controlledTransform_consolidated436 :
    MarkedSequenceOfBlowups.controlledTransform s I m i
      = ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData).controlledTransform I m i := by
  induction i with
  | zero =>
      exact (BlowupSequenceData.controlledTransform_zero ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData) I m).symm
  | succ n ih =>
      have h2 := BlowupSequenceData.controlledTransform_succ ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData) I m n
      refine Eq.trans ?_ h2.symm
      exact congrArg
        (fun Jj : (s.schemeAt n).IdealSheafData =>
          residualByPow (Jj.comap (s.transitionMapSucc n)) (s.exceptionalDivisor n) m) ih

private theorem comap_controlledTransform_eq_comap_ofMarkedSequence_consolidated436 :
    (MarkedSequenceOfBlowups.controlledTransform s I m i).comap (s.transitionMapSucc i)
      = (((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData).controlledTransform I m i).comap
          (((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData).map i) :=
  congrArg (fun Jj : (s.schemeAt i).IdealSheafData => Jj.comap (s.transitionMapSucc i))
    (controlledTransform_eq_ofMarkedSequence_controlledTransform_consolidated436 s I m i)


end

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) {M N : T.scheme.IdealSheafData} (hsplit : IsMonomialSplitting T.boundary T.ideal M N) {s : ℕ} (hs : 1 ≤ s) (hord : ∀ x ∈ orderAtLeastLocus T.ideal T.mult, orderAt N x ≤ (s : ℕ∞)) (t : MarkedSequenceOfBlowups T.structMap (N ^ T.mult ⊔ T.ideal ^ s) (T.mult * s) T.boundary)
include hG hT hsplit hs hord

theorem isMarked_ofMarkedSequence_of_isMonomialSplitting :
    (MarkedBlowupSequenceData.ofMarkedSequence t).toBlowupSequenceData.IsMarked T.structMap T.ideal T.mult
      T.boundary := by
  have hself := (MarkedBlowupSequenceData.ofMarkedSequence t).isMarked_toBlowupSequenceData
  refine ⟨?_, ?_, hself.center_smooth, hself.center_snc⟩
  · intro i hi
    have hi' : i < t.length := hi
    obtain ⟨A, hA⟩ := (exists_exceptionalDivisor_pow_mul_eq_comap_of_lt_length hG hT hsplit hs hord t i hi').2.2.1
    exact ⟨A, hA.trans (comap_controlledTransform_eq_comap_ofMarkedSequence_consolidated436 t T.ideal T.mult i)⟩
  · intro i hi
    have hi' : i < t.length := hi
    have hsub := (exists_exceptionalDivisor_pow_mul_eq_comap_of_lt_length hG hT hsplit hs hord t i hi').2.1
    intro x hx
    have h1 : (T.mult : ℕ∞) ≤ orderAt (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) x :=
      (mem_orderAtLeastLocus_iff _ _ _).1 (hsub hx)
    have he : orderAt (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) x
        = orderAt (((MarkedBlowupSequenceData.ofMarkedSequence t).toBlowupSequenceData).controlledTransform T.ideal T.mult i) x :=
      congrArg (fun Jj : (t.schemeAt i).IdealSheafData => orderAt Jj x)
        (controlledTransform_eq_ofMarkedSequence_controlledTransform_consolidated436 t T.ideal T.mult i)
    exact (mem_orderAtLeastLocus_iff _ _ _).2 (he ▸ h1)

theorem orderAt_controlledNonMonomialTransform_length_lt (hempty : orderAtLeastLocus (t.ideal t.length) (T.mult * s) = ∅) :
    ∀ x ∈ orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult t.length) T.mult,
      orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s t.length) x < (s : ℕ∞) := by
  classical
  have hECNC : EffectiveCartierSupportContainsNoComponent.{u} := effectiveCartierSupportContainsNoComponent
  have hadm : (T.withIdealAndMult (N ^ T.mult ⊔ T.ideal ^ s) (T.mult * s)).IsAdmissible :=
    (isAdmissible_withIdealAndMult_pow_sup_pow hT hs hord).1
  have hchar : CharZero T.base := hT.charZero
  have hsmooth : Smooth (t.projectionToSpec t.length) :=
    MarkedSequenceOfBlowups.smooth_projectionToSpec hECNC hadm t t.length le_rfl
  obtain ⟨hideal, -, -⟩ := isMonomialSplitting_controlledTransform_of_le_length hG hT hsplit hs hord t t.length le_rfl
  rw [hideal] at hempty
  exact (orderAtLeastLocus_pow_sup_pow_eq_empty_iff T.base (t.projectionToSpec t.length)
      (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s t.length)
      (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult t.length) hT.one_le_mult hs).1 hempty


end

end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.NonMonomialOrderReduction
section


section

section

theorem list_map_comap_id (B : Scheme.{u}) (E : List B.IdealSheafData) :
    List.map (fun D : B.IdealSheafData => D.comap (𝟙 B)) E = E := by
  have h : ∀ D : B.IdealSheafData, D.comap (𝟙 B) = D := fun D => by simp
  induction E with
  | nil => rfl
  | cons D E ih => rw [List.map_cons, h D, ih]

theorem orderAtLeastLocus_comap_eqToHom {A B : Scheme.{u}} (h : A = B) (J : B.IdealSheafData) (c : ℕ) :
    orderAtLeastLocus (J.comap (eqToHom h)) c = (eqToHom h).base ⁻¹' orderAtLeastLocus J c := by
  subst h
  simp

section
variable {k : Type u} [Field k]

theorem isAdmissible_congr {A : Scheme.{u}}
    {p q : A ⟶ Spec (CommRingCat.of k)} {I J : A.IdealSheafData} {m n : ℕ}
    {E F : List A.IdealSheafData} (hp : p = q) (hI : I = J) (hm : m = n) (hE : E = F)
    (h : (MarkedIdealWithBoundary.mk k A p I m E).IsAdmissible) :
    (MarkedIdealWithBoundary.mk k A q J n F).IsAdmissible := by
  subst hp
  subst hI
  subst hm
  subst hE
  exact h

theorem ofMarkedSequence_boundary_eq_of_le {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) (hi : i ≤ s.length) :
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.boundaryFrom E i = s.boundary i := by
  revert hi
  induction i with
  | zero =>
      intro _
      rw [BlowupSequenceData.boundary_zero]
      exact s.boundary_zero.symm
  | succ i ih =>
      intro hi
      have hlt : i < s.length := hi
      rw [BlowupSequenceData.boundary_succ, ih (Nat.le_of_lt hlt)]
      exact (s.boundary_succ i hlt).symm


end

end

section

abbrev principalizationOfDimLe (T : MarkedIdealWithBoundary.{u}) (A : PrincipalizationAssignment.{u}) :
    (S : MarkedIdealWithBoundary.{u}) → S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups :=
  fun S _ => A S

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private theorem quasiCompact_of_isNoetherian_consolidated437 (h : IsNoetherian X) : QuasiCompact f := by
  have := h
  infer_instance

private theorem locallyOfFiniteType_of_smooth_consolidated437 (h : Smooth f) : LocallyOfFiniteType f := by
  have := h
  infer_instance


end

theorem isAdmissible_tripleAtLength (_hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := by
  have hlen : s.length ≤ s.toMarkedSequenceOfBlowups.length :=
    le_of_eq (MarkedBlowupSequenceData.toMarkedSequence_length s).symm
  have hsm : Smooth (s.proj s.length ≫ T.structMap) := by
    have h := MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hT s.toMarkedSequenceOfBlowups
      s.length hlen
    rwa [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec] at h
  have hnz : NonzeroOnComponents (s.ideal s.length) := by
    have h := MarkedSequenceOfBlowups.nonzeroOnComponents_ideal_of_isAdmissible effectiveCartierSupportContainsNoComponent hT
      s.toMarkedSequenceOfBlowups s.length hlen
    rwa [MarkedBlowupSequenceData.toMarkedSequence_ideal] at h
  have hsnc : InStrictNormalCrossingPosition (s.proj s.length ≫ T.structMap) (s.boundary s.length) := by
    have h := MarkedSequenceOfBlowups.inStrictNormalCrossingPosition_projectionToSpec_boundary effectiveCartierSupportContainsNoComponent hT s.toMarkedSequenceOfBlowups
      s.length hlen
    rwa [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec, MarkedBlowupSequenceData.toMarkedSequence_boundary] at h
  have hno : IsNoetherian (s.obj s.length) := by
    have h := MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hT s.toMarkedSequenceOfBlowups
      s.length hlen
    rwa [MarkedBlowupSequenceData.toMarkedSequence_schemeAt] at h
  exact ⟨hT.charZero, locallyOfFiniteType_of_smooth_consolidated437 _ hsm, hnz, hT.one_le_mult,
    quasiCompact_of_isNoetherian_consolidated437 _ hno, hsm, hsnc⟩

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
include hG hT

theorem tripleAtLength_dim_le (J : (s.obj s.length).IdealSheafData) (μ : ℕ) :
    (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc := by
  rw [tripleAtLength_dim]
  have hlen : s.length ≤ s.toMarkedSequenceOfBlowups.length :=
    le_of_eq (MarkedBlowupSequenceData.toMarkedSequence_length s).symm
  have h := hG.monomialInputs.level_schemeDim_le T hT s.toMarkedSequenceOfBlowups s.length hlen
  rwa [MarkedBlowupSequenceData.toMarkedSequence_schemeAt] at h

theorem isMonomialSplitting_lastNonMonomialPart :
    IsMonomialSplitting (s.boundary s.length) (s.ideal s.length)
      (monomialPart (s.boundary s.length) (s.ideal s.length)) (lastNonMonomialPart T s) := by
  have h := hG.isMonomialSplitting_monomialPart_nonMonomialPart (tripleAtLength T s (s.ideal s.length) T.mult)
    (isAdmissible_tripleAtLength hG hT s)
  exact h

theorem exists_orderAt_lastNonMonomialPart_le :
    ∃ B : ℕ, ∀ x : ↥(s.obj s.length), orderAt (lastNonMonomialPart T s) x ≤ (B : ℕ∞) := by
  have hv := isAdmissible_tripleAtLength hG hT s
  have hnz : NonzeroOnComponents (s.ideal s.length) := hv.nonzeroOnComponents
  have hsplit := isMonomialSplitting_lastNonMonomialPart hG hT s
  have hnz' : NonzeroOnComponents (lastNonMonomialPart T s) :=
    hsplit.nonzeroOnComponents_nonMonomial hnz
  exact hG.monomialInputs.orderAt_bounded (tripleAtLength T s (s.ideal s.length) T.mult) hv
    (lastNonMonomialPart T s) hnz'

theorem orderAt_lastNonMonomialPart_le_maxOrderNonMonomial (x : ↥(s.obj s.length)) :
    orderAt (lastNonMonomialPart T s) x ≤ ((maxOrderNonMonomial T s : ℕ) : ℕ∞) := by
  obtain ⟨B, hB⟩ := exists_orderAt_lastNonMonomialPart_le hG hT s
  have h : maxOrderNonMonomial T s = maxOrder (lastNonMonomialPart T s) := rfl
  rw [h]
  exact orderAt_le_maxOrder (lastNonMonomialPart T s) hB x


end

abbrev nonMonomialTriple (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) : MarkedIdealWithBoundary.{u} :=
  tripleAtLength T s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)

theorem isAdmissible_nonMonomialTriple (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (hcont : NonMonomialOrderReductionContinues T s) :
    (nonMonomialTriple T s).IsAdmissible := by
  have hbase : (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := isAdmissible_tripleAtLength hG hT s
  have hsplit : IsMonomialSplitting (s.boundary s.length) (s.ideal s.length)
      (monomialPart (s.boundary s.length) (s.ideal s.length)) (lastNonMonomialPart T s) :=
    isMonomialSplitting_lastNonMonomialPart hG hT s
  have hnz0 : NonzeroOnComponents (s.ideal s.length) := hbase.nonzeroOnComponents
  have hnz : NonzeroOnComponents (lastNonMonomialPart T s) :=
    hsplit.nonzeroOnComponents_nonMonomial hnz0
  have hmult : 1 ≤ maxOrderNonMonomial T s :=
    le_trans hT.one_le_mult ((nonMonomialOrderReductionContinues_iff T s).1 hcont).1
  exact ⟨hbase.charZero, hbase.locallyOfFiniteType, hnz, hmult, hbase.quasiCompact, hbase.smooth,
    hbase.snc⟩

end

section

theorem isMarked_seqAtEnd_lastNonMonomialPart (hG : PrincipalizationGeometryHypotheses.{u}) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : NonMonomialOrderReductionContinues T s) :
    (MarkedBlowupSequenceData.ofMarkedSequence
          (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
            (tripleAtLength_dim_le hG hT s _ _))).toBlowupSequenceData.IsMarked
      (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length) := by
  have hμ : T.mult ≤ maxOrderNonMonomial T s := ((nonMonomialOrderReductionContinues_iff T s).1 hcont).1
  have hadmLast : (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := isAdmissible_tripleAtLength hG hT s
  have hadmNonMonomial : (nonMonomialTriple T s).IsAdmissible := isAdmissible_nonMonomialTriple hG hT s hcont
  have hsplit : IsMonomialSplitting (s.boundary s.length) (s.ideal s.length)
      (monomialPart (s.boundary s.length) (s.ideal s.length)) (lastNonMonomialPart T s) :=
    isMonomialSplitting_lastNonMonomialPart hG hT s
  have hdim' : (nonMonomialTriple T s).krullDimSucc ≤ n :=
    le_trans (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)) hdim
  have hob : (nonMonomialTriple T s).IsOrderBoundedByMult :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff (nonMonomialTriple T s)).2 fun x =>
      orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
  have hord := hspec.order_le (nonMonomialTriple T s) hadmNonMonomial hdim' hob
  exact isMarked_sequenceData_of_orderAt_le hG hadmLast hsplit hμ
    (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
      (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))) hord

def continuationByNonMonomialPart (hG : PrincipalizationGeometryHypotheses.{u}) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : NonMonomialOrderReductionContinues T s) :
    MarkedBlowupSequenceData (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult
      (s.boundary s.length) :=
  BlowupSequenceData.toMarkedBlowupSequenceData
    (MarkedBlowupSequenceData.ofMarkedSequence
        (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
          (tripleAtLength_dim_le hG hT s _ _))).toBlowupSequenceData
    (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length)
    (isMarked_seqAtEnd_lastNonMonomialPart hG hspec hT hdim s hcont)

@[simp]
theorem continuationByNonMonomialPart_length (hG : PrincipalizationGeometryHypotheses.{u}) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : NonMonomialOrderReductionContinues T s) :
    (continuationByNonMonomialPart hG hspec hT hdim s hcont).length =
      (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
        (tripleAtLength_dim_le hG hT s _ _)).length := by
  exact MarkedBlowupSequenceData.ofMarkedSequence_length
    (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
      (tripleAtLength_dim_le hG hT s _ _))

private theorem orderAtLeastLocus_comap_iso_nonempty_consolidated437 {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of k))
    (hp : Smooth p) (e : Y ≅ X) (N : X.IdealSheafData) (c : ℕ)
    (hne : (orderAtLeastLocus N c).Nonempty) :
    (orderAtLeastLocus (N.comap e.hom) c).Nonempty := by
  have := hp
  have : Smooth e.inv := inferInstance
  obtain ⟨x, hx⟩ := hne
  have hcomp : (N.comap e.hom).comap e.inv = N := by
    rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id]
    simp
  have hsub := image_orderAtLeastLocus_comap_subset k p e.inv (N.comap e.hom) c
  rw [hcomp] at hsub
  exact ⟨_, hsub (Set.mem_image_of_mem _ hx)⟩

section
variable (hG : PrincipalizationGeometryHypotheses.{u})

theorem seqAtEnd_lastNonMonomialPart_length_pos {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : NonMonomialOrderReductionContinues T s) :
    0 < (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
      (tripleAtLength_dim_le hG hT s _ _)).length := by
  have hadmNonMonomial : (nonMonomialTriple T s).IsAdmissible := isAdmissible_nonMonomialTriple hG hT s hcont
  have hdim' : (nonMonomialTriple T s).krullDimSucc ≤ n :=
    le_trans (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)) hdim
  have hob : (nonMonomialTriple T s).IsOrderBoundedByMult :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff (nonMonomialTriple T s)).2 fun x =>
      orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
  have key : 0 < (A (nonMonomialTriple T s)).length := by
    by_contra hzero
    have hlen : (A (nonMonomialTriple T s)).length = 0 := by omega
    have hres := hspec.resolves (nonMonomialTriple T s) hadmNonMonomial hdim' hob
    rw [MarkedSequenceOfBlowups.isResolution_iff] at hres
    rw [MarkedSequenceOfBlowups.lastIdeal_eq] at hres
    rw [hlen] at hres
    rw [MarkedSequenceOfBlowups.ideal_zero] at hres
    have := hadmNonMonomial.charZero
    have hsm0 : Smooth ((A (nonMonomialTriple T s)).projectionToSpec 0) :=
      MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hadmNonMonomial
        (A (nonMonomialTriple T s)) 0 (Nat.zero_le _)
    have hne : (orderAtLeastLocus ((nonMonomialTriple T s).ideal.comap
        (A (nonMonomialTriple T s)).isoZero.hom) (nonMonomialTriple T s).mult).Nonempty :=
      orderAtLeastLocus_comap_iso_nonempty_consolidated437 ((A (nonMonomialTriple T s)).projectionToSpec 0) hsm0
        (A (nonMonomialTriple T s)).isoZero (nonMonomialTriple T s).ideal
        (nonMonomialTriple T s).mult (((nonMonomialOrderReductionContinues_iff T s).1 hcont).2)
    exact absurd hres (Set.nonempty_iff_ne_empty.mp hne)
  exact key

theorem extendByNonMonomialPart_eq_append (hinv : ComapIsoInvariance.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (hcont : NonMonomialOrderReductionContinues T s) :
    extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s =
      s.append (continuationByNonMonomialPart hG hspec hT hdim s hcont) hinv := by
  have h := appendRecursivePrincipalization_eq_append hinv T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
    (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))
    (isMarked_seqAtEnd_lastNonMonomialPart hG hspec hT hdim s hcont)
  exact h


end

private def maxOrderNonMonomialPart_consolidated437 {k : Type u} [Field k] (D : MarkedSchemeWithCenter.{u} k) : ℕ :=
  maxOrder (nonMonomialPart D.boundary D.ideal)

private theorem nonMonomialOrder_transport_eqToIso_consolidated437 {k : Type u} [Field k] (D : MarkedSchemeWithCenter.{u} k)
    {Y : Scheme.{u}} (hY : Y = D.ambient) :
    maxOrderNonMonomialPart_consolidated437 (D.transport (eqToIso hY)) = maxOrderNonMonomialPart_consolidated437 D := by
  subst hY
  rw [eqToIso_refl, MarkedSchemeWithCenter.transport_refl]

private theorem isMonomialSplitting_of_boundary_eq_of_ideal_eq_consolidated437 {X : Scheme.{u}}
    {E F : List X.IdealSheafData} {I J M N : X.IdealSheafData} (hE : E = F) (hI : I = J)
    (h : IsMonomialSplitting F J M N) : IsMonomialSplitting E I M N := by
  subst hE
  subst hI
  exact h

private theorem controlledTransform_ofMarkedSequence_consolidated437 {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedSequenceOfBlowups p I m E) (J : X.IdealSheafData) (c : ℕ) (i : ℕ) :
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.controlledTransform J c i
      = MarkedSequenceOfBlowups.controlledTransform s J c i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      exact congrArg
        (fun Z : (s.schemeAt i).IdealSheafData =>
          residualByPow (Z.comap (s.transitionMapSucc i)) (s.exceptionalDivisor i) c) ih

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) {n : ℕ} {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (hcont : NonMonomialOrderReductionContinues T s)
include hG hspec hT hdim hcont

private theorem continuationByNonMonomialPart_length_pos_consolidated437 :
    0 < (continuationByNonMonomialPart hG hspec hT hdim s hcont).length := by
  rw [continuationByNonMonomialPart_length hG hspec hT hdim s hcont]
  exact seqAtEnd_lastNonMonomialPart_length_pos hG hspec hT hdim s hcont

private theorem continuationByNonMonomialPart_boundary_length_consolidated437 :
    (continuationByNonMonomialPart hG hspec hT hdim s hcont).boundary
        (continuationByNonMonomialPart hG hspec hT hdim s hcont).length
      = (A (nonMonomialTriple T s)).boundary (A (nonMonomialTriple T s)).length :=
  ofMarkedSequence_boundary_eq_of_le (A (nonMonomialTriple T s)) (A (nonMonomialTriple T s)).length le_rfl

private theorem continuationByNonMonomialPart_ideal_length_consolidated437 :
    (continuationByNonMonomialPart hG hspec hT hdim s hcont).ideal (continuationByNonMonomialPart hG hspec hT hdim s hcont).length
      = MarkedSequenceOfBlowups.controlledTransform (A (nonMonomialTriple T s))
          (tripleAtLength T s (s.ideal s.length) T.mult).ideal
          (tripleAtLength T s (s.ideal s.length) T.mult).mult
          (A (nonMonomialTriple T s)).length :=
  controlledTransform_ofMarkedSequence_consolidated437
    (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
      (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)))
    (s.ideal s.length) T.mult
    (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
      (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))).length

private theorem nonMonomialPart_continuationByNonMonomialPart_length_consolidated437 :
    nonMonomialPart
        ((continuationByNonMonomialPart hG hspec hT hdim s hcont).boundary
          (continuationByNonMonomialPart hG hspec hT hdim s hcont).length)
        ((continuationByNonMonomialPart hG hspec hT hdim s hcont).ideal
          (continuationByNonMonomialPart hG hspec hT hdim s hcont).length)
      = (A (nonMonomialTriple T s)).ideal (A (nonMonomialTriple T s)).length := by
  have hmu : T.mult ≤ maxOrderNonMonomial T s := ((nonMonomialOrderReductionContinues_iff T s).1 hcont).1
  have hadmLast : (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := isAdmissible_tripleAtLength hG hT s
  have hadmNonMonomial : (nonMonomialTriple T s).IsAdmissible := isAdmissible_nonMonomialTriple hG hT s hcont
  have hsplit : IsMonomialSplitting (s.boundary s.length) (s.ideal s.length)
      (monomialPart (s.boundary s.length) (s.ideal s.length)) (lastNonMonomialPart T s) :=
    isMonomialSplitting_lastNonMonomialPart hG hT s
  have hdim' : (nonMonomialTriple T s).krullDimSucc ≤ n :=
    le_trans (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)) hdim
  have hob : (nonMonomialTriple T s).IsOrderBoundedByMult :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff (nonMonomialTriple T s)).2 fun x =>
      orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
  have hordA := hspec.order_le (nonMonomialTriple T s) hadmNonMonomial hdim' hob
  have hsp := (isMonomialSplitting_controlledTransform_monomialFactor hG hadmLast hsplit hmu (A (nonMonomialTriple T s)) hordA
      (A (nonMonomialTriple T s)).length le_rfl).1
  have hvalid := isAdmissible_tripleAtLength hG hadmLast (continuationByNonMonomialPart hG hspec hT hdim s hcont)
  exact hG.nonMonomialPart_eq_of_isMonomialSplitting _ hvalid _ _
    (isMonomialSplitting_of_boundary_eq_of_ideal_eq_consolidated437 (continuationByNonMonomialPart_boundary_length_consolidated437 hG hspec hT hdim s hcont)
      (continuationByNonMonomialPart_ideal_length_consolidated437 hG hspec hT hdim s hcont) hsp)

private theorem maxOrder_idealAtLength_lt_maxOrderNonMonomial_consolidated437 :
    maxOrder ((A (nonMonomialTriple T s)).ideal (A (nonMonomialTriple T s)).length)
      < maxOrderNonMonomial T s := by
  have hmu : T.mult ≤ maxOrderNonMonomial T s := ((nonMonomialOrderReductionContinues_iff T s).1 hcont).1
  have hmu1 : 1 ≤ maxOrderNonMonomial T s := le_trans hT.one_le_mult hmu
  have hadmNonMonomial : (nonMonomialTriple T s).IsAdmissible := isAdmissible_nonMonomialTriple hG hT s hcont
  have hdim' : (nonMonomialTriple T s).krullDimSucc ≤ n :=
    le_trans (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)) hdim
  have hob : (nonMonomialTriple T s).IsOrderBoundedByMult :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff (nonMonomialTriple T s)).2 fun x =>
      orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
  have hres := hspec.resolves (nonMonomialTriple T s) hadmNonMonomial hdim' hob
  rw [MarkedSequenceOfBlowups.isResolution_iff, MarkedSequenceOfBlowups.lastIdeal_eq] at hres
  exact maxOrder_ideal_length_lt_of_orderAtLeastLocus_eq_empty (A (nonMonomialTriple T s))
    (hspec.order_le (nonMonomialTriple T s) hadmNonMonomial hdim' hob) hres hmu1


end

theorem maxOrderNonMonomial_extendByNonMonomialPart_lt (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (hcont : NonMonomialOrderReductionContinues T s) :
    maxOrderNonMonomial T (extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s) < maxOrderNonMonomial T s := by
  have ht : 0 < (continuationByNonMonomialPart hG hspec hT hdim s hcont).length :=
    continuationByNonMonomialPart_length_pos_consolidated437 hG hspec hT hdim s hcont
  have hconv : maxOrderNonMonomial T (s.append (continuationByNonMonomialPart hG hspec hT hdim s hcont) hinv)
      = maxOrder (nonMonomialPart
          ((continuationByNonMonomialPart hG hspec hT hdim s hcont).boundary
            (continuationByNonMonomialPart hG hspec hT hdim s hcont).length)
          ((continuationByNonMonomialPart hG hspec hT hdim s hcont).ideal
            (continuationByNonMonomialPart hG hspec hT hdim s hcont).length)) := by
    show maxOrderNonMonomialPart_consolidated437 ((s.append (continuationByNonMonomialPart hG hspec hT hdim s hcont) hinv).dataAt
      (s.append (continuationByNonMonomialPart hG hspec hT hdim s hcont) hinv).length) = _
    rw [MarkedBlowupSequenceData.append_dataAt_last s (continuationByNonMonomialPart hG hspec hT hdim s hcont) hinv ht]
    exact nonMonomialOrder_transport_eqToIso_consolidated437 _ _
  rw [extendByNonMonomialPart_eq_append hG hinv hspec hT hdim s hcont, hconv,
    nonMonomialPart_continuationByNonMonomialPart_length_consolidated437 hG hspec hT hdim s hcont]
  exact maxOrder_idealAtLength_lt_maxOrderNonMonomial_consolidated437 hG hspec hT hdim s hcont

end

section

private theorem maxOrderNonMonomial_emptyMarkedBlowupSequenceData_consolidated437 (T : MarkedIdealWithBoundary.{u}) :
    maxOrderNonMonomial T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) =
      maxOrder (nonMonomialPart T.boundary T.ideal) := by
  rfl

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) {n : ℕ} {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
include hG hspec hT hdim

private theorem maxOrderNonMonomial_iter_add_le_of_forall_le_consolidated437 (N : ℕ)
    (hall : ∀ f : ℕ, f ≤ N → NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f)) (f : ℕ) :
    f ≤ N →
      maxOrderNonMonomial T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f) + f ≤
        maxOrder (nonMonomialPart T.boundary T.ideal) := by
  induction f with
  | zero =>
      intro _
      have h0 : maxOrderNonMonomial T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) 0) =
          maxOrder (nonMonomialPart T.boundary T.ideal) := by
        rw [nonMonomialOrderReductionIter_zero hinv T (principalizationOfDimLe T A)]
        exact maxOrderNonMonomial_emptyMarkedBlowupSequenceData_consolidated437 T
      omega
  | succ f ih =>
      intro hf
      have hf' : f ≤ N := by omega
      have hc := hall f hf'
      have hstep := nonMonomialOrderReductionIter_succ_of_continues hinv T (principalizationOfDimLe T A) f hc
      have hlt := maxOrderNonMonomial_extendByNonMonomialPart_lt hG hinv hspec hT hdim
        (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f) hc
      have hih := ih hf'
      rw [hstep]
      omega

theorem not_nonMonomialOrderReductionContinues_nonMonomialOrderReduction :
    ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) := by
  intro hcont
  rw [nonMonomialOrderReduction_eq hinv T (principalizationOfDimLe T A)] at hcont
  have hall : ∀ f : ℕ, f ≤ maxOrder (nonMonomialPart T.boundary T.ideal) + 1 →
      NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f) := by
    intro f hf
    by_contra hnc
    have he := nonMonomialOrderReductionIter_eq_of_not_continues hinv T (principalizationOfDimLe T A) f hnc
      (maxOrder (nonMonomialPart T.boundary T.ideal) + 1) hf
    rw [he] at hcont
    exact hnc hcont
  have hfin := maxOrderNonMonomial_iter_add_le_of_forall_le_consolidated437 hG hinv hspec hT hdim
    (maxOrder (nonMonomialPart T.boundary T.ideal) + 1) hall
    (maxOrder (nonMonomialPart T.boundary T.ideal) + 1) le_rfl
  omega

theorem nonMonomialOrderReductionIter_eq_of_maxOrder_lt (g : ℕ)
    (hg : maxOrder (nonMonomialPart T.boundary T.ideal) + 1 ≤ g) :
    nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) g = nonMonomialOrderReduction hinv T (principalizationOfDimLe T A) := by
  have hnc : ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A)
      (maxOrder (nonMonomialPart T.boundary T.ideal) + 1)) := by
    rw [← nonMonomialOrderReduction_eq hinv T (principalizationOfDimLe T A)]
    exact not_nonMonomialOrderReductionContinues_nonMonomialOrderReduction hG hinv hspec hT hdim
  rw [nonMonomialOrderReduction_eq hinv T (principalizationOfDimLe T A)]
  exact nonMonomialOrderReductionIter_eq_of_not_continues hinv T (principalizationOfDimLe T A)
    (maxOrder (nonMonomialPart T.boundary T.ideal) + 1) hnc g hg


end

private theorem hasPrincipalizationCenter_of_principalizationCertificate_consolidated437 {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (t : MarkedBlowupSequenceData p I m E) (μ i : ℕ)
    (hne : (↑(t.center i).support : Set ↥(t.obj i)).Nonempty)
    (hcert : PrincipalizationCertificate (t.obj i) (t.proj i ≫ p) (t.ideal i) μ
      (t.toMarkedSequenceOfBlowups.boundaryLocus i) (t.center i)) :
    HasPrincipalizationCenter μ (t.dataAt i) := by
  refine ⟨hne, ?_⟩
  rw [MarkedBlowupSequenceData.boundarySupport_dataAt]
  exact hcert

private theorem hasCenter_continuationByNonMonomialPart_consolidated437 (hG : PrincipalizationGeometryHypotheses.{u}) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : NonMonomialOrderReductionContinues T s) (i : ℕ)
    (hi : i < (continuationByNonMonomialPart hG hspec hT hdim s hcont).length) :
    HasPrincipalizationCenter T.mult ((continuationByNonMonomialPart hG hspec hT hdim s hcont).dataAt i) := by
  have hadmNonMonomial : (nonMonomialTriple T s).IsAdmissible := isAdmissible_nonMonomialTriple hG hT s hcont
  have hdim' : (nonMonomialTriple T s).krullDimSucc ≤ n :=
    le_trans (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)) hdim
  have hob : (nonMonomialTriple T s).IsOrderBoundedByMult :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff (nonMonomialTriple T s)).2 fun x =>
      orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
  have hmu : T.mult ≤ maxOrderNonMonomial T s := ((nonMonomialOrderReductionContinues_iff T s).1 hcont).1
  have hadmLast : (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := isAdmissible_tripleAtLength hG hT s
  have hsplit := isMonomialSplitting_lastNonMonomialPart hG hT s
  have hord := hspec.order_le (nonMonomialTriple T s) hadmNonMonomial hdim' hob
  have hcertA := hspec.cert (nonMonomialTriple T s) hadmNonMonomial hdim' hob
  have hne := hspec.center_nonempty (nonMonomialTriple T s) hadmNonMonomial hdim' hob
  rw [continuationByNonMonomialPart_length hG hspec hT hdim s hcont] at hi
  have hprinc := principalizationCertificate_controlledTransform hG hadmLast hsplit hmu
    (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
      (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))) hord hcertA i hi
  have hidl : (continuationByNonMonomialPart hG hspec hT hdim s hcont).ideal i =
      MarkedSequenceOfBlowups.controlledTransform
        (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
          (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)))
        (s.ideal s.length) T.mult i :=
    controlledTransform_ofMarkedSequence_consolidated437
      (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
        (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)))
      (s.ideal s.length) T.mult i
  have hproj : (continuationByNonMonomialPart hG hspec hT hdim s hcont).proj i =
      (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
        (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))).projectionToBase i :=
    BlowupSequenceData.ofSequenceOfBlowups_projectionToBase
      (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
        (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))).toSequenceOfBlowups i
  have hbd : (continuationByNonMonomialPart hG hspec hT hdim s hcont).toMarkedSequenceOfBlowups.boundary i =
      (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
        (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))).boundary i := by
    rw [MarkedBlowupSequenceData.toMarkedSequence_boundary]
    exact ofMarkedSequence_boundary_eq_of_le
      (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
        (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))) i (le_of_lt hi)
  have hloc : (continuationByNonMonomialPart hG hspec hT hdim s hcont).toMarkedSequenceOfBlowups.boundaryLocus i =
      (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
        (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))).boundaryLocus i := by
    apply Set.ext
    intro x
    rw [MarkedSequenceOfBlowups.mem_boundaryLocus_iff
      (continuationByNonMonomialPart hG hspec hT hdim s hcont).toMarkedSequenceOfBlowups i x]
    constructor
    · intro hx
      rw [hbd] at hx
      exact (MarkedSequenceOfBlowups.mem_boundaryLocus_iff
        (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
          (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))) i x).2 hx
    · intro hx
      have hx' := (MarkedSequenceOfBlowups.mem_boundaryLocus_iff
        (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
          (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) (maxOrderNonMonomial T s))) i x).1 hx
      rw [← hbd] at hx'
      exact hx'
  refine hasPrincipalizationCenter_of_principalizationCertificate_consolidated437 (continuationByNonMonomialPart hG hspec hT hdim s hcont) T.mult i (hne i hi) ?_
  rw [hproj, hidl, hloc]
  exact hprinc

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) {n : ℕ} {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
include hG hspec hT hdim

private theorem hasCenter_nonMonomialOrderReductionIter_consolidated437 (f : ℕ) :
    ∀ i < (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).length,
      HasPrincipalizationCenter T.mult ((nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).dataAt i) := by
  induction f with
  | zero =>
      intro i hi
      rw [nonMonomialOrderReductionIter_zero hinv T (principalizationOfDimLe T A)] at hi
      rw [emptyMarkedBlowupSequenceData_length] at hi
      exact absurd hi (Nat.not_lt_zero i)
  | succ f ih =>
      by_cases hc : NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f)
      · have he : nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) (f + 1) =
            (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).append
              (continuationByNonMonomialPart hG hspec hT hdim (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f) hc) hinv := by
          rw [nonMonomialOrderReductionIter_succ_of_continues hinv T (principalizationOfDimLe T A) f hc,
            extendByNonMonomialPart_eq_append hG hinv hspec hT hdim (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f) hc]
        rw [he]
        intro i hi
        exact MarkedBlowupSequenceData.append_dataAt_of_forall _ _ hinv
          (fun D => HasPrincipalizationCenter T.mult D)
          (isInvariantUnderIso_hasPrincipalizationCenter hG.maxContactTransport T.mult) ih
          (fun j hj => hasCenter_continuationByNonMonomialPart_consolidated437 hG hspec hT hdim _ hc j hj) i hi
      · rw [nonMonomialOrderReductionIter_succ_of_not_continues hinv T (principalizationOfDimLe T A) f hc]
        exact ih

theorem hasCenter_nonMonomialOrderReduction (i : ℕ)
    (hi : i < (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).length) :
    HasPrincipalizationCenter T.mult ((nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).dataAt i) := by
  rw [nonMonomialOrderReduction_eq hinv T (principalizationOfDimLe T A)] at hi ⊢
  exact hasCenter_nonMonomialOrderReductionIter_consolidated437 hG hinv hspec hT hdim _ i hi

theorem orderAt_lastNonMonomialPart_nonMonomialOrderReduction_lt (x : ↥((nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).obj (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).length)) :
    orderAt (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))) x < ((T.mult : ℕ) : ℕ∞) := by
  have hB : ∀ y : ↥((nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).obj (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).length),
      orderAt (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))) y ≤
        ((maxOrderNonMonomial T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) : ℕ) : ℕ∞) :=
    fun y => orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) y
  have : Nonempty
      ↥((nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).obj (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).length) := ⟨x⟩
  have hne : (orderAtLeastLocus (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)))
      (maxOrder (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))))).Nonempty :=
    orderAtLeastLocus_maxOrder_nonempty (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))) hB
  have hnc : ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) :=
    not_nonMonomialOrderReductionContinues_nonMonomialOrderReduction hG hinv hspec hT hdim
  rw [nonMonomialOrderReductionContinues_iff] at hnc
  have hmax : maxOrderNonMonomial T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) =
      maxOrder (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))) := rfl
  have hlt : maxOrder (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))) < T.mult := by
    by_contra hle
    push Not at hle
    exact hnc ⟨by rw [hmax]; exact hle, by rw [hmax]; exact hne⟩
  exact orderAt_lt_of_maxOrder_lt (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))) hB hlt x


end

end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionHypotheses
section


section

structure MonomialCaseHypotheses : Prop where
  card_lt_dim :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        (intersectionComponents T.boundary J).Nonempty → J.card < krullDimSucc T.scheme
  center_smooth :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)),
            Smooth
              ((componentUnionIdeal T.boundary J 𝒞 hop).subschemeι ≫ T.structMap)
  center_snc :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)),
            HasStrictNormalCrossingsWith T.structMap (componentUnionIdeal T.boundary J 𝒞 hop) T.boundary
  blowup_total_transform :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary, ∀ (x' : ↥X'),
                ∃ (U' : X'.Opens) (ε : ℕ),
                  x' ∈ U' ∧ (ε = 0 ∨ ε = 1) ∧
                    (ε = 1 ↔ ∃ V : T.scheme.Opens, π x' ∈ V ∧
                      (Z.support : Set ↥T.scheme) ∩ (V : Set ↥T.scheme) ⊆
                        (D.support : Set ↥T.scheme)) ∧
                    (D.comap π).comap U'.ι =
                      (Blowup.strictTransform π Z D).comap U'.ι *
                        (Blowup.exceptionalIdeal π Z).comap U'.ι ^ ε
  components_subset_divisor_iff :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ C ∈ intersectionComponents T.boundary J,
          ∀ (i : Fin T.boundary.length),
            C ⊆ ((T.boundary.get i).support : Set ↥T.scheme) ↔ i ∈ J
  transformed_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J₀ : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J₀,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J₀).subschemeι ⁻¹' ⋃₀ 𝒞))
            (X' : Scheme.{u}) (π : X' ⟶ T.scheme),
            Blowup.IsBlowupAlongIdealSheaf π (componentUnionIdeal T.boundary J₀ 𝒞 hop) →
              ∀ (J : Finset (Fin T.boundary.length)),
                ∀ C' ∈ intersectionComponents
                    (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
                    (Finset.image
                      (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary) J),
                  ∀ (ξ' : ↥X'), IsGenericPoint ξ' C' →
                    ξ' ∉ (Blowup.exceptionalIdeal π (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support ∧
                      ∃ C ∈ intersectionComponents T.boundary J,
                        C ∉ 𝒞 ∧
                          C' = closure (⇑π ⁻¹' C \
                              ((Blowup.exceptionalIdeal π
                                (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support :
                                  Set ↥X')) ∧
                            ∀ (ξ : ↥T.scheme), IsGenericPoint ξ C → π ξ' = ξ
  stratum_smooth :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap)
  orderAt_comap_off_exceptional :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (Z : T.scheme.IdealSheafData),
        Blowup.IsBlowupAlongIdealSheaf π Z →
          ∀ x' ∉ (Blowup.exceptionalIdeal π Z).support,
            ∀ (A : T.scheme.IdealSheafData), orderAt (A.comap π) x' = orderAt A (π x')
  orderAt_boundary_eq_one :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ D ∈ T.boundary, ∀ x ∈ D.support, orderAt D x = 1

theorem monomialGeometryHypotheses_of_monomialCaseHypotheses (hR : MonomialCaseHypotheses.{u}) :
    MonomialGeometryHypotheses.{u} where
  card_lt_dim := hR.card_lt_dim
  flat_comap_center := by
    intro T hT Y k' hk q g hg hT' J 𝒞 h𝒞 hop
    exact FunctorialResolution.EmbeddedResolution.comap_componentUnionIdeal_of_flat T hT Y k' q g hT' J 𝒞 h𝒞 hop
  center_smooth := hR.center_smooth
  center_snc := hR.center_snc
  center_support := by
    intro T hT J 𝒞 h𝒞 hop
    exact FunctorialResolution.EmbeddedResolution.componentUnionIdeal_support_eq_sUnion T hT J 𝒞 h𝒞 hop
  blowup_total_transform := hR.blowup_total_transform
  flat_components_down := by
    intro T hT Y k' hk q g hg hT' J C' hC'
    exact FunctorialResolution.EmbeddedResolution.exists_intersectionComponents_mapsTo_of_flat T hT Y k' q g hT' J C' hC'
  flat_components_up := by
    intro T hT Y k' hk q g hg hT' J C hC y hy
    exact FunctorialResolution.EmbeddedResolution.exists_mem_intersectionComponents_pullbackOverField_of_flat T hT Y k' q g hT' J C hC y hy
  smooth_components_down := by
    intro T hT Y q h hsm hq hV J C' hC'
    have : Flat h := inferInstance
    have hV' : (T.pullbackOverField Y T.base q h).IsAdmissible := by
      rw [MarkedIdealWithBoundary.pullbackOverField_eq_pullbackAlong]
      exact hV
    have e : pullbackOverFieldIndex T Y T.base q h = pullbackAlongIndex T Y q h := by
      funext j
      apply Fin.ext
      rw [pullbackOverFieldIndex_val, pullbackAlongIndex_val]
    have hC'' : C' ∈ intersectionComponents (T.pullbackOverField Y T.base q h).boundary
        (Finset.image (pullbackOverFieldIndex T Y T.base q h) J) := by
      rw [e]
      exact hC'
    exact FunctorialResolution.EmbeddedResolution.exists_intersectionComponents_mapsTo_of_flat T hT Y T.base q h hV' J C' hC''
  smooth_components_up := by
    intro T hT Y q h hsm hq hV J C hC y hy
    have : Flat h := inferInstance
    have hV' : (T.pullbackOverField Y T.base q h).IsAdmissible := by
      rw [MarkedIdealWithBoundary.pullbackOverField_eq_pullbackAlong]
      exact hV
    have e : pullbackOverFieldIndex T Y T.base q h = pullbackAlongIndex T Y q h := by
      funext j
      apply Fin.ext
      rw [pullbackOverFieldIndex_val, pullbackAlongIndex_val]
    obtain ⟨C', hC'mem, hyC', hgen⟩ :=
      FunctorialResolution.EmbeddedResolution.exists_mem_intersectionComponents_pullbackOverField_of_flat T hT Y T.base q h hV' J C hC y hy
    refine ⟨C', ?_, hyC', hgen⟩
    rw [← e]
    exact hC'mem
  components_disjoint := by
    intro T hT J C hC C' hC' hne
    exact FunctorialResolution.EmbeddedResolution.intersectionComponents_disjoint_of_smooth T J (hR.stratum_smooth T hT J) C C' hC hC' hne
  components_finite := by
    intro T hT J
    exact FunctorialResolution.EmbeddedResolution.intersectionComponents_finite T hT J
  components_subset_divisor_iff := hR.components_subset_divisor_iff
  transformed_components := hR.transformed_components
  level_schemeDim_le := by
    intro T hT s i hi
    have h := MarkedIdealWithBoundary.transformAt_dim_le FunctorialResolution.EmbeddedResolution.dimensionNonincreasingAlongBlowups hT s i hi
    rwa [MarkedIdealWithBoundary.transformAt_dim] at h
  stratum_smooth := hR.stratum_smooth
  level_valid := by
    intro T hT s i hi
    exact MarkedIdealWithBoundary.IsAdmissible.transformAt FunctorialResolution.EmbeddedResolution.effectiveCartierSupportContainsNoComponent hT s i hi
  orderAt_bounded := by
    intro T hT I hI
    exact FunctorialResolution.EmbeddedResolution.exists_orderAt_le T hT I hI
  orderAt_comap_off_exceptional := hR.orderAt_comap_off_exceptional
  orderAt_boundary_eq_one := hR.orderAt_boundary_eq_one
  sUnion_isOpen := by
    intro T hT J 𝒞 h𝒞
    exact FunctorialResolution.EmbeddedResolution.isOpen_preimage_sUnion_intersectionComponents T hT J (hR.stratum_smooth T hT J) 𝒞 h𝒞
  withBoundary_valid := by
    intro T hT E' hE
    apply MarkedIdealWithBoundary.validOfSameNontrivialBoundary <;> assumption

structure OrderReductionHypotheses : Prop where
  controlledTransform_orderAt_le :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ (J : T.scheme.IdealSheafData) (c : ℕ),
                (∀ x ∈ Z.support, orderAt J x = (c : ℕ∞)) →
                  ∀ (J' : X'.IdealSheafData),
                    Blowup.exceptionalIdeal π Z ^ c * J' = J.comap π →
                      ∀ x' ∈ (Blowup.exceptionalIdeal π Z).support, orderAt J' x' ≤ (c : ℕ∞)
  strictTransform_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary,
                ∀ C' : Set ↥X',
                  IsIrreducibleComponentOf C' ((Blowup.strictTransform π Z D).support : Set ↥X') →
                    ∃ (ξ' : ↥X') (C : Set ↥T.scheme),
                      C' = closure ({ξ'} : Set ↥X') ∧
                        ξ' ∉ (Blowup.exceptionalIdeal π Z).support ∧
                          IsIrreducibleComponentOf C (D.support : Set ↥T.scheme) ∧
                            ¬ C ⊆ (Z.support : Set ↥T.scheme) ∧
                              C = closure ({π ξ'} : Set ↥T.scheme)
  monomial : MonomialCaseHypotheses.{u}

theorem geometricHypotheses_of_orderReductionHypotheses (hR : OrderReductionHypotheses.{u}) : PrincipalizationGeometryHypotheses.{u} where
  maxContactTransport := FunctorialResolution.EmbeddedResolution.isoInvariantOrderCertificateDescend
  exceptional_components_not_subset := by
    intro T hT Z hZsm hZsnc X' π hπ J c hord J' htr C' hC'
    have := hT.charZero
    have := hT.smooth
    have := hT.isNoetherian
    have := FunctorialResolution.EmbeddedResolution.isLocallyNoetherian_of_isBlowupAlongIdealSheaf π Z hπ
    refine FunctorialResolution.EmbeddedResolution.controlledTransform_not_subset_support T.structMap Z T.boundary hZsnc π hπ
      J c hord J' htr C' hC'.1 hC'.2.1 ?_
    intro S hirr hsub hsup
    exact hC'.2.2 S hirr hsup hsub
  orderAt_baseChange := by
    intro T hT L hL hLz f I y
    have := hT.charZero
    have := hT.smooth
    exact FunctorialResolution.EmbeddedResolution.orderAt_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) I y
  controlledTransform_orderAt_le := hR.controlledTransform_orderAt_le
  splitting_baseChange := by
    intro T hT L hL hLz f hV M N hs
    exact FunctorialResolution.EmbeddedResolution.isMonomialSplitting_comap_of_flat
      (CategoryTheory.Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f)) hs
  splitting_smooth_pullback := by
    intro T hT Y q h hsm hq hV M N hs
    exact FunctorialResolution.EmbeddedResolution.isMonomialSplitting_comap_of_smooth h hs
  splitting_exists := by
    intro T hT
    have := hT.charZero
    have := hT.smooth
    have := hT.locallyOfFiniteType
    have := hT.quasiCompact
    have := hT.isNoetherian
    exact FunctorialResolution.EmbeddedResolution.exists_isMonomialSplitting T.structMap T.boundary hT.snc T.ideal
      hT.nonzeroOnComponents
  splitting_unique := by
    intro T hT M N M' N' hs hs'
    have := hT.charZero
    have := hT.smooth
    have := hT.locallyOfFiniteType
    have := hT.quasiCompact
    have := hT.isNoetherian
    exact FunctorialResolution.EmbeddedResolution.isMonomialSplitting_unique T.structMap T.boundary hT.snc
      hT.nonzeroOnComponents hs hs'
  strictTransform_components := hR.strictTransform_components
  monomialInputs := monomialGeometryHypotheses_of_monomialCaseHypotheses hR.monomial


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.CompanionIdealReduction
section


section

abbrev companionTriple (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) : MarkedIdealWithBoundary.{u} :=
  tripleAtLength T s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
include hG hT

theorem orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus :
    ∀ x ∈ orderAtLeastLocus (s.ideal s.length) T.mult,
      orderAt (lastNonMonomialPart T s) x ≤ ((maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) := by
  obtain ⟨B, hB⟩ := exists_orderAt_lastNonMonomialPart_le hG hT s
  intro x hx
  exact orderAt_le_maxOrderOn (lastNonMonomialPart T s) hB
    (orderAtLeastLocus (s.ideal s.length) T.mult) hx

theorem orderAt_companionIdeal_le (hcont : CompanionIdealReductionContinues T s) :
    ∀ x : ↥(s.obj s.length),
      orderAt (companionIdeal T s) x ≤ ((T.mult * maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) := by
  have hs : 1 ≤ maxOrderNonMonomialOnOrderLocus T s := (companionIdealReductionContinues_iff T s).mp hcont
  have hT' : (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := isAdmissible_tripleAtLength hG hT s
  have hord := orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT s
  intro x
  exact (isAdmissible_withIdealAndMult_pow_sup_pow hT' hs hord).2 x

theorem companionTriple_isAdmissible (hcont : CompanionIdealReductionContinues T s) :
    (companionTriple T s).IsAdmissible := by
  have h1 : (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := isAdmissible_tripleAtLength hG hT s
  have hv : 1 ≤ maxOrderNonMonomialOnOrderLocus T s := (companionIdealReductionContinues_iff T s).mp hcont
  exact (isAdmissible_withIdealAndMult_pow_sup_pow h1 hv
    (orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT s)).1


end

theorem isMarked_seqAtEnd_companionIdeal (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (A : PrincipalizationAssignment.{u}) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : CompanionIdealReductionContinues T s) :
    (MarkedBlowupSequenceData.ofMarkedSequence
          (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
            (tripleAtLength_dim_le hG hT s _ _))).toBlowupSequenceData.IsMarked
      (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length) := by
  have hs : 1 ≤ maxOrderNonMonomialOnOrderLocus T s := (companionIdealReductionContinues_iff T s).mp hcont
  have hT' : (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := isAdmissible_tripleAtLength hG hT s
  have hsplit := isMonomialSplitting_lastNonMonomialPart hG hT s
  have hord := orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT s
  exact isMarked_ofMarkedSequence_of_isMonomialSplitting hG hT' hsplit hs hord
    (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
      (tripleAtLength_dim_le hG hT s _ _))

def continuationByCompanionIdeal (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (A : PrincipalizationAssignment.{u}) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : CompanionIdealReductionContinues T s) :
    MarkedBlowupSequenceData (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult
      (s.boundary s.length) :=
  BlowupSequenceData.toMarkedBlowupSequenceData
    (MarkedBlowupSequenceData.ofMarkedSequence
        (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
          (tripleAtLength_dim_le hG hT s _ _))).toBlowupSequenceData
    (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length)
    (isMarked_seqAtEnd_companionIdeal hG hT A s hcont)

private theorem orderAtLeastLocus_eq_empty_of_comap_iso_consolidated453 {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (e : Y ≅ X) (J : X.IdealSheafData) (c : ℕ)
    (hJ : orderAtLeastLocus (J.comap e.hom) c = ∅) : orderAtLeastLocus J c = ∅ := by
  have hhom : Smooth e.hom := inferInstance
  have hinv : Smooth e.inv := inferInstance
  have hp : Smooth (e.hom ≫ p) := inferInstance
  have hcomp : (J.comap e.hom).comap e.inv = J := by
    rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  have key := image_orderAtLeastLocus_comap_subset k (e.hom ≫ p) e.inv (J.comap e.hom) c
  rw [hcomp, hJ] at key
  exact Set.image_eq_empty.mp (Set.subset_empty_iff.mp key)

section
variable (hG : PrincipalizationGeometryHypotheses.{u})

theorem seqAtEnd_companionIdeal_length_pos {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : CompanionIdealReductionContinues T s) :
    0 < (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
      (tripleAtLength_dim_le hG hT s _ _)).length := by
  have hv : 1 ≤ maxOrderNonMonomialOnOrderLocus T s := (companionIdealReductionContinues_iff T s).mp hcont
  have hm : 1 ≤ T.mult := hT.one_le_mult
  have hSvalid : (companionTriple T s).IsAdmissible := companionTriple_isAdmissible hG hT s hcont
  have hSdim : (companionTriple T s).krullDimSucc ≤ n :=
    le_trans (tripleAtLength_dim_le hG hT s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)) hdim
  have hSob : (companionTriple T s).IsOrderBoundedByMult :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff _).mpr (orderAt_companionIdeal_le hG hT s hcont)
  have hcall : principalizationSeqAtEnd T (principalizationOfDimLe T A) s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
      (tripleAtLength_dim_le hG hT s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)) =
      A (companionTriple T s) := rfl
  rw [hcall]
  rcases Nat.eq_zero_or_pos (A (companionTriple T s)).length with h0 | hpos
  · exfalso
    have hcz : CharZero T.base := hT.charZero
    have hsm : Smooth (s.proj s.length ≫ T.structMap) := hSvalid.smooth
    have hres := (MarkedSequenceOfBlowups.isResolution_iff (A (companionTriple T s))).mp
      (hspec.resolves (companionTriple T s) hSvalid hSdim hSob)
    rw [MarkedSequenceOfBlowups.lastIdeal_eq, h0, MarkedSequenceOfBlowups.ideal_zero] at hres
    have hempty : orderAtLeastLocus (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s) = ∅ :=
      orderAtLeastLocus_eq_empty_of_comap_iso_consolidated453 (s.proj s.length ≫ T.structMap)
        (A (companionTriple T s)).isoZero (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s) hres
    have hforall := (orderAtLeastLocus_pow_sup_pow_eq_empty_iff T.base (s.proj s.length ≫ T.structMap)
      (lastNonMonomialPart T s) (s.ideal s.length) hm hv).mp hempty
    obtain ⟨Bd, hBd⟩ := exists_orderAt_lastNonMonomialPart_le hG hT s
    have hlt := maxOrderOn_lt_of_forall_lt (lastNonMonomialPart T s) hBd
      (orderAtLeastLocus (s.ideal s.length) T.mult) hv hforall
    have hpi : maxOrderNonMonomialOnOrderLocus T s =
        maxOrderOn (lastNonMonomialPart T s) (orderAtLeastLocus (s.ideal s.length) T.mult) := rfl
    rw [hpi] at hlt
    exact lt_irrefl _ hlt
  · exact hpos

theorem extendByCompanionIdeal_eq_append (hinv : ComapIsoInvariance.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (A : PrincipalizationAssignment.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (hcont : CompanionIdealReductionContinues T s) :
    extendByCompanionIdeal hinv T (principalizationOfDimLe T A) s =
      s.append (continuationByCompanionIdeal hG hT A s hcont) hinv :=
  appendRecursivePrincipalization_eq_append hinv T (principalizationOfDimLe T A) s (companionIdeal T s)
    (T.mult * maxOrderNonMonomialOnOrderLocus T s) (tripleAtLength_dim_le hG hT s _ _)
    (isMarked_seqAtEnd_companionIdeal hG hT A s hcont)


end

private noncomputable def maxOrderNonMonomialPartOnOrderAtLeastLocus {k : Type u} [Field k] (μ : ℕ)
    (D : MarkedSchemeWithCenter k) : ℕ :=
  maxOrderOn (nonMonomialPart D.boundary D.ideal) (orderAtLeastLocus D.ideal μ)

private theorem maxOrderNonMonomial_transport_eqToIso_consolidated453 {k : Type u} [Field k] (μ : ℕ)
    (D : MarkedSchemeWithCenter k) {A : Scheme.{u}} (h : A = D.ambient) :
    maxOrderNonMonomialPartOnOrderAtLeastLocus μ (D.transport (eqToIso h)) = maxOrderNonMonomialPartOnOrderAtLeastLocus μ D := by
  subst h
  exact congrArg (maxOrderNonMonomialPartOnOrderAtLeastLocus μ) (MarkedSchemeWithCenter.transport_refl D)

private noncomputable def companionIdealPrincipalizationSeq (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (A : PrincipalizationAssignment.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    MarkedSequenceOfBlowups (s.proj s.length ≫ T.structMap) (companionIdeal T s)
      (T.mult * maxOrderNonMonomialOnOrderLocus T s) (s.boundary s.length) :=
  principalizationSeqAtEnd T (principalizationOfDimLe T A) s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
    (tripleAtLength_dim_le hG hT s _ _)

section
variable (hG : PrincipalizationGeometryHypotheses.{u})
include hG

private theorem continuationByCompanionIdeal_ideal_eq_consolidated453 {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (A : PrincipalizationAssignment.{u}) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : CompanionIdealReductionContinues T s) : ∀ i : ℕ,
    (continuationByCompanionIdeal hG hT A s hcont).ideal i
      = MarkedSequenceOfBlowups.controlledTransform (companionIdealPrincipalizationSeq hG hT A s) (s.ideal s.length)
          T.mult i := by
  intro i
  induction i with
  | zero => rfl
  | succ j ih =>
      rw [MarkedSequenceOfBlowups.controlledTransform_succ, ← ih]
      rfl

theorem maxOrderNonMonomialOnOrderLocus_extendByCompanionIdeal_lt (hinv : ComapIsoInvariance.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (hcont : CompanionIdealReductionContinues T s) :
    maxOrderNonMonomialOnOrderLocus T (extendByCompanionIdeal hinv T (principalizationOfDimLe T A) s) < maxOrderNonMonomialOnOrderLocus T s := by
  have hs1 : 1 ≤ maxOrderNonMonomialOnOrderLocus T s := (companionIdealReductionContinues_iff T s).mp hcont
  have ht : 0 < (continuationByCompanionIdeal hG hT A s hcont).length :=
    seqAtEnd_companionIdeal_length_pos hG hspec hT hdim s hcont
  have hT2 : (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := isAdmissible_tripleAtLength hG hT s
  have hsplit := isMonomialSplitting_lastNonMonomialPart hG hT s
  have hord := orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT s
  have hboundaryEq : (continuationByCompanionIdeal hG hT A s hcont).boundary (continuationByCompanionIdeal hG hT A s hcont).length
      = (companionIdealPrincipalizationSeq hG hT A s).boundary
          (companionIdealPrincipalizationSeq hG hT A s).length :=
    ofMarkedSequence_boundary_eq_of_le (companionIdealPrincipalizationSeq hG hT A s)
      (companionIdealPrincipalizationSeq hG hT A s).length le_rfl
  have hideal : (continuationByCompanionIdeal hG hT A s hcont).ideal (continuationByCompanionIdeal hG hT A s hcont).length
      = MarkedSequenceOfBlowups.controlledTransform (companionIdealPrincipalizationSeq hG hT A s) (s.ideal s.length)
          T.mult (companionIdealPrincipalizationSeq hG hT A s).length :=
    continuationByCompanionIdeal_ideal_eq_consolidated453 hG hT A s hcont (continuationByCompanionIdeal hG hT A s hcont).length
  have hidealEq : (continuationByCompanionIdeal hG hT A s hcont).ideal (continuationByCompanionIdeal hG hT A s hcont).length
      = MarkedSequenceOfBlowups.controlledTransform (companionIdealPrincipalizationSeq hG hT A s)
          (tripleAtLength T s (s.ideal s.length) T.mult).ideal
          (tripleAtLength T s (s.ideal s.length) T.mult).mult
          (companionIdealPrincipalizationSeq hG hT A s).length := hideal
  have hempty : orderAtLeastLocus ((companionIdealPrincipalizationSeq hG hT A s).ideal
      (companionIdealPrincipalizationSeq hG hT A s).length) (T.mult * maxOrderNonMonomialOnOrderLocus T s) = ∅ := by
    have hres := hspec.resolves (companionTriple T s) (companionTriple_isAdmissible hG hT s hcont)
      (le_trans (tripleAtLength_dim_le hG hT s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)) hdim)
      ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff _).mpr (orderAt_companionIdeal_le hG hT s hcont))
    have h2 := (MarkedSequenceOfBlowups.isResolution_iff _).mp hres
    rw [MarkedSequenceOfBlowups.lastIdeal_eq] at h2
    exact h2
  have hlt0 := orderAt_controlledNonMonomialTransform_length_lt hG hT2 hsplit hs1 hord
    (companionIdealPrincipalizationSeq hG hT A s) hempty
  have hlt : ∀ x ∈ orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform (companionIdealPrincipalizationSeq hG hT A s)
        (s.ideal s.length) T.mult (companionIdealPrincipalizationSeq hG hT A s).length) T.mult,
      orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform (companionIdealPrincipalizationSeq hG hT A s)
        (lastNonMonomialPart T s) (maxOrderNonMonomialOnOrderLocus T s)
        (companionIdealPrincipalizationSeq hG hT A s).length) x
        < ((maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) := hlt0
  have hsp := (isMonomialSplitting_controlledTransform_of_le_length hG hT2 hsplit hs1 hord (companionIdealPrincipalizationSeq hG hT A s)
    (companionIdealPrincipalizationSeq hG hT A s).length le_rfl).2.1
  have hsp' : IsMonomialSplitting
      ((continuationByCompanionIdeal hG hT A s hcont).boundary (continuationByCompanionIdeal hG hT A s hcont).length)
      ((continuationByCompanionIdeal hG hT A s hcont).ideal (continuationByCompanionIdeal hG hT A s hcont).length)
      (MarkedSequenceOfBlowups.controlledMonomialTransform (companionIdealPrincipalizationSeq hG hT A s)
        (monomialPart (s.boundary s.length) (s.ideal s.length)) T.mult (maxOrderNonMonomialOnOrderLocus T s)
        (companionIdealPrincipalizationSeq hG hT A s).length)
      (MarkedSequenceOfBlowups.controlledNonMonomialTransform (companionIdealPrincipalizationSeq hG hT A s) (lastNonMonomialPart T s)
        (maxOrderNonMonomialOnOrderLocus T s) (companionIdealPrincipalizationSeq hG hT A s).length) := by
    rw [hboundaryEq, hidealEq]
    exact hsp
  have hT' := isAdmissible_tripleAtLength hG hT2 (continuationByCompanionIdeal hG hT A s hcont)
  have hNM0 := hG.nonMonomialPart_eq_of_isMonomialSplitting _ hT' _ _ hsp'
  have hnonMon : nonMonomialPart
      ((continuationByCompanionIdeal hG hT A s hcont).boundary (continuationByCompanionIdeal hG hT A s hcont).length)
      ((continuationByCompanionIdeal hG hT A s hcont).ideal (continuationByCompanionIdeal hG hT A s hcont).length)
      = MarkedSequenceOfBlowups.controlledNonMonomialTransform (companionIdealPrincipalizationSeq hG hT A s) (lastNonMonomialPart T s)
          (maxOrderNonMonomialOnOrderLocus T s) (companionIdealPrincipalizationSeq hG hT A s).length := hNM0
  obtain ⟨Bd, hBd⟩ := exists_orderAt_lastNonMonomialPart_le hG hT2 (continuationByCompanionIdeal hG hT A s hcont)
  have hBd3 : ∀ x : ↥((companionIdealPrincipalizationSeq hG hT A s).schemeAt
        (companionIdealPrincipalizationSeq hG hT A s).length),
      orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform (companionIdealPrincipalizationSeq hG hT A s)
        (lastNonMonomialPart T s) (maxOrderNonMonomialOnOrderLocus T s)
        (companionIdealPrincipalizationSeq hG hT A s).length) x ≤ (Bd : ℕ∞) := by
    intro x
    have h0 : orderAt (nonMonomialPart
        ((continuationByCompanionIdeal hG hT A s hcont).boundary (continuationByCompanionIdeal hG hT A s hcont).length)
        ((continuationByCompanionIdeal hG hT A s hcont).ideal (continuationByCompanionIdeal hG hT A s hcont).length)) x
          ≤ (Bd : ℕ∞) := hBd x
    rw [hnonMon] at h0
    exact h0
  have key : maxOrderNonMonomialOnOrderLocus T (s.append (continuationByCompanionIdeal hG hT A s hcont) hinv)
      = maxOrderNonMonomialPartOnOrderAtLeastLocus T.mult
        ((continuationByCompanionIdeal hG hT A s hcont).dataAt (continuationByCompanionIdeal hG hT A s hcont).length) := by
    have h1 : maxOrderNonMonomialOnOrderLocus T (s.append (continuationByCompanionIdeal hG hT A s hcont) hinv)
        = maxOrderNonMonomialPartOnOrderAtLeastLocus T.mult ((s.append (continuationByCompanionIdeal hG hT A s hcont) hinv).dataAt
            (s.append (continuationByCompanionIdeal hG hT A s hcont) hinv).length) := rfl
    rw [h1, MarkedBlowupSequenceData.append_dataAt_last s (continuationByCompanionIdeal hG hT A s hcont) hinv ht]
    exact maxOrderNonMonomial_transport_eqToIso_consolidated453 T.mult
      ((continuationByCompanionIdeal hG hT A s hcont).dataAt (continuationByCompanionIdeal hG hT A s hcont).length) _
  rw [extendByCompanionIdeal_eq_append hG hinv hT A s hcont, key]
  show maxOrderOn (nonMonomialPart
      ((continuationByCompanionIdeal hG hT A s hcont).boundary (continuationByCompanionIdeal hG hT A s hcont).length)
      ((continuationByCompanionIdeal hG hT A s hcont).ideal (continuationByCompanionIdeal hG hT A s hcont).length))
      (orderAtLeastLocus ((continuationByCompanionIdeal hG hT A s hcont).ideal (continuationByCompanionIdeal hG hT A s hcont).length)
        T.mult) < maxOrderNonMonomialOnOrderLocus T s
  rw [hnonMon, hideal]
  exact maxOrderOn_lt_of_forall_lt _ hBd3 _ hs1 hlt


end

private theorem support_comap_iso_hom_nonempty_consolidated453 {X Y : Scheme.{u}} (e : X ≅ Y)
    (J : Y.IdealSheafData) (h : (J.support : Set ↥Y).Nonempty) :
    ((J.comap e.hom).support : Set ↥X).Nonempty := by
  obtain ⟨y, hy⟩ := h
  refine ⟨e.inv y, ?_⟩
  have hy2 : e.hom (e.inv y) ∈ J.support := by
    rw [Scheme.inv_hom_apply]
    exact hy
  exact (mem_comap_support_iff_base_mem_support e.hom J (e.inv y)).mpr hy2

private theorem isInvariantUnderIso_hasPrincipalizationCenter_of_two_le_consolidated453 {k : Type u} [Field k] {μ : ℕ}
    (hμ : 2 ≤ μ) : IsInvariantUnderIso (fun D : MarkedSchemeWithCenter.{u} k => HasPrincipalizationCenter μ D) := by
  intro D A e hD
  exact ⟨support_comap_iso_hom_nonempty_consolidated453 e D.center hD.center_nonempty,
    PrincipalizationCertificate.of_two_le _ _ _ _ _ _ hμ⟩

theorem hasCenter_extendByCompanionIdeal (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (hcont : CompanionIdealReductionContinues T s)
    (hm : 2 ≤ T.mult) (hs : ∀ i < s.length, HasPrincipalizationCenter T.mult (s.dataAt i)) (i : ℕ)
    (hi : i < (extendByCompanionIdeal hinv T (principalizationOfDimLe T A) s).length) :
    HasPrincipalizationCenter T.mult ((extendByCompanionIdeal hinv T (principalizationOfDimLe T A) s).dataAt i) := by
  have hval : (companionTriple T s).IsAdmissible := companionTriple_isAdmissible hG hT s hcont
  have hd : (companionTriple T s).krullDimSucc ≤ n :=
    le_trans (tripleAtLength_dim_le hG hT s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)) hdim
  have hob : (companionTriple T s).IsOrderBoundedByMult :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff (companionTriple T s)).mpr
      (orderAt_companionIdeal_le hG hT s hcont)
  have ht : ∀ j < (continuationByCompanionIdeal hG hT A s hcont).length,
      HasPrincipalizationCenter T.mult ((continuationByCompanionIdeal hG hT A s hcont).dataAt j) := by
    intro j hj
    exact ⟨hspec.center_nonempty (companionTriple T s) hval hd hob j hj,
      PrincipalizationCertificate.of_two_le _ _ _ _ _ _ hm⟩
  rw [extendByCompanionIdeal_eq_append hG hinv hT A s hcont] at hi ⊢
  exact MarkedBlowupSequenceData.append_dataAt_of_forall s (continuationByCompanionIdeal hG hT A s hcont) hinv
    (fun D => HasPrincipalizationCenter T.mult D) (isInvariantUnderIso_hasPrincipalizationCenter_of_two_le_consolidated453 hm) hs ht i hi

theorem companionIdealReductionContinues_of_continues_iter (hinv : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (rc : (S : MarkedIdealWithBoundary.{u}) → S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s₀ : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (f : ℕ)
    (h : CompanionIdealReductionContinues T (companionIdealReductionIter hinv T rc s₀ f)) : CompanionIdealReductionContinues T s₀ := by
  revert h
  induction f with
  | zero =>
      intro h
      rwa [companionIdealReductionIter_zero] at h
  | succ n ih =>
      intro h
      by_cases hc : CompanionIdealReductionContinues T (companionIdealReductionIter hinv T rc s₀ n)
      · exact ih hc
      · rw [companionIdealReductionIter_succ_of_not_continues hinv T rc s₀ n hc] at h
        exact ih h

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) {n : ℕ} {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
include hG hspec hT hdim

theorem two_le_mult_of_continues_after_nonMonomialOrderReduction (hcont : CompanionIdealReductionContinues T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))) : 2 ≤ T.mult := by
  have hv : 1 ≤ maxOrderNonMonomialOnOrderLocus T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) :=
    (companionIdealReductionContinues_iff T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))).mp hcont
  obtain ⟨Bd, hBd⟩ := exists_orderAt_lastNonMonomialPart_le hG hT (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))
  have hlt : maxOrderOn (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)))
      (orderAtLeastLocus ((nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).ideal
        (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).length) T.mult) < T.mult :=
    maxOrderOn_lt_of_forall_lt (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))) hBd
      (orderAtLeastLocus ((nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).ideal
        (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).length) T.mult) hT.one_le_mult
      (fun x _ => orderAt_lastNonMonomialPart_nonMonomialOrderReduction_lt hG hinv hspec hT hdim x)
  have hpi : maxOrderNonMonomialOnOrderLocus T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) =
      maxOrderOn (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)))
        (orderAtLeastLocus ((nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).ideal
          (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).length) T.mult) := rfl
  rw [← hpi] at hlt
  omega

theorem maxOrderNonMonomialOnOrderLocus_iter_add_le (s₀ : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (f : ℕ)
    (h : CompanionIdealReductionContinues T (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s₀ f)) :
    maxOrderNonMonomialOnOrderLocus T (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s₀ f) + f ≤ maxOrderNonMonomialOnOrderLocus T s₀ := by
  revert h
  induction f with
  | zero =>
      intro h
      rw [companionIdealReductionIter_zero]
      omega
  | succ m ih =>
      intro h
      by_cases hc : CompanionIdealReductionContinues T (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s₀ m)
      · have hstep := companionIdealReductionIter_succ_of_continues hinv T (principalizationOfDimLe T A) s₀ m hc
        have hlt : maxOrderNonMonomialOnOrderLocus T (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s₀ (m + 1)) <
            maxOrderNonMonomialOnOrderLocus T (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s₀ m) := by
          rw [hstep]
          exact maxOrderNonMonomialOnOrderLocus_extendByCompanionIdeal_lt hG hinv hspec hT hdim
            (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s₀ m) hc
        have hih := ih hc
        omega
      · exfalso
        rw [companionIdealReductionIter_succ_of_not_continues hinv T (principalizationOfDimLe T A) s₀ m hc] at h
        exact hc h

theorem hasCenter_companionIdealReductionIter (f : ℕ) (i : ℕ)
    (hi : i <
      (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f).length) :
    HasPrincipalizationCenter T.mult
      ((companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f).dataAt i) := by
  revert i
  induction f with
  | zero =>
      intro i hi
      rw [companionIdealReductionIter_zero] at hi ⊢
      exact hasCenter_nonMonomialOrderReduction hG hinv hspec hT hdim i hi
  | succ m ih =>
      intro i hi
      by_cases hc : CompanionIdealReductionContinues T
          (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)
      · have hcont0 : CompanionIdealReductionContinues T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) :=
          companionIdealReductionContinues_of_continues_iter hinv T (principalizationOfDimLe T A)
            (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m hc
        have hm : 2 ≤ T.mult :=
          two_le_mult_of_continues_after_nonMonomialOrderReduction hG hinv hspec hT hdim hcont0
        rw [companionIdealReductionIter_succ_of_continues hinv T (principalizationOfDimLe T A)
          (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m hc] at hi ⊢
        exact hasCenter_extendByCompanionIdeal hG hinv hspec hT hdim
          (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m) hc hm
          (fun j hj => ih j hj) i hi
      · rw [companionIdealReductionIter_succ_of_not_continues hinv T (principalizationOfDimLe T A)
          (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m hc] at hi ⊢
        exact ih i hi

theorem not_companionIdealReductionContinues_companionIdealReduction :
    ¬ CompanionIdealReductionContinues T (companionIdealReduction hinv T (principalizationOfDimLe T A)) := by
  intro h
  rw [companionIdealReduction_eq hinv T (principalizationOfDimLe T A)] at h
  have hle := maxOrderNonMonomialOnOrderLocus_iter_add_le hG hinv hspec hT hdim
    (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) (maxOrderNonMonomialOnOrderLocus T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) + 1) h
  omega

theorem hasCenter_companionIdealReduction (i : ℕ)
    (hi : i < (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) :
    HasPrincipalizationCenter T.mult ((companionIdealReduction hinv T (principalizationOfDimLe T A)).dataAt i) := by
  rw [companionIdealReduction_eq hinv T (principalizationOfDimLe T A)] at hi ⊢
  exact hasCenter_companionIdealReductionIter hG hinv hspec hT hdim
    (maxOrderNonMonomialOnOrderLocus T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) + 1) i hi

theorem orderAt_lastNonMonomialPart_companionIdealReduction_eq_zero :
    ∀ x ∈ orderAtLeastLocus ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal
        (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult,
      orderAt (lastNonMonomialPart T (companionIdealReduction hinv T (principalizationOfDimLe T A))) x = 0 := by
  have hnc := not_companionIdealReductionContinues_companionIdealReduction hG hinv hspec hT hdim
  have hzero : maxOrderNonMonomialOnOrderLocus T (companionIdealReduction hinv T (principalizationOfDimLe T A)) = 0 := by
    by_contra hne
    exact hnc ((companionIdealReductionContinues_iff T (companionIdealReduction hinv T (principalizationOfDimLe T A))).mpr
      (Nat.one_le_iff_ne_zero.mpr hne))
  obtain ⟨Bd, hBd⟩ := exists_orderAt_lastNonMonomialPart_le hG hT (companionIdealReduction hinv T (principalizationOfDimLe T A))
  have hpi : maxOrderNonMonomialOnOrderLocus T (companionIdealReduction hinv T (principalizationOfDimLe T A)) =
      maxOrderOn (lastNonMonomialPart T (companionIdealReduction hinv T (principalizationOfDimLe T A)))
        (orderAtLeastLocus ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal
          (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult) := rfl
  rw [hpi] at hzero
  exact (maxOrderOn_eq_zero_iff (lastNonMonomialPart T (companionIdealReduction hinv T (principalizationOfDimLe T A))) hBd
    (orderAtLeastLocus ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal
      (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult)).mp hzero


end

private theorem foldr_ofFn_mul_eq_prod_consolidated453 {X : Scheme.{u}} (m : ℕ)
    (g : Fin m → X.IdealSheafData) :
    (List.ofFn g).foldr (· * ·) ⊤ = ∏ i, g i := by
  induction m with
  | zero =>
      have h1 : List.ofFn g = [] := by simp
      rw [h1, List.foldr_nil, Fin.prod_univ_zero]
      exact Scheme.IdealSheafData.one_eq_top.symm
  | succ p ih =>
      rw [List.ofFn_succ, List.foldr_cons, ih, Fin.prod_univ_succ]

theorem isLocallyMonomialTriple_tripleAtLength_companionIdealReduction (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    {n : ℕ} {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) :
    MonomialCenter.IsLocallyMonomialTriple
      (tripleAtLength T (companionIdealReduction hinv T (principalizationOfDimLe T A))
        ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult) := by
  refine ⟨isAdmissible_tripleAtLength hG hT (companionIdealReduction hinv T (principalizationOfDimLe T A)), ?_⟩
  intro x hx
  have hx' : x ∈ orderAtLeastLocus ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal
      (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult := hx
  have hzero := orderAt_lastNonMonomialPart_companionIdealReduction_eq_zero hG hinv hspec hT hdim x hx'
  obtain ⟨U, e, hxU, hU⟩ :=
    (isMonomialSplitting_lastNonMonomialPart hG hT
      (companionIdealReduction hinv T (principalizationOfDimLe T A))).exists_comap_eq_prod_pow_of_orderAt_eq_zero hzero
  exact ⟨U, hxU, e, hU.trans (foldr_ofFn_mul_eq_prod_consolidated453 _ _).symm⟩


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.ControlledTransformOrderBound
section


section

theorem orderAt_controlledTransform_le_of_orderAt_eq_on_center :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ (J : T.scheme.IdealSheafData) (c : ℕ),
                (∀ x ∈ Z.support, orderAt J x = (c : ℕ∞)) →
                  ∀ (J' : X'.IdealSheafData),
                    Blowup.exceptionalIdeal π Z ^ c * J' = J.comap π →
                      ∀ x' ∈ (Blowup.exceptionalIdeal π Z).support, orderAt J' x' ≤ (c : ℕ∞) := by
  intro T hT Z hZsm hZsnc X' π hπ J c hJ J' hJ' x' hx'
  have : CharZero T.base := hT.charZero
  have : Smooth T.structMap := hT.smooth
  have hN : IsNoetherian T.scheme := hT.isNoetherian
  have hlocNoeth : IsLocallyNoetherian T.scheme := inferInstance
  have hLN' : IsLocallyNoetherian X' :=
    isLocallyNoetherian_of_isBlowupAlongIdealSheaf π Z hπ
  have hsub : (Z.support : Set ↥T.scheme) ⊆ orderAtLeastLocus J c := by
    intro x hx
    exact (mem_orderAtLeastLocus_iff J c x).2 (hJ x hx).ge
  have hI : J ≤ Z ^ c :=
    le_pow_of_hasStrictNormalCrossingsWith T.structMap Z J T.boundary hZsnc c hsub
  have hJ'eq : J' = controlledTransform π Z J c hπ hI :=
    eq_controlledTransform_of_mul_eq_comap π Z J c hπ hI J' hJ'
  rw [hJ'eq]
  refine orderAt_controlledTransform_le_of_orderAt_image_le T.base T.structMap π Z T.boundary
    hZsnc hπ J c hI x' ?_
  have h1 : π x' ∈ (Z.support : Set ↥T.scheme) :=
    AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1
      (by rw [← Blowup.exceptionalIdeal_eq_comap π Z]; exact hx')
  exact le_of_eq (hJ _ h1)

structure StrictTransformAndMonomialCaseHypotheses : Prop where
  strictTransform_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary,
                ∀ C' : Set ↥X',
                  IsIrreducibleComponentOf C' ((Blowup.strictTransform π Z D).support : Set ↥X') →
                    ∃ (ξ' : ↥X') (C : Set ↥T.scheme),
                      C' = closure ({ξ'} : Set ↥X') ∧
                        ξ' ∉ (Blowup.exceptionalIdeal π Z).support ∧
                          IsIrreducibleComponentOf C (D.support : Set ↥T.scheme) ∧
                            ¬ C ⊆ (Z.support : Set ↥T.scheme) ∧
                              C = closure ({π ξ'} : Set ↥T.scheme)
  monomial : MonomialCaseHypotheses.{u}

theorem OrderReductionHypotheses.of_strictTransformHypotheses (h : StrictTransformAndMonomialCaseHypotheses.{u}) :
    OrderReductionHypotheses.{u} where
  controlledTransform_orderAt_le := orderAt_controlledTransform_le_of_orderAt_eq_on_center
  strictTransform_components := h.strictTransform_components
  monomial := h.monomial


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialCenterHypotheses
section



namespace MonomialCenterCase

structure MonomialCenterHypotheses : Prop where
  center_smooth :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)),
            Smooth
              ((componentUnionIdeal T.boundary J 𝒞 hop).subschemeι ≫ T.structMap)
  center_snc :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)),
            HasStrictNormalCrossingsWith T.structMap (componentUnionIdeal T.boundary J 𝒞 hop) T.boundary
  blowup_total_transform :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary,
                ∀ x' : ↥X',
                  ∃ (U' : X'.Opens) (ε : ℕ),
                    x' ∈ U' ∧ (ε = 0 ∨ ε = 1) ∧
                      (ε = 1 ↔ ∃ V : T.scheme.Opens, π x' ∈ V ∧
                        (Z.support : Set ↥T.scheme) ∩ (V : Set ↥T.scheme)
                          ⊆ (D.support : Set ↥T.scheme)) ∧
                      (D.comap π).comap U'.ι =
                        (Blowup.strictTransform π Z D).comap U'.ι *
                          (Blowup.exceptionalIdeal π Z).comap U'.ι ^ ε
  components_subset_divisor_iff :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ C ∈ intersectionComponents T.boundary J,
          ∀ i : Fin T.boundary.length,
            C ⊆ ((T.boundary.get i).support : Set ↥T.scheme) ↔ i ∈ J
  transformed_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J₀ : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J₀,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J₀).subschemeι ⁻¹' ⋃₀ 𝒞))
            (X' : Scheme.{u}) (π : X' ⟶ T.scheme),
            Blowup.IsBlowupAlongIdealSheaf π (componentUnionIdeal T.boundary J₀ 𝒞 hop) →
              ∀ (J : Finset (Fin T.boundary.length)),
                ∀ C' ∈ intersectionComponents
                    (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
                    (Finset.image
                      (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary) J),
                  ∀ ξ' : ↥X', IsGenericPoint ξ' C' →
                    ξ' ∉ (Blowup.exceptionalIdeal π
                        (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support ∧
                      ∃ C ∈ intersectionComponents T.boundary J,
                        C ∉ 𝒞 ∧
                          C' = closure (⇑π ⁻¹' C \
                              ((Blowup.exceptionalIdeal π
                                (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support :
                                  Set ↥X')) ∧
                            ∀ ξ : ↥T.scheme, IsGenericPoint ξ C → π ξ' = ξ

theorem monomialCaseHypotheses_of_monomialCenterHypotheses (h : MonomialCenterHypotheses.{u}) : MonomialCaseHypotheses.{u} where
  card_lt_dim := MonomialCodimension.card_lt_krullDimSucc_of_nonempty
  center_smooth := h.center_smooth
  center_snc := h.center_snc
  blowup_total_transform := h.blowup_total_transform
  components_subset_divisor_iff := h.components_subset_divisor_iff
  transformed_components := h.transformed_components
  stratum_smooth := MonomialChart.smooth_intersectionIdeal_subscheme
  orderAt_comap_off_exceptional := fun T hT X' π Z hπ x' hx' A =>
    orderAt_comap_eq_of_notMem_exceptionalIdeal T hT Z X' π hπ x' hx' A
  orderAt_boundary_eq_one := MonomialChart.orderAt_boundary_eq_one

end MonomialCenterCase

namespace StrictTransformCase

structure StrictTransformHypotheses : Prop extends MonomialCenterCase.MonomialCenterHypotheses.{u} where
  strictTransform_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary,
                ∀ C' : Set ↥X',
                  IsIrreducibleComponentOf C' ((Blowup.strictTransform π Z D).support : Set ↥X') →
                    ∃ (ξ' : ↥X') (C : Set ↥T.scheme),
                      C' = closure ({ξ'} : Set ↥X') ∧
                        ξ' ∉ (Blowup.exceptionalIdeal π Z).support ∧
                          IsIrreducibleComponentOf C (D.support : Set ↥T.scheme) ∧
                            ¬ C ⊆ (Z.support : Set ↥T.scheme) ∧
                              C = closure ({π ξ'} : Set ↥T.scheme)

theorem strictTransformHypotheses_of_residualHypotheses (h : StrictTransformHypotheses.{u}) : StrictTransformAndMonomialCaseHypotheses.{u} where
  strictTransform_components := h.strictTransform_components
  monomial := MonomialCenterCase.monomialCaseHypotheses_of_monomialCenterHypotheses h.toMonomialCenterHypotheses

end StrictTransformCase

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionResolution
section


section

structure MonomialPrincipalizationHypotheses (hinv : ComapIsoInvariance.{u}) : Prop where
  cert : ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
    ∀ i < (monomialPrincipalization hinv T).length,
      PrincipalizationCertificate ((monomialPrincipalization hinv T).schemeAt i)
        ((monomialPrincipalization hinv T).projectionToSpec i)
        ((monomialPrincipalization hinv T).ideal i) T.mult
        ((monomialPrincipalization hinv T).boundaryLocus i)
        ((monomialPrincipalization hinv T).center i)
  center_nonempty : ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
    ∀ i < (monomialPrincipalization hinv T).length,
      (((monomialPrincipalization hinv T).center i).support :
        Set ↥((monomialPrincipalization hinv T).schemeAt i)).Nonempty
  resolves : ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
    MarkedSequenceOfBlowups.IsResolution (monomialPrincipalization hinv T)
  trivial_of_coSupport_empty : ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
    orderAtLeastLocus T.ideal T.mult = ∅ → (monomialPrincipalization hinv T).length = 0

theorem orderAtLeastLocus_comap_eqToHom_eq_empty {A B : Scheme.{u}} (h : A = B) (J : B.IdealSheafData)
    (c : ℕ) (hJ : orderAtLeastLocus J c = ∅) : orderAtLeastLocus (J.comap (eqToHom h)) c = ∅ := by
  rw [orderAtLeastLocus_comap_eqToHom, hJ, Set.preimage_empty]

section
variable (hinv : ComapIsoInvariance.{u})
include hinv

private theorem orderAtLeastLocus_eq_empty_of_comap_iso_hom_eq_empty_consolidated467 {A B : Scheme.{u}}
    (e : A ≅ B) (J : B.IdealSheafData) (c : ℕ)
    (h : orderAtLeastLocus (J.comap e.hom) c = ∅) : orderAtLeastLocus J c = ∅ := by
  rw [hinv.coSupport_comap] at h
  have hb : ∀ y : ↥B, (e.hom) ((e.inv) y) = y := by
    intro y
    calc (e.hom) ((e.inv) y) = (e.inv ≫ e.hom) y := by simp
      _ = (𝟙 B) y := by rw [e.inv_hom_id]
      _ = y := by simp
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨y, hy⟩
  have hmem : (e.inv) y ∈ ⇑e.hom ⁻¹' orderAtLeastLocus J c := by
    have hby : (e.hom) ((e.inv) y) = y := hb y
    simp only [Set.mem_preimage, hby]
    exact hy
  rw [h] at hmem
  simp at hmem

theorem orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty (T : MarkedIdealWithBoundary.{u}) (f : PrincipalizationAssignment.{u}) (h : orderAtLeastLocus T.ideal T.mult = ∅) :
    (orderReductionSeq hinv T (principalizationOfDimLe T f)).length = 0 := by
  simp [orderReductionSeq, h, emptyMarkedSequenceOfBlowups_length]


end

abbrev orderReductionMonomialTriple (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (f : PrincipalizationAssignment.{u}) : MarkedIdealWithBoundary.{u} :=
  tripleAtLength T (companionIdealReduction hinv T (principalizationOfDimLe T f))
    ((companionIdealReduction hinv T (principalizationOfDimLe T f)).ideal (companionIdealReduction hinv T (principalizationOfDimLe T f)).length) T.mult

abbrev orderReductionMonomialSequence (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (f : PrincipalizationAssignment.{u}) :
    MarkedBlowupSequenceData
      ((companionIdealReduction hinv T (principalizationOfDimLe T f)).proj (companionIdealReduction hinv T (principalizationOfDimLe T f)).length ≫ T.structMap)
      ((companionIdealReduction hinv T (principalizationOfDimLe T f)).ideal (companionIdealReduction hinv T (principalizationOfDimLe T f)).length) T.mult
      ((companionIdealReduction hinv T (principalizationOfDimLe T f)).boundary (companionIdealReduction hinv T (principalizationOfDimLe T f)).length) :=
  MarkedBlowupSequenceData.ofMarkedSequence (monomialPrincipalization hinv (orderReductionMonomialTriple hinv T f))

theorem orderReductionData_eq_append (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (f : PrincipalizationAssignment.{u}) :
    orderReductionData hinv T (principalizationOfDimLe T f) =
      (companionIdealReduction hinv T (principalizationOfDimLe T f)).append (orderReductionMonomialSequence hinv T f) hinv :=
  orderReductionData_eq hinv T (principalizationOfDimLe T f)

section
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (s : MarkedSequenceOfBlowups p I m E) (i : ℕ)

private theorem hasPrincipalizationCenter_ofMarkedSequence_consolidated467 (hne : (((s.center i).support : Set ↥(s.schemeAt i))).Nonempty)
    (hc : PrincipalizationCertificate (s.schemeAt i) (s.projectionToSpec i) (s.ideal i) m (s.boundaryLocus i) (s.center i)) :
    HasPrincipalizationCenter m ((MarkedBlowupSequenceData.ofMarkedSequence s).dataAt i) := by
  refine ⟨?_, ?_⟩
  · exact hne
  · rw [MarkedBlowupSequenceData.boundarySupport_dataAt]
    exact hc

private theorem lt_length_of_lt_ofMarkedSequence_length_consolidated467 (hi : i < (MarkedBlowupSequenceData.ofMarkedSequence s).length) : i < s.length := by
  rwa [MarkedBlowupSequenceData.ofMarkedSequence_length] at hi


end

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (hmon : MonomialPrincipalizationHypotheses hinv) {n : ℕ} {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (i : ℕ)
include hG hmon hspec hT hdim

private theorem hasCenter_orderReductionData_consolidated467 (hi : i < (orderReductionData hinv T (principalizationOfDimLe T A)).length) :
    HasPrincipalizationCenter T.mult ((orderReductionData hinv T (principalizationOfDimLe T A)).dataAt i) := by
  have hlocMon := isLocallyMonomialTriple_tripleAtLength_companionIdealReduction hG hinv hspec hT hdim
  rw [orderReductionData_eq hinv T (principalizationOfDimLe T A)] at hi ⊢
  refine MarkedBlowupSequenceData.append_dataAt_of_forall _ _ hinv (fun D => HasPrincipalizationCenter T.mult D)
    (isInvariantUnderIso_hasPrincipalizationCenter hG.maxContactTransport T.mult)
    (hasCenter_companionIdealReduction hG hinv hspec hT hdim) ?_ i hi
  intro j hj
  have hj' := lt_length_of_lt_ofMarkedSequence_length_consolidated467
    (monomialPrincipalization hinv
      (tripleAtLength T (companionIdealReduction hinv T (principalizationOfDimLe T A))
        ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult))
    j hj
  exact hasPrincipalizationCenter_ofMarkedSequence_consolidated467
    (monomialPrincipalization hinv
      (tripleAtLength T (companionIdealReduction hinv T (principalizationOfDimLe T A))
        ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult))
    j
    (hmon.center_nonempty _ hlocMon j hj')
    (hmon.cert _ hlocMon j hj')

theorem center_support_nonempty_orderReductionSeq (hi : i < (orderReductionSeq hinv T (principalizationOfDimLe T A)).length) :
    (((orderReductionSeq hinv T (principalizationOfDimLe T A)).center i).support :
      Set ↥((orderReductionSeq hinv T (principalizationOfDimLe T A)).schemeAt i)).Nonempty := by
  by_cases hne : (orderAtLeastLocus T.ideal T.mult).Nonempty
  · rw [orderReductionSeq_eq_of_nonempty hinv T (principalizationOfDimLe T A) hne] at hi ⊢
    exact (MarkedBlowupSequenceData.nonempty_center_and_certificate_of_hasPrincipalizationCenter (orderReductionData hinv T (principalizationOfDimLe T A)) T.mult
      (hasCenter_orderReductionData_consolidated467 hG hinv hmon hspec hT hdim)).1 i hi
  · exact absurd (orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T A
      (Set.not_nonempty_iff_eq_empty.mp hne)) (by omega)

theorem certificate_orderReductionSeq (hi : i < (orderReductionSeq hinv T (principalizationOfDimLe T A)).length) :
    PrincipalizationCertificate ((orderReductionSeq hinv T (principalizationOfDimLe T A)).schemeAt i)
      ((orderReductionSeq hinv T (principalizationOfDimLe T A)).projectionToSpec i)
      ((orderReductionSeq hinv T (principalizationOfDimLe T A)).ideal i) T.mult
      ((orderReductionSeq hinv T (principalizationOfDimLe T A)).boundaryLocus i)
      ((orderReductionSeq hinv T (principalizationOfDimLe T A)).center i) := by
  by_cases hne : (orderAtLeastLocus T.ideal T.mult).Nonempty
  · rw [orderReductionSeq_eq_of_nonempty hinv T (principalizationOfDimLe T A) hne] at hi ⊢
    exact (MarkedBlowupSequenceData.nonempty_center_and_certificate_of_hasPrincipalizationCenter (orderReductionData hinv T (principalizationOfDimLe T A)) T.mult
      (hasCenter_orderReductionData_consolidated467 hG hinv hmon hspec hT hdim)).2 i hi
  · exact absurd (orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T A
      (Set.not_nonempty_iff_eq_empty.mp hne)) (by omega)


end

section
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

private theorem orderAtLeastLocus_ideal_congr_consolidated467 (d : MarkedBlowupSequenceData p I m E) (i j : ℕ) (h : i = j) (c : ℕ)
    (hh : orderAtLeastLocus (d.ideal i) c = ∅) : orderAtLeastLocus (d.ideal j) c = ∅ := by
  subst h
  exact hh

private theorem orderAtLeastLocus_ofMarkedSequence_last_eq_empty_consolidated467 (s : MarkedSequenceOfBlowups p I m E) (c : ℕ) (h : orderAtLeastLocus (s.ideal s.length) c = ∅) :
    orderAtLeastLocus ((MarkedBlowupSequenceData.ofMarkedSequence s).ideal
      (MarkedBlowupSequenceData.ofMarkedSequence s).length) c = ∅ := by
  rw [MarkedBlowupSequenceData.ofMarkedSequence_length, MarkedBlowupSequenceData.ofMarkedSequence_ideal]
  exact h

private theorem orderAtLeastLocus_append_last_eq_empty_consolidated467 (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (ht : orderAtLeastLocus (t.ideal t.length) m = ∅) :
    orderAtLeastLocus ((s.append t hinv).ideal (s.append t hinv).length) m = ∅ := by
  have hlen : (s.append t hinv).length = s.length + t.length :=
    MarkedBlowupSequenceData.append_length s t hinv
  rcases Nat.eq_zero_or_pos t.length with h0 | hpos
  · refine orderAtLeastLocus_ideal_congr_consolidated467 (s.append t hinv) s.length (s.append t hinv).length
      (by omega) m ?_
    rw [MarkedBlowupSequenceData.append_ideal, MarkedBlowupSequenceData.appendIdeal_of_le_length s t (le_refl s.length)]
    refine orderAtLeastLocus_comap_eqToHom_eq_empty _ _ _ ?_
    have ht0 : orderAtLeastLocus (t.ideal 0) m = ∅ :=
      orderAtLeastLocus_ideal_congr_consolidated467 t t.length 0 h0 m ht
    rw [t.ideal_zero] at ht0
    exact orderAtLeastLocus_eq_empty_of_comap_iso_hom_eq_empty_consolidated467 hinv t.isoZero _ _ ht0
  · refine orderAtLeastLocus_ideal_congr_consolidated467 (s.append t hinv) (s.length + t.length)
      (s.append t hinv).length hlen.symm m ?_
    rw [MarkedBlowupSequenceData.append_ideal_length_add_length s t hinv hpos]
    exact orderAtLeastLocus_comap_eqToHom_eq_empty _ _ _ ht


end

theorem isResolution_orderReductionSeq (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (hmon : MonomialPrincipalizationHypotheses hinv) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) :
    MarkedSequenceOfBlowups.IsResolution (orderReductionSeq hinv T (principalizationOfDimLe T A)) := by
  by_cases hne : (orderAtLeastLocus T.ideal T.mult).Nonempty
  · have hlocMon := isLocallyMonomialTriple_tripleAtLength_companionIdealReduction hG hinv hspec hT hdim
    have hres := hmon.resolves _ hlocMon
    rw [MarkedSequenceOfBlowups.isResolution_iff, MarkedSequenceOfBlowups.lastIdeal_eq] at hres
    rw [orderReductionSeq_eq_of_nonempty hinv T (principalizationOfDimLe T A) hne, MarkedSequenceOfBlowups.isResolution_iff,
      MarkedSequenceOfBlowups.lastIdeal_eq, MarkedBlowupSequenceData.toMarkedSequence_length,
      MarkedBlowupSequenceData.toMarkedSequence_ideal, orderReductionData_eq hinv T (principalizationOfDimLe T A)]
    exact orderAtLeastLocus_append_last_eq_empty_consolidated467 hinv _ _ (orderAtLeastLocus_ofMarkedSequence_last_eq_empty_consolidated467 _ T.mult hres)
  · rw [MarkedSequenceOfBlowups.isResolution_iff, MarkedSequenceOfBlowups.lastIdeal_eq,
      orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T A
        (Set.not_nonempty_iff_eq_empty.mp hne),
      MarkedSequenceOfBlowups.ideal_zero, hinv.coSupport_comap,
      Set.not_nonempty_iff_eq_empty.mp hne, Set.preimage_empty]


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.RecursivePrincipalizationPullback
section

open CategoryTheory.Limits

section

private def markedPullbackSquareId_consolidated466 {T : MarkedIdealWithBoundary.{u}} {Y : Scheme.{u}} (g : Y ⟶ T.scheme)
    (hT : T.IsAdmissible) : MarkedPullbackSquare T g where
  baseScheme := T.scheme
  topScheme := Y
  bottom := 𝟙 T.scheme
  structMap := T.structMap
  ideal := T.ideal
  mult := T.mult
  boundary := T.boundary
  left := g
  top := 𝟙 Y
  bottom_structMap := Category.id_comp T.structMap
  dim_le := le_rfl
  isPullback := (IsPullback.of_horiz_isIso ⟨by simp⟩).flip
  valid := hT

section
variable (hinv : ComapIsoInvariance.{u}) (F : PrincipalizationAssignment.{u}) (n : ℕ) (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) {Y : Scheme.{u}} (g : Y ⟶ T.scheme) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (hbc : BaseChangeCompatible hinv F n T g k' q)
include hT hbc

theorem orderAt_comap_of_baseChangeCompatible (A : T.scheme.IdealSheafData) (y : ↥Y) :
    orderAt (A.comap g) y = orderAt A (g.base y) :=
  MarkedPullbackSquare.orderAt_comap_verticalMap (markedPullbackSquareId_consolidated466 g hT) hT hbc.order A y

theorem orderAtLeastLocus_comap_eq_empty_of_baseChangeCompatible (h : orderAtLeastLocus T.ideal T.mult = ∅) :
    orderAtLeastLocus (T.ideal.comap g) T.mult = ∅ := by
  refine Set.eq_empty_of_subset_empty ?_
  intro y hy
  have hy' := (mem_orderAtLeastLocus_iff (T.ideal.comap g) T.mult y).1 hy
  rw [orderAt_comap_of_baseChangeCompatible hinv F n T hT g k' q hbc T.ideal y] at hy'
  have hmem := (mem_orderAtLeastLocus_iff T.ideal T.mult _).2 hy'
  rw [h] at hmem
  simp only [Set.mem_empty_iff_false] at hmem


end

private theorem transformAt_eq_mk_consolidated466 (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) :
    T.transformAt s i =
      MarkedIdealWithBoundary.mk T.base (s.schemeAt i) (s.projectionToBase i ≫ T.structMap) (s.ideal i) T.mult
        (s.boundary i) := rfl

section
variable (hmg : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
include hmg hT

theorem MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim :
    krullDimSucc (s.obj s.length) ≤ T.krullDimSucc :=
  hmg.level_schemeDim_le T hT s.toMarkedSequenceOfBlowups s.length le_rfl

theorem MonomialGeometryHypotheses.isAdmissible_tripleAtLength :
    (MarkedIdealWithBoundary.mk T.base (s.obj s.length) (s.proj s.length ≫ T.structMap)
      (s.ideal s.length) T.mult (s.boundary s.length)).IsAdmissible := by
  have h := hmg.level_valid T hT s.toMarkedSequenceOfBlowups s.length le_rfl
  rw [transformAt_eq_mk_consolidated466 T s.toMarkedSequenceOfBlowups s.length,
    toMarkedSequence_projectionToBase s s.length] at h
  exact h


end

private theorem isAdmissible_mk_congr_consolidated466 {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I₁ I₂ : X.IdealSheafData} {m₁ m₂ : ℕ}
    {E : List X.IdealSheafData} (hI : I₁ = I₂) (hm : m₁ = m₂)
    (h : (MarkedIdealWithBoundary.mk k X p I₁ m₁ E).IsAdmissible) : (MarkedIdealWithBoundary.mk k X p I₂ m₂ E).IsAdmissible := by
  subst hI
  subst hm
  exact h

def SequenceOfBlowupsPullback.toMarkedPullbackSquare {T T' : MarkedIdealWithBoundary.{u}} (g : T'.scheme ⟶ T.scheme)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hdim : krullDimSucc (s.obj s.length) ≤ T.krullDimSucc)
    (hval : (MarkedIdealWithBoundary.mk T.base (s.obj s.length) (s.proj s.length ≫ T.structMap)
      (s.ideal s.length) T.mult (s.boundary s.length)).IsAdmissible) :
    MarkedPullbackSquare T g where
  baseScheme := s.obj s.length
  topScheme := s'.obj s'.length
  bottom := s.proj s.length
  structMap := s.proj s.length ≫ T.structMap
  ideal := s.ideal s.length
  mult := T.mult
  boundary := s.boundary s.length
  left := c.lastMap
  top := s'.proj s'.length
  bottom_structMap := rfl
  dim_le := hdim
  isPullback := by
    have h := c.isPullback_lastMap
    rwa [toMarkedSequence_projectionToBase, toMarkedSequence_projectionToBase] at h
  valid := hval

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (n : ℕ) (A : PrincipalizationAssignment.{u}) (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme) (hT : T.IsAdmissible) (hT' : T'.IsAdmissible)
include hG hT hT'

theorem lastNonMonomialPart_eq_comap_lastMap_of_pullback (_hdim : T.krullDimSucc ≤ n) (_hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (_hideal : T'.ideal = T.ideal.comap g)
    (_hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap)) :
    lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap := by
  have hmg := hG.monomialInputs
  have hdimS := MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T hT s
  have hvalS := MonomialGeometryHypotheses.isAdmissible_tripleAtLength hmg T hT s
  have hvalS'0 := MonomialGeometryHypotheses.isAdmissible_tripleAtLength hmg T' hT' s'
  have hvalS' := isAdmissible_mk_congr_consolidated466 hlastIdeal hmult hvalS'0
  have hmain := hbc.nonMonomial (SequenceOfBlowupsPullback.toMarkedPullbackSquare g s s' c hdimS hvalS)
    (s'.boundary s'.length) hsameBoundary.symm hvalS'
  have h0 : lastNonMonomialPart T' s' = nonMonomialPart (s'.boundary s'.length) (s'.ideal s'.length) :=
    rfl
  have h1 : lastNonMonomialPart T s = nonMonomialPart (s.boundary s.length) (s.ideal s.length) := rfl
  rw [h0, h1, hlastIdeal]
  exact hmain

theorem maxOrderNonMonomial_le_of_pullback (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap)) :
    maxOrderNonMonomial T' s' ≤ maxOrderNonMonomial T s := by
  have key : lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap :=
    lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
      hbdry hbc s s' c hlastIdeal hsameBoundary
  have hvalid : (MarkedIdealWithBoundary.mk T.base (s.obj s.length) (s.toMarkedSequenceOfBlowups.projectionToSpec s.length)
      (s.ideal s.length) T.mult (s.boundary s.length)).IsAdmissible :=
    hG.monomialInputs.level_valid T hT s.toMarkedSequenceOfBlowups s.length le_rfl
  have hord : ∀ (J : (s.obj s.length).IdealSheafData) (y : ↥(s'.obj s'.length)),
      orderAt (J.comap c.lastMap) y = orderAt J (c.lastMap.base y) :=
    hbc.order (s.obj s.length) (s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase s.length)
      (s.toMarkedSequenceOfBlowups.projectionToSpec s.length) (s.ideal s.length) (s.boundary s.length) hvalid
      (MarkedSequenceOfBlowups.projectionToSpec_eq s.toMarkedSequenceOfBlowups s.length).symm
      (s'.obj s'.length) c.lastMap (s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase s'.length)
      c.isPullback_lastMap
  have hmain : ∀ y : ↥(s'.obj s'.length),
      orderAt (lastNonMonomialPart T' s') y ≤ (maxOrderNonMonomial T s : ℕ∞) := by
    intro y
    have h1 : orderAt (lastNonMonomialPart T' s') y
        = orderAt (lastNonMonomialPart T s) (c.lastMap.base y) :=
      (congrArg (fun I : (s'.obj s'.length).IdealSheafData => orderAt I y) key).trans
        (hord (lastNonMonomialPart T s) y)
    exact le_of_eq_of_le h1
      (orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s (c.lastMap.base y))
  show sSup {m : ℕ | ∃ x : ↥(s'.obj s'.length), (m : ℕ∞) ≤ orderAt (lastNonMonomialPart T' s') x}
      ≤ maxOrderNonMonomial T s
  refine csSup_le' ?_
  intro m hm
  obtain ⟨y, hy⟩ := hm
  have hcast : (m : ℕ∞) ≤ (maxOrderNonMonomial T s : ℕ∞) := hy.trans (hmain y)
  exact_mod_cast hcast


end

private theorem maxOrderOn_le_of_forall_consolidated466 {X : Scheme.{u}} (N : X.IdealSheafData) (S : Set ↥X)
    (K : ℕ) (h : ∀ m : ℕ, ∀ x ∈ S, (m : ℕ∞) ≤ orderAt N x → m ≤ K) :
    maxOrderOn N S ≤ K := by
  unfold maxOrderOn
  refine csSup_le' ?_
  intro m hmem
  obtain ⟨x, hx, hmx⟩ := hmem
  exact h m x hx hmx

theorem maxOrderNonMonomialOnOrderLocus_le_of_pullback (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A : PrincipalizationAssignment.{u}) (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap)) :
    maxOrderNonMonomialOnOrderLocus T' s' ≤ maxOrderNonMonomialOnOrderLocus T s := by
  have hmg := hG.monomialInputs
  have hdimS := MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T hT s
  have hvalS := MonomialGeometryHypotheses.isAdmissible_tripleAtLength hmg T hT s
  have hordLast : ∀ (Aid : (s.obj s.length).IdealSheafData) (y : ↥(s'.obj s'.length)),
      orderAt (Aid.comap c.lastMap) y = orderAt Aid (c.lastMap.base y) :=
    fun Aid y =>
      MarkedPullbackSquare.orderAt_comap_verticalMap (SequenceOfBlowupsPullback.toMarkedPullbackSquare g s s' c hdimS hvalS) hT
        hbc.order Aid y
  have hnonMon : lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap :=
    lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
      hbdry hbc s s' c hlastIdeal hsameBoundary
  have hmain : maxOrderNonMonomialOnOrderLocus T' s' =
      maxOrderOn (lastNonMonomialPart T' s') (orderAtLeastLocus (s'.ideal s'.length) T'.mult) := rfl
  rw [hmain]
  refine maxOrderOn_le_of_forall_consolidated466 _ _ _ ?_
  intro m x' hx' hm
  have hEq1 : orderAt (s'.ideal s'.length) x' = orderAt (s.ideal s.length) (c.lastMap.base x') :=
    (congrArg (fun I => orderAt I x') hlastIdeal).trans (hordLast (s.ideal s.length) x')
  have hEq2 : orderAt (lastNonMonomialPart T' s') x'
      = orderAt (lastNonMonomialPart T s) (c.lastMap.base x') :=
    (congrArg (fun I => orderAt I x') hnonMon).trans (hordLast (lastNonMonomialPart T s) x')
  have h1 : ((T'.mult : ℕ) : ℕ∞) ≤ orderAt (s'.ideal s'.length) x' :=
    (mem_orderAtLeastLocus_iff _ _ _).1 hx'
  have hmult' : ((T.mult : ℕ) : ℕ∞) = ((T'.mult : ℕ) : ℕ∞) := by rw [hmult]
  have h3 : ((T.mult : ℕ) : ℕ∞) ≤ orderAt (s.ideal s.length) (c.lastMap.base x') :=
    hmult'.trans_le (h1.trans_eq hEq1)
  have hxmem : c.lastMap.base x' ∈ orderAtLeastLocus (s.ideal s.length) T.mult :=
    (mem_orderAtLeastLocus_iff _ _ _).2 h3
  have hle := orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT s (c.lastMap.base x') hxmem
  have hfin : ((m : ℕ) : ℕ∞) ≤ ((maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) := (hm.trans_eq hEq2).trans hle
  exact_mod_cast hfin

private theorem orderAtLeastLocus_sSup_nonempty_consolidated466 {X : Scheme.{u}} (N : X.IdealSheafData)
    (x₀ : ↥X)
    (hbound : ∀ x : ↥X,
      orderAt N x ≤ ((sSup {m : ℕ | ∃ y : ↥X, (m : ℕ∞) ≤ orderAt N y} : ℕ) : ℕ∞)) :
    (orderAtLeastLocus N (sSup {m : ℕ | ∃ y : ↥X, (m : ℕ∞) ≤ orderAt N y})).Nonempty := by
  have hne : {m : ℕ | ∃ y : ↥X, (m : ℕ∞) ≤ orderAt N y}.Nonempty := by
    refine ⟨0, x₀, ?_⟩
    simp
  have hbdd : BddAbove {m : ℕ | ∃ y : ↥X, (m : ℕ∞) ≤ orderAt N y} := by
    refine ⟨sSup {m : ℕ | ∃ y : ↥X, (m : ℕ∞) ≤ orderAt N y}, ?_⟩
    intro m hm
    obtain ⟨y, hy⟩ := hm
    have h := hy.trans (hbound y)
    exact_mod_cast h
  obtain ⟨y, hy⟩ := Nat.sSup_mem hne hbdd
  exact ⟨y, (mem_orderAtLeastLocus_iff N _ y).2 hy⟩

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (n : ℕ) (A : PrincipalizationAssignment.{u}) (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme) (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n) (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g) (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g)) (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary) (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups) (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap) (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length) ((s.boundary s.length).map fun D => D.comap c.lastMap))
include hG hT hT' hdim hdim' hmult hideal hbdry hbc hlastIdeal hsameBoundary

theorem nonMonomialOrderReductionContinues_of_pullback (hcont : NonMonomialOrderReductionContinues T' s') : NonMonomialOrderReductionContinues T s := by
  have hle : maxOrderNonMonomial T' s' ≤ maxOrderNonMonomial T s :=
    maxOrderNonMonomial_le_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s'
      c hlastIdeal hsameBoundary
  unfold NonMonomialOrderReductionContinues at hcont ⊢
  obtain ⟨h1, h2⟩ := hcont
  obtain ⟨x', -⟩ := h2
  rw [hmult] at h1
  refine ⟨le_trans h1 hle, ?_⟩
  have hbound : ∀ x : ↥(s.obj s.length),
      orderAt (lastNonMonomialPart T s) x ≤ ((maxOrderNonMonomial T s : ℕ) : ℕ∞) :=
    fun x => orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
  exact orderAtLeastLocus_sSup_nonempty_consolidated466 (lastNonMonomialPart T s) (c.lastMap.base x') hbound

theorem companionIdealReductionContinues_of_pullback (hcont : CompanionIdealReductionContinues T' s') : CompanionIdealReductionContinues T s := by
  have hle : maxOrderNonMonomialOnOrderLocus T' s' ≤ maxOrderNonMonomialOnOrderLocus T s :=
    maxOrderNonMonomialOnOrderLocus_le_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc
      s s' c hlastIdeal hsameBoundary
  unfold CompanionIdealReductionContinues at hcont ⊢
  omega


end

section
variable {A B : Scheme.{u}} (f : A ⟶ B)

private theorem comap_pow_sup_pow_consolidated466 (N J : B.IdealSheafData)
    (a b : ℕ) : (N ^ a ⊔ J ^ b).comap f = (N.comap f) ^ a ⊔ (J.comap f) ^ b := by
  simp only [Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.comap_pow]

private theorem pow_sup_pow_eq_comap_pow_sup_pow_consolidated466 (N₁ N₂ : B.IdealSheafData) (M₁ M₂ : A.IdealSheafData) (a a' b b' : ℕ)
    (h₁ : M₁ = N₁.comap f) (h₂ : M₂ = N₂.comap f) (ha : a = a') (hb : b = b') :
    M₁ ^ a ⊔ M₂ ^ b = (N₁ ^ a' ⊔ N₂ ^ b').comap f := by
  subst h₁
  subst h₂
  subst ha
  subst hb
  exact (comap_pow_sup_pow_consolidated466 f N₁ N₂ _ _).symm


end

theorem companionIdeal_eq_comap_lastMap_of_pullback (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A : PrincipalizationAssignment.{u}) (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap))
    (hinveq : maxOrderNonMonomialOnOrderLocus T' s' = maxOrderNonMonomialOnOrderLocus T s) :
    companionIdeal T' s' = (companionIdeal T s).comap c.lastMap := by
  have hnonMon := lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim'
    hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary
  unfold companionIdeal
  exact pow_sup_pow_eq_comap_pow_sup_pow_consolidated466 _ _ _ _ _ T'.mult T.mult (maxOrderNonMonomialOnOrderLocus T' s') (maxOrderNonMonomialOnOrderLocus T s)
    hnonMon hlastIdeal hmult hinveq

section
variable (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) (rc : (S : MarkedIdealWithBoundary.{u}) → S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (J : (s.obj s.length).IdealSheafData) (μ : ℕ) (hd : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc)

private theorem appendRecursivePrincipalization_eq_self_of_eq_none_consolidated466 (h : markedDataOfSeq s J μ (rc (tripleAtLength T s J μ) hd) = none) :
    appendRecursivePrincipalization hinv T rc s J μ = s := by
  have h1 : appendRecursivePrincipalization hinv T rc s J μ = appendIfMarked hinv s J μ (rc (tripleAtLength T s J μ) hd) := by
    unfold appendRecursivePrincipalization
    exact dif_pos hd
  rw [h1]
  unfold appendIfMarked
  rw [h]

private theorem appendRecursivePrincipalization_eq_append_of_eq_some_consolidated466 (d : MarkedBlowupSequenceData (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult
      (s.boundary s.length))
    (h : markedDataOfSeq s J μ (rc (tripleAtLength T s J μ) hd) = some d) :
    appendRecursivePrincipalization hinv T rc s J μ = s.append d hinv := by
  have h1 : appendRecursivePrincipalization hinv T rc s J μ = appendIfMarked hinv s J μ (rc (tripleAtLength T s J μ) hd) := by
    unfold appendRecursivePrincipalization
    exact dif_pos hd
  rw [h1]
  unfold appendIfMarked
  rw [h]


end

private def markedPullbackSquareAtLength_consolidated466 (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (hdim : krullDimSucc (s.obj s.length) ≤ T.krullDimSucc)
    (hJ : (tripleAtLength T s J μ).IsAdmissible) :
    MarkedPullbackSquare T g where
  baseScheme := s.obj s.length
  topScheme := s'.obj s'.length
  bottom := s.proj s.length
  structMap := s.proj s.length ≫ T.structMap
  ideal := J
  mult := μ
  boundary := s.boundary s.length
  left := c.lastMap
  top := s'.proj s'.length
  bottom_structMap := rfl
  dim_le := hdim
  isPullback := by
    have h := c.isPullback_lastMap
    rwa [toMarkedSequence_projectionToBase, toMarkedSequence_projectionToBase] at h
  valid := hJ

private theorem nonempty_sequenceOfBlowupsPullback_of_markedDataOfSeq_consolidated466 {k₁ k₂ : Type u} [Field k₁] [Field k₂]
    {X Y : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k₁)} {q : Y ⟶ Spec (CommRingCat.of k₂)}
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    {I' : Y.IdealSheafData} {m' : ℕ} {E' : List Y.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (s' : MarkedBlowupSequenceData q I' m' E')
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (K : (s'.obj s'.length).IdealSheafData) (ν : ℕ)
    (f : s'.obj s'.length ⟶ s.obj s.length)
    (σ : MarkedSequenceOfBlowups (s.proj s.length ≫ p) J μ (s.boundary s.length))
    (σ' : MarkedSequenceOfBlowups (s'.proj s'.length ≫ q) K ν (s'.boundary s'.length))
    (d : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (d' : MarkedBlowupSequenceData (s'.proj s'.length ≫ q) (s'.ideal s'.length) m' (s'.boundary s'.length))
    (hrem : markedDataOfSeq s J μ σ = some d) (hrem' : markedDataOfSeq s' K ν σ' = some d')
    (cc : SequenceOfBlowupsPullback f σ'.toSequenceOfBlowups σ.toSequenceOfBlowups) :
    Nonempty (SequenceOfBlowupsPullback f d'.toSequenceOfBlowups d.toSequenceOfBlowups) := by
  classical
  by_cases hm : (MarkedBlowupSequenceData.ofMarkedSequence σ).IsMarked (s.proj s.length ≫ p)
      (s.ideal s.length) m (s.boundary s.length)
  · by_cases hm' : (MarkedBlowupSequenceData.ofMarkedSequence σ').IsMarked (s'.proj s'.length ≫ q)
        (s'.ideal s'.length) m' (s'.boundary s'.length)
    · have he : markedDataOfSeq s J μ σ = some ((MarkedBlowupSequenceData.ofMarkedSequence σ).toMarkedBlowupSequenceData
          (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) hm) := by
        unfold markedDataOfSeq
        exact dif_pos hm
      have he' : markedDataOfSeq s' K ν σ' = some ((MarkedBlowupSequenceData.ofMarkedSequence σ').toMarkedBlowupSequenceData
          (s'.proj s'.length ≫ q) (s'.ideal s'.length) m' (s'.boundary s'.length) hm') := by
        unfold markedDataOfSeq
        exact dif_pos hm'
      have hdd := Option.some.inj (hrem.symm.trans he)
      have hdd' := Option.some.inj (hrem'.symm.trans he')
      subst hdd
      subst hdd'
      exact ⟨SequenceOfBlowupsPullback.toBlowupDataOfSeq cc⟩
    · have hnone : markedDataOfSeq s' K ν σ' = none := by
        unfold markedDataOfSeq
        exact dif_neg hm'
      exact absurd (hrem'.symm.trans hnone) (Option.some_ne_none d')
  · have hnone : markedDataOfSeq s J μ σ = none := by
      unfold markedDataOfSeq
      exact dif_neg hm
    exact absurd (hrem.symm.trans hnone) (Option.some_ne_none d)

theorem nonempty_sequenceOfBlowupsPullback_appendRecursive (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (n : ℕ) (A B : PrincipalizationAssignment.{u}) (_hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (_hmult : T'.mult = T.mult) (_hideal : T'.ideal = T.ideal.comap g)
    (_hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (_htopIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap))
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (hJ : (tripleAtLength T s J μ).IsAdmissible)
    (hJ' : (tripleAtLength T' s' (J.comap c.lastMap) μ).IsAdmissible)
    (hord : ∀ x : ↥(s.obj s.length), orderAt J x ≤ (μ : ℕ∞))
    (hmark : ∀ (h : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc)
      (h' : (tripleAtLength T' s' (J.comap c.lastMap) μ).krullDimSucc ≤ T'.krullDimSucc),
      markedDataOfSeq s J μ (principalizationOfDimLe T A (tripleAtLength T s J μ) h) = none ↔
        markedDataOfSeq s' (J.comap c.lastMap) μ
          (principalizationOfDimLe T' A (tripleAtLength T' s' (J.comap c.lastMap) μ) h') = none) :
    Nonempty (SequenceOfBlowupsPullback g
      (appendRecursivePrincipalization hinv T' (principalizationOfDimLe T' A) s' (J.comap c.lastMap) μ).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  classical
  have hmg := hG.monomialInputs
  have hdimS : krullDimSucc (s.obj s.length) ≤ T.krullDimSucc :=
    MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T hT s
  have hdimS'T : krullDimSucc (s'.obj s'.length) ≤ T'.krullDimSucc :=
    MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T' hT' s'
  have hdimS'n : krullDimSucc (s'.obj s'.length) ≤ n := le_trans hdimS'T hdim'
  have hd : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc := hdimS
  have hd' : (tripleAtLength T' s' (J.comap c.lastMap) μ).krullDimSucc ≤ T'.krullDimSucc := hdimS'T
  have hiff := hmark hd hd'
  cases hq : markedDataOfSeq s J μ (principalizationOfDimLe T A (tripleAtLength T s J μ) hd) with
  | none =>
      have hq2 : markedDataOfSeq s' (J.comap c.lastMap) μ
          (principalizationOfDimLe T' A (tripleAtLength T' s' (J.comap c.lastMap) μ) hd') = none := hiff.mp hq
      rw [appendRecursivePrincipalization_eq_self_of_eq_none_consolidated466 hinv T (principalizationOfDimLe T A) s J μ hd hq,
        appendRecursivePrincipalization_eq_self_of_eq_none_consolidated466 hinv T' (principalizationOfDimLe T' A) s' (J.comap c.lastMap) μ hd' hq2]
      exact ⟨c⟩
  | some d =>
      cases hq' : markedDataOfSeq s' (J.comap c.lastMap) μ
          (principalizationOfDimLe T' A (tripleAtLength T' s' (J.comap c.lastMap) μ) hd') with
      | none => exact absurd (hq.symm.trans (hiff.mpr hq')) (Option.some_ne_none d)
      | some d' =>
          have hrule : IsPullbackBlowupSequence c.lastMap
              (principalizationOfDimLe T' A (tripleAtLength T' s' (J.comap c.lastMap) μ) hd').toSequenceOfBlowups
              (principalizationOfDimLe T A (tripleAtLength T s J μ) hd).toSequenceOfBlowups :=
            hbc.rule (markedPullbackSquareAtLength_consolidated466 T T' g s s' c J μ hdimS hJ) hord (s'.boundary s'.length)
              hsameBoundary.symm hJ' hdimS'n
          obtain ⟨cc⟩ := hrule.nonempty_sequenceOfBlowupsPullback
          obtain ⟨e⟩ := nonempty_sequenceOfBlowupsPullback_of_markedDataOfSeq_consolidated466 s s' J μ (J.comap c.lastMap) μ
            c.lastMap (principalizationOfDimLe T A (tripleAtLength T s J μ) hd)
            (principalizationOfDimLe T' A (tripleAtLength T' s' (J.comap c.lastMap) μ) hd') d d' hq hq' cc
          rw [appendRecursivePrincipalization_eq_append_of_eq_some_consolidated466 hinv T (principalizationOfDimLe T A) s J μ hd d hq,
            appendRecursivePrincipalization_eq_append_of_eq_some_consolidated466 hinv T' (principalizationOfDimLe T' A) s' (J.comap c.lastMap) μ
              hd' d' hq']
          exact (isPullbackBlowupSequence_append_of_two_fields g s d s' d' hinv c e).nonempty_sequenceOfBlowupsPullback

private theorem base_comp_comp_apply_consolidated466 {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (a : ↥A) : (f ≫ g ≫ h).base a = h.base (g.base (f.base a)) := rfl

private noncomputable def markedBlowupSequenceDataAtEndOfIsMarked {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (σ : MarkedSequenceOfBlowups (s.proj s.length ≫ p) J μ (s.boundary s.length))
    (hm : (MarkedBlowupSequenceData.ofMarkedSequence σ).IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m
      (s.boundary s.length)) :
    MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) :=
  (MarkedBlowupSequenceData.ofMarkedSequence σ).toMarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m
    (s.boundary s.length) hm

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (J : (s.obj s.length).IdealSheafData) (μ : ℕ) (hJ : (tripleAtLength T s J μ).IsAdmissible) (σ : MarkedSequenceOfBlowups (s.proj s.length ≫ T.structMap) J μ (s.boundary s.length))
include hG hinv hJ

private theorem projectionToBase_mem_orderAtLeastLocus_tripleAtLength_consolidated466 (j : ℕ) (hj : j ≤ σ.toSequenceOfBlowups.length) (z : ↥(σ.toSequenceOfBlowups.schemeAt j))
    (hz : z ∈ orderAtLeastLocus (σ.ideal j) μ) :
    (σ.toSequenceOfBlowups.projectionToBase j).base z ∈ orderAtLeastLocus J μ := by
  have hval : ∀ l ≤ σ.toSequenceOfBlowups.length, ((tripleAtLength T s J μ).transformAt σ l).IsAdmissible := by
    intro l hl
    exact hG.monomialInputs.level_valid (tripleAtLength T s J μ) hJ σ l hl
  have hsub := MarkedSequenceOfBlowups.orderAtLeastLocus_subset_preimage_transitionMap
    (orderAtComapOffExceptionalLocus_of_monomialGeometryHypotheses hG.monomialInputs)
    (tripleAtLength T s J μ) σ hval μ le_rfl 0 j (Nat.zero_le j) hj
  have h0 : (σ.toSequenceOfBlowups.transitionMap (Nat.zero_le j)).base z ∈ orderAtLeastLocus (σ.ideal 0) μ := hsub hz
  rw [σ.ideal_zero, hinv.coSupport_comap σ.toSequenceOfBlowups.isoZero J μ] at h0
  have hcomp : (σ.toSequenceOfBlowups.projectionToBase j).base z
      = (σ.toSequenceOfBlowups.isoZero.hom).base ((σ.toSequenceOfBlowups.transitionMap (Nat.zero_le j)).base z) := by
    rw [SequenceOfBlowups.projectionToBase_def]
    simp
  rw [hcomp]
  exact h0

private theorem exists_mem_orderAtLeastLocus_of_mem_center_append_consolidated466 (hm : (MarkedBlowupSequenceData.ofMarkedSequence σ).IsMarked (s.proj s.length ≫ T.structMap)
      (s.ideal s.length) T.mult (s.boundary s.length))
    (i : ℕ) (hi₀ : s.length ≤ i)
    (hi : i < (s.append (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) hinv).length)
    (z : ↥((s.append (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) hinv).obj i))
    (hz : z ∈ ((s.append (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) hinv).center i).support) :
    ∃ x : ↥(s.obj s.length), x ∈ orderAtLeastLocus J μ ∧
      ((s.append (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) hinv).proj i).base z = (s.proj s.length).base x := by
  have hdl : (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm).length = σ.toSequenceOfBlowups.length := rfl
  rw [MarkedBlowupSequenceData.append_length, hdl] at hi
  have hprojd : ∀ j : ℕ, (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm).proj j = σ.toSequenceOfBlowups.projectionToBase j := by
    intro j
    refine Eq.trans (MarkedBlowupSequenceData.projectionToBase_eq_toSequenceOfBlowups (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) j) ?_
    exact BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups σ.toSequenceOfBlowups j
  rcases Nat.eq_or_lt_of_le hi₀ with heq | hlt
  · subst heq
    have hσ0 : 0 < σ.toSequenceOfBlowups.length := by omega
    have hz1 : z ∈ ((s.appendToBlowupSequenceData (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm)).center s.length).support := hz
    rw [MarkedBlowupSequenceData.appendToBlowupSequenceData_center_length s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm)] at hz1
    have hz2 := AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1 hz1
    have hz3 := AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1 hz2
    have hz4 : (σ.toSequenceOfBlowups.isoZero.inv).base
        ((eqToHom (MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_of_le_length s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm)
          (le_refl s.length))).base z) ∈ orderAtLeastLocus (σ.ideal 0) μ :=
      σ.center_order 0 hσ0 hz3
    have hx0 := projectionToBase_mem_orderAtLeastLocus_tripleAtLength_consolidated466 hG hinv T s J μ hJ σ 0 (Nat.zero_le _) _ hz4
    refine ⟨(eqToHom (MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_of_le_length s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm)
      (le_refl s.length))).base z, ?_, ?_⟩
    · rw [SequenceOfBlowups.projectionToBase_zero] at hx0
      have hcan : ∀ u : ↥(s.obj s.length),
          (σ.toSequenceOfBlowups.isoZero.hom).base ((σ.toSequenceOfBlowups.isoZero.inv).base u) = u := by
        intro u
        simp
      rwa [hcan] at hx0
    · rw [MarkedBlowupSequenceData.append_projectionToBase,
        MarkedBlowupSequenceData.appendProjectionToBase_of_le_length s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) (le_refl s.length)]
      exact AlgebraicGeometry.Scheme.Hom.comp_apply _ _ z
  · have hkσ : i - s.length < σ.toSequenceOfBlowups.length := by omega
    have hz1 : z ∈ ((s.appendToBlowupSequenceData (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm)).center i).support := hz
    rw [MarkedBlowupSequenceData.appendToBlowupSequenceData_center_of_length_lt s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) hlt] at hz1
    have hz2 := AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1 hz1
    have hz3 : ((eqToHom (MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_of_length_lt s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm)
        hlt)).base z) ∈ orderAtLeastLocus (σ.ideal (i - s.length)) μ :=
      σ.center_order (i - s.length) hkσ hz2
    have hx0 := projectionToBase_mem_orderAtLeastLocus_tripleAtLength_consolidated466 hG hinv T s J μ hJ σ (i - s.length)
      (le_of_lt hkσ) _ hz3
    refine ⟨_, hx0, ?_⟩
    rw [MarkedBlowupSequenceData.append_projectionToBase,
      MarkedBlowupSequenceData.appendProjectionToBase_of_length_lt s (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) hlt, hprojd]
    exact base_comp_comp_apply_consolidated466 _ _ _ z


end

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
include hG

private theorem append_proj_center_ne_base_of_orderAtLeastLocus_empty_consolidated466 (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme) (hT : T.IsAdmissible)
    (n : ℕ) (A : PrincipalizationAssignment.{u})
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ) (hJ : (tripleAtLength T s J μ).IsAdmissible)
    (hempty : orderAtLeastLocus (J.comap c.lastMap) μ = ∅)
    (σ : MarkedSequenceOfBlowups (s.proj s.length ≫ T.structMap) J μ (s.boundary s.length))
    (hm : (MarkedBlowupSequenceData.ofMarkedSequence σ).IsMarked (s.proj s.length ≫ T.structMap)
      (s.ideal s.length) T.mult (s.boundary s.length))
    (D : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hD : D = s.append (markedBlowupSequenceDataAtEndOfIsMarked s J μ σ hm) hinv)
    (i : ℕ) (hi₀ : s.length ≤ i) (hi : i < D.length)
    (z : ↥(D.obj i)) (hz : z ∈ (D.center i).support) (y : ↥T'.scheme) :
    g.base y ≠ ((D.proj i).base z) := by
  subst hD
  obtain ⟨x, hx, hproj⟩ :=
    exists_mem_orderAtLeastLocus_of_mem_center_append_consolidated466 hG hinv T s J μ hJ σ hm i hi₀ hi z hz
  intro hcon
  rw [hproj] at hcon
  have hsq : IsPullback c.lastMap (s'.proj s'.length) (s.proj s.length) g := by
    have h := c.isPullback_lastMap
    rwa [toMarkedSequence_projectionToBase, toMarkedSequence_projectionToBase] at h
  obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback hsq x y hcon.symm
  have hdimS := MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hG.monomialInputs T hT s
  have hvalS := MonomialGeometryHypotheses.isAdmissible_tripleAtLength hG.monomialInputs T hT s
  have hord : orderAt (J.comap c.lastMap) w = orderAt J (c.lastMap.base w) :=
    MarkedPullbackSquare.orderAt_comap_verticalMap (SequenceOfBlowupsPullback.toMarkedPullbackSquare g s s' c hdimS hvalS) hT
      hbc.order J w
  have hmem : w ∈ orderAtLeastLocus (J.comap c.lastMap) μ := by
    rw [mem_orderAtLeastLocus_iff, hord, hw]
    exact (mem_orderAtLeastLocus_iff J μ x).1 hx
  rw [hempty] at hmem
  simp only [Set.mem_empty_iff_false] at hmem

theorem appendRecursive_proj_center_ne_of_orderAtLeastLocus_empty (n : ℕ) (A B : PrincipalizationAssignment.{u}) (_hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (_hT' : T'.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hdim' : T'.krullDimSucc ≤ n)
    (_hmult : T'.mult = T.mult) (_hideal : T'.ideal = T.ideal.comap g)
    (_hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (_htopIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (_hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap))
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (hJ : (tripleAtLength T s J μ).IsAdmissible)
    (hempty : orderAtLeastLocus (J.comap c.lastMap) μ = ∅)
    (i : ℕ) (hi₀ : s.length ≤ i) (hi : i < (appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ).length)
    (z : ↥((appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ).obj i))
    (hz : z ∈ ((appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ).center i).support) (y : ↥T'.scheme) :
    g.base y ≠ ((appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ).proj i).base z := by
  classical
  by_cases hd : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc
  · by_cases hm : (MarkedBlowupSequenceData.ofMarkedSequence (principalizationSeqAtEnd T (principalizationOfDimLe T A) s J μ hd)).IsMarked
        (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length)
    · exact append_proj_center_ne_base_of_orderAtLeastLocus_empty_consolidated466 hG hinv T T' g hT n A hbc s s' c J μ hJ hempty
        (principalizationSeqAtEnd T (principalizationOfDimLe T A) s J μ hd) hm (appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ)
        (appendRecursivePrincipalization_eq_append hinv T (principalizationOfDimLe T A) s J μ hd hm) i hi₀ hi z hz y
    · exfalso
      have hrs : markedDataOfSeq s J μ (principalizationOfDimLe T A (tripleAtLength T s J μ) hd) = none := by
        unfold markedDataOfSeq
        exact dif_neg hm
      have he : appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ = s :=
        appendRecursivePrincipalization_eq_self_of_eq_none_consolidated466 hinv T (principalizationOfDimLe T A) s J μ hd hrs
      rw [he] at hi
      omega
  · exfalso
    have he : appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ = s := by
      unfold appendRecursivePrincipalization
      exact dif_neg hd
    rw [he] at hi
    omega


end

private theorem appendRecursivePrincipalization_eq_self_or_append_consolidated466 (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : (S : MarkedIdealWithBoundary.{u}) → S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ) :
    appendRecursivePrincipalization hinv T rc s J μ = s ∨
      ∃ t : MarkedBlowupSequenceData (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult
        (s.boundary s.length), appendRecursivePrincipalization hinv T rc s J μ = s.append t hinv := by
  unfold appendRecursivePrincipalization
  by_cases hd : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc
  · rw [dif_pos hd]
    unfold appendIfMarked
    cases hrem : markedDataOfSeq s J μ (rc (tripleAtLength T s J μ) hd) with
    | none => exact Or.inl rfl
    | some d => exact Or.inr ⟨d, rfl⟩
  · rw [dif_neg hd]
    exact Or.inl rfl

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (n : ℕ) (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B) (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme) (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n) (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g) (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g)) (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary) (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups) (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap) (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length) ((s.boundary s.length).map fun D => D.comap c.lastMap))
include hG hspec hT hT' hdim hdim' hmult hideal hbdry hbc hlastIdeal hsameBoundary

theorem nonempty_sequenceOfBlowupsPullback_of_orderAtLeastLocus_empty (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (hJ : (tripleAtLength T s J μ).IsAdmissible)
    (hempty : orderAtLeastLocus (J.comap c.lastMap) μ = ∅) :
    Nonempty (SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J μ).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  rcases appendRecursivePrincipalization_eq_self_or_append_consolidated466 hinv T (principalizationOfDimLe T A) s J μ with heq | ⟨t, heq⟩
  · rw [heq]
    exact ⟨c⟩
  · have hmiss := appendRecursive_proj_center_ne_of_orderAtLeastLocus_empty hG hinv n A B hspec T T' g hT hT' hdim
      hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary J μ hJ hempty
    have hconcat : (s.append t hinv).toBlowupSequenceData
        = s.toBlowupSequenceData.append t.toBlowupSequenceData := by
      rw [MarkedBlowupSequenceData.append_toBlowupSequenceData]
      rfl
    have hseq : (s.append t hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups
        = (s.toBlowupSequenceData.append t.toBlowupSequenceData).toSequenceOfBlowups :=
      congrArg (fun D : BlowupSequenceData T.scheme => D.toSequenceOfBlowups) hconcat
    have h0 : ∀ i : ℕ, s.length ≤ i → i < (s.append t hinv).length →
        ∀ z : ↥((s.append t hinv).obj i), z ∈ ((s.append t hinv).center i).support →
          ∀ y : ↥T'.scheme, g.base y ≠ ((s.append t hinv).proj i).base z := by
      rw [← heq]
      exact hmiss
    have h0' : ∀ i : ℕ, s.length ≤ i → i < s.length + t.length →
        ∀ z : ↥((s.append t hinv).obj i), z ∈ ((s.append t hinv).center i).support →
          ∀ y : ↥T'.scheme, g.base y ≠ ((s.append t hinv).proj i).base z := by
      intro i hi0 hi
      refine h0 i hi0 ?_
      rw [MarkedBlowupSequenceData.append_length]
      exact hi
    have hproj : ∀ i : ℕ,
        (s.append t hinv).toBlowupSequenceData.projectionToBase i = (s.append t hinv).proj i := by
      intro i
      rw [MarkedBlowupSequenceData.projectionToBase_eq_toSequenceOfBlowups]
      exact (BlowupSequenceData.toSequenceOfBlowups_projectionToBase (s.append t hinv).toBlowupSequenceData i).symm
    have key : ∀ i : ℕ, s.toBlowupSequenceData.length ≤ i →
        i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length →
        ∀ z : ↥((s.toBlowupSequenceData.append t.toBlowupSequenceData).obj i),
          z ∈ ((s.toBlowupSequenceData.append t.toBlowupSequenceData).center i).support →
          ∀ y : ↥T'.scheme,
            g.base y ≠ ((s.toBlowupSequenceData.append t.toBlowupSequenceData).projectionToBase i).base z := by
      rw [← hconcat]
      intro i hi0 hi z hz y
      rw [hproj i]
      exact h0' i hi0 hi z hz y
    rw [heq, hseq]
    exact SequenceOfBlowupsPullback.nonempty_append_of_disjoint_centers g s'.toBlowupSequenceData s.toBlowupSequenceData
      t.toBlowupSequenceData c key

theorem nonempty_sequenceOfBlowupsPullback_extendByNonMonomialPart (hcont : NonMonomialOrderReductionContinues T s) (hcont' : NonMonomialOrderReductionContinues T' s')
    (hinveq : maxOrderNonMonomial T' s' = maxOrderNonMonomial T s)
    (hmark : ∀ (h : (tripleAtLength T s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)).krullDimSucc ≤ T.krullDimSucc)
      (h' : (tripleAtLength T' s' ((lastNonMonomialPart T s).comap c.lastMap)
        (maxOrderNonMonomial T s)).krullDimSucc ≤ T'.krullDimSucc),
      markedDataOfSeq s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
          (principalizationOfDimLe T A (tripleAtLength T s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)) h) = none ↔
        markedDataOfSeq s' ((lastNonMonomialPart T s).comap c.lastMap) (maxOrderNonMonomial T s)
          (principalizationOfDimLe T' A
            (tripleAtLength T' s' ((lastNonMonomialPart T s).comap c.lastMap) (maxOrderNonMonomial T s)) h')
          = none) :
    Nonempty (SequenceOfBlowupsPullback g
      (extendByNonMonomialPart hinv T' (principalizationOfDimLe T' A) s').toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  have hnonMon : lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap :=
    lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
      hbdry hbc s s' c hlastIdeal hsameBoundary
  have hJ : (tripleAtLength T s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)).IsAdmissible :=
    isAdmissible_nonMonomialTriple hG hT s hcont
  have hJ' : (tripleAtLength T' s' (lastNonMonomialPart T' s') (maxOrderNonMonomial T' s')).IsAdmissible :=
    isAdmissible_nonMonomialTriple hG hT' s' hcont'
  rw [hnonMon, hinveq] at hJ'
  have hord : ∀ x : ↥(s.obj s.length),
      orderAt (lastNonMonomialPart T s) x ≤ ((maxOrderNonMonomial T s : ℕ) : ℕ∞) :=
    fun x => orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
  have key := nonempty_sequenceOfBlowupsPullback_appendRecursive hG hinv n A B hspec T T' g hT hT' hdim hdim'
    hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
    hJ hJ' hord hmark
  have hL : extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s
      = appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s) := rfl
  have hU : extendByNonMonomialPart hinv T' (principalizationOfDimLe T' A) s'
      = appendRecursivePrincipalization hinv T' (principalizationOfDimLe T' A) s' (lastNonMonomialPart T' s') (maxOrderNonMonomial T' s') := rfl
  rw [hnonMon, hinveq] at hU
  rw [hL, hU]
  exact key


end

private theorem appendRecursivePrincipalization_congr_consolidated466 (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : (S : MarkedIdealWithBoundary.{u}) → S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J K : (s.obj s.length).IdealSheafData) (μ ν : ℕ) (hJK : J = K) (hμν : μ = ν) :
    appendRecursivePrincipalization hinv T rc s J μ = appendRecursivePrincipalization hinv T rc s K ν := by
  subst hJK
  subst hμν
  rfl

private theorem isAdmissible_tripleAtLength_congr_consolidated466 (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J K : (s.obj s.length).IdealSheafData) (μ ν : ℕ) (hJK : J = K) (hμν : μ = ν)
    (h : (tripleAtLength T s J μ).IsAdmissible) : (tripleAtLength T s K ν).IsAdmissible := by
  subst hJK
  subst hμν
  exact h

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (n : ℕ)
include hG

theorem nonempty_sequenceOfBlowupsPullback_extendByCompanionIdeal (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap))
    (hcont : CompanionIdealReductionContinues T s) (hcont' : CompanionIdealReductionContinues T' s')
    (hinveq : maxOrderNonMonomialOnOrderLocus T' s' = maxOrderNonMonomialOnOrderLocus T s)
    (hmark : ∀ (h : (tripleAtLength T s (companionIdeal T s)
        (T.mult * maxOrderNonMonomialOnOrderLocus T s)).krullDimSucc ≤ T.krullDimSucc)
      (h' : (tripleAtLength T' s' ((companionIdeal T s).comap c.lastMap)
        (T.mult * maxOrderNonMonomialOnOrderLocus T s)).krullDimSucc ≤ T'.krullDimSucc),
      markedDataOfSeq s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
          (principalizationOfDimLe T A
            (tripleAtLength T s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)) h) = none ↔
        markedDataOfSeq s' ((companionIdeal T s).comap c.lastMap) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
          (principalizationOfDimLe T' A
            (tripleAtLength T' s' ((companionIdeal T s).comap c.lastMap)
              (T.mult * maxOrderNonMonomialOnOrderLocus T s)) h') = none) :
    Nonempty (SequenceOfBlowupsPullback g
      (extendByCompanionIdeal hinv T' (principalizationOfDimLe T' A) s').toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (extendByCompanionIdeal hinv T (principalizationOfDimLe T A) s).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  have hJideal : companionIdeal T' s' = (companionIdeal T s).comap c.lastMap :=
    companionIdeal_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
      hbdry hbc s s' c hlastIdeal hsameBoundary hinveq
  have hmu : T'.mult * maxOrderNonMonomialOnOrderLocus T' s' = T.mult * maxOrderNonMonomialOnOrderLocus T s := by
    rw [hinveq, hmult]
  have hJ : (tripleAtLength T s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)).IsAdmissible :=
    companionTriple_isAdmissible hG hT s hcont
  have hJ'0 : (tripleAtLength T' s' (companionIdeal T' s') (T'.mult * maxOrderNonMonomialOnOrderLocus T' s')).IsAdmissible :=
    companionTriple_isAdmissible hG hT' s' hcont'
  have hJ' : (tripleAtLength T' s' ((companionIdeal T s).comap c.lastMap)
      (T.mult * maxOrderNonMonomialOnOrderLocus T s)).IsAdmissible :=
    isAdmissible_tripleAtLength_congr_consolidated466 T' s' (companionIdeal T' s')
      ((companionIdeal T s).comap c.lastMap) (T'.mult * maxOrderNonMonomialOnOrderLocus T' s')
      (T.mult * maxOrderNonMonomialOnOrderLocus T s) hJideal hmu hJ'0
  have hord := orderAt_companionIdeal_le hG hT s hcont
  have hA : extendByCompanionIdeal hinv T (principalizationOfDimLe T A) s
      = appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s) := rfl
  have hB0 : extendByCompanionIdeal hinv T' (principalizationOfDimLe T' A) s'
      = appendRecursivePrincipalization hinv T' (principalizationOfDimLe T' A) s' (companionIdeal T' s')
        (T'.mult * maxOrderNonMonomialOnOrderLocus T' s') := rfl
  have hB : extendByCompanionIdeal hinv T' (principalizationOfDimLe T' A) s'
      = appendRecursivePrincipalization hinv T' (principalizationOfDimLe T' A) s' ((companionIdeal T s).comap c.lastMap)
        (T.mult * maxOrderNonMonomialOnOrderLocus T s) :=
    hB0.trans
      (appendRecursivePrincipalization_congr_consolidated466 hinv T' (principalizationOfDimLe T' A) s' (companionIdeal T' s')
        ((companionIdeal T s).comap c.lastMap) (T'.mult * maxOrderNonMonomialOnOrderLocus T' s')
        (T.mult * maxOrderNonMonomialOnOrderLocus T s) hJideal hmu)
  rw [hA, hB]
  exact nonempty_sequenceOfBlowupsPullback_appendRecursive hG hinv n A B hspec T T' g hT hT' hdim hdim' hmult
    hideal hbdry hbc s s' c hlastIdeal hsameBoundary (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
    hJ hJ' hord hmark

theorem orderAtLeastLocus_comap_lastNonMonomialPart_eq_empty_of_lt (A : PrincipalizationAssignment.{u})
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap))
    (hlt : maxOrderNonMonomial T' s' < maxOrderNonMonomial T s) :
    orderAtLeastLocus ((lastNonMonomialPart T s).comap c.lastMap) (maxOrderNonMonomial T s) = ∅ := by
  have hnonMon : lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap :=
    lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
      hbdry hbc s s' c hlastIdeal hsameBoundary
  refine Set.eq_empty_of_subset_empty ?_
  intro y hy
  have hy' := (mem_orderAtLeastLocus_iff ((lastNonMonomialPart T s).comap c.lastMap) (maxOrderNonMonomial T s) y).1 hy
  rw [← hnonMon] at hy'
  have hle : orderAt (lastNonMonomialPart T' s') y ≤ ((maxOrderNonMonomial T' s' : ℕ) : ℕ∞) :=
    orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT' s' y
  have hcast : ((maxOrderNonMonomial T s : ℕ) : ℕ∞) ≤ ((maxOrderNonMonomial T' s' : ℕ) : ℕ∞) := hy'.trans hle
  have hnat : maxOrderNonMonomial T s ≤ maxOrderNonMonomial T' s' := by exact_mod_cast hcast
  exact absurd hnat (not_le.mpr hlt)


end

private theorem natCast_le_of_natCast_mul_le_mul_consolidated466 (m p : ℕ) (hp : 1 ≤ p) (a : ℕ∞)
    (h : ((m * p : ℕ) : ℕ∞) ≤ ((p : ℕ) : ℕ∞) * a) : ((m : ℕ) : ℕ∞) ≤ a := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · exact le_top
  · obtain ⟨a₀, rfl⟩ := ENat.ne_top_iff_exists.mp ha
    have h' : m * p ≤ p * a₀ := by exact_mod_cast h
    have h'' : p * m ≤ p * a₀ := by
      rw [Nat.mul_comm p m]
      exact h'
    have hle : m ≤ a₀ := Nat.le_of_mul_le_mul_left h'' (by omega)
    exact_mod_cast hle

theorem orderAtLeastLocus_comap_companionIdeal_eq_empty_of_lt (hG : PrincipalizationGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) (n : ℕ) (A : PrincipalizationAssignment.{u})
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap))
    (hlt : maxOrderNonMonomialOnOrderLocus T' s' < maxOrderNonMonomialOnOrderLocus T s) :
    orderAtLeastLocus ((companionIdeal T s).comap c.lastMap) (T.mult * maxOrderNonMonomialOnOrderLocus T s) = ∅ := by
  have hmg := hG.monomialInputs
  have hvalS' := MonomialGeometryHypotheses.isAdmissible_tripleAtLength hmg T' hT' s'
  have hchar : CharZero T'.base := hvalS'.charZero
  have hsmooth : Smooth (s'.proj s'.length ≫ T'.structMap) := hvalS'.smooth
  have hm1 : 1 ≤ T.mult := hT.one_le_mult
  have hp1 : 1 ≤ maxOrderNonMonomialOnOrderLocus T s := by omega
  have hnonMon : lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap :=
    lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
      hbdry hbc s s' c hlastIdeal hsameBoundary
  have hcompanion : (companionIdeal T s).comap c.lastMap
      = lastNonMonomialPart T' s' ^ T.mult ⊔ s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s := by
    unfold companionIdeal
    rw [hnonMon, hlastIdeal]
    exact comap_pow_sup_pow_consolidated466 c.lastMap (lastNonMonomialPart T s) (s.ideal s.length) T.mult
      (maxOrderNonMonomialOnOrderLocus T s)
  rw [hcompanion]
  refine Set.eq_empty_of_subset_empty ?_
  intro x hx
  exfalso
  have hx0 : ((T.mult * maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞)
      ≤ orderAt (lastNonMonomialPart T' s' ^ T.mult ⊔ s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s) x :=
    (mem_orderAtLeastLocus_iff _ _ _).1 hx
  have hsup : orderAt (lastNonMonomialPart T' s' ^ T.mult ⊔ s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s) x
      = min (orderAt (lastNonMonomialPart T' s' ^ T.mult) x)
        (orderAt (s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s) x) :=
    orderAt_sup _ _ x
  have hmin := le_trans hx0 (le_of_eq hsup)
  have hxN : ((T.mult * maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞)
      ≤ orderAt (lastNonMonomialPart T' s' ^ T.mult) x := le_trans hmin (min_le_left _ _)
  have hxI : ((T.mult * maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞)
      ≤ orderAt (s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s) x := le_trans hmin (min_le_right _ _)
  have hpowI : orderAt (s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s) x
      = ((maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) * orderAt (s'.ideal s'.length) x :=
    orderAt_pow T'.base (s'.proj s'.length ≫ T'.structMap) (s'.ideal s'.length)
      (maxOrderNonMonomialOnOrderLocus T s) x
  have hpowN : orderAt (lastNonMonomialPart T' s' ^ T.mult) x
      = ((T.mult : ℕ) : ℕ∞) * orderAt (lastNonMonomialPart T' s') x :=
    orderAt_pow T'.base (s'.proj s'.length ≫ T'.structMap) (lastNonMonomialPart T' s') T.mult x
  have hA : ((T.mult : ℕ) : ℕ∞) ≤ orderAt (s'.ideal s'.length) x :=
    natCast_le_of_natCast_mul_le_mul_consolidated466 T.mult (maxOrderNonMonomialOnOrderLocus T s) hp1 (orderAt (s'.ideal s'.length) x)
      (le_trans hxI (le_of_eq hpowI))
  have hmultE : ((T'.mult : ℕ) : ℕ∞) = ((T.mult : ℕ) : ℕ∞) := by rw [hmult]
  have hmem : x ∈ orderAtLeastLocus (s'.ideal s'.length) T'.mult :=
    (mem_orderAtLeastLocus_iff _ _ _).2 (hmultE.trans_le hA)
  have hb := orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT' s' x hmem
  have hxN2 : ((T.mult * maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞)
      ≤ ((T.mult : ℕ) : ℕ∞) * orderAt (lastNonMonomialPart T' s') x :=
    le_trans hxN (le_of_eq hpowN)
  have hxN3 : ((maxOrderNonMonomialOnOrderLocus T s * T.mult : ℕ) : ℕ∞)
      ≤ ((T.mult : ℕ) : ℕ∞) * orderAt (lastNonMonomialPart T' s') x := by
    rw [Nat.mul_comm (maxOrderNonMonomialOnOrderLocus T s) T.mult]
    exact hxN2
  have hC : ((maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) ≤ orderAt (lastNonMonomialPart T' s') x :=
    natCast_le_of_natCast_mul_le_mul_consolidated466 (maxOrderNonMonomialOnOrderLocus T s) T.mult hm1 (orderAt (lastNonMonomialPart T' s') x) hxN3
  have hfin : ((maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) ≤ ((maxOrderNonMonomialOnOrderLocus T' s' : ℕ) : ℕ∞) := le_trans hC hb
  have hnat : maxOrderNonMonomialOnOrderLocus T s ≤ maxOrderNonMonomialOnOrderLocus T' s' := by exact_mod_cast hfin
  omega


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionBaseChange
section

open CategoryTheory.Limits

section

private theorem isNoetherian_schemeAt_of_isAdmissible_consolidated474 (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (u : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (i : ℕ) (hi : i ≤ u.length) :
    IsNoetherian (u.obj i) := by
  have hlen : i ≤ u.toMarkedSequenceOfBlowups.length := hi.trans_eq (MarkedBlowupSequenceData.toMarkedSequence_length u).symm
  have h := MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hT u.toMarkedSequenceOfBlowups i hlen
  rwa [MarkedBlowupSequenceData.toMarkedSequence_schemeAt] at h

private theorem nonempty_sequenceOfBlowupsPullback_of_length_eq_zero_consolidated474 {X Y : Scheme.{u}} (g : Y ⟶ X)
    (hflat : Flat g) (sD : SequenceOfBlowups X) (sU : SequenceOfBlowups Y)
    (hD : sD.length = 0) (hU : sU.length = 0) :
    Nonempty (SequenceOfBlowupsPullback g sU sD) := by
  have := hflat
  refine ⟨SequenceOfBlowupsPullback.ofBlowupDataOfSeq (SequenceOfBlowupsPullback.ofCentersMissImage g (BlowupSequenceData.ofSequenceOfBlowups sD) ?_
    (BlowupSequenceData.ofSequenceOfBlowups sU) ?_)⟩
  · intro i hi
    rw [BlowupSequenceData.ofSequenceOfBlowups_length sD, hD] at hi
    exact absurd hi (Nat.not_lt_zero i)
  · exact (BlowupSequenceData.ofSequenceOfBlowups_length sU).trans hU

private theorem length_nonMonomialOrderReductionIter_zero_consolidated474 (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : (S : MarkedIdealWithBoundary.{u}) → S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) :
    (nonMonomialOrderReductionIter hinv T rc 0).toMarkedSequenceOfBlowups.toSequenceOfBlowups.length = 0 := by
  have h : (nonMonomialOrderReductionIter hinv T rc 0).length = 0 := by
    rw [nonMonomialOrderReductionIter_zero, emptyMarkedBlowupSequenceData_length]
  exact (MarkedBlowupSequenceData.toMarkedSequence_length (nonMonomialOrderReductionIter hinv T rc 0)).trans h

private theorem markedDataOfSeq_ne_none_of_isMarked_consolidated474 {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (σ : MarkedSequenceOfBlowups (s.proj s.length ≫ p) J μ (s.boundary s.length))
    (hm : (MarkedBlowupSequenceData.ofMarkedSequence σ).IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m
      (s.boundary s.length)) :
    markedDataOfSeq s J μ σ ≠ none := by
  have he : markedDataOfSeq s J μ σ = some ((MarkedBlowupSequenceData.ofMarkedSequence σ).toMarkedBlowupSequenceData
      (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) hm) := by
    unfold markedDataOfSeq
    exact dif_pos hm
  rw [he]
  exact Option.some_ne_none _

private theorem lastIdeal_and_boundary_comap_of_flat_consolidated474 {k k' : Type u} [Field k] [Field k'] {X Y : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k')} {g : Y ⟶ X}
    {I : X.IdealSheafData} {I' : Y.IdealSheafData} {m m' : ℕ}
    {E : List X.IdealSheafData} {E' : List Y.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (s' : MarkedBlowupSequenceData q I' m' E') (hm : m' = m)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hflat : Flat g)
    (hI : I' = I.comap g)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (E.map fun D => D.comap g))
    (hN : ∀ i : ℕ, i ≤ s.length → IsNoetherian (s.obj i))
    (hN' : ∀ j : ℕ, j ≤ s'.length → IsNoetherian (s'.obj j)) :
    s'.ideal s'.length = (s.ideal s.length).comap c.lastMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
        ((s.boundary s.length).map fun D => D.comap c.lastMap) := by
  subst hm
  have := hflat
  exact SequenceOfBlowupsPullback.ideal_boundary_last_eq_comap_lastMap s s' c hI hE hN hN'

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (n : ℕ) (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B) (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme) (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n) (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g) (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g)) (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
include hG hspec hT hT' hdim hdim' hmult hideal hbdry hbc

private theorem extendByNonMonomialPart_sequenceOfBlowupsPullback_cases_consolidated474 (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hcont : NonMonomialOrderReductionContinues T s) :
    (NonMonomialOrderReductionContinues T' s' ∧ Nonempty (SequenceOfBlowupsPullback g
        (extendByNonMonomialPart hinv T' (principalizationOfDimLe T' A) s').toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s).toMarkedSequenceOfBlowups.toSequenceOfBlowups)) ∨
      Nonempty (SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  classical
  obtain ⟨hlastIdeal, hsameBoundary⟩ :=
    lastIdeal_and_boundary_comap_of_flat_consolidated474 s s' hmult c hbc.flat hideal hbdry
      (isNoetherian_schemeAt_of_isAdmissible_consolidated474 T hT s) (isNoetherian_schemeAt_of_isAdmissible_consolidated474 T' hT' s')
  have hle : maxOrderNonMonomial T' s' ≤ maxOrderNonMonomial T s :=
    maxOrderNonMonomial_le_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc
      s s' c hlastIdeal hsameBoundary
  have hnonMon : lastNonMonomialPart T' s' = (lastNonMonomialPart T s).comap c.lastMap :=
    lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
      hbdry hbc s s' c hlastIdeal hsameBoundary
  have hJ : (tripleAtLength T s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)).IsAdmissible :=
    isAdmissible_nonMonomialTriple hG hT s hcont
  have hskip : orderAtLeastLocus ((lastNonMonomialPart T s).comap c.lastMap) (maxOrderNonMonomial T s) = ∅ →
      Nonempty (SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
    intro hempty
    have hL : extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s
        = appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s) := rfl
    rw [hL]
    exact nonempty_sequenceOfBlowupsPullback_of_orderAtLeastLocus_empty hG hinv n A B hspec T T' g hT hT' hdim hdim'
      hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
      hJ hempty
  by_cases hcont' : NonMonomialOrderReductionContinues T' s'
  · by_cases heq : maxOrderNonMonomial T' s' = maxOrderNonMonomial T s
    · refine Or.inl ⟨hcont', ?_⟩
      refine nonempty_sequenceOfBlowupsPullback_extendByNonMonomialPart hG hinv n A B hspec T T' g hT hT' hdim
        hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary hcont hcont' heq ?_
      intro h h'
      refine iff_of_false ?_ ?_
      · exact markedDataOfSeq_ne_none_of_isMarked_consolidated474 s (lastNonMonomialPart T s) (maxOrderNonMonomial T s) _
          (isMarked_seqAtEnd_lastNonMonomialPart hG hspec hT hdim s hcont)
      · have hmkU := isMarked_seqAtEnd_lastNonMonomialPart hG hspec hT' hdim' s' hcont'
        rw [hnonMon, heq] at hmkU
        exact markedDataOfSeq_ne_none_of_isMarked_consolidated474 s' ((lastNonMonomialPart T s).comap c.lastMap) (maxOrderNonMonomial T s) _
          hmkU
    · refine Or.inr (hskip ?_)
      exact orderAtLeastLocus_comap_lastNonMonomialPart_eq_empty_of_lt hG hinv n A T T' g hT hT'
        hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary (lt_of_le_of_ne hle heq)
  · refine Or.inr (hskip ?_)
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact orderAtLeastLocus_comap_lastNonMonomialPart_eq_empty_of_lt hG hinv n A T T' g hT hT'
        hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary hlt
    · have h1 : T'.mult ≤ maxOrderNonMonomial T' s' := by
        rw [hmult, heq]
        exact ((nonMonomialOrderReductionContinues_iff T s).1 hcont).1
      have h2 : ¬ (orderAtLeastLocus (lastNonMonomialPart T' s') (maxOrderNonMonomial T' s')).Nonempty := fun hx =>
        hcont' ((nonMonomialOrderReductionContinues_iff T' s').2 ⟨h1, hx⟩)
      have h3 := Set.not_nonempty_iff_eq_empty.mp h2
      rw [hnonMon, heq] at h3
      exact h3

theorem nonMonomialOrderReductionIter_exists_sequenceOfBlowupsPullback (f : ℕ) :
    ∃ (f' : ℕ) (c : SequenceOfBlowupsPullback g
        (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f').toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).toMarkedSequenceOfBlowups.toSequenceOfBlowups),
      (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f').ideal
          (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f').length =
        ((nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).ideal
          (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).length).comap c.lastMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary
        ((nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f').boundary
          (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f').length)
        (((nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).boundary
          (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).length).map fun D => D.comap c.lastMap) := by
  classical
  have key : ∀ j : ℕ, ∃ f' : ℕ, Nonempty (SequenceOfBlowupsPullback g
      (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f').toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) j).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
    intro j
    induction j with
    | zero =>
        exact ⟨0, nonempty_sequenceOfBlowupsPullback_of_length_eq_zero_consolidated474 g hbc.flat _ _
          (length_nonMonomialOrderReductionIter_zero_consolidated474 hinv T (principalizationOfDimLe T A))
          (length_nonMonomialOrderReductionIter_zero_consolidated474 hinv T' (principalizationOfDimLe T' A))⟩
    | succ j ih =>
        obtain ⟨f', hc⟩ := ih
        obtain ⟨c⟩ := hc
        by_cases hcont : NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) j)
        · rcases extendByNonMonomialPart_sequenceOfBlowupsPullback_cases_consolidated474 hG hinv n A B hspec T T' g hT hT' hdim hdim' hmult
            hideal hbdry hbc (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) j)
            (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f') c hcont with ⟨hcont', hcmp⟩ | hcmp
          · refine ⟨f' + 1, ?_⟩
            rw [nonMonomialOrderReductionIter_succ_of_continues hinv T (principalizationOfDimLe T A) j hcont,
              nonMonomialOrderReductionIter_succ_of_continues hinv T' (principalizationOfDimLe T' A) f' hcont']
            exact hcmp
          · refine ⟨f', ?_⟩
            rw [nonMonomialOrderReductionIter_succ_of_continues hinv T (principalizationOfDimLe T A) j hcont]
            exact hcmp
        · refine ⟨f', ?_⟩
          rw [nonMonomialOrderReductionIter_succ_of_not_continues hinv T (principalizationOfDimLe T A) j hcont]
          exact ⟨c⟩
  obtain ⟨f', hc⟩ := key f
  obtain ⟨c⟩ := hc
  refine ⟨f', c, ?_⟩
  exact lastIdeal_and_boundary_comap_of_flat_consolidated474 (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f)
    (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f') hmult c hbc.flat hideal hbdry
    (isNoetherian_schemeAt_of_isAdmissible_consolidated474 T hT (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f))
    (isNoetherian_schemeAt_of_isAdmissible_consolidated474 T' hT' (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f'))


end

private theorem lastIdeal_and_boundary_comap_of_isAdmissible_consolidated474 (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hflat : Flat g)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (s' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    s'.ideal s'.length = (s.ideal s.length).comap c.lastMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
        ((s.boundary s.length).map fun D => D.comap c.lastMap) :=
  lastIdeal_and_boundary_comap_of_flat_consolidated474 s s' hmult c hflat hideal hbdry
    (isNoetherian_schemeAt_of_isAdmissible_consolidated474 T hT s) (isNoetherian_schemeAt_of_isAdmissible_consolidated474 T' hT' s')

private theorem markedDataOfSeq_companionIdeal_ne_none_consolidated474 (hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : T.IsAdmissible) (A : PrincipalizationAssignment.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : CompanionIdealReductionContinues T s) (K : (s.obj s.length).IdealSheafData) (ν : ℕ)
    (hK : companionIdeal T s = K) (hν : T.mult * maxOrderNonMonomialOnOrderLocus T s = ν)
    (h : (tripleAtLength T s K ν).krullDimSucc ≤ T.krullDimSucc) :
    ¬ (markedDataOfSeq s K ν (principalizationOfDimLe T A (tripleAtLength T s K ν) h) = none) := by
  subst hK
  subst hν
  exact markedDataOfSeq_ne_none_of_isMarked_consolidated474 s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
    (principalizationOfDimLe T A (tripleAtLength T s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)) h)
    (isMarked_seqAtEnd_companionIdeal hG hT A s hcont)

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (n : ℕ) (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B) (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme) (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n) (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g) (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g)) (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
include hG hspec hT hT' hdim hdim' hmult hideal hbdry hbc

private theorem nonempty_sequenceOfBlowupsPullback_nonMonomialOrderReduction_consolidated474 :
    Nonempty (SequenceOfBlowupsPullback g
      (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  obtain ⟨f₁, c, hI, hB⟩ := nonMonomialOrderReductionIter_exists_sequenceOfBlowupsPullback hG hinv n A B hspec T T' g hT
    hT' hdim hdim' hmult hideal hbdry hbc (maxOrder (nonMonomialPart T.boundary T.ideal) + 1)
  have hlow : nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A)
      (maxOrder (nonMonomialPart T.boundary T.ideal) + 1) = nonMonomialOrderReduction hinv T (principalizationOfDimLe T A) :=
    (nonMonomialOrderReduction_eq hinv T (principalizationOfDimLe T A)).symm
  have hncT : ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A)
      (maxOrder (nonMonomialPart T.boundary T.ideal) + 1)) := by
    rw [hlow]
    exact not_nonMonomialOrderReductionContinues_nonMonomialOrderReduction hG hinv hspec hT hdim
  have hncT' : ¬ NonMonomialOrderReductionContinues T' (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f₁) := by
    intro hc
    exact hncT (nonMonomialOrderReductionContinues_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
      hbdry hbc
      (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) (maxOrder (nonMonomialPart T.boundary T.ideal) + 1))
      (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f₁) c hI hB hc)
  have h1 : nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A)
      (max f₁ (maxOrder (nonMonomialPart T'.boundary T'.ideal) + 1))
      = nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f₁ :=
    nonMonomialOrderReductionIter_eq_of_not_continues hinv T' (principalizationOfDimLe T' A) f₁ hncT'
      (max f₁ (maxOrder (nonMonomialPart T'.boundary T'.ideal) + 1)) (le_max_left _ _)
  have h2 : nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A)
      (max f₁ (maxOrder (nonMonomialPart T'.boundary T'.ideal) + 1))
      = nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A) :=
    nonMonomialOrderReductionIter_eq_of_maxOrder_lt hG hinv hspec hT' hdim'
      (max f₁ (maxOrder (nonMonomialPart T'.boundary T'.ideal) + 1)) (le_max_right _ _)
  have hup : nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f₁ = nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A) :=
    h1.symm.trans h2
  refine ⟨?_⟩
  rw [← hup, ← hlow]
  exact c

theorem companionIdealReductionIter_exists_sequenceOfBlowupsPullback (f : ℕ) :
    ∃ (f' : ℕ) (c : SequenceOfBlowupsPullback g
        (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A))
          f').toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))
          f).toMarkedSequenceOfBlowups.toSequenceOfBlowups),
      (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f').ideal
          (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f').length =
        ((companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f).ideal
          (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f).length).comap
            c.lastMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary
        ((companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f').boundary
          (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f').length)
        (((companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f).boundary
          (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f).length).map
            fun D => D.comap c.lastMap) := by
  have hflat : Flat g := hbc.flat
  have key : ∀ m : ℕ, ∃ f' : ℕ, Nonempty (SequenceOfBlowupsPullback g
      (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A))
        f').toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))
        m).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
    intro m
    induction m with
    | zero =>
        exact ⟨0, nonempty_sequenceOfBlowupsPullback_nonMonomialOrderReduction_consolidated474 hG hinv n A B hspec T T' g hT hT' hdim hdim' hmult
          hideal hbdry hbc⟩
    | succ m ih =>
        obtain ⟨f₁, hc⟩ := ih
        obtain ⟨c⟩ := hc
        by_cases hcont : CompanionIdealReductionContinues T
            (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)
        · obtain ⟨hI, hB⟩ := lastIdeal_and_boundary_comap_of_isAdmissible_consolidated474 T T' g hT hT' hflat hmult hideal hbdry
            (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)
            (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁) c
          have hstepL := companionIdealReductionIter_succ_of_continues hinv T (principalizationOfDimLe T A)
            (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m hcont
          have hle := maxOrderNonMonomialOnOrderLocus_le_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult
            hideal hbdry hbc
            (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)
            (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁) c hI hB
          rcases hle.lt_or_eq with hlt | heq
          · have hJ := companionTriple_isAdmissible hG hT
              (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m) hcont
            have hempty := orderAtLeastLocus_comap_companionIdeal_eq_empty_of_lt hG hinv n A
              T T' g hT hT' hdim hdim' hmult hideal hbdry hbc
              (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)
              (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁) c hI hB
              hlt
            refine ⟨f₁, ?_⟩
            rw [hstepL]
            exact nonempty_sequenceOfBlowupsPullback_of_orderAtLeastLocus_empty hG hinv n A B hspec T T' g hT hT'
              hdim hdim' hmult hideal hbdry hbc
              (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)
              (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁) c hI hB
              (companionIdeal T
                (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m))
              (T.mult * maxOrderNonMonomialOnOrderLocus T
                (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)) hJ hempty
          · have hcont1 : (1 : ℕ) ≤ maxOrderNonMonomialOnOrderLocus T
                (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m) := hcont
            have hcont' : CompanionIdealReductionContinues T'
                (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁) := by
              show (1 : ℕ) ≤ maxOrderNonMonomialOnOrderLocus T'
                (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁)
              exact le_trans hcont1 heq.ge
            have hid' := companionIdeal_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim
              hdim' hmult hideal hbdry hbc
              (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)
              (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁) c hI hB
              heq
            have hmu' : T'.mult * maxOrderNonMonomialOnOrderLocus T'
                (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁)
                = T.mult * maxOrderNonMonomialOnOrderLocus T
                  (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m) := by
              rw [hmult, heq]
            refine ⟨f₁ + 1, ?_⟩
            rw [hstepL, companionIdealReductionIter_succ_of_continues hinv T' (principalizationOfDimLe T' A)
              (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁ hcont']
            refine nonempty_sequenceOfBlowupsPullback_extendByCompanionIdeal hG hinv n A B hspec T T' g hT hT'
              hdim hdim' hmult hideal hbdry hbc
              (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)
              (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁) c hI hB
              hcont hcont' heq ?_
            intro h h'
            refine iff_of_false ?_ ?_
            · exact markedDataOfSeq_companionIdeal_ne_none_consolidated474 hG T hT A
                (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m) hcont
                (companionIdeal T
                  (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m))
                (T.mult * maxOrderNonMonomialOnOrderLocus T
                  (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m))
                rfl rfl h
            · exact markedDataOfSeq_companionIdeal_ne_none_consolidated474 hG T' hT' A
                (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f₁) hcont'
                ((companionIdeal T
                  (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)).comap
                    c.lastMap)
                (T.mult * maxOrderNonMonomialOnOrderLocus T
                  (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m))
                hid' hmu' h'
        · refine ⟨f₁, ?_⟩
          rw [companionIdealReductionIter_succ_of_not_continues hinv T (principalizationOfDimLe T A)
            (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m hcont]
          exact ⟨c⟩
  obtain ⟨f', hn⟩ := key f
  obtain ⟨c⟩ := hn
  exact ⟨f', c, lastIdeal_and_boundary_comap_of_isAdmissible_consolidated474 T T' g hT hT' hflat hmult hideal hbdry
    (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f)
    (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f') c⟩


end

private theorem projectionToBase_mem_orderAtLeastLocus_consolidated474 (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (σ : T.SequenceOfBlowups)
    (j : ℕ) (hj : j ≤ σ.toSequenceOfBlowups.length) (z : ↥(σ.toSequenceOfBlowups.schemeAt j))
    (hz : z ∈ orderAtLeastLocus (σ.ideal j) T.mult) :
    (σ.toSequenceOfBlowups.projectionToBase j).base z ∈ orderAtLeastLocus T.ideal T.mult := by
  have hval : ∀ l ≤ σ.toSequenceOfBlowups.length, (T.transformAt σ l).IsAdmissible := by
    intro l hl
    exact hG.monomialInputs.level_valid T hT σ l hl
  have hsub := MarkedSequenceOfBlowups.orderAtLeastLocus_subset_preimage_transitionMap
    (orderAtComapOffExceptionalLocus_of_monomialGeometryHypotheses hG.monomialInputs)
    T σ hval T.mult le_rfl 0 j (Nat.zero_le j) hj
  have h0 : (σ.toSequenceOfBlowups.transitionMap (Nat.zero_le j)).base z ∈ orderAtLeastLocus (σ.ideal 0) T.mult := hsub hz
  rw [σ.ideal_zero, hinv.coSupport_comap σ.toSequenceOfBlowups.isoZero T.ideal T.mult] at h0
  have hcomp : (σ.toSequenceOfBlowups.projectionToBase j).base z
      = (σ.toSequenceOfBlowups.isoZero.hom).base ((σ.toSequenceOfBlowups.transitionMap (Nat.zero_le j)).base z) := by
    rw [SequenceOfBlowups.projectionToBase_def]
    simp
  rw [hcomp]
  exact h0

private theorem nonempty_sequenceOfBlowupsPullback_of_center_not_mem_range_consolidated474 {X Y : Scheme.{u}} (g : Y ⟶ X)
    (hflat : Flat g) (sD : SequenceOfBlowups X) (sU : SequenceOfBlowups Y)
    (hU : sU.length = 0)
    (hmiss : ∀ i : ℕ, i < sD.length → ∀ z : ↥(sD.schemeAt i), z ∈ (sD.center i).support →
      ∀ y : ↥Y, g.base y ≠ (sD.projectionToBase i).base z) :
    Nonempty (SequenceOfBlowupsPullback g sU sD) := by
  have := hflat
  refine ⟨SequenceOfBlowupsPullback.ofBlowupDataOfSeq (SequenceOfBlowupsPullback.ofCentersMissImage g (BlowupSequenceData.ofSequenceOfBlowups sD) ?_
    (BlowupSequenceData.ofSequenceOfBlowups sU) ?_)⟩
  · intro i hi z hz y
    rw [BlowupSequenceData.ofSequenceOfBlowups_length sD] at hi
    have hproj : (BlowupSequenceData.ofSequenceOfBlowups sD).projectionToBase i = sD.projectionToBase i :=
      (BlowupSequenceData.toSequenceOfBlowups_projectionToBase (BlowupSequenceData.ofSequenceOfBlowups sD) i).symm.trans
        (BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups sD i)
    rw [hproj]
    exact hmiss i hi z hz y
  · exact (BlowupSequenceData.ofSequenceOfBlowups_length sU).trans hU

private theorem exists_sequenceOfBlowupsPullback_congr_consolidated474 {T T' : MarkedIdealWithBoundary.{u}} (g : T'.scheme ⟶ T.scheme)
    (S₁ S₂ : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (R₁ R₂ : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hS : S₁ = S₂) (hR : R₁ = R₂)
    (hex : ∃ c : SequenceOfBlowupsPullback g S₁.toMarkedSequenceOfBlowups.toSequenceOfBlowups R₁.toMarkedSequenceOfBlowups.toSequenceOfBlowups,
      S₁.ideal S₁.length = (R₁.ideal R₁.length).comap c.lastMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary (S₁.boundary S₁.length)
        ((R₁.boundary R₁.length).map fun D => D.comap c.lastMap)) :
    ∃ c : SequenceOfBlowupsPullback g S₂.toMarkedSequenceOfBlowups.toSequenceOfBlowups R₂.toMarkedSequenceOfBlowups.toSequenceOfBlowups,
      S₂.ideal S₂.length = (R₂.ideal R₂.length).comap c.lastMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary (S₂.boundary S₂.length)
        ((R₂.boundary R₂.length).map fun D => D.comap c.lastMap) := by
  subst hS
  subst hR
  exact hex

private theorem isLocallyMonomialTriple_tripleAtLength_congr_consolidated474 (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J K : (s.obj s.length).IdealSheafData) (μ ν : ℕ) (hJK : J = K) (hμν : μ = ν)
    (h : MonomialCenter.IsLocallyMonomialTriple (tripleAtLength T s J μ)) :
    MonomialCenter.IsLocallyMonomialTriple (tripleAtLength T s K ν) := by
  subst hJK
  subst hμν
  exact h

section
variable (hinv : ComapIsoInvariance.{u})

private theorem isPullbackBlowupSequence_monomialPrincipalization_congr_consolidated474 (T T' : MarkedIdealWithBoundary.{u})
    (S : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (S' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (f : S'.obj S'.length ⟶ S.obj S.length)
    (J : (S.obj S.length).IdealSheafData) (μ : ℕ)
    (K₁ K₂ : (S'.obj S'.length).IdealSheafData) (ν₁ ν₂ : ℕ)
    (hK : K₁ = K₂) (hν : ν₁ = ν₂)
    (h : IsPullbackBlowupSequence f (monomialPrincipalization hinv (tripleAtLength T' S' K₁ ν₁)).toSequenceOfBlowups
      (monomialPrincipalization hinv (tripleAtLength T S J μ)).toSequenceOfBlowups) :
    IsPullbackBlowupSequence f (monomialPrincipalization hinv (tripleAtLength T' S' K₂ ν₂)).toSequenceOfBlowups
      (monomialPrincipalization hinv (tripleAtLength T S J μ)).toSequenceOfBlowups := by
  subst hK
  subst hν
  exact h

private theorem isPullbackSequenceOfBlowups_monomial_of_pullback_consolidated474 (hmg : MonomialGeometryHypotheses.{u})
    (n : ℕ) (A : PrincipalizationAssignment.{u}) (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (S : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (S' : MarkedBlowupSequenceData T'.structMap T'.ideal T'.mult T'.boundary)
    (c : SequenceOfBlowupsPullback g S'.toMarkedSequenceOfBlowups.toSequenceOfBlowups S.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hmult : T'.mult = T.mult)
    (hidealLastComap : S'.ideal S'.length = (S.ideal S.length).comap c.lastMap)
    (hlastBoundary : MarkedIdealWithBoundary.SameNontrivialBoundary (S'.boundary S'.length)
      ((S.boundary S.length).map fun D => D.comap c.lastMap))
    (hmonLow : MonomialCenter.IsLocallyMonomialTriple (tripleAtLength T S (S.ideal S.length) T.mult))
    (hmonUp : MonomialCenter.IsLocallyMonomialTriple
      (tripleAtLength T' S' (S'.ideal S'.length) T'.mult)) :
    IsPullbackBlowupSequence c.lastMap
      (monomialPrincipalization hinv (tripleAtLength T' S' (S'.ideal S'.length) T'.mult)).toSequenceOfBlowups
      (monomialPrincipalization hinv (tripleAtLength T S (S.ideal S.length) T.mult)).toSequenceOfBlowups := by
  have hdimS := MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T hT S
  have hvalS := MonomialGeometryHypotheses.isAdmissible_tripleAtLength hmg T hT S
  have hmonUp' : MonomialCenter.IsLocallyMonomialTriple
      (tripleAtLength T' S' ((S.ideal S.length).comap c.lastMap) T.mult) :=
    isLocallyMonomialTriple_tripleAtLength_congr_consolidated474 T' S' (S'.ideal S'.length)
      ((S.ideal S.length).comap c.lastMap) T'.mult T.mult hidealLastComap hmult hmonUp
  have hmain := hbc.monomialBody (SequenceOfBlowupsPullback.toMarkedPullbackSquare g S S' c hdimS hvalS) hmonLow
    (S'.boundary S'.length) hlastBoundary.symm hmonUp'
  exact isPullbackBlowupSequence_monomialPrincipalization_congr_consolidated474 hinv T T' S S' c.lastMap (S.ideal S.length)
    T.mult ((S.ideal S.length).comap c.lastMap) (S'.ideal S'.length) T.mult T'.mult hidealLastComap.symm
    hmult.symm hmain


end

private theorem orderReductionSeq_isPullbackBlowupSequence_of_comap_consolidated474 (hG : PrincipalizationGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) (n : ℕ)
    (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T T' : MarkedIdealWithBoundary.{u}) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : MarkedIdealWithBoundary.SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap) :
    IsPullbackBlowupSequence g (orderReductionSeq hinv T' (principalizationOfDimLe T' A)).toSequenceOfBlowups
      (orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups := by
  classical
  by_cases hemp : orderAtLeastLocus T'.ideal T'.mult = ∅
  · have hU : (orderReductionSeq hinv T' (principalizationOfDimLe T' A)).toSequenceOfBlowups.length = 0 :=
      orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T' A hemp
    have hmiss : ∀ i : ℕ, i < (orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups.length →
        ∀ z : ↥((orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups.schemeAt i),
          z ∈ ((orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups.center i).support →
          ∀ y : ↥T'.scheme,
            g.base y ≠ ((orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups.projectionToBase i).base z := by
      intro i hi z hz y hcon
      have hz' : z ∈ orderAtLeastLocus ((orderReductionSeq hinv T (principalizationOfDimLe T A)).ideal i) T.mult :=
        (orderReductionSeq hinv T (principalizationOfDimLe T A)).center_order i hi hz
      have hkey := projectionToBase_mem_orderAtLeastLocus_consolidated474 hG hinv T hT (orderReductionSeq hinv T (principalizationOfDimLe T A)) i
        (le_of_lt hi) z hz'
      rw [← hcon] at hkey
      have hordy := orderAt_comap_of_baseChangeCompatible hinv A n T hT g T'.base T'.structMap hbc T.ideal y
      have hmem : y ∈ orderAtLeastLocus T'.ideal T'.mult := by
        rw [mem_orderAtLeastLocus_iff, hideal, hmult, hordy]
        exact (mem_orderAtLeastLocus_iff T.ideal T.mult (g.base y)).1 hkey
      rw [hemp] at hmem
      simp only [Set.mem_empty_iff_false] at hmem
    obtain ⟨cc⟩ := nonempty_sequenceOfBlowupsPullback_of_center_not_mem_range_consolidated474 g hbc.flat
      (orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups
      (orderReductionSeq hinv T' (principalizationOfDimLe T' A)).toSequenceOfBlowups hU hmiss
    exact cc.isPullbackSequenceOfBlowups
  · have hT'ne : (orderAtLeastLocus T'.ideal T'.mult).Nonempty := Set.nonempty_iff_ne_empty.2 hemp
    have hTne : (orderAtLeastLocus T.ideal T.mult).Nonempty := by
      rcases Set.eq_empty_or_nonempty (orderAtLeastLocus T.ideal T.mult) with h | h
      · exfalso
        apply hemp
        rw [hideal, hmult]
        exact orderAtLeastLocus_comap_eq_empty_of_baseChangeCompatible hinv A n T hT g T'.base T'.structMap hbc h
      · exact h
    obtain ⟨f', hc⟩ := companionIdealReductionIter_exists_sequenceOfBlowupsPullback hG hinv n A B hspec T T' g hT hT'
      hdim hdim' hmult hideal hbdry hbc (maxOrderNonMonomialOnOrderLocus T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) + 1)
    have hlowStop : ¬ CompanionIdealReductionContinues T
        (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))
          (maxOrderNonMonomialOnOrderLocus T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) + 1)) := by
      rw [← companionIdealReduction_eq hinv T (principalizationOfDimLe T A)]
      exact not_companionIdealReductionContinues_companionIdealReduction hG hinv hspec hT hdim
    have hupStop : ¬ CompanionIdealReductionContinues T'
        (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f') := by
      obtain ⟨c0, h1, h2⟩ := hc
      intro hcont
      exact hlowStop (companionIdealReductionContinues_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult
        hideal hbdry hbc _ _ c0 h1 h2 hcont)
    have hstop' : ¬ CompanionIdealReductionContinues T'
        (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A))
          (maxOrderNonMonomialOnOrderLocus T' (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) + 1)) := by
      rw [← companionIdealReduction_eq hinv T' (principalizationOfDimLe T' A)]
      exact not_companionIdealReductionContinues_companionIdealReduction hG hinv hspec hT' hdim'
    have hupEq : companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f'
        = companionIdealReduction hinv T' (principalizationOfDimLe T' A) := by
      rw [companionIdealReduction_eq hinv T' (principalizationOfDimLe T' A)]
      rcases le_total f' (maxOrderNonMonomialOnOrderLocus T' (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) + 1) with h | h
      · exact (companionIdealReductionIter_eq_of_not_continues hinv T' (principalizationOfDimLe T' A)
          (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f' hupStop _ h).symm
      · exact companionIdealReductionIter_eq_of_not_continues hinv T' (principalizationOfDimLe T' A)
          (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) _ hstop' f' h
    obtain ⟨c, hidealLastComap, hlastBoundary⟩ := exists_sequenceOfBlowupsPullback_congr_consolidated474 g _ _ _ _ hupEq
      (companionIdealReduction_eq hinv T (principalizationOfDimLe T A)).symm hc
    have hmonLow : MonomialCenter.IsLocallyMonomialTriple
        (tripleAtLength T (companionIdealReduction hinv T (principalizationOfDimLe T A))
          ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult) :=
      isLocallyMonomialTriple_tripleAtLength_companionIdealReduction hG hinv hspec hT hdim
    have hmonUp : MonomialCenter.IsLocallyMonomialTriple
        (tripleAtLength T' (companionIdealReduction hinv T' (principalizationOfDimLe T' A))
          ((companionIdealReduction hinv T' (principalizationOfDimLe T' A)).ideal
            (companionIdealReduction hinv T' (principalizationOfDimLe T' A)).length) T'.mult) :=
      isLocallyMonomialTriple_tripleAtLength_companionIdealReduction hG hinv hspec hT' hdim'
    have hIP := isPullbackSequenceOfBlowups_monomial_of_pullback_consolidated474 hinv hG.monomialInputs n A
      T T' g hT hbc (companionIdealReduction hinv T (principalizationOfDimLe T A)) (companionIdealReduction hinv T' (principalizationOfDimLe T' A)) c hmult
      hidealLastComap hlastBoundary hmonLow hmonUp
    obtain ⟨cc⟩ := hIP.nonempty_sequenceOfBlowupsPullback
    rw [orderReductionSeq_eq_of_nonempty hinv T (principalizationOfDimLe T A) hTne, orderReductionSeq_eq_of_nonempty hinv T' (principalizationOfDimLe T' A) hT'ne,
      orderReductionData_eq_append hinv T A, orderReductionData_eq_append hinv T' A]
    exact isPullbackBlowupSequence_append_of_two_fields g (companionIdealReduction hinv T (principalizationOfDimLe T A)) (orderReductionMonomialSequence hinv T A)
      (companionIdealReduction hinv T' (principalizationOfDimLe T' A)) (orderReductionMonomialSequence hinv T' A) hinv c
      (SequenceOfBlowupsPullback.toBlowupDataOfSeq cc)

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (n : ℕ) (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B) (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) {Y : Scheme.{u}} (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) (E' : List Y.IdealSheafData) (hE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.boundary.map fun D => D.comap g))
include hG hspec hT hdim hE

theorem orderReductionSeq_isPullbackBlowupSequence_mk (hT' : (MarkedIdealWithBoundary.mk k' Y q (T.ideal.comap g) T.mult E').IsAdmissible)
    (hdim' : (MarkedIdealWithBoundary.mk k' Y q (T.ideal.comap g) T.mult E').krullDimSucc ≤ n)
    (hbc : BaseChangeCompatible hinv A n T g k' q) :
    IsPullbackBlowupSequence g
      (orderReductionSeq hinv (MarkedIdealWithBoundary.mk k' Y q (T.ideal.comap g) T.mult E')
        (principalizationOfDimLe (MarkedIdealWithBoundary.mk k' Y q (T.ideal.comap g) T.mult E') A)).toSequenceOfBlowups
      (orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups :=
  orderReductionSeq_isPullbackBlowupSequence_of_comap_consolidated474 hG hinv n A B hspec T
    (MarkedIdealWithBoundary.mk k' Y q (T.ideal.comap g) T.mult E') g hT hT' hdim hdim' rfl rfl hE hbc

theorem orderReductionSeq_isPullbackBlowupSequence_pullbackOverField (hT' : ((T.pullbackOverField Y k' q g).withBoundary E').IsAdmissible)
    (hdim' : ((T.pullbackOverField Y k' q g).withBoundary E').krullDimSucc ≤ n)
    (hbc : BaseChangeCompatible hinv A n T g k' q) :
    IsPullbackBlowupSequence g
      (orderReductionSeq hinv ((T.pullbackOverField Y k' q g).withBoundary E')
        (principalizationOfDimLe ((T.pullbackOverField Y k' q g).withBoundary E') A)).toSequenceOfBlowups
      (orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups := by
  have hT2 : (MarkedIdealWithBoundary.mk k' Y q (T.ideal.comap g) T.mult E').IsAdmissible := hT'
  have hdim2 : (MarkedIdealWithBoundary.mk k' Y q (T.ideal.comap g) T.mult E').krullDimSucc ≤ n := hdim'
  exact orderReductionSeq_isPullbackBlowupSequence_mk hG hinv n A B hspec T hT hdim k' q g E' hE hT2 hdim2 hbc


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionTrivialCases
section


section

theorem SequenceOfBlowups.isomorphic_of_length_eq_zero {X : Scheme.{u}} (B B' : SequenceOfBlowups X)
    (h : B.length = 0) (h' : B'.length = 0) : B.Isomorphic B' := by
  have hl : (BlowupSequenceData.ofSequenceOfBlowups B).length = 0 := by
    rw [BlowupSequenceData.ofSequenceOfBlowups_length]; exact h
  have hl' : (BlowupSequenceData.ofSequenceOfBlowups B').length = 0 := by
    rw [BlowupSequenceData.ofSequenceOfBlowups_length]; exact h'
  have hz : ∀ i : ℕ, i ≤ (BlowupSequenceData.ofSequenceOfBlowups B).length → i = 0 := by
    intro i hi
    rw [hl] at hi
    exact Nat.le_zero.mp hi
  have hrfl1 : ∀ p : (BlowupSequenceData.ofSequenceOfBlowups B).obj 0 = (BlowupSequenceData.ofSequenceOfBlowups B).obj 0,
      eqToIso p = Iso.refl ((BlowupSequenceData.ofSequenceOfBlowups B).obj 0) := fun _ => rfl
  have hrfl2 : ∀ p : (BlowupSequenceData.ofSequenceOfBlowups B').obj 0 = (BlowupSequenceData.ofSequenceOfBlowups B').obj 0,
      eqToIso p = Iso.refl ((BlowupSequenceData.ofSequenceOfBlowups B').obj 0) := fun _ => rfl
  have key : (BlowupSequenceData.ofSequenceOfBlowups B).toSequenceOfBlowups.Isomorphic (BlowupSequenceData.ofSequenceOfBlowups B').toSequenceOfBlowups := by
    refine BlowupSequenceData.toSequenceOfBlowups_isomorphic_of_iso (BlowupSequenceData.ofSequenceOfBlowups B) (BlowupSequenceData.ofSequenceOfBlowups B')
      (by rw [hl, hl'])
      (fun i hi => eqToIso (congrArg (BlowupSequenceData.ofSequenceOfBlowups B).obj (hz i hi)) ≪≫
        (BlowupSequenceData.ofSequenceOfBlowups B).isoZero ≪≫ (BlowupSequenceData.ofSequenceOfBlowups B').isoZero.symm ≪≫
          eqToIso (congrArg (BlowupSequenceData.ofSequenceOfBlowups B').obj (hz i hi).symm)) ?_ ?_ ?_
    · simp only [hrfl1, hrfl2, Iso.trans_hom, Iso.refl_hom, Iso.symm_hom, Category.assoc,
        Category.id_comp, Category.comp_id, Iso.inv_hom_id]
    · intro i hi
      exact absurd hi (by rw [hl]; exact Nat.not_lt_zero i)
    · intro i hi
      exact absurd hi (by rw [hl]; exact Nat.not_lt_zero i)
  exact ((BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic B).symm.trans key).trans (BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic B')

theorem principalizationAssignment_mk_isomorphic (f : PrincipalizationAssignment.{u}) (T : MarkedIdealWithBoundary.{u})
    (p : T.scheme ⟶ Spec (CommRingCat.of T.base)) (I : T.scheme.IdealSheafData) (m : ℕ)
    (E : List T.scheme.IdealSheafData) (hp : p = T.structMap) (hI : I = T.ideal)
    (hm : m = T.mult) (hE : E = T.boundary) :
    (f { base := T.base, instField := T.instField, scheme := T.scheme, structMap := p,
          ideal := I, mult := m, boundary := E }).toSequenceOfBlowups.Isomorphic (f T).toSequenceOfBlowups := by
  subst hp
  subst hI
  subst hm
  subst hE
  exact SequenceOfBlowups.isomorphic_refl _

private theorem orderAtLeastLocus_append_eq_empty_consolidated475 {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (hinv : ComapIsoInvariance.{u}) (ht : 0 < t.length)
    (h : orderAtLeastLocus (t.ideal t.length) m = ∅) :
    orderAtLeastLocus ((s.append t hinv).ideal (s.append t hinv).length) m = ∅ := by
  have hlen : (s.append t hinv).length = s.length + t.length :=
    MarkedBlowupSequenceData.append_length s t hinv
  rw [hlen, MarkedBlowupSequenceData.append_ideal_length_add_length s t hinv ht]
  exact orderAtLeastLocus_comap_eqToHom_eq_empty _ _ _ h

theorem orderReductionSeq_isomorphic_of_boundary_nil (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (hmon : MonomialPrincipalizationHypotheses hinv) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (hE : T.boundary = [])
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) :
    (orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups.Isomorphic (A T).toSequenceOfBlowups := by
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = ∅
  · exact SequenceOfBlowups.isomorphic_of_length_eq_zero _ _
      (orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T A hcs)
      (hspec.trivial_of_coSupport_empty T hT hdim hord hcs)
  · obtain ⟨x₁, hx₁⟩ : (orderAtLeastLocus T.ideal T.mult).Nonempty := Set.nonempty_iff_ne_empty.mpr hcs
    have : Nonempty ↥T.scheme := ⟨x₁⟩
    obtain ⟨x₀, hx₀⟩ := exists_orderAt_eq_maxOrder T.ideal hord
    have hmax : maxOrder T.ideal = T.mult := by
      refine le_antisymm ?_ ?_
      · have h := hord x₀
        rw [hx₀] at h
        exact_mod_cast h
      · have h1 : (T.mult : ℕ∞) ≤ orderAt T.ideal x₁ := hx₁
        have h2 := orderAt_le_maxOrder T.ideal hord x₁
        have h3 : (T.mult : ℕ∞) ≤ ((maxOrder T.ideal : ℕ) : ℕ∞) := le_trans h1 h2
        exact_mod_cast h3
    have hJ0 : lastNonMonomialPart T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
        = T.ideal :=
      hG.nonMonomialPart_eq_ideal_of_boundary_eq_nil T hT hE
    have hμ0 : maxOrderNonMonomial T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
        = T.mult := by
      have h := congrArg (fun N => maxOrder N) hJ0
      exact h.trans hmax
    have hmem : ((maxOrderNonMonomial T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) : ℕ) : ℕ∞)
        ≤ orderAt (lastNonMonomialPart T
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)) x₁ := by
      rw [hμ0, hJ0]
      exact hx₁
    have hcont : NonMonomialOrderReductionContinues T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :=
      ⟨le_of_eq hμ0.symm, ⟨x₁, hmem⟩⟩
    have hlt := maxOrderNonMonomial_extendByNonMonomialPart_lt hG hinv hspec hT hdim
      (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hcont
    rw [hμ0] at hlt
    have hnot : ¬ NonMonomialOrderReductionContinues T (extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)) := by
      intro hc
      have h1 : T.mult ≤ maxOrderNonMonomial T (extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)) := hc.1
      omega
    have hzero : nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) 0
        = emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary := by
      simp only [nonMonomialOrderReductionIter]
    have hstepc : ∀ j : ℕ, NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) j) →
        nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) (j + 1)
          = extendByNonMonomialPart hinv T (principalizationOfDimLe T A) (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) j) := by
      intro j hj
      simp only [nonMonomialOrderReductionIter]
      split_ifs with h
      · rfl
      · exact absurd hj h
    have hstepn : ∀ j : ℕ, ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) j) →
        nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) (j + 1) = nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) j := by
      intro j hj
      simp only [nonMonomialOrderReductionIter]
      split_ifs with h
      · exact absurd h hj
      · rfl
    have hloop : ∀ j : ℕ, nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) (j + 1)
        = extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
            (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) := by
      intro j
      induction j with
      | zero =>
          rw [hstepc 0 (by rw [hzero]; exact hcont), hzero]
      | succ j ih =>
          rw [hstepn (j + 1) (by rw [ih]; exact hnot), ih]
    have hnonMonomialEq : nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)
        = extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
            (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) := by
      simp only [nonMonomialOrderReduction]
      exact hloop _
    have hconcat := extendByNonMonomialPart_eq_append hG hinv hspec hT hdim
      (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hcont
    have ht1pos : 0 < (continuationByNonMonomialPart hG hspec hT hdim
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hcont).length := by
      rw [continuationByNonMonomialPart_length hG hspec hT hdim _ hcont]
      exact seqAtEnd_lastNonMonomialPart_length_pos hG hspec hT hdim _ hcont
    have hcong : ∀ (Y : Scheme.{u}) (d : BlowupSequenceData Y) (I₁ I₂ : Y.IdealSheafData) (m₁ m₂ j : ℕ),
        I₁ = I₂ → m₁ = m₂ → d.controlledTransform I₁ m₁ j = d.controlledTransform I₂ m₂ j := by
      intro Y d I₁ I₂ m₁ m₂ j h1 h2
      rw [h1, h2]
    have hcs2 : ∀ (Y : Scheme.{u}) (Jy : Y.IdealSheafData) (m₁ m₂ : ℕ), m₁ = m₂ →
        orderAtLeastLocus Jy m₁ = ∅ → orderAtLeastLocus Jy m₂ = ∅ := by
      intro Y Jy m₁ m₂ h hh
      subst h
      exact hh
    have hnonMonomialLast : (nonMonomialTriple T
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)).IsAdmissible :=
      isAdmissible_nonMonomialTriple hG hT _ hcont
    have hdimLast : (nonMonomialTriple T
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)).krullDimSucc ≤ n :=
      le_trans (tripleAtLength_dim_le hG hT _ _ _) hdim
    have hboundaryLast : (nonMonomialTriple T
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)).IsOrderBoundedByMult := by
      rw [MarkedIdealWithBoundary.IsOrderBoundedByMult.eq_def]
      intro x
      exact orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) x
    have hresolves : MarkedSequenceOfBlowups.IsResolution
        (A (nonMonomialTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))) :=
      hspec.resolves _ hnonMonomialLast hdimLast hboundaryLast
    have hlocus : orderAtLeastLocus
        ((A (nonMonomialTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))).ideal
          (A (nonMonomialTriple T
            (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))).length) T.mult = ∅ := by
      have h := (MarkedSequenceOfBlowups.isResolution_iff _).mp hresolves
      rw [MarkedSequenceOfBlowups.lastIdeal_eq] at h
      exact hcs2 _ _ _ _ hμ0 h
    have hid : (continuationByNonMonomialPart hG hspec hT hdim
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hcont).ideal
        (continuationByNonMonomialPart hG hspec hT hdim
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hcont).length
        = (A (nonMonomialTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))).ideal
          (A (nonMonomialTriple T
            (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))).length := by
      have h1 := MarkedBlowupSequenceData.toBlowupSequenceData_controlledTransform_eq
        (MarkedBlowupSequenceData.ofMarkedSequence
          (A (nonMonomialTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))))
        (A (nonMonomialTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))).length
        (le_of_eq (MarkedBlowupSequenceData.ofMarkedSequence_length _).symm)
      have h2 := MarkedBlowupSequenceData.ofMarkedSequence_ideal
        (A (nonMonomialTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)))
        (A (nonMonomialTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))).length
      have h3 := hcong _
        (MarkedBlowupSequenceData.ofMarkedSequence
          (A (nonMonomialTriple T
            (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)))).toBlowupSequenceData
        ((emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).ideal
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).length)
        (lastNonMonomialPart T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))
        T.mult (maxOrderNonMonomial T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))
        (A (nonMonomialTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))).length
        hJ0.symm hμ0.symm
      exact h3.trans (h1.trans h2)
    have hG1 : orderAtLeastLocus ((continuationByNonMonomialPart hG hspec hT hdim
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hcont).ideal
        (continuationByNonMonomialPart hG hspec hT hdim
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hcont).length) T.mult = ∅ := by
      rw [hid]
      exact hlocus
    have hG2 : orderAtLeastLocus ((extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)).ideal
        (extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)).length) T.mult = ∅ := by
      rw [hconcat]
      exact orderAtLeastLocus_append_eq_empty_consolidated475 _ _ hinv ht1pos hG1
    have hmaxOn : ∀ (Y : Scheme.{u}) (N : Y.IdealSheafData),
        maxOrderOn N (∅ : Set ↥Y) = 0 := by
      intro Y N
      rw [maxOrderOn.eq_def]
      simp
    have hnc2 : ¬ CompanionIdealReductionContinues T (extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)) := by
      intro hc
      have h1 : 1 ≤ maxOrderOn
          (lastNonMonomialPart T (extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
            (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)))
          (orderAtLeastLocus ((extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
            (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)).ideal
            (extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
              (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)).length) T.mult) := hc
      rw [hG2, hmaxOn] at h1
      omega
    have hnc2' : ¬ CompanionIdealReductionContinues T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) := by
      rw [hnonMonomialEq]
      exact hnc2
    have hcompanionStep : ∀ (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (j : ℕ),
        ¬ CompanionIdealReductionContinues T (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s j) →
        companionIdealReductionIter hinv T (principalizationOfDimLe T A) s (j + 1)
          = companionIdealReductionIter hinv T (principalizationOfDimLe T A) s j := by
      intro s j hj
      simp only [companionIdealReductionIter]
      split_ifs with h
      · exact absurd h hj
      · rfl
    have hcompanionIter : ∀ j : ℕ, companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) j
        = nonMonomialOrderReduction hinv T (principalizationOfDimLe T A) := by
      intro j
      induction j with
      | zero => simp only [companionIdealReductionIter]
      | succ j ih =>
          rw [hcompanionStep _ j (by rw [ih]; exact hnc2'), ih]
    have hcompanionEq : companionIdealReduction hinv T (principalizationOfDimLe T A) = nonMonomialOrderReduction hinv T (principalizationOfDimLe T A) := by
      simp only [companionIdealReduction]
      exact hcompanionIter _
    have hG3 : orderAtLeastLocus ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal
        (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult = ∅ := by
      rw [hcompanionEq, hnonMonomialEq]
      exact hG2
    have hmonomialLen : (orderReductionMonomialSequence hinv T A).length = 0 := by
      show (MarkedBlowupSequenceData.ofMarkedSequence
        (monomialPrincipalization hinv (orderReductionMonomialTriple hinv T A))).length = 0
      rw [MarkedBlowupSequenceData.ofMarkedSequence_length]
      exact hmon.trivial_of_coSupport_empty _
        (isLocallyMonomialTriple_tripleAtLength_companionIdealReduction hG hinv hspec hT hdim) hG3
    have hAlg : orderReductionSeq hinv T (principalizationOfDimLe T A)
        = (orderReductionData hinv T (principalizationOfDimLe T A)).toMarkedSequenceOfBlowups := by
      unfold orderReductionSeq
      rw [if_neg hcs]
    rw [hAlg]
    have e1 : ((orderReductionData hinv T (principalizationOfDimLe T A)).toMarkedSequenceOfBlowups).toSequenceOfBlowups.Isomorphic
        ((companionIdealReduction hinv T (principalizationOfDimLe T A)).toMarkedSequenceOfBlowups).toSequenceOfBlowups := by
      rw [orderReductionData_eq_append hinv T A]
      exact MarkedBlowupSequenceData.append_isomorphic_of_length_eq_zero _ _ hinv hmonomialLen
    have e2 : ((companionIdealReduction hinv T (principalizationOfDimLe T A)).toMarkedSequenceOfBlowups).toSequenceOfBlowups.Isomorphic
        ((continuationByNonMonomialPart hG hspec hT hdim
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
          hcont).toMarkedSequenceOfBlowups).toSequenceOfBlowups := by
      rw [hcompanionEq, hnonMonomialEq, hconcat]
      exact MarkedBlowupSequenceData.emptyMarkedBlowupSequenceData_append_isomorphic T.structMap T.ideal T.mult T.boundary _ hinv
    have e3 : ((continuationByNonMonomialPart hG hspec hT hdim
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
          hcont).toMarkedSequenceOfBlowups).toSequenceOfBlowups.Isomorphic
        (A (nonMonomialTriple T
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))).toSequenceOfBlowups := by
      simp only [continuationByNonMonomialPart, BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
        MarkedBlowupSequenceData.blowupSequenceData_ofMarkedSequence]
      exact BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _
    have e4 : (A (nonMonomialTriple T
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))).toSequenceOfBlowups.Isomorphic
        (A T).toSequenceOfBlowups :=
      principalizationAssignment_mk_isomorphic A T
        ((emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).proj
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).length ≫ T.structMap)
        (lastNonMonomialPart T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))
        (maxOrderNonMonomial T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))
        ((emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).boundary
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).length)
        (by rw [emptyMarkedBlowupSequenceData_projectionToBase, Category.id_comp]) hJ0 hμ0 rfl
    exact e1.trans (e2.trans (e3.trans e4))


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SmoothBaseChangeCompatibility
section

open CategoryTheory.Limits

section

namespace MarkedPullbackSquare

variable {T : MarkedIdealWithBoundary.{u}} {Y : Scheme.{u}} {g : Y ⟶ T.scheme}

section
variable (S : MarkedPullbackSquare T g)

theorem smooth_verticalMap [Smooth g] :
    Smooth S.left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Smooth) S.isPullback.flip ‹Smooth g›

theorem verticalMap_comp_lowerStructMap (q : Y ⟶ Spec (CommRingCat.of T.base))
    (hq : g ≫ T.structMap = q) :
    S.left ≫ S.structMap = S.top ≫ q := by
  rw [← S.bottom_structMap, ← hq, ← Category.assoc, S.isPullback.w, Category.assoc]


end

theorem pullbackOverField_isAdmissible_of_sameNontrivialBoundary (hGeom : MonomialGeometryHypotheses.{u}) (S : MarkedPullbackSquare T g)
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (E : List S.topScheme.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap S.left) S.boundary) E)
    (hV : (S.upperTriple k' q E).IsAdmissible) :
    (S.lowerTriple.pullbackOverField S.topScheme k' (S.top ≫ q) S.left).IsAdmissible :=
  hGeom.withBoundary_valid (S.upperTriple k' q E) hV
    ((S.lowerTriple.pullbackOverField S.topScheme k' (S.top ≫ q) S.left).boundary) hE.symm

theorem orderAt_comap_verticalMap_le_of_forall_orderAt_le (S : MarkedPullbackSquare T g) (hT : T.IsAdmissible)
    (hg : OrderAtPullbackInvariant T g)
    (hord : ∀ x : ↥S.baseScheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) (y : ↥S.topScheme) :
    orderAt (S.ideal.comap S.left) y ≤ (S.mult : ℕ∞) :=
  S.orderAt_comap_verticalMap_le hT hg S.ideal _ hord y

end MarkedPullbackSquare

theorem baseChangeCompatible_of_smooth (hG : PrincipalizationGeometryHypotheses.{u}) (τ : ComapIsoInvariance.{u}) (n : ℕ)
    (F G : PrincipalizationAssignment.{u}) (hF : IsOrderReduction (fun d => d ≤ n) F G)
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) {Y : Scheme.{u}}
    (g : Y ⟶ T.scheme) [Smooth g]
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (hq : g ≫ T.structMap = q) :
    BaseChangeCompatible τ F n T g T.base q := by
  have hgord : OrderAtPullbackInvariant T g := orderAtPullbackInvariant_of_smooth T hT g
  refine ⟨?_, ?_, ?_, ?_, hgord⟩
  · intro S hord E hE hV hdimS
    have : Smooth S.left := MarkedPullbackSquare.smooth_verticalMap S
    exact hF.smooth_pullback S.lowerTriple S.valid (le_trans S.dim_le hdim) hord S.topScheme
      (S.top ≫ q) S.left (MarkedPullbackSquare.verticalMap_comp_lowerStructMap S q hq) E hE hV hdimS
      (fun y => MarkedPullbackSquare.orderAt_comap_verticalMap_le_of_forall_orderAt_le S hT hgord hord y)
  · exact inferInstance
  · intro S hmon E hE hmon'
    have : Smooth S.left := MarkedPullbackSquare.smooth_verticalMap S
    exact monomialPrincipalization_isPullbackBlowupSequence_of_smooth hG.monomialInputs τ S.lowerTriple hmon
      S.topScheme (S.top ≫ q) S.left (MarkedPullbackSquare.verticalMap_comp_lowerStructMap S q hq) E hE hmon'
  · intro S E hE hV
    have : Smooth S.left := MarkedPullbackSquare.smooth_verticalMap S
    exact hG.nonMonomialPart_comap_of_sameNontrivialBoundary S.lowerTriple S.valid S.topScheme
      (S.top ≫ q) S.left (MarkedPullbackSquare.verticalMap_comp_lowerStructMap S q hq)
      (MarkedPullbackSquare.pullbackOverField_isAdmissible_of_sameNontrivialBoundary hG.monomialInputs S T.base q E hE hV)
      E hE hV


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.TransformedComponentHypotheses
section


section

namespace MonomialStrictTransformComponents

structure TransformedComponentHypotheses : Prop where
  transformed_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J₀ : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J₀,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J₀).subschemeι ⁻¹' ⋃₀ 𝒞))
            (X' : Scheme.{u}) (π : X' ⟶ T.scheme),
            Blowup.IsBlowupAlongIdealSheaf π (componentUnionIdeal T.boundary J₀ 𝒞 hop) →
              ∀ (J : Finset (Fin T.boundary.length)),
                ∀ C' ∈ intersectionComponents
                    (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
                    (Finset.image
                      (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary) J),
                  ∀ ξ' : ↥X', IsGenericPoint ξ' C' →
                    ξ' ∉ (Blowup.exceptionalIdeal π
                        (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support ∧
                      ∃ C ∈ intersectionComponents T.boundary J,
                        C ∉ 𝒞 ∧
                          C' = closure (⇑π ⁻¹' C \
                              ((Blowup.exceptionalIdeal π
                                (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support :
                                  Set ↥X')) ∧
                            ∀ ξ : ↥T.scheme, IsGenericPoint ξ C → π ξ' = ξ
  strictTransform_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary,
                ∀ C' : Set ↥X',
                  IsIrreducibleComponentOf C' ((Blowup.strictTransform π Z D).support : Set ↥X') →
                    ∃ (ξ' : ↥X') (C : Set ↥T.scheme),
                      C' = closure ({ξ'} : Set ↥X') ∧
                        ξ' ∉ (Blowup.exceptionalIdeal π Z).support ∧
                          IsIrreducibleComponentOf C (D.support : Set ↥T.scheme) ∧
                            ¬ C ⊆ (Z.support : Set ↥T.scheme) ∧
                              C = closure ({π ξ'} : Set ↥T.scheme)

theorem strictTransformHypotheses_of_transformedComponents (h : TransformedComponentHypotheses.{u}) :
    StrictTransformCase.StrictTransformHypotheses.{u} where
  center_smooth := MonomialCenterGeometry.smooth_componentUnionIdeal
  center_snc := MonomialCenterGeometry.hasStrictNormalCrossingsWith_componentUnionIdeal
  blowup_total_transform := _root_.FunctorialResolution.EmbeddedResolution.comap_eq_strictTransform_mul_exceptionalIdeal_pow
  components_subset_divisor_iff := _root_.FunctorialResolution.EmbeddedResolution.intersectionComponents_subset_support_iff
  transformed_components := h.transformed_components
  strictTransform_components := h.strictTransform_components

end MonomialStrictTransformComponents


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.FieldExtensionBaseChange
section

open CategoryTheory.Limits

section

abbrev baseChangeProj (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] (f : T.base →+* L) :
    (T.baseChange L f).scheme ⟶ T.scheme :=
  pullback.fst T.structMap (specMapOfFieldHom T.base L f)

abbrev baseChangeStructMap (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] (f : T.base →+* L) :
    (T.baseChange L f).scheme ⟶ Spec (CommRingCat.of L) :=
  pullback.snd T.structMap (specMapOfFieldHom T.base L f)

private theorem comap_hom_comap_inv_eq_self_consolidated487 {A B : Scheme.{u}} (e : A ≅ B) (D : A.IdealSheafData) :
    (D.comap e.inv).comap e.hom = D := by
  rw [← Scheme.IdealSheafData.comap_comp, e.hom_inv_id]
  simp

private theorem nonMonomialPart_eq_of_isMonomialSplitting_unique_consolidated487 {X : Scheme.{u}} {E : List X.IdealSheafData}
    {I M N : X.IdealSheafData} (hs : IsMonomialSplitting E I M N)
    (hu : ∀ M' N' : X.IdealSheafData, IsMonomialSplitting E I M' N' → M = M' ∧ N = N') :
    nonMonomialPart E I = N := by
  have hex : ∃ q : X.IdealSheafData × X.IdealSheafData, IsMonomialSplitting E I q.1 q.2 :=
    ⟨(M, N), hs⟩
  have hch : IsMonomialSplitting E I hex.choose.1 hex.choose.2 := hex.choose_spec
  have hNN := (hu _ _ hch).2
  unfold nonMonomialPart monomialSplitting
  rw [dif_pos hex]
  exact hNN.symm

private theorem markedIdealWithBoundary_mk_congr_consolidated487 {k : Type u} [Field k] {A : Scheme.{u}}
    {p q : A ⟶ Spec (CommRingCat.of k)} {I J : A.IdealSheafData} {m n : ℕ}
    {E F : List A.IdealSheafData} (hp : p = q) (hI : I = J) (hm : m = n) (hE : E = F) :
    MarkedIdealWithBoundary.mk k A p I m E = MarkedIdealWithBoundary.mk k A q J n F := by
  subst hp; subst hI; subst hm; subst hE; rfl

private theorem isPullbackBlowupSequence_of_eq_of_heq_consolidated487 (F : PrincipalizationAssignment.{u}) (B : MarkedIdealWithBoundary.{u})
    {W U : MarkedIdealWithBoundary.{u}} (h : W = U) (g : W.scheme ⟶ B.scheme) (g' : U.scheme ⟶ B.scheme)
    (hg : HEq g g')
    (hh : IsPullbackBlowupSequence g (F W).toSequenceOfBlowups (F B).toSequenceOfBlowups) :
    IsPullbackBlowupSequence g' (F U).toSequenceOfBlowups (F B).toSequenceOfBlowups := by
  subst h
  have hgg := eq_of_heq hg
  subst hgg
  exact hh

theorem krullDimSucc_eq_of_iso {A B : Scheme.{u}} (e : A ≅ B) : krullDimSucc A = krullDimSucc B := by
  have hh := (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isHomeomorph
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]
  congr 1
  exact hh.topologicalKrullDim_eq

theorem isAdmissible_comap_of_iso {k : Type u} [Field k] {A B : Scheme.{u}} (e : A ≅ B)
    (s : B ⟶ Spec (CommRingCat.of k)) (J : B.IdealSheafData) (m : ℕ)
    (E : List B.IdealSheafData)
    (h : (MarkedIdealWithBoundary.mk k B s J m E).IsAdmissible) :
    (MarkedIdealWithBoundary.mk k A (e.hom ≫ s) (J.comap e.hom) m
      (E.map (fun D : B.IdealSheafData => D.comap e.hom))).IsAdmissible := by
  have hsm : Smooth s := h.smooth
  have hqc : QuasiCompact s := h.quasiCompact
  exact
    { charZero := h.charZero
      locallyOfFiniteType := inferInstance
      nonzeroOnComponents := nonzeroOnComponents_comap_iso_hom e J h.nonzeroOnComponents
      one_le_mult := h.one_le_mult
      quasiCompact := inferInstance
      smooth := inferInstance
      snc := inStrictNormalCrossingPosition_comap_iso s e E h.snc }

theorem orderAtPullbackInvariant_verticalMap {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    {Y : Scheme.{u}} {g : Y ⟶ T.scheme} (hg : OrderAtPullbackInvariant T g)
    (S : MarkedPullbackSquare T g) :
    OrderAtPullbackInvariant S.lowerTriple S.left := by
  intro B b pB IB EB hvalid hbp Q a b' hpb A y
  refine hg B (b ≫ S.bottom) pB IB EB ?_ ?_ Q a (b' ≫ S.top) ?_ A y
  · exact
      { charZero := hvalid.charZero
        locallyOfFiniteType := hvalid.locallyOfFiniteType
        nonzeroOnComponents := hvalid.nonzeroOnComponents
        one_le_mult := hT.one_le_mult
        quasiCompact := hvalid.quasiCompact
        smooth := hvalid.smooth
        snc := hvalid.snc }
  · rw [Category.assoc, S.bottom_structMap]
    exact hbp
  · exact hpb.paste_vert S.isPullback

section
variable (hG : PrincipalizationGeometryHypotheses.{u})
include hG

theorem nonMonomialPartBaseChange_of_flat (T : MarkedIdealWithBoundary.{u})
    {Y : Scheme.{u}} (g : Y ⟶ T.scheme) [Flat g] (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) :
    NonMonomialPartBaseChange T g k' q := by
  intro S E hE hV
  have : Flat S.left := S.flat_verticalMap
  obtain ⟨M, N, hMN⟩ := hG.splitting_exists S.lowerTriple S.valid
  have hu1 : ∀ M' N' : S.baseScheme.IdealSheafData,
      IsMonomialSplitting S.boundary S.ideal M' N' → M = M' ∧ N = N' :=
    fun M' N' h' => hG.splitting_unique S.lowerTriple S.valid M N M' N' hMN h'
  have h1 := isMonomialSplitting_comap_of_flat S.left hMN
  have hMNcomap : IsMonomialSplitting E (S.ideal.comap S.left) (M.comap S.left)
      (N.comap S.left) := (isMonomialSplitting_congr hE _ _ _).1 h1
  have hu2 : ∀ M' N' : S.topScheme.IdealSheafData,
      IsMonomialSplitting E (S.ideal.comap S.left) M' N' →
        M.comap S.left = M' ∧ N.comap S.left = N' :=
    fun M' N' h' => hG.splitting_unique (S.upperTriple k' q E) hV (M.comap S.left)
      (N.comap S.left) M' N' hMNcomap h'
  rw [nonMonomialPart_eq_of_isMonomialSplitting_unique_consolidated487 hMNcomap hu2, nonMonomialPart_eq_of_isMonomialSplitting_unique_consolidated487 hMN hu1]

theorem monomialPrincipalizationBaseChange_of_flat (τ : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) {Y : Scheme.{u}} (g : Y ⟶ T.scheme)
    [Flat g] (hg : OrderAtPullbackInvariant T g) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) :
    MonomialPrincipalizationBaseChange τ T g k' q := by
  intro S hsmooth E hE hSm'
  have : Flat S.left := S.flat_verticalMap
  exact monomialPrincipalization_isPullbackBlowupSequence_of_flat hG.monomialInputs τ S.lowerTriple S.topScheme k'
    (S.top ≫ q) S.left E hsmooth hE.symm hSm'
    (fun B b pB hbp IB EB hv Q a b' hpb A z =>
      orderAtPullbackInvariant_verticalMap hT hg S B b pB IB EB hv hbp Q a b' hpb A z)


end

namespace MarkedPullbackSquare

theorem isPullback_comp_baseChangeStructMap {T : MarkedIdealWithBoundary.{u}} {L : Type u} [Field L]
    {f : T.base →+* L} (S : MarkedPullbackSquare T (baseChangeProj T L f)) :
    IsPullback S.left (S.top ≫ baseChangeStructMap T L f) S.structMap (specMapOfFieldHom T.base L f) := by
  have h := S.isPullback.paste_vert
    (IsPullback.of_hasPullback T.structMap (specMapOfFieldHom T.base L f))
  rw [S.bottom_structMap] at h
  exact h

end MarkedPullbackSquare

section
variable (hG : PrincipalizationGeometryHypotheses.{u})
include hG

theorem commutesWithBaseChange_baseChangeProj_of_isOrderReduction (n : ℕ)
    (F G : PrincipalizationAssignment.{u}) (hF : IsOrderReduction (fun d => d ≤ n) F G)
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (L : Type u) [Field L] [CharZero L]
    (f : T.base →+* L) :
    PrincipalizationBaseChange F n T (baseChangeProj T L f) L (baseChangeStructMap T L f) := by
  intro S hord E hE hV hd
  have hgstable : OrderAtPullbackInvariant T (baseChangeProj T L f) :=
    orderAtPullbackInvariant_baseChange_field hG T hT L f
  have hsq : IsPullback S.left (S.top ≫ baseChangeStructMap T L f) S.structMap
      (specMapOfFieldHom T.base L f) := MarkedPullbackSquare.isPullback_comp_baseChangeStructMap S
  obtain ⟨e, hfst, hsnd⟩ :
      ∃ e : S.topScheme ≅ pullback S.structMap (specMapOfFieldHom T.base L f),
        e.hom ≫ pullback.fst S.structMap (specMapOfFieldHom T.base L f) = S.left ∧
          e.hom ≫ pullback.snd S.structMap (specMapOfFieldHom T.base L f) =
            S.top ≫ baseChangeStructMap T L f :=
    ⟨hsq.isoPullback, hsq.isoPullback_hom_fst, hsq.isoPullback_hom_snd⟩
  have hinvfst : e.inv ≫ S.left = pullback.fst S.structMap (specMapOfFieldHom T.base L f) := by
    rw [← hfst, Iso.inv_hom_id_assoc]
  have hinvsnd : e.inv ≫ (S.top ≫ baseChangeStructMap T L f) =
      pullback.snd S.structMap (specMapOfFieldHom T.base L f) := by
    rw [← hsnd, Iso.inv_hom_id_assoc]
  have h2gen : ∀ A : S.baseScheme.IdealSheafData,
      (A.comap S.left).comap e.inv =
        A.comap (pullback.fst S.structMap (specMapOfFieldHom T.base L f)) := by
    intro A
    have h : (A.comap S.left).comap e.inv = A.comap (e.inv ≫ S.left) := by simp
    rw [h, hinvfst]
  have hideal : (S.ideal.comap (pullback.fst S.structMap (specMapOfFieldHom T.base L f))).comap e.hom
      = S.ideal.comap S.left := by
    have h : (S.ideal.comap (pullback.fst S.structMap (specMapOfFieldHom T.base L f))).comap e.hom
        = S.ideal.comap (e.hom ≫ pullback.fst S.structMap (specMapOfFieldHom T.base L f)) := by simp
    rw [h, hfst]
  have hmapinv : ∀ l : List S.baseScheme.IdealSheafData,
      List.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv)
          (List.map (fun D : S.baseScheme.IdealSheafData => D.comap S.left) l)
        = List.map (fun D : S.baseScheme.IdealSheafData =>
            D.comap (pullback.fst S.structMap (specMapOfFieldHom T.base L f))) l := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih => simp only [List.map_cons, ih, h2gen a]
  have hmapback : ∀ l : List S.topScheme.IdealSheafData,
      List.map (fun D : (pullback S.structMap (specMapOfFieldHom T.base L f)).IdealSheafData =>
          D.comap e.hom) (List.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv) l)
        = l := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih => simp only [List.map_cons, ih, comap_hom_comap_inv_eq_self_consolidated487 e a]
  have hdimS : S.lowerTriple.krullDimSucc ≤ n := le_trans S.dim_le hdim
  have hOBS : S.lowerTriple.IsOrderBoundedByMult := (MarkedIdealWithBoundary.isOrderBoundedByMult_iff _).mpr hord
  have hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (S.lowerTriple.baseChange L f).boundary
      (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv)) := by
    have h := MarkedIdealWithBoundary.SameNontrivialBoundary.map (fun D => D.comap e.inv) (by simp) hE
    rw [hmapinv] at h
    exact h
  have h0 := isAdmissible_comap_of_iso (k := L) e.symm (S.top ≫ baseChangeStructMap T L f)
    (S.ideal.comap S.left) S.mult E hV
  simp only [Iso.symm_hom] at h0
  rw [hinvsnd, h2gen S.ideal] at h0
  have hval' : ((S.lowerTriple.baseChange L f).withBoundary
      (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv))).IsAdmissible := h0
  have hdim' : ((S.lowerTriple.baseChange L f).withBoundary
      (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv))).krullDimSucc ≤ n := by
    have hde : krullDimSucc S.topScheme = krullDimSucc (pullback S.structMap (specMapOfFieldHom T.base L f)) :=
      krullDimSucc_eq_of_iso e
    show krullDimSucc (pullback S.structMap (specMapOfFieldHom T.base L f)) ≤ n
    rw [← hde]
    exact hd
  have hOB'fun : ∀ y : ↥(pullback S.structMap (specMapOfFieldHom T.base L f)),
      orderAt (S.ideal.comap (pullback.fst S.structMap (specMapOfFieldHom T.base L f))) y
        ≤ (S.mult : ℕ∞) := by
    intro y
    have hy := S.orderAt_comap_verticalMap_le_of_forall_orderAt_le hT hgstable hord (e.inv y)
    have h3 : orderAt ((S.ideal.comap S.left).comap e.symm.hom) y
        = orderAt (S.ideal.comap S.left) (e.symm.hom y) :=
      orderAt_comap_of_isOpenImmersion e.symm.hom _ y
    simp only [Iso.symm_hom] at h3
    rw [h2gen S.ideal] at h3
    rw [h3]
    exact hy
  have hOB' : ((S.lowerTriple.baseChange L f).withBoundary
      (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv))).IsOrderBoundedByMult :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff _).mpr hOB'fun
  have hpull := hF.base_change S.lowerTriple S.valid hdimS hOBS L f
    (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv)) hBE hval' hdim' hOB'
  have htri : ((((S.lowerTriple.baseChange L f).withBoundary
        (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv))).pullbackAlong
        S.topScheme (S.top ≫ baseChangeStructMap T L f) e.hom).withBoundary E)
      = S.upperTriple L (baseChangeStructMap T L f) E :=
    markedIdealWithBoundary_mk_congr_consolidated487 rfl hideal rfl rfl
  have hBE2 : MarkedIdealWithBoundary.SameNontrivialBoundary
      ((((S.lowerTriple.baseChange L f).withBoundary
        (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv))).pullbackAlong
        S.topScheme (S.top ≫ baseChangeStructMap T L f) e.hom)).boundary E := by
    show MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.map (fun D : (pullback S.structMap (specMapOfFieldHom T.base L f)).IdealSheafData =>
        D.comap e.hom) (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv))) E
    rw [hmapback]
    exact MarkedIdealWithBoundary.SameNontrivialBoundary.refl E
  have hval2 : (((((S.lowerTriple.baseChange L f).withBoundary
        (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv))).pullbackAlong
        S.topScheme (S.top ≫ baseChangeStructMap T L f) e.hom)).withBoundary E).IsAdmissible := by
    rw [htri]
    exact hV
  have hdim2 : (((((S.lowerTriple.baseChange L f).withBoundary
        (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv))).pullbackAlong
        S.topScheme (S.top ≫ baseChangeStructMap T L f) e.hom)).withBoundary E).krullDimSucc ≤ n := hd
  have hOB2 : (((((S.lowerTriple.baseChange L f).withBoundary
        (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv))).pullbackAlong
        S.topScheme (S.top ≫ baseChangeStructMap T L f) e.hom)).withBoundary E).IsOrderBoundedByMult := by
    rw [htri]
    exact (MarkedIdealWithBoundary.isOrderBoundedByMult_iff _).mpr
      (fun y => S.orderAt_comap_verticalMap_le_of_forall_orderAt_le hT hgstable hord y)
  have hsmE : Smooth e.hom := inferInstance
  have hsjE : AlgebraicGeometry.Surjective e.hom := inferInstance
  have hstrict := @IsOrderReduction.smooth_pullback_strict (fun d => d ≤ n) F G hF
    ((S.lowerTriple.baseChange L f).withBoundary
      (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv)))
    hval' hdim' hOB' S.topScheme (S.top ≫ baseChangeStructMap T L f) e.hom hsmE hsjE hsnd E hBE2
    hval2 hdim2 hOB2
  have hres := hpull.comp_isStrictPullbackSequenceOfBlowups hstrict
  rw [hfst] at hres
  exact isPullbackBlowupSequence_of_eq_of_heq_consolidated487 F S.lowerTriple htri S.left S.left HEq.rfl hres

theorem baseChangeCompatible_baseChangeProj_of_isOrderReduction (τ : ComapIsoInvariance.{u}) (n : ℕ)
    (F G : PrincipalizationAssignment.{u}) (hF : IsOrderReduction (fun d => d ≤ n) F G)
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (L : Type u) [Field L] [CharZero L]
    (f : T.base →+* L) :
    BaseChangeCompatible τ F n T (baseChangeProj T L f) L (baseChangeStructMap T L f) := by
  have hflat : Flat (baseChangeProj T L f) :=
    inferInstanceAs
      (Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f)))
  exact ⟨commutesWithBaseChange_baseChangeProj_of_isOrderReduction hG n F G hF T hT hdim L f, hflat,
    monomialPrincipalizationBaseChange_of_flat hG τ T hT (baseChangeProj T L f)
      (orderAtPullbackInvariant_baseChange_field hG T hT L f) L (baseChangeStructMap T L f),
    nonMonomialPartBaseChange_of_flat hG T (baseChangeProj T L f) L (baseChangeStructMap T L f),
    orderAtPullbackInvariant_baseChange_field hG T hT L f⟩


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometricPrincipalization
section


section

theorem MonomialStrictTransformComponents.transformedComponentHypotheses : MonomialStrictTransformComponents.TransformedComponentHypotheses.{u} where
  transformed_components := intersectionComponents_transformedBoundary_of_isBlowupAlongIdealSheaf
  strictTransform_components := exists_eq_closure_of_isIrreducibleComponentOf_strictTransform

theorem principalizationGeometryHypotheses : PrincipalizationGeometryHypotheses.{u} :=
  geometricHypotheses_of_orderReductionHypotheses
    (OrderReductionHypotheses.of_strictTransformHypotheses
      (StrictTransformCase.strictTransformHypotheses_of_residualHypotheses
        (MonomialStrictTransformComponents.strictTransformHypotheses_of_transformedComponents
          MonomialStrictTransformComponents.transformedComponentHypotheses)))


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
section

open TopologicalSpace

open scoped Classical

section

namespace DivisorReduction

noncomputable abbrev lowerIdealWithoutBlowup (T : MarkedIdealWithBoundary.{u}) : T.scheme.IdealSheafData :=
  T.ideal.comap (𝟙 T.scheme)

noncomputable abbrev lowerBoundaryWithoutBlowup (T : MarkedIdealWithBoundary.{u}) : List T.scheme.IdealSheafData :=
  T.boundary.map (fun D => D.comap (𝟙 T.scheme))

@[simp]
theorem lowerBoundaryWithoutBlowup_eq (T : MarkedIdealWithBoundary.{u}) : lowerBoundaryWithoutBlowup T = T.boundary := by
  simp [lowerBoundaryWithoutBlowup]

noncomputable abbrev lowerIdealAfterBlowup (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    T.scheme.IdealSheafData :=
  residualByPow ((T.ideal.comap (𝟙 T.scheme)).comap (𝟙 T.scheme))
    (Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.mult

noncomputable abbrev lowerBoundaryAfterBlowup (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    List T.scheme.IdealSheafData :=
  (T.boundary.map (fun D => D.comap (𝟙 T.scheme))).map
      (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) ++
    [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)]

noncomputable def ambientTowerOfLowerResolution (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (hdn : (restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < T.krullDimSucc ∧ IsNoetherian T.scheme)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence
      (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdn.1)).toBlowupSequenceData.CentersContainNoComponent) :
    BlowupSequenceData T.scheme :=
  letI := hdn.2
  ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdn.1)).toBlowupSequenceData
    hres hno hpr

section
variable (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)

theorem containedComponentsIdeal_eq_ker_ι_comp_subschemeι_of_isOpen (h : IsOpen {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
      connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}) :
    containedComponentsIdeal T j hj =
      Scheme.Hom.ker
        (@AlgebraicGeometry.Scheme.Opens.ι (T.boundary.get ⟨j, hj⟩).subscheme
            ⟨{x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
                connectedComponent x ⊆
                  ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}, h⟩ ≫
          (T.boundary.get ⟨j, hj⟩).subschemeι) :=
  containedComponentsIdeal_eq_ker T j hj h

theorem containedComponentsIdeal_eq_top_of_not_isOpen_setOf_connectedComponent (h : ¬ IsOpen {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
      connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}) :
    containedComponentsIdeal T j hj = ⊤ :=
  containedComponentsIdeal_eq_top_of_not_isOpen T j hj h


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u}) (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) (hj : j < T.boundary.length) (hcs : orderAtLeastLocus T.ideal T.mult ≠ (∅ : Set ↥T.scheme))
include hcs

theorem divisorReductionSeq_eq_of_containedComponentsIdeal_eq_top (hZ : containedComponentsIdeal T j hj = ⊤)
    (hdn : (restrictToBoundaryDivisor T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T)).krullDimSucc < T.krullDimSucc ∧
      IsNoetherian T.scheme)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence (alg (restrictToBoundaryDivisor T j hj (lowerIdealWithoutBlowup T)
      (lowerBoundaryWithoutBlowup T)) hdn.1)).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientTowerOfLowerResolution hres hno T alg j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) hdn hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    divisorReductionSeq hres hno T alg j =
      ((ambientTowerOfLowerResolution hres hno T alg j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) hdn hpr).toMarkedBlowupSequenceData
        T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups := by
  have := hdn.2
  refine (divisorReductionSeq_eq_liftSeqFromDivisor_of_eq_top hres hno T alg j hj hcs hZ).trans ?_
  exact liftSeqFromDivisor_eq_toMarkedSequence hres hno T alg j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) id
    hdn.1 hpr hmk

theorem divisorReductionSeq_eq_of_isBlowupAlongIdealSheaf (hZ : containedComponentsIdeal T j hj ≠ ⊤)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (hdn : (restrictToBoundaryDivisor T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)).krullDimSucc < T.krullDimSucc ∧
      IsNoetherian T.scheme)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence
      (alg (restrictToBoundaryDivisor T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj))
        hdn.1)).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientTowerOfLowerResolution hres hno T alg j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
          hdn hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    divisorReductionSeq hres hno T alg j =
      ((BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
          (ambientTowerOfLowerResolution hres hno T alg j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
            hdn hpr)).toMarkedBlowupSequenceData
        T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups := by
  have := hdn.2
  refine (divisorReductionSeq_eq_liftSeqFromDivisor_prepend hres hno T alg j hj hcs hZ hb).trans ?_
  exact liftSeqFromDivisor_eq_toMarkedSequence hres hno T alg j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
    (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb) hdn.1 hpr hmk


end

end DivisorReduction

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
section

open CategoryTheory.Limits

section

namespace DivisorReduction

noncomputable abbrev restrictToDivisor (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    MarkedIdealWithBoundary.{u} :=
  restrictToBoundaryDivisor T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T)

noncomputable abbrev restrictTwistedToDivisor (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    MarkedIdealWithBoundary.{u} :=
  restrictToBoundaryDivisor T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)

theorem isNoetherian_scheme_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) :
    IsNoetherian T.scheme :=
  hV.isNoetherian

noncomputable def ambientBlowupSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) :
    BlowupSequenceData T.scheme :=
  ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr

noncomputable def embeddingIntoAmbient (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (n : ℕ) :
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.obj n ⟶
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj n :=
  embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr n

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups) (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)

theorem ambientBlowupSeq_center_eq_imageIdealSheaf (n : ℕ) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n =
      imageIdealSheaf (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) (s.center n) :=
  ambientBlowupSequence_center (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr n

theorem isClosedImmersion_embeddingIntoAmbient
    (n : ℕ) :
    IsClosedImmersion (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) :=
  isClosedImmersion_embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr n

theorem ambientBlowupSeq_length :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length = s.length :=
  ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr


end

end DivisorReduction

structure DivisorReductionTerminationProperties (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) : Prop where
  exists_ideal_mul_preIdeal_pow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → T.IsOrderBoundedByMult →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      ∃ J : T.scheme.IdealSheafData,
        DivisorReduction.containedComponentsIdeal T j hj ^ T.mult * J = T.ideal
  isMarked_pushedTop : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent),
        (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary
  isMarked_pushedPre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
      ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)),
      (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent),
        (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
            (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
          T.structMap T.ideal T.mult T.boundary
  isBlowup_id_preIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
  lowerTriple_dim_lt : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    (orderAtLeastLocus T.ideal T.mult).Nonempty →
    ∀ (j : ℕ) (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData)
      (E₀ : List T.scheme.IdealSheafData),
      (DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < T.krullDimSucc
  valid_lowerTop : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible
  valid_lowerPre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ → (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible
  orderAt_ctrlIdeal_le_top : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (i : ℕ),
        i ≤ s.length →
        ∀ x : ↥((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).obj i),
          orderAt ((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform T.ideal T.mult i) x
            ≤ (T.mult : ℕ∞)
  orderAt_ctrlIdeal_le_pre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
      ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)),
      (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (i : ℕ),
        i ≤ s.length + 1 →
        ∀ x : ↥((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
            (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).obj i),
          orderAt ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
            (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform T.ideal T.mult i) x
            ≤ (T.mult : ℕ∞)
  coSupport_inter_ker_eq_empty_top : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent),
        orderAtLeastLocus (s.ideal s.length) T.mult = (∅ : Set ↥(s.schemeAt s.length)) →
        (orderAtLeastLocus ((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
              (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform T.ideal T.mult s.length) T.mult ∩
            ((Scheme.Hom.ker (DivisorReduction.embeddingIntoAmbient hres hno T j hj
                (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr
                s.length)).support :
              Set ↥((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
                (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).obj s.length))) = ∅
  coSupport_inter_ker_eq_empty_pre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
      ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)),
      (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent),
        orderAtLeastLocus (s.ideal s.length) T.mult = (∅ : Set ↥(s.schemeAt s.length)) →
        (orderAtLeastLocus ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
                  (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform T.ideal T.mult
              (s.length + 1)) T.mult ∩
            ((Scheme.Hom.ker (DivisorReduction.embeddingIntoAmbient hres hno T j hj
                (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr
                s.length)).support :
              Set ↥((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr).obj s.length))) = ∅
  properCenters : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → 1 ≤ T.mult → ∀ s : T.SequenceOfBlowups,
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent
  isPullbackSeq_ambientTower : ∀ (X Y S S' : Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y)
      (φ : Y ⟶ X) (ψ : S' ⟶ S) [IsClosedImmersion σ]
      [IsClosedImmersion σ'] [Flat φ]
      [IsNoetherian X] [IsNoetherian Y],
      IsPullback σ' ψ φ σ →
      ∀ (d : BlowupSequenceData S) (d' : BlowupSequenceData S') (hc : d.CentersContainNoComponent)
        (hc' : d'.CentersContainNoComponent),
        IsPullbackBlowupSequence ψ d'.toSequenceOfBlowups d.toSequenceOfBlowups →
        IsPullbackBlowupSequence φ (ambientBlowupSequence σ' d' hres hno hc').toSequenceOfBlowups
          (ambientBlowupSequence σ d hres hno hc).toSequenceOfBlowups
  isStrictPullbackSeq_ambientTower : ∀ (X Y S S' : Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y)
      (φ : Y ⟶ X) (ψ : S' ⟶ S) [IsClosedImmersion σ]
      [IsClosedImmersion σ'] [Flat φ]
      [IsNoetherian X] [IsNoetherian Y],
      IsPullback σ' ψ φ σ →
      ∀ (d : BlowupSequenceData S) (d' : BlowupSequenceData S') (hc : d.CentersContainNoComponent)
        (hc' : d'.CentersContainNoComponent),
        IsStrictPullbackBlowupSeq ψ d'.toSequenceOfBlowups d.toSequenceOfBlowups →
        IsStrictPullbackBlowupSeq φ (ambientBlowupSequence σ' d' hres hno hc').toSequenceOfBlowups
          (ambientBlowupSequence σ d hres hno hc).toSequenceOfBlowups
  comap_ctrlIdeal_top : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (i : ℕ),
        i ≤ s.length →
        ((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
              (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform T.ideal T.mult i).comap
            (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
              (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr i) = s.ideal i
  comap_ctrlIdeal_pre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
      ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)),
      (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (i : ℕ),
        i ≤ s.length →
        ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
              (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform T.ideal T.mult
              (i + 1)).comap
            (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr i) = s.ideal i
  preIdeal_baseChange : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L), (T.baseChange L f).IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length)
      (hj' : j < (T.baseChange L f).boundary.length),
      DivisorReduction.containedComponentsIdeal (T.baseChange L f) j hj' =
        (DivisorReduction.containedComponentsIdeal T j hj).comap
          (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
  preIdeal_pullbackAlong : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
      (T.pullbackAlong Y q h).IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length)
      (hj' : j < (T.pullbackAlong Y q h).boundary.length),
      DivisorReduction.containedComponentsIdeal (T.pullbackAlong Y q h) j hj' =
        (DivisorReduction.containedComponentsIdeal T j hj).comap h
  preIdeal_eq_top_of_imageIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length)
      (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData), T.mult = 1 →
      (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          ((T.boundary.eraseIdx j).map
            (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι))).IsAdmissible →
      T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J →
      DivisorReduction.containedComponentsIdeal T j hj = ⊤
  isOpen_preLocus : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      IsOpen {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
        connectedComponent x ⊆
          ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}
  smooth_preIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      Smooth
        ((DivisorReduction.containedComponentsIdeal T j hj).subschemeι ≫ T.structMap)
  hasSNCWith_preIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      HasStrictNormalCrossingsWith T.structMap (DivisorReduction.containedComponentsIdeal T j hj) T.boundary
  support_preIdeal_subset : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      (((DivisorReduction.containedComponentsIdeal T j hj).support : Set ↥T.scheme)) ⊆
        orderAtLeastLocus T.ideal T.mult

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformRestriction
section


section

section
variable {S S' X X' : Scheme.{u}} (i : S ⟶ X) [IsClosedImmersion i] (i' : S' ⟶ X') (p : X' ⟶ X) (q : S' ⟶ S) (hsq : i' ≫ p = q ≫ i) (Z : S.IdealSheafData)
include hsq

theorem comap_exceptionalIdeal_of_closedImmersionSquare
    :
    (Blowup.exceptionalIdeal p (Z.map i)).comap i' = Blowup.exceptionalIdeal q Z := by
  rw [Blowup.exceptionalIdeal_eq_comap, Blowup.exceptionalIdeal_eq_comap, ← Scheme.IdealSheafData.comap_comp, hsq,
    Scheme.IdealSheafData.comap_comp, Blowup.comap_map_of_isClosedImmersion]

theorem comap_controlledTransform_of_closedImmersionSquare
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal q Z))
    (m : ℕ) (A : X.IdealSheafData) (A' : X'.IdealSheafData) (J' : S'.IdealSheafData)
    (hA : Blowup.exceptionalIdeal p (Z.map i) ^ m * A' = A.comap p)
    (hJ : Blowup.exceptionalIdeal q Z ^ m * J' = (A.comap i).comap q) :
    A'.comap i' = J' := by
  have h1 : (Blowup.exceptionalIdeal p (Z.map i) ^ m * A').comap i' = (A.comap p).comap i' := by
    rw [hA]
  rw [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow,
    comap_exceptionalIdeal_of_closedImmersionSquare i i' p q hsq Z,
    ← Scheme.IdealSheafData.comap_comp, hsq, Scheme.IdealSheafData.comap_comp] at h1
  have h2 : Blowup.exceptionalIdeal q Z ^ m * A'.comap i' = Blowup.exceptionalIdeal q Z ^ m * J' := by
    rw [h1, hJ]
  exact (hcart.pow m).eq_of_mul_eq_mul h2


end

namespace DivisorReduction

variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})
    (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData)
    (E₀ : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)

theorem embeddingIntoAmbient_comp_blowupMorphism (t : ℕ) :
    embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t =
      s.transitionMapSucc t ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t :=
  embeddingIntoAmbientBlowupSequence_succ_comp_map (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t

instance instIsClosedImmersionPushedEmb (t : ℕ) :
    IsClosedImmersion (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) :=
  isClosedImmersion_embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t

theorem embeddingIntoAmbient_zero :
    embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0 =
      s.isoZero.hom ≫ (T.boundary.get ⟨j, hj⟩).subschemeι :=
  embeddingIntoAmbientBlowupSequence_zero (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr

private theorem ambientBlowupSeq_isoObjZero_hom_consolidated315 :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom = 𝟙 T.scheme :=
  congrArg Iso.hom (ambientBlowupSequence_isoObjZero (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr)

theorem comap_controlledTransform_embeddingIntoAmbient (t : ℕ) (ht : t ≤ s.length)
    (hdiv : ∀ i < t, ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center i) ^ T.mult * B =
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult i).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i))) :
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.ideal t := by
  revert ht hdiv
  induction t with
  | zero =>
    intro ht hdiv
    have e1 : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult 0).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0) =
          I₀.comap (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0 ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom) := by
      rw [BlowupSequenceData.controlledTransform_zero]
      exact (Scheme.IdealSheafData.comap_comp ..).symm
    have e2 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0 ≫
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom =
          s.isoZero.hom ≫ (T.boundary.get ⟨j, hj⟩).subschemeι := by
      rw [ambientBlowupSeq_isoObjZero_hom_consolidated315 hres hno T j hj I₀ E₀ s hpr,
        embeddingIntoAmbient_zero hres hno T j hj I₀ E₀ s hpr]
      exact Category.comp_id _
    have e3 : s.ideal 0 =
        I₀.comap (s.isoZero.hom ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) :=
      s.ideal_zero.trans (Scheme.IdealSheafData.comap_comp ..).symm
    exact e1.trans ((congrArg (fun f => I₀.comap f) e2).trans e3.symm)
  | succ t IH =>
    intro ht hdiv
    have hts : t < s.length := ht
    have hIH : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.ideal t :=
      IH (Nat.le_of_succ_le ht) (fun i hi => hdiv i (Nat.lt_succ_of_lt hi))
    have h0 := BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr) I₀ T.mult t
      (hdiv t (Nat.lt_succ_self t))
    rw [ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I₀ E₀ s hpr t] at h0
    have hJ : Blowup.exceptionalIdeal (s.transitionMapSucc t) (s.center t) ^ T.mult * s.ideal (t + 1) =
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
          (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)).comap (s.transitionMapSucc t) := by
      rw [hIH]
      exact s.ideal_succ t hts
    exact comap_controlledTransform_of_closedImmersionSquare
      (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)
      (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1))
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) (s.transitionMapSucc t)
      (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr t) (s.center t)
      (isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal (s.isBlowupAlongIdealSheaf_blowupMorphism t hts)) T.mult
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult (t + 1))
      (s.ideal (t + 1)) h0 hJ

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DerivBalancedFactor
section

open TopologicalSpace


section
variable {X : Scheme.{u}}

private theorem exists_affineOpen_ideal_eq_top_of_not_mem_support_consolidated313 (I : X.IdealSheafData) (y : ↥X) (hy : y ∉ I.support) :
    ∃ V : X.affineOpens, y ∈ V.1 ∧ I.ideal V = ⊤ := by
  obtain ⟨U, hyU, -⟩ :=
    Scheme.exists_affineOpens_mem_le (X := X) (x := y) (U := ⊤) trivial
  have hny := hy
  rw [AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := U) hyU,
    AlgebraicGeometry.Scheme.mem_zeroLocus_iff] at hny
  push Not at hny
  obtain ⟨s, hs, hys⟩ := hny
  refine ⟨X.affineBasicOpen s, hys, ?_⟩
  let _ : Algebra Γ(X, U.1) Γ(X, X.basicOpen s) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom.toAlgebra
  have hloc : IsLocalization.Away s Γ(X, X.basicOpen s) := U.2.isLocalization_basicOpen s
  have hunit : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen s) s) :=
    IsLocalization.map_units (M := Submonoid.powers s) Γ(X, X.basicOpen s)
      ⟨s, Submonoid.mem_powers s⟩
  have hmem : algebraMap Γ(X, U.1) Γ(X, X.basicOpen s) s ∈ I.ideal (X.affineBasicOpen s) := by
    rw [← I.map_ideal_basicOpen U s]
    exact Ideal.mem_map_of_mem _ hs
  exact Ideal.eq_top_of_isUnit_mem _ hmem hunit

theorem not_mem_support_of_mem_support_of_pow_mul (Z I I₀ : X.IdealSheafData) (m : ℕ) (hfac : I = Z ^ m * I₀)
    (hord : ∀ x : ↥X, orderAt I x ≤ (m : ℕ∞)) {x : ↥X} (hx : x ∈ Z.support) :
    x ∉ I₀.support := by
  intro hx0
  have hZ : stalkIdeal Z x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (mem_support_iff_stalkIdeal_le_maximalIdeal Z x).mp hx
  have hI0 : stalkIdeal I₀ x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (mem_support_iff_stalkIdeal_le_maximalIdeal I₀ x).mp hx0
  have hIle : stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ (m + 1) := by
    rw [hfac, stalkIdeal_mul, stalkIdeal_pow, pow_succ]
    exact Ideal.mul_mono (Ideal.pow_right_mono hZ m) hI0
  have h1 := (le_orderAt_iff I x (m + 1)).mpr hIle
  have h3 : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := le_trans h1 (hord x)
  have h4 : m + 1 ≤ m := by exact_mod_cast h3
  omega


end

theorem isDerivBalanced_of_pow_mul (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (Z I I₀ : X.IdealSheafData) (m : ℕ) (hfac : I = Z ^ m * I₀)
    (hord : ∀ x : ↥X, orderAt I x ≤ (m : ℕ∞)) (hbal : IsDerivBalanced k p I m) :
    IsDerivBalanced k p I₀ m := by
  refine (isDerivBalanced_iff k p I₀ m).mpr ?_
  intro i hi
  refine le_of_forall_exists_affineOpen ?_
  intro y
  by_cases hyZ : y ∈ Z.support
  · obtain ⟨V, hyV, hV⟩ := exists_affineOpen_ideal_eq_top_of_not_mem_support_consolidated313 I₀ y
      (not_mem_support_of_mem_support_of_pow_mul Z I I₀ m hfac hord hyZ)
    refine ⟨V, hyV, ?_⟩
    have htop : (I₀ ^ (m - i)).ideal V = ⊤ := by
      rw [Scheme.IdealSheafData.ideal_pow]
      show I₀.ideal V ^ (m - i) = ⊤
      rw [hV, ← Ideal.one_eq_top, one_pow]
    rw [htop]
    exact le_top
  · obtain ⟨V, hyV, hV⟩ := exists_affineOpen_ideal_eq_top_of_not_mem_support_consolidated313 Z y hyZ
    refine ⟨V, hyV, ?_⟩
    have hIV : I.ideal V = I₀.ideal V := by
      rw [hfac, Scheme.IdealSheafData.ideal_mul, Scheme.IdealSheafData.ideal_pow]
      show Z.ideal V ^ m * I₀.ideal V = I₀.ideal V
      rw [hV, ← Ideal.one_eq_top, one_pow, one_mul]
    have hder : (derivIdealSheafIterate k p i I).ideal V
        = (derivIdealSheafIterate k p i I₀).ideal V := by
      rw [derivIdealSheafIterate_ideal, derivIdealSheafIterate_ideal, hIV]
    have hb : ((derivIdealSheafIterate k p i I).ideal V) ^ m ≤ (I.ideal V) ^ (m - i) := by
      have hb0 := Scheme.IdealSheafData.le_def.mp ((isDerivBalanced_iff k p I m).mp hbal i hi) V
      rwa [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_pow] at hb0
    rw [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_pow]
    show ((derivIdealSheafIterate k p i I₀).ideal V) ^ m ≤ (I₀.ideal V) ^ (m - i)
    rw [← hIV, ← hder]
    exact hb

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionStepProperties
section

open CategoryTheory.Limits TopologicalSpace

section

section
variable (X : Scheme.{u})

private theorem topologicalKrullDim_ne_bot_of_nonempty_consolidated316 [Nonempty ↥X] :
    topologicalKrullDim ↥X ≠ ⊥ := by
  intro hb
  have hb' : Order.krullDim (IrreducibleCloseds ↥X) = ⊥ := hb
  have hE : IsEmpty (IrreducibleCloseds ↥X) := Order.krullDim_eq_bot_iff.mp hb'
  obtain ⟨x⟩ := ‹Nonempty ↥X›
  exact hE.false ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩

theorem one_le_krullDimSucc [Nonempty ↥X] : 1 ≤ krullDimSucc X := by
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]
  obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp (topologicalKrullDim_ne_bot_of_nonempty_consolidated316 X)
  rw [← hn, withBotSuccToNat_coe]
  exact Nat.le_add_left 1 _

theorem krullDimSucc_eq_zero_of_isEmpty [IsEmpty ↥X] : krullDimSucc X = 0 := by
  have hE : IsEmpty (IrreducibleCloseds ↥X) := by
    constructor
    intro C
    obtain ⟨x, -⟩ := C.2.1
    exact isEmptyElim x
  have h : topologicalKrullDim ↥X = ⊥ := Order.krullDim_eq_bot_iff.mpr hE
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, h, withBotSuccToNat_bot]


end

section
variable {X : Scheme.{u}} (D : X.IdealSheafData)

private theorem nonempty_homeomorph_subscheme_range_subschemeι_consolidated316 :
    Nonempty (↥D.subscheme ≃ₜ ↥(Set.range ⇑D.subschemeι)) :=
  ⟨(Scheme.Hom.isClosedEmbedding D.subschemeι).toIsEmbedding.toHomeomorph⟩

private theorem isClosed_range_subschemeι_consolidated316 :
    IsClosed (Set.range ⇑D.subschemeι) :=
  (Scheme.Hom.isClosedEmbedding D.subschemeι).isClosed_range


end

theorem krullDimSucc_subscheme_lt_of_isLocallyGeneratedByNonZeroDivisor (X : Scheme.{u}) [Nonempty ↥X]
    (hfin : topologicalKrullDim ↥X < ⊤) (D : X.IdealSheafData) (hD : Blowup.IsLocallyGeneratedByNonZeroDivisor D) :
    krullDimSucc D.subscheme < krullDimSucc X := by
  rcases isEmpty_or_nonempty ↥D.subscheme with hem | hne
  · have := hem
    rw [krullDimSucc_eq_zero_of_isEmpty D.subscheme]
    exact lt_of_lt_of_le Nat.zero_lt_one (one_le_krullDimSucc X)
  · have := hne
    obtain ⟨e⟩ := nonempty_homeomorph_subscheme_range_subschemeι_consolidated316 D
    have hrange : Set.range ⇑D.subschemeι = (D.support : Set ↥X) :=
      Scheme.IdealSheafData.range_subschemeι D
    refine krullDimSucc_lt_of_homeomorph_isClosed X D.subscheme (Set.range ⇑D.subschemeι)
      (isClosed_range_subschemeι_consolidated316 D) ?_ ?_ hfin e
    · exact Set.range_nonempty _
    · intro C hC hsub
      rw [hrange] at hsub
      exact hD.not_irreducibleComponent_subset_support hC hsub

theorem isOpen_setOf_connectedComponent_subset {X : Type u} [TopologicalSpace X]
    [NoetherianSpace X] (P : Set X) : IsOpen {x : X | connectedComponent x ⊆ P} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨connectedComponent x, ?_, Blowup.isOpen_connectedComponent_of_noetherianSpace X x,
    mem_connectedComponent⟩
  intro y hy
  show connectedComponent y ⊆ P
  rw [← connectedComponent_eq hy]
  exact hx

section
variable (T : MarkedIdealWithBoundary.{u})

theorem centersContainNoComponent_of_isAdmissible (hV : T.IsAdmissible) (_hm : 1 ≤ T.mult)
    (s : T.SequenceOfBlowups) : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent :=
  MarkedSequenceOfBlowups.centersContainNoComponent_ofMarkedSequence effectiveCartierSupportContainsNoComponent hV s

theorem isOpen_setOf_connectedComponent_subset_orderAtLeastLocus (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    IsOpen {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
      connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult} := by
  have := hV.isNoetherian
  have hN : NoetherianSpace ↥T.scheme := inferInstance
  obtain ⟨e⟩ := nonempty_homeomorph_subscheme_range_subschemeι_consolidated316 (T.boundary.get ⟨j, hj⟩)
  have : NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    noetherianSpace_of_surjective _ e.symm.continuous e.symm.surjective
  exact isOpen_setOf_connectedComponent_subset _

private theorem get_mem_boundary_consolidated316 (j : ℕ) (hj : j < T.boundary.length) :
    T.boundary.get ⟨j, hj⟩ ∈ T.boundary := by
  simp

theorem dim_restrictToBoundaryDivisor_lt (hV : T.IsAdmissible)
    (hne : (orderAtLeastLocus T.ideal T.mult).Nonempty) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData) :
    (DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < T.krullDimSucc := by
  obtain ⟨x, -⟩ := hne
  have : Nonempty ↥T.scheme := ⟨x⟩
  have hsd : IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) :=
    hV.snc.1 _ (get_mem_boundary_consolidated316 T j hj)
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (T.boundary.get ⟨j, hj⟩) := hsd.1
  exact krullDimSucc_subscheme_lt_of_isLocallyGeneratedByNonZeroDivisor T.scheme
    hV.topologicalKrullDim_lt_top (T.boundary.get ⟨j, hj⟩) hcart


end

structure DivisorReductionStepProperties (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) : Prop where
  exists_ideal_mul_preIdeal_pow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → T.IsOrderBoundedByMult →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      ∃ J : T.scheme.IdealSheafData,
        DivisorReduction.containedComponentsIdeal T j hj ^ T.mult * J = T.ideal
  isMarked_pushedTop : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent),
        (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary
  isMarked_pushedPre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
      ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)),
      (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent),
        (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
            (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
          T.structMap T.ideal T.mult T.boundary
  isBlowup_id_preIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
  valid_lowerTop : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible
  valid_lowerPre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ → (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible
  orderAt_ctrlIdeal_le_top : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (i : ℕ),
        i ≤ s.length →
        ∀ x : ↥((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).obj i),
          orderAt ((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform T.ideal T.mult i) x
            ≤ (T.mult : ℕ∞)
  orderAt_ctrlIdeal_le_pre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
      ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)),
      (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (i : ℕ),
        i ≤ s.length + 1 →
        ∀ x : ↥((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
            (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).obj i),
          orderAt ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
            (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform T.ideal T.mult i) x
            ≤ (T.mult : ℕ∞)
  coSupport_inter_ker_eq_empty_top : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent),
        orderAtLeastLocus (s.ideal s.length) T.mult = (∅ : Set ↥(s.schemeAt s.length)) →
        (orderAtLeastLocus ((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
              (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform T.ideal T.mult s.length) T.mult ∩
            ((Scheme.Hom.ker (DivisorReduction.embeddingIntoAmbient hres hno T j hj
                (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr
                s.length)).support :
              Set ↥((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
                (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).obj s.length))) = ∅
  coSupport_inter_ker_eq_empty_pre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
      ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)),
      (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent),
        orderAtLeastLocus (s.ideal s.length) T.mult = (∅ : Set ↥(s.schemeAt s.length)) →
        (orderAtLeastLocus ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
                  (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform T.ideal T.mult
              (s.length + 1)) T.mult ∩
            ((Scheme.Hom.ker (DivisorReduction.embeddingIntoAmbient hres hno T j hj
                (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr
                s.length)).support :
              Set ↥((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr).obj s.length))) = ∅
  isPullbackSeq_ambientTower : ∀ (X Y S S' : Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y)
      (φ : Y ⟶ X) (ψ : S' ⟶ S) [IsClosedImmersion σ]
      [IsClosedImmersion σ'] [Flat φ]
      [IsNoetherian X] [IsNoetherian Y],
      IsPullback σ' ψ φ σ →
      ∀ (d : BlowupSequenceData S) (d' : BlowupSequenceData S') (hc : d.CentersContainNoComponent)
        (hc' : d'.CentersContainNoComponent),
        IsPullbackBlowupSequence ψ d'.toSequenceOfBlowups d.toSequenceOfBlowups →
        IsPullbackBlowupSequence φ (ambientBlowupSequence σ' d' hres hno hc').toSequenceOfBlowups
          (ambientBlowupSequence σ d hres hno hc).toSequenceOfBlowups
  isStrictPullbackSeq_ambientTower : ∀ (X Y S S' : Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y)
      (φ : Y ⟶ X) (ψ : S' ⟶ S) [IsClosedImmersion σ]
      [IsClosedImmersion σ'] [Flat φ]
      [IsNoetherian X] [IsNoetherian Y],
      IsPullback σ' ψ φ σ →
      ∀ (d : BlowupSequenceData S) (d' : BlowupSequenceData S') (hc : d.CentersContainNoComponent)
        (hc' : d'.CentersContainNoComponent),
        IsStrictPullbackBlowupSeq ψ d'.toSequenceOfBlowups d.toSequenceOfBlowups →
        IsStrictPullbackBlowupSeq φ (ambientBlowupSequence σ' d' hres hno hc').toSequenceOfBlowups
          (ambientBlowupSequence σ d hres hno hc).toSequenceOfBlowups
  comap_ctrlIdeal_top : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (i : ℕ),
        i ≤ s.length →
        ((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
              (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform T.ideal T.mult i).comap
            (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
              (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr i) = s.ideal i
  comap_ctrlIdeal_pre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
      ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)),
      (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (i : ℕ),
        i ≤ s.length →
        ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
              (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform T.ideal T.mult
              (i + 1)).comap
            (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr i) = s.ideal i
  preIdeal_baseChange : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L), (T.baseChange L f).IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length)
      (hj' : j < (T.baseChange L f).boundary.length),
      DivisorReduction.containedComponentsIdeal (T.baseChange L f) j hj' =
        (DivisorReduction.containedComponentsIdeal T j hj).comap
          (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
  preIdeal_pullbackAlong : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
      (T.pullbackAlong Y q h).IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length)
      (hj' : j < (T.pullbackAlong Y q h).boundary.length),
      DivisorReduction.containedComponentsIdeal (T.pullbackAlong Y q h) j hj' =
        (DivisorReduction.containedComponentsIdeal T j hj).comap h
  preIdeal_eq_top_of_imageIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length)
      (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData), T.mult = 1 →
      (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          ((T.boundary.eraseIdx j).map
            (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι))).IsAdmissible →
      T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J →
      DivisorReduction.containedComponentsIdeal T j hj = ⊤
  smooth_preIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      Smooth
        ((DivisorReduction.containedComponentsIdeal T j hj).subschemeι ≫ T.structMap)
  hasSNCWith_preIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      HasStrictNormalCrossingsWith T.structMap (DivisorReduction.containedComponentsIdeal T j hj) T.boundary
  support_preIdeal_subset : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      (((DivisorReduction.containedComponentsIdeal T j hj).support : Set ↥T.scheme)) ⊆
        orderAtLeastLocus T.ideal T.mult

theorem DivisorReductionStepProperties.toDivisorReductionTerminationProperties {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} (h : DivisorReductionStepProperties hres hno) :
    DivisorReductionTerminationProperties hres hno where
  exists_ideal_mul_preIdeal_pow := h.exists_ideal_mul_preIdeal_pow
  isMarked_pushedTop := h.isMarked_pushedTop
  isMarked_pushedPre := h.isMarked_pushedPre
  isBlowup_id_preIdeal := h.isBlowup_id_preIdeal
  lowerTriple_dim_lt := fun T hV hne j hj I₀ E₀ => dim_restrictToBoundaryDivisor_lt T hV hne j hj I₀ E₀
  valid_lowerTop := h.valid_lowerTop
  valid_lowerPre := h.valid_lowerPre
  orderAt_ctrlIdeal_le_top := h.orderAt_ctrlIdeal_le_top
  orderAt_ctrlIdeal_le_pre := h.orderAt_ctrlIdeal_le_pre
  coSupport_inter_ker_eq_empty_top := h.coSupport_inter_ker_eq_empty_top
  coSupport_inter_ker_eq_empty_pre := h.coSupport_inter_ker_eq_empty_pre
  properCenters := fun T hV hm s => centersContainNoComponent_of_isAdmissible T hV hm s
  isPullbackSeq_ambientTower := h.isPullbackSeq_ambientTower
  isStrictPullbackSeq_ambientTower := h.isStrictPullbackSeq_ambientTower
  comap_ctrlIdeal_top := h.comap_ctrlIdeal_top
  comap_ctrlIdeal_pre := h.comap_ctrlIdeal_pre
  preIdeal_baseChange := h.preIdeal_baseChange
  preIdeal_pullbackAlong := h.preIdeal_pullbackAlong
  preIdeal_eq_top_of_imageIdeal := h.preIdeal_eq_top_of_imageIdeal
  isOpen_preLocus := fun T hV j hj => isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T hV j hj
  smooth_preIdeal := h.smooth_preIdeal
  hasSNCWith_preIdeal := h.hasSNCWith_preIdeal
  support_preIdeal_subset := h.support_preIdeal_subset


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryComponentsInOrderLocus
section


section

namespace DivisorReduction

private theorem le_ker_comp_subschemeι_consolidated335 {X : Scheme.{u}} (D : X.IdealSheafData) {W : Scheme.{u}}
    (g : W ⟶ D.subscheme) : D ≤ AlgebraicGeometry.Scheme.Hom.ker (g ≫ D.subschemeι) :=
  (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι D).ge.trans
    (AlgebraicGeometry.Scheme.Hom.le_ker_comp g _)

abbrev boundaryComponentsInOrderLocus (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    Set ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
  {x | connectedComponent x ⊆
    ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' FunctorialResolution.EmbeddedResolution.orderAtLeastLocus T.ideal T.mult}

abbrev boundaryComponentsInOrderLocusOpens (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (h : IsOpen (boundaryComponentsInOrderLocus T j hj)) :
    (T.boundary.get ⟨j, hj⟩).subscheme.Opens :=
  ⟨boundaryComponentsInOrderLocus T j hj, h⟩

section
variable (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
include hV

theorem one_le_mult_of_isAdmissible : 1 ≤ T.mult :=
  hV.one_le_mult

theorem isSmoothDivisor_boundary_comap_isoObjZero (j : ℕ)
    (hj : j < T.boundary.length) (s : T.SequenceOfBlowups) :
    IsSmoothDivisor (s.projectionToSpec 0) ((T.boundary.get ⟨j, hj⟩).comap s.isoZero.hom) := by
  have hmem : T.boundary.get ⟨j, hj⟩ ∈ T.boundary := by
    simp only [List.get_eq_getElem]
    exact List.getElem_mem hj
  have hD : IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) :=
    ((inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hV.snc).1 _ hmem
  rw [MarkedSequenceOfBlowups.projectionToSpec_zero]
  exact PrincipalizationIsoTransport.isSmoothDivisor_comap_iso T.structMap s.toSequenceOfBlowups.isoZero _ hD


end

section
variable (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)

theorem containedComponentsIdeal_eq_ker_of_isOpen (h : IsOpen (boundaryComponentsInOrderLocus T j hj)) :
    containedComponentsIdeal T j hj =
      AlgebraicGeometry.Scheme.Hom.ker
        ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) :=
  containedComponentsIdeal_eq_ker_ι_comp_subschemeι_of_isOpen T j hj h

theorem containedComponentsIdeal_eq_top_of_not_isOpen_locus (h : ¬ IsOpen (boundaryComponentsInOrderLocus T j hj)) :
    containedComponentsIdeal T j hj = ⊤ :=
  containedComponentsIdeal_eq_top_of_not_isOpen_setOf_connectedComponent T j hj h

theorem support_containedComponentsIdeal_subset_support_boundary :
    ((containedComponentsIdeal T j hj).support : Set ↥T.scheme) ⊆
      ((T.boundary.get ⟨j, hj⟩).support : Set ↥T.scheme) := by
  by_cases h : IsOpen (boundaryComponentsInOrderLocus T j hj)
  · rw [containedComponentsIdeal_eq_ker_of_isOpen T j hj h]
    exact SetLike.coe_subset_coe.mpr
      (AlgebraicGeometry.Scheme.IdealSheafData.support_antitone
        (le_ker_comp_subschemeι_consolidated335 (T.boundary.get ⟨j, hj⟩) (boundaryComponentsInOrderLocusOpens T j hj h).ι))
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen_locus T j hj h,
      AlgebraicGeometry.Scheme.IdealSheafData.support_top, TopologicalSpace.Closeds.coe_bot]
    exact Set.empty_subset _


end

def PreimageSupportEqComponentsInOrderLocus (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) : Prop :=
  ∀ h : IsOpen (boundaryComponentsInOrderLocus T j hj),
    ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹'
        ((AlgebraicGeometry.Scheme.Hom.ker
            ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫
              (T.boundary.get ⟨j, hj⟩).subschemeι)).support : Set ↥T.scheme) =
      boundaryComponentsInOrderLocus T j hj

theorem isOpen_preimage_support_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (hc : PreimageSupportEqComponentsInOrderLocus T j hj) :
    IsOpen (⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹'
      ((containedComponentsIdeal T j hj).support : Set ↥T.scheme)) := by
  by_cases h : IsOpen (boundaryComponentsInOrderLocus T j hj)
  · rw [containedComponentsIdeal_eq_ker_of_isOpen T j hj h, hc h]
    exact h
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen_locus T j hj h,
      AlgebraicGeometry.Scheme.IdealSheafData.support_top, TopologicalSpace.Closeds.coe_bot,
      Set.preimage_empty]
    exact isOpen_empty

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdeal
section

open TopologicalSpace

section

theorem noetherianSpace_boundary_subscheme (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme := by
  have := hV.isNoetherian
  exact (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding
    (T.boundary.get ⟨j, hj⟩).subschemeι).toIsEmbedding.toIsInducing.noetherianSpace

abbrev divisorComponentsInOrderLocus (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    Set ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
  {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
    connectedComponent x ⊆
      ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}

theorem isClosed_divisorComponentsInOrderLocus (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    IsClosed (divisorComponentsInOrderLocus T j hj) := by
  have := noetherianSpace_boundary_subscheme T hV j hj
  exact TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset
    ↥(T.boundary.get ⟨j, hj⟩).subscheme
    (⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult)

section
variable (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)

theorem containedComponentsIdeal_eq_openSubschemeKer (h : IsOpen (divisorComponentsInOrderLocus T j hj)) :
    DivisorReduction.containedComponentsIdeal T j hj =
      openSubschemeKer (T.boundary.get ⟨j, hj⟩) ⟨divisorComponentsInOrderLocus T j hj, h⟩ :=
  DivisorReduction.containedComponentsIdeal_eq_ker T j hj h

theorem containedComponentsIdeal_eq_top_of_not_isOpen (h : ¬ IsOpen (divisorComponentsInOrderLocus T j hj)) :
    DivisorReduction.containedComponentsIdeal T j hj = ⊤ :=
  DivisorReduction.containedComponentsIdeal_eq_top_of_not_isOpen T j hj h


end

section
variable (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ) (hj : j < T.boundary.length)
include hV

theorem isSmoothDivisor_boundary_get :
    IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) := by
  have hmem : T.boundary.get ⟨j, hj⟩ ∈ T.boundary := by
    simp only [List.get_eq_getElem]
    exact List.getElem_mem hj
  exact ((inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hV.snc).1 _ hmem

theorem support_containedComponentsIdeal_subset_orderAtLeastLocus :
    (((DivisorReduction.containedComponentsIdeal T j hj).support : Set ↥T.scheme)) ⊆ orderAtLeastLocus T.ideal T.mult := by
  by_cases h : IsOpen (divisorComponentsInOrderLocus T j hj)
  · have hcl : IsClosed (((⟨divisorComponentsInOrderLocus T j hj, h⟩ :
        (T.boundary.get ⟨j, hj⟩).subscheme.Opens) :
          Set ↥(T.boundary.get ⟨j, hj⟩).subscheme)) := isClosed_divisorComponentsInOrderLocus T hV j hj
    rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h,
      support_openSubschemeKer (T.boundary.get ⟨j, hj⟩) ⟨divisorComponentsInOrderLocus T j hj, h⟩ hcl]
    rintro y ⟨x, hx, rfl⟩
    have hx' : connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult := hx
    exact hx' mem_connectedComponent
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj h]
    intro x hx
    have hx' : x ∈ (⊤ : T.scheme.IdealSheafData).support := hx
    rw [mem_support_iff_stalkIdeal_ne_top] at hx'
    exact absurd (stalkIdeal_top x) hx'

theorem smooth_subschemeι_containedComponentsIdeal_comp :
    Smooth ((DivisorReduction.containedComponentsIdeal T j hj).subschemeι ≫ T.structMap) := by
  have hsmp : Smooth T.structMap := hV.smooth
  by_cases h : IsOpen (divisorComponentsInOrderLocus T j hj)
  · have hsm : Smooth
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
      ((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).1
        (isSmoothDivisor_boundary_get T hV j hj)).2
    rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h]
    exact smooth_subschemeι_openSubschemeKer_comp (T.boundary.get ⟨j, hj⟩)
      ⟨divisorComponentsInOrderLocus T j hj, h⟩ (isClosed_divisorComponentsInOrderLocus T hV j hj) T.structMap
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj h]
    exact ((isSmoothDivisor_iff T.structMap (⊤ : T.scheme.IdealSheafData)).1
      (isSmoothDivisor_top T.structMap)).2

theorem exists_etaleChart_containedComponentsIdeal (x : ↥T.scheme)
    (hx : x ∈ (DivisorReduction.containedComponentsIdeal T j hj).support) :
    ∃ (U : T.scheme.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart T.structMap U n)
      (a : ℕ → Option (Fin n)) (b : Fin n),
      a j = some b ∧
      (∀ (i : ℕ) (hi : i < T.boundary.length), a i = none →
        restrictIdeal (T.boundary.get ⟨i, hi⟩) U = ⊤) ∧
      (∀ (i : ℕ) (hi : i < T.boundary.length) (t : Fin n), a i = some t →
        restrictIdeal (T.boundary.get ⟨i, hi⟩) U = c.coordIdeal {t}) ∧
      (∀ (i i' : ℕ), i < T.boundary.length → i' < T.boundary.length →
        ∀ t : Fin n, a i = some t → a i' = some t → i = i') ∧
      restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj) U = c.coordIdeal {b} := by
  classical
  by_cases hopen : IsOpen (divisorComponentsInOrderLocus T j hj)
  · have hWclosed : IsClosed (divisorComponentsInOrderLocus T j hj) := isClosed_divisorComponentsInOrderLocus T hV j hj
    have hpre : DivisorReduction.containedComponentsIdeal T j hj =
        openSubschemeKer (T.boundary.get ⟨j, hj⟩)
          (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ : (T.boundary.get ⟨j, hj⟩).subscheme.Opens) :=
      containedComponentsIdeal_eq_openSubschemeKer T j hj hopen
    have h1 : x ∈ ((openSubschemeKer (T.boundary.get ⟨j, hj⟩)
        (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ :
          (T.boundary.get ⟨j, hj⟩).subscheme.Opens)).support : Set ↥T.scheme) := by
      rw [← hpre]
      exact hx
    rw [support_openSubschemeKer (T.boundary.get ⟨j, hj⟩)
      (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ : (T.boundary.get ⟨j, hj⟩).subscheme.Opens) hWclosed] at h1
    obtain ⟨U₀, hxU₀, hU₀⟩ := exists_opens_preimage_subschemeι_le (T.boundary.get ⟨j, hj⟩)
      (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ : (T.boundary.get ⟨j, hj⟩).subscheme.Opens) x h1
    obtain ⟨U₁, hxU₁, n, c, a, hinj, hnone, hsome⟩ :=
      (((inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hV.snc).2 x).exists_etaleChart
    have hUle : U₀ ⊓ U₁ ≤ U₁ := inf_le_right
    have hxU : x ∈ U₀ ⊓ U₁ := ⟨hxU₀, hxU₁⟩
    have hpreU : ((T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹ᵁ (U₀ ⊓ U₁)) ≤
        (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ : (T.boundary.get ⟨j, hj⟩).subscheme.Opens) := by
      intro y hy
      exact hU₀ hy.1
    have hrestr : restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj) (U₀ ⊓ U₁) =
        restrictIdeal (T.boundary.get ⟨j, hj⟩) (U₀ ⊓ U₁) := by
      rw [hpre]
      exact restrictIdeal_openSubschemeKer_of_preimage_le _ _ hWclosed _ hpreU
    have hajne : a j ≠ none := by
      intro haj
      have h2 : restrictIdeal (T.boundary.get ⟨j, hj⟩) U₁ = ⊤ := by
        simpa only [List.get_eq_getElem] using hnone j hj haj
      have h3 : restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj) (U₀ ⊓ U₁) = ⊤ := by
        rw [hrestr]
        exact restrictIdeal_eq_top_of_le _ hUle h2
      exact notMem_support_of_restrictIdeal_eq_top _ _ x hxU h3 hx
    obtain ⟨b, hb⟩ : ∃ b : Fin n, a j = some b := by
      cases h : a j with
      | none => exact absurd h hajne
      | some b => exact ⟨b, rfl⟩
    refine ⟨U₀ ⊓ U₁, hxU, n, c.restrict hUle, a, b, hb, ?_, ?_, ?_, ?_⟩
    · intro i hi hai
      refine restrictIdeal_eq_top_of_le _ hUle ?_
      simpa only [List.get_eq_getElem] using hnone i hi hai
    · intro i hi t hai
      refine restrictIdeal_eq_restrict_coordIdeal_of_le hUle c _ {t} ?_
      simpa only [List.get_eq_getElem] using hsome i hi t hai
    · intro i i' hi hi' t h4 h5
      exact hinj i hi i' hi' t h4 h5
    · rw [hrestr]
      refine restrictIdeal_eq_restrict_coordIdeal_of_le hUle c _ {b} ?_
      simpa only [List.get_eq_getElem] using hsome j hj b hb
  · exfalso
    rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj hopen] at hx
    exact (mem_support_iff_stalkIdeal_ne_top (⊤ : T.scheme.IdealSheafData) x).1 hx
      (stalkIdeal_top x)

theorem isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal :
    Blowup.IsLocallyGeneratedByNonZeroDivisor (DivisorReduction.containedComponentsIdeal T j hj) := by
  have hsmp : Smooth T.structMap := hV.smooth
  by_cases h : IsOpen (divisorComponentsInOrderLocus T j hj)
  · rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h]
    exact isLocallyGeneratedByNonZeroDivisor_openSubschemeKer (T.boundary.get ⟨j, hj⟩)
      ⟨divisorComponentsInOrderLocus T j hj, h⟩ (isClosed_divisorComponentsInOrderLocus T hV j hj)
      (((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).1
        (isSmoothDivisor_boundary_get T hV j hj)).1)
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj h]
    exact ((isSmoothDivisor_iff T.structMap (⊤ : T.scheme.IdealSheafData)).1
      (isSmoothDivisor_top T.structMap)).1

theorem hasStrictNormalCrossingsWith_containedComponentsIdeal :
    HasStrictNormalCrossingsWith T.structMap (DivisorReduction.containedComponentsIdeal T j hj) T.boundary := by
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZ⟩ :=
    exists_etaleChart_containedComponentsIdeal T hV j hj x hx
  refine ⟨U, hxU, n, c, a, {b}, ?_, ?_, ?_, hZ⟩
  · intro i hi i' hi' t hti hti'
    exact hinj i i' hi hi' t hti hti'
  · intro i hi hni
    exact hnone i hi hni
  · intro i hi t hti
    exact hsome i hi t hti

theorem isBlowupAlongIdealSheaf_id_containedComponentsIdeal :
    Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) :=
  Blowup.isBlowupAlongIdealSheaf_id_of_isLocallyGeneratedByNonZeroDivisor _ (isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal T hV j hj)

theorem exists_mul_pow_containedComponentsIdeal_eq_ideal :
    ∃ J : T.scheme.IdealSheafData,
      DivisorReduction.containedComponentsIdeal T j hj ^ T.mult * J = T.ideal := by
  have := hV.isNoetherian
  have : CharZero T.base := hV.charZero
  have : Smooth T.structMap := hV.smooth
  have hle : T.ideal ≤ DivisorReduction.containedComponentsIdeal T j hj ^ T.mult :=
    le_pow_of_hasStrictNormalCrossingsWith T.structMap (DivisorReduction.containedComponentsIdeal T j hj) T.ideal T.boundary
      (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj) T.mult (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
  exact Blowup.IsLocallyGeneratedByNonZeroDivisor.exists_mul_eq
    ((isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal T hV j hj).pow T.mult) hle


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformBasic
section


section

private theorem iSup_le_zero_nat_consolidated340 {Y : Scheme.{u}} (G : ℕ → Y.IdealSheafData) :
    (⨆ l, ⨆ _ : l ≤ 0, G l) = G 0 := by
  simp only [Nat.le_zero]
  exact iSup_iSup_eq_left

namespace BlowupSequenceData

section
variable {X : Scheme.{u}} (d : BlowupSequenceData X)

theorem controlledTransform_congr (I I' : X.IdealSheafData)
    (h : I.comap (d.projectionToBase 0) = I'.comap (d.projectionToBase 0)) (m t : ℕ) :
    d.controlledTransform I m t = d.controlledTransform I' m t := by
  induction t with
  | zero =>
    rw [controlledTransform_zero, controlledTransform_zero, ← d.projectionToBase_zero]
    exact h
  | succ t ih =>
    rw [controlledTransform_succ, controlledTransform_succ, ih]

theorem boundary_congr (E E' : List X.IdealSheafData)
    (h : List.map (fun D => D.comap (d.projectionToBase 0)) E = List.map (fun D => D.comap (d.projectionToBase 0)) E')
    (t : ℕ) :
    d.boundaryFrom E t = d.boundaryFrom E' t := by
  induction t with
  | zero =>
    rw [boundary_zero, boundary_zero, ← d.projectionToBase_zero]
    exact h
  | succ t ih =>
    rw [boundary_succ, boundary_succ, ih]

theorem pow_controlledTransform_le_pow_controlledTransform_succ (K A : X.IdealSheafData) (m l t : ℕ)
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal (d.map t) (d.center t)))
    (hK : ∃ B : (d.obj (t + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map t) (d.center t) ^ (m - l) * B =
        (d.controlledTransform K (m - l) t).comap (d.map t))
    (hA : ∃ B : (d.obj (t + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map t) (d.center t) ^ m * B = (d.controlledTransform A m t).comap (d.map t))
    (hle : d.controlledTransform K (m - l) t ^ m ≤ d.controlledTransform A m t ^ (m - l)) :
    d.controlledTransform K (m - l) (t + 1) ^ m ≤ d.controlledTransform A m (t + 1) ^ (m - l) := by
  have hpowMul := d.pow_exceptionalIdeal_mul_controlledTransform_succ K (m - l) t hK
  have hAs := d.pow_exceptionalIdeal_mul_controlledTransform_succ A m t hA
  have hcomap : (d.controlledTransform K (m - l) t ^ m).comap (d.map t) ≤
      (d.controlledTransform A m t ^ (m - l)).comap (d.map t) :=
    Scheme.IdealSheafData.comap_mono _ hle
  rw [Scheme.IdealSheafData.comap_pow, Scheme.IdealSheafData.comap_pow, ← hpowMul, ← hAs,
    mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (m - l) m] at hcomap
  exact (hcart.pow (m * (m - l))).le_of_mul_le_mul hcomap


end

end BlowupSequenceData

theorem orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le (k : Type u) [Field k] [CharZero k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (K A : Y.IdealSheafData) (l m : ℕ) (hlm : l < m) (h : K ^ m ≤ A ^ (m - l)) :
    orderAtLeastLocus A m ⊆ orderAtLeastLocus K (m - l) := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx
  rw [mem_orderAtLeastLocus_iff]
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by omega)
  have hml : 1 ≤ m - l := by omega
  have h1 : orderAt (A ^ (m - l)) x ≤ orderAt (K ^ m) x := orderAt_le_of_le h x
  rw [orderAt_pow k p A (m - l) x, orderAt_pow k p K m x] at h1
  have h2 : ((m - l : ℕ) : ℕ∞) * ((m : ℕ) : ℕ∞) ≤ ((m - l : ℕ) : ℕ∞) * orderAt A x :=
    (natCast_mul_le_mul_iff hml m (orderAt A x)).mpr hx
  have h3 : ((m : ℕ) : ℕ∞) * ((m - l : ℕ) : ℕ∞) ≤ ((m : ℕ) : ℕ∞) * orderAt K x := by
    calc ((m : ℕ) : ℕ∞) * ((m - l : ℕ) : ℕ∞)
        = ((m - l : ℕ) : ℕ∞) * ((m : ℕ) : ℕ∞) := mul_comm _ _
      _ ≤ ((m - l : ℕ) : ℕ∞) * orderAt A x := h2
      _ ≤ ((m : ℕ) : ℕ∞) * orderAt K x := h1
  exact (natCast_mul_le_mul_iff hm (m - l) (orderAt K x)).mp h3

theorem comap_iSup_le_nat {Y Y' : Scheme.{u}} (f : Y' ⟶ Y) (n : ℕ) (G : ℕ → Y.IdealSheafData) :
    (⨆ l ≤ n, G l).comap f = ⨆ l ≤ n, (G l).comap f := by
  induction n with
  | zero => rw [iSup_le_zero_nat_consolidated340, iSup_le_zero_nat_consolidated340]
  | succ n ih =>
    rw [Nat.iSup_le_succ, Nat.iSup_le_succ, Scheme.IdealSheafData.comap_sup, ih]

theorem mem_support_iSup_le_nat {Y : Scheme.{u}} (n : ℕ) (G : ℕ → Y.IdealSheafData) (y : Y)
    (h : ∀ l ≤ n, y ∈ (G l).support) : y ∈ (⨆ l ≤ n, G l).support := by
  revert h
  induction n with
  | zero =>
    intro h
    rw [iSup_le_zero_nat_consolidated340]
    exact h 0 le_rfl
  | succ n ih =>
    intro h
    rw [Nat.iSup_le_succ, mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_sup]
    refine sup_le ?_ ?_
    · exact (mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp
        (ih fun l hl => h l (hl.trans (Nat.le_succ n)))
    · exact (mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp (h (n + 1) le_rfl)

namespace DivisorReduction

variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})
    (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData)
    (E₀ : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)

noncomputable abbrev divisorEmbedding : (restrictToBoundaryDivisor T j hj I₀ E₀).scheme ⟶ T.scheme :=
  (T.boundary.get ⟨j, hj⟩).subschemeι

noncomputable abbrev ambientBlowupSeqStructureMorphism (t : ℕ) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t ⟶ Spec (CommRingCat.of T.base) :=
  (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap

noncomputable abbrev ambientDerivIdeal [LocallyOfFiniteType T.structMap]
    (l t : ℕ) : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t).IdealSheafData :=
  (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform
    (derivIdealSheafIterate T.base T.structMap l I₀) (T.mult - l) t

theorem embeddingIntoAmbient_comp_projectionToBase (t : ℕ) :
    embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
      s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀ := by
  induction t with
  | zero =>
    have h0 : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero = Iso.refl T.scheme :=
      ambientBlowupSequence_isoObjZero (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
    rw [BlowupSequenceData.projectionToBase_zero, h0, embeddingIntoAmbient_zero, MarkedSequenceOfBlowups.projectionToBase_zero, Iso.refl_hom]
    exact Category.comp_id _
  | succ t ih =>
    have hmap := embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr t
    have hstruct : s.transitionMapSucc t ≫ s.projectionToBase t = s.projectionToBase (t + 1) := by
      rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
      exact SequenceOfBlowups.transitionMap_comp_projectionToBase s.toSequenceOfBlowups (Nat.le_succ t)
    have e1 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase (t + 1) =
        embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) :=
      congrArg (fun f => embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫ f)
        (BlowupSequenceData.projectionToBase_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr) t)
    have e2 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) =
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t :=
      (Category.assoc _ _ _).symm
    have e3 : (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
        (s.transitionMapSucc t ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t :=
      congrArg (fun f => f ≫ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) hmap
    have e4 : (s.transitionMapSucc t ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
        s.transitionMapSucc t ≫ (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) :=
      Category.assoc _ _ _
    have e5 : s.transitionMapSucc t ≫ (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) =
        s.transitionMapSucc t ≫ (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) :=
      congrArg (fun f => s.transitionMapSucc t ≫ f) ih
    have e6 : s.transitionMapSucc t ≫ (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) =
        (s.transitionMapSucc t ≫ s.projectionToBase t) ≫ divisorEmbedding T j hj I₀ E₀ :=
      (Category.assoc _ _ _).symm
    have e7 : (s.transitionMapSucc t ≫ s.projectionToBase t) ≫ divisorEmbedding T j hj I₀ E₀ =
        s.projectionToBase (t + 1) ≫ divisorEmbedding T j hj I₀ E₀ :=
      congrArg (fun f => f ≫ divisorEmbedding T j hj I₀ E₀) hstruct
    exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans e7)))))

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.UntwistedDivisorRestriction
section

open TopologicalSpace

section

section
variable {S : Type*} [TopologicalSpace S] [NoetherianSpace S] (hsep : ∀ C₁ ∈ irreducibleComponents S, ∀ C₂ ∈ irreducibleComponents S, C₁ ≠ C₂ → Disjoint C₁ C₂) {K : Set S} (hK : K ∈ irreducibleComponents S)
include hsep hK

theorem isClopen_of_pairwise_disjoint_irreducibleComponents : IsClopen K := by
  have hKc : IsClosed K := isClosed_of_mem_irreducibleComponents K hK
  have hcompl : Kᶜ = ⋃₀ (irreducibleComponents S \ {K}) := by
    ext x
    constructor
    · intro hx
      refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents .., ?_⟩, ?_⟩
      · simp only [Set.mem_singleton_iff]
        intro h
        exact hx (by rw [← h]; exact (irreducibleComponent_property x).2.1 rfl)
      · exact (irreducibleComponent_property x).2.1 rfl
    · rintro ⟨C, ⟨hC, hCK⟩, hxC⟩ hxK
      have hne : C ≠ K := by
        intro h
        exact hCK (by simp [h])
      exact Set.disjoint_left.mp (hsep C hC K hK hne) hxC hxK
  have hfin : (irreducibleComponents S \ {K}).Finite :=
    Set.Finite.subset NoetherianSpace.finite_irreducibleComponents Set.sdiff_subset
  refine ⟨hKc, ?_⟩
  rw [← isClosed_compl_iff, hcompl, Set.sUnion_eq_biUnion]
  exact hfin.isClosed_biUnion (fun C hC => isClosed_of_mem_irreducibleComponents C hC.1)

theorem connectedComponent_subset_of_mem_irreducibleComponents {x : S} (hx : x ∈ K) :
    connectedComponent x ⊆ K :=
  (isClopen_of_pairwise_disjoint_irreducibleComponents hsep hK).connectedComponent_subset hx


end

namespace DivisorReduction

section
variable (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ) (hj : j < T.boundary.length)
include hV

private theorem smooth_subschemeι_comp_structureMorphism_consolidated341 :
    Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) := by
  have hmem : T.boundary.get ⟨j, hj⟩ ∈ T.boundary := List.getElem_mem hj
  have hDiv : IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) :=
    ((inStrictNormalCrossingPosition_iff T.structMap T.boundary).mp hV.snc).1 _ hmem
  exact ((isSmoothDivisor_iff _ _).mp hDiv).2

private theorem noetherianSpace_boundary_subscheme_consolidated341 :
    NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme := by
  have := hV.isNoetherian
  have : NoetherianSpace ↥T.scheme := inferInstance
  exact (AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding
    (T.boundary.get ⟨j, hj⟩).subschemeι).isInducing.noetherianSpace


end

private theorem ker_ι_comp_ne_top_consolidated341 {X Z : Scheme.{u}} (hX : NoetherianSpace ↥X) (V : X.Opens)
    (g : X ⟶ Z) (x : ↥X) (hx : x ∈ V) :
    AlgebraicGeometry.Scheme.Hom.ker (V.ι ≫ g) ≠ ⊤ := by
  have := hX
  have : NoetherianSpace ↥V.toScheme := inferInstanceAs (NoetherianSpace ↥(V : Set ↥X))
  intro h
  have : QuasiCompact (V.ι ≫ g) := ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hx' : x ∈ Set.range ⇑V.ι := by simpa using hx
  obtain ⟨y, hy⟩ := hx'
  have h3 : ⇑g x ∈ ((AlgebraicGeometry.Scheme.Hom.ker (V.ι ≫ g)).support : Set ↥Z) := by
    rw [AlgebraicGeometry.Scheme.Hom.support_ker]
    exact subset_closure ⟨y, by simp [hy]⟩
  rw [h] at h3
  simp at h3

section
variable (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)

theorem nonzeroOnComponents_comap_lowerIdealWithoutBlowup (hBalanced : T.IsBalanced hV.locallyOfFiniteType) (j : ℕ) (hj : j < T.boundary.length)
    (hZ : DivisorReduction.containedComponentsIdeal T j hj = ⊤) :
    NonzeroOnComponents
      ((DivisorReduction.lowerIdealWithoutBlowup T).comap (T.boundary.get ⟨j, hj⟩).subschemeι) := by
  classical
  have := hV.charZero
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have hsm : Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    smooth_subschemeι_comp_structureMorphism_consolidated341 T hV j hj
  have hNoe : NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    noetherianSpace_boundary_subscheme_consolidated341 T hV j hj
  have := hNoe
  have hbal : IsDerivBalanced T.base T.structMap T.ideal T.mult := hBalanced
  have hcs : orderAtLeastLocus T.ideal T.mult = (T.ideal.support : Set ↥T.scheme) :=
    orderAtLeastLocus_eq_support_of_isDerivBalanced T.base T.structMap T.ideal T.mult hbal hV.one_le_mult
  have hdisj : ∀ C₁ ∈ irreducibleComponents ↥(T.boundary.get ⟨j, hj⟩).subscheme,
      ∀ C₂ ∈ irreducibleComponents ↥(T.boundary.get ⟨j, hj⟩).subscheme,
      C₁ ≠ C₂ → Disjoint C₁ C₂ :=
    irreducibleComponentsDisjointOfSmooth T.base (T.boundary.get ⟨j, hj⟩).subscheme
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) hsm
  have hopen := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T hV j hj
  rw [DivisorReduction.containedComponentsIdeal_eq_ker T j hj hopen] at hZ
  have hI : DivisorReduction.lowerIdealWithoutBlowup T = T.ideal := by
    show T.ideal.comap (𝟙 T.scheme) = T.ideal
    simp
  rw [hI, nonzeroOnComponents_iff]
  intro C hC hsub
  obtain ⟨x, hxC⟩ := hC.1.nonempty
  have hCsub : C ⊆ ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult := by
    intro y hy
    have h1 : y ∈ ((T.ideal.comap (T.boundary.get ⟨j, hj⟩).subschemeι).support :
        Set ↥(T.boundary.get ⟨j, hj⟩).subscheme) := hsub hy
    rw [Set.mem_preimage, hcs]
    simpa [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] using h1
  have hxV : connectedComponent x ⊆
      ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult :=
    fun z hz => hCsub (connectedComponent_subset_of_mem_irreducibleComponents hdisj hC hxC hz)
  exact absurd hZ (ker_ι_comp_ne_top_consolidated341 hNoe _ _ x hxV)

theorem isAdmissible_restrictToDivisor (_hOB : T.IsOrderBoundedByMult) (hBalanced : T.IsBalanced hV.locallyOfFiniteType) (j : ℕ)
    (hj : j < T.boundary.length) (hZ : DivisorReduction.containedComponentsIdeal T j hj = ⊤) :
    (DivisorReduction.restrictToDivisor T j hj).IsAdmissible := by
  have := hV.charZero
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have := hV.quasiCompact
  have hsm : Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    smooth_subschemeι_comp_structureMorphism_consolidated341 T hV j hj
  have := hsm
  have hlft : LocallyOfFiniteType
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) := inferInstance
  have hqc : QuasiCompact
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) := inferInstance
  have hsnc0 : InStrictNormalCrossingPosition ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
      ((T.boundary.eraseIdx j).map fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) :=
    inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx T.structMap T.boundary hV.snc j hj
  have hbd : DivisorReduction.lowerBoundaryWithoutBlowup T = T.boundary := by
    show List.map (fun D => D.comap (𝟙 T.scheme)) T.boundary = T.boundary
    simp
  have hsnc : InStrictNormalCrossingPosition ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
      (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
        (List.take (T.boundary.length - 1) ((DivisorReduction.lowerBoundaryWithoutBlowup T).eraseIdx j))) := by
    rw [hbd, List.take_of_length_le (le_of_eq (List.length_eraseIdx_of_lt hj))]
    exact hsnc0
  exact ⟨hV.charZero, hlft,
    nonzeroOnComponents_comap_lowerIdealWithoutBlowup T hV hBalanced j hj hZ, hV.one_le_mult, hqc, hsm, hsnc⟩


end

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientCenterImage
section



section
variable {S X : Scheme.{u}}

theorem imageIdealSheaf_eq_ker_subschemeι_comp (f : S ⟶ X) (Z : S.IdealSheafData) :
    imageIdealSheaf f Z = Scheme.Hom.ker (Z.subschemeι ≫ f) :=
  rfl

theorem support_imageIdealSheaf_eq_image_support (ι : S ⟶ X)
    [IsClosedImmersion ι] (Z : S.IdealSheafData) :
    (↑(imageIdealSheaf ι Z).support : Set ↥X) = ⇑ι '' (↑Z.support : Set ↥S) := by
  have hqc : QuasiCompact (Z.subschemeι ≫ ι) := inferInstance
  have hcl := AlgebraicGeometry.Scheme.Hom.isClosedEmbedding ι
  have hrange : Set.range ⇑Z.subschemeι = (↑Z.support : Set ↥S) :=
    AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι Z
  have hcomp : Set.range ⇑(Z.subschemeι ≫ ι) = ⇑ι '' (↑Z.support : Set ↥S) := by
    rw [← hrange]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⇑Z.subschemeι y, ⟨y, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
  have hclosed : IsClosed (⇑ι '' (↑Z.support : Set ↥S)) :=
    hcl.isClosedMap _ Z.support.2
  have hsup : (↑(AlgebraicGeometry.Scheme.Hom.ker (Z.subschemeι ≫ ι)).support : Set ↥X)
      = closure (Set.range ⇑(Z.subschemeι ≫ ι)) := by
    rw [AlgebraicGeometry.Scheme.Hom.support_ker]
  rw [imageIdealSheaf_eq_ker_subschemeι_comp, hsup, hcomp, hclosed.closure_eq]


end

private theorem exists_iso_ker_subscheme_consolidated369 {W X : Scheme.{u}} (g : W ⟶ X)
    [IsClosedImmersion g] :
    ∃ e : W ≅ (Scheme.Hom.ker g).subscheme,
      e.hom ≫ (Scheme.Hom.ker g).subschemeι = g :=
  ⟨asIso (Scheme.Hom.toImage g), Scheme.Hom.toImage_imageι g⟩

private theorem smooth_of_smooth_iso_hom_comp_consolidated369 {A A' B : Scheme.{u}} (e : A ≅ A') (p : A' ⟶ B)
    (h : Smooth (e.hom ≫ p)) : Smooth p := by
  have : Smooth (e.hom ≫ p) := h
  have h2 : Smooth (e.inv ≫ e.hom ≫ p) := inferInstance
  simpa using h2

theorem smooth_imageIdealSheaf_subschemeι_comp {S X B : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] (Z : S.IdealSheafData) (f : X ⟶ B)
    (h : Smooth (Z.subschemeι ≫ ι ≫ f)) :
    Smooth ((imageIdealSheaf ι Z).subschemeι ≫ f) := by
  have : IsClosedImmersion (Z.subschemeι ≫ ι) := inferInstance
  obtain ⟨e, he⟩ := exists_iso_ker_subscheme_consolidated369 (Z.subschemeι ≫ ι)
  rw [imageIdealSheaf_eq_ker_subschemeι_comp ι Z]
  refine smooth_of_smooth_iso_hom_comp_consolidated369 e _ ?_
  rw [← Category.assoc, he, Category.assoc]
  exact h

namespace BlowupSequenceData

section
variable {X : Scheme.{u}} (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (CategoryStruct.id X) Z) (d : BlowupSequenceData X)

theorem projectionToBase_prepend_zero :
    (BlowupSequenceData.prepend Z hZ d).projectionToBase 0 = CategoryStruct.id X := by
  rw [BlowupSequenceData.projectionToBase_zero, BlowupSequenceData.prepend_isoObjZero, CategoryTheory.Iso.refl_hom]

theorem projectionToBase_prepend_succ (t : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).projectionToBase (t + 1) = d.projectionToBase t := by
  induction t with
  | zero =>
    have e1 : (BlowupSequenceData.prepend Z hZ d).projectionToBase (0 + 1)
        = (BlowupSequenceData.prepend Z hZ d).map 0 ≫ (BlowupSequenceData.prepend Z hZ d).projectionToBase 0 :=
      BlowupSequenceData.projectionToBase_succ (BlowupSequenceData.prepend Z hZ d) 0
    have e2 : (BlowupSequenceData.prepend Z hZ d).projectionToBase 0 = (BlowupSequenceData.prepend Z hZ d).isoZero.hom :=
      BlowupSequenceData.projectionToBase_zero (BlowupSequenceData.prepend Z hZ d)
    have e3 : (BlowupSequenceData.prepend Z hZ d).isoZero = Iso.refl X :=
      BlowupSequenceData.prepend_isoObjZero Z hZ d
    have e4 : (BlowupSequenceData.prepend Z hZ d).map 0 = d.isoZero.hom :=
      BlowupSequenceData.prepend_blowupMorphism_zero Z hZ d
    have e5 : d.projectionToBase 0 = d.isoZero.hom := BlowupSequenceData.projectionToBase_zero d
    rw [e1, e2, e3, e4, e5]
    exact Category.comp_id _
  | succ n ih =>
    have e1 : (BlowupSequenceData.prepend Z hZ d).projectionToBase (n + 1 + 1)
        = (BlowupSequenceData.prepend Z hZ d).map (n + 1) ≫ (BlowupSequenceData.prepend Z hZ d).projectionToBase (n + 1) :=
      BlowupSequenceData.projectionToBase_succ (BlowupSequenceData.prepend Z hZ d) (n + 1)
    have e2 : (BlowupSequenceData.prepend Z hZ d).map (n + 1) = d.map n :=
      BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d n
    rw [e1, e2, ih]
    exact (BlowupSequenceData.projectionToBase_succ d n).symm

theorem controlledTransform_prepend_succ (I I₁ : X.IdealSheafData) (m : ℕ)
    (h1 : (BlowupSequenceData.prepend Z hZ d).controlledTransform I m 1 = I₁.comap d.isoZero.hom) (t : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).controlledTransform I m (t + 1) = d.controlledTransform I₁ m t := by
  induction t with
  | zero => exact h1.trans (d.controlledTransform_zero I₁ m).symm
  | succ n ih =>
    rewrite [BlowupSequenceData.controlledTransform_succ (BlowupSequenceData.prepend Z hZ d) I m (n + 1),
      BlowupSequenceData.controlledTransform_succ d I₁ m n, ih,
      BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d n, BlowupSequenceData.prepend_center_succ Z hZ d n]
    rfl

theorem boundary_prepend_succ (E E₁ : List X.IdealSheafData)
    (h1 : (BlowupSequenceData.prepend Z hZ d).boundaryFrom E 1
      = List.map (fun D => D.comap d.isoZero.hom) E₁) (t : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).boundaryFrom E (t + 1) = d.boundaryFrom E₁ t := by
  induction t with
  | zero =>
      rw [BlowupSequenceData.boundary_zero]
      exact h1
  | succ n ih =>
      rw [BlowupSequenceData.boundary_succ (BlowupSequenceData.prepend Z hZ d) E (n + 1),
        BlowupSequenceData.boundary_succ d E₁ n, ih, BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d n,
        BlowupSequenceData.prepend_center_succ Z hZ d n]
      all_goals rfl


end

end BlowupSequenceData

namespace DivisorReduction

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups) (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ)

theorem smooth_ambientBlowupSeq_center_comp (ht : t < s.length) :
    Smooth
      (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).subschemeι ≫
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap)) := by
  have hsm := s.center_smooth t ht
  have hemb := embeddingIntoAmbient_comp_projectionToBase hres hno T j hj I₀ E₀ s hpr t
  have h2 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap)
      = s.projectionToBase t ≫ (divisorEmbedding T j hj I₀ E₀ ≫ T.structMap) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg
          (fun g : ((MarkedBlowupSequenceData.ofMarkedSequence s).obj t ⟶ T.scheme) => g ≫ T.structMap)
          hemb).trans (Category.assoc _ _ _))
  have key : Smooth ((s.center t).subschemeι ≫
      (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap))) :=
    Eq.mpr
      (congrArg
        (fun g : ((MarkedBlowupSequenceData.ofMarkedSequence s).obj t ⟶ Spec (CommRingCat.of T.base)) =>
          Smooth ((s.center t).subschemeι ≫ g)) h2)
      hsm
  exact Eq.mpr
    (congrArg
      (fun Z : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t).IdealSheafData =>
        Smooth (Z.subschemeι ≫
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap)))
      (ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I₀ E₀ s hpr t))
    (smooth_imageIdealSheaf_subschemeι_comp (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap) key)

theorem support_ambientBlowupSeq_center_eq_image :
    (↑((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).support :
        Set ↥((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t)) =
      ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ''
        (↑((MarkedBlowupSequenceData.ofMarkedSequence s).center t).support :
          Set ↥((MarkedBlowupSequenceData.ofMarkedSequence s).obj t)) := by
  have h1 : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t =
      imageIdealSheaf (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t) :=
    ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I₀ E₀ s hpr t
  have h2 : (MarkedBlowupSequenceData.ofMarkedSequence s).center t = s.center t :=
    MarkedBlowupSequenceData.ofMarkedSequence_center s t
  rw [h1, h2]
  exact support_imageIdealSheaf_eq_image_support
    (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)


end

end DivisorReduction

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdealTop
section


section

namespace DivisorReduction

theorem containedComponentsIdeal_eq_top_of_eq_imageIdealSheaf
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ) (hj : j < T.boundary.length)
    (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData)
    (hm : T.mult = 1)
    (hlow : (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
        (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (T.boundary.eraseIdx j))).IsAdmissible)
    (hpush : T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J) :
    DivisorReduction.containedComponentsIdeal T j hj = ⊤ := by
  by_cases h : IsOpen (divisorComponentsInOrderLocus T j hj)
  · have hnz : NonzeroOnComponents J := hlow.nonzeroOnComponents
    have hcomap : T.ideal.comap (T.boundary.get ⟨j, hj⟩).subschemeι = J := by
      rw [hpush]
      exact Blowup.comap_map_of_isClosedImmersion _ J
    have hsub : ∀ y : ↥(T.boundary.get ⟨j, hj⟩).subscheme,
        (T.boundary.get ⟨j, hj⟩).subschemeι y ∈ (T.ideal.support : Set ↥T.scheme) →
        y ∈ (J.support : Set ↥(T.boundary.get ⟨j, hj⟩).subscheme) := by
      intro y hy
      have h1 := (one_le_orderAt_iff_mem_support T.ideal
        ((T.boundary.get ⟨j, hj⟩).subschemeι y)).mpr hy
      have h2 := orderAt_le_orderAt_comap (T.boundary.get ⟨j, hj⟩).subschemeι T.ideal y
      rw [hcomap] at h2
      exact (one_le_orderAt_iff_mem_support J y).mp (le_trans h1 h2)
    have hempty : divisorComponentsInOrderLocus T j hj = ∅ := by
      ext x
      refine ⟨fun hx => ?_, fun hx => ((Set.mem_empty_iff_false x).mp hx).elim⟩
      exfalso
      obtain ⟨C, hCpre, hxC, hCmax⟩ :=
        exists_preirreducible ({x} : Set ↥(T.boundary.get ⟨j, hj⟩).subscheme)
          isIrreducible_singleton.2
      have hxC' : x ∈ C := hxC rfl
      have hC : C ∈ irreducibleComponents ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
        ⟨⟨⟨x, hxC'⟩, hCpre⟩, fun u hu hCu => le_of_eq (hCmax u hu.2 hCu)⟩
      refine hnz C hC ?_
      intro y hyC
      have hyc : y ∈ connectedComponent x :=
        hCpre.isPreconnected.subset_connectedComponent hxC' hyC
      have h1 := hx hyc
      rw [hm] at h1
      have h1' : (T.boundary.get ⟨j, hj⟩).subschemeι y ∈ orderAtLeastLocus T.ideal 1 := h1
      exact hsub y ((mem_orderAtLeastLocus_one_iff T.ideal _).mp h1')
    rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h,
      AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty,
      support_openSubschemeKer (T.boundary.get ⟨j, hj⟩) ⟨divisorComponentsInOrderLocus T j hj, h⟩
        (isClosed_divisorComponentsInOrderLocus T hV j hj), Set.image_eq_empty]
    exact hempty
  · exact EmbeddedResolution.containedComponentsIdeal_eq_top_of_not_isOpen T j hj h

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformPowers
section


section

namespace BlowupSequenceData

private theorem pow_controlledTransform_le_pow_controlledTransform_of_dvd_consolidated368 {X : Scheme.{u}} (d : BlowupSequenceData X)
    (K A : X.IdealSheafData) (m l : ℕ) (hbase : K ^ m ≤ A ^ (m - l)) (t : ℕ)
    (ht : t ≤ d.length)
    (hdivA : ∀ i < t, ∃ B : (d.obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * B = (d.controlledTransform A m i).comap (d.map i))
    (hdivK : ∀ i < t, ∃ B : (d.obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map i) (d.center i) ^ (m - l) * B =
        (d.controlledTransform K (m - l) i).comap (d.map i)) :
    d.controlledTransform K (m - l) t ^ m ≤ d.controlledTransform A m t ^ (m - l) := by
  revert ht hdivA hdivK
  induction t with
  | zero =>
      intro _ _ _
      rw [BlowupSequenceData.controlledTransform_zero, BlowupSequenceData.controlledTransform_zero,
        ← Scheme.IdealSheafData.comap_pow, ← Scheme.IdealSheafData.comap_pow]
      exact Scheme.IdealSheafData.comap_mono (f := d.isoZero.hom) hbase
  | succ n ih =>
      intro ht hdivA hdivK
      have hn : n < d.length := lt_of_lt_of_le (Nat.lt_succ_self n) ht
      have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal (d.map n) (d.center n)) :=
        isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal (d.isBlowup n hn)
      exact pow_controlledTransform_le_pow_controlledTransform_succ d K A m l n hcart
        (hdivK n (Nat.lt_succ_self n)) (hdivA n (Nat.lt_succ_self n))
        (ih (le_of_lt hn) (fun i hi => hdivA i (Nat.lt_succ_of_lt hi))
          (fun i hi => hdivK i (Nat.lt_succ_of_lt hi)))

theorem exists_pow_mul_eq_comap_controlledTransform {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (d : BlowupSequenceData X) (p : X ⟶ Spec (CommRingCat.of k)) (A : X.IdealSheafData) (n t : ℕ)
    (ht : t < d.length) [IsLocallyNoetherian (d.obj (t + 1))]
    [Smooth (d.projectionToBase t ≫ p)]
    (E : List (d.obj t).IdealSheafData)
    (hE : HasStrictNormalCrossingsWith (d.projectionToBase t ≫ p) (d.center t) E)
    (hord : ↑(d.center t).support ⊆ orderAtLeastLocus (d.controlledTransform A n t) n) :
    ∃ B : (d.obj (t + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map t) (d.center t) ^ n * B = (d.controlledTransform A n t).comap (d.map t) := by
  have hle : d.controlledTransform A n t ≤ d.center t ^ n :=
    le_pow_of_hasStrictNormalCrossingsWith (d.projectionToBase t ≫ p) (d.center t) (d.controlledTransform A n t) E hE n hord
  obtain ⟨B, hB, -⟩ :=
    existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map t) (d.center t) (d.controlledTransform A n t) n
      (d.isBlowup t ht) hle
  exact ⟨B, hB⟩

end BlowupSequenceData

namespace DivisorReduction

theorem pow_ambientDerivIdeal_le_pow_controlledTransform
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})
    (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme]
    [LocallyOfFiniteType T.structMap]
    (j : ℕ) (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData)
    (E₀ : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult)
    (l : ℕ) (hl : l < T.mult) (t : ℕ) (ht : t ≤ s.length)
    (hdivA : ∀ i < t, ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center i) ^ T.mult * B =
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult i).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i))
    (hdivD : ∀ i < t, ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center i) ^ (T.mult - l) * B =
        (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l i).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)) :
    ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ^ T.mult ≤
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t ^ (T.mult - l) := by
  have ht' : t ≤ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length := by
    rw [ambientBlowupSeq_length hres hno T j hj I₀ E₀ s hpr]
    exact ht
  exact BlowupSequenceData.pow_controlledTransform_le_pow_controlledTransform_of_dvd_consolidated368 (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr)
    (derivIdealSheafIterate T.base T.structMap l I₀) I₀ T.mult l
    (IsDerivBalanced.derivIdealSheafIterate_pow_le T.base T.structMap hbal hl) t ht' hdivA hdivD

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionProperties
section


section

structure DivisorReductionProperties (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) : Prop where
  isMarked_pushedTop :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj = ⊤ →
            (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
              ∀ [IsNoetherian T.scheme]
                (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
                (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
                      (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
                  T.structMap T.ideal T.mult T.boundary
  isMarked_pushedPre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
            ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme)
                (DivisorReduction.containedComponentsIdeal T j hj)),
              (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
                ∀ [IsNoetherian T.scheme]
                  (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
                  (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                  (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                        (DivisorReduction.ambientBlowupSeq hres hno T j hj
                          (DivisorReduction.lowerIdealAfterBlowup T j hj)
                          (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
                    T.structMap T.ideal T.mult T.boundary
  valid_lowerPre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ → (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible
  orderAt_ctrlIdeal_le_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj = ⊤ →
            (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
              ∀ [IsNoetherian T.scheme]
                (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
                (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                ∀ i ≤ s.length,
                  ∀ (x : ↥((DivisorReduction.ambientBlowupSeq hres hno T j hj
                            (DivisorReduction.lowerIdealWithoutBlowup T)
                            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).obj i)),
                    orderAt ((DivisorReduction.ambientBlowupSeq hres hno T j hj
                          (DivisorReduction.lowerIdealWithoutBlowup T)
                          (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
                        T.ideal T.mult i) x ≤ (T.mult : ℕ∞)
  orderAt_ctrlIdeal_le_pre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
            ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme)
                (DivisorReduction.containedComponentsIdeal T j hj)),
              (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
                ∀ [IsNoetherian T.scheme]
                  (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
                  (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                  ∀ i ≤ s.length + 1,
                    ∀ (x : ↥((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                              (DivisorReduction.ambientBlowupSeq hres hno T j hj
                                (DivisorReduction.lowerIdealAfterBlowup T j hj)
                                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).obj i)),
                      orderAt ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                            (DivisorReduction.ambientBlowupSeq hres hno T j hj
                              (DivisorReduction.lowerIdealAfterBlowup T j hj)
                              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform
                          T.ideal T.mult i) x ≤ (T.mult : ℕ∞)
  coSupport_inter_ker_eq_empty_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj = ⊤ →
            (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
              ∀ [IsNoetherian T.scheme]
                (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
                (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                orderAtLeastLocus (s.ideal s.length) T.mult = ∅ →
                  orderAtLeastLocus ((DivisorReduction.ambientBlowupSeq hres hno T j hj
                          (DivisorReduction.lowerIdealWithoutBlowup T)
                          (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
                        T.ideal T.mult s.length) T.mult ∩
                      ↑(AlgebraicGeometry.Scheme.Hom.ker
                          (DivisorReduction.embeddingIntoAmbient hres hno T j hj
                            (DivisorReduction.lowerIdealWithoutBlowup T)
                            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr s.length)).support = ∅
  coSupport_inter_ker_eq_empty_pre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
            ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme)
                (DivisorReduction.containedComponentsIdeal T j hj)),
              (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
                ∀ [IsNoetherian T.scheme]
                  (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
                  (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                  orderAtLeastLocus (s.ideal s.length) T.mult = ∅ →
                    orderAtLeastLocus ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                            (DivisorReduction.ambientBlowupSeq hres hno T j hj
                              (DivisorReduction.lowerIdealAfterBlowup T j hj)
                              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform
                          T.ideal T.mult (s.length + 1)) T.mult ∩
                        (((AlgebraicGeometry.Scheme.Hom.ker
                            (DivisorReduction.embeddingIntoAmbient hres hno T j hj
                              (DivisorReduction.lowerIdealAfterBlowup T j hj)
                              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr s.length)).support :
                          Set ↥((DivisorReduction.ambientBlowupSeq hres hno T j hj
                              (DivisorReduction.lowerIdealAfterBlowup T j hj)
                              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr).obj s.length))) = ∅
  isPullbackSeq_ambientTower :
    ∀ (X Y S S' : AlgebraicGeometry.Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y) (φ : Y ⟶ X) (ψ : S' ⟶ S)
      [IsClosedImmersion σ] [IsClosedImmersion σ']
      [Flat φ] [IsNoetherian X]
      [IsNoetherian Y],
      CategoryTheory.IsPullback σ' ψ φ σ →
        ∀ (d : BlowupSequenceData S) (d' : BlowupSequenceData S') (hc : d.CentersContainNoComponent) (hc' : d'.CentersContainNoComponent),
          IsPullbackBlowupSequence ψ d'.toSequenceOfBlowups d.toSequenceOfBlowups →
            IsPullbackBlowupSequence φ (ambientBlowupSequence σ' d' hres hno hc').toSequenceOfBlowups
              (ambientBlowupSequence σ d hres hno hc).toSequenceOfBlowups
  isStrictPullbackSeq_ambientTower :
    ∀ (X Y S S' : AlgebraicGeometry.Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y) (φ : Y ⟶ X) (ψ : S' ⟶ S)
      [IsClosedImmersion σ] [IsClosedImmersion σ']
      [Flat φ] [IsNoetherian X]
      [IsNoetherian Y],
      CategoryTheory.IsPullback σ' ψ φ σ →
        ∀ (d : BlowupSequenceData S) (d' : BlowupSequenceData S') (hc : d.CentersContainNoComponent) (hc' : d'.CentersContainNoComponent),
          IsStrictPullbackBlowupSeq ψ d'.toSequenceOfBlowups d.toSequenceOfBlowups →
            IsStrictPullbackBlowupSeq φ (ambientBlowupSequence σ' d' hres hno hc').toSequenceOfBlowups
              (ambientBlowupSequence σ d hres hno hc).toSequenceOfBlowups
  comap_ctrlIdeal_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj = ⊤ →
            (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
              ∀ [IsNoetherian T.scheme]
                (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
                (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                ∀ i ≤ s.length,
                  ((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
                            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
                        T.ideal T.mult i).comap
                      (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
                        (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr i) = s.ideal i
  comap_ctrlIdeal_pre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
            ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme)
                (DivisorReduction.containedComponentsIdeal T j hj)),
              (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
                ∀ [IsNoetherian T.scheme]
                  (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
                  (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                  ∀ i ≤ s.length,
                    ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                              (DivisorReduction.ambientBlowupSeq hres hno T j hj
                                (DivisorReduction.lowerIdealAfterBlowup T j hj)
                                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform
                          T.ideal T.mult (i + 1)).comap
                        (DivisorReduction.embeddingIntoAmbient hres hno T j hj
                          (DivisorReduction.lowerIdealAfterBlowup T j hj)
                          (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr i) = s.ideal i
  preIdeal_baseChange :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L),
        (T.baseChange L f).IsAdmissible →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hj' : j < (T.baseChange L f).boundary.length),
            DivisorReduction.containedComponentsIdeal (T.baseChange L f) j hj' =
              (DivisorReduction.containedComponentsIdeal T j hj).comap
                (CategoryTheory.Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f))
  preIdeal_pullbackAlong :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : AlgebraicGeometry.Scheme.{u})
        (q : Y ⟶ AlgebraicGeometry.Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [Smooth h],
        CategoryTheory.CategoryStruct.comp h T.structMap = q →
          (T.pullbackAlong Y q h).IsAdmissible →
            ∀ (j : ℕ) (hj : j < T.boundary.length)
              (hj' : j < (T.pullbackAlong Y q h).boundary.length),
              DivisorReduction.containedComponentsIdeal (T.pullbackAlong Y q h) j hj' =
                (DivisorReduction.containedComponentsIdeal T j hj).comap h
  preIdeal_eq_top_of_imageIdeal :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length)
        (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData),
        T.mult = 1 →
          (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
                (CategoryTheory.CategoryStruct.comp (T.boundary.get ⟨j, hj⟩).subschemeι
                  T.structMap) J
                (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
                  (T.boundary.eraseIdx j))).IsAdmissible →
            T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J →
              DivisorReduction.containedComponentsIdeal T j hj = ⊤

theorem DivisorReductionProperties.toDivisorReductionStepProperties {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} (h : DivisorReductionProperties hres hno) :
    DivisorReductionStepProperties hres hno :=
  { exists_ideal_mul_preIdeal_pow := fun T hV _ j hj =>
      exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj
    isMarked_pushedTop := h.isMarked_pushedTop
    isMarked_pushedPre := h.isMarked_pushedPre
    isBlowup_id_preIdeal := fun T hV j hj => isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV j hj
    valid_lowerTop := fun T hV hOB hbal j hj hZ =>
      DivisorReduction.isAdmissible_restrictToDivisor T hV hOB hbal j hj hZ
    valid_lowerPre := h.valid_lowerPre
    orderAt_ctrlIdeal_le_top := h.orderAt_ctrlIdeal_le_top
    orderAt_ctrlIdeal_le_pre := h.orderAt_ctrlIdeal_le_pre
    coSupport_inter_ker_eq_empty_top := h.coSupport_inter_ker_eq_empty_top
    coSupport_inter_ker_eq_empty_pre := h.coSupport_inter_ker_eq_empty_pre
    isPullbackSeq_ambientTower := h.isPullbackSeq_ambientTower
    isStrictPullbackSeq_ambientTower := h.isStrictPullbackSeq_ambientTower
    comap_ctrlIdeal_top := h.comap_ctrlIdeal_top
    comap_ctrlIdeal_pre := h.comap_ctrlIdeal_pre
    preIdeal_baseChange := h.preIdeal_baseChange
    preIdeal_pullbackAlong := h.preIdeal_pullbackAlong
    preIdeal_eq_top_of_imageIdeal := h.preIdeal_eq_top_of_imageIdeal
    smooth_preIdeal := fun T hV j hj => smooth_subschemeι_containedComponentsIdeal_comp T hV j hj
    hasSNCWith_preIdeal := fun T hV j hj => hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj
    support_preIdeal_subset := fun T hV j hj => support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj }


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LogDerivIdealEstimate
section

open TopologicalSpace


private noncomputable def iSupIdealSheaf {Y : Scheme.{u}} {ι : Sort v} (J : ι → Y.IdealSheafData) :
    Y.IdealSheafData where
  ideal U := ⨆ i, (J i).ideal U
  map_ideal_basicOpen := by
    intro U f
    simp only [Ideal.map_iSup]
    exact iSup_congr fun i => (J i).map_ideal_basicOpen U f

section
variable {Y : Scheme.{u}} {ι : Sort v} (J : ι → Y.IdealSheafData) (U : Y.affineOpens)

private theorem pointwiseSup_ideal_consolidated367 : (iSupIdealSheaf J).ideal U = ⨆ i, (J i).ideal U := rfl

private theorem ideal_iSup_le_iSup_ideal_consolidated367 : (⨆ i, J i).ideal U ≤ ⨆ i, (J i).ideal U := by
  have h : (⨆ i, J i) ≤ iSupIdealSheaf J := by
    refine iSup_le fun i => Scheme.IdealSheafData.le_def.mpr fun V => ?_
    rw [pointwiseSup_ideal_consolidated367 J V]
    exact le_iSup (fun i' => (J i').ideal V) i
  have h2 := Scheme.IdealSheafData.le_def.mp h U
  rwa [pointwiseSup_ideal_consolidated367 J U] at h2


end

private theorem idealSheafData_mul_le_mul_left_consolidated367 {Y : Scheme.{u}} (F : Y.IdealSheafData)
    {A B : Y.IdealSheafData} (h : A ≤ B) : F * A ≤ F * B := by
  refine Scheme.IdealSheafData.le_def.mpr fun U => ?_
  have e1 : (F * A).ideal U = F.ideal U * A.ideal U := rfl
  have e2 : (F * B).ideal U = F.ideal U * B.ideal U := rfl
  rw [e1, e2]
  exact Ideal.mul_mono le_rfl (Scheme.IdealSheafData.le_def.mp h U)

section
variable (k : Type u) [CommRing k] [IsNoetherianRing k] {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (P : Y.IdealSheafData)

theorem logDerivIdealSheaf_iSup_le {ι : Sort v} (J : ι → Y.IdealSheafData) :
    logDerivIdealSheaf k p P (⨆ i, J i) ≤ ⨆ i, logDerivIdealSheaf k p P (J i) := by
  refine Scheme.IdealSheafData.le_def.mpr fun U => ?_
  refine le_trans (@logDerivIdeal_mono k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) _ _
    (ideal_iSup_le_iSup_ideal_consolidated367 J U)) ?_
  refine le_trans (@logDerivIdeal_iSup_le k _ _ _ (sectionsAlgebra k p U.1) ι (P.ideal U)
    (fun i => (J i).ideal U)) ?_
  exact iSup_le fun i =>
    Scheme.IdealSheafData.le_def.mp (le_iSup (fun i' => logDerivIdealSheaf k p P (J i')) i) U

theorem logDerivIdealSheafIterate_iSup_le (r : ℕ)
    {ι : Sort v} (J : ι → Y.IdealSheafData) :
    logDerivIdealSheafIterate k p P r (⨆ i, J i) ≤ ⨆ i, logDerivIdealSheafIterate k p P r (J i) := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
      have h1 : logDerivIdealSheafIterate k p P (r + 1) (⨆ i, J i)
          ≤ ⨆ i, logDerivIdealSheaf k p P (logDerivIdealSheafIterate k p P r (J i)) := by
        rw [logDerivIdealSheafIterate_succ]
        exact le_trans (logDerivIdealSheaf_mono k p P ih)
          (logDerivIdealSheaf_iSup_le k p P
            (fun i => logDerivIdealSheafIterate k p P r (J i)))
      refine h1.trans (iSup_le fun i => le_iSup_of_le i ?_)
      exact le_of_eq (logDerivIdealSheafIterate_succ k p P r (J i)).symm

theorem logDerivIdealSheafIterate_biSup_le (r n : ℕ)
    (J : ℕ → Y.IdealSheafData) :
    logDerivIdealSheafIterate k p P r (⨆ l, ⨆ _ : l ≤ n, J l) ≤
      ⨆ l, ⨆ _ : l ≤ n, logDerivIdealSheafIterate k p P r (J l) := by
  refine le_trans (logDerivIdealSheafIterate_iSup_le k p P r
    (fun l => ⨆ _ : l ≤ n, J l)) ?_
  refine iSup_le fun l => ?_
  refine le_trans (logDerivIdealSheafIterate_iSup_le k p P r (fun _ : l ≤ n => J l)) ?_
  exact iSup_le fun h => le_iSup_of_le l (le_iSup_of_le h le_rfl)


end

theorem derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_of_blowup
    (k : Type u) [Field k] [CharZero k] {X X₁ : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (π : X₁ ⟶ X) [IsLocallyNoetherian X₁]
    (Z H : X.IdealSheafData) (E : List X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (hHZ : H ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (m : ℕ) (K : ℕ → X.IdealSheafData) (hK : ∀ l ≤ m, K l ≤ Z ^ (m - l))
    (hest : ∀ n < m,
      derivIdealSheafIterate k p n (K 0) ≤
        ⨆ l, ⨆ _ : l ≤ n, logDerivIdealSheafIterate k p H (n - l) (K l))
    (K' : ℕ → X₁.IdealSheafData)
    (hK' : ∀ l ≤ m, Blowup.exceptionalIdeal π Z ^ (m - l) * K' l = (K l).comap π)
    (n : ℕ) (hn : n < m) :
    haveI : Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
    derivIdealSheafIterate k (π ≫ p) n (K' 0) ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (K' l) := by
  have hsm : Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
  show derivIdealSheafIterate k (π ≫ p) n (K' 0) ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (K' l)
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := hπ.1
  have hK0 : K 0 ≤ Z ^ m := by simpa using hK 0 (Nat.zero_le m)
  have hA : ∀ l : ℕ, derivIdealSheafIterate k p l (K 0) ≤ Z ^ (m - l) := fun l =>
    derivIdealSheafIterate_le_pow_of_hasStrictNormalCrossingsWith k p Z (K 0) (H :: E) hsnc m hK0 l
  obtain ⟨L, hLspec⟩ : ∃ L : ℕ → X₁.IdealSheafData, ∀ l : ℕ,
      Blowup.exceptionalIdeal π Z ^ (m - l) * L l = (derivIdealSheafIterate k p l (K 0)).comap π :=
    ⟨fun l => controlledTransform π Z (derivIdealSheafIterate k p l (K 0)) (m - l) hπ (hA l),
      fun l => exceptionalIdeal_pow_mul_controlledTransform π Z (derivIdealSheafIterate k p l (K 0)) (m - l) hπ (hA l)⟩
  have hL0 : L 0 = K' 0 := by
    refine Blowup.IsLocallyGeneratedByNonZeroDivisor.eq_of_mul_eq_mul (hcart.pow (m - 0)) ?_
    rw [hLspec 0, hK' 0 (Nat.zero_le m), derivIdealSheafIterate_zero]
  have hstep : ∀ l, l ≤ n → L l ≤
      ⨆ j, ⨆ _ : j ≤ l,
        logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (l - j) (K' j) := by
    intro l hl
    have hlm : l < m := lt_of_le_of_lt hl hn
    have key : ∀ j, j ≤ l → (logDerivIdealSheafIterate k p H (l - j) (K j)).comap π ≤
        Blowup.exceptionalIdeal π Z ^ (m - l) *
          logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (l - j) (K' j) := by
      intro j hj
      have hjm : j ≤ m := by omega
      have ha : l - j ≤ m - j := by omega
      have h3 := comap_logDerivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p π Z H E hsnc hHZ hπ
        (K j) (m - j) (hK j hjm) (l - j) ha
      have h4 : K' j = controlledTransform π Z (K j) (m - j) hπ (hK j hjm) :=
        eq_controlledTransform_of_mul_eq_comap π Z (K j) (m - j) hπ (hK j hjm) (K' j) (hK' j hjm)
      have harith : m - j - (l - j) = m - l := by omega
      rw [h4, ← harith]
      exact h3
    refine Blowup.IsLocallyGeneratedByNonZeroDivisor.le_of_mul_le_mul (hcart.pow (m - l)) ?_
    rw [hLspec l]
    refine le_trans (Scheme.IdealSheafData.comap_mono π (hest l hlm)) ?_
    refine le_trans (le_of_eq (comap_iSup_le_nat π l
      (fun j => logDerivIdealSheafIterate k p H (l - j) (K j)))) ?_
    refine iSup_le fun j => iSup_le fun hj => ?_
    exact le_trans (key j hj) (idealSheafData_mul_le_mul_left_consolidated367 _
      (le_iSup_of_le j (le_iSup_of_le hj le_rfl)))
  have hmain := derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_strictTransform
    k p π Z H E hsnc hHZ hπ (K 0) m L (fun l _ => hLspec l) n hn.le
  rw [hL0] at hmain
  refine le_trans hmain (iSup_le fun l => iSup_le fun hl => ?_)
  refine le_trans (logDerivIdealSheafIterate_mono k (π ≫ p) (Blowup.strictTransform π Z H) (n - l)
    (hstep l hl)) ?_
  refine le_trans (logDerivIdealSheafIterate_biSup_le k (π ≫ p) (Blowup.strictTransform π Z H)
    (n - l) l
    (fun j => logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (l - j) (K' j))) ?_
  refine iSup_le fun j => iSup_le fun hj => ?_
  rw [← logDerivIdealSheafIterate_add]
  have harith3 : n - l + (l - j) = n - j := by omega
  rw [harith3]
  exact le_iSup_of_le j (le_iSup_of_le (le_trans hj hl) le_rfl)

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryAfterBlowup
section

open TopologicalSpace

section

namespace DivisorReductionBoundary

private theorem mem_closeds_compl_consolidated354 {α : Type u} [TopologicalSpace α]
    (S : TopologicalSpace.Closeds α) (x : α) : x ∈ S.compl ↔ x ∉ S := Iff.rfl

private theorem saturation_top_eq_top_consolidated354 {Y : Scheme.{u}} (F : Y.IdealSheafData) :
    saturation F (⊤ : Y.IdealSheafData) = ⊤ := by
  have h := comap_le_strictTransform (𝟙 Y) F (⊤ : Y.IdealSheafData)
  rw [strictTransform_eq_saturation, Scheme.IdealSheafData.comap_id,
    Scheme.IdealSheafData.comap_id] at h
  exact top_le_iff.mp h

section
variable {X : Scheme.{u}}

private theorem restrictIdeal_mul_consolidated354 (A B : X.IdealSheafData) (U : X.Opens) :
    restrictIdeal (A * B) U = restrictIdeal A U * restrictIdeal B U :=
  Scheme.IdealSheafData.comap_mul A B U.ι

private theorem restrictIdeal_strictTransform_id_consolidated354 [IsLocallyNoetherian X]
    (Z D : X.IdealSheafData) (U : X.Opens) :
    restrictIdeal (Blowup.strictTransform (𝟙 X) Z D) U =
      saturation (restrictIdeal Z U) (restrictIdeal D U) := by
  have h1 := restrictIdeal_strictTransform (𝟙 X) Z D U
  have h2 := strictTransform_comp_ι U (𝟙 U.toScheme) Z D
  rw [Category.id_comp] at h2
  rw [h1, Category.comp_id, h2, strictTransform_eq_saturation, Scheme.IdealSheafData.comap_id,
    Scheme.IdealSheafData.comap_id]


end

private theorem map_eq_self_of_getElem_consolidated354 {α : Type u} (g : α → α) : ∀ l : List α,
    (∀ (i : ℕ) (h : i < l.length), g (l[i]'h) = l[i]'h) → l.map g = l
  | [], _ => rfl
  | a :: t, h => by
      have h0 : g a = a := h 0 (Nat.succ_pos _)
      have ht : t.map g = t :=
        map_eq_self_of_getElem_consolidated354 g t (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))
      rw [List.map_cons, h0, ht]

private theorem eraseIdx_map_eq_consolidated354 {α : Type u} (g : α → α) : ∀ (l : List α) (j : ℕ),
    (∀ (i : ℕ) (h : i < l.length), i ≠ j → g (l[i]'h) = l[i]'h) →
    (l.map g).eraseIdx j = l.eraseIdx j
  | [], _, _ => rfl
  | _ :: t, 0, h => by
      have ht : t.map g = t :=
        map_eq_self_of_getElem_consolidated354 g t
          (fun i hi => h (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_ne_zero i))
      show t.map g = t
      exact ht
  | a :: t, (m + 1), h => by
      have h0 : g a = a := h 0 (Nat.succ_pos _) (Nat.succ_ne_zero m).symm
      have ht := eraseIdx_map_eq_consolidated354 g t m
        (fun i hi hij => h (i + 1) (Nat.succ_lt_succ hi) (fun e => hij (by omega)))
      show g a :: (t.map g).eraseIdx m = a :: t.eraseIdx m
      rw [h0, ht]

section
variable (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ) (hj : j < T.boundary.length)
include hV

theorem strictTransform_comap_boundary_of_ne (i : ℕ) (hi : i < T.boundary.length) (hij : i ≠ j) :
    Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
        ((T.boundary.get ⟨i, hi⟩).comap (𝟙 T.scheme)) = T.boundary.get ⟨i, hi⟩ := by
  have := hV.isNoetherian
  rw [Scheme.IdealSheafData.comap_id]
  refine eq_of_locally_restrictIdeal_eq _ _ fun x => ?_
  by_cases hx : x ∈ (DivisorReduction.containedComponentsIdeal T j hj).support
  · obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZU⟩ :=
      exists_etaleChart_containedComponentsIdeal T hV j hj x hx
    refine ⟨U, hxU, ?_⟩
    rw [restrictIdeal_strictTransform_id_consolidated354, hZU]
    cases hai : a i with
    | none =>
        rw [hnone i hi hai]
        exact saturation_top_eq_top_consolidated354 _
    | some t =>
        have htb : t ≠ b := by
          intro e
          apply hij
          refine hinj i j hi hj b ?_ hab
          rw [hai, e]
        have ht := hsome i hi t hai
        have hq1 : QuasiCompact
            (saturationι (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨i, hi⟩)) :=
          quasiCompact_saturationι_of_isLocallyNoetherian _ _
        have hq2 := quasiCompact_saturationι_restrictIdeal
          (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨i, hi⟩) U
        rw [hZU, ht] at hq2
        have := hq2
        rw [ht]
        exact c.saturation_coordIdeal_of_ne t b htb
  · refine ⟨(DivisorReduction.containedComponentsIdeal T j hj).support.compl,
      (mem_closeds_compl_consolidated354 _ _).mpr hx, ?_⟩
    have hst := restrictIdeal_strictTransform_eq_comap_of_notMem_support (𝟙 T.scheme)
      (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨i, hi⟩)
      (DivisorReduction.containedComponentsIdeal T j hj).support.compl
      (fun y hy => by
        have h' : y ∉ (DivisorReduction.containedComponentsIdeal T j hj).support :=
          (mem_closeds_compl_consolidated354 _ y).mp hy
        simpa using h')
    rw [hst, Scheme.IdealSheafData.comap_id]

theorem isSmoothDivisor_containedComponentsIdeal :
    IsSmoothDivisor T.structMap (DivisorReduction.containedComponentsIdeal T j hj) :=
  ⟨isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal T hV j hj, smooth_subschemeι_containedComponentsIdeal_comp T hV j hj⟩

theorem strictTransform_mul_containedComponentsIdeal :
    Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
          ((T.boundary.get ⟨j, hj⟩).comap (𝟙 T.scheme)) *
        DivisorReduction.containedComponentsIdeal T j hj =
      T.boundary.get ⟨j, hj⟩ := by
  have := hV.isNoetherian
  rw [Scheme.IdealSheafData.comap_id]
  refine eq_of_locally_restrictIdeal_eq _ _ fun x => ?_
  by_cases hx : x ∈ (DivisorReduction.containedComponentsIdeal T j hj).support
  · obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZU⟩ :=
      exists_etaleChart_containedComponentsIdeal T hV j hj x hx
    refine ⟨U, hxU, ?_⟩
    have hDj := hsome j hj b hab
    have hq1 : QuasiCompact
        (saturationι (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩)) :=
      quasiCompact_saturationι_of_isLocallyNoetherian _ _
    have hq2 := quasiCompact_saturationι_restrictIdeal
      (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩) U
    rw [hZU, hDj] at hq2
    have := hq2
    rw [restrictIdeal_mul_consolidated354, restrictIdeal_strictTransform_id_consolidated354, hZU, hDj,
      c.saturation_coordIdeal_self b, Scheme.IdealSheafData.top_mul]
  · refine ⟨(DivisorReduction.containedComponentsIdeal T j hj).support.compl,
      (mem_closeds_compl_consolidated354 _ _).mpr hx, ?_⟩
    have hZtop : restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj)
        (DivisorReduction.containedComponentsIdeal T j hj).support.compl = ⊤ := by
      have h := restrictIdeal_exceptionalIdeal_eq_top_of_notMem_support (𝟙 T.scheme)
        (DivisorReduction.containedComponentsIdeal T j hj) (DivisorReduction.containedComponentsIdeal T j hj).support.compl
        (fun y hy => by
          have h' : y ∉ (DivisorReduction.containedComponentsIdeal T j hj).support :=
            (mem_closeds_compl_consolidated354 _ y).mp hy
          simpa using h')
      rwa [exceptionalIdeal_id] at h
    have hst := restrictIdeal_strictTransform_eq_comap_of_notMem_support (𝟙 T.scheme)
      (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩)
      (DivisorReduction.containedComponentsIdeal T j hj).support.compl
      (fun y hy => by
        have h' : y ∉ (DivisorReduction.containedComponentsIdeal T j hj).support :=
          (mem_closeds_compl_consolidated354 _ y).mp hy
        simpa using h')
    rw [restrictIdeal_mul_consolidated354, hst, Scheme.IdealSheafData.comap_id, hZtop,
      Scheme.IdealSheafData.mul_top]

theorem disjoint_support_strictTransform_containedComponentsIdeal :
    Disjoint
      ((Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
          ((T.boundary.get ⟨j, hj⟩).comap (𝟙 T.scheme))).support : Set ↥T.scheme)
      (((DivisorReduction.containedComponentsIdeal T j hj).support : Set ↥T.scheme)) := by
  have := hV.isNoetherian
  rw [Scheme.IdealSheafData.comap_id, Set.disjoint_right]
  intro x hx
  obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZU⟩ :=
    exists_etaleChart_containedComponentsIdeal T hV j hj x hx
  have hDj := hsome j hj b hab
  have hq1 : QuasiCompact
      (saturationι (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩)) :=
    quasiCompact_saturationι_of_isLocallyNoetherian _ _
  have hq2 := quasiCompact_saturationι_restrictIdeal
    (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩) U
  rw [hZU, hDj] at hq2
  have := hq2
  have hres : restrictIdeal (Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
      (T.boundary.get ⟨j, hj⟩)) U = ⊤ := by
    rw [restrictIdeal_strictTransform_id_consolidated354, hZU, hDj]
    exact c.saturation_coordIdeal_self b
  exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top _ U hres x hxU

theorem take_eraseIdx_lowerBoundaryAfterBlowup :
    ((DivisorReduction.lowerBoundaryAfterBlowup T j hj).eraseIdx j).take (T.boundary.length - 1) =
      T.boundary.eraseIdx j := by
  have hlist : (T.boundary.map (fun D => D.comap (𝟙 T.scheme))).map
        (Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)) =
      T.boundary.map (fun D =>
        Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) (D.comap (𝟙 T.scheme))) := by
    simp only [List.map_map, Function.comp_def]
  have key := eraseIdx_map_eq_consolidated354
    (fun D : T.scheme.IdealSheafData =>
      Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) (D.comap (𝟙 T.scheme)))
    T.boundary j
    (fun i h hij => strictTransform_comap_boundary_of_ne T hV j hj i h hij)
  have hlen : j < (T.boundary.map (fun D =>
      Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
        (D.comap (𝟙 T.scheme)))).length := by
    simpa using hj
  show ((((T.boundary.map (fun D => D.comap (𝟙 T.scheme))).map
        (Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))) ++
      [Blowup.exceptionalIdeal (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)]).eraseIdx j).take
      (T.boundary.length - 1) = T.boundary.eraseIdx j
  rw [hlist, List.eraseIdx_append_of_lt_length hlen, key]
  exact List.take_left' (List.length_eraseIdx_of_lt hj)

theorem inStrictNormalCrossingPosition_comap_lowerBoundaryAfterBlowup :
    InStrictNormalCrossingPosition ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
      ((((DivisorReduction.lowerBoundaryAfterBlowup T j hj).eraseIdx j).take (T.boundary.length - 1)).map
        fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) := by
  rw [take_eraseIdx_lowerBoundaryAfterBlowup T hV j hj]
  exact inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx_of_eq T.structMap T.boundary hV.snc j hj
    (T.boundary.get ⟨j, hj⟩) rfl


end

end DivisorReductionBoundary


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.OrderLocusComparison
section



section

variable (k : Type u) [Field k] [CharZero k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (ι : S ⟶ X) [IsClosedImmersion ι]
    [Smooth (ι ≫ p)]

theorem base_mem_orderAtLeastLocus_of_mem_comap
    (m : ℕ) (hm : 1 ≤ m) (A : X.IdealSheafData) (K : ℕ → X.IdealSheafData)
    (hdom : derivIdealSheafIterate k p (m - 1) A
      ≤ ⨆ l ≤ m - 1, logDerivIdealSheafIterate k p ι.ker (m - 1 - l) (K l))
    (hbal : ∀ l < m, K l ^ m ≤ A ^ (m - l))
    (y : S) (hy : y ∈ orderAtLeastLocus (A.comap ι) m) :
    ι.base y ∈ orderAtLeastLocus A m := by
  have hsupp : ι.base y ∈
      (⨆ l ≤ m - 1, logDerivIdealSheafIterate k p ι.ker (m - 1 - l) (K l)).support := by
    refine mem_support_iSup_le_nat (m - 1)
      (fun l => logDerivIdealSheafIterate k p ι.ker (m - 1 - l) (K l)) (ι.base y) ?_
    intro l hl
    have hlm : l < m := by omega
    have hml : 1 ≤ m - l := by omega
    apply (Scheme.IdealSheafData.mem_support_comap).mp
    refine Scheme.IdealSheafData.support_antitone
      (comap_logDerivIdealSheafIterate_ker_le_derivIdealSheafIterate k p ι (K l) (m - 1 - l)) ?_
    have hpow : ((K l).comap ι) ^ m ≤ (A.comap ι) ^ (m - l) := by
      have h1 : (K l ^ m).comap ι ≤ (A ^ (m - l)).comap ι :=
        Scheme.IdealSheafData.comap_mono ι (hbal l hlm)
      rwa [Scheme.IdealSheafData.comap_pow, Scheme.IdealSheafData.comap_pow] at h1
    have hy2 : y ∈ orderAtLeastLocus ((K l).comap ι) (m - l) :=
      orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le k (ι ≫ p) ((K l).comap ι) (A.comap ι) l m hlm hpow hy
    have hstep := support_derivIdealSheafIterate_eq_orderAtLeastLocus k (ι ≫ p) ((K l).comap ι) hml
    rw [← hstep] at hy2
    have hexp : m - 1 - l = m - l - 1 := by omega
    rw [hexp]
    exact hy2
  rw [← support_derivIdealSheafIterate_eq_orderAtLeastLocus k p A hm]
  exact Scheme.IdealSheafData.support_antitone hdom hsupp

end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ClopenStrictTransform
section

open TopologicalSpace


theorem imageIdealSheaf_comap_ι_eq_self_of_support_subset {Y : Scheme.{u}} (Z : Y.IdealSheafData)
    (U : Y.Opens) (_hU : IsClosed (U : Set Y))
    (hZ : (Z.support : Set Y) ⊆ (U : Set Y)) :
    imageIdealSheaf U.ι (Z.comap U.ι) = Z := by
  have hmem : ∀ x : ↥Z.subscheme, x ∈ (Z.subschemeι ⁻¹ᵁ U) := by
    intro x
    have hx : Z.subschemeι.base x ∈ (Z.support : Set Y) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact Set.mem_range_self x
    exact hZ hx
  have key : ∀ y : ↥Z.subscheme,
      y ∈ Set.range ⇑(Scheme.Opens.ι (Z.subschemeι ⁻¹ᵁ U)).base := by
    intro y
    rw [Scheme.Opens.range_ι]
    exact hmem y
  obtain ⟨e, he⟩ : ∃ e : Z.subscheme ⟶ (Z.subschemeι ⁻¹ᵁ U).toScheme,
      e ≫ Scheme.Opens.ι (Z.subschemeι ⁻¹ᵁ U) = 𝟙 Z.subscheme := by
    refine ⟨IsOpenImmersion.lift (Scheme.Opens.ι (Z.subschemeι ⁻¹ᵁ U)) (𝟙 Z.subscheme)
      (fun y _ => key y), ?_⟩
    exact IsOpenImmersion.lift_fac ..
  have h2 : Scheme.Opens.ι (Z.subschemeι ⁻¹ᵁ U) ≫ e = 𝟙 (Z.subschemeι ⁻¹ᵁ U).toScheme := by
    rw [← cancel_mono (Scheme.Opens.ι (Z.subschemeι ⁻¹ᵁ U)), Category.assoc, he,
      Category.comp_id, Category.id_comp]
  have : IsIso (Scheme.Opens.ι (Z.subschemeι ⁻¹ᵁ U)) := ⟨⟨e, h2, he⟩⟩
  rw [imageIdealSheaf_eq_ker_subschemeι_comp, ← ker_ι_preimage_comp_subschemeι_eq_ker_comap Z U,
    ker_eq_ker_of_isIso_comp (Scheme.Opens.ι (Z.subschemeι ⁻¹ᵁ U) ≫ Z.subschemeι) Z.subschemeι
      (Scheme.Opens.ι (Z.subschemeι ⁻¹ᵁ U)) rfl,
    Scheme.IdealSheafData.ker_subschemeι]

private theorem coe_base_comp_consolidated398 {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    ⇑(a ≫ b).base = ⇑b.base ∘ ⇑a.base := by
  funext x
  simp

section
variable {S Y : Scheme.{u}} (f : S ⟶ Y) [IsClosedImmersion f] (U : S.Opens) (hU : IsClosed (U : Set S))
include hU

private theorem isClosedEmbedding_base_opens_ι_comp_of_isClosed_consolidated398 :
    Topology.IsClosedEmbedding ⇑(U.ι ≫ f).base := by
  have hUce : Topology.IsClosedEmbedding ⇑U.ι.base := by
    refine ⟨U.ι.isOpenEmbedding.toIsEmbedding, ?_⟩
    rw [Scheme.Opens.range_ι]
    exact hU
  rw [coe_base_comp_consolidated398]
  exact (Scheme.Hom.isClosedEmbedding f).comp hUce

theorem support_ker_opens_ι_comp :
    ((Scheme.Hom.ker (U.ι ≫ f)).support : Set Y) = ⇑f.base '' (U : Set S) := by
  have hce : Topology.IsClosedEmbedding ⇑(U.ι ≫ f).base :=
    isClosedEmbedding_base_opens_ι_comp_of_isClosed_consolidated398 f U hU
  have : QuasiCompact (U.ι ≫ f) := by
    constructor
    intro V _ hV
    exact hce.isCompact_preimage hV
  have hrange : Set.range ⇑(U.ι ≫ f).base = ⇑f.base '' (U : Set S) := by
    rw [coe_base_comp_consolidated398, Set.range_comp, Scheme.Opens.range_ι]
  have hclosed : IsClosed (⇑f.base '' (U : Set S)) := by
    rw [← hrange]
    exact hce.isClosed_range
  rw [Scheme.Hom.support_ker, hrange]
  exact hclosed.closure_eq


end

private theorem range_base_comp_consolidated398 {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    Set.range ⇑(a ≫ b).base = ⇑b.base '' Set.range ⇑a.base := by
  rw [coe_base_comp_consolidated398, Set.range_comp]

private theorem quasiCompact_of_isClosedEmbedding_base_consolidated398 {A B : Scheme.{u}} (g : A ⟶ B)
    (hg : Topology.IsClosedEmbedding ⇑g.base) : QuasiCompact g := by
  constructor
  intro V _ hV
  exact hg.isCompact_preimage hV

section
variable {S Y : Scheme.{u}} (f : S ⟶ Y)

private theorem range_base_preimage_ι_comp_ι_eq_of_le_consolidated398 (U : S.Opens)
    (W : Y.Opens) (hW : (f ⁻¹ᵁ W : S.Opens) ≤ U) :
    Set.range ⇑(Scheme.Opens.ι ((U.ι ≫ f) ⁻¹ᵁ W) ≫ U.ι).base
      = Set.range ⇑(Scheme.Opens.ι (f ⁻¹ᵁ W)).base := by
  have h2 : (((U.ι ≫ f) ⁻¹ᵁ W : U.toScheme.Opens) : Set U.toScheme)
      = ⇑U.ι.base ⁻¹' ((f ⁻¹ᵁ W : S.Opens) : Set S) := rfl
  rw [range_base_comp_consolidated398, Scheme.Opens.range_ι, Scheme.Opens.range_ι, h2,
    Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
  refine Set.inter_eq_left.mpr ?_
  intro x hx
  exact hW hx

theorem restrictIdeal_ker_opens_ι_comp_of_preimage_le [IsClosedImmersion f]
    (U : S.Opens) (hU : IsClosed (U : Set S)) (W : Y.Opens)
    (hW : (f ⁻¹ᵁ W : S.Opens) ≤ U) :
    restrictIdeal (Scheme.Hom.ker (U.ι ≫ f)) W = restrictIdeal (Scheme.Hom.ker f) W := by
  have hcif : Topology.IsClosedEmbedding ⇑f.base := Scheme.Hom.isClosedEmbedding f
  have _hciU : IsClosedImmersion U.ι :=
    AlgebraicGeometry.Scheme.Opens.isClosedImmersion_ι_of_isClosed U hU
  have _hqf : QuasiCompact f := quasiCompact_of_isClosedEmbedding_base_consolidated398 f hcif
  have _hqUf : QuasiCompact (U.ι ≫ f) := by
    refine quasiCompact_of_isClosedEmbedding_base_consolidated398 _ ?_
    rw [coe_base_comp_consolidated398]
    exact hcif.comp (Scheme.Hom.isClosedEmbedding U.ι)
  have hrange : Set.range ⇑(Scheme.Opens.ι (f ⁻¹ᵁ W)).base
      = Set.range ⇑(Scheme.Opens.ι ((U.ι ≫ f) ⁻¹ᵁ W) ≫ U.ι).base :=
    (range_base_preimage_ι_comp_ι_eq_of_le_consolidated398 f U W hW).symm
  have hfac : ∀ e : (f ⁻¹ᵁ W).toScheme ⟶ ((U.ι ≫ f) ⁻¹ᵁ W).toScheme,
      e ≫ Scheme.Opens.ι ((U.ι ≫ f) ⁻¹ᵁ W) ≫ U.ι = Scheme.Opens.ι (f ⁻¹ᵁ W) →
      e ≫ ((U.ι ≫ f) ∣_ W) = f ∣_ W := by
    intro e he
    have he' : (e ≫ Scheme.Opens.ι ((U.ι ≫ f) ⁻¹ᵁ W)) ≫ U.ι = Scheme.Opens.ι (f ⁻¹ᵁ W) := by
      rw [Category.assoc]
      exact he
    rw [← cancel_mono (Scheme.Opens.ι W), Category.assoc, morphismRestrict_ι,
      morphismRestrict_ι, ← Category.assoc, ← Category.assoc, he']
  have key : (IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι (f ⁻¹ᵁ W))
      (Scheme.Opens.ι ((U.ι ≫ f) ⁻¹ᵁ W) ≫ U.ι) hrange).hom ≫ ((U.ι ≫ f) ∣_ W) = f ∣_ W :=
    hfac _ (IsOpenImmersion.isoOfRangeEq_hom_fac ..)
  rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ker_comap_ι_eq_ker_morphismRestrict (U.ι ≫ f) W,
    ker_comap_ι_eq_ker_morphismRestrict f W]
  exact (ker_eq_ker_of_isIso_comp (f ∣_ W) ((U.ι ≫ f) ∣_ W)
    (IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι (f ⁻¹ᵁ W))
      (Scheme.Opens.ι ((U.ι ≫ f) ⁻¹ᵁ W) ≫ U.ι) hrange).hom key).symm


end

theorem restrictIdeal_strictTransform_congr {Y Y₁ : Scheme.{u}} [IsLocallyNoetherian Y₁]
    (f : Y₁ ⟶ Y) (Z : Y.IdealSheafData) (W : Y.Opens) (A B : Y.IdealSheafData)
    (h : restrictIdeal A W = restrictIdeal B W) :
    restrictIdeal (Blowup.strictTransform f Z A) (f ⁻¹ᵁ W)
      = restrictIdeal (Blowup.strictTransform f Z B) (f ⁻¹ᵁ W) := by
  have hcomp : Scheme.Opens.ι (f ⁻¹ᵁ W) ≫ f = (f ∣_ W) ≫ Scheme.Opens.ι W :=
    (morphismRestrict_ι f W).symm
  have hA : restrictIdeal (Blowup.strictTransform f Z A) (f ⁻¹ᵁ W)
      = Blowup.strictTransform (f ∣_ W) (restrictIdeal Z W) (restrictIdeal A W) := by
    rw [restrictIdeal_strictTransform f Z A (f ⁻¹ᵁ W), hcomp,
      strictTransform_comp_ι W (f ∣_ W) Z A]
  have hB : restrictIdeal (Blowup.strictTransform f Z B) (f ⁻¹ᵁ W)
      = Blowup.strictTransform (f ∣_ W) (restrictIdeal Z W) (restrictIdeal B W) := by
    rw [restrictIdeal_strictTransform f Z B (f ⁻¹ᵁ W), hcomp,
      strictTransform_comp_ι W (f ∣_ W) Z B]
  rw [hA, hB, h]

section
variable {S Y S₁ Y₁ : Scheme.{u}} [IsLocallyNoetherian Y₁] (ι : S ⟶ Y) [IsClosedImmersion ι] (ι₁ : S₁ ⟶ Y₁) [IsClosedImmersion ι₁] (g : S₁ ⟶ S) (f : Y₁ ⟶ Y) (hsq : ι₁ ≫ f = g ≫ ι) (Z : Y.IdealSheafData) (U : S.Opens) (hU : IsClosed (U : Set S))
include hsq hU

private theorem ker_preimage_ι_comp_eq_strictTransform_of_cover_consolidated398 (hU₁ : IsClosed ((g ⁻¹ᵁ U : S₁.Opens) : Set S₁))
    (hker : Scheme.Hom.ker ι₁ = Blowup.strictTransform f Z (Scheme.Hom.ker ι))
    (W₁ W₂ : Y.Opens) (hcov : ∀ y : Y, y ∈ W₁ ∨ y ∈ W₂)
    (h₁ : (ι ⁻¹ᵁ W₁ : S.Opens) ≤ U)
    (h₂ : ∀ x : S, x ∈ U → ι.base x ∉ W₂) :
    Scheme.Hom.ker ((g ⁻¹ᵁ U).ι ≫ ι₁)
      = Blowup.strictTransform f Z (Scheme.Hom.ker (U.ι ≫ ι)) := by
  have hbase : ∀ x : S₁, f.base (ι₁.base x) = ι.base (g.base x) := by
    intro x
    have hh1 : (ι₁ ≫ f).base x = f.base (ι₁.base x) := by simp
    have hh2 : (g ≫ ι).base x = ι.base (g.base x) := by simp
    rw [← hh1, ← hh2, hsq]
  have hpre₁ : (ι₁ ⁻¹ᵁ (f ⁻¹ᵁ W₁) : S₁.Opens) ≤ (g ⁻¹ᵁ U : S₁.Opens) := by
    intro x hx
    have hx' : f.base (ι₁.base x) ∈ W₁ := hx
    rw [hbase x] at hx'
    have hmem : g.base x ∈ (ι ⁻¹ᵁ W₁ : S.Opens) := hx'
    exact h₁ hmem
  refine eq_of_restrictIdeal_eq_of_iSup_eq_top _ _
    (fun b : Bool => cond b (f ⁻¹ᵁ W₁) (f ⁻¹ᵁ W₂)) ?_ ?_
  · rw [eq_top_iff]
    intro y _
    refine TopologicalSpace.Opens.mem_iSup.mpr ?_
    rcases hcov (f.base y) with hy | hy
    · exact ⟨true, hy⟩
    · exact ⟨false, hy⟩
  · intro b
    cases b with
    | false =>
      show restrictIdeal (Scheme.Hom.ker ((g ⁻¹ᵁ U).ι ≫ ι₁)) (f ⁻¹ᵁ W₂)
        = restrictIdeal (Blowup.strictTransform f Z (Scheme.Hom.ker (U.ι ≫ ι))) (f ⁻¹ᵁ W₂)
      have t1 : restrictIdeal (Scheme.Hom.ker ((g ⁻¹ᵁ U).ι ≫ ι₁)) (f ⁻¹ᵁ W₂) = ⊤ := by
        refine (restrictIdeal_eq_top_iff_forall_notMem_support _ _).mpr ?_
        intro y hy hmem
        have hmem' : y ∈ ((Scheme.Hom.ker ((g ⁻¹ᵁ U).ι ≫ ι₁)).support : Set ↥Y₁) := hmem
        rw [support_ker_opens_ι_comp ι₁ (g ⁻¹ᵁ U) hU₁] at hmem'
        obtain ⟨x, hxU, rfl⟩ := hmem'
        have hxU' : g.base x ∈ U := hxU
        have hfy : f.base (ι₁.base x) ∈ W₂ := hy
        rw [hbase x] at hfy
        exact h₂ (g.base x) hxU' hfy
      have t2 : restrictIdeal (Scheme.Hom.ker (U.ι ≫ ι)) W₂ = ⊤ := by
        refine (restrictIdeal_eq_top_iff_forall_notMem_support _ _).mpr ?_
        intro y hy hmem
        have hmem' : y ∈ ((Scheme.Hom.ker (U.ι ≫ ι)).support : Set ↥Y) := hmem
        rw [support_ker_opens_ι_comp ι U hU] at hmem'
        obtain ⟨x, hxU, rfl⟩ := hmem'
        have hxU' : x ∈ U := hxU
        exact h₂ x hxU' hy
      have t3 : restrictIdeal (Scheme.Hom.ker (U.ι ≫ ι)) W₂
          = restrictIdeal (⊤ : Y.IdealSheafData) W₂ := by
        rw [t2]
        exact (Scheme.IdealSheafData.comap_top ..).symm
      have htop : Blowup.strictTransform f Z (⊤ : Y.IdealSheafData) = (⊤ : Y₁.IdealSheafData) := by
        refine le_antisymm le_top ?_
        have hle := Blowup.comap_le_strictTransform f Z (⊤ : Y.IdealSheafData)
        rwa [Scheme.IdealSheafData.comap_top] at hle
      rw [t1, restrictIdeal_strictTransform_congr f Z W₂ _ _ t3, htop]
      exact (Scheme.IdealSheafData.comap_top ..).symm
    | true =>
      show restrictIdeal (Scheme.Hom.ker ((g ⁻¹ᵁ U).ι ≫ ι₁)) (f ⁻¹ᵁ W₁)
        = restrictIdeal (Blowup.strictTransform f Z (Scheme.Hom.ker (U.ι ≫ ι))) (f ⁻¹ᵁ W₁)
      have e1 := restrictIdeal_ker_opens_ι_comp_of_preimage_le ι₁ (g ⁻¹ᵁ U) hU₁ (f ⁻¹ᵁ W₁) hpre₁
      have e2 := restrictIdeal_ker_opens_ι_comp_of_preimage_le ι U hU W₁ h₁
      rw [e1, hker, restrictIdeal_strictTransform_congr f Z W₁ _ _ e2]

theorem ker_preimage_ι_comp_eq_strictTransform_of_isClopen (hker : Scheme.Hom.ker ι₁ = Blowup.strictTransform f Z (Scheme.Hom.ker ι)) :
    Scheme.Hom.ker ((g ⁻¹ᵁ U).ι ≫ ι₁)
      = Blowup.strictTransform f Z (Scheme.Hom.ker (U.ι ≫ ι)) := by
  have hιemb : Topology.IsClosedEmbedding ⇑ι.base := Scheme.Hom.isClosedEmbedding ι
  have hinj : Function.Injective ⇑ι.base := hιemb.toIsEmbedding.injective
  have hVcl : IsClosed ((U : Set S)ᶜ) := isClosed_compl_iff.mpr U.isOpen
  have hUimg : IsClosed (⇑ι.base '' (U : Set S)) := hιemb.isClosedMap _ hU
  have hVimg : IsClosed (⇑ι.base '' ((U : Set S)ᶜ)) := hιemb.isClosedMap _ hVcl
  have hU₁ : IsClosed ((g ⁻¹ᵁ U : S₁.Opens) : Set S₁) :=
    isOpen_compl_iff.mp (g ⁻¹ᵁ (⟨(U : Set S)ᶜ, hU.isOpen_compl⟩ : S.Opens)).isOpen
  refine ker_preimage_ι_comp_eq_strictTransform_of_cover_consolidated398 ι ι₁ g f hsq Z U hU hU₁ hker
    ⟨(⇑ι.base '' ((U : Set S)ᶜ))ᶜ, hVimg.isOpen_compl⟩
    ⟨(⇑ι.base '' (U : Set S))ᶜ, hUimg.isOpen_compl⟩ ?_ ?_ ?_
  · intro y
    by_cases hy : y ∈ ⇑ι.base '' (U : Set S)
    · left
      obtain ⟨x, hxU, rfl⟩ := hy
      show ι.base x ∈ (⇑ι.base '' ((U : Set S)ᶜ))ᶜ
      rintro ⟨x', hx'V, hx'⟩
      have hx'U : x' ∈ (U : Set S) := by
        rw [hinj hx']
        exact hxU
      exact absurd hx'U hx'V
    · right
      show y ∈ (⇑ι.base '' (U : Set S))ᶜ
      exact hy
  · intro x hx
    have hx' : ι.base x ∈ (⇑ι.base '' ((U : Set S)ᶜ))ᶜ := hx
    by_contra hxU
    exact absurd (show ι.base x ∈ ⇑ι.base '' ((U : Set S)ᶜ) from ⟨x, hxU, rfl⟩) hx'
  · intro x hxU hmem
    have hmem' : ι.base x ∈ (⇑ι.base '' (U : Set S))ᶜ := hmem
    exact absurd (show ι.base x ∈ ⇑ι.base '' (U : Set S) from ⟨x, hxU, rfl⟩) hmem'


end

section
variable {Y Y₁ : Scheme.{u}}

theorem restrictIdeal_exceptionalIdeal (f : Y₁ ⟶ Y)
    (Z : Y.IdealSheafData) (W : Y.Opens) :
    restrictIdeal (Blowup.exceptionalIdeal f Z) (f ⁻¹ᵁ W)
      = Blowup.exceptionalIdeal (f ∣_ W) (restrictIdeal Z W) := by
  show (Z.comap f).comap (Scheme.Opens.ι (f ⁻¹ᵁ W))
      = (Z.comap (Scheme.Opens.ι W)).comap (f ∣_ W)
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    morphismRestrict_ι]

theorem restrictIdeal_strictTransform_preimage [IsLocallyNoetherian Y₁]
    (f : Y₁ ⟶ Y) (Z D : Y.IdealSheafData) (W : Y.Opens) :
    restrictIdeal (Blowup.strictTransform f Z D) (f ⁻¹ᵁ W)
      = Blowup.strictTransform (f ∣_ W) (restrictIdeal Z W) (restrictIdeal D W) := by
  have hcomp : Scheme.Opens.ι (f ⁻¹ᵁ W) ≫ f = (f ∣_ W) ≫ Scheme.Opens.ι W :=
    (morphismRestrict_ι f W).symm
  rw [restrictIdeal_strictTransform f Z D (f ⁻¹ᵁ W), hcomp,
    strictTransform_comp_ι W (f ∣_ W) Z D]


end

end
end FunctorialResolution.EmbeddedResolution
end
