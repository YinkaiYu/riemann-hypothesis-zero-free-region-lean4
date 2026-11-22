import Mathlib
import Core5.M09MaximalContact

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicGeometry
universe u
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.BlowupLogDerivativeIdealBound
section

open TopologicalSpace


section
variable {Y : Scheme.{u}}

private theorem ideal_mul_apply_consolidated326 (A B : Y.IdealSheafData) (V : Y.affineOpens) :
    (A * B).ideal V = A.ideal V * B.ideal V := rfl

private theorem ideal_pow_apply_consolidated326 (A : Y.IdealSheafData) (n : ℕ)
    (V : Y.affineOpens) : (A ^ n).ideal V = A.ideal V ^ n :=
  congrFun (Scheme.IdealSheafData.ideal_pow A n) V

private theorem ideal_top_eq_top_consolidated326 (V : Y.affineOpens) :
    (⊤ : Y.IdealSheafData).ideal V = ⊤ := by simp

private theorem restrictIdeal_top_eq_top_consolidated326 (V : Y.Opens) :
    restrictIdeal (⊤ : Y.IdealSheafData) V = ⊤ := Scheme.IdealSheafData.comap_top _

private theorem ideal_le_ideal_of_le_consolidated326 {A B : Y.IdealSheafData} (h : A ≤ B)
    (V : Y.affineOpens) : A.ideal V ≤ B.ideal V := h V


end

private theorem ideal_map_congr_consolidated326 {R S : Type u} [CommRing R] [CommRing S] {F G : Type u}
    [FunLike F R S] [RingHomClass F R S] [FunLike G R S] [RingHomClass G R S]
    (f : F) (g : G) (h : ∀ x, f x = g x) (I : Ideal R) :
    Ideal.map f I = Ideal.map g I := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, h x]
    exact Ideal.mem_map_of_mem _ hx
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← h x]
    exact Ideal.mem_map_of_mem _ hx

section
variable (k : Type u)

private theorem logDerivIdealSheafIterate_congr_hom_consolidated326 [CommRing k]
    [IsNoetherianRing k] {Y : Scheme.{u}} {q q' : Y ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (h : q = q') (P : Y.IdealSheafData) (r : ℕ)
    (I : Y.IdealSheafData) :
    logDerivIdealSheafIterate k q P r I = logDerivIdealSheafIterate k q' P r I := by
  subst h
  rfl

theorem exists_affineOpen_comap_logDerivIdealSheafIterate_eq [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (π : X₁ ⟶ X) [Smooth (π ≫ p)] (W : X.Opens)
    [IsIso (AlgebraicGeometry.morphismRestrict π W)] (x₁ : ↥X₁) (hx₁ : x₁ ∈ π ⁻¹ᵁ W)
    (a : ℕ) (P K : X.IdealSheafData) :
    ∃ V : X₁.affineOpens, x₁ ∈ V.1 ∧ V.1 ≤ π ⁻¹ᵁ W ∧
      ((logDerivIdealSheafIterate k p P a K).comap π).ideal V =
        (logDerivIdealSheafIterate k (π ≫ p) (P.comap π) a (K.comap π)).ideal V := by
  obtain ⟨⟨V, hVaff⟩, hxV, hVU⟩ :
      ∃ V : X₁.affineOpens, x₁ ∈ V.1 ∧ V.1 ≤ π ⁻¹ᵁ W := by
    apply AlgebraicGeometry.Scheme.exists_affineOpens_mem_le
    exact hx₁
  refine ⟨⟨V, hVaff⟩, hxV, hVU, ?_⟩
  have : IsOpenImmersion (π ∣_ W) := inferInstance
  have : LocallyOfFiniteType (W.ι ≫ p) := inferInstance
  have : LocallyOfFiniteType ((π ∣_ W) ≫ (W.ι ≫ p)) := inferInstance
  have : LocallyOfFiniteType ((π ⁻¹ᵁ W).ι ≫ (π ≫ p)) := inferInstance
  have hq : (π ∣_ W) ≫ (W.ι ≫ p) = (π ⁻¹ᵁ W).ι ≫ (π ≫ p) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  have hP : (P.comap W.ι).comap (π ∣_ W) = (P.comap π).comap (π ⁻¹ᵁ W).ι := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  have hKc : (K.comap W.ι).comap (π ∣_ W) = (K.comap π).comap (π ⁻¹ᵁ W).ι := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  have e1 : ((logDerivIdealSheafIterate k p P a K).comap π).comap (π ⁻¹ᵁ W).ι
      = ((logDerivIdealSheafIterate k p P a K).comap W.ι).comap (π ∣_ W) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  have e2 : ((logDerivIdealSheafIterate k p P a K).comap W.ι).comap (π ∣_ W)
      = (logDerivIdealSheafIterate k (W.ι ≫ p) (P.comap W.ι) a (K.comap W.ι)).comap (π ∣_ W) := by
    rw [logDerivIdealSheafIterate_comap_of_isOpenImmersion k p W.ι P K a]
  have e3 : (logDerivIdealSheafIterate k (W.ι ≫ p) (P.comap W.ι) a (K.comap W.ι)).comap (π ∣_ W)
      = logDerivIdealSheafIterate k ((π ∣_ W) ≫ (W.ι ≫ p)) ((P.comap W.ι).comap (π ∣_ W)) a
          ((K.comap W.ι).comap (π ∣_ W)) :=
    logDerivIdealSheafIterate_comap_of_isOpenImmersion k (W.ι ≫ p) (π ∣_ W) (P.comap W.ι)
      (K.comap W.ι) a
  have e4 : logDerivIdealSheafIterate k ((π ∣_ W) ≫ (W.ι ≫ p)) ((P.comap W.ι).comap (π ∣_ W)) a
        ((K.comap W.ι).comap (π ∣_ W))
      = logDerivIdealSheafIterate k ((π ⁻¹ᵁ W).ι ≫ (π ≫ p)) ((P.comap π).comap (π ⁻¹ᵁ W).ι) a
          ((K.comap π).comap (π ⁻¹ᵁ W).ι) := by
    rw [hP, hKc]
    exact logDerivIdealSheafIterate_congr_hom_consolidated326 k hq _ _ _
  have e5 : (logDerivIdealSheafIterate k (π ≫ p) (P.comap π) a (K.comap π)).comap (π ⁻¹ᵁ W).ι
      = logDerivIdealSheafIterate k ((π ⁻¹ᵁ W).ι ≫ (π ≫ p)) ((P.comap π).comap (π ⁻¹ᵁ W).ι) a
          ((K.comap π).comap (π ⁻¹ᵁ W).ι) :=
    logDerivIdealSheafIterate_comap_of_isOpenImmersion k (π ≫ p) (π ⁻¹ᵁ W).ι (P.comap π) (K.comap π) a
  have hmain : restrictIdeal ((logDerivIdealSheafIterate k p P a K).comap π) (π ⁻¹ᵁ W)
      = restrictIdeal (logDerivIdealSheafIterate k (π ≫ p) (P.comap π) a (K.comap π)) (π ⁻¹ᵁ W) :=
    e1.trans (e2.trans (e3.trans (e4.trans e5.symm)))
  exact ideal_eq_of_restrictIdeal_eq _ _ ⟨V, hVaff⟩ (FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_of_le_of_eq hVU hmain)


end

section
variable (k : Type u) [Field k] [CharZero k] {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (π : X₁ ⟶ X) [IsLocallyNoetherian X₁] (Z H : X.IdealSheafData) (E : List X.IdealSheafData) [QuasiCompact (strictTransformι π Z H)] (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (hHZ : H ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (K : X.IdealSheafData) (c : ℕ) (hK : K ≤ Z ^ c) (a : ℕ) (ha : a ≤ c)
include hsnc hHZ hπ hK ha

theorem exists_affineOpen_comap_logDerivIdealSheafIterate_le (x₁ : ↥X₁) (hx₁ : π.base x₁ ∈ Z.support) :
    haveI : Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
    ∃ V : X₁.affineOpens, x₁ ∈ V.1 ∧
      ((logDerivIdealSheafIterate k p H a K).comap π).ideal V ≤
        (Blowup.exceptionalIdeal π Z ^ (c - a) *
            logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) a
              (controlledTransform π Z K c hπ hK)).ideal V := by
  have hsm : Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
  obtain ⟨U0, hxU0, m, c0, S, aH, aE, hZ0, hHnone, hHsome, -, -, -, -⟩ :=
    hsnc.exists_etaleChart_of_cons hx₁
  obtain ⟨⟨U, hUaff⟩, hxU, hUU0⟩ :
      ∃ V : X.affineOpens, π.base x₁ ∈ V.1 ∧ V.1 ≤ U0 := by
    apply AlgebraicGeometry.Scheme.exists_affineOpens_mem_le
    exact hxU0
  let c1 : EtaleChart p U m := c0.restrict hUU0
  have hZ1 : restrictIdeal Z U = c1.coordIdeal S :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hUU0 c0 Z S hZ0
  have hx₁U : x₁ ∈ π ⁻¹ᵁ U := hxU
  obtain ⟨s, hsS, hx₁B0⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c1 S hπ hZ1 x₁ hx₁U
  let B0 : BlowupChart π c1 S s := blowupChartOfIsBlowup π c1 S hπ hZ1 s hsS
  have hx₁B0' : x₁ ∈ B0.domain := hx₁B0
  obtain ⟨Vsub, hVsubDomain, hV0aff, hx₁V0⟩ := B0.exists_isAffineOpen_mem_le_domain x₁ hx₁B0'
  let B : BlowupChart π c1 S s := B0.restrict Vsub hVsubDomain
  have hdom : B.domain = Vsub := BlowupChart.restrict_domain B0 Vsub hVsubDomain
  have hBaff : IsAffineOpen B.domain := by rw [hdom]; exact hV0aff
  have hx₁B : x₁ ∈ B.domain := by rw [hdom]; exact hx₁V0
  have hEW : restrictIdeal (Blowup.exceptionalIdeal π Z) B.domain = B.chart.coordIdeal {s} :=
    B.restrictIdeal_exceptionalIdeal Z hsS hZ1
  have hEideal : (Blowup.exceptionalIdeal π Z).ideal ⟨B.domain, hBaff⟩
      = Ideal.span {B.chart.coord s} := by
    have h := EtaleChart.ideal_eq_span_coord B.chart hBaff (Blowup.exceptionalIdeal π Z) {s} hEW
    simpa using h
  refine ⟨⟨B.domain, hBaff⟩, hx₁B, ?_⟩
  have hofEqTop : restrictIdeal (Blowup.strictTransform π Z H) B.domain = ⊤ →
      ((logDerivIdealSheafIterate k p H a K).comap π).ideal ⟨B.domain, hBaff⟩ ≤
        (Blowup.exceptionalIdeal π Z ^ (c - a) *
            logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) a
              (controlledTransform π Z K c hπ hK)).ideal ⟨B.domain, hBaff⟩ := by
    intro hST
    have hST2 : restrictIdeal (Blowup.strictTransform π Z H) B.domain
        = restrictIdeal (⊤ : X₁.IdealSheafData) B.domain := by
      rw [hST, restrictIdeal_top_eq_top_consolidated326]
    have hST' : (Blowup.strictTransform π Z H).ideal ⟨B.domain, hBaff⟩ = ⊤ :=
      (ideal_eq_of_restrictIdeal_eq _ _ ⟨B.domain, hBaff⟩ hST2).trans (ideal_top_eq_top_consolidated326 _)
    have h1 : (logDerivIdealSheafIterate k p H a K).ideal ⟨U, hUaff⟩ ≤
        (derivIdealSheafIterate k p a K).ideal ⟨U, hUaff⟩ :=
      ideal_le_ideal_of_le_consolidated326 (logDerivIdealSheafIterate_le_derivIdealSheafIterate k p H a K) _
    have h2 : ((logDerivIdealSheafIterate k p H a K).comap π).ideal ⟨B.domain, hBaff⟩ ≤
        ((derivIdealSheafIterate k p a K).comap π).ideal ⟨B.domain, hBaff⟩ := by
      rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (logDerivIdealSheafIterate k p H a K) π
          ⟨U, hUaff⟩ ⟨B.domain, hBaff⟩ B.domain_le,
        Scheme.IdealSheafData.comap_ideal_eq_map_appLE (derivIdealSheafIterate k p a K) π
          ⟨U, hUaff⟩ ⟨B.domain, hBaff⟩ B.domain_le]
      exact Ideal.map_mono h1
    have h3 := comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p π Z (H :: E) hsnc hπ
      K c hK a ha
    refine le_trans h2 (le_trans (ideal_le_ideal_of_le_consolidated326 h3 ⟨B.domain, hBaff⟩) (le_of_eq ?_))
    rw [ideal_mul_apply_consolidated326, ideal_mul_apply_consolidated326, logDerivIdealSheafIterate_ideal, derivIdealSheafIterate_ideal,
      hST', logDerivIdealIterate_top_eq_derivIdealIterate]
  cases haH : aH with
  | none =>
      have hHU : restrictIdeal H U = ⊤ := restrictIdeal_eq_top_of_le H hUU0 (hHnone haH)
      exact hofEqTop (B.restrictIdeal_strictTransform_of_eq_top Z H hHU)
  | some t =>
      have hHU : restrictIdeal H U = c1.coordIdeal {t} :=
        restrictIdeal_eq_restrict_coordIdeal_of_le hUU0 c0 H {t} (hHsome t haH)
      by_cases hts : t = s
      · subst hts
        exact hofEqTop (B.restrictIdeal_strictTransform_coordIdeal_self Z H hsS hZ1 hHU)
      · have htS : t ∈ S :=
          mem_of_restrictIdeal_eq_coordIdeal_of_le hUaff c1 Z H S t hHZ hHU hZ1 (π.base x₁) hxU hx₁
        have hSTW : restrictIdeal (Blowup.strictTransform π Z H) B.domain = B.chart.coordIdeal {t} :=
          B.restrictIdeal_strictTransform_of_mem_of_ne Z H hsS hZ1 t htS hts hHU
        have hHideal : H.ideal ⟨U, hUaff⟩ = Ideal.span {c1.coord t} := by
          have h := EtaleChart.ideal_eq_span_coord c1 hUaff H {t} hHU
          simpa using h
        have hSTideal : (Blowup.strictTransform π Z H).ideal ⟨B.domain, hBaff⟩
            = Ideal.span {B.chart.coord t} := by
          have h := EtaleChart.ideal_eq_span_coord B.chart hBaff (Blowup.strictTransform π Z H) {t} hSTW
          simpa using h
        let algU : Algebra k Γ(X, U) := sectionsAlgebra k p U
        let algB : Algebra k Γ(X₁, B.domain) := sectionsAlgebra k (π ≫ p) B.domain
        have hcomm : ∀ r : k,
            (π.appLE U B.domain B.domain_le).hom (sectionsAlgebraMap k p U r)
              = sectionsAlgebraMap k (π ≫ p) B.domain r :=
          sectionsAlgebraMap_appLE_apply k p π U B.domain B.domain_le
        let φ : Γ(X, U) →ₐ[k] Γ(X₁, B.domain) :=
          { toRingHom := (π.appLE U B.domain B.domain_le).hom
            commutes' := hcomm }
        have hφ : ∀ x, φ x = (π.appLE U B.domain B.domain_le).hom x := fun _ => rfl
        have hmapRestrict : ∀ I : Ideal Γ(X, U),
            Ideal.map φ I = Ideal.map (π.appLE U B.domain B.domain_le).hom I :=
          fun I => ideal_map_congr_consolidated326 φ (π.appLE U B.domain B.domain_le).hom hφ I
        have hcoordU : ∀ i : ULift.{u} (Fin m),
            @EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X, U) _ c1.algebra i
              = c1.coord i.down :=
          fun i => EtaleChart.etaleCoordinates_coord c1 i.down
        have hcoordW : ∀ i : ULift.{u} (Fin m),
            @EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X₁, B.domain) _ B.chart.algebra i
              = B.chart.coord i.down :=
          fun i => EtaleChart.etaleCoordinates_coord B.chart i.down
        have hcoordUt : @EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X, U) _ c1.algebra
            (ULift.up t) = c1.coord t := EtaleChart.etaleCoordinates_coord c1 t
        have hcoordWt : @EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X₁, B.domain) _
            B.chart.algebra (ULift.up t) = B.chart.coord t :=
          EtaleChart.etaleCoordinates_coord B.chart t
        have hcoordWs : @EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X₁, B.domain) _
            B.chart.algebra (ULift.up s) = B.chart.coord s :=
          EtaleChart.etaleCoordinates_coord B.chart s
        have hin : ∀ i ∈ uliftFinset m S, i ≠ (ULift.up s : ULift.{u} (Fin m)) →
            φ (@EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X, U) _ c1.algebra i) =
              (@EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X₁, B.domain) _
                  B.chart.algebra i) *
                (@EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X₁, B.domain) _
                  B.chart.algebra (ULift.up s)) := by
          intro i hi hne
          rw [hcoordU i, hcoordW i, hcoordW (ULift.up s), hφ]
          exact B.appLE_coord_of_mem i.down (down_mem_of_mem_uliftFinset hi)
            (fun h => hne (congrArg ULift.up h))
        have hself : φ (@EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X, U) _ c1.algebra
              (ULift.up s))
            = @EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X₁, B.domain) _ B.chart.algebra
              (ULift.up s) := by
          rw [hcoordU (ULift.up s), hcoordW (ULift.up s), hφ]
          exact B.appLE_coord_self
        have hout : ∀ i ∉ uliftFinset m S,
            φ (@EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X, U) _ c1.algebra i) =
              @EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X₁, B.domain) _
                B.chart.algebra i := by
          intro i hi
          rw [hcoordU i, hcoordW i, hφ]
          exact B.appLE_coord_of_not_mem i.down (fun h => hi (up_mem_uliftFinset h))
        have hnzd : (@EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X₁, B.domain) _
            B.chart.algebra (ULift.up s)) ∈ nonZeroDivisors Γ(X₁, B.domain) := by
          rw [hcoordWs]
          exact coord_mem_nonZeroDivisors hBaff B.chart s
        have hJ : Ideal.map φ (K.ideal ⟨U, hUaff⟩) ≤
            Ideal.span {(@EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X₁, B.domain) _
                B.chart.algebra (ULift.up s)) ^ c} *
              (controlledTransform π Z K c hπ hK).ideal ⟨B.domain, hBaff⟩ := by
          rw [hcoordWs, hmapRestrict]
          refine le_of_eq ?_
          rw [← Ideal.span_singleton_pow, ← hEideal, ← ideal_pow_apply_consolidated326, ← ideal_mul_apply_consolidated326,
            exceptionalIdeal_pow_mul_controlledTransform π Z K c hπ hK]
          exact (Scheme.IdealSheafData.comap_ideal_eq_map_appLE K π ⟨U, hUaff⟩
            ⟨B.domain, hBaff⟩ B.domain_le).symm
        have key := @EtaleCoordinates.map_logDerivIdealIterate_le_span_pow_mul k _ (ULift.{u} (Fin m))
          (Classical.decEq (ULift.{u} (Fin m)))
          Γ(X, U) _ (sectionsAlgebra k p U) c1.algebra c1.isScalarTower
          (c1.algebra_formallyEtale hUaff)
          Γ(X₁, B.domain) _ (sectionsAlgebra k (π ≫ p) B.domain) B.chart.algebra
          B.chart.isScalarTower (B.chart.algebra_formallyEtale hBaff)
          φ (uliftFinset m S) (ULift.up s) _
          hin hself hout (up_mem_uliftFinset hsS) hnzd (ULift.up t) (up_mem_uliftFinset htS)
          (fun h => hts (congrArg ULift.down h))
          (K.ideal ⟨U, hUaff⟩) ((controlledTransform π Z K c hπ hK).ideal ⟨B.domain, hBaff⟩)
          c hJ a ha
        rw [hcoordUt, hcoordWs, hcoordWt, hmapRestrict] at key
        rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (logDerivIdealSheafIterate k p H a K) π
            ⟨U, hUaff⟩ ⟨B.domain, hBaff⟩ B.domain_le,
          logDerivIdealSheafIterate_ideal, hHideal, ideal_mul_apply_consolidated326, ideal_pow_apply_consolidated326, hEideal,
          logDerivIdealSheafIterate_ideal, hSTideal, Ideal.span_singleton_pow]
        exact key

theorem comap_logDerivIdealSheafIterate_le_exceptionalIdeal_pow_mul :
    haveI : Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
    (logDerivIdealSheafIterate k p H a K).comap π ≤
      Blowup.exceptionalIdeal π Z ^ (c - a) *
        logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) a
          (controlledTransform π Z K c hπ hK) := by
  have hsm : Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
  refine le_of_forall_exists_affineOpen ?_
  intro y
  by_cases hy : π.base y ∈ Z.support
  · exact exists_affineOpen_comap_logDerivIdealSheafIterate_le k p π Z H E hsnc hHZ hπ K c hK a ha
      y hy
  · have : IsIso (π ∣_ Z.support.compl) :=
      isIso_morphismRestrict_of_isBlowupAlongIdealSheaf hπ Z.support.compl (fun x hx => hx)
    have hyW : y ∈ π ⁻¹ᵁ Z.support.compl := hy
    obtain ⟨V, hyV, hVW, heq⟩ :=
      exists_affineOpen_comap_logDerivIdealSheafIterate_eq k p π Z.support.compl y hyW a H K
    have hEV2 : restrictIdeal (Blowup.exceptionalIdeal π Z) V.1
        = restrictIdeal (⊤ : X₁.IdealSheafData) V.1 := by
      rw [restrictIdeal_exceptionalIdeal_eq_top_of_le_compl π Z V.1 hVW, restrictIdeal_top_eq_top_consolidated326]
    have hEV : (Blowup.exceptionalIdeal π Z).ideal V = ⊤ :=
      (ideal_eq_of_restrictIdeal_eq _ _ V hEV2).trans (ideal_top_eq_top_consolidated326 _)
    have hSTV : (Blowup.strictTransform π Z H).ideal V = (H.comap π).ideal V :=
      ideal_eq_of_restrictIdeal_eq _ _ V
        (restrictIdeal_strictTransform_eq_comap_of_le_compl π Z H V.1 hVW)
    have hCTV : (controlledTransform π Z K c hπ hK).ideal V = (K.comap π).ideal V := by
      have h := congrArg (fun A : X₁.IdealSheafData => A.ideal V)
        (exceptionalIdeal_pow_mul_controlledTransform π Z K c hπ hK)
      simp only [ideal_mul_apply_consolidated326, ideal_pow_apply_consolidated326, hEV] at h
      rw [← Ideal.one_eq_top, one_pow, one_mul] at h
      exact h
    have hexcPow : (Blowup.exceptionalIdeal π Z ^ (c - a) *
          logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) a
            (controlledTransform π Z K c hπ hK)).ideal V
        = (logDerivIdealSheafIterate k (π ≫ p) (H.comap π) a (K.comap π)).ideal V := by
      rw [ideal_mul_apply_consolidated326, ideal_pow_apply_consolidated326, hEV, ← Ideal.one_eq_top, one_pow, one_mul,
        logDerivIdealSheafIterate_ideal, logDerivIdealSheafIterate_ideal, hSTV, hCTV]
    exact ⟨V, hyV, le_of_eq (heq.trans hexcPow.symm)⟩


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.StrictTransformLogDerivativeIdealSheaf
section

open TopologicalSpace


section
variable {Y : Scheme.{u}}

private theorem top_ideal_eq_top_consolidated325 (U : Y.affineOpens) :
    (⊤ : Y.IdealSheafData).ideal U = ⊤ := by
  simp [Scheme.IdealSheafData.ideal_top]

private theorem pow_ideal_eq_ideal_pow_consolidated325 (A : Y.IdealSheafData)
    (U : Y.affineOpens) : ∀ j : ℕ, (A ^ j).ideal U = A.ideal U ^ j :=
  fun j => congrFun (Scheme.IdealSheafData.ideal_pow A j) U

private theorem restrictIdeal_top_consolidated325 (U : Y.Opens) :
    restrictIdeal (⊤ : Y.IdealSheafData) U = ⊤ := by
  simp [restrictIdeal_eq_comap_ι]

private theorem ideal_affineOpen_eq_top_of_restrictIdeal_eq_top_consolidated325 (D : Y.IdealSheafData)
    {V : Y.Opens} (hV : IsAffineOpen V) (h : restrictIdeal D V = ⊤) :
    D.ideal ⟨V, hV⟩ = ⊤ := by
  have h2 : restrictIdeal D V = restrictIdeal (⊤ : Y.IdealSheafData) V := by
    rw [restrictIdeal_top_consolidated325]
    exact h
  rw [ideal_eq_of_restrictIdeal_eq D ⊤ ⟨V, hV⟩ h2, top_ideal_eq_top_consolidated325]


end

section
variable (k : Type u) [Field k] [CharZero k] {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (π : X₁ ⟶ X) [IsLocallyNoetherian X₁] (Z H : X.IdealSheafData) (E : List X.IdealSheafData) (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (hHZ : H ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) [QuasiCompact (strictTransformι π Z H)] (A : X.IdealSheafData) (m : ℕ) (L : ℕ → X₁.IdealSheafData) (hL : ∀ l ≤ m, Blowup.exceptionalIdeal π Z ^ (m - l) * L l = (derivIdealSheafIterate k p l A).comap π) (n : ℕ) (hn : n ≤ m)
include hsnc hHZ hπ hL hn

theorem exists_affineOpen_derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate
    (x₁ : ↥X₁) (hx₁ : π.base x₁ ∈ Z.support) :
    haveI : Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
    ∃ V : X₁.affineOpens, x₁ ∈ V.1 ∧
      (derivIdealSheafIterate k (π ≫ p) n (L 0)).ideal V ≤
        (⨆ l, ⨆ _ : l ≤ n,
            logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (L l)).ideal V := by
  let hsmooth : Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
  show ∃ V : X₁.affineOpens, x₁ ∈ V.1 ∧
      (derivIdealSheafIterate k (π ≫ p) n (L 0)).ideal V ≤
        (⨆ l, ⨆ _ : l ≤ n,
            logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (L l)).ideal V
  obtain ⟨U, hxU, mm, c, S, aH, a, hZU, hHtop, hHcoord, -, -, -, -⟩ :=
    hsnc.exists_etaleChart_of_cons hx₁
  obtain ⟨U', _mm2, hxU', hU'U, hU'aff, -⟩ := exists_etaleChart_le p (π.base x₁) U hxU
  obtain ⟨cU, hZU', hHU'⟩ : ∃ cU : EtaleChart p U' mm, restrictIdeal Z U' = cU.coordIdeal S ∧
      (restrictIdeal H U' = ⊤ ∨ ∃ t : Fin mm, restrictIdeal H U' = cU.coordIdeal {t}) := by
    refine ⟨c.restrict hU'U, restrictIdeal_eq_restrict_coordIdeal_of_le hU'U c Z S hZU, ?_⟩
    cases haH : aH with
    | none => exact Or.inl (FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_top_of_le H hU'U (hHtop haH))
    | some t =>
        exact Or.inr ⟨t, restrictIdeal_eq_restrict_coordIdeal_of_le hU'U c H {t} (hHcoord t haH)⟩
  have hx₁U' : x₁ ∈ π ⁻¹ᵁ U' := hxU'
  obtain ⟨s, hs, hx₁dom⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π cU S hπ hZU' x₁ hx₁U'
  obtain ⟨B, hBaff, hx₁B⟩ : ∃ B : BlowupChart π cU S s, IsAffineOpen B.domain ∧ x₁ ∈ B.domain := by
    obtain ⟨V, hVle, hVaff, hxV⟩ :=
      (blowupChartOfIsBlowup π cU S hπ hZU' s hs).exists_isAffineOpen_mem_le_domain x₁ hx₁dom
    refine ⟨(blowupChartOfIsBlowup π cU S hπ hZU' s hs).restrict V hVle, ?_, ?_⟩
    · rw [BlowupChart.restrict_domain]
      exact hVaff
    · rw [BlowupChart.restrict_domain]
      exact hxV
  have hcase : (Blowup.strictTransform π Z H).ideal ⟨B.domain, hBaff⟩ = ⊤ ∨
      ∃ t : Fin mm, (Blowup.strictTransform π Z H).ideal ⟨B.domain, hBaff⟩
          = Ideal.span {B.chart.coord t} ∧ t ≠ s ∧ t ∈ S := by
    rcases hHU' with hHtopU | ⟨t, hHt⟩
    · exact Or.inl (ideal_affineOpen_eq_top_of_restrictIdeal_eq_top_consolidated325 _ hBaff
        (B.restrictIdeal_strictTransform_of_eq_top Z H hHtopU))
    · by_cases hts : t = s
      · subst hts
        exact Or.inl (ideal_affineOpen_eq_top_of_restrictIdeal_eq_top_consolidated325 _ hBaff
          (B.restrictIdeal_strictTransform_coordIdeal_self Z H hs hZU' hHt))
      · have htS : t ∈ S :=
          mem_of_restrictIdeal_eq_coordIdeal_of_le hU'aff cU Z H S t hHZ hHt hZU'
            (π.base x₁) hxU' hx₁
        refine Or.inr ⟨t, ?_, hts, htS⟩
        rw [B.chart.ideal_eq_span_coord hBaff _ {t}
          (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZU' t htS hts hHt)]
        simp
  rcases hcase with hP | ⟨t, hP, hts, htS⟩
  · refine ⟨⟨B.domain, hBaff⟩, hx₁B, ?_⟩
    refine le_trans ?_ (Scheme.IdealSheafData.le_def.mp (le_iSup₂ (f := fun l (_ : l ≤ n) =>
      logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (L l)) 0
      (Nat.zero_le n)) _)
    rw [derivIdealSheafIterate_ideal, logDerivIdealSheafIterate_ideal, hP,
      logDerivIdealIterate_top_eq_derivIdealIterate, Nat.sub_zero]
  · refine ⟨⟨B.domain, hBaff⟩, hx₁B, ?_⟩
    let instS : Algebra k Γ(X, U') := sectionsAlgebra k p U'
    let instS₁ : Algebra k Γ(X₁, B.domain) := sectionsAlgebra k (π ≫ p) B.domain
    let instPS : Algebra (MvPolynomial (ULift.{u, 0} (Fin mm)) k) Γ(X, U') := cU.algebra
    let instPS₁ : Algebra (MvPolynomial (ULift.{u, 0} (Fin mm)) k) Γ(X₁, B.domain) :=
      B.chart.algebra
    have instST : IsScalarTower k (MvPolynomial (ULift.{u, 0} (Fin mm)) k) Γ(X, U') :=
      cU.isScalarTower
    have instST₁ : IsScalarTower k (MvPolynomial (ULift.{u, 0} (Fin mm)) k) Γ(X₁, B.domain) :=
      B.chart.isScalarTower
    have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u, 0} (Fin mm)) k) Γ(X, U') :=
      cU.algebra_formallyEtale hU'aff
    have instFE₁ :
        Algebra.FormallyEtale (MvPolynomial (ULift.{u, 0} (Fin mm)) k) Γ(X₁, B.domain) :=
      B.chart.algebra_formallyEtale hBaff
    let instDecEq : DecidableEq (ULift.{u, 0} (Fin mm)) := Classical.decEq _
    have hcoordU : ∀ j : Fin mm,
        EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X, U') ⟨j⟩ = cU.coord j :=
      fun j => cU.etaleCoordinates_coord j
    have hcoordV : ∀ j : Fin mm,
        EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X₁, B.domain) ⟨j⟩ = B.chart.coord j :=
      fun j => B.chart.etaleCoordinates_coord j
    have hBle : B.domain ≤ π ⁻¹ᵁ U' := B.domain_le
    let φ : Γ(X, U') →ₐ[k] Γ(X₁, B.domain) :=
      { ((π.appLE U' B.domain hBle).hom) with
        commutes' := fun x => sectionsAlgebraMap_appLE_apply k p π U' B.domain hBle x }
    obtain ⟨T, hmemT⟩ : ∃ T : Finset (ULift.{u, 0} (Fin mm)),
        ∀ i : ULift.{u, 0} (Fin mm), i ∈ T ↔ i.down ∈ S := by
      refine ⟨S.map ⟨ULift.up, fun x y hxy => by simpa using hxy⟩, fun i => ?_⟩
      constructor
      · intro hi
        obtain ⟨j, hj, hji⟩ := Finset.mem_map.1 hi
        rw [← hji]
        exact hj
      · intro hi
        exact Finset.mem_map.2 ⟨i.down, hi, rfl⟩
    have hsT : (⟨s⟩ : ULift.{u, 0} (Fin mm)) ∈ T := (hmemT ⟨s⟩).2 hs
    have hhT : (⟨t⟩ : ULift.{u, 0} (Fin mm)) ∈ T := (hmemT ⟨t⟩).2 htS
    have hhs : (⟨t⟩ : ULift.{u, 0} (Fin mm)) ≠ ⟨s⟩ := fun hh => hts (congrArg ULift.down hh)
    have hin : ∀ i ∈ T, i ≠ (⟨s⟩ : ULift.{u, 0} (Fin mm)) →
        φ (EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X, U') i) =
          EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X₁, B.domain) i *
            EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X₁, B.domain) ⟨s⟩ := by
      rintro ⟨i⟩ hiT hine
      rw [hcoordU, hcoordV, hcoordV]
      exact B.appLE_coord_of_mem i ((hmemT ⟨i⟩).1 hiT) (fun hh => hine (congrArg ULift.up hh))
    have hsc : φ (EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X, U')
          (⟨s⟩ : ULift.{u, 0} (Fin mm))) =
        EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X₁, B.domain) ⟨s⟩ := by
      rw [hcoordU, hcoordV]
      exact B.appLE_coord_self
    have hout : ∀ i ∉ T,
        φ (EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X, U') i) =
          EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X₁, B.domain) i := by
      rintro ⟨i⟩ hiT
      rw [hcoordU, hcoordV]
      exact B.appLE_coord_of_not_mem i (fun hh => hiT ((hmemT ⟨i⟩).2 hh))
    have hnzd : EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X₁, B.domain)
        (⟨s⟩ : ULift.{u, 0} (Fin mm)) ∈ nonZeroDivisors Γ(X₁, B.domain) := by
      rw [hcoordV]
      exact coord_mem_nonZeroDivisors hBaff B.chart s
    have hE : (Blowup.exceptionalIdeal π Z).ideal ⟨B.domain, hBaff⟩
        = Ideal.span {B.chart.coord s} := by
      rw [B.chart.ideal_eq_span_coord hBaff _ {s} (B.restrictIdeal_exceptionalIdeal Z hs hZU')]
      simp
    have hL' : ∀ i ≤ m,
        Ideal.span {EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X₁, B.domain)
            (⟨s⟩ : ULift.{u, 0} (Fin mm)) ^ (m - i)} * (L i).ideal ⟨B.domain, hBaff⟩ =
          Ideal.map φ (derivIdealIterate k i (A.ideal ⟨U', hU'aff⟩)) := by
      intro i hi
      have hmul : (Blowup.exceptionalIdeal π Z ^ (m - i) * L i).ideal ⟨B.domain, hBaff⟩ =
          (Blowup.exceptionalIdeal π Z ^ (m - i)).ideal ⟨B.domain, hBaff⟩ *
            (L i).ideal ⟨B.domain, hBaff⟩ := by
        simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
      rw [hcoordV, ← Ideal.span_singleton_pow, ← hE, ← pow_ideal_eq_ideal_pow_consolidated325, ← hmul,
        hL i hi,
        Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ π ⟨U', hU'aff⟩ ⟨B.domain, hBaff⟩ hBle,
        derivIdealSheafIterate_ideal]
      rfl
    have key : derivIdealIterate k n ((L 0).ideal ⟨B.domain, hBaff⟩) ≤
        ⨆ i, ⨆ _ : i ≤ n, logDerivIdealIterate k
          (Ideal.span {EtaleCoordinates.coord k (ULift.{u, 0} (Fin mm)) Γ(X₁, B.domain)
            (⟨t⟩ : ULift.{u, 0} (Fin mm))}) (n - i) ((L i).ideal ⟨B.domain, hBaff⟩) :=
      EtaleCoordinates.derivIdealIterate_le_iSup_logDerivIdealIterate_controlledTransform
        k (ULift.{u, 0} (Fin mm)) Γ(X, U') Γ(X₁, B.domain) φ T ⟨s⟩ ⟨t⟩
        hsT hin hsc hout hnzd hhT hhs (A.ideal ⟨U', hU'aff⟩)
        (fun i => (L i).ideal ⟨B.domain, hBaff⟩) m hL' n hn
    rw [hcoordV] at key
    rw [derivIdealSheafIterate_ideal]
    refine le_trans key ?_
    refine iSup_le fun i => ?_
    refine iSup_le fun hi => ?_
    have hre : logDerivIdealIterate k (Ideal.span {B.chart.coord t}) (n - i)
          ((L i).ideal ⟨B.domain, hBaff⟩) =
        (logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - i) (L i)).ideal
          ⟨B.domain, hBaff⟩ := by
      rw [logDerivIdealSheafIterate_ideal, hP]
    rw [hre]
    exact Scheme.IdealSheafData.le_def.mp (le_iSup₂ (f := fun l (_ : l ≤ n) =>
      logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (L l)) i hi) _

theorem derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_strictTransform
    :
    haveI : Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
    derivIdealSheafIterate k (π ≫ p) n (L 0) ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (L l) := by
  let hsmooth : Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
  show derivIdealSheafIterate k (π ≫ p) n (L 0) ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (L l)
  have main : ∀ y : ↥X₁, ∃ V : X₁.affineOpens, y ∈ V.1 ∧
      (derivIdealSheafIterate k (π ≫ p) n (L 0)).ideal V ≤
        (⨆ l, ⨆ _ : l ≤ n,
            logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (L l)).ideal V := by
    intro y
    by_cases hy : π.base y ∈ Z.support
    · exact exists_affineOpen_derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate
        k p π Z H E hsnc hHZ hπ A m L hL n hn y hy
    · have hyW : y ∈ π ⁻¹ᵁ (Z.support.compl) := hy
      have : IsIso (π ∣_ (Z.support.compl)) :=
        isIso_morphismRestrict_of_isBlowupAlongIdealSheaf hπ (Z.support.compl) (fun x hx => hx)
      obtain ⟨V, hyV, hVW, heq⟩ :=
        exists_affineOpen_comap_derivIdealSheafIterate_eq k p π (Z.support.compl) y hyW n A
      refine ⟨V, hyV, ?_⟩
      have hEV : (Blowup.exceptionalIdeal π Z).ideal V = ⊤ :=
        ideal_affineOpen_eq_top_of_restrictIdeal_eq_top_consolidated325 _ V.2
          (restrictIdeal_exceptionalIdeal_eq_top_of_le_compl π Z (V : X₁.Opens) hVW)
      have hiterate : ∀ l, l ≤ m →
          (L l).ideal V = ((derivIdealSheafIterate k p l A).comap π).ideal V := by
        intro l hl
        have hx : (Blowup.exceptionalIdeal π Z ^ (m - l) * L l).ideal V
            = ((derivIdealSheafIterate k p l A).comap π).ideal V := by rw [hL l hl]
        have hmul : (Blowup.exceptionalIdeal π Z ^ (m - l) * L l).ideal V
            = (Blowup.exceptionalIdeal π Z ^ (m - l)).ideal V * (L l).ideal V := by
          simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
        rw [hmul, pow_ideal_eq_ideal_pow_consolidated325, hEV, Ideal.top_pow, Ideal.top_mul] at hx
        exact hx
      have h0 : (L 0).ideal V = (A.comap π).ideal V := by
        have h00 := hiterate 0 (Nat.zero_le m)
        rwa [derivIdealSheafIterate_zero] at h00
      have hstep : (derivIdealSheafIterate k (π ≫ p) n (L 0)).ideal V = (L n).ideal V := by
        rw [derivIdealSheafIterate_ideal, h0,
          ← derivIdealSheafIterate_ideal k (π ≫ p) n (A.comap π) V, ← heq, ← hiterate n hn]
      rw [hstep]
      have hmono := Scheme.IdealSheafData.le_def.mp (le_iSup₂ (f := fun l (_ : l ≤ n) =>
        logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (L l)) n
        (le_refl n)) V
      rwa [Nat.sub_self, logDerivIdealSheafIterate_zero] at hmono
  exact le_of_forall_exists_affineOpen main


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.SmoothDivisorOperations
section

open TopologicalSpace

section

theorem restrictIdeal_mul {X : Scheme.{u}} (I J : X.IdealSheafData) (U : X.Opens) :
    restrictIdeal (I * J) U = restrictIdeal I U * restrictIdeal J U :=
  Scheme.IdealSheafData.comap_mul I J U.ι

section
variable {X X' : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k)) (π : X' ⟶ X) {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (V : X'.Opens) (hV : V ≤ π ⁻¹ᵁ U)

private theorem etaleChart_comap_map_comp_affineSpaceFinToSpec_consolidated328 :
    (π.resLE U V hV ≫ c.map) ≫ affineSpaceFinToSpec k m = V.ι ≫ (π ≫ p) := by
  have h1 : π.resLE U V hV ≫ U.ι = V.ι ≫ π := by simp
  rw [Category.assoc, c.comp_struct, ← Category.assoc, h1, Category.assoc]

private theorem etale_etaleChart_comap_map_consolidated328 (he : Etale (π.resLE U V hV)) :
    Etale (π.resLE U V hV ≫ c.map) := by
  have := he
  have := c.isEtale
  infer_instance


end

def EtaleChart.comap {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (π : X' ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (V : X'.Opens) (hV : V ≤ π ⁻¹ᵁ U)
    (he : Etale (π.resLE U V hV)) : EtaleChart (π ≫ p) V m where
  map := π.resLE U V hV ≫ c.map
  comp_struct := etaleChart_comap_map_comp_affineSpaceFinToSpec_consolidated328 p π c V hV
  isEtale := etale_etaleChart_comap_map_consolidated328 p π c V hV he

section
variable {X X' : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k)) (π : X' ⟶ X) {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (V : X'.Opens) (hV : V ≤ π ⁻¹ᵁ U) (he : Etale (π.resLE U V hV))

theorem EtaleChart.comap_map :
    (EtaleChart.comap p π c V hV he).map = π.resLE U V hV ≫ c.map := rfl

theorem EtaleChart.comap_coordIdeal (S : Finset (Fin m)) :
    (EtaleChart.comap p π c V hV he).coordIdeal S =
      (c.coordIdeal S).comap (π.resLE U V hV) := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.comap_map,
    Scheme.IdealSheafData.comap_comp]


end

theorem isSmoothDivisor_mul_of_disjoint_support {X : Scheme.{u}} {k : Type u} [Field k]
    [CharZero k] (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (A B : X.IdealSheafData) (hA : IsSmoothDivisor p A) (hB : IsSmoothDivisor p B)
    (hAB : Disjoint (A.support : Set X) (B.support : Set X)) :
    IsSmoothDivisor p (A * B) := by
  refine isSmoothDivisor_of_locally_coordIdeal (p := p) (A * B) ?_
  intro x
  by_cases hxA : x ∈ A.support
  · have hxB : x ∉ B.support := fun h => Set.disjoint_left.mp hAB hxA h
    obtain ⟨U, m, c, j, hxU, hAU⟩ :=
      exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton p A hA x hxA
    refine ⟨U ⊓ B.support.compl, ⟨hxU, hxB⟩, m, c.restrict inf_le_left, Or.inr ⟨j, ?_⟩⟩
    have hBtop : restrictIdeal B (U ⊓ B.support.compl) = ⊤ := by
      refine (restrictIdeal_eq_top_iff_forall_notMem_support ..).mpr ?_
      intro y hy
      exact hy.2
    have hc := restrictIdeal_eq_restrict_coordIdeal_of_le (U := U) (V := U ⊓ B.support.compl)
      inf_le_left c A {j} hAU
    rw [restrictIdeal_mul, hBtop, Scheme.IdealSheafData.mul_top, hc]
  · by_cases hxB : x ∈ B.support
    · obtain ⟨U, m, c, j, hxU, hBU⟩ :=
        exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton p B hB x hxB
      refine ⟨U ⊓ A.support.compl, ⟨hxU, hxA⟩, m, c.restrict inf_le_left, Or.inr ⟨j, ?_⟩⟩
      have hAtop : restrictIdeal A (U ⊓ A.support.compl) = ⊤ := by
        refine (restrictIdeal_eq_top_iff_forall_notMem_support ..).mpr ?_
        intro y hy
        exact hy.2
      have hc := restrictIdeal_eq_restrict_coordIdeal_of_le (U := U) (V := U ⊓ A.support.compl)
        inf_le_left c B {j} hBU
      rw [restrictIdeal_mul, hAtop, Scheme.IdealSheafData.top_mul, hc]
    · obtain ⟨U, m, hxU, hUW, -, ⟨c⟩⟩ :=
        exists_etaleChart_le p x (A.support.compl ⊓ B.support.compl) ⟨hxA, hxB⟩
      refine ⟨U, hxU, m, c, Or.inl ?_⟩
      have hAtopW : restrictIdeal A (A.support.compl ⊓ B.support.compl) = ⊤ := by
        refine (restrictIdeal_eq_top_iff_forall_notMem_support ..).mpr ?_
        intro y hy
        exact hy.1
      have hBtopW : restrictIdeal B (A.support.compl ⊓ B.support.compl) = ⊤ := by
        refine (restrictIdeal_eq_top_iff_forall_notMem_support ..).mpr ?_
        intro y hy
        exact hy.2
      have hAtop : restrictIdeal A U = ⊤ := restrictIdeal_eq_top_of_le A hUW hAtopW
      have hBtop : restrictIdeal B U = ⊤ := restrictIdeal_eq_top_of_le B hUW hBtopW
      rw [restrictIdeal_mul, hAtop, hBtop, Scheme.IdealSheafData.mul_top]

section
variable {X X' : Scheme.{u}}

private theorem restrictIdeal_comap_eq_top_of_notMem_support_consolidated328 (π : X' ⟶ X)
    (B : X.IdealSheafData) (V : X'.Opens) (hV : ∀ y : X', y ∈ V → π.base y ∉ B.support) :
    restrictIdeal (B.comap π) V = ⊤ := by
  have hcc : B.comap (V.ι ≫ π) = (B.comap π).comap V.ι := by
    rw [Scheme.IdealSheafData.comap_comp]
  have htop : B.comap (V.ι ≫ π) = ⊤ := by
    refine Blowup.comap_eq_top_of_notMem_support (V.ι ≫ π) B ?_
    intro y
    have hy : V.ι.base y ∈ Set.range V.ι.base := Set.mem_range_self y
    rw [Scheme.Opens.range_ι] at hy
    have h2 : π.base (V.ι.base y) ∉ B.support := hV _ hy
    simpa using h2
  rw [restrictIdeal_eq_comap_ι, ← hcc]
  exact htop

theorem isSmoothDivisor_comap_of_isBlowupAlongIdealSheaf {k : Type u} [Field k]
    [CharZero k] (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (π : X' ⟶ X) [Smooth (π ≫ p)] (Z B : X.IdealSheafData)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hB : IsSmoothDivisor p B)
    (hdisj : Disjoint (Z.support : Set X) (B.support : Set X)) :
    IsSmoothDivisor (π ≫ p) (B.comap π) := by
  refine isSmoothDivisor_of_locally_coordIdeal (B.comap π) ?_
  intro x'
  by_cases hx : π.base x' ∈ B.support
  · obtain ⟨U, m, c, j, hxU, hBU⟩ :=
      exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton p B hB (π.base x') hx
    have hxZ : π.base x' ∉ Z.support := fun hZ => (Set.disjoint_left.mp hdisj hZ) hx
    have hWle : (U ⊓ Z.support.compl : X.Opens) ≤ U := inf_le_left
    have hWsup : ∀ y : X, y ∈ (U ⊓ Z.support.compl : X.Opens) → y ∉ Z.support :=
      fun y hy => hy.2
    have hiso : IsIso (π ∣_ (U ⊓ Z.support.compl : X.Opens)) :=
      isIso_morphismRestrict_of_isBlowupAlongIdealSheaf hπ (U ⊓ Z.support.compl : X.Opens) hWsup
    have hiso2 : IsIso (π.resLE (U ⊓ Z.support.compl : X.Opens)
        (π ⁻¹ᵁ (U ⊓ Z.support.compl : X.Opens)) le_rfl) := by
      rw [Scheme.Hom.resLE_eq_morphismRestrict]
      exact hiso
    have he : Etale (π.resLE (U ⊓ Z.support.compl : X.Opens)
        (π ⁻¹ᵁ (U ⊓ Z.support.compl : X.Opens)) le_rfl) := inferInstance
    have hxV : x' ∈ (π ⁻¹ᵁ (U ⊓ Z.support.compl : X.Opens)) := ⟨hxU, hxZ⟩
    refine ⟨π ⁻¹ᵁ (U ⊓ Z.support.compl : X.Opens), hxV, m,
      EtaleChart.comap p π (c.restrict hWle)
        (π ⁻¹ᵁ (U ⊓ Z.support.compl : X.Opens)) le_rfl he, Or.inr ⟨j, ?_⟩⟩
    rw [EtaleChart.comap_coordIdeal,
      restrictIdeal_comap_eq_comap_resLE_restrictIdeal π B (U ⊓ Z.support.compl : X.Opens)
        (π ⁻¹ᵁ (U ⊓ Z.support.compl : X.Opens)) le_rfl,
      restrictIdeal_eq_restrict_coordIdeal_of_le hWle c B {j} hBU]
  · obtain ⟨U, m, hxU, hUW, -, ⟨c⟩⟩ :=
      exists_etaleChart_le (π ≫ p) x' (π ⁻¹ᵁ B.support.compl) hx
    refine ⟨U, hxU, m, c, Or.inl ?_⟩
    refine restrictIdeal_comap_eq_top_of_notMem_support_consolidated328 π B U ?_
    intro y hy
    have hy' : y ∈ π ⁻¹ᵁ B.support.compl := hUW hy
    exact hy'

theorem strictTransform_mul_of_disjoint_support [IsLocallyNoetherian X']
    (π : X' ⟶ X) (Z A B : X.IdealSheafData)
    (hBZ : Disjoint (B.support : Set X) (Z.support : Set X)) :
    Blowup.strictTransform π Z (A * B) = Blowup.strictTransform π Z A * B.comap π := by
  have hqAB : QuasiCompact (strictTransformι π Z (A * B)) :=
    FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian π Z (A * B)
  have hqA : QuasiCompact (strictTransformι π Z A) :=
    FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian π Z A
  refine eq_of_locally_restrictIdeal_eq _ _ ?_
  intro x
  by_cases hx : π.base x ∈ Z.support
  · have hxB : π.base x ∉ B.support := fun hB => (Set.disjoint_left.mp hBZ hB) hx
    refine ⟨π ⁻¹ᵁ B.support.compl, ?_, ?_⟩
    · exact hxB
    · have hVmem : ∀ y : X', y ∈ π ⁻¹ᵁ B.support.compl → π.base y ∉ B.support := by
        intro y hy
        exact hy
      have hBtop : restrictIdeal (B.comap π) (π ⁻¹ᵁ B.support.compl) = ⊤ :=
        restrictIdeal_comap_eq_top_of_notMem_support_consolidated328 π B _ hVmem
      have hcomapB : B.comap ((π ⁻¹ᵁ B.support.compl).ι ≫ π) = ⊤ := by
        rw [Scheme.IdealSheafData.comap_comp]
        exact hBtop
      have hD : (A * B).comap ((π ⁻¹ᵁ B.support.compl).ι ≫ π)
          = A.comap ((π ⁻¹ᵁ B.support.compl).ι ≫ π) := by
        rw [Scheme.IdealSheafData.comap_mul, hcomapB, Scheme.IdealSheafData.mul_top]
      rw [restrictIdeal_mul, hBtop, Scheme.IdealSheafData.mul_top,
        restrictIdeal_strictTransform π Z (A * B) (π ⁻¹ᵁ B.support.compl),
        restrictIdeal_strictTransform π Z A (π ⁻¹ᵁ B.support.compl)]
      exact strictTransform_eq_of_comap_eq _ _ Z (A * B) Z A rfl hD
  · refine ⟨π ⁻¹ᵁ Z.support.compl, ?_, ?_⟩
    · exact hx
    · have hVmem : ∀ y : X', y ∈ π ⁻¹ᵁ Z.support.compl → π.base y ∉ Z.support := by
        intro y hy
        exact hy
      rw [restrictIdeal_strictTransform_eq_comap_of_notMem_support π Z (A * B) _ hVmem,
        Scheme.IdealSheafData.comap_mul, restrictIdeal_mul, restrictIdeal_mul,
        restrictIdeal_strictTransform_eq_comap_of_notMem_support π Z A _ hVmem]


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IteratedComapDivisor
section

open TopologicalSpace

section

namespace TransportedDivisor

def iteratedComap {X : Scheme.{u}} (d : BlowupSequenceData X) (B : (d.obj 0).IdealSheafData) (t : ℕ) :
    (d.obj t).IdealSheafData :=
  Nat.rec (motive := fun n => (d.obj n).IdealSheafData) B
    (fun n ih => ih.comap (d.map n)) t

@[simp]
theorem iteratedComap_zero {X : Scheme.{u}} (d : BlowupSequenceData X) (B : (d.obj 0).IdealSheafData) :
    iteratedComap d B 0 = B := rfl

@[simp]
theorem iteratedComap_succ {X : Scheme.{u}} (d : BlowupSequenceData X) (B : (d.obj 0).IdealSheafData)
    (t : ℕ) : iteratedComap d B (t + 1) = (iteratedComap d B t).comap (d.map t) := rfl

theorem support_strictTransform_subset_preimage {Y Y' : Scheme.{u}} [IsLocallyNoetherian Y']
    (π : Y' ⟶ Y) (Z D : Y.IdealSheafData) :
    ((Blowup.strictTransform π Z D).support : Set Y') ⊆ ⇑π.base ⁻¹' (D.support : Set Y) := by
  have hpre : (((D.comap π).support : Closeds Y') : Set Y') =
      ⇑π.base ⁻¹' (D.support : Set Y) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hclosed : IsClosed (((D.comap π).support : Closeds Y') : Set Y') :=
    (D.comap π).support.2
  rw [support_strictTransform_eq_closure_sdiff π Z D, ← hpre]
  exact closure_minimal Set.sdiff_subset hclosed

theorem isSmoothDivisor_iteratedComap {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (d : BlowupSequenceData X) (L : ℕ) (hL : L ≤ d.length)
    (hsm : ∀ t, t ≤ L → Smooth (BlowupSequenceData.projectionToBase d t ≫ p))
    (B₀ : (d.obj 0).IdealSheafData)
    (hB₀ : IsSmoothDivisor (BlowupSequenceData.projectionToBase d 0 ≫ p) B₀)
    (hcent : ∀ t, t < L →
      Disjoint (((d.center t).support : Set (d.obj t)))
        ((iteratedComap d B₀ t).support : Set (d.obj t))) :
    ∀ t, t ≤ L → IsSmoothDivisor (BlowupSequenceData.projectionToBase d t ≫ p) (iteratedComap d B₀ t) := by
  intro t
  induction t with
  | zero =>
    intro _
    exact hB₀
  | succ n ih =>
    intro hn
    have hlt : n < L := Nat.lt_of_succ_le hn
    have hle : n ≤ L := le_of_lt hlt
    have hs1 : Smooth (BlowupSequenceData.projectionToBase d n ≫ p) := hsm n hle
    have heq : BlowupSequenceData.projectionToBase d (n + 1) ≫ p = d.map n ≫ BlowupSequenceData.projectionToBase d n ≫ p := by
      rw [BlowupSequenceData.projectionToBase_succ, Category.assoc]
    have hs2 : Smooth (d.map n ≫ BlowupSequenceData.projectionToBase d n ≫ p) := by
      rw [← heq]
      exact hsm (n + 1) hn
    have hblow : Blowup.IsBlowupAlongIdealSheaf (d.map n) (d.center n) := d.isBlowup n (lt_of_lt_of_le hlt hL)
    have key := isSmoothDivisor_comap_of_isBlowupAlongIdealSheaf (BlowupSequenceData.projectionToBase d n ≫ p) (d.map n)
      (d.center n) (iteratedComap d B₀ n) hblow (ih hle) (hcent n hlt)
    rw [iteratedComap_succ, heq]
    exact key

theorem strictTransform_eq_mul_iteratedComap {X : Scheme.{u}} (d : BlowupSequenceData X) (L : ℕ)
    (hnoeth : ∀ t, t ≤ L → IsLocallyNoetherian (d.obj t))
    (K A : ∀ t : ℕ, (d.obj t).IdealSheafData) (B₀ : (d.obj 0).IdealSheafData)
    (hK0 : K 0 = A 0 * B₀)
    (hdisj0 : Disjoint ((A 0).support : Set (d.obj 0)) ((B₀).support : Set (d.obj 0)))
    (hKsucc : ∀ t, t < L → K (t + 1) = Blowup.strictTransform (d.map t) (d.center t) (K t))
    (hAsucc : ∀ t, t < L → A (t + 1) = Blowup.strictTransform (d.map t) (d.center t) (A t))
    (hcent : ∀ t, t < L →
      Disjoint (((d.center t).support : Set (d.obj t)))
        ((iteratedComap d B₀ t).support : Set (d.obj t))) :
    ∀ t, t ≤ L →
      K t = A t * iteratedComap d B₀ t ∧
        Disjoint ((A t).support : Set (d.obj t))
          ((iteratedComap d B₀ t).support : Set (d.obj t)) := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨hK0, hdisj0⟩
  | succ n ih =>
    intro hn
    have hlt : n < L := Nat.lt_of_succ_le hn
    have hle : n ≤ L := le_of_lt hlt
    obtain ⟨hKn, hdn⟩ := ih hle
    have hnoe : IsLocallyNoetherian (d.obj (n + 1)) := hnoeth (n + 1) hn
    have hmul : K (n + 1) = A (n + 1) * iteratedComap d B₀ (n + 1) := by
      rw [hKsucc n hlt, hKn, strictTransform_mul_of_disjoint_support (d.map n) (d.center n)
        (A n) (iteratedComap d B₀ n) (hcent n hlt).symm, hAsucc n hlt, iteratedComap_succ]
    refine ⟨hmul, ?_⟩
    have hsub : ((A (n + 1)).support : Set (d.obj (n + 1))) ⊆
        ⇑(d.map n).base ⁻¹' ((A n).support : Set (d.obj n)) := by
      rw [hAsucc n hlt]
      exact support_strictTransform_subset_preimage (d.map n) (d.center n) (A n)
    have hpre : ((((iteratedComap d B₀ n).comap (d.map n)).support : Closeds (d.obj (n + 1))) :
          Set (d.obj (n + 1))) =
        ⇑(d.map n).base ⁻¹' ((iteratedComap d B₀ n).support : Set (d.obj n)) := by
      rw [Scheme.IdealSheafData.support_comap]; rfl
    rw [iteratedComap_succ, hpre]
    rw [Set.disjoint_left] at hdn ⊢
    intro x hx hx'
    exact hdn (hsub hx) hx'

theorem isSmoothDivisor_strictTransform_of_disjoint_center {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (d : BlowupSequenceData X) (L : ℕ) (hL : L ≤ d.length)
    (hnoeth : ∀ t, t ≤ L → IsLocallyNoetherian (d.obj t))
    (hsm : ∀ t, t ≤ L → Smooth (BlowupSequenceData.projectionToBase d t ≫ p))
    (K A : ∀ t : ℕ, (d.obj t).IdealSheafData) (B₀ : (d.obj 0).IdealSheafData)
    (hK0 : K 0 = A 0 * B₀)
    (hdisj0 : Disjoint ((A 0).support : Set (d.obj 0)) ((B₀).support : Set (d.obj 0)))
    (hKsucc : ∀ t, t < L → K (t + 1) = Blowup.strictTransform (d.map t) (d.center t) (K t))
    (hAsucc : ∀ t, t < L → A (t + 1) = Blowup.strictTransform (d.map t) (d.center t) (A t))
    (hB₀ : IsSmoothDivisor (BlowupSequenceData.projectionToBase d 0 ≫ p) B₀)
    (hA : ∀ t, t ≤ L → IsSmoothDivisor (BlowupSequenceData.projectionToBase d t ≫ p) (A t))
    (hcent : ∀ t, t < L →
      Disjoint (((d.center t).support : Set (d.obj t)))
        ((iteratedComap d B₀ t).support : Set (d.obj t))) :
    ∀ t, t ≤ L → IsSmoothDivisor (BlowupSequenceData.projectionToBase d t ≫ p) (K t) := by
  intro t ht
  have hst : Smooth (BlowupSequenceData.projectionToBase d t ≫ p) := hsm t ht
  have hfac := strictTransform_eq_mul_iteratedComap d L hnoeth K A B₀ hK0 hdisj0 hKsucc hAsucc hcent t ht
  have hB := isSmoothDivisor_iteratedComap p d L hL hsm B₀ hB₀ hcent t ht
  rw [hfac.1]
  exact isSmoothDivisor_mul_of_disjoint_support (BlowupSequenceData.projectionToBase d t ≫ p) (A t)
    (iteratedComap d B₀ t) (hA t ht) hB hfac.2

end TransportedDivisor


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPartAlongDivisor
section

open Opposite TopologicalSpace

section

private theorem mem_span_of_pow_mul_mem_span_consolidated260 {R : Type*} [CommRing R] (g h : R)
    (hcan : ∀ (n : ℕ) (z : R), h * z ∈ Ideal.span ({g ^ n} : Set R) →
      z ∈ Ideal.span ({g ^ n} : Set R)) (n m : ℕ) :
    ∀ z : R, h ^ m * z ∈ Ideal.span ({g ^ n} : Set R) → z ∈ Ideal.span ({g ^ n} : Set R) := by
  induction m with
  | zero =>
      intro z hz
      simpa using hz
  | succ m ih =>
      intro z hz
      refine ih z (hcan n (h ^ m * z) ?_)
      have hmul : h * (h ^ m * z) = h ^ (m + 1) * z := by ring
      rw [hmul]
      exact hz

variable {X : Scheme.{u}}

theorem stalkIdeal_one (x : X) : stalkIdeal (1 : X.IdealSheafData) x = ⊤ := by
  have h := stalkIdeal_mul (1 : X.IdealSheafData) (⊤ : X.IdealSheafData) x
  rw [one_mul, stalkIdeal_top] at h
  refine le_antisymm le_top ?_
  rw [h]
  exact Ideal.mul_le.mpr (fun r hr s _ => Ideal.mul_mem_right s _ hr)

theorem stalkIdeal_listProd (L : List X.IdealSheafData) (x : X) :
    stalkIdeal L.prod x = (L.map (fun I => stalkIdeal I x)).prod := by
  induction L with
  | nil =>
      rw [List.prod_nil, List.map_nil, List.prod_nil, stalkIdeal_one x, Ideal.one_eq_top]
  | cons J L ih =>
      rw [List.prod_cons, stalkIdeal_mul, ih, List.map_cons, List.prod_cons]

variable {k : Type u} [Field k]

@[reducible]
def IsEtaleLocallyCoordinateDivisor (p : X ⟶ Spec (CommRingCat.of k)) (D : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
    restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j}

theorem isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition (p : X ⟶ Spec (CommRingCat.of k))
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) (D : X.IdealSheafData) (hD : D ∈ E) :
    IsEtaleLocallyCoordinateDivisor p D := by
  obtain ⟨i, hi, hiD⟩ := List.getElem_of_mem hD
  obtain ⟨-, hpos⟩ := (inStrictNormalCrossingPosition_iff p E).mp hE
  intro x
  obtain ⟨U, hxU, m, c, a, -, hnone, hsome⟩ := InStrictNormalCrossingPositionAt.exists_etaleChart (hpos x)
  refine ⟨U, hxU, m, c, ?_⟩
  cases hai : a i with
  | none =>
      left
      have h := hnone i hi hai
      rwa [hiD] at h
  | some t =>
      right
      refine ⟨t, ?_⟩
      have h := hsome i hi t hai
      rwa [hiD] at h

def orderAlongComponent (I : X.IdealSheafData) {C : Set X} (hC : IsIrreducible C) : ℕ :=
  (orderAt I hC.genericPoint).toNat

theorem orderAlongComponent_eq_orderAt_genericPoint (I : X.IdealSheafData) {C : Set X} (hC : IsIrreducible C) :
    orderAlongComponent I hC = (orderAt I hC.genericPoint).toNat := rfl

theorem coe_orderAlongComponent_eq_orderAt_genericPoint [IsLocallyNoetherian X] {D I : X.IdealSheafData} {C : Set X}
    (hC : IsIrreducibleComponentOfSupport D C) (hI : NonzeroOnComponents I) :
    (orderAlongComponent I hC.isIrreducible : ℕ∞) = orderAt I hC.isIrreducible.genericPoint := by
  have h : orderAt I hC.isIrreducible.genericPoint ≠ ⊤ :=
    hC.orderAt_genericPoint_ne_top I hI
  rw [orderAlongComponent_eq_orderAt_genericPoint, ENat.natCast_toNat h]

def componentPowerIdeal (I D : X.IdealSheafData) (C : Set X) : X.IdealSheafData :=
  letI : Decidable (IsIrreducibleComponentOfSupport D C) := Classical.propDecidable _
  if h : IsIrreducibleComponentOfSupport D C then
    Scheme.IdealSheafData.vanishingIdeal (⟨C, h.isClosed⟩ : TopologicalSpace.Closeds ↥X) ^
      orderAlongComponent I h.isIrreducible
  else ⊤

section
variable (I D : X.IdealSheafData)

theorem componentPowerIdeal_of_not_isIrreducibleComponentOfSupport {C : Set X}
    (h : ¬ IsIrreducibleComponentOfSupport D C) : componentPowerIdeal I D C = ⊤ :=
  @dif_neg (IsIrreducibleComponentOfSupport D C) (Classical.propDecidable (IsIrreducibleComponentOfSupport D C)) h
    X.IdealSheafData _ _

theorem componentPowerIdeal_of_isIrreducibleComponentOfSupport {C : Set X}
    (h : IsIrreducibleComponentOfSupport D C) :
    componentPowerIdeal I D C =
      Scheme.IdealSheafData.vanishingIdeal (⟨C, h.isClosed⟩ : TopologicalSpace.Closeds ↥X) ^
        orderAlongComponent I h.isIrreducible := by
  unfold componentPowerIdeal
  exact dif_pos h

theorem stalkIdeal_componentPowerIdeal_of_not_mem (C : Set X) {x : X}
    (hx : x ∉ C) : stalkIdeal (componentPowerIdeal I D C) x = ⊤ := by
  by_cases hC : IsIrreducibleComponentOfSupport D C
  · have htop : stalkIdeal (Scheme.IdealSheafData.vanishingIdeal
        (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)) x = ⊤ := by
      by_contra h
      have hmem : x ∈ ((Scheme.IdealSheafData.vanishingIdeal
          (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)).support : Set ↥X) :=
        (mem_support_iff_stalkIdeal_ne_top _ x).mpr h
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hmem
      exact hx hmem
    rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC, stalkIdeal_pow, htop, ← Ideal.one_eq_top,
      one_pow]
  · rw [componentPowerIdeal_of_not_isIrreducibleComponentOfSupport I D hC, stalkIdeal_top]


end

theorem stalkIdeal_componentPowerIdeal_of_mem [TopologicalSpace.NoetherianSpace ↥X]
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) {D : X.IdealSheafData}
    (hD : IsEtaleLocallyCoordinateDivisor p D) {C : Set X} (hC : IsIrreducibleComponentOfSupport D C) {x : X}
    (hx : x ∈ C) :
    stalkIdeal (componentPowerIdeal I D C) x =
      stalkIdeal D x ^ orderAlongComponent I hC.isIrreducible := by
  rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC, stalkIdeal_pow,
    hC.stalkIdeal_vanishingIdeal_eq p hD x hx]

def supportComponentsFinset [TopologicalSpace.NoetherianSpace ↥X] (D : X.IdealSheafData) :
    Finset (Set X) :=
  (finite_isIrreducibleComponentOfSupport D).toFinset

def monomialPartAlongDivisor [TopologicalSpace.NoetherianSpace ↥X] (I D : X.IdealSheafData) :
    X.IdealSheafData :=
  (supportComponentsFinset D).inf (fun C => componentPowerIdeal I D C)

theorem monomialPartAlongDivisor_eq_inf_componentPowerIdeal [TopologicalSpace.NoetherianSpace ↥X] (I D : X.IdealSheafData) :
    monomialPartAlongDivisor I D = (supportComponentsFinset D).inf (fun C => componentPowerIdeal I D C) := rfl

section
variable (a b : X.IdealSheafData)

private theorem idealSheafData_mul_le_left_consolidated260 : a * b ≤ a := by
  rw [le_iff_forall_stalkIdeal_le]
  intro x
  rw [stalkIdeal_mul]
  exact Ideal.mul_le.mpr fun r hr s _ => Ideal.mul_mem_right s _ hr

private theorem idealSheafData_mul_le_right_consolidated260 : a * b ≤ b := by
  rw [le_iff_forall_stalkIdeal_le]
  intro x
  rw [stalkIdeal_mul]
  exact Ideal.mul_le.mpr fun r _ s hs => Ideal.mul_mem_left _ r hs

private theorem stalkIdeal_inf_eq_top_consolidated260 (x : X)
    (ha : stalkIdeal a x = ⊤) (hb : stalkIdeal b x = ⊤) :
    stalkIdeal (a ⊓ b) x = ⊤ := by
  refine le_antisymm le_top ?_
  have hmono := stalkIdeal_mono
    (le_inf (idealSheafData_mul_le_left_consolidated260 a b) (idealSheafData_mul_le_right_consolidated260 a b)) x
  rw [stalkIdeal_mul, ha, hb] at hmono
  have htop : (⊤ : Ideal (X.presheaf.stalk x)) * ⊤ = ⊤ := by
    rw [← Ideal.one_eq_top, one_mul]
  rwa [htop] at hmono


end

private theorem stalkIdeal_finsetInf_eq_top_consolidated260 {β : Type u} (f : β → X.IdealSheafData) (x : X)
    (s : Finset β) : (∀ b ∈ s, stalkIdeal (f b) x = ⊤) → stalkIdeal (s.inf f) x = ⊤ := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.inf_empty]
    exact stalkIdeal_top x
  · intro a t ha ih hs
    rw [Finset.inf_insert]
    exact stalkIdeal_inf_eq_top_consolidated260 _ _ x (hs a (Finset.mem_insert_self a t))
      (ih fun b hb => hs b (Finset.mem_insert_of_mem hb))

theorem stalkIdeal_monomialPartAlongDivisor_of_not_mem_support [TopologicalSpace.NoetherianSpace ↥X]
    (I D : X.IdealSheafData) {x : X} (hx : x ∉ (D.support : Set X)) :
    stalkIdeal (monomialPartAlongDivisor I D) x = ⊤ := by
  rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
  refine stalkIdeal_finsetInf_eq_top_consolidated260 (fun C => componentPowerIdeal I D C) x
    (supportComponentsFinset D) ?_
  intro C hC
  have hCmem : IsIrreducibleComponentOfSupport D C :=
    (Set.Finite.mem_toFinset (finite_isIrreducibleComponentOfSupport D)).mp hC
  exact stalkIdeal_componentPowerIdeal_of_not_mem I D C (fun hxC => hx (hCmem.subset_support hxC))

private theorem idealSheafData_listProd_le_of_mem_consolidated260 :
    ∀ (L : List X.IdealSheafData) (a : X.IdealSheafData), a ∈ L → L.prod ≤ a := by
  intro L
  induction L with
  | nil =>
      intro a ha
      simp at ha
  | cons b L ih =>
      intro a ha
      rw [List.prod_cons]
      rcases List.mem_cons.mp ha with h | h
      · rw [h]
        exact idealSheafData_mul_le_left_consolidated260 _ _
      · exact le_trans (idealSheafData_mul_le_right_consolidated260 _ _) (ih a h)

section
variable {α : Type*} {M : Type*} [CommMonoid M] (g : α → M)

private theorem prod_map_eq_one_of_forall_eq_one_consolidated260 (L : List α) (h : ∀ b ∈ L, g b = 1) : (L.map g).prod = 1 :=
  List.prod_eq_one fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact h a ha

private theorem prod_map_eq_apply_of_nodup_of_forall_ne_consolidated260 : ∀ (L : List α) (a : α), L.Nodup → a ∈ L →
      (∀ b ∈ L, b ≠ a → g b = 1) → (L.map g).prod = g a := by
  intro L
  induction L with
  | nil =>
      intro a _ ha _
      simp at ha
  | cons b L ih =>
      intro a hnd ha hone
      rw [List.map_cons, List.prod_cons]
      rcases List.mem_cons.mp ha with h | h
      · have hL : (L.map g).prod = 1 := by
          refine prod_map_eq_one_of_forall_eq_one_consolidated260 g L ?_
          intro c hc
          refine hone c (List.mem_cons.mpr (Or.inr hc)) ?_
          intro hca
          exact absurd (show b ∈ L by rw [← h, ← hca]; exact hc) (List.nodup_cons.mp hnd).1
        rw [hL, mul_one, h]
      · have hb : g b = 1 := by
          refine hone b (List.mem_cons.mpr (Or.inl rfl)) ?_
          intro hba
          exact absurd (show b ∈ L by rw [hba]; exact h) (List.nodup_cons.mp hnd).1
        rw [hb, one_mul]
        exact ih a (List.nodup_cons.mp hnd).2 h
          (fun c hc => hone c (List.mem_cons.mpr (Or.inr hc)))


end

theorem stalkIdeal_monomialPartAlongDivisor_of_mem [TopologicalSpace.NoetherianSpace ↥X]
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) {D : X.IdealSheafData}
    (hD : IsEtaleLocallyCoordinateDivisor p D) {C : Set X} (hC : IsIrreducibleComponentOfSupport D C) {x : X}
    (hx : x ∈ C) :
    stalkIdeal (monomialPartAlongDivisor I D) x = stalkIdeal D x ^ orderAlongComponent I hC.isIrreducible := by
  classical
  have hmemiff : ∀ C' : Set X, C' ∈ supportComponentsFinset D ↔ IsIrreducibleComponentOfSupport D C' := by
    intro C'
    simp only [supportComponentsFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hCS : C ∈ supportComponentsFinset D := (hmemiff C).mpr hC
  have hCpart : stalkIdeal (componentPowerIdeal I D C) x
      = stalkIdeal D x ^ orderAlongComponent I hC.isIrreducible :=
    stalkIdeal_componentPowerIdeal_of_mem p I hD hC hx
  refine le_antisymm ?_ ?_
  · have h1 : monomialPartAlongDivisor I D ≤ componentPowerIdeal I D C := by
      rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
      exact Finset.inf_le hCS
    have h2 := stalkIdeal_mono h1 x
    rwa [hCpart] at h2
  · have hle : ((supportComponentsFinset D).toList.map (fun C' => componentPowerIdeal I D C')).prod
        ≤ monomialPartAlongDivisor I D := by
      rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
      refine Finset.le_inf ?_
      intro C' hC'
      exact idealSheafData_listProd_le_of_mem_consolidated260 _ (componentPowerIdeal I D C')
        (List.mem_map.mpr ⟨C', Finset.mem_toList.mpr hC', rfl⟩)
    have hprod : stalkIdeal
        ((supportComponentsFinset D).toList.map (fun C' => componentPowerIdeal I D C')).prod x
        = stalkIdeal (componentPowerIdeal I D C) x := by
      rw [stalkIdeal_listProd, List.map_map]
      refine prod_map_eq_apply_of_nodup_of_forall_ne_consolidated260 (fun C' => stalkIdeal (componentPowerIdeal I D C') x)
        ((supportComponentsFinset D).toList) C (Finset.nodup_toList _)
        (Finset.mem_toList.mpr hCS) ?_
      intro C' hC' hne
      show stalkIdeal (componentPowerIdeal I D C') x = 1
      have hC'comp : IsIrreducibleComponentOfSupport D C' := (hmemiff C').mp (Finset.mem_toList.mp hC')
      have hdisj : Disjoint C C' := hC.disjoint hC'comp p hD (Ne.symm hne)
      have hxC' : x ∉ C' := Set.disjoint_left.mp hdisj hx
      rw [stalkIdeal_componentPowerIdeal_of_not_mem I D C' hxC', Ideal.one_eq_top]
    have h3 := stalkIdeal_mono hle x
    rw [hprod, hCpart] at h3
    exact h3

def monomialFactorIdeal [TopologicalSpace.NoetherianSpace ↥X] (E : List X.IdealSheafData)
    (I : X.IdealSheafData) : X.IdealSheafData :=
  (E.map (fun D => monomialPartAlongDivisor I D)).prod

section
variable [TopologicalSpace.NoetherianSpace ↥X] (E : List X.IdealSheafData) (I : X.IdealSheafData)

theorem monomialFactorIdeal_eq_prod_monomialPartAlongDivisor :
    monomialFactorIdeal E I = (E.map (fun D => monomialPartAlongDivisor I D)).prod := rfl

theorem stalkIdeal_monomialFactorIdeal (x : X) :
    stalkIdeal (monomialFactorIdeal E I) x =
      (E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D) x)).prod := by
  have h : monomialFactorIdeal E I = (E.map (fun D => monomialPartAlongDivisor I D)).prod := rfl
  rw [h, stalkIdeal_listProd, List.map_map]
  rfl


end

private theorem idealSheafData_ideal_mul_consolidated260 (I J : X.IdealSheafData) (W : X.affineOpens) :
    (I * J).ideal W = I.ideal W * J.ideal W := rfl

section
variable (W : X.affineOpens)

private theorem idealSheafData_ideal_top_consolidated260 :
    (⊤ : X.IdealSheafData).ideal W = ⊤ :=
  (Ideal.eq_top_iff_one _).mpr (by simp)

private theorem idealSheafData_ideal_one_consolidated260 :
    (1 : X.IdealSheafData).ideal W = 1 := by
  rw [Ideal.one_eq_top]
  exact idealSheafData_ideal_top_consolidated260 W


end

private theorem idealSheafData_ideal_pow_consolidated260 (J : X.IdealSheafData) (n : ℕ)
    (W : X.affineOpens) : (J ^ n).ideal W = J.ideal W ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact idealSheafData_ideal_one_consolidated260 W
  | succ n ih => rw [pow_succ, pow_succ, idealSheafData_ideal_mul_consolidated260, ih]

private theorem idealSheafData_ideal_listProd_consolidated260 (L : List X.IdealSheafData) (W : X.affineOpens) :
    L.prod.ideal W = (L.map (fun J => J.ideal W)).prod := by
  induction L with
  | nil => rw [List.prod_nil, List.map_nil, List.prod_nil]; exact idealSheafData_ideal_one_consolidated260 W
  | cons J L ih =>
      rw [List.prod_cons, List.map_cons, List.prod_cons, idealSheafData_ideal_mul_consolidated260, ih]

private theorem ideal_vanishingIdeal_eq_top_of_disjoint_consolidated260 (C : Set X) (hCcl : IsClosed C) (W : X.affineOpens)
    (h : ∀ y : X, y ∈ (W : X.Opens) → y ∉ C) :
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨C, hCcl⟩ : TopologicalSpace.Closeds ↥X)).ideal W = ⊤ := by
  refine (Ideal.eq_top_iff_one _).mpr ?_
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  intro q hq
  have hqC : (W.2.fromSpec).base q ∈ C := hq
  have hmem0 : (W.2.fromSpec).base q ∈ ((W : X.Opens) : Set ↥X) := by
    rw [← AlgebraicGeometry.IsAffineOpen.range_fromSpec W.2]
    exact Set.mem_range_self q
  have hmem : (W.2.fromSpec).base q ∈ (W : X.Opens) := hmem0
  exact absurd hqC (h _ hmem)

private theorem ideal_componentPowerIdeal_eq_top_of_disjoint_consolidated260 (I D : X.IdealSheafData) (C : Set X)
    (W : X.affineOpens) (h : ∀ y : X, y ∈ (W : X.Opens) → y ∉ C) :
    (componentPowerIdeal I D C).ideal W = ⊤ := by
  by_cases hC : IsIrreducibleComponentOfSupport D C
  · rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC, idealSheafData_ideal_pow_consolidated260,
      ideal_vanishingIdeal_eq_top_of_disjoint_consolidated260 C hC.isClosed W h, ← Ideal.one_eq_top, one_pow]
  · rw [componentPowerIdeal_of_not_isIrreducibleComponentOfSupport I D hC]
    exact idealSheafData_ideal_top_consolidated260 W

section
variable [TopologicalSpace.NoetherianSpace ↥X] (p : X ⟶ Spec (CommRingCat.of k))

private theorem exists_nhds_ideal_monomialPartAlongDivisor_eq_span_consolidated260 (I D : X.IdealSheafData)
    (hD : IsEtaleLocallyCoordinateDivisor p D) (x : X) :
    ∃ Ω : X.Opens, x ∈ Ω ∧ ∀ W : X.affineOpens, (W : X.Opens) ≤ Ω →
      ∃ g ∈ nonZeroDivisors Γ(X, (W : X.Opens)),
        (monomialPartAlongDivisor I D).ideal W = Ideal.span {g} := by
  classical
  have hmemiff : ∀ C' : Set X, C' ∈ supportComponentsFinset D ↔ IsIrreducibleComponentOfSupport D C' := by
    intro C'
    simp only [supportComponentsFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hprodle : ∀ W : X.affineOpens,
      (((supportComponentsFinset D).toList.map (fun C => componentPowerIdeal I D C)).prod).ideal W
        ≤ (monomialPartAlongDivisor I D).ideal W := by
    intro W
    have hle : ((supportComponentsFinset D).toList.map (fun C => componentPowerIdeal I D C)).prod
        ≤ monomialPartAlongDivisor I D := by
      rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
      refine Finset.le_inf ?_
      intro C' hC'
      exact idealSheafData_listProd_le_of_mem_consolidated260 _ (componentPowerIdeal I D C')
        (List.mem_map.mpr ⟨C', Finset.mem_toList.mpr hC', rfl⟩)
    exact hle W
  by_cases hx : ∃ C ∈ supportComponentsFinset D, x ∈ C
  · obtain ⟨C₀, hC₀mem, hxC₀⟩ := hx
    have hC₀ : IsIrreducibleComponentOfSupport D C₀ := (hmemiff C₀).mp hC₀mem
    obtain ⟨V, hV, hxV, n, c, j, hDV, hVsupp, -, hagree, -⟩ :=
      hC₀.exists_affineOpen_etaleChart_coordIdeal p hD x hxC₀
    refine ⟨V, hxV, ?_⟩
    intro W hWV
    refine ⟨(c.restrict hWV).coord j ^ orderAlongComponent I hC₀.isIrreducible,
      pow_mem (coord_mem_nonZeroDivisors W.2 (c.restrict hWV) j) _, ?_⟩
    have hres : restrictIdeal D (W : X.Opens) = (c.restrict hWV).coordIdeal {j} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hWV c D {j} hDV
    have hDW : D.ideal W = Ideal.span {(c.restrict hWV).coord j} := by
      have h1 := EtaleChart.ideal_eq_span_coord (c.restrict hWV) W.2 D {j} hres
      simpa using h1
    have hcomp0 : (componentPowerIdeal I D C₀).ideal W
        = Ideal.span {(c.restrict hWV).coord j ^ orderAlongComponent I hC₀.isIrreducible} := by
      rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC₀, idealSheafData_ideal_pow_consolidated260,
        hagree W hWV, hDW, Ideal.span_singleton_pow]
    have hother : ∀ C : Set X, C ∈ (supportComponentsFinset D).toList → C ≠ C₀ →
        (componentPowerIdeal I D C).ideal W = ⊤ := by
      intro C hCmem hne
      have hCcomp : IsIrreducibleComponentOfSupport D C := (hmemiff C).mp (Finset.mem_toList.mp hCmem)
      refine ideal_componentPowerIdeal_eq_top_of_disjoint_consolidated260 I D C W ?_
      intro y hy hyC
      have hyV : y ∈ V := hWV hy
      have hyD : y ∈ (D.support : Set X) := hCcomp.subset_support hyC
      have hyC₀ : y ∈ C₀ := hVsupp y hyV hyD
      have hdisj : Disjoint C C₀ := hCcomp.disjoint hC₀ p hD hne
      exact (Set.disjoint_left.mp hdisj hyC) hyC₀
    have hprodideal : (((supportComponentsFinset D).toList.map
        (fun C => componentPowerIdeal I D C)).prod).ideal W = (componentPowerIdeal I D C₀).ideal W := by
      rw [idealSheafData_ideal_listProd_consolidated260, List.map_map]
      refine prod_map_eq_apply_of_nodup_of_forall_ne_consolidated260 (fun C => (componentPowerIdeal I D C).ideal W)
        ((supportComponentsFinset D).toList) C₀ (Finset.nodup_toList _)
        (Finset.mem_toList.mpr hC₀mem) ?_
      intro C' hC' hne
      show (componentPowerIdeal I D C').ideal W = 1
      rw [Ideal.one_eq_top]
      exact hother C' hC' hne
    refine le_antisymm ?_ ?_
    · rw [← hcomp0]
      have hle : monomialPartAlongDivisor I D ≤ componentPowerIdeal I D C₀ := by
        rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
        exact Finset.inf_le hC₀mem
      exact hle W
    · rw [← hcomp0, ← hprodideal]
      exact hprodle W
  · push Not at hx
    have hclosed : IsClosed (⋃ C ∈ (supportComponentsFinset D : Set (Set X)), C) := by
      refine Set.Finite.isClosed_biUnion (supportComponentsFinset D).finite_toSet ?_
      intro C hC
      exact ((hmemiff C).mp (Finset.mem_coe.mp hC)).isClosed
    refine ⟨⟨(⋃ C ∈ (supportComponentsFinset D : Set (Set X)), C)ᶜ, hclosed.isOpen_compl⟩, ?_, ?_⟩
    · intro hmem
      rw [Set.mem_iUnion₂] at hmem
      obtain ⟨C, hC, hxC⟩ := hmem
      exact hx C (Finset.mem_coe.mp hC) hxC
    · intro W hWΩ
      refine ⟨1, one_mem _, ?_⟩
      rw [Ideal.span_singleton_one]
      have hall : ∀ C ∈ (supportComponentsFinset D).toList,
          (componentPowerIdeal I D C).ideal W = 1 := by
        intro C hC
        rw [Ideal.one_eq_top]
        refine ideal_componentPowerIdeal_eq_top_of_disjoint_consolidated260 I D C W ?_
        intro y hy hyC
        have hyS : y ∈ (⋃ C' ∈ (supportComponentsFinset D : Set (Set X)), C') :=
          Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_toList.mp hC)) hyC
        exact absurd hyS (hWΩ hy)
      have hprodtop : (((supportComponentsFinset D).toList.map
          (fun C => componentPowerIdeal I D C)).prod).ideal W = ⊤ := by
        rw [idealSheafData_ideal_listProd_consolidated260, List.map_map, ← Ideal.one_eq_top]
        exact prod_map_eq_one_of_forall_eq_one_consolidated260 (fun C => (componentPowerIdeal I D C).ideal W)
          ((supportComponentsFinset D).toList) hall
      refine le_antisymm le_top ?_
      rw [← hprodtop]
      exact hprodle W

private theorem exists_prod_monomialPartAlongDivisor_eq_span_singleton_consolidated260 (I : X.IdealSheafData) (x : X) :
    ∀ L : List X.IdealSheafData, (∀ D ∈ L, IsEtaleLocallyCoordinateDivisor p D) →
      ∃ Ω : X.Opens, x ∈ Ω ∧ ∀ W : X.affineOpens, (W : X.Opens) ≤ Ω →
        ∃ g ∈ nonZeroDivisors Γ(X, (W : X.Opens)),
          ((L.map (fun D => monomialPartAlongDivisor I D)).prod).ideal W = Ideal.span {g} := by
  intro L
  induction L with
  | nil =>
      intro _
      refine ⟨⊤, trivial, ?_⟩
      intro W _
      refine ⟨1, one_mem _, ?_⟩
      rw [List.map_nil, List.prod_nil, Ideal.span_singleton_one]
      exact idealSheafData_ideal_top_consolidated260 W
  | cons D L ih =>
      intro hmem
      obtain ⟨Ω₁, hxΩ₁, h₁⟩ := exists_nhds_ideal_monomialPartAlongDivisor_eq_span_consolidated260 p I D
        (hmem D (List.mem_cons.mpr (Or.inl rfl))) x
      obtain ⟨Ω₂, hxΩ₂, h₂⟩ := ih (fun D' hD' => hmem D' (List.mem_cons.mpr (Or.inr hD')))
      refine ⟨Ω₁ ⊓ Ω₂, ⟨hxΩ₁, hxΩ₂⟩, ?_⟩
      intro W hW
      obtain ⟨g₁, hg₁, he₁⟩ := h₁ W (le_trans hW inf_le_left)
      obtain ⟨g₂, hg₂, he₂⟩ := h₂ W (le_trans hW inf_le_right)
      refine ⟨g₁ * g₂, mul_mem hg₁ hg₂, ?_⟩
      rw [List.map_cons, List.prod_cons, idealSheafData_ideal_mul_consolidated260, he₁, he₂,
        Ideal.span_singleton_mul_span_singleton]

theorem isLocallyGeneratedByNonZeroDivisor_monomialFactorIdeal (E : List X.IdealSheafData) (I : X.IdealSheafData)
    (hE : InStrictNormalCrossingPosition p E) : Blowup.IsLocallyGeneratedByNonZeroDivisor (monomialFactorIdeal E I) := by
  intro x
  obtain ⟨Ω, hxΩ, hΩ⟩ := exists_prod_monomialPartAlongDivisor_eq_span_singleton_consolidated260 p I x E
    (fun D hD => isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD)
  obtain ⟨U, hxU⟩ := Scheme.exists_affineOpens_mem x
  have hU : IsAffineOpen (U : X.Opens) := U.2
  obtain ⟨f, hfle, hxf⟩ := hU.exists_basicOpen_le (⟨x, hxΩ⟩ : ↥Ω) hxU
  obtain ⟨g, hg, hgeq⟩ := hΩ (X.affineBasicOpen f) hfle
  refine ⟨X.affineBasicOpen f, g, hxf, hg, ?_⟩
  rw [monomialFactorIdeal_eq_prod_monomialPartAlongDivisor]
  exact hgeq


end

private theorem natCast_add_one_le_of_not_le_consolidated260 (n : ℕ) (b : ℕ∞) (h : ¬ b ≤ (n : ℕ∞)) :
    ((n + 1 : ℕ) : ℕ∞) ≤ b := by
  rw [Nat.cast_succ]
  exact ENat.natCast_add_one_le_iff.2 (not_le.mp h)

private theorem prod_map_eq_apply_getElem_of_forall_ne_consolidated260 {α : Type*} {M : Type*} [CommMonoid M] (g : α → M) :
    ∀ (L : List α) (i : ℕ) (hi : i < L.length),
      (∀ (j : ℕ) (hj : j < L.length), j ≠ i → g L[j] = 1) → (L.map g).prod = g L[i] := by
  intro L
  induction L with
  | nil =>
      intro i hi
      exact absurd hi (by simp only [List.length_nil]; omega)
  | cons b L ih =>
      intro i hi hone
      cases i with
      | zero =>
          have h1 : (L.map g).prod = 1 := by
            refine prod_map_eq_one_of_forall_eq_one_consolidated260 g L ?_
            intro y hy
            obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hy
            have h2 := hone (j + 1) (by simp only [List.length_cons]; omega) (by omega)
            rw [← hjy]
            simpa using h2
          show (List.map g (b :: L)).prod = g b
          rw [List.map_cons, List.prod_cons, h1, mul_one]
      | succ i =>
          have hi' : i < L.length := by
            simp only [List.length_cons] at hi
            omega
          have hb : g b = 1 := by
            have h0 := hone 0 (by simp only [List.length_cons]; omega) (by omega)
            simpa using h0
          have hrest : (L.map g).prod = g L[i] := by
            refine ih i hi' ?_
            intro j hj hji
            have h2 := hone (j + 1) (by simp only [List.length_cons]; omega) (by omega)
            simpa using h2
          show (List.map g (b :: L)).prod = g L[i]
          rw [List.map_cons, List.prod_cons, hb, one_mul]
          exact hrest

private theorem not_mem_support_of_stalkIdeal_eq_maximalIdeal_consolidated260 (p : X ⟶ Spec (CommRingCat.of k))
    {V : X.Opens} (hV : IsAffineOpen V) {m : ℕ} (c : EtaleChart p V m)
    {D D' : X.IdealSheafData} {t s : Fin m} (hts : t ≠ s)
    (hDV : restrictIdeal D V = c.coordIdeal {t})
    (hD'V : restrictIdeal D' V = c.coordIdeal {s})
    {x : ↥X} (hx : x ∈ V)
    (hmax : stalkIdeal D x = IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hxD' : x ∈ D'.support) : False := by
  classical
  have hDspan : stalkIdeal D x =
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord t)} : Set (X.presheaf.stalk x)) :=
    stalkIdeal_eq_span_germ_coord p hV c t D hDV x hx
  have hD'span : stalkIdeal D' x =
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord s)} : Set (X.presheaf.stalk x)) :=
    stalkIdeal_eq_span_germ_coord p hV c s D' hD'V x hx
  have hle : stalkIdeal D' x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (mem_support_iff_stalkIdeal_le_maximalIdeal D' x).mp hxD'
  have hmem : (X.presheaf.germ V x hx).hom (c.coord s) ∈ stalkIdeal D x := by
    rw [hmax]
    refine hle ?_
    rw [hD'span]
    exact Ideal.mem_span_singleton_self _
  rw [hDspan, Ideal.mem_span_singleton'] at hmem
  obtain ⟨g, hg⟩ := hmem
  let : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hx).hom.toAlgebra
  have hlocz : IsLocalization (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) := hV.isLocalization_stalk ⟨x, hx⟩
  have halg : (algebraMap Γ(X, V) (X.presheaf.stalk x)) = (X.presheaf.germ V x hx).hom := rfl
  obtain ⟨w, hw⟩ := IsLocalization.surj
    (M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) g
  have hw' : g * (X.presheaf.germ V x hx).hom (w.2 : Γ(X, V))
      = (X.presheaf.germ V x hx).hom w.1 := by
    rw [← halg]
    exact hw
  have heq : (algebraMap Γ(X, V) (X.presheaf.stalk x)) ((w.2 : Γ(X, V)) * c.coord s)
      = (algebraMap Γ(X, V) (X.presheaf.stalk x)) (w.1 * c.coord t) := by
    rw [map_mul, map_mul, halg, ← hg, ← hw']
    ring
  obtain ⟨v, hv⟩ : ∃ v : (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl,
      (v : Γ(X, V)) * ((w.2 : Γ(X, V)) * c.coord s)
        = (v : Γ(X, V)) * (w.1 * c.coord t) :=
    (IsLocalization.eq_iff_exists (M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
      (S := X.presheaf.stalk x)).mp heq
  have hspan : ((v : Γ(X, V)) * (w.2 : Γ(X, V))) ∈ Ideal.span ({c.coord t} : Set Γ(X, V)) := by
    refine mem_span_coord_of_coord_mul_mem hV c hts ((v : Γ(X, V)) * (w.2 : Γ(X, V))) ?_
    have hmul : c.coord s * ((v : Γ(X, V)) * (w.2 : Γ(X, V)))
        = ((v : Γ(X, V)) * w.1) * c.coord t := by linear_combination hv
    rw [hmul]
    exact Ideal.mem_span_singleton'.mpr ⟨(v : Γ(X, V)) * w.1, rfl⟩
  have hunit : IsUnit ((X.presheaf.germ V x hx).hom ((v : Γ(X, V)) * (w.2 : Γ(X, V)))) := by
    rw [← halg, map_mul]
    exact (IsLocalization.map_units (X.presheaf.stalk x) v).mul
      (IsLocalization.map_units (X.presheaf.stalk x) w.2)
  have hfin : (X.presheaf.germ V x hx).hom ((v : Γ(X, V)) * (w.2 : Γ(X, V)))
      ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [← hmax, hDspan]
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hspan
    refine Ideal.mem_span_singleton'.mpr ⟨(X.presheaf.germ V x hx).hom z, ?_⟩
    rw [← map_mul, hz]
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hfin)) hunit

private theorem stalkIdeal_monomialFactorIdeal_genericPoint_consolidated260 [TopologicalSpace.NoetherianSpace ↥X]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (I : X.IdealSheafData)
    (hE : InStrictNormalCrossingPosition p E) {D : X.IdealSheafData} (hD : D ∈ E) {C : Set X}
    (hC : IsIrreducibleComponentOfSupport D C) :
    stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint =
      stalkIdeal D hC.isIrreducible.genericPoint ^ orderAlongComponent I hC.isIrreducible := by
  classical
  obtain ⟨i0, hi0, hi0D⟩ := List.getElem_of_mem hD
  have hloc : IsEtaleLocallyCoordinateDivisor p D := isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD
  obtain ⟨-, hpos⟩ := (inStrictNormalCrossingPosition_iff p E).mp hE
  obtain ⟨U, hηU, m, c, a, hinj, hnone, hsome⟩ :=
    InStrictNormalCrossingPositionAt.exists_etaleChart (hpos hC.isIrreducible.genericPoint)
  have hmaxD : stalkIdeal D hC.isIrreducible.genericPoint
      = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
    stalkIdeal_genericPoint_eq_maximalIdeal p D hloc hC.isIrreducible hC.subset_support hC.maximal
  have hηD : hC.isIrreducible.genericPoint ∈ D.support := hC.genericPoint_mem_support
  obtain ⟨t, hat⟩ : ∃ t : Fin m, a i0 = some t := by
    cases hai : a i0 with
    | none =>
        refine absurd hηD (notMem_support_of_mem_opens_of_restrictIdeal_eq_top D U ?_ _ hηU)
        rw [← hi0D]
        exact hnone i0 hi0 hai
    | some t =>
        refine ⟨t, ?_⟩
        simp
  have hDU : restrictIdeal D U = c.coordIdeal {t} := by
    rw [← hi0D]
    exact hsome i0 hi0 t hat
  have hother : ∀ (j : ℕ) (hj : j < E.length), j ≠ i0 →
      hC.isIrreducible.genericPoint ∉ (E[j].support : Set ↥X) := by
    intro j hj hji0 hmem
    cases haj : a j with
    | none =>
        exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top E[j] U (hnone j hj haj) _ hηU hmem
    | some s =>
        have hts : t ≠ s := by
          intro h
          exact hji0 (hinj j hj i0 hi0 t (by rw [haj, h]) hat)
        have hmem' : hC.isIrreducible.genericPoint ∈ E[j].support := hmem
        have hxtop : hC.isIrreducible.genericPoint ∈ (⨆ W : X.affineOpens, (W : X.Opens)) := by
          rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
          trivial
        obtain ⟨W, hηW⟩ := TopologicalSpace.Opens.mem_iSup.mp hxtop
        obtain ⟨f, hfU, hηf⟩ :=
          W.2.exists_basicOpen_le (⟨hC.isIrreducible.genericPoint, hηU⟩ : ↥U) hηW
        have hηf' : hC.isIrreducible.genericPoint ∈ X.basicOpen f := hηf
        have hVaff : IsAffineOpen (X.basicOpen f) := W.2.basicOpen f
        exact not_mem_support_of_stalkIdeal_eq_maximalIdeal_consolidated260 p hVaff (c.restrict hfU) hts
          (restrictIdeal_eq_restrict_coordIdeal_of_le hfU c D {t} hDU)
          (restrictIdeal_eq_restrict_coordIdeal_of_le hfU c E[j] {s} (hsome j hj s haj))
          hηf' hmaxD hmem'
  have hprod : (E.map (fun D' => stalkIdeal (monomialPartAlongDivisor I D') hC.isIrreducible.genericPoint)).prod
      = stalkIdeal (monomialPartAlongDivisor I E[i0]) hC.isIrreducible.genericPoint := by
    refine prod_map_eq_apply_getElem_of_forall_ne_consolidated260
      (fun D' => stalkIdeal (monomialPartAlongDivisor I D') hC.isIrreducible.genericPoint) E i0 hi0 ?_
    intro j hj hji0
    show stalkIdeal (monomialPartAlongDivisor I E[j]) hC.isIrreducible.genericPoint = 1
    have h1 : stalkIdeal (monomialPartAlongDivisor I E[j]) hC.isIrreducible.genericPoint = ⊤ :=
      stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I E[j] (hother j hj hji0)
    rw [h1, Ideal.one_eq_top]
  rw [stalkIdeal_monomialFactorIdeal, hprod, hi0D,
    stalkIdeal_monomialPartAlongDivisor_of_mem p I hloc hC hC.genericPoint_mem]

theorem orderAt_monomialFactorIdeal_genericPoint [TopologicalSpace.NoetherianSpace ↥X]
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (E : List X.IdealSheafData) (I : X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (hI : NonzeroOnComponents I) {D : X.IdealSheafData} (hD : D ∈ E) {C : Set X}
    (hC : IsIrreducibleComponentOfSupport D C) :
    orderAt (monomialFactorIdeal E I) hC.isIrreducible.genericPoint =
      (orderAlongComponent I hC.isIrreducible : ℕ∞) := by
  classical
  have hloc : IsEtaleLocallyCoordinateDivisor p D := isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD
  have hmaxD : stalkIdeal D hC.isIrreducible.genericPoint
      = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
    stalkIdeal_genericPoint_eq_maximalIdeal p D hloc hC.isIrreducible hC.subset_support hC.maximal
  have hstalk : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
      = stalkIdeal D hC.isIrreducible.genericPoint ^ orderAlongComponent I hC.isIrreducible :=
    stalkIdeal_monomialFactorIdeal_genericPoint_consolidated260 p E I hE hD hC
  have hmono : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
      = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint)
        ^ orderAlongComponent I hC.isIrreducible := by
    rw [hstalk, hmaxD]
  have hordI : orderAt I hC.isIrreducible.genericPoint
      = ((orderAlongComponent I hC.isIrreducible : ℕ) : ℕ∞) :=
    (coe_orderAlongComponent_eq_orderAt_genericPoint hC hI).symm
  have h3 : stalkIdeal I hC.isIrreducible.genericPoint
      ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint)
        ^ orderAlongComponent I hC.isIrreducible := by
    rw [← hmaxD]
    exact stalkIdeal_le_pow_of_le_orderAt_genericPoint p D hloc hC.isIrreducible
      hC.subset_support hC.maximal I (orderAlongComponent I hC.isIrreducible)
      (le_of_eq hordI.symm) hC.isIrreducible.genericPoint hC.genericPoint_mem
  refine le_antisymm ?_ ((le_orderAt_iff _ _ _).mpr (le_of_eq hmono))
  by_contra hcon
  have h2 : ((orderAlongComponent I hC.isIrreducible + 1 : ℕ) : ℕ∞)
      ≤ orderAt (monomialFactorIdeal E I) hC.isIrreducible.genericPoint :=
    natCast_add_one_le_of_not_le_consolidated260 (orderAlongComponent I hC.isIrreducible) _ hcon
  rw [le_orderAt_iff, hmono] at h2
  exact not_stalkIdeal_le_pow_succ_genericPoint p D hloc hC.isIrreducible hC.subset_support
    hC.maximal I (orderAlongComponent I hC.isIrreducible) hordI
    (by rw [hmaxD]; exact le_trans h3 h2)

def nonMonomialFactorIdeal [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    (E : List X.IdealSheafData) (I : X.IdealSheafData) : X.IdealSheafData :=
  idealSheafColon I (monomialFactorIdeal E I)

theorem nonMonomialFactorIdeal_eq_idealSheafColon [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    (E : List X.IdealSheafData) (I : X.IdealSheafData) :
    nonMonomialFactorIdeal E I = idealSheafColon I (monomialFactorIdeal E I) := rfl

private theorem mem_prod_map_of_forall_mem_span_consolidated260 {R : Type*} [CommRing R] {α : Type*}
    (F : α → Ideal R) :
    ∀ (L : List α) (g : ℕ → R),
      (∀ (i : ℕ) (h : i < L.length), F L[i] = Ideal.span ({g i} : Set R)) →
      (∀ (i : ℕ), i < L.length → ∀ (j : ℕ), j < L.length → i ≠ j →
        ∀ (n : ℕ) (w : R), g j * w ∈ Ideal.span ({g i ^ n} : Set R) →
          w ∈ Ideal.span ({g i ^ n} : Set R)) →
      ∀ z : R, (∀ (i : ℕ), i < L.length → z ∈ Ideal.span ({g i} : Set R)) →
        z ∈ (L.map F).prod := by
  intro L
  induction L with
  | nil =>
      intro g _ _ z _
      rw [List.map_nil, List.prod_nil, Ideal.one_eq_top]
      exact Submodule.mem_top
  | cons b L ih =>
      intro g hF hcan z hz
      have hb0 : F b = Ideal.span ({g 0} : Set R) := by
        have h := hF 0 (by simp only [List.length_cons]; omega)
        simpa using h
      have hz0 : z ∈ Ideal.span ({g 0} : Set R) :=
        hz 0 (by simp only [List.length_cons]; omega)
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hz0
      have hzy : z = g 0 * y := by rw [← hy]; ring
      have hyprod : y ∈ (L.map F).prod := by
        refine ih (fun i => g (i + 1)) ?_ ?_ y ?_
        · intro i h
          have h2 := hF (i + 1) (by simp only [List.length_cons]; omega)
          simpa using h2
        · intro i hi j hj hij n w hw
          exact hcan (i + 1) (by simp only [List.length_cons]; omega) (j + 1)
            (by simp only [List.length_cons]; omega) (by omega) n w hw
        · intro i h
          have hzi : z ∈ Ideal.span ({g (i + 1)} : Set R) :=
            hz (i + 1) (by simp only [List.length_cons]; omega)
          have hzi' : g 0 * y ∈ Ideal.span ({g (i + 1) ^ 1} : Set R) := by
            rw [pow_one, ← hzy]
            exact hzi
          have h3 := hcan (i + 1) (by simp only [List.length_cons]; omega) 0
            (by simp only [List.length_cons]; omega) (by omega) 1 y hzi'
          rwa [pow_one] at h3
      have hg0 : g 0 ∈ F b := by
        rw [hb0]
        exact Ideal.mem_span_singleton_self _
      rw [List.map_cons, List.prod_cons, hzy]
      exact Ideal.mul_mem_mul hg0 hyprod

private theorem mem_span_algebraMap_of_mul_mem_consolidated260 {S : Type*} [CommRing S] {q : Submonoid S}
    {A : Type*} [CommRing A] [Algebra S A] [IsLocalization q A] (b d : S)
    (hcan : ∀ w : S, b * w ∈ Ideal.span ({d} : Set S) → w ∈ Ideal.span ({d} : Set S))
    (z : A) (hz : algebraMap S A b * z ∈ Ideal.span ({algebraMap S A d} : Set A)) :
    z ∈ Ideal.span ({algebraMap S A d} : Set A) := by
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hz
  obtain ⟨⟨z₀, w₁⟩, hz₁⟩ := IsLocalization.surj (M := q) (S := A) z
  obtain ⟨⟨u₀, w₂⟩, hu₁⟩ := IsLocalization.surj (M := q) (S := A) u
  have key : algebraMap S A (b * z₀ * (w₂ : S)) = algebraMap S A (d * u₀ * (w₁ : S)) := by
    simp only [map_mul]
    linear_combination (-(algebraMap S A b) * algebraMap S A (w₂ : S)) * hz₁ +
      (algebraMap S A d * algebraMap S A (w₁ : S)) * hu₁ +
      (-(algebraMap S A (w₁ : S)) * algebraMap S A (w₂ : S)) * hu
  obtain ⟨cc, hcc⟩ := (IsLocalization.eq_iff_exists (M := q) (S := A)).mp key
  have hmem : b * (z₀ * (w₂ : S) * (cc : S)) ∈ Ideal.span ({d} : Set S) :=
    Ideal.mem_span_singleton'.mpr ⟨u₀ * (w₁ : S) * (cc : S), by linear_combination -hcc⟩
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp (hcan _ hmem)
  have hstep : z * algebraMap S A ((w₁ : S) * (w₂ : S) * (cc : S)) ∈
      Ideal.span ({algebraMap S A d} : Set A) := by
    refine Ideal.mem_span_singleton'.mpr ⟨algebraMap S A v, ?_⟩
    have h6 : algebraMap S A (z₀ * (w₂ : S) * (cc : S)) = algebraMap S A (v * d) := by rw [hv]
    simp only [map_mul] at h6 ⊢
    linear_combination -h6 - (algebraMap S A (w₂ : S) * algebraMap S A (cc : S)) * hz₁
  have hunit : IsUnit (algebraMap S A ((w₁ : S) * (w₂ : S) * (cc : S))) := by
    have h1 := IsLocalization.map_units (M := q) (S := A) w₁
    have h2 := IsLocalization.map_units (M := q) (S := A) w₂
    have h3 := IsLocalization.map_units (M := q) (S := A) cc
    rw [map_mul, map_mul]
    exact (h1.mul h2).mul h3
  obtain ⟨eu, heu⟩ := hunit
  have h7 := (Ideal.span ({algebraMap S A d} : Set A)).mul_mem_right ((eu⁻¹ : Aˣ) : A) hstep
  rw [mul_assoc, ← heu, Units.mul_inv, mul_one] at h7
  exact h7

private theorem mem_span_germ_coord_pow_of_mul_mem_consolidated260 (p : X ⟶ Spec (CommRingCat.of k))
    {V : X.Opens} (hV : IsAffineOpen V) {m : ℕ} (c : EtaleChart p V m) {x : X} (hx : x ∈ V)
    {i j : Fin m} (hij : i ≠ j) (N : ℕ) (z : X.presheaf.stalk x)
    (hz : (X.presheaf.germ V x hx).hom (c.coord j) * z ∈
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord i) ^ N} : Set (X.presheaf.stalk x))) :
    z ∈ Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord i) ^ N} :
      Set (X.presheaf.stalk x)) := by
  let : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hx).hom.toAlgebra
  have : IsLocalization (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x) :=
    hV.isLocalization_stalk ⟨x, hx⟩
  have hmap : ∀ y : Γ(X, V), algebraMap Γ(X, V) (X.presheaf.stalk x) y =
      (X.presheaf.germ V x hx).hom y := fun _ => rfl
  have hpow : algebraMap Γ(X, V) (X.presheaf.stalk x) (c.coord i ^ N) =
      (X.presheaf.germ V x hx).hom (c.coord i) ^ N := by
    rw [map_pow, hmap]
  have hmain := mem_span_algebraMap_of_mul_mem_consolidated260
    (q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) (c.coord j) (c.coord i ^ N)
    (fun w hw => mem_span_coord_pow_of_mul_mem hV c hij N w hw) z
    (by rw [hpow, hmap]; exact hz)
  rwa [hpow] at hmain

theorem monomialFactorIdeal_mul_nonMonomialFactorIdeal [TopologicalSpace.NoetherianSpace ↥X]
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (E : List X.IdealSheafData) (I : X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) :
    monomialFactorIdeal E I * nonMonomialFactorIdeal E I = I := by
  have hM : Blowup.IsLocallyGeneratedByNonZeroDivisor (monomialFactorIdeal E I) :=
    isLocallyGeneratedByNonZeroDivisor_monomialFactorIdeal p E I hE
  have hIM : I ≤ monomialFactorIdeal E I := by
    rw [le_iff_forall_stalkIdeal_le]
    intro x
    obtain ⟨-, hposall⟩ := (inStrictNormalCrossingPosition_iff p E).mp hE
    obtain ⟨U, hxU, m, c, aa, hinj, hnone, hsome⟩ := InStrictNormalCrossingPositionAt.exists_etaleChart (hposall x)
    obtain ⟨V, hVaff, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
    have hdata : ∀ i : ℕ, ∃ ee : X.presheaf.stalk x, ∀ h : i < E.length,
        stalkIdeal (monomialPartAlongDivisor I (E[i]'h)) x = Ideal.span ({ee} : Set (X.presheaf.stalk x)) ∧
        stalkIdeal I x ≤ Ideal.span ({ee} : Set (X.presheaf.stalk x)) ∧
        (ee = 1 ∨ ∃ (t : Fin m) (bb : ℕ), aa i = some t ∧
          ee = (X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t) ^ bb) := by
      intro i
      by_cases hi : i < E.length
      · by_cases hxs : x ∈ (((E[i]'hi)).support : Set ↥X)
        · have hDloc : IsEtaleLocallyCoordinateDivisor p (E[i]'hi) :=
            isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE (E[i]'hi) (List.getElem_mem hi)
          obtain ⟨C, hC, hxC⟩ := exists_isIrreducibleComponentOfSupport (E[i]'hi) x hxs
          have hopt : ∃ t : Fin m, aa i = some t := by
            by_contra hcon
            push Not at hcon
            have hnone' : aa i = none := by
              cases hca : aa i with
              | none => rfl
              | some t => exact absurd hca (hcon t)
            exact absurd hxs (notMem_support_of_mem_opens_of_restrictIdeal_eq_top (E[i]'hi) U
              (hnone i hi hnone') x hxU)
          obtain ⟨t, haa⟩ := hopt
          have hDU : restrictIdeal (E[i]'hi) U = c.coordIdeal {t} := hsome i hi t haa
          have hDV : restrictIdeal (E[i]'hi) V = (c.restrict hVU).coordIdeal {t} :=
            restrictIdeal_eq_restrict_coordIdeal_of_le hVU c (E[i]'hi) {t} hDU
          have hst : stalkIdeal (E[i]'hi) x =
              Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t)} :
                Set (X.presheaf.stalk x)) :=
            stalkIdeal_eq_span_germ_coord p hVaff (c.restrict hVU) t (E[i]'hi) hDV x hxV
          have hA : stalkIdeal (monomialPartAlongDivisor I (E[i]'hi)) x =
              Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t) ^
                orderAlongComponent I hC.isIrreducible} : Set (X.presheaf.stalk x)) := by
            rw [stalkIdeal_monomialPartAlongDivisor_of_mem p I hDloc hC hxC, hst, Ideal.span_singleton_pow]
          have hB : stalkIdeal I x ≤
              Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t) ^
                orderAlongComponent I hC.isIrreducible} : Set (X.presheaf.stalk x)) := by
            have hn : ((orderAlongComponent I hC.isIrreducible : ℕ) : ℕ∞) ≤
                orderAt I hC.isIrreducible.genericPoint := by
              rw [orderAlongComponent_eq_orderAt_genericPoint]
              exact ENat.natCast_toNat_le_self _
            have hle := stalkIdeal_le_pow_of_le_orderAt_genericPoint p (E[i]'hi) hDloc
              hC.isIrreducible hC.subset_support hC.maximal I
              (orderAlongComponent I hC.isIrreducible) hn x hxC
            rwa [hst, Ideal.span_singleton_pow] at hle
          exact ⟨(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t) ^
            orderAlongComponent I hC.isIrreducible,
            fun _ => ⟨hA, hB, Or.inr ⟨t, orderAlongComponent I hC.isIrreducible, haa, rfl⟩⟩⟩
        · have hA : stalkIdeal (monomialPartAlongDivisor I (E[i]'hi)) x =
              Ideal.span ({1} : Set (X.presheaf.stalk x)) := by
            rw [stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I (E[i]'hi) hxs,
              Ideal.span_singleton_one]
          have hB : stalkIdeal I x ≤ Ideal.span ({1} : Set (X.presheaf.stalk x)) := by
            rw [Ideal.span_singleton_one]
            exact le_top
          exact ⟨1, fun _ => ⟨hA, hB, Or.inl rfl⟩⟩
      · exact ⟨1, fun h => absurd h hi⟩
    choose ee hee using hdata
    have hcan : ∀ (i : ℕ), i < E.length → ∀ (j : ℕ), j < E.length → i ≠ j →
        ∀ (n : ℕ) (w : X.presheaf.stalk x),
          ee j * w ∈ Ideal.span ({ee i ^ n} : Set (X.presheaf.stalk x)) →
            w ∈ Ideal.span ({ee i ^ n} : Set (X.presheaf.stalk x)) := by
      intro i hi j hj hij n w hw
      rcases (hee i hi).2.2 with hi1 | ⟨ti, bi, hai, hei⟩
      · rw [hi1, one_pow, Ideal.span_singleton_one]
        exact Submodule.mem_top
      · rcases (hee j hj).2.2 with hj1 | ⟨tj, bj, haj, hej⟩
        · rw [hj1, one_mul] at hw
          exact hw
        · have htne : ti ≠ tj := by
            intro htt
            refine hij ?_
            have haj' : aa j = some ti := by rw [htt]; exact haj
            exact hinj i hi j hj ti hai haj'
          have hsingle : ∀ (N : ℕ) (zz : X.presheaf.stalk x),
              (X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord tj) * zz ∈
                Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord ti) ^ N} :
                  Set (X.presheaf.stalk x)) →
              zz ∈ Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord ti) ^ N} :
                  Set (X.presheaf.stalk x)) :=
            fun N zz hzz =>
              mem_span_germ_coord_pow_of_mul_mem_consolidated260 p hVaff (c.restrict hVU) hxV htne N zz hzz
          rw [hei, hej] at hw
          rw [hei]
          rw [← pow_mul] at hw ⊢
          exact mem_span_of_pow_mul_mem_span_consolidated260 _ _ hsingle (bi * n) bj w hw
    rw [stalkIdeal_monomialFactorIdeal]
    intro z hz
    refine mem_prod_map_of_forall_mem_span_consolidated260 (fun D => stalkIdeal (monomialPartAlongDivisor I D) x) E ee ?_
      hcan z ?_
    · intro i h
      exact (hee i h).1
    · intro i h
      exact (hee i h).2.1 hz
  rw [nonMonomialFactorIdeal_eq_idealSheafColon]
  exact hM.mul_idealSheafColon hIM

private theorem exists_affineOpens_ideal_comap_ι_eq_map_consolidated260 (Ω : X.Opens)
    (V : Ω.toScheme.affineOpens) :
    ∃ (W : X.affineOpens) (e : (V : Ω.toScheme.Opens) ≤
        (TopologicalSpace.Opens.map Ω.ι.base).obj (W : X.Opens)),
      (W : X.Opens) ≤ Ω ∧ ∀ A : X.IdealSheafData,
        (A.comap Ω.ι).ideal V
          = Ideal.map (Ω.ι.appLE (W : X.Opens) (V : Ω.toScheme.Opens) e).hom (A.ideal W) := by
  have haff : IsAffineOpen (Ω.ι ''ᵁ (V : Ω.toScheme.Opens)) :=
    V.2.image_of_isOpenImmersion Ω.ι
  have he : (V : Ω.toScheme.Opens) ≤
      (TopologicalSpace.Opens.map Ω.ι.base).obj (Ω.ι ''ᵁ (V : Ω.toScheme.Opens)) := by
    intro y hy
    exact ⟨y, hy, rfl⟩
  have hle : (Ω.ι ''ᵁ (V : Ω.toScheme.Opens)) ≤ Ω := by
    rintro z ⟨y, -, rfl⟩
    exact y.2
  exact ⟨⟨_, haff⟩, he, hle, fun A =>
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE A Ω.ι ⟨_, haff⟩ V he⟩

private theorem comap_ι_eq_of_forall_affineOpens_ideal_eq_consolidated260 (A B : X.IdealSheafData) (Ω : X.Opens)
    (h : ∀ W : X.affineOpens, (W : X.Opens) ≤ Ω → A.ideal W = B.ideal W) :
    A.comap Ω.ι = B.comap Ω.ι := by
  refine le_antisymm ?_ ?_
  · intro V
    obtain ⟨W, e, hW, hform⟩ := exists_affineOpens_ideal_comap_ι_eq_map_consolidated260 Ω V
    rw [hform A, hform B, h W hW]
  · intro V
    obtain ⟨W, e, hW, hform⟩ := exists_affineOpens_ideal_comap_ι_eq_map_consolidated260 Ω V
    rw [hform A, hform B, h W hW]

section
variable (Ω : X.Opens)

private theorem idealSheafData_comap_one_consolidated260 :
    (1 : X.IdealSheafData).comap Ω.ι = 1 := by
  rw [Scheme.IdealSheafData.one_eq_top]
  exact Scheme.IdealSheafData.comap_top _

private theorem idealSheafData_comap_prod_consolidated260 :
    ∀ (n : ℕ) (J : Fin n → X.IdealSheafData),
      (∏ i, J i).comap Ω.ι = ∏ i, (J i).comap Ω.ι := by
  intro n
  induction n with
  | zero =>
      intro J
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      exact idealSheafData_comap_one_consolidated260 Ω
  | succ n ih =>
      intro J
      rw [Fin.prod_univ_succ, Scheme.IdealSheafData.comap_mul, ih (fun i => J i.succ),
        Fin.prod_univ_succ]


end

section
variable [TopologicalSpace.NoetherianSpace ↥X] (p : X ⟶ Spec (CommRingCat.of k))

private theorem exists_nhds_ideal_monomialPartAlongDivisor_eq_pow_consolidated260 (I D : X.IdealSheafData)
    (hD : IsEtaleLocallyCoordinateDivisor p D) (x : X) :
    ∃ Ω : X.Opens, x ∈ Ω ∧ ∃ a : ℕ, ∀ W : X.affineOpens, (W : X.Opens) ≤ Ω →
      (monomialPartAlongDivisor I D).ideal W = (D ^ a).ideal W := by
  classical
  have hmemiff : ∀ C' : Set X, C' ∈ supportComponentsFinset D ↔ IsIrreducibleComponentOfSupport D C' := by
    intro C'
    simp only [supportComponentsFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hprodle : ∀ W : X.affineOpens,
      (((supportComponentsFinset D).toList.map (fun C => componentPowerIdeal I D C)).prod).ideal W
        ≤ (monomialPartAlongDivisor I D).ideal W := by
    intro W
    have hle : ((supportComponentsFinset D).toList.map (fun C => componentPowerIdeal I D C)).prod
        ≤ monomialPartAlongDivisor I D := by
      rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
      refine Finset.le_inf ?_
      intro C' hC'
      exact idealSheafData_listProd_le_of_mem_consolidated260 _ (componentPowerIdeal I D C')
        (List.mem_map.mpr ⟨C', Finset.mem_toList.mpr hC', rfl⟩)
    exact hle W
  by_cases hx : ∃ C ∈ supportComponentsFinset D, x ∈ C
  · obtain ⟨C₀, hC₀mem, hxC₀⟩ := hx
    have hC₀ : IsIrreducibleComponentOfSupport D C₀ := (hmemiff C₀).mp hC₀mem
    obtain ⟨V, hV, hxV, n, c, j, hDV, hVsupp, -, hagree, -⟩ :=
      hC₀.exists_affineOpen_etaleChart_coordIdeal p hD x hxC₀
    refine ⟨V, hxV, orderAlongComponent I hC₀.isIrreducible, ?_⟩
    intro W hWV
    have hres : restrictIdeal D (W : X.Opens) = (c.restrict hWV).coordIdeal {j} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hWV c D {j} hDV
    have hDW : D.ideal W = Ideal.span {(c.restrict hWV).coord j} := by
      have h1 := EtaleChart.ideal_eq_span_coord (c.restrict hWV) W.2 D {j} hres
      simpa using h1
    have hcomp0 : (componentPowerIdeal I D C₀).ideal W
        = Ideal.span {(c.restrict hWV).coord j ^ orderAlongComponent I hC₀.isIrreducible} := by
      rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC₀, idealSheafData_ideal_pow_consolidated260,
        hagree W hWV, hDW, Ideal.span_singleton_pow]
    have hDpow : (D ^ orderAlongComponent I hC₀.isIrreducible).ideal W
        = Ideal.span {(c.restrict hWV).coord j ^ orderAlongComponent I hC₀.isIrreducible} := by
      rw [idealSheafData_ideal_pow_consolidated260, hDW, Ideal.span_singleton_pow]
    have hother : ∀ C : Set X, C ∈ (supportComponentsFinset D).toList → C ≠ C₀ →
        (componentPowerIdeal I D C).ideal W = ⊤ := by
      intro C hCmem hne
      have hCcomp : IsIrreducibleComponentOfSupport D C := (hmemiff C).mp (Finset.mem_toList.mp hCmem)
      refine ideal_componentPowerIdeal_eq_top_of_disjoint_consolidated260 I D C W ?_
      intro y hy hyC
      have hyV : y ∈ V := hWV hy
      have hyD : y ∈ (D.support : Set X) := hCcomp.subset_support hyC
      have hyC₀ : y ∈ C₀ := hVsupp y hyV hyD
      have hdisj : Disjoint C C₀ := hCcomp.disjoint hC₀ p hD hne
      exact (Set.disjoint_left.mp hdisj hyC) hyC₀
    have hprodideal : (((supportComponentsFinset D).toList.map
        (fun C => componentPowerIdeal I D C)).prod).ideal W = (componentPowerIdeal I D C₀).ideal W := by
      rw [idealSheafData_ideal_listProd_consolidated260, List.map_map]
      refine prod_map_eq_apply_of_nodup_of_forall_ne_consolidated260 (fun C => (componentPowerIdeal I D C).ideal W)
        ((supportComponentsFinset D).toList) C₀ (Finset.nodup_toList _)
        (Finset.mem_toList.mpr hC₀mem) ?_
      intro C' hC' hne
      show (componentPowerIdeal I D C').ideal W = 1
      rw [Ideal.one_eq_top]
      exact hother C' hC' hne
    rw [hDpow, ← hcomp0]
    refine le_antisymm ?_ ?_
    · have hle : monomialPartAlongDivisor I D ≤ componentPowerIdeal I D C₀ := by
        rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
        exact Finset.inf_le hC₀mem
      exact hle W
    · rw [← hprodideal]
      exact hprodle W
  · push Not at hx
    have hclosed : IsClosed (⋃ C ∈ (supportComponentsFinset D : Set (Set X)), C) := by
      refine Set.Finite.isClosed_biUnion (supportComponentsFinset D).finite_toSet ?_
      intro C hC
      exact ((hmemiff C).mp (Finset.mem_coe.mp hC)).isClosed
    refine ⟨⟨(⋃ C ∈ (supportComponentsFinset D : Set (Set X)), C)ᶜ, hclosed.isOpen_compl⟩,
      ?_, 0, ?_⟩
    · intro hmem
      rw [Set.mem_iUnion₂] at hmem
      obtain ⟨C, hC, hxC⟩ := hmem
      exact hx C (Finset.mem_coe.mp hC) hxC
    · intro W hWΩ
      rw [pow_zero, idealSheafData_ideal_one_consolidated260, Ideal.one_eq_top]
      have hall : ∀ C ∈ (supportComponentsFinset D).toList,
          (componentPowerIdeal I D C).ideal W = 1 := by
        intro C hC
        rw [Ideal.one_eq_top]
        refine ideal_componentPowerIdeal_eq_top_of_disjoint_consolidated260 I D C W ?_
        intro y hy hyC
        have hyS : y ∈ (⋃ C' ∈ (supportComponentsFinset D : Set (Set X)), C') :=
          Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_toList.mp hC)) hyC
        exact absurd hyS (hWΩ hy)
      have hprodtop : (((supportComponentsFinset D).toList.map
          (fun C => componentPowerIdeal I D C)).prod).ideal W = ⊤ := by
        rw [idealSheafData_ideal_listProd_consolidated260, List.map_map, ← Ideal.one_eq_top]
        exact prod_map_eq_one_of_forall_eq_one_consolidated260 (fun C => (componentPowerIdeal I D C).ideal W)
          ((supportComponentsFinset D).toList) hall
      refine le_antisymm le_top ?_
      rw [← hprodtop]
      exact hprodle W

private theorem exists_prod_monomialPartAlongDivisor_eq_prod_pow_consolidated260
    (I : X.IdealSheafData) (x : X) :
    ∀ (n : ℕ) (g : Fin n → X.IdealSheafData), (∀ i, IsEtaleLocallyCoordinateDivisor p (g i)) →
      ∃ Ω : X.Opens, x ∈ Ω ∧ ∃ a : Fin n → ℕ, ∀ W : X.affineOpens, (W : X.Opens) ≤ Ω →
        ((List.ofFn fun i => monomialPartAlongDivisor I (g i)).prod).ideal W = (∏ i, g i ^ a i).ideal W := by
  intro n
  induction n with
  | zero =>
      intro g _
      refine ⟨⊤, trivial, Fin.elim0, ?_⟩
      intro W _
      simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.prod_empty]
  | succ n ih =>
      intro g hg
      obtain ⟨Ω₁, hxΩ₁, a₀, h₁⟩ := exists_nhds_ideal_monomialPartAlongDivisor_eq_pow_consolidated260 p I (g 0) (hg 0) x
      obtain ⟨Ω₂, hxΩ₂, a', h₂⟩ := ih (fun i => g i.succ) (fun i => hg i.succ)
      refine ⟨Ω₁ ⊓ Ω₂, ⟨hxΩ₁, hxΩ₂⟩, Fin.cons a₀ a', ?_⟩
      intro W hW
      have e1 := h₁ W (le_trans hW inf_le_left)
      have e2 := h₂ W (le_trans hW inf_le_right)
      simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
      rw [idealSheafData_ideal_mul_consolidated260, idealSheafData_ideal_mul_consolidated260, e1, e2]
      simp only [Fin.cons_zero, Fin.cons_succ]


end

theorem exists_isMonomialSplitting [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    [CharZero k] (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    [LocallyOfFiniteType p] [QuasiCompact p] (E : List X.IdealSheafData)
    (hE : InStrictNormalCrossingPosition p E) (I : X.IdealSheafData) (hI : NonzeroOnComponents I) :
    ∃ M N : X.IdealSheafData, IsMonomialSplitting E I M N := by
  classical
  have hetaleCoord : ∀ i : Fin E.length, IsEtaleLocallyCoordinateDivisor p (E.get i) := by
    intro i
    refine isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE _ ?_
    simp
  refine ⟨monomialFactorIdeal E I, nonMonomialFactorIdeal E I, ?_, ?_, ?_, ?_⟩
  · exact (monomialFactorIdeal_mul_nonMonomialFactorIdeal p E I hE).symm
  · intro z hz
    by_contra hcon
    have hnot : ∀ D ∈ E, z ∉ (D.support : Set X) := by
      intro D hD hmem
      refine hcon ?_
      rw [Set.mem_iUnion₂]
      exact ⟨D, hD, hmem⟩
    have htop : stalkIdeal (monomialFactorIdeal E I) z = ⊤ := by
      rw [stalkIdeal_monomialFactorIdeal, ← Ideal.one_eq_top]
      refine prod_map_eq_one_of_forall_eq_one_consolidated260 (fun D => stalkIdeal (monomialPartAlongDivisor I D) z) E ?_
      intro D hD
      rw [stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I D (hnot D hD), Ideal.one_eq_top]
    have hz' : z ∈ (monomialFactorIdeal E I).support := hz
    exact (mem_support_iff_stalkIdeal_ne_top (monomialFactorIdeal E I) z).mp hz' htop
  · intro x
    obtain ⟨Ω, hxΩ, a, ha⟩ :=
      exists_prod_monomialPartAlongDivisor_eq_prod_pow_consolidated260 p I x E.length E.get hetaleCoord
    refine ⟨Ω, hxΩ, a, ?_⟩
    have hlist : (List.ofFn fun i : Fin E.length => monomialPartAlongDivisor I (E.get i))
        = E.map fun D => monomialPartAlongDivisor I D := by
      refine List.ext_getElem (by simp) ?_
      intro i h1 h2
      simp
    have hcongr : (monomialFactorIdeal E I).comap Ω.ι
        = (∏ i : Fin E.length, E.get i ^ a i).comap Ω.ι := by
      refine comap_ι_eq_of_forall_affineOpens_ideal_eq_consolidated260 _ _ Ω ?_
      intro W hW
      have hW' := ha W hW
      rw [hlist] at hW'
      rw [monomialFactorIdeal_eq_prod_monomialPartAlongDivisor]
      exact hW'
    rw [hcongr, idealSheafData_comap_prod_consolidated260 Ω E.length (fun i => E.get i ^ a i)]
    exact Finset.prod_congr rfl
      (fun i _ => Scheme.IdealSheafData.comap_pow (E.get i) Ω.ι (a i))
  · intro D hD C hCirr hCsub hCmax hCN
    have hC : IsIrreducibleComponentOfSupport D C :=
      { isIrreducible := hCirr
        maximal := fun C' h1 h2 h3 => Set.Subset.antisymm (hCmax C' h1 h3 h2) h2
        subset_support := hCsub }
    have hloc : IsEtaleLocallyCoordinateDivisor p D := isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD
    have hmaxD : stalkIdeal D hC.isIrreducible.genericPoint
        = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
      stalkIdeal_genericPoint_eq_maximalIdeal p D hloc hC.isIrreducible hC.subset_support
        hC.maximal
    have hstalkM : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
        = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint)
          ^ orderAlongComponent I hC.isIrreducible := by
      rw [stalkIdeal_monomialFactorIdeal_genericPoint_consolidated260 p E I hE hD hC, hmaxD]
    have hN : stalkIdeal (nonMonomialFactorIdeal E I) hC.isIrreducible.genericPoint
        ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
      (mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp (hCN hC.genericPoint_mem)
    have hIeq : stalkIdeal I hC.isIrreducible.genericPoint
        = stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
          * stalkIdeal (nonMonomialFactorIdeal E I) hC.isIrreducible.genericPoint := by
      rw [← stalkIdeal_mul, monomialFactorIdeal_mul_nonMonomialFactorIdeal p E I hE]
    have hle : stalkIdeal I hC.isIrreducible.genericPoint
        ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint)
          ^ (orderAlongComponent I hC.isIrreducible + 1) := by
      rw [hIeq, hstalkM, pow_succ]
      exact Ideal.mul_mono le_rfl hN
    have h2 : ((orderAlongComponent I hC.isIrreducible + 1 : ℕ) : ℕ∞)
        ≤ orderAt I hC.isIrreducible.genericPoint :=
      (le_orderAt_iff I _ _).mpr hle
    rw [← coe_orderAlongComponent_eq_orderAt_genericPoint hC hI] at h2
    have h3 : orderAlongComponent I hC.isIrreducible + 1
        ≤ orderAlongComponent I hC.isIrreducible := by exact_mod_cast h2
    omega


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplittingFlatPullback
section



variable {X Y : Scheme.{u}}

private theorem comap_finset_prod_consolidated261 {ι : Type*} (s : Finset ι) (F : ι → X.IdealSheafData)
    (h : Y ⟶ X) : (∏ i ∈ s, F i).comap h = ∏ i ∈ s, (F i).comap h := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.prod_cons, Scheme.IdealSheafData.comap_mul, ih]

section
variable (h : Y ⟶ X)

theorem comap_comap_ι (J : X.IdealSheafData) (U : X.Opens) :
    (J.comap h).comap (h ⁻¹ᵁ U).ι = (J.comap U.ι).comap (h ∣_ U) := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι]

theorem support_comap_subset_biUnion (E : List X.IdealSheafData)
    (M : X.IdealSheafData) (hM : (M.support : Set X) ⊆ ⋃ D ∈ E, (D.support : Set X)) :
    ((M.comap h).support : Set Y) ⊆
      ⋃ D ∈ E.map (fun D : X.IdealSheafData => D.comap h), (D.support : Set Y) := by
  intro y hy
  have hy' : h.base y ∈ (M.support : Set X) := Scheme.IdealSheafData.mem_support_comap.mp hy
  obtain ⟨D, hD, hyD⟩ := Set.mem_iUnion₂.mp (hM hy')
  refine Set.mem_iUnion₂.mpr ⟨D.comap h, List.mem_map.mpr ⟨D, hD, rfl⟩, ?_⟩
  exact Scheme.IdealSheafData.mem_support_comap.mpr hyD


end

theorem IsMonomialIn.comap_of_isMonomialIn {E : List X.IdealSheafData} {M : X.IdealSheafData}
    (hM : IsMonomialIn E M) (h : Y ⟶ X) :
    IsMonomialIn (E.map (fun D : X.IdealSheafData => D.comap h)) (M.comap h) := by
  intro y
  obtain ⟨U, hU, a, ha⟩ := hM (h.base y)
  have hlen : (E.map (fun D : X.IdealSheafData => D.comap h)).length = E.length := by simp
  refine ⟨h ⁻¹ᵁ U, hU, fun i => a (Fin.cast hlen i), ?_⟩
  have hget : ∀ i : Fin (E.map (fun D : X.IdealSheafData => D.comap h)).length,
      (E.map (fun D : X.IdealSheafData => D.comap h)).get i
        = (E.get (Fin.cast hlen i)).comap h := by
    intro i
    simp [List.get_eq_getElem]
  have hterm : ∀ i : Fin E.length,
      (((E.get i).comap U.ι) ^ a i).comap (h ∣_ U)
        = ((E.get i).comap h).comap (h ⁻¹ᵁ U).ι ^ a i := by
    intro i
    rw [Scheme.IdealSheafData.comap_pow, ← comap_comap_ι h (E.get i) U]
  have hprod : (∏ i : Fin E.length, (((E.get i).comap U.ι) ^ a i).comap (h ∣_ U))
      = ∏ i : Fin E.length, ((E.get i).comap h).comap (h ⁻¹ᵁ U).ι ^ a i :=
    Finset.prod_congr rfl (fun i _ => hterm i)
  rw [comap_comap_ι h M U, ha, comap_finset_prod_consolidated261, hprod,
    ← Fin.prod_congr'
      (fun j : Fin E.length => ((E.get j).comap h).comap (h ⁻¹ᵁ U).ι ^ a j) hlen]
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [hget i]

section
variable (h : Y ⟶ X) (hg : GeneralizingMap (fun y : Y => h.base y))
include hg

theorem irreducibleComponents_not_subset_support_comap (E : List X.IdealSheafData) (N : X.IdealSheafData)
    (hN : ∀ D ∈ E, ∀ C : Set X, IsIrreducible C → C ⊆ (D.support : Set X) →
      (∀ C' : Set X, IsIrreducible C' → C' ⊆ (D.support : Set X) → C ⊆ C' → C' ⊆ C) →
      ¬ C ⊆ (N.support : Set X)) :
    ∀ D ∈ E.map (fun D : X.IdealSheafData => D.comap h), ∀ C : Set Y, IsIrreducible C →
      C ⊆ (D.support : Set Y) →
      (∀ C' : Set Y, IsIrreducible C' → C' ⊆ (D.support : Set Y) → C ⊆ C' → C' ⊆ C) →
      ¬ C ⊆ ((N.comap h).support : Set Y) := by
  rintro D' hD' C hC hCsub hCmax hCN
  obtain ⟨D, hD, hDD⟩ := List.mem_map.mp hD'
  have hDD' : D' = D.comap h := hDD.symm
  subst hDD'
  have hCclosed : IsClosed C := by
    rw [← closure_subset_iff_isClosed]
    exact hCmax (closure C) hC.closure
      (closure_minimal hCsub (D.comap h).support.isClosed) subset_closure
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hC hCclosed
  have hξC : ξ ∈ C := by
    rw [← hξ]
    exact subset_closure (Set.mem_singleton ξ)
  have hxD : h.base ξ ∈ (D.support : Set X) :=
    Scheme.IdealSheafData.mem_support_comap.mp (hCsub hξC)
  have hxN : h.base ξ ∈ (N.support : Set X) :=
    Scheme.IdealSheafData.mem_support_comap.mp (hCN hξC)
  refine hN D hD (closure ({h.base ξ} : Set X)) isIrreducible_singleton.closure
    (closure_minimal (Set.singleton_subset_iff.mpr hxD) D.support.isClosed) ?_
    (closure_minimal (Set.singleton_subset_iff.mpr hxN) N.support.isClosed)
  intro C'' hC'' hC''sub hsub
  obtain ⟨η, hη⟩ := QuasiSober.sober hC''.closure isClosed_closure
  have hηmem : η ∈ closure C'' := by
    rw [← hη]
    exact subset_closure (Set.mem_singleton η)
  have hηD : η ∈ (D.support : Set X) :=
    closure_minimal hC''sub D.support.isClosed hηmem
  have hηspec : η ⤳ h.base ξ := by
    refine specializes_iff_mem_closure.mpr ?_
    rw [hη]
    exact subset_closure (hsub (subset_closure (Set.mem_singleton _)))
  obtain ⟨ξ', hξ'1, hξ'2⟩ := hg hηspec
  have hξ'2' : h.base ξ' = η := hξ'2
  have hξ'D : ξ' ∈ ((D.comap h).support : Set Y) := by
    refine Scheme.IdealSheafData.mem_support_comap.mpr ?_
    rw [hξ'2']
    exact hηD
  have hclos : closure ({ξ'} : Set Y) ⊆ ((D.comap h).support : Set Y) :=
    closure_minimal (Set.singleton_subset_iff.mpr hξ'D) (D.comap h).support.isClosed
  have hCsubξ' : C ⊆ closure ({ξ'} : Set Y) := by
    rw [← hξ]
    exact closure_minimal
      (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hξ'1)) isClosed_closure
  have hclosure : closure ({ξ'} : Set Y) ⊆ C :=
    hCmax (closure ({ξ'} : Set Y)) isIrreducible_singleton.closure hclos hCsubξ'
  have hξ'C : ξ' ∈ C := hclosure (subset_closure (Set.mem_singleton _))
  have hspec : ξ ⤳ ξ' := by
    refine specializes_iff_mem_closure.mpr ?_
    rw [hξ]
    exact hξ'C
  have hspec2 : h.base ξ ⤳ h.base ξ' := hspec.map h.continuous
  have hηclos : η ∈ closure ({h.base ξ} : Set X) := by
    rw [← hξ'2']
    exact specializes_iff_mem_closure.mp hspec2
  intro z hz
  have hzc : z ∈ closure C'' := subset_closure hz
  rw [← hη] at hzc
  exact closure_minimal (Set.singleton_subset_iff.mpr hηclos) isClosed_closure hzc

theorem isMonomialSplitting_comap_of_generalizingMap {E : List X.IdealSheafData}
    {I M N : X.IdealSheafData} (hs : IsMonomialSplitting E I M N) :
    IsMonomialSplitting (E.map (fun D : X.IdealSheafData => D.comap h)) (I.comap h) (M.comap h)
      (N.comap h) where
  eq_mul := by rw [hs.eq_mul, Scheme.IdealSheafData.comap_mul]
  monomial_support := support_comap_subset_biUnion h E M hs.monomial_support
  monomial := hs.monomial.comap_of_isMonomialIn h
  transversal := irreducibleComponents_not_subset_support_comap h hg E N hs.transversal


end

section
variable (h : Y ⟶ X)

theorem generalizingMap_base_of_flat [Flat h] :
    GeneralizingMap (fun y : Y => h.base y) :=
  AlgebraicGeometry.Flat.generalizingMap h

theorem isMonomialSplitting_comap_of_flat [Flat h]
    {E : List X.IdealSheafData} {I M N : X.IdealSheafData} (hs : IsMonomialSplitting E I M N) :
    IsMonomialSplitting (E.map (fun D : X.IdealSheafData => D.comap h)) (I.comap h) (M.comap h)
      (N.comap h) :=
  isMonomialSplitting_comap_of_generalizingMap h (generalizingMap_base_of_flat h) hs

theorem isMonomialSplitting_comap_of_smooth [Smooth h]
    {E : List X.IdealSheafData} {I M N : X.IdealSheafData} (hs : IsMonomialSplitting E I M N) :
    IsMonomialSplitting (E.map (fun D : X.IdealSheafData => D.comap h)) (I.comap h) (M.comap h)
      (N.comap h) := by
  have : Flat h := inferInstance
  exact isMonomialSplitting_comap_of_flat h hs


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplittingUniqueness
section

open Opposite TopologicalSpace

section

variable {X : Scheme.{u}}

theorem orderAt_eq_of_stalkIdeal_eq_maximalIdeal_pow [IsLocallyNoetherian X]
    (M : X.IdealSheafData) (η : X) (a : ℕ)
    (hM : stalkIdeal M η = IsLocalRing.maximalIdeal ↥(X.presheaf.stalk η) ^ a)
    (hfin : orderAt M η ≠ ⊤) :
    orderAt M η = (a : ℕ∞) := by
  have hnoe : IsNoetherianRing (X.presheaf.stalk η) := inferInstance
  have hbot : stalkIdeal M η ≠ ⊥ := fun h => hfin ((orderAt_eq_top_iff M η).mpr h)
  have hle : (a : ℕ∞) ≤ orderAt M η := (le_orderAt_iff M η a).mpr (le_of_eq hM)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hordn : orderAt M η = (n : ℕ∞) := hn.symm
  have han : a ≤ n := by
    rw [hordn] at hle
    exact_mod_cast hle
  have hna : n ≤ a := by
    by_contra hc
    push Not at hc
    have hc' : a + 1 ≤ n := by omega
    have h1 : ((a + 1 : ℕ) : ℕ∞) ≤ orderAt M η := by
      rw [hordn]
      exact_mod_cast hc'
    have h2 : stalkIdeal M η ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ (a + 1) :=
      (le_orderAt_iff M η (a + 1)).mp h1
    have hps : IsLocalRing.maximalIdeal (X.presheaf.stalk η) •
        (IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a)
        = IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ (a + 1) := by
      rw [Ideal.smul_eq_mul, pow_succ, mul_comm]
    have hsm : (IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a) ≤
        IsLocalRing.maximalIdeal (X.presheaf.stalk η) •
          (IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a) := by
      rw [hps, ← hM]
      exact h2
    have hz : (IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a) = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
        (IsLocalRing.maximalIdeal (X.presheaf.stalk η))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a)
        (IsNoetherian.noetherian _) hsm
        (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    exact hbot (by rw [hM, hz])
  rw [hordn]
  exact_mod_cast le_antisymm hna han

def IsMonomialOnOpen (E : List X.IdealSheafData) (M : X.IdealSheafData) (U : X.Opens)
    (a : Fin E.length → ℕ) : Prop :=
  restrictIdeal M U =
    ((List.finRange E.length).map (fun j => restrictIdeal (E.get j) U ^ a j)).prod

section
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

private theorem ideal_map_listProd_consolidated289 (L : List (Ideal R)) :
    Ideal.map f L.prod = (L.map (fun I => Ideal.map f I)).prod :=
  map_list_prod (Ideal.mapHom f) L

private theorem eq_of_ideal_map_eq_of_ringHom_leftInverse_consolidated289 (g : S →+* R) (hgf : ∀ z, g (f z) = z) {A B : Ideal R}
    (hAB : Ideal.map f A = Ideal.map f B) : A = B := by
  have hcomp : g.comp f = RingHom.id R := RingHom.ext hgf
  have hA : Ideal.map g (Ideal.map f A) = A := by rw [Ideal.map_map, hcomp, Ideal.map_id]
  have hB : Ideal.map g (Ideal.map f B) = B := by rw [Ideal.map_map, hcomp, Ideal.map_id]
  rw [← hA, ← hB, hAB]


end

private theorem hom_apply_hom_apply_of_comp_eq_consolidated289 {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (k : A ⟶ C) (hk : f ≫ g = k) (z : A) : g.hom (f.hom z) = k.hom z := by
  rw [← hk, CommRingCat.hom_comp]
  rfl

private theorem inv_hom_apply_hom_apply_consolidated289 {A B : CommRingCat.{u}} (f : A ⟶ B) [IsIso f]
    (z : A) : (inv f).hom (f.hom z) = z := by
  rw [hom_apply_hom_apply_of_comp_eq_consolidated289 f (inv f) (𝟙 A) (IsIso.hom_inv_id f) z, CommRingCat.hom_id]
  rfl

theorem stalkIdeal_eq_prod_of_isMonomialOnOpen (E : List X.IdealSheafData) (M : X.IdealSheafData)
    (U : X.Opens) (a : Fin E.length → ℕ) (h : IsMonomialOnOpen E M U a) (x : X) (hx : x ∈ U) :
    stalkIdeal M x =
      ((List.finRange E.length).map (fun j => stalkIdeal (E.get j) x ^ a j)).prod := by
  have h' : restrictIdeal M U
      = ((List.finRange E.length).map (fun j => restrictIdeal (E.get j) U ^ a j)).prod := h
  have hxr : x ∈ Set.range (⇑U.ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact hx
  obtain ⟨y, hy⟩ := hxr
  subst hy
  have hgf : ∀ z, (inv (U.ι.stalkMap y)).hom ((U.ι.stalkMap y).hom z) = z :=
    fun z => inv_hom_apply_hom_apply_consolidated289 (U.ι.stalkMap y) z
  refine eq_of_ideal_map_eq_of_ringHom_leftInverse_consolidated289 (U.ι.stalkMap y).hom (inv (U.ι.stalkMap y)).hom hgf ?_
  have hL : ((List.finRange E.length).map
        (fun j => stalkIdeal (E.get j) (U.ι.base y) ^ a j)).map
        (fun I => Ideal.map (U.ι.stalkMap y).hom I)
      = ((List.finRange E.length).map (fun j => restrictIdeal (E.get j) U ^ a j)).map
        (fun I => stalkIdeal I y) := by
    rw [List.map_map, List.map_map]
    refine List.map_congr_left ?_
    intro j _
    show Ideal.map (U.ι.stalkMap y).hom (stalkIdeal (E.get j) (U.ι.base y) ^ a j)
        = stalkIdeal (restrictIdeal (E.get j) U ^ a j) y
    rw [stalkIdeal_pow, restrictIdeal_eq_comap_ι, stalkIdeal_comap, Ideal.map_pow]
  rw [ideal_map_listProd_consolidated289, hL, ← stalkIdeal_listProd, ← h', restrictIdeal_eq_comap_ι,
    stalkIdeal_comap]

section
variable {k : Type u} [Field k] [CharZero k] [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p] (E : List X.IdealSheafData) (_hE : InStrictNormalCrossingPosition p E) {I M N : X.IdealSheafData}
include _hE

theorem orderAt_genericPoint_eq_of_isMonomialSplitting (_hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N)
    {D : X.IdealSheafData} (hD : D ∈ E) {C : Set X} (hC : IsIrreducibleComponentOfSupport D C) :
    orderAt M hC.isIrreducible.genericPoint = orderAt I hC.isIrreducible.genericPoint := by
  have hmax' : ∀ C' : Set X, IsIrreducible C' → C' ⊆ (D.support : Set X) → C ⊆ C' → C' ⊆ C := by
    intro C' h1 h2 h3
    have he := hC.maximal C' h1 h3 h2
    intro y hy
    rw [he] at hy
    exact hy
  have hNC : ¬ C ⊆ (N.support : Set X) :=
    hsplit.transversal D hD C hC.isIrreducible hC.subset_support hmax'
  have hηN : hC.isIrreducible.genericPoint ∉ N.support := by
    intro h
    refine hNC ?_
    rw [← hC.closure_genericPoint]
    exact (N.support.2).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h)
  have h0 : orderAt N hC.isIrreducible.genericPoint = 0 :=
    (orderAt_eq_zero_iff_not_mem_support N hC.isIrreducible.genericPoint).mpr hηN
  rw [hsplit.eq_mul, orderAt_mul k p M N hC.isIrreducible.genericPoint, h0, add_zero]

theorem exponent_le_orderAlongComponent (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N)
    (U : X.Opens) (a : Fin E.length → ℕ) (ha : IsMonomialOnOpen E M U a)
    (l : Fin E.length) {C' : Set X} (hC' : IsIrreducibleComponentOfSupport (E.get l) C')
    (x : X) (hxU : x ∈ U) (hxC : x ∈ C') :
    a l ≤ orderAlongComponent I hC'.isIrreducible := by
  have hxcl : x ∈ closure ({hC'.isIrreducible.genericPoint} : Set X) := by
    rw [hC'.closure_genericPoint]
    exact hxC
  have hηU : hC'.isIrreducible.genericPoint ∈ U := by
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp hxcl (U : Set X) U.isOpen hxU
    rw [Set.mem_singleton_iff] at hz
    rw [← hz]
    exact hzU
  have hprod : stalkIdeal M hC'.isIrreducible.genericPoint =
      ((List.finRange E.length).map
        (fun j => stalkIdeal (E.get j) hC'.isIrreducible.genericPoint ^ a j)).prod :=
    stalkIdeal_eq_prod_of_isMonomialOnOpen E M U a ha hC'.isIrreducible.genericPoint hηU
  have hlen : (l : ℕ) <
      ((List.finRange E.length).map
        (fun j => stalkIdeal (E.get j) hC'.isIrreducible.genericPoint ^ a j)).length := by
    simp
  have hget : ((List.finRange E.length).map
        (fun j => stalkIdeal (E.get j) hC'.isIrreducible.genericPoint ^ a j))[(l : ℕ)]'hlen
      = stalkIdeal (E.get l) hC'.isIrreducible.genericPoint ^ a l := by
    simp
  have h1 : stalkIdeal M hC'.isIrreducible.genericPoint ≤
      stalkIdeal (E.get l) hC'.isIrreducible.genericPoint ^ a l := by
    rw [hprod, ← hget]
    exact Ideal.list_prod_le_getElem _ _ hlen
  have hle : stalkIdeal (E.get l) hC'.isIrreducible.genericPoint ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk hC'.isIrreducible.genericPoint) :=
    (mem_support_iff_stalkIdeal_le_maximalIdeal (E.get l)
      hC'.isIrreducible.genericPoint).mp hC'.genericPoint_mem_support
  have h2 : (a l : ℕ∞) ≤ orderAt M hC'.isIrreducible.genericPoint :=
    (le_orderAt_iff M hC'.isIrreducible.genericPoint (a l)).mpr
      (h1.trans (Ideal.pow_right_mono hle (a l)))
  have hIM : I ≤ M := by
    rw [hsplit.eq_mul]
    refine (le_iff_forall_stalkIdeal_le _ _).mpr (fun y => ?_)
    rw [stalkIdeal_mul]
    exact Ideal.mul_le_inf.trans inf_le_left
  have h3 : orderAt M hC'.isIrreducible.genericPoint ≤
      orderAt I hC'.isIrreducible.genericPoint :=
    orderAt_le_of_le hIM hC'.isIrreducible.genericPoint
  have h4 : (a l : ℕ∞) ≤ (orderAlongComponent I hC'.isIrreducible : ℕ∞) := by
    rw [coe_orderAlongComponent_eq_orderAt_genericPoint hC' hI]
    exact h2.trans h3
  exact_mod_cast h4


end

section
variable {R : Type*} [CommRing R]

private theorem ideal_listProd_le_mul_getElem_of_lt_consolidated289 (L : List (Ideal R)) :
    ∀ (i j : ℕ) (hi : i < L.length) (hj : j < L.length), i < j →
      L.prod ≤ (L[i]'hi) * (L[j]'hj) := by
  induction L with
  | nil =>
      intro i _ hi _ _
      simp at hi
  | cons A L ih =>
      intro i j hi hj hij
      cases i with
      | zero =>
          cases j with
          | zero => exact absurd hij (lt_irrefl 0)
          | succ j' =>
              have hj' : j' < L.length := by simpa using hj
              simp only [List.prod_cons, List.getElem_cons_zero, List.getElem_cons_succ]
              exact Ideal.mul_mono le_rfl (Ideal.list_prod_le_getElem L j' hj')
      | succ i' =>
          cases j with
          | zero => exact absurd hij (Nat.not_lt_zero _)
          | succ j' =>
              have hi' : i' < L.length := by simpa using hi
              have hj' : j' < L.length := by simpa using hj
              simp only [List.prod_cons, List.getElem_cons_succ]
              exact le_trans (le_trans Ideal.mul_le_inf inf_le_right)
                (ih i' j' hi' hj' (by omega))

private theorem ideal_listProd_le_mul_getElem_of_ne_consolidated289 (L : List (Ideal R))
    (i j : ℕ) (hi : i < L.length) (hj : j < L.length) (hij : i ≠ j) :
    L.prod ≤ (L[i]'hi) * (L[j]'hj) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact ideal_listProd_le_mul_getElem_of_lt_consolidated289 L i j hi hj h
  · rw [mul_comm]
    exact ideal_listProd_le_mul_getElem_of_lt_consolidated289 L j i hj hi h

private theorem ideal_listProd_le_pow_add_consolidated289 (m : Ideal R)
    (L : List (Ideal R)) (i j : ℕ) (hi : i < L.length) (hj : j < L.length) (hij : i ≠ j)
    (b c : ℕ) (hbi : (L[i]'hi) ≤ m ^ b) (hcj : (L[j]'hj) ≤ m ^ c) :
    L.prod ≤ m ^ (b + c) := by
  refine le_trans (ideal_listProd_le_mul_getElem_of_ne_consolidated289 L i j hi hj hij) ?_
  rw [pow_add]
  exact Ideal.mul_mono hbi hcj

private theorem ideal_listProd_finRange_eq_of_ne_eq_top_consolidated289 {n : ℕ}
    (f : Fin n → Ideal R) (j : Fin n) (h : ∀ l : Fin n, l ≠ j → f l = ⊤) :
    ((List.finRange n).map f).prod = f j := by
  rw [← Fin.prod_univ_def]
  refine Finset.prod_eq_single j (fun l _ hl => ?_) (fun hj => absurd (Finset.mem_univ j) hj)
  rw [h l hl, Ideal.one_eq_top]


end

theorem exponent_eq_orderAlongComponent {k : Type u} [Field k] [CharZero k]
    [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) {I M N : X.IdealSheafData}
    (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N)
    (U : X.Opens) (a : Fin E.length → ℕ) (ha : IsMonomialOnOpen E M U a)
    (j : Fin E.length) {C : Set X} (hC : IsIrreducibleComponentOfSupport (E.get j) C)
    (x : X) (hxU : x ∈ U) (hxC : x ∈ C) :
    a j = orderAlongComponent I hC.isIrreducible := by
  have hD : E.get j ∈ E := by simp
  have hxcl : x ∈ closure ({hC.isIrreducible.genericPoint} : Set X) := by
    rw [hC.closure_genericPoint]
    exact hxC
  have hηU : hC.isIrreducible.genericPoint ∈ U := by
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp hxcl (U : Set X) U.isOpen hxU
    rw [Set.mem_singleton_iff] at hz
    rw [← hz]
    exact hzU
  have hηC : hC.isIrreducible.genericPoint ∈ C := hC.genericPoint_mem
  have hlocj : IsEtaleLocallyCoordinateDivisor p (E.get j) :=
    isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE (E.get j) hD
  have hjmax : stalkIdeal (E.get j) hC.isIrreducible.genericPoint ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
    (mem_support_iff_stalkIdeal_le_maximalIdeal (E.get j)
      hC.isIrreducible.genericPoint).mp hC.genericPoint_mem_support
  have hmemj : stalkIdeal (monomialPartAlongDivisor I (E.get j)) hC.isIrreducible.genericPoint =
      stalkIdeal (E.get j) hC.isIrreducible.genericPoint ^
        orderAlongComponent I hC.isIrreducible :=
    stalkIdeal_monomialPartAlongDivisor_of_mem p I hlocj hC hηC
  have hbj : stalkIdeal (monomialPartAlongDivisor I (E.get j)) hC.isIrreducible.genericPoint ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) ^
        orderAlongComponent I hC.isIrreducible := by
    rw [hmemj]
    exact Ideal.pow_right_mono hjmax _
  have hPstalk : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint =
      (E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D) hC.isIrreducible.genericPoint)).prod :=
    stalkIdeal_monomialFactorIdeal E I hC.isIrreducible.genericPoint
  have hPord : orderAt (monomialFactorIdeal E I) hC.isIrreducible.genericPoint =
      (orderAlongComponent I hC.isIrreducible : ℕ∞) :=
    orderAt_monomialFactorIdeal_genericPoint p E I hE hI hD hC
  have hzero : ∀ l : Fin E.length, l ≠ j →
      stalkIdeal (E.get l) hC.isIrreducible.genericPoint ^ a l = ⊤ := by
    intro l hlj
    by_cases hs : hC.isIrreducible.genericPoint ∈ ((E.get l).support : Set X)
    · have hal : a l = 0 := by
        obtain ⟨C', hC', hηC'⟩ :=
          exists_isIrreducibleComponentOfSupport (E.get l) hC.isIrreducible.genericPoint hs
        have hDl : E.get l ∈ E := by simp
        have hlocl : IsEtaleLocallyCoordinateDivisor p (E.get l) :=
          isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE (E.get l) hDl
        have hle : a l ≤ orderAlongComponent I hC'.isIrreducible :=
          exponent_le_orderAlongComponent p E hE hI hsplit U a ha l hC'
            hC.isIrreducible.genericPoint hηU hηC'
        have hmeml : stalkIdeal (monomialPartAlongDivisor I (E.get l)) hC.isIrreducible.genericPoint =
            stalkIdeal (E.get l) hC.isIrreducible.genericPoint ^
              orderAlongComponent I hC'.isIrreducible :=
          stalkIdeal_monomialPartAlongDivisor_of_mem p I hlocl hC' hηC'
        have hlmax : stalkIdeal (E.get l) hC.isIrreducible.genericPoint ≤
            IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
          (mem_support_iff_stalkIdeal_le_maximalIdeal (E.get l)
            hC.isIrreducible.genericPoint).mp hs
        have hbl : stalkIdeal (monomialPartAlongDivisor I (E.get l)) hC.isIrreducible.genericPoint ≤
            IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) ^ a l := by
          rw [hmeml]
          exact le_trans (Ideal.pow_right_mono hlmax _) (Ideal.pow_le_pow_right hle)
        have hjlen : (j : ℕ) <
            (E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D)
              hC.isIrreducible.genericPoint)).length := by
          simp
        have hllen : (l : ℕ) <
            (E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D)
              hC.isIrreducible.genericPoint)).length := by
          simp
        have hjne : (j : ℕ) ≠ (l : ℕ) := by
          intro hv
          apply hlj
          ext
          exact hv.symm
        have hgj : (E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D)
            hC.isIrreducible.genericPoint))[(j : ℕ)]'hjlen =
            stalkIdeal (monomialPartAlongDivisor I (E.get j)) hC.isIrreducible.genericPoint := by
          simp
        have hgl : (E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D)
            hC.isIrreducible.genericPoint))[(l : ℕ)]'hllen =
            stalkIdeal (monomialPartAlongDivisor I (E.get l)) hC.isIrreducible.genericPoint := by
          simp
        have hPle : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint ≤
            IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) ^
              (orderAlongComponent I hC.isIrreducible + a l) := by
          rw [hPstalk]
          refine ideal_listProd_le_pow_add_consolidated289 _ _ (j : ℕ) (l : ℕ) hjlen hllen hjne _ _ ?_ ?_
          · rw [hgj]
            exact hbj
          · rw [hgl]
            exact hbl
        have hord : ((orderAlongComponent I hC.isIrreducible + a l : ℕ) : ℕ∞) ≤
            orderAt (monomialFactorIdeal E I) hC.isIrreducible.genericPoint :=
          (le_orderAt_iff (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
            (orderAlongComponent I hC.isIrreducible + a l)).mpr hPle
        rw [hPord] at hord
        have hnat : orderAlongComponent I hC.isIrreducible + a l ≤
            orderAlongComponent I hC.isIrreducible := by exact_mod_cast hord
        omega
      rw [hal, pow_zero, Ideal.one_eq_top]
    · have hstop : stalkIdeal (E.get l) hC.isIrreducible.genericPoint = ⊤ := by
        by_contra hcon
        exact hs ((mem_support_iff_stalkIdeal_ne_top (E.get l)
          hC.isIrreducible.genericPoint).mpr hcon)
      rw [hstop, ← Ideal.one_eq_top, one_pow]
  have hprod : stalkIdeal M hC.isIrreducible.genericPoint =
      ((List.finRange E.length).map
        (fun i => stalkIdeal (E.get i) hC.isIrreducible.genericPoint ^ a i)).prod :=
    stalkIdeal_eq_prod_of_isMonomialOnOpen E M U a ha hC.isIrreducible.genericPoint hηU
  have hMstalk : stalkIdeal M hC.isIrreducible.genericPoint =
      stalkIdeal (E.get j) hC.isIrreducible.genericPoint ^ a j := by
    rw [hprod]
    exact ideal_listProd_finRange_eq_of_ne_eq_top_consolidated289
      (fun i => stalkIdeal (E.get i) hC.isIrreducible.genericPoint ^ a i) j hzero
  have hmaxj : stalkIdeal (E.get j) hC.isIrreducible.genericPoint =
      IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
    stalkIdeal_genericPoint_eq_maximalIdeal p (E.get j) hlocj hC.isIrreducible
      hC.subset_support hC.maximal
  have hMI : orderAt M hC.isIrreducible.genericPoint =
      orderAt I hC.isIrreducible.genericPoint :=
    orderAt_genericPoint_eq_of_isMonomialSplitting p E hE hI hsplit hD hC
  have hfin : orderAt M hC.isIrreducible.genericPoint ≠ ⊤ := by
    rw [hMI]
    exact orderAt_ne_top_of_nonzeroOnComponents I hI hC.isIrreducible.genericPoint
  have hMord : orderAt M hC.isIrreducible.genericPoint = (a j : ℕ∞) :=
    orderAt_eq_of_stalkIdeal_eq_maximalIdeal_pow M hC.isIrreducible.genericPoint (a j)
      (by rw [hMstalk, hmaxj]) hfin
  have hco : (orderAlongComponent I hC.isIrreducible : ℕ∞) =
      orderAt I hC.isIrreducible.genericPoint := coe_orderAlongComponent_eq_orderAt_genericPoint hC hI
  have hfinal : ((a j : ℕ) : ℕ∞) = ((orderAlongComponent I hC.isIrreducible : ℕ) : ℕ∞) := by
    rw [← hMord, hMI, ← hco]
  exact_mod_cast hfinal

private theorem map_finRange_get_eq_map_consolidated289 {α : Type*} {β : Type*} (l : List α) (g : α → β) :
    (List.finRange l.length).map (fun j => g (l.get j)) = l.map g := by
  refine List.ext_getElem (by simp) ?_
  intro n h1 h2
  simp

section
variable {k : Type u} [Field k] [CharZero k] [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p] (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
include hE

theorem stalkIdeal_eq_stalkIdeal_monomialFactorIdeal {I M N : X.IdealSheafData}
    (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N) (x : X) :
    stalkIdeal M x = stalkIdeal (monomialFactorIdeal E I) x := by
  obtain ⟨U, hxU, a, haU⟩ := hsplit.monomial x
  have hmon : IsMonomialOnOpen E M U a := by
    show M.comap U.ι
        = ((List.finRange E.length).map (fun j => (E.get j).comap U.ι ^ a j)).prod
    rw [haU, Fin.prod_univ_def]
  have hstep : ∀ j : Fin E.length,
      stalkIdeal (E.get j) x ^ a j = stalkIdeal (monomialPartAlongDivisor I (E.get j)) x := by
    intro j
    have hmem : E.get j ∈ E := by simp
    by_cases hx : x ∈ ((E.get j).support : Set X)
    · obtain ⟨C, hC, hxC⟩ := exists_isIrreducibleComponentOfSupport (E.get j) x hx
      have hloc : IsEtaleLocallyCoordinateDivisor p (E.get j) :=
        isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE (E.get j) hmem
      rw [stalkIdeal_monomialPartAlongDivisor_of_mem p I hloc hC hxC,
        exponent_eq_orderAlongComponent p E hE hI hsplit U a hmon j hC x hxU hxC]
    · have h1 : stalkIdeal (E.get j) x = ⊤ := by
        by_contra hne
        exact hx ((mem_support_iff_stalkIdeal_ne_top (E.get j) x).mpr hne)
      rw [stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I (E.get j) hx, h1,
        ← Ideal.one_eq_top, one_pow]
  have hlist : (List.finRange E.length).map (fun j => stalkIdeal (E.get j) x ^ a j)
      = E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D) x) := by
    rw [← map_finRange_get_eq_map_consolidated289 E (fun D => stalkIdeal (monomialPartAlongDivisor I D) x)]
    exact List.map_congr_left (fun j _ => hstep j)
  rw [stalkIdeal_eq_prod_of_isMonomialOnOpen E M U a hmon x hxU,
    stalkIdeal_monomialFactorIdeal E I x, hlist]

theorem eq_monomialFactorIdeal {I M N : X.IdealSheafData}
    (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N) :
    M = monomialFactorIdeal E I := by
  have hstalk : ∀ x : X, stalkIdeal M x = stalkIdeal (monomialFactorIdeal E I) x :=
    fun x => stalkIdeal_eq_stalkIdeal_monomialFactorIdeal p E hE hI hsplit x
  refine le_antisymm ?_ ?_
  · exact (le_iff_forall_stalkIdeal_le M (monomialFactorIdeal E I)).mpr
      (fun x => le_of_eq (hstalk x))
  · exact (le_iff_forall_stalkIdeal_le (monomialFactorIdeal E I) M).mpr
      (fun x => le_of_eq (hstalk x).symm)

theorem eq_nonMonomialFactorIdeal {I M N : X.IdealSheafData}
    (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N) :
    N = nonMonomialFactorIdeal E I := by
  have hM : M = monomialFactorIdeal E I := eq_monomialFactorIdeal p E hE hI hsplit
  have hF : Blowup.IsLocallyGeneratedByNonZeroDivisor (monomialFactorIdeal E I) :=
    isLocallyGeneratedByNonZeroDivisor_monomialFactorIdeal p E I hE
  have hIM : I ≤ monomialFactorIdeal E I := by
    rw [← hM, hsplit.eq_mul]
    refine (le_iff_forall_stalkIdeal_le _ _).mpr (fun y => ?_)
    rw [stalkIdeal_mul]
    exact Ideal.mul_le_inf.trans inf_le_left
  have hmul : monomialFactorIdeal E I * N
      = monomialFactorIdeal E I * nonMonomialFactorIdeal E I := by
    rw [nonMonomialFactorIdeal_eq_idealSheafColon, hF.mul_idealSheafColon hIM, ← hM]
    exact hsplit.eq_mul.symm
  exact hF.eq_of_mul_eq_mul hmul

theorem isMonomialSplitting_unique {I M N M' N' : X.IdealSheafData}
    (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N)
    (hsplit' : IsMonomialSplitting E I M' N') :
    M = M' ∧ N = N' :=
  ⟨(eq_monomialFactorIdeal p E hE hI hsplit).trans
      (eq_monomialFactorIdeal p E hE hI hsplit').symm,
    (eq_nonMonomialFactorIdeal p E hE hI hsplit).trans
      (eq_nonMonomialFactorIdeal p E hE hI hsplit').symm⟩


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.StrictTransformRestriction
section


section

private theorem ker_le_ker_of_comp_eq_consolidated329 {A B T : Scheme.{u}} (f : A ⟶ T) (g : B ⟶ T) (e : A ⟶ B)
    (h : e ≫ g = f) : g.ker ≤ f.ker := by
  subst h
  exact Scheme.Hom.le_ker_comp e g

theorem comap_strictTransform_of_iso {X X₁ X₁' : Scheme.{u}} (π : X₁ ⟶ X)
    (f : X₁' ≅ X₁) (Z D : X.IdealSheafData) (_hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Z.comap π))
    [QuasiCompact (strictTransformι π Z D)]
    [QuasiCompact (strictTransformι (f.hom ≫ π) Z D)] :
    (Blowup.strictTransform π Z D).comap f.hom = Blowup.strictTransform (f.hom ≫ π) Z D := by
  have hRHS : Blowup.strictTransform (f.hom ≫ π) Z D
      = Blowup.strictTransform f.hom (Z.comap π) (D.comap π) :=
    strictTransform_eq_of_comap_eq (f.hom ≫ π) f.hom Z D (Z.comap π) (D.comap π)
      (by rw [Scheme.IdealSheafData.comap_comp])
      (by rw [Scheme.IdealSheafData.comap_comp])
  obtain ⟨m₀, hiso, hm₀⟩ :=
    Scheme.IdealSheafData.exists_iso_subscheme_comap_of_isIso f.hom (D.comap π)
  have := hiso
  have hsupp : ((Z.comap π).comap f.hom).support.compl
      = f.hom ⁻¹ᵁ (Z.comap π).support.compl := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have h1 : m₀ ⁻¹ᵁ strictTransformOpens π Z D
      = ((D.comap π).comap f.hom).subschemeι ⁻¹ᵁ (f.hom ⁻¹ᵁ (Z.comap π).support.compl) :=
    congrArg (fun w => w ⁻¹ᵁ (Z.comap π).support.compl) hm₀
  have hV' : strictTransformOpens f.hom (Z.comap π) (D.comap π)
      = m₀ ⁻¹ᵁ strictTransformOpens π Z D := by
    rw [h1]
    exact congrArg (fun W => ((D.comap π).comap f.hom).subschemeι ⁻¹ᵁ W) hsupp
  have hm₀2 : m₀ ≫ ((D.comap π).subschemeι ≫ inv f.hom)
      = ((D.comap π).comap f.hom).subschemeι := by
    rw [← Category.assoc, hm₀, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hm₀3 : inv m₀ ≫ ((D.comap π).comap f.hom).subschemeι
      = (D.comap π).subschemeι ≫ inv f.hom := by
    rw [IsIso.inv_comp_eq, hm₀2]
  have hinvle : strictTransformOpens π Z D
      ≤ inv m₀ ⁻¹ᵁ strictTransformOpens f.hom (Z.comap π) (D.comap π) := by
    rw [hV']
    have h3 : inv m₀ ⁻¹ᵁ (m₀ ⁻¹ᵁ strictTransformOpens π Z D)
        = (inv m₀ ≫ m₀) ⁻¹ᵁ strictTransformOpens π Z D := rfl
    rw [h3, IsIso.inv_hom_id]
    simp
  have hfac1 : (Scheme.Hom.resLE m₀ (strictTransformOpens π Z D)
        (strictTransformOpens f.hom (Z.comap π) (D.comap π)) (le_of_eq hV'))
      ≫ (strictTransformι π Z D ≫ inv f.hom)
      = strictTransformι f.hom (Z.comap π) (D.comap π) := by
    rw [strictTransformι_eq_ι_comp_subschemeι π Z D,
      strictTransformι_eq_ι_comp_subschemeι f.hom (Z.comap π) (D.comap π),
      ← Category.assoc, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
      Category.assoc, hm₀2]
  have hfac2 : (Scheme.Hom.resLE (inv m₀)
        (strictTransformOpens f.hom (Z.comap π) (D.comap π))
        (strictTransformOpens π Z D) hinvle)
      ≫ strictTransformι f.hom (Z.comap π) (D.comap π)
      = strictTransformι π Z D ≫ inv f.hom := by
    rw [strictTransformι_eq_ι_comp_subschemeι f.hom (Z.comap π) (D.comap π),
      strictTransformι_eq_ι_comp_subschemeι π Z D, ← Category.assoc, Scheme.Hom.resLE_comp_ι,
      Category.assoc, hm₀3, Category.assoc]
  have hcomp : (strictTransformι π Z D ≫ inv f.hom) ≫ f.hom
      = strictTransformι π Z D := by
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have : QuasiCompact (strictTransformι π Z D ≫ inv f.hom) := inferInstance
  have : QuasiCompact ((strictTransformι π Z D ≫ inv f.hom) ≫ f.hom) := by
    rw [hcomp]
    infer_instance
  have hL := Blowup.comap_ker_comp_of_isOpenImmersion
    (strictTransformι π Z D ≫ inv f.hom) f.hom
  rw [hcomp] at hL
  rw [hRHS, strictTransform_eq_ker_strictTransformι π Z D, hL,
    strictTransform_eq_ker_strictTransformι f.hom (Z.comap π) (D.comap π)]
  exact le_antisymm (ker_le_ker_of_comp_eq_consolidated329 _ _ _ hfac1) (ker_le_ker_of_comp_eq_consolidated329 _ _ _ hfac2)

section
variable {X X₁ S S₁ : Scheme.{u}}

theorem exists_iso_subscheme_of_ker_eq_strictTransform (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (ι : S ⟶ X) (ι₁ : S₁ ⟶ X₁) (ρ : S₁ ⟶ S)
    [IsClosedImmersion ι] [IsClosedImmersion ι₁]
    (hsq : ι₁ ≫ π = ρ ≫ ι)
    (hker : Scheme.Hom.ker ι₁ = Blowup.strictTransform π Z (Scheme.Hom.ker ι)) :
    ∃ (e : S ≅ (Scheme.Hom.ker ι).subscheme)
      (e₁ : S₁ ≅ (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subscheme),
      e.hom ≫ (Scheme.Hom.ker ι).subschemeι = ι ∧
        e₁.hom ≫ (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι = ι₁ ∧
        e₁.hom ≫ strictTransformSubschemeLift π Z (Scheme.Hom.ker ι) = ρ ≫ e.hom := by
  have hkH : (Scheme.Hom.ker ι).subschemeι.ker = Scheme.Hom.ker ι :=
    Scheme.IdealSheafData.ker_subschemeι _
  have hkT : (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι.ker
      = Blowup.strictTransform π Z (Scheme.Hom.ker ι) :=
    Scheme.IdealSheafData.ker_subschemeι _
  have hu : IsClosedImmersion.lift (Scheme.Hom.ker ι).subschemeι ι (le_of_eq hkH) ≫
      (Scheme.Hom.ker ι).subschemeι = ι := IsClosedImmersion.lift_fac _ _ _
  have : IsIso (IsClosedImmersion.lift (Scheme.Hom.ker ι).subschemeι ι (le_of_eq hkH)) :=
    IsClosedImmersion.isIso_of_ker_eq ι (Scheme.Hom.ker ι).subschemeι _ hu hkH.symm
  have hu₁ : IsClosedImmersion.lift (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι ι₁
        (le_of_eq (hkT.trans hker.symm)) ≫
      (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι = ι₁ :=
    IsClosedImmersion.lift_fac _ _ _
  have : IsIso (IsClosedImmersion.lift (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι ι₁
      (le_of_eq (hkT.trans hker.symm))) :=
    IsClosedImmersion.isIso_of_ker_eq ι₁ (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι _
      hu₁ (hker.trans hkT.symm)
  refine ⟨asIso (IsClosedImmersion.lift (Scheme.Hom.ker ι).subschemeι ι (le_of_eq hkH)),
    asIso (IsClosedImmersion.lift (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι ι₁
      (le_of_eq (hkT.trans hker.symm))), hu, hu₁, ?_⟩
  rw [← cancel_mono (Scheme.Hom.ker ι).subschemeι, Category.assoc,
    strictTransformSubschemeLift_comp_subschemeι π Z (Scheme.Hom.ker ι), ← Category.assoc]
  simp only [asIso_hom]
  rw [hu₁, Category.assoc, hu, hsq]

theorem comap_strictTransform_of_closedImmersion_commSq {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k)) (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (ι : S ⟶ X) (ι₁ : S₁ ⟶ X₁) (ρ : S₁ ⟶ S)
    [IsClosedImmersion ι] [IsClosedImmersion ι₁]
    [IsLocallyNoetherian X₁] [IsLocallyNoetherian S₁]
    (hsq : ι₁ ≫ π = ρ ≫ ι)
    (hker : Scheme.Hom.ker ι₁ = Blowup.strictTransform π Z (Scheme.Hom.ker ι))
    (E : List X.IdealSheafData)
    (hsnc : HasStrictNormalCrossingsWith p Z (Scheme.Hom.ker ι :: E))
    (hHZ : Scheme.Hom.ker ι ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (D : X.IdealSheafData) (hD : D ∈ E) :
    (Blowup.strictTransform π Z D).comap ι₁ =
      Blowup.strictTransform ρ (Z.comap ι) (D.comap ι) := by
  obtain ⟨e, e₁, he, he₁, hcomm⟩ :=
    exists_iso_subscheme_of_ker_eq_strictTransform π Z ι ι₁ ρ hsq hker
  have : IsLocallyNoetherian (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subscheme :=
    isLocallyNoetherian_subscheme _
  have hq := isBlowupAlongIdealSheaf_strictTransformSubschemeLift π Z (Scheme.Hom.ker ι) hπ
  have hfinal : (e₁.hom ≫ strictTransformSubschemeLift π Z (Scheme.Hom.ker ι)) ≫
      (Scheme.Hom.ker ι).subschemeι = ρ ≫ ι := by
    rw [Category.assoc, strictTransformSubschemeLift_comp_subschemeι, ← Category.assoc, he₁, hsq]
  have hmain := comap_strictTransform_eq_strictTransformSubschemeLift p π Z (Scheme.Hom.ker ι) E hsnc hHZ hπ D hD
  have h1 : (Blowup.strictTransform π Z D).comap ι₁
      = ((Blowup.strictTransform π Z D).comap
          (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι).comap e₁.hom := by
    rw [← he₁, Scheme.IdealSheafData.comap_comp]
  rw [h1, hmain, comap_strictTransform_of_iso
    (strictTransformSubschemeLift π Z (Scheme.Hom.ker ι)) e₁ (Z.comap (Scheme.Hom.ker ι).subschemeι)
    (D.comap (Scheme.Hom.ker ι).subschemeι) hq.1]
  refine strictTransform_eq_of_comap_eq _ ρ _ _ _ _ ?_ ?_
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hfinal]
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hfinal]

theorem comap_exceptionalIdeal_of_commSq (π : X₁ ⟶ X)
    (ι : S ⟶ X) (ι₁ : S₁ ⟶ X₁) (ρ : S₁ ⟶ S) (hsq : ι₁ ≫ π = ρ ≫ ι)
    (Z : X.IdealSheafData) :
    (Blowup.exceptionalIdeal π Z).comap ι₁ = Blowup.exceptionalIdeal ρ (Z.comap ι) := by
  rw [Blowup.exceptionalIdeal_eq_comap, Blowup.exceptionalIdeal_eq_comap, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, hsq]

theorem map_comap_strictTransform_append_exceptionalIdeal {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k)) (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (ι : S ⟶ X) (ι₁ : S₁ ⟶ X₁) (ρ : S₁ ⟶ S)
    [IsClosedImmersion ι] [IsClosedImmersion ι₁]
    [IsLocallyNoetherian X₁] [IsLocallyNoetherian S₁]
    (hsq : ι₁ ≫ π = ρ ≫ ι)
    (hker : Scheme.Hom.ker ι₁ = Blowup.strictTransform π Z (Scheme.Hom.ker ι))
    (E : List X.IdealSheafData)
    (hsnc : HasStrictNormalCrossingsWith p Z (Scheme.Hom.ker ι :: E))
    (hHZ : Scheme.Hom.ker ι ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    (List.map (Blowup.strictTransform π Z) E ++ [Blowup.exceptionalIdeal π Z]).map
        (fun A => A.comap ι₁) =
      List.map (Blowup.strictTransform ρ (Z.comap ι)) (List.map (fun D => D.comap ι) E) ++
        [Blowup.exceptionalIdeal ρ (Z.comap ι)] := by
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · refine List.map_congr_left ?_
    intro D hD
    exact comap_strictTransform_of_closedImmersion_commSq p π Z ι ι₁ ρ hsq hker E hsnc hHZ hπ D hD
  · rw [comap_exceptionalIdeal_of_commSq π ι ι₁ ρ hsq Z]


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.ClosedEmbeddingsIntoAffineSpace
section



private theorem comp_appTop_apply_consolidated116 {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (f ≫ g).appTop x = f.appTop (g.appTop x) := by
  simp
  rfl

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (a b : Γ(Y, ⊤))

private theorem appTop_add_consolidated116 :
    f.appTop (a + b) = f.appTop a + f.appTop b :=
  map_add (CommRingCat.Hom.hom f.appTop) a b

private theorem appTop_sub_consolidated116 :
    f.appTop (a - b) = f.appTop a - f.appTop b :=
  map_sub (CommRingCat.Hom.hom f.appTop) a b


end

private theorem appTop_id_apply_consolidated116 {X : Scheme.{u}} (x : Γ(X, ⊤)) :
    (𝟙 X : X ⟶ X).appTop x = x := by
  simp

private theorem exists_iso_affineSpace_sum_comp_eq_of_coord_consolidated116 {S : Scheme.{u}} (n m : ℕ)
    {Y : Scheme.{u}}
    (p : Y ⟶ S)
    (e₁ : Y ⟶ AffineSpace (ULift.{u} (Fin n)) S)
    (e₂ : Y ⟶ AffineSpace (ULift.{u} (Fin m)) S)
    (h₁ : e₁ ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = p)
    (h₂ : e₂ ≫ (AffineSpace (ULift.{u} (Fin m)) S ↘ S) = p)
    (F : Fin m → Γ(AffineSpace (ULift.{u} (Fin n)) S, ⊤))
    (hF : ∀ b : Fin m, e₁.appTop (F b)
      = e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m))))
    (G : Fin n → Γ(AffineSpace (ULift.{u} (Fin m)) S, ⊤))
    (hG : ∀ a : Fin n, e₂.appTop (G a)
      = e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))))
    (L R : Y ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S)
    (hLover : L ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) = p)
    (hRover : R ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) = p)
    (hLinl : ∀ a : Fin n, L.appTop (AffineSpace.coord S
        (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
      = e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))))
    (hLinr : ∀ b : Fin m, L.appTop (AffineSpace.coord S
        (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) = 0)
    (hRinl : ∀ a : Fin n, R.appTop (AffineSpace.coord S
        (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))) = 0)
    (hRinr : ∀ b : Fin m, R.appTop (AffineSpace.coord S
        (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
      = e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m)))) :
    ∃ Φ : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ≅ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
      Φ.hom ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
          = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) ∧ L ≫ Φ.hom = R := by
  obtain ⟨pr₁, hpr₁, hpr₁c⟩ :
      ∃ q : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ⟶ AffineSpace (ULift.{u} (Fin n)) S,
        q ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S)
            = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) ∧
          ∀ a : Fin n, q.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n)))
            = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)) :=
    ⟨AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
        (fun a : ULift.{u} (Fin n) =>
          AffineSpace.coord S (ULift.up (Sum.inl a.down) : ULift.{u} (Fin n ⊕ Fin m))),
      AffineSpace.homOfVector_over _ _, fun a => AffineSpace.homOfVector_appTop_coord _ _ _⟩
  obtain ⟨pr₂, hpr₂, hpr₂c⟩ :
      ∃ q : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ⟶ AffineSpace (ULift.{u} (Fin m)) S,
        q ≫ (AffineSpace (ULift.{u} (Fin m)) S ↘ S)
            = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) ∧
          ∀ b : Fin m, q.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m)))
            = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)) :=
    ⟨AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
        (fun b : ULift.{u} (Fin m) =>
          AffineSpace.coord S (ULift.up (Sum.inr b.down) : ULift.{u} (Fin n ⊕ Fin m))),
      AffineSpace.homOfVector_over _ _, fun b => AffineSpace.homOfVector_appTop_coord _ _ _⟩
  have mkHom : ∀ v : ULift.{u} (Fin n ⊕ Fin m) → Γ(AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S, ⊤),
      ∃ w : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S
            ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
        w ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
            = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) ∧
          ∀ i : ULift.{u} (Fin n ⊕ Fin m), w.appTop (AffineSpace.coord S i) = v i :=
    fun v => ⟨AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) v,
      AffineSpace.homOfVector_over _ _, fun i => AffineSpace.homOfVector_appTop_coord _ _ _⟩
  obtain ⟨σ, hσ, hσc⟩ := mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
    (fun a : Fin n => AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
    (fun b : Fin m =>
      AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))
        + pr₁.appTop (F b)) i.down)
  obtain ⟨σ', hσ', hσ'c⟩ := mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
    (fun a : Fin n => AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
    (fun b : Fin m =>
      AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))
        - pr₁.appTop (F b)) i.down)
  obtain ⟨τ, hτ, hτc⟩ := mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
    (fun a : Fin n =>
      AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))
        - pr₂.appTop (G a))
    (fun b : Fin m =>
      AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) i.down)
  obtain ⟨τ', hτ', hτ'c⟩ := mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
    (fun a : Fin n =>
      AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))
        + pr₂.appTop (G a))
    (fun b : Fin m =>
      AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) i.down)
  have hσinl : ∀ a : Fin n,
      σ.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)) :=
    fun a => hσc _
  have hσinr : ∀ b : Fin m,
      σ.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))
            + pr₁.appTop (F b) := fun b => hσc _
  have hσ'inl : ∀ a : Fin n,
      σ'.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)) :=
    fun a => hσ'c _
  have hσ'inr : ∀ b : Fin m,
      σ'.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))
            - pr₁.appTop (F b) := fun b => hσ'c _
  have hτinl : ∀ a : Fin n,
      τ.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))
            - pr₂.appTop (G a) := fun a => hτc _
  have hτinr : ∀ b : Fin m,
      τ.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)) :=
    fun b => hτc _
  have hτ'inl : ∀ a : Fin n,
      τ'.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))
            + pr₂.appTop (G a) := fun a => hτ'c _
  have hτ'inr : ∀ b : Fin m,
      τ'.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)) :=
    fun b => hτ'c _
  have hfix₁ : ∀ w : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S
        ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
      w ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
          = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) →
      (∀ a : Fin n,
        w.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
          = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))) →
      ∀ x : Γ(AffineSpace (ULift.{u} (Fin n)) S, ⊤),
        w.appTop (pr₁.appTop x) = pr₁.appTop x := by
    intro w hw hwc x
    have hcomp : w ≫ pr₁ = pr₁ := by
      refine AffineSpace.hom_ext ?_ ?_
      · rw [Category.assoc, hpr₁, hw]
      · rintro ⟨a⟩
        rw [comp_appTop_apply_consolidated116, hpr₁c a, hwc a]
    rw [← comp_appTop_apply_consolidated116, hcomp]
  have hfix₂ : ∀ w : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S
        ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
      w ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
          = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) →
      (∀ b : Fin m,
        w.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
          = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) →
      ∀ x : Γ(AffineSpace (ULift.{u} (Fin m)) S, ⊤),
        w.appTop (pr₂.appTop x) = pr₂.appTop x := by
    intro w hw hwc x
    have hcomp : w ≫ pr₂ = pr₂ := by
      refine AffineSpace.hom_ext ?_ ?_
      · rw [Category.assoc, hpr₂, hw]
      · rintro ⟨b⟩
        rw [comp_appTop_apply_consolidated116, hpr₂c b, hwc b]
    rw [← comp_appTop_apply_consolidated116, hcomp]
  have hσσ' : σ ≫ σ' = 𝟙 _ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hσ', hσ, Category.id_comp]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply_consolidated116, hσ'inl a, hσinl a, appTop_id_apply_consolidated116]
      · rw [comp_appTop_apply_consolidated116, hσ'inr b, appTop_sub_consolidated116, hσinr b,
          hfix₁ σ hσ hσinl (F b), appTop_id_apply_consolidated116]
        ring
  have hσ'σ : σ' ≫ σ = 𝟙 _ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hσ, hσ', Category.id_comp]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply_consolidated116, hσinl a, hσ'inl a, appTop_id_apply_consolidated116]
      · rw [comp_appTop_apply_consolidated116, hσinr b, appTop_add_consolidated116, hσ'inr b,
          hfix₁ σ' hσ' hσ'inl (F b), appTop_id_apply_consolidated116]
        ring
  have hττ' : τ ≫ τ' = 𝟙 _ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hτ', hτ, Category.id_comp]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply_consolidated116, hτ'inl a, appTop_add_consolidated116, hτinl a,
          hfix₂ τ hτ hτinr (G a), appTop_id_apply_consolidated116]
        ring
      · rw [comp_appTop_apply_consolidated116, hτ'inr b, hτinr b, appTop_id_apply_consolidated116]
  have hτ'τ : τ' ≫ τ = 𝟙 _ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hτ, hτ', Category.id_comp]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply_consolidated116, hτinl a, appTop_sub_consolidated116, hτ'inl a,
          hfix₂ τ' hτ' hτ'inr (G a), appTop_id_apply_consolidated116]
        ring
      · rw [comp_appTop_apply_consolidated116, hτinr b, hτ'inr b, appTop_id_apply_consolidated116]
  obtain ⟨D, hDover, hcoordEq⟩ :
      ∃ d : Y ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
        d ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) = p ∧
          ∀ i : ULift.{u} (Fin n ⊕ Fin m), d.appTop (AffineSpace.coord S i)
            = Sum.elim
                (fun a : Fin n =>
                  e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))))
                (fun b : Fin m =>
                  e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m)))) i.down :=
    ⟨AffineSpace.homOfVector p (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
        (fun a : Fin n => e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))))
        (fun b : Fin m => e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m))))
        i.down),
      AffineSpace.homOfVector_over _ _, fun i => AffineSpace.homOfVector_appTop_coord _ _ _⟩
  have hDinl : ∀ a : Fin n,
      D.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))) := fun a => hcoordEq _
  have hDinr : ∀ b : Fin m,
      D.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m))) := fun b => hcoordEq _
  have hLpr₁ : L ≫ pr₁ = e₁ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hpr₁, hLover, h₁]
    · rintro ⟨a⟩
      rw [comp_appTop_apply_consolidated116, hpr₁c a, hLinl a]
  have hLF : ∀ b : Fin m, L.appTop (pr₁.appTop (F b))
      = e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m))) := by
    intro b
    rw [← comp_appTop_apply_consolidated116, hLpr₁, hF b]
  have hDpr₂ : D ≫ pr₂ = e₂ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hpr₂, hDover, h₂]
    · rintro ⟨b⟩
      rw [comp_appTop_apply_consolidated116, hpr₂c b, hDinr b]
  have hcompG : ∀ a : Fin n, D.appTop (pr₂.appTop (G a))
      = e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))) := by
    intro a
    rw [← comp_appTop_apply_consolidated116, hDpr₂, hG a]
  have hA : L ≫ σ = D := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hσ, hLover, hDover]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply_consolidated116, hσinl a, hLinl a, hDinl a]
      · rw [comp_appTop_apply_consolidated116, hσinr b, appTop_add_consolidated116, hLinr b, hLF b, hDinr b, zero_add]
  have hB : D ≫ τ = R := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hτ, hDover, hRover]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply_consolidated116, hτinl a, appTop_sub_consolidated116, hDinl a, hcompG a, hRinl a, sub_self]
      · rw [comp_appTop_apply_consolidated116, hτinr b, hDinr b, hRinr b]
  refine ⟨⟨σ ≫ τ, τ' ≫ σ', ?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, ← Category.assoc τ τ' σ', hττ', Category.id_comp, hσσ']
  · rw [Category.assoc, ← Category.assoc σ' σ τ, hσ'σ, Category.id_comp, hτ'τ]
  · show (σ ≫ τ) ≫ _ = _
    rw [Category.assoc, hτ, hσ]
  · show L ≫ (σ ≫ τ) = R
    rw [← Category.assoc, hA, hB]

theorem closedEmbeddingsRelatedByAutomorphism : ClosedEmbeddingsRelatedByAutomorphism.{u} := by
  intro k hk Y hY p hp n m e₁ he₁ e₂ he₂ h₁ h₂
  have : IsAffine (affineSpaceIndexedBy k (ULift.{u} (Fin n))) := by
    unfold affineSpaceIndexedBy; infer_instance
  have : IsAffine (affineSpaceIndexedBy k (ULift.{u} (Fin m))) := by
    unfold affineSpaceIndexedBy; infer_instance
  choose F hF using fun b : Fin m =>
    (IsClosedImmersion.isAffine_surjective_of_isAffine e₁).2
      (e₂.appTop (AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up b : ULift.{u} (Fin m))))
  choose G hG using fun a : Fin n =>
    (IsClosedImmersion.isAffine_surjective_of_isAffine e₂).2
      (e₁.appTop (AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up a : ULift.{u} (Fin n))))
  exact exists_iso_affineSpace_sum_comp_eq_of_coord_consolidated116 n m p e₁ e₂ h₁ h₂ F hF G hG
    (AffineSpace.homOfVector p (coordVectorInl n m e₁))
    (AffineSpace.homOfVector p (coordVectorInr n m e₂))
    (AffineSpace.homOfVector_over _ _) (AffineSpace.homOfVector_over _ _)
    (fun a => AffineSpace.homOfVector_appTop_coord _ _ _)
    (fun b => AffineSpace.homOfVector_appTop_coord _ _ _)
    (fun a => AffineSpace.homOfVector_appTop_coord _ _ _)
    (fun b => AffineSpace.homOfVector_appTop_coord _ _ _)

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionCenters
section

open CategoryTheory.Limits


namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

private theorem comp_base_apply_consolidated127 {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (z : ↥A) :
    (a ≫ b).base z = b.base (a.base z) := by
  simp

private theorem hom_base_inv_base_apply_consolidated127 {A B : Scheme.{u}} (e : A ≅ B) (z : ↥B) :
    e.hom.base (e.inv.base z) = z := by
  rw [← comp_base_apply_consolidated127, e.inv_hom_id]
  simp

private theorem mem_support_comap_of_mem_support_consolidated127 {Z W : Scheme.{u}} (g : Z ⟶ W) (I : W.IdealSheafData)
    (z : ↥Z) (hz : g.base z ∈ I.support) : z ∈ (I.comap g).support := by
  rw [Scheme.IdealSheafData.support_comap]
  exact hz

theorem centersLieOver_smoothLocusComplement (d : LocalResolutionData k f s) :
    s.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X) := by
  intro i hi x hx
  obtain ⟨i₀, u, hu⟩ : ∃ (i₀ : d.cover.I₀) (u : ↥(d.cover.X i₀)),
      (d.cover.f i₀).base u = (s.projectionToBase i).base x := by
    obtain ⟨u, hu⟩ := d.cover.covers ((s.projectionToBase i).base x)
    exact ⟨d.cover.idx ((s.projectionToBase i).base x), u, hu⟩
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback u x hu
  have hw1' : (pullback.fst (d.cover.f i₀) (s.projectionToBase i)).base w = u := hw1
  have hw2' : (pullback.snd (d.cover.f i₀) (s.projectionToBase i)).base w = x := hw2
  have hws : w ∈ ((s.center i).comap (pullback.snd (d.cover.f i₀) (s.projectionToBase i))).support := by
    refine mem_support_comap_of_mem_support_consolidated127 _ _ _ ?_
    rw [hw2']
    exact hx
  obtain ⟨l, hl, hr⟩ := (d.exists_reindex_eq_iff_exists_mem_support i₀ i hi).2 ⟨w, hws⟩
  subst hr
  have ht : ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w) ∈ ((d.seq i₀).center l).support := by
    rw [d.localSequence_center_eq_comap i₀ l hl]
    refine mem_support_comap_of_mem_support_consolidated127 _ _ _ ?_
    rw [comp_base_apply_consolidated127, hom_base_inv_base_apply_consolidated127, hw2']
    exact hx
  have key : ((d.seq i₀).projectionToBase l).base ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w)
      = (pullback.fst (d.cover.f i₀) (s.projectionToBase (d.reindex i₀ l))).base w := by
    rw [← d.schemeAtIsoPullback_hom_fst i₀ l hl.le, comp_base_apply_consolidated127, hom_base_inv_base_apply_consolidated127]
  have hres := d.isResolution i₀
  unfold FunctorialResolution.EmbeddedResolution.IsStrongResolution at hres
  obtain ⟨-, -, -, -, hC, -⟩ := hres
  have hCt : ((d.seq i₀).projectionToBase l).base ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w) ∈
      ((smoothLocusComplement (d.cover.f i₀ ≫ f) : TopologicalSpace.Closeds ↥(d.cover.X i₀)) :
        Set ↥(d.cover.X i₀)) := hC l hl _ ht
  rw [← d.preimage_smoothLocusComplement_cover_map i₀] at hCt
  have hfin : (d.cover.f i₀).base
      (((d.seq i₀).projectionToBase l).base ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w)) ∈
      ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X) := hCt
  show (s.projectionToBase (d.reindex i₀ l)).base x ∈
    ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X)
  rw [← hu, ← hw1', ← key]
  exact hfin

end LocalResolutionData

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionDense
section

open CategoryTheory.Limits

section

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem dense_preimage_smoothLocus (d : LocalResolutionData k f s) :
    Dense ((s.lastStructMap ⁻¹ᵁ f.smoothLocus : TopologicalSpace.Opens ↥(s.lastObj)) : Set ↥(s.lastObj)) := by
  rw [dense_iff_inter_open]
  intro V hV hVne
  obtain ⟨x, hxV⟩ := hVne
  obtain ⟨i, y, hy⟩ := d.exists_chartToLastObj_eq x
  have hres := (d.isResolution i).2.2.2.1
  have hW : IsOpen (((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : TopologicalSpace.Opens ↥(s.lastObj)) :
      TopologicalSpace.Opens ↥((d.seq i).lastObj)) : Set ↥((d.seq i).lastObj)) :=
    ((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : TopologicalSpace.Opens ↥(s.lastObj))).2
  have hyW : y ∈ (((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : TopologicalSpace.Opens ↥(s.lastObj)) :
      TopologicalSpace.Opens ↥((d.seq i).lastObj)) : Set ↥((d.seq i).lastObj)) := by
    show (d.chartToLastObj i).base y ∈ V
    rw [hy]
    exact hxV
  obtain ⟨z, hz1, hz2⟩ := dense_iff_inter_open.mp hres _ hW ⟨y, hyW⟩
  refine ⟨(d.chartToLastObj i).base z, hz1, ?_⟩
  have hmem : ((d.seq i).lastStructMap).base z ∈ (d.cover.f i) ⁻¹ᵁ f.smoothLocus := by
    rw [d.preimage_smoothLocus_cover_map i]
    exact hz2
  have hbase : (s.lastStructMap).base ((d.chartToLastObj i).base z)
      = (d.cover.f i).base (((d.seq i).lastStructMap).base z) := by
    have h := congrArg (fun m : (d.seq i).lastObj ⟶ X => m.base z) (d.chartToLastObj_comp_lastStructMap i)
    simpa using h
  show (s.lastStructMap).base ((d.chartToLastObj i).base z) ∈ f.smoothLocus
  rw [hbase]
  exact hmem

end LocalResolutionData


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionProper
section

open CategoryTheory.Limits

section

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

def pullbackIsoLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    ((pullback s.lastStructMap (d.cover.f i) : Scheme.{u}) ≅ (d.seq i).lastObj) :=
  (pullbackSymmetry s.lastStructMap (d.cover.f i)).trans (d.lastObjIsoPullback i).symm

section
variable (d : LocalResolutionData k f s)
include d

theorem pullbackIsoLastObj_hom_lastStructMap (i : d.cover.I₀) :
    (d.pullbackIsoLastObj i).hom ≫ (d.seq i).lastStructMap = pullback.snd s.lastStructMap (d.cover.f i) := by
  rw [pullbackIsoLastObj]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← d.lastObjIsoPullback_hom_fst i, Iso.inv_hom_id_assoc]
  exact pullbackSymmetry_hom_comp_fst _ _

theorem isProper_lastStructMap : IsProper s.lastStructMap := by
  have key : ∀ i : d.cover.I₀, IsProper (d.seq i).lastStructMap := by
    intro i
    obtain ⟨-, h, -⟩ := d.isResolution i
    exact h
  obtain ⟨-, h2⟩ := (inferInstance :
    MorphismProperty.IsLocalAtTarget (@IsProper) Scheme.zariskiPrecoverage)
  refine h2 (R := d.cover.presieve₀) d.cover.mem₀ ?_
  intro U g _inst hg
  obtain ⟨i⟩ := hg
  rw [← d.pullbackIsoLastObj_hom_lastStructMap i]
  have := key i
  infer_instance


end

end LocalResolutionData


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionSmooth
section


section

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem chartToLastObj_comp_lastStructMap_assoc (d : LocalResolutionData k f s) (j : d.cover.I₀) :
    d.chartToLastObj j ≫ (s.lastStructMap ≫ f) = (d.seq j).lastStructMap ≫ (d.cover.f j ≫ f) := by
  rw [← Category.assoc, d.chartToLastObj_comp_lastStructMap j, Category.assoc]

section
variable {A B : Scheme.{u}} [IsAffine B] (g : A ⟶ B) (𝒲 : Scheme.OpenCover.{u, u} A) [∀ i, IsAffine (𝒲.X i)]

private theorem ringHom_smooth_appTop_of_smooth_consolidated125 (hg : Smooth g) (i : 𝒲.I₀) :
    RingHom.Smooth ((𝒲.f i ≫ g).appTop.hom) :=
  (AlgebraicGeometry.HasRingHomProperty.iff_of_source_openCover 𝒲).mp hg i

private theorem smooth_of_ringHom_smooth_appTop_consolidated125 (h : ∀ i : 𝒲.I₀, RingHom.Smooth ((𝒲.f i ≫ g).appTop.hom)) :
    Smooth g :=
  (AlgebraicGeometry.HasRingHomProperty.iff_of_source_openCover 𝒲).mpr h


end

section
variable (d : LocalResolutionData k f s) (j : d.cover.I₀)

private theorem smooth_chartToLastObj_comp_consolidated125 :
    Smooth (d.chartToLastObj j ≫ (s.lastStructMap ≫ f)) := by
  rw [d.chartToLastObj_comp_lastStructMap_assoc j]
  exact (d.isResolution j).1

private theorem smooth_appTop_affineCover_chartToLastObj_consolidated125 (a : ((d.seq j).lastObj.affineCover).I₀) :
    RingHom.Smooth (((((d.seq j).lastObj.affineCover).f a ≫ d.chartToLastObj j)
      ≫ (s.lastStructMap ≫ f)).appTop.hom) := by
  have h := ringHom_smooth_appTop_of_smooth_consolidated125 (d.chartToLastObj j ≫ (s.lastStructMap ≫ f))
    ((d.seq j).lastObj.affineCover) (smooth_chartToLastObj_comp_consolidated125 d j) a
  rw [Category.assoc]
  exact h


end

theorem smooth_lastStructMap_comp (d : LocalResolutionData k f s) :
    Smooth (s.lastStructMap ≫ f) := by
  have haffine : ∀ i : (d.lastObjCover.bind fun j => (d.lastObjCover.X j).affineCover).I₀,
      IsAffine
        ((d.lastObjCover.bind fun j => (d.lastObjCover.X j).affineCover).X i) := by
    rintro ⟨j, a⟩
    exact inferInstanceAs (IsAffine (((d.lastObjCover.X j).affineCover).X a))
  refine smooth_of_ringHom_smooth_appTop_consolidated125 (s.lastStructMap ≫ f)
    (d.lastObjCover.bind fun j => (d.lastObjCover.X j).affineCover) ?_
  rintro ⟨j, a⟩
  exact smooth_appTop_affineCover_chartToLastObj_consolidated125 d j a

end LocalResolutionData


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionStrictNormalCrossings
section

open CategoryTheory.Limits TopologicalSpace


namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

private theorem support_vanishingIdeal_eq_consolidated122 {Y : Scheme.{u}} (Z : Closeds ↥Y) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z := rfl

private theorem comap_vanishingIdeal_of_isOpenImmersion_consolidated122 {Y T : Scheme.{u}} (g : T ⟶ Y)
    [IsOpenImmersion g] (Z : Closeds ↥Y) (W : Closeds ↥T)
    (hW : (W : Set ↥T) = g.base ⁻¹' (Z : Set ↥Y)) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap g
      = Scheme.IdealSheafData.vanishingIdeal W := by
  have hrad : ((Scheme.IdealSheafData.vanishingIdeal Z).comap g).radical
      = (Scheme.IdealSheafData.vanishingIdeal Z).comap g := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    rw [Scheme.IdealSheafData.radical_ideal,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact ((PrimeSpectrum.isRadical_vanishingIdeal _).comap _).radical
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal Z).comap g).support = W := by
    rw [Scheme.IdealSheafData.support_comap, support_vanishingIdeal_eq_consolidated122]
    exact TopologicalSpace.Closeds.ext hW.symm
  rw [← hsupp, Scheme.IdealSheafData.vanishingIdeal_support, hrad]

section
variable {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (x : Fin n → R)

private theorem isRegularParameterSystem_map_ringEquiv_consolidated122 (h : IsRegularParameterSystem R n x) :
    IsRegularParameterSystem S n (fun i => e (x i)) := by
  unfold IsRegularParameterSystem at h ⊢
  obtain ⟨h1, h2⟩ := h
  constructor
  · have hmax : Ideal.comap (e : R →+* S) (IsLocalRing.maximalIdeal S)
        = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.comap_isMaximal_of_surjective (e : R →+* S) e.surjective)
    have hm : Ideal.map (e : R →+* S) (IsLocalRing.maximalIdeal R)
        = IsLocalRing.maximalIdeal S := by
      rw [← hmax]
      exact Ideal.map_comap_of_surjective (e : R →+* S) e.surjective _
    have himg : Ideal.span (Set.range fun i => e (x i))
        = Ideal.map (e : R →+* S) (Ideal.span (Set.range x)) := by
      rw [Ideal.map_span]
      congr 1
      ext b
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨x i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [himg, h1, hm]
  · rw [h2]
    exact ringKrullDim_eq_of_ringEquiv e

private theorem isRegularParameterSystem_of_ringEquiv_apply_eq_consolidated122 (y : Fin n → S)
    (hxy : ∀ i, e (x i) = y i) (h : IsRegularParameterSystem R n x) :
    IsRegularParameterSystem S n y := by
  have hy : y = fun i => e (x i) := (funext fun i => hxy i).symm
  subst hy
  exact isRegularParameterSystem_map_ringEquiv_consolidated122 e n x h


end

private theorem surjective_iso_inv_consolidated122 {A B : CommRingCat.{u}} (e : A ≅ B) :
    Function.Surjective (CommRingCat.Hom.hom e.inv) := by
  intro a
  refine ⟨(CommRingCat.Hom.hom e.hom) a, ?_⟩
  simp

private theorem map_eqToHom_germ_consolidated122 {T : Scheme.{u}} {U V : T.Opens}
    (h : Opposite.op U = Opposite.op V) (z : ↥T) (hz : z ∈ U) (hz' : z ∈ V) :
    T.presheaf.map (eqToHom h) ≫ T.presheaf.germ V z hz' = T.presheaf.germ U z hz := by
  have h' : U = V := congrArg Opposite.unop h
  subst h'
  simp

section
variable {Y T : Scheme.{u}} (g : T ⟶ Y) [IsOpenImmersion g] (U : T.Opens) (z : ↥T) (hz : z ∈ U) (hgz : g.base z ∈ (g ''ᵁ U : Y.Opens))

private theorem appIso_inv_germ_stalkMap_consolidated122 :
    (Scheme.Hom.appIso g U).inv ≫ Y.presheaf.germ (g ''ᵁ U) (g.base z) hgz ≫
        Scheme.Hom.stalkMap g z = T.presheaf.germ U z hz := by
  have h1 : Y.presheaf.germ (g ''ᵁ U) (g.base z) hgz ≫ Scheme.Hom.stalkMap g z
      = Scheme.Hom.app g (g ''ᵁ U) ≫ T.presheaf.germ (g ⁻¹ᵁ (g ''ᵁ U)) z hgz :=
    Scheme.Hom.germ_stalkMap g (g ''ᵁ U) z hgz
  rw [h1, ← Category.assoc]
  simp
  exact map_eqToHom_germ_consolidated122 _ z hz hgz

private theorem appIso_inv_germ_stalkMap_apply_consolidated122 (a : Γ(T, U)) :
    (ConcreteCategory.hom (Scheme.Hom.stalkMap g z))
        ((ConcreteCategory.hom (Y.presheaf.germ (g ''ᵁ U) (g.base z) hgz))
          ((ConcreteCategory.hom (Scheme.Hom.appIso g U).inv) a))
      = (ConcreteCategory.hom (T.presheaf.germ U z hz)) a := by
  have h := congrArg (fun m : Γ(T, U) ⟶ T.presheaf.stalk z => (ConcreteCategory.hom m) a)
    (appIso_inv_germ_stalkMap_consolidated122 g U z hz hgz)
  simpa only [CommRingCat.comp_apply] using h


end

section
variable (d : LocalResolutionData k f s) (i : d.cover.I₀) [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (d.cover.f i ≫ f)]

theorem chartToLastObj_preimage_smoothLocusComplement :
    (d.chartToLastObj i).base ⁻¹'
        (s.lastStructMap.base ⁻¹' ((smoothLocusComplement f : Closeds ↥X) : Set ↥X))
      = (d.seq i).lastStructMap.base ⁻¹'
        ((smoothLocusComplement (d.cover.f i ≫ f) : Closeds ↥(d.cover.X i)) : Set ↥(d.cover.X i)) := by
  have hcomp := d.chartToLastObj_comp_lastStructMap i
  have hsl := d.preimage_smoothLocusComplement_cover_map i
  ext x
  simp only [Set.mem_preimage]
  have hx : s.lastStructMap.base ((d.chartToLastObj i).base x)
      = (d.cover.f i).base ((d.seq i).lastStructMap.base x) := by
    have h := congrArg (fun g : (d.seq i).lastObj ⟶ X => g.base x) hcomp
    simpa using h
  rw [hx, ← Set.mem_preimage, hsl]

theorem comap_reducedInverseImage_chartToLastObj :
    (reducedInverseImage s.lastStructMap (smoothLocusComplement f)).comap (d.chartToLastObj i)
      = reducedInverseImage (d.seq i).lastStructMap (smoothLocusComplement (d.cover.f i ≫ f)) := by
  have h1 := d.chartToLastObj_preimage_smoothLocusComplement i
  unfold reducedInverseImage
  exact comap_vanishingIdeal_of_isOpenImmersion_consolidated122 (d.chartToLastObj i) _ _ h1.symm


end

private theorem isStrictNormalCrossingsDivisor_of_openCover_consolidated122 {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (H : ∀ y : ↥Y, ∃ (T : Scheme.{u}) (g : T ⟶ Y) (_ : IsOpenImmersion g) (z : ↥T),
      g.base z = y ∧ IsStrictNormalCrossingsDivisor (I.comap g)) : IsStrictNormalCrossingsDivisor I := by
  intro y
  obtain ⟨T, g, hg, z, hzy, hSNC⟩ := H y
  subst hzy
  have := hg
  obtain ⟨hreg, U, hzU, n, F, J, hpar, hid⟩ := hSNC z
  have : IsRegularLocalRing ↑(T.presheaf.stalk z) := hreg
  obtain ⟨E, hE⟩ : ∃ E : (↑(Y.presheaf.stalk (g.base z)) : Type u) ≃+* ↑(T.presheaf.stalk z),
      ∀ x, E x = (ConcreteCategory.hom (Scheme.Hom.stalkMap g z)) x :=
    ⟨(asIso (Scheme.Hom.stalkMap g z)).commRingCatIsoToRingEquiv, fun _ => rfl⟩
  have hgz : g.base z ∈ (g ''ᵁ (U : T.Opens) : Y.Opens) := ⟨z, hzU, rfl⟩
  have hVaff : IsAffineOpen (g ''ᵁ (U : T.Opens)) :=
    (U.2 : IsAffineOpen (U : T.Opens)).image_of_isOpenImmersion g
  have hsurj : Function.Surjective
      (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv) :=
    surjective_iso_inv_consolidated122 (Scheme.Hom.appIso g (U : T.Opens))
  refine ⟨IsRegularLocalRing.of_ringEquiv E.symm,
    ⟨g ''ᵁ (U : T.Opens), hVaff⟩, hgz, n,
    fun i => (ConcreteCategory.hom (Scheme.Hom.appIso g (U : T.Opens)).inv) (F i), J, ?_, ?_⟩
  · refine isRegularParameterSystem_of_ringEquiv_apply_eq_consolidated122 E.symm n _ _ ?_ hpar
    intro i
    have hgerm := appIso_inv_germ_stalkMap_apply_consolidated122 g (U : T.Opens) z hzU hgz (F i)
    rw [← hE] at hgerm
    rw [← hgerm, E.symm_apply_apply]
  · have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I g U
    rw [hid] at h1
    have h2 : Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv)
        (Ideal.span {∏ i ∈ J, F i})
        = Ideal.span {∏ i ∈ J,
            (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv) (F i)} := by
      rw [Ideal.map_span, Set.image_singleton, map_prod]
    have h3 : Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv)
        (Ideal.comap (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv)
          (I.ideal ⟨g ''ᵁ (U : T.Opens), hVaff⟩))
        = I.ideal ⟨g ''ᵁ (U : T.Opens), hVaff⟩ :=
      Ideal.map_comap_of_surjective _ hsurj _
    exact (h3.symm.trans
      (congrArg (Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv))
        h1.symm)).trans h2

theorem isStrictNormalCrossingsDivisor_reducedInverseImage (d : LocalResolutionData k f s) [LocallyOfFinitePresentation f] :
    IsStrictNormalCrossingsDivisor (reducedInverseImage s.lastStructMap (smoothLocusComplement f)) := by
  refine isStrictNormalCrossingsDivisor_of_openCover_consolidated122 _ ?_
  intro y
  obtain ⟨i, z, hz⟩ := d.exists_chartToLastObj_eq y
  refine ⟨(d.seq i).lastObj, d.chartToLastObj i, inferInstance, z, hz, ?_⟩
  rw [d.comap_reducedInverseImage_chartToLastObj i]
  exact (d.isResolution i).2.2.2.2.2

end LocalResolutionData

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SmoothLocusIsomorphism
section

open CategoryTheory.Limits

section

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

section
variable (d : LocalResolutionData k f s) (i : d.cover.I₀)

theorem isPullback_chartToLastObj :
    IsPullback (d.chartToLastObj i) ((d.seq i).lastStructMap) s.lastStructMap (d.cover.f i) := by
  have hsq : CommSq ((d.seq i).lastStructMap) (d.chartToLastObj i) (d.cover.f i) s.lastStructMap :=
    ⟨(d.chartToLastObj_comp_lastStructMap i).symm⟩
  have h : IsPullback ((d.seq i).lastStructMap) (d.chartToLastObj i) (d.cover.f i) s.lastStructMap :=
    IsPullback.of_iso_pullback hsq (d.lastObjIsoPullback i) (d.lastObjIsoPullback_hom_fst i)
      (d.chartToLastObj_eq i).symm
  exact h.flip

private theorem isIso_pullback_snd_restrict_smoothLocus_consolidated126 :
    IsIso (pullback.snd (s.lastStructMap ∣_ f.smoothLocus) (d.cover.f i ∣_ f.smoothLocus)) := by
  have hp := isPullback_morphismRestrict s.lastStructMap f.smoothLocus
  have hc := isPullback_morphismRestrict (d.cover.f i) f.smoothLocus
  have ht := isPullback_morphismRestrict ((d.seq i).lastStructMap) (d.cover.f i ⁻¹ᵁ f.smoothLocus)
  have hbig := ht.paste_vert (d.isPullback_chartToLastObj i).flip
  have hw : (((d.seq i).lastStructMap ∣_ (d.cover.f i ⁻¹ᵁ f.smoothLocus)) ≫
        (d.cover.f i ∣_ f.smoothLocus)) ≫ f.smoothLocus.ι
      = ((((d.seq i).lastStructMap ⁻¹ᵁ (d.cover.f i ⁻¹ᵁ f.smoothLocus)).ι) ≫ d.chartToLastObj i)
        ≫ s.lastStructMap := by
    rw [Category.assoc, hc.w]
    exact hbig.w
  have hsq : IsPullback ((d.seq i).lastStructMap ∣_ (d.cover.f i ⁻¹ᵁ f.smoothLocus))
      (hp.lift _ _ hw) (d.cover.f i ∣_ f.smoothLocus) (s.lastStructMap ∣_ f.smoothLocus) := by
    refine IsPullback.of_bot ?_ ?_ hp
    · rw [hp.lift_snd, hc.w]
      exact hbig
    · rw [hp.lift_fst]
  have hiso : IsIso ((d.seq i).lastStructMap ∣_ (d.cover.f i ⁻¹ᵁ f.smoothLocus)) := by
    rw [d.preimage_smoothLocus_cover_map i]
    exact (d.isResolution i).2.2.1
  have hcomp : IsIso (hsq.flip.isoPullback.hom ≫
      pullback.snd (s.lastStructMap ∣_ f.smoothLocus) (d.cover.f i ∣_ f.smoothLocus)) := by
    rw [hsq.flip.isoPullback_hom_snd]
    exact hiso
  exact IsIso.of_isIso_comp_left hsq.flip.isoPullback.hom
    (pullback.snd (s.lastStructMap ∣_ f.smoothLocus) (d.cover.f i ∣_ f.smoothLocus))


end

private theorem exists_restrict_smoothLocus_apply_eq_consolidated126 (d : LocalResolutionData k f s) :
    ∀ x : ↥(f.smoothLocus.toScheme), ∃ (i : d.cover.I₀)
      (y : ↥((d.cover.f i ⁻¹ᵁ f.smoothLocus).toScheme)),
        (d.cover.f i ∣_ f.smoothLocus) y = x := by
  intro x
  have hsup : (⨆ i, (d.cover.f i).opensRange) = ⊤ := d.cover.iSup_opensRange
  have hx : (x.1 : ↥X) ∈ (⨆ i, (d.cover.f i).opensRange : X.Opens) := by
    rw [hsup]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hi' : (x.1 : ↥X) ∈ Set.range (d.cover.f i).base := hi
  obtain ⟨y₀, hy₀⟩ := hi'
  have hmem : y₀ ∈ (d.cover.f i ⁻¹ᵁ f.smoothLocus) := by
    show (d.cover.f i).base y₀ ∈ f.smoothLocus
    rw [hy₀]
    exact x.2
  refine ⟨i, ⟨y₀, hmem⟩, ?_⟩
  have h2 := congrFun (morphismRestrict_base (d.cover.f i) f.smoothLocus) ⟨y₀, hmem⟩
  refine h2.trans (Subtype.ext ?_)
  exact hy₀

private def smoothLocusOpenCover_consolidated126 (d : LocalResolutionData k f s) :
    Scheme.OpenCover.{u, u} (f.smoothLocus.toScheme) :=
  Scheme.Cover.mkOfCovers d.cover.I₀
    (fun i => (d.cover.f i ⁻¹ᵁ f.smoothLocus).toScheme)
    (fun i => d.cover.f i ∣_ f.smoothLocus)
    (exists_restrict_smoothLocus_apply_eq_consolidated126 d)
    (fun i => show IsOpenImmersion (d.cover.f i ∣_ f.smoothLocus) from inferInstance)

theorem isIso_lastStructMap_restrict_smoothLocus (d : LocalResolutionData k f s) :
    IsIso (s.lastStructMap ∣_ f.smoothLocus) := by
  have hh : ∀ i : d.cover.I₀, MorphismProperty.isomorphisms Scheme.{u}
      (Scheme.Cover.pullbackHom (smoothLocusOpenCover_consolidated126 d) (s.lastStructMap ∣_ f.smoothLocus) i) := by
    intro i
    exact isIso_pullback_snd_restrict_smoothLocus_consolidated126 d i
  have key : MorphismProperty.isomorphisms Scheme.{u} (s.lastStructMap ∣_ f.smoothLocus) :=
    IsZariskiLocalAtTarget.of_openCover (smoothLocusOpenCover_consolidated126 d) hh
  exact key

end LocalResolutionData


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
section

open CategoryTheory.Limits

section

abbrev PrincipalizationAlgorithm : Type (u + 1) :=
  ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p]
    [QuasiCompact p]
    (I : X.IdealSheafData), NonzeroOnComponents I →
      ∀ E : List X.IdealSheafData, InStrictNormalCrossingPosition p E → IdealBlowupSequence p I E

abbrev specMapOfFieldHom (k K : Type u) [Field k] [Field K] (f : k →+* K) :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom f)

theorem specMapOfFieldHom_eq (k K : Type u) [Field k] [Field K] (f : k →+* K) :
    specMapOfFieldHom k K f = Spec.map (CommRingCat.ofHom f) := rfl

instance instSurjectiveSpecMapOfFieldHom (k K : Type u) [Field k] [Field K] (f : k →+* K) :
    Surjective (specMapOfFieldHom k K f) := by
  have hk : Subsingleton (PrimeSpectrum k) := by
    refine ⟨fun x y => ?_⟩
    have hx : x.asIdeal = ⊥ := x.asIdeal.eq_bot_or_top.resolve_right x.isPrime.ne_top
    have hy : y.asIdeal = ⊥ := y.asIdeal.eq_bot_or_top.resolve_right y.isPrime.ne_top
    exact PrimeSpectrum.ext (hx.trans hy.symm)
  obtain ⟨x⟩ : Nonempty (PrimeSpectrum K) := inferInstance
  refine ⟨fun y => ⟨x, ?_⟩⟩
  exact Subsingleton.elim (α := PrimeSpectrum k) _ _

instance instFlatSpecMapOfFieldHom (k K : Type u) [Field k] [Field K] (f : k →+* K) :
    Flat (specMapOfFieldHom k K f) := by
  show Flat (Spec.map (CommRingCat.ofHom f))
  let _inst : Algebra k K := f.toAlgebra
  have hflat : Module.Flat k K := inferInstance
  have hf : RingHom.Flat (CommRingCat.ofHom f).hom := hflat
  exact HasRingHomProperty.Spec_iff.mpr hf

structure IsFunctorialPrincipalization (A : PrincipalizationAlgorithm.{u}) : Prop where
  pushforward :
    ∀ (k : Type u) [Field k] [CharZero k] (S X : Scheme.{u})
      (pS : S ⟶ Spec (CommRingCat.of k)) (p : X ⟶ Spec (CommRingCat.of k))
      [Smooth pS] [LocallyOfFiniteType pS]
      [QuasiCompact pS]
      [Smooth p] [LocallyOfFiniteType p]
      [QuasiCompact p]
      (j : S ⟶ X) [IsClosedImmersion j] (_ : j ≫ p = pS)
      (c : ℕ) (_ : 1 ≤ c) (_ : HasEtaleCoordCodim p j c)
      (I : S.IdealSheafData) (hI : NonzeroOnComponents I)
      (hIX : NonzeroOnComponents (imageIdealSheaf j I))
      (hES : InStrictNormalCrossingPosition pS ([] : List S.IdealSheafData))
      (hEX : InStrictNormalCrossingPosition p ([] : List X.IdealSheafData)),
      IsPushforwardBlowupSeq j (A k S pS I hI [] hES).toSequenceOfBlowups
        (A k X p (imageIdealSheaf j I) hIX [] hEX).toSequenceOfBlowups
  base_change :
    ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k))
      [Smooth p] [LocallyOfFiniteType p]
      [QuasiCompact p]
      (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
      (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
      (K : Type u) [Field K] [CharZero K] (f : k →+* K)
      [Smooth (pullback.snd p (specMapOfFieldHom k K f))]
      [LocallyOfFiniteType (pullback.snd p (specMapOfFieldHom k K f))]
      [QuasiCompact (pullback.snd p (specMapOfFieldHom k K f))]
      (hI' : NonzeroOnComponents (I.comap (pullback.fst p (specMapOfFieldHom k K f))))
      (hE' : InStrictNormalCrossingPosition (pullback.snd p (specMapOfFieldHom k K f))
        (E.map fun D => D.comap (pullback.fst p (specMapOfFieldHom k K f)))),
      IsPullbackBlowupSequence (pullback.fst p (specMapOfFieldHom k K f))
        (A K (pullback p (specMapOfFieldHom k K f)) (pullback.snd p (specMapOfFieldHom k K f))
          (I.comap (pullback.fst p (specMapOfFieldHom k K f))) hI'
          (E.map fun D => D.comap (pullback.fst p (specMapOfFieldHom k K f))) hE').toSequenceOfBlowups
        (A k X p I hI E hE).toSequenceOfBlowups
  base_change_strict :
    ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k))
      [Smooth p] [LocallyOfFiniteType p]
      [QuasiCompact p]
      (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
      (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
      (K : Type u) [Field K] [CharZero K] (f : k →+* K)
      [Smooth (pullback.snd p (specMapOfFieldHom k K f))]
      [LocallyOfFiniteType (pullback.snd p (specMapOfFieldHom k K f))]
      [QuasiCompact (pullback.snd p (specMapOfFieldHom k K f))]
      (hI' : NonzeroOnComponents (I.comap (pullback.fst p (specMapOfFieldHom k K f))))
      (hE' : InStrictNormalCrossingPosition (pullback.snd p (specMapOfFieldHom k K f))
        (E.map fun D => D.comap (pullback.fst p (specMapOfFieldHom k K f)))),
      IsStrictPullbackBlowupSeq (pullback.fst p (specMapOfFieldHom k K f))
        (A K (pullback p (specMapOfFieldHom k K f)) (pullback.snd p (specMapOfFieldHom k K f))
          (I.comap (pullback.fst p (specMapOfFieldHom k K f))) hI'
          (E.map fun D => D.comap (pullback.fst p (specMapOfFieldHom k K f))) hE').toSequenceOfBlowups
        (A k X p I hI E hE).toSequenceOfBlowups
  lastIdeal_eq_top :
    ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k))
      [Smooth p] [LocallyOfFiniteType p]
      [QuasiCompact p]
      (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
      (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E),
      (A k X p I hI E hE).lastIdeal = ⊤
  smooth_pullback :
    ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k))
      [Smooth p] [LocallyOfFiniteType p]
      [QuasiCompact p]
      (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
      (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
      (X' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k))
      [Smooth p'] [LocallyOfFiniteType p']
      [QuasiCompact p']
      (φ : X' ⟶ X) [Smooth φ] (_ : φ ≫ p = p')
      (hI' : NonzeroOnComponents (I.comap φ))
      (hE' : InStrictNormalCrossingPosition p' (E.map fun D => D.comap φ)),
      IsPullbackBlowupSequence φ
        (A k X' p' (I.comap φ) hI' (E.map fun D => D.comap φ) hE').toSequenceOfBlowups
        (A k X p I hI E hE).toSequenceOfBlowups
  smooth_pullback_strict :
    ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k))
      [Smooth p] [LocallyOfFiniteType p]
      [QuasiCompact p]
      (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
      (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
      (X' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k))
      [Smooth p'] [LocallyOfFiniteType p']
      [QuasiCompact p']
      (φ : X' ⟶ X) [Smooth φ] [AlgebraicGeometry.Surjective φ]
      (_ : φ ≫ p = p')
      (hI' : NonzeroOnComponents (I.comap φ))
      (hE' : InStrictNormalCrossingPosition p' (E.map fun D => D.comap φ)),
      IsStrictPullbackBlowupSeq φ
        (A k X' p' (I.comap φ) hI' (E.map fun D => D.comap φ) hE').toSequenceOfBlowups
        (A k X p I hI E hE).toSequenceOfBlowups

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
section

open CategoryTheory.Limits TopologicalSpace Opposite

section

structure AffineSpacePrincipalizationData (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [IsAffine Y] (pY : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType pY] : Type (u + 1) where
  princ : PrincipalizationAlgorithm.{u}
  dim : ℕ
  emb : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin dim))
  emb_closedImmersion : IsClosedImmersion emb
  emb_nonzeroOnComponents : NonzeroOnComponents (Scheme.Hom.ker emb)
  emb_comp : emb ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin dim)) = pY
  ambient_smooth : Smooth (affineSpaceIndexedByToSpec k (ULift.{u} (Fin dim)))
  ambient_snc : InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k (ULift.{u} (Fin dim)))
      ([] : List (affineSpaceIndexedBy k (ULift.{u} (Fin dim))).IdealSheafData)

namespace AffineSpacePrincipalizationData

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)

abbrev ambient : Scheme.{u} := affineSpaceIndexedBy k (ULift.{u} (Fin S.dim))

abbrev ambientToSpec : S.ambient ⟶ Spec (CommRingCat.of k) :=
  affineSpaceIndexedByToSpec k (ULift.{u} (Fin S.dim))

def principalizationSequence : IdealBlowupSequence S.ambientToSpec (Scheme.Hom.ker S.emb)
    ([] : List S.ambient.IdealSheafData) :=
  haveI := S.ambient_smooth
  S.princ k S.ambient S.ambientToSpec (Scheme.Hom.ker S.emb) S.emb_nonzeroOnComponents []
    S.ambient_snc

def ambientBlowups : SequenceOfBlowups S.ambient := S.principalizationSequence.toSequenceOfBlowups

abbrev ambientLength : ℕ := S.ambientBlowups.length

abbrev ambientLevel (i : ℕ) : Scheme.{u} := S.ambientBlowups.schemeAt i

abbrev ambientBlowupMorphism (i : ℕ) : S.ambientLevel (i + 1) ⟶ S.ambientLevel i := S.ambientBlowups.transitionMapSucc i

abbrev ambientCenter (i : ℕ) : (S.ambientLevel i).IdealSheafData := S.ambientBlowups.center i

def strictTransformIdeal (i : ℕ) : (S.ambientLevel i).IdealSheafData :=
  Nat.rec (motive := fun j => (S.ambientLevel j).IdealSheafData)
    (Scheme.Hom.ker (S.emb ≫ S.ambientBlowups.isoZero.inv))
    (fun j ih => Blowup.strictTransform (S.ambientBlowupMorphism j) (S.ambientCenter j) ih) i

@[simp] theorem strictTransformIdeal_zero :
    S.strictTransformIdeal 0 = Scheme.Hom.ker (S.emb ≫ S.ambientBlowups.isoZero.inv) := rfl

@[simp] theorem strictTransformIdeal_succ (i : ℕ) :
    S.strictTransformIdeal (i + 1) =
      Blowup.strictTransform (S.ambientBlowupMorphism i) (S.ambientCenter i) (S.strictTransformIdeal i) := rfl

abbrev strictTransform (i : ℕ) : Scheme.{u} := (S.strictTransformIdeal i).subscheme

abbrev strictTransformι (i : ℕ) : S.strictTransform i ⟶ S.ambientLevel i := (S.strictTransformIdeal i).subschemeι

section
variable (i : ℕ)

theorem noetherianSpace_strictTransform [TopologicalSpace.NoetherianSpace ↥(S.ambientLevel i)] :
    TopologicalSpace.NoetherianSpace ↥(S.strictTransform i) :=
  Blowup.noetherianSpace_subscheme (S.strictTransformIdeal i)

theorem exists_strictTransformMap :
    ∃ f : S.strictTransform (i + 1) ⟶ S.strictTransform i,
      f ≫ S.strictTransformι i = S.strictTransformι (i + 1) ≫ S.ambientBlowupMorphism i := by
  have hle : S.strictTransformIdeal i ≤ (S.strictTransformIdeal (i + 1)).map (S.ambientBlowupMorphism i) := by
    refine le_trans (Scheme.IdealSheafData.le_map_comap (S.strictTransformIdeal i) (S.ambientBlowupMorphism i)) ?_
    exact Scheme.IdealSheafData.map_mono (S.ambientBlowupMorphism i)
      (Blowup.comap_le_strictTransform (S.ambientBlowupMorphism i) (S.ambientCenter i) (S.strictTransformIdeal i))
  exact ⟨(S.strictTransformIdeal (i + 1)).subschemeMap (S.strictTransformIdeal i) (S.ambientBlowupMorphism i) hle,
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ hle⟩


end

def strictTransformMap (i : ℕ) : S.strictTransform (i + 1) ⟶ S.strictTransform i := (S.exists_strictTransformMap i).choose

theorem strictTransformMap_comp_strictTransformι (i : ℕ) :
    S.strictTransformMap i ≫ S.strictTransformι i = S.strictTransformι (i + 1) ≫ S.ambientBlowupMorphism i :=
  (S.exists_strictTransformMap i).choose_spec

def discardedComponents (i : ℕ) : Set (Set ↥(S.strictTransform i)) :=
  {C | C ∈ irreducibleComponents ↥(S.strictTransform i) ∧
    (S.strictTransformι i).base '' C ⊆ ((S.ambientCenter i).support : Set ↥(S.ambientLevel i))}

theorem mem_discardedComponents_iff (i : ℕ) (C : Set ↥(S.strictTransform i)) :
    C ∈ S.discardedComponents i ↔
      C ∈ irreducibleComponents ↥(S.strictTransform i) ∧
        (S.strictTransformι i).base '' C ⊆ ((S.ambientCenter i).support : Set ↥(S.ambientLevel i)) := Iff.rfl

def discardedLocus (i : ℕ) : Set ↥(S.strictTransform i) := ⋃₀ (S.discardedComponents i)

section
variable (i : ℕ)

theorem discardedLocus_eq_sUnion_discardedComponents : S.discardedLocus i = ⋃₀ (S.discardedComponents i) := rfl

theorem isClosed_discardedLocus [TopologicalSpace.NoetherianSpace ↥(S.strictTransform i)] :
    IsClosed (S.discardedLocus i) := by
  have hfin : (irreducibleComponents ↥(S.strictTransform i)).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hsub : S.discardedComponents i ⊆ irreducibleComponents ↥(S.strictTransform i) := fun C hC =>
    ((S.mem_discardedComponents_iff i C).mp hC).1
  have hfin' : (S.discardedComponents i).Finite := Set.Finite.subset hfin hsub
  show IsClosed (⋃₀ (S.discardedComponents i))
  rw [Set.sUnion_eq_biUnion]
  exact Set.Finite.isClosed_biUnion hfin'
    (fun C hC => isClosed_of_mem_irreducibleComponents C (hsub hC))


end

def discardedLocusClosure (i : ℕ) : TopologicalSpace.Closeds ↥(S.strictTransform i) :=
  ⟨closure (S.discardedLocus i), isClosed_closure⟩

theorem coe_discardedLocusClosure (i : ℕ)
    [TopologicalSpace.NoetherianSpace ↥(S.strictTransform i)] :
    (S.discardedLocusClosure i : Set ↥(S.strictTransform i)) = S.discardedLocus i := by
  show closure (S.discardedLocus i) = S.discardedLocus i
  exact (S.isClosed_discardedLocus i).closure_eq

def discardedIdeal (i : ℕ) : (S.strictTransform i).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (S.discardedLocusClosure i)

theorem discardedIdeal_eq_vanishingIdeal (i : ℕ) :
    S.discardedIdeal i = Scheme.IdealSheafData.vanishingIdeal (S.discardedLocusClosure i) := rfl

abbrev discardedSubscheme (i : ℕ) : Scheme.{u} := (S.discardedIdeal i).subscheme

abbrev discardedι (i : ℕ) : S.discardedSubscheme i ⟶ S.strictTransform i := (S.discardedIdeal i).subschemeι

def discardedLocusClosureCompl (i : ℕ) : (S.strictTransform i).Opens := (S.discardedLocusClosure i).compl

theorem coe_discardedLocusClosureCompl (i : ℕ) :
    ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) =
      (S.discardedLocusClosure i : Set ↥(S.strictTransform i))ᶜ := rfl

def comapAmbientCenter (i : ℕ) : (S.strictTransform i).IdealSheafData :=
  (S.ambientCenter i).comap (S.strictTransformι i)

theorem comapAmbientCenter_eq (i : ℕ) :
    S.comapAmbientCenter i = (S.ambientCenter i).comap (S.strictTransformι i) := rfl

def centerOffDetached (i : ℕ) : (S.strictTransform i).IdealSheafData :=
  Scheme.Hom.ker
    (((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι ≫ (S.discardedLocusClosureCompl i).ι)

theorem centerOffDetached_eq (i : ℕ) :
    S.centerOffDetached i =
      Scheme.Hom.ker
        (((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι ≫
          (S.discardedLocusClosureCompl i).ι) := rfl

def discardedUnion (i : ℕ) : Scheme.{u} :=
  Nat.rec (motive := fun _ => Scheme.{u}) (⊥_ Scheme.{u})
    (fun j ih => ih ⨿ S.discardedSubscheme j) i

abbrev totalSpace (i : ℕ) : Scheme.{u} := S.strictTransform i ⨿ S.discardedUnion i

def transitionMap (i : ℕ) : S.totalSpace (i + 1) ⟶ S.totalSpace i :=
  coprod.desc (S.strictTransformMap i ≫ coprod.inl)
    (coprod.desc (coprod.inr : S.discardedUnion i ⟶ S.totalSpace i)
        (S.discardedι i ≫ coprod.inl) :
      S.discardedUnion i ⨿ S.discardedSubscheme i ⟶ S.totalSpace i)

theorem inl_comp_transitionMap (i : ℕ) :
    (coprod.inl : S.strictTransform (i + 1) ⟶ S.totalSpace (i + 1)) ≫ S.transitionMap i =
      S.strictTransformMap i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) := by
  exact coprod.inl_desc _ _

def centerOnTotalSpace (i : ℕ) : (S.totalSpace i).IdealSheafData :=
  Scheme.Hom.ker
    ((S.centerOffDetached i).subschemeι ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i))

theorem centerOnTotalSpace_eq_ker (i : ℕ) :
    S.centerOnTotalSpace i =
      Scheme.Hom.ker
        ((S.centerOffDetached i).subschemeι ≫
          (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) := rfl

private theorem exists_coprodInitialIso_inl_comp_eq_subschemeι_consolidated144 {Z W : Scheme.{u}} (I : Z.IdealSheafData)
    (g : W ⟶ Z) (e0 : W ≅ I.subscheme) (he0 : e0.hom ≫ I.subschemeι = g) :
    ∃ e : (I.subscheme ⨿ (⊥_ Scheme.{u})) ≅ W,
      (coprod.inl : I.subscheme ⟶ I.subscheme ⨿ (⊥_ Scheme.{u})) ≫ e.hom ≫ g =
        I.subschemeι := by
  refine ⟨(coprod.rightUnitor I.subscheme).trans e0.symm, ?_⟩
  have hunit : (coprod.inl : I.subscheme ⟶ I.subscheme ⨿ (⊥_ Scheme.{u})) ≫
      (coprod.rightUnitor I.subscheme).hom = 𝟙 I.subscheme := coprod.inl_desc _ _
  have h1 : (coprod.inl : I.subscheme ⟶ I.subscheme ⨿ (⊥_ Scheme.{u})) ≫
      ((coprod.rightUnitor I.subscheme).trans e0.symm).hom = e0.inv := by
    rw [Iso.trans_hom, ← Category.assoc, hunit, Category.id_comp, Iso.symm_hom]
  rw [← Category.assoc, h1, ← he0, ← Category.assoc, e0.inv_hom_id, Category.id_comp]

private theorem exists_iso_ker_subscheme_consolidated144 {W V : Scheme.{u}} (f : W ⟶ V)
    [IsClosedImmersion f] :
    ∃ e : W ≅ (Scheme.Hom.ker f).subscheme,
      e.hom ≫ (Scheme.Hom.ker f).subschemeι = f := by
  have hci2 : IsClosedImmersion (Scheme.Hom.ker f).subschemeι := inferInstance
  have hk : Scheme.Hom.ker (Scheme.Hom.ker f).subschemeι = Scheme.Hom.ker f :=
    Scheme.IdealSheafData.ker_subschemeι _
  have hα : AlgebraicGeometry.IsClosedImmersion.lift (Scheme.Hom.ker f).subschemeι f
      (le_of_eq hk) ≫ (Scheme.Hom.ker f).subschemeι = f :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
  have hβ : AlgebraicGeometry.IsClosedImmersion.lift f (Scheme.Hom.ker f).subschemeι
      (le_of_eq hk.symm) ≫ f = (Scheme.Hom.ker f).subschemeι :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
  have hm1 : CategoryTheory.Mono f := inferInstance
  have hm2 : CategoryTheory.Mono (Scheme.Hom.ker f).subschemeι := inferInstance
  refine ⟨⟨AlgebraicGeometry.IsClosedImmersion.lift (Scheme.Hom.ker f).subschemeι f (le_of_eq hk),
      AlgebraicGeometry.IsClosedImmersion.lift f (Scheme.Hom.ker f).subschemeι (le_of_eq hk.symm),
      ?_, ?_⟩, hα⟩
  · rw [← cancel_mono f, Category.assoc, hβ, hα, Category.id_comp]
  · rw [← cancel_mono (Scheme.Hom.ker f).subschemeι, Category.assoc, hα, hβ, Category.id_comp]

theorem exists_totalSpaceZeroIso :
    ∃ e : S.totalSpace 0 ≅ Y,
      (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ e.hom ≫
          (S.emb ≫ S.ambientBlowups.isoZero.inv) = S.strictTransformι 0 := by
  have := S.emb_closedImmersion
  have hci : IsClosedImmersion (S.emb ≫ S.ambientBlowups.isoZero.inv) :=
    inferInstance
  obtain ⟨e0, he0⟩ := exists_iso_ker_subscheme_consolidated144 (S.emb ≫ S.ambientBlowups.isoZero.inv)
  exact exists_coprodInitialIso_inl_comp_eq_subschemeι_consolidated144 (Scheme.Hom.ker (S.emb ≫ S.ambientBlowups.isoZero.inv))
    (S.emb ≫ S.ambientBlowups.isoZero.inv) e0 he0

def totalSpaceZeroIso : S.totalSpace 0 ≅ Y := S.exists_totalSpaceZeroIso.choose

theorem totalSpaceZeroIso_spec :
    (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom ≫
        (S.emb ≫ S.ambientBlowups.isoZero.inv) = S.strictTransformι 0 :=
  S.exists_totalSpaceZeroIso.choose_spec

def tower : ℕᵒᵖ ⥤ Scheme.{u} :=
  (Functor.ofSequence (fun i => (S.transitionMap i).op)).leftOp

theorem tower_map_succ (i : ℕ) :
    S.tower.map (homOfLE (Nat.le_succ i)).op = S.transitionMap i := by
  show ((Functor.ofSequence fun j => (S.transitionMap j).op).map (homOfLE (Nat.le_succ i))).unop
      = S.transitionMap i
  rw [Functor.ofSequence_map_homOfLE_succ]
  rfl

def TransitionsAreBlowups : Prop :=
  ∀ i, i < S.ambientLength → Blowup.IsBlowupAlongIdealSheaf (S.tower.map (homOfLE (Nat.le_succ i)).op) (S.centerOnTotalSpace i)

def blowupSequence (h : S.TransitionsAreBlowups) : SequenceOfBlowups Y where
  length := S.ambientLength
  tower := S.tower
  isoZero := S.totalSpaceZeroIso
  center := S.centerOnTotalSpace
  isBlowup := h

def blowupSequenceWithoutIsos (h : S.TransitionsAreBlowups) : SequenceOfBlowups Y := (S.blowupSequence h).withoutIsoBlowups

end AffineSpacePrincipalizationData

def AffineSpacePrincipalizationData.ofAffine (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) [IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY] :
    AffineSpacePrincipalizationData k Y pY where
  princ := A
  dim := (hemb k Y pY).choose
  emb := (hemb k Y pY).choose_spec.choose
  emb_closedImmersion := (hemb k Y pY).choose_spec.choose_spec.1
  emb_nonzeroOnComponents := (hemb k Y pY).choose_spec.choose_spec.2.1
  emb_comp := (hemb k Y pY).choose_spec.choose_spec.2.2
  ambient_smooth := hsm k ((hemb k Y pY).choose)
  ambient_snc := hsnc k ((hemb k Y pY).choose)

def EmbeddedPrincipalizationYieldsBlowups (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).TransitionsAreBlowups

def affineResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (h : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm) : AffineResolutionRule.{u} := by
  intro k _ _ Y pY _ _ _ _
  exact (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).blowupSequenceWithoutIsos (h k Y pY)


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
section

open CategoryTheory.Limits TopologicalSpace Opposite

section

structure EmbeddedBlowupSequence (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [IsAffine Y] (pY : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType pY] : Type (u + 1) where
  ambient : Scheme.{u}
  ambientStruct : ambient ⟶ Spec (CommRingCat.of k)
  isAffine_ambient : IsAffine ambient
  smooth_ambientStruct : Smooth ambientStruct
  locallyOfFiniteType_ambientStruct : LocallyOfFiniteType ambientStruct
  quasiCompact_ambientStruct : QuasiCompact ambientStruct
  emb : Y ⟶ ambient
  isClosedImmersion_emb : IsClosedImmersion emb
  emb_comp : emb ≫ ambientStruct = pY
  ambientSeq : SequenceOfBlowups ambient

namespace EmbeddedBlowupSequence

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]

instance instIsAffineAmbient (T : EmbeddedBlowupSequence k Y pY) :
    IsAffine T.ambient := T.isAffine_ambient

instance instSmoothAmbientStruct (T : EmbeddedBlowupSequence k Y pY) :
    Smooth T.ambientStruct := T.smooth_ambientStruct

instance instLocallyOfFiniteTypeAmbientStruct (T : EmbeddedBlowupSequence k Y pY) :
    LocallyOfFiniteType T.ambientStruct :=
  T.locallyOfFiniteType_ambientStruct

instance instQuasiCompactAmbientStruct (T : EmbeddedBlowupSequence k Y pY) :
    QuasiCompact T.ambientStruct := T.quasiCompact_ambientStruct

instance instIsClosedImmersionEmb (T : EmbeddedBlowupSequence k Y pY) :
    IsClosedImmersion T.emb := T.isClosedImmersion_emb

variable (T : EmbeddedBlowupSequence k Y pY)

abbrev length : ℕ := T.ambientSeq.length

abbrev schemeAt (i : ℕ) : Scheme.{u} := T.ambientSeq.schemeAt i

abbrev blowdown (i : ℕ) : T.schemeAt (i + 1) ⟶ T.schemeAt i := T.ambientSeq.transitionMapSucc i

abbrev ambientCenter (i : ℕ) : (T.schemeAt i).IdealSheafData := T.ambientSeq.center i

def strictTransformIdeal (i : ℕ) : (T.schemeAt i).IdealSheafData :=
  Nat.rec (motive := fun j => (T.schemeAt j).IdealSheafData)
    (Scheme.Hom.ker (T.emb ≫ T.ambientSeq.isoZero.inv))
    (fun j ih => Blowup.strictTransform (T.blowdown j) (T.ambientCenter j) ih) i

@[simp] theorem strictTransformIdeal_zero :
    T.strictTransformIdeal 0 = Scheme.Hom.ker (T.emb ≫ T.ambientSeq.isoZero.inv) := rfl

@[simp] theorem strictTransformIdeal_succ (i : ℕ) :
    T.strictTransformIdeal (i + 1) =
      Blowup.strictTransform (T.blowdown i) (T.ambientCenter i) (T.strictTransformIdeal i) := rfl

abbrev strictTransform (i : ℕ) : Scheme.{u} := (T.strictTransformIdeal i).subscheme

abbrev strictTransformι (i : ℕ) : T.strictTransform i ⟶ T.schemeAt i := (T.strictTransformIdeal i).subschemeι

section
variable (i : ℕ)

theorem comap_strictTransformIdeal_le :
    (T.strictTransformIdeal i).comap (T.blowdown i) ≤ T.strictTransformIdeal (i + 1) :=
  Blowup.comap_le_strictTransform _ _ _

theorem exists_strictTransformMap :
    ∃ f : T.strictTransform (i + 1) ⟶ T.strictTransform i,
      f ≫ T.strictTransformι i = T.strictTransformι (i + 1) ≫ T.blowdown i := by
  have hle : T.strictTransformIdeal i ≤ (T.strictTransformIdeal (i + 1)).map (T.blowdown i) :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr (T.comap_strictTransformIdeal_le i)
  exact ⟨(T.strictTransformIdeal (i + 1)).subschemeMap (T.strictTransformIdeal i) (T.blowdown i) hle,
    Scheme.IdealSheafData.subschemeMap_subschemeι (T.strictTransformIdeal (i + 1)) (T.strictTransformIdeal i)
      (T.blowdown i) hle⟩


end

def strictTransformMap (i : ℕ) : T.strictTransform (i + 1) ⟶ T.strictTransform i := (T.exists_strictTransformMap i).choose

theorem strictTransformMap_comp_strictTransformι (i : ℕ) :
    T.strictTransformMap i ≫ T.strictTransformι i = T.strictTransformι (i + 1) ≫ T.blowdown i :=
  (T.exists_strictTransformMap i).choose_spec

def detachedComponents (i : ℕ) : Set (Set ↥(T.strictTransform i)) :=
  {C | C ∈ irreducibleComponents ↥(T.strictTransform i) ∧
    (T.strictTransformι i).base '' C ⊆ ((T.ambientCenter i).support : Set ↥(T.schemeAt i))}

theorem mem_detachedComponents (i : ℕ) (C : Set ↥(T.strictTransform i)) :
    C ∈ T.detachedComponents i ↔
      C ∈ irreducibleComponents ↥(T.strictTransform i) ∧
        (T.strictTransformι i).base '' C ⊆ ((T.ambientCenter i).support : Set ↥(T.schemeAt i)) := Iff.rfl

def detachedLocus (i : ℕ) : Set ↥(T.strictTransform i) := ⋃₀ (T.detachedComponents i)

section
variable (i : ℕ)

theorem detachedLocus_eq_sUnion : T.detachedLocus i = ⋃₀ (T.detachedComponents i) := rfl

theorem isClosed_detachedLocus [TopologicalSpace.NoetherianSpace ↥(T.strictTransform i)] :
    IsClosed (T.detachedLocus i) := by
  have hfinComp : (irreducibleComponents ↥(T.strictTransform i)).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hsub : T.detachedComponents i ⊆ irreducibleComponents ↥(T.strictTransform i) :=
    fun C hC => ((T.mem_detachedComponents i C).mp hC).1
  have hfin : (T.detachedComponents i).Finite := hfinComp.subset hsub
  rw [T.detachedLocus_eq_sUnion i, Set.sUnion_eq_biUnion]
  exact hfin.isClosed_biUnion fun C hC => isClosed_of_mem_irreducibleComponents _ (hsub hC)


end

def detachedClosure (i : ℕ) : TopologicalSpace.Closeds ↥(T.strictTransform i) :=
  ⟨closure (T.detachedLocus i), isClosed_closure⟩

theorem detachedClosure_coe (i : ℕ)
    [TopologicalSpace.NoetherianSpace ↥(T.strictTransform i)] :
    (T.detachedClosure i : Set ↥(T.strictTransform i)) = T.detachedLocus i := by
  show closure (T.detachedLocus i) = T.detachedLocus i
  exact (T.isClosed_detachedLocus i).closure_eq

def detachedIdeal (i : ℕ) : (T.strictTransform i).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (T.detachedClosure i)

theorem detachedIdeal_eq (i : ℕ) :
    T.detachedIdeal i = Scheme.IdealSheafData.vanishingIdeal (T.detachedClosure i) := rfl

abbrev detachedScheme (i : ℕ) : Scheme.{u} := (T.detachedIdeal i).subscheme

abbrev detachedι (i : ℕ) : T.detachedScheme i ⟶ T.strictTransform i := (T.detachedIdeal i).subschemeι

def detachedClosureCompl (i : ℕ) : (T.strictTransform i).Opens := (T.detachedClosure i).compl

theorem detachedClosureCompl_coe (i : ℕ) :
    ((T.detachedClosureCompl i : (T.strictTransform i).Opens) : Set ↥(T.strictTransform i)) =
      (T.detachedClosure i : Set ↥(T.strictTransform i))ᶜ := rfl

def comapAmbientCenter (i : ℕ) : (T.strictTransform i).IdealSheafData :=
  (T.ambientCenter i).comap (T.strictTransformι i)

theorem comapAmbientCenter_eq (i : ℕ) :
    T.comapAmbientCenter i = (T.ambientCenter i).comap (T.strictTransformι i) := rfl

def centerOffDetached (i : ℕ) : (T.strictTransform i).IdealSheafData :=
  Scheme.Hom.ker
    (((T.comapAmbientCenter i).comap (T.detachedClosureCompl i).ι).subschemeι ≫ (T.detachedClosureCompl i).ι)

theorem centerOffDetached_eq (i : ℕ) :
    T.centerOffDetached i =
      Scheme.Hom.ker
        (((T.comapAmbientCenter i).comap (T.detachedClosureCompl i).ι).subschemeι ≫
          (T.detachedClosureCompl i).ι) := rfl

def detachedCoprod (i : ℕ) : Scheme.{u} :=
  Nat.rec (motive := fun _ => Scheme.{u}) (⊥_ Scheme.{u})
    (fun j ih => ih ⨿ T.detachedScheme j) i

@[simp] theorem detachedCoprod_zero : T.detachedCoprod 0 = ⊥_ Scheme.{u} := rfl

@[simp] theorem detachedCoprod_succ (i : ℕ) :
    T.detachedCoprod (i + 1) = (T.detachedCoprod i ⨿ T.detachedScheme i) := rfl

abbrev totalSpace (i : ℕ) : Scheme.{u} := T.strictTransform i ⨿ T.detachedCoprod i

def totalTransition (i : ℕ) : T.totalSpace (i + 1) ⟶ T.totalSpace i :=
  coprod.desc (T.strictTransformMap i ≫ coprod.inl)
    (coprod.desc (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i)
        (T.detachedι i ≫ coprod.inl) :
      T.detachedCoprod i ⨿ T.detachedScheme i ⟶ T.totalSpace i)

section
variable (i : ℕ)

theorem inl_totalTransition_eq_strictTransformMap_inl :
    (coprod.inl : T.strictTransform (i + 1) ⟶ T.totalSpace (i + 1)) ≫ T.totalTransition i =
      T.strictTransformMap i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i) := by
  exact coprod.inl_desc (T.strictTransformMap i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i))
    (coprod.desc (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i)
      (T.detachedι i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i)) :
      T.detachedCoprod i ⨿ T.detachedScheme i ⟶ T.totalSpace i)

theorem inl_inr_totalTransition :
    (coprod.inl : T.detachedCoprod i ⟶ T.detachedCoprod (i + 1)) ≫
        (coprod.inr : T.detachedCoprod (i + 1) ⟶ T.totalSpace (i + 1)) ≫ T.totalTransition i =
      (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i) := by
  have h : (coprod.inr : T.detachedCoprod (i + 1) ⟶ T.totalSpace (i + 1)) ≫ T.totalTransition i =
      (coprod.desc (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i)
          (T.detachedι i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i)) :
        T.detachedCoprod i ⨿ T.detachedScheme i ⟶ T.totalSpace i) :=
    coprod.inr_desc _ _
  exact Eq.trans
    (congrArg
      (fun f : T.detachedCoprod (i + 1) ⟶ T.totalSpace i =>
        (coprod.inl : T.detachedCoprod i ⟶ T.detachedCoprod (i + 1)) ≫ f) h)
    (coprod.inl_desc (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i)
      (T.detachedι i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i)))

theorem inr_inr_totalTransition :
    (coprod.inr : T.detachedScheme i ⟶ T.detachedCoprod (i + 1)) ≫
        (coprod.inr : T.detachedCoprod (i + 1) ⟶ T.totalSpace (i + 1)) ≫ T.totalTransition i =
      T.detachedι i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i) := by
  have h1 : (coprod.inr : T.detachedCoprod (i + 1) ⟶ T.totalSpace (i + 1)) ≫ T.totalTransition i =
      (coprod.desc (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i)
          (T.detachedι i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i)) :
        T.detachedCoprod i ⨿ T.detachedScheme i ⟶ T.totalSpace i) :=
    coprod.inr_desc _ _
  have h2 : (coprod.inr : T.detachedScheme i ⟶ T.detachedCoprod i ⨿ T.detachedScheme i) ≫
      (coprod.desc (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i)
          (T.detachedι i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i)) :
        T.detachedCoprod i ⨿ T.detachedScheme i ⟶ T.totalSpace i) =
      T.detachedι i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i) :=
    coprod.inr_desc _ _
  exact Eq.trans
    (congrArg
      (fun f : T.detachedCoprod (i + 1) ⟶ T.totalSpace i =>
        (coprod.inr : T.detachedScheme i ⟶ T.detachedCoprod (i + 1)) ≫ f) h1)
    h2


end

def totalCenter (i : ℕ) : (T.totalSpace i).IdealSheafData :=
  Scheme.Hom.ker
    ((T.centerOffDetached i).subschemeι ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i))

theorem totalCenter_eq (i : ℕ) :
    T.totalCenter i =
      Scheme.Hom.ker
        ((T.centerOffDetached i).subschemeι ≫
          (coprod.inl : T.strictTransform i ⟶ T.totalSpace i)) := rfl

private theorem exists_kerSubschemeIso_of_isClosedImmersion_consolidated164 {X Z : Scheme.{u}} (g : Z ⟶ X)
    [IsClosedImmersion g] :
    ∃ u : (Scheme.Hom.ker g).subscheme ≅ Z, u.hom ≫ g = (Scheme.Hom.ker g).subschemeι :=
  ⟨(asIso g.toImage).symm, by
    rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]⟩

private theorem exists_coprodIso_of_isInitial_consolidated164 {A B Z : Scheme.{u}}
    (hB : IsInitial B) (u : A ≅ Z) :
    ∃ e : (A ⨿ B) ≅ Z, (coprod.inl : A ⟶ A ⨿ B) ≫ e.hom = u.hom := by
  refine ⟨⟨coprod.desc u.hom (hB.to Z), u.inv ≫ coprod.inl, ?_, ?_⟩, coprod.inl_desc _ _⟩
  · refine coprod.hom_ext ?_ ?_
    · calc (coprod.inl : A ⟶ A ⨿ B) ≫ (coprod.desc u.hom (hB.to Z) ≫ (u.inv ≫ coprod.inl))
          = ((coprod.inl : A ⟶ A ⨿ B) ≫ coprod.desc u.hom (hB.to Z)) ≫
              (u.inv ≫ (coprod.inl : A ⟶ A ⨿ B)) := (Category.assoc _ _ _).symm
        _ = u.hom ≫ (u.inv ≫ (coprod.inl : A ⟶ A ⨿ B)) :=
            congrArg (fun t => t ≫ (u.inv ≫ (coprod.inl : A ⟶ A ⨿ B))) (coprod.inl_desc _ _)
        _ = (u.hom ≫ u.inv) ≫ (coprod.inl : A ⟶ A ⨿ B) := (Category.assoc _ _ _).symm
        _ = 𝟙 A ≫ (coprod.inl : A ⟶ A ⨿ B) :=
            congrArg (fun t => t ≫ (coprod.inl : A ⟶ A ⨿ B)) u.hom_inv_id
        _ = (coprod.inl : A ⟶ A ⨿ B) := Category.id_comp _
        _ = (coprod.inl : A ⟶ A ⨿ B) ≫ 𝟙 (A ⨿ B) := (Category.comp_id _).symm
    · exact hB.hom_ext _ _
  · calc (u.inv ≫ (coprod.inl : A ⟶ A ⨿ B)) ≫ coprod.desc u.hom (hB.to Z)
        = u.inv ≫ ((coprod.inl : A ⟶ A ⨿ B) ≫ coprod.desc u.hom (hB.to Z)) :=
          Category.assoc _ _ _
      _ = u.inv ≫ u.hom := congrArg (fun t => u.inv ≫ t) (coprod.inl_desc _ _)
      _ = 𝟙 Z := u.inv_hom_id

theorem exists_totalSpaceZeroIso :
    ∃ e : T.totalSpace 0 ≅ Y,
      (coprod.inl : T.strictTransform 0 ⟶ T.totalSpace 0) ≫ e.hom ≫
          (T.emb ≫ T.ambientSeq.isoZero.inv) = T.strictTransformι 0 := by
  have : IsClosedImmersion (T.emb ≫ T.ambientSeq.isoZero.inv) := inferInstance
  obtain ⟨u, hu⟩ := exists_kerSubschemeIso_of_isClosedImmersion_consolidated164
    (T.emb ≫ T.ambientSeq.isoZero.inv)
  have hB : IsInitial (T.detachedCoprod 0) := initialIsInitial
  obtain ⟨e, he⟩ :=
    exists_coprodIso_of_isInitial_consolidated164 (A := T.strictTransform 0) (B := T.detachedCoprod 0) (Z := Y) hB u
  refine ⟨e, ?_⟩
  refine Eq.trans ?_ hu
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun t => t ≫ (T.emb ≫ T.ambientSeq.isoZero.inv)) he

def totalSpaceZeroIso : T.totalSpace 0 ≅ Y := T.exists_totalSpaceZeroIso.choose

theorem totalSpaceZeroIso_spec :
    (coprod.inl : T.strictTransform 0 ⟶ T.totalSpace 0) ≫ T.totalSpaceZeroIso.hom ≫
        (T.emb ≫ T.ambientSeq.isoZero.inv) = T.strictTransformι 0 :=
  T.exists_totalSpaceZeroIso.choose_spec

def totalTower : ℕᵒᵖ ⥤ Scheme.{u} :=
  (Functor.ofSequence (fun i => (T.totalTransition i).op)).leftOp



theorem totalTower_map_succ (i : ℕ) :
    T.totalTower.map (homOfLE (Nat.le_succ i)).op = T.totalTransition i := by
  show ((Functor.ofSequence (fun j => (T.totalTransition j).op)).map
      (homOfLE (Nat.le_succ i))).unop = T.totalTransition i
  rw [Functor.ofSequence_map_homOfLE_succ]
  rfl

def TransitionsAreBlowups : Prop :=
  ∀ i, i < T.length → Blowup.IsBlowupAlongIdealSheaf (T.totalTower.map (homOfLE (Nat.le_succ i)).op) (T.totalCenter i)

def inducedBlowups (h : T.TransitionsAreBlowups) : SequenceOfBlowups Y where
  length := T.length
  tower := T.totalTower
  isoZero := T.totalSpaceZeroIso
  center := T.totalCenter
  isBlowup := h

section
variable (h : T.TransitionsAreBlowups)

@[simp] theorem inducedBlowups_length : (T.inducedBlowups h).length = T.length := rfl

@[simp] theorem inducedBlowups_tower : (T.inducedBlowups h).tower = T.totalTower := rfl



@[simp] theorem inducedBlowups_center (i : ℕ) :
    (T.inducedBlowups h).center i = T.totalCenter i := rfl


end

def inducedBlowupsWithoutIso (h : T.TransitionsAreBlowups) : SequenceOfBlowups Y := (T.inducedBlowups h).withoutIsoBlowups

end EmbeddedBlowupSequence

section
variable (k : Type u) [Field k] (n : ℕ)

private theorem locallyOfFiniteType_affineSpaceIndexedByToSpec_ulift_consolidated164 :
    LocallyOfFiniteType (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n))) := by
  unfold affineSpaceIndexedByToSpec
  infer_instance

private theorem quasiCompact_affineSpaceIndexedByToSpec_ulift_consolidated164 :
    QuasiCompact (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n))) := by
  unfold affineSpaceIndexedByToSpec
  infer_instance


end

namespace AffineSpacePrincipalizationData

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]

def toEmbeddedBlowupSequence (S : AffineSpacePrincipalizationData k Y pY) : EmbeddedBlowupSequence k Y pY where
  ambient := S.ambient
  ambientStruct := S.ambientToSpec
  isAffine_ambient := inferInstance
  smooth_ambientStruct := S.ambient_smooth
  locallyOfFiniteType_ambientStruct := locallyOfFiniteType_affineSpaceIndexedByToSpec_ulift_consolidated164 k S.dim
  quasiCompact_ambientStruct := quasiCompact_affineSpaceIndexedByToSpec_ulift_consolidated164 k S.dim
  emb := S.emb
  isClosedImmersion_emb := S.emb_closedImmersion
  emb_comp := S.emb_comp
  ambientSeq := S.ambientBlowups










section
variable (S : AffineSpacePrincipalizationData k Y pY)

theorem toEmbeddedBlowupSequence_schemeAt (i : ℕ) :
    S.toEmbeddedBlowupSequence.schemeAt i = S.ambientLevel i := rfl




theorem toEmbeddedBlowupSequence_transitionsAreBlowups_iff :
    S.toEmbeddedBlowupSequence.TransitionsAreBlowups ↔ S.TransitionsAreBlowups := Iff.rfl

theorem embeddedInducedBlowups_eq (h : S.TransitionsAreBlowups) :
    S.toEmbeddedBlowupSequence.inducedBlowups ((toEmbeddedBlowupSequence_transitionsAreBlowups_iff S).mpr h) = S.blowupSequence h := rfl

theorem embeddedInducedBlowupsWithoutIso_eq (h : S.TransitionsAreBlowups) :
    S.toEmbeddedBlowupSequence.inducedBlowupsWithoutIso ((toEmbeddedBlowupSequence_transitionsAreBlowups_iff S).mpr h) = S.blowupSequenceWithoutIsos h := by
  show (S.toEmbeddedBlowupSequence.inducedBlowups ((toEmbeddedBlowupSequence_transitionsAreBlowups_iff S).mpr h)).withoutIsoBlowups
      = (S.blowupSequence h).withoutIsoBlowups
  exact congrArg SequenceOfBlowups.withoutIsoBlowups (embeddedInducedBlowups_eq S h)


end

end AffineSpacePrincipalizationData

namespace EmbeddingDatum

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]

def toEmbeddedBlowupSequence (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) : EmbeddedBlowupSequence k Y pY where
  ambient := D.ambient
  ambientStruct := D.ambientStruct
  isAffine_ambient := D.isAffine_ambient
  smooth_ambientStruct := D.smooth_ambientStruct
  locallyOfFiniteType_ambientStruct := D.locallyOfFiniteType_ambientStruct
  quasiCompact_ambientStruct := D.quasiCompact_ambientStruct
  emb := D.emb
  isClosedImmersion_emb := D.isClosedImmersion_emb
  emb_comp := D.comp_eq
  ambientSeq :=
    (A k D.ambient D.ambientStruct (Scheme.Hom.ker D.emb) D.nonzeroOnComponents_ker
      ([] : List D.ambient.IdealSheafData) D.sncEmpty).toSequenceOfBlowups







theorem ambientBlowups_eq_toSequenceOfBlowups (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) :
    (D.toEmbeddedBlowupSequence A).ambientSeq =
      (A k D.ambient D.ambientStruct (Scheme.Hom.ker D.emb) D.nonzeroOnComponents_ker
        ([] : List D.ambient.IdealSheafData) D.sncEmpty).toSequenceOfBlowups := rfl

end EmbeddingDatum

def TransitionsAreBlowupsForEmbeddings (A : PrincipalizationAlgorithm.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y] (D : EmbeddingDatum k Y pY),
    (D.toEmbeddedBlowupSequence A).TransitionsAreBlowups

def embeddedResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u}) (h : TransitionsAreBlowupsForEmbeddings A) : EmbeddedResolutionRule.{u} := by
  intro k _ _ Y pY _ _ _ _ D
  exact (D.toEmbeddedBlowupSequence A).inducedBlowupsWithoutIso (h k Y pY D)

theorem embeddedResolutionRuleOfPrincipalization_apply (A : PrincipalizationAlgorithm.{u}) (h : TransitionsAreBlowupsForEmbeddings A)
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y] (D : EmbeddingDatum k Y pY) :
    embeddedResolutionRuleOfPrincipalization A h k Y pY D = (D.toEmbeddedBlowupSequence A).inducedBlowupsWithoutIso (h k Y pY D) := rfl

def affineSpaceEmbeddingDatum (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) [IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY] :
    EmbeddingDatum k Y pY where
  ambient := affineSpaceIndexedBy k (ULift.{u} (Fin (hemb k Y pY).choose))
  ambientStruct := affineSpaceIndexedByToSpec k (ULift.{u} (Fin (hemb k Y pY).choose))
  emb := (hemb k Y pY).choose_spec.choose
  isAffine_ambient := inferInstance
  smooth_ambientStruct := hsm k ((hemb k Y pY).choose)
  locallyOfFiniteType_ambientStruct :=
    locallyOfFiniteType_affineSpaceIndexedByToSpec_ulift_consolidated164 k ((hemb k Y pY).choose)
  quasiCompact_ambientStruct :=
    quasiCompact_affineSpaceIndexedByToSpec_ulift_consolidated164 k ((hemb k Y pY).choose)
  isClosedImmersion_emb := (hemb k Y pY).choose_spec.choose_spec.1
  nonzeroOnComponents_ker := (hemb k Y pY).choose_spec.choose_spec.2.1
  comp_eq := (hemb k Y pY).choose_spec.choose_spec.2.2
  sncEmpty := hsnc k ((hemb k Y pY).choose)

theorem affineSpaceEmbeddingDatum_toEmbeddedBlowupSequence (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) [IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY] :
    (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A =
      (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence := rfl

def affineSpaceEmbeddingChoice (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    EmbeddingChoice.{u} := by
  intro k _ _ Y pY _ _ _ _
  exact affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY

theorem affineSpaceEmbeddingChoice_eq_affineSpaceEmbeddingDatum (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y] :
    affineSpaceEmbeddingChoice hemb hsnc hsm k Y pY = affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY := rfl

theorem embeddedResolutionRuleOfPrincipalization_affineSpaceEmbeddingDatum (A : PrincipalizationAlgorithm.{u}) (h : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hw : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm)
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y] :
    embeddedResolutionRuleOfPrincipalization A h k Y pY (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) =
      affineResolutionRuleOfPrincipalization A hemb hsnc hsm hw k Y pY := by
  have hT := affineSpaceEmbeddingDatum_toEmbeddedBlowupSequence A hemb hsnc hsm k Y pY
  have key : ∀ (T₁ T₂ : EmbeddedBlowupSequence k Y pY), T₁ = T₂ →
      ∀ (h₁ : T₁.TransitionsAreBlowups) (h₂ : T₂.TransitionsAreBlowups),
        T₁.inducedBlowupsWithoutIso h₁ = T₂.inducedBlowupsWithoutIso h₂ := by
    rintro T₁ T₂ rfl h₁ h₂
    rfl
  calc embeddedResolutionRuleOfPrincipalization A h k Y pY (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY)
      = ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A).inducedBlowupsWithoutIso
          (h k Y pY (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY)) :=
        embeddedResolutionRuleOfPrincipalization_apply A h k Y pY (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY)
    _ = ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence).inducedBlowupsWithoutIso
          ((AffineSpacePrincipalizationData.toEmbeddedBlowupSequence_transitionsAreBlowups_iff
            (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)).mpr (hw k Y pY)) :=
        key _ _ hT _ _
    _ = (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).blowupSequenceWithoutIsos (hw k Y pY) :=
        AffineSpacePrincipalizationData.embeddedInducedBlowupsWithoutIso_eq (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)
          (hw k Y pY)
    _ = affineResolutionRuleOfPrincipalization A hemb hsnc hsm hw k Y pY := rfl


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRuleOfPrincipalization
section


section

def NilIsStrictNormalCrossingsOfSmooth : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u})
    (q : A ⟶ Spec (CommRingCat.of k)), Smooth q → InStrictNormalCrossingPosition q []

theorem nilIsStrictNormalCrossingsOfSmooth : NilIsStrictNormalCrossingsOfSmooth.{u} := by
  intro k _ _ A q hq
  have : Smooth q := hq
  exact inStrictNormalCrossingPosition_nil q

section
variable (A : PrincipalizationAlgorithm.{u}) (h : TransitionsAreBlowupsForEmbeddings A)

theorem hasProperCenters_embeddedResolutionRuleOfPrincipalization :
    (embeddedResolutionRuleOfPrincipalization A h).HasProperCenters := by
  intro k _ _ Y p _ _ _ _ D i hi
  have hi' : i < ((D.toEmbeddedBlowupSequence A).inducedBlowups (h k Y p D)).withoutIsoBlowups.length := hi
  exact SequenceOfBlowups.withoutIsoBlowups_center_ne_top _ hi'

theorem toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hw : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm) :
    (embeddedResolutionRuleOfPrincipalization A h).toAffineResolutionRule (affineSpaceEmbeddingChoice hemb hsnc hsm) =
      affineResolutionRuleOfPrincipalization A hemb hsnc hsm hw := by
  funext k _ _ Y p _ _ _ _
  rw [EmbeddedResolutionRule.toAffineResolutionRule_apply, affineSpaceEmbeddingChoice_eq_affineSpaceEmbeddingDatum]
  exact embeddedResolutionRuleOfPrincipalization_affineSpaceEmbeddingDatum A h hemb hsnc hsm hw k Y p


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceLinearEmbeddings
section


section

theorem nonzeroOnComponents_of_support_ne_univ {X : Scheme.{u}} [IrreducibleSpace ↥X]
    (I : X.IdealSheafData) (h : (↑I.support : Set ↥X) ≠ Set.univ) :
    NonzeroOnComponents I := by
  intro T hT hsub
  have huniv : IsIrreducible (Set.univ : Set ↥X) := IrreducibleSpace.isIrreducible_univ ↥X
  have hle : (Set.univ : Set ↥X) ⊆ T := hT.2 huniv (Set.subset_univ T)
  exact h (Set.univ_subset_iff.mp (hle.trans hsub))

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

private theorem base_injective_of_isClosedImmersion_consolidated264 : Function.Injective ⇑f.base :=
  (Scheme.Hom.isClosedEmbedding f).injective

private theorem isClosed_range_of_isClosedImmersion_consolidated264 : IsClosed (Set.range ⇑f.base) :=
  (Scheme.Hom.isClosedEmbedding f).isClosed_range

private theorem support_ker_eq_range_of_isClosedImmersion_consolidated264 :
    ((Scheme.Hom.ker f).support : Set ↥Y) = Set.range ⇑f.base := by
  have hcl := (isClosed_range_of_isClosedImmersion_consolidated264 f).closure_eq
  simp [Scheme.Hom.support_ker, hcl]


end

theorem nonzeroOnComponents_ker_comp {Y A A' : Scheme.{u}} (j : Y ⟶ A) (i : A ⟶ A')
    [IsClosedImmersion j] [IsClosedImmersion i] [IrreducibleSpace ↥A']
    (h : NonzeroOnComponents (Scheme.Hom.ker j)) :
    NonzeroOnComponents (Scheme.Hom.ker (j ≫ i)) := by
  refine nonzeroOnComponents_of_support_ne_univ _ ?_
  rw [support_ker_eq_range_of_isClosedImmersion_consolidated264 (j ≫ i)]
  intro hrange
  have hsurj : ∀ z : ↥A', ∃ y : ↥Y, (j ≫ i).base y = z := by
    intro z
    have hz : z ∈ Set.range ⇑(j ≫ i).base := by
      rw [hrange]
      exact Set.mem_univ z
    exact Set.mem_range.mp hz
  obtain ⟨a'⟩ : Nonempty ↥A' := inferInstance
  obtain ⟨y, -⟩ := hsurj a'
  have hjsurj : ∀ b : ↥A, ∃ y' : ↥Y, j.base y' = b := by
    intro b
    obtain ⟨y', hy'⟩ := hsurj (i.base b)
    refine ⟨y', base_injective_of_isClosedImmersion_consolidated264 i ?_⟩
    simpa using hy'
  refine h (irreducibleComponent (j.base y))
    (irreducibleComponent_mem_irreducibleComponents _) ?_
  rw [support_ker_eq_range_of_isClosedImmersion_consolidated264 j]
  intro b _
  exact Set.mem_range.mpr (hjsurj b)

private theorem appTop_comp_apply_eq_consolidated264 {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (x : ↑(Z.presheaf.obj (Opposite.op ⊤))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (a ≫ b))) x
      = (ConcreteCategory.hom (Scheme.Hom.appTop a))
          ((ConcreteCategory.hom (Scheme.Hom.appTop b)) x) := by
  have h : Scheme.Hom.appTop (a ≫ b) = Scheme.Hom.appTop b ≫ Scheme.Hom.appTop a := by
    simp
  rw [h]
  rfl

theorem isClosedImmersion_of_coord_surjective {R : CommRingCat.{u}} {N M : Type u}
    (f : AffineSpace N (Spec R) ⟶ AffineSpace M (Spec R))
    (hover : f ≫ (AffineSpace M (Spec R) ↘ Spec R) = (AffineSpace N (Spec R) ↘ Spec R))
    (hcoord : ∀ i : N, ∃ s : ↑((AffineSpace M (Spec R)).presheaf.obj (Opposite.op ⊤)),
      (ConcreteCategory.hom (Scheme.Hom.appTop f)) s = AffineSpace.coord (Spec R) i) :
    IsClosedImmersion f := by
  choose s hs using hcoord
  have hgcoord : ∀ i : N,
      (ConcreteCategory.hom (Scheme.Hom.appTop
        (AffineSpace.homOfVector (AffineSpace M (Spec R) ↘ Spec R) s)))
        (AffineSpace.coord (Spec R) i) = s i := by
    intro i
    simp [AffineSpace.homOfVector_appTop_coord]
  have key : f ≫ AffineSpace.homOfVector (AffineSpace M (Spec R) ↘ Spec R) s
      = 𝟙 (AffineSpace N (Spec R)) := by
    apply AffineSpace.hom_ext
    · simp [hover]
    · intro i
      rw [appTop_comp_apply_eq_consolidated264, hgcoord i, hs i]
      simp
  have hsurj : Function.Surjective (ConcreteCategory.hom (Scheme.Hom.appTop f)) := by
    intro x
    refine ⟨(ConcreteCategory.hom (Scheme.Hom.appTop
      (AffineSpace.homOfVector (AffineSpace M (Spec R) ↘ Spec R) s))) x, ?_⟩
    have h : (ConcreteCategory.hom (Scheme.Hom.appTop
          (f ≫ AffineSpace.homOfVector (AffineSpace M (Spec R) ↘ Spec R) s))) x
        = (ConcreteCategory.hom (Scheme.Hom.appTop (𝟙 (AffineSpace N (Spec R))))) x := by
      rw [key]
    rw [appTop_comp_apply_eq_consolidated264] at h
    simpa using h
  exact IsClosedImmersion.of_surjective_of_isAffine f hsurj

def affineSpaceInl (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)) ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n ⊕ Fin m)) :=
  AffineSpace.homOfVector (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)))
    (coordVectorInl n m (𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)))))

def affineSpaceInrEmbedding (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)) ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n ⊕ Fin m)) :=
  AffineSpace.homOfVector (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)))
    (coordVectorInr n m (𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)))))

@[simp]
theorem affineSpaceInl_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceInl k n m ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)) =
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) := by
  simp [affineSpaceInl]

@[simp]
theorem affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceInrEmbedding k n m ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)) =
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) := by
  simp [affineSpaceInrEmbedding]

private theorem pullbackCoord_id_consolidated264 {k : Type u} [Field k] {N : Type u} (j : N) :
    pullbackCoord (𝟙 (affineSpaceIndexedBy k N)) j
      = AffineSpace.coord (Spec (CommRingCat.of k)) j := by
  simp

section
variable (k : Type u) [Field k] (n m : ℕ)

theorem pullbackCoord_affineSpaceInl (i : ULift.{u, 0} (Fin n ⊕ Fin m)) :
    pullbackCoord (affineSpaceInl k n m) i =
      Sum.elim (fun a : Fin n =>
          AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a))
        (fun _ : Fin m => 0) i.down := by
  have h : pullbackCoord (affineSpaceInl k n m) i
      = coordVectorInl n m (𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)))) i := by
    simp only [pullbackCoord_def, affineSpaceInl, AffineSpace.homOfVector_appTop_coord]
  rw [h]
  obtain ⟨j⟩ := i
  cases j with
  | inl a =>
      show pullbackCoord (𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)))) (ULift.up.{u, 0} a)
          = AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a)
      exact pullbackCoord_id_consolidated264 _
  | inr _ => rfl

theorem pullbackCoord_affineSpaceInl_inl (a : Fin n) :
    pullbackCoord (affineSpaceInl k n m) (ULift.up.{u, 0} (Sum.inl a)) =
      AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a) :=
  pullbackCoord_affineSpaceInl k n m (ULift.up.{u, 0} (Sum.inl a))

theorem pullbackCoord_affineSpaceInl_inr (b : Fin m) :
    pullbackCoord (affineSpaceInl k n m) (ULift.up.{u, 0} (Sum.inr b)) = 0 :=
  pullbackCoord_affineSpaceInl k n m (ULift.up.{u, 0} (Sum.inr b))

theorem pullbackCoord_affineSpaceInrEmbedding (i : ULift.{u, 0} (Fin n ⊕ Fin m)) :
    pullbackCoord (affineSpaceInrEmbedding k n m) i =
      Sum.elim (fun _ : Fin n => 0)
        (fun b : Fin m =>
          AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} b)) i.down := by
  have h : pullbackCoord (affineSpaceInrEmbedding k n m) i
      = coordVectorInr n m (𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)))) i := by
    simp only [pullbackCoord_def, affineSpaceInrEmbedding, AffineSpace.homOfVector_appTop_coord]
  rw [h]
  obtain ⟨j⟩ := i
  cases j with
  | inl _ => rfl
  | inr b =>
      show pullbackCoord (𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)))) (ULift.up.{u, 0} b)
          = AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} b)
      exact pullbackCoord_id_consolidated264 _

theorem pullbackCoord_affineSpaceInrEmbedding_inl (a : Fin n) :
    pullbackCoord (affineSpaceInrEmbedding k n m) (ULift.up.{u, 0} (Sum.inl a)) = 0 :=
  pullbackCoord_affineSpaceInrEmbedding k n m (ULift.up.{u, 0} (Sum.inl a))

theorem pullbackCoord_affineSpaceInrEmbedding_inr (b : Fin m) :
    pullbackCoord (affineSpaceInrEmbedding k n m) (ULift.up.{u, 0} (Sum.inr b)) =
      AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} b) :=
  pullbackCoord_affineSpaceInrEmbedding k n m (ULift.up.{u, 0} (Sum.inr b))

theorem isClosedImmersion_affineSpaceInl :
    IsClosedImmersion (affineSpaceInl k n m) := by
  refine isClosedImmersion_of_coord_surjective (affineSpaceInl k n m)
    (affineSpaceInl_comp_affineSpaceIndexedByToSpec k n m) ?_
  rintro ⟨a⟩
  refine ⟨AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} (Sum.inl a)), ?_⟩
  have h : pullbackCoord (affineSpaceInl k n m) (ULift.up.{u, 0} (Sum.inl a))
      = AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a) :=
    pullbackCoord_affineSpaceInl_inl k n m a
  exact h

theorem isClosedImmersion_affineSpaceInrEmbedding :
    IsClosedImmersion (affineSpaceInrEmbedding k n m) := by
  refine isClosedImmersion_of_coord_surjective (R := CommRingCat.of k)
    (N := ULift.{u, 0} (Fin m)) (M := ULift.{u, 0} (Fin n ⊕ Fin m))
    (affineSpaceInrEmbedding k n m) (affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec k n m) ?_
  intro i
  refine ⟨AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} (Sum.inr i.down)), ?_⟩
  exact pullbackCoord_affineSpaceInrEmbedding k n m (ULift.up.{u, 0} (Sum.inr i.down))


end

instance instIsClosedImmersionLinEmbLeft (k : Type u) [Field k] (n m : ℕ) :
    IsClosedImmersion (affineSpaceInl k n m) :=
  isClosedImmersion_affineSpaceInl k n m

instance instIsClosedImmersionLinEmbRight (k : Type u) [Field k] (n m : ℕ) :
    IsClosedImmersion (affineSpaceInrEmbedding k n m) :=
  isClosedImmersion_affineSpaceInrEmbedding k n m

section
variable {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ) (q : Y ⟶ Spec (CommRingCat.of k))

theorem comp_affineSpaceInl (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)))
    (hf : f ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) = q) :
    f ≫ affineSpaceInl k n m = AffineSpace.homOfVector q (coordVectorInl n m f) := by
  apply AffineSpace.hom_ext
  · simp [hf]
  · intro i
    obtain ⟨j⟩ := i
    rw [appTop_comp_apply_eq_consolidated264, AffineSpace.homOfVector_appTop_coord, ← pullbackCoord_def,
      pullbackCoord_affineSpaceInl]
    cases j with
    | inl _ => rfl
    | inr _ => exact map_zero _

theorem comp_affineSpaceInrEmbedding (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)))
    (hf : f ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) = q) :
    f ≫ affineSpaceInrEmbedding k n m = AffineSpace.homOfVector q (coordVectorInr n m f) := by
  apply AffineSpace.hom_ext
  · simp [hf]
  · rintro ⟨j⟩
    rw [appTop_comp_apply_eq_consolidated264, AffineSpace.homOfVector_appTop_coord]
    cases j with
    | inl a =>
        have h := pullbackCoord_affineSpaceInrEmbedding_inl k n m a
        rw [pullbackCoord_def] at h
        rw [h, map_zero, coordVectorInr_inl]
    | inr b =>
        have h := pullbackCoord_affineSpaceInrEmbedding_inr k n m b
        rw [pullbackCoord_def] at h
        rw [h, coordVectorInr_inr, pullbackCoord_def]


end

section
variable {X : Scheme.{u}}

theorem IsStrictPullbackBlowupSeq.id (s : SequenceOfBlowups X) :
    IsStrictPullbackBlowupSeq (𝟙 X) s s := by
  refine ⟨rfl, fun i _ => 𝟙 (s.schemeAt i), by simp, fun i _ => ?_, fun i _ => ?_⟩
  · exact IsPullback.of_id_fst
  · simp

theorem isomorphic_of_isPullbackSequenceOfBlowups_id (s t : SequenceOfBlowups X)
    (h : IsPullbackBlowupSequence (𝟙 X) s t) (hc : ∀ i : ℕ, i < t.length → t.center i ≠ ⊤) :
    s.Isomorphic t := by
  have : AlgebraicGeometry.Surjective (𝟙 X) := inferInstance
  exact IsStrictPullbackBlowupSeq.isomorphic (h.isStrictPullback_of_surjective hc)
    (IsStrictPullbackBlowupSeq.id t)


end

section
variable (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] (n : ℕ)
include hsm

private theorem smooth_affineSpaceIndexedByToSpec_consolidated264 :
    Smooth (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n))) :=
  hsm k n

private theorem inStrictNormalCrossingPosition_nil_affineSpace_consolidated264 :
    InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n))) [] := by
  have : Smooth (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n))) := hsm k n
  exact inStrictNormalCrossingPosition_nil (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)))


end

def EmbeddingDatum.ofClosedImmersionAffineSpace (hsm : AffineSpaceIsSmooth.{u}) {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of k)} (n : ℕ)
    (e : Y ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) [IsClosedImmersion e]
    (hker : NonzeroOnComponents (Scheme.Hom.ker e))
    (hcomp : e ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) = p) :
    EmbeddingDatum k Y p where
  ambient := affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))
  ambientStruct := affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n))
  emb := e
  isAffine_ambient := by unfold affineSpaceIndexedBy; infer_instance
  smooth_ambientStruct := smooth_affineSpaceIndexedByToSpec_consolidated264 hsm k n
  locallyOfFiniteType_ambientStruct := by unfold affineSpaceIndexedByToSpec; infer_instance
  quasiCompact_ambientStruct := by unfold affineSpaceIndexedByToSpec; infer_instance
  isClosedImmersion_emb := inferInstance
  nonzeroOnComponents_ker := hker
  comp_eq := hcomp
  sncEmpty := inStrictNormalCrossingPosition_nil_affineSpace_consolidated264 hsm k n

@[simp]
theorem EmbeddingDatum.ofClosedImmersionAffineSpace_ambient (hsm : AffineSpaceIsSmooth.{u}) {k : Type u} [Field k]
    [CharZero k] {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of k)} (n : ℕ)
    (e : Y ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) [IsClosedImmersion e]
    (hker : NonzeroOnComponents (Scheme.Hom.ker e))
    (hcomp : e ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) = p) :
    (EmbeddingDatum.ofClosedImmersionAffineSpace hsm n e hker hcomp).ambient =
      affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)) :=
  rfl


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceOrigin
section


section

def affineSpaceOrigin (k : Type u) [Field k] (m : ℕ) :
    Spec (CommRingCat.of k) ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)) :=
  AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of k))) (fun _ => 0)

@[simp]
theorem affineSpaceOrigin_comp_toSpec (k : Type u) [Field k] (m : ℕ) :
    affineSpaceOrigin k m ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) =
      𝟙 (Spec (CommRingCat.of k)) := by
  unfold affineSpaceOrigin
  simp

@[simp]
theorem affineSpaceOrigin_comp_toSpec_assoc (k : Type u) [Field k] (m : ℕ) {Z : Scheme.{u}}
    (g : Spec (CommRingCat.of k) ⟶ Z) :
    affineSpaceOrigin k m ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) ≫ g = g := by
  rw [← Category.assoc, affineSpaceOrigin_comp_toSpec, Category.id_comp]

theorem pullbackCoord_affineSpaceOrigin (k : Type u) [Field k] (m : ℕ)
    (i : ULift.{u, 0} (Fin m)) :
    pullbackCoord (affineSpaceOrigin k m) i = 0 := by
  simp [pullbackCoord_def, affineSpaceOrigin]

@[simp]
theorem affineSpaceOrigin_appTop_coord (k : Type u) [Field k] (m : ℕ)
    (i : ULift.{u, 0} (Fin m)) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (affineSpaceOrigin k m)))
        (AffineSpace.coord (Spec (CommRingCat.of k)) i) = 0 := by
  simp [affineSpaceOrigin]

section
variable (k : Type u) [Field k] (m : ℕ)

theorem eq_affineSpaceOrigin_of_pullbackCoord_eq_zero (f : Spec (CommRingCat.of k) ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)))
    (hf : f ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) = 𝟙 (Spec (CommRingCat.of k)))
    (hcoord : ∀ i : ULift.{u, 0} (Fin m), pullbackCoord f i = 0) :
    f = affineSpaceOrigin k m := by
  refine AffineSpace.hom_ext ?_ ?_
  · simpa only [affineSpaceOrigin, AffineSpace.homOfVector_over] using hf
  · intro i
    simpa only [affineSpaceOrigin, AffineSpace.homOfVector_appTop_coord, pullbackCoord_def]
      using hcoord i

theorem isClosedImmersion_affineSpaceOrigin :
    IsClosedImmersion (affineSpaceOrigin k m) := by
  have hsurj : Function.Surjective
      (ConcreteCategory.hom (Scheme.Hom.appTop (affineSpaceOrigin k m))) := by
    intro x
    refine ⟨(ConcreteCategory.hom
        (Scheme.Hom.appTop (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m))))) x, ?_⟩
    have h1 : Scheme.Hom.appTop (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m))) ≫
        Scheme.Hom.appTop (affineSpaceOrigin k m) =
        Scheme.Hom.appTop (𝟙 (Spec (CommRingCat.of k))) := by
      rw [← Scheme.Hom.comp_appTop, affineSpaceOrigin_comp_toSpec]
    have h2 : (ConcreteCategory.hom (Scheme.Hom.appTop (affineSpaceOrigin k m)))
        ((ConcreteCategory.hom
          (Scheme.Hom.appTop (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m))))) x) =
        (ConcreteCategory.hom
          (Scheme.Hom.appTop (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m))) ≫
            Scheme.Hom.appTop (affineSpaceOrigin k m))) x := by
      simp
    rw [h2, h1]
    simp
  apply IsClosedImmersion.of_surjective_of_isAffine
  exact hsurj


end

instance instIsClosedImmersionAffineSpaceOrigin (k : Type u) [Field k] (m : ℕ) :
    IsClosedImmersion (affineSpaceOrigin k m) :=
  isClosedImmersion_affineSpaceOrigin k m

private theorem appTop_id_consolidated291 (X : Scheme.{u}) :
    Scheme.Hom.appTop (𝟙 X) = 𝟙 (X.presheaf.obj (Opposite.op ⊤)) := by
  simp [Scheme.Hom.appTop]

private theorem appTop_hom_appTop_inv_apply_consolidated291 {X Y : Scheme.{u}} (e : X ≅ Y)
    (x : ↑(X.presheaf.obj (Opposite.op ⊤))) :
    CommRingCat.Hom.hom (Scheme.Hom.appTop e.hom)
        (CommRingCat.Hom.hom (Scheme.Hom.appTop e.inv) x) = x := by
  have h : Scheme.Hom.appTop e.inv ≫ Scheme.Hom.appTop e.hom =
      𝟙 (X.presheaf.obj (Opposite.op ⊤)) := by
    rw [← Scheme.Hom.comp_appTop, e.hom_inv_id, appTop_id_consolidated291]
  have h2 := congrArg (fun φ => CommRingCat.Hom.hom φ x) h
  simpa using h2

private theorem nontrivial_globalSections_spec_consolidated291 (k : Type u) [Field k] :
    Nontrivial ↑((Spec (CommRingCat.of k)).presheaf.obj (Opposite.op ⊤)) := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have h3 := congrArg (fun z => CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of k)).hom z) h
  simp only [map_one, map_zero] at h3
  have h4 : (1 : k) = 0 := h3
  exact one_ne_zero h4

private def mvPolynomialFinToAffineSpaceGlobalSections_consolidated291 (k : Type u) [Field k] (m : ℕ) :
    MvPolynomial (ULift.{u, 0} (Fin m)) k →+*
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin m))).presheaf.obj (Opposite.op ⊤)) :=
  RingHom.comp
    (CommRingCat.Hom.hom (Scheme.Hom.appTop
      (AffineSpace.SpecIso (ULift.{u, 0} (Fin m)) (CommRingCat.of k)).hom))
    (CommRingCat.Hom.hom (Scheme.ΓSpecIso
      (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin m)) k))).inv)

section
variable (k : Type u) [Field k] (m : ℕ)

private theorem mvPolynomialToSections_apply_consolidated291 (x : MvPolynomial (ULift.{u, 0} (Fin m)) k) :
    mvPolynomialFinToAffineSpaceGlobalSections_consolidated291 k m x =
      CommRingCat.Hom.hom (Scheme.Hom.appTop
        (AffineSpace.SpecIso (ULift.{u, 0} (Fin m)) (CommRingCat.of k)).hom)
        (CommRingCat.Hom.hom (Scheme.ΓSpecIso
          (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin m)) k))).inv x) := rfl

private theorem mvPolynomialToSections_X_consolidated291 (i : ULift.{u, 0} (Fin m)) :
    mvPolynomialFinToAffineSpaceGlobalSections_consolidated291 k m (MvPolynomial.X i) =
      AffineSpace.coord (Spec (CommRingCat.of k)) i := by
  have hX : CommRingCat.Hom.hom (Scheme.Hom.appTop
        (AffineSpace.SpecIso (ULift.{u, 0} (Fin m)) (CommRingCat.of k)).inv)
        (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
      CommRingCat.Hom.hom (Scheme.ΓSpecIso
        (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin m)) k))).inv (MvPolynomial.X i) := by
    exact AffineSpace.SpecIso_inv_appTop_coord ..
  rw [mvPolynomialToSections_apply_consolidated291, ← hX]
  exact appTop_hom_appTop_inv_apply_consolidated291 _ _

private theorem mvPolynomialToSections_surjective_consolidated291 :
    Function.Surjective (mvPolynomialFinToAffineSpaceGlobalSections_consolidated291 k m) := by
  intro x
  refine ⟨CommRingCat.Hom.hom (Scheme.ΓSpecIso
      (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin m)) k))).hom
      (CommRingCat.Hom.hom (Scheme.Hom.appTop
        (AffineSpace.SpecIso (ULift.{u, 0} (Fin m)) (CommRingCat.of k)).inv) x), ?_⟩
  have hinv : CommRingCat.Hom.hom (Scheme.ΓSpecIso
        (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin m)) k))).inv
      (CommRingCat.Hom.hom (Scheme.ΓSpecIso
        (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin m)) k))).hom
        (CommRingCat.Hom.hom (Scheme.Hom.appTop
          (AffineSpace.SpecIso (ULift.{u, 0} (Fin m)) (CommRingCat.of k)).inv) x)) =
      CommRingCat.Hom.hom (Scheme.Hom.appTop
        (AffineSpace.SpecIso (ULift.{u, 0} (Fin m)) (CommRingCat.of k)).inv) x := by
    exact CommRingCat.inv_hom_apply ..
  rw [mvPolynomialToSections_apply_consolidated291, hinv, appTop_hom_appTop_inv_apply_consolidated291]


end

section
variable {σ : Type u}

private theorem sub_C_constantCoeff_mem_span_X_consolidated291 {A : Type u} [CommRing A]
    (p : MvPolynomial σ A) :
    p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈
      Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ A)) := by
  induction p using MvPolynomial.induction_on
  · rename_i a
    simp only [MvPolynomial.constantCoeff_C, sub_self]
    exact Ideal.zero_mem _
  · rename_i q r hq hr
    have hadd : q + r - MvPolynomial.C (MvPolynomial.constantCoeff (q + r)) =
        (q - MvPolynomial.C (MvPolynomial.constantCoeff q)) +
          (r - MvPolynomial.C (MvPolynomial.constantCoeff r)) := by
      simp only [map_add]
      ring
    rw [hadd]
    exact Ideal.add_mem _ hq hr
  · rename_i q i hq
    have hmul : q * MvPolynomial.X i -
        MvPolynomial.C (MvPolynomial.constantCoeff (q * MvPolynomial.X i)) =
        q * MvPolynomial.X i := by
      simp
    rw [hmul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

private theorem ker_eq_span_range_X_consolidated291 {K : Type u} [Field K] {T : Type u}
    [CommRing T] [Nontrivial T] (g : MvPolynomial σ K →+* T)
    (hg : ∀ i, g (MvPolynomial.X i) = 0) :
    RingHom.ker g = Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ K)) := by
  have hspan : Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ K)) ≤ RingHom.ker g := by
    rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    simpa [RingHom.mem_ker] using hg i
  refine le_antisymm ?_ hspan
  intro p hp
  have hsub := sub_C_constantCoeff_mem_span_X_consolidated291 (σ := σ) (A := K) p
  have h1 : g (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) = 0 :=
    RingHom.mem_ker.mp (hspan hsub)
  have hp0 : g p = 0 := RingHom.mem_ker.mp hp
  have h0 : g (MvPolynomial.C (MvPolynomial.constantCoeff p)) = 0 := by
    rw [map_sub, hp0, zero_sub, neg_eq_zero] at h1
    exact h1
  have hc : MvPolynomial.constantCoeff p = 0 := by
    have hinj : Function.Injective (g.comp (MvPolynomial.C : K →+* MvPolynomial σ K)) :=
      RingHom.injective _
    apply hinj
    simpa using h0
  have hpe : p = p - MvPolynomial.C (MvPolynomial.constantCoeff p) := by
    rw [hc, map_zero, sub_zero]
  rw [hpe]
  exact hsub


end

private theorem ker_eq_span_image_of_surjective_consolidated291 {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (ψ : A →+* B) (hsurj : Function.Surjective ψ) (g : B →+* C) (s : Set A)
    (h : RingHom.ker (g.comp ψ) = Ideal.span s) :
    RingHom.ker g = Ideal.span (ψ '' s) := by
  have h1 : Ideal.comap ψ (RingHom.ker g) = Ideal.span s := by
    rw [← h]
    ext x
    simp [RingHom.mem_ker, Ideal.mem_comap]
  have h2 : Ideal.map ψ (Ideal.comap ψ (RingHom.ker g)) = RingHom.ker g :=
    Ideal.map_comap_of_surjective ψ hsurj _
  rw [← h2, h1, Ideal.map_span]

section
variable (k : Type u) [Field k] (m : ℕ)

private theorem ker_appTop_affineSpaceOrigin_consolidated291 :
    RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop (affineSpaceOrigin k m))) =
      Ideal.span (Set.range fun i : Fin m =>
        AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} i)) := by
  have := nontrivial_globalSections_spec_consolidated291 k
  have hcomp : RingHom.ker
      ((CommRingCat.Hom.hom (Scheme.Hom.appTop (affineSpaceOrigin k m))).comp
        (mvPolynomialFinToAffineSpaceGlobalSections_consolidated291 k m)) =
      Ideal.span (Set.range
        (MvPolynomial.X : ULift.{u, 0} (Fin m) → MvPolynomial (ULift.{u, 0} (Fin m)) k)) := by
    refine ker_eq_span_range_X_consolidated291 _ ?_
    intro i
    rw [RingHom.comp_apply, mvPolynomialToSections_X_consolidated291 k m i]
    exact affineSpaceOrigin_appTop_coord k m i
  have main := ker_eq_span_image_of_surjective_consolidated291 (mvPolynomialFinToAffineSpaceGlobalSections_consolidated291 k m)
    (mvPolynomialToSections_surjective_consolidated291 k m)
    (CommRingCat.Hom.hom (Scheme.Hom.appTop (affineSpaceOrigin k m))) _ hcomp
  rw [main]
  congr 1
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨j, rfl⟩ := hp
    exact ⟨j.down, (mvPolynomialToSections_X_consolidated291 k m j).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨MvPolynomial.X (ULift.up.{u, 0} i), Set.mem_range_self _,
      mvPolynomialToSections_X_consolidated291 k m (ULift.up.{u, 0} i)⟩

theorem ker_affineSpaceOrigin :
    Scheme.Hom.ker (affineSpaceOrigin k m) = coordSubspaceIdeal k m Finset.univ := by
  have : QuasiCompact (affineSpaceOrigin k m) := inferInstance
  have hker : RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.app (affineSpaceOrigin k m) ⊤)) =
      Ideal.span (Set.range fun i : Fin m =>
        AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} i)) :=
    ker_appTop_affineSpaceOrigin_consolidated291 k m
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord]
  simpa using hker


end

private theorem pullbackCoord_comp_eq_hom_appTop_apply_consolidated291 {k : Type u} [Field k]
    {Y Z : Scheme.{u}} {n : Type u} (f : Y ⟶ Z) (g : Z ⟶ affineSpaceIndexedBy k n) (i : n) :
    pullbackCoord (f ≫ g) i =
      (ConcreteCategory.hom (Scheme.Hom.appTop f)) (pullbackCoord g i) := by
  rw [pullbackCoord_def, pullbackCoord_def, Scheme.Hom.comp_appTop]
  rfl

@[simp]
theorem affineSpaceInl_comp_projLeft (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceInl k n m ≫ projLeft k n m = 𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec, Category.id_comp]
  · rintro ⟨a⟩
    have h : pullbackCoord (affineSpaceInl k n m ≫ projLeft k n m) (ULift.up.{u, 0} a) =
        AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a) := by
      rw [pullbackCoord_comp_eq_hom_appTop_apply_consolidated291, pullbackCoord_def (projLeft k n m),
        projLeft_appTop_coord, ← pullbackCoord_def, pullbackCoord_affineSpaceInl_inl]
    rw [← pullbackCoord_def, h]
    simp

@[simp]
theorem affineSpaceInl_comp_projLeft_assoc (k : Type u) [Field k] (n m : ℕ) {Z : Scheme.{u}}
    (g : affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)) ⟶ Z) :
    affineSpaceInl k n m ≫ projLeft k n m ≫ g = g := by
  rw [← Category.assoc, affineSpaceInl_comp_projLeft, Category.id_comp]

@[simp]
theorem affineSpaceInrEmbedding_comp_projRight (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceInrEmbedding k n m ≫ projRight k n m = 𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin m))) := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, projRight_comp_affineSpaceIndexedByToSpec, affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec, Category.id_comp]
  · rintro ⟨b⟩
    have h : pullbackCoord (affineSpaceInrEmbedding k n m ≫ projRight k n m) (ULift.up.{u, 0} b) =
        AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} b) := by
      rw [pullbackCoord_comp_eq_hom_appTop_apply_consolidated291, pullbackCoord_def (projRight k n m),
        projRight_appTop_coord, ← pullbackCoord_def, pullbackCoord_affineSpaceInrEmbedding_inr]
    rw [← pullbackCoord_def, h]
    simp

@[simp]
theorem affineSpaceInrEmbedding_comp_projRight_assoc (k : Type u) [Field k] (n m : ℕ) {Z : Scheme.{u}}
    (g : affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)) ⟶ Z) :
    affineSpaceInrEmbedding k n m ≫ projRight k n m ≫ g = g := by
  rw [← Category.assoc, affineSpaceInrEmbedding_comp_projRight, Category.id_comp]

section
variable (k : Type u) [Field k] (n m : ℕ)

theorem affineSpaceInl_comp_projRight :
    affineSpaceInl k n m ≫ projRight k n m =
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) ≫ affineSpaceOrigin k m := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, projRight_comp_affineSpaceIndexedByToSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec, Category.assoc,
      affineSpaceOrigin_comp_toSpec, Category.comp_id]
  · rintro ⟨b⟩
    have h : pullbackCoord (affineSpaceInl k n m ≫ projRight k n m) (ULift.up.{u, 0} b) = 0 := by
      rw [pullbackCoord_comp_eq_hom_appTop_apply_consolidated291, pullbackCoord_def (projRight k n m),
        projRight_appTop_coord, ← pullbackCoord_def, pullbackCoord_affineSpaceInl_inr]
    have h2 : pullbackCoord
        (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) ≫ affineSpaceOrigin k m)
        (ULift.up.{u, 0} b) = 0 := by
      rw [pullbackCoord_comp_eq_hom_appTop_apply_consolidated291, pullbackCoord_affineSpaceOrigin, map_zero]
    rw [← pullbackCoord_def, ← pullbackCoord_def, h, h2]

theorem affineSpaceInrEmbedding_comp_projLeft :
    affineSpaceInrEmbedding k n m ≫ projLeft k n m =
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) ≫ affineSpaceOrigin k n := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec, Category.assoc,
      affineSpaceOrigin_comp_toSpec, Category.comp_id]
  · rintro ⟨a⟩
    have h : pullbackCoord (affineSpaceInrEmbedding k n m ≫ projLeft k n m) (ULift.up.{u, 0} a) = 0 := by
      rw [pullbackCoord_comp_eq_hom_appTop_apply_consolidated291, pullbackCoord_def (projLeft k n m),
        projLeft_appTop_coord, ← pullbackCoord_def, pullbackCoord_affineSpaceInrEmbedding_inl]
    have h2 : pullbackCoord (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) ≫
        affineSpaceOrigin k n) (ULift.up.{u, 0} a) = 0 := by
      rw [pullbackCoord_comp_eq_hom_appTop_apply_consolidated291, pullbackCoord_affineSpaceOrigin]
      simp
    rw [← pullbackCoord_def, ← pullbackCoord_def, h, h2]


end

theorem ker_affineSpaceInl_eq_comap (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] (n m : ℕ) :
    Scheme.Hom.ker (affineSpaceInl k n m) =
      (Scheme.Hom.ker (affineSpaceOrigin k m)).comap (projRight k n m) := by
  have hsmooth : Smooth (projRight k n m) := smooth_projRight hsm k n m
  have hflat : Flat (projRight k n m) := inferInstance
  have hbig : IsPullback (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)))
      (affineSpaceInl k n m ≫ projLeft k n m)
      (affineSpaceOrigin k m ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n))) := by
    rw [affineSpaceInl_comp_projLeft, affineSpaceOrigin_comp_toSpec]
    exact IsPullback.id_vert _
  have hsq : IsPullback (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n))) (affineSpaceInl k n m)
      (affineSpaceOrigin k m) (projRight k n m) :=
    IsPullback.of_bot hbig (affineSpaceInl_comp_projRight k n m).symm
      (isPullback_projLeft_projRight k n m).flip
  have : QuasiCompact (affineSpaceOrigin k m) := inferInstance
  have : QuasiCompact (affineSpaceInl k n m) := quasiCompact_of_isPullback hsq
  exact ker_eq_comap_ker_of_isPullback_of_flat hsq

private theorem isPullback_affineSpaceInrEmbedding_projLeft_consolidated291 (k : Type u) [Field k] (n m : ℕ) :
    IsPullback (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m))) (affineSpaceInrEmbedding k n m)
      (affineSpaceOrigin k n) (projLeft k n m) := by
  have h0 : IsPullback (𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin m))))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)))
      (𝟙 (Spec (CommRingCat.of k))) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have s : IsPullback (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)))
      (affineSpaceInrEmbedding k n m ≫ projRight k n m)
      (affineSpaceOrigin k n ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m))) := by
    rw [affineSpaceInrEmbedding_comp_projRight, affineSpaceOrigin_comp_toSpec]
    exact h0.flip
  exact IsPullback.of_bot s (affineSpaceInrEmbedding_comp_projLeft k n m).symm
    (isPullback_projLeft_projRight k n m)

section
variable (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] (n m : ℕ)
include hsm

theorem ker_affineSpaceInrEmbedding_eq_comap :
    Scheme.Hom.ker (affineSpaceInrEmbedding k n m) =
      (Scheme.Hom.ker (affineSpaceOrigin k n)).comap (projLeft k n m) := by
  have hsmooth : Smooth (projLeft k n m) := smooth_projLeft hsm k n m
  have hflat : Flat (projLeft k n m) := inferInstance
  have hq1 : QuasiCompact (affineSpaceOrigin k n) := inferInstance
  have hq2 : QuasiCompact (affineSpaceInrEmbedding k n m) := inferInstance
  exact ker_eq_comap_ker_of_isPullback_of_flat (isPullback_affineSpaceInrEmbedding_projLeft_consolidated291 k n m)

theorem hasSmoothCoordCodim_affineSpaceInl :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)))
      (affineSpaceInl k n m) m := by
  have hsp : Smooth (projRight k n m) := smooth_projRight hsm k n m
  intro x
  refine ⟨⊤, ?_, (⊤ : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin n ⊕ Fin m))).Opens).ι ≫
      projRight k n m, ?_, ?_, ?_⟩
  · trivial
  · infer_instance
  · rw [Category.assoc, projRight_comp_affineSpaceIndexedByToSpec]
  · rw [restrictIdeal_eq_comap_ι, ker_affineSpaceInl_eq_comap hsm, ker_affineSpaceOrigin,
      Scheme.IdealSheafData.comap_comp]

theorem hasSmoothCoordCodim_affineSpaceInrEmbedding :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)))
      (affineSpaceInrEmbedding k n m) n := by
  have hsmooth : Smooth (projLeft k n m) := smooth_projLeft hsm k n m
  intro x
  refine ⟨⊤, by simp, (⊤ : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin n ⊕ Fin m))).Opens).ι ≫
      projLeft k n m, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec]
  · rw [restrictIdeal_eq_comap_ι, ker_affineSpaceInrEmbedding_eq_comap hsm k n m, ker_affineSpaceOrigin k n]
    simp [Scheme.IdealSheafData.comap_comp]


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceChartPresentation
section


section

section
variable {n m : Type u} (e : n ≃ m) (S : Scheme.{u})

private theorem affineSpace_reindex_symm_comp_reindex_consolidated307 :
    AffineSpace.reindex (e.symm : m → n) S ≫ AffineSpace.reindex (e : n → m) S =
      𝟙 (AffineSpace n S) := by
  ext1
  · simp
  · rename_i i
    simp
    show (ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e.symm : m → n) S)))
        ((ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e : n → m) S)))
          (AffineSpace.coord S i)) = AffineSpace.coord S i
    simp

private theorem affineSpace_reindex_comp_reindex_symm_consolidated307 :
    AffineSpace.reindex (e : n → m) S ≫ AffineSpace.reindex (e.symm : m → n) S =
      𝟙 (AffineSpace m S) := by
  ext1
  · simp
  · rename_i i
    simp
    show (ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e : n → m) S)))
        ((ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e.symm : m → n) S)))
          (AffineSpace.coord S i)) = AffineSpace.coord S i
    simp


end

def affineSpaceIsoOfEquiv {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    AffineSpace n S ≅ AffineSpace m S where
  hom := AffineSpace.reindex (e.symm : m → n) S
  inv := AffineSpace.reindex (e : n → m) S
  hom_inv_id := affineSpace_reindex_symm_comp_reindex_consolidated307 e S
  inv_hom_id := affineSpace_reindex_comp_reindex_symm_consolidated307 e S

theorem affineSpaceIsoOfEquiv_hom_comp_over {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    (affineSpaceIsoOfEquiv e S).hom ≫ (AffineSpace m S ↘ S) = (AffineSpace n S ↘ S) := by
  simp [affineSpaceIsoOfEquiv, AffineSpace.reindex]

theorem affineSpaceIsoOfEquiv_hom_comp_toSpec (k : Type u) [Field k] {n m : Type u} (e : n ≃ m) :
    (affineSpaceIsoOfEquiv e (Spec (CommRingCat.of k))).hom ≫ affineSpaceIndexedByToSpec k m =
      affineSpaceIndexedByToSpec k n := by
  exact affineSpaceIsoOfEquiv_hom_comp_over e (Spec (CommRingCat.of k))

def uliftFinSumOneEquiv (n : ℕ) : ULift.{u, 0} (Fin n ⊕ Fin 1) ≃ ULift.{u, 0} (Fin (n + 1)) :=
  Equiv.ulift.trans (finSumFinEquiv.trans Equiv.ulift.symm)

def toAffineSpaceOfAmbientIso {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) :
    G.ambient ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin (n + 1))) :=
  φ.hom ≫ affineSpaceInl k n 1 ≫
    (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom

section
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ) (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)))

theorem isClosedImmersion_toAffineSpaceOfAmbientIso :
    IsClosedImmersion (toAffineSpaceOfAmbientIso G n φ) := by
  have h : IsClosedImmersion
      (φ.hom ≫ affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom) :=
    inferInstance
  exact h

theorem toAffineSpaceOfAmbientIso_comp_toSpec (hφ : φ.hom ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) = G.ambientStruct) :
    toAffineSpaceOfAmbientIso G n φ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))) =
      G.ambientStruct := by
  have h : toAffineSpaceOfAmbientIso G n φ =
      φ.hom ≫ affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom := rfl
  rw [h]
  simp only [Category.assoc]
  rw [affineSpaceIsoOfEquiv_hom_comp_toSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec, hφ]


end

theorem hasSmoothCoordCodim_toAffineSpaceOfAmbientIso (hsm : AffineSpaceIsSmooth.{u}) {k : Type u}
    [Field k] [CharZero k] {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of k)}
    (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))))
      (toAffineSpaceOfAmbientIso G n φ) 1 := by
  have h1 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin 1)))
      (affineSpaceInl k n 1) 1 := hasSmoothCoordCodim_affineSpaceInl hsm k n 1
  have h2 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))))
      (affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom) 1 :=
    h1.comp_iso_hom (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))))
      (affineSpaceIsoOfEquiv_hom_comp_toSpec k (uliftFinSumOneEquiv.{u} n))
  have hdef : toAffineSpaceOfAmbientIso G n φ =
      φ.hom ≫ affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom := rfl
  rw [hdef]
  exact h2.iso_hom_comp φ

def presentationOfAmbientIso (hsm : AffineSpaceIsSmooth.{u}) {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)))
    (hφ : φ.hom ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) = G.ambientStruct) :
    ClosedEmbeddingIntoAffineSpace G where
  codimBound := 1
  dim := n + 1
  toAffine := toAffineSpaceOfAmbientIso G n φ
  one_le_codimBound := le_rfl
  one_le_dim := Nat.succ_le_succ (Nat.zero_le n)
  isClosedImmersion_toAffine := isClosedImmersion_toAffineSpaceOfAmbientIso G n φ
  toAffine_comp := toAffineSpaceOfAmbientIso_comp_toSpec G n φ hφ
  locallyConstCodim := hasSmoothCoordCodim_toAffineSpaceOfAmbientIso hsm G n φ

def affineSpaceChartPresentation (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) [IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY] :
    ClosedEmbeddingIntoAffineSpace (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) :=
  presentationOfAmbientIso hsm (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) ((hemb k Y pY).choose)
    (Iso.refl _) (by exact Category.id_comp _)


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceFieldBaseChange
section


section

theorem exists_baseChangeAffineSpaceIso (k K : Type u) [Field k] [Field K] [Algebra k K]
    (n : Type u) :
    ∃ e : baseChange (affineSpaceIndexedByToSpec k n) K ≅ affineSpaceIndexedBy K n,
      e.hom ≫ affineSpaceIndexedByToSpec K n = baseChangeToSpec (affineSpaceIndexedByToSpec k n) K := by
  have hA : IsPullback (baseChangeProjection (affineSpaceIndexedByToSpec k n) K)
      (baseChangeToSpec (affineSpaceIndexedByToSpec k n) K) (affineSpaceIndexedByToSpec k n)
      (specMapAlgebraMap k K) := IsPullback.of_hasPullback _ _
  have hB : IsPullback (AlgebraicGeometry.AffineSpace.map n (specMapAlgebraMap k K))
      (affineSpaceIndexedByToSpec K n) (affineSpaceIndexedByToSpec k n) (specMapAlgebraMap k K) :=
    AlgebraicGeometry.AffineSpace.isPullback_map (n := n) (specMapAlgebraMap k K)
  exact ⟨hA.isoIsPullback _ _ hB, hA.isoIsPullback_hom_snd _ _ hB⟩

def baseChangeAffineSpaceIso (k K : Type u) [Field k] [Field K] [Algebra k K] (n : Type u) :
    baseChange (affineSpaceIndexedByToSpec k n) K ≅ affineSpaceIndexedBy K n :=
  (exists_baseChangeAffineSpaceIso k K n).choose

@[simp]
theorem baseChangeAffineSpaceIso_hom_comp_toSpec (k K : Type u) [Field k] [Field K] [Algebra k K]
    (n : Type u) :
    (baseChangeAffineSpaceIso k K n).hom ≫ affineSpaceIndexedByToSpec K n =
      baseChangeToSpec (affineSpaceIndexedByToSpec k n) K :=
  (exists_baseChangeAffineSpaceIso k K n).choose_spec

private theorem affineSpaceEmbeddingDatum_baseChange_ambient_eq_consolidated324
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k K : Type u) [Field k] [CharZero k] [Field K] [CharZero K]
    [Algebra k K] (Y : Scheme.{u}) [IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (hker : NonzeroOnComponents
      (Scheme.Hom.ker ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChangeEmb K)))
    (hsncK : InStrictNormalCrossingPosition
      (baseChangeToSpec (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambientStruct K) []) :
    ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK).ambient =
      baseChange (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (hemb k Y pY).choose))) K :=
  rfl

def affineSpaceChartBaseChangeAmbientIso
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k K : Type u) [Field k] [CharZero k] [Field K] [CharZero K]
    [Algebra k K] (Y : Scheme.{u}) [IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (hker : NonzeroOnComponents
      (Scheme.Hom.ker ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChangeEmb K)))
    (hsncK : InStrictNormalCrossingPosition
      (baseChangeToSpec (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambientStruct K) []) :
    ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK).ambient ≅
      affineSpaceIndexedBy K (ULift.{u, 0} (Fin (hemb k Y pY).choose)) :=
  eqToIso (affineSpaceEmbeddingDatum_baseChange_ambient_eq_consolidated324 hemb hsnc hsm k K Y pY hker hsncK) ≪≫
    baseChangeAffineSpaceIso k K (ULift.{u, 0} (Fin (hemb k Y pY).choose))

private theorem affineSpaceChartBaseChangeAmbientIso_hom_comp_consolidated324
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k K : Type u) [Field k] [CharZero k] [Field K] [CharZero K]
    [Algebra k K] (Y : Scheme.{u}) [IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (hker : NonzeroOnComponents
      (Scheme.Hom.ker ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChangeEmb K)))
    (hsncK : InStrictNormalCrossingPosition
      (baseChangeToSpec (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambientStruct K) []) :
    (affineSpaceChartBaseChangeAmbientIso hemb hsnc hsm k K Y pY hker hsncK).hom ≫
        affineSpaceIndexedByToSpec K (ULift.{u, 0} (Fin (hemb k Y pY).choose)) =
      ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK).ambientStruct := by
  have hA : (baseChangeAffineSpaceIso k K (ULift.{u, 0} (Fin (hemb k Y pY).choose))).hom ≫
      affineSpaceIndexedByToSpec K (ULift.{u, 0} (Fin (hemb k Y pY).choose)) =
      ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK).ambientStruct :=
    baseChangeAffineSpaceIso_hom_comp_toSpec k K _
  have hB : (𝟙 (baseChange (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (hemb k Y pY).choose))) K) ≫
        (baseChangeAffineSpaceIso k K (ULift.{u, 0} (Fin (hemb k Y pY).choose))).hom) ≫
      affineSpaceIndexedByToSpec K (ULift.{u, 0} (Fin (hemb k Y pY).choose)) =
      ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK).ambientStruct := by
    rw [Category.id_comp]
    exact hA
  exact hB

def affineSpaceChartBaseChangePresentation
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k K : Type u) [Field k] [CharZero k] [Field K] [CharZero K]
    [Algebra k K] (Y : Scheme.{u}) [IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (hker : NonzeroOnComponents
      (Scheme.Hom.ker ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChangeEmb K)))
    (hsncK : InStrictNormalCrossingPosition
      (baseChangeToSpec (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambientStruct K) []) :
    ClosedEmbeddingIntoAffineSpace
      ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK) :=
  presentationOfAmbientIso hsm
    ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK)
    (hemb k Y pY).choose
    (affineSpaceChartBaseChangeAmbientIso hemb hsnc hsm k K Y pY hker hsncK)
    (affineSpaceChartBaseChangeAmbientIso_hom_comp_consolidated324 hemb hsnc hsm k K Y pY hker hsncK)


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PresentedSelection
section


section

structure PresentedSelection where
  sel : EmbeddingChoice.{u}
  pres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y], ClosedEmbeddingIntoAffineSpace (sel k Y p)
  basePres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y] (K : Type u) [Field K] [CharZero K] [Algebra k K]
    (hker : NonzeroOnComponents (Scheme.Hom.ker ((sel k Y p).baseChangeEmb K)))
    (hsnc : InStrictNormalCrossingPosition (baseChangeToSpec (sel k Y p).ambientStruct K) []),
    ClosedEmbeddingIntoAffineSpace ((sel k Y p).baseChange K hker hsnc)

theorem isCompatibleWithFieldBaseChange_toAffineResolutionRule (R : EmbeddedResolutionRule.{u})
    (C : PresentedSelection.{u}) (hinv : R.IsIndependentOfPresentedEmbedding)
    (hfield : R.IsCompatibleWithFieldBaseChange)
    (hsnc : ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u})
      (q : A ⟶ Spec (CommRingCat.of k)), Smooth q → InStrictNormalCrossingPosition q []) :
    IsCompatibleWithFieldBaseChange (R.toAffineResolutionRule C.sel) := by
  intro k _ _ Y p _ _ _ _ K _ _ _ _ _
  have hlft : LocallyOfFiniteType (baseChangeToSpec p K) :=
    locallyOfFiniteType_baseChangeToSpec p K
  have hqcb : QuasiCompact (baseChangeToSpec p K) :=
    quasiCompact_baseChangeToSpec p K
  have hsncK : InStrictNormalCrossingPosition
      (baseChangeToSpec (C.sel k Y p).ambientStruct K)
      ([] : List (baseChange (C.sel k Y p).ambientStruct K).IdealSheafData) :=
    hsnc K (baseChange (C.sel k Y p).ambientStruct K)
      (baseChangeToSpec (C.sel k Y p).ambientStruct K)
      (EmbeddingDatum.smooth_baseChangeToSpec_ambientToSpec (C.sel k Y p) K)
  have hsq : IsPullback (baseChangeProjection p K) ((C.sel k Y p).baseChangeEmb K)
      (C.sel k Y p).emb (baseChangeProjection (C.sel k Y p).ambientStruct K) :=
    (EmbeddingDatum.isPullback_baseChangeEmb (C.sel k Y p) K).flip
  have hflat : Flat (baseChangeProjection (C.sel k Y p).ambientStruct K) :=
    inferInstance
  have hqc1 : QuasiCompact (C.sel k Y p).emb := inferInstance
  have hqc2 : QuasiCompact ((C.sel k Y p).baseChangeEmb K) :=
    quasiCompact_of_isPullback hsq
  have hkerK : NonzeroOnComponents (Scheme.Hom.ker ((C.sel k Y p).baseChangeEmb K)) := by
    rw [ker_eq_comap_ker_of_isPullback_of_flat hsq]
    exact NonzeroOnComponents.comap_of_flat (C.sel k Y p).nonzeroOnComponents_ker _
  exact IsStrictPullbackBlowupSeq.of_isomorphic_pullback (hfield k Y p (C.sel k Y p) K hkerK hsncK)
    (hinv K (baseChange p K) (baseChangeToSpec p K)
      ((C.sel k Y p).baseChange K hkerK hsncK)
      (C.sel K (baseChange p K) (baseChangeToSpec p K))
      (C.basePres k Y p K hkerK hsncK)
      (C.pres K (baseChange p K) (baseChangeToSpec p K)))

def affineSpacePresentedSelection (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    PresentedSelection.{u} where
  sel := affineSpaceEmbeddingChoice hemb hsncE hsm
  pres := fun k _ _ Y p _ _ _ _ => affineSpaceChartPresentation hemb hsncE hsm k Y p
  basePres := fun k _ _ Y p _ _ _ _ K _ _ _ hker hsncK =>
    affineSpaceChartBaseChangePresentation hemb hsncE hsm k K Y p hker hsncK

@[simp]
theorem affineSpacePresentedSelection_selection (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    (affineSpacePresentedSelection hemb hsncE hsm).sel = affineSpaceEmbeddingChoice hemb hsncE hsm :=
  rfl


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrictTransformTower
section

open CategoryTheory.Limits TopologicalSpace Opposite

section

namespace EmbeddedBlowupSequence

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]

instance instIsClosedImmersionEmbCompIsoZeroInv (S : EmbeddedBlowupSequence k Y pY) :
    IsClosedImmersion (S.emb ≫ S.ambientSeq.isoZero.inv) :=
  inferInstance

def detachedToCoprod (T : EmbeddedBlowupSequence k Y pY) (s : ℕ) :
    ∀ (i : ℕ), s < i → (T.detachedScheme s ⟶ T.detachedCoprod i)
  | 0, h => absurd h (Nat.not_lt_zero s)
  | (i + 1), h =>
      if hs : s = i then
        eqToHom (congrArg T.detachedScheme hs) ≫
          (coprod.inr : T.detachedScheme i ⟶ T.detachedCoprod i ⨿ T.detachedScheme i)
      else
        detachedToCoprod T s i (by omega) ≫
          (coprod.inl : T.detachedCoprod i ⟶ T.detachedCoprod i ⨿ T.detachedScheme i)

variable (S : EmbeddedBlowupSequence k Y pY)

def strictTransformMapOfLE {a b : ℕ} (h : a ≤ b) : S.strictTransform b ⟶ S.strictTransform a :=
  Nat.leRec (motive := fun n _ => S.strictTransform n ⟶ S.strictTransform a)
    (𝟙 (S.strictTransform a)) (fun n _ f => S.strictTransformMap n ≫ f) h

@[simp] theorem strictTransformMapOfLE_self (a : ℕ) :
    S.strictTransformMapOfLE (le_refl a) = 𝟙 (S.strictTransform a) := by
  exact Nat.leRec_self ..

private theorem strictTransformMapOfLE_succ_of_le_consolidated188 (T : EmbeddedBlowupSequence k Y pY) {a b : ℕ} (h : a ≤ b)
    {h' : a ≤ b + 1} :
    T.strictTransformMapOfLE h' = T.strictTransformMap b ≫ T.strictTransformMapOfLE h := by
  exact Nat.leRec_succ ..

theorem strictTransformMapOfLE_strictTransformι {a b : ℕ} (h : a ≤ b) :
    S.strictTransformMapOfLE h ≫ S.strictTransformι a = S.strictTransformι b ≫ S.ambientSeq.transitionMap h := by
  induction b, h using Nat.le_induction with
  | base =>
      have e1 : S.strictTransformMapOfLE (Nat.le_refl a) = 𝟙 (S.strictTransform a) := by
        simp [EmbeddedBlowupSequence.strictTransformMapOfLE, Nat.leRec_self]
      have e2 : S.ambientSeq.transitionMap (Nat.le_refl a) = 𝟙 (S.ambientSeq.schemeAt a) := by
        simp [SequenceOfBlowups.transitionMap_def]
      simp only [e1, e2, Category.id_comp, Category.comp_id]
  | succ b hb ih =>
      have e1 : S.strictTransformMapOfLE (Nat.le_succ_of_le hb) = S.strictTransformMap b ≫ S.strictTransformMapOfLE hb :=
        strictTransformMapOfLE_succ_of_le_consolidated188 S hb
      have e2 : S.ambientSeq.transitionMap (Nat.le_succ_of_le hb)
          = S.ambientSeq.transitionMapSucc b ≫ S.ambientSeq.transitionMap hb := by
        rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
        exact (SequenceOfBlowups.transitionMap_trans S.ambientSeq hb (Nat.le_succ b)).symm
      have e3 : S.strictTransformMap b ≫ S.strictTransformι b
          = S.strictTransformι (b + 1) ≫ S.ambientSeq.transitionMapSucc b := S.strictTransformMap_comp_strictTransformι b
      rw [e1, e2, Category.assoc, ih, ← Category.assoc, e3]
      simp only [Category.assoc]

private theorem exists_iso_coprod_of_isInitial_consolidated188 {A B : Scheme.{u}} (hB : IsInitial B) :
    ∃ u : A ≅ A ⨿ B, u.hom = (coprod.inl : A ⟶ A ⨿ B) := by
  refine ⟨⟨(coprod.inl : A ⟶ A ⨿ B), coprod.desc (𝟙 A) (hB.to A),
    coprod.inl_desc (𝟙 A) (hB.to A), ?_⟩, rfl⟩
  refine coprod.hom_ext ?_ (hB.hom_ext _ _)
  calc (coprod.inl : A ⟶ A ⨿ B) ≫ coprod.desc (𝟙 A) (hB.to A) ≫ (coprod.inl : A ⟶ A ⨿ B)
      = ((coprod.inl : A ⟶ A ⨿ B) ≫ coprod.desc (𝟙 A) (hB.to A)) ≫
          (coprod.inl : A ⟶ A ⨿ B) := (Category.assoc _ _ _).symm
    _ = 𝟙 A ≫ (coprod.inl : A ⟶ A ⨿ B) :=
        congrArg (fun t => t ≫ (coprod.inl : A ⟶ A ⨿ B)) (coprod.inl_desc (𝟙 A) (hB.to A))
    _ = (coprod.inl : A ⟶ A ⨿ B) := Category.id_comp _
    _ = (coprod.inl : A ⟶ A ⨿ B) ≫ 𝟙 (A ⨿ B) := (Category.comp_id _).symm

private theorem exists_iso_of_coprodIso_of_isInitial_consolidated188 {A B Z : Scheme.{u}} (hB : IsInitial B)
    (w : A ⨿ B ≅ Z) :
    ∃ e : A ≅ Z, e.hom = (coprod.inl : A ⟶ A ⨿ B) ≫ w.hom := by
  obtain ⟨u, hu⟩ := exists_iso_coprod_of_isInitial_consolidated188 (A := A) (B := B) hB
  refine ⟨u ≪≫ w, ?_⟩
  show u.hom ≫ w.hom = (coprod.inl : A ⟶ A ⨿ B) ≫ w.hom
  exact congrArg (fun t => t ≫ w.hom) hu

private theorem comp_inv_comp_hom_cancel_consolidated188 {A B C D E : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (h : C ⟶ E) (i : D ≅ E) :
    (f ≫ g ≫ (h ≫ i.inv)) ≫ i.hom = (f ≫ g) ≫ h := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem exists_strictTransformZeroIso :
    ∃ e : S.strictTransform 0 ≅ Y, e.hom ≫ S.emb = S.strictTransformι 0 ≫ S.ambientSeq.isoZero.hom := by
  obtain ⟨e, he⟩ := exists_iso_of_coprodIso_of_isInitial_consolidated188 (A := S.strictTransform 0)
    (B := S.detachedCoprod 0) (Z := Y) initialIsInitial S.totalSpaceZeroIso
  refine ⟨e, ?_⟩
  calc e.hom ≫ S.emb
      = ((coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom) ≫ S.emb :=
        congrArg (fun t => t ≫ S.emb) he
    _ = ((coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom ≫
          (S.emb ≫ S.ambientSeq.isoZero.inv)) ≫ S.ambientSeq.isoZero.hom :=
        (comp_inv_comp_hom_cancel_consolidated188 (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0)
          S.totalSpaceZeroIso.hom S.emb S.ambientSeq.isoZero).symm
    _ = S.strictTransformι 0 ≫ S.ambientSeq.isoZero.hom :=
        congrArg (fun t => t ≫ S.ambientSeq.isoZero.hom) S.totalSpaceZeroIso_spec

def strictTransformZeroIso : S.strictTransform 0 ≅ Y := S.exists_strictTransformZeroIso.choose

theorem strictTransformZeroIso_hom_emb :
    S.strictTransformZeroIso.hom ≫ S.emb = S.strictTransformι 0 ≫ S.ambientSeq.isoZero.hom :=
  S.exists_strictTransformZeroIso.choose_spec

theorem totalSpaceZeroIso_inv_eq :
    S.totalSpaceZeroIso.inv =
      S.strictTransformZeroIso.inv ≫ (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) := by
  have h2 : S.strictTransformZeroIso.hom ≫ (S.emb ≫ S.ambientSeq.isoZero.inv) = S.strictTransformι 0 := by
    rw [← Category.assoc, S.strictTransformZeroIso_hom_emb, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h3 : (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom =
      S.strictTransformZeroIso.hom := by
    refine (cancel_mono (S.emb ≫ S.ambientSeq.isoZero.inv)).mp ?_
    rw [Category.assoc, S.totalSpaceZeroIso_spec, h2]
  refine (cancel_mono S.totalSpaceZeroIso.hom).mp ?_
  rw [Iso.inv_hom_id, Category.assoc, h3, Iso.inv_hom_id]

theorem inl_totalSpaceZeroIso_hom :
    (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom =
      S.strictTransformZeroIso.hom := by
  have h : S.strictTransformZeroIso.hom ≫ S.totalSpaceZeroIso.inv =
      (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) := by
    rw [S.totalSpaceZeroIso_inv_eq, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

def strictTransformToBase (i : ℕ) : S.strictTransform i ⟶ Y :=
  S.strictTransformMapOfLE (Nat.zero_le i) ≫ S.strictTransformZeroIso.hom

theorem strictTransformToBase_emb (i : ℕ) :
    S.strictTransformToBase i ≫ S.emb = S.strictTransformι i ≫ S.ambientSeq.projectionToBase i := by
  have h1 : S.strictTransformToBase i = S.strictTransformMapOfLE (Nat.zero_le i) ≫ S.strictTransformZeroIso.hom := rfl
  have h2 : S.ambientSeq.projectionToBase i
      = S.ambientSeq.transitionMap (Nat.zero_le i) ≫ S.ambientSeq.isoZero.hom :=
    SequenceOfBlowups.projectionToBase_def S.ambientSeq i
  rw [h1, Category.assoc, S.strictTransformZeroIso_hom_emb, ← Category.assoc,
    S.strictTransformMapOfLE_strictTransformι (Nat.zero_le i), Category.assoc, h2]

def detachedCoprodInl (i : ℕ) : S.detachedCoprod i ⟶ S.detachedCoprod (i + 1) :=
  (coprod.inl : S.detachedCoprod i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i)

section
variable (i : ℕ)

theorem detachedCoprodInl_eq :
    S.detachedCoprodInl i = (coprod.inl : S.detachedCoprod i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i) :=
  rfl

theorem detachedCoprodInl_inr_totalTransition :
    S.detachedCoprodInl i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
        S.totalTransition i =
      (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) :=
  S.inl_inr_totalTransition i

theorem detachedCoprodInl_inr_totalTransition_assoc {T : Scheme.{u}}
    (g : S.totalSpace i ⟶ T) :
    S.detachedCoprodInl i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
        S.totalTransition i ≫ g =
      (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫ g := by
  have h : S.detachedCoprodInl i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
      S.totalTransition i = (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) :=
    S.detachedCoprodInl_inr_totalTransition i
  calc S.detachedCoprodInl i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
        S.totalTransition i ≫ g
      = (S.detachedCoprodInl i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
          S.totalTransition i) ≫ g := by simp only [Category.assoc]
    _ = (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫ g := by rw [h]


end

def detachedCoprodInr (i : ℕ) : S.detachedScheme i ⟶ S.detachedCoprod (i + 1) :=
  (coprod.inr : S.detachedScheme i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i)

section
variable (i : ℕ)

theorem detachedCoprodInr_eq :
    S.detachedCoprodInr i = (coprod.inr : S.detachedScheme i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i) :=
  rfl

theorem detachedCoprodInr_inr_totalTransition :
    S.detachedCoprodInr i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
        S.totalTransition i =
      S.detachedι i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) :=
  S.inr_inr_totalTransition i


end

section
variable (i : ℕ) {T : Scheme.{u}}

theorem detachedCoprodInr_inr_totalTransition_assoc (g : S.totalSpace i ⟶ T) :
    S.detachedCoprodInr i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
        S.totalTransition i ≫ g =
      S.detachedι i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ g := by
  have h : S.detachedCoprodInr i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
      S.totalTransition i = S.detachedι i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) :=
    S.detachedCoprodInr_inr_totalTransition i
  calc S.detachedCoprodInr i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
        S.totalTransition i ≫ g
      = (S.detachedCoprodInr i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
          S.totalTransition i) ≫ g := by simp only [Category.assoc]
    _ = (S.detachedι i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) ≫ g := by rw [h]
    _ = S.detachedι i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ g :=
        Category.assoc _ _ _

theorem detachedCoprod_succ_hom_ext {f g : S.detachedCoprod (i + 1) ⟶ T}
    (hl : S.detachedCoprodInl i ≫ f = S.detachedCoprodInl i ≫ g)
    (hr : S.detachedCoprodInr i ≫ f = S.detachedCoprodInr i ≫ g) : f = g := by
  refine coprod.hom_ext ?_ ?_
  · exact hl
  · exact hr


end

theorem detachedToCoprod_succ_of_lt (s i : ℕ) (h : s < i) :
    S.detachedToCoprod s (i + 1) (Nat.lt_succ_of_lt h) = S.detachedToCoprod s i h ≫ S.detachedCoprodInl i := by
  have hne : ¬ (s = i) := by omega
  exact dif_neg hne

theorem detachedToCoprod_self (i : ℕ) :
    S.detachedToCoprod i (i + 1) (Nat.lt_succ_self i) = S.detachedCoprodInr i := by
  rw [detachedToCoprod]
  simp [detachedCoprodInr_eq]

private theorem detachedCoprod_hom_ext_forall_consolidated188 (W : EmbeddedBlowupSequence k Y pY) :
    ∀ (i : ℕ) (Z : Scheme.{u}) (f g : W.detachedCoprod i ⟶ Z),
      (∀ s (hs : s < i), W.detachedToCoprod s i hs ≫ f = W.detachedToCoprod s i hs ≫ g) → f = g := by
  intro i
  induction i with
  | zero =>
      intro Z f g _
      have hI : IsInitial (W.detachedCoprod 0) := initialIsInitial
      exact hI.hom_ext f g
  | succ i ih =>
      intro Z f g hf
      refine W.detachedCoprod_succ_hom_ext i ?_ ?_
      · refine ih Z (W.detachedCoprodInl i ≫ f) (W.detachedCoprodInl i ≫ g) ?_
        intro s hs
        have h := hf s (Nat.lt_succ_of_lt hs)
        rw [W.detachedToCoprod_succ_of_lt s i hs] at h
        simp only [Category.assoc] at h
        exact h
      · have h := hf i (Nat.lt_succ_self i)
        rw [W.detachedToCoprod_self i] at h
        exact h

section
variable (i : ℕ)

theorem detachedCoprod_hom_ext {T : Scheme.{u}} {f g : S.detachedCoprod i ⟶ T}
    (hf : ∀ s (hs : s < i), S.detachedToCoprod s i hs ≫ f = S.detachedToCoprod s i hs ≫ g) : f = g :=
  detachedCoprod_hom_ext_forall_consolidated188 S i T f g hf

theorem inl_totalTransition :
    (coprod.inl : S.strictTransform (i + 1) ⟶ S.totalSpace (i + 1)) ≫ S.totalTransition i =
      S.strictTransformMap i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) :=
  S.inl_totalTransition_eq_strictTransformMap_inl i

theorem inl_totalTransition_assoc {T : Scheme.{u}} (g : S.totalSpace i ⟶ T) :
    (coprod.inl : S.strictTransform (i + 1) ⟶ S.totalSpace (i + 1)) ≫ S.totalTransition i ≫ g =
      S.strictTransformMap i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ g := by
  rw [← Category.assoc, S.inl_totalTransition_eq_strictTransformMap_inl i, Category.assoc]


end

def totalMapOfLE {a b : ℕ} (h : a ≤ b) : S.totalSpace b ⟶ S.totalSpace a :=
  Nat.leRec (motive := fun n _ => S.totalSpace n ⟶ S.totalSpace a)
    (𝟙 (S.totalSpace a)) (fun n _ f => S.totalTransition n ≫ f) h

@[simp] theorem totalMapOfLE_self (a : ℕ) :
    S.totalMapOfLE (le_refl a) = 𝟙 (S.totalSpace a) := by
  exact Nat.leRec_self ..

theorem totalMapOfLE_succ {a b : ℕ} (h : a ≤ b) :
    S.totalMapOfLE (h.trans (Nat.le_succ b)) = S.totalTransition b ≫ S.totalMapOfLE h := by
  simp [totalMapOfLE, Nat.leRec_succ, h]

private theorem totalMapOfLE_succ_of_le_consolidated188 (T : EmbeddedBlowupSequence k Y pY) {a b : ℕ} (h : a ≤ b)
    {h' : a ≤ b + 1} :
    T.totalMapOfLE h' = T.totalTransition b ≫ T.totalMapOfLE h := by
  exact Nat.leRec_succ ..

theorem inl_totalMapOfLE {a b : ℕ} (h : a ≤ b) :
    (coprod.inl : S.strictTransform b ⟶ S.totalSpace b) ≫ S.totalMapOfLE h =
      S.strictTransformMapOfLE h ≫ (coprod.inl : S.strictTransform a ⟶ S.totalSpace a) := by
  induction b, h using Nat.le_induction with
  | base =>
      rw [S.totalMapOfLE_self a, S.strictTransformMapOfLE_self a, Category.comp_id, Category.id_comp]
  | succ b hb ih =>
      rw [totalMapOfLE_succ_of_le_consolidated188 S hb, strictTransformMapOfLE_succ_of_le_consolidated188 S hb,
        ← Category.assoc, S.inl_totalTransition b, Category.assoc, ih]
      simp only [Category.assoc]

private theorem detachedToCoprod_inr_totalMapOfLE_forall_consolidated188 (W : EmbeddedBlowupSequence k Y pY) :
    ∀ (b a s : ℕ) (hab : a ≤ b) (has : a ≤ s) (hsb : s < b),
      W.detachedToCoprod s b hsb ≫ (coprod.inr : W.detachedCoprod b ⟶ W.totalSpace b) ≫ W.totalMapOfLE hab =
        W.detachedι s ≫ W.strictTransformMapOfLE has ≫ (coprod.inl : W.strictTransform a ⟶ W.totalSpace a) := by
  intro b
  induction b with
  | zero => exact fun a s _ _ hsb => absurd hsb (Nat.not_lt_zero s)
  | succ b ih =>
      intro a s hab has hsb
      by_cases h : s = b
      · subst h
        have hd : W.totalMapOfLE hab = W.totalTransition s ≫ W.totalMapOfLE has := W.totalMapOfLE_succ has
        have hfs : W.detachedToCoprod s (s + 1) hsb = W.detachedCoprodInr s := W.detachedToCoprod_self s
        rw [hfs, hd, W.detachedCoprodInr_inr_totalTransition_assoc s (W.totalMapOfLE has),
          W.inl_totalMapOfLE has]
      · have hsb' : s < b := lt_of_le_of_ne (Nat.lt_succ_iff.mp hsb) h
        have hab' : a ≤ b := has.trans hsb'.le
        have hd : W.totalMapOfLE hab = W.totalTransition b ≫ W.totalMapOfLE hab' := W.totalMapOfLE_succ hab'
        have hf : W.detachedToCoprod s (b + 1) hsb = W.detachedToCoprod s b hsb' ≫ W.detachedCoprodInl b :=
          W.detachedToCoprod_succ_of_lt s b hsb'
        rw [hf, hd, Category.assoc,
          W.detachedCoprodInl_inr_totalTransition_assoc b (W.totalMapOfLE hab')]
        exact ih a s hab' has hsb'

theorem detachedToCoprod_inr_totalMapOfLE {a b s : ℕ} (hab : a ≤ b) (has : a ≤ s) (hsb : s < b) :
    S.detachedToCoprod s b hsb ≫ (coprod.inr : S.detachedCoprod b ⟶ S.totalSpace b) ≫ S.totalMapOfLE hab =
      S.detachedι s ≫ S.strictTransformMapOfLE has ≫ (coprod.inl : S.strictTransform a ⟶ S.totalSpace a) :=
  detachedToCoprod_inr_totalMapOfLE_forall_consolidated188 S b a s hab has hsb

def detachedCoprodMapOfLE {a b : ℕ} (h : a ≤ b) : S.detachedCoprod a ⟶ S.detachedCoprod b :=
  Nat.leRec (motive := fun n _ => S.detachedCoprod a ⟶ S.detachedCoprod n)
    (𝟙 (S.detachedCoprod a)) (fun n _ f => f ≫ S.detachedCoprodInl n) h

@[simp] theorem detachedCoprodMapOfLE_self (a : ℕ) :
    S.detachedCoprodMapOfLE (le_refl a) = 𝟙 (S.detachedCoprod a) := by
  exact Nat.leRec_self ..

theorem detachedCoprodMapOfLE_succ {a b : ℕ} (h : a ≤ b) :
    S.detachedCoprodMapOfLE (h.trans (Nat.le_succ b)) = S.detachedCoprodMapOfLE h ≫ S.detachedCoprodInl b := by
  exact Nat.leRec_succ ..

private theorem detachedCoprodMapOfLE_succ_of_le_consolidated188 (T : EmbeddedBlowupSequence k Y pY) {a b : ℕ} (h : a ≤ b)
    {h' : a ≤ b + 1} :
    T.detachedCoprodMapOfLE h' = T.detachedCoprodMapOfLE h ≫ T.detachedCoprodInl b := by
  exact Nat.leRec_succ ..

theorem detachedToCoprod_detachedCoprodMapOfLE {s a b : ℕ} (hsa : s < a) (hab : a ≤ b) :
    S.detachedToCoprod s a hsa ≫ S.detachedCoprodMapOfLE hab = S.detachedToCoprod s b (lt_of_lt_of_le hsa hab) := by
  induction b, hab using Nat.le_induction with
  | base =>
      exact Eq.trans
        (congrArg (fun t : S.detachedCoprod a ⟶ S.detachedCoprod a => S.detachedToCoprod s a hsa ≫ t)
          (S.detachedCoprodMapOfLE_self a))
        (Category.comp_id _)
  | succ b hb ih =>
      have h1 : S.detachedCoprodMapOfLE (Nat.le_succ_of_le hb) = S.detachedCoprodMapOfLE hb ≫ S.detachedCoprodInl b :=
        detachedCoprodMapOfLE_succ_of_le_consolidated188 S hb
      calc S.detachedToCoprod s a hsa ≫ S.detachedCoprodMapOfLE (Nat.le_succ_of_le hb)
          = S.detachedToCoprod s a hsa ≫ (S.detachedCoprodMapOfLE hb ≫ S.detachedCoprodInl b) :=
            congrArg
              (fun t : S.detachedCoprod a ⟶ S.detachedCoprod (b + 1) => S.detachedToCoprod s a hsa ≫ t) h1
        _ = (S.detachedToCoprod s a hsa ≫ S.detachedCoprodMapOfLE hb) ≫ S.detachedCoprodInl b :=
            (Category.assoc _ _ _).symm
        _ = S.detachedToCoprod s b (lt_of_lt_of_le hsa hb) ≫ S.detachedCoprodInl b :=
            congrArg (fun t : S.detachedScheme s ⟶ S.detachedCoprod b => t ≫ S.detachedCoprodInl b) ih
        _ = S.detachedToCoprod s (b + 1) (lt_of_lt_of_le hsa (Nat.le_succ_of_le hb)) :=
            (S.detachedToCoprod_succ_of_lt s b (lt_of_lt_of_le hsa hb)).symm

theorem detachedCoprodMapOfLE_inr_totalMapOfLE {a b : ℕ} (hab : a ≤ b) :
    S.detachedCoprodMapOfLE hab ≫ (coprod.inr : S.detachedCoprod b ⟶ S.totalSpace b) ≫ S.totalMapOfLE hab =
      (coprod.inr : S.detachedCoprod a ⟶ S.totalSpace a) := by
  induction b, hab using Nat.le_induction with
  | base =>
      rw [S.detachedCoprodMapOfLE_self a, S.totalMapOfLE_self a, Category.id_comp, Category.comp_id]
  | succ b hb ih =>
      rw [detachedCoprodMapOfLE_succ_of_le_consolidated188 S hb, totalMapOfLE_succ_of_le_consolidated188 S hb, Category.assoc,
        S.detachedCoprodInl_inr_totalTransition_assoc b (S.totalMapOfLE hb), ih]

theorem comapAmbientCenter_le_centerOffDetached (i : ℕ) :
    S.comapAmbientCenter i ≤ S.centerOffDetached i := by
  have h : S.centerOffDetached i =
      ((S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι).map (S.detachedClosureCompl i).ι := rfl
  rw [h]
  exact Scheme.IdealSheafData.le_map_iff_comap_le.mpr le_rfl

private theorem hom_comp_base_apply_consolidated188 {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (x : ↥A) : ⇑(f ≫ g).base x = ⇑g.base (⇑f.base x) := rfl

theorem support_centerOffDetached_subset_preimage (i : ℕ) :
    ((S.centerOffDetached i).support : Set ↥(S.strictTransform i)) ⊆
      ⇑(S.strictTransformι i).base ⁻¹' ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
  have h1 : (S.ambientCenter i).comap (S.strictTransformι i) ≤ S.centerOffDetached i :=
    S.comapAmbientCenter_le_centerOffDetached i
  have h2 : S.ambientCenter i ≤ (S.centerOffDetached i).map (S.strictTransformι i) :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr h1
  have hu : (S.centerOffDetached i).subschemeMap (S.ambientCenter i) (S.strictTransformι i) h2 ≫
        (S.ambientCenter i).subschemeι =
      (S.centerOffDetached i).subschemeι ≫ S.strictTransformι i :=
    Scheme.IdealSheafData.subschemeMap_subschemeι ..
  intro x hx
  rw [← Scheme.IdealSheafData.range_subschemeι] at hx
  obtain ⟨z, rfl⟩ := hx
  have key : ⇑((S.centerOffDetached i).subschemeMap (S.ambientCenter i) (S.strictTransformι i) h2 ≫
        (S.ambientCenter i).subschemeι).base z =
      ⇑((S.centerOffDetached i).subschemeι ≫ S.strictTransformι i).base z := by
    rw [hu]
  rw [hom_comp_base_apply_consolidated188, hom_comp_base_apply_consolidated188] at key
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨_, key⟩

end EmbeddedBlowupSequence

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]

section
variable (S : EmbeddedBlowupSequence k Y pY) (h : S.TransitionsAreBlowups)

theorem inducedBlowups_blowupMorphism (i : ℕ) :
    (S.inducedBlowups h).transitionMapSucc i = S.totalTransition i := by
  have h1 : (S.inducedBlowups h).transitionMapSucc i = (S.inducedBlowups h).transitionMap (Nat.le_succ i) :=
    SequenceOfBlowups.blowupMorphism_eq_transitionMap (S.inducedBlowups h) i
  have h2 : (S.inducedBlowups h).transitionMap (Nat.le_succ i)
      = (S.inducedBlowups h).tower.map (homOfLE (Nat.le_succ i)).op :=
    SequenceOfBlowups.transitionMap_def (S.inducedBlowups h) (Nat.le_succ i)
  rw [h1, h2]
  exact S.totalTower_map_succ i

theorem inducedBlowups_transitionMap {a b : ℕ}
    (hab : a ≤ b) : (S.inducedBlowups h).transitionMap hab = S.totalMapOfLE hab := by
  induction b, hab using Nat.le_induction with
  | base =>
      have h1 : (S.inducedBlowups h).transitionMap (Nat.le_refl a) = 𝟙 ((S.inducedBlowups h).tower.obj (op a)) :=
        (SequenceOfBlowups.transitionMap_def (S.inducedBlowups h) (Nat.le_refl a)).trans
          ((S.inducedBlowups h).tower.map_id (op a))
      exact h1.trans (S.totalMapOfLE_self a).symm
  | succ b hb ih =>
      have e1 : (S.inducedBlowups h).transitionMap (hb.trans (Nat.le_succ b))
          = (S.inducedBlowups h).transitionMap (Nat.le_succ b) ≫ (S.inducedBlowups h).transitionMap hb :=
        (SequenceOfBlowups.transitionMap_trans (S.inducedBlowups h) hb (Nat.le_succ b)).symm
      have e2 : (S.inducedBlowups h).transitionMap (Nat.le_succ b) = S.totalTransition b :=
        (SequenceOfBlowups.blowupMorphism_eq_transitionMap (S.inducedBlowups h) b).symm.trans (inducedBlowups_blowupMorphism S h b)
      have e3 : S.totalMapOfLE (hb.trans (Nat.le_succ b)) = S.totalTransition b ≫ S.totalMapOfLE hb :=
        S.totalMapOfLE_succ hb
      have e4 : (S.inducedBlowups h).transitionMap (Nat.le_succ b) ≫ (S.inducedBlowups h).transitionMap hb
          = S.totalTransition b ≫ S.totalMapOfLE hb := by
        rw [e2, ih]
        exact rfl
      exact (e1.trans e4).trans e3.symm

theorem detachedToCoprod_inr_inducedBlowups_projectionToBase (s i : ℕ) (hs : s < i) :
    S.detachedToCoprod s i hs ≫ (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫
        (S.inducedBlowups h).projectionToBase i =
      S.detachedι s ≫ S.strictTransformToBase s := by
  have hdown : (S.inducedBlowups h).transitionMap (Nat.zero_le i) = S.totalMapOfLE (Nat.zero_le i) :=
    inducedBlowups_transitionMap S h (Nat.zero_le i)
  have hstruct : (S.inducedBlowups h).projectionToBase i
      = S.totalMapOfLE (Nat.zero_le i) ≫ S.totalSpaceZeroIso.hom :=
    Eq.trans (SequenceOfBlowups.projectionToBase_def (S.inducedBlowups h) i)
      (congrArg (fun t : S.totalSpace i ⟶ S.totalSpace 0 => t ≫ S.totalSpaceZeroIso.hom) hdown)
  have hkey := S.detachedToCoprod_inr_totalMapOfLE (Nat.zero_le i) (Nat.zero_le s) hs
  calc S.detachedToCoprod s i hs ≫ (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫
        (S.inducedBlowups h).projectionToBase i
      = (S.detachedToCoprod s i hs ≫ (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫
          S.totalMapOfLE (Nat.zero_le i)) ≫ S.totalSpaceZeroIso.hom := by
        rw [hstruct]; simp only [Category.assoc]
    _ = (S.detachedι s ≫ S.strictTransformMapOfLE (Nat.zero_le s) ≫
          (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0)) ≫ S.totalSpaceZeroIso.hom := by
        rw [hkey]
    _ = S.detachedι s ≫ S.strictTransformMapOfLE (Nat.zero_le s) ≫
          ((coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom) := by
        simp only [Category.assoc]
    _ = S.detachedι s ≫ S.strictTransformMapOfLE (Nat.zero_le s) ≫ S.strictTransformZeroIso.hom := by
        rw [S.inl_totalSpaceZeroIso_hom]
    _ = S.detachedι s ≫ S.strictTransformToBase s := rfl

theorem inl_inducedBlowups_projectionToBase (i : ℕ) :
    (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ (S.inducedBlowups h).projectionToBase i =
      S.strictTransformToBase i := by
  have hdown : (S.inducedBlowups h).transitionMap (Nat.zero_le i) = S.totalMapOfLE (Nat.zero_le i) :=
    inducedBlowups_transitionMap S h (Nat.zero_le i)
  have hstruct : (S.inducedBlowups h).projectionToBase i
      = S.totalMapOfLE (Nat.zero_le i) ≫ S.totalSpaceZeroIso.hom :=
    Eq.trans (SequenceOfBlowups.projectionToBase_def (S.inducedBlowups h) i)
      (congrArg (fun t : S.totalSpace i ⟶ S.totalSpace 0 => t ≫ S.totalSpaceZeroIso.hom) hdown)
  calc (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ (S.inducedBlowups h).projectionToBase i
      = ((coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ S.totalMapOfLE (Nat.zero_le i)) ≫
          S.totalSpaceZeroIso.hom := by
        rw [hstruct]; simp only [Category.assoc]
    _ = (S.strictTransformMapOfLE (Nat.zero_le i) ≫ (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0)) ≫
          S.totalSpaceZeroIso.hom := by
        rw [S.inl_totalMapOfLE (Nat.zero_le i)]
    _ = S.strictTransformMapOfLE (Nat.zero_le i) ≫
          ((coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom) :=
        Category.assoc _ _ _
    _ = S.strictTransformMapOfLE (Nat.zero_le i) ≫ S.strictTransformZeroIso.hom := by
        rw [S.inl_totalSpaceZeroIso_hom]
    _ = S.strictTransformToBase i := rfl


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DiscardedLocus
section

open CategoryTheory.Limits TopologicalSpace

section

section
variable {A B : Scheme.{u}} (f : A ⟶ B)

private theorem noetherianSpace_of_isClosedImmersion_consolidated214 [IsClosedImmersion f]
    (h : TopologicalSpace.NoetherianSpace ↥B) : TopologicalSpace.NoetherianSpace ↥A := by
  have := h
  exact (Scheme.Hom.isClosedEmbedding f).toIsEmbedding.toIsInducing.noetherianSpace

private theorem noetherianSpace_of_isOpenImmersion_consolidated214 [IsOpenImmersion f]
    (h : TopologicalSpace.NoetherianSpace ↥B) : TopologicalSpace.NoetherianSpace ↥A := by
  have := h
  exact f.isOpenEmbedding.toIsEmbedding.toIsInducing.noetherianSpace


end

private theorem range_comp_base_consolidated214 {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range ⇑(f ≫ g).base = ⇑g.base '' Set.range ⇑f.base := by
  ext x
  simp [Set.range_comp]

private theorem quasiCompact_strictTransformι_of_noetherianSpace_source_consolidated214 {X X₁ : Scheme.{u}}
    (π : X₁ ⟶ X) (Z D : X.IdealSheafData) (h : TopologicalSpace.NoetherianSpace ↥X₁) :
    QuasiCompact (strictTransformι π Z D) := by
  have := noetherianSpace_of_isOpenImmersion_consolidated214 (Scheme.Opens.ι (strictTransformOpens π Z D))
    (noetherianSpace_of_isClosedImmersion_consolidated214 (D.comap π).subschemeι h)
  infer_instance

private theorem ker_eq_ker_of_iso_hom_comp_consolidated214 {A B T : Scheme.{u}} (f : A ⟶ T) (g : B ⟶ T)
    (e : A ≅ B) (h : e.hom ≫ g = f) : Scheme.Hom.ker f = Scheme.Hom.ker g := by
  have : CategoryTheory.IsIso e.hom := ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  exact ker_eq_ker_of_isIso_comp f g e.hom h

private theorem ker_comp_comap_ι_eq_of_preimage_subset_consolidated214 {A X : Scheme.{u}} (a : A ⟶ X)
    (U : X.Opens) (V : A.Opens)
    (hle : ((a ⁻¹ᵁ U : A.Opens) : Set ↥A) ⊆ ((V : A.Opens) : Set ↥A))
    [QuasiCompact a]
    [QuasiCompact (Scheme.Opens.ι V ≫ a)] :
    (Scheme.Hom.ker (Scheme.Opens.ι V ≫ a)).comap (Scheme.Opens.ι U)
      = (Scheme.Hom.ker a).comap (Scheme.Opens.ι U) := by
  have hcoePre : ((Scheme.Opens.ι V ⁻¹ᵁ (a ⁻¹ᵁ U) : (V.toScheme).Opens) :
        Set ↥(V.toScheme))
      = ⇑(Scheme.Opens.ι V).base ⁻¹' ((a ⁻¹ᵁ U : A.Opens) : Set ↥A) := rfl
  have hrangeV : Set.range ⇑(Scheme.Opens.ι V).base = ((V : A.Opens) : Set ↥A) :=
    Scheme.Opens.range_ι V
  have hrange : Set.range
        ⇑(Scheme.Opens.ι (Scheme.Opens.ι V ⁻¹ᵁ (a ⁻¹ᵁ U)) ≫ Scheme.Opens.ι V).base
      = Set.range ⇑(Scheme.Opens.ι (a ⁻¹ᵁ U)).base := by
    rw [range_comp_base_consolidated214, Scheme.Opens.range_ι, Scheme.Opens.range_ι, hcoePre,
      Set.image_preimage_eq_inter_range, hrangeV, Set.inter_eq_self_of_subset_left hle]
  have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac
      (Scheme.Opens.ι (Scheme.Opens.ι V ⁻¹ᵁ (a ⁻¹ᵁ U)) ≫ Scheme.Opens.ι V)
      (Scheme.Opens.ι (a ⁻¹ᵁ U)) hrange
  have h1 : ((Scheme.Opens.ι V ≫ a) ∣_ U) ≫ Scheme.Opens.ι U
      = Scheme.Opens.ι (Scheme.Opens.ι V ⁻¹ᵁ (a ⁻¹ᵁ U)) ≫ (Scheme.Opens.ι V ≫ a) :=
    morphismRestrict_ι (Scheme.Opens.ι V ≫ a) U
  have hcomm : (IsOpenImmersion.isoOfRangeEq
        (Scheme.Opens.ι (Scheme.Opens.ι V ⁻¹ᵁ (a ⁻¹ᵁ U)) ≫ Scheme.Opens.ι V)
        (Scheme.Opens.ι (a ⁻¹ᵁ U)) hrange).hom ≫ (a ∣_ U)
      = (Scheme.Opens.ι V ≫ a) ∣_ U := by
    refine (cancel_mono (Scheme.Opens.ι U)).mp ?_
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hfac]
    exact (Category.assoc _ _ _).trans h1.symm
  rw [ker_comap_ι_eq_ker_morphismRestrict (Scheme.Opens.ι V ≫ a) U,
    ker_comap_ι_eq_ker_morphismRestrict a U]
  exact ker_eq_ker_of_iso_hom_comp_consolidated214 _ _ _ hcomm

private theorem exists_iso_subscheme_of_ideal_eq_consolidated214 {X : Scheme.{u}} {J J' : X.IdealSheafData} (h : J = J')
    {T : Scheme.{u}} (f : T ⟶ X)
    (he : ∃ e : J'.subscheme ≅ T, e.hom ≫ f = J'.subschemeι) :
    ∃ e : J.subscheme ≅ T, e.hom ≫ f = J.subschemeι := by
  subst h
  exact he

private theorem image_mem_irreducibleComponents_of_isOpenEmbedding_consolidated214 {A B : Type u} [TopologicalSpace A]
    [TopologicalSpace B] (f : A → B) (hf : Topology.IsOpenEmbedding f)
    (hcl : IsClosed (Set.range f)) {T : Set A} (hT : T ∈ irreducibleComponents A) :
    f '' T ∈ irreducibleComponents B := by
  have hTirr : IsIrreducible T := hT.1
  have hmax : ∀ ⦃D : Set B⦄, IsIrreducible D → f '' T ≤ D → D ≤ f '' T := by
    intro D hD hsubD
    have hDr : D ⊆ Set.range f := by
      by_contra hcon
      obtain ⟨z, hzD, hz⟩ := Set.not_subset.mp hcon
      obtain ⟨a0, ha0⟩ := hTirr.1
      have hw : (D ∩ Set.range f).Nonempty := ⟨f a0, hsubD ⟨a0, ha0, rfl⟩, ⟨a0, rfl⟩⟩
      obtain ⟨y, -, hy1, hy2⟩ :=
        hD.2 (Set.range f) (Set.range f)ᶜ hf.isOpen_range hcl.isOpen_compl hw ⟨z, hzD, hz⟩
      exact hy2 hy1
    have hpre : IsIrreducible (f ⁻¹' D) := by
      constructor
      · obtain ⟨b, hb⟩ := hD.1
        obtain ⟨a, rfl⟩ := hDr hb
        exact ⟨a, hb⟩
      · intro O₁ O₂ hO₁ hO₂ h₁ h₂
        obtain ⟨x₁, hx₁D, hx₁O⟩ := h₁
        obtain ⟨x₂, hx₂D, hx₂O⟩ := h₂
        obtain ⟨y, hyD, hy1, hy2⟩ :=
          hD.2 (f '' O₁) (f '' O₂) (hf.isOpenMap _ hO₁) (hf.isOpenMap _ hO₂)
            ⟨f x₁, hx₁D, ⟨x₁, hx₁O, rfl⟩⟩ ⟨f x₂, hx₂D, ⟨x₂, hx₂O, rfl⟩⟩
        obtain ⟨a₁, ha₁, ha₁e⟩ := hy1
        obtain ⟨a₂, ha₂, ha₂e⟩ := hy2
        refine ⟨a₂, ?_, ?_, ha₂⟩
        · show f a₂ ∈ D
          rw [ha₂e]
          exact hyD
        · have hEq : a₂ = a₁ := hf.injective (ha₂e.trans ha₁e.symm)
          rw [hEq]
          exact ha₁
    have hTle : T ≤ f ⁻¹' D := fun x hx => hsubD ⟨x, hx, rfl⟩
    intro y hy
    obtain ⟨a, rfl⟩ := hDr hy
    exact ⟨a, hT.2 hpre hTle hy, rfl⟩
  exact ⟨hTirr.image f hf.continuous.continuousOn, hmax⟩

private def coprodSwapAssocHom_consolidated214 (A F G : Scheme.{u}) : (A ⨿ (F ⨿ G)) ⟶ ((A ⨿ G) ⨿ F) :=
  coprod.desc (coprod.inl ≫ coprod.inl) (coprod.desc coprod.inr (coprod.inr ≫ coprod.inl))

private def coprodSwapAssocInv_consolidated214 (A F G : Scheme.{u}) : ((A ⨿ G) ⨿ F) ⟶ (A ⨿ (F ⨿ G)) :=
  coprod.desc (coprod.desc coprod.inl (coprod.inr ≫ coprod.inr)) (coprod.inl ≫ coprod.inr)

private theorem isIso_coprodSwapAssocHom_consolidated214 (A F G : Scheme.{u}) :
    CategoryTheory.IsIso (coprodSwapAssocHom_consolidated214 A F G) := by
  refine ⟨⟨coprodSwapAssocInv_consolidated214 A F G, ?_, ?_⟩⟩
  · refine coprod.hom_ext ?_ (coprod.hom_ext ?_ ?_) <;>
      simp only [coprodSwapAssocHom_consolidated214, coprodSwapAssocInv_consolidated214, Category.assoc, coprod.inl_desc,
        coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.comp_id]
  · refine coprod.hom_ext (coprod.hom_ext ?_ ?_) ?_ <;>
      simp only [coprodSwapAssocHom_consolidated214, coprodSwapAssocInv_consolidated214, Category.assoc, coprod.inl_desc,
        coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.comp_id]

private theorem isBlowupAlongIdealSheaf_coprodDesc_coprod_consolidated214 {A B F G : Scheme.{u}} (a : A ⟶ B) (g : G ⟶ B)
    (K : B.IdealSheafData) (J : (B ⨿ F).IdealSheafData)
    (hinl : J.comap (coprod.inl : B ⟶ B ⨿ F) = K)
    (hinr : J.comap (coprod.inr : F ⟶ B ⨿ F) = ⊤)
    (h : Blowup.IsBlowupAlongIdealSheaf (coprod.desc a g) K) :
    Blowup.IsBlowupAlongIdealSheaf (coprod.desc (a ≫ (coprod.inl : B ⟶ B ⨿ F))
      (coprod.desc (coprod.inr : F ⟶ B ⨿ F) (g ≫ (coprod.inl : B ⟶ B ⨿ F)))) J := by
  have hmap : Blowup.IsBlowupAlongIdealSheaf (coprod.map (coprod.desc a g) (𝟙 F)) J := by
    refine Blowup.IsBlowupAlongIdealSheaf.coprod ?_ ?_
    · rw [hinl]
      exact h
    · rw [hinr]
      exact Blowup.isBlowupAlongIdealSheaf_id_top _
  have := isIso_coprodSwapAssocHom_consolidated214 A F G
  have hfac : coprodSwapAssocHom_consolidated214 A F G ≫ coprod.map (coprod.desc a g) (𝟙 F)
      = coprod.desc (a ≫ (coprod.inl : B ⟶ B ⨿ F))
        (coprod.desc (coprod.inr : F ⟶ B ⨿ F) (g ≫ (coprod.inl : B ⟶ B ⨿ F))) := by
    refine coprod.hom_ext ?_ (coprod.hom_ext ?_ ?_) <;>
      simp only [coprodSwapAssocHom_consolidated214, Category.assoc, coprod.inl_desc, coprod.inr_desc,
        coprod.inl_desc_assoc, coprod.inr_desc_assoc, coprod.inl_map, coprod.inr_map,
        Category.id_comp]
  exact isBlowupAlongIdealSheaf_of_isIso_comp _ _ (coprodSwapAssocHom_consolidated214 A F G) hfac _ hmap

namespace AffineSpacePrincipalizationData

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)

theorem strictTransformIdeal_succ_eq_strictTransform (i : ℕ) :
    S.strictTransformIdeal (i + 1) =
      Blowup.strictTransform (S.ambientBlowupMorphism i) (S.ambientCenter i) (S.strictTransformIdeal i) :=
  S.strictTransformIdeal_succ i

section
variable (j : ℕ)

theorem strictTransformι_eq_subschemeι : S.strictTransformι j = (S.strictTransformIdeal j).subschemeι := rfl

theorem noetherianSpace_strictTransform_of_ambientLevel (h : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel j)) :
    TopologicalSpace.NoetherianSpace ↥(S.strictTransform j) :=
  noetherianSpace_of_isClosedImmersion_consolidated214 (S.strictTransformι j) h


end

def discardedLocusOpens (i : ℕ) (h : IsOpen (S.discardedLocus i)) : (S.strictTransform i).Opens :=
  ⟨S.discardedLocus i, h⟩

section
variable (i : ℕ)

theorem image_discardedLocus_subset_support :
    ⇑(S.strictTransformι i).base '' (S.discardedLocus i) ⊆
      ((S.ambientCenter i).support : Set ↥(S.ambientLevel i)) := by
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp hx
  exact ((S.mem_discardedComponents_iff i C).mp hC).2 (Set.mem_image_of_mem _ hxC)

theorem range_strictTransformMap_subset_discardedLocusClosureCompl (_hi : i < S.ambientLength)
    (hN : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i))
    (hN' : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel (i + 1)))
    (hopen : IsOpen (S.discardedLocus i)) :
    Set.range ⇑(S.strictTransformMap i).base ⊆
      ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
  have := hN
  have hqc : QuasiCompact
      (EmbeddedResolution.strictTransformι (S.ambientBlowupMorphism i) (S.ambientCenter i) (S.strictTransformIdeal i)) :=
    quasiCompact_strictTransformι_of_noetherianSpace_source_consolidated214 _ _ _ hN'
  have hιemb : Topology.IsClosedEmbedding ⇑(S.strictTransformι i).base :=
    Scheme.Hom.isClosedEmbedding (S.strictTransformι i)
  have hUcoe : ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))
      = (S.discardedLocus i)ᶜ := by
    rw [S.coe_discardedLocusClosureCompl i, S.coe_discardedLocusClosure i]
  have hRclosed : IsClosed (⇑(S.strictTransformι i).base ''
      ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))) := by
    refine hιemb.isClosedMap _ ?_
    rw [hUcoe]
    exact hopen.isClosed_compl
  have hsub : (((S.strictTransformIdeal i).support : Set ↥(S.ambientLevel i)) \
        ((S.ambientCenter i).support : Set ↥(S.ambientLevel i)))
      ⊆ ⇑(S.strictTransformι i).base ''
        ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
    rintro w ⟨hw, hw'⟩
    have hw2 : w ∈ Set.range ⇑(S.strictTransformι i).base := by
      rw [Scheme.IdealSheafData.range_subschemeι (S.strictTransformIdeal i)]
      exact hw
    obtain ⟨z, rfl⟩ := hw2
    refine ⟨z, ?_, rfl⟩
    rw [hUcoe]
    intro hz
    exact hw' (S.image_discardedLocus_subset_support i ⟨z, hz, rfl⟩)
  have hcl : closure (⇑(S.ambientBlowupMorphism i).base ⁻¹'
        (((S.strictTransformIdeal i).support : Set ↥(S.ambientLevel i)) \
          ((S.ambientCenter i).support : Set ↥(S.ambientLevel i))))
      ⊆ ⇑(S.ambientBlowupMorphism i).base ⁻¹' (⇑(S.strictTransformι i).base ''
        ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))) :=
    closure_minimal (Set.preimage_mono hsub)
      (hRclosed.preimage (S.ambientBlowupMorphism i).base.hom.continuous)
  rintro _ ⟨x, rfl⟩
  have h1 : ⇑(S.strictTransformι (i + 1)).base x ∈
      ((S.strictTransformIdeal (i + 1)).support : Set ↥(S.ambientLevel (i + 1))) := by
    rw [← Scheme.IdealSheafData.range_subschemeι (S.strictTransformIdeal (i + 1))]
    exact Set.mem_range_self x
  rw [S.strictTransformIdeal_succ i, support_strictTransform_eq_closure_preimage] at h1
  have h2 := hcl h1
  have he : ⇑(S.strictTransformι i).base (⇑(S.strictTransformMap i).base x)
      = ⇑(S.ambientBlowupMorphism i).base (⇑(S.strictTransformι (i + 1)).base x) := by
    have h := congrArg (fun m : S.strictTransform (i + 1) ⟶ S.ambientLevel i => ⇑m.base x) (S.strictTransformMap_comp_strictTransformι i)
    simpa using h
  have h3 : ⇑(S.strictTransformι i).base (⇑(S.strictTransformMap i).base x) ∈
      ⇑(S.strictTransformι i).base ''
        ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
    rw [he]
    exact h2
  obtain ⟨z, hz, hzeq⟩ := h3
  have hzz : z = ⇑(S.strictTransformMap i).base x := hιemb.injective hzeq
  rw [← hzz]
  exact hz


end

section
variable (i : ℕ) [IsReduced (S.strictTransform i)] (hN : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i)) (hopen : IsOpen (S.discardedLocus i))
include hN hopen

theorem exists_iso_discardedSubscheme_discardedLocusOpens :
    ∃ e : S.discardedSubscheme i ≅ Scheme.Opens.toScheme (S.discardedLocusOpens i hopen),
      e.hom ≫ Scheme.Opens.ι (S.discardedLocusOpens i hopen) = S.discardedι i := by
  have := hN
  have hC : IsClosed ((S.discardedLocusOpens i hopen : (S.strictTransform i).Opens) :
      Set ↥(S.strictTransform i)) := S.isClosed_discardedLocus i
  have hIeq : S.discardedIdeal i
      = Scheme.IdealSheafData.vanishingIdeal
          (⟨((S.discardedLocusOpens i hopen : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)), hC⟩ :
            TopologicalSpace.Closeds ↥(S.strictTransform i)) := by
    rw [S.discardedIdeal_eq_vanishingIdeal i]
    congr 1
    exact TopologicalSpace.Closeds.ext (S.coe_discardedLocusClosure i)
  exact exists_iso_subscheme_of_ideal_eq_consolidated214 hIeq _
    (exists_iso_subscheme_vanishingIdeal_of_isClosed (S.discardedLocusOpens i hopen) hC)

private theorem isBlowupAlongIdealSheaf_coprodDesc_of_restrict_consolidated214 (hf : Set.range ⇑(S.strictTransformMap i).base ⊆ Set.range ⇑(S.discardedLocusClosureCompl i).ι.base)
    (hkey : Blowup.IsBlowupAlongIdealSheaf (IsOpenImmersion.lift (S.discardedLocusClosureCompl i).ι (S.strictTransformMap i) hf)
      ((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι)) :
    Blowup.IsBlowupAlongIdealSheaf (coprod.desc (S.strictTransformMap i) (S.discardedι i)) (S.centerOffDetached i) := by
  have := hN
  have hUcoe : ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))
      = (S.discardedLocus i)ᶜ := by
    rw [S.coe_discardedLocusClosureCompl i, S.coe_discardedLocusClosure i]
  have hVcoe : ((S.discardedLocusOpens i hopen : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))
      = S.discardedLocus i := rfl
  have hcompl : IsCompl (S.discardedLocusClosureCompl i) (S.discardedLocusOpens i hopen) := by
    constructor
    · rw [disjoint_iff]
      refine TopologicalSpace.Opens.ext ?_
      rw [TopologicalSpace.Opens.coe_inf, hUcoe, hVcoe, TopologicalSpace.Opens.coe_bot]
      exact Set.compl_inter_self _
    · rw [codisjoint_iff]
      refine TopologicalSpace.Opens.ext ?_
      rw [TopologicalSpace.Opens.coe_sup, hUcoe, hVcoe, TopologicalSpace.Opens.coe_top]
      exact Set.compl_union_self _
  obtain ⟨e', he'⟩ := S.exists_iso_discardedSubscheme_discardedLocusOpens i hN hopen
  have hg : Set.range ⇑(S.discardedι i).base ⊆ Set.range ⇑(S.discardedLocusOpens i hopen).ι.base := by
    rw [← he']
    rintro _ ⟨z, rfl⟩
    exact ⟨⇑e'.hom.base z, by simp⟩
  have hliftV : IsOpenImmersion.lift (S.discardedLocusOpens i hopen).ι (S.discardedι i) hg = e'.hom := by
    refine (cancel_mono (S.discardedLocusOpens i hopen).ι).mp ?_
    rw [IsOpenImmersion.lift_fac, he']
  have : CategoryTheory.IsIso
      (IsOpenImmersion.lift (S.discardedLocusOpens i hopen).ι (S.discardedι i) hg) := by
    rw [hliftV]
    infer_instance
  have hNU : TopologicalSpace.NoetherianSpace ↥((S.discardedLocusClosureCompl i).toScheme) :=
    noetherianSpace_of_isOpenImmersion_consolidated214 (S.discardedLocusClosureCompl i).ι hN
  have hNsub : TopologicalSpace.NoetherianSpace
      ↥(((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subscheme) :=
    noetherianSpace_of_isClosedImmersion_consolidated214
      ((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι hNU
  have hq1 : QuasiCompact
      ((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι := inferInstance
  have hq2 : QuasiCompact
      (((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι ≫
        (S.discardedLocusClosureCompl i).ι) := inferInstance
  have hJU : (S.centerOffDetached i).comap (S.discardedLocusClosureCompl i).ι
      = (S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι := by
    rw [S.centerOffDetached_eq i]
    exact comap_ker_subschemeι_comp _ _
  have hJV : (S.centerOffDetached i).comap (S.discardedLocusOpens i hopen).ι = ⊤ := by
    rw [S.centerOffDetached_eq i]
    refine Blowup.comap_eq_top_of_notMem_support _ _ ?_
    intro x hx
    have hx' : ⇑(S.discardedLocusOpens i hopen).ι.base x ∈
        ((Scheme.Hom.ker (((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι ≫
          (S.discardedLocusClosureCompl i).ι)).support : Set ↥(S.strictTransform i)) := hx
    rw [Scheme.Hom.support_ker (((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι ≫
      (S.discardedLocusClosureCompl i).ι)] at hx'
    have hsubU : Set.range ⇑((((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι ≫
        (S.discardedLocusClosureCompl i).ι)).base
        ⊆ ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
      rw [← Scheme.Opens.range_ι (S.discardedLocusClosureCompl i)]
      rintro _ ⟨z, rfl⟩
      exact ⟨⇑(((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι).base z, by simp⟩
    have hclosedU : IsClosed
        ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
      rw [hUcoe]
      exact hopen.isClosed_compl
    have hmem := closure_minimal hsubU hclosedU hx'
    rw [hUcoe] at hmem
    refine hmem ?_
    have h0 : ⇑(S.discardedLocusOpens i hopen).ι.base x ∈
        Set.range ⇑(S.discardedLocusOpens i hopen).ι.base := Set.mem_range_self x
    rw [Scheme.Opens.range_ι] at h0
    exact h0
  have hoi : ∀ b : Bool, IsOpenImmersion
      (Bool.rec (motive := fun b : Bool =>
          (cond b (S.discardedLocusClosureCompl i).toScheme (S.discardedLocusOpens i hopen).toScheme) ⟶ S.strictTransform i)
        (S.discardedLocusOpens i hopen).ι (S.discardedLocusClosureCompl i).ι b) := by
    intro b
    cases b
    · exact inferInstanceAs
        (IsOpenImmersion (S.discardedLocusOpens i hopen).ι)
    · exact inferInstanceAs (IsOpenImmersion (S.discardedLocusClosureCompl i).ι)
  refine Blowup.IsBlowupAlongIdealSheaf.of_comap_of_isOpenImmersion_cover _ _
    (fun b : Bool => cond b (S.discardedLocusClosureCompl i).toScheme (S.discardedLocusOpens i hopen).toScheme)
    (Bool.rec (motive := fun b : Bool =>
        (cond b (S.discardedLocusClosureCompl i).toScheme (S.discardedLocusOpens i hopen).toScheme) ⟶ S.strictTransform i)
      (S.discardedLocusOpens i hopen).ι (S.discardedLocusClosureCompl i).ι) ?_ ?_
  · intro x
    by_cases hx : x ∈ S.discardedLocus i
    · refine ⟨false, ?_⟩
      show x ∈ Set.range ⇑(S.discardedLocusOpens i hopen).ι.base
      rw [Scheme.Opens.range_ι]
      exact hx
    · refine ⟨true, ?_⟩
      show x ∈ Set.range ⇑(S.discardedLocusClosureCompl i).ι.base
      rw [Scheme.Opens.range_ι, hUcoe]
      exact hx
  · intro b
    cases b
    · show Blowup.IsBlowupAlongIdealSheaf (pullback.snd (coprod.desc (S.strictTransformMap i) (S.discardedι i))
        (S.discardedLocusOpens i hopen).ι) ((S.centerOffDetached i).comap (S.discardedLocusOpens i hopen).ι)
      rw [hJV]
      obtain ⟨e, he1, _⟩ :=
        Blowup.exists_iso_pullback_coprod_desc_right (S.strictTransformMap i) (S.discardedι i) hcompl hf hg
      have : CategoryTheory.IsIso (pullback.snd (coprod.desc (S.strictTransformMap i) (S.discardedι i))
          (S.discardedLocusOpens i hopen).ι) := by
        rw [← he1]
        infer_instance
      exact Blowup.IsBlowupAlongIdealSheaf.of_isIso _
    · show Blowup.IsBlowupAlongIdealSheaf (pullback.snd (coprod.desc (S.strictTransformMap i) (S.discardedι i))
        (S.discardedLocusClosureCompl i).ι) ((S.centerOffDetached i).comap (S.discardedLocusClosureCompl i).ι)
      rw [hJU]
      obtain ⟨e, he1, _⟩ :=
        Blowup.exists_iso_pullback_coprod_desc_left (S.strictTransformMap i) (S.discardedι i) hcompl hf hg
      exact isBlowupAlongIdealSheaf_of_isIso_comp _ _ e.hom he1 _ hkey


end

theorem isReduced_strictTransform [IsReduced Y]
    (hN : ∀ j, j ≤ S.ambientLength → IsNoetherian (S.ambientLevel j))
    (j : ℕ) (hj : j ≤ S.ambientLength) :
    IsReduced (S.strictTransform j) := by
  revert hj
  induction j with
  | zero =>
    intro _
    have := S.emb_closedImmersion
    have hq : QuasiCompact (S.emb ≫ S.ambientBlowups.isoZero.inv) := inferInstance
    exact isReduced_subscheme_ker (S.emb ≫ S.ambientBlowups.isoZero.inv)
  | succ n ih =>
    intro hj
    have hn : n < S.ambientLength := Nat.lt_of_succ_le hj
    have : IsReduced (S.strictTransformIdeal n).subscheme := ih (le_of_lt hn)
    have hNoeth : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel (n + 1)) := by
      have : IsNoetherian (S.ambientLevel (n + 1)) := hN (n + 1) hj
      infer_instance
    have : QuasiCompact
        (EmbeddedResolution.strictTransformι (S.ambientBlowupMorphism n) (S.ambientCenter n) (S.strictTransformIdeal n)) :=
      quasiCompact_strictTransformι_of_noetherianSpace_source_consolidated214 _ _ _ hNoeth
    exact isReduced_subscheme_strictTransform (S.ambientBlowupMorphism n) (S.ambientCenter n)
      (S.strictTransformIdeal n) (S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn)

theorem isBlowupAlongIdealSheaf_transitionMap_of_coprodDesc (i : ℕ)
    (h : Blowup.IsBlowupAlongIdealSheaf (coprod.desc (S.strictTransformMap i) (S.discardedι i)) (S.centerOffDetached i)) :
    Blowup.IsBlowupAlongIdealSheaf (S.transitionMap i) (S.centerOnTotalSpace i) := by
  have hq1 : QuasiCompact (S.centerOffDetached i).subschemeι := inferInstance
  have hq2 : QuasiCompact ((S.centerOffDetached i).subschemeι ≫
      (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) := by
    have : QuasiCompact
        (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) := Blowup.instQuasiCompactCoprodInl _ _
    infer_instance
  have hinl : (S.centerOnTotalSpace i).comap (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)
      = S.centerOffDetached i := by
    rw [S.centerOnTotalSpace_eq_ker i, Blowup.ker_comp_coprod_inl_comap_inl,
      Scheme.IdealSheafData.ker_subschemeι]
  have hinr : (S.centerOnTotalSpace i).comap (coprod.inr : S.discardedUnion i ⟶ S.totalSpace i) = ⊤ := by
    rw [S.centerOnTotalSpace_eq_ker i]
    exact Blowup.ker_comp_coprod_inl_comap_inr _
  exact isBlowupAlongIdealSheaf_coprodDesc_coprod_consolidated214 (S.strictTransformMap i) (S.discardedι i) (S.centerOffDetached i) (S.centerOnTotalSpace i)
    hinl hinr h

private theorem isBlowupAlongIdealSheaf_lift_discardedLocusClosureCompl_consolidated214 (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (i : ℕ)
    (hi : i < S.ambientLength) (hNlev : IsNoetherian (S.ambientLevel i))
    (hNoetherian : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i))
    (hopen : IsOpen (S.discardedLocus i))
    (hf : Set.range ⇑(S.strictTransformMap i).base ⊆ Set.range ⇑(S.discardedLocusClosureCompl i).ι.base) :
    Blowup.IsBlowupAlongIdealSheaf (IsOpenImmersion.lift (S.discardedLocusClosureCompl i).ι (S.strictTransformMap i) hf)
      ((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι) := by
  have := hNlev
  have := hNoetherian
  have hUcoe : ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))
      = (S.discardedLocus i)ᶜ := by
    rw [S.coe_discardedLocusClosureCompl i, S.coe_discardedLocusClosure i]
  have hUclosed : IsClosed ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) :
      Set ↥(S.strictTransform i)) := by
    rw [hUcoe]
    exact hopen.isClosed_compl
  have hrangeU : Set.range ⇑(S.discardedLocusClosureCompl i).ι.base
      = ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) :=
    Scheme.Opens.range_ι _
  have hclos : IsClosedImmersion ((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i) := by
    refine AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion _ ?_
    have hcl2 : IsClosed (⇑(S.strictTransformι i).base ''
        ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))) :=
      (Scheme.Hom.isClosedEmbedding (S.strictTransformι i)).isClosedMap _ hUclosed
    have hr : Set.range ⇑((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i).base
        = ⇑(S.strictTransformι i).base ''
          ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
      rw [range_comp_base_consolidated214, hrangeU]
    have hfin : IsClosed (Set.range ⇑((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i).base) := by
      rw [hr]
      exact hcl2
    exact hfin
  have hIcomp : ∀ T ∈ irreducibleComponents ↥((S.discardedLocusClosureCompl i).toScheme),
      ¬ (⇑((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i).base '' T
        ⊆ ((S.ambientCenter i).support : Set ↥(S.ambientLevel i))) := by
    intro T hT hsub
    have hCmem : ⇑(S.discardedLocusClosureCompl i).ι.base '' T
        ∈ irreducibleComponents ↥(S.strictTransform i) := by
      refine image_mem_irreducibleComponents_of_isOpenEmbedding_consolidated214 _ (S.discardedLocusClosureCompl i).ι.isOpenEmbedding ?_ hT
      rw [hrangeU]
      exact hUclosed
    have himg : ⇑((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i).base '' T
        = ⇑(S.strictTransformι i).base '' (⇑(S.discardedLocusClosureCompl i).ι.base '' T) := by
      ext y
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨_, ⟨t, ht, rfl⟩, by simp⟩
      · rintro ⟨z, ⟨t, ht, rfl⟩, rfl⟩
        exact ⟨t, ht, by simp⟩
    rw [himg] at hsub
    have hDiscarded : ⇑(S.discardedLocusClosureCompl i).ι.base '' T ∈ S.discardedComponents i := ⟨hCmem, hsub⟩
    obtain ⟨t, ht⟩ := hT.1.1
    have h1 : ⇑(S.discardedLocusClosureCompl i).ι.base t ∈ S.discardedLocus i :=
      Set.subset_sUnion_of_mem hDiscarded ⟨t, ht, rfl⟩
    have h2 : ⇑(S.discardedLocusClosureCompl i).ι.base t
        ∈ ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
      rw [← hrangeU]
      exact Set.mem_range_self t
    rw [hUcoe] at h2
    exact h2 h1
  have hqι : QuasiCompact (S.strictTransformι i) := inferInstance
  have hqj : QuasiCompact ((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i) := inferInstance
  have hOU : ((S.strictTransformι i ⁻¹ᵁ (S.ambientCenter i).support.compl :
        (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))
      ⊆ ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
    intro x hx
    have hx' : ⇑(S.strictTransformι i).base x
        ∉ ((S.ambientCenter i).support : Set ↥(S.ambientLevel i)) := hx
    rw [hUcoe]
    intro hDisc
    exact hx' (S.image_discardedLocus_subset_support i ⟨x, hDisc, rfl⟩)
  have hkerRestr := ker_comp_comap_ι_eq_of_preimage_subset_consolidated214 (S.strictTransformι i) (S.ambientCenter i).support.compl
    (S.discardedLocusClosureCompl i) hOU
  have hKerStrict : Scheme.Hom.ker (S.strictTransformι i) = S.strictTransformIdeal i :=
    Scheme.IdealSheafData.ker_subschemeι (S.strictTransformIdeal i)
  have hST : Blowup.strictTransform (S.ambientBlowupMorphism i) (S.ambientCenter i)
      (Scheme.Hom.ker ((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i)) = S.strictTransformIdeal (i + 1) := by
    rw [S.strictTransformIdeal_succ i]
    refine strictTransform_congr_of_comap_ι_eq (S.ambientBlowupMorphism i) (S.ambientCenter i) _ _ ?_
    rw [hkerRestr, hKerStrict]
  have hstat := hres (S.ambientLevel i) (S.ambientLevel (i + 1)) ((S.discardedLocusClosureCompl i).toScheme)
      ((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i) (S.ambientBlowupMorphism i) (S.ambientCenter i)
      (S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism i hi) hIcomp
  rw [hST] at hstat
  obtain ⟨ψ, hψfac, hψbl⟩ := hstat
  have : Mono ((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i) := inferInstance
  have hψ : ψ = IsOpenImmersion.lift (S.discardedLocusClosureCompl i).ι (S.strictTransformMap i) hf := by
    refine (cancel_mono ((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i)).mp ?_
    rw [hψfac, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact (S.strictTransformMap_comp_strictTransformι i).symm
  rw [hψ] at hψbl
  rw [Scheme.IdealSheafData.comap_comp] at hψbl
  exact hψbl

end AffineSpacePrincipalizationData

def EmbeddedPrincipalizationDiscardedLocusIsOpen (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y] (i : ℕ),
    i < (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength →
      IsOpen ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedLocus i)

def EmbeddedPrincipalizationAmbientIsNoetherian (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y] (i : ℕ),
    i ≤ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength →
      IsNoetherian ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i)

theorem embeddedPrincipalizationYieldsBlowups_of_discardedLocusIsOpen (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (hiso : EmbeddedPrincipalizationDiscardedLocusIsOpen A hemb hsnc hsm)
    (hnoeth : EmbeddedPrincipalizationAmbientIsNoetherian A hemb hsnc hsm)
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) :
    EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  set S := AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY with hSdef
  intro i hi
  have hopen : IsOpen (S.discardedLocus i) := hiso k Y pY i hi
  have hNlev : ∀ j, j ≤ S.ambientLength → TopologicalSpace.NoetherianSpace ↥(S.ambientLevel j) := by
    intro j hj
    have : IsNoetherian (S.ambientLevel j) := hnoeth k Y pY j hj
    infer_instance
  have hNoetherian : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i) :=
    S.noetherianSpace_strictTransform_of_ambientLevel i (hNlev i (le_of_lt hi))
  have hRed : IsReduced (S.strictTransform i) :=
    S.isReduced_strictTransform (fun j hj => hnoeth k Y pY j hj) i (le_of_lt hi)
  have hf : Set.range ⇑(S.strictTransformMap i).base ⊆ Set.range ⇑(S.discardedLocusClosureCompl i).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact S.range_strictTransformMap_subset_discardedLocusClosureCompl i hi hNoetherian (hNlev (i + 1) hi) hopen
  have hkey := S.isBlowupAlongIdealSheaf_lift_discardedLocusClosureCompl_consolidated214 hres i hi (hnoeth k Y pY i (le_of_lt hi))
    hNoetherian hopen hf
  rw [S.tower_map_succ i]
  exact S.isBlowupAlongIdealSheaf_transitionMap_of_coprodDesc i
    (AffineSpacePrincipalizationData.isBlowupAlongIdealSheaf_coprodDesc_of_restrict_consolidated214 S i hNoetherian hopen hf hkey)


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
section

open CategoryTheory.Limits


section
variable {X Y : Scheme.{u}}

theorem isNoetherian_of_locallyOfFiniteType (f : X ⟶ Y)
    [IsNoetherian Y] [LocallyOfFiniteType f]
    [QuasiCompact f] :
    IsNoetherian X := by
  have : IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace ↥X := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace f
  constructor

theorem isNoetherian_of_iso (e : X ≅ Y)
    [IsNoetherian X] :
    IsNoetherian Y := by
  have : LocallyOfFiniteType e.inv := inferInstance
  have : QuasiCompact e.inv := inferInstance
  exact isNoetherian_of_locallyOfFiniteType e.inv


end

theorem isNoetherian_of_isBlowupAlongIdealSheaf {X X' : Scheme.{u}} [IsNoetherian X]
    {π : X' ⟶ X} {I : X.IdealSheafData} (h : Blowup.IsBlowupAlongIdealSheaf π I) :
    IsNoetherian X' := by
  have : IsProper π := Blowup.blowupIsProper.{u} X X' π I h
  have : LocallyOfFiniteType π := inferInstance
  have : QuasiCompact π := inferInstance
  exact isNoetherian_of_locallyOfFiniteType π

instance instIsNoetherianAffineSpaceIdx (k : Type u) [Field k] (n : Type u) [Finite n] :
    IsNoetherian (affineSpaceIndexedBy k n) := by
  have : IsNoetherianRing ↑(CommRingCat.of (MvPolynomial n k)) :=
    inferInstanceAs (IsNoetherianRing (MvPolynomial n k))
  have : IsNoetherian
      (Spec (CommRingCat.of (MvPolynomial n k))) := inferInstance
  exact isNoetherian_of_iso
    (AlgebraicGeometry.AffineSpace.SpecIso n (CommRingCat.of k)).symm

theorem isNoetherian_schemeAt {X : Scheme.{u}} (B : SequenceOfBlowups X)
    [IsNoetherian X] (i : ℕ) (hi : i ≤ B.length) :
    IsNoetherian (B.schemeAt i) := by
  revert hi
  induction i with
  | zero =>
    intro _
    exact isNoetherian_of_iso B.isoZero.symm
  | succ n ih =>
    intro hi
    have hn : n < B.length := hi
    exact @isNoetherian_of_isBlowupAlongIdealSheaf (B.schemeAt n) (B.schemeAt (n + 1)) (ih (le_of_lt hn)) _ _
      (B.isBlowupAlongIdealSheaf_blowupMorphism n hn)

instance SequenceOfBlowups.instIsNoetherianTop {X : Scheme.{u}} (B : SequenceOfBlowups X)
    [IsNoetherian X] : IsNoetherian B.lastObj :=
  isNoetherian_schemeAt B B.length le_rfl

theorem isNoetherian_ambientLevel {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) (i : ℕ)
    (hi : i ≤ S.ambientLength) :
    IsNoetherian (S.ambientLevel i) := by
  revert hi
  induction i with
  | zero =>
    intro _
    have : IsNoetherian S.ambient :=
      instIsNoetherianAffineSpaceIdx k (ULift.{u, 0} (Fin S.dim))
    exact isNoetherian_of_iso S.ambientBlowups.isoZero.symm
  | succ n ih =>
    intro hi
    have hn : n < S.ambientLength := hi
    exact @isNoetherian_of_isBlowupAlongIdealSheaf (S.ambientLevel n) (S.ambientLevel (n + 1)) (ih (le_of_lt hn)) _ _
      (S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn)

theorem embeddedPrincipalizationAmbientIsNoetherian (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    EmbeddedPrincipalizationAmbientIsNoetherian A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _ i hi
  exact isNoetherian_ambientLevel (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY) i hi

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
section


section

namespace MarkedSequenceOfBlowups

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

section
variable (s : MarkedSequenceOfBlowups p I m E)

theorem projectionToBase_zero :
    s.toSequenceOfBlowups.projectionToBase 0 = s.toSequenceOfBlowups.isoZero.hom := by
  have h0 : s.toSequenceOfBlowups.transitionMap (le_refl 0) = 𝟙 (s.toSequenceOfBlowups.schemeAt 0) := by
    rw [SequenceOfBlowups.transitionMap_def]
    have hid : (CategoryTheory.homOfLE (le_refl (0 : ℕ))).op = 𝟙 (Opposite.op (0 : ℕ)) := rfl
    rw [hid, CategoryTheory.Functor.map_id]
  rw [SequenceOfBlowups.projectionToBase_def, h0, Category.id_comp]

theorem projectionToBase_succ_apply (i : ℕ)
    (x : ↥(s.toSequenceOfBlowups.schemeAt (i + 1))) :
    (s.toSequenceOfBlowups.projectionToBase (i + 1)).base x =
      (s.toSequenceOfBlowups.projectionToBase i).base ((s.toSequenceOfBlowups.transitionMapSucc i).base x) := by
  have h : s.toSequenceOfBlowups.transitionMapSucc i ≫ s.toSequenceOfBlowups.projectionToBase i =
      s.toSequenceOfBlowups.projectionToBase (i + 1) := by
    rw [s.toSequenceOfBlowups.blowupMorphism_eq_transitionMap i]
    exact s.toSequenceOfBlowups.transitionMap_comp_projectionToBase (Nat.le_succ i)
  rw [← h]
  rfl


end

section
variable (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) (hi : i < s.toSequenceOfBlowups.length)
include hi

theorem comap_ideal_le_ideal_succ :
    (s.ideal i).comap (s.toSequenceOfBlowups.transitionMapSucc i) ≤ s.ideal (i + 1) := by
  rw [← s.ideal_succ i hi]
  exact fun U => Ideal.mul_le_right

theorem support_ideal_succ_subset_preimage :
    (((s.ideal (i + 1)).support : Set ↥(s.toSequenceOfBlowups.schemeAt (i + 1)))) ⊆
      ⇑(s.toSequenceOfBlowups.transitionMapSucc i).base ⁻¹'
        (((s.ideal i).support : Set ↥(s.toSequenceOfBlowups.schemeAt i))) := by
  refine subset_trans (SetLike.coe_subset_coe.mpr
    (Scheme.IdealSheafData.support_antitone (s.comap_ideal_le_ideal_succ i hi))) ?_
  exact (Scheme.IdealSheafData.support_comap _ _).le


end

end MarkedSequenceOfBlowups

theorem MarkedIdealWithBoundary.IsAdmissible.isNoetherian {T : MarkedIdealWithBoundary.{u}} (hV : T.IsAdmissible) :
    IsNoetherian T.scheme := by
  have : LocallyOfFiniteType T.structMap := hV.locallyOfFiniteType
  have : QuasiCompact T.structMap := hV.quasiCompact
  have : IsNoetherian (Spec (CommRingCat.of T.base)) := inferInstance
  exact isNoetherian_of_locallyOfFiniteType T.structMap

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequenceBoundary
section

open TopologicalSpace

section

namespace IdealBlowupSequence

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {E : List X.IdealSheafData}

section
variable (s : IdealBlowupSequence p I E)

theorem structureMorphism_zero :
    s.structureMorphism 0 = s.toSequenceOfBlowups.isoZero.hom ≫ p := by
  rw [structureMorphism_def, SequenceOfBlowups.projectionToBase_zero]

theorem structureMorphism_succ (i : ℕ) :
    s.structureMorphism (i + 1) = s.toSequenceOfBlowups.transitionMapSucc i ≫ s.structureMorphism i := by
  rw [structureMorphism_def, structureMorphism_def, SequenceOfBlowups.blowupMorphism_eq_transitionMap, ← Category.assoc,
    SequenceOfBlowups.transitionMap_comp_projectionToBase]


end

theorem smooth_structureMorphism [Smooth p] (s : IdealBlowupSequence p I E) (i : ℕ)
    (hi : i ≤ s.toSequenceOfBlowups.length) :
    Smooth (s.structureMorphism i) := by
  revert hi
  induction i with
  | zero =>
    intro _
    rw [structureMorphism_zero]
    infer_instance
  | succ n ih =>
    intro hi
    have hn : n < s.toSequenceOfBlowups.length := hi
    have := ih (le_of_lt hn)
    rw [structureMorphism_succ]
    exact smooth_comp_of_isBlowupAlongIdealSheaf (s.hasStrictNormalCrossingsWith_center n hn)
      (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn)

theorem isNoetherian_schemeAt [IsNoetherian X] (s : IdealBlowupSequence p I E) (i : ℕ)
    (hi : i ≤ s.toSequenceOfBlowups.length) :
    IsNoetherian (s.toSequenceOfBlowups.schemeAt i) :=
  EmbeddedResolution.isNoetherian_schemeAt s.toSequenceOfBlowups i hi

end IdealBlowupSequence


end
end
end FunctorialResolution.EmbeddedResolution
end
