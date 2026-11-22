import Mathlib
import Core5.M16DivisorInvariants

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

universe u
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariant
section

open CategoryTheory AlgebraicGeometry

section

def StrictNormalCrossingsLiftFromDivisor : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (P : Scheme.{u})
    (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (H : P.IdealSheafData) (N : List P.IdealSheafData),
    InStrictNormalCrossingPosition p (H :: N) →
    ∀ Z : H.subscheme.IdealSheafData,
      HasStrictNormalCrossingsWith (H.subschemeι ≫ p) Z (N.map (fun D => D.comap H.subschemeι)) →
      HasStrictNormalCrossingsWith p (imageIdealSheaf H.subschemeι Z) (H :: N)

section
variable {k : Type u} [Field k] {Y : Scheme.{u}} (p q : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [LocallyOfFiniteType q] (h : p = q)
include h

theorem derivIdealSheafIterate_congr (r : ℕ) (J : Y.IdealSheafData) :
    derivIdealSheafIterate k p r J = derivIdealSheafIterate k q r J := by
  subst h
  rfl

theorem logDerivIdealSheafIterate_congr (P : Y.IdealSheafData) (r : ℕ) (J : Y.IdealSheafData) :
    logDerivIdealSheafIterate k p P r J = logDerivIdealSheafIterate k q P r J := by
  subst h
  rfl


end

theorem imageIdealSheaf_hom_eq_comap_inv {A B : Scheme.{u}} (e : A ≅ B) (J : A.IdealSheafData) :
    imageIdealSheaf e.hom J = J.comap e.inv := by
  rw [FunctorialResolution.EmbeddedResolution.imageIdealSheaf_eq_comap_inv e.hom J,
    CategoryTheory.IsIso.Iso.inv_hom]

namespace DivisorReduction

theorem structureMorphism_ambientBlowupSeq_zero (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) :
    ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr 0 = T.structMap := by
  have h0 : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase 0 ≫ T.structMap = T.structMap := by
    rw [BlowupSequenceData.projectionToBase_zero]
    exact Category.id_comp T.structMap
  exact h0

private theorem list_map_comap_id_eq_self_consolidated397 {X : Scheme.{u}} (E : List X.IdealSheafData) :
    List.map (fun D : X.IdealSheafData => D.comap (CategoryTheory.CategoryStruct.id X)) E = E := by
  simp

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups) (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)

theorem ambientBlowupSeq_boundary_zero :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0 = E₀ := by
  rw [BlowupSequenceData.boundary_zero]
  show List.map (fun D : T.scheme.IdealSheafData =>
      D.comap (CategoryTheory.CategoryStruct.id T.scheme)) E₀ = E₀
  exact list_map_comap_id_eq_self_consolidated397 E₀

theorem ker_embeddingIntoAmbient_zero_eq_boundary_get :
    Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0) = T.boundary.get ⟨j, hj⟩ := by
  rw [embeddingIntoAmbient_zero hres hno T j hj I₀ E₀ s hpr]
  exact (Scheme.Hom.ker_comp_of_isIso s.isoZero.hom (T.boundary.get ⟨j, hj⟩).subschemeι).trans
    (Scheme.IdealSheafData.ker_subschemeι _)

private theorem le_length_imp_isNoetherian_ambientBlowupSeq_schemeAt_consolidated397
    (t : ℕ) :
    t ≤ s.length →
      IsNoetherian ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t) := by
  induction t with
  | zero =>
      intro _
      exact isNoetherian_of_iso (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.symm
  | succ n ih =>
      intro ht
      have hn : n < s.length := ht
      have : IsNoetherian ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj n) :=
        ih (le_of_lt hn)
      have hlen : n < (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length := by
        rw [ambientBlowupSeq_length hres hno T j hj I₀ E₀ s hpr]
        exact hn
      exact isNoetherian_of_isBlowupAlongIdealSheaf ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isBlowup n hlen)

theorem isNoetherian_ambientBlowupSeq_schemeAt (t : ℕ) (ht : t ≤ s.length) :
    IsNoetherian ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t) :=
  le_length_imp_isNoetherian_ambientBlowupSeq_schemeAt_consolidated397 hres hno T j hj I₀ E₀ s hpr t ht

theorem ker_embeddingIntoAmbient_le_center (t : ℕ) :
    Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≤
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t := by
  have key : Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≤
      Scheme.Hom.ker ((s.center t).subschemeι ≫
        embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) := by
    apply Scheme.Hom.le_ker_comp
  have h2 := (imageIdealSheaf_eq_ker_subschemeι_comp
    (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)).symm
  have h3 := (ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I₀ E₀ s hpr t).symm
  exact le_of_le_of_eq key (h2.trans h3)


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] [Smooth T.structMap] [LocallyOfFiniteType T.structMap] (j : ℕ) (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups) (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)

theorem ambientDerivIdeal_at_zero_eq_derivIdealSheafIterate (l : ℕ) :
    ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l 0 =
      derivIdealSheafIterate T.base T.structMap l I₀ := by
  unfold ambientDerivIdeal
  rw [BlowupSequenceData.controlledTransform_zero]
  show (derivIdealSheafIterate T.base T.structMap l I₀).comap
      (CategoryTheory.CategoryStruct.id T.scheme) =
    derivIdealSheafIterate T.base T.structMap l I₀
  simp

theorem ambientDerivIdeal_order_zero_eq_controlledTransform (t : ℕ) :
    ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr 0 t =
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t := by
  rfl


end

structure GoingUpInvariant (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) : Prop where
  divDeriv : ∀ l ≤ T.mult, ∀ i < t,
    ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center i) ^ (T.mult - l) * B =
        (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l i).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
  idx_lt : j < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).length
  deriv_le : ∀ [_hsmooth : Smooth
        (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)]
      [_instFt : LocallyOfFiniteType
        (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)], ∀ n < T.mult,
      derivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) n
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t) ≤
        ⨆ l ≤ n, logDerivIdealSheafIterate T.base
          (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
          (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)) (n - l)
          (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t)
  comap_eraseIdx :
    List.map (fun D => D.comap (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t))
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) = s.boundary t
  snc_bdry : InStrictNormalCrossingPosition (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t)
  bdry_getElem : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t)[j]'idx_lt =
      Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)
  smooth_structMap :
    Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)

namespace GoingUpInvariant

section
variable {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}} {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}} [IsNoetherian T.scheme] [Smooth T.structMap] [LocallyOfFiniteType T.structMap] {j : ℕ} {hj : j < T.boundary.length} {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData} {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups} {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent} {t : ℕ} (hgoingUp : GoingUpInvariant hres hno T j hj I₀ E₀ s hpr t)
include hgoingUp

theorem exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform :
    ∀ i < t, ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center i) ^ T.mult * B =
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult i).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i) := by
  intro i hi
  obtain ⟨B, hB⟩ := hgoingUp.divDeriv 0 (Nat.zero_le T.mult) i hi
  refine ⟨B, ?_⟩
  rw [← ambientDerivIdeal_order_zero_eq_controlledTransform hres hno T j hj I₀ E₀ s hpr i, ← hB, Nat.sub_zero]

theorem comap_controlledTransform (ht : t ≤ s.length) :
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.ideal t :=
  FunctorialResolution.EmbeddedResolution.DivisorReduction.comap_controlledTransform_embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ht hgoingUp.exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform


end

private theorem smooth_of_eq_consolidated397 {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g)
    (hg : Smooth g) : Smooth f := by
  rw [h]
  exact hg

theorem support_center_subset_orderAtLeastLocus {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [IsNoetherian T.scheme] [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap] [CharZero T.base]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent} {t : ℕ}
    (hgoingUp : GoingUpInvariant hres hno T j hj I₀ E₀ s hpr t)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (ht : t < s.length) :
    (↑((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).support :
        Set ↥((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t)) ⊆
      orderAtLeastLocus ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t) T.mult := by
  have hsmP : Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    hgoingUp.smooth_structMap
  have hftP : LocallyOfFiniteType
      (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) := inferInstance
  have hstep1 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t
      = (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) ≫ T.structMap :=
    (Category.assoc _ _ _).symm
  have hstep2 : (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) ≫ T.structMap
      = (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) ≫ T.structMap :=
    congrArg (fun f : (MarkedBlowupSequenceData.ofMarkedSequence s).obj t ⟶ T.scheme => f ≫ T.structMap)
      (embeddingIntoAmbient_comp_projectionToBase hres hno T j hj I₀ E₀ s hpr t)
  have hstep3 : (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) ≫ T.structMap = s.projectionToSpec t :=
    (Category.assoc _ _ _).trans (MarkedSequenceOfBlowups.projectionToSpec_eq s t).symm
  have hcomp := hstep1.trans (hstep2.trans hstep3)
  have hsmE : Smooth (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
      ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    smooth_of_eq_consolidated397 hcomp
      (MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hV s t (le_of_lt ht))
  have hdom := hgoingUp.deriv_le (T.mult - 1) (by omega)
  have hbal' : ∀ l < T.mult,
      ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ^ T.mult ≤
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t ^ (T.mult - l) := by
    intro l hl
    exact pow_ambientDerivIdeal_le_pow_controlledTransform hres hno T j hj I₀ E₀ s hpr hbal l hl t
      (le_of_lt ht) hgoingUp.exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform (fun i hi => hgoingUp.divDeriv l (le_of_lt hl) i hi)
  intro x hx
  rw [support_ambientBlowupSeq_center_eq_image hres hno T j hj I₀ E₀ s hpr t] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy1 : y ∈ orderAtLeastLocus (s.ideal t) T.mult := by
    have hco := s.center_order t ht
    exact hco hy
  have hy2 : y ∈ orderAtLeastLocus
      (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)) T.mult := by
    rw [hgoingUp.comap_controlledTransform (le_of_lt ht)]
    exact hy1
  exact base_mem_orderAtLeastLocus_of_mem_comap T.base
    (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
    (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) T.mult hm
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t)
    (fun l => ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t) hdom hbal' y hy2

private theorem exists_iso_ker_subschemeι_consolidated397 {S X : Scheme.{u}} (f : S ⟶ X)
    [IsClosedImmersion f] :
    ∃ e : S ≅ (Scheme.Hom.ker f).subscheme,
      e.hom ≫ (Scheme.Hom.ker f).subschemeι = f :=
  ⟨asIso f.toImage, f.toImage_imageι⟩

private theorem imageIdealSheaf_comp_consolidated397 {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (J : A.IdealSheafData) :
    imageIdealSheaf g (imageIdealSheaf f J) = imageIdealSheaf (f ≫ g) J :=
  (Scheme.IdealSheafData.map_comp J f g).symm

private theorem hasStrictNormalCrossingsWith_imageIdealSheaf_of_restriction_consolidated397 {k : Type u} [Field k] [CharZero k]
    {P S : Scheme.{u}}
    (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (ι : S ⟶ P) [IsClosedImmersion ι]
    (q : S ⟶ Spec (CommRingCat.of k)) (hq : ι ≫ p = q)
    (Zs : S.IdealSheafData) (Bs : List S.IdealSheafData) (N : List P.IdealSheafData)
    (hN : List.map (fun D : P.IdealSheafData => D.comap ι) N = Bs)
    (hsnc : InStrictNormalCrossingPosition p (Scheme.Hom.ker ι :: N))
    (hlow : HasStrictNormalCrossingsWith q Zs Bs)
    (hlift : StrictNormalCrossingsLiftFromDivisor.{u}) :
    HasStrictNormalCrossingsWith p (imageIdealSheaf ι Zs) (Scheme.Hom.ker ι :: N) := by
  obtain ⟨e, he⟩ := exists_iso_ker_subschemeι_consolidated397 ι
  have hinv : e.inv ≫ ι = (Scheme.Hom.ker ι).subschemeι := by
    have h := congrArg (fun m => e.inv ≫ m) he.symm
    simpa using h
  have hq' : e.inv ≫ q = (Scheme.Hom.ker ι).subschemeι ≫ p := by
    rw [← hq, ← Category.assoc, hinv]
  have hlist : List.map (fun D : S.IdealSheafData => D.comap e.inv) Bs
      = List.map (fun D : P.IdealSheafData =>
          D.comap (Scheme.Hom.ker ι).subschemeι) N := by
    rw [← hN, List.map_map]
    refine List.map_congr_left ?_
    intro D _
    show (D.comap ι).comap e.inv = D.comap (Scheme.Hom.ker ι).subschemeι
    rw [← hinv]
    simp
  have hZ : HasStrictNormalCrossingsWith ((Scheme.Hom.ker ι).subschemeι ≫ p) (Zs.comap e.inv)
      (List.map (fun D : P.IdealSheafData =>
        D.comap (Scheme.Hom.ker ι).subschemeι) N) := by
    have h := hasStrictNormalCrossingsWith_comap_iso q e.symm Zs Bs hlow
    simp only [Iso.symm_hom] at h
    rw [hq', hlist] at h
    exact h
  have hfin := hlift k P p (Scheme.Hom.ker ι) N hsnc (Zs.comap e.inv) hZ
  have himg : imageIdealSheaf (Scheme.Hom.ker ι).subschemeι (Zs.comap e.inv)
      = imageIdealSheaf ι Zs := by
    rw [← imageIdealSheaf_hom_eq_comap_inv e Zs, imageIdealSheaf_comp_consolidated397 e.hom _ Zs, he]
  rwa [himg] at hfin

section
variable {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}} {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}} [IsNoetherian T.scheme] [Smooth T.structMap] [LocallyOfFiniteType T.structMap] [CharZero T.base] {j : ℕ} {hj : j < T.boundary.length} {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData} {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups} {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent} {t : ℕ} (hgoingUp : GoingUpInvariant hres hno T j hj I₀ E₀ s hpr t)
include hgoingUp

theorem hasStrictNormalCrossingsWith_center_ker_cons (hlift : StrictNormalCrossingsLiftFromDivisor.{u}) (ht : t < s.length) :
    HasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ::
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) := by
  have hsmooth : Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    hgoingUp.smooth_structMap
  have hsnccons : InStrictNormalCrossingPosition (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ::
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) := by
    have h1 := inStrictNormalCrossingPosition_moveToFront (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) j hgoingUp.idx_lt hgoingUp.snc_bdry
    rwa [moveToFront_eq_cons _ _ hgoingUp.idx_lt, hgoingUp.bdry_getElem] at h1
  have hstep1 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t
      = (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) ≫ T.structMap :=
    (Category.assoc _ _ _).symm
  have hstep2 : (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) ≫ T.structMap
      = (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) ≫ T.structMap :=
    congrArg (fun f : (MarkedBlowupSequenceData.ofMarkedSequence s).obj t ⟶ T.scheme => f ≫ T.structMap)
      (embeddingIntoAmbient_comp_projectionToBase hres hno T j hj I₀ E₀ s hpr t)
  have hstep3 : (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) ≫ T.structMap = s.projectionToSpec t :=
    (Category.assoc _ _ _).trans (MarkedSequenceOfBlowups.projectionToSpec_eq s t).symm
  have hq : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
      ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t = s.projectionToSpec t :=
    hstep1.trans (hstep2.trans hstep3)
  have hlow : HasStrictNormalCrossingsWith (s.projectionToSpec t) (s.center t) (s.boundary t) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact s.center_snc t ht
  rw [ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I₀ E₀ s hpr t]
  exact hasStrictNormalCrossingsWith_imageIdealSheaf_of_restriction_consolidated397 (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
    (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.projectionToSpec t) hq (s.center t)
    (s.boundary t) (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j)
    hgoingUp.comap_eraseIdx hsnccons hlow hlift

theorem hasStrictNormalCrossingsWith_center_boundary (hlift : StrictNormalCrossingsLiftFromDivisor.{u}) (ht : t < s.length) :
    HasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) := by
  have hcons := hasStrictNormalCrossingsWith_center_ker_cons hgoingUp hlift ht
  refine hasStrictNormalCrossingsWith_of_moveToFront (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) j hgoingUp.idx_lt ?_
  rw [moveToFront_eq_cons _ j hgoingUp.idx_lt, hgoingUp.bdry_getElem]
  exact hcons

theorem exists_pow_mul_eq_comap_ambientDerivIdeal
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (ht : t < s.length) (l : ℕ) (hl : l ≤ T.mult) :
    ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t) ^ (T.mult - l) * B =
        (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) := by
  rcases hl.lt_or_eq with hlt | h
  · have hsmth : Smooth
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap) := hgoingUp.smooth_structMap
    have hnoe : IsNoetherian
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) :=
      isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr (t + 1) ht
    have hpow := pow_ambientDerivIdeal_le_pow_controlledTransform hres hno T j hj I₀ E₀ s hpr hbal l hlt t
      (le_of_lt ht) hgoingUp.exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform (hgoingUp.divDeriv l hl)
    have hcos := orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le T.base
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap)
      (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t) l T.mult hlt hpow
    have hord := (support_center_subset_orderAtLeastLocus hgoingUp hbal hm hV ht).trans hcos
    have hlen : t < (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length := by
      rw [ambientBlowupSeq_length hres hno T j hj I₀ E₀ s hpr]
      exact ht
    exact BlowupSequenceData.exists_pow_mul_eq_comap_controlledTransform (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr)
      T.structMap (derivIdealSheafIterate T.base T.structMap l I₀) (T.mult - l) t hlen
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) (hasStrictNormalCrossingsWith_center_boundary hgoingUp hlift ht) hord
  · refine ⟨(ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t).comap
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t), ?_⟩
    rw [h, Nat.sub_self, pow_zero, one_mul]

theorem ambientDerivIdeal_le_center_pow (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (ht : t < s.length) (l : ℕ) (hl : l ≤ T.mult) :
    ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ≤
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t ^ (T.mult - l) := by
  rcases hl.lt_or_eq with hlt | h
  · have hsmth : Smooth
        (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) := hgoingUp.smooth_structMap
    have hpow := pow_ambientDerivIdeal_le_pow_controlledTransform hres hno T j hj I₀ E₀ s hpr hbal l hlt t
      (le_of_lt ht) hgoingUp.exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform (hgoingUp.divDeriv l hl)
    have hcos := orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le T.base
      (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t) l T.mult hlt hpow
    exact le_pow_of_hasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) (hasStrictNormalCrossingsWith_center_boundary hgoingUp hlift ht)
      (T.mult - l) ((support_center_subset_orderAtLeastLocus hgoingUp hbal hm hV ht).trans hcos)
  · rw [h, Nat.sub_self, pow_zero]
    exact le_top


end

end GoingUpInvariant

private theorem list_map_comap_map_comap_eq_map_comap_comp_consolidated397 {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (L : List C.IdealSheafData) :
    List.map (fun D : B.IdealSheafData => D.comap f)
        (List.map (fun D : C.IdealSheafData => D.comap g) L)
      = List.map (fun D : C.IdealSheafData => D.comap (f ≫ g)) L := by
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro D _
  simp

theorem goingUpInvariant_zero (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap] [CharZero T.base]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hE₀ : InStrictNormalCrossingPosition T.structMap E₀) (hjE : j < E₀.length)
    (hget : E₀[j]'hjE = T.boundary[j]'hj)
    (htrunc : (E₀.eraseIdx j).take (T.boundary.length - 1) = E₀.eraseIdx j) :
    GoingUpInvariant hres hno T j hj I₀ E₀ s hpr 0 := by
  have hbd : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0 = E₀ :=
    ambientBlowupSeq_boundary_zero hres hno T j hj I₀ E₀ s hpr
  have hsm : ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr 0 = T.structMap :=
    structureMorphism_ambientBlowupSeq_zero hres hno T j hj I₀ E₀ s hpr
  have : @LocallyOfFiniteType
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj 0)
      (Spec (CommRingCat.of T.base)) T.structMap :=
    ‹LocallyOfFiniteType T.structMap›
  have hctrl : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult 0 = I₀ := by
    rw [BlowupSequenceData.controlledTransform_zero]
    show I₀.comap (CategoryTheory.CategoryStruct.id T.scheme) = I₀
    simp
  have hlow0 : (restrictToBoundaryDivisor T j hj I₀ E₀).boundary
      = List.map (fun D : T.scheme.IdealSheafData =>
          D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          ((E₀.eraseIdx j).take (T.boundary.length - 1)) := rfl
  have hlow : (restrictToBoundaryDivisor T j hj I₀ E₀).boundary
      = List.map (fun D : T.scheme.IdealSheafData =>
          D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) (E₀.eraseIdx j) :=
    hlow0.trans (congrArg (List.map (fun D : T.scheme.IdealSheafData =>
      D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)) htrunc)
  have hRHS : List.map (fun D : (restrictToBoundaryDivisor T j hj I₀ E₀).scheme.IdealSheafData =>
        D.comap s.isoZero.hom) (restrictToBoundaryDivisor T j hj I₀ E₀).boundary
      = List.map (fun D : T.scheme.IdealSheafData =>
        D.comap (s.isoZero.hom ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)) (E₀.eraseIdx j) :=
    (congrArg (List.map (fun D : (restrictToBoundaryDivisor T j hj I₀ E₀).scheme.IdealSheafData =>
        D.comap s.isoZero.hom)) hlow).trans
      (list_map_comap_map_comap_eq_map_comap_comp_consolidated397 s.isoZero.hom (T.boundary.get ⟨j, hj⟩).subschemeι (E₀.eraseIdx j))
  refine
    { divDeriv := ?_
      idx_lt := by rw [hbd]; exact hjE
      deriv_le := ?_
      comap_eraseIdx := ?_
      snc_bdry := ?_
      bdry_getElem := ?_
      smooth_structMap := ?_ }
  · intro l _ i hi
    exact absurd hi (Nat.not_lt_zero i)
  · intro _ _ n _
    have h1 : derivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr 0) n
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult 0)
        = derivIdealSheafIterate T.base T.structMap n
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult 0) :=
      derivIdealSheafIterate_congr _ _ hsm n _
    have h2 : derivIdealSheafIterate T.base T.structMap n
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult 0)
        = derivIdealSheafIterate T.base T.structMap n I₀ := by
      rw [hctrl]
    have h3 : derivIdealSheafIterate T.base T.structMap n I₀
        = ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr n 0 :=
      (ambientDerivIdeal_at_zero_eq_derivIdealSheafIterate hres hno T j hj I₀ E₀ s hpr n).symm
    refine le_iSup₂_of_le n le_rfl ?_
    rw [Nat.sub_self, logDerivIdealSheafIterate_zero]
    exact le_of_eq (h1.trans (h2.trans h3))
  · rw [hbd, embeddingIntoAmbient_zero hres hno T j hj I₀ E₀ s hpr,
      MarkedSequenceOfBlowups.boundary_zero s]
    exact hRHS.symm
  · rw [hbd, hsm]
    exact hE₀
  · rw [ker_embeddingIntoAmbient_zero_eq_boundary_get hres hno T j hj I₀ E₀ s hpr]
    simp only [hbd]
    exact hget
  · rw [hsm]
    exact ‹Smooth T.structMap›

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.OrderLocusDisjointBoundary
section

open CategoryTheory AlgebraicGeometry


namespace DivisorReduction

theorem orderAtLeastLocus_inter_ker_support_eq_empty_of_comap
    {S X : Scheme.{u}} (ι : S ⟶ X) [IsClosedImmersion ι]
    (J : X.IdealSheafData) (m : ℕ) (h : orderAtLeastLocus (J.comap ι) m = ∅) :
    orderAtLeastLocus J m ∩ (↑(Scheme.Hom.ker ι).support : Set ↥X) = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hx hker
  have hcl : IsClosed (Set.range ⇑ι.base) :=
    (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding ι).isClosed_range
  have hmem : x ∈ closure (Set.range ⇑ι.base) := by
    rw [Scheme.Hom.support_ker ι] at hker
    exact hker
  rw [hcl.closure_eq] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hxo : (m : ℕ∞) ≤ orderAt J x := hx
  have hyo : (m : ℕ∞) ≤ orderAt (J.comap ι) y := by
    refine le_trans ?_ (orderAt_le_orderAt_comap ι J y)
    rw [hy]
    exact hxo
  have hy' : y ∈ orderAtLeastLocus (J.comap ι) m := hyo
  rw [h] at hy'
  exact hy'

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)

theorem orderAtLeastLocus_inter_support_ker_eq_empty
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hdiv : ∀ i < s.length,
      ∃ B : ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).obj
          (i + 1)).IdealSheafData,
        Blowup.exceptionalIdeal
            ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).map i)
            ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).center i) ^ T.mult *
            B =
          (((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
              (lowerIdealWithoutBlowup T) T.mult i).comap
            ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).map i)))
    (hempty : orderAtLeastLocus (s.ideal s.length) T.mult = ∅) :
    orderAtLeastLocus
          ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
            T.ideal T.mult s.length)
          T.mult ∩
        (↑(Scheme.Hom.ker
              (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr
                s.length)).support :
          Set ↥((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).obj s.length)) =
      ∅ := by
  have hid : lowerIdealWithoutBlowup T = T.ideal := by
    show T.ideal.comap (CategoryStruct.id T.scheme) = T.ideal
    simp
  have hcomap := comap_controlledTransform_embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T)
    s hpr s.length le_rfl hdiv
  have hctrl :
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
          T.ideal T.mult s.length =
        (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
          (lowerIdealWithoutBlowup T) T.mult s.length :=
    congrArg
      (fun I => (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
        I T.mult s.length) hid.symm
  refine orderAtLeastLocus_inter_ker_support_eq_empty_of_comap
    (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr s.length) _ T.mult ?_
  rw [hctrl, hcomap]
  exact hempty

theorem orderAtLeastLocus_controlledTransform_inter_ker_support_eq_empty
    (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryStruct.id T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hdiv : ∀ i < s.length,
      ∃ B : ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).obj
          (i + 1)).IdealSheafData,
        Blowup.exceptionalIdeal
            ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).map i)
            ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).center i) ^
              T.mult * B =
          (((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).controlledTransform
              (lowerIdealAfterBlowup T j hj) T.mult i).comap
            ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).map i)))
    (hone :
      (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
            (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform
          T.ideal T.mult 1 =
        (lowerIdealAfterBlowup T j hj).comap
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).isoZero.hom)
    (hempty : orderAtLeastLocus (s.ideal s.length) T.mult = ∅) :
    orderAtLeastLocus
          ((BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
                (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s
                  hpr)).controlledTransform
            T.ideal T.mult (s.length + 1))
          T.mult ∩
        (↑(Scheme.Hom.ker
              (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr
                s.length)).support :
          Set ↥((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).obj
            s.length)) =
      ∅ := by
  have h1 := BlowupSequenceData.controlledTransform_prepend_succ (containedComponentsIdeal T j hj) hb
    (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)
    T.ideal (lowerIdealAfterBlowup T j hj) T.mult hone s.length
  have h2 := comap_controlledTransform_embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj)
    (lowerBoundaryAfterBlowup T j hj) s hpr s.length le_rfl hdiv
  refine orderAtLeastLocus_inter_ker_support_eq_empty_of_comap
    (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr s.length)
    _ T.mult ?_
  rw [h1, h2]
  exact hempty


end

end DivisorReduction

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.TwistedDivisorRestriction
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section

namespace DivisorReduction

section
variable (T : MarkedIdealWithBoundary.{u})

private theorem orderAt_le_mult_consolidated384 (hOB : T.IsOrderBoundedByMult) (x : ↥T.scheme) :
    orderAt T.ideal x ≤ (T.mult : ℕ∞) := hOB x

private theorem isDerivBalanced_of_isBalanced_consolidated384 (h : LocallyOfFiniteType T.structMap) (hbal : T.IsBalanced h) :
    IsDerivBalanced T.base T.structMap T.ideal T.mult := hbal


end

private theorem mem_support_of_mem_support_comap_consolidated384 {X Y : Scheme.{u}} (f : Y ⟶ X)
    (I : X.IdealSheafData) {y : ↥Y} (hy : y ∈ (I.comap f).support) : f y ∈ I.support := by
  rw [Scheme.IdealSheafData.support_comap] at hy
  exact hy

section
variable (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ) (hj : j < T.boundary.length)
include hV

private theorem disjoint_irreducibleComponents_boundary_subscheme_consolidated384 :
    ∀ C₁ ∈ irreducibleComponents ↥(T.boundary.get ⟨j, hj⟩).subscheme,
      ∀ C₂ ∈ irreducibleComponents ↥(T.boundary.get ⟨j, hj⟩).subscheme,
        C₁ ≠ C₂ → Disjoint C₁ C₂ := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.smooth
  have hsm : Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    ((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).mp
      (isSmoothDivisor_boundary_get T hV j hj)).2
  have h := irreducibleComponentsDisjointOfSmooth
  unfold IrreducibleComponentsDisjointOfSmooth at h
  exact h T.base _ _ hsm

private theorem containedComponentsIdeal_pow_mul_lowerIdealAfterBlowup_consolidated384 :
    DivisorReduction.containedComponentsIdeal T j hj ^ T.mult * DivisorReduction.lowerIdealAfterBlowup T j hj = T.ideal := by
  have hex : ∃ B, DivisorReduction.containedComponentsIdeal T j hj ^ T.mult * B = T.ideal :=
    exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj
  have h := pow_mul_residualByPow T.ideal (DivisorReduction.containedComponentsIdeal T j hj) T.mult hex
  simpa [DivisorReduction.lowerIdealAfterBlowup, exceptionalIdeal_id,
    Scheme.IdealSheafData.comap_id] using h


end

section
variable (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hOB : T.IsOrderBoundedByMult) (hbal : T.IsBalanced hV.locallyOfFiniteType) (j : ℕ) (hj : j < T.boundary.length)
include hOB hbal

theorem nonzeroOnComponents_comap_lowerIdealAfterBlowup :
    NonzeroOnComponents
      ((DivisorReduction.lowerIdealAfterBlowup T j hj).comap (T.boundary.get ⟨j, hj⟩).subschemeι) := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.smooth
  have : TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    EmbeddedResolution.noetherianSpace_boundary_subscheme T hV j hj
  have hfact : DivisorReduction.containedComponentsIdeal T j hj ^ T.mult *
      DivisorReduction.lowerIdealAfterBlowup T j hj = T.ideal := containedComponentsIdeal_pow_mul_lowerIdealAfterBlowup_consolidated384 T hV j hj
  have horder : ∀ x : ↥T.scheme, orderAt T.ideal x =
      (T.mult : ℕ∞) * orderAt (DivisorReduction.containedComponentsIdeal T j hj) x +
        orderAt (DivisorReduction.lowerIdealAfterBlowup T j hj) x := by
    intro x
    rw [← hfact, orderAt_mul T.base T.structMap, orderAt_pow T.base T.structMap]
  rw [nonzeroOnComponents_iff]
  intro C hC hsub
  obtain ⟨x, hx⟩ := hC.1.1
  by_cases hcase : ∀ y ∈ C, (T.boundary.get ⟨j, hj⟩).subschemeι y ∈ orderAtLeastLocus T.ideal T.mult
  · have hsep := disjoint_irreducibleComponents_boundary_subscheme_consolidated384 T hV j hj
    have hcc : connectedComponent x ⊆ C :=
      connectedComponent_subset_of_mem_irreducibleComponents hsep hC hx
    have hxrel : x ∈ divisorComponentsInOrderLocus T j hj := by
      intro z hz
      exact hcase z (hcc hz)
    have hopen : IsOpen (divisorComponentsInOrderLocus T j hj) := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T hV j hj
    have hcl : IsClosed (divisorComponentsInOrderLocus T j hj) := isClosed_divisorComponentsInOrderLocus T hV j hj
    have hZsupp : (T.boundary.get ⟨j, hj⟩).subschemeι x ∈
        (DivisorReduction.containedComponentsIdeal T j hj).support := by
      rw [containedComponentsIdeal_eq_openSubschemeKer T j hj hopen]
      have hmem : (T.boundary.get ⟨j, hj⟩).subschemeι x ∈
          ((openSubschemeKer (T.boundary.get ⟨j, hj⟩)
            ⟨divisorComponentsInOrderLocus T j hj, hopen⟩).support : Set ↥T.scheme) := by
        rw [support_openSubschemeKer _ _ hcl]
        exact ⟨x, hxrel, rfl⟩
      exact hmem
    have hxsupp : (T.boundary.get ⟨j, hj⟩).subschemeι x ∈
        (DivisorReduction.lowerIdealAfterBlowup T j hj).support :=
      mem_support_of_mem_support_comap_consolidated384 _ _ (hsub hx)
    have h1 : (1 : ℕ∞) ≤ orderAt (DivisorReduction.lowerIdealAfterBlowup T j hj)
        ((T.boundary.get ⟨j, hj⟩).subschemeι x) :=
      (one_le_orderAt_iff_mem_support _ _).mpr hxsupp
    have h2 : (1 : ℕ∞) ≤ orderAt (DivisorReduction.containedComponentsIdeal T j hj)
        ((T.boundary.get ⟨j, hj⟩).subschemeι x) :=
      (one_le_orderAt_iff_mem_support _ _).mpr hZsupp
    have h3 : (T.mult : ℕ∞) + 1 ≤ orderAt T.ideal ((T.boundary.get ⟨j, hj⟩).subschemeι x) := by
      calc (T.mult : ℕ∞) + 1 = (T.mult : ℕ∞) * 1 + 1 := by rw [mul_one]
        _ ≤ (T.mult : ℕ∞) * orderAt (DivisorReduction.containedComponentsIdeal T j hj)
              ((T.boundary.get ⟨j, hj⟩).subschemeι x) +
            orderAt (DivisorReduction.lowerIdealAfterBlowup T j hj)
              ((T.boundary.get ⟨j, hj⟩).subschemeι x) := by
          gcongr
        _ = orderAt T.ideal ((T.boundary.get ⟨j, hj⟩).subschemeι x) := (horder _).symm
    have h4 : orderAt T.ideal ((T.boundary.get ⟨j, hj⟩).subschemeι x) ≤ (T.mult : ℕ∞) :=
      orderAt_le_mult_consolidated384 T hOB _
    have h5 : (T.mult : ℕ∞) + 1 ≤ (T.mult : ℕ∞) := le_trans h3 h4
    have h6 : T.mult + 1 ≤ T.mult := by exact_mod_cast h5
    omega
  · push Not at hcase
    obtain ⟨y, hyC, hy⟩ := hcase
    have hy0 : orderAt T.ideal ((T.boundary.get ⟨j, hj⟩).subschemeι y) = 0 := by
      rcases orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced T.base T.structMap T.ideal T.mult
        (isDerivBalanced_of_isBalanced_consolidated384 T hV.locallyOfFiniteType hbal)
        ((T.boundary.get ⟨j, hj⟩).subschemeι y) with h | h
      · exact h
      · exact absurd ((mem_orderAtLeastLocus_iff T.ideal T.mult _).mpr h) hy
    have hle : orderAt (DivisorReduction.lowerIdealAfterBlowup T j hj)
        ((T.boundary.get ⟨j, hj⟩).subschemeι y) ≤ 0 := by
      rw [← hy0, horder]
      exact le_add_self
    have hJ0 : orderAt (DivisorReduction.lowerIdealAfterBlowup T j hj)
        ((T.boundary.get ⟨j, hj⟩).subschemeι y) = 0 := le_antisymm hle zero_le
    have hmem : (T.boundary.get ⟨j, hj⟩).subschemeι y ∈
        (DivisorReduction.lowerIdealAfterBlowup T j hj).support :=
      mem_support_of_mem_support_comap_consolidated384 _ _ (hsub hyC)
    rw [← one_le_orderAt_iff_mem_support, hJ0] at hmem
    simp at hmem

theorem isAdmissible_restrictTwistedToDivisor (_hZ : DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤) :
    (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.quasiCompact
  have := hV.smooth
  have hsm : Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    ((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).mp
      (isSmoothDivisor_boundary_get T hV j hj)).2
  have := hsm
  have hlft : LocallyOfFiniteType
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) := inferInstance
  have hqc : QuasiCompact
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) := inferInstance
  exact
    { charZero := hV.charZero
      locallyOfFiniteType := hlft
      nonzeroOnComponents := nonzeroOnComponents_comap_lowerIdealAfterBlowup T hV hOB hbal j hj
      one_le_mult := hV.one_le_mult
      quasiCompact := hqc
      smooth := hsm
      snc := DivisorReductionBoundary.inStrictNormalCrossingPosition_comap_lowerBoundaryAfterBlowup T hV j hj }


end

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariantSucc
section

open CategoryTheory AlgebraicGeometry

section

namespace DivisorReduction

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups) (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ)

theorem structureMorphism_ambientBlowupSeq_succ :
    ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1) =
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t := by
  show (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase (t + 1) ≫ T.structMap =
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap)
  rw [BlowupSequenceData.projectionToBase_succ, Category.assoc]

theorem ker_embeddingIntoAmbient_succ (ht : t < s.length) :
    Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1)) =
      Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
        (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)) :=
  ker_embeddingIntoAmbientBlowupSequence_succ (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t ht


end

namespace GoingUpInvariant

private theorem getElem_map_append_of_lt_length_consolidated426.{v, w} {α : Type v} {β : Type w} (f : α → β)
    (M : List β) (L : List α) (i : ℕ) (hi : i < L.length)
    (h : i < (L.map f ++ M).length) :
    (L.map f ++ M)[i]'h = f (L[i]'hi) := by
  rw [List.getElem_append_left (by simpa using hi), List.getElem_map]

theorem succ {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [IsNoetherian T.scheme] [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap] [CharZero T.base]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent} {t : ℕ}
    (hgoingUp : GoingUpInvariant hres hno T j hj I₀ E₀ s hpr t)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (ht : t < s.length) :
    GoingUpInvariant hres hno T j hj I₀ E₀ s hpr (t + 1) := by
  have hlen : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length = s.length :=
    ambientBlowupSeq_length hres hno T j hj I₀ E₀ s hpr
  have hblow : Blowup.IsBlowupAlongIdealSheaf ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t) :=
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isBlowup t (by rw [hlen]; exact ht)
  have hNt1 : IsNoetherian
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) :=
    isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr (t + 1) (by omega)
  have hnoetherian : TopologicalSpace.NoetherianSpace
      ↥((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) := inferInstance
  have hLNt1 : IsLocallyNoetherian
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) := inferInstance
  have hNs1 : IsNoetherian
      ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.obj (t + 1)) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s (t + 1) (by omega)
  have hLNs1 : IsLocallyNoetherian
      ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.obj (t + 1)) := inferInstance
  have hsm : Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    hgoingUp.smooth_structMap
  have hsncZ : HasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) :=
    hgoingUp.hasStrictNormalCrossingsWith_center_boundary hlift ht
  have hsncCons : HasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ::
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) :=
    hgoingUp.hasStrictNormalCrossingsWith_center_ker_cons hlift ht
  have hkerle : Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≤
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t :=
    ker_embeddingIntoAmbient_le_center hres hno T j hj I₀ E₀ s hpr t
  have hkersucc : Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1)) =
      Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
        (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)) :=
    ker_embeddingIntoAmbient_succ hres hno T j hj I₀ E₀ s hpr t ht
  have hps : ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1) =
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t :=
    structureMorphism_ambientBlowupSeq_succ hres hno T j hj I₀ E₀ s hpr t
  have hsmc : Smooth
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    smooth_comp_of_isBlowupAlongIdealSheaf hsncZ hblow
  have hsmsucc : Smooth
      (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) := by
    rw [hps]; exact hsmc
  have hsncSucc : InStrictNormalCrossingPosition (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1))
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1)) := by
    rw [hps, BlowupSequenceData.boundary_succ]
    exact inStrictNormalCrossingPosition_strictTransform_append
      (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) hblow hgoingUp.snc_bdry hsncZ
  have hidxt : j < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).length := hgoingUp.idx_lt
  have hidx : j < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1)).length := by
    have h1 : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).length = E₀.length + t :=
      BlowupSequenceData.boundary_length _ _ _
    have h2 : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1)).length
        = E₀.length + (t + 1) := BlowupSequenceData.boundary_length _ _ _
    omega
  have hmaplen : j < (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).map
      (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t))).length := by
    rw [List.length_map]; exact hidxt
  have hj2 : j < ((((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).map
        (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t))) ++
      [Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)]).length := by
    rw [List.length_append]
    omega
  have hget : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1))[j]'hidx =
      Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1)) := by
    rw [hkersucc, ← hgoingUp.bdry_getElem]
    refine (List.getElem_of_eq
      (BlowupSequenceData.boundary_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr) E₀ t) hidx).trans ?_
    exact getElem_map_append_of_lt_length_consolidated426
      (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t))
      [Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)]
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) j hidxt hj2
  have hcen : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).comap
      (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.center t := by
    rw [ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I₀ E₀ s hpr t]
    exact Blowup.comap_map_of_isClosedImmersion
      (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)
  have hA : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1)).eraseIdx j =
      List.map (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t))
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) ++
        [Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)] := by
    rw [BlowupSequenceData.boundary_succ, List.eraseIdx_append_of_lt_length hmaplen, List.eraseIdx_map]
  have hB := map_comap_strictTransform_append_exceptionalIdeal
    (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
    (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)
    (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1))
    (s.transitionMapSucc t)
    (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr t) hkersucc
    (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) hsncCons hkerle hblow
  have hbdrysucc : List.map
      (fun D => D.comap (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1)))
      (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1)).eraseIdx j) =
      s.boundary (t + 1) := by
    rw [hA, hB, hgoingUp.comap_eraseIdx, hcen]
    exact (s.boundary_succ t ht).symm
  have hKle : ∀ l, l ≤ T.mult →
      ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ≤
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t ^ (T.mult - l) :=
    fun l hl => hgoingUp.ambientDerivIdeal_le_center_pow hbal hm hV hlift ht l hl
  have hK' : ∀ l, l ≤ T.mult →
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t) ^ (T.mult - l) *
          ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1) =
        (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) := fun l hl =>
    BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr)
      (derivIdealSheafIterate T.base T.structMap l I₀) (T.mult - l) t
      (hgoingUp.exists_pow_mul_eq_comap_ambientDerivIdeal hbal hm hV hlift ht l hl)
  refine ⟨?_, hidx, ?_, hbdrysucc, hsncSucc, hget, hsmsucc⟩
  · intro l hl i hi
    by_cases hit : i < t
    · exact hgoingUp.divDeriv l hl i hit
    · have hie : i = t := by omega
      rw [hie]
      exact hgoingUp.exists_pow_mul_eq_comap_ambientDerivIdeal hbal hm hV hlift ht l hl
  · intro hsmooth instFt n hn
    have hsmS : Smooth
        (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) := hsmooth
    have hftS : LocallyOfFiniteType
        (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) := instFt
    have hest : ∀ m, m < T.mult →
        derivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) m
            (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr 0 t) ≤
          ⨆ l ≤ m, logDerivIdealSheafIterate T.base
            (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
            (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)) (m - l)
            (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t) := by
      intro m hm'
      rw [ambientDerivIdeal_order_zero_eq_controlledTransform]
      exact hgoingUp.deriv_le m hm'
    have key := derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_of_blowup
      T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t))
      (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j)
      hsncCons hkerle hblow T.mult
      (fun l => ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t) hKle hest
      (fun l => ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1)) hK' n hn
    have h0 : derivIdealSheafIterate T.base
          (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) n
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult (t + 1)) =
        derivIdealSheafIterate T.base
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) n
          (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr 0 (t + 1)) := by
      rw [ambientDerivIdeal_order_zero_eq_controlledTransform]
      exact derivIdealSheafIterate_congr
        (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1))
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
          ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) hps n _
    have h1 : (⨆ l ≤ n, logDerivIdealSheafIterate T.base
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
          (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
            (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t))) (n - l)
          (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1))) =
        ⨆ l ≤ n, logDerivIdealSheafIterate T.base
          (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1))
          (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1))) (n - l)
          (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1)) := by
      rw [hkersucc]
      exact iSup_congr fun l => iSup_congr fun _ =>
        logDerivIdealSheafIterate_congr
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
          (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) hps.symm _ _ _
    exact le_trans (le_of_eq h0) (le_trans key (le_of_eq h1))

end GoingUpInvariant

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.RestrictedBlowupEmbedding
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section

namespace DivisorReduction

variable (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)

def iteratedPreimage (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens) :
    (t : ℕ) → (s.toSequenceOfBlowups.schemeAt t).Opens
  | 0 => U₀
  | t + 1 => s.toSequenceOfBlowups.transitionMapSucc t ⁻¹ᵁ iteratedPreimage U₀ t

theorem iteratedPreimage_succ (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens) (t : ℕ) :
    iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1) =
      s.toSequenceOfBlowups.transitionMapSucc t ⁻¹ᵁ iteratedPreimage T j hj I₀ E₀ s U₀ t := rfl

def restrictedBlowupMorphism (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens) (t : ℕ) :
    (↑(iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)) : Scheme.{u}) ⟶
      (↑(iteratedPreimage T j hj I₀ E₀ s U₀ t) : Scheme.{u}) :=
  s.toSequenceOfBlowups.transitionMapSucc t ∣_ iteratedPreimage T j hj I₀ E₀ s U₀ t

section
variable (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens)

theorem restrictedBlowupMorphism_comp_ι (t : ℕ) :
    restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t ≫ (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι =
      (iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι ≫ s.toSequenceOfBlowups.transitionMapSucc t :=
  AlgebraicGeometry.morphismRestrict_ι (s.toSequenceOfBlowups.transitionMapSucc t)
    (iteratedPreimage T j hj I₀ E₀ s U₀ t)

theorem isClosed_iteratedPreimage (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))) (t : ℕ) :
    IsClosed ((iteratedPreimage T j hj I₀ E₀ s U₀ t : Set ↥(s.toSequenceOfBlowups.schemeAt t))) := by
  induction t with
  | zero => exact hU
  | succ n ih =>
      have hV : IsOpen ((iteratedPreimage T j hj I₀ E₀ s U₀ n : Set ↥(s.toSequenceOfBlowups.schemeAt n))ᶜ) :=
        ih.isOpen_compl
      have h2 : IsOpen
          (((s.toSequenceOfBlowups.transitionMapSucc n ⁻¹ᵁ
              (⟨(iteratedPreimage T j hj I₀ E₀ s U₀ n : Set ↥(s.toSequenceOfBlowups.schemeAt n))ᶜ, hV⟩ :
                (s.toSequenceOfBlowups.schemeAt n).Opens)) : (s.toSequenceOfBlowups.schemeAt (n + 1)).Opens) :
            Set ↥(s.toSequenceOfBlowups.schemeAt (n + 1))) :=
        TopologicalSpace.Opens.isOpen _
      have hop : IsOpen ((iteratedPreimage T j hj I₀ E₀ s U₀ (n + 1) :
          Set ↥(s.toSequenceOfBlowups.schemeAt (n + 1)))ᶜ) := h2
      exact isOpen_compl_iff.mp hop

theorem smooth_iteratedPreimage_ι_comp_projectionToSpec (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (t : ℕ) (ht : t ≤ s.toSequenceOfBlowups.length) :
    Smooth ((iteratedPreimage T j hj I₀ E₀ s U₀ t).ι ≫ s.projectionToSpec t) := by
  have : Smooth (s.projectionToSpec t) :=
    MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hV s t ht
  infer_instance

theorem support_center_comap_subset_orderAtLeastLocus (_hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (t : ℕ) (ht : t < s.toSequenceOfBlowups.length) :
    (((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι).support : Set _) ⊆
      orderAtLeastLocus ((s.ideal t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) T.mult := by
  intro y hy
  have hy0 : y ∈ ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι).support := hy
  have hy1 : (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι.base y ∈ (s.toSequenceOfBlowups.center t).support := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] at hy0
    exact hy0
  have hy2 : (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι.base y ∈
      ((s.toSequenceOfBlowups.center t).support : Set ↥(s.toSequenceOfBlowups.schemeAt t)) := hy1
  have hc : (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι.base y ∈ orderAtLeastLocus (s.ideal t) T.mult :=
    s.center_order t ht hy2
  have hord : (T.mult : ℕ∞) ≤
      orderAt (s.ideal t) ((iteratedPreimage T j hj I₀ E₀ s U₀ t).ι.base y) :=
    (mem_orderAtLeastLocus_iff _ _ _).1 hc
  refine (mem_orderAtLeastLocus_iff _ _ _).2 ?_
  rw [orderAt_comap_of_isOpenImmersion]
  exact hord


end

section
variable (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens) (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (t : ℕ) (ht : t < s.toSequenceOfBlowups.length)
include hV ht

theorem hasStrictNormalCrossingsWith_iteratedPreimage :
    HasStrictNormalCrossingsWith ((iteratedPreimage T j hj I₀ E₀ s U₀ t).ι ≫ s.projectionToSpec t)
      ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι)
      (List.map (fun D => D.comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) (s.boundary t)) := by
  have : Smooth (s.projectionToSpec t) :=
    MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hV s t (le_of_lt ht)
  have hZE : HasStrictNormalCrossingsWith (s.projectionToSpec t) (s.toSequenceOfBlowups.center t) (s.boundary t) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact s.center_snc t ht
  exact hasStrictNormalCrossingsWith_comap (s.projectionToSpec t) (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι
    (s.toSequenceOfBlowups.center t) (s.boundary t) hZE

theorem boundary_comap_iteratedPreimage_succ :
    List.map (fun D => D.comap (iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι) (s.boundary (t + 1)) =
      List.map
          (Blowup.strictTransform (restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t)
            ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι))
          (List.map (fun D => D.comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) (s.boundary t)) ++
        [Blowup.exceptionalIdeal (restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t)
            ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι)] := by
  have : IsNoetherian (s.toSequenceOfBlowups.schemeAt (t + 1)) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s (t + 1) ht
  have : IsLocallyNoetherian (s.toSequenceOfBlowups.schemeAt (t + 1)) := inferInstance
  have hex : (Blowup.exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc t) (s.toSequenceOfBlowups.center t)).comap
        (iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι =
      Blowup.exceptionalIdeal (restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t)
        ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) :=
    restrictIdeal_exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc t) (s.toSequenceOfBlowups.center t)
      (iteratedPreimage T j hj I₀ E₀ s U₀ t)
  have hst : ∀ D : (s.toSequenceOfBlowups.schemeAt t).IdealSheafData,
      (Blowup.strictTransform (s.toSequenceOfBlowups.transitionMapSucc t) (s.toSequenceOfBlowups.center t) D).comap
          (iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι =
        Blowup.strictTransform (restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t)
          ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι)
          (D.comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) := fun D =>
    restrictIdeal_strictTransform_preimage (s.toSequenceOfBlowups.transitionMapSucc t) (s.toSequenceOfBlowups.center t) D
      (iteratedPreimage T j hj I₀ E₀ s U₀ t)
  rw [s.boundary_succ t ht]
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, hex]
  congr 1
  exact List.map_congr_left fun D _ => hst D


end

section

variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})

def restrictedEmbedding [IsNoetherian T.scheme]
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens) (t : ℕ) :
    (↑(iteratedPreimage T j hj I₀ E₀ s U₀ t) : Scheme.{u}) ⟶ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t :=
  (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t

section
variable [IsNoetherian T.scheme] (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens)

theorem restrictedEmbedding_eq_ι_comp_embeddingIntoAmbient (t : ℕ) :
    restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t =
      (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t := rfl

theorem isClosedImmersion_restrictedEmbedding (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))) (t : ℕ) :
    IsClosedImmersion (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) := by
  have hι : IsClosedImmersion (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι :=
    Scheme.Opens.isClosedImmersion_ι_of_isClosed (iteratedPreimage T j hj I₀ E₀ s U₀ t)
      (isClosed_iteratedPreimage T j hj I₀ E₀ s U₀ hU t)
  have hemb : IsClosedImmersion (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) :=
    isClosedImmersion_embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t
  rw [restrictedEmbedding_eq_ι_comp_embeddingIntoAmbient]
  exact @IsClosedImmersion.comp _ _ _ _ _ hι hemb

theorem restrictedEmbedding_comp_blowupMorphism (t : ℕ) :
    restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ (t + 1) ≫
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t =
      restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t ≫ restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t := by
  have h1 := embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr t
  have h2 := restrictedBlowupMorphism_comp_ι T j hj I₀ E₀ s U₀ t
  have e1 : restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ (t + 1) ≫
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t =
      (iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι ≫
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) := by
    rw [restrictedEmbedding_eq_ι_comp_embeddingIntoAmbient]
    exact Category.assoc _ _ _
  have e2 : (iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι ≫
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) =
      (iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι ≫
        (s.toSequenceOfBlowups.transitionMapSucc t ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) :=
    congrArg (fun g => (iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι ≫ g) h1
  have e3 : (iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι ≫
        (s.toSequenceOfBlowups.transitionMapSucc t ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) =
      ((iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι ≫ s.toSequenceOfBlowups.transitionMapSucc t) ≫
        embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t := (Category.assoc _ _ _).symm
  have e4 : ((iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι ≫ s.toSequenceOfBlowups.transitionMapSucc t) ≫
        embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t =
      (restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t ≫ (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) ≫
        embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t :=
    congrArg (fun f => f ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) h2.symm
  have e5 : (restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t ≫ (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) ≫
        embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t =
      restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t ≫ restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t := by
    rw [restrictedEmbedding_eq_ι_comp_embeddingIntoAmbient]
    exact Category.assoc _ _ _
  exact e1.trans (e2.trans (e3.trans (e4.trans e5)))

theorem restrictedEmbedding_comp_structureMorphism_ambientBlowupSeq (t : ℕ) :
    restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t =
      (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι ≫ s.projectionToSpec t := by
  have h1 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
      s.toSequenceOfBlowups.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀ :=
    embeddingIntoAmbient_comp_projectionToBase hres hno T j hj I₀ E₀ s hpr t
  have h2 : (s.toSequenceOfBlowups.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) ≫ T.structMap = s.projectionToSpec t :=
    (Category.assoc (s.toSequenceOfBlowups.projectionToBase t) (divisorEmbedding T j hj I₀ E₀) T.structMap).trans
      (MarkedSequenceOfBlowups.projectionToSpec_eq s t).symm
  have h3 : (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) ≫ T.structMap = s.projectionToSpec t := by
    rw [h1]
    exact h2
  have key : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
      ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t = s.projectionToSpec t :=
    (Category.assoc (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) T.structMap).symm.trans h3
  have e1 : restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t =
      (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι ≫
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) := by
    rw [restrictedEmbedding_eq_ι_comp_embeddingIntoAmbient]
    exact Category.assoc _ _ _
  exact e1.trans (congrArg (fun g => (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι ≫ g) key)

theorem ker_restrictedEmbedding_succ (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))) (t : ℕ)
    (ht : t < s.toSequenceOfBlowups.length) :
    Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ (t + 1)) =
      Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
        (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)) := by
  have hlen : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.length = s.toSequenceOfBlowups.length := by
    rw [MarkedBlowupSequenceData.blowupSequenceData_ofMarkedSequence, BlowupSequenceData.ofSequenceOfBlowups_length]
  have htlt : t < (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.length := by
    rw [hlen]; exact ht
  have htle : t + 1 ≤ (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.length := htlt
  have : IsNoetherian
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) :=
    isNoetherian_ambientBlowupSequence_schemeAt (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr (t + 1) htle
  have : IsLocallyNoetherian
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) := inferInstance
  have hker : Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1)) =
      Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
        (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)) :=
    ker_embeddingIntoAmbientBlowupSequence_succ (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t htlt
  have h := ker_preimage_ι_comp_eq_strictTransform_of_isClopen
      (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)
      (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1))
      (s.toSequenceOfBlowups.transitionMapSucc t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
      (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      (iteratedPreimage T j hj I₀ E₀ s U₀ t) (isClosed_iteratedPreimage T j hj I₀ E₀ s U₀ hU t) hker
  rw [restrictedEmbedding_eq_ι_comp_embeddingIntoAmbient, restrictedEmbedding_eq_ι_comp_embeddingIntoAmbient, iteratedPreimage_succ]
  exact h


end

section
variable (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens)

private theorem support_ideal_subset_iteratedPreimage_consolidated427 (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) :
    ∀ t : ℕ, t ≤ s.toSequenceOfBlowups.length →
      (((s.ideal t).support : Set ↥(s.toSequenceOfBlowups.schemeAt t))) ⊆
        ((iteratedPreimage T j hj I₀ E₀ s U₀ t : Set ↥(s.toSequenceOfBlowups.schemeAt t))) := by
  intro t
  induction t with
  | zero =>
      intro _
      exact hsupp
  | succ n ih =>
      intro hn
      have hn' : n < s.toSequenceOfBlowups.length := hn
      have h1 := s.support_ideal_succ_subset_preimage n hn'
      have h2 := ih (le_of_lt hn')
      intro x hx
      have hx1 : (s.toSequenceOfBlowups.transitionMapSucc n).base x ∈
          (((s.ideal n).support : Set ↥(s.toSequenceOfBlowups.schemeAt n))) := h1 hx
      exact h2 hx1

private theorem support_center_subset_iteratedPreimage_consolidated427 (hm : 1 ≤ T.mult)
    (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))
    (t : ℕ) (ht : t < s.toSequenceOfBlowups.length) :
    (((s.toSequenceOfBlowups.center t).support : Set ↥(s.toSequenceOfBlowups.schemeAt t))) ⊆
      ((iteratedPreimage T j hj I₀ E₀ s U₀ t : Set ↥(s.toSequenceOfBlowups.schemeAt t))) := by
  intro x hx
  have h1 : x ∈ orderAtLeastLocus (s.ideal t) T.mult := s.center_order t ht hx
  have h2 : x ∈ orderAtLeastLocus (s.ideal t) 1 :=
    orderAtLeastLocus_subset_of_le (s.ideal t) hm h1
  have h3 : x ∈ (s.ideal t).support := (mem_orderAtLeastLocus_one_iff _ _).1 h2
  have h4 : x ∈ (((s.ideal t).support : Set ↥(s.toSequenceOfBlowups.schemeAt t))) := h3
  exact support_ideal_subset_iteratedPreimage_consolidated427 T j hj I₀ E₀ s U₀ hsupp t (le_of_lt ht) h4


end

private theorem imageIdealSheaf_comp_of_eq_consolidated427 {S X P : Scheme.{u}} (ι : S ⟶ X) (emb : X ⟶ P)
    (J : S.IdealSheafData) (Z : X.IdealSheafData) (hJ : imageIdealSheaf ι J = Z) :
    imageIdealSheaf (ι ≫ emb) J = imageIdealSheaf emb Z := by
  subst hJ
  exact Scheme.IdealSheafData.map_comp J ι emb

theorem center_ambientBlowupSeq_eq_imageIdealSheaf [IsNoetherian T.scheme]
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
    (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))) (hm : 1 ≤ T.mult)
    (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))
    (t : ℕ) (ht : t < s.toSequenceOfBlowups.length) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t =
      imageIdealSheaf (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)
        ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) := by
  have hcl : IsClosed ((iteratedPreimage T j hj I₀ E₀ s U₀ t : Set ↥(s.toSequenceOfBlowups.schemeAt t))) :=
    isClosed_iteratedPreimage T j hj I₀ E₀ s U₀ hU t
  have : IsClosedImmersion (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι :=
    Scheme.Opens.isClosedImmersion_ι_of_isClosed _ hcl
  have hsub : (((s.toSequenceOfBlowups.center t).support : Set ↥(s.toSequenceOfBlowups.schemeAt t))) ⊆
      ((iteratedPreimage T j hj I₀ E₀ s U₀ t : Set ↥(s.toSequenceOfBlowups.schemeAt t))) :=
    support_center_subset_iteratedPreimage_consolidated427 T j hj I₀ E₀ s U₀ hm hsupp t ht
  have h1 : imageIdealSheaf (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι
        ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι)
      = s.toSequenceOfBlowups.center t :=
    imageIdealSheaf_comap_ι_eq_self_of_support_subset (s.toSequenceOfBlowups.center t)
      (iteratedPreimage T j hj I₀ E₀ s U₀ t) hcl hsub
  rw [ambientBlowupSeq_center_eq_imageIdealSheaf, restrictedEmbedding_eq_ι_comp_embeddingIntoAmbient]
  exact (imageIdealSheaf_comp_of_eq_consolidated427 (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι
    (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)
    ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι)
    (s.toSequenceOfBlowups.center t) h1).symm

end

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupMarked
section

open CategoryTheory AlgebraicGeometry

section

namespace BlowupSequenceData

theorem IsMarked.of_comap_isoObjZero_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {d : BlowupSequenceData X} {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ}
    {I I' : X.IdealSheafData} {E E' : List X.IdealSheafData}
    (hI : I.comap d.isoZero.hom = I'.comap d.isoZero.hom)
    (hE : List.map (fun D => D.comap d.isoZero.hom) E =
      List.map (fun D => D.comap d.isoZero.hom) E')
    (h : d.IsMarked p I m E) : d.IsMarked p I' m E' := by
  have hIc : ∀ t : ℕ, d.controlledTransform I m t = d.controlledTransform I' m t := fun t =>
    d.controlledTransform_congr I I' (by rw [d.projectionToBase_zero]; exact hI) m t
  have hEc : ∀ t : ℕ, d.boundaryFrom E t = d.boundaryFrom E' t := fun t =>
    d.boundary_congr E E' (by simp only [d.projectionToBase_zero]; exact hE) t
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [← hIc i]
    exact h.divisible i hi
  · intro i hi
    rw [← hIc i]
    exact h.center_order i hi
  · exact h.center_smooth
  · intro i hi
    rw [← hEc i]
    exact h.center_snc i hi

end BlowupSequenceData

namespace DivisorReduction

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] [Smooth T.structMap] [LocallyOfFiniteType T.structMap] [CharZero T.base] (j : ℕ) (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups) (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult) (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u}) (hE₀ : InStrictNormalCrossingPosition T.structMap E₀) (hjE : j < E₀.length) (hget : E₀[j] = T.boundary[j]) (htrunc : List.take (T.boundary.length - 1) (E₀.eraseIdx j) = E₀.eraseIdx j)
include hbal hm hV hlift hE₀ hjE hget htrunc

theorem goingUpInvariant_of_le (t : ℕ) (ht : t ≤ s.length) :
    GoingUpInvariant hres hno T j hj I₀ E₀ s hpr t := by
  induction t with
  | zero => exact goingUpInvariant_zero hres hno T j hj I₀ E₀ s hpr hE₀ hjE hget htrunc
  | succ n ih =>
      exact GoingUpInvariant.succ (ih (Nat.le_of_succ_le ht)) hbal hm hV hlift (Nat.lt_of_succ_le ht)

theorem isMarked_ambientBlowupSeq :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).IsMarked T.structMap I₀ T.mult E₀ := by
  have hlen : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length = s.length :=
    ambientBlowupSeq_length hres hno T j hj I₀ E₀ s hpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hlen] at hi
    exact (goingUpInvariant_of_le hres hno T j hj I₀ E₀ s hpr hbal hm hV hlift hE₀ hjE hget htrunc
      (i + 1) hi).exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform i (Nat.lt_succ_self i)
  · intro i hi
    rw [hlen] at hi
    exact (goingUpInvariant_of_le hres hno T j hj I₀ E₀ s hpr hbal hm hV hlift hE₀ hjE hget htrunc
      i (le_of_lt hi)).support_center_subset_orderAtLeastLocus hbal hm hV hi
  · intro i hi
    rw [hlen] at hi
    exact smooth_ambientBlowupSeq_center_comp hres hno T j hj I₀ E₀ s hpr i hi
  · intro i hi
    rw [hlen] at hi
    exact (goingUpInvariant_of_le hres hno T j hj I₀ E₀ s hpr hbal hm hV hlift hE₀ hjE hget htrunc
      i (le_of_lt hi)).hasStrictNormalCrossingsWith_center_boundary hlift hi

theorem comap_controlledTransform_ambientBlowupSeq (t : ℕ) (ht : t ≤ s.length) :
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.ideal t :=
  (goingUpInvariant_of_le hres hno T j hj I₀ E₀ s hpr hbal hm hV hlift hE₀ hjE hget htrunc
    t ht).comap_controlledTransform ht


end

private theorem lowerIdealWithoutBlowup_eq_ideal_consolidated450 (T : MarkedIdealWithBoundary.{u}) :
    lowerIdealWithoutBlowup T = T.ideal :=
  Scheme.IdealSheafData.comap_id T.ideal

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (hlift : StrictNormalCrossingsLiftFromDivisor.{u}) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) [IsNoetherian T.scheme] (_hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) (hbal : ∀ [_inst : LocallyOfFiniteType T.structMap], IsDerivBalanced T.base T.structMap T.ideal T.mult) (j : ℕ) (hj : j < T.boundary.length) (_hZ : containedComponentsIdeal T j hj = ⊤) (hVlow : (restrictToDivisor T j hj).IsAdmissible) (s : (restrictToDivisor T j hj).SequenceOfBlowups) (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
include hlift hV _hord hbal _hZ hVlow

theorem isMarked_ambientBlowupSeq_of_containedComponentsIdeal_eq_top
    :
    (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.smooth
  have hbdry : lowerBoundaryWithoutBlowup T = T.boundary := lowerBoundaryWithoutBlowup_eq T
  have hideal : lowerIdealWithoutBlowup T = T.ideal := lowerIdealWithoutBlowup_eq_ideal_consolidated450 T
  have hjE : j < (lowerBoundaryWithoutBlowup T).length := by rw [hbdry]; exact hj
  have hE₀ : InStrictNormalCrossingPosition T.structMap (lowerBoundaryWithoutBlowup T) := by rw [hbdry]; exact hV.snc
  have hgetAll : ∀ h : j < (lowerBoundaryWithoutBlowup T).length,
      (lowerBoundaryWithoutBlowup T)[j]'h = T.boundary[j] := by
    rw [hbdry]
    intro _
    rfl
  have hlen1 : (T.boundary.eraseIdx j).length = T.boundary.length - 1 := by
    simp [List.length_eraseIdx, hj]
  have htrunc : List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j)
      = (lowerBoundaryWithoutBlowup T).eraseIdx j := by
    rw [hbdry, ← hlen1, List.take_length]
  have hbal' : IsDerivBalanced T.base T.structMap (lowerIdealWithoutBlowup T) T.mult := by
    rw [hideal]; exact hbal
  have main := isMarked_ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr
    hbal' hV.one_le_mult hVlow hlift hE₀ hjE (hgetAll hjE) htrunc
  exact BlowupSequenceData.IsMarked.of_comap_isoObjZero_eq (by simp only [hideal]) (by simp only [hbdry]) main

theorem comap_controlledTransform_of_containedComponentsIdeal_eq_top
    (t : ℕ) (ht : t ≤ s.length) :
    ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
        T.ideal T.mult t).comap
      (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t) = s.ideal t := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.smooth
  have hbdry : lowerBoundaryWithoutBlowup T = T.boundary := lowerBoundaryWithoutBlowup_eq T
  have hideal : lowerIdealWithoutBlowup T = T.ideal := lowerIdealWithoutBlowup_eq_ideal_consolidated450 T
  have hjE : j < (lowerBoundaryWithoutBlowup T).length := by rw [hbdry]; exact hj
  have hE₀ : InStrictNormalCrossingPosition T.structMap (lowerBoundaryWithoutBlowup T) := by rw [hbdry]; exact hV.snc
  have hgetAll : ∀ h : j < (lowerBoundaryWithoutBlowup T).length,
      (lowerBoundaryWithoutBlowup T)[j]'h = T.boundary[j] := by
    rw [hbdry]
    intro _
    rfl
  have hlen1 : (T.boundary.eraseIdx j).length = T.boundary.length - 1 := by
    simp [List.length_eraseIdx, hj]
  have htrunc : List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j)
      = (lowerBoundaryWithoutBlowup T).eraseIdx j := by
    rw [hbdry, ← hlen1, List.take_length]
  have hbal' : IsDerivBalanced T.base T.structMap (lowerIdealWithoutBlowup T) T.mult := by
    rw [hideal]; exact hbal
  have main := comap_controlledTransform_ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr
    hbal' hV.one_le_mult hVlow hlift hE₀ hjE (hgetAll hjE) htrunc t ht
  have hc := BlowupSequenceData.controlledTransform_congr
    (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr)
    (lowerIdealWithoutBlowup T) T.ideal (by simp only [hideal]) T.mult t
  rw [← hc]
  exact main


end

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariantOnOpens
section

open CategoryTheory AlgebraicGeometry

section

section
variable {X : Scheme.{u}} {D : X.IdealSheafData}

private theorem filterNeTop_cons_of_eq_top_consolidated451 (h : D = ⊤) (E : List X.IdealSheafData) :
    filterNeTop (D :: E) = filterNeTop E := by
  subst h
  simp [filterNeTop]

private theorem filterNeTop_cons_of_ne_top_consolidated451 (h : D ≠ ⊤) (E : List X.IdealSheafData) :
    filterNeTop (D :: E) = D :: filterNeTop E := by
  simp [filterNeTop, h]


end

section
variable {Y : Scheme.{u}}

private theorem filterNeTop_append_consolidated451 (A B : List Y.IdealSheafData) :
    filterNeTop (A ++ B) = filterNeTop A ++ filterNeTop B := by
  simp only [filterNeTop, List.filter_append]

private theorem filterNeTop_cons_congr_consolidated451 (a : Y.IdealSheafData)
    {L L' : List Y.IdealSheafData} (h : filterNeTop L = filterNeTop L') :
    filterNeTop (a :: L) = filterNeTop (a :: L') := by
  by_cases ha : a = ⊤
  · rw [filterNeTop_cons_of_eq_top_consolidated451 ha L, filterNeTop_cons_of_eq_top_consolidated451 ha L']
    exact h
  · rw [filterNeTop_cons_of_ne_top_consolidated451 ha L, filterNeTop_cons_of_ne_top_consolidated451 ha L', h]


end

section
variable {X Y : Scheme.{u}} (f : X.IdealSheafData → Y.IdealSheafData) (hf : f ⊤ = ⊤)
include hf

private theorem filterNeTop_map_filterNeTop_consolidated451 (E : List X.IdealSheafData) :
    filterNeTop (List.map f E) = filterNeTop (List.map f (filterNeTop E)) := by
  induction E with
  | nil => simp [filterNeTop]
  | cons a E ih =>
    by_cases ha : a = ⊤
    · have h1 : filterNeTop (a :: E) = filterNeTop E := filterNeTop_cons_of_eq_top_consolidated451 ha E
      have h2 : f a = ⊤ := by rw [ha]; exact hf
      have h3 : filterNeTop (List.map f (a :: E)) = filterNeTop (List.map f E) := by
        rw [List.map_cons]
        exact filterNeTop_cons_of_eq_top_consolidated451 h2 (List.map f E)
      rw [h1, h3]
      exact ih
    · have h1 : filterNeTop (a :: E) = a :: filterNeTop E := filterNeTop_cons_of_ne_top_consolidated451 ha E
      rw [h1]
      simp only [List.map_cons]
      exact filterNeTop_cons_congr_consolidated451 (f a) ih

theorem filterNeTop_map_append_congr (D : Y.IdealSheafData)
    (E E' : List X.IdealSheafData) (h : filterNeTop E = filterNeTop E') :
    filterNeTop (List.map f E ++ [D]) = filterNeTop (List.map f E' ++ [D]) := by
  rw [filterNeTop_append_consolidated451 (List.map f E) [D], filterNeTop_append_consolidated451 (List.map f E') [D],
    filterNeTop_map_filterNeTop_consolidated451 f hf E, filterNeTop_map_filterNeTop_consolidated451 f hf E', h]


end

namespace DivisorReduction

theorem ker_restrictedEmbedding_le_center (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
    (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))) (hm : 1 ≤ T.mult)
    (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))
    (t : ℕ) (ht : t < s.length) :
    Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) ≤
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t := by
  have hlt : t < s.toSequenceOfBlowups.length := ht
  have hc := center_ambientBlowupSeq_eq_imageIdealSheaf T j hj I₀ E₀ s hres hno hpr U₀ hU hm hsupp t hlt
  rw [hc, imageIdealSheaf_eq_ker_subschemeι_comp]
  exact Scheme.Hom.le_ker_comp _ _

structure GoingUpInvariantOnOpen (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens) (t : ℕ) : Prop where
  divDeriv : ∀ l ≤ T.mult, ∀ i < t,
    ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center i) ^ (T.mult - l) * B =
        (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l i).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
  idx_lt : j < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).length
  deriv_le : ∀ [_instFt : LocallyOfFiniteType
        (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)], ∀ n < T.mult,
      derivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) n
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t) ≤
        ⨆ l ≤ n, logDerivIdealSheafIterate T.base
          (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
          (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)) (n - l)
          (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t)
  comap_eraseIdx :
    filterNeTop (List.map (fun D => D.comap (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t))
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j)) =
      filterNeTop (List.map (fun D => D.comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) (s.boundary t))
  snc_bdry : InStrictNormalCrossingPosition (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t)
  bdry_getElem : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t)[j]'idx_lt =
      Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)
  smooth_structMap :
    Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)

namespace GoingUpInvariantOnOpen

theorem exists_pow_mul_eq_comap_controlledTransform {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [IsNoetherian T.scheme] [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent}
    {U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens} {t : ℕ}
    (hinv : GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ t) :
    ∀ i < t, ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center i) ^ T.mult * B =
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult i).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i) := by
  intro i hi
  obtain ⟨B, hB⟩ := hinv.divDeriv 0 (Nat.zero_le _) i hi
  refine ⟨B, ?_⟩
  have h0 : ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr 0 i =
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult i :=
    ambientDerivIdeal_order_zero_eq_controlledTransform hres hno T j hj I₀ E₀ s hpr i
  simp only [Nat.sub_zero] at hB
  rw [hB, h0]

private theorem comap_comap_of_commSq_consolidated451 {X A A' B : Scheme.{u}} (ι : A' ⟶ A) (p : A ⟶ X)
    (q : A' ⟶ B) (e : B ⟶ X) (I : X.IdealSheafData) (hsq : ι ≫ p = q ≫ e) :
    (I.comap p).comap ι = (I.comap e).comap q := by
  rw [← Scheme.IdealSheafData.comap_comp, hsq, Scheme.IdealSheafData.comap_comp]

private theorem comap_eq_of_pow_mul_comap_eq_consolidated451 {A A' B B' : Scheme.{u}} (m : ℕ)
    (π : B ⟶ A) (ιA : A' ⟶ A) (ιB : B' ⟶ B) (ρ : B' ⟶ A')
    (C J : A.IdealSheafData) (J' : B.IdealSheafData)
    (c jt : A'.IdealSheafData) (jt' : B'.IdealSheafData)
    (hsq : ιB ≫ π = ρ ≫ ιA)
    (hcen : C.comap ιA = c)
    (hprev : J.comap ιA = jt)
    (hpow : Blowup.exceptionalIdeal π C ^ m * J' = J.comap π)
    (hsucc : Blowup.exceptionalIdeal ρ c ^ m * jt' = jt.comap ρ)
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal ρ c)) :
    J'.comap ιB = jt' := by
  have hexc : (Blowup.exceptionalIdeal π C).comap ιB = Blowup.exceptionalIdeal ρ c := by
    rw [Blowup.exceptionalIdeal_eq_comap, Blowup.exceptionalIdeal_eq_comap, ← Scheme.IdealSheafData.comap_comp, hsq,
      Scheme.IdealSheafData.comap_comp, hcen]
  have hkey : Blowup.exceptionalIdeal ρ c ^ m * J'.comap ιB = Blowup.exceptionalIdeal ρ c ^ m * jt' := by
    rw [hsucc, ← hexc, ← Scheme.IdealSheafData.comap_pow, ← Scheme.IdealSheafData.comap_mul,
      hpow, ← Scheme.IdealSheafData.comap_comp, hsq, Scheme.IdealSheafData.comap_comp, hprev]
  exact (hcart.pow m).eq_of_mul_eq_mul hkey

private theorem comap_controlledTransform_embeddingIntoAmbient_consolidated451
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    t ≤ s.length →
    (∀ i < t, ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center i) ^ T.mult * B =
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult i).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)) →
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.ideal t := by
  induction t with
  | zero =>
      intro _ _
      have hs0 : s.projectionToBase 0 = s.isoZero.hom := by
        rw [← BlowupSequenceData.ofSequenceOfBlowups_projectionToBase s.toSequenceOfBlowups 0, BlowupSequenceData.projectionToBase_zero,
          BlowupSequenceData.ofSequenceOfBlowups_isoObjZero]
      have hsq := (embeddingIntoAmbient_comp_projectionToBase hres hno T j hj I₀ E₀ s hpr 0).trans
        (congrArg (fun f => f ≫ divisorEmbedding T j hj I₀ E₀) hs0)
      have hb := comap_comap_of_commSq_consolidated451 (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase 0) s.isoZero.hom
        (divisorEmbedding T j hj I₀ E₀) I₀ hsq
      rw [BlowupSequenceData.projectionToBase_zero] at hb
      rw [BlowupSequenceData.controlledTransform_zero]
      exact hb.trans s.ideal_zero.symm
  | succ t ih =>
      intro ht hdiv
      have htlt : t < s.length := Nat.lt_of_succ_le ht
      have hprev := ih (Nat.le_of_lt htlt) (fun i hi => hdiv i (Nat.lt_succ_of_lt hi))
      have := isClosedImmersion_embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t
      have hcen : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).comap
            (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.center t := by
        rw [ambientBlowupSeq_center_eq_imageIdealSheaf]
        exact Blowup.comap_map_of_isClosedImmersion _ _
      have hpow : Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t) ^ T.mult *
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult (t + 1) =
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) :=
        BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr) I₀ T.mult t
          (hdiv t (Nat.lt_succ_self t))
      have hblow : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc t) (s.center t) :=
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.isBlowup t
          (by rw [MarkedBlowupSequenceData.ofMarkedSequence_length]; exact htlt)
      exact comap_eq_of_pow_mul_comap_eq_consolidated451 T.mult ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1)) (s.transitionMapSucc t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult (t + 1))
        (s.center t) (s.ideal t) (s.ideal (t + 1))
        (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr t) hcen hprev hpow
        (s.ideal_succ t htlt) (isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hblow)

section
variable {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}} {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}} [IsNoetherian T.scheme] [Smooth T.structMap] [LocallyOfFiniteType T.structMap] {j : ℕ} {hj : j < T.boundary.length} {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData} {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups} {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent} {U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens} {t : ℕ} (hinv : GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ t) (ht : t ≤ s.length)
include hinv ht

theorem comap_controlledTransform :
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.ideal t :=
  comap_controlledTransform_embeddingIntoAmbient_consolidated451 hres hno T j hj I₀ E₀ s hpr t ht hinv.exists_pow_mul_eq_comap_controlledTransform

theorem comap_controlledTransform_restrictedEmbedding :
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) =
      (s.ideal t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι := by
  refine Eq.trans (Scheme.IdealSheafData.comap_comp ..) ?_
  exact congrArg
    (fun I : (s.toSequenceOfBlowups.schemeAt t).IdealSheafData =>
      I.comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι)
    (comap_controlledTransform hinv ht)


end

theorem support_center_subset_orderAtLeastLocus {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [IsNoetherian T.scheme] [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap] [CharZero T.base]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent}
    {U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens} {t : ℕ}
    (hinv : GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ t)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible)
    (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0))))
    (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))
    (ht : t < s.length) :
    (↑((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).support :
        Set ↥((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t)) ⊆
      orderAtLeastLocus ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t) T.mult := by
  have ht' : t < s.toSequenceOfBlowups.length := ht
  have htle : t ≤ s.length := le_of_lt ht
  have hmpos : 0 < T.mult := hm
  have : Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    hinv.smooth_structMap
  have : IsClosedImmersion
      (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) :=
    isClosedImmersion_restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ hU t
  have : Smooth
      (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) := by
    rw [restrictedEmbedding_comp_structureMorphism_ambientBlowupSeq T j hj I₀ E₀ s hres hno hpr U₀ t]
    exact smooth_iteratedPreimage_ι_comp_projectionToSpec T j hj I₀ E₀ s U₀ hV t (le_of_lt ht')
  have hdom := hinv.deriv_le (T.mult - 1) (Nat.sub_lt hmpos Nat.one_pos)
  have hbal' : ∀ l < T.mult,
      ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ^ T.mult ≤
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t ^ (T.mult - l) := by
    intro l hl
    exact pow_ambientDerivIdeal_le_pow_controlledTransform hres hno T j hj I₀ E₀ s hpr hbal l hl t htle
      (hinv.exists_pow_mul_eq_comap_controlledTransform) (hinv.divDeriv l (le_of_lt hl))
  have hc : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t =
      imageIdealSheaf (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)
        ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) :=
    center_ambientBlowupSeq_eq_imageIdealSheaf T j hj I₀ E₀ s hres hno hpr U₀ hU hm hsupp t ht'
  have hkey : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
      (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) =
      (s.ideal t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι :=
    comap_controlledTransform_restrictedEmbedding hinv htle
  intro x hx
  rw [hc, support_imageIdealSheaf_eq_image_support] at hx
  obtain ⟨y, hy0, rfl⟩ := hx
  have hy1 : y ∈ orderAtLeastLocus ((s.ideal t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) T.mult :=
    support_center_comap_subset_orderAtLeastLocus T j hj I₀ E₀ s U₀ hV t ht' hy0
  have hy2 : y ∈ orderAtLeastLocus
      (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)) T.mult := by
    rw [hkey]
    exact hy1
  exact base_mem_orderAtLeastLocus_of_mem_comap T.base
    (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
    (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) T.mult hm
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t)
    (fun l => ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t) hdom hbal' y hy2

section
variable {A S P : Scheme.{u}}

private theorem ker_comp_eq_ker_subschemeι_comp_consolidated451 (g : A ⟶ S)
    [IsClosedImmersion g] (f : S ⟶ P) :
    Scheme.Hom.ker (g ≫ f) = Scheme.Hom.ker ((Scheme.Hom.ker g).subschemeι ≫ f) := by
  symm
  rw [← kerSubschemeIso_hom_comp g, Category.assoc, Scheme.Hom.ker_comp_of_isIso]

private theorem imageIdealSheaf_iso_hom_comp_eq_consolidated451 (e : A ≅ S) (f : S ⟶ P)
    (C : A.IdealSheafData) :
    imageIdealSheaf (e.hom ≫ f) C = imageIdealSheaf f (C.comap e.inv) := by
  have : IsClosedImmersion (C.subschemeι ≫ e.hom) := inferInstance
  have hker : Scheme.Hom.ker (C.subschemeι ≫ e.hom) = C.comap e.inv := by
    rw [← imageIdealSheaf_eq_ker_subschemeι_comp]
    exact imageIdealSheaf_hom_eq_comap_inv e C
  rw [imageIdealSheaf_eq_ker_subschemeι_comp, imageIdealSheaf_eq_ker_subschemeι_comp, ← Category.assoc,
    ker_comp_eq_ker_subschemeι_comp_consolidated451 (C.subschemeι ≫ e.hom) f, hker]


end

section
variable {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}} {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}} [IsNoetherian T.scheme] [Smooth T.structMap] [LocallyOfFiniteType T.structMap] [CharZero T.base] {j : ℕ} {hj : j < T.boundary.length} {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData} {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups} {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent} {U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens} {t : ℕ} (hinv : GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ t) (hlift : StrictNormalCrossingsLiftFromDivisor.{u}) (hm : 1 ≤ T.mult) (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))) (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆ (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) (ht : t < s.length)
include hinv hlift hm hV hU hsupp ht

theorem hasStrictNormalCrossingsWith_center_cons :
    HasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) ::
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) := by
  have ht' : t < s.toSequenceOfBlowups.length := ht
  have hsm : Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    hinv.smooth_structMap
  have hci : IsClosedImmersion
      (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) :=
    isClosedImmersion_restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ hU t
  obtain ⟨e, he⟩ :
      ∃ e : _ ≅ (Scheme.Hom.ker
          (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subscheme,
        e.hom ≫ (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subschemeι =
          restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t :=
    ⟨(kerSubschemeIso (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).symm,
      kerSubschemeIso_inv_comp (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)⟩
  have hcomp : e.inv ≫ restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t =
      (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subschemeι := by
    calc e.inv ≫ restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t
        = e.inv ≫ (e.hom ≫
            (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subschemeι) := by
          rw [he]
      _ = (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subschemeι := by
          rw [Iso.inv_hom_id_assoc]
  have hsncE : InStrictNormalCrossingPosition (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) ::
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) := by
    have h1 := inStrictNormalCrossingPosition_moveToFront (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) j hinv.idx_lt hinv.snc_bdry
    rwa [moveToFront_eq_cons _ _ hinv.idx_lt, hinv.bdry_getElem] at h1
  have hsncErase : HasStrictNormalCrossingsWith
      (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι)
      (List.map (fun D => D.comap (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t))
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j)) := by
    rw [restrictedEmbedding_comp_structureMorphism_ambientBlowupSeq T j hj I₀ E₀ s hres hno hpr U₀ t]
    exact hasStrictNormalCrossingsWith_of_filterNeTop_eq _ _ _ _ hinv.comap_eraseIdx.symm
      (hasStrictNormalCrossingsWith_iteratedPreimage T j hj I₀ E₀ s U₀ hV t ht')
  have hq : e.inv ≫ (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      = (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subschemeι ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t := by
    rw [← Category.assoc, hcomp]
  have hlistEq : List.map (fun D => D.comap e.inv)
        (List.map (fun D => D.comap (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t))
          (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j))
      = List.map (fun D => D.comap
          (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subschemeι)
          (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) := by
    rw [List.map_map]
    refine List.map_congr_left ?_
    intro D _
    simp only [Function.comp_apply]
    rw [← Scheme.IdealSheafData.comap_comp, hcomp]
  have hsncCenter : HasStrictNormalCrossingsWith
      ((Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subschemeι ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      (((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι).comap e.inv)
      (List.map (fun D => D.comap
          (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subschemeι)
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j)) := by
    have h2 := hasStrictNormalCrossingsWith_comap_iso
      (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) e.symm
      ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι)
      (List.map (fun D => D.comap (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t))
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j)) hsncErase
    rw [← hq, ← hlistEq]
    exact h2
  have hmain := hlift T.base ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t)
      (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t))
      (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) hsncE
      (((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι).comap e.inv) hsncCenter
  have himg := imageIdealSheaf_iso_hom_comp_eq_consolidated451 e
      (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subschemeι
      ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι)
  rw [he] at himg
  rw [← himg, ← center_ambientBlowupSeq_eq_imageIdealSheaf T j hj I₀ E₀ s hres hno hpr U₀ hU hm
    hsupp t ht'] at hmain
  exact hmain

theorem hasStrictNormalCrossingsWith_center :
    HasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) := by
  refine hasStrictNormalCrossingsWith_of_moveToFront _ _ _ j hinv.idx_lt ?_
  rw [moveToFront_eq_cons _ j hinv.idx_lt, hinv.bdry_getElem]
  exact hasStrictNormalCrossingsWith_center_cons hinv hlift hm hV hU hsupp ht


end

section
variable {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}} {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}} [IsNoetherian T.scheme] [Smooth T.structMap] [LocallyOfFiniteType T.structMap] [CharZero T.base] {j : ℕ} {hj : j < T.boundary.length} {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData} {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups} {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent} {U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens} {t : ℕ} (hinv : GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ t) (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult) (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u}) (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))) (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆ (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) (ht : t < s.length) (l : ℕ) (hl : l ≤ T.mult)
include hinv hbal hm hV hlift hU hsupp ht hl

theorem exists_pow_mul_eq_comap_ambientDerivIdeal
    :
    ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t) ^ (T.mult - l) * B =
        (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) := by
  by_cases hlm : l < T.mult
  · have hnoe : IsNoetherian
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) :=
      isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr (t + 1) (by omega)
    have hsm : Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
      hinv.smooth_structMap
    have htle : t ≤ s.length := le_of_lt ht
    have hpow : ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ^ T.mult ≤
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t ^ (T.mult - l) :=
      pow_ambientDerivIdeal_le_pow_controlledTransform hres hno T j hj I₀ E₀ s hpr hbal l hlm t htle
        hinv.exists_pow_mul_eq_comap_controlledTransform (hinv.divDeriv l hl)
    have hcs := orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le T.base
      (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t) l T.mult hlm hpow
    have hsub := support_center_subset_orderAtLeastLocus hinv hbal hm hV hU hsupp ht
    have hle : ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ≤
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t ^ (T.mult - l) :=
      le_pow_of_hasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
        (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t)
        (hasStrictNormalCrossingsWith_center hinv hlift hm hV hU hsupp ht) (T.mult - l)
        (fun x hx => hcs (hsub hx))
    have hlen : t < (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length := by
      rw [ambientBlowupSeq_length hres hno T j hj I₀ E₀ s hpr]
      exact ht
    obtain ⟨B, hB, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t) (T.mult - l)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isBlowup t hlen) hle
    exact ⟨B, hB⟩
  · refine ⟨(ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t).comap
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t), ?_⟩
    have h0 : T.mult - l = 0 := Nat.sub_eq_zero_of_le (not_lt.mp hlm)
    rw [h0, pow_zero, one_mul]

theorem ambientDerivIdeal_le_center_pow :
    ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ≤
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t ^ (T.mult - l) := by
  have hsm : Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    hinv.smooth_structMap
  refine le_pow_of_hasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
    (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t)
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t)
    (hasStrictNormalCrossingsWith_center hinv hlift hm hV hU hsupp ht) (T.mult - l) ?_
  by_cases hlm : l < T.mult
  · have htle : t ≤ s.length := le_of_lt ht
    have hpow : ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ^ T.mult ≤
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t ^ (T.mult - l) :=
      pow_ambientDerivIdeal_le_pow_controlledTransform hres hno T j hj I₀ E₀ s hpr hbal l hlm t htle
        hinv.exists_pow_mul_eq_comap_controlledTransform (hinv.divDeriv l hl)
    have hcs := orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le T.base
      (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t) l T.mult hlm hpow
    have hsub := support_center_subset_orderAtLeastLocus hinv hbal hm hV hU hsupp ht
    exact fun x hx => hcs (hsub hx)
  · have h0 : T.mult - l = 0 := Nat.sub_eq_zero_of_le (not_lt.mp hlm)
    rw [h0, orderAtLeastLocus_zero]
    exact Set.subset_univ _


end

end GoingUpInvariantOnOpen

theorem goingUpInvariantOnOpen_zero (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap] [CharZero T.base]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
    (hE₀ : InStrictNormalCrossingPosition T.structMap E₀) (hjE : j < E₀.length)
    (hget : E₀[j]'hjE = Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ 0))
    (hcmp : filterNeTop (List.map
          (fun D => D.comap (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ 0))
          (E₀.eraseIdx j)) =
        filterNeTop (List.map (fun D => D.comap U₀.ι) (s.boundary 0))) :
    GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ 0 := by
  have hsmT : Smooth T.structMap := inferInstance
  have hftT : LocallyOfFiniteType T.structMap := inferInstance
  have hps : ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr 0 = T.structMap :=
    structureMorphism_ambientBlowupSeq_zero hres hno T j hj I₀ E₀ s hpr
  have hbd : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0 = E₀ :=
    ambientBlowupSeq_boundary_zero hres hno T j hj I₀ E₀ s hpr
  have hidx : j < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0).length := by
    rw [hbd]; exact hjE
  have hd0 : derivIdealSheafIterate T.base T.structMap 0 I₀ = I₀ := by
    have h1 := maxContactIdeal_eq_derivIdealSheafIterate T.base T.structMap I₀ 1
    have h2 := maxContactIdeal_one T.base T.structMap I₀
    rw [h1, Nat.sub_self] at h2
    exact h2
  have hctrl : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult 0 = I₀ := by
    have e1 := ambientDerivIdeal_order_zero_eq_controlledTransform hres hno T j hj I₀ E₀ s hpr 0
    have e2 := ambientDerivIdeal_at_zero_eq_derivIdealSheafIterate hres hno T j hj I₀ E₀ s hpr 0
    rw [e2, hd0] at e1
    exact e1.symm
  refine
    { divDeriv := ?_
      idx_lt := hidx
      deriv_le := ?_
      comap_eraseIdx := ?_
      snc_bdry := ?_
      bdry_getElem := ?_
      smooth_structMap := ?_ }
  · intro l _ i hi
    exact absurd hi (Nat.not_lt_zero i)
  · intro instFt n _
    have hcongr := @derivIdealSheafIterate_congr T.base _ _
      (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr 0) T.structMap instFt hftT hps n I₀
    have key : derivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr 0) n
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult 0) =
        ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr n 0 := by
      rw [hctrl]
      exact hcongr.trans (ambientDerivIdeal_at_zero_eq_derivIdealSheafIterate hres hno T j hj I₀ E₀ s hpr n).symm
    refine le_trans (le_of_eq key) (le_iSup_of_le n (le_iSup_of_le le_rfl (le_of_eq ?_)))
    simp only [Nat.sub_self, logDerivIdealSheafIterate_zero]
  · rw [hbd]
    exact hcmp
  · rw [hps, hbd]
    exact hE₀
  · revert hidx
    rw [hbd]
    intro h
    exact hget
  · rw [hps]
    exact hsmT

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariantInduction
section

open CategoryTheory AlgebraicGeometry

section

namespace DivisorReduction

namespace GoingUpInvariantOnOpen

private theorem getElem_of_eq_map_append_consolidated465 {α β : Type*} (f : α → β) (L : List α) (Lx : List β)
    (L' : List β) (hL : L' = L.map f ++ Lx) (i : ℕ) (hi : i < L.length) (hi' : i < L'.length) :
    L'[i]'hi' = f (L[i]'hi) := by
  subst hL
  have h1 : i < (L.map f).length := by simpa using hi
  rw [List.getElem_append_left h1, List.getElem_map]

theorem succ {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [IsNoetherian T.scheme] [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap] [CharZero T.base]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent}
    {U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens} {t : ℕ}
    (hinv : GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ t)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0))))
    (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))
    (ht : t < s.length) :
    GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ (t + 1) := by
  have hsmT : Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    hinv.smooth_structMap
  have hNt : IsNoetherian ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t) :=
    isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr t (by omega)
  have hNt1 : IsNoetherian ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) :=
    isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr (t + 1) (by omega)
  have hNs1 : IsNoetherian (s.toSequenceOfBlowups.schemeAt (t + 1)) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s (t + 1) (by omega)
  have hNs : IsNoetherian (s.toSequenceOfBlowups.schemeAt t) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s t (by omega)
  have hci : IsClosedImmersion
      (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) :=
    isClosedImmersion_restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ hU t
  have hci1 : IsClosedImmersion
      (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ (t + 1)) :=
    isClosedImmersion_restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ hU (t + 1)
  have htd : t < (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length := by
    rw [ambientBlowupSeq_length]; exact ht
  have hπ := (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isBlowup t htd
  have hHZ := ker_restrictedEmbedding_le_center hres hno T j hj I₀ E₀ s hpr U₀ hU hm hsupp t ht
  have hsncC := hinv.hasStrictNormalCrossingsWith_center_cons hlift hm hV hU hsupp ht
  have hsncZ := hinv.hasStrictNormalCrossingsWith_center hlift hm hV hU hsupp ht
  have hsmT1 : Smooth
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    smooth_comp_of_isBlowupAlongIdealSheaf hsncC hπ
  have hps : ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1) =
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t :=
    structureMorphism_ambientBlowupSeq_succ hres hno T j hj I₀ E₀ s hpr t
  have hker1 : Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ (t + 1)) =
      Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
        (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)) :=
    ker_restrictedEmbedding_succ T j hj I₀ E₀ s hres hno hpr U₀ hU t ht
  have hidx : j < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1)).length := by
    have h := hinv.idx_lt
    rw [BlowupSequenceData.boundary_length] at h ⊢
    omega
  refine ⟨?_, hidx, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl i hi
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
    · exact hinv.divDeriv l hl i h
    · subst h
      exact hinv.exists_pow_mul_eq_comap_ambientDerivIdeal hbal hm hV hlift hU hsupp ht l hl
  · intro instFt n hn
    have hest : ∀ m, m < T.mult →
        derivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) m
            (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr 0 t) ≤
          ⨆ l, ⨆ _ : l ≤ m, logDerivIdealSheafIterate T.base
            (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
            (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)) (m - l)
            (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t) := by
      intro m hmlt
      rw [ambientDerivIdeal_order_zero_eq_controlledTransform]
      exact hinv.deriv_le m hmlt
    have hK : ∀ l, l ≤ T.mult →
        ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ≤
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t ^ (T.mult - l) := fun l hl =>
      hinv.ambientDerivIdeal_le_center_pow hbal hm hV hlift hU hsupp ht l hl
    have hK' : ∀ l, l ≤ T.mult →
        Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t) ^ (T.mult - l) *
            ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1) =
          (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t).comap
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) := by
      intro l hl
      exact BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ _ _ _ _
        (hinv.exists_pow_mul_eq_comap_ambientDerivIdeal hbal hm hV hlift hU hsupp ht l hl)
    have hqc : QuasiCompact
        (strictTransformι ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
          (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t))) :=
      FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian _ _ _
    have key := derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_of_blowup
      T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t))
      (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) hsncC hHZ hπ T.mult
      (fun l => ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t) hK hest
      (fun l => ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1)) hK' n hn
    have e1 : derivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) n
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult (t + 1)) =
        derivIdealSheafIterate T.base
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) n
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult (t + 1)) :=
      derivIdealSheafIterate_congr _ _ hps _ _
    have e2 : ∀ l : ℕ,
        logDerivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1))
            (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ (t + 1))) (n - l)
            (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1)) =
          logDerivIdealSheafIterate T.base
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
              ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
            (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
              (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t))) (n - l)
            (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1)) := by
      intro l
      rw [hker1]
      exact logDerivIdealSheafIterate_congr _ _ hps _ _ _
    rw [e1]
    simp only [e2]
    have h0 : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult (t + 1) =
        ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr 0 (t + 1) :=
      (ambientDerivIdeal_order_zero_eq_controlledTransform hres hno T j hj I₀ E₀ s hpr (t + 1)).symm
    rw [h0]
    exact key
  · have hbs := BlowupSequenceData.boundary_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr) E₀ t
    have hlen : j < (List.map (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t))
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t)).length := by
      simpa using hinv.idx_lt
    have hZι : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).comap
        (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) =
        (s.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι := by
      rw [center_ambientBlowupSeq_eq_imageIdealSheaf T j hj I₀ E₀ s hres hno hpr U₀ hU hm hsupp t ht]
      exact Blowup.comap_map_of_isClosedImmersion _ _
    rw [hbs, List.eraseIdx_append_of_lt_length hlen _, List.eraseIdx_map,
      map_comap_strictTransform_append_exceptionalIdeal (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
        (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)
        (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ (t + 1))
        (restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t)
        (restrictedEmbedding_comp_blowupMorphism T j hj I₀ E₀ s hres hno hpr U₀ t) hker1
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) hsncC hHZ hπ,
      boundary_comap_iteratedPreimage_succ T j hj I₀ E₀ s U₀ hV t ht, hZι]
    refine filterNeTop_map_append_congr _ ?_ _ _ _ hinv.comap_eraseIdx
    exact FunctorialResolution.EmbeddedResolution.strictTransform_top _ _
  · rw [hps, BlowupSequenceData.boundary_succ]
    exact inStrictNormalCrossingPosition_strictTransform_append _ _ _ _ hπ hinv.snc_bdry hsncZ
  · rw [hker1, ← hinv.bdry_getElem]
    exact getElem_of_eq_map_append_consolidated465
      (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t))
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t)
      [Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)]
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1))
      (BlowupSequenceData.boundary_succ _ E₀ t) j hinv.idx_lt hidx
  · rw [hps]
    exact hsmT1

end GoingUpInvariantOnOpen

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerIdealAfterBlowup
section

open CategoryTheory AlgebraicGeometry

section

namespace DivisorReduction

section
variable {X : Scheme.{u}}

private theorem filterNeTop_append_top_consolidated473 (L : List X.IdealSheafData)
    (D : X.IdealSheafData) (hD : D = ⊤) : filterNeTop (L ++ [D]) = filterNeTop L := by
  subst hD
  unfold filterNeTop
  simp [List.filter_append]

private theorem comap_eq_self_of_eq_id_consolidated473 (I : X.IdealSheafData) (g : X ⟶ X)
    (hg : g = CategoryTheory.CategoryStruct.id X) : I.comap g = I := by
  subst hg
  exact Scheme.IdealSheafData.comap_id I

private theorem list_map_comap_id_consolidated473 (L : List X.IdealSheafData) :
    List.map (fun D => D.comap (CategoryTheory.CategoryStruct.id X)) L = L := by
  induction L with
  | nil => rfl
  | cons a l ih =>
      rw [List.map_cons, ih]
      exact congrArg (fun D => D :: l) (Scheme.IdealSheafData.comap_id a)


end

section
variable {A B C E : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ E)

private theorem comap_comp_comp_consolidated473 (D : E.IdealSheafData) :
    D.comap (CategoryTheory.CategoryStruct.comp f (CategoryTheory.CategoryStruct.comp g h))
      = ((D.comap h).comap g).comap f := by
  rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]

private theorem map_comap_comp_comp_consolidated473 (L : List E.IdealSheafData) :
    List.map (fun D => D.comap f)
        (List.map (fun D => D.comap g) (List.map (fun D => D.comap h) L))
      = List.map (fun D => ((D.comap h).comap g).comap f) L := by
  induction L with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, ih]


end

private theorem ker_opensι_preimage_iso_comp_consolidated473 {A B C : Scheme.{u}} (e : A ≅ B) (V : B.Opens)
    (g : B ⟶ C) :
    Scheme.Hom.ker (CategoryTheory.CategoryStruct.comp (Scheme.Opens.ι (e.hom ⁻¹ᵁ V))
        (CategoryTheory.CategoryStruct.comp e.hom g))
      = Scheme.Hom.ker (CategoryTheory.CategoryStruct.comp (Scheme.Opens.ι V) g) := by
  have : IsIso (e.hom ∣_ V) := inferInstance
  have h1 : CategoryTheory.CategoryStruct.comp (Scheme.Opens.ι (e.hom ⁻¹ᵁ V))
      (CategoryTheory.CategoryStruct.comp e.hom g)
      = CategoryTheory.CategoryStruct.comp (e.hom ∣_ V)
        (CategoryTheory.CategoryStruct.comp (Scheme.Opens.ι V) g) := by
    rw [← CategoryTheory.Category.assoc (e.hom ∣_ V) (Scheme.Opens.ι V) g, morphismRestrict_ι,
      CategoryTheory.Category.assoc]
  rw [h1]
  exact Scheme.Hom.ker_comp_of_isIso ..

private theorem ker_opensι_comp_subschemeι_congr_consolidated473 {X : Scheme.{u}} (Z J Z' J' : X.IdealSheafData)
    (hZ : Z' = Z) (hJ : J' = J) :
    Scheme.Hom.ker (CategoryTheory.CategoryStruct.comp
        (Scheme.Opens.ι ((TopologicalSpace.Opens.map J'.subschemeι.base).obj Z'.support.compl))
        J'.subschemeι)
      = Scheme.Hom.ker (CategoryTheory.CategoryStruct.comp
        (Scheme.Opens.ι ((TopologicalSpace.Opens.map J.subschemeι.base).obj Z.support.compl))
        J.subschemeι) := by
  subst hZ
  subst hJ
  rfl

private def boundaryDivisorEmbedding_consolidated473 (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    (restrictTwistedToDivisor T j hj).scheme ⟶ T.scheme :=
  (T.boundary.get ⟨j, hj⟩).subschemeι

section
variable (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)

private theorem lowerIdealAfterBlowup_eq_residualByPow_exceptionalIdeal_consolidated473 :
    lowerIdealAfterBlowup T j hj =
      residualByPow ((T.ideal.comap (CategoryTheory.CategoryStruct.id T.scheme)).comap
          (CategoryTheory.CategoryStruct.id T.scheme))
        (Blowup.exceptionalIdeal (CategoryTheory.CategoryStruct.id T.scheme) (containedComponentsIdeal T j hj)) T.mult :=
  rfl

private theorem lowerBoundaryAfterBlowup_eq_map_comap_id_append_consolidated473 :
    lowerBoundaryAfterBlowup T j hj =
      List.map (Blowup.strictTransform (CategoryTheory.CategoryStruct.id T.scheme) (containedComponentsIdeal T j hj))
          (List.map (fun D => D.comap (CategoryTheory.CategoryStruct.id T.scheme)) T.boundary) ++
        [Blowup.exceptionalIdeal (CategoryTheory.CategoryStruct.id T.scheme) (containedComponentsIdeal T j hj)] :=
  rfl

private theorem restrictTwistedToDivisor_boundary_consolidated473 :
    (restrictTwistedToDivisor T j hj).boundary =
      List.map (fun D => D.comap (boundaryDivisorEmbedding_consolidated473 T j hj))
        (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j)) :=
  rfl


end

section
variable {X : Scheme.{u}}

private theorem exceptionalIdeal_pow_mul_eq_comap_of_eq_id_consolidated473 (I Z J : X.IdealSheafData)
    (m : ℕ) (hJ : Z ^ m * J = I) (f g : X ⟶ X)
    (hf : f = CategoryTheory.CategoryStruct.id X)
    (hg : g = CategoryTheory.CategoryStruct.id X) :
    Blowup.exceptionalIdeal f Z ^ m * J = (I.comap g).comap f := by
  have h1 : Blowup.exceptionalIdeal f Z = Z := by
    rw [Blowup.exceptionalIdeal_eq_comap]
    exact comap_eq_self_of_eq_id_consolidated473 Z f hf
  have h2 : (I.comap g).comap f = I := by
    rw [comap_eq_self_of_eq_id_consolidated473 I g hg]
    exact comap_eq_self_of_eq_id_consolidated473 I f hf
  rw [h1, h2]
  exact hJ

private theorem support_subset_orderAtLeastLocus_comap_of_eq_id_consolidated473 (I Z : X.IdealSheafData)
    (m : ℕ) (h : ((Z.support : Set ↥X)) ⊆ orderAtLeastLocus I m) (g : X ⟶ X)
    (hg : g = CategoryTheory.CategoryStruct.id X) :
    ((Z.support : Set ↥X)) ⊆ orderAtLeastLocus (I.comap g) m := by
  rw [comap_eq_self_of_eq_id_consolidated473 I g hg]
  exact h


end

section
variable (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)

private theorem lowerIdealAfterBlowup_eq_residualByPow_consolidated473 :
    lowerIdealAfterBlowup T j hj = residualByPow T.ideal (containedComponentsIdeal T j hj) T.mult := by
  have h1 : (T.ideal.comap (CategoryTheory.CategoryStruct.id T.scheme)).comap
      (CategoryTheory.CategoryStruct.id T.scheme) = T.ideal := by
    rw [comap_eq_self_of_eq_id_consolidated473 T.ideal (CategoryTheory.CategoryStruct.id T.scheme) rfl]
    exact comap_eq_self_of_eq_id_consolidated473 T.ideal (CategoryTheory.CategoryStruct.id T.scheme) rfl
  have h2 : Blowup.exceptionalIdeal (CategoryTheory.CategoryStruct.id T.scheme) (containedComponentsIdeal T j hj)
      = containedComponentsIdeal T j hj := by
    rw [Blowup.exceptionalIdeal_eq_comap]
    exact comap_eq_self_of_eq_id_consolidated473 (containedComponentsIdeal T j hj) (CategoryTheory.CategoryStruct.id T.scheme) rfl
  rw [lowerIdealAfterBlowup_eq_residualByPow_exceptionalIdeal_consolidated473, h1, h2]

private theorem pow_mul_lowerIdealAfterBlowup_eq_ideal_consolidated473 (hfac : ∃ J, containedComponentsIdeal T j hj ^ T.mult * J = T.ideal) :
    containedComponentsIdeal T j hj ^ T.mult * lowerIdealAfterBlowup T j hj = T.ideal := by
  rw [lowerIdealAfterBlowup_eq_residualByPow_consolidated473]
  exact pow_mul_residualByPow T.ideal (containedComponentsIdeal T j hj) T.mult hfac


end

private theorem isDerivBalanced_lowerIdealAfterBlowup_consolidated473 (T : MarkedIdealWithBoundary.{u})
    [Smooth T.structMap] [LocallyOfFiniteType T.structMap]
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (hbal : IsDerivBalanced T.base T.structMap T.ideal T.mult)
    (j : ℕ) (hj : j < T.boundary.length)
    (hfac : ∃ J, containedComponentsIdeal T j hj ^ T.mult * J = T.ideal) :
    IsDerivBalanced T.base T.structMap (lowerIdealAfterBlowup T j hj) T.mult :=
  isDerivBalanced_of_pow_mul T.base T.structMap (containedComponentsIdeal T j hj) T.ideal (lowerIdealAfterBlowup T j hj) T.mult
    (pow_mul_lowerIdealAfterBlowup_eq_ideal_consolidated473 T j hj hfac).symm hord hbal

private theorem structureMorphism_ambientBlowupSeq_eq_projectionToBase_comp_consolidated473 (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t =
      CategoryTheory.CategoryStruct.comp ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t)
        T.structMap :=
  rfl

private def complContainedComponentsOnDivisor_consolidated473 (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    ((restrictTwistedToDivisor T j hj).scheme).Opens :=
  (TopologicalSpace.Opens.map (boundaryDivisorEmbedding_consolidated473 T j hj).base).obj (containedComponentsIdeal T j hj).support.compl

private def complContainedComponentsAtSchemeZero_consolidated473 (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups) : (s.toSequenceOfBlowups.schemeAt 0).Opens :=
  s.isoZero.hom ⁻¹ᵁ complContainedComponentsOnDivisor_consolidated473 T j hj

section
variable (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)

private theorem mem_complOpens_iff_consolidated473 (x : ↥(s.toSequenceOfBlowups.schemeAt 0)) :
    x ∈ (complContainedComponentsAtSchemeZero_consolidated473 T j hj s : Set ↥(s.toSequenceOfBlowups.schemeAt 0)) ↔
      (boundaryDivisorEmbedding_consolidated473 T j hj (s.isoZero.hom x)) ∉ ((containedComponentsIdeal T j hj).support : Set ↥T.scheme) :=
  Iff.rfl

private theorem isClosed_complOpens_of_isOpen_consolidated473 (hopen : IsOpen (⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹'
      ((containedComponentsIdeal T j hj).support : Set ↥T.scheme))) :
    IsClosed ((complContainedComponentsAtSchemeZero_consolidated473 T j hj s : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) := by
  have h1 : ((complContainedComponentsAtSchemeZero_consolidated473 T j hj s : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))
      = (⇑s.isoZero.hom ⁻¹' (⇑(boundaryDivisorEmbedding_consolidated473 T j hj) ⁻¹'
          ((containedComponentsIdeal T j hj).support : Set ↥T.scheme)))ᶜ := rfl
  rw [h1]
  exact (hopen.preimage (Scheme.Hom.continuous s.isoZero.hom)).isClosed_compl

private theorem support_ideal_zero_subset_complOpens_consolidated473 (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (hfac : ∃ J, containedComponentsIdeal T j hj ^ T.mult * J = T.ideal) :
    (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆
      ((complContainedComponentsAtSchemeZero_consolidated473 T j hj s : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) := by
  intro x hx
  have hfacEq : T.ideal = containedComponentsIdeal T j hj ^ T.mult * lowerIdealAfterBlowup T j hj :=
    (pow_mul_lowerIdealAfterBlowup_eq_ideal_consolidated473 T j hj hfac).symm
  have h1 : s.ideal 0 = ((restrictTwistedToDivisor T j hj).ideal).comap s.isoZero.hom := s.ideal_zero
  rw [h1] at hx
  have h2 : s.isoZero.hom x ∈ (((restrictTwistedToDivisor T j hj).ideal).support : Set _) :=
    (Scheme.IdealSheafData.mem_support_comap ..).1 hx
  have h3 : boundaryDivisorEmbedding_consolidated473 T j hj (s.isoZero.hom x) ∈ ((lowerIdealAfterBlowup T j hj).support : Set _) :=
    (Scheme.IdealSheafData.mem_support_comap ..).1 h2
  have hfin : (boundaryDivisorEmbedding_consolidated473 T j hj (s.isoZero.hom x))
      ∉ ((containedComponentsIdeal T j hj).support : Set ↥T.scheme) := by
    intro hmem
    exact not_mem_support_of_mem_support_of_pow_mul (containedComponentsIdeal T j hj) T.ideal
      (lowerIdealAfterBlowup T j hj) T.mult hfacEq hord hmem h3
  exact (mem_complOpens_iff_consolidated473 T j hj s x).mpr hfin


end

private theorem inStrictNormalCrossingPosition_lowerBoundaryAfterBlowup_consolidated473 (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme]
    (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme) (containedComponentsIdeal T j hj))
    (hsncT : InStrictNormalCrossingPosition T.structMap T.boundary)
    (hsnc : HasStrictNormalCrossingsWith T.structMap (containedComponentsIdeal T j hj) T.boundary) :
    InStrictNormalCrossingPosition T.structMap (lowerBoundaryAfterBlowup T j hj) := by
  have hE : InStrictNormalCrossingPosition T.structMap
      (List.map (fun D => D.comap (CategoryTheory.CategoryStruct.id T.scheme)) T.boundary) := by
    rw [list_map_comap_id_consolidated473]
    exact hsncT
  have hZE : HasStrictNormalCrossingsWith T.structMap (containedComponentsIdeal T j hj)
      (List.map (fun D => D.comap (CategoryTheory.CategoryStruct.id T.scheme)) T.boundary) := by
    rw [list_map_comap_id_consolidated473]
    exact hsnc
  have h := inStrictNormalCrossingPosition_strictTransform_append T.structMap
    (CategoryTheory.CategoryStruct.id T.scheme) (containedComponentsIdeal T j hj)
    (List.map (fun D => D.comap (CategoryTheory.CategoryStruct.id T.scheme)) T.boundary) hb hE hZE
  rw [CategoryTheory.Category.id_comp] at h
  rw [lowerBoundaryAfterBlowup_eq_map_comap_id_append_consolidated473]
  exact h

section
variable (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)

private theorem lt_length_lowerBoundaryAfterBlowup_consolidated473 :
    j < (lowerBoundaryAfterBlowup T j hj).length := by
  rw [lowerBoundaryAfterBlowup_eq_map_comap_id_append_consolidated473, List.length_append, List.length_map, List.length_map,
    List.length_singleton]
  omega

private theorem lowerBoundaryAfterBlowup_eq_map_strictTransform_append_consolidated473 :
    lowerBoundaryAfterBlowup T j hj =
      List.map (Blowup.strictTransform (CategoryTheory.CategoryStruct.id T.scheme) (containedComponentsIdeal T j hj))
          T.boundary ++
        [Blowup.exceptionalIdeal (CategoryTheory.CategoryStruct.id T.scheme) (containedComponentsIdeal T j hj)] := by
  rw [lowerBoundaryAfterBlowup_eq_map_comap_id_append_consolidated473, list_map_comap_id_consolidated473]

private theorem lt_length_map_strictTransform_boundary_consolidated473 :
    j < (List.map (Blowup.strictTransform (CategoryTheory.CategoryStruct.id T.scheme)
      (containedComponentsIdeal T j hj)) T.boundary).length := by
  rw [List.length_map]
  exact hj


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length) (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups) (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)

private theorem restrictedEmbedding_zero_eq_consolidated473 :
    restrictedEmbedding T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hres hno hpr
        (complContainedComponentsAtSchemeZero_consolidated473 T j hj s) 0 =
      CategoryTheory.CategoryStruct.comp (Scheme.Opens.ι (complContainedComponentsAtSchemeZero_consolidated473 T j hj s))
        (CategoryTheory.CategoryStruct.comp s.isoZero.hom (boundaryDivisorEmbedding_consolidated473 T j hj)) := by
  have e0 := embeddingIntoAmbient_zero hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr
  rw [restrictedEmbedding_eq_ι_comp_embeddingIntoAmbient]
  exact congrArg (fun g => CategoryTheory.CategoryStruct.comp
    (Scheme.Opens.ι (complContainedComponentsAtSchemeZero_consolidated473 T j hj s)) g) e0

private theorem comap_restrictedEmbedding_zero_consolidated473 (D : T.scheme.IdealSheafData) :
    D.comap (restrictedEmbedding T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hres hno hpr
        (complContainedComponentsAtSchemeZero_consolidated473 T j hj s) 0) =
      ((D.comap (boundaryDivisorEmbedding_consolidated473 T j hj)).comap s.isoZero.hom).comap
        (Scheme.Opens.ι (complContainedComponentsAtSchemeZero_consolidated473 T j hj s)) := by
  refine Eq.trans (congrArg (fun f => D.comap f)
    (restrictedEmbedding_zero_eq_consolidated473 hres hno T j hj s hpr)) ?_
  exact comap_comp_comp_consolidated473 (Scheme.Opens.ι (complContainedComponentsAtSchemeZero_consolidated473 T j hj s)) s.isoZero.hom (boundaryDivisorEmbedding_consolidated473 T j hj) D

private theorem lowerBoundaryAfterBlowup_getElem_eq_ker_restrictedEmbedding_consolidated473 :
    (lowerBoundaryAfterBlowup T j hj)[j]'(lt_length_lowerBoundaryAfterBlowup_consolidated473 T j hj) =
      Scheme.Hom.ker (restrictedEmbedding T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hres hno
        hpr (complContainedComponentsAtSchemeZero_consolidated473 T j hj s) 0) := by
  have hL : (lowerBoundaryAfterBlowup T j hj)[j]'(lt_length_lowerBoundaryAfterBlowup_consolidated473 T j hj)
      = Blowup.strictTransform (CategoryTheory.CategoryStruct.id T.scheme) (containedComponentsIdeal T j hj)
          (T.boundary.get ⟨j, hj⟩) := by
    simp only [lowerBoundaryAfterBlowup_eq_map_strictTransform_append_consolidated473 T j hj, List.get_eq_getElem]
    rw [List.getElem_append_left (lt_length_map_strictTransform_boundary_consolidated473 T j hj), List.getElem_map]
  have hA : Blowup.strictTransform (CategoryTheory.CategoryStruct.id T.scheme) (containedComponentsIdeal T j hj)
        (T.boundary.get ⟨j, hj⟩)
      = Scheme.Hom.ker (CategoryTheory.CategoryStruct.comp
          (Scheme.Opens.ι (complContainedComponentsOnDivisor_consolidated473 T j hj)) (boundaryDivisorEmbedding_consolidated473 T j hj)) := by
    rw [Blowup.strictTransform_eq_ker, Blowup.strictTransformImmersion_eq, Blowup.strictTransformOpens_eq]
    exact ker_opensι_comp_subschemeι_congr_consolidated473 (containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩)
      ((containedComponentsIdeal T j hj).comap (CategoryTheory.CategoryStruct.id T.scheme))
      ((T.boundary.get ⟨j, hj⟩).comap (CategoryTheory.CategoryStruct.id T.scheme))
      (Scheme.IdealSheafData.comap_id _) (Scheme.IdealSheafData.comap_id _)
  have hker : Scheme.Hom.ker (restrictedEmbedding T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s
        hres hno hpr (complContainedComponentsAtSchemeZero_consolidated473 T j hj s) 0)
      = Scheme.Hom.ker (CategoryTheory.CategoryStruct.comp
          (Scheme.Opens.ι (complContainedComponentsOnDivisor_consolidated473 T j hj)) (boundaryDivisorEmbedding_consolidated473 T j hj)) := by
    refine Eq.trans (congrArg (fun f => Scheme.Hom.ker f)
      (restrictedEmbedding_zero_eq_consolidated473 hres hno T j hj s hpr)) ?_
    exact ker_opensι_preimage_iso_comp_consolidated473 s.isoZero (complContainedComponentsOnDivisor_consolidated473 T j hj) (boundaryDivisorEmbedding_consolidated473 T j hj)
  rw [hL, hA]
  exact hker.symm

private theorem filterNeTop_comap_restrictedEmbedding_eraseIdx_consolidated473 :
    filterNeTop (List.map (fun D => D.comap (restrictedEmbedding T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hres hno hpr (complContainedComponentsAtSchemeZero_consolidated473 T j hj s) 0))
        ((lowerBoundaryAfterBlowup T j hj).eraseIdx j)) =
      filterNeTop (List.map (fun D => D.comap (Scheme.Opens.ι (complContainedComponentsAtSchemeZero_consolidated473 T j hj s)))
        (s.boundary 0)) := by
  have hsplit : (lowerBoundaryAfterBlowup T j hj).eraseIdx j
      = (List.map (Blowup.strictTransform (CategoryTheory.CategoryStruct.id T.scheme)
            (containedComponentsIdeal T j hj)) T.boundary).eraseIdx j ++
        [Blowup.exceptionalIdeal (CategoryTheory.CategoryStruct.id T.scheme) (containedComponentsIdeal T j hj)] := by
    rw [lowerBoundaryAfterBlowup_eq_map_strictTransform_append_consolidated473 T j hj,
      List.eraseIdx_append_of_lt_length (lt_length_map_strictTransform_boundary_consolidated473 T j hj)]
  have hlen : ((List.map (Blowup.strictTransform (CategoryTheory.CategoryStruct.id T.scheme)
      (containedComponentsIdeal T j hj)) T.boundary).eraseIdx j).length = T.boundary.length - 1 := by
    rw [List.length_eraseIdx_of_lt (lt_length_map_strictTransform_boundary_consolidated473 T j hj), List.length_map]
  have htake : List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j)
      = (List.map (Blowup.strictTransform (CategoryTheory.CategoryStruct.id T.scheme)
          (containedComponentsIdeal T j hj)) T.boundary).eraseIdx j := by
    rw [hsplit]
    exact List.take_left' hlen
  have hb : (restrictTwistedToDivisor T j hj).boundary =
      List.map (fun D => D.comap (boundaryDivisorEmbedding_consolidated473 T j hj))
        ((List.map (Blowup.strictTransform (CategoryTheory.CategoryStruct.id T.scheme)
          (containedComponentsIdeal T j hj)) T.boundary).eraseIdx j) := by
    rw [restrictTwistedToDivisor_boundary_consolidated473, htake]
  have hB0 : s.boundary 0 = List.map (fun D => D.comap s.isoZero.hom)
      (List.map (fun D => D.comap (boundaryDivisorEmbedding_consolidated473 T j hj))
        ((List.map (Blowup.strictTransform (CategoryTheory.CategoryStruct.id T.scheme)
          (containedComponentsIdeal T j hj)) T.boundary).eraseIdx j)) := by
    have h0 : s.boundary 0
        = List.map (fun D => D.comap s.isoZero.hom) (restrictTwistedToDivisor T j hj).boundary := s.boundary_zero
    rw [h0]
    exact congrArg (fun L => List.map (fun D => D.comap s.isoZero.hom) L) hb
  have hB0' : List.map (fun D => D.comap (Scheme.Opens.ι (complContainedComponentsAtSchemeZero_consolidated473 T j hj s)))
        (s.boundary 0)
      = List.map (fun D : T.scheme.IdealSheafData =>
          ((D.comap (boundaryDivisorEmbedding_consolidated473 T j hj)).comap s.isoZero.hom).comap
            (Scheme.Opens.ι (complContainedComponentsAtSchemeZero_consolidated473 T j hj s)))
          ((List.map (Blowup.strictTransform (CategoryTheory.CategoryStruct.id T.scheme)
            (containedComponentsIdeal T j hj)) T.boundary).eraseIdx j) := by
    rw [hB0]
    exact map_comap_comp_comp_consolidated473 (Scheme.Opens.ι (complContainedComponentsAtSchemeZero_consolidated473 T j hj s)) s.isoZero.hom
      (boundaryDivisorEmbedding_consolidated473 T j hj) _
  have htop' : (((Blowup.exceptionalIdeal (CategoryTheory.CategoryStruct.id T.scheme)
        (containedComponentsIdeal T j hj)).comap (boundaryDivisorEmbedding_consolidated473 T j hj)).comap s.isoZero.hom).comap
        (Scheme.Opens.ι (complContainedComponentsAtSchemeZero_consolidated473 T j hj s)) = ⊤ := by
    rw [Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id]
    exact (FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_top_iff_forall_notMem_support
      (((containedComponentsIdeal T j hj).comap (boundaryDivisorEmbedding_consolidated473 T j hj)).comap s.isoZero.hom)
      (complContainedComponentsAtSchemeZero_consolidated473 T j hj s)).mpr
      (fun x hx hmem => ((mem_complOpens_iff_consolidated473 T j hj s x).mp hx)
        ((Scheme.IdealSheafData.mem_support_comap ..).1
          ((Scheme.IdealSheafData.mem_support_comap ..).1 hmem)))
  have hfun : (fun D : T.scheme.IdealSheafData =>
        D.comap (restrictedEmbedding T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hres hno hpr
          (complContainedComponentsAtSchemeZero_consolidated473 T j hj s) 0))
      = (fun D : T.scheme.IdealSheafData =>
        ((D.comap (boundaryDivisorEmbedding_consolidated473 T j hj)).comap s.isoZero.hom).comap
          (Scheme.Opens.ι (complContainedComponentsAtSchemeZero_consolidated473 T j hj s))) :=
    funext (fun D => comap_restrictedEmbedding_zero_consolidated473 hres hno T j hj s hpr D)
  have key : filterNeTop (List.map (fun D : T.scheme.IdealSheafData =>
        ((D.comap (boundaryDivisorEmbedding_consolidated473 T j hj)).comap s.isoZero.hom).comap
          (Scheme.Opens.ι (complContainedComponentsAtSchemeZero_consolidated473 T j hj s)))
        ((lowerBoundaryAfterBlowup T j hj).eraseIdx j))
      = filterNeTop (List.map (fun D => D.comap (Scheme.Opens.ι (complContainedComponentsAtSchemeZero_consolidated473 T j hj s)))
          (s.boundary 0)) := by
    have h1 : List.map (fun D : T.scheme.IdealSheafData =>
          ((D.comap (boundaryDivisorEmbedding_consolidated473 T j hj)).comap s.isoZero.hom).comap
            (Scheme.Opens.ι (complContainedComponentsAtSchemeZero_consolidated473 T j hj s)))
          ((lowerBoundaryAfterBlowup T j hj).eraseIdx j)
        = List.map (fun D : T.scheme.IdealSheafData =>
            ((D.comap (boundaryDivisorEmbedding_consolidated473 T j hj)).comap s.isoZero.hom).comap
              (Scheme.Opens.ι (complContainedComponentsAtSchemeZero_consolidated473 T j hj s)))
            ((List.map (Blowup.strictTransform (CategoryTheory.CategoryStruct.id T.scheme)
              (containedComponentsIdeal T j hj)) T.boundary).eraseIdx j)
          ++ [(((Blowup.exceptionalIdeal (CategoryTheory.CategoryStruct.id T.scheme)
              (containedComponentsIdeal T j hj)).comap (boundaryDivisorEmbedding_consolidated473 T j hj)).comap s.isoZero.hom).comap
              (Scheme.Opens.ι (complContainedComponentsAtSchemeZero_consolidated473 T j hj s))] := by
      simp only [hsplit, List.map_append, List.map_cons, List.map_nil]
    rw [h1, filterNeTop_append_top_consolidated473 _ _ htop']
    exact congrArg filterNeTop hB0'.symm
  refine Eq.trans (congrArg (fun f => filterNeTop
    (List.map f ((lowerBoundaryAfterBlowup T j hj).eraseIdx j))) hfun) ?_
  exact key


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})

theorem goingUpInvariantOnOpen_of_le (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap] [CharZero T.base]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0))))
    (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))
    (hE₀ : InStrictNormalCrossingPosition T.structMap E₀) (hjE : j < E₀.length)
    (hget : E₀[j] = Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ 0))
    (hcmp : filterNeTop
        (List.map (fun D => D.comap (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ 0))
          (E₀.eraseIdx j)) =
      filterNeTop (List.map (fun D => D.comap U₀.ι) (s.boundary 0)))
    (t : ℕ) (ht : t ≤ s.length) :
    GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ t := by
  induction t with
  | zero => exact goingUpInvariantOnOpen_zero hres hno T j hj I₀ E₀ s hpr U₀ hE₀ hjE hget hcmp
  | succ n ih =>
      exact GoingUpInvariantOnOpen.succ (ih (Nat.le_of_succ_le ht)) hbal hm hV hlift hU hsupp
        (Nat.lt_of_succ_le ht)

theorem exists_isClosed_opens_goingUpInvariantOnOpen (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (hbal : ∀ [_inst : LocallyOfFiniteType T.structMap],
      IsDerivBalanced T.base T.structMap T.ideal T.mult)
    (j : ℕ) (hj : j < T.boundary.length)
    (_hZ : containedComponentsIdeal T j hj ≠ ⊤)
    (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme) (containedComponentsIdeal T j hj))
    (hVlow : (restrictTwistedToDivisor T j hj).IsAdmissible)
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (_hsm : Smooth
      (CategoryTheory.CategoryStruct.comp (containedComponentsIdeal T j hj).subschemeι T.structMap))
    (hsnc : HasStrictNormalCrossingsWith T.structMap (containedComponentsIdeal T j hj) T.boundary)
    (_hsup : ((containedComponentsIdeal T j hj).support : Set ↥T.scheme) ⊆ orderAtLeastLocus T.ideal T.mult)
    (hfac : ∃ J, containedComponentsIdeal T j hj ^ T.mult * J = T.ideal)
    (hopen : IsOpen (⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹'
      ((containedComponentsIdeal T j hj).support : Set ↥T.scheme))) :
    ∃ U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens,
      IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ∧
      (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0)) ⊆
        (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ∧
      (∀ [_inst : LocallyOfFiniteType T.structMap],
        IsDerivBalanced T.base T.structMap (lowerIdealAfterBlowup T j hj) T.mult) ∧
      (∀ [_hsmooth : Smooth T.structMap]
         [_instFt : LocallyOfFiniteType T.structMap]
         [_instCh : CharZero T.base],
        ∀ t ≤ s.length,
          GoingUpInvariantOnOpen hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr U₀ t) := by
  obtain ⟨_, _, _, hm, _, hsmT, hsncT⟩ := id hV
  refine ⟨complContainedComponentsAtSchemeZero_consolidated473 T j hj s, isClosed_complOpens_of_isOpen_consolidated473 T j hj s hopen,
    support_ideal_zero_subset_complOpens_consolidated473 T j hj s hord hfac, ?_, ?_⟩
  · intro instFt
    have : Smooth T.structMap := hsmT
    exact isDerivBalanced_lowerIdealAfterBlowup_consolidated473 T hord hbal j hj hfac
  · intro hsmooth instFt instCh t ht
    have : Smooth T.structMap := hsmooth
    have : LocallyOfFiniteType T.structMap := instFt
    have : CharZero T.base := instCh
    exact goingUpInvariantOnOpen_of_le hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr
      (complContainedComponentsAtSchemeZero_consolidated473 T j hj s) (isDerivBalanced_lowerIdealAfterBlowup_consolidated473 T hord hbal j hj hfac) hm hVlow hlift
      (isClosed_complOpens_of_isOpen_consolidated473 T j hj s hopen) (support_ideal_zero_subset_complOpens_consolidated473 T j hj s hord hfac)
      (inStrictNormalCrossingPosition_lowerBoundaryAfterBlowup_consolidated473 T j hj hb hsncT hsnc) (lt_length_lowerBoundaryAfterBlowup_consolidated473 T j hj)
      (lowerBoundaryAfterBlowup_getElem_eq_ker_restrictedEmbedding_consolidated473 hres hno T j hj s hpr)
      (filterNeTop_comap_restrictedEmbedding_eraseIdx_consolidated473 hres hno T j hj s hpr) t ht


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length) (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme) (containedComponentsIdeal T j hj)) (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups) (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)

theorem controlledTransform_prepend_ambientBlowupSeq_one :
    (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform
        T.ideal T.mult 1 =
      (lowerIdealAfterBlowup T j hj).comap
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
          s hpr).isoZero.hom := by
  rw [BlowupSequenceData.controlledTransform_succ, BlowupSequenceData.controlledTransform_zero, BlowupSequenceData.prepend_isoObjZero,
    BlowupSequenceData.prepend_blowupMorphism_zero, BlowupSequenceData.prepend_center_zero]
  exact (Scheme.IdealSheafData.comap_id (lowerIdealAfterBlowup T j hj)).symm

theorem boundary_prepend_ambientBlowupSeq_one :
    (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).boundaryFrom
        T.boundary 1 =
      List.map
        (fun D => D.comap
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).isoZero.hom)
        (lowerBoundaryAfterBlowup T j hj) := by
  rw [BlowupSequenceData.boundary_succ, BlowupSequenceData.boundary_zero, BlowupSequenceData.prepend_isoObjZero,
    BlowupSequenceData.prepend_blowupMorphism_zero, BlowupSequenceData.prepend_center_zero]
  exact (list_map_comap_id_consolidated473 (lowerBoundaryAfterBlowup T j hj)).symm


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (hlift : StrictNormalCrossingsLiftFromDivisor.{u}) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (hV : T.IsAdmissible) (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) (hbal : ∀ [_inst : LocallyOfFiniteType T.structMap], IsDerivBalanced T.base T.structMap T.ideal T.mult) (j : ℕ) (hj : j < T.boundary.length) (hZ : containedComponentsIdeal T j hj ≠ ⊤) (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme) (containedComponentsIdeal T j hj)) (hVlow : (restrictTwistedToDivisor T j hj).IsAdmissible) (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups) (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (hsm : Smooth (CategoryTheory.CategoryStruct.comp (containedComponentsIdeal T j hj).subschemeι T.structMap)) (hsnc : HasStrictNormalCrossingsWith T.structMap (containedComponentsIdeal T j hj) T.boundary) (hsup : ((containedComponentsIdeal T j hj).support : Set ↥T.scheme) ⊆ orderAtLeastLocus T.ideal T.mult) (hfac : ∃ J, containedComponentsIdeal T j hj ^ T.mult * J = T.ideal) (hopen : IsOpen (⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' ((containedComponentsIdeal T j hj).support : Set ↥T.scheme)))
include hlift hV hord hbal hZ hVlow hsm hsnc hsup hfac hopen

theorem isMarked_prepend_ambientBlowupSeq :
    (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked T.structMap T.ideal T.mult T.boundary := by
  obtain ⟨U₀, hUcl, hUsupp, hbalLow, hinv⟩ :=
    exists_isClosed_opens_goingUpInvariantOnOpen hres hno hlift T hV hord hbal j hj hZ hb hVlow s hpr hsm hsnc
      hsup hfac hopen
  obtain ⟨hch, hft, _, hm, _, hsmT, _⟩ := id hV
  have : CharZero T.base := hch
  have : LocallyOfFiniteType T.structMap := hft
  have : Smooth T.structMap := hsmT
  obtain ⟨Jfac, hJfac⟩ := hfac
  have hctrl1 := controlledTransform_prepend_ambientBlowupSeq_one hres hno T j hj hb s hpr
  have hbdry1 := boundary_prepend_ambientBlowupSeq_one hres hno T j hj hb s hpr
  have h0 : CategoryTheory.CategoryStruct.comp
      ((BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).projectionToBase 0)
      T.structMap = T.structMap := by
    rw [BlowupSequenceData.projectionToBase_prepend_zero]
    exact CategoryTheory.Category.id_comp T.structMap
  have hlen : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).length
      = s.length + 1 := by
    rw [BlowupSequenceData.prepend_length, ambientBlowupSeq_length]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hlen] at hi
    cases i with
    | zero =>
        refine ⟨Jfac, ?_⟩
        rw [BlowupSequenceData.prepend_blowupMorphism_zero, BlowupSequenceData.prepend_center_zero,
          BlowupSequenceData.controlledTransform_zero, BlowupSequenceData.prepend_isoObjZero]
        exact exceptionalIdeal_pow_mul_eq_comap_of_eq_id_consolidated473 T.ideal (containedComponentsIdeal T j hj) Jfac T.mult hJfac _ _
          rfl rfl
    | succ n =>
        have hn : n < s.length := Nat.lt_of_succ_lt_succ hi
        rw [BlowupSequenceData.prepend_blowupMorphism_succ, BlowupSequenceData.prepend_center_succ,
          BlowupSequenceData.controlledTransform_prepend_succ (containedComponentsIdeal T j hj) hb
            (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)
            T.ideal (lowerIdealAfterBlowup T j hj) T.mult hctrl1 n]
        exact (hinv (n + 1) hn).exists_pow_mul_eq_comap_controlledTransform n (Nat.lt_succ_self n)
  · intro i hi
    rw [hlen] at hi
    cases i with
    | zero =>
        rw [BlowupSequenceData.prepend_center_zero, BlowupSequenceData.controlledTransform_zero,
          BlowupSequenceData.prepend_isoObjZero]
        exact support_subset_orderAtLeastLocus_comap_of_eq_id_consolidated473 T.ideal (containedComponentsIdeal T j hj) T.mult hsup _ rfl
    | succ n =>
        have hn : n < s.length := Nat.lt_of_succ_lt_succ hi
        rw [BlowupSequenceData.prepend_center_succ,
          BlowupSequenceData.controlledTransform_prepend_succ (containedComponentsIdeal T j hj) hb
            (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)
            T.ideal (lowerIdealAfterBlowup T j hj) T.mult hctrl1 n]
        exact (hinv n (Nat.le_of_lt hn)).support_center_subset_orderAtLeastLocus hbalLow hm hVlow hUcl
          hUsupp hn
  · intro i hi
    rw [hlen] at hi
    cases i with
    | zero =>
        rw [h0]
        exact hsm
    | succ n =>
        have hn : n < s.length := Nat.lt_of_succ_lt_succ hi
        rw [BlowupSequenceData.prepend_center_succ, BlowupSequenceData.projectionToBase_prepend_succ]
        exact smooth_ambientBlowupSeq_center_comp hres hno T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hpr n hn
  · intro i hi
    rw [hlen] at hi
    cases i with
    | zero =>
        have hb0 : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
            (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).boundaryFrom
            T.boundary 0 = T.boundary := by
          rw [BlowupSequenceData.boundary_zero, BlowupSequenceData.prepend_isoObjZero]
          exact list_map_comap_id_consolidated473 T.boundary
        rw [h0, hb0]
        exact hsnc
    | succ n =>
        have hn : n < s.length := Nat.lt_of_succ_lt_succ hi
        have h4 := (hinv n (Nat.le_of_lt hn)).hasStrictNormalCrossingsWith_center hlift hm hVlow hUcl hUsupp hn
        rw [structureMorphism_ambientBlowupSeq_eq_projectionToBase_comp_consolidated473] at h4
        rw [BlowupSequenceData.prepend_center_succ, BlowupSequenceData.projectionToBase_prepend_succ,
          BlowupSequenceData.boundary_prepend_succ (containedComponentsIdeal T j hj) hb
            (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)
            T.boundary (lowerBoundaryAfterBlowup T j hj) hbdry1 n]
        exact h4

theorem comap_controlledTransform_prepend_ambientBlowupSeq (t : ℕ) (ht : t ≤ s.length) :
    ((BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
            (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
              (lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform T.ideal T.mult (t + 1)).comap
        (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t) =
      s.ideal t := by
  obtain ⟨_, _, _, _, hinv⟩ :=
    exists_isClosed_opens_goingUpInvariantOnOpen hres hno hlift T hV hord hbal j hj hZ hb hVlow s hpr hsm hsnc
      hsup hfac hopen
  obtain ⟨hch, hft, _, _, _, hsmT, _⟩ := id hV
  have : CharZero T.base := hch
  have : LocallyOfFiniteType T.structMap := hft
  have : Smooth T.structMap := hsmT
  rw [BlowupSequenceData.controlledTransform_prepend_succ (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)
      T.ideal (lowerIdealAfterBlowup T j hj) T.mult
      (controlledTransform_prepend_ambientBlowupSeq_one hres hno T j hj hb s hpr) t]
  exact (hinv t ht).comap_controlledTransform ht


end

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.FieldBaseChangeAdmissible
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section

namespace MarkedIdealWithBoundary

theorem isAdmissible_baseChange (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (L : Type u) [Field L]
    [CharZero L] (f : T.base →+* L) : (T.baseChange L f).IsAdmissible := by
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have := hV.quasiCompact
  have hflat : Flat (specMapOfFieldHom T.base L f) :=
    instFlatSpecMapOfFieldHom T.base L f
  have hfst : Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    inferInstance
  refine
    { charZero := ‹CharZero L›
      locallyOfFiniteType := ?_
      nonzeroOnComponents := ?_
      one_le_mult := hV.one_le_mult
      quasiCompact := ?_
      smooth := ?_
      snc := ?_ }
  · exact
      (inferInstance : LocallyOfFiniteType
        (pullback.snd T.structMap (specMapOfFieldHom T.base L f)))
  · exact hV.nonzeroOnComponents.comap_of_flat
      (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
  · exact
      (inferInstance : QuasiCompact
        (pullback.snd T.structMap (specMapOfFieldHom T.base L f)))
  · exact smooth_pullbackSnd_specMap T.structMap (CommRingCat.ofHom f)
  · exact inStrictNormalCrossingPosition_comap_pullback_specMap T.structMap (CommRingCat.ofHom f) T.boundary hV.snc

end MarkedIdealWithBoundary

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothPullbackAdmissible
section

open CategoryTheory AlgebraicGeometry

section

namespace MarkedIdealWithBoundary

theorem isAdmissible_pullbackAlong_of_smooth (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [Smooth h] [QuasiCompact q]
    (hq : h ≫ T.structMap = q) :
    (T.pullbackAlong Y q h).IsAdmissible := by
  have := hV.charZero
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have hqc : QuasiCompact q := inferInstance
  subst hq
  have : Smooth (h ≫ T.structMap) := inferInstance
  have : Flat h := inferInstance
  refine ⟨hV.charZero, ?_, ?_, hV.one_le_mult, hqc, ?_, ?_⟩
  · show LocallyOfFiniteType (h ≫ T.structMap)
    infer_instance
  · exact hV.nonzeroOnComponents.comap_of_flat h
  · show Smooth (h ≫ T.structMap)
    infer_instance
  · exact inStrictNormalCrossingPosition_comap T.structMap h T.boundary hV.snc

end MarkedIdealWithBoundary

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceZeroSection
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section

private theorem exists_iso_subscheme_of_ker_eq_consolidated387 {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (I : X.IdealSheafData) (hI : Scheme.Hom.ker i = I) :
    ∃ e : Z ≅ I.subscheme, e.hom ≫ I.subschemeι = i := by
  subst hI
  exact ⟨asIso i.toImage, i.toImage_imageι⟩

theorem exists_isPullback_of_ker_eq_comap {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (i' : Z' ⟶ X') [IsClosedImmersion i'] (g : X' ⟶ X)
    (h : Scheme.Hom.ker i' = (Scheme.Hom.ker i).comap g) :
    ∃ c : Z' ⟶ Z, IsPullback c i' i g := by
  obtain ⟨e, he⟩ := exists_iso_subscheme_of_ker_eq_consolidated387 i (Scheme.Hom.ker i) rfl
  obtain ⟨e', he'⟩ := exists_iso_subscheme_of_ker_eq_consolidated387 i' ((Scheme.Hom.ker i).comap g) h
  have h1 : IsPullback e'.hom i' ((Scheme.Hom.ker i).comap g).subschemeι (𝟙 X') :=
    IsPullback.of_horiz_isIso ⟨by rw [he', Category.comp_id]⟩
  have h2 := isPullback_comapSubschemeHom (Scheme.Hom.ker i) g
  have h3 : IsPullback e.inv (Scheme.Hom.ker i).subschemeι i (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, Iso.inv_comp_eq]; exact he.symm⟩
  refine ⟨(e'.hom ≫ comapSubschemeHom (Scheme.Hom.ker i) g) ≫ e.inv, ?_⟩
  have h4 := (h1.paste_horiz h2).paste_horiz h3
  rwa [Category.id_comp, Category.comp_id] at h4

abbrev opensPreimageProjLeft (k : Type u) [Field k] (M p : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).Opens) :
    (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin p))).Opens :=
  (Opens.map (projLeft k M p).base).obj U

section
variable (k : Type u) [Field k] (M p : ℕ) (U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).Opens)

theorem range_affineSpaceInl_subset_range_opensPreimageProjLeft :
    Set.range ⇑(U.ι ≫ affineSpaceInl k M p) ⊆ Set.range ⇑(opensPreimageProjLeft k M p U).ι := by
  have hcomp : (U.ι ≫ affineSpaceInl k M p) ≫ projLeft k M p = U.ι := by
    rw [Category.assoc, affineSpaceInl_comp_projLeft, Category.comp_id]
  rw [Set.range_subset_iff]
  intro x
  have hx : (projLeft k M p) ((U.ι ≫ affineSpaceInl k M p) x) = U.ι x :=
    congrArg (fun f : (U : Scheme.{u}) ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) => ⇑f x) hcomp
  have hmem : (U.ι ≫ affineSpaceInl k M p) x ∈ opensPreimageProjLeft k M p U := by
    show (projLeft k M p) ((U.ι ≫ affineSpaceInl k M p) x) ∈ U
    rw [hx]
    exact x.2
  exact ⟨⟨(U.ι ≫ affineSpaceInl k M p) x, hmem⟩, rfl⟩

private theorem exists_zeroSectionOverOpen_consolidated387 :
    ∃ z, z ≫ (opensPreimageProjLeft k M p U).ι = U.ι ≫ affineSpaceInl k M p ∧
      z ≫ (projLeft k M p ∣_ U) = 𝟙 _ := by
  have hfac : IsOpenImmersion.lift (opensPreimageProjLeft k M p U).ι (U.ι ≫ affineSpaceInl k M p)
        (range_affineSpaceInl_subset_range_opensPreimageProjLeft k M p U) ≫ (projLeft k M p ⁻¹ᵁ U).ι =
      U.ι ≫ affineSpaceInl k M p :=
    IsOpenImmersion.lift_fac (opensPreimageProjLeft k M p U).ι (U.ι ≫ affineSpaceInl k M p)
      (range_affineSpaceInl_subset_range_opensPreimageProjLeft k M p U)
  refine ⟨IsOpenImmersion.lift (opensPreimageProjLeft k M p U).ι (U.ι ≫ affineSpaceInl k M p)
      (range_affineSpaceInl_subset_range_opensPreimageProjLeft k M p U), hfac, ?_⟩
  rw [← cancel_mono (U.ι), Category.assoc, Category.id_comp, morphismRestrict_ι,
    ← Category.assoc, hfac, Category.assoc, affineSpaceInl_comp_projLeft, Category.comp_id]


end

def zeroSectionOverOpen (k : Type u) [Field k] (M p : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).Opens) :=
  (exists_zeroSectionOverOpen_consolidated387 k M p U).choose

@[simp]
theorem zeroSectionOverOpen_comp_ι (k : Type u) [Field k] (M p : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).Opens) :
    zeroSectionOverOpen k M p U ≫ (opensPreimageProjLeft k M p U).ι = U.ι ≫ affineSpaceInl k M p :=
  (exists_zeroSectionOverOpen_consolidated387 k M p U).choose_spec.1

@[simp]
theorem zeroSectionOverOpen_comp_ι_assoc (k : Type u) [Field k] (M p : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).Opens) {Z : Scheme.{u}}
    (g : affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin p)) ⟶ Z) :
    zeroSectionOverOpen k M p U ≫ (opensPreimageProjLeft k M p U).ι ≫ g = U.ι ≫ affineSpaceInl k M p ≫ g := by
  rw [← Category.assoc, zeroSectionOverOpen_comp_ι, Category.assoc]

@[simp]
theorem zeroSectionOverOpen_comp_restrict (k : Type u) [Field k] (M p : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).Opens) :
    zeroSectionOverOpen k M p U ≫ (projLeft k M p ∣_ U) = 𝟙 _ :=
  (exists_zeroSectionOverOpen_consolidated387 k M p U).choose_spec.2

theorem isPullback_zeroSectionOverOpen (k : Type u) [Field k] (M p c : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).Opens)
    (q : ↑U ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin c)))
    (hq : q ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin c)) =
      U.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) :
    IsPullback (zeroSectionOverOpen k M p U) q (prodMapOnPreimage k M p c U q) (affineSpaceInl k c p) := by
  have hcomm : zeroSectionOverOpen k M p U ≫ prodMapOnPreimage k M p c U q = q ≫ affineSpaceInl k c p := by
    refine (isPullback_projLeft_projRight k c p).hom_ext ?_ ?_
    · rw [Category.assoc, ← morphismRestrict_projLeft_comp k M p c U q hq]
      simp
      rw [← Category.assoc, zeroSectionOverOpen_comp_restrict, Category.id_comp]
    · rw [Category.assoc, prodMapOnPreimage_comp_projRight, zeroSectionOverOpen_comp_ι_assoc,
        affineSpaceInl_comp_projRight, Category.assoc, affineSpaceInl_comp_projRight,
        ← Category.assoc, ← Category.assoc, hq]
  have hs : IsPullback (zeroSectionOverOpen k M p U ≫ (projLeft k M p ∣_ U)) q q
      (affineSpaceInl k c p ≫ projLeft k c p) := by
    rw [zeroSectionOverOpen_comp_restrict, affineSpaceInl_comp_projLeft]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact IsPullback.of_right hs hcomm (isPullback_prodMapOnPreimage k M p c U q hq).flip

private theorem pullbackCoord_comp_eq_appTop_consolidated387 {k : Type u} [Field k] {T Y : Scheme.{u}}
    {n : Type u} (a : T ⟶ Y) (g : Y ⟶ affineSpaceIndexedBy k n) (i : n) :
    pullbackCoord (a ≫ g) i = a.appTop (pullbackCoord g i) := rfl

def uliftFinSumEquiv (c p : ℕ) : ULift.{u, 0} (Fin c ⊕ Fin p) ≃ ULift.{u, 0} (Fin (c + p)) :=
  Equiv.ulift.trans (finSumFinEquiv.trans Equiv.ulift.symm)

section
variable (k : Type u) [Field k]

private theorem pullbackCoord_affineSpaceIsoOfEquiv_hom_consolidated387 {n m : Type u}
    (e : n ≃ m) (i : m) :
    pullbackCoord (affineSpaceIsoOfEquiv e (Spec (CommRingCat.of k))).hom i =
      AffineSpace.coord (Spec (CommRingCat.of k)) (e.symm i) := by
  simp [pullbackCoord, affineSpaceIsoOfEquiv]

theorem affineSpaceOrigin_comp_affineSpaceInl_affineSpaceIsoOfEquiv (c p : ℕ) :
    affineSpaceOrigin k c ≫ affineSpaceInl k c p ≫
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom =
      affineSpaceOrigin k (c + p) := by
  refine eq_affineSpaceOrigin_of_pullbackCoord_eq_zero k (c + p) _ ?_ ?_
  · simp only [Category.assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec,
      affineSpaceInl_comp_affineSpaceIndexedByToSpec, affineSpaceOrigin_comp_toSpec]
  · intro i
    obtain ⟨j, rfl⟩ : ∃ j, i = uliftFinSumEquiv.{u} c p j :=
      ⟨(uliftFinSumEquiv.{u} c p).symm i, ((uliftFinSumEquiv.{u} c p).apply_symm_apply i).symm⟩
    have h1 : pullbackCoord (affineSpaceInl k c p ≫
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom)
          (uliftFinSumEquiv.{u} c p j) = pullbackCoord (affineSpaceInl k c p) j := by
      rw [pullbackCoord_comp_eq_appTop_consolidated387, pullbackCoord_affineSpaceIsoOfEquiv_hom_consolidated387,
        Equiv.symm_apply_apply, pullbackCoord_def]
    rw [pullbackCoord_comp_eq_appTop_consolidated387, h1]
    obtain ⟨a | b⟩ := j
    · rw [pullbackCoord_affineSpaceInl_inl]
      exact affineSpaceOrigin_appTop_coord k c (ULift.up a)
    · rw [pullbackCoord_affineSpaceInl_inr]
      simp


end

namespace HasSmoothCoordCodim

private theorem ker_eq_comap_ker_of_isPullback_closedImmersion_consolidated387 {Z X X' W : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (g : X' ⟶ X) (j : W ⟶ X') (a : W ⟶ Z)
    (H : IsPullback a j i g) :
    Scheme.Hom.ker j = (Scheme.Hom.ker i).comap g := by
  rw [← H.flip.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

section
variable (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] {M c : ℕ} {A : Scheme.{u}} (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ] (p : ℕ) (h : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) ρ c)
include hsm h

theorem comp_affineSpaceInl :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin p)))
      (ρ ≫ affineSpaceInl k M p) (c + p) := by
  intro x
  obtain ⟨U, hxU, q, hqsm, hqcomp, hker⟩ := h x
  have : Smooth q := hqsm
  have hker' : (Scheme.Hom.ker ρ).comap U.ι = (coordSubspaceIdeal k c Finset.univ).comap q := hker
  have hs : IsPullback (zeroSectionOverOpen k M p U ≫ (projLeft k M p ∣_ U)) U.ι U.ι
      (affineSpaceInl k M p ≫ projLeft k M p) := by
    rw [zeroSectionOverOpen_comp_restrict, affineSpaceInl_comp_projLeft]
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
  have hA : IsPullback (zeroSectionOverOpen k M p U) U.ι (opensPreimageProjLeft k M p U).ι (affineSpaceInl k M p) :=
    IsPullback.of_right hs (zeroSectionOverOpen_comp_ι k M p U)
      (isPullback_morphismRestrict (projLeft k M p) U)
  obtain ⟨a₀, hB⟩ := exists_isPullback_of_ker_eq_comap ρ
    ((Scheme.Hom.ker ρ).comap U.ι).subschemeι U.ι (Scheme.IdealSheafData.ker_subschemeι ..)
  have hW1 := hB.flip.paste_horiz hA
  have hB2 : Scheme.Hom.ker ((Scheme.Hom.ker ρ).comap U.ι).subschemeι =
      (Scheme.Hom.ker (affineSpaceOrigin k c)).comap q := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ker_affineSpaceOrigin]
    exact hker'
  obtain ⟨c₁, hC⟩ := exists_isPullback_of_ker_eq_comap (affineSpaceOrigin k c)
    ((Scheme.Hom.ker ρ).comap U.ι).subschemeι q hB2
  have hW2 := hC.flip.paste_horiz (isPullback_zeroSectionOverOpen k M p c U q hqcomp)
  have hRsq : IsPullback (𝟙 (opensPreimageProjLeft k M p U).toScheme) (prodMapOnPreimage k M p c U q)
      (prodMapOnPreimage k M p c U q ≫
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom)
      (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp]⟩
  have hσR : (affineSpaceOrigin k c ≫ affineSpaceInl k c p) ≫
      (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom =
      affineSpaceOrigin k (c + p) := by
    rw [Category.assoc, affineSpaceOrigin_comp_affineSpaceInl_affineSpaceIsoOfEquiv]
  have hW3 := hW2.paste_horiz hRsq
  rw [Category.comp_id, hσR] at hW3
  refine ⟨opensPreimageProjLeft k M p U, ?_, prodMapOnPreimage k M p c U q ≫
      (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom, ?_, ?_, ?_⟩
  · show (projLeft k M p) ((ρ ≫ affineSpaceInl k M p) x) ∈ U
    have hx1 : (projLeft k M p) ((ρ ≫ affineSpaceInl k M p) x) = ρ x :=
      congrArg (fun f : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) => ⇑f x)
        (show (ρ ≫ affineSpaceInl k M p) ≫ projLeft k M p = ρ by
          rw [Category.assoc, affineSpaceInl_comp_projLeft, Category.comp_id])
    rw [hx1]
    exact hxU
  · have : Smooth (prodMapOnPreimage k M p c U q) :=
      smooth_prodMapOnPreimage hsm k M p c U q hqcomp
    infer_instance
  · rw [Category.assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec, prodMapOnPreimage_comp_affineSpaceIndexedByToSpec]
  · show (Scheme.Hom.ker (ρ ≫ affineSpaceInl k M p)).comap (opensPreimageProjLeft k M p U).ι =
      (coordSubspaceIdeal k (c + p) Finset.univ).comap (prodMapOnPreimage k M p c U q ≫
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom)
    rw [← ker_eq_comap_ker_of_isPullback_closedImmersion_consolidated387 (ρ ≫ affineSpaceInl k M p)
        (opensPreimageProjLeft k M p U).ι _ _ hW1.flip,
      ker_eq_comap_ker_of_isPullback_closedImmersion_consolidated387 (affineSpaceOrigin k (c + p))
        (prodMapOnPreimage k M p c U q ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom) _ _ hW3.flip,
      ker_affineSpaceOrigin]

theorem comp_affineSpaceInl_affineSpaceIsoOfEquiv :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + p))))
      (ρ ≫ affineSpaceInl k M p ≫
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M p) (Spec (CommRingCat.of k))).hom) (c + p) := by
  have h1 := comp_affineSpaceInl hsm k ρ p h
  have h2 := h1.comp_iso_hom
    (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M p) (Spec (CommRingCat.of k)))
    (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + p))))
    (affineSpaceIsoOfEquiv_hom_comp_toSpec k (uliftFinSumEquiv.{u} M p))
  rwa [Category.assoc] at h2


end

end HasSmoothCoordCodim


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BasicOpenClosedEmbedding
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section

abbrev affineSpaceTimesLine (k : Type u) [Field k] (M : ℕ) : Scheme.{u} :=
  affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin 1))

def lastCoordinate (k : Type u) [Field k] (M : ℕ) :
    ↑((affineSpaceTimesLine k M).presheaf.obj (Opposite.op ⊤)) :=
  AffineSpace.coord (Spec (CommRingCat.of k)) (⟨Sum.inr 0⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))

@[simp]
theorem lastCoordinate_eq (k : Type u) [Field k] (M : ℕ) :
    lastCoordinate k M =
      AffineSpace.coord (Spec (CommRingCat.of k)) (⟨Sum.inr 0⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)) :=
  rfl

section
variable (k : Type u) [Field k] (M : ℕ)

theorem lastCoordinate_eq_coord (j : Fin 1) :
    lastCoordinate k M =
      AffineSpace.coord (Spec (CommRingCat.of k)) (⟨Sum.inr j⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)) := by
  rw [Subsingleton.elim j (0 : Fin 1)]
  rfl

theorem lastCoordinate_appTop_comp_affineSpaceInl {A : Scheme.{u}}
    (f : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (f ≫ affineSpaceInl k M 1))) (lastCoordinate k M) = 0 := by
  have h1 := pullbackCoord_affineSpaceInl_inr k M 1 (0 : Fin 1)
  rw [pullbackCoord_def] at h1
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, lastCoordinate_eq, h1, map_zero]


end

def pullbackAlongProjection (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) :
    ↑((affineSpaceTimesLine k M).presheaf.obj (Opposite.op ⊤)) :=
  (ConcreteCategory.hom (Scheme.Hom.appTop (projLeft k M 1))) G

def pullbackBasicOpen (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) :
    (affineSpaceTimesLine k M).Opens :=
  (affineSpaceTimesLine k M).basicOpen (pullbackAlongProjection k M G)

private theorem isUnit_appTop_ι_basicOpen_consolidated418 {X : Scheme.{u}}
    (f : ↑(X.presheaf.obj (Opposite.op ⊤))) :
    IsUnit ((ConcreteCategory.hom (Scheme.Hom.appTop (X.basicOpen f).ι)) f) := by
  have h1 : (↑(X.basicOpen f) : Scheme.{u}).basicOpen
        ((ConcreteCategory.hom (Scheme.Hom.appTop (X.basicOpen f).ι)) f) =
      (X.basicOpen f).ι ⁻¹ᵁ X.basicOpen f := (Scheme.preimage_basicOpen ..).symm
  have h2 : (X.basicOpen f).ι ⁻¹ᵁ X.basicOpen f = ⊤ :=
    Opens.ext (Set.eq_univ_of_forall fun x => x.2)
  have hbo := h1.trans h2
  refine RingedSpace.isUnit_of_isUnit_germ
    ((↑(X.basicOpen f) : Scheme.{u}).toLocallyRingedSpace.toRingedSpace) ⊤ _ ?_
  intro x hx
  refine ((↑(X.basicOpen f) : Scheme.{u}).mem_basicOpen
    ((ConcreteCategory.hom (Scheme.Hom.appTop (X.basicOpen f).ι)) f) x hx).mp ?_
  rw [hbo]
  exact Opens.mem_top _

theorem isUnit_appTop_ι_pullbackAlongProjection (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) :
    IsUnit ((ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι)) (pullbackAlongProjection k M G)) :=
  isUnit_appTop_ι_basicOpen_consolidated418 (pullbackAlongProjection k M G)

def unitOnPullbackBasicOpen (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) :
    (↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤)))ˣ :=
  (isUnit_appTop_ι_pullbackAlongProjection k M G).unit

@[simp]
theorem unitOnPullbackBasicOpen_val (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) :
    (unitOnPullbackBasicOpen k M G).val =
      (ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι)) (pullbackAlongProjection k M G) :=
  IsUnit.unit_spec _

section
variable (k : Type u) [Field k] (M : ℕ)

private theorem appTop_comp_projLeft_coord_consolidated418 {T : Scheme.{u}}
    (t : T ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin 1))) (j : Fin M) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (t ≫ projLeft k M 1)))
        (AffineSpace.coord (Spec (CommRingCat.of k)) (⟨j⟩ : ULift.{u, 0} (Fin M))) =
      (ConcreteCategory.hom (Scheme.Hom.appTop t))
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (⟨Sum.inl j⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, projLeft_appTop_coord]

private theorem exists_replaceLastCoord_consolidated418 (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    ∃ f : (↑(pullbackBasicOpen k M G) : Scheme.{u}) ⟶ affineSpaceTimesLine k M,
      f ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
          (pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) ∧
      (∀ a : Fin M,
          pullbackCoord f ⟨Sum.inl a⟩ = pullbackCoord (pullbackBasicOpen k M G).ι ⟨Sum.inl a⟩) ∧
      (ConcreteCategory.hom (Scheme.Hom.appTop f)) (lastCoordinate k M) = s ∧
      f ≫ projLeft k M 1 = (pullbackBasicOpen k M G).ι ≫ projLeft k M 1 := by
  obtain ⟨f, hover, hcoord⟩ :
      ∃ f : (↑(pullbackBasicOpen k M G) : Scheme.{u}) ⟶ affineSpaceTimesLine k M,
        f ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
            (pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) ∧
          ∀ i : ULift.{u, 0} (Fin M ⊕ Fin 1),
            (ConcreteCategory.hom (Scheme.Hom.appTop f))
                (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
              Sum.elim
                (fun a : Fin M =>
                  pullbackCoord (pullbackBasicOpen k M G).ι (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)))
                (fun _ : Fin 1 => s) i.down := by
    refine ⟨AffineSpace.homOfVector
        ((pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
        (fun i : ULift.{u, 0} (Fin M ⊕ Fin 1) =>
          Sum.elim
            (fun a : Fin M =>
              pullbackCoord (pullbackBasicOpen k M G).ι (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)))
            (fun _ : Fin 1 => s) i.down), ?_, ?_⟩
    · apply AffineSpace.homOfVector_over
    · intro i
      rw [AffineSpace.homOfVector_appTop_coord]
  refine ⟨f, hover, ?_, ?_, ?_⟩
  · intro a
    exact (pullbackCoord_def f (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))).trans
      (hcoord (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)))
  · exact hcoord (⟨Sum.inr 0⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))
  · refine AffineSpace.hom_ext ?_ ?_
    · have h1 : (f ≫ projLeft k M 1) ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) =
          ((pullbackBasicOpen k M G).ι ≫ projLeft k M 1) ≫
            affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) := by
        rw [Category.assoc, Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, hover]
      exact h1
    · intro i
      obtain ⟨j⟩ := i
      exact (appTop_comp_projLeft_coord_consolidated418 k M f j).trans
        ((hcoord (⟨Sum.inl j⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))).trans
          ((pullbackCoord_def (pullbackBasicOpen k M G).ι
              (⟨Sum.inl j⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))).trans
            (appTop_comp_projLeft_coord_consolidated418 k M (pullbackBasicOpen k M G).ι j).symm))


end

def replaceLastCoord (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    (↑(pullbackBasicOpen k M G) : Scheme.{u}) ⟶ affineSpaceTimesLine k M :=
  (exists_replaceLastCoord_consolidated418 k M G s).choose

section
variable (k : Type u) [Field k] (M : ℕ) (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤)))

theorem replaceLastCoord_comp_affineSpaceIndexedByToSpec :
    replaceLastCoord k M G s ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
      (pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) :=
  (exists_replaceLastCoord_consolidated418 k M G s).choose_spec.1

theorem pullbackCoord_replaceLastCoord_inl (a : Fin M) :
    pullbackCoord (replaceLastCoord k M G s) ⟨Sum.inl a⟩ =
      pullbackCoord (pullbackBasicOpen k M G).ι ⟨Sum.inl a⟩ :=
  (exists_replaceLastCoord_consolidated418 k M G s).choose_spec.2.1 a

theorem replaceLastCoord_appTop_lastCoordinate :
    (ConcreteCategory.hom (Scheme.Hom.appTop (replaceLastCoord k M G s))) (lastCoordinate k M) = s :=
  (exists_replaceLastCoord_consolidated418 k M G s).choose_spec.2.2.1


end

@[simp]
theorem replaceLastCoord_comp_projLeft (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    replaceLastCoord k M G s ≫ projLeft k M 1 = (pullbackBasicOpen k M G).ι ≫ projLeft k M 1 :=
  (exists_replaceLastCoord_consolidated418 k M G s).choose_spec.2.2.2

@[simp]
theorem replaceLastCoord_comp_projLeft_assoc (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) {Z : Scheme.{u}}
    (g : affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) ⟶ Z) :
    replaceLastCoord k M G s ≫ projLeft k M 1 ≫ g = (pullbackBasicOpen k M G).ι ≫ projLeft k M 1 ≫ g := by
  rw [← Category.assoc, replaceLastCoord_comp_projLeft, Category.assoc]

section
variable (k : Type u) [Field k] (M : ℕ) (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))

private theorem mem_pullbackBasicOpen_iff_consolidated418 (y : ↥(affineSpaceTimesLine k M)) :
    y ∈ pullbackBasicOpen k M G ↔
      (projLeft k M 1).base y ∈ (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).basicOpen G :=
  Iff.symm (iff_of_eq (congrArg (fun U : (affineSpaceTimesLine k M).Opens => y ∈ U)
    (Scheme.preimage_basicOpen (projLeft k M 1) G)))

private theorem exists_comp_ι_eq_replaceLastCoord_consolidated418 (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    ∃ g : (↑(pullbackBasicOpen k M G) : Scheme.{u}) ⟶ (↑(pullbackBasicOpen k M G) : Scheme.{u}),
      g ≫ (pullbackBasicOpen k M G).ι = replaceLastCoord k M G s := by
  have hrange : Set.range (replaceLastCoord k M G s).base ⊆
      Set.range (pullbackBasicOpen k M G).ι.base := by
    rintro _ ⟨x, rfl⟩
    have h1 : (projLeft k M 1).base ((replaceLastCoord k M G s).base x) =
        (projLeft k M 1).base ((pullbackBasicOpen k M G).ι.base x) :=
      congrArg (fun f : (↑(pullbackBasicOpen k M G) : Scheme.{u}) ⟶
          affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) => f.base x)
        (replaceLastCoord_comp_projLeft k M G s)
    have hx : (pullbackBasicOpen k M G).ι.base x ∈ pullbackBasicOpen k M G := by
      have h0 : (pullbackBasicOpen k M G).ι.base x ∈ Set.range (pullbackBasicOpen k M G).ι.base :=
        Set.mem_range_self x
      rw [Scheme.Opens.range_ι] at h0
      exact h0
    have h2 := (mem_pullbackBasicOpen_iff_consolidated418 k M G ((pullbackBasicOpen k M G).ι.base x)).1 hx
    rw [Scheme.Opens.range_ι]
    refine (mem_pullbackBasicOpen_iff_consolidated418 k M G ((replaceLastCoord k M G s).base x)).2 ?_
    rw [h1]
    exact h2
  exact ⟨IsOpenImmersion.lift (pullbackBasicOpen k M G).ι (replaceLastCoord k M G s) hrange,
    IsOpenImmersion.lift_fac (pullbackBasicOpen k M G).ι (replaceLastCoord k M G s) hrange⟩


end

def shiftLastCoord (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    (↑(pullbackBasicOpen k M G) : Scheme.{u}) ⟶ (↑(pullbackBasicOpen k M G) : Scheme.{u}) :=
  (exists_comp_ι_eq_replaceLastCoord_consolidated418 k M G s).choose

@[simp]
theorem shiftLastCoord_comp_ι (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    shiftLastCoord k M G s ≫ (pullbackBasicOpen k M G).ι = replaceLastCoord k M G s :=
  (exists_comp_ι_eq_replaceLastCoord_consolidated418 k M G s).choose_spec

@[simp]
theorem shiftLastCoord_comp_ι_assoc (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) {Z : Scheme.{u}}
    (g : affineSpaceTimesLine k M ⟶ Z) :
    shiftLastCoord k M G s ≫ (pullbackBasicOpen k M G).ι ≫ g = replaceLastCoord k M G s ≫ g := by
  rw [← Category.assoc, shiftLastCoord_comp_ι]

private theorem appTop_surjective_of_isAffine_consolidated418 {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine Y] [IsClosedImmersion f] :
    Function.Surjective (ConcreteCategory.hom (Scheme.Hom.appTop f)) :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine ..).2

private theorem exists_appTop_eq_of_isClosedImmersion_consolidated418 (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    ∃ G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)),
      (ConcreteCategory.hom (Scheme.Hom.appTop ρ)) G = F :=
  appTop_surjective_of_isAffine_consolidated418 ρ F

def globalSectionLift (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)) :=
  (exists_appTop_eq_of_isClosedImmersion_consolidated418 k M ρ F).choose

@[simp]
theorem appTop_globalSectionLift (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop ρ)) (globalSectionLift k M ρ F) = F :=
  (exists_appTop_eq_of_isClosedImmersion_consolidated418 k M ρ F).choose_spec

section
variable (k : Type u) [Field k] (M : ℕ) (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))

private theorem pullbackAlongProjection_eq_consolidated418 :
    pullbackAlongProjection k M G = (ConcreteCategory.hom (Scheme.Hom.appTop (projLeft k M 1))) G :=
  rfl

private theorem replaceLastCoord_appTop_pullbackAlongProjection_consolidated418 (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (replaceLastCoord k M G s))) (pullbackAlongProjection k M G) =
      (ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι)) (pullbackAlongProjection k M G) := by
  rw [pullbackAlongProjection_eq_consolidated418, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, replaceLastCoord_comp_projLeft]

private theorem shiftLastCoord_appTop_unitOnPullbackBasicOpen_val_consolidated418 (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (shiftLastCoord k M G s))) ((unitOnPullbackBasicOpen k M G).val) =
      (unitOnPullbackBasicOpen k M G).val := by
  rw [unitOnPullbackBasicOpen_val, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, shiftLastCoord_comp_ι,
    replaceLastCoord_appTop_pullbackAlongProjection_consolidated418]

private theorem shiftLastCoord_appTop_unitOnPullbackBasicOpen_inv_val_consolidated418 (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (shiftLastCoord k M G s))) (((unitOnPullbackBasicOpen k M G)⁻¹).val) =
      ((unitOnPullbackBasicOpen k M G)⁻¹).val := by
  have h1 : (ConcreteCategory.hom (Scheme.Hom.appTop (shiftLastCoord k M G s)))
      (((unitOnPullbackBasicOpen k M G)⁻¹).val) * (unitOnPullbackBasicOpen k M G).val = 1 := by
    rw [← shiftLastCoord_appTop_unitOnPullbackBasicOpen_val_consolidated418 k M G s, ← map_mul, Units.inv_mul, map_one]
  exact (Units.inv_eq_of_mul_eq_one_left h1).symm

private theorem shiftLastCoord_comp_shiftLastCoord_consolidated418 (s t : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤)))
    (ht : (ConcreteCategory.hom (Scheme.Hom.appTop (shiftLastCoord k M G s))) t =
      (ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι)) (lastCoordinate k M)) :
    shiftLastCoord k M G s ≫ shiftLastCoord k M G t = 𝟙 _ := by
  rw [← cancel_mono (pullbackBasicOpen k M G).ι, Category.assoc, shiftLastCoord_comp_ι, Category.id_comp]
  refine AffineSpace.hom_ext ?_ ?_
  · have h1 : (shiftLastCoord k M G s ≫ replaceLastCoord k M G t) ≫
        affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
        (pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) := by
      rw [Category.assoc, replaceLastCoord_comp_affineSpaceIndexedByToSpec, ← Category.assoc, shiftLastCoord_comp_ι,
        replaceLastCoord_comp_affineSpaceIndexedByToSpec]
    exact h1
  · intro i
    obtain ⟨j⟩ := i
    cases j with
    | inl a =>
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        ← pullbackCoord_def (replaceLastCoord k M G t)
          (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)),
        pullbackCoord_replaceLastCoord_inl,
        pullbackCoord_def (pullbackBasicOpen k M G).ι (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)),
        ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, shiftLastCoord_comp_ι,
        ← pullbackCoord_def (replaceLastCoord k M G s)
          (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)),
        pullbackCoord_replaceLastCoord_inl,
        pullbackCoord_def (pullbackBasicOpen k M G).ι (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))]
    | inr b =>
      rw [← lastCoordinate_eq_coord k M b, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        replaceLastCoord_appTop_lastCoordinate, ht]

private theorem isIso_shiftLastCoord_lastCoordinate_add_inv_consolidated418 :
    IsIso (shiftLastCoord k M G
      ((ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι)) (lastCoordinate k M) +
        ((unitOnPullbackBasicOpen k M G)⁻¹).val)) := by
  refine ⟨⟨shiftLastCoord k M G
      ((ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι)) (lastCoordinate k M) -
        ((unitOnPullbackBasicOpen k M G)⁻¹).val), ?_, ?_⟩⟩
  · apply shiftLastCoord_comp_shiftLastCoord_consolidated418
    rw [map_sub, shiftLastCoord_appTop_unitOnPullbackBasicOpen_inv_val_consolidated418, ← CommRingCat.comp_apply,
      ← Scheme.Hom.comp_appTop, shiftLastCoord_comp_ι, replaceLastCoord_appTop_lastCoordinate]
    ring
  · apply shiftLastCoord_comp_shiftLastCoord_consolidated418
    rw [map_add, shiftLastCoord_appTop_unitOnPullbackBasicOpen_inv_val_consolidated418, ← CommRingCat.comp_apply,
      ← Scheme.Hom.comp_appTop, shiftLastCoord_comp_ι, replaceLastCoord_appTop_lastCoordinate]
    ring


end

section
variable (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}} (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]

private theorem exists_isClosedImmersion_pullbackBasicOpen_consolidated418 (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (V : A.Opens)
    (hV : V = (Opens.map (ρ ≫ affineSpaceInl k M 1).base).obj (pullbackBasicOpen k M G)) :
    ∃ e : (↑V : Scheme.{u}) ⟶ (↑(pullbackBasicOpen k M G) : Scheme.{u}),
      IsClosedImmersion e ∧
      e ≫ (pullbackBasicOpen k M G).ι ≫ projLeft k M 1 = V.ι ≫ ρ ∧
      (ConcreteCategory.hom (Scheme.Hom.appTop (e ≫ (pullbackBasicOpen k M G).ι)))
          (lastCoordinate k M * pullbackAlongProjection k M G) = 1 := by
  subst hV
  have hci : IsClosedImmersion ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) := by
    have hco : IsClosedImmersion (ρ ≫ affineSpaceInl k M 1) := inferInstance
    infer_instance
  have hiso := isIso_shiftLastCoord_lastCoordinate_add_inv_consolidated418 k M G
  refine ⟨((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) ≫
      shiftLastCoord k M G ((ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι))
        (lastCoordinate k M) + ((unitOnPullbackBasicOpen k M G)⁻¹).val), ?_, ?_, ?_⟩
  · exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ _).mpr hci
  · rw [Category.assoc, shiftLastCoord_comp_ι_assoc, replaceLastCoord_comp_projLeft, ← Category.assoc,
      morphismRestrict_ι, Category.assoc, Category.assoc, affineSpaceInl_comp_projLeft,
      Category.comp_id]
  · have h0 : (ConcreteCategory.hom (Scheme.Hom.appTop
        ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G)))
        ((ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι)) (lastCoordinate k M)) = 0 := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, morphismRestrict_ι,
        ← Category.assoc]
      exact lastCoordinate_appTop_comp_affineSpaceInl k M _
    rw [Category.assoc, shiftLastCoord_comp_ι, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, map_mul,
      replaceLastCoord_appTop_lastCoordinate, replaceLastCoord_appTop_pullbackAlongProjection_consolidated418, ← unitOnPullbackBasicOpen_val, map_mul,
      map_add, h0, zero_add, ← map_mul, Units.inv_mul, map_one]

private theorem exists_isClosedImmersion_basicOpen_pullbackBasicOpen_consolidated418 (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    ∃ e : (↑(A.basicOpen F) : Scheme.{u}) ⟶
        (↑(pullbackBasicOpen k M (globalSectionLift k M ρ F)) : Scheme.{u}),
      IsClosedImmersion e ∧
      e ≫ (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι ≫ projLeft k M 1 = (A.basicOpen F).ι ≫ ρ ∧
      (ConcreteCategory.hom
          (Scheme.Hom.appTop (e ≫ (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι)))
          (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F)) = 1 := by
  refine exists_isClosedImmersion_pullbackBasicOpen_consolidated418 k M ρ (globalSectionLift k M ρ F) (A.basicOpen F) ?_
  have hF : (ConcreteCategory.hom (Scheme.Hom.appTop (ρ ≫ affineSpaceInl k M 1)))
      (pullbackAlongProjection k M (globalSectionLift k M ρ F)) = F := by
    rw [pullbackAlongProjection_eq_consolidated418, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Category.assoc,
      affineSpaceInl_comp_projLeft, Category.comp_id, appTop_globalSectionLift]
  exact (congrArg (fun r : ↑(A.presheaf.obj (Opposite.op ⊤)) => A.basicOpen r) hF).symm.trans
    (Scheme.preimage_basicOpen (ρ ≫ affineSpaceInl k M 1)
      (pullbackAlongProjection k M (globalSectionLift k M ρ F))).symm


end

def basicOpenToPullbackBasicOpen (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    (↑(A.basicOpen F) : Scheme.{u}) ⟶ (↑(pullbackBasicOpen k M (globalSectionLift k M ρ F)) : Scheme.{u}) :=
  (exists_isClosedImmersion_basicOpen_pullbackBasicOpen_consolidated418 k M ρ F).choose

theorem isClosedImmersion_basicOpenToPullbackBasicOpen (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    IsClosedImmersion (basicOpenToPullbackBasicOpen k M ρ F) :=
  (exists_isClosedImmersion_basicOpen_pullbackBasicOpen_consolidated418 k M ρ F).choose_spec.1

instance instIsClosedImmersionPadLocalEmb (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    IsClosedImmersion (basicOpenToPullbackBasicOpen k M ρ F) :=
  isClosedImmersion_basicOpenToPullbackBasicOpen k M ρ F

theorem basicOpenToPullbackBasicOpen_comp_projLeft (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    basicOpenToPullbackBasicOpen k M ρ F ≫ (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι ≫ projLeft k M 1 =
      (A.basicOpen F).ι ≫ ρ :=
  (exists_isClosedImmersion_basicOpen_pullbackBasicOpen_consolidated418 k M ρ F).choose_spec.2.1

def basicOpenEmbedding (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    (↑(A.basicOpen F) : Scheme.{u}) ⟶ affineSpaceTimesLine k M :=
  basicOpenToPullbackBasicOpen k M ρ F ≫ (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι

theorem appTop_basicOpenEmbedding_lastCoordinate_mul (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (basicOpenEmbedding k M ρ F)))
        (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F)) = 1 :=
  (exists_isClosedImmersion_basicOpen_pullbackBasicOpen_consolidated418 k M ρ F).choose_spec.2.2

section
variable {R S : Type u} [CommRing R] [CommRing S]

private theorem isUnit_map_of_not_isUnit_map_mul_sub_one_consolidated418 [IsLocalRing S] (φ : R →+* S) (a b : R) (h : ¬ IsUnit (φ (a * b - 1))) : IsUnit (φ b) := by
  rw [map_sub, map_mul, map_one] at h
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (φ a * φ b) with h1 | h1
  · exact isUnit_of_mul_isUnit_right h1
  · refine absurd ?_ h
    have h2 := h1.neg
    rwa [neg_sub] at h2

private theorem false_of_isUnit_map_zero_consolidated418 [Nontrivial S] (φ : R →+* S) (h : IsUnit (φ (0 : R))) : False := by
  rw [map_zero] at h
  exact not_isUnit_zero h


end

private theorem isClosed_image_of_isInducing_consolidated418 {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (g : Y → X) (hg : Topology.IsInducing g) (S : Set X) (C : Set Y)
    (hSimage : S = g '' C) (hC : IsClosed C) (W : Set X) (hW : IsClosed W) (h1 : S ⊆ W)
    (h2 : W ⊆ Set.range g) :
    IsClosed S := by
  obtain ⟨D, hD, hpreimage⟩ := hg.isClosed_iff.1 hC
  have himg : g '' C = D ∩ Set.range g := by
    rw [← hpreimage, Set.image_preimage_eq_inter_range]
  have hEq : S = D ∩ W := by
    refine Set.Subset.antisymm (Set.subset_inter ?_ h1) ?_
    · rw [hSimage, himg]
      exact fun x hx => hx.1
    · intro x hx
      rw [hSimage, himg]
      exact ⟨hx.1, h2 hx.2⟩
  rw [hEq]
  exact hD.inter hW

theorem isClosedImmersion_basicOpenEmbedding (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    IsClosedImmersion (basicOpenEmbedding k M ρ F) := by
  have hpre : IsPreimmersion (basicOpenEmbedding k M ρ F) := by
    show IsPreimmersion (basicOpenToPullbackBasicOpen k M ρ F ≫ (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι)
    infer_instance
  have h0 : (ConcreteCategory.hom (Scheme.Hom.appTop (basicOpenEmbedding k M ρ F)))
      (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F) - 1) = 0 := by
    rw [map_sub, map_one, appTop_basicOpenEmbedding_lastCoordinate_mul, sub_self]
  have hind : Topology.IsInducing (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι.base :=
    (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι.isOpenEmbedding.toIsEmbedding.toIsInducing
  have hC : IsClosed (Set.range (basicOpenToPullbackBasicOpen k M ρ F).base) :=
    (Scheme.Hom.isClosedEmbedding (basicOpenToPullbackBasicOpen k M ρ F)).isClosed_range
  have heq : Set.range (basicOpenEmbedding k M ρ F).base =
      (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι.base '' Set.range (basicOpenToPullbackBasicOpen k M ρ F).base := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(basicOpenToPullbackBasicOpen k M ρ F).base y, ⟨y, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, rfl⟩
  have hW : IsClosed ((((affineSpaceTimesLine k M).basicOpen
      (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F) - 1) : (affineSpaceTimesLine k M).Opens) :
        Set ↥(affineSpaceTimesLine k M))ᶜ) :=
    ((affineSpaceTimesLine k M).basicOpen
      (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F) - 1)).isOpen.isClosed_compl
  have h1 : Set.range (basicOpenEmbedding k M ρ F).base ⊆
      ((((affineSpaceTimesLine k M).basicOpen
        (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F) - 1) : (affineSpaceTimesLine k M).Opens) :
          Set ↥(affineSpaceTimesLine k M))ᶜ) := by
    rintro z ⟨y, rfl⟩
    intro hz
    have hz' : y ∈ (basicOpenEmbedding k M ρ F) ⁻¹ᵁ ((affineSpaceTimesLine k M).basicOpen
        (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F) - 1)) := hz
    rw [Scheme.preimage_basicOpen] at hz'
    have hy : y ∈ (↑(A.basicOpen F) : Scheme.{u}).basicOpen
        ((ConcreteCategory.hom (Scheme.Hom.appTop (basicOpenEmbedding k M ρ F)))
          (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F) - 1)) := hz'
    rw [h0] at hy
    exact false_of_isUnit_map_zero_consolidated418 _
      (((↑(A.basicOpen F) : Scheme.{u}).mem_basicOpen _ y (Opens.mem_top y)).mp hy)
  have h2 : ((((affineSpaceTimesLine k M).basicOpen
      (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F) - 1) : (affineSpaceTimesLine k M).Opens) :
        Set ↥(affineSpaceTimesLine k M))ᶜ) ⊆ Set.range (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι.base := by
    intro x hx
    have hx' : x ∉ (affineSpaceTimesLine k M).basicOpen
        (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F) - 1) := hx
    rw [(affineSpaceTimesLine k M).mem_basicOpen _ x (Opens.mem_top x)] at hx'
    have hmem : x ∈ (affineSpaceTimesLine k M).basicOpen (pullbackAlongProjection k M (globalSectionLift k M ρ F)) := by
      rw [(affineSpaceTimesLine k M).mem_basicOpen _ x (Opens.mem_top x)]
      exact isUnit_map_of_not_isUnit_map_mul_sub_one_consolidated418 _ (lastCoordinate k M)
        (pullbackAlongProjection k M (globalSectionLift k M ρ F)) hx'
    rw [Scheme.Opens.range_ι]
    exact hmem
  apply IsClosedImmersion.of_isPreimmersion
  exact isClosed_image_of_isInducing_consolidated418 _ hind _ _ heq hC _ hW h1 h2

instance instIsClosedImmersionLocalizationEmb (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    IsClosedImmersion (basicOpenEmbedding k M ρ F) :=
  isClosedImmersion_basicOpenEmbedding k M ρ F

theorem basicOpenEmbedding_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) (p : A ⟶ Spec (CommRingCat.of k))
    (hp : ρ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) = p) :
    basicOpenEmbedding k M ρ F ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
      (A.basicOpen F).ι ≫ p := by
  have h1 := basicOpenToPullbackBasicOpen_comp_projLeft k M ρ F
  have h2 : basicOpenToPullbackBasicOpen k M ρ F ≫ (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι ≫ projLeft k M 1 ≫
        affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) =
      (A.basicOpen F).ι ≫ ρ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) := by
    rw [← Category.assoc ((pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι) (projLeft k M 1),
      ← Category.assoc (basicOpenToPullbackBasicOpen k M ρ F), h1, Category.assoc]
  show (basicOpenToPullbackBasicOpen k M ρ F ≫ (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι) ≫
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) = (A.basicOpen F).ι ≫ p
  rw [Category.assoc, ← projLeft_comp_affineSpaceIndexedByToSpec k M 1, h2, hp]

private theorem hasSmoothCoordCodim_comp_opens_ι_consolidated418 {k : Type u} [Field k] {X Y : Scheme.{u}}
    (s : Y ⟶ Spec (CommRingCat.of k)) (O : Y.Opens) (g : X ⟶ (↑O : Scheme.{u})) {c : ℕ}
    (hcg : IsClosedImmersion g) (hcgo : IsClosedImmersion (g ≫ O.ι))
    (h : HasSmoothCoordCodim (O.ι ≫ s) g c) :
    HasSmoothCoordCodim s (g ≫ O.ι) c := by
  have := hcg
  have := hcgo
  rw [hasSmoothCoordCodim_iff]
  intro x
  obtain ⟨U, hxU, q, hq, hqs, hideal⟩ := (hasSmoothCoordCodim_iff (O.ι ≫ s) g c).1 h x
  obtain ⟨W, ψ, hψiso, hψ, hmem⟩ :
      ∃ (W : Y.Opens) (ψ : (↑W : Scheme.{u}) ⟶ (↑U : Scheme.{u})),
        IsIso ψ ∧ ψ ≫ (U.ι ≫ O.ι) = W.ι ∧ (g ≫ O.ι).base x ∈ W := by
    have hrange : Set.range (U.ι ≫ O.ι).base =
        Set.range (Scheme.Hom.opensRange (U.ι ≫ O.ι)).ι.base := by
      rw [Scheme.Opens.range_ι]
      rfl
    refine ⟨Scheme.Hom.opensRange (U.ι ≫ O.ι),
      (IsOpenImmersion.isoOfRangeEq (U.ι ≫ O.ι)
        (Scheme.Hom.opensRange (U.ι ≫ O.ι)).ι hrange).inv, inferInstance,
      IsOpenImmersion.isoOfRangeEq_inv_fac _ _ hrange, ?_⟩
    have hxr : g.base x ∈ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      exact hxU
    obtain ⟨y, hy⟩ := hxr
    exact ⟨y, congrArg (⇑O.ι) hy⟩
  have := hψiso
  refine ⟨W, hmem, ψ ≫ q, ?_, ?_, ?_⟩
  · have : Smooth q := hq
    infer_instance
  · rw [Category.assoc, hqs, ← hψ]
    simp only [Category.assoc]
  · rw [restrictIdeal_eq_comap_ι] at hideal
    rw [restrictIdeal_eq_comap_ι, ← hψ, Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.comap_comp, Blowup.comap_ker_comp_of_isOpenImmersion g O.ι, hideal,
      Scheme.IdealSheafData.comap_comp]

private noncomputable def lastCoordinateAddInvUnit (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) :
    ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤)) :=
  (ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι)) (lastCoordinate k M) +
    ((unitOnPullbackBasicOpen k M G)⁻¹).val

section
variable (k : Type u) [Field k] (M : ℕ) (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))

private theorem shiftLastCoordSection_eq_consolidated418 :
    lastCoordinateAddInvUnit k M G =
      (ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι)) (lastCoordinate k M) +
        ((unitOnPullbackBasicOpen k M G)⁻¹).val :=
  rfl

private theorem isIso_shiftLastCoord_shiftLastCoordSection_consolidated418 :
    IsIso (shiftLastCoord k M G (lastCoordinateAddInvUnit k M G)) :=
  isIso_shiftLastCoord_lastCoordinate_add_inv_consolidated418 k M G


end

section
variable (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] (M c : ℕ) {A : Scheme.{u}} (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
include hsm

private theorem hasSmoothCoordCodim_comp_pullbackBasicOpen_ι_consolidated418 (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (V : A.Opens)
    (hV : V = (Opens.map (ρ ≫ affineSpaceInl k M 1).base).obj (pullbackBasicOpen k M G))
    (e : (↑V : Scheme.{u}) ⟶ (↑(pullbackBasicOpen k M G) : Scheme.{u}))
    (hce : IsClosedImmersion e)
    (hceo : IsClosedImmersion (e ≫ (pullbackBasicOpen k M G).ι))
    (hproj : e ≫ (pullbackBasicOpen k M G).ι ≫ projLeft k M 1 = V.ι ≫ ρ)
    (hrel : (ConcreteCategory.hom (Scheme.Hom.appTop (e ≫ (pullbackBasicOpen k M G).ι)))
      (lastCoordinate k M * pullbackAlongProjection k M G) = 1)
    (h : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) ρ c) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
      (e ≫ (pullbackBasicOpen k M G).ι) (c + 1) := by
  subst hV
  have := hce
  have : IsIso (shiftLastCoord k M G (lastCoordinateAddInvUnit k M G)) := isIso_shiftLastCoord_shiftLastCoordSection_consolidated418 k M G
  have hE : ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) ≫
      (asIso (shiftLastCoord k M G (lastCoordinateAddInvUnit k M G))).hom = e := by
    show ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) ≫ shiftLastCoord k M G (lastCoordinateAddInvUnit k M G) = e
    rw [← cancel_mono (pullbackBasicOpen k M G).ι, Category.assoc, shiftLastCoord_comp_ι]
    have hstr : (e ≫ (pullbackBasicOpen k M G).ι) ≫
          affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
        (((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) ≫
            replaceLastCoord k M G (lastCoordinateAddInvUnit k M G)) ≫
          affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) := by
      rw [Category.assoc, Category.assoc, replaceLastCoord_comp_affineSpaceIndexedByToSpec,
        ← Category.assoc ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G), morphismRestrict_ι,
        ← projLeft_comp_affineSpaceIndexedByToSpec k M 1, ← Category.assoc (pullbackBasicOpen k M G).ι, ← Category.assoc e, hproj]
      simp only [Category.assoc]
      rw [affineSpaceInl_comp_projLeft_assoc]
    refine AffineSpace.hom_ext ?_ ?_
    · exact hstr.symm
    · intro i
      obtain ⟨j⟩ := i
      cases j with
      | inl a =>
        have hl : (ConcreteCategory.hom (Scheme.Hom.appTop (e ≫ (pullbackBasicOpen k M G).ι)))
              (AffineSpace.coord (Spec (CommRingCat.of k))
                (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))) =
            (ConcreteCategory.hom (Scheme.Hom.appTop
              (e ≫ (pullbackBasicOpen k M G).ι ≫ projLeft k M 1)))
              (AffineSpace.coord (Spec (CommRingCat.of k)) (⟨a⟩ : ULift.{u, 0} (Fin M))) := by
          rw [← projLeft_appTop_coord k M 1 a, ← CommRingCat.comp_apply,
            ← Scheme.Hom.comp_appTop, Category.assoc]
        have hr : (ConcreteCategory.hom (Scheme.Hom.appTop
              (((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) ≫
                replaceLastCoord k M G (lastCoordinateAddInvUnit k M G))))
              (AffineSpace.coord (Spec (CommRingCat.of k))
                (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))) =
            (ConcreteCategory.hom (Scheme.Hom.appTop
              (e ≫ (pullbackBasicOpen k M G).ι ≫ projLeft k M 1)))
              (AffineSpace.coord (Spec (CommRingCat.of k)) (⟨a⟩ : ULift.{u, 0} (Fin M))) := by
          rw [hproj, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
            ← pullbackCoord_def (replaceLastCoord k M G (lastCoordinateAddInvUnit k M G))
              (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)),
            pullbackCoord_replaceLastCoord_inl, pullbackCoord_def, ← CommRingCat.comp_apply,
            ← Scheme.Hom.comp_appTop, morphismRestrict_ι, ← Category.assoc,
            Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
            ← pullbackCoord_def (affineSpaceInl k M 1)
              (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)),
            pullbackCoord_affineSpaceInl_inl]
        exact hr.trans hl.symm
      | inr b =>
        have hu : (ConcreteCategory.hom (Scheme.Hom.appTop (e ≫ (pullbackBasicOpen k M G).ι)))
              (lastCoordinate k M) *
            (ConcreteCategory.hom (Scheme.Hom.appTop (e ≫ (pullbackBasicOpen k M G).ι)))
              (pullbackAlongProjection k M G) = 1 := by
          rw [← map_mul]
          exact hrel
        have hX : (ConcreteCategory.hom (Scheme.Hom.appTop (e ≫ (pullbackBasicOpen k M G).ι)))
              (pullbackAlongProjection k M G) =
            (ConcreteCategory.hom (Scheme.Hom.appTop
              ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G))) ((unitOnPullbackBasicOpen k M G).val) := by
          rw [unitOnPullbackBasicOpen_val, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
            morphismRestrict_ι, pullbackAlongProjection_eq_consolidated418, ← CommRingCat.comp_apply,
            ← Scheme.Hom.comp_appTop, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
            Category.assoc, Category.assoc, Category.assoc, affineSpaceInl_comp_projLeft,
            Category.comp_id, hproj]
        have hw : (ConcreteCategory.hom (Scheme.Hom.appTop
              ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G))) (((unitOnPullbackBasicOpen k M G)⁻¹).val) *
            (ConcreteCategory.hom (Scheme.Hom.appTop
              ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G))) ((unitOnPullbackBasicOpen k M G).val) = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        have hRP : (ConcreteCategory.hom (Scheme.Hom.appTop
              (((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) ≫
                replaceLastCoord k M G (lastCoordinateAddInvUnit k M G)))) (lastCoordinate k M) =
            (ConcreteCategory.hom (Scheme.Hom.appTop
              ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G))) (((unitOnPullbackBasicOpen k M G)⁻¹).val) := by
          rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, replaceLastCoord_appTop_lastCoordinate,
            shiftLastCoordSection_eq_consolidated418, map_add, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
            morphismRestrict_ι, ← Category.assoc, lastCoordinate_appTop_comp_affineSpaceInl, zero_add]
        rw [hX] at hu
        rw [← lastCoordinate_eq_coord k M b, hRP]
        exact (inv_unique ((mul_comm _ _).trans hu) ((mul_comm _ _).trans hw)).symm
  have H1 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
      (ρ ≫ affineSpaceInl k M 1) (c + 1) := HasSmoothCoordCodim.comp_affineSpaceInl hsm k ρ 1 h
  have H2 := H1.resLE_open (pullbackBasicOpen k M G)
  have hres : Scheme.Hom.resLE (ρ ≫ affineSpaceInl k M 1) (pullbackBasicOpen k M G)
      ((Opens.map (ρ ≫ affineSpaceInl k M 1).base).obj (pullbackBasicOpen k M G)) le_rfl =
      ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) := by
    rw [← cancel_mono (pullbackBasicOpen k M G).ι, Scheme.Hom.resLE_comp_ι, morphismRestrict_ι]
  rw [hres] at H2
  have hφ : (asIso (shiftLastCoord k M G (lastCoordinateAddInvUnit k M G))).hom ≫
        ((pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) =
      (pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) := by
    show shiftLastCoord k M G (lastCoordinateAddInvUnit k M G) ≫
        ((pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) = _
    rw [shiftLastCoord_comp_ι_assoc, replaceLastCoord_comp_affineSpaceIndexedByToSpec]
  have H3 := H2.comp_iso_hom (asIso (shiftLastCoord k M G (lastCoordinateAddInvUnit k M G)))
    ((pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) hφ
  rw [hE] at H3
  exact hasSmoothCoordCodim_comp_opens_ι_consolidated418 (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
    (pullbackBasicOpen k M G) e hce hceo H3

theorem hasSmoothCoordCodim_basicOpenEmbedding (F : ↑(A.presheaf.obj (Opposite.op ⊤)))
    (h : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) ρ c) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + 1))))
      (basicOpenEmbedding k M ρ F ≫
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M 1) (Spec (CommRingCat.of k))).hom) (c + 1) := by
  have hF : (ConcreteCategory.hom (Scheme.Hom.appTop (ρ ≫ affineSpaceInl k M 1)))
      (pullbackAlongProjection k M (globalSectionLift k M ρ F)) = F := by
    rw [pullbackAlongProjection_eq_consolidated418, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Category.assoc,
      affineSpaceInl_comp_projLeft, Category.comp_id, appTop_globalSectionLift]
  have hV : A.basicOpen F =
      (Opens.map (ρ ≫ affineSpaceInl k M 1).base).obj (pullbackBasicOpen k M (globalSectionLift k M ρ F)) :=
    (congrArg (fun r : ↑(A.presheaf.obj (Opposite.op ⊤)) => A.basicOpen r) hF).symm.trans
      (Scheme.preimage_basicOpen (ρ ≫ affineSpaceInl k M 1)
        (pullbackAlongProjection k M (globalSectionLift k M ρ F))).symm
  have key : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
      (basicOpenEmbedding k M ρ F) (c + 1) :=
    hasSmoothCoordCodim_comp_pullbackBasicOpen_ι_consolidated418 hsm k M c ρ (globalSectionLift k M ρ F) (A.basicOpen F) hV
      (basicOpenToPullbackBasicOpen k M ρ F)
      (isClosedImmersion_basicOpenToPullbackBasicOpen k M ρ F) (isClosedImmersion_basicOpenEmbedding k M ρ F)
      (basicOpenToPullbackBasicOpen_comp_projLeft k M ρ F) (appTop_basicOpenEmbedding_lastCoordinate_mul k M ρ F) h
  exact key.comp_iso_hom (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M 1) (Spec (CommRingCat.of k)))
    (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + 1))))
    (affineSpaceIsoOfEquiv_hom_comp_toSpec k (uliftFinSumEquiv.{u} M 1))


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphChartLocalAmbientEmbedding
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section

private theorem appTop_comp_hom_apply_consolidated417 {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : ↑(Z.presheaf.obj (Opposite.op ⊤))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (f ≫ g))) s
      = (ConcreteCategory.hom (Scheme.Hom.appTop f))
        ((ConcreteCategory.hom (Scheme.Hom.appTop g)) s) := by
  have h : Scheme.Hom.appTop (f ≫ g) = Scheme.Hom.appTop g ≫ Scheme.Hom.appTop f := by
    simp [Scheme.Hom.appTop]
  rw [h]
  rfl

theorem graphMorphismToAffineSpace_comp_projLeft (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (D : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens) :
    graphMorphismToAffineSpace k M n q F D ≫ projLeft k M q = D.ι ≫ projLeft k M n := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, graphMorphismToAffineSpace_comp_affineSpaceIndexedByToSpec]
  · intro i
    obtain ⟨a⟩ := i
    show (ConcreteCategory.hom (Scheme.Hom.appTop (graphMorphismToAffineSpace k M n q F D ≫ projLeft k M q)))
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a))
        = (ConcreteCategory.hom (Scheme.Hom.appTop (D.ι ≫ projLeft k M n)))
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a))
    rw [appTop_comp_hom_apply_consolidated417, appTop_comp_hom_apply_consolidated417, projLeft_appTop_coord, projLeft_appTop_coord,
      graphMorphismToAffineSpace_appTop_coord_inl]

private theorem smooth_of_smooth_comp_isOpenImmersion_consolidated417 {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (i : Y ⟶ Z) [IsOpenImmersion i] (h : Smooth (f ≫ i)) : Smooth f := by
  have hsq : f ≫ i = 𝟙 X ≫ (f ≫ i) := by simp
  have hp : IsPullback f (𝟙 X) i (f ≫ i) := by
    refine IsPullback.of_isLimit (c := Limits.PullbackCone.mk f (𝟙 X) hsq) ?_
    refine Limits.PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_) (fun s => ?_)
      (fun s m h₁ h₂ => ?_)
    · have hc : s.fst ≫ i = (s.snd ≫ f) ≫ i := by
        rw [Category.assoc]; exact s.condition
      exact ((cancel_mono i).mp hc).symm
    · simp
    · simpa using h₂
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hp.flip h

section
variable {Z : Scheme.{u}}

private theorem ker_subschemeι_app_consolidated417 (I : Z.IdealSheafData)
    (V : Z.affineOpens) :
    RingHom.ker (Scheme.Hom.app I.subschemeι (V : Z.Opens)).hom = I.ideal V := by
  have hinj : Function.Injective ⇑((I.subschemeObjIso V).inv.hom) := by
    intro a b hab
    have h1 : ((I.subschemeObjIso V).inv ≫ (I.subschemeObjIso V).hom).hom a
        = ((I.subschemeObjIso V).inv ≫ (I.subschemeObjIso V).hom).hom b := by
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hab]
    simpa using h1
  rw [Scheme.IdealSheafData.subschemeι_app]
  ext x
  simp only [CommRingCat.hom_comp, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom]
  rw [← map_zero ((I.subschemeObjIso V).inv.hom), hinj.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

private theorem ideal_top_ofIdealTop_eq_consolidated417 [IsAffine Z]
    (J : Ideal Γ(Z, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop J).ideal ⟨⊤, isAffineOpen_top Z⟩ = J := by
  have h := (Scheme.IdealSheafData.equivOfIsAffine (X := Z)).apply_symm_apply J
  rw [Scheme.IdealSheafData.equivOfIsAffine_symm_apply,
    Scheme.IdealSheafData.equivOfIsAffine_apply] at h
  exact h

private theorem eq_of_ideal_top_eq_consolidated417 [IsAffine Z] {I J : Z.IdealSheafData}
    (h : I.ideal ⟨⊤, isAffineOpen_top Z⟩ = J.ideal ⟨⊤, isAffineOpen_top Z⟩) : I = J := by
  have hI := (Scheme.IdealSheafData.equivOfIsAffine (X := Z)).symm_apply_apply I
  have hJ := (Scheme.IdealSheafData.equivOfIsAffine (X := Z)).symm_apply_apply J
  rw [Scheme.IdealSheafData.equivOfIsAffine_apply,
    Scheme.IdealSheafData.equivOfIsAffine_symm_apply] at hI hJ
  rw [← hI, ← hJ, h]

private theorem ofIdealTop_sup_consolidated417 [IsAffine Z] (I J : Ideal Γ(Z, ⊤)) :
    Scheme.IdealSheafData.ofIdealTop (I ⊔ J) =
      Scheme.IdealSheafData.ofIdealTop I ⊔ Scheme.IdealSheafData.ofIdealTop J := by
  refine eq_of_ideal_top_eq_consolidated417 ?_
  simp only [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, ideal_top_ofIdealTop_eq_consolidated417]


end

private theorem comap_ofIdealTop_span_consolidated417 {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (s : Set Γ(Y, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop (Ideal.span s)).comap f =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop f)) '' s)) := by
  rw [Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_span]

private theorem coordSubspaceIdeal_univ_eq_ofIdealTop_consolidated417 (k : Type u) [Field k] (m : ℕ) :
    coordSubspaceIdeal k m Finset.univ =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (Set.range (fun i : Fin m =>
          AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} i)))) := by
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, Finset.coe_univ, Set.image_univ]

private theorem ker_eq_ofIdealTop_ker_appTop_consolidated417 {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [IsClosedImmersion f] :
    Scheme.Hom.ker f =
      Scheme.IdealSheafData.ofIdealTop
        (RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop f))) := by
  have : IsIso (Scheme.Hom.toImage f) := inferInstance
  have hc : Scheme.Hom.toImage f ≫ (Scheme.Hom.ker f).subschemeι = f :=
    Scheme.Hom.toImage_imageι f
  have h2 : ∀ z, (CommRingCat.Hom.hom (Scheme.Hom.appTop (inv (Scheme.Hom.toImage f))))
      ((CommRingCat.Hom.hom (Scheme.Hom.appTop (Scheme.Hom.toImage f))) z) = z := by
    intro z
    have hz := (appTop_comp_hom_apply_consolidated417 (inv (Scheme.Hom.toImage f))
      (Scheme.Hom.toImage f) z).symm
    rw [IsIso.inv_hom_id] at hz
    simpa using hz
  have hinj : Function.Injective
      ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (Scheme.Hom.toImage f))) := by
    intro a b hab
    have ha := h2 a
    rw [hab, h2 b] at ha
    exact ha.symm
  have happ : ∀ z, (CommRingCat.Hom.hom (Scheme.Hom.appTop f)) z
      = (CommRingCat.Hom.hom (Scheme.Hom.appTop (Scheme.Hom.toImage f)))
        ((CommRingCat.Hom.hom (Scheme.Hom.appTop ((Scheme.Hom.ker f).subschemeι))) z) := by
    intro z
    conv_lhs => rw [← hc]
    rw [appTop_comp_hom_apply_consolidated417]
  have hkers : RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop f)) =
      RingHom.ker (CommRingCat.Hom.hom
        (Scheme.Hom.appTop ((Scheme.Hom.ker f).subschemeι))) := by
    ext z
    simp only [RingHom.mem_ker]
    rw [happ z]
    constructor
    · intro hz
      apply hinj
      rw [hz, map_zero]
    · intro hz
      rw [hz, map_zero]
  refine eq_of_ideal_top_eq_consolidated417 ?_
  rw [ideal_top_ofIdealTop_eq_consolidated417,
    ← ker_subschemeι_app_consolidated417 (Scheme.Hom.ker f) ⟨⊤, isAffineOpen_top Y⟩]
  exact hkers.symm

private theorem coordSubspaceIdeal_univ_comap_affineSpaceIsoOfEquiv_consolidated417 (k : Type u) [Field k] (c q : ℕ) :
    (coordSubspaceIdeal k (c + q) Finset.univ).comap
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c q) (Spec (CommRingCat.of k))).hom
      = (coordSubspaceIdeal k c Finset.univ).comap (projLeft k c q)
        ⊔ (coordSubspaceIdeal k q Finset.univ).comap (projRight k c q) := by
  have h1 : ∀ i : ULift.{u, 0} (Fin (c + q)),
      (CommRingCat.Hom.hom (Scheme.Hom.appTop
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c q) (Spec (CommRingCat.of k))).hom))
          (AffineSpace.coord (Spec (CommRingCat.of k)) i)
        = AffineSpace.coord (Spec (CommRingCat.of k)) ((uliftFinSumEquiv.{u} c q).symm i) := by
    intro i
    simp [affineSpaceIsoOfEquiv]
  have h2 : ∀ a : Fin c,
      (CommRingCat.Hom.hom (Scheme.Hom.appTop (projLeft k c q)))
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a))
        = AffineSpace.coord (Spec (CommRingCat.of k))
            (ULift.up.{u, 0} (Sum.inl a) : ULift.{u, 0} (Fin c ⊕ Fin q)) := by
    intro a
    simp
  have h3 : ∀ b : Fin q,
      (CommRingCat.Hom.hom (Scheme.Hom.appTop (projRight k c q)))
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} b))
        = AffineSpace.coord (Spec (CommRingCat.of k))
            (ULift.up.{u, 0} (Sum.inr b) : ULift.{u, 0} (Fin c ⊕ Fin q)) := by
    intro b
    simp
  have hset :
      ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c q) (Spec (CommRingCat.of k))).hom)) ''
        Set.range (fun i : Fin (c + q) =>
          AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} i))
      = (⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (projLeft k c q))) ''
          Set.range (fun a : Fin c =>
            AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a)))
        ∪ (⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (projRight k c q))) ''
          Set.range (fun b : Fin q =>
            AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} b))) := by
    ext x
    simp only [Set.mem_image, Set.mem_range, Set.mem_union]
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      rw [h1]
      rcases hcase : ((uliftFinSumEquiv.{u} c q).symm (ULift.up.{u, 0} i)).down with a | b
      · refine Or.inl ⟨_, ⟨a, rfl⟩, ?_⟩
        rw [h2]
        have hEq : ULift.up.{u, 0} (Sum.inl a : Fin c ⊕ Fin q)
            = (uliftFinSumEquiv.{u} c q).symm (ULift.up.{u, 0} i) := by
          rw [← hcase]
        rw [hEq]
      · refine Or.inr ⟨_, ⟨b, rfl⟩, ?_⟩
        rw [h3]
        have hEq : ULift.up.{u, 0} (Sum.inr b : Fin c ⊕ Fin q)
            = (uliftFinSumEquiv.{u} c q).symm (ULift.up.{u, 0} i) := by
          rw [← hcase]
        rw [hEq]
    · rintro (⟨y, ⟨a, rfl⟩, rfl⟩ | ⟨y, ⟨b, rfl⟩, rfl⟩)
      · refine ⟨_, ⟨((uliftFinSumEquiv.{u} c q) (ULift.up.{u, 0} (Sum.inl a))).down, rfl⟩, ?_⟩
        rw [h1, h2]
        congr 1
        rw [ULift.up_down, Equiv.symm_apply_apply]
      · refine ⟨_, ⟨((uliftFinSumEquiv.{u} c q) (ULift.up.{u, 0} (Sum.inr b))).down, rfl⟩, ?_⟩
        rw [h1, h3]
        congr 1
        rw [ULift.up_down, Equiv.symm_apply_apply]
  rw [coordSubspaceIdeal_univ_eq_ofIdealTop_consolidated417, coordSubspaceIdeal_univ_eq_ofIdealTop_consolidated417,
    coordSubspaceIdeal_univ_eq_ofIdealTop_consolidated417, comap_ofIdealTop_span_consolidated417, comap_ofIdealTop_span_consolidated417,
    comap_ofIdealTop_span_consolidated417, ← ofIdealTop_sup_consolidated417, ← Ideal.span_union, hset]

section
variable (hsm : AffineSpaceIsSmooth.{u})
include hsm

theorem hasSmoothCoordCodim_add_of_smooth_graphMorphism (k : Type u) [Field k]
    {A A' : Scheme.{u}} [IsAffine A] [IsAffine A'] (M c n q : ℕ)
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (hρ : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) ρ c)
    (g : A' ⟶ A)
    (ρ' : A' ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))) [IsClosedImmersion ρ']
    (hcomm : ρ' ≫ projLeft k M n = g ≫ ρ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (Δ : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (hker : RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop ρ')) =
      Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appTop (projLeft k M n)))
          (RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop ρ))) ⊔
        Ideal.span (Set.range F))
    (hD : ρ' ⁻¹ᵁ ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ) = ⊤)
    (hsmooth : Smooth (graphMorphismToAffineSpace k M n q F
      ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ))) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin n))) ρ' (c + q) := by
  classical
  have hDaff : IsAffine
      (((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ).toScheme) :=
    (isAffineOpen_top (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n)))).basicOpen Δ
  have hker' : Scheme.Hom.ker ρ' =
      (Scheme.Hom.ker ρ).comap (projLeft k M n) ⊔
        Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range F)) := by
    rw [ker_eq_ofIdealTop_ker_appTop_consolidated417 ρ', hker, ofIdealTop_sup_consolidated417,
      ker_eq_ofIdealTop_ker_appTop_consolidated417 ρ, Scheme.IdealSheafData.comap_ofIdealTop]
  have hcomapEq : (coordSubspaceIdeal k q Finset.univ).comap
        (graphMorphismToAffineSpace k M n q F ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ)
          ≫ projRight k M q)
      = (Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range F))).comap
          ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ).ι := by
    have hset :
        ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop
            (graphMorphismToAffineSpace k M n q F
              ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ)
              ≫ projRight k M q))) ''
          Set.range (fun j : Fin q =>
            AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} j))
        = ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop
            ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ).ι)) ''
          Set.range F := by
      rw [← Set.range_comp, ← Set.range_comp]
      refine congrArg Set.range (funext fun j => ?_)
      show (ConcreteCategory.hom (Scheme.Hom.appTop
            (graphMorphismToAffineSpace k M n q F
              ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ)
              ≫ projRight k M q)))
            (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} j))
          = (ConcreteCategory.hom (Scheme.Hom.appTop
              ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ).ι)) (F j)
      rw [appTop_comp_hom_apply_consolidated417, projRight_appTop_coord, graphMorphismToAffineSpace_appTop_coord_inr]
    rw [coordSubspaceIdeal_univ_eq_ofIdealTop_consolidated417, comap_ofIdealTop_span_consolidated417,
      comap_ofIdealTop_span_consolidated417, hset]
  intro x
  obtain ⟨U₀, hU₀, q₀, hq₀s, hq₀o, hq₀k⟩ := hρ (g.base x)
  have := hq₀s
  have hmem1 : (projLeft k M n).base (ρ'.base x) ∈ U₀ := by
    have hb : (ρ' ≫ projLeft k M n).base x = (g ≫ ρ).base x := by rw [hcomm]
    simpa using (hb ▸ hU₀ : _)
  have hmem2 : ρ'.base x ∈
      (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ := by
    have hx : x ∈ ρ' ⁻¹ᵁ ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ) := by
      rw [hD]; trivial
    exact hx
  set U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens :=
    (projLeft k M n ⁻¹ᵁ U₀) ⊓
      ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ) with hUdef
  have hUD : U ≤ (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ := by
    rw [hUdef]; exact inf_le_right
  set G : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin q)) :=
    (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).homOfLE hUD ≫
      graphMorphismToAffineSpace k M n q F ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ)
    with hGdef
  have hGproj : G ≫ projLeft k M q = U.ι ≫ projLeft k M n := by
    rw [hGdef, Category.assoc, graphMorphismToAffineSpace_comp_projLeft, ← Category.assoc, Scheme.homOfLE_ι]
  have hsub : Set.range ⇑G.base ⊆ Set.range ⇑(projLeft k M q ⁻¹ᵁ U₀).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro y ⟨z, rfl⟩
    have hz : (G ≫ projLeft k M q).base z = (U.ι ≫ projLeft k M n).base z := by rw [hGproj]
    have hz' : (projLeft k M q).base (G.base z) = (projLeft k M n).base (U.ι.base z) := by
      simpa using hz
    show (projLeft k M q).base (G.base z) ∈ U₀
    rw [hz']
    have hzU : U.ι.base z ∈ U := z.2
    exact hzU.1
  set L : U.toScheme ⟶ (projLeft k M q ⁻¹ᵁ U₀).toScheme :=
    IsOpenImmersion.lift (projLeft k M q ⁻¹ᵁ U₀).ι G hsub with hLdef
  have hLfac : L ≫ (projLeft k M q ⁻¹ᵁ U₀).ι = G :=
    IsOpenImmersion.lift_fac _ _ hsub
  have hGsmooth : Smooth G := by
    rw [hGdef]
    have := hsmooth
    infer_instance
  have hLsmooth : Smooth L := by
    refine smooth_of_smooth_comp_isOpenImmersion_consolidated417 L (projLeft k M q ⁻¹ᵁ U₀).ι ?_
    rw [hLfac]; exact hGsmooth
  set P : (projLeft k M q ⁻¹ᵁ U₀).toScheme ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin c ⊕ Fin q)) :=
    prodMapOnPreimage k M q c U₀ q₀ with hPdef
  have hPsmooth : Smooth P := smooth_prodMapOnPreimage hsm k M q c U₀ q₀ hq₀o
  set chart : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin (c + q))) :=
    L ≫ P ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c q) (Spec (CommRingCat.of k))).hom
    with hchartdef
  refine ⟨U, ⟨hmem1, hmem2⟩, chart, ?_, ?_, ?_⟩
  · have := hLsmooth
    have := hPsmooth
    rw [hchartdef]
    infer_instance
  · rw [hchartdef, Category.assoc, Category.assoc,
      affineSpaceIsoOfEquiv_hom_comp_toSpec, hPdef, prodMapOnPreimage_comp_affineSpaceIndexedByToSpec, ← Category.assoc,
      hLfac, hGdef, Category.assoc, graphMorphismToAffineSpace_comp_affineSpaceIndexedByToSpec, ← Category.assoc, Scheme.homOfLE_ι]
  · have hA : (coordSubspaceIdeal k c Finset.univ).comap (L ≫ P ≫ projLeft k c q)
        = (Scheme.Hom.ker ρ).comap (U.ι ≫ projLeft k M n) := by
      rw [hPdef, ← morphismRestrict_projLeft_comp k M q c U₀ q₀ hq₀o,
        Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, ← hq₀k,
        restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
        ← Scheme.IdealSheafData.comap_comp, Category.assoc, morphismRestrict_ι,
        ← Category.assoc, hLfac, hGproj]
    have hB : (coordSubspaceIdeal k q Finset.univ).comap (L ≫ P ≫ projRight k c q)
        = (Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range F))).comap U.ι := by
      rw [hPdef, prodMapOnPreimage_comp_projRight, ← Category.assoc, hLfac, hGdef, Category.assoc,
        Scheme.IdealSheafData.comap_comp, hcomapEq, ← Scheme.IdealSheafData.comap_comp,
        Scheme.homOfLE_ι]
    have key : (coordSubspaceIdeal k (c + q) Finset.univ).comap chart
        = (coordSubspaceIdeal k c Finset.univ).comap (L ≫ P ≫ projLeft k c q)
          ⊔ (coordSubspaceIdeal k q Finset.univ).comap (L ≫ P ≫ projRight k c q) := by
      rw [hchartdef, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
        coordSubspaceIdeal_univ_comap_affineSpaceIsoOfEquiv_consolidated417, Scheme.IdealSheafData.comap_sup,
        Scheme.IdealSheafData.comap_sup]
      simp only [← Scheme.IdealSheafData.comap_comp]
    have key2 : restrictIdeal (Scheme.Hom.ker ρ') U
        = (Scheme.Hom.ker ρ).comap (U.ι ≫ projLeft k M n)
          ⊔ (Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range F))).comap U.ι := by
      rw [restrictIdeal_eq_comap_ι, hker', Scheme.IdealSheafData.comap_sup,
        ← Scheme.IdealSheafData.comap_comp]
    rw [key2, key, hA, hB]

theorem smoothPullbackHasLocalAmbientEmbedding_of_hasGraphChart (hgr : SmoothPullbackHasGraphChart.{u}) : SmoothPullbackHasLocalAmbientEmbedding.{u} := by
  intro k _ _ X Y A pX pY pA _ _ _ _ i _ hi M c ρ _ hρ hρc r h _ hh y
  obtain ⟨V, hyV, hVaff, A', pA', hA'aff, hA'sm, hA'ft, hA'qc, g, hgsm, hgpA, j, hjci,
    hjpb, n, q, hnqr, σ, hσci, hσcomm, F, Δ, hkerσ, hDtop, hgrsm⟩ :=
      hgr k X Y A pX pY pA i hi M ρ hρ r h hh y
  have := hA'aff
  have := hσci
  refine ⟨V, hyV, hVaff, A', pA', hA'aff, hA'sm, hA'ft, hA'qc, g, hgsm, hgpA, j, hjci, hjpb,
    n, by omega, ?_⟩
  intro N hN
  obtain ⟨p, rfl⟩ : ∃ p, N = n + p := ⟨N - n, by omega⟩
  rw [show M + (n + p) = M + n + p from by omega,
    show c + (n + p - r) = c + q + p from by omega]
  have hcc : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin n)))
      σ (c + q) :=
    hasSmoothCoordCodim_add_of_smooth_graphMorphism hsm k M c n q ρ hρc g σ hσcomm F Δ hkerσ hDtop hgrsm
  have hcc1 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + n))))
      (σ ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k))).hom)
      (c + q) :=
    HasSmoothCoordCodim.comp_iso_hom hcc
      (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + n))))
      (affineSpaceIsoOfEquiv_hom_comp_toSpec k (uliftFinSumEquiv.{u} M n))
  have : IsClosedImmersion
      (σ ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k))).hom) :=
    inferInstance
  have hpad := HasSmoothCoordCodim.comp_affineSpaceInl_affineSpaceIsoOfEquiv hsm k
      (σ ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k))).hom) p hcc1
  refine ⟨(σ ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k))).hom) ≫
      affineSpaceInl k (M + n) p ≫
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} (M + n) p) (Spec (CommRingCat.of k))).hom,
    inferInstance, ?_, hpad⟩
  have hstruct : affineSpaceInl k (M + n) p ≫
      (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} (M + n) p) (Spec (CommRingCat.of k))).hom ≫
        affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + n + p)))
      = affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + n))) := by
    rw [affineSpaceIsoOfEquiv_hom_comp_toSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec]
  simp only [Category.assoc]
  rw [hstruct, affineSpaceIsoOfEquiv_hom_comp_toSpec, ← projLeft_comp_affineSpaceIndexedByToSpec, ← Category.assoc,
    hσcomm, Category.assoc, hρ, hgpA]


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.LastCoordinateSlices
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

section

def baseFieldToGlobalSections {X : Scheme.{u}} (k : Type u) [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) : k →+* ↑(X.presheaf.obj (Opposite.op ⊤)) :=
  RingHom.comp (Scheme.Hom.appTop p).hom (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

private theorem exists_translateLastCoord_consolidated443 (k : Type u) [Field k] (M : ℕ) (a : k) :
    ∃ f : affineSpaceTimesLine k M ⟶ affineSpaceTimesLine k M,
      f ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
          affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) ∧
        (∀ b : Fin M, pullbackCoord f (⟨Sum.inl b⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)) =
          AffineSpace.coord (Spec (CommRingCat.of k))
            (⟨Sum.inl b⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))) ∧
        (ConcreteCategory.hom (Scheme.Hom.appTop f)) (lastCoordinate k M) =
          lastCoordinate k M +
            baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) a := by
  refine ⟨AffineSpace.homOfVector (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
      (fun i : ULift.{u, 0} (Fin M ⊕ Fin 1) =>
        Sum.elim
          (fun b : Fin M =>
            AffineSpace.coord (Spec (CommRingCat.of k))
              (⟨Sum.inl b⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)))
          (fun j : Fin 1 =>
            AffineSpace.coord (Spec (CommRingCat.of k))
                (⟨Sum.inr j⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)) +
              baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) a)
          i.down),
    ?_, ?_, ?_⟩
  · simp
  · intro b
    simp [pullbackCoord_def]
  · simp

def translateLastCoord (k : Type u) [Field k] (M : ℕ) (a : k) : affineSpaceTimesLine k M ⟶ affineSpaceTimesLine k M :=
  (exists_translateLastCoord_consolidated443 k M a).choose

@[simp]
theorem translateLastCoord_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (M : ℕ) (a : k) :
    translateLastCoord k M a ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) :=
  (exists_translateLastCoord_consolidated443 k M a).choose_spec.1

section
variable (k : Type u) [Field k]

theorem pullbackCoord_translateLastCoord_inl (M : ℕ) (a : k) (b : Fin M) :
    pullbackCoord (translateLastCoord k M a) (⟨Sum.inl b⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)) =
      AffineSpace.coord (Spec (CommRingCat.of k))
        (⟨Sum.inl b⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)) :=
  (exists_translateLastCoord_consolidated443 k M a).choose_spec.2.1 b

theorem translateLastCoord_appTop_lastCoordinate (M : ℕ) (a : k) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (translateLastCoord k M a))) (lastCoordinate k M) =
      lastCoordinate k M +
        baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) a :=
  (exists_translateLastCoord_consolidated443 k M a).choose_spec.2.2

private theorem baseFieldToGlobalSections_apply_consolidated443 {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (a : k) :
    baseFieldToGlobalSections k p a =
      (ConcreteCategory.hom (Scheme.Hom.appTop p))
        ((ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of k)).inv) a) :=
  rfl

private theorem appTop_baseFieldToGlobalSections_consolidated443 {X Y : Scheme.{u}}
    (f : X ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of k)) (a : k) :
    (ConcreteCategory.hom (Scheme.Hom.appTop f)) (baseFieldToGlobalSections k p a) =
      baseFieldToGlobalSections k (f ≫ p) a := by
  rw [baseFieldToGlobalSections_apply_consolidated443, baseFieldToGlobalSections_apply_consolidated443, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]






theorem translateLastCoord_comp_translateLastCoord_neg (M : ℕ) (a : k) :
    translateLastCoord k M a ≫ translateLastCoord k M (-a) = 𝟙 (affineSpaceTimesLine k M) := by
  have hstruct : ∀ b : k,
      translateLastCoord k M b ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
        affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) := translateLastCoord_comp_affineSpaceIndexedByToSpec k M
  have hconst : ∀ b c : k,
      (ConcreteCategory.hom (Scheme.Hom.appTop (translateLastCoord k M b)))
          (baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) c) =
        baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) c := by
    intro b c
    rw [appTop_baseFieldToGlobalSections_consolidated443, hstruct b]
  have H0 : (translateLastCoord k M a ≫ translateLastCoord k M (-a)) ≫
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
      𝟙 (affineSpaceTimesLine k M) ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) := by
    rw [Category.assoc, hstruct, hstruct, Category.id_comp]
  have H : ∀ i : ULift.{u, 0} (Fin M ⊕ Fin 1),
      (ConcreteCategory.hom (Scheme.Hom.appTop (translateLastCoord k M a ≫ translateLastCoord k M (-a))))
          (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
        (ConcreteCategory.hom (Scheme.Hom.appTop (𝟙 (affineSpaceTimesLine k M))))
          (AffineSpace.coord (Spec (CommRingCat.of k)) i) := by
    rintro ⟨b | j⟩
    · have h1 := pullbackCoord_translateLastCoord_inl k M a b
      have h2 := pullbackCoord_translateLastCoord_inl k M (-a) b
      rw [pullbackCoord_def] at h1 h2
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h2, h1, Scheme.Hom.id_appTop,
        CommRingCat.id_apply]
    · have h1 := translateLastCoord_appTop_lastCoordinate k M a
      have h2 := translateLastCoord_appTop_lastCoordinate k M (-a)
      rw [← lastCoordinate_eq_coord k M j, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h2,
        map_add, h1, hconst, map_neg, Scheme.Hom.id_appTop, CommRingCat.id_apply,
        add_neg_cancel_right]
  apply AffineSpace.hom_ext
  · exact H0
  · exact H

theorem translateLastCoord_neg_comp_translateLastCoord (M : ℕ) (a : k) :
    translateLastCoord k M (-a) ≫ translateLastCoord k M a = 𝟙 (affineSpaceTimesLine k M) := by
  have h := translateLastCoord_comp_translateLastCoord_neg k M (-a)
  rwa [neg_neg] at h


end

def translateLastCoordIso (k : Type u) [Field k] (M : ℕ) (a : k) : affineSpaceTimesLine k M ≅ affineSpaceTimesLine k M where
  hom := translateLastCoord k M a
  inv := translateLastCoord k M (-a)
  hom_inv_id := translateLastCoord_comp_translateLastCoord_neg k M a
  inv_hom_id := translateLastCoord_neg_comp_translateLastCoord k M a

@[simp]
theorem translateLastCoordIso_hom (k : Type u) [Field k] (M : ℕ) (a : k) :
    (translateLastCoordIso k M a).hom = translateLastCoord k M a := rfl

@[simp]
theorem translateLastCoordIso_inv (k : Type u) [Field k] (M : ℕ) (a : k) :
    (translateLastCoordIso k M a).inv = translateLastCoord k M (-a) := rfl

private theorem exists_sliceAtLastCoord_consolidated443 (k : Type u) [Field k] (M : ℕ) (a : k) :
    ∃ f : affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) ⟶ affineSpaceTimesLine k M,
      f ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
          affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) ∧
        IsClosedImmersion f ∧
        f ≫ projLeft k M 1 = 𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) ∧
        (ConcreteCategory.hom (Scheme.Hom.appTop f)) (lastCoordinate k M) =
          baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) a := by
  refine ⟨AffineSpace.homOfVector (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)))
      (fun i : ULift.{u, 0} (Fin M ⊕ Fin 1) =>
        Sum.elim
          (fun b : Fin M =>
            AffineSpace.coord (Spec (CommRingCat.of k)) (⟨b⟩ : ULift.{u, 0} (Fin M)))
          (fun _ : Fin 1 =>
            baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) a)
          i.down),
    ?_, ?_, ?_, ?_⟩
  · simp
  · refine isClosedImmersion_of_coord_surjective _ ?_ ?_
    · simp
    · rintro ⟨b⟩
      exact ⟨AffineSpace.coord (Spec (CommRingCat.of k))
        (⟨Sum.inl b⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)), by simp⟩
  · apply AffineSpace.hom_ext
    · rw [Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec]
      simp
    · rintro ⟨b⟩
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, projLeft_appTop_coord]
      simp
  · simp

def sliceAtLastCoord (k : Type u) [Field k] (M : ℕ) (a : k) :
    affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) ⟶ affineSpaceTimesLine k M :=
  (exists_sliceAtLastCoord_consolidated443 k M a).choose

@[simp]
theorem sliceAtLastCoord_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (M : ℕ) (a : k) :
    sliceAtLastCoord k M a ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) :=
  (exists_sliceAtLastCoord_consolidated443 k M a).choose_spec.1

theorem isClosedImmersion_sliceAtLastCoord (k : Type u) [Field k] (M : ℕ) (a : k) :
    IsClosedImmersion (sliceAtLastCoord k M a) :=
  (exists_sliceAtLastCoord_consolidated443 k M a).choose_spec.2.1

instance instIsClosedImmersionHeightSlice (k : Type u) [Field k] (M : ℕ) (a : k) :
    IsClosedImmersion (sliceAtLastCoord k M a) :=
  isClosedImmersion_sliceAtLastCoord k M a

@[simp]
theorem sliceAtLastCoord_comp_projLeft (k : Type u) [Field k] (M : ℕ) (a : k) :
    sliceAtLastCoord k M a ≫ projLeft k M 1 = 𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) :=
  (exists_sliceAtLastCoord_consolidated443 k M a).choose_spec.2.2.1

@[simp]
theorem sliceAtLastCoord_comp_projLeft_assoc (k : Type u) [Field k] (M : ℕ) (a : k) {Z : Scheme.{u}}
    (g : affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) ⟶ Z) :
    sliceAtLastCoord k M a ≫ projLeft k M 1 ≫ g = g := by
  rw [← Category.assoc, sliceAtLastCoord_comp_projLeft, Category.id_comp]

theorem sliceAtLastCoord_appTop_lastCoordinate (k : Type u) [Field k] (M : ℕ) (a : k) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (sliceAtLastCoord k M a))) (lastCoordinate k M) =
      baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) a :=
  (exists_sliceAtLastCoord_consolidated443 k M a).choose_spec.2.2.2

def sliceSeparatingFunction (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (e : ι → k) (i : ι) : ↑((affineSpaceTimesLine k M).presheaf.obj (Opposite.op ⊤)) :=
  ∏ j ∈ Finset.univ.erase i,
    (lastCoordinate k M -
      baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) (e j))

def sliceSeparatingOpen (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (e : ι → k) (i : ι) : (affineSpaceTimesLine k M).Opens :=
  (affineSpaceTimesLine k M).basicOpen (sliceSeparatingFunction k M e i)

def coproductSliceMap (k : Type u) [Field k] (M : ℕ) {ι : Type u} (e : ι → k) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) : (∐ A) ⟶ affineSpaceTimesLine k M :=
  Sigma.desc fun i => ρ i ≫ sliceAtLastCoord k M (e i)

@[simp]
theorem sigma_ι_coproductSliceMap (k : Type u) [Field k] (M : ℕ) {ι : Type u} (e : ι → k) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i : ι) :
    Sigma.ι A i ≫ coproductSliceMap k M e A ρ = ρ i ≫ sliceAtLastCoord k M (e i) := by
  simp [coproductSliceMap]

@[simp]
theorem sigma_ι_coproductSliceMap_assoc (k : Type u) [Field k] (M : ℕ) {ι : Type u} (e : ι → k)
    (A : ι → Scheme.{u}) (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i : ι)
    {Z : Scheme.{u}} (g : affineSpaceTimesLine k M ⟶ Z) :
    Sigma.ι A i ≫ coproductSliceMap k M e A ρ ≫ g = ρ i ≫ sliceAtLastCoord k M (e i) ≫ g := by
  rw [← Category.assoc, sigma_ι_coproductSliceMap, Category.assoc]

section
variable (k : Type u) [Field k] (M : ℕ)

private theorem sliceAtLastCoord_appTop_pullbackAlongProjection_consolidated443 (a : k)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (sliceAtLastCoord k M a))) (pullbackAlongProjection k M G) = G := by
  have hp : pullbackAlongProjection k M G =
      (ConcreteCategory.hom (Scheme.Hom.appTop (projLeft k M 1))) G := rfl
  rw [hp, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, sliceAtLastCoord_comp_projLeft,
    Scheme.Hom.id_appTop, CommRingCat.id_apply]

private theorem sliceAtLastCoord_appTop_baseFieldToGlobalSections_consolidated443 (a x : k) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (sliceAtLastCoord k M a)))
        (baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) x) =
      baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) x := by
  rw [appTop_baseFieldToGlobalSections_consolidated443, sliceAtLastCoord_comp_affineSpaceIndexedByToSpec]


end

private def lagrangeBasisSection_consolidated443 (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι]
    [DecidableEq ι] (e : ι → k) (j : ι) : ↑((affineSpaceTimesLine k M).presheaf.obj (Opposite.op ⊤)) :=
  baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
      ((∏ l ∈ Finset.univ.erase j, (e j - e l))⁻¹) *
    ∏ l ∈ Finset.univ.erase j,
      (lastCoordinate k M -
        baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) (e l))

section
variable (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι] (e : ι → k) (he : Function.Injective e)
include he

private theorem sliceAtLastCoord_appTop_lagrangeSection_consolidated443 (i j : ι) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (sliceAtLastCoord k M (e i))))
        (lagrangeBasisSection_consolidated443 k M e j) = if j = i then 1 else 0 := by
  have hlag : lagrangeBasisSection_consolidated443 k M e j =
      baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
          ((∏ l ∈ Finset.univ.erase j, (e j - e l))⁻¹) *
        ∏ l ∈ Finset.univ.erase j,
          (lastCoordinate k M -
            baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
              (e l)) := rfl
  rw [hlag, map_mul, map_prod]
  simp only [map_sub, sliceAtLastCoord_appTop_baseFieldToGlobalSections_consolidated443, sliceAtLastCoord_appTop_lastCoordinate]
  have hprod : (∏ l ∈ Finset.univ.erase j,
        (baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) (e i) -
          baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) (e l))) =
      baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)))
        (∏ l ∈ Finset.univ.erase j, (e i - e l)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun l _ => (map_sub _ _ _).symm
  rw [hprod, ← map_mul]
  by_cases hji : j = i
  · rw [if_pos hji, ← hji]
    have hne : (∏ l ∈ Finset.univ.erase j, (e j - e l)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro l hl
      exact sub_ne_zero_of_ne fun hcon => (Finset.mem_erase.mp hl).1 (he hcon).symm
    rw [inv_mul_cancel₀ hne, map_one]
  · have hz : (∏ l ∈ Finset.univ.erase j, (e i - e l)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun hc => hji hc.symm, Finset.mem_univ i⟩)
        (sub_self (e i))
    rw [if_neg hji, hz, mul_zero, map_zero]

private theorem sliceAtLastCoord_appTop_sum_mul_lagrangeSection_consolidated443 (G : ι → ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) (i : ι) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (sliceAtLastCoord k M (e i))))
        (∑ j : ι, pullbackAlongProjection k M (G j) * lagrangeBasisSection_consolidated443 k M e j) = G i := by
  rw [map_sum, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp only [map_mul, sliceAtLastCoord_appTop_pullbackAlongProjection_consolidated443,
      sliceAtLastCoord_appTop_lagrangeSection_consolidated443 k M e he i i]
    simp
  · intro j _ hj
    simp only [map_mul, sliceAtLastCoord_appTop_lagrangeSection_consolidated443 k M e he i j]
    rw [if_neg hj, mul_zero]


end

private theorem coproduct_globalSections_ext_consolidated443 (k : Type u) [Field k] {ι : Type u} (A : ι → Scheme.{u})
    (q : (∐ A) ⟶ Spec (CommRingCat.of k))
    (s t : ↑((∐ A).presheaf.obj (Opposite.op ⊤)))
    (h : ∀ i : ι, (ConcreteCategory.hom (Scheme.Hom.appTop (Sigma.ι A i))) s =
      (ConcreteCategory.hom (Scheme.Hom.appTop (Sigma.ι A i))) t) : s = t := by
  have hv : ∀ (v : ↑((∐ A).presheaf.obj (Opposite.op ⊤))) (c : ULift.{u, 0} (Fin 1)),
      (ConcreteCategory.hom (Scheme.Hom.appTop
        (AffineSpace.homOfVector q (fun _ : ULift.{u, 0} (Fin 1) => v))))
          (AffineSpace.coord (Spec (CommRingCat.of k)) c) = v := by
    intro v c
    simp
  have hfg : AffineSpace.homOfVector q (fun _ : ULift.{u, 0} (Fin 1) => s) =
      AffineSpace.homOfVector q (fun _ : ULift.{u, 0} (Fin 1) => t) := by
    refine Limits.Sigma.hom_ext _ _ fun i => ?_
    refine AffineSpace.hom_ext ?_ ?_
    · simp
    · intro c
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      rw [hv s c, hv t c]
      exact h i
  calc s = (ConcreteCategory.hom (Scheme.Hom.appTop
        (AffineSpace.homOfVector q (fun _ : ULift.{u, 0} (Fin 1) => s))))
          (AffineSpace.coord (Spec (CommRingCat.of k)) (⟨0⟩ : ULift.{u, 0} (Fin 1))) :=
        (hv s ⟨0⟩).symm
    _ = (ConcreteCategory.hom (Scheme.Hom.appTop
        (AffineSpace.homOfVector q (fun _ : ULift.{u, 0} (Fin 1) => t))))
          (AffineSpace.coord (Spec (CommRingCat.of k)) (⟨0⟩ : ULift.{u, 0} (Fin 1))) := by
        rw [hfg]
    _ = t := hv t ⟨0⟩

section
variable (k : Type u) [Field k] (M : ℕ) {ι : Type u}

theorem isClosedImmersion_coproductSliceMap [Fintype ι]
    [DecidableEq ι] (e : ι → k) (he : Function.Injective e) (A : ι → Scheme.{u})
    [∀ i, IsAffine (A i)] (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)))
    [∀ i, IsClosedImmersion (ρ i)] : IsClosedImmersion (coproductSliceMap k M e A ρ) := by
  have haffine : IsAffine (∐ A) := inferInstance
  have hsurj : ∀ F : ↑((∐ A).presheaf.obj (Opposite.op ⊤)),
      ∃ H : ↑((affineSpaceTimesLine k M).presheaf.obj (Opposite.op ⊤)),
        (ConcreteCategory.hom (Scheme.Hom.appTop (coproductSliceMap k M e A ρ))) H = F := by
    intro F
    refine ⟨∑ j : ι, pullbackAlongProjection k M (globalSectionLift k M (ρ j)
        ((ConcreteCategory.hom (Scheme.Hom.appTop (Sigma.ι A j))) F)) *
          lagrangeBasisSection_consolidated443 k M e j, ?_⟩
    refine coproduct_globalSections_ext_consolidated443 k A
      (Sigma.desc fun j => ρ j ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) _ _ fun i => ?_
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, sigma_ι_coproductSliceMap, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply,
      sliceAtLastCoord_appTop_sum_mul_lagrangeSection_consolidated443 k M e he
        (fun j => globalSectionLift k M (ρ j)
          ((ConcreteCategory.hom (Scheme.Hom.appTop (Sigma.ι A j))) F)) i,
      appTop_globalSectionLift]
  exact IsClosedImmersion.of_surjective_of_isAffine (coproductSliceMap k M e A ρ) hsurj

theorem coproductSliceMap_comp_affineSpaceIndexedByToSpec (e : ι → k)
    (A : ι → Scheme.{u}) (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)))
    (q : (∐ A) ⟶ Spec (CommRingCat.of k))
    (hq : ∀ i, Sigma.ι A i ≫ q = ρ i ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) :
    coproductSliceMap k M e A ρ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) = q := by
  refine CategoryTheory.Limits.Sigma.hom_ext _ _ fun i => ?_
  rw [sigma_ι_coproductSliceMap_assoc, sliceAtLastCoord_comp_affineSpaceIndexedByToSpec, hq i]


end

private theorem sigma_ι_base_jointly_surjective_consolidated443 {ι : Type u} (A : ι → Scheme.{u}) (x : ↥(∐ A)) :
    ∃ (j : ι) (b : ↥(A j)), (Sigma.ι A j).base b = x := by
  obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk A).surjective x
  exact ⟨i, y, (sigmaMk_mk A i y).symm⟩

private theorem coproductSliceMap_base_sigma_ι_consolidated443 (k : Type u) [Field k] (M : ℕ) {ι : Type u} (e : ι → k)
    (A : ι → Scheme.{u}) (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (j : ι)
    (b : ↥(A j)) :
    (coproductSliceMap k M e A ρ).base ((Sigma.ι A j).base b) =
      (ρ j ≫ sliceAtLastCoord k M (e j)).base b := by
  show (Sigma.ι A j ≫ coproductSliceMap k M e A ρ).base b = (ρ j ≫ sliceAtLastCoord k M (e j)).base b
  rw [sigma_ι_coproductSliceMap]

section
variable (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι] (e : ι → k)

private theorem sliceAtLastCoord_appTop_sliceSeparatingFunction_eq_prod_sub_consolidated443 (i j : ι) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (sliceAtLastCoord k M (e j)))) (sliceSeparatingFunction k M e i) =
      baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)))
        (∏ l ∈ Finset.univ.erase i, (e j - e l)) := by
  have hdef : sliceSeparatingFunction k M e i =
      ∏ l ∈ Finset.univ.erase i,
        (lastCoordinate k M -
          baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) (e l)) := rfl
  rw [hdef, map_prod, map_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [map_sub, map_sub, sliceAtLastCoord_appTop_lastCoordinate, appTop_baseFieldToGlobalSections_consolidated443,
    sliceAtLastCoord_comp_affineSpaceIndexedByToSpec]

private theorem comp_sliceAtLastCoord_appTop_sliceSeparatingFunction_consolidated443 (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i j : ι) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (ρ j ≫ sliceAtLastCoord k M (e j))))
        (sliceSeparatingFunction k M e i) =
      baseFieldToGlobalSections k (ρ j ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)))
        (∏ l ∈ Finset.univ.erase i, (e j - e l)) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, sliceAtLastCoord_appTop_sliceSeparatingFunction_eq_prod_sub_consolidated443,
    appTop_baseFieldToGlobalSections_consolidated443]

private theorem mem_sliceSeparatingOpen_consolidated443 (he : Function.Injective e) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i : ι) (b : ↥(A i)) :
    (ρ i ≫ sliceAtLastCoord k M (e i)).base b ∈ sliceSeparatingOpen k M e i := by
  have hne0 : (∏ l ∈ Finset.univ.erase i, (e i - e l)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro l hl
    exact sub_ne_zero.2 fun hx => (Finset.mem_erase.1 hl).1 (he hx).symm
  have hunit : IsUnit ((ConcreteCategory.hom (Scheme.Hom.appTop (ρ i ≫ sliceAtLastCoord k M (e i))))
      (sliceSeparatingFunction k M e i)) := by
    rw [comp_sliceAtLastCoord_appTop_sliceSeparatingFunction_consolidated443]
    exact IsUnit.map _ (isUnit_iff_ne_zero.2 hne0)
  have hbasic : (Opens.map (ρ i ≫ sliceAtLastCoord k M (e i)).base).obj (sliceSeparatingOpen k M e i) =
      (A i).basicOpen ((ConcreteCategory.hom (Scheme.Hom.appTop
        (ρ i ≫ sliceAtLastCoord k M (e i)))) (sliceSeparatingFunction k M e i)) :=
    Scheme.preimage_basicOpen _ _
  have hpre : (Opens.map (ρ i ≫ sliceAtLastCoord k M (e i)).base).obj (sliceSeparatingOpen k M e i) = ⊤ := by
    rw [hbasic]
    exact (A i).basicOpen_of_isUnit hunit
  have hmem : b ∈ (Opens.map (ρ i ≫ sliceAtLastCoord k M (e i)).base).obj (sliceSeparatingOpen k M e i) := by
    rw [hpre]; trivial
  exact hmem

private theorem not_mem_sliceSeparatingOpen_of_ne_consolidated443 (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i j : ι) (hne : j ≠ i)
    (b : ↥(A j)) :
    (ρ j ≫ sliceAtLastCoord k M (e j)).base b ∉ sliceSeparatingOpen k M e i := by
  have hzero : (∏ l ∈ Finset.univ.erase i, (e j - e l)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hne, Finset.mem_univ j⟩) (sub_self _)
  have hbasic : (Opens.map (ρ j ≫ sliceAtLastCoord k M (e j)).base).obj (sliceSeparatingOpen k M e i) =
      (A j).basicOpen ((ConcreteCategory.hom (Scheme.Hom.appTop
        (ρ j ≫ sliceAtLastCoord k M (e j)))) (sliceSeparatingFunction k M e i)) :=
    Scheme.preimage_basicOpen _ _
  have hpre : (Opens.map (ρ j ≫ sliceAtLastCoord k M (e j)).base).obj (sliceSeparatingOpen k M e i) = ⊥ := by
    rw [hbasic, comp_sliceAtLastCoord_appTop_sliceSeparatingFunction_consolidated443, hzero, map_zero, Scheme.basicOpen_zero]
  intro hmem
  have hmem' : b ∈ (Opens.map (ρ j ≫ sliceAtLastCoord k M (e j)).base).obj (sliceSeparatingOpen k M e i) :=
    hmem
  rw [hpre] at hmem'
  simp at hmem'


end

section
variable (k : Type u) [Field k] (M : ℕ)

private theorem quasiCompact_coproductSliceMap_consolidated443 {ι : Type u} [Fintype ι]
    (e : ι → k) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [∀ i, IsClosedImmersion (ρ i)] :
    QuasiCompact (coproductSliceMap k M e A ρ) := by
  have hqcj : ∀ j, QuasiCompact (ρ j ≫ sliceAtLastCoord k M (e j)) := fun j => inferInstance
  refine ⟨fun V hV1 hV2 => ?_⟩
  have hset : ⇑(coproductSliceMap k M e A ρ).base ⁻¹' V =
      ⋃ j, ⇑(Sigma.ι A j).base '' (⇑(ρ j ≫ sliceAtLastCoord k M (e j)).base ⁻¹' V) := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨j, b, rfl⟩ := sigma_ι_base_jointly_surjective_consolidated443 A y
      refine Set.mem_iUnion.2 ⟨j, b, ?_, rfl⟩
      show (ρ j ≫ sliceAtLastCoord k M (e j)).base b ∈ V
      rw [← coproductSliceMap_base_sigma_ι_consolidated443 k M e A ρ j b]
      exact hy
    · intro y hy
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hy
      obtain ⟨b, hb, rfl⟩ := hj
      show (coproductSliceMap k M e A ρ).base ((Sigma.ι A j).base b) ∈ V
      rw [coproductSliceMap_base_sigma_ι_consolidated443]
      exact hb
  rw [hset]
  refine isCompact_iUnion fun j => ?_
  exact (QuasiCompact.isCompact_preimage (f := ρ j ≫ sliceAtLastCoord k M (e j)) V hV1 hV2).image
    (Sigma.ι A j).continuous

private theorem comap_ker_coproductSliceMap_eq_of_le_sliceSeparatingOpen_consolidated443 {ι : Type u}
    [Fintype ι] [DecidableEq ι] (e : ι → k) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [∀ i, IsClosedImmersion (ρ i)]
    (i : ι) (U : (affineSpaceTimesLine k M).Opens) (hU : U ≤ sliceSeparatingOpen k M e i) :
    (Scheme.Hom.ker (coproductSliceMap k M e A ρ)).comap U.ι =
      (Scheme.Hom.ker (ρ i ≫ sliceAtLastCoord k M (e i))).comap U.ι := by
  have : QuasiCompact (coproductSliceMap k M e A ρ) := quasiCompact_coproductSliceMap_consolidated443 k M e A ρ
  have : QuasiCompact (ρ i ≫ sliceAtLastCoord k M (e i)) := inferInstance
  have hfun : ⇑(Scheme.Opens.ι (X := A i)
        ((Opens.map (ρ i ≫ sliceAtLastCoord k M (e i)).base).obj U) ≫ Sigma.ι A i).base =
      ⇑(Sigma.ι A i).base ∘
        ⇑(Scheme.Opens.ι (X := A i)
          ((Opens.map (ρ i ≫ sliceAtLastCoord k M (e i)).base).obj U)).base :=
    funext fun _ => rfl
  have hrange :
      Set.range ⇑(Scheme.Opens.ι (X := A i)
          ((Opens.map (ρ i ≫ sliceAtLastCoord k M (e i)).base).obj U) ≫ Sigma.ι A i).base =
        Set.range ⇑(Scheme.Opens.ι (X := ∐ A)
          ((Opens.map (coproductSliceMap k M e A ρ).base).obj U)).base := by
    rw [hfun, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    show ⇑(Sigma.ι A i).base '' (⇑(ρ i ≫ sliceAtLastCoord k M (e i)).base ⁻¹'
        (U : Set ↥(affineSpaceTimesLine k M))) =
      ⇑(coproductSliceMap k M e A ρ).base ⁻¹' (U : Set ↥(affineSpaceTimesLine k M))
    apply Set.Subset.antisymm
    · rintro _ ⟨b, hb, rfl⟩
      show (coproductSliceMap k M e A ρ).base ((Sigma.ι A i).base b) ∈ (U : Set ↥(affineSpaceTimesLine k M))
      rw [coproductSliceMap_base_sigma_ι_consolidated443]
      exact hb
    · intro y hy
      obtain ⟨j, b, rfl⟩ := sigma_ι_base_jointly_surjective_consolidated443 A y
      have hb : (ρ j ≫ sliceAtLastCoord k M (e j)).base b ∈ (U : Set ↥(affineSpaceTimesLine k M)) := by
        have hy' : (coproductSliceMap k M e A ρ).base ((Sigma.ι A j).base b) ∈
            (U : Set ↥(affineSpaceTimesLine k M)) := hy
        rwa [coproductSliceMap_base_sigma_ι_consolidated443] at hy'
      rcases eq_or_ne j i with rfl | hne
      · exact ⟨b, hb, rfl⟩
      · exact absurd (hU hb) (not_mem_sliceSeparatingOpen_of_ne_consolidated443 k M e A ρ i j hne b)
  refine (ker_comap_ι_eq_ker_of_isIso_comp (coproductSliceMap k M e A ρ) U
      ((ρ i ≫ sliceAtLastCoord k M (e i)) ∣_ U)
      (IsOpenImmersion.isoOfRangeEq _ _ hrange).hom ?_).trans
    (ker_comap_ι_eq_ker_morphismRestrict (ρ i ≫ sliceAtLastCoord k M (e i)) U).symm
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
    IsOpenImmersion.isoOfRangeEq_hom_fac, Category.assoc, sigma_ι_coproductSliceMap, morphismRestrict_ι]

private theorem sliceAtLastCoord_eq_affineSpaceInl_comp_translateLastCoord_consolidated443 (a : k) :
    sliceAtLastCoord k M a = affineSpaceInl k M 1 ≫ translateLastCoord k M a := by
  apply AffineSpace.hom_ext
  · rw [Category.assoc, translateLastCoord_comp_affineSpaceIndexedByToSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec, sliceAtLastCoord_comp_affineSpaceIndexedByToSpec]
  · rintro ⟨b | j⟩
    · have h0 := sliceAtLastCoord_comp_projLeft k M a
      have h1 := congrArg
        (fun m : affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) ⟶
            affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) =>
          (ConcreteCategory.hom (Scheme.Hom.appTop m))
            (AffineSpace.coord (Spec (CommRingCat.of k)) (⟨b⟩ : ULift.{u, 0} (Fin M)))) h0
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, projLeft_appTop_coord,
        Scheme.Hom.id_appTop, CommRingCat.id_apply] at h1
      rw [h1, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      have h2 := pullbackCoord_translateLastCoord_inl k M a b
      rw [pullbackCoord_def] at h2
      rw [h2]
      have h3 := pullbackCoord_affineSpaceInl_inl k M 1 b
      rw [pullbackCoord_def] at h3
      rw [h3]
    · rw [← lastCoordinate_eq_coord k M j, sliceAtLastCoord_appTop_lastCoordinate, Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply, translateLastCoord_appTop_lastCoordinate, map_add, appTop_baseFieldToGlobalSections_consolidated443,
        affineSpaceInl_comp_affineSpaceIndexedByToSpec]
      have h4 := pullbackCoord_affineSpaceInl_inr k M 1 (0 : Fin 1)
      rw [pullbackCoord_def] at h4
      rw [lastCoordinate_eq, h4, zero_add]


end

section
variable (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] (M c : ℕ)
include hsm

private theorem hasSmoothCoordCodim_comp_sliceAtLastCoord_consolidated443 (a : k) {B : Scheme.{u}}
    (σ : B ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion σ]
    (hσ : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) σ c) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
      (σ ≫ sliceAtLastCoord k M a) (c + 1) := by
  have h1 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
      (σ ≫ affineSpaceInl k M 1) (c + 1) := HasSmoothCoordCodim.comp_affineSpaceInl hsm k σ 1 hσ
  have h2 := h1.comp_iso_hom (translateLastCoordIso k M a)
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) (by simp)
  rw [sliceAtLastCoord_eq_affineSpaceInl_comp_translateLastCoord_consolidated443, ← Category.assoc]
  exact h2

theorem hasSmoothCoordCodim_coproductSliceMap {ι : Type u} [Fintype ι] [DecidableEq ι] (e : ι → k) (he : Function.Injective e)
    (A : ι → Scheme.{u}) [∀ i, IsAffine (A i)]
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [∀ i, IsClosedImmersion (ρ i)]
    (h : ∀ i, HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) (ρ i) c) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
      (coproductSliceMap k M e A ρ) (c + 1) := by
  rw [hasSmoothCoordCodim_iff]
  intro x
  obtain ⟨i, a, rfl⟩ := sigma_ι_base_jointly_surjective_consolidated443 A x
  have hpiece := hasSmoothCoordCodim_comp_sliceAtLastCoord_consolidated443 hsm k M c (e i) (ρ i) (h i)
  rw [hasSmoothCoordCodim_iff] at hpiece
  obtain ⟨W, hW, q, hqS, hqstruct, hkerW⟩ := hpiece a
  have : Smooth q := hqS
  refine ⟨W ⊓ sliceSeparatingOpen k M e i, ?_,
    (affineSpaceTimesLine k M).homOfLE (inf_le_left) ≫ q, inferInstance, ?_, ?_⟩
  · show (coproductSliceMap k M e A ρ).base ((Sigma.ι A i).base a) ∈ W ⊓ sliceSeparatingOpen k M e i
    rw [coproductSliceMap_base_sigma_ι_consolidated443]
    exact ⟨hW, mem_sliceSeparatingOpen_consolidated443 k M e he A ρ i a⟩
  · rw [Category.assoc, hqstruct, ← Category.assoc, Scheme.homOfLE_ι]
  · have hcrux := comap_ker_coproductSliceMap_eq_of_le_sliceSeparatingOpen_consolidated443 k M e A ρ i (W ⊓ sliceSeparatingOpen k M e i)
      inf_le_right
    rw [Scheme.IdealSheafData.comap_comp, ← hkerW, restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι,
      ← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]
    exact hcrux


end

def componentSliceOpen (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (e : ι → k) (A : ι → Scheme.{u}) (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)))
    (i : ι) : (∐ A).Opens :=
  (Opens.map (coproductSliceMap k M e A ρ).base).obj (sliceSeparatingOpen k M e i)

section
variable (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι] (e : ι → k)

private theorem sigma_ι_comp_coproductSliceMap_appTop_sliceSeparatingFunction_consolidated443 (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i j : ι) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (Sigma.ι A j ≫ coproductSliceMap k M e A ρ)))
        (sliceSeparatingFunction k M e i) =
      baseFieldToGlobalSections k (ρ j ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)))
        (∏ l ∈ Finset.univ.erase i, (e j - e l)) := by
  rw [sigma_ι_coproductSliceMap]
  exact comp_sliceAtLastCoord_appTop_sliceSeparatingFunction_consolidated443 k M e A ρ i j

private theorem preimage_sliceSeparatingOpen_self_consolidated443 (he : Function.Injective e) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i : ι) :
    (Opens.map (Sigma.ι A i ≫ coproductSliceMap k M e A ρ).base).obj (sliceSeparatingOpen k M e i) = ⊤ := by
  have hpre : (Opens.map (Sigma.ι A i ≫ coproductSliceMap k M e A ρ).base).obj (sliceSeparatingOpen k M e i) =
      (A i).basicOpen ((ConcreteCategory.hom (Scheme.Hom.appTop
        (Sigma.ι A i ≫ coproductSliceMap k M e A ρ))) (sliceSeparatingFunction k M e i)) :=
    Scheme.preimage_basicOpen _ _
  rw [hpre, sigma_ι_comp_coproductSliceMap_appTop_sliceSeparatingFunction_consolidated443 k M e A ρ i i]
  have hne : (∏ l ∈ Finset.univ.erase i, (e i - e l)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun l hl => ?_
    exact sub_ne_zero_of_ne fun hcon => (Finset.mem_erase.mp hl).1 (he hcon).symm
  apply Scheme.basicOpen_of_isUnit
  exact IsUnit.map (baseFieldToGlobalSections k (ρ i ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))))
    (isUnit_iff_ne_zero.mpr hne)

private theorem preimage_sliceSeparatingOpen_of_ne_consolidated443 (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i j : ι) (hij : j ≠ i) :
    (Opens.map (Sigma.ι A j ≫ coproductSliceMap k M e A ρ).base).obj (sliceSeparatingOpen k M e i) = ⊥ := by
  have hpre : (Opens.map (Sigma.ι A j ≫ coproductSliceMap k M e A ρ).base).obj (sliceSeparatingOpen k M e i) =
      (A j).basicOpen ((ConcreteCategory.hom (Scheme.Hom.appTop
        (Sigma.ι A j ≫ coproductSliceMap k M e A ρ))) (sliceSeparatingFunction k M e i)) :=
    Scheme.preimage_basicOpen _ _
  have hzero : (∏ l ∈ Finset.univ.erase i, (e j - e l)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩) (sub_self (e j))
  rw [hpre, sigma_ι_comp_coproductSliceMap_appTop_sliceSeparatingFunction_consolidated443 k M e A ρ i j, hzero, map_zero]
  simp


end

section
variable (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι] (e : ι → k) (he : Function.Injective e) (A : ι → Scheme.{u}) (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i : ι)
include he

private theorem range_sigma_ι_eq_range_componentSliceOpen_ι_consolidated443 :
    Set.range (Sigma.ι A i).base = Set.range (componentSliceOpen k M e A ρ i).ι.base := by
  rw [Scheme.Opens.range_ι]
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨y, rfl⟩
    have hy : y ∈ (Opens.map (Sigma.ι A i ≫ coproductSliceMap k M e A ρ).base).obj
        (sliceSeparatingOpen k M e i) := by
      rw [preimage_sliceSeparatingOpen_self_consolidated443 k M e he A ρ i]
      simp
    exact hy
  · intro x hx
    obtain ⟨j, y, rfl⟩ := sigma_ι_base_jointly_surjective_consolidated443 A x
    by_cases hij : j = i
    · subst hij
      exact Set.mem_range_self y
    · exfalso
      have hy : y ∈ (Opens.map (Sigma.ι A j ≫ coproductSliceMap k M e A ρ).base).obj
          (sliceSeparatingOpen k M e i) := hx
      rw [preimage_sliceSeparatingOpen_of_ne_consolidated443 k M e A ρ i j hij] at hy
      have hy' : y ∈ ((⊥ : (A j).Opens) : Set ↥(A j)) := hy
      rw [TopologicalSpace.Opens.coe_bot] at hy'
      exact (Set.mem_empty_iff_false y).mp hy'

private theorem exists_iso_componentSliceOpen_consolidated443 :
    ∃ φ : A i ≅ (↑(componentSliceOpen k M e A ρ i) : Scheme.{u}),
      φ.hom ≫ (componentSliceOpen k M e A ρ i).ι = Sigma.ι A i := by
  have hrange := range_sigma_ι_eq_range_componentSliceOpen_ι_consolidated443 k M e he A ρ i
  refine ⟨IsOpenImmersion.isoOfRangeEq (Sigma.ι A i) (componentSliceOpen k M e A ρ i).ι hrange, ?_⟩
  apply IsOpenImmersion.isoOfRangeEq_hom_fac


end

def componentIsoSliceOpen (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (e : ι → k) (he : Function.Injective e) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i : ι) :
    A i ≅ (↑(componentSliceOpen k M e A ρ i) : Scheme.{u}) :=
  (exists_iso_componentSliceOpen_consolidated443 k M e he A ρ i).choose

@[simp]
theorem componentIsoSliceOpen_hom_comp_ι (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι]
    [DecidableEq ι] (e : ι → k) (he : Function.Injective e) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i : ι) :
    (componentIsoSliceOpen k M e he A ρ i).hom ≫ (componentSliceOpen k M e A ρ i).ι = Sigma.ι A i :=
  (exists_iso_componentSliceOpen_consolidated443 k M e he A ρ i).choose_spec

@[simp]
theorem componentIsoSliceOpen_hom_comp_ι_assoc (k : Type u) [Field k] (M : ℕ) {ι : Type u} [Fintype ι]
    [DecidableEq ι] (e : ι → k) (he : Function.Injective e) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) (i : ι) {Z : Scheme.{u}}
    (g : (∐ A) ⟶ Z) :
    (componentIsoSliceOpen k M e he A ρ i).hom ≫ (componentSliceOpen k M e A ρ i).ι ≫ g =
      Sigma.ι A i ≫ g := by
  rw [← Category.assoc, componentIsoSliceOpen_hom_comp_ι]

abbrev coproductSliceMapReindexed (k : Type u) [Field k] (M : ℕ) {ι : Type u} (e : ι → k) (A : ι → Scheme.{u})
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) :
    (∐ A) ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin (M + 1))) :=
  coproductSliceMap k M e A ρ ≫
    (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M 1) (Spec (CommRingCat.of k))).hom

theorem coproductSliceMapReindexed_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (M : ℕ) {ι : Type u} (e : ι → k)
    (A : ι → Scheme.{u}) (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)))
    (q : (∐ A) ⟶ Spec (CommRingCat.of k))
    (hq : ∀ i, Sigma.ι A i ≫ q = ρ i ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) :
    coproductSliceMapReindexed k M e A ρ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + 1))) = q := by
  rw [Category.assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec]
  exact coproductSliceMap_comp_affineSpaceIndexedByToSpec k M e A ρ q hq

theorem hasSmoothCoordCodim_coproductSliceMapReindexed (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k]
    (M c : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι] (e : ι → k) (he : Function.Injective e)
    (A : ι → Scheme.{u}) [∀ i, IsAffine (A i)]
    (ρ : ∀ i, A i ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [∀ i, IsClosedImmersion (ρ i)]
    (h : ∀ i, HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) (ρ i) c) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + 1))))
      (coproductSliceMapReindexed k M e A ρ) (c + 1) := by
  have : IsClosedImmersion (coproductSliceMap k M e A ρ) := isClosedImmersion_coproductSliceMap k M e he A ρ
  exact (hasSmoothCoordCodim_coproductSliceMap hsm k M c e he A ρ h).comp_iso_hom
    (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M 1) (Spec (CommRingCat.of k)))
    (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + 1))))
    (affineSpaceIsoOfEquiv_hom_comp_toSpec k (uliftFinSumEquiv.{u} M 1))


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PresentedLocalChart
section

open CategoryTheory AlgebraicGeometry

section

structure PresentedLocalChart {k : Type u} [Field k] [CharZero k] {Y V : Scheme.{u}}
    {pY : Y ⟶ Spec (CommRingCat.of k)} {pV : V ⟶ Spec (CommRingCat.of k)}
    {G : EmbeddingDatum k Y pY} (P : ClosedEmbeddingIntoAffineSpace G) (H : EmbeddingDatum k V pV)
    (u : V ⟶ Y) (r : ℕ) (y : ↥V) extends SmoothLocalChart G H u y where
  threshold : ℕ
  presentation : ∀ N : ℕ, threshold ≤ N →
    ∃ σ : ambient ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N + 1))),
      IsClosedImmersion σ ∧
      σ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (P.dim + N + 1))) = ambientStruct ∧
      HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (P.dim + N + 1)))) σ
        (P.codimBound + (N - r) + 1)
  le_threshold : r ≤ threshold

theorem nonempty_presentedLocalChart (hS : SmoothPullbackHasLocalAmbientEmbedding.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    [IsAffine Y] [IsAffine V]
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    (G : EmbeddingDatum k Y pY) (P : ClosedEmbeddingIntoAffineSpace G) (H : EmbeddingDatum k V pV)
    (u : V ⟶ Y) (r : ℕ) [SmoothOfRelativeDimension r u]
    (hu : u ≫ pY = pV) (y : ↥V) :
    Nonempty (PresentedLocalChart P H u r y) := by
  classical
  obtain ⟨V₀, hyV₀, hV₀aff, A', pA', hA'aff, hA'sm, hA'ft, hA'qc, gg, hgsm, hgp, jj, hjci,
      hjpb, N₀, hrN₀, hpres⟩ :=
    hS k Y V G.ambient pY pV G.ambientStruct G.emb G.comp_eq P.dim P.codimBound P.toAffine
      P.toAffine_comp P.locallyConstCodim r u hu y
  have := hA'aff
  have := hA'sm
  have := hA'ft
  have := hA'qc
  have := hgsm
  have := hjci
  obtain ⟨σ₀, hσ₀ci, hσ₀comp, hσ₀codim⟩ := hpres N₀ le_rfl
  have := hσ₀ci
  have hembCI : IsClosedImmersion H.emb := H.isClosedImmersion_emb
  have hind := H.emb.isClosedEmbedding.toIsEmbedding.toIsInducing
  obtain ⟨Ω, hΩ, hΩeq⟩ := hind.isOpen_iff.mp V₀.isOpen
  have hyΩ : H.emb.base y ∈ Ω := by
    have h0 : y ∈ ⇑H.emb.base ⁻¹' Ω := by rw [hΩeq]; exact hyV₀
    exact h0
  obtain ⟨Ubase, hUmem, hyU, hUΩ⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen H.ambient)
      (U := (⟨Ω, hΩ⟩ : H.ambient.Opens)) (x := H.emb.base y) hyΩ
  obtain ⟨func, rfl⟩ := hUmem
  have hymem : y ∈ (H.emb ⁻¹ᵁ H.ambient.basicOpen func) := hyU
  have hsub : (H.emb ⁻¹ᵁ H.ambient.basicOpen func) ≤ V₀ := by
    intro x hx
    have hx1 : H.emb.base x ∈ H.ambient.basicOpen func := hx
    have hx2 : x ∈ ⇑H.emb.base ⁻¹' Ω := hUΩ hx1
    rw [hΩeq] at hx2
    exact hx2
  obtain ⟨L, hL⟩ : ∃ L : Γ(affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N₀))), ⊤),
      (ConcreteCategory.hom (Scheme.Hom.appTop (jj ≫ σ₀))) L
        = (ConcreteCategory.hom (Scheme.Hom.appTop (V₀.ι ≫ H.emb))) func :=
    ⟨_, appTop_globalSectionLift k (P.dim + N₀) (jj ≫ σ₀) _⟩
  obtain ⟨Fsec, hopen⟩ : ∃ Fsec : Γ(A', ⊤),
      jj ⁻¹ᵁ (A'.basicOpen Fsec) = V₀.ι ⁻¹ᵁ (H.emb ⁻¹ᵁ H.ambient.basicOpen func) := by
    refine ⟨(ConcreteCategory.hom (Scheme.Hom.appTop σ₀)) L, ?_⟩
    have eA : A'.basicOpen ((ConcreteCategory.hom (Scheme.Hom.appTop σ₀)) L)
        = σ₀ ⁻¹ᵁ ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N₀)))).basicOpen L) :=
      (Scheme.preimage_basicOpen σ₀ L).symm
    have e1 : jj ⁻¹ᵁ
          (σ₀ ⁻¹ᵁ ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N₀)))).basicOpen L))
        = (jj ≫ σ₀) ⁻¹ᵁ
          ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N₀)))).basicOpen L) := rfl
    have eB : (jj ≫ σ₀) ⁻¹ᵁ
          ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N₀)))).basicOpen L)
        = (↑V₀ : Scheme.{u}).basicOpen
            ((ConcreteCategory.hom (Scheme.Hom.appTop (jj ≫ σ₀))) L) :=
      Scheme.preimage_basicOpen _ _
    have e2 : V₀.ι ⁻¹ᵁ (H.emb ⁻¹ᵁ H.ambient.basicOpen func)
        = (V₀.ι ≫ H.emb) ⁻¹ᵁ (H.ambient.basicOpen func) := rfl
    have eC : (V₀.ι ≫ H.emb) ⁻¹ᵁ (H.ambient.basicOpen func)
        = (↑V₀ : Scheme.{u}).basicOpen
            ((ConcreteCategory.hom (Scheme.Hom.appTop (V₀.ι ≫ H.emb))) func) :=
      Scheme.preimage_basicOpen _ _
    rw [eA, e1, eB, hL, e2, eC]
  obtain ⟨θ, hθ⟩ : ∃ θ : (H.emb ⁻¹ᵁ H.ambient.basicOpen func).toScheme ≅
      (jj ⁻¹ᵁ A'.basicOpen Fsec).toScheme,
      θ.hom ≫ ((jj ⁻¹ᵁ A'.basicOpen Fsec).ι ≫ V₀.ι)
        = (H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι := by
    have hrange : Set.range ⇑(H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι.base
        = Set.range ⇑((jj ⁻¹ᵁ A'.basicOpen Fsec).ι ≫ V₀.ι).base := by
      have hcomp : Set.range ⇑((jj ⁻¹ᵁ A'.basicOpen Fsec).ι ≫ V₀.ι).base
          = ⇑V₀.ι.base '' Set.range ⇑(jj ⁻¹ᵁ A'.basicOpen Fsec).ι.base := by
        simp [Set.range_comp]
      rw [hcomp, hopen, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      have h4 : (↑(V₀.ι ⁻¹ᵁ (H.emb ⁻¹ᵁ H.ambient.basicOpen func)) : Set ↥V₀.toScheme)
          = ⇑V₀.ι.base ⁻¹' (↑(H.emb ⁻¹ᵁ H.ambient.basicOpen func) : Set ↥V) := rfl
      rw [h4, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
      exact (Set.inter_eq_self_of_subset_left (fun x hx => hsub hx)).symm
    exact ⟨AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq _ _ hrange,
      AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange⟩
  have hθ' : (θ.hom ≫ (jj ⁻¹ᵁ A'.basicOpen Fsec).ι) ≫ V₀.ι
      = (H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι := by
    rw [Category.assoc]; exact hθ
  have hpb1 : CategoryTheory.IsPullback
      (AlgebraicGeometry.morphismRestrict jj (A'.basicOpen Fsec))
      ((jj ⁻¹ᵁ A'.basicOpen Fsec).ι ≫ (V₀.ι ≫ u)) ((A'.basicOpen Fsec).ι ≫ gg) G.emb :=
    (AlgebraicGeometry.isPullback_morphismRestrict jj (A'.basicOpen Fsec)).paste_vert hjpb
  have hcomm : CategoryTheory.CommSq θ.hom
      ((H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι ≫ u)
      ((jj ⁻¹ᵁ A'.basicOpen Fsec).ι ≫ (V₀.ι ≫ u)) (𝟙 Y) := by
    constructor
    rw [Category.comp_id, ← Category.assoc, ← Category.assoc, hθ']
  have hiso : CategoryTheory.IsPullback θ.hom
      ((H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι ≫ u)
      ((jj ⁻¹ᵁ A'.basicOpen Fsec).ι ≫ (V₀.ι ≫ u)) (𝟙 Y) :=
    CategoryTheory.IsPullback.of_horiz_isIso hcomm
  have hpb : CategoryTheory.IsPullback
      (θ.hom ≫ AlgebraicGeometry.morphismRestrict jj (A'.basicOpen Fsec))
      ((H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι ≫ u)
      ((A'.basicOpen Fsec).ι ≫ gg) G.emb := by
    have h5 := hiso.paste_horiz hpb1
    rwa [Category.id_comp] at h5
  have hambaff : IsAffine (A'.basicOpen Fsec).toScheme :=
    (AlgebraicGeometry.isAffineOpen_top A').basicOpen Fsec
  refine ⟨{
    func := func
    mem_domain := hymem
    ambient := (A'.basicOpen Fsec).toScheme
    ambientStruct := (A'.basicOpen Fsec).ι ≫ pA'
    isAffine_ambient := hambaff
    smooth_ambientStruct := by infer_instance
    locallyOfFiniteType_ambientStruct := by infer_instance
    quasiCompact_ambientStruct := by infer_instance
    toAmbient := (A'.basicOpen Fsec).ι ≫ gg
    smooth_toAmbient := by infer_instance
    comp_eq := by rw [Category.assoc, hgp]
    imm := θ.hom ≫ AlgebraicGeometry.morphismRestrict jj (A'.basicOpen Fsec)
    isClosedImmersion_imm := by
      have : IsClosedImmersion
          (AlgebraicGeometry.morphismRestrict jj (A'.basicOpen Fsec)) := by infer_instance
      infer_instance
    isPullback := hpb
    threshold := N₀
    le_threshold := hrN₀
    presentation := by
      intro N hN
      obtain ⟨σ, hσci, hσcomp, hσcodim⟩ := hpres N hN
      have := hσci
      refine ⟨basicOpenEmbedding k (P.dim + N) σ Fsec ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} (P.dim + N) 1)
            (Spec (CommRingCat.of k))).hom, by infer_instance, ?_, ?_⟩
      · rw [Category.assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec]
        exact basicOpenEmbedding_comp_affineSpaceIndexedByToSpec k (P.dim + N) σ Fsec pA' hσcomp
      · exact hasSmoothCoordCodim_basicOpenEmbedding hsm k (P.dim + N)
          (P.codimBound + (N - r)) σ Fsec hσcodim }⟩


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EtaleCoverClosedEmbedding
section

open CategoryTheory AlgebraicGeometry

section

private theorem isZariskiLocalAtSource_locallyOfFiniteType_consolidated456 :
    IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) := by
  have hrh : HasRingHomProperty (@LocallyOfFiniteType.{u}) RingHom.FiniteType := inferInstance
  exact @HasRingHomProperty.instIsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) _ hrh

private theorem isZariskiLocalAtSource_flat_consolidated456 :
    IsZariskiLocalAtSource (@Flat.{u}) := by
  have hrh : HasRingHomProperty (@Flat.{u}) RingHom.Flat := inferInstance
  exact @HasRingHomProperty.instIsZariskiLocalAtSource (@Flat.{u}) _ hrh

section
variable {ι : Type u} {X : ι → Scheme.{u}} {Z : Scheme.{u}} (f : ∀ i, X i ⟶ Z)

private theorem locallyOfFiniteType_sigmaDesc_consolidated456 (hf : ∀ i, LocallyOfFiniteType (f i)) :
    LocallyOfFiniteType (Limits.Sigma.desc f) := by
  have := isZariskiLocalAtSource_locallyOfFiniteType_consolidated456
  exact IsZariskiLocalAtSource.sigmaDesc hf

private theorem flat_sigmaDesc_consolidated456 (hf : ∀ i, Flat (f i)) : Flat (Limits.Sigma.desc f) := by
  have := isZariskiLocalAtSource_flat_consolidated456
  exact IsZariskiLocalAtSource.sigmaDesc hf


end

private theorem exists_etaleCover_closedEmbeddingIntoAffineSpace_of_localCharts_consolidated456 (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k]
    (hsnc : ∀ (A : Scheme.{u}) (q : A ⟶ Spec (CommRingCat.of k)),
      Smooth q → InStrictNormalCrossingPosition q [])
    (Y V : Scheme.{u}) (pY : Y ⟶ Spec (CommRingCat.of k))
    (pV : V ⟶ Spec (CommRingCat.of k))
    [IsAffine Y] [IsAffine V]
    [IsReduced Y] [IsReduced V]
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    [LocallyOfFiniteType pV] [QuasiCompact pV]
    (G : EmbeddingDatum k Y pY) (P : ClosedEmbeddingIntoAffineSpace G)
    (H : EmbeddingDatum k V pV) (Q : ClosedEmbeddingIntoAffineSpace H)
    (u : V ⟶ Y) (r : ℕ) (hu : u ≫ pY = pV)
    (ι : Type u) [Fintype ι] [DecidableEq ι] (pt : ι → ↥V)
    (ch : ∀ i, PresentedLocalChart P H u r (pt i))
    (N : ℕ) (hN : ∀ i, (ch i).threshold ≤ N)
    (hcov : (⨆ i, (ch i).chartDomain) = ⊤) :
    ∃ (V'' : Scheme.{u}) (pV'' : V'' ⟶ Spec (CommRingCat.of k)) (c : V'' ⟶ V),
      IsAffine V'' ∧ IsReduced V'' ∧
      LocallyOfFiniteType pV'' ∧ QuasiCompact pV'' ∧
      Etale c ∧ AlgebraicGeometry.Surjective c ∧ c ≫ pV = pV'' ∧
      (∃ (G' : EmbeddingDatum k V'' pV'') (f : G'.ambient ⟶ G.ambient),
        Nonempty (ClosedEmbeddingIntoAffineSpace G') ∧
        Smooth f ∧ f ≫ G.ambientStruct = G'.ambientStruct ∧
        CategoryTheory.IsPullback G'.emb (c ≫ u) f G.emb) ∧
      (∃ (H' : EmbeddingDatum k V'' pV'') (g : H'.ambient ⟶ H.ambient),
        Nonempty (ClosedEmbeddingIntoAffineSpace H') ∧
        Smooth g ∧ g ≫ H.ambientStruct = H'.ambientStruct ∧
        CategoryTheory.IsPullback H'.emb c g H.emb) := by
  classical
  have hsubs : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstance
  have hDaff : ∀ i, IsAffine (((ch i).chartDomain).toScheme) := fun i =>
    (ch i).isAffineOpen_chartDomain
  have hambaff : ∀ i, IsAffine ((ch i).ambient) := fun i => (ch i).isAffine_ambient
  have hBaff : ∀ i, IsAffine ((H.ambient.basicOpen ((ch i).func)).toScheme) := fun i =>
    (isAffineOpen_top H.ambient).basicOpen ((ch i).func)
  have hVaff : IsAffine (sigmaOpens V fun i => (ch i).chartDomain) :=
    isAffine_sigmaOpens V _ fun i => (ch i).isAffineOpen_chartDomain
  have hVcs : CompactSpace ↥(sigmaOpens V fun i => (ch i).chartDomain) := inferInstance
  obtain ⟨e, he⟩ : ∃ e : ι → k, Function.Injective e := by
    refine ⟨fun i => ((Fintype.equivFin ι i : ℕ) : k), fun a b hab => ?_⟩
    have h2 : (Fintype.equivFin ι a : ℕ) = (Fintype.equivFin ι b : ℕ) := Nat.cast_injective hab
    exact (Fintype.equivFin ι).injective (Fin.eq_of_val_eq h2)
  refine ⟨sigmaOpens V (fun i => (ch i).chartDomain),
    (sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ pV,
    sigmaOpensDesc V (fun i => (ch i).chartDomain),
    hVaff, inferInstance, inferInstance,
    quasiCompact_of_compactSpace_of_subsingleton .., inferInstance,
    surjective_sigmaOpensDesc V _ hcov, rfl, ?_, ?_⟩
  · have hpullbackG : IsPullback (Limits.Sigma.map fun i => (ch i).imm)
        ((sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ u)
        (Limits.Sigma.desc fun i => (ch i).toAmbient) G.emb := by
      have h0 : IsPullback (Limits.Sigma.map fun i => (ch i).imm)
          (Limits.Sigma.desc fun i => ((ch i).chartDomain).ι ≫ u)
          (Limits.Sigma.desc fun i => (ch i).toAmbient) G.emb :=
        isPullback_sigmaMap_sigmaDesc G.emb (fun i => (ch i).ambient)
          (fun i => ((ch i).chartDomain).toScheme) (fun i => (ch i).imm)
          (fun i => ((ch i).chartDomain).ι ≫ u) (fun i => (ch i).toAmbient)
          (fun i => (ch i).isPullback)
      have hdescu : (Limits.Sigma.desc fun i => ((ch i).chartDomain).ι ≫ u)
          = (sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ u := by
        refine Limits.Sigma.hom_ext _ _ fun i => ?_
        simp
      rwa [hdescu] at h0
    have hsmfG : Smooth (Limits.Sigma.desc fun i => (ch i).toAmbient) :=
      smooth_sigmaDesc _ fun i => (ch i).smooth_toAmbient
    have hstructeq : (Limits.Sigma.desc fun i => (ch i).toAmbient) ≫ G.ambientStruct
        = Limits.Sigma.desc fun i => (ch i).ambientStruct := by
      refine Limits.Sigma.hom_ext _ _ fun i => ?_
      simp [(ch i).comp_eq]
    have hsmstructG :
        Smooth ((Limits.Sigma.desc fun i => (ch i).toAmbient) ≫ G.ambientStruct) := by
      rw [hstructeq]
      exact smooth_sigmaDesc _ fun i => (ch i).smooth_ambientStruct
    have hlftstructG :
        LocallyOfFiniteType ((Limits.Sigma.desc fun i => (ch i).toAmbient) ≫ G.ambientStruct) := by
      rw [hstructeq]
      exact locallyOfFiniteType_sigmaDesc_consolidated456 _ fun i => (ch i).locallyOfFiniteType_ambientStruct
    have hGaff : IsAffine (∐ fun i => (ch i).ambient) := inferInstance
    have hGcs : CompactSpace ↥(∐ fun i => (ch i).ambient) := inferInstance
    have hqcstructG :
        QuasiCompact ((Limits.Sigma.desc fun i => (ch i).toAmbient) ≫ G.ambientStruct) :=
      quasiCompact_of_compactSpace_of_subsingleton ..
    have hCIembG : IsClosedImmersion (Limits.Sigma.map fun i => (ch i).imm) :=
      MorphismProperty.of_isPullback (P := (@IsClosedImmersion : MorphismProperty Scheme.{u}))
        hpullbackG.flip G.isClosedImmersion_emb
    have hqcGemb : QuasiCompact G.emb := inferInstance
    have hqcembG : QuasiCompact (Limits.Sigma.map fun i => (ch i).imm) :=
      quasiCompact_of_isPullback hpullbackG.flip
    have hflatfG : Flat (Limits.Sigma.desc fun i => (ch i).toAmbient) :=
      flat_sigmaDesc_consolidated456 _ fun i => inferInstance
    have hkerG : (Limits.Sigma.map fun i => (ch i).imm).ker
        = G.emb.ker.comap (Limits.Sigma.desc fun i => (ch i).toAmbient) :=
      ker_eq_comap_ker_of_isPullback_of_flat hpullbackG.flip
    have hnzG : NonzeroOnComponents (Limits.Sigma.map fun i => (ch i).imm).ker := by
      rw [hkerG]
      exact NonzeroOnComponents.comap_of_flat G.nonzeroOnComponents_ker _
    have hcompG : (Limits.Sigma.map fun i => (ch i).imm) ≫
        ((Limits.Sigma.desc fun i => (ch i).toAmbient) ≫ G.ambientStruct)
        = (sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ pV := by
      rw [← Category.assoc, hpullbackG.w, Category.assoc, G.comp_eq, Category.assoc, hu]
    refine ⟨embeddingDatumOfClosedImmersion (∐ fun i => (ch i).ambient)
        ((Limits.Sigma.desc fun i => (ch i).toAmbient) ≫ G.ambientStruct)
        (Limits.Sigma.map fun i => (ch i).imm) hnzG hcompG (hsnc _ _ hsmstructG),
      Limits.Sigma.desc fun i => (ch i).toAmbient, ⟨?_⟩, hsmfG, rfl, hpullbackG⟩
    have hpres : ∀ i, ∃ σ : (ch i).ambient ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N + 1))),
        IsClosedImmersion σ ∧
        σ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (P.dim + N + 1))) = (ch i).ambientStruct ∧
        HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (P.dim + N + 1)))) σ
          (P.codimBound + (N - r) + 1) := fun i => (ch i).presentation N (hN i)
    choose σ hσCI hσcomp hσcod using hpres
    have hσCI' : ∀ i, IsClosedImmersion (σ i) := hσCI
    have hCIunionG :
        IsClosedImmersion (coproductSliceMap k (P.dim + N + 1) e (fun i => (ch i).ambient) σ) :=
      isClosedImmersion_coproductSliceMap k (P.dim + N + 1) e he (fun i => (ch i).ambient) σ
    have hCIfinG :
        IsClosedImmersion (coproductSliceMapReindexed k (P.dim + N + 1) e (fun i => (ch i).ambient) σ) :=
      inferInstance
    refine ⟨P.codimBound + (N - r) + 1 + 1, P.dim + N + 1 + 1,
      coproductSliceMapReindexed k (P.dim + N + 1) e (fun i => (ch i).ambient) σ, by omega, by omega,
      hCIfinG, ?_, ?_⟩
    · refine coproductSliceMapReindexed_comp_affineSpaceIndexedByToSpec k (P.dim + N + 1) e (fun i => (ch i).ambient) σ _ ?_
      intro i
      show Limits.Sigma.ι (fun j => (ch j).ambient) i ≫
          ((Limits.Sigma.desc fun j => (ch j).toAmbient) ≫ G.ambientStruct) =
          σ i ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (P.dim + N + 1)))
      simp [(ch i).comp_eq, hσcomp i]
    · exact hasSmoothCoordCodim_coproductSliceMapReindexed hsm k (P.dim + N + 1)
        (P.codimBound + (N - r) + 1) e he (fun i => (ch i).ambient) σ hσcod
  · have hpullbackH : IsPullback
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func)))
        (sigmaOpensDesc V fun i => (ch i).chartDomain)
        (sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) H.emb :=
      isPullback_sigmaMap_sigmaDesc H.emb
        (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
        (fun i => ((ch i).chartDomain).toScheme)
        (fun i => H.emb ∣_ H.ambient.basicOpen ((ch i).func))
        (fun i => ((ch i).chartDomain).ι)
        (fun i => (H.ambient.basicOpen ((ch i).func)).ι)
        (fun i => (ch i).isPullback_morphismRestrict_basicOpen)
    have hsmg : Smooth (sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) :=
      smooth_sigmaDesc _ fun i => inferInstance
    have hlftg : LocallyOfFiniteType
        (sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) :=
      inferInstance
    have hflatg : Flat (sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) :=
      flat_sigmaDesc_consolidated456 _ fun i => inferInstance
    have hHaff : IsAffine (sigmaOpens H.ambient fun i => H.ambient.basicOpen ((ch i).func)) :=
      isAffine_sigmaOpens H.ambient _ fun i =>
        (isAffineOpen_top H.ambient).basicOpen ((ch i).func)
    have hHcs :
        CompactSpace ↥(sigmaOpens H.ambient fun i => H.ambient.basicOpen ((ch i).func)) :=
      inferInstance
    have hsmq : Smooth
        ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) ≫
          H.ambientStruct) := inferInstance
    have hlftq : LocallyOfFiniteType
        ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) ≫
          H.ambientStruct) := inferInstance
    have hqcq : QuasiCompact
        ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) ≫
          H.ambientStruct) := quasiCompact_of_compactSpace_of_subsingleton ..
    have hCIembH : IsClosedImmersion
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func))) :=
      MorphismProperty.of_isPullback (P := (@IsClosedImmersion : MorphismProperty Scheme.{u}))
        hpullbackH.flip H.isClosedImmersion_emb
    have hqcHemb : QuasiCompact H.emb := inferInstance
    have hqcembH : QuasiCompact
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func))) :=
      quasiCompact_of_isPullback hpullbackH.flip
    have hkerH :
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func))).ker
          = H.emb.ker.comap
            (sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) :=
      ker_eq_comap_ker_of_isPullback_of_flat hpullbackH.flip
    have hnzH : NonzeroOnComponents
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func))).ker := by
      rw [hkerH]
      exact NonzeroOnComponents.comap_of_flat H.nonzeroOnComponents_ker _
    have hcompH :
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func))) ≫
          ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) ≫
            H.ambientStruct)
          = (sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ pV := by
      rw [← Category.assoc, hpullbackH.w, Category.assoc, H.comp_eq]
    refine ⟨embeddingDatumOfClosedImmersion
        (sigmaOpens H.ambient fun i => H.ambient.basicOpen ((ch i).func))
        ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) ≫ H.ambientStruct)
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func)))
        hnzH hcompH (hsnc _ _ hsmq),
      sigmaOpensDesc H.ambient (fun i => H.ambient.basicOpen ((ch i).func)), ⟨?_⟩, hsmg, rfl,
      hpullbackH⟩
    have hCIrho : ∀ i, IsClosedImmersion
        (basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom) :=
      fun i => inferInstance
    have hrhocomp : ∀ i,
        (basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom) ≫
            affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (Q.dim + 1)))
          = (H.ambient.basicOpen ((ch i).func)).ι ≫ H.ambientStruct := by
      intro i
      rw [Category.assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec]
      exact basicOpenEmbedding_comp_affineSpaceIndexedByToSpec k Q.dim Q.toAffine ((ch i).func) H.ambientStruct
        Q.toAffine_comp
    have hrhocod : ∀ i,
        HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (Q.dim + 1))))
          (basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
            (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom)
          (Q.codimBound + 1) :=
      fun i => hasSmoothCoordCodim_basicOpenEmbedding hsm k Q.dim Q.codimBound Q.toAffine
        ((ch i).func) Q.locallyConstCodim
    have hCIunionH : IsClosedImmersion
        (coproductSliceMap k (Q.dim + 1) e (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
          (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
            (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom)) :=
      isClosedImmersion_coproductSliceMap k (Q.dim + 1) e he
        (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
        (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom)
    have hCIfinH : IsClosedImmersion
        (coproductSliceMapReindexed k (Q.dim + 1) e (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
          (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
            (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom)) :=
      inferInstance
    refine ⟨Q.codimBound + 1 + 1, Q.dim + 1 + 1,
      coproductSliceMapReindexed k (Q.dim + 1) e (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
        (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom),
      by omega, by omega, hCIfinH, ?_, ?_⟩
    · refine coproductSliceMapReindexed_comp_affineSpaceIndexedByToSpec k (Q.dim + 1) e
        (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
        (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom) _ ?_
      intro i
      show Limits.Sigma.ι (fun j => (H.ambient.basicOpen ((ch j).func)).toScheme) i ≫
          ((sigmaOpensDesc H.ambient fun j => H.ambient.basicOpen ((ch j).func)) ≫
            H.ambientStruct) =
          (basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
            (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom) ≫
            affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (Q.dim + 1)))
      rw [hrhocomp i]
      simp
    · exact hasSmoothCoordCodim_coproductSliceMapReindexed hsm k (Q.dim + 1) (Q.codimBound + 1) e he
        (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
        (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom)
        hrhocod

theorem exists_etaleCover_closedEmbeddingIntoAffineSpace_of_smooth
    (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k]
    (hsnc : ∀ (A : Scheme.{u}) (q : A ⟶ Spec (CommRingCat.of k)),
      Smooth q → InStrictNormalCrossingPosition q [])
    (Y V : Scheme.{u}) (pY : Y ⟶ Spec (CommRingCat.of k))
    (pV : V ⟶ Spec (CommRingCat.of k))
    [IsAffine Y] [IsAffine V]
    [IsReduced Y] [IsReduced V]
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    [LocallyOfFiniteType pV] [QuasiCompact pV]
    (G : EmbeddingDatum k Y pY) (P : ClosedEmbeddingIntoAffineSpace G)
    (H : EmbeddingDatum k V pV) (Q : ClosedEmbeddingIntoAffineSpace H)
    (u : V ⟶ Y) (r : ℕ) [SmoothOfRelativeDimension r u]
    (hu : u ≫ pY = pV) :
    ∃ (V'' : Scheme.{u}) (pV'' : V'' ⟶ Spec (CommRingCat.of k)) (c : V'' ⟶ V),
      IsAffine V'' ∧ IsReduced V'' ∧
      LocallyOfFiniteType pV'' ∧ QuasiCompact pV'' ∧
      Etale c ∧ AlgebraicGeometry.Surjective c ∧ c ≫ pV = pV'' ∧
      (∃ (G' : EmbeddingDatum k V'' pV'') (f : G'.ambient ⟶ G.ambient),
        Nonempty (ClosedEmbeddingIntoAffineSpace G') ∧
        Smooth f ∧ f ≫ G.ambientStruct = G'.ambientStruct ∧
        CategoryTheory.IsPullback G'.emb (c ≫ u) f G.emb) ∧
      (∃ (H' : EmbeddingDatum k V'' pV'') (g : H'.ambient ⟶ H.ambient),
        Nonempty (ClosedEmbeddingIntoAffineSpace H') ∧
        Smooth g ∧ g ≫ H.ambientStruct = H'.ambientStruct ∧
        CategoryTheory.IsPullback H'.emb c g H.emb) := by
  classical
  have hVcs : CompactSpace ↥V := inferInstance
  have hch : ∀ y : ↥V, Nonempty (PresentedLocalChart P H u r y) := fun y =>
    nonempty_presentedLocalChart hS hsm k Y V pY pV G P H u r hu y
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun y : ↥V => ((((hch y).some.chartDomain) : V.Opens) : Set ↥V))
    (fun y => ((hch y).some.chartDomain).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, (hch x).some.mem_domain⟩)
  have hfin : Fintype { y : ↥V // y ∈ t } := FinsetCoe.fintype t
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i : { y : ↥V // y ∈ t }, ((hch i.1).some).threshold ≤ N :=
    ⟨Finset.univ.sup fun i : { y : ↥V // y ∈ t } => ((hch i.1).some).threshold,
      fun i => Finset.le_sup
        (f := fun i : { y : ↥V // y ∈ t } => ((hch i.1).some).threshold) (Finset.mem_univ i)⟩
  refine exists_etaleCover_closedEmbeddingIntoAffineSpace_of_localCharts_consolidated456 hsm k hsnc Y V pY pV G P H Q u r hu
    { y : ↥V // y ∈ t } (fun i => i.1) (fun i => (hch i.1).some) N hN ?_
  refine TopologicalSpace.Opens.ext ?_
  rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
  refine Set.eq_univ_of_univ_subset fun x _ => ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PresentedSelectionCompatibility
section

open CategoryTheory AlgebraicGeometry

section

section
variable (E : EmbeddedResolutionRule.{u}) (C : PresentedSelection.{u}) (hinv : E.IsIndependentOfPresentedEmbedding) (hsbc : E.IsCompatibleWithSmoothAmbientMaps) (hprop : E.HasProperCenters) (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) (hsm : AffineSpaceIsSmooth.{u}) (hsnc : ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u}) (q : A ⟶ Spec (CommRingCat.of k)), Smooth q → InStrictNormalCrossingPosition q [])
include hinv hsbc hprop hS hsm hsnc

theorem isPullbackBlowupSequence_presentedSelection_of_smooth (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    [IsAffine Y] [IsAffine V]
    [IsReduced Y] [IsReduced V]
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    [LocallyOfFiniteType pV] [QuasiCompact pV]
    (u : V ⟶ Y) (r : ℕ) [SmoothOfRelativeDimension r u]
    (hu : u ≫ pY = pV) :
    IsPullbackBlowupSequence u (E k V pV (C.sel k V pV)) (E k Y pY (C.sel k Y pY)) := by
  obtain ⟨V'', pV'', c, hV''aff, hV''red, hV''ft, hV''qc, hcet, hcsurj, hcpV,
      ⟨G', f, hG'pres, hfsm, hfcomp, hfpb⟩, ⟨H', g, hH'pres, hgsm, hgcomp, hgpb⟩⟩ :=
    exists_etaleCover_closedEmbeddingIntoAffineSpace_of_smooth hS hsm k (fun A q hq => hsnc k A q hq)
      Y V pY pV (C.sel k Y pY) (C.pres k Y pY) (C.sel k V pV) (C.pres k V pV) u r hu
  have := hV''aff
  have := hV''red
  have := hV''ft
  have := hV''qc
  have := hcet
  have := hcsurj
  have := hfsm
  have := hgsm
  have : Smooth u := AlgebraicGeometry.SmoothOfRelativeDimension.smooth r u
  have : Flat u := inferInstance
  have : Flat c := inferInstance
  have s1 : IsPullbackBlowupSequence (c ≫ u) (E k V'' pV'' G') (E k Y pY (C.sel k Y pY)) :=
    hsbc k Y V'' pY pV'' (C.sel k Y pY) G' f (c ≫ u) hfcomp hfpb
  have s2 : IsPullbackBlowupSequence c (E k V'' pV'' H') (E k V pV (C.sel k V pV)) :=
    hsbc k V V'' pV pV'' (C.sel k V pV) H' g c hgcomp hgpb
  have heq : (E k V'' pV'' G').Isomorphic (E k V'' pV'' H') :=
    hinv k V'' pV'' G' H' hG'pres.some hH'pres.some
  have s2' : IsStrictPullbackBlowupSeq c (E k V'' pV'' H') (E k V pV (C.sel k V pV)) :=
    s2.isStrictPullback_of_surjective
      (fun i hi => hprop k V pV (C.sel k V pV) i hi)
  have hBu : IsStrictPullbackBlowupSeq u ((E k Y pY (C.sel k Y pY)).baseChange u)
      (E k Y pY (C.sel k Y pY)) :=
    isStrictPullbackSequenceOfBlowups_baseChange (E k Y pY (C.sel k Y pY)) u
  have hB' : IsPullbackBlowupSequence u ((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups
      (E k Y pY (C.sel k Y pY)) := hBu.isPullbackSequenceOfBlowups_withoutIsoBlowups
  have hCc : IsStrictPullbackBlowupSeq c
      ((((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups).baseChange c)
      (((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups) :=
    isStrictPullbackSequenceOfBlowups_baseChange
      (((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups) c
  have hC : IsPullbackBlowupSequence (c ≫ u)
      ((((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups).baseChange c)
      (E k Y pY (C.sel k Y pY)) := hB'.comp_isStrictPullbackSequenceOfBlowups hCc
  have heq2 : (E k V'' pV'' G').Isomorphic
      ((((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups).baseChange c) := s1.isomorphic hC
  have hdesc : (E k V pV (C.sel k V pV)).Isomorphic
      (((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups) :=
    IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic s2' hCc (heq.symm.trans heq2)
  exact hB'.of_isomorphic hdesc.symm

theorem isCompatibleWithOpenImmersions_toAffineResolutionRule :
    IsCompatibleWithOpenImmersions (E.toAffineResolutionRule C.sel) := by
  intro k _ _ Y V pY pV _ _ _ _ _ _ _ _ φ _ hφ
  have : SmoothOfRelativeDimension 0 φ := inferInstance
  exact isPullbackBlowupSequence_presentedSelection_of_smooth E C hinv hsbc hprop hS hsm hsnc k Y V pY pV
    φ 0 hφ

theorem isCompatibleWithEtaleCovers_toAffineResolutionRule :
    IsCompatibleWithEtaleCovers (E.toAffineResolutionRule C.sel) := by
  intro k _ _ Y W pY pW _ _ _ _ _ _ _ _ φ _ hφ hsurj
  have : SmoothOfRelativeDimension 0 φ := inferInstance
  have : AlgebraicGeometry.Surjective φ := ⟨hsurj⟩
  have hpb : IsPullbackBlowupSequence φ (E k W pW (C.sel k W pW)) (E k Y pY (C.sel k Y pY)) :=
    isPullbackBlowupSequence_presentedSelection_of_smooth E C hinv hsbc hprop hS hsm hsnc k Y W pY pW
      φ 0 hφ
  exact hpb.isStrictPullback_of_surjective
    (fun i hi => hprop k Y pY (C.sel k Y pY) i hi)


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRuleCompatibility
section

open CategoryTheory AlgebraicGeometry


theorem smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth (hsm : AffineSpaceIsSmooth.{u}) :
    SmoothPullbackHasLocalAmbientEmbedding.{u} :=
  smoothPullbackHasLocalAmbientEmbedding_of_hasGraphChart hsm smoothPullbackHasGraphChart

section
variable (A : PrincipalizationAlgorithm.{u}) (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A) (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm) (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u})
include hAlg hw hcmp

theorem isCompatibleWithOpenImmersions_affineResolutionRuleOfPrincipalization_of_smoothPullbackHasLocalAmbientEmbedding
    (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) :
    IsCompatibleWithOpenImmersions (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) := by
  have key := isCompatibleWithOpenImmersions_toAffineResolutionRule (embeddedResolutionRuleOfPrincipalization A hw)
    (affineSpacePresentedSelection hemb hsncE hsm)
    (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
    (embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps A hAlg hw)
    (hasProperCenters_embeddedResolutionRuleOfPrincipalization A hw) hS hsm nilIsStrictNormalCrossingsOfSmooth
  rw [affineSpacePresentedSelection_selection,
    toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex] at key
  exact key

theorem isCompatibleWithEtaleCovers_affineResolutionRuleOfPrincipalization_of_smoothPullbackHasLocalAmbientEmbedding
    (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) :
    IsCompatibleWithEtaleCovers (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) := by
  have key := isCompatibleWithEtaleCovers_toAffineResolutionRule (embeddedResolutionRuleOfPrincipalization A hw)
    (affineSpacePresentedSelection hemb hsncE hsm)
    (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
    (embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps A hAlg hw)
    (hasProperCenters_embeddedResolutionRuleOfPrincipalization A hw) hS hsm nilIsStrictNormalCrossingsOfSmooth
  rw [affineSpacePresentedSelection_selection,
    toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex] at key
  exact key

theorem isCompatibleWithOpenImmersions_affineResolutionRuleOfPrincipalization :
    IsCompatibleWithOpenImmersions (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) :=
  isCompatibleWithOpenImmersions_affineResolutionRuleOfPrincipalization_of_smoothPullbackHasLocalAmbientEmbedding A hAlg hw hemb hsncE
    hsm hex hcmp (smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth hsm)

theorem isCompatibleWithEtaleCovers_affineResolutionRuleOfPrincipalization :
    IsCompatibleWithEtaleCovers (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) :=
  isCompatibleWithEtaleCovers_affineResolutionRuleOfPrincipalization_of_smoothPullbackHasLocalAmbientEmbedding A hAlg hw hemb hsncE
    hsm hex hcmp (smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth hsm)

theorem isCompatibleWithFieldBaseChange_affineResolutionRuleOfPrincipalization :
    IsCompatibleWithFieldBaseChange (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) := by
  have key := isCompatibleWithFieldBaseChange_toAffineResolutionRule (embeddedResolutionRuleOfPrincipalization A hw)
    (affineSpacePresentedSelection hemb hsncE hsm)
    (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
    (embeddedResolutionRule_isCompatibleWithFieldBaseChange A hAlg hw) nilIsStrictNormalCrossingsOfSmooth
  rw [affineSpacePresentedSelection_selection,
    toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex] at key
  exact key

theorem isPullbackBlowupSequence_affineResolutionRuleOfPrincipalization_of_smooth (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    [IsAffine Y] [IsAffine V]
    [IsReduced Y] [IsReduced V]
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    [LocallyOfFiniteType pV] [QuasiCompact pV]
    (u : V ⟶ Y) (r : ℕ) [SmoothOfRelativeDimension r u]
    (hu : u ≫ pY = pV) :
    IsPullbackBlowupSequence u (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex k V pV)
      (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex k Y pY) := by
  have key := isPullbackBlowupSequence_presentedSelection_of_smooth (embeddedResolutionRuleOfPrincipalization A hw)
    (affineSpacePresentedSelection hemb hsncE hsm)
    (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
    (embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps A hAlg hw)
    (hasProperCenters_embeddedResolutionRuleOfPrincipalization A hw)
    (smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth hsm) hsm nilIsStrictNormalCrossingsOfSmooth
    k Y V pY pV u r hu
  rw [affineSpacePresentedSelection_selection] at key
  rw [← toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex,
    EmbeddedResolutionRule.toAffineResolutionRule_apply, EmbeddedResolutionRule.toAffineResolutionRule_apply]
  exact key


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.GlobalResolutionFromAffine
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section

def IsCompatibleWithSmoothOfRelativeDimension (B : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    [IsAffine Y] [IsAffine V]
    [IsReduced Y] [IsReduced V]
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    [LocallyOfFiniteType pV] [QuasiCompact pV]
    (u : V ⟶ Y) (r : ℕ) [SmoothOfRelativeDimension r u],
    u ≫ pY = pV → IsPullbackBlowupSequence u (B k V pV) (B k Y pY)

theorem isCompatibleWithSmoothOfRelativeDimension_affineResolutionRule (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) :
    IsCompatibleWithSmoothOfRelativeDimension (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) := by
  intro k _ _ Y V pY pV _ _ _ _ _ _ _ _ u r _ hu
  exact isPullbackBlowupSequence_affineResolutionRuleOfPrincipalization_of_smooth A hAlg hw hemb hsncE hsm hex hcmp
    k Y V pY pV u r hu

section
variable {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (r : ℕ)

private theorem smoothOfRelativeDimension_comp_zero_consolidated489 [SmoothOfRelativeDimension r f]
    [SmoothOfRelativeDimension 0 g] :
    SmoothOfRelativeDimension r (f ≫ g) := by
  have h : SmoothOfRelativeDimension (r + 0) (f ≫ g) := inferInstance
  simpa using h

private theorem smoothOfRelativeDimension_zero_comp_consolidated489 [SmoothOfRelativeDimension 0 f]
    [SmoothOfRelativeDimension r g] :
    SmoothOfRelativeDimension r (f ≫ g) := by
  have h : SmoothOfRelativeDimension (0 + r) (f ≫ g) := inferInstance
  simpa using h


end

private theorem opensImage_le_preimage_consolidated489 {X Y : Scheme.{u}} (f : X ⟶ Y) (Z : X.Opens) (U₀ : Y.Opens)
    (W : Z.toScheme.Opens) (e : W ≤ (Z.ι ≫ f) ⁻¹ᵁ U₀) : Z.ι ''ᵁ W ≤ f ⁻¹ᵁ U₀ := by
  rintro x ⟨w, hw, rfl⟩
  simpa using e hw

section
variable (r : ℕ)

private theorem respectsIso_smoothOfRelativeDimension_consolidated489 :
    MorphismProperty.RespectsIso
      (@SmoothOfRelativeDimension r : MorphismProperty Scheme.{u}) := by
  have hL : MorphismProperty.RespectsLeft
      (@SmoothOfRelativeDimension r : MorphismProperty Scheme.{u})
      (MorphismProperty.isomorphisms Scheme.{u}) := by
    constructor
    intro X Y Z i hi f hf
    have : CategoryTheory.IsIso i := hi
    have : IsOpenImmersion i := inferInstance
    have : SmoothOfRelativeDimension 0 i := inferInstance
    have := hf
    exact smoothOfRelativeDimension_zero_comp_consolidated489 i f r
  have hR : MorphismProperty.RespectsRight
      (@SmoothOfRelativeDimension r : MorphismProperty Scheme.{u})
      (MorphismProperty.isomorphisms Scheme.{u}) := by
    constructor
    intro X Y Z i hi f hf
    have : CategoryTheory.IsIso i := hi
    have : IsOpenImmersion i := inferInstance
    have : SmoothOfRelativeDimension 0 i := inferInstance
    have := hf
    exact smoothOfRelativeDimension_comp_zero_consolidated489 f i r
  exact ⟨⟩

private theorem smoothOfRelativeDimension_of_iSup_eq_top_consolidated489 {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (H : ∀ i, SmoothOfRelativeDimension r ((U i).ι ≫ f)) :
    SmoothOfRelativeDimension r f := by
  refine ⟨fun x => ?_⟩
  have htop : x ∈ (⊤ : X.Opens) := trivial
  rw [← hU] at htop
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp htop
  obtain ⟨H'⟩ := H i
  obtain ⟨U₀, hU₀, W, hW, hxW, e, hsm⟩ := H' ⟨x, hi⟩
  have e' : (U i).ι ''ᵁ W ≤ f ⁻¹ᵁ U₀ := opensImage_le_preimage_consolidated489 f (U i) U₀ W e
  have hle : W ≤ (U i).ι ⁻¹ᵁ ((U i).ι ''ᵁ W) := by
    intro w hw
    exact ⟨w, hw, rfl⟩
  refine ⟨U₀, hU₀, (U i).ι ''ᵁ W, hW.image_of_isOpenImmersion (U i).ι,
    ⟨⟨x, hi⟩, hxW, rfl⟩, e', ?_⟩
  have h1 := Scheme.Hom.appLE_comp_appLE (U i).ι f U₀ ((U i).ι ''ᵁ W) W e' hle
  have h2 := Scheme.Opens.ι_appLE (U i) ((U i).ι ''ᵁ W) W hle
  have h3 : X.presheaf.map (homOfLE (le_refl ((U i).ι ''ᵁ W))).op
      = 𝟙 (X.presheaf.obj (Opposite.op ((U i).ι ''ᵁ W))) := by
    simp
  have h23 := h2.trans h3
  have key : ((U i).ι ≫ f).appLE U₀ W e = f.appLE U₀ ((U i).ι ''ᵁ W) e' :=
    h1.symm.trans ((congrArg (fun m => f.appLE U₀ ((U i).ι ''ᵁ W) e' ≫ m) h23).trans
      (Category.comp_id _))
  exact Eq.mp (congrArg (fun m =>
    RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom m)) key) hsm

private theorem isZariskiLocalAtSource_smoothOfRelativeDimension_consolidated489 :
    AlgebraicGeometry.IsZariskiLocalAtSource
      (@SmoothOfRelativeDimension r : MorphismProperty Scheme.{u}) := by
  have := respectsIso_smoothOfRelativeDimension_consolidated489 r
  refine AlgebraicGeometry.IsZariskiLocalAtSource.mk' ?_ ?_
  · intro X Y f U hf
    have := hf
    have : SmoothOfRelativeDimension 0 U.ι := inferInstance
    exact smoothOfRelativeDimension_zero_comp_consolidated489 U.ι f r
  · intro X Y f ι U hU H
    exact smoothOfRelativeDimension_of_iSup_eq_top_consolidated489 r f U hU H


end

theorem smoothOfRelativeDimension_opensCoprodMapOfRefinement {X' X : Scheme.{u}} (φ : X' ⟶ X) (r : ℕ)
    [SmoothOfRelativeDimension r φ] {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    SmoothOfRelativeDimension r (opensCoprodMapOfRefinement φ U V β hβ) := by
  have := isZariskiLocalAtSource_smoothOfRelativeDimension_consolidated489 r
  have h : ∀ a : κ, SmoothOfRelativeDimension r
      (φ.resLE (U (β a)) (V a) (hβ a) ≫ Sigma.ι (fun i => (U i).toScheme) (β a)) := by
    intro a
    have : SmoothOfRelativeDimension 0
        (Sigma.ι (fun i => (U i).toScheme) (β a)) := inferInstance
    exact smoothOfRelativeDimension_comp_zero_consolidated489 _ _ r
  exact AlgebraicGeometry.IsZariskiLocalAtSource.sigmaDesc h

theorem exists_affine_etale_cover_of_smoothOfRelativeDimension {k : Type u} [Field k]
    {X X' : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    [IsReduced X]
    [LocallyOfFiniteType f'] [QuasiCompact f']
    [IsReduced X']
    (φ : X' ⟶ X) (r : ℕ) [SmoothOfRelativeDimension r φ]
    (hφ : φ ≫ f = f') :
    ∃ (W : Scheme.{u}) (q : W ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
      (W' : Scheme.{u}) (q' : W' ⟶ Spec (CommRingCat.of k)) (c' : W' ⟶ X') (ψ : W' ⟶ W),
      IsAffine W ∧ IsReduced W ∧
        LocallyOfFiniteType q ∧ QuasiCompact q ∧
        Etale c ∧ AlgebraicGeometry.Surjective c ∧ c ≫ f = q ∧
      IsAffine W' ∧ IsReduced W' ∧
        LocallyOfFiniteType q' ∧ QuasiCompact q' ∧
        Etale c' ∧ AlgebraicGeometry.Surjective c' ∧ c' ≫ f' = q' ∧
      SmoothOfRelativeDimension r ψ ∧ ψ ≫ c = c' ≫ φ ∧ ψ ≫ q = q' := by
  have hcX : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace f
  have hcX' : CompactSpace ↥X' := QuasiCompact.compactSpace_of_compactSpace f'
  obtain ⟨ι, hι, U, hUaff, hUtop⟩ := exists_finite_affine_cover X
  have : Finite ι := hι
  obtain ⟨κ, hκ, V, β, hVaff, hβ, hVtop⟩ := exists_finite_affine_cover_subordinate φ U hUtop
  have : Finite κ := hκ
  have hWaff : IsAffine (sigmaOpens X U) := isAffine_sigmaOpens X U hUaff
  have hW'aff : IsAffine (sigmaOpens X' V) := isAffine_sigmaOpens X' V hVaff
  have hcW : CompactSpace ↥(sigmaOpens X U) := inferInstance
  have hcW' : CompactSpace ↥(sigmaOpens X' V) := inferInstance
  exact ⟨sigmaOpens X U, sigmaOpensDesc X U ≫ f, sigmaOpensDesc X U,
    sigmaOpens X' V, sigmaOpensDesc X' V ≫ f', sigmaOpensDesc X' V,
    opensCoprodMapOfRefinement φ U V β hβ,
    hWaff, inferInstance, inferInstance,
    quasiCompact_of_compactSpace_of_subsingleton (sigmaOpensDesc X U ≫ f), inferInstance,
    surjective_sigmaOpensDesc X U hUtop, rfl,
    hW'aff, inferInstance, inferInstance,
    quasiCompact_of_compactSpace_of_subsingleton (sigmaOpensDesc X' V ≫ f'), inferInstance,
    surjective_sigmaOpensDesc X' V hVtop, rfl,
    smoothOfRelativeDimension_opensCoprodMapOfRefinement φ r U V β hβ,
    opensCoprodMapOfRefinement_comp_sigmaOpensDesc φ U V β hβ,
    (by rw [← Category.assoc, opensCoprodMapOfRefinement_comp_sigmaOpensDesc, Category.assoc, hφ])⟩

theorem isCompatibleWithSmoothMorphisms_of_isInducedByAffineRule (B : AffineResolutionRule.{u})
    (hB : IsCompatibleWithSmoothOfRelativeDimension B) (R : ResolutionRule.{u})
    (hR : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [LocallyOfFiniteType p] [QuasiCompact p]
      [IsReduced Y], IsInducedByAffineRule B k Y p (R k Y p)) :
    IsCompatibleWithSmoothMorphisms R := by
  intro k _ _ X X' f f' _ _ _ _ _ _ φ r _ hφ
  obtain ⟨W, q, c, W', q', c', ψ, hWaff, hWred, hqlft, hqqc, hcet, hcsurj, hcq,
    hW'aff, hW'red, hq'lft, hq'qc, hc'et, hc'surj, hc'q', hψsm, hψc, hψq⟩ :=
    exists_affine_etale_cover_of_smoothOfRelativeDimension f f' φ r hφ
  have := hWaff
  have := hWred
  have := hqlft
  have := hqqc
  have := hcet
  have := hcsurj
  have := hW'aff
  have := hW'red
  have := hq'lft
  have := hq'qc
  have := hc'et
  have := hc'surj
  have := hψsm
  have hsmφ : Smooth φ :=
    AlgebraicGeometry.SmoothOfRelativeDimension.smooth r φ
  have hsmψ : Smooth ψ :=
    AlgebraicGeometry.SmoothOfRelativeDimension.smooth r ψ
  have hflatφ : Flat φ := inferInstance
  have hflatψ : Flat ψ := inferInstance
  have hflatc' : Flat c' := inferInstance
  have hcs : ∀ y : ↥X, ∃ w, c w = y := fun y => hcsurj.surj y
  have hc's : ∀ y : ↥X', ∃ w, c' w = y := fun y => hc'surj.surj y
  have hA : IsStrictPullbackBlowupSeq c (B k W q) (R k X f) := hR k X f W q c hcq hcs
  have hA' : IsStrictPullbackBlowupSeq c' (B k W' q') (R k X' f') := hR k X' f' W' q' c' hc'q' hc's
  have hC : IsPullbackBlowupSequence ψ (B k W' q') (B k W q) := hB k W W' q q' ψ r hψq
  have h1 : IsStrictPullbackBlowupSeq φ ((R k X f).baseChange φ) (R k X f) :=
    isStrictPullbackSequenceOfBlowups_baseChange (R k X f) φ
  have h2 : IsStrictPullbackBlowupSeq c' (((R k X f).baseChange φ).baseChange c')
      ((R k X f).baseChange φ) :=
    isStrictPullbackSequenceOfBlowups_baseChange ((R k X f).baseChange φ) c'
  have h3 : IsStrictPullbackBlowupSeq (c' ≫ φ) (((R k X f).baseChange φ).baseChange c')
      (R k X f) := h2.comp h1
  have h4 : IsStrictPullbackBlowupSeq ψ ((B k W q).baseChange ψ) (B k W q) :=
    isStrictPullbackSequenceOfBlowups_baseChange (B k W q) ψ
  have h5 : IsStrictPullbackBlowupSeq (c' ≫ φ) ((B k W q).baseChange ψ) (R k X f) := by
    have h5' : IsStrictPullbackBlowupSeq (ψ ≫ c) ((B k W q).baseChange ψ) (R k X f) := h4.comp hA
    rwa [hψc] at h5'
  have h6 := h3.isomorphic h5
  have h7 := h6.withoutIsoBlowups
  have h8 : IsPullbackBlowupSequence ψ ((B k W q).baseChange ψ).withoutIsoBlowups (B k W q) := h4.isPullbackSequenceOfBlowups_withoutIsoBlowups
  have h9 := hC.isomorphic h8
  have h10 := h9.trans h7.symm
  have h11 := h2.withoutIsoBlowups
  have h12 := hA'.isomorphic_of_isomorphic h11 h10
  have h13 : IsPullbackBlowupSequence φ ((R k X f).baseChange φ).withoutIsoBlowups (R k X f) :=
    h1.isPullbackSequenceOfBlowups_withoutIsoBlowups
  exact h13.of_isomorphic h12.symm

section
variable (B : AffineResolutionRule.{u}) (hres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) (p : Y ⟶ Spec (CommRingCat.of k)) [IsAffine Y] [IsReduced Y] [LocallyOfFiniteType p] [QuasiCompact p], IsStrongResolution k Y p (B k Y p)) (hetale : IsCompatibleWithEtaleCovers B)
include hres hetale

private theorem isStrongResolution_of_isInducedByAffineRule_of_isAffine_consolidated489 (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) (p : Y ⟶ Spec (CommRingCat.of k))
    [IsAffine Y] [IsReduced Y]
    [LocallyOfFiniteType p] [QuasiCompact p]
    (s : SequenceOfBlowups Y) (hc : IsInducedByAffineRule B k Y p s) :
    IsStrongResolution k Y p s := by
  obtain ⟨W, q, g, hWaff, hWred, hqlft, hqqc, hget, hgsurj, hgq⟩ :=
    exists_affine_etale_cover_of_isReduced Y p
  have := hWaff
  have := hWred
  have := hqlft
  have := hqqc
  have := hget
  have := hgsurj
  have : Flat g := inferInstance
  have hsurj : ∀ y : ↥Y, ∃ w, g w = y := fun y => hgsurj.surj y
  have h1 : IsStrictPullbackBlowupSeq g (B k W q) s := hc W q g hgq hsurj
  have h2 : IsStrictPullbackBlowupSeq g (B k W q) (B k Y p) := hetale k Y W p q g hgq hsurj
  exact IsStrongResolution.of_isomorphic k Y p (h2.isomorphic_of_isomorphic h1 (SequenceOfBlowups.isomorphic_refl _)) (hres k Y p)

private theorem isStrongResolution_of_isInducedByAffineRule_consolidated489 (R : ResolutionRule.{u})
    (hcomes : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [LocallyOfFiniteType p] [QuasiCompact p]
      [IsReduced Y], IsInducedByAffineRule B k Y p (R k Y p))
    (hsmF : IsCompatibleWithSmoothMorphisms R)
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    [IsReduced X] :
    IsStrongResolution k X f (R k X f) := by
  have hOI : ∀ i : X.affineCover.I₀,
      IsOpenImmersion (X.affineCover.f i) := fun _ => inferInstance
  have hA : ∀ i : X.affineCover.I₀,
      IsAffine (X.affineCover.X i) := fun _ => inferInstance
  have hRed : ∀ i : X.affineCover.I₀,
      IsReduced (X.affineCover.X i) := by
    intro i
    have := hOI i
    exact inferInstance
  have hLFT : ∀ i : X.affineCover.I₀,
      LocallyOfFiniteType (X.affineCover.f i ≫ f) := by
    intro i
    have := hOI i
    exact inferInstance
  have hqc : ∀ i : X.affineCover.I₀,
      QuasiCompact (X.affineCover.f i ≫ f) := by
    intro i
    have := hA i
    have : CompactSpace ↥(X.affineCover.X i) := inferInstance
    exact quasiCompact_of_compactSpace_of_subsingleton (X.affineCover.f i ≫ f)
  have hCharts : ∀ i : X.affineCover.I₀,
      SmoothOfRelativeDimension 0 (X.affineCover.f i) := by
    intro i
    have := hOI i
    exact inferInstance
  have d : LocalResolutionData k f (R k X f) := by
    refine
      { cover := X.affineCover
        seq := fun i =>
          haveI := hLFT i
          haveI := hqc i
          haveI := hRed i
          R k (X.affineCover.X i) (X.affineCover.f i ≫ f)
        isPullback := ?_
        finiteType := hLFT
        isResolution := ?_ }
    · intro i
      have := hLFT i
      have := hqc i
      have := hRed i
      have := hCharts i
      exact hsmF k X (X.affineCover.X i) f (X.affineCover.f i ≫ f)
        (X.affineCover.f i) 0 rfl
    · intro i
      have := hA i
      have := hLFT i
      have := hqc i
      have := hRed i
      exact isStrongResolution_of_isInducedByAffineRule_of_isAffine_consolidated489 B hres hetale k (X.affineCover.X i)
        (X.affineCover.f i ≫ f)
        (R k (X.affineCover.X i) (X.affineCover.f i ≫ f))
        (hcomes k (X.affineCover.X i) (X.affineCover.f i ≫ f))
  refine ⟨d.smooth_lastStructMap_comp, d.isProper_lastStructMap, d.isIso_lastStructMap_restrict_smoothLocus, ?_,
    d.centersLieOver_smoothLocusComplement, d.isStrictNormalCrossingsDivisor_reducedInverseImage⟩
  exact d.dense_preimage_smoothLocus

theorem strongResolutionOfSingularitiesCharZero_of_affineResolutionRule (hopen : IsCompatibleWithOpenImmersions B)
    (hfield : IsCompatibleWithFieldBaseChange B) (hsmooth : IsCompatibleWithSmoothOfRelativeDimension B) :
    StrongResolutionOfSingularitiesCharZero.{u} := by
  have hcen : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
      [QuasiCompact p] [IsReduced Y]
      [IsAffine Y] (i : ℕ),
      i < (B k Y p).length → (B k Y p).center i ≠ ⊤ := by
    intro k _ _ Y p _ _ _ _ i hi
    exact AffineResolutionRule.center_ne_top B hopen k Y p i hi
  have H := existsGluedBlowupSequence_of_center_ne_top B hcen hetale
  obtain ⟨R, hcomes⟩ : ∃ R : ResolutionRule.{u},
      ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
        (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
        [QuasiCompact p] [IsReduced Y],
        IsInducedByAffineRule B k Y p (R k Y p) :=
    ⟨fun k _ _ Y p _ _ _ => (H k Y p).choose,
      fun k _ _ Y p _ _ _ => (H k Y p).choose_spec.2⟩
  have hsmF : IsCompatibleWithSmoothMorphisms R :=
    isCompatibleWithSmoothMorphisms_of_isInducedByAffineRule B hsmooth R hcomes
  refine ⟨R, ?_, hsmF, inducedRuleCompatibleWithFieldExtension B hopen hfield R hcomes⟩
  refine (isStrongResolutionRule_iff R).mpr ?_
  intro k _ _ X f _ _ _
  exact isStrongResolution_of_isInducedByAffineRule_consolidated489 B hres hetale R hcomes hsmF k X f


end

theorem strongResolutionOfSingularitiesCharZero_of_principalizationAlgorithm (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm) (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u})
    (haff : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [IsAffine Y] [IsReduced Y]
      [LocallyOfFiniteType p] [QuasiCompact p],
      IsStrongResolution k Y p (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex k Y p)) :
    StrongResolutionOfSingularitiesCharZero.{u} :=
  strongResolutionOfSingularitiesCharZero_of_affineResolutionRule
    (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) haff
    (isCompatibleWithEtaleCovers_affineResolutionRuleOfPrincipalization A hAlg hw hemb hsncE hsm hex hcmp)
    (isCompatibleWithOpenImmersions_affineResolutionRuleOfPrincipalization A hAlg hw hemb hsncE hsm hex hcmp)
    (isCompatibleWithFieldBaseChange_affineResolutionRuleOfPrincipalization A hAlg hw hemb hsncE hsm hex hcmp)
    (isCompatibleWithSmoothOfRelativeDimension_affineResolutionRule A hAlg hw hemb hsncE hsm hex hcmp)


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
section

section

structure PrincipalizationRules where
  divisorRed : ∀ T : MarkedIdealWithBoundary.{u},
    (∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) → ℕ → T.SequenceOfBlowups
  maxOrderRed : ∀ T : MarkedIdealWithBoundary.{u},
    (∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) → T.SequenceOfBlowups
  orderRed : ∀ T : MarkedIdealWithBoundary.{u},
    (∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) → T.SequenceOfBlowups

namespace PrincipalizationRules

def divisorFamily (B : PrincipalizationRules.{u}) (L : PrincipalizationAssignment.{u}) (j : ℕ) :
    PrincipalizationAssignment.{u} :=
  fun T => B.divisorRed T (fun S _ => L S) j

theorem divisorFamily_apply (B : PrincipalizationRules.{u}) (L : PrincipalizationAssignment.{u}) (j : ℕ)
    (T : MarkedIdealWithBoundary.{u}) :
    B.divisorFamily L j T = B.divisorRed T (fun S _ => L S) j := rfl

def orderFamily (B : PrincipalizationRules.{u}) (D : ℕ → PrincipalizationAssignment.{u}) :
    PrincipalizationAssignment.{u} :=
  fun T => B.orderRed T (fun S _ j => D j S)

def maxOrderFamily (B : PrincipalizationRules.{u}) (A : PrincipalizationAssignment.{u}) :
    PrincipalizationAssignment.{u} :=
  fun T => B.maxOrderRed T (fun S _ => A S)

def nextLevel (B : PrincipalizationRules.{u}) (L : OrderReductionData.{u}) : OrderReductionData.{u} where
  maxOrderRed := B.maxOrderFamily (B.orderFamily (fun j => B.divisorFamily L.maxOrderRed j))
  orderRed := B.orderFamily (fun j => B.divisorFamily L.maxOrderRed j)

def inputLevelData (B : PrincipalizationRules.{u}) : ℕ → OrderReductionData.{u}
  | 0 => trivialOrderReductionData.{u}
  | n + 1 => B.nextLevel (B.inputLevelData n)

def outputLevelData (B : PrincipalizationRules.{u}) (n : ℕ) : OrderReductionData.{u} := B.nextLevel (B.inputLevelData n)

@[simp] theorem inputLevelData_succ (B : PrincipalizationRules.{u}) (n : ℕ) :
    B.inputLevelData (n + 1) = B.outputLevelData n := rfl

structure ReducesInductivelyOnDimension (B : PrincipalizationRules.{u}) : Prop where
  divisorSpec : ∀ (n : ℕ) (L O : PrincipalizationAssignment.{u}),
    IsMaxOrderReduction (fun d => d < n) L O →
    ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (B.divisorFamily L j) L
  divisorShift : ∀ (n : ℕ) (L O : PrincipalizationAssignment.{u}),
    IsMaxOrderReduction (fun d => d < n) L O →
    IsBoundaryPositionInvariant (fun d => d ≤ n) (fun j => B.divisorFamily L j)
  maxOrderSpec : ∀ (n : ℕ) (A L : PrincipalizationAssignment.{u}),
    IsOrderReduction (fun d => d ≤ n) A L →
    IsMaxOrderReduction (fun d => d ≤ n) (B.maxOrderFamily A) A
  orderSpec : ∀ (n : ℕ) (D : ℕ → PrincipalizationAssignment.{u}) (L O : PrincipalizationAssignment.{u}),
    IsMaxOrderReduction (fun d => d < n) L O →
    (∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (D j) L) →
    IsBoundaryPositionInvariant (fun d => d ≤ n) D →
    IsOrderReduction (fun d => d ≤ n) (B.orderFamily D) L

section
variable (B : PrincipalizationRules.{u}) (L L' : OrderReductionData.{u}) (T : MarkedIdealWithBoundary.{u}) (h : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → L.maxOrderRed S = L'.maxOrderRed S)
include h

private theorem nextLevel_orderReduction_congr_consolidated163 :
    (B.nextLevel L).orderRed T = (B.nextLevel L').orderRed T := by
  have hfun : (fun (S : MarkedIdealWithBoundary.{u}) (_ : S.krullDimSucc ≤ T.krullDimSucc) (j : ℕ) =>
        B.divisorFamily L.maxOrderRed j S)
      = (fun (S : MarkedIdealWithBoundary.{u}) (_ : S.krullDimSucc ≤ T.krullDimSucc) (j : ℕ) =>
        B.divisorFamily L'.maxOrderRed j S) := by
    funext S hS j
    have hinner : (fun (S' : MarkedIdealWithBoundary.{u}) (_ : S'.krullDimSucc < S.krullDimSucc) => L.maxOrderRed S')
        = (fun (S' : MarkedIdealWithBoundary.{u}) (_ : S'.krullDimSucc < S.krullDimSucc) => L'.maxOrderRed S') := by
      funext S' h'
      exact h S' (lt_of_lt_of_le h' hS)
    show B.divisorRed S (fun S' _ => L.maxOrderRed S') j
        = B.divisorRed S (fun S' _ => L'.maxOrderRed S') j
    exact congrArg (fun f => B.divisorRed S f j) hinner
  show B.orderRed T (fun S _ j => B.divisorFamily L.maxOrderRed j S)
      = B.orderRed T (fun S _ j => B.divisorFamily L'.maxOrderRed j S)
  exact congrArg (B.orderRed T) hfun

private theorem nextLevel_maxOrderReduction_congr_consolidated163 :
    (B.nextLevel L).maxOrderRed T = (B.nextLevel L').maxOrderRed T := by
  have hfun : (fun (S : MarkedIdealWithBoundary.{u}) (_ : S.krullDimSucc ≤ T.krullDimSucc) => (B.nextLevel L).orderRed S)
      = (fun (S : MarkedIdealWithBoundary.{u}) (_ : S.krullDimSucc ≤ T.krullDimSucc) => (B.nextLevel L').orderRed S) := by
    funext S hS
    exact nextLevel_orderReduction_congr_consolidated163 B L L' S (fun S' h' => h S' (lt_of_lt_of_le h' hS))
  show B.maxOrderRed T (fun S _ => (B.nextLevel L).orderRed S)
      = B.maxOrderRed T (fun S _ => (B.nextLevel L').orderRed S)
  exact congrArg (B.maxOrderRed T) hfun


end

private theorem inputLevelData_reductions_eq_of_dim_lt_consolidated163 (B : PrincipalizationRules.{u}) :
    ∀ (d : ℕ) (T : MarkedIdealWithBoundary.{u}), T.krullDimSucc ≤ d → ∀ m M : ℕ, d < m → m ≤ M →
      (B.inputLevelData m).maxOrderRed T = (B.inputLevelData M).maxOrderRed T ∧
        (B.inputLevelData m).orderRed T = (B.inputLevelData M).orderRed T := by
  intro d
  induction d with
  | zero =>
      intro T hT m M hm hmM
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      have h0 : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc →
          (B.inputLevelData m').maxOrderRed S = (B.inputLevelData M').maxOrderRed S := by
        intro S hS
        exact absurd (lt_of_lt_of_le hS hT) (Nat.not_lt_zero _)
      exact ⟨nextLevel_maxOrderReduction_congr_consolidated163 B (B.inputLevelData m') (B.inputLevelData M') T h0,
        nextLevel_orderReduction_congr_consolidated163 B (B.inputLevelData m') (B.inputLevelData M') T h0⟩
  | succ d ih =>
      intro T hT m M hm hmM
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      have h0 : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc →
          (B.inputLevelData m').maxOrderRed S = (B.inputLevelData M').maxOrderRed S := by
        intro S hS
        exact (ih S (by omega) m' M' (by omega) (by omega)).1
      exact ⟨nextLevel_maxOrderReduction_congr_consolidated163 B (B.inputLevelData m') (B.inputLevelData M') T h0,
        nextLevel_orderReduction_congr_consolidated163 B (B.inputLevelData m') (B.inputLevelData M') T h0⟩

section
variable (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension) (n : ℕ)
include hB

private theorem inputLevelData_isMaxOrderReduction_consolidated163 :
    IsMaxOrderReduction (fun d => d < n) (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed := by
  induction n with
  | zero => exact isMaxOrderReduction_of_forall_not _ (fun m => Nat.not_lt_zero m) _ _
  | succ n ih =>
      have hord : IsOrderReduction (fun d => d ≤ n) (B.outputLevelData n).orderRed
          (B.inputLevelData n).maxOrderRed :=
        hB.orderSpec n (fun j => B.divisorFamily (B.inputLevelData n).maxOrderRed j)
          (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed ih
          (fun j => hB.divisorSpec n (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed ih j)
          (hB.divisorShift n (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed ih)
      have hmax : IsMaxOrderReduction (fun d => d ≤ n) (B.outputLevelData n).maxOrderRed
          (B.outputLevelData n).orderRed :=
        hB.maxOrderSpec n (B.outputLevelData n).orderRed (B.inputLevelData n).maxOrderRed hord
      exact hmax.mono (fun d => d < n + 1) (fun m hm => Nat.lt_succ_iff.mp hm)

theorem isOrderReduction_outputLevelData :
    IsOrderReduction (fun d => d ≤ n) (B.outputLevelData n).orderRed (B.inputLevelData n).maxOrderRed :=
  hB.orderSpec n (fun j => B.divisorFamily (B.inputLevelData n).maxOrderRed j)
    (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed
    (inputLevelData_isMaxOrderReduction_consolidated163 B hB n)
    (fun j => hB.divisorSpec n (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed
      (inputLevelData_isMaxOrderReduction_consolidated163 B hB n) j)
    (hB.divisorShift n (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed
      (inputLevelData_isMaxOrderReduction_consolidated163 B hB n))

theorem isMaxOrderReduction_outputLevelData :
    IsMaxOrderReduction (fun d => d ≤ n) (B.outputLevelData n).maxOrderRed (B.outputLevelData n).orderRed :=
  hB.maxOrderSpec n (B.outputLevelData n).orderRed (B.inputLevelData n).maxOrderRed
    (isOrderReduction_outputLevelData B hB n)


end

section
variable (B : PrincipalizationRules.{u})

theorem outputLevelData_maxOrderReduction_eq_of_le {n N : ℕ} (hnN : n ≤ N)
    (T : MarkedIdealWithBoundary.{u}) (hT : T.krullDimSucc ≤ n) :
    (B.outputLevelData N).maxOrderRed T = (B.outputLevelData n).maxOrderRed T :=
  (inputLevelData_reductions_eq_of_dim_lt_consolidated163 B n T hT (n + 1) (N + 1) (Nat.lt_succ_self n)
    (Nat.succ_le_succ hnN)).1.symm

theorem outputLevelData_maxOrderReduction_eq_at_dim (T : MarkedIdealWithBoundary.{u}) {N : ℕ}
    (hT : T.krullDimSucc ≤ N) :
    (B.outputLevelData N).maxOrderRed T = (B.outputLevelData T.krullDimSucc).maxOrderRed T :=
  outputLevelData_maxOrderReduction_eq_of_le B hT T le_rfl


end

end PrincipalizationRules

end
end
end FunctorialResolution.EmbeddedResolution
end
