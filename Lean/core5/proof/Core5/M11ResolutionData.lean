import Mathlib
import Core5.M10TransformGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

universe u v
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineResolutionConditions
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

section

namespace AffineSpacePrincipalizationData

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)

def schemeAtToSpec (i : ℕ) : S.ambientLevel i ⟶ Spec (CommRingCat.of k) :=
  S.ambientBlowups.projectionToBase i ≫ S.ambientToSpec

@[simp] theorem schemeAtToSpec_def (i : ℕ) :
    S.schemeAtToSpec i = S.ambientBlowups.projectionToBase i ≫ S.ambientToSpec := rfl

def boundary (i : ℕ) : List (S.ambientLevel i).IdealSheafData := S.principalizationSequence.boundary i

theorem boundary_def (i : ℕ) : S.boundary i = S.principalizationSequence.boundary i := rfl

def strictTransformToZero (i : ℕ) : S.strictTransform i ⟶ S.strictTransform 0 :=
  Nat.rec (motive := fun j => S.strictTransform j ⟶ S.strictTransform 0) (𝟙 _)
    (fun j ih => S.strictTransformMap j ≫ ih) i

@[simp] theorem strictTransformToZero_zero : S.strictTransformToZero 0 = 𝟙 (S.strictTransform 0) := rfl

@[simp] theorem strictTransformToZero_succ (i : ℕ) :
    S.strictTransformToZero (i + 1) = S.strictTransformMap i ≫ S.strictTransformToZero i := rfl

def strictTransformZeroToBase : S.strictTransform 0 ⟶ Y :=
  (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom

theorem strictTransformZeroToBase_def :
    S.strictTransformZeroToBase = (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom := rfl

theorem strictTransformZeroToBase_comp : S.strictTransformZeroToBase ≫ pY = S.strictTransformι 0 ≫ S.schemeAtToSpec 0 := by
  have hemb : S.emb ≫ S.ambientToSpec = pY := S.emb_comp
  have hz : S.ambientBlowups.projectionToBase 0 = S.ambientBlowups.isoZero.hom :=
    SequenceOfBlowups.projectionToBase_zero S.ambientBlowups
  have hspec := S.totalSpaceZeroIso_spec
  calc S.strictTransformZeroToBase ≫ pY
      = (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom ≫ pY := by
        rw [strictTransformZeroToBase_def, Category.assoc]
    _ = ((coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom ≫
          (S.emb ≫ S.ambientBlowups.isoZero.inv)) ≫
          (S.ambientBlowups.isoZero.hom ≫ S.ambientToSpec) := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc, hemb]
    _ = S.strictTransformι 0 ≫ S.schemeAtToSpec 0 := by
        rw [hspec, schemeAtToSpec_def, hz]

def detachedToBase (i : ℕ) : S.discardedSubscheme i ⟶ Y :=
  S.discardedι i ≫ S.strictTransformToZero i ≫ S.strictTransformZeroToBase

theorem detachedToBase_def (i : ℕ) :
    S.detachedToBase i = S.discardedι i ≫ S.strictTransformToZero i ≫ S.strictTransformZeroToBase := rfl

def StrictTransformEmptyAtLast : Prop := S.strictTransformIdeal S.ambientLength = ⊤

def DetachedSmooth : Prop :=
  ∀ i, i < S.ambientLength →
    Smooth (S.discardedι i ≫ S.strictTransformι i ≫ S.schemeAtToSpec i)

def SmoothLocusPreimageDenseInDetached : Prop :=
  ∀ i, i < S.ambientLength →
    Dense ((S.detachedToBase i).base ⁻¹' (pY.smoothLocus : Set ↥Y))

def InducedCentersLieOverSingularLocus (h : S.TransitionsAreBlowups) : Prop :=
  (S.blowupSequence h).CentersLieOver ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y)

def DetachedClopenInCenter : Prop :=
  ∀ i, i < S.ambientLength →
    ∃ (T : (S.ambientCenter i).subscheme.Opens),
      IsClosed ((T : Set ↥((S.ambientCenter i).subscheme))) ∧
      ∃ e : S.discardedSubscheme i ≅ T.toScheme,
        e.hom ≫ T.ι ≫ (S.ambientCenter i).subschemeι = S.discardedι i ≫ S.strictTransformι i

def DetachedComponentsNotInBoundary : Prop :=
  ∀ i, i < S.ambientLength → ∀ (j : ℕ) (hj : j < (S.boundary i).length),
    ∀ C ∈ irreducibleComponents ↥(S.discardedSubscheme i),
      ¬ ((S.discardedι i ≫ S.strictTransformι i).base '' C ⊆
        ((((S.boundary i).get ⟨j, hj⟩).support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) :
          Set ↥(S.ambientLevel i)))

def DetachedSingularPreimageEqBoundary : Prop :=
  ∀ i, i < S.ambientLength →
    (S.detachedToBase i).base ⁻¹' ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y) =
      (S.discardedι i ≫ S.strictTransformι i).base ⁻¹'
        (⋃ D ∈ S.boundary i,
          ((D.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) : Set ↥(S.ambientLevel i)))

def CentersHaveStrictNormalCrossingsWithBoundary : Prop :=
  ∀ i, i < S.ambientLength → HasStrictNormalCrossingsWith (S.schemeAtToSpec i) (S.ambientCenter i) (S.boundary i)

def AllLevelsSmooth : Prop :=
  ∀ i, i ≤ S.ambientLength → Smooth (S.schemeAtToSpec i)

def BoundaryInStrictNormalCrossingPosition : Prop :=
  ∀ i, i ≤ S.ambientLength → InStrictNormalCrossingPosition (S.schemeAtToSpec i) (S.boundary i)

theorem inl_comp_blowupSequence_projectionToBase (h : S.TransitionsAreBlowups) (j : ℕ) :
    (coprod.inl : S.strictTransform j ⟶ S.totalSpace j) ≫ (S.blowupSequence h).projectionToBase j =
      S.strictTransformToZero j ≫ S.strictTransformZeroToBase := by
  induction j with
  | zero =>
    have h0 : (S.blowupSequence h).projectionToBase 0 = S.totalSpaceZeroIso.hom :=
      SequenceOfBlowups.projectionToBase_zero (S.blowupSequence h)
    rw [h0, S.strictTransformToZero_zero, Category.id_comp, S.strictTransformZeroToBase_def]
  | succ j ih =>
    have hdown : (S.blowupSequence h).transitionMap (Nat.le_succ j) = S.transitionMap j := by
      rw [SequenceOfBlowups.transitionMap_def]
      exact S.tower_map_succ j
    have hd := (S.blowupSequence h).transitionMap_comp_projectionToBase (Nat.le_succ j)
    rw [hdown] at hd
    have e1 : (coprod.inl : S.strictTransform (j + 1) ⟶ S.totalSpace (j + 1)) ≫
          (S.blowupSequence h).projectionToBase (j + 1)
        = ((coprod.inl : S.strictTransform (j + 1) ⟶ S.totalSpace (j + 1)) ≫ S.transitionMap j)
            ≫ (S.blowupSequence h).projectionToBase j :=
      ((Category.assoc (coprod.inl : S.strictTransform (j + 1) ⟶ S.totalSpace (j + 1))
            (S.transitionMap j) ((S.blowupSequence h).projectionToBase j)).trans
        (congrArg (fun f : S.totalSpace (j + 1) ⟶ Y =>
          (coprod.inl : S.strictTransform (j + 1) ⟶ S.totalSpace (j + 1)) ≫ f) hd)).symm
    have e2 : ((coprod.inl : S.strictTransform (j + 1) ⟶ S.totalSpace (j + 1)) ≫ S.transitionMap j)
            ≫ (S.blowupSequence h).projectionToBase j
        = (S.strictTransformMap j ≫ (coprod.inl : S.strictTransform j ⟶ S.totalSpace j))
            ≫ (S.blowupSequence h).projectionToBase j :=
      congrArg (fun g : S.strictTransform (j + 1) ⟶ S.totalSpace j =>
        g ≫ (S.blowupSequence h).projectionToBase j) (S.inl_comp_transitionMap j)
    have e3 : (S.strictTransformMap j ≫ (coprod.inl : S.strictTransform j ⟶ S.totalSpace j))
            ≫ (S.blowupSequence h).projectionToBase j
        = S.strictTransformMap j ≫ ((coprod.inl : S.strictTransform j ⟶ S.totalSpace j)
            ≫ (S.blowupSequence h).projectionToBase j) :=
      Category.assoc _ _ _
    have e4 : S.strictTransformMap j ≫ ((coprod.inl : S.strictTransform j ⟶ S.totalSpace j)
            ≫ (S.blowupSequence h).projectionToBase j)
        = S.strictTransformMap j ≫ (S.strictTransformToZero j ≫ S.strictTransformZeroToBase) :=
      congrArg (fun g : S.strictTransform j ⟶ Y => S.strictTransformMap j ≫ g) ih
    have e5 : S.strictTransformMap j ≫ (S.strictTransformToZero j ≫ S.strictTransformZeroToBase)
        = S.strictTransformToZero (j + 1) ≫ S.strictTransformZeroToBase := by
      rw [S.strictTransformToZero_succ j, Category.assoc]
    exact e1.trans (e2.trans (e3.trans (e4.trans e5)))

end AffineSpacePrincipalizationData

def AffineStrictTransformEmptyAtLast (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).StrictTransformEmptyAtLast

def AffineDetachedSmooth (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).DetachedSmooth

def AffineSmoothLocusPreimageDenseInDetached (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).SmoothLocusPreimageDenseInDetached

def AffineCentersLieOverSingularLocus (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (hPrincipalization : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).InducedCentersLieOverSingularLocus (hPrincipalization k Y pY)

def AffineDetachedClopenInCenter (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).DetachedClopenInCenter

def AffineDetachedComponentsNotInBoundary (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).DetachedComponentsNotInBoundary

def AffineDetachedSingularPreimageEqBoundary (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).DetachedSingularPreimageEqBoundary

def AffineCentersHaveStrictNormalCrossingsWithBoundary (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).CentersHaveStrictNormalCrossingsWithBoundary

def AffineAllLevelsSmooth (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).AllLevelsSmooth

def AffineBoundaryInStrictNormalCrossingPosition (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).BoundaryInStrictNormalCrossingPosition

private theorem smooth_from_initial_consolidated254 {Z : Scheme.{u}} (f : (⊥_ Scheme.{u}) ⟶ Z) :
    Smooth f := by
  have hf : f = initial.to Z := initial.hom_ext _ _
  rw [hf]
  infer_instance

private theorem preimage_comp_base_eq_preimage_preimage_consolidated254 {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (W : Set ↥C) :
    (f ≫ g).base ⁻¹' W = f.base ⁻¹' (g.base ⁻¹' W) := by
  ext x
  simp

private theorem dense_of_isEmpty_consolidated254 {α : Type u} [TopologicalSpace α] [IsEmpty α]
    (T : Set α) : Dense T := fun x => isEmptyElim x

private theorem isStrictNormalCrossingsDivisor_of_isEmpty_consolidated254 {X : Scheme.{u}} (hX : IsEmpty ↥X)
    (D : X.IdealSheafData) : IsStrictNormalCrossingsDivisor D := fun x => (hX.false x).elim

section
variable {X Z : Scheme.{u}} {f g : X ⟶ Z} (h : f = g)
include h

private theorem smooth_of_eq_consolidated254 (hg : Smooth g) : Smooth f := by
  rw [h]
  exact hg

private theorem dense_preimage_of_eq_consolidated254 (W : Set ↥Z)
    (hg : Dense (g.base ⁻¹' W)) : Dense (f.base ⁻¹' W) := by
  rw [h]
  exact hg

private theorem isStrictNormalCrossingsDivisor_reducedInverseImage_of_eq_consolidated254 (W : TopologicalSpace.Closeds ↥Z) (hg : IsStrictNormalCrossingsDivisor (reducedInverseImage g W)) :
    IsStrictNormalCrossingsDivisor (reducedInverseImage f W) := by
  rw [h]
  exact hg


end

private theorem dense_of_dense_preimage_inl_inr_consolidated254 {A B : Scheme.{u}} (T : Set ↥(A ⨿ B))
    (hA : Dense ((coprod.inl : A ⟶ A ⨿ B).base ⁻¹' T))
    (hB : Dense ((coprod.inr : B ⟶ A ⨿ B).base ⁻¹' T)) : Dense T := by
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨z, hz⟩ := hne
  by_cases hzl : z ∈ Set.range ⇑(coprod.inl : A ⟶ A ⨿ B).base
  · obtain ⟨a, ha⟩ := hzl
    have hopen : IsOpen ((coprod.inl : A ⟶ A ⨿ B).base ⁻¹' U) :=
      hU.preimage (Scheme.Hom.continuous _)
    have hne2 : ((coprod.inl : A ⟶ A ⨿ B).base ⁻¹' U).Nonempty := by
      refine ⟨a, ?_⟩
      rw [Set.mem_preimage, ha]
      exact hz
    obtain ⟨x, hxU, hxT⟩ := (dense_iff_inter_open.mp hA) _ hopen hne2
    exact ⟨(coprod.inl : A ⟶ A ⨿ B).base x, hxU, hxT⟩
  · have hzr : z ∈ Set.range ⇑(coprod.inr : B ⟶ A ⨿ B).base := by
      rw [Blowup.range_coprod_inr_eq_compl]
      exact hzl
    obtain ⟨b, hb⟩ := hzr
    have hopen : IsOpen ((coprod.inr : B ⟶ A ⨿ B).base ⁻¹' U) :=
      hU.preimage (Scheme.Hom.continuous _)
    have hne2 : ((coprod.inr : B ⟶ A ⨿ B).base ⁻¹' U).Nonempty := by
      refine ⟨b, ?_⟩
      rw [Set.mem_preimage, hb]
      exact hz
    obtain ⟨x, hxU, hxT⟩ := (dense_iff_inter_open.mp hB) _ hopen hne2
    exact ⟨(coprod.inr : B ⟶ A ⨿ B).base x, hxU, hxT⟩

private theorem dense_preimage_of_dense_preimage_inl_inr_comp_consolidated254 {A B Z : Scheme.{u}} (g : A ⨿ B ⟶ Z) (W : Set ↥Z)
    (hA : Dense (((coprod.inl : A ⟶ A ⨿ B) ≫ g).base ⁻¹' W))
    (hB : Dense (((coprod.inr : B ⟶ A ⨿ B) ≫ g).base ⁻¹' W)) :
    Dense (g.base ⁻¹' W) := by
  refine dense_of_dense_preimage_inl_inr_consolidated254 _ ?_ ?_
  · rwa [preimage_comp_base_eq_preimage_preimage_consolidated254] at hA
  · rwa [preimage_comp_base_eq_preimage_preimage_consolidated254] at hB

section
variable {P Q Z : Scheme.{u}} (a : P ⟶ Z) (b : Q ⟶ Z)

private theorem dense_preimage_coprod_desc_consolidated254 (W : Set ↥Z) (ha : Dense (a.base ⁻¹' W)) (hb : Dense (b.base ⁻¹' W)) :
    Dense ((coprod.desc a b).base ⁻¹' W) := by
  refine dense_preimage_of_dense_preimage_inl_inr_comp_consolidated254 (coprod.desc a b) W ?_ ?_
  · rw [coprod.inl_desc]
    exact ha
  · rw [coprod.inr_desc]
    exact hb

private theorem isStrictNormalCrossingsDivisor_reducedInverseImage_coprod_desc_consolidated254 (W : TopologicalSpace.Closeds ↥Z)
    (ha : IsStrictNormalCrossingsDivisor (reducedInverseImage a W)) (hb : IsStrictNormalCrossingsDivisor (reducedInverseImage b W)) :
    IsStrictNormalCrossingsDivisor (reducedInverseImage (coprod.desc a b) W) := by
  refine IsStrictNormalCrossingsDivisor.reducedInverseImage_coprod (coprod.desc a b) W ?_ ?_
  · rw [coprod.inl_desc]
    exact ha
  · rw [coprod.inr_desc]
    exact hb


end

section
variable {A P Z : Scheme.{u}} (g : A ⨿ P ⟶ Z)

private theorem smooth_of_isEmpty_left_consolidated254 (hA : IsEmpty ↥A)
    (hP : Smooth ((coprod.inr : P ⟶ A ⨿ P) ≫ g)) :
    Smooth g := by
  have hdesc : coprod.desc ((coprod.inl : A ⟶ A ⨿ P) ≫ g)
      ((coprod.inr : P ⟶ A ⨿ P) ≫ g) = g :=
    coprod.hom_ext (by rw [coprod.inl_desc]) (by rw [coprod.inr_desc])
  have hA' : Smooth ((coprod.inl : A ⟶ A ⨿ P) ≫ g) := by
    have := hA
    exact Blowup.smooth_of_isEmpty _
  exact smooth_of_eq_consolidated254 hdesc.symm (Blowup.smooth_coprod_desc _ _ hA' hP)

private theorem dense_preimage_of_isEmpty_left_consolidated254 (W : Set ↥Z)
    (hA : IsEmpty ↥A)
    (hP : Dense (((coprod.inr : P ⟶ A ⨿ P) ≫ g).base ⁻¹' W)) : Dense (g.base ⁻¹' W) := by
  have := hA
  exact dense_preimage_of_dense_preimage_inl_inr_comp_consolidated254 g W (dense_of_isEmpty_consolidated254 _) hP

private theorem isStrictNormalCrossingsDivisor_reducedInverseImage_of_isEmpty_left_consolidated254 (W : TopologicalSpace.Closeds ↥Z) (hA : IsEmpty ↥A)
    (hP : IsStrictNormalCrossingsDivisor (reducedInverseImage ((coprod.inr : P ⟶ A ⨿ P) ≫ g) W)) :
    IsStrictNormalCrossingsDivisor (reducedInverseImage g W) :=
  IsStrictNormalCrossingsDivisor.reducedInverseImage_coprod g W (isStrictNormalCrossingsDivisor_of_isEmpty_consolidated254 hA _) hP


end

private theorem smooth_eqToHom_comp_comp_consolidated254 {X₁ X₂ Z W : Scheme.{u}} (e : X₁ = X₂) (g : X₂ ⟶ Z)
    (p : Z ⟶ W) (hg : Smooth (g ≫ p)) :
    Smooth ((eqToHom e ≫ g) ≫ p) := by
  subst e
  rw [eqToHom_refl, Category.id_comp]
  exact hg

section
variable {X₁ X₂ Z : Scheme.{u}} (e : X₁ = X₂) (g : X₂ ⟶ Z)

private theorem isProper_eqToHom_comp_consolidated254 (hg : IsProper g) : IsProper (eqToHom e ≫ g) := by
  subst e
  rw [eqToHom_refl, Category.id_comp]
  exact hg

private theorem dense_preimage_eqToHom_comp_consolidated254 (W : Set ↥Z) (hg : Dense (g.base ⁻¹' W)) : Dense ((eqToHom e ≫ g).base ⁻¹' W) := by
  subst e
  rw [eqToHom_refl, Category.id_comp]
  exact hg

private theorem isStrictNormalCrossingsDivisor_reducedInverseImage_eqToHom_comp_consolidated254 (W : TopologicalSpace.Closeds ↥Z) (hg : IsStrictNormalCrossingsDivisor (reducedInverseImage g W)) :
    IsStrictNormalCrossingsDivisor (reducedInverseImage (eqToHom e ≫ g) W) := by
  subst e
  rw [eqToHom_refl, Category.id_comp]
  exact hg


end

private theorem image_mem_irreducibleComponents_of_continuous_inverse_consolidated254 {α β : Type u} [TopologicalSpace α]
    [TopologicalSpace β] (f : α → β) (g : β → α) (hf : Continuous f) (hg : Continuous g)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y)
    {C : Set β} (hC : C ∈ irreducibleComponents β) :
    g '' C ∈ irreducibleComponents α := by
  obtain ⟨hirr, hmax⟩ := hC
  refine ⟨hirr.image g hg.continuousOn, ?_⟩
  intro b hb hsub
  have hb' : IsIrreducible (f '' b) := hb.image f hf.continuousOn
  have hCsub : C ⊆ f '' b := by
    intro y hy
    exact ⟨g y, hsub ⟨y, hy, rfl⟩, hfg y⟩
  have hmax' := hmax hb' hCsub
  intro x hx
  exact ⟨f x, hmax' ⟨x, hx, rfl⟩, hgf x⟩

private theorem support_prod_eq_iUnion_consolidated254 {X : Scheme.{u}} (L : List X.IdealSheafData) :
    ((L.prod.support : TopologicalSpace.Closeds ↥X) : Set ↥X)
      = ⋃ D ∈ L, ((D.support : TopologicalSpace.Closeds ↥X) : Set ↥X) := by
  induction L with
  | nil =>
      rw [Blowup.idealSheafData_prod_nil]
      simp [AlgebraicGeometry.Scheme.IdealSheafData.support_top]
  | cons D E ih =>
      rw [Blowup.idealSheafData_prod_cons]
      simp [AlgebraicGeometry.Scheme.IdealSheafData.support_mul, ih]

private theorem support_comap_eq_preimage_consolidated254 {X Z : Scheme.{u}} (f : X ⟶ Z) (I : Z.IdealSheafData) :
    (((I.comap f).support : TopologicalSpace.Closeds ↥X) : Set ↥X)
      = f.base ⁻¹' ((I.support : TopologicalSpace.Closeds ↥Z) : Set ↥Z) := by
  simp [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]

private theorem isProper_projectionToBase_consolidated254 (hproper : FunctorialResolution.Blowup.BlowupIsProper.{u}) {X : Scheme.{u}}
    [IsNoetherian X] (s : SequenceOfBlowups X) :
    ∀ i : ℕ, i ≤ s.length → IsProper (s.projectionToBase i) := by
  intro i
  induction i with
  | zero =>
      intro _
      rw [SequenceOfBlowups.projectionToBase_zero s]
      infer_instance
  | succ n ih =>
      intro hn
      have hlt : n < s.length := hn
      have : IsNoetherian (s.schemeAt n) :=
        isNoetherian_schemeAt s n (le_of_lt hlt)
      have : IsProper (s.projectionToBase n) := ih (le_of_lt hlt)
      have : IsProper (s.transitionMapSucc n) :=
        hproper _ _ _ _ (s.isBlowupAlongIdealSheaf_blowupMorphism n hlt)
      have h1 : s.transitionMapSucc n ≫ s.projectionToBase n = s.projectionToBase (n + 1) := by
        rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
        exact s.transitionMap_comp_projectionToBase (Nat.le_succ n)
      rw [← h1]
      infer_instance

section
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY)

private theorem strictTransformToZero_comp_schemeAtToSpec_consolidated254 :
    ∀ i : ℕ, S.strictTransformToZero i ≫ S.strictTransformι 0 ≫ S.schemeAtToSpec 0 = S.strictTransformι i ≫ S.schemeAtToSpec i := by
  intro i
  induction i with
  | zero => rw [S.strictTransformToZero_zero, Category.id_comp]
  | succ j ih =>
      have h2 : S.ambientBlowupMorphism j ≫ S.ambientBlowups.projectionToBase j = S.ambientBlowups.projectionToBase (j + 1) := by
        rw [show S.ambientBlowupMorphism j = S.ambientBlowups.transitionMapSucc j from rfl, SequenceOfBlowups.blowupMorphism_eq_transitionMap]
        exact S.ambientBlowups.transitionMap_comp_projectionToBase (Nat.le_succ j)
      have h1 : S.ambientBlowupMorphism j ≫ S.schemeAtToSpec j = S.schemeAtToSpec (j + 1) := by
        rw [S.schemeAtToSpec_def j, S.schemeAtToSpec_def (j + 1), ← Category.assoc, h2]
      calc S.strictTransformToZero (j + 1) ≫ S.strictTransformι 0 ≫ S.schemeAtToSpec 0
          = S.strictTransformMap j ≫ (S.strictTransformToZero j ≫ S.strictTransformι 0 ≫ S.schemeAtToSpec 0) := by
            rw [S.strictTransformToZero_succ j, Category.assoc]
        _ = S.strictTransformMap j ≫ S.strictTransformι j ≫ S.schemeAtToSpec j := by rw [ih]
        _ = (S.strictTransformMap j ≫ S.strictTransformι j) ≫ S.schemeAtToSpec j := by rw [Category.assoc]
        _ = (S.strictTransformι (j + 1) ≫ S.ambientBlowupMorphism j) ≫ S.schemeAtToSpec j := by rw [S.strictTransformMap_comp_strictTransformι]
        _ = S.strictTransformι (j + 1) ≫ (S.ambientBlowupMorphism j ≫ S.schemeAtToSpec j) := by rw [Category.assoc]
        _ = S.strictTransformι (j + 1) ≫ S.schemeAtToSpec (j + 1) := by rw [h1]

private theorem detachedToBase_comp_eq_consolidated254 (i : ℕ) :
    S.detachedToBase i ≫ pY = S.discardedι i ≫ S.strictTransformι i ≫ S.schemeAtToSpec i := by
  rw [S.detachedToBase_def i, Category.assoc, Category.assoc, S.strictTransformZeroToBase_comp,
    strictTransformToZero_comp_schemeAtToSpec_consolidated254 S i]


end

private theorem inr_comp_eq_coprod_desc_consolidated254 {A₁ A₀ P Q Z : Scheme.{u}} (φ : Q ⟶ A₀)
    (τ : (A₁ ⨿ (P ⨿ Q)) ⟶ (A₀ ⨿ P)) (u : (A₁ ⨿ (P ⨿ Q)) ⟶ Z) (v : (A₀ ⨿ P) ⟶ Z)
    (w : Q ⟶ Z)
    (hτ : (coprod.inr : (P ⨿ Q) ⟶ (A₁ ⨿ (P ⨿ Q))) ≫ τ
        = coprod.desc (coprod.inr : P ⟶ (A₀ ⨿ P)) (φ ≫ (coprod.inl : A₀ ⟶ (A₀ ⨿ P))))
    (hv : τ ≫ v = u)
    (hw : φ ≫ ((coprod.inl : A₀ ⟶ (A₀ ⨿ P)) ≫ v) = w) :
    (coprod.inr : (P ⨿ Q) ⟶ (A₁ ⨿ (P ⨿ Q))) ≫ u
      = coprod.desc ((coprod.inr : P ⟶ (A₀ ⨿ P)) ≫ v) w := by
  rw [← hw, ← hv, ← Category.assoc (coprod.inr : (P ⨿ Q) ⟶ (A₁ ⨿ (P ⨿ Q))) τ v, hτ]
  apply coprod.hom_ext <;> simp

section
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]

private theorem isStrictNormalCrossingsDivisor_reducedInverseImage_detachedToBase_consolidated254 [QuasiCompact pY]
    (S : AffineSpacePrincipalizationData k Y pY)
    (hClopen : S.DetachedClopenInCenter) (hNotInBoundary : S.DetachedComponentsNotInBoundary)
    (hSing : S.DetachedSingularPreimageEqBoundary) (hCentersSNC : S.CentersHaveStrictNormalCrossingsWithBoundary) (hBoundarySNC : S.BoundaryInStrictNormalCrossingPosition)
    (hLevels : S.AllLevelsSmooth) (hsncClopen : StrictNormalCrossingsRestrictToClopen.{u})
    (i : ℕ) (hi : i < S.ambientLength) :
    IsStrictNormalCrossingsDivisor (reducedInverseImage (S.detachedToBase i) (smoothLocusComplement pY)) := by
  obtain ⟨T, hTclosed, e, he⟩ := hClopen i hi
  have : Smooth (S.schemeAtToSpec i) := hLevels i (le_of_lt hi)
  have hoi : IsOpenImmersion e.inv := inferInstance
  have hgf : ∀ x : ↥(S.discardedSubscheme i), e.inv.base (e.hom.base x) = x := by
    intro x
    simp
  have hfg : ∀ x : ↥(T.toScheme), e.hom.base (e.inv.base x) = x := by
    intro x
    simp
  have hmor : e.inv ≫ (S.discardedι i ≫ S.strictTransformι i) = T.ι ≫ (S.ambientCenter i).subschemeι := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hbase : ∀ x : ↥(T.toScheme),
      (S.discardedι i ≫ S.strictTransformι i).base (e.inv.base x)
        = (T.ι ≫ (S.ambientCenter i).subschemeι).base x := by
    intro x
    have hh := congrArg (fun f : T.toScheme ⟶ S.ambientLevel i => f.base x) hmor
    simpa using hh
  have hcond : ∀ D ∈ S.boundary i, ∀ C ∈ irreducibleComponents ↥(T.toScheme),
      ¬ ((T.ι ≫ (S.ambientCenter i).subschemeι).base '' C ⊆
        ((D.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) : Set ↥(S.ambientLevel i))) := by
    intro D hD C hC hsub
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hD
    have hC' : e.inv.base '' C ∈ irreducibleComponents ↥(S.discardedSubscheme i) :=
      image_mem_irreducibleComponents_of_continuous_inverse_consolidated254 e.hom.base e.inv.base
        (Scheme.Hom.continuous _) (Scheme.Hom.continuous _) hgf hfg hC
    have himg : (S.discardedι i ≫ S.strictTransformι i).base '' (e.inv.base '' C)
        = (T.ι ≫ (S.ambientCenter i).subschemeι).base '' C := by
      rw [Set.image_image]
      exact Set.image_congr (fun x _ => hbase x)
    have hoff := hNotInBoundary i hi j hj (e.inv.base '' C) hC'
    rw [List.get_eq_getElem] at hoff
    exact hoff (by rw [himg]; exact hsub)
  have hsnc1 := hsncClopen k (S.ambientLevel i) (S.schemeAtToSpec i) (S.boundary i) (S.ambientCenter i)
      (hBoundarySNC i (le_of_lt hi)) (hCentersSNC i hi) T hTclosed hcond
  have hpre : ∀ W : Set ↥(S.ambientLevel i),
      (T.ι ≫ (S.ambientCenter i).subschemeι).base ⁻¹' W
        = e.inv.base ⁻¹' ((S.discardedι i ≫ S.strictTransformι i).base ⁻¹' W) := by
    intro W
    ext x
    simp only [Set.mem_preimage]
    rw [← hbase x]
  have hJsupp : (((((S.boundary i).prod.comap
        (T.ι ≫ (S.ambientCenter i).subschemeι)).support) :
          TopologicalSpace.Closeds ↥(T.toScheme)) : Set ↥(T.toScheme))
      = (T.ι ≫ (S.ambientCenter i).subschemeι).base ⁻¹'
        (⋃ D ∈ S.boundary i,
          ((D.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) : Set ↥(S.ambientLevel i))) := by
    rw [support_comap_eq_preimage_consolidated254, support_prod_eq_iUnion_consolidated254]
  have hrp : reducedInverseImage (e.inv ≫ S.detachedToBase i) (smoothLocusComplement pY)
      = ((S.boundary i).prod.comap (T.ι ≫ (S.ambientCenter i).subschemeι)).radical := by
    refine reducedInverseImage_eq_radical _ _ _ ?_
    rw [hJsupp, hpre, ← hSing i hi, preimage_comp_base_eq_preimage_preimage_consolidated254]
  refine IsStrictNormalCrossingsDivisor.of_isOpenImmersion_jointly_surjective (reducedInverseImage (S.detachedToBase i) (smoothLocusComplement pY))
      (fun _ : Unit => T.toScheme) (fun _ => e.inv) (fun _ => hoi) ?_ ?_
  · intro x
    exact ⟨(), e.hom.base x, hgf x⟩
  · intro _
    rw [comap_reducedInverseImage_of_isOpenImmersion e.inv (S.detachedToBase i) (smoothLocusComplement pY), hrp]
    exact hsnc1

private theorem smooth_discardedUnion_comp_consolidated254 (S : AffineSpacePrincipalizationData k Y pY)
    (G : ∀ j, S.discardedUnion j ⟶ Y)
    (hG : ∀ j, G (j + 1) = coprod.desc (G j) (S.detachedToBase j))
    (hSmooth : S.DetachedSmooth) :
    ∀ j, j ≤ S.ambientLength → Smooth (G j ≫ pY) := by
  intro j
  induction j with
  | zero =>
      intro _
      exact smooth_from_initial_consolidated254 (G 0 ≫ pY)
  | succ j ih =>
      intro hj
      have hj' : j < S.ambientLength := hj
      have e1 : G (j + 1) ≫ pY
          = coprod.desc (G j ≫ pY) (S.detachedToBase j ≫ pY) :=
        (congrArg (fun t : S.discardedUnion (j + 1) ⟶ Y => t ≫ pY) (hG j)).trans
          (coprod.desc_comp pY (G j) (S.detachedToBase j))
      refine smooth_of_eq_consolidated254 e1 ?_
      refine Blowup.smooth_coprod_desc _ _ (ih (le_of_lt hj')) ?_
      exact smooth_of_eq_consolidated254 (detachedToBase_comp_eq_consolidated254 S j) (hSmooth j hj')

private theorem dense_preimage_smoothLocus_of_discardedUnion_consolidated254 (S : AffineSpacePrincipalizationData k Y pY)
    (G : ∀ j, S.discardedUnion j ⟶ Y)
    (hG : ∀ j, G (j + 1) = coprod.desc (G j) (S.detachedToBase j))
    (hDense : S.SmoothLocusPreimageDenseInDetached) :
    ∀ j, j ≤ S.ambientLength → Dense ((G j).base ⁻¹' (pY.smoothLocus : Set ↥Y)) := by
  intro j
  induction j with
  | zero =>
      intro _
      have : IsEmpty ↥(S.discardedUnion 0) := (inferInstance : IsEmpty ↥(⊥_ Scheme.{u}))
      exact dense_of_isEmpty_consolidated254 _
  | succ j ih =>
      intro hj
      have hj' : j < S.ambientLength := hj
      refine dense_preimage_of_eq_consolidated254 (hG j) _ ?_
      exact dense_preimage_coprod_desc_consolidated254 _ _ _ (ih (le_of_lt hj')) (hDense j hj')

private theorem isStrictNormalCrossingsDivisor_reducedInverseImage_discardedUnion_consolidated254 [QuasiCompact pY]
    (S : AffineSpacePrincipalizationData k Y pY) (G : ∀ j, S.discardedUnion j ⟶ Y)
    (hG : ∀ j, G (j + 1) = coprod.desc (G j) (S.detachedToBase j))
    (hClopen : S.DetachedClopenInCenter) (hNotInBoundary : S.DetachedComponentsNotInBoundary)
    (hSing : S.DetachedSingularPreimageEqBoundary) (hCentersSNC : S.CentersHaveStrictNormalCrossingsWithBoundary) (hBoundarySNC : S.BoundaryInStrictNormalCrossingPosition)
    (hLevels : S.AllLevelsSmooth) (hsncClopen : StrictNormalCrossingsRestrictToClopen.{u}) :
    ∀ j, j ≤ S.ambientLength → IsStrictNormalCrossingsDivisor (reducedInverseImage (G j) (smoothLocusComplement pY)) := by
  intro j
  induction j with
  | zero =>
      intro _
      exact isStrictNormalCrossingsDivisor_of_isEmpty_consolidated254 (inferInstance : IsEmpty ↥(⊥_ Scheme.{u}))
        (reducedInverseImage (G 0) (smoothLocusComplement pY))
  | succ j ih =>
      intro hj
      have hj' : j < S.ambientLength := hj
      refine isStrictNormalCrossingsDivisor_reducedInverseImage_of_eq_consolidated254 (hG j) _ ?_
      exact isStrictNormalCrossingsDivisor_reducedInverseImage_coprod_desc_consolidated254 _ _ _ (ih (le_of_lt hj'))
        (isStrictNormalCrossingsDivisor_reducedInverseImage_detachedToBase_consolidated254 S hClopen hNotInBoundary hSing hCentersSNC hBoundarySNC hLevels
          hsncClopen j hj')

private theorem isStrongResolution_blowupSequenceWithoutIsos_consolidated254 [QuasiCompact pY]
    (S : AffineSpacePrincipalizationData k Y pY) (h : S.TransitionsAreBlowups)
    (hEmpty : S.StrictTransformEmptyAtLast) (hSmooth : S.DetachedSmooth) (hDense : S.SmoothLocusPreimageDenseInDetached)
    (hCenters : S.InducedCentersLieOverSingularLocus h) (hClopen : S.DetachedClopenInCenter)
    (hNotInBoundary : S.DetachedComponentsNotInBoundary) (hSing : S.DetachedSingularPreimageEqBoundary)
    (hCentersSNC : S.CentersHaveStrictNormalCrossingsWithBoundary) (hLevels : S.AllLevelsSmooth) (hBoundarySNC : S.BoundaryInStrictNormalCrossingPosition)
    (hsncClopen : StrictNormalCrossingsRestrictToClopen.{u}) (hproper : FunctorialResolution.Blowup.BlowupIsProper.{u}) :
    IsStrongResolution k Y pY (S.blowupSequenceWithoutIsos h) := by
  have : IsNoetherianRing ↑(CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  have : IsNoetherian (Spec (CommRingCat.of k)) := inferInstance
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType pY
  have hFeq : ∀ j : ℕ, S.transitionMap j ≫ (S.blowupSequence h).projectionToBase j
      = (S.blowupSequence h).projectionToBase (j + 1) := by
    intro j
    have hdown : (S.blowupSequence h).transitionMap (Nat.le_succ j) = S.transitionMap j := by
      rw [SequenceOfBlowups.transitionMap_def]
      exact S.tower_map_succ j
    have hd := (S.blowupSequence h).transitionMap_comp_projectionToBase (Nat.le_succ j)
    rw [hdown] at hd
    exact hd
  have hWeq : ∀ j : ℕ, S.discardedι j ≫ ((coprod.inl : S.strictTransform j ⟶ S.totalSpace j) ≫
      (S.blowupSequence h).projectionToBase j) = S.detachedToBase j := by
    intro j
    rw [S.inl_comp_blowupSequence_projectionToBase h j]
    exact (S.detachedToBase_def j).symm
  have hGeq : ∀ j : ℕ,
      ((coprod.inr : S.discardedUnion (j + 1) ⟶ S.totalSpace (j + 1)) ≫
          (S.blowupSequence h).projectionToBase (j + 1))
        = coprod.desc ((coprod.inr : S.discardedUnion j ⟶ S.totalSpace j) ≫
            (S.blowupSequence h).projectionToBase j) (S.detachedToBase j) := fun j =>
    inr_comp_eq_coprod_desc_consolidated254 (S.discardedι j) (S.transitionMap j) ((S.blowupSequence h).projectionToBase (j + 1))
      ((S.blowupSequence h).projectionToBase j) (S.detachedToBase j) (coprod.inr_desc _ _) (hFeq j) (hWeq j)
  have hStrictEmpty : IsEmpty ↥(S.strictTransform S.ambientLength) := by
    have h2 : Set.range ⇑(S.strictTransformι S.ambientLength)
        = (((S.strictTransformIdeal S.ambientLength).support : TopologicalSpace.Closeds ↥(S.ambientLevel S.ambientLength)) :
          Set ↥(S.ambientLevel S.ambientLength)) :=
      AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι _
    have h3 : (((S.strictTransformIdeal S.ambientLength).support : TopologicalSpace.Closeds ↥(S.ambientLevel S.ambientLength)) :
        Set ↥(S.ambientLevel S.ambientLength)) = ∅ := by
      have h1 : S.strictTransformIdeal S.ambientLength = ⊤ := hEmpty
      simp [h1, AlgebraicGeometry.Scheme.IdealSheafData.support_top]
    rw [h3] at h2
    exact Set.range_eq_empty_iff.mp h2
  have hLastStruct : (S.blowupSequenceWithoutIsos h).lastStructMap
      = eqToHom (SequenceOfBlowups.withoutIsoBlowups_lastObj (S.blowupSequence h)) ≫ (S.blowupSequence h).lastStructMap :=
    SequenceOfBlowups.withoutIsoBlowups_lastStructMap (S.blowupSequence h)
  have hLastProjection : (S.blowupSequence h).lastStructMap = (S.blowupSequence h).projectionToBase S.ambientLength :=
    SequenceOfBlowups.lastStructMap_eq_projectionToBase (S.blowupSequence h)
  have hSmoothDiscarded : Smooth
      (((coprod.inr : S.discardedUnion S.ambientLength ⟶ S.totalSpace S.ambientLength) ≫
        (S.blowupSequence h).projectionToBase S.ambientLength) ≫ pY) :=
    smooth_discardedUnion_comp_consolidated254 S
      (fun j => (coprod.inr : S.discardedUnion j ⟶ S.totalSpace j) ≫ (S.blowupSequence h).projectionToBase j)
      hGeq hSmooth S.ambientLength le_rfl
  have hDenseDiscarded : Dense ((((coprod.inr : S.discardedUnion S.ambientLength ⟶ S.totalSpace S.ambientLength) ≫
      (S.blowupSequence h).projectionToBase S.ambientLength)).base ⁻¹' (pY.smoothLocus : Set ↥Y)) :=
    dense_preimage_smoothLocus_of_discardedUnion_consolidated254 S
      (fun j => (coprod.inr : S.discardedUnion j ⟶ S.totalSpace j) ≫ (S.blowupSequence h).projectionToBase j)
      hGeq hDense S.ambientLength le_rfl
  have hSNCDiscarded : IsStrictNormalCrossingsDivisor (reducedInverseImage
      ((coprod.inr : S.discardedUnion S.ambientLength ⟶ S.totalSpace S.ambientLength) ≫
        (S.blowupSequence h).projectionToBase S.ambientLength) (smoothLocusComplement pY)) :=
    isStrictNormalCrossingsDivisor_reducedInverseImage_discardedUnion_consolidated254 S
      (fun j => (coprod.inr : S.discardedUnion j ⟶ S.totalSpace j) ≫ (S.blowupSequence h).projectionToBase j)
      hGeq hClopen hNotInBoundary hSing hCentersSNC hBoundarySNC hLevels hsncClopen S.ambientLength le_rfl
  have hstruct : Smooth ((S.blowupSequence h).projectionToBase S.ambientLength ≫ pY) := by
    refine smooth_of_isEmpty_left_consolidated254 (A := S.strictTransform S.ambientLength) (P := S.discardedUnion S.ambientLength)
      ((S.blowupSequence h).projectionToBase S.ambientLength ≫ pY) hStrictEmpty ?_
    exact smooth_of_eq_consolidated254 (Category.assoc _ _ _).symm hSmoothDiscarded
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hLastStruct, hLastProjection]
    refine smooth_eqToHom_comp_comp_consolidated254 _ _ _ ?_
    exact hstruct
  · rw [hLastStruct, hLastProjection]
    exact isProper_eqToHom_comp_consolidated254 _ _
      (isProper_projectionToBase_consolidated254 hproper (S.blowupSequence h) S.ambientLength le_rfl)
  · exact isIso_restrict_lastStructMap_smoothLocus pY _ (SequenceOfBlowups.withoutIsoBlowups_centersLieOver _ hCenters)
  · rw [hLastStruct, hLastProjection]
    refine dense_preimage_eqToHom_comp_consolidated254 _ _ _ ?_
    exact dense_preimage_of_isEmpty_left_consolidated254 (A := S.strictTransform S.ambientLength) (P := S.discardedUnion S.ambientLength)
      _ _ hStrictEmpty hDenseDiscarded
  · exact SequenceOfBlowups.withoutIsoBlowups_centersLieOver _ hCenters
  · rw [hLastStruct, hLastProjection]
    refine isStrictNormalCrossingsDivisor_reducedInverseImage_eqToHom_comp_consolidated254 _ _ _ ?_
    exact isStrictNormalCrossingsDivisor_reducedInverseImage_of_isEmpty_left_consolidated254 (A := S.strictTransform S.ambientLength)
      (P := S.discardedUnion S.ambientLength) _ _ hStrictEmpty hSNCDiscarded


end

theorem isStrongResolution_blowupSequenceWithoutIsos_ofAffine (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hPrincipalization : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm)
    (hEmpty : AffineStrictTransformEmptyAtLast A hemb hsnc hsm)
    (hSmooth : AffineDetachedSmooth A hemb hsnc hsm)
    (hDense : AffineSmoothLocusPreimageDenseInDetached A hemb hsnc hsm)
    (hCenters : AffineCentersLieOverSingularLocus A hemb hsnc hsm hPrincipalization)
    (hClopen : AffineDetachedClopenInCenter A hemb hsnc hsm)
    (hNotInBoundary : AffineDetachedComponentsNotInBoundary A hemb hsnc hsm)
    (hSing : AffineDetachedSingularPreimageEqBoundary A hemb hsnc hsm)
    (hCentersSNC : AffineCentersHaveStrictNormalCrossingsWithBoundary A hemb hsnc hsm)
    (hLevels : AffineAllLevelsSmooth A hemb hsnc hsm)
    (hBoundarySNC : AffineBoundaryInStrictNormalCrossingPosition A hemb hsnc hsm)
    (hsncClopen : StrictNormalCrossingsRestrictToClopen.{u}) (hproper : FunctorialResolution.Blowup.BlowupIsProper.{u}) :
    ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
      [QuasiCompact pY] [IsReduced Y]
      [IsAffine Y],
      IsStrongResolution k Y pY
        ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).blowupSequenceWithoutIsos (hPrincipalization k Y pY)) := by
  intro k _ _ Y pY _ _ _ _
  exact isStrongResolution_blowupSequenceWithoutIsos_consolidated254 (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)
    (hPrincipalization k Y pY) (hEmpty k Y pY) (hSmooth k Y pY) (hDense k Y pY) (hCenters k Y pY)
    (hClopen k Y pY) (hNotInBoundary k Y pY) (hSing k Y pY) (hCentersSNC k Y pY) (hLevels k Y pY)
    (hBoundarySNC k Y pY) hsncClopen hproper


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DetachedLocus
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

section

namespace EmbeddedBlowupSequence

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]

variable (S : EmbeddedBlowupSequence k Y pY)

theorem isNoetherian_schemeAt (i : ℕ) (hi : i ≤ S.length) :
    IsNoetherian (S.schemeAt i) := by
  have hring : IsNoetherianRing ↥(CommRingCat.of k) := by
    show IsNoetherianRing k
    infer_instance
  have hspec : IsNoetherian (Spec (CommRingCat.of k)) :=
    AlgebraicGeometry.isNoetherian_Spec.mpr hring
  have hamb : IsNoetherian S.ambient :=
    isNoetherian_of_locallyOfFiniteType S.ambientStruct
  have h0 : IsNoetherian (S.ambientSeq.schemeAt 0) :=
    isNoetherian_of_iso S.ambientSeq.isoZero.symm
  revert hi
  induction i with
  | zero =>
    intro _
    exact h0
  | succ n ih =>
    intro hi
    have hn : IsNoetherian (S.ambientSeq.schemeAt n) :=
      ih (Nat.le_of_succ_le hi)
    exact isNoetherian_of_isBlowupAlongIdealSheaf (S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism n hi)

theorem strictTransformι_eq_subschemeι (j : ℕ) :
    S.strictTransformι j = (S.strictTransformIdeal j).subschemeι := rfl

private theorem noetherianSpace_of_isClosedImmersion_consolidated258
    {Z X : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f]
    (h : TopologicalSpace.NoetherianSpace ↥X) :
    TopologicalSpace.NoetherianSpace ↥Z := by
  have := h
  have hcl := AlgebraicGeometry.Scheme.Hom.isClosedEmbedding f
  exact hcl.toIsEmbedding.toIsInducing.noetherianSpace

theorem noetherianSpace_strictTransform_of_noetherianSpace_schemeAt (j : ℕ)
    (h : TopologicalSpace.NoetherianSpace ↥(S.schemeAt j)) :
    TopologicalSpace.NoetherianSpace ↥(S.strictTransform j) :=
  noetherianSpace_of_isClosedImmersion_consolidated258 (S.strictTransformIdeal j).subschemeι h

theorem quasiCompact_strictTransformι_blowdown (i : ℕ)
    (h : TopologicalSpace.NoetherianSpace ↥(S.schemeAt (i + 1))) :
    QuasiCompact
      (EmbeddedResolution.strictTransformι (S.blowdown i) (S.ambientCenter i) (S.strictTransformIdeal i)) := by
  have := h
  exact quasiCompact_strictTransformι_of_noetherianSpace _ _ _

def detachedOpens (i : ℕ) (h : IsOpen (S.detachedLocus i)) : (S.strictTransform i).Opens :=
  ⟨S.detachedLocus i, h⟩

section
variable (i : ℕ) (h : IsOpen (S.detachedLocus i))

theorem coe_detachedOpens :
    ((S.detachedOpens i h : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) =
      S.detachedLocus i := rfl

theorem disjoint_detachedOpens_detachedClosureCompl (_hn : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i)) :
    Disjoint ((S.detachedOpens i h : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))
      ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 : x ∈ S.detachedLocus i := hx
  have h2 : x ∈ closure (S.detachedLocus i) := subset_closure h1
  exact hx' h2

theorem union_detachedOpens_detachedClosureCompl (hn : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i)) :
    ((S.detachedOpens i h : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) ∪
        ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) = Set.univ := by
  have := hn
  rw [S.coe_detachedOpens i h, S.detachedClosureCompl_coe i, S.detachedClosure_coe i]
  exact Set.union_compl_self _


end

section
variable (i : ℕ)

theorem coe_detachedClosureCompl :
    ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) =
      ((S.detachedClosure i : TopologicalSpace.Closeds ↥(S.strictTransform i)) :
        Set ↥(S.strictTransform i))ᶜ := rfl

theorem isClosed_detachedClosureCompl (hn : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i))
    (h : IsOpen (S.detachedLocus i)) :
    IsClosed ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
  have := hn
  have hc : ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))
      = (S.detachedLocus i)ᶜ := by
    rw [S.coe_detachedClosureCompl i, S.detachedClosure_coe i]
  rw [hc]
  exact isClosed_compl_iff.mpr h

theorem image_detachedLocus_subset_ambientCenter_support :
    ⇑(S.strictTransformι i).base '' (S.detachedLocus i) ⊆
      ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
  rintro x ⟨y, hy, rfl⟩
  rw [S.detachedLocus_eq_sUnion i, Set.mem_sUnion] at hy
  obtain ⟨C, hC, hyC⟩ := hy
  exact ((S.mem_detachedComponents i C).mp hC).2 ⟨y, hyC, rfl⟩

theorem support_centerOffDetached_subset_detachedClosureCompl (hn : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i))
    (h : IsOpen (S.detachedLocus i)) :
    ((S.centerOffDetached i).support : Set ↥(S.strictTransform i)) ⊆
      ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
  have := hn
  have hco : ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) =
      (S.detachedLocus i)ᶜ := by
    rw [S.detachedClosureCompl_coe i, S.detachedClosure_coe i]
  have hoe := (S.detachedClosureCompl i).ι.isOpenEmbedding
  have hnU := hoe.toIsEmbedding.toIsInducing.noetherianSpace
  have hnW := noetherianSpace_of_isClosedImmersion_consolidated258
    ((S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι).subschemeι hnU
  have hqc : QuasiCompact
      (((S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι).subschemeι ≫
        (S.detachedClosureCompl i).ι) :=
    ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hr : Set.range ⇑(S.detachedClosureCompl i).ι.base =
      ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) :=
    (S.detachedClosureCompl i).range_ι
  rw [S.centerOffDetached_eq i, Scheme.Hom.support_ker, hco]
  refine closure_minimal ?_ h.isClosed_compl
  rintro y ⟨z, rfl⟩
  rw [← hco, ← hr]
  exact ⟨_, rfl⟩


end

theorem isReduced_strictTransform_of_isNoetherian [IsReduced Y]
    (hN : ∀ j ≤ S.length, IsNoetherian (S.schemeAt j))
    (i : ℕ) (hi : i ≤ S.length) :
    IsReduced (S.strictTransform i) := by
  revert hi
  induction i with
  | zero =>
    intro _
    have hq : QuasiCompact S.emb := inferInstance
    have hq2 : QuasiCompact (S.emb ≫ S.ambientSeq.isoZero.inv) :=
      inferInstance
    exact isReduced_subscheme_ker (S.emb ≫ S.ambientSeq.isoZero.inv)
  | succ n ih =>
    intro hi
    have hred : IsReduced (S.strictTransformIdeal n).subscheme :=
      ih (Nat.le_of_succ_le hi)
    have hno : IsNoetherian (S.schemeAt (n + 1)) := hN (n + 1) hi
    have hqc : QuasiCompact
        (EmbeddedResolution.strictTransformι (S.blowdown n) (S.ambientCenter n) (S.strictTransformIdeal n)) :=
      FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian
        (S.blowdown n) (S.ambientCenter n) (S.strictTransformIdeal n)
    exact isReduced_subscheme_strictTransform (S.blowdown n) (S.ambientCenter n)
      (S.strictTransformIdeal n) (S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism n hi)

section
variable {A B X : Scheme.{u}} (a : A ⟶ X) (b : B ⟶ X) (V W : Set ↥X) (hdisj : Disjoint V W) (ha : ∀ x : ↥A, a.base x ∈ V) (hb : ∀ y : ↥B, b.base y ∈ W)
include hdisj ha hb

private theorem range_coprod_inl_eq_preimage_consolidated258 :
    Set.range ⇑(coprod.inl : A ⟶ A ⨿ B).base = ⇑(coprod.desc a b).base ⁻¹' V := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    have h1 : (coprod.desc a b).base ((coprod.inl : A ⟶ A ⨿ B).base z) = a.base z := by
      have h := congrArg (fun f : A ⟶ X => f.base z) (coprod.inl_desc a b)
      exact h
    rw [Set.mem_preimage, h1]
    exact ha z
  · intro z hz
    by_contra hzn
    have hz2 : z ∈ Set.range ⇑(coprod.inr : B ⟶ A ⨿ B).base := by
      rw [Blowup.range_coprod_inr_eq_compl]
      exact hzn
    obtain ⟨y, rfl⟩ := hz2
    have h1 : (coprod.desc a b).base ((coprod.inr : B ⟶ A ⨿ B).base y) = b.base y := by
      have h := congrArg (fun f : B ⟶ X => f.base y) (coprod.inr_desc a b)
      exact h
    rw [Set.mem_preimage, h1] at hz
    exact Set.disjoint_left.mp hdisj hz (hb y)

private theorem range_coprod_inr_eq_preimage_consolidated258 :
    Set.range ⇑(coprod.inr : B ⟶ A ⨿ B).base = ⇑(coprod.desc a b).base ⁻¹' W := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y, rfl⟩
    have h1 : (coprod.desc a b).base ((coprod.inr : B ⟶ A ⨿ B).base y) = b.base y := by
      have h := congrArg (fun f : B ⟶ X => f.base y) (coprod.inr_desc a b)
      exact h
    rw [Set.mem_preimage, h1]
    exact hb y
  · intro z hz
    rw [Blowup.range_coprod_inr_eq_compl]
    intro hzl
    obtain ⟨x, rfl⟩ := hzl
    have h1 : (coprod.desc a b).base ((coprod.inl : A ⟶ A ⨿ B).base x) = a.base x := by
      have h := congrArg (fun f : A ⟶ X => f.base x) (coprod.inl_desc a b)
      exact h
    rw [Set.mem_preimage, h1] at hz
    exact Set.disjoint_left.mp hdisj (ha x) hz


end

private theorem exists_iso_subscheme_of_eq_vanishingIdeal_consolidated258 {X : Scheme.{u}}
    [IsReduced X] (C : X.Opens)
    (hC : IsClosed ((C : Set ↥X))) (J : X.IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.vanishingIdeal
      (⟨(C : Set ↥X), hC⟩ : TopologicalSpace.Closeds ↥X)) :
    ∃ e : J.subscheme ≅ C.toScheme, e.hom ≫ C.ι = J.subschemeι := by
  subst hJ
  exact exists_iso_subscheme_vanishingIdeal_of_isClosed C hC

private theorem isBlowupAlongIdealSheaf_lift_of_comp_eq_consolidated258 {X X₁ S₀ : Scheme.{u}} (j : S₀ ⟶ X)
    [IsClosedImmersion j] [Mono j]
    [IsLocallyNoetherian X₁] (π : X₁ ⟶ X) (Z : X.IdealSheafData)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (D : X.IdealSheafData) (hD : Scheme.Hom.ker j = D)
    (q : (Blowup.strictTransform π Z D).subscheme ⟶ S₀)
    (hq : q ≫ j = (Blowup.strictTransform π Z D).subschemeι ≫ π) :
    Blowup.IsBlowupAlongIdealSheaf q (Z.comap j) := by
  subst hD
  have h2 := strictTransformLiftOfClosedImmersion_comp j π Z
  have h3 : q = strictTransformLiftOfClosedImmersion j π Z := by
    rw [← cancel_mono j, hq, h2]
  rw [h3]
  exact isBlowupAlongIdealSheaf_strictTransformLiftOfClosedImmersion j π Z hπ

private theorem isBlowupAlongIdealSheaf_coprod_desc_of_disjoint_cover_consolidated258 {A A' F : Scheme.{u}} (g : A' ⟶ A) (j : F ⟶ A)
    (I : A.IdealSheafData) (V W : A.Opens)
    (hdisj : Disjoint ((V : Set ↥A)) ((W : Set ↥A)))
    (hcov : (V : Set ↥A) ∪ (W : Set ↥A) = Set.univ)
    (hgV : ∀ x : ↥A', g.base x ∈ (V : Set ↥A))
    (hjW : ∀ y : ↥F, j.base y ∈ (W : Set ↥A))
    (e : F ≅ W.toScheme) (he : e.hom ≫ W.ι = j)
    (hIW : I.comap W.ι = ⊤)
    (gV : A' ⟶ V.toScheme) (hgv : gV ≫ V.ι = g)
    (hblow : Blowup.IsBlowupAlongIdealSheaf gV (I.comap V.ι)) :
    Blowup.IsBlowupAlongIdealSheaf (coprod.desc g j) I := by
  have hrl : Set.range ⇑(coprod.inl : A' ⟶ A' ⨿ F).base
      = Set.range ⇑(coprod.desc g j ⁻¹ᵁ V).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact range_coprod_inl_eq_preimage_consolidated258 g j _ _ hdisj hgV hjW
  have hrr : Set.range ⇑(coprod.inr : F ⟶ A' ⨿ F).base
      = Set.range ⇑(coprod.desc g j ⁻¹ᵁ W).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact range_coprod_inr_eq_preimage_consolidated258 g j _ _ hdisj hgV hjW
  obtain ⟨δ, hδ⟩ : ∃ δ : A' ≅ (coprod.desc g j ⁻¹ᵁ V).toScheme,
      δ.hom ≫ (coprod.desc g j ⁻¹ᵁ V).ι = (coprod.inl : A' ⟶ A' ⨿ F) :=
    ⟨IsOpenImmersion.isoOfRangeEq _ _ hrl, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : F ≅ (coprod.desc g j ⁻¹ᵁ W).toScheme,
      ε.hom ≫ (coprod.desc g j ⁻¹ᵁ W).ι = (coprod.inr : F ⟶ A' ⨿ F) :=
    ⟨IsOpenImmersion.isoOfRangeEq _ _ hrr, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrr⟩
  have key1 : δ.hom ≫ (coprod.desc g j ∣_ V) = gV := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hδ,
      coprod.inl_desc, hgv]
  have key2 : ε.hom ≫ (coprod.desc g j ∣_ W) = e.hom := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hε,
      coprod.inr_desc, he]
  have hV : Blowup.IsBlowupAlongIdealSheaf (coprod.desc g j ∣_ V) (I.comap V.ι) := by
    have hb := hblow.iso_hom_comp δ.symm
    rw [← key1, Iso.symm_hom, Iso.inv_hom_id_assoc] at hb
    exact hb
  have hisoW : IsIso (coprod.desc g j ∣_ W) := by
    have hw : (coprod.desc g j ∣_ W) = ε.inv ≫ e.hom := by
      rw [← key2, Iso.inv_hom_id_assoc]
    rw [hw]
    infer_instance
  have hW : Blowup.IsBlowupAlongIdealSheaf (coprod.desc g j ∣_ W) (I.comap W.ι) := by
    rw [hIW]
    exact Blowup.IsBlowupAlongIdealSheaf.of_isIso _
  have hoi : ∀ b : Bool,
      IsOpenImmersion (Bool.rec (motive := fun b =>
        (Bool.rec (motive := fun _ => Scheme.{u}) V.toScheme W.toScheme b) ⟶ A) V.ι W.ι b) := by
    intro b
    cases b
    · exact (inferInstance : IsOpenImmersion V.ι)
    · exact (inferInstance : IsOpenImmersion W.ι)
  refine Blowup.IsBlowupAlongIdealSheaf.of_comap_of_isOpenImmersion_cover (coprod.desc g j) I
      (fun b : Bool => Bool.rec (motive := fun _ => Scheme.{u}) V.toScheme W.toScheme b)
      (fun b : Bool => Bool.rec (motive := fun b =>
        (Bool.rec (motive := fun _ => Scheme.{u}) V.toScheme W.toScheme b) ⟶ A) V.ι W.ι b) ?_ ?_
  · intro x
    by_cases hx : x ∈ (V : Set ↥A)
    · refine ⟨false, ?_⟩
      show x ∈ Set.range ⇑V.ι.base
      rw [Scheme.Opens.range_ι]
      exact hx
    · refine ⟨true, ?_⟩
      show x ∈ Set.range ⇑W.ι.base
      rw [Scheme.Opens.range_ι]
      have hxu : x ∈ (V : Set ↥A) ∪ (W : Set ↥A) := by rw [hcov]; trivial
      exact hxu.resolve_left hx
  · intro b
    cases b
    · show Blowup.IsBlowupAlongIdealSheaf (pullback.snd (coprod.desc g j) V.ι) (I.comap V.ι)
      have hb := hV.iso_hom_comp (pullbackRestrictIsoRestrict (coprod.desc g j) V)
      rwa [pullbackRestrictIsoRestrict_hom_morphismRestrict] at hb
    · show Blowup.IsBlowupAlongIdealSheaf (pullback.snd (coprod.desc g j) W.ι) (I.comap W.ι)
      have hb := hW.iso_hom_comp (pullbackRestrictIsoRestrict (coprod.desc g j) W)
      rwa [pullbackRestrictIsoRestrict_hom_morphismRestrict] at hb

theorem isBlowupAlongIdealSheaf_coprod_desc_centerOffDetached [IsReduced Y]
    [QuasiCompact pY] (i : ℕ) (hi : i < S.length)
    (h : IsOpen (S.detachedLocus i))
    (hN : ∀ j ≤ S.length, IsNoetherian (S.schemeAt j)) :
    Blowup.IsBlowupAlongIdealSheaf (coprod.desc (S.strictTransformMap i) (S.detachedι i)) (S.centerOffDetached i) := by
  have hn0 : IsNoetherian (S.schemeAt i) := hN i hi.le
  have hn1 : IsNoetherian (S.schemeAt (i + 1)) := hN (i + 1) hi
  have hns0 : TopologicalSpace.NoetherianSpace ↥(S.schemeAt i) := inferInstance
  have hns1 : TopologicalSpace.NoetherianSpace ↥(S.schemeAt (i + 1)) := inferInstance
  have hnsA : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i) :=
    S.noetherianSpace_strictTransform_of_noetherianSpace_schemeAt i hns0
  have hnsA1 : TopologicalSpace.NoetherianSpace ↥(S.strictTransform (i + 1)) :=
    S.noetherianSpace_strictTransform_of_noetherianSpace_schemeAt (i + 1) hns1
  have hred : IsReduced (S.strictTransform i) :=
    S.isReduced_strictTransform_of_isNoetherian hN i hi.le
  have hqcst : QuasiCompact
      (EmbeddedResolution.strictTransformι (S.blowdown i) (S.ambientCenter i) (S.strictTransformIdeal i)) :=
    S.quasiCompact_strictTransformι_blowdown i hns1
  have hUc : IsClosed ((S.detachedOpens i h : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
    rw [S.coe_detachedOpens i h]
    exact S.isClosed_detachedLocus i
  have hdetached : S.detachedIdeal i
      = Scheme.IdealSheafData.vanishingIdeal
          (⟨((S.detachedOpens i h : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)), hUc⟩ :
            TopologicalSpace.Closeds ↥(S.strictTransform i)) := by
    rw [S.detachedIdeal_eq i]
    congr 1
    refine TopologicalSpace.Closeds.ext ?_
    show ((S.detachedClosure i : TopologicalSpace.Closeds ↥(S.strictTransform i)) :
        Set ↥(S.strictTransform i)) =
      ((S.detachedOpens i h : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))
    rw [S.detachedClosure_coe i, S.coe_detachedOpens i h]
  obtain ⟨e, he⟩ := exists_iso_subscheme_of_eq_vanishingIdeal_consolidated258 (S.detachedOpens i h) hUc
    (S.detachedIdeal i) hdetached
  have hblowA : Blowup.IsBlowupAlongIdealSheaf (S.strictTransformMap i) (S.comapAmbientCenter i) := by
    have hln : IsLocallyNoetherian (S.schemeAt (i + 1)) := inferInstance
    have hmono : Mono (S.strictTransformι i) := inferInstance
    exact isBlowupAlongIdealSheaf_lift_of_comp_eq_consolidated258 (S.strictTransformι i) (S.blowdown i) (S.ambientCenter i)
      (S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism i hi) (S.strictTransformIdeal i) (by simp) (S.strictTransformMap i)
      (S.strictTransformMap_comp_strictTransformι i)
  have hstrict : ∀ x : ↥(S.strictTransform (i + 1)),
      (S.strictTransformMap i).base x ∈
        ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
    have hVcl : IsClosed ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) :=
      S.isClosed_detachedClosureCompl i hnsA h
    have himV : IsClosed (⇑(S.strictTransformι i).base ''
        ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))) :=
      (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding (S.strictTransformι i)).isClosedMap _ hVcl
    have hsub : (((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) \
          ((S.ambientCenter i).support : Set ↥(S.schemeAt i)))
        ⊆ ⇑(S.strictTransformι i).base ''
            ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
      rintro y ⟨hy, hy2⟩
      rw [← Scheme.IdealSheafData.range_subschemeι] at hy
      obtain ⟨z, rfl⟩ := hy
      refine ⟨z, ?_, rfl⟩
      by_contra hz
      refine absurd (S.image_detachedLocus_subset_ambientCenter_support i ⟨z, ?_, rfl⟩) hy2
      have hz' : z ∈ ((S.detachedClosure i : TopologicalSpace.Closeds ↥(S.strictTransform i)) :
          Set ↥(S.strictTransform i)) := by
        by_contra hz2
        exact hz (by rw [S.detachedClosureCompl_coe i]; exact hz2)
      rw [S.detachedClosure_coe i] at hz'
      exact hz'
    intro x
    have h1 : (S.strictTransformι (i + 1)).base x ∈
        ((S.strictTransformIdeal (i + 1)).support : Set ↥(S.schemeAt (i + 1))) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨x, rfl⟩
    rw [S.strictTransformIdeal_succ i,
      support_strictTransform_eq_closure_preimage (S.blowdown i) (S.ambientCenter i) (S.strictTransformIdeal i)] at h1
    have h2 : closure (⇑(S.blowdown i).base ⁻¹'
          (((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) \
            ((S.ambientCenter i).support : Set ↥(S.schemeAt i))))
        ⊆ ⇑(S.blowdown i).base ⁻¹' (⇑(S.strictTransformι i).base ''
            ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))) :=
      closure_minimal (Set.preimage_mono hsub)
        (himV.preimage (S.blowdown i).base.hom.continuous)
    obtain ⟨v, hv, hveq⟩ := h2 h1
    have h3 : (S.strictTransformι i).base ((S.strictTransformMap i).base x)
        = (S.blowdown i).base ((S.strictTransformι (i + 1)).base x) := by
      have hc := congrArg (fun f : S.strictTransform (i + 1) ⟶ S.schemeAt i => f.base x)
        (S.strictTransformMap_comp_strictTransformι i)
      simpa using hc
    have h4 : (S.strictTransformι i).base v = (S.strictTransformι i).base ((S.strictTransformMap i).base x) := by
      rw [h3, hveq]
    have h5 := (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding (S.strictTransformι i)).injective h4
    rw [← h5]
    exact hv
  have hζr : Set.range ⇑(𝟙 (S.strictTransform (i + 1))).base
      = Set.range ⇑(S.strictTransformMap i ⁻¹ᵁ (S.detachedClosureCompl i)).ι.base := by
    rw [Scheme.Opens.range_ι]
    have hA : Set.range ⇑(𝟙 (S.strictTransform (i + 1))).base = Set.univ := by simp
    rw [hA]
    symm
    rw [Set.eq_univ_iff_forall]
    intro z
    exact hstrict z
  obtain ⟨ζ, hζ⟩ : ∃ ζ : S.strictTransform (i + 1) ≅ (S.strictTransformMap i ⁻¹ᵁ (S.detachedClosureCompl i)).toScheme,
      ζ.hom ≫ (S.strictTransformMap i ⁻¹ᵁ (S.detachedClosureCompl i)).ι = 𝟙 (S.strictTransform (i + 1)) :=
    ⟨IsOpenImmersion.isoOfRangeEq _ _ hζr, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hζr⟩
  have hgv : (ζ.hom ≫ (S.strictTransformMap i ∣_ (S.detachedClosureCompl i))) ≫ (S.detachedClosureCompl i).ι
      = S.strictTransformMap i := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hζ, Category.id_comp]
  have hnU : TopologicalSpace.NoetherianSpace ↥((S.detachedClosureCompl i).toScheme) :=
    ((S.detachedClosureCompl i).ι.isOpenEmbedding).toIsEmbedding.toIsInducing.noetherianSpace
  have hnW : TopologicalSpace.NoetherianSpace
      ↥(((S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι).subscheme) :=
    noetherianSpace_of_isClosedImmersion_consolidated258
      ((S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι).subschemeι hnU
  have hq1 : QuasiCompact
      (((S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι).subschemeι) :=
    ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hq2 : QuasiCompact
      ((((S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι).subschemeι) ≫
        (S.detachedClosureCompl i).ι) :=
    ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hWeq : (S.centerOffDetached i).comap (S.detachedClosureCompl i).ι
      = (S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι := by
    rw [S.centerOffDetached_eq i]
    exact comap_ker_subschemeι_comp _ _
  have hblowV : Blowup.IsBlowupAlongIdealSheaf (ζ.hom ≫ (S.strictTransformMap i ∣_ (S.detachedClosureCompl i)))
      ((S.centerOffDetached i).comap (S.detachedClosureCompl i).ι) := by
    rw [hWeq]
    exact (hblowA.restrict (S.detachedClosureCompl i)).iso_hom_comp ζ
  have hIW : (S.centerOffDetached i).comap (S.detachedOpens i h).ι = ⊤ := by
    refine Blowup.comap_eq_top_of_notMem_support _ _ ?_
    intro x hx
    have h1 : (S.detachedOpens i h).ι.base x ∈
        ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) :=
      S.support_centerOffDetached_subset_detachedClosureCompl i hnsA h hx
    have h2 : (S.detachedOpens i h).ι.base x ∈
        ((S.detachedOpens i h : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
      rw [← Scheme.Opens.range_ι]
      exact ⟨x, rfl⟩
    exact Set.disjoint_left.mp (S.disjoint_detachedOpens_detachedClosureCompl i h hnsA) h2 h1
  refine isBlowupAlongIdealSheaf_coprod_desc_of_disjoint_cover_consolidated258 (S.strictTransformMap i) (S.detachedι i) (S.centerOffDetached i)
      (S.detachedClosureCompl i) (S.detachedOpens i h) ((S.disjoint_detachedOpens_detachedClosureCompl i h hnsA).symm)
      ?_ hstrict ?_ e he hIW (ζ.hom ≫ (S.strictTransformMap i ∣_ (S.detachedClosureCompl i))) hgv hblowV
  · rw [Set.union_comm]
    exact S.union_detachedOpens_detachedClosureCompl i h hnsA
  · intro y
    have hy : (S.detachedι i).base y ∈ Set.range ⇑(S.detachedOpens i h).ι.base := by
      refine ⟨e.hom.base y, ?_⟩
      have hc := congrArg (fun f : (S.detachedIdeal i).subscheme ⟶ S.strictTransform i => f.base y) he
      simpa using hc
    rwa [Scheme.Opens.range_ι] at hy

private def coprodSwapAssocHom_consolidated258 (A F T : Scheme.{u}) : A ⨿ (T ⨿ F) ⟶ (A ⨿ F) ⨿ T :=
  coprod.desc ((coprod.inl : A ⟶ A ⨿ F) ≫ (coprod.inl : A ⨿ F ⟶ (A ⨿ F) ⨿ T))
    (coprod.desc (coprod.inr : T ⟶ (A ⨿ F) ⨿ T)
      ((coprod.inr : F ⟶ A ⨿ F) ≫ (coprod.inl : A ⨿ F ⟶ (A ⨿ F) ⨿ T)))

private def coprodSwapAssocInv_consolidated258 (A F T : Scheme.{u}) : (A ⨿ F) ⨿ T ⟶ A ⨿ (T ⨿ F) :=
  coprod.desc
    (coprod.desc (coprod.inl : A ⟶ A ⨿ (T ⨿ F))
      ((coprod.inr : F ⟶ T ⨿ F) ≫ (coprod.inr : T ⨿ F ⟶ A ⨿ (T ⨿ F))))
    ((coprod.inl : T ⟶ T ⨿ F) ≫ (coprod.inr : T ⨿ F ⟶ A ⨿ (T ⨿ F)))

private def coprodSwapAssocIso_consolidated258 (A F T : Scheme.{u}) : A ⨿ (T ⨿ F) ≅ (A ⨿ F) ⨿ T where
  hom := coprodSwapAssocHom_consolidated258 A F T
  inv := coprodSwapAssocInv_consolidated258 A F T
  hom_inv_id := by
    refine coprod.hom_ext ?_ ?_
    · simp [coprodSwapAssocHom_consolidated258, coprodSwapAssocInv_consolidated258, coprod.inl_desc, coprod.inr_desc]
    · refine coprod.hom_ext ?_ ?_ <;>
        simp [coprodSwapAssocHom_consolidated258, coprodSwapAssocInv_consolidated258, coprod.inl_desc, coprod.inr_desc]
  inv_hom_id := by
    refine coprod.hom_ext ?_ ?_
    · refine coprod.hom_ext ?_ ?_ <;>
        simp [coprodSwapAssocHom_consolidated258, coprodSwapAssocInv_consolidated258, coprod.inl_desc, coprod.inr_desc]
    · simp [coprodSwapAssocHom_consolidated258, coprodSwapAssocInv_consolidated258, coprod.inl_desc, coprod.inr_desc]

private theorem coprodSwapAssocIso_hom_consolidated258 (A F T : Scheme.{u}) :
    (coprodSwapAssocIso_consolidated258 A F T).hom = coprodSwapAssocHom_consolidated258 A F T := rfl

theorem isBlowupAlongIdealSheaf_totalTransition_of_coprod_desc (i : ℕ)
    (h : Blowup.IsBlowupAlongIdealSheaf (coprod.desc (S.strictTransformMap i) (S.detachedι i)) (S.centerOffDetached i)) :
    Blowup.IsBlowupAlongIdealSheaf (S.totalTransition i) (S.totalCenter i) := by
  have hq1 : QuasiCompact (S.centerOffDetached i).subschemeι := inferInstance
  have hq2 : QuasiCompact
      ((S.centerOffDetached i).subschemeι ≫
        (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) := inferInstance
  have hker : Scheme.Hom.ker (S.centerOffDetached i).subschemeι = S.centerOffDetached i := by simp
  have hl : (S.totalCenter i).comap (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)
      = S.centerOffDetached i := by
    rw [S.totalCenter_eq i,
      Blowup.ker_comp_coprod_inl_comap_inl (Y := S.detachedCoprod i) (S.centerOffDetached i).subschemeι, hker]
  have hr : (S.totalCenter i).comap (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) = ⊤ := by
    rw [S.totalCenter_eq i,
      Blowup.ker_comp_coprod_inl_comap_inr (Y := S.detachedCoprod i) (S.centerOffDetached i).subschemeι]
  have h₁ : Blowup.IsBlowupAlongIdealSheaf (coprod.desc (S.strictTransformMap i) (S.detachedι i))
      ((S.totalCenter i).comap (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) := by
    rw [hl]; exact h
  have h₂ : Blowup.IsBlowupAlongIdealSheaf (𝟙 (S.detachedCoprod i))
      ((S.totalCenter i).comap (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i)) := by
    rw [hr]; exact Blowup.isBlowupAlongIdealSheaf_id_top _
  have hmap := Blowup.IsBlowupAlongIdealSheaf.coprod h₁ h₂
  have hcomp :
      (coprodSwapAssocIso_consolidated258 (S.strictTransform (i + 1)) (S.detachedScheme i) (S.detachedCoprod i)).hom ≫
          coprod.map (coprod.desc (S.strictTransformMap i) (S.detachedι i)) (𝟙 (S.detachedCoprod i)) =
        S.totalTransition i := by
    refine coprod.hom_ext ?_ ?_
    · simp [coprodSwapAssocIso_hom_consolidated258, coprodSwapAssocHom_consolidated258, EmbeddedBlowupSequence.totalTransition,
        coprod.inl_desc, coprod.inr_desc]
    · refine coprod.hom_ext ?_ ?_ <;>
        simp [coprodSwapAssocIso_hom_consolidated258, coprodSwapAssocHom_consolidated258, EmbeddedBlowupSequence.totalTransition,
          coprod.inl_desc, coprod.inr_desc]
  have hfin := hmap.iso_hom_comp
    (coprodSwapAssocIso_consolidated258 (S.strictTransform (i + 1)) (S.detachedScheme i) (S.detachedCoprod i))
  rw [hcomp] at hfin
  exact hfin

end EmbeddedBlowupSequence

def EmbeddedBlowupSequence.DetachedLocusIsOpen {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType pY] (S : EmbeddedBlowupSequence k Y pY) : Prop :=
  ∀ i < S.length, IsOpen (S.detachedLocus i)

def EmbeddedBlowupSequence.AllLevelsNoetherian {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType pY] (S : EmbeddedBlowupSequence k Y pY) : Prop :=
  ∀ i ≤ S.length, IsNoetherian (S.schemeAt i)

theorem transitionsAreBlowups_of_detachedLocusIsOpen {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [IsAffine Y] [IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]
    [QuasiCompact pY] (S : EmbeddedBlowupSequence k Y pY)
    (hOpen : EmbeddedBlowupSequence.DetachedLocusIsOpen S) (hnoeth : EmbeddedBlowupSequence.AllLevelsNoetherian S) :
    S.TransitionsAreBlowups := by
  intro i hi
  rw [S.totalTower_map_succ i]
  exact EmbeddedBlowupSequence.isBlowupAlongIdealSheaf_totalTransition_of_coprod_desc S i
    (EmbeddedBlowupSequence.isBlowupAlongIdealSheaf_coprod_desc_centerOffDetached S i hi (hOpen i hi) hnoeth)

def DetachedLocusIsOpenForEmbeddings (A : PrincipalizationAlgorithm.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y] (D : EmbeddingDatum k Y pY),
    EmbeddedBlowupSequence.DetachedLocusIsOpen (D.toEmbeddedBlowupSequence A)

section
variable (A : PrincipalizationAlgorithm.{u})

theorem allLevelsNoetherian_toEmbeddedBlowupSequence (k : Type u) [Field k] [CharZero k]
    (Y : Scheme.{u}) (pY : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    [IsReduced Y] [IsAffine Y]
    (D : EmbeddingDatum k Y pY) :
    EmbeddedBlowupSequence.AllLevelsNoetherian (D.toEmbeddedBlowupSequence A) := by
  intro i hi
  exact EmbeddedBlowupSequence.isNoetherian_schemeAt (D.toEmbeddedBlowupSequence A) i hi

theorem transitionsAreBlowupsForEmbeddings_of_detachedLocusIsOpen (h : DetachedLocusIsOpenForEmbeddings A) :
    TransitionsAreBlowupsForEmbeddings A := by
  intro k _ _ Y pY _ _ _ _ D
  exact transitionsAreBlowups_of_detachedLocusIsOpen (D.toEmbeddedBlowupSequence A) (h k Y pY D)
    (allLevelsNoetherian_toEmbeddedBlowupSequence A k Y pY D)


end

section
variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p] (C : Set ↥X)
include p

theorem isClopen_of_mem_irreducibleComponents_of_smooth (hC : C ∈ irreducibleComponents ↥X) : IsClopen C :=
  isClopen_irreducibleComponent_of_smooth p inferInstance hC

theorem smooth_subschemeι_vanishingIdeal_comp_of_isClopen (hC : IsClopen C) :
    Smooth
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)).subschemeι ≫ p) := by
  have hredX : IsReduced X := isReduced_of_smooth p
  obtain ⟨e, he⟩ := exists_iso_subscheme_vanishingIdeal_of_isClosed
    (⟨C, hC.isOpen⟩ : X.Opens) hC.isClosed
  have key : Smooth
      ((e.hom ≫ Scheme.Opens.ι (⟨C, hC.isOpen⟩ : X.Opens)) ≫ p) := inferInstance
  rw [he] at key
  exact key


end

namespace EmbeddedBlowupSequence

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]

variable (S : EmbeddedBlowupSequence k Y pY)

def schemeAtToSpec (i : ℕ) : S.schemeAt i ⟶ Spec (CommRingCat.of k) :=
  S.ambientSeq.projectionToBase i ≫ S.ambientStruct

theorem schemeAtToSpec_eq (i : ℕ) :
    S.schemeAtToSpec i = S.ambientSeq.projectionToBase i ≫ S.ambientStruct := rfl

def strictTransformToSpec (i : ℕ) : S.strictTransform i ⟶ Spec (CommRingCat.of k) :=
  S.strictTransformι i ≫ S.schemeAtToSpec i

theorem strictTransformToSpec_eq (i : ℕ) :
    S.strictTransformToSpec i = S.strictTransformι i ≫ S.schemeAtToSpec i := rfl

section
variable (i : ℕ) (hi : i ≤ S.length)
include hi

theorem locallyOfFiniteType_schemeAtToSpec :
    LocallyOfFiniteType (S.schemeAtToSpec i) := by
  have key : ∀ j : ℕ, j ≤ S.length →
      LocallyOfFiniteType (S.ambientSeq.projectionToBase j) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [SequenceOfBlowups.projectionToBase_zero]
      infer_instance
    | succ n ih =>
      intro hn
      have hft : LocallyOfFiniteType (S.ambientSeq.projectionToBase n) :=
        ih (Nat.le_of_succ_le hn)
      have hno : IsNoetherian (S.schemeAt n) :=
        S.isNoetherian_schemeAt n (Nat.le_of_succ_le hn)
      have hprop : IsProper (S.ambientSeq.transitionMapSucc n) :=
        Blowup.blowupIsProper (S.schemeAt n) (S.schemeAt (n + 1)) (S.ambientSeq.transitionMapSucc n)
          (S.ambientCenter n) (S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism n hn)
      have hftb : LocallyOfFiniteType (S.ambientSeq.transitionMapSucc n) :=
        inferInstance
      rw [SequenceOfBlowups.projectionToBase_succ]
      infer_instance
  have := key i hi
  rw [S.schemeAtToSpec_eq i]
  infer_instance

theorem locallyOfFiniteType_strictTransformToSpec :
    LocallyOfFiniteType (S.strictTransformToSpec i) := by
  have hlev : LocallyOfFiniteType (S.schemeAtToSpec i) :=
    S.locallyOfFiniteType_schemeAtToSpec i hi
  have hι : LocallyOfFiniteType (S.strictTransformι i) := inferInstance
  rw [S.strictTransformToSpec_eq i]
  infer_instance


end

end EmbeddedBlowupSequence


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ChartFlatBaseChange
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

section

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]
  {k' : Type u} [Field k'] [CharZero k'] {Y' : Scheme.{u}} [IsAffine Y']
  {pY' : Y' ⟶ Spec (CommRingCat.of k')} [LocallyOfFiniteType pY']

structure ChartFlatBaseChange (S : EmbeddedBlowupSequence k Y pY) (S' : EmbeddedBlowupSequence k' Y' pY') where
  ambientMap : S'.ambient ⟶ S.ambient
  flat_ambientMap : Flat ambientMap
  baseMap : Y' ⟶ Y
  isPullback_emb : IsPullback baseMap S'.emb S.emb ambientMap
  reindex : ℕ → ℕ
  levelMap : ∀ j : ℕ, j ≤ S'.length → (S'.schemeAt j ⟶ S.schemeAt (reindex j))
  reindex_lt : ∀ j : ℕ, j < S'.length → reindex j < S.length
  reindex_lt_succ : ∀ j : ℕ, j < S'.length → reindex j < reindex (j + 1)
  reindex_len : reindex S'.length = S.length
  isPullback_level : ∀ (j : ℕ) (hj : j ≤ S'.length),
    IsPullback (levelMap j hj) (S'.ambientSeq.projectionToBase j)
      (S.ambientSeq.projectionToBase (reindex j)) ambientMap
  isPullback_down : ∀ (j : ℕ) (hj : j ≤ S'.length) (i : ℕ) (hi : i ≤ reindex j),
    (∀ m, i ≤ m → m < reindex j → ∀ j', j' < S'.length → reindex j' ≠ m) →
    IsPullback (levelMap j hj ≫ S.ambientSeq.transitionMap hi) (S'.ambientSeq.projectionToBase j)
      (S.ambientSeq.projectionToBase i) ambientMap
  isPullback_step : ∀ (j : ℕ) (hj : j < S'.length) (hσ : reindex j + 1 ≤ reindex (j + 1)),
    IsPullback (levelMap (j + 1) (Nat.succ_le_of_lt hj) ≫ S.ambientSeq.transitionMap hσ)
      (S'.blowdown j) (S.blowdown (reindex j)) (levelMap j (Nat.le_of_lt hj))
  center_eq : ∀ (j : ℕ) (hj : j < S'.length),
    S'.ambientCenter j = (S.ambientCenter (reindex j)).comap (levelMap j (Nat.le_of_lt hj))
  comap_center_skipped : ∀ i, i < S.length → (∀ j, j < S'.length → reindex j ≠ i) →
    ∀ (P : Scheme.{u}) (q : P ⟶ S.schemeAt i) (p : P ⟶ S'.ambient),
      IsPullback q p (S.ambientSeq.projectionToBase i) ambientMap → (S.ambientCenter i).comap q = ⊤

namespace ChartFlatBaseChange

variable {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

instance instFlatAmbientMap (F : ChartFlatBaseChange S S') :
    Flat F.ambientMap := F.flat_ambientMap

private theorem apply_lt_apply_of_forall_lt_succ_consolidated286
    {σ : ℕ → ℕ} {N : ℕ} (h : ∀ j, j < N → σ j < σ (j + 1)) :
    ∀ j, j ≤ N → ∀ i, i < j → σ i < σ j := by
  intro j hj i hij
  exact strictMonoOn_Iic_of_lt_succ h (Set.mem_Iic.mpr (le_trans (le_of_lt hij) hj))
    (Set.mem_Iic.mpr hj) hij

section
variable (F : ChartFlatBaseChange S S')

theorem reindex_lt_reindex_of_lt {i j : ℕ} (hij : i < j) (hj : j ≤ S'.length) :
    F.reindex i < F.reindex j :=
  apply_lt_apply_of_forall_lt_succ_consolidated286 (σ := F.reindex) (N := S'.length)
    F.reindex_lt_succ j hj i hij

theorem reindex_le_length {j : ℕ} (hj : j ≤ S'.length) :
    F.reindex j ≤ S.length := by
  rcases eq_or_lt_of_le hj with h | h
  · subst h
    exact le_of_eq F.reindex_len
  · exact le_of_lt (F.reindex_lt j h)

theorem flat_levelMap (j : ℕ) (hj : j ≤ S'.length) :
    Flat (F.levelMap j hj) := by
  have hst : MorphismProperty.IsStableUnderBaseChange
      (@Flat : MorphismProperty Scheme.{u}) := inferInstance
  exact hst.of_isPullback (F.isPullback_level j hj).flip F.flat_ambientMap

theorem reindex_ne_of_lt_reindex_zero (m : ℕ)
    (hm : m < F.reindex 0) (j : ℕ) (hj : j < S'.length) : F.reindex j ≠ m := by
  have h : F.reindex 0 ≤ F.reindex j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      exact le_rfl
    · exact le_of_lt (F.reindex_lt_reindex_of_lt h0 (le_of_lt hj))
  omega

theorem reindex_ne_of_reindex_lt_of_lt_reindex_succ (j : ℕ) (hj : j < S'.length) (m : ℕ)
    (h1 : F.reindex j < m) (h2 : m < F.reindex (j + 1)) (j' : ℕ) (hj' : j' < S'.length) :
    F.reindex j' ≠ m := by
  intro hEq
  rcases Nat.lt_or_ge j' (j + 1) with hlt | hge
  · have hle : F.reindex j' ≤ F.reindex j := by
      rcases Nat.lt_or_ge j' j with h | h
      · exact le_of_lt (F.reindex_lt_reindex_of_lt h (le_of_lt hj))
      · have hjj : j' = j := le_antisymm (Nat.lt_succ_iff.mp hlt) h
        subst hjj
        exact le_rfl
    omega
  · have hle : F.reindex (j + 1) ≤ F.reindex j' := by
      rcases Nat.eq_or_lt_of_le hge with h | h
      · exact le_of_eq (congrArg F.reindex h)
      · exact le_of_lt (F.reindex_lt_reindex_of_lt h (le_of_lt hj'))
    omega


end

section
variable (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j ≤ S'.length)

private theorem strictTransformIdeal_comap_transitionMap_eq_consolidated286 :
    ∀ (n i : ℕ) (hi : i ≤ F.reindex j), i + n = F.reindex j →
      (∀ m, i ≤ m → m < F.reindex j → ∀ j', j' < S'.length → F.reindex j' ≠ m) →
      (S.strictTransformIdeal i).comap (F.levelMap j hj ≫ S.ambientSeq.transitionMap hi)
        = (S.strictTransformIdeal (F.reindex j)).comap (F.levelMap j hj) := by
  intro n
  induction n with
  | zero =>
      intro i hi hsum _
      have hie : i = F.reindex j := by omega
      subst hie
      rw [S.ambientSeq.transitionMap_self hi, Category.comp_id]
  | succ n ih =>
      intro i hi hsum hskip
      have hi1 : i + 1 ≤ F.reindex j := by omega
      have hlen : F.reindex j ≤ S.length := F.reindex_le_length hj
      have hiS : i + 1 ≤ S.length := le_trans hi1 hlen
      have := S.isNoetherian_schemeAt (i + 1) hiS
      have hIH := ih (i + 1) hi1 (by omega)
        (fun m hm hm2 j' hj' => hskip m (by omega) hm2 j' hj')
      have hdown : S.ambientSeq.transitionMap hi1 ≫ S.blowdown i = S.ambientSeq.transitionMap hi := by
        have h := S.ambientSeq.transitionMap_trans (Nat.le_succ i) hi1
        rw [← S.ambientSeq.blowupMorphism_eq_transitionMap] at h
        exact h
      have htop : (S.ambientCenter i).comap (F.levelMap j hj ≫ S.ambientSeq.transitionMap hi) = ⊤ :=
        F.comap_center_skipped i (by omega) (fun j' hj' => hskip i le_rfl (by omega) j' hj')
          (S'.schemeAt j) (F.levelMap j hj ≫ S.ambientSeq.transitionMap hi)
          (S'.ambientSeq.projectionToBase j) (F.isPullback_down j hj i hi hskip)
      have hg : ((S.ambientCenter i).comap (S.blowdown i)).comap
          (F.levelMap j hj ≫ S.ambientSeq.transitionMap hi1) = ⊤ := by
        rw [← Scheme.IdealSheafData.comap_comp, Category.assoc, hdown]
        exact htop
      have hst := strictTransform_comap_of_comap_center_eq_top (S.blowdown i)
        (S.ambientCenter i) (S.strictTransformIdeal i) (F.levelMap j hj ≫ S.ambientSeq.transitionMap hi1) hg
      rw [← hIH, S.strictTransformIdeal_succ i, hst, ← Scheme.IdealSheafData.comap_comp, Category.assoc,
        hdown]

theorem strictTransformIdeal_eq_comap :
    S'.strictTransformIdeal j = (S.strictTransformIdeal (F.reindex j)).comap (F.levelMap j hj) := by
  revert hj
  induction j with
  | zero =>
      intro hj
      have h0 : (0 : ℕ) ≤ F.reindex 0 := Nat.zero_le _
      have hskip : ∀ m, 0 ≤ m → m < F.reindex 0 → ∀ j', j' < S'.length → F.reindex j' ≠ m :=
        fun m _ hm j' hj' => F.reindex_ne_of_lt_reindex_zero m hm j' hj'
      have hkey := strictTransformIdeal_comap_transitionMap_eq_consolidated286 F 0 hj (F.reindex 0) 0 h0 (by omega) hskip
      have hlev : IsPullback (F.levelMap 0 hj ≫ S.ambientSeq.transitionMap h0)
          (S'.ambientSeq.projectionToBase 0) (S.ambientSeq.projectionToBase 0) F.ambientMap :=
        F.isPullback_down 0 hj 0 h0 hskip
      have hcomm : S'.ambientSeq.isoZero.inv ≫ (F.levelMap 0 hj ≫ S.ambientSeq.transitionMap h0)
          = F.ambientMap ≫ S.ambientSeq.isoZero.inv := by
        have h1 := hlev.w
        rw [S.ambientSeq.projectionToBase_zero, S'.ambientSeq.projectionToBase_zero] at h1
        have h2 : (S'.ambientSeq.isoZero.inv ≫ (F.levelMap 0 hj ≫ S.ambientSeq.transitionMap h0)) ≫
            S.ambientSeq.isoZero.hom
            = (F.ambientMap ≫ S.ambientSeq.isoZero.inv) ≫ S.ambientSeq.isoZero.hom := by
          simp only [Category.assoc] at h1 ⊢
          rw [h1]
          simp
        exact (cancel_mono S.ambientSeq.isoZero.hom).mp h2
      have hD : IsPullback F.ambientMap S'.ambientSeq.isoZero.inv S.ambientSeq.isoZero.inv
          (F.levelMap 0 hj ≫ S.ambientSeq.transitionMap h0) :=
        (IsPullback.of_horiz_isIso ⟨hcomm⟩).flip
      have hC : IsPullback F.baseMap (S'.emb ≫ S'.ambientSeq.isoZero.inv)
          (S.emb ≫ S.ambientSeq.isoZero.inv) (F.levelMap 0 hj ≫ S.ambientSeq.transitionMap h0) :=
        F.isPullback_emb.paste_vert hD
      have : QuasiCompact (S.emb ≫ S.ambientSeq.isoZero.inv) := inferInstance
      have : QuasiCompact (S'.emb ≫ S'.ambientSeq.isoZero.inv) :=
        quasiCompact_of_isPullback hC
      have : Flat (F.levelMap 0 hj ≫ S.ambientSeq.transitionMap h0) :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback
          (P := @Flat) hlev.flip inferInstance
      rw [← hkey, S'.strictTransformIdeal_zero, S.strictTransformIdeal_zero]
      exact ker_eq_comap_ker_of_isPullback_of_flat hC
  | succ n ih =>
      intro hj
      have hn : n < S'.length := Nat.lt_of_succ_le hj
      have hnle : n ≤ S'.length := Nat.le_of_lt hn
      have hσ : F.reindex n + 1 ≤ F.reindex (n + 1) := F.reindex_lt_succ n hn
      have hlen : F.reindex (n + 1) ≤ S.length := F.reindex_le_length hj
      have hIH := ih hnle
      have hcenter : S'.ambientCenter n
          = (S.ambientCenter (F.reindex n)).comap (F.levelMap n hnle) := F.center_eq n hn
      have : Flat (F.levelMap n hnle) := F.flat_levelMap n hnle
      have := S.isNoetherian_schemeAt (F.reindex n + 1) (le_trans hσ hlen)
      have := S'.isNoetherian_schemeAt (n + 1) hj
      have hst := comap_strictTransform_of_flat_of_isLocallyNoetherian
        (S.blowdown (F.reindex n)) (F.levelMap n hnle) (S'.blowdown n)
        (F.levelMap (n + 1) hj ≫ S.ambientSeq.transitionMap hσ)
        (F.isPullback_step n hn hσ) (S.ambientCenter (F.reindex n))
        (S.strictTransformIdeal (F.reindex n))
        (S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism (F.reindex n) (F.reindex_lt n hn))
      have hbet : ∀ m, F.reindex n + 1 ≤ m → m < F.reindex (n + 1) →
          ∀ j', j' < S'.length → F.reindex j' ≠ m :=
        fun m h1 h2 j' hj' => F.reindex_ne_of_reindex_lt_of_lt_reindex_succ n hn m (by omega) h2 j' hj'
      have hkey := strictTransformIdeal_comap_transitionMap_eq_consolidated286 F (n + 1) hj
        (F.reindex (n + 1) - (F.reindex n + 1)) (F.reindex n + 1) hσ (by omega) hbet
      rw [← hkey, S.strictTransformIdeal_succ (F.reindex n), hst, ← hIH, ← hcenter]
      exact S'.strictTransformIdeal_succ n


end

private theorem exists_iso_of_mono_of_comp_eq_consolidated286
    {A Z W : Scheme.{u}} (g : Z ⟶ A) (i : W ⟶ A)
    [CategoryTheory.Mono g] [CategoryTheory.Mono i] (a : W ⟶ Z) (b : Z ⟶ W)
    (ha : a ≫ g = i) (hb : b ≫ i = g) :
    ∃ u : W ≅ Z, u.hom ≫ g = i := by
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · refine (cancel_mono i).mp ?_
    rw [Category.assoc, hb, ha, Category.id_comp]
  · refine (cancel_mono g).mp ?_
    rw [Category.assoc, ha, hb, Category.id_comp]

private theorem exists_iso_subscheme_ker_consolidated286
    {A Z : Scheme.{u}} (g : Z ⟶ A) [IsClosedImmersion g] :
    ∃ u : (Scheme.Hom.ker g).subscheme ≅ Z, u.hom ≫ g = (Scheme.Hom.ker g).subschemeι := by
  have hker : Scheme.Hom.ker (Scheme.Hom.ker g).subschemeι = Scheme.Hom.ker g :=
    AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι _
  have h1 : Scheme.Hom.ker g ≤ Scheme.Hom.ker (Scheme.Hom.ker g).subschemeι :=
    le_of_eq hker.symm
  have h2 : Scheme.Hom.ker (Scheme.Hom.ker g).subschemeι ≤ Scheme.Hom.ker g := le_of_eq hker
  exact exists_iso_of_mono_of_comp_eq_consolidated286 g (Scheme.Hom.ker g).subschemeι
    (AlgebraicGeometry.IsClosedImmersion.lift g (Scheme.Hom.ker g).subschemeι h1)
    (AlgebraicGeometry.IsClosedImmersion.lift (Scheme.Hom.ker g).subschemeι g h2)
    (AlgebraicGeometry.IsClosedImmersion.lift_fac ..)
    (AlgebraicGeometry.IsClosedImmersion.lift_fac ..)

private theorem exists_isPullback_subscheme_of_ker_eq_consolidated286
    {A B : Scheme.{u}} (f : A ⟶ B) (I : B.IdealSheafData) (J : A.IdealSheafData)
    (hJ : J = Scheme.Hom.ker (pullback.fst f I.subschemeι)) :
    ∃ g : J.subscheme ⟶ I.subscheme,
      g ≫ I.subschemeι = J.subschemeι ≫ f ∧
        IsPullback g J.subschemeι I.subschemeι f := by
  subst hJ
  have : IsClosedImmersion (pullback.fst f I.subschemeι) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsClosedImmersion)
      (IsPullback.of_hasPullback f I.subschemeι).flip inferInstance
  obtain ⟨u, hu⟩ := exists_iso_subscheme_ker_consolidated286 (pullback.fst f I.subschemeι)
  have hfst : (u ≪≫ pullbackSymmetry f I.subschemeι).hom ≫ pullback.fst I.subschemeι f
      = u.hom ≫ pullback.snd f I.subschemeι := by
    rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst]
  have hsnd : (u ≪≫ pullbackSymmetry f I.subschemeι).hom ≫ pullback.snd I.subschemeι f
      = (Scheme.Hom.ker (pullback.fst f I.subschemeι)).subschemeι := by
    rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd, hu]
  have hcomm : ((u ≪≫ pullbackSymmetry f I.subschemeι).hom ≫ pullback.fst I.subschemeι f)
        ≫ I.subschemeι
      = (Scheme.Hom.ker (pullback.fst f I.subschemeι)).subschemeι ≫ f := by
    rw [hfst, Category.assoc, ← pullback.condition, ← Category.assoc, hu]
  exact ⟨(u ≪≫ pullbackSymmetry f I.subschemeι).hom ≫ pullback.fst I.subschemeι f, hcomm,
    IsPullback.of_iso_pullback ⟨hcomm⟩ (u ≪≫ pullbackSymmetry f I.subschemeι) rfl hsnd⟩

theorem exists_isPullback_strictTransformι (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j ≤ S'.length) :
    ∃ g : S'.strictTransform j ⟶ S.strictTransform (F.reindex j),
      g ≫ S.strictTransformι (F.reindex j) = S'.strictTransformι j ≫ F.levelMap j hj ∧
        IsPullback g (S'.strictTransformι j) (S.strictTransformι (F.reindex j)) (F.levelMap j hj) := by
  have hJ : S'.strictTransformIdeal j
      = Scheme.Hom.ker (pullback.fst (F.levelMap j hj)
          (S.strictTransformIdeal (F.reindex j)).subschemeι) := F.strictTransformIdeal_eq_comap j hj
  exact exists_isPullback_subscheme_of_ker_eq_consolidated286 (F.levelMap j hj)
    (S.strictTransformIdeal (F.reindex j)) (S'.strictTransformIdeal j) hJ

def strictTransformComparison (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j ≤ S'.length) :
    S'.strictTransform j ⟶ S.strictTransform (F.reindex j) :=
  (F.exists_isPullback_strictTransformι j hj).choose

section
variable (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j ≤ S'.length)

theorem strictTransformComparison_comp_strictTransformι :
    F.strictTransformComparison j hj ≫ S.strictTransformι (F.reindex j) = S'.strictTransformι j ≫ F.levelMap j hj :=
  (F.exists_isPullback_strictTransformι j hj).choose_spec.1

theorem isPullback_strictTransformComparison_strictTransformι :
    IsPullback (F.strictTransformComparison j hj) (S'.strictTransformι j) (S.strictTransformι (F.reindex j))
      (F.levelMap j hj) :=
  (F.exists_isPullback_strictTransformι j hj).choose_spec.2

theorem flat_strictTransformComparison :
    Flat (F.strictTransformComparison j hj) := by
  have hst : MorphismProperty.IsStableUnderBaseChange
      (@Flat : MorphismProperty Scheme.{u}) := inferInstance
  exact hst.of_isPullback (F.isPullback_strictTransformComparison_strictTransformι j hj).flip (F.flat_levelMap j hj)


end

end ChartFlatBaseChange

def chartFlatBaseChangeOfIsPullbackSeq (S : EmbeddedBlowupSequence k Y pY) (S' : EmbeddedBlowupSequence k' Y' pY')
    (f : S'.ambient ⟶ S.ambient) [Flat f] (b : Y' ⟶ Y)
    (hb : IsPullback b S'.emb S.emb f)
    (hpb : IsPullbackBlowupSequence f S'.ambientSeq S.ambientSeq) :
    ChartFlatBaseChange S S' where
  ambientMap := f
  flat_ambientMap := inferInstance
  baseMap := b
  isPullback_emb := hb
  reindex := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose
  levelMap := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose
  reindex_lt := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.1
  reindex_lt_succ := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.1
  reindex_len := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.2.1
  isPullback_level := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.2.2.1
  isPullback_down := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.2.2.2.1
  isPullback_step :=
    (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.2.2.2.2.1
  center_eq :=
    (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.2.2.2.2.2.1
  comap_center_skipped :=
    (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.2.2.2.2.2.2


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ChartPushforward
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section

def subschemeIsoOfEq {V : Scheme.{u}} {I J : V.IdealSheafData} (h : I = J) :
    I.subscheme ≅ J.subscheme :=
  eqToIso (congrArg (fun K : V.IdealSheafData => K.subscheme) h)

@[reassoc (attr := simp)]
theorem subschemeIsoOfEq_hom_subschemeι {V : Scheme.{u}} {I J : V.IdealSheafData} (h : I = J) :
    (subschemeIsoOfEq h).hom ≫ J.subschemeι = I.subschemeι := by
  subst h
  simp [subschemeIsoOfEq]

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]

structure ChartPushforward (S S' : EmbeddedBlowupSequence k Y pY) where
  ambientMap : S.ambient ⟶ S'.ambient
  isClosedImmersion_ambientMap : IsClosedImmersion ambientMap
  emb_ambientMap : S.emb ≫ ambientMap = S'.emb
  len_eq : S.length = S'.length
  levelMap : ∀ i : ℕ, i ≤ S'.length → (S.schemeAt i ⟶ S'.schemeAt i)
  isClosedImmersion_levelMap :
    ∀ (i : ℕ) (hi : i ≤ S'.length), IsClosedImmersion (levelMap i hi)
  levelMap_zero :
    levelMap 0 (Nat.zero_le _) ≫ S'.ambientSeq.isoZero.hom =
      S.ambientSeq.isoZero.hom ≫ ambientMap
  levelMap_blowdown :
    ∀ (i : ℕ) (hi : i < S'.length),
      levelMap (i + 1) hi ≫ S'.blowdown i = S.blowdown i ≫ levelMap i hi.le
  ambientCenter_eq :
    ∀ (i : ℕ) (hi : i < S'.length),
      S'.ambientCenter i = imageIdealSheaf (levelMap i hi.le) (S.ambientCenter i)
  ker_levelMap_succ :
    ∀ (i : ℕ) (hi : i < S'.length),
      (levelMap (i + 1) hi).ker =
        Blowup.strictTransform (S'.blowdown i) (S'.ambientCenter i) (levelMap i hi.le).ker

namespace ChartPushforward

section

variable {S S' : EmbeddedBlowupSequence k Y pY}

instance instIsClosedImmersionAmbientMap (P : ChartPushforward S S') :
    IsClosedImmersion P.ambientMap :=
  P.isClosedImmersion_ambientMap

instance instIsClosedImmersionLevelMap (P : ChartPushforward S S') (i : ℕ) (hi : i ≤ S'.length) :
    IsClosedImmersion (P.levelMap i hi) :=
  P.isClosedImmersion_levelMap i hi

theorem le_length (P : ChartPushforward S S') {i : ℕ} (hi : i ≤ S'.length) : i ≤ S.length :=
  hi.trans_eq P.len_eq.symm

end

section

variable (S S' : EmbeddedBlowupSequence k Y pY) (f : S.ambient ⟶ S'.ambient)
  [IsClosedImmersion f]

section
variable (h : IsPushforwardBlowupSeq f S.ambientSeq S'.ambientSeq)

private theorem isClosedImmersion_of_isPushforwardBlowupSeq_consolidated287
    (i : ℕ) (hi : i ≤ S'.length) :
    IsClosedImmersion (h.2.choose i (hi.trans_eq h.1.symm)) :=
  h.2.choose_spec.1 i (hi.trans_eq h.1.symm)

private theorem isoObjZero_comm_of_isPushforwardBlowupSeq_consolidated287
    :
    h.2.choose 0 ((Nat.zero_le S'.length).trans_eq h.1.symm) ≫ S'.ambientSeq.isoZero.hom =
      S.ambientSeq.isoZero.hom ≫ f := by
  exact h.2.choose_spec.2.1


end

section
variable (h : IsPushforwardBlowupSeq f S.ambientSeq S'.ambientSeq) (i : ℕ) (hi : i < S'.length)

private theorem blowdown_comm_of_isPushforwardBlowupSeq_consolidated287
    :
    h.2.choose (i + 1) (hi.trans_eq h.1.symm) ≫ S'.blowdown i =
      S.blowdown i ≫ h.2.choose i (hi.le.trans_eq h.1.symm) :=
  h.2.choose_spec.2.2.1 i (hi.trans_eq h.1.symm)

private theorem ambientCenter_eq_imageIdealSheaf_of_isPushforwardBlowupSeq_consolidated287
    :
    S'.ambientCenter i =
      imageIdealSheaf (h.2.choose i (hi.le.trans_eq h.1.symm)) (S.ambientCenter i) :=
  h.2.choose_spec.2.2.2.1 i (hi.trans_eq h.1.symm)

private theorem ker_succ_eq_strictTransform_of_isPushforwardBlowupSeq_consolidated287
    :
    (h.2.choose (i + 1) (hi.trans_eq h.1.symm)).ker =
      Blowup.strictTransform (S'.blowdown i) (S'.ambientCenter i)
        (h.2.choose i (hi.le.trans_eq h.1.symm)).ker :=
  h.2.choose_spec.2.2.2.2 i (hi.trans_eq h.1.symm)


end

def ofIsPushforwardSeq (hemb : S.emb ≫ f = S'.emb)
    (h : IsPushforwardBlowupSeq f S.ambientSeq S'.ambientSeq) : ChartPushforward S S' where
  ambientMap := f
  isClosedImmersion_ambientMap := inferInstance
  emb_ambientMap := hemb
  len_eq := h.1
  levelMap := fun i hi => h.2.choose i (hi.trans_eq h.1.symm)
  isClosedImmersion_levelMap := fun i hi => isClosedImmersion_of_isPushforwardBlowupSeq_consolidated287 S S' f h i hi
  levelMap_zero := isoObjZero_comm_of_isPushforwardBlowupSeq_consolidated287 S S' f h
  levelMap_blowdown := fun i hi => blowdown_comm_of_isPushforwardBlowupSeq_consolidated287 S S' f h i hi
  ambientCenter_eq := fun i hi => ambientCenter_eq_imageIdealSheaf_of_isPushforwardBlowupSeq_consolidated287 S S' f h i hi
  ker_levelMap_succ := fun i hi => ker_succ_eq_strictTransform_of_isPushforwardBlowupSeq_consolidated287 S S' f h i hi





end

section

variable {S S' : EmbeddedBlowupSequence k Y pY}

private theorem map_strictTransformIdeal_levelMap_consolidated287 {T T' : EmbeddedBlowupSequence k Y pY}
    (P : ChartPushforward T T') (i : ℕ) :
    ∀ hi : i ≤ T'.length, (T.strictTransformIdeal i).map (P.levelMap i hi) = T'.strictTransformIdeal i := by
  induction i with
  | zero =>
    intro hi
    have key : T.ambientSeq.isoZero.inv ≫ P.levelMap 0 hi
        = P.ambientMap ≫ T'.ambientSeq.isoZero.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← P.levelMap_zero, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    have hcomp : (T.emb ≫ T.ambientSeq.isoZero.inv) ≫ P.levelMap 0 hi
        = T'.emb ≫ T'.ambientSeq.isoZero.inv := by
      rw [Category.assoc, key, ← Category.assoc, P.emb_ambientMap]
    rw [EmbeddedBlowupSequence.strictTransformIdeal_zero, EmbeddedBlowupSequence.strictTransformIdeal_zero, ← Scheme.Hom.ker_comp, hcomp]
  | succ n ih =>
    intro hi
    have hn : n < T'.length := Nat.lt_of_succ_le hi
    have : IsNoetherian (T.schemeAt (n + 1)) :=
      T.isNoetherian_schemeAt (n + 1) (P.le_length hi)
    have : IsNoetherian (T'.schemeAt (n + 1)) :=
      T'.isNoetherian_schemeAt (n + 1) hi
    have hsq : P.levelMap (n + 1) hi ≫ T'.blowdown n = T.blowdown n ≫ P.levelMap n hn.le :=
      P.levelMap_blowdown n hn
    have hcenter : (T.ambientCenter n).map (P.levelMap n hn.le) = T'.ambientCenter n := by
      rw [map_eq_ker_subschemeι_comp, P.ambientCenter_eq n hn, imageIdealSheaf_eq_ker]
    have hker : Scheme.Hom.ker (P.levelMap (n + 1) hi)
        = Blowup.strictTransform (T'.blowdown n) ((T.ambientCenter n).map (P.levelMap n hn.le))
            (Scheme.Hom.ker (P.levelMap n hn.le)) := by
      rw [hcenter]
      exact P.ker_levelMap_succ n hn
    have hmain := map_strictTransform_eq_strictTransform_map (P.levelMap n hn.le)
      (T.ambientCenter n) (T.strictTransformIdeal n) (T.blowdown n) (T'.blowdown n)
      (P.levelMap (n + 1) hi) hsq hker
    rw [EmbeddedBlowupSequence.strictTransformIdeal_succ, EmbeddedBlowupSequence.strictTransformIdeal_succ, hmain, ih hn.le, hcenter]

theorem exists_strictTransform_iso (P : ChartPushforward S S') (i : ℕ) (hi : i ≤ S'.length) :
    ∃ e : S.strictTransform i ≅ S'.strictTransform i,
      e.hom ≫ S'.strictTransformι i = S.strictTransformι i ≫ P.levelMap i hi := by
  have hmap := map_strictTransformIdeal_levelMap_consolidated287 P i hi
  have hA : Scheme.Hom.ker (S.strictTransformι i) = S.strictTransformIdeal i := by
    rw [S.strictTransformι_eq_subschemeι]
    exact Scheme.IdealSheafData.ker_subschemeι _
  have hA' : Scheme.Hom.ker (S'.strictTransformι i) = S'.strictTransformIdeal i := by
    rw [S'.strictTransformι_eq_subschemeι]
    exact Scheme.IdealSheafData.ker_subschemeι _
  have : IsClosedImmersion (S.strictTransformι i ≫ P.levelMap i hi) := inferInstance
  have hker : Scheme.Hom.ker (S'.strictTransformι i) = Scheme.Hom.ker (S.strictTransformι i ≫ P.levelMap i hi) := by
    rw [Scheme.Hom.ker_comp, hA, hA', hmap]
  have := AlgebraicGeometry.IsClosedImmersion.isIso_lift (S'.strictTransformι i)
    (S.strictTransformι i ≫ P.levelMap i hi) hker
  refine ⟨asIso (AlgebraicGeometry.IsClosedImmersion.lift (S'.strictTransformι i)
    (S.strictTransformι i ≫ P.levelMap i hi) (le_of_eq hker)), ?_⟩
  rw [asIso_hom, AlgebraicGeometry.IsClosedImmersion.lift_fac]

def strictTransformIso (P : ChartPushforward S S') (i : ℕ) (hi : i ≤ S'.length) :
    S.strictTransform i ≅ S'.strictTransform i :=
  (P.exists_strictTransform_iso i hi).choose

@[reassoc (attr := simp)]
theorem strictTransformIso_hom_comp_strictTransformι (P : ChartPushforward S S') (i : ℕ) (hi : i ≤ S'.length) :
    (P.strictTransformIso i hi).hom ≫ S'.strictTransformι i = S.strictTransformι i ≫ P.levelMap i hi :=
  (P.exists_strictTransform_iso i hi).choose_spec

@[reassoc]
theorem strictTransformIso_hom_comp_strictTransformMap (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    (P.strictTransformIso (i + 1) hi).hom ≫ S'.strictTransformMap i =
      S.strictTransformMap i ≫ (P.strictTransformIso i hi.le).hom := by
  have hmono : Mono (S'.strictTransformι i) := by
    rw [EmbeddedBlowupSequence.strictTransformι_eq_subschemeι]
    infer_instance
  rw [← cancel_mono (S'.strictTransformι i)]
  simp only [Category.assoc]
  rw [strictTransformIso_hom_comp_strictTransformι P i hi.le, EmbeddedBlowupSequence.strictTransformMap_comp_strictTransformι S' i, ← Category.assoc,
    strictTransformIso_hom_comp_strictTransformι P (i + 1) hi, Category.assoc, P.levelMap_blowdown i hi,
    ← Category.assoc, ← EmbeddedBlowupSequence.strictTransformMap_comp_strictTransformι S i, Category.assoc]

theorem strictTransformIso_zero_hom_comp_strictTransformZeroIso_hom (P : ChartPushforward S S') :
    (P.strictTransformIso 0 (Nat.zero_le _)).hom ≫ S'.strictTransformZeroIso.hom = S.strictTransformZeroIso.hom := by
  have key : ((P.strictTransformIso 0 (Nat.zero_le _)).hom ≫ S'.strictTransformZeroIso.hom) ≫ S'.emb
      = S.strictTransformZeroIso.hom ≫ S'.emb := by
    calc ((P.strictTransformIso 0 (Nat.zero_le _)).hom ≫ S'.strictTransformZeroIso.hom) ≫ S'.emb
        = (P.strictTransformIso 0 (Nat.zero_le _)).hom ≫ (S'.strictTransformZeroIso.hom ≫ S'.emb) := by
          rw [Category.assoc]
      _ = (P.strictTransformIso 0 (Nat.zero_le _)).hom ≫ (S'.strictTransformι 0 ≫ S'.ambientSeq.isoZero.hom) := by
          rw [S'.strictTransformZeroIso_hom_emb]
      _ = ((P.strictTransformIso 0 (Nat.zero_le _)).hom ≫ S'.strictTransformι 0) ≫ S'.ambientSeq.isoZero.hom := by
          rw [Category.assoc]
      _ = (S.strictTransformι 0 ≫ P.levelMap 0 (Nat.zero_le _)) ≫ S'.ambientSeq.isoZero.hom := by
          rw [P.strictTransformIso_hom_comp_strictTransformι 0 (Nat.zero_le _)]
      _ = S.strictTransformι 0 ≫ (P.levelMap 0 (Nat.zero_le _) ≫ S'.ambientSeq.isoZero.hom) := by
          rw [Category.assoc]
      _ = S.strictTransformι 0 ≫ (S.ambientSeq.isoZero.hom ≫ P.ambientMap) := by
          rw [P.levelMap_zero]
      _ = (S.strictTransformι 0 ≫ S.ambientSeq.isoZero.hom) ≫ P.ambientMap := by
          rw [Category.assoc]
      _ = (S.strictTransformZeroIso.hom ≫ S.emb) ≫ P.ambientMap := by
          rw [S.strictTransformZeroIso_hom_emb]
      _ = S.strictTransformZeroIso.hom ≫ (S.emb ≫ P.ambientMap) := by
          rw [Category.assoc]
      _ = S.strictTransformZeroIso.hom ≫ S'.emb := by
          rw [P.emb_ambientMap]
  exact (cancel_mono S'.emb).mp key

private theorem range_subset_range_of_ker_le_consolidated287 {U V W : Scheme.{u}} (f : U ⟶ W) (g : V ⟶ W)
    [IsClosedImmersion f] [IsClosedImmersion g]
    (hle : Scheme.Hom.ker g ≤ Scheme.Hom.ker f) :
    Set.range ⇑f ⊆ Set.range ⇑g := by
  obtain ⟨e, he⟩ : ∃ e : U ⟶ V, e ≫ g = f :=
    ⟨AlgebraicGeometry.IsClosedImmersion.lift g f hle, by rw [IsClosedImmersion.lift_fac]⟩
  rintro y ⟨x, rfl⟩
  refine ⟨e.base x, ?_⟩
  have hx : ⇑(e ≫ g) x = ⇑f x := by rw [he]
  exact hx

private theorem support_ker_eq_range_consolidated287 {U W : Scheme.{u}} (h : U ⟶ W)
    [IsClosedImmersion h] :
    ((Scheme.Hom.ker h).support : Set ↥W) = Set.range ⇑h := by
  have hker : Scheme.Hom.ker ((Scheme.Hom.ker h).subschemeι) = Scheme.Hom.ker h :=
    Scheme.IdealSheafData.ker_subschemeι _
  have h1 : Set.range ⇑((Scheme.Hom.ker h).subschemeι)
      = ((Scheme.Hom.ker h).support : Set ↥W) :=
    Scheme.IdealSheafData.range_subschemeι _
  rw [← h1]
  exact Set.Subset.antisymm (range_subset_range_of_ker_le_consolidated287 _ h (le_of_eq hker.symm))
    (range_subset_range_of_ker_le_consolidated287 h _ (le_of_eq hker))

theorem support_ambientCenter_eq_image (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    ((S'.ambientCenter i).support : Set ↥(S'.schemeAt i)) =
      ⇑(P.levelMap i hi.le) '' ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
  have hJ := P.ambientCenter_eq i hi
  rw [imageIdealSheaf_eq_ker] at hJ
  have hI : ((S.ambientCenter i).support : Set ↥(S.schemeAt i))
      = Set.range ⇑((S.ambientCenter i).subschemeι) := by
    have h2 := support_ker_eq_range_consolidated287 ((S.ambientCenter i).subschemeι)
    rwa [Scheme.IdealSheafData.ker_subschemeι] at h2
  have hcomp : ⇑((S.ambientCenter i).subschemeι ≫ P.levelMap i hi.le)
      = ⇑(P.levelMap i hi.le) ∘ ⇑((S.ambientCenter i).subschemeι) := rfl
  rw [hJ, support_ker_eq_range_consolidated287, hI, hcomp, Set.range_comp]

end

end ChartPushforward


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.DetachedLocusFlatBaseChange
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

section

private theorem exists_isPullback_subschemeι_comap_consolidated305 {X X' : Scheme.{u}} (f : X' ⟶ X)
    (I : X.IdealSheafData) :
    ∃ g : (I.comap f).subscheme ⟶ I.subscheme,
      g ≫ I.subschemeι = (I.comap f).subschemeι ≫ f ∧
        IsPullback g (I.comap f).subschemeι I.subschemeι f := by
  have hker : Scheme.Hom.ker (I.comap f).subschemeι
      = Scheme.Hom.ker (pullback.fst f I.subschemeι) :=
    (Scheme.IdealSheafData.ker_subschemeι _).trans rfl
  obtain ⟨u, hufac⟩ : ∃ u : (I.comap f).subscheme ⟶ pullback f I.subschemeι,
      u ≫ pullback.fst f I.subschemeι = (I.comap f).subschemeι :=
    ⟨IsClosedImmersion.lift _ _ hker.ge, IsClosedImmersion.lift_fac _ _ hker.ge⟩
  obtain ⟨v, hvfac⟩ : ∃ v : pullback f I.subschemeι ⟶ (I.comap f).subscheme,
      v ≫ (I.comap f).subschemeι = pullback.fst f I.subschemeι :=
    ⟨IsClosedImmersion.lift _ _ hker.le, IsClosedImmersion.lift_fac _ _ hker.le⟩
  have huv : u ≫ v = 𝟙 _ := by
    apply (cancel_mono (I.comap f).subschemeι).1
    rw [Category.assoc, hvfac, hufac, Category.id_comp]
  have hvu : v ≫ u = 𝟙 _ := by
    apply (cancel_mono (pullback.fst f I.subschemeι)).1
    rw [Category.assoc, hufac, hvfac, Category.id_comp]
  have hw : (I.comap f).subschemeι ≫ f
      = (u ≫ pullback.snd f I.subschemeι) ≫ I.subschemeι := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hufac]
  refine ⟨u ≫ pullback.snd f I.subschemeι, hw.symm, ?_⟩
  exact (IsPullback.of_iso_pullback ⟨hw⟩
    (⟨u, v, huv, hvu⟩ : (I.comap f).subscheme ≅ pullback f I.subschemeι) hufac rfl).flip

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]
  {k' : Type u} [Field k'] [CharZero k'] {Y' : Scheme.{u}} [IsAffine Y']
  {pY' : Y' ⟶ Spec (CommRingCat.of k')} [LocallyOfFiniteType pY']

namespace EmbeddedBlowupSequence

section
variable (S : EmbeddedBlowupSequence k Y pY)

theorem noetherianSpace_strictTransform (i : ℕ) (hi : i ≤ S.length) :
    TopologicalSpace.NoetherianSpace ↥(S.strictTransform i) := by
  have : IsNoetherian (S.schemeAt i) := S.isNoetherian_schemeAt i hi
  exact S.noetherianSpace_strictTransform_of_noetherianSpace_schemeAt i inferInstance

theorem isReduced_strictTransform [IsReduced Y]
    (i : ℕ) (hi : i ≤ S.length) : IsReduced (S.strictTransform i) :=
  S.isReduced_strictTransform_of_isNoetherian (fun j hj => S.isNoetherian_schemeAt j hj) i hi


end

end EmbeddedBlowupSequence

namespace ChartFlatBaseChange

variable {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

section
variable (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length)

theorem mem_support_ambientCenter_iff (y : ↥(S'.strictTransform j)) :
    (S'.strictTransformι j) y ∈ (↑(S'.ambientCenter j).support : Set ↥(S'.schemeAt j)) ↔
      (S.strictTransformι (F.reindex j)) ((F.strictTransformComparison j hj.le) y) ∈
        (↑(S.ambientCenter (F.reindex j)).support : Set ↥(S.schemeAt (F.reindex j))) := by
  have hcomp : (S.strictTransformι (F.reindex j)) ((F.strictTransformComparison j hj.le) y)
      = (F.levelMap j hj.le) ((S'.strictTransformι j) y) :=
    congrArg (fun f : S'.strictTransform j ⟶ S.schemeAt (F.reindex j) => f y)
      (F.strictTransformComparison_comp_strictTransformι j hj.le)
  rw [F.center_eq j hj, FunctorialResolution.EmbeddedResolution.support_comap, Set.mem_preimage, hcomp]

theorem detachedLocus_eq_preimage :
    S'.detachedLocus j =
      (fun x : ↥(S'.strictTransform j) => (F.strictTransformComparison j hj.le) x) ⁻¹'
        S.detachedLocus (F.reindex j) := by
  have := F.flat_strictTransformComparison j hj.le
  have himg := F.mem_support_ambientCenter_iff j hj
  have hclosed : IsClosed
      ((fun z : ↥(S.strictTransform (F.reindex j)) => (S.strictTransformι (F.reindex j)) z) ⁻¹'
        (↑(S.ambientCenter (F.reindex j)).support : Set ↥(S.schemeAt (F.reindex j)))) := by
    rw [← FunctorialResolution.EmbeddedResolution.support_comap]
    exact ((S.ambientCenter (F.reindex j)).comap (S.strictTransformι (F.reindex j))).support.2
  refine Set.ext fun x => ?_
  simp only [Set.mem_preimage, S'.detachedLocus_eq_sUnion j, S.detachedLocus_eq_sUnion (F.reindex j), Set.mem_sUnion]
  constructor
  · rintro ⟨C', hC', hxC'⟩
    rw [S'.mem_detachedComponents] at hC'
    obtain ⟨hirr, hsub⟩ := hC'
    refine ⟨closure ((fun z : ↥(S'.strictTransform j) => (F.strictTransformComparison j hj.le) z) '' C'), ?_, ?_⟩
    · rw [S.mem_detachedComponents]
      refine ⟨FunctorialResolution.EmbeddedResolution.closure_image_mem_irreducibleComponents_of_flat _ hirr, ?_⟩
      rw [Set.image_subset_iff]
      refine closure_minimal ?_ hclosed
      rintro _ ⟨y, hy, rfl⟩
      exact (himg y).1 (hsub ⟨y, hy, rfl⟩)
    · exact subset_closure ⟨x, hxC', rfl⟩
  · rintro ⟨C, hC, hxC⟩
    rw [S.mem_detachedComponents] at hC
    obtain ⟨hirr, hsub⟩ := hC
    obtain ⟨C', hC'irr, hxC', hcl⟩ :=
      (FunctorialResolution.EmbeddedResolution.apply_mem_irreducibleComponent_iff_of_flat (F.strictTransformComparison j hj.le) hirr x).1 hxC
    refine ⟨C', ?_, hxC'⟩
    rw [S'.mem_detachedComponents]
    refine ⟨hC'irr, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    refine (himg y).2 ?_
    have hgy : (F.strictTransformComparison j hj.le) y ∈ C := by
      rw [← hcl]
      exact subset_closure ⟨y, hy, rfl⟩
    exact hsub ⟨_, hgy, rfl⟩

theorem coe_detachedClosure_eq_preimage :
    (↑(S'.detachedClosure j) : Set ↥(S'.strictTransform j)) =
      (fun x : ↥(S'.strictTransform j) => (F.strictTransformComparison j hj.le) x) ⁻¹'
        (↑(S.detachedClosure (F.reindex j)) : Set ↥(S.strictTransform (F.reindex j))) := by
  have : TopologicalSpace.NoetherianSpace ↥(S'.strictTransform j) :=
    S'.noetherianSpace_strictTransform j hj.le
  have : TopologicalSpace.NoetherianSpace ↥(S.strictTransform (F.reindex j)) :=
    S.noetherianSpace_strictTransform (F.reindex j) (F.reindex_le_length hj.le)
  rw [S'.detachedClosure_coe j, S.detachedClosure_coe (F.reindex j), F.detachedLocus_eq_preimage j hj]


end

section
variable (F : ChartFlatBaseChange S S') [IsReduced Y] [IsReduced Y'] (j : ℕ) (hj : j < S'.length)

theorem detachedIdeal_eq_comap :
    S'.detachedIdeal j = (S.detachedIdeal (F.reindex j)).comap (F.strictTransformComparison j hj.le) := by
  have : TopologicalSpace.NoetherianSpace ↥(S'.strictTransform j) :=
    S'.noetherianSpace_strictTransform j hj.le
  have : TopologicalSpace.NoetherianSpace ↥(S.strictTransform (F.reindex j)) :=
    S.noetherianSpace_strictTransform (F.reindex j) (F.reindex_le_length hj.le)
  have := S'.isReduced_strictTransform j hj.le
  have := S.isReduced_strictTransform (F.reindex j) (F.reindex_le_length hj.le)
  have := F.flat_strictTransformComparison j hj.le
  have hS : S.detachedComponents (F.reindex j) ⊆
      irreducibleComponents ↥(S.strictTransform (F.reindex j)) :=
    fun C hC => ((S.mem_detachedComponents (F.reindex j) C).1 hC).1
  have hZ : (↑(S.detachedClosure (F.reindex j)) : Set ↥(S.strictTransform (F.reindex j)))
      = ⋃₀ S.detachedComponents (F.reindex j) := by
    rw [S.detachedClosure_coe (F.reindex j)]
    exact S.detachedLocus_eq_sUnion (F.reindex j)
  have hZ' : (↑(S'.detachedClosure j) : Set ↥(S'.strictTransform j))
      = ⇑(F.strictTransformComparison j hj.le).base ⁻¹' (⋃₀ S.detachedComponents (F.reindex j)) := by
    have h := F.coe_detachedClosure_eq_preimage j hj
    rw [S.detachedClosure_coe (F.reindex j), S.detachedLocus_eq_sUnion (F.reindex j)] at h
    exact h
  rw [S'.detachedIdeal_eq j, S.detachedIdeal_eq (F.reindex j)]
  exact (comap_vanishingIdeal_sUnion (F.strictTransformComparison j hj.le)
    (S := S.detachedComponents (F.reindex j)) (Z := S.detachedClosure (F.reindex j))
    (Z' := S'.detachedClosure j) hS hZ hZ').symm

theorem exists_isPullback_detachedScheme :
    ∃ g : S'.detachedScheme j ⟶ S.detachedScheme (F.reindex j),
      g ≫ S.detachedι (F.reindex j) = S'.detachedι j ≫ F.strictTransformComparison j hj.le ∧
        IsPullback g (S'.detachedι j) (S.detachedι (F.reindex j)) (F.strictTransformComparison j hj.le) := by
  have key : ∀ J : (S'.strictTransform j).IdealSheafData,
      J = (S.detachedIdeal (F.reindex j)).comap (F.strictTransformComparison j hj.le) →
      ∃ g : J.subscheme ⟶ (S.detachedIdeal (F.reindex j)).subscheme,
        g ≫ (S.detachedIdeal (F.reindex j)).subschemeι =
            J.subschemeι ≫ F.strictTransformComparison j hj.le ∧
          IsPullback g J.subschemeι (S.detachedIdeal (F.reindex j)).subschemeι
            (F.strictTransformComparison j hj.le) := by
    rintro J rfl
    exact exists_isPullback_subschemeι_comap_consolidated305 _ _
  exact key (S'.detachedIdeal j) (F.detachedIdeal_eq_comap j hj)


end

def detachedSchemeComparison (F : ChartFlatBaseChange S S') [IsReduced Y]
    [IsReduced Y'] (j : ℕ) (hj : j < S'.length) :
    S'.detachedScheme j ⟶ S.detachedScheme (F.reindex j) :=
  (F.exists_isPullback_detachedScheme j hj).choose

section
variable (F : ChartFlatBaseChange S S') [IsReduced Y] [IsReduced Y'] (j : ℕ) (hj : j < S'.length)

theorem detachedSchemeComparison_comp_detachedι :
    F.detachedSchemeComparison j hj ≫ S.detachedι (F.reindex j) =
      S'.detachedι j ≫ F.strictTransformComparison j hj.le :=
  (F.exists_isPullback_detachedScheme j hj).choose_spec.1

theorem detachedSchemeComparison_comp_detachedι_assoc {Z : Scheme.{u}}
    (h : S.strictTransform (F.reindex j) ⟶ Z) :
    F.detachedSchemeComparison j hj ≫ S.detachedι (F.reindex j) ≫ h =
      S'.detachedι j ≫ F.strictTransformComparison j hj.le ≫ h := by
  rw [← Category.assoc, F.detachedSchemeComparison_comp_detachedι j hj, Category.assoc]

theorem isPullback_detachedSchemeComparison :
    IsPullback (F.detachedSchemeComparison j hj) (S'.detachedι j) (S.detachedι (F.reindex j))
      (F.strictTransformComparison j hj.le) :=
  (F.exists_isPullback_detachedScheme j hj).choose_spec.2


end

section
variable (F : ChartFlatBaseChange S S')

theorem detachedClosureCompl_eq_preimage (j : ℕ) (hj : j < S'.length) :
    S'.detachedClosureCompl j = (F.strictTransformComparison j hj.le) ⁻¹ᵁ (S.detachedClosureCompl (F.reindex j)) := by
  refine TopologicalSpace.Opens.ext ?_
  have h1 : (↑(S'.detachedClosureCompl j) : Set ↥(S'.strictTransform j))
      = (↑(S'.detachedClosure j) : Set ↥(S'.strictTransform j))ᶜ := S'.detachedClosureCompl_coe j
  have h2 : (↑((F.strictTransformComparison j hj.le) ⁻¹ᵁ (S.detachedClosureCompl (F.reindex j)))
        : Set ↥(S'.strictTransform j))
      = (fun x : ↥(S'.strictTransform j) => (F.strictTransformComparison j hj.le) x) ⁻¹'
        (↑(S.detachedClosureCompl (F.reindex j)) : Set ↥(S.strictTransform (F.reindex j))) := rfl
  rw [h1, h2, S.detachedClosureCompl_coe (F.reindex j), Set.preimage_compl,
    F.coe_detachedClosure_eq_preimage j hj]

theorem isEmpty_of_forall_reindex_ne (s : ℕ) (hs : s < S.length)
    (hskip : ∀ j, j < S'.length → F.reindex j ≠ s) (P : Scheme.{u})
    (q : P ⟶ S.detachedScheme s) (p : P ⟶ S'.ambient)
    (hcomm : q ≫ S.detachedι s ≫ S.strictTransformι s ≫ S.ambientSeq.projectionToBase s = p ≫ F.ambientMap) :
    IsEmpty ↥P := by
  have : TopologicalSpace.NoetherianSpace ↥(S.strictTransform s) :=
    S.noetherianSpace_strictTransform s hs.le
  constructor
  intro x
  have hcsq : (q ≫ S.detachedι s ≫ S.strictTransformι s) ≫ S.ambientSeq.projectionToBase s = p ≫ F.ambientMap := by
    simp only [Category.assoc]
    exact hcomm
  have hpb := IsPullback.of_hasPullback (S.ambientSeq.projectionToBase s) F.ambientMap
  have hcomap := F.comap_center_skipped s hs hskip
    (pullback (S.ambientSeq.projectionToBase s) F.ambientMap)
    (pullback.fst (S.ambientSeq.projectionToBase s) F.ambientMap)
    (pullback.snd (S.ambientSeq.projectionToBase s) F.ambientMap) hpb
  have hwf : hpb.lift _ _ hcsq ≫ pullback.fst (S.ambientSeq.projectionToBase s) F.ambientMap
      = q ≫ S.detachedι s ≫ S.strictTransformι s := hpb.lift_fst _ _ hcsq
  have hpt : (pullback.fst (S.ambientSeq.projectionToBase s) F.ambientMap) ((hpb.lift _ _ hcsq) x)
      = (S.strictTransformι s) ((S.detachedι s) (q x)) :=
    congrArg (fun f : P ⟶ S.schemeAt s => f x) hwf
  have hfl : (S.detachedι s) (q x) ∈ S.detachedLocus s := by
    have h1 : (S.detachedι s) (q x) ∈ (↑(S.detachedIdeal s).support : Set ↥(S.strictTransform s)) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨q x, rfl⟩
    rw [S.detachedIdeal_eq s] at h1
    have h2 := (Scheme.IdealSheafData.coe_support_vanishingIdeal (S.detachedClosure s)).le h1
    rw [S.detachedClosure_coe s] at h2
    exact h2
  have hmem : (S.strictTransformι s) ((S.detachedι s) (q x)) ∈
      (↑(S.ambientCenter s).support : Set ↥(S.schemeAt s)) :=
    S.image_detachedLocus_subset_ambientCenter_support s ⟨_, hfl, rfl⟩
  have hmem2 : (hpb.lift _ _ hcsq) x ∈ (↑((S.ambientCenter s).comap
      (pullback.fst (S.ambientSeq.projectionToBase s) F.ambientMap)).support
        : Set ↥(pullback (S.ambientSeq.projectionToBase s) F.ambientMap)) := by
    rw [FunctorialResolution.EmbeddedResolution.support_comap, Set.mem_preimage, hpt]
    exact hmem
  rw [hcomap] at hmem2
  simp at hmem2


end

end ChartFlatBaseChange


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.DetachedCenterFlatBaseChange
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

section

namespace ChartFlatBaseChange

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]
  {k' : Type u} [Field k'] [CharZero k'] {Y' : Scheme.{u}} [IsAffine Y']
  {pY' : Y' ⟶ Spec (CommRingCat.of k')} [LocallyOfFiniteType pY']
  {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

private theorem map_eq_ker_subschemeι_comp_consolidated323 {X Y : Scheme.{u}} (f : X ⟶ Y) (I : X.IdealSheafData) :
    I.map f = Scheme.Hom.ker (I.subschemeι ≫ f) := rfl

section
variable (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length)

theorem comapAmbientCenter_eq_comap :
    S'.comapAmbientCenter j =
      (S.comapAmbientCenter (F.reindex j)).comap (F.strictTransformComparison j hj.le) := by
  have h1 : S'.ambientCenter j
      = (S.ambientCenter (F.reindex j)).comap (F.levelMap j hj.le) := F.center_eq j hj
  have h2 : F.strictTransformComparison j hj.le ≫ S.strictTransformι (F.reindex j)
      = S'.strictTransformι j ≫ F.levelMap j hj.le := F.strictTransformComparison_comp_strictTransformι j hj.le
  calc S'.comapAmbientCenter j = (S'.ambientCenter j).comap (S'.strictTransformι j) := rfl
    _ = ((S.ambientCenter (F.reindex j)).comap (F.levelMap j hj.le)).comap (S'.strictTransformι j) := by
        rw [h1]
    _ = (S.ambientCenter (F.reindex j)).comap (S'.strictTransformι j ≫ F.levelMap j hj.le) := by
        simp [Scheme.IdealSheafData.comap_comp]
    _ = (S.ambientCenter (F.reindex j)).comap
          (F.strictTransformComparison j hj.le ≫ S.strictTransformι (F.reindex j)) := by rw [h2]
    _ = ((S.ambientCenter (F.reindex j)).comap (S.strictTransformι (F.reindex j))).comap
          (F.strictTransformComparison j hj.le) := by simp [Scheme.IdealSheafData.comap_comp]
    _ = (S.comapAmbientCenter (F.reindex j)).comap (F.strictTransformComparison j hj.le) := rfl

theorem centerOffDetached_eq_comap :
    S'.centerOffDetached j =
      (S.centerOffDetached (F.reindex j)).comap (F.strictTransformComparison j hj.le) := by
  have hflat : Flat (F.strictTransformComparison j hj.le) := F.flat_strictTransformComparison j hj.le
  have hnoe : TopologicalSpace.NoetherianSpace ↥(S.strictTransform (F.reindex j)) :=
    S.noetherianSpace_strictTransform (F.reindex j) (F.reindex_le_length hj.le)
  have hqc : QuasiCompact (S.detachedClosureCompl (F.reindex j)).ι :=
    ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hpb : IsPullback (F.strictTransformComparison j hj.le ∣_ S.detachedClosureCompl (F.reindex j))
      ((F.strictTransformComparison j hj.le ⁻¹ᵁ S.detachedClosureCompl (F.reindex j)).ι)
      (S.detachedClosureCompl (F.reindex j)).ι (F.strictTransformComparison j hj.le) :=
    AlgebraicGeometry.isPullback_morphismRestrict _ _
  have key := comap_map_eq_map_comap_of_isPullback hpb
      ((S.comapAmbientCenter (F.reindex j)).comap (S.detachedClosureCompl (F.reindex j)).ι)
  have htrace : S'.comapAmbientCenter j
      = (S.comapAmbientCenter (F.reindex j)).comap (F.strictTransformComparison j hj.le) :=
    F.comapAmbientCenter_eq_comap j hj
  have hcomap :
      ((S.comapAmbientCenter (F.reindex j)).comap (S.detachedClosureCompl (F.reindex j)).ι).comap
          (F.strictTransformComparison j hj.le ∣_ S.detachedClosureCompl (F.reindex j))
        = (S'.comapAmbientCenter j).comap
            ((F.strictTransformComparison j hj.le ⁻¹ᵁ S.detachedClosureCompl (F.reindex j)).ι) := by
    rw [htrace, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hpb.w]
  rw [S'.centerOffDetached_eq j, S.centerOffDetached_eq (F.reindex j),
    ← _root_.FunctorialResolution.EmbeddedResolution.ChartFlatBaseChange.map_eq_ker_subschemeι_comp_consolidated323 (S'.detachedClosureCompl j).ι, ← _root_.FunctorialResolution.EmbeddedResolution.ChartFlatBaseChange.map_eq_ker_subschemeι_comp_consolidated323 (S.detachedClosureCompl (F.reindex j)).ι,
    F.detachedClosureCompl_eq_preimage j hj, key, hcomap]


end

end ChartFlatBaseChange


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.InactiveTotalSpaceFlatBaseChange
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]

namespace EmbeddedBlowupSequence

section
variable (S : EmbeddedBlowupSequence k Y pY)

theorem detachedToCoprod_detachedCoprodInl_detachedCoprodMapOfLE (s a b : ℕ)
    (hsa : s < a) (hab : a + 1 ≤ b) :
    S.detachedToCoprod s a hsa ≫ S.detachedCoprodInl a ≫ S.detachedCoprodMapOfLE hab =
      S.detachedToCoprod s b (lt_of_lt_of_le hsa (le_trans (Nat.le_succ a) hab)) := by
  rw [← Category.assoc, ← S.detachedToCoprod_succ_of_lt s a hsa, S.detachedToCoprod_detachedCoprodMapOfLE]

theorem detachedCoprodInr_detachedCoprodMapOfLE (a b : ℕ) (hab : a + 1 ≤ b) :
    S.detachedCoprodInr a ≫ S.detachedCoprodMapOfLE hab =
      S.detachedToCoprod a b (lt_of_lt_of_le (Nat.lt_succ_self a) hab) := by
  rw [← S.detachedToCoprod_self a, S.detachedToCoprod_detachedCoprodMapOfLE]


end

def inactiveTotalToBase (S : EmbeddedBlowupSequence k Y pY) (h : S.TransitionsAreBlowups) (i : ℕ) :
    S.detachedCoprod i ⟶ Y :=
  (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫ (S.inducedBlowups h).projectionToBase i

section
variable (S : EmbeddedBlowupSequence k Y pY) (h : S.TransitionsAreBlowups)

theorem detachedToCoprod_inactiveTotalToBase (s i : ℕ)
    (hs : s < i) :
    S.detachedToCoprod s i hs ≫ S.inactiveTotalToBase h i = S.detachedι s ≫ S.strictTransformToBase s :=
  detachedToCoprod_inr_inducedBlowups_projectionToBase S h s i hs

theorem coprodDesc_strictTransformToBase_inactiveTotalToBase (i : ℕ) :
    coprod.desc (S.strictTransformToBase i) (S.inactiveTotalToBase h i) = (S.inducedBlowups h).projectionToBase i := by
  apply coprod.hom_ext
  · rw [coprod.inl_desc]
    exact (inl_inducedBlowups_projectionToBase S h i).symm
  · rw [coprod.inr_desc]
    rfl


end

end EmbeddedBlowupSequence

namespace ChartFlatBaseChange

variable {k' : Type u} [Field k'] [CharZero k'] {Y' : Scheme.{u}} [IsAffine Y']
  {pY' : Y' ⟶ Spec (CommRingCat.of k')} [LocallyOfFiniteType pY']
  {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

theorem reindex_lt_reindex (F : ChartFlatBaseChange S S') {s j : ℕ} (hsj : s < j)
    (hj : j ≤ S'.length) : F.reindex s < F.reindex j :=
  F.reindex_lt_reindex_of_lt hsj hj

section
variable (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j + 1 ≤ S'.length)
include hj

private theorem reindex_le_reindex_succ_consolidated322 :
    F.reindex j ≤ F.reindex (j + 1) :=
  (F.reindex_lt_succ j (by omega)).le

private theorem reindex_lt_reindex_succ_consolidated322 :
    F.reindex j < F.reindex (j + 1) :=
  F.reindex_lt_succ j (by omega)


end

section
variable (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j ≤ S'.length)

theorem strictTransformComparison_comp_strictTransformToBase :
    F.strictTransformComparison j hj ≫ S.strictTransformToBase (F.reindex j) = S'.strictTransformToBase j ≫ F.baseMap := by
  have : CategoryTheory.Mono S.emb := inferInstance
  have key : (F.strictTransformComparison j hj ≫ S.strictTransformToBase (F.reindex j)) ≫ S.emb
      = (S'.strictTransformToBase j ≫ F.baseMap) ≫ S.emb := by
    calc (F.strictTransformComparison j hj ≫ S.strictTransformToBase (F.reindex j)) ≫ S.emb
        = F.strictTransformComparison j hj ≫ (S.strictTransformToBase (F.reindex j) ≫ S.emb) := Category.assoc _ _ _
      _ = F.strictTransformComparison j hj ≫
            (S.strictTransformι (F.reindex j) ≫ S.ambientSeq.projectionToBase (F.reindex j)) := by
            rw [S.strictTransformToBase_emb (F.reindex j)]
      _ = (F.strictTransformComparison j hj ≫ S.strictTransformι (F.reindex j)) ≫
            S.ambientSeq.projectionToBase (F.reindex j) := (Category.assoc _ _ _).symm
      _ = (S'.strictTransformι j ≫ F.levelMap j hj) ≫ S.ambientSeq.projectionToBase (F.reindex j) := by
            rw [F.strictTransformComparison_comp_strictTransformι j hj]
      _ = S'.strictTransformι j ≫ (F.levelMap j hj ≫ S.ambientSeq.projectionToBase (F.reindex j)) :=
            Category.assoc _ _ _
      _ = S'.strictTransformι j ≫ (S'.ambientSeq.projectionToBase j ≫ F.ambientMap) := by
            rw [(F.isPullback_level j hj).w]
      _ = (S'.strictTransformι j ≫ S'.ambientSeq.projectionToBase j) ≫ F.ambientMap :=
            (Category.assoc _ _ _).symm
      _ = (S'.strictTransformToBase j ≫ S'.emb) ≫ F.ambientMap := by rw [S'.strictTransformToBase_emb j]
      _ = S'.strictTransformToBase j ≫ (S'.emb ≫ F.ambientMap) := Category.assoc _ _ _
      _ = S'.strictTransformToBase j ≫ (F.baseMap ≫ S.emb) := by rw [F.isPullback_emb.w]
      _ = (S'.strictTransformToBase j ≫ F.baseMap) ≫ S.emb := (Category.assoc _ _ _).symm
  exact (cancel_mono S.emb).mp key

theorem isPullback_strictTransformComparison_strictTransformToBase :
    IsPullback (F.strictTransformComparison j hj) (S'.strictTransformToBase j) (S.strictTransformToBase (F.reindex j))
      F.baseMap := by
  have h1 := (F.isPullback_strictTransformComparison_strictTransformι j hj).paste_vert (F.isPullback_level j hj)
  have h2 : IsPullback (F.strictTransformComparison j hj) (S'.strictTransformToBase j ≫ S'.emb)
      (S.strictTransformToBase (F.reindex j) ≫ S.emb) F.ambientMap := by
    rw [S'.strictTransformToBase_emb j, S.strictTransformToBase_emb (F.reindex j)]
    exact h1
  exact h2.of_bot (F.strictTransformComparison_comp_strictTransformToBase j hj) F.isPullback_emb


end

theorem isEmpty_of_comm_detachedScheme_of_not_mem_range (F : ChartFlatBaseChange S S') (s : ℕ) (hs : s < S.length)
    (hskip : ∀ j, j < S'.length → F.reindex j ≠ s) (Q : Scheme.{u}) (q : Q ⟶ S.detachedScheme s)
    (p : Q ⟶ Y') (hcomm : q ≫ S.detachedι s ≫ S.strictTransformToBase s = p ≫ F.baseMap) :
    IsEmpty ↥Q := by
  refine F.isEmpty_of_forall_reindex_ne s hs hskip Q q (p ≫ S'.emb) ?_
  calc q ≫ S.detachedι s ≫ S.strictTransformι s ≫ S.ambientSeq.projectionToBase s
      = q ≫ S.detachedι s ≫ S.strictTransformToBase s ≫ S.emb := by rw [S.strictTransformToBase_emb s]
    _ = (q ≫ S.detachedι s ≫ S.strictTransformToBase s) ≫ S.emb := by simp only [Category.assoc]
    _ = (p ≫ F.baseMap) ≫ S.emb := by rw [hcomm]
    _ = p ≫ (F.baseMap ≫ S.emb) := Category.assoc _ _ _
    _ = p ≫ (S'.emb ≫ F.ambientMap) := by rw [F.isPullback_emb.w]
    _ = (p ≫ S'.emb) ≫ F.ambientMap := (Category.assoc _ _ _).symm

private theorem isEmpty_of_hom_to_initial_consolidated322 {P : Scheme.{u}}
    (f : P ⟶ ⊥_ Scheme.{u}) : IsEmpty ↥P :=
  Function.isEmpty f.base

private theorem inactiveTotalToBase_succ_eq_desc_consolidated322 (T : EmbeddedBlowupSequence k Y pY)
    (hT : T.TransitionsAreBlowups) (i : ℕ) :
    T.inactiveTotalToBase hT (i + 1) =
      coprod.desc (T.inactiveTotalToBase hT i) (T.detachedι i ≫ T.strictTransformToBase i) := by
  have hl : T.detachedCoprodInl i ≫ T.inactiveTotalToBase hT (i + 1) = T.inactiveTotalToBase hT i := by
    refine T.detachedCoprod_hom_ext i ?_
    intro s hs
    calc T.detachedToCoprod s i hs ≫ T.detachedCoprodInl i ≫ T.inactiveTotalToBase hT (i + 1)
        = (T.detachedToCoprod s i hs ≫ T.detachedCoprodInl i) ≫ T.inactiveTotalToBase hT (i + 1) :=
          (Category.assoc _ _ _).symm
      _ = T.detachedToCoprod s (i + 1) (Nat.lt_succ_of_lt hs) ≫ T.inactiveTotalToBase hT (i + 1) := by
          rw [T.detachedToCoprod_succ_of_lt s i hs]
      _ = T.detachedι s ≫ T.strictTransformToBase s :=
          T.detachedToCoprod_inactiveTotalToBase hT s (i + 1) (Nat.lt_succ_of_lt hs)
      _ = T.detachedToCoprod s i hs ≫ T.inactiveTotalToBase hT i :=
          (T.detachedToCoprod_inactiveTotalToBase hT s i hs).symm
  have hr : T.detachedCoprodInr i ≫ T.inactiveTotalToBase hT (i + 1) = T.detachedι i ≫ T.strictTransformToBase i := by
    calc T.detachedCoprodInr i ≫ T.inactiveTotalToBase hT (i + 1)
        = T.detachedToCoprod i (i + 1) (Nat.lt_succ_self i) ≫ T.inactiveTotalToBase hT (i + 1) := by
          rw [T.detachedToCoprod_self i]
      _ = T.detachedι i ≫ T.strictTransformToBase i :=
          T.detachedToCoprod_inactiveTotalToBase hT i (i + 1) (Nat.lt_succ_self i)
  refine T.detachedCoprod_succ_hom_ext i ?_ ?_
  · exact hl.trans (coprod.inl_desc _ _).symm
  · exact hr.trans (coprod.inr_desc _ _).symm

section
variable (F : ChartFlatBaseChange S S') (h : S.TransitionsAreBlowups)

private theorem forall_isEmpty_of_comm_inactiveTotalToBase_consolidated322 :
    ∀ (i : ℕ), (∀ s, s < i → s < S.length) →
      (∀ s, s < i → ∀ j, j < S'.length → F.reindex j ≠ s) →
      ∀ (P : Scheme.{u}) (q : P ⟶ S.detachedCoprod i) (p : P ⟶ Y'),
        q ≫ S.inactiveTotalToBase h i = p ≫ F.baseMap → IsEmpty ↥P := by
  intro i
  induction i with
  | zero =>
      intro _ _ P q _ _
      exact isEmpty_of_hom_to_initial_consolidated322 q
  | succ n ih =>
      intro hlt hskip P q p hcomm
      have h1 : IsPullback (initial.to (S.detachedCoprod n)) (initial.to Y')
          (S.inactiveTotalToBase h n) F.baseMap :=
        isPullback_initial_of_isEmpty (S.inactiveTotalToBase h n) F.baseMap
          (fun Q a b hab =>
            ih (fun s hs => hlt s (Nat.lt_succ_of_lt hs))
              (fun s hs => hskip s (Nat.lt_succ_of_lt hs)) Q a b hab)
      have h2 : IsPullback (initial.to (S.detachedScheme n)) (initial.to Y')
          (S.detachedι n ≫ S.strictTransformToBase n) F.baseMap :=
        isPullback_initial_of_isEmpty (S.detachedι n ≫ S.strictTransformToBase n) F.baseMap
          (fun Q c d hcd =>
            F.isEmpty_of_comm_detachedScheme_of_not_mem_range n (hlt n (Nat.lt_succ_self n))
              (hskip n (Nat.lt_succ_self n)) Q c d hcd)
      have h3 := isPullback_coprodMap_coprodDesc (initial.to (S.detachedCoprod n))
        (initial.to (S.detachedScheme n)) (initial.to Y') (initial.to Y')
        (S.inactiveTotalToBase h n) (S.detachedι n ≫ S.strictTransformToBase n) F.baseMap h1 h2
      have hcomm' : q ≫ coprod.desc (S.inactiveTotalToBase h n) (S.detachedι n ≫ S.strictTransformToBase n)
          = p ≫ F.baseMap :=
        (congrArg (fun t : S.detachedCoprod (n + 1) ⟶ Y => q ≫ t)
          (inactiveTotalToBase_succ_eq_desc_consolidated322 S h n)).symm.trans hcomm
      exact isEmpty_of_hom_to_initial_consolidated322
        (h3.lift q p hcomm' ≫ coprod.desc (𝟙 (⊥_ Scheme.{u})) (𝟙 (⊥_ Scheme.{u})))

theorem isEmpty_of_comm_inactiveTotalToBase_of_not_mem_range (i : ℕ) (hlt : ∀ s, s < i → s < S.length)
    (hskip : ∀ s, s < i → ∀ j, j < S'.length → F.reindex j ≠ s) (P : Scheme.{u})
    (q : P ⟶ S.detachedCoprod i) (p : P ⟶ Y')
    (hcomm : q ≫ S.inactiveTotalToBase h i = p ≫ F.baseMap) : IsEmpty ↥P :=
  forall_isEmpty_of_comm_inactiveTotalToBase_consolidated322 F h i hlt hskip P q p hcomm

theorem isPullback_detachedCoprodMapOfLE_inactiveTotalToBase {a b : ℕ} (hab : a ≤ b) (hlt : ∀ s, a ≤ s → s < b → s < S.length)
    (hskip : ∀ s, a ≤ s → s < b → ∀ j, j < S'.length → F.reindex j ≠ s) {P : Scheme.{u}}
    (q : P ⟶ S.detachedCoprod a) (p : P ⟶ Y')
    (hsq : IsPullback q p (S.inactiveTotalToBase h a) F.baseMap) :
    IsPullback (q ≫ S.detachedCoprodMapOfLE hab) p (S.inactiveTotalToBase h b) F.baseMap := by
  have main : ∀ (c : ℕ) (hac : a ≤ c),
      (∀ s, a ≤ s → s < c → s < S.length) →
      (∀ s, a ≤ s → s < c → ∀ j, j < S'.length → F.reindex j ≠ s) →
      IsPullback (q ≫ S.detachedCoprodMapOfLE hac) p (S.inactiveTotalToBase h c) F.baseMap := by
    intro c hac
    induction c, hac using Nat.le_induction with
    | base =>
        intro _ _
        have hself : S.detachedCoprodMapOfLE (Nat.le_refl a) = 𝟙 (S.detachedCoprod a) := S.detachedCoprodMapOfLE_self a
        have hpbRefl : IsPullback (q ≫ S.detachedCoprodMapOfLE (Nat.le_refl a)) p
            (S.inactiveTotalToBase h a) F.baseMap := by
          rw [hself, Category.comp_id]
          exact hsq
        exact hpbRefl
    | succ c hac ih =>
        intro hlt1 hskip1
        have ih' := ih (fun s h1 h2 => hlt1 s h1 (Nat.lt_succ_of_lt h2))
          (fun s h1 h2 => hskip1 s h1 (Nat.lt_succ_of_lt h2))
        have hc : c < S.length := hlt1 c hac (Nat.lt_succ_self c)
        have hsk : ∀ j, j < S'.length → F.reindex j ≠ c := hskip1 c hac (Nat.lt_succ_self c)
        have hF : ∀ (Q : Scheme.{u}) (cc : Q ⟶ S.detachedScheme c) (d : Q ⟶ Y'),
            cc ≫ S.detachedι c ≫ S.strictTransformToBase c = d ≫ F.baseMap → IsEmpty Q :=
          fun Q cc d hcomm => F.isEmpty_of_comm_detachedScheme_of_not_mem_range c hc hsk Q cc d hcomm
        have hinl : S.detachedCoprodInl c ≫ S.inactiveTotalToBase h (c + 1) = S.inactiveTotalToBase h c := by
          show S.detachedCoprodInl c ≫ (coprod.inr : S.detachedCoprod (c + 1) ⟶ S.totalSpace (c + 1)) ≫
              (S.inducedBlowups h).projectionToBase (c + 1) = S.inactiveTotalToBase h c
          rw [SequenceOfBlowups.projectionToBase_succ, inducedBlowups_blowupMorphism]
          exact S.detachedCoprodInl_inr_totalTransition_assoc c ((S.inducedBlowups h).projectionToBase c)
        have hinr : S.detachedCoprodInr c ≫ S.inactiveTotalToBase h (c + 1) =
            S.detachedι c ≫ S.strictTransformToBase c := by
          have hkey := S.detachedToCoprod_inactiveTotalToBase h c (c + 1) (Nat.lt_succ_self c)
          rw [S.detachedToCoprod_self c] at hkey
          exact hkey
        have hdesc : (coprod.desc (S.inactiveTotalToBase h c) (S.detachedι c ≫ S.strictTransformToBase c) :
            S.detachedCoprod c ⨿ S.detachedScheme c ⟶ Y) = S.inactiveTotalToBase h (c + 1) := by
          apply coprod.hom_ext
          · rw [coprod.inl_desc]
            exact hinl.symm
          · rw [coprod.inr_desc]
            exact hinr.symm
        have key1 : IsPullback ((q ≫ S.detachedCoprodMapOfLE hac) ≫ S.detachedCoprodInl c) p
            (S.inactiveTotalToBase h (c + 1)) F.baseMap := by
          have key0 := isPullback_comp_inl_coprodDesc (q ≫ S.detachedCoprodMapOfLE hac) p
            (S.inactiveTotalToBase h c) F.baseMap (S.detachedι c ≫ S.strictTransformToBase c) ih' hF
          rw [hdesc] at key0
          exact key0
        have hup : S.detachedCoprodMapOfLE (Nat.le_succ_of_le hac) = S.detachedCoprodMapOfLE hac ≫ S.detachedCoprodInl c :=
          S.detachedCoprodMapOfLE_succ hac
        have hpbSucc : IsPullback (q ≫ S.detachedCoprodMapOfLE (Nat.le_succ_of_le hac)) p
            (S.inactiveTotalToBase h (c + 1)) F.baseMap := by
          rw [hup, ← Category.assoc]
          exact key1
        exact hpbSucc
  exact main b hab hlt hskip


end

theorem isPullback_inactiveSchemeMap_baseMap (F : ChartFlatBaseChange S S')
    [IsReduced Y] [IsReduced Y'] (j : ℕ) (hj : j < S'.length) :
    IsPullback (F.detachedSchemeComparison j hj) (S'.detachedι j ≫ S'.strictTransformToBase j)
      (S.detachedι (F.reindex j) ≫ S.strictTransformToBase (F.reindex j)) F.baseMap :=
  (F.isPullback_detachedSchemeComparison j hj).paste_vert (F.isPullback_strictTransformComparison_strictTransformToBase j hj.le)

def inactiveTotalMap (F : ChartFlatBaseChange S S') [IsReduced Y]
    [IsReduced Y'] :
    ∀ (j : ℕ), j ≤ S'.length → (S'.detachedCoprod j ⟶ S.detachedCoprod (F.reindex j))
  | 0, _ => eqToHom S'.detachedCoprod_zero ≫ initial.to (S.detachedCoprod (F.reindex 0))
  | (j + 1), hj =>
      eqToHom (S'.detachedCoprod_succ j) ≫
        coprod.desc
          (inactiveTotalMap F j (Nat.le_of_succ_le hj) ≫ S.detachedCoprodMapOfLE (F.reindex_le_reindex_succ_consolidated322 j hj))
          (F.detachedSchemeComparison j (by omega) ≫
            S.detachedToCoprod (F.reindex j) (F.reindex (j + 1)) (F.reindex_lt_reindex_succ_consolidated322 j hj))

section
variable (F : ChartFlatBaseChange S S') [IsReduced Y] [IsReduced Y'] (n : ℕ) (hj : n + 1 ≤ S'.length)

private theorem inactiveTotalMap_succ_eq_desc_consolidated322 :
    F.inactiveTotalMap (n + 1) hj =
      coprod.desc
        (F.inactiveTotalMap n (Nat.le_of_succ_le hj) ≫ S.detachedCoprodMapOfLE (F.reindex_le_reindex_succ_consolidated322 n hj))
        (F.detachedSchemeComparison n (lt_of_lt_of_le (Nat.lt_succ_self n) hj) ≫
          S.detachedToCoprod (F.reindex n) (F.reindex (n + 1)) (F.reindex_lt_reindex_succ_consolidated322 n hj)) := by
  have h0 : F.inactiveTotalMap (n + 1) hj =
      eqToHom (S'.detachedCoprod_succ n) ≫
        coprod.desc
          (F.inactiveTotalMap n (Nat.le_of_succ_le hj) ≫ S.detachedCoprodMapOfLE (F.reindex_le_reindex_succ_consolidated322 n hj))
          (F.detachedSchemeComparison n (lt_of_lt_of_le (Nat.lt_succ_self n) hj) ≫
            S.detachedToCoprod (F.reindex n) (F.reindex (n + 1)) (F.reindex_lt_reindex_succ_consolidated322 n hj)) := rfl
  have hid : eqToHom (S'.detachedCoprod_succ n) = 𝟙 (S'.detachedCoprod (n + 1)) := eqToHom_refl _ _
  rw [h0, hid]
  exact Category.id_comp _

private theorem detachedCoprodInl_inactiveTotalMap_consolidated322 :
    S'.detachedCoprodInl n ≫ F.inactiveTotalMap (n + 1) hj =
      F.inactiveTotalMap n (Nat.le_of_succ_le hj) ≫ S.detachedCoprodMapOfLE (F.reindex_le_reindex_succ_consolidated322 n hj) := by
  rw [inactiveTotalMap_succ_eq_desc_consolidated322 F n hj]
  exact coprod.inl_desc _ _

private theorem detachedCoprodInr_inactiveTotalMap_consolidated322 :
    S'.detachedCoprodInr n ≫ F.inactiveTotalMap (n + 1) hj =
      F.detachedSchemeComparison n (lt_of_lt_of_le (Nat.lt_succ_self n) hj) ≫
        S.detachedToCoprod (F.reindex n) (F.reindex (n + 1)) (F.reindex_lt_reindex_succ_consolidated322 n hj) := by
  rw [inactiveTotalMap_succ_eq_desc_consolidated322 F n hj]
  exact coprod.inr_desc _ _


end

section
variable (F : ChartFlatBaseChange S S') [IsReduced Y] [IsReduced Y']

private theorem forall_detachedToCoprod_inactiveTotalMap_consolidated322 :
    ∀ (j : ℕ) (hj : j ≤ S'.length) (s : ℕ) (hs : s < j),
      S'.detachedToCoprod s j hs ≫ F.inactiveTotalMap j hj =
        F.detachedSchemeComparison s (lt_of_lt_of_le hs hj) ≫
          S.detachedToCoprod (F.reindex s) (F.reindex j) (F.reindex_lt_reindex hs hj) := by
  intro j
  induction j with
  | zero =>
      intro hj s hs
      exact absurd hs (Nat.not_lt_zero s)
  | succ n ih =>
      intro hj s hs
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hs) with hlt | heq
      · rw [S'.detachedToCoprod_succ_of_lt s n hlt, Category.assoc,
          detachedCoprodInl_inactiveTotalMap_consolidated322 F n hj, ← Category.assoc,
          ih (Nat.le_of_succ_le hj) s hlt, Category.assoc, S.detachedToCoprod_detachedCoprodMapOfLE]
      · subst heq
        rw [S'.detachedToCoprod_self s, detachedCoprodInr_inactiveTotalMap_consolidated322 F s hj]

theorem detachedToCoprod_inactiveTotalMap (j : ℕ) (hj : j ≤ S'.length)
    (s : ℕ) (hs : s < j) :
    S'.detachedToCoprod s j hs ≫ F.inactiveTotalMap j hj =
      F.detachedSchemeComparison s (lt_of_lt_of_le hs hj) ≫
        S.detachedToCoprod (F.reindex s) (F.reindex j) (F.reindex_lt_reindex hs hj) :=
  forall_detachedToCoprod_inactiveTotalMap_consolidated322 F j hj s hs


end

section
variable (T : EmbeddedBlowupSequence k Y pY) {c b : ℕ} (hcb : c + 1 ≤ b)

private theorem inl_detachedCoprodMapOfLE_consolidated322 :
    (coprod.inl : T.detachedCoprod c ⟶ T.detachedCoprod c ⨿ T.detachedScheme c) ≫ T.detachedCoprodMapOfLE hcb =
      T.detachedCoprodMapOfLE (Nat.le_of_succ_le hcb) := by
  refine T.detachedCoprod_hom_ext c (fun s hs => ?_)
  have h1 := T.detachedToCoprod_detachedCoprodInl_detachedCoprodMapOfLE s c b hs hcb
  have h2 := T.detachedToCoprod_detachedCoprodMapOfLE hs (Nat.le_of_succ_le hcb)
  exact h1.trans h2.symm

private theorem inr_detachedCoprodMapOfLE_consolidated322 :
    (coprod.inr : T.detachedScheme c ⟶ T.detachedCoprod c ⨿ T.detachedScheme c) ≫ T.detachedCoprodMapOfLE hcb =
      T.detachedToCoprod c b hcb :=
  T.detachedCoprodInr_detachedCoprodMapOfLE c b hcb


end

section
variable {P X Z W : Scheme.{u}}

private theorem isPullback_of_fst_eq_consolidated322 {f f' : P ⟶ X} {g : P ⟶ Z}
    {q : X ⟶ W} {u : Z ⟶ W} (hf : f = f') (hp : IsPullback f' g q u) : IsPullback f g q u := by
  subst hf
  exact hp

private theorem isPullback_of_fst_eq_of_snd_eq_consolidated322 {f f' : P ⟶ X}
    {g g' : P ⟶ Z} {q : X ⟶ W} {u : Z ⟶ W} (hf : f = f') (hg : g = g')
    (hp : IsPullback f' g' q u) : IsPullback f g q u := by
  subst hf
  subst hg
  exact hp

private theorem isPullback_of_snd_eq_of_map_eq_consolidated322 {f : P ⟶ X} {g g' : P ⟶ Z}
    {q q' : X ⟶ W} {u : Z ⟶ W} (hg : g = g') (hq : q = q')
    (hp : IsPullback f g' q' u) : IsPullback f g q u := by
  subst hg
  subst hq
  exact hp


end

theorem isPullback_inactiveTotalMap (F : ChartFlatBaseChange S S')
    [IsReduced Y] [IsReduced Y']
    (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups) (j : ℕ) (hj : j ≤ S'.length) :
    IsPullback (F.inactiveTotalMap j hj) (S'.inactiveTotalToBase h' j)
      (S.inactiveTotalToBase h (F.reindex j)) F.baseMap := by
  have main : ∀ (m : ℕ) (hm : m ≤ S'.length),
      IsPullback (F.inactiveTotalMap m hm) (S'.inactiveTotalToBase h' m)
        (S.inactiveTotalToBase h (F.reindex m)) F.baseMap := by
    intro m
    induction m with
    | zero =>
        intro hm
        have hI : IsInitial (S'.detachedCoprod 0) := initialIsInitial
        have hlen : F.reindex 0 ≤ S.length := F.reindex_le_length (Nat.zero_le S'.length)
        have hempty : ∀ (P : Scheme.{u}) (a : P ⟶ S.detachedCoprod (F.reindex 0)) (b : P ⟶ Y'),
            a ≫ S.inactiveTotalToBase h (F.reindex 0) = b ≫ F.baseMap → IsEmpty ↥P := by
          intro P a b hcomm
          exact F.isEmpty_of_comm_inactiveTotalToBase_of_not_mem_range h (F.reindex 0)
            (fun s hs => lt_of_lt_of_le hs hlen)
            (fun s hs j' hj' => F.reindex_ne_of_lt_reindex_zero s hs j' hj') P a b hcomm
        have hpb :=
          isPullback_initial_of_isEmpty (S.inactiveTotalToBase h (F.reindex 0)) F.baseMap hempty
        have e1 : F.inactiveTotalMap 0 hm = initial.to (S.detachedCoprod (F.reindex 0)) :=
          hI.hom_ext _ _
        have e2 : S'.inactiveTotalToBase h' 0 = initial.to Y' := hI.hom_ext _ _
        exact isPullback_of_fst_eq_of_snd_eq_consolidated322 e1 e2 hpb
    | succ n ih =>
        intro hm
        have hn : n ≤ S'.length := Nat.le_of_succ_le hm
        have hnlt : n < S'.length := hm
        have hab : F.reindex n + 1 ≤ F.reindex (n + 1) := F.reindex_lt_succ n hnlt
        have hlen : F.reindex (n + 1) ≤ S.length := F.reindex_le_length hm
        have hcop := isPullback_coprodMap_coprodDesc (F.inactiveTotalMap n hn)
          (F.detachedSchemeComparison n hnlt) (S'.inactiveTotalToBase h' n) (S'.detachedι n ≫ S'.strictTransformToBase n)
          (S.inactiveTotalToBase h (F.reindex n))
          (S.detachedι (F.reindex n) ≫ S.strictTransformToBase (F.reindex n)) F.baseMap (ih hn)
          (F.isPullback_inactiveSchemeMap_baseMap n hnlt)
        have hcop2 : IsPullback
            (coprod.map (F.inactiveTotalMap n hn) (F.detachedSchemeComparison n hnlt))
            (S'.inactiveTotalToBase h' (n + 1)) (S.inactiveTotalToBase h (F.reindex n + 1)) F.baseMap :=
          isPullback_of_snd_eq_of_map_eq_consolidated322 (inactiveTotalToBase_succ_eq_desc_consolidated322 S' h' n)
            (inactiveTotalToBase_succ_eq_desc_consolidated322 S h (F.reindex n)) hcop
        have hstep := F.isPullback_detachedCoprodMapOfLE_inactiveTotalToBase h hab
          (fun s _ hs2 => lt_of_lt_of_le hs2 hlen)
          (fun s hs1 hs2 j' hj' => F.reindex_ne_of_reindex_lt_of_lt_reindex_succ n hnlt s (by omega) hs2 j' hj')
          (coprod.map (F.inactiveTotalMap n hn) (F.detachedSchemeComparison n hnlt))
          (S'.inactiveTotalToBase h' (n + 1)) hcop2
        have hE : F.inactiveTotalMap (n + 1) hm =
            coprod.map (F.inactiveTotalMap n hn) (F.detachedSchemeComparison n hnlt) ≫
              S.detachedCoprodMapOfLE hab := by
          refine S'.detachedCoprod_succ_hom_ext n ?_ ?_
          · exact (detachedCoprodInl_inactiveTotalMap_consolidated322 F n hm).trans
              ((coprod.inl_map_assoc (F.inactiveTotalMap n hn)
                  (F.detachedSchemeComparison n hnlt) (S.detachedCoprodMapOfLE hab)).trans
                (congrArg
                  (fun t : (S.detachedCoprod (F.reindex n) ⟶ S.detachedCoprod (F.reindex (n + 1))) =>
                    F.inactiveTotalMap n hn ≫ t)
                  (inl_detachedCoprodMapOfLE_consolidated322 S hab))).symm
          · exact (detachedCoprodInr_inactiveTotalMap_consolidated322 F n hm).trans
              ((coprod.inr_map_assoc (F.inactiveTotalMap n hn)
                  (F.detachedSchemeComparison n hnlt) (S.detachedCoprodMapOfLE hab)).trans
                (congrArg
                  (fun t : (S.detachedScheme (F.reindex n) ⟶ S.detachedCoprod (F.reindex (n + 1))) =>
                    F.detachedSchemeComparison n hnlt ≫ t)
                  (inr_detachedCoprodMapOfLE_consolidated322 S hab))).symm
        exact isPullback_of_fst_eq_consolidated322 hE hstep
  exact main j hj

def totalSpaceMap (F : ChartFlatBaseChange S S') [IsReduced Y]
    [IsReduced Y'] (j : ℕ) (hj : j ≤ S'.length) :
    S'.totalSpace j ⟶ S.totalSpace (F.reindex j) :=
  coprod.map (F.strictTransformComparison j hj) (F.inactiveTotalMap j hj)

section
variable (F : ChartFlatBaseChange S S') [IsReduced Y] [IsReduced Y'] (j : ℕ) (hj : j ≤ S'.length)

theorem totalSpaceMap_eq_coprodMap :
    F.totalSpaceMap j hj = coprod.map (F.strictTransformComparison j hj) (F.inactiveTotalMap j hj) := rfl

theorem inl_totalSpaceMap :
    (coprod.inl : S'.strictTransform j ⟶ S'.totalSpace j) ≫ F.totalSpaceMap j hj =
      F.strictTransformComparison j hj ≫
        (coprod.inl : S.strictTransform (F.reindex j) ⟶ S.totalSpace (F.reindex j)) := by
  simp [ChartFlatBaseChange.totalSpaceMap]

theorem detachedToCoprod_inr_totalSpaceMap (s : ℕ) (hs : s < j) :
    S'.detachedToCoprod s j hs ≫ (coprod.inr : S'.detachedCoprod j ⟶ S'.totalSpace j) ≫
        F.totalSpaceMap j hj =
      F.detachedSchemeComparison s (lt_of_lt_of_le hs hj) ≫
        S.detachedToCoprod (F.reindex s) (F.reindex j) (F.reindex_lt_reindex hs hj) ≫
          (coprod.inr : S.detachedCoprod (F.reindex j) ⟶ S.totalSpace (F.reindex j)) := by
  rw [F.totalSpaceMap_eq_coprodMap j hj, coprod.inr_map, ← Category.assoc,
    F.detachedToCoprod_inactiveTotalMap j hj s hs, Category.assoc]


end

theorem isPullback_totalSpaceMap (F : ChartFlatBaseChange S S') [IsReduced Y]
    [IsReduced Y'] (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups)
    (j : ℕ) (hj : j ≤ S'.length) :
    IsPullback (F.totalSpaceMap j hj) ((S'.inducedBlowups h').projectionToBase j)
      ((S.inducedBlowups h).projectionToBase (F.reindex j)) F.baseMap := by
  have key := isPullback_coprodMap_coprodDesc (F.strictTransformComparison j hj)
    (F.inactiveTotalMap j hj) (S'.strictTransformToBase j) (S'.inactiveTotalToBase h' j)
    (S.strictTransformToBase (F.reindex j)) (S.inactiveTotalToBase h (F.reindex j)) F.baseMap
    (F.isPullback_strictTransformComparison_strictTransformToBase j hj) (F.isPullback_inactiveTotalMap h h' j hj)
  rw [S'.coprodDesc_strictTransformToBase_inactiveTotalToBase h' j, S.coprodDesc_strictTransformToBase_inactiveTotalToBase h (F.reindex j)] at key
  rw [F.totalSpaceMap_eq_coprodMap j hj]
  exact key

end ChartFlatBaseChange


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.DetachedLocusPushforward
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

section

namespace ChartPushforward

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]
  {S S' : EmbeddedBlowupSequence k Y pY}

private theorem mem_irreducibleComponents_iff_image_consolidated350 {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (f : α → β) (g : β → α) (hf : Continuous f) (hg : Continuous g)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) (C : Set α) :
    C ∈ irreducibleComponents α ↔ f '' C ∈ irreducibleComponents β := by
  have hinj : Function.Injective f := by
    intro a b hab
    have h := congrArg g hab
    rwa [hgf, hgf] at h
  have hirrf : ∀ s : Set α, IsIrreducible s → IsIrreducible (f '' s) := fun s hs =>
    hs.image f hf.continuousOn
  have hirrg : ∀ t : Set β, IsIrreducible t → IsIrreducible (g '' t) := fun t ht =>
    ht.image g hg.continuousOn
  have himg : g '' (f '' C) = C := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      rwa [hgf]
    · intro x hx
      exact ⟨f x, ⟨x, hx, rfl⟩, hgf x⟩
  constructor
  · intro hC0
    have hC : IsIrreducible C ∧ ∀ ⦃b : Set α⦄, IsIrreducible b → C ≤ b → b ≤ C := hC0
    show IsIrreducible (f '' C) ∧ ∀ ⦃b : Set β⦄, IsIrreducible b → f '' C ≤ b → b ≤ f '' C
    refine ⟨hirrf C hC.1, ?_⟩
    intro t ht hsub
    have hsub' : f '' C ⊆ t := hsub
    have hCt : C ⊆ g '' t := fun x hx => ⟨f x, hsub' ⟨x, hx, rfl⟩, hgf x⟩
    have hle : g '' t ⊆ C := hC.2 (hirrg t ht) hCt
    intro y hy
    exact ⟨g y, hle ⟨y, hy, rfl⟩, hfg y⟩
  · intro hC0
    have hC : IsIrreducible (f '' C) ∧
        ∀ ⦃b : Set β⦄, IsIrreducible b → f '' C ≤ b → b ≤ f '' C := hC0
    show IsIrreducible C ∧ ∀ ⦃b : Set α⦄, IsIrreducible b → C ≤ b → b ≤ C
    refine ⟨?_, ?_⟩
    · have h1 := hirrg _ hC.1
      rwa [himg] at h1
    · intro t ht hsub
      have hsub' : C ⊆ t := hsub
      have himt : f '' C ⊆ f '' t := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x, hsub' hx, rfl⟩
      have hle : f '' t ⊆ f '' C := hC.2 (hirrf t ht) himt
      intro x hx
      obtain ⟨x', hx', hxx⟩ := hle ⟨x, hx, rfl⟩
      have hx'x : x' = x := hinj hxx
      rwa [← hx'x]

theorem mem_detachedComponents_iff (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length)
    (C : Set ↥(S.strictTransform i)) :
    C ∈ S.detachedComponents i ↔
      ⇑((P.strictTransformIso i hi.le).hom) '' C ∈ S'.detachedComponents i := by
  have hgf : ∀ x : ↥(S.strictTransform i),
      ((P.strictTransformIso i hi.le).inv).base (((P.strictTransformIso i hi.le).hom).base x) = x := fun x =>
    Scheme.hom_inv_apply (P.strictTransformIso i hi.le) x
  have hfg : ∀ y : ↥(S'.strictTransform i),
      ((P.strictTransformIso i hi.le).hom).base (((P.strictTransformIso i hi.le).inv).base y) = y := fun y =>
    Scheme.inv_hom_apply (P.strictTransformIso i hi.le) y
  have hcomm : ∀ x : ↥(S.strictTransform i),
      (S'.strictTransformι i).base (((P.strictTransformIso i hi.le).hom).base x)
        = (P.levelMap i hi.le).base ((S.strictTransformι i).base x) := fun x =>
    congrArg (fun g : S.strictTransform i ⟶ S'.schemeAt i => g.base x)
      (P.strictTransformIso_hom_comp_strictTransformι i hi.le)
  have hinj :=
    (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding (P.levelMap i hi.le)).injective
  have hsupp := P.support_ambientCenter_eq_image i hi
  simp only [EmbeddedBlowupSequence.mem_detachedComponents]
  refine and_congr (mem_irreducibleComponents_iff_image_consolidated350 (⇑((P.strictTransformIso i hi.le).hom))
    (⇑((P.strictTransformIso i hi.le).inv)) (P.strictTransformIso i hi.le).hom.base.hom.continuous
    (P.strictTransformIso i hi.le).inv.base.hom.continuous hgf hfg C) ?_
  constructor
  · intro h z hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨x, hxC, rfl⟩ := hy
    rw [hsupp]
    exact ⟨(S.strictTransformι i).base x, h ⟨x, hxC, rfl⟩, (hcomm x).symm⟩
  · intro h z hz
    obtain ⟨x, hxC, rfl⟩ := hz
    have hmem : (S'.strictTransformι i).base (((P.strictTransformIso i hi.le).hom).base x)
        ∈ ((S'.ambientCenter i).support : Set ↥(S'.schemeAt i)) :=
      h ⟨((P.strictTransformIso i hi.le).hom).base x, ⟨x, hxC, rfl⟩, rfl⟩
    rw [hsupp] at hmem
    obtain ⟨w, hw, hweq⟩ := hmem
    have hweq' : (P.levelMap i hi.le).base w
        = (P.levelMap i hi.le).base ((S.strictTransformι i).base x) := hweq.trans (hcomm x)
    have hwx : w = (S.strictTransformι i).base x := hinj hweq'
    rwa [hwx] at hw

private theorem sUnion_eq_image_sUnion_consolidated350 {α β : Type u} (f : α → β)
    (hf : Function.Surjective f) (A : Set (Set α)) (B : Set (Set β))
    (h : ∀ C : Set α, C ∈ A ↔ f '' C ∈ B) :
    ⋃₀ B = f '' (⋃₀ A) := by
  apply Set.Subset.antisymm
  · rintro x ⟨D, hD, hxD⟩
    obtain ⟨y, rfl⟩ := hf x
    refine ⟨y, ⟨f ⁻¹' D, ?_, hxD⟩, rfl⟩
    refine (h (f ⁻¹' D)).mpr ?_
    rw [Set.image_preimage_eq D hf]
    exact hD
  · rintro z ⟨y, hy, rfl⟩
    obtain ⟨C, hC, hyC⟩ := hy
    exact ⟨f '' C, (h C).mp hC, ⟨y, hyC, rfl⟩⟩

section
variable (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length)

theorem detachedLocus_eq_image :
    S'.detachedLocus i = ⇑((P.strictTransformIso i hi.le).hom) '' S.detachedLocus i := by
  have hsurj : Function.Surjective ⇑((P.strictTransformIso i hi.le).hom) :=
    (Scheme.homeoOfIso (P.strictTransformIso i hi.le)).surjective
  rw [S'.detachedLocus_eq_sUnion i, S.detachedLocus_eq_sUnion i]
  exact sUnion_eq_image_sUnion_consolidated350 _ hsurj _ _
    (fun C => P.mem_detachedComponents_iff i hi C)

theorem coe_detachedClosure_eq_image :
    (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) =
      ⇑((P.strictTransformIso i hi.le).hom) '' (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) := by
  have h1 : (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) = closure (S'.detachedLocus i) := rfl
  have h2 : (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) = closure (S.detachedLocus i) := rfl
  rw [h1, h2, P.detachedLocus_eq_image i hi]
  exact ((Scheme.homeoOfIso (P.strictTransformIso i hi.le)).image_closure (S.detachedLocus i)).symm

theorem preimage_coe_detachedClosure :
    ⇑((P.strictTransformIso i hi.le).hom) ⁻¹' (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) =
      (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) := by
  rw [P.coe_detachedClosure_eq_image i hi]
  exact Set.preimage_image_eq _ (Scheme.homeoOfIso (P.strictTransformIso i hi.le)).injective


end

theorem comap_detachedIdeal (P : ChartPushforward S S') [IsReduced Y] (i : ℕ)
    (hi : i < S'.length) :
    (S'.detachedIdeal i).comap (P.strictTransformIso i hi.le).hom = S.detachedIdeal i := by
  have hn' : TopologicalSpace.NoetherianSpace ↥(S'.strictTransform i) :=
    S'.noetherianSpace_strictTransform i hi.le
  have hn : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i) :=
    S.noetherianSpace_strictTransform i (P.le_length hi.le)
  have hr' : IsReduced (S'.strictTransform i) :=
    S'.isReduced_strictTransform i hi.le
  have hr : IsReduced (S.strictTransform i) :=
    S.isReduced_strictTransform i (P.le_length hi.le)
  have hfl : Flat (P.strictTransformIso i hi.le).hom := inferInstance
  have hS : S'.detachedComponents i ⊆ irreducibleComponents ↥(S'.strictTransform i) :=
    fun C hC => ((S'.mem_detachedComponents i C).mp hC).1
  have hZ : (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) = ⋃₀ (S'.detachedComponents i) :=
    (S'.detachedClosure_coe i).trans (S'.detachedLocus_eq_sUnion i)
  have hZ' : (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) =
      ⇑((P.strictTransformIso i hi.le).hom).base ⁻¹' (⋃₀ (S'.detachedComponents i)) := by
    rw [← hZ]
    exact (P.preimage_coe_detachedClosure i hi).symm
  rw [S'.detachedIdeal_eq i, S.detachedIdeal_eq i]
  exact comap_vanishingIdeal_sUnion (P.strictTransformIso i hi.le).hom hS hZ hZ'

private theorem exists_subschemeIso_of_comap_eq_consolidated350 {X Z : Scheme.{u}} (e : X ≅ Z)
    (I : X.IdealSheafData) (J : Z.IdealSheafData) (h : J.comap e.hom = I) :
    ∃ u : I.subscheme ≅ J.subscheme, u.hom ≫ J.subschemeι = I.subschemeι ≫ e.hom := by
  have h1 : J ≤ I.map e.hom :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr (le_of_eq h)
  have hcomp : I.comap e.inv = J := by
    rw [← h, ← Scheme.IdealSheafData.comap_comp, e.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  have h2 : I ≤ J.map e.inv :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr (le_of_eq hcomp)
  obtain ⟨a, ha⟩ : ∃ a : I.subscheme ⟶ J.subscheme,
      a ≫ J.subschemeι = I.subschemeι ≫ e.hom :=
    ⟨I.subschemeMap J e.hom h1, Scheme.IdealSheafData.subschemeMap_subschemeι I J e.hom h1⟩
  obtain ⟨b, hb⟩ : ∃ b : J.subscheme ⟶ I.subscheme,
      b ≫ I.subschemeι = J.subschemeι ≫ e.inv :=
    ⟨J.subschemeMap I e.inv h2, Scheme.IdealSheafData.subschemeMap_subschemeι J I e.inv h2⟩
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · refine (cancel_mono I.subschemeι).mp ?_
    rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc, e.hom_inv_id,
      Category.comp_id, Category.id_comp]
  · refine (cancel_mono J.subschemeι).mp ?_
    rw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc, e.inv_hom_id,
      Category.comp_id, Category.id_comp]

theorem exists_iso_detachedScheme (P : ChartPushforward S S') [IsReduced Y] (i : ℕ)
    (hi : i < S'.length) :
    ∃ e : S.detachedScheme i ≅ S'.detachedScheme i,
      e.hom ≫ S'.detachedι i = S.detachedι i ≫ (P.strictTransformIso i hi.le).hom := by
  exact exists_subschemeIso_of_comap_eq_consolidated350 (P.strictTransformIso i hi.le) (S.detachedIdeal i)
    (S'.detachedIdeal i) (P.comap_detachedIdeal i hi)

def detachedSchemeIso (P : ChartPushforward S S') [IsReduced Y] (i : ℕ)
    (hi : i < S'.length) : S.detachedScheme i ≅ S'.detachedScheme i :=
  (P.exists_iso_detachedScheme i hi).choose

@[reassoc]
theorem detachedSchemeIso_hom_comp_detachedι (P : ChartPushforward S S') [IsReduced Y] (i : ℕ)
    (hi : i < S'.length) :
    (P.detachedSchemeIso i hi).hom ≫ S'.detachedι i = S.detachedι i ≫ (P.strictTransformIso i hi.le).hom :=
  (P.exists_iso_detachedScheme i hi).choose_spec

section
variable (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length)

theorem preimage_detachedClosureCompl :
    (P.strictTransformIso i hi.le).hom ⁻¹ᵁ (S'.detachedClosureCompl i) = S.detachedClosureCompl i := by
  have h : ⇑((P.strictTransformIso i hi.le).hom) ⁻¹' (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) =
      (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) := P.preimage_coe_detachedClosure i hi
  have h2 : ⇑((P.strictTransformIso i hi.le).hom) ⁻¹'
      ((↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i))ᶜ) =
      ((↑(S.detachedClosure i) : Set ↥(S.strictTransform i))ᶜ) := by
    rw [Set.preimage_compl, h]
  exact TopologicalSpace.Opens.ext h2

theorem comap_comapAmbientCenter :
    (S'.comapAmbientCenter i).comap (P.strictTransformIso i hi.le).hom = S.comapAmbientCenter i := by
  have hmap : S'.ambientCenter i = (S.ambientCenter i).map (P.levelMap i hi.le) := by
    rw [P.ambientCenter_eq i hi, map_eq_imageIdealSheaf]
  simp only [EmbeddedBlowupSequence.comapAmbientCenter_eq]
  rw [← Scheme.IdealSheafData.comap_comp, P.strictTransformIso_hom_comp_strictTransformι i hi.le,
    Scheme.IdealSheafData.comap_comp, hmap, Blowup.comap_map_of_isClosedImmersion]


end

private theorem exists_isIso_of_preimage_opens_eq_consolidated350 {X Z : Scheme.{u}} (e : X ≅ Z) (U : X.Opens)
    (U' : Z.Opens) (hU : e.hom ⁻¹ᵁ U' = U) :
    ∃ ψ : U.toScheme ⟶ U'.toScheme, IsIso ψ ∧ ψ ≫ U'.ι = U.ι ≫ e.hom := by
  have hfwd : ∀ y : ↥X, y ∈ (U : Set ↥X) → ⇑e.hom.base y ∈ (U' : Set ↥Z) := by
    intro y hy
    have h : y ∈ (↑(e.hom ⁻¹ᵁ U') : Set ↥X) := by rw [hU]; exact hy
    exact h
  have hbwd : ∀ y : ↥X, ⇑e.hom.base y ∈ (U' : Set ↥Z) → y ∈ (U : Set ↥X) := by
    intro y hy
    have h : y ∈ (↑(e.hom ⁻¹ᵁ U') : Set ↥X) := hy
    rwa [hU] at h
  have h1 : Set.range ⇑(U.ι ≫ e.hom).base ⊆ Set.range ⇑U'.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    show ⇑e.hom.base (⇑U.ι.base x) ∈ (U' : Set ↥Z)
    exact hfwd _ x.2
  have h2 : Set.range ⇑(U'.ι ≫ e.inv).base ⊆ Set.range ⇑U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    show ⇑e.inv.base (⇑U'.ι.base y) ∈ (U : Set ↥X)
    refine hbwd _ ?_
    have hy : ⇑e.hom.base (⇑e.inv.base (⇑U'.ι.base y)) = ⇑U'.ι.base y :=
      Scheme.inv_hom_apply e (⇑U'.ι.base y)
    rw [hy]
    exact y.2
  refine ⟨IsOpenImmersion.lift U'.ι (U.ι ≫ e.hom) h1, ?_, ?_⟩
  · refine ⟨⟨IsOpenImmersion.lift U.ι (U'.ι ≫ e.inv) h2, ?_, ?_⟩⟩
    · rw [← cancel_mono U.ι, Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc,
        IsOpenImmersion.lift_fac, Category.assoc, e.hom_inv_id, Category.comp_id,
        Category.id_comp]
    · rw [← cancel_mono U'.ι, Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc,
        IsOpenImmersion.lift_fac, Category.assoc, e.inv_hom_id, Category.comp_id,
        Category.id_comp]
  · rw [IsOpenImmersion.lift_fac]

theorem comap_centerOffDetached (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    (S'.centerOffDetached i).comap (P.strictTransformIso i hi.le).hom = S.centerOffDetached i := by
  have hns' : TopologicalSpace.NoetherianSpace ↥(S'.strictTransform i) :=
    S'.noetherianSpace_strictTransform i hi.le
  have hnU : TopologicalSpace.NoetherianSpace ↥((S'.detachedClosureCompl i).toScheme) :=
    Blowup.noetherianSpace_toScheme (S'.strictTransform i) (S'.detachedClosureCompl i)
  have hqc : QuasiCompact (S'.detachedClosureCompl i).ι :=
    ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hfl : Flat (P.strictTransformIso i hi.le).hom := inferInstance
  obtain ⟨ψ, hψ, hψc⟩ := exists_isIso_of_preimage_opens_eq_consolidated350 (P.strictTransformIso i hi.le) (S.detachedClosureCompl i)
    (S'.detachedClosureCompl i) (P.preimage_detachedClosureCompl i hi)
  have := hψ
  have H : IsPullback ψ (S.detachedClosureCompl i).ι (S'.detachedClosureCompl i).ι (P.strictTransformIso i hi.le).hom :=
    IsPullback.of_horiz_isIso ⟨hψc⟩
  have key := comap_map_eq_map_comap_of_isPullback H
    ((S'.comapAmbientCenter i).comap (S'.detachedClosureCompl i).ι)
  have hW : ((S'.comapAmbientCenter i).comap (S'.detachedClosureCompl i).ι).comap ψ
      = (S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι := by
    rw [← Scheme.IdealSheafData.comap_comp, hψc, Scheme.IdealSheafData.comap_comp,
      P.comap_comapAmbientCenter i hi]
  rw [hW] at key
  have hS' : S'.centerOffDetached i
      = ((S'.comapAmbientCenter i).comap (S'.detachedClosureCompl i).ι).map (S'.detachedClosureCompl i).ι :=
    (S'.centerOffDetached_eq i).trans (map_eq_ker_subschemeι_comp _ _).symm
  have hS : S.centerOffDetached i
      = ((S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι).map (S.detachedClosureCompl i).ι :=
    (S.centerOffDetached_eq i).trans (map_eq_ker_subschemeι_comp _ _).symm
  rw [hS', hS]
  exact key

end ChartPushforward


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.InducedBlowupsFlatBaseChange
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section

namespace ChartFlatBaseChange

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]
  {k' : Type u} [Field k'] [CharZero k'] {Y' : Scheme.{u}} [IsAffine Y']
  {pY' : Y' ⟶ Spec (CommRingCat.of k')} [LocallyOfFiniteType pY']
  {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

private theorem congr_hom_apply_consolidated351 {A B : Scheme.{u}} {f g : A ⟶ B} (e : f = g) (a : A) :
    f a = g a := by
  subst e
  rfl

@[reassoc]
theorem levelMap_succ_comp_transitionMap (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length)
    (hσ : F.reindex j ≤ F.reindex (j + 1)) :
    F.levelMap (j + 1) (Nat.succ_le_of_lt hj) ≫ S.ambientSeq.transitionMap hσ =
      S'.blowdown j ≫ F.levelMap j (le_of_lt hj) := by
  have hσ' : F.reindex j + 1 ≤ F.reindex (j + 1) := F.reindex_lt_succ j hj
  have key : S.ambientSeq.transitionMap hσ' ≫ S.blowdown (F.reindex j) = S.ambientSeq.transitionMap hσ := by
    rw [show S.blowdown (F.reindex j) = S.ambientSeq.transitionMap (Nat.le_succ (F.reindex j)) from
        S.ambientSeq.blowupMorphism_eq_transitionMap _, S.ambientSeq.transitionMap_trans]
  have hw := (F.isPullback_step j hj hσ').w
  rw [Category.assoc, key] at hw
  exact hw

@[reassoc]
theorem strictTransformComparison_succ_comp_strictTransformMapOfLE (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length)
    (hσ : F.reindex j ≤ F.reindex (j + 1)) :
    F.strictTransformComparison (j + 1) (Nat.succ_le_of_lt hj) ≫ S.strictTransformMapOfLE hσ =
      S'.strictTransformMap j ≫ F.strictTransformComparison j (le_of_lt hj) := by
  have : Mono (S.strictTransformι (F.reindex j)) := inferInstance
  rw [← cancel_mono (S.strictTransformι (F.reindex j))]
  have e1 : (F.strictTransformComparison (j + 1) (Nat.succ_le_of_lt hj) ≫ S.strictTransformMapOfLE hσ) ≫
        S.strictTransformι (F.reindex j)
      = S'.strictTransformι (j + 1) ≫ (S'.blowdown j ≫ F.levelMap j (le_of_lt hj)) := by
    rw [Category.assoc, S.strictTransformMapOfLE_strictTransformι, ← Category.assoc, F.strictTransformComparison_comp_strictTransformι,
      Category.assoc, F.levelMap_succ_comp_transitionMap j hj hσ]
  have e2 : (S'.strictTransformMap j ≫ F.strictTransformComparison j (le_of_lt hj)) ≫ S.strictTransformι (F.reindex j)
      = S'.strictTransformι (j + 1) ≫ (S'.blowdown j ≫ F.levelMap j (le_of_lt hj)) := by
    rw [Category.assoc, F.strictTransformComparison_comp_strictTransformι, ← Category.assoc, S'.strictTransformMap_comp_strictTransformι, Category.assoc]
  rw [e1, e2]

@[reassoc]
theorem inr_totalSpaceMap (F : ChartFlatBaseChange S S') [IsReduced Y]
    [IsReduced Y'] (j : ℕ) (hj : j ≤ S'.length) :
    (coprod.inr : S'.detachedCoprod j ⟶ S'.totalSpace j) ≫ F.totalSpaceMap j hj =
      F.inactiveTotalMap j hj ≫
        (coprod.inr : S.detachedCoprod (F.reindex j) ⟶ S.totalSpace (F.reindex j)) := by
  simp [ChartFlatBaseChange.totalSpaceMap]

section
variable (F : ChartFlatBaseChange S S') [IsReduced Y] [IsReduced Y']

private theorem totalTransition_comp_totalSpaceMap_consolidated351 (j : ℕ) (hj : j < S'.length)
    (hσ : F.reindex j ≤ F.reindex (j + 1)) :
    S'.totalTransition j ≫ F.totalSpaceMap j (le_of_lt hj) =
      F.totalSpaceMap (j + 1) (Nat.succ_le_of_lt hj) ≫ S.totalMapOfLE hσ := by
  apply coprod.hom_ext
  · have e1 : (coprod.inl : S'.strictTransform (j + 1) ⟶ S'.totalSpace (j + 1)) ≫
          (S'.totalTransition j ≫ F.totalSpaceMap j (le_of_lt hj))
        = S'.strictTransformMap j ≫ F.strictTransformComparison j (le_of_lt hj) ≫ coprod.inl := by
      rw [← Category.assoc, S'.inl_totalTransition, Category.assoc, F.inl_totalSpaceMap]
    have e2 : (coprod.inl : S'.strictTransform (j + 1) ⟶ S'.totalSpace (j + 1)) ≫
          (F.totalSpaceMap (j + 1) (Nat.succ_le_of_lt hj) ≫ S.totalMapOfLE hσ)
        = S'.strictTransformMap j ≫ F.strictTransformComparison j (le_of_lt hj) ≫ coprod.inl := by
      rw [← Category.assoc, F.inl_totalSpaceMap, Category.assoc, S.inl_totalMapOfLE,
        ← Category.assoc, F.strictTransformComparison_succ_comp_strictTransformMapOfLE j hj hσ, Category.assoc]
    rw [e1, e2]
  · apply S'.detachedCoprod_hom_ext (j + 1)
    intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hlt | heq
    · have h1 := F.detachedToCoprod_inr_totalSpaceMap (j + 1) (Nat.succ_le_of_lt hj) s hs
      have h4 := F.detachedToCoprod_inr_totalSpaceMap j (le_of_lt hj) s hlt
      have h2 := S.detachedToCoprod_detachedCoprodMapOfLE (F.reindex_lt_reindex hlt (le_of_lt hj)) hσ
      have h3 := S.detachedCoprodMapOfLE_inr_totalMapOfLE hσ
      have h6 := S'.detachedCoprodInl_inr_totalTransition_assoc j (F.totalSpaceMap j (le_of_lt hj))
      rw [reassoc_of% h1, ← h2]
      rw [S'.detachedToCoprod_succ_of_lt s j hlt]
      simp only [Category.assoc]
      rw [h6, h4, h3]
    · subst heq
      have h1 := F.detachedToCoprod_inr_totalSpaceMap (s + 1) (Nat.succ_le_of_lt hj) s hs
      rw [reassoc_of% h1, S.detachedToCoprod_inr_totalMapOfLE hσ (le_refl (F.reindex s))
          (F.reindex_lt_succ s hj), S.strictTransformMapOfLE_self]
      rw [S'.detachedToCoprod_self s]
      simp only [Category.id_comp]
      rw [S'.detachedCoprodInr_inr_totalTransition_assoc s (F.totalSpaceMap s (le_of_lt hj)),
        F.inl_totalSpaceMap, F.detachedSchemeComparison_comp_detachedι_assoc s hj coprod.inl]

private theorem totalCenter_eq_comap_consolidated351 (i : ℕ) (hi : i < S'.length) :
    S'.totalCenter i = (S.totalCenter (F.reindex i)).comap (F.totalSpaceMap i hi.le) := by
  apply FunctorialResolution.Blowup.idealSheafData_ext_coprod
  · have l1 : (S'.totalCenter i).comap
        (coprod.inl : S'.strictTransform i ⟶ S'.totalSpace i) = S'.centerOffDetached i := by
      rw [S'.totalCenter_eq, FunctorialResolution.Blowup.ker_comp_coprod_inl_comap_inl,
        Scheme.IdealSheafData.ker_subschemeι]
    have l2 : (S.totalCenter (F.reindex i)).comap
        (coprod.inl : S.strictTransform (F.reindex i) ⟶ S.totalSpace (F.reindex i))
        = S.centerOffDetached (F.reindex i) := by
      rw [S.totalCenter_eq, FunctorialResolution.Blowup.ker_comp_coprod_inl_comap_inl,
        Scheme.IdealSheafData.ker_subschemeι]
    rw [l1, ← Scheme.IdealSheafData.comap_comp, F.inl_totalSpaceMap,
      Scheme.IdealSheafData.comap_comp, l2, ← F.centerOffDetached_eq_comap i hi]
  · have r1 : (S'.totalCenter i).comap
        (coprod.inr : S'.detachedCoprod i ⟶ S'.totalSpace i) = ⊤ := by
      rw [S'.totalCenter_eq]
      exact FunctorialResolution.Blowup.ker_comp_coprod_inl_comap_inr _
    rw [r1, ← Scheme.IdealSheafData.comap_comp, F.inr_totalSpaceMap,
      Scheme.IdealSheafData.comap_comp, S.totalCenter_eq,
      FunctorialResolution.Blowup.ker_comp_coprod_inl_comap_inr]
    simp


end

private theorem comap_center_eq_top_of_not_mem_range_reindex_consolidated351 (F : ChartFlatBaseChange S S') (h : S.TransitionsAreBlowups) (i : ℕ)
    (hi : i < S.length) (hskip : ∀ j, j < S'.length → F.reindex j ≠ i) :
    ((S.inducedBlowups h).center i).comap (pullback.snd F.baseMap ((S.inducedBlowups h).projectionToBase i)) = ⊤ := by
  rw [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_center]
  apply FunctorialResolution.Blowup.comap_eq_top_of_notMem_support
  intro x hx
  rw [S.totalCenter_eq] at hx
  have hmem : (pullback.snd F.baseMap ((S.inducedBlowups h).projectionToBase i)) x ∈
      closure (Set.range
        (⇑((S.centerOffDetached i).subschemeι ≫
          (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)))) := by
    rw [← Scheme.Hom.support_ker]
    exact hx
  have hrange : Set.range
        (⇑((S.centerOffDetached i).subschemeι ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)))
      ⊆ (⇑(coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) ''
        (↑(S.centerOffDetached i).support : Set (S.strictTransform i)) := by
    rintro y ⟨t, rfl⟩
    refine ⟨(S.centerOffDetached i).subschemeι t, ?_, (Scheme.Hom.comp_apply _ _ t).symm⟩
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact Set.mem_range_self t
  have hce : Topology.IsClosedEmbedding
      (⇑(coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) :=
    AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding
      (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)
  have hsupclosed : IsClosed (↑(S.centerOffDetached i).support : Set (S.strictTransform i)) :=
    (S.centerOffDetached i).support.2
  have hclosed : IsClosed ((⇑(coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) ''
      (↑(S.centerOffDetached i).support : Set (S.strictTransform i))) :=
    hce.isClosedMap _ hsupclosed
  obtain ⟨a, ha, hax⟩ := (closure_minimal hrange hclosed) hmem
  have ha2 : (S.strictTransformι i) a ∈ (↑(S.ambientCenter i).support : Set (S.schemeAt i)) :=
    S.support_centerOffDetached_subset_preimage i ha
  set b := (pullback.fst F.baseMap ((S.inducedBlowups h).projectionToBase i)) x with hb
  have hcond := congr_hom_apply_consolidated351 (pullback.condition (f := F.baseMap)
    (g := (S.inducedBlowups h).projectionToBase i)) x
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hcond
  have hstr : ((S.inducedBlowups h).projectionToBase i) ((coprod.inl : S.strictTransform i ⟶ S.totalSpace i) a)
      = (S.strictTransformToBase i) a :=
    congr_hom_apply_consolidated351 (FunctorialResolution.EmbeddedResolution.inl_inducedBlowups_projectionToBase S h i) a
  have hemb := congr_hom_apply_consolidated351 F.isPullback_emb.w b
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hemb
  have hae := congr_hom_apply_consolidated351 (S.strictTransformToBase_emb i) a
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hae
  have hcompat : F.ambientMap (S'.emb b) = (S.ambientSeq.projectionToBase i) ((S.strictTransformι i) a) := by
    rw [← hemb, ← hae, ← hstr, hax, ← hcond]
  obtain ⟨z, hz1, hz2⟩ :=
    Scheme.Pullback.exists_preimage_pullback (S'.emb b) ((S.strictTransformι i) a) hcompat
  have hcs := F.comap_center_skipped i hi (fun j hj => hskip j hj)
    (pullback F.ambientMap (S.ambientSeq.projectionToBase i))
    (pullback.snd F.ambientMap (S.ambientSeq.projectionToBase i))
    (pullback.fst F.ambientMap (S.ambientSeq.projectionToBase i))
    ((IsPullback.of_hasPullback F.ambientMap (S.ambientSeq.projectionToBase i)).flip)
  have hz0 : (pullback.snd F.ambientMap (S.ambientSeq.projectionToBase i)) z ∈
      (S.ambientCenter i).support := by
    rw [hz2]; exact ha2
  have hz : z ∈ ((S.ambientCenter i).comap
      (pullback.snd F.ambientMap (S.ambientSeq.projectionToBase i))).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hz0
  rw [hcs] at hz
  simp at hz
  exact hz

private def inducedBlowupsSchemeAtIsoPullback_consolidated351 (F : ChartFlatBaseChange S S') [IsReduced Y]
    [IsReduced Y'] (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups)
    (i : ℕ) (hi : i ≤ (S'.inducedBlowups h').length) :
    (S'.inducedBlowups h').schemeAt i ≅ pullback F.baseMap ((S.inducedBlowups h).projectionToBase (F.reindex i)) :=
  ((F.isPullback_totalSpaceMap h h' i
    (by rwa [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hi)).flip).isoPullback

section
variable (F : ChartFlatBaseChange S S') [IsReduced Y] [IsReduced Y'] (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups)

private theorem inducedBlowupsIso_hom_fst_consolidated351 (i : ℕ) (hi : i ≤ (S'.inducedBlowups h').length) :
    (F.inducedBlowupsSchemeAtIsoPullback_consolidated351 h h' i hi).hom ≫ pullback.fst F.baseMap ((S.inducedBlowups h).projectionToBase (F.reindex i))
      = (S'.inducedBlowups h').projectionToBase i :=
  IsPullback.isoPullback_hom_fst _

private theorem inducedBlowupsIso_hom_snd_consolidated351 (i : ℕ) (hi : i ≤ (S'.inducedBlowups h').length) :
    (F.inducedBlowupsSchemeAtIsoPullback_consolidated351 h h' i hi).hom ≫ pullback.snd F.baseMap ((S.inducedBlowups h).projectionToBase (F.reindex i))
      = F.totalSpaceMap i (by rwa [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hi) :=
  IsPullback.isoPullback_hom_snd _

theorem isPullbackUpToEmptyCenters_inducedBlowups :
    IsPullbackUpToEmptyCenters F.baseMap (S'.inducedBlowups h') (S.inducedBlowups h) := by
  refine ⟨F.reindex, fun i hi => F.inducedBlowupsSchemeAtIsoPullback_consolidated351 h h' i hi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hi ⊢
    exact F.reindex_lt i hi
  · intro i j hj hij
    rw [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hj
    exact F.reindex_lt_reindex_of_lt hij hj
  · rw [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length, FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length]
    exact F.reindex_len
  · intro i hi hns
    have hi' : i < S.length := by rwa [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hi
    have hskip : ∀ j, j < S'.length → F.reindex j ≠ i := by
      intro j hj he
      exact hns ⟨j, by rwa [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length], he⟩
    rintro ⟨x, hx⟩
    rw [F.comap_center_eq_top_of_not_mem_range_reindex_consolidated351 h i hi' hskip] at hx
    simp at hx
    exact hx
  · intro i hi
    exact F.inducedBlowupsIso_hom_fst_consolidated351 h h' i hi
  · intro i hi hr
    have hi' : i < S'.length := by rwa [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hi
    apply pullback.hom_ext
    · rw [Category.assoc, F.inducedBlowupsIso_hom_fst_consolidated351, Category.assoc,
        SequenceOfBlowups.pullbackTransitionMap_comp_fst, F.inducedBlowupsIso_hom_fst_consolidated351,
        SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_comp_projectionToBase]
    · rw [Category.assoc, F.inducedBlowupsIso_hom_snd_consolidated351, Category.assoc,
        SequenceOfBlowups.pullbackTransitionMap_comp_snd, ← Category.assoc, F.inducedBlowupsIso_hom_snd_consolidated351,
        FunctorialResolution.EmbeddedResolution.inducedBlowups_blowupMorphism, FunctorialResolution.EmbeddedResolution.inducedBlowups_transitionMap]
      exact F.totalTransition_comp_totalSpaceMap_consolidated351 i hi' hr
  · intro i hi
    have hi' : i < S'.length := by rwa [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hi
    rw [F.inducedBlowupsIso_hom_snd_consolidated351, FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_center, FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_center]
    exact F.totalCenter_eq_comap_consolidated351 i hi'

theorem isPullbackBlowupSequence_inducedBlowupsWithoutIso :
    IsPullbackBlowupSequence F.baseMap (S'.inducedBlowupsWithoutIso h') (S.inducedBlowupsWithoutIso h) :=
  (F.isPullbackUpToEmptyCenters_inducedBlowups h h').isPullbackSequenceOfBlowups_withoutIsoBlowups


end

end ChartFlatBaseChange


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRuleLocality
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private theorem principalizationAlgorithm_toSequenceOfBlowups_congr_ideal_consolidated383 (A : PrincipalizationAlgorithm.{u}) (k : Type u) [Field k] [CharZero k]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p]
    [QuasiCompact p]
    (I J : X.IdealSheafData) (hIJ : I = J)
    (hI : NonzeroOnComponents I) (hJ : NonzeroOnComponents J)
    (E : List X.IdealSheafData) (hE hE' : InStrictNormalCrossingPosition p E) :
    (A k X p I hI E hE).toSequenceOfBlowups = (A k X p J hJ E hE').toSequenceOfBlowups := by
  subst hIJ
  rfl

private theorem isPullbackSequenceOfBlowups_congr_left_consolidated383 {X X' : Scheme.{u}} {φ : X' ⟶ X}
    {s1 s2 : SequenceOfBlowups X'} {t : SequenceOfBlowups X} (h : s1 = s2) (H : IsPullbackBlowupSequence φ s1 t) :
    IsPullbackBlowupSequence φ s2 t := by
  subst h
  exact H

section
variable (A : PrincipalizationAlgorithm.{u}) (hA : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
include hA hw

theorem embeddedResolutionRule_isPullbackBlowupSequence_of_smooth
    (k : Type u) [Field k] [CharZero k] (Y Y' : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) (p' : Y' ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [QuasiCompact p]
    [IsReduced Y] [IsAffine Y]
    [LocallyOfFiniteType p'] [QuasiCompact p']
    [IsReduced Y'] [IsAffine Y']
    (D : EmbeddingDatum k Y p) (D' : EmbeddingDatum k Y' p')
    (φ : D'.ambient ⟶ D.ambient) [Smooth φ] (ψ : Y' ⟶ Y)
    (hφ : φ ≫ D.ambientStruct = D'.ambientStruct)
    (hsq : IsPullback D'.emb ψ φ D.emb) :
    IsPullbackBlowupSequence ψ (embeddedResolutionRuleOfPrincipalization A hw k Y' p' D')
      (embeddedResolutionRuleOfPrincipalization A hw k Y p D) := by
  have : Flat φ := inferInstance
  have : QuasiCompact D.emb := inferInstance
  have : QuasiCompact D'.emb := inferInstance
  have hker : D'.emb.ker = D.emb.ker.comap φ :=
    ker_eq_comap_ker_of_isPullback_of_flat hsq.flip
  have hI' : NonzeroOnComponents (D.emb.ker.comap φ) := hker ▸ D'.nonzeroOnComponents_ker
  have hE' : InStrictNormalCrossingPosition D'.ambientStruct
      (List.map (fun Z => Z.comap φ) ([] : List D.ambient.IdealSheafData)) := D'.sncEmpty
  have h0 := hA.smooth_pullback k D.ambient D.ambientStruct D.emb.ker
      D.nonzeroOnComponents_ker [] D.sncEmpty D'.ambient D'.ambientStruct φ hφ hI' hE'
  have hpb : IsPullbackBlowupSequence φ (D'.toEmbeddedBlowupSequence A).ambientSeq (D.toEmbeddedBlowupSequence A).ambientSeq := by
    rw [EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups, EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups]
    exact isPullbackSequenceOfBlowups_congr_left_consolidated383
      (principalizationAlgorithm_toSequenceOfBlowups_congr_ideal_consolidated383 A k D'.ambient D'.ambientStruct
        (D.emb.ker.comap φ) D'.emb.ker hker.symm hI' _ [] hE' _) h0
  have hflat2 : Flat
      (show (D'.toEmbeddedBlowupSequence A).ambient ⟶ (D.toEmbeddedBlowupSequence A).ambient from φ) :=
    (inferInstance : Flat φ)
  rw [embeddedResolutionRuleOfPrincipalization_apply, embeddedResolutionRuleOfPrincipalization_apply]
  exact (chartFlatBaseChangeOfIsPullbackSeq (D.toEmbeddedBlowupSequence A) (D'.toEmbeddedBlowupSequence A) φ ψ
    hsq.flip hpb).isPullbackBlowupSequence_inducedBlowupsWithoutIso _ _

theorem embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps
    :
    EmbeddedResolutionRule.IsCompatibleWithSmoothAmbientMaps (embeddedResolutionRuleOfPrincipalization A hw) := by
  intro k _ _ Y Y' p p' _ _ _ _ _ _ _ _ D D' φ _ ψ hφ hsq
  exact embeddedResolutionRule_isPullbackBlowupSequence_of_smooth A hA hw k Y Y' p p' D D' φ ψ hφ hsq

theorem embeddedResolutionRule_isStrictPullbackBlowupSeq_baseChange
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [QuasiCompact p]
    [IsReduced Y] [IsAffine Y]
    (D : EmbeddingDatum k Y p) (K : Type u) [Field K] [CharZero K] [Algebra k K]
    [IsReduced (baseChange p K)]
    (hker : NonzeroOnComponents (D.baseChangeEmb K).ker)
    (hsnc : InStrictNormalCrossingPosition (baseChangeToSpec D.ambientStruct K)
      ([] : List (baseChange D.ambientStruct K).IdealSheafData)) :
    haveI : IsAffine (baseChange p K) := isAffine_baseChange p K
    haveI : LocallyOfFiniteType (baseChangeToSpec p K) :=
      locallyOfFiniteType_baseChangeToSpec p K
    haveI : QuasiCompact (baseChangeToSpec p K) :=
      quasiCompact_baseChangeToSpec p K
    IsStrictPullbackBlowupSeq (baseChangeProjection p K)
      (embeddedResolutionRuleOfPrincipalization A hw K (baseChange p K) (baseChangeToSpec p K)
        (D.baseChange K hker hsnc))
      (embeddedResolutionRuleOfPrincipalization A hw k Y p D) := by
  have : IsAffine (baseChange p K) := isAffine_baseChange p K
  have : LocallyOfFiniteType (baseChangeToSpec p K) :=
    locallyOfFiniteType_baseChangeToSpec p K
  have : QuasiCompact (baseChangeToSpec p K) :=
    quasiCompact_baseChangeToSpec p K
  have : IsAffine (baseChange D.ambientStruct K) :=
    EmbeddingDatum.isAffine_baseChange_ambientToSpec D K
  have : Smooth (baseChangeToSpec D.ambientStruct K) :=
    EmbeddingDatum.smooth_baseChangeToSpec_ambientToSpec D K
  have : LocallyOfFiniteType (baseChangeToSpec D.ambientStruct K) :=
    EmbeddingDatum.locallyOfFiniteType_baseChangeToSpec_ambientToSpec D K
  have : QuasiCompact (baseChangeToSpec D.ambientStruct K) :=
    EmbeddingDatum.quasiCompact_baseChangeToSpec_ambientToSpec D K
  have : Flat (baseChangeProjection D.ambientStruct K) := inferInstance
  have : AlgebraicGeometry.Surjective (baseChangeProjection p K) := inferInstance
  have : QuasiCompact D.emb := inferInstance
  have : QuasiCompact (D.baseChangeEmb K) := inferInstance
  show IsStrictPullbackBlowupSeq (baseChangeProjection p K)
      (embeddedResolutionRuleOfPrincipalization A hw K (baseChange p K) (baseChangeToSpec p K)
        (D.baseChange K hker hsnc))
      (embeddedResolutionRuleOfPrincipalization A hw k Y p D)
  have hkerbc : (D.baseChangeEmb K).ker
      = D.emb.ker.comap (baseChangeProjection D.ambientStruct K) :=
    ker_eq_comap_ker_of_isPullback_of_flat (D.isPullback_baseChangeEmb K).flip
  have hI' : NonzeroOnComponents (D.emb.ker.comap (baseChangeProjection D.ambientStruct K)) :=
    hkerbc ▸ hker
  have hE' : InStrictNormalCrossingPosition (baseChangeToSpec D.ambientStruct K)
      (List.map (fun Z => Z.comap (baseChangeProjection D.ambientStruct K))
        ([] : List D.ambient.IdealSheafData)) := hsnc
  have h0 := hA.base_change k D.ambient D.ambientStruct D.emb.ker D.nonzeroOnComponents_ker
      [] D.sncEmpty K (algebraMap k K) hI' hE'
  have hpb : IsPullbackBlowupSequence (baseChangeProjection D.ambientStruct K)
      ((D.baseChange K hker hsnc).toEmbeddedBlowupSequence A).ambientSeq
      (D.toEmbeddedBlowupSequence A).ambientSeq := by
    rw [EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups, EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups]
    exact isPullbackSequenceOfBlowups_congr_left_consolidated383
      (principalizationAlgorithm_toSequenceOfBlowups_congr_ideal_consolidated383 A K (baseChange D.ambientStruct K)
        (baseChangeToSpec D.ambientStruct K)
        (D.emb.ker.comap (baseChangeProjection D.ambientStruct K)) (D.baseChangeEmb K).ker
        hkerbc.symm hI' _ [] hE' _) h0
  have hflat2 : Flat
      (show ((D.baseChange K hker hsnc).toEmbeddedBlowupSequence A).ambient ⟶
          (D.toEmbeddedBlowupSequence A).ambient from baseChangeProjection D.ambientStruct K) :=
    (inferInstance : Flat (baseChangeProjection D.ambientStruct K))
  rw [embeddedResolutionRuleOfPrincipalization_apply, embeddedResolutionRuleOfPrincipalization_apply]
  refine IsPullbackBlowupSequence.isStrictPullback_of_surjective ?_ ?_
  · exact (chartFlatBaseChangeOfIsPullbackSeq (D.toEmbeddedBlowupSequence A)
      ((D.baseChange K hker hsnc).toEmbeddedBlowupSequence A) (baseChangeProjection D.ambientStruct K)
      (baseChangeProjection p K) (D.isPullback_baseChangeEmb K).flip hpb).isPullbackBlowupSequence_inducedBlowupsWithoutIso _ _
  · intro i hi
    exact SequenceOfBlowups.withoutIsoBlowups_center_ne_top ((D.toEmbeddedBlowupSequence A).inducedBlowups _) hi

theorem embeddedResolutionRule_isCompatibleWithFieldBaseChange
    :
    EmbeddedResolutionRule.IsCompatibleWithFieldBaseChange (embeddedResolutionRuleOfPrincipalization A hw) := by
  intro k _ _ Y p _ _ _ _ D K _ _ _ _ hker hsnc
  exact embeddedResolutionRule_isStrictPullbackBlowupSeq_baseChange A hA hw k Y p D K hker hsnc


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.InactiveTotalSpacePushforward
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section

namespace ChartPushforward

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]
  {S S' : EmbeddedBlowupSequence k Y pY}

section
variable (P : ChartPushforward S S') {i : ℕ}
include P

theorem le_length_of_le_length (hi : i ≤ S.length) : i ≤ S'.length := by
  rw [← P.len_eq]
  exact hi

theorem lt_length_of_lt_length (hi : i < S.length) : i < S'.length := by
  rw [← P.len_eq]
  exact hi


end

private def detachedCoprodIsoOfLE_consolidated382 (P : ChartPushforward S S') [IsReduced Y] :
    ∀ i : ℕ, i ≤ S'.length → (S.detachedCoprod i ≅ S'.detachedCoprod i) := fun i =>
  Nat.rec (motive := fun n => n ≤ S'.length → (S.detachedCoprod n ≅ S'.detachedCoprod n))
    (fun _ => eqToIso (S.detachedCoprod_zero.trans S'.detachedCoprod_zero.symm))
    (fun n ih hn => coprod.mapIso (ih (Nat.le_of_succ_le hn))
      (P.detachedSchemeIso n (lt_of_lt_of_le (Nat.lt_succ_self n) hn))) i

theorem exists_iso_detachedCoprod_compatible (P : ChartPushforward S S')
    [IsReduced Y] :
    ∃ e : ∀ i : ℕ, i ≤ S'.length → (S.detachedCoprod i ≅ S'.detachedCoprod i),
      (∀ h : (0 : ℕ) ≤ S'.length,
          (e 0 h).hom = eqToHom (S.detachedCoprod_zero.trans S'.detachedCoprod_zero.symm)) ∧
      (∀ (i : ℕ) (hi : i < S'.length),
          S.detachedCoprodInl i ≫ (e (i + 1) hi).hom = (e i hi.le).hom ≫ S'.detachedCoprodInl i) ∧
      (∀ (i : ℕ) (hi : i < S'.length),
          S.detachedCoprodInr i ≫ (e (i + 1) hi).hom =
            (P.detachedSchemeIso i hi).hom ≫ S'.detachedCoprodInr i) := by
  refine ⟨detachedCoprodIsoOfLE_consolidated382 P, fun _ => rfl, ?_, ?_⟩
  · intro i hi
    show (coprod.inl : S.detachedCoprod i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i) ≫
        coprod.map (detachedCoprodIsoOfLE_consolidated382 P i hi.le).hom (P.detachedSchemeIso i hi).hom =
      (detachedCoprodIsoOfLE_consolidated382 P i hi.le).hom ≫
        (coprod.inl : S'.detachedCoprod i ⟶ S'.detachedCoprod i ⨿ S'.detachedScheme i)
    simp
  · intro i hi
    show (coprod.inr : S.detachedScheme i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i) ≫
        coprod.map (detachedCoprodIsoOfLE_consolidated382 P i hi.le).hom (P.detachedSchemeIso i hi).hom =
      (P.detachedSchemeIso i hi).hom ≫
        (coprod.inr : S'.detachedScheme i ⟶ S'.detachedCoprod i ⨿ S'.detachedScheme i)
    simp

def inactiveTotalIso (P : ChartPushforward S S') [IsReduced Y] (i : ℕ)
    (hi : i ≤ S'.length) : S.detachedCoprod i ≅ S'.detachedCoprod i :=
  P.exists_iso_detachedCoprod_compatible.choose i hi

@[reassoc]
theorem detachedCoprodInl_inactiveTotalIso_hom (P : ChartPushforward S S')
    [IsReduced Y] (i : ℕ) (hi : i < S'.length) :
    S.detachedCoprodInl i ≫ (P.inactiveTotalIso (i + 1) hi).hom =
      (P.inactiveTotalIso i hi.le).hom ≫ S'.detachedCoprodInl i :=
  P.exists_iso_detachedCoprod_compatible.choose_spec.2.1 i hi

@[reassoc]
theorem detachedCoprodInr_inactiveTotalIso_hom (P : ChartPushforward S S')
    [IsReduced Y] (i : ℕ) (hi : i < S'.length) :
    S.detachedCoprodInr i ≫ (P.inactiveTotalIso (i + 1) hi).hom =
      (P.detachedSchemeIso i hi).hom ≫ S'.detachedCoprodInr i :=
  P.exists_iso_detachedCoprod_compatible.choose_spec.2.2 i hi

def totalSpaceIso (P : ChartPushforward S S') [IsReduced Y] (i : ℕ)
    (hi : i ≤ S'.length) : S.totalSpace i ≅ S'.totalSpace i :=
  coprod.mapIso (P.strictTransformIso i hi) (P.inactiveTotalIso i hi)

theorem totalSpaceIso_hom_eq_coprodMap (P : ChartPushforward S S') [IsReduced Y] (i : ℕ)
    (hi : i ≤ S'.length) :
    (P.totalSpaceIso i hi).hom =
      coprod.map (P.strictTransformIso i hi).hom (P.inactiveTotalIso i hi).hom := rfl

@[reassoc]
theorem inl_totalSpaceIso_hom (P : ChartPushforward S S') [IsReduced Y] (i : ℕ)
    (hi : i ≤ S'.length) :
    (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ (P.totalSpaceIso i hi).hom =
      (P.strictTransformIso i hi).hom ≫ (coprod.inl : S'.strictTransform i ⟶ S'.totalSpace i) := by
  rw [P.totalSpaceIso_hom_eq_coprodMap i hi]
  simp

@[reassoc]
theorem inr_totalSpaceIso_hom (P : ChartPushforward S S') [IsReduced Y] (i : ℕ)
    (hi : i ≤ S'.length) :
    (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫ (P.totalSpaceIso i hi).hom =
      (P.inactiveTotalIso i hi).hom ≫ (coprod.inr : S'.detachedCoprod i ⟶ S'.totalSpace i) := by
  rw [P.totalSpaceIso_hom_eq_coprodMap i hi]
  simp

section
variable {A B : Scheme.{u}} (e : A ≅ B)

private theorem comap_hom_comap_inv_consolidated382 (I : B.IdealSheafData) :
    (I.comap e.hom).comap e.inv = I := by
  rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id]

private theorem comap_inv_comap_hom_consolidated382 (I : A.IdealSheafData) :
    (I.comap e.inv).comap e.hom = I := by
  rw [← Scheme.IdealSheafData.comap_comp, e.hom_inv_id, Scheme.IdealSheafData.comap_id]


end

private theorem comap_map_of_comm_iso_consolidated382 {A B A' B' : Scheme.{u}} (eA : A ≅ A') (eB : B ≅ B')
    (u : A ⟶ B) (u' : A' ⟶ B') (hcomm : u ≫ eB.hom = eA.hom ≫ u')
    (J : A'.IdealSheafData) :
    (J.map u').comap eB.hom = (J.comap eA.hom).map u := by
  have hcomm' : u' ≫ eB.inv = eA.inv ≫ u := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hcomm, Category.assoc, eB.hom_inv_id,
      Category.comp_id]
  refine le_antisymm ?_ ?_
  · rw [Scheme.IdealSheafData.le_map_iff_comap_le, ← Scheme.IdealSheafData.comap_comp, hcomm,
      Scheme.IdealSheafData.comap_comp]
    exact Scheme.IdealSheafData.comap_mono _
      (Scheme.IdealSheafData.le_map_iff_comap_le.mp le_rfl)
  · have key : ((J.comap eA.hom).map u).comap eB.inv ≤ J.map u' := by
      rw [Scheme.IdealSheafData.le_map_iff_comap_le, ← Scheme.IdealSheafData.comap_comp, hcomm',
        Scheme.IdealSheafData.comap_comp]
      have h2 : (((J.comap eA.hom).map u).comap u).comap eA.inv ≤
          (J.comap eA.hom).comap eA.inv :=
        Scheme.IdealSheafData.comap_mono eA.inv
          (Scheme.IdealSheafData.le_map_iff_comap_le.mp
            (le_rfl : (J.comap eA.hom).map u ≤ (J.comap eA.hom).map u))
      rw [comap_hom_comap_inv_consolidated382 eA J] at h2
      exact h2
    have h3 : (((J.comap eA.hom).map u).comap eB.inv).comap eB.hom ≤
        (J.map u').comap eB.hom :=
      Scheme.IdealSheafData.comap_mono eB.hom key
    rwa [comap_inv_comap_hom_consolidated382 eB] at h3

section
variable (P : ChartPushforward S S') [IsReduced Y] (i : ℕ) (hi : i < S'.length)

theorem comap_totalCenter :
    (S'.totalCenter i).comap (P.totalSpaceIso i hi.le).hom = S.totalCenter i := by
  have h := comap_map_of_comm_iso_consolidated382 (P.strictTransformIso i hi.le) (P.totalSpaceIso i hi.le)
      (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)
      (coprod.inl : S'.strictTransform i ⟶ S'.totalSpace i)
      (P.inl_totalSpaceIso_hom i hi.le) (S'.centerOffDetached i)
  rw [P.comap_centerOffDetached i hi] at h
  exact h

private theorem totalSpaceIso_hom_totalTransition_consolidated382 :
    (P.totalSpaceIso (i + 1) hi).hom ≫ S'.totalTransition i
      = S.totalTransition i ≫ (P.totalSpaceIso i hi.le).hom := by
  refine coprod.hom_ext ?_ ?_
  · rw [P.inl_totalSpaceIso_hom_assoc (i + 1) hi, S'.inl_totalTransition_eq_strictTransformMap_inl i, S.inl_totalTransition_assoc i,
      P.inl_totalSpaceIso_hom i hi.le]
    exact P.strictTransformIso_hom_comp_strictTransformMap_assoc i hi _
  · refine S.detachedCoprod_succ_hom_ext i ?_ ?_
    · rw [P.inr_totalSpaceIso_hom_assoc (i + 1) hi, P.detachedCoprodInl_inactiveTotalIso_hom_assoc i hi,
        S'.detachedCoprodInl_inr_totalTransition i, S.detachedCoprodInl_inr_totalTransition_assoc i,
        P.inr_totalSpaceIso_hom i hi.le]
    · rw [P.inr_totalSpaceIso_hom_assoc (i + 1) hi, P.detachedCoprodInr_inactiveTotalIso_hom_assoc i hi,
        S'.detachedCoprodInr_inr_totalTransition i, S.detachedCoprodInr_inr_totalTransition_assoc i,
        P.inl_totalSpaceIso_hom i hi.le]
      exact P.detachedSchemeIso_hom_comp_detachedι_assoc i hi _


end

section
variable (P : ChartPushforward S S') [IsReduced Y] (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups)
include P

theorem inducedBlowups_isomorphic :
    (S.inducedBlowups h).Isomorphic (S'.inducedBlowups h') := by
  refine ⟨P.len_eq, fun i hi => P.totalSpaceIso i (P.le_length_of_le_length hi), ?_, ?_, ?_⟩
  · show (P.totalSpaceIso 0 (Nat.zero_le _)).hom ≫ S'.totalSpaceZeroIso.hom = S.totalSpaceZeroIso.hom
    refine coprod.hom_ext ?_ ?_
    · rw [P.inl_totalSpaceIso_hom_assoc 0 (Nat.zero_le _), S'.inl_totalSpaceZeroIso_hom,
        S.inl_totalSpaceZeroIso_hom]
      exact P.strictTransformIso_zero_hom_comp_strictTransformZeroIso_hom
    · have hB : IsInitial (S.detachedCoprod 0) := initialIsInitial
      exact hB.hom_ext _ _
  · intro i hi
    rw [inducedBlowups_blowupMorphism S' h' i, inducedBlowups_blowupMorphism S h i]
    exact P.totalSpaceIso_hom_totalTransition_consolidated382 i (P.lt_length_of_lt_length hi)
  · intro i hi
    exact P.comap_totalCenter i (P.lt_length_of_lt_length hi)

theorem inducedBlowupsWithoutIso_isomorphic :
    (S.inducedBlowupsWithoutIso h).Isomorphic (S'.inducedBlowupsWithoutIso h') :=
  (P.inducedBlowups_isomorphic h h').withoutIsoBlowups


end

end ChartPushforward


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EnlargeAmbientSpace
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section

namespace EmbeddingDatum

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
  {p : Y ⟶ Spec (CommRingCat.of k)}

private theorem emb_comp_comp_eq_of_comp_eq_consolidated413 (G : EmbeddingDatum k Y p) {A' : Scheme.{u}}
    (q : A' ⟶ Spec (CommRingCat.of k)) (τ : G.ambient ⟶ A')
    (hτ : τ ≫ q = G.ambientStruct) :
    (G.emb ≫ τ) ≫ q = p := by
  rw [Category.assoc, hτ, G.comp_eq]

def enlargeAmbient (G : EmbeddingDatum k Y p) (A' : Scheme.{u}) [IsAffine A']
    (q : A' ⟶ Spec (CommRingCat.of k)) [Smooth q]
    [LocallyOfFiniteType q] [QuasiCompact q]
    (τ : G.ambient ⟶ A') [IsClosedImmersion τ]
    (hτ : τ ≫ q = G.ambientStruct)
    (hker : NonzeroOnComponents (G.emb ≫ τ).ker)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A'.IdealSheafData)) :
    EmbeddingDatum k Y p :=
  embeddingDatumOfClosedImmersion A' q (G.emb ≫ τ) hker (emb_comp_comp_eq_of_comp_eq_consolidated413 G q τ hτ) hsnc

private theorem imageIdealSheaf_ker_eq_ker_comp_consolidated413 {Yc A A' : Scheme.{u}} (e : Yc ⟶ A)
    [IsClosedImmersion e] (σ : A ⟶ A') :
    imageIdealSheaf σ (Scheme.Hom.ker e) = Scheme.Hom.ker (e ≫ σ) :=
  (Scheme.Hom.ker_comp e σ).symm

theorem isPushforwardBlowupSeq_ambientBlowups_enlargeAmbient [IsAffine Y]
    [LocallyOfFiniteType p]
    (G : EmbeddingDatum k Y p) (Alg : PrincipalizationAlgorithm.{u}) (hAlg : IsFunctorialPrincipalization Alg)
    (A' : Scheme.{u}) [IsAffine A']
    (q : A' ⟶ Spec (CommRingCat.of k)) [Smooth q]
    [LocallyOfFiniteType q] [QuasiCompact q]
    (τ : G.ambient ⟶ A') [IsClosedImmersion τ]
    (hτ : τ ≫ q = G.ambientStruct)
    (hker : NonzeroOnComponents (G.emb ≫ τ).ker)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A'.IdealSheafData))
    (c : ℕ) (hc : 1 ≤ c) (hcodim : HasEtaleCoordCodim q τ c) :
    IsPushforwardBlowupSeq τ (G.toEmbeddedBlowupSequence Alg).ambientSeq
      ((G.enlargeAmbient A' q τ hτ hker hsnc).toEmbeddedBlowupSequence Alg).ambientSeq := by
  have himg : imageIdealSheaf τ (Scheme.Hom.ker G.emb) = Scheme.Hom.ker (G.emb ≫ τ) :=
    imageIdealSheaf_ker_eq_ker_comp_consolidated413 G.emb τ
  have hJ : NonzeroOnComponents (imageIdealSheaf τ (Scheme.Hom.ker G.emb)) := by
    rw [himg]; exact hker
  have key : ∀ (J : A'.IdealSheafData) (hJ' : NonzeroOnComponents J),
      J = Scheme.Hom.ker (G.emb ≫ τ) →
      IsPushforwardBlowupSeq τ (G.toEmbeddedBlowupSequence Alg).ambientSeq
        (Alg k A' q J hJ' ([] : List A'.IdealSheafData) hsnc).toSequenceOfBlowups →
      IsPushforwardBlowupSeq τ (G.toEmbeddedBlowupSequence Alg).ambientSeq
        ((G.enlargeAmbient A' q τ hτ hker hsnc).toEmbeddedBlowupSequence Alg).ambientSeq := by
    rintro J hJ' rfl h
    exact h
  exact key _ hJ himg
    (hAlg.pushforward k G.ambient A' G.ambientStruct q τ hτ c hc hcodim
      (Scheme.Hom.ker G.emb) G.nonzeroOnComponents_ker hJ G.sncEmpty hsnc)

theorem isomorphic_embeddedResolutionRule_enlargeAmbient [IsAffine Y]
    [IsReduced Y] [LocallyOfFiniteType p]
    [QuasiCompact p]
    (G : EmbeddingDatum k Y p) (Alg : PrincipalizationAlgorithm.{u}) (hAlg : IsFunctorialPrincipalization Alg)
    (hw : TransitionsAreBlowupsForEmbeddings Alg)
    (A' : Scheme.{u}) [IsAffine A']
    (q : A' ⟶ Spec (CommRingCat.of k)) [Smooth q]
    [LocallyOfFiniteType q] [QuasiCompact q]
    (τ : G.ambient ⟶ A') [IsClosedImmersion τ]
    (hτ : τ ≫ q = G.ambientStruct)
    (hker : NonzeroOnComponents (G.emb ≫ τ).ker)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A'.IdealSheafData))
    (c : ℕ) (hc : 1 ≤ c) (hcodim : HasEtaleCoordCodim q τ c) :
    (embeddedResolutionRuleOfPrincipalization Alg hw k Y p G).Isomorphic
      (embeddedResolutionRuleOfPrincipalization Alg hw k Y p (G.enlargeAmbient A' q τ hτ hker hsnc)) := by
  have P : ChartPushforward (G.toEmbeddedBlowupSequence Alg)
      ((G.enlargeAmbient A' q τ hτ hker hsnc).toEmbeddedBlowupSequence Alg) :=
    @ChartPushforward.ofIsPushforwardSeq k _ _ Y _ p _ (G.toEmbeddedBlowupSequence Alg)
      ((G.enlargeAmbient A' q τ hτ hker hsnc).toEmbeddedBlowupSequence Alg) τ
      (inferInstanceAs (IsClosedImmersion τ)) rfl
      (isPushforwardBlowupSeq_ambientBlowups_enlargeAmbient G Alg hAlg A' q τ hτ hker hsnc c hc hcodim)
  exact P.inducedBlowupsWithoutIso_isomorphic (hw k Y p G) (hw k Y p (G.enlargeAmbient A' q τ hτ hker hsnc))

end EmbeddingDatum


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IndependenceOfEmbedding
section

open CategoryTheory AlgebraicGeometry

section

private def affineSpaceIndexedByIsoOfEquiv_consolidated435 (k : Type u) [Field k] {N M : Type u} (σ : N ≃ M) :
    affineSpaceIndexedBy k M ≅ affineSpaceIndexedBy k N where
  hom := AffineSpace.reindex σ (Spec (CommRingCat.of k))
  inv := AffineSpace.reindex σ.symm (Spec (CommRingCat.of k))
  hom_inv_id := by
    refine AffineSpace.hom_ext ?_ ?_
    · simp
    · intro i
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
        AffineSpace.reindex_appTop_coord, Equiv.apply_symm_apply]
      simp
  inv_hom_id := by
    refine AffineSpace.hom_ext ?_ ?_
    · simp
    · intro i
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
        AffineSpace.reindex_appTop_coord, Equiv.symm_apply_apply]
      simp

private def uliftFinAddEquivUliftSum_consolidated435 (n m : ℕ) :
    ULift.{u, 0} (Fin (n + m)) ≃ ULift.{u, 0} (Fin n ⊕ Fin m) :=
  Equiv.ulift.trans (finSumFinEquiv.symm.trans Equiv.ulift.symm)

section
variable (k : Type u) [Field k] (N : Type u)

private theorem locallyOfFiniteType_affineSpaceIndexedByToSpec_consolidated435 [Finite N] : LocallyOfFiniteType (affineSpaceIndexedByToSpec k N) := by
  unfold affineSpaceIndexedByToSpec
  infer_instance

private theorem quasiCompact_affineSpaceIndexedByToSpec_consolidated435 :
    QuasiCompact (affineSpaceIndexedByToSpec k N) := by
  unfold affineSpaceIndexedByToSpec
  infer_instance

private theorem irreducibleSpace_affineSpaceIndexedBy_consolidated435 :
    IrreducibleSpace ↥(affineSpaceIndexedBy k N) := by
  have : IrreducibleSpace ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum k))
  infer_instance


end

private theorem flat_of_isIso_consolidated435 {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : CategoryTheory.IsIso f) :
    Flat f := by
  have := hf
  have : IsOpenImmersion f := inferInstance
  infer_instance

private theorem principalizationAlgorithm_toSequenceOfBlowups_congr_consolidated435 (Alg : PrincipalizationAlgorithm.{u}) (k : Type u) [Field k]
    [CharZero k] (X : Scheme.{u}) (q : X ⟶ Spec (CommRingCat.of k))
    [Smooth q] [LocallyOfFiniteType q]
    [QuasiCompact q] (I J : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (hJ : NonzeroOnComponents J) (E F : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition q E)
    (hF : InStrictNormalCrossingPosition q F) (hIJ : I = J) (hEF : E = F) :
    (Alg k X q I hI E hE).toSequenceOfBlowups = (Alg k X q J hJ F hF).toSequenceOfBlowups := by
  subst hIJ
  subst hEF
  rfl

theorem smooth_affineSpaceIndexedByToSpec_finSumFin (hsm : AffineSpaceIsSmooth.{u}) (k : Type u)
    [Field k] (n m : ℕ) :
    Smooth (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m))) := by
  have hs : Smooth (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + m)))) :=
    hsm k (n + m)
  have h : AffineSpace.reindex (uliftFinAddEquivUliftSum_consolidated435 n m) (Spec (CommRingCat.of k)) ≫
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + m))) =
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)) := by
    simp [affineSpaceIndexedByToSpec]
  have : CategoryTheory.IsIso (AffineSpace.reindex (uliftFinAddEquivUliftSum_consolidated435 n m) (Spec (CommRingCat.of k))) :=
    ⟨AffineSpace.reindex (uliftFinAddEquivUliftSum_consolidated435 n m).symm (Spec (CommRingCat.of k)),
      (affineSpaceIndexedByIsoOfEquiv_consolidated435 k (uliftFinAddEquivUliftSum_consolidated435 n m)).hom_inv_id,
      (affineSpaceIndexedByIsoOfEquiv_consolidated435 k (uliftFinAddEquivUliftSum_consolidated435 n m)).inv_hom_id⟩
  have hiso : Smooth
      (AffineSpace.reindex (uliftFinAddEquivUliftSum_consolidated435 n m) (Spec (CommRingCat.of k))) :=
    inferInstance
  rw [← h]
  exact MorphismProperty.comp_mem (@Smooth) _ _ hiso hs

theorem isomorphic_embeddedResolutionRuleOfPrincipalization_of_iso (Alg : PrincipalizationAlgorithm.{u}) (hAlg : IsFunctorialPrincipalization Alg)
    (hw : TransitionsAreBlowupsForEmbeddings Alg) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [IsAffine Y] [IsReduced Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    [QuasiCompact p] (D D' : EmbeddingDatum k Y p)
    (Φ : D.ambient ≅ D'.ambient) (hΦ : Φ.hom ≫ D'.ambientStruct = D.ambientStruct)
    (hemb : D.emb ≫ Φ.hom = D'.emb) :
    (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D).Isomorphic (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D') := by
  have : QuasiCompact D.emb := inferInstance
  have : QuasiCompact D'.emb := inferInstance
  have hiso : CategoryTheory.IsIso Φ.inv := ⟨Φ.hom, Φ.inv_hom_id, Φ.hom_inv_id⟩
  have : Flat Φ.inv := flat_of_isIso_consolidated435 Φ.inv hiso
  have : Smooth Φ.inv := inferInstance
  have hsq : D'.emb ≫ Φ.inv = D.emb := by
    rw [← hemb, Category.assoc, Φ.hom_inv_id, Category.comp_id]
  have hpbk : IsPullback (𝟙 Y) D'.emb D.emb Φ.inv :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, hsq]⟩
  have hker : D'.emb.ker = D.emb.ker.comap Φ.inv := ker_eq_comap_ker_of_isPullback_of_flat hpbk
  have hφp : Φ.inv ≫ D.ambientStruct = D'.ambientStruct := by
    rw [← hΦ, ← Category.assoc, Φ.inv_hom_id, Category.id_comp]
  have hI' : NonzeroOnComponents (D.emb.ker.comap Φ.inv) := by
    rw [← hker]
    exact D'.nonzeroOnComponents_ker
  have hpbseq := hAlg.smooth_pullback k D.ambient D.ambientStruct D.emb.ker
    D.nonzeroOnComponents_ker ([] : List D.ambient.IdealSheafData) D.sncEmpty
    D'.ambient D'.ambientStruct Φ.inv hφp hI' D'.sncEmpty
  have hseq : (Alg k D'.ambient D'.ambientStruct D'.emb.ker D'.nonzeroOnComponents_ker
        ([] : List D'.ambient.IdealSheafData) D'.sncEmpty).toSequenceOfBlowups =
      (Alg k D'.ambient D'.ambientStruct (D.emb.ker.comap Φ.inv) hI'
        (List.map (fun Z => Z.comap Φ.inv) ([] : List D.ambient.IdealSheafData))
        D'.sncEmpty).toSequenceOfBlowups :=
    principalizationAlgorithm_toSequenceOfBlowups_congr_consolidated435 Alg k D'.ambient D'.ambientStruct _ _ _ _ _ _ _ _ hker rfl
  have hpb2 : IsPullbackBlowupSequence Φ.inv (D'.toEmbeddedBlowupSequence Alg).ambientSeq
      (D.toEmbeddedBlowupSequence Alg).ambientSeq := by
    rw [EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups, EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups, hseq]
    exact hpbseq
  have hpbemb : IsPullback (𝟙 Y) (D'.toEmbeddedBlowupSequence Alg).emb (D.toEmbeddedBlowupSequence Alg).emb Φ.inv :=
    hpbk
  have hisoC : CategoryTheory.IsIso
      (show (D'.toEmbeddedBlowupSequence Alg).ambient ⟶ (D.toEmbeddedBlowupSequence Alg).ambient from Φ.inv) :=
    ⟨Φ.hom, Φ.inv_hom_id, Φ.hom_inv_id⟩
  have hflatC : Flat
      (show (D'.toEmbeddedBlowupSequence Alg).ambient ⟶ (D.toEmbeddedBlowupSequence Alg).ambient from Φ.inv) :=
    flat_of_isIso_consolidated435 _ hisoC
  have hres : IsPullbackBlowupSequence (𝟙 Y) (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D')
      (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D) :=
    ChartFlatBaseChange.isPullbackBlowupSequence_inducedBlowupsWithoutIso
      (chartFlatBaseChangeOfIsPullbackSeq (D.toEmbeddedBlowupSequence Alg) (D'.toEmbeddedBlowupSequence Alg) Φ.inv (𝟙 Y)
        hpbemb hpb2) (hw k Y p D) (hw k Y p D')
  exact (isomorphic_of_isPullbackSequenceOfBlowups_id _ _ hres
    (hasProperCenters_embeddedResolutionRuleOfPrincipalization Alg hw k Y p D)).symm

def LocallyConstCodimImpliesConstantCodim : Prop :=
  ∀ (k : Type u) [Field k] (X X' : Scheme.{u}) (q : X' ⟶ Spec (CommRingCat.of k))
    [Smooth q] (τ : X ⟶ X') [IsClosedImmersion τ] (c : ℕ),
    HasSmoothCoordCodim q τ c → HasEtaleCoordCodim q τ c

def LinearEmbeddingsHaveLocallyConstCodim : Prop :=
  ∀ (k : Type u) [Field k] (n m : ℕ),
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)))
        (affineSpaceInl k n m) m ∧
      HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)))
        (affineSpaceInrEmbedding k n m) n

section
variable (Alg : PrincipalizationAlgorithm.{u}) (hAlg : IsFunctorialPrincipalization Alg) (hw : TransitionsAreBlowupsForEmbeddings Alg) (hsm : AffineSpaceIsSmooth.{u}) (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) (hcod : LocallyConstCodimImpliesConstantCodim.{u}) (hlin : LinearEmbeddingsHaveLocallyConstCodim.{u})
include hAlg hsm hcmp hcod hlin

theorem isomorphic_embeddedResolutionRuleOfPrincipalization (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [IsAffine Y] [IsReduced Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    [QuasiCompact p] (D D' : EmbeddingDatum k Y p)
    (P : ClosedEmbeddingIntoAffineSpace D) (P' : ClosedEmbeddingIntoAffineSpace D') :
    (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D).Isomorphic (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D') := by
  have hsA : Smooth (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))) :=
    hsm k P.dim
  have hsA' : Smooth (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))) :=
    hsm k P'.dim
  have hsB : Smooth
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim))) :=
    smooth_affineSpaceIndexedByToSpec_finSumFin hsm k P.dim P'.dim
  have := locallyOfFiniteType_affineSpaceIndexedByToSpec_consolidated435 k (ULift.{u, 0} (Fin P.dim))
  have := locallyOfFiniteType_affineSpaceIndexedByToSpec_consolidated435 k (ULift.{u, 0} (Fin P'.dim))
  have := locallyOfFiniteType_affineSpaceIndexedByToSpec_consolidated435 k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim))
  have := quasiCompact_affineSpaceIndexedByToSpec_consolidated435 k (ULift.{u, 0} (Fin P.dim))
  have := quasiCompact_affineSpaceIndexedByToSpec_consolidated435 k (ULift.{u, 0} (Fin P'.dim))
  have := quasiCompact_affineSpaceIndexedByToSpec_consolidated435 k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim))
  have := irreducibleSpace_affineSpaceIndexedBy_consolidated435 k (ULift.{u, 0} (Fin P.dim))
  have := irreducibleSpace_affineSpaceIndexedBy_consolidated435 k (ULift.{u, 0} (Fin P'.dim))
  have := irreducibleSpace_affineSpaceIndexedBy_consolidated435 k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim))
  have hciL : IsClosedImmersion (affineSpaceInl k P.dim P'.dim) :=
    isClosedImmersion_affineSpaceInl k P.dim P'.dim
  have hciR : IsClosedImmersion (affineSpaceInrEmbedding k P.dim P'.dim) :=
    isClosedImmersion_affineSpaceInrEmbedding k P.dim P'.dim
  have : IsClosedImmersion (D.emb ≫ P.toAffine) := inferInstance
  have : IsClosedImmersion (D'.emb ≫ P'.toAffine) := inferInstance
  have hker1 : NonzeroOnComponents (Scheme.Hom.ker (D.emb ≫ P.toAffine)) :=
    nonzeroOnComponents_ker_comp D.emb P.toAffine D.nonzeroOnComponents_ker
  have hker1' : NonzeroOnComponents (Scheme.Hom.ker (D'.emb ≫ P'.toAffine)) :=
    nonzeroOnComponents_ker_comp D'.emb P'.toAffine D'.nonzeroOnComponents_ker
  have hsnc1 : InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim)))
      ([] : List (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim))).IdealSheafData) :=
    inStrictNormalCrossingPosition_nil (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim)))
  have hsnc1' : InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim)))
      ([] : List (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim))).IdealSheafData) :=
    inStrictNormalCrossingPosition_nil (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim)))
  have hsncB : InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      ([] : List
        (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim))).IdealSheafData) :=
    inStrictNormalCrossingPosition_nil (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
  have hcd1 : HasEtaleCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim)))
      P.toAffine P.codimBound :=
    hcod k D.ambient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))) P.toAffine P.codimBound
      P.locallyConstCodim
  have hcd1' : HasEtaleCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim)))
      P'.toAffine P'.codimBound :=
    hcod k D'.ambient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))) P'.toAffine P'.codimBound
      P'.locallyConstCodim
  have hker2 : NonzeroOnComponents
      (Scheme.Hom.ker ((D.emb ≫ P.toAffine) ≫ affineSpaceInl k P.dim P'.dim)) :=
    nonzeroOnComponents_ker_comp (D.emb ≫ P.toAffine) (affineSpaceInl k P.dim P'.dim) hker1
  have hker2' : NonzeroOnComponents
      (Scheme.Hom.ker ((D'.emb ≫ P'.toAffine) ≫ affineSpaceInrEmbedding k P.dim P'.dim)) :=
    nonzeroOnComponents_ker_comp (D'.emb ≫ P'.toAffine) (affineSpaceInrEmbedding k P.dim P'.dim) hker1'
  have hcd2 : HasEtaleCoordCodim
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceInl k P.dim P'.dim) P'.dim :=
    hcod k (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim)))
      (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceInl k P.dim P'.dim) P'.dim (hlin k P.dim P'.dim).1
  have hcd2' : HasEtaleCoordCodim
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceInrEmbedding k P.dim P'.dim) P.dim :=
    hcod k (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim)))
      (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceInrEmbedding k P.dim P'.dim) P.dim (hlin k P.dim P'.dim).2
  have hciL2 : IsClosedImmersion
      (show (D.enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim)))
            (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))) P.toAffine P.toAffine_comp
            hker1 hsnc1).ambient ⟶
          affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)) from
        affineSpaceInl k P.dim P'.dim) :=
    isClosedImmersion_affineSpaceInl k P.dim P'.dim
  have hciR2 : IsClosedImmersion
      (show (D'.enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim)))
            (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))) P'.toAffine P'.toAffine_comp
            hker1' hsnc1').ambient ⟶
          affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)) from
        affineSpaceInrEmbedding k P.dim P'.dim) :=
    isClosedImmersion_affineSpaceInrEmbedding k P.dim P'.dim
  have e1 := D.isomorphic_embeddedResolutionRule_enlargeAmbient Alg hAlg hw
    (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim)))
    (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))) P.toAffine P.toAffine_comp hker1 hsnc1
    P.codimBound P.one_le_codimBound hcd1
  have e2 := (D.enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))) P.toAffine P.toAffine_comp hker1
      hsnc1).isomorphic_embeddedResolutionRule_enlargeAmbient Alg hAlg hw
      (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceInl k P.dim P'.dim) (affineSpaceInl_comp_affineSpaceIndexedByToSpec k P.dim P'.dim) hker2 hsncB
      P'.dim P'.one_le_dim hcd2
  have e1' := D'.isomorphic_embeddedResolutionRule_enlargeAmbient Alg hAlg hw
    (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim)))
    (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))) P'.toAffine P'.toAffine_comp hker1'
    hsnc1' P'.codimBound P'.one_le_codimBound hcd1'
  have e2' := (D'.enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))) P'.toAffine P'.toAffine_comp hker1'
      hsnc1').isomorphic_embeddedResolutionRule_enlargeAmbient Alg hAlg hw
      (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceInrEmbedding k P.dim P'.dim) (affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec k P.dim P'.dim) hker2' hsncB
      P.dim P.one_le_dim hcd2'
  have hc1 : (D.emb ≫ P.toAffine) ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim)) = p := by
    rw [Category.assoc, P.toAffine_comp, D.comp_eq]
  have hc2 : (D'.emb ≫ P'.toAffine) ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim)) = p := by
    rw [Category.assoc, P'.toAffine_comp, D'.comp_eq]
  obtain ⟨Φ, hΦ1, hΦ2⟩ :=
    hcmp k Y p P.dim P'.dim (D.emb ≫ P.toAffine) (D'.emb ≫ P'.toAffine) hc1 hc2
  have hembL : (D.emb ≫ P.toAffine) ≫ affineSpaceInl k P.dim P'.dim =
      AffineSpace.homOfVector p (coordVectorInl P.dim P'.dim (D.emb ≫ P.toAffine)) :=
    comp_affineSpaceInl P.dim P'.dim p (D.emb ≫ P.toAffine) hc1
  have hembR : (D'.emb ≫ P'.toAffine) ≫ affineSpaceInrEmbedding k P.dim P'.dim =
      AffineSpace.homOfVector p (coordVectorInr P.dim P'.dim (D'.emb ≫ P'.toAffine)) :=
    comp_affineSpaceInrEmbedding P.dim P'.dim p (D'.emb ≫ P'.toAffine) hc2
  have hfin : ((D.emb ≫ P.toAffine) ≫ affineSpaceInl k P.dim P'.dim) ≫ Φ.hom =
      (D'.emb ≫ P'.toAffine) ≫ affineSpaceInrEmbedding k P.dim P'.dim := by
    rw [hembL, hembR]
    exact hΦ2
  have e3 := isomorphic_embeddedResolutionRuleOfPrincipalization_of_iso Alg hAlg hw k Y p
    ((D.enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim)))
        (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))) P.toAffine P.toAffine_comp hker1
        hsnc1).enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
        (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
        (affineSpaceInl k P.dim P'.dim) (affineSpaceInl_comp_affineSpaceIndexedByToSpec k P.dim P'.dim) hker2 hsncB)
    ((D'.enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim)))
        (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))) P'.toAffine P'.toAffine_comp hker1'
        hsnc1').enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
        (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
        (affineSpaceInrEmbedding k P.dim P'.dim) (affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec k P.dim P'.dim) hker2' hsncB)
    Φ hΦ1 hfin
  exact e1.trans (e2.trans (e3.trans (e1'.trans e2').symm))

theorem isIndependentOfPresentedEmbedding_of_locallyConstCodim :
    (embeddedResolutionRuleOfPrincipalization Alg hw).IsIndependentOfPresentedEmbedding := by
  intro k _ _ Y p _ _ _ _ D D' P P'
  exact isomorphic_embeddedResolutionRuleOfPrincipalization Alg hAlg hw hsm hcmp hcod hlin k Y p D D' P P'


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IndependenceOfEmbeddingHypotheses
section

open CategoryTheory AlgebraicGeometry

section

theorem locallyConstCodimImpliesConstantCodim : LocallyConstCodimImpliesConstantCodim.{u} := by
  intro k _ X X' q _ τ _ c h
  exact hasEtaleCoordCodim_of_locally_smooth_over_affineSpace q τ c h

theorem linearEmbeddingsHaveLocallyConstCodim_of_affineSpaceIsSmooth (hsm : AffineSpaceIsSmooth.{u}) :
    LinearEmbeddingsHaveLocallyConstCodim.{u} := by
  intro k _ n m
  exact ⟨hasSmoothCoordCodim_affineSpaceInl hsm k n m, hasSmoothCoordCodim_affineSpaceInrEmbedding hsm k n m⟩

theorem isIndependentOfPresentedEmbedding_embeddedResolutionRule (Alg : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization Alg) (hw : TransitionsAreBlowupsForEmbeddings Alg) (hsm : AffineSpaceIsSmooth.{u})
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) :
    (embeddedResolutionRuleOfPrincipalization Alg hw).IsIndependentOfPresentedEmbedding :=
  isIndependentOfPresentedEmbedding_of_locallyConstCodim Alg hAlg hw hsm hcmp
    locallyConstCodimImpliesConstantCodim (linearEmbeddingsHaveLocallyConstCodim_of_affineSpaceIsSmooth hsm)


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.CentersLieOverSingularLocus
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

section

namespace AffineSpacePrincipalizationData

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)

def CentersLieOverSingularLocus : Prop :=
  ∀ i, i < S.ambientLength → ∀ p : ↥(S.strictTransform i),
    p ∈ (((S.centerOffDetached i).support : TopologicalSpace.Closeds ↥(S.strictTransform i)) :
        Set ↥(S.strictTransform i)) →
      (S.strictTransformToZero i ≫ S.strictTransformZeroToBase).base p ∈
        ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y)

def totalSpaceToBase (j : ℕ) : S.totalSpace j ⟶ Y :=
  Nat.rec (motive := fun j => S.totalSpace j ⟶ Y) S.totalSpaceZeroIso.hom
    (fun j ih => S.transitionMap j ≫ ih) j

@[simp] theorem totalSpaceToBase_succ (j : ℕ) :
    S.totalSpaceToBase (j + 1) = S.transitionMap j ≫ S.totalSpaceToBase j := rfl

theorem totalSpaceToBase_eq_blowupSequence_projectionToBase (h : S.TransitionsAreBlowups) (j : ℕ) :
    S.totalSpaceToBase j = (S.blowupSequence h).projectionToBase j := by
  induction j with
  | zero =>
      show S.totalSpaceZeroIso.hom = (S.blowupSequence h).projectionToBase 0
      rw [(S.blowupSequence h).projectionToBase_zero]
      rfl
  | succ j ih =>
      have hb : (S.blowupSequence h).transitionMapSucc j = S.transitionMap j := S.tower_map_succ j
      rw [totalSpaceToBase_succ, ih, (S.blowupSequence h).projectionToBase_succ, hb]
      rfl

theorem inl_comp_totalSpaceToBase (j : ℕ) :
    (coprod.inl : S.strictTransform j ⟶ S.totalSpace j) ≫ S.totalSpaceToBase j =
      S.strictTransformToZero j ≫ S.strictTransformZeroToBase := by
  induction j with
  | zero =>
      show (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom
          = 𝟙 (S.strictTransform 0) ≫ S.strictTransformZeroToBase
      rw [Category.id_comp, strictTransformZeroToBase_def]
  | succ j ih =>
      rw [totalSpaceToBase_succ, ← Category.assoc, S.inl_comp_transitionMap j, Category.assoc, ih,
        strictTransformToZero_succ, Category.assoc]

theorem centersLieOverSingularLocus_of_inducedCentersLieOverSingularLocus (h : S.TransitionsAreBlowups)
    (hc : S.InducedCentersLieOverSingularLocus h) : S.CentersLieOverSingularLocus := by
  intro i hi p hp
  have : QuasiCompact (S.centerOffDetached i).subschemeι := inferInstance
  have : QuasiCompact
      ((S.centerOffDetached i).subschemeι ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) :=
    inferInstance
  have hcomap : (S.centerOnTotalSpace i).comap (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)
      = S.centerOffDetached i := by
    have hk := Blowup.ker_comp_coprod_inl_comap_inl (Y := S.discardedUnion i) (S.centerOffDetached i).subschemeι
    rw [Scheme.IdealSheafData.ker_subschemeι] at hk
    exact hk
  have hp2 : p ∈ ((S.centerOnTotalSpace i).comap
      (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)).support := by
    rw [hcomap]
    exact hp
  have hp3 : (coprod.inl : S.strictTransform i ⟶ S.totalSpace i).base p
      ∈ (S.centerOnTotalSpace i).support :=
    AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.mp hp2
  have hmem := hc i hi _ hp3
  have e : (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ (S.blowupSequence h).projectionToBase i
      = S.strictTransformToZero i ≫ S.strictTransformZeroToBase := by
    rw [← S.totalSpaceToBase_eq_blowupSequence_projectionToBase h i]
    exact S.inl_comp_totalSpaceToBase i
  have key : ((S.blowupSequence h).projectionToBase i).base
      ((coprod.inl : S.strictTransform i ⟶ S.totalSpace i).base p)
      = (S.strictTransformToZero i ≫ S.strictTransformZeroToBase).base p :=
    congrArg (fun g : S.strictTransform i ⟶ Y => g.base p) e
  rw [← key]
  exact hmem

end AffineSpacePrincipalizationData


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.GenericPointsAvoidCenter
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section

theorem nonempty_inter_of_dense_of_mem_irreducibleComponents
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X]
    {V : Set X} (hV : Dense V) {C : Set X} (hC : C ∈ irreducibleComponents X) :
    (C ∩ V).Nonempty := by
  classical
  have hfin : (irreducibleComponents X).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hfin' : (irreducibleComponents X \ {C}).Finite := hfin.subset (fun _ h => h.1)
  have hCirr : IsIrreducible C := hC.1
  have hFclosed : IsClosed (⋃₀ (irreducibleComponents X \ {C})) := by
    rw [Set.sUnion_eq_biUnion]
    exact hfin'.isClosed_biUnion fun C' hC' => isClosed_of_mem_irreducibleComponents _ hC'.1
  have hnotsub : ¬ C ⊆ ⋃₀ (irreducibleComponents X \ {C}) := by
    intro hsub
    have hsub' : C ⊆ ⋃₀ (↑hfin'.toFinset : Set (Set X)) := by
      rwa [Set.Finite.coe_toFinset]
    obtain ⟨z, hz, hCz⟩ := isIrreducible_iff_sUnion_isClosed.mp hCirr hfin'.toFinset
      (fun z hz => isClosed_of_mem_irreducibleComponents _ (hfin'.mem_toFinset.mp hz).1) hsub'
    have hz' : z ∈ irreducibleComponents X \ {C} := hfin'.mem_toFinset.mp hz
    have hzC : z ⊆ C := hC.2 hz'.1.1 hCz
    exact hz'.2 (Set.mem_singleton_iff.mpr (Set.Subset.antisymm hzC hCz))
  obtain ⟨x, hxC, hxF⟩ := Set.not_subset.mp hnotsub
  have hUsub : (⋃₀ (irreducibleComponents X \ {C}))ᶜ ⊆ C := by
    intro y hy
    by_contra hyC
    have hne : irreducibleComponent y ≠ C := by
      intro h
      apply hyC
      rw [← h]
      exact mem_irreducibleComponent
    have hmem : irreducibleComponent y ∈ irreducibleComponents X \ {C} :=
      ⟨irreducibleComponent_mem_irreducibleComponents y,
        fun hmm => hne (Set.mem_singleton_iff.mp hmm)⟩
    exact hy (Set.mem_sUnion.mpr ⟨irreducibleComponent y, hmem, mem_irreducibleComponent⟩)
  obtain ⟨y, hyU, hyV⟩ := mem_closure_iff.mp (hV x) _ hFclosed.isOpen_compl hxF
  exact ⟨y, hUsub hyU, hyV⟩

namespace EmbeddedBlowupSequence

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]

variable (S : EmbeddedBlowupSequence k Y pY)

theorem isClosedEmbedding_strictTransformι (i : ℕ) :
    Topology.IsClosedEmbedding ⇑(S.strictTransformι i).base := by
  have hrange : Set.range ⇑(S.strictTransformι i).base
      = ((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) :=
    AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι ..
  refine ⟨(S.strictTransformι i).isEmbedding, ?_⟩
  rw [hrange]
  exact (S.strictTransformIdeal i).support.2

theorem noetherianSpace_strictTransform_of_isNoetherian
    (hN : ∀ j ≤ S.length, IsNoetherian (S.schemeAt j)) (i : ℕ) (hi : i ≤ S.length) :
    TopologicalSpace.NoetherianSpace ↥(S.strictTransform i) := by
  have := hN i hi
  exact S.noetherianSpace_strictTransform_of_noetherianSpace_schemeAt i inferInstance

theorem notMem_ambientCenter_support_of_isGenericPoint (i : ℕ) (C : Set ↥(S.strictTransform i))
    (hC : C ∈ irreducibleComponents ↥(S.strictTransform i)) (hfr : C ∉ S.detachedComponents i)
    (η : ↥(S.strictTransform i)) (hη : IsGenericPoint η C) :
    (S.strictTransformι i).base η ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
  intro hmem
  have hηe : closure ({η} : Set ↥(S.strictTransform i)) = C := hη
  have hclosed : IsClosed
      (⇑(S.strictTransformι i).base ⁻¹' ((S.ambientCenter i).support : Set ↥(S.schemeAt i))) :=
    IsClosed.preimage (S.strictTransformι i).base.hom.continuous ((S.ambientCenter i).support).2
  have hmem' : η ∈ ⇑(S.strictTransformι i).base ⁻¹' ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) :=
    hmem
  have hsub : C ⊆ ⇑(S.strictTransformι i).base ⁻¹' ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
    rw [← hηe]
    exact hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem')
  exact hfr ((S.mem_detachedComponents i C).mpr ⟨hC, Set.image_subset_iff.mpr hsub⟩)

theorem range_strictTransformι_succ [IsReduced Y]
    (hN : ∀ j ≤ S.length, IsNoetherian (S.schemeAt j)) (i : ℕ) (hi : i < S.length) :
    Set.range ⇑(S.strictTransformι (i + 1)).base =
      closure (⇑(S.blowdown i).base ⁻¹'
        (((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) \
          ((S.ambientCenter i).support : Set ↥(S.schemeAt i)))) := by
  have hNi : IsNoetherian (S.schemeAt (i + 1)) := hN (i + 1) hi
  have hns : TopologicalSpace.NoetherianSpace ↥(S.schemeAt (i + 1)) := inferInstance
  have hqc := S.quasiCompact_strictTransformι_blowdown i hns
  have h1 : Set.range ⇑(S.strictTransformι (i + 1)).base
      = ((S.strictTransformIdeal (i + 1)).support : Set ↥(S.schemeAt (i + 1))) :=
    AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι ..
  rw [h1]
  exact support_strictTransform_eq_closure_preimage (S.blowdown i) (S.ambientCenter i) (S.strictTransformIdeal i)

abbrev ambientCenterSupportCompl (i : ℕ) : (S.schemeAt i).Opens := (S.ambientCenter i).support.compl

section
variable (i : ℕ)

@[simp] theorem mem_ambientCenterSupportCompl (x : ↥(S.schemeAt i)) :
    x ∈ S.ambientCenterSupportCompl i ↔ x ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := Iff.rfl

theorem isIso_blowdown_restrict_ambientCenterSupportCompl (hi : i < S.length) :
    CategoryTheory.IsIso (S.blowdown i ∣_ S.ambientCenterSupportCompl i) := by
  have h : Blowup.IsBlowupAlongIdealSheaf (S.blowdown i) (S.ambientCenter i) :=
    S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism i hi
  have h1 := h.restrict (S.ambientCenter i).support.compl
  rw [Blowup.comap_ι_support_compl_eq_top (S.ambientCenter i)] at h1
  exact h1.isIso_of_top


end

def strictTransformOffCenter (i : ℕ) : (S.strictTransform i).Opens :=
  (TopologicalSpace.Opens.map (S.strictTransformι i).base).obj (S.ambientCenterSupportCompl i)

abbrev strictTransformMapPreimageOffCenter (i : ℕ) : (S.strictTransform (i + 1)).Opens :=
  (TopologicalSpace.Opens.map (S.strictTransformMap i).base).obj (S.strictTransformOffCenter i)

theorem mem_strictTransformMapPreimageOffCenter (i : ℕ) (x : ↥(S.strictTransform (i + 1))) :
    x ∈ S.strictTransformMapPreimageOffCenter i ↔
      (S.strictTransformι i).base ((S.strictTransformMap i).base x) ∉
        ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := Iff.rfl

theorem exists_irreducibleComponent_isGenericPoint_strictTransformMap [IsReduced Y]
    (hN : ∀ j ≤ S.length, IsNoetherian (S.schemeAt j)) (i : ℕ) (hi : i < S.length)
    (C : Set ↥(S.strictTransform (i + 1))) (hC : C ∈ irreducibleComponents ↥(S.strictTransform (i + 1)))
    (η : ↥(S.strictTransform (i + 1))) (hη : IsGenericPoint η C) :
    ∃ C' : Set ↥(S.strictTransform i), C' ∈ irreducibleComponents ↥(S.strictTransform i) ∧
      IsGenericPoint ((S.strictTransformMap i).base η) C' ∧ C' ∉ S.detachedComponents i := by
  classical
  have hns1 : TopologicalSpace.NoetherianSpace ↥(S.strictTransform (i + 1)) :=
    S.noetherianSpace_strictTransform_of_isNoetherian hN (i + 1) hi
  have hisoG : CategoryTheory.IsIso (S.blowdown i ∣_ S.ambientCenterSupportCompl i) :=
    S.isIso_blowdown_restrict_ambientCenterSupportCompl i hi
  have hcont0 : Continuous ⇑(S.strictTransformι i).base := (S.strictTransformι i).base.hom.continuous
  have hcontf : Continuous ⇑(S.strictTransformMap i).base := (S.strictTransformMap i).base.hom.continuous
  have hcontι' : Continuous ⇑(Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base :=
    (Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base.hom.continuous
  have hcontginv : Continuous ⇑(CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base :=
    (CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base.hom.continuous
  have hcomm : ∀ x : ↥(S.strictTransform (i + 1)),
      (S.strictTransformι i).base ((S.strictTransformMap i).base x)
        = (S.blowdown i).base ((S.strictTransformι (i + 1)).base x) := by
    intro x
    have h2 : (S.strictTransformMap i ≫ S.strictTransformι i).base x
        = (S.strictTransformι (i + 1) ≫ S.blowdown i).base x := by
      rw [S.strictTransformMap_comp_strictTransformι i]
    exact h2
  have hrange0 : Set.range ⇑(S.strictTransformι i).base
      = ((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) :=
    AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι ..
  have hrange1 : Set.range ⇑(S.strictTransformι (i + 1)).base
      = closure (⇑(S.blowdown i).base ⁻¹'
        (((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) \
          ((S.ambientCenter i).support : Set ↥(S.schemeAt i)))) :=
    S.range_strictTransformι_succ hN i hi
  have hemb1 : Topology.IsClosedEmbedding ⇑(S.strictTransformι (i + 1)).base :=
    S.isClosedEmbedding_strictTransformι (i + 1)
  have hemb0 : Topology.IsClosedEmbedding ⇑(S.strictTransformι i).base := S.isClosedEmbedding_strictTransformι i
  have hrU : Set.range ⇑(Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base
      = ((S.ambientCenterSupportCompl i : (S.schemeAt i).Opens) : Set ↥(S.schemeAt i)) := by
    rw [Scheme.Opens.range_ι]
  have hrU' : Set.range ⇑(Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base
      = ((S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i : (S.schemeAt (i + 1)).Opens) :
          Set ↥(S.schemeAt (i + 1))) := by
    rw [Scheme.Opens.range_ι]
  have hιinj : Function.Injective ⇑(Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base :=
    (Scheme.Opens.ι (S.ambientCenterSupportCompl i)).isEmbedding.injective
  have hιopen : IsOpenMap ⇑(Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base := by
    refine (Scheme.Opens.ι (S.ambientCenterSupportCompl i)).isEmbedding.toIsInducing.isOpenMap ?_
    rw [hrU]
    exact (S.ambientCenterSupportCompl i).2
  have hgcomm : ∀ x : ↥((S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i).toScheme),
      (Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base
          ((S.blowdown i ∣_ S.ambientCenterSupportCompl i).base x)
        = (S.blowdown i).base
          ((Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base x) := by
    intro x
    have h2 : ((S.blowdown i ∣_ S.ambientCenterSupportCompl i) ≫
          Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base x
        = (Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i) ≫ S.blowdown i).base x := by
      rw [morphismRestrict_ι]
    exact h2
  have hggi : ∀ y : ↥((S.ambientCenterSupportCompl i).toScheme),
      (S.blowdown i ∣_ S.ambientCenterSupportCompl i).base
          ((CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base y) = y := by
    intro y
    have h2 : (CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i) ≫
        (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base y = y := by
      rw [CategoryTheory.IsIso.inv_hom_id]
      simp
    exact h2
  have hgig : ∀ x : ↥((S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i).toScheme),
      (CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base
          ((S.blowdown i ∣_ S.ambientCenterSupportCompl i).base x) = x := by
    intro x
    have h2 : ((S.blowdown i ∣_ S.ambientCenterSupportCompl i) ≫
        CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base x = x := by
      rw [CategoryTheory.IsIso.hom_inv_id]
      simp
    exact h2
  have hLift : ∀ c : ↥(S.schemeAt i),
      c ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) →
      ∃ c' : ↥(S.schemeAt (i + 1)), (S.blowdown i).base c' = c := by
    intro c hc
    have hcU : c ∈ Set.range ⇑(Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base := by
      rw [hrU]
      exact hc
    obtain ⟨y, hy⟩ := hcU
    refine ⟨(Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base
      ((CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base y), ?_⟩
    rw [← hgcomm, hggi, hy]
  have hLiftNext : ∀ c' e' : ↥(S.schemeAt (i + 1)),
      (S.blowdown i).base c' ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) →
      (S.blowdown i).base e' ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) →
      (S.blowdown i).base e'
          ∈ closure ({(S.blowdown i).base c'} : Set ↥(S.schemeAt i)) →
      e' ∈ closure ({c'} : Set ↥(S.schemeAt (i + 1))) := by
    intro c' e' hc' he' hsp
    have hc'' : c' ∈ Set.range ⇑(Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base := by
      rw [hrU']
      exact hc'
    have he'' : e' ∈ Set.range ⇑(Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base := by
      rw [hrU']
      exact he'
    obtain ⟨x, hx⟩ := hc''
    obtain ⟨w, hw⟩ := he''
    have hsp2 : (Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base
          ((S.blowdown i ∣_ S.ambientCenterSupportCompl i).base w)
        ∈ closure ({(Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base
          ((S.blowdown i ∣_ S.ambientCenterSupportCompl i).base x)} : Set ↥(S.schemeAt i)) := by
      rw [hgcomm w, hgcomm x, hx, hw]
      exact hsp
    have hsp3 := IsOpenMap.mem_closure_singleton_of_apply hιopen hιinj hsp2
    have hsp4 := specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr hsp3).map hcontginv)
    rw [hgig w, hgig x] at hsp4
    have hsp5 := specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr hsp4).map hcontι')
    rw [hx, hw] at hsp5
    exact hsp5
  have hWsub : (⇑(S.blowdown i).base ⁻¹'
        (((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) \
          ((S.ambientCenter i).support : Set ↥(S.schemeAt i))))
      ⊆ ⇑(S.strictTransformι (i + 1)).base ''
        (↑(S.strictTransformMapPreimageOffCenter i) : Set ↥(S.strictTransform (i + 1))) := by
    intro w hw
    have hwr : w ∈ Set.range ⇑(S.strictTransformι (i + 1)).base := by
      rw [hrange1]
      exact subset_closure hw
    obtain ⟨a, ha⟩ := hwr
    refine ⟨a, ?_, ha⟩
    refine (S.mem_strictTransformMapPreimageOffCenter i a).mpr ?_
    rw [hcomm a, ha]
    exact hw.2
  have hVdense : Dense (↑(S.strictTransformMapPreimageOffCenter i) : Set ↥(S.strictTransform (i + 1))) := by
    intro x
    have h2 := closure_mono hWsub
    rw [← hrange1] at h2
    have h3 := h2 (Set.mem_range_self x)
    rw [hemb1.closure_image_eq] at h3
    obtain ⟨y, hy, hyx⟩ := h3
    rwa [hemb1.injective hyx] at hy
  have hηZ : (S.strictTransformι i).base ((S.strictTransformMap i).base η)
      ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
    obtain ⟨y, hyC, hyV⟩ :=
      nonempty_inter_of_dense_of_mem_irreducibleComponents hVdense hC
    have hyc : y ∈ closure ({η} : Set ↥(S.strictTransform (i + 1))) := by
      rw [hη]
      exact hyC
    obtain ⟨z, hzV, hzη⟩ :=
      (mem_closure_iff.mp hyc) (↑(S.strictTransformMapPreimageOffCenter i) : Set ↥(S.strictTransform (i + 1)))
        (S.strictTransformMapPreimageOffCenter i).2 hyV
    rw [Set.mem_singleton_iff] at hzη
    rw [hzη] at hzV
    exact (S.mem_strictTransformMapPreimageOffCenter i η).mp hzV
  have hExistsPreimage : ∀ ξ : ↥(S.strictTransform i),
      (S.strictTransformMap i).base η ∈ closure ({ξ} : Set ↥(S.strictTransform i)) →
      ∃ z : ↥(S.strictTransform (i + 1)), (S.strictTransformMap i).base z = ξ ∧
        η ∈ closure ({z} : Set ↥(S.strictTransform (i + 1))) := by
    intro ξ hmem
    have h1 : (S.strictTransformι i).base ((S.strictTransformMap i).base η)
        ∈ closure ({(S.strictTransformι i).base ξ} : Set ↥(S.schemeAt i)) :=
      specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hmem).map hcont0)
    have hξZ : (S.strictTransformι i).base ξ ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
      obtain ⟨t, htc, hts⟩ := (mem_closure_iff.mp h1)
        (((S.ambientCenter i).support : Set ↥(S.schemeAt i))ᶜ)
        ((S.ambientCenter i).support.2).isOpen_compl hηZ
      rw [Set.mem_singleton_iff] at hts
      rwa [hts] at htc
    obtain ⟨c', hc'⟩ := hLift ((S.strictTransformι i).base ξ) hξZ
    have hc'W : c' ∈ ⇑(S.blowdown i).base ⁻¹'
        (((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) \
          ((S.ambientCenter i).support : Set ↥(S.schemeAt i))) := by
      have h5 : (S.blowdown i).base c' ∈ (((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) \
          ((S.ambientCenter i).support : Set ↥(S.schemeAt i))) := by
        rw [hc']
        refine ⟨?_, hξZ⟩
        rw [← hrange0]
        exact Set.mem_range_self ξ
      exact h5
    have hc'r : c' ∈ Set.range ⇑(S.strictTransformι (i + 1)).base := by
      rw [hrange1]
      exact subset_closure hc'W
    obtain ⟨z, hz⟩ := hc'r
    have hfz : (S.strictTransformMap i).base z = ξ := by
      apply hemb0.injective
      rw [hcomm z, hz, hc']
    refine ⟨z, hfz, ?_⟩
    have hspec : (S.blowdown i).base ((S.strictTransformι (i + 1)).base η)
        ∈ closure ({(S.blowdown i).base c'} : Set ↥(S.schemeAt i)) := by
      rw [hc', ← hcomm η]
      exact h1
    have hstep := hLiftNext c' ((S.strictTransformι (i + 1)).base η) (by rw [hc']; exact hξZ)
      (by rw [← hcomm η]; exact hηZ) hspec
    rw [← hz] at hstep
    exact specializes_iff_mem_closure.mp
      (hemb1.isInducing.specializes_iff.mp (specializes_iff_mem_closure.mpr hstep))
  have hmemComp : closure ({(S.strictTransformMap i).base η} : Set ↥(S.strictTransform i))
      ∈ irreducibleComponents ↥(S.strictTransform i) := by
    refine ⟨isIrreducible_singleton.closure, ?_⟩
    intro D hD hsub
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober hD.closure isClosed_closure
    have hξ0 : (S.strictTransformMap i).base η ∈ closure ({ξ} : Set ↥(S.strictTransform i)) := by
      rw [hξ]
      exact subset_closure (hsub (subset_closure rfl))
    obtain ⟨z, hfz, hηz⟩ := hExistsPreimage ξ hξ0
    have hCz : C ⊆ closure ({z} : Set ↥(S.strictTransform (i + 1))) := by
      rw [← hη]
      exact closure_minimal (Set.singleton_subset_iff.mpr hηz) isClosed_closure
    have hzC : closure ({z} : Set ↥(S.strictTransform (i + 1))) ⊆ C :=
      hC.2 isIrreducible_singleton.closure hCz
    have hzη : z ∈ closure ({η} : Set ↥(S.strictTransform (i + 1))) := by
      rw [hη]
      exact hzC (subset_closure rfl)
    have hξmem : ξ ∈ closure ({(S.strictTransformMap i).base η} : Set ↥(S.strictTransform i)) := by
      have hmap := specializes_iff_mem_closure.mp
        ((specializes_iff_mem_closure.mpr hzη).map hcontf)
      rwa [hfz] at hmap
    intro d hd
    have hd' : d ∈ closure ({ξ} : Set ↥(S.strictTransform i)) := by
      rw [hξ]
      exact subset_closure hd
    exact closure_minimal (Set.singleton_subset_iff.mpr hξmem) isClosed_closure hd'
  have hnotfr : closure ({(S.strictTransformMap i).base η} : Set ↥(S.strictTransform i))
      ∉ S.detachedComponents i := by
    intro hfr
    have h2 := ((S.mem_detachedComponents i _).mp hfr).2
    exact hηZ (h2 ⟨(S.strictTransformMap i).base η, subset_closure rfl, rfl⟩)
  exact ⟨closure ({(S.strictTransformMap i).base η} : Set ↥(S.strictTransform i)), hmemComp, rfl, hnotfr⟩

end EmbeddedBlowupSequence


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineBoundaryStrictNormalCrossings
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

section

section
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY)

private theorem centersHaveStrictNormalCrossingsWithBoundary_consolidated308 :
    S.CentersHaveStrictNormalCrossingsWithBoundary := fun i hi => S.principalizationSequence.center_snc i hi

private theorem smooth_schemeAtToSpec_consolidated308 :
    ∀ i, i ≤ S.ambientLength → Smooth (S.schemeAtToSpec i) := by
  intro i
  induction i with
  | zero =>
      intro _
      have : Smooth S.ambientToSpec := S.ambient_smooth
      rw [AffineSpacePrincipalizationData.schemeAtToSpec_def, SequenceOfBlowups.projectionToBase_zero]
      infer_instance
  | succ n ih =>
      intro hn
      have hlt : n < S.ambientLength := hn
      have hsm0 : Smooth (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) :=
        ih (Nat.le_of_lt hlt)
      have hZE : HasStrictNormalCrossingsWith (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) (S.ambientBlowups.center n)
          (S.principalizationSequence.boundary n) := S.principalizationSequence.center_snc n hlt
      have hb : Blowup.IsBlowupAlongIdealSheaf (S.ambientBlowups.transitionMapSucc n) (S.ambientBlowups.center n) :=
        S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt
      have hres := smooth_comp_of_isBlowupAlongIdealSheaf hZE hb
      rw [AffineSpacePrincipalizationData.schemeAtToSpec_def, SequenceOfBlowups.projectionToBase_succ, Category.assoc]
      exact hres

private theorem boundaryInStrictNormalCrossingPosition_consolidated308 :
    S.BoundaryInStrictNormalCrossingPosition := by
  intro i
  induction i with
  | zero =>
      intro _
      have : Smooth (S.schemeAtToSpec 0) :=
        smooth_schemeAtToSpec_consolidated308 S 0 (Nat.zero_le _)
      have h0 : S.boundary 0 = ([] : List (S.ambientLevel 0).IdealSheafData) := by
        rw [AffineSpacePrincipalizationData.boundary_def, IdealBlowupSequence.boundary_zero]
        rfl
      rw [h0]
      exact inStrictNormalCrossingPosition_nil (S.schemeAtToSpec 0)
  | succ n ih =>
      intro hn
      have hlt : n < S.ambientLength := hn
      have : IsNoetherian (S.ambientLevel (n + 1)) :=
        isNoetherian_ambientLevel S (n + 1) hn
      have : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel (n + 1)) := inferInstance
      have hE : InStrictNormalCrossingPosition (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec)
          (S.principalizationSequence.boundary n) := ih (Nat.le_of_lt hlt)
      have hZE : HasStrictNormalCrossingsWith (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) (S.ambientBlowups.center n)
          (S.principalizationSequence.boundary n) := S.principalizationSequence.center_snc n hlt
      have hb : Blowup.IsBlowupAlongIdealSheaf (S.ambientBlowups.transitionMapSucc n) (S.ambientBlowups.center n) :=
        S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt
      have hres := inStrictNormalCrossingPosition_strictTransform_append
        (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) (S.ambientBlowups.transitionMapSucc n)
        (S.ambientBlowups.center n) (S.principalizationSequence.boundary n) hb hE hZE
      rw [AffineSpacePrincipalizationData.schemeAtToSpec_def, SequenceOfBlowups.projectionToBase_succ, Category.assoc,
        AffineSpacePrincipalizationData.boundary_def, S.principalizationSequence.boundary_succ n hlt]
      exact hres


end

section
variable (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})

theorem affineCentersHaveStrictNormalCrossingsWithBoundary :
    AffineCentersHaveStrictNormalCrossingsWithBoundary A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact centersHaveStrictNormalCrossingsWithBoundary_consolidated308 (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)

theorem affineAllLevelsSmooth :
    AffineAllLevelsSmooth A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact smooth_schemeAtToSpec_consolidated308 (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)

theorem affineBoundaryInStrictNormalCrossingPosition :
    AffineBoundaryInStrictNormalCrossingPosition A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact boundaryInStrictNormalCrossingPosition_consolidated308 (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.InvarianceUnderIsomorphism
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section

private theorem isIso_resLE_of_iso_consolidated247 {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens) :
    IsIso (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

def preimageOpensIso {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens) :
    Scheme.Opens.toScheme ((Opens.map e.hom.base).obj U) ≅ Scheme.Opens.toScheme U :=
  letI := isIso_resLE_of_iso_consolidated247 e U
  asIso (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl)

@[simp]
theorem preimageOpensIso_hom {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens) :
    (preimageOpensIso e U).hom = e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl :=
  rfl

def OrderCertificateIsoInvariantOfMaxContact : Prop :=
  ∀ (k : Type u) [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))
      (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W) (Z : W.IdealSheafData)
      (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
      (_hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
      (H : ∀ (z : ↥W) (hz : z ∈ Z.support), (U z hz).toScheme.IdealSheafData)
      (_hH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        IsSmoothDivisor ((U z hz).ι ≫ p) (H z hz))
      (_hNsubH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        ((N.comap (U z hz).ι).support : Set ↥(U z hz).toScheme) ⊆
          ((H z hz).support : Set ↥(U z hz).toScheme))
      (_hZH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        ((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme) ⊆
          ((H z hz).support : Set ↥(U z hz).toScheme))
      (J : ∀ (z : ↥W) (hz : z ∈ Z.support), Option (H z hz).subscheme.IdealSheafData)
      (_hJnone : ∀ (z : ↥W) (hz : z ∈ Z.support), J z hz = Option.none →
        IsOpen (⇑(H z hz).subschemeι.base ⁻¹'
          ((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)))
      (_hJcomp : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = Option.some Jz → NonzeroOnComponents Jz)
      (_hJloc : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = Option.some Jz →
          ∀ x : ↥(H z hz).subscheme,
            ((H z hz).subschemeι ≫ (U z hz).ι).base x ∉ Mem →
              ∃ V : (H z hz).subscheme.Opens, x ∈ V ∧
                Jz.comap V.ι = ((N.comap (U z hz).ι).comap (H z hz).subschemeι).comap V.ι)
      (_hJcert : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = Option.some Jz →
          PrincipalizationCertificate (H z hz).subscheme ((H z hz).subschemeι ≫ (U z hz).ι ≫ p) Jz μ
            (⇑((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
            ((Z.comap (U z hz).ι).comap (H z hz).subschemeι))
      (_hJtrans : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = Option.some Jz →
          ∀ (X : Scheme.{u}) (f : X ≅ (H z hz).subscheme),
            PrincipalizationCertificate X (f.hom ≫ (H z hz).subschemeι ≫ (U z hz).ι ≫ p) (Jz.comap f.hom) μ
              (⇑f.hom.base ⁻¹' (⇑((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem))
              (((Z.comap (U z hz).ι).comap (H z hz).subschemeι).comap f.hom))
      (W' : Scheme.{u}) (e : W' ≅ W),
    OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom)

private theorem coe_support_comap_iso_hom_consolidated247 {X Y : Scheme.{u}} (e : X ≅ Y) (Z : Y.IdealSheafData) :
    ((Z.comap e.hom).support : Set ↥X) = ⇑e.hom.base ⁻¹' (Z.support : Set ↥Y) := by
  ext x
  simp

private theorem preimage_comp_base_consolidated247 {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (S : Set ↥C) :
    ⇑f.base ⁻¹' (⇑g.base ⁻¹' S) = ⇑(f ≫ g).base ⁻¹' S := by
  ext x
  simp

private theorem preimageOpensIso_hom_comp_ι_consolidated247 {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens) :
    (preimageOpensIso e U).hom ≫ U.ι = Scheme.Opens.ι ((Opens.map e.hom.base).obj U) ≫ e.hom := by
  rw [preimageOpensIso_hom, Scheme.Hom.resLE_comp_ι]

private theorem preimageOpensIso_hom_comp_ι_comp_consolidated247 {k : Type u} [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) (U : Y.Opens) :
    (preimageOpensIso e U).hom ≫ (U.ι ≫ q) =
      Scheme.Opens.ι ((Opens.map e.hom.base).obj U) ≫ (e.hom ≫ q) := by
  rw [← Category.assoc, preimageOpensIso_hom_comp_ι_consolidated247, Category.assoc]

section
variable {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens)

private theorem comap_preimageOpensIso_hom_consolidated247 (I : Y.IdealSheafData) :
    (I.comap U.ι).comap (preimageOpensIso e U).hom =
      (I.comap e.hom).comap (Scheme.Opens.ι ((Opens.map e.hom.base).obj U)) := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, preimageOpensIso_hom_comp_ι_consolidated247]

private theorem preimage_preimageOpensIso_hom_consolidated247 (Mem : Set ↥Y) :
    ⇑(preimageOpensIso e U).hom.base ⁻¹' (⇑U.ι.base ⁻¹' Mem) =
      ⇑(Scheme.Opens.ι ((Opens.map e.hom.base).obj U)).base ⁻¹' (⇑e.hom.base ⁻¹' Mem) := by
  rw [preimage_comp_base_consolidated247, preimage_comp_base_consolidated247, preimageOpensIso_hom_comp_ι_consolidated247]


end

section
variable {k : Type u} [Field k] {W : Scheme.{u}} {p p' : W ⟶ Spec (CommRingCat.of k)}

private theorem principalizationCertificate_congr_consolidated247 {I I' : W.IdealSheafData} {m : ℕ}
    {Mem Mem' : Set ↥W} {Z Z' : W.IdealSheafData} (hp : p = p') (hI : I = I')
    (hMem : Mem = Mem') (hZ : Z = Z') (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W p' I' m Mem' Z' := by
  subst hp hI hMem hZ
  exact h

private theorem orderCertificate_congr_consolidated247 {N N' : W.IdealSheafData} {μ : ℕ}
    {Mem Mem' : Set ↥W} {Z Z' : W.IdealSheafData} (hp : p = p') (hN : N = N')
    (hMem : Mem = Mem') (hZ : Z = Z') (h : OrderCertificate W p N μ Mem Z) :
    OrderCertificate W p' N' μ Mem' Z' := by
  subst hp hN hMem hZ
  exact h


end

section
variable {k : Type u} [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k)) (I : W.IdealSheafData) (m : ℕ) (Mem : Set ↥W) (Z : W.IdealSheafData)

private theorem principalizationCertificate_comap_iso_of_support_subset_consolidated247 (h : (Z.support : Set ↥W) ⊆ Mem) (W' : Scheme.{u}) (e : W' ≅ W) :
    PrincipalizationCertificate W' (e.hom ≫ p) (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) := by
  refine PrincipalizationCertificate.memory ?_
  rw [coe_support_comap_iso_hom_consolidated247 e Z]
  exact Set.preimage_mono h

private theorem principalizationCertificate_comap_iso_of_two_le_consolidated247 (hm : 2 ≤ m) (W' : Scheme.{u}) (e : W' ≅ W) :
    PrincipalizationCertificate W' (e.hom ≫ p) (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  PrincipalizationCertificate.large hm

private theorem principalizationCertificate_comap_iso_of_orderCertificate_consolidated247 (M N : W.IdealSheafData) (μ : ℕ) (hI : I = M * N)
    (hM : (M.support : Set ↥W) ⊆ Mem) (hmu : m ≤ μ)
    (hZ : (Z.support : Set ↥W) ⊆ orderAtLeastLocus N μ) (_hcert : OrderCertificate W p N μ Mem Z)
    (ih : ∀ (W' : Scheme.{u}) (e : W' ≅ W),
      OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom))
    (W' : Scheme.{u}) (e : W' ≅ W) :
    PrincipalizationCertificate W' (e.hom ≫ p) (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) := by
  refine PrincipalizationCertificate.toOrder (M.comap e.hom) (N.comap e.hom) μ ?_ ?_ hmu ?_ (ih W' e)
  · rw [hI, Scheme.IdealSheafData.comap_mul]
  · rw [coe_support_comap_iso_hom_consolidated247 e M]
    exact Set.preimage_mono hM
  · rw [coe_support_comap_iso_hom_consolidated247 e Z, orderAtLeastLocus_comap_iso_hom_eq_preimage e N μ]
    exact Set.preimage_mono hZ

private theorem principalizationCertificate_comap_iso_of_opens_cover_consolidated247 (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (_hcert : ∀ (z : ↥W) (hz : z ∈ Z.support),
      PrincipalizationCertificate (U z hz).toScheme ((U z hz).ι ≫ p) (I.comap (U z hz).ι) m
        (⇑(U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι))
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support) (X : Scheme.{u}) (f : X ≅ (U z hz).toScheme),
      PrincipalizationCertificate X (f.hom ≫ ((U z hz).ι ≫ p)) ((I.comap (U z hz).ι).comap f.hom) m
        (⇑f.hom.base ⁻¹' (⇑(U z hz).ι.base ⁻¹' Mem)) ((Z.comap (U z hz).ι).comap f.hom))
    (W' : Scheme.{u}) (e : W' ≅ W) :
    PrincipalizationCertificate W' (e.hom ≫ p) (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) := by
  refine PrincipalizationCertificate.localize
    (fun z' hz' =>
      (Opens.map e.hom.base).obj
        (U (e.hom.base z') (by rwa [Scheme.IdealSheafData.mem_support_comap] at hz')))
    (fun z' hz' => ?_) ?_
  · exact hU (e.hom.base z') (by rwa [Scheme.IdealSheafData.mem_support_comap] at hz')
  · intro z' hz'
    have hz : e.hom.base z' ∈ Z.support := by
      rwa [Scheme.IdealSheafData.mem_support_comap] at hz'
    exact principalizationCertificate_congr_consolidated247 (preimageOpensIso_hom_comp_ι_comp_consolidated247 p e (U (e.hom.base z') hz))
      (comap_preimageOpensIso_hom_consolidated247 e (U (e.hom.base z') hz) I)
      (preimage_preimageOpensIso_hom_consolidated247 e (U (e.hom.base z') hz) Mem)
      (comap_preimageOpensIso_hom_consolidated247 e (U (e.hom.base z') hz) Z)
      (ih (e.hom.base z') hz _ (preimageOpensIso e (U (e.hom.base z') hz)))


end

section
variable {k : Type u} [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k)) (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W) (Z : W.IdealSheafData)

private theorem orderCertificate_comap_iso_of_support_subset_consolidated247 (h : (Z.support : Set ↥W) ⊆ Mem) (W' : Scheme.{u}) (e : W' ≅ W) :
    OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) := by
  refine OrderCertificate.memory ?_
  rw [coe_support_comap_iso_hom_consolidated247 e Z]
  exact Set.preimage_mono h

private theorem orderCertificate_comap_iso_of_two_le_consolidated247 (hmu : 2 ≤ μ) (W' : Scheme.{u}) (e : W' ≅ W) :
    OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  OrderCertificate.large hmu

private theorem orderCertificate_comap_iso_of_opens_cover_consolidated247 (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (_hcert : ∀ (z : ↥W) (hz : z ∈ Z.support),
      OrderCertificate (U z hz).toScheme ((U z hz).ι ≫ p) (N.comap (U z hz).ι) μ
        (⇑(U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι))
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support) (X : Scheme.{u}) (f : X ≅ (U z hz).toScheme),
      OrderCertificate X (f.hom ≫ ((U z hz).ι ≫ p)) ((N.comap (U z hz).ι).comap f.hom) μ
        (⇑f.hom.base ⁻¹' (⇑(U z hz).ι.base ⁻¹' Mem)) ((Z.comap (U z hz).ι).comap f.hom))
    (W' : Scheme.{u}) (e : W' ≅ W) :
    OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) := by
  refine OrderCertificate.localize
    (fun z' hz' =>
      (Opens.map e.hom.base).obj
        (U (e.hom.base z') (by rwa [Scheme.IdealSheafData.mem_support_comap] at hz')))
    (fun z' hz' => ?_) ?_
  · exact hU (e.hom.base z') (by rwa [Scheme.IdealSheafData.mem_support_comap] at hz')
  · intro z' hz'
    have hz : e.hom.base z' ∈ Z.support := by
      rwa [Scheme.IdealSheafData.mem_support_comap] at hz'
    exact orderCertificate_congr_consolidated247 (preimageOpensIso_hom_comp_ι_comp_consolidated247 p e (U (e.hom.base z') hz))
      (comap_preimageOpensIso_hom_consolidated247 e (U (e.hom.base z') hz) N)
      (preimage_preimageOpensIso_hom_consolidated247 e (U (e.hom.base z') hz) Mem)
      (comap_preimageOpensIso_hom_consolidated247 e (U (e.hom.base z') hz) Z)
      (ih (e.hom.base z') hz _ (preimageOpensIso e (U (e.hom.base z') hz)))


end

section
variable (hT : OrderCertificateIsoInvariantOfMaxContact.{u}) {k : Type u} [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))
include hT

private theorem orderCertificate_comap_iso_of_smoothDivisor_cover_consolidated247 (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData)
    (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (H : ∀ (z : ↥W) (hz : z ∈ Z.support), (U z hz).toScheme.IdealSheafData)
    (hH : ∀ (z : ↥W) (hz : z ∈ Z.support), IsSmoothDivisor ((U z hz).ι ≫ p) (H z hz))
    (hNsubH : ∀ (z : ↥W) (hz : z ∈ Z.support),
      ((N.comap (U z hz).ι).support : Set ↥(U z hz).toScheme) ⊆
        ((H z hz).support : Set ↥(U z hz).toScheme))
    (hZH : ∀ (z : ↥W) (hz : z ∈ Z.support),
      ((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme) ⊆
        ((H z hz).support : Set ↥(U z hz).toScheme))
    (J : ∀ (z : ↥W) (hz : z ∈ Z.support), Option (H z hz).subscheme.IdealSheafData)
    (hJnone : ∀ (z : ↥W) (hz : z ∈ Z.support), J z hz = Option.none →
      IsOpen (⇑(H z hz).subschemeι.base ⁻¹'
        ((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)))
    (hJcomp : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = Option.some Jz → NonzeroOnComponents Jz)
    (hJloc : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = Option.some Jz →
        ∀ x : ↥(H z hz).subscheme,
          ((H z hz).subschemeι ≫ (U z hz).ι).base x ∉ Mem →
            ∃ V : (H z hz).subscheme.Opens, x ∈ V ∧
              Jz.comap V.ι = ((N.comap (U z hz).ι).comap (H z hz).subschemeι).comap V.ι)
    (hJcert : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = Option.some Jz →
        PrincipalizationCertificate (H z hz).subscheme ((H z hz).subschemeι ≫ (U z hz).ι ≫ p) Jz μ
          (⇑((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
          ((Z.comap (U z hz).ι).comap (H z hz).subschemeι))
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = Option.some Jz →
        ∀ (X : Scheme.{u}) (f : X ≅ (H z hz).subscheme),
          PrincipalizationCertificate X (f.hom ≫ (H z hz).subschemeι ≫ (U z hz).ι ≫ p) (Jz.comap f.hom) μ
            (⇑f.hom.base ⁻¹' (⇑((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem))
            (((Z.comap (U z hz).ι).comap (H z hz).subschemeι).comap f.hom))
    (W' : Scheme.{u}) (e : W' ≅ W) :
    OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  hT k W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert ih W' e

private theorem principalizationCertificate_comap_iso_consolidated247 (I : W.IdealSheafData) (m : ℕ)
    (Mem : Set ↥W) (Z : W.IdealSheafData) (h : PrincipalizationCertificate W p I m Mem Z) :
    ∀ (W' : Scheme.{u}) (e : W' ≅ W),
      PrincipalizationCertificate W' (e.hom ≫ p) (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  @PrincipalizationCertificate.rec k _
    (fun W p I m Mem Z _ => ∀ (W' : Scheme.{u}) (e : W' ≅ W),
      PrincipalizationCertificate W' (e.hom ≫ p) (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom))
    (fun W p N μ Mem Z _ => ∀ (W' : Scheme.{u}) (e : W' ≅ W),
      OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom))
    (fun {W p I m Mem Z} h => principalizationCertificate_comap_iso_of_support_subset_consolidated247 W p I m Mem Z h)
    (fun {W p I m Mem Z} hm => principalizationCertificate_comap_iso_of_two_le_consolidated247 W p I m Mem Z hm)
    (fun {W p I m Mem Z} M N μ hI hM hmu hZ hcert ihc =>
      principalizationCertificate_comap_iso_of_orderCertificate_consolidated247 W p I m Mem Z M N μ hI hM hmu hZ hcert ihc)
    (fun {W p I m Mem Z} U hU hcert ihc =>
      principalizationCertificate_comap_iso_of_opens_cover_consolidated247 W p I m Mem Z U hU hcert ihc)
    (fun {W p N μ Mem Z} h => orderCertificate_comap_iso_of_support_subset_consolidated247 W p N μ Mem Z h)
    (fun {W p N μ Mem Z} hmu => orderCertificate_comap_iso_of_two_le_consolidated247 W p N μ Mem Z hmu)
    (fun {W p N μ Mem Z} U hU hcert ihc =>
      orderCertificate_comap_iso_of_opens_cover_consolidated247 W p N μ Mem Z U hU hcert ihc)
    (fun {W p N μ Mem Z} U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert ihc =>
      orderCertificate_comap_iso_of_smoothDivisor_cover_consolidated247 hT W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc
        hJcert ihc)
    W p I m Mem Z h

private theorem orderCertificate_comap_iso_consolidated247 (N : W.IdealSheafData) (μ : ℕ)
    (Mem : Set ↥W) (Z : W.IdealSheafData) (h : OrderCertificate W p N μ Mem Z) :
    ∀ (W' : Scheme.{u}) (e : W' ≅ W),
      OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  @OrderCertificate.rec k _
    (fun W p I m Mem Z _ => ∀ (W' : Scheme.{u}) (e : W' ≅ W),
      PrincipalizationCertificate W' (e.hom ≫ p) (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom))
    (fun W p N μ Mem Z _ => ∀ (W' : Scheme.{u}) (e : W' ≅ W),
      OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom))
    (fun {W p I m Mem Z} h => principalizationCertificate_comap_iso_of_support_subset_consolidated247 W p I m Mem Z h)
    (fun {W p I m Mem Z} hm => principalizationCertificate_comap_iso_of_two_le_consolidated247 W p I m Mem Z hm)
    (fun {W p I m Mem Z} M N μ hI hM hmu hZ hcert ihc =>
      principalizationCertificate_comap_iso_of_orderCertificate_consolidated247 W p I m Mem Z M N μ hI hM hmu hZ hcert ihc)
    (fun {W p I m Mem Z} U hU hcert ihc =>
      principalizationCertificate_comap_iso_of_opens_cover_consolidated247 W p I m Mem Z U hU hcert ihc)
    (fun {W p N μ Mem Z} h => orderCertificate_comap_iso_of_support_subset_consolidated247 W p N μ Mem Z h)
    (fun {W p N μ Mem Z} hmu => orderCertificate_comap_iso_of_two_le_consolidated247 W p N μ Mem Z hmu)
    (fun {W p N μ Mem Z} U hU hcert ihc =>
      orderCertificate_comap_iso_of_opens_cover_consolidated247 W p N μ Mem Z U hU hcert ihc)
    (fun {W p N μ Mem Z} U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert ihc =>
      orderCertificate_comap_iso_of_smoothDivisor_cover_consolidated247 hT W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc
        hJcert ihc)
    W p N μ Mem Z h


end

section
variable (hT : OrderCertificateIsoInvariantOfMaxContact.{u}) {k : Type u} [Field k] {W W' : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
include hT

theorem PrincipalizationCertificate.comap_iso {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (e : W' ≅ W) (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W' (e.hom ≫ p) (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  principalizationCertificate_comap_iso_consolidated247 hT W p I m Mem Z h W' e

theorem OrderCertificate.comap_iso {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (e : W' ≅ W) (h : OrderCertificate W p N μ Mem Z) :
    OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  orderCertificate_comap_iso_consolidated247 hT W p N μ Mem Z h W' e

theorem PrincipalizationCertificate.comap_iso_of_eq {p' : W' ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (e : W' ≅ W) (hp : p' = e.hom ≫ p)
    (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W' p' (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) := by
  subst hp
  exact PrincipalizationCertificate.comap_iso hT e h

theorem OrderCertificate.comap_iso_of_eq {p' : W' ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (e : W' ≅ W) (hp : p' = e.hom ≫ p)
    (h : OrderCertificate W p N μ Mem Z) :
    OrderCertificate W' p' (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) := by
  subst hp
  exact OrderCertificate.comap_iso hT e h


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section

namespace PrincipalizationIsoTransport

abbrev preimageOpens {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens) : X.Opens :=
  (Opens.map e.hom.base).obj U

section
variable {X Y : Scheme.{u}} (f : X ≅ Y) (I : Y.IdealSheafData)

private theorem ker_subschemeι_le_ker_comap_subschemeι_comp_hom_consolidated269 :
    Scheme.Hom.ker I.subschemeι
      ≤ Scheme.Hom.ker ((I.comap f.hom).subschemeι ≫ f.hom) := by
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.ker_subschemeι]
  exact Scheme.IdealSheafData.le_map_comap I f.hom

private theorem ker_comap_subschemeι_le_ker_subschemeι_comp_inv_consolidated269 :
    Scheme.Hom.ker (I.comap f.hom).subschemeι
      ≤ Scheme.Hom.ker (I.subschemeι ≫ f.inv) := by
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.ker_subschemeι]
  have h : (I.comap f.hom).comap f.inv = I := by
    rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  have h2 := Scheme.IdealSheafData.le_map_comap (I.comap f.hom) f.inv
  rw [h] at h2
  exact h2

private theorem exists_iso_subscheme_comap_comm_consolidated269 :
    ∃ g : (I.comap f.hom).subscheme ≅ I.subscheme,
      g.hom ≫ I.subschemeι = (I.comap f.hom).subschemeι ≫ f.hom := by
  have hc := IsClosedImmersion.lift_fac I.subschemeι
    ((I.comap f.hom).subschemeι ≫ f.hom) (ker_subschemeι_le_ker_comap_subschemeι_comp_hom_consolidated269 f I)
  have hd := IsClosedImmersion.lift_fac (I.comap f.hom).subschemeι
    (I.subschemeι ≫ f.inv) (ker_comap_subschemeι_le_ker_subschemeι_comp_inv_consolidated269 f I)
  set c := IsClosedImmersion.lift I.subschemeι ((I.comap f.hom).subschemeι ≫ f.hom)
    (ker_subschemeι_le_ker_comap_subschemeι_comp_hom_consolidated269 f I)
  set d := IsClosedImmersion.lift (I.comap f.hom).subschemeι (I.subschemeι ≫ f.inv)
    (ker_comap_subschemeι_le_ker_subschemeι_comp_inv_consolidated269 f I)
  refine ⟨⟨c, d, ?_, ?_⟩, hc⟩
  · rw [← cancel_mono (I.comap f.hom).subschemeι, Category.assoc, hd, ← Category.assoc, hc,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [← cancel_mono I.subschemeι, Category.assoc, hc, ← Category.assoc, hd,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]


end

def comapSubschemeIso {X Y : Scheme.{u}} (f : X ≅ Y) (I : Y.IdealSheafData) :
    (I.comap f.hom).subscheme ≅ I.subscheme :=
  (exists_iso_subscheme_comap_comm_consolidated269 f I).choose

@[reassoc]
theorem comapSubschemeIso_hom_comp {X Y : Scheme.{u}} (f : X ≅ Y) (I : Y.IdealSheafData) :
    (comapSubschemeIso f I).hom ≫ I.subschemeι = (I.comap f.hom).subschemeι ≫ f.hom :=
  (exists_iso_subscheme_comap_comm_consolidated269 f I).choose_spec

@[reassoc]
theorem preimageOpens_ι_comp_hom {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens) :
    (preimageOpens e U).ι ≫ e.hom = (preimageOpensIso e U).hom ≫ U.ι := by
  rw [preimageOpensIso_hom, Scheme.Hom.resLE_comp_ι]

@[reassoc]
theorem subschemeι_comp_preimageOpens_ι_comp_hom {W W' : Scheme.{u}} (e : W' ≅ W) (U : W.Opens)
    (H : U.toScheme.IdealSheafData) :
    (H.comap (preimageOpensIso e U).hom).subschemeι ≫ (preimageOpens e U).ι ≫ e.hom
      = (comapSubschemeIso (preimageOpensIso e U) H).hom ≫ H.subschemeι ≫ U.ι := by
  rw [preimageOpens_ι_comp_hom, ← Category.assoc, ← comapSubschemeIso_hom_comp, Category.assoc]

section
variable {X Y : Scheme.{u}} (g : X ≅ Y)

private theorem coe_support_comap_iso_consolidated269 (J : Y.IdealSheafData) :
    ((J.comap g.hom).support : Set ↥X) = ⇑g.hom.base ⁻¹' (J.support : Set ↥Y) := by
  have h := orderAtLeastLocus_comap_iso_hom_eq_preimage g J 1
  rw [orderAtLeastLocus_one, orderAtLeastLocus_one] at h
  exact h

private theorem support_comap_iso_subset_of_subset_consolidated269 {A B : Y.IdealSheafData} (h : (A.support : Set ↥Y) ⊆ (B.support : Set ↥Y)) :
    ((A.comap g.hom).support : Set ↥X) ⊆ ((B.comap g.hom).support : Set ↥X) := by
  rw [coe_support_comap_iso_consolidated269, coe_support_comap_iso_consolidated269]
  exact Set.preimage_mono h


end

private theorem preimage_base_comp_consolidated269 {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (S : Set ↥Z) :
    ⇑(f ≫ g).base ⁻¹' S = ⇑f.base ⁻¹' (⇑g.base ⁻¹' S) := by
  ext x
  simp

private theorem image_mem_irreducibleComponents_of_homeomorph_consolidated269 {α β : Type u} [TopologicalSpace α]
    [TopologicalSpace β] (h : α ≃ₜ β) {T : Set α} (hT : T ∈ irreducibleComponents α) :
    ⇑h '' T ∈ irreducibleComponents β := by
  have himg : IsIrreducible (⇑h '' T) := hT.1.image _ h.continuous.continuousOn
  refine ⟨himg, ?_⟩
  intro S hS hsub
  have h2 : ⇑h.symm '' S = ⇑h ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hy
      exact ⟨h y, hy, by simp⟩
  have hpre : IsIrreducible (⇑h ⁻¹' S) := by
    rw [← h2]
    exact hS.image _ h.symm.continuous.continuousOn
  have hTsub : T ⊆ ⇑h ⁻¹' S := fun y hy => hsub ⟨y, hy, rfl⟩
  have h3 : ⇑h ⁻¹' S ⊆ T := hT.2 hpre hTsub
  intro y hy
  refine ⟨h.symm y, h3 ?_, by simp⟩
  simpa using hy

section
variable {X Y : Scheme.{u}}

private theorem comap_preimageOpens_ι_comap_iso_consolidated269 (e : X ≅ Y) (V : Y.Opens)
    (A : Y.IdealSheafData) :
    (A.comap e.hom).comap (preimageOpens e V).ι = (A.comap V.ι).comap (preimageOpensIso e V).hom := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, preimageOpens_ι_comp_hom]

private theorem comap_subschemeι_comap_iso_consolidated269 (r : X ≅ Y) (B : Y.IdealSheafData)
    (A : Y.IdealSheafData) :
    (A.comap r.hom).comap (B.comap r.hom).subschemeι
      = (A.comap B.subschemeι).comap (comapSubschemeIso r B).hom := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    comapSubschemeIso_hom_comp]


end

section
variable {X Y : Scheme.{u}} (e : X ≅ Y) (V : Y.Opens)

private theorem support_comap_preimageOpens_subset_consolidated269 (A : Y.IdealSheafData) (B : V.toScheme.IdealSheafData)
    (h : ((A.comap V.ι).support : Set ↥V.toScheme) ⊆ (B.support : Set ↥V.toScheme)) :
    (((A.comap e.hom).comap (preimageOpens e V).ι).support :
        Set ↥(preimageOpens e V).toScheme)
      ⊆ ((B.comap (preimageOpensIso e V).hom).support : Set ↥(preimageOpens e V).toScheme) := by
  rw [comap_preimageOpens_ι_comap_iso_consolidated269]
  exact support_comap_iso_subset_of_subset_consolidated269 (preimageOpensIso e V) h

private theorem isOpen_preimage_support_comap_preimageOpensIso_consolidated269 (A : Y.IdealSheafData) (B : V.toScheme.IdealSheafData)
    (h : IsOpen (⇑B.subschemeι.base ⁻¹' ((A.comap V.ι).support : Set ↥V.toScheme))) :
    IsOpen (⇑(B.comap (preimageOpensIso e V).hom).subschemeι.base ⁻¹'
      (((A.comap e.hom).comap (preimageOpens e V).ι).support :
        Set ↥(preimageOpens e V).toScheme)) := by
  rw [comap_preimageOpens_ι_comap_iso_consolidated269, coe_support_comap_iso_consolidated269 (preimageOpensIso e V) (A.comap V.ι), ← _root_.FunctorialResolution.EmbeddedResolution.PrincipalizationIsoTransport.preimage_base_comp_consolidated269,
    ← comapSubschemeIso_hom_comp, _root_.FunctorialResolution.EmbeddedResolution.PrincipalizationIsoTransport.preimage_base_comp_consolidated269]
  exact h.preimage (comapSubschemeIso (preimageOpensIso e V) B).hom.continuous

private theorem preimage_comap_subschemeι_preimageOpens_comp_consolidated269 (B : V.toScheme.IdealSheafData) (Mem : Set ↥Y) :
    ⇑((B.comap (preimageOpensIso e V).hom).subschemeι ≫ (preimageOpens e V).ι).base ⁻¹'
        (⇑e.hom.base ⁻¹' Mem)
      = ⇑(comapSubschemeIso (preimageOpensIso e V) B).hom.base ⁻¹'
        (⇑(B.subschemeι ≫ V.ι).base ⁻¹' Mem) := by
  rw [← _root_.FunctorialResolution.EmbeddedResolution.PrincipalizationIsoTransport.preimage_base_comp_consolidated269, ← _root_.FunctorialResolution.EmbeddedResolution.PrincipalizationIsoTransport.preimage_base_comp_consolidated269, Category.assoc, subschemeι_comp_preimageOpens_ι_comp_hom]


end

section
variable {X Y : Scheme.{u}} (g : X ≅ Y) {o : Option Y.IdealSheafData}

private theorem eq_none_of_map_comap_eq_none_consolidated269 (h : o.map (fun J => J.comap g.hom) = Option.none) :
    o = Option.none := by
  cases o with
  | none => rfl
  | some a => simp at h

private theorem exists_eq_some_of_map_comap_eq_some_consolidated269 {b : X.IdealSheafData}
    (h : o.map (fun J => J.comap g.hom) = Option.some b) :
    ∃ a, o = Option.some a ∧ a.comap g.hom = b := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, rfl, by simpa using h⟩


end

private theorem exists_isOpen_comap_eq_comap_preimageOpensIso_consolidated269 {W W' : Scheme.{u}} (e : W' ≅ W) (N : W.IdealSheafData)
    (Mem : Set ↥W) (V : W.Opens) (B : V.toScheme.IdealSheafData)
    (Jz : B.subscheme.IdealSheafData)
    (h : ∀ x : ↥B.subscheme, (B.subschemeι ≫ V.ι).base x ∉ Mem →
      ∃ O : B.subscheme.Opens, x ∈ O ∧
        Jz.comap O.ι = ((N.comap V.ι).comap B.subschemeι).comap O.ι)
    (x : ↥(B.comap (preimageOpensIso e V).hom).subscheme)
    (hx : ((B.comap (preimageOpensIso e V).hom).subschemeι ≫ (preimageOpens e V).ι).base x
      ∉ ⇑e.hom.base ⁻¹' Mem) :
    ∃ O : (B.comap (preimageOpensIso e V).hom).subscheme.Opens, x ∈ O ∧
      (Jz.comap (comapSubschemeIso (preimageOpensIso e V) B).hom).comap O.ι =
        (((N.comap e.hom).comap (preimageOpens e V).ι).comap
          (B.comap (preimageOpensIso e V).hom).subschemeι).comap O.ι := by
  have hx' : (B.subschemeι ≫ V.ι).base
      ((comapSubschemeIso (preimageOpensIso e V) B).hom.base x) ∉ Mem := by
    intro hmem
    apply hx
    have hmem2 : x ∈ ⇑(comapSubschemeIso (preimageOpensIso e V) B).hom.base ⁻¹'
        (⇑(B.subschemeι ≫ V.ι).base ⁻¹' Mem) := hmem
    rw [← preimage_comap_subschemeι_preimageOpens_comp_consolidated269 e V B Mem] at hmem2
    exact hmem2
  obtain ⟨O, hxO, hO⟩ := h ((comapSubschemeIso (preimageOpensIso e V) B).hom.base x) hx'
  refine ⟨preimageOpens (comapSubschemeIso (preimageOpensIso e V) B) O, hxO, ?_⟩
  rw [comap_preimageOpens_ι_comap_iso_consolidated269, comap_preimageOpens_ι_comap_iso_consolidated269, comap_subschemeι_comap_iso_consolidated269, comap_preimageOpens_ι_comap_iso_consolidated269, hO]

section
variable {k : Type u} [Field k]

private theorem principalizationCertificate_comap_preimageOpensIso_consolidated269 {W W' : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of k)) (e : W' ≅ W) (Z : W.IdealSheafData) (μ : ℕ)
    (Mem : Set ↥W) (V : W.Opens) (B : V.toScheme.IdealSheafData)
    (Jz : B.subscheme.IdealSheafData)
    (h : ∀ (T : Scheme.{u}) (f : T ≅ B.subscheme),
      PrincipalizationCertificate T (f.hom ≫ B.subschemeι ≫ V.ι ≫ p) (Jz.comap f.hom) μ
        (⇑f.hom.base ⁻¹' (⇑(B.subschemeι ≫ V.ι).base ⁻¹' Mem))
        (((Z.comap V.ι).comap B.subschemeι).comap f.hom)) :
    PrincipalizationCertificate (B.comap (preimageOpensIso e V).hom).subscheme
      ((B.comap (preimageOpensIso e V).hom).subschemeι ≫ (preimageOpens e V).ι ≫ e.hom ≫ p)
      (Jz.comap (comapSubschemeIso (preimageOpensIso e V) B).hom) μ
      (⇑((B.comap (preimageOpensIso e V).hom).subschemeι ≫ (preimageOpens e V).ι).base ⁻¹'
        (⇑e.hom.base ⁻¹' Mem))
      (((Z.comap e.hom).comap (preimageOpens e V).ι).comap
        (B.comap (preimageOpensIso e V).hom).subschemeι) := by
  have ht := h (B.comap (preimageOpensIso e V).hom).subscheme (comapSubschemeIso (preimageOpensIso e V) B)
  rw [← subschemeι_comp_preimageOpens_ι_comp_hom_assoc, ← preimage_comap_subschemeι_preimageOpens_comp_consolidated269, ← comap_subschemeι_comap_iso_consolidated269,
    ← comap_preimageOpens_ι_comap_iso_consolidated269] at ht
  exact ht

theorem isSmoothDivisor_comap_iso {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) (D : Y.IdealSheafData)
    (h : IsSmoothDivisor q D) : IsSmoothDivisor (e.hom ≫ q) (D.comap e.hom) := by
  rw [isSmoothDivisor_iff] at h ⊢
  exact ⟨h.1.comap_iso e, smooth_comap_iso q e D h.2⟩

theorem isSmoothDivisor_comap_preimageOpensIso {W W' : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of k)) (e : W' ≅ W) (U : W.Opens)
    (H : U.toScheme.IdealSheafData) (h : IsSmoothDivisor (U.ι ≫ p) H) :
    IsSmoothDivisor ((preimageOpens e U).ι ≫ e.hom ≫ p) (H.comap (preimageOpensIso e U).hom) := by
  have h' := isSmoothDivisor_comap_iso (U.ι ≫ p) (preimageOpensIso e U) H h
  rwa [← Category.assoc, ← preimageOpens_ι_comp_hom, Category.assoc] at h'


end

theorem nonzeroOnComponents_comap_iso {X Y : Scheme.{u}} (f : X ≅ Y) (I : Y.IdealSheafData)
    (h : NonzeroOnComponents I) : NonzeroOnComponents (I.comap f.hom) := by
  rw [nonzeroOnComponents_iff] at h ⊢
  intro T hT hsub
  refine h (⇑f.hom.base '' T) ?_ ?_
  · exact image_mem_irreducibleComponents_of_homeomorph_consolidated269 (Scheme.homeoOfIso f) hT
  · rintro y ⟨x, hx, rfl⟩
    have hx' : x ∈ ((I.comap f.hom).support : Set ↥X) := hsub hx
    rw [coe_support_comap_iso_consolidated269 f I] at hx'
    exact hx'

end PrincipalizationIsoTransport

theorem isoInvariantOrderCertificateDescend : OrderCertificateIsoInvariantOfMaxContact.{u} := by
  intro k inst W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert hJtrans W' e
  have hsupp : ∀ z' : ↥W', z' ∈ (Z.comap e.hom).support → e.hom.base z' ∈ Z.support := by
    intro z' hz'
    have h1 : z' ∈ ((Z.comap e.hom).support : Set ↥W') := hz'
    rw [PrincipalizationIsoTransport.coe_support_comap_iso_consolidated269 e Z] at h1
    exact h1
  refine OrderCertificate.descend
    (fun z' hz' => PrincipalizationIsoTransport.preimageOpens e (U (e.hom.base z') (hsupp z' hz')))
    (fun z' hz' => hU (e.hom.base z') (hsupp z' hz'))
    (fun z' hz' => (H (e.hom.base z') (hsupp z' hz')).comap
      (preimageOpensIso e (U (e.hom.base z') (hsupp z' hz'))).hom)
    (fun z' hz' => PrincipalizationIsoTransport.isSmoothDivisor_comap_preimageOpensIso p e
      (U (e.hom.base z') (hsupp z' hz')) (H (e.hom.base z') (hsupp z' hz'))
      (hH (e.hom.base z') (hsupp z' hz')))
    (fun z' hz' => PrincipalizationIsoTransport.support_comap_preimageOpens_subset_consolidated269 e
      (U (e.hom.base z') (hsupp z' hz')) N (H (e.hom.base z') (hsupp z' hz'))
      (hNsubH (e.hom.base z') (hsupp z' hz')))
    (fun z' hz' => PrincipalizationIsoTransport.support_comap_preimageOpens_subset_consolidated269 e
      (U (e.hom.base z') (hsupp z' hz')) Z (H (e.hom.base z') (hsupp z' hz'))
      (hZH (e.hom.base z') (hsupp z' hz')))
    (fun z' hz' => (J (e.hom.base z') (hsupp z' hz')).map
      (fun Jz => Jz.comap (PrincipalizationIsoTransport.comapSubschemeIso
        (preimageOpensIso e (U (e.hom.base z') (hsupp z' hz')))
        (H (e.hom.base z') (hsupp z' hz'))).hom))
    ?_ ?_ ?_ ?_
  · intro z' hz' hnone
    refine PrincipalizationIsoTransport.isOpen_preimage_support_comap_preimageOpensIso_consolidated269 e (U (e.hom.base z') (hsupp z' hz')) Z
      (H (e.hom.base z') (hsupp z' hz'))
      (hJnone (e.hom.base z') (hsupp z' hz') ?_)
    exact PrincipalizationIsoTransport.eq_none_of_map_comap_eq_none_consolidated269 _ hnone
  · intro z' hz' Jz' heq
    obtain ⟨Jz, hJz, rfl⟩ := PrincipalizationIsoTransport.exists_eq_some_of_map_comap_eq_some_consolidated269 _ heq
    exact PrincipalizationIsoTransport.nonzeroOnComponents_comap_iso _ Jz
      (hJcomp (e.hom.base z') (hsupp z' hz') Jz hJz)
  · intro z' hz' Jz' heq x hx
    obtain ⟨Jz, hJz, rfl⟩ := PrincipalizationIsoTransport.exists_eq_some_of_map_comap_eq_some_consolidated269 _ heq
    exact PrincipalizationIsoTransport.exists_isOpen_comap_eq_comap_preimageOpensIso_consolidated269 e N Mem (U (e.hom.base z') (hsupp z' hz'))
      (H (e.hom.base z') (hsupp z' hz')) Jz
      (hJloc (e.hom.base z') (hsupp z' hz') Jz hJz) x hx
  · intro z' hz' Jz' heq
    obtain ⟨Jz, hJz, rfl⟩ := PrincipalizationIsoTransport.exists_eq_some_of_map_comap_eq_some_consolidated269 _ heq
    exact PrincipalizationIsoTransport.principalizationCertificate_comap_preimageOpensIso_consolidated269 p e Z μ Mem (U (e.hom.base z') (hsupp z' hz'))
      (H (e.hom.base z') (hsupp z' hz')) Jz
      (hJtrans (e.hom.base z') (hsupp z' hz') Jz hJz)

section
variable {k : Type u} [Field k] {W W' : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}

theorem OrderCertificate.comap_iso_hom_comp {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (e : W' ≅ W) (h : OrderCertificate W p N μ Mem Z) :
    OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  OrderCertificate.comap_iso isoInvariantOrderCertificateDescend e h

theorem PrincipalizationCertificate.comap_iso_of_eq_iso_hom_comp {p' : W' ⟶ Spec (CommRingCat.of k)}
    {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
    (e : W' ≅ W) (hp : p' = e.hom ≫ p) (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W' p' (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  PrincipalizationCertificate.comap_iso_of_eq isoInvariantOrderCertificateDescend e hp h

theorem OrderCertificate.comap_iso_of_eq_iso_hom_comp {p' : W' ⟶ Spec (CommRingCat.of k)}
    {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
    (e : W' ≅ W) (hp : p' = e.hom ≫ p) (h : OrderCertificate W p N μ Mem Z) :
    OrderCertificate W' p' (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  OrderCertificate.comap_iso_of_eq isoInvariantOrderCertificateDescend e hp h


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.KrullDimClosedSubset
section

open TopologicalSpace AlgebraicGeometry


open Order in
private theorem topologicalKrullDim_eq_iSup_length_consolidated132 {Z : Type*} [TopologicalSpace Z] :
    topologicalKrullDim Z =
      ⨆ p : LTSeries (IrreducibleCloseds Z), (p.length : WithBot ℕ∞) := rfl

private def irreducibleClosedsImageSubtypeVal_consolidated132 {X : Type u} [TopologicalSpace X] {Y : Set X} (hY : IsClosed Y)
    (a : IrreducibleCloseds ↥Y) : IrreducibleCloseds X :=
  ⟨Subtype.val '' a.1, a.2.image _ continuous_subtype_val.continuousOn,
    hY.isClosedMap_subtype_val _ a.3⟩

section
variable {X : Type u} [TopologicalSpace X] {Y : Set X} (hY : IsClosed Y)

private theorem coe_irreducibleClosedsImageVal_consolidated132 (a : IrreducibleCloseds ↥Y) :
    ((irreducibleClosedsImageSubtypeVal_consolidated132 hY a : IrreducibleCloseds X) : Set X) = Subtype.val '' (a : Set ↥Y) := rfl

private theorem irreducibleClosedsImageVal_subset_consolidated132 (a : IrreducibleCloseds ↥Y) :
    ((irreducibleClosedsImageSubtypeVal_consolidated132 hY a : IrreducibleCloseds X) : Set X) ⊆ Y := by
  rw [coe_irreducibleClosedsImageVal_consolidated132]
  rintro x ⟨y, -, rfl⟩
  exact y.2

private theorem strictMono_irreducibleClosedsImageVal_consolidated132 : StrictMono (irreducibleClosedsImageSubtypeVal_consolidated132 hY) := by
  intro a b hab
  refine lt_of_le_of_ne ?_ ?_
  · rw [← SetLike.coe_subset_coe, coe_irreducibleClosedsImageVal_consolidated132, coe_irreducibleClosedsImageVal_consolidated132]
    exact Set.image_mono (SetLike.coe_subset_coe.mpr hab.le)
  · intro h
    have h1 : Subtype.val '' (a : Set ↥Y) = Subtype.val '' (b : Set ↥Y) := by
      rw [← coe_irreducibleClosedsImageVal_consolidated132 hY a, ← coe_irreducibleClosedsImageVal_consolidated132 hY b, h]
    exact hab.ne (SetLike.coe_injective (Set.image_injective.mpr Subtype.val_injective h1))


end

private theorem exists_mem_irreducibleComponents_superset_of_isIrreducible_consolidated132 {X : Type u} [TopologicalSpace X] {s : Set X}
    (hs : IsIrreducible s) :
    ∃ C : Set X, C ∈ irreducibleComponents X ∧ IsIrreducible C ∧ IsClosed C ∧ s ⊆ C := by
  obtain ⟨t, ht, hst, hmax⟩ := exists_preirreducible s hs.2
  have htirr : IsIrreducible t := ⟨hs.1.mono hst, ht⟩
  have htc : closure t = t := hmax (closure t) ht.closure subset_closure
  exact ⟨t, ⟨htirr, fun u hu htu => le_of_eq (hmax u hu.2 htu)⟩, htirr,
    closure_eq_iff_isClosed.mp htc, hst⟩

private theorem nonempty_irreducibleCloseds_consolidated132 {Z : Type u} [TopologicalSpace Z] (z : Z) :
    Nonempty (IrreducibleCloseds Z) :=
  ⟨⟨closure {z}, ⟨⟨z, subset_closure rfl⟩, isPreirreducible_singleton.closure⟩,
    isClosed_closure⟩⟩

open Order in
theorem topologicalKrullDim_lt_of_isClosed_of_not_subset_irreducibleComponents
    {X : Type u} [TopologicalSpace X] (Y : Set X) (hY : IsClosed Y) (hne : Y.Nonempty)
    (hcomp : ∀ C ∈ irreducibleComponents X, ¬ C ⊆ Y)
    (hfin : topologicalKrullDim X < ⊤) :
    topologicalKrullDim ↥Y < topologicalKrullDim X := by
  have key : ∀ p : LTSeries (IrreducibleCloseds ↥Y),
      (((p.length + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim X := by
    intro p
    obtain ⟨q, hqlen, hqlast⟩ :
        ∃ q : LTSeries (IrreducibleCloseds X),
          q.length = p.length ∧ q.last = irreducibleClosedsImageSubtypeVal_consolidated132 hY p.last :=
      ⟨p.map (irreducibleClosedsImageSubtypeVal_consolidated132 hY) (strictMono_irreducibleClosedsImageVal_consolidated132 hY), rfl, rfl⟩
    obtain ⟨C, hCmem, hCirr, hCcl, hsub⟩ := exists_mem_irreducibleComponents_superset_of_isIrreducible_consolidated132 q.last.2
    have hsub' : ((q.last : IrreducibleCloseds X) : Set X)
        ⊆ ((⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) : Set X) := hsub
    have hlt : q.last < (⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) := by
      refine lt_of_le_of_ne (SetLike.coe_subset_coe.mp hsub') ?_
      intro h
      refine hcomp C hCmem ?_
      have hc : ((⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) : Set X) ⊆ Y := by
        rw [← h, hqlast]
        exact irreducibleClosedsImageVal_subset_consolidated132 hY p.last
      exact hc
    have hs1 : (q.snoc (⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) hlt).length = q.length + 1 := rfl
    have hs2 : (q.snoc (⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) hlt).length = p.length + 1 := by
      omega
    have h1 : ((q.snoc (⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) hlt).length : WithBot ℕ∞)
        ≤ ⨆ r : LTSeries (IrreducibleCloseds X), (r.length : WithBot ℕ∞) :=
      le_iSup (fun r : LTSeries (IrreducibleCloseds X) => (r.length : WithBot ℕ∞)) _
    rw [hs2] at h1
    rw [topologicalKrullDim_eq_iSup_length_consolidated132, WithBot.coe_natCast]
    exact h1
  obtain ⟨y0, hy0⟩ := hne
  obtain ⟨a0⟩ := nonempty_irreducibleCloseds_consolidated132 (⟨y0, hy0⟩ : ↥Y)
  have hp0 : (((1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim X :=
    key ⟨0, fun _ => a0, fun i => i.elim0⟩
  have hbot : topologicalKrullDim X ≠ ⊥ := by
    intro hb
    rw [hb] at hp0
    exact WithBot.coe_ne_bot (le_bot_iff.mp hp0)
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hetop : e ≠ ⊤ := by
    rintro rfl
    rw [← he] at hfin
    exact lt_irrefl _ hfin
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp hetop
  have hD : topologicalKrullDim X = (((N : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [← he, ← hN]
  rw [hD] at hp0
  have hN1 : 1 ≤ N := by
    have h2 := WithBot.coe_le_coe.mp hp0
    exact_mod_cast h2
  have hbound : (⨆ p : LTSeries (IrreducibleCloseds ↥Y), (p.length : WithBot ℕ∞))
      ≤ ((((N - 1 : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
    refine iSup_le fun p => ?_
    show ((p.length : ℕ) : WithBot ℕ∞) ≤ ((((N - 1 : ℕ)) : ℕ∞) : WithBot ℕ∞)
    have hk := key p
    rw [hD] at hk
    have h3 : p.length + 1 ≤ N := by
      have h2 := WithBot.coe_le_coe.mp hk
      exact_mod_cast h2
    have h4 : p.length ≤ N - 1 := by omega
    rw [← WithBot.coe_natCast]
    exact WithBot.coe_le_coe.mpr (by exact_mod_cast h4)
  have h5 : N - 1 < N := by omega
  have h6 : (((N - 1 : ℕ)) : ℕ∞) < ((N : ℕ) : ℕ∞) := by exact_mod_cast h5
  rw [topologicalKrullDim_eq_iSup_length_consolidated132 (Z := ↥Y), hD]
  exact lt_of_le_of_lt hbound (WithBot.coe_lt_coe.mpr h6)

private def irreducibleClosedsMapHomeomorph_consolidated132 {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (a : IrreducibleCloseds X) : IrreducibleCloseds Y :=
  ⟨e '' a.1, a.2.image e e.continuous.continuousOn, e.isClosedMap _ a.3⟩

section
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)

private theorem coe_irreducibleClosedsMapOfHomeomorph_consolidated132 (a : IrreducibleCloseds X) :
    ((irreducibleClosedsMapHomeomorph_consolidated132 e a : IrreducibleCloseds Y) : Set Y) = e '' (a : Set X) := rfl

private theorem strictMono_irreducibleClosedsMapOfHomeomorph_consolidated132 : StrictMono (irreducibleClosedsMapHomeomorph_consolidated132 e) := by
  intro a b hab
  refine lt_of_le_of_ne ?_ ?_
  · rw [← SetLike.coe_subset_coe, coe_irreducibleClosedsMapOfHomeomorph_consolidated132, coe_irreducibleClosedsMapOfHomeomorph_consolidated132]
    exact Set.image_mono (SetLike.coe_subset_coe.mpr hab.le)
  · intro h
    have h1 : e '' (a : Set X) = e '' (b : Set X) := by
      rw [← coe_irreducibleClosedsMapOfHomeomorph_consolidated132 e a, ← coe_irreducibleClosedsMapOfHomeomorph_consolidated132 e b, h]
    exact hab.ne (SetLike.coe_injective (Set.image_injective.mpr e.injective h1))


end

open Order in
private theorem topologicalKrullDim_le_of_homeomorph_consolidated132 {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [topologicalKrullDim_eq_iSup_length_consolidated132 (Z := X), topologicalKrullDim_eq_iSup_length_consolidated132 (Z := Y)]
  refine iSup_le fun p => ?_
  have h := le_iSup (fun r : LTSeries (IrreducibleCloseds Y) => (r.length : WithBot ℕ∞))
    (p.map (irreducibleClosedsMapHomeomorph_consolidated132 e) (strictMono_irreducibleClosedsMapOfHomeomorph_consolidated132 e))
  exact h

theorem topologicalKrullDim_eq_of_homeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  le_antisymm (topologicalKrullDim_le_of_homeomorph_consolidated132 e) (topologicalKrullDim_le_of_homeomorph_consolidated132 e.symm)

private theorem withBotSuccToNat_lt_withBotSuccToNat_consolidated132 {a b : WithBot ℕ∞} (h : a < b) (hb : b < ⊤) :
    withBotSuccToNat a < withBotSuccToNat b := by
  induction b using WithBot.recBotCoe with
  | bot => exact absurd h not_lt_bot
  | coe n =>
    have hn : n ≠ ⊤ := by
      rintro rfl
      exact lt_irrefl _ hb
    induction a using WithBot.recBotCoe with
    | bot =>
      rw [withBotSuccToNat_bot, withBotSuccToNat_coe]
      omega
    | coe m =>
      have hmn : m < n := WithBot.coe_lt_coe.mp h
      have hm : m ≠ ⊤ := ne_top_of_lt hmn
      obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp hm
      obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp hn
      subst hM
      subst hN
      rw [withBotSuccToNat_coe, withBotSuccToNat_coe]
      have hMN : M < N := by exact_mod_cast hmn
      have e1 : ((M : ℕ∞)).toNat = M := by simp
      have e2 : ((N : ℕ∞)).toNat = N := by simp
      omega

theorem krullDimSucc_lt_of_topologicalKrullDim_lt (Z X : Scheme.{u})
    (h : topologicalKrullDim ↥Z < topologicalKrullDim ↥X)
    (hfin : topologicalKrullDim ↥X < ⊤) :
    krullDimSucc Z < krullDimSucc X := withBotSuccToNat_lt_withBotSuccToNat_consolidated132 h hfin

theorem krullDimSucc_lt_of_homeomorph_isClosed (X Z : Scheme.{u}) (Y : Set ↥X)
    (hY : IsClosed Y) (hne : Y.Nonempty)
    (hcomp : ∀ C ∈ irreducibleComponents ↥X, ¬ C ⊆ Y)
    (hfin : topologicalKrullDim ↥X < ⊤)
    (e : ↥Z ≃ₜ ↥Y) :
    krullDimSucc Z < krullDimSucc X := by
  have h := topologicalKrullDim_lt_of_isClosed_of_not_subset_irreducibleComponents Y hY hne hcomp
    hfin
  refine krullDimSucc_lt_of_topologicalKrullDim_lt Z X ?_ hfin
  rw [topologicalKrullDim_eq_of_homeomorph e]
  exact h

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FiniteKrullDim
section

open TopologicalSpace AlgebraicGeometry


private theorem topologicalKrullDim_lt_top_of_homeomorph_consolidated155 {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B) (h : topologicalKrullDim B < ⊤) :
    topologicalKrullDim A < ⊤ := by
  rw [topologicalKrullDim_eq_of_homeomorph e]
  exact h

section
variable {X : Type u} [TopologicalSpace X]

private theorem subset_closure_inter_of_isPreirreducible_consolidated155 {S V : Set X} (hS : IsPreirreducible S) (hV : IsOpen V) (hne : (S ∩ V).Nonempty) :
    S ⊆ closure (S ∩ V) := by
  intro s hs
  rw [mem_closure_iff]
  intro W hW hsW
  obtain ⟨y, hyS, hyW, hyV⟩ := hS W V hW hV ⟨s, hs, hsW⟩ hne
  exact ⟨y, hyW, hyS, hyV⟩

private theorem eq_of_preimage_val_eq_consolidated155 {W : Set X}
    (hW : IsOpen W) {C D : Set X} (hC : IsClosed C) (hD : IsIrreducible D) (hCsubD : C ⊆ D)
    (hne : (C ∩ W).Nonempty)
    (heq : (Subtype.val ⁻¹' C : Set ↥W) = (Subtype.val ⁻¹' D : Set ↥W)) : C = D := by
  refine subset_antisymm hCsubD ?_
  have h1 : D ∩ W ⊆ C := by
    rintro y ⟨hyD, hyW⟩
    have hy : (⟨y, hyW⟩ : ↥W) ∈ (Subtype.val ⁻¹' D : Set ↥W) := hyD
    rw [← heq] at hy
    exact hy
  obtain ⟨z, hzC, hzW⟩ := hne
  have h2 : (D ∩ W).Nonempty := ⟨z, hCsubD hzC, hzW⟩
  calc D ⊆ closure (D ∩ W) := subset_closure_inter_of_isPreirreducible_consolidated155 hD.2 hW h2
    _ ⊆ closure C := closure_mono h1
    _ = C := hC.closure_eq


end

section
variable {X : Type u} [TopologicalSpace X] {ι : Type v} (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)
include hU hcov

private theorem topologicalKrullDim_le_of_iUnion_eq_univ_consolidated155 (c : WithBot ℕ∞) (h : ∀ i, topologicalKrullDim ↥(U i) ≤ c) :
    topologicalKrullDim X ≤ c := by
  refine iSup_le ?_
  intro p
  obtain ⟨x, hx⟩ := (p 0).isIrreducible.1
  have hxU : x ∈ ⋃ i, U i := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
  have hoe := (hU i).isOpenEmbedding_subtypeVal
  have hsub : ∀ j : Fin (p.length + 1),
      ((p 0 : IrreducibleCloseds X) : Set X) ⊆ ((p j : IrreducibleCloseds X) : Set X) :=
    fun j => SetLike.coe_subset_coe.mpr (LTSeries.monotone p (Fin.zero_le j))
  let V : Fin (p.length + 1) → IrreducibleCloseds ↥(U i) := fun j =>
    ⟨Subtype.val ⁻¹' ((p j : IrreducibleCloseds X) : Set X),
      ⟨⟨⟨x, hi⟩, hsub j hx⟩, (p j).isIrreducible.2.preimage hoe⟩,
      (p j).isClosed.preimage continuous_subtype_val⟩
  have hstep : ∀ j : Fin p.length, V j.castSucc < V j.succ := by
    intro j
    have hlt : p j.castSucc < p j.succ := p.step j
    have hsubset : ((p j.castSucc : IrreducibleCloseds X) : Set X)
        ⊆ ((p j.succ : IrreducibleCloseds X) : Set X) :=
      SetLike.coe_subset_coe.mpr hlt.le
    have hle : V j.castSucc ≤ V j.succ := by
      refine SetLike.coe_subset_coe.mp ?_
      intro z hz
      exact hsubset hz
    refine lt_of_le_of_ne hle ?_
    intro hEq
    have hcar : (Subtype.val ⁻¹' ((p j.castSucc : IrreducibleCloseds X) : Set X) : Set ↥(U i))
        = (Subtype.val ⁻¹' ((p j.succ : IrreducibleCloseds X) : Set X) : Set ↥(U i)) :=
      congrArg (fun s : IrreducibleCloseds ↥(U i) => (s : Set ↥(U i))) hEq
    have hCsubD : ((p j.castSucc : IrreducibleCloseds X) : Set X)
        = ((p j.succ : IrreducibleCloseds X) : Set X) :=
      eq_of_preimage_val_eq_consolidated155 (hU i) (p j.castSucc).isClosed (p j.succ).isIrreducible hsubset
        ⟨x, hsub _ hx, hi⟩ hcar
    exact absurd (IrreducibleCloseds.ext hCsubD) hlt.ne
  let q : LTSeries (IrreducibleCloseds ↥(U i)) := ⟨p.length, V, hstep⟩
  have hq : ((q.length : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim ↥(U i) :=
    Order.LTSeries.length_le_krullDim q
  exact le_trans hq (h i)

theorem topologicalKrullDim_le_natCast_of_isOpenCover (n : ℕ)
    (h : ∀ i, topologicalKrullDim ↥(U i) ≤ (n : WithBot ℕ∞)) :
    topologicalKrullDim X ≤ (n : WithBot ℕ∞) :=
  topologicalKrullDim_le_of_iUnion_eq_univ_consolidated155 U hU hcov _ h


end

section
variable (n : ℕ)

private theorem natCast_withBot_ne_top_consolidated155 : ((n : ℕ) : WithBot ℕ∞) ≠ ⊤ := by
  intro hcontra
  have h2 : ((n : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_natCast]
    exact hcontra
  have h3 : (n : ℕ∞) = ⊤ := WithBot.coe_injective h2
  simp at h3

private theorem natCast_withBot_lt_top_consolidated155 : ((n : ℕ) : WithBot ℕ∞) < ⊤ :=
  lt_top_iff_ne_top.mpr (natCast_withBot_ne_top_consolidated155 n)


end

private theorem exists_le_natCast_of_lt_top_consolidated155 {a : WithBot ℕ∞} (h : a < ⊤) :
    ∃ n : ℕ, a ≤ ((n : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact ⟨0, bot_le⟩
  | coe b =>
    induction b using WithTop.recTopCoe with
    | top => exact absurd h (lt_irrefl _)
    | coe n => exact ⟨n, le_rfl⟩

theorem topologicalKrullDim_lt_top_of_finite_isOpenCover {X : Type u} [TopologicalSpace X]
    {ι : Type v} [Finite ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = Set.univ) (h : ∀ i, topologicalKrullDim ↥(U i) < ⊤) :
    topologicalKrullDim X < ⊤ := by
  classical
  choose N hN using fun i => exists_le_natCast_of_lt_top_consolidated155 (h i)
  have : Fintype ι := Fintype.ofFinite ι
  have hle : topologicalKrullDim X ≤ (((Finset.univ.sup N : ℕ) : ℕ) : WithBot ℕ∞) := by
    refine topologicalKrullDim_le_natCast_of_isOpenCover U hU hcov _ ?_
    intro i
    exact le_trans (hN i) (Nat.mono_cast (Finset.le_sup (Finset.mem_univ i)))
  exact lt_of_le_of_lt hle (natCast_withBot_lt_top_consolidated155 _)

private theorem two_ne_zero_withBotENat_consolidated155 : (2 : WithBot ℕ∞) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ∞) : WithBot ℕ∞) = ((0 : ℕ∞) : WithBot ℕ∞) := h
  have h2 : (2 : ℕ∞) = 0 := WithBot.coe_injective h'
  simp at h2

private theorem two_mul_natCast_add_one_consolidated155 (m : ℕ) :
    (2 : WithBot ℕ∞) * ((m : ℕ∞) : WithBot ℕ∞) + 1 = (((2 * m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have e2 : (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := rfl
  have e1 : (1 : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) := rfl
  rw [e2, e1, ← WithBot.coe_mul, ← WithBot.coe_add]
  congr 1

private theorem two_mul_add_one_lt_top_consolidated155 {a : WithBot ℕ∞} (h : a ≠ ⊤) : 2 * a + 1 < ⊤ := by
  induction a using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.mul_bot two_ne_zero_withBotENat_consolidated155, WithBot.bot_add]
    exact bot_lt_top
  | coe b =>
    induction b using WithTop.recTopCoe with
    | top => exact absurd rfl h
    | coe m =>
      refine lt_of_eq_of_lt ?_ (natCast_withBot_lt_top_consolidated155 (2 * m + 1))
      exact two_mul_natCast_add_one_consolidated155 m

private theorem ringKrullDim_mvPolynomial_lt_top_consolidated155 (k : Type u) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) < ⊤ := by
  induction n with
  | zero =>
    have h0 : ((0 : ℕ) : WithBot ℕ∞) = 0 := Nat.cast_zero
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.isEmptyRingEquiv k (Fin 0)),
      ringKrullDim_eq_zero_of_field k, ← h0]
    exact natCast_withBot_lt_top_consolidated155 0
  | succ m ih =>
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.finSuccEquiv k m).toRingEquiv]
    exact lt_of_le_of_lt Polynomial.ringKrullDim_le (two_mul_add_one_lt_top_consolidated155 (ne_of_lt ih))

section
variable (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
include k

theorem ringKrullDim_lt_top_of_finiteType : ringKrullDim A < ⊤ := by
  obtain ⟨n, φ, hφ⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType k A›
  refine lt_of_le_of_lt (ringKrullDim_le_of_surjective φ.toRingHom hφ) ?_
  exact ringKrullDim_mvPolynomial_lt_top_consolidated155 k n

theorem topologicalKrullDim_primeSpectrum_lt_top : topologicalKrullDim (PrimeSpectrum A) < ⊤ := by
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_lt_top_of_finiteType k A


end

theorem topologicalKrullDim_spec_lt_top (k : Type u) [Field k] (R : CommRingCat.{v})
    [Algebra k R] [Algebra.FiniteType k R] : topologicalKrullDim ↥(Spec R) < ⊤ :=
  topologicalKrullDim_primeSpectrum_lt_top k R

section
variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (hft : LocallyOfFiniteType f)
include hft

private theorem topologicalKrullDim_affineOpen_lt_top_consolidated155 {U : X.Opens}
    (hU : IsAffineOpen U) : topologicalKrullDim ↥((U : Set ↥X)) < ⊤ := by
  have hle : U ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens) := le_top
  have hQ : RingHom.FiniteType ((f.appLE ⊤ U hle).hom) :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f hft
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of k))⟩ ⟨U, hU⟩ hle
  have hsurj : Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom := by
    intro y
    refine ⟨((Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom y, ?_⟩
    have hid := (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id
    exact congrArg (fun φ => (CommRingCat.Hom.hom φ) y) hid
  let _ : Algebra k Γ(X, U) :=
    RingHom.toAlgebra (((f.appLE ⊤ U hle).hom).comp
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom)
  have : Algebra.FiniteType k Γ(X, U) :=
    hQ.comp (RingHom.FiniteType.of_surjective _ hsurj)
  have e : ↥((U : Set ↥X)) ≃ₜ ↥(Spec Γ(X, U)) := Scheme.homeoOfIso hU.isoSpec
  exact topologicalKrullDim_lt_top_of_homeomorph_consolidated155 e (topologicalKrullDim_spec_lt_top k Γ(X, U))

theorem topologicalKrullDim_lt_top_of_finiteType (hqc : QuasiCompact f) :
    topologicalKrullDim ↥X < ⊤ := by
  classical
  have hcompact : IsCompact (Set.univ : Set ↥(Spec (CommRingCat.of k))) := by
    simp
  have : CompactSpace ↥X := by
    constructor
    have h := hqc.isCompact_preimage Set.univ isOpen_univ hcompact
    simpa using h
  have hcov : ⋃ i : X.affineOpens, ((i : X.Opens) : Set ↥X) = Set.univ := by
    rw [← Opens.coe_iSup, iSup_affineOpens_eq_top X, Opens.coe_top]
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i : X.affineOpens => ((i : X.Opens) : Set ↥X))
    (fun i => ((i : X.Opens)).isOpen) hcov.ge
  refine topologicalKrullDim_lt_top_of_finite_isOpenCover
    (ι := {i : X.affineOpens // i ∈ t})
    (fun i => ((i.1 : X.Opens) : Set ↥X)) (fun i => ((i.1 : X.Opens)).isOpen) ?_ ?_
  · refine Set.eq_univ_of_univ_subset ?_
    intro x _
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩
  · intro i
    exact topologicalKrullDim_affineOpen_lt_top_consolidated155 f hft i.1.2


end

theorem MarkedIdealWithBoundary.IsAdmissible.topologicalKrullDim_lt_top {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) :
    topologicalKrullDim ↥T.scheme < ⊤ :=
  topologicalKrullDim_lt_top_of_finiteType T.structMap hT.locallyOfFiniteType hT.quasiCompact

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupDimension
section

open CategoryTheory AlgebraicGeometry TopologicalSpace


section
variable {Y W : Scheme.{u}} (g : Y ⟶ W) [IsOpenImmersion g] (y : Y)

theorem ringKrullDim_stalk_eq_of_isOpenImmersion :
    ringKrullDim (Y.presheaf.stalk y) = ringKrullDim (W.presheaf.stalk (g.base y)) := by
  have : IsIso (g.stalkMap y) := inferInstance
  have e : (W.presheaf.stalk (g.base y)) ≅ (Y.presheaf.stalk y) := asIso (g.stalkMap y)
  exact (ringKrullDim_eq_of_ringEquiv e.commRingCatIsoToRingEquiv).symm

theorem isNoetherianRing_stalk_of_isOpenImmersion [IsNoetherianRing (W.presheaf.stalk (g.base y))] :
    IsNoetherianRing (Y.presheaf.stalk y) := by
  have : IsIso (g.stalkMap y) := inferInstance
  exact isNoetherianRing_of_ringEquiv _
    (CategoryTheory.asIso (g.stalkMap y)).commRingCatIsoToRingEquiv


end

section
variable {k : Type u} [Field k]

theorem ringKrullDim_stalk_le_of_etaleChart {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [IsLocallyNoetherian Y]
    {U : Y.Opens} {m : ℕ} (c : EtaleChart p U m) (y : Y) (hy : y ∈ U) :
    ringKrullDim (Y.presheaf.stalk y) ≤ ((m : ℕ∞) : WithBot ℕ∞) := by
  have := c.isEtale
  have hbase : U.ι.base (⟨y, hy⟩ : ↥U) = y := rfl
  have h0 : IsNoetherianRing (Y.presheaf.stalk (U.ι.base (⟨y, hy⟩ : ↥U))) := by
    rw [hbase]
    exact inferInstance
  have h1 : IsNoetherianRing (U.toScheme.presheaf.stalk (⟨y, hy⟩ : ↥U)) :=
    isNoetherianRing_stalk_of_isOpenImmersion U.ι (⟨y, hy⟩ : ↥U)
  have h2 := ringKrullDim_stalk_le_of_etale_affineSpace c.map (⟨y, hy⟩ : ↥U)
  have h3 := ringKrullDim_stalk_eq_of_isOpenImmersion U.ι (⟨y, hy⟩ : ↥U)
  rw [hbase] at h3
  rw [← h3]
  exact h2

theorem le_topologicalKrullDim_of_etaleChart {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (hU : (U : Set X).Nonempty) :
    ((m : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim ↥X := by
  have : Etale c.map := c.isEtale
  have : IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨x0, hx0⟩ := hU
  obtain ⟨V, hVaff, hxv, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := U.toScheme) (x := ⟨x0, hx0⟩) (U := ⊤) trivial
  obtain ⟨y, hy⟩ := exists_isClosed_singleton_of_isAffineOpen V hVaff ⟨_, hxv⟩
  have he1 : Etale (Scheme.Opens.ι V) := inferInstance
  have he2 : Etale (V.ι ≫ c.map) := inferInstance
  have : IsNoetherianRing (X.presheaf.stalk ((V.ι ≫ U.ι).base y)) := inferInstance
  have : IsNoetherianRing (V.toScheme.presheaf.stalk y) :=
    isNoetherianRing_stalk_of_isOpenImmersion (V.ι ≫ U.ι) y
  calc ((m : ℕ∞) : WithBot ℕ∞)
      = ringKrullDim (V.toScheme.presheaf.stalk y) :=
        (ringKrullDim_stalk_eq_of_etale_affineSpace (V.ι ≫ c.map) y hy).symm
    _ = ringKrullDim (X.presheaf.stalk ((V.ι ≫ U.ι).base y)) :=
        ringKrullDim_stalk_eq_of_isOpenImmersion (V.ι ≫ U.ι) y
    _ ≤ topologicalKrullDim ↥X :=
        ringKrullDim_stalk_le_topologicalKrullDim X ((V.ι ≫ U.ι).base y)


end

theorem ringKrullDim_stalk_eq_of_isBlowupAlongIdealSheaf_of_notMem {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (x₁ : X₁) (hx₁ : π.base x₁ ∉ Z.support) :
    ringKrullDim (X₁.presheaf.stalk x₁) = ringKrullDim (X.presheaf.stalk (π.base x₁)) := by
  obtain ⟨W, hWeq⟩ : ∃ W : X.Opens, (W : Set X) = (Z.support : Set X)ᶜ :=
    ⟨⟨(Z.support : Set X)ᶜ, Z.support.2.isOpen_compl⟩, rfl⟩
  have hW : ∀ x : X, x ∈ W → x ∉ Z.support := by
    intro x hxm
    have h2 : x ∈ (W : Set X) := hxm
    rw [hWeq] at h2
    exact h2
  have hxW : π.base x₁ ∈ W := by
    have h2 : π.base x₁ ∈ (Z.support : Set X)ᶜ := hx₁
    rw [← hWeq] at h2
    exact h2
  have hx : x₁ ∈ π ⁻¹ᵁ W := hxW
  have hiso : IsIso (π ∣_ W) := isIso_morphismRestrict_of_isBlowupAlongIdealSheaf hπ W hW
  have hoi : IsOpenImmersion (π ∣_ W) := inferInstance
  have e1 := ringKrullDim_stalk_eq_of_isOpenImmersion (Scheme.Opens.ι (π ⁻¹ᵁ W))
    (⟨x₁, hx⟩ : ↥(π ⁻¹ᵁ W))
  have e2 := ringKrullDim_stalk_eq_of_isOpenImmersion ((π ∣_ W) ≫ Scheme.Opens.ι W)
    (⟨x₁, hx⟩ : ↥(π ⁻¹ᵁ W))
  rw [morphismRestrict_ι] at e2
  exact e1.symm.trans e2

theorem topologicalKrullDim_le_of_blowup_strictNormalCrossings {k : Type u} [Field k] {X X₁ : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (π : X₁ ⟶ X) (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hZE : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    topologicalKrullDim ↥X₁ ≤ topologicalKrullDim ↥X := by
  have hXN : IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian p
  have hX₁N : IsLocallyNoetherian X₁ :=
    isLocallyNoetherian_of_isBlowupAlongIdealSheaf π Z hπ
  refine topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le X₁ _ ?_
  intro x₁
  by_cases hx : π.base x₁ ∈ Z.support
  · obtain ⟨U, hU, m, c, a, S, h1, h2, h3, h4⟩ := hZE.exists_etaleChart hx
    have hxU : x₁ ∈ π ⁻¹ᵁ U := hU
    obtain ⟨s, hs, hmem⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ h4 x₁ hxU
    have hle := ringKrullDim_stalk_le_of_etaleChart (π ≫ p)
      (blowupChartOfIsBlowup π c S hπ h4 s hs).chart x₁ hmem
    exact hle.trans (le_topologicalKrullDim_of_etaleChart p c ⟨π.base x₁, hU⟩)
  · rw [ringKrullDim_stalk_eq_of_isBlowupAlongIdealSheaf_of_notMem π Z hπ x₁ hx]
    exact ringKrullDim_stalk_le_topologicalKrullDim X (π.base x₁)

private theorem withBotSuccToNat_mono_of_lt_top_consolidated309 {a b : WithBot ℕ∞} (hab : a ≤ b) (hb : b < ⊤) :
    withBotSuccToNat a ≤ withBotSuccToNat b := by
  revert hab hb
  induction a using WithBot.recBotCoe with
  | bot =>
      intro _ _
      rw [withBotSuccToNat_bot]
      exact Nat.zero_le _
  | coe x =>
      induction b using WithBot.recBotCoe with
      | bot =>
          intro hab _
          exact absurd (le_bot_iff.mp hab) (by simp)
      | coe y =>
          intro hab hb
          have hy : y ≠ ⊤ := fun h => hb.ne (by simp [h])
          obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hy
          have hxy : x ≤ ((n : ℕ) : ℕ∞) := WithBot.coe_le_coe.mp hab
          have hx : x ≠ ⊤ := by
            intro h
            rw [h, top_le_iff] at hxy
            exact absurd hxy (by simp)
          obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hx
          have hmn : m ≤ n := by exact_mod_cast hxy
          rw [withBotSuccToNat_coe, withBotSuccToNat_coe]
          have h1 : ((m : ℕ) : ℕ∞).toNat = m := by simp
          have h2 : ((n : ℕ) : ℕ∞).toNat = n := by simp
          omega

theorem krullDimSucc_le_of_blowup_strictNormalCrossings {k : Type u} [Field k] {X X₁ : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    [QuasiCompact p]
    (π : X₁ ⟶ X) (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hZE : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    krullDimSucc X₁ ≤ krullDimSucc X := by
  have h1 : topologicalKrullDim ↥X₁ ≤ topologicalKrullDim ↥X :=
    topologicalKrullDim_le_of_blowup_strictNormalCrossings p π Z E hZE hπ
  have h2 : topologicalKrullDim ↥X < ⊤ :=
    topologicalKrullDim_lt_top_of_finiteType p inferInstance inferInstance
  simp only [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]
  exact withBotSuccToNat_mono_of_lt_top_consolidated309 h1 h2

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.ClosedImmersionKrullDim
section

open CategoryTheory AlgebraicGeometry TopologicalSpace


private theorem smooth_ker_subschemeι_comp_consolidated220 {k : Type u} [Field k] {X X' : Scheme.{u}}
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X')
    [IsClosedImmersion τ] [Smooth (τ ≫ p)] :
    Smooth (τ.ker.subschemeι ≫ p) := by
  have hinv : inv τ.toImage ≫ τ = τ.ker.subschemeι :=
    (IsIso.inv_comp_eq _).mpr τ.toImage_imageι.symm
  have hcomp : τ.ker.subschemeι ≫ p = inv τ.toImage ≫ (τ ≫ p) := by
    rw [← Category.assoc, hinv]
  rw [hcomp]
  infer_instance

theorem ker_le_map_idealSheaf {X X' : Scheme.{u}} (f : X ⟶ X') (I : X.IdealSheafData) :
    f.ker ≤ I.map f := by
  have hle : (⊥ : X.IdealSheafData).map f ≤ I.map f :=
    Scheme.IdealSheafData.map_mono f bot_le
  rwa [Scheme.IdealSheafData.map_bot] at hle

section
variable {k : Type u} [Field k]

theorem orderAt_map_le_one_of_isClosedImmersion [CharZero k]
    {X X' : Scheme.{u}} (p : X' ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (τ : X ⟶ X') [IsClosedImmersion τ]
    [Smooth (τ ≫ p)]
    (hker : NonzeroOnComponents τ.ker) (I : X.IdealSheafData) (x : ↥X') :
    orderAt (I.map τ) x ≤ 1 := by
  refine le_trans (orderAt_le_of_le (ker_le_map_idealSheaf τ I) x) ?_
  by_cases hx : x ∈ τ.ker.support
  · have : Smooth (τ.ker.subschemeι ≫ p) := smooth_ker_subschemeι_comp_consolidated220 p τ
    obtain ⟨U, m, c, S, hxU, hU, hD⟩ :=
      exists_chart_restrictIdeal_eq_coordIdeal p τ.ker x hx
    have hD' : τ.ker.comap U.ι = c.coordIdeal S := hD
    rcases S.eq_empty_or_nonempty with hS | ⟨j, hj⟩
    · subst hS
      exfalso
      have hcoord : c.coordIdeal (∅ : Finset (Fin m))
          = (⊥ : (affineSpaceFin k m).IdealSheafData).comap c.map := by
        rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_empty]
      have hUsupp : (U : Set ↥X') ⊆ (τ.ker.support : Set ↥X') := by
        intro y hy
        have hy' : y ∈ Set.range ⇑U.ι.base := by
          rw [Scheme.Opens.range_ι]
          exact hy
        obtain ⟨z, rfl⟩ := hy'
        have h1 : z ∈ ((τ.ker.comap U.ι).support : Set ↥U.toScheme) := by
          rw [hD', hcoord, support_comap_eq]
          simp [Scheme.IdealSheafData.support_bot]
        rw [support_comap_eq] at h1
        exact h1
      have hCmem : irreducibleComponent x ∈ irreducibleComponents ↥X' :=
        irreducibleComponent_mem_irreducibleComponents x
      refine hker _ hCmem ?_
      have hcl := closure_inter_open_eq (isClosed_irreducibleComponent)
        (isIrreducible_irreducibleComponent) U.2 ⟨x, mem_irreducibleComponent, hxU⟩
      rw [← hcl]
      refine closure_minimal ?_ (τ.ker.support).2
      exact fun y hy => hUsupp hy.2
    · exact orderAt_le_one_of_restrictIdeal_eq_coordIdeal p hU c S j hj τ.ker hD x hxU
  · have h0 : orderAt τ.ker x = 0 := (orderAt_eq_zero_iff_not_mem_support τ.ker x).mpr hx
    rw [h0]
    exact zero_le

theorem krullDimSucc_lt_of_isClosedImmersion_of_nonzeroOnComponents {X X' : Scheme.{u}} (p : X' ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [QuasiCompact p]
    (τ : X ⟶ X') [IsClosedImmersion τ] [Nonempty ↥X]
    (hker : NonzeroOnComponents τ.ker) :
    krullDimSucc X < krullDimSucc X' := by
  have hfin : topologicalKrullDim ↥X' < ⊤ :=
    topologicalKrullDim_lt_top_of_finiteType p ‹LocallyOfFiniteType p›
      ‹QuasiCompact p›
  have hemb : Topology.IsClosedEmbedding ⇑τ.base :=
    AlgebraicGeometry.Scheme.Hom.isClosedEmbedding τ
  obtain ⟨z⟩ := ‹Nonempty ↥X›
  refine krullDimSucc_lt_of_homeomorph_isClosed X' X (Set.range ⇑τ.base) hemb.isClosed_range
    ⟨τ.base z, z, rfl⟩ ?_ hfin hemb.toIsEmbedding.toHomeomorph
  intro C hC hsub
  exact hker C hC (hsub.trans τ.range_subset_ker_support)


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section

def kerSubschemeIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] : (Scheme.Hom.ker f).subscheme ≅ X :=
  (asIso (Scheme.Hom.toImage f)).symm

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

theorem kerSubschemeIso_hom_comp :
    (kerSubschemeIso f).hom ≫ f = (Scheme.Hom.ker f).subschemeι := by
  have key := IsIso.inv_hom_id_assoc (Scheme.Hom.toImage f) (Scheme.Hom.imageι f)
  rw [Scheme.Hom.toImage_imageι] at key
  exact key

theorem kerSubschemeIso_inv_comp :
    (kerSubschemeIso f).inv ≫ (Scheme.Hom.ker f).subschemeι = f := by
  rw [← kerSubschemeIso_hom_comp f, Iso.inv_hom_id_assoc]


end

namespace MarkedIdealWithBoundary

def pullbackAlong (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) : MarkedIdealWithBoundary.{u} where
  base := T.base
  instField := T.instField
  scheme := Y
  structMap := q
  ideal := T.ideal.comap h
  mult := T.mult
  boundary := T.boundary.map (fun D => D.comap h)

section
variable (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)

@[simp] theorem pullbackAlong_mult :
    (T.pullbackAlong Y q h).mult = T.mult := rfl

theorem pullbackAlong_structureMorphism :
    (T.pullbackAlong Y q h).structMap = q := rfl

theorem pullbackAlong_ideal :
    (T.pullbackAlong Y q h).ideal = T.ideal.comap h := rfl

theorem pullbackAlong_boundary :
    (T.pullbackAlong Y q h).boundary = T.boundary.map (fun D => D.comap h) := rfl


end

def baseChange (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] (f : T.base →+* L) :
    MarkedIdealWithBoundary.{u} where
  base := L
  scheme := pullback T.structMap (specMapOfFieldHom T.base L f)
  structMap := pullback.snd T.structMap (specMapOfFieldHom T.base L f)
  ideal := T.ideal.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
  mult := T.mult
  boundary :=
    T.boundary.map (fun D => D.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f)))

section
variable (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] (f : T.base →+* L)

@[simp] theorem baseChange_mult : (T.baseChange L f).mult = T.mult := rfl

theorem baseChange_structureMorphism :
    (T.baseChange L f).structMap = pullback.snd T.structMap (specMapOfFieldHom T.base L f) := rfl

theorem baseChange_ideal :
    (T.baseChange L f).ideal =
      T.ideal.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) := rfl

theorem baseChange_boundary :
    (T.baseChange L f).boundary =
      T.boundary.map
        (fun D => D.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f))) := rfl


end

def withSchemeIdealBoundary (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base))
    (J : Y.IdealSheafData) (E : List Y.IdealSheafData) : MarkedIdealWithBoundary.{u} where
  base := T.base
  instField := T.instField
  scheme := Y
  structMap := q
  ideal := J
  mult := T.mult
  boundary := E

section
variable (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (J : Y.IdealSheafData) (E : List Y.IdealSheafData)

@[simp] theorem withSchemeIdealBoundary_mult : (T.withSchemeIdealBoundary Y q J E).mult = T.mult := rfl

theorem withSchemeIdealBoundary_structureMorphism : (T.withSchemeIdealBoundary Y q J E).structMap = q := rfl

theorem withSchemeIdealBoundary_ideal : (T.withSchemeIdealBoundary Y q J E).ideal = J := rfl


end

def withBoundary (T : MarkedIdealWithBoundary.{u}) (E : List T.scheme.IdealSheafData) :
    MarkedIdealWithBoundary.{u} where
  base := T.base
  instField := T.instField
  scheme := T.scheme
  structMap := T.structMap
  ideal := T.ideal
  mult := T.mult
  boundary := E

section
variable (T : MarkedIdealWithBoundary.{u}) (E : List T.scheme.IdealSheafData)

@[simp] theorem withBoundary_ideal :
    (T.withBoundary E).ideal = T.ideal := rfl

@[simp] theorem withBoundary_mult :
    (T.withBoundary E).mult = T.mult := rfl

@[simp] theorem withBoundary_boundary : (T.withBoundary E).boundary = E := rfl

@[simp] theorem withBoundary_dim :
    (T.withBoundary E).krullDimSucc = T.krullDimSucc := rfl


end

@[simp] theorem withBoundary_self (T : MarkedIdealWithBoundary.{u}) :
    T.withBoundary T.boundary = T := rfl

def nontrivialPart {X : Scheme.{u}} (E : List X.IdealSheafData) : List X.IdealSheafData :=
  E.filter (fun D => !(@decide (D = ⊤) (Classical.propDecidable _)))

def SameNontrivialBoundary {X : Scheme.{u}} (E E' : List X.IdealSheafData) : Prop :=
  nontrivialPart E = nontrivialPart E'

section
variable {X : Scheme.{u}}

theorem sameNontrivialBoundary_iff (E E' : List X.IdealSheafData) :
    SameNontrivialBoundary E E' ↔ nontrivialPart E = nontrivialPart E' := Iff.rfl

theorem SameNontrivialBoundary.refl (E : List X.IdealSheafData) :
    SameNontrivialBoundary E E := rfl

theorem SameNontrivialBoundary.symm {E E' : List X.IdealSheafData}
    (h : SameNontrivialBoundary E E') : SameNontrivialBoundary E' E := Eq.symm h

theorem SameNontrivialBoundary.trans {E E' E'' : List X.IdealSheafData}
    (h : SameNontrivialBoundary E E') (h' : SameNontrivialBoundary E' E'') : SameNontrivialBoundary E E'' := Eq.trans h h'

theorem nontrivialPart_append (A B : List X.IdealSheafData) :
    nontrivialPart (A ++ B) = nontrivialPart A ++ nontrivialPart B := by
  simp [nontrivialPart, List.filter_append]

theorem SameNontrivialBoundary.append {L₁ L₁' L₂ L₂' : List X.IdealSheafData}
    (h₁ : SameNontrivialBoundary L₁ L₁') (h₂ : SameNontrivialBoundary L₂ L₂') :
    SameNontrivialBoundary (L₁ ++ L₂) (L₁' ++ L₂') := by
  have e₁ : nontrivialPart L₁ = nontrivialPart L₁' := h₁
  have e₂ : nontrivialPart L₂ = nontrivialPart L₂' := h₂
  show nontrivialPart (L₁ ++ L₂) = nontrivialPart (L₁' ++ L₂')
  rw [nontrivialPart_append, nontrivialPart_append, e₁, e₂]


end

section
variable {X Y : Scheme.{u}} (f : X.IdealSheafData → Y.IdealSheafData) (hf : f ⊤ = ⊤)
include hf

private theorem nontrivialPart_map_nontrivialPart_consolidated142 (L : List X.IdealSheafData) :
    nontrivialPart ((nontrivialPart L).map f) = nontrivialPart (L.map f) := by
  have hcons_top : ∀ {Z : Scheme.{u}} {a : Z.IdealSheafData}, a = ⊤ →
      ∀ M : List Z.IdealSheafData, nontrivialPart (a :: M) = nontrivialPart M := by
    intro Z a ha M
    have hb : (@decide (a = ⊤) (Classical.propDecidable (a = ⊤))) = true := by simp [ha]
    simp [nontrivialPart, hb]
  have hcons_ne : ∀ {Z : Scheme.{u}} {a : Z.IdealSheafData}, ¬ a = ⊤ →
      ∀ M : List Z.IdealSheafData, nontrivialPart (a :: M) = a :: nontrivialPart M := by
    intro Z a ha M
    have hb : (@decide (a = ⊤) (Classical.propDecidable (a = ⊤))) = false := by simp [ha]
    simp [nontrivialPart, hb]
  induction L with
  | nil => simp [nontrivialPart]
  | cons a L ih =>
    by_cases ha : a = ⊤
    · have hfa : f a = ⊤ := by rw [ha]; exact hf
      rw [hcons_top ha L, List.map_cons, hcons_top hfa (L.map f), ih]
    · by_cases hfa : f a = ⊤
      · rw [hcons_ne ha L, List.map_cons, List.map_cons,
          hcons_top hfa ((nontrivialPart L).map f), hcons_top hfa (L.map f), ih]
      · rw [hcons_ne ha L, List.map_cons, List.map_cons,
          hcons_ne hfa ((nontrivialPart L).map f), hcons_ne hfa (L.map f), ih]

theorem SameNontrivialBoundary.map {L L' : List X.IdealSheafData} (h : SameNontrivialBoundary L L') :
    SameNontrivialBoundary (L.map f) (L'.map f) := by
  have e : nontrivialPart L = nontrivialPart L' := h
  show nontrivialPart (L.map f) = nontrivialPart (L'.map f)
  rw [← nontrivialPart_map_nontrivialPart_consolidated142 f hf L, ← nontrivialPart_map_nontrivialPart_consolidated142 f hf L', e]


end

def AdmissibleUnderBoundaryReplacement : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}) (E' : List T.scheme.IdealSheafData), T.IsAdmissible →
    SameNontrivialBoundary T.boundary E' → (T.withBoundary E').IsAdmissible

def IsOrderBoundedByMult (T : MarkedIdealWithBoundary.{u}) : Prop :=
  ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)

theorem isOrderBoundedByMult_iff (T : MarkedIdealWithBoundary.{u}) :
    T.IsOrderBoundedByMult ↔ ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞) := Iff.rfl

def IsBalanced (T : MarkedIdealWithBoundary.{u})
    (hft : LocallyOfFiniteType T.structMap) : Prop :=
  haveI : LocallyOfFiniteType T.structMap := hft
  haveI : IsNoetherianRing T.base := inferInstance
  IsDerivBalanced T.base T.structMap T.ideal T.mult

end MarkedIdealWithBoundary

namespace MarkedSequenceOfBlowups

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def boundaryLocus (s : MarkedSequenceOfBlowups p I m E) (t : ℕ) : Set ↥(s.toSequenceOfBlowups.schemeAt t) :=
  ⋃ D ∈ s.boundary t, ((D.support : Set ↥(s.toSequenceOfBlowups.schemeAt t)))

theorem mem_boundaryLocus_iff (s : MarkedSequenceOfBlowups p I m E) (t : ℕ)
    (x : ↥(s.toSequenceOfBlowups.schemeAt t)) :
    x ∈ s.boundaryLocus t ↔
      ∃ D ∈ s.boundary t, x ∈ ((D.support : Set ↥(s.toSequenceOfBlowups.schemeAt t))) := by
  constructor
  · intro hx
    have hx' : x ∈ ⋃ D ∈ s.boundary t, ((D.support : Set ↥(s.toSequenceOfBlowups.schemeAt t))) := hx
    obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.mp hx'
    exact ⟨D, hD, hxD⟩
  · rintro ⟨D, hD, hxD⟩
    have hx' : x ∈ ⋃ D ∈ s.boundary t, ((D.support : Set ↥(s.toSequenceOfBlowups.schemeAt t))) :=
      Set.mem_iUnion₂.mpr ⟨D, hD, hxD⟩
    exact hx'

def otherBoundaryLocus (s : MarkedSequenceOfBlowups p I m E) (j t : ℕ) :
    Set ↥(s.toSequenceOfBlowups.schemeAt t) :=
  ⋃ (i : Fin (s.boundary t).length) (_ : (i : ℕ) ≠ j),
    (((s.boundary t).get i).support : Set ↥(s.toSequenceOfBlowups.schemeAt t))

theorem mem_otherBoundaryLocus_iff (s : MarkedSequenceOfBlowups p I m E) (j t : ℕ)
    (x : ↥(s.toSequenceOfBlowups.schemeAt t)) :
    x ∈ s.otherBoundaryLocus j t ↔
      ∃ i : Fin (s.boundary t).length, (i : ℕ) ≠ j ∧
        x ∈ (((s.boundary t).get i).support : Set ↥(s.toSequenceOfBlowups.schemeAt t)) := by
  constructor
  · intro hx
    have hx' : x ∈ ⋃ (i : Fin (s.boundary t).length) (_ : (i : ℕ) ≠ j),
        (((s.boundary t).get i).support : Set ↥(s.toSequenceOfBlowups.schemeAt t)) := hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx'
    exact ⟨i, hi, hxi⟩
  · rintro ⟨i, hi, hxi⟩
    have hx' : x ∈ ⋃ (i : Fin (s.boundary t).length) (_ : (i : ℕ) ≠ j),
        (((s.boundary t).get i).support : Set ↥(s.toSequenceOfBlowups.schemeAt t)) :=
      Set.mem_iUnion₂.mpr ⟨i, hi, hxi⟩
    exact hx'

end MarkedSequenceOfBlowups

structure IsMaxOrderReduction (P : ℕ → Prop) (A B : PrincipalizationAssignment.{u}) : Prop where
  cert : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
    ∀ i, i < (A T).toSequenceOfBlowups.length →
      PrincipalizationCertificate ((A T).toSequenceOfBlowups.schemeAt i) ((A T).projectionToSpec i) ((A T).ideal i) T.mult
        ((A T).boundaryLocus i) ((A T).toSequenceOfBlowups.center i)
  orderRed_equiv : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
    T.boundary = [] → T.IsOrderBoundedByMult →
    (A T).toSequenceOfBlowups.Isomorphic (B T).toSequenceOfBlowups
  base_change : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.baseChange L f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
      ((T.baseChange L f).withBoundary E').IsAdmissible →
      P ((T.baseChange L f).withBoundary E').krullDimSucc →
      IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (A ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups (A T).toSequenceOfBlowups
  base_change_strict : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.baseChange L f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
      ((T.baseChange L f).withBoundary E').IsAdmissible →
      P ((T.baseChange L f).withBoundary E').krullDimSucc →
      IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (A ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups (A T).toSequenceOfBlowups
  center_nonempty : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
    ∀ i, i < (A T).toSequenceOfBlowups.length →
      (((A T).toSequenceOfBlowups.center i).support : Set ↥((A T).toSequenceOfBlowups.schemeAt i)).Nonempty
  resolves : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → (A T).IsResolution
  smooth_pullback : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
    ∀ E' : List Y.IdealSheafData,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
      ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
      P ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc →
      IsPullbackBlowupSequence h (A ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  smooth_pullback_strict : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h] [AlgebraicGeometry.Surjective h], h ≫ T.structMap = q →
    ∀ E' : List Y.IdealSheafData,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
      ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
      P ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc →
      IsStrictPullbackBlowupSeq h (A ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  trivial_of_coSupport_empty : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
    orderAtLeastLocus T.ideal T.mult = ∅ → (A T).toSequenceOfBlowups.length = 0

theorem isMaxOrderReduction_of_forall_not (P : ℕ → Prop) (hP : ∀ n, ¬ P n)
    (A B : PrincipalizationAssignment.{u}) : IsMaxOrderReduction P A B := by
  constructor <;> exact fun T _ hd => absurd hd (hP T.krullDimSucc)

theorem IsMaxOrderReduction.mono {P : ℕ → Prop} {A B : PrincipalizationAssignment.{u}}
    (hs : IsMaxOrderReduction P A B) (Q : ℕ → Prop) (hQP : ∀ n, Q n → P n) :
    IsMaxOrderReduction Q A B := by
  constructor
  · intro T hV hQ
    exact hs.cert T hV (hQP _ hQ)
  · intro T hV hQ
    exact hs.orderRed_equiv T hV (hQP _ hQ)
  · intro T hV hQ L _ _ f E' hBE hV' hQ'
    exact hs.base_change T hV (hQP _ hQ) L f E' hBE hV' (hQP _ hQ')
  · intro T hV hQ L _ _ f E' hBE hV' hQ'
    exact hs.base_change_strict T hV (hQP _ hQ) L f E' hBE hV' (hQP _ hQ')
  · intro T hV hQ
    exact hs.center_nonempty T hV (hQP _ hQ)
  · intro T hV hQ
    exact hs.resolves T hV (hQP _ hQ)
  · intro T hV hQ Y q h _ hq E' hBE hV' hQ'
    exact hs.smooth_pullback T hV (hQP _ hQ) Y q h hq E' hBE hV' (hQP _ hQ')
  · intro T hV hQ Y q h _ _ hq E' hBE hV' hQ'
    exact hs.smooth_pullback_strict T hV (hQP _ hQ) Y q h hq E' hBE hV' (hQP _ hQ')
  · intro T hV hQ
    exact hs.trivial_of_coSupport_empty T hV (hQP _ hQ)

section
variable {P : ℕ → Prop} {A B : PrincipalizationAssignment.{u}} (hs : IsMaxOrderReduction P A B) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : P T.krullDimSucc) (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [Smooth h]
include hs hV hP

theorem IsMaxOrderReduction.isPullbackBlowupSequence_of_smooth (hq : h ≫ T.structMap = q)
    (hV' : (T.pullbackAlong Y q h).IsAdmissible) (hP' : P (T.pullbackAlong Y q h).krullDimSucc) :
    IsPullbackBlowupSequence h (A (T.pullbackAlong Y q h)).toSequenceOfBlowups (A T).toSequenceOfBlowups :=
  hs.smooth_pullback T hV hP Y q h hq (T.pullbackAlong Y q h).boundary
    (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _) hV' hP'

theorem IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective [AlgebraicGeometry.Surjective h] (hq : h ≫ T.structMap = q)
    (hV' : (T.pullbackAlong Y q h).IsAdmissible) (hP' : P (T.pullbackAlong Y q h).krullDimSucc) :
    IsStrictPullbackBlowupSeq h (A (T.pullbackAlong Y q h)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by
  exact hs.smooth_pullback_strict T hV hP Y q h hq (T.pullbackAlong Y q h).boundary
    (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _) hV' hP'


end

section
variable {P : ℕ → Prop} {A B : PrincipalizationAssignment.{u}} (hs : IsMaxOrderReduction P A B) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : P T.krullDimSucc) (L : Type u) [Field L] [CharZero L] (f : T.base →+* L) (hV' : (T.baseChange L f).IsAdmissible) (hP' : P (T.baseChange L f).krullDimSucc)
include hs hV hP hV' hP'

theorem IsMaxOrderReduction.isPullbackBlowupSequence_baseChange :
    IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
      (A (T.baseChange L f)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by
  exact hs.base_change T hV hP L f (T.baseChange L f).boundary
    (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _) hV' hP'

theorem IsMaxOrderReduction.isStrictPullbackBlowupSeq_baseChange :
    IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
      (A (T.baseChange L f)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by
  exact hs.base_change_strict T hV hP L f (T.baseChange L f).boundary
    (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _) hV' hP'


end

structure IsOrderReduction (P : ℕ → Prop) (A B : PrincipalizationAssignment.{u}) : Prop where
  cert : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ i, i < (A T).toSequenceOfBlowups.length →
      OrderCertificate ((A T).toSequenceOfBlowups.schemeAt i) ((A T).projectionToSpec i) ((A T).ideal i) T.mult
        ((A T).boundaryLocus i) ((A T).toSequenceOfBlowups.center i)
  base_change : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.baseChange L f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
      ((T.baseChange L f).withBoundary E').IsAdmissible →
      P ((T.baseChange L f).withBoundary E').krullDimSucc →
      ((T.baseChange L f).withBoundary E').IsOrderBoundedByMult →
      IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (A ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups (A T).toSequenceOfBlowups
  base_change_strict : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.baseChange L f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
      ((T.baseChange L f).withBoundary E').IsAdmissible →
      P ((T.baseChange L f).withBoundary E').krullDimSucc →
      ((T.baseChange L f).withBoundary E').IsOrderBoundedByMult →
      IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (A ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups (A T).toSequenceOfBlowups
  pushforward : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.boundary = [] → T.mult = 1 →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (e : Y ⟶ T.scheme)
      [IsClosedImmersion e], e ≫ T.structMap = q →
      IsSmoothDivisor T.structMap (Scheme.Hom.ker e) →
    ∀ J : Y.IdealSheafData,
      (T.withSchemeIdealBoundary Y q J ([] : List Y.IdealSheafData)).IsAdmissible →
      (T.withSchemeIdealBoundary Y q J ([] : List Y.IdealSheafData)).krullDimSucc < T.krullDimSucc →
      T.ideal = imageIdealSheaf e J →
      IsPushforwardBlowupSeq e (B (T.withSchemeIdealBoundary Y q J ([] : List Y.IdealSheafData))).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  order_le : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ i, i ≤ (A T).toSequenceOfBlowups.length →
      ∀ x : ↥((A T).toSequenceOfBlowups.schemeAt i), orderAt ((A T).ideal i) x ≤ (T.mult : ℕ∞)
  center_nonempty : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ i, i < (A T).toSequenceOfBlowups.length →
      (((A T).toSequenceOfBlowups.center i).support : Set ↥((A T).toSequenceOfBlowups.schemeAt i)).Nonempty
  resolves : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult → (A T).IsResolution
  smooth_pullback : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
    ∀ E' : List Y.IdealSheafData,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
      ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
      P ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc →
      ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult →
      IsPullbackBlowupSequence h (A ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  smooth_pullback_strict : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h] [AlgebraicGeometry.Surjective h], h ≫ T.structMap = q →
    ∀ E' : List Y.IdealSheafData,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
      ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
      P ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc →
      ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult →
      IsStrictPullbackBlowupSeq h (A ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  trivial_of_coSupport_empty : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    orderAtLeastLocus T.ideal T.mult = ∅ → (A T).toSequenceOfBlowups.length = 0

structure IsBoundaryDivisorReduction (P : ℕ → Prop) (j : ℕ) (A B : PrincipalizationAssignment.{u}) : Prop where
  base_change : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.baseChange L f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
      E'.take (j + 1) = (T.baseChange L f).boundary.take (j + 1) →
    ∀ hV' : ((T.baseChange L f).withBoundary E').IsAdmissible,
      P ((T.baseChange L f).withBoundary E').krullDimSucc →
      ((T.baseChange L f).withBoundary E').IsOrderBoundedByMult →
      ((T.baseChange L f).withBoundary E').IsBalanced hV'.locallyOfFiniteType →
      j < ((T.baseChange L f).withBoundary E').boundary.length →
      IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (A ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups (A T).toSequenceOfBlowups
  base_change_strict : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.baseChange L f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
      E'.take (j + 1) = (T.baseChange L f).boundary.take (j + 1) →
    ∀ hV' : ((T.baseChange L f).withBoundary E').IsAdmissible,
      P ((T.baseChange L f).withBoundary E').krullDimSucc →
      ((T.baseChange L f).withBoundary E').IsOrderBoundedByMult →
      ((T.baseChange L f).withBoundary E').IsBalanced hV'.locallyOfFiniteType →
      j < ((T.baseChange L f).withBoundary E').boundary.length →
      IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (A ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups (A T).toSequenceOfBlowups
  order_le : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    ∀ i, i ≤ (A T).toSequenceOfBlowups.length →
      ∀ x : ↥((A T).toSequenceOfBlowups.schemeAt i), orderAt ((A T).ideal i) x ≤ (T.mult : ℕ∞)
  center_nonempty : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    ∀ i, i < (A T).toSequenceOfBlowups.length →
      (((A T).toSequenceOfBlowups.center i).support : Set ↥((A T).toSequenceOfBlowups.schemeAt i)).Nonempty
  pushforward : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ hj : j < T.boundary.length, T.mult = 1 →
    ∀ J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData,
      (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          ((T.boundary.eraseIdx j).map
            (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι))).IsAdmissible →
      (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          ((T.boundary.eraseIdx j).map
            (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι))).krullDimSucc < T.krullDimSucc →
      T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J →
      IsPushforwardBlowupSeq (T.boundary.get ⟨j, hj⟩).subschemeι
        (B (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
            ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
            ((T.boundary.eraseIdx j).map
              (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)))).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  shape : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ hj : j < T.boundary.length,
    ∃ (D : ∀ t : ℕ, ((A T).toSequenceOfBlowups.schemeAt t).IdealSheafData) (b : Bool),
      (∀ t ≤ (A T).toSequenceOfBlowups.length, IsSmoothDivisor ((A T).projectionToSpec t) (D t)) ∧
      D 0 = (T.boundary.get ⟨j, hj⟩).comap (A T).toSequenceOfBlowups.isoZero.hom ∧
      (∀ t < (A T).toSequenceOfBlowups.length,
        (((A T).toSequenceOfBlowups.center t).support : Set ↥((A T).toSequenceOfBlowups.schemeAt t)) ⊆
          (((D t).support : Set ↥((A T).toSequenceOfBlowups.schemeAt t)))) ∧
      (b = true →
        0 < (A T).toSequenceOfBlowups.length ∧
        IsOpen ((D 0).subschemeι.base ⁻¹'
          ((((A T).toSequenceOfBlowups.center 0).support : Set ↥((A T).toSequenceOfBlowups.schemeAt 0)))) ∧
        D 1 = (D 0).comap ((A T).toSequenceOfBlowups.transitionMapSucc 0)) ∧
      (∀ t < (A T).toSequenceOfBlowups.length, ¬ (b = true ∧ t = 0) →
        D (t + 1) = Blowup.strictTransform ((A T).toSequenceOfBlowups.transitionMapSucc t)
          ((A T).toSequenceOfBlowups.center t) (D t)) ∧
      (orderAtLeastLocus (A T).lastIdeal T.mult ∩
        (((D (A T).toSequenceOfBlowups.length).support :
          Set ↥((A T).toSequenceOfBlowups.schemeAt (A T).toSequenceOfBlowups.length)))) = ∅ ∧
      (∀ t < (A T).toSequenceOfBlowups.length, ¬ (b = true ∧ t = 0) →
        ∃ J : (D t).subscheme.IdealSheafData,
          NonzeroOnComponents J ∧
          (∀ x : ↥(D t).subscheme,
            (D t).subschemeι.base x ∉ (A T).otherBoundaryLocus j t →
            ∃ V : (D t).subscheme.Opens, x ∈ V ∧
              J.comap V.ι = (((A T).ideal t).comap (D t).subschemeι).comap V.ι) ∧
          PrincipalizationCertificate (D t).subscheme ((D t).subschemeι ≫ (A T).projectionToSpec t) J T.mult
            ((D t).subschemeι.base ⁻¹' (A T).otherBoundaryLocus j t)
            (((A T).toSequenceOfBlowups.center t).comap (D t).subschemeι))
  smooth_pullback : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
    ∀ E' : List Y.IdealSheafData,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
      E'.take (j + 1) = (T.pullbackAlong Y q h).boundary.take (j + 1) →
    ∀ hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible,
      P ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc →
      ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult →
      ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType →
      j < ((T.pullbackAlong Y q h).withBoundary E').boundary.length →
      IsPullbackBlowupSequence h (A ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  smooth_pullback_strict : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h] [AlgebraicGeometry.Surjective h], h ≫ T.structMap = q →
    ∀ E' : List Y.IdealSheafData,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
      E'.take (j + 1) = (T.pullbackAlong Y q h).boundary.take (j + 1) →
    ∀ hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible,
      P ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc →
      ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult →
      ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType →
      j < ((T.pullbackAlong Y q h).withBoundary E').boundary.length →
      IsStrictPullbackBlowupSeq h (A ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  trivial_of_coSupport_empty : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), P T.krullDimSucc →
    T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    orderAtLeastLocus T.ideal T.mult = ∅ → (A T).toSequenceOfBlowups.length = 0

section
variable {P : ℕ → Prop} {j : ℕ} {A B : PrincipalizationAssignment.{u}} (hs : IsBoundaryDivisorReduction P j A B) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : P T.krullDimSucc) (hO : T.IsOrderBoundedByMult) (hD : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
include hs hP hO hD hj

theorem IsBoundaryDivisorReduction.isPullbackBlowupSequence_of_smooth (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [Smooth h] (hq : h ≫ T.structMap = q)
    (hV' : (T.pullbackAlong Y q h).IsAdmissible) (hP' : P (T.pullbackAlong Y q h).krullDimSucc)
    (hO' : (T.pullbackAlong Y q h).IsOrderBoundedByMult)
    (hD' : (T.pullbackAlong Y q h).IsBalanced hV'.locallyOfFiniteType)
    (hj' : j < (T.pullbackAlong Y q h).boundary.length) :
    IsPullbackBlowupSequence h (A (T.pullbackAlong Y q h)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by
  exact hs.smooth_pullback T hV hP hO hD hj Y q h hq (T.pullbackAlong Y q h).boundary
    (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _) rfl hV' hP' hO' hD' hj'

theorem IsBoundaryDivisorReduction.isStrictPullbackBlowupSeq_of_smooth_surjective (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [Smooth h] [AlgebraicGeometry.Surjective h] (hq : h ≫ T.structMap = q)
    (hV' : (T.pullbackAlong Y q h).IsAdmissible) (hP' : P (T.pullbackAlong Y q h).krullDimSucc)
    (hO' : (T.pullbackAlong Y q h).IsOrderBoundedByMult)
    (hD' : (T.pullbackAlong Y q h).IsBalanced hV'.locallyOfFiniteType)
    (hj' : j < (T.pullbackAlong Y q h).boundary.length) :
    IsStrictPullbackBlowupSeq h (A (T.pullbackAlong Y q h)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by
  exact hs.smooth_pullback_strict T hV hP hO hD hj Y q h hq (T.pullbackAlong Y q h).boundary
    (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _) rfl hV' hP' hO' hD' hj'

theorem IsBoundaryDivisorReduction.isStrictPullbackBlowupSeq_baseChange (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
    (hV' : (T.baseChange L f).IsAdmissible) (hP' : P (T.baseChange L f).krullDimSucc)
    (hO' : (T.baseChange L f).IsOrderBoundedByMult)
    (hD' : (T.baseChange L f).IsBalanced hV'.locallyOfFiniteType)
    (hj' : j < (T.baseChange L f).boundary.length) :
    IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
      (A (T.baseChange L f)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by
  exact hs.base_change_strict T hV hP hO hD hj L f (T.baseChange L f).boundary
    (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _) rfl hV' hP' hO' hD' hj'


end

structure IsBoundaryPositionInvariant (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u}) : Prop where
  shift : ∀ (T : MarkedIdealWithBoundary.{u}), P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ hft : LocallyOfFiniteType T.structMap, T.IsBalanced hft →
    ∀ (E₁ E₂ E₁' E₂' : List T.scheme.IdealSheafData) (D : T.scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary E₁ E₁' → MarkedIdealWithBoundary.SameNontrivialBoundary E₂ E₂' →
      (T.withBoundary (E₁ ++ D :: E₂)).IsAdmissible →
      (T.withBoundary (E₁' ++ D :: E₂')).IsAdmissible →
      ((A E₁.length) (T.withBoundary (E₁ ++ D :: E₂))).toSequenceOfBlowups.Isomorphic
        ((A E₁'.length) (T.withBoundary (E₁' ++ D :: E₂'))).toSequenceOfBlowups

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
section

open CategoryTheory AlgebraicGeometry

section

namespace MonomialCenter

def sortedIndices {n : ℕ} (J : Finset (Fin n)) : List ℕ :=
  (J.sort (· ≤ ·)).map Fin.val

section
variable {n : ℕ} (J : Finset (Fin n))

theorem sortedIndices_eq_map_sort :
    sortedIndices J = (J.sort (· ≤ ·)).map Fin.val := rfl

theorem mem_sortedIndices (a : ℕ) :
    a ∈ sortedIndices J ↔ ∃ j ∈ J, (j : ℕ) = a := by
  simp [sortedIndices, List.mem_map, Finset.mem_sort]


end

structure CenterInvariant (n : ℕ) : Type where
  positions : Finset (Fin n)
  rank : ℕ
  value : ℕ∞

def CenterInvariant.sortedIndices {n : ℕ} (K : CenterInvariant n) : List ℕ :=
  _root_.FunctorialResolution.EmbeddedResolution.MonomialCenter.sortedIndices K.positions

def CenterInvariant.Lt {n n' : ℕ} (K : CenterInvariant n) (K' : CenterInvariant n') : Prop :=
  K.rank < K'.rank ∨
    (K.rank = K'.rank ∧
      (K'.value < K.value ∨
        (K.value = K'.value ∧
          List.Lex (· < ·) K.sortedIndices K'.sortedIndices)))

def CenterInvariant.Le {n n' : ℕ} (K : CenterInvariant n) (K' : CenterInvariant n') : Prop :=
  K.Lt K' ∨
    (K.rank = K'.rank ∧ K.value = K'.value ∧ K.sortedIndices = K'.sortedIndices)

def centerInvariant {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) :
    CenterInvariant L.length where
  positions := lexMaxIndices I m L
  rank := minIndexCard I m L
  value := maxCandidateOrder I m L

end MonomialCenter


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CoordinateSubspaceIdeal
section

open CategoryTheory AlgebraicGeometry

section

namespace MonomialChart

theorem comap_biSup_finset {X Y : Scheme.{u}} {ι : Type v} (f : X ⟶ Y)
    (I : ι → Y.IdealSheafData) (S : Finset ι) :
    (⨆ j ∈ S, I j).comap f = ⨆ j ∈ S, (I j).comap f := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.iSup_insert, Finset.iSup_insert, Scheme.IdealSheafData.comap_sup, ih]

section
variable {X : Scheme.{u}}

theorem restrictIdeal_biSup_finset {ι : Type v} (U : X.Opens)
    (I : ι → X.IdealSheafData) (S : Finset ι) :
    restrictIdeal (⨆ j ∈ S, I j) U = ⨆ j ∈ S, restrictIdeal (I j) U :=
  comap_biSup_finset U.ι I S

private theorem ofIdealTop_sup_consolidated252 [IsAffine X] (I J : Ideal Γ(X, ⊤)) :
    Scheme.IdealSheafData.ofIdealTop (I ⊔ J) =
      Scheme.IdealSheafData.ofIdealTop I ⊔ Scheme.IdealSheafData.ofIdealTop J := by
  ext U : 2
  simp [Scheme.IdealSheafData.ofIdealTop, Ideal.map_sup]


end

section
variable (k : Type u) [Field k] (m : ℕ)

theorem coordSubspaceIdeal_insert (j : Fin m)
    (S : Finset (Fin m)) :
    coordSubspaceIdeal k m (insert j S) =
      coordSubspaceIdeal k m {j} ⊔ coordSubspaceIdeal k m S := by
  classical
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, coordSubspaceIdeal_eq_ofIdealTop_span_coord, coordSubspaceIdeal_eq_ofIdealTop_span_coord,
    Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert, Finset.coe_singleton,
    Set.image_singleton, ofIdealTop_sup_consolidated252]

theorem coordSubspaceIdeal_eq_biSup_singleton (S : Finset (Fin m)) :
    coordSubspaceIdeal k m S = ⨆ j ∈ S, coordSubspaceIdeal k m {j} := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp [coordSubspaceIdeal_empty]
  · intro a s _ ih
    rw [coordSubspaceIdeal_insert, ih, Finset.iSup_insert]


end

theorem coordIdeal_eq_biSup_singleton {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (m : ℕ) (c : EtaleChart p U m)
    (S : Finset (Fin m)) :
    c.coordIdeal S = ⨆ j ∈ S, c.coordIdeal {j} := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_eq_biSup_singleton, comap_biSup_finset]
  exact iSup_congr fun j => iSup_congr fun _ => (c.coordIdeal_eq_comap_coordSubspaceIdeal {j}).symm

theorem orderAt_boundary_eq_one : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ D ∈ T.boundary, ∀ x : ↥T.scheme, x ∈ D.support → orderAt D x = 1 := by
  intro T hT D hD x hx
  have : Smooth T.structMap := hT.smooth
  obtain ⟨_, hpos⟩ := (inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hT.snc
  obtain ⟨U, hxU, m, c, a, _, hnone, hsome⟩ := (hpos x).exists_etaleChart
  obtain ⟨i, hi, hDi⟩ := List.mem_iff_getElem.1 hD
  cases hai : a i with
  | none =>
      refine absurd hx (notMem_support_of_mem_opens_of_restrictIdeal_eq_top D U ?_ x hxU)
      rw [← hDi]
      exact hnone i hi hai
  | some t =>
      obtain ⟨V, m', hxV, hVU', hV, -⟩ := exists_etaleChart_le T.structMap x U hxU
      have hDU : restrictIdeal D U = c.coordIdeal {t} := by
        rw [← hDi]
        exact hsome i hi t hai
      have hDV : restrictIdeal D V = (c.restrict hVU').coordIdeal {t} :=
        restrictIdeal_eq_restrict_coordIdeal_of_le hVU' c D {t} hDU
      exact orderAt_eq_one_of_restrictIdeal_eq_coordIdeal_singleton T.structMap hV
        (c.restrict hVU') t D hDV x hxV hx

theorem smooth_intersectionIdeal_subscheme : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ J : Finset (Fin T.boundary.length),
      Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap) := by
  classical
  intro T hT J
  refine smooth_subschemeι_comp_of_locally_eq_coordIdeal (p := T.structMap) (intersectionIdeal T.boundary J) ?_
  intro x hx
  obtain ⟨_, hpos⟩ := (inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hT.snc
  obtain ⟨U, hxU, m, c, a, _, hnone, hsome⟩ := (hpos x).exists_etaleChart
  have hle : ∀ j ∈ J, T.boundary.get j ≤ intersectionIdeal T.boundary J := by
    intro j hj
    rw [intersectionIdeal_eq_iSup]
    exact le_iSup₂ (f := fun j (_ : j ∈ J) => T.boundary.get j) j hj
  have hxj : ∀ j ∈ J, x ∈ (T.boundary.get j).support := by
    intro j hj
    rw [mem_support_iff_stalkIdeal_ne_top]
    intro hcon
    have h2 := stalkIdeal_mono (hle j hj) x
    rw [hcon] at h2
    exact (mem_support_iff_stalkIdeal_ne_top _ _).1 hx (top_le_iff.1 h2)
  have hsomej : ∀ j ∈ J, ∃ t : Fin m, a (j : ℕ) = some t := by
    intro j hj
    cases haj : a (j : ℕ) with
    | none =>
        refine absurd (hxj j hj)
          (notMem_support_of_mem_opens_of_restrictIdeal_eq_top _ U ?_ x hxU)
        rw [List.get_eq_getElem]
        exact hnone (j : ℕ) j.isLt haj
    | some t => exact ⟨t, rfl⟩
  refine ⟨U, hxU, m, c, J.biUnion (fun j => (a (j : ℕ)).toFinset), ?_⟩
  have h1 : restrictIdeal (intersectionIdeal T.boundary J) U
      = ⨆ j ∈ J, restrictIdeal (T.boundary.get j) U := by
    rw [intersectionIdeal_eq_iSup]
    exact restrictIdeal_biSup_finset U (fun j => T.boundary.get j) J
  have h2 : c.coordIdeal (J.biUnion (fun j => (a (j : ℕ)).toFinset))
      = ⨆ t ∈ J.biUnion (fun j => (a (j : ℕ)).toFinset), c.coordIdeal {t} :=
    coordIdeal_eq_biSup_singleton T.structMap U m c _
  rw [h1, h2]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun j => iSup_le fun hj => ?_
    obtain ⟨t, ht⟩ := hsomej j hj
    have hres : restrictIdeal (T.boundary.get j) U = c.coordIdeal {t} := by
      rw [List.get_eq_getElem]
      exact hsome (j : ℕ) j.isLt t ht
    have htS : t ∈ J.biUnion (fun j => (a (j : ℕ)).toFinset) :=
      Finset.mem_biUnion.2 ⟨j, hj, by simp [ht]⟩
    rw [hres]
    exact le_iSup₂
      (f := fun t (_ : t ∈ J.biUnion (fun j => (a (j : ℕ)).toFinset)) =>
        c.coordIdeal ({t} : Finset (Fin m))) t htS
  · refine iSup_le fun t => iSup_le fun htS => ?_
    obtain ⟨j, hj, htj⟩ := Finset.mem_biUnion.1 htS
    have ht : a (j : ℕ) = some t := Option.mem_def.1 (Option.mem_toFinset.1 htj)
    have hres : restrictIdeal (T.boundary.get j) U = c.coordIdeal {t} := by
      rw [List.get_eq_getElem]
      exact hsome (j : ℕ) j.isLt t ht
    rw [← hres]
    exact le_iSup₂ (f := fun j (_ : j ∈ J) => restrictIdeal (T.boundary.get j) U) j hj

end MonomialChart


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.ComponentsInSupport
section

open CategoryTheory AlgebraicGeometry

section

section
variable {X : Scheme.{u}}

private theorem mem_basicOpen_iff_notMem_asIdeal_primeIdealOf_consolidated279 {V : X.Opens} (hV : IsAffineOpen V)
    {x : ↥X} (hx : x ∈ V) (f : Γ(X, V)) :
    x ∈ X.basicOpen f ↔ f ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h1 : hV.fromSpec.base (hV.primeIdealOf ⟨x, hx⟩) = x := hV.fromSpec_primeIdealOf ⟨x, hx⟩
  have h2 : (hV.primeIdealOf ⟨x, hx⟩) ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen f ↔ x ∈ X.basicOpen f := by
    show hV.fromSpec.base (hV.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f ↔ _
    rw [h1]
  rw [← h2, hV.fromSpec_preimage_basicOpen]
  exact PrimeSpectrum.mem_basicOpen f _

private theorem mem_support_iff_ideal_le_asIdeal_primeIdealOf_consolidated279 (I : X.IdealSheafData) {V : X.Opens}
    (hV : IsAffineOpen V) {x : ↥X} (hx : x ∈ V) :
    x ∈ I.support ↔ I.ideal ⟨V, hV⟩ ≤ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hx, Scheme.mem_zeroLocus_iff]
  constructor
  · intro h f hf
    by_contra hfP
    exact h f hf ((mem_basicOpen_iff_notMem_asIdeal_primeIdealOf_consolidated279 hV hx f).mpr hfP)
  · intro h f hf hb
    exact (mem_basicOpen_iff_notMem_asIdeal_primeIdealOf_consolidated279 hV hx f).mp hb (h (SetLike.mem_coe.mp hf))


end

section
variable {R : Type u} [CommRing R] (I : Ideal R) (g : R) (hnzd : ∀ x : R, g * x ∈ I → x ∈ I)
include hnzd

private theorem mem_of_mul_pow_mem_consolidated279 :
    ∀ (n : ℕ) (u : R), u * g ^ n ∈ I → u ∈ I := by
  intro n
  induction n with
  | zero =>
      intro u h
      simpa using h
  | succ n ih =>
      intro u h
      refine ih u (hnzd _ ?_)
      have e : g * (u * g ^ n) = u * g ^ (n + 1) := by ring
      rw [e]
      exact h

private theorem exists_isPrime_between_notMem_of_mul_mem_consolidated279 (P : Ideal R) (hP : P.IsPrime) (hIP : I ≤ P) :
    ∃ Q : Ideal R, Q.IsPrime ∧ I ≤ Q ∧ Q ≤ P ∧ g ∉ Q := by
  classical
  have h1P : (1 : R) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  let M : Submonoid R :=
    { carrier := {x : R | ∃ (u : R) (n : ℕ), u ∉ P ∧ x = u * g ^ n}
      mul_mem' := by
        rintro x y ⟨u, n, hu, rfl⟩ ⟨v, l, hv, rfl⟩
        refine ⟨u * v, n + l, ?_, by ring⟩
        intro h
        rcases hP.mem_or_mem h with h' | h'
        · exact hu h'
        · exact hv h'
      one_mem' := ⟨1, 0, h1P, by ring⟩ }
  have hdisj : Disjoint (I : Set R) (M : Set R) := by
    rw [Set.disjoint_left]
    rintro x hxI ⟨u, n, hu, rfl⟩
    exact hu (hIP (mem_of_mul_pow_mem_consolidated279 I g hnzd n u hxI))
  obtain ⟨Q, hQ, hIQ, hQdisj⟩ := Ideal.exists_le_prime_disjoint I M hdisj
  refine ⟨Q, hQ, hIQ, ?_, ?_⟩
  · intro x hx
    by_contra hxP
    exact Set.disjoint_left.mp hQdisj hx ⟨x, 0, hxP, by ring⟩
  · intro hg
    exact Set.disjoint_left.mp hQdisj hg ⟨1, 1, h1P, by ring⟩


end

private theorem mem_map_of_mul_mem_of_etale_of_isSMulRegular_consolidated279 {P A : Type u} [CommRing P] [CommRing A]
    {f : P →+* A} (hf : f.Etale) (I : Ideal P) (w : P)
    (hw : ∀ a b : P ⧸ I,
      (Ideal.Quotient.mk I) w * a = (Ideal.Quotient.mk I) w * b → a = b)
    (x : A) (hx : f w * x ∈ Ideal.map f I) : x ∈ Ideal.map f I := by
  have hg : (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).Etale :=
    etale_quotientMap hf I
  let _ : Algebra (P ⧸ I) (A ⧸ Ideal.map f I) :=
    (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).toAlgebra
  have : Algebra.Etale (P ⧸ I) (A ⧸ Ideal.map f I) := hg
  have : Module.Flat (P ⧸ I) (A ⧸ Ideal.map f I) := inferInstance
  have hy : (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map)
        ((Ideal.Quotient.mk I) w) * (Ideal.Quotient.mk (Ideal.map f I)) x = 0 := by
    rw [Ideal.quotientMap_mk, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hsm : ((Ideal.Quotient.mk I) w) • ((Ideal.Quotient.mk (Ideal.map f I)) x)
      = (0 : A ⧸ Ideal.map f I) := by
    show (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map)
        ((Ideal.Quotient.mk I) w) * (Ideal.Quotient.mk (Ideal.map f I)) x = 0
    exact hy
  have hreg0 : IsSMulRegular (P ⧸ I) ((Ideal.Quotient.mk I) w) := fun a b h => hw a b h
  have hreg : IsSMulRegular (A ⧸ Ideal.map f I) ((Ideal.Quotient.mk I) w) := hreg0.of_flat
  have hzero : (Ideal.Quotient.mk (Ideal.map f I)) x = 0 := by
    refine hreg ?_
    show ((Ideal.Quotient.mk I) w) • ((Ideal.Quotient.mk (Ideal.map f I)) x)
      = ((Ideal.Quotient.mk I) w) • (0 : A ⧸ Ideal.map f I)
    rw [smul_zero]
    exact hsm
  exact Ideal.Quotient.eq_zero_iff_mem.mp hzero

private theorem mem_mvPolynomialCoordIdeal_of_X_mul_mem_consolidated279 (k : Type u) [Field k] (m : ℕ)
    (S : Finset (Fin m)) {s : Fin m} (hs : s ∉ S) (r : MvPolynomial (ULift.{u} (Fin m)) k)
    (h : MvPolynomial.X (ULift.up.{u} s) * r ∈ mvPolynomialCoordIdeal k m S) :
    r ∈ mvPolynomialCoordIdeal k m S := by
  classical
  obtain ⟨ψ, hψC, hψX⟩ :
      ∃ ψ : MvPolynomial (ULift.{u} (Fin m)) k →+* MvPolynomial (ULift.{u} (Fin m)) k,
        (∀ a : k, ψ (MvPolynomial.C a) = MvPolynomial.C a) ∧
        (∀ j : Fin m, ψ (MvPolynomial.X (ULift.up.{u} j))
          = if j ∈ S then 0 else MvPolynomial.X (ULift.up.{u} j)) := by
    refine ⟨MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i : ULift.{u} (Fin m) =>
        if i.down ∈ S then (0 : MvPolynomial (ULift.{u} (Fin m)) k)
        else MvPolynomial.X i), ?_, ?_⟩
    · intro a
      simp
    · intro j
      simp
  have hker : mvPolynomialCoordIdeal k m S ≤ RingHom.ker ψ := by
    rw [mvPolynomialCoordIdeal_eq_span, Ideal.span_le]
    rintro _ ⟨j, hj, rfl⟩
    have hz : ψ (MvPolynomial.X (ULift.up.{u} j)) = 0 := by
      rw [hψX j]
      exact if_pos (Finset.mem_coe.mp hj)
    exact SetLike.mem_coe.mpr (RingHom.mem_ker.mpr hz)
  have key : (Ideal.Quotient.mk (mvPolynomialCoordIdeal k m S)).comp ψ
      = Ideal.Quotient.mk (mvPolynomialCoordIdeal k m S) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, hψC]
    · intro i
      obtain ⟨j⟩ := i
      rw [RingHom.comp_apply, hψX j]
      by_cases hi : j ∈ S
      · rw [if_pos hi, map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr (X_mem_mvPolynomialCoordIdeal k m S hi)).symm
      · rw [if_neg hi]
  have h0 : ψ (MvPolynomial.X (ULift.up.{u} s) * r) = 0 :=
    RingHom.mem_ker.mp (hker h)
  rw [map_mul, hψX s, if_neg hs] at h0
  have hXne : (MvPolynomial.X (ULift.up.{u} s) : MvPolynomial (ULift.{u} (Fin m)) k) ≠ 0 :=
    MvPolynomial.X_ne_zero _
  have hψr : ψ r = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hXne
    · exact h1
  have hfin := DFunLike.congr_fun key r
  rw [RingHom.comp_apply, hψr, map_zero] at hfin
  exact Ideal.Quotient.eq_zero_iff_mem.mp hfin.symm

private theorem false_of_restrictIdeal_eq_coordIdeal_consolidated279 {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {V : X.Opens} (hV : IsAffineOpen V) {m : ℕ}
    (c : EtaleChart p V m) (Z D : X.IdealSheafData) (S : Finset (Fin m)) (s : Fin m)
    (hs : s ∉ S) (hZ : restrictIdeal Z V = c.coordIdeal S)
    (hD : restrictIdeal D V = c.coordIdeal {s})
    (ξ : ↥X) (hξV : ξ ∈ V) (hξZ : ξ ∈ Z.support) (_hξD : ξ ∈ D.support)
    (hmin : ∀ η : ↥X, η ∈ Z.support → ξ ∈ closure ({η} : Set ↥X) → η ∈ D.support) : False := by
  classical
  have hIZ : Ideal.map c.coordRingHom (mvPolynomialCoordIdeal k m S) = Z.ideal ⟨V, hV⟩ :=
    c.map_mvPolynomialCoordIdeal_eq_ideal hV Z S hZ
  have hID : Ideal.map c.coordRingHom (mvPolynomialCoordIdeal k m {s}) = D.ideal ⟨V, hV⟩ :=
    c.map_mvPolynomialCoordIdeal_eq_ideal hV D {s} hD
  have hDspan : D.ideal ⟨V, hV⟩ = Ideal.span {c.coord s} := by
    rw [← hID, mvPolynomialCoordIdeal_eq_span, Finset.coe_singleton, Set.image_singleton, Ideal.map_span,
      Set.image_singleton, c.coordRingHom_X]
  have hnzd : ∀ x : Γ(X, V), c.coord s * x ∈ Z.ideal ⟨V, hV⟩ → x ∈ Z.ideal ⟨V, hV⟩ := by
    intro x hx
    rw [← hIZ] at hx ⊢
    refine mem_map_of_mul_mem_of_etale_of_isSMulRegular_consolidated279 (c.coordRingHom_etale hV) (mvPolynomialCoordIdeal k m S)
      (MvPolynomial.X (ULift.up.{u} s)) ?_ x ?_
    · intro A B hAB
      obtain ⟨A', rfl⟩ := Ideal.Quotient.mk_surjective A
      obtain ⟨B', rfl⟩ := Ideal.Quotient.mk_surjective B
      rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub] at hAB
      exact Ideal.Quotient.eq.mpr (mem_mvPolynomialCoordIdeal_of_X_mul_mem_consolidated279 k m S hs (A' - B') hAB)
    · rw [c.coordRingHom_X]
      exact hx
  have hIP : Z.ideal ⟨V, hV⟩ ≤ (hV.primeIdealOf ⟨ξ, hξV⟩).asIdeal :=
    (mem_support_iff_ideal_le_asIdeal_primeIdealOf_consolidated279 Z hV hξV).mp hξZ
  obtain ⟨Q, hQp, hIQ, hQP, hgQ⟩ :=
    exists_isPrime_between_notMem_of_mul_mem_consolidated279 (Z.ideal ⟨V, hV⟩) (c.coord s) hnzd
      (hV.primeIdealOf ⟨ξ, hξV⟩).asIdeal (hV.primeIdealOf ⟨ξ, hξV⟩).isPrime hIP
  obtain ⟨q, hqQ⟩ : ∃ q : PrimeSpectrum Γ(X, V), q.asIdeal = Q := ⟨⟨Q, hQp⟩, rfl⟩
  have hrange : hV.fromSpec.base q ∈ V := by
    have h0 : hV.fromSpec.base q ∈ Set.range ⇑hV.fromSpec.base := ⟨q, rfl⟩
    rw [hV.range_fromSpec] at h0
    exact h0
  have hQeq : hV.primeIdealOf ⟨hV.fromSpec.base q, hrange⟩ = q := by
    apply hV.fromSpec.isOpenEmbedding.injective
    rw [hV.fromSpec_primeIdealOf]
  have hηZ : hV.fromSpec.base q ∈ Z.support := by
    rw [mem_support_iff_ideal_le_asIdeal_primeIdealOf_consolidated279 Z hV hrange, hQeq, hqQ]
    exact hIQ
  have hspec : ξ ∈ closure ({hV.fromSpec.base q} : Set ↥X) := by
    have hle : q.asIdeal ≤ (hV.primeIdealOf ⟨ξ, hξV⟩).asIdeal := by
      rw [hqQ]
      exact hQP
    have h1 : q ⤳ hV.primeIdealOf ⟨ξ, hξV⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp hle
    have h2 := h1.map hV.fromSpec.base.hom.continuous
    rw [hV.fromSpec_primeIdealOf] at h2
    exact specializes_iff_mem_closure.mp h2
  have hηD := hmin _ hηZ hspec
  rw [mem_support_iff_ideal_le_asIdeal_primeIdealOf_consolidated279 D hV hrange, hQeq, hDspan, hqQ] at hηD
  exact hgQ (hηD (Ideal.mem_span_singleton_self _))

private theorem not_subset_boundary_support_of_notMem_consolidated279 (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme)
    (hC : C ∈ intersectionComponents T.boundary J) (i : Fin T.boundary.length) (hi : i ∉ J)
    (hsub : C ⊆ ((T.boundary.get i).support : Set ↥T.scheme)) : False := by
  classical
  obtain ⟨hirr, hCsub, hmax⟩ := hC
  have hirr' : IsIrreducible C := hirr
  have hclosed : IsClosed C :=
    isClosed_of_maximal_irreducible_subset_support (intersectionIdeal T.boundary J) hirr' hCsub hmax
  have hgen : closure ({hirr'.genericPoint} : Set ↥T.scheme) = C := by
    have h : closure ({hirr'.genericPoint} : Set ↥T.scheme) = closure C :=
      hirr'.genericPoint_closure_eq
    rw [h, hclosed.closure_eq]
  have hxiC : hirr'.genericPoint ∈ C := IsGenericPoint.mem hgen
  have hxiZ : hirr'.genericPoint ∈ (intersectionIdeal T.boundary J).support := hCsub hxiC
  have hxiD : hirr'.genericPoint ∈ (T.boundary.get i).support := hsub hxiC
  obtain ⟨U, hxiU, m, c, a, hinj, hnone, hsome⟩ := hT.snc.2 hirr'.genericPoint
  obtain ⟨V, hVaff, hxiV, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.scheme.isBasis_affineOpens hxiU
  have hV : IsAffineOpen V := hVaff
  have key : ∀ j : Fin T.boundary.length, hirr'.genericPoint ∈ (T.boundary.get j).support →
      ∃ t : Fin m, a (j : ℕ) = some t ∧
        restrictIdeal (T.boundary.get j) V = (c.restrict hVU).coordIdeal {t} := by
    intro j hj
    cases hA : a (j : ℕ) with
    | none =>
        exfalso
        have h1 : restrictIdeal (T.boundary[(j : ℕ)]'j.isLt) U = ⊤ := hnone (j : ℕ) j.isLt hA
        have h2 : restrictIdeal (T.boundary.get j) U = ⊤ := by
          rw [List.get_eq_getElem]
          exact h1
        exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top (T.boundary.get j) U h2
          hirr'.genericPoint hxiU hj
    | some t =>
        refine ⟨t, rfl, ?_⟩
        have h1 : restrictIdeal (T.boundary[(j : ℕ)]'j.isLt) U = c.coordIdeal {t} :=
          hsome (j : ℕ) j.isLt t hA
        have h2 : restrictIdeal (T.boundary.get j) U = c.coordIdeal {t} := by
          rw [List.get_eq_getElem]
          exact h1
        exact restrictIdeal_eq_restrict_coordIdeal_of_le hVU c (T.boundary.get j) {t} h2
  have hmemJ : ∀ j ∈ J, hirr'.genericPoint ∈ (T.boundary.get j).support := by
    intro j hj
    refine Scheme.IdealSheafData.support_antitone ?_ hxiZ
    rw [intersectionIdeal_eq_iSup]
    exact le_biSup T.boundary.get hj
  obtain ⟨si, hsi, hDi⟩ := key i hxiD
  obtain ⟨S, hmemS⟩ :
      ∃ S : Finset (Fin m), ∀ t : Fin m, t ∈ S ↔ ∃ j ∈ J, a (j : ℕ) = some t :=
    ⟨Finset.univ.filter (fun t : Fin m => ∃ j ∈ J, a (j : ℕ) = some t), by
      intro t
      simp⟩
  have hsiS : si ∉ S := by
    intro hmem
    obtain ⟨j, hj, haj⟩ := (hmemS si).mp hmem
    have hval : (i : ℕ) = (j : ℕ) := hinj (i : ℕ) i.isLt (j : ℕ) j.isLt si hsi haj
    have hij : i = j := Fin.eq_of_val_eq hval
    exact hi (by rw [hij]; exact hj)
  have hZV : restrictIdeal (intersectionIdeal T.boundary J) V = (c.restrict hVU).coordIdeal S := by
    have hbi : restrictIdeal (intersectionIdeal T.boundary J) V
        = ⨆ j ∈ J, restrictIdeal (T.boundary.get j) V := by
      rw [intersectionIdeal_eq_iSup]
      exact MonomialChart.restrictIdeal_biSup_finset V T.boundary.get J
    have hcb : (c.restrict hVU).coordIdeal S = ⨆ t ∈ S, (c.restrict hVU).coordIdeal {t} :=
      MonomialChart.coordIdeal_eq_biSup_singleton T.structMap V m (c.restrict hVU) S
    rw [hbi, hcb]
    refine le_antisymm (iSup₂_le fun j hj => ?_) (iSup₂_le fun t ht => ?_)
    · obtain ⟨t, hat, hres⟩ := key j (hmemJ j hj)
      rw [hres]
      exact le_biSup (fun t : Fin m => (c.restrict hVU).coordIdeal {t})
        ((hmemS t).mpr ⟨j, hj, hat⟩)
    · obtain ⟨j, hj, hat⟩ := (hmemS t).mp ht
      obtain ⟨t', hat', hres⟩ := key j (hmemJ j hj)
      have htt : t = t' := Option.some.inj (hat.symm.trans hat')
      rw [htt, ← hres]
      exact le_biSup (fun j : Fin T.boundary.length => restrictIdeal (T.boundary.get j) V) hj
  refine false_of_restrictIdeal_eq_coordIdeal_consolidated279 hV (c.restrict hVU) (intersectionIdeal T.boundary J) (T.boundary.get i)
    S si hsiS hZV hDi hirr'.genericPoint hxiV hxiZ hxiD ?_
  intro η hηZ hηxi
  have hirr2 : IsIrreducible (closure ({η} : Set ↥T.scheme)) := isIrreducible_singleton.closure
  have hs1 : C ⊆ closure ({η} : Set ↥T.scheme) := by
    rw [← hgen]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηxi) isClosed_closure
  have hs2 : closure ({η} : Set ↥T.scheme)
      ⊆ ((intersectionIdeal T.boundary J).support : Set ↥T.scheme) :=
    closure_minimal (Set.singleton_subset_iff.mpr hηZ)
      (intersectionIdeal T.boundary J).support.2
  have heq : closure ({η} : Set ↥T.scheme) = C := hmax _ hirr2 hs1 hs2
  have hηC : η ∈ C := by
    rw [← heq]
    exact subset_closure (Set.mem_singleton η)
  exact hsub hηC

theorem intersectionComponents_subset_support_iff : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)),
      ∀ C ∈ intersectionComponents T.boundary J,
        ∀ (i : Fin T.boundary.length),
          C ⊆ ((T.boundary.get i).support : Set ↥T.scheme) ↔ i ∈ J := by
  intro T hT J C hC i
  constructor
  · intro hsub
    by_contra hi
    exact not_subset_boundary_support_of_notMem_consolidated279 T hT J C hC i hi hsub
  · intro hi x hx
    have hle : T.boundary.get i ≤ intersectionIdeal T.boundary J := by
      rw [intersectionIdeal_eq_iSup]
      exact le_biSup T.boundary.get hi
    exact Scheme.IdealSheafData.support_antitone hle (hC.2.1 hx)


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LexOrderEncoding
section

namespace MonomialCenter

private theorem sort_image_of_strictMono_consolidated281 {α β : Type*} [LinearOrder α] [LinearOrder β]
    [DecidableEq β] (f : α → β) (hf : StrictMono f) (s : Finset α) :
    (s.image f).sort (· ≤ ·) = (s.sort (· ≤ ·)).map f := by
  have hlt' : List.Pairwise (· < ·) ((s.image f).sort (· ≤ ·)) :=
    (Finset.sortedLT_sort (s.image f)).pairwise
  have hmap : List.Pairwise (· < ·) ((s.sort (· ≤ ·)).map f) :=
    (Finset.sortedLT_sort s).pairwise.map f (fun _ _ hab => hf hab)
  refine List.Pairwise.eq_of_mem_iff hlt' hmap ?_
  intro b
  simp [Finset.mem_sort]

theorem sortedIndices_image_of_strictMono {n n' : ℕ} [DecidableEq (Fin n')]
    (φ : Fin n → Fin n') (hφ : StrictMono φ) (J : Finset (Fin n)) :
    sortedIndices (J.image φ) = (J.sort (· ≤ ·)).map (fun j => ((φ j : Fin n') : ℕ)) := by
  rw [sortedIndices_eq_map_sort, sort_image_of_strictMono_consolidated281 φ hφ J, List.map_map]
  rfl

theorem lex_map_iff_of_strictMono {α β : Type*} [LinearOrder α] [LinearOrder β]
    (f : α → β) (hf : StrictMono f) (l l' : List α) :
    List.Lex (· < ·) (l.map f) (l'.map f) ↔ List.Lex (· < ·) l l' := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil =>
      simp only [List.map_nil]
      exact iff_of_false (by rintro ⟨⟩) (by rintro ⟨⟩)
    | cons b t =>
      simp only [List.map_nil, List.map_cons]
      exact iff_of_true List.Lex.nil List.Lex.nil
  | cons a s ih =>
    cases l' with
    | nil =>
      simp only [List.map_nil, List.map_cons]
      exact iff_of_false (by rintro ⟨⟩) (by rintro ⟨⟩)
    | cons b t =>
      simp only [List.map_cons, List.cons_lex_cons_iff]
      constructor
      · rintro (h | ⟨h, h2⟩)
        · exact Or.inl (hf.lt_iff_lt.mp h)
        · exact Or.inr ⟨hf.injective h, (ih t).mp h2⟩
      · rintro (h | ⟨rfl, h2⟩)
        · exact Or.inl (hf h)
        · exact Or.inr ⟨rfl, (ih t).mpr h2⟩

theorem lex_sortedIndices_image_iff {n n' : ℕ} [DecidableEq (Fin n')]
    (φ : Fin n → Fin n') (hφ : StrictMono φ) (J J' : Finset (Fin n)) :
    List.Lex (· < ·) (sortedIndices (J.image φ)) (sortedIndices (J'.image φ)) ↔
      List.Lex (· < ·) (sortedIndices J) (sortedIndices J') := by
  have hg : StrictMono (fun j : Fin n => ((φ j : Fin n') : ℕ)) :=
    fun a b h => Fin.val_strictMono (hφ h)
  have h1 := lex_map_iff_of_strictMono _ hg (J.sort (· ≤ ·)) (J'.sort (· ≤ ·))
  have h2 := lex_map_iff_of_strictMono (Fin.val : Fin n → ℕ) Fin.val_strictMono
    (J.sort (· ≤ ·)) (J'.sort (· ≤ ·))
  rw [sortedIndices_image_of_strictMono φ hφ J, sortedIndices_image_of_strictMono φ hφ J',
    sortedIndices_eq_map_sort, sortedIndices_eq_map_sort]
  exact h1.trans h2.symm

def reversedIndex (n : ℕ) (j : Fin n) : ℕ := n - 1 - (j : ℕ)

section
variable {n : ℕ}

theorem reversedIndex_lt_reversedIndex_iff (j j' : Fin n) :
    reversedIndex n j < reversedIndex n j' ↔ j' < j := by
  have hj := j.isLt
  have hj' := j'.isLt
  simp only [reversedIndex, Fin.lt_def]
  omega

theorem reversedIndex_injective : Function.Injective (reversedIndex n) := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  have h' : n - 1 - (a : ℕ) = n - 1 - (b : ℕ) := h
  exact Fin.val_injective (by omega)

theorem binaryEncode_eq_sum_image (J : Finset (Fin n)) :
    _root_.FunctorialResolution.EmbeddedResolution.binaryEncode J = ∑ e ∈ J.image (reversedIndex n), 2 ^ e := by
  have hinj : ∀ a ∈ J, ∀ b ∈ J, reversedIndex n a = reversedIndex n b → a = b :=
    fun a _ b _ h => reversedIndex_injective h
  rw [Finset.sum_image hinj]
  rfl

theorem binaryEncode_lt_iff (J J' : Finset (Fin n)) :
    _root_.FunctorialResolution.EmbeddedResolution.binaryEncode J' < _root_.FunctorialResolution.EmbeddedResolution.binaryEncode J ↔
      (∃ a ∈ J, a ∉ J' ∧ ∀ b ∈ J', b ∉ J → a < b) := by
  simp only [binaryEncode_eq_sum_image]
  rw [(Finset.geomSum_lt_geomSum_iff_toColex_lt_toColex (le_refl 2)).trans
    Finset.Colex.toColex_lt_toColex_iff_exists_forall_lt]
  constructor
  · rintro ⟨e, he, he', hmax⟩
    obtain ⟨a, haJ, rfl⟩ := Finset.mem_image.mp he
    refine ⟨a, haJ, ?_, ?_⟩
    · intro haJ'
      exact he' (Finset.mem_image_of_mem _ haJ')
    · intro b hb hbJ
      have hb1 : reversedIndex n b ∈ J'.image (reversedIndex n) := Finset.mem_image_of_mem _ hb
      have hb2 : reversedIndex n b ∉ J.image (reversedIndex n) := by
        intro hmem
        obtain ⟨c, hc, hceq⟩ := Finset.mem_image.mp hmem
        have hcb : c = b := reversedIndex_injective hceq
        rw [hcb] at hc
        exact hbJ hc
      exact (reversedIndex_lt_reversedIndex_iff b a).mp (hmax _ hb1 hb2)
  · rintro ⟨a, haJ, haJ', hmin⟩
    refine ⟨reversedIndex n a, Finset.mem_image_of_mem _ haJ, ?_, ?_⟩
    · intro hmem
      obtain ⟨c, hc, hceq⟩ := Finset.mem_image.mp hmem
      have hca : c = a := reversedIndex_injective hceq
      rw [hca] at hc
      exact haJ' hc
    · rintro f hf hfnot
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
      have hbJ : b ∉ J := by
        intro hbJ
        exact hfnot (Finset.mem_image_of_mem _ hbJ)
      exact (reversedIndex_lt_reversedIndex_iff b a).mpr (hmin b hb hbJ)


end

private theorem lex_iff_exists_min_mem_consolidated281 {α : Type*} [LinearOrder α] :
    ∀ (L L' : List α), L.length = L'.length → List.Pairwise (· < ·) L →
      List.Pairwise (· < ·) L' →
      (List.Lex (· < ·) L L' ↔ ∃ a ∈ L, a ∉ L' ∧ ∀ b ∈ L', b ∉ L → a < b) := by
  intro L
  induction L with
  | nil =>
    intro L' hlen _ _
    cases L' with
    | nil =>
      constructor
      · intro h
        cases h
      · rintro ⟨a, ha, -⟩
        simp at ha
    | cons b t => simp at hlen
  | cons a s ih =>
    intro L' hlen hs hL'
    cases L' with
    | nil => simp at hlen
    | cons b t =>
      rw [List.pairwise_cons] at hs hL'
      have hlen' : s.length = t.length := by simpa using hlen
      rw [List.cons_lex_cons_iff]
      rcases lt_trichotomy a b with hab | hab | hab
      · constructor
        · intro _
          refine ⟨a, by simp, ?_, ?_⟩
          · intro hmem
            rcases List.mem_cons.mp hmem with h | h
            · rw [h] at hab
              exact absurd hab (lt_irrefl b)
            · exact absurd (hL'.1 a h) (not_lt.mpr hab.le)
          · intro y hy _
            rcases List.mem_cons.mp hy with h | h
            · rw [h]
              exact hab
            · exact lt_trans hab (hL'.1 y h)
        · intro _
          exact Or.inl hab
      · subst hab
        have ihst := ih t hlen' hs.2 hL'.2
        constructor
        · rintro (h | ⟨-, h⟩)
          · exact absurd h (lt_irrefl _)
          · obtain ⟨x, hxs, hxt, hmin⟩ := ihst.mp h
            refine ⟨x, List.mem_cons.mpr (Or.inr hxs), ?_, ?_⟩
            · intro hx
              rcases List.mem_cons.mp hx with heq | hx
              · rw [heq] at hxs
                exact absurd (hs.1 _ hxs) (lt_irrefl _)
              · exact hxt hx
            · intro y hy hyn
              rcases List.mem_cons.mp hy with heq | hy
              · refine absurd ?_ hyn
                rw [heq]
                simp
              · exact hmin y hy (fun hys => hyn (List.mem_cons.mpr (Or.inr hys)))
        · rintro ⟨x, hx, hxn, hmin⟩
          refine Or.inr ⟨rfl, ihst.mpr ?_⟩
          have hxs : x ∈ s := by
            rcases List.mem_cons.mp hx with h | h
            · refine absurd ?_ hxn
              rw [h]
              simp
            · exact h
          refine ⟨x, hxs, ?_, ?_⟩
          · intro hxt
            exact hxn (List.mem_cons.mpr (Or.inr hxt))
          · intro y hy hys
            refine hmin y (List.mem_cons.mpr (Or.inr hy)) ?_
            intro hy'
            rcases List.mem_cons.mp hy' with h | h
            · rw [h] at hy
              exact absurd (hL'.1 _ hy) (lt_irrefl _)
            · exact hys h
      · constructor
        · rintro (h | ⟨h, -⟩)
          · exact absurd h (not_lt.mpr hab.le)
          · rw [h] at hab
            exact absurd hab (lt_irrefl b)
        · rintro ⟨x, hx, hxn, hmin⟩
          have hbs : b ∉ a :: s := by
            intro hb
            rcases List.mem_cons.mp hb with h | h
            · rw [h] at hab
              exact absurd hab (lt_irrefl a)
            · exact absurd (hs.1 b h) (not_lt.mpr hab.le)
          have hxb : x < b := hmin b (by simp) hbs
          have hax : a ≤ x := by
            rcases List.mem_cons.mp hx with h | h
            · exact le_of_eq h.symm
            · exact le_of_lt (hs.1 x h)
          exact absurd hxb (not_lt.mpr (le_trans hab.le hax))

section
variable {n : ℕ}

theorem binaryEncode_lt_iff_lex_of_card_eq (J J' : Finset (Fin n)) (hcard : J.card = J'.card) :
    _root_.FunctorialResolution.EmbeddedResolution.binaryEncode J' < _root_.FunctorialResolution.EmbeddedResolution.binaryEncode J ↔
      List.Lex (· < ·) (sortedIndices J) (sortedIndices J') := by
  have hlen : (J.sort (· ≤ ·)).length = (J'.sort (· ≤ ·)).length := by
    rw [Finset.length_sort, Finset.length_sort, hcard]
  have hsJ : List.Pairwise (· < ·) (J.sort (· ≤ ·)) := (Finset.sortedLT_sort J).pairwise
  have hsJ' : List.Pairwise (· < ·) (J'.sort (· ≤ ·)) := (Finset.sortedLT_sort J').pairwise
  have hmap := lex_map_iff_of_strictMono (Fin.val : Fin n → ℕ) Fin.val_strictMono
    (J.sort (· ≤ ·)) (J'.sort (· ≤ ·))
  have hA := lex_iff_exists_min_mem_consolidated281 (J.sort (· ≤ ·)) (J'.sort (· ≤ ·)) hlen hsJ hsJ'
  have hfin : (∃ a ∈ J.sort (· ≤ ·), a ∉ J'.sort (· ≤ ·) ∧
      ∀ b ∈ J'.sort (· ≤ ·), b ∉ J.sort (· ≤ ·) → a < b) ↔
      (∃ a ∈ J, a ∉ J' ∧ ∀ b ∈ J', b ∉ J → a < b) := by
    simp only [Finset.mem_sort]
  rw [sortedIndices_eq_map_sort, sortedIndices_eq_map_sort]
  exact (binaryEncode_lt_iff J J').trans (hfin.symm.trans (hA.symm.trans hmap.symm))

theorem binaryEncode_injective :
    Function.Injective (fun J : Finset (Fin n) => _root_.FunctorialResolution.EmbeddedResolution.binaryEncode J) := by
  intro J J' h
  have hJ := binaryEncode_eq_sum_image J
  have hJ' := binaryEncode_eq_sum_image J'
  have h1 : (∑ e ∈ J.image (reversedIndex n), 2 ^ e) = (∑ e ∈ J'.image (reversedIndex n), 2 ^ e) := by
    rw [← hJ, ← hJ']
    exact h
  exact Finset.image_injective reversedIndex_injective (Finset.geomSum_injective (le_refl 2) h1)


end

end MonomialCenter

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
section

open CategoryTheory AlgebraicGeometry

section

namespace MonomialCenter

def IsMonomialNear {X : Scheme.{u}} (E : List X.IdealSheafData) (M : X.IdealSheafData)
    (x : ↥X) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧ ∃ a : Fin E.length → ℕ,
    M.comap U.ι =
      (List.ofFn (fun i : Fin E.length => (E.get i).comap U.ι ^ a i)).foldr (· * ·) ⊤

structure IsLocallyMonomialTriple (T : MarkedIdealWithBoundary.{u}) : Prop where
  valid : T.IsAdmissible
  monomialNear : ∀ x ∈ orderAtLeastLocus T.ideal T.mult, IsMonomialNear T.boundary T.ideal x

structure IsLocallyMonomialPrincipalization (P : ℕ → Prop) (F : PrincipalizationAssignment.{u}) : Prop where
  center_subset_boundaryLocus :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ i < (F T).length,
        (↑((F T).center i).support : Set ↥((F T).schemeAt i)) ⊆
          MarkedSequenceOfBlowups.boundaryLocus (F T) i
  cert :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ i < (F T).length,
        PrincipalizationCertificate ((F T).schemeAt i) (MarkedSequenceOfBlowups.projectionToSpec (F T) i) ((F T).ideal i) T.mult
          (MarkedSequenceOfBlowups.boundaryLocus (F T) i) ((F T).center i)
  base_change :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
        (E' : List (T.baseChange L f).scheme.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
          IsLocallyMonomialTriple ((T.baseChange L f).withBoundary E') →
            P ((T.baseChange L f).withBoundary E').krullDimSucc →
              IsPullbackBlowupSequence
                (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f))
                (F ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups (F T).toSequenceOfBlowups
  base_change_strict :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
        (E' : List (T.baseChange L f).scheme.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
          IsLocallyMonomialTriple ((T.baseChange L f).withBoundary E') →
            P ((T.baseChange L f).withBoundary E').krullDimSucc →
              IsStrictPullbackBlowupSeq
                (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f))
                (F ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups (F T).toSequenceOfBlowups
  center_eq :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ i < (F T).length,
        (F T).center i = monomialCenter ((F T).ideal i) T.mult ((F T).boundary i)
  minLevel_ne_zero :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ i < (F T).length, minIndexCard ((F T).ideal i) T.mult ((F T).boundary i) ≠ 0
  key_le :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ t, t + 1 < (F T).length →
        (centerInvariant ((F T).ideal t) T.mult ((F T).boundary t)).Le
          (centerInvariant ((F T).ideal (t + 1)) T.mult ((F T).boundary (t + 1)))
  monomial_near :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ i ≤ (F T).length, ∀ x ∈ orderAtLeastLocus ((F T).ideal i) T.mult,
        IsMonomialNear ((F T).boundary i) ((F T).ideal i) x
  center_nonempty :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ i < (F T).length, (↑((F T).center i).support : Set ↥((F T).schemeAt i)).Nonempty
  resolves :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      MarkedSequenceOfBlowups.IsResolution (F T)
  smooth_pullback :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [Smooth h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
            IsLocallyMonomialTriple ((T.pullbackAlong Y q h).withBoundary E') →
              P ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc →
                IsPullbackBlowupSequence h
                  (F ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups (F T).toSequenceOfBlowups
  smooth_pullback_strict :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [Smooth h] [AlgebraicGeometry.Surjective h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
            IsLocallyMonomialTriple ((T.pullbackAlong Y q h).withBoundary E') →
              P ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc →
                IsStrictPullbackBlowupSeq h
                  (F ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups (F T).toSequenceOfBlowups
  trivial_of_coSupport_empty :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      orderAtLeastLocus T.ideal T.mult = ∅ → (F T).length = 0

end MonomialCenter


end
end
end FunctorialResolution.EmbeddedResolution
end
