import Mathlib
import Core5.M12AdmissibleCenters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicGeometry
universe u
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.AmbientBlowupFlatBaseChange
section

open CategoryTheory.Limits

section

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) {X Y S S' : Scheme.{u}} (ι : S ⟶ X) (ι' : S' ⟶ Y) (h : Y ⟶ X) (h' : S' ⟶ S) [IsClosedImmersion ι] [IsClosedImmersion ι'] [Flat h] [IsNoetherian X] [IsNoetherian Y] (hsq : IsPullback ι' h' h ι) (s : BlowupSequenceData S) (s' : BlowupSequenceData S') (hs : s.CentersContainNoComponent) (hs' : s'.CentersContainNoComponent)
include hsq

theorem isStrictPullbackBlowupSeq_ambientBlowupSequence_of_flat
    (hpb : IsStrictPullbackBlowupSeq h' s'.toSequenceOfBlowups s.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq h (ambientBlowupSequence ι' s' hres hno hs').toSequenceOfBlowups
      (ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups := by
  have hstrict : IsStrictPullbackBlowupSeq h
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)
      ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) :=
    isStrictPullbackSequenceOfBlowups_baseChange ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) h
  have hN : ∀ i : ℕ, i ≤ ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).length →
      IsLocallyNoetherian (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).schemeAt i) := by
    intro i hi
    have : IsNoetherian (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).schemeAt i) :=
      isNoetherian_ambientBlowupSequence_schemeAt ι s hres hno hs i hi
    infer_instance
  have hN' : ∀ i : ℕ, i ≤ (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).length →
      IsLocallyNoetherian
        ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).schemeAt i) := by
    intro i hi
    have : IsNoetherian
        ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).schemeAt i) :=
      isNoetherian_schemeAt
        (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) i hi
    infer_instance
  have hpushTb : IsPushforwardBlowupSeq ι' s'.toSequenceOfBlowups
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) :=
    IsPushforwardBlowupSeq.of_flat_isPullback ι ι' h h' hsq s.toSequenceOfBlowups
      ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) s'.toSequenceOfBlowups
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) hN hN'
      (isPushforwardBlowupSeq_ambientBlowupSequence ι s hres hno hs) hpb hstrict
  have hequiv : ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)).Isomorphic
      ((ambientBlowupSequence ι' s' hres hno hs').toSequenceOfBlowups) :=
    IsPushforwardBlowupSeq.isomorphic ι' hpushTb
      (isPushforwardBlowupSeq_ambientBlowupSequence ι' s' hres hno hs')
  exact IsStrictPullbackBlowupSeq.of_isomorphic_pullback hstrict hequiv

theorem isPullbackBlowupSequence_ambientBlowupSequence_of_flat
    (hpb : IsPullbackBlowupSequence h' s'.toSequenceOfBlowups s.toSequenceOfBlowups) :
    IsPullbackBlowupSequence h (ambientBlowupSequence ι' s' hres hno hs').toSequenceOfBlowups
      (ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups := by
  have : Flat h' := by
    rw [← hsq.isoPullback_hom_snd]
    infer_instance
  have hUstrict : IsStrictPullbackBlowupSeq h' (s.toSequenceOfBlowups.baseChange h') s.toSequenceOfBlowups :=
    isStrictPullbackSequenceOfBlowups_baseChange s.toSequenceOfBlowups h'
  have hstrict : IsStrictPullbackBlowupSeq h
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)
      ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) :=
    isStrictPullbackSequenceOfBlowups_baseChange ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) h
  have hN : ∀ i : ℕ, i ≤ ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).length →
      IsLocallyNoetherian (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).schemeAt i) := by
    intro i hi
    have : IsNoetherian (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).schemeAt i) :=
      isNoetherian_ambientBlowupSequence_schemeAt ι s hres hno hs i hi
    infer_instance
  have hN' : ∀ i : ℕ, i ≤ (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).length →
      IsLocallyNoetherian
        ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).schemeAt i) := by
    intro i hi
    have : IsNoetherian
        ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).schemeAt i) :=
      isNoetherian_schemeAt
        (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) i hi
    infer_instance
  have hpushTb : IsPushforwardBlowupSeq ι' (s.toSequenceOfBlowups.baseChange h')
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) :=
    IsPushforwardBlowupSeq.of_flat_isPullback ι ι' h h' hsq s.toSequenceOfBlowups
      ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) (s.toSequenceOfBlowups.baseChange h')
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) hN hN'
      (isPushforwardBlowupSeq_ambientBlowupSequence ι s hres hno hs) hUstrict hstrict
  have hpushPrune : IsPushforwardBlowupSeq ι' (s.toSequenceOfBlowups.baseChange h').withoutIsoBlowups
      ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)).withoutIsoBlowups :=
    isPushforwardSequenceOfBlowups_withoutIsoBlowups ι' (s.toSequenceOfBlowups.baseChange h')
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) hN' hpushTb
  have heq : ((s.toSequenceOfBlowups.baseChange h').withoutIsoBlowups).Isomorphic s'.toSequenceOfBlowups :=
    IsPullbackBlowupSequence.isomorphic hUstrict.isPullbackSequenceOfBlowups_withoutIsoBlowups hpb
  have hpush' : IsPushforwardBlowupSeq ι' s'.toSequenceOfBlowups
      ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)).withoutIsoBlowups :=
    IsPushforwardBlowupSeq.of_isomorphic_source ι' heq hpushPrune
  have hequivT : (((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)).withoutIsoBlowups).Isomorphic
      ((ambientBlowupSequence ι' s' hres hno hs').toSequenceOfBlowups) :=
    IsPushforwardBlowupSeq.isomorphic ι' hpush'
      (isPushforwardBlowupSeq_ambientBlowupSequence ι' s' hres hno hs')
  exact IsPullbackBlowupSequence.of_isomorphic hstrict.isPullbackSequenceOfBlowups_withoutIsoBlowups hequivT


end

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
section


section

namespace MarkedIdealWithBoundary

def pullbackOverField (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (h : Y ⟶ T.scheme) : MarkedIdealWithBoundary.{u} where
  base := k'
  instField := inferInstance
  scheme := Y
  structMap := q
  ideal := T.ideal.comap h
  mult := T.mult
  boundary := T.boundary.map fun D => D.comap h

section
variable (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})

theorem pullbackOverField_eq_pullbackAlong (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) :
    T.pullbackOverField Y T.base q h = T.pullbackAlong Y q h :=
  rfl

theorem pullbackOverField_boundary_length (k' : Type u)
    [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (h : Y ⟶ T.scheme) :
    (T.pullbackOverField Y k' q h).boundary.length = T.boundary.length :=
  List.length_map _

theorem pullbackAlong_boundary_length (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) :
    (T.pullbackAlong Y q h).boundary.length = T.boundary.length :=
  (congrArg List.length (MarkedIdealWithBoundary.pullbackAlong_boundary T Y q h)).trans (List.length_map _)


end

end MarkedIdealWithBoundary

def pullbackOverFieldIndex (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (h : Y ⟶ T.scheme) :
    Fin T.boundary.length → Fin (T.pullbackOverField Y k' q h).boundary.length :=
  Fin.cast (MarkedIdealWithBoundary.pullbackOverField_boundary_length T Y k' q h).symm

theorem pullbackOverFieldIndex_val (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (h : Y ⟶ T.scheme) (j : Fin T.boundary.length) :
    ((pullbackOverFieldIndex T Y k' q h j : Fin (T.pullbackOverField Y k' q h).boundary.length) : ℕ)
      = (j : ℕ) := rfl

def pullbackAlongIndex (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) :
    Fin T.boundary.length → Fin (T.pullbackAlong Y q h).boundary.length :=
  Fin.cast (MarkedIdealWithBoundary.pullbackAlong_boundary_length T Y q h).symm

theorem pullbackAlongIndex_val (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) (j : Fin T.boundary.length) :
    ((pullbackAlongIndex T Y q h j : Fin (T.pullbackAlong Y q h).boundary.length) : ℕ)
      = (j : ℕ) := rfl

def IsIrreducibleComponentOf {Y : Scheme.{u}} (C S : Set ↥Y) : Prop :=
  IsIrreducible C ∧ C ⊆ S ∧ ∀ C' : Set ↥Y, IsIrreducible C' → C ⊆ C' → C' ⊆ S → C' = C

theorem mem_intersectionComponents_iff {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) (C : Set ↥Y) :
    C ∈ intersectionComponents L J ↔ IsIrreducibleComponentOf C ↑(intersectionIdeal L J).support :=
  Iff.rfl

abbrev transformedBoundary {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) : List X'.IdealSheafData :=
  L.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]

theorem transformedBoundary_length {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) :
    (transformedBoundary π Z L).length = L.length + 1 := by
  simp [transformedBoundary]

def strictTransformIndex {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) (j : Fin L.length) :
    Fin (transformedBoundary π Z L).length :=
  Fin.cast (transformedBoundary_length π Z L).symm j.castSucc

theorem strictTransformIndex_val {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) (j : Fin L.length) :
    ((strictTransformIndex π Z L j : Fin (transformedBoundary π Z L).length) : ℕ) = (j : ℕ) := rfl

def exceptionalIndex {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) : Fin (transformedBoundary π Z L).length :=
  Fin.cast (transformedBoundary_length π Z L).symm (Fin.last L.length)

theorem exceptionalIndex_val {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) :
    ((exceptionalIndex π Z L : Fin (transformedBoundary π Z L).length) : ℕ) = L.length := rfl

def preimageStrictTransformIndex {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData)
    (J' : Finset (Fin (transformedBoundary π Z L).length)) : Finset (Fin L.length) :=
  Finset.univ.filter fun j => strictTransformIndex π Z L j ∈ J'

theorem mem_preimageStrictTransformIndex_iff {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData)
    (J' : Finset (Fin (transformedBoundary π Z L).length)) (j : Fin L.length) :
    j ∈ preimageStrictTransformIndex π Z L J' ↔ strictTransformIndex π Z L j ∈ J' := by
  simp [preimageStrictTransformIndex]

def componentUnionOpens {Y : Scheme.{u}} (L : List Y.IdealSheafData) (J : Finset (Fin L.length))
    (𝒞 : Set (Set ↥Y)) (hop : IsOpen (⇑(intersectionIdeal L J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    (intersectionIdeal L J).subscheme.Opens :=
  ⟨⇑(intersectionIdeal L J).subschemeι ⁻¹' ⋃₀ 𝒞, hop⟩

def componentUnionIdeal {Y : Scheme.{u}} (L : List Y.IdealSheafData) (J : Finset (Fin L.length))
    (𝒞 : Set (Set ↥Y)) (hop : IsOpen (⇑(intersectionIdeal L J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    Y.IdealSheafData :=
  Scheme.Hom.ker ((componentUnionOpens L J 𝒞 hop).ι ≫ (intersectionIdeal L J).subschemeι)

theorem componentUnionIdeal_eq_ker {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) (𝒞 : Set (Set ↥Y))
    (hop : IsOpen (⇑(intersectionIdeal L J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    componentUnionIdeal L J 𝒞 hop =
      Scheme.Hom.ker ((componentUnionOpens L J 𝒞 hop).ι ≫ (intersectionIdeal L J).subschemeι) := rfl

structure MonomialGeometryHypotheses : Prop where
  card_lt_dim : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ J : Finset (Fin T.boundary.length),
      (intersectionComponents T.boundary J).Nonempty → J.card < krullDimSucc T.scheme
  flat_comap_center : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
      (g : Y ⟶ T.scheme) [Flat g],
      (T.pullbackOverField Y k' q g).IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme)),
        𝒞 ⊆ intersectionComponents T.boundary J →
        ∀ hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞),
          ∃ hop' : IsOpen (⇑(intersectionIdeal (T.pullbackOverField Y k' q g).boundary
                  (J.image (pullbackOverFieldIndex T Y k' q g))).subschemeι ⁻¹'
                ⋃₀ {C' : Set ↥Y | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
                    (J.image (pullbackOverFieldIndex T Y k' q g)) ∧
                  ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C}),
            (componentUnionIdeal T.boundary J 𝒞 hop).comap g =
              componentUnionIdeal (T.pullbackOverField Y k' q g).boundary
                (J.image (pullbackOverFieldIndex T Y k' q g))
                {C' : Set ↥Y | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
                    (J.image (pullbackOverFieldIndex T Y k' q g)) ∧
                  ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C} hop'
  center_smooth : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme)),
      𝒞 ⊆ intersectionComponents T.boundary J →
      ∀ hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞),
        Smooth ((componentUnionIdeal T.boundary J 𝒞 hop).subschemeι ≫ T.structMap)
  center_snc : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme)),
      𝒞 ⊆ intersectionComponents T.boundary J →
      ∀ hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞),
        HasStrictNormalCrossingsWith T.structMap (componentUnionIdeal T.boundary J 𝒞 hop) T.boundary
  center_support : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme)),
      𝒞 ⊆ intersectionComponents T.boundary J →
      ∀ hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞),
        (↑(componentUnionIdeal T.boundary J 𝒞 hop).support : Set ↥T.scheme) = ⋃₀ 𝒞
  blowup_total_transform : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ Z : T.scheme.IdealSheafData,
      Smooth (Z.subschemeι ≫ T.structMap) →
      HasStrictNormalCrossingsWith T.structMap Z T.boundary →
      ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
      ∀ D ∈ T.boundary, ∀ x' : ↥X',
        ∃ (U' : X'.Opens) (ε : ℕ), x' ∈ U' ∧ (ε = 0 ∨ ε = 1) ∧
          (ε = 1 ↔ ∃ V : T.scheme.Opens, π x' ∈ V ∧
            ((↑Z.support : Set ↥T.scheme) ∩ (V : Set ↥T.scheme)) ⊆ (↑D.support : Set ↥T.scheme)) ∧
          (D.comap π).comap U'.ι =
            (Blowup.strictTransform π Z D).comap U'.ι * ((Blowup.exceptionalIdeal π Z).comap U'.ι) ^ ε
  flat_components_down : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
      (g : Y ⟶ T.scheme) [Flat g],
      (T.pullbackOverField Y k' q g).IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)) (C' : Set ↥Y),
        C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
            (J.image (pullbackOverFieldIndex T Y k' q g)) →
        ∃ C ∈ intersectionComponents T.boundary J,
          Set.MapsTo (⇑g) C' C ∧
            ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ
  flat_components_up : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
      (g : Y ⟶ T.scheme) [Flat g],
      (T.pullbackOverField Y k' q g).IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
        C ∈ intersectionComponents T.boundary J →
        ∀ y : ↥Y, g y ∈ C →
          ∃ C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
              (J.image (pullbackOverFieldIndex T Y k' q g)),
            y ∈ C' ∧
              ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ
  smooth_components_down : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h],
      h ≫ T.structMap = q →
      (T.pullbackAlong Y q h).IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)) (C' : Set ↥Y),
        C' ∈ intersectionComponents (T.pullbackAlong Y q h).boundary
            (J.image (pullbackAlongIndex T Y q h)) →
        ∃ C ∈ intersectionComponents T.boundary J,
          Set.MapsTo (⇑h) C' C ∧
            ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → h ξ' = ξ
  smooth_components_up : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h],
      h ≫ T.structMap = q →
      (T.pullbackAlong Y q h).IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
        C ∈ intersectionComponents T.boundary J →
        ∀ y : ↥Y, h y ∈ C →
          ∃ C' ∈ intersectionComponents (T.pullbackAlong Y q h).boundary
              (J.image (pullbackAlongIndex T Y q h)),
            y ∈ C' ∧
              ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → h ξ' = ξ
  components_disjoint : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ J : Finset (Fin T.boundary.length),
      ∀ C ∈ intersectionComponents T.boundary J, ∀ C' ∈ intersectionComponents T.boundary J, C ≠ C' → Disjoint C C'
  components_finite : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ J : Finset (Fin T.boundary.length), (intersectionComponents T.boundary J).Finite
  components_subset_divisor_iff : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
      C ∈ intersectionComponents T.boundary J →
      ∀ i : Fin T.boundary.length,
        (C ⊆ (↑(T.boundary.get i).support : Set ↥T.scheme) ↔ i ∈ J)
  transformed_components : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J₀ : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme)),
      𝒞 ⊆ intersectionComponents T.boundary J₀ →
      ∀ hop : IsOpen (⇑(intersectionIdeal T.boundary J₀).subschemeι ⁻¹' ⋃₀ 𝒞),
      ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme),
        Blowup.IsBlowupAlongIdealSheaf π (componentUnionIdeal T.boundary J₀ 𝒞 hop) →
        ∀ (J : Finset (Fin T.boundary.length)) (C' : Set ↥X'),
          C' ∈ intersectionComponents
              (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
              (J.image (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)) →
          ∀ ξ' : ↥X', IsGenericPoint ξ' C' →
            ξ' ∉ (Blowup.exceptionalIdeal π (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support ∧
              ∃ C ∈ intersectionComponents T.boundary J, C ∉ 𝒞 ∧
                C' = closure ((⇑π ⁻¹' C) \
                    (↑(Blowup.exceptionalIdeal π (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support :
                      Set ↥X')) ∧
                  ∀ ξ : ↥T.scheme, IsGenericPoint ξ C → π ξ' = ξ
  level_schemeDim_le : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
      krullDimSucc (s.toSequenceOfBlowups.schemeAt i) ≤ T.krullDimSucc
  stratum_smooth : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ J : Finset (Fin T.boundary.length),
      Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap)
  level_valid : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length → (T.transformAt s i).IsAdmissible
  orderAt_bounded : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ I : T.scheme.IdealSheafData, NonzeroOnComponents I →
      ∃ B : ℕ, ∀ x : ↥T.scheme, orderAt I x ≤ (B : ℕ∞)
  orderAt_comap_off_exceptional : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (Z : T.scheme.IdealSheafData), Blowup.IsBlowupAlongIdealSheaf π Z →
      ∀ x' : ↥X', x' ∉ (Blowup.exceptionalIdeal π Z).support →
        ∀ A : T.scheme.IdealSheafData, orderAt (A.comap π) x' = orderAt A (π x')
  orderAt_boundary_eq_one : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ D ∈ T.boundary, ∀ x : ↥T.scheme, x ∈ D.support → orderAt D x = 1
  sUnion_isOpen : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme)),
      𝒞 ⊆ intersectionComponents T.boundary J →
      IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)
  withBoundary_valid : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ E' : List T.scheme.IdealSheafData, MarkedIdealWithBoundary.SameNontrivialBoundary T.boundary E' →
      (T.withBoundary E').IsAdmissible


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.IntersectionComponentCodimension
section

open TopologicalSpace


namespace MonomialCodimension

theorem lt_krullDimSucc_of_le_ringKrullDim_stalk (X : Scheme.{u}) (x : ↥X) (n : ℕ)
    (hn : (n : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x))
    (hfin : topologicalKrullDim ↥X ≠ ⊤) : n < krullDimSucc X := by
  have hn' : ((n : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := hn
  have hle : ((n : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim ↥X :=
    le_trans hn' (ringKrullDim_stalk_le_topologicalKrullDim X x)
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]
  by_cases hb : topologicalKrullDim ↥X = ⊥
  · rw [hb] at hle
    exact absurd (le_bot_iff.mp hle) WithBot.coe_ne_bot
  · obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hb
    rw [← he] at hle hfin ⊢
    have he' : e ≠ ⊤ := by
      intro hcon
      apply hfin
      rw [hcon]
      simp
    lift e to ℕ using he' with m
    rw [withBotSuccToNat_coe]
    have hmm : ((m : ℕ∞)).toNat = m := by simp
    rw [hmm]
    have hnm : n ≤ m := by exact_mod_cast hle
    omega

theorem card_lt_krullDimSucc_of_mem_intersectionComponents : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
      C ∈ intersectionComponents T.boundary J → J.card < krullDimSucc T.scheme := by
  classical
  intro T hT J C hC
  have hC' : IsIrreducible C ∧ C ⊆ (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) ∧
      ∀ C' : Set ↥T.scheme, IsIrreducible C' → C ⊆ C' →
        C' ⊆ (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) → C' = C :=
    (mem_intersectionComponents_iff T.boundary J C).mp hC
  obtain ⟨hirr, hsub, -⟩ := hC'
  obtain ⟨x, hxC⟩ := hirr.nonempty
  have hxsupp : x ∈ (intersectionIdeal T.boundary J).support := hsub hxC
  have hxj : ∀ j ∈ J, x ∈ (T.boundary.get j).support := by
    intro j hj
    rw [mem_support_iff_stalkIdeal_ne_top]
    intro htop
    rw [mem_support_iff_stalkIdeal_ne_top] at hxsupp
    have hle : T.boundary.get j ≤ intersectionIdeal T.boundary J := by
      rw [intersectionIdeal_eq_iSup]
      exact le_iSup₂ (f := fun (i : Fin T.boundary.length) (_ : i ∈ J) => T.boundary.get i) j hj
    have h1 := stalkIdeal_mono hle x
    rw [htop] at h1
    exact hxsupp (top_le_iff.mp h1)
  obtain ⟨-, hsnc⟩ := (inStrictNormalCrossingPosition_iff T.structMap T.boundary).mp hT.snc
  obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := (hsnc x).exists_etaleChart
  obtain ⟨V, hVB, hxV, hVU⟩ :=
    Opens.isBasis_iff_nbhd.mp T.scheme.isBasis_affineOpens hxU
  have hV : IsAffineOpen V := hVB
  have hex : ∀ j : Fin T.boundary.length, j ∈ J → ∃ t : Fin m, a (j : ℕ) = some t := by
    intro j hj
    have hne : a (j : ℕ) ≠ none := by
      intro hj'
      have htop := hnone (j : ℕ) j.isLt hj'
      have hx' := hxj j hj
      rw [List.get_eq_getElem] at hx'
      exact Scheme.IdealSheafData.notMem_support_of_comap_ι_eq_top _ htop hxU hx'
    exact Option.ne_none_iff_exists'.mp hne
  choose F hFspec using hex
  have hGinj : Function.Injective
      (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2) := by
    intro p q h
    have h1 : a (q.1 : ℕ) = some (F p.1 p.2) := by
      rw [hFspec q.1 q.2]
      exact congrArg Option.some h.symm
    have h2 := hinj (p.1 : ℕ) p.1.isLt (q.1 : ℕ) q.1.isLt (F p.1 p.2) (hFspec p.1 p.2) h1
    exact Subtype.ext (Fin.val_injective h2)
  have hcard : (J.attach.image
      (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2)).card = J.card := by
    rw [Finset.card_image_of_injective _ hGinj, Finset.card_attach]
  have hmem : ∀ t ∈ J.attach.image
      (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2),
      (c.restrict hVU).coord t ∈ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    intro t ht
    obtain ⟨p, -, hpt⟩ := Finset.mem_image.mp ht
    have hat : a (p.1 : ℕ) = some t := by
      rw [hFspec p.1 p.2]
      exact congrArg Option.some hpt
    have hU' := hsome (p.1 : ℕ) p.1.isLt t hat
    have hV' := restrictIdeal_eq_restrict_coordIdeal_of_le hVU c _ {t} hU'
    have hx' := hxj p.1 p.2
    rw [List.get_eq_getElem] at hx'
    exact coord_mem_primeIdealOf_of_restrictIdeal_eq_coordIdeal_singleton hV
      (c.restrict hVU) t _ hV' x hxV hx'
  have hle2 := card_le_ringKrullDim_stalk hV (c.restrict hVU) x hxV
    (J.attach.image (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2)) hmem
  have hfin : topologicalKrullDim ↥T.scheme ≠ ⊤ := ne_of_lt hT.topologicalKrullDim_lt_top
  have hlt := lt_krullDimSucc_of_le_ringKrullDim_stalk T.scheme x _ hle2 hfin
  rwa [hcard] at hlt

theorem card_lt_krullDimSucc_of_nonempty (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (hJ : (intersectionComponents T.boundary J).Nonempty) :
    J.card < krullDimSucc T.scheme := by
  obtain ⟨C, hC⟩ := hJ
  exact card_lt_krullDimSucc_of_mem_intersectionComponents T hT J C hC

end MonomialCodimension

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.IntersectionComponents
section


section

private theorem mem_irreducibleComponents_iff_isIrreducible_and_maximal_consolidated362 {α : Type*}
    [TopologicalSpace α] (s : Set α) :
    s ∈ irreducibleComponents α ↔
      IsIrreducible s ∧ ∀ t : Set α, IsIrreducible t → s ⊆ t → t ⊆ s :=
  ⟨fun h => ⟨h.1, fun _ ht hst => h.2 ht hst⟩, fun h => ⟨h.1, fun t ht hst => h.2 t ht hst⟩⟩

private theorem maximal_irreducible_subset_range_iff_consolidated362 {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} (hf : Topology.IsClosedEmbedding f) {S : Set β}
    (hr : Set.range f = S) (C : Set β) :
    (IsIrreducible C ∧ C ⊆ S ∧ ∀ C' : Set β, IsIrreducible C' → C ⊆ C' → C' ⊆ S → C' = C)
      ↔ ∃ D ∈ irreducibleComponents α, f '' D = C := by
  constructor
  · rintro ⟨hirr, hsub, hmax⟩
    have hCr : C ⊆ Set.range f := by rw [hr]; exact hsub
    have himg : f '' (f ⁻¹' C) = C := Set.image_preimage_eq_of_subset hCr
    refine ⟨f ⁻¹' C, (mem_irreducibleComponents_iff_isIrreducible_and_maximal_consolidated362 _).mpr ⟨?_, ?_⟩, himg⟩
    · exact isIrreducible_preimage_of_isEmbedding hf.toIsEmbedding hirr hCr
    · intro t ht hDt x hx
      have himgt : IsIrreducible (f '' t) := ht.image f hf.continuous.continuousOn
      have hCt : C ⊆ f '' t := by
        rw [← himg]
        exact Set.image_mono hDt
      have htS : f '' t ⊆ S := by
        rw [← hr]
        exact Set.image_subset_range _ _
      have heq : f '' t = C := hmax _ himgt hCt htS
      have hmem : f x ∈ C := by
        rw [← heq]
        exact ⟨x, hx, rfl⟩
      exact hmem
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨hDirr, hDmax⟩ := (mem_irreducibleComponents_iff_isIrreducible_and_maximal_consolidated362 _).mp hD
    refine ⟨hDirr.image f hf.continuous.continuousOn, ?_, ?_⟩
    · rw [← hr]
      exact Set.image_subset_range _ _
    · intro C' hC' hsub' hS'
      have hC'r : C' ⊆ Set.range f := by rw [hr]; exact hS'
      have hirr' : IsIrreducible (f ⁻¹' C') :=
        isIrreducible_preimage_of_isEmbedding hf.toIsEmbedding hC' hC'r
      have hDD : D ⊆ f ⁻¹' C' := fun x hx => hsub' ⟨x, hx, rfl⟩
      have h1 : f ⁻¹' C' ⊆ D := hDmax _ hirr' hDD
      have h2 : f '' (f ⁻¹' C') = C' := Set.image_preimage_eq_of_subset hC'r
      apply Set.Subset.antisymm
      · rw [← h2]
        exact Set.image_mono h1
      · exact hsub'

section
variable {Y : Scheme.{u}} (L : List Y.IdealSheafData) (J : Finset (Fin L.length)) (C : Set ↥Y)

theorem mem_intersectionComponents_iff_exists_irreducibleComponent :
    C ∈ intersectionComponents L J ↔
      ∃ D ∈ irreducibleComponents ↥(intersectionIdeal L J).subscheme,
        ⇑(intersectionIdeal L J).subschemeι '' D = C := by
  have hemb : Topology.IsClosedEmbedding ⇑(intersectionIdeal L J).subschemeι :=
    Scheme.Hom.isClosedEmbedding (intersectionIdeal L J).subschemeι
  have hrange : Set.range ⇑(intersectionIdeal L J).subschemeι
      = (↑(intersectionIdeal L J).support : Set ↥Y) :=
    Scheme.IdealSheafData.range_subschemeι _
  exact maximal_irreducible_subset_range_iff_consolidated362 hemb hrange C

theorem isClosed_of_mem_intersectionComponents (hC : C ∈ intersectionComponents L J) : IsClosed C := by
  obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent L J C).mp hC
  exact (Scheme.Hom.isClosedEmbedding (intersectionIdeal L J).subschemeι).isClosedMap _
    (isClosed_of_mem_irreducibleComponents _ hD)


end

theorem intersectionComponents_finite (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) : (intersectionComponents T.boundary J).Finite := by
  have := hT.isNoetherian
  have : TopologicalSpace.NoetherianSpace ↥(intersectionIdeal T.boundary J).subscheme := inferInstance
  have h : intersectionComponents T.boundary J =
      (fun D => ⇑(intersectionIdeal T.boundary J).subschemeι '' D) ''
        irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme := by
    ext C
    rw [mem_intersectionComponents_iff_exists_irreducibleComponent]
    exact Iff.rfl
  rw [h]
  exact Set.Finite.image _ (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents ..)

section
variable (T : MarkedIdealWithBoundary.{u}) (J : Finset (Fin T.boundary.length)) (hsm : Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap))
include hsm

private theorem irreducibleComponents_eq_of_inter_nonempty_of_smooth_consolidated362 :
    ∀ C₁ ∈ irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme,
      ∀ C₂ ∈ irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme,
        (C₁ ∩ C₂).Nonempty → C₁ = C₂ := by
  have := hsm
  rintro C₁ h₁ C₂ h₂ ⟨x, hx₁, hx₂⟩
  exact irreducibleComponents_eq_of_stalk_isDomain _
    (fun z => isDomain_stalk_of_smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap) z)
    h₁ h₂ hx₁ hx₂

theorem intersectionComponents_disjoint_of_smooth (C C' : Set ↥T.scheme) (hC : C ∈ intersectionComponents T.boundary J)
    (hC' : C' ∈ intersectionComponents T.boundary J) (hne : C ≠ C') : Disjoint C C' := by
  obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp hC
  obtain ⟨D', hD', rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp hC'
  have hinj : Function.Injective ⇑(intersectionIdeal T.boundary J).subschemeι :=
    (Scheme.Hom.isClosedEmbedding (intersectionIdeal T.boundary J).subschemeι).injective
  rw [Set.disjoint_left]
  rintro x ⟨d, hd, rfl⟩ ⟨d', hd', he⟩
  have hdd : d' = d := hinj he
  subst hdd
  have hDD : D = D' :=
    irreducibleComponents_eq_of_inter_nonempty_of_smooth_consolidated362 T J hsm D hD D' hD' ⟨d', hd, hd'⟩
  exact hne (by rw [hDD])


end

section
variable (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (J : Finset (Fin T.boundary.length))
include hT

theorem isOpen_preimage_sUnion_intersectionComponents (hsm : Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap))
    (𝒞 : Set (Set ↥T.scheme)) (h𝒞 : 𝒞 ⊆ intersectionComponents T.boundary J) :
    IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞) := by
  have := hT.isNoetherian
  have : TopologicalSpace.NoetherianSpace ↥(intersectionIdeal T.boundary J).subscheme := inferInstance
  have hinj : Function.Injective ⇑(intersectionIdeal T.boundary J).subschemeι :=
    (Scheme.Hom.isClosedEmbedding (intersectionIdeal T.boundary J).subschemeι).injective
  have key : ⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞 =
      ⋃₀ {D : Set ↥(intersectionIdeal T.boundary J).subscheme |
        D ∈ irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme ∧
          ⇑(intersectionIdeal T.boundary J).subschemeι '' D ∈ 𝒞} := by
    apply Set.Subset.antisymm
    · rintro x hx
      obtain ⟨C, hC𝒞, hxC⟩ := hx
      obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp (h𝒞 hC𝒞)
      obtain ⟨d, hd, hde⟩ := hxC
      have hdx : d = x := hinj hde
      subst hdx
      exact ⟨D, ⟨hD, hC𝒞⟩, hd⟩
    · rintro x ⟨D, ⟨hD, hD𝒞⟩, hxD⟩
      exact ⟨⇑(intersectionIdeal T.boundary J).subschemeι '' D, hD𝒞, ⟨x, hxD, rfl⟩⟩
  rw [key]
  exact isOpen_sUnion_of_subset_irreducibleComponents
    (irreducibleComponents_eq_of_inter_nonempty_of_smooth_consolidated362 T J hsm) (fun D hD => hD.1)

theorem componentUnionIdeal_support_eq_sUnion (𝒞 : Set (Set ↥T.scheme))
    (h𝒞 : 𝒞 ⊆ intersectionComponents T.boundary J)
    (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    (↑(componentUnionIdeal T.boundary J 𝒞 hop).support : Set ↥T.scheme) = ⋃₀ 𝒞 := by
  have := hT.isNoetherian
  have : TopologicalSpace.NoetherianSpace ↥(intersectionIdeal T.boundary J).subscheme := inferInstance
  have hqc : QuasiCompact ((componentUnionOpens T.boundary J 𝒞 hop).ι ≫
      (intersectionIdeal T.boundary J).subschemeι) := inferInstance
  have hsub : ⋃₀ 𝒞 ⊆ Set.range ⇑(intersectionIdeal T.boundary J).subschemeι := by
    rintro x ⟨C, hC, hxC⟩
    obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp (h𝒞 hC)
    obtain ⟨d, hd, rfl⟩ := hxC
    exact ⟨d, rfl⟩
  have h0 : ⇑((componentUnionOpens T.boundary J 𝒞 hop).ι ≫ (intersectionIdeal T.boundary J).subschemeι)
      = ⇑(intersectionIdeal T.boundary J).subschemeι ∘ ⇑(componentUnionOpens T.boundary J 𝒞 hop).ι := rfl
  have hr2 : Set.range ⇑(componentUnionOpens T.boundary J 𝒞 hop).ι
      = ⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞 :=
    Scheme.Opens.range_ι _
  have hrange : Set.range ⇑((componentUnionOpens T.boundary J 𝒞 hop).ι ≫
      (intersectionIdeal T.boundary J).subschemeι) = ⋃₀ 𝒞 := by
    rw [h0, Set.range_comp, hr2]
    exact Set.image_preimage_eq_of_subset hsub
  have hfin : 𝒞.Finite := (intersectionComponents_finite T hT J).subset h𝒞
  have hclosed : IsClosed (⋃₀ 𝒞) := by
    rw [Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion
      (fun C hC => isClosed_of_mem_intersectionComponents T.boundary J C (h𝒞 hC))
  have h1 : (↑(componentUnionIdeal T.boundary J 𝒞 hop).support : Set ↥T.scheme)
      = closure (Set.range ⇑((componentUnionOpens T.boundary J 𝒞 hop).ι ≫
          (intersectionIdeal T.boundary J).subschemeι)) :=
    Scheme.Hom.support_ker _
  rw [h1, hrange]
  exact hclosed.closure_eq


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.IntersectionComponentsFlatBaseChange
section

open TopologicalSpace

section

private theorem comap_biSup_finset_fin_consolidated359 {X Y : Scheme.{u}} (f : X ⟶ Y) {n : ℕ}
    (s : Finset (Fin n)) (F : Fin n → Y.IdealSheafData) :
    (⨆ i ∈ s, F i).comap f = ⨆ i ∈ s, (F i).comap f :=
  (Scheme.IdealSheafData.map_gc f).l_iSup₂

section
variable (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)

private theorem pullbackOverField_boundary_get_consolidated359 (j : Fin T.boundary.length) :
    (T.pullbackOverField Y k' q g).boundary.get (pullbackOverFieldIndex T Y k' q g j)
      = (T.boundary.get j).comap g := by
  have h : (T.pullbackOverField Y k' q g).boundary.get (pullbackOverFieldIndex T Y k' q g j)
      = (T.boundary.map fun D => D.comap g).get
          (Fin.cast (MarkedIdealWithBoundary.pullbackOverField_boundary_length T Y k' q g).symm j) := rfl
  rw [h]
  simp only [List.get_eq_getElem, List.getElem_map]
  rfl

theorem intersectionIdeal_pullbackOverField (J : Finset (Fin T.boundary.length)) :
    intersectionIdeal (T.pullbackOverField Y k' q g).boundary (J.image (pullbackOverFieldIndex T Y k' q g)) =
      (intersectionIdeal T.boundary J).comap g := by
  rw [intersectionIdeal_eq_iSup, intersectionIdeal_eq_iSup, comap_biSup_finset_fin_consolidated359]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun j' => iSup_le fun hj' => ?_
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hj'
    rw [pullbackOverField_boundary_get_consolidated359]
    exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)
  · refine iSup_le fun j => iSup_le fun hj => ?_
    rw [← pullbackOverField_boundary_get_consolidated359 T Y k' q g j]
    exact le_iSup_of_le (pullbackOverFieldIndex T Y k' q g j)
      (le_iSup_of_le (Finset.mem_image_of_mem _ hj) le_rfl)

theorem support_intersectionIdeal_pullbackOverField (J : Finset (Fin T.boundary.length)) :
    (↑(intersectionIdeal (T.pullbackOverField Y k' q g).boundary
          (J.image (pullbackOverFieldIndex T Y k' q g))).support :
        Set ↥(T.pullbackOverField Y k' q g).scheme) =
      ⇑g ⁻¹' (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) := by
  have h : intersectionIdeal (T.pullbackOverField Y k' q g).boundary (J.image (pullbackOverFieldIndex T Y k' q g))
      = (intersectionIdeal T.boundary J).comap g := intersectionIdeal_pullbackOverField T Y k' q g J
  have h2 : (↑((intersectionIdeal T.boundary J).comap g).support : Set ↥Y)
      = ⇑g ⁻¹' (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) :=
    support_comap g (intersectionIdeal T.boundary J)
  rw [h]
  exact h2

theorem mem_intersectionComponents_pullbackOverField_iff (J : Finset (Fin T.boundary.length)) (C' : Set ↥Y) :
    C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary (J.image (pullbackOverFieldIndex T Y k' q g)) ↔
      IsIrreducibleComponentOf C' (⇑g ⁻¹' (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme)) := by
  have h1 := mem_intersectionComponents_iff (T.pullbackOverField Y k' q g).boundary
      (J.image (pullbackOverFieldIndex T Y k' q g)) C'
  rw [support_intersectionIdeal_pullbackOverField T Y k' q g J] at h1
  exact h1


end

theorem IsIrreducibleComponentOf.exists_isGenericPoint {Y : Scheme.{u}} {C S : Set ↥Y}
    (h : IsIrreducibleComponentOf C S) (hS : IsClosed S) :
    ∃ ξ : ↥Y, IsGenericPoint ξ C := by
  obtain ⟨hirr, hsub, hmax⟩ := h
  have hcl : closure C = C :=
    hmax (closure C) hirr.closure subset_closure (hS.closure_subset_iff.mpr hsub)
  have hCclosed : IsClosed C := closure_eq_iff_isClosed.mp hcl
  exact QuasiSober.sober hirr hCclosed

private theorem isPreirreducible_sUnion_of_isChain_consolidated359 {α : Type u} [TopologicalSpace α]
    (c : Set (Set α)) (hcc : IsChain (· ⊆ ·) c)
    (hirr : ∀ t ∈ c, IsPreirreducible t) : IsPreirreducible (⋃₀ c) := by
  intro u v hu hv hxne hyne
  obtain ⟨x, hxU, hxu⟩ := hxne
  obtain ⟨y, hyU, hyv⟩ := hyne
  obtain ⟨t₁, ht₁c, hxt₁⟩ := Set.mem_sUnion.mp hxU
  obtain ⟨t₂, ht₂c, hyt₂⟩ := Set.mem_sUnion.mp hyU
  rcases eq_or_ne t₁ t₂ with rfl | hne
  · obtain ⟨z, hzt, hzuv⟩ := hirr t₁ ht₁c u v hu hv ⟨x, hxt₁, hxu⟩ ⟨y, hyt₂, hyv⟩
    exact ⟨z, Set.mem_sUnion.mpr ⟨t₁, ht₁c, hzt⟩, hzuv⟩
  · rcases hcc ht₁c ht₂c hne with h | h
    · obtain ⟨z, hzt, hzuv⟩ := hirr t₂ ht₂c u v hu hv ⟨x, h hxt₁, hxu⟩ ⟨y, hyt₂, hyv⟩
      exact ⟨z, Set.mem_sUnion.mpr ⟨t₂, ht₂c, hzt⟩, hzuv⟩
    · obtain ⟨z, hzt, hzuv⟩ := hirr t₁ ht₁c u v hu hv ⟨x, hxt₁, hxu⟩ ⟨y, h hyt₂, hyv⟩
      exact ⟨z, Set.mem_sUnion.mpr ⟨t₁, ht₁c, hzt⟩, hzuv⟩

theorem exists_isIrreducibleComponentOf {Y : Scheme.{u}} (S A : Set ↥Y) (hA : IsIrreducible A)
    (hAS : A ⊆ S) :
    ∃ C : Set ↥Y, IsIrreducibleComponentOf C S ∧ A ⊆ C := by
  have hchain : ∀ c ⊆ {C : Set ↥Y | IsIrreducible C ∧ C ⊆ S}, IsChain (· ⊆ ·) c →
      c.Nonempty → ∃ ub ∈ {C : Set ↥Y | IsIrreducible C ∧ C ⊆ S}, ∀ s ∈ c, s ⊆ ub := by
    intro c hcS hcc hcn
    obtain ⟨t, htc⟩ := hcn
    have hne : (⋃₀ c).Nonempty := by
      obtain ⟨x, hx⟩ := (hcS htc).1.1
      exact ⟨x, Set.mem_sUnion.mpr ⟨t, htc, hx⟩⟩
    refine ⟨⋃₀ c, ⟨⟨hne, isPreirreducible_sUnion_of_isChain_consolidated359 c hcc
        fun s hs => (hcS hs).1.2⟩, Set.sUnion_subset fun s hs => (hcS hs).2⟩,
      fun s hs => Set.subset_sUnion_of_mem hs⟩
  obtain ⟨C, hAC, hmax⟩ :=
    zorn_subset_nonempty {C : Set ↥Y | IsIrreducible C ∧ C ⊆ S} hchain A ⟨hA, hAS⟩
  have hmem : IsIrreducible C ∧ C ⊆ S := hmax.1
  refine ⟨C, ⟨hmem.1, hmem.2, ?_⟩, hAC⟩
  intro C' hC' hCle hC'S
  exact subset_antisymm (hmax.2 ⟨hC', hC'S⟩ hCle) hCle

section
variable {X Y : Scheme.{u}} (g : Y ⟶ X) (hg : GeneralizingMap (fun y : ↥Y => g y)) {S : Set ↥X} (hS : IsClosed S)
include hg hS

theorem IsIrreducibleComponentOf.closure_image_genericPoint {C' : Set ↥Y}
    (hC' : IsIrreducibleComponentOf C' (⇑g ⁻¹' S)) {ξ' : ↥Y} (hξ' : IsGenericPoint ξ' C') :
    IsIrreducibleComponentOf (closure {g ξ'}) S ∧ Set.MapsTo (⇑g) C' (closure {g ξ'}) := by
  have hC'unf : IsIrreducible C' ∧ C' ⊆ ⇑g ⁻¹' S ∧
      ∀ D : Set ↥Y, IsIrreducible D → C' ⊆ D → D ⊆ ⇑g ⁻¹' S → D = C' := hC'
  obtain ⟨-, hsub, hmax⟩ := hC'unf
  have hξ'eq : closure ({ξ'} : Set ↥Y) = C' := hξ'
  have hcont : Continuous (fun y : ↥Y => g y) := g.continuous
  have himg : ∀ z w : ↥Y, z ∈ closure ({w} : Set ↥Y) → g z ∈ closure ({g w} : Set ↥X) := by
    intro z w hz
    have h2 : (fun y : ↥Y => g y) '' closure ({w} : Set ↥Y)
        ⊆ closure ((fun y : ↥Y => g y) '' ({w} : Set ↥Y)) :=
      image_closure_subset_closure_image hcont
    have h3 : g z ∈ closure ((fun y : ↥Y => g y) '' ({w} : Set ↥Y)) := h2 ⟨z, hz, rfl⟩
    rwa [Set.image_singleton] at h3
  have hξ'mem : ξ' ∈ C' := by
    rw [← hξ'eq]
    exact subset_closure rfl
  have hgS : g ξ' ∈ S := hsub hξ'mem
  have hDsub : closure ({g ξ'} : Set ↥X) ⊆ S :=
    hS.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hgS)
  have hDirr : IsIrreducible (closure ({g ξ'} : Set ↥X)) := isIrreducible_singleton.closure
  have hmaps : Set.MapsTo (⇑g) C' (closure ({g ξ'} : Set ↥X)) := by
    intro y hy
    refine himg y ξ' ?_
    rw [hξ'eq]
    exact hy
  have hirred : IsIrreducible (closure ({g ξ'} : Set ↥X)) ∧
      closure ({g ξ'} : Set ↥X) ⊆ S ∧
      ∀ E : Set ↥X, IsIrreducible E → closure ({g ξ'} : Set ↥X) ⊆ E → E ⊆ S →
        E = closure ({g ξ'} : Set ↥X) := by
    refine ⟨hDirr, hDsub, ?_⟩
    intro E hE hsubE hES
    obtain ⟨η, hη⟩ := QuasiSober.sober hE.closure (isClosed_closure (s := E))
    have hηeq : closure ({η} : Set ↥X) = closure E := hη
    have hgξ'E : g ξ' ∈ E := hsubE (subset_closure rfl)
    have hspec0 : (η : ↥X) ⤳ g ξ' := by
      refine specializes_iff_mem_closure.mpr ?_
      rw [hηeq]
      exact subset_closure hgξ'E
    obtain ⟨ξ'', hspec, hgη⟩ := hg hspec0
    have hgη' : g ξ'' = η := hgη
    have hspec' : ξ' ∈ closure ({ξ''} : Set ↥Y) := specializes_iff_mem_closure.mp hspec
    have hclE : closure E ⊆ S := hS.closure_subset_iff.mpr hES
    have hsub2 : closure ({ξ''} : Set ↥Y) ⊆ ⇑g ⁻¹' S := by
      intro z hz
      have h3 : g z ∈ closure ({g ξ''} : Set ↥X) := himg z ξ'' hz
      rw [hgη', hηeq] at h3
      exact hclE h3
    have hsub3 : C' ⊆ closure ({ξ''} : Set ↥Y) := by
      rw [← hξ'eq]
      exact closure_minimal (Set.singleton_subset_iff.mpr hspec') isClosed_closure
    have heq : closure ({ξ''} : Set ↥Y) = C' :=
      hmax (closure ({ξ''} : Set ↥Y)) isIrreducible_singleton.closure hsub3 hsub2
    have hξ''mem : ξ'' ∈ C' := by
      rw [← heq]
      exact subset_closure rfl
    have hηmem : η ∈ closure ({g ξ'} : Set ↥X) := by
      have h4 := hmaps hξ''mem
      rwa [hgη'] at h4
    have hZsub : closure E ⊆ closure ({g ξ'} : Set ↥X) := by
      rw [← hηeq]
      exact closure_minimal (Set.singleton_subset_iff.mpr hηmem) isClosed_closure
    exact Set.Subset.antisymm (Set.Subset.trans subset_closure hZsub) hsubE
  exact ⟨hirred, hmaps⟩

theorem exists_isIrreducibleComponentOf_preimage {C : Set ↥X}
    (hC : IsIrreducibleComponentOf C S) (y : ↥Y) (hy : g y ∈ C) :
    ∃ C' : Set ↥Y, IsIrreducibleComponentOf C' (⇑g ⁻¹' S) ∧ y ∈ C' ∧ Set.MapsTo (⇑g) C' C ∧
      ∀ (ξ' : ↥Y) (ξ : ↥X), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ := by
  classical
  have hcont : Continuous (⇑g : ↥Y → ↥X) := g.continuous
  have hSY : IsClosed (⇑g ⁻¹' S) := IsClosed.preimage hcont hS
  obtain ⟨ξ, hξ⟩ := IsIrreducibleComponentOf.exists_isGenericPoint hC hS
  have hξeq : closure ({ξ} : Set ↥X) = C := hξ
  obtain ⟨-, hCS, hCmax⟩ := hC
  have hmemC : g y ∈ closure ({ξ} : Set ↥X) := by
    rw [hξeq]; exact hy
  have hspec : ξ ⤳ g y := specializes_iff_mem_closure.mpr hmemC
  obtain ⟨y₀, hy₀spec, hy₀eq⟩ := hg hspec
  have hgy₀ : g y₀ = ξ := hy₀eq
  have hymem : y ∈ closure ({y₀} : Set ↥Y) := specializes_iff_mem_closure.mp hy₀spec
  have hξC : ξ ∈ C := by
    have h0 : ξ ∈ ({ξ} : Set ↥X) := Set.mem_singleton_iff.mpr rfl
    have h1 := subset_closure h0
    rwa [hξeq] at h1
  have hy₀S : y₀ ∈ ⇑g ⁻¹' S := by
    have h2 : g y₀ ∈ S := by rw [hgy₀]; exact hCS hξC
    exact h2
  have hsub : closure ({y₀} : Set ↥Y) ⊆ ⇑g ⁻¹' S :=
    closure_minimal (Set.singleton_subset_iff.mpr hy₀S) hSY
  obtain ⟨C', hC', hAC'⟩ :=
    exists_isIrreducibleComponentOf (⇑g ⁻¹' S) (closure ({y₀} : Set ↥Y))
      (IsIrreducible.closure isIrreducible_singleton) hsub
  have hy₀C' : y₀ ∈ C' := by
    have h3 : y₀ ∈ ({y₀} : Set ↥Y) := Set.mem_singleton_iff.mpr rfl
    exact hAC' (subset_closure h3)
  have key : ∀ ζ : ↥Y, IsGenericPoint ζ C' → closure ({g ζ} : Set ↥X) = C := by
    intro ζ hζ
    obtain ⟨hcomp, -⟩ := IsIrreducibleComponentOf.closure_image_genericPoint g hg hS hC' hζ
    obtain ⟨hirr2, hsub2, -⟩ := hcomp
    have hζeq : closure ({ζ} : Set ↥Y) = C' := hζ
    have h4 : y₀ ∈ closure ({ζ} : Set ↥Y) := by rw [hζeq]; exact hy₀C'
    have h6 := image_closure_subset_closure_image hcont (Set.mem_image_of_mem (⇑g) h4)
    rw [Set.image_singleton] at h6
    rw [hgy₀] at h6
    have hCsub : C ⊆ closure ({g ζ} : Set ↥X) := by
      rw [← hξeq]
      exact closure_minimal (Set.singleton_subset_iff.mpr h6) isClosed_closure
    exact hCmax (closure ({g ζ} : Set ↥X)) hirr2 hCsub hsub2
  obtain ⟨ζ₀, hζ₀⟩ := IsIrreducibleComponentOf.exists_isGenericPoint hC' hSY
  have hmapsC : Set.MapsTo (⇑g) C' C := by
    have h7 := (IsIrreducibleComponentOf.closure_image_genericPoint g hg hS hC' hζ₀).2
    rwa [key ζ₀ hζ₀] at h7
  refine ⟨C', hC', hAC' hymem, hmapsC, ?_⟩
  intro ζ ξ₂ hgen1 hgen2
  have h8 : closure ({g ζ} : Set ↥X) = C := key ζ hgen1
  have h9 : closure ({ξ₂} : Set ↥X) = C := hgen2
  have hm1 : g ζ ∈ closure ({ξ₂} : Set ↥X) := by
    rw [h9, ← h8]
    exact subset_closure (Set.mem_singleton_iff.mpr rfl)
  have hm2 : ξ₂ ∈ closure ({g ζ} : Set ↥X) := by
    rw [h8, ← h9]
    exact subset_closure (Set.mem_singleton_iff.mpr rfl)
  exact ((specializes_iff_mem_closure.mpr hm2).antisymm
    (specializes_iff_mem_closure.mpr hm1)).eq


end

private theorem exists_isPullback_comapSubscheme_consolidated359 {X Y : Scheme.{u}} (W : X.IdealSheafData)
    (g : Y ⟶ X) :
    ∃ c : (W.comap g).subscheme ⟶ W.subscheme,
      IsPullback c (W.comap g).subschemeι W.subschemeι g := by
  obtain ⟨e, he⟩ : ∃ e : (W.comap g).subscheme ≅ Limits.pullback g W.subschemeι,
      e.hom ≫ Limits.pullback.fst g W.subschemeι = (W.comap g).subschemeι :=
    ⟨W.comapIso g, W.comapIso_hom_fst g⟩
  refine ⟨e.hom ≫ Limits.pullback.snd g W.subschemeι, ?_⟩
  have hsq : (W.comap g).subschemeι ≫ g
      = (e.hom ≫ Limits.pullback.snd g W.subschemeι) ≫ W.subschemeι := by
    rw [← he]
    simp only [Category.assoc, Limits.pullback.condition]
  exact (IsPullback.of_iso_pullback ⟨hsq⟩ e he rfl).flip

def comapSubschemeHom {X Y : Scheme.{u}} (W : X.IdealSheafData) (g : Y ⟶ X) :
    (W.comap g).subscheme ⟶ W.subscheme :=
  (exists_isPullback_comapSubscheme_consolidated359 W g).choose

section
variable {X Y : Scheme.{u}} (W : X.IdealSheafData) (g : Y ⟶ X)

theorem isPullback_comapSubschemeHom :
    IsPullback (comapSubschemeHom W g) (W.comap g).subschemeι W.subschemeι g :=
  (exists_isPullback_comapSubscheme_consolidated359 W g).choose_spec

theorem comapSubschemeHom_comp_subschemeι :
    comapSubschemeHom W g ≫ W.subschemeι = (W.comap g).subschemeι ≫ g :=
  (isPullback_comapSubschemeHom W g).w


end

section
variable (T : MarkedIdealWithBoundary.{u}) (_hT : T.IsAdmissible) (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) [Flat g] (_hT' : (T.pullbackOverField Y k' q g).IsAdmissible) (J : Finset (Fin T.boundary.length))
include _hT _hT'

theorem exists_intersectionComponents_mapsTo_of_flat (C' : Set ↥Y)
    (hC' : C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
      (J.image (pullbackOverFieldIndex T Y k' q g))) :
    ∃ C ∈ intersectionComponents T.boundary J,
      Set.MapsTo (⇑g) C' C ∧
        ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ := by
  have hg : GeneralizingMap (fun y : ↥Y => g y) :=
    AlgebraicGeometry.Flat.generalizingMap (f := g)
  have hS : IsClosed (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) :=
    (intersectionIdeal T.boundary J).support.2
  have hcomp : IsIrreducibleComponentOf C'
      (⇑g ⁻¹' (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme)) :=
    (mem_intersectionComponents_pullbackOverField_iff T Y k' q g J C').mp hC'
  have hS' : IsClosed (⇑g ⁻¹' (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme)) :=
    hS.preimage g.continuous
  obtain ⟨ξ₀, hξ₀⟩ := IsIrreducibleComponentOf.exists_isGenericPoint hcomp hS'
  obtain ⟨hCmem, hmaps⟩ := IsIrreducibleComponentOf.closure_image_genericPoint g hg hS hcomp hξ₀
  refine ⟨closure ({g ξ₀} : Set ↥T.scheme),
    (mem_intersectionComponents_iff T.boundary J (closure ({g ξ₀} : Set ↥T.scheme))).mpr hCmem, hmaps, ?_⟩
  intro ξ' ξ hξ' hξ
  have h1 : ξ' = ξ₀ := hξ'.eq hξ₀
  have h2 : IsGenericPoint (g ξ₀) (closure ({g ξ₀} : Set ↥T.scheme)) := rfl
  rw [h1]
  exact h2.eq hξ

theorem exists_mem_intersectionComponents_pullbackOverField_of_flat (C : Set ↥T.scheme)
    (hC : C ∈ intersectionComponents T.boundary J) (y : ↥Y) (hy : g y ∈ C) :
    ∃ C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
        (J.image (pullbackOverFieldIndex T Y k' q g)),
      y ∈ C' ∧
        ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ := by
  classical
  have hg : GeneralizingMap (fun z : ↥Y => g z) := by
    apply AlgebraicGeometry.Flat.generalizingMap
  have hS : IsClosed (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) :=
    (intersectionIdeal T.boundary J).support.2
  have hC0 : IsIrreducibleComponentOf C (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) :=
    (mem_intersectionComponents_iff T.boundary J C).mp hC
  obtain ⟨C', hC'comp, hyC', _, hgen⟩ :=
    exists_isIrreducibleComponentOf_preimage g hg hS hC0 y hy
  exact ⟨C', (mem_intersectionComponents_pullbackOverField_iff T Y k' q g J C').mpr hC'comp, hyC', hgen⟩


end

private def subschemePreimageOpens_consolidated359 {X : Scheme.{u}} (W : X.IdealSheafData) (A : Set ↥X)
    (h : IsOpen (⇑W.subschemeι ⁻¹' A)) : W.subscheme.Opens :=
  ⟨⇑W.subschemeι ⁻¹' A, h⟩

private theorem quasiCompact_comp_of_noetherianSpace_consolidated359 {Z₁ Z₂ Z₃ : Scheme.{u}} (a : Z₁ ⟶ Z₂)
    (b : Z₂ ⟶ Z₃) [IsOpenImmersion a] [IsClosedImmersion b]
    (h : TopologicalSpace.NoetherianSpace ↥Z₃) :
    QuasiCompact (a ≫ b) :=
  haveI := h
  haveI : TopologicalSpace.NoetherianSpace ↥Z₁ :=
    (((AlgebraicGeometry.Scheme.Hom.isClosedEmbedding b).toIsEmbedding.toIsInducing).comp
      a.isOpenEmbedding.toIsEmbedding.toIsInducing).noetherianSpace
  ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩

private theorem exists_isOpen_comap_ker_of_flat_consolidated359 {X Y : Scheme.{u}} (g : Y ⟶ X)
    [Flat g]
    (W : X.IdealSheafData) (W' : Y.IdealSheafData) (hW : W' = W.comap g)
    (A : Set ↥X) (A' : Set ↥Y) (hA' : A' = ⇑g ⁻¹' A)
    (hA : IsOpen (⇑W.subschemeι ⁻¹' A))
    (hqc : QuasiCompact ((subschemePreimageOpens_consolidated359 W A hA).ι ≫ W.subschemeι)) :
    ∃ h' : IsOpen (⇑W'.subschemeι ⁻¹' A'),
      (Scheme.Hom.ker ((subschemePreimageOpens_consolidated359 W A hA).ι ≫ W.subschemeι)).comap g =
        Scheme.Hom.ker ((subschemePreimageOpens_consolidated359 W' A' h').ι ≫ W'.subschemeι) := by
  subst hW
  subst hA'
  have := hqc
  have hbase : ∀ x : ↥(W.comap g).subscheme,
      W.subschemeι (comapSubschemeHom W g x) = g ((W.comap g).subschemeι x) := by
    intro x
    exact congrArg (fun m : (W.comap g).subscheme ⟶ X => m x) (comapSubschemeHom_comp_subschemeι W g)
  have hset : ⇑(W.comap g).subschemeι ⁻¹' (⇑g ⁻¹' A)
      = ⇑(comapSubschemeHom W g) ⁻¹' (⇑W.subschemeι ⁻¹' A) := by
    ext x
    simp only [Set.mem_preimage]
    rw [hbase x]
  have hopen : IsOpen (⇑(W.comap g).subschemeι ⁻¹' (⇑g ⁻¹' A)) := by
    rw [hset]
    exact hA.preimage (comapSubschemeHom W g).continuous
  refine ⟨hopen, ?_⟩
  have hV : subschemePreimageOpens_consolidated359 (W.comap g) (⇑g ⁻¹' A) hopen
      = comapSubschemeHom W g ⁻¹ᵁ subschemePreimageOpens_consolidated359 W A hA := by
    apply TopologicalSpace.Opens.ext
    exact hset
  rw [hV]
  have hsq2 := (AlgebraicGeometry.isPullback_morphismRestrict (comapSubschemeHom W g)
    (subschemePreimageOpens_consolidated359 W A hA)).paste_vert (isPullback_comapSubschemeHom W g)
  have := quasiCompact_of_isPullback hsq2
  exact (ker_eq_comap_ker_of_isPullback_of_flat hsq2).symm

theorem comap_componentUnionIdeal_of_flat (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) [Flat g]
    (hT' : (T.pullbackOverField Y k' q g).IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme))
    (h𝒞 : 𝒞 ⊆ intersectionComponents T.boundary J)
    (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    ∃ hop' : IsOpen (⇑(intersectionIdeal (T.pullbackOverField Y k' q g).boundary
            (J.image (pullbackOverFieldIndex T Y k' q g))).subschemeι ⁻¹'
          ⋃₀ {C' : Set ↥Y | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
              (J.image (pullbackOverFieldIndex T Y k' q g)) ∧
            ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C}),
      (componentUnionIdeal T.boundary J 𝒞 hop).comap g =
        componentUnionIdeal (T.pullbackOverField Y k' q g).boundary
          (J.image (pullbackOverFieldIndex T Y k' q g))
          {C' : Set ↥Y | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
              (J.image (pullbackOverFieldIndex T Y k' q g)) ∧
            ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C} hop' := by
  classical
  have := hT.isNoetherian
  have hns : TopologicalSpace.NoetherianSpace ↥T.scheme := inferInstance
  have hSclosed : IsClosed (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) :=
    (intersectionIdeal T.boundary J).support.2
  have hSclosed' : IsClosed (⇑g ⁻¹' (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme)) :=
    hSclosed.preimage g.continuous
  have hU : (⋃₀ {C' : Set ↥Y | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
        (J.image (pullbackOverFieldIndex T Y k' q g)) ∧ ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C})
      = ⇑g ⁻¹' ⋃₀ 𝒞 := by
    ext y
    simp only [Set.mem_sUnion, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨C', ⟨-, C, hC𝒞, hmaps⟩, hyC'⟩
      exact ⟨C, hC𝒞, hmaps hyC'⟩
    · rintro ⟨C, hC𝒞, hyC⟩
      obtain ⟨C', hC'mem, hyC', hgen⟩ :=
        exists_mem_intersectionComponents_pullbackOverField_of_flat T hT Y k' q g hT' J C (h𝒞 hC𝒞) y hyC
      obtain ⟨C₀, hC₀mem, hmaps0, hgen0⟩ :=
        exists_intersectionComponents_mapsTo_of_flat T hT Y k' q g hT' J C' hC'mem
      obtain ⟨ξ', hξ'⟩ := IsIrreducibleComponentOf.exists_isGenericPoint
        ((mem_intersectionComponents_pullbackOverField_iff T Y k' q g J C').mp hC'mem) hSclosed'
      obtain ⟨ξ, hξ⟩ := IsIrreducibleComponentOf.exists_isGenericPoint
        ((mem_intersectionComponents_iff T.boundary J C).mp (h𝒞 hC𝒞)) hSclosed
      obtain ⟨ξ₀, hξ₀⟩ := IsIrreducibleComponentOf.exists_isGenericPoint
        ((mem_intersectionComponents_iff T.boundary J C₀).mp hC₀mem) hSclosed
      have h1 : g ξ' = ξ := hgen ξ' ξ hξ' hξ
      have h2 : g ξ' = ξ₀ := hgen0 ξ' ξ₀ hξ' hξ₀
      have hξe : closure ({ξ} : Set ↥T.scheme) = C := hξ
      have hξ0e : closure ({ξ₀} : Set ↥T.scheme) = C₀ := hξ₀
      have h3 : C₀ = C := by rw [← hξ0e, ← hξe, ← h1, ← h2]
      refine ⟨C', ⟨hC'mem, C, hC𝒞, ?_⟩, hyC'⟩
      rw [← h3]
      exact hmaps0
  have hqc := quasiCompact_comp_of_noetherianSpace_consolidated359
    (subschemePreimageOpens_consolidated359 (intersectionIdeal T.boundary J) (⋃₀ 𝒞) hop).ι
    (intersectionIdeal T.boundary J).subschemeι hns
  obtain ⟨h', hker⟩ := exists_isOpen_comap_ker_of_flat_consolidated359 g (intersectionIdeal T.boundary J)
    (intersectionIdeal (T.pullbackOverField Y k' q g).boundary (J.image (pullbackOverFieldIndex T Y k' q g)))
    (intersectionIdeal_pullbackOverField T Y k' q g J) (⋃₀ 𝒞)
    (⋃₀ {C' : Set ↥Y | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
        (J.image (pullbackOverFieldIndex T Y k' q g)) ∧ ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C})
    hU hop hqc
  exact ⟨h', hker⟩


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenter
section


section

section
variable {Y : Scheme.{u}} {L : List Y.IdealSheafData} {J : Finset (Fin L.length)} {C : Set ↥Y} (hC : C ∈ intersectionComponents L J)
include hC

theorem isClosed_intersectionComponents_of_mem : IsClosed C := by
  have h : IsIrreducibleComponentOf C (↑(intersectionIdeal L J).support : Set ↥Y) :=
    (mem_intersectionComponents_iff L J C).1 hC
  have hclosed : IsClosed (↑(intersectionIdeal L J).support : Set ↥Y) :=
    (intersectionIdeal L J).support.2
  have hcl : closure C = C :=
    h.2.2 (closure C) h.1.closure subset_closure (closure_minimal h.2.1 hclosed)
  exact isClosed_of_closure_subset hcl.subset

theorem isIrreducible_of_mem_intersectionComponents : IsIrreducible C :=
  ((mem_intersectionComponents_iff L J C).1 hC).1

theorem isGenericPoint_genericPoint_of_mem_intersectionComponents :
    IsGenericPoint (isIrreducible_of_mem_intersectionComponents hC).genericPoint C := by
  have hcl : closure C = C := (isClosed_intersectionComponents_of_mem hC).closure_eq
  have h : closure {(isIrreducible_of_mem_intersectionComponents hC).genericPoint} = closure C := by
    simp
  exact h.trans hcl


end

section
variable {Y : Scheme.{u}} (I : Y.IdealSheafData)

theorem orderAlong_eq_orderAt_of_mem_intersectionComponents {L : List Y.IdealSheafData} {J : Finset (Fin L.length)} {C : Set ↥Y}
    (hC : C ∈ intersectionComponents L J) :
    orderAlong I C = orderAt I (isIrreducible_of_mem_intersectionComponents hC).genericPoint := by
  unfold orderAlong
  exact dif_pos (isIrreducible_of_mem_intersectionComponents hC)

theorem orderAlong_eq_orderAt_genericPoint {C : Set ↥Y} (h : IsIrreducible C) : orderAlong I C = orderAt I h.genericPoint := by
  unfold orderAlong
  exact dif_pos h

theorem orderAlong_eq_of_closure_eq {S : Set ↥Y}
    (hS : IsIrreducible S) {C : Set ↥Y} (hC : IsIrreducible C)
    (hcl : closure S = closure C) : orderAlong I S = orderAlong I C := by
  rw [orderAlong_eq_orderAt_genericPoint I hS, orderAlong_eq_orderAt_genericPoint I hC]
  have e1 : closure ({hS.genericPoint} : Set ↥Y) = closure S := by simp
  have e2 : closure ({hC.genericPoint} : Set ↥Y) = closure C := by simp
  have h1 : closure ({hS.genericPoint} : Set ↥Y) = closure ({hC.genericPoint} : Set ↥Y) := by
    rw [e1, e2, hcl]
  rw [(inseparable_iff_closure_eq.mpr h1).eq]


end

section
variable {Y : Scheme.{u}}

private theorem mem_support_bot_consolidated361 (x : ↥Y) :
    x ∈ (⊥ : Y.IdealSheafData).support := by
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_bot]
  exact bot_le

private theorem mem_support_sup_of_mem_consolidated361 {I J : Y.IdealSheafData} {x : ↥Y}
    (hI : x ∈ I.support) (hJ : x ∈ J.support) : x ∈ (I ⊔ J).support := by
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal] at hI hJ ⊢
  rw [stalkIdeal_sup]
  exact sup_le hI hJ

private theorem mem_support_finsetSup_of_forall_mem_consolidated361 (L : List Y.IdealSheafData)
    (x : ↥Y) (S : Finset (Fin L.length)) (hx : ∀ j ∈ S, x ∈ (L.get j).support) :
    x ∈ (S.sup fun j => L.get j).support := by
  revert hx
  refine Finset.induction_on S ?_ ?_
  · intro _
    rw [Finset.sup_empty]
    exact mem_support_bot_consolidated361 x
  · intro a s ha ih hS
    rw [Finset.sup_insert]
    exact mem_support_sup_of_mem_consolidated361 (hS a (Finset.mem_insert_self a s))
      (ih fun j hj => hS j (Finset.mem_insert_of_mem hj))

theorem mem_support_intersectionIdeal (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) (x : ↥Y) (hx : ∀ j ∈ J, x ∈ (L.get j).support) :
    x ∈ (intersectionIdeal L J).support := by
  have he : intersectionIdeal L J = J.sup fun j => L.get j :=
    (intersectionIdeal_eq_iSup L J).trans (Finset.sup_eq_iSup J fun j => L.get j).symm
  rw [he]
  exact mem_support_finsetSup_of_forall_mem_consolidated361 L x J hx


end

section
variable (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T) {J : Finset (Fin T.boundary.length)} {C : Set ↥T.scheme} (hC : C ∈ intersectionComponents T.boundary J) (i : Fin T.boundary.length)
include hGeom hT hC

theorem subset_support_iff_mem_of_mem_intersectionComponents :
    C ⊆ (↑(T.boundary.get i).support : Set ↥T.scheme) ↔ i ∈ J :=
  hGeom.components_subset_divisor_iff T hT.valid J C hC i

theorem genericPoint_mem_support_iff_mem :
    (isIrreducible_of_mem_intersectionComponents hC).genericPoint ∈ (T.boundary.get i).support ↔ i ∈ J := by
  have hgen : closure {(isIrreducible_of_mem_intersectionComponents hC).genericPoint} = C :=
    isGenericPoint_genericPoint_of_mem_intersectionComponents hC
  have hsub := subset_support_iff_mem_of_mem_intersectionComponents hGeom hT hC i
  have hcl : IsClosed (↑(T.boundary.get i).support : Set ↥T.scheme) :=
    (T.boundary.get i).support.2
  constructor
  · intro hx
    refine hsub.1 ?_
    have hx' : ({(isIrreducible_of_mem_intersectionComponents hC).genericPoint} : Set ↥T.scheme) ⊆
        (↑(T.boundary.get i).support : Set ↥T.scheme) := Set.singleton_subset_iff.2 hx
    have hsubc := hcl.closure_subset_iff.2 hx'
    rwa [hgen] at hsubc
  · intro hi
    have hmem : (isIrreducible_of_mem_intersectionComponents hC).genericPoint ∈
        closure ({(isIrreducible_of_mem_intersectionComponents hC).genericPoint} : Set ↥T.scheme) :=
      subset_closure rfl
    rw [hgen] at hmem
    exact hsub.2 hi hmem


end

theorem subset_orderAtLeastLocus_of_le_orderAlong {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    {J : Finset (Fin T.boundary.length)} {C : Set ↥T.scheme}
    (hC : C ∈ intersectionComponents T.boundary J) (c : ℕ) (hc : (c : ℕ∞) ≤ orderAlong T.ideal C) :
    C ⊆ orderAtLeastLocus T.ideal c := by
  have : CharZero T.base := hT.charZero
  have : Smooth T.structMap := hT.smooth
  have hmem : (isIrreducible_of_mem_intersectionComponents hC).genericPoint ∈ orderAtLeastLocus T.ideal c := by
    rw [mem_orderAtLeastLocus_iff, ← orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC]
    exact hc
  have hclosed : IsClosed (orderAtLeastLocus T.ideal c) :=
    isClosed_orderAtLeastLocus T.base T.structMap T.ideal c
  have h2 : closure ({(isIrreducible_of_mem_intersectionComponents hC).genericPoint} : Set ↥T.scheme) = C :=
    isGenericPoint_genericPoint_of_mem_intersectionComponents hC
  have hsub :
      closure ({(isIrreducible_of_mem_intersectionComponents hC).genericPoint} : Set ↥T.scheme) ⊆
        orderAtLeastLocus T.ideal c :=
    closure_minimal (Set.singleton_subset_iff.2 hmem) hclosed
  rw [← h2]
  exact hsub

def supportIndices {Y : Scheme.{u}} (L : List Y.IdealSheafData) (x : ↥Y) :
    Finset (Fin L.length) :=
  @Finset.filter _ (fun j => x ∈ (L.get j).support) (Classical.decPred _) Finset.univ

theorem mem_supportIndices {Y : Scheme.{u}} (L : List Y.IdealSheafData) (x : ↥Y)
    (j : Fin L.length) : j ∈ supportIndices L x ↔ x ∈ (L.get j).support := by
  simp [supportIndices]

theorem orderAt_foldr_mul (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (x : ↥X) (L : List X.IdealSheafData) :
    orderAt (L.foldr (· * ·) ⊤) x = (L.map (fun I => orderAt I x)).sum := by
  induction L with
  | nil => simp [orderAt_top]
  | cons I L ih => simp [orderAt_mul k p, ih]

theorem orderAt_eq_sum_indicator_support (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) (U : T.scheme.Opens)
    (a : Fin T.boundary.length → ℕ)
    (hmon : T.ideal.comap U.ι =
      (List.ofFn fun i : Fin T.boundary.length =>
        (T.boundary.get i).comap U.ι ^ a i).foldr (· * ·) ⊤)
    (x : ↥T.scheme) (hx : x ∈ U) :
    orderAt T.ideal x =
      ∑ j : Fin T.boundary.length,
        (a j : ℕ∞) *
          (↑(T.boundary.get j).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) x := by
  classical
  have : CharZero T.base := hT.valid.charZero
  have : Smooth T.structMap := hT.valid.smooth
  have : Smooth U.ι := inferInstance
  have : Smooth (U.ι ≫ T.structMap) := inferInstance
  have h1 : orderAt (T.ideal.comap U.ι) ⟨x, hx⟩ = orderAt T.ideal x :=
    orderAt_comap T.base T.structMap U.ι T.ideal ⟨x, hx⟩
  have h2 : orderAt (T.ideal.comap U.ι) ⟨x, hx⟩
      = ∑ i : Fin T.boundary.length,
          orderAt ((T.boundary.get i).comap U.ι ^ a i) ⟨x, hx⟩ := by
    rw [hmon, orderAt_foldr_mul T.base (U.ι ≫ T.structMap) ⟨x, hx⟩]
    simp [List.map_ofFn, List.sum_ofFn]
  have h3 : ∀ i : Fin T.boundary.length,
      orderAt ((T.boundary.get i).comap U.ι ^ a i) ⟨x, hx⟩
        = (a i : ℕ∞) *
            (↑(T.boundary.get i).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) x := by
    intro i
    have hmemlist : T.boundary.get i ∈ T.boundary := by simp
    have hcomap : orderAt ((T.boundary.get i).comap U.ι) ⟨x, hx⟩
        = orderAt (T.boundary.get i) x :=
      orderAt_comap T.base T.structMap U.ι (T.boundary.get i) ⟨x, hx⟩
    rw [orderAt_pow T.base (U.ι ≫ T.structMap) ((T.boundary.get i).comap U.ι) (a i) ⟨x, hx⟩,
      hcomap]
    by_cases hmem : x ∈ (T.boundary.get i).support
    · have hset : x ∈ (↑(T.boundary.get i).support : Set ↥T.scheme) := hmem
      rw [hGeom.orderAt_boundary_eq_one T hT.valid (T.boundary.get i) hmemlist x hmem,
        Set.indicator_of_mem hset]
    · have hset : x ∉ (↑(T.boundary.get i).support : Set ↥T.scheme) := hmem
      rw [(orderAt_eq_zero_iff_not_mem_support (T.boundary.get i) x).2 hmem,
        Set.indicator_apply, if_neg hset]
  calc orderAt T.ideal x = orderAt (T.ideal.comap U.ι) ⟨x, hx⟩ := h1.symm
    _ = ∑ i : Fin T.boundary.length,
          orderAt ((T.boundary.get i).comap U.ι ^ a i) ⟨x, hx⟩ := h2
    _ = ∑ j : Fin T.boundary.length,
          (a j : ℕ∞) *
            (↑(T.boundary.get j).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) x :=
        Finset.sum_congr rfl fun i _ => h3 i

section
variable {α : Type u} (s : Set α) (x : α)

private theorem indicator_one_eq_zero_of_notMem_consolidated361 (h : x ∉ s) :
    s.indicator (fun _ => (1 : ℕ∞)) x = 0 := by
  simp [Set.indicator, h]

private theorem indicator_one_eq_one_of_mem_consolidated361 (h : x ∈ s) :
    s.indicator (fun _ => (1 : ℕ∞)) x = 1 := by
  simp [Set.indicator, h]


end

section
variable (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
include hGeom hT

theorem orderAlong_eq_sum_of_monomial {J : Finset (Fin T.boundary.length)}
    {C : Set ↥T.scheme} (hC : C ∈ intersectionComponents T.boundary J) {x : ↥T.scheme} (hxC : x ∈ C)
    (U : T.scheme.Opens) (hxU : x ∈ U) (a : Fin T.boundary.length → ℕ)
    (hmon : T.ideal.comap U.ι =
      (List.ofFn fun i : Fin T.boundary.length =>
        (T.boundary.get i).comap U.ι ^ a i).foldr (· * ·) ⊤) :
    orderAlong T.ideal C = ((∑ j ∈ J, a j : ℕ) : ℕ∞) := by
  have hgen : closure ({(isIrreducible_of_mem_intersectionComponents hC).genericPoint} : Set ↥T.scheme) = C :=
    isGenericPoint_genericPoint_of_mem_intersectionComponents hC
  have hξU0 : (isIrreducible_of_mem_intersectionComponents hC).genericPoint ∈ U := by
    by_contra hnot
    have h2 : C ⊆ (↑U : Set ↥T.scheme)ᶜ := by
      rw [← hgen]
      exact closure_minimal (Set.singleton_subset_iff.2 hnot)
        (TopologicalSpace.Opens.isOpen U).isClosed_compl
    exact h2 hxC hxU
  obtain ⟨ξ, hord, hξU, hξs⟩ :
      ∃ ξ : ↥T.scheme, orderAlong T.ideal C = orderAt T.ideal ξ ∧ ξ ∈ U ∧
        ∀ j : Fin T.boundary.length, (ξ ∈ (T.boundary.get j).support ↔ j ∈ J) :=
    ⟨(isIrreducible_of_mem_intersectionComponents hC).genericPoint,
      orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC, hξU0,
      fun j => genericPoint_mem_support_iff_mem hGeom hT hC j⟩
  rw [hord, orderAt_eq_sum_indicator_support hGeom hT U a hmon ξ hξU]
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin T.boundary.length)), j ∉ J →
      (a j : ℕ∞) *
        (↑(T.boundary.get j).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) ξ = 0 := by
    intro j _ hj
    have h1 : ξ ∉ (↑(T.boundary.get j).support : Set ↥T.scheme) := fun hm => hj ((hξs j).1 hm)
    rw [indicator_one_eq_zero_of_notMem_consolidated361 _ ξ h1, mul_zero]
  have hone : ∀ j ∈ J,
      (a j : ℕ∞) *
        (↑(T.boundary.get j).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) ξ
        = (a j : ℕ∞) := by
    intro j hj
    have h1 : ξ ∈ (↑(T.boundary.get j).support : Set ↥T.scheme) := (hξs j).2 hj
    rw [indicator_one_eq_one_of_mem_consolidated361 _ ξ h1, mul_one]
  rw [← Finset.sum_subset (Finset.subset_univ J) hzero, Finset.sum_congr rfl hone]
  exact (Nat.cast_sum J a).symm

theorem orderAt_eq_sum_supportIndices (x : ↥T.scheme) (U : T.scheme.Opens)
    (hxU : x ∈ U) (a : Fin T.boundary.length → ℕ)
    (hmon : T.ideal.comap U.ι =
      (List.ofFn fun i : Fin T.boundary.length =>
        (T.boundary.get i).comap U.ι ^ a i).foldr (· * ·) ⊤) :
    orderAt T.ideal x = ((∑ j ∈ supportIndices T.boundary x, a j : ℕ) : ℕ∞) := by
  classical
  have h2 : ∀ j ∈ (Finset.univ : Finset (Fin T.boundary.length)),
      j ∉ supportIndices T.boundary x →
      (a j : ℕ∞) *
          (↑(T.boundary.get j).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) x = 0 := by
    intro j _ hj
    have hx : x ∉ (↑(T.boundary.get j).support : Set ↥T.scheme) := by
      intro hmem
      exact hj ((mem_supportIndices T.boundary x j).2 hmem)
    rw [Set.indicator_apply, if_neg hx, mul_zero]
  have h1 : ∀ j ∈ supportIndices T.boundary x,
      (a j : ℕ∞) *
          (↑(T.boundary.get j).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) x
        = (a j : ℕ∞) := by
    intro j hj
    have hx : x ∈ (↑(T.boundary.get j).support : Set ↥T.scheme) :=
      (mem_supportIndices T.boundary x j).1 hj
    rw [Set.indicator_apply, if_pos hx]
    exact mul_one _
  rw [orderAt_eq_sum_indicator_support hGeom hT U a hmon x hxU, Nat.cast_sum,
    ← Finset.sum_subset (Finset.subset_univ (supportIndices T.boundary x)) h2]
  exact Finset.sum_congr rfl h1


end

private theorem mem_intersectionComponents_of_isCandidateComponent_consolidated361 {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (m : ℕ) (L : List Y.IdealSheafData) (r : ℕ) (J : Finset (Fin L.length)) (C : Set ↥Y)
    (h : IsCandidateComponent I m L r J C) : C ∈ intersectionComponents L J := by
  unfold IsCandidateComponent at h
  simp only [mem_intersectionComponents_iff] at h ⊢
  tauto

theorem finite_setOf_isCandidateComponent (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) :
    {p : Finset (Fin T.boundary.length) × Set ↥T.scheme |
      ∃ r : ℕ, IsCandidateComponent T.ideal T.mult T.boundary r p.1 p.2}.Finite := by
  classical
  have hfin : (⋃ J : Finset (Fin T.boundary.length),
      (fun C : Set ↥T.scheme => ((J, C) : Finset (Fin T.boundary.length) × Set ↥T.scheme)) ''
        intersectionComponents T.boundary J).Finite :=
    Set.finite_iUnion fun J =>
      Set.Finite.image
        (fun C : Set ↥T.scheme => ((J, C) : Finset (Fin T.boundary.length) × Set ↥T.scheme))
        (hGeom.components_finite T hT.valid J)
  refine hfin.subset ?_
  rintro ⟨J, C⟩ ⟨r, hcand⟩
  have hmem : C ∈ intersectionComponents T.boundary J :=
    mem_intersectionComponents_of_isCandidateComponent_consolidated361 T.ideal T.mult T.boundary r J C hcand
  exact Set.mem_iUnion.2 ⟨J, Set.mem_image_of_mem _ hmem⟩

private theorem lt_top_of_le_natCast_consolidated361 {a : ℕ∞} {B : ℕ} (h : a ≤ (B : ℕ∞)) : a < ⊤ :=
  h.trans_lt (ENat.natCast_lt_top B)

theorem orderAlong_lt_top_of_isCandidateComponent (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T) {r : ℕ}
    {J : Finset (Fin T.boundary.length)} {C : Set ↥T.scheme}
    (hcand : IsCandidateComponent T.ideal T.mult T.boundary r J C) :
    orderAlong T.ideal C < ⊤ := by
  have hC : C ∈ intersectionComponents T.boundary J := by
    unfold IsCandidateComponent at hcand
    tauto
  obtain ⟨B, hB⟩ :=
    hGeom.orderAt_bounded T hT.valid T.ideal hT.valid.nonzeroOnComponents
  rw [orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC]
  exact lt_top_of_le_natCast_consolidated361 (hB _)

section
variable {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData)

private theorem minIndexCard_eq_sInf_consolidated361 :
    minIndexCard I m L =
      sInf {r : ℕ | 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
        IsCandidateComponent I m L r J C} := rfl

theorem minIndexCard_spec (hex : ∃ r : ℕ, 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
      IsCandidateComponent I m L r J C) :
    1 ≤ minIndexCard I m L ∧
      (∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
        IsCandidateComponent I m L (minIndexCard I m L) J C) ∧
      (∀ r : ℕ, 1 ≤ r → ∀ (J : Finset (Fin L.length)) (C : Set ↥Y),
        IsCandidateComponent I m L r J C → minIndexCard I m L ≤ r) := by
  classical
  have hne : {r : ℕ | 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
      IsCandidateComponent I m L r J C}.Nonempty := hex
  have hmem : minIndexCard I m L ∈ {r : ℕ | 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
      IsCandidateComponent I m L r J C} := by
    rw [minIndexCard_eq_sInf_consolidated361 I m L]
    exact Nat.sInf_mem hne
  obtain ⟨h1, h2⟩ := hmem
  refine ⟨h1, h2, ?_⟩
  intro r hr J C hcand
  rw [minIndexCard_eq_sInf_consolidated361 I m L]
  exact Nat.sInf_le ⟨hr, J, C, hcand⟩

theorem minIndexCard_eq_zero_iff :
    minIndexCard I m L = 0 ↔
      ¬ ∃ r : ℕ, 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
        IsCandidateComponent I m L r J C := by
  rw [minIndexCard_eq_sInf_consolidated361 I m L, Nat.sInf_eq_zero]
  constructor
  · rintro (h0 | hempty) hex
    · obtain ⟨h1, -⟩ := h0
      omega
    · obtain ⟨r, hr⟩ := hex
      have h2 : r ∈ (∅ : Set ℕ) := by
        rw [← hempty]
        exact hr
      exact (Set.mem_empty_iff_false r).mp h2
  · intro hne
    refine Or.inr ?_
    ext r
    constructor
    · intro hr
      exact (hne ⟨r, hr⟩).elim
    · intro hr
      exact ((Set.mem_empty_iff_false r).mp hr).elim

theorem exists_isCandidateComponent_minIndexCard (h : minIndexCard I m L ≠ 0) :
    ∃ (J : Finset (Fin L.length)) (C : Set ↥Y), IsCandidateComponent I m L (minIndexCard I m L) J C := by
  have hex : ∃ r : ℕ, 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
      IsCandidateComponent I m L r J C := by
    by_contra hc
    exact h ((minIndexCard_eq_zero_iff I m L).2 hc)
  exact (minIndexCard_spec I m L hex).2.1

private theorem maxCandidateOrder_eq_iSup_orderAlong_consolidated361 :
    maxCandidateOrder I m L =
      ⨆ J : Finset (Fin L.length), ⨆ C : Set ↥Y,
        ⨆ _ : IsCandidateComponent I m L (minIndexCard I m L) J C, orderAlong I C :=
  rfl


end

section
variable (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T) (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
include hGeom hT h

theorem maxCandidateOrder_spec :
    (∃ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
        IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary) J C ∧
          orderAlong T.ideal C = maxCandidateOrder T.ideal T.mult T.boundary) ∧
      (∀ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
        IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary) J C →
          orderAlong T.ideal C ≤ maxCandidateOrder T.ideal T.mult T.boundary) ∧
      ((T.mult : ℕ∞) ≤ maxCandidateOrder T.ideal T.mult T.boundary) ∧
      maxCandidateOrder T.ideal T.mult T.boundary < ⊤ := by
  classical
  obtain ⟨J₁, C₁, hcand₁⟩ := exists_isCandidateComponent_minIndexCard T.ideal T.mult T.boundary h
  have hsub : {p : Finset (Fin T.boundary.length) × Set ↥T.scheme |
        IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary) p.1 p.2} ⊆
      {p : Finset (Fin T.boundary.length) × Set ↥T.scheme |
        ∃ r : ℕ, IsCandidateComponent T.ideal T.mult T.boundary r p.1 p.2} := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp ⊢
    exact ⟨minIndexCard T.ideal T.mult T.boundary, hp⟩
  have hfin : {p : Finset (Fin T.boundary.length) × Set ↥T.scheme |
      IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary)
        p.1 p.2}.Finite :=
    (finite_setOf_isCandidateComponent hGeom hT).subset hsub
  have hne : {p : Finset (Fin T.boundary.length) × Set ↥T.scheme |
      IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary)
        p.1 p.2}.Nonempty := ⟨(J₁, C₁), hcand₁⟩
  obtain ⟨p₀, hmem₀, hmax₀⟩ :=
    Set.exists_max_image _
      (fun q : Finset (Fin T.boundary.length) × Set ↥T.scheme => orderAlong T.ideal q.2) hfin hne
  have hcand₀ : IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary)
      p₀.1 p₀.2 := hmem₀
  have hkey : maxCandidateOrder T.ideal T.mult T.boundary = orderAlong T.ideal p₀.2 := by
    rw [maxCandidateOrder_eq_iSup_orderAlong_consolidated361]
    refine le_antisymm ?_ ?_
    · apply iSup_le
      intro J
      apply iSup_le
      intro C
      apply iSup_le
      intro hc
      exact hmax₀ (J, C) hc
    · exact le_iSup_of_le p₀.1 (le_iSup_of_le p₀.2 (le_iSup_of_le hcand₀ le_rfl))
  refine ⟨⟨p₀.1, p₀.2, hcand₀, hkey.symm⟩, ?_, ?_, ?_⟩
  · intro J C hc
    rw [hkey]
    exact hmax₀ (J, C) hc
  · rw [hkey]
    have hcomp := hcand₀
    unfold IsCandidateComponent at hcomp
    exact hcomp.2.2
  · rw [hkey]
    exact orderAlong_lt_top_of_isCandidateComponent hGeom hT hcand₀

theorem exists_isMaxOrderIndexSet :
    ∃ J : Finset (Fin T.boundary.length), IsMaxOrderIndexSet T.ideal T.mult T.boundary J := by
  obtain ⟨J, C, hcand, hord⟩ := (maxCandidateOrder_spec hGeom hT h).1
  refine ⟨J, ?_⟩
  unfold IsMaxOrderIndexSet
  exact ⟨C, hcand, hord⟩


end

section
variable {Y : Scheme.{u}}

private theorem maxBinaryCode_eq_sSup_consolidated361 (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) :
    maxBinaryCode I m L =
      sSup {c : ℕ | ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J ∧ binaryEncode J = c} := rfl

private theorem card_eq_minIndexCard_of_isMaxOrderIndexSet_consolidated361 {I : Y.IdealSheafData}
    {m : ℕ} {L : List Y.IdealSheafData} {J : Finset (Fin L.length)} (hJ : IsMaxOrderIndexSet I m L J) :
    J.card = minIndexCard I m L := by
  unfold IsMaxOrderIndexSet at hJ
  obtain ⟨C, hcand, -⟩ := hJ
  unfold IsCandidateComponent at hcand
  exact hcand.1


end

section
variable (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T) (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
include hGeom hT h

theorem lexMaxIndices_spec :
    IsMaxOrderIndexSet T.ideal T.mult T.boundary (lexMaxIndices T.ideal T.mult T.boundary) ∧
      ∀ J : Finset (Fin T.boundary.length), IsMaxOrderIndexSet T.ideal T.mult T.boundary J →
        ¬ List.Lex (· < ·) (MonomialCenter.sortedIndices J)
            (MonomialCenter.sortedIndices (lexMaxIndices T.ideal T.mult T.boundary)) := by
  classical
  obtain ⟨J0, hJ0⟩ := exists_isMaxOrderIndexSet hGeom hT h
  have hbdd : BddAbove {c : ℕ | ∃ J : Finset (Fin T.boundary.length),
      IsMaxOrderIndexSet T.ideal T.mult T.boundary J ∧ binaryEncode J = c} := by
    refine Set.Finite.bddAbove (Set.Finite.subset
      (Set.finite_range (fun J : Finset (Fin T.boundary.length) => binaryEncode J)) ?_)
    rintro c ⟨J, -, rfl⟩
    exact Set.mem_range_self J
  have hne : {c : ℕ | ∃ J : Finset (Fin T.boundary.length),
      IsMaxOrderIndexSet T.ideal T.mult T.boundary J ∧ binaryEncode J = c}.Nonempty :=
    ⟨binaryEncode J0, ⟨J0, hJ0, rfl⟩⟩
  have hex : ∃ J : Finset (Fin T.boundary.length),
      IsMaxOrderIndexSet T.ideal T.mult T.boundary J ∧
        binaryEncode J = maxBinaryCode T.ideal T.mult T.boundary := by
    have hmem : maxBinaryCode T.ideal T.mult T.boundary ∈
        {c : ℕ | ∃ J : Finset (Fin T.boundary.length),
          IsMaxOrderIndexSet T.ideal T.mult T.boundary J ∧ binaryEncode J = c} := by
      rw [maxBinaryCode_eq_sSup_consolidated361]
      exact Nat.sSup_mem hne hbdd
    exact hmem
  have hchosen : IsMaxOrderIndexSet T.ideal T.mult T.boundary (lexMaxIndices T.ideal T.mult T.boundary) ∧
      binaryEncode (lexMaxIndices T.ideal T.mult T.boundary)
        = maxBinaryCode T.ideal T.mult T.boundary := by
    unfold lexMaxIndices
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨hchosen.1, ?_⟩
  intro J hJ hlex
  have hcard : J.card = (lexMaxIndices T.ideal T.mult T.boundary).card := by
    rw [card_eq_minIndexCard_of_isMaxOrderIndexSet_consolidated361 hJ, card_eq_minIndexCard_of_isMaxOrderIndexSet_consolidated361 hchosen.1]
  have hlt : binaryEncode (lexMaxIndices T.ideal T.mult T.boundary) < binaryEncode J :=
    (MonomialCenter.binaryEncode_lt_iff_lex_of_card_eq J (lexMaxIndices T.ideal T.mult T.boundary) hcard).2
      hlex
  have hle : binaryEncode J ≤ binaryEncode (lexMaxIndices T.ideal T.mult T.boundary) := by
    rw [hchosen.2, maxBinaryCode_eq_sSup_consolidated361]
    exact le_csSup hbdd ⟨J, hJ, rfl⟩
  exact absurd hlt (not_lt.2 hle)

theorem card_lexMaxIndices :
    (lexMaxIndices T.ideal T.mult T.boundary).card = minIndexCard T.ideal T.mult T.boundary :=
  card_eq_minIndexCard_of_isMaxOrderIndexSet_consolidated361 (lexMaxIndices_spec hGeom hT h).1


end

theorem monomialCenter_eq_top_of_minIndexCard_eq_zero {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) (h : minIndexCard I m L = 0) : monomialCenter I m L = ⊤ := by
  unfold monomialCenter
  simp [h]

def centerComponents {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) : Set (Set ↥Y) :=
  {C : Set ↥Y |
    IsCandidateComponent I m L (minIndexCard I m L) (lexMaxIndices I m L) C ∧
      orderAlong I C = maxCandidateOrder I m L}

section
variable {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData)

theorem mem_centerComponents_iff (C : Set ↥Y) :
    C ∈ centerComponents I m L ↔
      IsCandidateComponent I m L (minIndexCard I m L) (lexMaxIndices I m L) C ∧
        orderAlong I C = maxCandidateOrder I m L :=
  Iff.rfl

theorem centerComponents_subset_intersectionComponents :
    centerComponents I m L ⊆ intersectionComponents L (lexMaxIndices I m L) := by
  intro C hC
  exact mem_intersectionComponents_of_isCandidateComponent_consolidated361 I m L (minIndexCard I m L) (lexMaxIndices I m L) C
    ((mem_centerComponents_iff I m L C).1 hC).1


end

theorem isOpen_preimage_sUnion_centerComponents (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T) :
    IsOpen (⇑(intersectionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)).subschemeι ⁻¹'
      ⋃₀ centerComponents T.ideal T.mult T.boundary) :=
  hGeom.sUnion_isOpen T hT.valid _ _
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary)

theorem monomialCenterSet_eq_sUnion_centerComponents {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) :
    monomialCenterSet I m L = ⋃₀ centerComponents I m L := by
  ext x
  simp [monomialCenterSet, centerComponents, Set.mem_sUnion]

theorem isOpen_preimage_monomialCenterSet (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) :
    IsOpen (⇑(intersectionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)).subschemeι ⁻¹'
      monomialCenterSet T.ideal T.mult T.boundary) := by
  rw [monomialCenterSet_eq_sUnion_centerComponents]
  exact isOpen_preimage_sUnion_centerComponents hGeom hT

private theorem openSublocusIdeal_eq_componentUnionIdeal_consolidated361 {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) (𝒞 : Set (Set ↥Y))
    (S : Set ↥(intersectionIdeal L J).subscheme)
    (hEq : S = ⇑(intersectionIdeal L J).subschemeι ⁻¹' ⋃₀ 𝒞)
    (hS : IsOpen S) (hop : IsOpen (⇑(intersectionIdeal L J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    openSublocusIdeal (intersectionIdeal L J).subschemeι S hS = componentUnionIdeal L J 𝒞 hop := by
  subst hEq
  rfl

section
variable (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T) (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
include hGeom hT h

theorem monomialCenter_eq_componentUnionIdeal :
    monomialCenter T.ideal T.mult T.boundary =
      componentUnionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)
        (centerComponents T.ideal T.mult T.boundary)
        (isOpen_preimage_sUnion_centerComponents hGeom hT) := by
  have hc : minIndexCard T.ideal T.mult T.boundary ≠ 0 ∧
      IsOpen (⇑(intersectionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)).subschemeι ⁻¹'
        monomialCenterSet T.ideal T.mult T.boundary) :=
    ⟨h, isOpen_preimage_monomialCenterSet hGeom hT⟩
  unfold monomialCenter
  rw [dif_pos hc]
  exact openSublocusIdeal_eq_componentUnionIdeal_consolidated361 T.boundary (lexMaxIndices T.ideal T.mult T.boundary)
    (centerComponents T.ideal T.mult T.boundary) _
    (by rw [monomialCenterSet_eq_sUnion_centerComponents]) _ _

theorem support_monomialCenter :
    (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) =
      monomialCenterSet T.ideal T.mult T.boundary := by
  rw [monomialCenterSet_eq_sUnion_centerComponents T.ideal T.mult T.boundary,
    monomialCenter_eq_componentUnionIdeal hGeom hT h]
  exact hGeom.center_support T hT.valid _ _
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary) _

theorem monomialCenterSet_nonempty :
    (monomialCenterSet T.ideal T.mult T.boundary).Nonempty := by
  have hbest := (lexMaxIndices_spec hGeom hT h).1
  unfold IsMaxOrderIndexSet at hbest
  obtain ⟨C, hcand, hord⟩ := hbest
  have hmem : C ∈ centerComponents T.ideal T.mult T.boundary :=
    (mem_centerComponents_iff T.ideal T.mult T.boundary C).2 ⟨hcand, hord⟩
  have hC : C ∈ intersectionComponents T.boundary (lexMaxIndices T.ideal T.mult T.boundary) :=
    mem_intersectionComponents_of_isCandidateComponent_consolidated361 T.ideal T.mult T.boundary
      (minIndexCard T.ideal T.mult T.boundary) (lexMaxIndices T.ideal T.mult T.boundary) C hcand
  obtain ⟨x, hx⟩ := (isIrreducible_of_mem_intersectionComponents hC).1
  refine ⟨x, ?_⟩
  rw [monomialCenterSet_eq_sUnion_centerComponents T.ideal T.mult T.boundary]
  exact Set.mem_sUnion.2 ⟨C, hmem, hx⟩

theorem monomialCenter_ne_top :
    monomialCenter T.ideal T.mult T.boundary ≠ ⊤ := by
  intro htop
  obtain ⟨x, hx⟩ := monomialCenterSet_nonempty hGeom hT h
  have hsupp := support_monomialCenter hGeom hT h
  have hxmem : x ∈ (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) := by
    rw [hsupp]
    exact hx
  have hx2 : x ∈ (monomialCenter T.ideal T.mult T.boundary).support := hxmem
  rw [mem_support_iff_stalkIdeal_ne_top, htop, stalkIdeal_top] at hx2
  exact hx2 rfl

theorem smooth_monomialCenter :
    Smooth
      ((monomialCenter T.ideal T.mult T.boundary).subschemeι ≫ T.structMap) := by
  rw [monomialCenter_eq_componentUnionIdeal hGeom hT h]
  exact hGeom.center_smooth T hT.valid _ _
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary) _

theorem hasStrictNormalCrossingsWith_monomialCenter :
    HasStrictNormalCrossingsWith T.structMap (monomialCenter T.ideal T.mult T.boundary) T.boundary := by
  rw [monomialCenter_eq_componentUnionIdeal hGeom hT h]
  exact hGeom.center_snc T hT.valid _ _
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary) _

theorem support_monomialCenter_subset_orderAtLeastLocus :
    (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) ⊆
      orderAtLeastLocus T.ideal T.mult := by
  rw [support_monomialCenter hGeom hT h,
    monomialCenterSet_eq_sUnion_centerComponents T.ideal T.mult T.boundary]
  rintro x ⟨C, hC, hxC⟩
  have hcand : IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary)
      (lexMaxIndices T.ideal T.mult T.boundary) C :=
    ((mem_centerComponents_iff T.ideal T.mult T.boundary C).1 hC).1
  have hmem : C ∈ intersectionComponents T.boundary (lexMaxIndices T.ideal T.mult T.boundary) :=
    mem_intersectionComponents_of_isCandidateComponent_consolidated361 T.ideal T.mult T.boundary
      (minIndexCard T.ideal T.mult T.boundary) (lexMaxIndices T.ideal T.mult T.boundary) C hcand
  have hord : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    have hcomp := hcand
    unfold IsCandidateComponent at hcomp
    exact hcomp.2.2
  exact subset_orderAtLeastLocus_of_le_orderAlong hT.valid hmem T.mult hord hxC

theorem support_monomialCenter_subset_boundary :
    (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) ⊆
      ⋃ D ∈ T.boundary, (↑D.support : Set ↥T.scheme) := by
  rw [support_monomialCenter hGeom hT h,
    monomialCenterSet_eq_sUnion_centerComponents T.ideal T.mult T.boundary]
  intro x hx
  obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.1 hx
  have hCcomp : C ∈ intersectionComponents T.boundary (lexMaxIndices T.ideal T.mult T.boundary) :=
    centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary hC
  have hcard : (lexMaxIndices T.ideal T.mult T.boundary).card =
      minIndexCard T.ideal T.mult T.boundary := card_lexMaxIndices hGeom hT h
  have hne : (lexMaxIndices T.ideal T.mult T.boundary).Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact Nat.pos_of_ne_zero h
  obtain ⟨j, hj⟩ := hne
  have hsub : C ⊆ (↑(T.boundary.get j).support : Set ↥T.scheme) :=
    (subset_support_iff_mem_of_mem_intersectionComponents hGeom hT hCcomp j).2 hj
  have hmemlist : T.boundary.get j ∈ T.boundary := by simp
  exact Set.mem_iUnion₂.2 ⟨T.boundary.get j, hmemlist, hsub hxC⟩

theorem exists_controlledTransform_monomialCenter :
    ∃ J : (Blowup.blowup (monomialCenter T.ideal T.mult T.boundary)).IdealSheafData,
      ((monomialCenter T.ideal T.mult T.boundary).comap
            (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) ^ T.mult * J =
        T.ideal.comap (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary)) := by
  classical
  have : CharZero T.base := hT.valid.charZero
  have : Smooth T.structMap := hT.valid.smooth
  have : IsNoetherian T.scheme := hT.valid.isNoetherian
  have : IsNoetherian (Blowup.blowup (monomialCenter T.ideal T.mult T.boundary)) :=
    isNoetherian_of_isBlowupAlongIdealSheaf (Blowup.blowup.isBlowupAlongIdealSheaf_proj (monomialCenter T.ideal T.mult T.boundary))
  have hle : T.ideal ≤ monomialCenter T.ideal T.mult T.boundary ^ T.mult :=
    le_pow_of_hasStrictNormalCrossingsWith T.structMap (monomialCenter T.ideal T.mult T.boundary) T.ideal T.boundary
      (hasStrictNormalCrossingsWith_monomialCenter hGeom hT h) T.mult (support_monomialCenter_subset_orderAtLeastLocus hGeom hT h)
  obtain ⟨J, hJ, -⟩ :=
    existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf
      (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))
      (monomialCenter T.ideal T.mult T.boundary) T.ideal T.mult
      (Blowup.blowup.isBlowupAlongIdealSheaf_proj (monomialCenter T.ideal T.mult T.boundary)) hle
  exact ⟨J, hJ⟩

theorem monomialCenter_spec :
    monomialCenter T.ideal T.mult T.boundary ≠ ⊤ ∧
      Smooth
        ((monomialCenter T.ideal T.mult T.boundary).subschemeι ≫ T.structMap) ∧
      HasStrictNormalCrossingsWith T.structMap (monomialCenter T.ideal T.mult T.boundary) T.boundary ∧
      (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) ⊆
        orderAtLeastLocus T.ideal T.mult ∧
      (∃ J : (Blowup.blowup (monomialCenter T.ideal T.mult T.boundary)).IdealSheafData,
        ((monomialCenter T.ideal T.mult T.boundary).comap
              (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) ^ T.mult * J =
          T.ideal.comap (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) :=
  ⟨monomialCenter_ne_top hGeom hT h, smooth_monomialCenter hGeom hT h, hasStrictNormalCrossingsWith_monomialCenter hGeom hT h,
    support_monomialCenter_subset_orderAtLeastLocus hGeom hT h,
    exists_controlledTransform_monomialCenter hGeom hT h⟩


end

section
variable {Y : Scheme.{u}}

theorem exists_isIrreducibleComponentOf_mem (S : Set ↥Y) (x : ↥Y) (hx : x ∈ S) :
    ∃ C : Set ↥Y, x ∈ C ∧ IsIrreducibleComponentOf C S := by
  have hsing : IsPreirreducible ({(⟨x, hx⟩ : ↥S)} : Set ↥S) := by
    intro u v _ _ hu hv
    obtain ⟨p, hp, hpu⟩ := hu
    obtain ⟨q, hq, hqv⟩ := hv
    rw [Set.mem_singleton_iff] at hp hq
    subst hp
    subst hq
    exact ⟨(⟨x, hx⟩ : ↥S), rfl, hpu, hqv⟩
  obtain ⟨t, ht, hts, hmax⟩ := exists_preirreducible ({(⟨x, hx⟩ : ↥S)} : Set ↥S) hsing
  have hxt : (⟨x, hx⟩ : ↥S) ∈ t := hts (Set.mem_singleton_iff.2 rfl)
  have hxim : x ∈ Subtype.val '' t := ⟨(⟨x, hx⟩ : ↥S), hxt, rfl⟩
  have hsubS : Subtype.val '' t ⊆ S := by
    rintro y ⟨p, -, rfl⟩
    exact p.2
  have hpre : IsPreirreducible (Subtype.val '' t) := by
    intro u v hu hv hu' hv'
    obtain ⟨p, hpim, hpu⟩ := hu'
    obtain ⟨q, hqim, hqv⟩ := hv'
    obtain ⟨p', hp't, hp'eq⟩ := hpim
    obtain ⟨q', hq't, hq'eq⟩ := hqim
    have hp'u : p' ∈ Subtype.val ⁻¹' u := by
      rw [Set.mem_preimage, hp'eq]
      exact hpu
    have hq'v : q' ∈ Subtype.val ⁻¹' v := by
      rw [Set.mem_preimage, hq'eq]
      exact hqv
    obtain ⟨r, hrt, hru, hrv⟩ :=
      ht (Subtype.val ⁻¹' u) (Subtype.val ⁻¹' v) (hu.preimage continuous_subtype_val)
        (hv.preimage continuous_subtype_val) ⟨p', hp't, hp'u⟩ ⟨q', hq't, hq'v⟩
    exact ⟨(r : ↥Y), ⟨r, hrt, rfl⟩, hru, hrv⟩
  have hirr : IsIrreducible (Subtype.val '' t) := ⟨⟨x, hxim⟩, hpre⟩
  have hmaxi : ∀ C' : Set ↥Y, IsIrreducible C' → Subtype.val '' t ⊆ C' → C' ⊆ S →
      C' = Subtype.val '' t := by
    intro C' hC' hle hC'S
    have hpre' : IsPreirreducible (Subtype.val ⁻¹' C' : Set ↥S) := by
      intro u v hu hv hu' hv'
      obtain ⟨u₀, hu₀, hu₀e⟩ : ∃ u₀ : Set ↥Y, IsOpen u₀ ∧ Subtype.val ⁻¹' u₀ = u :=
        isOpen_induced_iff.1 hu
      obtain ⟨v₀, hv₀, hv₀e⟩ : ∃ v₀ : Set ↥Y, IsOpen v₀ ∧ Subtype.val ⁻¹' v₀ = v :=
        isOpen_induced_iff.1 hv
      subst hu₀e
      subst hv₀e
      obtain ⟨p, hp, hpu⟩ := hu'
      obtain ⟨q, hq, hqv⟩ := hv'
      obtain ⟨y, hyC', hyu, hyv⟩ :=
        hC'.2 u₀ v₀ hu₀ hv₀ ⟨(p : ↥Y), hp, hpu⟩ ⟨(q : ↥Y), hq, hqv⟩
      exact ⟨(⟨y, hC'S hyC'⟩ : ↥S), hyC', hyu, hyv⟩
    have hsubt : t ⊆ Subtype.val ⁻¹' C' := fun p hp => hle ⟨p, hp, rfl⟩
    have hkey : Subtype.val ⁻¹' C' = t := hmax _ hpre' hsubt
    refine Set.Subset.antisymm ?_ hle
    intro y hy
    refine ⟨(⟨y, hC'S hy⟩ : ↥S), ?_, rfl⟩
    rw [← hkey]
    exact hy
  refine ⟨Subtype.val '' t, hxim, ?_⟩
  show IsIrreducible (Subtype.val '' t) ∧ Subtype.val '' t ⊆ S ∧
    ∀ C' : Set ↥Y, IsIrreducible C' → Subtype.val '' t ⊆ C' → C' ⊆ S → C' = Subtype.val '' t
  exact ⟨hirr, hsubS, hmaxi⟩

theorem exists_mem_intersectionComponents_of_mem_support (L : List Y.IdealSheafData) (J : Finset (Fin L.length)) (x : ↥Y)
    (hx : x ∈ (↑(intersectionIdeal L J).support : Set ↥Y)) :
    ∃ C : Set ↥Y, x ∈ C ∧ C ∈ intersectionComponents L J := by
  obtain ⟨C, hxC, hcomp⟩ :=
    exists_isIrreducibleComponentOf_mem (↑(intersectionIdeal L J).support : Set ↥Y) x hx
  exact ⟨C, hxC, (mem_intersectionComponents_iff L J C).2 hcomp⟩


end

theorem orderAtLeastLocus_eq_empty_of_minIndexCard_eq_zero (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary = 0) :
    orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme) := by
  classical
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨U, hxU, a, hmon⟩ := hT.monomialNear x hx
  have hmult : 1 ≤ T.mult := hT.valid.one_le_mult
  have hmle : (T.mult : ℕ∞) ≤ orderAt T.ideal x := (mem_orderAtLeastLocus_iff _ _ _).1 hx
  have hord : orderAt T.ideal x
      = ((∑ j ∈ supportIndices T.boundary x, a j : ℕ) : ℕ∞) :=
    orderAt_eq_sum_supportIndices hGeom hT x U hxU a hmon
  have hJne : (supportIndices T.boundary x).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (supportIndices T.boundary x) with he | hne'
    · exfalso
      rw [he, Finset.sum_empty] at hord
      rw [hord] at hmle
      have hm0 : T.mult ≤ 0 := by exact_mod_cast hmle
      omega
    · exact hne'
  have hxsupp : x ∈ (↑(intersectionIdeal T.boundary (supportIndices T.boundary x)).support :
      Set ↥T.scheme) :=
    mem_support_intersectionIdeal T.boundary (supportIndices T.boundary x) x
      fun j hj => (mem_supportIndices T.boundary x j).1 hj
  obtain ⟨C, hxC, hcomp⟩ :=
    exists_isIrreducibleComponentOf_mem
      (↑(intersectionIdeal T.boundary (supportIndices T.boundary x)).support : Set ↥T.scheme) x hxsupp
  have hCmem : C ∈ intersectionComponents T.boundary (supportIndices T.boundary x) :=
    (mem_intersectionComponents_iff T.boundary (supportIndices T.boundary x) C).2 hcomp
  have hordC : orderAlong T.ideal C
      = ((∑ j ∈ supportIndices T.boundary x, a j : ℕ) : ℕ∞) :=
    orderAlong_eq_sum_of_monomial hGeom hT hCmem hxC U hxU a hmon
  have hordm : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    rw [hordC, ← hord]
    exact hmle
  have hcand : IsCandidateComponent T.ideal T.mult T.boundary
      (supportIndices T.boundary x).card (supportIndices T.boundary x) C := by
    unfold IsCandidateComponent
    refine ⟨?_, ?_, ?_⟩
    · rfl
    · assumption
    · assumption
  have hcontr : ¬ ∃ r : ℕ, 1 ≤ r ∧ ∃ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
      IsCandidateComponent T.ideal T.mult T.boundary r J C := (minIndexCard_eq_zero_iff _ _ _).1 h
  have hcard : 1 ≤ (supportIndices T.boundary x).card := by
    have hpos := Finset.card_pos.2 hJne
    omega
  exact hcontr ⟨(supportIndices T.boundary x).card, hcard,
    supportIndices T.boundary x, C, hcand⟩

theorem minIndexCard_eq_zero_of_orderAtLeastLocus_eq_empty {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (h : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)) :
    minIndexCard T.ideal T.mult T.boundary = 0 := by
  rw [minIndexCard_eq_zero_iff]
  rintro ⟨r, hr, J, C, hcand⟩
  have hC : C ∈ intersectionComponents T.boundary J :=
    mem_intersectionComponents_of_isCandidateComponent_consolidated361 T.ideal T.mult T.boundary r J C hcand
  have hord : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    unfold IsCandidateComponent at hcand
    exact hcand.2.2
  have hsub : C ⊆ orderAtLeastLocus T.ideal T.mult :=
    subset_orderAtLeastLocus_of_le_orderAlong hT hC T.mult hord
  obtain ⟨x, hx⟩ := (isIrreducible_of_mem_intersectionComponents hC).1
  rw [h] at hsub
  exact (Set.mem_empty_iff_false x).mp (hsub hx)

def maxOrderCandidatePairs {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) : Set (Finset (Fin L.length) × Set ↥Y) :=
  {p : Finset (Fin L.length) × Set ↥Y |
    IsCandidateComponent I m L (minIndexCard I m L) p.1 p.2 ∧ orderAlong I p.2 = maxCandidateOrder I m L}

theorem mem_maxOrderCandidatePairs_iff {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) (p : Finset (Fin L.length) × Set ↥Y) :
    p ∈ maxOrderCandidatePairs I m L ↔
      IsCandidateComponent I m L (minIndexCard I m L) p.1 p.2 ∧ orderAlong I p.2 = maxCandidateOrder I m L :=
  Iff.rfl

theorem finite_maxOrderCandidatePairs (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) :
    (maxOrderCandidatePairs T.ideal T.mult T.boundary).Finite := by
  refine (finite_setOf_isCandidateComponent hGeom hT).subset ?_
  rintro ⟨J, C⟩ ⟨hcand, -⟩
  exact ⟨minIndexCard T.ideal T.mult T.boundary, hcand⟩


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.StrictTransformComponents
section

open TopologicalSpace

section

theorem exists_isOpen_inter_subset_of_maximal {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] (A : Set α) (hA : IsClosed A) (C : Set α)
    (hC : IsIrreducible C) (hCA : C ⊆ A)
    (hmax : ∀ C' : Set α, IsIrreducible C' → C ⊆ C' → C' ⊆ A → C' = C) :
    ∃ O : Set α, IsOpen O ∧ (O ∩ A).Nonempty ∧ O ∩ A ⊆ C := by
  classical
  obtain ⟨S, hirr, hsup⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finset_irreducible
      (⟨A, hA⟩ : TopologicalSpace.Closeds α)
  have hcoe : ∀ S' : Finset (TopologicalSpace.Closeds α),
      ((S'.sup id : TopologicalSpace.Closeds α) : Set α) = ⋃ k ∈ S', (k : Set α) := by
    intro S'
    refine Finset.induction_on S' ?_ ?_
    · simp
    · intro a S'' _ ih
      simp [Finset.sup_insert, ih]
  have hA' : A = ⋃ k ∈ S, (k : Set α) :=
    (congrArg (fun s : TopologicalSpace.Closeds α => (s : Set α)) hsup).trans (hcoe S)
  obtain ⟨T, hTdef⟩ : ∃ T : Finset (TopologicalSpace.Closeds α),
      T = S.filter (fun k : TopologicalSpace.Closeds α => ¬ ((k : Set α) ⊆ C)) := ⟨_, rfl⟩
  have hmemT : ∀ k : TopologicalSpace.Closeds α,
      k ∈ T ↔ k ∈ S ∧ ¬ ((k : Set α) ⊆ C) := by
    intro k
    rw [hTdef]
    exact Finset.mem_filter
  have hTcl : IsClosed (⋃ k ∈ T, (k : Set α)) :=
    Set.Finite.isClosed_biUnion (Finset.finite_toSet _) (fun k _ => k.2)
  refine ⟨(⋃ k ∈ T, (k : Set α))ᶜ, hTcl.isOpen_compl, ?_, ?_⟩
  · by_contra hemp
    have hAsub : A ⊆ ⋃ k ∈ T, (k : Set α) := by
      intro z hz
      by_contra hz'
      exact hemp ⟨z, hz', hz⟩
    obtain ⟨s, hsT, hCs⟩ :=
      isIrreducible_iff_sUnion_isClosed.mp hC
        (T.image fun k : TopologicalSpace.Closeds α => (k : Set α))
        (by
          intro z hz
          obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
          exact k.2)
        (by
          refine hCA.trans (hAsub.trans ?_)
          intro z hz
          obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp hz
          exact Set.mem_sUnion.mpr
            ⟨(k : Set α), Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hk), hzk⟩)
    obtain ⟨k, hkT, rfl⟩ := Finset.mem_image.mp hsT
    have hkS : k ∈ S := ((hmemT k).mp hkT).1
    have hkA : (k : Set α) ⊆ A := by
      rw [hA']
      exact fun z hz => Set.mem_iUnion₂.mpr ⟨k, hkS, hz⟩
    exact ((hmemT k).mp hkT).2 (le_of_eq (hmax (k : Set α) (hirr ⟨k, hkS⟩) hCs hkA))
  · rintro z ⟨hzO, hzA⟩
    rw [hA'] at hzA
    obtain ⟨k, hkS, hzk⟩ := Set.mem_iUnion₂.mp hzA
    by_cases hk : (k : Set α) ⊆ C
    · exact hk hzk
    · exact absurd (Set.mem_iUnion₂.mpr ⟨k, (hmemT k).mpr ⟨hkS, hk⟩, hzk⟩) hzO

theorem exists_specializes_of_homeomorph {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (p : α → Prop) (q : β → Prop) (f : α → β) (e : {x : α // p x} ≃ₜ {y : β // q y})
    (he : ∀ x : {x : α // p x}, ((e x : β)) = f (x : α))
    (ξ : β) (hξ : q ξ) (y : α) (hy : p y) (hs : f y ∈ closure ({ξ} : Set β)) :
    ∃ x : α, p x ∧ f x = ξ ∧ y ∈ closure ({x} : Set α) := by
  refine ⟨((e.symm ⟨ξ, hξ⟩ : {x : α // p x}) : α), (e.symm ⟨ξ, hξ⟩).2, ?_, ?_⟩
  · have h1 := he (e.symm ⟨ξ, hξ⟩)
    rw [← h1]
    simp
  · have h2 : ((e ⟨y, hy⟩ : {z : β // q z}) : β) ∈ closure ({ξ} : Set β) := by
      rw [he ⟨y, hy⟩]
      exact hs
    have h3 : (e ⟨y, hy⟩) ∈ closure ({(⟨ξ, hξ⟩ : {z : β // q z})} : Set {z : β // q z}) := by
      rw [closure_subtype, Set.image_singleton]
      exact h2
    have h4 := Set.mem_image_of_mem (⇑e.symm) h3
    rw [e.symm.image_closure, Set.image_singleton, Homeomorph.symm_apply_apply] at h4
    have h5 := closure_subtype.mp h4
    rwa [Set.image_singleton] at h5

section
variable {X X' : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)

theorem exists_lift_of_specializes_of_isBlowupAlongIdealSheaf (h : Blowup.IsBlowupAlongIdealSheaf π Z) (ξ : ↥X) (hξ : ξ ∉ Z.support)
    (y : ↥X') (hy : π y ∉ Z.support) (hs : π y ∈ closure ({ξ} : Set ↥X)) :
    ∃ x : ↥X', π x = ξ ∧ y ∈ closure ({x} : Set ↥X') := by
  have h1 := h.restrict Z.support.compl
  rw [Blowup.comap_ι_support_compl_eq_top Z] at h1
  have hiso : IsIso (π ∣_ Z.support.compl) := h1.isIso_of_top
  obtain ⟨e, he⟩ : ∃ e : {a : ↥X' // a ∈ (π ⁻¹ᵁ Z.support.compl)} ≃ₜ
      {b : ↥X // b ∈ Z.support.compl},
      ∀ a : {a : ↥X' // a ∈ (π ⁻¹ᵁ Z.support.compl)},
        ((e a : ↥X)) = (⇑π.base) (a : ↥X') :=
    ⟨Scheme.homeoOfIso (asIso (π ∣_ Z.support.compl)),
      fun a => morphismRestrict_base_coe π Z.support.compl a⟩
  have hξ' : ξ ∈ Z.support.compl := hξ
  have hy' : y ∈ (π ⁻¹ᵁ Z.support.compl) := hy
  obtain ⟨x, -, hx1, hx2⟩ :=
    exists_specializes_of_homeomorph (fun a : ↥X' => a ∈ (π ⁻¹ᵁ Z.support.compl))
      (fun b : ↥X => b ∈ Z.support.compl) (fun a => (⇑π.base) a) e he ξ hξ' y hy' hs
  exact ⟨x, hx1, hx2⟩

theorem eq_of_isBlowupAlongIdealSheaf_of_notMem_support (h : Blowup.IsBlowupAlongIdealSheaf π Z) (x y : ↥X')
    (hx : π x ∉ Z.support) (hy : π y ∉ Z.support) (hxy : π x = π y) : x = y := by
  have h1 := h.restrict Z.support.compl
  rw [Blowup.comap_ι_support_compl_eq_top Z] at h1
  have hiso : IsIso (π ∣_ Z.support.compl) := h1.isIso_of_top
  obtain ⟨e, he⟩ : ∃ e : {a : ↥X' // a ∈ (π ⁻¹ᵁ Z.support.compl)} ≃ₜ
      {b : ↥X // b ∈ Z.support.compl},
      ∀ a : {a : ↥X' // a ∈ (π ⁻¹ᵁ Z.support.compl)},
        ((e a : ↥X)) = (⇑π.base) (a : ↥X') :=
    ⟨Scheme.homeoOfIso (asIso (π ∣_ Z.support.compl)),
      fun a => morphismRestrict_base_coe π Z.support.compl a⟩
  have hx' : x ∈ (π ⁻¹ᵁ Z.support.compl) := hx
  have hy' : y ∈ (π ⁻¹ᵁ Z.support.compl) := hy
  have key : e ⟨x, hx'⟩ = e ⟨y, hy'⟩ := by
    apply Subtype.ext
    rw [he ⟨x, hx'⟩, he ⟨y, hy'⟩]
    exact hxy
  exact congrArg Subtype.val (e.injective key)

theorem notMem_support_exceptionalIdeal (y : ↥X') (hy : π y ∉ Z.support) :
    y ∉ (Blowup.exceptionalIdeal π Z).support := by
  have h1 : (((Z.comap π).support : TopologicalSpace.Closeds ↥X') : Set ↥X')
      = ⇑π.base ⁻¹' ((Z.support : TopologicalSpace.Closeds ↥X) : Set ↥X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  intro hmem
  have hmem' : y ∈ (((Z.comap π).support : TopologicalSpace.Closeds ↥X') : Set ↥X') := hmem
  rw [h1] at hmem'
  exact hy hmem'


end

theorem exists_eq_closure_of_isIrreducibleComponentOf_strictTransform :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        Smooth (CategoryTheory.CategoryStruct.comp Z.subschemeι T.structMap) →
        HasStrictNormalCrossingsWith T.structMap Z T.boundary →
        ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
          ∀ D ∈ T.boundary,
            ∀ C' : Set ↥X',
              IsIrreducibleComponentOf C' (↑(Blowup.strictTransform π Z D).support : Set ↥X') →
              ∃ (η' : ↥X') (C : Set ↥T.scheme),
                C' = closure ({η'} : Set ↥X') ∧
                η' ∉ (Blowup.exceptionalIdeal π Z).support ∧
                IsIrreducibleComponentOf C (↑D.support : Set ↥T.scheme) ∧
                ¬ C ⊆ (↑Z.support : Set ↥T.scheme) ∧
                C = closure ({π η'} : Set ↥T.scheme) := by
  intro T hT Z _hsm _hsnc X' π hπ D _hD C' hC'
  have hTnoeth : IsNoetherian T.scheme := hT.isNoetherian
  have hX'noeth : IsNoetherian X' := isNoetherian_of_isBlowupAlongIdealSheaf hπ
  have hX'loc : IsLocallyNoetherian X' := inferInstance
  have hX'top : TopologicalSpace.NoetherianSpace ↥X' := inferInstance
  obtain ⟨hC'irr, hC'sub, hC'max⟩ := hC'
  have hcont : Continuous (⇑π.base) := π.continuous
  have hSclosed : IsClosed (↑(Blowup.strictTransform π Z D).support : Set ↥X') :=
    (Blowup.strictTransform π Z D).support.2
  have hSeq : (↑(Blowup.strictTransform π Z D).support : Set ↥X')
      = closure (⇑π.base ⁻¹'
          ((↑D.support : Set ↥T.scheme) \ (↑Z.support : Set ↥T.scheme))) :=
    support_strictTransform_eq_closure_preimage π Z D
  have hC'closed : IsClosed C' := by
    have h1 : closure C' = C' :=
      hC'max (closure C') hC'irr.closure subset_closure
        (hSclosed.closure_subset_iff.mpr hC'sub)
    rw [← h1]
    exact isClosed_closure
  obtain ⟨η', hgen⟩ := QuasiSober.sober hC'irr hC'closed
  have hη'' : closure ({η'} : Set ↥X') = C' := hgen
  obtain ⟨O, hOopen, hOne, hOsub⟩ :=
    exists_isOpen_inter_subset_of_maximal (↑(Blowup.strictTransform π Z D).support : Set ↥X')
      hSclosed C' hC'irr hC'sub hC'max
  obtain ⟨w, hwO, hwS⟩ := hOne
  have hwA : w ∈ closure (⇑π.base ⁻¹'
      ((↑D.support : Set ↥T.scheme) \ (↑Z.support : Set ↥T.scheme))) := by
    rw [← hSeq]; exact hwS
  obtain ⟨a, haO, haA⟩ := mem_closure_iff.mp hwA O hOopen hwO
  have haA' : (⇑π.base) a
      ∈ ((↑D.support : Set ↥T.scheme) \ (↑Z.support : Set ↥T.scheme)) := haA
  have haS : a ∈ (↑(Blowup.strictTransform π Z D).support : Set ↥X') := by
    rw [hSeq]
    exact subset_closure haA
  have haC' : a ∈ C' := hOsub ⟨haO, haS⟩
  have hVopen : IsOpen ((π ⁻¹ᵁ Z.support.compl : X'.Opens) : Set ↥X') :=
    (π ⁻¹ᵁ Z.support.compl).isOpen
  have haV : a ∈ ((π ⁻¹ᵁ Z.support.compl : X'.Opens) : Set ↥X') := haA'.2
  have hη'V : η' ∈ ((π ⁻¹ᵁ Z.support.compl : X'.Opens) : Set ↥X') := by
    have h1 : a ∈ closure ({η'} : Set ↥X') := by rw [hη'']; exact haC'
    obtain ⟨z, hzV, hz⟩ := mem_closure_iff.mp h1 _ hVopen haV
    have hz' : z = η' := hz
    rwa [hz'] at hzV
  have hπη' : (⇑π.base) η' ∉ (↑Z.support : Set ↥T.scheme) := hη'V
  have hη'S : η' ∈ (↑(Blowup.strictTransform π Z D).support : Set ↥X') := by
    refine hC'sub ?_
    rw [← hη'']
    exact subset_closure rfl
  have hπη'D : (⇑π.base) η' ∈ (↑D.support : Set ↥T.scheme) := by
    have h2 : η' ∈ closure (⇑π.base ⁻¹'
        ((↑D.support : Set ↥T.scheme) \ (↑Z.support : Set ↥T.scheme))) := by
      rw [← hSeq]; exact hη'S
    have h3 : closure (⇑π.base ⁻¹'
          ((↑D.support : Set ↥T.scheme) \ (↑Z.support : Set ↥T.scheme)))
        ⊆ ⇑π.base ⁻¹' (↑D.support : Set ↥T.scheme) :=
      closure_minimal (Set.preimage_mono Set.sdiff_subset)
        (IsClosed.preimage hcont D.support.2)
    exact h3 h2
  have hCirr : IsIrreducible (closure ({((⇑π.base) η')} : Set ↥T.scheme)) :=
    isIrreducible_singleton.closure
  have hCsub : closure ({((⇑π.base) η')} : Set ↥T.scheme) ⊆ (↑D.support : Set ↥T.scheme) :=
    closure_minimal (Set.singleton_subset_iff.mpr hπη'D) D.support.2
  have hCmax : ∀ C₂ : Set ↥T.scheme, IsIrreducible C₂ →
      closure ({((⇑π.base) η')} : Set ↥T.scheme) ⊆ C₂ →
      C₂ ⊆ (↑D.support : Set ↥T.scheme) →
      C₂ = closure ({((⇑π.base) η')} : Set ↥T.scheme) := by
    intro C₂ hC₂irr hCC₂ hC₂D
    obtain ⟨ξ, hgen2⟩ := QuasiSober.sober hC₂irr.closure isClosed_closure
    have hξ2 : closure ({ξ} : Set ↥T.scheme) = closure C₂ := hgen2
    have hξD : ξ ∈ (↑D.support : Set ↥T.scheme) := by
      have h4 : ξ ∈ closure C₂ := by rw [← hξ2]; exact subset_closure rfl
      exact (closure_minimal hC₂D D.support.2) h4
    have hspec : (⇑π.base) η' ∈ closure ({ξ} : Set ↥T.scheme) := by
      rw [hξ2]
      exact subset_closure (hCC₂ (subset_closure rfl))
    have hξZ : ξ ∉ (↑Z.support : Set ↥T.scheme) := by
      intro hmem
      exact hπη' ((closure_minimal (Set.singleton_subset_iff.mpr hmem) Z.support.2) hspec)
    obtain ⟨x, hx1, hx2⟩ :=
      exists_lift_of_specializes_of_isBlowupAlongIdealSheaf π Z hπ ξ hξZ η' hπη' hspec
    have hx1' : (⇑π.base) x = ξ := hx1
    have hxmem : (⇑π.base) x
        ∈ ((↑D.support : Set ↥T.scheme) \ (↑Z.support : Set ↥T.scheme)) := by
      rw [hx1']
      exact ⟨hξD, hξZ⟩
    have hxS : x ∈ (↑(Blowup.strictTransform π Z D).support : Set ↥X') := by
      rw [hSeq]
      exact subset_closure hxmem
    have hclx : closure ({x} : Set ↥X') ⊆ (↑(Blowup.strictTransform π Z D).support : Set ↥X') :=
      closure_minimal (Set.singleton_subset_iff.mpr hxS) hSclosed
    have hsub2 : C' ⊆ closure ({x} : Set ↥X') := by
      rw [← hη'']
      exact closure_minimal (Set.singleton_subset_iff.mpr hx2) isClosed_closure
    have heq : closure ({x} : Set ↥X') = C' :=
      hC'max (closure ({x} : Set ↥X')) isIrreducible_singleton.closure hsub2 hclx
    have hxC' : x ∈ closure ({η'} : Set ↥X') := by
      rw [hη'', ← heq]
      exact subset_closure rfl
    have himg : (⇑π.base) x ∈ closure (⇑π.base '' ({η'} : Set ↥X')) :=
      image_closure_subset_closure_image hcont ⟨x, hxC', rfl⟩
    rw [Set.image_singleton] at himg
    have hξC : ξ ∈ closure ({((⇑π.base) η')} : Set ↥T.scheme) := by
      rw [← hx1']; exact himg
    refine Set.Subset.antisymm ?_ hCC₂
    refine subset_trans subset_closure ?_
    rw [← hξ2]
    exact closure_minimal (Set.singleton_subset_iff.mpr hξC) isClosed_closure
  have hcomp : IsIrreducibleComponentOf (closure ({((⇑π.base) η')} : Set ↥T.scheme))
      (↑D.support : Set ↥T.scheme) := ⟨hCirr, hCsub, hCmax⟩
  refine ⟨η', closure ({((⇑π.base) η')} : Set ↥T.scheme), hη''.symm,
    notMem_support_exceptionalIdeal π Z η' hπη', hcomp, ?_, rfl⟩
  intro hsub
  exact hπη' (hsub (subset_closure rfl))


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BlowupAtMonomialCenter
section


section

def blowupTriple (T : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (π : X' ⟶ T.scheme)
    (q : X' ⟶ Spec (CommRingCat.of T.base)) (I' : X'.IdealSheafData) : MarkedIdealWithBoundary.{u} where
  base := T.base
  instField := inferInstance
  scheme := X'
  structMap := q
  ideal := I'
  mult := T.mult
  boundary := transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary

@[simp] theorem blowupTriple_boundary (T : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}}
    (π : X' ⟶ T.scheme) (q : X' ⟶ Spec (CommRingCat.of T.base)) (I' : X'.IdealSheafData) :
    (blowupTriple T π q I').boundary =
      transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary := rfl

theorem orderAt_transform_eq_of_not_mem_exceptional (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    {X' : Scheme.{u}} (π : X' ⟶ T.scheme)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π (monomialCenter T.ideal T.mult T.boundary))
    (I' : X'.IdealSheafData)
    (hI' : (monomialCenter T.ideal T.mult T.boundary).comap π ^ T.mult * I' =
      T.ideal.comap π)
    (x' : ↥X')
    (hx' : x' ∉ (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).support) :
    orderAt I' x' = orderAt T.ideal (π x') := by
  have hE : Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)
      = (monomialCenter T.ideal T.mult T.boundary).comap π := by
    rw [Blowup.exceptionalIdeal_eq_comap]
  have hx2 : x' ∉ ((monomialCenter T.ideal T.mult T.boundary).comap π).support := by
    rw [← hE]
    exact hx'
  have htop : stalkIdeal ((monomialCenter T.ideal T.mult T.boundary).comap π) x' = ⊤ := by
    by_contra hne
    exact hx2 ((mem_support_iff_stalkIdeal_ne_top _ _).2 hne)
  have hst : stalkIdeal (T.ideal.comap π) x' = stalkIdeal I' x' := by
    rw [← hI', stalkIdeal_mul, stalkIdeal_pow, htop, ← Ideal.one_eq_top, one_pow, one_mul]
  exact (orderAt_eq_of_stalkIdeal_eq hst).symm.trans
    (hGeom.orderAt_comap_off_exceptional T hT.valid X' π
      (monomialCenter T.ideal T.mult T.boundary) hπ x' hx' T.ideal)

theorem orderAlong_transform_eq_of_genericPoint_not_mem_exceptional (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (_h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    {X' : Scheme.{u}} (π : X' ⟶ T.scheme)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π (monomialCenter T.ideal T.mult T.boundary))
    (I' : X'.IdealSheafData)
    (hI' : (monomialCenter T.ideal T.mult T.boundary).comap π ^ T.mult * I' =
      T.ideal.comap π)
    {J : Finset (Fin T.boundary.length)} {C' : Set ↥X'}
    (hC' : C' ∈ intersectionComponents
      (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
      (J.image (strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)))
    (hoff : (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∉
      (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).support) :
    orderAlong I' C' = orderAlong T.ideal (⇑π '' C') := by
  have hgen : IsGenericPoint (isIrreducible_of_mem_intersectionComponents hC').genericPoint C' :=
    isGenericPoint_genericPoint_of_mem_intersectionComponents hC'
  have hSirr : IsIrreducible (⇑π '' C') :=
    (isIrreducible_of_mem_intersectionComponents hC').image _ π.continuous.continuousOn
  have hclim : closure (⇑π '' C')
      = closure ({π (isIrreducible_of_mem_intersectionComponents hC').genericPoint} : Set ↥T.scheme) :=
    closure_image_genericPoint (f := ⇑π) π.continuous hgen
  have h2 : orderAlong T.ideal (⇑π '' C')
      = orderAt T.ideal (π (isIrreducible_of_mem_intersectionComponents hC').genericPoint) := by
    rw [orderAlong_eq_orderAt_genericPoint T.ideal hSirr]
    have h3 : closure ({hSirr.genericPoint} : Set ↥T.scheme)
        = closure ({π (isIrreducible_of_mem_intersectionComponents hC').genericPoint} : Set ↥T.scheme) := by
      rw [← hclim]
      simp
    rw [(inseparable_iff_closure_eq.mpr h3).eq]
  rw [orderAlong_eq_orderAt_of_mem_intersectionComponents I' hC', h2]
  exact orderAt_transform_eq_of_not_mem_exceptional hGeom hT π hπ I' hI' _ hoff

section
variable {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData) (L : List X.IdealSheafData)

private theorem get_transformedBoundary_strictTransformIndex_consolidated389 (j : Fin L.length) :
    (transformedBoundary π Z L).get (strictTransformIndex π Z L j) = Blowup.strictTransform π Z (L.get j) := by
  have hlt : ((strictTransformIndex π Z L j : Fin (transformedBoundary π Z L).length) : ℕ)
      < (L.map (Blowup.strictTransform π Z)).length := by
    rw [strictTransformIndex_val]
    simp
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_left hlt]
  exact List.getElem_map _

private theorem get_transformedBoundary_exceptionalIndex_consolidated389 :
    (transformedBoundary π Z L).get (exceptionalIndex π Z L) = Blowup.exceptionalIdeal π Z := by
  have hge : (L.map (Blowup.strictTransform π Z)).length
      ≤ ((exceptionalIndex π Z L : Fin (transformedBoundary π Z L).length) : ℕ) := by
    rw [exceptionalIndex_val]
    simp
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_right hge]
  simp [exceptionalIndex_val]

private theorem strictTransformIndex_injective_consolidated389 : Function.Injective (strictTransformIndex π Z L) := by
  intro i j hij
  have hv : ((strictTransformIndex π Z L i : Fin (transformedBoundary π Z L).length) : ℕ)
      = ((strictTransformIndex π Z L j : Fin (transformedBoundary π Z L).length) : ℕ) := by rw [hij]
  rw [strictTransformIndex_val, strictTransformIndex_val] at hv
  exact Fin.val_injective hv

private theorem eq_exceptionalIndex_or_exists_strictTransformIndex_consolidated389 (i : Fin (transformedBoundary π Z L).length) :
    i = exceptionalIndex π Z L ∨ ∃ j : Fin L.length, strictTransformIndex π Z L j = i := by
  have hlen := transformedBoundary_length π Z L
  have hi : (i : ℕ) < (transformedBoundary π Z L).length := i.isLt
  have hlt : (i : ℕ) < L.length + 1 := by omega
  rcases Nat.lt_or_ge (i : ℕ) L.length with hj | hj
  · exact Or.inr ⟨⟨(i : ℕ), hj⟩, Fin.val_injective (by rw [strictTransformIndex_val])⟩
  · refine Or.inl (Fin.val_injective ?_)
    rw [exceptionalIndex_val]
    omega

private theorem image_strictTransformIndex_preimageStrictTransformIndex_consolidated389 (J' : Finset (Fin (transformedBoundary π Z L).length))
    (hnew : exceptionalIndex π Z L ∉ J') :
    (preimageStrictTransformIndex π Z L J').image (strictTransformIndex π Z L) = J' := by
  classical
  ext i
  simp only [Finset.mem_image, mem_preimageStrictTransformIndex_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hj
  · intro hi
    rcases eq_exceptionalIndex_or_exists_strictTransformIndex_consolidated389 π Z L i with rfl | ⟨j, rfl⟩
    · exact absurd hi hnew
    · exact ⟨j, hi, rfl⟩

private theorem card_preimageStrictTransformIndex_of_not_mem_consolidated389 (J' : Finset (Fin (transformedBoundary π Z L).length)) (hnew : exceptionalIndex π Z L ∉ J') :
    (preimageStrictTransformIndex π Z L J').card = J'.card := by
  classical
  have h1 := Finset.card_image_of_injective (preimageStrictTransformIndex π Z L J') (strictTransformIndex_injective_consolidated389 π Z L)
  rw [image_strictTransformIndex_preimageStrictTransformIndex_consolidated389 π Z L J' hnew] at h1
  exact h1.symm

private theorem card_preimageStrictTransformIndex_add_one_of_mem_consolidated389 (J' : Finset (Fin (transformedBoundary π Z L).length)) (hnew : exceptionalIndex π Z L ∈ J') :
    (preimageStrictTransformIndex π Z L J').card + 1 = J'.card := by
  classical
  have himg : (preimageStrictTransformIndex π Z L J').image (strictTransformIndex π Z L) = J'.erase (exceptionalIndex π Z L) := by
    ext i
    simp only [Finset.mem_image, mem_preimageStrictTransformIndex_iff, Finset.mem_erase]
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, hj⟩
      intro hc
      have hval : ((strictTransformIndex π Z L j : Fin (transformedBoundary π Z L).length) : ℕ)
          = ((exceptionalIndex π Z L : Fin (transformedBoundary π Z L).length) : ℕ) := by rw [hc]
      rw [strictTransformIndex_val, exceptionalIndex_val] at hval
      exact absurd hval (Nat.ne_of_lt j.isLt)
    · rintro ⟨hne, hi⟩
      rcases eq_exceptionalIndex_or_exists_strictTransformIndex_consolidated389 π Z L i with rfl | ⟨j, rfl⟩
      · exact absurd rfl hne
      · exact ⟨j, hi, rfl⟩
  have h1 := Finset.card_image_of_injective (preimageStrictTransformIndex π Z L J') (strictTransformIndex_injective_consolidated389 π Z L)
  rw [himg, Finset.card_erase_of_mem hnew] at h1
  have h2 : 1 ≤ J'.card := Finset.card_pos.2 ⟨_, hnew⟩
  omega


end

private theorem exists_orderAt_comap_eq_strictTransform_add_exceptional_consolidated389 (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    {X' : Scheme.{u}} (π : X' ⟶ T.scheme) (q : X' ⟶ Spec (CommRingCat.of T.base))
    (hq : Smooth q)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π (monomialCenter T.ideal T.mult T.boundary))
    (i : Fin T.boundary.length) (x' : ↥X') :
    ∃ ε : ℕ, (ε = 0 ∨ ε = 1) ∧
      (ε = 1 ↔ ∃ V : T.scheme.Opens, π x' ∈ V ∧
        ((↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) ∩
            (V : Set ↥T.scheme)) ⊆ (↑(T.boundary.get i).support : Set ↥T.scheme)) ∧
      orderAt ((T.boundary.get i).comap π) x'
        = orderAt (Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
            (T.boundary.get i)) x'
          + (ε : ℕ∞) *
            orderAt (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)) x' := by
  classical
  have : CharZero T.base := hT.valid.charZero
  have : Smooth q := hq
  have hmemL : T.boundary.get i ∈ T.boundary := by simp
  obtain ⟨U', ε, hx'U', hε01, hεiff, hfact⟩ :=
    hGeom.blowup_total_transform T hT.valid (monomialCenter T.ideal T.mult T.boundary)
      (smooth_monomialCenter hGeom hT h) (hasStrictNormalCrossingsWith_monomialCenter hGeom hT h) X' π hπ
      (T.boundary.get i) hmemL x'
  refine ⟨ε, hε01, hεiff, ?_⟩
  have : Smooth U'.ι := inferInstance
  have : Smooth (U'.ι ≫ q) := inferInstance
  have e1 : orderAt (((T.boundary.get i).comap π).comap U'.ι) ⟨x', hx'U'⟩
      = orderAt ((T.boundary.get i).comap π) x' :=
    orderAt_comap T.base q U'.ι ((T.boundary.get i).comap π) ⟨x', hx'U'⟩
  have e2 : orderAt ((Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
        (T.boundary.get i)).comap U'.ι) ⟨x', hx'U'⟩
      = orderAt (Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
          (T.boundary.get i)) x' :=
    orderAt_comap T.base q U'.ι
      (Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary) (T.boundary.get i))
      ⟨x', hx'U'⟩
  have e3 : orderAt ((Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).comap U'.ι)
        ⟨x', hx'U'⟩
      = orderAt (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)) x' :=
    orderAt_comap T.base q U'.ι
      (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)) ⟨x', hx'U'⟩
  have hmul := orderAt_mul T.base (U'.ι ≫ q)
      ((Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
        (T.boundary.get i)).comap U'.ι)
      (((Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).comap U'.ι) ^ ε)
      ⟨x', hx'U'⟩
  have hpow := orderAt_pow T.base (U'.ι ≫ q)
      ((Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).comap U'.ι) ε
      ⟨x', hx'U'⟩
  have h4 : orderAt (((Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).comap U'.ι)
        ^ ε) ⟨x', hx'U'⟩
      = (ε : ℕ∞) *
        orderAt (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)) x' :=
    hpow.trans (congrArg (fun z : ℕ∞ => (ε : ℕ∞) * z) e3)
  calc orderAt ((T.boundary.get i).comap π) x'
      = orderAt (((T.boundary.get i).comap π).comap U'.ι) ⟨x', hx'U'⟩ := e1.symm
    _ = orderAt ((Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
            (T.boundary.get i)).comap U'.ι *
          ((Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).comap U'.ι) ^ ε)
          ⟨x', hx'U'⟩ := by rw [hfact]
    _ = orderAt ((Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
            (T.boundary.get i)).comap U'.ι) ⟨x', hx'U'⟩
        + orderAt (((Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).comap U'.ι)
            ^ ε) ⟨x', hx'U'⟩ := hmul
    _ = orderAt (Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
            (T.boundary.get i)) x'
        + (ε : ℕ∞) *
          orderAt (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)) x' := by
        rw [e2, h4]

private theorem comap_foldr_mul_consolidated389 {X Y : Scheme.{u}} (f : Y ⟶ X) (l : List X.IdealSheafData) :
    (l.foldr (· * ·) ⊤).comap f = (l.map (fun A => A.comap f)).foldr (· * ·) ⊤ := by
  induction l with
  | nil => simp
  | cons A l ih =>
    simp only [List.foldr_cons, List.map_cons,
      AlgebraicGeometry.Scheme.IdealSheafData.comap_mul, ih]

section
variable (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T) (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) {X' : Scheme.{u}} (π : X' ⟶ T.scheme) (q : X' ⟶ Spec (CommRingCat.of T.base)) (hπ : Blowup.IsBlowupAlongIdealSheaf π (monomialCenter T.ideal T.mult T.boundary)) (I' : X'.IdealSheafData) (hI' : (monomialCenter T.ideal T.mult T.boundary).comap π ^ T.mult * I' = T.ideal.comap π) (hT' : MonomialCenter.IsLocallyMonomialTriple (blowupTriple T π q I'))
include hGeom hT h hπ hI' hT'

theorem orderAlong_transform_add_mult_of_exceptionalIndex_mem {J' : Finset (Fin (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
      T.boundary).length)}
    (hJ' : exceptionalIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary ∈ J')
    {C' : Set ↥X'}
    (hC' : C' ∈ intersectionComponents
      (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) J')
    (U : T.scheme.Opens)
    (hU : π (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈ U)
    (a : Fin T.boundary.length → ℕ)
    (hmon : T.ideal.comap U.ι =
      (List.ofFn fun i : Fin T.boundary.length =>
        (T.boundary.get i).comap U.ι ^ a i).foldr (· * ·) ⊤)
    {C₀ : Set ↥T.scheme}
    (hC₀ : C₀ ∈ centerComponents T.ideal T.mult T.boundary)
    (hmem₀ : π (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈ C₀) :
    orderAlong I' C' + (T.mult : ℕ∞) =
      ((∑ i ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J', a i : ℕ) : ℕ∞)
        + orderAlong T.ideal C₀ := by
  classical
  have : CharZero T.base := hT.valid.charZero
  have : Smooth q := hT'.valid.smooth
  have hC'' : C' ∈ intersectionComponents (blowupTriple T π q I').boundary J' := hC'
  have hmemiff : ∀ i : Fin (transformedBoundary π
      (monomialCenter T.ideal T.mult T.boundary) T.boundary).length,
      ((isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈
        ((transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
          T.boundary).get i).support) ↔ i ∈ J' :=
    fun i => genericPoint_mem_support_iff_mem hGeom hT' hC'' i
  have hEmem : (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈
      (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).support := by
    have hx := (hmemiff (exceptionalIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)).2 hJ'
    rwa [get_transformedBoundary_exceptionalIndex_consolidated389] at hx
  have hstrictmem0 : Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)
      ∈ (blowupTriple T π q I').boundary := by
    simp only [blowupTriple_boundary]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hEord : orderAt (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary))
      (isIrreducible_of_mem_intersectionComponents hC').genericPoint = 1 :=
    hGeom.orderAt_boundary_eq_one (blowupTriple T π q I') hT'.valid
      (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)) hstrictmem0
      (isIrreducible_of_mem_intersectionComponents hC').genericPoint hEmem
  have hZord : orderAt ((monomialCenter T.ideal T.mult T.boundary).comap π)
      (isIrreducible_of_mem_intersectionComponents hC').genericPoint = 1 := by
    rw [← Blowup.exceptionalIdeal_eq_comap]
    exact hEord
  have h3 : orderAt (T.ideal.comap π) (isIrreducible_of_mem_intersectionComponents hC').genericPoint
      = (T.mult : ℕ∞) + orderAt I' (isIrreducible_of_mem_intersectionComponents hC').genericPoint := by
    rw [← hI', orderAt_mul T.base q, orderAt_pow T.base q, hZord, mul_one]
  have hmaxIdx : ∀ i ∈ lexMaxIndices T.ideal T.mult T.boundary,
      (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme)
        ⊆ (↑(T.boundary.get i).support : Set ↥T.scheme) := by
    intro i hi
    rw [support_monomialCenter hGeom hT h, monomialCenterSet_eq_sUnion_centerComponents]
    rintro y ⟨C, hCmem, hyC⟩
    exact (subset_support_iff_mem_of_mem_intersectionComponents hGeom hT
      (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary hCmem) i).2 hi hyC
  have hkeyc : ∀ (i : Fin T.boundary.length) (V : T.scheme.Opens),
      π (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈ V →
      ((↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme)
          ∩ (V : Set ↥T.scheme)) ⊆ (↑(T.boundary.get i).support : Set ↥T.scheme) →
      i ∈ lexMaxIndices T.ideal T.mult T.boundary := by
    intro i V hVmem hVsub
    have hC₀comp : C₀ ∈ intersectionComponents T.boundary (lexMaxIndices T.ideal T.mult T.boundary) :=
      centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary hC₀
    have hirr0 : IsIrreducible C₀ := isIrreducible_of_mem_intersectionComponents hC₀comp
    have hC₀Z : C₀ ⊆ (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) := by
      rw [support_monomialCenter hGeom hT h, monomialCenterSet_eq_sUnion_centerComponents]
      intro y hy
      exact ⟨C₀, hC₀, hy⟩
    have hclosed : IsClosed (↑(T.boundary.get i).support : Set ↥T.scheme) :=
      (T.boundary.get i).support.2
    have hcl : closure (C₀ ∩ (V : Set ↥T.scheme))
        ⊆ (↑(T.boundary.get i).support : Set ↥T.scheme) :=
      closure_minimal (fun z hz => hVsub ⟨hC₀Z hz.1, hz.2⟩) hclosed
    have hsub2 : C₀ ⊆ (↑(T.boundary.get i).support : Set ↥T.scheme) := by
      intro y hy
      refine hcl ?_
      rw [mem_closure_iff]
      intro W hW hyW
      obtain ⟨z, hzC, hzW, hzV⟩ :=
        hirr0.2 W (V : Set ↥T.scheme) hW V.isOpen ⟨y, hy, hyW⟩
          ⟨π (isIrreducible_of_mem_intersectionComponents hC').genericPoint, hmem₀, hVmem⟩
      exact ⟨z, hzW, hzC, hzV⟩
    exact (subset_support_iff_mem_of_mem_intersectionComponents hGeom hT hC₀comp i).1 hsub2
  have hξU : (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈ π ⁻¹ᵁ U := hU
  have hrestr : ∀ A : T.scheme.IdealSheafData,
      (A.comap U.ι).comap (π ∣_ U) = (A.comap π).comap (π ⁻¹ᵁ U).ι := by
    intro A
    have h1 : A.comap ((π ∣_ U) ≫ U.ι) = A.comap ((π ⁻¹ᵁ U).ι ≫ π) := by
      rw [morphismRestrict_ι]
    simpa only [AlgebraicGeometry.Scheme.IdealSheafData.comap_comp] using h1
  have hmon' : (T.ideal.comap π).comap (π ⁻¹ᵁ U).ι
      = (List.ofFn fun i : Fin T.boundary.length =>
          ((T.boundary.get i).comap π).comap (π ⁻¹ᵁ U).ι ^ a i).foldr (· * ·) ⊤ := by
    rw [← hrestr T.ideal, hmon, comap_foldr_mul_consolidated389]
    congr 1
    rw [List.map_ofFn]
    refine congrArg List.ofFn (funext fun i => ?_)
    simp only [Function.comp_apply]
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_pow, hrestr]
  have : Smooth (π ⁻¹ᵁ U).ι := inferInstance
  have : Smooth ((π ⁻¹ᵁ U).ι ≫ q) := inferInstance
  have e0 : orderAt ((T.ideal.comap π).comap (π ⁻¹ᵁ U).ι)
      ⟨(isIrreducible_of_mem_intersectionComponents hC').genericPoint, hξU⟩
      = orderAt (T.ideal.comap π) (isIrreducible_of_mem_intersectionComponents hC').genericPoint :=
    orderAt_comap T.base q (π ⁻¹ᵁ U).ι (T.ideal.comap π)
      ⟨(isIrreducible_of_mem_intersectionComponents hC').genericPoint, hξU⟩
  have ecomap : ∀ i : Fin T.boundary.length,
      orderAt (((T.boundary.get i).comap π).comap (π ⁻¹ᵁ U).ι)
          ⟨(isIrreducible_of_mem_intersectionComponents hC').genericPoint, hξU⟩
        = orderAt ((T.boundary.get i).comap π)
            (isIrreducible_of_mem_intersectionComponents hC').genericPoint :=
    fun i => orderAt_comap T.base q (π ⁻¹ᵁ U).ι ((T.boundary.get i).comap π)
      ⟨(isIrreducible_of_mem_intersectionComponents hC').genericPoint, hξU⟩
  have e2 : orderAt ((T.ideal.comap π).comap (π ⁻¹ᵁ U).ι)
      ⟨(isIrreducible_of_mem_intersectionComponents hC').genericPoint, hξU⟩
      = ∑ i : Fin T.boundary.length,
          orderAt (((T.boundary.get i).comap π).comap (π ⁻¹ᵁ U).ι ^ a i)
            ⟨(isIrreducible_of_mem_intersectionComponents hC').genericPoint, hξU⟩ := by
    rw [hmon', orderAt_foldr_mul T.base ((π ⁻¹ᵁ U).ι ≫ q)
      ⟨(isIrreducible_of_mem_intersectionComponents hC').genericPoint, hξU⟩]
    simp [List.map_ofFn, List.sum_ofFn]
  have e3 : ∀ i : Fin T.boundary.length,
      orderAt (((T.boundary.get i).comap π).comap (π ⁻¹ᵁ U).ι ^ a i)
          ⟨(isIrreducible_of_mem_intersectionComponents hC').genericPoint, hξU⟩
        = (a i : ℕ∞) * orderAt ((T.boundary.get i).comap π)
            (isIrreducible_of_mem_intersectionComponents hC').genericPoint := by
    intro i
    have hp := orderAt_pow T.base ((π ⁻¹ᵁ U).ι ≫ q)
      (((T.boundary.get i).comap π).comap (π ⁻¹ᵁ U).ι) (a i)
      ⟨(isIrreducible_of_mem_intersectionComponents hC').genericPoint, hξU⟩
    exact hp.trans (congrArg (fun z : ℕ∞ => (a i : ℕ∞) * z) (ecomap i))
  have h1 : orderAt (T.ideal.comap π) (isIrreducible_of_mem_intersectionComponents hC').genericPoint
      = ∑ i : Fin T.boundary.length, (a i : ℕ∞) *
          orderAt ((T.boundary.get i).comap π)
            (isIrreducible_of_mem_intersectionComponents hC').genericPoint := by
    rw [← e0, e2]
    exact Finset.sum_congr rfl fun i _ => e3 i
  have hoi : ∀ i : Fin T.boundary.length,
      orderAt ((T.boundary.get i).comap π)
          (isIrreducible_of_mem_intersectionComponents hC').genericPoint
        = (((if strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i ∈ J'
              then 1 else 0)
            + (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0) : ℕ) : ℕ∞) := by
    intro i
    obtain ⟨ε, hε01, hεiff, hfact⟩ :=
      exists_orderAt_comap_eq_strictTransform_add_exceptional_consolidated389 hGeom hT h π q hT'.valid.smooth hπ i
        (isIrreducible_of_mem_intersectionComponents hC').genericPoint
    have hstrictmem : Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
        (T.boundary.get i) ∈ (blowupTriple T π q I').boundary := by
      simp only [blowupTriple_boundary]
      exact List.mem_append_left _
        (List.mem_map_of_mem
          (f := Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)) (by simp))
    have hstrict : orderAt (Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
          (T.boundary.get i)) (isIrreducible_of_mem_intersectionComponents hC').genericPoint
        = ((if strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i ∈ J'
            then 1 else 0 : ℕ) : ℕ∞) := by
      by_cases hi : strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i ∈ J'
      · have hmem := (hmemiff
          (strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i)).2 hi
        rw [get_transformedBoundary_strictTransformIndex_consolidated389] at hmem
        have hone : orderAt (Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
            (T.boundary.get i)) (isIrreducible_of_mem_intersectionComponents hC').genericPoint = 1 :=
          hGeom.orderAt_boundary_eq_one (blowupTriple T π q I') hT'.valid _ hstrictmem _ hmem
        rw [hone]
        simp [hi]
      · have hnot : (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∉
            (Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
              (T.boundary.get i)).support := by
          intro hc
          refine hi ((hmemiff
            (strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i)).1 ?_)
          rw [get_transformedBoundary_strictTransformIndex_consolidated389]
          exact hc
        rw [(orderAt_eq_zero_iff_not_mem_support _ _).2 hnot]
        simp [hi]
    have hεval : ε = (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0) := by
      by_cases hi : i ∈ lexMaxIndices T.ideal T.mult T.boundary
      · rw [if_pos hi]
        exact hεiff.2 ⟨⊤, trivial, fun y hy => hmaxIdx i hi hy.1⟩
      · rw [if_neg hi]
        rcases hε01 with h0 | h1
        · exact h0
        · exfalso
          obtain ⟨V, hVmem, hVsub⟩ := hεiff.1 h1
          exact hi (hkeyc i V hVmem hVsub)
    rw [hfact, hstrict, hEord, mul_one, hεval, Nat.cast_add]
  have hA : ∑ i : Fin T.boundary.length,
      a i * ((if strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i ∈ J'
        then 1 else 0 : ℕ))
      = ∑ i ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J', a i := by
    simp [preimageStrictTransformIndex, mul_ite, mul_one, mul_zero, Finset.sum_filter]
  have hB : ∑ i : Fin T.boundary.length,
      a i * ((if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0 : ℕ))
      = ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j := by
    simp [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem]
  have hnat : ∑ i : Fin T.boundary.length,
      a i * ((if strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i ∈ J'
          then 1 else 0)
        + (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0))
      = (∑ i ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J', a i)
        + ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j := by
    calc ∑ i : Fin T.boundary.length,
        a i * ((if strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i ∈ J'
            then 1 else 0)
          + (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0))
        = ∑ i : Fin T.boundary.length,
            (a i * (if strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i ∈ J'
              then 1 else 0)
              + a i * (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0)) :=
          Finset.sum_congr rfl fun i _ => mul_add _ _ _
      _ = (∑ i : Fin T.boundary.length,
            a i * (if strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i ∈ J'
              then 1 else 0))
          + ∑ i : Fin T.boundary.length,
            a i * (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0) :=
          Finset.sum_add_distrib
      _ = (∑ i ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J', a i)
          + ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j := by rw [hA, hB]
  have hgoal1 : orderAlong T.ideal C₀
      = ((∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j : ℕ) : ℕ∞) :=
    orderAlong_eq_sum_of_monomial hGeom hT
      (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary hC₀) hmem₀ U hU a hmon
  have ekey : ∑ i : Fin T.boundary.length, (a i : ℕ∞) *
        orderAt ((T.boundary.get i).comap π)
          (isIrreducible_of_mem_intersectionComponents hC').genericPoint
      = ((∑ i : Fin T.boundary.length,
          a i * ((if strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary i ∈ J'
              then 1 else 0)
            + (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0)) : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hoi i, Nat.cast_mul]
  have key : (T.mult : ℕ∞) + orderAt I' (isIrreducible_of_mem_intersectionComponents hC').genericPoint
      = ((∑ i ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J', a i : ℕ) : ℕ∞)
        + ((∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j : ℕ) : ℕ∞) := by
    rw [← h3, h1, ekey, hnat, Nat.cast_add]
  rw [orderAlong_eq_orderAt_of_mem_intersectionComponents I' hC', hgoal1,
    add_comm (orderAt I' (isIrreducible_of_mem_intersectionComponents hC').genericPoint) ((T.mult : ℕ∞))]
  exact key

private theorem exceptionalIndex_not_mem_of_orderAlong_eq_maxCandidateOrder_consolidated389 (hr : minIndexCard I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
      = minIndexCard T.ideal T.mult T.boundary)
    (hv : maxCandidateOrder I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
      = maxCandidateOrder T.ideal T.mult T.boundary)
    {J' : Finset (Fin (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
      T.boundary).length)}
    {C' : Set ↥X'}
    (hcand : IsCandidateComponent I' T.mult
      (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
      (minIndexCard I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)) J' C')
    (hordmax : orderAlong I' C'
      = maxCandidateOrder I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)) :
    exceptionalIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary ∉ J' := by
  classical
  intro hnew
  have : CharZero T.base := hT.valid.charZero
  have : Smooth q := hT'.valid.smooth
  have hC'comp : C' ∈ intersectionComponents
      (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) J' := by
    have hc := hcand
    unfold IsCandidateComponent at hc
    tauto
  have hC'' : C' ∈ intersectionComponents (blowupTriple T π q I').boundary J' := hC'comp
  have hmemiff : ∀ i : Fin (transformedBoundary π
      (monomialCenter T.ideal T.mult T.boundary) T.boundary).length,
      ((isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈
        ((transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
          T.boundary).get i).support) ↔ i ∈ J' :=
    fun i => genericPoint_mem_support_iff_mem hGeom hT' hC'' i
  have hEmem : (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈
      (Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).support := by
    have hx := (hmemiff (exceptionalIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)).2 hnew
    rwa [get_transformedBoundary_exceptionalIndex_consolidated389] at hx
  have hZmem : (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈
      ((monomialCenter T.ideal T.mult T.boundary).comap π).support := by
    rw [← Blowup.exceptionalIdeal_eq_comap]
    exact hEmem
  have hπZ : π (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈
      (monomialCenter T.ideal T.mult T.boundary).support :=
    (AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap ..).mp hZmem
  have hπZset : π (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈
      (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) := hπZ
  have hcos : π (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈
      orderAtLeastLocus T.ideal T.mult := support_monomialCenter_subset_orderAtLeastLocus hGeom hT h hπZset
  obtain ⟨U, hU, a, hmon⟩ := hT.monomialNear _ hcos
  have hπcenter : π (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈
      monomialCenterSet T.ideal T.mult T.boundary := by
    rw [← support_monomialCenter hGeom hT h]
    exact hπZset
  rw [monomialCenterSet_eq_sUnion_centerComponents] at hπcenter
  obtain ⟨C₀, hC₀, hmem₀⟩ := Set.mem_sUnion.1 hπcenter
  have hformula := orderAlong_transform_add_mult_of_exceptionalIndex_mem hGeom hT h π q hπ I' hI' hT'
    hnew hC'comp U hU a hmon hC₀ hmem₀
  have hv0 : orderAlong T.ideal C₀ = maxCandidateOrder T.ideal T.mult T.boundary :=
    ((mem_centerComponents_iff T.ideal T.mult T.boundary C₀).1 hC₀).2
  have hvU : orderAlong I' C' = maxCandidateOrder T.ideal T.mult T.boundary := by rw [hordmax, hv]
  rw [hvU, hv0] at hformula
  have hvlt : maxCandidateOrder T.ideal T.mult T.boundary < ⊤ := (maxCandidateOrder_spec hGeom hT h).2.2.2
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 (ne_of_lt hvlt)
  rw [← hN] at hformula
  have hnateq : N + T.mult
      = (∑ i ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J', a i) + N := by
    exact_mod_cast hformula
  have hsumeq : (∑ i ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J', a i)
      = T.mult := by omega
  have hmpos : 1 ≤ T.mult := hT.valid.one_le_mult
  have hcardpos :
      1 ≤ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card := by
    rcases Finset.eq_empty_or_nonempty
        (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J') with he | hne
    · exfalso
      rw [he, Finset.sum_empty] at hsumeq
      omega
    · exact Finset.card_pos.2 hne
  have hdiv : ∀ j ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J',
      π (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈ (T.boundary.get j).support := by
    intro j hj
    have hj' : strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary j ∈ J' :=
      (mem_preimageStrictTransformIndex_iff π (monomialCenter T.ideal T.mult T.boundary) T.boundary J' j).1 hj
    have hmem := (hmemiff
      (strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary j)).2 hj'
    rw [get_transformedBoundary_strictTransformIndex_consolidated389] at hmem
    obtain ⟨ε, hε01, hεiff, hfact⟩ :=
      exists_orderAt_comap_eq_strictTransform_add_exceptional_consolidated389 hGeom hT h π q hT'.valid.smooth hπ j
        (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint
    have h1 : (1 : ℕ∞) ≤ orderAt (Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
        (T.boundary.get j)) (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint :=
      (one_le_orderAt_iff_mem_support _ _).2 hmem
    have h2 : (1 : ℕ∞) ≤ orderAt ((T.boundary.get j).comap π)
        (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint := by
      rw [hfact]
      exact le_trans h1 le_self_add
    have h3 : (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈
        ((T.boundary.get j).comap π).support :=
      (one_le_orderAt_iff_mem_support _ _).1 h2
    exact (AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap ..).mp h3
  have hsupp : π (isIrreducible_of_mem_intersectionComponents hC'comp).genericPoint ∈
      (intersectionIdeal T.boundary
        (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J')).support :=
    mem_support_intersectionIdeal T.boundary
      (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J') _ hdiv
  obtain ⟨C₁, hxC₁, hcomp₁⟩ := exists_isIrreducibleComponentOf_mem
    (↑(intersectionIdeal T.boundary
      (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J')).support :
        Set ↥T.scheme) _ hsupp
  have hC₁ : C₁ ∈ intersectionComponents T.boundary
      (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J') :=
    (mem_intersectionComponents_iff _ _ _).2 hcomp₁
  have hord₁ : orderAlong T.ideal C₁
      = ((∑ i ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J',
          a i : ℕ) : ℕ∞) :=
    orderAlong_eq_sum_of_monomial hGeom hT hC₁ hxC₁ U hU a hmon
  have hcand₁ : IsCandidateComponent T.ideal T.mult T.boundary
      (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card
      (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J') C₁ := by
    unfold IsCandidateComponent
    refine ⟨rfl, hC₁, ?_⟩
    rw [hord₁, hsumeq]
  have hex : ∃ r : ℕ, 1 ≤ r ∧ ∃ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
      IsCandidateComponent T.ideal T.mult T.boundary r J C :=
    ⟨_, hcardpos, _, _, hcand₁⟩
  have hle := (minIndexCard_spec T.ideal T.mult T.boundary hex).2.2 _ hcardpos _ _ hcand₁
  have hcardJ' : J'.card = minIndexCard I' T.mult
      (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) := by
    have hc := hcand
    unfold IsCandidateComponent at hc
    exact hc.1
  have hcard2 : (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card + 1
      = J'.card :=
    card_preimageStrictTransformIndex_add_one_of_mem_consolidated389 π (monomialCenter T.ideal T.mult T.boundary) T.boundary J' hnew
  rw [hr] at hcardJ'
  omega

theorem maxOrderCandidatePairs_ncard_lt_of_blowup (_h' : minIndexCard I' T.mult
      (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) ≠ 0)
    (hr : minIndexCard I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
      = minIndexCard T.ideal T.mult T.boundary)
    (hv : maxCandidateOrder I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
      = maxCandidateOrder T.ideal T.mult T.boundary) :
    (maxOrderCandidatePairs I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)).ncard
      < (maxOrderCandidatePairs T.ideal T.mult T.boundary).ncard := by
  classical
  have : CharZero T.base := hT.valid.charZero
  have : Smooth q := hT'.valid.smooth
  have hfinD : (maxOrderCandidatePairs T.ideal T.mult T.boundary).Finite :=
    finite_maxOrderCandidatePairs hGeom hT
  have hbest := (lexMaxIndices_spec hGeom hT h).1
  unfold IsMaxOrderIndexSet at hbest
  obtain ⟨C₀, hcand₀, hord₀⟩ := hbest
  have hC₀opt : C₀ ∈ centerComponents T.ideal T.mult T.boundary :=
    (mem_centerComponents_iff T.ideal T.mult T.boundary C₀).2 ⟨hcand₀, hord₀⟩
  have hp₀ : (lexMaxIndices T.ideal T.mult T.boundary, C₀)
      ∈ maxOrderCandidatePairs T.ideal T.mult T.boundary :=
    (mem_maxOrderCandidatePairs_iff T.ideal T.mult T.boundary _).2 ⟨hcand₀, hord₀⟩
  have hπ' : Blowup.IsBlowupAlongIdealSheaf π (componentUnionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)
      (centerComponents T.ideal T.mult T.boundary)
      (isOpen_preimage_sUnion_centerComponents hGeom hT)) := by
    rw [← monomialCenter_eq_componentUnionIdeal hGeom hT h]
    exact hπ
  have htc := hGeom.transformed_components T hT.valid
    (lexMaxIndices T.ideal T.mult T.boundary)
    (centerComponents T.ideal T.mult T.boundary)
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary)
    (isOpen_preimage_sUnion_centerComponents hGeom hT) X' π hπ'
  rw [← monomialCenter_eq_componentUnionIdeal hGeom hT h] at htc
  have hkey : ∀ p ∈ maxOrderCandidatePairs I' T.mult
      (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary),
      ((preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1,
          closure (⇑π '' p.2)) ∈ maxOrderCandidatePairs T.ideal T.mult T.boundary) ∧
        closure (⇑π '' p.2) ∉ centerComponents T.ideal T.mult T.boundary ∧
        exceptionalIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary ∉ p.1 ∧
        p.2 = closure ((⇑π ⁻¹' closure (⇑π '' p.2)) \
          (↑(Blowup.exceptionalIdeal π (monomialCenter T.ideal T.mult T.boundary)).support :
            Set ↥X')) := by
    intro p hp
    obtain ⟨hcand, hordmax⟩ := (mem_maxOrderCandidatePairs_iff I' T.mult
      (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) p).1 hp
    have hnew := exceptionalIndex_not_mem_of_orderAlong_eq_maxCandidateOrder_consolidated389 hGeom hT h π q hπ I' hI' hT' hr hv
      hcand hordmax
    have hC'comp : p.2 ∈ intersectionComponents
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) p.1 := by
      have hc := hcand
      unfold IsCandidateComponent at hc
      tauto
    have hC'img : p.2 ∈ intersectionComponents
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
        ((preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1).image
          (strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)) := by
      rw [image_strictTransformIndex_preimageStrictTransformIndex_consolidated389 π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1
        hnew]
      exact hC'comp
    have hgen : IsGenericPoint (isIrreducible_of_mem_intersectionComponents hC'img).genericPoint p.2 :=
      isGenericPoint_genericPoint_of_mem_intersectionComponents hC'img
    obtain ⟨hoff, C, hC, hCnot, hC'eq, hlast⟩ :=
      htc (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1) p.2 hC'img _ hgen
    have hCirr : IsIrreducible C := isIrreducible_of_mem_intersectionComponents hC
    have hCcl : IsClosed C := isClosed_intersectionComponents_of_mem hC
    have hgpC : IsGenericPoint hCirr.genericPoint C :=
      isGenericPoint_genericPoint_of_mem_intersectionComponents hC
    have hπgp : π (isIrreducible_of_mem_intersectionComponents hC'img).genericPoint = hCirr.genericPoint :=
      hlast _ hgpC
    have hclim : closure (⇑π '' p.2) = C := by
      rw [closure_image_genericPoint (f := ⇑π) π.continuous hgen, hπgp, hgpC]
    have hSirr : IsIrreducible (⇑π '' p.2) :=
      (isIrreducible_of_mem_intersectionComponents hC'img).image _ π.continuous.continuousOn
    have hcl2 : closure (⇑π '' p.2) = closure C := by
      rw [hclim, hCcl.closure_eq]
    have hordeq : orderAlong I' p.2 = orderAlong T.ideal C := by
      have h1 := orderAlong_transform_eq_of_genericPoint_not_mem_exceptional hGeom hT h π hπ I' hI' hC'img hoff
      rw [h1]
      exact orderAlong_eq_of_closure_eq T.ideal hSirr hCirr hcl2
    have hordC : orderAlong T.ideal C = maxCandidateOrder T.ideal T.mult T.boundary := by
      rw [← hordeq, hordmax, hv]
    refine ⟨?_, ?_, hnew, ?_⟩
    · refine (mem_maxOrderCandidatePairs_iff T.ideal T.mult T.boundary _).2 ⟨?_, ?_⟩
      · unfold IsCandidateComponent
        refine ⟨?_, ?_, ?_⟩
        · rw [card_preimageStrictTransformIndex_of_not_mem_consolidated389 π (monomialCenter T.ideal T.mult T.boundary)
            T.boundary p.1 hnew]
          have hc := hcand
          unfold IsCandidateComponent at hc
          rw [hc.1]
          exact hr
        · rw [hclim]
          exact hC
        · rw [hclim, hordC]
          exact (maxCandidateOrder_spec hGeom hT h).2.2.1
      · rw [hclim, hordC]
    · rw [hclim]
      exact hCnot
    · rw [hclim]
      exact hC'eq
  have hinj : Set.InjOn
      (fun p : Finset (Fin (transformedBoundary π
          (monomialCenter T.ideal T.mult T.boundary) T.boundary).length) × Set ↥X' =>
        (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1,
          closure (⇑π '' p.2)))
      (maxOrderCandidatePairs I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)) := by
    intro p hp p' hp' heq
    obtain ⟨-, -, hnew1, hrep1⟩ := hkey p hp
    obtain ⟨-, -, hnew2, hrep2⟩ := hkey p' hp'
    have hJ : preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1
        = preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p'.1 :=
      congrArg Prod.fst heq
    have hC : closure (⇑π '' p.2) = closure (⇑π '' p'.2) := congrArg Prod.snd heq
    have hfst : p.1 = p'.1 := by
      rw [← image_strictTransformIndex_preimageStrictTransformIndex_consolidated389 π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1
          hnew1,
        ← image_strictTransformIndex_preimageStrictTransformIndex_consolidated389 π (monomialCenter T.ideal T.mult T.boundary) T.boundary p'.1
          hnew2,
        hJ]
    have hsnd : p.2 = p'.2 := by
      rw [hrep1, hC]
      exact hrep2.symm
    exact Prod.ext hfst hsnd
  have himg : (fun p : Finset (Fin (transformedBoundary π
        (monomialCenter T.ideal T.mult T.boundary) T.boundary).length) × Set ↥X' =>
      (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1,
        closure (⇑π '' p.2))) ''
      (maxOrderCandidatePairs I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))
      ⊆ maxOrderCandidatePairs T.ideal T.mult T.boundary := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hkey p hp).1
  have hnotin : (lexMaxIndices T.ideal T.mult T.boundary, C₀) ∉
      (fun p : Finset (Fin (transformedBoundary π
          (monomialCenter T.ideal T.mult T.boundary) T.boundary).length) × Set ↥X' =>
        (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1,
          closure (⇑π '' p.2))) ''
      (maxOrderCandidatePairs I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)) := by
    rintro ⟨p, hp, heq⟩
    have hsnd : closure (⇑π '' p.2) = C₀ := congrArg Prod.snd heq
    refine (hkey p hp).2.1 ?_
    rw [hsnd]
    exact hC₀opt
  have hss : (fun p : Finset (Fin (transformedBoundary π
        (monomialCenter T.ideal T.mult T.boundary) T.boundary).length) × Set ↥X' =>
      (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary p.1,
        closure (⇑π '' p.2))) ''
      (maxOrderCandidatePairs I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))
      ⊂ maxOrderCandidatePairs T.ideal T.mult T.boundary := by
    refine Set.ssubset_iff_subset_ne.2 ⟨himg, ?_⟩
    intro hEq
    apply hnotin
    rw [hEq]
    exact hp₀
  have hlt := Set.ncard_lt_ncard hss hfinD
  rwa [Set.InjOn.ncard_image hinj] at hlt


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
section



namespace MonomialCenter

structure OrderedMatchingOfNonTop {Y : Scheme.{u}} (L L' : List Y.IdealSheafData) where
  size : ℕ
  toFirst : Fin size → Fin L.length
  toSecond : Fin size → Fin L'.length
  strictMono_toFirst : StrictMono toFirst
  strictMono_toSecond : StrictMono toSecond
  get_eq : ∀ a : Fin size, L.get (toFirst a) = L'.get (toSecond a)
  exists_toFirst : ∀ i : Fin L.length, L.get i ≠ ⊤ → ∃ a : Fin size, toFirst a = i
  exists_toSecond : ∀ i : Fin L'.length, L'.get i ≠ ⊤ → ∃ a : Fin size, toSecond a = i

namespace OrderedMatchingOfNonTop

def symm {Y : Scheme.{u}} {L L' : List Y.IdealSheafData} (h : OrderedMatchingOfNonTop L L') :
    OrderedMatchingOfNonTop L' L where
  size := h.size
  toFirst := h.toSecond
  toSecond := h.toFirst
  strictMono_toFirst := h.strictMono_toSecond
  strictMono_toSecond := h.strictMono_toFirst
  get_eq := fun a => (h.get_eq a).symm
  exists_toFirst := h.exists_toSecond
  exists_toSecond := h.exists_toFirst

def preimage {Y : Scheme.{u}} {L L' : List Y.IdealSheafData} (h : OrderedMatchingOfNonTop L L')
    (J : Finset (Fin L.length)) : Finset (Fin h.size) :=
  Finset.filter (fun a => h.toFirst a ∈ J) Finset.univ

def transport {Y : Scheme.{u}} {L L' : List Y.IdealSheafData} (h : OrderedMatchingOfNonTop L L')
    (J : Finset (Fin L.length)) : Finset (Fin L'.length) :=
  Finset.image h.toSecond (h.preimage J)

section
variable {Y : Scheme.{u}} {L L' : List Y.IdealSheafData} (h : OrderedMatchingOfNonTop L L') (J : Finset (Fin L.length))

theorem mem_preimage (a : Fin h.size) :
    a ∈ h.preimage J ↔ h.toFirst a ∈ J := by
  constructor
  · intro ha
    exact (Finset.mem_filter.1 ha).2
  · intro ha
    exact Finset.mem_filter.2 ⟨Finset.mem_univ a, ha⟩

theorem mem_transport (i : Fin L'.length) :
    i ∈ h.transport J ↔ ∃ a : Fin h.size, h.toSecond a = i ∧ h.toFirst a ∈ J := by
  constructor
  · intro hi
    rcases Finset.mem_image.1 hi with ⟨a, ha, hai⟩
    exact ⟨a, hai, (h.mem_preimage J a).1 ha⟩
  · rintro ⟨a, hai, haJ⟩
    exact Finset.mem_image.2 ⟨a, (h.mem_preimage J a).2 haJ, hai⟩


end

end OrderedMatchingOfNonTop

private def orderedMatchingOfNonTopRefl_consolidated390 {Y : Scheme.{u}} (L : List Y.IdealSheafData) : OrderedMatchingOfNonTop L L where
  size := L.length
  toFirst := id
  toSecond := id
  strictMono_toFirst := strictMono_id
  strictMono_toSecond := strictMono_id
  get_eq := fun _ => rfl
  exists_toFirst := fun i _ => ⟨i, rfl⟩
  exists_toSecond := fun i _ => ⟨i, rfl⟩

private def orderedMatchingOfNonTopConsTopLeft_consolidated390 {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') : OrderedMatchingOfNonTop ((⊤ : Y.IdealSheafData) :: L) L' where
  size := rel.size
  toFirst := fun a => (rel.toFirst a).succ
  toSecond := rel.toSecond
  strictMono_toFirst := fun a b hab => Fin.succ_lt_succ_iff.2 (rel.strictMono_toFirst hab)
  strictMono_toSecond := rel.strictMono_toSecond
  get_eq := fun a => rel.get_eq a
  exists_toFirst := by
    intro i
    refine Fin.cases ?_ ?_ i
    · intro h0
      exact absurd rfl h0
    · intro j hj
      obtain ⟨a, ha⟩ := rel.exists_toFirst j hj
      exact ⟨a, by rw [ha]⟩
  exists_toSecond := rel.exists_toSecond

private def orderedMatchingOfNonTopConsTopRight_consolidated390 {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') : OrderedMatchingOfNonTop L ((⊤ : Y.IdealSheafData) :: L') :=
  (orderedMatchingOfNonTopConsTopLeft_consolidated390 rel.symm).symm

private def orderedMatchingOfNonTopCons_consolidated390 {Y : Scheme.{u}} {L L' : List Y.IdealSheafData} (D : Y.IdealSheafData)
    (rel : OrderedMatchingOfNonTop L L') : OrderedMatchingOfNonTop (D :: L) (D :: L') where
  size := rel.size + 1
  toFirst := Fin.cases 0 (fun b => (rel.toFirst b).succ)
  toSecond := Fin.cases 0 (fun b => (rel.toSecond b).succ)
  strictMono_toFirst := by
    intro a b hab
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩
    · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
      · exact absurd hab (lt_irrefl _)
      · simp only [Fin.cases_zero, Fin.cases_succ]
        exact Fin.succ_pos _
    · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
      · simp at hab
      · simp only [Fin.cases_succ]
        exact Fin.succ_lt_succ_iff.2 (rel.strictMono_toFirst (Fin.succ_lt_succ_iff.1 hab))
  strictMono_toSecond := by
    intro a b hab
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩
    · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
      · exact absurd hab (lt_irrefl _)
      · simp only [Fin.cases_zero, Fin.cases_succ]
        exact Fin.succ_pos _
    · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
      · simp at hab
      · simp only [Fin.cases_succ]
        exact Fin.succ_lt_succ_iff.2 (rel.strictMono_toSecond (Fin.succ_lt_succ_iff.1 hab))
  get_eq := by
    intro a
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩
    · rfl
    · simp only [Fin.cases_succ]
      exact rel.get_eq a'
  exists_toFirst := by
    intro i
    refine Fin.cases ?_ ?_ i
    · intro _
      exact ⟨0, rfl⟩
    · intro j hj
      obtain ⟨a, ha⟩ := rel.exists_toFirst j hj
      refine ⟨a.succ, ?_⟩
      simp only [Fin.cases_succ]
      rw [ha]
  exists_toSecond := by
    intro i
    refine Fin.cases ?_ ?_ i
    · intro _
      exact ⟨0, rfl⟩
    · intro j hj
      obtain ⟨a, ha⟩ := rel.exists_toSecond j hj
      refine ⟨a.succ, ?_⟩
      simp only [Fin.cases_succ]
      rw [ha]

section
variable {Y : Scheme.{u}}

private theorem nonempty_orderedMatchingOfNonTop_of_length_add_le_consolidated390 (n : ℕ) :
    ∀ L L' : List Y.IdealSheafData, L.length + L'.length ≤ n →
      MarkedIdealWithBoundary.nontrivialPart L = MarkedIdealWithBoundary.nontrivialPart L' →
      Nonempty (OrderedMatchingOfNonTop L L') := by
  induction n with
  | zero =>
      intro L L' hlen _
      cases L with
      | cons _ _ =>
          simp only [List.length_cons] at hlen
          omega
      | nil =>
          cases L' with
          | cons _ _ =>
              simp only [List.length_cons, List.length_nil] at hlen
              omega
          | nil => exact ⟨orderedMatchingOfNonTopRefl_consolidated390 []⟩
  | succ n ih =>
      intro L L' hlen hfil
      cases L with
      | nil =>
          cases L' with
          | nil => exact ⟨orderedMatchingOfNonTopRefl_consolidated390 []⟩
          | cons D' t' =>
              by_cases hD' : D' = ⊤
              · subst hD'
                have hlen' : ([] : List Y.IdealSheafData).length + t'.length ≤ n := by
                  simp only [List.length_nil, List.length_cons] at hlen ⊢
                  omega
                have hfil' : MarkedIdealWithBoundary.nontrivialPart ([] : List Y.IdealSheafData)
                    = MarkedIdealWithBoundary.nontrivialPart t' := by
                  simpa [MarkedIdealWithBoundary.nontrivialPart] using hfil
                obtain ⟨r⟩ := ih [] t' hlen' hfil'
                exact ⟨orderedMatchingOfNonTopConsTopRight_consolidated390 r⟩
              · exfalso
                simp [MarkedIdealWithBoundary.nontrivialPart, hD'] at hfil
      | cons D t =>
          by_cases hD : D = ⊤
          · subst hD
            have hlen' : t.length + L'.length ≤ n := by
              simp only [List.length_cons] at hlen
              omega
            have hfil' : MarkedIdealWithBoundary.nontrivialPart t = MarkedIdealWithBoundary.nontrivialPart L' := by
              simpa [MarkedIdealWithBoundary.nontrivialPart] using hfil
            obtain ⟨r⟩ := ih t L' hlen' hfil'
            exact ⟨orderedMatchingOfNonTopConsTopLeft_consolidated390 r⟩
          · cases L' with
            | nil =>
                exfalso
                simp [MarkedIdealWithBoundary.nontrivialPart, hD] at hfil
            | cons D' t' =>
                by_cases hD' : D' = ⊤
                · subst hD'
                  have hlen' : (D :: t).length + t'.length ≤ n := by
                    simp only [List.length_cons] at hlen ⊢
                    omega
                  have hfil' : MarkedIdealWithBoundary.nontrivialPart (D :: t)
                      = MarkedIdealWithBoundary.nontrivialPart t' := by
                    simpa [MarkedIdealWithBoundary.nontrivialPart, hD] using hfil
                  obtain ⟨r⟩ := ih (D :: t) t' hlen' hfil'
                  exact ⟨orderedMatchingOfNonTopConsTopRight_consolidated390 r⟩
                · have hcons : D = D' ∧ MarkedIdealWithBoundary.nontrivialPart t
                      = MarkedIdealWithBoundary.nontrivialPart t' := by
                    simpa [MarkedIdealWithBoundary.nontrivialPart, hD, hD'] using hfil
                  obtain ⟨rfl, hfil'⟩ := hcons
                  have hlen' : t.length + t'.length ≤ n := by
                    simp only [List.length_cons] at hlen
                    omega
                  obtain ⟨r⟩ := ih t t' hlen' hfil'
                  exact ⟨orderedMatchingOfNonTopCons_consolidated390 _ r⟩

theorem nonempty_orderedMatchingOfNonTop {L L' : List Y.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary L L') : Nonempty (OrderedMatchingOfNonTop L L') := by
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff] at h
  exact nonempty_orderedMatchingOfNonTop_of_length_add_le_consolidated390 (L.length + L'.length) L L' le_rfl h

theorem sameNontrivialBoundary_refl (L : List Y.IdealSheafData) :
    MarkedIdealWithBoundary.SameNontrivialBoundary L L :=
  MarkedIdealWithBoundary.SameNontrivialBoundary.refl L

theorem sameNontrivialBoundary_append {L₁ L₁' L₂ L₂' : List Y.IdealSheafData}
    (h₁ : MarkedIdealWithBoundary.SameNontrivialBoundary L₁ L₁') (h₂ : MarkedIdealWithBoundary.SameNontrivialBoundary L₂ L₂') :
    MarkedIdealWithBoundary.SameNontrivialBoundary (L₁ ++ L₂) (L₁' ++ L₂') :=
  h₁.append h₂

private theorem support_top_eq_empty_consolidated390 :
    (↑(⊤ : Y.IdealSheafData).support : Set ↥Y) = ∅ :=
  (AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty
    (⊤ : Y.IdealSheafData)).1 rfl

private theorem intersectionIdeal_eq_top_consolidated390 (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) {j : Fin L.length} (hj : j ∈ J) (hg : L.get j = ⊤) :
    intersectionIdeal L J = ⊤ := by
  rw [intersectionIdeal_eq_iSup]
  refine top_le_iff.mp ?_
  have h2 : L.get j ≤ ⨆ j' ∈ J, L.get j' :=
    le_iSup₂ (f := fun (j' : Fin L.length) (_ : j' ∈ J) => L.get j') j hj
  rw [hg] at h2
  exact h2

private theorem get_ne_top_of_mem_intersectionComponents_consolidated390 {L : List Y.IdealSheafData}
    {J : Finset (Fin L.length)} {C : Set ↥Y} (hC : C ∈ intersectionComponents L J) :
    ∀ j ∈ J, L.get j ≠ ⊤ := by
  intro j hj hg
  have h1 : intersectionIdeal L J = ⊤ := intersectionIdeal_eq_top_consolidated390 L J hj hg
  have h2 : C ⊆ (↑(intersectionIdeal L J).support : Set ↥Y) := by
    simp only [intersectionComponents, Set.mem_ofPred_eq] at hC
    exact hC.2.1
  rw [h1, support_top_eq_empty_consolidated390] at h2
  exact (isIrreducible_of_mem_intersectionComponents hC).1.ne_empty (Set.subset_empty_iff.1 h2)

private theorem intersectionComponents_congr_consolidated390 {L L' : List Y.IdealSheafData}
    (J : Finset (Fin L.length)) (J' : Finset (Fin L'.length))
    (hEq : intersectionIdeal L J = intersectionIdeal L' J') : intersectionComponents L J = intersectionComponents L' J' := by
  unfold intersectionComponents
  rw [hEq]


end

section
variable {Y : Scheme.{u}} {L L' : List Y.IdealSheafData} (rel : OrderedMatchingOfNonTop L L') (J : Finset (Fin L.length)) (hgood : ∀ j ∈ J, L.get j ≠ ⊤)
include hgood

private theorem intersectionIdeal_transport_consolidated390 :
    intersectionIdeal L J = intersectionIdeal L' (rel.transport J) := by
  rw [intersectionIdeal_eq_iSup, intersectionIdeal_eq_iSup]
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    obtain ⟨a, ha⟩ := rel.exists_toFirst j (hgood j hj)
    have hmem : rel.toSecond a ∈ rel.transport J :=
      (rel.mem_transport J _).2 ⟨a, rfl, by rw [ha]; exact hj⟩
    have h1 : L.get j = L'.get (rel.toSecond a) := by
      rw [← ha]; exact rel.get_eq a
    rw [h1]
    exact le_iSup₂ (f := fun (i : Fin L'.length) (_ : i ∈ rel.transport J) => L'.get i)
      (rel.toSecond a) hmem
  · refine iSup₂_le fun i hi => ?_
    obtain ⟨a, hai, haJ⟩ := (rel.mem_transport J i).1 hi
    have h1 : L'.get i = L.get (rel.toFirst a) := by
      rw [← hai]; exact (rel.get_eq a).symm
    rw [h1]
    exact le_iSup₂ (f := fun (j : Fin L.length) (_ : j ∈ J) => L.get j) (rel.toFirst a) haJ

private theorem image_toFirst_preimage_consolidated390 :
    Finset.image rel.toFirst (rel.preimage J) = J := by
  ext j
  constructor
  · intro hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hj
    exact (rel.mem_preimage J a).1 ha
  · intro hj
    obtain ⟨a, ha⟩ := rel.exists_toFirst j (hgood j hj)
    refine Finset.mem_image.2 ⟨a, ?_, ha⟩
    exact (rel.mem_preimage J a).2 (by rw [ha]; exact hj)

private theorem card_transport_consolidated390 :
    (rel.transport J).card = J.card := by
  have h1 : (rel.transport J).card = (rel.preimage J).card :=
    Finset.card_image_of_injective _ rel.strictMono_toSecond.injective
  have h2 : (Finset.image rel.toFirst (rel.preimage J)).card = (rel.preimage J).card :=
    Finset.card_image_of_injective _ rel.strictMono_toFirst.injective
  rw [image_toFirst_preimage_consolidated390 rel J hgood] at h2
  rw [h1, ← h2]


end

section
variable {Y : Scheme.{u}} {L L' : List Y.IdealSheafData} (rel : OrderedMatchingOfNonTop L L')
include rel

private theorem isCandidateComponent_transport_consolidated390 {I : Y.IdealSheafData} {m r : ℕ} {J : Finset (Fin L.length)}
    {C : Set ↥Y} (hc : IsCandidateComponent I m L r J C) : IsCandidateComponent I m L' r (rel.transport J) C := by
  unfold IsCandidateComponent at hc ⊢
  obtain ⟨hcard, hC, horder⟩ := hc
  have hgood : ∀ j ∈ J, L.get j ≠ ⊤ := get_ne_top_of_mem_intersectionComponents_consolidated390 hC
  refine ⟨?_, ?_, horder⟩
  · rw [card_transport_consolidated390 rel J hgood]
    exact hcard
  · rw [← intersectionComponents_congr_consolidated390 J (rel.transport J) (intersectionIdeal_transport_consolidated390 rel J hgood)]
    exact hC

private theorem minIndexCard_eq_of_orderedMatchingOfNonTop_consolidated390 (I : Y.IdealSheafData) (m : ℕ) :
    minIndexCard I m L = minIndexCard I m L' := by
  have hsets : {r : ℕ | 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
        IsCandidateComponent I m L r J C}
      = {r : ℕ | 1 ≤ r ∧ ∃ (J : Finset (Fin L'.length)) (C : Set ↥Y),
        IsCandidateComponent I m L' r J C} := by
    ext r
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hr, J, C, hc⟩
      exact ⟨hr, rel.transport J, C, isCandidateComponent_transport_consolidated390 rel hc⟩
    · rintro ⟨hr, J, C, hc⟩
      exact ⟨hr, rel.symm.transport J, C, isCandidateComponent_transport_consolidated390 rel.symm hc⟩
  unfold minIndexCard
  exact congrArg sInf hsets

private theorem iSup_orderAlong_le_of_orderedMatchingOfNonTop_consolidated390 (I : Y.IdealSheafData) (m r : ℕ) :
    (⨆ (J : Finset (Fin L.length)) (C : Set ↥Y) (_ : IsCandidateComponent I m L r J C), orderAlong I C) ≤
      ⨆ (J : Finset (Fin L'.length)) (C : Set ↥Y) (_ : IsCandidateComponent I m L' r J C),
        orderAlong I C := by
  refine iSup_le fun J => iSup_le fun C => iSup_le fun hc => ?_
  exact le_iSup_of_le (rel.transport J)
    (le_iSup_of_le C (le_iSup_of_le (isCandidateComponent_transport_consolidated390 rel hc) le_rfl))

private theorem maxCandidateOrder_eq_of_orderedMatchingOfNonTop_consolidated390 (I : Y.IdealSheafData) (m : ℕ) :
    maxCandidateOrder I m L = maxCandidateOrder I m L' := by
  have hmin : minIndexCard I m L = minIndexCard I m L' := minIndexCard_eq_of_orderedMatchingOfNonTop_consolidated390 rel I m
  unfold maxCandidateOrder
  rw [hmin]
  exact le_antisymm (iSup_orderAlong_le_of_orderedMatchingOfNonTop_consolidated390 rel I m _) (iSup_orderAlong_le_of_orderedMatchingOfNonTop_consolidated390 rel.symm I m _)


end

section
variable {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) {J : Finset (Fin L.length)} (hJ : IsMaxOrderIndexSet I m L J)
include hJ

private theorem get_ne_top_of_isMaxOrderIndexSet_consolidated390 :
    ∀ j ∈ J, L.get j ≠ ⊤ := by
  unfold IsMaxOrderIndexSet at hJ
  obtain ⟨C, hc, -⟩ := hJ
  unfold IsCandidateComponent at hc
  exact get_ne_top_of_mem_intersectionComponents_consolidated390 hc.2.1

private theorem card_eq_minIndexCard_of_isMaxOrderIndexSet_consolidated390 :
    J.card = minIndexCard I m L := by
  unfold IsMaxOrderIndexSet at hJ
  obtain ⟨C, hc, -⟩ := hJ
  unfold IsCandidateComponent at hc
  exact hc.1


end

private theorem isMaxOrderIndexSet_transport_consolidated390 {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') (I : Y.IdealSheafData) (m : ℕ) {J : Finset (Fin L.length)}
    (hJ : IsMaxOrderIndexSet I m L J) : IsMaxOrderIndexSet I m L' (rel.transport J) := by
  unfold IsMaxOrderIndexSet at hJ ⊢
  obtain ⟨C, hc, hord⟩ := hJ
  refine ⟨C, ?_, ?_⟩
  · rw [← minIndexCard_eq_of_orderedMatchingOfNonTop_consolidated390 rel I m]
    exact isCandidateComponent_transport_consolidated390 rel hc
  · rw [hord]
    exact maxCandidateOrder_eq_of_orderedMatchingOfNonTop_consolidated390 rel I m

section
variable {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData)

private theorem isMaxOrderIndexSet_lexMaxIndices_consolidated390 (hex : ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J) :
    IsMaxOrderIndexSet I m L (lexMaxIndices I m L) ∧
      ∀ K : Finset (Fin L.length), IsMaxOrderIndexSet I m L K →
        binaryEncode K ≤ binaryEncode (lexMaxIndices I m L) := by
  have hne : ({c : ℕ | ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J ∧
      binaryEncode J = c}).Nonempty := by
    obtain ⟨J, hJ⟩ := hex
    exact ⟨binaryEncode J, J, hJ, rfl⟩
  have hbdd : BddAbove {c : ℕ | ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J ∧
      binaryEncode J = c} := by
    refine ⟨∑ j : Fin L.length, 2 ^ (L.length - 1 - (j : ℕ)), ?_⟩
    rintro c ⟨J, -, rfl⟩
    unfold binaryEncode
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ J)
  have hmem : maxBinaryCode I m L ∈ {c : ℕ | ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J ∧
      binaryEncode J = c} := by
    unfold maxBinaryCode
    exact Nat.sSup_mem hne hbdd
  obtain ⟨J₀, hJ₀, hcode⟩ := hmem
  have hdite : ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J ∧ binaryEncode J = maxBinaryCode I m L :=
    ⟨J₀, hJ₀, hcode⟩
  have hch : lexMaxIndices I m L = hdite.choose := by
    unfold lexMaxIndices
    exact dif_pos hdite
  have hspec := hdite.choose_spec
  rw [← hch] at hspec
  refine ⟨hspec.1, fun K hK => ?_⟩
  rw [hspec.2]
  unfold maxBinaryCode
  exact le_csSup hbdd ⟨K, hK, rfl⟩

private theorem lexMaxIndices_eq_empty_consolidated390 (hex : ¬ ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J) :
    lexMaxIndices I m L = ∅ := by
  have hno : ¬ ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J ∧ binaryEncode J = maxBinaryCode I m L := by
    rintro ⟨J, hJ, -⟩
    exact hex ⟨J, hJ⟩
  unfold lexMaxIndices
  exact dif_neg hno

private theorem lexMaxIndices_eq_of_binaryEncode_le_consolidated390 {J : Finset (Fin L.length)} (hJ : IsMaxOrderIndexSet I m L J)
    (hmax : ∀ K : Finset (Fin L.length), IsMaxOrderIndexSet I m L K → binaryEncode K ≤ binaryEncode J) :
    lexMaxIndices I m L = J := by
  obtain ⟨hb, hub⟩ := isMaxOrderIndexSet_lexMaxIndices_consolidated390 I m L ⟨J, hJ⟩
  have h1 : binaryEncode (lexMaxIndices I m L) = binaryEncode J :=
    le_antisymm (hmax _ hb) (hub J hJ)
  exact binaryEncode_injective h1

private theorem get_ne_top_of_mem_lexMaxIndices_consolidated390 : ∀ j ∈ lexMaxIndices I m L, L.get j ≠ ⊤ := by
  by_cases hex : ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J
  · exact get_ne_top_of_isMaxOrderIndexSet_consolidated390 I m L (isMaxOrderIndexSet_lexMaxIndices_consolidated390 I m L hex).1
  · rw [lexMaxIndices_eq_empty_consolidated390 I m L hex]
    intro j hj
    exact absurd hj (by simp)


end

section
variable {Y : Scheme.{u}} {L L' : List Y.IdealSheafData} (rel : OrderedMatchingOfNonTop L L')
include rel

private theorem binaryEncode_transport_lt_iff_consolidated390 (J K : Finset (Fin L.length))
    (hJ : ∀ j ∈ J, L.get j ≠ ⊤) (hK : ∀ j ∈ K, L.get j ≠ ⊤) (hcard : J.card = K.card) :
    binaryEncode (rel.transport K) < binaryEncode (rel.transport J) ↔
      binaryEncode K < binaryEncode J := by
  have hcardT : (rel.transport J).card = (rel.transport K).card := by
    rw [card_transport_consolidated390 rel J hJ, card_transport_consolidated390 rel K hK]
    exact hcard
  have e1 := binaryEncode_lt_iff_lex_of_card_eq (rel.transport J) (rel.transport K) hcardT
  have e2 := binaryEncode_lt_iff_lex_of_card_eq J K hcard
  have htJ : rel.transport J = Finset.image rel.toSecond (rel.preimage J) := rfl
  have htK : rel.transport K = Finset.image rel.toSecond (rel.preimage K) := rfl
  have hA := lex_sortedIndices_image_iff rel.toSecond rel.strictMono_toSecond
    (rel.preimage J) (rel.preimage K)
  have hB := lex_sortedIndices_image_iff rel.toFirst rel.strictMono_toFirst
    (rel.preimage J) (rel.preimage K)
  rw [image_toFirst_preimage_consolidated390 rel J hJ, image_toFirst_preimage_consolidated390 rel K hK] at hB
  rw [e1, e2, htJ, htK, hA, hB]

private theorem transport_symm_transport_consolidated390 (K : Finset (Fin L'.length)) (hK : ∀ i ∈ K, L'.get i ≠ ⊤) :
    rel.transport (rel.symm.transport K) = K := by
  ext i
  constructor
  · intro hi
    obtain ⟨a, hai, haK⟩ := (rel.mem_transport _ i).1 hi
    obtain ⟨b, hb1, hb2⟩ := (OrderedMatchingOfNonTop.mem_transport rel.symm K (rel.toFirst a)).1 haK
    have hba : b = a := rel.strictMono_toFirst.injective hb1
    subst hba
    rw [← hai]
    exact hb2
  · intro hi
    obtain ⟨a, ha⟩ := rel.exists_toSecond i (hK i hi)
    refine (rel.mem_transport _ i).2 ⟨a, ha, ?_⟩
    refine (OrderedMatchingOfNonTop.mem_transport rel.symm K (rel.toFirst a)).2 ⟨a, rfl, ?_⟩
    show rel.toSecond a ∈ K
    rw [ha]
    exact hi

private theorem lexMaxIndices_transport_consolidated390 (I : Y.IdealSheafData) (m : ℕ) :
    lexMaxIndices I m L' = rel.transport (lexMaxIndices I m L) := by
  by_cases hex : ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J
  · obtain ⟨hbest, hub⟩ := isMaxOrderIndexSet_lexMaxIndices_consolidated390 I m L hex
    refine lexMaxIndices_eq_of_binaryEncode_le_consolidated390 I m L' (isMaxOrderIndexSet_transport_consolidated390 rel I m hbest) ?_
    intro K hK
    have hK0 : IsMaxOrderIndexSet I m L (rel.symm.transport K) := isMaxOrderIndexSet_transport_consolidated390 rel.symm I m hK
    have hKeq : rel.transport (rel.symm.transport K) = K :=
      transport_symm_transport_consolidated390 rel K (get_ne_top_of_isMaxOrderIndexSet_consolidated390 I m L' hK)
    have hcard : (rel.symm.transport K).card = (lexMaxIndices I m L).card := by
      rw [card_eq_minIndexCard_of_isMaxOrderIndexSet_consolidated390 I m L hK0, card_eq_minIndexCard_of_isMaxOrderIndexSet_consolidated390 I m L hbest]
    have hlt := binaryEncode_transport_lt_iff_consolidated390 rel (rel.symm.transport K) (lexMaxIndices I m L)
      (get_ne_top_of_isMaxOrderIndexSet_consolidated390 I m L hK0) (get_ne_top_of_isMaxOrderIndexSet_consolidated390 I m L hbest) hcard
    have hnot : ¬ (binaryEncode (lexMaxIndices I m L) < binaryEncode (rel.symm.transport K)) :=
      not_lt.2 (hub _ hK0)
    have hnot2 : ¬ (binaryEncode (rel.transport (lexMaxIndices I m L)) <
        binaryEncode (rel.transport (rel.symm.transport K))) := fun hc => hnot (hlt.1 hc)
    rw [hKeq] at hnot2
    exact not_lt.1 hnot2
  · have hex' : ¬ ∃ J : Finset (Fin L'.length), IsMaxOrderIndexSet I m L' J := by
      rintro ⟨J, hJ⟩
      exact hex ⟨rel.symm.transport J, isMaxOrderIndexSet_transport_consolidated390 rel.symm I m hJ⟩
    rw [lexMaxIndices_eq_empty_consolidated390 I m L' hex', lexMaxIndices_eq_empty_consolidated390 I m L hex]
    symm
    ext i
    constructor
    · intro hi
      obtain ⟨a, -, ha⟩ := (rel.mem_transport _ i).1 hi
      exact absurd ha (by simp)
    · intro hi
      exact absurd hi (by simp)

private theorem monomialCenterSet_eq_of_orderedMatchingOfNonTop_consolidated390 (I : Y.IdealSheafData) (m : ℕ) :
    monomialCenterSet I m L = monomialCenterSet I m L' := by
  have hmin := minIndexCard_eq_of_orderedMatchingOfNonTop_consolidated390 rel I m
  have hmax := maxCandidateOrder_eq_of_orderedMatchingOfNonTop_consolidated390 rel I m
  have hch := lexMaxIndices_transport_consolidated390 rel I m
  have hgood := get_ne_top_of_mem_lexMaxIndices_consolidated390 I m L
  have hback : rel.symm.transport (rel.transport (lexMaxIndices I m L)) = lexMaxIndices I m L :=
    transport_symm_transport_consolidated390 rel.symm (lexMaxIndices I m L) hgood
  have hsets : {C : Set ↥Y | IsCandidateComponent I m L (minIndexCard I m L) (lexMaxIndices I m L) C ∧
        orderAlong I C = maxCandidateOrder I m L}
      = {C : Set ↥Y | IsCandidateComponent I m L' (minIndexCard I m L') (lexMaxIndices I m L') C ∧
        orderAlong I C = maxCandidateOrder I m L'} := by
    ext C
    simp only [Set.mem_ofPred_eq]
    rw [hch, ← hmin, ← hmax]
    constructor
    · rintro ⟨hc, hord⟩
      exact ⟨isCandidateComponent_transport_consolidated390 rel hc, hord⟩
    · rintro ⟨hc, hord⟩
      refine ⟨?_, hord⟩
      have h2 := isCandidateComponent_transport_consolidated390 rel.symm hc
      rwa [hback] at h2
  unfold monomialCenterSet
  exact congrArg Set.sUnion hsets


end

section
variable {Y : Scheme.{u}}

private theorem openSublocusIdeal_congr_consolidated390 {M M' : Y.IdealSheafData} {S S' : Set ↥Y}
    (hM : M = M') (hS : S = S')
    (h : IsOpen (⇑M.subschemeι ⁻¹' S)) (h' : IsOpen (⇑M'.subschemeι ⁻¹' S')) :
    openSublocusIdeal M.subschemeι (⇑M.subschemeι ⁻¹' S) h
      = openSublocusIdeal M'.subschemeι (⇑M'.subschemeι ⁻¹' S') h' := by
  subst hM
  subst hS
  rfl

private theorem monomialCenter_eq_of_orderedMatchingOfNonTop_consolidated390 {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') (I : Y.IdealSheafData) (m : ℕ) :
    monomialCenter I m L = monomialCenter I m L' := by
  have hmin := minIndexCard_eq_of_orderedMatchingOfNonTop_consolidated390 rel I m
  have hcen := monomialCenterSet_eq_of_orderedMatchingOfNonTop_consolidated390 rel I m
  have hint : intersectionIdeal L (lexMaxIndices I m L) = intersectionIdeal L' (lexMaxIndices I m L') := by
    rw [lexMaxIndices_transport_consolidated390 rel I m]
    exact intersectionIdeal_transport_consolidated390 rel (lexMaxIndices I m L) (get_ne_top_of_mem_lexMaxIndices_consolidated390 I m L)
  have hiff : (minIndexCard I m L ≠ 0 ∧
        IsOpen (⇑(intersectionIdeal L (lexMaxIndices I m L)).subschemeι ⁻¹' monomialCenterSet I m L))
      ↔ (minIndexCard I m L' ≠ 0 ∧
        IsOpen (⇑(intersectionIdeal L' (lexMaxIndices I m L')).subschemeι ⁻¹' monomialCenterSet I m L')) := by
    rw [hmin, hint, hcen]
  unfold monomialCenter
  by_cases hc : minIndexCard I m L ≠ 0 ∧
      IsOpen (⇑(intersectionIdeal L (lexMaxIndices I m L)).subschemeι ⁻¹' monomialCenterSet I m L)
  · rw [dif_pos hc, dif_pos (hiff.1 hc)]
    exact openSublocusIdeal_congr_consolidated390 hint hcen _ _
  · rw [dif_neg hc, dif_neg (fun hx => hc (hiff.2 hx))]


end

section
variable {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ) {L L' : List Y.IdealSheafData} (h : MarkedIdealWithBoundary.SameNontrivialBoundary L L')
include h

theorem minIndexCard_eq_of_sameNontrivialBoundary :
    minIndexCard I m L = minIndexCard I m L' := by
  obtain ⟨rel⟩ := nonempty_orderedMatchingOfNonTop h
  exact minIndexCard_eq_of_orderedMatchingOfNonTop_consolidated390 rel I m

theorem monomialCenter_eq_of_sameNontrivialBoundary :
    monomialCenter I m L = monomialCenter I m L' := by
  obtain ⟨rel⟩ := nonempty_orderedMatchingOfNonTop h
  exact monomialCenter_eq_of_orderedMatchingOfNonTop_consolidated390 rel I m


end

end MonomialCenter

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.ComponentUnionIdeal
section


section

namespace MonomialCenterGeometry

section
variable (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme)) (h𝒞 : 𝒞 ⊆ intersectionComponents T.boundary J)
include hT h𝒞

theorem isClosed_sUnion_intersectionComponents :
    IsClosed (⋃₀ 𝒞) := by
  classical
  have hfin : 𝒞.Finite := Set.Finite.subset (intersectionComponents_finite T hT J) h𝒞
  rw [Set.sUnion_eq_biUnion]
  exact hfin.isClosed_biUnion
    (fun C hC => isClosed_of_mem_intersectionComponents T.boundary J C (h𝒞 hC))

theorem isClosed_componentUnionOpens (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    IsClosed ((componentUnionOpens T.boundary J 𝒞 hop : Set ↥(intersectionIdeal T.boundary J).subscheme)) := by
  have hK : IsClosed (⋃₀ 𝒞) := isClosed_sUnion_intersectionComponents T hT J 𝒞 h𝒞
  have h1 : IsOpen ((⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)ᶜ) := by
    rw [← Set.preimage_compl]
    exact ((intersectionIdeal T.boundary J).subschemeι ⁻¹ᵁ ⟨(⋃₀ 𝒞)ᶜ, hK.isOpen_compl⟩).isOpen
  exact isOpen_compl_iff.mp h1


end

theorem componentUnionIdeal_eq_openSubschemeKer (T : MarkedIdealWithBoundary.{u})
    (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme))
    (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    componentUnionIdeal T.boundary J 𝒞 hop
      = openSubschemeKer (intersectionIdeal T.boundary J) (componentUnionOpens T.boundary J 𝒞 hop) := by
  rw [componentUnionIdeal_eq_ker, openSubschemeKer_eq_ker]

theorem smooth_componentUnionIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)),
      ∀ 𝒞 ⊆ intersectionComponents T.boundary J,
        ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)),
          Smooth
            ((componentUnionIdeal T.boundary J 𝒞 hop).subschemeι ≫ T.structMap) := by
  intro T hT J 𝒞 h𝒞 hop
  have hsm : Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap) :=
    MonomialChart.smooth_intersectionIdeal_subscheme T hT J
  rw [componentUnionIdeal_eq_openSubschemeKer T J 𝒞 hop]
  exact smooth_subschemeι_openSubschemeKer_comp (intersectionIdeal T.boundary J)
    (componentUnionOpens T.boundary J 𝒞 hop)
    (isClosed_componentUnionOpens T hT J 𝒞 h𝒞 hop) T.structMap

theorem hasStrictNormalCrossingsWith_componentUnionIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)),
      ∀ 𝒞 ⊆ intersectionComponents T.boundary J,
        ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)),
          HasStrictNormalCrossingsWith T.structMap (componentUnionIdeal T.boundary J 𝒞 hop) T.boundary := by
  classical
  intro T hT J 𝒞 h𝒞 hop
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  have hWcl : IsClosed
      ((componentUnionOpens T.boundary J 𝒞 hop : Set ↥(intersectionIdeal T.boundary J).subscheme)) :=
    isClosed_componentUnionOpens T hT J 𝒞 h𝒞 hop
  have hce : componentUnionIdeal T.boundary J 𝒞 hop
      = openSubschemeKer (intersectionIdeal T.boundary J) (componentUnionOpens T.boundary J 𝒞 hop) :=
    componentUnionIdeal_eq_openSubschemeKer T J 𝒞 hop
  have hximg : x ∈ ⇑(intersectionIdeal T.boundary J).subschemeι.base ''
      ((componentUnionOpens T.boundary J 𝒞 hop : Set ↥(intersectionIdeal T.boundary J).subscheme)) := by
    rw [← support_openSubschemeKer (intersectionIdeal T.boundary J)
      (componentUnionOpens T.boundary J 𝒞 hop) hWcl, ← hce]
    exact hx
  obtain ⟨U₁, hxU₁, hU₁⟩ := exists_opens_preimage_subschemeι_le (intersectionIdeal T.boundary J)
    (componentUnionOpens T.boundary J 𝒞 hop) x hximg
  obtain ⟨U₀, hxU₀, m, c₀, a, ha1, ha2, ha3⟩ :=
    (((inStrictNormalCrossingPosition_iff T.structMap T.boundary).mp hT.snc).2 x).exists_etaleChart
  have hxV : x ∈ U₀ ⊓ U₁ := ⟨hxU₀, hxU₁⟩
  have hxsupp : x ∈ ((intersectionIdeal T.boundary J).support : Set ↥T.scheme) := by
    have hxs : x ∈ ⋃₀ 𝒞 := by
      rw [← componentUnionIdeal_support_eq_sUnion T hT J 𝒞 h𝒞 hop]
      exact hx
    obtain ⟨C, hC, hxC⟩ := hxs
    exact (h𝒞 hC).2.1 hxC
  have hbs : restrictIdeal (intersectionIdeal T.boundary J) (U₀ ⊓ U₁)
      = ⨆ j ∈ J, restrictIdeal (T.boundary.get j) (U₀ ⊓ U₁) :=
    MonomialChart.restrictIdeal_biSup_finset (U₀ ⊓ U₁) (fun j => T.boundary.get j) J
  have h4 : restrictIdeal (componentUnionIdeal T.boundary J 𝒞 hop) (U₀ ⊓ U₁)
      = restrictIdeal (intersectionIdeal T.boundary J) (U₀ ⊓ U₁) := by
    rw [hce]
    exact restrictIdeal_openSubschemeKer_of_preimage_le (intersectionIdeal T.boundary J)
      (componentUnionOpens T.boundary J 𝒞 hop) hWcl (U₀ ⊓ U₁)
      (le_trans (Scheme.Hom.preimage_mono _ inf_le_right) hU₁)
  have hJsome : ∀ j ∈ J, ∃ t : Fin m, a (j : ℕ) = some t := by
    intro j hj
    by_cases hn : a (j : ℕ) = none
    · exfalso
      have htop : restrictIdeal (T.boundary.get j) (U₀ ⊓ U₁) = ⊤ :=
        restrictIdeal_eq_top_of_le (T.boundary.get j) inf_le_left
          (ha2 (j : ℕ) j.isLt hn)
      have hle : restrictIdeal (T.boundary.get j) (U₀ ⊓ U₁)
          ≤ ⨆ i ∈ J, restrictIdeal (T.boundary.get i) (U₀ ⊓ U₁) :=
        le_iSup₂ (f := fun (i : Fin T.boundary.length) (_ : i ∈ J) =>
          restrictIdeal (T.boundary.get i) (U₀ ⊓ U₁)) j hj
      rw [htop] at hle
      have htop' : restrictIdeal (intersectionIdeal T.boundary J) (U₀ ⊓ U₁) = ⊤ :=
        hbs.trans (top_le_iff.mp hle)
      exact Scheme.IdealSheafData.notMem_support_of_comap_ι_eq_top (intersectionIdeal T.boundary J)
        htop' hxV hxsupp
    · exact Option.ne_none_iff_exists'.mp hn
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin m), ∀ t : Fin m, t ∈ S ↔ ∃ j ∈ J, a (j : ℕ) = some t :=
    ⟨Finset.univ.filter (fun t => ∃ j ∈ J, a (j : ℕ) = some t), by intro t; simp⟩
  have key : ∀ j ∈ J, ∃ t : Fin m, t ∈ S ∧
      restrictIdeal (T.boundary.get j) (U₀ ⊓ U₁)
        = (c₀.restrict (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).coordIdeal {t} := by
    intro j hj
    obtain ⟨t, hat⟩ := hJsome j hj
    exact ⟨t, (hS t).mpr ⟨j, hj, hat⟩,
      restrictIdeal_eq_restrict_coordIdeal_of_le inf_le_left c₀ (T.boundary.get j) {t}
        (ha3 (j : ℕ) j.isLt t hat)⟩
  have key2 : ∀ t ∈ S, ∃ j ∈ J,
      (c₀.restrict (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).coordIdeal {t}
        = restrictIdeal (T.boundary.get j) (U₀ ⊓ U₁) := by
    intro t ht
    obtain ⟨j, hj, hat⟩ := (hS t).mp ht
    exact ⟨j, hj, (restrictIdeal_eq_restrict_coordIdeal_of_le inf_le_left c₀ (T.boundary.get j) {t}
      (ha3 (j : ℕ) j.isLt t hat)).symm⟩
  refine ⟨U₀ ⊓ U₁, hxV, m, c₀.restrict (inf_le_left : U₀ ⊓ U₁ ≤ U₀), a, S, ha1, ?_, ?_, ?_⟩
  · intro i hi hin
    exact restrictIdeal_eq_top_of_le _ inf_le_left (ha2 i hi hin)
  · intro i hi t hit
    exact restrictIdeal_eq_restrict_coordIdeal_of_le inf_le_left c₀ _ {t} (ha3 i hi t hit)
  · rw [h4, hbs, MonomialChart.coordIdeal_eq_biSup_singleton T.structMap (U₀ ⊓ U₁) m
      (c₀.restrict (inf_le_left : U₀ ⊓ U₁ ≤ U₀)) S]
    refine le_antisymm (iSup₂_le ?_) (iSup₂_le ?_)
    · intro j hj
      obtain ⟨t, htS, heq⟩ := key j hj
      rw [heq]
      exact le_iSup₂ (f := fun (t : Fin m) (_ : t ∈ S) =>
        (c₀.restrict (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).coordIdeal {t}) t htS
    · intro t ht
      obtain ⟨j, hj, heq⟩ := key2 t ht
      rw [heq]
      exact le_iSup₂ (f := fun (j : Fin T.boundary.length) (_ : j ∈ J) =>
        restrictIdeal (T.boundary.get j) (U₀ ⊓ U₁)) j hj

end MonomialCenterGeometry


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenterSmoothPullback
section


section

namespace MonomialCenter

def pullbackIndex (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) :
    Fin T.boundary.length → Fin (T.pullbackOverField Y k' q g).boundary.length :=
  pullbackOverFieldIndex T Y k' q g

@[simp]
theorem pullbackIndex_val (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) (j : Fin T.boundary.length) :
    ((pullbackIndex T Y k' q g j : Fin (T.pullbackOverField Y k' q g).boundary.length) : ℕ) = (j : ℕ) :=
  pullbackOverFieldIndex_val T Y k' q g j

def pullbackIndexSymm (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) :
    Fin (T.pullbackOverField Y k' q g).boundary.length → Fin T.boundary.length :=
  Fin.cast (MarkedIdealWithBoundary.pullbackOverField_boundary_length T Y k' q g)

@[simp]
theorem pullbackIndexSymm_val (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (j : Fin (T.pullbackOverField Y k' q g).boundary.length) :
    ((pullbackIndexSymm T Y k' q g j : Fin T.boundary.length) : ℕ) = (j : ℕ) :=
  rfl

@[simp]
theorem pullbackIndex_pullbackIndexSymm (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (j : Fin (T.pullbackOverField Y k' q g).boundary.length) :
    pullbackIndex T Y k' q g (pullbackIndexSymm T Y k' q g j) = j := by
  apply Fin.val_injective
  rw [pullbackIndex_val, pullbackIndexSymm_val]

def pullbackAlongIndex (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (g : Y ⟶ T.scheme) :
    Fin T.boundary.length → Fin (T.pullbackAlong Y q g).boundary.length :=
  EmbeddedResolution.pullbackAlongIndex T Y q g

@[simp]
theorem pullbackAlongIndex_val (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (g : Y ⟶ T.scheme) (j : Fin T.boundary.length) :
    ((pullbackAlongIndex T Y q g j : Fin (T.pullbackAlong Y q g).boundary.length) : ℕ) = (j : ℕ) :=
  EmbeddedResolution.pullbackAlongIndex_val T Y q g j

structure IsComponentCompatiblePullback (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) : Prop where
  comapCenter : ∀ (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme)),
    𝒞 ⊆ intersectionComponents T.boundary J →
    ∀ hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞),
      ∃ hop' : IsOpen (⇑(intersectionIdeal (T.pullbackOverField Y k' q g).boundary
          (Finset.image (pullbackIndex T Y k' q g) J)).subschemeι ⁻¹'
          ⋃₀ {C' | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
              (Finset.image (pullbackIndex T Y k' q g) J) ∧ ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C}),
        (componentUnionIdeal T.boundary J 𝒞 hop).comap g =
          componentUnionIdeal (T.pullbackOverField Y k' q g).boundary
            (Finset.image (pullbackIndex T Y k' q g) J)
            {C' | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
              (Finset.image (pullbackIndex T Y k' q g) J) ∧ ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C} hop'
  componentsDown : ∀ (J : Finset (Fin T.boundary.length)),
    ∀ C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary (Finset.image (pullbackIndex T Y k' q g) J),
      ∃ C ∈ intersectionComponents T.boundary J, Set.MapsTo (⇑g) C' C ∧
        ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ
  componentsUp : ∀ (J : Finset (Fin T.boundary.length)),
    ∀ C ∈ intersectionComponents T.boundary J, ∀ y : ↥Y, g y ∈ C →
      ∃ C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary (Finset.image (pullbackIndex T Y k' q g) J),
        y ∈ C' ∧
          ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ
  orderAtComap : ∀ (I : T.scheme.IdealSheafData) (y : ↥Y), orderAt (I.comap g) y = orderAt I (g y)

theorem centerInvariant_le_iff {Y Y' : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData)
    (I' : Y'.IdealSheafData) (m' : ℕ) (L' : List Y'.IdealSheafData) :
    (centerInvariant I m L).Le (centerInvariant I' m' L') ↔
      ((centerInvariant I m L).Lt (centerInvariant I' m' L') ∨
        (minIndexCard I m L = minIndexCard I' m' L' ∧ maxCandidateOrder I m L = maxCandidateOrder I' m' L' ∧
          sortedIndices (lexMaxIndices I m L) = sortedIndices (lexMaxIndices I' m' L'))) :=
  Iff.rfl

theorem minIndexCard_ne_zero_and_le_pullbackOverField (_hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (_hT : IsLocallyMonomialTriple T)
    (_hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g))
    (hP : IsComponentCompatiblePullback T Y k' q g)
    (h0 : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary ≠ 0) :
    minIndexCard T.ideal T.mult T.boundary ≠ 0 ∧
      minIndexCard T.ideal T.mult T.boundary ≤
        minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary := by
  obtain ⟨J', C', hcard', hmem', hord'⟩ :=
    exists_isCandidateComponent_minIndexCard (T.pullbackOverField Y k' q g).ideal
      (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary h0
  have hinj : Function.Injective (pullbackIndexSymm T Y k' q g) := by
    intro a b hab
    apply Fin.val_injective
    have h := congrArg (fun z : Fin T.boundary.length => (z : ℕ)) hab
    simpa using h
  have hJ : Finset.image (pullbackIndex T Y k' q g)
      (Finset.image (pullbackIndexSymm T Y k' q g) J') = J' := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
      rwa [pullbackIndex_pullbackIndexSymm]
    · intro hx
      exact Finset.mem_image.2 ⟨pullbackIndexSymm T Y k' q g x,
        Finset.mem_image.2 ⟨x, hx, rfl⟩, pullbackIndex_pullbackIndexSymm T Y k' q g x⟩
  obtain ⟨C, hC, -, hgen⟩ :=
    hP.componentsDown (Finset.image (pullbackIndexSymm T Y k' q g) J') C'
      (by rw [hJ]; exact hmem')
  have h4 : g (isIrreducible_of_mem_intersectionComponents hmem').genericPoint
      = (isIrreducible_of_mem_intersectionComponents hC).genericPoint :=
    hgen _ _ (isGenericPoint_genericPoint_of_mem_intersectionComponents hmem')
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC)
  have heq : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C := by
    have e1 : orderAlong (T.pullbackOverField Y k' q g).ideal C'
        = orderAt (T.pullbackOverField Y k' q g).ideal
            (isIrreducible_of_mem_intersectionComponents hmem').genericPoint :=
      orderAlong_eq_orderAt_of_mem_intersectionComponents _ hmem'
    have e2 : orderAt (T.pullbackOverField Y k' q g).ideal
          (isIrreducible_of_mem_intersectionComponents hmem').genericPoint
        = orderAt T.ideal (g (isIrreducible_of_mem_intersectionComponents hmem').genericPoint) :=
      hP.orderAtComap T.ideal _
    have e3 : orderAlong T.ideal C
        = orderAt T.ideal (isIrreducible_of_mem_intersectionComponents hC).genericPoint :=
      orderAlong_eq_orderAt_of_mem_intersectionComponents _ hC
    rw [e1, e2, h4, e3]
  have hord2 : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    have hx : (T.mult : ℕ∞) ≤ orderAlong (T.pullbackOverField Y k' q g).ideal C' := hord'
    rw [heq] at hx
    exact hx
  have hcardJ : (Finset.image (pullbackIndexSymm T Y k' q g) J').card = J'.card :=
    Finset.card_image_of_injective J' hinj
  have hcand : IsCandidateComponent T.ideal T.mult T.boundary
      (minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary)
      (Finset.image (pullbackIndexSymm T Y k' q g) J') C :=
    ⟨hcardJ.trans hcard', hC, hord2⟩
  have hone : 1 ≤ minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary := Nat.pos_of_ne_zero h0
  have hex : ∃ r : ℕ, 1 ≤ r ∧ ∃ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
      IsCandidateComponent T.ideal T.mult T.boundary r J C :=
    ⟨minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary, hone,
      Finset.image (pullbackIndexSymm T Y k' q g) J', C, hcand⟩
  have hspec := minIndexCard_spec T.ideal T.mult T.boundary hex
  refine ⟨?_, hspec.2.2 _ hone _ _ hcand⟩
  have h1 := hspec.1
  omega

theorem maxCandidateOrder_le_of_minIndexCard_eq (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hT : IsLocallyMonomialTriple T)
    (hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g))
    (hP : IsComponentCompatiblePullback T Y k' q g)
    (hmin : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = minIndexCard T.ideal T.mult T.boundary)
    (h0 : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    maxCandidateOrder (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary ≤ maxCandidateOrder T.ideal T.mult T.boundary := by
  have h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary ≠ 0 := by
    rw [hmin]
    exact h0
  obtain ⟨J', C', hcand', hord'⟩ := (maxCandidateOrder_spec hGeom hT' h0').1
  have hcandSplit :
      J'.card = minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary ∧
        C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary J' ∧
        ((T.pullbackOverField Y k' q g).mult : ℕ∞) ≤
          orderAlong (T.pullbackOverField Y k' q g).ideal C' := hcand'
  obtain ⟨hcard', hmemC', hmult'⟩ := hcandSplit
  have hback_inj : Function.Injective (pullbackIndexSymm T Y k' q g) := by
    intro a b hab
    apply Fin.val_injective
    have h := congrArg Fin.val hab
    rwa [pullbackIndexSymm_val, pullbackIndexSymm_val] at h
  have himg : Finset.image (pullbackIndex T Y k' q g)
      (Finset.image (pullbackIndexSymm T Y k' q g) J') = J' := by
    apply Finset.ext
    intro j
    constructor
    · intro hj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hj
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
      rw [pullbackIndex_pullbackIndexSymm]
      exact hb
    · intro hj
      exact Finset.mem_image.2 ⟨pullbackIndexSymm T Y k' q g j,
        Finset.mem_image.2 ⟨j, hj, rfl⟩, pullbackIndex_pullbackIndexSymm T Y k' q g j⟩
  have hmem : C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
      (Finset.image (pullbackIndex T Y k' q g) (Finset.image (pullbackIndexSymm T Y k' q g) J')) := by
    rw [himg]
    exact hmemC'
  obtain ⟨C, hC, _hmaps, hgen⟩ :=
    hP.componentsDown (Finset.image (pullbackIndexSymm T Y k' q g) J') C' hmem
  have hg : g (isIrreducible_of_mem_intersectionComponents hmemC').genericPoint =
      (isIrreducible_of_mem_intersectionComponents hC).genericPoint :=
    hgen _ _ (isGenericPoint_genericPoint_of_mem_intersectionComponents hmemC')
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC)
  have hord : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C := by
    rw [orderAlong_eq_orderAt_of_mem_intersectionComponents (T.pullbackOverField Y k' q g).ideal hmemC',
      orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC, ← hg]
    exact hP.orderAtComap T.ideal (isIrreducible_of_mem_intersectionComponents hmemC').genericPoint
  have hcardJ : (Finset.image (pullbackIndexSymm T Y k' q g) J').card
      = minIndexCard T.ideal T.mult T.boundary := by
    rw [Finset.card_image_of_injective _ hback_inj, hcard']
    exact hmin
  have hmultC : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    have hb := hmult'
    rw [hord] at hb
    exact hb
  have hcandT : IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary)
      (Finset.image (pullbackIndexSymm T Y k' q g) J') C :=
    And.intro hcardJ (And.intro hC hmultC)
  have hmaxOrd := (maxCandidateOrder_spec hGeom hT h0).2.1 _ _ hcandT
  rw [← hord', hord]
  exact hmaxOrd

private theorem centerInvariant_lt_iff_lex_consolidated388 {Y Y' : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) (I' : Y'.IdealSheafData) (m' : ℕ)
    (L' : List Y'.IdealSheafData) :
    (centerInvariant I m L).Lt (centerInvariant I' m' L') ↔
      (minIndexCard I m L < minIndexCard I' m' L' ∨
        (minIndexCard I m L = minIndexCard I' m' L' ∧
          (maxCandidateOrder I' m' L' < maxCandidateOrder I m L ∨
            (maxCandidateOrder I m L = maxCandidateOrder I' m' L' ∧
              List.Lex (· < ·) (sortedIndices (lexMaxIndices I m L))
                (sortedIndices (lexMaxIndices I' m' L')))))) :=
  Iff.rfl

section
variable (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)

private theorem pullbackIndexSymm_injective_consolidated388 :
    Function.Injective (pullbackIndexSymm T Y k' q g) := by
  intro a b h
  apply Fin.val_injective
  rw [← pullbackIndexSymm_val T Y k' q g a, ← pullbackIndexSymm_val T Y k' q g b, h]

private theorem pullbackIndex_strictMono_consolidated388 :
    StrictMono (pullbackIndex T Y k' q g) := by
  intro a b hab
  have h : (a : ℕ) < (b : ℕ) := Fin.lt_def.mp hab
  rw [Fin.lt_def, pullbackIndex_val, pullbackIndex_val]
  exact h

private theorem sortedIndices_image_pullbackIndex_consolidated388 (J : Finset (Fin T.boundary.length)) :
    sortedIndices (Finset.image (pullbackIndex T Y k' q g) J) = sortedIndices J := by
  rw [sortedIndices_image_of_strictMono (pullbackIndex T Y k' q g)
    (pullbackIndex_strictMono_consolidated388 T Y k' q g) J]
  simp only [pullbackIndex_val]
  rfl

private theorem orderAlong_pullbackOverField_eq_orderAlong_consolidated388 (hP : IsComponentCompatiblePullback T Y k' q g) (J : Finset (Fin T.boundary.length))
    (C' : Set ↥Y) (C : Set ↥T.scheme)
    (hC' : C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
      (Finset.image (pullbackIndex T Y k' q g) J))
    (hC : C ∈ intersectionComponents T.boundary J)
    (hgen : ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ) :
    orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C := by
  have h1 := orderAlong_eq_orderAt_of_mem_intersectionComponents (T.pullbackOverField Y k' q g).ideal hC'
  have h2 := orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC
  have hg := hgen (isIrreducible_of_mem_intersectionComponents hC').genericPoint
      (isIrreducible_of_mem_intersectionComponents hC).genericPoint
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC')
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC)
  have h3 := hP.orderAtComap T.ideal (isIrreducible_of_mem_intersectionComponents hC').genericPoint
  exact h1.trans (h3.trans ((congrArg (orderAt T.ideal) hg).trans h2.symm))


end

theorem minIndexCard_pullbackOverField_eq_zero_or_centerInvariant_le (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hT : IsLocallyMonomialTriple T)
    (hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g))
    (hP : IsComponentCompatiblePullback T Y k' q g) :
    minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = 0 ∨
      (centerInvariant T.ideal T.mult T.boundary).Le
        (centerInvariant (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary) := by
  by_cases h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary = 0
  · exact Or.inl h0'
  refine Or.inr ?_
  obtain ⟨h0, hle⟩ := minIndexCard_ne_zero_and_le_pullbackOverField hGeom T Y k' q g hT hT' hP h0'
  rw [centerInvariant_le_iff, centerInvariant_lt_iff_lex_consolidated388]
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl (Or.inl hlt)
  have hmaxle := maxCandidateOrder_le_of_minIndexCard_eq hGeom T Y k' q g hT hT' hP heq.symm h0
  rcases lt_or_eq_of_le hmaxle with hmlt | hmeq
  · exact Or.inl (Or.inr ⟨heq, Or.inl hmlt⟩)
  have hoptT := lexMaxIndices_spec hGeom hT h0
  have hoptT' := lexMaxIndices_spec hGeom hT' h0'
  have hbest' : ∃ C : Set ↥Y,
      IsCandidateComponent (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary
        (minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary)
        (lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary) C ∧
        orderAlong (T.pullbackOverField Y k' q g).ideal C =
          maxCandidateOrder (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
            (T.pullbackOverField Y k' q g).boundary := And.left hoptT'
  obtain ⟨C', hcand', hordC'⟩ := hbest'
  have hmemC' : C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
      (lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary) := And.left (And.right hcand')
  have hmultC' : ((T.pullbackOverField Y k' q g).mult : ℕ∞) ≤
      orderAlong (T.pullbackOverField Y k' q g).ideal C' := And.right (And.right hcand')
  have hex : ∃ B : Finset (Fin T.boundary.length),
      Finset.image (pullbackIndex T Y k' q g) B =
          lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
            (T.pullbackOverField Y k' q g).boundary ∧
        B.card = (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
          (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary).card := by
    refine ⟨Finset.image (pullbackIndexSymm T Y k' q g)
      (lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary), ?_, ?_⟩
    · rw [Finset.image_image]
      have hcomp : (pullbackIndex T Y k' q g) ∘ (pullbackIndexSymm T Y k' q g) = id :=
        funext (pullbackIndex_pullbackIndexSymm T Y k' q g)
      rw [hcomp, Finset.image_id]
    · exact Finset.card_image_of_injective _ (pullbackIndexSymm_injective_consolidated388 T Y k' q g)
  obtain ⟨B, hBim, hBcard⟩ := hex
  have hmemB : C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
      (Finset.image (pullbackIndex T Y k' q g) B) := by
    rw [hBim]
    exact hmemC'
  obtain ⟨C, hC, -, hgenericPt⟩ := hP.componentsDown B C' hmemB
  have hordEq : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C :=
    orderAlong_pullbackOverField_eq_orderAlong_consolidated388 T Y k' q g hP B C' C hmemB hC hgenericPt
  have hcardB : B.card = minIndexCard T.ideal T.mult T.boundary := by
    rw [hBcard, card_lexMaxIndices hGeom hT' h0']
    exact heq.symm
  have hmultC : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    rw [← hordEq]
    exact hmultC'
  have hmaxC : orderAlong T.ideal C = maxCandidateOrder T.ideal T.mult T.boundary := by
    rw [← hordEq, hordC']
    exact hmeq
  have hbestB : IsMaxOrderIndexSet T.ideal T.mult T.boundary B :=
    Exists.intro C (And.intro (And.intro hcardB (And.intro hC hmultC)) hmaxC)
  have hnotlex := And.right hoptT B hbestB
  have hsp : sortedIndices (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
      (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary) =
      sortedIndices B := by
    rw [← hBim]
    exact sortedIndices_image_pullbackIndex_consolidated388 T Y k' q g B
  rcases trichotomous_of (List.Lex (· < ·))
      (sortedIndices (lexMaxIndices T.ideal T.mult T.boundary))
      (sortedIndices (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
        (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary)) with
    hlex | hlexeq | hlex
  · exact Or.inl (Or.inr ⟨heq, Or.inr ⟨hmeq.symm, hlex⟩⟩)
  · exact Or.inr ⟨heq, hmeq.symm, hlexeq⟩
  · rw [hsp] at hlex
    exact absurd hlex hnotlex

theorem lexMaxIndices_pullbackOverField_eq_image (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u)
    [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (h : sortedIndices (lexMaxIndices T.ideal T.mult T.boundary) =
      sortedIndices (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
        (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary)) :
    lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary =
      Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary) := by
  apply Finset.ext
  intro j'
  constructor
  · intro hj'
    have hmem : ((j' : ℕ)) ∈ sortedIndices (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
        (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary) :=
      (mem_sortedIndices _ _).2 ⟨j', hj', rfl⟩
    rw [← h] at hmem
    obtain ⟨j, hj, hval⟩ := (mem_sortedIndices _ _).1 hmem
    refine Finset.mem_image.2 ⟨j, hj, ?_⟩
    apply Fin.val_injective
    rw [pullbackIndex_val]
    exact hval
  · intro hj'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hj'
    have hmem : ((j : ℕ)) ∈ sortedIndices (lexMaxIndices T.ideal T.mult T.boundary) :=
      (mem_sortedIndices _ _).2 ⟨j, hj, rfl⟩
    rw [h] at hmem
    obtain ⟨j2, hj2, hval⟩ := (mem_sortedIndices _ _).1 hmem
    have hj2eq : j2 = pullbackIndex T Y k' q g j := by
      apply Fin.val_injective
      rw [pullbackIndex_val]
      exact hval
    rwa [hj2eq] at hj2

private theorem componentUnionIdeal_congr_consolidated388 {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J J' : Finset (Fin L.length)) (𝒞 𝒞' : Set (Set ↥Y)) (hJ : J = J') (h𝒞 : 𝒞 = 𝒞')
    (hop : IsOpen (⇑(intersectionIdeal L J).subschemeι ⁻¹' ⋃₀ 𝒞))
    (hop' : IsOpen (⇑(intersectionIdeal L J').subschemeι ⁻¹' ⋃₀ 𝒞')) :
    componentUnionIdeal L J 𝒞 hop = componentUnionIdeal L J' 𝒞' hop' := by
  subst hJ
  subst h𝒞
  rfl

section
variable (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) (hT : IsLocallyMonomialTriple T) (hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g)) (hP : IsComponentCompatiblePullback T Y k' q g)
include hGeom hT hT' hP

theorem monomialCenter_pullbackOverField_eq_comap (hmin : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = minIndexCard T.ideal T.mult T.boundary)
    (hmax : maxCandidateOrder (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = maxCandidateOrder T.ideal T.mult T.boundary)
    (hch : lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary =
      Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) :
    monomialCenter (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary =
      (monomialCenter T.ideal T.mult T.boundary).comap g := by
  by_cases h0 : minIndexCard T.ideal T.mult T.boundary = 0
  · have h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = 0 := by rw [hmin]; exact h0
    rw [monomialCenter_eq_top_of_minIndexCard_eq_zero _ _ _ h0']
    rw [monomialCenter_eq_top_of_minIndexCard_eq_zero _ _ _ h0]
    exact (Scheme.IdealSheafData.comap_top g).symm
  · have h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary ≠ 0 := by rw [hmin]; exact h0
    obtain ⟨hop', heq⟩ := hP.comapCenter (lexMaxIndices T.ideal T.mult T.boundary)
      (centerComponents T.ideal T.mult T.boundary)
      (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary)
      (isOpen_preimage_sUnion_centerComponents hGeom hT)
    have hSet : centerComponents (T.pullbackOverField Y k' q g).ideal
          (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary =
        {C' | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
            (Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) ∧
          ∃ C ∈ centerComponents T.ideal T.mult T.boundary, Set.MapsTo (⇑g) C' C} := by
      ext C'
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro hmem
        obtain ⟨hcand, hordC'⟩ := (mem_centerComponents_iff _ _ _ C').1 hmem
        obtain ⟨hcardJ', hmemC', hmultC'⟩ := hcand
        rw [hch] at hmemC'
        refine ⟨hmemC', ?_⟩
        obtain ⟨C, hC, hmaps, hgen⟩ :=
          hP.componentsDown (lexMaxIndices T.ideal T.mult T.boundary) C' hmemC'
        have hord : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C :=
          orderAlong_pullbackOverField_eq_orderAlong_consolidated388 T Y k' q g hP
            (lexMaxIndices T.ideal T.mult T.boundary) C' C hmemC' hC hgen
        refine ⟨C, (mem_centerComponents_iff _ _ _ C).2
          ⟨⟨card_lexMaxIndices hGeom hT h0, hC, ?_⟩, ?_⟩, hmaps⟩
        · rw [← hord]
          exact hmultC'
        · rw [← hord, hordC']
          exact hmax
      · rintro ⟨hmemC', C, hCopt, hmaps⟩
        obtain ⟨hcandC, hordC⟩ := (mem_centerComponents_iff _ _ _ C).1 hCopt
        obtain ⟨hcardJ, hCmem, hmultC⟩ := hcandC
        obtain ⟨C₀, hC₀, hmaps₀, hgen⟩ :=
          hP.componentsDown (lexMaxIndices T.ideal T.mult T.boundary) C' hmemC'
        obtain ⟨x, hx⟩ := (isIrreducible_of_mem_intersectionComponents hmemC').nonempty
        have hCC₀ : C₀ = C := by
          by_contra hne
          exact Set.disjoint_left.1
            (hGeom.components_disjoint T hT.valid _ C₀ hC₀ C hCmem hne) (hmaps₀ hx) (hmaps hx)
        have hord : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C₀ :=
          orderAlong_pullbackOverField_eq_orderAlong_consolidated388 T Y k' q g hP
            (lexMaxIndices T.ideal T.mult T.boundary) C' C₀ hmemC' hC₀ hgen
        refine (mem_centerComponents_iff _ _ _ C').2
          ⟨⟨card_lexMaxIndices hGeom hT' h0', ?_, ?_⟩, ?_⟩
        · rw [hch]
          exact hmemC'
        · rw [hord, hCC₀]
          exact hmultC
        · rw [hord, hCC₀, hordC]
          exact hmax.symm
    rw [monomialCenter_eq_componentUnionIdeal hGeom hT' h0',
      monomialCenter_eq_componentUnionIdeal hGeom hT h0, heq]
    exact componentUnionIdeal_congr_consolidated388 _ _ _ _ _ hch hSet _ _

theorem comap_monomialCenter_eq_top (h0 : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    (hkey : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary = 0 ∨
        (centerInvariant T.ideal T.mult T.boundary).Lt
          (centerInvariant (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
            (T.pullbackOverField Y k' q g).boundary)) :
    (monomialCenter T.ideal T.mult T.boundary).comap g = ⊤ := by
  refine Blowup.comap_eq_top_of_notMem_support g (monomialCenter T.ideal T.mult T.boundary) ?_
  intro y hy
  have hmem : g y ∈ monomialCenterSet T.ideal T.mult T.boundary := by
    rw [← support_monomialCenter hGeom hT h0]
    exact hy
  rw [monomialCenterSet_eq_sUnion_centerComponents, Set.mem_sUnion] at hmem
  obtain ⟨C, hCopt, hgyC⟩ := hmem
  obtain ⟨hcandC, hordC⟩ :=
    (mem_centerComponents_iff T.ideal T.mult T.boundary C).1 hCopt
  obtain ⟨-, hmemC, hmultC⟩ := hcandC
  obtain ⟨C', hC'mem, -, hgen⟩ :=
    hP.componentsUp (lexMaxIndices T.ideal T.mult T.boundary) C hmemC y hgyC
  have hordEq : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C :=
    orderAlong_pullbackOverField_eq_orderAlong_consolidated388 T Y k' q g hP
      (lexMaxIndices T.ideal T.mult T.boundary) C' C hC'mem hmemC hgen
  have hinj : Function.Injective (pullbackIndex T Y k' q g) :=
    (pullbackIndex_strictMono_consolidated388 T Y k' q g).injective
  have hcard' : (Finset.image (pullbackIndex T Y k' q g)
      (lexMaxIndices T.ideal T.mult T.boundary)).card
      = minIndexCard T.ideal T.mult T.boundary := by
    rw [Finset.card_image_of_injective _ hinj]
    exact card_lexMaxIndices hGeom hT h0
  have hmultC' : ((T.pullbackOverField Y k' q g).mult : ℕ∞)
      ≤ orderAlong (T.pullbackOverField Y k' q g).ideal C' := by
    rw [hordEq]
    exact hmultC
  have hcand' : IsCandidateComponent (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary (minIndexCard T.ideal T.mult T.boundary)
      (Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) C' :=
    ⟨hcard', hC'mem, hmultC'⟩
  have hone : 1 ≤ minIndexCard T.ideal T.mult T.boundary := Nat.pos_of_ne_zero h0
  have hspec := minIndexCard_spec (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary
      ⟨minIndexCard T.ideal T.mult T.boundary, hone,
        Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary), C',
        hcand'⟩
  have hle : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary ≤ minIndexCard T.ideal T.mult T.boundary :=
    hspec.2.2 _ hone _ _ hcand'
  have hgeone := hspec.1
  rcases hkey with hzero | hlt
  · omega
  rw [centerInvariant_lt_iff_lex_consolidated388] at hlt
  have h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary ≠ 0 := by omega
  rcases hlt with hml | ⟨hmeq, hrest⟩
  · omega
  have hcand'' : IsCandidateComponent (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary
      (minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary)
      (Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) C' := by
    rw [← hmeq]
    exact hcand'
  have hordC' : orderAlong (T.pullbackOverField Y k' q g).ideal C'
      = maxCandidateOrder T.ideal T.mult T.boundary := by
    rw [hordEq]
    exact hordC
  rcases hrest with hmax | ⟨hmaxeq, hlex⟩
  · have hb := (maxCandidateOrder_spec hGeom hT' h0').2.1 _ _ hcand''
    rw [hordC'] at hb
    exact absurd hmax (not_lt.mpr hb)
  have hbest : IsMaxOrderIndexSet (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary
      (Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) :=
    ⟨C', hcand'', hordC'.trans hmaxeq⟩
  have hnot := (lexMaxIndices_spec hGeom hT' h0').2 _ hbest
  rw [sortedIndices_image_pullbackIndex_consolidated388 T Y k' q g (lexMaxIndices T.ideal T.mult T.boundary)] at hnot
  exact hnot hlex


end

end MonomialCenter


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonotoneInvariantSmoothPullback
section


section

namespace MonomialCenter

theorem IsComponentCompatiblePullback.of_flat (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : T.IsAdmissible) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) [Flat g]
    (hT' : (T.pullbackOverField Y k' q g).IsAdmissible)
    (hord : ∀ (A : T.scheme.IdealSheafData) (y : ↥Y), orderAt (A.comap g) y = orderAt A (g y)) :
    IsComponentCompatiblePullback T Y k' q g :=
  ⟨fun J 𝒞 h𝒞 hop => hGeom.flat_comap_center T hT Y k' q g hT' J 𝒞 h𝒞 hop,
    fun J => hGeom.flat_components_down T hT Y k' q g hT' J,
    fun J => hGeom.flat_components_up T hT Y k' q g hT' J, hord⟩

end MonomialCenter


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.TransformedBoundaryComponents
section

open TopologicalSpace

section

section
variable {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData) (L : List X.IdealSheafData)

private theorem getElem_map_strictTransform_append_of_lt_consolidated433 (i : ℕ) (hi : i < L.length)
    (hi' : i < (L.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length) :
    (L.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z])[i]'hi'
      = Blowup.strictTransform π Z (L[i]'hi) := by
  have h1 : i < (L.map (Blowup.strictTransform π Z)).length := by
    rw [List.length_map]; exact hi
  exact (List.getElem_append_left h1).trans (List.getElem_map _)

private theorem getElem_length_map_strictTransform_append_consolidated433 (hi' : L.length < (L.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length) :
    (L.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z])[L.length]'hi'
      = Blowup.exceptionalIdeal π Z := by
  simp [List.getElem_append_right]

theorem transformedBoundary_get_strictTransformIndex (j : Fin L.length) :
    (transformedBoundary π Z L).get (strictTransformIndex π Z L j) = Blowup.strictTransform π Z (L.get j) := by
  simp only [List.get_eq_getElem]
  exact getElem_map_strictTransform_append_of_lt_consolidated433 π Z L (j : ℕ) j.isLt _


end

theorem mem_support_intersectionIdeal_iff {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) (y : ↥Y) :
    y ∈ (intersectionIdeal L J).support ↔ ∀ j ∈ J, y ∈ (L.get j).support := by
  have hsup : ∀ A B : Y.IdealSheafData,
      y ∈ (A ⊔ B).support ↔ y ∈ A.support ∧ y ∈ B.support := by
    intro A B
    rw [Scheme.IdealSheafData.support_sup]
    exact Iff.rfl
  rw [intersectionIdeal_eq_iSup]
  induction J using Finset.induction_on with
  | empty =>
      have hbot : (⨆ j ∈ (∅ : Finset (Fin L.length)), L.get j) = ⊥ := by simp
      rw [hbot]
      constructor
      · intro _ j hj
        exact absurd hj (Finset.notMem_empty j)
      · intro _
        rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_bot]
        exact bot_le
  | insert a s _ ih =>
      rw [Finset.iSup_insert, hsup, Finset.forall_mem_insert]
      exact and_congr_right fun _ => ih

theorem mem_support_strictTransform_iff_of_notMem_support {X X' : Scheme.{u}}
    [IsLocallyNoetherian X'] (π : X' ⟶ X) (Z D : X.IdealSheafData) (x' : ↥X')
    (hx' : π x' ∉ Z.support) :
    x' ∈ (Blowup.strictTransform π Z D).support ↔ π x' ∈ D.support := by
  have hsupp : ((Blowup.strictTransform π Z D).support : Set ↥X') =
      closure (⇑π.base ⁻¹' ((D.support : Set ↥X) \ (Z.support : Set ↥X))) :=
    support_strictTransform_eq_closure_preimage π Z D
  constructor
  · intro hx
    have h1 : x' ∈ closure (⇑π.base ⁻¹' ((D.support : Set ↥X) \ (Z.support : Set ↥X))) := by
      have h0 : x' ∈ ((Blowup.strictTransform π Z D).support : Set ↥X') := hx
      rw [hsupp] at h0
      exact h0
    have h2 : closure (⇑π.base ⁻¹' ((D.support : Set ↥X) \ (Z.support : Set ↥X)))
        ⊆ ⇑π.base ⁻¹' ((D.support : Set ↥X)) := by
      refine closure_minimal (fun y hy => hy.1) ?_
      exact (Scheme.IdealSheafData.support D).isClosed.preimage π.base.hom.continuous
    exact h2 h1
  · intro hx
    have h3 : x' ∈ ⇑π.base ⁻¹' ((D.support : Set ↥X) \ (Z.support : Set ↥X)) := ⟨hx, hx'⟩
    have h4 := subset_closure h3
    rw [← hsupp] at h4
    exact h4

theorem mem_support_intersectionIdeal_transformedBoundary_iff (T : MarkedIdealWithBoundary.{u}) (X' : Scheme.{u})
    (π : X' ⟶ T.scheme) (Z : T.scheme.IdealSheafData)
    (J : Finset (Fin T.boundary.length)) (x' : ↥X') :
    x' ∈ (intersectionIdeal (transformedBoundary π Z T.boundary)
            (Finset.image (strictTransformIndex π Z T.boundary) J)).support ↔
      ∀ j ∈ J, x' ∈ (Blowup.strictTransform π Z (T.boundary.get j)).support := by
  rw [mem_support_intersectionIdeal_iff]
  constructor
  · intro h j hj
    have h1 := h (strictTransformIndex π Z T.boundary j) (Finset.mem_image_of_mem _ hj)
    rwa [transformedBoundary_get_strictTransformIndex] at h1
  · intro h j' hj'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hj'
    rw [transformedBoundary_get_strictTransformIndex]
    exact h j hj

private theorem mem_support_intersectionIdeal_transformedBoundary_iff_of_notMem_consolidated433 {X X' : Scheme.{u}} [IsLocallyNoetherian X']
    (π : X' ⟶ X) (Z : X.IdealSheafData) (L : List X.IdealSheafData)
    (J : Finset (Fin L.length)) (x' : ↥X') (hx' : π x' ∉ Z.support) :
    x' ∈ (intersectionIdeal (transformedBoundary π Z L) (J.image (strictTransformIndex π Z L))).support ↔
      π x' ∈ (intersectionIdeal L J).support := by
  rw [mem_support_intersectionIdeal_iff, mem_support_intersectionIdeal_iff]
  constructor
  · intro h j hj
    have h1 := h (strictTransformIndex π Z L j) (Finset.mem_image_of_mem _ hj)
    rw [transformedBoundary_get_strictTransformIndex] at h1
    exact (mem_support_strictTransform_iff_of_notMem_support π Z (L.get j) x' hx').mp h1
  · intro h j' hj'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hj'
    rw [transformedBoundary_get_strictTransformIndex]
    exact (mem_support_strictTransform_iff_of_notMem_support π Z (L.get j) x' hx').mpr (h j hj)

private theorem genericPoint_notMem_support_exceptionalIdeal_consolidated433
    (T : MarkedIdealWithBoundary.{u}) (Z : T.scheme.IdealSheafData)
    (hsncZ : HasStrictNormalCrossingsWith T.structMap Z T.boundary)
    (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    [IsLocallyNoetherian X'] [NoetherianSpace ↥X']
    (J : Finset (Fin T.boundary.length)) (C' : Set ↥X')
    (hC'irr : IsIrreducible C')
    (hC'sub : C' ⊆ (↑(intersectionIdeal (transformedBoundary π Z T.boundary)
        (J.image (strictTransformIndex π Z T.boundary))).support : Set ↥X'))
    (hC'max : ∀ D : Set ↥X', IsIrreducible D → C' ⊆ D →
        D ⊆ (↑(intersectionIdeal (transformedBoundary π Z T.boundary)
          (J.image (strictTransformIndex π Z T.boundary))).support : Set ↥X') → D = C')
    (ξ' : ↥X') (hξ' : IsGenericPoint ξ' C') :
    ξ' ∉ (Blowup.exceptionalIdeal π Z).support := by
  intro hmem
  have hπξ : π ξ' ∈ Z.support := by
    have h0 : ξ' ∈ (↑(Z.comap π).support : Set ↥X') := hmem
    rw [support_comap_eq π Z] at h0
    exact h0
  have hξ'A' : ξ' ∈ (intersectionIdeal (transformedBoundary π Z T.boundary)
      (J.image (strictTransformIndex π Z T.boundary))).support := hC'sub hξ'.mem
  have hpos := inStrictNormalCrossingPositionAt_strictTransform_of_mem_support
    T.structMap π Z T.boundary hπ hsncZ ξ' hπξ
  obtain ⟨U, hξU, m, c, a, hinj, hnone, hsome⟩ := hpos
  have hlen : (T.boundary.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length
      = T.boundary.length + 1 := by simp
  have hnlt : T.boundary.length
      < (T.boundary.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length := by
    rw [hlen]; exact Nat.lt_succ_self _
  have hBlast :
      (T.boundary.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z])[T.boundary.length]'hnlt
        = Blowup.exceptionalIdeal π Z := getElem_length_map_strictTransform_append_consolidated433 π Z T.boundary hnlt
  have hexists : ∃ t : Fin m, a T.boundary.length = some t := by
    cases hh : a T.boundary.length with
    | none =>
        exfalso
        have h0 := hnone T.boundary.length hnlt hh
        rw [hBlast] at h0
        exact notMem_support_of_restrictIdeal_eq_top (Blowup.exceptionalIdeal π Z) U ξ' hξU h0 hmem
    | some t => exact ⟨t, rfl⟩
  obtain ⟨t₀, hat₀⟩ := hexists
  have hexcU : restrictIdeal (Blowup.exceptionalIdeal π Z) U = c.coordIdeal {t₀} := by
    have h0 := hsome T.boundary.length hnlt t₀ hat₀
    rwa [hBlast] at h0
  have hchoice : ∀ j : Fin T.boundary.length, ∃ t : Fin m,
      j ∈ J → (a (j : ℕ) = some t ∧
        restrictIdeal (Blowup.strictTransform π Z (T.boundary.get j)) U = c.coordIdeal {t}) := by
    intro j
    by_cases hj : j ∈ J
    · have hjlt : (j : ℕ)
          < (T.boundary.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length := by
        rw [hlen]; exact Nat.lt_succ_of_lt j.isLt
      have hBj : (T.boundary.map (Blowup.strictTransform π Z)
            ++ [Blowup.exceptionalIdeal π Z])[(j : ℕ)]'hjlt
          = Blowup.strictTransform π Z (T.boundary.get j) := by
        rw [List.get_eq_getElem]
        exact getElem_map_strictTransform_append_of_lt_consolidated433 π Z T.boundary (j : ℕ) j.isLt hjlt
      have hmemj : ξ' ∈ (Blowup.strictTransform π Z (T.boundary.get j)).support :=
        (mem_support_intersectionIdeal_transformedBoundary_iff T X' π Z J ξ').mp hξ'A' j hj
      cases hh : a (j : ℕ) with
      | none =>
          exfalso
          have h0 := hnone (j : ℕ) hjlt hh
          rw [hBj] at h0
          exact notMem_support_of_restrictIdeal_eq_top _ U ξ' hξU h0 hmemj
      | some t =>
          refine ⟨t, fun _ => ⟨rfl, ?_⟩⟩
          have h0 := hsome (j : ℕ) hjlt t hh
          rwa [hBj] at h0
    · exact ⟨t₀, fun h => absurd h hj⟩
  choose tfun htfun using hchoice
  have ht₀notin : t₀ ∉ J.image tfun := by
    intro hcon
    obtain ⟨j, hj, hjt⟩ := Finset.mem_image.mp hcon
    have h1 : a (j : ℕ) = some t₀ := by rw [(htfun j hj).1, hjt]
    have hjlt : (j : ℕ)
        < (T.boundary.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length := by
      rw [hlen]; exact Nat.lt_succ_of_lt j.isLt
    have h2 := hinj (j : ℕ) hjlt T.boundary.length hnlt t₀ h1 hat₀
    exact absurd h2 (Nat.ne_of_lt j.isLt)
  have hstep1 : restrictIdeal (intersectionIdeal (transformedBoundary π Z T.boundary)
        (J.image (strictTransformIndex π Z T.boundary))) U
      = ⨆ j' ∈ J.image (strictTransformIndex π Z T.boundary),
          restrictIdeal ((transformedBoundary π Z T.boundary).get j') U := by
    rw [intersectionIdeal_eq_iSup]
    exact MonomialChart.restrictIdeal_biSup_finset U
      (fun j' => (transformedBoundary π Z T.boundary).get j') _
  have hstep2 : (⨆ j' ∈ J.image (strictTransformIndex π Z T.boundary),
          restrictIdeal ((transformedBoundary π Z T.boundary).get j') U)
      = ⨆ j ∈ J, restrictIdeal
          ((transformedBoundary π Z T.boundary).get (strictTransformIndex π Z T.boundary j)) U :=
    Finset.iSup_finset_image
  have hstep3 : (⨆ j ∈ J, restrictIdeal
          ((transformedBoundary π Z T.boundary).get (strictTransformIndex π Z T.boundary j)) U)
      = ⨆ j ∈ J, c.coordIdeal {tfun j} := by
    refine iSup_congr fun j => iSup_congr fun hj => ?_
    rw [transformedBoundary_get_strictTransformIndex]
    exact (htfun j hj).2
  have hstep4 : (⨆ j ∈ J, c.coordIdeal {tfun j}) = c.coordIdeal (J.image tfun) := by
    rw [MonomialChart.coordIdeal_eq_biSup_singleton, Finset.iSup_finset_image]
  have hZU : restrictIdeal (intersectionIdeal (transformedBoundary π Z T.boundary)
        (J.image (strictTransformIndex π Z T.boundary))) U = c.coordIdeal (J.image tfun) :=
    hstep1.trans (hstep2.trans (hstep3.trans hstep4))
  obtain ⟨O, hOopen, hOne, hOsub⟩ := exists_isOpen_inter_subset_of_maximal
    ((↑(intersectionIdeal (transformedBoundary π Z T.boundary)
        (J.image (strictTransformIndex π Z T.boundary))).support : Set ↥X'))
    (Scheme.IdealSheafData.support (intersectionIdeal (transformedBoundary π Z T.boundary)
      (J.image (strictTransformIndex π Z T.boundary)))).isClosed C' hC'irr hC'sub hC'max
  have hξ'O : ξ' ∈ O := by
    obtain ⟨y, hyO, hyA⟩ := hOne
    exact (hξ'.mem_open_set_iff hOopen).mpr ⟨y, hOsub ⟨hyO, hyA⟩, hyO⟩
  obtain ⟨V, hξV, hVle⟩ :=
    AlgebraicGeometry.Scheme.exists_affineOpens_mem_le (X := X') (x := ξ')
      (U := U ⊓ ⟨O, hOopen⟩) ⟨hξU, hξ'O⟩
  have hVU : (V : X'.Opens) ≤ U := le_trans hVle inf_le_left
  have hZV : restrictIdeal (intersectionIdeal (transformedBoundary π Z T.boundary)
        (J.image (strictTransformIndex π Z T.boundary))) (V : X'.Opens)
      = (c.restrict hVU).coordIdeal (J.image tfun) :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU c _ _ hZU
  have hEV : restrictIdeal (Blowup.exceptionalIdeal π Z) (V : X'.Opens)
      = (c.restrict hVU).coordIdeal {t₀} :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU c _ _ hexcU
  refine not_inter_support_subset_support_of_notMem_coordIdeal (π ≫ T.structMap) V.2
    (c.restrict hVU) _ _ (J.image tfun) t₀ ht₀notin hZV hEV ξ' hξV hξ'A' ?_
  rintro x ⟨hxA, hxV⟩
  have hxmem := hVle hxV
  have hxO : x ∈ O := hxmem.2
  have hCE : C' ⊆ (↑(Blowup.exceptionalIdeal π Z).support : Set ↥X') :=
    (hξ'.mem_closed_set_iff
      (Scheme.IdealSheafData.support (Blowup.exceptionalIdeal π Z)).isClosed).mp hmem
  exact hCE (hOsub ⟨hxO, hxA⟩)

theorem intersectionComponents_transformedBoundary_of_isBlowupAlongIdealSheaf :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J₀ : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J₀,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J₀).subschemeι ⁻¹' ⋃₀ 𝒞)) (X' : Scheme.{u})
            (π : X' ⟶ T.scheme),
            Blowup.IsBlowupAlongIdealSheaf π (componentUnionIdeal T.boundary J₀ 𝒞 hop) →
              ∀ (J : Finset (Fin T.boundary.length)),
                ∀ C' ∈ intersectionComponents
                      (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
                      (Finset.image
                        (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary) J),
                  ∀ ξ' : ↥X', IsGenericPoint ξ' C' →
                    ξ' ∉ (Blowup.exceptionalIdeal π (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support ∧
                      ∃ C ∈ intersectionComponents T.boundary J,
                        C ∉ 𝒞 ∧
                          C' = closure (⇑π ⁻¹' C \
                              (↑(Blowup.exceptionalIdeal π
                                  (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support : Set ↥X')) ∧
                            ∀ ξ : ↥T.scheme, IsGenericPoint ξ C → π ξ' = ξ := by
  intro T hT J₀ 𝒞 h𝒞 hop X' π hπ J C' hC' ξ' hξ'
  have : IsNoetherian T.scheme := hT.isNoetherian
  have : IsNoetherian X' := isNoetherian_of_isBlowupAlongIdealSheaf hπ
  have : IsLocallyNoetherian X' := inferInstance
  have : NoetherianSpace ↥X' := inferInstance
  obtain ⟨hC'irr, hC'sub, hC'max⟩ := hC'
  have hsncZ : HasStrictNormalCrossingsWith T.structMap (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary :=
    MonomialCenterGeometry.hasStrictNormalCrossingsWith_componentUnionIdeal T hT J₀ 𝒞 h𝒞 hop
  have hξ'E : ξ' ∉ (Blowup.exceptionalIdeal π (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support :=
    genericPoint_notMem_support_exceptionalIdeal_consolidated433 T _ hsncZ X' π hπ J C' hC'irr hC'sub hC'max ξ' hξ'
  have hπξ' : π ξ' ∉ (componentUnionIdeal T.boundary J₀ 𝒞 hop).support := by
    intro hcon
    apply hξ'E
    have h0 : ξ' ∈ (↑((componentUnionIdeal T.boundary J₀ 𝒞 hop).comap π).support : Set ↥X') := by
      rw [support_comap_eq]
      exact hcon
    exact h0
  have hξ'A' : ξ' ∈ (intersectionIdeal
      (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
      (J.image (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary))).support :=
    hC'sub hξ'.mem
  have hξA : π ξ' ∈ (intersectionIdeal T.boundary J).support :=
    (mem_support_intersectionIdeal_transformedBoundary_iff_of_notMem_consolidated433 π _ T.boundary J ξ' hπξ').mp hξ'A'
  have hAclosed : IsClosed ((intersectionIdeal T.boundary J).support : Set ↥T.scheme) :=
    (Scheme.IdealSheafData.support (intersectionIdeal T.boundary J)).isClosed
  have hCsubA : closure ({π ξ'} : Set ↥T.scheme)
      ⊆ ((intersectionIdeal T.boundary J).support : Set ↥T.scheme) :=
    closure_minimal (Set.singleton_subset_iff.mpr hξA) hAclosed
  have hmax : ∀ D : Set ↥T.scheme, IsIrreducible D → closure ({π ξ'} : Set ↥T.scheme) ⊆ D →
      D ⊆ ((intersectionIdeal T.boundary J).support : Set ↥T.scheme) →
      D = closure ({π ξ'} : Set ↥T.scheme) := by
    intro D hDirr hCsubD hDsubA
    obtain ⟨η, hηspec⟩ : ∃ η : ↥T.scheme, IsGenericPoint η (closure D) :=
      QuasiSober.sober (IsIrreducible.closure hDirr) isClosed_closure
    have hπξ'D : π ξ' ∈ closure D :=
      subset_closure (hCsubD (subset_closure (Set.mem_singleton _)))
    have hηnotZ : η ∉ (componentUnionIdeal T.boundary J₀ 𝒞 hop).support := by
      intro hcon
      apply hπξ'
      have h1 : closure D
          ⊆ (↑(componentUnionIdeal T.boundary J₀ 𝒞 hop).support : Set ↥T.scheme) := by
        rw [← hηspec]
        exact closure_minimal (Set.singleton_subset_iff.mpr hcon)
          (Scheme.IdealSheafData.support (componentUnionIdeal T.boundary J₀ 𝒞 hop)).isClosed
      exact h1 hπξ'D
    have hs : π ξ' ∈ closure ({η} : Set ↥T.scheme) := by
      rw [hηspec]; exact hπξ'D
    obtain ⟨x, hxη, hξ'x⟩ := exists_lift_of_specializes_of_isBlowupAlongIdealSheaf π
      (componentUnionIdeal T.boundary J₀ 𝒞 hop) hπ η hηnotZ ξ' hπξ' hs
    have hxnotZ : π x ∉ (componentUnionIdeal T.boundary J₀ 𝒞 hop).support := by
      rw [hxη]; exact hηnotZ
    have hxA' : x ∈ (intersectionIdeal
        (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
        (J.image (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary))).support := by
      refine (mem_support_intersectionIdeal_transformedBoundary_iff_of_notMem_consolidated433 π _ T.boundary J x hxnotZ).mpr ?_
      have h1 : π x ∈ closure D := by
        rw [hxη]; exact hηspec.mem
      exact (closure_minimal hDsubA hAclosed) h1
    have hclxsub : closure ({x} : Set ↥X') ⊆ (↑(intersectionIdeal
        (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
        (J.image (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary))).support
          : Set ↥X') :=
      closure_minimal (Set.singleton_subset_iff.mpr hxA')
        (Scheme.IdealSheafData.support (intersectionIdeal
          (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
          (J.image (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)))).isClosed
    have hC'sub_x : C' ⊆ closure ({x} : Set ↥X') :=
      (hξ'.mem_closed_set_iff isClosed_closure).mp hξ'x
    have hclx : closure ({x} : Set ↥X') = C' :=
      hC'max _ (IsIrreducible.closure isIrreducible_singleton) hC'sub_x hclxsub
    have hxC' : x ∈ C' := by
      rw [← hclx]; exact subset_closure (Set.mem_singleton x)
    have hxclξ' : x ∈ closure ({ξ'} : Set ↥X') := by
      rw [hξ'.def]
      exact hxC'
    have hπxcl : π x ∈ closure ({π ξ'} : Set ↥T.scheme) := by
      have hsub : closure ({ξ'} : Set ↥X')
          ⊆ ⇑π.base ⁻¹' closure ({π ξ'} : Set ↥T.scheme) := by
        refine closure_minimal (Set.singleton_subset_iff.mpr ?_) ?_
        · exact subset_closure (Set.mem_singleton _)
        · exact isClosed_closure.preimage π.base.hom.continuous
      exact hsub hxclξ'
    refine Set.Subset.antisymm ?_ hCsubD
    have h2 : closure D ⊆ closure ({π ξ'} : Set ↥T.scheme) := by
      rw [← hηspec]
      refine closure_minimal (Set.singleton_subset_iff.mpr ?_) isClosed_closure
      rw [← hxη]; exact hπxcl
    exact fun z hz => h2 (subset_closure hz)
  have hCcomp : closure ({π ξ'} : Set ↥T.scheme) ∈ intersectionComponents T.boundary J :=
    ⟨IsIrreducible.closure isIrreducible_singleton, hCsubA, hmax⟩
  have hCnot : closure ({π ξ'} : Set ↥T.scheme) ∉ 𝒞 := by
    intro hcon
    apply hπξ'
    have h1 : π ξ' ∈ ⋃₀ 𝒞 := ⟨_, hcon, subset_closure (Set.mem_singleton _)⟩
    rw [← componentUnionIdeal_support_eq_sUnion T hT J₀ 𝒞 h𝒞 hop] at h1
    exact h1
  have hCeq : C' = closure ((⇑π ⁻¹' closure ({π ξ'} : Set ↥T.scheme)) \
      (↑(Blowup.exceptionalIdeal π (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support : Set ↥X')) := by
    apply Set.Subset.antisymm
    · rw [← hξ'.def]
      refine closure_mono (Set.singleton_subset_iff.mpr ?_)
      exact ⟨subset_closure (Set.mem_singleton _), hξ'E⟩
    · refine closure_minimal ?_ ?_
      · rintro x ⟨hx1, hx2⟩
        have hxnotZ : π x ∉ (componentUnionIdeal T.boundary J₀ 𝒞 hop).support := by
          intro hcon
          apply hx2
          have h0 : x ∈ (↑((componentUnionIdeal T.boundary J₀ 𝒞 hop).comap π).support
              : Set ↥X') := by
            rw [support_comap_eq]
            exact hcon
          exact h0
        obtain ⟨x₀, hx₀, hxx₀⟩ := exists_lift_of_specializes_of_isBlowupAlongIdealSheaf π
          (componentUnionIdeal T.boundary J₀ 𝒞 hop) hπ (π ξ') hπξ' x hxnotZ hx1
        have hx₀eq : x₀ = ξ' :=
          eq_of_isBlowupAlongIdealSheaf_of_notMem_support π (componentUnionIdeal T.boundary J₀ 𝒞 hop) hπ x₀ ξ'
            (by rw [hx₀]; exact hπξ') hπξ' hx₀
        rw [hx₀eq] at hxx₀
        rw [← hξ'.def]
        exact hxx₀
      · rw [← hξ'.def]
        exact isClosed_closure
  refine ⟨hξ'E, closure ({π ξ'} : Set ↥T.scheme), hCcomp, hCnot, hCeq, ?_⟩
  intro ξ hgen
  have h0 : IsGenericPoint (π ξ') (closure ({π ξ'} : Set ↥T.scheme)) := rfl
  exact IsGenericPoint.eq h0 hgen


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
section



structure MaxContactCoverProperties : Prop where
  strictTransform_admissible :
    ∀ (k : Type u) [Field k] [CharZero k] {P P₁ : Scheme.{u}}
      (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p]
      [LocallyOfFiniteType p]
      [IsLocallyNoetherian P₁]
      (π : P₁ ⟶ P) [LocallyOfFiniteType (π ≫ p)]
      (Z : P.IdealSheafData) (E : List P.IdealSheafData),
      HasStrictNormalCrossingsWith p Z E → Blowup.IsBlowupAlongIdealSheaf π Z →
      ∀ (A : P.IdealSheafData) (A₁ : P₁.IdealSheafData) (μ : ℕ), 1 ≤ μ →
        (∀ x : ↥P, orderAt A x ≤ (μ : ℕ∞)) →
        (Z.support : Set ↥P) ⊆ orderAtLeastLocus A μ →
        Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π →
        ∀ H : P.IdealSheafData, IsMaxContactHypersurface k p A μ H →
          IsMaxContactHypersurface k (π ≫ p) A₁ μ (Blowup.strictTransform π Z H)
  coSupport_le_preimage :
    ∀ {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData), Blowup.IsBlowupAlongIdealSheaf π Z →
      ∀ (A : X.IdealSheafData) (A₁ : X₁.IdealSheafData) (μ : ℕ),
        Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π →
        (Z.support : Set ↥X) ⊆ orderAtLeastLocus A μ →
        orderAtLeastLocus A₁ μ ⊆ (⇑π.base) ⁻¹' orderAtLeastLocus A μ
  schemeDim_level_le :
    ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
      krullDimSucc (s.toSequenceOfBlowups.schemeAt i) ≤ T.krullDimSucc
  exists_goodCover :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T,
        MaxContactReduction.IsMaxContactCover T D hv.locallyOfFiniteType
          (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)
  hasSNCWith_cons :
    ∀ (k : Type u) [Field k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
      [Smooth p] (Z H : P.IdealSheafData) (N : List P.IdealSheafData),
      Smooth (Z.subschemeι ≫ p) →
      InStrictNormalCrossingPosition p (H :: N) → HasStrictNormalCrossingsWith p Z N → H ≤ Z →
      HasStrictNormalCrossingsWith p Z (H :: N)
  valid_level :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
      (T.transformAt s i).IsAdmissible
  orderAt_level_le :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
        ∀ x : ↥(s.toSequenceOfBlowups.schemeAt i), orderAt (s.ideal i) x ≤ (T.mult : ℕ∞)
  coverTriple_dim_le :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      krullDimSucc (MaxContactCoverData.coverTriple T hv).scheme ≤ T.krullDimSucc
  coverTriple_valid :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
        (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) →
      (MaxContactCoverData.coverTriple T hv).IsAdmissible
  coverContact_admissible :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
        (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) →
      ∀ [LocallyOfFiniteType (MaxContactCoverData.coverTriple T hv).structMap],
        IsMaxContactHypersurface (MaxContactCoverData.coverTriple T hv).base
          (MaxContactCoverData.coverTriple T hv).structMap
          (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.tunedMult T)
          (MaxContactCoverData.coverMaxContactIdeal T hv)
  coverContact_snc :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
        (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) →
      InStrictNormalCrossingPosition (MaxContactCoverData.coverTriple T hv).structMap
        [MaxContactCoverData.coverMaxContactIdeal T hv]
  tuning : TunedSheafProperties.{u}

section
variable (hf : MaxContactCoverProperties.{u})
include hf

theorem MaxContactCoverProperties.krullDimSucc_schemeAt_le_dim {S : MarkedIdealWithBoundary.{u}} (hv : S.IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (i : ℕ) (hi : i ≤ s.length) :
    krullDimSucc (s.obj i) ≤ S.krullDimSucc :=
  hf.schemeDim_level_le S hv s.toMarkedSequenceOfBlowups i (by simpa using hi)

theorem MaxContactCoverProperties.derivedTriple_dim_le {T S : MarkedIdealWithBoundary.{u}} (hv : S.IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) (hdim : S.krullDimSucc ≤ T.krullDimSucc) :
    (MaxContactCoverData.derivedTriple S s hft extra keep).krullDimSucc ≤ T.krullDimSucc :=
  le_trans (hf.krullDimSucc_schemeAt_le_dim hv s s.length le_rfl) hdim


end

private theorem isMaxContactHypersurface_of_eq_consolidated339 {k : Type u} [Field k] {X : Scheme.{u}}
    {p q : X ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType p]
    [LocallyOfFiniteType q] (h : p = q) {A : X.IdealSheafData} {m : ℕ}
    {H : X.IdealSheafData} (hH : IsMaxContactHypersurface k p A m H) :
    IsMaxContactHypersurface k q A m H := by
  subst h
  exact hH

section
variable (hf : MaxContactCoverProperties.{u}) {T : MarkedIdealWithBoundary.{u}}
include hf

theorem MaxContactCoverProperties.isMaxContactHypersurface_strictTransform_succ (hv : T.IsAdmissible) (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (s : T.SequenceOfBlowups) (i : ℕ) (hi : i < s.toSequenceOfBlowups.length)
    [LocallyOfFiniteType (s.projectionToSpec i)]
    [LocallyOfFiniteType (s.projectionToSpec (i + 1))]
    (H : (s.toSequenceOfBlowups.schemeAt i).IdealSheafData)
    (hH : IsMaxContactHypersurface T.base (s.projectionToSpec i) (s.ideal i) T.mult H) :
    IsMaxContactHypersurface T.base (s.projectionToSpec (i + 1)) (s.ideal (i + 1)) T.mult
      (Blowup.strictTransform (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i) H) := by
  have hi' : i ≤ s.toSequenceOfBlowups.length := le_of_lt hi
  have hvi := hf.valid_level T hv s i hi'
  have hvi1 := hf.valid_level T hv s (i + 1) hi
  have : CharZero T.base := hv.charZero
  have : Smooth (s.projectionToSpec i) := hvi.smooth
  have hno : IsNoetherian (s.toSequenceOfBlowups.schemeAt (i + 1)) := hvi1.isNoetherian
  have : IsLocallyNoetherian (s.toSequenceOfBlowups.schemeAt (i + 1)) := inferInstance
  have : LocallyOfFiniteType
      (s.toSequenceOfBlowups.transitionMapSucc i ≫ s.projectionToSpec i) := by
    rw [← MarkedSequenceOfBlowups.projectionToSpec_succ]
    infer_instance
  have hsnc : HasStrictNormalCrossingsWith (s.projectionToSpec i) (s.toSequenceOfBlowups.center i) (s.boundary i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact s.center_snc i hi
  have key := hf.strictTransform_admissible T.base (s.projectionToSpec i)
    (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i) (s.boundary i) hsnc
    (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism i hi) (s.ideal i) (s.ideal (i + 1)) T.mult
    hv.one_le_mult (hf.orderAt_level_le T hv hord s i hi') (s.center_order i hi)
    (s.ideal_succ i hi) H hH
  exact isMaxContactHypersurface_of_eq_consolidated339 (MarkedSequenceOfBlowups.projectionToSpec_succ s i).symm key

theorem MaxContactCoverProperties.hasStrictNormalCrossingsWith_cons_of_le_center (s : T.SequenceOfBlowups) (i : ℕ) (hi : i < s.toSequenceOfBlowups.length)
    [Smooth (s.projectionToSpec i)]
    (H : (s.toSequenceOfBlowups.schemeAt i).IdealSheafData)
    (N : List (s.toSequenceOfBlowups.schemeAt i).IdealSheafData)
    (hsnc : InStrictNormalCrossingPosition (s.projectionToSpec i) (H :: N))
    (hZN : HasStrictNormalCrossingsWith (s.projectionToSpec i) (s.toSequenceOfBlowups.center i) N)
    (hHZ : H ≤ s.toSequenceOfBlowups.center i) :
    HasStrictNormalCrossingsWith (s.projectionToSpec i) (s.toSequenceOfBlowups.center i) (H :: N) := by
  have hsm : Smooth
      ((s.toSequenceOfBlowups.center i).subschemeι ≫ s.projectionToSpec i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact s.center_smooth i hi
  exact hf.hasSNCWith_cons T.base (s.projectionToSpec i) (s.toSequenceOfBlowups.center i) H N hsm hsnc hZN hHZ


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderBoundAlongSequence
section



theorem orderAt_ideal_le_mult_along_sequence (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) (s : T.SequenceOfBlowups) :
    ∀ (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
      ∀ x : ↥(s.toSequenceOfBlowups.schemeAt i), orderAt (s.ideal i) x ≤ (T.mult : ℕ∞) := by
  have : CharZero T.base := hT.charZero
  intro i
  induction i with
  | zero =>
      intro _ x
      have : IsOpenImmersion s.toSequenceOfBlowups.isoZero.hom := inferInstance
      rw [s.ideal_zero, orderAt_comap_of_isOpenImmersion]
      exact hord _
  | succ k ih =>
      intro hk x
      have hlt : k < s.toSequenceOfBlowups.length := hk
      have hprev := ih (le_of_lt hlt)
      have hnoeth : IsNoetherian (s.toSequenceOfBlowups.schemeAt (k + 1)) :=
        MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hT s (k + 1) hk
      have : IsLocallyNoetherian (s.toSequenceOfBlowups.schemeAt (k + 1)) := inferInstance
      have hsmooth : Smooth (s.projectionToSpec k) :=
        MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hT s k (le_of_lt hlt)
      have hS : HasStrictNormalCrossingsWith (s.projectionToSpec k) (s.toSequenceOfBlowups.center k) (s.boundary k) := by
        rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
        exact s.center_snc k hlt
      have hI : s.ideal k ≤ s.toSequenceOfBlowups.center k ^ T.mult :=
        le_pow_of_hasStrictNormalCrossingsWith (s.projectionToSpec k) (s.toSequenceOfBlowups.center k) (s.ideal k)
          (s.boundary k) hS T.mult (s.center_order k hlt)
      have hEq : s.ideal (k + 1) =
          controlledTransform (s.toSequenceOfBlowups.transitionMapSucc k) (s.toSequenceOfBlowups.center k)
            (s.ideal k) T.mult (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism k hlt) hI :=
        eq_controlledTransform_of_mul_eq_comap (s.toSequenceOfBlowups.transitionMapSucc k) (s.toSequenceOfBlowups.center k)
          (s.ideal k) T.mult (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism k hlt) hI
          (s.ideal (k + 1)) (s.ideal_succ k hlt)
      rw [hEq]
      exact orderAt_controlledTransform_le_of_forall_le T.base (s.projectionToSpec k)
        (s.toSequenceOfBlowups.transitionMapSucc k) (s.toSequenceOfBlowups.center k) (s.boundary k) hS
        (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism k hlt) (s.ideal k) T.mult hI hprev x

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.FaithfullyFlatDescent
section


section

section
variable {X' X : Scheme.{u}}

theorem IsStrictPullbackBlowupSeq.congr_hom {g g' : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (h : IsStrictPullbackBlowupSeq g t s) (hg : g = g') :
    IsStrictPullbackBlowupSeq g' t s := by
  subst hg
  exact h

theorem IsStrictPullbackBlowupSeq.congr_sourceSeq {g : X' ⟶ X}
    {t t' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (h : IsStrictPullbackBlowupSeq g t s) (ht : t = t') :
    IsStrictPullbackBlowupSeq g t' s := by
  subst ht
  exact h


end

theorem IsStrictPullbackBlowupSeq.baseChange_of_comp {Q Y X : Scheme.{u}} {φ : Q ⟶ Y} {h : Y ⟶ X}
    [Flat φ] [Flat h]
    {u : SequenceOfBlowups Q} {s : SequenceOfBlowups X}
    (hu : IsStrictPullbackBlowupSeq (φ ≫ h) u s) :
    IsStrictPullbackBlowupSeq φ u (s.baseChange h) := by
  have ht : IsStrictPullbackBlowupSeq h (s.baseChange h) s :=
    isStrictPullbackSequenceOfBlowups_baseChange s h
  have hw : IsStrictPullbackBlowupSeq φ ((s.baseChange h).baseChange φ) (s.baseChange h) :=
    isStrictPullbackSequenceOfBlowups_baseChange (s.baseChange h) φ
  have hwc : IsStrictPullbackBlowupSeq (φ ≫ h) ((s.baseChange h).baseChange φ) s := hw.comp ht
  exact hw.of_isomorphic_pullback (hwc.isomorphic hu)

theorem comap_ne_top_iff_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.Surjective f] (J : Y.IdealSheafData) :
    J.comap f ≠ ⊤ ↔ J ≠ ⊤ := by
  have hsurj : Function.Surjective f.base := AlgebraicGeometry.Surjective.surj
  have htop : (⊤ : Y.IdealSheafData).comap f = ⊤ := by simp
  have hpre : ((J.comap f).support : Set ↥X) = f.base ⁻¹' ((J.support : Set ↥Y)) := by simp
  have hbot : J.support = ⊥ → J = ⊤ := by simp
  constructor
  · intro h hJ
    apply h
    rw [hJ, htop]
  · intro hJ h
    apply hJ
    apply hbot
    apply SetLike.ext'
    have hsupp : ((J.support : Set ↥Y)) = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hsurj y
      have hx : x ∈ ((J.comap f).support : Set ↥X) := by
        rw [hpre]
        exact Set.mem_preimage.mpr hy
      rw [h] at hx
      simp at hx
    simpa using hsupp

namespace MaxContactFunctoriality

theorem isMaxContactHypersurface_of_triple_eq {T₁ T₂ : MarkedIdealWithBoundary.{u}} (hT : T₁ = T₂)
    (hft₁ : LocallyOfFiniteType T₁.structMap)
    (hft₂ : LocallyOfFiniteType T₂.structMap)
    (H₁ : T₁.scheme.IdealSheafData) (H₂ : T₂.scheme.IdealSheafData) (hH : HEq H₁ H₂)
    (h : haveI := hft₂;
      IsMaxContactHypersurface T₂.base T₂.structMap T₂.ideal T₂.mult H₂) :
    haveI := hft₁;
      IsMaxContactHypersurface T₁.base T₁.structMap T₁.ideal T₁.mult H₁ := by
  subst hT
  have hHe : H₁ = H₂ := eq_of_heq hH
  subst hHe
  exact h

theorem inStrictNormalCrossingPosition_of_triple_eq {T₁ T₂ : MarkedIdealWithBoundary.{u}} (hT : T₁ = T₂)
    (L₁ : List T₁.scheme.IdealSheafData) (L₂ : List T₂.scheme.IdealSheafData) (hL : HEq L₁ L₂)
    (h : InStrictNormalCrossingPosition T₂.structMap L₂) :
    InStrictNormalCrossingPosition T₁.structMap L₁ := by
  subst hT
  have hLe : L₁ = L₂ := eq_of_heq hL
  subst hLe
  exact h

theorem orderAtLeastLocus_comap_eq_empty (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) {Y : Scheme.{u}}
    (h : Y ⟶ T.scheme) [Smooth h]
    (hemp : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)) :
    orderAtLeastLocus (T.ideal.comap h) T.mult = (∅ : Set ↥Y) := by
  have hcz : CharZero T.base := by
    cases hv
    assumption
  have hsm : Smooth T.structMap := by
    cases hv
    assumption
  rw [orderAtLeastLocus_comap T.base T.structMap h T.ideal T.mult, hemp, Set.preimage_empty]

private theorem derivedTriple_dim_le_consolidated378 (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u})
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) :
    (MaxContactCoverData.derivedTriple S s hft extra keep).krullDimSucc ≤ S.krullDimSucc :=
  hstar.schemeDim_level_le S hV s.toMarkedSequenceOfBlowups s.length le_rfl

section
variable (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u}) (A : ℕ → PrincipalizationAssignment.{u}) (T₁ T₂ : MarkedIdealWithBoundary.{u}) (hdim : T₁.krullDimSucc ≤ T₂.krullDimSucc) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible) (hS : S.krullDimSucc ≤ T₁.krullDimSucc)
include hstar hdim hV hS

private theorem appendLowerDimReduction_congr_of_dim_le_consolidated378 (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (extra : List (s.obj s.length).IdealSheafData) (keep n : ℕ) :
    MaxContactReduction.appendLowerDimReduction hinv T₁ (lowerDimensionalFamily A T₁) S s extra keep n =
      MaxContactReduction.appendLowerDimReduction hinv T₂ (lowerDimensionalFamily A T₂) S s extra keep n := by
  by_cases hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap)
  · have h1 : (MaxContactCoverData.derivedTriple S s hft extra keep).krullDimSucc ≤ T₁.krullDimSucc :=
      le_trans (derivedTriple_dim_le_consolidated378 hstar S hV s hft extra keep) hS
    exact (MaxContactCoverData.appendLowerDimReduction_eq_concatOfIsMarked hinv T₁ (lowerDimensionalFamily A T₁) S s extra keep n
        hft h1).trans
      (MaxContactCoverData.appendLowerDimReduction_eq_concatOfIsMarked hinv T₂ (lowerDimensionalFamily A T₂) S s extra keep n
        hft (le_trans h1 hdim)).symm
  · exact (MaxContactCoverData.appendLowerDimReduction_of_not_locallyOfFiniteType hinv T₁ (lowerDimensionalFamily A T₁) S s extra
        keep n hft).trans
      (MaxContactCoverData.appendLowerDimReduction_of_not_locallyOfFiniteType hinv T₂ (lowerDimensionalFamily A T₂) S s extra
        keep n hft).symm

private theorem separateBoundary_congr_of_dim_le_consolidated378 (j : ℕ) :
    MaxContactReduction.separateBoundary hinv T₁ (lowerDimensionalFamily A T₁) S j =
      MaxContactReduction.separateBoundary hinv T₂ (lowerDimensionalFamily A T₂) S j := by
  induction j with
  | zero =>
    rw [MaxContactCoverData.separateBoundary_zero hinv T₁ (lowerDimensionalFamily A T₁) S,
      MaxContactCoverData.separateBoundary_zero hinv T₂ (lowerDimensionalFamily A T₂) S]
  | succ n ih =>
    rw [MaxContactCoverData.separateBoundary_succ hinv T₁ (lowerDimensionalFamily A T₁) S n,
      MaxContactCoverData.separateBoundary_succ hinv T₂ (lowerDimensionalFamily A T₂) S n, ih]
    exact appendLowerDimReduction_congr_of_dim_le_consolidated378 hstar hinv A T₁ T₂ hdim S hV hS
      (MaxContactReduction.separateBoundary hinv T₂ (lowerDimensionalFamily A T₂) S n) [] 0 n

theorem reduceAlongHypersurface_congr_of_dim_le (H : S.scheme.IdealSheafData) :
    MaxContactReduction.reduceAlongHypersurface hinv T₁ (lowerDimensionalFamily A T₁) S H =
      MaxContactReduction.reduceAlongHypersurface hinv T₂ (lowerDimensionalFamily A T₂) S H := by
  rw [MaxContactCoverData.reduceAlongHypersurface_eq_appendLowerDimReduction hinv T₁ (lowerDimensionalFamily A T₁) S H,
    MaxContactCoverData.reduceAlongHypersurface_eq_appendLowerDimReduction hinv T₂ (lowerDimensionalFamily A T₂) S H,
    separateBoundary_congr_of_dim_le_consolidated378 hstar hinv A T₁ T₂ hdim S hV hS S.boundary.length]
  exact appendLowerDimReduction_congr_of_dim_le_consolidated378 hstar hinv A T₁ T₂ hdim S hV hS _ _ S.boundary.length 0


end

theorem reduceAlongHypersurface_toSequenceOfBlowups_heq (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : (S : MarkedIdealWithBoundary.{u}) → S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups)
    {S₁ S₂ : MarkedIdealWithBoundary.{u}} (hS : S₁ = S₂)
    (H₁ : S₁.scheme.IdealSheafData) (H₂ : S₂.scheme.IdealSheafData) (hH : HEq H₁ H₂) :
    HEq (MaxContactReduction.reduceAlongHypersurface hinv T resolveLower S₁ H₁).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv T resolveLower S₂ H₂).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  subst hS
  have hHe : H₁ = H₂ := eq_of_heq hH
  subst hHe
  exact HEq.refl _

def MarkingDescends (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment.{u}) : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T) (d : BlowupSequenceData T.scheme),
    IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
        (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toSequenceOfBlowups d.toSequenceOfBlowups →
      d.IsMarked T.structMap T.ideal T.mult T.boundary

def CoverFaithfullyFlat (P : ℕ → Prop) : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T),
    AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap T h.valid) ∧
      Flat (MaxContactCoverData.coverMap T h.valid)

def DropTrivialBoundaryAdmissible : Prop :=
  ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → (MaxContactReduction.dropTrivialBoundary T).IsAdmissible

def MarkedOfMarkedDropTrivialBoundary : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ d : BlowupSequenceData T.scheme,
    d.IsMarked T.structMap T.ideal T.mult (MaxContactReduction.dropTrivialBoundary T).boundary →
      d.IsMarked T.structMap T.ideal T.mult T.boundary

theorem OrderReductionHypotheses.of_dropTrivialBoundaryAdmissible {P : ℕ → Prop} {T : MarkedIdealWithBoundary.{u}} (h : OrderReductionHypotheses P T)
    (htv : DropTrivialBoundaryAdmissible.{u}) : OrderReductionHypotheses P (MaxContactReduction.dropTrivialBoundary T) := by
  refine ⟨?_, ?_, ?_, htv T h.valid⟩
  · exact h.dim_prop
  · exact h.orderLE
  · exact h.coSupport_nonempty

theorem exists_isStrictPullback_cover_dropTrivialBoundary {hinv : ComapIsoInvariance.{u}} {P : ℕ → Prop}
    {A : ℕ → PrincipalizationAssignment.{u}} (hstar : CoverSequenceProperties hinv P A)
    (hdesc : MarkingDescends hinv P A) (htv : DropTrivialBoundaryAdmissible.{u}) (htm : MarkedOfMarkedDropTrivialBoundary.{u})
    (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T) :
    ∃ d : BlowupSequenceData T.scheme,
      IsStrictPullbackBlowupSeq
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid)
          (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid hinv
            (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toSequenceOfBlowups d.toSequenceOfBlowups ∧
        (maxContactPrincipalization hinv A T).toSequenceOfBlowups = d.toSequenceOfBlowups := by
  obtain ⟨d0, hd0⟩ := hstar.descends (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv)
  obtain ⟨d, hdsome⟩ :=
    MaxContactCoverData.exists_descendStrictPullback_eq_some
      (T := MaxContactReduction.dropTrivialBoundary T)
      (S := MaxContactCoverData.coverTriple (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid)
      (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid)
      (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid hinv
        (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T)))
      ⟨d0, hd0⟩
  have hpb : IsStrictPullbackBlowupSeq
      (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid)
      (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid hinv
        (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toSequenceOfBlowups d.toSequenceOfBlowups :=
    MaxContactCoverData.isStrictPullbackBlowupSeq_of_descendStrictPullback_eq_some _ _ hdsome
  have hm0 : d.IsMarked (MaxContactReduction.dropTrivialBoundary T).structMap (MaxContactReduction.dropTrivialBoundary T).ideal
      (MaxContactReduction.dropTrivialBoundary T).mult (MaxContactReduction.dropTrivialBoundary T).boundary :=
    hdesc (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv) d hpb
  have hm : d.IsMarked T.structMap T.ideal T.mult T.boundary := htm T h.valid d hm0
  refine ⟨d, hpb, ?_⟩
  rw [maxContactPrincipalization_apply,
    MaxContactCoverData.reduceOrder_eq_asMarkedSeq hinv T (lowerDimensionalFamily A T) h.valid h.orderAtLeastLocus_ne_empty
      (h.of_dropTrivialBoundaryAdmissible htv).valid d hdsome]
  exact MaxContactCoverData.asMarkedSeq_toSequenceOfBlowups T d hm

end MaxContactFunctoriality


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactHypersurfaceTransform
section


section

theorem isMaxContactHypersurface_of_eq_of_eq_of_eq (k : Type u) [Field k] {P : Scheme.{u}}
    {p p' : P ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType p]
    [LocallyOfFiniteType p']
    {A A' H H' : P.IdealSheafData} {μ : ℕ}
    (hp : p = p') (hA : A = A') (hH : H = H')
    (h : IsMaxContactHypersurface k p A μ H) :
    IsMaxContactHypersurface k p' A' μ H' := by
  subst hp hA hH
  exact h

private theorem locallyOfFiniteType_of_smooth_morphism_consolidated364 {X Y : Scheme.{u}} {f : X ⟶ Y}
    (h : Smooth f) : LocallyOfFiniteType f := by
  have := h
  infer_instance

section
variable (k : Type u)

private theorem isMaxContactHypersurface_congr_consolidated364 [instk : Field k] {P : Scheme.{u}}
    {p p' : P ⟶ Spec (CommRingCat.of k)}
    (i1 : LocallyOfFiniteType p)
    (i2 : LocallyOfFiniteType p')
    {A A' H H' : P.IdealSheafData} {μ : ℕ}
    (hp : p = p') (hA : A = A') (hH : H = H')
    (h : @IsMaxContactHypersurface k instk P p i1 A μ H) :
    @IsMaxContactHypersurface k instk P p' i2 A' μ H' := by
  subst hp hA hH
  exact h

private theorem isMaxContactHypersurface_comap_iso_consolidated364 [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) [Smooth q]
    [LocallyOfFiniteType q] (e : X ≅ Y)
    [LocallyOfFiniteType (e.hom ≫ q)]
    (A : Y.IdealSheafData) (m : ℕ) (H : Y.IdealSheafData)
    (h : IsMaxContactHypersurface k q A m H) :
    IsMaxContactHypersurface k (e.hom ≫ q) (A.comap e.hom) m (H.comap e.hom) := by
  have : Smooth e.hom := inferInstance
  have hmax : maxContactIdeal k (e.hom ≫ q) (A.comap e.hom) m
      = (maxContactIdeal k q A m).comap e.hom := by
    rw [maxContactIdeal_eq_derivIdealSheafIterate, maxContactIdeal_eq_derivIdealSheafIterate]
    exact derivIdealSheafIterate_comap k q e.hom (m - 1) A
  rw [isMaxContactHypersurface_iff] at h
  rw [isMaxContactHypersurface_iff]
  intro x
  obtain ⟨U, hU, hxU, hcase⟩ := h (e.hom.base x)
  refine ⟨(TopologicalSpace.Opens.map e.hom.base).obj U, hU.preimage_of_isIso e.hom, hxU, ?_⟩
  rcases hcase with ⟨hdisj, htop⟩ | ⟨n, c, j, hHU, hmc⟩
  · left
    constructor
    · have hd : Disjoint (⇑e.hom.base ⁻¹' orderAtLeastLocus A m) (⇑e.hom.base ⁻¹' (U : Set ↥Y)) :=
        hdisj.preimage _
      rw [orderAtLeastLocus_comap_iso_hom_eq_preimage]
      exact hd
    · rw [restrictIdeal_comap, htop]
      simp
  · right
    refine ⟨n, EtaleChart.ofIso q e c, j, ?_, ?_⟩
    · rw [restrictIdeal_comap, hHU, EtaleChart.ofIso_coordIdeal]
    · rw [isMaxContactCoord_iff] at hmc
      rw [isMaxContactCoord_iff, EtaleChart.ofIso_coordIdeal, hmax, restrictIdeal_comap]
      exact Scheme.IdealSheafData.comap_mono _ hmc


end

theorem isMaxContactHypersurface_iteratedStrictTransform (hstar : MaxContactCoverProperties.{u})
    (S : MarkedIdealWithBoundary.{u}) (hv : S.IsAdmissible)
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (H : S.scheme.IdealSheafData)
    (hH : @IsMaxContactHypersurface S.base _ S.scheme S.structMap hv.locallyOfFiniteType
      S.ideal S.mult H)
    (u : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (t : ℕ) (ht : t ≤ u.length)
    [LocallyOfFiniteType (u.proj t ≫ S.structMap)] :
    IsMaxContactHypersurface S.base (u.proj t ≫ S.structMap) (u.ideal t) S.mult
      (MaxContactReduction.iteratedStrictTransform u H t) := by
  have hlft : ∀ i : ℕ, i ≤ u.length →
      LocallyOfFiniteType (u.proj i ≫ S.structMap) := by
    intro i hi
    have hsm : Smooth (u.toMarkedSequenceOfBlowups.projectionToSpec i) :=
      MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hv u.toMarkedSequenceOfBlowups i
        (by rw [MarkedBlowupSequenceData.toMarkedSequence_length]; exact hi)
    rw [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec] at hsm
    exact locallyOfFiniteType_of_smooth_morphism_consolidated364 hsm
  have key : ∀ i : ℕ, i ≤ u.length →
      ∀ inst : LocallyOfFiniteType (u.proj i ≫ S.structMap),
        @IsMaxContactHypersurface S.base _ _ (u.proj i ≫ S.structMap) inst
          (u.ideal i) S.mult (MaxContactReduction.iteratedStrictTransform u H i) := by
    intro i
    induction i with
    | zero =>
        intro _ inst
        have hiso : LocallyOfFiniteType (u.isoZero.hom ≫ S.structMap) := by
          rw [← u.proj_zero]
          exact inst
        refine isMaxContactHypersurface_congr_consolidated364 S.base hiso inst ?_ (u.ideal_zero).symm
          (MaxContactReduction.iteratedStrictTransform_zero u H).symm
          (@isMaxContactHypersurface_comap_iso_consolidated364 S.base _ _ _ S.structMap hv.smooth
            hv.locallyOfFiniteType u.isoZero hiso S.ideal S.mult H hH)
        rw [u.proj_zero]
    | succ j ih =>
        intro hj inst
        have hjl : j < u.length := hj
        have instj : LocallyOfFiniteType (u.proj j ≫ S.structMap) :=
          hlft j (le_of_lt hjl)
        have instsj : LocallyOfFiniteType (u.toMarkedSequenceOfBlowups.projectionToSpec j) := by
          rw [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec]
          exact instj
        have instsj1 : LocallyOfFiniteType
            (u.toMarkedSequenceOfBlowups.projectionToSpec (j + 1)) := by
          rw [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec]
          exact inst
        have hlt : j < u.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length := by
          rw [MarkedBlowupSequenceData.toMarkedSequence_length]
          exact hjl
        have hadm := isMaxContactHypersurface_congr_consolidated364 S.base instj instsj
          (MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec u j).symm
          (MarkedBlowupSequenceData.toMarkedSequence_ideal u j).symm
          (rfl : MaxContactReduction.iteratedStrictTransform u H j = MaxContactReduction.iteratedStrictTransform u H j)
          (ih (le_of_lt hjl) instj)
        have hstep := @MaxContactCoverProperties.isMaxContactHypersurface_strictTransform_succ hstar S hv hord u.toMarkedSequenceOfBlowups
          j hlt instsj instsj1 (MaxContactReduction.iteratedStrictTransform u H j) hadm
        have hHeq : Blowup.strictTransform (u.toMarkedSequenceOfBlowups.transitionMapSucc j) (u.toMarkedSequenceOfBlowups.center j)
            (MaxContactReduction.iteratedStrictTransform u H j) = MaxContactReduction.iteratedStrictTransform u H (j + 1) := by
          simp only [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, MarkedBlowupSequenceData.toMarkedSequence_center,
            MaxContactReduction.iteratedStrictTransform_succ]
          rfl
        exact isMaxContactHypersurface_congr_consolidated364 S.base instsj1 inst
          (MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec u (j + 1))
          (MarkedBlowupSequenceData.toMarkedSequence_ideal u (j + 1)) hHeq hstep
  exact key t ht (hlft t ht)

private theorem radical_le_of_isReduced_subscheme_consolidated364 {X : Scheme.{u}} (I : X.IdealSheafData)
    (hred : IsReduced I.subscheme) : I.radical ≤ I := by
  have := hred
  have hker : Scheme.Hom.ker I.subschemeι = I := Scheme.IdealSheafData.ker_subschemeι I
  have hmem : I ≤ Scheme.IdealSheafData.ofIdeals
      (fun U : X.affineOpens =>
        RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.app I.subschemeι U.1))) :=
    le_of_eq hker.symm
  have hle := Scheme.IdealSheafData.le_ofIdeals_iff.mp hmem
  have hgoal : I.radical ≤ Scheme.IdealSheafData.ofIdeals
      (fun U : X.affineOpens =>
        RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.app I.subschemeι U.1))) := by
    refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr ?_
    intro U
    rw [Scheme.IdealSheafData.radical_ideal]
    intro x hx
    obtain ⟨n, hn⟩ := hx
    have hR := AlgebraicGeometry.IsReduced.component_reduced
      (X := I.subscheme) (I.subschemeι ⁻¹ᵁ U.1)
    refine RingHom.mem_ker.mpr (hR.eq_zero _ ⟨n, ?_⟩)
    rw [← map_pow]
    exact RingHom.mem_ker.mp (hle U hn)
  exact le_trans hgoal (le_of_eq hker)

theorem inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop (hstar : MaxContactCoverProperties.{u})
    (S : MarkedIdealWithBoundary.{u}) (hv : S.IsAdmissible)
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (H : S.scheme.IdealSheafData)
    (hH : @IsMaxContactHypersurface S.base _ S.scheme S.structMap hv.locallyOfFiniteType
      S.ideal S.mult H)
    (u : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (h0 : InStrictNormalCrossingPosition (u.proj 0 ≫ S.structMap) [MaxContactReduction.iteratedStrictTransform u H 0])
    (t : ℕ) (ht : t ≤ u.length) :
    InStrictNormalCrossingPosition (u.proj t ≫ S.structMap)
      (MaxContactReduction.iteratedStrictTransform u H t :: (u.boundary t).drop S.boundary.length) := by
  have hsmooth : ∀ i : ℕ, i ≤ u.length →
      Smooth (u.proj i ≫ S.structMap) := by
    intro i hi
    have hsm : Smooth (u.toMarkedSequenceOfBlowups.projectionToSpec i) :=
      MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hv u.toMarkedSequenceOfBlowups i
        (by rw [MarkedBlowupSequenceData.toMarkedSequence_length]; exact hi)
    rw [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec] at hsm
    exact hsm
  have hkey : ∀ i : ℕ, i < u.length →
      MaxContactReduction.iteratedStrictTransform u H i ≤ u.center i := by
    intro i hi
    have hsmi : Smooth (u.proj i ≫ S.structMap) := hsmooth i (le_of_lt hi)
    have hlfti : LocallyOfFiniteType (u.proj i ≫ S.structMap) :=
      locallyOfFiniteType_of_smooth_morphism_consolidated364 hsmi
    have hcz : CharZero S.base := hv.charZero
    have hadm := isMaxContactHypersurface_iteratedStrictTransform hstar S hv hord H hH u i (le_of_lt hi)
    have hcos := hadm.orderAtLeastLocus_subset_support hv.one_le_mult
    have hsupp : (((u.center i).support : Set ↥(u.obj i))) ⊆
        (((MaxContactReduction.iteratedStrictTransform u H i).support : Set ↥(u.obj i))) :=
      Set.Subset.trans (u.center_order i hi) hcos
    have hsupp' : (u.center i).support ≤ (MaxContactReduction.iteratedStrictTransform u H i).support :=
      SetLike.coe_subset_coe.mp hsupp
    have h1 : MaxContactReduction.iteratedStrictTransform u H i ≤
        Scheme.IdealSheafData.vanishingIdeal (u.center i).support :=
      (Scheme.IdealSheafData.gc _ _).mp hsupp'
    rw [Scheme.IdealSheafData.vanishingIdeal_support] at h1
    have hsmZ : Smooth
        ((u.center i).subschemeι ≫ (u.proj i ≫ S.structMap)) := u.center_smooth i hi
    have hred : IsReduced (u.center i).subscheme :=
      isReduced_of_smooth ((u.center i).subschemeι ≫ (u.proj i ≫ S.structMap))
    exact le_trans h1 (radical_le_of_isReduced_subscheme_consolidated364 (u.center i) hred)
  revert ht
  induction t with
  | zero =>
      intro _
      have hb : (u.boundary 0).drop S.boundary.length = [] := by
        rw [u.boundary_zero]
        simp
      rw [hb]
      exact h0
  | succ j ih =>
      intro hj
      have hjl : j < u.length := hj
      have hjle : j ≤ u.length := le_of_lt hjl
      have hsmj : Smooth (u.proj j ≫ S.structMap) := hsmooth j hjle
      have hlj : LocallyOfFiniteType (u.proj j ≫ S.structMap) :=
        locallyOfFiniteType_of_smooth_morphism_consolidated364 hsmj
      have hnoeth : IsNoetherian (u.obj (j + 1)) :=
        MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hv u.toMarkedSequenceOfBlowups (j + 1)
          (by rw [MarkedBlowupSequenceData.toMarkedSequence_length]; exact hj)
      have hnsp : TopologicalSpace.NoetherianSpace ↥(u.obj (j + 1)) := inferInstance
      have hsncj : InStrictNormalCrossingPosition (u.proj j ≫ S.structMap)
          (MaxContactReduction.iteratedStrictTransform u H j :: (u.boundary j).drop S.boundary.length) := ih hjle
      have hZN : HasStrictNormalCrossingsWith (u.proj j ≫ S.structMap) (u.center j)
          ((u.boundary j).drop S.boundary.length) := by
        have hfull := u.center_snc j hjl
        rw [← List.take_append_drop S.boundary.length (u.boundary j)] at hfull
        exact HasStrictNormalCrossingsWith.of_append hfull
      have hcons : HasStrictNormalCrossingsWith (u.proj j ≫ S.structMap) (u.center j)
          (MaxContactReduction.iteratedStrictTransform u H j :: (u.boundary j).drop S.boundary.length) := by
        have hsm' : Smooth (u.toMarkedSequenceOfBlowups.projectionToSpec j) := by
          rw [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec]
          exact hsmj
        have hlt : j < u.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length := by
          rw [MarkedBlowupSequenceData.toMarkedSequence_length]
          exact hjl
        have hsnc' : InStrictNormalCrossingPosition (u.toMarkedSequenceOfBlowups.projectionToSpec j)
            (MaxContactReduction.iteratedStrictTransform u H j :: (u.boundary j).drop S.boundary.length) := by
          rw [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec]
          exact hsncj
        have hZN' : HasStrictNormalCrossingsWith (u.toMarkedSequenceOfBlowups.projectionToSpec j) (u.toMarkedSequenceOfBlowups.center j)
            ((u.boundary j).drop S.boundary.length) := by
          rw [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec, MarkedBlowupSequenceData.toMarkedSequence_center]
          exact hZN
        have hHZ' : MaxContactReduction.iteratedStrictTransform u H j ≤ u.toMarkedSequenceOfBlowups.center j := by
          rw [MarkedBlowupSequenceData.toMarkedSequence_center]
          exact hkey j hjl
        have hres := @MaxContactCoverProperties.hasStrictNormalCrossingsWith_cons_of_le_center hstar S u.toMarkedSequenceOfBlowups j hlt hsm'
          (MaxContactReduction.iteratedStrictTransform u H j) ((u.boundary j).drop S.boundary.length)
          hsnc' hZN' hHZ'
        rw [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec, MarkedBlowupSequenceData.toMarkedSequence_center] at hres
        exact hres
      have hbd : (u.boundary (j + 1)).drop S.boundary.length =
          ((u.boundary j).drop S.boundary.length).map
              (Blowup.strictTransform (u.map j) (u.center j)) ++
            [Blowup.exceptionalIdeal (u.map j) (u.center j)] :=
        u.boundary_succ_drop hjl S.boundary.length
          (by rw [u.boundary_length j hjle]; omega)
      rw [hbd, MaxContactReduction.iteratedStrictTransform_succ, u.proj_succ j, Category.assoc]
      exact inStrictNormalCrossingPosition_strictTransform_cons_append (u.proj j ≫ S.structMap) (u.map j)
        (u.center j) (MaxContactReduction.iteratedStrictTransform u H j)
        ((u.boundary j).drop S.boundary.length) (u.isBlowup j hjl) hsncj hcons


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
section


section

theorem orderAtLeastLocus_comap_iso {X Y : Scheme.{u}} (e : X ≅ Y) (J : Y.IdealSheafData) (n : ℕ) :
    orderAtLeastLocus (J.comap e.hom) n = ⇑e.hom ⁻¹' orderAtLeastLocus J n :=
  orderAtLeastLocus_comap_iso_hom_eq_preimage e J n

namespace BlowupSequenceData

def iteratedStrictTransform {X : Scheme.{u}} (d : BlowupSequenceData X) (i : ℕ) (D : X.IdealSheafData) :
    (d.obj i).IdealSheafData :=
  Nat.rec (motive := fun j => (d.obj j).IdealSheafData) (D.comap d.isoZero.hom)
    (fun j J => Blowup.strictTransform (d.map j) (d.center j) J) i

section
variable {X : Scheme.{u}} (d : BlowupSequenceData X)

@[simp] theorem iteratedStrictTransform_zero (D : X.IdealSheafData) :
    d.iteratedStrictTransform 0 D = D.comap d.isoZero.hom := rfl

@[simp] theorem iteratedStrictTransform_succ (i : ℕ)
    (D : X.IdealSheafData) :
    d.iteratedStrictTransform (i + 1) D = Blowup.strictTransform (d.map i) (d.center i) (d.iteratedStrictTransform i D) := rfl

theorem boundary_cons (D : X.IdealSheafData)
    (L : List X.IdealSheafData) (i : ℕ) :
    d.boundaryFrom (D :: L) i = d.iteratedStrictTransform i D :: d.boundaryFrom L i := by
  induction i with
  | zero => simp [BlowupSequenceData.boundary_zero]
  | succ i ih => simp [BlowupSequenceData.boundary_succ, ih]

theorem boundary_append (L₁ L₂ : List X.IdealSheafData) (i : ℕ) :
    d.boundaryFrom (L₁ ++ L₂) i = L₁.map (d.iteratedStrictTransform i) ++ d.boundaryFrom L₂ i := by
  induction L₁ with
  | nil => simp
  | cons D L ih => simp [BlowupSequenceData.boundary_cons, ih]


end

end BlowupSequenceData

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

private theorem isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal_consolidated365 {Y Y' : Scheme.{u}} (π : Y' ⟶ Y)
    (J : Y.IdealSheafData) (h : Blowup.IsBlowupAlongIdealSheaf π J) : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π J) := h.1

private theorem eq_of_exceptionalIdeal_pow_mul_eq_consolidated365 (s : MarkedBlowupSequenceData p I m E) :
    ∀ i < s.length, ∀ A B : (s.obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (s.map i) (s.center i) ^ m * A = (s.ideal i).comap (s.map i) →
      Blowup.exceptionalIdeal (s.map i) (s.center i) ^ m * B = (s.ideal i).comap (s.map i) → A = B := by
  intro i hi A B hA hB
  exact ((isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal_consolidated365 (s.map i) (s.center i) (s.isBlowup i hi)).pow
    m).eq_of_mul_eq_mul (hA.trans hB.symm)

section
variable (s : MarkedBlowupSequenceData p I m E) (i : ℕ) (hi : i ≤ s.length)
include hi

theorem controlledTransform_eq_ideal :
    s.controlledTransform I m i = s.ideal i :=
  (s.controlledTransform_and_boundary_eq_of_cancel (eq_of_exceptionalIdeal_pow_mul_eq_consolidated365 s) i hi).1

theorem toBlowupSequenceData_boundary_eq :
    s.boundaryFrom E i = s.boundary i := by
  revert hi
  induction i with
  | zero =>
      intro _
      simp [BlowupSequenceData.boundary_zero, s.boundary_zero]
  | succ j ih =>
      intro hi
      have hj : j < s.length := hi
      rw [BlowupSequenceData.boundary_succ, ih (le_of_lt hj), s.boundary_succ j hj]


end

end MarkedBlowupSequenceData

private theorem foldr_lcm_consecutive_ne_zero_consolidated365 (n : ℕ) :
    ∀ s : ℕ, s ≠ 0 → List.foldr Nat.lcm 1 (List.range' s n) ≠ 0 := by
  induction n with
  | zero => intro s _; simp
  | succ n ih =>
      intro s hs
      have hr : List.range' s (n + 1) 1 = s :: List.range' (s + 1) n 1 := rfl
      rw [hr, List.foldr_cons]
      exact Nat.lcm_ne_zero hs (ih (s + 1) (by omega))

theorem one_le_tuningExponent (m : ℕ) : 1 ≤ tuningExponent m := by
  rcases Nat.lt_or_ge m 2 with h | h
  · have h1 : m ≤ 1 := by omega
    exact le_of_eq (tuningExponent_of_le_one h1).symm
  · have hl : lcmUpTo m ≠ 0 := by
      rw [lcmUpTo_eq_foldr]
      exact foldr_lcm_consecutive_ne_zero_consolidated365 m 1 one_ne_zero
    have hm : m - 1 ≠ 0 := by omega
    have hne : tuningExponent m ≠ 0 := by
      rw [tuningExponent_of_two_le h]
      exact Nat.mul_ne_zero hm hl
    omega

namespace LowerDimReductionPullback

def tunedIdealAtLength (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap)) :
    (s.obj s.length).IdealSheafData :=
  haveI := hft
  balancedTunedSheaf S.base (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult

theorem tunedIdealAtLength_eq_balancedTunedSheaf (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap)) :
    tunedIdealAtLength S s hft =
      haveI := hft
      balancedTunedSheaf S.base (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult :=
  rfl

abbrev TunedMarkedBlowupSeq (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ) : Type (u + 1) :=
  MarkedSequenceOfBlowups (s.proj s.length ≫ S.structMap) (tunedIdealAtLength S s hft) (tuningExponent S.mult)
    (extra ++ (s.boundary s.length).drop ndrop)

section
variable (S : MarkedIdealWithBoundary.{u}) (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap)) (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ)

theorem structureMorphism_derivedTriple :
    (MaxContactCoverData.derivedTriple S s hft extra ndrop).structMap = s.proj s.length ≫ S.structMap :=
  MaxContactCoverData.derivedTriple_structureMorphism S s hft extra ndrop

theorem ideal_derivedTriple :
    (MaxContactCoverData.derivedTriple S s hft extra ndrop).ideal = tunedIdealAtLength S s hft :=
  rfl


end

section
variable (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible) (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
include hstar hV hO

theorem orderAt_ideal_length_le :
    ∀ x : ↥(s.obj s.length), orderAt (s.ideal s.length) x ≤ (S.mult : ℕ∞) := by
  have h := hstar.orderAt_level_le S hV hO s.toMarkedSequenceOfBlowups s.length
    (le_of_eq (MarkedBlowupSequenceData.toMarkedSequence_length s).symm)
  intro x
  exact h x

theorem maxOrderEq_ideal_length_of_nonempty (hne : (orderAtLeastLocus (s.ideal s.length) S.mult).Nonempty) :
    MaxOrderEq (s.ideal s.length) S.mult :=
  ⟨(orderLE_iff _ _).2 (orderAt_ideal_length_le hstar S hV hO s), hne⟩


end

theorem isOrderBoundedByMult_derivedTriple (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hm : 1 ≤ S.mult) (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ)
    (hVc : (MaxContactCoverData.derivedTriple S s hft extra ndrop).IsAdmissible) :
    (MaxContactCoverData.derivedTriple S s hft extra ndrop).IsOrderBoundedByMult := by
  have := hV.charZero
  have : IsNoetherianRing S.base := inferInstance
  have hsm : Smooth (s.proj s.length ≫ S.structMap) := by
    have h := hVc.smooth
    rwa [MaxContactCoverData.derivedTriple_structureMorphism S s hft extra ndrop] at h
  have hftI : LocallyOfFiniteType (s.proj s.length ≫ S.structMap) := hft
  have key : ∀ y : ↥(s.obj s.length),
      orderAt (tunedIdealAtLength S s hft) y ≤ ((tuningExponent S.mult : ℕ) : ℕ∞) := by
    by_cases hempty : orderAtLeastLocus (s.ideal s.length) S.mult = ∅
    · have htuned : tunedIdealAtLength S s hft = ⊤ :=
        balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty S.base (s.proj s.length ≫ S.structMap)
          (s.ideal s.length) hm hempty
      intro y
      rw [htuned, orderAt_top]
      exact zero_le
    · have hne : (orderAtLeastLocus (s.ideal s.length) S.mult).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hempty
      have hmax : MaxOrderEq (s.ideal s.length) S.mult :=
        maxOrderEq_ideal_length_of_nonempty hstar S hV hO s hne
      have htune := hstar.tuning.coSupport_tunedSheaf_eq_and_orderLE S.base (s.obj s.length)
        (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult hm hmax
        (tuningExponent S.mult) (one_le_tuningExponent S.mult)
      have heq : tunedIdealAtLength S s hft =
          tunedSheaf S.base (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
            (tuningExponent S.mult) :=
        balancedTunedSheaf_eq S.base (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
      intro y
      rw [heq]
      exact (orderLE_iff _ _).1 htune.2 y
  intro x
  rw [ideal_derivedTriple S s hft extra ndrop, MaxContactCoverData.derivedTriple_mult S s hft extra ndrop]
  exact key x

private theorem idealSheafData_top_pow_consolidated365 {X : Scheme.{u}} (n : ℕ) :
    (⊤ : X.IdealSheafData) ^ n = ⊤ := by
  have h1 : (1 : X.IdealSheafData) = ⊤ := by simp
  rw [← h1, one_pow]

section
variable (hstar : MaxContactCoverProperties.{u})
include hstar

theorem isBalanced_derivedTriple (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hm : 1 ≤ S.mult) (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ)
    (hVc : (MaxContactCoverData.derivedTriple S s hft extra ndrop).IsAdmissible) :
    (MaxContactCoverData.derivedTriple S s hft extra ndrop).IsBalanced hVc.locallyOfFiniteType := by
  have := hV.charZero
  have : IsNoetherianRing S.base := inferInstance
  have hsm : Smooth (s.proj s.length ≫ S.structMap) := by
    have h := hVc.smooth
    rwa [MaxContactCoverData.derivedTriple_structureMorphism S s hft extra ndrop] at h
  have hftI : LocallyOfFiniteType (s.proj s.length ≫ S.structMap) := hft
  have key : IsDerivBalanced S.base (s.proj s.length ≫ S.structMap) (tunedIdealAtLength S s hft)
      (tuningExponent S.mult) := by
    rcases Nat.lt_or_ge S.mult 2 with hlt | hge
    · have h1 : tuningExponent S.mult = 1 := tuningExponent_of_le_one (by omega)
      rw [h1]
      exact isDerivBalanced_one S.base (s.proj s.length ≫ S.structMap) (tunedIdealAtLength S s hft)
    · rcases Set.eq_empty_or_nonempty (orderAtLeastLocus (s.ideal s.length) S.mult) with hempty | hne
      · have htop : tunedIdealAtLength S s hft = ⊤ :=
          balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty S.base (s.proj s.length ≫ S.structMap)
            (s.ideal s.length) hm hempty
        rw [htop]
        refine isDerivBalanced_of_pow_le S.base (s.proj s.length ≫ S.structMap) ?_
        intro i _
        rw [idealSheafData_top_pow_consolidated365]
        exact le_top
      · have hmax : MaxOrderEq (s.ideal s.length) S.mult :=
          maxOrderEq_ideal_length_of_nonempty hstar S hV hO s hne
        have hexp : tuningExponent S.mult = (S.mult - 1) * lcmUpTo S.mult := tuningExponent_of_two_le hge
        have hderivPow := hstar.tuning.derivIdealSheafIter_tunedSheaf_pow_le
        unfold FunctorialResolution.EmbeddedResolution.IsDerivBalancedTunedSheafMulLcm at hderivPow
        have hderivPowAt := hderivPow S.base (s.obj s.length) (s.proj s.length ≫ S.structMap)
          (s.ideal s.length) S.mult hm hmax (S.mult - 1) le_rfl
        have hset : tunedIdealAtLength S s hft =
            tunedSheaf S.base (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
              ((S.mult - 1) * lcmUpTo S.mult) := by
          rw [← hexp]
          exact balancedTunedSheaf_eq S.base (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
        refine isDerivBalanced_of_pow_le S.base (s.proj s.length ≫ S.structMap) ?_
        intro i hi
        rw [hexp] at hi
        rw [hset, hexp]
        exact hderivPowAt i hi
  exact key

theorem length_eq_zero_of_orderAtLeastLocus_eq_empty (P : ℕ → Prop) (j : ℕ)
    (A B : PrincipalizationAssignment.{u}) (hspec : IsBoundaryDivisorReduction P j A B)
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible) (hm : 1 ≤ S.mult)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ)
    (hP : P (MaxContactCoverData.derivedTriple S s hft extra ndrop).krullDimSucc)
    (hVc : (MaxContactCoverData.derivedTriple S s hft extra ndrop).IsAdmissible)
    (hj : j < (extra ++ (s.boundary s.length).drop ndrop).length)
    (hempty : orderAtLeastLocus (s.ideal s.length) S.mult = ∅) :
    (A (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups.length = 0 := by
  have := hV.charZero
  have : IsNoetherianRing S.base := inferInstance
  have hsm : Smooth (s.proj s.length ≫ S.structMap) := by
    have h := hVc.smooth
    rwa [MaxContactCoverData.derivedTriple_structureMorphism S s hft extra ndrop] at h
  have hftI : LocallyOfFiniteType (s.proj s.length ≫ S.structMap) := hft
  have htuned : tunedIdealAtLength S s hft = ⊤ :=
    balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty S.base (s.proj s.length ≫ S.structMap)
      (s.ideal s.length) hm hempty
  have hjb : j < (MaxContactCoverData.derivedTriple S s hft extra ndrop).boundary.length := by
    rw [MaxContactCoverData.derivedTriple_boundary S s hft extra ndrop]
    exact hj
  have h1 : (MaxContactCoverData.derivedTriple S s hft extra ndrop).ideal = ⊤ := by
    rw [ideal_derivedTriple S s hft extra ndrop]
    exact htuned
  have hcs : orderAtLeastLocus (MaxContactCoverData.derivedTriple S s hft extra ndrop).ideal
      (MaxContactCoverData.derivedTriple S s hft extra ndrop).mult = ∅ := by
    rw [h1, MaxContactCoverData.derivedTriple_mult S s hft extra ndrop]
    exact orderAtLeastLocus_top_eq_empty _ (one_le_tuningExponent S.mult)
  exact hspec.trivial_of_coSupport_empty _ hVc hP
    (isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hft extra ndrop hVc)
    (isBalanced_derivedTriple hstar S hV hm hO s hft extra ndrop hVc) hjb hcs


end

section
variable (hstar : MaxContactCoverProperties.{u}) {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
include hstar

private theorem orderAtLeastLocus_controlledTransform_disjoint_strictTransform_consolidated365 {E : List X.IdealSheafData} {d : BlowupSequenceData X} (hmk : d.IsMarked p I m E)
    (D : X.IdealSheafData) (hD : orderAtLeastLocus I m ∩ (D.support : Set ↥X) = ∅) :
    ∀ i, i ≤ d.length →
      orderAtLeastLocus (d.controlledTransform I m i) m ∩ ((d.iteratedStrictTransform i D).support : Set ↥(d.obj i)) = ∅ := by
  intro i
  induction i with
  | zero =>
      intro _
      have hsupp : ((D.comap d.isoZero.hom).support : Set ↥(d.obj 0)) =
          ⇑d.isoZero.hom ⁻¹' (D.support : Set ↥X) := by
        rw [Scheme.IdealSheafData.support_comap]; rfl
      rw [BlowupSequenceData.controlledTransform_zero, BlowupSequenceData.iteratedStrictTransform_zero, orderAtLeastLocus_comap_iso,
        hsupp, ← Set.preimage_inter, hD, Set.preimage_empty]
  | succ i ih =>
      intro hi
      have hilt : i < d.length := hi
      have hih := ih (le_of_lt hilt)
      apply Set.eq_empty_of_subset_empty
      rintro x ⟨hx1, hx2⟩
      have heq := BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ d I m i (hmk.divisible i hilt)
      have hsub := hstar.coSupport_le_preimage (d.map i) (d.center i) (d.isBlowup i hilt)
        (d.controlledTransform I m i) (d.controlledTransform I m (i + 1)) m heq (hmk.center_order i hilt)
      rw [BlowupSequenceData.iteratedStrictTransform_succ] at hx2
      have hmem : ⇑(d.map i) x ∈
          orderAtLeastLocus (d.controlledTransform I m i) m ∩ ((d.iteratedStrictTransform i D).support : Set ↥(d.obj i)) :=
        ⟨hsub hx1,
          support_strictTransform_subset_preimage (d.map i) (d.center i) (d.iteratedStrictTransform i D) hx2⟩
      rw [hih] at hmem
      simp at hmem

private theorem isMarked_append_of_orderAtLeastLocus_disjoint_consolidated365 {L₁ L₃ : List X.IdealSheafData} (L₂ : List X.IdealSheafData) {d : BlowupSequenceData X}
    (hmk : d.IsMarked p I m (L₁ ++ L₃))
    (hsep : ∀ D ∈ L₂, orderAtLeastLocus I m ∩ (D.support : Set ↥X) = ∅) :
    d.IsMarked p I m (L₂ ++ L₃) := by
  refine ⟨hmk.divisible, hmk.center_order, hmk.center_smooth, ?_⟩
  intro i hi
  have h1 := hmk.center_snc i hi
  rw [BlowupSequenceData.boundary_append] at h1
  rw [BlowupSequenceData.boundary_append]
  refine HasStrictNormalCrossingsWith.append_of_support_disjoint (HasStrictNormalCrossingsWith.of_append h1) ?_
  intro D hD
  obtain ⟨D0, hD0, hDeq⟩ := List.mem_map.mp hD
  subst hDeq
  have hdis := orderAtLeastLocus_controlledTransform_disjoint_strictTransform_consolidated365 hstar hmk D0 (hsep D0 hD0) i (le_of_lt hi)
  apply Set.eq_empty_of_subset_empty
  rintro x ⟨hx1, hx2⟩
  have hx3 : x ∈ orderAtLeastLocus (d.controlledTransform I m i) m := hmk.center_order i hi hx2
  have hmem : x ∈ orderAtLeastLocus (d.controlledTransform I m i) m ∩
      ((d.iteratedStrictTransform i D0).support : Set ↥(d.obj i)) := ⟨hx3, hx1⟩
  rw [hdis] at hmem
  simp at hmem


end

section
variable {k : Type u} [Field k] {X : Scheme.{u}}

private theorem isMarked_of_length_eq_zero_consolidated365 (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (d : BlowupSequenceData X) (hd : d.length = 0) :
    d.IsMarked p I m E := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals intro i hi
  all_goals rw [hd] at hi
  all_goals exact absurd hi (Nat.not_lt_zero i)

private theorem orderAtLeastLocus_controlledTransform_eq_of_length_eq_zero_consolidated365 {p : X ⟶ Spec (CommRingCat.of k)} {J : X.IdealSheafData} {n : ℕ}
    {E : List X.IdealSheafData} (t : MarkedSequenceOfBlowups p J n E)
    (I : X.IdealSheafData) (m n' : ℕ) (hlen : t.toSequenceOfBlowups.length = 0)
    (hempty : orderAtLeastLocus I m = ∅) (hJ : J = ⊤) (hn1 : 1 ≤ n') :
    ∀ i ≤ t.toSequenceOfBlowups.length,
      orderAtLeastLocus ((BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).controlledTransform I m i) m =
        orderAtLeastLocus (t.ideal i) n' := by
  have hJempty : orderAtLeastLocus J n' = ∅ := by
    rw [hJ]
    exact orderAtLeastLocus_top_eq_empty n' hn1
  intro i hi
  rw [hlen, Nat.le_zero] at hi
  subst hi
  have h1 : orderAtLeastLocus ((BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).controlledTransform I m 0) m = ∅ := by
    rw [BlowupSequenceData.controlledTransform_zero, orderAtLeastLocus_comap_iso, hempty, Set.preimage_empty]
  have h2 : orderAtLeastLocus (t.ideal 0) n' = ∅ := by
    rw [t.ideal_zero, orderAtLeastLocus_comap_iso, hJempty, Set.preimage_empty]
  exact h1.trans h2.symm


end

section
variable (hstar : MaxContactCoverProperties.{u})
include hstar

private theorem isMarked_and_orderAtLeastLocus_eq_of_balancedTunedSheaf_consolidated365 {k : Type u} [Field k]
    [CharZero k] [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ) (hm : 1 ≤ m) (hmax : MaxOrderEq I m)
    (L₁ L₂ L₃ E₀ : List X.IdealSheafData) (hE₀ : L₂ ++ L₃ = E₀)
    (hsep : ∀ D ∈ L₂, orderAtLeastLocus I m ∩ (D.support : Set ↥X) = ∅)
    (t : MarkedSequenceOfBlowups p (balancedTunedSheaf k p I m) (tuningExponent m) (L₁ ++ L₃)) :
    ∃ _hmk : (BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).IsMarked p I m E₀,
      ∀ i ≤ t.toSequenceOfBlowups.length,
        orderAtLeastLocus ((BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).controlledTransform I m i) m =
          orderAtLeastLocus (t.ideal i) (tuningExponent m) := by
  subst hE₀
  have hmarkedIff := hstar.tuning.isMarked_tuned_iff k X p I m hm hmax (L₁ ++ L₃)
    (BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups)
  have hmkW : (BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).IsMarked p (balancedTunedSheaf k p I m) (tuningExponent m)
      (L₁ ++ L₃) := (MarkedBlowupSequenceData.ofMarkedSequence t).isMarked_toBlowupSequenceData
  have hmkI : (BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).IsMarked p I m (L₁ ++ L₃) := hmarkedIff.1.mpr hmkW
  refine ⟨isMarked_append_of_orderAtLeastLocus_disjoint_consolidated365 hstar L₂ hmkI hsep, ?_⟩
  intro i hi
  have h2 := hmarkedIff.2.1 hmkI i (by rw [BlowupSequenceData.ofSequenceOfBlowups_length]; exact hi)
  have h3 : (BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).controlledTransform (balancedTunedSheaf k p I m) (tuningExponent m) i =
      t.ideal i :=
    MarkedBlowupSequenceData.toBlowupSequenceData_controlledTransform_eq (MarkedBlowupSequenceData.ofMarkedSequence t) i
      (by rw [MarkedBlowupSequenceData.ofMarkedSequence_length]; exact hi)
  exact h2.symm.trans (congrArg (fun Z => orderAtLeastLocus Z (tuningExponent m)) h3)

theorem appendLowerDimReduction_eq_append (hinv : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})
    (B : PrincipalizationAssignment.{u}) (j : ℕ) (hspec : IsBoundaryDivisorReduction P j (A j) B)
    (reduce : (S' : MarkedIdealWithBoundary.{u}) → S'.krullDimSucc ≤ T.krullDimSucc → ℕ → S'.SequenceOfBlowups)
    (hrc : ∀ (S' : MarkedIdealWithBoundary.{u}) (h : S'.krullDimSucc ≤ T.krullDimSucc) (i : ℕ), reduce S' h i = A i S')
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible) (hm : 1 ≤ S.mult)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hdim : (MaxContactCoverData.derivedTriple S s hft extra ndrop).krullDimSucc ≤ T.krullDimSucc)
    (hP : P (MaxContactCoverData.derivedTriple S s hft extra ndrop).krullDimSucc)
    (hVc : (MaxContactCoverData.derivedTriple S s hft extra ndrop).IsAdmissible)
    (hj : j < (extra ++ (s.boundary s.length).drop ndrop).length)
    (hsep : ∀ D ∈ (s.boundary s.length).take ndrop,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (D.support : Set ↥(s.obj s.length)) = ∅) :
    ∃ hmk :
        (BlowupSequenceData.ofSequenceOfBlowups
            (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups).IsMarked
          (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult (s.boundary s.length),
      MaxContactReduction.appendLowerDimReduction hinv T reduce S s extra ndrop j =
          s.append
            ((BlowupSequenceData.ofSequenceOfBlowups
                (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups).toMarkedBlowupSequenceData
              (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
              (s.boundary s.length) hmk) hinv ∧
        ∀ i ≤ (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups.length,
          orderAtLeastLocus
              ((BlowupSequenceData.ofSequenceOfBlowups
                  (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups).controlledTransform
                (s.ideal s.length) S.mult i) S.mult =
            orderAtLeastLocus ((A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).ideal i)
              (tuningExponent S.mult) := by
  have happend : MaxContactReduction.appendLowerDimReduction hinv T reduce S s extra ndrop j =
      MaxContactReduction.concatOfIsMarked hinv s
        (BlowupSequenceData.ofSequenceOfBlowups (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups) := by
    rw [MaxContactCoverData.appendLowerDimReduction_eq_concatOfIsMarked hinv T reduce S s extra ndrop j hft hdim,
      hrc (MaxContactCoverData.derivedTriple S s hft extra ndrop) hdim j]
  have := hV.charZero
  have : IsNoetherianRing S.base := inferInstance
  have hsm : Smooth (s.proj s.length ≫ S.structMap) := by
    have h := hVc.smooth
    rwa [MaxContactCoverData.derivedTriple_structureMorphism S s hft extra ndrop] at h
  have hftI : LocallyOfFiniteType (s.proj s.length ≫ S.structMap) := hft
  by_cases hempty : orderAtLeastLocus (s.ideal s.length) S.mult = ∅
  · have hlen : (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups.length = 0 :=
      length_eq_zero_of_orderAtLeastLocus_eq_empty hstar P j (A j) B hspec S hV hm hO s hft extra ndrop hP hVc hj hempty
    have hJtop : (MaxContactCoverData.derivedTriple S s hft extra ndrop).ideal = ⊤ := by
      rw [ideal_derivedTriple S s hft extra ndrop]
      exact balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty S.base (s.proj s.length ≫ S.structMap)
        (s.ideal s.length) hm hempty
    have hmk : (BlowupSequenceData.ofSequenceOfBlowups
        (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups).IsMarked
        (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult (s.boundary s.length) :=
      isMarked_of_length_eq_zero_consolidated365 (s.proj s.length ≫ S.structMap) (s.ideal s.length)
        S.mult (s.boundary s.length) _ ((BlowupSequenceData.ofSequenceOfBlowups_length _).trans hlen)
    exact ⟨hmk, happend.trans (MaxContactCoverData.concatOfIsMarked_eq_append_of_isMarked hinv s _ hmk),
      orderAtLeastLocus_controlledTransform_eq_of_length_eq_zero_consolidated365
        (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop))
        (s.ideal s.length) S.mult (tuningExponent S.mult) hlen hempty hJtop
        (one_le_tuningExponent S.mult)⟩
  · have hne : (orderAtLeastLocus (s.ideal s.length) S.mult).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hempty
    have hmax : MaxOrderEq (s.ideal s.length) S.mult :=
      maxOrderEq_ideal_length_of_nonempty hstar S hV hO s hne
    obtain ⟨hmk, hcos⟩ := isMarked_and_orderAtLeastLocus_eq_of_balancedTunedSheaf_consolidated365 hstar (s.proj s.length ≫ S.structMap)
      (s.ideal s.length) S.mult hm hmax extra ((s.boundary s.length).take ndrop)
      ((s.boundary s.length).drop ndrop) (s.boundary s.length)
      (List.take_append_drop ndrop (s.boundary s.length)) hsep
      (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop))
    exact ⟨hmk, happend.trans (MaxContactCoverData.concatOfIsMarked_eq_append_of_isMarked hinv s _ hmk), hcos⟩


end

end LowerDimReductionPullback


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverTriple
section


section

namespace BlowupSequenceData

section
variable {X : Scheme.{u}} (d : BlowupSequenceData X)

theorem boundary_eq_map_iteratedStrictTransform_append (L : List X.IdealSheafData) (i : ℕ) :
    d.boundaryFrom L i = L.map (d.iteratedStrictTransform i) ++ d.boundaryFrom ([] : List X.IdealSheafData) i := by
  have h := d.boundary_append L ([] : List X.IdealSheafData) i
  rwa [List.append_nil] at h

private theorem support_iteratedStrictTransform_subset_of_strictTransform_mono_consolidated393 (D : X.IdealSheafData)
    (K : ∀ t : ℕ, (d.obj t).IdealSheafData) (h0 : K 0 = D.comap d.isoZero.hom)
    (hstep : ∀ t, t < d.length →
      K (t + 1) = Blowup.strictTransform (d.map t) (d.center t) (K t) ∨
        K (t + 1) = (K t).comap (d.map t))
    (hsupp : ∀ (i : ℕ), i < d.length → ∀ (A B : (d.obj i).IdealSheafData),
      ((A.support : Set ↥(d.obj i)) ⊆ (B.support : Set ↥(d.obj i))) →
      ((Blowup.strictTransform (d.map i) (d.center i) A).support : Set ↥(d.obj (i + 1))) ⊆
        ((Blowup.strictTransform (d.map i) (d.center i) B).support : Set ↥(d.obj (i + 1))))
    (t : ℕ) (ht : t ≤ d.length) :
    ((d.iteratedStrictTransform t D).support : Set ↥(d.obj t)) ⊆ ((K t).support : Set ↥(d.obj t)) := by
  have key : ∀ s, s ≤ d.length →
      ((d.iteratedStrictTransform s D).support : Set ↥(d.obj s)) ⊆ ((K s).support : Set ↥(d.obj s)) := by
    intro s
    induction s with
    | zero =>
        intro _ x hx
        have hz : K 0 = d.iteratedStrictTransform 0 D := by rw [h0, iteratedStrictTransform_zero]
        rw [hz]
        exact hx
    | succ n ih =>
        intro hn
        have hlt : n < d.length := hn
        have hle := ih (Nat.le_of_lt hlt)
        rcases hstep n hlt with hh | hh
        · rw [hh, iteratedStrictTransform_succ]
          exact hsupp n hlt (d.iteratedStrictTransform n D) (K n) hle
        · rw [hh, iteratedStrictTransform_succ]
          intro y hy
          have h1 := support_strictTransform_subset_preimage (d.map n) (d.center n)
            (d.iteratedStrictTransform n D) hy
          have h2 := hle h1
          exact (one_le_orderAt_iff_mem_support ((K n).comap (d.map n)) y).1
            (le_trans ((one_le_orderAt_iff_mem_support (K n) _).2 h2)
              (orderAt_le_orderAt_comap (d.map n) (K n) y))
  exact key t ht

theorem support_iteratedStrictTransform_subset_support (hN : ∀ i ≤ d.length, IsLocallyNoetherian (d.obj i))
    (D : X.IdealSheafData) (K : ∀ t : ℕ, (d.obj t).IdealSheafData)
    (h0 : K 0 = D.comap d.isoZero.hom)
    (hstep : ∀ t, t < d.length →
      K (t + 1) = Blowup.strictTransform (d.map t) (d.center t) (K t) ∨
        K (t + 1) = (K t).comap (d.map t))
    (t : ℕ) (ht : t ≤ d.length) :
    ((d.iteratedStrictTransform t D).support : Set ↥(d.obj t)) ⊆ ((K t).support : Set ↥(d.obj t)) := by
  refine support_iteratedStrictTransform_subset_of_strictTransform_mono_consolidated393 d D K h0 hstep ?_ t ht
  intro i hi A B hAB
  have := hN (i + 1) hi
  have := FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian (d.map i) (d.center i) A
  have := FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian (d.map i) (d.center i) B
  rw [support_strictTransform_eq_closure_preimage, support_strictTransform_eq_closure_preimage]
  exact closure_mono (Set.sdiff_subset_sdiff_left (Set.preimage_mono hAB))


end

end BlowupSequenceData

namespace BoundarySeparationByMaxContact

section
variable (k : Type u) [Field k] [CharZero k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p] (A : P.IdealSheafData)

private theorem maxContactIdeal_eq_top_of_orderAtLeastLocus_eq_empty_consolidated393 (m : ℕ) (hm : 1 ≤ m)
    (hempty : orderAtLeastLocus A m = ∅) : maxContactIdeal k p A m = ⊤ := by
  have hlt : m - 1 < m := by omega
  have h := orderAtLeastLocus_derivIdealSheafIterate k p A (r := m - 1) (m := m) hlt
  rw [show m - (m - 1) = 1 from by omega, hempty] at h
  refine (Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).2 ?_
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  have hy' : y ∈ orderAtLeastLocus (derivIdealSheafIterate k p (m - 1) A) 1 := by
    refine (mem_orderAtLeastLocus_one_iff _ y).2 ?_
    rw [← maxContactIdeal_eq_derivIdealSheafIterate]
    exact hy
  rw [h] at hy'
  exact hy'

private theorem prod_derivIdealSheafIter_pow_le_balancedTunedSheaf_consolidated393 (μ : ℕ) (c : ℕ → ℕ)
    (hc : tuningExponent μ ≤ ∑ j ∈ Finset.range μ, (μ - j) * c j) :
    (List.map (fun j => derivIdealSheafIterate k p j A ^ c j) (List.range μ)).prod ≤
      balancedTunedSheaf k p A μ := by
  unfold FunctorialResolution.EmbeddedResolution.balancedTunedSheaf FunctorialResolution.EmbeddedResolution.tunedSheaf
  exact le_iSup
    (fun d : {e : ℕ → ℕ // tuningExponent μ ≤ ∑ j ∈ Finset.range μ, (μ - j) * e j} =>
      (List.map (fun j => derivIdealSheafIterate k p j A ^ d.1 j) (List.range μ)).prod) ⟨c, hc⟩


end

private theorem stalkIdeal_prod_eq_top_consolidated393 {X : Scheme.{u}} (x : ↥X) :
    ∀ L : List X.IdealSheafData, (∀ I ∈ L, stalkIdeal I x = ⊤) → stalkIdeal L.prod x = ⊤ := by
  intro L
  induction L with
  | nil =>
      intro _
      have h0 := stalkIdeal_pow (⊤ : X.IdealSheafData) 0 x
      rw [pow_zero, pow_zero] at h0
      rw [List.prod_nil, h0, Ideal.one_eq_top]
  | cons I L ih =>
      intro h
      rw [List.prod_cons, stalkIdeal_mul, h I (by simp),
        ih (fun J hJ => h J (by simp [hJ]))]
      simp

private theorem orderAtLeastLocus_balancedTunedSheaf_eq_empty_consolidated393 (k : Type u) [Field k] [CharZero k]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p]
    [LocallyOfFiniteType p] (A : P.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ)
    (hempty : orderAtLeastLocus A μ = ∅) : orderAtLeastLocus (balancedTunedSheaf k p A μ) (tuningExponent μ) = ∅ := by
  have hE : 1 ≤ tuningExponent μ := one_le_tuningExponent μ
  have hmc : maxContactIdeal k p A μ = ⊤ :=
    maxContactIdeal_eq_top_of_orderAtLeastLocus_eq_empty_consolidated393 k p A μ hμ hempty
  have hstalk : ∀ y : ↥P, stalkIdeal (derivIdealSheafIterate k p (μ - 1) A) y = ⊤ := by
    intro y
    rw [← maxContactIdeal_eq_derivIdealSheafIterate, hmc]
    exact stalkIdeal_top y
  have hsum : (∑ j ∈ Finset.range μ, (μ - j) * (if j = μ - 1 then tuningExponent μ else 0))
      = tuningExponent μ := by
    rw [Finset.sum_eq_single (μ - 1)]
    · simp [show μ - (μ - 1) = 1 from by omega]
    · intro b _ hb
      simp [hb]
    · intro hcon
      exact absurd (Finset.mem_range.mpr (show μ - 1 < μ from by omega)) hcon
  have hle : (List.map
      (fun j => derivIdealSheafIterate k p j A ^ (if j = μ - 1 then tuningExponent μ else 0))
      (List.range μ)).prod ≤ balancedTunedSheaf k p A μ :=
    prod_derivIdealSheafIter_pow_le_balancedTunedSheaf_consolidated393 k p A μ
      (fun j => if j = μ - 1 then tuningExponent μ else 0) (le_of_eq hsum.symm)
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hprod : stalkIdeal (List.map
      (fun j => derivIdealSheafIterate k p j A ^ (if j = μ - 1 then tuningExponent μ else 0))
      (List.range μ)).prod x = ⊤ := by
    refine stalkIdeal_prod_eq_top_consolidated393 x _ ?_
    intro I hI
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hI
    simp only [stalkIdeal_pow]
    split_ifs with hjj
    · rw [hjj, hstalk x, ← Ideal.one_eq_top, one_pow]
    · rw [pow_zero]
      exact Ideal.one_eq_top
  have hmono := stalkIdeal_mono hle x
  rw [hprod] at hmono
  have htop : stalkIdeal (balancedTunedSheaf k p A μ) x = ⊤ := top_le_iff.mp hmono
  have hx1 : x ∈ orderAtLeastLocus (balancedTunedSheaf k p A μ) 1 :=
    orderAtLeastLocus_subset_of_le (balancedTunedSheaf k p A μ) hE hx
  have hxs : x ∈ (balancedTunedSheaf k p A μ).support := (mem_orderAtLeastLocus_one_iff _ x).1 hx1
  exact ((mem_support_iff_stalkIdeal_ne_top _ x).1 hxs) htop

theorem isMaxContactHypersurface_balancedTunedSheaf (hstar : MaxContactCoverProperties.{u}) (k : Type u) [Field k] [CharZero k]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p]
    [LocallyOfFiniteType p] (A : P.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ)
    (hord : ∀ x : ↥P, orderAt A x ≤ (μ : ℕ∞)) (H : P.IdealSheafData)
    (hH : IsMaxContactHypersurface k p A μ H) :
    IsMaxContactHypersurface k p (balancedTunedSheaf k p A μ) (tuningExponent μ) H := by
  by_cases hne : (orderAtLeastLocus A μ).Nonempty
  · have hmax : MaxOrderEq A μ := ⟨(orderLE_iff A μ).2 hord, hne⟩
    have hcs : orderAtLeastLocus (balancedTunedSheaf k p A μ) (tuningExponent μ) = orderAtLeastLocus A μ :=
      (hstar.tuning.coSupport_tunedSheaf_eq_and_orderLE k P p A μ hμ hmax (tuningExponent μ)
        (one_le_tuningExponent μ)).1
    have hmi : maxContactIdeal k p (balancedTunedSheaf k p A μ) (tuningExponent μ) = maxContactIdeal k p A μ :=
      hstar.tuning.derivIdealSheafIter_pred_tunedSheaf k P p A μ hμ hmax (tuningExponent μ)
        (one_le_tuningExponent μ)
    intro x
    obtain ⟨U, hUaff, hxU, hcase⟩ := hH x
    refine ⟨U, hUaff, hxU, ?_⟩
    rcases hcase with ⟨hdisj, htop⟩ | ⟨n, c, j, hcoord, hmcc⟩
    · refine Or.inl ⟨?_, htop⟩
      rw [hcs]
      exact hdisj
    · refine Or.inr ⟨n, c, j, hcoord, ?_⟩
      intro i
      rw [hmi]
      exact hmcc i
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hcs : orderAtLeastLocus (balancedTunedSheaf k p A μ) (tuningExponent μ) = ∅ :=
      orderAtLeastLocus_balancedTunedSheaf_eq_empty_consolidated393 k p A μ hμ hne
    have h1 : maxContactIdeal k p A μ = ⊤ :=
      maxContactIdeal_eq_top_of_orderAtLeastLocus_eq_empty_consolidated393 k p A μ hμ hne
    have h2 : maxContactIdeal k p (balancedTunedSheaf k p A μ) (tuningExponent μ) = ⊤ :=
      maxContactIdeal_eq_top_of_orderAtLeastLocus_eq_empty_consolidated393 k p (balancedTunedSheaf k p A μ) (tuningExponent μ)
        (one_le_tuningExponent μ) hcs
    intro x
    obtain ⟨U, hUaff, hxU, hcase⟩ := hH x
    refine ⟨U, hUaff, hxU, ?_⟩
    rcases hcase with ⟨hdisj, htop⟩ | ⟨n, c, j, hcoord, hmcc⟩
    · refine Or.inl ⟨?_, htop⟩
      rw [hcs]
      exact Set.disjoint_left.2 (fun y hy => ((Set.mem_empty_iff_false y).mp hy).elim)
    · refine Or.inr ⟨n, c, j, hcoord, ?_⟩
      intro i
      rw [h2, ← h1]
      exact hmcc i

section
variable (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible) (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (i : ℕ) (hi : i ≤ s.length)
include hstar hV hi

theorem locallyOfFiniteType_projectionToBase_comp :
    LocallyOfFiniteType (s.proj i ≫ S.structMap) := by
  have h := (hstar.valid_level S hV s.toMarkedSequenceOfBlowups i hi).locallyOfFiniteType
  simp at h
  with_unfolding_all exact h

theorem smooth_projectionToBase_comp :
    Smooth (s.proj i ≫ S.structMap) := by
  have h := (hstar.valid_level S hV s.toMarkedSequenceOfBlowups i hi).smooth
  simp at h
  with_unfolding_all exact h


end

theorem iteratedStrictTransform_eq_toBlowupSequenceData {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) (i : ℕ) :
    MaxContactReduction.iteratedStrictTransform s H i = s.toBlowupSequenceData.iteratedStrictTransform i H := by
  induction i with
  | zero =>
      rewrite [MaxContactReduction.iteratedStrictTransform_zero, BlowupSequenceData.iteratedStrictTransform_zero]
      rfl
  | succ n ih =>
      rewrite [MaxContactReduction.iteratedStrictTransform_succ, BlowupSequenceData.iteratedStrictTransform_succ, ih]
      rfl

theorem inStrictNormalCrossingPosition_iteratedStrictTransform_zero (S : MarkedIdealWithBoundary.{u})
    (u : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (H : S.scheme.IdealSheafData)
    (hH : InStrictNormalCrossingPosition S.structMap [H]) :
    InStrictNormalCrossingPosition (u.proj 0 ≫ S.structMap) [MaxContactReduction.iteratedStrictTransform u H 0] := by
  have hproj : u.proj 0 = u.isoZero.hom := u.proj_zero
  have h := inStrictNormalCrossingPosition_comap_iso S.structMap u.isoZero [H] hH
  rw [MaxContactReduction.iteratedStrictTransform_zero u H, hproj]
  exact h

section
variable {X : Scheme.{u}}

private theorem prod_map_range_succ_eq_apply_zero_consolidated393 (f : ℕ → X.IdealSheafData)
    (hf : ∀ j, j ≠ 0 → f j = 1) (n : ℕ) :
    (List.map f (List.range (n + 1))).prod = f 0 := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih]
      simp [hf (m + 1) (Nat.succ_ne_zero m)]

private theorem support_pow_subset_support_consolidated393 (A : X.IdealSheafData) (e : ℕ) :
    ((A ^ e).support : Set ↥X) ⊆ (A.support : Set ↥X) := by
  intro x hx
  have hx' : stalkIdeal (A ^ e) x ≠ ⊤ := (mem_support_iff_stalkIdeal_ne_top (A ^ e) x).1 hx
  refine (mem_support_iff_stalkIdeal_ne_top A x).2 ?_
  intro htop
  exact hx' (by rw [stalkIdeal_pow, htop, ← Ideal.one_eq_top, one_pow])


end

private theorem pow_tuningExponent_le_balancedTunedSheaf_consolidated393 (k : Type u) [Field k] [CharZero k] {P : Scheme.{u}}
    (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p]
    [LocallyOfFiniteType p] (A : P.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ) :
    A ^ tuningExponent μ ≤ balancedTunedSheaf k p A μ := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, μ = n + 1 := ⟨μ - 1, by omega⟩
  have hd0 : derivIdealSheafIterate k p 0 A = A := rfl
  have hsum : (∑ j ∈ Finset.range (n + 1),
      ((n + 1) - j) * (if j = 0 then tuningExponent (n + 1) else 0)) = (n + 1) * tuningExponent (n + 1) := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hcon
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) hcon
  have hc : tuningExponent (n + 1) ≤ ∑ j ∈ Finset.range (n + 1),
      ((n + 1) - j) * (if j = 0 then tuningExponent (n + 1) else 0) := by
    rw [hsum]
    calc tuningExponent (n + 1) = 1 * tuningExponent (n + 1) := (one_mul _).symm
      _ ≤ (n + 1) * tuningExponent (n + 1) :=
          Nat.mul_le_mul (Nat.succ_le_succ (Nat.zero_le n)) (le_refl _)
  have hle := prod_derivIdealSheafIter_pow_le_balancedTunedSheaf_consolidated393 k p A (n + 1)
    (fun j => if j = 0 then tuningExponent (n + 1) else 0) hc
  have hf : ∀ j : ℕ, j ≠ 0 →
      derivIdealSheafIterate k p j A ^ (if j = 0 then tuningExponent (n + 1) else 0) = 1 := by
    intro j hj
    simp [hj]
  have hA : A ^ tuningExponent (n + 1) ≤
      (List.map (fun j => derivIdealSheafIterate k p j A ^ (if j = 0 then tuningExponent (n + 1) else 0))
        (List.range (n + 1))).prod := by
    rw [prod_map_range_succ_eq_apply_zero_consolidated393
      (fun j => derivIdealSheafIterate k p j A ^ (if j = 0 then tuningExponent (n + 1) else 0)) hf n]
    simp [hd0]
  exact le_trans hA hle

theorem isAdmissible_derivedTriple (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)
    (hsnc : InStrictNormalCrossingPosition (s.proj s.length ≫ S.structMap)
      (extra ++ (s.boundary s.length).drop keep)) :
    (MaxContactCoverData.derivedTriple S s hft extra keep).IsAdmissible := by
  have hlev := hstar.valid_level S hV s.toMarkedSequenceOfBlowups s.length (le_refl s.length)
  constructor
  case charZero => exact hV.charZero
  case locallyOfFiniteType =>
    rw [MaxContactCoverData.derivedTriple_structureMorphism]
    exact hft
  case one_le_mult =>
    rw [MaxContactCoverData.derivedTriple_mult]
    exact one_le_tuningExponent S.mult
  case quasiCompact =>
    have h := hlev.quasiCompact
    rw [MaxContactCoverData.derivedTriple_structureMorphism]
    simp at h
    with_unfolding_all exact h
  case smooth =>
    rw [MaxContactCoverData.derivedTriple_structureMorphism]
    exact smooth_projectionToBase_comp hstar S hV s s.length (le_refl s.length)
  case snc =>
    rw [MaxContactCoverData.derivedTriple_structureMorphism, MaxContactCoverData.derivedTriple_boundary]
    exact hsnc
  case nonzeroOnComponents =>
    have hNZ := hlev.nonzeroOnComponents
    have hsupp : ((LowerDimReductionPullback.tunedIdealAtLength S s hft).support : Set ↥(s.obj s.length)) ⊆
        ((s.ideal s.length).support : Set ↥(s.obj s.length)) := by
      have : CharZero S.base := hV.charZero
      have : Smooth (s.proj s.length ≫ S.structMap) :=
        smooth_projectionToBase_comp hstar S hV s s.length (le_refl s.length)
      have := hft
      have hpow := pow_tuningExponent_le_balancedTunedSheaf_consolidated393 S.base (s.proj s.length ≫ S.structMap)
        (s.ideal s.length) S.mult hV.one_le_mult
      exact Set.Subset.trans (Scheme.IdealSheafData.support_antitone hpow)
        (support_pow_subset_support_consolidated393 (s.ideal s.length) (tuningExponent S.mult))
    rw [LowerDimReductionPullback.ideal_derivedTriple]
    unfold FunctorialResolution.EmbeddedResolution.NonzeroOnComponents
    intro T hT hsub
    exact hNZ T hT (Set.Subset.trans hsub hsupp)

theorem isLocallyNoetherian_tunedMarkedBlowupSeq_schemeAt (_hMaxContact : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u})
    (_hV : S.IsAdmissible) (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)
    (hVc : (MaxContactCoverData.derivedTriple S s hft extra keep).IsAdmissible)
    (u : LowerDimReductionPullback.TunedMarkedBlowupSeq S s hft extra keep) (i : ℕ) (hi : i ≤ u.length) :
    IsLocallyNoetherian ((BlowupSequenceData.ofSequenceOfBlowups u.toSequenceOfBlowups).obj i) := by
  have hi' : i ≤ u.toSequenceOfBlowups.length := hi
  have hN : IsNoetherian (u.toSequenceOfBlowups.schemeAt i) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hVc u i hi'
  exact inferInstanceAs (IsLocallyNoetherian (u.toSequenceOfBlowups.schemeAt i))

abbrev continuationMarkedData (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)
    (u : LowerDimReductionPullback.TunedMarkedBlowupSeq S s hft extra keep)
    (hmk : (BlowupSequenceData.ofSequenceOfBlowups u.toSequenceOfBlowups).IsMarked (s.proj s.length ≫ S.structMap)
      (s.ideal s.length) S.mult (s.boundary s.length)) :
    MarkedBlowupSequenceData (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
      (s.boundary s.length) :=
  (BlowupSequenceData.ofSequenceOfBlowups u.toSequenceOfBlowups).toMarkedBlowupSequenceData (s.proj s.length ≫ S.structMap)
    (s.ideal s.length) S.mult (s.boundary s.length) hmk

section
variable (hstar : MaxContactCoverProperties.{u}) (P : ℕ → Prop) (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T)
include hstar

theorem isAdmissible_coverTriple :
    (MaxContactCoverData.coverTriple T h.valid).IsAdmissible :=
  hstar.coverTriple_valid T h.valid h.orderLE
    (MaxContactCoverData.isMaxContactCover_chosenCoverData T h.valid
      (hstar.exists_goodCover T h.valid h.orderLE))

theorem orderAt_coverTriple_ideal_le_mult :
    ∀ x : ↥(MaxContactCoverData.coverTriple T h.valid).scheme,
      orderAt (MaxContactCoverData.coverTriple T h.valid).ideal x ≤
        ((MaxContactCoverData.coverTriple T h.valid).mult : ℕ∞) := by
  have := h.valid.locallyOfFiniteType
  have := h.valid.smooth
  have : CharZero T.base := h.valid.charZero
  have hμ : 1 ≤ T.mult := h.valid.one_le_mult
  have hmax : MaxOrderEq T.ideal T.mult :=
    ⟨(orderLE_iff T.ideal T.mult).2 h.orderLE, h.coSupport_nonempty⟩
  have H := hstar.tuning.coSupport_tunedSheaf_eq_and_orderLE T.base T.scheme T.structMap T.ideal
    T.mult hμ hmax (tuningExponent T.mult) (one_le_tuningExponent T.mult)
  intro x
  exact (orderAt_comap T.base T.structMap (MaxContactCoverData.coverMap T h.valid)
    (MaxContactCoverData.balancedTunedIdeal T h.valid) x).trans_le (H.2 _)

theorem isMaxContactHypersurface_coverMaxContactIdeal :
    @IsMaxContactHypersurface (MaxContactCoverData.coverTriple T h.valid).base _
      (MaxContactCoverData.coverTriple T h.valid).scheme
      (MaxContactCoverData.coverTriple T h.valid).structMap
      (isAdmissible_coverTriple hstar P T h).locallyOfFiniteType
      (MaxContactCoverData.coverTriple T h.valid).ideal
      (MaxContactCoverData.coverTriple T h.valid).mult
      (MaxContactCoverData.coverMaxContactIdeal T h.valid) := by
  have hft : LocallyOfFiniteType
      (MaxContactCoverData.coverTriple T h.valid).structMap :=
    (isAdmissible_coverTriple hstar P T h).locallyOfFiniteType
  have key := hstar.coverContact_admissible T h.valid
    (MaxContactCoverData.isMaxContactCover_chosenCoverData T h.valid
      (hstar.exists_goodCover T h.valid h.orderLE))
  rw [MaxContactCoverData.coverTriple_mult]
  exact key

theorem inStrictNormalCrossingPosition_coverMaxContactIdeal :
    InStrictNormalCrossingPosition (MaxContactCoverData.coverTriple T h.valid).structMap
      [MaxContactCoverData.coverMaxContactIdeal T h.valid] :=
  hstar.coverContact_snc T h.valid
    (MaxContactCoverData.isMaxContactCover_chosenCoverData T h.valid
      (hstar.exists_goodCover T h.valid h.orderLE))


end

end BoundarySeparationByMaxContact


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LevelwiseIso
section


section

theorem strictTransform_top_eq_top {X' X : Scheme.{u}} (f : X' ⟶ X) (Z : X.IdealSheafData) :
    Blowup.strictTransform f Z ⊤ = ⊤ := by
  have h := comap_le_strictTransform f Z (⊤ : X.IdealSheafData)
  have h2 : (⊤ : X'.IdealSheafData) ≤ Blowup.strictTransform f Z ⊤ := by
    refine le_trans ?_ h
    simp
  exact top_le_iff.mp h2

theorem BlowupSequenceData.iteratedStrictTransform_top {X : Scheme.{u}} (d : BlowupSequenceData X) (i : ℕ) :
    d.iteratedStrictTransform i ⊤ = ⊤ := by
  induction i with
  | zero =>
      rw [BlowupSequenceData.iteratedStrictTransform_zero]
      simp
  | succ i ih =>
      rw [BlowupSequenceData.iteratedStrictTransform_succ, ih, strictTransform_top_eq_top]


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LowerDimReductionSmoothPullback
section


section

namespace StrictPullbackBlowupSeq

theorem smooth_map {X' X : Scheme.{u}} {g : X' ⟶ X} [Smooth g]
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (D : StrictPullbackBlowupSeq g t s)
    (i : ℕ) (hi : i ≤ t.length) : Smooth (D.comp i hi) := by
  have hsq : IsPullback (D.comp i hi) (t.projectionToBase i) (s.projectionToBase i) g :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism g t s t.length D.comp D.comp_zero
      D.pullback i hi
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (@Smooth : MorphismProperty Scheme.{u}) := inferInstance
  exact hbc.of_isPullback hsq.flip ‹Smooth g›

end StrictPullbackBlowupSeq

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

section
variable (u : MarkedBlowupSequenceData p I m E) {i j : ℕ} (h : i = j)

theorem ideal_congr_index :
    u.ideal i = (u.ideal j).comap (eqToHom (congrArg (fun n => u.obj n) h)) := by
  subst h
  simp

theorem boundary_congr_index :
    u.boundary i =
      (u.boundary j).map (fun A => A.comap (eqToHom (congrArg (fun n => u.obj n) h))) := by
  subst h
  simp


end

end MarkedBlowupSequenceData

theorem IsStrictPullbackBlowupSeq.of_eq {X' X : Scheme.{u}} {φ : X' ⟶ X} {B₁ B₂ : SequenceOfBlowups X'}
    {C₁ C₂ : SequenceOfBlowups X} (h₁ : B₁ = B₂) (h₂ : C₁ = C₂)
    (hh : IsStrictPullbackBlowupSeq φ B₁ C₁) : IsStrictPullbackBlowupSeq φ B₂ C₂ := by
  subst h₁
  subst h₂
  exact hh

namespace LowerDimReductionPullback

@[reducible] noncomputable def pullbackTriple (S : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}}
    (g : Y ⟶ S.scheme) : MarkedIdealWithBoundary.{u} :=
  S.pullbackAlong Y (g ≫ S.structMap) g

variable (S : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}} (g : Y ⟶ S.scheme)
  (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
  (t : MarkedBlowupSequenceData (pullbackTriple S g).structMap (pullbackTriple S g).ideal (pullbackTriple S g).mult
      (pullbackTriple S g).boundary)
  (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)

noncomputable def pullbackMapAtLength : t.obj t.length ⟶ s.obj s.length :=
  D.lastMap

theorem pullbackMapAtLength_eq_lastMap : pullbackMapAtLength S g s t D = D.lastMap := rfl

@[reducible] noncomputable def comapBoundaryPullback (L : List (s.obj s.length).IdealSheafData) :
    List (t.obj t.length).IdealSheafData :=
  L.map (fun A => A.comap (pullbackMapAtLength S g s t D))

private theorem eqToHom_comp_projectionToBase_consolidated395 {X : Scheme.{u}} (s : SequenceOfBlowups X) {a b : ℕ}
    (h : a = b) :
    eqToHom (congrArg (fun n => s.schemeAt n) h) ≫ s.projectionToBase b = s.projectionToBase a := by
  subst h
  simp

private theorem lastMap_comp_projectionToBase_consolidated395 {X' X : Scheme.{u}} {g : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (D : StrictPullbackBlowupSeq g t s) :
    D.lastMap ≫ s.projectionToBase s.length = t.projectionToBase t.length ≫ g := by
  have key := isPullback_projectionToBase_of_isPullback_blowupMorphism g t s t.length D.comp D.comp_zero
    D.pullback t.length le_rfl
  rw [StrictPullbackBlowupSeq.lastMap_eq, Category.assoc, eqToHom_comp_projectionToBase_consolidated395 s D.length_eq]
  exact key.w

theorem pullbackMapAtLength_comp_eq_comp_structureMorphism :
    pullbackMapAtLength S g s t D ≫ (s.proj s.length ≫ S.structMap) =
      t.proj t.length ≫ (g ≫ S.structMap) := by
  have h2 : pullbackMapAtLength S g s t D ≫ s.proj s.length = t.proj t.length ≫ g := by
    rw [MarkedBlowupSequenceData.projectionToBase_eq_toSequenceOfBlowups s s.length,
      MarkedBlowupSequenceData.projectionToBase_eq_toSequenceOfBlowups t t.length]
    exact lastMap_comp_projectionToBase_consolidated395 D
  have h3 : (pullbackMapAtLength S g s t D ≫ s.proj s.length) ≫ S.structMap
      = (t.proj t.length ≫ g) ≫ S.structMap :=
    congrArg (fun φ : t.obj t.length ⟶ S.scheme => φ ≫ S.structMap) h2
  exact (Category.assoc _ _ _).symm.trans (h3.trans (Category.assoc _ _ _))

theorem pullbackMapAtLength_comp_eq_pullbackTriple_structureMorphism :
    pullbackMapAtLength S g s t D ≫ (s.proj s.length ≫ S.structMap) =
      t.proj t.length ≫ (pullbackTriple S g).structMap := by
  have h : g ≫ S.structMap = (pullbackTriple S g).structMap :=
    (MarkedIdealWithBoundary.pullbackAlong_structureMorphism S Y (g ≫ S.structMap) g).symm
  refine (pullbackMapAtLength_comp_eq_comp_structureMorphism S g s t D).trans ?_
  exact congrArg (fun f => t.proj t.length ≫ f) h

private theorem comap_eq_comap_comp_eqToHom_consolidated395
    (F : ℕ → Scheme.{u}) (J : ∀ n : ℕ, (F n).IdealSheafData) {a b : ℕ} (hab : a = b)
    {Z : Scheme.{u}} (f : Z ⟶ F a) :
    (J a).comap f = (J b).comap (f ≫ eqToHom (congrArg F hab)) := by
  subst hab
  simp

theorem ideal_eq_comap_pullbackMapAtLength :
    t.ideal t.length = (s.ideal s.length).comap (pullbackMapAtLength S g s t D) := by
  have hL : t.length = s.length := D.length_eq
  have key := MarkedBlowupSequenceData.ideal_eq_comap_controlledTransform (I := S.ideal) (m := S.mult) (E := S.boundary)
    (d := s.toBlowupSequenceData) t D s.isMarked.divisible t.length le_rfl
  refine key.trans ?_
  rw [s.controlledTransform_eq_ideal t.length hL.le]
  exact comap_eq_comap_comp_eqToHom_consolidated395 s.obj s.ideal hL _

private theorem boundary_eq_map_comap_strictPullbackComparisonMap_consolidated395 {K : Type u} [Field K] {XX' XX : Scheme.{u}}
    {qq : XX' ⟶ Spec (CommRingCat.of K)} {gg : XX' ⟶ XX} [Flat gg]
    {II : XX.IdealSheafData} {mm : ℕ} {EE : List XX.IdealSheafData} {dd : BlowupSequenceData XX}
    (tt : MarkedBlowupSequenceData qq (II.comap gg) mm (EE.map fun A => A.comap gg))
    (DD : StrictPullbackBlowupSeq gg tt.toMarkedSequenceOfBlowups.toSequenceOfBlowups dd.toSequenceOfBlowups)
    (hNd : ∀ i ≤ dd.length, IsLocallyNoetherian (dd.obj i))
    (hNt : ∀ i ≤ tt.length, IsLocallyNoetherian (tt.obj i))
    (i j : ℕ) (hi : i ≤ tt.length) (hij : i = j) :
    tt.boundary i =
      (dd.boundaryFrom EE j).map
        (fun A => A.comap (tt.strictPullbackComparisonMap DD i hi ≫ eqToHom (congrArg (fun n => dd.obj n) hij))) := by
  subst hij
  simp only [eqToHom_refl, Category.comp_id]
  exact tt.boundary_eq_comap_strictPullbackComparisonMap DD hNd hNt i hi

theorem boundary_eq_map_comap_pullbackMapAtLength [Flat g]
    (hNs : ∀ i ≤ s.length, IsLocallyNoetherian (s.obj i))
    (hNt : ∀ i ≤ t.length, IsLocallyNoetherian (t.obj i)) :
    t.boundary t.length =
      (s.boundary s.length).map (fun A => A.comap (pullbackMapAtLength S g s t D)) := by
  have hlen : t.length = s.length := D.length_eq
  have key := boundary_eq_map_comap_strictPullbackComparisonMap_consolidated395 (dd := s.toBlowupSequenceData) (II := S.ideal) (mm := S.mult)
    (EE := S.boundary) (gg := g) t D hNs hNt t.length s.length le_rfl hlen
  rw [MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq s s.length le_rfl] at key
  exact key

private theorem smooth_comp_eqToHom_consolidated395 {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (h : Y = Y')
    (hf : Smooth f) : Smooth (f ≫ eqToHom h) := by
  subst h
  simp only [eqToHom_refl, Category.comp_id]
  exact hf

private theorem smooth_lastMap_consolidated395 {X' X : Scheme.{u}} {g : X' ⟶ X}
    [Smooth g] {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (D : StrictPullbackBlowupSeq g t s) : Smooth D.lastMap := by
  rw [StrictPullbackBlowupSeq.lastMap_eq]
  exact smooth_comp_eqToHom_consolidated395 _ _ (StrictPullbackBlowupSeq.smooth_map D t.length le_rfl)

theorem smooth_pullbackMapAtLength [Smooth g] :
    Smooth (pullbackMapAtLength S g s t D) := by
  rw [pullbackMapAtLength_eq_lastMap]
  exact smooth_lastMap_consolidated395 D

private theorem surjective_comp_eqToHom_consolidated395 {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (hf : AlgebraicGeometry.Surjective f) (h : Y = Z) :
    AlgebraicGeometry.Surjective (f ≫ eqToHom h) := by
  subst h
  rw [eqToHom_refl, Category.comp_id]
  exact hf

private theorem surjective_lastMap_consolidated395 {X' X : Scheme.{u}} {g : X' ⟶ X}
    [AlgebraicGeometry.Surjective g] {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (D : StrictPullbackBlowupSeq g t s) : AlgebraicGeometry.Surjective D.lastMap := by
  rw [StrictPullbackBlowupSeq.lastMap_eq]
  exact surjective_comp_eqToHom_consolidated395 _
    (surjective_of_isPullback_blowupMorphism g t s t.length D.comp D.comp_zero D.pullback
      t.length le_rfl) _

theorem surjective_pullbackMapAtLength [AlgebraicGeometry.Surjective g] :
    AlgebraicGeometry.Surjective (pullbackMapAtLength S g s t D) := by
  rw [pullbackMapAtLength_eq_lastMap]
  exact surjective_lastMap_consolidated395 D

private theorem balancedTunedSheaf_congr_consolidated395 (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} {p q : X ⟶ Spec (CommRingCat.of k)} (hpq : p = q)
    (hp : LocallyOfFiniteType p)
    (hq : LocallyOfFiniteType q)
    {I J : X.IdealSheafData} (hIJ : I = J) {m n : ℕ} (hmn : m = n) :
    @balancedTunedSheaf k _ _ X p hp I m = @balancedTunedSheaf k _ _ X q hq J n := by
  subst hpq
  subst hIJ
  subst hmn
  rfl

section
variable [Smooth g] (hftS : LocallyOfFiniteType (s.proj s.length ≫ S.structMap)) (hftT : LocallyOfFiniteType (t.proj t.length ≫ (pullbackTriple S g).structMap)) (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) (hVc : (MaxContactCoverData.derivedTriple S s hftS extra keep).IsAdmissible)
include hVc

theorem tunedIdealAtLength_comap_pullbackMapAtLength :
    (tunedIdealAtLength S s hftS).comap (pullbackMapAtLength S g s t D) = tunedIdealAtLength (pullbackTriple S g) t hftT := by
  have hmor : pullbackMapAtLength S g s t D ≫ (s.proj s.length ≫ S.structMap)
      = t.proj t.length ≫ (pullbackTriple S g).structMap := pullbackMapAtLength_comp_eq_pullbackTriple_structureMorphism S g s t D
  have hid : t.ideal t.length = (s.ideal s.length).comap (pullbackMapAtLength S g s t D) :=
    ideal_eq_comap_pullbackMapAtLength S g s t D
  have hsm : Smooth (s.proj s.length ≫ S.structMap) := by
    have h0 := hVc.smooth
    rwa [structureMorphism_derivedTriple S s hftS extra keep] at h0
  have := hftS
  have := hftT
  have := smooth_pullbackMapAtLength S g s t D
  have : LocallyOfFiniteType
      (pullbackMapAtLength S g s t D ≫ (s.proj s.length ≫ S.structMap)) := by
    rw [hmor]
    exact hftT
  rw [tunedIdealAtLength_eq_balancedTunedSheaf, tunedIdealAtLength_eq_balancedTunedSheaf,
    ← balancedTunedSheaf_comap S.base (s.proj s.length ≫ S.structMap) (pullbackMapAtLength S g s t D)
      (s.ideal s.length) S.mult]
  exact balancedTunedSheaf_congr_consolidated395 S.base hmor _ _ hid.symm
    (MarkedIdealWithBoundary.pullbackAlong_mult S Y (g ≫ S.structMap) g).symm

theorem pullbackAlong_derivedTriple_eq :
    ((MaxContactCoverData.derivedTriple S s hftS extra keep).pullbackAlong (t.obj t.length)
          (pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap)
          (pullbackMapAtLength S g s t D)).withBoundary
        (@List.append (t.obj t.length).IdealSheafData (comapBoundaryPullback S g s t D extra)
          ((t.boundary t.length).drop keep)) =
      MaxContactCoverData.derivedTriple (pullbackTriple S g) t hftT (comapBoundaryPullback S g s t D extra) keep := by
  have hstruct : pullbackMapAtLength S g s t D ≫ (s.proj s.length ≫ S.structMap)
      = t.proj t.length ≫ (pullbackTriple S g).structMap := pullbackMapAtLength_comp_eq_pullbackTriple_structureMorphism S g s t D
  have hideal : (tunedIdealAtLength S s hftS).comap (pullbackMapAtLength S g s t D) = tunedIdealAtLength (pullbackTriple S g) t hftT :=
    tunedIdealAtLength_comap_pullbackMapAtLength S g s t D hftS hftT extra keep hVc
  simp only [MaxContactCoverData.derivedTriple, MarkedIdealWithBoundary.pullbackAlong, MarkedIdealWithBoundary.withBoundary]
  congr 1


end

private theorem map_comap_append_drop_consolidated395 {X₁ X₂ : Scheme.{u}} (f : X₁ ⟶ X₂)
    (E Bd : List X₂.IdealSheafData) (Bd' : List X₁.IdealSheafData) (n : ℕ)
    (h : Bd' = Bd.map (fun A' => A'.comap f)) :
    List.map (fun Dv : X₂.IdealSheafData => Dv.comap f) (E ++ Bd.drop n)
      = List.map (fun Dv : X₂.IdealSheafData => Dv.comap f) E ++ Bd'.drop n := by
  subst h
  rw [List.map_append, List.map_drop]

private theorem isStrictPullbackBlowupSeq_of_isBoundaryDivisorReduction_consolidated395 {P : ℕ → Prop} {jj : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsBoundaryDivisorReduction P jj A B) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : P T.krullDimSucc)
    (hO : T.IsOrderBoundedByMult)
    (hft : LocallyOfFiniteType T.structMap) (hD : T.IsBalanced hft)
    (hjb : jj < T.boundary.length)
    (Yv : Scheme.{u}) (q : Yv ⟶ Spec (CommRingCat.of T.base)) (h : Yv ⟶ T.scheme)
    (hsm : Smooth h) (hsu : AlgebraicGeometry.Surjective h)
    (hq : h ≫ T.structMap = q) (E' : List Yv.IdealSheafData)
    (hbe : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Yv q h).boundary E')
    (htake : List.take (jj + 1) E' = List.take (jj + 1) (T.pullbackAlong Yv q h).boundary)
    (hV2 : ((T.pullbackAlong Yv q h).withBoundary E').IsAdmissible)
    (hP2 : P ((T.pullbackAlong Yv q h).withBoundary E').krullDimSucc)
    (hO2 : ((T.pullbackAlong Yv q h).withBoundary E').IsOrderBoundedByMult)
    (hft2 : LocallyOfFiniteType
      ((T.pullbackAlong Yv q h).withBoundary E').structMap)
    (hD2 : ((T.pullbackAlong Yv q h).withBoundary E').IsBalanced hft2)
    (hjb2 : jj < ((T.pullbackAlong Yv q h).withBoundary E').boundary.length) :
    IsStrictPullbackBlowupSeq h (A ((T.pullbackAlong Yv q h).withBoundary E')).toSequenceOfBlowups
      (A T).toSequenceOfBlowups := by
  have := hsm
  have := hsu
  exact hspec.smooth_pullback_strict T hV hP hO hD hjb Yv q h hq E' hbe htake hV2 hP2 hO2 hD2 hjb2

theorem nonempty_strictPullback_appendLowerDimReduction [Smooth g] [Flat g]
    [AlgebraicGeometry.Surjective g]
    (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u}) (j : ℕ)
    (hspec : IsBoundaryDivisorReduction P j (A j) B)
    (rc : (S' : MarkedIdealWithBoundary.{u}) → S'.krullDimSucc ≤ T.krullDimSucc → ℕ → S'.SequenceOfBlowups)
    (hrc : ∀ (S' : MarkedIdealWithBoundary.{u}) (h : S'.krullDimSucc ≤ T.krullDimSucc) (i : ℕ), rc S' h i = A i S')
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)
    (hftS : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hftT : LocallyOfFiniteType (t.proj t.length ≫ (pullbackTriple S g).structMap))
    (hV : S.IsAdmissible) (hm : 1 ≤ S.mult)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hNs : ∀ i ≤ s.length, IsLocallyNoetherian (s.obj i))
    (hV' : (pullbackTriple S g).IsAdmissible)
    (hO' : ∀ x : ↥(pullbackTriple S g).scheme,
      orderAt (pullbackTriple S g).ideal x ≤ (((pullbackTriple S g).mult : ℕ) : ℕ∞))
    (hNt : ∀ i ≤ t.length, IsLocallyNoetherian (t.obj i))
    (hdim : (MaxContactCoverData.derivedTriple S s hftS extra keep).krullDimSucc ≤ T.krullDimSucc)
    (hP : P (MaxContactCoverData.derivedTriple S s hftS extra keep).krullDimSucc)
    (hVc : (MaxContactCoverData.derivedTriple S s hftS extra keep).IsAdmissible)
    (hj : j < (extra ++ (s.boundary s.length).drop keep).length)
    (hsep : ∀ Dv ∈ (s.boundary s.length).take keep,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (Dv.support : Set ↥(s.obj s.length)) = ∅)
    (hdim' : (MaxContactCoverData.derivedTriple (pullbackTriple S g) t hftT
      (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep).krullDimSucc ≤ T.krullDimSucc)
    (hP' : P (MaxContactCoverData.derivedTriple (pullbackTriple S g) t hftT
      (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep).krullDimSucc)
    (hVc' : (MaxContactCoverData.derivedTriple (pullbackTriple S g) t hftT
      (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep).IsAdmissible)
    (hj' : j < (@List.append (t.obj t.length).IdealSheafData
      (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap)
      ((t.boundary t.length).drop keep)).length)
    (hsep' : ∀ Dv ∈ (t.boundary t.length).take keep,
      orderAtLeastLocus (t.ideal t.length) (pullbackTriple S g).mult ∩
        (Dv.support : Set ↥(t.obj t.length)) = ∅) :
    Nonempty (StrictPullbackBlowupSeq g
      (MaxContactReduction.appendLowerDimReduction hinv T rc (pullbackTriple S g) t
        (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap)
        keep j).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.appendLowerDimReduction hinv T rc S s extra keep j).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  have hsm : Smooth (pullbackMapAtLength S g s t D) := smooth_pullbackMapAtLength S g s t D
  have hsu : AlgebraicGeometry.Surjective (pullbackMapAtLength S g s t D) := surjective_pullbackMapAtLength S g s t D
  have hmult : (pullbackTriple S g).mult = S.mult :=
    MarkedIdealWithBoundary.pullbackAlong_mult S Y (g ≫ S.structMap) g
  have hm' : 1 ≤ (pullbackTriple S g).mult := le_of_le_of_eq hm hmult.symm
  have hb1 : (MaxContactCoverData.derivedTriple S s hftS extra keep).boundary
      = extra ++ (s.boundary s.length).drop keep := rfl
  have hbd : ((MaxContactCoverData.derivedTriple S s hftS extra keep).pullbackAlong (t.obj t.length)
        (pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap)
        (pullbackMapAtLength S g s t D)).boundary
      = comapBoundaryPullback S g s t D extra ++ (t.boundary t.length).drop keep := by
    refine (MarkedIdealWithBoundary.pullbackAlong_boundary (MaxContactCoverData.derivedTriple S s hftS extra keep)
        (t.obj t.length)
        (pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap)
        (pullbackMapAtLength S g s t D)).trans ?_
    exact map_comap_append_drop_consolidated395 (pullbackMapAtLength S g s t D) extra (s.boundary s.length)
      (t.boundary t.length) keep (boundary_eq_map_comap_pullbackMapAtLength S g s t D hNs hNt)
  have hbe : MarkedIdealWithBoundary.SameNontrivialBoundary
      ((MaxContactCoverData.derivedTriple S s hftS extra keep).pullbackAlong (t.obj t.length)
        (pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap)
        (pullbackMapAtLength S g s t D)).boundary
      (comapBoundaryPullback S g s t D extra ++ (t.boundary t.length).drop keep) := by
    have hrefl : ∀ L L' : List (t.obj t.length).IdealSheafData,
        L = L' → MarkedIdealWithBoundary.SameNontrivialBoundary L L' := by
      rintro L L' rfl
      exact MarkedIdealWithBoundary.SameNontrivialBoundary.refl L
    exact hrefl _ _ hbd
  have htake : List.take (j + 1) (comapBoundaryPullback S g s t D extra ++ (t.boundary t.length).drop keep)
      = List.take (j + 1)
          (((MaxContactCoverData.derivedTriple S s hftS extra keep).pullbackAlong (t.obj t.length)
            (pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap)
            (pullbackMapAtLength S g s t D)).boundary) :=
    congrArg (fun l => List.take (j + 1) l) hbd.symm
  have hkey : ((MaxContactCoverData.derivedTriple S s hftS extra keep).pullbackAlong (t.obj t.length)
        (pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap)
        (pullbackMapAtLength S g s t D)).withBoundary
        (comapBoundaryPullback S g s t D extra ++ (t.boundary t.length).drop keep)
      = MaxContactCoverData.derivedTriple (pullbackTriple S g) t hftT
          (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep :=
    pullbackAlong_derivedTriple_eq S g s t D hftS hftT extra keep hVc
  have hO1 : (MaxContactCoverData.derivedTriple S s hftS extra keep).IsOrderBoundedByMult :=
    isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hftS extra keep hVc
  have hD1 := isBalanced_derivedTriple hstar S hV hm hO s hftS extra keep hVc
  have hjb1 : j < (MaxContactCoverData.derivedTriple S s hftS extra keep).boundary.length := by
    rw [hb1]
    exact hj
  have hO2' := isOrderBoundedByMult_derivedTriple hstar (pullbackTriple S g) hV' hm' hO' t hftT
      (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep hVc'
  have hD2' := isBalanced_derivedTriple hstar (pullbackTriple S g) hV' hm' hO' t hftT
      (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep hVc'
  have hfacts : ∀ T' : MarkedIdealWithBoundary.{u},
      T' = MaxContactCoverData.derivedTriple (pullbackTriple S g) t hftT
        (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep →
      T'.IsAdmissible ∧ P T'.krullDimSucc ∧ T'.IsOrderBoundedByMult ∧ j < T'.boundary.length ∧
        ∀ hft : LocallyOfFiniteType T'.structMap, T'.IsBalanced hft := by
    rintro T' rfl
    exact ⟨hVc', hP', hO2', hj', fun _ => hD2'⟩
  obtain ⟨hV2, hP2, hO2, hjb2, hD2⟩ := hfacts _ hkey
  have h0 := isStrictPullbackBlowupSeq_of_isBoundaryDivisorReduction_consolidated395 hspec (MaxContactCoverData.derivedTriple S s hftS extra keep)
      hVc hP hO1 _ hD1 hjb1 (t.obj t.length)
      (pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap)
      (pullbackMapAtLength S g s t D) hsm hsu rfl
      (comapBoundaryPullback S g s t D extra ++ (t.boundary t.length).drop keep) hbe htake
      hV2 hP2 hO2 hV2.locallyOfFiniteType (hD2 hV2.locallyOfFiniteType) hjb2
  have hspb : IsStrictPullbackBlowupSeq (pullbackMapAtLength S g s t D)
      (A j (MaxContactCoverData.derivedTriple (pullbackTriple S g) t hftT
        (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep)).toSequenceOfBlowups
      (A j (MaxContactCoverData.derivedTriple S s hftS extra keep)).toSequenceOfBlowups :=
    IsStrictPullbackBlowupSeq.of_eq (eq_of_heq ((A j).toSequenceOfBlowups_heq_of_eq hkey)) rfl h0
  obtain ⟨hmkS, hSeq, -⟩ := appendLowerDimReduction_eq_append hstar hinv T P A B j hspec rc hrc S hV hm hO s
    extra keep hftS hdim hP hVc hj hsep
  obtain ⟨hmkT, hTeq, -⟩ := appendLowerDimReduction_eq_append hstar hinv T P A B j hspec rc hrc (pullbackTriple S g)
    hV' hm' hO' t (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep
    hftT hdim' hP' hVc' hj' hsep'
  rw [hSeq, hTeq]
  refine ⟨(MarkedBlowupSequenceData.isStrictPullbackBlowupSeq_append g s _ t _ hinv D ?_).toStrictPullbackBlowupSeq⟩
  exact (IsStrictPullbackBlowupSeq.of_eq
    (BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups _ _ _ _ _ hmkT).symm
    (BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups _ _ _ _ _ hmkS).symm
    ((hspb.of_isomorphic_pullback (BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _).symm).of_isomorphic_base
      (BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _).symm)).toStrictPullbackBlowupSeq

end LowerDimReductionPullback


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCover
section

open CategoryTheory.Limits

section

namespace MaxContactOpenCover

private theorem isOpenImmersion_fst_of_isPullback_consolidated392
    {P' X' Y' Z' : Scheme.{u}} {p₁ : P' ⟶ X'} {p₂ : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (hsq : IsPullback p₁ p₂ f' g') (hg : IsOpenImmersion g') : IsOpenImmersion p₁ :=
  MorphismProperty.of_isPullback hsq.flip hg

theorem isLocalIsomorphism_fst_of_isPullback {P X Y Z : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hsq : IsPullback fst snd f g)
    (hg : MaxContactFunctoriality.IsLocalIsomorphism g) :
    MaxContactFunctoriality.IsLocalIsomorphism fst := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hg (snd.base x)
  exact ⟨_, hxU, isOpenImmersion_fst_of_isPullback_consolidated392
    ((isPullback_morphismRestrict snd U).flip.paste_horiz hsq) hU⟩

abbrev coverPiece (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) : Scheme.{u} :=
  (((MaxContactCoverData.chosenCoverData T hv).opens i : T.scheme.Opens) : Scheme.{u})

abbrev coverPieceι (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    coverPiece T hv i ⟶ (MaxContactCoverData.coverTriple T hv).scheme :=
  Sigma.ι (fun j : (MaxContactCoverData.chosenCoverData T hv).idx =>
    (((MaxContactCoverData.chosenCoverData T hv).opens j : T.scheme.Opens) : Scheme.{u})) i

theorem isOpenImmersion_coverPieceι (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    IsOpenImmersion (coverPieceι T hv i) := by
  have h : IsOpenImmersion (Sigma.ι (fun j : (MaxContactCoverData.chosenCoverData T hv).idx =>
      (((MaxContactCoverData.chosenCoverData T hv).opens j : T.scheme.Opens) : Scheme.{u})) i) :=
    inferInstance
  exact h

instance instIsOpenImmersionStarι (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    IsOpenImmersion (coverPieceι T hv i) :=
  isOpenImmersion_coverPieceι T hv i

abbrev coverTripleOpen (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    (MaxContactCoverData.coverTriple T hv).scheme.Opens :=
  (coverPieceι T hv i).opensRange

abbrev coverTriplePiece (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) : Scheme.{u} :=
  ((coverTripleOpen T hv i : (MaxContactCoverData.coverTriple T hv).scheme.Opens) : Scheme.{u})

theorem range_coverPieceι (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    Set.range (coverPieceι T hv i).base = Set.range (coverTripleOpen T hv i).ι.base :=
  ((coverTripleOpen T hv i).range_ι).symm

def coverPieceIso (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    coverPiece T hv i ≅ coverTriplePiece T hv i :=
  IsOpenImmersion.isoOfRangeEq (coverPieceι T hv i) (coverTripleOpen T hv i).ι (range_coverPieceι T hv i)

theorem exists_mem_coverTripleOpen (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (x : ↥(MaxContactCoverData.coverTriple T hv).scheme) :
    ∃ i : (MaxContactCoverData.chosenCoverData T hv).idx, x ∈ coverTripleOpen T hv i := by
  obtain ⟨⟨i, y⟩, hy⟩ := (AlgebraicGeometry.sigmaMk
    (fun j : (MaxContactCoverData.chosenCoverData T hv).idx =>
      (((MaxContactCoverData.chosenCoverData T hv).opens j : T.scheme.Opens) : Scheme.{u}))).surjective x
  refine ⟨i, ?_⟩
  show x ∈ Set.range (Sigma.ι (fun j : (MaxContactCoverData.chosenCoverData T hv).idx =>
    (((MaxContactCoverData.chosenCoverData T hv).opens j : T.scheme.Opens) : Scheme.{u})) i).base
  refine ⟨y, ?_⟩
  rw [← hy]
  simp

section
variable (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (i : (MaxContactCoverData.chosenCoverData T hv).idx)

private theorem coverPieceIso_inv_comp_coverPieceι_consolidated392 :
    (coverPieceIso T hv i).inv ≫ coverPieceι T hv i = (coverTripleOpen T hv i).ι := by
  apply AlgebraicGeometry.IsOpenImmersion.lift_fac

private theorem coverPieceι_comp_coverMap_consolidated392 :
    coverPieceι T hv i ≫ MaxContactCoverData.coverMap T hv =
      ((MaxContactCoverData.chosenCoverData T hv).opens i).ι := by
  rw [MaxContactCoverData.coverMap_eq_sigmaOpensDesc]
  exact sigma_ι_sigmaOpensDesc T.scheme (MaxContactCoverData.chosenCoverData T hv).opens i

theorem coverTripleOpen_ι_comp_coverMap :
    (coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv =
      (coverPieceIso T hv i).inv ≫ ((MaxContactCoverData.chosenCoverData T hv).opens i).ι := by
  have h := coverPieceIso_inv_comp_coverPieceι_consolidated392 T hv i
  calc (coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv
      = ((coverPieceIso T hv i).inv ≫ coverPieceι T hv i) ≫ MaxContactCoverData.coverMap T hv := by rw [h]
    _ = (coverPieceIso T hv i).inv ≫ (coverPieceι T hv i ≫ MaxContactCoverData.coverMap T hv) :=
        Category.assoc _ _ _
    _ = (coverPieceIso T hv i).inv ≫ ((MaxContactCoverData.chosenCoverData T hv).opens i).ι := by
        rw [coverPieceι_comp_coverMap_consolidated392 T hv i]

theorem restrictIdeal_coverTripleOpen (J : (MaxContactCoverData.coverTriple T hv).scheme.IdealSheafData) :
    restrictIdeal J (coverTripleOpen T hv i) = (J.comap (coverPieceι T hv i)).comap (coverPieceIso T hv i).inv := by
  simp only [restrictIdeal_eq_comap_ι, ← coverPieceIso_inv_comp_coverPieceι_consolidated392 T hv i,
    Scheme.IdealSheafData.comap_comp]


end

theorem isLocalIsomorphism_coverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    MaxContactFunctoriality.IsLocalIsomorphism (MaxContactCoverData.coverMap T hv) := by
  intro x
  obtain ⟨i, hxi⟩ := exists_mem_coverTripleOpen T hv x
  have hψ : IsOpenImmersion ((coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv) := by
    rw [coverTripleOpen_ι_comp_coverMap T hv i]
    infer_instance
  exact ⟨coverTripleOpen T hv i, hxi, hψ⟩

section
variable (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (i : (MaxContactCoverData.chosenCoverData T hv).idx) {n : ℕ} (c : EtaleChart T.structMap ((MaxContactCoverData.chosenCoverData T hv).opens i) n)

private theorem coverPieceIso_inv_comp_map_comp_affineSpaceFinToSpec_consolidated392 :
    ((coverPieceIso T hv i).inv ≫ c.map) ≫ affineSpaceFinToSpec T.base n =
      (coverTripleOpen T hv i).ι ≫ (MaxContactCoverData.coverMap T hv ≫ T.structMap) := by
  have h1 : c.map ≫ affineSpaceFinToSpec T.base n =
      ((MaxContactCoverData.chosenCoverData T hv).opens i).ι ≫ T.structMap := c.comp_struct
  have h2 := coverTripleOpen_ι_comp_coverMap T hv i
  calc ((coverPieceIso T hv i).inv ≫ c.map) ≫ affineSpaceFinToSpec T.base n
      = (coverPieceIso T hv i).inv ≫ (c.map ≫ affineSpaceFinToSpec T.base n) := Category.assoc _ _ _
    _ = (coverPieceIso T hv i).inv ≫ (((MaxContactCoverData.chosenCoverData T hv).opens i).ι ≫ T.structMap) := by
        rw [h1]
    _ = ((coverPieceIso T hv i).inv ≫ ((MaxContactCoverData.chosenCoverData T hv).opens i).ι) ≫ T.structMap :=
        (Category.assoc _ _ _).symm
    _ = ((coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv) ≫ T.structMap := by rw [h2]
    _ = (coverTripleOpen T hv i).ι ≫ (MaxContactCoverData.coverMap T hv ≫ T.structMap) :=
        Category.assoc _ _ _

private theorem etale_coverPieceIso_inv_comp_map_consolidated392 :
    Etale ((coverPieceIso T hv i).inv ≫ c.map) := by
  have : Etale c.map := c.isEtale
  have : IsIso (coverPieceIso T hv i).inv := inferInstance
  have : IsOpenImmersion (coverPieceIso T hv i).inv := inferInstance
  have : Etale (coverPieceIso T hv i).inv := inferInstance
  infer_instance


end

def coverEtaleChart (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) {n : ℕ}
    (c : EtaleChart T.structMap ((MaxContactCoverData.chosenCoverData T hv).opens i) n) :
    EtaleChart (MaxContactCoverData.coverMap T hv ≫ T.structMap) (coverTripleOpen T hv i) n where
  map := (coverPieceIso T hv i).inv ≫ c.map
  comp_struct := coverPieceIso_inv_comp_map_comp_affineSpaceFinToSpec_consolidated392 T hv i c
  isEtale := etale_coverPieceIso_inv_comp_map_consolidated392 T hv i c

theorem coverEtaleChart_coordIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) {n : ℕ}
    (c : EtaleChart T.structMap ((MaxContactCoverData.chosenCoverData T hv).opens i) n)
    (S : Finset (Fin n)) :
    (coverEtaleChart T hv i c).coordIdeal S = (c.coordIdeal S).comap (coverPieceIso T hv i).inv := by
  have key : (coordSubspaceIdeal T.base n S).comap ((coverPieceIso T hv i).inv ≫ c.map)
      = ((coordSubspaceIdeal T.base n S).comap c.map).comap (coverPieceIso T hv i).inv := by
    rw [Scheme.IdealSheafData.comap_comp]
  have h1 : (coverEtaleChart T hv i c).coordIdeal S
      = (coordSubspaceIdeal T.base n S).comap ((coverPieceIso T hv i).inv ≫ c.map) :=
    EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal (coverEtaleChart T hv i c) S
  have h2 : (c.coordIdeal S).comap (coverPieceIso T hv i).inv
      = ((coordSubspaceIdeal T.base n S).comap c.map).comap (coverPieceIso T hv i).inv :=
    congrArg (fun J => J.comap (coverPieceIso T hv i).inv) (EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal c S)
  exact h1.trans (key.trans h2.symm)

private theorem compactSpace_of_quasiCompact_toSpec_consolidated392 {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) (hf : QuasiCompact f) : CompactSpace ↥X := by
  have := hf
  exact QuasiCompact.compactSpace_of_compactSpace f

section
variable (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)

private theorem exists_affineOpen_maxContactCoord_or_disjoint_locus_consolidated392 [LocallyOfFiniteType T.structMap]
    (h : ∀ x : ↥T.scheme,
      orderAt (MaxContactCoverData.balancedTunedIdeal T hv) x ≤ ((MaxContactCoverData.tunedMult T : ℕ) : ℕ∞))
    (x : ↥T.scheme) :
    ∃ (V : T.scheme.Opens) (J : (V : Scheme.{u}).IdealSheafData),
      x ∈ V ∧ IsAffineOpen V ∧
        ((Disjoint (orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
              (V : Set ↥T.scheme) ∧ J = ⊤) ∨
          ∃ (n : ℕ) (c : EtaleChart T.structMap V n) (j : Fin n),
            J = c.coordIdeal {j} ∧
              MaxContactReduction.IsMaxContactCoord T.base T.structMap
                (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) c j) := by
  classical
  have := hv.charZero
  have := hv.smooth
  have hm : 1 ≤ MaxContactCoverData.tunedMult T := one_le_tuningExponent T.mult
  by_cases hx : x ∈ orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)
  · have hord : orderAt (MaxContactCoverData.balancedTunedIdeal T hv) x
        = ((MaxContactCoverData.tunedMult T : ℕ) : ℕ∞) :=
      le_antisymm (h x) ((mem_orderAtLeastLocus_iff _ _ _).1 hx)
    obtain ⟨V, hVaff, hxV, n, c, j, hmc, -⟩ :=
      exists_isMaxContactCoord T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv) hm x hord
    exact ⟨V, c.coordIdeal {j}, hxV, hVaff, Or.inr ⟨n, c, j, rfl, hmc⟩⟩
  · have hcl : IsClosed
        (orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)) :=
      isClosed_orderAtLeastLocus T.base T.structMap _ _
    obtain ⟨V, n, hxV, hVW, hVaff, -⟩ :=
      exists_etaleChart_le T.structMap x
        ⟨(orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))ᶜ,
          hcl.isOpen_compl⟩ hx
    refine ⟨V, ⊤, hxV, hVaff, Or.inl ⟨?_, rfl⟩⟩
    refine Set.disjoint_left.2 ?_
    intro y hyS hyV
    exact (hVW hyV) hyS

theorem exists_isMaxContactCover (h : ∀ x : ↥T.scheme,
      orderAt (MaxContactCoverData.balancedTunedIdeal T hv) x ≤ ((MaxContactCoverData.tunedMult T : ℕ) : ℕ∞)) :
    ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T,
      MaxContactReduction.IsMaxContactCover T D hv.locallyOfFiniteType (MaxContactCoverData.balancedTunedIdeal T hv)
        (MaxContactCoverData.tunedMult T) := by
  classical
  have := hv.locallyOfFiniteType
  have : CompactSpace ↥T.scheme := compactSpace_of_quasiCompact_toSpec_consolidated392 T.structMap hv.quasiCompact
  choose V J hxV hVaff hdich using exists_affineOpen_maxContactCoord_or_disjoint_locus_consolidated392 T hv h
  have hcover : (Set.univ : Set ↥T.scheme) ⊆
      ⋃ x : ↥T.scheme, ((V x : T.scheme.Opens) : Set ↥T.scheme) := by
    intro y _
    exact Set.mem_iUnion.2 ⟨y, hxV y⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : ↥T.scheme => ((V x : T.scheme.Opens) : Set ↥T.scheme))
    (fun x => (V x).isOpen) hcover
  refine ⟨{ idx := {y : ↥T.scheme // y ∈ t},
            finiteIdx := inferInstance,
            opens := fun i => V i.1,
            localIdeal := fun i => J i.1 }, ?_, ?_, ?_⟩
  · refine le_antisymm le_top ?_
    intro y _
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hyi⟩
  · exact fun i => hVaff i.1
  · exact fun i => hdich i.1


end

def tunedTriple (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) : MarkedIdealWithBoundary.{u} where
  base := T.base
  scheme := T.scheme
  structMap := T.structMap
  ideal := MaxContactCoverData.balancedTunedIdeal T hv
  mult := MaxContactCoverData.tunedMult T
  boundary := T.boundary

section
variable (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)

@[simp] theorem tunedTriple_baseField :
    (tunedTriple T hv).base = T.base := rfl

@[simp] theorem tunedTriple_scheme :
    (tunedTriple T hv).scheme = T.scheme := rfl

@[simp] theorem tunedTriple_structureMorphism :
    (tunedTriple T hv).structMap = T.structMap := rfl

@[simp] theorem tunedTriple_ideal :
    (tunedTriple T hv).ideal = MaxContactCoverData.balancedTunedIdeal T hv := rfl

@[simp] theorem tunedTriple_mult :
    (tunedTriple T hv).mult = MaxContactCoverData.tunedMult T := rfl

@[simp] theorem tunedTriple_boundary :
    (tunedTriple T hv).boundary = T.boundary := rfl

theorem isAdmissible_tunedTriple (hnz : NonzeroOnComponents (MaxContactCoverData.balancedTunedIdeal T hv)) :
    (tunedTriple T hv).IsAdmissible :=
  { charZero := hv.charZero
    locallyOfFiniteType := hv.locallyOfFiniteType
    nonzeroOnComponents := hnz
    one_le_mult := one_le_tuningExponent T.mult
    quasiCompact := hv.quasiCompact
    smooth := hv.smooth
    snc := hv.snc }

theorem coverTriple_eq_tunedTriple_pullbackAlong :
    MaxContactCoverData.coverTriple T hv =
      (tunedTriple T hv).pullbackAlong (MaxContactCoverData.chosenCoverData T hv).disjointUnion
        (MaxContactCoverData.coverMap T hv ≫ T.structMap) (MaxContactCoverData.coverMap T hv) :=
  rfl


end

section
variable (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
include hgood

theorem isAffine_coverTriple_scheme :
    IsAffine (MaxContactCoverData.coverTriple T hv).scheme :=
  isAffine_sigmaOpens T.scheme (MaxContactCoverData.chosenCoverData T hv).opens hgood.isAffine

theorem quasiCompact_coverMap_comp_structureMorphism :
    QuasiCompact (MaxContactCoverData.coverMap T hv ≫ T.structMap) := by
  have : IsAffine ((MaxContactCoverData.chosenCoverData T hv).disjointUnion) :=
    isAffine_coverTriple_scheme T hv hgood
  have : IsAffine (MaxContactCoverData.coverTriple T hv).scheme :=
    isAffine_coverTriple_scheme T hv hgood
  have : Subsingleton ↥(AlgebraicGeometry.Spec (CommRingCat.of T.base)) := inferInstance
  constructor
  intro U _hU _hUc
  by_cases hUe : U = ∅
  · subst hUe
    rw [Set.preimage_empty]
    exact isCompact_empty
  · have hUu : U = Set.univ := by
      obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.mpr hUe
      refine Set.eq_univ_of_forall fun z => ?_
      rwa [Subsingleton.elim z u]
    subst hUu
    rw [Set.preimage_univ]
    exact isCompact_univ


end

private theorem isEmpty_irreducibleCloseds_of_isEmpty_consolidated392 {C : Type u} [TopologicalSpace C] (h : IsEmpty C) :
    IsEmpty (TopologicalSpace.IrreducibleCloseds C) :=
  ⟨fun Z => h.elim Z.2.1.choose⟩

private theorem topologicalKrullDim_le_of_isEmpty_consolidated392 {C B : Type u} [TopologicalSpace C]
    [TopologicalSpace B] (h : IsEmpty C) :
    topologicalKrullDim C ≤ topologicalKrullDim B := by
  have := isEmpty_irreducibleCloseds_of_isEmpty_consolidated392 h
  show Order.krullDim (TopologicalSpace.IrreducibleCloseds C)
      ≤ Order.krullDim (TopologicalSpace.IrreducibleCloseds B)
  exact Order.krullDim_le_of_strictMono
    (fun Z : TopologicalSpace.IrreducibleCloseds C => isEmptyElim Z)
    (fun a _ _ => isEmptyElim a)

private theorem topologicalKrullDim_ne_bot_consolidated392 {B : Type u} [TopologicalSpace B] (b : B) :
    topologicalKrullDim B ≠ ⊥ := by
  intro hb
  have hb' : Order.krullDim (TopologicalSpace.IrreducibleCloseds B) = ⊥ := hb
  have hE : IsEmpty (TopologicalSpace.IrreducibleCloseds B) := Order.krullDim_eq_bot_iff.mp hb'
  exact hE.elim ⟨closure {b}, isIrreducible_singleton.closure, isClosed_closure⟩

private theorem topologicalKrullDim_le_of_isOpenImmersion_consolidated392 {P Q : Scheme.{u}} (f : P ⟶ Q)
    (h : IsOpenImmersion f) : topologicalKrullDim ↥P ≤ topologicalKrullDim ↥Q := by
  have := h
  exact f.isOpenEmbedding.isInducing.topologicalKrullDim_le

section
variable (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)

private theorem topologicalKrullDim_coverTripleOpen_le_consolidated392 (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    topologicalKrullDim
        ↥(↑(coverTripleOpen T hv i) : Set ↥(MaxContactCoverData.coverTriple T hv).scheme)
      ≤ topologicalKrullDim ↥T.scheme := by
  have hψ : IsOpenImmersion ((coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv) := by
    rw [coverTripleOpen_ι_comp_coverMap T hv i]
    infer_instance
  exact topologicalKrullDim_le_of_isOpenImmersion_consolidated392
    ((coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv) hψ

theorem krullDimSucc_coverTriple_scheme_le_dim :
    krullDimSucc (MaxContactCoverData.coverTriple T hv).scheme ≤ T.krullDimSucc := by
  have hd : topologicalKrullDim ↥T.scheme < ⊤ := hv.topologicalKrullDim_lt_top
  by_cases hTe : IsEmpty ↥T.scheme
  · have hce : IsEmpty ↥(MaxContactCoverData.coverTriple T hv).scheme :=
      ⟨fun x => hTe.elim ((MaxContactCoverData.coverMap T hv).base x)⟩
    exact krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le _ _
      (topologicalKrullDim_le_of_isEmpty_consolidated392 hce) hd
  · obtain ⟨y⟩ : Nonempty ↥T.scheme := not_isEmpty_iff.mp hTe
    have hbot : topologicalKrullDim ↥T.scheme ≠ ⊥ := topologicalKrullDim_ne_bot_consolidated392 y
    obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hbot
    have hmtop : m ≠ ⊤ := by
      rintro rfl
      rw [WithBot.coe_top] at hm
      rw [← hm] at hd
      exact lt_irrefl _ hd
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hmtop
    have hdeq : topologicalKrullDim ↥T.scheme = ((k : ℕ) : WithBot ℕ∞) := by
      rw [← hm, ← hk]
      norm_cast
    refine krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le _ _ ?_ hd
    rw [hdeq]
    refine topologicalKrullDim_le_natCast_of_isOpenCover
      (fun i : (MaxContactCoverData.chosenCoverData T hv).idx =>
        (↑(coverTripleOpen T hv i) : Set ↥(MaxContactCoverData.coverTriple T hv).scheme))
      (fun i => (coverTripleOpen T hv i).isOpen) ?_ k ?_
    · refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨i, hi⟩ := exists_mem_coverTripleOpen T hv x
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    · intro i
      have hpiece := topologicalKrullDim_coverTripleOpen_le_consolidated392 T hv i
      rw [hdeq] at hpiece
      exact hpiece


end

end MaxContactOpenCover


end
end
end FunctorialResolution.EmbeddedResolution
end
