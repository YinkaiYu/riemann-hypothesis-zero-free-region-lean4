import Mathlib
import Core5.M18Principalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicGeometry
universe u
noncomputable section
-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionHypotheses
section


section
namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

structure DivisorReductionHypotheses (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) : Prop where
  trivial_of_coSupport_empty :
    ∀ (L : PrincipalizationAssignment.{u}) (j : ℕ) (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      j < T.boundary.length →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [Smooth h],
        h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
          (orderAtLeastLocus T.ideal T.mult).Nonempty →
          orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult = ∅ →
          ∀ (B' : SequenceOfBlowups Y), B'.length = 0 →
            IsPullbackBlowupSequence h B' (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups)
  baseChange : SmoothPullbackCompatibility.{u}
  smoothImpliesFlat : FlatOfSmooth.{u}
  degenerateTransversal : EmptyPulledBackCenterCompatibility.{u}
  fieldBaseChangeCompatibility : FieldBaseChangeCompatibility.{u}
  boundaryReindexingInvariance : BoundaryReindexingInvariance.{u}
  fieldLower : DivisorRestrictionFieldBaseChange.{u}
  divisorReduction : DivisorReductionStepProperties hres blowupPreservesNoetherian
  pushedBlowupSequenceProperties : PushedBlowupSequenceProperties hres blowupPreservesNoetherian

section
variable {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}} (hin : DivisorReductionHypotheses hres)
include hin

theorem DivisorReductionHypotheses.divisorReductionTerminationProperties :
    DivisorReductionTerminationProperties hres blowupPreservesNoetherian :=
  hin.divisorReduction.toDivisorReductionTerminationProperties

theorem DivisorReductionHypotheses.trivialPullbackBlowupSequence (L : PrincipalizationAssignment.{u}) (j : ℕ) :
    IsPullbackSeqOfEmptyBlowupSeq hres L j :=
  pullbackOfEmptySequence_of_isPullbackSequenceOfBlowups hres L j
    (fun T hV hj Y q h _ hq E' hV' hcs hcs' B' hB' =>
      hin.trivial_of_coSupport_empty L j T hV hj Y q h hq E' hV' hcs hcs' B' hB')

theorem DivisorReductionHypotheses.divisorReductionSeqEqAmbient (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (_hL : IsMaxOrderReduction (fun d => d < n) L O) :
    ∀ (j : ℕ) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReductionSeqEqAmbient hres L j T hV hj := by
  intro j T hV hj _hdim hO hD hcs
  have : IsNoetherian T.scheme := isNoetherian_scheme_of_isAdmissible T hV
  have h := divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hin.divisorReductionTerminationProperties L j T hV hj hO hD hcs.ne_empty
  rcases h with ⟨hZ, hpr, hmk, hstep⟩ | ⟨hZ, hb, hpr, hmk, hstep⟩
  · exact Or.inl ⟨hZ, hpr, hmk, hstep hmk⟩
  · exact Or.inr ⟨hZ, hb, hpr, hmk, hstep hmk⟩


end

end DivisorReduction

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})

private theorem strictPullbackOfSmoothBaseChangeOnDivisor_of_isMaxOrderReduction_consolidated432
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ) :
    DivisorReduction.StrictPullbackOfSmoothBaseChangeOnDivisor n L j := by
  constructor
  · intro T hV hdim hO hbal hj hcs Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'
    exact DivisorReduction.isStrictPullbackBlowupSeq_restrictToDivisor_of_eq_top hres hfacts n L O hL j hbc T hV hdim hO hbal
      hj hcs Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'
  · intro T hV hdim hO hbal hj hcs Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'
    exact DivisorReduction.isStrictPullbackBlowupSeq_restrictTwistedToDivisor hres hfacts n L O hL j hbc T hV hdim hO hbal
      hj hcs Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'

theorem isBoundaryDivisorReduction_divisorFamily_canonicalAlgorithmRules
    (hin : DivisorReduction.DivisorReductionHypotheses hres) :
    ∀ (n : ℕ) (L O : PrincipalizationAssignment.{u}),
      IsMaxOrderReduction (fun d => d < n) L O →
      ∀ (j : ℕ),
        IsBoundaryDivisorReduction (fun d => d ≤ n) j ((canonicalAlgorithmRules hres).divisorFamily L j) L := by
  intro n L O hL j
  have hshapeN : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj :=
    fun T hV hj hdim hO hbal hcs => hin.divisorReductionSeqEqAmbient n L O hL j T hV hj hdim hO hbal hcs
  have hshapeE : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      orderAtLeastLocus T.ideal T.mult ≠ ∅ → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj :=
    fun T hV hj hdim hO hbal hcs =>
      hshapeN T hV hj hdim hO hbal (Set.nonempty_iff_ne_empty.mpr hcs)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hV hdim hO hbal hj K _ _ f E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isPullbackBlowupSequence_fieldBaseChange_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties hin.baseChange
      hin.fieldBaseChangeCompatibility hin.fieldLower n L O hL j hshapeE T hV hdim hO hbal hj K f E' hBE htake
      hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj K _ _ f E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties
      hin.baseChange hin.fieldBaseChangeCompatibility hin.fieldLower n L O hL j hshapeE T hV hdim hO hbal hj K f E'
      hBE htake hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj i hi x
    exact divisorFamily_canonicalAlgorithmRules_orderAt_le_mult hres hin.divisorReductionTerminationProperties n L j T hV hdim hO hbal hj i hi x
  · intro T hV hdim hO hbal hj i hi
    exact divisorFamily_canonicalAlgorithmRules_center_nonempty hres hin.divisorReductionTerminationProperties n L O hL j T hV hdim hO hbal
      hj i hi
  · intro T hV hdim hO hbal hj hm J hVJ hdimJ him
    exact isPushforwardBlowupSeq_divisorFamily_canonicalAlgorithmRules hres hin.divisorReductionTerminationProperties n L O hL j T hV hdim hO
      (fun _ => hbal) hj hm J hVJ hdimJ him
  · intro T hV hdim hO hbal hj
    obtain ⟨D, b, h1, h2, h3, h4, h5, h6, h7⟩ :=
      exists_smoothDivisorSeq_divisorFamily_canonicalAlgorithmRules hres hin.divisorReductionTerminationProperties hin.pushedBlowupSequenceProperties n L O hL j T hV hdim hO
        hbal hj
    refine ⟨D, b, h1, h2, h3, h4, ?_, h6, ?_⟩
    · intro t ht hb
      exact h5 t ht (fun hbt h0 => hb ⟨hbt, h0⟩)
    · intro t ht hb
      exact h7 t ht (fun hbt h0 => hb ⟨hbt, h0⟩)
  · intro T hV hdim hO hbal hj Y q h _ hq E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isPullbackBlowupSequence hres hin.divisorReductionTerminationProperties hin.baseChange
      hin.smoothImpliesFlat n L j (hin.trivialPullbackBlowupSequence L j)
      (restrictedSmoothPullback_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties hin.baseChange
        hin.degenerateTransversal n L O hL j)
      hshapeN T hV hdim hO hbal hj Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isStrictPullbackBlowupSeq_of_smooth hres hin.divisorReductionTerminationProperties hin.baseChange
      hin.smoothImpliesFlat n L j
      (strictPullbackOfSmoothBaseChangeOnDivisor_of_isMaxOrderReduction_consolidated432 hres hin.divisorReductionTerminationProperties hin.baseChange n L O hL j)
      hshapeN T hV hdim hO hbal hj Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj hcs
    exact divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO hbal hj hcs

theorem isBoundaryPositionInvariant_divisorFamily_canonicalAlgorithmRules
    (hin : DivisorReduction.DivisorReductionHypotheses hres) :
    ∀ (n : ℕ) (L O : PrincipalizationAssignment.{u}),
      IsMaxOrderReduction (fun d => d < n) L O →
      IsBoundaryPositionInvariant (fun d => d ≤ n) fun j => (canonicalAlgorithmRules hres).divisorFamily L j :=
  fun n L O hL =>
    isBoundaryPositionInvariant_divisorFamily_of_divisorReductionSeqEqAmbient hres hin.divisorReductionTerminationProperties hin.baseChange hin.boundaryReindexingInvariance
      n L O hL (hin.divisorReductionSeqEqAmbient n L O hL)


end

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerIdealFunctoriality
section


section
namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem map_comap_id_consolidated421 {W : Scheme.{u}} (l : List W.IdealSheafData) :
    List.map (fun D : W.IdealSheafData => D.comap (𝟙 W)) l = l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [Scheme.IdealSheafData.comap_id]

section
variable {α : Type*} (A : List α)

private theorem take_eraseIdx_append_singleton_consolidated421 (e : α) (j n : ℕ)
    (hj : j < A.length) (hn : n = A.length - 1) :
    List.take n ((A ++ [e]).eraseIdx j) = A.eraseIdx j := by
  subst hn
  have hlen : (A.eraseIdx j).length = A.length - 1 := by
    rw [List.length_eraseIdx, if_pos hj]
  rw [List.eraseIdx_append_of_lt_length hj, ← hlen, List.take_left]

private theorem take_length_sub_one_eraseIdx_consolidated421 (j n : ℕ) (hj : j < A.length)
    (hn : n = A.length - 1) : List.take n (A.eraseIdx j) = A.eraseIdx j := by
  subst hn
  refine List.take_of_length_le ?_
  rw [List.length_eraseIdx, if_pos hj]


end

private theorem top_pow_consolidated421 {Y : Scheme.{u}} (m : ℕ) :
    (⊤ : Y.IdealSheafData) ^ m = ⊤ := by
  rw [← Scheme.IdealSheafData.one_eq_top, one_pow]

section
variable {X Y : Scheme.{u}} (g : Y ⟶ X)

private theorem residualByPow_comap_of_isLocallyGeneratedByNonZeroDivisor_consolidated421 (A F : X.IdealSheafData) (F' : Y.IdealSheafData) (m : ℕ) (hF' : F' = F.comap g)
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor F') (hex : ∃ B : X.IdealSheafData, F ^ m * B = A) :
    residualByPow (A.comap g) F' m = (residualByPow A F m).comap g := by
  have hdown : F ^ m * residualByPow A F m = A := pow_mul_residualByPow A F m hex
  have hup : F' ^ m * (residualByPow A F m).comap g = A.comap g := by
    rw [hF', ← Scheme.IdealSheafData.comap_pow, ← Scheme.IdealSheafData.comap_mul, hdown]
  have hup2 : F' ^ m * residualByPow (A.comap g) F' m = A.comap g :=
    pow_mul_residualByPow (A.comap g) F' m ⟨_, hup⟩
  exact (hcart.pow m).eq_of_mul_eq_mul (hup2.trans hup.symm)

private theorem sameNontrivialBoundary_eraseIdx_strictTransform_comap_of_flat_consolidated421 (hX : IsNoetherian X) (hY : IsNoetherian Y)
    (hflat : Flat g)
    (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (Z' : Y.IdealSheafData) (hZ' : Z' = Z.comap g)
    (B : List X.IdealSheafData) (E : List Y.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap g) B) E)
    (j : ℕ) (hj : j < B.length) (hjE : j < E.length)
    (htake : List.take (j + 1) E = List.take (j + 1) (List.map (fun D => D.comap g) B)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (E.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 Y) Z') (List.map (fun D => D.comap (𝟙 Y)) E)
          ++ [Blowup.exceptionalIdeal (𝟙 Y) Z']).eraseIdx j))
      (List.map (fun D => D.comap g)
        (List.take (B.length - 1)
          ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) B)
            ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx j))) := by
  have := hX
  have := hY
  have := hflat
  subst hZ'
  have hst : ∀ D : X.IdealSheafData,
      (Blowup.strictTransform (𝟙 X) Z D).comap g
        = Blowup.strictTransform (𝟙 Y) (Z.comap g) (D.comap g) := fun D =>
    comap_strictTransform_of_flat_of_isLocallyNoetherian (𝟙 X) g (𝟙 Y) g
      (CategoryTheory.IsPullback.id_vert g) Z D hZ
  have hcomp : List.map ((fun D : X.IdealSheafData => D.comap g)
        ∘ Blowup.strictTransform (𝟙 X) Z) B
      = List.map (Blowup.strictTransform (𝟙 Y) (Z.comap g))
          (List.map (fun D : X.IdealSheafData => D.comap g) B) := by
    rw [List.map_map]
    exact List.map_congr_left (fun D _ => hst D)
  rw [map_comap_id_consolidated421, map_comap_id_consolidated421,
    take_eraseIdx_append_singleton_consolidated421 (List.map (Blowup.strictTransform (𝟙 Y) (Z.comap g)) E)
      (Blowup.exceptionalIdeal (𝟙 Y) (Z.comap g)) j (E.length - 1) (by simpa using hjE) (by simp),
    take_eraseIdx_append_singleton_consolidated421 (List.map (Blowup.strictTransform (𝟙 X) Z) B)
      (Blowup.exceptionalIdeal (𝟙 X) Z) j (B.length - 1) (by simpa using hj) (by simp),
    ← List.eraseIdx_map, List.map_map, hcomp]
  refine ((MarkedIdealWithBoundary.SameNontrivialBoundary.map (Blowup.strictTransform (𝟙 Y) (Z.comap g))
    (strictTransform_top (𝟙 Y) (Z.comap g)) hBE).eraseIdx j ?_).symm
  rw [← List.map_take, ← List.map_take, ← List.map_take, htake, List.map_take]


end

theorem lowerIdealAfterBlowup_pullbackAlong_of_smooth
    (htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj)) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [Smooth h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
            List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
            ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
            T.IsOrderBoundedByMult →
            containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = (containedComponentsIdeal T j hj).comap h →
              lowerIdealAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE =
                (lowerIdealAfterBlowup T j hj).comap h := by
  intro T hV Y q h hsm hq E' hBE j hj hjE htake hV' hO hpre
  have hOx : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞) :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).1 hO
  have hex : ∃ B : T.scheme.IdealSheafData, containedComponentsIdeal T j hj ^ T.mult * B = T.ideal := by
    obtain ⟨B, hB⟩ := htwist T hV hOx j hj
    exact ⟨B, by rw [mul_comm]; exact hB⟩
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE) := by
    have hb := hblow ((T.pullbackAlong Y q h).withBoundary E') hV' j hjE
    have hc := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hb
    rwa [Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id] at hc
  have key := residualByPow_comap_of_isLocallyGeneratedByNonZeroDivisor_consolidated421 h T.ideal (containedComponentsIdeal T j hj)
      (containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE) T.mult hpre hcart hex
  simp only [lowerIdealAfterBlowup, Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id]
  exact key

theorem lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_smooth
    (_htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj)) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [Smooth h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
            List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
            ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
            T.IsOrderBoundedByMult →
            containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = (containedComponentsIdeal T j hj).comap h →
              MarkedIdealWithBoundary.SameNontrivialBoundary
                (List.take (E'.length - 1)
                  ((lowerBoundaryAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE).eraseIdx j))
                (List.map (fun D => D.comap h)
                  (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j))) := by
  intro T hV Y q h hsm hq E' hBE j hj hjE htake hV' hO hpre
  have hsmooth : Smooth h := hsm
  have hbdry : (T.pullbackAlong Y q h).boundary
      = List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary :=
    MarkedIdealWithBoundary.pullbackAlong_boundary T Y q h
  rw [hbdry] at hBE htake
  exact sameNontrivialBoundary_eraseIdx_strictTransform_comap_of_flat_consolidated421 h hV.isNoetherian hV'.isNoetherian inferInstance
    (containedComponentsIdeal T j hj) (hblow T hV j hj)
    (containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE) hpre
    T.boundary E' hBE j hj hjE htake

theorem comap_lowerIdealAfterBlowup_eq_comap_lowerIdealWithoutBlowup
    (htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (_hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (j : ℕ) (hj : j < T.boundary.length) (Y : Scheme.{u}) (h : Y ⟶ T.scheme)
    (htop : (containedComponentsIdeal T j hj).comap h = ⊤) :
    (lowerIdealAfterBlowup T j hj).comap h = (lowerIdealWithoutBlowup T).comap h := by
  have hex : ∃ B : T.scheme.IdealSheafData, containedComponentsIdeal T j hj ^ T.mult * B = T.ideal := by
    obtain ⟨B, hB⟩ := htwist T hV hO j hj
    exact ⟨B, by rw [mul_comm]; exact hB⟩
  have hdown : containedComponentsIdeal T j hj ^ T.mult * residualByPow T.ideal (containedComponentsIdeal T j hj) T.mult = T.ideal :=
    pow_mul_residualByPow T.ideal (containedComponentsIdeal T j hj) T.mult hex
  have hup := congrArg (fun I : T.scheme.IdealSheafData => I.comap h) hdown
  simp only [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow, htop,
    top_pow_consolidated421, Scheme.IdealSheafData.top_mul] at hup
  simp only [lowerIdealAfterBlowup, lowerIdealWithoutBlowup, Blowup.exceptionalIdeal_eq_comap,
    Scheme.IdealSheafData.comap_id]
  exact hup

theorem comap_lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_eq_top
    (_htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (_hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) (Y : Scheme.{u}) (h : Y ⟶ T.scheme)
    (htop : (containedComponentsIdeal T j hj).comap h = ⊤) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.map (fun D => D.comap h)
        (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j)))
      (List.map (fun D => D.comap h)
        (List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j))) := by
  have hnoT : IsNoetherian T.scheme := hV.isNoetherian
  have hstT : ∀ D : T.scheme.IdealSheafData,
      (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj) D).comap h = D.comap h := by
    intro D
    have hg : ((containedComponentsIdeal T j hj).comap (𝟙 T.scheme)).comap h = ⊤ := by
      rw [Scheme.IdealSheafData.comap_id]; exact htop
    have h2 := strictTransform_comap_of_comap_center_eq_top (𝟙 T.scheme) (containedComponentsIdeal T j hj) D h hg
    rw [h2, Scheme.IdealSheafData.comap_id]
  have hR0 : lowerBoundaryAfterBlowup T j hj
      = List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj))
          (List.map (fun D : T.scheme.IdealSheafData => D.comap (𝟙 T.scheme)) T.boundary)
        ++ [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)] := rfl
  have hR : lowerBoundaryAfterBlowup T j hj
      = List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.boundary
        ++ [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)] := by
    rw [hR0, map_comap_id_consolidated421]
  have key : List.map (fun D : T.scheme.IdealSheafData => D.comap h)
        ((List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.boundary).eraseIdx j)
      = List.map (fun D : T.scheme.IdealSheafData => D.comap h) (T.boundary.eraseIdx j) := by
    rw [← List.eraseIdx_map, ← List.eraseIdx_map, List.map_map]
    congr 1
    exact List.map_congr_left (fun D _ => hstT D)
  rw [hR, lowerBoundaryWithoutBlowup_eq T,
    take_eraseIdx_append_singleton_consolidated421
      (List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.boundary)
      (Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)) j (T.boundary.length - 1)
      (by simpa using hj) (by simp),
    take_length_sub_one_eraseIdx_consolidated421 T.boundary j (T.boundary.length - 1) hj rfl, key]
  exact MonomialCenter.sameNontrivialBoundary_refl _

theorem lowerIdealAfterBlowup_fieldBaseChange
    (htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (j : ℕ) (hj : j < T.boundary.length) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (_hBE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.baseChange K f).boundary)
    (hjE : j < E'.length)
    (_htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hpre : containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
      (containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f)) :
    lowerIdealAfterBlowup ((T.baseChange K f).withBoundary E') j hjE =
      (lowerIdealAfterBlowup T j hj).comap (fieldBaseChangeProjection T K f) := by
  have hex : ∃ B : T.scheme.IdealSheafData, containedComponentsIdeal T j hj ^ T.mult * B = T.ideal := by
    obtain ⟨B, hB⟩ := htwist T hV hO j hj
    exact ⟨B, by rw [mul_comm]; exact hB⟩
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE) := by
    have hb := hblow ((T.baseChange K f).withBoundary E') hV' j hjE
    have hc := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hb
    rwa [Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id] at hc
  have key := residualByPow_comap_of_isLocallyGeneratedByNonZeroDivisor_consolidated421 (fieldBaseChangeProjection T K f) T.ideal
      (containedComponentsIdeal T j hj)
      (containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE) T.mult hpre hcart hex
  simp only [lowerIdealAfterBlowup, Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id]
  exact key

theorem lowerBoundaryAfterBlowup_fieldBaseChange
    (_htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (_hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (j : ℕ) (hj : j < T.boundary.length) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.baseChange K f).boundary)
    (hjE : j < E'.length)
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hpre : containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
      (containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (E'.length - 1)
        ((lowerBoundaryAfterBlowup ((T.baseChange K f).withBoundary E') j hjE).eraseIdx j))
      (List.map (fun D => D.comap (fieldBaseChangeProjection T K f))
        (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j))) := by
  have hbdry : (T.baseChange K f).boundary
      = List.map (fun D : T.scheme.IdealSheafData => D.comap (fieldBaseChangeProjection T K f))
          T.boundary := MarkedIdealWithBoundary.baseChange_boundary T K f
  rw [hbdry] at hBE htake
  exact sameNontrivialBoundary_eraseIdx_strictTransform_comap_of_flat_consolidated421 (fieldBaseChangeProjection T K f) hV.isNoetherian
    hV'.isNoetherian inferInstance
    (containedComponentsIdeal T j hj) (hblow T hV j hj)
    (containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE) hpre
    T.boundary E' hBE.symm j hj hjE htake

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.NontrivialBoundaryReindexing
section


section
namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem filter_map_eq_of_filter_eq_consolidated431 {α : Type*} (p : α → Bool) (g : α → α)
    (hpg : ∀ a, p a = false → p (g a) = false) {A B : List α}
    (hAB : List.filter p A = List.filter p B) :
    List.filter p (A.map g) = List.filter p (B.map g) := by
  have key : ∀ L : List α,
      List.filter p (L.map g) = List.filter p ((List.filter p L).map g) := by
    intro L
    induction L with
    | nil => rfl
    | cons a t ih =>
      by_cases ha : p a = true
      · simp [List.filter_cons, ha, ih]
      · have ha' : p a = false := by simpa using ha
        have hga : p (g a) = false := hpg a ha'
        simp [ha', hga, ih]
  rw [key A, key B, hAB]

section
variable {X : Scheme.{u}}

private theorem sameNontrivialBoundary_map_consolidated431 (g : X.IdealSheafData → X.IdealSheafData)
    (hg : g ⊤ = ⊤) {A B : List X.IdealSheafData} (h : MarkedIdealWithBoundary.SameNontrivialBoundary A B) :
    MarkedIdealWithBoundary.SameNontrivialBoundary (A.map g) (B.map g) := by
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff] at h ⊢
  unfold MarkedIdealWithBoundary.nontrivialPart at h ⊢
  refine filter_map_eq_of_filter_eq_consolidated431 _ g ?_ h
  intro a ha
  have ha' : a = ⊤ := by simpa using ha
  subst ha'
  simp [hg]

private theorem sameNontrivialBoundary_take_eraseIdx_strictTransform_consolidated431 (Z : X.IdealSheafData)
    (A B : List X.IdealSheafData) (a b : ℕ) (ha : a < A.length) (hb : b < B.length)
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary (A.eraseIdx a) (B.eraseIdx b)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (A.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) A)
          ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx a))
      (List.take (B.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) B)
          ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx b)) := by
  have hcomap : ∀ I : X.IdealSheafData, I.comap (𝟙 X) = I := by
    intro I
    simp
  have hgtop : (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X))) ⊤
      = (⊤ : X.IdealSheafData) := by
    show Blowup.strictTransform (𝟙 X) Z ((⊤ : X.IdealSheafData).comap (𝟙 X)) = ⊤
    rw [hcomap]
    have h1 := comap_le_strictTransform (𝟙 X) Z (⊤ : X.IdealSheafData)
    rw [hcomap] at h1
    exact le_antisymm le_top h1
  have key : ∀ (C : List X.IdealSheafData) (c : ℕ), c < C.length →
      List.take (C.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) C)
          ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx c)
        = List.map (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X)))
            (C.eraseIdx c) := by
    intro C c hc
    have hlen : (List.map (fun D : X.IdealSheafData =>
        Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X))) (C.eraseIdx c)).length = C.length - 1 := by
      rw [List.length_map]
      exact List.length_eraseIdx_of_lt hc
    have hmap : ∀ f : X.IdealSheafData → X.IdealSheafData, c < (C.map f).length := by
      intro f
      rw [List.length_map]
      exact hc
    simp only [List.map_map, Function.comp_def]
    rw [List.eraseIdx_append_of_lt_length (hmap _)]
    rw [List.eraseIdx_map, ← hlen, List.take_append_of_le_length (Nat.le_refl _),
      List.take_length]
  rw [key A a ha, key B b hb]
  exact sameNontrivialBoundary_map_consolidated431 (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X)))
    hgtop h


end

section
variable (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData) (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length) (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩)
include heq

theorem lowerIdealAfterBlowup_withBoundary_eq_of_get_eq :
    lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hj₂ = lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hj₁ := by
  unfold lowerIdealAfterBlowup
  rw [containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq]
  rfl

theorem sameNontrivialBoundary_lowerBoundaryAfterBlowup_of_get_eq (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (L₂.eraseIdx j₂) (L₁.eraseIdx j₁)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (L₂.length - 1) ((lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hj₂).eraseIdx j₂))
      (List.take (L₁.length - 1) ((lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hj₁).eraseIdx j₁)) := by
  unfold lowerBoundaryAfterBlowup
  rw [containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq]
  exact sameNontrivialBoundary_take_eraseIdx_strictTransform_consolidated431
    (containedComponentsIdeal (T.withBoundary L₂) j₂ hj₂) L₂ L₁ j₂ j₁ hj₂ hj₁ hBE


end

theorem boundaryReindexingInvariance : BoundaryReindexingInvariance.{u} :=
  ⟨smooth_id, surjective_id, lowerIdealAfterBlowup_withBoundary_eq_of_get_eq, sameNontrivialBoundary_lowerBoundaryAfterBlowup_of_get_eq⟩

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientEmbeddingCompatibility
section


section
namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem toMarkedSequence_projectionToBase_eq_consolidated484 {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (d : BlowupSequenceData X) (h : d.IsMarked p I m E) (n : ℕ) :
    ((d.toMarkedBlowupSequenceData p I m E h).toMarkedSequenceOfBlowups).projectionToBase n = d.projectionToBase n :=
  BlowupSequenceData.toSequenceOfBlowups_projectionToBase d n

private theorem embeddingIntoAmbientBlowupSequence_comp_projectionToBase_consolidated484 {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] [IsNoetherian X]
    (d : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i < d.length, ∀ W ∈ irreducibleComponents ↥(d.obj i), ¬W ⊆ ↑(d.center i).support)
    (n : ℕ) :
    embeddingIntoAmbientBlowupSequence ι d hres hno hcen n ≫ (ambientBlowupSequence ι d hres hno hcen).projectionToBase n =
      d.projectionToBase n ≫ ι := by
  induction n with
  | zero =>
    have hiso : (ambientBlowupSequence ι d hres hno hcen).isoZero.hom = 𝟙 X :=
      congrArg (fun e => Iso.hom e) (ambientBlowupSequence_isoObjZero ι d hres hno hcen)
    rw [BlowupSequenceData.projectionToBase_zero, BlowupSequenceData.projectionToBase_zero, embeddingIntoAmbientBlowupSequence_zero, hiso]
    exact Category.comp_id _
  | succ m ih =>
    rw [BlowupSequenceData.projectionToBase_succ, BlowupSequenceData.projectionToBase_succ, ← Category.assoc,
      embeddingIntoAmbientBlowupSequence_succ_comp_map ι d hres hno hcen m, Category.assoc, ih, ← Category.assoc]

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)

theorem embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
      (MarkedBlowupSequenceData.ofMarkedSequence s).proj t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι := by
  have h := embeddingIntoAmbientBlowupSequence_comp_projectionToBase_consolidated484 (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t
  rw [MarkedBlowupSequenceData.projectionToBase_eq_toBlowupSequenceData_projectionToBase (MarkedBlowupSequenceData.ofMarkedSequence s) t]
  exact h

theorem projectionToSpec_eq_comp_ambientMarkedSeq (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    MarkedSequenceOfBlowups.projectionToSpec s t =
      embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t ≫
        MarkedSequenceOfBlowups.projectionToSpec (pushedMarkedSeq hres hno T j hj s hpr hmk) t := by
  have h6 := embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres hno T j hj
    (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t
  rw [MarkedBlowupSequenceData.ofMarkedSequence_projectionToBase] at h6
  have hB : (pushedMarkedSeq hres hno T j hj s hpr hmk).projectionToBase t =
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t :=
    toMarkedSequence_projectionToBase_eq_consolidated484 _ hmk t
  have hstruct : MarkedSequenceOfBlowups.projectionToSpec (pushedMarkedSeq hres hno T j hj s hpr hmk) t =
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t ≫ T.structMap := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact congrArg (fun f => f ≫ T.structMap) hB
  have e1 : embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t ≫
        ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t ≫ T.structMap)
      = (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t) ≫
            T.structMap := (Category.assoc _ _ _).symm
  have e2 : (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t) ≫ T.structMap
      = (s.projectionToBase t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap :=
    congrArg (fun f => f ≫ T.structMap) h6
  have e3 : (s.projectionToBase t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap
      = s.projectionToBase t ≫ ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    Category.assoc _ _ _
  rw [hstruct, MarkedSequenceOfBlowups.projectionToSpec_eq]
  exact ((e1.trans e2).trans e3).symm

theorem projectionToSpec_eq_comp_prependedAmbientSeq (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    MarkedSequenceOfBlowups.projectionToSpec s t =
      embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
        MarkedSequenceOfBlowups.projectionToSpec (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) (t + 1) := by
  have h6 := embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres hno T j hj
    (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t
  rw [MarkedBlowupSequenceData.ofMarkedSequence_projectionToBase] at h6
  have hA : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToBase (t + 1) =
      (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hpr)).projectionToBase (t + 1) :=
    toMarkedSequence_projectionToBase_eq_consolidated484 _ hmk (t + 1)
  have hB : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToBase (t + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t :=
    hA.trans (BlowupSequenceData.projectionToBase_prepend_succ (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr) t)
  have hstruct : MarkedSequenceOfBlowups.projectionToSpec (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) (t + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t ≫
        T.structMap := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact congrArg (fun f => f ≫ T.structMap) hB
  have e1 : embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
        ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t ≫
          T.structMap)
      = (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t) ≫
            T.structMap := (Category.assoc _ _ _).symm
  have e2 : (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t) ≫
            T.structMap
      = (s.projectionToBase t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap :=
    congrArg (fun f => f ≫ T.structMap) h6
  have e3 : (s.projectionToBase t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap
      = s.projectionToBase t ≫ ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    Category.assoc _ _ _
  rw [hstruct, MarkedSequenceOfBlowups.projectionToSpec_eq]
  exact ((e1.trans e2).trans e3).symm


end

private def unionSupportsExcept_consolidated484 {Y : Scheme.{u}} (L : List Y.IdealSheafData) (j : ℕ) : Set ↥Y :=
  ⋃ i : Fin L.length, ⋃ (_ : (i : ℕ) ≠ j), ((L.get i).support : Set ↥Y)

section
variable {Y : Scheme.{u}} (L : List Y.IdealSheafData)

private theorem support_subset_otherLocusOfList_consolidated484 (j i : ℕ)
    (hi : i < L.length) (hij : i ≠ j) :
    ((L[i].support : Set ↥Y)) ⊆ unionSupportsExcept_consolidated484 L j := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, Set.mem_iUnion.2 ⟨hij, hx⟩⟩

private theorem exists_mem_support_of_mem_otherLocusOfList_consolidated484 (j : ℕ)
    {x : ↥Y} (hx : x ∈ unionSupportsExcept_consolidated484 L j) :
    ∃ i : ℕ, ∃ h : i < L.length, i ≠ j ∧ x ∈ ((L[i].support : Set ↥Y)) := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  obtain ⟨h1, h2⟩ := Set.mem_iUnion.1 hi
  exact ⟨i.1, i.2, h1, h2⟩


end

private theorem isClosed_iUnion_prop_consolidated484 {α : Type u} [TopologicalSpace α] {p : Prop} {A : Set α}
    (h : IsClosed A) : IsClosed (⋃ _ : p, A) :=
  isClosed_iUnion_of_finite fun _ => h

private theorem isClosed_otherLocusOfList_consolidated484 {Y : Scheme.{u}} (L : List Y.IdealSheafData) (j : ℕ) :
    IsClosed (unionSupportsExcept_consolidated484 L j) := by
  refine isClosed_iUnion_of_finite ?_
  intro i
  exact isClosed_iUnion_prop_consolidated484 ((L.get i).support).2

private theorem apply_eq_apply_of_comp_eq_consolidated484 {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (f' : A ⟶ D) (g' : D ⟶ C) (e : f ≫ g = f' ≫ g') (x : ↥A) : ⇑g (⇑f x) = ⇑g' (⇑f' x) :=
  congrArg (fun m : A ⟶ C => ⇑m x) e

section
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

private theorem mem_boundaryLocus_iff_consolidated484 (s : MarkedSequenceOfBlowups p I m E) (t : ℕ) (x : ↥(s.schemeAt t)) :
    x ∈ MarkedSequenceOfBlowups.boundaryLocus s t ↔
      ∃ D ∈ s.boundary t, x ∈ ((D.support : Set ↥(s.schemeAt t))) := by
  constructor
  · intro hx
    unfold MarkedSequenceOfBlowups.boundaryLocus at hx
    obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨D, hD, hxD⟩
  · rintro ⟨D, hD, hxD⟩
    unfold MarkedSequenceOfBlowups.boundaryLocus
    exact Set.mem_iUnion₂.2 ⟨D, hD, hxD⟩

private theorem otherBoundaryLocus_eq_otherLocusOfList_consolidated484 (S : MarkedSequenceOfBlowups p I m E) (j t : ℕ) :
    MarkedSequenceOfBlowups.otherBoundaryLocus S j t = unionSupportsExcept_consolidated484 (S.boundary t) j := rfl


end

section
variable {Y : Scheme.{u}}

private theorem support_subset_otherLocusOfList_append_left_consolidated484 (L M : List Y.IdealSheafData)
    (j i : ℕ) (hi : i < L.length) (hij : i ≠ j) :
    ((L[i].support : Set ↥Y)) ⊆ unionSupportsExcept_consolidated484 (L ++ M) j := by
  have h1 : i < (L ++ M).length := by
    rw [List.length_append]
    omega
  have h2 := support_subset_otherLocusOfList_consolidated484 (L ++ M) j i h1 hij
  rwa [List.getElem_append_left hi] at h2

private theorem support_subset_otherLocusOfList_append_singleton_consolidated484 (L : List Y.IdealSheafData)
    (e : Y.IdealSheafData) (j : ℕ) (hj : j < L.length) :
    ((e.support : Set ↥Y)) ⊆ unionSupportsExcept_consolidated484 (L ++ [e]) j := by
  have h1 : L.length < (L ++ [e]).length := by
    rw [List.length_append]
    simp
  have h2 := support_subset_otherLocusOfList_consolidated484 (L ++ [e]) j L.length h1 (by omega)
  have h3 : (L ++ [e])[L.length]'h1 = e := by simp
  rwa [h3] at h2


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups) (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)

private theorem embeddingIntoAmbient_zero_comp_isoObjZero_hom_consolidated484 :
    embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0 ≫
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom =
      s.isoZero.hom ≫ (T.boundary.get ⟨j, hj⟩).subschemeι := by
  have h := embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres hno T j hj I₀ E₀ s hpr 0
  rw [MarkedBlowupSequenceData.ofMarkedSequence_projectionToBase, MarkedSequenceOfBlowups.projectionToBase_zero,
    BlowupSequenceData.projectionToBase_zero] at h
  exact h

private theorem comap_embeddingIntoAmbient_center_ambientBlowupSeq_consolidated484 (t : ℕ) :
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.center t := by
  have := instIsClosedImmersionPushedEmb hres hno T j hj I₀ E₀ s hpr t
  rw [ambientBlowupSeq_center_eq_imageIdealSheaf]
  exact Blowup.comap_schemeImageIdeal (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)

private theorem preimage_support_center_ambientBlowupSeq_consolidated484 (t : ℕ) :
    ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ⁻¹'
        ((((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).support : Set _)) =
      (((s.center t).support : Set ↥(s.schemeAt t))) := by
  ext x
  have h : x ∈ (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)).support ↔
      ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) x ∈
        ((((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).support) : Set _) :=
    Scheme.IdealSheafData.mem_support_comap ..
  rw [comap_embeddingIntoAmbient_center_ambientBlowupSeq_consolidated484] at h
  exact h.symm


end

section
variable (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)

private theorem isNoetherian_boundary_subscheme_consolidated484 :
    IsNoetherian (T.boundary.get ⟨j, hj⟩).subscheme := by
  have : LocallyOfFiniteType (T.boundary.get ⟨j, hj⟩).subschemeι :=
    inferInstance
  have : QuasiCompact (T.boundary.get ⟨j, hj⟩).subschemeι := inferInstance
  exact isNoetherian_of_locallyOfFiniteType (T.boundary.get ⟨j, hj⟩).subschemeι

private theorem isNoetherian_schemeAt_restrictToBoundaryDivisor_consolidated484 (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.length) :
    IsNoetherian (s.schemeAt i) :=
  @isNoetherian_schemeAt _ s.toSequenceOfBlowups (isNoetherian_boundary_subscheme_consolidated484 T j hj) i hi


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)

private theorem boundaryLocus_subset_preimage_otherLocus_consolidated484 (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hjE : j < E₀.length) :
    ∀ t, t ≤ s.length →
      MarkedSequenceOfBlowups.boundaryLocus s t ⊆
        ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ⁻¹'
          unionSupportsExcept_consolidated484 ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) j := by
  intro t
  induction t with
  | zero =>
      intro _ x hx
      obtain ⟨D, hD, hxD⟩ := (mem_boundaryLocus_iff_consolidated484 s 0 x).1 hx
      rw [MarkedSequenceOfBlowups.boundary_zero] at hD
      obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD
      have hD₀' : D₀ ∈ List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (List.take (T.boundary.length - 1) (E₀.eraseIdx j)) := hD₀
      obtain ⟨D₁, hD₁, rfl⟩ := List.mem_map.1 hD₀'
      have hD₁' : D₁ ∈ E₀.eraseIdx j := List.mem_of_mem_take hD₁
      obtain ⟨i, hi, hij, hget⟩ := List.mem_eraseIdx_iff_getElem.1 hD₁'
      subst hget
      have hlen0 : i < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0).length := by
        rw [BlowupSequenceData.boundary_length]
        omega
      have hentry0 : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0)[i]'hlen0
          = (E₀[i]'hi).comap (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom := by
        simp [BlowupSequenceData.boundary_zero]
      have hmem0 : x ∈ ((((E₀[i]'hi).comap (T.boundary.get ⟨j, hj⟩).subschemeι).comap
          s.isoZero.hom).support : Set _) := hxD
      have hmem1 := Scheme.IdealSheafData.mem_support_comap.mp hmem0
      have hmem2 := Scheme.IdealSheafData.mem_support_comap.mp hmem1
      have hkey := apply_eq_apply_of_comp_eq_consolidated484 (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0)
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom s.isoZero.hom
        (T.boundary.get ⟨j, hj⟩).subschemeι
        (embeddingIntoAmbient_zero_comp_isoObjZero_hom_consolidated484 hres hno T j hj I₀ E₀ s hpr) x
      have hmem3 : ⇑(ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom
          (⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0) x) ∈ (E₀[i]'hi).support := by
        rw [hkey]
        exact hmem2
      show ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0) x ∈
        unionSupportsExcept_consolidated484 ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0) j
      refine support_subset_otherLocusOfList_consolidated484 _ j i hlen0 hij ?_
      rw [hentry0]
      exact Scheme.IdealSheafData.mem_support_comap.mpr hmem3
  | succ n ih =>
      intro ht x hx
      have hn : n < s.length := ht
      have ihn := ih (Nat.le_of_lt hn)
      have : IsNoetherian (s.schemeAt (n + 1)) :=
        isNoetherian_schemeAt_restrictToBoundaryDivisor_consolidated484 T j hj I₀ E₀ s (n + 1) hn
      have : IsNoetherian
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (n + 1)) :=
        isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr (n + 1) hn
      have hmapeq : ∀ y : ↥(s.schemeAt (n + 1)),
          ⇑((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
              (⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) y)
            = ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) (⇑(s.transitionMapSucc n) y) := by
        intro y
        exact apply_eq_apply_of_comp_eq_consolidated484 _ _ _ _
          (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr n) y
      have hcenter := preimage_support_center_ambientBlowupSeq_consolidated484 hres hno T j hj I₀ E₀ s hpr n
      obtain ⟨D, hD, hxD⟩ := (mem_boundaryLocus_iff_consolidated484 s (n + 1) x).1 hx
      rw [MarkedSequenceOfBlowups.boundary_succ s n hn] at hD
      rcases List.mem_append.1 hD with hD' | hD'
      · obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD'
        have hCclosed : IsClosed (⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) ⁻¹'
            unionSupportsExcept_consolidated484 ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (n + 1)) j) :=
          (isClosed_otherLocusOfList_consolidated484 _ _).preimage
            (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)).continuous
        rw [support_strictTransform_eq_closure_sdiff (s.transitionMapSucc n) (s.center n) D₀] at hxD
        refine hCclosed.closure_subset_iff.2 ?_ hxD
        intro y hy
        have hy1 : ⇑(s.transitionMapSucc n) y ∈ (D₀.support : Set _) :=
          (Scheme.IdealSheafData.mem_support_comap ..).1 hy.1
        have hy2 : ⇑(s.transitionMapSucc n) y ∉ (((s.center n).support) : Set _) := fun hcon =>
          hy.2 ((Scheme.IdealSheafData.mem_support_comap ..).2 hcon)
        have hIH0 := ihn ((mem_boundaryLocus_iff_consolidated484 s n _).2 ⟨D₀, hD₀, hy1⟩)
        have hIH : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) (⇑(s.transitionMapSucc n) y)
            ∈ unionSupportsExcept_consolidated484 ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n) j := hIH0
        obtain ⟨i, hi, hij, hmem⟩ :=
          exists_mem_support_of_mem_otherLocusOfList_consolidated484 ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n) j hIH
        have hnotZ : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) (⇑(s.transitionMapSucc n) y)
            ∉ ((((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n).support : Set _)) := by
          intro hcon
          exact hy2 ((Set.ext_iff.1 hcenter (⇑(s.transitionMapSucc n) y)).1 hcon)
        have hstep : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) y ∈
            ((Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
                ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)
                (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)[i]'hi)).support : Set _) := by
          rw [support_strictTransform_eq_closure_sdiff]
          refine subset_closure ?_
          refine ⟨?_, ?_⟩
          · refine (Scheme.IdealSheafData.mem_support_comap ..).2 ?_
            rw [hmapeq y]
            exact hmem
          · intro hcon
            have hcon' := (Scheme.IdealSheafData.mem_support_comap ..).1 hcon
            rw [hmapeq y] at hcon'
            exact hnotZ hcon'
        have hlen : i < (List.map
            (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n))
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)).length := by
          rw [List.length_map]
          exact hi
        have hentry : (List.map
              (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
                ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n))
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n))[i]'hlen
            = Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
                ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)
                (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)[i]'hi) := by
          simp
        have hfin := support_subset_otherLocusOfList_append_left_consolidated484
          (List.map (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n))
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n))
          [Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)] j i hlen hij
        rw [hentry] at hfin
        show ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) y ∈
          unionSupportsExcept_consolidated484 ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (n + 1)) j
        rw [BlowupSequenceData.boundary_succ]
        exact hfin hstep
      · have hDe : D = Blowup.exceptionalIdeal (s.transitionMapSucc n) (s.center n) := by
          simpa using hD'
        subst hDe
        rw [Blowup.exceptionalIdeal_eq_comap] at hxD
        have hxD' : ⇑(s.transitionMapSucc n) x ∈ (((s.center n).support) : Set _) :=
          (Scheme.IdealSheafData.mem_support_comap ..).1 hxD
        have hjlen : j < (List.map
            (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n))
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)).length := by
          rw [List.length_map, BlowupSequenceData.boundary_length]
          omega
        have hmem : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) x ∈
            ((Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)).support : Set _) := by
          rw [Blowup.exceptionalIdeal_eq_comap]
          refine (Scheme.IdealSheafData.mem_support_comap ..).2 ?_
          rw [hmapeq x]
          exact (Set.ext_iff.1 hcenter (⇑(s.transitionMapSucc n) x)).2 hxD'
        show ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) x ∈
          unionSupportsExcept_consolidated484 ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (n + 1)) j
        rw [BlowupSequenceData.boundary_succ]
        exact support_subset_otherLocusOfList_append_singleton_consolidated484 _ _ j hjlen hmem

private theorem ambientMarkedSeq_boundary_consolidated484 (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t =
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom T.boundary t :=
  BlowupSequenceData.toMarkedBlowupSequenceData_boundary _ _ _ _ _ hmk t

private theorem prependedAmbientSeq_boundary_consolidated484 (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary t =
      (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hpr)).boundaryFrom T.boundary t :=
  BlowupSequenceData.toMarkedBlowupSequenceData_boundary _ _ _ _ _ hmk t

private theorem prepend_boundary_succ_eq_consolidated484 (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hpr)).boundaryFrom T.boundary (t + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
        (lowerBoundaryAfterBlowup T j hj) s hpr).boundaryFrom (lowerBoundaryAfterBlowup T j hj) t := by
  induction t with
  | zero =>
      rw [boundary_prepend_ambientBlowupSeq_one, BlowupSequenceData.boundary_zero]
  | succ m ih =>
      rw [BlowupSequenceData.boundary_succ, ih, BlowupSequenceData.boundary_succ, BlowupSequenceData.prepend_blowupMorphism_succ,
        BlowupSequenceData.prepend_center_succ]
      rfl

theorem boundaryLocus_subset_preimage_otherBoundaryLocus (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) (ht : t < s.length) :
    MarkedSequenceOfBlowups.boundaryLocus s t ⊆
      ⇑(embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t) ⁻¹'
        MarkedSequenceOfBlowups.otherBoundaryLocus (pushedMarkedSeq hres hno T j hj s hpr hmk) j t := by
  have hlowerEq : lowerBoundaryWithoutBlowup T = T.boundary := by simp [lowerBoundaryWithoutBlowup_eq]
  have hjE : j < (lowerBoundaryWithoutBlowup T).length := by
    rw [hlowerEq]
    exact hj
  have hmain := boundaryLocus_subset_preimage_otherLocus_consolidated484 hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T)
    s hpr hjE t (le_of_lt ht)
  have h1 : (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t =
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom
        (lowerBoundaryWithoutBlowup T) t := by
    rw [ambientMarkedSeq_boundary_consolidated484]
    exact congrArg
      (fun E => (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom E t)
      hlowerEq.symm
  have hset : MarkedSequenceOfBlowups.otherBoundaryLocus (pushedMarkedSeq hres hno T j hj s hpr hmk) j t
      = unionSupportsExcept_consolidated484 ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom
          (lowerBoundaryWithoutBlowup T) t) j :=
    (otherBoundaryLocus_eq_otherLocusOfList_consolidated484 _ j t).trans (congrArg (fun L => unionSupportsExcept_consolidated484 L j) h1)
  rw [hset]
  exact hmain

theorem boundaryLocus_subset_preimage_otherBoundaryLocus_succ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) (ht : t < s.length) :
    MarkedSequenceOfBlowups.boundaryLocus s t ⊆
      ⇑(embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t) ⁻¹'
        MarkedSequenceOfBlowups.otherBoundaryLocus (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) j (t + 1) := by
  have hjE : j < (lowerBoundaryAfterBlowup T j hj).length := by
    show j < (List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj))
      (List.map (fun D => D.comap (𝟙 T.scheme)) T.boundary) ++
      [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)]).length
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  have hmain := boundaryLocus_subset_preimage_otherLocus_consolidated484 hres hno T j hj (lowerIdealAfterBlowup T j hj)
    (lowerBoundaryAfterBlowup T j hj) s hpr hjE t (le_of_lt ht)
  have h1 : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary (t + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).boundaryFrom
        (lowerBoundaryAfterBlowup T j hj) t := by
    rw [prependedAmbientSeq_boundary_consolidated484, prepend_boundary_succ_eq_consolidated484]
  have hset : MarkedSequenceOfBlowups.otherBoundaryLocus (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) j (t + 1)
      = unionSupportsExcept_consolidated484 ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
          s hpr).boundaryFrom (lowerBoundaryAfterBlowup T j hj) t) j :=
    (otherBoundaryLocus_eq_otherLocusOfList_consolidated484 _ j (t + 1)).trans (congrArg (fun L => unionSupportsExcept_consolidated484 L j) h1)
  rw [hset]
  exact hmain


end

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BalancedDivisorReduction
section


section
namespace FunctorialResolution.EmbeddedResolution

section
variable (T : MarkedIdealWithBoundary.{u})

private theorem lowerIdealWithoutBlowup_eq_ideal_consolidated483 :
    DivisorReduction.lowerIdealWithoutBlowup T = T.ideal := by
  show T.ideal.comap (CategoryTheory.CategoryStruct.id T.scheme) = T.ideal
  exact Scheme.IdealSheafData.comap_id _

private theorem orderAt_le_mult_of_isOrderBoundedByMult_consolidated483 (hOB : T.IsOrderBoundedByMult) :
    ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞) := hOB

private theorem isDerivBalanced_of_isBalanced_consolidated483 (hV : T.IsAdmissible)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) :
    ∀ [_inst : LocallyOfFiniteType T.structMap],
      IsDerivBalanced T.base T.structMap T.ideal T.mult := by
  intro _
  exact hbal


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})

private theorem goingUpInvariant_length_of_isBalanced_consolidated483 (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hbal : T.IsBalanced hV.locallyOfFiniteType)
    [IsNoetherian T.scheme]
    [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap]
    [CharZero T.base]
    (j : ℕ) (hj : j < T.boundary.length)
    (hVlow : (DivisorReduction.restrictToDivisor T j hj).IsAdmissible)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent) :
    DivisorReduction.GoingUpInvariant hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
      (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr s.length := by
  have hbalLower : IsDerivBalanced T.base T.structMap (DivisorReduction.lowerIdealWithoutBlowup T) T.mult := by
    rw [lowerIdealWithoutBlowup_eq_ideal_consolidated483]
    exact hbal
  have hE₀ : InStrictNormalCrossingPosition T.structMap (DivisorReduction.lowerBoundaryWithoutBlowup T) := by
    rw [DivisorReduction.lowerBoundaryWithoutBlowup_eq]
    exact hV.snc
  have hjE : j < (DivisorReduction.lowerBoundaryWithoutBlowup T).length := by
    rw [DivisorReduction.lowerBoundaryWithoutBlowup_eq]
    exact hj
  have hget : (DivisorReduction.lowerBoundaryWithoutBlowup T)[j]'hjE = T.boundary[j]'hj := by
    simp [DivisorReduction.lowerBoundaryWithoutBlowup_eq T]
  have hlen : ((DivisorReduction.lowerBoundaryWithoutBlowup T).eraseIdx j).length = T.boundary.length - 1 := by
    rw [DivisorReduction.lowerBoundaryWithoutBlowup_eq]
    simp [List.length_eraseIdx, hj]
  have htrunc : List.take (T.boundary.length - 1) ((DivisorReduction.lowerBoundaryWithoutBlowup T).eraseIdx j)
      = (DivisorReduction.lowerBoundaryWithoutBlowup T).eraseIdx j := by
    rw [← hlen, List.take_length]
  exact DivisorReduction.goingUpInvariant_of_le hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
    (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr hbalLower hV.one_le_mult hVlow hlift hE₀ hjE hget
    htrunc s.length le_rfl

theorem divisorReductionProperties_of_blowupPreservesNoetherian : DivisorReductionProperties hres hno := by
  have hlift : StrictNormalCrossingsLiftFromDivisor.{u} := hasStrictNormalCrossingsWith_ker_cons_of_comap
  exact
    { isMarked_pushedTop := by
        intro T hV hOB hbal j hj hZ hVlow inst s hpr
        have := inst
        exact DivisorReduction.isMarked_ambientBlowupSeq_of_containedComponentsIdeal_eq_top hres hno hlift T hV
          (orderAt_le_mult_of_isOrderBoundedByMult_consolidated483 T hOB) (isDerivBalanced_of_isBalanced_consolidated483 T hV hbal) j hj hZ hVlow s hpr
      isMarked_pushedPre := by
        intro T hV hOB hbal j hj hZ hb hVlow inst s hpr
        have := inst
        exact DivisorReduction.isMarked_prepend_ambientBlowupSeq hres hno hlift T hV
          (orderAt_le_mult_of_isOrderBoundedByMult_consolidated483 T hOB) (isDerivBalanced_of_isBalanced_consolidated483 T hV hbal) j hj hZ hb hVlow
          s hpr
          (smooth_subschemeι_containedComponentsIdeal_comp T hV j hj)
          (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj)
          (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
          (exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj)
          (DivisorReduction.isOpen_preimage_support_containedComponentsIdeal T j hj
            (DivisorReduction.preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj))
      valid_lowerPre := by
        intro T hV hOB hbal j hj hZ
        exact DivisorReduction.isAdmissible_restrictTwistedToDivisor T hV hOB hbal j hj hZ
      orderAt_ctrlIdeal_le_top := by
        intro T hV hOB hbal j hj hZ hVlow inst s hpr i hi x
        have := inst
        have := hV.charZero
        have := hV.smooth
        exact orderAt_controlledTransform_le_of_isMarked T.base T.structMap T.ideal T.mult T.boundary
          (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr)
          (DivisorReduction.isMarked_ambientBlowupSeq_of_containedComponentsIdeal_eq_top hres hno hlift T hV
            (orderAt_le_mult_of_isOrderBoundedByMult_consolidated483 T hOB) (isDerivBalanced_of_isBalanced_consolidated483 T hV hbal) j hj hZ hVlow
            s hpr)
          (orderAt_le_mult_of_isOrderBoundedByMult_consolidated483 T hOB) i
          (by rw [DivisorReduction.ambientBlowupSeq_length]; exact hi) x
      orderAt_ctrlIdeal_le_pre := by
        intro T hV hOB hbal j hj hZ hb hVlow inst s hpr i hi x
        have := inst
        have := hV.charZero
        have := hV.smooth
        exact orderAt_controlledTransform_le_of_isMarked T.base T.structMap T.ideal T.mult T.boundary
          (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
            (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr))
          (DivisorReduction.isMarked_prepend_ambientBlowupSeq hres hno hlift T hV
            (orderAt_le_mult_of_isOrderBoundedByMult_consolidated483 T hOB) (isDerivBalanced_of_isBalanced_consolidated483 T hV hbal) j hj hZ hb hVlow
            s hpr
            (smooth_subschemeι_containedComponentsIdeal_comp T hV j hj)
            (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj)
            (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
            (exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj)
            (DivisorReduction.isOpen_preimage_support_containedComponentsIdeal T j hj
              (DivisorReduction.preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj)))
          (orderAt_le_mult_of_isOrderBoundedByMult_consolidated483 T hOB) i
          (by rw [BlowupSequenceData.prepend_length, DivisorReduction.ambientBlowupSeq_length]; exact hi) x
      coSupport_inter_ker_eq_empty_top := by
        intro T hV hOB hbal j hj hZ hVlow inst s hpr hempty
        have := inst
        have := hV.charZero
        have := hV.smooth
        have := hV.locallyOfFiniteType
        have hgoingUp := goingUpInvariant_length_of_isBalanced_consolidated483 hres hno hlift T hV hbal j hj hVlow s hpr
        exact DivisorReduction.orderAtLeastLocus_inter_support_ker_eq_empty hres hno T j hj s hpr
          (fun i hi => hgoingUp.exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform i hi) hempty
      coSupport_inter_ker_eq_empty_pre := by
        intro T hV hOB hbal j hj hZ hb hVlow inst s hpr hempty
        have := inst
        have := hV.charZero
        have := hV.smooth
        have := hV.locallyOfFiniteType
        obtain ⟨U₀, hU, hsupp, hbalPre, hinv⟩ :=
          DivisorReduction.exists_isClosed_opens_goingUpInvariantOnOpen hres hno hlift T hV
            (orderAt_le_mult_of_isOrderBoundedByMult_consolidated483 T hOB) (isDerivBalanced_of_isBalanced_consolidated483 T hV hbal) j hj hZ hb hVlow
            s hpr
            (smooth_subschemeι_containedComponentsIdeal_comp T hV j hj)
            (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj)
            (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
            (exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj)
            (DivisorReduction.isOpen_preimage_support_containedComponentsIdeal T j hj
              (DivisorReduction.preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj))
        exact DivisorReduction.orderAtLeastLocus_controlledTransform_inter_ker_support_eq_empty hres hno T j hj hb s hpr
          (fun i hi => (hinv s.length le_rfl).exists_pow_mul_eq_comap_controlledTransform i hi)
          (DivisorReduction.controlledTransform_prepend_ambientBlowupSeq_one hres hno T j hj hb s hpr) hempty
      isPullbackSeq_ambientTower := by
        intro X Y S S' σ σ' φ ψ _ _ _ _ _ hsq d d' hc hc' hpb
        exact isPullbackBlowupSequence_ambientBlowupSequence_of_flat hres hno σ σ' φ ψ hsq d d' hc hc' hpb
      isStrictPullbackSeq_ambientTower := by
        intro X Y S S' σ σ' φ ψ _ _ _ _ _ hsq d d' hc hc' hpb
        exact isStrictPullbackBlowupSeq_ambientBlowupSequence_of_flat hres hno σ σ' φ ψ hsq d d' hc hc' hpb
      comap_ctrlIdeal_top := by
        intro T hV hOB hbal j hj hZ hVlow inst s hpr i hi
        have := inst
        exact DivisorReduction.comap_controlledTransform_of_containedComponentsIdeal_eq_top hres hno hlift T hV
          (orderAt_le_mult_of_isOrderBoundedByMult_consolidated483 T hOB) (isDerivBalanced_of_isBalanced_consolidated483 T hV hbal) j hj hZ hVlow
          s hpr i hi
      comap_ctrlIdeal_pre := by
        intro T hV hOB hbal j hj hZ hb hVlow inst s hpr i hi
        have := inst
        exact DivisorReduction.comap_controlledTransform_prepend_ambientBlowupSeq hres hno hlift T hV
          (orderAt_le_mult_of_isOrderBoundedByMult_consolidated483 T hOB) (isDerivBalanced_of_isBalanced_consolidated483 T hV hbal) j hj hZ hb hVlow
          s hpr
          (smooth_subschemeι_containedComponentsIdeal_comp T hV j hj)
          (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj)
          (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
          (exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj)
          (DivisorReduction.isOpen_preimage_support_containedComponentsIdeal T j hj
            (DivisorReduction.preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj))
          i hi
      preIdeal_baseChange := by
        intro T hV L _ _ f hV' j hj hj'
        exact containedComponentsIdeal_baseChange T hV L f hV' j hj hj'
      preIdeal_pullbackAlong := by
        intro T hV Y q h _ hq hV' j hj hj'
        exact containedComponentsIdeal_pullbackAlong_of_smooth T hV Y q h hq hV' j hj hj'
      preIdeal_eq_top_of_imageIdeal := by
        intro T hV j hj J hm hlow hpush
        exact DivisorReduction.containedComponentsIdeal_eq_top_of_eq_imageIdealSheaf T hV j hj J hm hlow hpush }


end

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.EmptyOrderLocus
section


section
namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReductionEmptyOrderLocus

private theorem blowupMorphism_mem_orderAtLeastLocus_consolidated485 {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedSequenceOfBlowups p I m E) (hm : 1 ≤ m)
    (hsm : ∀ i, i ≤ s.length → Smooth (MarkedSequenceOfBlowups.projectionToSpec s i))
    (hno : ∀ i, i ≤ s.length → IsNoetherian (s.schemeAt i))
    (i : ℕ) (hi : i < s.length) (z : s.schemeAt (i + 1))
    (hz : z ∈ orderAtLeastLocus (s.ideal (i + 1)) m) :
    (s.transitionMapSucc i) z ∈ orderAtLeastLocus (s.ideal i) m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
  have := hsm i hi.le
  have := hno (i + 1) hi
  have hsnc : HasStrictNormalCrossingsWith (MarkedSequenceOfBlowups.projectionToSpec s i) (s.center i) (s.boundary i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact s.center_snc i hi
  have hord : (↑(s.center i).support : Set (s.schemeAt i)) ⊆ orderAtLeastLocus (s.ideal i) n :=
    (s.center_order i hi).trans
      (orderAtLeastLocus_subset_of_le (s.ideal i) (Nat.le_succ n))
  have hI : s.ideal i ≤ s.center i ^ n :=
    le_pow_of_hasStrictNormalCrossingsWith (MarkedSequenceOfBlowups.projectionToSpec s i) (s.center i) (s.ideal i)
      (s.boundary i) hsnc n hord
  have hpb : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc i) (s.center i) := s.isBlowupAlongIdealSheaf_blowupMorphism i hi
  have key := orderAtLeastLocus_controlledTransform_subset_preimage k
      (MarkedSequenceOfBlowups.projectionToSpec s i) (s.transitionMapSucc i) (s.center i) (s.boundary i) hsnc hpb
      (s.ideal i) n hI
  have hmul : Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i) ^ n *
      (Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i) * s.ideal (i + 1))
      = (s.ideal i).comap (s.transitionMapSucc i) := by
    rw [← mul_assoc, ← pow_succ]
    exact s.ideal_succ i hi
  have heq := eq_controlledTransform_of_mul_eq_comap (s.transitionMapSucc i) (s.center i) (s.ideal i) n hpb hI
      (Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i) * s.ideal (i + 1)) hmul
  have hz' : z ∈ orderAtLeastLocus
      (Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i) * s.ideal (i + 1)) (n + 1) := by
    rw [mem_orderAtLeastLocus_iff] at hz ⊢
    exact hz.trans ((self_le_add_left _ _).trans
      (add_orderAt_le_orderAt_mul (Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i))
        (s.ideal (i + 1)) z))
  rw [heq] at hz'
  exact key hz'

private theorem projectionToBase_mem_orderAtLeastLocus_consolidated485 {T : MarkedIdealWithBoundary.{u}} (hV : T.IsAdmissible) (s : T.SequenceOfBlowups) :
    ∀ i, i ≤ s.length → ∀ z : s.schemeAt i,
      z ∈ orderAtLeastLocus (s.ideal i) T.mult → (s.projectionToBase i) z ∈ orderAtLeastLocus T.ideal T.mult := by
  have := hV.charZero
  intro i
  induction i with
  | zero =>
      intro _ z hz
      rw [markedSequenceOfBlowups_ideal_zero s, MarkedSequenceOfBlowups.projectionToBase_zero s, orderAtLeastLocus_comap_iso_hom_eq_preimage] at hz
      rw [MarkedSequenceOfBlowups.projectionToBase_zero s]
      exact hz
  | succ i ih =>
      intro hi z hz
      rw [MarkedSequenceOfBlowups.projectionToBase_succ_apply]
      refine ih (Nat.le_of_succ_le hi) _ ?_
      exact blowupMorphism_mem_orderAtLeastLocus_consolidated485 s hV.one_le_mult
        (fun j hj => MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hV s j hj)
        (fun j hj => MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s j hj)
        i (Nat.lt_of_succ_le hi) z hz

section
variable {T : MarkedIdealWithBoundary.{u}} (hV : T.IsAdmissible) {Y : Scheme.{u}} (h : Y ⟶ T.scheme)
include hV

theorem center_disjoint_range_of_preimage_orderAtLeastLocus_eq_empty
    (hempty : (⇑h ⁻¹' orderAtLeastLocus T.ideal T.mult) = ∅) (s : T.SequenceOfBlowups) :
    ∀ i < s.length, ∀ z : s.schemeAt i, z ∈ (s.center i).support →
      ∀ y : Y, h y ≠ (s.projectionToBase i) z := by
  intro i hi z hz y hy
  have hz' : z ∈ (↑((s.center i).support) : Set (s.schemeAt i)) := hz
  have hzc : z ∈ orderAtLeastLocus (s.ideal i) T.mult := s.center_order i hi hz'
  have himg := projectionToBase_mem_orderAtLeastLocus_consolidated485 hV s i hi.le z hzc
  rw [← hy] at himg
  have hmem : y ∈ (⇑h ⁻¹' orderAtLeastLocus T.ideal T.mult) := himg
  rw [hempty] at hmem
  simp at hmem

theorem isPullbackSequenceOfBlowups_of_preimage_orderAtLeastLocus_empty
    [Flat h]
    (hempty : (⇑h ⁻¹' orderAtLeastLocus T.ideal T.mult) = ∅) (s : T.SequenceOfBlowups)
    (B' : SequenceOfBlowups Y) (hB' : B'.length = 0) :
    IsPullbackBlowupSequence h B' s.toSequenceOfBlowups := by
  have hdisj := center_disjoint_range_of_preimage_orderAtLeastLocus_eq_empty hV h hempty s
  refine (SequenceOfBlowupsPullback.ofBlowupDataOfSeq
      (SequenceOfBlowupsPullback.ofCentersMissImage h (BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups) ?_
        (BlowupSequenceData.ofSequenceOfBlowups B') ?_)).isPullbackSequenceOfBlowups
  · intro i hi z hz y
    rw [BlowupSequenceData.ofSequenceOfBlowups_projectionToBase]
    exact hdisj i hi z hz y
  · exact hB'


end

theorem divisorFamily_isPullbackSequenceOfBlowups_of_orderAtLeastLocus_empty
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (L : PrincipalizationAssignment.{u}) (j : ℕ) (T : MarkedIdealWithBoundary.{u})
    (hV : T.IsAdmissible) (_hj : j < T.boundary.length)
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [Smooth h]
    (_hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
    (_hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible)
    (_hne : (orderAtLeastLocus T.ideal T.mult).Nonempty)
    (hempty : orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult = ∅)
    (B' : SequenceOfBlowups Y) (hB' : B'.length = 0) :
    IsPullbackBlowupSequence h B' ((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups := by
  have := hV.charZero
  have := hV.smooth
  have hsub : (⇑h ⁻¹' orderAtLeastLocus T.ideal T.mult) ⊆ ∅ := by
    intro y hy
    have hy' : y ∈ orderAtLeastLocus (T.ideal.comap h) T.mult := by
      rw [orderAtLeastLocus_comap T.base T.structMap h T.ideal T.mult]
      exact hy
    have hy2 : y ∈ orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult := hy'
    rw [hempty] at hy2
    exact hy2
  exact isPullbackSequenceOfBlowups_of_preimage_orderAtLeastLocus_empty hV h (Set.subset_empty_iff.mp hsub)
    ((canonicalAlgorithmRules hres).divisorFamily L j T) B' hB'

end DivisorReductionEmptyOrderLocus

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.RestrictedBaseChangeComparison
section


namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

section
variable {A B : Scheme.{u}} (g : A ⟶ B) [IsIso g]

private theorem smooth_of_isIso_consolidated492 :
    Smooth g := inferInstance

private theorem surjective_of_isIso_consolidated492 :
    AlgebraicGeometry.Surjective g := inferInstance


end

private theorem comap_congr_consolidated492 {X W : Scheme.{u}} {a b : W ⟶ X} (h : a = b)
    (I : X.IdealSheafData) : I.comap a = I.comap b := by
  subst h
  rfl

private theorem map_comap_map_comap_eq_map_comap_comp_consolidated492 {X Y W : Scheme.{u}} (a : W ⟶ Y) (b : Y ⟶ X)
    (M : List X.IdealSheafData) :
    List.map (fun D : Y.IdealSheafData => D.comap a)
        (List.map (fun D : X.IdealSheafData => D.comap b) M)
      = List.map (fun D : X.IdealSheafData => D.comap (a ≫ b)) M := by
  induction M with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [← Scheme.IdealSheafData.comap_comp, ih]

private theorem map_comap_congr_consolidated492 {X W : Scheme.{u}} {a b : W ⟶ X} (h : a = b)
    (M : List X.IdealSheafData) :
    List.map (fun D : X.IdealSheafData => D.comap a) M
      = List.map (fun D : X.IdealSheafData => D.comap b) M := by
  subst h
  rfl

private theorem sameNontrivialBoundary_of_eq_right_consolidated492 {X : Scheme.{u}} {A B B' : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary A B) (hB : B = B') : MarkedIdealWithBoundary.SameNontrivialBoundary A B' :=
  hB ▸ h

section
variable (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) (K : Type u) [Field K]

private theorem isPullback_subschemeMapOfComap_comp_structureMorphism_consolidated492 (f : T.base →+* K)
    (Z : (T.baseChange K f).scheme.IdealSheafData)
    (hZ : Z = (T.boundary.get ⟨j, hj⟩).comap (fieldBaseChangeProjection T K f)) :
    IsPullback (subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩) Z hZ)
      (Z.subschemeι ≫ (T.baseChange K f).structMap)
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
      (specMapOfFieldHom T.base K f) := by
  have h2 : IsPullback (fieldBaseChangeProjection T K f) ((T.baseChange K f).structMap) T.structMap
      (specMapOfFieldHom T.base K f) := IsPullback.of_hasPullback _ _
  exact (isPullback_subschemeMapOfComap _ _ (fieldBaseChangeProjection T K f)
    (T.boundary.get ⟨j, hj⟩) Z hZ).paste_vert h2

theorem exists_smooth_surjective_to_restrictToBoundaryDivisor_baseChange [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData) (hjE : j < E'.length)
    (hget : E'.get ⟨j, hjE⟩ = (T.boundary.get ⟨j, hj⟩).comap (fieldBaseChangeProjection T K f))
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (I₀' : (T.baseChange K f).scheme.IdealSheafData)
    (E₀' : List (T.baseChange K f).scheme.IdealSheafData)
    (hI₀' : I₀' = I₀.comap (fieldBaseChangeProjection T K f))
    (hE₀' : MarkedIdealWithBoundary.SameNontrivialBoundary (List.take (E'.length - 1) (E₀'.eraseIdx j))
      (List.map (fun D => D.comap (fieldBaseChangeProjection T K f))
        (List.take (T.boundary.length - 1) (E₀.eraseIdx j)))) :
    ∃ (E'' : List ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).scheme.IdealSheafData)
      (e : (E'.get ⟨j, hjE⟩).subscheme ⟶ ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).scheme),
      Smooth e ∧
      AlgebraicGeometry.Surjective e ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary E'' ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).boundary ∧
      e ≫ CategoryTheory.Limits.pullback.fst (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
            (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) =
          divisorPullbackMap T j hj I₀ E₀ (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
            (E'.get ⟨j, hjE⟩) hget ∧
      e ≫ (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').structMap =
          (E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary
        (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j)))
        (List.map (fun D => D.comap e) E'') ∧
      (((T.baseChange K f).withSchemeIdealBoundary (E'.get ⟨j, hjE⟩).subscheme
            ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap)
            (I₀'.comap (E'.get ⟨j, hjE⟩).subschemeι)
            (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
              (List.take (E'.length - 1) (E₀'.eraseIdx j)))).IsAdmissible →
          (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').IsAdmissible) ∧
      (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').krullDimSucc =
        ((T.baseChange K f).withSchemeIdealBoundary (E'.get ⟨j, hjE⟩).subscheme
            ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap)
            (I₀'.comap (E'.get ⟨j, hjE⟩).subschemeι)
            (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
              (List.take (E'.length - 1) (E₀'.eraseIdx j)))).krullDimSucc := by
  classical
  subst hI₀'
  have hsq : IsPullback
      (subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hget)
      ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap)
      (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
      (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) :=
    isPullback_subschemeMapOfComap_comp_structureMorphism_consolidated492 T j hj K f (E'.get ⟨j, hjE⟩) hget
  have hQ : IsPullback
      (CategoryTheory.Limits.pullback.fst (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
        (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f))
      (CategoryTheory.Limits.pullback.snd (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
        (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f))
      (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
      (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨ee, hfst, hsnd, hinv1, hinv2⟩ :
      ∃ ee : _ ≅ _,
        ee.hom ≫ CategoryTheory.Limits.pullback.fst (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
              (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) =
            subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩)
              (E'.get ⟨j, hjE⟩) hget ∧
          ee.hom ≫ CategoryTheory.Limits.pullback.snd (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
              (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) =
            (E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap ∧
          ee.inv ≫ subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩)
              (E'.get ⟨j, hjE⟩) hget =
            CategoryTheory.Limits.pullback.fst (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
              (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) ∧
          ee.inv ≫ ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) =
            CategoryTheory.Limits.pullback.snd (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
              (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) :=
    ⟨hsq.isoIsPullback _ _ hQ, hsq.isoIsPullback_hom_fst _ _ hQ,
      hsq.isoIsPullback_hom_snd _ _ hQ, hsq.isoIsPullback_inv_fst _ _ hQ,
      hsq.isoIsPullback_inv_snd _ _ hQ⟩
  have hlbc : divisorPullbackMap T j hj I₀ E₀ (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
        (E'.get ⟨j, hjE⟩) hget
      = subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩)
          (E'.get ⟨j, hjE⟩) hget := rfl
  have hbe := sameNontrivialBoundary_comap_subschemeι (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩)
      (E'.get ⟨j, hjE⟩) hget (List.take (T.boundary.length - 1) (E₀.eraseIdx j))
      (List.take (E'.length - 1) (E₀'.eraseIdx j)) hE₀'
  refine ⟨List.map (fun D : (E'.get ⟨j, hjE⟩).subscheme.IdealSheafData => D.comap ee.inv)
      (List.map (fun D : (T.baseChange K f).scheme.IdealSheafData =>
        D.comap (E'.get ⟨j, hjE⟩).subschemeι) (List.take (E'.length - 1) (E₀'.eraseIdx j))),
      ee.hom, ?_, ?_, ?_, hfst.trans hlbc.symm, hsnd, ?_, ?_,
      krullDimSucc_eq_of_iso ee.symm⟩
  · exact smooth_of_isIso_consolidated492 ee.hom
  · exact surjective_of_isIso_consolidated492 ee.hom
  · exact sameNontrivialBoundary_of_eq_right_consolidated492 (MarkedIdealWithBoundary.SameNontrivialBoundary.comap ee.inv hbe)
      (((map_comap_map_comap_eq_map_comap_comp_consolidated492 ee.inv (subschemeMapOfComap (fieldBaseChangeProjection T K f)
            (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hget) _).trans
          (map_comap_congr_consolidated492 hinv1 _)).trans
        (MarkedIdealWithBoundary.baseChange_boundary (restrictToBoundaryDivisor T j hj I₀ E₀) K f).symm)
  · exact sameNontrivialBoundary_of_eq_right_consolidated492 (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _)
      (((map_comap_map_comap_eq_map_comap_comp_consolidated492 ee.hom ee.inv _).trans
          (map_comap_congr_consolidated492 ee.hom_inv_id _)).trans (list_map_comap_id _ _)).symm
  · intro hS
    have hval := isAdmissible_comap_of_iso ee.symm
      ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap)
      ((I₀.comap (fieldBaseChangeProjection T K f)).comap (E'.get ⟨j, hjE⟩).subschemeι) T.mult
      (List.map (fun D : (T.baseChange K f).scheme.IdealSheafData =>
        D.comap (E'.get ⟨j, hjE⟩).subschemeι) (List.take (E'.length - 1) (E₀'.eraseIdx j))) hS
    have hp : ee.symm.hom ≫ ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap)
        = ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).structMap := hinv2
    have s1 : (I₀.comap (fieldBaseChangeProjection T K f)).comap (E'.get ⟨j, hjE⟩).subschemeι
        = (I₀.comap (T.boundary.get ⟨j, hj⟩).subschemeι).comap
            (subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩)
              (E'.get ⟨j, hjE⟩) hget) :=
      (comap_subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩)
        (E'.get ⟨j, hjE⟩) hget I₀).symm
    have hI : ((I₀.comap (fieldBaseChangeProjection T K f)).comap
          (E'.get ⟨j, hjE⟩).subschemeι).comap ee.symm.hom
        = ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).ideal :=
      (congrArg (fun J : (E'.get ⟨j, hjE⟩).subscheme.IdealSheafData => J.comap ee.symm.hom)
          s1).trans
        (((Scheme.IdealSheafData.comap_comp _ ee.symm.hom _).symm.trans
            (comap_congr_consolidated492 hinv1 _)).trans
          (MarkedIdealWithBoundary.baseChange_ideal (restrictToBoundaryDivisor T j hj I₀ E₀) K f).symm)
    exact isAdmissible_congr hp hI rfl rfl hval


end

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.CanonicalDivisorReduction
section


namespace FunctorialResolution.EmbeddedResolution

private theorem exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le_consolidated494 : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      ∃ B : T.scheme.IdealSheafData, B * DivisorReduction.containedComponentsIdeal T j hj ^ T.mult = T.ideal := by
  intro T hV _ j hj
  obtain ⟨J, hJ⟩ := exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj
  exact ⟨J, by rw [mul_comm]; exact hJ⟩

private theorem orderAtComapOffExceptionalLocus_consolidated494 : OrderAtComapOffExceptionalLocus.{u} := by
  delta OrderAtComapOffExceptionalLocus
  exact fun T hT X' π Z hπ x' hx' A =>
    orderAt_comap_eq_of_notMem_exceptionalIdeal T hT Z X' π hπ x' hx' A

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
include hfacts

private theorem smoothPullbackCompatibility_of_divisorReductionTermination_consolidated494 :
    DivisorReduction.SmoothPullbackCompatibility.{u} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact comap_ne_top_of_surjective
  · intro T hV Y q h inst hq m
    exact DivisorReduction.orderAtLeastLocus_comap_of_smooth T hV Y q h hq m
  · exact DivisorReduction.isPullback_subschemeMapOfComap
  · exact DivisorReduction.smooth_of_isPullback
  · exact DivisorReduction.lowerIdealAfterBlowup_pullbackAlong_of_smooth exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le_consolidated494 isBlowupAlongIdealSheaf_id_containedComponentsIdeal
  · exact DivisorReduction.lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_smooth exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le_consolidated494
      isBlowupAlongIdealSheaf_id_containedComponentsIdeal
  · exact DivisorReduction.containedComponentsIdeal_pullbackAlong_of_smooth hfacts

private theorem fieldBaseChangeCompatibility_of_divisorReductionTermination_consolidated494 :
    FieldBaseChangeCompatibility.{u} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T hV K inst f E' m
    exact orderAtLeastLocus_withBoundary_baseChange_eq_preimage T hV K f E' m
  · exact flat_fieldBaseChangeProjection
  · exact surjective_fieldBaseChangeProjection
  · exact containedComponentsIdeal_withBoundary_baseChange hfacts MarkedIdealWithBoundary.validOfSameNontrivialBoundary


end

private theorem divisorRestrictionFieldBaseChange_consolidated494 : DivisorReduction.DivisorRestrictionFieldBaseChange.{u} := by
  refine ⟨comap_comap, comap_fieldBaseChangeProjection_ne_top, ?_, ?_, ?_, ?_, ?_⟩
  · intro T j hj K inst1 inst2 f E' hjE hD I₀ E₀ I₀' E₀' hI hE
    obtain ⟨E'', e, hs, hsu, h1, h2, h3, h4, h5, h6⟩ :=
      DivisorReduction.exists_smooth_surjective_to_restrictToBoundaryDivisor_baseChange T j hj K f E' hjE hD I₀ E₀ I₀' E₀' hI hE
    exact ⟨E'', e, hs, hsu, h1.symm, h2, h3, h4, h5, h6⟩
  · intro T K inst1 inst2 f E'
    exact lowerIdealWithoutBlowup_withBoundary_baseChange T K f E'
  · intro T j hj K inst1 inst2 f E' hBE htake hjE
    exact DivisorReduction.lowerBoundaryWithoutBlowup_baseChange_sameNontrivialBoundary T j hj K f E' hBE htake hjE
  · intro T hV hO j hj K inst1 inst2 f E' hBE hjE htake hV' hpre
    exact DivisorReduction.lowerIdealAfterBlowup_fieldBaseChange exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le_consolidated494 isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV
      hO j hj K f E' hBE.symm hjE htake hV' hpre
  · intro T hV hO j hj K inst1 inst2 f E' hBE hjE htake hV' hpre
    exact DivisorReduction.lowerBoundaryAfterBlowup_fieldBaseChange exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le_consolidated494 isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV hO
      j hj K f E' hBE.symm hjE htake hV' hpre

private theorem emptyPulledBackCenterCompatibility_consolidated494 : DivisorReduction.EmptyPulledBackCenterCompatibility.{u} := by
  refine ⟨?_, ?_⟩
  · intro T hV hO j hj Y h htop
    exact DivisorReduction.comap_lowerIdealAfterBlowup_eq_comap_lowerIdealWithoutBlowup exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le_consolidated494
      isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV hO j hj Y h htop
  · intro T hV j hj Y h htop
    exact DivisorReduction.comap_lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_eq_top exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le_consolidated494
      isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV j hj Y h htop

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})

private theorem pushedBlowupSequenceProperties_canonicalAlgorithmRules_consolidated494 :
    PushedBlowupSequenceProperties hres blowupPreservesNoetherian := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hV j hj
    exact DivisorReduction.isOpen_preimage_support_containedComponentsIdeal T j hj
      (DivisorReduction.preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj)
  · intro T inst j hj s hpr hmk
    exact DivisorReduction.ker_embeddingIntoAmbient_zero_eq_comap_isoObjZero hres blowupPreservesNoetherian T j hj s hpr hmk
  · intro T inst j hj hb s hpr hmk
    exact DivisorReduction.ker_embeddingIntoAmbient_zero_eq_comap_blowupMorphism hres blowupPreservesNoetherian T j hj hb s hpr
      hmk
  · intro T hV j hj S
    exact DivisorReduction.isSmoothDivisor_boundary_comap_isoObjZero T hV j hj S
  · intro T inst j hj s hpr hmk t ht
    exact DivisorReduction.boundaryLocus_subset_preimage_otherBoundaryLocus hres blowupPreservesNoetherian T j hj s hpr
      hmk t ht
  · intro T inst j hj hb s hpr hmk t ht
    exact DivisorReduction.boundaryLocus_subset_preimage_otherBoundaryLocus_succ hres blowupPreservesNoetherian T j hj hb s
      hpr hmk t ht
  · intro T hV
    exact DivisorReduction.one_le_mult_of_isAdmissible T hV
  · intro T hV hOB hbal j hj hpre hlow inst s hpr hmk t ht
    exact DivisorReduction.isSmoothDivisor_ker_embeddingIntoAmbient_of_eq_top hres blowupPreservesNoetherian T hV
      hOB hbal j hj hpre hlow s hpr hmk t ht
  · intro T hV hOB hbal j hj hne hb hlow inst s hpr hmk t ht
    exact DivisorReduction.isSmoothDivisor_ker_embeddingIntoAmbient hres blowupPreservesNoetherian
      orderAtComapOffExceptionalLocus_consolidated494 T hV hOB j hj hb hlow s hpr hmk
      (fun t _ => DivisorReduction.embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres
        blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
        (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t) t ht
  · intro T inst j hj s hpr hmk t
    exact DivisorReduction.projectionToSpec_eq_comp_ambientMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk t
  · intro T inst j hj hb s hpr hmk t
    exact DivisorReduction.projectionToSpec_eq_comp_prependedAmbientSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk t
  · intro X Y f inst I
    exact support_ker_comp_subset_support_ker I.subschemeι f
  · intro T hV j hj
    exact DivisorReduction.support_containedComponentsIdeal_subset_support_boundary T j hj

private theorem divisorReductionStepProperties_canonicalAlgorithmRules_consolidated494 :
    DivisorReductionStepProperties hres blowupPreservesNoetherian :=
  (divisorReductionProperties_of_blowupPreservesNoetherian hres blowupPreservesNoetherian).toDivisorReductionStepProperties

theorem divisorReductionHypotheses_canonicalAlgorithmRules :
    DivisorReduction.DivisorReductionHypotheses hres := by
  have hstepProps := divisorReductionStepProperties_canonicalAlgorithmRules_consolidated494 hres
  have hfacts := hstepProps.toDivisorReductionTerminationProperties
  refine
    { trivial_of_coSupport_empty := ?_
      baseChange := smoothPullbackCompatibility_of_divisorReductionTermination_consolidated494 hres hfacts
      smoothImpliesFlat := ⟨fun X Y f hf => by have := hf; infer_instance⟩
      degenerateTransversal := emptyPulledBackCenterCompatibility_consolidated494
      fieldBaseChangeCompatibility := fieldBaseChangeCompatibility_of_divisorReductionTermination_consolidated494 hres hfacts
      boundaryReindexingInvariance := DivisorReduction.boundaryReindexingInvariance
      fieldLower := divisorRestrictionFieldBaseChange_consolidated494
      divisorReduction := hstepProps
      pushedBlowupSequenceProperties := pushedBlowupSequenceProperties_canonicalAlgorithmRules_consolidated494 hres }
  intro L j T hV hj Y q h inst hq E' hV' hne hempty B' hB'
  exact DivisorReductionEmptyOrderLocus.divisorFamily_isPullbackSequenceOfBlowups_of_orderAtLeastLocus_empty hres L j T hV hj Y q h hq E' hV'
    hne hempty B' hB'


end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.ChartIsolation
section


section
namespace FunctorialResolution.EmbeddedResolution

namespace OpenImmersionRestriction

abbrev principalizationOfEmbedding (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) :
    IdealBlowupSequence D.ambientStruct (AlgebraicGeometry.Scheme.Hom.ker D.emb) [] :=
  A k D.ambient D.ambientStruct (AlgebraicGeometry.Scheme.Hom.ker D.emb)
    D.nonzeroOnComponents_ker [] D.sncEmpty

structure ChartIsolationHypotheses (V : VanishingAssignment.{u}) (A : PrincipalizationAlgorithm.{u}) : Prop where
  noetherianSpace_alive : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      [IsAffine Y] [IsReduced Y]
      (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
      [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (i : ℕ),
      i ≤ (D.toEmbeddedBlowupSequence A).length →
        TopologicalSpace.NoetherianSpace ↥((D.toEmbeddedBlowupSequence A).strictTransform i)
  isClosedEmbedding_aliveι : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      [IsAffine Y] [IsReduced Y]
      (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
      [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (i : ℕ),
      i ≤ (D.toEmbeddedBlowupSequence A).length →
        Topology.IsClosedEmbedding ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base
  generic_not_mem_member : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      [IsAffine Y] [IsReduced Y]
      (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
      [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (i : ℕ),
      i ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform i),
      ∀ ξ : ↥((D.toEmbeddedBlowupSequence A).strictTransform i), IsGenericPoint ξ C →
      ∀ E ∈ (principalizationOfEmbedding k Y pY D A).boundary i,
        ((D.toEmbeddedBlowupSequence A).strictTransformι i).base ξ ∉
          (E.support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i))
  agreeNear_orderAt_eq_one : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      [IsAffine Y] [IsReduced Y]
      (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
      [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (i : ℕ),
      i ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform i),
      ∀ ξ : ↥((D.toEmbeddedBlowupSequence A).strictTransform i), IsGenericPoint ξ C →
      ∀ hC : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C),
        AgreeNear ((principalizationOfEmbedding k Y pY D A).ideal i)
            (V ((D.toEmbeddedBlowupSequence A).schemeAt i)
              ⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C, hC⟩)
            (((D.toEmbeddedBlowupSequence A).strictTransformι i).base ξ) ∧
          orderAt ((principalizationOfEmbedding k Y pY D A).ideal i)
            (((D.toEmbeddedBlowupSequence A).strictTransformι i).base ξ) = 1

theorem disjoint_detachedComponent_of_principalizationCertificate
    {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]
    (S : EmbeddedBlowupSequence k Y pY) (i : ℕ)
    [TopologicalSpace.NoetherianSpace ↥(S.strictTransform i)]
    (I : (S.schemeAt i).IdealSheafData) (Mem : Set ↥(S.schemeAt i))
    (hcl : Topology.IsClosedEmbedding ⇑(S.strictTransformι i).base)
    (hmem : ∀ C ∈ irreducibleComponents ↥(S.strictTransform i),
      ∀ ξ : ↥(S.strictTransform i), IsGenericPoint ξ C → ((S.strictTransformι i).base ξ) ∉ Mem)
    (hagree : ∀ C ∈ irreducibleComponents ↥(S.strictTransform i),
      ∀ ξ : ↥(S.strictTransform i), IsGenericPoint ξ C →
      ∀ hC : IsClosed (⇑(S.strictTransformι i).base '' C),
        AgreeNear I (V (S.schemeAt i) ⟨⇑(S.strictTransformι i).base '' C, hC⟩) ((S.strictTransformι i).base ξ) ∧
          orderAt I ((S.strictTransformι i).base ξ) = 1)
    (hcert : ∃ q : S.schemeAt i ⟶ Spec (CommRingCat.of k),
      PrincipalizationCertificate (S.schemeAt i) q I 1 Mem (S.ambientCenter i))
    {C₁ C₂ : Set ↥(S.strictTransform i)}
    (h₁ : C₁ ∈ S.detachedComponents i)
    (h₂ : C₂ ∈ irreducibleComponents ↥(S.strictTransform i))
    (h₂' : C₂ ∉ S.detachedComponents i) :
    Disjoint C₁ C₂ := by
  obtain ⟨q, hq⟩ := hcert
  have hiso := orderOneCentersIsolated_of_principalizationCertificate (V := V) hV hq
  have hC₁comp := ((S.mem_detachedComponents i C₁).1 h₁).1
  have hC₁sub := ((S.mem_detachedComponents i C₁).1 h₁).2
  have hcl₁ : IsClosed C₁ := isClosed_of_mem_irreducibleComponents _ hC₁comp
  have hcl₂ : IsClosed C₂ := isClosed_of_mem_irreducibleComponents _ h₂
  obtain ⟨ξ₁, hξ₁⟩ := QuasiSober.sober hC₁comp.1 hcl₁
  obtain ⟨ξ₂, hξ₂⟩ := QuasiSober.sober h₂.1 hcl₂
  have him1 : IsClosed (⇑(S.strictTransformι i).base '' C₁) := hcl.isClosedMap _ hcl₁
  have him2 : IsClosed (⇑(S.strictTransformι i).base '' C₂) := hcl.isClosedMap _ hcl₂
  have hirr1 : IsIrreducible (⇑(S.strictTransformι i).base '' C₁) :=
    hC₁comp.1.image _ hcl.continuous.continuousOn
  have hirr2 : IsIrreducible (⇑(S.strictTransformι i).base '' C₂) :=
    h₂.1.image _ hcl.continuous.continuousOn
  have hg1 : IsGenericPoint ((S.strictTransformι i).base ξ₁) (⇑(S.strictTransformι i).base '' C₁) :=
    isGenericPoint_image_of_isClosedEmbedding hcl hξ₁
  have hg2 : IsGenericPoint ((S.strictTransformι i).base ξ₂) (⇑(S.strictTransformι i).base '' C₂) :=
    isGenericPoint_image_of_isClosedEmbedding hcl hξ₂
  obtain ⟨hag1, hord1⟩ := hagree C₁ hC₁comp ξ₁ hξ₁ him1
  obtain ⟨hag2, hord2⟩ := hagree C₂ h₂ ξ₂ hξ₂ him2
  have hnotcenter :
      ((S.strictTransformι i).base ξ₂) ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
    intro hmem2
    apply h₂'
    rw [S.mem_detachedComponents i C₂]
    exact ⟨h₂, (hg2.mem_closed_set_iff
      (hV.isClosed_support (S.schemeAt i) (S.ambientCenter i))).mp hmem2⟩
  rw [Set.disjoint_left]
  intro x hx1 hx2
  exact hiso
    ⟨⇑(S.strictTransformι i).base '' C₁, ⇑(S.strictTransformι i).base '' C₂,
      (S.strictTransformι i).base ξ₁, (S.strictTransformι i).base ξ₂, (S.strictTransformι i).base x,
      him1, him2, hirr1, hirr2, hg1, hg2, ⟨x, hx1, rfl⟩, ⟨x, hx2, rfl⟩⟩
    rfl hC₁sub hnotcenter (hmem C₁ hC₁comp ξ₁ hξ₁) (hmem C₂ h₂ ξ₂ hξ₂) hag1 hord1
    ((one_le_orderAt_iff_mem_support I ((S.strictTransformι i).base ξ₂)).1 (le_of_eq hord2.symm))

section
variable {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension) (hrad : SmoothSubschemeIdealIsRadical.{u}) (hind : ChartIsolationHypotheses V (canonicalPrincipalization hres hrad)) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) [IsAffine Y] [IsReduced Y] (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY] [QuasiCompact pY] (D : EmbeddingDatum k Y pY)
include hV hB hind

theorem disjoint_detachedComponent_canonicalPrincipalization
    (i : ℕ)
    (hi : i < (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    {C₁ C₂ : Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform i)}
    (h₁ : C₁ ∈ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedComponents i)
    (h₂ : C₂ ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform i))
    (h₂' : C₂ ∉ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedComponents i) :
    Disjoint C₁ C₂ := by
  have := hind.noetherianSpace_alive k Y pY D i (le_of_lt hi)
  have hspec := (PrincipalizationRules.isMaxOrderReduction_outputLevelData (canonicalAlgorithmRules hres) hB
      (krullDimSucc D.ambient)).cert
      (markedTripleOrderOne k D.ambient D.ambientStruct (AlgebraicGeometry.Scheme.Hom.ker D.emb) [])
      (markedTripleOrderOne_isAdmissible k D.ambient D.ambientStruct
        (AlgebraicGeometry.Scheme.Hom.ker D.emb) D.nonzeroOnComponents_ker [] D.sncEmpty)
      (le_of_eq (markedTripleOrderOne_dim k D.ambient D.ambientStruct
        (AlgebraicGeometry.Scheme.Hom.ker D.emb) []))
      i hi
  refine disjoint_detachedComponent_of_principalizationCertificate hV
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)) i
    ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal i)
    (⋃ E ∈ (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).boundary i,
      (E.support : Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt i)))
    (hind.isClosedEmbedding_aliveι k Y pY D i (le_of_lt hi)) ?_ ?_ ⟨_, hspec⟩ h₁ h₂ h₂'
  · intro C hC ξ hξ hx
    obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp hx
    exact hind.generic_not_mem_member k Y pY D i (le_of_lt hi) C hC ξ hξ E hE hxE
  · exact hind.agreeNear_orderAt_eq_one k Y pY D i (le_of_lt hi)

theorem detachedLocusIsOpen_toEmbeddedBlowupSequence
    :
    EmbeddedBlowupSequence.DetachedLocusIsOpen (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)) := by
  intro i hi
  have := hind.noetherianSpace_alive k Y pY D i (le_of_lt hi)
  rw [EmbeddedBlowupSequence.detachedLocus_eq_sUnion]
  exact isOpen_sUnion_of_irreducibleComponents _
    (fun C₁ hC₁ C₂ hC₂ hC₂' =>
      disjoint_detachedComponent_canonicalPrincipalization hV hres hB hrad hind k Y pY D i hi hC₁ hC₂ hC₂')


end

theorem detachedLocusIsOpenForEmbeddings_canonicalPrincipalization
    {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    (hind : ChartIsolationHypotheses V (canonicalPrincipalization hres hrad)) :
    DetachedLocusIsOpenForEmbeddings (canonicalPrincipalization hres hrad) := by
  intro k _ _ Y pY _ _ _ _ D
  exact detachedLocusIsOpen_toEmbeddedBlowupSequence hV hres hB hrad hind k Y pY D

end OpenImmersionRestriction

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.StrictTransformAvoidance
section


section
namespace FunctorialResolution.EmbeddedResolution

private theorem comp_base_apply_consolidated342 {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (x : ↥A) :
    (f ≫ g).base x = g.base (f.base x) := by simp

namespace EmbeddedBlowupSequence

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]

def AvoidsCenters (S : EmbeddedBlowupSequence k Y pY) : ∀ (i : ℕ), ↥(S.schemeAt i) → Prop
  | 0 => fun _ => True
  | (i + 1) => fun x =>
      (S.blowdown i).base x ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) ∧
        AvoidsCenters S i ((S.blowdown i).base x)

section
variable (S : EmbeddedBlowupSequence k Y pY)

@[simp] theorem avoidsCenters_zero (x : ↥(S.schemeAt 0)) : S.AvoidsCenters 0 x := trivial

@[simp] theorem avoidsCenters_succ_iff (i : ℕ) (x : ↥(S.schemeAt (i + 1))) :
    S.AvoidsCenters (i + 1) x ↔
      ((S.blowdown i).base x ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) ∧
        S.AvoidsCenters i ((S.blowdown i).base x)) :=
  Iff.rfl


end

private theorem forall_avoidsCenters_strictTransformι_of_isGenericPoint_consolidated342 [IsReduced Y]
    (S : EmbeddedBlowupSequence k Y pY)
    (hN : ∀ j ≤ S.length, IsNoetherian (S.schemeAt j)) :
    ∀ (i : ℕ), i ≤ S.length → ∀ C : Set ↥(S.strictTransform i),
      C ∈ irreducibleComponents ↥(S.strictTransform i) →
      ∀ ξ : ↥(S.strictTransform i), IsGenericPoint ξ C →
      S.AvoidsCenters i ((S.strictTransformι i).base ξ) := by
  intro i
  induction i with
  | zero =>
    intro _ _ _ _ _
    exact S.avoidsCenters_zero _
  | succ i ih =>
    intro hi C hC ξ hξ
    have hi' : i < S.length := Nat.lt_of_succ_le hi
    obtain ⟨C', hC', hη', hfr⟩ := S.exists_irreducibleComponent_isGenericPoint_strictTransformMap hN i hi' C hC ξ hξ
    have key : (S.strictTransformι i).base ((S.strictTransformMap i).base ξ)
        = (S.blowdown i).base ((S.strictTransformι (i + 1)).base ξ) := by
      have h : (S.strictTransformMap i ≫ S.strictTransformι i).base ξ
          = (S.strictTransformι (i + 1) ≫ S.blowdown i).base ξ := by
        rw [S.strictTransformMap_comp_strictTransformι i]
      simpa using h
    refine (S.avoidsCenters_succ_iff i _).mpr ⟨?_, ?_⟩
    · rw [← key]
      exact S.notMem_ambientCenter_support_of_isGenericPoint i C' hC' hfr _ hη'
    · rw [← key]
      exact ih (Nat.le_of_succ_le hi) C' hC' _ hη'

theorem avoidsCenters_strictTransformι_of_isGenericPoint [IsReduced Y] (S : EmbeddedBlowupSequence k Y pY)
    (hN : ∀ j ≤ S.length, IsNoetherian (S.schemeAt j)) (i : ℕ) (hi : i ≤ S.length)
    (C : Set ↥(S.strictTransform i)) (hC : C ∈ irreducibleComponents ↥(S.strictTransform i))
    (ξ : ↥(S.strictTransform i)) (hξ : IsGenericPoint ξ C) :
    S.AvoidsCenters i ((S.strictTransformι i).base ξ) :=
  forall_avoidsCenters_strictTransformι_of_isGenericPoint_consolidated342 S hN i hi C hC ξ hξ

section
variable (S : EmbeddedBlowupSequence k Y pY) (i : ℕ)

theorem isOpenImmersion_ι_comp_blowdown (hi : i < S.length)
    (U : (S.schemeAt (i + 1)).Opens)
    (hU : (U : Set ↥(S.schemeAt (i + 1))) ⊆
      ⇑(S.blowdown i).base ⁻¹' ((S.ambientCenterSupportCompl i : (S.schemeAt i).Opens) : Set ↥(S.schemeAt i))) :
    IsOpenImmersion (U.ι ≫ S.blowdown i) := by
  have : CategoryTheory.IsIso (S.blowdown i ∣_ S.ambientCenterSupportCompl i) :=
    S.isIso_blowdown_restrict_ambientCenterSupportCompl i hi
  have : IsOpenImmersion (S.blowdown i ∣_ S.ambientCenterSupportCompl i) := inferInstance
  have hle : U ≤ (TopologicalSpace.Opens.map (S.blowdown i).base).obj (S.ambientCenterSupportCompl i) := by
    intro x hx
    exact hU hx
  have key : (S.schemeAt (i + 1)).homOfLE hle ≫
      ((S.blowdown i ∣_ S.ambientCenterSupportCompl i) ≫ (S.ambientCenterSupportCompl i).ι) = U.ι ≫ S.blowdown i := by
    rw [AlgebraicGeometry.morphismRestrict_ι, ← CategoryTheory.Category.assoc,
      AlgebraicGeometry.Scheme.homOfLE_ι]
  rw [← key]
  infer_instance

theorem mem_image_strictTransformι_of_mem_image_succ (C : Set ↥(S.strictTransform (i + 1))) (η : ↥(S.strictTransform (i + 1))) (hη : IsGenericPoint η C)
    (C' : Set ↥(S.strictTransform i)) (hη' : IsGenericPoint ((S.strictTransformMap i).base η) C')
    (x : ↥(S.schemeAt (i + 1))) (hx : x ∈ ⇑(S.strictTransformι (i + 1)).base '' C) :
    (S.blowdown i).base x ∈ ⇑(S.strictTransformι i).base '' C' := by
  obtain ⟨c, hc, rfl⟩ := hx
  have hcont : Continuous ⇑(S.strictTransformMap i).base := (S.strictTransformMap i).base.hom.continuous
  have hηC : closure ({η} : Set ↥(S.strictTransform (i + 1))) = C := hη
  have hηC' : closure ({(S.strictTransformMap i).base η} : Set ↥(S.strictTransform i)) = C' := hη'
  have hclosed : IsClosed (⇑(S.strictTransformMap i).base ⁻¹' C') := by
    rw [← hηC']
    exact isClosed_closure.preimage hcont
  have hsub : C ⊆ ⇑(S.strictTransformMap i).base ⁻¹' C' := by
    rw [← hηC]
    refine closure_minimal ?_ hclosed
    intro z hz
    have hz' : z = η := hz
    subst hz'
    rw [Set.mem_preimage, ← hηC']
    exact subset_closure rfl
  refine ⟨(S.strictTransformMap i).base c, hsub hc, ?_⟩
  have key : ((S.strictTransformMap i) ≫ (S.strictTransformι i)).base c
      = ((S.strictTransformι (i + 1)) ≫ (S.blowdown i)).base c := by
    rw [S.strictTransformMap_comp_strictTransformι i]
  simpa using key


end

private theorem mem_closure_singleton_of_base_mem_consolidated342 {X₀ X₁ : Scheme.{u}}
    (π : X₁ ⟶ X₀) (V : X₁.Opens)
    (hoe : Topology.IsOpenEmbedding ⇑(V.ι ≫ π).base)
    {x y : ↥X₁} (hx : x ∈ V) (hy : y ∈ V)
    (h : π.base x ∈ closure ({π.base y} : Set ↥X₀)) :
    x ∈ closure ({y} : Set ↥X₁) := by
  have hvx : V.ι.base (⟨x, hx⟩ : ↥V) = x := rfl
  have hvy : V.ι.base (⟨y, hy⟩ : ↥V) = y := rfl
  have h' : (V.ι ≫ π).base (⟨y, hy⟩ : ↥V) ⤳ (V.ι ≫ π).base (⟨x, hx⟩ : ↥V) := by
    rw [comp_base_apply_consolidated342 V.ι π (⟨x, hx⟩ : ↥V), comp_base_apply_consolidated342 V.ι π (⟨y, hy⟩ : ↥V), hvx, hvy]
    exact specializes_iff_mem_closure.mpr h
  have hspec : (⟨y, hy⟩ : ↥V) ⤳ (⟨x, hx⟩ : ↥V) := hoe.isInducing.specializes_iff.mp h'
  have hfin := hspec.map V.ι.base.hom.continuous
  rw [hvx, hvy] at hfin
  exact specializes_iff_mem_closure.mp hfin

section
variable [IsReduced Y] (S : EmbeddedBlowupSequence k Y pY)

private theorem mem_image_strictTransformι_succ_of_mem_image_consolidated342 (i : ℕ) (hi : i < S.length)
    (C : Set ↥(S.strictTransform (i + 1))) (η : ↥(S.strictTransform (i + 1))) (hη : IsGenericPoint η C)
    (C' : Set ↥(S.strictTransform i)) (hη' : IsGenericPoint ((S.strictTransformMap i).base η) C')
    (x : ↥(S.schemeAt (i + 1)))
    (hx : (S.blowdown i).base x ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)))
    (hmem : (S.blowdown i).base x ∈ ⇑(S.strictTransformι i).base '' C') :
    x ∈ ⇑(S.strictTransformι (i + 1)).base '' C := by
  have hgenericImage : IsGenericPoint ((S.strictTransformι (i + 1)).base η) (⇑(S.strictTransformι (i + 1)).base '' C) :=
    FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding (S.isClosedEmbedding_strictTransformι (i + 1)) hη
  have hgenericImagePrev : IsGenericPoint ((S.strictTransformι i).base ((S.strictTransformMap i).base η))
      (⇑(S.strictTransformι i).base '' C') :=
    FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding (S.isClosedEmbedding_strictTransformι i) hη'
  have hclA : closure ({(S.strictTransformι (i + 1)).base η} : Set ↥(S.schemeAt (i + 1)))
      = ⇑(S.strictTransformι (i + 1)).base '' C := hgenericImage
  have hclB : closure ({(S.strictTransformι i).base ((S.strictTransformMap i).base η)} : Set ↥(S.schemeAt i))
      = ⇑(S.strictTransformι i).base '' C' := hgenericImagePrev
  have key : (S.strictTransformι i).base ((S.strictTransformMap i).base η)
      = (S.blowdown i).base ((S.strictTransformι (i + 1)).base η) := by
    have h : (S.strictTransformMap i ≫ S.strictTransformι i).base η
        = (S.strictTransformι (i + 1) ≫ S.blowdown i).base η := by
      rw [S.strictTransformMap_comp_strictTransformι i]
    simpa using h
  have hclosure : (S.blowdown i).base x ∈
      closure ({(S.blowdown i).base ((S.strictTransformι (i + 1)).base η)} : Set ↥(S.schemeAt i)) := by
    rw [← key, hclB]
    exact hmem
  have hy₀ : (S.blowdown i).base ((S.strictTransformι (i + 1)).base η) ∉
      ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
    intro hmemc
    exact hx (closure_minimal (Set.singleton_subset_iff.mpr hmemc)
      ((S.ambientCenter i).support).2 hclosure)
  obtain ⟨V, hVdef⟩ : ∃ V : (S.schemeAt (i + 1)).Opens,
      V = (TopologicalSpace.Opens.map (S.blowdown i).base).obj (S.ambientCenterSupportCompl i) := ⟨_, rfl⟩
  have hVsub : (V : Set ↥(S.schemeAt (i + 1))) ⊆
      ⇑(S.blowdown i).base ⁻¹'
        ((S.ambientCenterSupportCompl i : (S.schemeAt i).Opens) : Set ↥(S.schemeAt i)) := by
    rw [hVdef]
    intro y hy
    exact hy
  have hoi : IsOpenImmersion (V.ι ≫ S.blowdown i) :=
    S.isOpenImmersion_ι_comp_blowdown i hi V hVsub
  have hxV : x ∈ V := by
    rw [hVdef]
    exact hx
  have hyV : (S.strictTransformι (i + 1)).base η ∈ V := by
    rw [hVdef]
    exact hy₀
  have hmain := mem_closure_singleton_of_base_mem_consolidated342 (S.blowdown i) V
    (V.ι ≫ S.blowdown i).isOpenEmbedding hxV hyV hclosure
  rw [← hclA]
  exact hmain

theorem mem_image_strictTransformι_iff_of_notMem_ambientCenter (_hN : ∀ j ≤ S.length, IsNoetherian (S.schemeAt j)) (i : ℕ) (hi : i < S.length)
    (C : Set ↥(S.strictTransform (i + 1))) (η : ↥(S.strictTransform (i + 1))) (hη : IsGenericPoint η C)
    (C' : Set ↥(S.strictTransform i)) (hη' : IsGenericPoint ((S.strictTransformMap i).base η) C')
    (x : ↥(S.schemeAt (i + 1)))
    (hx : (S.blowdown i).base x ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i))) :
    ((S.blowdown i).base x ∈ ⇑(S.strictTransformι i).base '' C') ↔ (x ∈ ⇑(S.strictTransformι (i + 1)).base '' C) :=
  ⟨fun hmem => mem_image_strictTransformι_succ_of_mem_image_consolidated342 S i hi C η hη C' hη' x hx hmem,
    fun hxC => mem_image_strictTransformι_of_mem_image_succ S i C η hη C' hη' x hxC⟩


end

end EmbeddedBlowupSequence

namespace OpenImmersionRestriction

theorem mem_support_of_mem_support_comap {X Z : Scheme.{u}} (f : X ⟶ Z) (I : Z.IdealSheafData)
    (x : ↥X) (hx : x ∈ ((I.comap f).support : Set ↥X)) :
    f.base x ∈ (I.support : Set ↥Z) := by
  rw [FunctorialResolution.EmbeddedResolution.support_comap_eq] at hx
  exact hx

def reducedVanishingAssignment : VanishingAssignment.{u} :=
  fun _ T => Scheme.IdealSheafData.vanishingIdeal T

private theorem preimage_congr_of_inter_eq_consolidated342 {W : Scheme.{u}} {Z₁ Z₂ : TopologicalSpace.Closeds ↥W}
    {U : W.Opens} (h : (Z₁ : Set ↥W) ∩ (U : Set ↥W) = (Z₂ : Set ↥W) ∩ (U : Set ↥W))
    {A : Type u} (g : A → ↥W) (hg : ∀ a, g a ∈ (U : Set ↥W)) :
    g ⁻¹' (Z₁ : Set ↥W) = g ⁻¹' (Z₂ : Set ↥W) := by
  ext a
  constructor
  · intro ha
    have h2 : g a ∈ (Z₁ : Set ↥W) ∩ (U : Set ↥W) := ⟨ha, hg a⟩
    rw [h] at h2
    exact h2.1
  · intro ha
    have h2 : g a ∈ (Z₂ : Set ↥W) ∩ (U : Set ↥W) := ⟨ha, hg a⟩
    rw [← h] at h2
    exact h2.1

section
variable {W : Scheme.{u}} (Z₁ Z₂ : TopologicalSpace.Closeds ↥W) (U : W.Opens)

private theorem vanishingIdeal_ideal_eq_of_inter_eq_consolidated342 (h : (Z₁ : Set ↥W) ∩ (U : Set ↥W) = (Z₂ : Set ↥W) ∩ (U : Set ↥W))
    (V : W.affineOpens) (hV : (V.1 : Set ↥W) ⊆ (U : Set ↥W)) :
    (Scheme.IdealSheafData.vanishingIdeal Z₁).ideal V
      = (Scheme.IdealSheafData.vanishingIdeal Z₂).ideal V := by
  have hg : ∀ a, (V.2.fromSpec).base a ∈ (U : Set ↥W) := by
    intro a
    have ha : (V.2.fromSpec).base a ∈ (V.1 : Set ↥W) := by
      rw [← IsAffineOpen.range_fromSpec V.2]
      exact Set.mem_range_self a
    exact hV ha
  exact congrArg PrimeSpectrum.vanishingIdeal
    (preimage_congr_of_inter_eq_consolidated342 h (fun a => (V.2.fromSpec).base a) hg)

theorem agreeNear_vanishingIdeal_of_inter_eq (x : ↥W) (hx : x ∈ (U : Set ↥W))
    (h : (Z₁ : Set ↥W) ∩ (U : Set ↥W) = (Z₂ : Set ↥W) ∩ (U : Set ↥W)) :
    AgreeNear (Scheme.IdealSheafData.vanishingIdeal Z₁)
      (Scheme.IdealSheafData.vanishingIdeal Z₂) x := by
  refine (agreeNear_iff _ _ _).mpr ⟨U, hx, ?_⟩
  refine Scheme.IdealSheafData.ext (funext fun V => ?_)
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  refine congrArg _ ?_
  refine vanishingIdeal_ideal_eq_of_inter_eq_consolidated342 Z₁ Z₂ U h _ ?_
  intro y hy
  obtain ⟨z, -, rfl⟩ := hy
  exact z.2


end

private theorem comap_eq_comap_mul_of_comap_eq_top_consolidated342 {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (P Q : Ideal B) (hP : Ideal.comap φ P = ⊤) :
    Ideal.comap φ Q = Ideal.comap φ (P * Q) := by
  have h1 : (1 : A) ∈ Ideal.comap φ P := by
    rw [hP]
    exact Submodule.mem_top
  have h2 : φ (1 : A) ∈ P := Ideal.mem_comap.mp h1
  rw [map_one] at h2
  have hPtop : P = ⊤ := Submodule.eq_top_iff'.mpr fun x => by
    simpa using Ideal.mul_mem_left P x h2
  rw [hPtop, ← Ideal.one_eq_top, one_mul]

theorem comap_eq_comap_comp_of_mul_eq {X Z : Scheme.{u}} (f : X ⟶ Z) (U : X.Opens)
    (I J : X.IdealSheafData) (K : Z.IdealSheafData)
    (hmul : I * J = K.comap f) (hI : I.comap U.ι = ⊤) :
    J.comap U.ι = K.comap (U.ι ≫ f) := by
  have hcomp : K.comap (U.ι ≫ f) = (K.comap f).comap U.ι := by
    simp [Scheme.IdealSheafData.comap_comp]
  rw [hcomp, ← hmul]
  refine Scheme.IdealSheafData.ext (funext fun V => ?_)
  rw [AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion J U.ι V,
    AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion (I * J) U.ι V]
  simp only [AlgebraicGeometry.Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  refine comap_eq_comap_mul_of_comap_eq_top_consolidated342 _ _ _ ?_
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I U.ι V, hI]
  simp

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]
  [QuasiCompact pY]

omit [QuasiCompact pY] in
theorem isNoetherian_schemeAt_toEmbeddedBlowupSequence (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) :
    ∀ i ≤ (D.toEmbeddedBlowupSequence A).length,
      IsNoetherian ((D.toEmbeddedBlowupSequence A).schemeAt i) :=
  fun i hi => (D.toEmbeddedBlowupSequence A).isNoetherian_schemeAt i hi

section
variable (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u})

private theorem forall_not_avoidsCenters_of_mem_boundary_support_consolidated342 :
    ∀ (i : ℕ), i ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ E : ((principalizationOfEmbedding k Y pY D A).schemeAt i).IdealSheafData,
        E ∈ (principalizationOfEmbedding k Y pY D A).boundary i →
        ∀ x : ↥((D.toEmbeddedBlowupSequence A).schemeAt i),
          x ∈ (E.support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i)) →
          ¬ (D.toEmbeddedBlowupSequence A).AvoidsCenters i x := by
  intro i
  induction i with
  | zero =>
      intro _ E hE x hx hcl
      rw [(principalizationOfEmbedding k Y pY D A).boundary_zero] at hE
      simp at hE
  | succ i ih =>
      intro hi E hE x hx hcl
      have hilt : i < (principalizationOfEmbedding k Y pY D A).length := hi
      rw [(principalizationOfEmbedding k Y pY D A).boundary_succ_eq_map_strictTransform_append i hilt, List.mem_append] at hE
      have hcl' := ((D.toEmbeddedBlowupSequence A).avoidsCenters_succ_iff i x).mp hcl
      rcases hE with hE | hE
      · obtain ⟨E', hE', rfl⟩ := List.mem_map.mp hE
        have hmem : x ∈ ((E'.comap ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i)).support :
            Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt (i + 1))) :=
          AlgebraicGeometry.Scheme.IdealSheafData.support_antitone
            (FunctorialResolution.EmbeddedResolution.comap_le_strictTransform
              ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i)
              ((principalizationOfEmbedding k Y pY D A).center i) E') hx
        have hmem2 : ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i).base x ∈
            (E'.support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i)) :=
          mem_support_of_mem_support_comap ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i) E' x hmem
        exact ih (Nat.le_of_succ_le hi) E' hE' _ hmem2 hcl'.2
      · rw [List.mem_singleton] at hE
        subst hE
        rw [(principalizationOfEmbedding k Y pY D A).exceptionalIdeal_eq i] at hx
        have hmem2 : ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i).base x ∈
            (((principalizationOfEmbedding k Y pY D A).center i).support :
              Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i)) :=
          mem_support_of_mem_support_comap ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i)
            ((principalizationOfEmbedding k Y pY D A).center i) x hx
        exact hcl'.1 hmem2

theorem not_avoidsCenters_of_mem_boundary_support (i : ℕ) (hi : i ≤ (D.toEmbeddedBlowupSequence A).length)
    (E : ((principalizationOfEmbedding k Y pY D A).schemeAt i).IdealSheafData)
    (hE : E ∈ (principalizationOfEmbedding k Y pY D A).boundary i)
    (x : ↥((D.toEmbeddedBlowupSequence A).schemeAt i))
    (hx : x ∈ (E.support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i))) :
    ¬ (D.toEmbeddedBlowupSequence A).AvoidsCenters i x :=
  forall_not_avoidsCenters_of_mem_boundary_support_consolidated342 D A i hi E hE x hx


end

private theorem ker_congr_consolidated342 {A B : Scheme.{u}} {f g : A ⟶ B}
    [QuasiCompact f] [QuasiCompact g] (h : f = g) :
    AlgebraicGeometry.Scheme.Hom.ker f = AlgebraicGeometry.Scheme.Hom.ker g := by
  subst h
  rfl

private theorem ker_comap_iso_hom_eq_ker_comp_inv_consolidated342 {W B X : Scheme.{u}} (j : W ⟶ B) (e : X ≅ B)
    [QuasiCompact j] [QuasiCompact (j ≫ e.inv)] :
    (AlgebraicGeometry.Scheme.Hom.ker j).comap e.hom
      = AlgebraicGeometry.Scheme.Hom.ker (j ≫ e.inv) := by
  have h2 : (j ≫ e.inv) ≫ e.hom = j := by simp
  have : QuasiCompact ((j ≫ e.inv) ≫ e.hom) := by
    rw [h2]
    infer_instance
  have h3 : AlgebraicGeometry.Scheme.Hom.ker j
      = AlgebraicGeometry.Scheme.Hom.ker ((j ≫ e.inv) ≫ e.hom) := ker_congr_consolidated342 h2.symm
  rw [h3]
  exact FunctorialResolution.Blowup.comap_ker_comp_of_isOpenImmersion (j ≫ e.inv) e.hom

private theorem radical_ker_eq_of_isReduced_consolidated342 {W Z : Scheme.{u}} [IsReduced W]
    (f : W ⟶ Z) :
    (AlgebraicGeometry.Scheme.Hom.ker f).radical = AlgebraicGeometry.Scheme.Hom.ker f := by
  have hle : (AlgebraicGeometry.Scheme.Hom.ker f).radical
      ≤ AlgebraicGeometry.Scheme.Hom.ker f := by
    show (AlgebraicGeometry.Scheme.Hom.ker f).radical ≤
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals
        (fun U : Z.affineOpens =>
          RingHom.ker (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.app f U.1)))
    rw [AlgebraicGeometry.Scheme.IdealSheafData.le_ofIdeals_iff]
    intro U
    have h1 : (AlgebraicGeometry.Scheme.Hom.ker f).ideal U ≤
        RingHom.ker (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.app f U.1)) :=
      AlgebraicGeometry.Scheme.IdealSheafData.ideal_ofIdeals_le _ U
    have hrad : (RingHom.ker
        (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.app f U.1))).IsRadical := by
      rw [RingHom.ker_eq_comap_bot]
      exact Ideal.isRadical_bot.comap _
    exact le_trans (Ideal.radical_mono h1) hrad
  exact le_antisymm hle (AlgebraicGeometry.Scheme.IdealSheafData.le_radical _)

private theorem radical_eq_of_eq_ker_consolidated342 {Z W : Scheme.{u}} [IsReduced W]
    (I : Z.IdealSheafData) (f : W ⟶ Z)
    (h : I = AlgebraicGeometry.Scheme.Hom.ker f) : I.radical = I := by
  subst h
  exact radical_ker_eq_of_isReduced_consolidated342 f

theorem principalizationOfEmbedding_ideal_zero_eq_vanishingIdeal [IsReduced Y]
    (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u})
    (hcl : IsClosed (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base)) :
    (principalizationOfEmbedding k Y pY D A).ideal 0 =
      Scheme.IdealSheafData.vanishingIdeal
        (⟨Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base, hcl⟩ :
          TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt 0)) := by
  have hB : (D.toEmbeddedBlowupSequence A).strictTransformIdeal 0
      = AlgebraicGeometry.Scheme.Hom.ker
          (D.emb ≫ (principalizationOfEmbedding k Y pY D A).isoZero.inv) :=
    EmbeddedBlowupSequence.strictTransformIdeal_zero (D.toEmbeddedBlowupSequence A)
  have hA : (principalizationOfEmbedding k Y pY D A).ideal 0
      = AlgebraicGeometry.Scheme.Hom.ker
          (D.emb ≫ (principalizationOfEmbedding k Y pY D A).isoZero.inv) := by
    rw [IdealBlowupSequence.ideal_zero, FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_zero]
    exact ker_comap_iso_hom_eq_ker_comp_inv_consolidated342 D.emb (principalizationOfEmbedding k Y pY D A).isoZero
  have hsupp : (⟨Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base, hcl⟩ :
      TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt 0))
      = ((D.toEmbeddedBlowupSequence A).strictTransformIdeal 0).support :=
    TopologicalSpace.Closeds.ext
      (Scheme.IdealSheafData.range_subschemeι ((D.toEmbeddedBlowupSequence A).strictTransformIdeal 0))
  have hrad : ((D.toEmbeddedBlowupSequence A).strictTransformIdeal 0).radical = (D.toEmbeddedBlowupSequence A).strictTransformIdeal 0 :=
    radical_eq_of_eq_ker_consolidated342 ((D.toEmbeddedBlowupSequence A).strictTransformIdeal 0)
      (D.emb ≫ (principalizationOfEmbedding k Y pY D A).isoZero.inv) hB
  have key : Scheme.IdealSheafData.vanishingIdeal
      (⟨Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base, hcl⟩ :
        TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt 0))
      = (D.toEmbeddedBlowupSequence A).strictTransformIdeal 0 := by
    rw [hsupp, Scheme.IdealSheafData.vanishingIdeal_support]
    exact hrad
  exact hA.trans (hB.symm.trans key.symm)

def AgreesWithComponentsOrderOne (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) (i : ℕ) : Prop :=
  ∀ C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform i),
  ∀ ξ : ↥((D.toEmbeddedBlowupSequence A).strictTransform i), IsGenericPoint ξ C →
  ∀ hC : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C),
    AgreeNear ((principalizationOfEmbedding k Y pY D A).ideal i)
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C, hC⟩ :
            TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i)))
        (((D.toEmbeddedBlowupSequence A).strictTransformι i).base ξ) ∧
      orderAt ((principalizationOfEmbedding k Y pY D A).ideal i)
        (((D.toEmbeddedBlowupSequence A).strictTransformι i).base ξ) = 1

section
variable {X : Scheme.{u}} (x : ↥X)

private theorem eq_of_specializes_of_isField_stalk_consolidated342 (hfield : IsField ↑(X.presheaf.stalk x)) (y : ↥X) (hy : y ⤳ x) : y = x := by
  have hrange : Set.range ⇑(X.fromSpecStalk x).base = {z : ↥X | z ⤳ x} := by
    rw [AlgebraicGeometry.Scheme.range_fromSpecStalk]
  have hy' : y ∈ Set.range ⇑(X.fromSpecStalk x).base := by
    rw [hrange]; exact hy
  have hx' : x ∈ Set.range ⇑(X.fromSpecStalk x).base := by
    rw [hrange]; exact specializes_refl x
  obtain ⟨a, ha⟩ := hy'
  obtain ⟨b, hb⟩ := hx'
  have hab : a = b := by
    let : Field ↑(X.presheaf.stalk x) := hfield.toField
    have key : ∀ p q : PrimeSpectrum ↑(X.presheaf.stalk x), p = q := fun p q =>
      Subsingleton.elim p q
    exact key a b
  exact ha.symm.trans ((congrArg (fun t => (X.fromSpecStalk x).base t) hab).trans hb)

private theorem closure_singleton_mem_irreducibleComponents_consolidated342 (h : ∀ y : ↥X, y ⤳ x → y = x) :
    closure ({x} : Set ↥X) ∈ irreducibleComponents ↥X := by
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro S hS hsub
  obtain ⟨y, hy⟩ := QuasiSober.sober hS.closure isClosed_closure
  have hy2 : closure ({y} : Set ↥X) = closure S := hy
  have hxS : x ∈ closure S := subset_closure (hsub (subset_closure rfl))
  have hyx : y = x := by
    refine h y (specializes_iff_mem_closure.mpr ?_)
    rw [hy2]
    exact hxS
  rw [hyx] at hy2
  rw [hy2]
  exact subset_closure


end

private theorem eq_of_specializes_iso_hom_consolidated342 {X B : Scheme.{u}} (e : X ≅ B) (x : ↥X)
    (h : ∀ y : ↥X, y ⤳ x → y = x) (w : ↥B) (hw : w ⤳ e.hom.base x) :
    w = e.hom.base x := by
  have hcont : Continuous ⇑e.inv.base := e.inv.base.hom.continuous
  have h1 : e.inv.base w ⤳ e.inv.base (e.hom.base x) := hw.map hcont
  have h2 : e.inv.base (e.hom.base x) = x := by
    rw [← comp_base_apply_consolidated342 e.hom e.inv x, e.hom_inv_id]
    simp
  rw [h2] at h1
  have h3 := h _ h1
  have h4 : e.hom.base (e.inv.base w) = w := by
    rw [← comp_base_apply_consolidated342 e.inv e.hom w, e.inv_hom_id]
    simp
  rw [← h4, h3]

section
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y] [IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY] [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u})

private theorem not_isField_stalk_strictTransformι_zero_consolidated342 (ξ : ↥((D.toEmbeddedBlowupSequence A).strictTransform 0)) :
    ¬ IsField ↑(((D.toEmbeddedBlowupSequence A).schemeAt 0).presheaf.stalk
      (((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ)) := by
  intro hfield
  have hB : (D.toEmbeddedBlowupSequence A).strictTransformIdeal 0
      = AlgebraicGeometry.Scheme.Hom.ker
          (D.emb ≫ (principalizationOfEmbedding k Y pY D A).isoZero.inv) :=
    EmbeddedBlowupSequence.strictTransformIdeal_zero (D.toEmbeddedBlowupSequence A)
  have hcomap : (AlgebraicGeometry.Scheme.Hom.ker D.emb).comap
        (principalizationOfEmbedding k Y pY D A).isoZero.hom
      = AlgebraicGeometry.Scheme.Hom.ker
          (D.emb ≫ (principalizationOfEmbedding k Y pY D A).isoZero.inv) :=
    ker_comap_iso_hom_eq_ker_comp_inv_consolidated342 D.emb (principalizationOfEmbedding k Y pY D A).isoZero
  have hxsupp : ((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ ∈
      ((((D.toEmbeddedBlowupSequence A).strictTransformIdeal 0).support) : Set ↥((D.toEmbeddedBlowupSequence A).schemeAt 0)) := by
    rw [← Scheme.IdealSheafData.range_subschemeι ((D.toEmbeddedBlowupSequence A).strictTransformIdeal 0)]
    exact ⟨ξ, rfl⟩
  have hz : (principalizationOfEmbedding k Y pY D A).isoZero.hom.base
        (((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ)
      ∈ ((AlgebraicGeometry.Scheme.Hom.ker D.emb).support : Set ↥D.ambient) := by
    refine mem_support_of_mem_support_comap (principalizationOfEmbedding k Y pY D A).isoZero.hom
      (AlgebraicGeometry.Scheme.Hom.ker D.emb) _ ?_
    rw [hcomap, ← hB]
    exact hxsupp
  have hnogen : ∀ y, y ⤳ ((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ
      → y = ((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ :=
    fun y hy => eq_of_specializes_of_isField_stalk_consolidated342 _ hfield y hy
  have hcomp := closure_singleton_mem_irreducibleComponents_consolidated342
    ((principalizationOfEmbedding k Y pY D A).isoZero.hom.base (((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ))
    (eq_of_specializes_iso_hom_consolidated342 (principalizationOfEmbedding k Y pY D A).isoZero
      (((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ) hnogen)
  exact D.nonzeroOnComponents_ker _ hcomp
    (closure_minimal (Set.singleton_subset_iff.mpr hz)
      (AlgebraicGeometry.Scheme.Hom.ker D.emb).support.2)

private theorem agreesWithComponentsOrderOne_zero_consolidated342 :
    AgreesWithComponentsOrderOne D A 0 := by
  classical
  intro C hC ξ hξ hCcl
  have : IsLocallyNoetherian ((principalizationOfEmbedding k Y pY D A).schemeAt 0) :=
    ((D.toEmbeddedBlowupSequence A).isNoetherian_schemeAt 0 (Nat.zero_le _)).toIsLocallyNoetherian
  have : TopologicalSpace.NoetherianSpace ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) :=
    (D.toEmbeddedBlowupSequence A).noetherianSpace_strictTransform_of_isNoetherian (isNoetherian_schemeAt_toEmbeddedBlowupSequence D A) 0
      (Nat.zero_le _)
  have hemb := (D.toEmbeddedBlowupSequence A).isClosedEmbedding_strictTransformι 0
  have hclr : IsClosed (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base) := hemb.isClosed_range
  have hid0 := principalizationOfEmbedding_ideal_zero_eq_vanishingIdeal D A hclr
  set Bad : Set ↥((D.toEmbeddedBlowupSequence A).schemeAt 0) :=
    ⋃ C'' ∈ (irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) \ {C}),
      ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C'' with hBaddef
  have hfin : (irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) \ {C}).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset Set.sdiff_subset
  have hBadcl : IsClosed Bad := by
    rw [hBaddef]
    exact hfin.isClosed_biUnion (fun C'' hC'' =>
      hemb.isClosedMap _ (isClosed_of_mem_irreducibleComponents C'' hC''.1))
  have hxU : ((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ ∈ Badᶜ := by
    intro hmem
    rw [hBaddef] at hmem
    obtain ⟨C'', hC''D, hxim⟩ := Set.mem_iUnion₂.mp hmem
    obtain ⟨z, hzC'', hz⟩ := hxim
    have hzξ : z = ξ := hemb.injective hz
    subst hzξ
    have hsub : C ⊆ C'' := by
      rw [← hξ.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr hzC'')
        (isClosed_of_mem_irreducibleComponents C'' hC''D.1)
    exact hC''D.2 (subset_antisymm (hC.2 hC''D.1.1 hsub) hsub)
  have hinter : (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base) ∩ Badᶜ
      = (⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C) ∩ Badᶜ := by
    ext y
    constructor
    · rintro ⟨⟨z, rfl⟩, hy⟩
      refine ⟨?_, hy⟩
      by_cases hz : z ∈ C
      · exact ⟨z, hz, rfl⟩
      · refine absurd ?_ hy
        rw [hBaddef]
        refine Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents z, ?_⟩
          ⟨z, mem_irreducibleComponent, rfl⟩
        intro h
        exact hz (h ▸ mem_irreducibleComponent)
    · rintro ⟨⟨z, hzC, rfl⟩, hy⟩
      exact ⟨⟨z, rfl⟩, hy⟩
  have hgen : IsGenericPoint (((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ)
      (⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C) :=
    FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding hemb hξ
  have hmax : Maximal (fun s => IsIrreducible s ∧
      s ⊆ (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base))
      (⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C) := by
    constructor
    · exact ⟨hC.1.image _ hemb.continuous.continuousOn, Set.image_subset_range _ _⟩
    · rintro b ⟨hbirr, hbr⟩ hsub y hy
      have hpre : IsIrreducible (⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ⁻¹' b) :=
        FunctorialResolution.EmbeddedResolution.isIrreducible_preimage_of_isEmbedding hemb.isEmbedding hbirr hbr
      have hCsub : C ⊆ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ⁻¹' b :=
        fun z hz => hsub ⟨z, hz, rfl⟩
      have hle := hC.2 hpre hCsub
      obtain ⟨z, rfl⟩ := hbr hy
      exact ⟨z, hle hy, rfl⟩
  have hfield := not_isField_stalk_strictTransformι_zero_consolidated342 D A ξ
  refine ⟨?_, ?_⟩
  · rw [hid0]
    exact agreeNear_vanishingIdeal_of_inter_eq _ _ ⟨Badᶜ, hBadcl.isOpen_compl⟩ _ hxU hinter
  · rw [hid0]
    exact FunctorialResolution.EmbeddedResolution.orderAt_vanishingIdeal_eq_one_of_not_isField _ _ _ hmax hgen hfield

private theorem agreesWithComponentsOrderOne_succ_consolidated342 (i : ℕ) (hi : i + 1 ≤ (D.toEmbeddedBlowupSequence A).length) (ih : AgreesWithComponentsOrderOne D A i) :
    AgreesWithComponentsOrderOne D A (i + 1) := by
  classical
  intro C hC η hηgen hCcl
  have hN := isNoetherian_schemeAt_toEmbeddedBlowupSequence D A
  have hi' : i < (D.toEmbeddedBlowupSequence A).length := Nat.lt_of_succ_le hi
  have hilt : i < (principalizationOfEmbedding k Y pY D A).length := hi'
  obtain ⟨C', hC'm, hη', hfr⟩ :=
    (D.toEmbeddedBlowupSequence A).exists_irreducibleComponent_isGenericPoint_strictTransformMap hN i hi' C hC η hηgen
  have hC'cl : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C') :=
    ((D.toEmbeddedBlowupSequence A).isClosedEmbedding_strictTransformι i).isClosedMap _
      (isClosed_of_mem_irreducibleComponents C' hC'm)
  obtain ⟨hag, hord⟩ := ih C' hC'm _ hη' hC'cl
  obtain ⟨V, hxV, hVeq⟩ := (agreeNear_iff _ _ _).mp hag
  obtain ⟨V', hV'⟩ : ∃ V' : ((D.toEmbeddedBlowupSequence A).schemeAt i).Opens, V' = V := ⟨V, rfl⟩
  have hkey : ((D.toEmbeddedBlowupSequence A).strictTransformι i).base (((D.toEmbeddedBlowupSequence A).strictTransformMap i).base η)
      = ((D.toEmbeddedBlowupSequence A).blowdown i).base (((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η) := by
    have h : ((D.toEmbeddedBlowupSequence A).strictTransformMap i ≫ (D.toEmbeddedBlowupSequence A).strictTransformι i).base η
        = ((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1) ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base η := by
      rw [(D.toEmbeddedBlowupSequence A).strictTransformMap_comp_strictTransformι i]
    simpa using h
  have hnot :=
    (D.toEmbeddedBlowupSequence A).notMem_ambientCenter_support_of_isGenericPoint i C' hC'm hfr _ hη'
  have hxV' : ((D.toEmbeddedBlowupSequence A).strictTransformι i).base (((D.toEmbeddedBlowupSequence A).strictTransformMap i).base η)
      ∈ V' := by
    rw [hV']; exact hxV
  have hV'eq : ((principalizationOfEmbedding k Y pY D A).ideal i).comap V'.ι
      = (Scheme.IdealSheafData.vanishingIdeal
          (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ :
            TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap V'.ι := by
    rw [hV']; exact hVeq
  obtain ⟨U, hUdef⟩ : ∃ U : ((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)).Opens,
      U = (TopologicalSpace.Opens.map ((D.toEmbeddedBlowupSequence A).blowdown i).base).obj
        (V' ⊓ (D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i) := ⟨_, rfl⟩
  have hUsub : (U : Set ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1))) ⊆
      ⇑((D.toEmbeddedBlowupSequence A).blowdown i).base ⁻¹'
        (((D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i : ((D.toEmbeddedBlowupSequence A).schemeAt i).Opens) :
          Set ↥((D.toEmbeddedBlowupSequence A).schemeAt i)) := by
    rw [hUdef]
    intro y hy
    exact hy.2
  have hmemU : ∀ y : ↥U, ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base y) ∉
      (((D.toEmbeddedBlowupSequence A).ambientCenter i).support :
        Set ↥((D.toEmbeddedBlowupSequence A).schemeAt i)) := by
    intro y
    exact hUsub y.2
  have hxU : ((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η ∈ U := by
    rw [hUdef]
    have h1 : ((D.toEmbeddedBlowupSequence A).blowdown i).base
        (((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η) ∈ V' := by
      rw [← hkey]; exact hxV'
    have h2 : ((D.toEmbeddedBlowupSequence A).blowdown i).base
        (((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η)
        ∈ (D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i := by
      rw [← hkey]; exact hnot
    exact ⟨h1, h2⟩
  have : IsOpenImmersion (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) :=
    EmbeddedBlowupSequence.isOpenImmersion_ι_comp_blowdown (D.toEmbeddedBlowupSequence A) i hi' U hUsub
  have hexc : ((principalizationOfEmbedding k Y pY D A).exceptionalIdeal i).comap U.ι = ⊤ := by
    refine FunctorialResolution.EmbeddedResolution.comap_ι_eq_top_of_disjoint _ _ ?_
    rw [Set.disjoint_left]
    intro y hy hmem
    rw [(principalizationOfEmbedding k Y pY D A).exceptionalIdeal_eq i] at hmem
    exact absurd (mem_support_of_mem_support_comap
      ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i) _ y hmem) (hUsub hy)
  have hJ : ((principalizationOfEmbedding k Y pY D A).ideal (i + 1)).comap U.ι
      = ((principalizationOfEmbedding k Y pY D A).ideal i).comap
          (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) :=
    comap_eq_comap_comp_of_mul_eq _ U _ _ _
      ((principalizationOfEmbedding k Y pY D A).ideal_succ i hilt) hexc
  have hle : U ≤ (TopologicalSpace.Opens.map ((D.toEmbeddedBlowupSequence A).blowdown i).base).obj V' := by
    rw [hUdef]
    intro y hy
    exact hy.1
  have hcomapφ : ((principalizationOfEmbedding k Y pY D A).ideal i).comap
        (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i)
      = (Scheme.IdealSheafData.vanishingIdeal
          (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ :
            TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap
          (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) :=
    AlgebraicGeometry.Scheme.IdealSheafData.comap_ι_comp_eq_of_comap_ι_eq
      ((D.toEmbeddedBlowupSequence A).blowdown i) V' U hle _ _ hV'eq
  have hLHS : (Scheme.IdealSheafData.vanishingIdeal
        (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ :
          TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap
        (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i)
      = Scheme.IdealSheafData.vanishingIdeal
          (FunctorialResolution.EmbeddedResolution.closedPreimage U.ι
            (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C, hCcl⟩ :
              TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)))) := by
    refine FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq
      (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) _ _ ?_
    ext y
    have hcb := comp_base_apply_consolidated342 U.ι ((D.toEmbeddedBlowupSequence A).blowdown i) y
    have hiff := EmbeddedBlowupSequence.mem_image_strictTransformι_iff_of_notMem_ambientCenter
      (D.toEmbeddedBlowupSequence A) hN i hi' C η hηgen C' hη' (U.ι.base y) (hmemU y)
    constructor
    · intro hy
      have hy1 : U.ι.base y ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C := hy
      have hy2 : ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base y)
          ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := hiff.mpr hy1
      have hy3 : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base y
          ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := by
        rw [hcb]; exact hy2
      exact hy3
    · intro hy
      have hy1 : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base y
          ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := hy
      have hy2 : ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base y)
          ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := by
        rw [← hcb]; exact hy1
      exact hiff.mp hy2
  refine ⟨(agreeNear_iff _ _ _).mpr ⟨U, hxU, ?_⟩, ?_⟩
  · exact hJ.trans (hcomapφ.trans (hLHS.trans
      (FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion U.ι
        (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C, hCcl⟩ :
          TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)))).symm))
  · have e1 := FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isOpenImmersion U.ι
      ((principalizationOfEmbedding k Y pY D A).ideal (i + 1))
      (⟨((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η, hxU⟩ : ↥U)
    have e2 := FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isOpenImmersion
      (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) ((principalizationOfEmbedding k Y pY D A).ideal i)
      (⟨((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η, hxU⟩ : ↥U)
    have hφp : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base
        (⟨((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η, hxU⟩ : ↥U)
        = ((D.toEmbeddedBlowupSequence A).strictTransformι i).base (((D.toEmbeddedBlowupSequence A).strictTransformMap i).base η) := by
      rw [comp_base_apply_consolidated342 U.ι ((D.toEmbeddedBlowupSequence A).blowdown i)
        (⟨((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η, hxU⟩ : ↥U)]
      exact hkey.symm
    calc FunctorialResolution.EmbeddedResolution.orderAt ((principalizationOfEmbedding k Y pY D A).ideal (i + 1))
          (((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η)
        = FunctorialResolution.EmbeddedResolution.orderAt (((principalizationOfEmbedding k Y pY D A).ideal (i + 1)).comap U.ι)
            (⟨((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η, hxU⟩ : ↥U) := e1.symm
      _ = FunctorialResolution.EmbeddedResolution.orderAt (((principalizationOfEmbedding k Y pY D A).ideal i).comap
            (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i))
            (⟨((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η, hxU⟩ : ↥U) := by rw [hJ]
      _ = FunctorialResolution.EmbeddedResolution.orderAt ((principalizationOfEmbedding k Y pY D A).ideal i)
            ((U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base
              (⟨((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η, hxU⟩ : ↥U)) := e2
      _ = FunctorialResolution.EmbeddedResolution.orderAt ((principalizationOfEmbedding k Y pY D A).ideal i)
            (((D.toEmbeddedBlowupSequence A).strictTransformι i).base
              (((D.toEmbeddedBlowupSequence A).strictTransformMap i).base η)) := by rw [hφp]
      _ = 1 := hord

private theorem forall_agreesWithComponentsOrderOne_consolidated342 :
    ∀ i : ℕ, i ≤ (D.toEmbeddedBlowupSequence A).length → AgreesWithComponentsOrderOne D A i := by
  intro i
  induction i with
  | zero => intro _; exact agreesWithComponentsOrderOne_zero_consolidated342 D A
  | succ i ih => intro hi; exact agreesWithComponentsOrderOne_succ_consolidated342 D A i hi (ih (Nat.le_of_succ_le hi))


end

theorem agreesWithComponentsOrderOne_of_le [IsReduced Y] (D : EmbeddingDatum k Y pY)
    (A : PrincipalizationAlgorithm.{u}) (i : ℕ) (hi : i ≤ (D.toEmbeddedBlowupSequence A).length) :
    AgreesWithComponentsOrderOne D A i :=
  forall_agreesWithComponentsOrderOne_consolidated342 D A i hi

section
variable (A : PrincipalizationAlgorithm.{u})

theorem noetherianSpace_strictTransform :
    ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      [IsAffine Y] [IsReduced Y]
      (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
      [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (i : ℕ),
      i ≤ (D.toEmbeddedBlowupSequence A).length →
        TopologicalSpace.NoetherianSpace ↥((D.toEmbeddedBlowupSequence A).strictTransform i) := by
  intro k _ _ Y _ _ pY _ _ D i hi
  exact (D.toEmbeddedBlowupSequence A).noetherianSpace_strictTransform_of_isNoetherian (isNoetherian_schemeAt_toEmbeddedBlowupSequence D A) i hi

theorem isClosedEmbedding_strictTransformι :
    ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      [IsAffine Y] [IsReduced Y]
      (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
      [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (i : ℕ),
      i ≤ (D.toEmbeddedBlowupSequence A).length →
        Topology.IsClosedEmbedding ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base := by
  intro k _ _ Y _ _ pY _ _ D i _
  exact (D.toEmbeddedBlowupSequence A).isClosedEmbedding_strictTransformι i

theorem genericPoint_notMem_boundary_support :
    ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      [IsAffine Y] [IsReduced Y]
      (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
      [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (i : ℕ),
      i ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform i),
      ∀ ξ : ↥((D.toEmbeddedBlowupSequence A).strictTransform i), IsGenericPoint ξ C →
      ∀ E ∈ (principalizationOfEmbedding k Y pY D A).boundary i,
        ((D.toEmbeddedBlowupSequence A).strictTransformι i).base ξ ∉
          (E.support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i)) := by
  intro k _ _ Y _ _ pY _ _ D i hi C hC ξ hξ E hE hx
  exact not_avoidsCenters_of_mem_boundary_support D A i hi E hE _ hx
    (EmbeddedBlowupSequence.avoidsCenters_strictTransformι_of_isGenericPoint (D.toEmbeddedBlowupSequence A)
      (isNoetherian_schemeAt_toEmbeddedBlowupSequence D A) i hi C hC ξ hξ)

theorem agreeNear_and_orderAt_eq_one_reducedVanishingAssignment :
    ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      [IsAffine Y] [IsReduced Y]
      (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
      [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (i : ℕ),
      i ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform i),
      ∀ ξ : ↥((D.toEmbeddedBlowupSequence A).strictTransform i), IsGenericPoint ξ C →
      ∀ hC : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C),
        AgreeNear ((principalizationOfEmbedding k Y pY D A).ideal i)
            (reducedVanishingAssignment ((D.toEmbeddedBlowupSequence A).schemeAt i)
              ⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C, hC⟩)
            (((D.toEmbeddedBlowupSequence A).strictTransformι i).base ξ) ∧
          orderAt ((principalizationOfEmbedding k Y pY D A).ideal i)
            (((D.toEmbeddedBlowupSequence A).strictTransformι i).base ξ) = 1 := by
  intro k _ _ Y _ _ pY _ _ D i hi C hC ξ hξ hCcl
  exact agreesWithComponentsOrderOne_of_le D A i hi C hC ξ hξ hCcl

theorem chartIsolationHypotheses_reducedVanishingAssignment :
    ChartIsolationHypotheses reducedVanishingAssignment A :=
  { noetherianSpace_alive := noetherianSpace_strictTransform A
    isClosedEmbedding_aliveι := isClosedEmbedding_strictTransformι A
    generic_not_mem_member := genericPoint_notMem_boundary_support A
    agreeNear_orderAt_eq_one := agreeNear_and_orderAt_eq_one_reducedVanishingAssignment A }


end

theorem not_image_irreducibleComponent_subset_boundary_support [IsReduced Y]
    (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) (i : ℕ) (hi : i ≤ (D.toEmbeddedBlowupSequence A).length)
    (C : Set ↥((D.toEmbeddedBlowupSequence A).strictTransform i))
    (hC : C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform i))
    (E : ((principalizationOfEmbedding k Y pY D A).schemeAt i).IdealSheafData)
    (hE : E ∈ (principalizationOfEmbedding k Y pY D A).boundary i) :
    ¬ (⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C ⊆
        (E.support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i))) := by
  intro hsub
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
  exact genericPoint_notMem_boundary_support A k Y pY D i hi C hC ξ hξ E hE
    (hsub ⟨ξ, hξ.mem, rfl⟩)

end OpenImmersionRestriction

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineDetachedConditions
section

open TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

theorem range_base_subschemeι {X : Scheme.{u}} (I : X.IdealSheafData) :
    Set.range ⇑I.subschemeι.base = ((I.support : TopologicalSpace.Closeds ↥X) : Set ↥X) := by
  rw [Scheme.IdealSheafData.range_subschemeι]

private theorem mem_of_mem_support_vanishingIdeal_consolidated372 {W : Scheme.{u}} (Z : TopologicalSpace.Closeds ↥W)
    (x : ↥W) (hx : x ∈ (Scheme.IdealSheafData.vanishingIdeal Z).support) : x ∈ (Z : Set ↥W) := by
  have h2 : x ∈ (((Scheme.IdealSheafData.vanishingIdeal Z).support :
      TopologicalSpace.Closeds ↥W) : Set ↥W) := hx
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at h2
  exact h2

private theorem exists_iso_subscheme_vanishingIdeal_of_closure_range_consolidated372 {A W : Scheme.{u}} (f : A ⟶ W)
    [IsClosedImmersion f] [IsReduced A]
    (K : TopologicalSpace.Closeds ↥W)
    (hK : (K : Set ↥W) = closure (Set.range ⇑f.base))
    (hle : Scheme.Hom.ker f ≤ Scheme.IdealSheafData.vanishingIdeal K) :
    ∃ e : (Scheme.IdealSheafData.vanishingIdeal K).subscheme ≅ A,
      e.hom ≫ f = (Scheme.IdealSheafData.vanishingIdeal K).subschemeι := by
  have hrange : Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal K).subschemeι.base
      = (K : Set ↥W) := by
    rw [range_base_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hle' : Scheme.Hom.ker f
      ≤ Scheme.Hom.ker (Scheme.IdealSheafData.vanishingIdeal K).subschemeι := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact hle
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (Scheme.IdealSheafData.vanishingIdeal K).subscheme ⟶ A,
      ψ ≫ f = (Scheme.IdealSheafData.vanishingIdeal K).subschemeι :=
    ⟨IsClosedImmersion.lift f (Scheme.IdealSheafData.vanishingIdeal K).subschemeι hle',
      IsClosedImmersion.lift_fac _ _ hle'⟩
  have hψbase : ∀ x, f.base (ψ.base x)
      = (Scheme.IdealSheafData.vanishingIdeal K).subschemeι.base x := by
    intro x
    show (ψ ≫ f).base x = (Scheme.IdealSheafData.vanishingIdeal K).subschemeι.base x
    rw [hψ]
  have hinj : Function.Injective ⇑f.base := f.isEmbedding.injective
  have hsurj : Function.Surjective ⇑ψ.base := by
    intro a
    have h1 : f.base a ∈ (K : Set ↥W) := by
      rw [hK]
      exact subset_closure (Set.mem_range_self a)
    rw [← hrange] at h1
    obtain ⟨y, hy⟩ := h1
    exact ⟨y, hinj (by rw [hψbase y]; exact hy)⟩
  have hru : Set.range ⇑ψ.base = (Set.univ : Set ↥A) := hsurj.range_eq
  have : IsPreimmersion (ψ ≫ f) := by rw [hψ]; infer_instance
  have : IsPreimmersion ψ := IsPreimmersion.of_comp ψ f
  have : IsClosedImmersion ψ :=
    IsClosedImmersion.of_isPreimmersion ψ (by rw [hru]; exact isClosed_univ)
  have hker : Scheme.Hom.ker ψ = ⊥ := by
    rw [← Scheme.IdealSheafData.support_eq_top_iff]
    refine TopologicalSpace.Closeds.ext ?_
    rw [Scheme.Hom.support_ker, hru, closure_univ]
    simp
  have : IsIso ψ := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  exact ⟨asIso ψ, hψ⟩

theorem exists_iso_of_range_base_eq {A B W : Scheme.{u}} (f : A ⟶ W) (g : B ⟶ W)
    [IsClosedImmersion f] [IsClosedImmersion g]
    [IsReduced A] [IsReduced B]
    (h : Set.range ⇑f.base = Set.range ⇑g.base) :
    ∃ e : A ≅ B, e.hom ≫ g = f := by
  have hA : ((Scheme.Hom.ker f).support : Set ↥W) = closure (Set.range ⇑f.base) :=
    Scheme.Hom.support_ker f
  have hB : ((Scheme.Hom.ker f).support : Set ↥W) = closure (Set.range ⇑g.base) := by
    rw [Scheme.Hom.support_ker f, h]
  have hKeq : (Scheme.Hom.ker g).support = (Scheme.Hom.ker f).support :=
    TopologicalSpace.Closeds.ext (by rw [Scheme.Hom.support_ker g, hB])
  obtain ⟨e₁, he₁⟩ := exists_iso_subscheme_vanishingIdeal_of_closure_range_consolidated372 f (Scheme.Hom.ker f).support hA
    (by rw [Scheme.IdealSheafData.vanishingIdeal_support]
        exact Scheme.IdealSheafData.le_radical _)
  obtain ⟨e₂, he₂⟩ := exists_iso_subscheme_vanishingIdeal_of_closure_range_consolidated372 g (Scheme.Hom.ker f).support hB
    (by rw [← hKeq, Scheme.IdealSheafData.vanishingIdeal_support]
        exact Scheme.IdealSheafData.le_radical _)
  refine ⟨e₁.symm ≪≫ e₂, ?_⟩
  have hcomp : (e₁.symm ≪≫ e₂).hom = e₁.inv ≫ e₂.hom := rfl
  rw [hcomp, Category.assoc, he₂, ← he₁, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem isNoetherian_ambientLevel_ofAffine (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [IsAffine Y] (pY : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType pY] :
    ∀ i ≤ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength,
      IsNoetherian ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i) := by
  intro i hi
  have h := EmbeddedBlowupSequence.isNoetherian_schemeAt
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence i hi
  rw [AffineSpacePrincipalizationData.toEmbeddedBlowupSequence_schemeAt] at h
  exact h

section
variable {X : Scheme.{u}}

private theorem mem_support_of_le_consolidated372 {I J : X.IdealSheafData} (h : I ≤ J)
    (x : ↥X) (hx : x ∈ J.support) : x ∈ I.support :=
  (mem_orderAtLeastLocus_one_iff I x).mp
    (orderAtLeastLocus_subset_of_le_ideal h 1 ((mem_orderAtLeastLocus_one_iff J x).mpr hx))

private theorem mem_support_mul_consolidated372 (I J : X.IdealSheafData) (x : ↥X) :
    x ∈ (I * J).support ↔ x ∈ I.support ∨ x ∈ J.support := by
  have h : (((I * J).support : TopologicalSpace.Closeds ↥X) : Set ↥X)
      = ((I.support : TopologicalSpace.Closeds ↥X) : Set ↥X)
        ∪ ((J.support : TopologicalSpace.Closeds ↥X) : Set ↥X) := by
    simp
  constructor
  · intro hx
    have h2 : x ∈ (((I * J).support : TopologicalSpace.Closeds ↥X) : Set ↥X) := hx
    rw [h] at h2
    exact h2
  · intro hx
    have h2 : x ∈ (((I * J).support : TopologicalSpace.Closeds ↥X) : Set ↥X) := by
      rw [h]
      exact hx
    exact h2


end

private theorem mem_support_comap_consolidated372 {X Z : Scheme.{u}} (f : X ⟶ Z) (I : Z.IdealSheafData) (x : ↥X) :
    x ∈ (I.comap f).support ↔ ⇑f.base x ∈ I.support := by
  constructor
  · intro hx
    have h : x ∈ ((((I.comap f)).support : TopologicalSpace.Closeds ↥X) : Set ↥X) := hx
    rw [support_comap_eq] at h
    exact h
  · intro hx
    have h : x ∈ ((((I.comap f)).support : TopologicalSpace.Closeds ↥X) : Set ↥X) := by
      rw [support_comap_eq]
      exact hx
    exact h

private theorem exists_mem_list_subset_of_isIrreducible_consolidated372 {α : Type*} [TopologicalSpace α] {ι : Type*}
    {s : Set α} (hs : IsIrreducible s) (g : ι → Set α) :
    ∀ L : List ι, (∀ t ∈ L, IsClosed (g t)) → s ⊆ (⋃ t ∈ L, g t) → ∃ t ∈ L, s ⊆ g t := by
  intro L
  induction L with
  | nil =>
      intro _ hsub
      obtain ⟨x, hx⟩ := hs.nonempty
      obtain ⟨t, ht, -⟩ := Set.mem_iUnion₂.mp (hsub hx)
      simp at ht
  | cons a L ih =>
      intro hcl hsub
      have hsub' : s ⊆ g a ∪ ⋃ t ∈ L, g t := by
        intro z hz
        obtain ⟨t, ht, hzt⟩ := Set.mem_iUnion₂.mp (hsub hz)
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact Or.inl hzt
        · exact Or.inr (Set.mem_biUnion ht' hzt)
      have hacl : IsClosed (g a) := hcl a (List.mem_cons.mpr (Or.inl rfl))
      have hUcl : IsClosed (⋃ t ∈ L, g t) :=
        Set.Finite.isClosed_biUnion L.finite_toSet
          (fun t ht => hcl t (List.mem_cons.mpr (Or.inr ht)))
      rcases isPreirreducible_iff_isClosed_union_isClosed.mp hs.2 _ _ hacl hUcl hsub' with h | h
      · exact ⟨a, List.mem_cons.mpr (Or.inl rfl), h⟩
      · obtain ⟨t, ht, hts⟩ := ih (fun t ht => hcl t (List.mem_cons.mpr (Or.inr ht))) h
        exact ⟨t, List.mem_cons.mpr (Or.inr ht), hts⟩

section
variable {X' X : Scheme.{u}}

private theorem quasiCompact_strictTransformImmersion_consolidated372 [TopologicalSpace.NoetherianSpace ↥X'] (π : X' ⟶ X) (Z J : X.IdealSheafData) :
    QuasiCompact (Blowup.strictTransformImmersion π Z J) := by
  have : AlgebraicGeometry.IsPreimmersion (Blowup.strictTransformImmersion π Z J) := by
    rw [Blowup.strictTransformImmersion_eq]
    infer_instance
  refine ⟨fun U _ _ => ?_⟩
  refine ((Blowup.strictTransformImmersion π Z J).isEmbedding.isInducing.isCompact_iff).mpr ?_
  exact TopologicalSpace.NoetherianSpace.isCompact _

private theorem mem_support_strictTransform_consolidated372 (π : X' ⟶ X)
    (Z J : X.IdealSheafData)
    (hqc : QuasiCompact (Blowup.strictTransformImmersion π Z J)) (x : ↥X')
    (h1 : ⇑π.base x ∈ J.support) (h2 : ⇑π.base x ∉ Z.support) :
    x ∈ (Blowup.strictTransform π Z J).support := by
  have := hqc
  have hxr : x ∈ Set.range ⇑(J.comap π).subschemeι.base := by
    rw [range_base_subschemeι]
    exact (mem_support_comap_consolidated372 π J x).mpr h1
  obtain ⟨y, hy⟩ := hxr
  have h3 : ⇑(J.comap π).subschemeι.base y ∉ (Z.comap π).support := by
    intro hc
    have h5 := (mem_support_comap_consolidated372 π Z _).mp hc
    rw [hy] at h5
    exact h2 h5
  have hyo : y ∈ Blowup.strictTransformOpens π Z J := by
    rw [Blowup.strictTransformOpens_eq]
    have h4 : ⇑(J.comap π).subschemeι.base y
        ∉ ((((Z.comap π)).support : TopologicalSpace.Closeds ↥X') : Set ↥X') := h3
    exact h4
  have hyr : y ∈ Set.range ⇑(Blowup.strictTransformOpens π Z J).ι.base := by
    have hrι : Set.range ⇑(Blowup.strictTransformOpens π Z J).ι.base
        = ((Blowup.strictTransformOpens π Z J : (J.comap π).subscheme.Opens) :
            Set ↥(J.comap π).subscheme) := (Blowup.strictTransformOpens π Z J).range_ι
    rw [hrι]
    exact hyo
  obtain ⟨y', hy'⟩ := hyr
  have hcomp : ⇑(Blowup.strictTransformImmersion π Z J).base y' = x := by
    rw [Blowup.strictTransformImmersion_eq]
    show ⇑(J.comap π).subschemeι.base (⇑(Blowup.strictTransformOpens π Z J).ι.base y') = x
    rw [hy', hy]
  have hfin : x ∈ ((((Blowup.strictTransform π Z J)).support : TopologicalSpace.Closeds ↥X')
      : Set ↥X') := by
    rw [Blowup.strictTransform_eq_ker, Scheme.Hom.support_ker]
    exact subset_closure ⟨y', hcomp⟩
  exact hfin


end

private def principalizationSequenceIdeal_consolidated372 {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) (j : ℕ) :
    (S.ambientLevel j).IdealSheafData :=
  S.principalizationSequence.ideal j

section
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY)

private theorem exceptionalIdeal_mul_weakTransform_succ_consolidated372 (j : ℕ)
    (hj : j < S.ambientLength) :
    Blowup.exceptionalIdeal (S.ambientBlowupMorphism j) (S.ambientCenter j) * principalizationSequenceIdeal_consolidated372 S (j + 1)
      = (principalizationSequenceIdeal_consolidated372 S j).comap (S.ambientBlowupMorphism j) :=
  S.principalizationSequence.ideal_succ j hj

private theorem weakTransform_le_ambientCenter_consolidated372 (j : ℕ)
    (hj : j < S.ambientLength) : principalizationSequenceIdeal_consolidated372 S j ≤ S.ambientCenter j :=
  (vanishesAlong_iff_le _ _).mp (S.principalizationSequence.ideal_vanishes j hj)

private theorem boundary_succ_eq_consolidated372 (j : ℕ)
    (hj : j < S.ambientLength) :
    S.boundary (j + 1)
      = List.map (Blowup.strictTransform (S.ambientBlowupMorphism j) (S.ambientCenter j)) (S.boundary j)
        ++ [Blowup.exceptionalIdeal (S.ambientBlowupMorphism j) (S.ambientCenter j)] :=
  S.principalizationSequence.boundary_succ j hj

private theorem mem_range_strictTransformι_iff_consolidated372 (j : ℕ)
    (x : ↥(S.ambientLevel j)) :
    x ∈ Set.range ⇑(S.strictTransformι j).base ↔ x ∈ (S.strictTransformIdeal j).support := by
  have h : Set.range ⇑(S.strictTransformι j).base
      = (((S.strictTransformIdeal j).support : TopologicalSpace.Closeds ↥(S.ambientLevel j))
          : Set ↥(S.ambientLevel j)) := by
    rw [S.strictTransformι_eq_subschemeι j]
    exact range_base_subschemeι _
  constructor
  · intro hx
    have h2 : x ∈ Set.range ⇑(S.strictTransformι j).base := hx
    rw [h] at h2
    exact h2
  · intro hx
    have h2 : x ∈ (((S.strictTransformIdeal j).support : TopologicalSpace.Closeds ↥(S.ambientLevel j))
        : Set ↥(S.ambientLevel j)) := hx
    rw [← h] at h2
    exact h2

private theorem support_weakTransform_subset_range_or_boundary_consolidated372 (hN : ∀ j ≤ S.ambientLength, IsNoetherian (S.ambientLevel j))
    (hbase : ∀ x : ↥(S.ambientLevel 0), x ∈ (principalizationSequenceIdeal_consolidated372 S 0).support →
      x ∈ Set.range ⇑(S.strictTransformι 0).base) :
    ∀ j ≤ S.ambientLength, ∀ x : ↥(S.ambientLevel j), x ∈ (principalizationSequenceIdeal_consolidated372 S j).support →
      x ∈ Set.range ⇑(S.strictTransformι j).base ∨ ∃ E ∈ S.boundary j, x ∈ E.support := by
  intro j
  induction j with
  | zero =>
      intro _ x hx
      exact Or.inl (hbase x hx)
  | succ j ih =>
      intro hj x hx
      have hjlt : j < S.ambientLength := hj
      have hNs : IsNoetherian (S.ambientLevel (j + 1)) := hN (j + 1) hj
      have hNSs : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel (j + 1)) := inferInstance
      have hxp : x ∈ (Blowup.exceptionalIdeal (S.ambientBlowupMorphism j) (S.ambientCenter j)
          * principalizationSequenceIdeal_consolidated372 S (j + 1)).support :=
        (mem_support_mul_consolidated372 (Blowup.exceptionalIdeal (S.ambientBlowupMorphism j) (S.ambientCenter j))
          (principalizationSequenceIdeal_consolidated372 S (j + 1)) x).mpr (Or.inr hx)
      rw [exceptionalIdeal_mul_weakTransform_succ_consolidated372 S j hjlt] at hxp
      have hx1 : ⇑(S.ambientBlowupMorphism j).base x ∈ (principalizationSequenceIdeal_consolidated372 S j).support :=
        (mem_support_comap_consolidated372 (S.ambientBlowupMorphism j) (principalizationSequenceIdeal_consolidated372 S j) x).mp hxp
      by_cases hexc : x ∈ (Blowup.exceptionalIdeal (S.ambientBlowupMorphism j) (S.ambientCenter j)).support
      · have hmem1 : Blowup.exceptionalIdeal (S.ambientBlowupMorphism j) (S.ambientCenter j) ∈ S.boundary (j + 1) := by
          rw [boundary_succ_eq_consolidated372 S j hjlt]
          simp
        exact Or.inr ⟨_, hmem1, hexc⟩
      · have hnc : ⇑(S.ambientBlowupMorphism j).base x ∉ (S.ambientCenter j).support := by
          intro hc
          apply hexc
          have h6 : x ∈ ((S.ambientCenter j).comap (S.ambientBlowupMorphism j)).support :=
            (mem_support_comap_consolidated372 (S.ambientBlowupMorphism j) (S.ambientCenter j) x).mpr hc
          rw [Blowup.exceptionalIdeal_eq_comap]
          exact h6
        rcases ih (le_of_lt hjlt) (⇑(S.ambientBlowupMorphism j).base x) hx1 with hA | ⟨E, hE, hxE⟩
        · refine Or.inl ?_
          have h1 : ⇑(S.ambientBlowupMorphism j).base x ∈ (S.strictTransformIdeal j).support :=
            (mem_range_strictTransformι_iff_consolidated372 S j _).mp hA
          have h2 := mem_support_strictTransform_consolidated372 (S.ambientBlowupMorphism j) (S.ambientCenter j)
            (S.strictTransformIdeal j)
            (quasiCompact_strictTransformImmersion_consolidated372 (S.ambientBlowupMorphism j) (S.ambientCenter j)
              (S.strictTransformIdeal j)) x h1 hnc
          refine (mem_range_strictTransformι_iff_consolidated372 S (j + 1) x).mpr ?_
          rw [S.strictTransformIdeal_succ_eq_strictTransform j]
          exact h2
        · have hmem1 : Blowup.strictTransform (S.ambientBlowupMorphism j) (S.ambientCenter j) E
              ∈ S.boundary (j + 1) := by
            rw [boundary_succ_eq_consolidated372 S j hjlt]
            simp only [List.mem_append, List.mem_map]
            exact Or.inl ⟨E, hE, rfl⟩
          have hmem2 := mem_support_strictTransform_consolidated372 (S.ambientBlowupMorphism j) (S.ambientCenter j) E
            (quasiCompact_strictTransformImmersion_consolidated372 (S.ambientBlowupMorphism j) (S.ambientCenter j) E) x hxE hnc
          exact Or.inr ⟨_, hmem1, hmem2⟩

private theorem detachedClopenInCenter_of_isNoetherian_of_support_consolidated372 (hN : ∀ j ≤ S.ambientLength, IsNoetherian (S.ambientLevel j))
    (hsupp : ∀ j ≤ S.ambientLength, ∀ x : ↥(S.ambientLevel j), x ∈ (principalizationSequenceIdeal_consolidated372 S j).support →
      x ∈ Set.range ⇑(S.strictTransformι j).base ∨ ∃ E ∈ S.boundary j, x ∈ E.support)
    (hmk : ∀ j ≤ S.ambientLength, ∀ C ∈ irreducibleComponents ↥(S.strictTransform j), ∀ E ∈ S.boundary j,
      ¬ (⇑(S.strictTransformι j).base '' C ⊆
        ((E.support : TopologicalSpace.Closeds ↥(S.ambientLevel j)) : Set ↥(S.ambientLevel j)))) :
    S.DetachedClopenInCenter := by
  intro i hi
  have hNi : IsNoetherian (S.ambientLevel i) := hN i hi.le
  have hNSi : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel i) := inferInstance
  have hnoeth : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i) :=
    S.noetherianSpace_strictTransform_of_ambientLevel i hNSi
  have hsmW : Smooth
      ((S.ambientCenter i).subschemeι ≫ S.schemeAtToSpec i) := S.principalizationSequence.smooth_center_subschemeι i hi
  have hredW : IsReduced (S.ambientCenter i).subscheme :=
    smooth_isReduced ((S.ambientCenter i).subschemeι ≫ S.schemeAtToSpec i) hsmW
  have hNW : TopologicalSpace.NoetherianSpace ↥(S.ambientCenter i).subscheme := inferInstance
  have hrangeA : Set.range ⇑(S.strictTransformι i).base
      = (((S.strictTransformIdeal i).support : TopologicalSpace.Closeds ↥(S.ambientLevel i))
          : Set ↥(S.ambientLevel i)) := by
    rw [S.strictTransformι_eq_subschemeι i]
    exact range_base_subschemeι _
  have hrangeC : Set.range ⇑((S.ambientCenter i).subschemeι).base
      = (((S.ambientCenter i).support : TopologicalSpace.Closeds ↥(S.ambientLevel i))
          : Set ↥(S.ambientLevel i)) :=
    range_base_subschemeι _
  have hdom : ∀ x : ↥(S.ambientCenter i).subscheme,
      IsDomain (((S.ambientCenter i).subscheme).presheaf.stalk x) := fun x =>
    smooth_isDomain_stalk ((S.ambientCenter i).subschemeι ≫ S.schemeAtToSpec i) hsmW x
  have hsubr : ⇑(S.strictTransformι i).base '' S.discardedLocus i
      ⊆ Set.range ⇑((S.ambientCenter i).subschemeι).base := by
    rw [hrangeC]
    exact S.image_discardedLocus_subset_support i
  have hRcl : IsClosed (Set.range ⇑(S.strictTransformι i).base ∪
      ⋃ E ∈ S.boundary i,
        ((E.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) : Set ↥(S.ambientLevel i))) := by
    refine IsClosed.union ?_ ?_
    · rw [hrangeA]
      exact ((S.strictTransformIdeal i).support).2
    · exact Set.Finite.isClosed_biUnion (S.boundary i).finite_toSet (fun E _ => (E.support).2)
  have hcomp : ∀ C ∈ S.discardedComponents i,
      ⇑((S.ambientCenter i).subschemeι).base ⁻¹' (⇑(S.strictTransformι i).base '' C)
        ∈ irreducibleComponents ↥(S.ambientCenter i).subscheme := by
    intro C hC
    obtain ⟨hCcomp, hCsub⟩ := (S.mem_discardedComponents_iff i C).mp hC
    have himg : IsIrreducible (⇑(S.strictTransformι i).base '' C) :=
      hCcomp.1.image _ ((S.strictTransformι i).continuous).continuousOn
    have hsubrC : ⇑(S.strictTransformι i).base '' C
        ⊆ Set.range ⇑((S.ambientCenter i).subschemeι).base := by
      rw [hrangeC]
      exact hCsub
    refine ⟨isIrreducible_preimage_of_isEmbedding
      ((S.ambientCenter i).subschemeι.isEmbedding) himg hsubrC, ?_⟩
    intro s hs hKle
    have hcimg : ⇑((S.ambientCenter i).subschemeι).base ''
        (⇑((S.ambientCenter i).subschemeι).base ⁻¹' (⇑(S.strictTransformι i).base '' C))
        = ⇑(S.strictTransformι i).base '' C := Set.image_preimage_eq_of_subset hsubrC
    have hFirr : IsIrreducible (closure (⇑((S.ambientCenter i).subschemeι).base '' s)) :=
      (hs.image _ (((S.ambientCenter i).subschemeι).continuous).continuousOn).closure
    have hCsubF : ⇑(S.strictTransformι i).base '' C
        ⊆ closure (⇑((S.ambientCenter i).subschemeι).base '' s) := by
      rw [← hcimg]
      exact (Set.image_mono hKle).trans subset_closure
    have hcsI : ⇑((S.ambientCenter i).subschemeι).base '' s
        ⊆ Set.range ⇑(S.strictTransformι i).base ∪
          ⋃ E ∈ S.boundary i,
            ((E.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) : Set ↥(S.ambientLevel i)) := by
      intro z hz
      obtain ⟨w, -, rfl⟩ := hz
      have h1 : ⇑((S.ambientCenter i).subschemeι).base w ∈ (S.ambientCenter i).support := by
        have h0 : ⇑((S.ambientCenter i).subschemeι).base w
            ∈ (((S.ambientCenter i).support : TopologicalSpace.Closeds ↥(S.ambientLevel i))
                : Set ↥(S.ambientLevel i)) := by
          rw [← hrangeC]
          exact Set.mem_range_self w
        exact h0
      have h2 : ⇑((S.ambientCenter i).subschemeι).base w ∈ (principalizationSequenceIdeal_consolidated372 S i).support :=
        mem_support_of_le_consolidated372 (weakTransform_le_ambientCenter_consolidated372 S i hi) _ h1
      rcases hsupp i hi.le _ h2 with hA | ⟨E, hE, hxE⟩
      · exact Or.inl hA
      · exact Or.inr (Set.mem_biUnion hE hxE)
    have hFsub : closure (⇑((S.ambientCenter i).subschemeι).base '' s)
        ⊆ Set.range ⇑(S.strictTransformι i).base ∪
          ⋃ E ∈ S.boundary i,
            ((E.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) : Set ↥(S.ambientLevel i)) :=
      (IsClosed.closure_subset_iff hRcl).mpr hcsI
    rcases isPreirreducible_iff_isClosed_union_isClosed.mp hFirr.2 _ _
        (by rw [hrangeA]; exact ((S.strictTransformIdeal i).support).2)
        (Set.Finite.isClosed_biUnion (S.boundary i).finite_toSet (fun E _ => (E.support).2))
        hFsub with hcase | hcase
    · have hG := hCcomp.2
        (isIrreducible_preimage_of_isEmbedding ((S.strictTransformι i).isEmbedding) hFirr hcase)
        (fun z hz => hCsubF (Set.mem_image_of_mem _ hz))
      have hclosure : closure (⇑((S.ambientCenter i).subschemeι).base '' s)
          ⊆ ⇑(S.strictTransformι i).base '' C := by
        rw [← Set.image_preimage_eq_of_subset hcase]
        exact Set.image_mono hG
      intro z hz
      exact hclosure (subset_closure (Set.mem_image_of_mem _ hz))
    · obtain ⟨E, hE, hFsubE⟩ := exists_mem_list_subset_of_isIrreducible_consolidated372 hFirr
        (fun E : (S.ambientLevel i).IdealSheafData =>
          ((E.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) : Set ↥(S.ambientLevel i)))
        (S.boundary i) (fun E _ => (E.support).2) hcase
      exact ((hmk i hi.le C hCcomp E hE) (hCsubF.trans hFsubE)).elim
  have hPreimageDiscarded : ⇑((S.ambientCenter i).subschemeι).base ⁻¹'
      (⇑(S.strictTransformι i).base '' S.discardedLocus i)
      = ⋃₀ ((fun C : Set ↥(S.strictTransform i) =>
          ⇑((S.ambientCenter i).subschemeι).base ⁻¹' (⇑(S.strictTransformι i).base '' C))
            '' S.discardedComponents i) := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, hwz⟩ := hz
      rw [S.discardedLocus_eq_sUnion_discardedComponents i] at hw
      obtain ⟨C, hC, hwC⟩ := hw
      exact ⟨_, ⟨C, hC, rfl⟩, ⟨w, hwC, hwz⟩⟩
    · intro hz
      obtain ⟨t, ⟨C, hC, rfl⟩, hzt⟩ := hz
      obtain ⟨w, hwC, hwz⟩ := hzt
      refine ⟨w, ?_, hwz⟩
      rw [S.discardedLocus_eq_sUnion_discardedComponents i]
      exact ⟨C, hC, hwC⟩
  have hopenU : IsOpen (⇑((S.ambientCenter i).subschemeι).base ⁻¹'
      (⇑(S.strictTransformι i).base '' S.discardedLocus i)) := by
    rw [hPreimageDiscarded]
    refine isOpen_sUnion_of_irreducibleComponents _ ?_
    · intro Zs hZs W hW hWnot
      obtain ⟨C, hC, rfl⟩ := hZs
      rw [Set.disjoint_left]
      intro z hz1 hz2
      have heqq := irreducibleComponents_eq_of_stalk_isDomain _ hdom (hcomp C hC) hW hz1 hz2
      refine hWnot ?_
      rw [← heqq]
      exact ⟨C, hC, rfl⟩
  have hembA : Topology.IsClosedEmbedding ⇑(S.strictTransformι i).base := by
    refine ⟨(S.strictTransformι i).isEmbedding, ?_⟩
    rw [hrangeA]
    exact ((S.strictTransformIdeal i).support).2
  have hclosedU : IsClosed (⇑((S.ambientCenter i).subschemeι).base ⁻¹'
      (⇑(S.strictTransformι i).base '' S.discardedLocus i)) :=
    (hembA.isClosedMap _ (S.isClosed_discardedLocus i)).preimage
      ((S.ambientCenter i).subschemeι).continuous
  obtain ⟨U, hUcoe⟩ : ∃ U : ((S.ambientCenter i).subscheme).Opens,
      (U : Set ↥(S.ambientCenter i).subscheme)
        = ⇑((S.ambientCenter i).subschemeι).base ⁻¹'
          (⇑(S.strictTransformι i).base '' S.discardedLocus i) :=
    ⟨⟨_, hopenU⟩, rfl⟩
  have hUcl : IsClosed ((U : Set ↥(S.ambientCenter i).subscheme)) := by
    rw [hUcoe]
    exact hclosedU
  have : IsClosedImmersion U.ι :=
    Scheme.Opens.isClosedImmersion_ι_of_isClosed U hUcl
  have : IsReduced (S.discardedIdeal i).subscheme := by
    rw [S.discardedIdeal_eq_vanishingIdeal i]
    exact Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _ _
  have hRangeDiscarded : Set.range ⇑(S.discardedι i).base = S.discardedLocus i := by
    have h1 : Set.range ⇑(S.discardedι i).base
        = (((S.discardedIdeal i).support : TopologicalSpace.Closeds ↥(S.strictTransform i))
            : Set ↥(S.strictTransform i)) := range_base_subschemeι _
    rw [h1, S.discardedIdeal_eq_vanishingIdeal i, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      S.coe_discardedLocusClosure i]
  have hrf : Set.range ⇑(S.discardedι i ≫ S.strictTransformι i).base
      = ⇑(S.strictTransformι i).base '' S.discardedLocus i := by
    rw [Scheme.Hom.range_comp_base, hRangeDiscarded]
  have hrU : Set.range ⇑U.ι.base = (U : Set ↥(S.ambientCenter i).subscheme) := U.range_ι
  have hrg : Set.range ⇑(U.ι ≫ (S.ambientCenter i).subschemeι).base
      = ⇑(S.strictTransformι i).base '' S.discardedLocus i := by
    rw [Scheme.Hom.range_comp_base, hrU, hUcoe]
    exact Set.image_preimage_eq_of_subset hsubr
  obtain ⟨e, he⟩ := exists_iso_of_range_base_eq (S.discardedι i ≫ S.strictTransformι i)
    (U.ι ≫ (S.ambientCenter i).subschemeι) (hrf.trans hrg.symm)
  exact ⟨U, hUcl, e, he⟩


end

section
variable (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})

private theorem detachedClopenInCenter_ofAffine_consolidated372 (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [IsAffine Y] [IsReduced Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [QuasiCompact pY] :
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).DetachedClopenInCenter := by
  have hN := isNoetherian_ambientLevel_ofAffine A hemb hsnc hsm k Y pY
  have hcl0 :
      IsClosed (Set.range ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι 0).base) := by
    rw [(AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι_eq_subschemeι 0, range_base_subschemeι]
    exact (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformIdeal 0).support).2
  have heq : principalizationSequenceIdeal_consolidated372 (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY) 0
      = Scheme.IdealSheafData.vanishingIdeal
        (⟨Set.range ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι 0).base, hcl0⟩ :
          TopologicalSpace.Closeds ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel 0)) :=
    OpenImmersionRestriction.principalizationOfEmbedding_ideal_zero_eq_vanishingIdeal
      (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) A hcl0
  have hbase : ∀ x : ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel 0),
      x ∈ (principalizationSequenceIdeal_consolidated372 (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY) 0).support →
        x ∈ Set.range ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι 0).base := by
    intro x hx
    rw [heq] at hx
    exact mem_of_mem_support_vanishingIdeal_consolidated372 _ x hx
  refine detachedClopenInCenter_of_isNoetherian_of_support_consolidated372 _ hN (support_weakTransform_subset_range_or_boundary_consolidated372 _ hN hbase) ?_
  intro j hj C hC E hE
  exact OpenImmersionRestriction.not_image_irreducibleComponent_subset_boundary_support
    (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) A j hj C hC E hE

theorem affineDetachedSmooth :
    AffineDetachedSmooth A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _ i hi
  obtain ⟨T, hTcl, e, he⟩ := detachedClopenInCenter_ofAffine_consolidated372 A hemb hsnc hsm k Y pY i hi
  have hsmC : Smooth
      (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientCenter i).subschemeι
        ≫ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).schemeAtToSpec i) :=
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).principalizationSequence.smooth_center_subschemeι i hi
  have : IsClosedImmersion T.ι :=
    Scheme.Opens.isClosedImmersion_ι_of_isClosed T hTcl
  have key := congrArg
    (fun m => m ≫ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).schemeAtToSpec i) he
  simp only [Category.assoc] at key
  rw [← key]
  infer_instance

theorem affineDetachedClopenInCenter :
    AffineDetachedClopenInCenter A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact detachedClopenInCenter_ofAffine_consolidated372 A hemb hsnc hsm k Y pY


end

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.StrictTransformSmoothness
section

open TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

namespace OpenImmersionRestriction

def chartLevelStructureMorphism (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [IsAffine Y] (pY : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) (t : ℕ) :
    (principalizationOfEmbedding k Y pY D A).schemeAt t ⟶ Spec (CommRingCat.of k) :=
  (principalizationOfEmbedding k Y pY D A).structureMorphism t

theorem chartLevelStructureMorphism_eq_structureMorphism (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [IsAffine Y] (pY : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) (t : ℕ) :
    chartLevelStructureMorphism k Y pY D A t = (principalizationOfEmbedding k Y pY D A).structureMorphism t :=
  rfl

theorem subset_detachedLocus_of_mem_detachedComponents {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType pY] (S : EmbeddedBlowupSequence k Y pY) (t : ℕ)
    {C : Set ↥(S.strictTransform t)} (hC : C ∈ S.detachedComponents t) :
    C ⊆ S.detachedLocus t := by
  rw [EmbeddedBlowupSequence.detachedLocus_eq_sUnion]
  exact Set.subset_sUnion_of_mem hC

theorem exists_iso_of_ker_eq {X X' W : Scheme.{u}} (f : X ⟶ W) (g : X' ⟶ W)
    [IsClosedImmersion f] [IsClosedImmersion g]
    (h : AlgebraicGeometry.Scheme.Hom.ker f = AlgebraicGeometry.Scheme.Hom.ker g) :
    ∃ e : X ≅ X', e.hom ≫ g = f := by
  have hgf : AlgebraicGeometry.Scheme.Hom.ker f ≤ AlgebraicGeometry.Scheme.Hom.ker g :=
    le_of_eq h
  have hfg : AlgebraicGeometry.Scheme.Hom.ker g ≤ AlgebraicGeometry.Scheme.Hom.ker f :=
    le_of_eq h.symm
  obtain ⟨ψ, hψg⟩ : ∃ ψ : X ⟶ X', ψ ≫ g = f :=
    ⟨AlgebraicGeometry.IsClosedImmersion.lift g f hfg,
      AlgebraicGeometry.IsClosedImmersion.lift_fac g f hfg⟩
  obtain ⟨φ, hφf⟩ : ∃ φ : X' ⟶ X, φ ≫ f = g :=
    ⟨AlgebraicGeometry.IsClosedImmersion.lift f g hgf,
      AlgebraicGeometry.IsClosedImmersion.lift_fac f g hgf⟩
  have : CategoryTheory.Mono f := inferInstance
  have : CategoryTheory.Mono g := inferInstance
  have h1 : ψ ≫ φ = 𝟙 X := by
    apply (CategoryTheory.cancel_mono f).1
    rw [Category.assoc, hφf, hψg, Category.id_comp]
  have h2 : φ ≫ ψ = 𝟙 X' := by
    apply (CategoryTheory.cancel_mono g).1
    rw [Category.assoc, hψg, hφf, Category.id_comp]
  exact ⟨⟨ψ, φ, h1, h2⟩, hψg⟩

theorem ker_eq_comap_ker_of_isPullback_isOpenImmersion {X₁ Y₁ U V : Scheme.{u}}
    (f : X₁ ⟶ Y₁) [QuasiCompact f] (g : V ⟶ Y₁)
    [IsOpenImmersion g] (f' : U ⟶ V) (g' : U ⟶ X₁)
    (H : CategoryTheory.IsPullback g' f' f g) :
    AlgebraicGeometry.Scheme.Hom.ker f' =
      (AlgebraicGeometry.Scheme.Hom.ker f).comap g := by
  have : QuasiCompact f' := FunctorialResolution.EmbeddedResolution.quasiCompact_of_isPullback H
  exact FunctorialResolution.EmbeddedResolution.ker_eq_comap_ker_of_isPullback_of_flat H

private theorem smooth_of_smooth_iso_hom_comp_consolidated400 {X X' Sc : Scheme.{u}} (e : X ≅ X') (g : X' ⟶ Sc)
    (h : Smooth (e.hom ≫ g)) : Smooth g := by
  have := h
  have hg : Smooth (e.inv ≫ (e.hom ≫ g)) := inferInstance
  rwa [← Category.assoc, e.inv_hom_id, Category.id_comp] at hg

theorem smooth_comp_of_iso_hom_eq {A B V W Sc : Scheme.{u}} (e : A ≅ B)
    (ι₀ : A ⟶ V) (a : V ⟶ W) (g : B ⟶ W) (q : W ⟶ Sc)
    (he : e.hom ≫ g = ι₀ ≫ a)
    (h : Smooth (ι₀ ≫ a ≫ q)) :
    Smooth (g ≫ q) := by
  refine smooth_of_smooth_iso_hom_comp_consolidated400 e (g ≫ q) ?_
  have key : e.hom ≫ g ≫ q = ι₀ ≫ a ≫ q := by
    rw [← Category.assoc, he, Category.assoc]
  rw [key]
  exact h

theorem radical_ker_eq_ker {W Z : Scheme.{u}} [IsReduced W]
    (f : W ⟶ Z) :
    (AlgebraicGeometry.Scheme.Hom.ker f).radical = AlgebraicGeometry.Scheme.Hom.ker f := by
  have hle : (AlgebraicGeometry.Scheme.Hom.ker f).radical
      ≤ AlgebraicGeometry.Scheme.Hom.ker f := by
    show (AlgebraicGeometry.Scheme.Hom.ker f).radical ≤
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals
        (fun U : Z.affineOpens =>
          RingHom.ker (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.app f U.1)))
    rw [AlgebraicGeometry.Scheme.IdealSheafData.le_ofIdeals_iff]
    intro U
    have h1 : (AlgebraicGeometry.Scheme.Hom.ker f).ideal U ≤
        RingHom.ker (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.app f U.1)) :=
      AlgebraicGeometry.Scheme.IdealSheafData.ideal_ofIdeals_le _ U
    refine le_trans (Ideal.radical_mono h1) ?_
    exact Ideal.isRadical_bot.comap _
  exact le_antisymm hle (AlgebraicGeometry.Scheme.IdealSheafData.le_radical _)

section
variable {k : Type u} [Field k]

theorem nonzeroOnComponents_ideal {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {E : List X.IdealSheafData}
    (s : FunctorialResolution.EmbeddedResolution.IdealBlowupSequence p I E) (hI : FunctorialResolution.EmbeddedResolution.NonzeroOnComponents I) :
    ∀ i : ℕ, i ≤ s.toSequenceOfBlowups.length → FunctorialResolution.EmbeddedResolution.NonzeroOnComponents (s.ideal i) := by
  intro i
  induction i with
  | zero =>
    intro _
    have h0 : s.ideal 0 = I.comap s.toSequenceOfBlowups.isoZero.hom := by
      rw [s.ideal_zero, FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_zero]
    rw [h0]
    exact FunctorialResolution.EmbeddedResolution.nonzeroOnComponents_comap_iso_hom s.toSequenceOfBlowups.isoZero I hI
  | succ i ih =>
    intro hi
    have hi' : i < s.toSequenceOfBlowups.length := hi
    have htr : (s.toSequenceOfBlowups.center i).comap (s.toSequenceOfBlowups.transitionMapSucc i) ^ 1 * s.ideal (i + 1)
        = (s.ideal i).comap (s.toSequenceOfBlowups.transitionMapSucc i) := by
      have h2 := s.ideal_succ i hi'
      rw [FunctorialResolution.Blowup.exceptionalIdeal_eq_comap] at h2
      rw [pow_one]
      exact h2
    exact FunctorialResolution.EmbeddedResolution.nonzeroOnComponents_of_pow_mul_eq_comap FunctorialResolution.EmbeddedResolution.effectiveCartierSupportContainsNoComponent
      (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i)
      (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism i hi') 1 (s.ideal i) (s.ideal (i + 1)) htr
      (ih (Nat.le_of_succ_le hi))

theorem false_of_mem_support_center [CharZero k] {W : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of k)) (hp : Smooth p)
    (I Z : W.IdealSheafData) (Mem : Set ↥W)
    (hcert : FunctorialResolution.EmbeddedResolution.PrincipalizationCertificate W p I 1 Mem Z)
    (T : Set ↥W) (hTcl : IsClosed T) (hTirr : IsIrreducible T)
    (ξ x : ↥W) (hξ : IsGenericPoint ξ T) (hx : x ∈ T)
    (hsmT : Smooth
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨T, hTcl⟩ : TopologicalSpace.Closeds ↥W)).subschemeι ≫ p))
    (hcomp : ∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ T)
    (hxi : ξ ∉ (Z.support : Set ↥W))
    (hdisj : Disjoint T Mem)
    (hagree : ∀ z ∈ T, AgreeNear I
      (Scheme.IdealSheafData.vanishingIdeal (⟨T, hTcl⟩ : TopologicalSpace.Closeds ↥W)) z)
    (hpt : x ∈ (Z.support : Set ↥W)) : False := by
  have hIso := smoothOrderOneCentersIsolated_vanishingIdealAssignment_of_principalizationCertificate
    (hcert.comap_of_isOpenImmersion (⊤ : W.Opens).ι)
  refine false_of_smoothOrderOneCentersIsolated_opens idealSheafGeometryHypotheses_vanishingIdealAssignment smoothVanishingHypotheses_vanishingIdealAssignment p I Z 1 Mem
    ⟨T, ξ, x, hTcl, hTirr, hξ, hx⟩ ⊤ ?_ hIso hp rfl ?_ hcomp hxi hdisj ?_ hpt
  · simp
  · rw [vanishingIdealAssignment_apply]
    exact hsmT
  · intro z hz
    rw [vanishingIdealAssignment_apply]
    exact hagree z hz


end

section
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y] [IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]

private theorem smooth_strictTransformι_comp_schemeAtToSpec_zero_consolidated400 (S : EmbeddedBlowupSequence k Y pY) (hsm : Smooth pY) :
    Smooth (S.strictTransformι 0 ≫ S.schemeAtToSpec 0) := by
  have : Smooth pY := hsm
  have hker : AlgebraicGeometry.Scheme.Hom.ker (S.strictTransformι 0)
      = AlgebraicGeometry.Scheme.Hom.ker (S.emb ≫ S.ambientSeq.isoZero.inv) := by
    rw [EmbeddedBlowupSequence.strictTransformι_eq_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      EmbeddedBlowupSequence.strictTransformIdeal_zero]
  obtain ⟨e, he⟩ :=
    exists_iso_of_ker_eq (S.strictTransformι 0) (S.emb ≫ S.ambientSeq.isoZero.inv) hker
  have hstruct : S.ambientSeq.isoZero.inv ≫ S.schemeAtToSpec 0 = S.ambientStruct := by
    rw [EmbeddedBlowupSequence.schemeAtToSpec_eq, FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_zero,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have key : e.hom ≫ pY = S.strictTransformι 0 ≫ S.schemeAtToSpec 0 := by
    rw [← he]
    simp only [Category.assoc]
    rw [hstruct, S.emb_comp]
  rw [← key]
  infer_instance

private theorem smooth_strictTransformι_comp_schemeAtToSpec_succ_consolidated400 (S : EmbeddedBlowupSequence k Y pY)
    (hN : ∀ j ≤ S.length, IsNoetherian (S.schemeAt j))
    (i : ℕ) (hi' : i < S.length)
    (ih' : Smooth (S.strictTransformι i ≫ S.schemeAtToSpec i))
    (hcl : ∀ y : ↥(S.strictTransform (i + 1)),
      (S.blowdown i).base ((S.strictTransformι (i + 1)).base y) ∉
        ((S.ambientCenter i).support : Set ↥(S.schemeAt i))) :
    Smooth (S.strictTransformι (i + 1) ≫ S.schemeAtToSpec (i + 1)) := by
  have := ih'
  have hredi : IsReduced (S.strictTransform i) :=
    EmbeddedBlowupSequence.isReduced_strictTransform_of_isNoetherian S hN i (Nat.le_of_lt hi')
  have hredi1 : IsReduced (S.strictTransform (i + 1)) :=
    EmbeddedBlowupSequence.isReduced_strictTransform_of_isNoetherian S hN (i + 1) hi'
  set U : (S.schemeAt (i + 1)).Opens :=
    (TopologicalSpace.Opens.map (S.blowdown i).base).obj (S.ambientCenterSupportCompl i) with _hU
  have hUsub : (U : Set ↥(S.schemeAt (i + 1))) ⊆
      ⇑(S.blowdown i).base ⁻¹'
        ((S.ambientCenterSupportCompl i : (S.schemeAt i).Opens) : Set ↥(S.schemeAt i)) := fun _ hx => hx
  have hgi : IsOpenImmersion (U.ι ≫ S.blowdown i) :=
    EmbeddedBlowupSequence.isOpenImmersion_ι_comp_blowdown S i hi' U hUsub
  have hrangeA : Set.range ⇑(S.strictTransformι (i + 1)).base ⊆ Set.range ⇑U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro z ⟨y, rfl⟩
    exact (S.mem_ambientCenterSupportCompl i _).mpr (hcl y)
  set j := AlgebraicGeometry.IsOpenImmersion.lift U.ι (S.strictTransformι (i + 1)) hrangeA with _hjdef
  have hj : j ≫ U.ι = S.strictTransformι (i + 1) :=
    AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  have hjc : IsClosedImmersion (j ≫ U.ι) := by
    rw [hj]; infer_instance
  have : IsClosedImmersion j :=
    AlgebraicGeometry.IsClosedImmersion.of_comp j U.ι
  have hbase : ∀ y : ↥(S.strictTransform (i + 1)),
      U.ι.base (j.base y) = (S.strictTransformι (i + 1)).base y := by
    intro y
    rw [show U.ι.base (j.base y) = (j ≫ U.ι).base y from rfl, hj]
  have hkeymap : ∀ y : ↥(S.strictTransform (i + 1)),
      (S.blowdown i).base ((S.strictTransformι (i + 1)).base y)
        = (S.strictTransformι i).base ((S.strictTransformMap i).base y) := by
    intro y
    have h : (S.strictTransformMap i ≫ S.strictTransformι i).base y
        = (S.strictTransformι (i + 1) ≫ S.blowdown i).base y := by
      rw [S.strictTransformMap_comp_strictTransformι i]
    exact h.symm
  set pre : Set ↥(U.toScheme) := ⇑(U.ι ≫ S.blowdown i).base ⁻¹'
      (((S.strictTransformIdeal i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
        Set ↥(S.schemeAt i)) with hpre
  have hsuppcl : IsClosed pre := by
    rw [hpre]
    exact (S.strictTransformIdeal i).support.2.preimage
      (U.ι ≫ S.blowdown i).base.hom.continuous
  have hker_eq : S.strictTransformIdeal i = AlgebraicGeometry.Scheme.Hom.ker (S.strictTransformι i) := by
    rw [EmbeddedBlowupSequence.strictTransformι_eq_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
  have h1 : Scheme.IdealSheafData.vanishingIdeal
      ((S.strictTransformIdeal i).support) = S.strictTransformIdeal i := by
    rw [Scheme.IdealSheafData.vanishingIdeal_support, hker_eq]
    exact radical_ker_eq_ker (S.strictTransformι i)
  have hKvan : (S.strictTransformIdeal i).comap (U.ι ≫ S.blowdown i)
      = Scheme.IdealSheafData.vanishingIdeal
          (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme)) := by
    calc (S.strictTransformIdeal i).comap (U.ι ≫ S.blowdown i)
        = (Scheme.IdealSheafData.vanishingIdeal
            ((S.strictTransformIdeal i).support)).comap (U.ι ≫ S.blowdown i) := by rw [h1]
      _ = Scheme.IdealSheafData.vanishingIdeal
            (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme)) :=
          comap_vanishingIdeal_of_isOpenImmersion (U.ι ≫ S.blowdown i) _ _ rfl
  have hrange1 : Set.range ⇑j.base = pre := by
    rw [hpre]
    ext z
    simp only [Set.mem_range, Set.mem_preimage]
    constructor
    · rintro ⟨y, rfl⟩
      rw [show (U.ι ≫ S.blowdown i).base (j.base y)
          = (S.blowdown i).base (U.ι.base (j.base y)) from rfl, hbase y, hkeymap y,
        ← Scheme.IdealSheafData.range_subschemeι (S.strictTransformIdeal i)]
      exact ⟨(S.strictTransformMap i).base y, rfl⟩
    · intro hz
      have hzU : U.ι.base z ∈ ((U : (S.schemeAt (i + 1)).Opens) :
          Set ↥(S.schemeAt (i + 1))) := by
        rw [← Scheme.Opens.range_ι U]
        exact ⟨z, rfl⟩
      have hnc : (S.blowdown i).base (U.ι.base z) ∉
          (((S.ambientCenter i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
            Set ↥(S.schemeAt i)) :=
        (S.mem_ambientCenterSupportCompl i _).mp (hUsub hzU)
      have hin : (S.blowdown i).base (U.ι.base z) ∈
          (((S.strictTransformIdeal i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
            Set ↥(S.schemeAt i)) := hz
      have hrr : Set.range ⇑(S.strictTransformι (i + 1)).base
          = closure (⇑(S.blowdown i).base ⁻¹'
              ((((S.strictTransformIdeal i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
                  Set ↥(S.schemeAt i)) \
                (((S.ambientCenter i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
                  Set ↥(S.schemeAt i)))) :=
        EmbeddedBlowupSequence.range_strictTransformι_succ S hN i hi'
      have hx : U.ι.base z ∈ Set.range ⇑(S.strictTransformι (i + 1)).base := by
        rw [hrr]
        exact subset_closure ⟨hin, hnc⟩
      obtain ⟨w, hw⟩ := hx
      refine ⟨w, ?_⟩
      apply U.ι.isOpenEmbedding.injective
      rw [hbase w, hw]
  have hrange2 : Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal
      (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme))).subschemeι.base
        = pre := by
    rw [FunctorialResolution.EmbeddedResolution.range_base_subschemeι,
      AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : IsReduced
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme))).subscheme :=
    AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _ _
  obtain ⟨e, he⟩ := FunctorialResolution.EmbeddedResolution.exists_iso_of_range_base_eq j
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme))).subschemeι
    (hrange1.trans hrange2.symm)
  have ihsub : Smooth
      ((S.strictTransformIdeal i).subschemeι ≫ S.schemeAtToSpec i) := by
    rw [← EmbeddedBlowupSequence.strictTransformι_eq_subschemeι]
    exact ih'
  have hsm2 := smooth_comap_subschemeι_of_isOpenImmersion
    (U.ι ≫ S.blowdown i) (S.strictTransformIdeal i) (S.schemeAtToSpec i) ihsub
  rw [hKvan] at hsm2
  have hlev : S.blowdown i ≫ S.schemeAtToSpec i = S.schemeAtToSpec (i + 1) := by
    rw [EmbeddedBlowupSequence.schemeAtToSpec_eq, EmbeddedBlowupSequence.schemeAtToSpec_eq, ← Category.assoc,
      ← FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_succ]
  have hgoal : S.strictTransformι (i + 1) ≫ S.schemeAtToSpec (i + 1)
      = e.hom ≫ ((Scheme.IdealSheafData.vanishingIdeal
          (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme))).subschemeι
          ≫ ((U.ι ≫ S.blowdown i) ≫ S.schemeAtToSpec i)) := by
    rw [← hj, ← hlev, ← he]
    simp only [Category.assoc]
  rw [hgoal]
  have := hsm2
  infer_instance

private theorem agreeNear_vanishingIdeal_image_of_avoidsCenters_le_of_disjoint_zero_consolidated400
    [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u})
    (hDisj0 : ∀ C₁ C₂ : Set ↥((D.toEmbeddedBlowupSequence A).strictTransform 0),
      C₁ ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) →
      C₂ ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) →
      C₁ ≠ C₂ → Disjoint C₁ C₂) :
    ∀ (t : ℕ),
      (∀ s, s ≤ t → ∀ y : ↥((D.toEmbeddedBlowupSequence A).strictTransform s),
        (D.toEmbeddedBlowupSequence A).AvoidsCenters s (((D.toEmbeddedBlowupSequence A).strictTransformι s).base y)) →
      t ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ C : Set ↥((D.toEmbeddedBlowupSequence A).strictTransform t),
        C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform t) →
        ∀ hCcl : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C),
        ∀ x : ↥((D.toEmbeddedBlowupSequence A).schemeAt t),
          x ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C →
          AgreeNear ((principalizationOfEmbedding k Y pY D A).ideal t)
            (Scheme.IdealSheafData.vanishingIdeal
              (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C, hCcl⟩ :
                TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt t))) x := by
  intro t
  induction t with
  | zero =>
    intro _ _ C hC hCcl x hx
    classical
    have hNoeth : TopologicalSpace.NoetherianSpace ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) :=
      (D.toEmbeddedBlowupSequence A).noetherianSpace_strictTransform_of_isNoetherian (isNoetherian_schemeAt_toEmbeddedBlowupSequence D A) 0
        (Nat.zero_le _)
    have hemb := (D.toEmbeddedBlowupSequence A).isClosedEmbedding_strictTransformι 0
    have hclr : IsClosed (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base) := hemb.isClosed_range
    have hid0 := principalizationOfEmbedding_ideal_zero_eq_vanishingIdeal D A hclr
    obtain ⟨Bad, hBaddef⟩ : ∃ B : Set ↥((D.toEmbeddedBlowupSequence A).schemeAt 0),
        B = ⋃ C'' ∈ (irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) \ {C}),
          ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C'' := ⟨_, rfl⟩
    have hfin : (irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) \ {C}).Finite :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset Set.sdiff_subset
    have hBadcl : IsClosed Bad := by
      rw [hBaddef]
      exact hfin.isClosed_biUnion fun C'' hC'' =>
        hemb.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ hC''.1)
    have hxU : x ∈ Badᶜ := by
      intro hmem
      rw [hBaddef] at hmem
      obtain ⟨C'', hC''D, hxim⟩ := Set.mem_iUnion₂.mp hmem
      obtain ⟨z, hzC'', hz⟩ := hxim
      obtain ⟨w, hwC, hw⟩ := hx
      have hzw : z = w := hemb.injective (hz.trans hw.symm)
      rw [hzw] at hzC''
      have hne : C'' ≠ C := fun h => hC''D.2 (Set.mem_singleton_iff.mpr h)
      exact Set.disjoint_left.mp (hDisj0 C'' C hC''D.1 hC hne) hzC'' hwC
    have hinter : (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base) ∩ Badᶜ
        = (⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C) ∩ Badᶜ := by
      ext z
      constructor
      · rintro ⟨⟨w, rfl⟩, hz⟩
        refine ⟨?_, hz⟩
        by_cases hw : w ∈ C
        · exact ⟨w, hw, rfl⟩
        · refine absurd ?_ hz
          rw [hBaddef]
          refine Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents w, ?_⟩
            ⟨w, mem_irreducibleComponent, rfl⟩
          intro h
          exact hw (h ▸ mem_irreducibleComponent)
      · rintro ⟨⟨w, hwC, rfl⟩, hz⟩
        exact ⟨⟨w, rfl⟩, hz⟩
    rw [hid0]
    exact agreeNear_vanishingIdeal_of_inter_eq _ _ ⟨Badᶜ, hBadcl.isOpen_compl⟩ _ hxU hinter
  | succ i ih =>
    intro hcl hi C hC hCcl x hx
    classical
    have hN := isNoetherian_schemeAt_toEmbeddedBlowupSequence D A
    have hi' : i < (D.toEmbeddedBlowupSequence A).length := Nat.lt_of_succ_le hi
    have hilt : i < (principalizationOfEmbedding k Y pY D A).length := hi'
    obtain ⟨η, hηgen⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents _ hC)
    obtain ⟨C', hC'm, hη', _⟩ :=
      (D.toEmbeddedBlowupSequence A).exists_irreducibleComponent_isGenericPoint_strictTransformMap hN i hi' C hC η hηgen
    have hC'cl : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C') :=
      ((D.toEmbeddedBlowupSequence A).isClosedEmbedding_strictTransformι i).isClosedMap _
        (isClosed_of_mem_irreducibleComponents _ hC'm)
    obtain ⟨y, hyC, hxy⟩ := hx
    have hclx : (D.toEmbeddedBlowupSequence A).AvoidsCenters (i + 1) x := by
      rw [← hxy]
      exact hcl (i + 1) le_rfl y
    have hnot := (((D.toEmbeddedBlowupSequence A).avoidsCenters_succ_iff i x).mp hclx).1
    have hblow : ((D.toEmbeddedBlowupSequence A).blowdown i).base x ∈
        ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' :=
      EmbeddedBlowupSequence.mem_image_strictTransformι_of_mem_image_succ (D.toEmbeddedBlowupSequence A) i C η hηgen
        C' hη' x ⟨y, hyC, hxy⟩
    obtain ⟨V, hxV, hVeq⟩ := (agreeNear_iff _ _ _).mp
      (ih (fun s hs => hcl s (le_trans hs (Nat.le_succ i))) (Nat.le_of_succ_le hi)
        C' hC'm hC'cl _ hblow)
    obtain ⟨V', hV'⟩ : ∃ V' : ((D.toEmbeddedBlowupSequence A).schemeAt i).Opens, V' = V := ⟨V, rfl⟩
    have hxV' : ((D.toEmbeddedBlowupSequence A).blowdown i).base x ∈ V' := by
      rw [hV']; exact hxV
    have hV'eq : ((principalizationOfEmbedding k Y pY D A).ideal i).comap V'.ι
        = (Scheme.IdealSheafData.vanishingIdeal
            (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ :
              TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap V'.ι := by
      rw [hV']; exact hVeq
    obtain ⟨U, hUdef⟩ : ∃ U : ((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)).Opens,
        U = (TopologicalSpace.Opens.map ((D.toEmbeddedBlowupSequence A).blowdown i).base).obj
          (V' ⊓ (D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i) := ⟨_, rfl⟩
    have hUsub : (U : Set ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1))) ⊆
        ⇑((D.toEmbeddedBlowupSequence A).blowdown i).base ⁻¹'
          (((D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i : ((D.toEmbeddedBlowupSequence A).schemeAt i).Opens) :
            Set ↥((D.toEmbeddedBlowupSequence A).schemeAt i)) := by
      rw [hUdef]
      intro z hz
      exact hz.2
    have hmemU : ∀ z : ↥U, ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base z) ∉
        (((D.toEmbeddedBlowupSequence A).ambientCenter i).support :
          Set ↥((D.toEmbeddedBlowupSequence A).schemeAt i)) := by
      intro z
      exact hUsub z.2
    have hxU : x ∈ U := by
      rw [hUdef]
      exact ⟨hxV', ((D.toEmbeddedBlowupSequence A).mem_ambientCenterSupportCompl i _).mpr hnot⟩
    have : IsOpenImmersion (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) :=
      EmbeddedBlowupSequence.isOpenImmersion_ι_comp_blowdown (D.toEmbeddedBlowupSequence A) i hi' U hUsub
    have hexc : ((principalizationOfEmbedding k Y pY D A).exceptionalIdeal i).comap U.ι = ⊤ := by
      refine FunctorialResolution.EmbeddedResolution.comap_ι_eq_top_of_disjoint _ _ ?_
      rw [Set.disjoint_left]
      intro z hz hmem
      rw [(principalizationOfEmbedding k Y pY D A).exceptionalIdeal_eq i] at hmem
      exact absurd (mem_support_of_mem_support_comap
        ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i) _ z hmem) (hUsub hz)
    have hJ : ((principalizationOfEmbedding k Y pY D A).ideal (i + 1)).comap U.ι
        = ((principalizationOfEmbedding k Y pY D A).ideal i).comap
            (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) :=
      comap_eq_comap_comp_of_mul_eq _ U _ _ _
        ((principalizationOfEmbedding k Y pY D A).ideal_succ i hilt) hexc
    have hle : U ≤ (TopologicalSpace.Opens.map
        ((D.toEmbeddedBlowupSequence A).blowdown i).base).obj V' := by
      rw [hUdef]
      intro z hz
      exact hz.1
    have hcomapφ : ((principalizationOfEmbedding k Y pY D A).ideal i).comap
          (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i)
        = (Scheme.IdealSheafData.vanishingIdeal
            (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ :
              TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap
            (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) :=
      AlgebraicGeometry.Scheme.IdealSheafData.comap_ι_comp_eq_of_comap_ι_eq
        ((D.toEmbeddedBlowupSequence A).blowdown i) V' U hle _ _ hV'eq
    have hLHS : (Scheme.IdealSheafData.vanishingIdeal
          (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ :
            TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap
          (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i)
        = Scheme.IdealSheafData.vanishingIdeal
            (FunctorialResolution.EmbeddedResolution.closedPreimage U.ι
              (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C, hCcl⟩ :
                TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)))) := by
      refine FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq
        (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) _ _ ?_
      ext z
      have hcb : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base z
          = ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base z) := rfl
      have hiff := EmbeddedBlowupSequence.mem_image_strictTransformι_iff_of_notMem_ambientCenter
        (D.toEmbeddedBlowupSequence A) hN i hi' C η hηgen C' hη' (U.ι.base z) (hmemU z)
      constructor
      · intro hz
        have hz1 : U.ι.base z ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C := hz
        have hz2 : ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base z)
            ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := hiff.mpr hz1
        have hz3 : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base z
            ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := by
          rw [hcb]; exact hz2
        exact hz3
      · intro hz
        have hz1 : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base z
            ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := hz
        have hz2 : ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base z)
            ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := by
          rw [← hcb]; exact hz1
        exact hiff.mp hz2
    refine (agreeNear_iff _ _ _).mpr ⟨U, hxU, ?_⟩
    exact hJ.trans (hcomapφ.trans (hLHS.trans
      (FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion U.ι
        (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C, hCcl⟩ :
          TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)))).symm))

private theorem smooth_vanishingIdeal_image_of_smooth_strictTransformι_consolidated400
    [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u})
    (t : ℕ) (ht : t ≤ (D.toEmbeddedBlowupSequence A).length)
    (hsmq : Smooth
      ((D.toEmbeddedBlowupSequence A).strictTransformι t ≫ chartLevelStructureMorphism k Y pY D A t))
    (C : Set ↥((D.toEmbeddedBlowupSequence A).strictTransform t))
    (hC : C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform t))
    (hCcl : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C)) :
    Smooth
      ((Scheme.IdealSheafData.vanishingIdeal
          (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C, hCcl⟩ :
            TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt t))).subschemeι ≫
        chartLevelStructureMorphism k Y pY D A t) := by
  have := hsmq
  have hPlevel : (D.toEmbeddedBlowupSequence A).schemeAtToSpec t = chartLevelStructureMorphism k Y pY D A t := rfl
  have hftq : LocallyOfFiniteType
      ((D.toEmbeddedBlowupSequence A).strictTransformι t ≫ chartLevelStructureMorphism k Y pY D A t) := by
    have h1 := (D.toEmbeddedBlowupSequence A).locallyOfFiniteType_strictTransformToSpec t ht
    rw [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.strictTransformToSpec_eq, hPlevel] at h1
    exact h1
  have hclopen : IsClopen C :=
    FunctorialResolution.EmbeddedResolution.isClopen_of_mem_irreducibleComponents_of_smooth
      ((D.toEmbeddedBlowupSequence A).strictTransformι t ≫ chartLevelStructureMorphism k Y pY D A t) C hC
  have hsub := FunctorialResolution.EmbeddedResolution.smooth_subschemeι_vanishingIdeal_comp_of_isClopen
      ((D.toEmbeddedBlowupSequence A).strictTransformι t ≫ chartLevelStructureMorphism k Y pY D A t) C hclopen
  have : IsReduced
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨C, hclopen.isClosed⟩ :
          TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).strictTransform t))).subscheme :=
    AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _ _
  have : IsReduced
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C, hCcl⟩ :
          TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt t))).subscheme :=
    AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _ _
  have hrange :
      Set.range ⇑((Scheme.IdealSheafData.vanishingIdeal
            (⟨C, hclopen.isClosed⟩ :
              TopologicalSpace.Closeds
                ↥((D.toEmbeddedBlowupSequence A).strictTransform t))).subschemeι ≫
          (D.toEmbeddedBlowupSequence A).strictTransformι t).base
        = Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal
            (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C, hCcl⟩ :
              TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt t))).subschemeι.base := by
    rw [Scheme.Hom.range_comp_base, FunctorialResolution.EmbeddedResolution.range_base_subschemeι,
      FunctorialResolution.EmbeddedResolution.range_base_subschemeι,
      AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal,
      AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨e, he⟩ := FunctorialResolution.EmbeddedResolution.exists_iso_of_range_base_eq _ _ hrange
  exact smooth_comp_of_iso_hom_eq e _ _ _ _ he hsub


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension) (hrad : SmoothSubschemeIdealIsRadical.{u}) {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y] [IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY] [QuasiCompact pY] (D : EmbeddingDatum k Y pY)
include hB

private theorem notMem_ambientCenter_support_of_notMem_detachedComponents_consolidated400
    (t : ℕ) (ht : t < (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    (hsmq : Smooth
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t ≫
        chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t))
    (hcl : ∀ s, s ≤ t →
      ∀ y : ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform s),
      (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).AvoidsCenters s
        (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι s).base y))
    (hDisj0 : ∀ C₁ C₂ :
        Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform 0),
      C₁ ∈ irreducibleComponents
        ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform 0) →
      C₂ ∈ irreducibleComponents
        ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform 0) →
      C₁ ≠ C₂ → Disjoint C₁ C₂)
    (C : Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hC : C ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hfr : C ∉ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedComponents t)
    (z : ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t)) (hz : z ∈ C) :
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base z ∉
      (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).ambientCenter t).support :
        Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t)) := by
  classical
  intro hmem
  have hemb := (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).isClosedEmbedding_strictTransformι t
  have hCcl : IsClosed
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C) :=
    hemb.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ hC)
  obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents _ hC)
  have hagree := agreeNear_vanishingIdeal_image_of_avoidsCenters_le_of_disjoint_zero_consolidated400 D (canonicalPrincipalization hres hrad) hDisj0 t hcl
    (le_of_lt ht) C hC hCcl
  have hsmV := smooth_vanishingIdeal_image_of_smooth_strictTransformι_consolidated400 D
    (canonicalPrincipalization hres hrad) t (le_of_lt ht) hsmq C hC hCcl
  have hsmp : Smooth
      (chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) := by
    rw [chartLevelStructureMorphism_eq_structureMorphism]
    exact IdealBlowupSequence.smooth_structureMorphism
      (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)) t (le_of_lt ht)
  have hspec := (PrincipalizationRules.isMaxOrderReduction_outputLevelData (canonicalAlgorithmRules hres) hB
      (krullDimSucc D.ambient)).cert
      (markedTripleOrderOne k D.ambient D.ambientStruct (AlgebraicGeometry.Scheme.Hom.ker D.emb) [])
      (markedTripleOrderOne_isAdmissible k D.ambient D.ambientStruct
        (AlgebraicGeometry.Scheme.Hom.ker D.emb) D.nonzeroOnComponents_ker [] D.sncEmpty)
      (le_of_eq (markedTripleOrderOne_dim k D.ambient D.ambientStruct
        (AlgebraicGeometry.Scheme.Hom.ker D.emb) []))
      t ht
  have hcert : FunctorialResolution.EmbeddedResolution.PrincipalizationCertificate
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t)
      (chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t)
      ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t) 1
      (⋃ E ∈ (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).boundary t,
        (E.support :
          Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t)))
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).ambientCenter t) := hspec
  have hgen : IsGenericPoint
      (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base η)
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C) :=
    FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding hemb hη
  have hirr : IsIrreducible
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C) :=
    hC.1.image _ hemb.continuous.continuousOn
  have hIsupp :
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C) ⊆
      ((((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t).support) :
        Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t)) := by
    refine subset_support_of_agreeNear idealSheafGeometryHypotheses_vanishingIdealAssignment _ _ _ hCcl ?_
    intro x hx
    rw [vanishingIdealAssignment_apply]
    exact hagree x hx
  have hnz : FunctorialResolution.EmbeddedResolution.NonzeroOnComponents
      ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t) :=
    nonzeroOnComponents_ideal (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad))
      D.nonzeroOnComponents_ker t (le_of_lt ht)
  have hcomp : ∀ E ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t),
      ¬ E ⊆ (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C) := by
    intro E hE hEsub
    exact (FunctorialResolution.EmbeddedResolution.nonzeroOnComponents_iff _).1 hnz E hE (hEsub.trans hIsupp)
  have hxi : ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base η ∉
      ((((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).ambientCenter t).support) :
        Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t)) :=
    (D.toEmbeddedBlowupSequence
      (canonicalPrincipalization hres hrad)).notMem_ambientCenter_support_of_isGenericPoint t
      C hC hfr η hη
  have hdisj : Disjoint
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C)
      (⋃ E ∈ (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).boundary t,
        (E.support :
          Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t))) := by
    rw [Set.disjoint_left]
    rintro a ⟨w, hwC, rfl⟩ ha
    obtain ⟨E, hE, haE⟩ := Set.mem_iUnion₂.mp ha
    exact not_avoidsCenters_of_mem_boundary_support D (canonicalPrincipalization hres hrad) t
      (le_of_lt ht) E hE _ haE (hcl t le_rfl w)
  exact false_of_mem_support_center
    (chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) hsmp
    ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t)
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).ambientCenter t)
    (⋃ E ∈ (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).boundary t,
      (E.support :
        Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t)))
    hcert
    (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C) hCcl hirr
    (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base η)
    (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base z)
    hgen ⟨z, hz, rfl⟩ hsmV hcomp hxi hdisj hagree hmem

theorem avoidsCenters_strictTransformι_of_smooth
    (hsm : Smooth pY) (t : ℕ)
    (ht : t ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    (y : ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t)) :
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).AvoidsCenters t
      (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base y) := by
  classical
  have := hsm
  have hN := isNoetherian_schemeAt_toEmbeddedBlowupSequence D (canonicalPrincipalization hres hrad)
  have hsm0 : Smooth
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι 0 ≫
        (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAtToSpec 0) :=
    smooth_strictTransformι_comp_schemeAtToSpec_zero_consolidated400 (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)) hsm
  have hDisj0 : ∀ C₁ C₂ :
        Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform 0),
      C₁ ∈ irreducibleComponents
        ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform 0) →
      C₂ ∈ irreducibleComponents
        ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform 0) →
      C₁ ≠ C₂ → Disjoint C₁ C₂ := by
    intro C₁ C₂ h₁ h₂ hne
    exact FunctorialResolution.EmbeddedResolution.irreducibleComponentsDisjointOfSmooth k _ _ hsm0 C₁ h₁ C₂ h₂ hne
  have main : ∀ s : ℕ, s ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length →
      Smooth
        ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι s ≫
          (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAtToSpec s) ∧
      ∀ r, r ≤ s →
        ∀ w : ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform r),
        (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).AvoidsCenters r
          (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι r).base w) := by
    intro s
    induction s with
    | zero =>
      intro _
      refine ⟨hsm0, ?_⟩
      intro r hr w
      obtain rfl : r = 0 := Nat.le_zero.mp hr
      exact (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).avoidsCenters_zero _
    | succ i ih =>
      intro hi
      have hi' : i < (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length :=
        Nat.lt_of_succ_le hi
      obtain ⟨ihsm, ihcl⟩ := ih (Nat.le_of_succ_le hi)
      have hsmq' : Smooth
          ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι i ≫
            chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) i) := ihsm
      have hclear : ∀ w :
          ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform (i + 1)),
          (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).AvoidsCenters (i + 1)
            (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι (i + 1)).base w) := by
        intro w
        have hCw : irreducibleComponent w ∈ irreducibleComponents
            ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform (i + 1)) :=
          irreducibleComponent_mem_irreducibleComponents w
        obtain ⟨η₁, hη₁⟩ :=
          QuasiSober.sober hCw.1 (isClosed_of_mem_irreducibleComponents _ hCw)
        obtain ⟨C', hC'm, hη', hfr⟩ :=
          (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).exists_irreducibleComponent_isGenericPoint_strictTransformMap hN i hi'
            (irreducibleComponent w) hCw η₁ hη₁
        have hcont : Continuous
            ⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformMap i).base :=
          ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformMap i).base.hom.continuous
        have hsubcl : closure ({η₁} :
            Set ↥((D.toEmbeddedBlowupSequence
              (canonicalPrincipalization hres hrad)).strictTransform (i + 1))) ⊆
            ⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformMap i).base ⁻¹'
              closure ({((D.toEmbeddedBlowupSequence
                  (canonicalPrincipalization hres hrad)).strictTransformMap i).base η₁} :
                Set ↥((D.toEmbeddedBlowupSequence
                  (canonicalPrincipalization hres hrad)).strictTransform i)) := by
          refine closure_minimal ?_ (isClosed_closure.preimage hcont)
          intro v hv
          have hv' : v = η₁ := hv
          subst hv'
          exact subset_closure rfl
        have hwC : w ∈ closure ({η₁} :
            Set ↥((D.toEmbeddedBlowupSequence
              (canonicalPrincipalization hres hrad)).strictTransform (i + 1))) := by
          rw [hη₁]; exact mem_irreducibleComponent
        have hzC' : ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformMap i).base w
            ∈ C' := by
          have hmm := hsubcl hwC
          rw [Set.mem_preimage, hη'] at hmm
          exact hmm
        have hkey : ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι i).base
            (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformMap i).base w)
            = ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).blowdown i).base
                (((D.toEmbeddedBlowupSequence
                  (canonicalPrincipalization hres hrad)).strictTransformι (i + 1)).base w) := by
          have h : (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformMap i) ≫
              ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι i)).base w
              = (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι (i + 1)) ≫
                ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).blowdown i)).base w := by
            rw [(D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformMap_comp_strictTransformι i]
          simpa using h
        refine ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).avoidsCenters_succ_iff i _).mpr
          ⟨?_, ?_⟩
        · rw [← hkey]
          exact notMem_ambientCenter_support_of_notMem_detachedComponents_consolidated400 hres hB hrad D i hi'
            hsmq' ihcl hDisj0 C' hC'm hfr _ hzC'
        · rw [← hkey]
          exact ihcl i le_rfl _
      refine ⟨smooth_strictTransformι_comp_schemeAtToSpec_succ_consolidated400 (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)) hN i hi'
        ihsm ?_, ?_⟩
      · intro w
        exact (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).avoidsCenters_succ_iff i _).mp
          (hclear w)).1
      · intro r hr w
        rcases Nat.lt_or_ge r (i + 1) with hlt | hge
        · exact ihcl r (Nat.lt_succ_iff.mp hlt) w
        · obtain rfl : r = i + 1 := le_antisymm hr hge
          exact hclear w
  exact (main t ht).2 t le_rfl y

theorem strictTransformι_notMem_support_of_mem_boundary
    (hsm : Smooth pY) (t : ℕ)
    (ht : t ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    (y : ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (E : ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t).IdealSheafData)
    (hE : E ∈ (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).boundary t) :
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base y ∉
      (E.support :
        Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t)) := by
  intro hx
  exact not_avoidsCenters_of_mem_boundary_support D (canonicalPrincipalization hres hrad) t ht E hE _ hx
    (avoidsCenters_strictTransformι_of_smooth hres hB hrad D hsm t ht y)


end

end OpenImmersionRestriction

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.SmoothStrictTransformComponents
section

open TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

namespace OpenImmersionRestriction

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension) (hrad : SmoothSubschemeIdealIsRadical.{u}) {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y] [IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY] [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (hsm : Smooth pY)
include hB hsm

private theorem smooth_strictTransformι_comp_schemeAtToSpec_consolidated429
    :
    ∀ i, i ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length →
      Smooth
        ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι i ≫
          (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAtToSpec i) := by
  have : Smooth pY := hsm
  have hN := isNoetherian_schemeAt_toEmbeddedBlowupSequence D (canonicalPrincipalization hres hrad)
  intro i
  induction i with
  | zero =>
      intro _
      set S := D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad) with _hS
      have hker : AlgebraicGeometry.Scheme.Hom.ker (S.strictTransformι 0)
          = AlgebraicGeometry.Scheme.Hom.ker (S.emb ≫ S.ambientSeq.isoZero.inv) := by
        rw [EmbeddedBlowupSequence.strictTransformι_eq_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
          EmbeddedBlowupSequence.strictTransformIdeal_zero]
      obtain ⟨e, he⟩ :=
        exists_iso_of_ker_eq (S.strictTransformι 0) (S.emb ≫ S.ambientSeq.isoZero.inv) hker
      have hstruct : S.ambientSeq.isoZero.inv ≫ S.schemeAtToSpec 0 = S.ambientStruct := by
        rw [EmbeddedBlowupSequence.schemeAtToSpec_eq, FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_zero,
          ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      have key : e.hom ≫ pY = S.strictTransformι 0 ≫ S.schemeAtToSpec 0 := by
        rw [← he]
        simp only [Category.assoc]
        rw [hstruct, S.emb_comp]
      rw [← key]
      infer_instance
  | succ i ih =>
      intro hi
      set S := D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad) with _hS
      have hi' : i < S.length := hi
      have ih' := ih (Nat.le_of_succ_le hi)
      have hredi : IsReduced (S.strictTransform i) :=
        EmbeddedBlowupSequence.isReduced_strictTransform_of_isNoetherian S hN i (Nat.le_of_lt hi')
      have hredi1 : IsReduced (S.strictTransform (i + 1)) :=
        EmbeddedBlowupSequence.isReduced_strictTransform_of_isNoetherian S hN (i + 1) hi
      set U : (S.schemeAt (i + 1)).Opens :=
        (TopologicalSpace.Opens.map (S.blowdown i).base).obj (S.ambientCenterSupportCompl i) with _hU
      have hUsub : (U : Set ↥(S.schemeAt (i + 1))) ⊆
          ⇑(S.blowdown i).base ⁻¹'
            ((S.ambientCenterSupportCompl i : (S.schemeAt i).Opens) : Set ↥(S.schemeAt i)) := fun _ hx => hx
      have hgi : IsOpenImmersion (U.ι ≫ S.blowdown i) :=
        EmbeddedBlowupSequence.isOpenImmersion_ι_comp_blowdown S i hi' U hUsub
      have hrangeA : Set.range ⇑(S.strictTransformι (i + 1)).base ⊆ Set.range ⇑U.ι.base := by
        rw [Scheme.Opens.range_ι]
        rintro z ⟨y, rfl⟩
        exact (S.mem_ambientCenterSupportCompl i _).mpr
          ((S.avoidsCenters_succ_iff i _).mp (avoidsCenters_strictTransformι_of_smooth hres hB hrad D hsm (i + 1) hi y)).1
      set j := AlgebraicGeometry.IsOpenImmersion.lift U.ι (S.strictTransformι (i + 1)) hrangeA with _hjdef
      have hj : j ≫ U.ι = S.strictTransformι (i + 1) :=
        AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
      have hjc : IsClosedImmersion (j ≫ U.ι) := by
        rw [hj]; infer_instance
      have : IsClosedImmersion j :=
        AlgebraicGeometry.IsClosedImmersion.of_comp j U.ι
      have hbase : ∀ y : ↥(S.strictTransform (i + 1)),
          U.ι.base (j.base y) = (S.strictTransformι (i + 1)).base y := by
        intro y
        rw [show U.ι.base (j.base y) = (j ≫ U.ι).base y from rfl, hj]
      have hkeymap : ∀ y : ↥(S.strictTransform (i + 1)),
          (S.blowdown i).base ((S.strictTransformι (i + 1)).base y)
            = (S.strictTransformι i).base ((S.strictTransformMap i).base y) := by
        intro y
        have h : (S.strictTransformMap i ≫ S.strictTransformι i).base y
            = (S.strictTransformι (i + 1) ≫ S.blowdown i).base y := by
          rw [S.strictTransformMap_comp_strictTransformι i]
        exact h.symm
      set pre : Set ↥(U.toScheme) := ⇑(U.ι ≫ S.blowdown i).base ⁻¹'
          (((S.strictTransformIdeal i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
            Set ↥(S.schemeAt i)) with hpre
      have hsuppcl : IsClosed pre := by
        rw [hpre]
        exact (S.strictTransformIdeal i).support.2.preimage
          (U.ι ≫ S.blowdown i).base.hom.continuous
      have hker_eq : S.strictTransformIdeal i = AlgebraicGeometry.Scheme.Hom.ker (S.strictTransformι i) := by
        rw [EmbeddedBlowupSequence.strictTransformι_eq_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
      have h1 : Scheme.IdealSheafData.vanishingIdeal
          ((S.strictTransformIdeal i).support) = S.strictTransformIdeal i := by
        rw [Scheme.IdealSheafData.vanishingIdeal_support, hker_eq]
        exact radical_ker_eq_ker (S.strictTransformι i)
      have hKvan : (S.strictTransformIdeal i).comap (U.ι ≫ S.blowdown i)
          = Scheme.IdealSheafData.vanishingIdeal
              (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme)) := by
        calc (S.strictTransformIdeal i).comap (U.ι ≫ S.blowdown i)
            = (Scheme.IdealSheafData.vanishingIdeal
                ((S.strictTransformIdeal i).support)).comap (U.ι ≫ S.blowdown i) := by rw [h1]
          _ = Scheme.IdealSheafData.vanishingIdeal
                (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme)) :=
              comap_vanishingIdeal_of_isOpenImmersion (U.ι ≫ S.blowdown i) _ _ rfl
      have hrange1 : Set.range ⇑j.base = pre := by
        rw [hpre]
        ext z
        simp only [Set.mem_range, Set.mem_preimage]
        constructor
        · rintro ⟨y, rfl⟩
          rw [show (U.ι ≫ S.blowdown i).base (j.base y)
              = (S.blowdown i).base (U.ι.base (j.base y)) from rfl, hbase y, hkeymap y,
            ← Scheme.IdealSheafData.range_subschemeι (S.strictTransformIdeal i)]
          exact ⟨(S.strictTransformMap i).base y, rfl⟩
        · intro hz
          have hzU : U.ι.base z ∈ ((U : (S.schemeAt (i + 1)).Opens) :
              Set ↥(S.schemeAt (i + 1))) := by
            rw [← Scheme.Opens.range_ι U]
            exact ⟨z, rfl⟩
          have hnc : (S.blowdown i).base (U.ι.base z) ∉
              (((S.ambientCenter i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
                Set ↥(S.schemeAt i)) :=
            (S.mem_ambientCenterSupportCompl i _).mp (hUsub hzU)
          have hin : (S.blowdown i).base (U.ι.base z) ∈
              (((S.strictTransformIdeal i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
                Set ↥(S.schemeAt i)) := hz
          have hrr : Set.range ⇑(S.strictTransformι (i + 1)).base
              = closure (⇑(S.blowdown i).base ⁻¹'
                  ((((S.strictTransformIdeal i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
                      Set ↥(S.schemeAt i)) \
                    (((S.ambientCenter i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
                      Set ↥(S.schemeAt i)))) :=
            EmbeddedBlowupSequence.range_strictTransformι_succ S hN i hi'
          have hx : U.ι.base z ∈ Set.range ⇑(S.strictTransformι (i + 1)).base := by
            rw [hrr]
            exact subset_closure ⟨hin, hnc⟩
          obtain ⟨w, hw⟩ := hx
          refine ⟨w, ?_⟩
          apply U.ι.isOpenEmbedding.injective
          rw [hbase w, hw]
      have hrange2 : Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal
          (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme))).subschemeι.base
            = pre := by
        rw [FunctorialResolution.EmbeddedResolution.range_base_subschemeι,
          AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal]
        rfl
      have : IsReduced
          (Scheme.IdealSheafData.vanishingIdeal
            (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme))).subscheme :=
        AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _ _
      obtain ⟨e, he⟩ := FunctorialResolution.EmbeddedResolution.exists_iso_of_range_base_eq j
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme))).subschemeι
        (hrange1.trans hrange2.symm)
      have ihsub : Smooth
          ((S.strictTransformIdeal i).subschemeι ≫ S.schemeAtToSpec i) := by
        rw [← EmbeddedBlowupSequence.strictTransformι_eq_subschemeι]
        exact ih'
      have hsm2 := smooth_comap_subschemeι_of_isOpenImmersion
        (U.ι ≫ S.blowdown i) (S.strictTransformIdeal i) (S.schemeAtToSpec i) ihsub
      rw [hKvan] at hsm2
      have hlev : S.blowdown i ≫ S.schemeAtToSpec i = S.schemeAtToSpec (i + 1) := by
        rw [EmbeddedBlowupSequence.schemeAtToSpec_eq, EmbeddedBlowupSequence.schemeAtToSpec_eq, ← Category.assoc,
          ← FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_succ]
      have hgoal : S.strictTransformι (i + 1) ≫ S.schemeAtToSpec (i + 1)
          = e.hom ≫ ((Scheme.IdealSheafData.vanishingIdeal
              (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme))).subschemeι
              ≫ ((U.ι ≫ S.blowdown i) ≫ S.schemeAtToSpec i)) := by
        rw [← hj, ← hlev, ← he]
        simp only [Category.assoc]
      rw [hgoal]
      have := hsm2
      infer_instance

theorem smooth_strictTransformι_comp_chartLevelStructureMorphism
    (t : ℕ)
    (ht : t ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length) :
    Smooth
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t ≫
        chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) := by
  have hP : (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAtToSpec t
      = chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t := rfl
  rw [← hP]
  exact smooth_strictTransformι_comp_schemeAtToSpec_consolidated429 hres hB hrad D hsm t ht

theorem disjoint_irreducibleComponents_strictTransform
    (t : ℕ)
    (ht : t ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    {C₁ C₂ : Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t)}
    (h₁ : C₁ ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (h₂ : C₂ ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hne : C₁ ≠ C₂) :
    Disjoint C₁ C₂ :=
  FunctorialResolution.EmbeddedResolution.irreducibleComponentsDisjointOfSmooth k _ _
    (smooth_strictTransformι_comp_chartLevelStructureMorphism hres hB hrad D hsm t ht) C₁ h₁ C₂ h₂ hne

theorem isClopen_of_mem_irreducibleComponents_strictTransform
    (t : ℕ)
    (ht : t ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    {C : Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t)}
    (hC : C ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t)) :
    IsClopen C := by
  have hNoeth : TopologicalSpace.NoetherianSpace
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t) :=
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).noetherianSpace_strictTransform_of_isNoetherian
      (isNoetherian_schemeAt_toEmbeddedBlowupSequence D (canonicalPrincipalization hres hrad)) t ht
  have hsep : ∀ C₁ ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t),
      ∀ C₂ ∈ irreducibleComponents
        ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t),
      (C₁ ∩ C₂).Nonempty → C₁ = C₂ := by
    intro C₁ h₁ C₂ h₂ hx
    by_contra hne
    obtain ⟨x, hx₁, hx₂⟩ := hx
    exact Set.disjoint_left.mp
      (disjoint_irreducibleComponents_strictTransform hres hB hrad D hsm t ht h₁ h₂ hne) hx₁ hx₂
  have hopen : IsOpen (⋃₀ ({C} :
      Set (Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t)))) :=
    FunctorialResolution.EmbeddedResolution.isOpen_sUnion_of_subset_irreducibleComponents hsep (by
      intro C' hC'
      obtain rfl : C' = C := Set.mem_singleton_iff.mp hC'
      exact hC)
  rw [Set.sUnion_singleton] at hopen
  exact ⟨isClosed_of_mem_irreducibleComponents _ hC, hopen⟩

theorem smooth_vanishingIdeal_image_comp_chartLevelStructureMorphism
    (t : ℕ)
    (ht : t ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    (C : Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hC : C ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hCcl : IsClosed
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C)) :
    Smooth
      ((Scheme.IdealSheafData.vanishingIdeal
          (⟨⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C, hCcl⟩ :
            TopologicalSpace.Closeds
              ↥((D.toEmbeddedBlowupSequence
                (canonicalPrincipalization hres hrad)).schemeAt t))).subschemeι ≫
        chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) := by
  have hclopen : IsClopen C :=
    isClopen_of_mem_irreducibleComponents_strictTransform hres hB hrad D hsm t ht hC
  have hsmq : Smooth
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t ≫
        chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) :=
    smooth_strictTransformι_comp_chartLevelStructureMorphism hres hB hrad D hsm t ht
  have hPlevel : (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAtToSpec t
      = chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t := rfl
  have hftq : LocallyOfFiniteType
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t ≫
        chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) := by
    have h1 :=
      (D.toEmbeddedBlowupSequence
        (canonicalPrincipalization hres hrad)).locallyOfFiniteType_strictTransformToSpec t ht
    rw [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.strictTransformToSpec_eq, hPlevel] at h1
    exact h1
  have hsub := FunctorialResolution.EmbeddedResolution.smooth_subschemeι_vanishingIdeal_comp_of_isClopen
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t ≫
        chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) C hclopen
  have : IsReduced
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨C, hclopen.isClosed⟩ :
          TopologicalSpace.Closeds
            ↥((D.toEmbeddedBlowupSequence
              (canonicalPrincipalization hres hrad)).strictTransform t))).subscheme :=
    AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _ _
  have : IsReduced
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C, hCcl⟩ :
          TopologicalSpace.Closeds
            ↥((D.toEmbeddedBlowupSequence
              (canonicalPrincipalization hres hrad)).schemeAt t))).subscheme :=
    AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _ _
  have hrange :
      Set.range ⇑((Scheme.IdealSheafData.vanishingIdeal
            (⟨C, hclopen.isClosed⟩ :
              TopologicalSpace.Closeds
                ↥((D.toEmbeddedBlowupSequence
                  (canonicalPrincipalization hres hrad)).strictTransform t))).subschemeι ≫
          (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base
        = Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal
            (⟨⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
                C, hCcl⟩ :
              TopologicalSpace.Closeds
                ↥((D.toEmbeddedBlowupSequence
                  (canonicalPrincipalization hres hrad)).schemeAt t))).subschemeι.base := by
    rw [Scheme.Hom.range_comp_base, FunctorialResolution.EmbeddedResolution.range_base_subschemeι,
      FunctorialResolution.EmbeddedResolution.range_base_subschemeι,
      AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal,
      AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨e, he⟩ := FunctorialResolution.EmbeddedResolution.exists_iso_of_range_base_eq _ _ hrange
  exact smooth_comp_of_iso_hom_eq e _ _ _ _ he hsub


end

private theorem agreeNear_vanishingIdeal_image_of_forall_avoidsCenters_of_disjoint_consolidated429
    {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [IsAffine Y] [IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]
    [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u})
    (hClearAll : ∀ (s : ℕ), s ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ y : ↥((D.toEmbeddedBlowupSequence A).strictTransform s),
        (D.toEmbeddedBlowupSequence A).AvoidsCenters s (((D.toEmbeddedBlowupSequence A).strictTransformι s).base y))
    (hDisjAll : ∀ (s : ℕ), s ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ C₁ C₂ : Set ↥((D.toEmbeddedBlowupSequence A).strictTransform s),
        C₁ ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform s) →
        C₂ ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform s) →
        C₁ ≠ C₂ → Disjoint C₁ C₂) :
    ∀ (t : ℕ), t ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ C : Set ↥((D.toEmbeddedBlowupSequence A).strictTransform t),
        C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform t) →
        ∀ hCcl : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C),
        ∀ x : ↥((D.toEmbeddedBlowupSequence A).schemeAt t),
          x ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C →
          AgreeNear ((principalizationOfEmbedding k Y pY D A).ideal t)
            (Scheme.IdealSheafData.vanishingIdeal
              (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C, hCcl⟩ :
                TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt t))) x := by
  intro t
  induction t with
  | zero =>
    intro _ C hC hCcl x hx
    classical
    have hNoeth : TopologicalSpace.NoetherianSpace ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) :=
      (D.toEmbeddedBlowupSequence A).noetherianSpace_strictTransform_of_isNoetherian (isNoetherian_schemeAt_toEmbeddedBlowupSequence D A) 0
        (Nat.zero_le _)
    have hemb := (D.toEmbeddedBlowupSequence A).isClosedEmbedding_strictTransformι 0
    have hclr : IsClosed (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base) := hemb.isClosed_range
    have hid0 := principalizationOfEmbedding_ideal_zero_eq_vanishingIdeal D A hclr
    obtain ⟨Bad, hBaddef⟩ : ∃ B : Set ↥((D.toEmbeddedBlowupSequence A).schemeAt 0),
        B = ⋃ C'' ∈ (irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) \ {C}),
          ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C'' := ⟨_, rfl⟩
    have hfin : (irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) \ {C}).Finite :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset Set.sdiff_subset
    have hBadcl : IsClosed Bad := by
      rw [hBaddef]
      exact hfin.isClosed_biUnion fun C'' hC'' =>
        hemb.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ hC''.1)
    have hxU : x ∈ Badᶜ := by
      intro hmem
      rw [hBaddef] at hmem
      obtain ⟨C'', hC''D, hxim⟩ := Set.mem_iUnion₂.mp hmem
      obtain ⟨z, hzC'', hz⟩ := hxim
      obtain ⟨w, hwC, hw⟩ := hx
      have hzw : z = w := hemb.injective (hz.trans hw.symm)
      rw [hzw] at hzC''
      have hne : C'' ≠ C := fun h => hC''D.2 (Set.mem_singleton_iff.mpr h)
      exact Set.disjoint_left.mp
        (hDisjAll 0 (Nat.zero_le _) C'' C hC''D.1 hC hne) hzC'' hwC
    have hinter : (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base) ∩ Badᶜ
        = (⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C) ∩ Badᶜ := by
      ext z
      constructor
      · rintro ⟨⟨w, rfl⟩, hz⟩
        refine ⟨?_, hz⟩
        by_cases hw : w ∈ C
        · exact ⟨w, hw, rfl⟩
        · refine absurd ?_ hz
          rw [hBaddef]
          refine Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents w, ?_⟩
            ⟨w, mem_irreducibleComponent, rfl⟩
          intro h
          exact hw (h ▸ mem_irreducibleComponent)
      · rintro ⟨⟨w, hwC, rfl⟩, hz⟩
        exact ⟨⟨w, rfl⟩, hz⟩
    rw [hid0]
    exact agreeNear_vanishingIdeal_of_inter_eq _ _ ⟨Badᶜ, hBadcl.isOpen_compl⟩ _ hxU hinter
  | succ i ih =>
    intro hi C hC hCcl x hx
    classical
    have hN := isNoetherian_schemeAt_toEmbeddedBlowupSequence D A
    have hi' : i < (D.toEmbeddedBlowupSequence A).length := Nat.lt_of_succ_le hi
    have hilt : i < (principalizationOfEmbedding k Y pY D A).length := hi'
    obtain ⟨η, hηgen⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents _ hC)
    obtain ⟨C', hC'm, hη', _⟩ :=
      (D.toEmbeddedBlowupSequence A).exists_irreducibleComponent_isGenericPoint_strictTransformMap hN i hi' C hC η hηgen
    have hC'cl : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C') :=
      ((D.toEmbeddedBlowupSequence A).isClosedEmbedding_strictTransformι i).isClosedMap _
        (isClosed_of_mem_irreducibleComponents _ hC'm)
    obtain ⟨y, hyC, hxy⟩ := hx
    have hclx : (D.toEmbeddedBlowupSequence A).AvoidsCenters (i + 1) x := by
      rw [← hxy]
      exact hClearAll (i + 1) hi y
    have hnot := (((D.toEmbeddedBlowupSequence A).avoidsCenters_succ_iff i x).mp hclx).1
    have hblow : ((D.toEmbeddedBlowupSequence A).blowdown i).base x ∈
        ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' :=
      EmbeddedBlowupSequence.mem_image_strictTransformι_of_mem_image_succ (D.toEmbeddedBlowupSequence A) i C η hηgen
        C' hη' x ⟨y, hyC, hxy⟩
    obtain ⟨V, hxV, hVeq⟩ := (agreeNear_iff _ _ _).mp
      (ih (Nat.le_of_succ_le hi) C' hC'm hC'cl _ hblow)
    obtain ⟨V', hV'⟩ : ∃ V' : ((D.toEmbeddedBlowupSequence A).schemeAt i).Opens, V' = V := ⟨V, rfl⟩
    have hxV' : ((D.toEmbeddedBlowupSequence A).blowdown i).base x ∈ V' := by
      rw [hV']; exact hxV
    have hV'eq : ((principalizationOfEmbedding k Y pY D A).ideal i).comap V'.ι
        = (Scheme.IdealSheafData.vanishingIdeal
            (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ :
              TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap V'.ι := by
      rw [hV']; exact hVeq
    obtain ⟨U, hUdef⟩ : ∃ U : ((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)).Opens,
        U = (TopologicalSpace.Opens.map ((D.toEmbeddedBlowupSequence A).blowdown i).base).obj
          (V' ⊓ (D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i) := ⟨_, rfl⟩
    have hUsub : (U : Set ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1))) ⊆
        ⇑((D.toEmbeddedBlowupSequence A).blowdown i).base ⁻¹'
          (((D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i : ((D.toEmbeddedBlowupSequence A).schemeAt i).Opens) :
            Set ↥((D.toEmbeddedBlowupSequence A).schemeAt i)) := by
      rw [hUdef]
      intro z hz
      exact hz.2
    have hmemU : ∀ z : ↥U, ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base z) ∉
        (((D.toEmbeddedBlowupSequence A).ambientCenter i).support :
          Set ↥((D.toEmbeddedBlowupSequence A).schemeAt i)) := by
      intro z
      exact hUsub z.2
    have hxU : x ∈ U := by
      rw [hUdef]
      exact ⟨hxV', ((D.toEmbeddedBlowupSequence A).mem_ambientCenterSupportCompl i _).mpr hnot⟩
    have : IsOpenImmersion (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) :=
      EmbeddedBlowupSequence.isOpenImmersion_ι_comp_blowdown (D.toEmbeddedBlowupSequence A) i hi' U hUsub
    have hexc : ((principalizationOfEmbedding k Y pY D A).exceptionalIdeal i).comap U.ι = ⊤ := by
      refine FunctorialResolution.EmbeddedResolution.comap_ι_eq_top_of_disjoint _ _ ?_
      rw [Set.disjoint_left]
      intro z hz hmem
      rw [(principalizationOfEmbedding k Y pY D A).exceptionalIdeal_eq i] at hmem
      exact absurd (mem_support_of_mem_support_comap
        ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i) _ z hmem) (hUsub hz)
    have hJ : ((principalizationOfEmbedding k Y pY D A).ideal (i + 1)).comap U.ι
        = ((principalizationOfEmbedding k Y pY D A).ideal i).comap
            (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) :=
      comap_eq_comap_comp_of_mul_eq _ U _ _ _
        ((principalizationOfEmbedding k Y pY D A).ideal_succ i hilt) hexc
    have hle : U ≤ (TopologicalSpace.Opens.map
        ((D.toEmbeddedBlowupSequence A).blowdown i).base).obj V' := by
      rw [hUdef]
      intro z hz
      exact hz.1
    have hcomapφ : ((principalizationOfEmbedding k Y pY D A).ideal i).comap
          (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i)
        = (Scheme.IdealSheafData.vanishingIdeal
            (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ :
              TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap
            (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) :=
      AlgebraicGeometry.Scheme.IdealSheafData.comap_ι_comp_eq_of_comap_ι_eq
        ((D.toEmbeddedBlowupSequence A).blowdown i) V' U hle _ _ hV'eq
    have hLHS : (Scheme.IdealSheafData.vanishingIdeal
          (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ :
            TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap
          (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i)
        = Scheme.IdealSheafData.vanishingIdeal
            (FunctorialResolution.EmbeddedResolution.closedPreimage U.ι
              (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C, hCcl⟩ :
                TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)))) := by
      refine FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq
        (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) _ _ ?_
      ext z
      have hcb : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base z
          = ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base z) := rfl
      have hiff := EmbeddedBlowupSequence.mem_image_strictTransformι_iff_of_notMem_ambientCenter
        (D.toEmbeddedBlowupSequence A) hN i hi' C η hηgen C' hη' (U.ι.base z) (hmemU z)
      constructor
      · intro hz
        have hz1 : U.ι.base z ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C := hz
        have hz2 : ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base z)
            ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := hiff.mpr hz1
        have hz3 : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base z
            ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := by
          rw [hcb]; exact hz2
        exact hz3
      · intro hz
        have hz1 : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base z
            ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := hz
        have hz2 : ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base z)
            ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := by
          rw [← hcb]; exact hz1
        exact hiff.mp hz2
    refine (agreeNear_iff _ _ _).mpr ⟨U, hxU, ?_⟩
    exact hJ.trans (hcomapφ.trans (hLHS.trans
      (FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion U.ι
        (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C, hCcl⟩ :
          TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)))).symm))

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension) (hrad : SmoothSubschemeIdealIsRadical.{u}) {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y] [IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]
include hB

theorem agreeNear_ideal_vanishingIdeal_image_of_smooth
    [QuasiCompact pY] (D : EmbeddingDatum k Y pY)
    (hsm : Smooth pY) (t : ℕ)
    (ht : t ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    (C : Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hC : C ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hCcl : IsClosed
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C))
    (x : ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t))
    (hx : x ∈ ⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C) :
    AgreeNear ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t)
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C, hCcl⟩ :
          TopologicalSpace.Closeds
            ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t))) x :=
  agreeNear_vanishingIdeal_image_of_forall_avoidsCenters_of_disjoint_consolidated429 D (canonicalPrincipalization hres hrad)
    (fun s hs y => avoidsCenters_strictTransformι_of_smooth hres hB hrad D hsm s hs y)
    (fun s hs _C₁ _C₂ h₁ h₂ hne =>
      disjoint_irreducibleComponents_strictTransform hres hB hrad D hsm s hs h₁ h₂ hne)
    t ht C hC hCcl x hx

theorem mem_detachedLocus_of_mem_support_ambientCenter
    (D : EmbeddingDatum k Y pY)
    (hsm : Smooth pY) (t : ℕ)
    (ht : t < (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    (y : ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hy : ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base y ∈
      ((((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).ambientCenter t).support) :
        Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t))) :
    y ∈ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedLocus t := by
  classical
  have hqc : QuasiCompact pY := inferInstance
  refine subset_detachedLocus_of_mem_detachedComponents
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)) t ?_ mem_irreducibleComponent
  rw [EmbeddedBlowupSequence.mem_detachedComponents]
  refine ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩
  by_contra hsub
  have hCmem : irreducibleComponent y ∈
      irreducibleComponents
        ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t) :=
    irreducibleComponent_mem_irreducibleComponents y
  have hCfr : irreducibleComponent y ∉
      (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedComponents t := by
    intro hmem
    exact hsub
      (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).mem_detachedComponents t
        (irreducibleComponent y)).1 hmem).2
  have hCcl : IsClosed (irreducibleComponent y) :=
    isClosed_of_mem_irreducibleComponents _ hCmem
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hCmem.1 hCcl
  have hemb : Topology.IsClosedEmbedding
      ⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base :=
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).isClosedEmbedding_strictTransformι t
  have himcl : IsClosed (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
      irreducibleComponent y) := hemb.isClosedMap _ hCcl
  have himirr : IsIrreducible
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
        irreducibleComponent y) := hCmem.1.image _ hemb.continuous.continuousOn
  have hgim : IsGenericPoint
      (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ξ)
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
        irreducibleComponent y) :=
    FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding hemb hξ
  have hxi : ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ξ ∉
      ((((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).ambientCenter t).support) :
        Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t)) :=
    (D.toEmbeddedBlowupSequence
      (canonicalPrincipalization hres hrad)).notMem_ambientCenter_support_of_isGenericPoint t
      (irreducibleComponent y) hCmem hCfr ξ hξ
  have hagreeId : ∀ x ∈
        (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
          irreducibleComponent y),
      AgreeNear ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t)
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
              irreducibleComponent y, himcl⟩ :
            TopologicalSpace.Closeds
              ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t))) x := by
    intro x hx
    exact agreeNear_ideal_vanishingIdeal_image_of_smooth hres hB hrad D hsm t (le_of_lt ht)
      (irreducibleComponent y) hCmem himcl x hx
  have hsubsupp : (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
        irreducibleComponent y) ⊆
      ((((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t).support) :
        Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t)) := by
    refine subset_support_of_agreeNear idealSheafGeometryHypotheses_vanishingIdealAssignment _ _ _ himcl ?_
    intro x hx
    rw [vanishingIdealAssignment_apply]
    exact hagreeId x hx
  have hnz : FunctorialResolution.EmbeddedResolution.NonzeroOnComponents
      ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t) :=
    nonzeroOnComponents_ideal (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad))
      D.nonzeroOnComponents_ker t (le_of_lt ht)
  have hcomp : ∀ E ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t),
      ¬ E ⊆ (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
        irreducibleComponent y) := by
    intro E hE hEsub
    exact (FunctorialResolution.EmbeddedResolution.nonzeroOnComponents_iff _).1 hnz E hE (hEsub.trans hsubsupp)
  have hdisj : Disjoint
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
        irreducibleComponent y)
      (⋃ E ∈ (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).boundary t,
        (E.support :
          Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t))) := by
    rw [Set.disjoint_left]
    rintro a ⟨z, hz, rfl⟩ ha
    obtain ⟨E, hE, haE⟩ := Set.mem_iUnion₂.mp ha
    exact strictTransformι_notMem_support_of_mem_boundary hres hB hrad D hsm t (le_of_lt ht) z E hE haE
  have hspec := (PrincipalizationRules.isMaxOrderReduction_outputLevelData (canonicalAlgorithmRules hres) hB
      (krullDimSucc D.ambient)).cert
      (markedTripleOrderOne k D.ambient D.ambientStruct (AlgebraicGeometry.Scheme.Hom.ker D.emb) [])
      (markedTripleOrderOne_isAdmissible k D.ambient D.ambientStruct
        (AlgebraicGeometry.Scheme.Hom.ker D.emb) D.nonzeroOnComponents_ker [] D.sncEmpty)
      (le_of_eq (markedTripleOrderOne_dim k D.ambient D.ambientStruct
        (AlgebraicGeometry.Scheme.Hom.ker D.emb) []))
      t ht
  have hcert : FunctorialResolution.EmbeddedResolution.PrincipalizationCertificate
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t)
      (chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t)
      ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t) 1
      (⋃ E ∈ (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).boundary t,
        (E.support :
          Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t)))
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).ambientCenter t) := hspec
  have hp : Smooth
      (chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) := by
    rw [chartLevelStructureMorphism_eq_structureMorphism]
    exact IdealBlowupSequence.smooth_structureMorphism
      (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)) t (le_of_lt ht)
  exact false_of_mem_support_center
    (chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) hp
    ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t)
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).ambientCenter t)
    (⋃ E ∈ (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).boundary t,
      (E.support :
        Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t)))
    hcert
    (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
      irreducibleComponent y)
    himcl himirr
    (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ξ)
    (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base y)
    hgim ⟨y, mem_irreducibleComponent, rfl⟩
    (smooth_vanishingIdeal_image_comp_chartLevelStructureMorphism hres hB hrad D hsm t (le_of_lt ht)
      (irreducibleComponent y) hCmem himcl)
    hcomp hxi hdisj hagreeId hy


end

end OpenImmersionRestriction

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DiscardedComponents
section

open TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

private theorem subset_or_subset_of_isIrreducible_consolidated371 {W : Type*} [TopologicalSpace W] {s a b : Set W}
    (hs : IsIrreducible s) (ha : IsClosed a) (hb : IsClosed b) (h : s ⊆ a ∪ b) :
    s ⊆ a ∨ s ⊆ b :=
  isPreirreducible_iff_isClosed_union_isClosed.mp hs.2 a b ha hb h

section
variable {W : Type*} [TopologicalSpace W] {s : Set W} (hs : IsIrreducible s)
include hs

private theorem exists_mem_finset_subset_of_isIrreducible_consolidated371 (F : Finset (Set W))
    (hcl : ∀ Z ∈ F, IsClosed Z) (hsub : s ⊆ ⋃₀ (F : Set (Set W))) :
    ∃ Z ∈ F, s ⊆ Z := by
  classical
  revert hcl hsub
  refine Finset.induction_on F ?_ ?_
  · intro _ hsub'
    obtain ⟨x, hx⟩ := hs.1
    have hx' := hsub' hx
    simp at hx'
  · intro a G _ ih hcl' hsub'
    have hcla : IsClosed a := hcl' a (Finset.mem_insert_self a G)
    have hclG : ∀ Z ∈ G, IsClosed Z := fun Z hZ => hcl' Z (Finset.mem_insert_of_mem hZ)
    have hclU : IsClosed (⋃₀ ((G : Finset (Set W)) : Set (Set W))) := by
      rw [Set.sUnion_eq_biUnion]
      exact Set.Finite.isClosed_biUnion G.finite_toSet (fun Z hZ => hclG Z hZ)
    have hsub2 : s ⊆ a ∪ ⋃₀ ((G : Finset (Set W)) : Set (Set W)) := by
      intro y hy
      have hy' := hsub' hy
      rw [Finset.coe_insert, Set.sUnion_insert] at hy'
      exact hy'
    rcases subset_or_subset_of_isIrreducible_consolidated371 hs hcla hclU hsub2 with hh | hh
    · exact ⟨a, Finset.mem_insert_self a G, hh⟩
    · obtain ⟨Z, hZ, hZs⟩ := ih hclG hh
      exact ⟨Z, Finset.mem_insert_of_mem hZ, hZs⟩

theorem exists_mem_of_isIrreducible_subset_sUnion {F : Set (Set W)} (hF : F.Finite)
    (hcl : ∀ Z ∈ F, IsClosed Z) (hsub : s ⊆ ⋃₀ F) :
    ∃ Z ∈ F, s ⊆ Z := by
  classical
  obtain ⟨Z, hZ, hsZ⟩ :=
    exists_mem_finset_subset_of_isIrreducible_consolidated371 hs hF.toFinset
      (fun Z hZ => hcl Z (hF.mem_toFinset.mp hZ))
      (by
        intro y hy
        obtain ⟨Z, hZF, hyZ⟩ := hsub hy
        refine ⟨Z, ?_, hyZ⟩
        simpa only [Finset.mem_coe, Set.Finite.mem_toFinset] using hZF)
  exact ⟨Z, hF.mem_toFinset.mp hZ, hsZ⟩


end

section
variable {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] {f : X → Z} (hf : Topology.IsClosedEmbedding f)
include hf

private theorem exists_isOpen_preimage_eq_consolidated371 {u : Set X} (hu : IsOpen u) :
    ∃ U : Set Z, IsOpen U ∧ f ⁻¹' U = u :=
  hf.isInducing.isOpen_iff.mp hu

theorem isPreirreducible_preimage_of_isClosedEmbedding {t : Set Z}
    (hran : t ⊆ Set.range f) (ht : IsPreirreducible t) :
    IsPreirreducible (f ⁻¹' t) := by
  intro u v hu hv hsu hsv
  obtain ⟨U, hU, hUeq⟩ := exists_isOpen_preimage_eq_consolidated371 hf hu
  obtain ⟨V, hV, hVeq⟩ := exists_isOpen_preimage_eq_consolidated371 hf hv
  obtain ⟨x, hxt, hxu⟩ := hsu
  obtain ⟨y, hyt, hyv⟩ := hsv
  have hxU : f x ∈ U := by
    have hx' : x ∈ f ⁻¹' U := by rw [hUeq]; exact hxu
    exact hx'
  have hyV : f y ∈ V := by
    have hy' : y ∈ f ⁻¹' V := by rw [hVeq]; exact hyv
    exact hy'
  obtain ⟨z, hzt, hzU, hzV⟩ := ht U V hU hV ⟨f x, hxt, hxU⟩ ⟨f y, hyt, hyV⟩
  obtain ⟨w, rfl⟩ := hran hzt
  refine ⟨w, hzt, ?_, ?_⟩
  · have hw : w ∈ f ⁻¹' U := hzU
    rw [hUeq] at hw
    exact hw
  · have hw : w ∈ f ⁻¹' V := hzV
    rw [hVeq] at hw
    exact hw

theorem isIrreducible_preimage_of_isClosedEmbedding {t : Set Z}
    (hran : t ⊆ Set.range f) (ht : IsIrreducible t) :
    IsIrreducible (f ⁻¹' t) := by
  refine ⟨?_, isPreirreducible_preimage_of_isClosedEmbedding hf hran ht.2⟩
  obtain ⟨z, hz⟩ := ht.1
  obtain ⟨w, rfl⟩ := hran hz
  exact ⟨w, hz⟩


end

section
variable (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY] [QuasiCompact pY] [IsReduced Y] [IsAffine Y] (i : ℕ)

theorem discardedComponents_subset_irreducibleComponents :
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedComponents i ⊆
      irreducibleComponents ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransform i) := by
  intro C hC
  exact (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).mem_discardedComponents_iff i C).mp hC).1

theorem isClosedEmbedding_discardedι :
    Topology.IsClosedEmbedding ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base :=
  AlgebraicGeometry.Scheme.Hom.isClosedEmbedding
    ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedIdeal i).subschemeι

theorem range_discardedι_eq_sUnion_discardedComponents (hi : i < (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength) :
    Set.range ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base =
      ⋃₀ ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedComponents i) := by
  have hNoeth : TopologicalSpace.NoetherianSpace
      ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransform i) :=
    EmbeddedBlowupSequence.noetherianSpace_strictTransform_of_isNoetherian ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A)
      (OpenImmersionRestriction.isNoetherian_schemeAt_toEmbeddedBlowupSequence (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) A) i
      (le_of_lt hi)
  have h1 : Set.range ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base =
      (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedIdeal i).support :
        Set ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransform i)) :=
    AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι
      ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedIdeal i)
  rw [h1, AffineSpacePrincipalizationData.discardedIdeal_eq_vanishingIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    AffineSpacePrincipalizationData.coe_discardedLocusClosure, AffineSpacePrincipalizationData.discardedLocus_eq_sUnion_discardedComponents]


end

section
variable (A : PrincipalizationAlgorithm.{u})

theorem affineStrictTransformEmptyAtLast_of_isFunctorialPrincipalization (hA : IsFunctorialPrincipalization A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) :
    AffineStrictTransformEmptyAtLast A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  show (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformIdeal
      (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength = ⊤
  have htop : (OpenImmersionRestriction.principalizationOfEmbedding k Y pY (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) A).ideal
      ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A).length = ⊤ := by
    have h := hA.lastIdeal_eq_top k (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambient
      (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambientStruct
      (AlgebraicGeometry.Scheme.Hom.ker (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).emb)
      (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).nonzeroOnComponents_ker
      ([] : List (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambient.IdealSheafData)
      (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).sncEmpty
    rw [IdealBlowupSequence.lastIdeal_eq] at h
    exact h
  have hno : ∀ C : Set ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransform
        (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength),
      C ∉ irreducibleComponents ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransform
        (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength) := by
    intro C hC
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents _ hC)
    have himgCl : IsClosed (⇑(((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A).strictTransformι
        ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A).length).base '' C) :=
      (EmbeddedBlowupSequence.isClosedEmbedding_strictTransformι
        ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A) _).isClosedMap _
        (isClosed_of_mem_irreducibleComponents _ hC)
    obtain ⟨-, hord⟩ := OpenImmersionRestriction.agreesWithComponentsOrderOne_of_le (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) A
      ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A).length le_rfl C hC ξ hξ himgCl
    rw [htop] at hord
    have h01 : (0 : ℕ∞) = 1 := (orderAt_top _).symm.trans hord
    simp at h01
  have : IsEmpty ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransform
      (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength) := by
    constructor
    intro x
    exact hno (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x)
  have hsupp : (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformIdeal
      (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength).support :
      Set ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel
        (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength)) = ∅ := by
    rw [← AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι]
    exact Set.range_eq_empty _
  exact (Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).mpr hsupp

theorem affineDetachedComponentsNotInBoundary (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) :
    AffineDetachedComponentsNotInBoundary A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _ i hi j hj C hC hsubset
  have hle : i ≤ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength := le_of_lt hi
  have hNoeth : TopologicalSpace.NoetherianSpace
      ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransform i) :=
    EmbeddedBlowupSequence.noetherianSpace_strictTransform_of_isNoetherian ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A)
      (OpenImmersionRestriction.isNoetherian_schemeAt_toEmbeddedBlowupSequence (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) A) i hle
  have hfemb : Topology.IsClosedEmbedding
      ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base :=
    isClosedEmbedding_discardedι A hemb hsnc hsm k Y pY i
  have hrange : Set.range ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base =
      ⋃₀ ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedComponents i) :=
    range_discardedι_eq_sUnion_discardedComponents A hemb hsnc hsm k Y pY i hi
  have hsubComp : (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedComponents i ⊆
      irreducibleComponents ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransform i) :=
    discardedComponents_subset_irreducibleComponents A hemb hsnc hsm k Y pY i
  have hfin : ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedComponents i).Finite :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).subset hsubComp
  have hCirr : IsIrreducible C := hC.1
  have himgIrr :
      IsIrreducible (⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base '' C) :=
    hCirr.image _ hfemb.continuous.continuousOn
  obtain ⟨C₀, hC₀mem, hC₀sub⟩ :=
    exists_mem_of_isIrreducible_subset_sUnion himgIrr hfin
      (fun Z hZ => isClosed_of_mem_irreducibleComponents _ (hsubComp hZ))
      (by rw [← hrange]; exact Set.image_subset_range _ _)
  have hC₀ic : C₀ ∈ irreducibleComponents
      ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransform i) := hsubComp hC₀mem
  have hC₀range :
      C₀ ⊆ Set.range ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base := by
    rw [hrange]
    exact Set.subset_sUnion_of_mem hC₀mem
  have hpre : IsIrreducible
      (⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base ⁻¹' C₀) :=
    isIrreducible_preimage_of_isClosedEmbedding hfemb hC₀range hC₀ic.1
  have hCsub : C ⊆ ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base ⁻¹' C₀ :=
    fun z hz => hC₀sub ⟨z, hz, rfl⟩
  have hCeq : ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base ⁻¹' C₀ ⊆ C :=
    hC.2 hpre hCsub
  have himg : ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base '' C = C₀ := by
    refine Set.Subset.antisymm hC₀sub ?_
    intro z hz
    obtain ⟨w, rfl⟩ := hC₀range hz
    exact ⟨w, hCeq hz, rfl⟩
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hC₀ic.1 (isClosed_of_mem_irreducibleComponents _ hC₀ic)
  have hξmem : ξ ∈ ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base '' C := by
    rw [himg]
    exact hξ.mem
  obtain ⟨w, hwC, hw⟩ := hξmem
  have hmem : ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base ξ ∈
      ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i ≫
        (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base '' C := by
    refine ⟨w, hwC, ?_⟩
    show ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base
        (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base w) =
      ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base ξ
    rw [hw]
  have hx := hsubset hmem
  have hclear := EmbeddedBlowupSequence.avoidsCenters_strictTransformι_of_isGenericPoint
    ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A)
    (OpenImmersionRestriction.isNoetherian_schemeAt_toEmbeddedBlowupSequence (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) A) i hle
    C₀ hC₀ic ξ hξ
  exact OpenImmersionRestriction.not_avoidsCenters_of_mem_boundary_support (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) A i hle
    (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).boundary i).get ⟨j, hj⟩)
    (List.get_mem ..) _ hx hclear


end

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SmoothLocusPreimageDense
section

open TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Type*} [TopologicalSpace X]

theorem dense_of_forall_mem_of_isGenericPoint [QuasiSober X]
    {V : Set X} (h : ∀ C ∈ irreducibleComponents X, ∀ η : X, IsGenericPoint η C → η ∈ V) :
    Dense V := by
  intro x
  obtain ⟨η, hη⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := x))
    isClosed_irreducibleComponent
  have hmem : η ∈ V := h _ (irreducibleComponent_mem_irreducibleComponents x) η hη
  have hx : x ∈ closure ({η} : Set X) := by
    have hη' : closure ({η} : Set X) = irreducibleComponent x := hη
    rw [hη']
    exact mem_irreducibleComponent
  exact closure_mono (Set.singleton_subset_iff.mpr hmem) hx

theorem mem_of_isGenericPoint_of_isOpen_of_dense [TopologicalSpace.NoetherianSpace X] {U : Set X} (hUo : IsOpen U) (hUd : Dense U)
    {C : Set X} (hC : C ∈ irreducibleComponents X) {η : X} (hη : IsGenericPoint η C) :
    η ∈ U := by
  obtain ⟨y, hyC, hyU⟩ := nonempty_inter_of_dense_of_mem_irreducibleComponents hUd hC
  have hy : y ∈ closure ({η} : Set X) := by
    have hη' : closure ({η} : Set X) = C := hη
    rw [hη']
    exact hyC
  obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp hy U hUo hyU
  rw [Set.mem_singleton_iff] at hz
  exact hz ▸ hzU


end

section
variable {X W : Type*} [TopologicalSpace X] [TopologicalSpace W] {f : X → W}

theorem isGenericPoint_image_of_isClosed (hf : Continuous f) {C : Set X} {η : X} (hη : IsGenericPoint η C)
    (hcl : IsClosed (f '' C)) :
    IsGenericPoint (f η) (f '' C) := by
  have hη' : closure ({η} : Set X) = C := hη
  have hηC : η ∈ C := by
    rw [← hη']
    exact subset_closure (Set.mem_singleton_iff.mpr rfl)
  show closure ({f η} : Set W) = f '' C
  apply Set.Subset.antisymm
  · exact hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨η, hηC, rfl⟩)
  · have hcont : f '' closure ({η} : Set X) ⊆ closure (f '' ({η} : Set X)) :=
      image_closure_subset_closure_image hf
    rw [Set.image_singleton] at hcont
    rw [← hη']
    exact hcont

theorem exists_isGenericPoint_image_of_isClosedEmbedding (hf : Topology.IsClosedEmbedding f) {F : Set (Set W)}
    (hF : ∀ Z ∈ F, Z ∈ irreducibleComponents W) (hun : ⋃₀ F = Set.range f)
    {C : Set X} (hC : C ∈ irreducibleComponents X) {η : X} (hη : IsGenericPoint η C) :
    ∃ Z ∈ F, IsGenericPoint (f η) Z := by
  have hη' : closure ({η} : Set X) = C := hη
  have hmem : f η ∈ ⋃₀ F := by
    rw [hun]
    exact ⟨η, rfl⟩
  obtain ⟨Z, hZF, hZ⟩ := hmem
  refine ⟨Z, hZF, ?_⟩
  have hZcomp : Z ∈ irreducibleComponents W := hF Z hZF
  have hZcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZcomp
  have hZran : Z ⊆ Set.range f := by
    intro w hw
    rw [← hun]
    exact ⟨Z, hZF, hw⟩
  have hpre : IsIrreducible (f ⁻¹' Z) :=
    isIrreducible_preimage_of_isClosedEmbedding hf hZran hZcomp.1
  have hsub : C ⊆ f ⁻¹' Z := by
    rw [← hη']
    exact (hZcl.preimage hf.continuous).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hZ)
  have heq : f ⁻¹' Z = C := Set.Subset.antisymm (hC.2 hpre hsub) hsub
  have himg : f '' C = Z := by
    rw [← heq, Set.image_preimage_eq_of_subset hZran]
  have hgen : IsGenericPoint (f η) (f '' C) :=
    isGenericPoint_image_of_isClosed hf.continuous hη (by rw [himg]; exact hZcl)
  rwa [himg] at hgen

theorem exists_isGenericPoint_image_of_isOpenEmbedding (hf : Topology.IsOpenEmbedding f)
    {C : Set X} (hC : C ∈ irreducibleComponents X) {η : X} (hη : IsGenericPoint η C) :
    ∃ D ∈ irreducibleComponents W, IsGenericPoint (f η) D := by
  have hη' : closure ({η} : Set X) = C := hη
  have hmax : ∀ E : Set W, IsIrreducible E → closure ({f η} : Set W) ⊆ E →
      E ⊆ closure ({f η} : Set W) := by
    intro E hE hsub
    have hfηE : f η ∈ E := hsub (subset_closure (Set.mem_singleton_iff.mpr rfl))
    have hne : (E ∩ Set.range f).Nonempty := ⟨f η, hfηE, ⟨η, rfl⟩⟩
    have hEsub : E ⊆ closure (E ∩ Set.range f) :=
      subset_closure_inter_of_isPreirreducible_of_isOpen hE.2 hf.isOpen_range hne
    have hpre : IsPreirreducible (f ⁻¹' E) := hE.2.preimage hf
    have hηpre : η ∈ f ⁻¹' E := hfηE
    have hirrcl : IsIrreducible (closure (f ⁻¹' E)) :=
      ⟨⟨η, subset_closure hηpre⟩, hpre.closure⟩
    have hCsub : C ⊆ closure (f ⁻¹' E) := by
      rw [← hη']
      exact closure_mono (Set.singleton_subset_iff.mpr hηpre)
    have hback : closure (f ⁻¹' E) ⊆ C := hC.2 hirrcl hCsub
    have h1 : E ∩ Set.range f ⊆ f '' C := by
      rintro w ⟨hwE, x, rfl⟩
      exact ⟨x, hback (subset_closure hwE), rfl⟩
    have h2 : f '' C ⊆ closure ({f η} : Set W) := by
      have hcont : f '' closure ({η} : Set X) ⊆ closure (f '' ({η} : Set X)) :=
        image_closure_subset_closure_image hf.continuous
      rw [Set.image_singleton] at hcont
      rw [← hη']
      exact hcont
    calc E ⊆ closure (E ∩ Set.range f) := hEsub
      _ ⊆ closure (f '' C) := closure_mono h1
      _ ⊆ closure (closure ({f η} : Set W)) := closure_mono h2
      _ = closure ({f η} : Set W) := closure_closure
  exact ⟨closure ({f η} : Set W),
    ⟨isIrreducible_singleton.closure, fun E hE hsub => hmax E hE hsub⟩, rfl⟩


end

section
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]

theorem isOpenImmersion_strictTransformZeroToBase (S : AffineSpacePrincipalizationData k Y pY) :
    IsOpenImmersion S.strictTransformZeroToBase := by
  have h0 : CategoryTheory.IsIso
      (Limits.coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) :=
    (Limits.coprod.rightUnitor (S.strictTransform 0)).isIso_inv
  have hiso : CategoryTheory.IsIso S.strictTransformZeroToBase := by
    rw [AffineSpacePrincipalizationData.strictTransformZeroToBase_def]
    infer_instance
  infer_instance

private theorem exists_isGenericPoint_strictTransformToZero_consolidated399 [IsReduced Y]
    (S : AffineSpacePrincipalizationData k Y pY)
    (hN : ∀ j ≤ S.ambientLength, IsNoetherian (S.ambientLevel j)) (n : ℕ) :
    n ≤ S.ambientLength → ∀ (C : Set ↥(S.strictTransform n)),
      C ∈ irreducibleComponents ↥(S.strictTransform n) → ∀ η : ↥(S.strictTransform n),
      IsGenericPoint η C →
      ∃ D ∈ irreducibleComponents ↥(S.strictTransform 0),
        IsGenericPoint ((S.strictTransformToZero n).base η) D := by
  induction n with
  | zero =>
    intro _ C hC η hη
    exact ⟨C, hC, hη⟩
  | succ m ih =>
    intro hn C hC η hη
    have hm : m < S.ambientLength := hn
    obtain ⟨C', hC', hgen', -⟩ :=
      EmbeddedBlowupSequence.exists_irreducibleComponent_isGenericPoint_strictTransformMap S.toEmbeddedBlowupSequence (fun j hj => hN j hj) m hm C hC η hη
    obtain ⟨D, hD, hDgen⟩ := ih (le_of_lt hm) C' hC' ((S.strictTransformMap m).base η) hgen'
    exact ⟨D, hD, hDgen⟩


end

theorem affineSmoothLocusPreimageDenseInDetached (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    AffineSmoothLocusPreimageDenseInDetached A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _ i hi
  have hY : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType pY
  apply dense_of_forall_mem_of_isGenericPoint
  intro C hC η hη
  obtain ⟨Z, hZ, hZgen⟩ :=
    exists_isGenericPoint_image_of_isClosedEmbedding
      (isClosedEmbedding_discardedι A hemb hsnc hsm k Y pY i)
      (discardedComponents_subset_irreducibleComponents A hemb hsnc hsm k Y pY i)
      (range_discardedι_eq_sUnion_discardedComponents A hemb hsnc hsm k Y pY i hi).symm hC hη
  have hZc := discardedComponents_subset_irreducibleComponents A hemb hsnc hsm k Y pY i hZ
  obtain ⟨D, hD, hDgen⟩ :=
    exists_isGenericPoint_strictTransformToZero_consolidated399 (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)
      (fun j hj =>
        isNoetherian_ambientLevel (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY) j hj)
      i (le_of_lt hi) Z hZc _ hZgen
  have := isOpenImmersion_strictTransformZeroToBase (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)
  obtain ⟨E, hE, hEgen⟩ :=
    exists_isGenericPoint_image_of_isOpenEmbedding
      (Scheme.Hom.isOpenEmbedding
        (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformZeroToBase)
      hD hDgen
  have hdense : Dense ((pY.smoothLocus : Set ↥Y)) := pY.dense_smoothLocus_of_perfectField
  have hmem := mem_of_isGenericPoint_of_isOpen_of_dense
    (U := (pY.smoothLocus : Set ↥Y)) (pY.smoothLocus).isOpen hdense hE hEgen
  rw [Set.mem_preimage, AffineSpacePrincipalizationData.detachedToBase_def]
  exact hmem

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SingularPreimageBoundary
section

open TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

private theorem isIso_stalkMap_of_isOpenImmersion_consolidated428 {A B : Scheme.{u}} (f : A ⟶ B)
    [IsOpenImmersion f] (x : ↥A) :
    CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap f x) := by
  infer_instance

namespace AffineSpacePrincipalizationData

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)

private theorem base_apply_mem_support_ker_consolidated428 {W Z : Scheme.{u}} (g : W ⟶ Z) (q : ↥W) :
    g.base q ∈ ((AlgebraicGeometry.Scheme.Hom.ker g).support : Set ↥Z) := by
  have hle : AlgebraicGeometry.Scheme.Hom.ker
        (AlgebraicGeometry.Scheme.Hom.ker g).subschemeι ≤
      AlgebraicGeometry.Scheme.Hom.ker g :=
    le_of_eq (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι _)
  have hfac : AlgebraicGeometry.IsClosedImmersion.lift
        (AlgebraicGeometry.Scheme.Hom.ker g).subschemeι g hle ≫
      (AlgebraicGeometry.Scheme.Hom.ker g).subschemeι = g :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι]
  exact ⟨(AlgebraicGeometry.IsClosedImmersion.lift
      (AlgebraicGeometry.Scheme.Hom.ker g).subschemeι g hle).base q, by
    rw [← comp_base_apply_consolidated342, hfac]⟩

theorem mem_support_centerOffDetached_of_mem_support_ambientCenter (i : ℕ) (p : ↥(S.strictTransform i))
    (hp : p ∈ ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)))
    (hmem : (S.strictTransformι i).base p ∈ ((S.ambientCenter i).support : Set ↥(S.ambientLevel i))) :
    p ∈ (((S.centerOffDetached i).support : TopologicalSpace.Closeds ↥(S.strictTransform i)) :
      Set ↥(S.strictTransform i)) := by
  have hU : p ∈ S.discardedLocusClosureCompl i := hp
  have htrace : p ∈ ((S.comapAmbientCenter i).support : Set ↥(S.strictTransform i)) := by
    rw [S.comapAmbientCenter_eq i]
    exact Scheme.IdealSheafData.mem_support_comap.mpr hmem
  have hq0 : (⟨p, hU⟩ : ↥(S.discardedLocusClosureCompl i)) ∈
      ((((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).support :
        TopologicalSpace.Closeds ↥(S.discardedLocusClosureCompl i).toScheme) :
        Set ↥(S.discardedLocusClosureCompl i).toScheme) :=
    Scheme.IdealSheafData.mem_support_comap.mpr htrace
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι] at hq0
  obtain ⟨q, hq⟩ := hq0
  have hmain := base_apply_mem_support_ker_consolidated428
    (((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι ≫ (S.discardedLocusClosureCompl i).ι) q
  rw [comp_base_apply_consolidated342, hq] at hmain
  rw [S.centerOffDetached_eq i]
  exact hmain

private theorem forall_mem_smoothLocusComplement_of_not_avoidsCenters_consolidated428
    (hN : ∀ j ≤ S.ambientLength, IsNoetherian (S.ambientLevel j))
    (hopen : ∀ j < S.ambientLength, IsOpen (S.discardedLocus j))
    (hcent : S.CentersLieOverSingularLocus) :
    ∀ (i : ℕ), i ≤ S.ambientLength → ∀ p : ↥(S.strictTransform i),
      ¬ S.toEmbeddedBlowupSequence.AvoidsCenters i ((S.strictTransformι i).base p) →
      (S.strictTransformToZero i ≫ S.strictTransformZeroToBase).base p ∈
        ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y) := by
  have hNl : ∀ m, m ≤ S.ambientLength → TopologicalSpace.NoetherianSpace ↥(S.ambientLevel m) := by
    intro m hm
    have := hN m hm
    infer_instance
  intro i
  induction i with
  | zero =>
      intro _ p hp
      exact absurd (S.toEmbeddedBlowupSequence.avoidsCenters_zero _) hp
  | succ j ih =>
      intro hj p hp
      have hjlt : j < S.ambientLength := Nat.lt_of_succ_le hj
      have hjle : j ≤ S.ambientLength := Nat.le_of_lt hjlt
      have hnj : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel j) := hNl j hjle
      have hNa : TopologicalSpace.NoetherianSpace ↥(S.strictTransform j) :=
        S.noetherianSpace_strictTransform j
      have hNl' : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel (j + 1)) := hNl (j + 1) hj
      have key : (S.strictTransformι j).base ((S.strictTransformMap j).base p)
          = (S.ambientBlowupMorphism j).base ((S.strictTransformι (j + 1)).base p) := by
        have h : (S.strictTransformMap j ≫ S.strictTransformι j).base p
            = (S.strictTransformι (j + 1) ≫ S.ambientBlowupMorphism j).base p := by
          rw [S.strictTransformMap_comp_strictTransformι j]
        simpa using h
      have hdown : (S.strictTransformToZero (j + 1) ≫ S.strictTransformZeroToBase).base p
          = (S.strictTransformToZero j ≫ S.strictTransformZeroToBase).base ((S.strictTransformMap j).base p) := by
        simp
      rw [hdown]
      by_cases hc : (S.ambientBlowupMorphism j).base ((S.strictTransformι (j + 1)).base p) ∈
          ((S.ambientCenter j).support : Set ↥(S.ambientLevel j))
      · have hfc : (S.strictTransformMap j).base p ∈
            ((S.discardedLocusClosureCompl j : (S.strictTransform j).Opens) : Set ↥(S.strictTransform j)) :=
          S.range_strictTransformMap_subset_discardedLocusClosureCompl j hjlt hNa hNl' (hopen j hjlt) ⟨p, rfl⟩
        have hmem : (S.strictTransformι j).base ((S.strictTransformMap j).base p) ∈
            ((S.ambientCenter j).support : Set ↥(S.ambientLevel j)) := by
          rw [key]
          exact hc
        exact hcent j hjlt ((S.strictTransformMap j).base p)
          (S.mem_support_centerOffDetached_of_mem_support_ambientCenter j ((S.strictTransformMap j).base p)
            hfc hmem)
      · refine ih hjle ((S.strictTransformMap j).base p) ?_
        intro hcl
        have hcl' : S.toEmbeddedBlowupSequence.AvoidsCenters j ((S.ambientBlowupMorphism j).base ((S.strictTransformι (j + 1)).base p)) := by
          rw [← key]
          exact hcl
        exact hp ((S.toEmbeddedBlowupSequence.avoidsCenters_succ_iff j ((S.strictTransformι (j + 1)).base p)).mpr ⟨hc, hcl'⟩)

theorem mem_smoothLocusComplement_of_not_avoidsCenters [IsReduced Y]
    (hN : ∀ j ≤ S.ambientLength, IsNoetherian (S.ambientLevel j))
    (hopen : ∀ j < S.ambientLength, IsOpen (S.discardedLocus j))
    (hcent : S.CentersLieOverSingularLocus)
    (i : ℕ) (hi : i ≤ S.ambientLength) (p : ↥(S.strictTransform i))
    (hp : ¬ S.toEmbeddedBlowupSequence.AvoidsCenters i ((S.strictTransformι i).base p)) :
    (S.strictTransformToZero i ≫ S.strictTransformZeroToBase).base p ∈
      ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y) :=
  forall_mem_smoothLocusComplement_of_not_avoidsCenters_consolidated428 S hN hopen hcent i hi p hp

private theorem mem_support_strictTransform_of_mem_support_of_notMem_support_consolidated428 {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    [IsLocallyNoetherian X₁] (Z D : X.IdealSheafData) (x : ↥X₁)
    (hD : π.base x ∈ ((D.support : TopologicalSpace.Closeds ↥X) : Set ↥X))
    (hZ : π.base x ∉ ((Z.support : TopologicalSpace.Closeds ↥X) : Set ↥X)) :
    x ∈ (((FunctorialResolution.Blowup.strictTransform π Z D).support :
      TopologicalSpace.Closeds ↥X₁) : Set ↥X₁) := by
  rw [FunctorialResolution.EmbeddedResolution.support_strictTransform_eq_closure_preimage π Z D]
  exact subset_closure (Set.mem_preimage.mpr (Set.mem_sdiff_of_mem hD hZ))

section
variable (hN : ∀ j ≤ S.ambientLength, IsNoetherian (S.ambientLevel j))
include hN

private theorem avoidsCenters_of_forall_notMem_support_boundary_consolidated428
    :
    ∀ (i : ℕ), i ≤ S.principalizationSequence.length → ∀ x : ↥(S.principalizationSequence.schemeAt i),
      (∀ E ∈ S.principalizationSequence.boundary i,
        x ∉ ((E.support : TopologicalSpace.Closeds ↥(S.principalizationSequence.schemeAt i)) :
          Set ↥(S.principalizationSequence.schemeAt i))) →
      S.toEmbeddedBlowupSequence.AvoidsCenters i x := by
  intro i
  induction i with
  | zero =>
      intro _ x _
      exact S.toEmbeddedBlowupSequence.avoidsCenters_zero x
  | succ i ih =>
      intro hi x hx
      have hilt : i < S.principalizationSequence.length := hi
      have hbnd := S.principalizationSequence.boundary_succ_eq_map_strictTransform_append i hilt
      have hexc : S.principalizationSequence.exceptionalIdeal i ∈ S.principalizationSequence.boundary (i + 1) := by
        rw [hbnd]
        exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
      have hnc : ((S.principalizationSequence.transitionMapSucc i).base x) ∉
          (((S.principalizationSequence.center i).support :
            TopologicalSpace.Closeds ↥(S.principalizationSequence.schemeAt i)) : Set ↥(S.principalizationSequence.schemeAt i)) := by
        intro hmem
        refine hx _ hexc ?_
        rw [S.principalizationSequence.exceptionalIdeal_eq i]
        exact Scheme.IdealSheafData.mem_support_comap.mpr hmem
      refine (S.toEmbeddedBlowupSequence.avoidsCenters_succ_iff i x).mpr ⟨hnc, ?_⟩
      refine ih (Nat.le_of_succ_le hi) ((S.principalizationSequence.transitionMapSucc i).base x) ?_
      intro E hE hmem
      have hlocNoeth : IsLocallyNoetherian (S.principalizationSequence.schemeAt (i + 1)) :=
        (hN (i + 1) hi).toIsLocallyNoetherian
      refine hx (FunctorialResolution.Blowup.strictTransform (S.principalizationSequence.transitionMapSucc i) (S.principalizationSequence.center i) E)
        ?_ ?_
      · rw [hbnd]
        exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨E, hE, rfl⟩))
      · exact @_root_.FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.mem_support_strictTransform_of_mem_support_of_notMem_support_consolidated428 (S.principalizationSequence.schemeAt i) (S.principalizationSequence.schemeAt (i + 1))
          (S.principalizationSequence.transitionMapSucc i) hlocNoeth (S.principalizationSequence.center i) E x hmem hnc

theorem avoidsCenters_of_forall_notMem_boundary
    (i : ℕ) (hi : i ≤ S.ambientLength) (x : ↥(S.ambientLevel i))
    (hx : ∀ E ∈ S.boundary i, x ∉ ((E.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) :
      Set ↥(S.ambientLevel i))) :
    S.toEmbeddedBlowupSequence.AvoidsCenters i x :=
  avoidsCenters_of_forall_notMem_support_boundary_consolidated428 S hN i hi x hx


end

section
variable {P Q R : CommRingCat.{u}} (u : P ⟶ Q) (v : Q ⟶ R)

private theorem isIso_comp_of_isIso_commRingCat_consolidated428 (hu : CategoryTheory.IsIso u) (hv : CategoryTheory.IsIso v) :
    CategoryTheory.IsIso (u ≫ v) := by
  have := hu
  have := hv
  infer_instance

private theorem isIso_of_isIso_comp_right_consolidated428 (hv : CategoryTheory.IsIso v) (huv : CategoryTheory.IsIso (u ≫ v)) :
    CategoryTheory.IsIso u := by
  have := hv
  have := huv
  have h : u = (u ≫ v) ≫ CategoryTheory.inv v := by
    rw [CategoryTheory.Category.assoc, CategoryTheory.IsIso.hom_inv_id,
      CategoryTheory.Category.comp_id]
  rw [h]
  infer_instance


end

private theorem isIso_stalkMap_of_isIso_stalkMap_comp_consolidated428 {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (x : ↥A)
    (hf : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap f x))
    (hfg : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap (f ≫ g) x)) :
    CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap g (f.base x)) := by
  rw [AlgebraicGeometry.Scheme.Hom.stalkMap_comp] at hfg
  exact isIso_of_isIso_comp_right_consolidated428 _ _ hf hfg

private theorem idealSheafData_comap_injective_of_isIso_consolidated428 {A B : Scheme.{u}} (φ : A ⟶ B)
    [CategoryTheory.IsIso φ] (I J : B.IdealSheafData)
    (h : I.comap φ = J.comap φ) : I = J := by
  have h2 : (I.comap φ).comap (CategoryTheory.inv φ)
      = (J.comap φ).comap (CategoryTheory.inv φ) := by rw [h]
  rwa [← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    CategoryTheory.IsIso.inv_hom_id,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id] at h2

private theorem strictTransform_comap_ι_eq_comap_restrict_consolidated428 {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [TopologicalSpace.NoetherianSpace ↥X₁] :
    (FunctorialResolution.Blowup.strictTransform π Z D).comap (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl))
      = (D.comap (Scheme.Opens.ι Z.support.compl)).comap (π ∣_ Z.support.compl) := by
  have := (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).isEmbedding.toIsInducing.noetherianSpace
  rw [FunctorialResolution.EmbeddedResolution.strictTransform_eq_ker_restrict π Z D]
  exact FunctorialResolution.EmbeddedResolution.comap_ker_subschemeι_comp _ _

private theorem isOpenImmersion_preimage_ι_comp_of_ker_comap_eq_consolidated428 {X X₁ A₀ A₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (ι₀ : A₀ ⟶ X) (ι₁ : A₁ ⟶ X₁) (m : A₁ ⟶ A₀) (V : X.Opens)
    [IsClosedImmersion ι₀] [IsClosedImmersion ι₁]
    [CategoryTheory.IsIso (π ∣_ V)]
    (hm : m ≫ ι₀ = ι₁ ≫ π)
    (hker : (AlgebraicGeometry.Scheme.Hom.ker ι₁).comap (Scheme.Opens.ι (π ⁻¹ᵁ V))
      = ((AlgebraicGeometry.Scheme.Hom.ker ι₀).comap (Scheme.Opens.ι V)).comap (π ∣_ V)) :
    IsOpenImmersion (Scheme.Opens.ι (ι₁ ⁻¹ᵁ (π ⁻¹ᵁ V)) ≫ m) := by
  have hciα : IsClosedImmersion ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) :=
    inferInstance
  have hk1 := FunctorialResolution.EmbeddedResolution.ker_comap_ι_eq_ker_morphismRestrict ι₁ (π ⁻¹ᵁ V)
  have hk0 := FunctorialResolution.EmbeddedResolution.ker_comap_ι_eq_ker_morphismRestrict ι₀ V
  have hcomp := FunctorialResolution.Blowup.comap_ker_comp_of_isOpenImmersion (ι₁ ∣_ (π ⁻¹ᵁ V)) (π ∣_ V)
  have hkereq : AlgebraicGeometry.Scheme.Hom.ker ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V))
      = AlgebraicGeometry.Scheme.Hom.ker (ι₀ ∣_ V) := by
    refine idealSheafData_comap_injective_of_isIso_consolidated428 (π ∣_ V) _ _ ?_
    rw [hcomp, ← hk1, hker, hk0]
  have hle : AlgebraicGeometry.Scheme.Hom.ker (ι₀ ∣_ V)
      ≤ AlgebraicGeometry.Scheme.Hom.ker ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) := le_of_eq hkereq.symm
  have hfac := AlgebraicGeometry.IsClosedImmersion.lift_fac (ι₀ ∣_ V)
    ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle
  have hIso : CategoryTheory.IsIso (AlgebraicGeometry.IsClosedImmersion.lift (ι₀ ∣_ V)
      ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle) :=
    AlgebraicGeometry.IsClosedImmersion.isIso_of_ker_eq _ _ _ hfac hkereq
  have hmono : (Scheme.Opens.ι (ι₁ ⁻¹ᵁ (π ⁻¹ᵁ V)) ≫ m) ≫ ι₀
      = ((AlgebraicGeometry.IsClosedImmersion.lift (ι₀ ∣_ V)
          ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle) ≫ Scheme.Opens.ι (ι₀ ⁻¹ᵁ V)) ≫ ι₀ := by
    calc (Scheme.Opens.ι (ι₁ ⁻¹ᵁ (π ⁻¹ᵁ V)) ≫ m) ≫ ι₀
        = Scheme.Opens.ι (ι₁ ⁻¹ᵁ (π ⁻¹ᵁ V)) ≫ (m ≫ ι₀) := CategoryTheory.Category.assoc _ _ _
      _ = Scheme.Opens.ι (ι₁ ⁻¹ᵁ (π ⁻¹ᵁ V)) ≫ (ι₁ ≫ π) := by rw [hm]
      _ = (Scheme.Opens.ι (ι₁ ⁻¹ᵁ (π ⁻¹ᵁ V)) ≫ ι₁) ≫ π :=
          (CategoryTheory.Category.assoc _ _ _).symm
      _ = ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ Scheme.Opens.ι (π ⁻¹ᵁ V)) ≫ π := by
          rw [AlgebraicGeometry.morphismRestrict_ι]
      _ = (ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (Scheme.Opens.ι (π ⁻¹ᵁ V) ≫ π) :=
          CategoryTheory.Category.assoc _ _ _
      _ = (ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ ((π ∣_ V) ≫ Scheme.Opens.ι V) := by
          rw [AlgebraicGeometry.morphismRestrict_ι]
      _ = ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) ≫ Scheme.Opens.ι V :=
          (CategoryTheory.Category.assoc _ _ _).symm
      _ = ((AlgebraicGeometry.IsClosedImmersion.lift (ι₀ ∣_ V)
            ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle) ≫ (ι₀ ∣_ V)) ≫ Scheme.Opens.ι V := by
          rw [hfac]
      _ = (AlgebraicGeometry.IsClosedImmersion.lift (ι₀ ∣_ V)
            ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle) ≫ ((ι₀ ∣_ V) ≫ Scheme.Opens.ι V) :=
          CategoryTheory.Category.assoc _ _ _
      _ = (AlgebraicGeometry.IsClosedImmersion.lift (ι₀ ∣_ V)
            ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle) ≫ (Scheme.Opens.ι (ι₀ ⁻¹ᵁ V) ≫ ι₀) := by
          rw [AlgebraicGeometry.morphismRestrict_ι]
      _ = ((AlgebraicGeometry.IsClosedImmersion.lift (ι₀ ∣_ V)
            ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle) ≫ Scheme.Opens.ι (ι₀ ⁻¹ᵁ V)) ≫ ι₀ :=
          (CategoryTheory.Category.assoc _ _ _).symm
  have hfin := (CategoryTheory.cancel_mono ι₀).mp hmono
  rw [hfin]
  infer_instance

private theorem ambientBlowupMorphism_comp_schemeAtToSpec_consolidated428 (j : ℕ) :
    S.ambientBlowupMorphism j ≫ S.schemeAtToSpec j = S.schemeAtToSpec (j + 1) := by
  have h := FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_succ S.ambientBlowups j
  rw [AffineSpacePrincipalizationData.schemeAtToSpec_def, AffineSpacePrincipalizationData.schemeAtToSpec_def, h,
    CategoryTheory.Category.assoc]

section
variable (i : ℕ)

private theorem strictTransformToZero_comp_schemeAtToSpec_consolidated428 :
    S.strictTransformToZero i ≫ S.strictTransformι 0 ≫ S.schemeAtToSpec 0 = S.strictTransformι i ≫ S.schemeAtToSpec i := by
  induction i with
  | zero => rw [AffineSpacePrincipalizationData.strictTransformToZero_zero, CategoryTheory.Category.id_comp]
  | succ j ih =>
      rw [AffineSpacePrincipalizationData.strictTransformToZero_succ, CategoryTheory.Category.assoc, ih,
        ← CategoryTheory.Category.assoc, S.strictTransformMap_comp_strictTransformι j, CategoryTheory.Category.assoc,
        ambientBlowupMorphism_comp_schemeAtToSpec_consolidated428 S j]

private theorem detachedToBase_comp_eq_discardedι_comp_schemeAtToSpec_consolidated428 :
    S.detachedToBase i ≫ pY = S.discardedι i ≫ S.strictTransformι i ≫ S.schemeAtToSpec i := by
  rw [AffineSpacePrincipalizationData.detachedToBase_def, CategoryTheory.Category.assoc,
    CategoryTheory.Category.assoc, AffineSpacePrincipalizationData.strictTransformZeroToBase_comp,
    ← strictTransformToZero_comp_schemeAtToSpec_consolidated428 S i]


end

private theorem isIso_stalkMap_strictTransformToZero_of_avoidsCenters_consolidated428
    (hN : ∀ j ≤ S.ambientLength, IsNoetherian (S.ambientLevel j)) (j : ℕ) :
    j ≤ S.ambientLength → ∀ a : ↥(S.strictTransform j),
      S.toEmbeddedBlowupSequence.AvoidsCenters j ((S.strictTransformι j).base a) →
      CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap (S.strictTransformToZero j) a) := by
  induction j with
  | zero =>
      intro _ a _
      rw [AffineSpacePrincipalizationData.strictTransformToZero_zero]
      exact isIso_stalkMap_of_isOpenImmersion_consolidated428
        (CategoryTheory.CategoryStruct.id (S.strictTransform 0)) a
  | succ j ih =>
      intro hj a ha
      have hjlt : j < S.ambientLength := Nat.lt_of_succ_le hj
      have hNoe : IsNoetherian (S.ambientLevel (j + 1)) := hN (j + 1) hj
      have hNs : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel (j + 1)) := inferInstance
      obtain ⟨hnc, hcl⟩ := (S.toEmbeddedBlowupSequence.avoidsCenters_succ_iff j ((S.strictTransformι (j + 1)).base a)).mp ha
      have haO : a ∈ (S.strictTransformι (j + 1) ⁻¹ᵁ
          (S.ambientBlowupMorphism j ⁻¹ᵁ (S.ambientCenter j).support.compl)) := hnc
      have hiso : CategoryTheory.IsIso
          (S.ambientBlowupMorphism j ∣_ ((S.ambientCenter j).support.compl)) :=
        S.toEmbeddedBlowupSequence.isIso_blowdown_restrict_ambientCenterSupportCompl j hjlt
      have hker : (AlgebraicGeometry.Scheme.Hom.ker (S.strictTransformι (j + 1))).comap
            (Scheme.Opens.ι (S.ambientBlowupMorphism j ⁻¹ᵁ (S.ambientCenter j).support.compl))
          = ((AlgebraicGeometry.Scheme.Hom.ker (S.strictTransformι j)).comap
              (Scheme.Opens.ι ((S.ambientCenter j).support.compl))).comap
              (S.ambientBlowupMorphism j ∣_ ((S.ambientCenter j).support.compl)) := by
        rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι,
          AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι, S.strictTransformIdeal_succ j]
        exact strictTransform_comap_ι_eq_comap_restrict_consolidated428 (S.ambientBlowupMorphism j) (S.ambientCenter j) (S.strictTransformIdeal j)
      have hoi : IsOpenImmersion
          (Scheme.Opens.ι (S.strictTransformι (j + 1) ⁻¹ᵁ
            (S.ambientBlowupMorphism j ⁻¹ᵁ (S.ambientCenter j).support.compl)) ≫ S.strictTransformMap j) :=
        isOpenImmersion_preimage_ι_comp_of_ker_comap_eq_consolidated428 (S.ambientBlowupMorphism j) (S.strictTransformι j) (S.strictTransformι (j + 1))
          (S.strictTransformMap j) ((S.ambientCenter j).support.compl) (S.strictTransformMap_comp_strictTransformι j) hker
      have h2 : CategoryTheory.IsIso
          (AlgebraicGeometry.Scheme.Hom.stalkMap (S.strictTransformMap j) a) :=
        isIso_stalkMap_of_isIso_stalkMap_comp_consolidated428
          (Scheme.Opens.ι (S.strictTransformι (j + 1) ⁻¹ᵁ
            (S.ambientBlowupMorphism j ⁻¹ᵁ (S.ambientCenter j).support.compl))) (S.strictTransformMap j)
          ⟨a, haO⟩ (isIso_stalkMap_of_isOpenImmersion_consolidated428 _ _) (isIso_stalkMap_of_isOpenImmersion_consolidated428 _ _)
      have hb : (S.strictTransformι j).base ((S.strictTransformMap j).base a)
          = (S.ambientBlowupMorphism j).base ((S.strictTransformι (j + 1)).base a) := by
        have h := congrArg (fun f : S.strictTransform (j + 1) ⟶ S.ambientLevel j => f.base a)
          (S.strictTransformMap_comp_strictTransformι j)
        simpa using h
      have hclj : S.toEmbeddedBlowupSequence.AvoidsCenters j ((S.strictTransformι j).base ((S.strictTransformMap j).base a)) := by
        rw [hb]
        exact hcl
      have hih := ih (Nat.le_of_succ_le hj) ((S.strictTransformMap j).base a) hclj
      rw [AffineSpacePrincipalizationData.strictTransformToZero_succ, AlgebraicGeometry.Scheme.Hom.stalkMap_comp]
      exact isIso_comp_of_isIso_commRingCat_consolidated428 _ _ hih h2

private theorem formallySmooth_of_isIso_consolidated428 {A B : CommRingCat.{u}} (ψ : A ⟶ B)
    [CategoryTheory.IsIso ψ] : (CommRingCat.Hom.hom ψ).FormallySmooth := by
  have hb : Function.Bijective (CommRingCat.Hom.hom ψ) :=
    CategoryTheory.ConcreteCategory.bijective_of_isIso ψ
  exact RingHom.FormallySmooth.of_bijective hb

private theorem formallySmooth_of_formallySmooth_comp_isIso_consolidated428 {R A B : CommRingCat.{u}} (φ : R ⟶ A) (ψ : A ⟶ B)
    [CategoryTheory.IsIso ψ]
    (h : (CommRingCat.Hom.hom (φ ≫ ψ)).FormallySmooth) :
    (CommRingCat.Hom.hom φ).FormallySmooth := by
  have h1 : (φ ≫ ψ) ≫ CategoryTheory.inv ψ = φ := by
    rw [CategoryTheory.Category.assoc, CategoryTheory.IsIso.hom_inv_id,
      CategoryTheory.Category.comp_id]
  rw [← h1, CommRingCat.hom_comp]
  exact RingHom.FormallySmooth.comp h (formallySmooth_of_isIso_consolidated428 (CategoryTheory.inv ψ))

section
variable [IsReduced Y] (hN : ∀ j ≤ S.ambientLength, IsNoetherian (S.ambientLevel j)) (hopen : ∀ j < S.ambientLength, IsOpen (S.discardedLocus j)) (hsmooth : S.DetachedSmooth) (i : ℕ) (hi : i < S.ambientLength) (q : ↥(S.discardedSubscheme i))
include hN hopen hsmooth hi

theorem notMem_smoothLocusComplement_detachedToBase_of_avoidsCenters (hq : S.toEmbeddedBlowupSequence.AvoidsCenters i ((S.strictTransformι i).base ((S.discardedι i).base q))) :
    (S.detachedToBase i).base q ∉
      ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y) := by
  intro hmem
  have hred : IsReduced (S.strictTransform i) :=
    S.isReduced_strictTransform hN i (le_of_lt hi)
  have hnl : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel i) := by
    have := hN i (le_of_lt hi)
    infer_instance
  have hna : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i) :=
    S.noetherianSpace_strictTransform i
  obtain ⟨e, he⟩ := S.exists_iso_discardedSubscheme_discardedLocusOpens i hna (hopen i hi)
  have hfi : IsOpenImmersion (S.discardedι i) := by
    rw [← he]
    infer_instance
  have hab : IsOpenImmersion S.strictTransformZeroToBase :=
    FunctorialResolution.EmbeddedResolution.isOpenImmersion_strictTransformZeroToBase S
  have hchain := isIso_stalkMap_strictTransformToZero_of_avoidsCenters_consolidated428 S hN i (le_of_lt hi) ((S.discardedι i).base q) hq
  have hsm : Smooth (S.detachedToBase i ≫ pY) := by
    rw [detachedToBase_comp_eq_discardedι_comp_schemeAtToSpec_consolidated428 S i]
    exact hsmooth i hi
  have hstq : CategoryTheory.IsIso
      (AlgebraicGeometry.Scheme.Hom.stalkMap (S.detachedToBase i) q) := by
    have h1 : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap S.strictTransformZeroToBase
        ((S.strictTransformToZero i).base ((S.discardedι i).base q))) := isIso_stalkMap_of_isOpenImmersion_consolidated428 _ _
    have h2 : CategoryTheory.IsIso
        (AlgebraicGeometry.Scheme.Hom.stalkMap (S.discardedι i) q) :=
      isIso_stalkMap_of_isOpenImmersion_consolidated428 _ _
    rw [AffineSpacePrincipalizationData.detachedToBase_def, AlgebraicGeometry.Scheme.Hom.stalkMap_comp,
      AlgebraicGeometry.Scheme.Hom.stalkMap_comp]
    exact isIso_comp_of_isIso_commRingCat_consolidated428 _ _ (isIso_comp_of_isIso_commRingCat_consolidated428 _ _ h1 hchain) h2
  have htop : (S.detachedToBase i ≫ pY).smoothLocus = ⊤ :=
    AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff.mpr hsm
  have hmemq : q ∈ (S.detachedToBase i ≫ pY).smoothLocus := by
    rw [htop]
    exact TopologicalSpace.Opens.mem_top q
  have hfs := AlgebraicGeometry.Scheme.Hom.mem_smoothLocus.mp hmemq
  rw [AlgebraicGeometry.Scheme.Hom.stalkMap_comp] at hfs
  have hfs2 : (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.stalkMap pY
      ((S.detachedToBase i).base q))).FormallySmooth :=
    formallySmooth_of_formallySmooth_comp_isIso_consolidated428 _ _ hfs
  have hin : (S.detachedToBase i).base q ∈ pY.smoothLocus :=
    AlgebraicGeometry.Scheme.Hom.mem_smoothLocus.mpr hfs2
  exact hmem hin

theorem notMem_smoothLocusComplement_detachedToBase_of_notMem_boundary (hq : ∀ E ∈ S.boundary i,
      (S.strictTransformι i).base ((S.discardedι i).base q) ∉
        ((E.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) : Set ↥(S.ambientLevel i))) :
    (S.detachedToBase i).base q ∉
      ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y) := by
  have hclear : S.toEmbeddedBlowupSequence.AvoidsCenters i ((S.strictTransformι i).base ((S.discardedι i).base q)) :=
    avoidsCenters_of_forall_notMem_boundary S hN i (le_of_lt hi)
      ((S.strictTransformι i).base ((S.discardedι i).base q)) hq
  exact notMem_smoothLocusComplement_detachedToBase_of_avoidsCenters S hN hopen hsmooth i hi q hclear


end

end AffineSpacePrincipalizationData

private theorem principalizationSequence_not_avoidsCenters_of_mem_boundary_consolidated428 {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) :
    ∀ (i : ℕ), i ≤ S.principalizationSequence.length →
      ∀ E : (S.principalizationSequence.schemeAt i).IdealSheafData, E ∈ S.principalizationSequence.boundary i →
        ∀ x : ↥(S.principalizationSequence.schemeAt i), x ∈ (E.support : Set ↥(S.principalizationSequence.schemeAt i)) →
          ¬ S.toEmbeddedBlowupSequence.AvoidsCenters i x := by
  intro i
  induction i with
  | zero =>
      intro _ E hE x _ _
      rw [S.principalizationSequence.boundary_zero] at hE
      simp at hE
  | succ i ih =>
      intro hi E hE x hx hcl
      have hilt : i < S.principalizationSequence.length := hi
      rw [S.principalizationSequence.boundary_succ_eq_map_strictTransform_append i hilt, List.mem_append] at hE
      have hcl' := (S.toEmbeddedBlowupSequence.avoidsCenters_succ_iff i x).mp hcl
      rcases hE with hE | hE
      · obtain ⟨E', hE', rfl⟩ := List.mem_map.mp hE
        have hmem : x ∈ ((E'.comap (S.principalizationSequence.transitionMapSucc i)).support :
            Set ↥(S.principalizationSequence.schemeAt (i + 1))) :=
          AlgebraicGeometry.Scheme.IdealSheafData.support_antitone
            (FunctorialResolution.EmbeddedResolution.comap_le_strictTransform (S.principalizationSequence.transitionMapSucc i)
              (S.principalizationSequence.center i) E') hx
        have hmem2 : (S.principalizationSequence.transitionMapSucc i).base x ∈
            (E'.support : Set ↥(S.principalizationSequence.schemeAt i)) :=
          OpenImmersionRestriction.mem_support_of_mem_support_comap (S.principalizationSequence.transitionMapSucc i) E' x hmem
        exact ih (Nat.le_of_succ_le hi) E' hE' _ hmem2 hcl'.2
      · rw [List.mem_singleton] at hE
        subst hE
        rw [S.principalizationSequence.exceptionalIdeal_eq i] at hx
        have hmem2 : (S.principalizationSequence.transitionMapSucc i).base x ∈
            ((S.principalizationSequence.center i).support : Set ↥(S.principalizationSequence.schemeAt i)) :=
          OpenImmersionRestriction.mem_support_of_mem_support_comap (S.principalizationSequence.transitionMapSucc i)
            (S.principalizationSequence.center i) x hx
        exact hcl'.1 hmem2

theorem not_avoidsCenters_of_mem_support_boundary (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [IsAffine Y] (pY : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType pY]
    (i : ℕ) (hi : i ≤ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength)
    (E : ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i).IdealSheafData)
    (hE : E ∈ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).boundary i)
    (x : ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i))
    (hx : x ∈ ((E.support : TopologicalSpace.Closeds
        ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i)) :
      Set ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i))) :
    ¬ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence.AvoidsCenters i x :=
  principalizationSequence_not_avoidsCenters_of_mem_boundary_consolidated428 (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY) i hi E hE
    x hx

section
variable (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) [IsAffine Y] [IsReduced Y] (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY] [QuasiCompact pY] (hopen : ∀ j < (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength, IsOpen ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedLocus j))
include hopen

theorem boundary_preimage_subset_smoothLocusComplement_preimage (hcent : (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).CentersLieOverSingularLocus)
    (i : ℕ) (hi : i < (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength) :
    ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i ≫
          (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base ⁻¹'
        (⋃ E ∈ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).boundary i,
          ((E.support : TopologicalSpace.Closeds
              ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i)) :
            Set ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i))) ⊆
      ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).detachedToBase i).base ⁻¹'
        ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y) := by
  intro q hq
  have hq' : ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i ≫
        (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base q ∈
      ⋃ E ∈ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).boundary i,
        ((E.support : TopologicalSpace.Closeds
            ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i)) :
          Set ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i)) := hq
  obtain ⟨E, hE, hmem⟩ := Set.mem_iUnion₂.mp hq'
  have hbase : ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i ≫
        (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base q
      = ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base
          (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base q) :=
    comp_base_apply_consolidated342 _ _ q
  rw [hbase] at hmem
  have hnc := not_avoidsCenters_of_mem_support_boundary A hemb hsnc hsm k Y pY i (le_of_lt hi) E hE
    (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base
      (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base q)) hmem
  have hsing := (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).mem_smoothLocusComplement_of_not_avoidsCenters
    (isNoetherian_ambientLevel_ofAffine A hemb hsnc hsm k Y pY) hopen hcent i (le_of_lt hi)
    (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base q) hnc
  show ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).detachedToBase i).base q ∈
    ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y)
  rw [AffineSpacePrincipalizationData.detachedToBase_def, comp_base_apply_consolidated342]
  exact hsing

theorem detachedSingularPreimageEqBoundary_ofAffine (hsmooth : (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).DetachedSmooth)
    (hcent : (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).CentersLieOverSingularLocus) :
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).DetachedSingularPreimageEqBoundary := by
  intro i hi
  refine Set.Subset.antisymm ?_
    (boundary_preimage_subset_smoothLocusComplement_preimage A hemb hsnc hsm k Y pY hopen hcent i hi)
  intro q hq
  by_contra hcon
  have hboundary : ∀ E ∈ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).boundary i,
      ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base
          (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base q) ∉
        ((E.support : TopologicalSpace.Closeds
            ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i)) :
          Set ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i)) := by
    intro E hE hmem
    refine hcon ?_
    have hb := comp_base_apply_consolidated342
      ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i)
      ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i) q
    simp only [Set.mem_preimage, hb]
    exact Set.mem_iUnion₂.mpr ⟨E, hE, hmem⟩
  exact (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y
      pY).notMem_smoothLocusComplement_detachedToBase_of_notMem_boundary
    (isNoetherian_ambientLevel_ofAffine A hemb hsnc hsm k Y pY) hopen hsmooth i hi q hboundary hq


end

theorem affineDetachedSingularPreimageEqBoundary_of_centersLieOverSing (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u})
    (hiso : EmbeddedPrincipalizationDiscardedLocusIsOpen A hemb hsnc hsm)
    (hsmooth : AffineDetachedSmooth A hemb hsnc hsm)
    (hPrincipalization : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm)
    (hcent : AffineCentersLieOverSingularLocus A hemb hsnc hsm hPrincipalization) :
    AffineDetachedSingularPreimageEqBoundary A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  refine detachedSingularPreimageEqBoundary_ofAffine A hemb hsnc hsm k Y pY (hiso k Y pY)
    (hsmooth k Y pY) ?_
  exact AffineSpacePrincipalizationData.centersLieOverSingularLocus_of_inducedCentersLieOverSingularLocus
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY) (hPrincipalization k Y pY) (hcent k Y pY)

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.RadicalCenterIdeal
section


namespace FunctorialResolution.EmbeddedResolution

private theorem radical_ker_le_ker_of_isReduced_consolidated204 {R S : Type*} [CommRing R] [CommRing S] [IsReduced S]
    (f : R →+* S) : (RingHom.ker f).radical ≤ RingHom.ker f := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  rw [RingHom.mem_ker, map_pow] at hn
  rw [RingHom.mem_ker]
  exact IsNilpotent.eq_zero ⟨n, hn⟩

theorem smoothSubschemeIdealIsRadical : SmoothSubschemeIdealIsRadical.{u} := by
  intro k ik X p Z ism J hsub
  have hstalk : ∀ x : ↥Z.subscheme, _root_.IsReduced ↑(Z.subscheme.presheaf.stalk x) := by
    intro x
    have := isDomain_stalk_of_smooth (Z.subschemeι ≫ p) x
    infer_instance
  have hred : IsReduced Z.subscheme :=
    isReduced_of_isReduced_stalk Z.subscheme
  have hcomp : ∀ U : Z.subscheme.Opens,
      _root_.IsReduced ↑(Z.subscheme.presheaf.obj (Opposite.op U)) :=
    fun U => AlgebraicGeometry.IsReduced.component_reduced U
  have hZrad : ∀ U : X.affineOpens, (Z.ideal U).radical ≤ Z.ideal U := by
    intro U
    rw [← Z.ker_subschemeι_app U]
    exact radical_ker_le_ker_of_isReduced_consolidated204 _
  have hle : Z.support ≤ J.support := SetLike.coe_subset_coe.mp hsub
  have hJv : J ≤ Scheme.IdealSheafData.vanishingIdeal Z.support := by
    apply (Scheme.IdealSheafData.gc J Z.support).mp
    exact hle
  rw [Scheme.IdealSheafData.vanishingIdeal_support] at hJv
  have hrad : Z.radical ≤ Z := by
    rw [Scheme.IdealSheafData.le_def]
    intro U
    rw [Scheme.IdealSheafData.radical_ideal]
    exact hZrad U
  exact le_trans hJv hrad

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometry
section


section
namespace FunctorialResolution.EmbeddedResolution

namespace OrderReductionCorrectness

theorem blowupLiftEqOnControlledTransform : BlowupLiftEqOnControlledTransform.{u} := EmbeddedResolution.blowupLiftEqOnControlledTransform

theorem le_of_support_subset_of_smooth : ∀ (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData),
    Smooth (Z.subschemeι ≫ p) →
    ∀ J : X.IdealSheafData,
      (((Z.support : Set ↥X)) ⊆ ((J.support : Set ↥X))) → J ≤ Z :=
  smoothSubschemeIdealIsRadical

theorem isLocallyNoetherian_schemeAt : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ),
    i ≤ s.length → IsLocallyNoetherian (s.schemeAt i) := by
  intro T hT s i hi
  have : IsNoetherian (s.schemeAt i) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hT s i hi
  infer_instance

theorem isBalanced_comap_of_smooth : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [Smooth h], h ≫ T.structMap = q →
    ∀ [LocallyOfFiniteType T.structMap]
      [LocallyOfFiniteType q],
    IsDerivBalanced T.base T.structMap T.ideal T.mult →
    IsDerivBalanced T.base q (T.ideal.comap h) T.mult := by
  intro T hT Y q f _ hq _ _ hbal
  subst hq
  have : Smooth T.structMap := hT.smooth
  refine isDerivBalanced_of_pow_le T.base (f ≫ T.structMap) ?_
  intro i hi
  rw [derivIdealSheafIterate_comap T.base T.structMap f i T.ideal,
    ← Scheme.IdealSheafData.comap_pow, ← Scheme.IdealSheafData.comap_pow]
  exact Scheme.IdealSheafData.comap_mono f (IsDerivBalanced.derivIdealSheafIterate_pow_le T.base T.structMap hbal hi)

theorem maxContactIdealComapLeControlled : MaxContactIdealComapLeControlled.{u} := by
  intro k _ _ X X₁ p _ _ π Z E hZ hπ _ _ _ A μ hμ hA A₁ hA₁
  have hct : A₁ = controlledTransform π Z A μ hπ hA :=
    eq_controlledTransform_of_mul_eq_comap π Z A μ hπ hA A₁ hA₁
  have key := comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p π Z E hZ hπ A μ hA
    (μ - 1) (Nat.sub_le μ 1)
  have hsub : μ - (μ - 1) = 1 := by omega
  rw [hsub, pow_one] at key
  simp only [maxContactIdeal_eq_derivIdealSheafIterate]
  rw [hct]
  exact key

theorem existsMaxContactControlledTransforms : ExistsMaxContactControlledTransforms.{u} :=
  existsMaxContactControlledTransforms_of_comapLeControlled maxContactIdealComapLeControlled

theorem projectionToBase_mem_orderAtLeastLocus_of_mem_ideal :
    ∀ (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.length → ∀ x : ↥(s.schemeAt i),
      x ∈ orderAtLeastLocus (s.ideal i) T.mult →
      (s.projectionToBase i).base x ∈ orderAtLeastLocus T.ideal T.mult := by
  intro T s i
  induction i with
  | zero =>
      intro _ x hx
      rw [s.ideal_zero, orderAtLeastLocus_comap_iso_hom_eq_preimage] at hx
      rw [SequenceOfBlowups.projectionToBase_zero]
      exact hx
  | succ n ih =>
      intro hn x hx
      have hn' : n < s.length := hn
      have h1 : (s.transitionMapSucc n).base x ∈ orderAtLeastLocus (s.ideal n) T.mult :=
        OrderLocusBlowup.orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf (s.transitionMapSucc n) (s.center n)
          (s.isBlowupAlongIdealSheaf_blowupMorphism n hn') (s.ideal n) (s.ideal (n + 1)) T.mult
          (s.ideal_succ n hn') (s.center_order n hn') hx
      have h2 := ih (le_of_lt hn') _ h1
      rw [MarkedSequenceOfBlowups.projectionToBase_succ_apply]
      exact h2

theorem projectionToBase_mem_orderAtLeastLocus_of_mem_center : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ),
    i < s.length → ∀ x : ↥(s.schemeAt i),
      x ∈ (((s.center i).support : Set ↥(s.schemeAt i))) →
      (s.projectionToBase i).base x ∈ orderAtLeastLocus T.ideal T.mult := by
  intro T hT s i hi x hx
  exact projectionToBase_mem_orderAtLeastLocus_of_mem_ideal T s i (le_of_lt hi) x (s.center_order i hi hx)

theorem isStrictPullback_of_isPullback_of_center_nonempty : ∀ (X' X : Scheme.{u}) (φ : X' ⟶ X) (s' : SequenceOfBlowups X')
    (s : SequenceOfBlowups X), IsPullbackBlowupSequence φ s' s →
    (∀ i : ℕ, i < s.length → (((s.center i).support : Set ↥(s.schemeAt i))).Nonempty) →
    (∀ i : ℕ, i < s.length → ∀ x ∈ (((s.center i).support : Set ↥(s.schemeAt i))),
      (s.projectionToBase i).base x ∈ Set.range φ.base) →
    IsStrictPullbackBlowupSeq φ s' s := by
  intro X' X φ s' s hpb hne hran
  exact hpb.isStrictPullback_of_support_comap_center_nonempty (support_comap_center_nonempty_of_mem_range φ s hne hran)

end OrderReductionCorrectness

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.EmptyOrderLocusPullback
section


namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactFunctoriality

theorem isPullback_of_orderAtLeastLocus_comap_eq_empty
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})
    (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T)
    (Y : Scheme.{u}) (φ : Y ⟶ T.scheme) [Smooth φ]
    (n : SequenceOfBlowups Y) (hn : n.length = 0)
    (hempty : orderAtLeastLocus (T.ideal.comap φ) T.mult = (∅ : Set ↥Y)) :
    IsPullbackBlowupSequence φ n (maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
  have : CharZero T.base := h.valid.charZero
  have : Smooth T.structMap := h.valid.smooth
  refine isPullback_of_length_zero_of_comap_center_eq_top φ n
    (maxContactPrincipalization hinv A T).toSequenceOfBlowups hn ?_
  intro i hi ψ hψ
  refine Blowup.comap_eq_top_of_notMem_support ψ ((maxContactPrincipalization hinv A T).toSequenceOfBlowups.center i) ?_
  intro y hy
  have hmem : ((maxContactPrincipalization hinv A T).toSequenceOfBlowups.projectionToBase i).base (ψ.base y)
      ∈ orderAtLeastLocus T.ideal T.mult :=
    OrderReductionCorrectness.projectionToBase_mem_orderAtLeastLocus_of_mem_center T h.valid (maxContactPrincipalization hinv A T) i hi
      (ψ.base y) hy
  have hfy : φ.base y ∈ orderAtLeastLocus T.ideal T.mult := by
    have h1 : φ.base y
        = ((maxContactPrincipalization hinv A T).toSequenceOfBlowups.projectionToBase i).base (ψ.base y) := by
      rw [← hψ]
      rfl
    rw [h1]
    exact hmem
  have hcs := orderAtLeastLocus_comap T.base T.structMap φ T.ideal T.mult
  rw [hempty] at hcs
  have hy2 : y ∈ (∅ : Set ↥Y) := by
    rw [hcs]
    exact hfy
  exact hy2.elim

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderReductionCompatibility
section

open CategoryTheory.Limits

namespace FunctorialResolution.EmbeddedResolution.OrderReductionProperties

theorem tunedSheafProperties : TunedSheafProperties.{u} :=
  tunedSheafProperties_of_succ_le_of_mul_le tunedSheaf_succ_le.{u} tunedSheaf_mul_le_add.{u}

theorem maxContactHypersurfacesEtaleEquivalent : MaxContactHypersurfacesEtaleEquivalent.{u} := by
  apply FunctorialResolution.EmbeddedResolution.exists_etale_equalizing_isMaxContactHypersurface

theorem validPullbackAlongSmooth : OrderReduction.ValidPullbackAlongSmooth.{u} := by
  rw [OrderReduction.validPullbackAlongSmooth_iff]
  intro T hV Y q h hsm hqc hq
  have : Smooth h := hsm
  have : QuasiCompact q := hqc
  exact MarkedIdealWithBoundary.isAdmissible_pullbackAlong_of_smooth T hV Y q h hq

theorem validBaseChange : OrderReductionFieldBaseChange.ValidBaseChange.{u} := by
  unfold FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.ValidBaseChange
  intros
  apply MarkedIdealWithBoundary.isAdmissible_baseChange
  all_goals assumption

theorem orderAtBaseChangeEq : OrderReductionFieldBaseChange.OrderAtBaseChangeEq.{u} := by
  intro T L _ _ f hV y
  have : CharZero T.base := f.charZero
  cases hV
  have : Smooth T.structMap := by assumption
  exact FunctorialResolution.EmbeddedResolution.orderAt_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal y

private theorem derivIdealSheafIter_comap_of_isPullback_consolidated493
    {k L : Type u} [Field k] [Field L]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (CommRingCat.of k))
    (pY : Y ⟶ Spec (CommRingCat.of L))
    [Smooth pX] [Smooth pY]
    (f : k →+* L) (q : Y ⟶ X)
    (hq : IsPullback q pY pX (specMapOfFieldHom k L f))
    (I : X.IdealSheafData) (r : ℕ) :
    derivIdealSheafIterate L pY r (I.comap q)
      = (derivIdealSheafIterate k pX r I).comap q := by
  have hspec : specMapOfFieldHom k L f = Spec.map (CommRingCat.ofHom f) := rfl
  rw [hspec] at hq
  obtain ⟨e, hfst, hsnd⟩ :
      ∃ e : Y ≅ pullback pX (Spec.map (CommRingCat.ofHom f)),
        e.hom ≫ pullback.fst pX (Spec.map (CommRingCat.ofHom f)) = q ∧
          e.hom ≫ pullback.snd pX (Spec.map (CommRingCat.ofHom f)) = pY :=
    ⟨hq.isoPullback, hq.isoPullback_hom_fst, hq.isoPullback_hom_snd⟩
  clear hq
  subst hfst
  subst hsnd
  have : Smooth e.hom := inferInstance
  have key := derivIdealSheafIterate_comap_fieldBaseChange pX (CommRingCat.ofHom f) r I
  have h2 := derivIdealSheafIterate_comap L
      (pullback.snd pX (Spec.map (CommRingCat.ofHom f))) e.hom r
      (I.comap (pullback.fst pX (Spec.map (CommRingCat.ofHom f))))
  have hc1 : I.comap (e.hom ≫ pullback.fst pX (Spec.map (CommRingCat.ofHom f)))
      = (I.comap (pullback.fst pX (Spec.map (CommRingCat.ofHom f)))).comap e.hom := by
    simp [AlgebraicGeometry.Scheme.IdealSheafData.comap_comp]
  have hc2 : (derivIdealSheafIterate k pX r I).comap
        (e.hom ≫ pullback.fst pX (Spec.map (CommRingCat.ofHom f)))
      = ((derivIdealSheafIterate k pX r I).comap
          (pullback.fst pX (Spec.map (CommRingCat.ofHom f)))).comap e.hom := by
    simp [AlgebraicGeometry.Scheme.IdealSheafData.comap_comp]
  rw [hc1, hc2, h2, key]

theorem derivIdealSheafIterate_comm_baseChange : DerivIdealSheafIterateCommBaseChange.{u} := by
  unfold DerivIdealSheafIterateCommBaseChange
  intros
  apply derivIdealSheafIter_comap_of_isPullback_consolidated493 <;> assumption

theorem isBalanced_baseChange (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (hft : LocallyOfFiniteType (T.baseChange K f).structMap)
    (hB : T.IsBalanced hV.locallyOfFiniteType) :
    (T.baseChange K f).IsBalanced hft := by
  have : CharZero T.base := f.charZero
  have hlft : LocallyOfFiniteType T.structMap := hV.locallyOfFiniteType
  have hsm : Smooth T.structMap := by
    clear hB
    cases hV
    assumption
  have hft' : LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd T.structMap
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f))) := hft
  have hB' : FunctorialResolution.EmbeddedResolution.IsDerivBalanced T.base T.structMap T.ideal T.mult := hB
  have hgoal : FunctorialResolution.EmbeddedResolution.IsDerivBalanced K
      (CategoryTheory.Limits.pullback.snd T.structMap
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)))
      (T.ideal.comap (CategoryTheory.Limits.pullback.fst T.structMap
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)))) T.mult := by
    apply FunctorialResolution.EmbeddedResolution.isDerivBalanced_of_pow_le
    intro i hi
    rw [FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_comap_fieldBaseChange (L := K) T.structMap
        (CommRingCat.ofHom f) i T.ideal,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_pow,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_pow]
    apply AlgebraicGeometry.Scheme.IdealSheafData.comap_mono
    exact FunctorialResolution.EmbeddedResolution.IsDerivBalanced.derivIdealSheafIterate_pow_le T.base T.structMap hB' hi
  exact hgoal

theorem forall_isAdmissible_dropTrivialBoundary : MaxContactFunctoriality.DropTrivialBoundaryAdmissible.{u} := by
  intro T hV
  have key : ∀ L : List T.scheme.IdealSheafData,
      MarkedIdealWithBoundary.SameNontrivialBoundary T.boundary L → (T.withBoundary L).IsAdmissible := by
    intro L hL
    have hL' := hL.symm
    apply MarkedIdealWithBoundary.validOfSameNontrivialBoundary <;> assumption
  rw [MaxContactReduction.dropTrivialBoundary_def]
  apply key
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff]
  simp [MarkedIdealWithBoundary.nontrivialPart, List.filter_filter]
  congr 1
  funext D
  by_cases hD : D = ⊤ <;> simp [hD]

section
variable {X : Scheme.{u}}

private theorem filterNeTop_cons_top_consolidated493 (L : List X.IdealSheafData) :
    FunctorialResolution.EmbeddedResolution.filterNeTop ((⊤ : X.IdealSheafData) :: L) = FunctorialResolution.EmbeddedResolution.filterNeTop L := by
  simp [FunctorialResolution.EmbeddedResolution.filterNeTop]

private theorem filterNeTop_cons_of_ne_top_consolidated493 {D : X.IdealSheafData} (hD : D ≠ ⊤) (L : List X.IdealSheafData) :
    FunctorialResolution.EmbeddedResolution.filterNeTop (D :: L) = D :: FunctorialResolution.EmbeddedResolution.filterNeTop L := by
  simp [FunctorialResolution.EmbeddedResolution.filterNeTop, hD]


end

private theorem filterNeTop_map_filter_append_consolidated493 {X Y : Scheme.{u}}
    (f : X.IdealSheafData → Y.IdealSheafData) (hf : f ⊤ = ⊤)
    (p : X.IdealSheafData → Bool)
    (hp : ∀ D : X.IdealSheafData, p D = false → D = ⊤)
    (R : List Y.IdealSheafData) (L : List X.IdealSheafData) :
    FunctorialResolution.EmbeddedResolution.filterNeTop (List.map f (List.filter p L) ++ R)
      = FunctorialResolution.EmbeddedResolution.filterNeTop (List.map f L ++ R) := by
  induction L with
  | nil => rfl
  | cons D L ih =>
      by_cases hpD : p D = true
      · rw [List.filter_cons, if_pos hpD, List.map_cons, List.map_cons,
          List.cons_append, List.cons_append]
        by_cases hfD : f D = ⊤
        · rw [hfD, filterNeTop_cons_top_consolidated493, filterNeTop_cons_top_consolidated493]
          exact ih
        · rw [filterNeTop_cons_of_ne_top_consolidated493 hfD, filterNeTop_cons_of_ne_top_consolidated493 hfD, ih]
      · have hDtop : D = ⊤ := hp D (by simpa using hpD)
        rw [List.filter_cons, if_neg hpD, List.map_cons, List.cons_append, hDtop, hf,
          filterNeTop_cons_top_consolidated493]
        exact ih

private theorem filterNeTop_boundary_filter_consolidated493 {X : Scheme.{u}}
    (d : BlowupSequenceData X) (p : X.IdealSheafData → Bool)
    (hp : ∀ D : X.IdealSheafData, p D = false → D = ⊤)
    (L : List X.IdealSheafData) (i : ℕ) :
    FunctorialResolution.EmbeddedResolution.filterNeTop (d.boundaryFrom (List.filter p L) i)
      = FunctorialResolution.EmbeddedResolution.filterNeTop (d.boundaryFrom L i) := by
  rw [BlowupSequenceData.boundary_eq_map_iteratedStrictTransform_append d (List.filter p L) i,
    BlowupSequenceData.boundary_eq_map_iteratedStrictTransform_append d L i]
  exact filterNeTop_map_filter_append_consolidated493 (d.iteratedStrictTransform i)
    (d.iteratedStrictTransform_top i) p hp (d.boundaryFrom [] i) L

theorem isMarked_of_isMarked_dropTrivialBoundary (T : MarkedIdealWithBoundary.{u}) (_hV : T.IsAdmissible)
    (d : BlowupSequenceData T.scheme) (I : T.scheme.IdealSheafData) (m : ℕ)
    (h : d.IsMarked T.structMap I m (MaxContactReduction.dropTrivialBoundary T).boundary) :
    d.IsMarked T.structMap I m T.boundary := by
  refine ⟨h.divisible, h.center_order, h.center_smooth, ?_⟩
  intro i hi
  have key : FunctorialResolution.EmbeddedResolution.filterNeTop (d.boundaryFrom (MaxContactReduction.dropTrivialBoundary T).boundary i)
      = FunctorialResolution.EmbeddedResolution.filterNeTop (d.boundaryFrom T.boundary i) := by
    rw [MaxContactReduction.dropTrivialBoundary_boundary]
    refine filterNeTop_boundary_filter_consolidated493 d _ ?_ T.boundary i
    intro D hD
    simpa using hD
  exact hasStrictNormalCrossingsWith_of_filterNeTop_eq _ _ _ _ key (h.center_snc i hi)

theorem forall_isMarked_of_isMarked_dropTrivialBoundary : MaxContactFunctoriality.MarkedOfMarkedDropTrivialBoundary.{u} := by
  intro T hV d h
  exact isMarked_of_isMarked_dropTrivialBoundary T hV d T.ideal T.mult h

theorem orderCertificateLocalToGlobal : OrderCertificateLocalToGlobal.{u} := by
  intro k _ W p N μ Mem Z h
  exact FunctorialResolution.EmbeddedResolution.OrderCertificate.localize (fun z _ => (h z).choose)
    (fun z _ => (h z).choose_spec.1) (fun z _ => (h z).choose_spec.2)

theorem isSmoothDivisorStableUnderSmoothPullback : IsSmoothDivisorStableUnderSmoothPullback.{u} := by
  unfold FunctorialResolution.EmbeddedResolution.IsSmoothDivisorStableUnderSmoothPullback
  intros
  exact FunctorialResolution.EmbeddedResolution.isSmoothDivisor_comap_of_mem_inStrictNormalCrossingPosition _ _ _
      (FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPosition_singleton_of_isSmoothDivisor _ _ (by assumption)) _
      (List.mem_singleton_self _)

theorem maxContactHypersurfaceSmoothPullback : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u} :=
  maxContactHypersurfaceSmoothPullback_of_isSmoothDivisorStableUnderSmoothPullback isSmoothDivisorStableUnderSmoothPullback.{u}

section
variable (htf : TunedSheafProperties.{u})
include htf

private theorem isMaxContactInvariant_balancedTunedSheaf_consolidated493 (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    [LocallyOfFiniteType p] (I : X.IdealSheafData) (m : ℕ)
    (hm : 1 ≤ m) (hmax : FunctorialResolution.EmbeddedResolution.MaxOrderEq I m) :
    FunctorialResolution.EmbeddedResolution.IsMaxContactInvariant k p (FunctorialResolution.EmbeddedResolution.balancedTunedSheaf k p I m) (FunctorialResolution.EmbeddedResolution.tuningExponent m) := by
  apply FunctorialResolution.EmbeddedResolution.isMaxContactInvariant_of_mul_le
  rw [FunctorialResolution.EmbeddedResolution.maxContactIdeal_eq_derivIdealSheafIterate, FunctorialResolution.EmbeddedResolution.balancedTunedSheaf_eq]
  exact htf.derivIdealSheafIter_mul_derivIdealSheaf_le_tunedSheaf k X p I m hm hmax
    (FunctorialResolution.EmbeddedResolution.tuningExponent m) (FunctorialResolution.EmbeddedResolution.one_le_tuningExponent m)

theorem isMaxContactInvariantBalancedTuned_of_tunedSheafProperties :
    BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u} := by
  unfold FunctorialResolution.EmbeddedResolution.BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned
  intros
  apply isMaxContactInvariant_balancedTunedSheaf_consolidated493 htf
  all_goals assumption


end

theorem isAdmissible_withBoundary_ker_of_isSmoothDivisor (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    {Y : Scheme.{u}} (e : Y ⟶ T.scheme) [IsClosedImmersion e]
    (hD : IsSmoothDivisor T.structMap (Scheme.Hom.ker e)) :
    (T.withBoundary [Scheme.Hom.ker e]).IsAdmissible := by
  have hsm : Smooth T.structMap := by
    cases hV
    assumption
  have hcz : CharZero T.base := by
    cases hV
    assumption
  have hsnc : FunctorialResolution.EmbeddedResolution.InStrictNormalCrossingPosition T.structMap [Scheme.Hom.ker e] :=
    FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPosition_singleton_of_isSmoothDivisor T.structMap (Scheme.Hom.ker e) hD
  cases hV
  constructor <;> assumption

private theorem removeUnitIdeals_eq_nontrivialPart_consolidated493 {X : Scheme.{u}} (L : List X.IdealSheafData) :
    FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.removeUnitIdeals L = FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.nontrivialPart L := by
  unfold FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.removeUnitIdeals FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.nontrivialPart
  congr 1
  funext D
  by_cases hD : D = ⊤ <;> simp [hD]

private theorem smoothPullbackTriple_eq_pullbackWithNontrivialBoundary_consolidated493 (S : EmbeddedResolution.MarkedIdealWithBoundary.{u})
    {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [Smooth q] :
    FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.smoothPullbackTriple S q = FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q := by
  unfold FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.smoothPullbackTriple FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary
  rw [removeUnitIdeals_eq_nontrivialPart_consolidated493]
  rfl

theorem separateBoundary_pullback_of_smooth (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment.{u}) :
    MaxContactFunctoriality.LoopCompatibleWithSmoothPullback hinv P A := by
  unfold FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.LoopCompatibleWithSmoothPullback
  intro hstar hin hMC hAdm hmono B hspec hshift T T' hPdimT hPdimOther S hV hO hdimS H hH hHsnc hlive
    X' q hsm hV' hdim' hH' hH'snc
  have : Smooth q := hsm
  have heq : FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.smoothPullbackTriple S q = FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q :=
    smoothPullbackTriple_eq_pullbackWithNontrivialBoundary_consolidated493 S q
  have hV2 : (FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible := by
    rw [← heq]; exact hV'
  have hdim2 : (FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q).krullDimSucc ≤ T'.krullDimSucc := by
    rw [← heq]; exact hdim'
  have hH2 : ∀ [inst : LocallyOfFiniteType
        (FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap],
      FunctorialResolution.EmbeddedResolution.IsMaxContactHypersurface (FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q).base
        (FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap (FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal
        (FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult (H.comap q) := by
    intro inst
    have hft2 : LocallyOfFiniteType
        (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.smoothPullbackTriple S q).structMap := inst
    exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isMaxContactHypersurface_of_triple_eq heq.symm inst hft2
      (H.comap q) (H.comap q) HEq.rfl hH'
  have hH2snc : FunctorialResolution.EmbeddedResolution.InStrictNormalCrossingPosition (FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap
      [H.comap q] :=
    FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.inStrictNormalCrossingPosition_of_triple_eq heq.symm [H.comap q] [H.comap q]
      HEq.rfl hH'snc
  have hmain := FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isPullbackBlowupSequence_reduceAlongHypersurface_lowerDimensionalFamily.{u, u} hstar
    hin hMC hAdm hinv P hmono A B hspec hshift T T' hPdimT hPdimOther S hV hO hdimS hlive H hH hHsnc q hV2
    hdim2 hH2 hH2snc
  have hstep : (FunctorialResolution.EmbeddedResolution.MaxContactReduction.reduceAlongHypersurface hinv T'
        (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.lowerDimensionalFamily A T')
        (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.smoothPullbackTriple S q) (H.comap q)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      = (FunctorialResolution.EmbeddedResolution.MaxContactReduction.reduceAlongHypersurface hinv T' (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.lowerDimensionalFamily A T')
        (FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q) (H.comap q)).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
    eq_of_heq (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.reduceAlongHypersurface_toSequenceOfBlowups_heq hinv T'
      (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.lowerDimensionalFamily A T') heq (H.comap q) (H.comap q) HEq.rfl)
  exact Eq.mpr (congrArg (fun z => FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence q z
    (FunctorialResolution.EmbeddedResolution.MaxContactReduction.reduceAlongHypersurface hinv T (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.lowerDimensionalFamily A T) S
      H).toMarkedSequenceOfBlowups.toSequenceOfBlowups) hstep) hmain

theorem orderReductionHypotheses : OrderReduction.OrderReductionHypotheses.{u} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact EmbeddedResolution.OrderReductionCorrectness.existsMaxContactControlledTransforms.{u}
  · exact FunctorialResolution.EmbeddedResolution.OrderReductionCorrectness.projectionToBase_mem_orderAtLeastLocus_of_mem_center
  · exact FunctorialResolution.EmbeddedResolution.OrderReductionCorrectness.isBalanced_comap_of_smooth
  · intro V W f hf hN hdim
    have : Etale f := hf
    have : IsLocallyNoetherian W := hN
    exact FunctorialResolution.EmbeddedResolution.krullDimSucc_le_of_etale f hdim
  · exact FunctorialResolution.EmbeddedResolution.OrderReductionCorrectness.isLocallyNoetherian_schemeAt
  · exact EmbeddedResolution.OrderReductionCorrectness.blowupLiftEqOnControlledTransform.{u}
  · exact FunctorialResolution.EmbeddedResolution.OrderReductionCorrectness.le_of_support_subset_of_smooth
  · exact maxContactHypersurfacesEtaleEquivalent.{u}
  · exact FunctorialResolution.EmbeddedResolution.OrderReductionCorrectness.isStrictPullback_of_isPullback_of_center_nonempty
  · intro T hV Y q h hsm hqc hq
    have : Smooth h := hsm
    have : QuasiCompact q := hqc
    exact MarkedIdealWithBoundary.isAdmissible_pullbackAlong_of_smooth T hV Y q h hq

theorem maxContactCoverProperties : MaxContactCoverProperties.{u} :=
  FunctorialResolution.EmbeddedResolution.OrderReduction.maxContactCoverProperties_of_tunedSheafProperties.{u} tunedSheafProperties.{u} EmbeddedResolution.dimensionNonincreasingAlongBlowups.{u}
    validPullbackAlongSmooth.{u}

theorem isBaseChangeInherited (P : ℕ → Prop) : IsBaseChangeInherited.{u} P := by
  unfold FunctorialResolution.EmbeddedResolution.IsBaseChangeInherited
  intro T L _ _ f hV hP hO hB
  have : CharZero T.base := f.charZero
  refine ⟨MarkedIdealWithBoundary.isAdmissible_baseChange T hV L f, ?_, ?_, ?_⟩
  · rw [MarkedIdealWithBoundary.dim_baseChange T hV L f]
    exact hP
  · intro y
    have hsm : Smooth T.structMap := by
      cases hV
      assumption
    have := hsm
    have key := FunctorialResolution.EmbeddedResolution.orderAt_comap_fieldBaseChange (k := T.base) (L := L) T.structMap
      (CommRingCat.ofHom f) T.ideal y
    exact key.trans_le (hO _)
  · intro hft
    exact isBalanced_baseChange T hV L f hft (hB _)

section
variable (hinv : ComapIsoInvariance.{u})

theorem coverSequenceProperties_of_isBoundaryDivisorReduction (n : ℕ)
    (A : ℕ → PrincipalizationAssignment.{u}) (L : PrincipalizationAssignment.{u})
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L) :
    MaxContactFunctoriality.CoverSequenceProperties hinv (fun d => d ≤ n) A := by
  have hmono : ∀ a b : ℕ, a ≤ b → b ≤ n → a ≤ n := fun _ _ hab hb => le_trans hab hb
  have hstar : MaxContactCoverProperties.{u} := maxContactCoverProperties
  have hin : OrderReduction.OrderReductionHypotheses.{u} := orderReductionHypotheses
  have hopen : ∀ (k : Type u) [Field k], FunctorialResolution.EmbeddedResolution.OpenImmersionStability k :=
    fun k inst => @FunctorialResolution.EmbeddedResolution.openImmersionStability k inst
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T h i hi
    exact FunctorialResolution.EmbeddedResolution.BoundarySeparationByMaxContact.center_coverMarkedBlowupData_ne_top hstar hinv (fun d => d ≤ n) hmono A L
      hdiv T h i hi
  · intro T h hmult i hi
    exact FunctorialResolution.EmbeddedResolution.BoundarySeparationByMaxContact.orderCertificate_coverMarkedBlowupData_of_mult_eq_one hstar hopen hinv
      (fun d => d ≤ n) hmono A L hdiv T h hmult i hi
  · intro T h
    exact FunctorialResolution.EmbeddedResolution.MaxContactCoverDescent.exists_isStrictPullback_coverMarkedSequence hstar hin hinv
      (fun d => d ≤ n) hmono A L hdiv
      (isMaxContactInvariantBalancedTuned_of_tunedSheafProperties tunedSheafProperties.{u}) maxContactHypersurfaceSmoothPullback.{u} T h
  · intro T h hbd hmult Y q e hei _hq hD J _hJv hJ
    have : IsClosedImmersion e := hei
    exact FunctorialResolution.EmbeddedResolution.MaxContactCoverData.isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_isSmoothDivisor hstar hin hinv
      (fun d => d ≤ n) hmono A L hdiv T h hbd hmult e hD J hJ
      (isAdmissible_withBoundary_ker_of_isSmoothDivisor T h.valid e hD)
  · intro T h
    exact FunctorialResolution.EmbeddedResolution.BoundarySeparationByMaxContact.orderAtLeastLocus_coverMarkedBlowupData_eq_empty hstar hinv (fun d => d ≤ n) hmono
      A L hdiv T h

theorem markingDescends (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment.{u}) :
    MaxContactFunctoriality.MarkingDescends hinv P A := by
  unfold FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.MarkingDescends
  intro T h d hd
  have hv : T.IsAdmissible := h.valid
  have hcz : CharZero T.base := by
    cases hv
    assumption
  have hsm : Smooth T.structMap := by
    cases hv
    assumption
  have hlft : LocallyOfFiniteType T.structMap := hv.locallyOfFiniteType
  have hsurj : AlgebraicGeometry.Surjective (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap T hv) :=
    FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.coverMap_surjective tunedSheafProperties.{u} T h
  have hoi : FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.IsLocalIsomorphism
      (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap T hv) :=
    FunctorialResolution.EmbeddedResolution.MaxContactOpenCover.isLocalIsomorphism_coverMap T hv
  have hmult : 1 ≤ FunctorialResolution.EmbeddedResolution.MaxContactCoverData.tunedMult T := FunctorialResolution.EmbeddedResolution.one_le_tuningExponent T.mult
  have hstar : MaxContactCoverProperties.{u} := maxContactCoverProperties
  have hlev := FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isLocallyNoetherian_schemeAt_coverBlowupSequence hinv A hstar T h d hd
  have hmax : FunctorialResolution.EmbeddedResolution.MaxOrderEq T.ideal T.mult :=
    ⟨(FunctorialResolution.EmbeddedResolution.orderLE_iff T.ideal T.mult).2 h.orderLE, h.coSupport_nonempty⟩
  have key := FunctorialResolution.EmbeddedResolution.isMarked_balancedTunedIdeal_of_isStrictPullbackBlowupSeq hinv P A T h hoi hmult d hd hlev.1 hlev.2
    (fun D i hi =>
      FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isLocalIsomorphism_map_coverBlowupSequence hinv A T h d D i hi)
  have htuned : FunctorialResolution.EmbeddedResolution.MaxContactCoverData.balancedTunedIdeal T hv
      = FunctorialResolution.EmbeddedResolution.balancedTunedSheaf T.base T.structMap T.ideal T.mult :=
    FunctorialResolution.EmbeddedResolution.MaxContactCoverData.balancedTunedIdeal_eq_balancedTunedSheaf T hv
  have htm : FunctorialResolution.EmbeddedResolution.MaxContactCoverData.tunedMult T = FunctorialResolution.EmbeddedResolution.tuningExponent T.mult := rfl
  have key2 : d.IsMarked T.structMap (FunctorialResolution.EmbeddedResolution.balancedTunedSheaf T.base T.structMap T.ideal T.mult)
      (FunctorialResolution.EmbeddedResolution.tuningExponent T.mult) T.boundary := by
    rw [← htuned, ← htm]
    exact key
  exact ((tunedSheafProperties.{u}.isMarked_tuned_iff T.base T.scheme T.structMap T.ideal T.mult
    hv.one_le_mult hmax T.boundary d).1).mpr key2


end

private theorem coverFaithfullyFlat_consolidated493 (P : ℕ → Prop) :
    MaxContactFunctoriality.CoverFaithfullyFlat.{u} P := by
  intro T h
  exact ⟨MaxContactFunctoriality.coverMap_surjective tunedSheafProperties.{u} T h,
    MaxContactFunctoriality.coverMap_flat T h⟩

section
variable {P : CategoryTheory.MorphismProperty Scheme.{u}} [CategoryTheory.MorphismProperty.IsStableUnderBaseChange P] {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

private theorem pullback_snd_of_isStableUnderBaseChange_consolidated493
    (hf : P f) :
    P (pullback.snd f g) :=
  CategoryTheory.MorphismProperty.of_isPullback (P := P)
    (CategoryTheory.IsPullback.of_hasPullback f g) hf

private theorem pullback_fst_of_isStableUnderBaseChange_consolidated493
    (hg : P g) :
    P (pullback.fst f g) :=
  CategoryTheory.MorphismProperty.of_isPullback (P := P)
    (CategoryTheory.IsPullback.of_hasPullback f g).flip hg


end

section
variable (hinv : ComapIsoInvariance.{u})

theorem isStrictPullbackBlowupSeq_maxContact_baseChange
    (n : ℕ) (A : ℕ → PrincipalizationAssignment.{u})
    (L : PrincipalizationAssignment.{u})
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : T.krullDimSucc ≤ n)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E')
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hP' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n) :
    IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base K f))
      (MaxContactFunctoriality.maxContactPrincipalization hinv A
        ((T.baseChange K f).withBoundary E')).toSequenceOfBlowups
      (MaxContactFunctoriality.maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
  have hcz : CharZero T.base := f.charZero
  have hsm : Smooth T.structMap := by
    cases hV
    assumption
  have hflat0 : Flat (specMapOfFieldHom T.base K f) := inferInstance
  have hflat : Flat
      (pullback.fst T.structMap (specMapOfFieldHom T.base K f)) :=
    pullback_fst_of_isStableUnderBaseChange_consolidated493 (P := @AlgebraicGeometry.Flat.{u}) _ _ hflat0
  have hordS : ∀ x : ↥((T.baseChange K f).withBoundary E').scheme,
      orderAt ((T.baseChange K f).withBoundary E').ideal x
        = orderAt T.ideal ((pullback.fst T.structMap (specMapOfFieldHom T.base K f)) x) :=
    FunctorialResolution.EmbeddedResolution.orderAt_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal
  have hcsS : orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal
      ((T.baseChange K f).withBoundary E').mult
      = (pullback.fst T.structMap (specMapOfFieldHom T.base K f)) ⁻¹' orderAtLeastLocus T.ideal T.mult :=
    FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal T.mult
  have hordBound : ∀ x : ↥((T.baseChange K f).withBoundary E').scheme,
      orderAt ((T.baseChange K f).withBoundary E').ideal x
        ≤ ((((T.baseChange K f).withBoundary E').mult : ℕ) : ℕ∞) := by
    intro x
    rw [hordS x]
    exact hO _
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  · have hempS : orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal
        ((T.baseChange K f).withBoundary E').mult = ∅ := by
      rw [hcsS, hemp]
      exact Set.preimage_empty
    refine FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.of_length_zero _ _ _ ?_ ?_
    · exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (fun d => d ≤ n) A
        ((T.baseChange K f).withBoundary E') hV' hP' hordBound hempS
    · exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (fun d => d ≤ n) A
        T hV hP hO hemp
  · have hne : (orderAtLeastLocus T.ideal T.mult).Nonempty := Set.nonempty_iff_ne_empty.mpr hemp
    have hyp : MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n) T := ⟨hP, hO, hne, hV⟩
    have hneS : (orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal
        ((T.baseChange K f).withBoundary E').mult).Nonempty := by
      rw [hcsS]
      exact Set.Nonempty.preimage hne
        (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.surjective_baseChange_fst T K f).1
    have hypS : MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n)
        ((T.baseChange K f).withBoundary E') := ⟨hP', hordBound, hneS, hV'⟩
    have htrimv : (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).IsAdmissible := forall_isAdmissible_dropTrivialBoundary.{u} T hV
    have hyptrim : MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n) (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) :=
      hyp.of_dropTrivialBoundaryAdmissible forall_isAdmissible_dropTrivialBoundary.{u}
    have htrEq : FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary ((T.baseChange K f).withBoundary E')
        = (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f) :=
      FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundary_withBoundary_baseChange T K f E' hE
    have hypA : MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n)
        ((FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)) := by
      rw [← htrEq]
      exact hypS.of_dropTrivialBoundaryAdmissible forall_isAdmissible_dropTrivialBoundary.{u}
    have hA'v : ((FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
        (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)).IsAdmissible := hypA.valid
    have hDv : (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
        ((FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)) hA'v).IsAdmissible :=
      FunctorialResolution.EmbeddedResolution.BoundarySeparationByMaxContact.isAdmissible_coverTriple maxContactCoverProperties (fun d => d ≤ n) _ hypA
    have hcoverAdm : (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T)
        htrimv).IsAdmissible :=
      FunctorialResolution.EmbeddedResolution.BoundarySeparationByMaxContact.isAdmissible_coverTriple maxContactCoverProperties (fun d => d ≤ n) _ hyptrim
    have hCbcv : ((FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T)
        htrimv).baseChange K
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.coverBaseFieldHom (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f))).IsAdmissible :=
      MarkedIdealWithBoundary.isAdmissible_baseChange _ hcoverAdm K
        (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.coverBaseFieldHom (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv K
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f))
    have hnD : IsNoetherian
        (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
          ((FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)) hA'v).scheme := hDv.isNoetherian
    have hnC : IsNoetherian
        ((FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv).baseChange K
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.coverBaseFieldHom (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f))).scheme := hCbcv.isNoetherian
    have hqcCover : QuasiCompact
        (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap
          ((FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)) hA'v) := by
      constructor
      intro U hU hU2
      have hns : TopologicalSpace.NoetherianSpace
          ↥(FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
            ((FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
              (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)) hA'v).scheme := inferInstance
      exact @TopologicalSpace.NoetherianSpace.isCompact _ _ hns _
    have hqcCbc : QuasiCompact
        ((FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv).baseChange K
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.coverBaseFieldHom (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f))).structMap := by
      constructor
      intro U hU hU2
      have hns : TopologicalSpace.NoetherianSpace
          ↥((FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T)
              htrimv).baseChange K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.coverBaseFieldHom (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv K
              (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f))).scheme := inferInstance
      exact @TopologicalSpace.NoetherianSpace.isCompact _ _ hns _
    have hqcSnd : QuasiCompact
        (pullback.snd
          (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap
            ((FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
              (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)) hA'v)
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.coverBaseChangeMap (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f))) :=
      pullback_snd_of_isStableUnderBaseChange_consolidated493 (P := @AlgebraicGeometry.QuasiCompact.{u}) _ _
        hqcCover
    have hetSnd : Etale
        (pullback.snd
          (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap
            ((FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
              (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)) hA'v)
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.coverBaseChangeMap (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f))) :=
      pullback_snd_of_isStableUnderBaseChange_consolidated493 (P := @AlgebraicGeometry.Etale.{u}) _ _
        inferInstance
    have hdimChart : ((FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T)
        htrimv).baseChange K
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.coverBaseFieldHom (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f))).krullDimSucc ≤ (T.baseChange K f).krullDimSucc := by
      rw [MarkedIdealWithBoundary.dim_baseChange _ hcoverAdm, MarkedIdealWithBoundary.dim_baseChange T hV]
      have h1 := FunctorialResolution.EmbeddedResolution.MaxContactOpenCover.krullDimSucc_coverTriple_scheme_le_dim (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv
      rw [FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary_dim] at h1
      exact h1
    have hdimQ := FunctorialResolution.EmbeddedResolution.krullDimSucc_le_of_etale
      (pullback.snd
        (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap
          ((FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)) hA'v)
        (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.coverBaseChangeMap (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv K
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)))
      hCbcv.topologicalKrullDim_lt_top
    exact FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.isStrictPullbackBlowupSeq_baseChange_withBoundary
      maxContactCoverProperties orderReductionHypotheses (isMaxContactInvariantBalancedTuned_of_tunedSheafProperties tunedSheafProperties.{u})
      maxContactHypersurfaceSmoothPullback.{u} derivIdealSheafIterate_comm_baseChange.{u} validBaseChange.{u} orderAtBaseChangeEq.{u}
      EmbeddedResolution.OrderReductionFieldBaseChange.maxContactHypersurfaceBaseChange.{u} hinv (fun d => d ≤ n)
      (fun _ _ hab hb => le_trans hab hb) A L hdiv (isBaseChangeInherited (fun d => d ≤ n))
      (coverSequenceProperties_of_isBoundaryDivisorReduction hinv n A L hdiv) (markingDescends hinv (fun d => d ≤ n) A)
      (coverFaithfullyFlat_consolidated493 (fun d => d ≤ n)) forall_isAdmissible_dropTrivialBoundary.{u} forall_isMarked_of_isMarked_dropTrivialBoundary.{u}
      T hV hP hO K f E' hE hV' hP' hdimChart
      (MorphismProperty.comp_mem (@AlgebraicGeometry.QuasiCompact.{u}) _ _ hqcSnd hqcCbc)
      (le_trans hdimQ hdimChart)

private theorem center_maxContact_ne_top_consolidated493
    (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})
    (hsf : MaxContactFunctoriality.CoverSequenceProperties hinv P A)
    (hmd : MaxContactFunctoriality.MarkingDescends hinv P A)
    (S : MarkedIdealWithBoundary.{u}) (hS : MaxContactFunctoriality.OrderReductionHypotheses P S) :
    ∀ i < (MaxContactFunctoriality.maxContactPrincipalization hinv A S).toSequenceOfBlowups.length,
      (MaxContactFunctoriality.maxContactPrincipalization hinv A S).toSequenceOfBlowups.center i ≠ ⊤ := by
  obtain ⟨d, hpb, heq⟩ :=
    FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.exists_isStrictPullback_cover_dropTrivialBoundary hsf hmd forall_isAdmissible_dropTrivialBoundary.{u}
      forall_isMarked_of_isMarked_dropTrivialBoundary.{u} S hS
  rw [heq]
  exact hpb.center_ne_top_of_forall_center_ne_top
    (hsf.center_ne_top _ (hS.of_dropTrivialBoundaryAdmissible forall_isAdmissible_dropTrivialBoundary.{u}))

theorem maxContact_baseChange_isPullbackBlowupSequence
    (n : ℕ) (A : ℕ → PrincipalizationAssignment.{u})
    (L : PrincipalizationAssignment.{u})
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : T.krullDimSucc ≤ n)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E')
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hP' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n)
    (hO' : ∀ x : ↥((T.baseChange K f).withBoundary E').scheme,
      orderAt ((T.baseChange K f).withBoundary E').ideal x ≤ (T.mult : ℕ∞)) :
    IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base K f))
      (MaxContactFunctoriality.maxContactPrincipalization hinv A
        ((T.baseChange K f).withBoundary E')).toSequenceOfBlowups
      (MaxContactFunctoriality.maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
  have hstrict := isStrictPullbackBlowupSeq_maxContact_baseChange hinv n A L hdiv T hV hP hO K f
    E' hE hV' hP'
  have hmult : ((T.baseChange K f).withBoundary E').mult = T.mult := by
    rw [MarkedIdealWithBoundary.withBoundary_mult, MarkedIdealWithBoundary.baseChange_mult]
  have hideal : ((T.baseChange K f).withBoundary E').ideal
      = T.ideal.comap (pullback.fst T.structMap (specMapOfFieldHom T.base K f)) := by
    rw [MarkedIdealWithBoundary.withBoundary_ideal, MarkedIdealWithBoundary.baseChange_ideal]
  have hO2 : ∀ x : ↥((T.baseChange K f).withBoundary E').scheme,
      orderAt ((T.baseChange K f).withBoundary E').ideal x
        ≤ ((((T.baseChange K f).withBoundary E').mult : ℕ) : ℕ∞) := by
    intro x
    rw [hmult]
    exact hO' x
  by_cases hemp : FunctorialResolution.EmbeddedResolution.orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal
      ((T.baseChange K f).withBoundary E').mult = ∅
  · have hlen' : (MaxContactFunctoriality.maxContactPrincipalization hinv A
        ((T.baseChange K f).withBoundary E')).length = 0 :=
      FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (fun d => d ≤ n) A
        ((T.baseChange K f).withBoundary E') hV' hP' hO2 hemp
    have hemp2 : FunctorialResolution.EmbeddedResolution.orderAtLeastLocus
        (T.ideal.comap (pullback.fst T.structMap (specMapOfFieldHom T.base K f))) T.mult = ∅ := by
      rw [hideal, hmult] at hemp
      exact hemp
    have : AlgebraicGeometry.Surjective (pullback.fst T.structMap (specMapOfFieldHom T.base K f)) :=
      FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.surjective_baseChange_fst T K f
    have hempT : FunctorialResolution.EmbeddedResolution.orderAtLeastLocus T.ideal T.mult = ∅ :=
      FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_eq_empty_of_comap_eq_empty
        (pullback.fst T.structMap (specMapOfFieldHom T.base K f)) T.ideal T.mult hemp2
    have hlen : (MaxContactFunctoriality.maxContactPrincipalization hinv A T).length = 0 :=
      FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (fun d => d ≤ n) A T hV hP hO
        hempT
    exact FunctorialResolution.EmbeddedResolution.isPullback_of_length_eq_zero_of_length_eq_zero _ _ _ hlen' hlen
  · have hhyp' : MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n)
        ((T.baseChange K f).withBoundary E') :=
      ⟨hP', hO2, Set.nonempty_iff_ne_empty.mpr hemp, hV'⟩
    have hct := center_maxContact_ne_top_consolidated493 hinv (fun d => d ≤ n) A
      (coverSequenceProperties_of_isBoundaryDivisorReduction hinv n A L hdiv) (markingDescends hinv (fun d => d ≤ n) A)
      ((T.baseChange K f).withBoundary E') hhyp'
    exact (hstrict.isPullbackSequenceOfBlowups_withoutIsoBlowups).of_isomorphic
      (FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_isomorphic_self _ hct)


end

section
variable {X : Scheme.{u}} (L : List X.IdealSheafData)

private theorem nontrivialPart_idem_consolidated493 :
    FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.nontrivialPart (FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.nontrivialPart L)
      = FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.nontrivialPart L := by
  simp [FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.nontrivialPart, List.filter_filter]

private theorem sameNontrivialBoundary_removeUnitIdeals_consolidated493 :
    FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.SameNontrivialBoundary (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.removeUnitIdeals L) L := by
  rw [FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.sameNontrivialBoundary_iff, removeUnitIdeals_eq_nontrivialPart_consolidated493]
  exact nontrivialPart_idem_consolidated493 L


end

private theorem isAdmissible_withBoundary_of_sameNontrivialBoundary_consolidated493 (S : EmbeddedResolution.MarkedIdealWithBoundary.{u})
    (E F : List S.scheme.IdealSheafData)
    (hV : (S.withBoundary E).IsAdmissible)
    (hsame : FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.SameNontrivialBoundary F E) :
    (S.withBoundary F).IsAdmissible := by
  have hEF : FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.SameNontrivialBoundary E F := hsame.symm
  have h2 : ((S.withBoundary E).withBoundary F).IsAdmissible := by
    apply FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.validOfSameNontrivialBoundary <;> assumption
  exact h2

section
variable (hinv : ComapIsoInvariance.{u}) (n : ℕ) (A : ℕ → PrincipalizationAssignment.{u}) (L : PrincipalizationAssignment.{u}) (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L) (hshift : IsBoundaryPositionInvariant (fun d => d ≤ n) A)
include hdiv hshift

theorem maxContact_isPullback_of_smooth_of_orderAt_le_mult
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : T.krullDimSucc ≤ n)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [Smooth h] (hq : h ≫ T.structMap = q)
    (E' : List Y.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
    (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible)
    (hP' : ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc ≤ n)
    (hO' : ∀ x : ↥((T.pullbackAlong Y q h).withBoundary E').scheme,
      orderAt ((T.pullbackAlong Y q h).withBoundary E').ideal x ≤ (T.mult : ℕ∞)) :
    IsPullbackBlowupSequence h
      (MaxContactFunctoriality.maxContactPrincipalization hinv A
        ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
      (MaxContactFunctoriality.maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
  have hcz : CharZero T.base := by
    cases hV
    assumption
  have hsm : Smooth T.structMap := by
    cases hV
    assumption
  have hflat : Flat h := inferInstance
  have hidS : ((T.pullbackAlong Y q h).withBoundary E').ideal = T.ideal.comap h :=
    (FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.withBoundary_ideal (T.pullbackAlong Y q h) E').trans
      (FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.pullbackAlong_ideal T Y q h)
  have hmultS : ((T.pullbackAlong Y q h).withBoundary E').mult = T.mult :=
    (FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.withBoundary_mult (T.pullbackAlong Y q h) E').trans
      (FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.pullbackAlong_mult T Y q h)
  have hordBound : ∀ x : ↥((T.pullbackAlong Y q h).withBoundary E').scheme,
      orderAt ((T.pullbackAlong Y q h).withBoundary E').ideal x
        ≤ ((((T.pullbackAlong Y q h).withBoundary E').mult : ℕ) : ℕ∞) := by
    intro x
    rw [hmultS]
    exact hO' x
  have hvan : FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.TrivialOnEmptyOrderLocus hinv (fun d => d ≤ n) A := by
    unfold FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.TrivialOnEmptyOrderLocus
    intros
    apply FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isPullback_of_orderAtLeastLocus_comap_eq_empty hinv
      (fun d => d ≤ n) A
    all_goals assumption
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  · have hempS : orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal
        ((T.pullbackAlong Y q h).withBoundary E').mult = ∅ := by
      rw [hidS, hmultS]
      exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.orderAtLeastLocus_comap_eq_empty T hV h hemp
    refine FunctorialResolution.EmbeddedResolution.isPullback_of_length_eq_zero_of_length_eq_zero h _ _ ?_ ?_
    · exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (fun d => d ≤ n) A
        ((T.pullbackAlong Y q h).withBoundary E') hV' hP' hordBound hempS
    · exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (fun d => d ≤ n) A
        T hV hP hO hemp
  · have hne : (orderAtLeastLocus T.ideal T.mult).Nonempty := Set.nonempty_iff_ne_empty.mpr hemp
    have hyp : FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n) T := ⟨hP, hO, hne, hV⟩
    by_cases hempS : orderAtLeastLocus (T.ideal.comap h) T.mult = ∅
    · have hempS' : orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal
          ((T.pullbackAlong Y q h).withBoundary E').mult = ∅ := by
        rw [hidS, hmultS]
        exact hempS
      have hz : (MaxContactFunctoriality.maxContactPrincipalization hinv A
          ((T.pullbackAlong Y q h).withBoundary E')).length = 0 :=
        FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (fun d => d ≤ n) A
          ((T.pullbackAlong Y q h).withBoundary E') hV' hP' hordBound hempS'
      exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isPullback_of_orderAtLeastLocus_comap_eq_empty hinv
        (fun d => d ≤ n) A T hyp Y h
        (MaxContactFunctoriality.maxContactPrincipalization hinv A
          ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups hz hempS
    · have hneS : (orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal
          ((T.pullbackAlong Y q h).withBoundary E').mult).Nonempty := by
        rw [hidS, hmultS]
        exact Set.nonempty_iff_ne_empty.mpr hempS
      have _hypS : FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n)
          ((T.pullbackAlong Y q h).withBoundary E') := ⟨hP', hordBound, hneS, hV'⟩
      have htrimv : (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).IsAdmissible := forall_isAdmissible_dropTrivialBoundary.{u} T hV
      have hpbv : (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E').IsAdmissible := by
        unfold FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback
        exact isAdmissible_withBoundary_of_sameNontrivialBoundary_consolidated493 (T.pullbackAlong Y q h) E'
          (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.removeUnitIdeals E') hV' (sameNontrivialBoundary_removeUnitIdeals_consolidated493 E')
      have hyppb : FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n)
          (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') :=
        ⟨hP', hordBound, hneS, hpbv⟩
      have hyptrim : FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n)
          (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) := hyp.of_dropTrivialBoundaryAdmissible forall_isAdmissible_dropTrivialBoundary.{u}
      have hcoverAdm : (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
          (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv).IsAdmissible :=
        FunctorialResolution.EmbeddedResolution.BoundarySeparationByMaxContact.isAdmissible_coverTriple maxContactCoverProperties (fun d => d ≤ n) _ hyptrim
      have hPv : (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
          (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv).IsAdmissible :=
        FunctorialResolution.EmbeddedResolution.BoundarySeparationByMaxContact.isAdmissible_coverTriple maxContactCoverProperties (fun d => d ≤ n) _ hyppb
      have hnC : IsNoetherian
          (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
            (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv).scheme := hcoverAdm.isNoetherian
      have hnP : IsNoetherian
          (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
            (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv).scheme :=
        hPv.isNoetherian
      have hnPt : IsNoetherian
          (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.chosenCoverData
            (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv).disjointUnion :=
        hPv.isNoetherian
      have hlnPt : IsLocallyNoetherian
          (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.chosenCoverData
            (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv).disjointUnion :=
        inferInstance
      have hqcStruct : QuasiCompact
          (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
            (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv).structMap := by
        constructor
        intro U hU hU2
        have hns : TopologicalSpace.NoetherianSpace
            ↥(FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
              (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv).scheme := inferInstance
        exact @TopologicalSpace.NoetherianSpace.isCompact _ _ hns _
      have hqcf : QuasiCompact
          (CategoryTheory.CategoryStruct.comp
            (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap
              (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv) h) := by
        constructor
        intro U hU hU2
        have hns : TopologicalSpace.NoetherianSpace
            ↥(FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
              (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv).scheme :=
          inferInstance
        exact @TopologicalSpace.NoetherianSpace.isCompact _ _ hns _
      have hqcSnd : QuasiCompact
          (CategoryTheory.Limits.pullback.snd
            (CategoryTheory.CategoryStruct.comp
              (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap
                (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv) h)
            (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv)) :=
        pullback_snd_of_isStableUnderBaseChange_consolidated493 (P := @AlgebraicGeometry.QuasiCompact.{u}) _ _
          hqcf
      have hetFst : Etale
          (CategoryTheory.Limits.pullback.fst
            (CategoryTheory.CategoryStruct.comp
              (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap
                (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv) h)
            (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv)) :=
        pullback_fst_of_isStableUnderBaseChange_consolidated493 (P := @AlgebraicGeometry.Etale.{u}) _ _
          (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.etale_coverMap_of_isAdmissible (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv)
      have hdimQ := FunctorialResolution.EmbeddedResolution.krullDimSucc_le_of_etale
        (CategoryTheory.Limits.pullback.fst
          (CategoryTheory.CategoryStruct.comp
            (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap
              (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv) h)
          (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv))
        hPv.topologicalKrullDim_lt_top
      have hdimTrim : (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E').krullDimSucc
          = (T.pullbackAlong Y q h).krullDimSucc := rfl
      have hdimfp : FunctorialResolution.EmbeddedResolution.krullDimSucc
          (CategoryTheory.Limits.pullback
            (CategoryTheory.CategoryStruct.comp
              (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap
                (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv) h)
            (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv))
          ≤ (T.pullbackAlong Y q h).krullDimSucc := by
        refine le_trans hdimQ ?_
        refine le_trans (FunctorialResolution.EmbeddedResolution.MaxContactOpenCover.krullDimSucc_coverTriple_scheme_le_dim _ hpbv) ?_
        exact le_of_eq hdimTrim
      exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.maxContactPrincipalization_isPullbackBlowupSequence_of_smooth
        hinv (fun d => d ≤ n) (fun _ _ hab hb => le_trans hab hb) A L hdiv hshift
        maxContactCoverProperties orderReductionHypotheses (isMaxContactInvariantBalancedTuned_of_tunedSheafProperties tunedSheafProperties.{u})
        maxContactHypersurfaceSmoothPullback.{u} (separateBoundary_pullback_of_smooth hinv (fun d => d ≤ n) A) hvan
        (coverSequenceProperties_of_isBoundaryDivisorReduction hinv n A L hdiv) (markingDescends hinv (fun d => d ≤ n) A)
        (coverFaithfullyFlat_consolidated493 (fun d => d ≤ n)) forall_isAdmissible_dropTrivialBoundary.{u} forall_isMarked_of_isMarked_dropTrivialBoundary.{u}
        T hV hP hO q h hq E' hE hV' hP' htrimv hpbv
        (MorphismProperty.comp_mem (@AlgebraicGeometry.QuasiCompact.{u}) _ _ hqcSnd hqcStruct)
        hdimfp

theorem descentProperties_of_isBoundaryDivisorReduction :
    MaxContactFunctoriality.DescentHypotheses hinv (fun d => d ≤ n) A L := by
  have hstar : MaxContactCoverProperties.{u} := maxContactCoverProperties
  have hCoverSeq : MaxContactFunctoriality.CoverSequenceProperties hinv (fun d => d ≤ n) A :=
    coverSequenceProperties_of_isBoundaryDivisorReduction hinv n A L hdiv
  have hmd : MaxContactFunctoriality.MarkingDescends hinv (fun d => d ≤ n) A :=
    markingDescends hinv (fun d => d ≤ n) A
  refine ⟨tunedSheafProperties.{u}.isMarked_tuned_iff, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro k hfk W' W p g hg hsurj N μ Mem Z hcert
    exact @FunctorialResolution.EmbeddedResolution.orderCertificate_of_comap_of_isLocalIsomorphism (fun K inst => @FunctorialResolution.EmbeddedResolution.openImmersionStability K inst)
      orderCertificateLocalToGlobal.{u} k hfk W W' p g hg hsurj N μ Mem Z hcert
  · intro T hV hP hO K hfK hcK f E' hE hV' hP' hO'
    exact @maxContact_baseChange_isPullbackBlowupSequence hinv n A L hdiv T hV hP hO K hfK hcK f E'
      hE hV' hP' hO'
  · intro T hV hP hO K hfK hcK f E' hE hV' hP' _hO'
    exact @isStrictPullbackBlowupSeq_maxContact_baseChange hinv n A L hdiv T hV hP hO K hfK hcK f
      E' hE hV' hP'
  · intro T h db D i hi
    exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isLocalIsomorphism_map_coverBlowupSequence hinv A T h db D i hi
  · intro T h db hd
    exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isLocallyNoetherian_schemeAt_coverBlowupSequence hinv A hstar T h db hd
  · intro T h db hd
    have hv : T.IsAdmissible := h.valid
    have hcz : CharZero T.base := by
      cases hv
      assumption
    have hsm : Smooth T.structMap := by
      cases hv
      assumption
    have hlft : LocallyOfFiniteType T.structMap := hv.locallyOfFiniteType
    have hsurj : AlgebraicGeometry.Surjective (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap T hv) :=
      FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.coverMap_surjective tunedSheafProperties.{u} T h
    have hoi : FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.IsLocalIsomorphism
        (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap T hv) :=
      FunctorialResolution.EmbeddedResolution.MaxContactOpenCover.isLocalIsomorphism_coverMap T hv
    have hmult : 1 ≤ FunctorialResolution.EmbeddedResolution.MaxContactCoverData.tunedMult T := FunctorialResolution.EmbeddedResolution.one_le_tuningExponent T.mult
    have hlev := FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isLocallyNoetherian_schemeAt_coverBlowupSequence hinv A hstar T h db hd
    exact FunctorialResolution.EmbeddedResolution.isMarked_balancedTunedIdeal_of_isStrictPullbackBlowupSeq hinv (fun d => d ≤ n) A T h hoi hmult db hd hlev.1 hlev.2
      (fun D i hi =>
        FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isLocalIsomorphism_map_coverBlowupSequence hinv A T h db D i hi)
  · intro T hV db I m hm
    exact isMarked_of_isMarked_dropTrivialBoundary T hV db I m hm
  · intro T hV hO s i hi x
    exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.orderAt_sequenceOfBlowups_ideal_le_mult hstar T hV hO s i hi x
  · intro T hV hP hO Y q g hsmg hq E' hE hV' hP' hO'
    exact @maxContact_isPullback_of_smooth_of_orderAt_le_mult hinv n A L hdiv hshift T hV hP hO Y q g hsmg
      hq E' hE hV' hP' hO'
  · intro T hV hP hO Y q g hsmg hsjg hq E' hE hV' hP' hO'
    have hpb := @maxContact_isPullback_of_smooth_of_orderAt_le_mult hinv n A L hdiv hshift T hV hP hO Y q g
      hsmg hq E' hE hV' hP' hO'
    refine @FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence.isStrictPullback_of_surjective _ _ _ hsjg _ _ hpb ?_
    intro i hi
    by_cases hemp : FunctorialResolution.EmbeddedResolution.orderAtLeastLocus T.ideal T.mult = ∅
    · exfalso
      have hlen : (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.maxContactPrincipalization hinv A T).toSequenceOfBlowups.length = 0 :=
        FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (fun d => d ≤ n) A T hV hP hO
          hemp
      omega
    · have hne : (FunctorialResolution.EmbeddedResolution.orderAtLeastLocus T.ideal T.mult).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hemp
      have hyp : FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n) T := ⟨hP, hO, hne, hV⟩
      obtain ⟨dd, hdd, heq⟩ :=
        FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.exists_isStrictPullback_cover_dropTrivialBoundary hCoverSeq hmd forall_isAdmissible_dropTrivialBoundary.{u}
          forall_isMarked_of_isMarked_dropTrivialBoundary.{u} T hyp
      rw [heq] at hi ⊢
      refine hdd.center_ne_top_of_forall_center_ne_top ?_ i hi
      intro l hl
      exact hCoverSeq.center_ne_top (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T)
        (hyp.of_dropTrivialBoundaryAdmissible forall_isAdmissible_dropTrivialBoundary.{u}) l hl
  · intro T h
    exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.coverMap_flat T h
  · intro T h
    exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.coverMap_surjective tunedSheafProperties.{u} T h
  · intro T hV Y q e hei hq J hJ ε hε
    exact @FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isAdmissible_and_dim_eq_withSchemeIdealBoundary_ker T hV Y q e hei hq J hJ ε hε
  · intro T hv hm
    exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.balancedTunedIdeal_eq_of_mult_eq_one T hv hm
  · exact forall_isAdmissible_dropTrivialBoundary.{u}
  · intro T hV _hbd Y q e hei _hq hD
    exact @isAdmissible_withBoundary_ker_of_isSmoothDivisor T hV Y e hei hD


end

theorem isOrderReduction_maxContact_of_isBoundaryPositionInvariant (hinv : ComapIsoInvariance.{u}) (n : ℕ)
    (A : ℕ → PrincipalizationAssignment.{u}) (L L' : PrincipalizationAssignment.{u})
    (hlow : IsMaxOrderReduction (fun d => d < n) L L')
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L)
    (hshift : IsBoundaryPositionInvariant (fun d => d ≤ n) A) :
    IsOrderReduction (fun d => d ≤ n) (MaxContactFunctoriality.maxContactPrincipalization hinv A) L :=
  FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isOrderReduction_maxContact_dim_le_of_descentHypotheses hinv n A L L' hlow hdiv
    (coverSequenceProperties_of_isBoundaryDivisorReduction hinv n A L hdiv)
    (descentProperties_of_isBoundaryDivisorReduction hinv n A L hdiv hshift)

theorem isOrderReduction_orderFamily_of_strictTransformIsBlowup
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) :
    ∀ (n : ℕ) (A : ℕ → PrincipalizationAssignment.{u}) (L L' : PrincipalizationAssignment.{u}),
      IsMaxOrderReduction (fun d => d < n) L L' →
      (∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L) →
      IsBoundaryPositionInvariant (fun d => d ≤ n) A →
      IsOrderReduction (fun d => d ≤ n) ((canonicalAlgorithmRules hres).orderFamily A) L := by
  intro n A L L' hlow hdiv hshift
  have h : IsOrderReduction (fun d => d ≤ n)
      (MaxContactFunctoriality.maxContactPrincipalization comapIsoInvariance.{u} A) L :=
    isOrderReduction_maxContact_of_isBoundaryPositionInvariant comapIsoInvariance.{u} n A L L' hlow hdiv hshift
  have heq : (canonicalAlgorithmRules hres).orderFamily A
      = MaxContactFunctoriality.maxContactPrincipalization comapIsoInvariance.{u} A := by
    funext T
    rfl
  rw [heq]
  exact h

end FunctorialResolution.EmbeddedResolution.OrderReductionProperties
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalRulesCorrect
section


namespace FunctorialResolution.EmbeddedResolution

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})

theorem isCorrect_canonicalAlgorithmRules_of_hypotheses
    (hdiv : DivisorReduction.DivisorReductionHypotheses hres)
    (hG : PrincipalizationGeometryHypotheses.{u}) :
    (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension where
  divisorSpec := isBoundaryDivisorReduction_divisorFamily_canonicalAlgorithmRules hres hdiv
  divisorShift := isBoundaryPositionInvariant_divisorFamily_canonicalAlgorithmRules hres hdiv
  maxOrderSpec := fun n A L hspec =>
    MaxOrderReduction.isMaxOrderReduction_canonicalAlgorithmRules hG hres n A L hspec
  orderSpec := OrderReductionProperties.isOrderReduction_orderFamily_of_strictTransformIsBlowup hres

theorem isCorrect_canonicalAlgorithmRules
    :
    (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension :=
  isCorrect_canonicalAlgorithmRules_of_hypotheses hres
    (divisorReductionHypotheses_canonicalAlgorithmRules hres)
    principalizationGeometryHypotheses.{u}


end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.PrincipalizationWithRadicalCenters
section


section
namespace FunctorialResolution.EmbeddedResolution

theorem canonicalAlgorithmRules_isCorrect :
    (canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme.{u}).ReducesInductivelyOnDimension :=
  isCorrect_canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme

noncomputable abbrev principalizationWithRadicalCenters : PrincipalizationAlgorithm.{u} :=
  canonicalPrincipalization strictTransformIsBlowupOfClosedSubscheme smoothSubschemeIdealIsRadical.{u}

theorem embeddedPrincipalizationDiscardedLocusIsOpen_of_detachedLocusIsOpen (A : PrincipalizationAlgorithm.{u}) (h : DetachedLocusIsOpenForEmbeddings.{u} A) :
    EmbeddedPrincipalizationDiscardedLocusIsOpen.{u} A affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth := by
  intro k _ _ Y pY _ _ _ _ i hi
  exact h k Y pY
    (affineSpaceEmbeddingDatum affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace
      affineSpaceIsSmooth k Y pY) i hi

theorem chartIsolationHypotheses_principalizationWithRadicalCenters :
    OpenImmersionRestriction.ChartIsolationHypotheses OpenImmersionRestriction.vanishingIdealAssignment.{u} principalizationWithRadicalCenters.{u} := by
  have h : OpenImmersionRestriction.reducedVanishingAssignment.{u} = OpenImmersionRestriction.vanishingIdealAssignment.{u} := by
    funext X T
    rw [OpenImmersionRestriction.vanishingIdealAssignment_apply]
    rfl
  have h2 := OpenImmersionRestriction.chartIsolationHypotheses_reducedVanishingAssignment principalizationWithRadicalCenters.{u}
  rwa [h] at h2

theorem detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters :
    DetachedLocusIsOpenForEmbeddings.{u} principalizationWithRadicalCenters.{u} :=
  OpenImmersionRestriction.detachedLocusIsOpenForEmbeddings_canonicalPrincipalization OpenImmersionRestriction.idealSheafGeometryHypotheses_vanishingIdealAssignment.{u}
    strictTransformIsBlowupOfClosedSubscheme.{u} canonicalAlgorithmRules_isCorrect smoothSubschemeIdealIsRadical.{u}
    chartIsolationHypotheses_principalizationWithRadicalCenters.{u}

theorem transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters :
    TransitionsAreBlowupsForEmbeddings principalizationWithRadicalCenters.{u} :=
  transitionsAreBlowupsForEmbeddings_of_detachedLocusIsOpen principalizationWithRadicalCenters.{u}
    detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters

theorem embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters :
    EmbeddedPrincipalizationYieldsBlowups principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth :=
  embeddedPrincipalizationYieldsBlowups_of_discardedLocusIsOpen principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
    nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
    (embeddedPrincipalizationDiscardedLocusIsOpen_of_detachedLocusIsOpen principalizationWithRadicalCenters.{u}
      detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters)
    (embeddedPrincipalizationAmbientIsNoetherian principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    strictTransformIsBlowupOfClosedSubscheme

theorem isFunctorialPrincipalization_principalizationWithRadicalCenters : IsFunctorialPrincipalization principalizationWithRadicalCenters.{u} :=
  isFunctorialPrincipalization_canonicalPrincipalization strictTransformIsBlowupOfClosedSubscheme canonicalAlgorithmRules_isCorrect
    smoothSubschemeIdealIsRadical
    (commutesWithClosedImmersion_of_isCorrect (canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme) canonicalAlgorithmRules_isCorrect)

noncomputable def canonicalAffineResolutionRule : AffineResolutionRule.{u} :=
  affineResolutionRuleOfPrincipalization principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
    nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineCentersOverSingularLocus
section

open TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private theorem smooth_opens_ι_consolidated497 {X : Scheme.{u}} (U : X.Opens) :
    Smooth U.ι := by
  rw [← AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff]
  refine le_antisymm le_top ?_
  intro x _
  exact (RingHom.FormallySmooth.of_bijective (ConcreteCategory.bijective_of_isIso _) :
    (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.stalkMap U.ι x)).FormallySmooth)

section
variable {X Z : Scheme.{u}} (f : X ⟶ Z) [AlgebraicGeometry.LocallyOfFinitePresentation f]

private theorem smooth_ι_comp_of_le_smoothLocus_consolidated497 (U : X.Opens)
    (hU : U ≤ AlgebraicGeometry.Scheme.Hom.smoothLocus f) :
    Smooth (U.ι ≫ f) := by
  rw [← AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff]
  refine le_antisymm le_top ?_
  intro x _
  have hx : (CommRingCat.Hom.hom
      (AlgebraicGeometry.Scheme.Hom.stalkMap f (U.ι x))).FormallySmooth := hU x.2
  have hg : (CommRingCat.Hom.hom
      (AlgebraicGeometry.Scheme.Hom.stalkMap U.ι x)).FormallySmooth :=
    RingHom.FormallySmooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have heq : (CommRingCat.Hom.hom
        (AlgebraicGeometry.Scheme.Hom.stalkMap (U.ι ≫ f) x)).FormallySmooth =
      (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.stalkMap f (U.ι x) ≫
        AlgebraicGeometry.Scheme.Hom.stalkMap U.ι x)).FormallySmooth :=
    congrArg (fun φ => (CommRingCat.Hom.hom φ).FormallySmooth)
      (AlgebraicGeometry.Scheme.Hom.stalkMap_comp U.ι f x)
  exact Eq.mpr heq (RingHom.FormallySmooth.comp hx hg)

private theorem mem_smoothLocusComplement_iff_consolidated497 (x : ↥X) :
    x ∈ (↑(smoothLocusComplement f) : Set ↥X) ↔
      x ∉ (↑(AlgebraicGeometry.Scheme.Hom.smoothLocus f) : Set ↥X) :=
  Iff.rfl


end

private theorem ker_morphismRestrict_consolidated497 {X W : Scheme.{u}} (f : X ⟶ W)
    [IsClosedImmersion f] (V : W.Opens) :
    AlgebraicGeometry.Scheme.Hom.ker (f ∣_ V) =
      (AlgebraicGeometry.Scheme.Hom.ker f).comap V.ι :=
  OpenImmersionRestriction.ker_eq_comap_ker_of_isPullback_isOpenImmersion f V.ι (f ∣_ V) ((f ⁻¹ᵁ V).ι)
    (AlgebraicGeometry.isPullback_morphismRestrict f V).flip

private theorem inducedBlowupsWithoutIso_eq_withoutIsoBlowups_consolidated497 {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType pY] (S : EmbeddedBlowupSequence k Y pY)
    (h : S.TransitionsAreBlowups) : S.inducedBlowupsWithoutIso h = (S.inducedBlowups h).withoutIsoBlowups := rfl

private noncomputable def restrictEmbeddingDatumBasicOpen {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY)
    (hsnc : NilIsStrictNormalCrossingsOfSmooth.{u}) (r : Γ(D.ambient, ⊤)) :
    EmbeddingDatum k (D.emb ⁻¹ᵁ D.ambient.basicOpen r).toScheme
      ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) where
  ambient := (D.ambient.basicOpen r).toScheme
  ambientStruct := (D.ambient.basicOpen r).ι ≫ D.ambientStruct
  emb := D.emb ∣_ D.ambient.basicOpen r
  isAffine_ambient := (AlgebraicGeometry.isAffineOpen_top D.ambient).basicOpen r
  smooth_ambientStruct := by
    have := D.smooth_ambientStruct
    have := smooth_opens_ι_consolidated497 (D.ambient.basicOpen r)
    infer_instance
  locallyOfFiniteType_ambientStruct := inferInstance
  quasiCompact_ambientStruct := by
    have : IsAffine (D.ambient.basicOpen r).toScheme :=
      (AlgebraicGeometry.isAffineOpen_top D.ambient).basicOpen r
    exact inferInstance
  isClosedImmersion_emb := inferInstance
  nonzeroOnComponents_ker := by
    rw [ker_morphismRestrict_consolidated497]
    exact D.nonzeroOnComponents_ker.comap_of_isOpenImmersion _
  comp_eq := by
    rw [← Category.assoc, AlgebraicGeometry.morphismRestrict_ι, Category.assoc, D.comp_eq]
  sncEmpty := by
    have := D.smooth_ambientStruct
    have := smooth_opens_ι_consolidated497 (D.ambient.basicOpen r)
    exact hsnc k _ _ inferInstance

private theorem isPullbackSeq_of_smooth_consolidated497
    (A : PrincipalizationAlgorithm.{u}) (hA : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (k : Type u) [Field k] [CharZero k] (Y Y' : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) (p' : Y' ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [QuasiCompact p]
    [IsReduced Y] [IsAffine Y]
    [LocallyOfFiniteType p'] [QuasiCompact p']
    [IsReduced Y'] [IsAffine Y']
    (D : EmbeddingDatum k Y p) (D' : EmbeddingDatum k Y' p')
    (φ : D'.ambient ⟶ D.ambient) (hsmφ : Smooth φ) (ψ : Y' ⟶ Y)
    (hφ : φ ≫ D.ambientStruct = D'.ambientStruct)
    (hsq : IsPullback D'.emb ψ φ D.emb) :
    IsPullbackBlowupSequence ψ (embeddedResolutionRuleOfPrincipalization A hw k Y' p' D')
      (embeddedResolutionRuleOfPrincipalization A hw k Y p D) := by
  have := hsmφ
  exact embeddedResolutionRule_isPullbackBlowupSequence_of_smooth A hA hw k Y Y' p p' D D' φ ψ hφ hsq

private theorem centersLieOver_of_withoutIsoBlowups_consolidated497 {X : Scheme.{u}} (s : SequenceOfBlowups X) (Z : Set ↥X)
    (h : s.withoutIsoBlowups.CentersLieOver Z) : s.CentersLieOver Z := by
  intro i hi x hx
  have hne : s.center i ≠ ⊤ := by
    intro h0
    have h1 : (s.center i).support = ⊥ :=
      (AlgebraicGeometry.Scheme.IdealSheafData.support_eq_bot_iff _).mpr h0
    have h2 : x ∈ ((⊥ : TopologicalSpace.Closeds ↥(s.schemeAt i)) : Set ↥(s.schemeAt i)) := by
      rw [← h1]; exact hx
    exact h2
  obtain ⟨j, hj, hji⟩ := s.exists_nontrivialIndex_eq_of_center_ne_top hi hne
  subst hji
  have h1 := h j (by rw [SequenceOfBlowups.withoutIsoBlowups_length]; exact hj) x
    (by rw [SequenceOfBlowups.withoutIsoBlowups_center]; exact hx)
  rwa [SequenceOfBlowups.withoutIsoBlowups_projectionToBase] at h1

section
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY]

private theorem blowupSequence_centersLieOver_congr_consolidated497 {S T : EmbeddedBlowupSequence k Y pY} (e : S = T)
    (hS : S.TransitionsAreBlowups) (hT : T.TransitionsAreBlowups) (Z : Set ↥Y)
    (h : (S.inducedBlowups hS).CentersLieOver Z) : (T.inducedBlowups hT).CentersLieOver Z := by
  subst e
  exact h

private theorem quasiCompact_of_embeddingDatum_consolidated497 (D : EmbeddingDatum k Y pY) :
    QuasiCompact pY := by
  rw [← D.comp_eq]
  infer_instance


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension) (hrad : SmoothSubschemeIdealIsRadical.{u}) {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y] [IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY) (hsm : Smooth pY)
include hB hsm

theorem centerOffDetached_eq_top_of_smooth
    (t : ℕ)
    (ht : t < (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length) :
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).centerOffDetached t = ⊤ := by
  have : QuasiCompact pY := quasiCompact_of_embeddingDatum_consolidated497 D
  have hiso := OpenImmersionRestriction.detachedLocusIsOpen_toEmbeddedBlowupSequence OpenImmersionRestriction.idealSheafGeometryHypotheses_vanishingIdealAssignment hres hB hrad
    (OpenImmersionRestriction.chartIsolationHypotheses_reducedVanishingAssignment (canonicalPrincipalization hres hrad)) k Y pY D
  have hnoe : NoetherianSpace
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t) :=
    EmbeddedBlowupSequence.noetherianSpace_strictTransform_of_isNoetherian _
      (EmbeddedBlowupSequence.isNoetherian_schemeAt (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad))) t
      (le_of_lt ht)
  have hopen : IsOpen ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedLocus t) :=
    hiso t ht
  apply (Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).mpr
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  have h1 := EmbeddedBlowupSequence.support_centerOffDetached_subset_preimage
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)) t hy
  have h2 : y ∈ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedLocus t :=
    OpenImmersionRestriction.mem_detachedLocus_of_mem_support_ambientCenter hres hB hrad D hsm t ht y h1
  have h3 := EmbeddedBlowupSequence.support_centerOffDetached_subset_detachedClosureCompl
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)) t hnoe hopen hy
  rw [EmbeddedBlowupSequence.detachedClosureCompl_coe, EmbeddedBlowupSequence.detachedClosure_coe] at h3
  exact h3 h2

theorem toEmbeddedBlowupSequence_center_eq_top_of_smooth
    (hbl : (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).TransitionsAreBlowups) (t : ℕ)
    (ht : t < (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length) :
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).inducedBlowups hbl).center t = ⊤ := by
  rw [EmbeddedBlowupSequence.inducedBlowups_center, EmbeddedBlowupSequence.totalCenter_eq,
    centerOffDetached_eq_top_of_smooth hres hB hrad D hsm t ht]
  exact AlgebraicGeometry.Scheme.ker_eq_top_of_isEmpty ..

private theorem withoutIsoBlowups_length_eq_zero_of_smooth_consolidated497
    (hbl : (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).TransitionsAreBlowups) :
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).inducedBlowups hbl).lengthWithoutIsoBlowups = 0 := by
  by_contra hne
  have h0 : 0 < ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).inducedBlowups hbl).lengthWithoutIsoBlowups :=
    Nat.pos_of_ne_zero hne
  have h1 := SequenceOfBlowups.nontrivialIndex_lt_length _ h0
  have h2 := SequenceOfBlowups.center_nontrivialIndex_ne_top _ h0
  rw [EmbeddedBlowupSequence.inducedBlowups_length] at h1
  exact h2 (toEmbeddedBlowupSequence_center_eq_top_of_smooth hres hB hrad D hsm hbl _ h1)


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension) (hrad : SmoothSubschemeIdealIsRadical.{u}) (hA : IsFunctorialPrincipalization (canonicalPrincipalization hres hrad)) (hw : TransitionsAreBlowupsForEmbeddings (canonicalPrincipalization hres hrad)) (hsnc : NilIsStrictNormalCrossingsOfSmooth.{u}) {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [IsAffine Y] [IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType pY] [QuasiCompact pY] [AlgebraicGeometry.LocallyOfFinitePresentation pY] (D : EmbeddingDatum k Y pY)
include hB hA hw hsnc

private theorem centersLieOver_embeddedResolutionRuleOfPrincipalization_consolidated497
    :
    (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).CentersLieOver
      (↑(smoothLocusComplement pY) : Set ↥Y) := by
  intro i hi x hx
  by_contra hns
  have hy : (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x ∈
      (↑(AlgebraicGeometry.Scheme.Hom.smoothLocus pY) : Set ↥Y) := by
    by_contra h
    exact hns ((mem_smoothLocusComplement_iff_consolidated497 pY _).mpr h)
  obtain ⟨W, hWopen, hW⟩ :=
    ((AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding D.emb).isInducing).isOpen_iff.mp
      (AlgebraicGeometry.Scheme.Hom.smoothLocus pY).isOpen
  have hWy :
      D.emb
        ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x)
        ∈ W := by
    have h2 :
        (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x ∈
          ⇑D.emb ⁻¹' W := by
      rw [hW]; exact hy
    exact h2
  obtain ⟨U', hU'mem, hxU', hU'le⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.isBasis_basicOpen D.ambient)
      (show D.emb
          ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x)
          ∈ (⟨W, hWopen⟩ : D.ambient.Opens) from hWy)
  obtain ⟨r, hr⟩ := hU'mem
  have hyV : (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x ∈
      D.emb ⁻¹ᵁ D.ambient.basicOpen r := by
    have h3 :
        D.emb
          ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x)
          ∈ D.ambient.basicOpen r := by
      rw [hr]; exact hxU'
    exact h3
  have hVle : (D.emb ⁻¹ᵁ D.ambient.basicOpen r) ≤
      AlgebraicGeometry.Scheme.Hom.smoothLocus pY := by
    intro z hz
    have h3 : D.emb z ∈ D.ambient.basicOpen r := hz
    rw [hr] at h3
    have h5 : z ∈ ⇑D.emb ⁻¹' W := hU'le h3
    rw [hW] at h5
    exact h5
  have hVaff : IsAffine (D.emb ⁻¹ᵁ D.ambient.basicOpen r).toScheme :=
    ((AlgebraicGeometry.isAffineOpen_top D.ambient).basicOpen r).preimage D.emb
  have hsmV : Smooth ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) :=
    smooth_ι_comp_of_le_smoothLocus_consolidated497 pY _ hVle
  have hqcV : QuasiCompact ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) :=
    inferInstance
  have hlen0 : (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k
      (D.emb ⁻¹ᵁ D.ambient.basicOpen r).toScheme
      ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) (restrictEmbeddingDatumBasicOpen D hsnc r)).length = 0 := by
    rw [embeddedResolutionRuleOfPrincipalization_apply, inducedBlowupsWithoutIso_eq_withoutIsoBlowups_consolidated497, SequenceOfBlowups.withoutIsoBlowups_length]
    exact withoutIsoBlowups_length_eq_zero_of_smooth_consolidated497 hres hB hrad (restrictEmbeddingDatumBasicOpen D hsnc r) hsmV _
  have hps := isPullbackSeq_of_smooth_consolidated497 (canonicalPrincipalization hres hrad) hA hw k Y
      (D.emb ⁻¹ᵁ D.ambient.basicOpen r).toScheme pY
      ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) D (restrictEmbeddingDatumBasicOpen D hsnc r)
      (D.ambient.basicOpen r).ι (smooth_opens_ι_consolidated497 (D.ambient.basicOpen r))
      (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι rfl
      (AlgebraicGeometry.isPullback_morphismRestrict D.emb (D.ambient.basicOpen r))
  obtain ⟨ρ, e, h1, h2, h3, h4, h5, h6, h7⟩ := hps
  have hmemrange :
      (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x ∈
        Set.range ⇑(D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    exact hyV
  obtain ⟨x', hx'eq⟩ := hmemrange
  obtain ⟨z, hz1, hz2⟩ :=
    AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
      (f := (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι)
      (g := (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i)
      x' x hx'eq
  have hex : ∃ w, w ∈
      (((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).center i).comap
        (Limits.pullback.snd (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι
          ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase
            i))).support := by
    refine ⟨z, ?_⟩
    have hmem : z ∈
        (↑((((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).center
          i).comap (Limits.pullback.snd (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι
            ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase
              i))).support) : Set _) := by
      rw [FunctorialResolution.EmbeddedResolution.support_comap]
      show (Limits.pullback.snd (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι
          ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i)) z
          ∈ (↑((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).center
                i).support : Set _)
      rw [hz2]
      exact hx
    exact hmem
  obtain ⟨j, hj, -⟩ := (h4 i hi).mp hex
  rw [hlen0] at hj
  exact absurd hj (Nat.not_lt_zero j)

theorem toEmbeddedBlowupSequence_centersLieOver_smoothLocusComplement
    (hbl : (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).TransitionsAreBlowups) :
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).inducedBlowups hbl).CentersLieOver
      (↑(smoothLocusComplement pY) : Set ↥Y) := by
  apply centersLieOver_of_withoutIsoBlowups_consolidated497
  have h := centersLieOver_embeddedResolutionRuleOfPrincipalization_consolidated497 hres hB hrad hA hw hsnc D
  rw [embeddedResolutionRuleOfPrincipalization_apply] at h
  exact h


end

theorem affineCentersLieOverSingularLocus_principalizationWithRadicalCenters :
    AffineCentersLieOverSingularLocus.{u} principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters := by
  intro k _ _ Y pY _ _ _ _
  unfold FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.InducedCentersLieOverSingularLocus
  have hbl0 :
      ((affineSpaceEmbeddingDatum affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
          k Y pY).toEmbeddedBlowupSequence principalizationWithRadicalCenters).TransitionsAreBlowups :=
    transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters k Y pY _
  have key := toEmbeddedBlowupSequence_centersLieOver_smoothLocusComplement strictTransformIsBlowupOfClosedSubscheme
    canonicalAlgorithmRules_isCorrect smoothSubschemeIdealIsRadical
    (isFunctorialPrincipalization_canonicalPrincipalization strictTransformIsBlowupOfClosedSubscheme canonicalAlgorithmRules_isCorrect
      smoothSubschemeIdealIsRadical
      (commutesWithClosedImmersion_of_isCorrect (canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme) canonicalAlgorithmRules_isCorrect))
    transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters nilIsStrictNormalCrossingsOfSmooth
    (affineSpaceEmbeddingDatum affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
      k Y pY) hbl0
  rw [← AffineSpacePrincipalizationData.embeddedInducedBlowups_eq]
  exact blowupSequence_centersLieOver_congr_consolidated497
    (affineSpaceEmbeddingDatum_toEmbeddedBlowupSequence principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth k Y pY) hbl0 _ _ key

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.HironakaTheorem
section


namespace FunctorialResolution.EmbeddedResolution

theorem isStrongResolution_canonicalAffineResolutionRule (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [IsAffine Y]
    [IsReduced Y] [LocallyOfFiniteType p]
    [QuasiCompact p] :
    IsStrongResolution k Y p (canonicalAffineResolutionRule k Y p) := by
  have hIso : EmbeddedPrincipalizationDiscardedLocusIsOpen principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth :=
    embeddedPrincipalizationDiscardedLocusIsOpen_of_detachedLocusIsOpen principalizationWithRadicalCenters.{u}
      detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters
  have hsmooth : AffineDetachedSmooth principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth :=
    affineDetachedSmooth principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
  have hCen : AffineCentersLieOverSingularLocus principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters :=
    affineCentersLieOverSingularLocus_principalizationWithRadicalCenters
  show IsStrongResolution k Y p
    (affineResolutionRuleOfPrincipalization principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters k Y p)
  exact isStrongResolution_blowupSequenceWithoutIsos_ofAffine principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
    nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters
    (affineStrictTransformEmptyAtLast_of_isFunctorialPrincipalization principalizationWithRadicalCenters.{u}
      isFunctorialPrincipalization_principalizationWithRadicalCenters affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace
      affineSpaceIsSmooth)
    hsmooth
    (affineSmoothLocusPreimageDenseInDetached principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    hCen
    (affineDetachedClopenInCenter principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineDetachedComponentsNotInBoundary principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineDetachedSingularPreimageEqBoundary_of_centersLieOverSing principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth hIso hsmooth
      embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters hCen)
    (affineCentersHaveStrictNormalCrossingsWithBoundary principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineAllLevelsSmooth principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineBoundaryInStrictNormalCrossingPosition principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    strictNormalCrossingsRestrictToClopen Blowup.blowupIsProper k Y p

theorem strongResolutionOfSingularitiesCharZero :
    StrongResolutionOfSingularitiesCharZero.{u} :=
  strongResolutionOfSingularitiesCharZero_of_principalizationAlgorithm principalizationWithRadicalCenters.{u}
    affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
    isFunctorialPrincipalization_principalizationWithRadicalCenters
    transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters
    embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters
    closedEmbeddingsRelatedByAutomorphism
    isStrongResolution_canonicalAffineResolutionRule

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.HasSimpleNormalCrossingsOfInStrictNormalCrossing
section
open CategoryTheory.Limits


namespace FunctorialResolution

theorem functorialResolutionCharZero : FunctorialResolutionCharZero.{u} := by
  obtain ⟨R, h1, h2, h3⟩ := EmbeddedResolution.strongResolutionOfSingularitiesCharZero.{u}
  exact ⟨fun k _ _ X f _ _ _ =>
    ⟨(R k X f).length, (R k X f).tower, (R k X f).isoZero, (R k X f).center, (R k X f).isBlowup⟩, h1, h2, h3⟩

end FunctorialResolution
end
end
