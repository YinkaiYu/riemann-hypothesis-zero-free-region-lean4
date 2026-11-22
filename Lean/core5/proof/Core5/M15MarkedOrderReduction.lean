import Mathlib
import Core5.M14OrderInduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicGeometry
universe u
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderPullbackInvariance
section

open CategoryTheory.Limits

section

def OrderAtPullbackInvariant (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}} (g : Y ⟶ T.scheme) : Prop :=
  ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base))
    (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
    (MarkedIdealWithBoundary.mk T.base B pB IB T.mult EB).IsAdmissible →
    b ≫ T.structMap = pB →
    ∀ (Q : Scheme.{u}) (q : Q ⟶ B) (p : Q ⟶ Y), IsPullback q p b g →
    ∀ (A : B.IdealSheafData) (y : ↥Q),
      orderAt (A.comap q) y = orderAt A (q.base y)

theorem orderAtPullbackInvariant_of_smooth (T : MarkedIdealWithBoundary.{u}) (_hT : T.IsAdmissible)
    {Y : Scheme.{u}} (g : Y ⟶ T.scheme) [Smooth g] :
    OrderAtPullbackInvariant T g := by
  intro B b pB IB EB hB hcomm Q q p hpb A y
  have : CharZero T.base := hB.charZero
  have : Smooth pB := hB.smooth
  have : Smooth q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Smooth) hpb.flip inferInstance
  exact orderAt_comap T.base pB q A y

theorem orderAtPullbackInvariant_baseChange_field (hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (_hT : T.IsAdmissible) (L : Type u) [Field L] [CharZero L] (f : T.base →+* L) :
    OrderAtPullbackInvariant T (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) := by
  intro B b pB IB EB hB hcomm Q q p hpb A y
  have hbig : IsPullback q (p ≫ pullback.snd T.structMap (specMapOfFieldHom T.base L f)) pB
      (specMapOfFieldHom T.base L f) := by
    rw [← hcomm]
    exact hpb.paste_vert (IsPullback.of_hasPullback T.structMap (specMapOfFieldHom T.base L f))
  have he : hbig.isoPullback.hom ≫ pullback.fst pB (specMapOfFieldHom T.base L f) = q :=
    hbig.isoPullback_hom_fst
  have : IsOpenImmersion hbig.isoPullback.hom := inferInstance
  have hkey := hG.orderAt_baseChange (MarkedIdealWithBoundary.mk T.base B pB IB T.mult EB) hB L f A
      (hbig.isoPullback.hom.base y)
  have hq : (pullback.fst pB (specMapOfFieldHom T.base L f)).base (hbig.isoPullback.hom.base y)
      = q.base y := congrArg (fun m : Q ⟶ B => m.base y) he
  calc orderAt (A.comap q) y
      = orderAt (A.comap (hbig.isoPullback.hom ≫
          pullback.fst pB (specMapOfFieldHom T.base L f))) y := by
        rw [he]
    _ = orderAt ((A.comap (pullback.fst pB (specMapOfFieldHom T.base L f))).comap
          hbig.isoPullback.hom) y := by
        rw [Scheme.IdealSheafData.comap_comp]
    _ = orderAt (A.comap (pullback.fst pB (specMapOfFieldHom T.base L f)))
          (hbig.isoPullback.hom.base y) :=
        orderAt_comap_of_isOpenImmersion _ _ y
    _ = orderAt A ((pullback.fst pB (specMapOfFieldHom T.base L f)).base
          (hbig.isoPullback.hom.base y)) := hkey
    _ = orderAt A (q.base y) := by rw [hq]


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MapToEarlierScheme
section

open CategoryTheory.Limits Opposite

section

section
variable {X : Scheme.{u}}

private theorem sameNontrivialBoundary_append_top_consolidated420 (L : List X.IdealSheafData) :
    MarkedIdealWithBoundary.SameNontrivialBoundary (L ++ [⊤]) L := by
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff]
  induction L with
  | nil => simp [MarkedIdealWithBoundary.nontrivialPart]
  | cons D t ih =>
      simp only [MarkedIdealWithBoundary.nontrivialPart, List.cons_append, List.filter_cons] at ih ⊢
      rw [ih]

private theorem sameNontrivialBoundary_of_eq_consolidated420 {A B C : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary A B) (e : C = B) : MarkedIdealWithBoundary.SameNontrivialBoundary A C := by
  subst e
  exact h

private theorem top_pow_mul_consolidated420 (J : X.IdealSheafData) (m : ℕ) :
    (⊤ : X.IdealSheafData) ^ m * J = J := by
  have e : (1 : X.IdealSheafData) = ⊤ := rfl
  rw [← e, one_pow, one_mul]


end

section
variable {F : ℕ → Scheme.{u}}

private theorem comap_comp_eqToHom_consolidated420 (G : ∀ n, (F n).IdealSheafData)
    {a b : ℕ} (h : a = b) {W : Scheme.{u}} (f : W ⟶ F a) :
    (G b).comap (f ≫ eqToHom (congrArg F h)) = (G a).comap f := by
  cases h
  have e : (eqToHom (congrArg F (rfl : a = a)) : F a ⟶ F a) = 𝟙 (F a) := rfl
  rw [e, Category.comp_id]

private theorem map_comap_comp_eqToHom_consolidated420 (G : ∀ n, List (F n).IdealSheafData)
    {a b : ℕ} (h : a = b) {W : Scheme.{u}} (f : W ⟶ F a) :
    (G b).map (fun D => D.comap (f ≫ eqToHom (congrArg F h)))
      = (G a).map (fun D => D.comap f) := by
  cases h
  have e : (eqToHom (congrArg F (rfl : a = a)) : F a ⟶ F a) = 𝟙 (F a) := rfl
  rw [e]
  simp


end

private theorem comap_ideal_boundary_succ_of_comap_center_eq_top_consolidated420 {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (n : ℕ) (hn : n < s.length)
    {W : Scheme.{u}} (f : W ⟶ s.obj (n + 1))
    (hnoe : IsNoetherian (s.obj (n + 1)))
    (hf : (s.center n).comap (f ≫ s.map n) = ⊤) :
    (s.ideal n).comap (f ≫ s.map n) = (s.ideal (n + 1)).comap f ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary ((s.boundary (n + 1)).map (fun D => D.comap f))
        ((s.boundary n).map (fun D => D.comap (f ≫ s.map n))) := by
  have := hnoe
  have he : ((s.center n).comap (s.map n)).comap f = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_comp]
    exact hf
  have hST : ∀ D : (s.obj n).IdealSheafData,
      (Blowup.strictTransform (s.map n) (s.center n) D).comap f = D.comap (f ≫ s.map n) := by
    intro D
    rw [strictTransform_comap_of_comap_center_eq_top (s.map n) (s.center n) D f he,
      ← Scheme.IdealSheafData.comap_comp]
  constructor
  · have h1 := s.ideal_succ n hn
    simp only [Blowup.exceptionalIdeal_eq_comap] at h1
    have h2 := congrArg (fun J : (s.obj (n + 1)).IdealSheafData => J.comap f) h1
    rw [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow, he,
      top_pow_mul_consolidated420] at h2
    simpa [Scheme.IdealSheafData.comap_comp] using h2.symm
  · have hfun : ((fun D : (s.obj (n + 1)).IdealSheafData => D.comap f) ∘
        Blowup.strictTransform (s.map n) (s.center n))
        = fun D => D.comap (f ≫ s.map n) := by
      funext D
      exact hST D
    rw [s.boundary_succ n hn, List.map_append, List.map_map, List.map_cons, List.map_nil,
      Blowup.exceptionalIdeal_eq_comap, he, hfun]
    exact sameNontrivialBoundary_append_top_consolidated420 _

namespace SequenceOfBlowupsPullback

variable {X X' : Scheme.{u}} {φ : X' ⟶ X}

def mapToEarlierScheme {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s)
    (j : ℕ) (hj : j ≤ s'.length) (i : ℕ) (hi : i ≤ c.idx j) : s'.schemeAt j ⟶ s.schemeAt i :=
  c.map j hj ≫ s.transitionMap hi

section
variable {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s) (j : ℕ) (hj : j ≤ s'.length)

theorem mapToEarlierScheme_eq_map_comp_transitionMap (i : ℕ) (hi : i ≤ c.idx j) :
    c.mapToEarlierScheme j hj i hi = c.map j hj ≫ s.transitionMap hi := rfl

theorem mapToEarlierScheme_index :
    c.mapToEarlierScheme j hj (c.idx j) le_rfl = c.map j hj := by
  rw [mapToEarlierScheme_eq_map_comp_transitionMap, SequenceOfBlowups.transitionMap_self_eq_id, Category.comp_id]

theorem mapToEarlierScheme_eq_comp_blowupMorphism (i : ℕ) (hi : i < c.idx j) :
    c.mapToEarlierScheme j hj i (le_of_lt hi) = c.mapToEarlierScheme j hj (i + 1) hi ≫ s.transitionMapSucc i := by
  simp only [mapToEarlierScheme_eq_map_comp_transitionMap, SequenceOfBlowups.blowupMorphism_eq_transitionMap, Category.assoc, SequenceOfBlowups.transitionMap_trans]

theorem mapToEarlierScheme_comp_projectionToBase (i : ℕ) (hi : i ≤ c.idx j) :
    c.mapToEarlierScheme j hj i hi ≫ s.projectionToBase i = s'.projectionToBase j ≫ φ := by
  rw [mapToEarlierScheme_eq_map_comp_transitionMap, Category.assoc, SequenceOfBlowups.transitionMap_comp_projectionToBase]
  exact (c.isPullback j hj).w


end

section
variable {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s)

private theorem index_mono_consolidated420 :
    ∀ b : ℕ, b ≤ s'.length → ∀ a : ℕ, a ≤ b → c.idx a ≤ c.idx b := by
  intro b
  induction b with
  | zero =>
      intro _ a ha
      rw [Nat.le_zero.1 ha]
  | succ n ih =>
      intro hb a ha
      rcases Nat.lt_or_ge a (n + 1) with h | h
      · exact le_trans (ih (Nat.le_of_succ_le hb) a (Nat.lt_succ_iff.1 h))
          (le_of_lt (c.idx_strictMono n hb))
      · have hae : a = n + 1 := le_antisymm ha h
        subst hae
        exact le_rfl

theorem index_le_length (j : ℕ) (hj : j ≤ s'.length) : c.idx j ≤ s.length := by
  rcases Nat.lt_or_ge j s'.length with h | h
  · exact le_of_lt (c.idx_lt j h)
  · have hje : j = s'.length := le_antisymm hj h
    subst hje
    exact le_of_eq c.idx_length

theorem comap_center_mapToEarlierScheme_eq_top_of_unmatched (j : ℕ) (hj : j ≤ s'.length) (i : ℕ) (hi : i < c.idx j)
    (hmiss : ∀ j' : ℕ, j' < s'.length → c.idx j' ≠ i) :
    (s.center i).comap (c.mapToEarlierScheme j hj i (le_of_lt hi)) = ⊤ := by
  have hilt : i < s.length := lt_of_lt_of_le hi (c.index_le_length j hj)
  have hw : c.mapToEarlierScheme j hj i (le_of_lt hi) ≫ s.projectionToBase i = s'.projectionToBase j ≫ φ :=
    c.mapToEarlierScheme_comp_projectionToBase j hj i (le_of_lt hi)
  rw [Scheme.IdealSheafData.eq_top_iff_support_eq_empty]
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  rw [Scheme.IdealSheafData.support_comap] at hy
  refine c.omitted i hilt hmiss _ hy ((s'.projectionToBase j).base y) ?_
  have hb : (c.mapToEarlierScheme j hj i (le_of_lt hi) ≫ s.projectionToBase i).base y
      = (s'.projectionToBase j ≫ φ).base y := by rw [hw]
  simpa using hb.symm

theorem index_ne_of_index_lt_of_lt_index_succ (j : ℕ) (hj : j + 1 ≤ s'.length) (i : ℕ)
    (hlo : c.idx j < i) (hhi : i < c.idx (j + 1)) :
    ∀ j' : ℕ, j' < s'.length → c.idx j' ≠ i := by
  intro j' hj' hEq
  rcases Nat.lt_or_ge j' (j + 1) with h | h
  · have hm := index_mono_consolidated420 c j (Nat.le_of_succ_le hj) j' (Nat.lt_succ_iff.1 h)
    omega
  · have hm := index_mono_consolidated420 c j' (le_of_lt hj') (j + 1) h
    omega

theorem index_ne_of_lt_index_zero (i : ℕ) (hi : i < c.idx 0) :
    ∀ j' : ℕ, j' < s'.length → c.idx j' ≠ i := by
  intro j' hj' hEq
  have hm := index_mono_consolidated420 c j' (le_of_lt hj') 0 (Nat.zero_le _)
  omega

theorem flat_map [Flat φ] (j : ℕ) (hj : j ≤ s'.length) :
    Flat (c.map j hj) := by
  have h : MorphismProperty.IsStableUnderBaseChange (@Flat) := inferInstance
  exact h.of_isPullback (c.isPullback j hj).flip inferInstance

theorem isPullback_blowupMorphism [Flat φ] (j : ℕ) (hj : j < s'.length) :
    IsPullback (c.mapToEarlierScheme (j + 1) hj (c.idx j + 1) (c.idx_strictMono j hj))
      (s'.transitionMapSucc j) (s.transitionMapSucc (c.idx j)) (c.map j (le_of_lt hj)) := by
  have hidxlt : c.idx j < s.length := c.idx_lt j hj
  have hbl : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc (c.idx j)) (s.center (c.idx j)) :=
    s.isBlowupAlongIdealSheaf_blowupMorphism _ hidxlt
  have : Flat (c.map j (le_of_lt hj)) := c.flat_map j (le_of_lt hj)
  have hbj : Blowup.IsBlowupAlongIdealSheaf (s'.transitionMapSucc j) (s'.center j) := s'.isBlowupAlongIdealSheaf_blowupMorphism j hj
  have hbl' : Blowup.IsBlowupAlongIdealSheaf (s'.transitionMapSucc j) ((s.center (c.idx j)).comap (c.map j (le_of_lt hj))) := by
    rw [← c.center_comap j hj]
    exact hbj
  obtain ⟨q, hq, hsq⟩ := hbl.exists_isPullback_of_flat (c.map j (le_of_lt hj)) hbl'
  have hcart0 : Blowup.IsLocallyGeneratedByNonZeroDivisor ((s'.center j).comap (s'.transitionMapSucc j)) := by
    unfold FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf at hbj
    exact hbj.1
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor
      ((s.center (c.idx j)).comap (s'.transitionMapSucc j ≫ c.map j (le_of_lt hj))) := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, ← c.center_comap j hj]
    exact hcart0
  have hstep : c.mapToEarlierScheme (j + 1) hj (c.idx j + 1) (c.idx_strictMono j hj) ≫ s.transitionMapSucc (c.idx j)
      = s'.transitionMapSucc j ≫ c.map j (le_of_lt hj) := by
    rw [← c.mapToEarlierScheme_eq_comp_blowupMorphism (j + 1) hj (c.idx j) (c.idx_strictMono j hj), mapToEarlierScheme_eq_map_comp_transitionMap]
    exact (c.step j hj).symm
  have heq : c.mapToEarlierScheme (j + 1) hj (c.idx j + 1) (c.idx_strictMono j hj) = q :=
    hbl.hom_ext_of_comp_eq hcart hstep hq
  rw [heq]
  exact hsq


end

private def markedMapToEarlierScheme_consolidated420 {k k' : Type u} [Field k] [Field k'] {A B : Scheme.{u}}
    {p : A ⟶ Spec (CommRingCat.of k)} {q : B ⟶ Spec (CommRingCat.of k')} {g : B ⟶ A}
    {I : A.IdealSheafData} {I' : B.IdealSheafData} {m : ℕ} {E : List A.IdealSheafData}
    {E' : List B.IdealSheafData} (s : MarkedBlowupSequenceData p I m E) (s' : MarkedBlowupSequenceData q I' m E')
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (j : ℕ) (hj : j ≤ s'.length) (i : ℕ) (hi : i ≤ c.idx j) : s'.obj j ⟶ s.obj i :=
  c.mapToEarlierScheme j hj i hi

private def markedMap_consolidated420 {k k' : Type u} [Field k] [Field k'] {A B : Scheme.{u}}
    {p : A ⟶ Spec (CommRingCat.of k)} {q : B ⟶ Spec (CommRingCat.of k')} {g : B ⟶ A}
    {I : A.IdealSheafData} {I' : B.IdealSheafData} {m : ℕ} {E : List A.IdealSheafData}
    {E' : List B.IdealSheafData} (s : MarkedBlowupSequenceData p I m E) (s' : MarkedBlowupSequenceData q I' m E')
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (j : ℕ) (hj : j ≤ s'.length) : s'.obj j ⟶ s.obj (c.idx j) :=
  c.map j hj

section
variable {k k' : Type u} [Field k] [Field k'] {A B : Scheme.{u}} {p : A ⟶ Spec (CommRingCat.of k)} {q : B ⟶ Spec (CommRingCat.of k')} {g : B ⟶ A} {I : A.IdealSheafData} {I' : B.IdealSheafData} {m : ℕ} {E : List A.IdealSheafData} {E' : List B.IdealSheafData} (s : MarkedBlowupSequenceData p I m E) (s' : MarkedBlowupSequenceData q I' m E') (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups) (j : ℕ) (hj : j ≤ s'.length)

private theorem markedMapToEarlierScheme_comp_projectionToBase_consolidated420 (i : ℕ) (hi : i ≤ c.idx j) :
    markedMapToEarlierScheme_consolidated420 s s' c j hj i hi ≫ s.proj i = s'.proj j ≫ g := by
  have h := c.mapToEarlierScheme_comp_projectionToBase j hj i hi
  rw [MarkedBlowupSequenceData.toMarkedSequence_projectionToBase, MarkedBlowupSequenceData.toMarkedSequence_projectionToBase] at h
  exact h

private theorem markedMapToEarlierScheme_index_consolidated420 :
    markedMapToEarlierScheme_consolidated420 s s' c j hj (c.idx j) le_rfl = markedMap_consolidated420 s s' c j hj :=
  c.mapToEarlierScheme_index j hj


end

theorem ideal_boundary_last_eq_comap_lastMap {k k' : Type u} [Field k] [Field k'] {X Y : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k')}
    {g : Y ⟶ X} [Flat g]
    {I : X.IdealSheafData} {I' : Y.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} {E' : List Y.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (s' : MarkedBlowupSequenceData q I' m E')
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hI : I' = I.comap g)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (E.map (fun D => D.comap g)))
    (hN : ∀ i : ℕ, i ≤ s.length → IsNoetherian (s.obj i))
    (hN' : ∀ j : ℕ, j ≤ s'.length → IsNoetherian (s'.obj j)) :
    s'.ideal s'.length = (s.ideal s.length).comap c.lastMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
        ((s.boundary s.length).map (fun D => D.comap c.lastMap)) := by
  subst hI
  have hrun : ∀ (j : ℕ) (hj : j ≤ s'.length) (b : ℕ) (hb : b ≤ c.idx j) (a : ℕ) (hab : a ≤ b),
      (∀ t : ℕ, a ≤ t → t < b → ∀ j' : ℕ, j' < s'.length → c.idx j' ≠ t) →
        (s.ideal a).comap (markedMapToEarlierScheme_consolidated420 s s' c j hj a (le_trans hab hb)) =
            (s.ideal b).comap (markedMapToEarlierScheme_consolidated420 s s' c j hj b hb) ∧
          MarkedIdealWithBoundary.SameNontrivialBoundary
            ((s.boundary a).map (fun D => D.comap (markedMapToEarlierScheme_consolidated420 s s' c j hj a (le_trans hab hb))))
            ((s.boundary b).map (fun D => D.comap (markedMapToEarlierScheme_consolidated420 s s' c j hj b hb))) := by
    intro j hj b
    induction b with
    | zero =>
        intro hb a hab _
        have ha0 : a = 0 := Nat.le_zero.1 hab
        subst ha0
        exact ⟨rfl, MarkedIdealWithBoundary.SameNontrivialBoundary.refl _⟩
    | succ nn ihb =>
        intro hb a hab hun
        rcases Nat.lt_or_ge a (nn + 1) with h | h
        · have han : a ≤ nn := Nat.lt_succ_iff.1 h
          have hnb : nn ≤ c.idx j := le_trans (Nat.le_succ nn) hb
          obtain ⟨i1, b1⟩ := ihb hnb a han (fun t ht ht2 => hun t ht (Nat.lt_succ_of_lt ht2))
          have hnlt : nn < c.idx j := lt_of_lt_of_le (Nat.lt_succ_self nn) hb
          have hlen : c.idx j ≤ s.length := c.index_le_length j hj
          have hnlen : nn < s.length := lt_of_lt_of_le hnlt hlen
          have hntop : (s.center nn).comap (markedMapToEarlierScheme_consolidated420 s s' c j hj nn hnb) = ⊤ := by
            have h0 := c.comap_center_mapToEarlierScheme_eq_top_of_unmatched j hj nn hnlt (hun nn han (Nat.lt_succ_self nn))
            rw [MarkedBlowupSequenceData.toMarkedSequence_center] at h0
            exact h0
          have hmt : markedMapToEarlierScheme_consolidated420 s s' c j hj nn hnb
              = markedMapToEarlierScheme_consolidated420 s s' c j hj (nn + 1) hb ≫ s.map nn := by
            have h0 := c.mapToEarlierScheme_eq_comp_blowupMorphism j hj nn hnlt
            rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism] at h0
            exact h0
          have htop2 : (s.center nn).comap
              (markedMapToEarlierScheme_consolidated420 s s' c j hj (nn + 1) hb ≫ s.map nn) = ⊤ := by
            rw [← hmt]
            exact hntop
          obtain ⟨i2, b2⟩ := comap_ideal_boundary_succ_of_comap_center_eq_top_consolidated420 s nn hnlen (markedMapToEarlierScheme_consolidated420 s s' c j hj (nn + 1) hb)
            (hN (nn + 1) hnlen) htop2
          constructor
          · refine i1.trans ?_
            rw [hmt]
            exact i2
          · refine b1.trans ?_
            rw [hmt]
            exact b2.symm
        · have hae : a = nn + 1 := le_antisymm hab h
          subst hae
          exact ⟨rfl, MarkedIdealWithBoundary.SameNontrivialBoundary.refl _⟩
  have main : ∀ (j : ℕ) (hj : j ≤ s'.length),
      s'.ideal j = (s.ideal (c.idx j)).comap (markedMap_consolidated420 s s' c j hj) ∧
        MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary j)
          ((s.boundary (c.idx j)).map (fun D => D.comap (markedMap_consolidated420 s s' c j hj))) := by
    intro j
    induction j with
    | zero =>
        intro hj0
        have hz : (0 : ℕ) ≤ c.idx 0 := Nat.zero_le _
        obtain ⟨r1, r2⟩ := hrun 0 hj0 (c.idx 0) le_rfl 0 hz
          (fun t _ ht => c.index_ne_of_lt_index_zero t ht)
        have hmi : markedMapToEarlierScheme_consolidated420 s s' c 0 hj0 (c.idx 0) le_rfl = markedMap_consolidated420 s s' c 0 hj0 :=
          markedMapToEarlierScheme_index_consolidated420 s s' c 0 hj0
        have e1 : s'.ideal 0 = (s.ideal 0).comap (markedMapToEarlierScheme_consolidated420 s s' c 0 hj0 0 hz) := by
          rw [s'.ideal_zero, s.ideal_zero, ← s.proj_zero, ← s'.proj_zero,
            ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
            markedMapToEarlierScheme_comp_projectionToBase_consolidated420]
        constructor
        · refine e1.trans ?_
          rw [← hmi]
          exact r1
        · have hmap : MarkedIdealWithBoundary.SameNontrivialBoundary
              (E'.map (fun D => D.comap (s'.proj 0)))
              ((E.map (fun D => D.comap g)).map (fun D => D.comap (s'.proj 0))) :=
            MarkedIdealWithBoundary.SameNontrivialBoundary.map _ (by simp) hE
          have hlist : (E.map (fun D => D.comap g)).map (fun D => D.comap (s'.proj 0))
              = (E.map (fun D => D.comap (s.proj 0))).map
                (fun D => D.comap (markedMapToEarlierScheme_consolidated420 s s' c 0 hj0 0 hz)) := by
            simp only [List.map_map]
            apply List.map_congr_left
            intro D _
            simp only [Function.comp_apply]
            rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
              markedMapToEarlierScheme_comp_projectionToBase_consolidated420]
          have hb0 : s'.boundary 0 = E'.map (fun D => D.comap (s'.proj 0)) := by
            rw [s'.boundary_zero, ← s'.proj_zero]
          have hb0s : s.boundary 0 = E.map (fun D => D.comap (s.proj 0)) := by
            rw [s.boundary_zero, ← s.proj_zero]
          rw [hb0]
          refine hmap.trans ?_
          rw [hlist, ← hb0s, ← hmi]
          exact r2
    | succ n ih =>
        intro hj
        have hn : n < s'.length := hj
        have hnle : n ≤ s'.length := le_of_lt hn
        obtain ⟨ihI, ihB⟩ := ih hnle
        have hidxlt : c.idx n < s.length := c.idx_lt n hn
        have hstr : c.idx n < c.idx (n + 1) := c.idx_strictMono n hn
        have hcen : s'.center n = (s.center (c.idx n)).comap (markedMap_consolidated420 s s' c n hnle) := by
          have h0 := c.center_comap n hn
          rw [MarkedBlowupSequenceData.toMarkedSequence_center, MarkedBlowupSequenceData.toMarkedSequence_center] at h0
          exact h0
        have hsq : IsPullback (markedMapToEarlierScheme_consolidated420 s s' c (n + 1) hj (c.idx n + 1) hstr) (s'.map n)
            (s.map (c.idx n)) (markedMap_consolidated420 s s' c n hnle) := by
          have h0 := c.isPullback_blowupMorphism n hn
          rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism] at h0
          exact h0
        have hw := hsq.w
        have hexc : (s'.center n).comap (s'.map n)
            = ((s.center (c.idx n)).comap (s.map (c.idx n))).comap
              (markedMapToEarlierScheme_consolidated420 s s' c (n + 1) hj (c.idx n + 1) hstr) := by
          rw [hcen, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hw]
        have hblow : Blowup.IsBlowupAlongIdealSheaf (s.map (c.idx n)) (s.center (c.idx n)) := s.isBlowup _ hidxlt
        have hb' : Blowup.IsBlowupAlongIdealSheaf (s'.map n) (s'.center n) := s'.isBlowup n hn
        have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor ((s'.center n).comap (s'.map n)) := by
          unfold FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf at hb'
          exact hb'.1
        have hstepI : s'.ideal (n + 1)
            = (s.ideal (c.idx n + 1)).comap
              (markedMapToEarlierScheme_consolidated420 s s' c (n + 1) hj (c.idx n + 1) hstr) := by
          refine (hcart.pow m).eq_of_mul_eq_mul ?_
          have h1 := s'.ideal_succ n hn
          have h2 := s.ideal_succ (c.idx n) hidxlt
          simp only [Blowup.exceptionalIdeal_eq_comap] at h1 h2
          rw [h1, ihI, ← Scheme.IdealSheafData.comap_comp, ← hw,
            Scheme.IdealSheafData.comap_comp, ← h2, Scheme.IdealSheafData.comap_mul,
            Scheme.IdealSheafData.comap_pow, ← hexc]
        have : Flat (markedMap_consolidated420 s s' c n hnle) := c.flat_map n hnle
        have := hN (c.idx n + 1) hidxlt
        have := hN' (n + 1) hj
        have hST : ∀ D : (s.obj (c.idx n)).IdealSheafData,
            (Blowup.strictTransform (s.map (c.idx n)) (s.center (c.idx n)) D).comap
                (markedMapToEarlierScheme_consolidated420 s s' c (n + 1) hj (c.idx n + 1) hstr)
              = Blowup.strictTransform (s'.map n) (s'.center n) (D.comap (markedMap_consolidated420 s s' c n hnle)) := by
          intro D
          rw [comap_strictTransform_of_flat_of_isLocallyNoetherian (s.map (c.idx n))
            (markedMap_consolidated420 s s' c n hnle) (s'.map n)
            (markedMapToEarlierScheme_consolidated420 s s' c (n + 1) hj (c.idx n + 1) hstr) hsq
            (s.center (c.idx n)) D hblow, ← hcen]
        have hB2 : ((s.boundary (c.idx n)).map (fun D => D.comap (markedMap_consolidated420 s s' c n hnle))).map
              (Blowup.strictTransform (s'.map n) (s'.center n)) ++ [(s'.center n).comap (s'.map n)]
            = (s.boundary (c.idx n + 1)).map
              (fun D => D.comap (markedMapToEarlierScheme_consolidated420 s s' c (n + 1) hj (c.idx n + 1) hstr)) := by
          rw [s.boundary_succ (c.idx n) hidxlt, List.map_append, List.map_map, List.map_map,
            List.map_cons, List.map_nil, Blowup.exceptionalIdeal_eq_comap, ← hexc]
          congr 1
          apply List.map_congr_left
          intro D _
          exact (hST D).symm
        have hB1 : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary (n + 1))
            (((s.boundary (c.idx n)).map (fun D => D.comap (markedMap_consolidated420 s s' c n hnle))).map
              (Blowup.strictTransform (s'.map n) (s'.center n)) ++
                [(s'.center n).comap (s'.map n)]) := by
          rw [s'.boundary_succ n hn, Blowup.exceptionalIdeal_eq_comap]
          exact MonomialCenter.sameNontrivialBoundary_append
            (MarkedIdealWithBoundary.SameNontrivialBoundary.map _ (strictTransform_top _ _) ihB)
            (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _)
        obtain ⟨r1, r2⟩ := hrun (n + 1) hj (c.idx (n + 1)) le_rfl (c.idx n + 1) hstr
          (fun t ht ht2 => c.index_ne_of_index_lt_of_lt_index_succ n hj t (by omega) ht2)
        have hmi :
            markedMapToEarlierScheme_consolidated420 s s' c (n + 1) hj (c.idx (n + 1)) le_rfl = markedMap_consolidated420 s s' c (n + 1) hj :=
          markedMapToEarlierScheme_index_consolidated420 s s' c (n + 1) hj
        constructor
        · refine hstepI.trans ?_
          rw [← hmi]
          exact r1
        · refine hB1.trans ?_
          rw [hB2, ← hmi]
          exact r2
  obtain ⟨hmI, hmB⟩ := main s'.length le_rfl
  have e1 : (s.ideal s.length).comap c.lastMap
      = (s.ideal (c.idx s'.length)).comap (markedMap_consolidated420 s s' c s'.length le_rfl) :=
    comap_comp_eqToHom_consolidated420 (F := s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.schemeAt) (fun n => s.ideal n) c.idx_length
      (c.map s'.length le_rfl)
  have e2 : (s.boundary s.length).map (fun D => D.comap c.lastMap)
      = (s.boundary (c.idx s'.length)).map
        (fun D => D.comap (markedMap_consolidated420 s s' c s'.length le_rfl)) :=
    map_comap_comp_eqToHom_consolidated420 (F := s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.schemeAt) (fun n => s.boundary n) c.idx_length
      (c.map s'.length le_rfl)
  exact ⟨hmI.trans e1.symm, sameNontrivialBoundary_of_eq_consolidated420 hmB e2⟩

end SequenceOfBlowupsPullback


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalizationBaseChange
section


section

noncomputable abbrev MarkedIdealWithBoundary.pullbackWithBoundary (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (E' : List Y.IdealSheafData) : MarkedIdealWithBoundary.{u} :=
  (T.pullbackOverField Y k' q g).withBoundary E'

private theorem false_of_mem_support_top_consolidated469 {X : Scheme.{u}} (y : ↥X)
    (h : y ∈ (⊤ : X.IdealSheafData).support) : False := by
  have hb : (⊤ : X.IdealSheafData).support = ⊥ :=
    (Scheme.IdealSheafData.support_eq_bot_iff _).mpr rfl
  rw [hb] at h
  have h' : y ∈ ((⊥ : TopologicalSpace.Closeds ↥X) : Set ↥X) := h
  rw [TopologicalSpace.Closeds.coe_bot] at h'
  simp at h'

private theorem false_of_mem_support_of_comap_eq_top_consolidated469 {A B : Scheme.{u}} (u : B ⟶ A)
    (I : A.IdealSheafData) (htop : I.comap u = ⊤) (y : ↥B) (hz : u.base y ∈ I.support) : False := by
  have hmem : y ∈ (I.comap u).support := Scheme.IdealSheafData.mem_support_comap.mpr hz
  rw [htop] at hmem
  exact false_of_mem_support_top_consolidated469 y hmem

private theorem flat_lastMap_consolidated469 {X X' : Scheme.{u}} {φ : X' ⟶ X}
    [Flat φ] {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (c : SequenceOfBlowupsPullback φ s' s) : Flat c.lastMap :=
  MorphismProperty.of_isPullback c.isPullback_lastMap.flip inferInstance

section
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

private theorem isNoetherian_schemeAt_of_le_length_consolidated469 (hX : IsNoetherian X) (d : MarkedBlowupSequenceData p I m E) :
    ∀ i ≤ d.length, IsNoetherian (d.obj i) := by
  have : IsNoetherian X := hX
  intro i
  induction i with
  | zero =>
      intro _
      exact isNoetherian_of_iso d.toBlowupSequenceData.isoZero.symm
  | succ n ih =>
      intro hn
      have : IsNoetherian (d.obj n) := ih (le_of_lt hn)
      exact isNoetherian_of_isBlowupAlongIdealSheaf (d.toBlowupSequenceData.isBlowup n hn)

private theorem centerAtLast_ne_top_of_isAdmissibleCenter_consolidated469 (s : MarkedBlowupSequenceData p I m E) (h : MarkedBlowupSequenceData.IsAdmissibleCenter s) : s.centerAtLast ≠ ⊤ := h.1


end

private theorem length_monomialIterateFromEmpty_zero_consolidated469 (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) :
    (monomialIterateFromEmpty hinv T 0).length = 0 := emptyMarkedBlowupSequenceData_length _ _ _ _

private theorem nonempty_sequenceOfBlowupsPullback_of_length_eq_one_consolidated469 {A B : Scheme.{u}} (φ : B ⟶ A)
    (t : BlowupSequenceData A) (t' : BlowupSequenceData B) (ht : t.length = 1) (ht' : t'.length = 1)
    (ψ : t'.obj 0 ⟶ t.obj 0)
    (hψ : t'.isoZero.hom ≫ φ ≫ t.isoZero.inv = ψ) (hflat : Flat ψ)
    (hcen : t'.center 0 = (t.center 0).comap ψ) (hne : t'.center 0 ≠ ⊤) :
    Nonempty (SequenceOfBlowupsPullback φ t'.toSequenceOfBlowups t.toSequenceOfBlowups) := by
  have := hflat
  have hlt : (0 : ℕ) < t.length := by rw [ht]; omega
  have hlt' : (0 : ℕ) < t'.length := by rw [ht']; omega
  have hB : Blowup.IsBlowupAlongIdealSheaf (t.map 0) (t.center 0) := t.isBlowup 0 hlt
  have hB' : Blowup.IsBlowupAlongIdealSheaf (t'.map 0) ((t.center 0).comap ψ) := by
    have h := t'.isBlowup 0 hlt'
    rwa [hcen] at h
  obtain ⟨qq, -, hqq⟩ := hB.exists_isPullback_of_flat ψ hB'
  refine ⟨SequenceOfBlowupsPullback.ofLengthOne φ t t' ht ht' qq ?_ ?_ hne⟩
  · rw [hψ]
    exact hqq
  · rw [hψ]
    exact hcen

section
variable {k₁ k₂ : Type u} [Field k₁] [Field k₂] {X₁ X₂ : Scheme.{u}} {p₁ : X₁ ⟶ Spec (CommRingCat.of k₁)} {I₁ : X₁.IdealSheafData} {m₁ : ℕ} {E₁ : List X₁.IdealSheafData} {p₂ : X₂ ⟶ Spec (CommRingCat.of k₂)} {I₂ : X₂.IdealSheafData} {m₂ : ℕ} {E₂ : List X₂.IdealSheafData} (g : X₂ ⟶ X₁) (hg : Flat g) (hinv : ComapIsoInvariance.{u}) (S : MarkedBlowupSequenceData p₁ I₁ m₁ E₁) (S' : MarkedBlowupSequenceData p₂ I₂ m₂ E₂) (hS : MarkedBlowupSequenceData.IsAdmissibleCenter S)
include hg hS

private theorem nonempty_sequenceOfBlowupsPullback_blowupAtCenter_of_comap_eq_top_consolidated469 (c : SequenceOfBlowupsPullback g S'.toSequenceOfBlowups S.toSequenceOfBlowups)
    (htop : (S.centerAtLast).comap c.lastMap = ⊤) :
    Nonempty (SequenceOfBlowupsPullback g S'.toSequenceOfBlowups (MarkedBlowupSequenceData.blowupAtCenter hinv S).toSequenceOfBlowups) := by
  have := hg
  have : Flat c.lastMap := flat_lastMap_consolidated469 c
  have hmiss : ∀ i : ℕ, i < (S.monomialBlowupStep hS).toBlowupSequenceData.length →
      ∀ z : ↥((S.monomialBlowupStep hS).toBlowupSequenceData.obj i),
        z ∈ ((S.monomialBlowupStep hS).toBlowupSequenceData.center i).support →
        ∀ y : ↥(S'.obj S'.length),
          c.lastMap.base y ≠ ((S.monomialBlowupStep hS).toBlowupSequenceData.projectionToBase i).base z := by
    intro i hi z hz y heq
    have hlen : (S.monomialBlowupStep hS).toBlowupSequenceData.length = 1 :=
      MarkedBlowupSequenceData.monomialBlowupStep_length ..
    have hi0 : i = 0 := by omega
    subst hi0
    have hzz : ((S.monomialBlowupStep hS).toBlowupSequenceData.projectionToBase 0).base z ∈ S.centerAtLast.support := hz
    have hz2 : c.lastMap.base y ∈ S.centerAtLast.support := by
      rw [heq]
      exact hzz
    exact false_of_mem_support_of_comap_eq_top_consolidated469 c.lastMap S.centerAtLast htop y hz2
  have hE0 : (emptyMarkedBlowupSequenceData (S'.proj S'.length ≫ p₂) (S'.ideal S'.length) m₂
      (S'.boundary S'.length)).toBlowupSequenceData.length = 0 := emptyMarkedBlowupSequenceData_length _ _ _ _
  have e := SequenceOfBlowupsPullback.ofCentersMissImage c.lastMap (S.monomialBlowupStep hS).toBlowupSequenceData hmiss
    (emptyMarkedBlowupSequenceData (S'.proj S'.length ≫ p₂) (S'.ideal S'.length) m₂
      (S'.boundary S'.length)).toBlowupSequenceData hE0
  have c2 := SequenceOfBlowupsPullback.concat S.toBlowupSequenceData (S.monomialBlowupStep hS).toBlowupSequenceData
    S'.toBlowupSequenceData
    (emptyMarkedBlowupSequenceData (S'.proj S'.length ≫ p₂) (S'.ideal S'.length) m₂
      (S'.boundary S'.length)).toBlowupSequenceData c e
  refine ⟨?_⟩
  rw [MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv S hS, MarkedBlowupSequenceData.append_toBlowupSequenceData]
  exact SequenceOfBlowupsPullback.ofConcatLengthZero g S'.toBlowupSequenceData
    (S.appendToBlowupSequenceData (S.monomialBlowupStep hS)).toSequenceOfBlowups
    (emptyMarkedBlowupSequenceData (S'.proj S'.length ≫ p₂) (S'.ideal S'.length) m₂
      (S'.boundary S'.length)).toBlowupSequenceData hE0 c2

private theorem nonempty_sequenceOfBlowupsPullback_blowupAtCenter_consolidated469 (hS' : MarkedBlowupSequenceData.IsAdmissibleCenter S') (c : SequenceOfBlowupsPullback g S'.toSequenceOfBlowups S.toSequenceOfBlowups)
    (hcen : S'.centerAtLast = (S.centerAtLast).comap c.lastMap) :
    Nonempty (SequenceOfBlowupsPullback g (MarkedBlowupSequenceData.blowupAtCenter hinv S').toSequenceOfBlowups
      (MarkedBlowupSequenceData.blowupAtCenter hinv S).toSequenceOfBlowups) := by
  have := hg
  have : Flat c.lastMap := flat_lastMap_consolidated469 c
  have h1 : (S'.monomialBlowupStep hS').toBlowupSequenceData.isoZero.hom ≫ c.lastMap ≫
      (S.monomialBlowupStep hS).toBlowupSequenceData.isoZero.inv
      = c.lastMap ≫ (S.monomialBlowupStep hS).toBlowupSequenceData.isoZero.inv :=
    Category.id_comp _
  have h2 : c.lastMap ≫ (S.monomialBlowupStep hS).toBlowupSequenceData.isoZero.inv = c.lastMap :=
    Category.comp_id _
  have hconj : (S'.monomialBlowupStep hS').toBlowupSequenceData.isoZero.hom ≫ c.lastMap ≫
      (S.monomialBlowupStep hS).toBlowupSequenceData.isoZero.inv = c.lastMap := h1.trans h2
  obtain ⟨e⟩ := nonempty_sequenceOfBlowupsPullback_of_length_eq_one_consolidated469 c.lastMap
    (S.monomialBlowupStep hS).toBlowupSequenceData
    (S'.monomialBlowupStep hS').toBlowupSequenceData (MarkedBlowupSequenceData.monomialBlowupStep_length ..)
    (MarkedBlowupSequenceData.monomialBlowupStep_length ..) c.lastMap hconj
    (flat_lastMap_consolidated469 c) hcen (centerAtLast_ne_top_of_isAdmissibleCenter_consolidated469 S' hS')
  refine ⟨?_⟩
  rw [MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv S hS,
    MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv S' hS',
    MarkedBlowupSequenceData.append_toBlowupSequenceData, MarkedBlowupSequenceData.append_toBlowupSequenceData]
  exact SequenceOfBlowupsPullback.concat S.toBlowupSequenceData (S.monomialBlowupStep hS).toBlowupSequenceData
    S'.toBlowupSequenceData (S'.monomialBlowupStep hS').toBlowupSequenceData c e


end

private theorem minIndexCard_ne_zero_and_monomialCenter_comap_of_flat_consolidated469 (hGeom : MonomialGeometryHypotheses.{u})
    (Tn : MarkedIdealWithBoundary.{u})
    (Yj : Scheme.{u}) (k' : Type u) [instk' : Field k'] (qj : Yj ⟶ Spec (CommRingCat.of k'))
    (φ : Yj ⟶ Tn.scheme) (hφ : Flat φ)
    (I' : Yj.IdealSheafData) (E2 : List Yj.IdealSheafData)
    (hTn : MonomialCenter.IsLocallyMonomialTriple Tn)
    (hTj : MonomialCenter.IsLocallyMonomialTriple (@MarkedIdealWithBoundary.mk k' instk' Yj qj I' Tn.mult E2))
    (hI' : I' = Tn.ideal.comap φ)
    (hE2 : MarkedIdealWithBoundary.SameNontrivialBoundary E2 (Tn.boundary.map fun D => D.comap φ))
    (hordφ : ∀ (A : Tn.scheme.IdealSheafData) (y : ↥Yj),
      orderAt (A.comap φ) y = orderAt A (φ y)) :
    (minIndexCard I' Tn.mult E2 ≠ 0 → minIndexCard Tn.ideal Tn.mult Tn.boundary ≠ 0) ∧
      (minIndexCard Tn.ideal Tn.mult Tn.boundary ≠ 0 →
        ((monomialCenter Tn.ideal Tn.mult Tn.boundary).comap φ = ⊤ ∨
          (minIndexCard I' Tn.mult E2 ≠ 0 ∧
            monomialCenter I' Tn.mult E2 = (monomialCenter Tn.ideal Tn.mult Tn.boundary).comap φ))) := by
  classical
  have := hφ
  subst hI'
  have htrip : (@MarkedIdealWithBoundary.mk k' instk' Yj qj (Tn.ideal.comap φ) Tn.mult E2).withBoundary
      (Tn.boundary.map fun D => D.comap φ) = Tn.pullbackOverField Yj k' qj φ :=
    MarkedIdealWithBoundary.mk_eq_mk Yj Tn.mult rfl rfl rfl
  have hTpb : MonomialCenter.IsLocallyMonomialTriple (Tn.pullbackOverField Yj k' qj φ) := by
    rw [← htrip]
    exact MonomialCenter.isLocallyMonomialTriple_withBoundary hGeom _ hTj _ hE2
  have hP : MonomialCenter.IsComponentCompatiblePullback Tn Yj k' qj φ :=
    MonomialCenter.IsComponentCompatiblePullback.of_flat hGeom Tn hTn.valid Yj k' qj φ hTpb.valid hordφ
  have hmin : minIndexCard (Tn.pullbackOverField Yj k' qj φ).ideal (Tn.pullbackOverField Yj k' qj φ).mult
      (Tn.pullbackOverField Yj k' qj φ).boundary = minIndexCard (Tn.ideal.comap φ) Tn.mult E2 :=
    (MonomialCenter.minIndexCard_eq_of_sameNontrivialBoundary (Tn.ideal.comap φ) Tn.mult hE2).symm
  have hcenpb : monomialCenter (Tn.pullbackOverField Yj k' qj φ).ideal (Tn.pullbackOverField Yj k' qj φ).mult
      (Tn.pullbackOverField Yj k' qj φ).boundary = monomialCenter (Tn.ideal.comap φ) Tn.mult E2 :=
    (MonomialCenter.monomialCenter_eq_of_sameNontrivialBoundary (Tn.ideal.comap φ) Tn.mult hE2).symm
  refine ⟨?_, ?_⟩
  · intro hne
    have hne' : minIndexCard (Tn.pullbackOverField Yj k' qj φ).ideal (Tn.pullbackOverField Yj k' qj φ).mult
        (Tn.pullbackOverField Yj k' qj φ).boundary ≠ 0 := by
      rw [hmin]
      exact hne
    exact (MonomialCenter.minIndexCard_ne_zero_and_le_pullbackOverField hGeom Tn Yj k' qj φ hTn hTpb hP hne').1
  · intro h0
    by_cases hz : minIndexCard (Tn.pullbackOverField Yj k' qj φ).ideal (Tn.pullbackOverField Yj k' qj φ).mult
        (Tn.pullbackOverField Yj k' qj φ).boundary = 0
    · exact Or.inl (MonomialCenter.comap_monomialCenter_eq_top hGeom Tn Yj k' qj φ hTn hTpb hP h0
        (Or.inl hz))
    · have hle := (MonomialCenter.minIndexCard_pullbackOverField_eq_zero_or_centerInvariant_le hGeom Tn Yj k' qj φ hTn hTpb
        hP).resolve_left hz
      rw [MonomialCenter.centerInvariant_le_iff] at hle
      rcases hle with hlt | ⟨hm, hx, hs⟩
      · exact Or.inl (MonomialCenter.comap_monomialCenter_eq_top hGeom Tn Yj k' qj φ hTn hTpb hP h0
          (Or.inr hlt))
      · refine Or.inr ⟨?_, ?_⟩
        · rw [← hmin]
          exact hz
        · rw [← hcenpb]
          exact MonomialCenter.monomialCenter_pullbackOverField_eq_comap hGeom Tn Yj k' qj φ hTn hTpb hP
            hm.symm hx.symm
            (MonomialCenter.lexMaxIndices_pullbackOverField_eq_image Tn Yj k' qj φ hs)

section
variable (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) (hg : Flat g) (E' : List Y.IdealSheafData) (hT : MonomialCenter.IsLocallyMonomialTriple T) (hE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.boundary.map fun D => D.comap g)) (hT' : MonomialCenter.IsLocallyMonomialTriple (T.pullbackWithBoundary Y k' q g E')) (hord : ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)), b ≫ T.structMap = pB → ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData), (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible → ∀ (Q : Scheme.{u}) (a : Q ⟶ B) (b' : Q ⟶ Y), IsPullback a b' b g → ∀ (A : B.IdealSheafData) (z : ↥Q), orderAt (A.comap a) z = orderAt A (a z))
include hGeom hg hT hE hT' hord

private theorem sequenceOfBlowupsPullback_blowupAtCenter_cases_consolidated469
    (S : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (S' : MarkedBlowupSequenceData (T.pullbackWithBoundary Y k' q g E').structMap
      (T.pullbackWithBoundary Y k' q g E').ideal (T.pullbackWithBoundary Y k' q g E').mult
      (T.pullbackWithBoundary Y k' q g E').boundary)
    (hTn : MonomialCenter.IsLocallyMonomialTriple (tripleAtLastBlowup T S))
    (hTj : MonomialCenter.IsLocallyMonomialTriple
      (tripleAtLastBlowup (T.pullbackWithBoundary Y k' q g E') S'))
    (c : SequenceOfBlowupsPullback g S'.toSequenceOfBlowups S.toSequenceOfBlowups) :
    (MarkedBlowupSequenceData.IsAdmissibleCenter S' →
        minIndexCard (tripleAtLastBlowup T S).ideal (tripleAtLastBlowup T S).mult
          (tripleAtLastBlowup T S).boundary ≠ 0) ∧
      (MarkedBlowupSequenceData.IsAdmissibleCenter S →
        Nonempty (SequenceOfBlowupsPullback g S'.toSequenceOfBlowups
            (MarkedBlowupSequenceData.blowupAtCenter hinv S).toSequenceOfBlowups) ∨
          (MarkedBlowupSequenceData.IsAdmissibleCenter S' ∧
            Nonempty (SequenceOfBlowupsPullback g
              (MarkedBlowupSequenceData.blowupAtCenter hinv S').toSequenceOfBlowups
              (MarkedBlowupSequenceData.blowupAtCenter hinv S).toSequenceOfBlowups))) := by
  classical
  have hfl1 : Flat g := hg
  have hfl2 : @Flat (T.pullbackWithBoundary Y k' q g E').scheme T.scheme g := hg
  have hflt : Flat c.lastMap := flat_lastMap_consolidated469 c
  have hN : ∀ i : ℕ, i ≤ S.length → IsNoetherian (S.obj i) :=
    isNoetherian_schemeAt_of_le_length_consolidated469 hT.valid.isNoetherian S
  have hN' : ∀ i : ℕ, i ≤ S'.length → IsNoetherian (S'.obj i) :=
    isNoetherian_schemeAt_of_le_length_consolidated469 hT'.valid.isNoetherian S'
  obtain ⟨hIdeal, hboundary⟩ := SequenceOfBlowupsPullback.ideal_boundary_last_eq_comap_lastMap S S' c rfl hE hN hN'
  have hsq : IsPullback c.lastMap (S'.proj S'.length) (S.proj S.length) g := by
    rw [MarkedBlowupSequenceData.projectionToBase_eq_toSequenceOfBlowups S S.length,
      MarkedBlowupSequenceData.projectionToBase_eq_toSequenceOfBlowups S' S'.length]
    exact c.isPullback_lastMap
  have hordφ : ∀ (A : (S.obj S.length).IdealSheafData) (y : ↥(S'.obj S'.length)),
      orderAt (A.comap c.lastMap) y = orderAt A (c.lastMap y) :=
    fun A y => hord (S.obj S.length) (S.proj S.length) (S.proj S.length ≫ T.structMap) rfl
      (S.ideal S.length) (S.boundary S.length) hTn.valid (S'.obj S'.length) c.lastMap
      (S'.proj S'.length) hsq A y
  have hminCard := minIndexCard_ne_zero_and_monomialCenter_comap_of_flat_consolidated469 hGeom (tripleAtLastBlowup T S)
    (S'.obj S'.length) k' (S'.proj S'.length ≫ q) c.lastMap
    (flat_lastMap_consolidated469 c) (S'.ideal S'.length) (S'.boundary S'.length)
    hTn hTj hIdeal hboundary hordφ
  refine ⟨fun hok' => hminCard.1
    (minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter (T.pullbackWithBoundary Y k' q g E') S' hok'), ?_⟩
  intro hok
  have h0 := minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter T S hok
  rcases hminCard.2 h0 with hmiss | ⟨hne', hcenEq⟩
  · exact Or.inl
      (nonempty_sequenceOfBlowupsPullback_blowupAtCenter_of_comap_eq_top_consolidated469 g hg hinv S S' hok c hmiss)
  · have hok' : MarkedBlowupSequenceData.IsAdmissibleCenter S' :=
      isAdmissibleCenter_of_minIndexCard_tripleAtLastBlowup_ne_zero hGeom (T.pullbackWithBoundary Y k' q g E') S'
        hTj hne'
    exact Or.inr ⟨hok', nonempty_sequenceOfBlowupsPullback_blowupAtCenter_consolidated469 g hg hinv S S' hok hok' c hcenEq⟩

private theorem exists_sequenceOfBlowupsPullback_monomialIterateFromEmpty_consolidated469
    (n : ℕ) :
    n ≤ monomialStallIndexOfTriple hinv T →
    ∃ j : ℕ,
      (∀ j' : ℕ, j' < j →
        MarkedBlowupSequenceData.IsAdmissibleCenter (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j')) ∧
      Nonempty (SequenceOfBlowupsPullback g
        (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j).toSequenceOfBlowups
        (monomialIterateFromEmpty hinv T n).toSequenceOfBlowups) := by
  have := hg
  induction n with
  | zero =>
    intro _
    refine ⟨0, fun j' hj' => absurd hj' (Nat.not_lt_zero j'), ⟨?_⟩⟩
    refine SequenceOfBlowupsPullback.ofCentersMissImage g (monomialIterateFromEmpty hinv T 0).toBlowupSequenceData ?_
      (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') 0).toBlowupSequenceData
      (length_monomialIterateFromEmpty_zero_consolidated469 hinv (T.pullbackWithBoundary Y k' q g E'))
    intro i hi
    exact absurd hi (by rw [length_monomialIterateFromEmpty_zero_consolidated469 hinv T]; exact Nat.not_lt_zero i)
  | succ n ih =>
    intro hn
    have hn' : n < monomialStallIndexOfTriple hinv T := lt_of_lt_of_le (Nat.lt_succ_self n) hn
    obtain ⟨j, hjstep, hc⟩ := ih (le_of_lt hn')
    obtain ⟨c⟩ := hc
    have hok : MarkedBlowupSequenceData.IsAdmissibleCenter (monomialIterateFromEmpty hinv T n) :=
      isAdmissibleCenter_of_lt_monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary n hn'
    rcases (sequenceOfBlowupsPullback_blowupAtCenter_cases_consolidated469 hGeom hinv T Y k' q g hg E' hT hE hT' hord
      (monomialIterateFromEmpty hinv T n)
      (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j)
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT n)
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv
        (T.pullbackWithBoundary Y k' q g E') hT' j) c).2 hok with h | ⟨hok', h⟩
    · exact ⟨j, hjstep, h⟩
    · refine ⟨j + 1, ?_, h⟩
      intro j' hj'
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj') with h1 | h1
      · exact hjstep j' h1
      · rw [h1]
        exact hok'


end

theorem monomialPrincipalization_isPullbackBlowupSequence_of_flat
    (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) [Flat g] (E' : List Y.IdealSheafData)
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.boundary.map fun D => D.comap g))
    (hT' : MonomialCenter.IsLocallyMonomialTriple (T.pullbackWithBoundary Y k' q g E'))
    (hord : ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)),
      b ≫ T.structMap = pB →
      ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
        (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible →
        ∀ (Q : Scheme.{u}) (a : Q ⟶ B) (b' : Q ⟶ Y), IsPullback a b' b g →
          ∀ (A : B.IdealSheafData) (z : ↥Q), orderAt (A.comap a) z = orderAt A (a z)) :
    IsPullbackBlowupSequence g
      (monomialPrincipalization hinv (T.pullbackWithBoundary Y k' q g E')).toSequenceOfBlowups
      (monomialPrincipalization hinv T).toSequenceOfBlowups := by
  classical
  have hg : Flat g := inferInstance
  obtain ⟨j, hjstep, hc⟩ := exists_sequenceOfBlowupsPullback_monomialIterateFromEmpty_consolidated469 hGeom hinv T Y k' q g hg E'
    hT hE hT' hord (monomialStallIndexOfTriple hinv T) le_rfl
  obtain ⟨c⟩ := hc
  have hstall : ¬ MarkedBlowupSequenceData.IsAdmissibleCenter
      (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j) := by
    intro hok'
    refine (sequenceOfBlowupsPullback_blowupAtCenter_cases_consolidated469 hGeom hinv T Y k' q g hg E' hT hE hT' hord
      (monomialIterateFromEmpty hinv T (monomialStallIndexOfTriple hinv T))
      (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j)
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT
        (monomialStallIndexOfTriple hinv T))
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv
        (T.pullbackWithBoundary Y k' q g E') hT' j) c).1 hok' ?_
    exact minIndexCard_monomialIterateFromEmpty_stallIndex_eq_zero hGeom hinv T hT
  have hjeq : monomialStallIndex hinv (T.pullbackWithBoundary Y k' q g E').structMap
      (T.pullbackWithBoundary Y k' q g E').ideal (T.pullbackWithBoundary Y k' q g E').mult
      (T.pullbackWithBoundary Y k' q g E').boundary = j :=
    monomialStallIndex_eq_of_isStationaryAt hinv (T.pullbackWithBoundary Y k' q g E').structMap
      (T.pullbackWithBoundary Y k' q g E').ideal (T.pullbackWithBoundary Y k' q g E').mult
      (T.pullbackWithBoundary Y k' q g E').boundary j
      ((MarkedBlowupSequenceData.isStationaryAt_iff_not_isAdmissibleCenter hinv
        (emptyMarkedBlowupSequenceData (T.pullbackWithBoundary Y k' q g E').structMap
          (T.pullbackWithBoundary Y k' q g E').ideal (T.pullbackWithBoundary Y k' q g E').mult
          (T.pullbackWithBoundary Y k' q g E').boundary) j).mpr hstall) hjstep
  rw [monomialPrincipalization_apply, monomialPrincipalization_apply, monomialBlowupSeq_eq_monomialBlowupIterate,
    monomialBlowupSeq_eq_monomialBlowupIterate, hjeq]
  exact SequenceOfBlowupsPullback.isPullbackSequenceOfBlowups c

private theorem smooth_fst_of_isPullback_consolidated469 {X Y B Q : Scheme.{u}} {hm : Y ⟶ X}
    [Smooth hm] {b : B ⟶ X} {a : Q ⟶ B} {b' : Q ⟶ Y}
    (hsq : IsPullback a b' b hm) : Smooth a :=
  MorphismProperty.of_isPullback hsq.flip inferInstance

theorem monomialPrincipalization_isPullbackBlowupSequence_of_smooth
    (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [Smooth h] (_hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
    (hT' : MonomialCenter.IsLocallyMonomialTriple ((T.pullbackAlong Y q h).withBoundary E')) :
    IsPullbackBlowupSequence h
      (monomialPrincipalization hinv ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
      (monomialPrincipalization hinv T).toSequenceOfBlowups := by
  have : Flat h := inferInstance
  have hE2 : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.boundary.map fun D => D.comap h) := hE.symm
  have hT2 : MonomialCenter.IsLocallyMonomialTriple (T.pullbackWithBoundary Y T.base q h E') := hT'
  have hord : ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)),
      b ≫ T.structMap = pB →
      ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
        (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible →
        ∀ (Q : Scheme.{u}) (a : Q ⟶ B) (b' : Q ⟶ Y), IsPullback a b' b h →
          ∀ (A : B.IdealSheafData) (z : ↥Q), orderAt (A.comap a) z = orderAt A (a z) := by
    intro B b pB hbp IB EB hvalid Q a b' hsq A z
    have : CharZero T.base := hvalid.charZero
    have : Smooth pB := hvalid.smooth
    have : Smooth a := smooth_fst_of_isPullback_consolidated469 hsq
    exact orderAt_comap T.base pB a A z
  exact monomialPrincipalization_isPullbackBlowupSequence_of_flat hGeom hinv T Y T.base q h E' hT hE2 hT2 hord


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomialPrincipalization
section

open CategoryTheory.Limits


def OrderAtBaseFieldChangeInvariance : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)),
      b ≫ T.structMap = pB →
      ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
        (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible →
        ∀ (Q : Scheme.{u}) (a : Q ⟶ B)
          (b' : Q ⟶ pullback T.structMap (specMapOfFieldHom T.base L f)),
          IsPullback a b' b (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) →
          ∀ (A : B.IdealSheafData) (y : ↥Q), orderAt (A.comap a) y = orderAt A (a y)

instance instSurjectivePullbackFstSpecMapField (k L : Type u) [Field k] [Field L]
    (f : k →+* L) (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)) :
    AlgebraicGeometry.Surjective (pullback.fst p (specMapOfFieldHom k L f)) :=
  inferInstance

section
variable (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (hord : OrderAtBaseFieldChangeInvariance.{u})
include hGeom hord

private theorem isPullbackBlowupSequence_monomialPrincipalization_baseChange_consolidated478 (T : MarkedIdealWithBoundary.{u})
    (hT : MonomialCenter.IsLocallyMonomialTriple T) (L : Type u) [Field L] [CharZero L]
    (f : T.base →+* L) (E' : List (T.baseChange L f).scheme.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E')
    (hT' : MonomialCenter.IsLocallyMonomialTriple ((T.baseChange L f).withBoundary E')) :
    IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
      (monomialPrincipalization hinv ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups
      (monomialPrincipalization hinv T).toSequenceOfBlowups := by
  have : Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    inferInstance
  have hord' : ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)),
      b ≫ T.structMap = pB →
      ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
        (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible →
        ∀ (Q : Scheme.{u}) (a : Q ⟶ B)
          (b' : Q ⟶ pullback T.structMap (specMapOfFieldHom T.base L f)),
          IsPullback a b' b (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) →
          ∀ (A : B.IdealSheafData) (z : ↥Q), orderAt (A.comap a) z = orderAt A (a z) :=
    hord T hT.valid L f
  exact monomialPrincipalization_isPullbackBlowupSequence_of_flat hGeom hinv T
    (pullback T.structMap (specMapOfFieldHom T.base L f)) L
    (pullback.snd T.structMap (specMapOfFieldHom T.base L f))
    (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) E' hT hE.symm hT' hord'

theorem isLocallyMonomialPrincipalization_monomialPrincipalization
    (P : ℕ → Prop) :
    MonomialCenter.IsLocallyMonomialPrincipalization P (monomialPrincipalization hinv) := by
  have hmonomial := isMonomialCasePrincipalization_monomialPrincipalization hGeom hinv
  have hne : ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i : ℕ, i < (monomialPrincipalization hinv T).length →
        (monomialPrincipalization hinv T).center i ≠ ⊤ := fun T hT i hi =>
    (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp
      (monomialPrincipalization_center_support_nonempty hGeom hinv T hT i hi)
  refine
    { center_subset_boundaryLocus := fun T hT _ => hmonomial.center_subset_boundaryLocus T hT
      cert := fun T hT _ => hmonomial.cert T hT
      base_change := ?_
      base_change_strict := ?_
      center_eq := fun T hT _ => hmonomial.center_eq T hT
      minLevel_ne_zero := fun T hT _ => hmonomial.minLevel_ne_zero T hT
      key_le := fun T hT _ => hmonomial.key_le T hT
      monomial_near := fun T hT _ => hmonomial.monomial_near T hT
      center_nonempty := fun T hT _ => hmonomial.center_nonempty T hT
      resolves := fun T hT _ => hmonomial.resolves T hT
      smooth_pullback := ?_
      smooth_pullback_strict := ?_
      trivial_of_coSupport_empty := fun T hT _ => hmonomial.trivial_of_coSupport_empty T hT }
  · intro T hT _ L instL instCZ f E' hE hT' _
    exact isPullbackBlowupSequence_monomialPrincipalization_baseChange_consolidated478 hGeom hinv hord T hT L f E' hE hT'
  · intro T hT _ L instL instCZ f E' hE hT' _
    exact (isPullbackBlowupSequence_monomialPrincipalization_baseChange_consolidated478 hGeom hinv hord T hT L f E' hE
      hT').isStrictPullback_of_surjective (hne T hT)
  · intro T hT _ Y q h hsmooth hq E' hE hT' _
    exact monomialPrincipalization_isPullbackBlowupSequence_of_smooth hGeom hinv T hT Y q h hq E' hE hT'
  · intro T hT _ Y q h hsmooth instSurj hq E' hE hT' _
    exact (monomialPrincipalization_isPullbackBlowupSequence_of_smooth hGeom hinv T hT Y q h hq E' hE
      hT').isStrictPullback_of_surjective (hne T hT)


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IteratedStrictTransformPullback
section



private theorem comap_eqToHom_of_eq_consolidated444 {F : ℕ → Scheme.{u}} (K : ∀ i : ℕ, (F i).IdealSheafData)
    {a b : ℕ} (h : a = b) : (K b).comap (eqToHom (congrArg F h)) = K a := by
  subst h
  exact AlgebraicGeometry.Scheme.IdealSheafData.comap_id _

private theorem smooth_of_isPullback_of_smooth_right_consolidated444 {A B C D : Scheme.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {h : B ⟶ D} {k : C ⟶ D} (sq : IsPullback f g h k) [Smooth k] :
    Smooth f :=
  MorphismProperty.of_isPullback (P := @Smooth) sq.flip inferInstance

private theorem isPullback_of_unique_consolidated444 {P A C B : Scheme.{u}} (e : P ⟶ A) [IsIso e]
    (ψ : A ⟶ C) (h : C ⟶ B) (φ : A ⟶ B) (hψ : ψ ≫ h = φ)
    (huniq : ∀ (T : Scheme.{u}) (v : T ⟶ A) (u : T ⟶ C), u ≫ h = v ≫ φ → u = v ≫ ψ) :
    IsPullback (e ≫ ψ) e h φ := by
  have w : (e ≫ ψ) ≫ h = e ≫ φ := by rw [Category.assoc, hψ]
  refine IsPullback.of_isLimit' ⟨w⟩
    (Limits.PullbackCone.IsLimit.mk w (fun s => s.snd ≫ inv e) ?_ ?_ ?_)
  · intro s
    have h1 := huniq s.pt s.snd s.fst s.condition
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    exact h1.symm
  · intro s
    simp
  · intro s m _ hm2
    rw [← hm2]
    simp

private theorem exists_lift_of_centers_comap_eq_top_consolidated444 {A B : Scheme.{u}} (φ : A ⟶ B) (c : SequenceOfBlowups B)
    (hinv : ∀ i : ℕ, i < c.length → ∀ ψ : A ⟶ c.schemeAt i,
      ψ ≫ c.projectionToBase i = φ → (c.center i).comap ψ = ⊤) :
    ∀ i : ℕ, i ≤ c.length → ∃ ψ : A ⟶ c.schemeAt i, ψ ≫ c.projectionToBase i = φ ∧
      ∀ (T : Scheme.{u}) (v : T ⟶ A) (u : T ⟶ c.schemeAt i), u ≫ c.projectionToBase i = v ≫ φ →
        u = v ≫ ψ := by
  intro i
  induction i with
  | zero =>
    intro _
    have : IsIso (c.projectionToBase 0) := by
      rw [SequenceOfBlowups.projectionToBase_zero]
      infer_instance
    refine ⟨φ ≫ CategoryTheory.inv (c.projectionToBase 0), by simp, ?_⟩
    intro T v u h
    rw [← Category.assoc, ← h]
    simp
  | succ m ih =>
    intro hm
    obtain ⟨ψ, hψ, hu⟩ := ih (Nat.le_of_lt hm)
    have hmlt : m < c.length := hm
    have htop : (c.center m).comap ψ = ⊤ := hinv m hmlt ψ hψ
    have hbl : Blowup.IsBlowupAlongIdealSheaf (c.transitionMapSucc m) (c.center m) := c.isBlowupAlongIdealSheaf_blowupMorphism m hmlt
    have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor ((c.center m).comap ψ) := by
      rw [htop]
      exact Blowup.isLocallyGeneratedByNonZeroDivisor_top _
    have h2 : c.transitionMapSucc m ≫ c.projectionToBase m = c.projectionToBase (m + 1) := by
      rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
      exact c.transitionMap_comp_projectionToBase _
    refine ⟨hbl.lift ψ hcart, ?_, ?_⟩
    · have h1 : hbl.lift ψ hcart ≫ c.transitionMapSucc m = ψ := hbl.lift_comp ψ hcart
      rw [← h2, ← Category.assoc, h1, hψ]
    · intro T v u h
      have hdown : u ≫ c.transitionMapSucc m = v ≫ ψ := by
        refine hu T v (u ≫ c.transitionMapSucc m) ?_
        rw [Category.assoc, h2]
        exact h
      have hcart2 : Blowup.IsLocallyGeneratedByNonZeroDivisor ((c.center m).comap (v ≫ ψ)) := by
        rw [Scheme.IdealSheafData.comap_comp, htop]
        exact Blowup.isLocallyGeneratedByNonZeroDivisor_comap_top v
      refine hbl.hom_ext_of_comp_eq hcart2 hdown ?_
      rw [Category.assoc, hbl.lift_comp ψ hcart]

section
variable {X X' : Scheme.{u}} {φ : X' ⟶ X} {t' : SequenceOfBlowups X'} {t : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ t' t) (K : ∀ i : ℕ, (t.schemeAt i).IdealSheafData) (hN : ∀ i : ℕ, i ≤ t.length → IsNoetherian (t.schemeAt i)) (hrec : ∀ i : ℕ, i < t.length → K (i + 1) = Blowup.strictTransform (t.transitionMapSucc i) (t.center i) (K i)) (j : ℕ) (hj : j ≤ t'.length)
include hN hrec

private theorem eq_comap_mapToEarlierScheme_succ_of_index_ne_consolidated444 (i : ℕ) (hi : i < c.idx j)
    (hmiss : ∀ j' : ℕ, j' < t'.length → c.idx j' ≠ i)
    (L : (t'.schemeAt j).IdealSheafData)
    (h : L = (K i).comap (c.mapToEarlierScheme j hj i (le_of_lt hi))) :
    L = (K (i + 1)).comap (c.mapToEarlierScheme j hj (i + 1) hi) := by
  have hilt : i < t.length := lt_of_lt_of_le hi (c.index_le_length j hj)
  have : IsNoetherian (t.schemeAt (i + 1)) := hN (i + 1) hilt
  have hcenter : ((t.center i).comap (t.transitionMapSucc i)).comap (c.mapToEarlierScheme j hj (i + 1) hi) = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_comp, ← c.mapToEarlierScheme_eq_comp_blowupMorphism j hj i hi]
    exact c.comap_center_mapToEarlierScheme_eq_top_of_unmatched j hj i hi hmiss
  rw [h, hrec i hilt,
    FunctorialResolution.EmbeddedResolution.strictTransform_comap_of_comap_center_eq_top (t.transitionMapSucc i) (t.center i) (K i)
      (c.mapToEarlierScheme j hj (i + 1) hi) hcenter,
    ← Scheme.IdealSheafData.comap_comp, ← c.mapToEarlierScheme_eq_comp_blowupMorphism j hj i hi]

private theorem eq_comap_mapToEarlierScheme_of_le_of_index_ne_consolidated444 (L : (t'.schemeAt j).IdealSheafData) (i₀ : ℕ) (hi₀ : i₀ ≤ c.idx j)
    (hmiss : ∀ i : ℕ, i₀ ≤ i → i < c.idx j → ∀ j' : ℕ, j' < t'.length → c.idx j' ≠ i)
    (h : L = (K i₀).comap (c.mapToEarlierScheme j hj i₀ hi₀)) :
    ∀ i : ℕ, i₀ ≤ i → ∀ hi : i ≤ c.idx j, L = (K i).comap (c.mapToEarlierScheme j hj i hi) := by
  intro i hii
  induction i, hii using Nat.le_induction with
  | base => intro _; exact h
  | succ p hp ih =>
    intro hi
    have hplt : p < c.idx j := hi
    exact eq_comap_mapToEarlierScheme_succ_of_index_ne_consolidated444 c K hN hrec j hj p hplt (hmiss p hp hplt) L (ih (le_of_lt hplt))


end

section
variable {X X' : Scheme.{u}} {φ : X' ⟶ X} {t' : SequenceOfBlowups X'} {t : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ t' t) [Flat φ] (K : ∀ i : ℕ, (t.schemeAt i).IdealSheafData) (K' : ∀ j : ℕ, (t'.schemeAt j).IdealSheafData) (hN : ∀ i : ℕ, i ≤ t.length → IsNoetherian (t.schemeAt i)) (hN' : ∀ j : ℕ, j ≤ t'.length → IsNoetherian (t'.schemeAt j))
include hN hN'

private theorem iteratedStrictTransform_succ_eq_comap_map_consolidated444 (hrec : ∀ i : ℕ, i < t.length → K (i + 1) = Blowup.strictTransform (t.transitionMapSucc i) (t.center i) (K i))
    (hrec' : ∀ j : ℕ, j < t'.length →
      K' (j + 1) = Blowup.strictTransform (t'.transitionMapSucc j) (t'.center j) (K' j))
    (j : ℕ) (hj : j < t'.length)
    (h : K' j = (K (c.idx j)).comap (c.map j (le_of_lt hj))) :
    K' (j + 1) = (K (c.idx (j + 1))).comap (c.map (j + 1) hj) := by
  have hidxlt : c.idx j < t.length := c.idx_lt j hj
  have : IsNoetherian (t.schemeAt (c.idx j + 1)) := hN (c.idx j + 1) hidxlt
  have : IsNoetherian (t'.schemeAt (j + 1)) := hN' (j + 1) hj
  have : Flat (c.map j (le_of_lt hj)) := c.flat_map j (le_of_lt hj)
  have hsq := c.isPullback_blowupMorphism j hj
  have key := FunctorialResolution.EmbeddedResolution.comap_strictTransform_of_flat_of_isLocallyNoetherian
    (t.transitionMapSucc (c.idx j)) (c.map j (le_of_lt hj)) (t'.transitionMapSucc j)
    (c.mapToEarlierScheme (j + 1) hj (c.idx j + 1) (c.idx_strictMono j hj)) hsq
    (t.center (c.idx j)) (K (c.idx j)) (t.isBlowupAlongIdealSheaf_blowupMorphism (c.idx j) hidxlt)
  have e1 : K (c.idx j + 1)
      = Blowup.strictTransform (t.transitionMapSucc (c.idx j)) (t.center (c.idx j)) (K (c.idx j)) :=
    hrec (c.idx j) hidxlt
  have e2 : K' (j + 1)
      = (K (c.idx j + 1)).comap (c.mapToEarlierScheme (j + 1) hj (c.idx j + 1) (c.idx_strictMono j hj)) := by
    rw [hrec' j hj, e1, key, h, c.center_comap j hj]
  have hmiss : ∀ i : ℕ, c.idx j + 1 ≤ i → i < c.idx (j + 1) →
      ∀ j' : ℕ, j' < t'.length → c.idx j' ≠ i :=
    fun i h1 h2 => c.index_ne_of_index_lt_of_lt_index_succ j hj i h1 h2
  have hfin := eq_comap_mapToEarlierScheme_of_le_of_index_ne_consolidated444 c K hN hrec (j + 1) hj (K' (j + 1)) (c.idx j + 1)
    (c.idx_strictMono j hj) hmiss e2 (c.idx (j + 1)) (c.idx_strictMono j hj) le_rfl
  rw [c.mapToEarlierScheme_index (j + 1) hj] at hfin
  exact hfin

private theorem iteratedStrictTransform_eq_comap_lastMap_of_sequence_consolidated444 (hzero : K' 0 = (K 0).comap (c.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _)))
    (hrec : ∀ i : ℕ, i < t.length → K (i + 1) = Blowup.strictTransform (t.transitionMapSucc i) (t.center i) (K i))
    (hrec' : ∀ j : ℕ, j < t'.length →
      K' (j + 1) = Blowup.strictTransform (t'.transitionMapSucc j) (t'.center j) (K' j)) :
    K' t'.length = (K t.length).comap c.lastMap := by
  have main : ∀ (j : ℕ) (hj : j ≤ t'.length), K' j = (K (c.idx j)).comap (c.map j hj) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have hmiss : ∀ i : ℕ, 0 ≤ i → i < c.idx 0 → ∀ j' : ℕ, j' < t'.length → c.idx j' ≠ i :=
        fun i _ h2 => c.index_ne_of_lt_index_zero i h2
      have hfin := eq_comap_mapToEarlierScheme_of_le_of_index_ne_consolidated444 c K hN hrec 0 hj (K' 0) 0 (Nat.zero_le _) hmiss hzero
        (c.idx 0) (Nat.zero_le _) le_rfl
      rw [c.mapToEarlierScheme_index 0 hj] at hfin
      exact hfin
    | succ m ih =>
      intro hj
      exact iteratedStrictTransform_succ_eq_comap_map_consolidated444 c K K' hN hN' hrec hrec' m hj (ih (Nat.le_of_lt hj))
  have hend := main t'.length le_rfl
  have hLastMap : c.lastMap = c.map t'.length le_rfl ≫ eqToHom (congrArg t.schemeAt c.idx_length) := rfl
  rw [hend, hLastMap, Scheme.IdealSheafData.comap_comp, comap_eqToHom_of_eq_consolidated444]
  exact c.idx_length


end

namespace SequenceOfBlowupsPullback

section

variable {X X' : Scheme.{u}} {φ : X' ⟶ X}

theorem smooth_lastMap {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s)
    [Smooth φ] : Smooth c.lastMap :=
  smooth_of_isPullback_of_smooth_right_consolidated444 c.isPullback_lastMap

end

section

variable {k k' : Type u} [Field k] [Field k']
variable {X Y : Scheme.{u}}
variable {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k')}
variable {g : Y ⟶ X}
variable {I : X.IdealSheafData} {I' : Y.IdealSheafData} {m : ℕ}
variable {E : List X.IdealSheafData} {E' : List Y.IdealSheafData}

theorem iteratedStrictTransform_eq_comap_lastMap {s : MarkedBlowupSequenceData p I m E} {s' : MarkedBlowupSequenceData q I' m E'}
    (d : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    [Flat g]
    (K : ∀ i : ℕ, (s.obj i).IdealSheafData) (K' : ∀ j : ℕ, (s'.obj j).IdealSheafData)
    (hN : ∀ i : ℕ, i ≤ s.length → IsNoetherian (s.obj i))
    (hN' : ∀ j : ℕ, j ≤ s'.length → IsNoetherian (s'.obj j))
    (hzero : K' 0 = (K 0).comap (d.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _)))
    (hrec : ∀ i : ℕ, i < s.length →
      K (i + 1) = Blowup.strictTransform (s.map i) (s.center i) (K i))
    (hrec' : ∀ j : ℕ, j < s'.length →
      K' (j + 1) = Blowup.strictTransform (s'.map j) (s'.center j) (K' j)) :
    K' s'.length = (K s.length).comap d.lastMap := by
  refine iteratedStrictTransform_eq_comap_lastMap_of_sequence_consolidated444 d K K' ?_ ?_ hzero ?_ ?_
  · intro i hi
    exact hN i hi
  · intro j hj
    exact hN' j hj
  · intro i hi
    rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, MarkedBlowupSequenceData.toMarkedSequence_center]
    exact hrec i hi
  · intro j hj
    rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, MarkedBlowupSequenceData.toMarkedSequence_center]
    exact hrec' j hj

end

end SequenceOfBlowupsPullback

theorem isPullback_of_length_zero_of_comap_center_eq_top {A B : Scheme.{u}} (φ : A ⟶ B)
    (n : SequenceOfBlowups A) (c : SequenceOfBlowups B) (hn : n.length = 0)
    (hinv : ∀ i : ℕ, i < c.length → ∀ ψ : A ⟶ c.schemeAt i,
      ψ ≫ c.projectionToBase i = φ → (c.center i).comap ψ = ⊤) :
    IsPullbackBlowupSequence φ n c := by
  obtain ⟨ψ, hψ, huniq⟩ := exists_lift_of_centers_comap_eq_top_consolidated444 φ c hinv c.length le_rfl
  have hlt : ∀ j : ℕ, ¬ j < n.length := by
    intro j hj
    rw [hn] at hj
    exact Nat.not_lt_zero j hj
  refine SequenceOfBlowupsPullback.isPullbackSequenceOfBlowups
    { idx := fun _ => c.length
      map := fun j _ => n.projectionToBase j ≫ ψ
      idx_length := rfl
      idx_lt := fun j hj => absurd hj (hlt j)
      idx_strictMono := fun j hj => absurd hj (hlt j)
      isPullback := ?_
      step := fun j hj => absurd hj (hlt j)
      center_comap := fun j hj => absurd hj (hlt j)
      center_ne_top := fun j hj => absurd hj (hlt j)
      omitted := ?_ }
  · intro j hj
    have hj0 : j = 0 := by
      rw [hn] at hj
      omega
    subst hj0
    have : IsIso (n.projectionToBase 0) := by
      rw [SequenceOfBlowups.projectionToBase_zero]
      infer_instance
    exact isPullback_of_unique_consolidated444 (n.projectionToBase 0) ψ (c.projectionToBase c.length) φ hψ huniq
  · intro i hi _ z hz x' hcon
    obtain ⟨ψi, hψi, huniqi⟩ := exists_lift_of_centers_comap_eq_top_consolidated444 φ c hinv i (le_of_lt hi)
    have htop : (c.center i).comap ψi = ⊤ := hinv i hi ψi hψi
    obtain ⟨w, hw1, hw2⟩ :=
      AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
        (f := c.projectionToBase i) (g := φ) (x := z) (y := x') hcon.symm
    have hfac : Limits.pullback.fst (c.projectionToBase i) φ
        = Limits.pullback.snd (c.projectionToBase i) φ ≫ ψi :=
      huniqi _ (Limits.pullback.snd (c.projectionToBase i) φ) (Limits.pullback.fst (c.projectionToBase i) φ)
        Limits.pullback.condition
    have hza : ψi.base ((Limits.pullback.snd (c.projectionToBase i) φ).base w) = z := by
      rw [← hw1]
      show (Limits.pullback.snd (c.projectionToBase i) φ ≫ ψi).base w
        = (Limits.pullback.fst (c.projectionToBase i) φ).base w
      rw [hfac]
    have key : (1 : ℕ∞) ≤ orderAt ((c.center i).comap ψi)
        ((Limits.pullback.snd (c.projectionToBase i) φ).base w) := by
      refine le_trans ?_ (orderAt_le_orderAt_comap ψi (c.center i) _)
      show (1 : ℕ∞) ≤ orderAt (c.center i) (ψi.base _)
      rw [hza]
      exact (one_le_orderAt_iff_mem_support _ _).2 hz
    rw [htop, orderAt_top] at key
    simp at key

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.RemoveUnitIdeals
section


section

theorem isPullback_of_length_eq_zero_of_length_eq_zero {X' X : Scheme.{u}} (φ : X' ⟶ X)
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (ht : t.length = 0) (hs : s.length = 0) :
    IsPullbackBlowupSequence φ t s := by
  refine isPullback_of_length_zero_of_comap_center_eq_top φ t s ht ?_
  intro i hi _ _
  exact absurd hi (by omega)

namespace MaxContactFunctoriality

def removeUnitIdeals {X : Scheme.{u}} (L : List X.IdealSheafData) : List X.IdealSheafData :=
  L.filter (fun D => @decide (D ≠ ⊤) (Classical.propDecidable _))

section
variable {X : Scheme.{u}}

private theorem removeUnitIdeals_cons_top_consolidated463 (L : List X.IdealSheafData) :
    removeUnitIdeals ((⊤ : X.IdealSheafData) :: L) = removeUnitIdeals L := by
  simp [removeUnitIdeals]

private theorem removeUnitIdeals_cons_of_ne_top_consolidated463 {D : X.IdealSheafData}
    (hD : D ≠ ⊤) (L : List X.IdealSheafData) :
    removeUnitIdeals (D :: L) = D :: removeUnitIdeals L := by
  simp [removeUnitIdeals, hD]


end

theorem removeUnitIdeals_map_comap_removeUnitIdeals {X Y : Scheme.{u}} (f : Y ⟶ X) (L : List X.IdealSheafData) :
    removeUnitIdeals (List.map (fun D => D.comap f) (removeUnitIdeals L)) =
      removeUnitIdeals (List.map (fun D => D.comap f) L) := by
  induction L with
  | nil => rfl
  | cons D L ih =>
    by_cases hD : D = ⊤
    · subst hD
      rw [removeUnitIdeals_cons_top_consolidated463, ih]
      simp only [List.map_cons, Scheme.IdealSheafData.comap_top]
      rw [removeUnitIdeals_cons_top_consolidated463]
    · rw [removeUnitIdeals_cons_of_ne_top_consolidated463 hD]
      simp only [List.map_cons]
      by_cases hD' : D.comap f = ⊤
      · rw [hD', removeUnitIdeals_cons_top_consolidated463, removeUnitIdeals_cons_top_consolidated463, ih]
      · rw [removeUnitIdeals_cons_of_ne_top_consolidated463 hD', removeUnitIdeals_cons_of_ne_top_consolidated463 hD', ih]

noncomputable abbrev smoothPullbackTriple (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme) :
    MarkedIdealWithBoundary.{u} :=
  (S.pullbackAlong X' (q ≫ S.structMap) q).withBoundary
    (removeUnitIdeals (S.pullbackAlong X' (q ≫ S.structMap) q).boundary)

def LoopCompatibleWithSmoothPullback (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment.{u}) : Prop :=
  ∀ (_hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u}) (_hin : OrderReduction.OrderReductionHypotheses.{u})
    (_hMC : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u})
    (_hAdm : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u}),
    (∀ a b : ℕ, a ≤ b → P b → P a) →
    ∀ B : PrincipalizationAssignment.{u}, (∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B) →
      IsBoundaryPositionInvariant P A →
      ∀ T T' : MarkedIdealWithBoundary.{u}, P T.krullDimSucc → P T'.krullDimSucc →
        ∀ S : MarkedIdealWithBoundary.{u}, S.IsAdmissible →
          (∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) →
          S.krullDimSucc ≤ T.krullDimSucc →
          ∀ H : S.scheme.IdealSheafData,
            (∀ [_inst : LocallyOfFiniteType S.structMap],
                IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H) →
            InStrictNormalCrossingPosition S.structMap [H] →
            (∀ D ∈ S.boundary, D ≠ ⊤) →
            ∀ {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [Smooth q],
              (smoothPullbackTriple S q).IsAdmissible →
              (smoothPullbackTriple S q).krullDimSucc ≤ T'.krullDimSucc →
              (∀ [_inst : LocallyOfFiniteType (smoothPullbackTriple S q).structMap],
                  IsMaxContactHypersurface (smoothPullbackTriple S q).base
                    (smoothPullbackTriple S q).structMap (smoothPullbackTriple S q).ideal
                    (smoothPullbackTriple S q).mult (H.comap q)) →
              InStrictNormalCrossingPosition (smoothPullbackTriple S q).structMap [H.comap q] →
              IsPullbackBlowupSequence q
                (MaxContactReduction.reduceAlongHypersurface hinv T' (lowerDimensionalFamily A T') (smoothPullbackTriple S q)
                  (H.comap q)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
                (MaxContactReduction.reduceAlongHypersurface hinv T (lowerDimensionalFamily A T) S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups

def TrivialOnEmptyOrderLocus (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment.{u}) : Prop :=
  ∀ T : MarkedIdealWithBoundary.{u}, OrderReductionHypotheses P T →
    ∀ {Y : Scheme.{u}} (g : Y ⟶ T.scheme) [Smooth g] (t : SequenceOfBlowups Y),
      t.length = 0 →
      orderAtLeastLocus (T.ideal.comap g) T.mult = (∅ : Set ↥Y) →
      IsPullbackBlowupSequence g t (maxContactPrincipalization hinv A T).toSequenceOfBlowups

noncomputable abbrev dropTrivialBoundaryPullback (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}}
    (qY : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    (E' : List Y.IdealSheafData) : MarkedIdealWithBoundary.{u} :=
  ((MaxContactReduction.dropTrivialBoundary T).pullbackAlong Y qY h).withBoundary (removeUnitIdeals E')

theorem reduceAlongHypersurface_isomorphic_of_isMaxContactHypersurface
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (_hshift : IsBoundaryPositionInvariant P A)
    (hstar0 : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u}) (hin : OrderReduction.OrderReductionHypotheses.{u})
    (hMC : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u})
    (hAdm : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u})
    (T : MarkedIdealWithBoundary.{u}) (hP : P T.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hv : S.IsAdmissible)
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hdim : S.krullDimSucc ≤ T.krullDimSucc)
    (H H' : S.scheme.IdealSheafData)
    (hH : ∀ [_inst : LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    (hH' : ∀ [_inst : LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H')
    (hH'snc : InStrictNormalCrossingPosition S.structMap [H']) :
    (MaxContactReduction.reduceAlongHypersurface hinv T (lowerDimensionalFamily A T) S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups.Isomorphic
      (MaxContactReduction.reduceAlongHypersurface hinv T (lowerDimensionalFamily A T) S H').toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have hsmid : Smooth (𝟙 S.scheme) := inferInstance
  have hflid : Flat (𝟙 S.scheme) := inferInstance
  have hsuid : AlgebraicGeometry.Surjective (𝟙 S.scheme) := inferInstance
  have hft2 : LocallyOfFiniteType S.structMap := hv.locallyOfFiniteType
  have hpb : LowerDimReductionPullback.pullbackTriple S (𝟙 S.scheme) = S := by
    simp [LowerDimReductionPullback.pullbackTriple, MarkedIdealWithBoundary.pullbackAlong]
  have hVpb : (LowerDimReductionPullback.pullbackTriple S (𝟙 S.scheme)).IsAdmissible := by rw [hpb]; exact hv
  have hdimpb : (LowerDimReductionPullback.pullbackTriple S (𝟙 S.scheme)).krullDimSucc ≤ T.krullDimSucc := by rw [hpb]; exact hdim
  have hHup : ∀ [inst : LocallyOfFiniteType
      (LowerDimReductionPullback.pullbackTriple S (𝟙 S.scheme)).structMap],
      IsMaxContactHypersurface (LowerDimReductionPullback.pullbackTriple S (𝟙 S.scheme)).base
        (LowerDimReductionPullback.pullbackTriple S (𝟙 S.scheme)).structMap
        (LowerDimReductionPullback.pullbackTriple S (𝟙 S.scheme)).ideal
        (LowerDimReductionPullback.pullbackTriple S (𝟙 S.scheme)).mult H := by
    intro inst
    exact isMaxContactHypersurface_of_triple_eq hpb inst hft2 H H HEq.rfl (@hH hft2)
  have hHupsnc : InStrictNormalCrossingPosition (LowerDimReductionPullback.pullbackTriple S (𝟙 S.scheme)).structMap [H] :=
    inStrictNormalCrossingPosition_of_triple_eq hpb [H] [H] HEq.rfl hHsnc
  have hA := BoundarySeparationBaseChange.isStrictPullbackBlowupSeq_reduceAlongHypersurface hstar0 hin hMC hAdm hinv P hmono A B hspec
    T hP S hv hord hdim H hH hHsnc (𝟙 S.scheme) hVpb hdimpb H hHup hHupsnc
  have hB := BoundarySeparationBaseChange.isStrictPullbackBlowupSeq_reduceAlongHypersurface hstar0 hin hMC hAdm hinv P hmono A B hspec
    T hP S hv hord hdim H' hH' hH'snc (𝟙 S.scheme) hVpb hdimpb H hHup hHupsnc
  exact hA.isomorphic_of_isomorphic hB (SequenceOfBlowups.isomorphic_refl _)

private theorem map_comap_map_comap_consolidated463 {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : List Z.IdealSheafData) :
    List.map (fun D => D.comap f) (List.map (fun D => D.comap g) L)
      = List.map (fun D => D.comap (f ≫ g)) L := by
  rw [List.map_map]
  exact List.map_congr_left (fun D _ => (Scheme.IdealSheafData.comap_comp D f g).symm)

private theorem dropTrivialBoundary_boundary_eq_removeUnitIdeals_consolidated463 (T : MarkedIdealWithBoundary.{u}) :
    (MaxContactReduction.dropTrivialBoundary T).boundary = removeUnitIdeals T.boundary := by
  rw [MaxContactReduction.dropTrivialBoundary_boundary]
  exact List.filter_congr (fun D _ => congrArg _ (Subsingleton.elim _ _))

private theorem removeUnitIdeals_eq_of_sameNontrivialBoundary_consolidated463 {X : Scheme.{u}} {L L' : List X.IdealSheafData}
    (hL : MarkedIdealWithBoundary.SameNontrivialBoundary L L') : removeUnitIdeals L = removeUnitIdeals L' := by
  have hdn : ∀ D : X.IdealSheafData,
      (@decide (D ≠ ⊤) (Classical.propDecidable _))
        = !(@decide (D = ⊤) (Classical.propDecidable _)) :=
    fun D => @decide_not (D = ⊤) (Classical.propDecidable _) (Classical.propDecidable _)
  have hL' : List.filter (fun D : X.IdealSheafData =>
        !(@decide (D = ⊤) (Classical.propDecidable _))) L
      = List.filter (fun D : X.IdealSheafData =>
        !(@decide (D = ⊤) (Classical.propDecidable _))) L' := hL
  have h1 : removeUnitIdeals L = List.filter (fun D : X.IdealSheafData =>
      !(@decide (D = ⊤) (Classical.propDecidable _))) L :=
    List.filter_congr (fun D _ => hdn D)
  have h2 : List.filter (fun D : X.IdealSheafData =>
      !(@decide (D = ⊤) (Classical.propDecidable _))) L' = removeUnitIdeals L' :=
    List.filter_congr (fun D _ => (hdn D).symm)
  exact h1.trans (hL'.trans h2)

private theorem removeUnitIdeals_map_comap_congr_consolidated463 {X Y : Scheme.{u}} (g : X ⟶ Y)
    {L L' : List Y.IdealSheafData}
    (hL : removeUnitIdeals L = removeUnitIdeals L') :
    removeUnitIdeals (List.map (fun D => D.comap g) L)
      = removeUnitIdeals (List.map (fun D => D.comap g) L') := by
  rw [← removeUnitIdeals_map_comap_removeUnitIdeals g L, ← removeUnitIdeals_map_comap_removeUnitIdeals g L', hL]

private theorem markedIdealWithBoundary_mk_congr_consolidated463 {k : Type u} [fk : Field k] {Z : Scheme.{u}}
    {p₁ p₂ : Z ⟶ Spec (CommRingCat.of k)} {I₁ I₂ : Z.IdealSheafData} {m₁ m₂ : ℕ}
    {b₁ b₂ : List Z.IdealSheafData}
    (hp : p₁ = p₂) (hI : I₁ = I₂) (hm : m₁ = m₂) (hb : b₁ = b₂) :
    ({ base := k, instField := fk, scheme := Z, structMap := p₁, ideal := I₁, mult := m₁,
        boundary := b₁ } : MarkedIdealWithBoundary.{u}) =
      { base := k, instField := fk, scheme := Z, structMap := p₂, ideal := I₂, mult := m₂,
        boundary := b₂ } := by
  subst hp; subst hI; subst hm; subst hb; rfl

theorem smoothPullbackTriple_coverTriple_eq (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}}
    (qY : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [Smooth h]
    (hq : h ≫ T.structMap = qY)
    (E' : List Y.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y qY h).boundary E')
    (htrimv : (MaxContactReduction.dropTrivialBoundary T).IsAdmissible)
    (hpbv : (dropTrivialBoundaryPullback T qY h E').IsAdmissible)
    [AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv)]
    [AlgebraicGeometry.Surjective
      (Limits.pullback.fst (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
        (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))] :
    smoothPullbackTriple (MaxContactCoverData.coverTriple (dropTrivialBoundaryPullback T qY h E') hpbv)
        (Limits.pullback.fst
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)) =
      smoothPullbackTriple (MaxContactCoverData.coverTriple (MaxContactReduction.dropTrivialBoundary T) htrimv)
        (Limits.pullback.snd
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)) := by
  subst hq
  have hcond :
      Limits.pullback.fst
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
        (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
      = Limits.pullback.snd
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
        MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv := Limits.pullback.condition
  have hcond2 :
      (Limits.pullback.fst
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
        MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv) ≫ h
      = Limits.pullback.snd
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
        MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv :=
    (Category.assoc _ _ _).trans hcond
  have hti : MaxContactCoverData.balancedTunedIdeal (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv
      = (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv).comap h := by
    have : Smooth T.structMap := htrimv.smooth
    have : LocallyOfFiniteType T.structMap := htrimv.locallyOfFiniteType
    have : LocallyOfFiniteType (h ≫ T.structMap) := hpbv.locallyOfFiniteType
    exact balancedTunedSheaf_comap T.base T.structMap h T.ideal T.mult
  have hsmC := congrArg (fun φ => φ ≫ T.structMap) hcond2
  have hsm :
      Limits.pullback.fst
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
        (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫
          (h ≫ T.structMap))
      = Limits.pullback.snd
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
        (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv ≫ T.structMap) :=
    (Category.assoc _ _ _).symm.trans
      ((Category.assoc _ _ _).symm.trans (hsmC.trans (Category.assoc _ _ _)))
  have i1 := congrArg (fun J => (J.comap
      (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv)).comap
      (Limits.pullback.fst
        (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
        (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))) hti
  have i2 :
      (((MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv).comap h).comap
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv)).comap
        (Limits.pullback.fst
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))
      = (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv).comap
        (Limits.pullback.fst
            (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
            (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)) :=
    (congrArg (fun J => J.comap
        (Limits.pullback.fst
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)))
      (Scheme.IdealSheafData.comap_comp
        (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv)
        (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv)
        h).symm).trans
      (Scheme.IdealSheafData.comap_comp
        (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv) _ _).symm
  have i3 := congrArg
      (fun φ => (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv).comap φ) hcond
  have i4 :
      (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv).comap
          (Limits.pullback.snd
              (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
              (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
            MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)
      = ((MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv).comap
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)).comap
        (Limits.pullback.snd
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)) :=
    Scheme.IdealSheafData.comap_comp
      (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv) _ _
  have hideal :
      ((MaxContactCoverData.balancedTunedIdeal (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv).comap
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv)).comap
        (Limits.pullback.fst
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))
      = ((MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv).comap
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)).comap
        (Limits.pullback.snd
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)) :=
    i1.trans (i2.trans (i3.trans i4))
  have hE'' : removeUnitIdeals E' = removeUnitIdeals (List.map (fun D => D.comap h) T.boundary) :=
    (removeUnitIdeals_eq_of_sameNontrivialBoundary_consolidated463 hE).symm
  have b1 :
      List.map (fun D => D.comap
          (Limits.pullback.fst
            (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
            (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)))
        (List.map (fun D => D.comap
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv))
          (removeUnitIdeals E'))
      = List.map (fun D => D.comap
          (Limits.pullback.fst
              (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
              (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
            MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv))
          (removeUnitIdeals E') := map_comap_map_comap_consolidated463 _ _ _
  have hb :
      removeUnitIdeals (List.map (fun D => D.comap
          (Limits.pullback.fst
            (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
            (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)))
        (List.map (fun D => D.comap
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv))
          (removeUnitIdeals E')))
      = removeUnitIdeals (List.map (fun D => D.comap
          (Limits.pullback.snd
            (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
            (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)))
        (List.map (fun D => D.comap
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))
          (MaxContactReduction.dropTrivialBoundary T).boundary)) :=
    calc removeUnitIdeals (List.map (fun D => D.comap
          (Limits.pullback.fst
            (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
            (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)))
        (List.map (fun D => D.comap
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv))
          (removeUnitIdeals E')))
        = removeUnitIdeals (List.map (fun D => D.comap
            (Limits.pullback.fst
                (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
                (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
              MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv))
            (removeUnitIdeals E')) := congrArg removeUnitIdeals b1
      _ = removeUnitIdeals (List.map (fun D => D.comap
            (Limits.pullback.fst
                (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
                (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
              MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv))
            E') := removeUnitIdeals_map_comap_removeUnitIdeals _ _
      _ = removeUnitIdeals (List.map (fun D => D.comap
            (Limits.pullback.fst
                (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
                (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
              MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv))
            (List.map (fun D => D.comap h) T.boundary)) := removeUnitIdeals_map_comap_congr_consolidated463 _ hE''
      _ = removeUnitIdeals (List.map (fun D => D.comap
            ((Limits.pullback.fst
                (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
                (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
              MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv) ≫ h))
            T.boundary) := congrArg removeUnitIdeals (map_comap_map_comap_consolidated463 _ h _)
      _ = removeUnitIdeals (List.map (fun D => D.comap
            (Limits.pullback.snd
                (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
                (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
              MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))
            T.boundary) :=
          congrArg (fun φ => removeUnitIdeals (List.map (fun D => D.comap φ) T.boundary)) hcond2
      _ = removeUnitIdeals (List.map (fun D => D.comap
            (Limits.pullback.snd
                (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
                (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
              MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))
            (removeUnitIdeals T.boundary)) := (removeUnitIdeals_map_comap_removeUnitIdeals _ _).symm
      _ = removeUnitIdeals (List.map (fun D => D.comap
            (Limits.pullback.snd
                (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
                (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
              MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))
            (MaxContactReduction.dropTrivialBoundary T).boundary) :=
          congrArg (fun L => removeUnitIdeals (List.map (fun D => D.comap
            (Limits.pullback.snd
                (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
                (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
              MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)) L))
            (dropTrivialBoundary_boundary_eq_removeUnitIdeals_consolidated463 T).symm
      _ = removeUnitIdeals (List.map (fun D => D.comap
            (Limits.pullback.snd
              (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
              (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)))
          (List.map (fun D => D.comap
            (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))
            (MaxContactReduction.dropTrivialBoundary T).boundary)) :=
          congrArg removeUnitIdeals (map_comap_map_comap_consolidated463 _ _ _).symm
  exact markedIdealWithBoundary_mk_congr_consolidated463 hsm hideal rfl hb

private theorem filter_eq_removeUnitIdeals_consolidated463 {X : Scheme.{u}}
    (p : X.IdealSheafData → Bool) (hp : ∀ D : X.IdealSheafData, p D = true ↔ D ≠ ⊤)
    (L : List X.IdealSheafData) : L.filter p = removeUnitIdeals L := by
  induction L with
  | nil => rfl
  | cons D L ih =>
    by_cases hD : D = ⊤
    · subst hD
      have hpf : p (⊤ : X.IdealSheafData) = false := by
        cases hb : p (⊤ : X.IdealSheafData) with
        | false => rfl
        | true => exact absurd ((hp ⊤).1 hb) (fun hne => hne rfl)
      rw [removeUnitIdeals_cons_top_consolidated463]
      simp [hpf, ih]
    · have hpt : p D = true := (hp D).2 hD
      rw [removeUnitIdeals_cons_of_ne_top_consolidated463 hD]
      simp [hpt, ih]

private theorem dropTrivialBoundary_eq_withBoundary_removeUnitIdeals_consolidated463 (S : MarkedIdealWithBoundary.{u}) :
    MaxContactReduction.dropTrivialBoundary S = S.withBoundary (removeUnitIdeals S.boundary) := by
  rw [MaxContactReduction.dropTrivialBoundary_def]
  exact congrArg S.withBoundary
    (filter_eq_removeUnitIdeals_consolidated463 _ (fun D => by simp) S.boundary)

private theorem ne_top_of_mem_removeUnitIdeals_consolidated463 {X : Scheme.{u}} (L : List X.IdealSheafData) :
    ∀ D ∈ removeUnitIdeals L, D ≠ ⊤ := by
  induction L with
  | nil =>
    intro D hD
    simp [removeUnitIdeals] at hD
  | cons C L ih =>
    intro D hD
    by_cases hC : C = ⊤
    · subst hC
      rw [removeUnitIdeals_cons_top_consolidated463] at hD
      exact ih D hD
    · rw [removeUnitIdeals_cons_of_ne_top_consolidated463 hC] at hD
      rcases List.mem_cons.1 hD with h1 | h1
      · subst h1; exact hC
      · exact ih D h1

private theorem isStrictPullback_coverMarkedSequence_of_eq_of_heq_consolidated463 (hinv : ComapIsoInvariance.{u})
    (A : ℕ → PrincipalizationAssignment.{u}) {S₁ S₂ : MarkedIdealWithBoundary.{u}} (hS : S₁ = S₂)
    (hv₁ : S₁.IsAdmissible) (hv₂ : S₂.IsAdmissible) (e₁ : BlowupSequenceData S₁.scheme) (e₂ : BlowupSequenceData S₂.scheme)
    (hee : HEq e₁ e₂)
    (hd : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap S₁ hv₁)
        (MaxContactCoverData.coverMarkedBlowupData S₁ hv₁ hinv (lowerDimensionalFamily A S₁)).toSequenceOfBlowups e₁.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap S₂ hv₂)
        (MaxContactCoverData.coverMarkedBlowupData S₂ hv₂ hinv (lowerDimensionalFamily A S₂)).toSequenceOfBlowups e₂.toSequenceOfBlowups := by
  subst hS
  cases hee
  exact hd

private theorem orderReductionHypotheses_of_eq_consolidated463 {P : ℕ → Prop} {S₁ S₂ : MarkedIdealWithBoundary.{u}}
    (hS : S₁ = S₂) (hy : OrderReductionHypotheses P S₁) : OrderReductionHypotheses P S₂ := by
  subst hS
  exact hy

section
variable {X Y : Scheme.{u}} (h : Y ⟶ X)

private theorem isPullback_of_faithfullyFlat_covers_consolidated463 [Flat h] {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ X) (c₂ : C₂ ⟶ Y)
    (hf₁ : Flat c₁) (hs₁ : AlgebraicGeometry.Surjective c₁)
    (hf₂ : Flat c₂) (hs₂ : AlgebraicGeometry.Surjective c₂)
    (t₁ : SequenceOfBlowups C₁) (t₂ : SequenceOfBlowups C₂) (s₁ : SequenceOfBlowups X) (s₂ : SequenceOfBlowups Y)
    (hd₁ : IsStrictPullbackBlowupSeq c₁ t₁ s₁) (hd₂ : IsStrictPullbackBlowupSeq c₂ t₂ s₂)
    (hne₂ : ∀ i, i < t₂.length → t₂.center i ≠ ⊤)
    (hcomp : ∀ v v' : SequenceOfBlowups (Limits.pullback (c₂ ≫ h) c₁),
      IsStrictPullbackBlowupSeq (Limits.pullback.fst (c₂ ≫ h) c₁) v t₂ →
      IsStrictPullbackBlowupSeq (Limits.pullback.snd (c₂ ≫ h) c₁) v' t₁ →
      v.withoutIsoBlowups.Isomorphic v'.withoutIsoBlowups) :
    IsPullbackBlowupSequence h s₂ s₁ := by
  have := hf₁
  have := hs₁
  have := hf₂
  have := hs₂
  have hfc : Flat (c₂ ≫ h) :=
    CategoryTheory.MorphismProperty.comp_mem _ c₂ h inferInstance inferInstance
  have hflfst : Flat (Limits.pullback.fst (c₂ ≫ h) c₁) := inferInstance
  have hsufst : AlgebraicGeometry.Surjective (Limits.pullback.fst (c₂ ≫ h) c₁) := inferInstance
  have hw : IsStrictPullbackBlowupSeq h (s₁.baseChange h) s₁ :=
    isStrictPullbackSequenceOfBlowups_baseChange s₁ h
  refine (IsStrictPullbackBlowupSeq.isPullbackSequenceOfBlowups_withoutIsoBlowups hw).of_isomorphic ?_
  have hu : IsStrictPullbackBlowupSeq (c₂ ≫ h) (s₁.baseChange (c₂ ≫ h)) s₁ :=
    isStrictPullbackSequenceOfBlowups_baseChange s₁ (c₂ ≫ h)
  have hu' : IsStrictPullbackBlowupSeq c₂ (s₁.baseChange (c₂ ≫ h)) (s₁.baseChange h) :=
    hu.baseChange_of_comp
  have hv : IsStrictPullbackBlowupSeq (Limits.pullback.fst (c₂ ≫ h) c₁)
      ((s₁.baseChange (c₂ ≫ h)).baseChange (Limits.pullback.fst (c₂ ≫ h) c₁))
      (s₁.baseChange (c₂ ≫ h)) := isStrictPullbackSequenceOfBlowups_baseChange _ _
  have hv2 : IsStrictPullbackBlowupSeq (Limits.pullback.fst (c₂ ≫ h) c₁)
      (t₂.baseChange (Limits.pullback.fst (c₂ ≫ h) c₁)) t₂ :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  have hv1 : IsStrictPullbackBlowupSeq (Limits.pullback.snd (c₂ ≫ h) c₁)
      (t₁.baseChange (Limits.pullback.snd (c₂ ≫ h) c₁)) t₁ :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  have e1 : IsStrictPullbackBlowupSeq (Limits.pullback.snd (c₂ ≫ h) c₁ ≫ c₁)
      ((s₁.baseChange (c₂ ≫ h)).baseChange (Limits.pullback.fst (c₂ ≫ h) c₁)) s₁ :=
    (hv.comp hu).congr_hom Limits.pullback.condition
  have e2 : IsStrictPullbackBlowupSeq (Limits.pullback.snd (c₂ ≫ h) c₁ ≫ c₁)
      (t₁.baseChange (Limits.pullback.snd (c₂ ≫ h) c₁)) s₁ := hv1.comp hd₁
  have e3 : ((s₁.baseChange (c₂ ≫ h)).baseChange
      (Limits.pullback.fst (c₂ ≫ h) c₁)).Isomorphic
      (t₁.baseChange (Limits.pullback.snd (c₂ ≫ h) c₁)) := e1.isomorphic e2
  have hmid : (s₁.baseChange (c₂ ≫ h)).withoutIsoBlowups.Isomorphic t₂.withoutIsoBlowups :=
    IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic hv.withoutIsoBlowups hv2.withoutIsoBlowups
      ((e3.withoutIsoBlowups).trans (hcomp _ _ hv2 hv1).symm)
  have hfin : (s₁.baseChange h).withoutIsoBlowups.Isomorphic s₂.withoutIsoBlowups :=
    IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic hu'.withoutIsoBlowups hd₂.withoutIsoBlowups hmid
  exact hfin.trans (SequenceOfBlowups.withoutIsoBlowups_isomorphic_self s₂
    (fun i hi => hd₂.center_ne_top_of_forall_center_ne_top hne₂ i hi))

private theorem smooth_pullback_fst_snd_and_surjective_fst_consolidated463 [Smooth h]
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ X) (c₂ : C₂ ⟶ Y)
    [Smooth c₁] [Smooth c₂]
    [AlgebraicGeometry.Surjective c₁] :
    Smooth (Limits.pullback.fst (c₂ ≫ h) c₁) ∧
      Smooth (Limits.pullback.snd (c₂ ≫ h) c₁) ∧
        AlgebraicGeometry.Surjective (Limits.pullback.fst (c₂ ≫ h) c₁) := by
  have hcc : Smooth (c₂ ≫ h) := inferInstance
  exact ⟨inferInstance, inferInstance, inferInstance⟩


end

private theorem smoothPullbackTriple_eq_dropTrivialBoundary_consolidated463 (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}}
    (q : X' ⟶ S.scheme) :
    smoothPullbackTriple S q = MaxContactReduction.dropTrivialBoundary (S.pullbackAlong X' (q ≫ S.structMap) q) :=
  (dropTrivialBoundary_eq_withBoundary_removeUnitIdeals_consolidated463 (S.pullbackAlong X' (q ≫ S.structMap) q)).symm

private theorem boundary_ne_top_of_eq_consolidated463 {S₁ S₂ : MarkedIdealWithBoundary.{u}} (hS : S₁ = S₂)
    (hb : ∀ D ∈ S₁.boundary, D ≠ ⊤) : ∀ D ∈ S₂.boundary, D ≠ ⊤ := by
  subst hS
  exact hb

private theorem coverTriple_boundary_ne_top_consolidated463 (S : MarkedIdealWithBoundary.{u}) (hv : S.IsAdmissible)
    [AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap S hv)]
    (hb : ∀ D ∈ S.boundary, D ≠ ⊤) :
    ∀ D ∈ (MaxContactCoverData.coverTriple S hv).boundary, D ≠ ⊤ := by
  refine boundary_ne_top_of_eq_consolidated463 (MaxContactOpenCover.coverTriple_eq_tunedTriple_pullbackAlong S hv).symm ?_
  intro D hD
  have hD2 : D ∈ List.map (fun D₀ : S.scheme.IdealSheafData =>
      D₀.comap (MaxContactCoverData.coverMap S hv)) S.boundary := hD
  obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD2
  exact (comap_ne_top_iff_of_surjective (MaxContactCoverData.coverMap S hv) D₀).2 (hb D₀ hD₀)

private theorem orderAt_coverTriple_le_mult_consolidated463 (hstar0 : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u})
    (horder : CoSupportTunedSheafEqAndOrderLE.{u}) (S : MarkedIdealWithBoundary.{u}) (hv : S.IsAdmissible)
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hmax : MaxOrderEq S.ideal S.mult) :
    ∀ x : ↥(MaxContactCoverData.coverTriple S hv).scheme,
      orderAt (MaxContactCoverData.coverTriple S hv).ideal x
        ≤ ((MaxContactCoverData.coverTriple S hv).mult : ℕ∞) := by
  have hgood := MaxContactCoverData.isMaxContactCover_chosenCoverData S hv (hstar0.exists_goodCover S hv hord)
  have hcv : (MaxContactCoverData.coverTriple S hv).IsAdmissible :=
    hstar0.coverTriple_valid S hv hord hgood
  have hsm : Smooth S.structMap := hv.smooth
  have hft : LocallyOfFiniteType S.structMap := hv.locallyOfFiniteType
  have hcz : CharZero S.base := hv.charZero
  have hnoe : IsNoetherianRing S.base := inferInstance
  have hsmc : Smooth (MaxContactCoverData.coverMap S hv) :=
    MaxContactCoverData.smooth_coverMap_of_isAdmissible S hv
  have hs : 1 ≤ MaxContactCoverData.tunedMult S := hcv.one_le_mult
  have hOL : OrderLE (MaxContactCoverData.balancedTunedIdeal S hv) (MaxContactCoverData.tunedMult S) :=
    horder.orderLE S.base S.scheme S.structMap S.ideal S.mult hv.one_le_mult hmax
      (MaxContactCoverData.tunedMult S) hs
  have hOL' : ∀ y : ↥S.scheme, orderAt (MaxContactCoverData.balancedTunedIdeal S hv) y
      ≤ ((MaxContactCoverData.tunedMult S : ℕ) : ℕ∞) := hOL
  intro x
  show orderAt ((MaxContactCoverData.balancedTunedIdeal S hv).comap (MaxContactCoverData.coverMap S hv)) x
      ≤ ((MaxContactCoverData.tunedMult S : ℕ) : ℕ∞)
  rw [orderAt_comap S.base S.structMap (MaxContactCoverData.coverMap S hv)
    (MaxContactCoverData.balancedTunedIdeal S hv) x]
  exact hOL' _

section
variable (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B) (hshift : IsBoundaryPositionInvariant P A) (hstar0 : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u}) (hin : OrderReduction.OrderReductionHypotheses.{u}) (hMC : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u}) (hAdm : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u}) (hdel : LoopCompatibleWithSmoothPullback hinv P A)
include hmono hspec hshift hstar0 hin hMC hAdm hdel

private theorem withoutIsoBlowups_isomorphic_of_smoothPullbackTriple_eq_consolidated463
    (htv : DropTrivialBoundaryAdmissible.{u})
    (S₁ S₂ : MarkedIdealWithBoundary.{u}) (hv₁ : S₁.IsAdmissible) (hv₂ : S₂.IsAdmissible)
    (hP₁ : P S₁.krullDimSucc) (hP₂ : P S₂.krullDimSucc)
    (hord₁ : ∀ x : ↥S₁.scheme, orderAt S₁.ideal x ≤ (S₁.mult : ℕ∞))
    (hord₂ : ∀ x : ↥S₂.scheme, orderAt S₂.ideal x ≤ (S₂.mult : ℕ∞))
    (_hcsn₁ : (orderAtLeastLocus S₁.ideal S₁.mult).Nonempty)
    (_hcsn₂ : (orderAtLeastLocus S₂.ideal S₂.mult).Nonempty)
    (hbd₁ : ∀ D ∈ S₁.boundary, D ≠ ⊤) (hbd₂ : ∀ D ∈ S₂.boundary, D ≠ ⊤)
    (hsuc₁ : AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap S₁ hv₁))
    (hsuc₂ : AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap S₂ hv₂))
    (hcord₁ : ∀ x : ↥(MaxContactCoverData.coverTriple S₁ hv₁).scheme,
      orderAt (MaxContactCoverData.coverTriple S₁ hv₁).ideal x
        ≤ ((MaxContactCoverData.coverTriple S₁ hv₁).mult : ℕ∞))
    (hcord₂ : ∀ x : ↥(MaxContactCoverData.coverTriple S₂ hv₂).scheme,
      orderAt (MaxContactCoverData.coverTriple S₂ hv₂).ideal x
        ≤ ((MaxContactCoverData.coverTriple S₂ hv₂).mult : ℕ∞))
    {Q : Scheme.{u}}
    (π₁ : Q ⟶ (MaxContactCoverData.coverTriple S₁ hv₁).scheme)
    (π₂ : Q ⟶ (MaxContactCoverData.coverTriple S₂ hv₂).scheme)
    (hsmπ₁ : Smooth π₁) (hsmπ₂ : Smooth π₂)
    (hdeleq : smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂
      = smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁)
    (hqc : QuasiCompact
      (π₁ ≫ (MaxContactCoverData.coverTriple S₁ hv₁).structMap))
    (hdim : (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).krullDimSucc ≤ S₂.krullDimSucc)
    (v v' : SequenceOfBlowups Q)
    (hvv : IsStrictPullbackBlowupSeq π₂ v
      (MaxContactCoverData.coverMarkedBlowupData S₂ hv₂ hinv (lowerDimensionalFamily A S₂)).toSequenceOfBlowups)
    (hvv' : IsStrictPullbackBlowupSeq π₁ v'
      (MaxContactCoverData.coverMarkedBlowupData S₁ hv₁ hinv (lowerDimensionalFamily A S₁)).toSequenceOfBlowups) :
    v.withoutIsoBlowups.Isomorphic v'.withoutIsoBlowups := by
  have := hqc
  have := hsuc₁
  have := hsuc₂
  have := hsmπ₁
  have := hsmπ₂
  have hgood₁ := MaxContactCoverData.isMaxContactCover_chosenCoverData S₁ hv₁ (hstar0.exists_goodCover S₁ hv₁ hord₁)
  have hgood₂ := MaxContactCoverData.isMaxContactCover_chosenCoverData S₂ hv₂ (hstar0.exists_goodCover S₂ hv₂ hord₂)
  have hcv₁ : (MaxContactCoverData.coverTriple S₁ hv₁).IsAdmissible :=
    hstar0.coverTriple_valid S₁ hv₁ hord₁ hgood₁
  have hcv₂ : (MaxContactCoverData.coverTriple S₂ hv₂).IsAdmissible :=
    hstar0.coverTriple_valid S₂ hv₂ hord₂ hgood₂
  have : Smooth (MaxContactCoverData.coverTriple S₁ hv₁).structMap := hcv₁.smooth
  have : Smooth (MaxContactCoverData.coverTriple S₂ hv₂).structMap := hcv₂.smooth
  have : LocallyOfFiniteType
      (MaxContactCoverData.coverTriple S₁ hv₁).structMap := hcv₁.locallyOfFiniteType
  have : LocallyOfFiniteType
      (MaxContactCoverData.coverTriple S₂ hv₂).structMap := hcv₂.locallyOfFiniteType
  have : CharZero (MaxContactCoverData.coverTriple S₁ hv₁).base := hcv₁.charZero
  have : CharZero (MaxContactCoverData.coverTriple S₂ hv₂).base := hcv₂.charZero
  have hm₁ : 1 ≤ (MaxContactCoverData.coverTriple S₁ hv₁).mult := hcv₁.one_le_mult
  have hm₂ : 1 ≤ (MaxContactCoverData.coverTriple S₂ hv₂).mult := hcv₂.one_le_mult
  have hcdim₁ : (MaxContactCoverData.coverTriple S₁ hv₁).krullDimSucc ≤ S₁.krullDimSucc :=
    hstar0.coverTriple_dim_le S₁ hv₁
  have hcdim₂ : (MaxContactCoverData.coverTriple S₂ hv₂).krullDimSucc ≤ S₂.krullDimSucc :=
    hstar0.coverTriple_dim_le S₂ hv₂
  have hcadm₁ : ∀ [inst : LocallyOfFiniteType
      (MaxContactCoverData.coverTriple S₁ hv₁).structMap],
      IsMaxContactHypersurface (MaxContactCoverData.coverTriple S₁ hv₁).base
        (MaxContactCoverData.coverTriple S₁ hv₁).structMap
        (MaxContactCoverData.coverTriple S₁ hv₁).ideal
        (MaxContactCoverData.coverTriple S₁ hv₁).mult
        (MaxContactCoverData.coverMaxContactIdeal S₁ hv₁) := by
    intro _inst
    exact hstar0.coverContact_admissible S₁ hv₁ hgood₁
  have hcadm₂ : ∀ [inst : LocallyOfFiniteType
      (MaxContactCoverData.coverTriple S₂ hv₂).structMap],
      IsMaxContactHypersurface (MaxContactCoverData.coverTriple S₂ hv₂).base
        (MaxContactCoverData.coverTriple S₂ hv₂).structMap
        (MaxContactCoverData.coverTriple S₂ hv₂).ideal
        (MaxContactCoverData.coverTriple S₂ hv₂).mult
        (MaxContactCoverData.coverMaxContactIdeal S₂ hv₂) := by
    intro _inst
    exact hstar0.coverContact_admissible S₂ hv₂ hgood₂
  have hcsnc₁ : InStrictNormalCrossingPosition (MaxContactCoverData.coverTriple S₁ hv₁).structMap
      [MaxContactCoverData.coverMaxContactIdeal S₁ hv₁] := hstar0.coverContact_snc S₁ hv₁ hgood₁
  have hcsnc₂ : InStrictNormalCrossingPosition (MaxContactCoverData.coverTriple S₂ hv₂).structMap
      [MaxContactCoverData.coverMaxContactIdeal S₂ hv₂] := hstar0.coverContact_snc S₂ hv₂ hgood₂
  have hcbd₁ : ∀ D ∈ (MaxContactCoverData.coverTriple S₁ hv₁).boundary, D ≠ ⊤ :=
    coverTriple_boundary_ne_top_consolidated463 S₁ hv₁ hbd₁
  have hcbd₂ : ∀ D ∈ (MaxContactCoverData.coverTriple S₂ hv₂).boundary, D ≠ ⊤ :=
    coverTriple_boundary_ne_top_consolidated463 S₂ hv₂ hbd₂
  have hpbv₁ : ((MaxContactCoverData.coverTriple S₁ hv₁).pullbackAlong Q
      (π₁ ≫ (MaxContactCoverData.coverTriple S₁ hv₁).structMap) π₁).IsAdmissible :=
    hin.valid_pullbackAlong (MaxContactCoverData.coverTriple S₁ hv₁) hcv₁ Q
      (π₁ ≫ (MaxContactCoverData.coverTriple S₁ hv₁).structMap) π₁ rfl
  have hdv₁ : (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).IsAdmissible := by
    rw [smoothPullbackTriple_eq_dropTrivialBoundary_consolidated463]
    exact htv _ hpbv₁
  have hdv₂ : (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂).IsAdmissible := by
    rw [hdeleq]
    exact hdv₁
  have hdim₂ : (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂).krullDimSucc ≤ S₂.krullDimSucc := by
    rw [hdeleq]
    exact hdim
  have hdord₁ : ∀ x : ↥(smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).scheme,
      orderAt (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).ideal x
        ≤ ((smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).mult : ℕ∞) :=
    fun x => BoundarySeparationBaseChange.orderAt_pullbackTriple_le_mult (MaxContactCoverData.coverTriple S₁ hv₁) π₁ hcv₁ hcord₁ x
  have hdadm₁ : ∀ [inst : LocallyOfFiniteType
      (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).structMap],
      IsMaxContactHypersurface (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).base
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).structMap
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).ideal
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).mult
        ((MaxContactCoverData.coverMaxContactIdeal S₁ hv₁).comap π₁) := by
    intro inst
    have : LocallyOfFiniteType
        (π₁ ≫ (MaxContactCoverData.coverTriple S₁ hv₁).structMap) := inst
    exact hAdm (MaxContactCoverData.coverTriple S₁ hv₁).base
      (MaxContactCoverData.coverTriple S₁ hv₁).scheme (MaxContactCoverData.coverTriple S₁ hv₁).structMap
      Q π₁ (MaxContactCoverData.coverTriple S₁ hv₁).ideal (MaxContactCoverData.coverTriple S₁ hv₁).mult
      hm₁ (MaxContactCoverData.coverMaxContactIdeal S₁ hv₁) hcadm₁
  have hdadm₂ : ∀ [inst : LocallyOfFiniteType
      (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂).structMap],
      IsMaxContactHypersurface (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂).base
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂).structMap
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂).ideal
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂).mult
        ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂) := by
    intro inst
    have : LocallyOfFiniteType
        (π₂ ≫ (MaxContactCoverData.coverTriple S₂ hv₂).structMap) := inst
    exact hAdm (MaxContactCoverData.coverTriple S₂ hv₂).base
      (MaxContactCoverData.coverTriple S₂ hv₂).scheme (MaxContactCoverData.coverTriple S₂ hv₂).structMap
      Q π₂ (MaxContactCoverData.coverTriple S₂ hv₂).ideal (MaxContactCoverData.coverTriple S₂ hv₂).mult
      hm₂ (MaxContactCoverData.coverMaxContactIdeal S₂ hv₂) hcadm₂
  have hdsnc₁ : InStrictNormalCrossingPosition (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).structMap
      [(MaxContactCoverData.coverMaxContactIdeal S₁ hv₁).comap π₁] :=
    inStrictNormalCrossingPosition_comap_singleton (MaxContactCoverData.coverTriple S₁ hv₁).structMap π₁
      (MaxContactCoverData.coverMaxContactIdeal S₁ hv₁) hcsnc₁
  have hdsnc₂ : InStrictNormalCrossingPosition (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂).structMap
      [(MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂] :=
    inStrictNormalCrossingPosition_comap_singleton (MaxContactCoverData.coverTriple S₂ hv₂).structMap π₂
      (MaxContactCoverData.coverMaxContactIdeal S₂ hv₂) hcsnc₂
  have hA : IsPullbackBlowupSequence π₁
      (MaxContactReduction.reduceAlongHypersurface hinv S₂ (lowerDimensionalFamily A S₂)
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁)
        ((MaxContactCoverData.coverMaxContactIdeal S₁ hv₁).comap π₁)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactCoverData.coverMarkedBlowupData S₁ hv₁ hinv (lowerDimensionalFamily A S₁)).toSequenceOfBlowups :=
    hdel hstar0 hin hMC hAdm hmono B hspec hshift S₁ S₂ hP₁ hP₂
      (MaxContactCoverData.coverTriple S₁ hv₁) hcv₁ hcord₁ hcdim₁
      (MaxContactCoverData.coverMaxContactIdeal S₁ hv₁) hcadm₁ hcsnc₁ hcbd₁ π₁ hdv₁ hdim hdadm₁ hdsnc₁
  have hB : IsPullbackBlowupSequence π₂
      (MaxContactReduction.reduceAlongHypersurface hinv S₂ (lowerDimensionalFamily A S₂)
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂)
        ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactCoverData.coverMarkedBlowupData S₂ hv₂ hinv (lowerDimensionalFamily A S₂)).toSequenceOfBlowups :=
    hdel hstar0 hin hMC hAdm hmono B hspec hshift S₂ S₂ hP₂ hP₂
      (MaxContactCoverData.coverTriple S₂ hv₂) hcv₂ hcord₂ hcdim₂
      (MaxContactCoverData.coverMaxContactIdeal S₂ hv₂) hcadm₂ hcsnc₂ hcbd₂ π₂ hdv₂ hdim₂ hdadm₂ hdsnc₂
  have hu : (MaxContactReduction.reduceAlongHypersurface hinv S₂ (lowerDimensionalFamily A S₂)
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂)
        ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      = (MaxContactReduction.reduceAlongHypersurface hinv S₂ (lowerDimensionalFamily A S₂)
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁)
        ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂)).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
    eq_of_heq (reduceAlongHypersurface_toSequenceOfBlowups_heq hinv S₂ (lowerDimensionalFamily A S₂) hdeleq
      ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂)
      ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂) HEq.rfl)
  have hdsnc₂' : InStrictNormalCrossingPosition (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).structMap
      [(MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂] :=
    inStrictNormalCrossingPosition_of_triple_eq hdeleq.symm
      [(MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂]
      [(MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂] HEq.rfl hdsnc₂
  have hdadm₂' : ∀ [inst : LocallyOfFiniteType
      (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).structMap],
      IsMaxContactHypersurface (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).base
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).structMap
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).ideal
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).mult
        ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂) := by
    intro inst
    have hft2 : LocallyOfFiniteType
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂).structMap := by
      rw [hdeleq]
      exact inst
    exact isMaxContactHypersurface_of_triple_eq hdeleq.symm inst hft2
      ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂)
      ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂) HEq.rfl (@hdadm₂ hft2)
  have hmid : (MaxContactReduction.reduceAlongHypersurface hinv S₂ (lowerDimensionalFamily A S₂)
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁)
        ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂)).toMarkedSequenceOfBlowups.toSequenceOfBlowups.Isomorphic
      (MaxContactReduction.reduceAlongHypersurface hinv S₂ (lowerDimensionalFamily A S₂)
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁)
        ((MaxContactCoverData.coverMaxContactIdeal S₁ hv₁).comap π₁)).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
    reduceAlongHypersurface_isomorphic_of_isMaxContactHypersurface hinv P hmono A B hspec hshift hstar0
      hin hMC hAdm
      S₂ hP₂ (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁) hdv₁ hdord₁ hdim
      ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂)
      ((MaxContactCoverData.coverMaxContactIdeal S₁ hv₁).comap π₁)
      hdadm₂' hdsnc₂' hdadm₁ hdsnc₁
  have e₂ := IsPullbackBlowupSequence.isomorphic hvv.isPullbackSequenceOfBlowups_withoutIsoBlowups hB
  have e₁ := IsPullbackBlowupSequence.isomorphic hvv'.isPullbackSequenceOfBlowups_withoutIsoBlowups hA
  rw [hu] at e₂
  exact e₂.trans (hmid.trans e₁.symm)

theorem maxContactPrincipalization_isPullbackBlowupSequence_of_smooth
    (hvan : TrivialOnEmptyOrderLocus hinv P A)
    (hsf : CoverSequenceProperties hinv P A) (hmd : MarkingDescends hinv P A)
    (hff : CoverFaithfullyFlat.{u} P) (htv : DropTrivialBoundaryAdmissible.{u}) (htm : MarkedOfMarkedDropTrivialBoundary.{u})
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hP : P T.krullDimSucc)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [Smooth h] [Flat h]
    (hq : h ≫ T.structMap = qY)
    (E' : List Y.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y qY h).boundary E')
    (hv' : ((T.pullbackAlong Y qY h).withBoundary E').IsAdmissible)
    (hP' : P ((T.pullbackAlong Y qY h).withBoundary E').krullDimSucc)
    (htrimv : (MaxContactReduction.dropTrivialBoundary T).IsAdmissible)
    (hpbv : (dropTrivialBoundaryPullback T qY h E').IsAdmissible)
    (hqc : QuasiCompact
      (Limits.pullback.snd (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
        (MaxContactCoverData.coverTriple (MaxContactReduction.dropTrivialBoundary T) htrimv).structMap))
    (hdimfp : krullDimSucc
        (Limits.pullback (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)) ≤
      (T.pullbackAlong Y qY h).krullDimSucc) :
    IsPullbackBlowupSequence h
      (maxContactPrincipalization hinv A ((T.pullbackAlong Y qY h).withBoundary E')).toSequenceOfBlowups
      (maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
  have horder : CoSupportTunedSheafEqAndOrderLE.{u} :=
    hstar0.tuning.coSupport_tunedSheaf_eq_and_orderLE
  have hord₂ : ∀ x : ↥((T.pullbackAlong Y qY h).withBoundary E').scheme,
      orderAt ((T.pullbackAlong Y qY h).withBoundary E').ideal x
        ≤ ((((T.pullbackAlong Y qY h).withBoundary E').mult : ℕ) : ℕ∞) :=
    fun x => BoundarySeparationBaseChange.orderAt_pullbackTriple_le_mult T h hv hord x
  by_cases hemp₂ : orderAtLeastLocus (T.ideal.comap h) T.mult = (∅ : Set ↥Y)
  · have hlen₂ :
        (maxContactPrincipalization hinv A ((T.pullbackAlong Y qY h).withBoundary E')).toSequenceOfBlowups.length = 0 :=
      length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P A _ hv' hP' hord₂ hemp₂
    by_cases hemp₁ : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)
    · exact isPullback_of_length_eq_zero_of_length_eq_zero h _ _ hlen₂
        (length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P A T hv hP hord hemp₁)
    · exact hvan T ⟨hP, hord, Set.nonempty_iff_ne_empty.mpr hemp₁, hv⟩ h _ hlen₂ hemp₂
  · have hcs₂ : (orderAtLeastLocus (T.ideal.comap h) T.mult).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hemp₂
    have hcs₁ : (orderAtLeastLocus T.ideal T.mult).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hzero
      exact hemp₂ (orderAtLeastLocus_comap_eq_empty T hv h hzero)
    have hypT : OrderReductionHypotheses P T := ⟨hP, hord, hcs₁, hv⟩
    have hypT₂ : OrderReductionHypotheses P ((T.pullbackAlong Y qY h).withBoundary E') := ⟨hP', hord₂, hcs₂, hv'⟩
    obtain ⟨d₁, hd₁, he₁⟩ := exists_isStrictPullback_cover_dropTrivialBoundary hsf hmd htv htm T hypT
    obtain ⟨d₂, hd₂, he₂⟩ := exists_isStrictPullback_cover_dropTrivialBoundary hsf hmd htv htm
      ((T.pullbackAlong Y qY h).withBoundary E') hypT₂
    have htrim₂ : MaxContactReduction.dropTrivialBoundary ((T.pullbackAlong Y qY h).withBoundary E')
        = dropTrivialBoundaryPullback T qY h E' :=
      (dropTrivialBoundary_eq_withBoundary_removeUnitIdeals_consolidated463 ((T.pullbackAlong Y qY h).withBoundary E')).trans rfl
    have hypS₁ : OrderReductionHypotheses P (MaxContactReduction.dropTrivialBoundary T) := hypT.of_dropTrivialBoundaryAdmissible htv
    have hypS₂ : OrderReductionHypotheses P (dropTrivialBoundaryPullback T qY h E') :=
      orderReductionHypotheses_of_eq_consolidated463 htrim₂ (hypT₂.of_dropTrivialBoundaryAdmissible htv)
    have hd₁' : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)
        (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) htrimv hinv
          (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toSequenceOfBlowups d₁.toSequenceOfBlowups := hd₁
    have hd₂' : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv)
        (MaxContactCoverData.coverMarkedBlowupData (dropTrivialBoundaryPullback T qY h E') hpbv hinv
          (lowerDimensionalFamily A (dropTrivialBoundaryPullback T qY h E'))).toSequenceOfBlowups d₂.toSequenceOfBlowups :=
      isStrictPullback_coverMarkedSequence_of_eq_of_heq_consolidated463 hinv A htrim₂ ((hypT₂.of_dropTrivialBoundaryAdmissible htv).valid) hpbv d₂ d₂
        HEq.rfl hd₂
    have hfl₁ : Flat
        (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) :=
      (hff (MaxContactReduction.dropTrivialBoundary T) hypS₁).2
    have hsu₁ : AlgebraicGeometry.Surjective
        (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) :=
      (hff (MaxContactReduction.dropTrivialBoundary T) hypS₁).1
    have hfl₂ : Flat
        (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv) :=
      (hff (dropTrivialBoundaryPullback T qY h E') hypS₂).2
    have hsu₂ : AlgebraicGeometry.Surjective
        (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv) :=
      (hff (dropTrivialBoundaryPullback T qY h E') hypS₂).1
    have hne₂ : ∀ i, i < (MaxContactCoverData.coverMarkedBlowupData (dropTrivialBoundaryPullback T qY h E') hpbv hinv
          (lowerDimensionalFamily A (dropTrivialBoundaryPullback T qY h E'))).toSequenceOfBlowups.length →
        (MaxContactCoverData.coverMarkedBlowupData (dropTrivialBoundaryPullback T qY h E') hpbv hinv
          (lowerDimensionalFamily A (dropTrivialBoundaryPullback T qY h E'))).toSequenceOfBlowups.center i ≠ ⊤ :=
      fun i hi => hsf.center_ne_top (dropTrivialBoundaryPullback T qY h E') hypS₂ i hi
    have hsmc₁ : Smooth
        (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) :=
      MaxContactCoverData.smooth_coverMap_of_isAdmissible _ htrimv
    have hsmc₂ : Smooth
        (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv) :=
      MaxContactCoverData.smooth_coverMap_of_isAdmissible _ hpbv
    have hpbf := @smooth_pullback_fst_snd_and_surjective_fst_consolidated463 T.scheme Y h ‹Smooth h› _ _
      (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)
      (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv)
      hsmc₁ hsmc₂ hsu₁
    have hbdT : ∀ D ∈ (MaxContactReduction.dropTrivialBoundary T).boundary, D ≠ ⊤ :=
      boundary_ne_top_of_eq_consolidated463 (dropTrivialBoundary_eq_withBoundary_removeUnitIdeals_consolidated463 T).symm
        (fun D hD => ne_top_of_mem_removeUnitIdeals_consolidated463 T.boundary D hD)
    have hbdP : ∀ D ∈ (dropTrivialBoundaryPullback T qY h E').boundary, D ≠ ⊤ :=
      fun D hD => ne_top_of_mem_removeUnitIdeals_consolidated463 E' D hD
    have hmax₁ : MaxOrderEq (MaxContactReduction.dropTrivialBoundary T).ideal (MaxContactReduction.dropTrivialBoundary T).mult :=
      ⟨hypS₁.orderLE, hypS₁.coSupport_nonempty⟩
    have hmax₂ : MaxOrderEq (dropTrivialBoundaryPullback T qY h E').ideal
        (dropTrivialBoundaryPullback T qY h E').mult :=
      ⟨hypS₂.orderLE, hypS₂.coSupport_nonempty⟩
    have hcord₁ := orderAt_coverTriple_le_mult_consolidated463 hstar0 horder (MaxContactReduction.dropTrivialBoundary T) htrimv hord hmax₁
    have hcord₂ := orderAt_coverTriple_le_mult_consolidated463 hstar0 horder (dropTrivialBoundaryPullback T qY h E') hpbv
      hord₂ hmax₂
    have hdeleq := @smoothPullbackTriple_coverTriple_eq T Y qY h ‹Smooth h› hq E' hE
      htrimv hpbv hsu₂ hpbf.2.2
    rw [he₁, he₂]
    refine isPullback_of_faithfullyFlat_covers_consolidated463 h
      (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)
      (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv)
      hfl₁ hsu₁ hfl₂ hsu₂
      (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) htrimv hinv
        (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toSequenceOfBlowups
      (MaxContactCoverData.coverMarkedBlowupData (dropTrivialBoundaryPullback T qY h E') hpbv hinv
        (lowerDimensionalFamily A (dropTrivialBoundaryPullback T qY h E'))).toSequenceOfBlowups
      d₁.toSequenceOfBlowups d₂.toSequenceOfBlowups hd₁' hd₂' hne₂ ?_
    intro v v' hvv hvv'
    exact withoutIsoBlowups_isomorphic_of_smoothPullbackTriple_eq_consolidated463 hinv P hmono A B hspec hshift hstar0 hin hMC hAdm hdel htv
      (MaxContactReduction.dropTrivialBoundary T) (dropTrivialBoundaryPullback T qY h E') htrimv hpbv hP hP'
      hord hord₂ hypS₁.coSupport_nonempty hypS₂.coSupport_nonempty hbdT hbdP
      hsu₁ hsu₂ hcord₁ hcord₂
      (Limits.pullback.snd (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
        (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))
      (Limits.pullback.fst (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
        (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))
      hpbf.2.1 hpbf.1 hdeleq hqc hdimfp v v' hvv hvv'


end

end MaxContactFunctoriality


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedPullbackSquare
section

open CategoryTheory.Limits

section

structure MarkedPullbackSquare (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}} (g : Y ⟶ T.scheme) where
  baseScheme : Scheme.{u}
  topScheme : Scheme.{u}
  bottom : baseScheme ⟶ T.scheme
  structMap : baseScheme ⟶ Spec (CommRingCat.of T.base)
  ideal : baseScheme.IdealSheafData
  mult : ℕ
  boundary : List baseScheme.IdealSheafData
  left : topScheme ⟶ baseScheme
  top : topScheme ⟶ Y
  bottom_structMap : bottom ≫ T.structMap = structMap
  dim_le : krullDimSucc baseScheme ≤ T.krullDimSucc
  isPullback : IsPullback left top bottom g
  valid : (MarkedIdealWithBoundary.mk T.base baseScheme structMap ideal mult boundary).IsAdmissible

namespace MarkedPullbackSquare

variable {T : MarkedIdealWithBoundary.{u}} {Y : Scheme.{u}} {g : Y ⟶ T.scheme}

abbrev lowerTriple (S : MarkedPullbackSquare T g) : MarkedIdealWithBoundary.{u} :=
  MarkedIdealWithBoundary.mk T.base S.baseScheme S.structMap S.ideal S.mult S.boundary

abbrev upperTriple (S : MarkedPullbackSquare T g) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (E : List S.topScheme.IdealSheafData) :
    MarkedIdealWithBoundary.{u} :=
  (S.lowerTriple.pullbackOverField S.topScheme k' (S.top ≫ q) S.left).withBoundary E

section
variable (S : MarkedPullbackSquare T g) (hT : T.IsAdmissible) (hg : OrderAtPullbackInvariant T g) (A : S.baseScheme.IdealSheafData)
include hT hg

theorem orderAt_comap_verticalMap (y : ↥S.topScheme) :
    orderAt (A.comap S.left) y = orderAt A (S.left.base y) := by
  have hval :
      (MarkedIdealWithBoundary.mk T.base S.baseScheme S.structMap S.ideal T.mult S.boundary).IsAdmissible :=
    { charZero := S.valid.charZero
      locallyOfFiniteType := S.valid.locallyOfFiniteType
      nonzeroOnComponents := S.valid.nonzeroOnComponents
      one_le_mult := hT.one_le_mult
      quasiCompact := S.valid.quasiCompact
      smooth := S.valid.smooth
      snc := S.valid.snc }
  exact hg S.baseScheme S.bottom S.structMap S.ideal S.boundary hval S.bottom_structMap
    S.topScheme S.left S.top S.isPullback A y

theorem orderAt_comap_verticalMap_le (c : ℕ∞)
    (hA : ∀ x : ↥S.baseScheme, orderAt A x ≤ c) (y : ↥S.topScheme) :
    orderAt (A.comap S.left) y ≤ c := by
  rw [S.orderAt_comap_verticalMap hT hg A y]
  exact hA (S.left.base y)


end

theorem flat_verticalMap (S : MarkedPullbackSquare T g) [Flat g] :
    Flat S.left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Flat) S.isPullback.flip ‹Flat g›

end MarkedPullbackSquare

def NonMonomialPartBaseChange (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}} (g : Y ⟶ T.scheme)
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) : Prop :=
  ∀ (S : MarkedPullbackSquare T g) (E : List S.topScheme.IdealSheafData),
    MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap S.left) S.boundary) E →
    (S.upperTriple k' q E).IsAdmissible →
      nonMonomialPart E (S.ideal.comap S.left)
        = (nonMonomialPart S.boundary S.ideal).comap S.left

def PrincipalizationBaseChange (F : PrincipalizationAssignment.{u}) (n : ℕ) (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}}
    (g : Y ⟶ T.scheme) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) : Prop :=
  ∀ (S : MarkedPullbackSquare T g),
    (∀ x : ↥S.baseScheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) →
    ∀ (E : List S.topScheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap S.left) S.boundary) E →
      (S.upperTriple k' q E).IsAdmissible →
      krullDimSucc S.topScheme ≤ n →
        IsPullbackBlowupSequence S.left (F (S.upperTriple k' q E)).toSequenceOfBlowups (F S.lowerTriple).toSequenceOfBlowups

def MonomialPrincipalizationBaseChange (τ : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}}
    (g : Y ⟶ T.scheme) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) : Prop :=
  ∀ (S : MarkedPullbackSquare T g),
    MonomialCenter.IsLocallyMonomialTriple S.lowerTriple →
    ∀ (E : List S.topScheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap S.left) S.boundary) E →
      MonomialCenter.IsLocallyMonomialTriple (S.upperTriple k' q E) →
        IsPullbackBlowupSequence S.left
          (monomialPrincipalization τ (S.upperTriple k' q E)).toSequenceOfBlowups
          (monomialPrincipalization τ S.lowerTriple).toSequenceOfBlowups

structure BaseChangeCompatible (τ : ComapIsoInvariance.{u}) (F : PrincipalizationAssignment.{u}) (n : ℕ)
    (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}} (g : Y ⟶ T.scheme) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) : Prop where
  rule : PrincipalizationBaseChange F n T g k' q
  flat : Flat g
  monomialBody : MonomialPrincipalizationBaseChange τ T g k' q
  nonMonomial : NonMonomialPartBaseChange T g k' q
  order : OrderAtPullbackInvariant T g


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialFactorTransform
section


section

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {N : X.IdealSheafData} {μ : ℕ} {E : List X.IdealSheafData}

def MarkedSequenceOfBlowups.monomialFactor (s : MarkedSequenceOfBlowups p N μ E) (M : X.IdealSheafData) (m : ℕ) :
    ∀ i : ℕ, (s.schemeAt i).IdealSheafData
  | 0 => M.comap s.isoZero.hom
  | i + 1 =>
      (MarkedSequenceOfBlowups.monomialFactor s M m i).comap (s.transitionMapSucc i) * s.exceptionalDivisor i ^ (μ - m)

@[simp]
theorem MarkedSequenceOfBlowups.monomialFactor_succ (s : MarkedSequenceOfBlowups p N μ E) (M : X.IdealSheafData)
    (m i : ℕ) :
    MarkedSequenceOfBlowups.monomialFactor s M m (i + 1) =
      (MarkedSequenceOfBlowups.monomialFactor s M m i).comap (s.transitionMapSucc i) * s.exceptionalDivisor i ^ (μ - m) :=
  rfl

def MarkedSequenceOfBlowups.controlledTransform (s : MarkedSequenceOfBlowups p N μ E) (I : X.IdealSheafData) (m : ℕ) :
    ∀ i : ℕ, (s.schemeAt i).IdealSheafData
  | 0 => I.comap s.isoZero.hom
  | i + 1 =>
      residualByPow ((MarkedSequenceOfBlowups.controlledTransform s I m i).comap (s.transitionMapSucc i)) (s.exceptionalDivisor i) m

@[simp]
theorem MarkedSequenceOfBlowups.controlledTransform_zero (s : MarkedSequenceOfBlowups p N μ E) (I : X.IdealSheafData)
    (m : ℕ) : MarkedSequenceOfBlowups.controlledTransform s I m 0 = I.comap s.isoZero.hom :=
  rfl

@[simp]
theorem MarkedSequenceOfBlowups.controlledTransform_succ (s : MarkedSequenceOfBlowups p N μ E) (I : X.IdealSheafData)
    (m i : ℕ) :
    MarkedSequenceOfBlowups.controlledTransform s I m (i + 1) =
      residualByPow ((MarkedSequenceOfBlowups.controlledTransform s I m i).comap (s.transitionMapSucc i)) (s.exceptionalDivisor i) m :=
  rfl

end

section

variable {A B : Scheme.{u}}

section
variable {A' B' : Scheme.{u}} (f : A' ⟶ B')

private theorem support_comap_coe_consolidated414 (I : B'.IdealSheafData) :
    (↑(I.comap f).support : Set ↥A') = ⇑f.base ⁻¹' (↑I.support : Set ↥B') := by
  rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
  rfl

private theorem comap_one_consolidated414 :
    (1 : B'.IdealSheafData).comap f = 1 := by
  simp


end

section
variable {Y : Scheme.{u}}

private theorem support_mul_subset_consolidated414 (P Q : Y.IdealSheafData) :
    (↑(P * Q).support : Set ↥Y) ⊆ (↑P.support : Set ↥Y) ∪ (↑Q.support : Set ↥Y) := by
  rw [Scheme.IdealSheafData.support_mul]
  exact Set.Subset.rfl

private theorem support_pow_subset_consolidated414 (P : Y.IdealSheafData) (n : ℕ) :
    (↑(P ^ n).support : Set ↥Y) ⊆ (↑P.support : Set ↥Y) := by
  rcases eq_or_ne n 0 with rfl | hn
  · intro x hx
    have h1 : stalkIdeal (P ^ 0) x = ⊤ := by
      rw [stalkIdeal_pow, pow_zero, ← Ideal.one_eq_top]
    exact absurd h1 ((mem_support_iff_stalkIdeal_ne_top (P ^ 0) x).1 hx)
  · rw [Scheme.IdealSheafData.support_pow]
    exact hn

private theorem support_subset_support_mul_right_consolidated414 (P Q : Y.IdealSheafData) :
    (↑Q.support : Set ↥Y) ⊆ (↑(P * Q).support : Set ↥Y) := by
  rw [Scheme.IdealSheafData.support_mul]
  exact Set.subset_union_right

private theorem isIrreducibleComponentOf_of_maximal_consolidated414 {C S : Set ↥Y} (h1 : IsIrreducible C)
    (h2 : C ⊆ S) (h3 : ∀ C', IsIrreducible C' → C' ⊆ S → C ⊆ C' → C' ⊆ C) :
    IsIrreducibleComponentOf C S := by
  unfold IsIrreducibleComponentOf
  exact ⟨h1, h2, fun C' hC' hCle hC'S => Set.Subset.antisymm (h3 C' hC' hC'S hCle) hCle⟩

private theorem isIrreducible_subset_maximal_of_isIrreducibleComponentOf_consolidated414 {C S : Set ↥Y} (h : IsIrreducibleComponentOf C S) :
    IsIrreducible C ∧ C ⊆ S ∧ ∀ C', IsIrreducible C' → C' ⊆ S → C ⊆ C' → C' ⊆ C := by
  unfold IsIrreducibleComponentOf at h
  exact ⟨h.1, h.2.1, fun C' hC' hC'S hCle => (h.2.2 C' hC' hCle hC'S).subset⟩

private theorem comap_homOfLE_consolidated414 {U V : Y.Opens} (h : U ≤ V)
    (D : Y.IdealSheafData) : (D.comap V.ι).comap (Y.homOfLE h) = D.comap U.ι := by
  rw [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]

private theorem comap_homOfLE_mem_closure_comap_consolidated414 {E : List Y.IdealSheafData}
    {U V : Y.Opens} (h : U ≤ V) :
    ∀ y ∈ Submonoid.closure ((fun D : Y.IdealSheafData => D.comap V.ι) '' {D | D ∈ E}),
      y.comap (Y.homOfLE h) ∈
        Submonoid.closure ((fun D : Y.IdealSheafData => D.comap U.ι) '' {D | D ∈ E}) := by
  intro y hy
  induction hy using Submonoid.closure_induction with
  | mem D hD =>
      obtain ⟨D₀, hD₀, rfl⟩ := hD
      rw [comap_homOfLE_consolidated414]
      exact Submonoid.subset_closure ⟨D₀, hD₀, rfl⟩
  | one =>
      rw [comap_one_consolidated414]
      exact one_mem _
  | mul a b _ _ iha ihb =>
      rw [Scheme.IdealSheafData.comap_mul]
      exact mul_mem iha ihb

private theorem isMonomialIn_of_mem_consolidated414 {E : List Y.IdealSheafData}
    {D : Y.IdealSheafData} (hD : D ∈ E) : IsMonomialIn E D := by
  rw [isMonomialIn_iff_forall_exists_mem_closure]
  intro x
  refine ⟨⊤, trivial, ?_⟩
  exact Submonoid.subset_closure ⟨D, hD, rfl⟩

private theorem isMonomialIn_mul_consolidated414 (E : List Y.IdealSheafData)
    {P Q : Y.IdealSheafData} (hP : IsMonomialIn E P) (hQ : IsMonomialIn E Q) :
    IsMonomialIn E (P * Q) := by
  rw [isMonomialIn_iff_forall_exists_mem_closure] at hP hQ ⊢
  intro x
  obtain ⟨U1, hx1, h1⟩ := hP x
  obtain ⟨U2, hx2, h2⟩ := hQ x
  refine ⟨U1 ⊓ U2, ⟨hx1, hx2⟩, ?_⟩
  have k1 := comap_homOfLE_mem_closure_comap_consolidated414 (E := E) (inf_le_left : U1 ⊓ U2 ≤ U1) _ h1
  have k2 := comap_homOfLE_mem_closure_comap_consolidated414 (E := E) (inf_le_right : U1 ⊓ U2 ≤ U2) _ h2
  rw [comap_homOfLE_consolidated414] at k1 k2
  rw [Scheme.IdealSheafData.comap_mul]
  exact mul_mem k1 k2

private theorem isMonomialIn_pow_consolidated414 (E : List Y.IdealSheafData)
    {P : Y.IdealSheafData} (hP : IsMonomialIn E P) (n : ℕ) : IsMonomialIn E (P ^ n) := by
  rw [isMonomialIn_iff_forall_exists_mem_closure] at hP ⊢
  intro x
  obtain ⟨U, hxU, h⟩ := hP x
  refine ⟨U, hxU, ?_⟩
  rw [Scheme.IdealSheafData.comap_pow]
  exact pow_mem h n

private theorem exists_opens_forall_comap_mem_closure_consolidated414 (L2 : List Y.IdealSheafData) :
    ∀ (L : List Y.IdealSheafData), (∀ D ∈ L, IsMonomialIn L2 D) → ∀ x : ↥Y,
      ∃ V : Y.Opens, x ∈ V ∧ ∀ D ∈ L, D.comap V.ι ∈
        Submonoid.closure ((fun D' : Y.IdealSheafData => D'.comap V.ι) '' {D' | D' ∈ L2}) := by
  intro L
  induction L with
  | nil =>
      intro _ x
      refine ⟨⊤, trivial, ?_⟩
      intro D hD
      exact absurd hD (by simp)
  | cons D0 L ih =>
      intro hall x
      obtain ⟨Vleft, hxVleft, hV1⟩ := ih (fun D hD => hall D (by simp [hD])) x
      obtain ⟨Vright, hxVright, hV2⟩ :=
        (isMonomialIn_iff_forall_exists_mem_closure L2 D0).1 (hall D0 (by simp)) x
      refine ⟨Vleft ⊓ Vright, ⟨hxVleft, hxVright⟩, ?_⟩
      intro D hD
      rcases List.mem_cons.1 hD with rfl | hD'
      · have hk := comap_homOfLE_mem_closure_comap_consolidated414 (E := L2) (inf_le_right : Vleft ⊓ Vright ≤ Vright) _ hV2
        rwa [comap_homOfLE_consolidated414] at hk
      · have hk := comap_homOfLE_mem_closure_comap_consolidated414 (E := L2) (inf_le_left : Vleft ⊓ Vright ≤ Vleft) _ (hV1 D hD')
        rwa [comap_homOfLE_consolidated414] at hk

private theorem isMonomialIn_of_forall_mem_consolidated414 {L1 L2 : List Y.IdealSheafData}
    (h : ∀ D ∈ L1, IsMonomialIn L2 D) {P : Y.IdealSheafData} (hP : IsMonomialIn L1 P) :
    IsMonomialIn L2 P := by
  rw [isMonomialIn_iff_forall_exists_mem_closure] at hP ⊢
  intro x
  obtain ⟨U, hxU, hU⟩ := hP x
  obtain ⟨Vinter, hxW, hW⟩ := exists_opens_forall_comap_mem_closure_consolidated414 L2 L1 h x
  refine ⟨U ⊓ Vinter, ⟨hxU, hxW⟩, ?_⟩
  have h1 := comap_homOfLE_mem_closure_comap_consolidated414 (E := L1) (inf_le_left : U ⊓ Vinter ≤ U) _ hU
  rw [comap_homOfLE_consolidated414] at h1
  refine Submonoid.closure_le.2 ?_ h1
  rintro y ⟨D, hD, rfl⟩
  have h2 := comap_homOfLE_mem_closure_comap_consolidated414 (E := L2) (inf_le_right : U ⊓ Vinter ≤ Vinter) _ (hW D hD)
  rwa [comap_homOfLE_consolidated414] at h2

private theorem support_subset_union_of_locally_eq_mul_pow_consolidated414 (D' A' B' : Y.IdealSheafData)
    (h : ∀ x : ↥Y, ∃ (U : Y.Opens) (ε : ℕ), x ∈ U ∧
      D'.comap U.ι = A'.comap U.ι * B'.comap U.ι ^ ε) :
    (↑D'.support : Set ↥Y) ⊆ (↑A'.support : Set ↥Y) ∪ (↑B'.support : Set ↥Y) := by
  intro x hx
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨hA, hB⟩ := hcon
  obtain ⟨U, ε, hxU, heq⟩ := h x
  have hA0 : orderAt A' x = 0 := (orderAt_eq_zero_iff_not_mem_support A' x).2 hA
  have hB0 : orderAt B' x = 0 := (orderAt_eq_zero_iff_not_mem_support B' x).2 hB
  have hAy : orderAt (A'.comap U.ι) (⟨x, hxU⟩ : ↥U) = 0 := by
    rw [orderAt_comap_of_isOpenImmersion U.ι A' (⟨x, hxU⟩ : ↥U)]
    exact hA0
  have hBy : orderAt (B'.comap U.ι) (⟨x, hxU⟩ : ↥U) = 0 := by
    rw [orderAt_comap_of_isOpenImmersion U.ι B' (⟨x, hxU⟩ : ↥U)]
    exact hB0
  have hnA := (orderAt_eq_zero_iff_not_mem_support (A'.comap U.ι) (⟨x, hxU⟩ : ↥U)).1 hAy
  have hnB := (orderAt_eq_zero_iff_not_mem_support (B'.comap U.ι) (⟨x, hxU⟩ : ↥U)).1 hBy
  have hDy : orderAt (D'.comap U.ι) (⟨x, hxU⟩ : ↥U) = 0 := by
    refine (orderAt_eq_zero_iff_not_mem_support (D'.comap U.ι) (⟨x, hxU⟩ : ↥U)).2 ?_
    rw [heq]
    intro hmem
    rcases support_mul_subset_consolidated414 (A'.comap U.ι) (B'.comap U.ι ^ ε) hmem with h1 | h2
    · exact hnA h1
    · exact hnB (support_pow_subset_consolidated414 (B'.comap U.ι) ε h2)
  rw [orderAt_comap_of_isOpenImmersion U.ι D' (⟨x, hxU⟩ : ↥U)] at hDy
  exact (orderAt_eq_zero_iff_not_mem_support D' x).1 hDy hx

private theorem isMonomialIn_of_locally_eq_mul_pow_consolidated414 (L : List Y.IdealSheafData)
    (D' A' B' : Y.IdealSheafData) (hA : A' ∈ L) (hB : B' ∈ L)
    (h : ∀ x : ↥Y, ∃ (U : Y.Opens) (ε : ℕ), x ∈ U ∧
      D'.comap U.ι = A'.comap U.ι * B'.comap U.ι ^ ε) :
    IsMonomialIn L D' := by
  rw [isMonomialIn_iff_forall_exists_mem_closure]
  intro x
  obtain ⟨U, ε, hxU, heq⟩ := h x
  refine ⟨U, hxU, ?_⟩
  have hA2 : A'.comap U.ι ∈
      Submonoid.closure ((fun D0 : Y.IdealSheafData => D0.comap U.ι) '' {D0 | D0 ∈ L}) :=
    Submonoid.subset_closure ⟨A', hA, rfl⟩
  have hB2 : B'.comap U.ι ∈
      Submonoid.closure ((fun D0 : Y.IdealSheafData => D0.comap U.ι) '' {D0 | D0 ∈ L}) :=
    Submonoid.subset_closure ⟨B', hB, rfl⟩
  rw [heq]
  exact mul_mem hA2 (pow_mem hB2 ε)


end

theorem IsMonomialIn.comap (f : A ⟶ B) {E : List B.IdealSheafData} {M : B.IdealSheafData}
    (h : IsMonomialIn E M) :
    IsMonomialIn (List.map (fun D : B.IdealSheafData => D.comap f) E) (M.comap f) := by
  rw [isMonomialIn_iff_forall_exists_mem_closure] at h ⊢
  intro x
  obtain ⟨U, hxU, hmem⟩ := h (f.base x)
  refine ⟨f ⁻¹ᵁ U, hxU, ?_⟩
  have hcomp : f.resLE U (f ⁻¹ᵁ U) le_rfl ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f :=
    Scheme.Hom.resLE_comp_ι f le_rfl
  have key : ∀ J : B.IdealSheafData,
      (J.comap f).comap (f ⁻¹ᵁ U).ι = (J.comap U.ι).comap (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
    intro J
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcomp]
  have main : ∀ y ∈ Submonoid.closure ((fun D : B.IdealSheafData => D.comap U.ι) '' {D | D ∈ E}),
      y.comap (f.resLE U (f ⁻¹ᵁ U) le_rfl) ∈
        Submonoid.closure ((fun D : A.IdealSheafData => D.comap (f ⁻¹ᵁ U).ι) ''
          {D | D ∈ List.map (fun D : B.IdealSheafData => D.comap f) E}) := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem D hD =>
        obtain ⟨D₀, hD₀, rfl⟩ := hD
        rw [← key D₀]
        exact Submonoid.subset_closure ⟨D₀.comap f, List.mem_map.2 ⟨D₀, hD₀, rfl⟩, rfl⟩
    | one =>
        rw [comap_one_consolidated414]
        exact one_mem _
    | mul a b _ _ iha ihb =>
        rw [Scheme.IdealSheafData.comap_mul]
        exact mul_mem iha ihb
  rw [key M]
  exact main _ hmem

theorem IsMonomialSplitting.comap_iso (e : A ≅ B) {E : List B.IdealSheafData}
    {I M N : B.IdealSheafData} (h : IsMonomialSplitting E I M N) :
    IsMonomialSplitting (List.map (fun D : B.IdealSheafData => D.comap e.hom) E) (I.comap e.hom)
      (M.comap e.hom) (N.comap e.hom) := by
  have hAB : ∀ x : ↥A, (e.inv).base ((e.hom).base x) = x := by
    intro x
    simp
  have hhomInv : ∀ y : ↥B, (e.hom).base ((e.inv).base y) = y := by
    intro y
    simp
  have hcont : Continuous (⇑e.hom.base) := (Scheme.homeoOfIso e).continuous
  have hcont' : Continuous (⇑e.inv.base) := (Scheme.homeoOfIso e).symm.continuous
  refine ⟨?_, ?_, h.monomial.comap e.hom, ?_⟩
  · rw [h.eq_mul, Scheme.IdealSheafData.comap_mul]
  · intro x hx
    rw [support_comap_coe_consolidated414] at hx
    obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.1 (h.monomial_support hx)
    refine Set.mem_iUnion₂.2 ⟨D.comap e.hom, List.mem_map.2 ⟨D, hD, rfl⟩, ?_⟩
    rw [support_comap_coe_consolidated414]
    exact hxD
  · rintro D hD C hCirr hCsubD hCmax hCN
    obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD
    rw [support_comap_coe_consolidated414] at hCsubD
    rw [support_comap_coe_consolidated414] at hCN
    refine h.transversal D₀ hD₀ (⇑e.hom.base '' C) (hCirr.image _ hcont.continuousOn)
      (Set.image_subset_iff.2 hCsubD) ?_ (Set.image_subset_iff.2 hCN)
    intro C' hC'irr hC'D hCle
    have hsub : ⇑e.inv.base '' C' ⊆ (↑((D₀.comap e.hom)).support : Set ↥A) := by
      rw [support_comap_coe_consolidated414]
      rintro x ⟨y, hy, rfl⟩
      simp only [Set.mem_preimage, hhomInv]
      exact hC'D hy
    have hCsub : C ⊆ ⇑e.inv.base '' C' := by
      intro x hx
      exact ⟨(e.hom).base x, hCle ⟨x, hx, rfl⟩, hAB x⟩
    have hfin := hCmax (⇑e.inv.base '' C') (hC'irr.image _ hcont'.continuousOn) hsub hCsub
    intro y hy
    exact ⟨(e.inv).base y, hfin ⟨y, hy, rfl⟩, hhomInv y⟩

end

section

def MarkedIdealWithBoundary.withIdealAndMult (T : MarkedIdealWithBoundary.{u}) (N : T.scheme.IdealSheafData) (μ : ℕ) :
    MarkedIdealWithBoundary.{u} :=
  { base := T.base
    instField := T.instField
    scheme := T.scheme
    structMap := T.structMap
    ideal := N
    mult := μ
    boundary := T.boundary }

theorem MarkedIdealWithBoundary.IsAdmissible.withIdealAndMult {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    {M N : T.scheme.IdealSheafData} (hsplit : IsMonomialSplitting T.boundary T.ideal M N)
    {μ : ℕ} (hμ : T.mult ≤ μ) :
    (T.withIdealAndMult N μ).IsAdmissible :=
  { charZero := hT.charZero
    locallyOfFiniteType := hT.locallyOfFiniteType
    nonzeroOnComponents := hsplit.nonzeroOnComponents_nonMonomial hT.nonzeroOnComponents
    one_le_mult := le_trans hT.one_le_mult hμ
    quasiCompact := hT.quasiCompact
    smooth := hT.smooth
    snc := hT.snc }

end

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {N : X.IdealSheafData} {μ : ℕ} {E : List X.IdealSheafData}

section
variable (s : MarkedSequenceOfBlowups p N μ E) (i : ℕ)

private theorem exceptionalDivisor_eq_exceptionalIdeal_consolidated414 :
    s.exceptionalDivisor i = Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i) := by
  rw [MarkedSequenceOfBlowups.exceptionalDivisor_eq, Blowup.exceptionalIdeal_eq_comap]

private theorem isLocallyGeneratedByNonZeroDivisor_exceptionalDivisor_consolidated414 (hi : i < s.length) : Blowup.IsLocallyGeneratedByNonZeroDivisor (s.exceptionalDivisor i) := by
  rw [exceptionalDivisor_eq_exceptionalIdeal_consolidated414]
  exact isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal (s.isBlowupAlongIdealSheaf_blowupMorphism i hi)


end

private theorem subset_orderAtLeastLocus_of_eq_mul_consolidated414 {Y : Scheme.{u}} (Mi Ni Ci : Y.IdealSheafData)
    (h : Ci = Mi * Ni) (m : ℕ) (S : Set ↥Y) (hS : S ⊆ orderAtLeastLocus Ni m) :
    S ⊆ orderAtLeastLocus Ci m := by
  intro x hx
  have h1 : (m : ℕ∞) ≤ orderAt Ni x := (mem_orderAtLeastLocus_iff _ _ _).1 (hS hx)
  have h2 := add_orderAt_le_orderAt_mul Mi Ni x
  rw [← h] at h2
  exact (mem_orderAtLeastLocus_iff _ _ _).2 (le_trans h1 (le_trans le_add_self h2))

private theorem exceptionalDivisor_pow_mul_comap_mul_eq_comap_consolidated414 (s : MarkedSequenceOfBlowups p N μ E) (m : ℕ) (hm : m ≤ μ)
    (i : ℕ) (hi : i < s.length) (Ci Mi : (s.schemeAt i).IdealSheafData)
    (h : Ci = Mi * s.ideal i) :
    s.exceptionalDivisor i ^ m *
        (Mi.comap (s.transitionMapSucc i) * s.exceptionalDivisor i ^ (μ - m) * s.ideal (i + 1))
      = Ci.comap (s.transitionMapSucc i) := by
  have hid : s.exceptionalDivisor i ^ μ * s.ideal (i + 1) = (s.ideal i).comap (s.transitionMapSucc i) := by
    rw [exceptionalDivisor_eq_exceptionalIdeal_consolidated414]
    exact s.ideal_succ i hi
  have hF : s.exceptionalDivisor i ^ m * s.exceptionalDivisor i ^ (μ - m) = s.exceptionalDivisor i ^ μ := by
    rw [← pow_add, Nat.add_sub_cancel' hm]
  calc s.exceptionalDivisor i ^ m *
          (Mi.comap (s.transitionMapSucc i) * s.exceptionalDivisor i ^ (μ - m) * s.ideal (i + 1))
      = Mi.comap (s.transitionMapSucc i) *
          ((s.exceptionalDivisor i ^ m * s.exceptionalDivisor i ^ (μ - m)) * s.ideal (i + 1)) := by
        simp only [mul_assoc, mul_comm, mul_left_comm]
    _ = Mi.comap (s.transitionMapSucc i) * ((s.ideal i).comap (s.transitionMapSucc i)) := by rw [hF, hid]
    _ = Ci.comap (s.transitionMapSucc i) := by rw [h, Scheme.IdealSheafData.comap_mul]

section
variable (s : MarkedSequenceOfBlowups p N μ E) (I : X.IdealSheafData) (m i : ℕ)

private theorem controlledTransform_eq_sequenceData_consolidated414 :
    MarkedSequenceOfBlowups.controlledTransform s I m i
      = ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData).controlledTransform I m i := by
  induction i with
  | zero =>
      exact (BlowupSequenceData.controlledTransform_zero ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData) I m).symm
  | succ n ih =>
      have h2 := BlowupSequenceData.controlledTransform_succ ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData) I m n
      refine Eq.trans ?_ h2.symm
      exact congrArg
        (fun J : (s.schemeAt n).IdealSheafData =>
          residualByPow (J.comap (s.transitionMapSucc n)) (s.exceptionalDivisor n) m) ih

private theorem comap_controlledTransform_eq_comap_sequenceData_consolidated414 :
    (MarkedSequenceOfBlowups.controlledTransform s I m i).comap (s.transitionMapSucc i)
      = (((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData).controlledTransform I m i).comap
          (((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData).map i) :=
  congrArg (fun J : (s.schemeAt i).IdealSheafData => J.comap (s.transitionMapSucc i))
    (controlledTransform_eq_sequenceData_consolidated414 s I m i)

private theorem exceptionalDivisor_pow_mul_controlledTransform_succ_consolidated414 (h : ∃ Bd, s.exceptionalDivisor i ^ m * Bd
        = (MarkedSequenceOfBlowups.controlledTransform s I m i).comap (s.transitionMapSucc i)) :
    s.exceptionalDivisor i ^ m * MarkedSequenceOfBlowups.controlledTransform s I m (i + 1)
      = (MarkedSequenceOfBlowups.controlledTransform s I m i).comap (s.transitionMapSucc i) := by
  obtain ⟨Bd, hBd⟩ := h
  have hd := BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData)
    I m i ⟨Bd, hBd.trans (comap_controlledTransform_eq_comap_sequenceData_consolidated414 s I m i)⟩
  exact (congrArg (fun J : (s.schemeAt (i + 1)).IdealSheafData => s.exceptionalDivisor i ^ m * J)
      (controlledTransform_eq_sequenceData_consolidated414 s I m (i + 1))).trans
    (hd.trans (comap_controlledTransform_eq_comap_sequenceData_consolidated414 s I m i).symm)


end

private theorem orderAt_eq_of_mem_center_support_consolidated414 (s : MarkedSequenceOfBlowups p N μ E)
    (hord : ∀ i ≤ s.length, ∀ x : ↥(s.schemeAt i), orderAt (s.ideal i) x ≤ (μ : ℕ∞))
    (i : ℕ) (hi : i < s.length) (x : ↥(s.schemeAt i)) (hx : x ∈ (s.center i).support) :
    orderAt (s.ideal i) x = (μ : ℕ∞) :=
  le_antisymm (hord i (le_of_lt hi) x) ((mem_orderAtLeastLocus_iff _ _ _).1 (s.center_order i hi hx))

end

section

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) {M N : T.scheme.IdealSheafData} (hsplit : IsMonomialSplitting T.boundary T.ideal M N) {μ : ℕ} (hμ : T.mult ≤ μ) (s : MarkedSequenceOfBlowups T.structMap N μ T.boundary) (hord : ∀ i ≤ s.length, ∀ x : ↥(s.schemeAt i), orderAt (s.ideal i) x ≤ (μ : ℕ∞))
include hG hT hsplit hμ hord

theorem isMonomialSplitting_controlledTransform_monomialFactor (i : ℕ) (hi : i ≤ s.length) :
    IsMonomialSplitting (s.boundary i) (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult i)
        (MarkedSequenceOfBlowups.monomialFactor s M T.mult i) (s.ideal i) ∧
      (i < s.length →
        (∀ x ∈ (s.center i).support, orderAt (s.ideal i) x = (μ : ℕ∞)) ∧
        (↑(s.center i).support : Set ↥(s.schemeAt i)) ⊆
          orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult i) T.mult ∧
        ∃ Bd : (s.schemeAt (i + 1)).IdealSheafData,
          s.exceptionalDivisor i ^ T.mult * Bd =
            (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult i).comap (s.transitionMapSucc i)) := by
  have hECNC : EffectiveCartierSupportContainsNoComponent.{u} := effectiveCartierSupportContainsNoComponent
  have hadm : (T.withIdealAndMult N μ).IsAdmissible := hT.withIdealAndMult hsplit hμ
  have hsplit_all : ∀ j, j ≤ s.length →
      IsMonomialSplitting (s.boundary j) (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult j)
        (MarkedSequenceOfBlowups.monomialFactor s M T.mult j) (s.ideal j) := by
    intro j
    induction j with
    | zero =>
        intro _
        rw [s.boundary_zero, s.ideal_zero]
        exact hsplit.comap_iso s.isoZero
    | succ n ih =>
        intro hn
        have hn' : n < s.length := hn
        have hsp := ih (le_of_lt hn')
        have hdiv : s.exceptionalDivisor n ^ T.mult *
            ((MarkedSequenceOfBlowups.monomialFactor s M T.mult n).comap (s.transitionMapSucc n)
              * s.exceptionalDivisor n ^ (μ - T.mult) * s.ideal (n + 1))
            = (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult n).comap (s.transitionMapSucc n) :=
          exceptionalDivisor_pow_mul_comap_mul_eq_comap_consolidated414 s T.mult hμ n hn' _ _ hsp.eq_mul
        have htw := exceptionalDivisor_pow_mul_controlledTransform_succ_consolidated414 s T.ideal T.mult n ⟨_, hdiv⟩
        have heq : MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult (n + 1)
            = MarkedSequenceOfBlowups.monomialFactor s M T.mult (n + 1) * s.ideal (n + 1) := by
          refine eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul (isLocallyGeneratedByNonZeroDivisor_exceptionalDivisor_consolidated414 s n hn')
            T.mult ?_
          rw [htw, ← hdiv]
          simp only [MarkedSequenceOfBlowups.monomialFactor_succ, mul_comm, mul_left_comm]
        have hTn := MarkedIdealWithBoundary.IsAdmissible.transformAt hECNC hadm s n (le_of_lt hn')
        have hsm : Smooth ((s.center n).subschemeι ≫ s.projectionToSpec n) := by
          rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
          exact s.center_smooth n hn'
        have hsnc : HasStrictNormalCrossingsWith (s.projectionToSpec n) (s.center n) (s.boundary n) := by
          rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
          exact s.center_snc n hn'
        have hbl : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc n) (s.center n) := s.isBlowupAlongIdealSheaf_blowupMorphism n hn'
        have hbnd : s.boundary (n + 1) =
            List.map (Blowup.strictTransform (s.transitionMapSucc n) (s.center n)) (s.boundary n) ++
              [Blowup.exceptionalIdeal (s.transitionMapSucc n) (s.center n)] := s.boundary_succ n hn'
        have hExcMem : Blowup.exceptionalIdeal (s.transitionMapSucc n) (s.center n) ∈ s.boundary (n + 1) := by
          rw [hbnd]
          simp
        have hExcMem' : s.exceptionalDivisor n ∈ s.boundary (n + 1) := by
          rw [exceptionalDivisor_eq_exceptionalIdeal_consolidated414]
          exact hExcMem
        have hSTmem : ∀ D₀ ∈ s.boundary n,
            Blowup.strictTransform (s.transitionMapSucc n) (s.center n) D₀ ∈ s.boundary (n + 1) := by
          intro D₀ hD₀
          rw [hbnd]
          exact List.mem_append_left _ (List.mem_map.2 ⟨D₀, hD₀, rfl⟩)
        have hfac : ∀ D₀ ∈ s.boundary n, ∀ x' : ↥(s.schemeAt (n + 1)),
            ∃ (U : (s.schemeAt (n + 1)).Opens) (ε : ℕ), x' ∈ U ∧
              (D₀.comap (s.transitionMapSucc n)).comap U.ι =
                (Blowup.strictTransform (s.transitionMapSucc n) (s.center n) D₀).comap U.ι *
                  (Blowup.exceptionalIdeal (s.transitionMapSucc n) (s.center n)).comap U.ι ^ ε := by
          intro D₀ hD₀ x'
          obtain ⟨U, ε, hxU, _, _, hEq⟩ :=
            hG.monomialInputs.blowup_total_transform _ hTn (s.center n) hsm hsnc _
              (s.transitionMapSucc n) hbl D₀ hD₀ x'
          exact ⟨U, ε, hxU, hEq⟩
        have hmonD : ∀ D₀ ∈ s.boundary n,
            IsMonomialIn (s.boundary (n + 1)) (D₀.comap (s.transitionMapSucc n)) := by
          intro D₀ hD₀
          exact isMonomialIn_of_locally_eq_mul_pow_consolidated414 _ _ _ _ (hSTmem D₀ hD₀) hExcMem (hfac D₀ hD₀)
        have hmonM : IsMonomialIn (s.boundary (n + 1))
            ((MarkedSequenceOfBlowups.monomialFactor s M T.mult n).comap (s.transitionMapSucc n)) := by
          refine isMonomialIn_of_forall_mem_consolidated414 ?_ (hsp.monomial.comap (s.transitionMapSucc n))
          intro D hD
          obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD
          exact hmonD D₀ hD₀
        refine ⟨heq, ?_, ?_, ?_⟩
        · intro x hx
          rw [MarkedSequenceOfBlowups.monomialFactor_succ] at hx
          rcases support_mul_subset_consolidated414 _ _ hx with hx1 | hx2
          · rw [support_comap_coe_consolidated414] at hx1
            obtain ⟨D₀, hD₀, hxD⟩ := Set.mem_iUnion₂.1 (hsp.monomial_support hx1)
            have hx' : x ∈ (↑((D₀.comap (s.transitionMapSucc n))).support : Set ↥(s.schemeAt (n + 1))) := by
              rw [support_comap_coe_consolidated414]
              exact hxD
            rcases support_subset_union_of_locally_eq_mul_pow_consolidated414 _ _ _ (hfac D₀ hD₀) hx' with h1 | h2
            · exact Set.mem_iUnion₂.2 ⟨_, hSTmem D₀ hD₀, h1⟩
            · exact Set.mem_iUnion₂.2 ⟨_, hExcMem, h2⟩
          · exact Set.mem_iUnion₂.2 ⟨_, hExcMem', support_pow_subset_consolidated414 _ _ hx2⟩
        · rw [MarkedSequenceOfBlowups.monomialFactor_succ]
          exact isMonomialIn_mul_consolidated414 _ hmonM (isMonomialIn_pow_consolidated414 _ (isMonomialIn_of_mem_consolidated414 hExcMem') _)
        · intro D hD C hCirr hCsubD hCmax hCsub
          rw [hbnd] at hD
          rcases List.mem_append.1 hD with hD' | hD'
          · obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD'
            obtain ⟨η', C0, hCeq, _, hC0comp, _, hC0eq⟩ :=
              hG.strictTransform_components _ hTn (s.center n) hsm hsnc _ (s.transitionMapSucc n) hbl
                D₀ hD₀ C (isIrreducibleComponentOf_of_maximal_consolidated414 hCirr hCsubD hCmax)
            obtain ⟨hc1, hc2, hc3⟩ := isIrreducible_subset_maximal_of_isIrreducibleComponentOf_consolidated414 hC0comp
            have hηC : η' ∈ C := by
              rw [hCeq]
              exact subset_closure (Set.mem_singleton η')
            have h2 : η' ∈
                (↑((s.ideal n).comap (s.transitionMapSucc n)).support : Set ↥(s.schemeAt (n + 1))) := by
              rw [← s.ideal_succ n hn']
              exact support_subset_support_mul_right_consolidated414 _ _ (hCsub hηC)
            rw [support_comap_coe_consolidated414] at h2
            have hsub0 : C0 ⊆ (↑(s.ideal n).support : Set ↥(s.schemeAt n)) := by
              rw [hC0eq]
              exact closure_minimal (Set.singleton_subset_iff.2 h2) (s.ideal n).support.2
            exact hsp.transversal D₀ hD₀ C0 hc1 hc2 hc3 hsub0
          · rw [List.mem_singleton] at hD'
            subst hD'
            exact hG.exceptional_components_not_subset _ hTn (s.center n) hsm hsnc _
              (s.transitionMapSucc n) hbl (s.ideal n) μ (orderAt_eq_of_mem_center_support_consolidated414 s hord n hn')
              (s.ideal (n + 1)) (s.ideal_succ n hn') C (isIrreducibleComponentOf_of_maximal_consolidated414 hCirr hCsubD hCmax) hCsub
  refine ⟨hsplit_all i hi, ?_⟩
  intro hilt
  refine ⟨fun x hx => orderAt_eq_of_mem_center_support_consolidated414 s hord i hilt x hx, ?_, ?_⟩
  · refine subset_orderAtLeastLocus_of_eq_mul_consolidated414 _ _ _ (hsplit_all i hi).eq_mul T.mult _ ?_
    intro x hx
    exact orderAtLeastLocus_subset_of_le (s.ideal i) hμ (s.center_order i hilt hx)
  · exact ⟨_, exceptionalDivisor_pow_mul_comap_mul_eq_comap_consolidated414 s T.mult hμ i hilt _ _ (hsplit_all i hi).eq_mul⟩

theorem isMarked_sequenceData_of_orderAt_le :
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.IsMarked T.structMap T.ideal T.mult
      T.boundary := by
  have hself := (MarkedBlowupSequenceData.ofMarkedSequence s).isMarked_toBlowupSequenceData
  refine ⟨?_, ?_, hself.center_smooth, hself.center_snc⟩
  · intro i hi
    have hi' : i < s.length := hi
    obtain ⟨Bd, hBd⟩ := ((isMonomialSplitting_controlledTransform_monomialFactor hG hT hsplit hμ s hord i (le_of_lt hi')).2 hi').2.2
    exact ⟨Bd, hBd.trans (comap_controlledTransform_eq_comap_sequenceData_consolidated414 s T.ideal T.mult i)⟩
  · intro i hi
    have hi' : i < s.length := hi
    have hsub := ((isMonomialSplitting_controlledTransform_monomialFactor hG hT hsplit hμ s hord i (le_of_lt hi')).2 hi').2.1
    intro x hx
    have h1 : (T.mult : ℕ∞) ≤ orderAt (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult i) x :=
      (mem_orderAtLeastLocus_iff _ _ _).1 (hsub hx)
    have he : orderAt (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult i) x
        = orderAt (((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData).controlledTransform T.ideal T.mult i) x :=
      congrArg (fun J : (s.schemeAt i).IdealSheafData => orderAt J x)
        (controlledTransform_eq_sequenceData_consolidated414 s T.ideal T.mult i)
    exact (mem_orderAtLeastLocus_iff _ _ _).2 (he ▸ h1)

theorem principalizationCertificate_controlledTransform (hcert : ∀ i < s.length,
      OrderCertificate (s.schemeAt i) (s.projectionToSpec i) (s.ideal i) μ (s.boundaryLocus i) (s.center i))
    (i : ℕ) (hi : i < s.length) :
    PrincipalizationCertificate (s.schemeAt i) (s.projectionToSpec i) (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult i) T.mult
      (s.boundaryLocus i) (s.center i) := by
  have hsp := (isMonomialSplitting_controlledTransform_monomialFactor hG hT hsplit hμ s hord i (le_of_lt hi)).1
  have hMsub : (↑(MarkedSequenceOfBlowups.monomialFactor s M T.mult i).support : Set ↥(s.schemeAt i)) ⊆
      s.boundaryLocus i := by
    intro x hx
    obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.1 (hsp.monomial_support hx)
    exact (MarkedSequenceOfBlowups.mem_boundaryLocus_iff s i x).2 ⟨D, hD, hxD⟩
  exact PrincipalizationCertificate.toOrder (MarkedSequenceOfBlowups.monomialFactor s M T.mult i) (s.ideal i) μ hsp.eq_mul
    hMsub hμ (s.center_order i hi) (hcert i hi)


end

theorem maxOrder_ideal_length_lt_of_orderAtLeastLocus_eq_empty {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {N : X.IdealSheafData} {μ : ℕ}
    {E : List X.IdealSheafData} (s : MarkedSequenceOfBlowups p N μ E)
    (hord : ∀ i ≤ s.length, ∀ x : ↥(s.schemeAt i), orderAt (s.ideal i) x ≤ (μ : ℕ∞))
    (hempty : orderAtLeastLocus (s.ideal s.length) μ = ∅) (hμ : 1 ≤ μ) :
    maxOrder (s.ideal s.length) < μ :=
  maxOrder_lt_of_orderAtLeastLocus_eq_empty (s.ideal s.length) (hord s.length le_rfl) hμ hempty

end

section

private theorem cast_sub_le_of_cast_le_add_consolidated414 {a : ℕ∞} {m s : ℕ}
    (h : (m : ℕ∞) ≤ a + (s : ℕ∞)) : ((m - s : ℕ) : ℕ∞) ≤ a := by
  rcases eq_or_ne a ⊤ with rfl | hne
  · exact le_top
  · obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hne
    have h' : m ≤ n + s := by exact_mod_cast h
    have h'' : m - s ≤ n := by omega
    exact_mod_cast h''

theorem exists_exceptionalIdeal_pow_mul_eq_comap_mul_pow (_hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : T.IsAdmissible) (Z : T.scheme.IdealSheafData)
    (_hsm : Smooth (Z.subschemeι ≫ T.structMap))
    (hsnc : HasStrictNormalCrossingsWith T.structMap Z T.boundary)
    (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (hbl : Blowup.IsBlowupAlongIdealSheaf π Z)
    (Bd Mon Ad : T.scheme.IdealSheafData) (m sdeg : ℕ)
    (hsplit : IsMonomialSplitting T.boundary Bd Mon Ad)
    (hZsub : (↑Z.support : Set ↥T.scheme) ⊆ orderAtLeastLocus Bd m)
    (hordA : ∀ x ∈ Z.support, orderAt Ad x = (sdeg : ℕ∞))
    (B' : X'.IdealSheafData) (_hB' : Blowup.exceptionalIdeal π Z ^ m * B' = Bd.comap π)
    (A' : X'.IdealSheafData) (_hA' : Blowup.exceptionalIdeal π Z ^ sdeg * A' = Ad.comap π) :
    ∃ C : X'.IdealSheafData,
      Blowup.exceptionalIdeal π Z ^ m * C = Mon.comap π * Blowup.exceptionalIdeal π Z ^ sdeg := by
  rcases Nat.lt_or_ge sdeg m with hms | hms
  · have := hT.charZero
    have := hT.smooth
    have : IsNoetherian T.scheme := hT.isNoetherian
    have : IsNoetherian X' := isNoetherian_of_isBlowupAlongIdealSheaf hbl
    have hsub : (↑Z.support : Set ↥T.scheme) ⊆ orderAtLeastLocus Mon (m - sdeg) := by
      intro x hx
      refine (mem_orderAtLeastLocus_iff Mon (m - sdeg) x).2 ?_
      have h1 : (m : ℕ∞) ≤ orderAt Bd x := (mem_orderAtLeastLocus_iff Bd m x).1 (hZsub hx)
      rw [hsplit.orderAt_eq_add T.structMap x, hordA x hx] at h1
      exact cast_sub_le_of_cast_le_add_consolidated414 h1
    have hle : Mon ≤ Z ^ (m - sdeg) :=
      le_pow_of_hasStrictNormalCrossingsWith T.structMap Z Mon T.boundary hsnc (m - sdeg) hsub
    obtain ⟨C, hC, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf π Z Mon (m - sdeg) hbl hle
    refine ⟨C, ?_⟩
    have hms' : m - sdeg + sdeg = m := Nat.sub_add_cancel hms.le
    calc Blowup.exceptionalIdeal π Z ^ m * C
        = Blowup.exceptionalIdeal π Z ^ (m - sdeg) * Blowup.exceptionalIdeal π Z ^ sdeg * C := by
          rw [← pow_add, hms']
      _ = Blowup.exceptionalIdeal π Z ^ (m - sdeg) * C * Blowup.exceptionalIdeal π Z ^ sdeg := by
          simp only [mul_comm, mul_left_comm]
      _ = Mon.comap π * Blowup.exceptionalIdeal π Z ^ sdeg := by rw [hC]
  · refine ⟨Mon.comap π * Blowup.exceptionalIdeal π Z ^ (sdeg - m), ?_⟩
    have hpow : Blowup.exceptionalIdeal π Z ^ m * Blowup.exceptionalIdeal π Z ^ (sdeg - m)
        = Blowup.exceptionalIdeal π Z ^ sdeg := by
      rw [← pow_add, Nat.add_sub_cancel' hms]
    calc Blowup.exceptionalIdeal π Z ^ m * (Mon.comap π * Blowup.exceptionalIdeal π Z ^ (sdeg - m))
        = Mon.comap π * (Blowup.exceptionalIdeal π Z ^ m * Blowup.exceptionalIdeal π Z ^ (sdeg - m)) := by
          simp only [mul_assoc, mul_comm]
      _ = Mon.comap π * Blowup.exceptionalIdeal π Z ^ sdeg := by rw [hpow]

section
variable {Y : Scheme.{u}}

private theorem mem_closeds_compl_iff_consolidated414 (S : TopologicalSpace.Closeds ↥Y)
    (x : ↥Y) : x ∈ S.compl ↔ x ∉ S := Iff.rfl

private theorem comap_eq_one_of_forall_notMem_support_consolidated414 (I : Y.IdealSheafData)
    (U : Y.Opens) (h : ∀ x : ↥Y, x ∈ U → x ∉ (↑I.support : Set ↥Y)) : I.comap U.ι = 1 := by
  rw [Scheme.IdealSheafData.one_eq_top]
  exact Blowup.comap_eq_top_of_notMem_support U.ι I (fun y => h y.1 y.2)

private theorem orderAt_comap_opens_ι_consolidated414 (U : Y.Opens) (I : Y.IdealSheafData)
    (x : ↥Y) (hx : x ∈ U) : orderAt (I.comap U.ι) ⟨x, hx⟩ = orderAt I x := by
  have h := orderAt_comap_of_isOpenImmersion U.ι I ⟨x, hx⟩
  simpa using h


end

section
variable {A B : Scheme.{u}} (f : A ⟶ B)

private theorem comap_list_prod_consolidated414 :
    ∀ L : List B.IdealSheafData,
      (L.prod).comap f = (L.map (fun D : B.IdealSheafData => D.comap f)).prod := by
  intro L
  induction L with
  | nil =>
      rw [List.prod_nil, List.map_nil, List.prod_nil]
      exact comap_one_consolidated414 f
  | cons D L ih =>
      rw [List.prod_cons, Scheme.IdealSheafData.comap_mul, ih, List.map_cons, List.prod_cons]

private theorem exists_list_prod_eq_of_mem_closure_consolidated414 (E : List B.IdealSheafData) {y : A.IdealSheafData}
    (hy : y ∈ Submonoid.closure ((fun D : B.IdealSheafData => D.comap f) '' {D | D ∈ E})) :
    ∃ L : List B.IdealSheafData, (∀ D ∈ L, D ∈ E) ∧
      y = (L.map (fun D : B.IdealSheafData => D.comap f)).prod := by
  induction hy using Submonoid.closure_induction with
  | mem a ha =>
      obtain ⟨D, hD, rfl⟩ := ha
      refine ⟨[D], ?_, ?_⟩
      · intro D' hD'
        rw [List.mem_singleton.1 hD']
        exact hD
      · simp
  | one => exact ⟨[], by simp, by simp⟩
  | mul a b _ _ iha ihb =>
      obtain ⟨L1, h1, e1⟩ := iha
      obtain ⟨L2, h2, e2⟩ := ihb
      refine ⟨L1 ++ L2, ?_, ?_⟩
      · intro D hD
        rcases List.mem_append.1 hD with h | h
        · exact h1 D h
        · exact h2 D h
      · rw [e1, e2, List.map_append, List.prod_append]


end

private theorem isIrreducible_inter_isOpen_consolidated414 {α : Type u} [TopologicalSpace α] {S O : Set α}
    (hS : IsIrreducible S) (hO : IsOpen O) (hne : (S ∩ O).Nonempty) :
    IsIrreducible (S ∩ O) := by
  refine ⟨hne, ?_⟩
  intro u v hu hv hsu hsv
  obtain ⟨a, ha, hau⟩ := hsu
  obtain ⟨b, hb, hbv⟩ := hsv
  obtain ⟨c, hcS, hc⟩ :=
    hS.2 (u ∩ O) (v ∩ O) (hu.inter hO) (hv.inter hO) ⟨a, ha.1, hau, ha.2⟩ ⟨b, hb.1, hbv, hb.2⟩
  exact ⟨c, ⟨hcS, hc.1.2⟩, hc.1.1, hc.2.1⟩

private theorem exists_closure_singleton_eq_closure_consolidated414 (X : Scheme.{u}) {S : Set ↥X}
    (hS : IsIrreducible S) : ∃ η : ↥X, closure ({η} : Set ↥X) = closure S := by
  obtain ⟨η, hη⟩ := QuasiSober.sober hS.closure isClosed_closure
  exact ⟨η, hη⟩

section
variable {α : Type u} [TopologicalSpace α] {S : Set α} {η : α} (hη : closure ({η} : Set α) = closure S)
include hη

private theorem mem_of_isOpen_of_closure_singleton_eq_consolidated414 {O : Set α} (hO : IsOpen O)
    (hne : (S ∩ O).Nonempty) : η ∈ O := by
  by_contra hx
  have h1 : closure ({η} : Set α) ⊆ Oᶜ :=
    closure_minimal (Set.singleton_subset_iff.2 hx) hO.isClosed_compl
  rw [hη] at h1
  obtain ⟨a, haS, haO⟩ := hne
  exact (h1 (subset_closure haS)) haO

private theorem subset_of_closure_singleton_eq_closure_consolidated414 {F : Set α} (hF : IsClosed F)
    (hmem : η ∈ F) : S ⊆ F := by
  have h1 : closure ({η} : Set α) ⊆ F := closure_minimal (Set.singleton_subset_iff.2 hmem) hF
  rw [hη] at h1
  exact fun a ha => h1 (subset_closure ha)


end

private theorem isNoetherian_spec_field_consolidated414 (k : Type u) [Field k] :
    IsNoetherian (Spec (CommRingCat.of k)) := by
  rw [AlgebraicGeometry.isNoetherian_Spec]
  infer_instance

section
variable (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (Z : T.scheme.IdealSheafData) (hsm : Smooth (Z.subschemeι ≫ T.structMap))
include hT hsm

private theorem isNoetherian_subscheme_of_smooth_consolidated414 :
    IsNoetherian Z.subscheme := by
  have := hsm
  have := hT.quasiCompact
  have : IsNoetherian (Spec (CommRingCat.of T.base)) :=
    isNoetherian_spec_field_consolidated414 T.base
  have : LocallyOfFiniteType (Z.subschemeι ≫ T.structMap) := inferInstance
  have : QuasiCompact (Z.subschemeι ≫ T.structMap) := inferInstance
  exact isNoetherian_of_locallyOfFiniteType (Z.subschemeι ≫ T.structMap)

private theorem exists_opens_isIrreducible_support_inter_consolidated414 (y : ↥T.scheme) (hy : y ∈ (↑Z.support : Set ↥T.scheme)) :
    ∃ V : T.scheme.Opens, y ∈ V ∧
      IsIrreducible ((↑Z.support : Set ↥T.scheme) ∩ (↑V : Set ↥T.scheme)) := by
  have := hT.charZero
  have := hT.smooth
  have : IsNoetherian Z.subscheme := isNoetherian_subscheme_of_smooth_consolidated414 T hT Z hsm
  have : TopologicalSpace.NoetherianSpace ↥Z.subscheme := inferInstance
  have hemb : Topology.IsClosedEmbedding (⇑(Z.subschemeι).base) :=
    AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding Z.subschemeι
  have hrange : Set.range (⇑(Z.subschemeι).base) = (↑Z.support : Set ↥T.scheme) := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι]
  obtain ⟨y', hy'⟩ : ∃ y' : ↥Z.subscheme, (Z.subschemeι).base y' = y := by
    have h1 : y ∈ Set.range (⇑(Z.subschemeι).base) := by rw [hrange]; exact hy
    exact h1
  have hfin : (irreducibleComponents ↥Z.subscheme).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hC₁ : irreducibleComponent y' ∈ irreducibleComponents ↥Z.subscheme :=
    irreducibleComponent_mem_irreducibleComponents y'
  have hy'C : y' ∈ irreducibleComponent y' := mem_irreducibleComponent
  have hRclosed : IsClosed
      (⋃ C ∈ {C : Set ↥Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧
        C ≠ irreducibleComponent y'}, (⇑(Z.subschemeι).base) '' C) := by
    refine Set.Finite.isClosed_biUnion (hfin.subset (fun C hC => hC.1)) ?_
    intro C hC
    exact hemb.isClosedMap _ (isClosed_of_mem_irreducibleComponents C hC.1)
  have hyR : y ∉ (⋃ C ∈ {C : Set ↥Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧
      C ≠ irreducibleComponent y'}, (⇑(Z.subschemeι).base) '' C) := by
    intro hmem
    obtain ⟨C, hC, hyC⟩ := Set.mem_iUnion₂.1 hmem
    obtain ⟨c, hcC, hceq⟩ := hyC
    have hcy : c = y' := hemb.injective (by rw [hceq, hy'])
    have hdisj := irreducibleComponentsDisjointOfSmooth T.base Z.subscheme (Z.subschemeι ≫ T.structMap) hsm
      C hC.1 (irreducibleComponent y') hC₁ hC.2
    exact (Set.disjoint_left.mp hdisj (hcy ▸ hcC)) hy'C
  have hSV : (↑Z.support : Set ↥T.scheme) ∩
        (⋃ C ∈ {C : Set ↥Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧
          C ≠ irreducibleComponent y'}, (⇑(Z.subschemeι).base) '' C)ᶜ
      = ((⇑(Z.subschemeι).base) '' (irreducibleComponent y')) ∩
        (⋃ C ∈ {C : Set ↥Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧
          C ≠ irreducibleComponent y'}, (⇑(Z.subschemeι).base) '' C)ᶜ := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro a ⟨haS, haR⟩
      rw [← hrange] at haS
      obtain ⟨c, rfl⟩ := haS
      refine ⟨⟨c, ?_, rfl⟩, haR⟩
      by_contra hcc
      have hne : irreducibleComponent c ≠ irreducibleComponent y' := by
        intro hEq
        exact hcc (hEq ▸ mem_irreducibleComponent)
      exact haR (Set.mem_iUnion₂.2 ⟨irreducibleComponent c,
        ⟨irreducibleComponent_mem_irreducibleComponents c, hne⟩,
        ⟨c, mem_irreducibleComponent, rfl⟩⟩)
    · rintro a ⟨haim, haR⟩
      refine ⟨?_, haR⟩
      rw [← hrange]
      exact Set.image_subset_range _ _ haim
  have hfinal : IsIrreducible ((↑Z.support : Set ↥T.scheme) ∩
      (⋃ C ∈ {C : Set ↥Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧
        C ≠ irreducibleComponent y'}, (⇑(Z.subschemeι).base) '' C)ᶜ) := by
    rw [hSV]
    exact isIrreducible_inter_isOpen_consolidated414
      (isIrreducible_irreducibleComponent.image _ hemb.continuous.continuousOn)
      hRclosed.isOpen_compl ⟨y, ⟨y', hy'C, hy'⟩, hyR⟩
  exact ⟨⟨_, hRclosed.isOpen_compl⟩, hyR, hfinal⟩


end

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (Z : T.scheme.IdealSheafData) (hsm : Smooth (Z.subschemeι ≫ T.structMap)) (hsnc : HasStrictNormalCrossingsWith T.structMap Z T.boundary) (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (hbl : Blowup.IsBlowupAlongIdealSheaf π Z)
include hG hT hsm hsnc hbl

private theorem isMonomialIn_comap_blowup_consolidated414 (Mon : T.scheme.IdealSheafData) (hMon : IsMonomialIn T.boundary Mon) :
    IsMonomialIn (List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z])
      (Mon.comap π) := by
  have hExcMem : Blowup.exceptionalIdeal π Z ∈
      List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z] := by simp
  have hSTmem : ∀ D₀ ∈ T.boundary, Blowup.strictTransform π Z D₀ ∈
      List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z] := by
    intro D₀ hD₀
    exact List.mem_append_left _ (List.mem_map.2 ⟨D₀, hD₀, rfl⟩)
  have hfac : ∀ D₀ ∈ T.boundary, ∀ x' : ↥X',
      ∃ (U : X'.Opens) (ε : ℕ), x' ∈ U ∧
        (D₀.comap π).comap U.ι =
          (Blowup.strictTransform π Z D₀).comap U.ι * (Blowup.exceptionalIdeal π Z).comap U.ι ^ ε := by
    intro D₀ hD₀ x'
    obtain ⟨U, ε, hxU, _, _, hEq⟩ :=
      hG.monomialInputs.blowup_total_transform T hT Z hsm hsnc X' π hbl D₀ hD₀ x'
    exact ⟨U, ε, hxU, hEq⟩
  have hmonD : ∀ D₀ ∈ T.boundary,
      IsMonomialIn (List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z])
        (D₀.comap π) := fun D₀ hD₀ =>
    isMonomialIn_of_locally_eq_mul_pow_consolidated414 _ _ _ _ (hSTmem D₀ hD₀) hExcMem (hfac D₀ hD₀)
  refine isMonomialIn_of_forall_mem_consolidated414 ?_ (hMon.comap π)
  intro D hD
  obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD
  exact hmonD D₀ hD₀

private theorem exists_opens_comap_list_prod_eq_mul_exceptionalIdeal_pow_consolidated414 (x' : ↥X') (z : ↥T.scheme)
    (hz1 : ∀ D ∈ T.boundary,
      (∃ V : T.scheme.Opens, π.base x' ∈ V ∧
        (↑Z.support : Set ↥T.scheme) ∩ (↑V : Set ↥T.scheme) ⊆ (↑D.support : Set ↥T.scheme)) →
      z ∈ D.support)
    (hz0 : ∀ D ∈ T.boundary,
      ¬ (∃ V : T.scheme.Opens, π.base x' ∈ V ∧
        (↑Z.support : Set ↥T.scheme) ∩ (↑V : Set ↥T.scheme) ⊆ (↑D.support : Set ↥T.scheme)) →
      z ∉ D.support) :
    ∀ L : List T.scheme.IdealSheafData, (∀ D ∈ L, D ∈ T.boundary) →
      ∃ (U : X'.Opens) (m : U.toScheme.IdealSheafData) (s : ℕ), x' ∈ U ∧
        m ∈ Submonoid.closure ((fun D : X'.IdealSheafData => D.comap U.ι) ''
          {D | D ∈ List.map (Blowup.strictTransform π Z) T.boundary}) ∧
        ((L.prod).comap π).comap U.ι = m * ((Blowup.exceptionalIdeal π Z).comap U.ι) ^ s ∧
        orderAt (L.prod) z = (s : ℕ∞) := by
  have := hT.charZero
  have := hT.smooth
  intro L
  induction L with
  | nil =>
      intro _
      refine ⟨⊤, 1, 0, trivial, one_mem _, ?_, ?_⟩
      · rw [List.prod_nil, comap_one_consolidated414, comap_one_consolidated414, pow_zero, mul_one]
      · rw [List.prod_nil, Scheme.IdealSheafData.one_eq_top, orderAt_top]
        simp
  | cons D L ih =>
      intro hall
      have hD : D ∈ T.boundary := hall D List.mem_cons_self
      obtain ⟨U₁, m₁, s₁, hx1, hm1, heq1, hord1⟩ :=
        ih (fun D' hD' => hall D' (List.mem_cons_of_mem _ hD'))
      obtain ⟨U₂, ε, hx2, hε01, hεiff, heq2⟩ :=
        hG.monomialInputs.blowup_total_transform T hT Z hsm hsnc X' π hbl D hD x'
      have hDeq : (D.comap π).comap (U₁ ⊓ U₂).ι
          = (Blowup.strictTransform π Z D).comap (U₁ ⊓ U₂).ι
            * ((Blowup.exceptionalIdeal π Z).comap (U₁ ⊓ U₂).ι) ^ ε := by
        have h : ((D.comap π).comap U₂.ι).comap
              (X'.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂))
            = ((Blowup.strictTransform π Z D).comap U₂.ι
              * ((Blowup.exceptionalIdeal π Z).comap U₂.ι) ^ ε).comap
                (X'.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) := by
          rw [heq2]
        simp only [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow,
          comap_homOfLE_consolidated414] at h
        exact h
      have hLeq : ((L.prod).comap π).comap (U₁ ⊓ U₂).ι
          = (m₁.comap (X'.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)))
            * ((Blowup.exceptionalIdeal π Z).comap (U₁ ⊓ U₂).ι) ^ s₁ := by
        have h : (((L.prod).comap π).comap U₁.ι).comap
              (X'.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
            = (m₁ * ((Blowup.exceptionalIdeal π Z).comap U₁.ι) ^ s₁).comap
                (X'.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) := by
          rw [heq1]
        simp only [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow,
          comap_homOfLE_consolidated414] at h
        exact h
      have hordD : orderAt D z = (ε : ℕ∞) := by
        rcases hε01 with h0 | h1
        · have hnotex : ¬ (∃ V : T.scheme.Opens, π.base x' ∈ V ∧
              (↑Z.support : Set ↥T.scheme) ∩ (↑V : Set ↥T.scheme)
                ⊆ (↑D.support : Set ↥T.scheme)) := by
            intro hex
            have h1' : ε = 1 := hεiff.2 hex
            rw [h0] at h1'
            simp at h1'
          have hzn := hz0 D hD hnotex
          rw [h0, (orderAt_eq_zero_iff_not_mem_support D z).2 hzn]
          simp
        · have hzm := hz1 D hD (hεiff.1 h1)
          rw [h1, MonomialChart.orderAt_boundary_eq_one T hT D hD z hzm]
          simp
      refine ⟨U₁ ⊓ U₂, (Blowup.strictTransform π Z D).comap (U₁ ⊓ U₂).ι
        * (m₁.comap (X'.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))), ε + s₁, ⟨hx1, hx2⟩, ?_, ?_, ?_⟩
      · refine mul_mem (Submonoid.subset_closure ⟨Blowup.strictTransform π Z D, ?_, rfl⟩) ?_
        · exact List.mem_map.2 ⟨D, hD, rfl⟩
        · exact comap_homOfLE_mem_closure_comap_consolidated414
            (E := List.map (Blowup.strictTransform π Z) T.boundary) inf_le_left m₁ hm1
      · rw [List.prod_cons, Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_mul,
          hDeq, hLeq, pow_add, mul_mul_mul_comm]
      · rw [List.prod_cons, orderAt_mul T.base T.structMap D L.prod z, hordD, hord1,
          Nat.cast_add]

theorem isMonomialIn_of_exceptionalIdeal_pow_mul_eq_comap (Mon : T.scheme.IdealSheafData) (hMon : IsMonomialIn T.boundary Mon)
    (d : ℕ) (hd : Mon ≤ Z ^ d)
    (C : X'.IdealSheafData) (hC : Blowup.exceptionalIdeal π Z ^ d * C = Mon.comap π) :
    IsMonomialIn (List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]) C := by
  have := hT.charZero
  have := hT.smooth
  have hEC : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hbl
  have hExcMem : Blowup.exceptionalIdeal π Z ∈
      List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z] := by simp
  have hMonComap := isMonomialIn_comap_blowup_consolidated414 hG T hT Z hsm hsnc X' π hbl Mon hMon
  have hsubimg : ∀ U : X'.Opens,
      ((fun D : X'.IdealSheafData => D.comap U.ι) ''
          {D | D ∈ List.map (Blowup.strictTransform π Z) T.boundary})
        ⊆ ((fun D : X'.IdealSheafData => D.comap U.ι) ''
          {D | D ∈ List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]}) := by
    intro U
    exact Set.image_mono (fun D hD => List.mem_append_left _ hD)
  rw [isMonomialIn_iff_forall_exists_mem_closure]
  intro x'
  by_cases hx'E : x' ∈ (Blowup.exceptionalIdeal π Z).support
  · have hyZ : (π.base x') ∈ (↑Z.support : Set ↥T.scheme) := by
      have h0 : (↑(Blowup.exceptionalIdeal π Z).support : Set ↥X')
          = ⇑π.base ⁻¹' (↑Z.support : Set ↥T.scheme) := by
        rw [Blowup.exceptionalIdeal_eq_comap, support_comap_coe_consolidated414]
      have h1 : x' ∈ (↑(Blowup.exceptionalIdeal π Z).support : Set ↥X') := hx'E
      rw [h0] at h1
      exact h1
    obtain ⟨V₀, hyV₀, hirr₀⟩ :=
      exists_opens_isIrreducible_support_inter_consolidated414 T hT Z hsm (π.base x') hyZ
    obtain ⟨W, hyW, hWmem⟩ :=
      (isMonomialIn_iff_forall_exists_mem_closure T.boundary Mon).1 hMon (π.base x')
    obtain ⟨L, hLsub, hLeq⟩ := exists_list_prod_eq_of_mem_closure_consolidated414 W.ι T.boundary hWmem
    have hWeq : Mon.comap W.ι = (L.prod).comap W.ι := by
      rw [comap_list_prod_consolidated414 W.ι L]
      exact hLeq
    have hyS₀ : π.base x' ∈ ((↑Z.support : Set ↥T.scheme) ∩ (↑V₀ : Set ↥T.scheme))
        ∩ (↑W : Set ↥T.scheme) := ⟨⟨hyZ, hyV₀⟩, hyW⟩
    have hirr : IsIrreducible (((↑Z.support : Set ↥T.scheme) ∩ (↑V₀ : Set ↥T.scheme))
        ∩ (↑W : Set ↥T.scheme)) := isIrreducible_inter_isOpen_consolidated414 hirr₀ W.2 ⟨_, hyS₀⟩
    obtain ⟨η, hη⟩ := exists_closure_singleton_eq_closure_consolidated414 T.scheme hirr
    have hηZ : η ∈ (↑Z.support : Set ↥T.scheme) := by
      have h1 : closure (((↑Z.support : Set ↥T.scheme) ∩ (↑V₀ : Set ↥T.scheme))
          ∩ (↑W : Set ↥T.scheme)) ⊆ (↑Z.support : Set ↥T.scheme) :=
        closure_minimal (fun a ha => ha.1.1) (Z.support).2
      have h2 : η ∈ closure (((↑Z.support : Set ↥T.scheme) ∩ (↑V₀ : Set ↥T.scheme))
          ∩ (↑W : Set ↥T.scheme)) := by
        rw [← hη]
        exact subset_closure rfl
      exact h1 h2
    have hηW : η ∈ W := mem_of_isOpen_of_closure_singleton_eq_consolidated414 hη W.2 ⟨_, hyS₀, hyW⟩
    have hz1 : ∀ D ∈ T.boundary, (∃ V : T.scheme.Opens, π.base x' ∈ V ∧
        (↑Z.support : Set ↥T.scheme) ∩ (↑V : Set ↥T.scheme) ⊆ (↑D.support : Set ↥T.scheme)) →
        η ∈ D.support := by
      rintro D hD ⟨V, hyV, hsub⟩
      have hηV : η ∈ V := mem_of_isOpen_of_closure_singleton_eq_consolidated414 hη V.2 ⟨_, hyS₀, hyV⟩
      exact hsub ⟨hηZ, hηV⟩
    have hz0 : ∀ D ∈ T.boundary, ¬ (∃ V : T.scheme.Opens, π.base x' ∈ V ∧
        (↑Z.support : Set ↥T.scheme) ∩ (↑V : Set ↥T.scheme) ⊆ (↑D.support : Set ↥T.scheme)) →
        η ∉ D.support := by
      intro D _ hnot hmem
      refine hnot ⟨V₀ ⊓ W, ⟨hyV₀, hyW⟩, ?_⟩
      have hsub := subset_of_closure_singleton_eq_closure_consolidated414 hη (D.support).2 hmem
      intro a ha
      have ha1 : a ∈ (↑Z.support : Set ↥T.scheme) := ha.1
      have ha2 : a ∈ (↑(V₀ ⊓ W) : Set ↥T.scheme) := ha.2
      rw [TopologicalSpace.Opens.coe_inf] at ha2
      exact hsub ⟨⟨ha1, ha2.1⟩, ha2.2⟩
    obtain ⟨U₂, m, s, hx2, hmclo, hUeq, hords⟩ :=
      exists_opens_comap_list_prod_eq_mul_exceptionalIdeal_pow_consolidated414 hG T hT Z hsm hsnc X' π hbl x' η hz1 hz0 L hLsub
    have hMonord : ((d : ℕ) : ℕ∞) ≤ orderAt Mon η := by
      have h1 : η ∈ orderAtLeastLocus Z 1 := (mem_orderAtLeastLocus_one_iff Z η).2 hηZ
      have h2 : η ∈ orderAtLeastLocus (Z ^ d) (d * 1) := orderAtLeastLocus_subset_orderAtLeastLocus_pow Z d 1 h1
      rw [mul_one] at h2
      have h3 : ((d : ℕ) : ℕ∞) ≤ orderAt (Z ^ d) η := (mem_orderAtLeastLocus_iff _ _ _).1 h2
      exact le_trans h3 (orderAt_le_of_le hd η)
    have hMonLprod : orderAt Mon η = orderAt (L.prod) η := by
      rw [← orderAt_comap_opens_ι_consolidated414 W Mon η hηW, ← orderAt_comap_opens_ι_consolidated414 W (L.prod) η hηW, hWeq]
    have hds : d ≤ s := by
      rw [hMonLprod, hords] at hMonord
      exact_mod_cast hMonord
    refine ⟨U₂ ⊓ π ⁻¹ᵁ W, ⟨hx2, hyW⟩, ?_⟩
    have hkey : ∀ J : T.scheme.IdealSheafData,
        (J.comap π).comap (U₂ ⊓ π ⁻¹ᵁ W).ι
          = (J.comap W.ι).comap (π.resLE W (U₂ ⊓ π ⁻¹ᵁ W) inf_le_right) := by
      intro J
      rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        Scheme.Hom.resLE_comp_ι]
    have hMonL : (Mon.comap π).comap (U₂ ⊓ π ⁻¹ᵁ W).ι
        = ((L.prod).comap π).comap (U₂ ⊓ π ⁻¹ᵁ W).ι := by
      rw [hkey Mon, hkey (L.prod), hWeq]
    have hfact : ((L.prod).comap π).comap (U₂ ⊓ π ⁻¹ᵁ W).ι
        = (m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂)))
          * ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ s := by
      have h : (((L.prod).comap π).comap U₂.ι).comap
            (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂))
          = (m * ((Blowup.exceptionalIdeal π Z).comap U₂.ι) ^ s).comap
              (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂)) := by
        rw [hUeq]
      simp only [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow,
        comap_homOfLE_consolidated414] at h
      exact h
    have hm' : (m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂))) ∈
        Submonoid.closure ((fun D : X'.IdealSheafData => D.comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ''
          {D | D ∈ List.map (Blowup.strictTransform π Z) T.boundary}) :=
      comap_homOfLE_mem_closure_comap_consolidated414 (E := List.map (Blowup.strictTransform π Z) T.boundary)
        inf_le_left m hmclo
    have hexp : d + (s - d) = s := Nat.add_sub_cancel' hds
    have hCmul : ((Blowup.exceptionalIdeal π Z) ^ d).comap (U₂ ⊓ π ⁻¹ᵁ W).ι
          * (C.comap (U₂ ⊓ π ⁻¹ᵁ W).ι)
        = ((Blowup.exceptionalIdeal π Z) ^ d).comap (U₂ ⊓ π ⁻¹ᵁ W).ι
          * ((m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂)))
            * ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ (s - d)) := by
      calc ((Blowup.exceptionalIdeal π Z) ^ d).comap (U₂ ⊓ π ⁻¹ᵁ W).ι
              * (C.comap (U₂ ⊓ π ⁻¹ᵁ W).ι)
          = (((Blowup.exceptionalIdeal π Z) ^ d) * C).comap (U₂ ⊓ π ⁻¹ᵁ W).ι := by
            rw [Scheme.IdealSheafData.comap_mul]
        _ = (Mon.comap π).comap (U₂ ⊓ π ⁻¹ᵁ W).ι := by rw [hC]
        _ = ((L.prod).comap π).comap (U₂ ⊓ π ⁻¹ᵁ W).ι := hMonL
        _ = (m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂)))
              * ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ s := hfact
        _ = (m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂)))
              * ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ (d + (s - d)) := by
            rw [hexp]
        _ = ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ d
              * ((m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂)))
                * ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ (s - d)) := by
            rw [pow_add]
            exact mul_left_comm _ _ _
        _ = ((Blowup.exceptionalIdeal π Z) ^ d).comap (U₂ ⊓ π ⁻¹ᵁ W).ι
              * ((m.comap (X'.homOfLE (inf_le_left : U₂ ⊓ π ⁻¹ᵁ W ≤ U₂)))
                * ((Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ^ (s - d)) := by
            rw [Scheme.IdealSheafData.comap_pow]
    have hCeq := (hEC.pow d).eq_of_mul_eq_mul_comap_opensι (U₂ ⊓ π ⁻¹ᵁ W) hCmul
    rw [hCeq]
    have hEmem : (Blowup.exceptionalIdeal π Z).comap (U₂ ⊓ π ⁻¹ᵁ W).ι ∈
        ((fun D : X'.IdealSheafData => D.comap (U₂ ⊓ π ⁻¹ᵁ W).ι) ''
          {D | D ∈ List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]}) :=
      ⟨Blowup.exceptionalIdeal π Z, hExcMem, rfl⟩
    refine mul_mem (Submonoid.closure_mono (hsubimg (U₂ ⊓ π ⁻¹ᵁ W)) hm') ?_
    exact pow_mem (Submonoid.subset_closure hEmem) (s - d)
  · obtain ⟨U₀, hx0, hmem0⟩ :=
      (isMonomialIn_iff_forall_exists_mem_closure _ _).1 hMonComap x'
    have hxVc : x' ∈ (Blowup.exceptionalIdeal π Z).support.compl :=
      (mem_closeds_compl_iff_consolidated414 _ _).2 hx'E
    refine ⟨U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl, ⟨hx0, hxVc⟩, ?_⟩
    have hE1 : (Blowup.exceptionalIdeal π Z).comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι = 1 := by
      refine comap_eq_one_of_forall_notMem_support_consolidated414 _ _ ?_
      intro x hx
      exact (mem_closeds_compl_iff_consolidated414 _ _).1 hx.2
    have hCU : C.comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι
        = (Mon.comap π).comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι := by
      calc C.comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι
          = (1 : (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).toScheme.IdealSheafData) ^ d
              * C.comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι := by
            rw [one_pow, one_mul]
        _ = ((Blowup.exceptionalIdeal π Z).comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι) ^ d
              * C.comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι := by rw [hE1]
        _ = (((Blowup.exceptionalIdeal π Z) ^ d) * C).comap
              (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι := by
            rw [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow]
        _ = (Mon.comap π).comap (U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl).ι := by rw [hC]
    rw [hCU]
    have hfin := comap_homOfLE_mem_closure_comap_consolidated414
      (E := List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z])
      (inf_le_left : U₀ ⊓ (Blowup.exceptionalIdeal π Z).support.compl ≤ U₀) _ hmem0
    rwa [comap_homOfLE_consolidated414] at hfin

theorem isMonomialSplitting_of_isBlowupAlongIdealSheaf (Bd Mon Ad : T.scheme.IdealSheafData) (m sdeg : ℕ)
    (hsplit : IsMonomialSplitting T.boundary Bd Mon Ad)
    (hZsub : (↑Z.support : Set ↥T.scheme) ⊆ orderAtLeastLocus Bd m)
    (hordA : ∀ x ∈ Z.support, orderAt Ad x = (sdeg : ℕ∞))
    (B' : X'.IdealSheafData) (hB' : Blowup.exceptionalIdeal π Z ^ m * B' = Bd.comap π)
    (A' : X'.IdealSheafData) (hA' : Blowup.exceptionalIdeal π Z ^ sdeg * A' = Ad.comap π)
    (C : X'.IdealSheafData)
    (hC : Blowup.exceptionalIdeal π Z ^ m * C = Mon.comap π * Blowup.exceptionalIdeal π Z ^ sdeg) :
    IsMonomialSplitting
      (List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z]) B' C A' := by
  have := hT.charZero
  have := hT.smooth
  have hEC : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hbl
  have hExcMem : Blowup.exceptionalIdeal π Z ∈
      List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z] := by
    simp
  have hSTmem : ∀ D₀ ∈ T.boundary, Blowup.strictTransform π Z D₀ ∈
      List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z] := by
    intro D₀ hD₀
    exact List.mem_append_left _ (List.mem_map.2 ⟨D₀, hD₀, rfl⟩)
  have hfac : ∀ D₀ ∈ T.boundary, ∀ x' : ↥X',
      ∃ (U : X'.Opens) (ε : ℕ), x' ∈ U ∧
        (D₀.comap π).comap U.ι =
          (Blowup.strictTransform π Z D₀).comap U.ι * (Blowup.exceptionalIdeal π Z).comap U.ι ^ ε := by
    intro D₀ hD₀ x'
    obtain ⟨U, ε, hxU, _, _, hEq⟩ :=
      hG.monomialInputs.blowup_total_transform T hT Z hsm hsnc X' π hbl D₀ hD₀ x'
    exact ⟨U, ε, hxU, hEq⟩
  have hmonD : ∀ D₀ ∈ T.boundary,
      IsMonomialIn (List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z])
        (D₀.comap π) := by
    intro D₀ hD₀
    exact isMonomialIn_of_locally_eq_mul_pow_consolidated414 _ _ _ _ (hSTmem D₀ hD₀) hExcMem (hfac D₀ hD₀)
  have hmonMon : IsMonomialIn (List.map (Blowup.strictTransform π Z) T.boundary ++ [Blowup.exceptionalIdeal π Z])
      (Mon.comap π) := by
    refine isMonomialIn_of_forall_mem_consolidated414 ?_ (hsplit.monomial.comap π)
    intro D hD
    obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD
    exact hmonD D₀ hD₀
  have key : Blowup.exceptionalIdeal π Z ^ m * B' = Blowup.exceptionalIdeal π Z ^ m * (C * A') := by
    rw [← mul_assoc (Blowup.exceptionalIdeal π Z ^ m) C A', hC, hB', hsplit.eq_mul,
      Scheme.IdealSheafData.comap_mul,
      mul_assoc (Mon.comap π) (Blowup.exceptionalIdeal π Z ^ sdeg) A', hA']
  refine ⟨(hEC.pow m).eq_of_mul_eq_mul key, ?_, ?_, ?_⟩
  · intro x hx
    have hx1 : x ∈ (↑(Blowup.exceptionalIdeal π Z ^ m * C).support : Set ↥X') :=
      support_subset_support_mul_right_consolidated414 _ C hx
    rw [hC] at hx1
    rcases support_mul_subset_consolidated414 _ _ hx1 with h1 | h2
    · rw [support_comap_coe_consolidated414] at h1
      obtain ⟨D₀, hD₀, hxD⟩ := Set.mem_iUnion₂.1 (hsplit.monomial_support h1)
      have hx' : x ∈ (↑((D₀.comap π)).support : Set ↥X') := by
        rw [support_comap_coe_consolidated414]
        exact hxD
      rcases support_subset_union_of_locally_eq_mul_pow_consolidated414 _ _ _ (hfac D₀ hD₀) hx' with h3 | h4
      · exact Set.mem_iUnion₂.2 ⟨_, hSTmem D₀ hD₀, h3⟩
      · exact Set.mem_iUnion₂.2 ⟨_, hExcMem, h4⟩
    · exact Set.mem_iUnion₂.2 ⟨_, hExcMem, support_pow_subset_consolidated414 _ _ h2⟩
  · rcases Nat.lt_or_ge sdeg m with hms | hms
    · have hsub : (↑Z.support : Set ↥T.scheme) ⊆ orderAtLeastLocus Mon (m - sdeg) := by
        intro x hx
        refine (mem_orderAtLeastLocus_iff Mon (m - sdeg) x).2 ?_
        have h1 : (m : ℕ∞) ≤ orderAt Bd x := (mem_orderAtLeastLocus_iff Bd m x).1 (hZsub hx)
        rw [hsplit.orderAt_eq_add T.structMap x, hordA x hx] at h1
        exact cast_sub_le_of_cast_le_add_consolidated414 h1
      have hle : Mon ≤ Z ^ (m - sdeg) :=
        le_pow_of_hasStrictNormalCrossingsWith T.structMap Z Mon T.boundary hsnc (m - sdeg) hsub
      have hC2 : Blowup.exceptionalIdeal π Z ^ (m - sdeg) * C = Mon.comap π := by
        refine (hEC.pow sdeg).eq_of_mul_eq_mul ?_
        rw [← mul_assoc (Blowup.exceptionalIdeal π Z ^ sdeg) (Blowup.exceptionalIdeal π Z ^ (m - sdeg)) C,
          ← pow_add, Nat.add_sub_cancel' hms.le, hC,
          mul_comm (Mon.comap π) (Blowup.exceptionalIdeal π Z ^ sdeg)]
      exact isMonomialIn_of_exceptionalIdeal_pow_mul_eq_comap hG T hT Z hsm hsnc X' π hbl Mon
        hsplit.monomial (m - sdeg) hle C hC2
    · have hC3 : C = Mon.comap π * Blowup.exceptionalIdeal π Z ^ (sdeg - m) := by
        refine (hEC.pow m).eq_of_mul_eq_mul ?_
        rw [hC,
          ← mul_assoc (Blowup.exceptionalIdeal π Z ^ m) (Mon.comap π)
            (Blowup.exceptionalIdeal π Z ^ (sdeg - m)),
          mul_comm (Blowup.exceptionalIdeal π Z ^ m) (Mon.comap π),
          mul_assoc (Mon.comap π) (Blowup.exceptionalIdeal π Z ^ m)
            (Blowup.exceptionalIdeal π Z ^ (sdeg - m)),
          ← pow_add, Nat.add_sub_cancel' hms]
      rw [hC3]
      exact isMonomialIn_mul_consolidated414 _ hmonMon (isMonomialIn_pow_consolidated414 _ (isMonomialIn_of_mem_consolidated414 hExcMem) _)
  · rintro D hD Cs hCirr hCsubD hCmax hCA
    rcases List.mem_append.1 hD with hD' | hD'
    · obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD'
      obtain ⟨η', C0, hCeq, _, hC0comp, _, hC0eq⟩ :=
        hG.strictTransform_components T hT Z hsm hsnc X' π hbl D₀ hD₀ Cs
          (isIrreducibleComponentOf_of_maximal_consolidated414 hCirr hCsubD hCmax)
      obtain ⟨hc1, hc2, hc3⟩ := isIrreducible_subset_maximal_of_isIrreducibleComponentOf_consolidated414 hC0comp
      have hηC : η' ∈ Cs := by
        rw [hCeq]
        exact subset_closure (Set.mem_singleton η')
      have h2 : η' ∈ (↑(Ad.comap π).support : Set ↥X') := by
        rw [← hA']
        exact support_subset_support_mul_right_consolidated414 _ _ (hCA hηC)
      rw [support_comap_coe_consolidated414] at h2
      have hsub0 : C0 ⊆ (↑Ad.support : Set ↥T.scheme) := by
        rw [hC0eq]
        exact closure_minimal (Set.singleton_subset_iff.2 h2) Ad.support.2
      exact hsplit.transversal D₀ hD₀ C0 hc1 hc2 hc3 hsub0
    · rw [List.mem_singleton] at hD'
      subst hD'
      exact hG.exceptional_components_not_subset T hT Z hsm hsnc X' π hbl Ad sdeg hordA A' hA'
        Cs (isIrreducibleComponentOf_of_maximal_consolidated414 hCirr hCsubD hCmax) hCA


end

end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.OrderOffExceptionalDivisor
section

open TopologicalSpace


theorem orderAt_comap_eq_of_notMem_exceptionalIdeal
    (T : MarkedIdealWithBoundary.{u}) (_hT : T.IsAdmissible) (Z : T.scheme.IdealSheafData)
    (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (x' : X') (hx' : x' ∉ (Blowup.exceptionalIdeal π Z).support)
    (A : T.scheme.IdealSheafData) :
    orderAt (A.comap π) x' = orderAt A (π.base x') := by
  have hx : π.base x' ∉ Z.support := by
    intro hc
    apply hx'
    rw [Blowup.exceptionalIdeal_eq_comap]
    exact Scheme.IdealSheafData.mem_support_comap.mpr hc
  haveI : IsIso (π.stalkMap x') := isIso_stalkMap_of_isBlowupAlongIdealSheaf π Z hπ x' hx
  exact orderAt_comap_of_isIso_stalkMap π A x'

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SeparateBoundaryFieldBaseChange
section

open CategoryTheory.Limits

section

def IsBaseChangeInherited (P : ℕ → Prop) : Prop :=
  ∀ (R : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] [CharZero L] (f : R.base →+* L),
    R.IsAdmissible → P R.krullDimSucc →
    (∀ x : ↥R.scheme, orderAt R.ideal x ≤ (R.mult : ℕ∞)) →
    (∀ hft : LocallyOfFiniteType R.structMap, R.IsBalanced hft) →
      (R.baseChange L f).IsAdmissible ∧
      P (R.baseChange L f).krullDimSucc ∧
      (∀ x : ↥(R.baseChange L f).scheme,
        orderAt (R.baseChange L f).ideal x ≤ (R.mult : ℕ∞)) ∧
      (∀ hft : LocallyOfFiniteType (R.baseChange L f).structMap,
        (R.baseChange L f).IsBalanced hft)

theorem MarkedIdealWithBoundary.length_boundary_baseChange (S : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L]
    (f : S.base →+* L) :
    (S.baseChange L f).boundary.length = S.boundary.length := by
  have h : (S.baseChange L f).boundary.length
      = (List.map (fun D => D.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f)))
          S.boundary).length :=
    congrArg List.length (S.baseChange_boundary L f)
  rw [h]
  simp

namespace BoundaryLoopFieldBaseChange

private theorem lt_length_nil_append_boundary_consolidated462 (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (j : ℕ)
    (hj : j < S.boundary.length) :
    j < (([] : List (s.obj s.length).IdealSheafData) ++ (s.boundary s.length).drop 0).length := by
  have h : (s.boundary s.length).length = S.boundary.length + s.length :=
    s.boundary_length s.length le_rfl
  have h2 : (([] : List (s.obj s.length).IdealSheafData) ++ (s.boundary s.length).drop 0).length
      = S.boundary.length + s.length := by
    simp [h]
  rw [h2]
  omega

private theorem nonempty_strictPullback_of_length_eq_zero_consolidated462 {X' X : Scheme.{u}} (g : X' ⟶ X)
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (ht : t.length = 0) (hs : s.length = 0) :
    Nonempty (StrictPullbackBlowupSeq g t s) :=
  ⟨{ comp := fun i hi =>
        eqToHom (congrArg t.schemeAt (show i = 0 by omega)) ≫ t.isoZero.hom ≫ g ≫ s.isoZero.inv ≫
          eqToHom (congrArg s.schemeAt (show (0 : ℕ) = i by omega))
     comp_zero := by simp
     pullback := fun i hi => absurd hi (by omega)
     length_eq := by rw [ht, hs]
     center_eq := fun i hi => absurd hi (by omega) }⟩

private theorem length_eq_of_strictPullbackBlowupSeq_consolidated462
    {k k' : Type u} [Field k] [Field k'] {X X' : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {p' : X' ⟶ Spec (CommRingCat.of k')}
    {I : X.IdealSheafData} {I' : X'.IdealSheafData} {m m' : ℕ}
    {E : List X.IdealSheafData} {E' : List X'.IdealSheafData} {g : X' ⟶ X}
    (s : MarkedBlowupSequenceData p I m E) (t : MarkedBlowupSequenceData p' I' m' E')
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    t.length = s.length := by
  have h := D.length_eq
  rwa [MarkedBlowupSequenceData.toMarkedSequence_length, MarkedBlowupSequenceData.toMarkedSequence_length] at h

private def strictPullbackMapAt_consolidated462
    {k k' : Type u} [Field k] [Field k'] {X X' : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {p' : X' ⟶ Spec (CommRingCat.of k')}
    {I : X.IdealSheafData} {I' : X'.IdealSheafData} {m m' : ℕ}
    {E : List X.IdealSheafData} {E' : List X'.IdealSheafData} {g : X' ⟶ X}
    (s : MarkedBlowupSequenceData p I m E) (t : MarkedBlowupSequenceData p' I' m' E')
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (i : ℕ) (hi : i ≤ t.length) : t.obj i ⟶ s.obj i :=
  D.comp i (t.le_toSequenceOfBlowups_length hi)

private theorem strictPullbackMapAt_zero_comp_isoObjZero_hom_consolidated462
    {k k' : Type u} [Field k] [Field k'] {X X' : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {p' : X' ⟶ Spec (CommRingCat.of k')}
    {I : X.IdealSheafData} {I' : X'.IdealSheafData} {m m' : ℕ}
    {E : List X.IdealSheafData} {E' : List X'.IdealSheafData} {g : X' ⟶ X}
    (s : MarkedBlowupSequenceData p I m E) (t : MarkedBlowupSequenceData p' I' m' E')
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (h0 : 0 ≤ t.length) :
    strictPullbackMapAt_consolidated462 s t D 0 h0 ≫ s.isoZero.hom = t.isoZero.hom ≫ g :=
  D.comp_zero

private theorem iteratedStrictTransform_comap_eqToHom_consolidated462 {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) (a b : ℕ) (hab : a = b)
    (hh : s.obj a = s.obj b) :
    (MaxContactReduction.iteratedStrictTransform s H b).comap (eqToHom hh) = MaxContactReduction.iteratedStrictTransform s H a := by
  subst hab
  simp

section
variable {k k' : Type u} [Field k] [Field k'] {X X' : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {p' : X' ⟶ Spec (CommRingCat.of k')} {I : X.IdealSheafData} {I' : X'.IdealSheafData} {m m' : ℕ} {E : List X.IdealSheafData} {E' : List X'.IdealSheafData} {g : X' ⟶ X} (hflat : Flat g) (s : MarkedBlowupSequenceData p I m E) (t : MarkedBlowupSequenceData p' I' m' E') (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups) (hNs : ∀ i ≤ s.length, IsLocallyNoetherian (s.obj i)) (hNt : ∀ i ≤ t.length, IsLocallyNoetherian (t.obj i)) (H : X.IdealSheafData)
include hflat hNs hNt

private theorem iteratedStrictTransform_comap_consolidated462
    :
    ∀ (i : ℕ) (hi : i ≤ t.length),
      MaxContactReduction.iteratedStrictTransform t (H.comap g) i
        = (MaxContactReduction.iteratedStrictTransform s H i).comap (strictPullbackMapAt_consolidated462 s t D i hi) := by
  have := hflat
  have hlen := length_eq_of_strictPullbackBlowupSeq_consolidated462 s t D
  intro i
  induction i with
  | zero =>
    intro hi
    rw [MaxContactReduction.iteratedStrictTransform_zero, MaxContactReduction.iteratedStrictTransform_zero,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      strictPullbackMapAt_zero_comp_isoObjZero_hom_consolidated462 s t D hi]
  | succ i ih =>
    intro hi
    have hlt : i < t.length := hi
    have hle : i ≤ t.length := le_of_lt hlt
    have := hNs (i + 1) (by omega)
    have := hNt (i + 1) (by omega)
    have hflati : Flat (strictPullbackMapAt_consolidated462 s t D i hle) :=
      D.flat_map i (t.le_toSequenceOfBlowups_length hle)
    have := hflati
    have hsq : IsPullback (strictPullbackMapAt_consolidated462 s t D (i + 1) hi) (t.map i) (s.map i)
        (strictPullbackMapAt_consolidated462 s t D i hle) := by
      have h := D.pullback i (t.lt_toSequenceOfBlowups_length hlt)
      have key : ∀ (a : t.obj (i + 1) ⟶ t.obj i) (b : s.obj (i + 1) ⟶ s.obj i),
          a = t.map i → b = s.map i →
          IsPullback (strictPullbackMapAt_consolidated462 s t D (i + 1) hi) a b (strictPullbackMapAt_consolidated462 s t D i hle) →
          IsPullback (strictPullbackMapAt_consolidated462 s t D (i + 1) hi) (t.map i) (s.map i) (strictPullbackMapAt_consolidated462 s t D i hle) := by
        rintro a b rfl rfl hh
        exact hh
      exact key _ _ (MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism t i)
        (MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism s i) h
    have hc : t.center i = (s.center i).comap (strictPullbackMapAt_consolidated462 s t D i hle) := by
      have h := D.center_eq i (t.lt_toSequenceOfBlowups_length hlt)
      have key : ∀ (a : (t.obj i).IdealSheafData) (b : (s.obj i).IdealSheafData),
          a = t.center i → b = s.center i →
          a = b.comap (strictPullbackMapAt_consolidated462 s t D i hle) →
          t.center i = (s.center i).comap (strictPullbackMapAt_consolidated462 s t D i hle) := by
        rintro a b rfl rfl hh
        exact hh
      exact key _ _ (MarkedBlowupSequenceData.toMarkedSequence_center t i)
        (MarkedBlowupSequenceData.toMarkedSequence_center s i) h
    have key := comap_strictTransform_of_flat_of_isLocallyNoetherian (s.map i)
      (strictPullbackMapAt_consolidated462 s t D i hle) (t.map i) (strictPullbackMapAt_consolidated462 s t D (i + 1) hi) hsq (s.center i)
      (MaxContactReduction.iteratedStrictTransform s H i) (s.isBlowup i (by omega))
    rw [MaxContactReduction.iteratedStrictTransform_succ, MaxContactReduction.iteratedStrictTransform_succ, key, ih hle, hc]

private theorem strictTransformAtLength_comap_consolidated462
    (fLast : t.obj t.length ⟶ s.obj s.length)
    (hfLast : fLast = strictPullbackMapAt_consolidated462 s t D t.length le_rfl
      ≫ eqToHom (congrArg s.obj (length_eq_of_strictPullbackBlowupSeq_consolidated462 s t D))) :
    MaxContactReduction.strictTransformAtLength t (H.comap g)
      = (MaxContactReduction.strictTransformAtLength s H).comap fLast := by
  have h1 := iteratedStrictTransform_comap_consolidated462 hflat s t D hNs hNt H t.length le_rfl
  rw [MaxContactReduction.strictTransformAtLength_eq, MaxContactReduction.strictTransformAtLength_eq, hfLast,
    Scheme.IdealSheafData.comap_comp,
    iteratedStrictTransform_comap_eqToHom_consolidated462 s H t.length s.length (length_eq_of_strictPullbackBlowupSeq_consolidated462 s t D)
      (congrArg s.obj (length_eq_of_strictPullbackBlowupSeq_consolidated462 s t D))]
  exact h1


end

section
variable (hderiv : DerivIdealSheafIterateCommBaseChange.{u}) (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B) (T T' : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc) (hPdimOther : P T'.krullDimSucc) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible) (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) (hdimS : S.krullDimSucc ≤ T.krullDimSucc) (L : Type u) [Field L] [CharZero L] (f : S.base →+* L) [Flat (pullback.fst S.structMap (specMapOfFieldHom S.base L f))] (hV' : (S.baseChange L f).IsAdmissible) (hO' : ∀ x : ↥(S.baseChange L f).scheme, orderAt (S.baseChange L f).ideal x ≤ ((S.baseChange L f).mult : ℕ∞))
include hderiv hstar hmono hspec hPdimT hPdimOther hV hO hdimS hV' hO'

private theorem nonempty_strictPullbackBlowupSeq_appendLowerDimReduction_consolidated462
    (hdimS' : (S.baseChange L f).krullDimSucc ≤ T'.krullDimSucc)
    (hbc : IsBaseChangeInherited.{u} P)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (t : MarkedBlowupSequenceData (S.baseChange L f).structMap (S.baseChange L f).ideal
      (S.baseChange L f).mult (S.baseChange L f).boundary)
    (hftS : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hftT : LocallyOfFiniteType
      (t.proj t.length ≫ (S.baseChange L f).structMap))
    (D : StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (extra : List (s.obj s.length).IdealSheafData)
    (extra' : List (t.obj t.length).IdealSheafData)
    (hextra' : extra' = extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap)
    (keep j : ℕ)
    (hVc : (MaxContactCoverData.derivedTriple S s hftS extra keep).IsAdmissible)
    (hVc' : (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
      (LowerDimReductionPullback.comapBoundaryBaseChange S L f s t D extra) keep).IsAdmissible)
    (hj : j < (extra ++ (s.boundary s.length).drop keep).length)
    (hj' : j < (@List.append (t.obj t.length).IdealSheafData (LowerDimReductionPullback.comapBoundaryBaseChange S L f s t D extra)
      ((t.boundary t.length).drop keep)).length)
    (hsep : ∀ Dv ∈ (s.boundary s.length).take keep,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (Dv.support : Set ↥(s.obj s.length)) = ∅)
    (hsep' : ∀ Dv ∈ (t.boundary t.length).take keep,
      orderAtLeastLocus (t.ideal t.length) (S.baseChange L f).mult ∩
        (Dv.support : Set ↥(t.obj t.length)) = ∅) :
    Nonempty (StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      (MaxContactReduction.appendLowerDimReduction hinv T' (fun S' _ i => A i S') (S.baseChange L f) t extra'
        keep j).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') S s extra keep
        j).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  subst hextra'
  have hm : 1 ≤ S.mult := hV.one_le_mult
  have hdim := hstar.derivedTriple_dim_le hV s hftS extra keep hdimS
  have hdim2 := hstar.derivedTriple_dim_le hV' t hftT (LowerDimReductionPullback.comapBoundaryBaseChange S L f s t D extra) keep hdimS'
  have hP := hmono _ _ hdim hPdimT
  have hP2 := hmono _ _ hdim2 hPdimOther
  have hOb0 : ∀ x : ↥(MaxContactCoverData.derivedTriple S s hftS extra keep).scheme,
      orderAt (MaxContactCoverData.derivedTriple S s hftS extra keep).ideal x
        ≤ ((MaxContactCoverData.derivedTriple S s hftS extra keep).mult : ℕ∞) :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff _).mp
      (LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hftS extra keep hVc)
  have hDb0 : ∀ hft : LocallyOfFiniteType
      (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap,
      (MaxContactCoverData.derivedTriple S s hftS extra keep).IsBalanced hft :=
    fun _ => LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hm hO s hftS extra keep hVc
  obtain ⟨hVb, hPb, hOb, hDb⟩ :=
    hbc (MaxContactCoverData.derivedTriple S s hftS extra keep) L f hVc hP hOb0 hDb0
  exact LowerDimReductionPullback.nonempty_strictPullbackSeq_appendLowerDimReduction_baseChange S L f s t D hderiv hstar hinv P A B j
    (hspec j) T T' extra keep hftS hftT hV hm hO
    (BoundarySeparationBaseChange.isLocallyNoetherian_schemeAt hstar S hV s) hV' hO'
    (BoundarySeparationBaseChange.isLocallyNoetherian_schemeAt hstar (S.baseChange L f) hV' t) hdim hP hVc hj hsep
    hdim2 hP2 hVc' hj' hsep' hVb hPb hOb hDb

private theorem nonempty_strictPullbackBlowupSeq_separateBoundary_consolidated462
    (hdimS' : (S.baseChange L f).krullDimSucc ≤ T'.krullDimSucc)
    (hbc : IsBaseChangeInherited.{u} P) :
    ∀ j : ℕ, j ≤ S.boundary.length →
      Nonempty (StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
        (MaxContactReduction.separateBoundary hinv T' (fun S' _ i => A i S')
          (S.baseChange L f) j).toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (MaxContactReduction.separateBoundary hinv T (fun S' _ i => A i S') S
          j).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MaxContactCoverData.separateBoundary_zero, MaxContactCoverData.separateBoundary_zero]
    exact nonempty_strictPullback_of_length_eq_zero_consolidated462 _ _ _
      (emptyMarkedBlowupSequenceData_toMarkedSequence_length _ _ _ _) (emptyMarkedBlowupSequenceData_toMarkedSequence_length _ _ _ _)
  | succ j ih =>
    intro hj
    obtain ⟨D⟩ := ih (by omega)
    rw [MaxContactCoverData.separateBoundary_succ, MaxContactCoverData.separateBoundary_succ]
    have hftS := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV
      (MaxContactReduction.separateBoundary hinv T (fun S' _ i => A i S') S j) _ le_rfl
    have hftT := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar (S.baseChange L f) hV'
      (MaxContactReduction.separateBoundary hinv T' (fun S' _ i => A i S') (S.baseChange L f) j) _ le_rfl
    exact nonempty_strictPullbackBlowupSeq_appendLowerDimReduction_consolidated462 hderiv hstar hinv P hmono A B hspec T T' hPdimT hPdimOther S
      hV hO hdimS L f hV' hO' hdimS' hbc _ _ hftS hftT D [] [] rfl 0 j
      (BoundarySeparationBaseChange.isAdmissible_derivedTriple_nil hstar S hV _ hftS)
      (BoundarySeparationBaseChange.isAdmissible_derivedTriple_nil hstar (S.baseChange L f) hV' _ hftT)
      (lt_length_nil_append_boundary_consolidated462 S _ j (by omega))
      (lt_length_nil_append_boundary_consolidated462 (S.baseChange L f) _ j
        (by rw [MarkedIdealWithBoundary.length_boundary_baseChange]; omega))
      (BoundarySeparationBaseChange.orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero S _) (BoundarySeparationBaseChange.orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero (S.baseChange L f) _)

private theorem isStrictPullbackBlowupSeq_appendLowerDimReduction_baseChange_consolidated462
    (hdimS' : (S.baseChange L f).krullDimSucc ≤ T'.krullDimSucc)
    (hbc : IsBaseChangeInherited.{u} P)
    (H : S.scheme.IdealSheafData)
    (hH : ∀ [LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    (hH' : ∀ [LocallyOfFiniteType (S.baseChange L f).structMap],
      IsMaxContactHypersurface (S.baseChange L f).base (S.baseChange L f).structMap
        (S.baseChange L f).ideal (S.baseChange L f).mult
        (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))))
    (hH'snc : InStrictNormalCrossingPosition (S.baseChange L f).structMap
      [H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))])
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (t : MarkedBlowupSequenceData (S.baseChange L f).structMap (S.baseChange L f).ideal
      (S.baseChange L f).mult (S.baseChange L f).boundary)
    (D : StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hsep : ∀ Dv ∈ (s.boundary s.length).take S.boundary.length,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (Dv.support : Set ↥(s.obj s.length)) = ∅)
    (hsep' : ∀ Dv ∈ (t.boundary t.length).take S.boundary.length,
      orderAtLeastLocus (t.ideal t.length) (S.baseChange L f).mult ∩
        (Dv.support : Set ↥(t.obj t.length)) = ∅) :
    IsStrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      (MaxContactReduction.appendLowerDimReduction hinv T' (fun S' _ i => A i S') (S.baseChange L f) t
        [MaxContactReduction.strictTransformAtLength t
          (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f)))]
        S.boundary.length 0).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') S s
        [MaxContactReduction.strictTransformAtLength s H] S.boundary.length 0).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have := hV.locallyOfFiniteType
  have := hV'.locallyOfFiniteType
  have hlen : (S.baseChange L f).boundary.length = S.boundary.length :=
    MarkedIdealWithBoundary.length_boundary_baseChange S L f
  have hftS := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV s _ le_rfl
  have hftT := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar (S.baseChange L f) hV' t _
    le_rfl
  have hNs := BoundarySeparationBaseChange.isLocallyNoetherian_schemeAt hstar S hV s
  have hNt := BoundarySeparationBaseChange.isLocallyNoetherian_schemeAt hstar (S.baseChange L f) hV' t
  have hfLast : LowerDimReductionPullback.baseChangeMapAtLength S L f s t D
      = strictPullbackMapAt_consolidated462 s t D t.length le_rfl
        ≫ eqToHom (congrArg s.obj (length_eq_of_strictPullbackBlowupSeq_consolidated462 s t D)) :=
    D.lastMap_eq
  have hE : (MaxContactReduction.strictTransformAtLength s H).comap (LowerDimReductionPullback.baseChangeMapAtLength S L f s t D)
      = MaxContactReduction.strictTransformAtLength t
        (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))) :=
    (strictTransformAtLength_comap_consolidated462
      ‹Flat (pullback.fst S.structMap (_root_.FunctorialResolution.EmbeddedResolution.specMapOfFieldHom S.base L f))›
      s t D hNs hNt H (LowerDimReductionPullback.baseChangeMapAtLength S L f s t D) hfLast).symm
  have hbcx : LowerDimReductionPullback.comapBoundaryBaseChange S L f s t D [MaxContactReduction.strictTransformAtLength s H]
      = [MaxContactReduction.strictTransformAtLength t
          (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f)))] := by
    show [(MaxContactReduction.strictTransformAtLength s H).comap (LowerDimReductionPullback.baseChangeMapAtLength S L f s t D)] = _
    rw [hE]
  have hsncS : InStrictNormalCrossingPosition (s.proj s.length ≫ S.structMap)
      ([MaxContactReduction.strictTransformAtLength s H] ++ (s.boundary s.length).drop S.boundary.length) := by
    rw [MaxContactReduction.strictTransformAtLength_eq]
    exact inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar S hV hO H hH s
      (BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_iteratedStrictTransform_zero S s H hHsnc) s.length le_rfl
  have hsncT : InStrictNormalCrossingPosition (t.proj t.length ≫ (S.baseChange L f).structMap)
      (LowerDimReductionPullback.comapBoundaryBaseChange S L f s t D [MaxContactReduction.strictTransformAtLength s H] ++
        (t.boundary t.length).drop S.boundary.length) := by
    rw [hbcx, MaxContactReduction.strictTransformAtLength_eq, ← hlen]
    exact inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar (S.baseChange L f) hV' hO'
      (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))) hH' t
      (BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_iteratedStrictTransform_zero (S.baseChange L f) t
        (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))) hH'snc) t.length le_rfl
  have hVcS := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar S hV s hftS
    [MaxContactReduction.strictTransformAtLength s H] S.boundary.length hsncS
  have hVcT := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar (S.baseChange L f) hV' t hftT
    (LowerDimReductionPullback.comapBoundaryBaseChange S L f s t D [MaxContactReduction.strictTransformAtLength s H]) S.boundary.length hsncT
  obtain ⟨D2⟩ := nonempty_strictPullbackBlowupSeq_appendLowerDimReduction_consolidated462 hderiv hstar hinv P hmono A B hspec T T' hPdimT
    hPdimOther S hV hO hdimS L f hV' hO' hdimS' hbc s t hftS hftT D [MaxContactReduction.strictTransformAtLength s H]
    [MaxContactReduction.strictTransformAtLength t
      (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f)))]
    hbcx.symm S.boundary.length 0 hVcS hVcT (by simp) (by simp [LowerDimReductionPullback.comapBoundaryBaseChange]) hsep hsep'
  exact D2.isStrictPullback

theorem isStrictPullbackBlowupSeq_reduceAlongHypersurface_baseChange
    (hdim' : (S.baseChange L f).krullDimSucc ≤ T'.krullDimSucc)
    (H : S.scheme.IdealSheafData)
    (hH : ∀ [LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    (hH' : ∀ [LocallyOfFiniteType (S.baseChange L f).structMap],
      IsMaxContactHypersurface (S.baseChange L f).base (S.baseChange L f).structMap
        (S.baseChange L f).ideal (S.baseChange L f).mult
        (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))))
    (hH'snc : InStrictNormalCrossingPosition (S.baseChange L f).structMap
      [H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))])
    (hbc : IsBaseChangeInherited.{u} P) :
    IsStrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      (MaxContactReduction.reduceAlongHypersurface hinv T' (fun S' _ i => A i S') (S.baseChange L f)
        (H.comap (pullback.fst S.structMap
          (specMapOfFieldHom S.base L f)))).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have hlen : (S.baseChange L f).boundary.length = S.boundary.length :=
    MarkedIdealWithBoundary.length_boundary_baseChange S L f
  obtain ⟨D⟩ := nonempty_strictPullbackBlowupSeq_separateBoundary_consolidated462 hderiv hstar hinv P hmono A B hspec T T'
    hPdimT hPdimOther S hV hO hdimS L f hV' hO' hdim' hbc S.boundary.length le_rfl
  have hSeparated := BoundarySeparationBaseChange.separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A B hspec T hPdimT
    S hV hO hdimS H hHsnc S.boundary.length le_rfl
  have hSeparatedSeq := BoundarySeparationBaseChange.separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A B hspec T'
    hPdimOther (S.baseChange L f) hV' hO' hdim'
    (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))) hH'snc
    (S.baseChange L f).boundary.length le_rfl
  rw [hlen] at hSeparatedSeq
  rw [MaxContactCoverData.reduceAlongHypersurface_eq_appendLowerDimReduction, MaxContactCoverData.reduceAlongHypersurface_eq_appendLowerDimReduction, hlen]
  exact isStrictPullbackBlowupSeq_appendLowerDimReduction_baseChange_consolidated462 hderiv hstar hinv P hmono A B hspec T T' hPdimT hPdimOther S hV
    hO hdimS L f hV' hO' hdim' hbc H hH hHsnc hH' hH'snc
    (MaxContactReduction.separateBoundary hinv T (fun S' _ i => A i S') S S.boundary.length)
    (MaxContactReduction.separateBoundary hinv T' (fun S' _ i => A i S') (S.baseChange L f)
      S.boundary.length)
    D (BoundarySeparationBaseChange.orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated S _ S.boundary.length hSeparated.1)
    (BoundarySeparationBaseChange.orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated (S.baseChange L f) _ S.boundary.length hSeparatedSeq.1)


end

end BoundaryLoopFieldBaseChange


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.BlowupDataOfSequence
section

open CategoryTheory.Limits

section

theorem toMarkedSequence_projectionToBase {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase i = s.proj i :=
  (s.projectionToBase_eq_toSequenceOfBlowups i).symm

theorem isPullbackBlowupSequence_congr (F : PrincipalizationAssignment.{u})
    {k₁ k₂ : Type u} [Field k₁] [Field k₂] {B Q : Scheme.{u}}
    (pB : B ⟶ Spec (CommRingCat.of k₁)) (IB : B.IdealSheafData) (mB : ℕ)
    (EB : List B.IdealSheafData) (q : Q ⟶ B)
    (pQ₁ pQ₂ : Q ⟶ Spec (CommRingCat.of k₂)) (IQ₁ IQ₂ : Q.IdealSheafData) (mQ₁ mQ₂ : ℕ)
    (EQ₁ EQ₂ : List Q.IdealSheafData)
    (hp : pQ₁ = pQ₂) (hI : IQ₁ = IQ₂) (hm : mQ₁ = mQ₂) (hE : EQ₁ = EQ₂)
    (h : IsPullbackBlowupSequence q (F (MarkedIdealWithBoundary.mk k₂ Q pQ₁ IQ₁ mQ₁ EQ₁)).toSequenceOfBlowups
        (F (MarkedIdealWithBoundary.mk k₁ B pB IB mB EB)).toSequenceOfBlowups) :
    IsPullbackBlowupSequence q (F (MarkedIdealWithBoundary.mk k₂ Q pQ₂ IQ₂ mQ₂ EQ₂)).toSequenceOfBlowups
      (F (MarkedIdealWithBoundary.mk k₁ B pB IB mB EB)).toSequenceOfBlowups := by
  subst hp
  subst hI
  subst hm
  subst hE
  exact h

section
variable {X : Scheme.{u}} (s : SequenceOfBlowups X)

theorem BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length :
    (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length = s.length := by
  rw [BlowupSequenceData.toSequenceOfBlowups_length]
  rfl

private theorem ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt_consolidated438 (j : ℕ) :
    (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.schemeAt j = s.schemeAt j :=
  (BlowupSequenceData.toSequenceOfBlowups_schemeAt _ j).trans (BlowupSequenceData.ofSequenceOfBlowups_schemeAt s j)

private theorem le_length_of_le_ofSequenceOfBlowups_length_consolidated438 {j : ℕ}
    (hj : j ≤ (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length) : j ≤ s.length := by
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj
  exact hj

private theorem le_ofSequenceOfBlowups_length_of_le_length_consolidated438 {j : ℕ}
    (hj : j ≤ s.length) : j ≤ (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length := by
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
  exact hj


end

theorem BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups {X : Scheme.{u}} (t : SequenceOfBlowups X) (j : ℕ) :
    (BlowupSequenceData.ofSequenceOfBlowups t).toSequenceOfBlowups.projectionToBase j = t.projectionToBase j :=
  (BlowupSequenceData.toSequenceOfBlowups_projectionToBase (BlowupSequenceData.ofSequenceOfBlowups t) j).trans (BlowupSequenceData.ofSequenceOfBlowups_projectionToBase t j)

namespace SequenceOfBlowupsPullback

variable {X X' : Scheme.{u}} {φ : X' ⟶ X} {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}

private def ofSequenceOfBlowupsMap_consolidated438 (c : SequenceOfBlowupsPullback φ s' s) (j : ℕ)
    (hj : j ≤ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length) :
    (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.schemeAt j ⟶ (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.schemeAt (c.idx j) :=
  eqToHom (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt_consolidated438 s' j) ≫ c.map j (le_length_of_le_ofSequenceOfBlowups_length_consolidated438 s' hj) ≫
    eqToHom (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt_consolidated438 s (c.idx j)).symm

section
variable (c : SequenceOfBlowupsPullback φ s' s)

private theorem index_ofSequenceOfBlowups_length_consolidated438 :
    c.idx (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length = (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length := by
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s', BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s]
  exact c.idx_length

private theorem index_lt_ofSequenceOfBlowups_length_consolidated438 :
    ∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length →
      c.idx j < (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length := by
  intro j hj
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
  exact c.idx_lt j hj

private theorem index_lt_index_succ_of_lt_length_ofSequenceOfBlowups_consolidated438 :
    ∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length → c.idx j < c.idx (j + 1) := by
  intro j hj
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj
  exact c.idx_strictMono j hj

private theorem ofSequenceOfBlowups_map_eq_consolidated438 (j : ℕ)
    (hj : j ≤ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length) :
    ofSequenceOfBlowupsMap_consolidated438 c j hj = c.map j (le_length_of_le_ofSequenceOfBlowups_length_consolidated438 s' hj) := by
  show 𝟙 (s'.schemeAt j) ≫ c.map j (le_length_of_le_ofSequenceOfBlowups_length_consolidated438 s' hj) ≫ 𝟙 (s.schemeAt (c.idx j))
      = c.map j (le_length_of_le_ofSequenceOfBlowups_length_consolidated438 s' hj)
  exact (Category.id_comp _).trans (Category.comp_id _)


end

private theorem isPullback_congr_consolidated438 {A B C D : Scheme.{u}} {f f' : A ⟶ B} {g g' : A ⟶ C}
    {h h' : B ⟶ D} {k k' : C ⟶ D} (hf : f = f') (hg : g = g') (hh : h = h') (hk : k = k')
    (H : IsPullback f g h k) : IsPullback f' g' h' k' := by
  subst hf
  subst hg
  subst hh
  subst hk
  exact H

private theorem isPullback_projectionToBase_ofSequenceOfBlowups_consolidated438 (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ (j : ℕ) (hj : j ≤ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length),
      IsPullback (ofSequenceOfBlowupsMap_consolidated438 c j hj) ((BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.projectionToBase j)
        ((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.projectionToBase (c.idx j)) φ := by
  intro j hj
  exact isPullback_congr_consolidated438 (ofSequenceOfBlowups_map_eq_consolidated438 c j hj).symm
    (BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s' j).symm
    (BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s (c.idx j)).symm rfl
    (c.isPullback j (le_length_of_le_ofSequenceOfBlowups_length_consolidated438 s' hj))

section
variable {W : Scheme.{u}} (t : SequenceOfBlowups W)

private theorem ofSequenceOfBlowups_transitionMap_consolidated438 {i i' : ℕ}
    (h : i ≤ i') : (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap h = t.transitionMap h := by
  induction h with
  | refl =>
      have e1 : (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap (le_refl i) = 𝟙 ((BlowupSequenceData.ofSequenceOfBlowups t).obj i) := by
        rw [BlowupSequenceData.transitionMap_refl]
      have e2 : t.transitionMap (le_refl i) = 𝟙 (t.schemeAt i) := by
        rw [SequenceOfBlowups.transitionMap_self_eq_id]
      exact e1.trans e2.symm
  | @step m hm ih =>
      have hmap : (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap (Nat.le_succ m) = t.transitionMapSucc m :=
        (BlowupSequenceData.transitionMap_succ (BlowupSequenceData.ofSequenceOfBlowups t) m).trans (BlowupSequenceData.ofSequenceOfBlowups_blowupMorphism t m)
      have h1 : (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap (Nat.le_trans hm (Nat.le_succ m))
          = (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap (Nat.le_succ m) ≫ (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap hm :=
        (BlowupSequenceData.transitionMap_comp_transitionMap (BlowupSequenceData.ofSequenceOfBlowups t) hm (Nat.le_succ m)).symm
      have h2a : (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap (Nat.le_succ m) ≫ (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap hm
          = t.transitionMapSucc m ≫ (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap hm :=
        congrArg (fun f : t.schemeAt (m + 1) ⟶ t.schemeAt m => f ≫ (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap hm) hmap
      have h2b : t.transitionMapSucc m ≫ (BlowupSequenceData.ofSequenceOfBlowups t).transitionMap hm
          = t.transitionMapSucc m ≫ t.transitionMap hm :=
        congrArg (fun g : t.schemeAt m ⟶ t.schemeAt i => t.transitionMapSucc m ≫ g) ih
      have h3 : t.transitionMapSucc m ≫ t.transitionMap hm = t.transitionMap (Nat.le_trans hm (Nat.le_succ m)) := by
        rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
        exact SequenceOfBlowups.transitionMap_trans t hm (Nat.le_succ m)
      exact h1.trans (h2a.trans (h2b.trans h3))

private theorem ofSequenceOfBlowups_toSequenceOfBlowups_transitionMap_consolidated438 {i i' : ℕ}
    (h : i ≤ i') : (BlowupSequenceData.ofSequenceOfBlowups t).toSequenceOfBlowups.transitionMap h = t.transitionMap h :=
  (BlowupSequenceData.toSequenceOfBlowups_transitionMap (BlowupSequenceData.ofSequenceOfBlowups t) h).trans (ofSequenceOfBlowups_transitionMap_consolidated438 t h)

private theorem ofSequenceOfBlowups_toSequenceOfBlowups_blowupMorphism_consolidated438 (i : ℕ) :
    (BlowupSequenceData.ofSequenceOfBlowups t).toSequenceOfBlowups.transitionMapSucc i = t.transitionMapSucc i :=
  (SequenceOfBlowups.blowupMorphism_eq_transitionMap ((BlowupSequenceData.ofSequenceOfBlowups t).toSequenceOfBlowups) i).trans
    ((ofSequenceOfBlowups_toSequenceOfBlowups_transitionMap_consolidated438 t (Nat.le_succ i)).trans
      (SequenceOfBlowups.blowupMorphism_eq_transitionMap t i).symm)


end

private theorem ofSequenceOfBlowups_blowupMorphism_comp_map_consolidated438 (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ (j : ℕ) (hj : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length),
      (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.transitionMapSucc j ≫ ofSequenceOfBlowupsMap_consolidated438 c j (le_of_lt hj) =
        ofSequenceOfBlowupsMap_consolidated438 c (j + 1) hj ≫
          (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap (le_of_lt (index_lt_index_succ_of_lt_length_ofSequenceOfBlowups_consolidated438 c j hj)) := by
  intro j hj
  have hlt : j < s'.length := by
    have h := hj
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at h
    exact h
  rw [ofSequenceOfBlowups_map_eq_consolidated438 c j (le_of_lt hj), ofSequenceOfBlowups_map_eq_consolidated438 c (j + 1) hj,
    ofSequenceOfBlowups_toSequenceOfBlowups_blowupMorphism_consolidated438, ofSequenceOfBlowups_toSequenceOfBlowups_transitionMap_consolidated438]
  exact c.step j hlt

private theorem eqToHom_refl_comp_comp_eqToHom_refl_consolidated438 {A B : Scheme.{u}} (hA : A = A) (hB : B = B)
    (f : A ⟶ B) : eqToHom hA ≫ f ≫ eqToHom hB = f := by
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

section
variable (c : SequenceOfBlowupsPullback φ s' s)
include c

private theorem center_ofSequenceOfBlowups_eq_comap_consolidated438 :
    ∀ (j : ℕ) (hj : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length),
      (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.center j =
        ((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.center (c.idx j)).comap (ofSequenceOfBlowupsMap_consolidated438 c j (le_of_lt hj)) := by
  intro j hj
  have hj' : j < s'.length := lt_of_lt_of_le hj (le_of_eq (BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s'))
  have hmap : ofSequenceOfBlowupsMap_consolidated438 c j (le_of_lt hj) = c.map j (le_of_lt hj') :=
    eqToHom_refl_comp_comp_eqToHom_refl_consolidated438 (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt_consolidated438 s' j) (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt_consolidated438 s (c.idx j)).symm
      (c.map j (le_length_of_le_ofSequenceOfBlowups_length_consolidated438 s' (le_of_lt hj)))
  rw [hmap]
  exact c.center_comap j hj'

private theorem center_ofSequenceOfBlowups_ne_top_consolidated438 :
    ∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length →
      (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.center j ≠ ⊤ := by
  intro j hj
  have hj' : j < s'.length := lt_of_lt_of_le hj (le_of_eq (BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s'))
  exact c.center_ne_top j hj'

private theorem ofSequenceOfBlowups_ne_of_mem_unmatched_center_consolidated438 :
    ∀ i : ℕ, i < (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length →
      (∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length → c.idx j ≠ i) →
      ∀ z : ↥((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.schemeAt i),
        z ∈ ((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.center i).support →
        ∀ x' : ↥X', φ.base x' ≠ ((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.projectionToBase i).base z := by
  intro i hi hmiss z hz x'
  have hi' : i < s.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hi
    exact hi
  have hmiss' : ∀ j : ℕ, j < s'.length → c.idx j ≠ i := by
    intro j hj
    refine hmiss j ?_
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  have h := c.omitted i hi' hmiss' z hz x'
  rw [BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s i]
  exact h


end

def toBlowupDataOfSeq (c : SequenceOfBlowupsPullback φ s' s) :
    SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups where
  idx := c.idx
  map := ofSequenceOfBlowupsMap_consolidated438 c
  idx_length := index_ofSequenceOfBlowups_length_consolidated438 c
  idx_lt := index_lt_ofSequenceOfBlowups_length_consolidated438 c
  idx_strictMono := index_lt_index_succ_of_lt_length_ofSequenceOfBlowups_consolidated438 c
  isPullback := isPullback_projectionToBase_ofSequenceOfBlowups_consolidated438 c
  step := ofSequenceOfBlowups_blowupMorphism_comp_map_consolidated438 c
  center_comap := center_ofSequenceOfBlowups_eq_comap_consolidated438 c
  center_ne_top := center_ofSequenceOfBlowups_ne_top_consolidated438 c
  omitted := ofSequenceOfBlowups_ne_of_mem_unmatched_center_consolidated438 c

private def transportedMap_consolidated438
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups)
    (j : ℕ) (hj : j ≤ s'.length) : s'.schemeAt j ⟶ s.schemeAt (c.idx j) :=
  eqToHom (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt_consolidated438 s' j).symm ≫ c.map j (le_ofSequenceOfBlowups_length_of_le_length_consolidated438 s' hj) ≫
    eqToHom (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt_consolidated438 s (c.idx j))

section
variable (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups)
include c

private theorem ofSequenceOfBlowups_index_length_consolidated438
    :
    c.idx s'.length = s.length := by
  have h := c.idx_length
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s', BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s] at h
  exact h

private theorem ofSequenceOfBlowups_index_lt_length_consolidated438
    :
    ∀ j : ℕ, j < s'.length → c.idx j < s.length := by
  intro j hj
  have hj' : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  have h := c.idx_lt j hj'
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at h
  exact h

private theorem index_lt_index_succ_of_lt_length_consolidated438
    :
    ∀ j : ℕ, j < s'.length → c.idx j < c.idx (j + 1) := by
  intro j hj
  refine c.idx_strictMono j ?_
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
  exact hj

private theorem transportedMap_eq_map_consolidated438
    (j : ℕ) (hj : j ≤ s'.length) :
    transportedMap_consolidated438 c j hj = c.map j (le_ofSequenceOfBlowups_length_of_le_length_consolidated438 s' hj) :=
  eqToHom_refl_comp_comp_eqToHom_refl_consolidated438 (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt_consolidated438 s' j).symm (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt_consolidated438 s (c.idx j))
    (c.map j (le_ofSequenceOfBlowups_length_of_le_length_consolidated438 s' hj))

private theorem isPullback_transportedMap_consolidated438
    :
    ∀ (j : ℕ) (hj : j ≤ s'.length),
      IsPullback (transportedMap_consolidated438 c j hj) (s'.projectionToBase j) (s.projectionToBase (c.idx j)) φ := by
  intro j hj
  exact isPullback_congr_consolidated438 (transportedMap_eq_map_consolidated438 c j hj).symm (BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s' j)
    (BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s (c.idx j)) rfl
    (c.isPullback j (le_ofSequenceOfBlowups_length_of_le_length_consolidated438 s' hj))

private theorem blowupMorphism_comp_map_of_ofSequenceOfBlowups_consolidated438
    :
    ∀ (j : ℕ) (hj : j < s'.length),
      s'.transitionMapSucc j ≫ transportedMap_consolidated438 c j (le_of_lt hj) =
        transportedMap_consolidated438 c (j + 1) hj ≫ s.transitionMap (le_of_lt (index_lt_index_succ_of_lt_length_consolidated438 c j hj)) := by
  intro j hj
  have hj' : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  have key := c.step j hj'
  rw [ofSequenceOfBlowups_toSequenceOfBlowups_blowupMorphism_consolidated438, ofSequenceOfBlowups_toSequenceOfBlowups_transitionMap_consolidated438] at key
  rw [transportedMap_eq_map_consolidated438 c j (le_of_lt hj), transportedMap_eq_map_consolidated438 c (j + 1) hj]
  exact key

private theorem center_eq_comap_transportedMap_consolidated438
    :
    ∀ (j : ℕ) (hj : j < s'.length),
      s'.center j = (s.center (c.idx j)).comap (transportedMap_consolidated438 c j (le_of_lt hj)) := by
  intro j hj
  have hj' : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  have hmap : transportedMap_consolidated438 c j (le_of_lt hj) = c.map j (le_of_lt hj') :=
    eqToHom_refl_comp_comp_eqToHom_refl_consolidated438 (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt_consolidated438 s' j).symm (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt_consolidated438 s (c.idx j))
      (c.map j (le_ofSequenceOfBlowups_length_of_le_length_consolidated438 s' (le_of_lt hj)))
  rw [hmap]
  exact c.center_comap j hj'

private theorem center_ne_top_of_pullback_ofSequenceOfBlowups_consolidated438
    :
    ∀ j : ℕ, j < s'.length → s'.center j ≠ ⊤ := by
  intro j hj
  have hj' : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  exact c.center_ne_top j hj'

private theorem ofSequenceOfBlowups_projectionToBase_ne_consolidated438
    :
    ∀ i : ℕ, i < s.length → (∀ j : ℕ, j < s'.length → c.idx j ≠ i) →
      ∀ z : ↥(s.schemeAt i), z ∈ (s.center i).support →
        ∀ x' : ↥X', φ.base x' ≠ (s.projectionToBase i).base z := by
  intro i hi hmiss z hz x'
  have hi' : i < (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hi
  have hmiss' : ∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length → c.idx j ≠ i := by
    intro j hj
    refine hmiss j ?_
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj
    exact hj
  have h := c.omitted i hi' hmiss' z hz x'
  rw [BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s i] at h
  exact h


end

def ofBlowupDataOfSeq (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    SequenceOfBlowupsPullback φ s' s where
  idx := c.idx
  map := transportedMap_consolidated438 c
  idx_length := ofSequenceOfBlowups_index_length_consolidated438 c
  idx_lt := ofSequenceOfBlowups_index_lt_length_consolidated438 c
  idx_strictMono := index_lt_index_succ_of_lt_length_consolidated438 c
  isPullback := isPullback_transportedMap_consolidated438 c
  step := blowupMorphism_comp_map_of_ofSequenceOfBlowups_consolidated438 c
  center_comap := center_eq_comap_transportedMap_consolidated438 c
  center_ne_top := center_ne_top_of_pullback_ofSequenceOfBlowups_consolidated438 c
  omitted := ofSequenceOfBlowups_projectionToBase_ne_consolidated438 c

end SequenceOfBlowupsPullback


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SameNontrivialBoundary
section


section

namespace NontrivialBoundary

section

variable {Y : Scheme.{u}}

theorem sameNontrivialBoundary_refl (L : List Y.IdealSheafData) : MarkedIdealWithBoundary.SameNontrivialBoundary L L :=
  MarkedIdealWithBoundary.SameNontrivialBoundary.refl L

theorem sameNontrivialBoundary_symm {L L' : List Y.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary L L') : MarkedIdealWithBoundary.SameNontrivialBoundary L' L :=
  h.symm

theorem sameNontrivialBoundary_nontrivialPart (L : List Y.IdealSheafData) :
    MarkedIdealWithBoundary.SameNontrivialBoundary (MarkedIdealWithBoundary.nontrivialPart L) L := by
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff]
  induction L with
  | nil => simp [MarkedIdealWithBoundary.nontrivialPart]
  | cons D L _ih =>
    by_cases h : D = ⊤
    · simp [MarkedIdealWithBoundary.nontrivialPart, h]
    · simp [MarkedIdealWithBoundary.nontrivialPart, h]

theorem sameNontrivialBoundary_append {L₁ L₂ L₁' L₂' : List Y.IdealSheafData}
    (h₁ : MarkedIdealWithBoundary.SameNontrivialBoundary L₁ L₁')
    (h₂ : MarkedIdealWithBoundary.SameNontrivialBoundary L₂ L₂') :
    MarkedIdealWithBoundary.SameNontrivialBoundary (L₁ ++ L₂) (L₁' ++ L₂') :=
  h₁.append h₂

theorem sameNontrivialBoundary_cons {D : Y.IdealSheafData} {L L' : List Y.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary L L') :
    MarkedIdealWithBoundary.SameNontrivialBoundary (D :: L) (D :: L') :=
  sameNontrivialBoundary_append (sameNontrivialBoundary_refl [D]) h

theorem sameNontrivialBoundary_cancel_left {L₁ L₂ L₁' L₂' : List Y.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary (L₁ ++ L₂) (L₁' ++ L₂'))
    (h₁ : MarkedIdealWithBoundary.SameNontrivialBoundary L₁ L₁') :
    MarkedIdealWithBoundary.SameNontrivialBoundary L₂ L₂' := by
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff] at h h₁ ⊢
  rw [MarkedIdealWithBoundary.nontrivialPart_append, MarkedIdealWithBoundary.nontrivialPart_append, h₁] at h
  exact List.append_cancel_left h

private theorem nontrivialPart_top_singleton_consolidated457 {Z : Scheme.{u}} :
    MarkedIdealWithBoundary.nontrivialPart [(⊤ : Z.IdealSheafData)] = [] := by
  simp [MarkedIdealWithBoundary.nontrivialPart]

theorem sameNontrivialBoundary_append_top {L L' : List Y.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary L L') :
    MarkedIdealWithBoundary.SameNontrivialBoundary (L ++ [(⊤ : Y.IdealSheafData)]) L' := by
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff] at h ⊢
  rw [MarkedIdealWithBoundary.nontrivialPart_append, h, nontrivialPart_top_singleton_consolidated457, List.append_nil]

end

@[reducible] noncomputable def pullbackWithNontrivialBoundary (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}}
    (q : X' ⟶ S.scheme) : MarkedIdealWithBoundary.{u} :=
  @MarkedIdealWithBoundary.mk S.base S.instField X' (q ≫ S.structMap) (S.ideal.comap q) S.mult
    (MarkedIdealWithBoundary.nontrivialPart (S.boundary.map fun D => D.comap q))

section

section
variable (R : MarkedIdealWithBoundary.{u}) (t : MarkedBlowupSequenceData R.structMap R.ideal R.mult R.boundary)

theorem lastBoundary_eq_append :
    t.boundary t.length =
      R.boundary.map (t.iteratedStrictTransform t.length) ++
        t.boundaryFrom ([] : List R.scheme.IdealSheafData) t.length := by
  rw [← MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq t t.length le_rfl, ← BlowupSequenceData.boundary_append,
    List.append_nil]

theorem length_boundary_le_length_lastBoundary :
    R.boundary.length ≤ (t.boundary t.length).length := by
  have h : t.boundaryFrom R.boundary t.length = t.boundary t.length :=
    MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq t t.length le_rfl
  have h3 : (t.boundary t.length).length = R.boundary.length + t.length := by
    rw [← h]
    exact BlowupSequenceData.boundary_length _ _ _
  omega

theorem getElem_lastBoundary_eq_iteratedStrictTransform (i : ℕ) (hi : i < R.boundary.length) :
    (t.boundary t.length)[i]'(lt_of_lt_of_le hi (length_boundary_le_length_lastBoundary R t)) =
      t.iteratedStrictTransform t.length (R.boundary[i]'hi) := by
  have hmap : i < (R.boundary.map (t.iteratedStrictTransform t.length)).length := by
    simpa using hi
  have h := lastBoundary_eq_append R t
  rw [List.getElem_of_eq h, List.getElem_append_left hmap, List.getElem_map]


end

end

section

noncomputable def survivingBoundaryCount (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme)
    (n : ℕ) : ℕ :=
  (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take n).map fun D => D.comap q)).length

section
variable (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme)

@[simp] theorem survivingBoundaryCount_zero :
    survivingBoundaryCount S q 0 = 0 := by
  simp [survivingBoundaryCount, MarkedIdealWithBoundary.nontrivialPart]

theorem survivingBoundaryCount_succ_of_eq_top (i : ℕ) (hi : i < S.boundary.length) (hdead : (S.boundary[i]'hi).comap q = ⊤) :
    survivingBoundaryCount S q (i + 1) = survivingBoundaryCount S q i := by
  have h : S.boundary.take (i + 1) = S.boundary.take i ++ S.boundary[i]?.toList :=
    List.take_add_one
  rw [List.getElem?_eq_getElem hi] at h
  have htake : S.boundary.take (i + 1) = S.boundary.take i ++ [S.boundary[i]'hi] := h
  unfold survivingBoundaryCount
  rw [htake]
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [MarkedIdealWithBoundary.nontrivialPart_append, hdead, nontrivialPart_top_singleton_consolidated457, List.append_nil]


end

private theorem nontrivialPart_singleton_of_ne_top_consolidated457 {Z : Scheme.{u}} (D : Z.IdealSheafData)
    (h : D ≠ ⊤) : MarkedIdealWithBoundary.nontrivialPart [D] = [D] := by
  simp [MarkedIdealWithBoundary.nontrivialPart, h]

section
variable (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme)

theorem survivingBoundaryCount_succ_of_ne_top (i : ℕ) (hi : i < S.boundary.length) (hlive : (S.boundary[i]'hi).comap q ≠ ⊤) :
    survivingBoundaryCount S q (i + 1) = survivingBoundaryCount S q i + 1 := by
  have h : S.boundary.take (i + 1) = S.boundary.take i ++ S.boundary[i]?.toList :=
    List.take_add_one
  rw [List.getElem?_eq_getElem hi] at h
  have htake : S.boundary.take (i + 1) = S.boundary.take i ++ [S.boundary[i]'hi] := h
  unfold survivingBoundaryCount
  rw [htake]
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [MarkedIdealWithBoundary.nontrivialPart_append, nontrivialPart_singleton_of_ne_top_consolidated457 _ hlive,
    List.length_append]
  simp

theorem survivingBoundaryCount_length_eq :
    survivingBoundaryCount S q S.boundary.length = (pullbackWithNontrivialBoundary S q).boundary.length := by
  have h : S.boundary.take S.boundary.length = S.boundary := by simp
  show (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take S.boundary.length).map
      fun D => D.comap q)).length = (pullbackWithNontrivialBoundary S q).boundary.length
  rw [h]

theorem survivingBoundaryCount_lt_length (i : ℕ) (hi : i < S.boundary.length) (hlive : (S.boundary[i]'hi).comap q ≠ ⊤) :
    survivingBoundaryCount S q i < (pullbackWithNontrivialBoundary S q).boundary.length := by
  have hsucc := survivingBoundaryCount_succ_of_ne_top S q i hi hlive
  have hmap : (S.boundary.map fun D => D.comap q) =
      ((S.boundary.take (i + 1)).map fun D => D.comap q) ++
        ((S.boundary.drop (i + 1)).map fun D => D.comap q) := by
    rw [← List.map_append, List.take_append_drop]
  have hlen : (pullbackWithNontrivialBoundary S q).boundary.length =
      (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take (i + 1)).map fun D => D.comap q)).length +
        (MarkedIdealWithBoundary.nontrivialPart
          ((S.boundary.drop (i + 1)).map fun D => D.comap q)).length := by
    show (MarkedIdealWithBoundary.nontrivialPart (S.boundary.map fun D => D.comap q)).length = _
    rw [hmap, MarkedIdealWithBoundary.nontrivialPart_append, List.length_append]
  have hdef : survivingBoundaryCount S q (i + 1) =
      (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take (i + 1)).map fun D => D.comap q)).length := rfl
  omega


end

private theorem getElem_eq_getElem_of_eq_consolidated457.{v} {α : Type v} (l l' : List α) (n n' : ℕ)
    (hl : l = l') (hn : n = n') (h : n < l.length) (h' : n' < l'.length) :
    l[n]'h = l'[n']'h' := by
  subst hl
  subst hn
  rfl

private theorem getElem_append_cons_length_consolidated457.{v} {α : Type v} :
    ∀ (A : List α) (x : α) (B : List α) (h : A.length < (A ++ x :: B).length),
      (A ++ x :: B)[A.length]'h = x := by
  intro A
  induction A with
  | nil => intro x B h; rfl
  | cons a t ih =>
      intro x B h
      have hb : t.length < (t ++ x :: B).length := by
        rw [List.length_append, List.length_cons]
        omega
      exact ih x B hb

private theorem nontrivialPart_cons_of_ne_top_consolidated457 {Z : Scheme.{u}} (D : Z.IdealSheafData) (hD : D ≠ ⊤)
    (L : List Z.IdealSheafData) :
    MarkedIdealWithBoundary.nontrivialPart (D :: L) = D :: MarkedIdealWithBoundary.nontrivialPart L := by
  have h : MarkedIdealWithBoundary.nontrivialPart ([D] ++ L)
      = MarkedIdealWithBoundary.nontrivialPart [D] ++ MarkedIdealWithBoundary.nontrivialPart L := by
    rw [MarkedIdealWithBoundary.nontrivialPart_append]
  rw [nontrivialPart_singleton_of_ne_top_consolidated457 D hD] at h
  simpa using h

theorem pullbackWithNontrivialBoundary_boundary_getElem (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme)
    (i : ℕ) (hi : i < S.boundary.length) (hlive : (S.boundary[i]'hi).comap q ≠ ⊤) :
    (pullbackWithNontrivialBoundary S q).boundary[survivingBoundaryCount S q i]'(survivingBoundaryCount_lt_length S q i hi hlive) =
      (S.boundary[i]'hi).comap q := by
  have hdrop : S.boundary.drop i = (S.boundary[i]'hi) :: S.boundary.drop (i + 1) :=
    List.drop_eq_getElem_cons hi
  have hsplit : S.boundary
      = S.boundary.take i ++ ((S.boundary[i]'hi) :: S.boundary.drop (i + 1)) := by
    rw [← hdrop, List.take_append_drop]
  have hmapeq : S.boundary.map (fun D => D.comap q)
      = (S.boundary.take i).map (fun D => D.comap q)
        ++ ((S.boundary[i]'hi).comap q :: (S.boundary.drop (i + 1)).map (fun D => D.comap q)) := by
    conv_lhs => rw [hsplit]
    simp only [List.map_append, List.map_cons]
  have hntp : MarkedIdealWithBoundary.nontrivialPart (S.boundary.map (fun D => D.comap q))
      = MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take i).map (fun D => D.comap q))
        ++ ((S.boundary[i]'hi).comap q ::
            MarkedIdealWithBoundary.nontrivialPart ((S.boundary.drop (i + 1)).map (fun D => D.comap q))) := by
    rw [hmapeq, MarkedIdealWithBoundary.nontrivialPart_append, nontrivialPart_cons_of_ne_top_consolidated457 _ hlive]
  have hlt : (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take i).map (fun D => D.comap q))).length
      < (MarkedIdealWithBoundary.nontrivialPart (S.boundary.map (fun D => D.comap q))).length := by
    rw [hntp, List.length_append, List.length_cons]
    omega
  have hbound :
      (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take i).map (fun D => D.comap q))).length
      < (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take i).map (fun D => D.comap q))
          ++ ((S.boundary[i]'hi).comap q ::
            MarkedIdealWithBoundary.nontrivialPart
              ((S.boundary.drop (i + 1)).map (fun D => D.comap q)))).length := by
    rw [List.length_append, List.length_cons]
    omega
  have htb : (pullbackWithNontrivialBoundary S q).boundary
      = MarkedIdealWithBoundary.nontrivialPart (S.boundary.map (fun D => D.comap q)) := rfl
  have hsc : survivingBoundaryCount S q i
      = (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take i).map (fun D => D.comap q))).length := rfl
  have main :
      (MarkedIdealWithBoundary.nontrivialPart (S.boundary.map (fun D => D.comap q)))[
        (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take i).map (fun D => D.comap q))).length]'hlt
        = (S.boundary[i]'hi).comap q :=
    (getElem_eq_getElem_of_eq_consolidated457 _ _ _ _ hntp rfl hlt hbound).trans
      (getElem_append_cons_length_consolidated457 _ _ _ hbound)
  exact (getElem_eq_getElem_of_eq_consolidated457 _ _ _ _ htb hsc (survivingBoundaryCount_lt_length S q i hi hlive) hlt).trans main

end

section

variable (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme)
  (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
  (s' : MarkedBlowupSequenceData (pullbackWithNontrivialBoundary S q).structMap (pullbackWithNontrivialBoundary S q).ideal
      (pullbackWithNontrivialBoundary S q).mult (pullbackWithNontrivialBoundary S q).boundary)
  (D : SequenceOfBlowupsPullback q s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)

theorem lastMap_comp_projectionToBase :
    D.lastMap ≫ s.proj s.length = s'.proj s'.length ≫ q := by
  have h := D.isPullback_lastMap.w
  have e1 : s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length
      = s.proj s.length := toMarkedSequence_projectionToBase s _
  have e2 : s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length
      = s'.proj s'.length := toMarkedSequence_projectionToBase s' _
  rw [e1, e2] at h
  exact h

theorem lastMap_comp_structureMorphism :
    D.lastMap ≫ (s.proj s.length ≫ S.structMap) =
      s'.proj s'.length ≫ (q ≫ S.structMap) := by
  have h := lastMap_comp_projectionToBase S q s s' D
  have h2 : (D.lastMap ≫ s.proj s.length) ≫ S.structMap
      = (s'.proj s'.length ≫ q) ≫ S.structMap :=
    congrArg (fun f => CategoryStruct.comp f S.structMap) h
  exact (Category.assoc D.lastMap (s.proj s.length) S.structMap).symm.trans
    (h2.trans (Category.assoc (s'.proj s'.length) q S.structMap))

theorem ideal_and_boundary_comap_lastMap [Smooth q] (_hMaxContact : MaxContactCoverProperties.{u})
    (hV : S.IsAdmissible) (hV' : (pullbackWithNontrivialBoundary S q).IsAdmissible) :
    s'.ideal s'.length = (s.ideal s.length).comap D.lastMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
        ((s.boundary s.length).map fun A => A.comap D.lastMap) := by
  have hflatq : Flat q := inferInstance
  have hN : ∀ i : ℕ, i ≤ s.length → IsNoetherian (s.obj i) := by
    intro i hi
    exact MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s.toMarkedSequenceOfBlowups i hi
  have hN' : ∀ j : ℕ, j ≤ s'.length → IsNoetherian (s'.obj j) := by
    intro j hj
    exact MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV' s'.toMarkedSequenceOfBlowups j hj
  exact SequenceOfBlowupsPullback.ideal_boundary_last_eq_comap_lastMap s s' D rfl
    (sameNontrivialBoundary_nontrivialPart (S.boundary.map fun A => A.comap q)) hN hN'

private theorem comap_eq_comap_comap_of_comp_eq_consolidated457 {A B C : Scheme.{u}} (e : A ⟶ B) (f : A ⟶ C)
    (g : B ⟶ C) (h : e ≫ g = f) (M : C.IdealSheafData) :
    M.comap f = (M.comap g).comap e := by
  subst h
  simp [Scheme.IdealSheafData.comap_comp]

theorem iteratedStrictTransform_comap_lastMap [Flat q] (_hMaxContact : MaxContactCoverProperties.{u})
    (hV : S.IsAdmissible) (hV' : (pullbackWithNontrivialBoundary S q).IsAdmissible) (M : S.scheme.IdealSheafData) :
    (s.iteratedStrictTransform s.length M).comap D.lastMap = s'.iteratedStrictTransform s'.length (M.comap q) := by
  have hz0s : s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase 0 = s.isoZero.hom := by
    rw [toMarkedSequence_projectionToBase s 0, MarkedBlowupSequenceData.projectionToBase_eq_toBlowupSequenceData_projectionToBase,
      BlowupSequenceData.projectionToBase_zero]
  have hz0s' : s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase 0 = s'.isoZero.hom := by
    rw [toMarkedSequence_projectionToBase s' 0, MarkedBlowupSequenceData.projectionToBase_eq_toBlowupSequenceData_projectionToBase,
      BlowupSequenceData.projectionToBase_zero]
  have hsq := SequenceOfBlowupsPullback.mapToEarlierScheme_comp_projectionToBase D 0 (Nat.zero_le _) 0 (Nat.zero_le _)
  rw [hz0s, hz0s'] at hsq
  have hs : s.iteratedStrictTransform 0 M = M.comap s.isoZero.hom := BlowupSequenceData.iteratedStrictTransform_zero _ M
  have hs' : s'.iteratedStrictTransform 0 (M.comap q) = (M.comap q).comap s'.isoZero.hom :=
    BlowupSequenceData.iteratedStrictTransform_zero _ (M.comap q)
  have h1 : (M.comap q).comap s'.isoZero.hom = M.comap (s'.isoZero.hom ≫ q) :=
    (comap_eq_comap_comap_of_comp_eq_consolidated457 s'.isoZero.hom (s'.isoZero.hom ≫ q) q rfl M).symm
  have h2 : M.comap (s'.isoZero.hom ≫ q)
      = (M.comap s.isoZero.hom).comap (D.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _)) :=
    comap_eq_comap_comap_of_comp_eq_consolidated457 (D.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _))
      (s'.isoZero.hom ≫ q) s.isoZero.hom hsq M
  have h3 : (M.comap s.isoZero.hom).comap (D.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _))
      = (s.iteratedStrictTransform 0 M).comap (D.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _)) :=
    congrArg (fun I : (s.obj 0).IdealSheafData =>
      I.comap (D.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _))) hs.symm
  have hzero : s'.iteratedStrictTransform 0 (M.comap q)
      = (s.iteratedStrictTransform 0 M).comap (D.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _)) :=
    hs'.trans (h1.trans (h2.trans h3))
  refine (SequenceOfBlowupsPullback.iteratedStrictTransform_eq_comap_lastMap D (fun i => s.iteratedStrictTransform i M)
    (fun j => s'.iteratedStrictTransform j (M.comap q)) ?_ ?_ hzero ?_ ?_).symm
  · intro i hi
    exact MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s.toMarkedSequenceOfBlowups i hi
  · intro j hj
    exact MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV' s'.toMarkedSequenceOfBlowups j hj
  · intro i _
    exact BlowupSequenceData.iteratedStrictTransform_succ _ i M
  · intro j _
    exact BlowupSequenceData.iteratedStrictTransform_succ _ j (M.comap q)

section
variable [Flat q] (hstar : MaxContactCoverProperties.{u}) (hV : S.IsAdmissible) (hV' : (pullbackWithNontrivialBoundary S q).IsAdmissible) (i : ℕ) (hi : i < S.boundary.length)
include hstar hV hV'

theorem lastBoundary_comap_lastMap_eq_top (hdead : (S.boundary[i]'hi).comap q = ⊤) :
    ((s.boundary s.length)[i]'(lt_of_lt_of_le hi (length_boundary_le_length_lastBoundary S s))).comap D.lastMap =
      ⊤ := by
  have h1 : (s.boundary s.length)[i]'(lt_of_lt_of_le hi (length_boundary_le_length_lastBoundary S s))
      = s.iteratedStrictTransform s.length (S.boundary[i]'hi) := getElem_lastBoundary_eq_iteratedStrictTransform S s i hi
  have h2 := iteratedStrictTransform_comap_lastMap S q s s' D hstar hV hV' (S.boundary[i]'hi)
  rw [h1, h2, hdead, BlowupSequenceData.iteratedStrictTransform_top]
  rfl

theorem getElem_lastBoundary_comap_lastMap (hlive : (S.boundary[i]'hi).comap q ≠ ⊤) :
    ((s.boundary s.length)[i]'(lt_of_lt_of_le hi (length_boundary_le_length_lastBoundary S s))).comap D.lastMap =
      (s'.boundary s'.length)[survivingBoundaryCount S q i]'(lt_of_lt_of_le
        (survivingBoundaryCount_lt_length S q i hi hlive) (length_boundary_le_length_lastBoundary (pullbackWithNontrivialBoundary S q) s')) := by
  have h1 := getElem_lastBoundary_eq_iteratedStrictTransform S s i hi
  have h2 := getElem_lastBoundary_eq_iteratedStrictTransform (pullbackWithNontrivialBoundary S q) s' (survivingBoundaryCount S q i)
    (survivingBoundaryCount_lt_length S q i hi hlive)
  have h3 := pullbackWithNontrivialBoundary_boundary_getElem S q i hi hlive
  rw [h1, h2, h3]
  exact iteratedStrictTransform_comap_lastMap S q s s' D hstar hV hV' (S.boundary[i]'hi)


end

section
variable {Y Z : Scheme.{u}} (f : Y.IdealSheafData → Z.IdealSheafData) (L : List Y.IdealSheafData) (n : ℕ) (hn : n < L.length)
include hn

private theorem sameNontrivialBoundary_take_succ_of_eq_top_consolidated457 (hf : f (L[n]'hn) = ⊤) (M : List Z.IdealSheafData)
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary ((L.take n).map f) M) :
    MarkedIdealWithBoundary.SameNontrivialBoundary ((L.take (n + 1)).map f) M := by
  rw [List.take_succ_eq_append_getElem hn, List.map_append, List.map_cons, List.map_nil, hf]
  exact sameNontrivialBoundary_append_top h

private theorem sameNontrivialBoundary_take_succ_of_getElem_eq_consolidated457 (M : List Z.IdealSheafData) (m : ℕ) (hm : m < M.length)
    (hf : f (L[n]'hn) = M[m]'hm)
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary ((L.take n).map f) (M.take m)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary ((L.take (n + 1)).map f) (M.take (m + 1)) := by
  rw [List.take_succ_eq_append_getElem hn, List.take_succ_eq_append_getElem hm, List.map_append,
    List.map_cons, List.map_nil, hf]
  exact sameNontrivialBoundary_append h (sameNontrivialBoundary_refl _)


end

theorem sameNontrivialBoundary_lastBoundary_take [Flat q] (hstar : MaxContactCoverProperties.{u})
    (hV : S.IsAdmissible) (hV' : (pullbackWithNontrivialBoundary S q).IsAdmissible) :
    ∀ n : ℕ, n ≤ S.boundary.length →
      MarkedIdealWithBoundary.SameNontrivialBoundary
        (((s.boundary s.length).take n).map fun A => A.comap D.lastMap)
        ((s'.boundary s'.length).take (survivingBoundaryCount S q n)) := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [survivingBoundaryCount_zero]
      simp only [List.take_zero, List.map_nil]
      exact sameNontrivialBoundary_refl _
  | succ n ih =>
      intro hn
      have hi : n < S.boundary.length := by omega
      have ihn := ih (le_of_lt hi)
      have hnlt : n < (s.boundary s.length).length :=
        lt_of_lt_of_le hi (length_boundary_le_length_lastBoundary S s)
      by_cases hdead : (S.boundary[n]'hi).comap q = ⊤
      · have hsc : survivingBoundaryCount S q (n + 1) = survivingBoundaryCount S q n :=
          survivingBoundaryCount_succ_of_eq_top S q n hi hdead
        have htop : ((s.boundary s.length)[n]'hnlt).comap D.lastMap = ⊤ :=
          lastBoundary_comap_lastMap_eq_top S q s s' D hstar hV hV' n hi hdead
        rw [hsc]
        exact sameNontrivialBoundary_take_succ_of_eq_top_consolidated457 (fun A => A.comap D.lastMap)
          (s.boundary s.length) n hnlt htop _ ihn
      · have hsc : survivingBoundaryCount S q (n + 1) = survivingBoundaryCount S q n + 1 :=
          survivingBoundaryCount_succ_of_ne_top S q n hi hdead
        have hclt : survivingBoundaryCount S q n < (s'.boundary s'.length).length :=
          lt_of_lt_of_le (survivingBoundaryCount_lt_length S q n hi hdead)
            (length_boundary_le_length_lastBoundary (pullbackWithNontrivialBoundary S q) s')
        have hgp : ((s.boundary s.length)[n]'hnlt).comap D.lastMap
            = (s'.boundary s'.length)[survivingBoundaryCount S q n]'hclt :=
          getElem_lastBoundary_comap_lastMap S q s s' D hstar hV hV' n hi hdead
        rw [hsc]
        exact sameNontrivialBoundary_take_succ_of_getElem_eq_consolidated457 (fun A => A.comap D.lastMap)
          (s.boundary s.length) n hnlt (s'.boundary s'.length) (survivingBoundaryCount S q n) hclt hgp ihn

private theorem sameNontrivialBoundary_congr_consolidated457 {Z : Scheme.{u}}
    {L L' M M' : List Z.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary L M) (hL : L' = L) (hM : M' = M) :
    MarkedIdealWithBoundary.SameNontrivialBoundary L' M' := by
  subst hL
  subst hM
  exact h

theorem sameNontrivialBoundary_lastBoundary_drop [Flat q] (hstar : MaxContactCoverProperties.{u})
    (hV : S.IsAdmissible) (hV' : (pullbackWithNontrivialBoundary S q).IsAdmissible) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      ((s'.boundary s'.length).drop (pullbackWithNontrivialBoundary S q).boundary.length)
      (((s.boundary s.length).drop S.boundary.length).map fun A => A.comap D.lastMap) := by
  have hN : ∀ i : ℕ, i ≤ s.length → IsNoetherian (s.obj i) := by
    intro i hi
    exact MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s.toMarkedSequenceOfBlowups i hi
  have hN' : ∀ j : ℕ, j ≤ s'.length → IsNoetherian (s'.obj j) := by
    intro j hj
    exact MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV' s'.toMarkedSequenceOfBlowups j hj
  have hfull : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun A => A.comap D.lastMap) :=
    (SequenceOfBlowupsPullback.ideal_boundary_last_eq_comap_lastMap s s' D rfl
      (sameNontrivialBoundary_nontrivialPart (S.boundary.map fun A => A.comap q)) hN hN').2
  have htake := sameNontrivialBoundary_lastBoundary_take S q s s' D hstar hV hV' S.boundary.length le_rfl
  rw [survivingBoundaryCount_length_eq] at htake
  have hsplit' : (s'.boundary s'.length).take (pullbackWithNontrivialBoundary S q).boundary.length ++
      (s'.boundary s'.length).drop (pullbackWithNontrivialBoundary S q).boundary.length = s'.boundary s'.length :=
    List.take_append_drop _ _
  have hsplit : (((s.boundary s.length).take S.boundary.length).map fun A => A.comap D.lastMap) ++
      (((s.boundary s.length).drop S.boundary.length).map fun A => A.comap D.lastMap) =
      (s.boundary s.length).map fun A => A.comap D.lastMap := by
    rw [← List.map_append, List.take_append_drop]
  refine sameNontrivialBoundary_cancel_left ?_ htake.symm
  exact sameNontrivialBoundary_congr_consolidated457 hfull hsplit' hsplit

section
variable (k : Type u) [Field k] [IsNoetherianRing k]

private theorem balancedTunedSheaf_comap_of_smooth_consolidated457 {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) (h : Y ⟶ X)
    (hsp : Smooth p) (hfp : LocallyOfFiniteType p)
    (hsh : Smooth h)
    (hfc : LocallyOfFiniteType (h ≫ p))
    (I : X.IdealSheafData) (m : ℕ) :
    FunctorialResolution.EmbeddedResolution.balancedTunedSheaf k (h ≫ p) (I.comap h) m = (FunctorialResolution.EmbeddedResolution.balancedTunedSheaf k p I m).comap h := by
  have := hsp
  have := hfp
  have := hsh
  have := hfc
  exact FunctorialResolution.EmbeddedResolution.balancedTunedSheaf_comap k p h I m

private theorem balancedTunedSheaf_congr_consolidated457 {X : Scheme.{u}} (p p' : X ⟶ Spec (CommRingCat.of k))
    (hf : LocallyOfFiniteType p)
    (hf' : LocallyOfFiniteType p')
    (hp : p = p') (I I' : X.IdealSheafData) (hI : I = I') (m : ℕ) :
    FunctorialResolution.EmbeddedResolution.balancedTunedSheaf k p I m = FunctorialResolution.EmbeddedResolution.balancedTunedSheaf k p' I' m := by
  subst hI
  subst hp
  rfl


end

theorem tunedIdealAtLength_comap_lastMap [Smooth q] (hstar : MaxContactCoverProperties.{u})
    (hV : S.IsAdmissible) (hV' : (pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hftS : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hftT : LocallyOfFiniteType
      (s'.proj s'.length ≫ (pullbackWithNontrivialBoundary S q).structMap))
    (hsm : Smooth (s.proj s.length ≫ S.structMap)) :
    (LowerDimReductionPullback.tunedIdealAtLength S s hftS).comap D.lastMap = LowerDimReductionPullback.tunedIdealAtLength (pullbackWithNontrivialBoundary S q) s' hftT := by
  have hSmoothLast : Smooth D.lastMap := SequenceOfBlowupsPullback.smooth_lastMap D
  have hcomp : D.lastMap ≫ (s.proj s.length ≫ S.structMap)
      = s'.proj s'.length ≫ (q ≫ S.structMap) := lastMap_comp_structureMorphism S q s s' D
  have hftT2 : LocallyOfFiniteType
      (s'.proj s'.length ≫ (q ≫ S.structMap)) := hftT
  have hftcomp : LocallyOfFiniteType
      (D.lastMap ≫ (s.proj s.length ≫ S.structMap)) := by
    rw [hcomp]
    exact hftT2
  have hid : s'.ideal s'.length = (s.ideal s.length).comap D.lastMap :=
    (ideal_and_boundary_comap_lastMap S q s s' D hstar hV hV').1
  have e1 := LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf S s hftS
  have e2 := LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf (pullbackWithNontrivialBoundary S q) s' hftT
  have h1 : (LowerDimReductionPullback.tunedIdealAtLength S s hftS).comap D.lastMap
      = (FunctorialResolution.EmbeddedResolution.balancedTunedSheaf S.base (s.proj s.length ≫ S.structMap) (s.ideal s.length)
          S.mult).comap D.lastMap :=
    congrArg (fun J : (s.obj s.length).IdealSheafData => J.comap D.lastMap) e1
  have h2 := balancedTunedSheaf_comap_of_smooth_consolidated457 S.base (s.proj s.length ≫ S.structMap) D.lastMap
    hsm hftS hSmoothLast hftcomp (s.ideal s.length) S.mult
  have h3 := balancedTunedSheaf_congr_consolidated457 S.base (D.lastMap ≫ (s.proj s.length ≫ S.structMap))
    (s'.proj s'.length ≫ (q ≫ S.structMap)) hftcomp hftT2 hcomp
    ((s.ideal s.length).comap D.lastMap) (s'.ideal s'.length) hid.symm S.mult
  have h4 : FunctorialResolution.EmbeddedResolution.balancedTunedSheaf S.base (s'.proj s'.length ≫ (q ≫ S.structMap))
      (s'.ideal s'.length) S.mult = LowerDimReductionPullback.tunedIdealAtLength (pullbackWithNontrivialBoundary S q) s' hftT := e2.symm
  exact h1.trans (h2.symm.trans (h3.trans h4))

private theorem markedIdealWithBoundary_mk_congr_consolidated457 {k : Type u} [inst : Field k] {X : Scheme.{u}}
    {p p' : X ⟶ Spec (CommRingCat.of k)} {I I' : X.IdealSheafData} {m m' : ℕ}
    {E E' : List X.IdealSheafData}
    (hp : p = p') (hI : I = I') (hm : m = m') (hE : E = E') :
    MarkedIdealWithBoundary.mk k X p I m E = MarkedIdealWithBoundary.mk k X p' I' m' E' := by
  subst hp
  subst hI
  subst hm
  subst hE
  rfl

theorem pullbackAlong_derivedTriple_eq [Smooth q] (hstar : MaxContactCoverProperties.{u})
    (hV : S.IsAdmissible) (hV' : (pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hftS : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hftT : LocallyOfFiniteType
      (s'.proj s'.length ≫ (pullbackWithNontrivialBoundary S q).structMap))
    (hsm : Smooth (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep keep' : ℕ) :
    ((MaxContactCoverData.derivedTriple S s hftS extra keep).pullbackAlong (s'.obj s'.length)
          (D.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap)
          D.lastMap).withBoundary
        (@List.append (s'.obj s'.length).IdealSheafData
          (extra.map fun A => A.comap D.lastMap)
          ((s'.boundary s'.length).drop keep')) =
      MaxContactCoverData.derivedTriple (pullbackWithNontrivialBoundary S q) s' hftT
        (extra.map fun A => A.comap D.lastMap) keep' := by
  refine markedIdealWithBoundary_mk_congr_consolidated457 (k := S.base) (inst := S.instField) (X := s'.obj s'.length)
    (p := D.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap)
    (p' := (MaxContactCoverData.derivedTriple (pullbackWithNontrivialBoundary S q) s' hftT
      (extra.map fun A => A.comap D.lastMap) keep').structMap)
    (I := (MaxContactCoverData.derivedTriple S s hftS extra keep).ideal.comap D.lastMap)
    (I' := (MaxContactCoverData.derivedTriple (pullbackWithNontrivialBoundary S q) s' hftT
      (extra.map fun A => A.comap D.lastMap) keep').ideal)
    (m := (MaxContactCoverData.derivedTriple S s hftS extra keep).mult)
    (m' := (MaxContactCoverData.derivedTriple (pullbackWithNontrivialBoundary S q) s' hftT
      (extra.map fun A => A.comap D.lastMap) keep').mult)
    (E := @List.append (s'.obj s'.length).IdealSheafData
      (extra.map fun A => A.comap D.lastMap) ((s'.boundary s'.length).drop keep'))
    (E' := (MaxContactCoverData.derivedTriple (pullbackWithNontrivialBoundary S q) s' hftT
      (extra.map fun A => A.comap D.lastMap) keep').boundary)
    (hp := ?_) (hI := ?_) (hm := ?_) (hE := ?_)
  · simp only [LowerDimReductionPullback.structureMorphism_derivedTriple]
    exact lastMap_comp_structureMorphism S q s s' D
  · simp only [LowerDimReductionPullback.ideal_derivedTriple]
    exact tunedIdealAtLength_comap_lastMap S q s s' D hstar hV hV' hftS hftT hsm
  · rfl
  · rfl

end

end NontrivialBoundary


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.ContinuationComparison
section
universe v


section

namespace BoundaryDeletion

private theorem take_append_getElem_cons_drop_consolidated472 {α : Type v} (L : List α) (i : ℕ)
    (h : i < L.length) : L.take i ++ L[i] :: L.drop (i + 1) = L := by
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

section
variable {X : Scheme.{u}}

private theorem sameNontrivialBoundary_congr_right_consolidated472 (L₁ L₂ L₂' : List X.IdealSheafData)
    (h : L₂ = L₂') (hbe : MarkedIdealWithBoundary.SameNontrivialBoundary L₁ L₂') :
    MarkedIdealWithBoundary.SameNontrivialBoundary L₁ L₂ := by
  subst h
  exact hbe

private theorem sameNontrivialBoundary_congr_consolidated472 (L₁ L₁' L₂ L₂' : List X.IdealSheafData)
    (h₁ : L₁ = L₁') (h₂ : L₂ = L₂') (hbe : MarkedIdealWithBoundary.SameNontrivialBoundary L₁' L₂') :
    MarkedIdealWithBoundary.SameNontrivialBoundary L₁ L₂ := by
  subst h₁
  subst h₂
  exact hbe


end

private theorem isPullback_congr_consolidated472 {X₀ Y₀ : Scheme.{u}} (φ : Y₀ ⟶ X₀) (sbase : SequenceOfBlowups X₀)
    {t₁ t₂ : SequenceOfBlowups Y₀} (h : t₁ = t₂) (hp : IsPullbackBlowupSequence φ t₁ sbase) :
    IsPullbackBlowupSequence φ t₂ sbase := by
  subst h
  exact hp

private theorem isPullback_congr_marked_consolidated472 (F : PrincipalizationAssignment.{u}) {X₀ : Scheme.{u}}
    (sbase : SequenceOfBlowups X₀) {T₁ T₂ : MarkedIdealWithBoundary.{u}} (h : T₁ = T₂)
    (φ₁ : T₁.scheme ⟶ X₀) (φ₂ : T₂.scheme ⟶ X₀) (hφ : HEq φ₁ φ₂)
    (hp : IsPullbackBlowupSequence φ₁ (F T₁).toSequenceOfBlowups sbase) :
    IsPullbackBlowupSequence φ₂ (F T₂).toSequenceOfBlowups sbase := by
  subst h
  have hee : φ₁ = φ₂ := eq_of_heq hφ
  subst hee
  exact hp

section
variable {T₁ T₂ : MarkedIdealWithBoundary.{u}} (h : T₁ = T₂)
include h

private theorem isAdmissible_of_eq_consolidated472 (hv : T₂.IsAdmissible) :
    T₁.IsAdmissible := by
  subst h
  exact hv

private theorem pred_dim_of_eq_consolidated472 (P : ℕ → Prop)
    (hp : P T₂.krullDimSucc) : P T₁.krullDimSucc := by
  subst h
  exact hp

private theorem isOrderBoundedByMult_of_eq_consolidated472 (ho : T₂.IsOrderBoundedByMult) : T₁.IsOrderBoundedByMult := by
  subst h
  exact ho

private theorem locallyOfFiniteType_of_eq_consolidated472 (h₂ : LocallyOfFiniteType T₂.structMap) :
    LocallyOfFiniteType T₁.structMap := by
  subst h
  exact h₂

private theorem isBalanced_of_eq_consolidated472 (h₁ : LocallyOfFiniteType T₁.structMap)
    (h₂ : LocallyOfFiniteType T₂.structMap)
    (hd : T₂.IsBalanced h₂) : T₁.IsBalanced h₁ := by
  subst h
  exact hd


end

section
variable (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})

private theorem isPullback_of_sameNontrivialBoundary_consolidated472
    (j c : ℕ)
    (hshift : IsBoundaryPositionInvariant P A)
    (W : MarkedIdealWithBoundary.{u}) (hWP : P W.krullDimSucc) (hWO : W.IsOrderBoundedByMult)
    (hftW : LocallyOfFiniteType W.structMap) (hWD : W.IsBalanced hftW)
    (E₁ E₂ E₁' E₂' : List W.scheme.IdealSheafData) (Dv : W.scheme.IdealSheafData)
    (hBE₁ : MarkedIdealWithBoundary.SameNontrivialBoundary E₁ E₁')
    (hBE₂ : MarkedIdealWithBoundary.SameNontrivialBoundary E₂ E₂')
    (hlen : E₁.length = j) (hlen' : E₁'.length = c)
    (hV1 : (W.withBoundary (E₁ ++ Dv :: E₂)).IsAdmissible)
    (hV2 : (W.withBoundary (E₁' ++ Dv :: E₂')).IsAdmissible)
    {X₀ : Scheme.{u}} (φ : (W.withBoundary (E₁ ++ Dv :: E₂)).scheme ⟶ X₀)
    (sbase : SequenceOfBlowups X₀)
    (hpull : IsPullbackBlowupSequence φ (A j (W.withBoundary (E₁ ++ Dv :: E₂))).toSequenceOfBlowups sbase) :
    IsPullbackBlowupSequence φ (A c (W.withBoundary (E₁' ++ Dv :: E₂'))).toSequenceOfBlowups sbase := by
  have hEq := hshift.shift W hWP hWO hftW hWD E₁ E₂ E₁' E₂' Dv hBE₁ hBE₂ hV1 hV2
  rw [hlen, hlen'] at hEq
  exact IsPullbackBlowupSequence.of_isomorphic hpull hEq

private theorem isPullbackBlowupSequence_pullbackAlong_consolidated472
    (Bl : PrincipalizationAssignment.{u}) (j c : ℕ)
    (hspec : IsBoundaryDivisorReduction P j (A j) Bl) (hshift : IsBoundaryPositionInvariant P A)
    (V : MarkedIdealWithBoundary.{u}) (hVv : V.IsAdmissible) (hP : P V.krullDimSucc) (hO : V.IsOrderBoundedByMult)
    (hftV : LocallyOfFiniteType V.structMap) (hDb : V.IsBalanced hftV)
    (Y : Scheme.{u}) (qy : Y ⟶ Spec (CommRingCat.of V.base)) (hmap : Y ⟶ V.scheme)
    (hsm : Smooth hmap) (hqy : hmap ≫ V.structMap = qy)
    (LT : List Y.IdealSheafData)
    (hVv' : ((V.pullbackAlong Y qy hmap).withBoundary LT).IsAdmissible)
    (hP' : P ((V.pullbackAlong Y qy hmap).withBoundary LT).krullDimSucc)
    (hO' : ((V.pullbackAlong Y qy hmap).withBoundary LT).IsOrderBoundedByMult)
    (hftV' : LocallyOfFiniteType
      ((V.pullbackAlong Y qy hmap).withBoundary LT).structMap)
    (hDb' : ((V.pullbackAlong Y qy hmap).withBoundary LT).IsBalanced hftV')
    (Lbd : List V.scheme.IdealSheafData) (hLbd : V.boundary = Lbd)
    (hjLbd : j < Lbd.length) (hcLT : c < LT.length)
    (hget : (Lbd[j]'hjLbd).comap hmap = LT[c]'hcLT)
    (hfull : MarkedIdealWithBoundary.SameNontrivialBoundary (Lbd.map (fun D => D.comap hmap)) LT)
    (hpre : MarkedIdealWithBoundary.SameNontrivialBoundary ((Lbd.take j).map (fun D => D.comap hmap)) (LT.take c))
    (hsuf : MarkedIdealWithBoundary.SameNontrivialBoundary ((Lbd.drop (j + 1)).map (fun D => D.comap hmap))
      (LT.drop (c + 1))) :
    IsPullbackBlowupSequence hmap (A c ((V.pullbackAlong Y qy hmap).withBoundary LT)).toSequenceOfBlowups
      (A j V).toSequenceOfBlowups := by
  have := hsm
  have hPBb : (V.pullbackAlong Y qy hmap).boundary = Lbd.map (fun D => D.comap hmap) :=
    (MarkedIdealWithBoundary.pullbackAlong_boundary V Y qy hmap).trans
      (congrArg (List.map (fun D => D.comap hmap)) hLbd)
  have hjV : j < V.boundary.length := by
    rw [hLbd]
    exact hjLbd
  have hmaplen : (Lbd.map (fun D => D.comap hmap)).length = Lbd.length := by simp
  have hlenPB : (V.pullbackAlong Y qy hmap).boundary.length = Lbd.length := by
    rw [hPBb]
    exact hmaplen
  have hjPB : j < (V.pullbackAlong Y qy hmap).boundary.length := by
    rw [hlenPB]
    exact hjLbd
  have hPW : P (V.pullbackAlong Y qy hmap).krullDimSucc := hP'
  have hOW : (V.pullbackAlong Y qy hmap).IsOrderBoundedByMult := hO'
  have hftW : LocallyOfFiniteType (V.pullbackAlong Y qy hmap).structMap := hftV'
  have hDW : (V.pullbackAlong Y qy hmap).IsBalanced hftW := hDb'
  have hLTbe : MarkedIdealWithBoundary.SameNontrivialBoundary LT (V.pullbackAlong Y qy hmap).boundary :=
    sameNontrivialBoundary_congr_right_consolidated472 LT (V.pullbackAlong Y qy hmap).boundary
      (Lbd.map (fun D => D.comap hmap)) hPBb hfull.symm
  have hPBV : (V.pullbackAlong Y qy hmap).IsAdmissible :=
    MarkedIdealWithBoundary.validOfSameNontrivialBoundary ((V.pullbackAlong Y qy hmap).withBoundary LT)
      (V.pullbackAlong Y qy hmap).boundary hVv' hLTbe
  have hsplit : (Lbd.take j).map (fun D => D.comap hmap) ++ (LT[c]'hcLT)
        :: (Lbd.drop (j + 1)).map (fun D => D.comap hmap) = Lbd.map (fun D => D.comap hmap) := by
    rw [← hget]
    have h := congrArg (fun L : List V.scheme.IdealSheafData => L.map (fun D => D.comap hmap))
      (take_append_getElem_cons_drop_consolidated472 Lbd j hjLbd)
    simpa only [List.map_append, List.map_cons] using h
  have hsplitLT : LT.take c ++ (LT[c]'hcLT) :: LT.drop (c + 1) = LT :=
    take_append_getElem_cons_drop_consolidated472 LT c hcLT
  have hPBself : (V.pullbackAlong Y qy hmap).withBoundary
        ((Lbd.take j).map (fun D => D.comap hmap) ++ (LT[c]'hcLT)
          :: (Lbd.drop (j + 1)).map (fun D => D.comap hmap)) = V.pullbackAlong Y qy hmap :=
    (congrArg (MarkedIdealWithBoundary.withBoundary (V.pullbackAlong Y qy hmap))
      (hsplit.trans hPBb.symm)).trans (MarkedIdealWithBoundary.withBoundary_self _)
  have hPBeq : (V.pullbackAlong Y qy hmap).withBoundary
        (LT.take c ++ (LT[c]'hcLT) :: LT.drop (c + 1))
      = (V.pullbackAlong Y qy hmap).withBoundary LT :=
    congrArg (MarkedIdealWithBoundary.withBoundary (V.pullbackAlong Y qy hmap)) hsplitLT
  have hpullPB := hspec.isPullbackBlowupSequence_of_smooth V hVv hP hO hDb hjV Y qy hmap hqy hPBV hPW hOW hDW hjPB
  have hpull1 : IsPullbackBlowupSequence hmap
      (A j ((V.pullbackAlong Y qy hmap).withBoundary
        ((Lbd.take j).map (fun D => D.comap hmap) ++ (LT[c]'hcLT)
          :: (Lbd.drop (j + 1)).map (fun D => D.comap hmap)))).toSequenceOfBlowups
      (A j V).toSequenceOfBlowups :=
    isPullback_congr_consolidated472 hmap (A j V).toSequenceOfBlowups
      (eq_of_heq ((A j).toSequenceOfBlowups_heq_of_eq hPBself.symm)) hpullPB
  have hV1 : ((V.pullbackAlong Y qy hmap).withBoundary
      ((Lbd.take j).map (fun D => D.comap hmap) ++ (LT[c]'hcLT)
        :: (Lbd.drop (j + 1)).map (fun D => D.comap hmap))).IsAdmissible := by
    rw [hPBself]
    exact hPBV
  have hV2 : ((V.pullbackAlong Y qy hmap).withBoundary
      (LT.take c ++ (LT[c]'hcLT) :: LT.drop (c + 1))).IsAdmissible := by
    rw [hPBeq]
    exact hVv'
  have hlenE1 : ((Lbd.take j).map (fun D => D.comap hmap)).length = j := by
    simp only [List.length_map, List.length_take]
    omega
  have hlenE1' : (LT.take c).length = c := by
    simp only [List.length_take]
    omega
  have hres := isPullback_of_sameNontrivialBoundary_consolidated472 P A j c hshift (V.pullbackAlong Y qy hmap) hPW hOW hftW hDW
    ((Lbd.take j).map (fun D => D.comap hmap)) ((Lbd.drop (j + 1)).map (fun D => D.comap hmap))
    (LT.take c) (LT.drop (c + 1)) (LT[c]'hcLT) hpre hsuf hlenE1 hlenE1' hV1 hV2 hmap
    (A j V).toSequenceOfBlowups hpull1
  exact isPullback_congr_consolidated472 hmap (A j V).toSequenceOfBlowups
    (eq_of_heq ((A c).toSequenceOfBlowups_heq_of_eq hPBeq)) hres


end

variable (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u}) (Bl : PrincipalizationAssignment.{u}) (j : ℕ)
  (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [Smooth q]
  (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
  (s' : MarkedBlowupSequenceData (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary)
  (Dt : SequenceOfBlowupsPullback q s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
  (hftS : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
  (hftT : LocallyOfFiniteType
    (s'.proj s'.length ≫ (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap))

theorem isPullbackBlowupSequence_derivedTriple
    (hstar : MaxContactCoverProperties.{u})
    (hspec : IsBoundaryDivisorReduction P j (A j) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (hV : S.IsAdmissible) (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hm : 1 ≤ S.mult)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hO' : ∀ x : ↥(NontrivialBoundary.pullbackWithNontrivialBoundary S q).scheme,
      orderAt (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hj : j < S.boundary.length)
    (hlive : (S.boundary[j]'hj).comap q ≠ ⊤)
    (hPU : P (MaxContactCoverData.derivedTriple S s hftS [] 0).krullDimSucc)
    (hVU : (MaxContactCoverData.derivedTriple S s hftS [] 0).IsAdmissible)
    (hPU' : P (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).krullDimSucc)
    (hVU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).IsAdmissible) :
    IsPullbackBlowupSequence Dt.lastMap
      (A (NontrivialBoundary.survivingBoundaryCount S q j)
        (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0)).toSequenceOfBlowups
      (A j (MaxContactCoverData.derivedTriple S s hftS [] 0)).toSequenceOfBlowups := by
  classical
  have hflatq : Flat q := inferInstance
  have hSmoothLast : Smooth Dt.lastMap := Dt.smooth_lastMap
  have hsm : Smooth (s.proj s.length ≫ S.structMap) := by
    have hsmU := hVU.smooth
    rwa [LowerDimReductionPullback.structureMorphism_derivedTriple] at hsmU
  have hpb0 := NontrivialBoundary.pullbackAlong_derivedTriple_eq S q s s' Dt hstar hV hV' hftS hftT hsm [] 0 0
  have hOU := LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hftS [] 0 hVU
  have hDU := LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hm hO s hftS [] 0 hVU
  have hOU' := LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' hm hO' s'
    hftT [] 0 hVU'
  have hDU' := LowerDimReductionPullback.isBalanced_derivedTriple hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' hm hO' s'
    hftT [] 0 hVU'
  have hUb : (MaxContactCoverData.derivedTriple S s hftS [] 0).boundary = s.boundary s.length := by
    simp
  have hjL : j < (s.boundary s.length).length :=
    lt_of_lt_of_le hj (NontrivialBoundary.length_boundary_le_length_lastBoundary S s)
  have hcLT : NontrivialBoundary.survivingBoundaryCount S q j < (s'.boundary s'.length).length :=
    lt_of_lt_of_le (NontrivialBoundary.survivingBoundaryCount_lt_length S q j hj hlive)
      (NontrivialBoundary.length_boundary_le_length_lastBoundary (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s')
  have hget : ((s.boundary s.length)[j]'hjL).comap Dt.lastMap
      = (s'.boundary s'.length)[NontrivialBoundary.survivingBoundaryCount S q j]'hcLT :=
    NontrivialBoundary.getElem_lastBoundary_comap_lastMap S q s s' Dt hstar hV hV' j hj hlive
  have hfull : MarkedIdealWithBoundary.SameNontrivialBoundary
      ((s.boundary s.length).map (fun D => D.comap Dt.lastMap)) (s'.boundary s'.length) :=
    ((NontrivialBoundary.ideal_and_boundary_comap_lastMap S q s s' Dt hstar hV hV').2).symm
  have hpre : MarkedIdealWithBoundary.SameNontrivialBoundary
      (((s.boundary s.length).take j).map (fun D => D.comap Dt.lastMap))
      ((s'.boundary s'.length).take (NontrivialBoundary.survivingBoundaryCount S q j)) :=
    NontrivialBoundary.sameNontrivialBoundary_lastBoundary_take S q s s' Dt hstar hV hV' j (le_of_lt hj)
  have hpre1 : MarkedIdealWithBoundary.SameNontrivialBoundary
      (((s.boundary s.length).take (j + 1)).map (fun D => D.comap Dt.lastMap))
      ((s'.boundary s'.length).take (NontrivialBoundary.survivingBoundaryCount S q j + 1)) := by
    have hh := NontrivialBoundary.sameNontrivialBoundary_lastBoundary_take S q s s' Dt hstar hV hV' (j + 1) hj
    rwa [NontrivialBoundary.survivingBoundaryCount_succ_of_ne_top S q j hj hlive] at hh
  have hmapsplit : ((s.boundary s.length).take (j + 1)).map (fun D => D.comap Dt.lastMap)
        ++ ((s.boundary s.length).drop (j + 1)).map (fun D => D.comap Dt.lastMap)
      = (s.boundary s.length).map (fun D => D.comap Dt.lastMap) := by
    rw [← List.map_append, List.take_append_drop]
  have hltsplit : (s'.boundary s'.length).take (NontrivialBoundary.survivingBoundaryCount S q j + 1)
        ++ (s'.boundary s'.length).drop (NontrivialBoundary.survivingBoundaryCount S q j + 1)
      = s'.boundary s'.length := List.take_append_drop _ _
  have happ := sameNontrivialBoundary_congr_consolidated472 _ _ _ _ hmapsplit hltsplit hfull
  have hsuf := NontrivialBoundary.sameNontrivialBoundary_cancel_left happ hpre1
  have hVW' := isAdmissible_of_eq_consolidated472 hpb0 hVU'
  have hPW' := pred_dim_of_eq_consolidated472 hpb0 P hPU'
  have hOW' := isOrderBoundedByMult_of_eq_consolidated472 hpb0 hOU'
  have hftW' := locallyOfFiniteType_of_eq_consolidated472 hpb0 hVU'.locallyOfFiniteType
  have hDW' := isBalanced_of_eq_consolidated472 hpb0 hftW' hVU'.locallyOfFiniteType hDU'
  have hinner := isPullbackBlowupSequence_pullbackAlong_consolidated472 P A Bl j (NontrivialBoundary.survivingBoundaryCount S q j) hspec hshift
    (MaxContactCoverData.derivedTriple S s hftS [] 0) hVU hPU hOU hVU.locallyOfFiniteType hDU
    (s'.obj s'.length) (Dt.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS [] 0).structMap)
    Dt.lastMap hSmoothLast rfl (s'.boundary s'.length)
    hVW' hPW' hOW' hftW' hDW'
    (s.boundary s.length) hUb hjL hcLT hget hfull hpre hsuf
  exact isPullback_congr_marked_consolidated472 (A (NontrivialBoundary.survivingBoundaryCount S q j))
    (A j (MaxContactCoverData.derivedTriple S s hftS [] 0)).toSequenceOfBlowups hpb0 Dt.lastMap Dt.lastMap
    HEq.rfl hinner

include Dt in
theorem isPullbackBlowupSequence_appendLowerDimReduction
    (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (hstar : MaxContactCoverProperties.{u})
    (hspec : IsBoundaryDivisorReduction P j (A j) Bl)
    (hspec' : IsBoundaryDivisorReduction P (NontrivialBoundary.survivingBoundaryCount S q j)
      (A (NontrivialBoundary.survivingBoundaryCount S q j)) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (hV : S.IsAdmissible) (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hm : 1 ≤ S.mult)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hO' : ∀ x : ↥(NontrivialBoundary.pullbackWithNontrivialBoundary S q).scheme,
      orderAt (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hj : j < S.boundary.length)
    (hlive : (S.boundary[j]'hj).comap q ≠ ⊤)
    (hPU : P (MaxContactCoverData.derivedTriple S s hftS [] 0).krullDimSucc)
    (hVU : (MaxContactCoverData.derivedTriple S s hftS [] 0).IsAdmissible)
    (hPU' : P (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).krullDimSucc)
    (hVU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).IsAdmissible)
    (hdimU : (MaxContactCoverData.derivedTriple S s hftS [] 0).krullDimSucc ≤ T.krullDimSucc)
    (hdimU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).krullDimSucc ≤ T.krullDimSucc) :
    IsPullbackBlowupSequence q
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S₀ _ i => A i S₀) (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s'
        [] 0 (NontrivialBoundary.survivingBoundaryCount S q j)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S₀ _ i => A i S₀) S s [] 0
        j).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  classical
  have hjb : j < ((([] : List (s.obj s.length).IdealSheafData))
      ++ List.drop 0 (s.boundary s.length)).length := by
    simpa using lt_of_lt_of_le hj (NontrivialBoundary.length_boundary_le_length_lastBoundary S s)
  have hjb' : NontrivialBoundary.survivingBoundaryCount S q j <
      ((([] : List (s'.obj s'.length).IdealSheafData))
        ++ List.drop 0 (s'.boundary s'.length)).length := by
    simpa using lt_of_lt_of_le (NontrivialBoundary.survivingBoundaryCount_lt_length S q j hj hlive)
      (NontrivialBoundary.length_boundary_le_length_lastBoundary (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s')
  obtain ⟨hmk, hEq, -⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A Bl j hspec
    (fun S₀ _ i => A i S₀) (fun _ _ _ => rfl) S hV hm hO s [] 0 hftS hdimU hPU hVU hjb (by simp)
  obtain ⟨hmk', hEq', -⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A Bl
    (NontrivialBoundary.survivingBoundaryCount S q j) hspec' (fun S₀ _ i => A i S₀) (fun _ _ _ => rfl)
    (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' hm hO' s' [] 0 hftT hdimU' hPU' hVU' hjb' (by simp)
  rw [hEq, hEq']
  refine isPullbackBlowupSequence_append_same_field q s _ s' _ hinv Dt ?_
  exact SequenceOfBlowupsPullback.toBlowupDataOfSeq
    (IsPullbackBlowupSequence.nonempty_sequenceOfBlowupsPullback
      (isPullbackBlowupSequence_derivedTriple (P := P) (A := A) (Bl := Bl) (j := j) (S := S) (q := q)
        (s := s) (s' := s') (Dt := Dt) (hftS := hftS) (hftT := hftT) (hstar := hstar)
        (hspec := hspec) (hshift := hshift) (hV := hV) (hV' := hV') (hm := hm) (hO := hO)
        (hO' := hO') (hj := hj) (hlive := hlive) (hPU := hPU) (hVU := hVU) (hPU' := hPU')
        (hVU' := hVU'))).some

include Dt in
def continuationComparison
    (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (hstar : MaxContactCoverProperties.{u})
    (hspec : IsBoundaryDivisorReduction P j (A j) Bl)
    (hspec' : IsBoundaryDivisorReduction P (NontrivialBoundary.survivingBoundaryCount S q j)
      (A (NontrivialBoundary.survivingBoundaryCount S q j)) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (hV : S.IsAdmissible) (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hm : 1 ≤ S.mult)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hO' : ∀ x : ↥(NontrivialBoundary.pullbackWithNontrivialBoundary S q).scheme,
      orderAt (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hj : j < S.boundary.length)
    (hlive : (S.boundary[j]'hj).comap q ≠ ⊤)
    (hPU : P (MaxContactCoverData.derivedTriple S s hftS [] 0).krullDimSucc)
    (hVU : (MaxContactCoverData.derivedTriple S s hftS [] 0).IsAdmissible)
    (hPU' : P (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).krullDimSucc)
    (hVU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).IsAdmissible)
    (hdimU : (MaxContactCoverData.derivedTriple S s hftS [] 0).krullDimSucc ≤ T.krullDimSucc)
    (hdimU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).krullDimSucc ≤ T.krullDimSucc) :
    SequenceOfBlowupsPullback q
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S₀ _ i => A i S₀) (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s'
        [] 0 (NontrivialBoundary.survivingBoundaryCount S q j)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S₀ _ i => A i S₀) S s [] 0 j).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
  (IsPullbackBlowupSequence.nonempty_sequenceOfBlowupsPullback
    (isPullbackBlowupSequence_appendLowerDimReduction (P := P) (A := A) (Bl := Bl) (j := j) (S := S) (q := q)
      (s := s) (s' := s') (Dt := Dt) (hftS := hftS) (hftT := hftT)
      (hinv := hinv) (T := T) (hstar := hstar) (hspec := hspec) (hspec' := hspec')
      (hshift := hshift) (hV := hV) (hV' := hV') (hm := hm) (hO := hO) (hO' := hO')
      (hj := hj) (hlive := hlive) (hPU := hPU) (hVU := hVU) (hPU' := hPU') (hVU' := hVU')
      (hdimU := hdimU) (hdimU' := hdimU'))).some

end BoundaryDeletion


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TrivialDivisorContinuation
section


section

namespace TrivialDivisorContinuation

private theorem hom_apply_congr_consolidated471 {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g) (x : ↥A) : f x = g x := by
  subst h; rfl

private theorem mem_support_of_eq_consolidated471 {A : Scheme.{u}} {M : A.IdealSheafData} {x y : ↥A} (h : x = y)
    (hx : y ∈ M.support) : x ∈ M.support := by
  subst h; exact hx

private theorem projectionToBase_zero_isoObjZero_inv_apply_consolidated471 {W : Scheme.{u}} (n : FunctorialResolution.EmbeddedResolution.BlowupSequenceData W) (w : ↥W) :
    (n.projectionToBase 0) (n.isoZero.inv w) = w :=
  (hom_apply_congr_consolidated471 (FunctorialResolution.EmbeddedResolution.BlowupSequenceData.projectionToBase_zero n) (n.isoZero.inv w)).trans
    (Scheme.inv_hom_apply n.isoZero w)

private theorem notMem_support_of_eq_top_consolidated471 {A : Scheme.{u}} {M : A.IdealSheafData} (h : M = ⊤)
    (x : ↥A) : x ∉ M.support := by
  have h2 : (↑M.support : Set ↥A) = ∅ :=
    (AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty M).mp h
  intro hx
  have hx' : x ∈ (↑M.support : Set ↥A) := hx
  rw [h2] at hx'
  exact hx'

private theorem false_of_mem_support_comp_consolidated471 {X' Y W Z : Scheme.{u}} (q : X' ⟶ Y) (pr : W ⟶ Y)
    (M : W.IdealSheafData)
    (hImageDisjoint : ∀ y : ↥W, y ∈ M.support → ∀ x : ↥X', q x ≠ pr y)
    (g : Z ⟶ W) (z : ↥Z) (x : ↥X') (hx : q x = (g ≫ pr) z)
    (hz : g z ∈ M.support) : False :=
  hImageDisjoint (g z) hz x hx

private theorem false_of_mem_support_comp_comp_consolidated471 {X' Y W Z Z' : Scheme.{u}} (q : X' ⟶ Y)
    (pr : W ⟶ Y) (M : W.IdealSheafData)
    (hImageDisjoint : ∀ y : ↥W, y ∈ M.support → ∀ x : ↥X', q x ≠ pr y)
    (g : Z ⟶ Z') (h : Z' ⟶ W) (z : ↥Z) (x : ↥X') (hx : q x = (g ≫ (h ≫ pr)) z)
    (hz : h (g z) ∈ M.support) : False :=
  hImageDisjoint (h (g z)) hz x hx

theorem nonempty_pullback_appendLowerDimReduction_of_comap_eq_top
    (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u}) (j₁ : ℕ)
    (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [Smooth q]
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (s' : MarkedBlowupSequenceData (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary)
    (D : SequenceOfBlowupsPullback q s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hstar : MaxContactCoverProperties.{u}) (hspec : IsBoundaryDivisorReduction P j₁ (A j₁) B)
    (hV : S.IsAdmissible) (hm : 1 ≤ S.mult)
    (hO : ∀ x : S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hP : P (MaxContactCoverData.derivedTriple S s hft [] 0).krullDimSucc)
    (hVc : (MaxContactCoverData.derivedTriple S s hft [] 0).IsAdmissible)
    (hj : j₁ < (s.boundary s.length).length)
    (hComapTop : ((s.boundary s.length).get ⟨j₁, hj⟩).comap D.lastMap = ⊤)
    (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (hdim : (MaxContactCoverData.derivedTriple S s hft [] 0).krullDimSucc ≤ T.krullDimSucc) :
    Nonempty (SequenceOfBlowupsPullback q s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') S s [] 0
        j₁).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  classical
  set Dj := (s.boundary s.length).get ⟨j₁, hj⟩ with hDtopDef
  have hmapeq : s.toMarkedSequenceOfBlowups.projectionToBase s.toMarkedSequenceOfBlowups.length = s.toBlowupSequenceData.projectionToBase s.length :=
    FunctorialResolution.EmbeddedResolution.BlowupSequenceData.toSequenceOfBlowups_projectionToBase s.toBlowupSequenceData s.length
  have hImageDisjoint : ∀ y : ↥(s.obj s.length), y ∈ Dj.support →
      ∀ x'' : ↥X', q x'' ≠ (s.toBlowupSequenceData.projectionToBase s.length) y := by
    intro y hy x'' hxy
    have hpb := D.isPullback_lastMap
    have hcomm : (s.toMarkedSequenceOfBlowups.projectionToBase s.toMarkedSequenceOfBlowups.length) y = q x'' :=
      (hom_apply_congr_consolidated471 hmapeq y).trans hxy.symm
    obtain ⟨w, hw1, -⟩ :=
      AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback y x'' hcomm
    have h1 : D.lastMap (hpb.isoPullback.inv w) = y :=
      (hom_apply_congr_consolidated471 hpb.isoPullback_inv_fst w).trans hw1
    have h4 : (hpb.isoPullback.inv w) ∈ (Dj.comap D.lastMap).support :=
      Scheme.IdealSheafData.mem_support_comap.mpr (mem_support_of_eq_consolidated471 h1 hy)
    exact notMem_support_of_eq_top_consolidated471 hComapTop _ h4
  have hb : (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0).boundary = s.boundary s.length := by
    rw [FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple_boundary]
    simp
  have hj' : j₁ < (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0).boundary.length := by
    rw [hb]; exact hj
  have hget : (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0).boundary.get ⟨j₁, hj'⟩ = Dj := by
    rw [hDtopDef]
    have hgen : ∀ (L L' : List (s.obj s.length).IdealSheafData), L = L' →
        ∀ (h1 : j₁ < L.length) (h2 : j₁ < L'.length), L.get ⟨j₁, h1⟩ = L'.get ⟨j₁, h2⟩ := by
      rintro L L' rfl h1 h2
      rfl
    exact hgen _ _ hb hj' hj
  have hOB := FunctorialResolution.EmbeddedResolution.LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hft [] 0 hVc
  have hbalanced := FunctorialResolution.EmbeddedResolution.LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hm hO s hft [] 0 hVc
  obtain ⟨Dv, bb, -, hD0, hcen, hbtrue, hstrictD, -, -⟩ :=
    hspec.shape (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0) hVc hP hOB hbalanced hj'
  have hInduction : ∀ r : ℕ,
      r ≤ (A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).length →
      ∀ z : ↥((A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).schemeAt r),
        z ∈ (Dv r).support →
        ((A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).projectionToBase r) z
          ∈ Dj.support := by
    intro r
    induction r with
    | zero =>
      intro _ z hz
      rw [hD0, hget] at hz
      exact mem_support_of_eq_consolidated471 (hom_apply_congr_consolidated471 (FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_zero _) z)
        (Scheme.IdealSheafData.mem_support_comap.mp hz)
    | succ r ih =>
      intro hr z hz
      have hrlt : r < (A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).length := hr
      have hmem : ((A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).transitionMapSucc r) z
          ∈ (Dv r).support := by
        by_cases hc : bb = true ∧ r = 0
        · obtain ⟨hb1, hb2⟩ := hc
          subst hb2
          obtain ⟨-, -, hD1⟩ := hbtrue hb1
          have hz' : z ∈ (Dv 1).support := hz
          rw [hD1] at hz'
          exact Scheme.IdealSheafData.mem_support_comap.mp hz'
        · rw [hstrictD r hrlt hc] at hz
          exact FunctorialResolution.EmbeddedResolution.support_strictTransform_subset_preimage _ _ _ hz
      have hnext := ih (le_of_lt hrlt) _ hmem
      exact mem_support_of_eq_consolidated471 (hom_apply_congr_consolidated471 (FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_succ _ r) z) hnext
  have hcent : ∀ nn : FunctorialResolution.EmbeddedResolution.BlowupSequenceData (s.obj s.length),
      nn = FunctorialResolution.EmbeddedResolution.BlowupSequenceData.ofSequenceOfBlowups
        (A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).toSequenceOfBlowups →
      ∀ (r : ℕ) (z : ↥(nn.obj r)), z ∈ (nn.center r).support → r < nn.length →
        (nn.projectionToBase r) z ∈ Dj.support := by
    rintro nn rfl r z hz hr
    have hr' : r < (A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).length := hr
    have hz2 : z ∈ ((A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).center r).support :=
      hz
    have hmem := hInduction r (le_of_lt hr') z (hcen r hr' hz2)
    exact mem_support_of_eq_consolidated471 (hom_apply_congr_consolidated471 (FunctorialResolution.EmbeddedResolution.BlowupSequenceData.ofSequenceOfBlowups_projectionToBase
      (A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).toSequenceOfBlowups r) z) hmem
  have c : FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPullback q s'.toSequenceOfBlowups s.toSequenceOfBlowups := by
    rw [← FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups s,
        ← FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups s']
    exact D
  have hcd : ∀ (tt : FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData (s.proj s.length ≫ S.structMap)
      (s.ideal s.length) S.mult (s.boundary s.length)),
      (s.append tt hinv).toSequenceOfBlowups = (s.toBlowupSequenceData.append tt.toBlowupSequenceData).toSequenceOfBlowups := fun tt =>
    congrArg FunctorialResolution.EmbeddedResolution.BlowupSequenceData.toSequenceOfBlowups
      ((FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData.append_toBlowupSequenceData s tt hinv).trans rfl)
  have main : ∀ (tt : FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData (s.proj s.length ≫ S.structMap)
        (s.ideal s.length) S.mult (s.boundary s.length)),
      tt.toBlowupSequenceData = FunctorialResolution.EmbeddedResolution.BlowupSequenceData.ofSequenceOfBlowups
        (A j₁ (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.derivedTriple S s hft [] 0)).toSequenceOfBlowups →
      Nonempty (FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPullback q s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (s.append tt hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
    intro tt htt
    have hcn := hcent tt.toBlowupSequenceData htt
    rw [FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups s',
        FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups (s.append tt hinv), hcd tt]
    refine FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPullback.nonempty_append_of_disjoint_centers q s'.toBlowupSequenceData s.toBlowupSequenceData
      tt.toBlowupSequenceData c ?_
    intro i hi1 hi2 z hz x'' hx
    rcases eq_or_lt_of_le hi1 with he | hlt
    · subst he
      rw [FunctorialResolution.EmbeddedResolution.BlowupSequenceData.append_center_length] at hz
      rw [FunctorialResolution.EmbeddedResolution.BlowupSequenceData.projectionToBase_append_of_le_length _ _ (le_refl _)] at hx
      have hz1 := Scheme.IdealSheafData.mem_support_comap.mp hz
      have hz2 := Scheme.IdealSheafData.mem_support_comap.mp hz1
      have hy := hcn 0 _ hz2 (by omega)
      exact false_of_mem_support_comp_consolidated471 q (s.toBlowupSequenceData.projectionToBase s.length) Dj hImageDisjoint _ z x'' hx
        (mem_support_of_eq_consolidated471 (projectionToBase_zero_isoObjZero_inv_apply_consolidated471 _ _).symm hy)
    · rw [FunctorialResolution.EmbeddedResolution.BlowupSequenceData.append_center_of_length_lt _ _ hlt] at hz
      rw [FunctorialResolution.EmbeddedResolution.BlowupSequenceData.projectionToBase_append_of_length_lt _ _ hlt] at hx
      have hz1 := Scheme.IdealSheafData.mem_support_comap.mp hz
      have hy := hcn (i - s.toBlowupSequenceData.length) _ hz1 (by omega)
      exact false_of_mem_support_comp_comp_consolidated471 q (s.toBlowupSequenceData.projectionToBase s.length) Dj hImageDisjoint _
        (tt.toBlowupSequenceData.projectionToBase (i - s.toBlowupSequenceData.length)) z x'' hx hy
  obtain ⟨hmk, heq, -⟩ := FunctorialResolution.EmbeddedResolution.LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A B j₁ hspec
      (fun S' _ i => A i S') (fun _ _ _ => rfl) S hV hm hO s [] 0 hft hdim hP hVc
      (by simpa using hj) (fun Dx hDx => FunctorialResolution.EmbeddedResolution.BoundarySeparationBaseChange.orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero S s Dx hDx)
  rw [heq]
  exact main _ (FunctorialResolution.EmbeddedResolution.BlowupSequenceData.toMarkedBlowupSequenceData_toBlowupSequenceData _ _ _ _ _ _)

end TrivialDivisorContinuation


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparationPullbackComparison
section


section

namespace NontrivialBoundary

theorem nonempty_separateBoundaryPullbackComparison
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (Bl : PrincipalizationAssignment.{u})
    (hspec : ∀ i : ℕ, IsBoundaryDivisorReduction P i (A i) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [Smooth q]
    (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hdim' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).krullDimSucc ≤ T.krullDimSucc)
    (j : ℕ) (hj : j ≤ S.boundary.length) :
    Nonempty (SequenceOfBlowupsPullback q
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.survivingBoundaryCount S q j)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  classical
  have : Flat q := inferInstance
  revert hj
  induction j with
  | zero =>
    intro _
    have e0 : BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S 0
        = FunctorialResolution.EmbeddedResolution.emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary :=
      MaxContactCoverData.separateBoundary_zero hinv T (fun S₀ _ i => A i S₀) S
    have e0' : BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.survivingBoundaryCount S q 0)
        = FunctorialResolution.EmbeddedResolution.emptyMarkedBlowupSequenceData (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap
            (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult
            (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary := by
      rw [NontrivialBoundary.survivingBoundaryCount_zero]
      exact MaxContactCoverData.separateBoundary_zero hinv T (fun S₀ _ i => A i S₀)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
    rw [e0, e0']
    simp only [FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups]
    refine ⟨SequenceOfBlowupsPullback.ofCentersMissImage q _ ?_ _ ?_⟩
    · intro i hi
      simp at hi
    · simp
  | succ j ih =>
    intro hj1
    have hjS : j < S.boundary.length := Nat.lt_of_succ_le hj1
    obtain ⟨D⟩ := ih (Nat.le_of_succ_le hj1)
    have hftS : LocallyOfFiniteType
        ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).proj
            (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).length ≫ S.structMap) :=
      BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV _ _ le_rfl
    have hftT : LocallyOfFiniteType
        ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
              (NontrivialBoundary.survivingBoundaryCount S q j)).proj
            (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
              (NontrivialBoundary.survivingBoundaryCount S q j)).length
          ≫ (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap) :=
      BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV'
        _ _ le_rfl
    have hm : 1 ≤ S.mult := hV.one_le_mult
    have hdimU : (MaxContactCoverData.derivedTriple S
          (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j) hftS [] 0).krullDimSucc ≤ T.krullDimSucc :=
      hstar.derivedTriple_dim_le (T := T) hV (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j) hftS [] 0 hdimS
    have hPU :
        P (MaxContactCoverData.derivedTriple S (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j) hftS [] 0).krullDimSucc :=
      hmono _ _ hdimU hPdimT
    have hVU := BoundarySeparationBaseChange.isAdmissible_derivedTriple_nil hstar S hV
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j) hftS
    have hdimU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
            (NontrivialBoundary.survivingBoundaryCount S q j)) hftT [] 0).krullDimSucc ≤ T.krullDimSucc :=
      hstar.derivedTriple_dim_le (T := T) hV'
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.survivingBoundaryCount S q j))
        hftT [] 0 hdim'
    have hPU' : P (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
            (NontrivialBoundary.survivingBoundaryCount S q j)) hftT [] 0).krullDimSucc :=
      hmono _ _ hdimU' hPdimT
    have hVU' := BoundarySeparationBaseChange.isAdmissible_derivedTriple_nil hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV'
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.survivingBoundaryCount S q j))
      hftT
    have hO' : ∀ x : ↥(NontrivialBoundary.pullbackWithNontrivialBoundary S q).scheme,
        orderAt (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal x ≤ ((S.mult : ℕ) : ℕ∞) :=
      fun x => BoundarySeparationBaseChange.orderAt_pullbackTriple_le_mult S q hV hO x
    have eS : BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S (j + 1)
        = MaxContactReduction.appendLowerDimReduction hinv T (fun S₀ _ i => A i S₀) S
            (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j) [] 0 j :=
      MaxContactCoverData.separateBoundary_succ hinv T (fun S₀ _ i => A i S₀) S j
    by_cases hlive : (S.boundary[j]'hjS).comap q = ⊤
    · have eT : NontrivialBoundary.survivingBoundaryCount S q (j + 1) = NontrivialBoundary.survivingBoundaryCount S q j :=
        NontrivialBoundary.survivingBoundaryCount_succ_of_eq_top S q j hjS hlive
      rw [eS, eT]
      have hjlen : j < ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).boundary
          (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).length).length :=
        lt_of_lt_of_le hjS
          (NontrivialBoundary.length_boundary_le_length_lastBoundary S (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j))
      have hBoundaryTop : (((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).boundary
              (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).length).get ⟨j, hjlen⟩).comap D.lastMap
          = ⊤ := by
        rw [List.get_eq_getElem]
        exact NontrivialBoundary.lastBoundary_comap_lastMap_eq_top S q
          (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j)
          (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
            (NontrivialBoundary.survivingBoundaryCount S q j)) D hstar hV hV' j hjS hlive
      exact TrivialDivisorContinuation.nonempty_pullback_appendLowerDimReduction_of_comap_eq_top P A Bl j S q
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j)
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.survivingBoundaryCount S q j))
        D hftS hstar (hspec j) hV hm hO hPU hVU hjlen hBoundaryTop hinv T hdimU
    · have eT : BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
            (NontrivialBoundary.survivingBoundaryCount S q (j + 1))
          = MaxContactReduction.appendLowerDimReduction hinv T (fun S₀ _ i => A i S₀) (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
              (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
                (NontrivialBoundary.survivingBoundaryCount S q j)) [] 0 (NontrivialBoundary.survivingBoundaryCount S q j) := by
        rw [NontrivialBoundary.survivingBoundaryCount_succ_of_ne_top S q j hjS hlive]
        exact MaxContactCoverData.separateBoundary_succ hinv T (fun S₀ _ i => A i S₀)
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q) (NontrivialBoundary.survivingBoundaryCount S q j)
      rw [eS, eT]
      exact ⟨BoundaryDeletion.continuationComparison (P := P) (A := A) (Bl := Bl) (j := j) (S := S)
        (q := q) (s := BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j)
        (s' := BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.survivingBoundaryCount S q j))
        (Dt := D) (hftS := hftS) (hftT := hftT) (hinv := hinv) (T := T)
        (hstar := hstar) (hspec := hspec j) (hspec' := hspec (NontrivialBoundary.survivingBoundaryCount S q j))
        (hshift := hshift) (hV := hV) (hV' := hV') (hm := hm) (hO := hO) (hO' := hO')
        (hj := hjS) (hlive := hlive) (hPU := hPU) (hVU := hVU) (hPU' := hPU') (hVU' := hVU')
        (hdimU := hdimU) (hdimU' := hdimU')⟩

def separateBoundaryPullbackComparison
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (Bl : PrincipalizationAssignment.{u})
    (hspec : ∀ i : ℕ, IsBoundaryDivisorReduction P i (A i) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [Smooth q]
    (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hdim' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).krullDimSucc ≤ T.krullDimSucc)
    (j : ℕ) (hj : j ≤ S.boundary.length) :
    SequenceOfBlowupsPullback q
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.survivingBoundaryCount S q j)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
  (nonempty_separateBoundaryPullbackComparison P hmono A Bl hspec hshift hstar hinv T hPdimT S q hV hO hdimS hV' hdim'
    j hj).some

end NontrivialBoundary


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LowerDimensionalContinuation
section


section

namespace StrictTransformComparison

variable (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u}) (Bl : PrincipalizationAssignment.{u})
  (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [Smooth q]
  (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
  (s' : MarkedBlowupSequenceData (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary)
  (Dt : SequenceOfBlowupsPullback q s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
  (hftS : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
  (hftT : LocallyOfFiniteType
    (s'.proj s'.length ≫ (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap))

theorem strictTransformAtLength_comap_lastMap
    (hstar : MaxContactCoverProperties.{u})
    (hV : S.IsAdmissible) (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (H : S.scheme.IdealSheafData) :
    MaxContactReduction.strictTransformAtLength s' (H.comap q)
      = (MaxContactReduction.strictTransformAtLength s H).comap Dt.lastMap := by
  have : Flat q := inferInstance
  have h1 : MaxContactReduction.strictTransformAtLength s' (H.comap q) = s'.iteratedStrictTransform s'.length (H.comap q) := by
    rw [MaxContactReduction.strictTransformAtLength_eq, BoundarySeparationByMaxContact.iteratedStrictTransform_eq_toBlowupSequenceData]
  have h2 : MaxContactReduction.strictTransformAtLength s H = s.iteratedStrictTransform s.length H := by
    rw [MaxContactReduction.strictTransformAtLength_eq, BoundarySeparationByMaxContact.iteratedStrictTransform_eq_toBlowupSequenceData]
  rw [h1, h2]
  exact (NontrivialBoundary.iteratedStrictTransform_comap_lastMap S q s s' Dt hstar hV hV' H).symm

include Dt in
theorem isPullbackBlowupSequence_appendLowerDimReduction
    (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (hstar : MaxContactCoverProperties.{u})
    (hspec : IsBoundaryDivisorReduction P 0 (A 0) Bl)
    (H : S.scheme.IdealSheafData)
    (hV : S.IsAdmissible) (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hm : 1 ≤ S.mult)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hO' : ∀ x : ↥(NontrivialBoundary.pullbackWithNontrivialBoundary S q).scheme,
      orderAt (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hdimU : (MaxContactCoverData.derivedTriple S s hftS
        [MaxContactReduction.strictTransformAtLength s H] S.boundary.length).krullDimSucc ≤ T.krullDimSucc)
    (hPU : P (MaxContactCoverData.derivedTriple S s hftS
        [MaxContactReduction.strictTransformAtLength s H] S.boundary.length).krullDimSucc)
    (hVU : (MaxContactCoverData.derivedTriple S s hftS
        [MaxContactReduction.strictTransformAtLength s H] S.boundary.length).IsAdmissible)
    (hdimU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).krullDimSucc ≤ T.krullDimSucc)
    (hPU' : P (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).krullDimSucc)
    (hVU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).IsAdmissible)
    (hsep : BoundarySeparationByMaxContact.BoundarySeparated S s S.boundary.length)
    (hsep' : BoundarySeparationByMaxContact.BoundarySeparated (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s'
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) :
    IsPullbackBlowupSequence q
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S₀ _ i => A i S₀) (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s'
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length 0).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S₀ _ i => A i S₀) S s
        [MaxContactReduction.strictTransformAtLength s H] S.boundary.length 0).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have : Flat q := inferInstance
  have hSmoothLast : Smooth Dt.lastMap := SequenceOfBlowupsPullback.smooth_lastMap Dt
  have hsm : Smooth (s.proj s.length ≫ S.structMap) :=
    BoundarySeparationByMaxContact.smooth_projectionToBase_comp hstar S hV s s.length le_rfl
  have hft1 : MaxContactReduction.strictTransformAtLength s' (H.comap q)
      = (MaxContactReduction.strictTransformAtLength s H).comap Dt.lastMap :=
    strictTransformAtLength_comap_lastMap S q s s' Dt hstar hV hV' H
  have hlist : List.map (fun Z : (s.obj s.length).IdealSheafData => Z.comap Dt.lastMap)
      [MaxContactReduction.strictTransformAtLength s H] = [MaxContactReduction.strictTransformAtLength s' (H.comap q)] :=
    congrArg (fun Z => [Z]) hft1.symm
  have hdrop : MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.map (fun Z : (s.obj s.length).IdealSheafData => Z.comap Dt.lastMap)
        (List.drop S.boundary.length (s.boundary s.length)))
      (List.drop (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length (s'.boundary s'.length)) :=
    NontrivialBoundary.sameNontrivialBoundary_symm
      (NontrivialBoundary.sameNontrivialBoundary_lastBoundary_drop S q s s' Dt hstar hV hV')
  have e1 : ((MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
        S.boundary.length).pullbackAlong (s'.obj s'.length)
      (Dt.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
        S.boundary.length).structMap) Dt.lastMap).boundary
      = List.map (fun D => D.comap Dt.lastMap)
        (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
          S.boundary.length).boundary :=
    MarkedIdealWithBoundary.pullbackAlong_boundary _ _ _ _
  have e2 := MaxContactCoverData.derivedTriple_boundary S s hftS
    [MaxContactReduction.strictTransformAtLength s H] S.boundary.length
  have e3 := MaxContactCoverData.derivedTriple_boundary (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
    [MaxContactReduction.strictTransformAtLength s' (H.comap q)] (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length
  have hbe : MarkedIdealWithBoundary.SameNontrivialBoundary
      ((MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
          S.boundary.length).pullbackAlong (s'.obj s'.length)
        (Dt.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
          S.boundary.length).structMap) Dt.lastMap).boundary
      (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).boundary := by
    rw [e1, e2, e3, hft1]
    exact NontrivialBoundary.sameNontrivialBoundary_cons hdrop
  have htake : List.take (0 + 1)
        (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).boundary
      = List.take (0 + 1)
        ((MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
            S.boundary.length).pullbackAlong (s'.obj s'.length)
          (Dt.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
            S.boundary.length).structMap) Dt.lastMap).boundary := by
    have t : [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        = [(MaxContactReduction.strictTransformAtLength s H).comap Dt.lastMap] := congrArg (fun Z => [Z]) hft1
    rw [e1, e2, e3]
    exact t
  have hjU : 0 < (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
      S.boundary.length).boundary.length := by
    rw [e2]
    simp
  have hjU' : 0 < (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
      [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).boundary.length := by
    rw [e3]
    simp
  have hOU := LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hftS
    [MaxContactReduction.strictTransformAtLength s H] S.boundary.length hVU
  have hDU := LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hm hO s hftS
    [MaxContactReduction.strictTransformAtLength s H] S.boundary.length hVU
  have hOU' := LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' hm hO' s'
    hftT [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
    (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length hVU'
  have hpb := NontrivialBoundary.pullbackAlong_derivedTriple_eq S q s s' Dt hstar hV hV' hftS hftT hsm
    [MaxContactReduction.strictTransformAtLength s H] S.boundary.length
    (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length
  have hEb : List.append
        (List.map (fun Z : (s.obj s.length).IdealSheafData => Z.comap Dt.lastMap)
          [MaxContactReduction.strictTransformAtLength s H])
        (List.drop (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length (s'.boundary s'.length))
      = (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).boundary :=
    (congrArg (fun L => List.append L
      (List.drop (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length (s'.boundary s'.length)))
      hlist).trans e3.symm
  have hEqLast :
      ((MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
          S.boundary.length).pullbackAlong (s'.obj s'.length)
        (Dt.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
          S.boundary.length).structMap) Dt.lastMap).withBoundary
        (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).boundary
      = MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length :=
    ((congrArg (fun L =>
        ((MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
            S.boundary.length).pullbackAlong (s'.obj s'.length)
          (Dt.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
            S.boundary.length).structMap) Dt.lastMap).withBoundary L) hEb).symm.trans hpb).trans
      (congrArg (fun E => MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT E
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) hlist)
  have hVtr : ∀ W : MarkedIdealWithBoundary.{u},
      W = MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length → W.IsAdmissible := by
    intro W hW
    subst hW
    exact hVU'
  have hPtr : ∀ W : MarkedIdealWithBoundary.{u},
      W = MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length → P W.krullDimSucc := by
    intro W hW
    subst hW
    exact hPU'
  have hOtr : ∀ W : MarkedIdealWithBoundary.{u},
      W = MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length → W.IsOrderBoundedByMult := by
    intro W hW
    subst hW
    exact hOU'
  have hjtr : ∀ W : MarkedIdealWithBoundary.{u},
      W = MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length → 0 < W.boundary.length := by
    intro W hW
    subst hW
    exact hjU'
  have hDtr : ∀ W : MarkedIdealWithBoundary.{u},
      W = MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length →
      ∀ hft : LocallyOfFiniteType W.structMap, W.IsBalanced hft := by
    intro W hW hft
    subst hW
    exact LowerDimReductionPullback.isBalanced_derivedTriple hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' hm hO' s' hftT
      [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length hVU'
  have inner0 := @IsBoundaryDivisorReduction.smooth_pullback P 0 (A 0) Bl hspec
    (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H] S.boundary.length)
    hVU hPU hOU hDU hjU (s'.obj s'.length)
    (Dt.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
      S.boundary.length).structMap) Dt.lastMap (SequenceOfBlowupsPullback.smooth_lastMap Dt) rfl
    (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
      [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).boundary
    hbe htake (hVtr _ hEqLast) (hPtr _ hEqLast) (hOtr _ hEqLast) (hDtr _ hEqLast _)
    (hjtr _ hEqLast)
  have hp : Dt.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS
        [MaxContactReduction.strictTransformAtLength s H] S.boundary.length).structMap
      = (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).structMap :=
    (congrArg (fun mm => Dt.lastMap ≫ mm)
        (MaxContactCoverData.derivedTriple_structureMorphism S s hftS
          [MaxContactReduction.strictTransformAtLength s H] S.boundary.length)).trans
      ((NontrivialBoundary.lastMap_comp_structureMorphism S q s s' Dt).trans
        (MaxContactCoverData.derivedTriple_structureMorphism (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).symm)
  have hI : (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
        S.boundary.length).ideal.comap Dt.lastMap
      = (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).ideal :=
    (congrArg (fun J => J.comap Dt.lastMap)
        (LowerDimReductionPullback.ideal_derivedTriple S s hftS
          [MaxContactReduction.strictTransformAtLength s H] S.boundary.length)).trans
      ((NontrivialBoundary.tunedIdealAtLength_comap_lastMap S q s s' Dt hstar hV hV' hftS hftT hsm).trans
        (LowerDimReductionPullback.ideal_derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).symm)
  have hm2 : (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
        S.boundary.length).mult
      = (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).mult :=
    (MaxContactCoverData.derivedTriple_mult S s hftS
        [MaxContactReduction.strictTransformAtLength s H] S.boundary.length).trans
      (MaxContactCoverData.derivedTriple_mult (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).symm
  have inner : IsPullbackBlowupSequence Dt.lastMap
      (A 0 (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length)).toSequenceOfBlowups
      (A 0 (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
          S.boundary.length)).toSequenceOfBlowups :=
    isPullbackBlowupSequence_congr (A 0) _ _ _ _ Dt.lastMap _ _ _ _ _ _ _ _ hp hI hm2 rfl inner0
  have hjlist : 0 < ([MaxContactReduction.strictTransformAtLength s H] ++
      (s.boundary s.length).drop S.boundary.length).length := by simp
  have hjlist' : 0 < ([MaxContactReduction.strictTransformAtLength s' (H.comap q)] ++
      (s'.boundary s'.length).drop (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).length := by simp
  obtain ⟨hmk, heq, -⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A Bl 0 hspec
    (fun S₀ _ i => A i S₀) (fun _ _ _ => rfl) S hV hm hO s
    [MaxContactReduction.strictTransformAtLength s H] S.boundary.length hftS hdimU hPU hVU hjlist
    (BoundarySeparationBaseChange.orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated S s S.boundary.length hsep)
  obtain ⟨hmk', heq', -⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A Bl 0 hspec
    (fun S₀ _ i => A i S₀) (fun _ _ _ => rfl) (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' hm hO' s'
    [MaxContactReduction.strictTransformAtLength s' (H.comap q)] (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length
    hftT hdimU' hPU' hVU' hjlist'
    (BoundarySeparationBaseChange.orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s'
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length hsep')
  rw [heq, heq']
  exact isPullbackBlowupSequence_append_of_two_fields q s _ s' _ hinv Dt
    (inner.nonempty_sequenceOfBlowupsPullback.some.toBlowupDataOfSeq)

end StrictTransformComparison


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderReductionFieldBaseChange
section

open CategoryTheory.Limits

section

namespace OrderReductionFieldBaseChange

def dropTrivialBoundaryBaseFieldHom (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] (f : T.base →+* L) :
    (MaxContactReduction.dropTrivialBoundary T).base →+* L := f

def coverBaseFieldHom (A : MarkedIdealWithBoundary.{u}) (hv : A.IsAdmissible) (L : Type u) [Field L]
    (f : A.base →+* L) : (MaxContactCoverData.coverTriple A hv).base →+* L := f

theorem coverTriple_structureMorphism_eq (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (MaxContactCoverData.coverTriple T hv).structMap = MaxContactCoverData.coverMap T hv ≫ T.structMap :=
  MaxContactCoverData.coverTriple_structureMorphism T hv

section
variable (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] (f : T.base →+* L)

theorem surjective_baseChange_fst :
    AlgebraicGeometry.Surjective (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
  MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective)
    (CategoryTheory.IsPullback.of_hasPullback T.structMap (specMapOfFieldHom T.base L f)).flip
    (FunctorialResolution.EmbeddedResolution.instSurjectiveSpecMapOfFieldHom T.base L f)

theorem orderAtLeastLocus_baseChange_eq_empty (hord : ∀ y : ↥(T.baseChange L f).scheme,
      orderAt (T.baseChange L f).ideal y
        = orderAt T.ideal ((pullback.fst T.structMap (specMapOfFieldHom T.base L f)) y))
    (hemp : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)) :
    orderAtLeastLocus (T.baseChange L f).ideal T.mult = (∅ : Set ↥(T.baseChange L f).scheme) := by
  apply Set.subset_empty_iff.mp
  intro y hy
  have h1 := (mem_orderAtLeastLocus_iff (T.baseChange L f).ideal T.mult y).1 hy
  rw [hord y] at h1
  have h2 : (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) y ∈ orderAtLeastLocus T.ideal T.mult :=
    (mem_orderAtLeastLocus_iff T.ideal T.mult _).2 h1
  rw [hemp] at h2
  simp at h2


end

def ValidBaseChange : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] [CharZero L] (f : T.base →+* L),
    T.IsAdmissible → (T.baseChange L f).IsAdmissible

def OrderAtBaseChangeEq : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] [CharZero L] (f : T.base →+* L),
    T.IsAdmissible → ∀ y : ↥(T.baseChange L f).scheme,
      orderAt (T.baseChange L f).ideal y
        = orderAt T.ideal ((pullback.fst T.structMap (specMapOfFieldHom T.base L f)) y)

def MaxContactHypersurfaceBaseChange : Prop :=
  ∀ (S : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] [CharZero L] (f : S.base →+* L),
    S.IsAdmissible → (S.baseChange L f).IsAdmissible →
    ∀ H : S.scheme.IdealSheafData,
      (∀ [LocallyOfFiniteType S.structMap],
        IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H) →
      InStrictNormalCrossingPosition S.structMap [H] →
      ((∀ [LocallyOfFiniteType (S.baseChange L f).structMap],
          IsMaxContactHypersurface (S.baseChange L f).base (S.baseChange L f).structMap
            (S.baseChange L f).ideal (S.baseChange L f).mult
            (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f)))) ∧
        InStrictNormalCrossingPosition (S.baseChange L f).structMap
          [H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))])

private theorem comp_assoc_eq_of_eq_comp_consolidated479 {X Y Z W V : Scheme.{u}}
    (p : X ⟶ Y) (q : Y ⟶ W) (b : Y ⟶ Z) (c : Z ⟶ W) (r : X ⟶ V) (s : V ⟶ W)
    (hq : q = b ≫ c) (h : p ≫ q = r ≫ s) :
    (p ≫ b) ≫ c = r ≫ s := by
  rw [Category.assoc, ← hq]
  exact h

theorem coverBaseChangeMap_condition (A : MarkedIdealWithBoundary.{u}) (hv : A.IsAdmissible) (L : Type u) [Field L]
    (f : A.base →+* L) :
    (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
          (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))
        ≫ MaxContactCoverData.coverMap A hv) ≫ A.structMap
      = pullback.snd (MaxContactCoverData.coverTriple A hv).structMap
          (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))
        ≫ specMapOfFieldHom A.base L f :=
  comp_assoc_eq_of_eq_comp_consolidated479
    (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
      (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f)))
    (MaxContactCoverData.coverTriple A hv).structMap
    (MaxContactCoverData.coverMap A hv)
    A.structMap
    (pullback.snd (MaxContactCoverData.coverTriple A hv).structMap
      (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f)))
    (specMapOfFieldHom A.base L f)
    (coverTriple_structureMorphism_eq A hv)
    pullback.condition

def coverBaseChangeMap (A : MarkedIdealWithBoundary.{u}) (hv : A.IsAdmissible) (L : Type u) [Field L]
    (f : A.base →+* L) :
    ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).scheme ⟶
      (A.baseChange L f).scheme :=
  pullback.lift
    (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
        (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))
      ≫ MaxContactCoverData.coverMap A hv)
    (pullback.snd (MaxContactCoverData.coverTriple A hv).structMap
      (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f)))
    (coverBaseChangeMap_condition A hv L f)

abbrev coverBaseChangeFiber (A : MarkedIdealWithBoundary.{u}) (hv : A.IsAdmissible) (L : Type u) [Field L]
    (f : A.base →+* L) (hv' : (A.baseChange L f).IsAdmissible) : Scheme.{u} :=
  pullback (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)

section
variable (p : Prop) (i : Decidable p)

private theorem decide_eq_true_iff_self_consolidated479 :
    (@decide p i = true) ↔ p := by
  cases i with
  | isTrue h => exact ⟨fun _ => h, fun _ => rfl⟩
  | isFalse h => exact ⟨fun hb => Bool.noConfusion hb, fun hp => absurd hp h⟩

private theorem not_decide_eq_true_iff_not_consolidated479 :
    ((!(@decide p i)) = true) ↔ ¬ p := by
  cases i with
  | isTrue h => exact ⟨fun hb => Bool.noConfusion hb, fun hn => absurd h hn⟩
  | isFalse h => exact ⟨fun _ => h, fun _ => rfl⟩


end

private theorem nontrivialPart_eq_filter_consolidated479 {X : Scheme.{u}}
    {q : X.IdealSheafData → Bool} (hq : ∀ D : X.IdealSheafData, q D = true ↔ D ≠ ⊤)
    (E : List X.IdealSheafData) :
    MarkedIdealWithBoundary.nontrivialPart E = List.filter q E := by
  unfold MarkedIdealWithBoundary.nontrivialPart
  refine congrArg (fun r => List.filter r E) (funext fun D => ?_)
  refine Bool.eq_iff_iff.mpr ?_
  rw [hq D]
  exact not_decide_eq_true_iff_not_consolidated479 _ _

section
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

private theorem filter_map_comap_consolidated479 (p : Y.IdealSheafData → Bool) (q : X.IdealSheafData → Bool)
    (hpq : ∀ D : Y.IdealSheafData, q (D.comap g) = p D) (E : List Y.IdealSheafData) :
    List.filter q (List.map (fun D => D.comap g) E)
      = List.map (fun D => D.comap g) (List.filter p E) := by
  induction E with
  | nil => simp
  | cons D E ih =>
      cases hD : p D
      · simp [hpq D, hD, ih]
      · simp [hpq D, hD, ih]

private theorem filter_eq_map_filter_of_nontrivialPart_eq_consolidated479 [AlgebraicGeometry.Surjective g]
    {p : Y.IdealSheafData → Bool} {q : X.IdealSheafData → Bool}
    {E : List Y.IdealSheafData} {E' : List X.IdealSheafData}
    (hp : ∀ D : Y.IdealSheafData, p D = true ↔ D ≠ ⊤)
    (hq : ∀ D : X.IdealSheafData, q D = true ↔ D ≠ ⊤)
    (hEE : MarkedIdealWithBoundary.nontrivialPart (List.map (fun D => D.comap g) E)
      = MarkedIdealWithBoundary.nontrivialPart E') :
    List.filter q E' = List.map (fun D => D.comap g) (List.filter p E) := by
  have hpq : ∀ D : Y.IdealSheafData, q (D.comap g) = p D := by
    intro D
    refine Bool.eq_iff_iff.mpr ?_
    rw [hq, hp]
    exact comap_ne_top_iff_of_surjective g D
  have h1 : List.filter q (List.map (fun D => D.comap g) E) = List.filter q E' := by
    rw [← nontrivialPart_eq_filter_consolidated479 hq (List.map (fun D => D.comap g) E),
      ← nontrivialPart_eq_filter_consolidated479 hq E']
    exact hEE
  rw [← h1]
  exact filter_map_comap_consolidated479 g p q hpq E


end

theorem dropTrivialBoundary_withBoundary_baseChange (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L]
    (f : T.base →+* L) (E' : List (T.baseChange L f).scheme.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E') :
    MaxContactReduction.dropTrivialBoundary ((T.baseChange L f).withBoundary E')
      = (MaxContactReduction.dropTrivialBoundary T).baseChange L (dropTrivialBoundaryBaseFieldHom T L f) := by
  have hsurj : AlgebraicGeometry.Surjective
      (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    surjective_baseChange_fst T L f
  have hb : (MaxContactReduction.dropTrivialBoundary ((T.baseChange L f).withBoundary E')).boundary
      = List.map (fun D => D.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f)))
          (MaxContactReduction.dropTrivialBoundary T).boundary := by
    rw [MaxContactReduction.dropTrivialBoundary_boundary, MaxContactReduction.dropTrivialBoundary_boundary,
      MarkedIdealWithBoundary.withBoundary_boundary]
    refine filter_eq_map_filter_of_nontrivialPart_eq_consolidated479
      (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) ?_ ?_ ?_
    · intro _
      exact decide_eq_true_iff_self_consolidated479 _ _
    · intro _
      exact decide_eq_true_iff_self_consolidated479 _ _
    · have h := (MarkedIdealWithBoundary.sameNontrivialBoundary_iff ((T.baseChange L f).boundary) E').mp hE
      rw [MarkedIdealWithBoundary.baseChange_boundary] at h
      exact h
  exact congrArg (fun E : List (T.baseChange L f).scheme.IdealSheafData =>
    (T.baseChange L f).withBoundary E) hb

section
variable {Q S Y X : Scheme.{u}} (q : Q ⟶ S) (c : S ⟶ Y) (p : Y ⟶ X)

private theorem comap_comap_comap_consolidated479 (I : X.IdealSheafData) : ((I.comap p).comap c).comap q = I.comap (q ≫ c ≫ p) := by
  simp [Scheme.IdealSheafData.comap_comp]

private theorem map_comap_comap_comap_consolidated479 (E : List X.IdealSheafData) :
    List.map (fun D => D.comap q)
        (List.map (fun D => D.comap c) (List.map (fun D => D.comap p) E))
      = List.map (fun D => D.comap (q ≫ c ≫ p)) E := by
  induction E with
  | nil => rfl
  | cons D Es ih => simp only [List.map_cons, comap_comap_comap_consolidated479, ih]


end

section
variable {Q S₁ S₂ Y₁ Y₂ X : Scheme.{u}} (q₁ : Q ⟶ S₁) (q₂ : Q ⟶ S₂) (c₁ : S₁ ⟶ Y₁) (p₁ : Y₁ ⟶ X) (c₂ : S₂ ⟶ Y₂) (p₂ : Y₂ ⟶ X)

private theorem comap_eq_comap_of_comp_eq_consolidated479 (I : X.IdealSheafData) (I₁ : S₁.IdealSheafData) (I₂ : S₂.IdealSheafData)
    (h₁ : I₁ = (I.comap p₁).comap c₁) (h₂ : I₂ = (I.comap p₂).comap c₂)
    (hk : q₁ ≫ c₁ ≫ p₁ = q₂ ≫ c₂ ≫ p₂) :
    I₁.comap q₁ = I₂.comap q₂ := by
  subst h₁
  subst h₂
  rw [comap_comap_comap_consolidated479, comap_comap_comap_consolidated479, hk]

private theorem map_comap_eq_map_comap_of_comp_eq_consolidated479 (E : List X.IdealSheafData) (E₁ : List S₁.IdealSheafData) (E₂ : List S₂.IdealSheafData)
    (h₁ : E₁ = List.map (fun D => D.comap c₁) (List.map (fun D => D.comap p₁) E))
    (h₂ : E₂ = List.map (fun D => D.comap c₂) (List.map (fun D => D.comap p₂) E))
    (hk : q₁ ≫ c₁ ≫ p₁ = q₂ ≫ c₂ ≫ p₂) :
    List.map (fun D => D.comap q₁) E₁ = List.map (fun D => D.comap q₂) E₂ := by
  subst h₁
  subst h₂
  rw [map_comap_comap_comap_consolidated479, map_comap_comap_comap_consolidated479, hk]


end

private theorem comp_structureMorphism_eq_of_comp_eq_consolidated479 {Q S₁ S₂ Y W : Scheme.{u}}
    (q₁ : Q ⟶ S₁) (q₂ : Q ⟶ S₂) (c₁ : S₁ ⟶ Y) (c₂ : S₂ ⟶ Y) (sY : Y ⟶ W)
    (s₁ : S₁ ⟶ W) (s₂ : S₂ ⟶ W)
    (h₁ : s₁ = c₁ ≫ sY) (h₂ : c₂ ≫ sY = s₂) (hpc : q₁ ≫ c₁ = q₂ ≫ c₂) :
    q₁ ≫ s₁ = q₂ ≫ s₂ := by
  subst h₁
  subst h₂
  rw [← Category.assoc, hpc, Category.assoc]

private theorem comp_comp_eq_comp_comp_consolidated479 {Q S₁ S₂ Y₁ Y₂ X : Scheme.{u}}
    (q₁ : Q ⟶ S₁) (q₂ : Q ⟶ S₂) (c₁ : S₁ ⟶ Y₁) (p₁ : Y₁ ⟶ X) (cc : S₂ ⟶ Y₁)
    (c₂ : S₂ ⟶ Y₂) (p₂ : Y₂ ⟶ X)
    (hpc : q₁ ≫ c₁ = q₂ ≫ cc) (hcf : cc ≫ p₁ = c₂ ≫ p₂) :
    q₁ ≫ c₁ ≫ p₁ = q₂ ≫ c₂ ≫ p₂ := by
  rw [← Category.assoc, hpc, Category.assoc, hcf]

private theorem markedIdealWithBoundary_mk_congr_consolidated479 (k : Type u) [Field k] (Y : Scheme.{u})
    (q q' : Y ⟶ Spec (CommRingCat.of k)) (I I' : Y.IdealSheafData) (m : ℕ)
    (E E' : List Y.IdealSheafData) (hq : q = q') (hI : I = I') (hE : E = E') :
    MarkedIdealWithBoundary.mk k Y q I m E = MarkedIdealWithBoundary.mk k Y q' I' m E' := by
  subst hq
  subst hI
  subst hE
  rfl

theorem pullbackAlong_coverBaseChangeFiber_eq (hderiv : DerivIdealSheafIterateCommBaseChange.{u})
    (A : MarkedIdealWithBoundary.{u}) (hv : A.IsAdmissible) (L : Type u) [Field L] [CharZero L]
    (f : A.base →+* L) (hv' : (A.baseChange L f).IsAdmissible) :
    (MaxContactCoverData.coverTriple (A.baseChange L f) hv').pullbackAlong
        (coverBaseChangeFiber A hv L f hv')
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)
          ≫ (MaxContactCoverData.coverTriple (A.baseChange L f) hv').structMap)
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f))
      = ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).pullbackAlong
        (coverBaseChangeFiber A hv L f hv')
        (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)
          ≫ ((MaxContactCoverData.coverTriple A hv).baseChange L
              (coverBaseFieldHom A hv L f)).structMap)
        (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f)) := by
  have hcf : coverBaseChangeMap A hv L f ≫ pullback.fst A.structMap (specMapOfFieldHom A.base L f)
      = pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
          (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))
        ≫ MaxContactCoverData.coverMap A hv := by
    unfold coverBaseChangeMap
    exact pullback.lift_fst _ _ _
  have hcs : coverBaseChangeMap A hv L f ≫ (A.baseChange L f).structMap
      = ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).structMap := by
    simp only [MarkedIdealWithBoundary.baseChange_structureMorphism]
    unfold coverBaseChangeMap
    exact pullback.lift_snd _ _ _
  have hT : MaxContactCoverData.balancedTunedIdeal (A.baseChange L f) hv'
      = (MaxContactCoverData.balancedTunedIdeal A hv).comap
        (pullback.fst A.structMap (specMapOfFieldHom A.base L f)) := by
    have : CharZero A.base := hv.charZero
    have : Smooth A.structMap := hv.smooth
    have : LocallyOfFiniteType A.structMap := hv.locallyOfFiniteType
    have : Smooth (pullback.snd A.structMap (specMapOfFieldHom A.base L f)) :=
      hv'.smooth
    have : LocallyOfFiniteType
        (pullback.snd A.structMap (specMapOfFieldHom A.base L f)) := hv'.locallyOfFiniteType
    exact balancedTunedSheaf_comap_of_isPullback hderiv A.base L f A.structMap
      (pullback.snd A.structMap (specMapOfFieldHom A.base L f))
      (pullback.fst A.structMap (specMapOfFieldHom A.base L f))
      (IsPullback.of_hasPullback A.structMap (specMapOfFieldHom A.base L f)) A.ideal A.mult
  have hkey :
      pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)
          ≫ MaxContactCoverData.coverMap (A.baseChange L f) hv'
            ≫ pullback.fst A.structMap (specMapOfFieldHom A.base L f)
        = pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)
          ≫ pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
              (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))
            ≫ MaxContactCoverData.coverMap A hv :=
    comp_comp_eq_comp_comp_consolidated479 _ _ _ _ (coverBaseChangeMap A hv L f) _ _ pullback.condition hcf
  have hI1 : (MaxContactCoverData.coverTriple (A.baseChange L f) hv').ideal
      = ((MaxContactCoverData.balancedTunedIdeal A hv).comap
          (pullback.fst A.structMap (specMapOfFieldHom A.base L f))).comap
        (MaxContactCoverData.coverMap (A.baseChange L f) hv') := by
    rw [MaxContactCoverData.coverTriple_ideal, hT]
    exact rfl
  have hI2 : ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).ideal
      = ((MaxContactCoverData.balancedTunedIdeal A hv).comap (MaxContactCoverData.coverMap A hv)).comap
        (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
          (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))) := by
    rw [MarkedIdealWithBoundary.baseChange_ideal, MaxContactCoverData.coverTriple_ideal]
    exact rfl
  have hE1 : (MaxContactCoverData.coverTriple (A.baseChange L f) hv').boundary
      = List.map (fun D => D.comap (MaxContactCoverData.coverMap (A.baseChange L f) hv'))
        (List.map (fun D => D.comap (pullback.fst A.structMap (specMapOfFieldHom A.base L f)))
          A.boundary) := by
    rw [MaxContactCoverData.coverTriple_boundary, MarkedIdealWithBoundary.baseChange_boundary]
    exact rfl
  have hE2 : ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).boundary
      = List.map (fun D => D.comap
            (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
              (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))))
        (List.map (fun D => D.comap (MaxContactCoverData.coverMap A hv)) A.boundary) := by
    rw [MarkedIdealWithBoundary.baseChange_boundary, MaxContactCoverData.coverTriple_boundary]
    exact rfl
  have hsm :
      pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)
          ≫ (MaxContactCoverData.coverTriple (A.baseChange L f) hv').structMap
        = pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)
          ≫ ((MaxContactCoverData.coverTriple A hv).baseChange L
              (coverBaseFieldHom A hv L f)).structMap :=
    comp_structureMorphism_eq_of_comp_eq_consolidated479 _ _ _ _ _ _ _
      (MaxContactCoverData.coverTriple_structureMorphism (A.baseChange L f) hv') hcs pullback.condition
  have hide :
      (MaxContactCoverData.coverTriple (A.baseChange L f) hv').ideal.comap
          (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f))
        = ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).ideal.comap
          (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)) :=
    comap_eq_comap_of_comp_eq_consolidated479 _ _ _ _ _ _ _ _ _ hI1 hI2 hkey
  have hbd :
      List.map
          (fun D => D.comap (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))
          (MaxContactCoverData.coverTriple (A.baseChange L f) hv').boundary
        = List.map
          (fun D => D.comap (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))
          ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).boundary :=
    map_comap_eq_map_comap_of_comp_eq_consolidated479 _ _ _ _ _ _ _ _ _ hE1 hE2 hkey
  exact markedIdealWithBoundary_mk_congr_consolidated479 L (coverBaseChangeFiber A hv L f hv') _ _ _ _
    (MaxContactCoverData.coverTriple (A.baseChange L f) hv').mult _ _ hsm hide hbd

section
variable {W X Y Z : Scheme.{u}} {fst : W ⟶ X} {snd : W ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z} (sq : CategoryTheory.IsPullback fst snd a b)
include sq

private theorem flat_fst_of_isPullback_consolidated479 (hb : Flat b) : Flat fst :=
  MorphismProperty.of_isPullback (P := @Flat) sq.flip hb

private theorem surjective_fst_of_isPullback_consolidated479 (hb : AlgebraicGeometry.Surjective b) : AlgebraicGeometry.Surjective fst :=
  MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) sq.flip hb

private theorem smooth_fst_of_isPullback_consolidated479 (hb : Smooth b) : Smooth fst :=
  MorphismProperty.of_isPullback (P := @Smooth) sq.flip hb


end

private theorem isPullback_congr_hom_consolidated479 {W X Y Z : Scheme.{u}} {fst : W ⟶ X} {snd snd' : W ⟶ Y}
    {a a' : X ⟶ Z} {b : Y ⟶ Z} (h : CategoryTheory.IsPullback fst snd a b)
    (hs : snd' = snd) (ha : a = a') : CategoryTheory.IsPullback fst snd' a' b := by
  subst hs
  subst ha
  exact h

private theorem isPullback_coverBaseChangeMap_consolidated479 (A : MarkedIdealWithBoundary.{u}) (hv : A.IsAdmissible)
    (L : Type u) [Field L] (f : A.base →+* L) :
    CategoryTheory.IsPullback
      (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
        (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f)))
      (coverBaseChangeMap A hv L f)
      (MaxContactCoverData.coverMap A hv)
      (pullback.fst A.structMap (specMapOfFieldHom A.base L f)) := by
  have hfst : coverBaseChangeMap A hv L f ≫ pullback.fst A.structMap (specMapOfFieldHom A.base L f)
      = pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
          (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))
        ≫ MaxContactCoverData.coverMap A hv := pullback.lift_fst _ _ _
  have hsnd : coverBaseChangeMap A hv L f ≫ pullback.snd A.structMap (specMapOfFieldHom A.base L f)
      = pullback.snd (MaxContactCoverData.coverTriple A hv).structMap
          (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f)) :=
    pullback.lift_snd _ _ _
  refine CategoryTheory.IsPullback.of_bot ?_ hfst.symm
    (CategoryTheory.IsPullback.of_hasPullback A.structMap (specMapOfFieldHom A.base L f))
  exact isPullback_congr_hom_consolidated479
    (CategoryTheory.IsPullback.of_hasPullback (MaxContactCoverData.coverTriple A hv).structMap
      (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f)))
    hsnd (coverTriple_structureMorphism_eq A hv)

private theorem isAdmissible_withBoundary_singleton_consolidated479 (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (H : S.scheme.IdealSheafData) (hsnc : InStrictNormalCrossingPosition S.structMap [H]) :
    (S.withBoundary [H]).IsAdmissible :=
  ⟨hV.charZero, hV.locallyOfFiniteType, hV.nonzeroOnComponents, hV.one_le_mult,
    hV.quasiCompact, hV.smooth, hsnc⟩

private theorem isStrictPullback_descend_of_flat_surjective_cover_consolidated479
    {XA XB XC XC' XCb XQ : Scheme.{u}}
    (hh : XB ⟶ XA) (g : XC ⟶ XA) (g' : XC' ⟶ XB) (p : XCb ⟶ XB) (pA : XCb ⟶ XC)
    (q₁ : XQ ⟶ XC') (q₂ : XQ ⟶ XCb)
    (hfh : Flat hh) (hfq : Flat q₁)
    (hfg' : Flat g')
    (hsq : AlgebraicGeometry.Surjective q₁) (hsg' : AlgebraicGeometry.Surjective g')
    (hsq1 : q₁ ≫ g' = q₂ ≫ p) (hsq2 : p ≫ hh = pA ≫ g)
    (u : SequenceOfBlowups XQ) (sB : SequenceOfBlowups XC') (sCb : SequenceOfBlowups XCb) (sA : SequenceOfBlowups XC)
    (dA : SequenceOfBlowups XA) (dB : SequenceOfBlowups XB)
    (hX : IsStrictPullbackBlowupSeq q₁ u sB) (hY : IsStrictPullbackBlowupSeq q₂ u sCb)
    (hZ : IsStrictPullbackBlowupSeq pA sCb sA)
    (hdA : IsStrictPullbackBlowupSeq g sA dA) (hdB : IsStrictPullbackBlowupSeq g' sB dB) :
    IsStrictPullbackBlowupSeq hh dB dA := by
  have := hfh
  have := hfq
  have := hfg'
  have := hsq
  have := hsg'
  have hfc : Flat (q₁ ≫ g') := inferInstance
  have hsc : AlgebraicGeometry.Surjective (q₁ ≫ g') := inferInstance
  have M1 : IsStrictPullbackBlowupSeq (q₁ ≫ g') u dB := hX.comp hdB
  have M2 : IsStrictPullbackBlowupSeq (q₂ ≫ (pA ≫ g)) u dA := hY.comp (hZ.comp hdA)
  have hcomp : (q₁ ≫ g') ≫ hh = q₂ ≫ (pA ≫ g) := by
    rw [hsq1, Category.assoc, hsq2]
  have M2' : IsStrictPullbackBlowupSeq ((q₁ ≫ g') ≫ hh) u dA := M2.congr_hom hcomp.symm
  have M3 : IsStrictPullbackBlowupSeq (q₁ ≫ g') u (dA.baseChange hh) := M2'.baseChange_of_comp
  have heqv : dB.Isomorphic (dA.baseChange hh) := M1.isomorphic_of_isomorphic M3 (SequenceOfBlowups.isomorphic_refl u)
  exact (isStrictPullbackSequenceOfBlowups_baseChange dA hh).of_isomorphic_pullback heqv.symm

private theorem isStrictPullbackBlowupSeq_coverTriple_baseChange_consolidated479
    (hderiv : DerivIdealSheafIterateCommBaseChange.{u}) (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u})
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (Fam : ℕ → PrincipalizationAssignment.{u}) (Bp : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (Fam j) Bp)
    (hinherit : IsBaseChangeInherited.{u} P)
    (hbcV : ValidBaseChange.{u}) (hbcO : OrderAtBaseChangeEq.{u}) (hbcA : MaxContactHypersurfaceBaseChange.{u})
    (A : MarkedIdealWithBoundary.{u}) (hv : A.IsAdmissible) (L : Type u) [Field L] [CharZero L] (f : A.base →+* L)
    (hflat : Flat (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
      (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))))
    (hHyp : MaxContactFunctoriality.OrderReductionHypotheses P A) (hHyp' : MaxContactFunctoriality.OrderReductionHypotheses P (A.baseChange L f))
    (hdimChart : ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).krullDimSucc
      ≤ (A.baseChange L f).krullDimSucc) :
    IsStrictPullbackBlowupSeq
      (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
        (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f)))
      (MaxContactReduction.reduceAlongHypersurface hinv (A.baseChange L f) (fun S' _ i => Fam i S')
        ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f))
        ((MaxContactCoverData.coverMaxContactIdeal A hv).comap
          (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
            (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L
              (coverBaseFieldHom A hv L f))))).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactCoverData.coverMarkedBlowupData A hv hinv (MaxContactFunctoriality.lowerDimensionalFamily Fam A)).toSequenceOfBlowups := by
  have := hflat
  have hVC : (MaxContactCoverData.coverTriple A hv).IsAdmissible :=
    BoundarySeparationByMaxContact.isAdmissible_coverTriple hstar P A hHyp
  have hVCb : ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).IsAdmissible :=
    hbcV (MaxContactCoverData.coverTriple A hv) L (coverBaseFieldHom A hv L f) hVC
  have hadm := hbcA (MaxContactCoverData.coverTriple A hv) L (coverBaseFieldHom A hv L f) hVC hVCb
    (MaxContactCoverData.coverMaxContactIdeal A hv)
    (BoundarySeparationByMaxContact.isMaxContactHypersurface_coverMaxContactIdeal hstar P A hHyp)
    (BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P A hHyp)
  have hO' : ∀ x : ↥((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).scheme,
      orderAt ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).ideal x
        ≤ ((((MaxContactCoverData.coverTriple A hv).baseChange L
            (coverBaseFieldHom A hv L f)).mult : ℕ) : ℕ∞) := by
    intro x
    rw [hbcO (MaxContactCoverData.coverTriple A hv) L (coverBaseFieldHom A hv L f) hVC x]
    exact BoundarySeparationByMaxContact.orderAt_coverTriple_ideal_le_mult hstar P A hHyp _
  exact BoundaryLoopFieldBaseChange.isStrictPullbackBlowupSeq_reduceAlongHypersurface_baseChange hderiv hstar hinv P hmono Fam Bp hspec
    A (A.baseChange L f) hHyp.dim_prop hHyp'.dim_prop
    (MaxContactCoverData.coverTriple A hv) hVC
    (BoundarySeparationByMaxContact.orderAt_coverTriple_ideal_le_mult hstar P A hHyp)
    (MaxContactOpenCover.krullDimSucc_coverTriple_scheme_le_dim A hv) L (coverBaseFieldHom A hv L f) hVCb hO' hdimChart
    (MaxContactCoverData.coverMaxContactIdeal A hv)
    (BoundarySeparationByMaxContact.isMaxContactHypersurface_coverMaxContactIdeal hstar P A hHyp)
    (BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P A hHyp)
    hadm.1 hadm.2 hinherit

theorem isStrictPullbackBlowupSeq_baseChange_of_cover
    (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u}) (hin : OrderReduction.OrderReductionHypotheses.{u})
    (hMC : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u}) (hAdm : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u})
    (hderiv : DerivIdealSheafIterateCommBaseChange.{u})
    (hbcV : ValidBaseChange.{u}) (hbcO : OrderAtBaseChangeEq.{u}) (hbcA : MaxContactHypersurfaceBaseChange.{u})
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (Fam : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (Fam j) B)
    (hinherit : IsBaseChangeInherited.{u} P)
    (hcff : MaxContactFunctoriality.CoverFaithfullyFlat.{u} P)
    (A : MarkedIdealWithBoundary.{u}) (hv : A.IsAdmissible)
    (L : Type u) [Field L] [CharZero L] (f : A.base →+* L)
    [Flat (pullback.fst A.structMap (specMapOfFieldHom A.base L f))]
    (hv' : (A.baseChange L f).IsAdmissible)
    (hHyp : MaxContactFunctoriality.OrderReductionHypotheses P A)
    (hHyp' : MaxContactFunctoriality.OrderReductionHypotheses P (A.baseChange L f))
    (hdimChart :
      ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).krullDimSucc
        ≤ (A.baseChange L f).krullDimSucc)
    (hqc : QuasiCompact
      (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)
        ≫ ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).structMap))
    (hQdim : krullDimSucc (coverBaseChangeFiber A hv L f hv') ≤ (A.baseChange L f).krullDimSucc)
    (d : BlowupSequenceData A.scheme) (d' : BlowupSequenceData (A.baseChange L f).scheme)
    (hd : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap A hv)
      (MaxContactCoverData.coverMarkedBlowupData A hv hinv (MaxContactFunctoriality.lowerDimensionalFamily Fam A)).toSequenceOfBlowups d.toSequenceOfBlowups)
    (hd' : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap (A.baseChange L f) hv')
      (MaxContactCoverData.coverMarkedBlowupData (A.baseChange L f) hv' hinv
        (MaxContactFunctoriality.lowerDimensionalFamily Fam (A.baseChange L f))).toSequenceOfBlowups d'.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq (pullback.fst A.structMap (specMapOfFieldHom A.base L f)) d'.toSequenceOfBlowups d.toSequenceOfBlowups := by
  have hfA : Flat (pullback.fst A.structMap (specMapOfFieldHom A.base L f)) :=
    inferInstance
  have hVCA : (MaxContactCoverData.coverTriple A hv).IsAdmissible :=
    BoundarySeparationByMaxContact.isAdmissible_coverTriple hstar P A hHyp
  have hVC1 : (MaxContactCoverData.coverTriple (A.baseChange L f) hv').IsAdmissible :=
    BoundarySeparationByMaxContact.isAdmissible_coverTriple hstar P (A.baseChange L f) hHyp'
  have hVS2 : ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).IsAdmissible :=
    hbcV (MaxContactCoverData.coverTriple A hv) L (coverBaseFieldHom A hv L f) hVCA
  have hsqc := isPullback_coverBaseChangeMap_consolidated479 A hv L f
  have hfg : Flat (MaxContactCoverData.coverMap A hv) :=
    MaxContactCoverData.flat_coverMap_of_isAdmissible A hv
  have hsg : AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap A hv) := (hcff A hHyp).1
  have hsmg : Smooth (MaxContactCoverData.coverMap A hv) :=
    MaxContactCoverData.smooth_coverMap_of_isAdmissible A hv
  have hfg' : Flat (MaxContactCoverData.coverMap (A.baseChange L f) hv') :=
    MaxContactCoverData.flat_coverMap_of_isAdmissible (A.baseChange L f) hv'
  have hsg' : AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap (A.baseChange L f) hv') :=
    (hcff (A.baseChange L f) hHyp').1
  have hsmg' : Smooth (MaxContactCoverData.coverMap (A.baseChange L f) hv') :=
    MaxContactCoverData.smooth_coverMap_of_isAdmissible (A.baseChange L f) hv'
  have hfpA : Flat (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
      (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))) :=
    flat_fst_of_isPullback_consolidated479 hsqc hfA
  have hfp : Flat (coverBaseChangeMap A hv L f) :=
    flat_fst_of_isPullback_consolidated479 hsqc.flip hfg
  have hsp : AlgebraicGeometry.Surjective (coverBaseChangeMap A hv L f) :=
    surjective_fst_of_isPullback_consolidated479 hsqc.flip hsg
  have hsmp : Smooth (coverBaseChangeMap A hv L f) :=
    smooth_fst_of_isPullback_consolidated479 hsqc.flip hsmg
  have hbig : CategoryTheory.IsPullback
      (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
      (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
      (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f) :=
    CategoryTheory.IsPullback.of_hasPullback _ _
  have hfl1 := flat_fst_of_isPullback_consolidated479 hbig hfp
  have hsu1 := surjective_fst_of_isPullback_consolidated479 hbig hsp
  have hsm1 := smooth_fst_of_isPullback_consolidated479 hbig hsmp
  have hfl2 := flat_fst_of_isPullback_consolidated479 hbig.flip hfg'
  have hsu2 := surjective_fst_of_isPullback_consolidated479 hbig.flip hsg'
  have hsm2 := smooth_fst_of_isPullback_consolidated479 hbig.flip hsmg'
  have hT : LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
      = LowerDimReductionPullback.pullbackTriple ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f))
        (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f)) :=
    pullbackAlong_coverBaseChangeFiber_eq hderiv A hv L f hv'
  have hVQ2 : (LowerDimReductionPullback.pullbackTriple
      ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f))
      (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
        (coverBaseChangeMap A hv L f))).IsAdmissible :=
    @OrderReduction.OrderReductionHypotheses.valid_pullbackAlong hin
      ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)) hVS2
      (coverBaseChangeFiber A hv L f hv')
      (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)
        ≫ ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).structMap)
      (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
      hsm2 hqc rfl
  have hVQ1 : (LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
      (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
        (coverBaseChangeMap A hv L f))).IsAdmissible := by
    rw [hT]
    exact hVQ2
  have hVb : ((MaxContactCoverData.coverTriple (A.baseChange L f) hv').withBoundary
      [MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv']).IsAdmissible :=
    isAdmissible_withBoundary_singleton_consolidated479 (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
      hVC1 (MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv')
      (BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P (A.baseChange L f) hHyp')
  have hVQb := @OrderReduction.OrderReductionHypotheses.valid_pullbackAlong hin
    ((MaxContactCoverData.coverTriple (A.baseChange L f) hv').withBoundary
      [MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv']) hVb
    (coverBaseChangeFiber A hv L f hv')
    (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)
      ≫ (MaxContactCoverData.coverTriple (A.baseChange L f) hv').structMap)
    (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
    hsm1 hVQ1.quasiCompact rfl
  have hsncQ1 : InStrictNormalCrossingPosition
      (LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f))).structMap
      [(MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f))] := hVQb.snc
  have hloftQ1 : LocallyOfFiniteType
      (LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f))).structMap := hVQ1.locallyOfFiniteType
  have hadmQ1 : IsMaxContactHypersurface
      (LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f))).base
      (LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f))).structMap
      (LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f))).ideal
      (LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f))).mult
      ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f))) :=
    @hAdm (MaxContactCoverData.coverTriple (A.baseChange L f) hv').base inferInstance hVC1.charZero
      (MaxContactCoverData.coverTriple (A.baseChange L f) hv').scheme
      (MaxContactCoverData.coverTriple (A.baseChange L f) hv').structMap hVC1.smooth
      hVC1.locallyOfFiniteType (coverBaseChangeFiber A hv L f hv')
      (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
      hsm1 hVQ1.locallyOfFiniteType
      (MaxContactCoverData.coverTriple (A.baseChange L f) hv').ideal
      (MaxContactCoverData.coverTriple (A.baseChange L f) hv').mult hVC1.one_le_mult
      (MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv')
      (BoundarySeparationByMaxContact.isMaxContactHypersurface_coverMaxContactIdeal hstar P (A.baseChange L f) hHyp')
  have hadmQ2 := MaxContactFunctoriality.isMaxContactHypersurface_of_triple_eq hT.symm
    hVQ2.locallyOfFiniteType hVQ1.locallyOfFiniteType
    ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
      (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)))
    ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
      (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)))
    HEq.rfl hadmQ1
  have hsncQ2 := MaxContactFunctoriality.inStrictNormalCrossingPosition_of_triple_eq hT.symm
    [(MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
      (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))]
    [(MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
      (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))]
    HEq.rfl hsncQ1
  have hO2 : ∀ x : ↥((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).scheme,
      orderAt ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).ideal x
        ≤ ((((MaxContactCoverData.coverTriple A hv).baseChange L
            (coverBaseFieldHom A hv L f)).mult : ℕ) : ℕ∞) := by
    intro x
    rw [hbcO (MaxContactCoverData.coverTriple A hv) L (coverBaseFieldHom A hv L f) hVCA x]
    exact BoundarySeparationByMaxContact.orderAt_coverTriple_ideal_le_mult hstar P A hHyp _
  have hadmS2 := hbcA (MaxContactCoverData.coverTriple A hv) L (coverBaseFieldHom A hv L f) hVCA hVS2
    (MaxContactCoverData.coverMaxContactIdeal A hv)
    (BoundarySeparationByMaxContact.isMaxContactHypersurface_coverMaxContactIdeal hstar P A hHyp)
    (BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P A hHyp)
  have hX : IsStrictPullbackBlowupSeq
      (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
      (MaxContactReduction.reduceAlongHypersurface hinv (A.baseChange L f) (fun S' _ i => Fam i S')
        (LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
          (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))
        ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
          (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactCoverData.coverMarkedBlowupData (A.baseChange L f) hv' hinv
        (MaxContactFunctoriality.lowerDimensionalFamily Fam (A.baseChange L f))).toSequenceOfBlowups :=
    @BoundarySeparationBaseChange.isStrictPullbackBlowupSeq_reduceAlongHypersurface hstar hin hMC hAdm hinv P hmono Fam B hspec
      (A.baseChange L f) hHyp'.dim_prop
      (MaxContactCoverData.coverTriple (A.baseChange L f) hv') hVC1
      (BoundarySeparationByMaxContact.orderAt_coverTriple_ideal_le_mult hstar P (A.baseChange L f) hHyp')
      (MaxContactOpenCover.krullDimSucc_coverTriple_scheme_le_dim (A.baseChange L f) hv')
      (MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv')
      (BoundarySeparationByMaxContact.isMaxContactHypersurface_coverMaxContactIdeal hstar P (A.baseChange L f) hHyp')
      (BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P (A.baseChange L f) hHyp')
      (coverBaseChangeFiber A hv L f hv')
      (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
      hsm1 hfl1 hsu1 hVQ1 hQdim
      ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)))
      hadmQ1 hsncQ1
  have hY0 : IsStrictPullbackBlowupSeq
      (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
      (MaxContactReduction.reduceAlongHypersurface hinv (A.baseChange L f) (fun S' _ i => Fam i S')
        (LowerDimReductionPullback.pullbackTriple ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f))
          (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))
        ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
          (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv (A.baseChange L f) (fun S' _ i => Fam i S')
        ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f))
        ((MaxContactCoverData.coverMaxContactIdeal A hv).comap
          (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
            (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L
              (coverBaseFieldHom A hv L f))))).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
    @BoundarySeparationBaseChange.isStrictPullbackBlowupSeq_reduceAlongHypersurface hstar hin hMC hAdm hinv P hmono Fam B hspec
      (A.baseChange L f) hHyp'.dim_prop
      ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)) hVS2 hO2 hdimChart
      ((MaxContactCoverData.coverMaxContactIdeal A hv).comap
        (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
          (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))))
      hadmS2.1 hadmS2.2
      (coverBaseChangeFiber A hv L f hv')
      (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
      hsm2 hfl2 hsu2 hVQ2 hQdim
      ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)))
      hadmQ2 hsncQ2
  have hEqSeq : (MaxContactReduction.reduceAlongHypersurface hinv (A.baseChange L f) (fun S' _ i => Fam i S')
        (LowerDimReductionPullback.pullbackTriple ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f))
          (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))
        ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
          (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      = (MaxContactReduction.reduceAlongHypersurface hinv (A.baseChange L f) (fun S' _ i => Fam i S')
        (LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
          (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))
        ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
          (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
    eq_of_heq (MaxContactFunctoriality.reduceAlongHypersurface_toSequenceOfBlowups_heq hinv (A.baseChange L f)
      (fun S' _ i => Fam i S') hT.symm
      ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)))
      ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)))
      HEq.rfl)
  have hY := hY0.congr_sourceSeq hEqSeq
  have hZ := isStrictPullbackBlowupSeq_coverTriple_baseChange_consolidated479 hderiv hstar hinv P hmono Fam B hspec hinherit
    hbcV hbcO hbcA A hv L f hfpA hHyp hHyp' hdimChart
  exact isStrictPullback_descend_of_flat_surjective_cover_consolidated479 (pullback.fst A.structMap (specMapOfFieldHom A.base L f))
    (MaxContactCoverData.coverMap A hv) (MaxContactCoverData.coverMap (A.baseChange L f) hv')
    (coverBaseChangeMap A hv L f)
    (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
      (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f)))
    (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
    (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
    hfA hfl1 hfg' hsu1 hsg' pullback.condition hsqc.w.symm
    _ _ _ _ _ _ hX hY hZ hd hd'

private theorem isStrictPullback_of_eq_of_heq_consolidated479
    (hinv : ComapIsoInvariance.{u}) (Fam : ℕ → PrincipalizationAssignment.{u})
    {T₁ T₂ : MarkedIdealWithBoundary.{u}} (hT : T₁ = T₂)
    (hv₁ : T₁.IsAdmissible) (hv₂ : T₂.IsAdmissible) (d : BlowupSequenceData T₁.scheme)
    {Z : Scheme.{u}} (ψ : T₁.scheme ⟶ Z) (ψ' : T₂.scheme ⟶ Z) (hψ : HEq ψ ψ')
    (w : SequenceOfBlowups Z)
    (hcrit : ∀ e : BlowupSequenceData T₂.scheme,
      IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T₂ hv₂)
          (MaxContactCoverData.coverMarkedBlowupData T₂ hv₂ hinv
            (MaxContactFunctoriality.lowerDimensionalFamily Fam T₂)).toSequenceOfBlowups e.toSequenceOfBlowups →
        IsStrictPullbackBlowupSeq ψ' e.toSequenceOfBlowups w)
    (hd : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T₁ hv₁)
      (MaxContactCoverData.coverMarkedBlowupData T₁ hv₁ hinv
        (MaxContactFunctoriality.lowerDimensionalFamily Fam T₁)).toSequenceOfBlowups d.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq ψ d.toSequenceOfBlowups w := by
  subst hT
  have hψ2 : ψ = ψ' := eq_of_heq hψ
  subst hψ2
  exact hcrit d hd

theorem isStrictPullbackBlowupSeq_baseChange_withBoundary
    (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u}) (hin : OrderReduction.OrderReductionHypotheses.{u})
    (hMC : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u}) (hAdm : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u})
    (hderiv : DerivIdealSheafIterateCommBaseChange.{u})
    (hbcV : ValidBaseChange.{u}) (hbcO : OrderAtBaseChangeEq.{u}) (hbcA : MaxContactHypersurfaceBaseChange.{u})
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (Fam : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (Fam j) B)
    (hinherit : IsBaseChangeInherited.{u} P)
    (hsf : MaxContactFunctoriality.CoverSequenceProperties hinv P Fam)
    (hmd : MaxContactFunctoriality.MarkingDescends hinv P Fam)
    (hcff : MaxContactFunctoriality.CoverFaithfullyFlat.{u} P)
    (htv : MaxContactFunctoriality.DropTrivialBoundaryAdmissible.{u})
    (htm : MaxContactFunctoriality.MarkedOfMarkedDropTrivialBoundary.{u})
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : P T.krullDimSucc)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
    [Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f))]
    (E' : List (T.baseChange L f).scheme.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E')
    (hV' : ((T.baseChange L f).withBoundary E').IsAdmissible)
    (hP' : P ((T.baseChange L f).withBoundary E').krullDimSucc)
    (hdimChart :
      ((MaxContactCoverData.coverTriple (MaxContactReduction.dropTrivialBoundary T) (htv T hV)).baseChange L
          (coverBaseFieldHom (MaxContactReduction.dropTrivialBoundary T) (htv T hV) L (dropTrivialBoundaryBaseFieldHom T L f))).krullDimSucc
        ≤ (T.baseChange L f).krullDimSucc)
    (hqc : QuasiCompact
      (pullback.snd
          (MaxContactCoverData.coverMap ((MaxContactReduction.dropTrivialBoundary T).baseChange L (dropTrivialBoundaryBaseFieldHom T L f))
            (hbcV (MaxContactReduction.dropTrivialBoundary T) L (dropTrivialBoundaryBaseFieldHom T L f) (htv T hV)))
          (coverBaseChangeMap (MaxContactReduction.dropTrivialBoundary T) (htv T hV) L (dropTrivialBoundaryBaseFieldHom T L f))
        ≫ ((MaxContactCoverData.coverTriple (MaxContactReduction.dropTrivialBoundary T) (htv T hV)).baseChange L
            (coverBaseFieldHom (MaxContactReduction.dropTrivialBoundary T) (htv T hV) L (dropTrivialBoundaryBaseFieldHom T L f))).structMap))
    (hQdim : krullDimSucc
        (coverBaseChangeFiber (MaxContactReduction.dropTrivialBoundary T) (htv T hV) L (dropTrivialBoundaryBaseFieldHom T L f)
          (hbcV (MaxContactReduction.dropTrivialBoundary T) L (dropTrivialBoundaryBaseFieldHom T L f) (htv T hV)))
      ≤ (T.baseChange L f).krullDimSucc) :
    IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
      (MaxContactFunctoriality.maxContactPrincipalization hinv Fam ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups
      (MaxContactFunctoriality.maxContactPrincipalization hinv Fam T).toSequenceOfBlowups := by
  have hord : ∀ y : ↥(T.baseChange L f).scheme,
      orderAt (T.baseChange L f).ideal y
        = orderAt T.ideal ((pullback.fst T.structMap (specMapOfFieldHom T.base L f)) y) :=
    hbcO T L f hV
  have hord' : ∀ x : ↥((T.baseChange L f).withBoundary E').scheme,
      orderAt ((T.baseChange L f).withBoundary E').ideal x
        ≤ ((((T.baseChange L f).withBoundary E').mult : ℕ) : ℕ∞) := by
    intro x
    exact (hord x).le.trans (hO _)
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)
  · have h1 : (MaxContactFunctoriality.maxContactPrincipalization hinv Fam T).length = 0 :=
      MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P Fam T hV hP hO hemp
    have hemp' : orderAtLeastLocus ((T.baseChange L f).withBoundary E').ideal
        ((T.baseChange L f).withBoundary E').mult = ∅ :=
      orderAtLeastLocus_baseChange_eq_empty T L f hord hemp
    have h2 : (MaxContactFunctoriality.maxContactPrincipalization hinv Fam
        ((T.baseChange L f).withBoundary E')).length = 0 :=
      MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P Fam
        ((T.baseChange L f).withBoundary E') hV' hP' hord' hemp'
    exact IsStrictPullbackBlowupSeq.of_length_zero
      (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
      (MaxContactFunctoriality.maxContactPrincipalization hinv Fam ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups
      (MaxContactFunctoriality.maxContactPrincipalization hinv Fam T).toSequenceOfBlowups h2 h1
  · have hHypT : MaxContactFunctoriality.OrderReductionHypotheses P T :=
      ⟨hP, hO, Set.nonempty_iff_ne_empty.mpr hemp, hV⟩
    have hHypT' : MaxContactFunctoriality.OrderReductionHypotheses P ((T.baseChange L f).withBoundary E') := by
      have hsurjfst := surjective_baseChange_fst T L f
      refine ⟨hP', hord', ?_, hV'⟩
      by_contra hcon
      exact hemp (orderAtLeastLocus_eq_empty_of_comap_eq_empty
        (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) T.ideal T.mult
        (Set.not_nonempty_iff_eq_empty.mp hcon))
    obtain ⟨d, hd, hmain⟩ :=
      MaxContactFunctoriality.exists_isStrictPullback_cover_dropTrivialBoundary hsf hmd htv htm T hHypT
    obtain ⟨d', hd', hmain'⟩ :=
      MaxContactFunctoriality.exists_isStrictPullback_cover_dropTrivialBoundary hsf hmd htv htm
        ((T.baseChange L f).withBoundary E') hHypT'
    rw [hmain, hmain']
    have hT : MaxContactReduction.dropTrivialBoundary ((T.baseChange L f).withBoundary E')
        = (MaxContactReduction.dropTrivialBoundary T).baseChange L (dropTrivialBoundaryBaseFieldHom T L f) :=
      dropTrivialBoundary_withBoundary_baseChange T L f E' hE
    have hflat : Flat
        (pullback.fst (MaxContactReduction.dropTrivialBoundary T).structMap
          (specMapOfFieldHom (MaxContactReduction.dropTrivialBoundary T).base L (dropTrivialBoundaryBaseFieldHom T L f))) :=
      inferInstanceAs
        (Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f)))
    have hHypBC : MaxContactFunctoriality.OrderReductionHypotheses P
        ((MaxContactReduction.dropTrivialBoundary T).baseChange L (dropTrivialBoundaryBaseFieldHom T L f)) := by
      rw [← hT]
      exact hHypT'.of_dropTrivialBoundaryAdmissible htv
    refine isStrictPullback_of_eq_of_heq_consolidated479 hinv Fam hT ((hHypT'.of_dropTrivialBoundaryAdmissible htv).valid)
      (hbcV (MaxContactReduction.dropTrivialBoundary T) L (dropTrivialBoundaryBaseFieldHom T L f) (htv T hV)) d'
      (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
      (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) HEq.rfl d.toSequenceOfBlowups ?_ hd'
    intro e he
    exact isStrictPullbackBlowupSeq_baseChange_of_cover hstar hin hMC hAdm hderiv hbcV hbcO hbcA hinv P
      hmono Fam B hspec hinherit hcff (MaxContactReduction.dropTrivialBoundary T) (htv T hV) L (dropTrivialBoundaryBaseFieldHom T L f)
      (hbcV (MaxContactReduction.dropTrivialBoundary T) L (dropTrivialBoundaryBaseFieldHom T L f) (htv T hV))
      (hHypT.of_dropTrivialBoundaryAdmissible htv) hHypBC hdimChart hqc hQdim d e hd he

end OrderReductionFieldBaseChange


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.HypersurfaceReductionFunctoriality
section


section

namespace MaxContactFunctoriality

section
variable (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u})
include hstar

theorem isPullbackBlowupSequence_reduceAlongHypersurface_of_smooth
    (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (Bl : PrincipalizationAssignment.{u})
    (hspec : ∀ i : ℕ, IsBoundaryDivisorReduction P i (A i) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (H : S.scheme.IdealSheafData)
    (hH : ∀ [LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [Smooth q]
    (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hdim' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).krullDimSucc ≤ T.krullDimSucc)
    (hH' : ∀ [LocallyOfFiniteType (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap],
      IsMaxContactHypersurface (NontrivialBoundary.pullbackWithNontrivialBoundary S q).base
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult (H.comap q))
    (hH'snc : InStrictNormalCrossingPosition (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap [H.comap q]) :
    IsPullbackBlowupSequence q
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S₀ _ i => A i S₀)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q) (H.comap q)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S₀ _ i => A i S₀) S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have hcnt : NontrivialBoundary.survivingBoundaryCount S q S.boundary.length
      = (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length := NontrivialBoundary.survivingBoundaryCount_length_eq S q
  have Dt0 := NontrivialBoundary.separateBoundaryPullbackComparison P hmono A Bl hspec hshift hstar hinv T hPdimT S q hV hO
    hdimS hV' hdim' S.boundary.length le_rfl
  rw [hcnt] at Dt0
  have hftS : LocallyOfFiniteType
      ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length).proj
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length).length ≫ S.structMap) :=
    BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV _ _ le_rfl
  have hftT : LocallyOfFiniteType
      ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).proj
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).length
        ≫ (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap) :=
    BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' _ _
      le_rfl
  have hF := BoundarySeparationBaseChange.separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A Bl hspec T hPdimT S
    hV hO hdimS H hHsnc S.boundary.length le_rfl
  have hF' := BoundarySeparationBaseChange.separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A Bl hspec T hPdimT
    (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' (BoundarySeparationBaseChange.orderAt_pullbackTriple_le_mult S q hV hO) hdim' (H.comap q)
    hH'snc (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length le_rfl
  have hm : 1 ≤ S.mult := hV.one_le_mult
  have hO' : ∀ x : ↥(NontrivialBoundary.pullbackWithNontrivialBoundary S q).scheme,
      orderAt (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal x ≤ ((S.mult : ℕ) : ℕ∞) :=
    BoundarySeparationBaseChange.orderAt_pullbackTriple_le_mult S q hV hO
  have hdimU : (MaxContactCoverData.derivedTriple S
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) hftS
      [MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) H]
      S.boundary.length).krullDimSucc ≤ T.krullDimSucc :=
    hstar.derivedTriple_dim_le hV _ hftS _ _ hdimS
  have hPU : P (MaxContactCoverData.derivedTriple S
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) hftS
      [MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) H]
      S.boundary.length).krullDimSucc := hmono _ _ hdimU hPdimT
  have hsncU : InStrictNormalCrossingPosition
      ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length).proj
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length).length ≫ S.structMap)
      ([MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) H] ++
        List.drop S.boundary.length
          ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length).boundary
            (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length).length)) := by
    simpa [MaxContactReduction.strictTransformAtLength_eq] using
      inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar S hV hO H (@hH hV.locallyOfFiniteType)
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) hF.2.2 _ le_rfl
  have hVU := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar S hV
    (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) hftS
    [MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) H]
    S.boundary.length hsncU
  have hdimU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) hftT
      [MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) (H.comap q)]
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).krullDimSucc ≤ T.krullDimSucc :=
    hstar.derivedTriple_dim_le hV' _ hftT _ _ hdim'
  have hPU' : P (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) hftT
      [MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) (H.comap q)]
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).krullDimSucc := hmono _ _ hdimU' hPdimT
  have hsncU' : InStrictNormalCrossingPosition
      ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).proj
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).length
        ≫ (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap)
      ([MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) (H.comap q)] ++
        List.drop (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length
          ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
            (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).boundary
            (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
              (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).length)) := by
    simpa [MaxContactReduction.strictTransformAtLength_eq] using
      inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV'
        (BoundarySeparationBaseChange.orderAt_pullbackTriple_le_mult S q hV hO) (H.comap q) (@hH' hV'.locallyOfFiniteType)
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) hF'.2.2 _ le_rfl
  have hVU' := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV'
    (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) hftT
    [MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) (H.comap q)]
    (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length hsncU'
  have hsep : BoundarySeparationByMaxContact.BoundarySeparated S
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) S.boundary.length := hF.1
  have hsep' : BoundarySeparationByMaxContact.BoundarySeparated (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length)
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length := hF'.1
  simp only [MaxContactCoverData.reduceAlongHypersurface_eq_appendLowerDimReduction]
  exact StrictTransformComparison.isPullbackBlowupSequence_appendLowerDimReduction (P := P) (A := A) (Bl := Bl) (S := S) (q := q)
    (s := BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length)
    (s' := BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length)
    (Dt := Dt0) (hftS := hftS) (hftT := hftT) (hinv := hinv) (T := T) (hstar := hstar)
    (hspec := hspec 0) (H := H) (hV := hV) (hV' := hV') (hm := hm) (hO := hO) (hO' := hO')
    (hdimU := hdimU) (hPU := hPU) (hVU := hVU) (hdimU' := hdimU') (hPU' := hPU') (hVU' := hVU')
    (hsep := hsep) (hsep' := hsep')

theorem isPullbackBlowupSequence_reduceAlongHypersurface_lowerDimensionalFamily
    (_hin : _root_.FunctorialResolution.EmbeddedResolution.OrderReduction.OrderReductionHypotheses)
    (_hMC : _root_.FunctorialResolution.EmbeddedResolution.BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u})
    (_hAdm : _root_.FunctorialResolution.EmbeddedResolution.BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u})
    (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (Bl : PrincipalizationAssignment.{u})
    (hspec : ∀ i : ℕ, IsBoundaryDivisorReduction P i (A i) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (T T' : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc) (hPdimOther : P T'.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (_hBoundaryNeTop : ∀ D ∈ S.boundary, D ≠ ⊤)
    (H : S.scheme.IdealSheafData)
    (hH : ∀ [LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [Smooth q]
    (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hdim' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).krullDimSucc ≤ T'.krullDimSucc)
    (hH' : ∀ [LocallyOfFiniteType (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap],
      IsMaxContactHypersurface (NontrivialBoundary.pullbackWithNontrivialBoundary S q).base
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult (H.comap q))
    (hH'snc : InStrictNormalCrossingPosition (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap [H.comap q]) :
    IsPullbackBlowupSequence q
      (MaxContactReduction.reduceAlongHypersurface hinv T' (lowerDimensionalFamily A T')
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q) (H.comap q)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv T (lowerDimensionalFamily A T) S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  rcases le_total T.krullDimSucc T'.krullDimSucc with hle | hle
  · rw [reduceAlongHypersurface_congr_of_dim_le hstar hinv A T T' hle S hV hdimS H]
    exact isPullbackBlowupSequence_reduceAlongHypersurface_of_smooth hstar hinv P hmono A Bl hspec hshift T' hPdimOther S hV hO
      (le_trans hdimS hle) H hH hHsnc q hV' hdim' hH' hH'snc
  · rw [reduceAlongHypersurface_congr_of_dim_le hstar hinv A T' T hle (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' hdim'
      (H.comap q)]
    exact isPullbackBlowupSequence_reduceAlongHypersurface_of_smooth hstar hinv P hmono A Bl hspec hshift T hPdimT S hV hO hdimS
      H hH hHsnc q hV' (le_trans hdim' hle) hH' hH'snc


end

end MaxContactFunctoriality


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactHypersurfaceFieldBaseChange
section

open CategoryTheory.Limits TopologicalSpace

section

theorem isMaxContactHypersurface_comap_fieldBaseChange {k K : Type u} [Field k] [Field K]
    [CharZero k] [CharZero K] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p]
    (φ : CommRingCat.of k ⟶ CommRingCat.of K)
    [LocallyOfFiniteType (pullback.snd p (Spec.map φ))]
    (A : X.IdealSheafData) (m : ℕ) (H : X.IdealSheafData)
    (h : IsMaxContactHypersurface k p A m H) :
    IsMaxContactHypersurface K (pullback.snd p (Spec.map φ))
      (A.comap (pullback.fst p (Spec.map φ))) m
      (H.comap (pullback.fst p (Spec.map φ))) := by
  intro y
  obtain ⟨U, hU, hxU, hcase⟩ := h ((pullback.fst p (Spec.map φ)).base y)
  have hVaff : IsAffineOpen (pullback.fst p (Spec.map φ) ⁻¹ᵁ U) :=
    hU.preimage (pullback.fst p (Spec.map φ))
  refine ⟨pullback.fst p (Spec.map φ) ⁻¹ᵁ U, hVaff, hxU, ?_⟩
  rcases hcase with ⟨hdisj, hHtop⟩ | ⟨n, c, j, hH, hmc⟩
  · left
    refine ⟨?_, ?_⟩
    · rw [orderAtLeastLocus_comap_fieldBaseChange p φ A m, Set.disjoint_left]
      intro a ha ha'
      exact Set.disjoint_left.mp hdisj ha ha'
    · have h1 := restrictIdeal_comap (pullback.fst p (Spec.map φ)) H U
      rw [hHtop, Scheme.IdealSheafData.comap_top] at h1
      exact h1
  · right
    refine ⟨n, c.baseChange (isPullback_pullback_specMap p φ), j, ?_, ?_⟩
    · refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hVaff
        (c.baseChange (isPullback_pullback_specMap p φ))
        (H.comap (pullback.fst p (Spec.map φ))) {j} ?_
      rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE H (pullback.fst p (Spec.map φ))
          ⟨U, hU⟩ ⟨pullback.fst p (Spec.map φ) ⁻¹ᵁ U, hVaff⟩ le_rfl,
        c.ideal_eq_span_coord hU H {j} hH, Ideal.map_span]
      simp only [Finset.coe_singleton, Set.image_singleton]
      rw [EtaleChart.baseChange_coord]
    · refine (isMaxContactCoord_iff_coord_mem K (pullback.snd p (Spec.map φ))
        (A.comap (pullback.fst p (Spec.map φ))) m hVaff
        (c.baseChange (isPullback_pullback_specMap p φ)) j).mpr ?_
      rw [maxContactIdeal_comap_fieldBaseChange p φ m A,
        Scheme.IdealSheafData.comap_ideal_eq_map_appLE (maxContactIdeal k p A m)
          (pullback.fst p (Spec.map φ)) ⟨U, hU⟩
          ⟨pullback.fst p (Spec.map φ) ⁻¹ᵁ U, hVaff⟩ le_rfl,
        EtaleChart.baseChange_coord]
      exact Ideal.mem_map_of_mem _ ((isMaxContactCoord_iff_coord_mem k p A m hU c j).mp hmc)

namespace OrderReductionFieldBaseChange

section
variable (k L : Type u) [Field k] [Field L]

private theorem isMaxContactHypersurface_comap_specMapOfFieldHom_consolidated488 [CharZero k] [CharZero L] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p] (f : k →+* L)
    [hft : LocallyOfFiniteType (pullback.snd p (specMapOfFieldHom k L f))]
    (A : X.IdealSheafData) (m : ℕ) (H : X.IdealSheafData)
    (h : IsMaxContactHypersurface k p A m H) :
    IsMaxContactHypersurface L (pullback.snd p (specMapOfFieldHom k L f))
      (A.comap (pullback.fst p (specMapOfFieldHom k L f))) m
      (H.comap (pullback.fst p (specMapOfFieldHom k L f))) := by
  revert hft
  rw [specMapOfFieldHom_eq k L f]
  intro hft
  exact @isMaxContactHypersurface_comap_fieldBaseChange k L _ _ _ _ X p _ _
    (CommRingCat.ofHom f) hft A m H h

private theorem inStrictNormalCrossingPosition_comap_specMapOfFieldHom_consolidated488 {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (f : k →+* L)
    (H : X.IdealSheafData) (hsnc : InStrictNormalCrossingPosition p [H]) :
    InStrictNormalCrossingPosition (pullback.snd p (specMapOfFieldHom k L f))
      [H.comap (pullback.fst p (specMapOfFieldHom k L f))] := by
  rw [specMapOfFieldHom_eq k L f]
  exact inStrictNormalCrossingPosition_comap_pullback_specMap p (CommRingCat.ofHom f) [H] hsnc


end

theorem maxContactHypersurfaceBaseChange : MaxContactHypersurfaceBaseChange.{u} := by
  intro S L instL instCZ f hV hV' H hadm hsnc
  refine ⟨?_, ?_⟩
  · rw [S.baseChange_structureMorphism L f, S.baseChange_ideal L f, S.baseChange_mult L f]
    intro hlft
    exact @isMaxContactHypersurface_comap_specMapOfFieldHom_consolidated488 S.base L S.instField instL hV.charZero
      instCZ S.scheme S.structMap hV.smooth hV.locallyOfFiniteType f hlft S.ideal S.mult H
      (@hadm hV.locallyOfFiniteType)
  · rw [S.baseChange_structureMorphism L f]
    exact @inStrictNormalCrossingPosition_comap_specMapOfFieldHom_consolidated488 S.base L S.instField instL S.scheme S.structMap
      hV.smooth f H hsnc

end OrderReductionFieldBaseChange


end
end
end FunctorialResolution.EmbeddedResolution
end
