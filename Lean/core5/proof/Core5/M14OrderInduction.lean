import Mathlib
import Core5.M13MonomialInvariants

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicGeometry
universe u v
noncomputable section
-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparation
section


section
namespace FunctorialResolution.EmbeddedResolution

namespace BoundarySeparationByMaxContact

def BoundarySeparated (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (n : ℕ) : Prop :=
  ∀ (i : ℕ), i < n → ∀ hi : i < (s.boundary s.length).length,
    orderAtLeastLocus (s.ideal s.length) S.mult ∩
        ((((s.boundary s.length).get ⟨i, hi⟩).support : Set ↥(s.obj s.length))) = ∅

def SeparateBoundaryInvariant (S : MarkedIdealWithBoundary.{u}) (H : S.scheme.IdealSheafData)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (n : ℕ) : Prop :=
  BoundarySeparated S s n ∧ (∀ i < s.length, s.center i ≠ ⊤) ∧
    InStrictNormalCrossingPosition (s.proj 0 ≫ S.structMap) [MaxContactReduction.iteratedStrictTransform s H 0]

private theorem ne_top_of_support_nonempty_consolidated424 {X : Scheme.{u}} {J : X.IdealSheafData}
    (h : ((J.support : Set ↥X)).Nonempty) : J ≠ ⊤ := by
  intro hc
  obtain ⟨x, hx⟩ := h
  rw [hc] at hx
  have h1 : (1 : ℕ∞) ≤ orderAt (⊤ : X.IdealSheafData) x :=
    (one_le_orderAt_iff_mem_support (⊤ : X.IdealSheafData) x).2 hx
  rw [orderAt_top] at h1
  exact absurd h1 (by simp)

section
variable {X Y : Scheme.{u}}

private theorem comap_hom_ne_top_of_ne_top_consolidated424 (e : X ≅ Y) (J : Y.IdealSheafData)
    (hJ : J ≠ ⊤) : J.comap e.hom ≠ ⊤ := by
  have hs : ((J.support : Set ↥Y)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hc
    exact hJ ((AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty J).2 hc)
  obtain ⟨y, hy⟩ := hs
  have h2 : e.hom (e.inv y) = y := by simp
  have h3 : e.hom.base (e.inv.base y) ∈ J.support := by
    rw [show e.hom.base (e.inv.base y) = y from h2]
    exact hy
  have h4 : e.inv.base y ∈ (J.comap e.hom).support :=
    AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.2 h3
  exact ne_top_of_support_nonempty_consolidated424 ⟨e.inv.base y, h4⟩

private theorem comap_eqToHom_ne_top_consolidated424 (h : X = Y)
    (J : Y.IdealSheafData) (hJ : J ≠ ⊤) : J.comap (eqToHom h) ≠ ⊤ :=
  comap_hom_ne_top_of_ne_top_consolidated424 (eqToIso h) J hJ

private theorem comap_iso_inv_ne_top_consolidated424 (e : X ≅ Y)
    (J : X.IdealSheafData) (hJ : J ≠ ⊤) : J.comap e.inv ≠ ⊤ :=
  comap_hom_ne_top_of_ne_top_consolidated424 e.symm J hJ


end

private theorem orderAtLeastLocus_inter_support_eq_empty_of_eq_consolidated424 {X : Scheme.{u}} {I I' D D' : X.IdealSheafData}
    {m : ℕ} (hI : I = I') (hD : D = D')
    (h : orderAtLeastLocus I' m ∩ (D'.support : Set ↥X) = ∅) :
    orderAtLeastLocus I m ∩ (D.support : Set ↥X) = ∅ := by
  subst hI
  subst hD
  exact h

section
variable {X Y : Scheme.{u}} (hinv : ComapIsoInvariance.{u})
include hinv

private theorem orderAtLeastLocus_comap_iso_inter_support_eq_empty_consolidated424 (e : X ≅ Y) (I D : Y.IdealSheafData) (m : ℕ)
    (h : orderAtLeastLocus I m ∩ (D.support : Set ↥Y) = ∅) :
    orderAtLeastLocus (I.comap e.hom) m ∩ ((D.comap e.hom).support : Set ↥X) = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hx1, hx2⟩
  rw [hinv.coSupport_comap e I m] at hx1
  have hx2c : x ∈ (D.comap e.hom).support := hx2
  have hx2' : e.hom.base x ∈ D.support :=
    AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1 hx2c
  have hmem : e.hom.base x ∈ orderAtLeastLocus I m ∩ (D.support : Set ↥Y) := ⟨hx1, hx2'⟩
  rw [h] at hmem
  exact hmem

private theorem orderAtLeastLocus_comap_eqToHom_inter_support_eq_empty_consolidated424 (h : X = Y) (I D : Y.IdealSheafData) (m : ℕ)
    (hsep : orderAtLeastLocus I m ∩ (D.support : Set ↥Y) = ∅) :
    orderAtLeastLocus (I.comap (eqToHom h)) m ∩ ((D.comap (eqToHom h)).support : Set ↥X) = ∅ :=
  orderAtLeastLocus_comap_iso_inter_support_eq_empty_consolidated424 hinv (eqToIso h) I D m hsep

private theorem orderAtLeastLocus_inter_support_eq_empty_of_comap_iso_consolidated424 (e : X ≅ Y) (I D : Y.IdealSheafData) (m : ℕ)
    (h : orderAtLeastLocus (I.comap e.hom) m ∩ ((D.comap e.hom).support : Set ↥X) = ∅) :
    orderAtLeastLocus I m ∩ (D.support : Set ↥Y) = ∅ := by
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hy1, hy2⟩
  have h2 : e.hom (e.inv y) = y := by simp
  have k1 : e.inv.base y ∈ orderAtLeastLocus (I.comap e.hom) m := by
    rw [hinv.coSupport_comap e I m]
    show e.hom.base (e.inv.base y) ∈ orderAtLeastLocus I m
    rw [show e.hom.base (e.inv.base y) = y from h2]
    exact hy1
  have k2 : e.inv.base y ∈ ((D.comap e.hom).support : Set ↥X) := by
    have hy2' : e.hom.base (e.inv.base y) ∈ D.support := by
      rw [show e.hom.base (e.inv.base y) = y from h2]
      exact hy2
    exact AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.2 hy2'
  have hmem : e.inv.base y ∈
      orderAtLeastLocus (I.comap e.hom) m ∩ ((D.comap e.hom).support : Set ↥X) := ⟨k1, k2⟩
  rw [h] at hmem
  exact hmem


end

private theorem getElem_eq_of_list_eq_consolidated424 {α : Type*} {L L' : List α} (h : L = L') (n : ℕ)
    (hn : n < L.length) (hn' : n < L'.length) : L[n]'hn = L'[n]'hn' := by
  subst h
  rfl

section
variable {α β : Type*} (f : α → β)

private theorem getElem_map_of_lt_consolidated424 :
    ∀ (L : List α) (n : ℕ) (hn : n < L.length) (hn' : n < (L.map f).length),
      (L.map f)[n]'hn' = f (L[n]'hn) := by
  intro L
  induction L with
  | nil =>
      intro n hn _
      exact absurd hn (Nat.not_lt_zero n)
  | cons a L ih =>
      intro n hn hn'
      cases n with
      | zero => rfl
      | succ r =>
          have h1 : r < L.length := by
            simp only [List.length_cons] at hn
            omega
          have h2 : r < (L.map f).length := by
            simp only [List.length_map, List.length_cons] at hn' ⊢
            omega
          exact ih r h1 h2

private theorem getElem_map_append_of_lt_consolidated424 :
    ∀ (L : List α) (R : List β) (n : ℕ) (hn : n < L.length)
      (hn' : n < (L.map f ++ R).length), (L.map f ++ R)[n]'hn' = f (L[n]'hn) := by
  intro L
  induction L with
  | nil =>
      intro R n hn _
      exact absurd hn (Nat.not_lt_zero n)
  | cons a L ih =>
      intro R n hn hn'
      cases n with
      | zero => rfl
      | succ r =>
          have h1 : r < L.length := by
            simp only [List.length_cons] at hn
            omega
          have h2 : r < (L.map f ++ R).length := by
            simp only [List.length_append, List.length_map, List.length_cons] at hn' ⊢
            omega
          exact ih R r h1 h2


end

private theorem boundary_getElem_eq_iteratedStrictTransform_consolidated424 {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (u : MarkedBlowupSequenceData p I m E) (i : ℕ) (hi : i ≤ u.length) (n : ℕ) (hn : n < E.length)
    (hn' : n < (u.boundary i).length) :
    (u.boundary i)[n]'hn' = u.iteratedStrictTransform i (E[n]'hn) := by
  have h1 : u.boundary i = E.map (u.iteratedStrictTransform i) ++ u.boundaryFrom ([] : List X.IdealSheafData) i := by
    rw [← MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq u i hi]
    exact BlowupSequenceData.boundary_eq_map_iteratedStrictTransform_append u.toBlowupSequenceData E i
  have h2 : n < (E.map (u.iteratedStrictTransform i) ++ u.boundaryFrom ([] : List X.IdealSheafData) i).length := by
    rw [← h1]
    exact hn'
  rw [getElem_eq_of_list_eq_consolidated424 h1 n hn' h2]
  exact getElem_map_append_of_lt_consolidated424 (u.iteratedStrictTransform i) E
    (u.boundaryFrom ([] : List X.IdealSheafData) i) n hn h2

private theorem orderAtLeastLocus_append_succ_subset_preimage_consolidated424 (hstar : MaxContactCoverProperties.{u}) {k : Type u} [Field k]
    {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (hinv : ComapIsoInvariance.{u}) (r : ℕ) (hr : r < (s.append t hinv).length) :
    orderAtLeastLocus ((s.append t hinv).ideal (r + 1)) m ⊆
      ⇑((s.append t hinv).map r) ⁻¹' orderAtLeastLocus ((s.append t hinv).ideal r) m := by
  have hlen := MarkedBlowupSequenceData.append_length s t hinv
  have hrlen : r < (s.appendToBlowupSequenceData t).length := by
    rw [MarkedBlowupSequenceData.appendToBlowupSequenceData_length]
    omega
  have hb : Blowup.IsBlowupAlongIdealSheaf ((s.append t hinv).map r) ((s.append t hinv).center r) :=
    (s.append t hinv).isBlowup r hr
  have heq : Blowup.exceptionalIdeal ((s.append t hinv).map r) ((s.append t hinv).center r) ^ m *
      (s.append t hinv).ideal (r + 1)
        = ((s.append t hinv).ideal r).comap ((s.append t hinv).map r) :=
    MarkedBlowupSequenceData.exceptionalIdeal_pow_mul_appendIdeal_succ s t hinv r hrlen
  have hsupp : (((s.append t hinv).center r).support : Set ↥((s.append t hinv).obj r)) ⊆
      orderAtLeastLocus ((s.append t hinv).ideal r) m :=
    MarkedBlowupSequenceData.center_support_subset_orderAtLeastLocus_appendIdeal s t hinv r hrlen
  exact hstar.coSupport_le_preimage ((s.append t hinv).map r) ((s.append t hinv).center r) hb
    ((s.append t hinv).ideal r) ((s.append t hinv).ideal (r + 1)) m heq hsupp

section
variable (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
include hstar

private theorem separateBoundaryInvariant_append_consolidated424 (S : MarkedIdealWithBoundary.{u}) (H : S.scheme.IdealSheafData) (hH : InStrictNormalCrossingPosition S.structMap [H])
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
      (s.boundary s.length))
    (j : ℕ) (hj : j < S.boundary.length) (hbj : j < (s.boundary s.length).length)
    (hfacts : SeparateBoundaryInvariant S H s j)
    (hN : ∀ i, i ≤ t.length → IsLocallyNoetherian (t.obj i))
    (K : ∀ r : ℕ, (t.obj r).IdealSheafData)
    (h0 : K 0 = ((s.boundary s.length)[j]'hbj).comap t.isoZero.hom)
    (hstep : ∀ r, r < t.length →
      K (r + 1) = Blowup.strictTransform (t.map r) (t.center r) (K r) ∨
        K (r + 1) = (K r).comap (t.map r))
    (hsepK : ∀ r, r = t.length →
      orderAtLeastLocus (t.ideal r) S.mult ∩ ((K r).support : Set ↥(t.obj r)) = ∅)
    (hcent : ∀ r, r < t.length → t.center r ≠ ⊤) :
    SeparateBoundaryInvariant S H (s.append t hinv) (j + 1) := by
  have hsub : ∀ r, r ≤ t.length →
      ((t.iteratedStrictTransform r ((s.boundary s.length)[j]'hbj)).support : Set ↥(t.obj r)) ⊆
        ((K r).support : Set ↥(t.obj r)) := by
    intro r hr
    exact BlowupSequenceData.support_iteratedStrictTransform_subset_support t.toBlowupSequenceData hN
      ((s.boundary s.length)[j]'hbj) K h0 hstep r hr
  have hsepT : ∀ r, r ≤ t.length →
      orderAtLeastLocus (t.ideal r) S.mult ∩ ((K r).support : Set ↥(t.obj r)) = ∅ →
      orderAtLeastLocus (t.ideal r) S.mult ∩
        ((t.iteratedStrictTransform r ((s.boundary s.length)[j]'hbj)).support : Set ↥(t.obj r)) = ∅ := by
    intro r hr hsep
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hx1, hx2⟩
    have hmem : x ∈ orderAtLeastLocus (t.ideal r) S.mult ∩ ((K r).support : Set ↥(t.obj r)) :=
      ⟨hx1, hsub r hr hx2⟩
    rw [hsep] at hmem
    exact hmem
  have hulen : (s.append t hinv).length = s.length + t.length :=
    MarkedBlowupSequenceData.append_length s t hinv
  have hsle : s.length ≤ (s.append t hinv).length := by omega
  have hdesc : ∀ r, r < (s.append t hinv).length →
      orderAtLeastLocus ((s.append t hinv).ideal (r + 1)) S.mult ⊆
        ⇑((s.append t hinv).map r) ⁻¹' orderAtLeastLocus ((s.append t hinv).ideal r) S.mult :=
    fun r hr => orderAtLeastLocus_append_succ_subset_preimage_consolidated424 hstar s t hinv r hr
  have hblenU : ∀ r, r ≤ (s.append t hinv).length →
      ((s.append t hinv).boundary r).length = S.boundary.length + r :=
    fun r hr => MarkedBlowupSequenceData.boundary_length (s.append t hinv) r hr
  have hobj0 : (s.appendToBlowupSequenceData t).obj s.length = s.obj s.length :=
    MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.length)
  have hid0 : (s.append t hinv).ideal s.length = (s.ideal s.length).comap (eqToHom hobj0) := by
    rw [MarkedBlowupSequenceData.append_ideal s t hinv s.length,
      MarkedBlowupSequenceData.appendIdeal_of_le_length s t (le_refl s.length)]
  have hbd0 : (s.append t hinv).boundary s.length
      = (s.boundary s.length).map (fun D => D.comap (eqToHom hobj0)) := by
    rw [MarkedBlowupSequenceData.append_boundary s t hinv s.length,
      MarkedBlowupSequenceData.appendBoundary_of_le_length s t (le_refl s.length)]
  have hstep0 : ∀ (i : ℕ) (hiS : i < (s.boundary s.length).length)
      (hiU : i < ((s.append t hinv).boundary s.length).length),
      orderAtLeastLocus (s.ideal s.length) S.mult ∩
          (((s.boundary s.length)[i]'hiS).support : Set ↥(s.obj s.length)) = ∅ →
        orderAtLeastLocus ((s.append t hinv).ideal s.length) S.mult ∩
          ((((s.append t hinv).boundary s.length)[i]'hiU).support :
            Set ↥((s.append t hinv).obj s.length)) = ∅ := by
    intro i hiS hiU hsep
    have himap : i < ((s.boundary s.length).map
        (fun D => D.comap (eqToHom hobj0))).length := by simpa using hiS
    have hbeli : ((s.append t hinv).boundary s.length)[i]'hiU
        = ((s.boundary s.length)[i]'hiS).comap (eqToHom hobj0) :=
      (getElem_eq_of_list_eq_consolidated424 hbd0 i hiU himap).trans
        (getElem_map_of_lt_consolidated424
          (fun D : (s.obj s.length).IdealSheafData => D.comap (eqToHom hobj0))
          (s.boundary s.length) i hiS himap)
    exact orderAtLeastLocus_inter_support_eq_empty_of_eq_consolidated424 hid0 hbeli
      (orderAtLeastLocus_comap_eqToHom_inter_support_eq_empty_consolidated424 hinv hobj0 (s.ideal s.length)
        ((s.boundary s.length)[i]'hiS) S.mult hsep)
  have hmid : ∀ (hjU : j < ((s.append t hinv).boundary (s.length + t.length)).length),
      orderAtLeastLocus ((s.append t hinv).ideal (s.length + t.length)) S.mult ∩
        ((((s.append t hinv).boundary (s.length + t.length))[j]'hjU).support :
          Set ↥((s.append t hinv).obj (s.length + t.length))) = ∅ := by
    intro hjU
    rcases Nat.eq_zero_or_pos t.length with hz | hpos
    · have hI0 : t.ideal 0 = (s.ideal s.length).comap t.isoZero.hom := t.ideal_zero
      have hjun : orderAtLeastLocus (s.ideal s.length) S.mult ∩
          (((s.boundary s.length)[j]'hbj).support : Set ↥(s.obj s.length)) = ∅ := by
        refine orderAtLeastLocus_inter_support_eq_empty_of_comap_iso_consolidated424 hinv t.isoZero (s.ideal s.length)
          ((s.boundary s.length)[j]'hbj) S.mult ?_
        have h1 := hsepT 0 (Nat.zero_le _) (hsepK 0 hz.symm)
        rw [BlowupSequenceData.iteratedStrictTransform_zero] at h1
        exact orderAtLeastLocus_inter_support_eq_empty_of_eq_consolidated424 hI0.symm rfl h1
      have hjU0 : j < ((s.append t hinv).boundary s.length).length := by
        have h := hblenU s.length hsle
        omega
      exact (s.append t hinv).orderAtLeastLocus_disjoint_boundary_of_le hdesc hj hsle
        (hstep0 j hbj hjU0 hjun) (s.length + t.length) (Nat.le_add_right _ _)
        (le_of_eq hulen.symm)
    · have hobjT : (s.appendToBlowupSequenceData t).obj (s.length + t.length) = t.obj t.length :=
        MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_length_add_length s t hpos
      have hidT : (s.append t hinv).ideal (s.length + t.length)
          = (t.ideal t.length).comap (eqToHom hobjT) :=
        MarkedBlowupSequenceData.append_ideal_length_add_length s t hinv hpos
      have hbdT : (s.append t hinv).boundary (s.length + t.length)
          = (t.boundary t.length).map (fun D => D.comap (eqToHom hobjT)) :=
        MarkedBlowupSequenceData.append_boundary_length_add_length s t hinv hpos
      have hjtt : j < (t.boundary t.length).length := by
        have h := MarkedBlowupSequenceData.boundary_length t t.length (le_refl t.length)
        omega
      have hjmapT : j < ((t.boundary t.length).map
          (fun D => D.comap (eqToHom hobjT))).length := by simpa using hjtt
      have hbelT : ((s.append t hinv).boundary (s.length + t.length))[j]'hjU
          = ((t.boundary t.length)[j]'hjtt).comap (eqToHom hobjT) :=
        (getElem_eq_of_list_eq_consolidated424 hbdT j hjU hjmapT).trans
          (getElem_map_of_lt_consolidated424
            (fun D : (t.obj t.length).IdealSheafData => D.comap (eqToHom hobjT))
            (t.boundary t.length) j hjtt hjmapT)
      have hbel : (t.boundary t.length)[j]'hjtt
          = t.iteratedStrictTransform t.length ((s.boundary s.length)[j]'hbj) :=
        boundary_getElem_eq_iteratedStrictTransform_consolidated424 t t.length (le_refl t.length) j hbj hjtt
      refine orderAtLeastLocus_inter_support_eq_empty_of_eq_consolidated424 hidT hbelT ?_
      refine orderAtLeastLocus_comap_eqToHom_inter_support_eq_empty_consolidated424 hinv hobjT (t.ideal t.length)
        ((t.boundary t.length)[j]'hjtt) S.mult ?_
      exact orderAtLeastLocus_inter_support_eq_empty_of_eq_consolidated424 rfl hbel
        (hsepT t.length (le_refl t.length) (hsepK t.length rfl))
  have htop : ∀ (hjU : j < ((s.append t hinv).boundary ((s.append t hinv).length)).length),
      orderAtLeastLocus ((s.append t hinv).ideal ((s.append t hinv).length)) S.mult ∩
        ((((s.append t hinv).boundary ((s.append t hinv).length))[j]'hjU).support :
          Set ↥((s.append t hinv).obj ((s.append t hinv).length))) = ∅ := by
    intro hjU
    have hjmid : j < ((s.append t hinv).boundary (s.length + t.length)).length := by
      have h := hblenU (s.length + t.length) (le_of_eq hulen.symm)
      omega
    exact (s.append t hinv).orderAtLeastLocus_disjoint_boundary_of_le hdesc hj (le_of_eq hulen.symm)
      (hmid hjmid) ((s.append t hinv).length) (le_of_eq hulen.symm) (le_refl _)
  refine ⟨?_, ?_, inStrictNormalCrossingPosition_iteratedStrictTransform_zero S (s.append t hinv) H hH⟩
  · intro i hi hii
    simp only [List.get_eq_getElem]
    rcases Nat.lt_or_ge i j with hij | hij
    · have hiE : i < S.boundary.length := lt_trans hij hj
      have hiU0 : i < ((s.append t hinv).boundary s.length).length := by
        have h := hblenU s.length hsle
        omega
      have hiS : i < (s.boundary s.length).length := by
        have h := MarkedBlowupSequenceData.boundary_length s s.length (le_refl s.length)
        omega
      have hbase : orderAtLeastLocus (s.ideal s.length) S.mult ∩
          (((s.boundary s.length)[i]'hiS).support : Set ↥(s.obj s.length)) = ∅ := by
        have h := hfacts.1 i hij hiS
        simp only [List.get_eq_getElem] at h
        exact h
      exact (s.append t hinv).orderAtLeastLocus_disjoint_boundary_of_le hdesc hiE hsle
        (hstep0 i hiS hiU0 hbase) ((s.append t hinv).length) hsle (le_refl _)
    · have hije : i = j := by omega
      subst hije
      exact htop hii
  · intro r hr
    rw [MarkedBlowupSequenceData.append_toBlowupSequenceData]
    rcases lt_trichotomy r s.length with h | h | h
    · rw [MarkedBlowupSequenceData.appendToBlowupSequenceData_center_of_lt_length s t h]
      exact comap_eqToHom_ne_top_consolidated424 _ _ (hfacts.2.1 r h)
    · subst h
      rw [MarkedBlowupSequenceData.appendToBlowupSequenceData_center_length s t]
      have hpos : 0 < t.length := by omega
      exact comap_eqToHom_ne_top_consolidated424 _ _
        (comap_iso_inv_ne_top_consolidated424 t.isoZero (t.center 0) (hcent 0 hpos))
    · rw [MarkedBlowupSequenceData.appendToBlowupSequenceData_center_of_length_lt s t h]
      have hlt : r - s.length < t.length := by omega
      exact comap_eqToHom_ne_top_consolidated424 _ _ (hcent (r - s.length) hlt)

theorem separateBoundaryInvariant_appendLowerDimReduction (P : ℕ → Prop)
    (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u})
    (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (H : S.scheme.IdealSheafData) (hH : InStrictNormalCrossingPosition S.structMap [H])
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (j : ℕ) (hj : j < S.boundary.length) (hfacts : SeparateBoundaryInvariant S H s j) :
    SeparateBoundaryInvariant S H
      (MaxContactReduction.appendLowerDimReduction hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T) S s [] 0 j) (j + 1) := by
  classical
  have hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap) :=
    locallyOfFiniteType_projectionToBase_comp hstar S hV s s.length (le_refl s.length)
  have hm : 1 ≤ S.mult := hV.one_le_mult
  have hbj : j < (s.boundary s.length).length := by
    have h := MarkedBlowupSequenceData.boundary_length s s.length (le_refl s.length)
    omega
  have hsncAll : InStrictNormalCrossingPosition (s.proj s.length ≫ S.structMap) (s.boundary s.length) := by
    have h := (hstar.valid_level S hV s.toMarkedSequenceOfBlowups s.length (le_refl s.length)).snc
    simp at h
    with_unfolding_all exact h
  have hsnc0 : InStrictNormalCrossingPosition (s.proj s.length ≫ S.structMap)
      (([] : List ((s.obj s.length)).IdealSheafData) ++ (s.boundary s.length).drop 0) := by
    simpa using hsncAll
  have hVc : (MaxContactCoverData.derivedTriple S s hft [] 0).IsAdmissible :=
    isAdmissible_derivedTriple hstar S hV s hft [] 0 hsnc0
  have hdimC : (MaxContactCoverData.derivedTriple S s hft [] 0).krullDimSucc ≤ T.krullDimSucc := by
    have h1 := hstar.schemeDim_level_le S hV s.toMarkedSequenceOfBlowups s.length (le_refl s.length)
    have h2 : (MaxContactCoverData.derivedTriple S s hft [] 0).krullDimSucc ≤ S.krullDimSucc := by
      with_unfolding_all exact h1
    exact le_trans h2 hdimS
  have hPC : P (MaxContactCoverData.derivedTriple S s hft [] 0).krullDimSucc := hmono _ _ hdimC hPdimT
  have hordBound := LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hft [] 0 hVc
  have hbalanced := LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hm hO s hft [] 0 hVc
  have hbdC : (MaxContactCoverData.derivedTriple S s hft [] 0).boundary = s.boundary s.length := by
    rw [MaxContactCoverData.derivedTriple_boundary]
    simp
  have hjC' : j < (MaxContactCoverData.derivedTriple S s hft [] 0).boundary.length := by
    rw [hbdC]
    exact hbj
  have hjC : j < (([] : List ((s.obj s.length)).IdealSheafData)
      ++ (s.boundary s.length).drop 0).length := by simpa using hbj
  have hsepC : ∀ D ∈ (s.boundary s.length).take 0,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (D.support : Set ↥(s.obj s.length)) = ∅ := by
    intro D hD
    simp at hD
  obtain ⟨hmk, hceq, hcos⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A B j (hspec j)
    (MaxContactFunctoriality.lowerDimensionalFamily A T) (fun _ _ _ => rfl) S hV hm hO s [] 0 hft hdimC hPC hVc
    hjC hsepC
  obtain ⟨Dv, bv, _, hC2, _, hC4, hC5, hC6, _⟩ :=
    (hspec j).shape (MaxContactCoverData.derivedTriple S s hft [] 0) hVc hPC hordBound hbalanced hjC'
  have hget : ((MaxContactCoverData.derivedTriple S s hft [] 0).boundary.get ⟨j, hjC'⟩)
      = (s.boundary s.length)[j]'hbj := by
    simp only [List.get_eq_getElem]
    exact getElem_eq_of_list_eq_consolidated424 hbdC j hjC' hbj
  rw [hceq]
  refine separateBoundaryInvariant_append_consolidated424 hstar hinv S H hH s _ j hj hbj hfacts ?_ Dv ?_ ?_ ?_ ?_
  · intro i hi
    exact isLocallyNoetherian_tunedMarkedBlowupSeq_schemeAt hstar S hV s hft [] 0 hVc
      (A j (MaxContactCoverData.derivedTriple S s hft [] 0)) i hi
  · rw [hC2, hget]
    with_unfolding_all rfl
  · intro r hr
    by_cases hb : bv = true ∧ r = 0
    · obtain ⟨hb1, hb2⟩ := hb
      subst hb2
      exact Or.inr (hC4 hb1).2.2
    · exact Or.inl (hC5 r hr hb)
  · intro r hrr
    have hrr' : r = (A j (MaxContactCoverData.derivedTriple S s hft [] 0)).length := hrr
    subst hrr'
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hx1, hx2⟩
    have hc := hcos ((A j (MaxContactCoverData.derivedTriple S s hft [] 0)).length) (le_refl _)
    have hx1' : x ∈ orderAtLeastLocus
        ((BlowupSequenceData.ofSequenceOfBlowups (A j (MaxContactCoverData.derivedTriple S s hft [] 0)).toSequenceOfBlowups).controlledTransform
          (s.ideal s.length) S.mult ((A j (MaxContactCoverData.derivedTriple S s hft [] 0)).length))
        S.mult := hx1
    rw [hc] at hx1'
    have hmem : x ∈ orderAtLeastLocus
        (MarkedSequenceOfBlowups.lastIdeal (A j (MaxContactCoverData.derivedTriple S s hft [] 0)))
        (MaxContactCoverData.derivedTriple S s hft [] 0).mult ∩
        (((Dv ((A j (MaxContactCoverData.derivedTriple S s hft [] 0)).length)).support) :
          Set ↥((A j (MaxContactCoverData.derivedTriple S s hft [] 0)).schemeAt
            ((A j (MaxContactCoverData.derivedTriple S s hft [] 0)).length))) := ⟨hx1', hx2⟩
    rw [hC6] at hmem
    exact hmem
  · intro r hr htop
    exact ((hspec j).center_nonempty (MaxContactCoverData.derivedTriple S s hft [] 0) hVc hPC hordBound hbalanced
      hjC' r hr).ne_empty
      ((AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).1 htop)


end

abbrev separateBoundarySeq (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hinv : ComapIsoInvariance.{u})
    (A : ℕ → PrincipalizationAssignment.{u}) (j : ℕ) :
    MarkedBlowupSequenceData (MaxContactCoverData.coverTriple T hv).structMap
      (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.coverTriple T hv).mult
      (MaxContactCoverData.coverTriple T hv).boundary :=
  MaxContactReduction.separateBoundary hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
    (MaxContactCoverData.coverTriple T hv) j

abbrev separateAllBoundary (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hinv : ComapIsoInvariance.{u})
    (A : ℕ → PrincipalizationAssignment.{u}) :
    MarkedBlowupSequenceData (MaxContactCoverData.coverTriple T hv).structMap
      (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.coverTriple T hv).mult
      (MaxContactCoverData.coverTriple T hv).boundary :=
  separateBoundarySeq T hv hinv A (MaxContactCoverData.coverTriple T hv).boundary.length

abbrev reduceAlongHypersurfaceTriple (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hinv : ComapIsoInvariance.{u})
    (A : ℕ → PrincipalizationAssignment.{u})
    (hft : LocallyOfFiniteType
      ((separateAllBoundary T hv hinv A).proj (separateAllBoundary T hv hinv A).length ≫
        (MaxContactCoverData.coverTriple T hv).structMap)) : MarkedIdealWithBoundary.{u} :=
  MaxContactCoverData.derivedTriple (MaxContactCoverData.coverTriple T hv) (separateAllBoundary T hv hinv A) hft
    [MaxContactReduction.strictTransformAtLength (separateAllBoundary T hv hinv A) (MaxContactCoverData.coverMaxContactIdeal T hv)]
    (MaxContactCoverData.coverTriple T hv).boundary.length

theorem separateBoundaryInvariant_separateBoundarySeq (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop)
    (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u})
    (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T)
    (j : ℕ) (hj : j ≤ (MaxContactCoverData.coverTriple T h.valid).boundary.length) :
    SeparateBoundaryInvariant (MaxContactCoverData.coverTriple T h.valid)
      (MaxContactCoverData.coverMaxContactIdeal T h.valid) (separateBoundarySeq T h.valid hinv A j) j := by
  revert hj
  induction j with
  | zero =>
      intro _
      have h0 : separateBoundarySeq T h.valid hinv A 0
          = emptyMarkedBlowupSequenceData (MaxContactCoverData.coverTriple T h.valid).structMap
              (MaxContactCoverData.coverTriple T h.valid).ideal
              (MaxContactCoverData.coverTriple T h.valid).mult
              (MaxContactCoverData.coverTriple T h.valid).boundary :=
        MaxContactCoverData.separateBoundary_zero hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
          (MaxContactCoverData.coverTriple T h.valid)
      refine And.intro ?_ (And.intro ?_ ?_)
      · intro i hi
        exact absurd hi (Nat.not_lt_zero i)
      · rw [h0]
        intro i hi
        exact absurd hi (Nat.not_lt_zero i)
      · exact inStrictNormalCrossingPosition_iteratedStrictTransform_zero (MaxContactCoverData.coverTriple T h.valid)
          (separateBoundarySeq T h.valid hinv A 0) (MaxContactCoverData.coverMaxContactIdeal T h.valid)
          (inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P T h)
  | succ n ih =>
      intro hj
      have hn : n < (MaxContactCoverData.coverTriple T h.valid).boundary.length := hj
      have hfacts := ih (Nat.le_of_succ_le hj)
      have hsucc : separateBoundarySeq T h.valid hinv A (n + 1)
          = MaxContactReduction.appendLowerDimReduction hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
              (MaxContactCoverData.coverTriple T h.valid) (separateBoundarySeq T h.valid hinv A n) [] 0 n :=
        MaxContactCoverData.separateBoundary_succ hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
          (MaxContactCoverData.coverTriple T h.valid) n
      rw [hsucc]
      exact separateBoundaryInvariant_appendLowerDimReduction hstar hinv P hmono A B hspec T h.dim_prop
        (MaxContactCoverData.coverTriple T h.valid) (isAdmissible_coverTriple hstar P T h)
        (orderAt_coverTriple_ideal_le_mult hstar P T h) (hstar.coverTriple_dim_le T h.valid)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid) (inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P T h)
        (separateBoundarySeq T h.valid hinv A n) n hn hfacts

private theorem forall_mem_take_of_forall_lt_consolidated424 {α : Type*} (Q : α → Prop) :
    ∀ (L : List α) (n : ℕ),
      (∀ i : ℕ, i < n → ∀ hi : i < L.length, Q (L.get ⟨i, hi⟩)) → ∀ a ∈ L.take n, Q a := by
  intro L
  induction L with
  | nil =>
      intro n _ a ha
      simp at ha
  | cons b L ih =>
      intro n hQ a ha
      cases n with
      | zero => simp at ha
      | succ m =>
          have ha' : a ∈ b :: L.take m := ha
          rcases List.mem_cons.mp ha' with rfl | ha''
          · exact hQ 0 (Nat.succ_pos m) (by simp)
          · exact ih m
              (fun i him hi => hQ (i + 1) (Nat.succ_lt_succ him) (Nat.succ_lt_succ hi)) a ha''

theorem exists_cover_eq_separateAllBoundary_append (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u})
    (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T) :
    ∃ hft : LocallyOfFiniteType
        ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
          (MaxContactCoverData.coverTriple T h.valid).structMap),
      ∃ _hV : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).IsAdmissible,
        P (reduceAlongHypersurfaceTriple T h.valid hinv A hft).krullDimSucc ∧
        ∃ hmk : (BlowupSequenceData.ofSequenceOfBlowups
            (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).IsMarked
            ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
              (MaxContactCoverData.coverTriple T h.valid).structMap)
            ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
            (MaxContactCoverData.coverTriple T h.valid).mult
            ((separateAllBoundary T h.valid hinv A).boundary
              (separateAllBoundary T h.valid hinv A).length),
          MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T) =
              (separateAllBoundary T h.valid hinv A).append
                (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
                  (separateAllBoundary T h.valid hinv A)
                  hft
                  [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
                    (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
                  (MaxContactCoverData.coverTriple T h.valid).boundary.length
                  (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk) hinv ∧
            ∀ i ≤ (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups.length,
              orderAtLeastLocus
                  ((BlowupSequenceData.ofSequenceOfBlowups
                      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).controlledTransform
                    ((separateAllBoundary T h.valid hinv A).ideal
                      (separateAllBoundary T h.valid hinv A).length)
                    (MaxContactCoverData.coverTriple T h.valid).mult i)
                  (MaxContactCoverData.coverTriple T h.valid).mult =
                orderAtLeastLocus ((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).ideal i)
                  (tuningExponent (MaxContactCoverData.coverTriple T h.valid).mult) := by
  have hV : (MaxContactCoverData.coverTriple T h.valid).IsAdmissible := isAdmissible_coverTriple hstar P T h
  have hO : ∀ x : ↥(MaxContactCoverData.coverTriple T h.valid).scheme,
      orderAt (MaxContactCoverData.coverTriple T h.valid).ideal x ≤
        ((MaxContactCoverData.coverTriple T h.valid).mult : ℕ∞) :=
    orderAt_coverTriple_ideal_le_mult hstar P T h
  have hft : LocallyOfFiniteType
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap) :=
    locallyOfFiniteType_projectionToBase_comp hstar (MaxContactCoverData.coverTriple T h.valid) hV
      (separateAllBoundary T h.valid hinv A) (separateAllBoundary T h.valid hinv A).length (le_refl _)
  have hadm := isMaxContactHypersurface_coverMaxContactIdeal hstar P T h
  have hzero := inStrictNormalCrossingPosition_iteratedStrictTransform_zero (MaxContactCoverData.coverTriple T h.valid)
    (separateAllBoundary T h.valid hinv A) (MaxContactCoverData.coverMaxContactIdeal T h.valid)
    (inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P T h)
  have hsnc := inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar (MaxContactCoverData.coverTriple T h.valid)
    hV hO (MaxContactCoverData.coverMaxContactIdeal T h.valid) hadm (separateAllBoundary T h.valid hinv A) hzero
    (separateAllBoundary T h.valid hinv A).length (le_refl _)
  have hsnc' : InStrictNormalCrossingPosition
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap)
      ([MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)] ++
        ((separateAllBoundary T h.valid hinv A).boundary
          (separateAllBoundary T h.valid hinv A).length).drop
            (MaxContactCoverData.coverTriple T h.valid).boundary.length) := by
    exact hsnc
  have hVc : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).IsAdmissible :=
    isAdmissible_derivedTriple hstar (MaxContactCoverData.coverTriple T h.valid) hV
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length hsnc'
  have hdim : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).krullDimSucc ≤ T.krullDimSucc := by
    have h1 := hstar.schemeDim_level_le (MaxContactCoverData.coverTriple T h.valid) hV
      (separateAllBoundary T h.valid hinv A).toMarkedSequenceOfBlowups (separateAllBoundary T h.valid hinv A).length
      (le_refl _)
    have h2 := hstar.coverTriple_dim_le T h.valid
    have h3 : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).krullDimSucc ≤
        (MaxContactCoverData.coverTriple T h.valid).krullDimSucc := by
      with_unfolding_all exact h1
    exact le_trans h3 h2
  have hP : P (reduceAlongHypersurfaceTriple T h.valid hinv A hft).krullDimSucc := hmono _ _ hdim h.dim_prop
  have hj : 0 < ([MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)] ++
      ((separateAllBoundary T h.valid hinv A).boundary
        (separateAllBoundary T h.valid hinv A).length).drop
          (MaxContactCoverData.coverTriple T h.valid).boundary.length).length := by
    rw [List.singleton_append, List.length_cons]
    omega
  have hfacts := separateBoundaryInvariant_separateBoundarySeq hstar hinv P hmono A B hspec T h
    (MaxContactCoverData.coverTriple T h.valid).boundary.length (le_refl _)
  have htop : BoundarySeparated (MaxContactCoverData.coverTriple T h.valid) (separateAllBoundary T h.valid hinv A)
      (MaxContactCoverData.coverTriple T h.valid).boundary.length := And.left hfacts
  have hsep : ∀ D ∈ ((separateAllBoundary T h.valid hinv A).boundary
        (separateAllBoundary T h.valid hinv A).length).take
          (MaxContactCoverData.coverTriple T h.valid).boundary.length,
      orderAtLeastLocus ((separateAllBoundary T h.valid hinv A).ideal
            (separateAllBoundary T h.valid hinv A).length)
          (MaxContactCoverData.coverTriple T h.valid).mult ∩
        ((D.support : Set ↥((separateAllBoundary T h.valid hinv A).obj
          (separateAllBoundary T h.valid hinv A).length))) = ∅ :=
    forall_mem_take_of_forall_lt_consolidated424 _ _ _ htop
  obtain ⟨hmk, heq, hcos⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A B 0 (hspec 0)
    (MaxContactFunctoriality.lowerDimensionalFamily A T) (fun _ _ _ => rfl)
    (MaxContactCoverData.coverTriple T h.valid) hV hV.one_le_mult hO
    (separateAllBoundary T h.valid hinv A)
    [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
      (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
    (MaxContactCoverData.coverTriple T h.valid).boundary.length hft hdim hP hVc hj hsep
  have hcover : MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T) =
      MaxContactReduction.appendLowerDimReduction hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
        (MaxContactCoverData.coverTriple T h.valid) (separateAllBoundary T h.valid hinv A)
        [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
        (MaxContactCoverData.coverTriple T h.valid).boundary.length 0 :=
    MaxContactCoverData.reduceAlongHypersurface_eq_appendLowerDimReduction hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
      (MaxContactCoverData.coverTriple T h.valid) (MaxContactCoverData.coverMaxContactIdeal T h.valid)
  refine ⟨hft, hVc, hP, hmk, ?_, hcos⟩
  rw [hcover]
  exact heq

end BoundarySeparationByMaxContact

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverMaxContactIdeal
section

open CategoryTheory.Limits

section
namespace FunctorialResolution.EmbeddedResolution

private theorem range_ι_base_subset_consolidated423 {X : Scheme.{u}} (U : X.Opens) :
    Set.range U.ι.base ⊆ (U : Set ↥X) :=
  (Scheme.Opens.range_ι U).subset

private theorem comap_comap_eq_of_comp_eq_consolidated423 {W X Y Z : Scheme.{u}} (a : W ⟶ X) (b : X ⟶ Z) (a' : W ⟶ Y)
    (b' : Y ⟶ Z) (hsq : a ≫ b = a' ≫ b') (I : Z.IdealSheafData) :
    (I.comap b).comap a = (I.comap b').comap a' := by
  have h1 : (I.comap b).comap a = I.comap (a ≫ b) := by
    simp [Scheme.IdealSheafData.comap_comp]
  have h2 : (I.comap b').comap a' = I.comap (a' ≫ b') := by
    simp [Scheme.IdealSheafData.comap_comp]
  rw [h1, h2, hsq]

section
variable (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)

private theorem restrictIdeal_coverTripleOpen_coverMaxContactIdeal_consolidated423 (hres : ∀ i : (MaxContactCoverData.chosenCoverData T hv).idx,
      (MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i) =
        (MaxContactCoverData.chosenCoverData T hv).localIdeal i)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    @restrictIdeal (MaxContactCoverData.coverTriple T hv).scheme
        (MaxContactCoverData.coverMaxContactIdeal T hv) (MaxContactOpenCover.coverTripleOpen T hv i) =
      ((MaxContactCoverData.chosenCoverData T hv).localIdeal i).comap (MaxContactOpenCover.coverPieceIso T hv i).inv :=
  (MaxContactOpenCover.restrictIdeal_coverTripleOpen T hv i (MaxContactCoverData.coverMaxContactIdeal T hv)).trans
    (congrArg (fun J : (MaxContactOpenCover.coverPiece T hv i).IdealSheafData =>
      J.comap (MaxContactOpenCover.coverPieceIso T hv i).inv) (hres i))

theorem isMaxContactHypersurface_coverMaxContactIdeal_of_comap_eq [LocallyOfFiniteType (MaxContactCoverData.coverTriple T hv).structMap]
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
    (hres : ∀ i : (MaxContactCoverData.chosenCoverData T hv).idx,
      (MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i) =
        (MaxContactCoverData.chosenCoverData T hv).localIdeal i) :
    IsMaxContactHypersurface (MaxContactCoverData.coverTriple T hv).base
      (MaxContactCoverData.coverTriple T hv).structMap (MaxContactCoverData.coverTriple T hv).ideal
      (MaxContactCoverData.tunedMult T) (MaxContactCoverData.coverMaxContactIdeal T hv) := by
  have := hv.charZero
  have := hv.smooth
  have := hv.locallyOfFiniteType
  have hftc : LocallyOfFiniteType
      (MaxContactCoverData.coverMap T hv ≫ T.structMap) :=
    (inferInstance : LocallyOfFiniteType
      (MaxContactCoverData.coverTriple T hv).structMap)
  intro x
  obtain ⟨i, hxi⟩ := MaxContactOpenCover.exists_mem_coverTripleOpen T hv x
  have hAff0 : IsAffine (MaxContactOpenCover.coverPiece T hv i) := hgood.isAffine i
  have haffineOpen : IsAffineOpen (MaxContactOpenCover.coverTripleOpen T hv i) :=
    isAffineOpen_opensRange (MaxContactOpenCover.coverPieceι T hv i)
  refine ⟨MaxContactOpenCover.coverTripleOpen T hv i, haffineOpen, hxi, ?_⟩
  have hcompι : MaxContactOpenCover.coverPieceι T hv i ≫ MaxContactCoverData.coverMap T hv =
      ((MaxContactCoverData.chosenCoverData T hv).opens i).ι :=
    sigma_ι_sigmaOpensDesc T.scheme (MaxContactCoverData.chosenCoverData T hv).opens i
  have hsub : ∀ y : ↥(MaxContactCoverData.coverTriple T hv).scheme,
      y ∈ (↑(MaxContactOpenCover.coverTripleOpen T hv i) :
        Set ↥(MaxContactCoverData.coverTriple T hv).scheme) →
      (MaxContactCoverData.coverMap T hv).base y ∈
        (↑((MaxContactCoverData.chosenCoverData T hv).opens i) : Set ↥T.scheme) := by
    intro y hy
    have hy' : y ∈ Set.range (MaxContactOpenCover.coverPieceι T hv i).base := hy
    obtain ⟨z, rfl⟩ := hy'
    have hz : (MaxContactCoverData.coverMap T hv).base ((MaxContactOpenCover.coverPieceι T hv i).base z) =
        ((MaxContactCoverData.chosenCoverData T hv).opens i).ι.base z := by
      rw [← hcompι]
      rfl
    rw [hz]
    exact range_ι_base_subset_consolidated423 _ ⟨z, rfl⟩
  rcases hgood.dichotomy i with ⟨hdisj, htop⟩ | ⟨n, c, j, hloc, hmc⟩
  · left
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      intro y hy hy2
      have hy3 : y ∈ orderAtLeastLocus
          ((MaxContactCoverData.balancedTunedIdeal T hv).comap (MaxContactCoverData.coverMap T hv))
          (MaxContactCoverData.tunedMult T) := hy
      rw [orderAtLeastLocus_comap T.base T.structMap (MaxContactCoverData.coverMap T hv)
        (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)] at hy3
      have hy4 : (MaxContactCoverData.coverMap T hv).base y ∈
          orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) := hy3
      exact (Set.disjoint_left.mp hdisj) hy4 (hsub y hy2)
    · rw [restrictIdeal_coverTripleOpen_coverMaxContactIdeal_consolidated423 T hv hres i, htop]
      exact Scheme.IdealSheafData.comap_top _
  · right
    refine ⟨n, MaxContactOpenCover.coverEtaleChart T hv i c, j, ?_, ?_⟩
    · rw [restrictIdeal_coverTripleOpen_coverMaxContactIdeal_consolidated423 T hv hres i, hloc]
      exact (MaxContactOpenCover.coverEtaleChart_coordIdeal T hv i c {j}).symm
    · have hmc' : c.coordIdeal {j} ≤
          (maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv)
            (MaxContactCoverData.tunedMult T)).comap
            ((MaxContactCoverData.chosenCoverData T hv).opens i).ι := hmc
      have hmax : maxContactIdeal (MaxContactCoverData.coverTriple T hv).base
            (MaxContactCoverData.coverTriple T hv).structMap
            (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.tunedMult T) =
          (maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv)
            (MaxContactCoverData.tunedMult T)).comap (MaxContactCoverData.coverMap T hv) :=
        derivIdealSheafIterate_comap T.base T.structMap (MaxContactCoverData.coverMap T hv)
          (MaxContactCoverData.tunedMult T - 1) (MaxContactCoverData.balancedTunedIdeal T hv)
      have h1 : (MaxContactOpenCover.coverEtaleChart T hv i c).coordIdeal {j}
          = (c.coordIdeal {j}).comap (MaxContactOpenCover.coverPieceIso T hv i).inv :=
        MaxContactOpenCover.coverEtaleChart_coordIdeal T hv i c {j}
      have h2 := comap_comap_eq_of_comp_eq_consolidated423 (MaxContactOpenCover.coverTripleOpen T hv i).ι
        (MaxContactCoverData.coverMap T hv)
        (MaxContactOpenCover.coverPieceIso T hv i).inv ((MaxContactCoverData.chosenCoverData T hv).opens i).ι
        (MaxContactOpenCover.coverTripleOpen_ι_comp_coverMap T hv i)
        (maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv)
          (MaxContactCoverData.tunedMult T))
      have h3 : (c.coordIdeal {j}).comap (MaxContactOpenCover.coverPieceIso T hv i).inv ≤
          ((maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv)
            (MaxContactCoverData.tunedMult T)).comap
              ((MaxContactCoverData.chosenCoverData T hv).opens i).ι).comap
            (MaxContactOpenCover.coverPieceIso T hv i).inv :=
        Scheme.IdealSheafData.comap_mono _ hmc'
      show (MaxContactOpenCover.coverEtaleChart T hv i c).coordIdeal {j} ≤
        restrictIdeal (maxContactIdeal (MaxContactCoverData.coverTriple T hv).base
          (MaxContactCoverData.coverTriple T hv).structMap
          (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.tunedMult T))
          (MaxContactOpenCover.coverTripleOpen T hv i)
      rw [hmax]
      exact (le_of_eq h1).trans (le_of_le_of_eq h3 h2.symm)


end

section
variable (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)) (hres : ∀ i : (MaxContactCoverData.chosenCoverData T hv).idx, (MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i) = (MaxContactCoverData.chosenCoverData T hv).localIdeal i)
include hgood hres

theorem inStrictNormalCrossingPositionAt_coverMaxContactIdeal (x : ↥(MaxContactCoverData.coverTriple T hv).scheme) :
    InStrictNormalCrossingPositionAt (MaxContactCoverData.coverTriple T hv).structMap
      [MaxContactCoverData.coverMaxContactIdeal T hv] x := by
  obtain ⟨i, hxi⟩ := MaxContactOpenCover.exists_mem_coverTripleOpen T hv x
  have h1 := MaxContactOpenCover.restrictIdeal_coverTripleOpen T hv i (MaxContactCoverData.coverMaxContactIdeal T hv)
  rcases hgood.dichotomy i with ⟨_hdisj, htop⟩ | ⟨n, c, j, hlocal, _hmc⟩
  · have h2 : ((MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i)).comap
        (MaxContactOpenCover.coverPieceIso T hv i).inv = ⊤ := by
      rw [hres i, htop]
      exact Scheme.IdealSheafData.comap_top _
    have key := h1.trans h2
    have hsm : Smooth (MaxContactCoverData.coverTriple T hv).structMap := by
      have := MaxContactCoverData.smooth_coverMap_of_isAdmissible T hv
      have := hv.smooth
      exact (inferInstance : Smooth
        (MaxContactCoverData.coverMap T hv ≫ T.structMap))
    obtain ⟨U, m, hxU, hUle, -, ⟨ch⟩⟩ :=
      exists_etaleChart_le (MaxContactCoverData.coverTriple T hv).structMap x
        (MaxContactOpenCover.coverTripleOpen T hv i) hxi
    have keyU : restrictIdeal (MaxContactCoverData.coverMaxContactIdeal T hv) U = ⊤ := by
      apply restrictIdeal_eq_top_of_le <;> assumption
    refine inStrictNormalCrossingPositionAt_of_exists_etaleChart ⟨U, hxU, m, ch, fun _ => none, ?_, ?_, ?_⟩
    · intro r _hr s _hs t hrt _hst
      simp at hrt
    · intro r hr _hnone
      have hr1 : r < 1 := by simpa using hr
      have hr0 : r = 0 := by omega
      subst hr0
      exact keyU
    · intro r _hr t hrt
      simp at hrt
  · have h2 : ((MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i)).comap
        (MaxContactOpenCover.coverPieceIso T hv i).inv = (MaxContactOpenCover.coverEtaleChart T hv i c).coordIdeal {j} := by
      rw [hres i, hlocal, MaxContactOpenCover.coverEtaleChart_coordIdeal]
    have key := h1.trans h2
    refine inStrictNormalCrossingPositionAt_of_exists_etaleChart
      ⟨MaxContactOpenCover.coverTripleOpen T hv i, hxi, n, MaxContactOpenCover.coverEtaleChart T hv i c, fun _ => some j,
        ?_, ?_, ?_⟩
    · intro r hr s hs t _hrt _hst
      have hr1 : r < 1 := by simpa using hr
      have hs1 : s < 1 := by simpa using hs
      omega
    · intro r _hr hnone
      simp at hnone
    · intro r hr t hrt
      have hr1 : r < 1 := by simpa using hr
      have hr0 : r = 0 := by omega
      subst hr0
      obtain rfl : j = t := Option.some.inj hrt
      exact key

theorem inStrictNormalCrossingPosition_coverMaxContactIdeal (hsm : IsSmoothDivisor (MaxContactCoverData.coverTriple T hv).structMap
      (MaxContactCoverData.coverMaxContactIdeal T hv)) :
    InStrictNormalCrossingPosition (MaxContactCoverData.coverTriple T hv).structMap
      [MaxContactCoverData.coverMaxContactIdeal T hv] := by
  refine (inStrictNormalCrossingPosition_iff _ _).mpr
    ⟨?_, fun x => inStrictNormalCrossingPositionAt_coverMaxContactIdeal T hv hgood hres x⟩
  intro D hD
  have hD' : D = MaxContactCoverData.coverMaxContactIdeal T hv := List.mem_singleton.mp hD
  subst hD'
  exact hsm


end

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LowerDimReductionFieldBaseChange
section

open CategoryTheory.Limits

section
namespace FunctorialResolution.EmbeddedResolution

private theorem list_prod_map_comap_consolidated425 {X Y : Scheme.{u}} (q : X ⟶ Y) (Ls : List Y.IdealSheafData) :
    (Ls.map (fun A => A.comap q)).prod = Ls.prod.comap q := by
  induction Ls with
  | nil => simp
  | cons a L ih => simp [AlgebraicGeometry.Scheme.IdealSheafData.comap_mul, ih]

section
variable {X Y Z : Scheme.{u}}

private theorem list_map_comap_comp_consolidated425 (g : X ⟶ Y) (h : Y ⟶ Z)
    (l : List Z.IdealSheafData) :
    (l.map (fun A => A.comap h)).map (fun A => A.comap g) = l.map (fun A => A.comap (g ≫ h)) := by
  rw [List.map_map]
  refine List.map_congr_left fun A _ => ?_
  simp

private theorem isPullback_projectionToBase_of_index_eq_consolidated425 (b : SequenceOfBlowups X) {i j : ℕ}
    (h : i = j) {σ : Z ⟶ b.schemeAt i} {v : Z ⟶ Y} {g : Y ⟶ X}
    (hp : IsPullback σ v (b.projectionToBase i) g) :
    IsPullback (σ ≫ eqToHom (congrArg (fun n => b.schemeAt n) h)) v (b.projectionToBase j) g := by
  subst h
  simpa using hp


end

private theorem append_drop_eq_map_comap_consolidated425 {X Y : Scheme.{u}} (g : Y ⟶ X)
    (Es Bs : List X.IdealSheafData) (Et Bt : List Y.IdealSheafData) (keep : ℕ)
    (hE : Et = Es.map (fun A => A.comap g)) (hB : Bt = Bs.map (fun A => A.comap g)) :
    Et ++ Bt.drop keep = (Es ++ Bs.drop keep).map (fun A => A.comap g) := by
  subst hE
  subst hB
  rw [List.map_append, List.map_drop]

private theorem markedIdealWithBoundary_mk_eq_of_eq_consolidated425 {k : Type u} [Field k] {X : Scheme.{u}}
    (q : X ⟶ Spec (CommRingCat.of k)) {I I' : X.IdealSheafData} {m m' : ℕ}
    {E E' : List X.IdealSheafData} (hI : I = I') (hm : m = m') (hE : E = E') :
    MarkedIdealWithBoundary.mk k X q I m E = MarkedIdealWithBoundary.mk k X q I' m' E' := by
  subst hI
  subst hm
  subst hE
  rfl

private theorem isStrictPullback_of_morphism_eq_consolidated425 {X' X : Scheme.{u}} {g g' : X' ⟶ X} (h : g = g')
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (hd : IsStrictPullbackBlowupSeq g t s) :
    IsStrictPullbackBlowupSeq g' t s := by
  subst h
  exact hd

private theorem isAdmissible_of_eq_consolidated425 {T T' : MarkedIdealWithBoundary.{u}} (h : T = T') (hv : T'.IsAdmissible) :
    T.IsAdmissible := by
  subst h
  exact hv

private theorem pred_dim_of_eq_consolidated425 (P : ℕ → Prop) {T T' : MarkedIdealWithBoundary.{u}} (h : T = T')
    (hp : P T'.krullDimSucc) : P T.krullDimSucc := by
  subst h
  exact hp

section
variable {T T' : MarkedIdealWithBoundary.{u}} (h : T = T')
include h

private theorem isOrderBoundedByMult_of_eq_consolidated425 (ho : T'.IsOrderBoundedByMult) : T.IsOrderBoundedByMult := by
  subst h
  exact ho

private theorem lt_boundary_length_of_eq_consolidated425 {j : ℕ}
    (hj : j < T'.boundary.length) : j < T.boundary.length := by
  subst h
  exact hj

private theorem isBalanced_of_eq_consolidated425 (hft : LocallyOfFiniteType T.structMap)
    (hft' : LocallyOfFiniteType T'.structMap)
    (hd : T'.IsBalanced hft') : T.IsBalanced hft := by
  subst h
  exact hd


end

private theorem isStrictPullback_of_markedIdealWithBoundary_eq_consolidated425 (A : PrincipalizationAssignment.{u})
    {T T' : MarkedIdealWithBoundary.{u}} (h : T = T')
    {X : Scheme.{u}} {B : SequenceOfBlowups X} {φ : T.scheme ⟶ X} {φ' : T'.scheme ⟶ X} (hφ : HEq φ φ')
    (hd : IsStrictPullbackBlowupSeq φ (A T).toSequenceOfBlowups B) :
    IsStrictPullbackBlowupSeq φ' (A T').toSequenceOfBlowups B := by
  subst h
  cases hφ
  exact hd

private def castStrictPullbackBlowupSeq_consolidated425 {X' X : Scheme.{u}} {g : X' ⟶ X}
    {t t' : SequenceOfBlowups X'} {s s' : SequenceOfBlowups X} (ht : t = t') (hs : s = s')
    (D : StrictPullbackBlowupSeq g t s) : StrictPullbackBlowupSeq g t' s' := by
  subst ht
  subst hs
  exact D

private theorem isStrictPullback_of_markedBlowupSequenceData_eq_consolidated425 {k k' : Type u} [Field k] [Field k']
    {X X' : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {p' : X' ⟶ Spec (CommRingCat.of k')}
    {I : X.IdealSheafData} {I' : X'.IdealSheafData} {m m' : ℕ}
    {E : List X.IdealSheafData} {E' : List X'.IdealSheafData} {g : X' ⟶ X}
    {a b : MarkedBlowupSequenceData p I m E} {a' b' : MarkedBlowupSequenceData p' I' m' E'}
    (ha : a = b) (ha' : a' = b')
    (H : IsStrictPullbackBlowupSeq g a'.toMarkedSequenceOfBlowups.toSequenceOfBlowups a.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq g b'.toMarkedSequenceOfBlowups.toSequenceOfBlowups b.toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  subst ha
  subst ha'
  exact H

def DerivIdealSheafIterateCommBaseChange : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [CharZero k] [CharZero L] (f : k →+* L)
    (X Y : Scheme.{u}) (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of L))
    [Smooth pX] [LocallyOfFiniteType pX]
    [Smooth pY] [LocallyOfFiniteType pY]
    (q : Y ⟶ X),
    IsPullback q pY pX (specMapOfFieldHom k L f) →
      ∀ (r : ℕ) (I : X.IdealSheafData),
        derivIdealSheafIterate L pY r (I.comap q) = (derivIdealSheafIterate k pX r I).comap q

theorem balancedTunedSheaf_comap_of_isPullback (hderiv : DerivIdealSheafIterateCommBaseChange.{u})
    (k L : Type u) [Field k] [Field L] [CharZero k] [CharZero L] (f : k →+* L)
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of L))
    [Smooth pX] [LocallyOfFiniteType pX]
    [Smooth pY] [LocallyOfFiniteType pY]
    (q : Y ⟶ X) (hq : IsPullback q pY pX (specMapOfFieldHom k L f))
    (I : X.IdealSheafData) (m : ℕ) :
    balancedTunedSheaf L pY (I.comap q) m = (balancedTunedSheaf k pX I m).comap q := by
  rw [balancedTunedSheaf_eq, balancedTunedSheaf_eq, tunedSheaf_eq_iSup, tunedSheaf_eq_iSup, Scheme.IdealSheafData.comap_iSup]
  refine iSup_congr fun c => ?_
  rw [← list_prod_map_comap_consolidated425 q, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun r _ => ?_)
  simp [Function.comp_apply, hderiv k L f X Y pX pY q hq r I,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_pow]

namespace MarkedBlowupSequenceData

theorem isStrictPullbackBlowupSeq_append_of_field {k k' : Type u} [Field k] [Field k']
    {X X' : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {p' : X' ⟶ Spec (CommRingCat.of k')}
    {I : X.IdealSheafData} {I' : X'.IdealSheafData} {m m' : ℕ}
    {E : List X.IdealSheafData} {E' : List X'.IdealSheafData} (g : X' ⟶ X)
    (s : MarkedBlowupSequenceData p I m E)
    (u : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (s' : MarkedBlowupSequenceData p' I' m' E')
    (u' : MarkedBlowupSequenceData (s'.proj s'.length ≫ p') (s'.ideal s'.length) m'
      (s'.boundary s'.length))
    (hinv : ComapIsoInvariance.{u})
    (D : StrictPullbackBlowupSeq g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap u'.toMarkedSequenceOfBlowups.toSequenceOfBlowups u.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq g ((s'.append u' hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups)
      ((s.append u hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups) :=
  FunctorialResolution.EmbeddedResolution.isStrictPullbackBlowupSeq_append (g := g) s.toBlowupSequenceData u.toBlowupSequenceData s'.toBlowupSequenceData
    u'.toBlowupSequenceData D D'

end MarkedBlowupSequenceData

namespace LowerDimReductionPullback

variable (S : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] (f : S.base →+* L)
  (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
  (t : MarkedBlowupSequenceData (S.baseChange L f).structMap (S.baseChange L f).ideal
      (S.baseChange L f).mult (S.baseChange L f).boundary)

theorem length_eq_of_strictPullbackBlowupSeq
    (D : StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    t.length = s.length := by
  have h : t.toMarkedSequenceOfBlowups.length = s.toMarkedSequenceOfBlowups.length := D.length_eq
  rw [MarkedBlowupSequenceData.toMarkedSequence_length, MarkedBlowupSequenceData.toMarkedSequence_length] at h
  exact h

noncomputable def baseChangeMapAtLength
    (D : StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    t.obj t.length ⟶ s.obj s.length :=
  D.lastMap

@[reducible] noncomputable def comapBoundaryBaseChange
    (D : StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (Ls : List (s.obj s.length).IdealSheafData) : List (t.obj t.length).IdealSheafData :=
  Ls.map (fun A => A.comap (baseChangeMapAtLength S L f s t D))

theorem nonempty_strictPullbackSeq_appendLowerDimReduction_baseChange
    (D : StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    [CharZero L]
    [Flat (pullback.fst S.structMap (specMapOfFieldHom S.base L f))]
    (hderiv : DerivIdealSheafIterateCommBaseChange.{u}) (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u}) (Bp : PrincipalizationAssignment.{u}) (j : ℕ)
    (hspec : IsBoundaryDivisorReduction P j (A j) Bp)
    (T T' : MarkedIdealWithBoundary.{u})
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)
    (hftS : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hftT : LocallyOfFiniteType
      (t.proj t.length ≫ (S.baseChange L f).structMap))
    (hV : S.IsAdmissible) (hm : 1 ≤ S.mult)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hNs : ∀ i ≤ s.length, IsLocallyNoetherian (s.obj i))
    (hV' : (S.baseChange L f).IsAdmissible)
    (hO' : ∀ x : ↥(S.baseChange L f).scheme,
      orderAt (S.baseChange L f).ideal x ≤ ((S.baseChange L f).mult : ℕ∞))
    (hNt : ∀ i ≤ t.length, IsLocallyNoetherian (t.obj i))
    (hdim : (MaxContactCoverData.derivedTriple S s hftS extra keep).krullDimSucc ≤ T.krullDimSucc)
    (hP : P (MaxContactCoverData.derivedTriple S s hftS extra keep).krullDimSucc)
    (hVc : (MaxContactCoverData.derivedTriple S s hftS extra keep).IsAdmissible)
    (hj : j < (extra ++ (s.boundary s.length).drop keep).length)
    (hsep : ∀ Dv ∈ (s.boundary s.length).take keep,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (Dv.support : Set ↥(s.obj s.length)) = ∅)
    (hdim' : (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep).krullDimSucc ≤ T'.krullDimSucc)
    (hP' : P (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep).krullDimSucc)
    (hVc' : (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep).IsAdmissible)
    (hj' : j < (@List.append (t.obj t.length).IdealSheafData (comapBoundaryBaseChange S L f s t D extra)
      ((t.boundary t.length).drop keep)).length)
    (hsep' : ∀ Dv ∈ (t.boundary t.length).take keep,
      orderAtLeastLocus (t.ideal t.length) (S.baseChange L f).mult ∩
        (Dv.support : Set ↥(t.obj t.length)) = ∅)
    (hVb : ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).IsAdmissible)
    (hPb : P ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).krullDimSucc)
    (hOb : ∀ x : ↥((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).scheme,
      orderAt ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).ideal x ≤
        ((MaxContactCoverData.derivedTriple S s hftS extra keep).mult : ℕ∞))
    (hDb : ∀ hft : LocallyOfFiniteType
        ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).structMap,
      ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).IsBalanced hft) :
    Nonempty (StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      (MaxContactReduction.appendLowerDimReduction hinv T' (fun S' _ i => A i S') (S.baseChange L f) t
        (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap)
        keep j).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') S s extra keep
        j).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  classical
  have hlen : t.length = s.length := length_eq_of_strictPullbackBlowupSeq S L f s t D
  have hm' : 1 ≤ (S.baseChange L f).mult := hm
  have hbe : comapBoundaryBaseChange S L f s t D extra = extra.map (fun A => A.comap D.lastMap) := rfl
  obtain ⟨hmk1, heq1, -⟩ :=
    LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A Bp j hspec (fun S' _ i => A i S')
      (fun _ _ _ => rfl) S hV hm hO s extra keep hftS hdim hP hVc hj hsep
  obtain ⟨hmk2, heq2, -⟩ :=
    LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T' P A Bp j hspec (fun S' _ i => A i S')
      (fun _ _ _ => rfl) (S.baseChange L f) hV' hm' hO' t (comapBoundaryBaseChange S L f s t D extra) keep
      hftT hdim' hP' hVc' hj' hsep'
  have hcz : CharZero S.base := hV.charZero
  have hsmA : Smooth
      ((s.proj s.length ≫ S.structMap : s.obj s.length ⟶ Spec (CommRingCat.of S.base))) :=
    hVc.smooth
  have hsmB : Smooth
      ((t.proj t.length ≫ (S.baseChange L f).structMap :
        t.obj t.length ⟶ Spec (CommRingCat.of L))) :=
    hVc'.smooth
  have hftA : LocallyOfFiniteType
      ((s.proj s.length ≫ S.structMap : s.obj s.length ⟶ Spec (CommRingCat.of S.base))) :=
    hftS
  have hftB : LocallyOfFiniteType
      ((t.proj t.length ≫ (S.baseChange L f).structMap :
        t.obj t.length ⟶ Spec (CommRingCat.of L))) :=
    hftT
  have hbase : IsPullback (D.comp t.length le_rfl)
      (t.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase t.length)
      (s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase t.length)
      (pullback.fst S.structMap (specMapOfFieldHom S.base L f)) :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism
      (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups t.length D.comp D.comp_zero D.pullback
      t.length le_rfl
  have hbase2 := isPullback_projectionToBase_of_index_eq_consolidated425 s.toMarkedSequenceOfBlowups.toSequenceOfBlowups hlen hbase
  have hbase3 := hbase2.paste_vert
    (IsPullback.of_hasPullback S.structMap (specMapOfFieldHom S.base L f))
  have e1 : t.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase t.length = t.proj t.length :=
    MarkedBlowupSequenceData.toMarkedSequence_projectionToBase t t.length
  have e2 : s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase s.length = s.proj s.length :=
    MarkedBlowupSequenceData.toMarkedSequence_projectionToBase s s.length
  have hsq : IsPullback D.lastMap (t.proj t.length ≫ (S.baseChange L f).structMap)
      (s.proj s.length ≫ S.structMap) (specMapOfFieldHom S.base L f) := by
    rw [← e1, ← e2]
    exact hbase3
  have hsq1 : IsPullback D.lastMap (t.proj t.length ≫ (S.baseChange L f).structMap)
      (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap
      (specMapOfFieldHom (MaxContactCoverData.derivedTriple S s hftS extra keep).base L f) := hsq
  obtain ⟨ι, hfst, hsnd⟩ :
      ∃ e : t.obj t.length ≅ pullback (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap
          (specMapOfFieldHom (MaxContactCoverData.derivedTriple S s hftS extra keep).base L f),
        (e.hom ≫ pullback.fst (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap
            (specMapOfFieldHom (MaxContactCoverData.derivedTriple S s hftS extra keep).base L f) = D.lastMap) ∧
          (e.hom ≫ pullback.snd (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap
              (specMapOfFieldHom (MaxContactCoverData.derivedTriple S s hftS extra keep).base L f)
            = t.proj t.length ≫ (S.baseChange L f).structMap) :=
    ⟨hsq1.isoPullback, hsq1.isoPullback_hom_fst, hsq1.isoPullback_hom_snd⟩
  have hisoι : IsIso ι.hom := inferInstance
  have hsmι : Smooth ι.hom := inferInstance
  have hsurjι : AlgebraicGeometry.Surjective ι.hom := inferInstance
  have hdiv := (MarkedBlowupSequenceData.isMarked_toBlowupSequenceData s).divisible
  have hpi := MarkedBlowupSequenceData.ideal_eq_comap_controlledTransform (d := s.toBlowupSequenceData) (I := S.ideal) (m := S.mult)
    (E := S.boundary) (g := pullback.fst S.structMap (specMapOfFieldHom S.base L f)) t D hdiv
    t.length le_rfl
  have hpb := MarkedBlowupSequenceData.boundary_eq_comap_strictPullbackComparisonMap (d := s.toBlowupSequenceData) (I := S.ideal) (m := S.mult)
    (E := S.boundary) (g := pullback.fst S.structMap (specMapOfFieldHom S.base L f)) t D hNs hNt
    t.length le_rfl
  have hpm : MarkedBlowupSequenceData.strictPullbackComparisonMap (q := (S.baseChange L f).structMap)
      (g := pullback.fst S.structMap (specMapOfFieldHom S.base L f)) (I := S.ideal) (m := S.mult)
      (E := S.boundary) (d := s.toBlowupSequenceData) t D t.length le_rfl ≫
        eqToHom (congrArg (fun n => s.obj n) hlen) = D.lastMap := rfl
  have hIdealLast : t.ideal t.length = (s.ideal s.length).comap D.lastMap := by
    refine hpi.trans ?_
    rw [MarkedBlowupSequenceData.toBlowupSequenceData_controlledTransform_eq s t.length (le_of_eq hlen),
      MarkedBlowupSequenceData.ideal_congr_index s hlen, ← Scheme.IdealSheafData.comap_comp]
    exact congrArg (fun q => (s.ideal s.length).comap q) hpm
  have hBoundaryLast : t.boundary t.length
      = (s.boundary s.length).map (fun A => A.comap D.lastMap) := by
    refine hpb.trans ?_
    rw [MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq_boundary_of_le s t.length (le_of_eq hlen),
      MarkedBlowupSequenceData.boundary_congr_index s hlen, List.map_map]
    refine List.map_congr_left fun A _ => ?_
    simp only [Function.comp_apply, ← Scheme.IdealSheafData.comap_comp]
    exact congrArg (fun q => A.comap q) hpm
  have htuned := balancedTunedSheaf_comap_of_isPullback hderiv S.base L f
    (s.proj s.length ≫ S.structMap) (t.proj t.length ≫ (S.baseChange L f).structMap)
    D.lastMap hsq (s.ideal s.length) S.mult
  have hid : (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
        (comapBoundaryBaseChange S L f s t D extra) keep).ideal
      = ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).ideal.comap ι.hom := by
    have hA : ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).ideal.comap ι.hom
        = (LowerDimReductionPullback.tunedIdealAtLength S s hftS).comap D.lastMap := by
      refine Eq.trans (congrArg (fun I => I.comap ι.hom)
        (MarkedIdealWithBoundary.baseChange_ideal (MaxContactCoverData.derivedTriple S s hftS extra keep) L f)) ?_
      refine Eq.trans (Scheme.IdealSheafData.comap_comp _ _ _).symm ?_
      refine Eq.trans (congrArg
        (fun m => (MaxContactCoverData.derivedTriple S s hftS extra keep).ideal.comap m) hfst) ?_
      exact congrArg (fun I => I.comap D.lastMap)
        (LowerDimReductionPullback.ideal_derivedTriple S s hftS extra keep)
    have hB : (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
          (comapBoundaryBaseChange S L f s t D extra) keep).ideal
        = (LowerDimReductionPullback.tunedIdealAtLength S s hftS).comap D.lastMap := by
      rw [LowerDimReductionPullback.ideal_derivedTriple (S.baseChange L f) t hftT (comapBoundaryBaseChange S L f s t D extra) keep,
        LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf (S.baseChange L f) t hftT, LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf S s hftS,
        hIdealLast]
      exact htuned
    exact hB.trans hA.symm
  have hbd : (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
        (comapBoundaryBaseChange S L f s t D extra) keep).boundary
      = (((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).boundary).map
          (fun Dv => Dv.comap ι.hom) := by
    have r1 : (((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).boundary).map
          (fun Dv => Dv.comap ι.hom)
        = (extra ++ (s.boundary s.length).drop keep).map (fun A => A.comap D.lastMap) := by
      refine Eq.trans (congrArg (fun l => l.map (fun Dv => Dv.comap ι.hom))
        (MarkedIdealWithBoundary.baseChange_boundary
          (MaxContactCoverData.derivedTriple S s hftS extra keep) L f)) ?_
      refine Eq.trans (list_map_comap_comp_consolidated425 ι.hom
        (pullback.fst (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap
          (specMapOfFieldHom (MaxContactCoverData.derivedTriple S s hftS extra keep).base L f))
        (MaxContactCoverData.derivedTriple S s hftS extra keep).boundary) ?_
      refine Eq.trans (congrArg (fun m =>
        (MaxContactCoverData.derivedTriple S s hftS extra keep).boundary.map
          (fun A => A.comap m)) hfst) ?_
      exact congrArg (fun l => l.map (fun A => A.comap D.lastMap))
        (MaxContactCoverData.derivedTriple_boundary S s hftS extra keep)
    have r2 : (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
          (comapBoundaryBaseChange S L f s t D extra) keep).boundary
        = (extra ++ (s.boundary s.length).drop keep).map (fun A => A.comap D.lastMap) := by
      refine Eq.trans (MaxContactCoverData.derivedTriple_boundary (S.baseChange L f) t hftT
        (comapBoundaryBaseChange S L f s t D extra) keep) ?_
      exact append_drop_eq_map_comap_consolidated425 D.lastMap extra (s.boundary s.length)
        (comapBoundaryBaseChange S L f s t D extra) (t.boundary t.length) keep hbe hBoundaryLast
    exact r2.trans r1.symm
  have hTriple : ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).pullbackAlong
        (t.obj t.length)
        (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
          (comapBoundaryBaseChange S L f s t D extra) keep).structMap ι.hom
      = MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT (comapBoundaryBaseChange S L f s t D extra) keep :=
    markedIdealWithBoundary_mk_eq_of_eq_consolidated425 _ hid.symm rfl hbd.symm
  have hft1 : LocallyOfFiniteType
      (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap := hVc.locallyOfFiniteType
  have hO1 : (MaxContactCoverData.derivedTriple S s hftS extra keep).IsOrderBoundedByMult :=
    LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hftS extra keep hVc
  have hD1 : (MaxContactCoverData.derivedTriple S s hftS extra keep).IsBalanced hft1 :=
    LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hm hO s hftS extra keep hVc
  have hj1 : j < (MaxContactCoverData.derivedTriple S s hftS extra keep).boundary.length :=
    lt_of_lt_of_eq hj (congrArg List.length
      (MaxContactCoverData.derivedTriple_boundary S s hftS extra keep)).symm
  have hO1b : ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).IsOrderBoundedByMult :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff _).mpr hOb
  have hlenb : ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).boundary.length
      = (MaxContactCoverData.derivedTriple S s hftS extra keep).boundary.length :=
    (congrArg List.length
      (MarkedIdealWithBoundary.baseChange_boundary (MaxContactCoverData.derivedTriple S s hftS extra keep) L f)).trans
      (List.length_map _)
  have hj1b :
      j < ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).boundary.length :=
    lt_of_lt_of_eq hj1 hlenb.symm
  have hbc := hspec.isStrictPullbackBlowupSeq_baseChange (MaxContactCoverData.derivedTriple S s hftS extra keep)
    hVc hP hO1 hD1 hj1 L f hVb hPb hO1b (hDb hVb.locallyOfFiniteType) hj1b
  have hO2 : (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep).IsOrderBoundedByMult :=
    LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar (S.baseChange L f) hV' hm' hO' t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep hVc'
  have hD2b : (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep).IsBalanced hVc'.locallyOfFiniteType :=
    LowerDimReductionPullback.isBalanced_derivedTriple hstar (S.baseChange L f) hV' hm' hO' t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep hVc'
  have hj2 : j < (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep).boundary.length :=
    lt_of_lt_of_eq hj' (congrArg List.length
      (MaxContactCoverData.derivedTriple_boundary (S.baseChange L f) t hftT
        (comapBoundaryBaseChange S L f s t D extra) keep)).symm
  have hStrictPullback := @IsBoundaryDivisorReduction.isStrictPullbackBlowupSeq_of_smooth_surjective P j (A j) Bp hspec
    ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f) hVb hPb hO1b
    (hDb hVb.locallyOfFiniteType) hj1b (t.obj t.length)
    (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep).structMap
    ι.hom hsmι hsurjι hsnd
    (isAdmissible_of_eq_consolidated425 hTriple hVc') (pred_dim_of_eq_consolidated425 P hTriple hP')
    (isOrderBoundedByMult_of_eq_consolidated425 hTriple hO2)
    (isBalanced_of_eq_consolidated425 hTriple _ _ hD2b)
    (lt_boundary_length_of_eq_consolidated425 hTriple hj2)
  have hsmT : IsStrictPullbackBlowupSeq ι.hom
      (A j (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
        (comapBoundaryBaseChange S L f s t D extra) keep)).toSequenceOfBlowups
      (A j ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f)).toSequenceOfBlowups :=
    isStrictPullback_of_markedIdealWithBoundary_eq_consolidated425 (A j) hTriple (HEq.refl ι.hom) hStrictPullback
  have hcomp := isStrictPullback_of_morphism_eq_consolidated425 hfst (hsmT.comp hbc)
  have hD'0 := (hcomp.of_isomorphic_pullback (BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _).symm).of_isomorphic_base
    (BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _).symm
  have hE1 := BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups
    (BlowupSequenceData.ofSequenceOfBlowups (A j (MaxContactCoverData.derivedTriple S s hftS extra keep)).toSequenceOfBlowups)
    (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult (s.boundary s.length) hmk1
  have hE2 := BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups
    (BlowupSequenceData.ofSequenceOfBlowups (A j (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep)).toSequenceOfBlowups)
    (t.proj t.length ≫ (S.baseChange L f).structMap) (t.ideal t.length) (S.baseChange L f).mult
    (t.boundary t.length) hmk2
  have hD2 := castStrictPullbackBlowupSeq_consolidated425 hE2.symm hE1.symm hD'0.toStrictPullbackBlowupSeq
  have main := isStrictPullback_of_markedBlowupSequenceData_eq_consolidated425 heq1.symm heq2.symm
    (MarkedBlowupSequenceData.isStrictPullbackBlowupSeq_append_of_field
      (pullback.fst S.structMap (specMapOfFieldHom S.base L f)) s _ t _ hinv D hD2)
  exact ⟨main.toStrictPullbackBlowupSeq⟩

end LowerDimReductionPullback

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverDescent
section


section
namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactFunctoriality

variable (hinv : ComapIsoInvariance) (A : ℕ → PrincipalizationAssignment.{u})
variable {P : ℕ → Prop}

section
variable (T : MarkedIdealWithBoundary.{u})

theorem balancedTunedIdeal_eq_of_mult_eq_one (hv : T.IsAdmissible) (hm : T.mult = 1) :
    MaxContactCoverData.balancedTunedIdeal T hv = T.ideal := by
  have := hv.charZero
  have := hv.locallyOfFiniteType
  have := hv.smooth
  simp only [MaxContactCoverData.balancedTunedIdeal, hm, FunctorialResolution.EmbeddedResolution.balancedTunedSheaf_eq, FunctorialResolution.EmbeddedResolution.tuningExponent_one,
    FunctorialResolution.EmbeddedResolution.tunedSheaf_one_one]

theorem coverMap_flat (h : OrderReductionHypotheses P T) :
    Flat (MaxContactCoverData.coverMap T h.valid) :=
  MaxContactCoverData.flat_coverMap_of_isAdmissible T h.valid


end

section
variable (htune : TunedSheafProperties.{u}) (T : MarkedIdealWithBoundary.{u})
include htune

private theorem orderAt_balancedTunedIdeal_le_tunedMult_of_nonempty_consolidated422 (hv : T.IsAdmissible)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (hne : (orderAtLeastLocus T.ideal T.mult).Nonempty) :
    ∀ x : ↥T.scheme,
      orderAt (MaxContactCoverData.balancedTunedIdeal T hv) x ≤ ((MaxContactCoverData.tunedMult T : ℕ) : ℕ∞) := by
  have := hv.charZero
  have := hv.smooth
  have := hv.locallyOfFiniteType
  have hmax : MaxOrderEq T.ideal T.mult :=
    ⟨(orderLE_iff T.ideal T.mult).mpr hord, hne⟩
  have hkey := htune.coSupport_tunedSheaf_eq_and_orderLE.orderLE T.base T.scheme T.structMap
    T.ideal T.mult hv.one_le_mult hmax (tuningExponent T.mult) (one_le_tuningExponent T.mult)
  have he0 : MaxContactCoverData.balancedTunedIdeal T hv = balancedTunedSheaf T.base T.structMap T.ideal T.mult := rfl
  have he : MaxContactCoverData.balancedTunedIdeal T hv
      = tunedSheaf T.base T.structMap T.ideal T.mult (tuningExponent T.mult) := by
    rw [he0, balancedTunedSheaf_eq]
  have hm : MaxContactCoverData.tunedMult T = tuningExponent T.mult := rfl
  intro x
  rw [he, hm]
  exact (orderLE_iff _ _).mp hkey x

theorem coverMap_surjective (h : OrderReductionHypotheses P T) :
    AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap T h.valid) :=
  MaxContactCoverData.surjective_coverMap T h.valid
    (MaxContactOpenCover.exists_isMaxContactCover T h.valid
      (orderAt_balancedTunedIdeal_le_tunedMult_of_nonempty_consolidated422 htune T h.valid h.orderLE h.coSupport_nonempty))


end

section
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

theorem IsLocalIsomorphism.comp_isIso (g : Y ⟶ Z)
    [CategoryTheory.IsIso g] (hf : IsLocalIsomorphism f) :
    IsLocalIsomorphism (f ≫ g) := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hf x
  have := hU
  refine ⟨U, hxU, ?_⟩
  rw [← Category.assoc]
  infer_instance

theorem IsLocalIsomorphism.isIso_comp [CategoryTheory.IsIso f]
    (g : Y ⟶ Z) (hg : IsLocalIsomorphism g) :
    IsLocalIsomorphism (f ≫ g) := by
  have hsurj : Function.Surjective ⇑f.base := by
    intro y
    refine ⟨(CategoryTheory.inv f).base y, ?_⟩
    exact congrArg (fun m : Y ⟶ Y => m.base y) (CategoryTheory.IsIso.inv_hom_id f)
  intro x
  obtain ⟨U, hxU, hU⟩ := hg (f.base x)
  refine ⟨f ⁻¹ᵁ U, hxU, ?_⟩
  have : IsOpenImmersion f := inferInstance
  have hrange : Set.range ((f ⁻¹ᵁ U).ι ≫ f).base = Set.range U.ι.base := by
    have h1 : Set.range ⇑((f ⁻¹ᵁ U).ι ≫ f).base
        = Set.range (⇑f.base ∘ ⇑(f ⁻¹ᵁ U).ι.base) := rfl
    rw [h1, Set.range_comp]
    simp only [AlgebraicGeometry.Scheme.Opens.range_ι]
    exact Set.image_preimage_eq _ hsurj
  obtain ⟨φ, hfac⟩ : ∃ φ : (f ⁻¹ᵁ U).toScheme ≅ U.toScheme,
      φ.hom ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f :=
    ⟨AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq ((f ⁻¹ᵁ U).ι ≫ f) U.ι hrange,
      AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange⟩
  have heq : (f ⁻¹ᵁ U).ι ≫ f ≫ g = φ.hom ≫ U.ι ≫ g := by
    rw [← Category.assoc, ← hfac, Category.assoc]
  rw [heq]
  have := hU
  infer_instance


end

private theorem isLocalIsomorphism_of_eq_consolidated422 {W' W : Scheme.{u}} {f f' : W' ⟶ W}
    (h : f = f') (hf : IsLocalIsomorphism f') : IsLocalIsomorphism f := by
  subst h
  exact hf

theorem isLocalIsomorphism_map_of_isLocalIsomorphism {X' X : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsLocalIsomorphism g) {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (D : StrictPullbackBlowupSeq g t s) (i : ℕ) (hi : i ≤ t.length) :
    IsLocalIsomorphism (D.comp i hi) := by
  revert hi
  induction i with
  | zero =>
    intro hi
    exact isLocalIsomorphism_of_eq_consolidated422 D.map_zero_eq
      (IsLocalIsomorphism.isIso_comp t.isoZero.hom (g ≫ s.isoZero.inv)
        (IsLocalIsomorphism.comp_isIso g s.isoZero.inv hg))
  | succ n ih =>
    intro hi
    have hn : n < t.length := hi
    exact MaxContactOpenCover.isLocalIsomorphism_fst_of_isPullback (D.pullback n hn) (ih hn.le)

theorem isLocalIsomorphism_map_coverBlowupSequence (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T)
    (d : BlowupSequenceData T.scheme)
    (D : StrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
      (coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (i : ℕ) (hi : i ≤ (coverBlowupSequence hinv A T h.valid).length) :
    IsLocalIsomorphism
      (D.comp i ((coverBlowupSequence hinv A T h.valid).le_toSequenceOfBlowups_length hi)) :=
  isLocalIsomorphism_map_of_isLocalIsomorphism
    (MaxContactOpenCover.isLocalIsomorphism_coverMap T h.valid) D i
    ((coverBlowupSequence hinv A T h.valid).le_toSequenceOfBlowups_length hi)

theorem isNoetherian_blowupSequenceData_schemeAt (X : Scheme.{u}) [IsNoetherian X]
    (d : BlowupSequenceData X) (i : ℕ) (hi : i ≤ d.length) :
    IsNoetherian (d.obj i) := by
  have hi' : i ≤ d.toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length]
    exact hi
  have h : IsNoetherian (d.toSequenceOfBlowups.schemeAt i) :=
    isNoetherian_schemeAt d.toSequenceOfBlowups i hi'
  rwa [BlowupSequenceData.toSequenceOfBlowups_schemeAt] at h

section
variable (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u}) (T : MarkedIdealWithBoundary.{u})
include hstar

theorem isLocallyNoetherian_schemeAt_coverBlowupSequence (h : OrderReductionHypotheses P T) (d : BlowupSequenceData T.scheme)
    (_hd : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
      (coverBlowupSequence hinv A T h.valid).toSequenceOfBlowups d.toSequenceOfBlowups) :
    (∀ i ≤ d.length, IsLocallyNoetherian (d.obj i)) ∧
      ∀ i ≤ (coverBlowupSequence hinv A T h.valid).length,
        IsLocallyNoetherian ((coverBlowupSequence hinv A T h.valid).obj i) := by
  have := h.valid.locallyOfFiniteType
  have := h.valid.quasiCompact
  have : IsNoetherianRing ↑(CommRingCat.of T.base) := inferInstanceAs (IsNoetherianRing T.base)
  have : IsNoetherian (Spec (CommRingCat.of T.base)) := inferInstance
  have : IsNoetherian T.scheme :=
    isNoetherian_of_locallyOfFiniteType T.structMap
  have hgood := MaxContactCoverData.isMaxContactCover_chosenCoverData T h.valid
    (hstar.exists_goodCover T h.valid h.orderLE)
  have hvc : (MaxContactCoverData.coverTriple T h.valid).IsAdmissible :=
    hstar.coverTriple_valid T h.valid h.orderLE hgood
  have := hvc.locallyOfFiniteType
  have := hvc.quasiCompact
  have : IsNoetherianRing ↑(CommRingCat.of (MaxContactCoverData.coverTriple T h.valid).base) :=
    inferInstanceAs (IsNoetherianRing (MaxContactCoverData.coverTriple T h.valid).base)
  have : IsNoetherian
      (Spec (CommRingCat.of (MaxContactCoverData.coverTriple T h.valid).base)) := inferInstance
  have : IsNoetherian (MaxContactCoverData.coverTriple T h.valid).scheme :=
    isNoetherian_of_locallyOfFiniteType (MaxContactCoverData.coverTriple T h.valid).structMap
  constructor
  · intro i hi
    have := isNoetherian_blowupSequenceData_schemeAt T.scheme d i hi
    infer_instance
  · intro i hi
    have := isNoetherian_blowupSequenceData_schemeAt (MaxContactCoverData.coverTriple T h.valid).scheme
      (coverBlowupSequence hinv A T h.valid).toBlowupSequenceData i hi
    infer_instance

theorem orderAt_sequenceOfBlowups_ideal_le_mult (hv : T.IsAdmissible) (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.length) (x : ↥(s.schemeAt i)) :
    orderAt (s.ideal i) x ≤ (T.mult : ℕ∞) :=
  hstar.orderAt_level_le T hv hord s i hi x


end

private theorem imageIdealSheaf_inv_eq_comap_consolidated422 {X Y : Scheme.{u}} (φ : X ≅ Y)
    (J : Y.IdealSheafData) :
    imageIdealSheaf φ.inv J = J.comap φ.hom := by
  have h1 : (imageIdealSheaf φ.inv J).comap φ.inv = J :=
    Blowup.comap_map_of_isClosedImmersion φ.inv J
  have h2 : ((imageIdealSheaf φ.inv J).comap φ.inv).comap φ.hom = imageIdealSheaf φ.inv J := by
    rw [← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id, Scheme.IdealSheafData.comap_id]
  calc imageIdealSheaf φ.inv J = ((imageIdealSheaf φ.inv J).comap φ.inv).comap φ.hom := h2.symm
    _ = J.comap φ.hom := by rw [h1]

theorem isAdmissible_and_dim_eq_withSchemeIdealBoundary_ker (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (e : Y ⟶ T.scheme)
    [IsClosedImmersion e] (hq : e ≫ T.structMap = q)
    (J : Y.IdealSheafData) (hJ : (T.withSchemeIdealBoundary Y q J []).IsAdmissible)
    (ε : Y ⟶ (Scheme.Hom.ker e).subscheme)
    (hε : ε ≫ (Scheme.Hom.ker e).subschemeι = e) :
    (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap) (imageIdealSheaf ε J) []).IsAdmissible ∧
      (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
          ((Scheme.Hom.ker e).subschemeι ≫ T.structMap) (imageIdealSheaf ε J) []).krullDimSucc
        = (T.withSchemeIdealBoundary Y q J []).krullDimSucc := by
  have : CategoryTheory.Mono ((Scheme.Hom.ker e).subschemeι) := inferInstance
  have hεi : ε = (kerSubschemeIso e).inv := by
    apply (CategoryTheory.cancel_mono ((Scheme.Hom.ker e).subschemeι)).mp
    rw [hε, kerSubschemeIso_inv_comp]
  subst hεi
  have hsmq : Smooth q := by
    have h := hJ.smooth
    rwa [MarkedIdealWithBoundary.withSchemeIdealBoundary_structureMorphism] at h
  have hftq : LocallyOfFiniteType q := by
    have h := hJ.locallyOfFiniteType
    rwa [MarkedIdealWithBoundary.withSchemeIdealBoundary_structureMorphism] at h
  have hqcq : QuasiCompact q := by
    have h := hJ.quasiCompact
    rwa [MarkedIdealWithBoundary.withSchemeIdealBoundary_structureMorphism] at h
  have hnzJ : NonzeroOnComponents J := by
    have h := hJ.nonzeroOnComponents
    rwa [MarkedIdealWithBoundary.withSchemeIdealBoundary_ideal] at h
  have hkey : (Scheme.Hom.ker e).subschemeι ≫ T.structMap
      = (kerSubschemeIso e).hom ≫ q := by
    rw [← hq, ← Category.assoc, kerSubschemeIso_hom_comp]
  have hsm' : Smooth
      ((Scheme.Hom.ker e).subschemeι ≫ T.structMap) := by
    rw [hkey]
    infer_instance
  have hft' : LocallyOfFiniteType
      ((Scheme.Hom.ker e).subschemeι ≫ T.structMap) := by
    rw [hkey]
    infer_instance
  have hqc' : QuasiCompact
      ((Scheme.Hom.ker e).subschemeι ≫ T.structMap) := by
    rw [hkey]
    infer_instance
  have hnz : NonzeroOnComponents (imageIdealSheaf (kerSubschemeIso e).inv J) := by
    rw [imageIdealSheaf_inv_eq_comap_consolidated422 (kerSubschemeIso e) J]
    exact nonzeroOnComponents_comap_iso_hom (kerSubschemeIso e) J hnzJ
  have hdim : krullDimSucc ((Scheme.Hom.ker e).subscheme) = krullDimSucc Y := by
    rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim,
      topologicalKrullDim_eq_of_homeomorph (Scheme.homeoOfIso (kerSubschemeIso e))]
  exact ⟨⟨hv.charZero, hft', hnz, hv.one_le_mult, hqc', hsm',
    inStrictNormalCrossingPosition_nil ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)⟩, hdim⟩

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparationBaseChange
section


section
namespace FunctorialResolution.EmbeddedResolution

theorem maxContactIdeal_comap (k : Type u) [Field k] {P Y : Scheme.{u}}
    (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p]
    [LocallyOfFiniteType p]
    (g : Y ⟶ P) [Smooth g]
    [LocallyOfFiniteType (g ≫ p)]
    (A : P.IdealSheafData) (μ : ℕ) :
    maxContactIdeal k (g ≫ p) (A.comap g) μ = (maxContactIdeal k p A μ).comap g := by
  unfold maxContactIdeal
  exact derivIdealSheafIterate_comap k p g (μ - 1) A

namespace BoundarySeparationBaseChange

def IsMaxContactInvariantBalancedTuned : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p]
    (A : P.IdealSheafData) (μ : ℕ), 1 ≤ μ → MaxOrderEq A μ →
      IsMaxContactInvariant k p (balancedTunedSheaf k p A μ) (tuningExponent μ)

def MaxContactHypersurfaceSmoothPullback : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p]
    (Y : Scheme.{u}) (g : Y ⟶ P) [Smooth g]
    [LocallyOfFiniteType (g ≫ p)]
    (A : P.IdealSheafData) (μ : ℕ), 1 ≤ μ →
      ∀ H : P.IdealSheafData, IsMaxContactHypersurface k p A μ H →
        IsMaxContactHypersurface k (g ≫ p) (A.comap g) μ (H.comap g)

theorem isLocallyNoetherian_schemeAt (_hMaxContact : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) :
    ∀ i ≤ s.length, IsLocallyNoetherian (s.obj i) := by
  intro i hi
  have hnoeth : IsNoetherian (s.toMarkedSequenceOfBlowups.schemeAt i) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s.toMarkedSequenceOfBlowups i
      (s.le_toSequenceOfBlowups_length hi)
  show IsLocallyNoetherian (s.toMarkedSequenceOfBlowups.schemeAt i)
  infer_instance

theorem isAdmissible_derivedTriple_nil (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap)) :
    (MaxContactCoverData.derivedTriple S s hft ([] : List (s.obj s.length).IdealSheafData) 0).IsAdmissible := by
  refine BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar S hV s hft [] 0 ?_
  have hlev : (S.transformAt s.toMarkedSequenceOfBlowups s.length).IsAdmissible :=
    MarkedIdealWithBoundary.IsAdmissible.transformAt effectiveCartierSupportContainsNoComponent hV s.toMarkedSequenceOfBlowups s.length
      (s.le_toSequenceOfBlowups_length (le_refl s.length))
  have h := hlev.snc
  rw [MarkedIdealWithBoundary.transformAt_structureMorphism, MarkedIdealWithBoundary.transformAt_boundary,
    MarkedSequenceOfBlowups.projectionToSpec_eq, MarkedBlowupSequenceData.toMarkedSequence_projectionToBase] at h
  exact h

theorem orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) :
    ∀ D ∈ (s.boundary s.length).take 0,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (D.support : Set ↥(s.obj s.length)) = ∅ := by
  intro D hD
  simp at hD

private theorem exists_index_of_mem_take_consolidated446 {α : Type*} :
    ∀ (L : List α) (n : ℕ) (D : α), D ∈ L.take n →
      ∃ i, ∃ hi : i < L.length, i < n ∧ L.get ⟨i, hi⟩ = D := by
  intro L
  induction L with
  | nil =>
    intro n D hD
    simp at hD
  | cons a t ih =>
    intro n D hD
    cases n with
    | zero => simp at hD
    | succ m =>
      have hD' : D ∈ a :: t.take m := hD
      rcases List.mem_cons.mp hD' with rfl | hD''
      · exact ⟨0, by simp, Nat.succ_pos m, rfl⟩
      · obtain ⟨i, hi, hin, hget⟩ := ih m D hD''
        exact ⟨i + 1, Nat.succ_lt_succ hi, Nat.succ_lt_succ hin, hget⟩

section
variable (S : MarkedIdealWithBoundary.{u}) (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)

theorem orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated (n : ℕ)
    (h : BoundarySeparationByMaxContact.BoundarySeparated S s n) :
    ∀ D ∈ (s.boundary s.length).take n,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (D.support : Set ↥(s.obj s.length)) = ∅ := by
  intro D hD
  obtain ⟨i, hi, hin, hget⟩ := exists_index_of_mem_take_consolidated446 (s.boundary s.length) n D hD
  have key := h i hin hi
  rw [hget] at key
  exact key

theorem lt_length_nil_append_boundary_drop_zero (j : ℕ)
    (hj : j < S.boundary.length) :
    j < (([] : List (s.obj s.length).IdealSheafData) ++ (s.boundary s.length).drop 0).length := by
  have h1 : s.boundaryFrom S.boundary s.length = s.boundary s.length :=
    MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq s s.length le_rfl
  have h2 : s.boundaryFrom S.boundary s.length
      = S.boundary.map (s.toBlowupSequenceData.iteratedStrictTransform s.length) ++
        s.boundaryFrom ([] : List S.scheme.IdealSheafData) s.length :=
    BlowupSequenceData.boundary_eq_map_iteratedStrictTransform_append s.toBlowupSequenceData S.boundary s.length
  have h5 : S.boundary.length ≤ (s.boundary s.length).length := by
    rw [← h1, h2]
    simp only [List.length_append, List.length_map]
    omega
  simp only [List.nil_append, List.drop_zero]
  omega


end

theorem orderAt_pullbackTriple_le_mult (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme)
    [Smooth q] (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) :
    ∀ x : ↥(LowerDimReductionPullback.pullbackTriple S q).scheme,
      orderAt (LowerDimReductionPullback.pullbackTriple S q).ideal x ≤ (((LowerDimReductionPullback.pullbackTriple S q).mult : ℕ) : ℕ∞) := by
  have : CharZero S.base := hV.charZero
  have : Smooth S.structMap := hV.smooth
  intro x
  have h : orderAt (S.ideal.comap q) x = orderAt S.ideal (q x) :=
    orderAt_comap S.base S.structMap q S.ideal x
  exact le_trans (le_of_eq h) (hO (q x))

abbrev separateBoundaryOfFamily (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (A : ℕ → PrincipalizationAssignment.{u}) (S : MarkedIdealWithBoundary.{u}) (n : ℕ) :
    MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary :=
  MaxContactReduction.separateBoundary hinv T (fun S' _ i => A i S') S n

theorem separateBoundaryInvariant_separateBoundaryOfFamily (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u})
    (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (H : S.scheme.IdealSheafData) (hH : InStrictNormalCrossingPosition S.structMap [H])
    (j : ℕ) (hj : j ≤ S.boundary.length) :
    BoundarySeparationByMaxContact.SeparateBoundaryInvariant S H (separateBoundaryOfFamily hinv T A S j) j := by
  revert hj
  induction j with
  | zero =>
      intro _
      show BoundarySeparationByMaxContact.SeparateBoundaryInvariant S H (separateBoundaryOfFamily hinv T A S 0) 0
      have h0 : separateBoundaryOfFamily hinv T A S 0
          = emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary :=
        MaxContactCoverData.separateBoundary_zero hinv T (fun S' _ i => A i S') S
      have h1 : (separateBoundaryOfFamily hinv T A S 0).toBlowupSequenceData = BlowupSequenceData.empty S.scheme :=
        Eq.trans
          (congrArg
            (fun s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary => s.toBlowupSequenceData) h0)
          (emptyMarkedBlowupSequenceData_toBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
      have hlen : (separateBoundaryOfFamily hinv T A S 0).length = 0 :=
        Eq.trans (congrArg (fun d : BlowupSequenceData S.scheme => d.length) h1)
          (BlowupSequenceData.empty_length S.scheme)
      refine And.intro ?_ (And.intro ?_ ?_)
      · intro i hi
        exact absurd hi (Nat.not_lt_zero i)
      · intro i hi
        exact absurd hi (by omega)
      · exact BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_iteratedStrictTransform_zero S (separateBoundaryOfFamily hinv T A S 0) H hH
  | succ n ih =>
      intro hj
      show BoundarySeparationByMaxContact.SeparateBoundaryInvariant S H (separateBoundaryOfFamily hinv T A S (n + 1)) (n + 1)
      have hjn : n < S.boundary.length := Nat.lt_of_succ_le hj
      have key : BoundarySeparationByMaxContact.SeparateBoundaryInvariant S H
          (MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') S
            (separateBoundaryOfFamily hinv T A S n) [] 0 n) (n + 1) :=
        BoundarySeparationByMaxContact.separateBoundaryInvariant_appendLowerDimReduction hstar hinv P hmono A B hspec T hPdimT S hV hO
          hdimS H hH (separateBoundaryOfFamily hinv T A S n) n hjn (ih (Nat.le_of_succ_le hj))
      have hstep : separateBoundaryOfFamily hinv T A S (n + 1)
          = MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') S
              (separateBoundaryOfFamily hinv T A S n) [] 0 n :=
        MaxContactCoverData.separateBoundary_succ hinv T (fun S' _ i => A i S') S n
      rw [hstep]
      exact key

private theorem isStrictPullback_of_length_eq_zero_consolidated446 {X' X : Scheme.{u}} (g : X' ⟶ X)
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (ht : t.length = 0) (hs : s.length = 0) :
    IsStrictPullbackBlowupSeq g t s :=
  StrictPullbackBlowupSeq.isStrictPullback
    { comp := fun i hi =>
        eqToHom (congrArg t.schemeAt (by omega : i = 0)) ≫ t.isoZero.hom ≫ g ≫ s.isoZero.inv ≫
          eqToHom (congrArg s.schemeAt (by omega : (0 : ℕ) = i))
      comp_zero := by simp
      pullback := fun i hi => absurd hi (by omega)
      length_eq := by rw [ht, hs]
      center_eq := fun i hi => absurd hi (by omega) }

private theorem length_separateBoundaryOfFamily_zero_consolidated446 (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (A : ℕ → PrincipalizationAssignment.{u}) (S : MarkedIdealWithBoundary.{u}) :
    (separateBoundaryOfFamily hinv T A S 0).toMarkedSequenceOfBlowups.toSequenceOfBlowups.length = 0 := by
  have h0 : separateBoundaryOfFamily hinv T A S 0 = emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary :=
    MaxContactCoverData.separateBoundary_zero hinv T (fun S' _ i => A i S') S
  have h1 : (separateBoundaryOfFamily hinv T A S 0).toBlowupSequenceData = BlowupSequenceData.empty S.scheme :=
    Eq.trans
      (congrArg
        (fun s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary => s.toBlowupSequenceData) h0)
      (emptyMarkedBlowupSequenceData_toBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
  have hlen : (separateBoundaryOfFamily hinv T A S 0).length = 0 :=
    Eq.trans (congrArg (fun d : BlowupSequenceData S.scheme => d.length) h1)
      (BlowupSequenceData.empty_length S.scheme)
  exact hlen

private theorem dim_derivedTriple_le_dim_consolidated446 (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u})
    (hV : S.IsAdmissible) (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (added : List (s.obj s.length).IdealSheafData) (nDrop : ℕ) :
    (MaxContactCoverData.derivedTriple S s hft added nDrop).krullDimSucc ≤ S.krullDimSucc := by
  have h : krullDimSucc (s.toMarkedSequenceOfBlowups.schemeAt s.length) ≤ S.krullDimSucc :=
    hstar.schemeDim_level_le S hV s.toMarkedSequenceOfBlowups s.length
      (s.le_toSequenceOfBlowups_length (le_refl s.length))
  show krullDimSucc (MaxContactCoverData.derivedTriple S s hft added nDrop).scheme ≤ S.krullDimSucc
  rw [MaxContactCoverData.derivedTriple_scheme]
  exact h

private theorem boundary_length_pullbackTriple_consolidated446 (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}}
    (g : X' ⟶ S.scheme) : (LowerDimReductionPullback.pullbackTriple S g).boundary.length = S.boundary.length := by
  show (List.map (fun D : S.scheme.IdealSheafData => D.comap g) S.boundary).length
      = S.boundary.length
  simp

section
variable (U : MarkedIdealWithBoundary.{u})

private theorem boundary_pullbackAlong_eq_map_comap_consolidated446 {Y : Scheme.{u}}
    (qq : Y ⟶ Spec (CommRingCat.of U.base)) (h : Y ⟶ U.scheme)
    (L : List U.scheme.IdealSheafData) (hL : U.boundary = L) :
    (U.pullbackAlong Y qq h).boundary = L.map (fun Dv => Dv.comap h) := by
  subst hL
  rfl

private theorem isAdmissible_withBoundary_of_eq_consolidated446 (hU : U.IsAdmissible)
    (L : List U.scheme.IdealSheafData) (hL : U.boundary = L) : (U.withBoundary L).IsAdmissible := by
  subst hL
  exact hU


end

private theorem length_toMarkedSequence_eq_zero_consolidated446 {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData)
    (b : SequenceOfBlowups X) (h : (BlowupSequenceData.ofSequenceOfBlowups b).IsMarked p I m E) (hb : b.length = 0) :
    ((BlowupSequenceData.ofSequenceOfBlowups b).toMarkedBlowupSequenceData p I m E h).length = 0 := hb

private theorem orderAt_le_mult_of_isOrderBoundedByMult_consolidated446 (T : MarkedIdealWithBoundary.{u}) (h : T.IsOrderBoundedByMult) :
    ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞) := h

private theorem isMaxContactHypersurface_derivedTriple_consolidated446 (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (added : List (s.obj s.length).IdealSheafData) (nDrop : ℕ)
    (E : (s.obj s.length).IdealSheafData)
    (inst : LocallyOfFiniteType
      (MaxContactCoverData.derivedTriple S s hft added nDrop).structMap)
    (h : @IsMaxContactHypersurface S.base S.instField (s.obj s.length)
      (s.proj s.length ≫ S.structMap) hft (LowerDimReductionPullback.tunedIdealAtLength S s hft) (tuningExponent S.mult) E) :
    @IsMaxContactHypersurface (MaxContactCoverData.derivedTriple S s hft added nDrop).base
      (MaxContactCoverData.derivedTriple S s hft added nDrop).instField
      (MaxContactCoverData.derivedTriple S s hft added nDrop).scheme
      (MaxContactCoverData.derivedTriple S s hft added nDrop).structMap inst
      (MaxContactCoverData.derivedTriple S s hft added nDrop).ideal
      (MaxContactCoverData.derivedTriple S s hft added nDrop).mult E := h

private theorem isMaxContactHypersurface_strictTransformAtLength_consolidated446 (hstar : MaxContactCoverProperties.{u})
    (S : MarkedIdealWithBoundary.{u})
    (hV : S.IsAdmissible) (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (Hs : S.scheme.IdealSheafData)
    (hH : ∀ [LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult Hs)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap)) :
    @IsMaxContactHypersurface S.base S.instField (s.obj s.length)
      (s.proj s.length ≫ S.structMap) hft (LowerDimReductionPullback.tunedIdealAtLength S s hft) (tuningExponent S.mult)
      (MaxContactReduction.strictTransformAtLength s Hs) := by
  have := hV.charZero
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have := BoundarySeparationByMaxContact.smooth_projectionToBase_comp hstar S hV s s.length (le_refl s.length)
  have := hft
  have h1 : IsMaxContactHypersurface S.base (s.proj s.length ≫ S.structMap) (s.ideal s.length)
      S.mult (MaxContactReduction.iteratedStrictTransform s Hs s.length) :=
    isMaxContactHypersurface_iteratedStrictTransform hstar S hV hO Hs hH s s.length (le_refl s.length)
  rw [LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf, MaxContactReduction.strictTransformAtLength_eq]
  exact BoundarySeparationByMaxContact.isMaxContactHypersurface_balancedTunedSheaf hstar S.base
    (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult hV.one_le_mult
    (fun x => LowerDimReductionPullback.orderAt_ideal_length_le hstar S hV hO s x)
    (MaxContactReduction.iteratedStrictTransform s Hs s.length) h1

private theorem isMaxContactHypersurface_comap_lastMap_consolidated446 (hAdm : MaxContactHypersurfaceSmoothPullback.{u})
    (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    {X' : Scheme.{u}} (g : X' ⟶ S.scheme) [Smooth g]
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (t : MarkedBlowupSequenceData (LowerDimReductionPullback.pullbackTriple S g).structMap (LowerDimReductionPullback.pullbackTriple S g).ideal
      (LowerDimReductionPullback.pullbackTriple S g).mult (LowerDimReductionPullback.pullbackTriple S g).boundary)
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hftS : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hftT : LocallyOfFiniteType
      (t.proj t.length ≫ (LowerDimReductionPullback.pullbackTriple S g).structMap))
    (Hs : (s.obj s.length).IdealSheafData)
    (h : @IsMaxContactHypersurface S.base S.instField (s.obj s.length)
      (s.proj s.length ≫ S.structMap) hftS (LowerDimReductionPullback.tunedIdealAtLength S s hftS) (tuningExponent S.mult) Hs)
    (added : List (s.obj s.length).IdealSheafData) (nDrop : ℕ)
    (hVc : (MaxContactCoverData.derivedTriple S s hftS added nDrop).IsAdmissible) :
    @IsMaxContactHypersurface (LowerDimReductionPullback.pullbackTriple S g).base (LowerDimReductionPullback.pullbackTriple S g).instField
      (t.obj t.length) (t.proj t.length ≫ (LowerDimReductionPullback.pullbackTriple S g).structMap) hftT
      (LowerDimReductionPullback.tunedIdealAtLength (LowerDimReductionPullback.pullbackTriple S g) t hftT)
      (tuningExponent (LowerDimReductionPullback.pullbackTriple S g).mult) (Hs.comap D.lastMap) := by
  have := hV.charZero
  have := BoundarySeparationByMaxContact.smooth_projectionToBase_comp hstar S hV s s.length (le_refl s.length)
  have := hftS
  have hsm : Smooth (LowerDimReductionPullback.pullbackMapAtLength S g s t D) :=
    LowerDimReductionPullback.smooth_pullbackMapAtLength S g s t D
  have hftg : LocallyOfFiniteType
      (LowerDimReductionPullback.pullbackMapAtLength S g s t D ≫ (s.proj s.length ≫ S.structMap)) := by
    rw [LowerDimReductionPullback.pullbackMapAtLength_comp_eq_pullbackTriple_structureMorphism S g s t D]
    exact hftT
  have key := hAdm S.base (s.obj s.length) (s.proj s.length ≫ S.structMap) (t.obj t.length)
    (LowerDimReductionPullback.pullbackMapAtLength S g s t D) (LowerDimReductionPullback.tunedIdealAtLength S s hftS) (tuningExponent S.mult)
    (one_le_tuningExponent S.mult) Hs h
  exact @isMaxContactHypersurface_of_eq_of_eq_of_eq S.base S.instField (t.obj t.length)
    (LowerDimReductionPullback.pullbackMapAtLength S g s t D ≫ (s.proj s.length ≫ S.structMap))
    (t.proj t.length ≫ (LowerDimReductionPullback.pullbackTriple S g).structMap) hftg hftT
    ((LowerDimReductionPullback.tunedIdealAtLength S s hftS).comap (LowerDimReductionPullback.pullbackMapAtLength S g s t D))
    (LowerDimReductionPullback.tunedIdealAtLength (LowerDimReductionPullback.pullbackTriple S g) t hftT)
    (Hs.comap (LowerDimReductionPullback.pullbackMapAtLength S g s t D)) (Hs.comap (LowerDimReductionPullback.pullbackMapAtLength S g s t D))
    (tuningExponent S.mult)
    (LowerDimReductionPullback.pullbackMapAtLength_comp_eq_pullbackTriple_structureMorphism S g s t D)
    (LowerDimReductionPullback.tunedIdealAtLength_comap_pullbackMapAtLength S g s t D hftS hftT added nDrop hVc) rfl key

private theorem isAdmissible_derivedTriple_pullbackTriple_consolidated446 (hin : OrderReduction.OrderReductionHypotheses.{u})
    (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (g : X' ⟶ S.scheme) [Smooth g]
    [Flat g] (hV' : (LowerDimReductionPullback.pullbackTriple S g).IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (t : MarkedBlowupSequenceData (LowerDimReductionPullback.pullbackTriple S g).structMap (LowerDimReductionPullback.pullbackTriple S g).ideal
      (LowerDimReductionPullback.pullbackTriple S g).mult (LowerDimReductionPullback.pullbackTriple S g).boundary)
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hNs : ∀ i ≤ s.length, IsLocallyNoetherian (s.obj i))
    (hNt : ∀ i ≤ t.length, IsLocallyNoetherian (t.obj i))
    (hftS : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hftT : LocallyOfFiniteType
      (t.proj t.length ≫ (LowerDimReductionPullback.pullbackTriple S g).structMap))
    (added : List (s.obj s.length).IdealSheafData) (nDrop : ℕ)
    (hVc : (MaxContactCoverData.derivedTriple S s hftS added nDrop).IsAdmissible) :
    (MaxContactCoverData.derivedTriple (LowerDimReductionPullback.pullbackTriple S g) t hftT
      (LowerDimReductionPullback.comapBoundaryPullback S g s t D added) nDrop).IsAdmissible := by
  have hsm : Smooth (LowerDimReductionPullback.pullbackMapAtLength S g s t D) :=
    LowerDimReductionPullback.smooth_pullbackMapAtLength S g s t D
  have hlev : ((LowerDimReductionPullback.pullbackTriple S g).transformAt t.toMarkedSequenceOfBlowups t.length).IsAdmissible :=
    MarkedIdealWithBoundary.IsAdmissible.transformAt effectiveCartierSupportContainsNoComponent hV' t.toMarkedSequenceOfBlowups t.length
      (t.le_toSequenceOfBlowups_length (le_refl t.length))
  have hqc0 := hlev.quasiCompact
  rw [MarkedIdealWithBoundary.transformAt_structureMorphism, MarkedSequenceOfBlowups.projectionToSpec_eq,
    MarkedBlowupSequenceData.toMarkedSequence_projectionToBase] at hqc0
  have hqcA : QuasiCompact
      (LowerDimReductionPullback.pullbackMapAtLength S g s t D ≫ (s.proj s.length ≫ S.structMap)) := by
    rw [LowerDimReductionPullback.pullbackMapAtLength_comp_eq_pullbackTriple_structureMorphism S g s t D]
    exact hqc0
  have hpb := @OrderReduction.OrderReductionHypotheses.valid_pullbackAlong hin
    (MaxContactCoverData.derivedTriple S s hftS added nDrop) hVc (t.obj t.length)
    (LowerDimReductionPullback.pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS added nDrop).structMap)
    (LowerDimReductionPullback.pullbackMapAtLength S g s t D) hsm hqcA rfl
  have hbd1 : ((MaxContactCoverData.derivedTriple S s hftS added nDrop).pullbackAlong (t.obj t.length)
      (LowerDimReductionPullback.pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS added nDrop).structMap)
      (LowerDimReductionPullback.pullbackMapAtLength S g s t D)).boundary
      = (added ++ (s.boundary s.length).drop nDrop).map
          (fun Dv => Dv.comap (LowerDimReductionPullback.pullbackMapAtLength S g s t D)) :=
    boundary_pullbackAlong_eq_map_comap_consolidated446 (MaxContactCoverData.derivedTriple S s hftS added nDrop)
      (LowerDimReductionPullback.pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS added nDrop).structMap)
      (LowerDimReductionPullback.pullbackMapAtLength S g s t D) _
      (MaxContactCoverData.derivedTriple_boundary S s hftS added nDrop)
  have hbd2 : (added ++ (s.boundary s.length).drop nDrop).map
        (fun Dv => Dv.comap (LowerDimReductionPullback.pullbackMapAtLength S g s t D))
      = LowerDimReductionPullback.comapBoundaryPullback S g s t D added ++ (t.boundary t.length).drop nDrop := by
    rw [List.map_append, List.map_drop, LowerDimReductionPullback.boundary_eq_map_comap_pullbackMapAtLength S g s t D hNs hNt]
  rw [← LowerDimReductionPullback.pullbackAlong_derivedTriple_eq S g s t D hftS hftT added nDrop hVc]
  exact isAdmissible_withBoundary_of_eq_consolidated446 _ hpb _ (hbd1.trans hbd2)

section
variable (hstar : MaxContactCoverProperties.{u}) (hin : OrderReduction.OrderReductionHypotheses.{u}) (hMC : IsMaxContactInvariantBalancedTuned.{u})
include hstar hin hMC

private theorem isomorphic_appendLowerDimReduction_of_isMaxContactHypersurface_consolidated446 (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (nDrop : ℕ) (E1 E2 : (s.obj s.length).IdealSheafData)
    (hV1 : (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).IsAdmissible)
    (hV2 : (MaxContactCoverData.derivedTriple S s hft [E2] nDrop).IsAdmissible)
    (hR1 : @IsMaxContactHypersurface S.base S.instField (s.obj s.length)
      (s.proj s.length ≫ S.structMap) hft (LowerDimReductionPullback.tunedIdealAtLength S s hft) (tuningExponent S.mult) E1)
    (hR2 : @IsMaxContactHypersurface S.base S.instField (s.obj s.length)
      (s.proj s.length ≫ S.structMap) hft (LowerDimReductionPullback.tunedIdealAtLength S s hft) (tuningExponent S.mult) E2)
    (hsep : ∀ Dv ∈ (s.boundary s.length).take nDrop,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (Dv.support : Set ↥(s.obj s.length)) = ∅) :
    (MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') S s [E1] nDrop
        0).toMarkedSequenceOfBlowups.toSequenceOfBlowups.Isomorphic
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') S s [E2] nDrop
        0).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  classical
  have hdim1 : (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).krullDimSucc ≤ T.krullDimSucc :=
    le_trans (dim_derivedTriple_le_dim_consolidated446 hstar S hV s hft [E1] nDrop) hdimS
  have hdim2 : (MaxContactCoverData.derivedTriple S s hft [E2] nDrop).krullDimSucc ≤ T.krullDimSucc :=
    le_trans (dim_derivedTriple_le_dim_consolidated446 hstar S hV s hft [E2] nDrop) hdimS
  have hj1 : 0 < ([E1] ++ (s.boundary s.length).drop nDrop).length := by simp
  have hj2 : 0 < ([E2] ++ (s.boundary s.length).drop nDrop).length := by simp
  obtain ⟨hmk1, hc1, -⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A B 0 (hspec 0)
    (fun S' _ i => A i S') (fun _ _ _ => rfl) S hV hV.one_le_mult hO s [E1] nDrop hft hdim1
    (hmono _ _ hdim1 hPdimT) hV1 hj1 hsep
  obtain ⟨hmk2, hc2, -⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A B 0 (hspec 0)
    (fun S' _ i => A i S') (fun _ _ _ => rfl) S hV hV.one_le_mult hO s [E2] nDrop hft hdim2
    (hmono _ _ hdim2 hPdimT) hV2 hj2 hsep
  rw [hc1, hc2]
  by_cases hne : (orderAtLeastLocus (s.ideal s.length) S.mult).Nonempty
  · have := hV.charZero
    have := BoundarySeparationByMaxContact.smooth_projectionToBase_comp hstar S hV s s.length (le_refl s.length)
    have := hft
    have hmax : MaxOrderEq (s.ideal s.length) S.mult :=
      LowerDimReductionPullback.maxOrderEq_ideal_length_of_nonempty hstar S hV hO s hne
    have hbdT : (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).boundary
        = E1 :: (s.boundary s.length).drop nDrop :=
      MaxContactCoverData.derivedTriple_boundary S s hft [E1] nDrop
    have hA1 : ∀ [inst : LocallyOfFiniteType
        (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).structMap],
        IsMaxContactHypersurface (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).base
          (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).structMap
          (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).ideal
          (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).mult E1 := by
      intro inst
      exact isMaxContactHypersurface_derivedTriple_consolidated446 S s hft [E1] nDrop E1 inst hR1
    have hA2 : ∀ [inst : LocallyOfFiniteType
        (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).structMap],
        IsMaxContactHypersurface (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).base
          (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).structMap
          (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).ideal
          (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).mult E2 := by
      intro inst
      exact isMaxContactHypersurface_derivedTriple_consolidated446 S s hft [E1] nDrop E2 inst hR2
    have hMCinv : ∀ [inst : LocallyOfFiniteType
        (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).structMap],
        IsMaxContactInvariant (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).base
          (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).structMap
          (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).ideal
          (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).mult := by
      intro inst
      rw [MaxContactCoverData.derivedTriple_mult, LowerDimReductionPullback.ideal_derivedTriple, LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf]
      exact hMC S.base (s.obj s.length) (s.proj s.length ≫ S.structMap) (s.ideal s.length)
        S.mult hV.one_le_mult hmax
    have hEq := DivisorReductionIndependence.isomorphic_withBoundary_cons_of_isMaxContactHypersurface hin P hmono (A 0) B (hspec 0)
      (MaxContactCoverData.derivedTriple S s hft [E1] nDrop) hV1 (hmono _ _ hdim1 hPdimT)
      (orderAt_le_mult_of_isOrderBoundedByMult_consolidated446 _
        (LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hV.one_le_mult hO s hft [E1] nDrop hV1))
      (fun _ => LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hV.one_le_mult hO s hft [E1] nDrop hV1)
      hMCinv ((s.boundary s.length).drop nDrop) E1 E2 hbdT hV2 hA1 hA2
    refine MarkedBlowupSequenceData.append_isomorphic_of_isomorphic s _ _ hinv ?_
    exact SequenceOfBlowups.Isomorphic.trans
      (BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic
        (A 0 (MaxContactCoverData.derivedTriple S s hft [E1] nDrop)).toSequenceOfBlowups)
      (SequenceOfBlowups.Isomorphic.trans hEq
        (SequenceOfBlowups.Isomorphic.symm
          (BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic
            (A 0 (MaxContactCoverData.derivedTriple S s hft [E2] nDrop)).toSequenceOfBlowups)))
  · have hempty : orderAtLeastLocus (s.ideal s.length) S.mult = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    have hl1 : (A 0 (MaxContactCoverData.derivedTriple S s hft [E1] nDrop)).length = 0 :=
      LowerDimReductionPullback.length_eq_zero_of_orderAtLeastLocus_eq_empty hstar P 0 (A 0) B (hspec 0) S hV hV.one_le_mult hO s hft
        [E1] nDrop (hmono _ _ hdim1 hPdimT) hV1 hj1 hempty
    have hl2 : (A 0 (MaxContactCoverData.derivedTriple S s hft [E2] nDrop)).length = 0 :=
      LowerDimReductionPullback.length_eq_zero_of_orderAtLeastLocus_eq_empty hstar P 0 (A 0) B (hspec 0) S hV hV.one_le_mult hO s hft
        [E2] nDrop (hmono _ _ hdim2 hPdimT) hV2 hj2 hempty
    have e1 := MarkedBlowupSequenceData.append_isomorphic_of_length_eq_zero s _ hinv
      (length_toMarkedSequence_eq_zero_consolidated446 (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
        (s.boundary s.length) (A 0 (MaxContactCoverData.derivedTriple S s hft [E1] nDrop)).toSequenceOfBlowups
        hmk1 hl1)
    have e2 := MarkedBlowupSequenceData.append_isomorphic_of_length_eq_zero s _ hinv
      (length_toMarkedSequence_eq_zero_consolidated446 (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
        (s.boundary s.length) (A 0 (MaxContactCoverData.derivedTriple S s hft [E2] nDrop)).toSequenceOfBlowups
        hmk2 hl2)
    exact SequenceOfBlowups.Isomorphic.trans e1 (SequenceOfBlowups.Isomorphic.symm e2)

theorem isStrictPullbackBlowupSeq_reduceAlongHypersurface (hAdm : MaxContactHypersurfaceSmoothPullback.{u})
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (H : S.scheme.IdealSheafData)
    (hH : ∀ [LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [Smooth q]
    [Flat q] [AlgebraicGeometry.Surjective q]
    (hV' : (LowerDimReductionPullback.pullbackTriple S q).IsAdmissible) (hdim' : (LowerDimReductionPullback.pullbackTriple S q).krullDimSucc ≤ T.krullDimSucc)
    (H' : (LowerDimReductionPullback.pullbackTriple S q).scheme.IdealSheafData)
    (hH' : ∀ [LocallyOfFiniteType (LowerDimReductionPullback.pullbackTriple S q).structMap],
      IsMaxContactHypersurface (LowerDimReductionPullback.pullbackTriple S q).base (LowerDimReductionPullback.pullbackTriple S q).structMap
        (LowerDimReductionPullback.pullbackTriple S q).ideal (LowerDimReductionPullback.pullbackTriple S q).mult H')
    (hH'snc : InStrictNormalCrossingPosition (LowerDimReductionPullback.pullbackTriple S q).structMap [H']) :
    IsStrictPullbackBlowupSeq q
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S') (LowerDimReductionPullback.pullbackTriple S q)
        H').toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  classical
  have hO' := orderAt_pullbackTriple_le_mult S q hV hO
  have hLen : (LowerDimReductionPullback.pullbackTriple S q).boundary.length = S.boundary.length :=
    boundary_length_pullbackTriple_consolidated446 S q
  have key : ∀ n : ℕ, n ≤ S.boundary.length →
      IsStrictPullbackBlowupSeq q
        (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) n).toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (separateBoundaryOfFamily hinv T A S n).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
    intro n
    induction n with
    | zero =>
        intro _
        exact isStrictPullback_of_length_eq_zero_consolidated446 q _ _
          (length_separateBoundaryOfFamily_zero_consolidated446 hinv T A (LowerDimReductionPullback.pullbackTriple S q))
          (length_separateBoundaryOfFamily_zero_consolidated446 hinv T A S)
    | succ m ih =>
        intro hm
        have hm' : m < S.boundary.length := lt_of_lt_of_le (Nat.lt_succ_self m) hm
        have D := (ih (le_of_lt hm')).toStrictPullbackBlowupSeq
        have hftS := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV
          (separateBoundaryOfFamily hinv T A S m) (separateBoundaryOfFamily hinv T A S m).length le_rfl
        have hftT := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar
          (LowerDimReductionPullback.pullbackTriple S q) hV' (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m)
          (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m).length le_rfl
        have hdim : (MaxContactCoverData.derivedTriple S (separateBoundaryOfFamily hinv T A S m) hftS
            ([] : List ((separateBoundaryOfFamily hinv T A S m).obj
              (separateBoundaryOfFamily hinv T A S m).length).IdealSheafData) 0).krullDimSucc ≤ T.krullDimSucc :=
          le_trans (dim_derivedTriple_le_dim_consolidated446 hstar S hV (separateBoundaryOfFamily hinv T A S m) hftS [] 0) hdimS
        have hdimb : (MaxContactCoverData.derivedTriple (LowerDimReductionPullback.pullbackTriple S q)
            (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m) hftT
            ([] : List ((separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m).obj
              (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m).length).IdealSheafData)
            0).krullDimSucc ≤ T.krullDimSucc :=
          le_trans (dim_derivedTriple_le_dim_consolidated446 hstar (LowerDimReductionPullback.pullbackTriple S q) hV'
            (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m) hftT [] 0) hdim'
        have hres := LowerDimReductionPullback.nonempty_strictPullback_appendLowerDimReduction S q (separateBoundaryOfFamily hinv T A S m)
          (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m) D hstar hinv T P A B m (hspec m)
          (fun S' _ i => A i S') (fun _ _ _ => rfl) [] 0 hftS hftT hV hV.one_le_mult hO
          (isLocallyNoetherian_schemeAt hstar S hV (separateBoundaryOfFamily hinv T A S m)) hV' hO'
          (isLocallyNoetherian_schemeAt hstar (LowerDimReductionPullback.pullbackTriple S q) hV'
            (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m))
          hdim (hmono _ _ hdim hPdimT)
          (isAdmissible_derivedTriple_nil hstar S hV (separateBoundaryOfFamily hinv T A S m) hftS)
          (lt_length_nil_append_boundary_drop_zero S (separateBoundaryOfFamily hinv T A S m) m hm')
          (orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero S (separateBoundaryOfFamily hinv T A S m))
          hdimb (hmono _ _ hdimb hPdimT)
          (isAdmissible_derivedTriple_nil hstar (LowerDimReductionPullback.pullbackTriple S q) hV'
            (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m) hftT)
          (lt_length_nil_append_boundary_drop_zero (LowerDimReductionPullback.pullbackTriple S q)
            (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m) m (by rw [hLen]; exact hm'))
          (orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero (LowerDimReductionPullback.pullbackTriple S q)
            (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m))
        have e1 : separateBoundaryOfFamily hinv T A S (m + 1)
            = MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') S
              (separateBoundaryOfFamily hinv T A S m) [] 0 m :=
          MaxContactCoverData.separateBoundary_succ hinv T (fun S' _ i => A i S') S m
        have e2 : separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) (m + 1)
            = MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') (LowerDimReductionPullback.pullbackTriple S q)
              (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m) [] 0 m :=
          MaxContactCoverData.separateBoundary_succ hinv T (fun S' _ i => A i S') (LowerDimReductionPullback.pullbackTriple S q) m
        rw [e1, e2]
        exact hres.elim fun D' => D'.isStrictPullback
  have hftS2 := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV
    (separateBoundaryOfFamily hinv T A S S.boundary.length)
    (separateBoundaryOfFamily hinv T A S S.boundary.length).length le_rfl
  have hftT2 := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar (LowerDimReductionPullback.pullbackTriple S q) hV'
    (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length)
    (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length).length le_rfl
  have hTS := separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A B hspec T hPdimT S hV hO
    hdimS H hHsnc S.boundary.length le_rfl
  have hTS' := separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A B hspec T hPdimT
    (LowerDimReductionPullback.pullbackTriple S q) hV' hO' hdim' H' hH'snc (LowerDimReductionPullback.pullbackTriple S q).boundary.length le_rfl
  rw [hLen] at hTS'
  have hsncF0 := inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar S hV hO H
    (@hH hV.locallyOfFiniteType) (separateBoundaryOfFamily hinv T A S S.boundary.length) hTS.2.2
    (separateBoundaryOfFamily hinv T A S S.boundary.length).length le_rfl
  rw [← MaxContactReduction.strictTransformAtLength_eq] at hsncF0
  have hVcF := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar S hV
    (separateBoundaryOfFamily hinv T A S S.boundary.length) hftS2
    [MaxContactReduction.strictTransformAtLength (separateBoundaryOfFamily hinv T A S S.boundary.length) H]
    S.boundary.length hsncF0
  have hsncF0' := inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar (LowerDimReductionPullback.pullbackTriple S q) hV' hO' H'
    (@hH' hV'.locallyOfFiniteType)
    (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) hTS'.2.2
    (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length).length le_rfl
  rw [← MaxContactReduction.strictTransformAtLength_eq, hLen] at hsncF0'
  have hVcF' := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar (LowerDimReductionPullback.pullbackTriple S q) hV'
    (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) hftT2
    [MaxContactReduction.strictTransformAtLength
      (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) H']
    S.boundary.length hsncF0'
  rw [MaxContactCoverData.reduceAlongHypersurface_eq_appendLowerDimReduction, MaxContactCoverData.reduceAlongHypersurface_eq_appendLowerDimReduction, hLen]
  have D := (key S.boundary.length le_rfl).toStrictPullbackBlowupSeq
  have hdimF : (MaxContactCoverData.derivedTriple S (separateBoundaryOfFamily hinv T A S S.boundary.length) hftS2
      [MaxContactReduction.strictTransformAtLength (separateBoundaryOfFamily hinv T A S S.boundary.length) H]
      S.boundary.length).krullDimSucc ≤ T.krullDimSucc :=
    le_trans (dim_derivedTriple_le_dim_consolidated446 hstar S hV (separateBoundaryOfFamily hinv T A S S.boundary.length) hftS2
      [MaxContactReduction.strictTransformAtLength (separateBoundaryOfFamily hinv T A S S.boundary.length) H]
      S.boundary.length) hdimS
  have hVcF2 := isAdmissible_derivedTriple_pullbackTriple_consolidated446 hin S q hV'
    (separateBoundaryOfFamily hinv T A S S.boundary.length)
    (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) D
    (isLocallyNoetherian_schemeAt hstar S hV (separateBoundaryOfFamily hinv T A S S.boundary.length))
    (isLocallyNoetherian_schemeAt hstar (LowerDimReductionPullback.pullbackTriple S q) hV'
      (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length))
    hftS2 hftT2
    [MaxContactReduction.strictTransformAtLength (separateBoundaryOfFamily hinv T A S S.boundary.length) H]
    S.boundary.length hVcF
  have hdimF' : (MaxContactCoverData.derivedTriple (LowerDimReductionPullback.pullbackTriple S q)
      (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) hftT2
      (LowerDimReductionPullback.comapBoundaryPullback S q (separateBoundaryOfFamily hinv T A S S.boundary.length)
        (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) D
        [MaxContactReduction.strictTransformAtLength (separateBoundaryOfFamily hinv T A S S.boundary.length) H])
      S.boundary.length).krullDimSucc ≤ T.krullDimSucc :=
    le_trans (dim_derivedTriple_le_dim_consolidated446 hstar (LowerDimReductionPullback.pullbackTriple S q) hV'
      (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) hftT2 _
      S.boundary.length) hdim'
  have hNonempty := LowerDimReductionPullback.nonempty_strictPullback_appendLowerDimReduction S q
      (separateBoundaryOfFamily hinv T A S S.boundary.length)
      (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) D hstar hinv T P A B 0
      (hspec 0) (fun S' _ i => A i S') (fun _ _ _ => rfl)
      [MaxContactReduction.strictTransformAtLength (separateBoundaryOfFamily hinv T A S S.boundary.length) H]
      S.boundary.length
      hftS2 hftT2 hV hV.one_le_mult hO
      (isLocallyNoetherian_schemeAt hstar S hV (separateBoundaryOfFamily hinv T A S S.boundary.length)) hV' hO'
      (isLocallyNoetherian_schemeAt hstar (LowerDimReductionPullback.pullbackTriple S q) hV'
        (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length))
      hdimF (hmono _ _ hdimF hPdimT) hVcF (by simp)
      (orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated S (separateBoundaryOfFamily hinv T A S S.boundary.length) S.boundary.length hTS.1)
      hdimF' (hmono _ _ hdimF' hPdimT) hVcF2 (by simp)
      (orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated (LowerDimReductionPullback.pullbackTriple S q)
        (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) S.boundary.length
        hTS'.1)
  have hMaxContactS := isMaxContactHypersurface_strictTransformAtLength_consolidated446 hstar S hV hO H hH
    (separateBoundaryOfFamily hinv T A S S.boundary.length) hftS2
  have hMaxContactT := isMaxContactHypersurface_strictTransformAtLength_consolidated446 hstar (LowerDimReductionPullback.pullbackTriple S q) hV' hO' H' hH'
    (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) hftT2
  have hMaxContactComap := isMaxContactHypersurface_comap_lastMap_consolidated446 hAdm hstar S hV q
    (separateBoundaryOfFamily hinv T A S S.boundary.length)
    (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) D hftS2 hftT2
    (MaxContactReduction.strictTransformAtLength (separateBoundaryOfFamily hinv T A S S.boundary.length) H) hMaxContactS
    [MaxContactReduction.strictTransformAtLength (separateBoundaryOfFamily hinv T A S S.boundary.length) H]
    S.boundary.length hVcF
  have he := isomorphic_appendLowerDimReduction_of_isMaxContactHypersurface_consolidated446 hstar hin hMC hinv P hmono A B hspec T hPdimT
    (LowerDimReductionPullback.pullbackTriple S q) hV' hO' hdim'
    (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) hftT2 S.boundary.length
    ((MaxContactReduction.strictTransformAtLength (separateBoundaryOfFamily hinv T A S S.boundary.length) H).comap D.lastMap)
    (MaxContactReduction.strictTransformAtLength
      (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) H')
    hVcF2 hVcF' hMaxContactComap hMaxContactT
    (orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated (LowerDimReductionPullback.pullbackTriple S q)
      (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) S.boundary.length hTS'.1)
  exact hNonempty.elim fun D' => IsStrictPullbackBlowupSeq.of_isomorphic_pullback D'.isStrictPullback he


end

end BoundarySeparationBaseChange

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.EmptyOrderLocusAfterReduction
section


section
namespace FunctorialResolution.EmbeddedResolution

namespace BoundarySeparationByMaxContact

private theorem orderAtLeastLocus_eq_support_maxContactIdeal_consolidated449 (k : Type u) [Field k] [CharZero k]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p]
    [LocallyOfFiniteType p] (A : P.IdealSheafData) (m : ℕ) (hm : 1 ≤ m) :
    orderAtLeastLocus A m = ((maxContactIdeal k p A m).support : Set ↥P) := by
  have hlt : m - 1 < m := by omega
  have hd := orderAtLeastLocus_derivIdealSheafIterate k p A (r := m - 1) (m := m) hlt
  rw [show m - (m - 1) = 1 from by omega] at hd
  ext x
  rw [← hd]
  exact mem_orderAtLeastLocus_one_iff _ x

private theorem restrictIdeal_eq_comap_consolidated449 {X : Scheme.{u}} (D : X.IdealSheafData) (V : X.Opens) :
    restrictIdeal D V = D.comap V.ι := rfl

private theorem mem_support_toBlowupSequenceData_iteratedStrictTransform_consolidated449 {k : Type u} [Field k]
    {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) (i : ℕ)
    (x : ↥(s.obj i))
    (hx : x ∈ ((MaxContactReduction.iteratedStrictTransform s H i).support : Set ↥(s.obj i))) :
    x ∈ ((s.toBlowupSequenceData.iteratedStrictTransform i H).support : Set ↥(s.obj i)) := by
  rw [← iteratedStrictTransform_eq_toBlowupSequenceData s H i]
  exact hx

private theorem orderAtLeastLocus_subset_support_of_isMaxContactHypersurface_consolidated449 (k : Type u) [Field k]
    [CharZero k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p]
    (A H : P.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ)
    (hH : IsMaxContactHypersurface k p A μ H) :
    orderAtLeastLocus A μ ⊆ (H.support : Set ↥P) := by
  intro x hx
  obtain ⟨U, _, hxU, hcase⟩ := hH x
  rcases hcase with ⟨hdisj, _⟩ | ⟨_, _, _, hcoord, hmcc⟩
  · exact absurd hxU (Set.disjoint_left.1 hdisj hx)
  · have hmc : x ∈ ((maxContactIdeal k p A μ).support : Set ↥P) := by
      rw [← orderAtLeastLocus_eq_support_maxContactIdeal_consolidated449 k p A μ hμ]
      exact hx
    have hbase : (U.ι).base (⟨x, hxU⟩ : ↥U) = x := rfl
    have h1 : (⟨x, hxU⟩ : ↥U) ∈ ((maxContactIdeal k p A μ).comap U.ι).support := by
      refine AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.2 ?_
      rw [hbase]
      exact hmc
    have hle : (H.comap U.ι) ≤ ((maxContactIdeal k p A μ).comap U.ι) := by
      rw [← restrictIdeal_eq_comap_consolidated449, ← restrictIdeal_eq_comap_consolidated449, hcoord]
      exact hmcc
    have h2 : (⟨x, hxU⟩ : ↥U) ∈ (H.comap U.ι).support :=
      Scheme.IdealSheafData.support_antitone hle h1
    have h3 := AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1 h2
    rw [hbase] at h3
    exact h3

section
variable {X Y : Scheme.{u}} (e : X ≅ Y) (J : Y.IdealSheafData) (n : ℕ)

private theorem orderAtLeastLocus_comap_iso_eq_empty_consolidated449 (hJ : orderAtLeastLocus J n = ∅) :
    orderAtLeastLocus (J.comap e.hom) n = ∅ := by
  rw [orderAtLeastLocus_comap_iso e J n, hJ, Set.preimage_empty]

private theorem orderAtLeastLocus_eq_empty_of_comap_iso_consolidated449 (hJ : orderAtLeastLocus (J.comap e.hom) n = ∅) :
    orderAtLeastLocus J n = ∅ := by
  rw [orderAtLeastLocus_comap_iso e J n] at hJ
  have hsurj : ∀ y : ↥Y, ∃ x : ↥X, e.hom x = y := by
    intro y
    refine ⟨e.inv y, ?_⟩
    simp
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  obtain ⟨x, hx⟩ := hsurj y
  have hmem : x ∈ (⇑e.hom ⁻¹' orderAtLeastLocus J n) := by
    simp only [Set.mem_preimage, hx]
    exact hy
  rw [hJ] at hmem
  exact hmem


end

private theorem orderAtLeastLocus_append_eq_empty_consolidated449 {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (hinv : ComapIsoInvariance.{u}) (n : ℕ)
    (ht : ∀ i : ℕ, i = t.length → orderAtLeastLocus (t.ideal i) n = ∅)
    (hs : t.length = 0 → ∀ i : ℕ, i = s.length → orderAtLeastLocus (s.ideal i) n = ∅) :
    orderAtLeastLocus ((s.append t hinv).ideal (s.append t hinv).length) n = ∅ := by
  have key : ∀ i : ℕ, i = s.length + t.length →
      orderAtLeastLocus ((s.append t hinv).ideal i) n = ∅ := by
    rintro i rfl
    rw [MarkedBlowupSequenceData.append_ideal]
    rcases Nat.eq_zero_or_pos t.length with hz | hpos
    · have hle : s.length + t.length ≤ s.length := by omega
      have hobj : (s.appendToBlowupSequenceData t).obj (s.length + t.length) = s.obj (s.length + t.length) :=
        MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_of_le_length s t hle
      rw [MarkedBlowupSequenceData.appendIdeal_of_le_length s t hle]
      exact orderAtLeastLocus_comap_iso_eq_empty_consolidated449 (eqToIso hobj) _ _ (hs hz _ (by omega))
    · have hgt : s.length < s.length + t.length := by omega
      have hobj : (s.appendToBlowupSequenceData t).obj (s.length + t.length)
          = t.obj (s.length + t.length - s.length) :=
        MarkedBlowupSequenceData.appendToBlowupSequenceData_schemeAt_of_length_lt s t hgt
      rw [MarkedBlowupSequenceData.appendIdeal_of_length_lt s t hgt]
      exact orderAtLeastLocus_comap_iso_eq_empty_consolidated449 (eqToIso hobj) _ _ (ht _ (by omega))
  exact key _ (MarkedBlowupSequenceData.append_length s t hinv)

section
variable (hstar : MaxContactCoverProperties.{u})
include hstar

private theorem orderAtLeastLocus_derivedTriple_ideal_length_eq_empty_consolidated449 (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (S : MarkedIdealWithBoundary.{u}) (hSV : S.IsAdmissible) (hmS : 1 ≤ S.mult)
    (hSO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hsm : Smooth (s.proj s.length ≫ S.structMap))
    (Hc : (s.obj s.length).IdealSheafData)
    (hHc : @IsMaxContactHypersurface S.base _ (s.obj s.length)
      (s.proj s.length ≫ S.structMap) hft (s.ideal s.length) S.mult Hc)
    (keep : ℕ)
    (hVc : (MaxContactCoverData.derivedTriple S s hft [Hc] keep).IsAdmissible)
    (hPdim : P (MaxContactCoverData.derivedTriple S s hft [Hc] keep).krullDimSucc)
    (hN : ∀ i ≤ (MarkedBlowupSequenceData.ofMarkedSequence
          (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).toBlowupSequenceData.length,
        IsLocallyNoetherian
          ((MarkedBlowupSequenceData.ofMarkedSequence
            (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).toBlowupSequenceData.obj i)) :
    ∀ i : ℕ, i = (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep)).length →
      orderAtLeastLocus ((A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep)).ideal i)
        (MaxContactCoverData.derivedTriple S s hft [Hc] keep).mult = ∅ := by
  rintro i rfl
  have := hft
  have := hsm
  have : CharZero S.base := hSV.charZero
  have hOB : (MaxContactCoverData.derivedTriple S s hft [Hc] keep).IsOrderBoundedByMult :=
    LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hSV hmS hSO s hft [Hc] keep hVc
  have hbalanced : (MaxContactCoverData.derivedTriple S s hft [Hc] keep).IsBalanced hVc.locallyOfFiniteType :=
    LowerDimReductionPullback.isBalanced_derivedTriple hstar S hSV hmS hSO s hft [Hc] keep hVc
  have hj : 0 < (MaxContactCoverData.derivedTriple S s hft [Hc] keep).boundary.length := by
    rw [MaxContactCoverData.derivedTriple_boundary]
    simp
  obtain ⟨Dv, bv, _, hDvEq, _, hBoundaryOfMem, hBoundaryOfLt, hBoundaryEq, _⟩ :=
    (hspec 0).shape (MaxContactCoverData.derivedTriple S s hft [Hc] keep) hVc hPdim hOB hbalanced hj
  have htuned : @IsMaxContactHypersurface S.base _ (s.obj s.length)
      (s.proj s.length ≫ S.structMap) hft (LowerDimReductionPullback.tunedIdealAtLength S s hft) (tuningExponent S.mult) Hc :=
    isMaxContactHypersurface_balancedTunedSheaf hstar S.base (s.proj s.length ≫ S.structMap)
      (s.ideal s.length) S.mult hmS (LowerDimReductionPullback.orderAt_ideal_length_le hstar S hSV hSO s) Hc hHc
  have hadm2 : @IsMaxContactHypersurface (MaxContactCoverData.derivedTriple S s hft [Hc] keep).base _
      (MaxContactCoverData.derivedTriple S s hft [Hc] keep).scheme
      (MaxContactCoverData.derivedTriple S s hft [Hc] keep).structMap hVc.locallyOfFiniteType
      (MaxContactCoverData.derivedTriple S s hft [Hc] keep).ideal
      (MaxContactCoverData.derivedTriple S s hft [Hc] keep).mult Hc := by
    rw [MaxContactCoverData.derivedTriple_mult]
    exact @isMaxContactHypersurface_of_eq_of_eq_of_eq S.base _ (s.obj s.length)
      (s.proj s.length ≫ S.structMap)
      (MaxContactCoverData.derivedTriple S s hft [Hc] keep).structMap hft hVc.locallyOfFiniteType
      (LowerDimReductionPullback.tunedIdealAtLength S s hft) (MaxContactCoverData.derivedTriple S s hft [Hc] keep).ideal Hc Hc
      (tuningExponent S.mult)
      (MaxContactCoverData.derivedTriple_structureMorphism S s hft [Hc] keep).symm
      (LowerDimReductionPullback.ideal_derivedTriple S s hft [Hc] keep).symm rfl htuned
  have hordT : ∀ x : ↥(MaxContactCoverData.derivedTriple S s hft [Hc] keep).scheme,
      orderAt (MaxContactCoverData.derivedTriple S s hft [Hc] keep).ideal x
        ≤ (((MaxContactCoverData.derivedTriple S s hft [Hc] keep).mult : ℕ) : ℕ∞) :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff _).1 hOB
  have : CharZero (MaxContactCoverData.derivedTriple S s hft [Hc] keep).base := hVc.charZero
  have hftL := locallyOfFiniteType_projectionToBase_comp hstar (MaxContactCoverData.derivedTriple S s hft [Hc] keep)
    hVc (MarkedBlowupSequenceData.ofMarkedSequence (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep)))
    (MarkedBlowupSequenceData.ofMarkedSequence
      (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).length (le_refl _)
  have hsmL := smooth_projectionToBase_comp hstar (MaxContactCoverData.derivedTriple S s hft [Hc] keep)
    hVc (MarkedBlowupSequenceData.ofMarkedSequence (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep)))
    (MarkedBlowupSequenceData.ofMarkedSequence
      (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).length (le_refl _)
  have hadmL := isMaxContactHypersurface_iteratedStrictTransform hstar
    (MaxContactCoverData.derivedTriple S s hft [Hc] keep) hVc hordT Hc hadm2
    (MarkedBlowupSequenceData.ofMarkedSequence (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep)))
    (MarkedBlowupSequenceData.ofMarkedSequence
      (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).length (le_refl _)
  have hsub1 := @orderAtLeastLocus_subset_support_of_isMaxContactHypersurface_consolidated449
    (MaxContactCoverData.derivedTriple S s hft [Hc] keep).base _ _ _
    ((MarkedBlowupSequenceData.ofMarkedSequence (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).proj
        (MarkedBlowupSequenceData.ofMarkedSequence
          (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).length ≫
      (MaxContactCoverData.derivedTriple S s hft [Hc] keep).structMap) hsmL hftL
    ((MarkedBlowupSequenceData.ofMarkedSequence (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).ideal
      (MarkedBlowupSequenceData.ofMarkedSequence
        (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).length)
    (MaxContactReduction.iteratedStrictTransform
      (MarkedBlowupSequenceData.ofMarkedSequence (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))) Hc
      (MarkedBlowupSequenceData.ofMarkedSequence
        (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).length)
    (MaxContactCoverData.derivedTriple S s hft [Hc] keep).mult hVc.one_le_mult hadmL
  have h0 : Dv 0 = Hc.comap (MarkedBlowupSequenceData.ofMarkedSequence
      (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).toBlowupSequenceData.isoZero.hom := by
    rw [hDvEq]
    rfl
  have hstep : ∀ tt : ℕ, tt < (MarkedBlowupSequenceData.ofMarkedSequence
        (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).toBlowupSequenceData.length →
      Dv (tt + 1) = Blowup.strictTransform
          ((MarkedBlowupSequenceData.ofMarkedSequence
            (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).toBlowupSequenceData.map tt)
          ((MarkedBlowupSequenceData.ofMarkedSequence
            (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).toBlowupSequenceData.center tt) (Dv tt) ∨
        Dv (tt + 1) = (Dv tt).comap
          ((MarkedBlowupSequenceData.ofMarkedSequence
            (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).toBlowupSequenceData.map tt) := by
    intro tt htt
    by_cases hb : bv = true ∧ tt = 0
    · obtain ⟨hb1, hb2⟩ := hb
      subst hb2
      exact Or.inr (hBoundaryOfMem hb1).2.2
    · exact Or.inl (hBoundaryOfLt tt htt hb)
  have hsub2raw := BlowupSequenceData.support_iteratedStrictTransform_subset_support
    (MarkedBlowupSequenceData.ofMarkedSequence
      (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).toBlowupSequenceData hN Hc Dv h0 hstep
    (MarkedBlowupSequenceData.ofMarkedSequence
      (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep))).length (le_refl _)
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hx2 := mem_support_toBlowupSequenceData_iteratedStrictTransform_consolidated449 _ _ _ _ (hsub1 hx)
  have hmem : x ∈ orderAtLeastLocus (MarkedSequenceOfBlowups.lastIdeal
        (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep)))
        (MaxContactCoverData.derivedTriple S s hft [Hc] keep).mult ∩
      (((Dv (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep)).length).support) :
        Set ↥((A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep)).schemeAt
          (A 0 (MaxContactCoverData.derivedTriple S s hft [Hc] keep)).length)) :=
    ⟨hx, hsub2raw hx2⟩
  rw [hBoundaryEq] at hmem
  exact hmem

theorem orderAtLeastLocus_coverMarkedBlowupData_eq_empty (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u})
    (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T) :
    orderAtLeastLocus
        ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).ideal
          (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).length)
        (MaxContactCoverData.tunedMult T) = ∅ := by
  obtain ⟨hft, hVc, hPdim, hmk, heq, hcs⟩ := exists_cover_eq_separateAllBoundary_append hstar hinv P hmono A B hspec T h
  have hScV : (MaxContactCoverData.coverTriple T h.valid).IsAdmissible := isAdmissible_coverTriple hstar P T h
  have hScO := orderAt_coverTriple_ideal_le_mult hstar P T h
  have hsmS : Smooth
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap) :=
    smooth_projectionToBase_comp hstar (MaxContactCoverData.coverTriple T h.valid) hScV
      (separateAllBoundary T h.valid hinv A) (separateAllBoundary T h.valid hinv A).length (le_refl _)
  have hadm0 : @IsMaxContactHypersurface (MaxContactCoverData.coverTriple T h.valid).base _
      ((separateAllBoundary T h.valid hinv A).obj (separateAllBoundary T h.valid hinv A).length)
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap) hft
      ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
      (MaxContactCoverData.coverTriple T h.valid).mult
      (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)) :=
    isMaxContactHypersurface_iteratedStrictTransform hstar (MaxContactCoverData.coverTriple T h.valid) hScV hScO
      (MaxContactCoverData.coverMaxContactIdeal T h.valid) (isMaxContactHypersurface_coverMaxContactIdeal hstar P T h)
      (separateAllBoundary T h.valid hinv A) (separateAllBoundary T h.valid hinv A).length (le_refl _)
  have hNo : ∀ i ≤ (MarkedBlowupSequenceData.ofMarkedSequence
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft))).toBlowupSequenceData.length,
      IsLocallyNoetherian
        ((MarkedBlowupSequenceData.ofMarkedSequence
          (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft))).toBlowupSequenceData.obj i) := by
    intro i hi
    exact isLocallyNoetherian_tunedMarkedBlowupSeq_schemeAt hstar (MaxContactCoverData.coverTriple T h.valid) hScV
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length hVc
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) i hi
  have hlow := orderAtLeastLocus_derivedTriple_ideal_length_eq_empty_consolidated449 hstar P A B hspec
    (MaxContactCoverData.coverTriple T h.valid) hScV hScV.one_le_mult hScO
    (separateAllBoundary T h.valid hinv A) hft hsmS
    (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
      (MaxContactCoverData.coverMaxContactIdeal T h.valid)) hadm0
    (MaxContactCoverData.coverTriple T h.valid).boundary.length hVc hPdim hNo
  rw [heq, ← MaxContactCoverData.coverTriple_mult T h.valid]
  refine orderAtLeastLocus_append_eq_empty_consolidated449 (separateAllBoundary T h.valid hinv A)
    (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid) (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk) hinv
    (MaxContactCoverData.coverTriple T h.valid).mult ?_ ?_
  · rintro i rfl
    refine Eq.trans (hcs (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups.length
      (le_refl _)) ?_
    rw [← MaxContactCoverData.derivedTriple_mult (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length]
    exact hlow _ rfl
  · intro hz i hi
    subst hi
    refine orderAtLeastLocus_eq_empty_of_comap_iso_consolidated449
      (BlowupSequenceData.ofSequenceOfBlowups (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).isoZero
      _ _ ?_
    refine Eq.trans (hcs 0 (Nat.zero_le _)) ?_
    rw [← MaxContactCoverData.derivedTriple_mult (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length]
    exact hlow 0 hz.symm


end

section
variable {X Y : Scheme.{u}}

private theorem comap_ne_top_of_surjective_base_consolidated449 (f : Y ⟶ X)
    (hf : ∀ x : ↥X, ∃ y : ↥Y, f.base y = x) (J : X.IdealSheafData) (hJ : J ≠ ⊤) :
    J.comap f ≠ ⊤ := by
  intro htop
  refine hJ ((Scheme.IdealSheafData.eq_top_iff_support_eq_empty J).2 ?_)
  have h0 : ((J.comap f).support : Set ↥Y) = ∅ :=
    (Scheme.IdealSheafData.eq_top_iff_support_eq_empty (J.comap f)).1 htop
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨y, hy⟩ := hf x
  have h1 : (1 : ℕ∞) ≤ orderAt J (f.base y) := by
    rw [hy]
    exact (one_le_orderAt_iff_mem_support J x).2 hx
  have h2 : y ∈ ((J.comap f).support : Set ↥Y) :=
    (one_le_orderAt_iff_mem_support (J.comap f) y).1
      (le_trans h1 (orderAt_le_orderAt_comap f J y))
  rw [h0] at h2
  exact (Set.mem_empty_iff_false y).1 h2

private theorem exists_base_eqToHom_eq_consolidated449 (h : X = Y) (x : ↥Y) :
    ∃ y : ↥X, (CategoryTheory.eqToHom h).base y = x := by
  subst h
  refine ⟨x, ?_⟩
  simp

private theorem exists_base_iso_inv_eq_consolidated449 (e : X ≅ Y) (x : ↥X) :
    ∃ y : ↥Y, e.inv.base y = x :=
  ⟨e.hom.base x, congrArg (fun f : X ⟶ X => f.base x) e.hom_inv_id⟩


end

private theorem length_pos_of_eq_cons_consolidated449 {α : Type*} {L : List α} {a : α} {M : List α}
    (h : L = a :: M) : 0 < L.length := by
  subst h
  exact Nat.succ_pos _

private theorem center_append_ne_top_consolidated449 {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (hinv : ComapIsoInvariance.{u})
    (hs : ∀ i < s.length, s.center i ≠ ⊤)
    (ht : ∀ i < t.length, t.center i ≠ ⊤) :
    ∀ i < (s.append t hinv).length, (s.append t hinv).center i ≠ ⊤ := by
  intro i hi
  rw [MarkedBlowupSequenceData.append_length] at hi
  rw [MarkedBlowupSequenceData.append_toBlowupSequenceData]
  rcases lt_trichotomy i s.length with hlt | hmid | hgt
  · rw [MarkedBlowupSequenceData.appendToBlowupSequenceData_center_of_lt_length s t hlt]
    exact comap_ne_top_of_surjective_base_consolidated449 _ (exists_base_eqToHom_eq_consolidated449 _) _ (hs i hlt)
  · subst hmid
    rw [MarkedBlowupSequenceData.appendToBlowupSequenceData_center_length s t]
    refine comap_ne_top_of_surjective_base_consolidated449 _ (exists_base_eqToHom_eq_consolidated449 _) _ ?_
    refine comap_ne_top_of_surjective_base_consolidated449 _ (exists_base_iso_inv_eq_consolidated449 _) _ ?_
    exact ht 0 (by omega)
  · rw [MarkedBlowupSequenceData.appendToBlowupSequenceData_center_of_length_lt s t hgt]
    exact comap_ne_top_of_surjective_base_consolidated449 _ (exists_base_eqToHom_eq_consolidated449 _) _ (ht _ (by omega))

theorem center_coverMarkedBlowupData_ne_top (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u})
    (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T) :
    ∀ i < (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).length,
      (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).center i
        ≠ ⊤ := by
  obtain ⟨hft, hVc, hP, hmk, heq, _⟩ :=
    exists_cover_eq_separateAllBoundary_append hstar hinv P hmono A B hspec T h
  have hV : (MaxContactCoverData.coverTriple T h.valid).IsAdmissible := isAdmissible_coverTriple hstar P T h
  have hO := orderAt_coverTriple_ideal_le_mult hstar P T h
  have hOB : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).IsOrderBoundedByMult :=
    LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar (MaxContactCoverData.coverTriple T h.valid) hV
      hV.one_le_mult hO (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length hVc
  have hbalanced : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).IsBalanced hVc.locallyOfFiniteType :=
    LowerDimReductionPullback.isBalanced_derivedTriple hstar (MaxContactCoverData.coverTriple T h.valid) hV
      hV.one_le_mult hO (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length hVc
  have hb : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).boundary =
      MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid) ::
        ((separateAllBoundary T h.valid hinv A).boundary
          (separateAllBoundary T h.valid hinv A).length).drop
            (MaxContactCoverData.coverTriple T h.valid).boundary.length :=
    MaxContactCoverData.derivedTriple_boundary (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length
  have hbd : 0 < (reduceAlongHypersurfaceTriple T h.valid hinv A hft).boundary.length :=
    length_pos_of_eq_cons_consolidated449 hb
  have hcn := (hspec 0).center_nonempty (reduceAlongHypersurfaceTriple T h.valid hinv A hft) hVc hP hOB hbalanced hbd
  have hfacts := separateBoundaryInvariant_separateBoundarySeq hstar hinv P hmono A B hspec T h
    (MaxContactCoverData.coverTriple T h.valid).boundary.length (le_refl _)
  rw [heq]
  refine center_append_ne_top_consolidated449 _ _ _ (And.left (And.right hfacts)) ?_
  intro i hi htop
  have hi' : i < (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).length := hi
  exact (hcn i hi').ne_empty
    ((Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).1 htop)

end BoundarySeparationByMaxContact

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverPieces
section

open CategoryTheory.Limits

section
namespace FunctorialResolution.EmbeddedResolution.MaxContactCoverGeometry

private theorem map_iInf_of_bijective_consolidated445 {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Bijective φ) {ι : Type*} (K : ι → Ideal A) :
    Ideal.map φ (⨅ i, K i) = ⨅ i, Ideal.map φ (K i) :=
  (Ideal.relIsoOfBijective φ hφ).symm.map_iInf K

private theorem bijective_appLE_image_consolidated445 {A B : Scheme.{u}} (g : A ⟶ B) [IsOpenImmersion g]
    (S : A.Opens) (e : S ≤ g ⁻¹ᵁ (g ''ᵁ S)) :
    Function.Bijective (CommRingCat.Hom.hom (Scheme.Hom.appLE g (g ''ᵁ S) S e)) := by
  have : IsIso (Scheme.Hom.appLE g (g ''ᵁ S) S e) := by
    rw [← Scheme.Hom.appIso_hom' g S]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso _

private theorem ideal_iInf_consolidated445 {X : Scheme.{u}} {ι : Type v} [Finite ι]
    (I : ι → X.IdealSheafData) (U : X.affineOpens) :
    (⨅ i, I i).ideal U = ⨅ i, (I i).ideal U := by
  simp only [AlgebraicGeometry.Scheme.IdealSheafData.ideal_iInf, iInf_apply]

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

theorem comap_iInf {ι : Type v} [Finite ι] (J : ι → Y.IdealSheafData) :
    (⨅ i, J i).comap f = ⨅ i, (J i).comap f := by
  refine Scheme.IdealSheafData.ext ?_
  funext V
  have hU : IsAffineOpen (f ''ᵁ (V : X.Opens)) := V.2.image_of_isOpenImmersion f
  have e : (V : X.Opens) ≤ f ⁻¹ᵁ (f ''ᵁ (V : X.Opens)) :=
    (f.preimage_image_eq (V : X.Opens)).ge
  have hbij : Function.Bijective
      (f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e).hom :=
    bijective_appLE_image_consolidated445 f (V : X.Opens) e
  have key : ∀ I : Y.IdealSheafData, (I.comap f).ideal V =
      (I.ideal ⟨f ''ᵁ (V : X.Opens), hU⟩).map
        (f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e).hom := fun I =>
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE I f ⟨f ''ᵁ (V : X.Opens), hU⟩ V e
  have h1 : (⨅ i, J i).ideal ⟨f ''ᵁ (V : X.Opens), hU⟩
      = ⨅ i, (J i).ideal ⟨f ''ᵁ (V : X.Opens), hU⟩ :=
    ideal_iInf_consolidated445 J ⟨f ''ᵁ (V : X.Opens), hU⟩
  have h2 : (⨅ i, (J i).comap f).ideal V = ⨅ i, ((J i).comap f).ideal V :=
    ideal_iInf_consolidated445 (fun i => (J i).comap f) V
  rw [h2, key (⨅ i, J i), h1, map_iInf_of_bijective_consolidated445 _ hbij]
  exact iInf_congr fun i => (key (J i)).symm

theorem ker_subschemeι_comp_comap_self [QuasiCompact f]
    (I : X.IdealSheafData) :
    ((I.subschemeι ≫ f).ker).comap f = I :=
  FunctorialResolution.EmbeddedResolution.comap_ker_subschemeι_comp I f


end

theorem ker_subschemeι_comp_comap_eq_top_of_disjoint {X X' Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (g : X' ⟶ Y) [QuasiCompact g]
    (hdisj : ∀ (x : ↥X) (x' : ↥X'), f.base x ≠ g.base x') (J : X'.IdealSheafData) :
    ((J.subschemeι ≫ g).ker).comap f = ⊤ := by
  refine FunctorialResolution.Blowup.comap_eq_top_of_notMem_support f ((J.subschemeι ≫ g).ker) ?_
  intro x hx
  have hx' : f.base x ∈ (((J.subschemeι ≫ g).ker).support : Set ↥Y) := hx
  rw [Scheme.Hom.support_ker] at hx'
  have hopen : IsOpen (Set.range ⇑f.base) := f.isOpenEmbedding.isOpen_range
  obtain ⟨y, hy1, hy2⟩ :=
    mem_closure_iff.mp hx' (Set.range ⇑f.base) hopen (Set.mem_range_self x)
  obtain ⟨x₀, hx₀⟩ := hy1
  obtain ⟨w, hw⟩ := hy2
  have hwe : g.base (J.subschemeι.base w) = y := by
    rw [← hw]
    simp
  exact hdisj x₀ (J.subschemeι.base w) (hx₀.trans hwe.symm)

variable (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)

instance instIsClosedImmersionStarι (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    IsClosedImmersion (MaxContactOpenCover.coverPieceι T hv i) :=
  FunctorialResolution.Blowup.isClosedImmersion_sigmaι
    (fun j : (MaxContactCoverData.chosenCoverData T hv).idx => MaxContactOpenCover.coverPiece T hv j) i

theorem quasiCompact_coverPieceι (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    QuasiCompact (MaxContactOpenCover.coverPieceι T hv i) :=
  FunctorialResolution.Blowup.quasiCompact_sigmaι
    (fun j : (MaxContactCoverData.chosenCoverData T hv).idx => MaxContactOpenCover.coverPiece T hv j) i

instance instQuasiCompactStarι (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    QuasiCompact (MaxContactOpenCover.coverPieceι T hv i) :=
  quasiCompact_coverPieceι T hv i

theorem coverPieceι_base_ne_of_ne {i j : (MaxContactCoverData.chosenCoverData T hv).idx} (hij : i ≠ j)
    (x : ↥(MaxContactOpenCover.coverPiece T hv i)) (y : ↥(MaxContactOpenCover.coverPiece T hv j)) :
    (MaxContactOpenCover.coverPieceι T hv i).base x ≠ (MaxContactOpenCover.coverPieceι T hv j).base y :=
  FunctorialResolution.Blowup.sigmaι_base_ne
    (fun k : (MaxContactCoverData.chosenCoverData T hv).idx => MaxContactOpenCover.coverPiece T hv k) hij x y

theorem ker_subschemeι_comp_coverPieceι_comap_self (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    ((((MaxContactCoverData.chosenCoverData T hv).localIdeal i).subschemeι ≫
        MaxContactOpenCover.coverPieceι T hv i).ker).comap (MaxContactOpenCover.coverPieceι T hv i) =
      (MaxContactCoverData.chosenCoverData T hv).localIdeal i :=
  ker_subschemeι_comp_comap_self (MaxContactOpenCover.coverPieceι T hv i) _

theorem ker_subschemeι_comp_coverPieceι_comap_of_ne {i j : (MaxContactCoverData.chosenCoverData T hv).idx} (hij : i ≠ j) :
    ((((MaxContactCoverData.chosenCoverData T hv).localIdeal j).subschemeι ≫
        MaxContactOpenCover.coverPieceι T hv j).ker).comap (MaxContactOpenCover.coverPieceι T hv i) = ⊤ :=
  ker_subschemeι_comp_comap_eq_top_of_disjoint (MaxContactOpenCover.coverPieceι T hv i) (MaxContactOpenCover.coverPieceι T hv j)
    (coverPieceι_base_ne_of_ne T hv hij) _

theorem comap_coverMaxContactIdeal_coverPieceι (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    (MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i) =
      (MaxContactCoverData.chosenCoverData T hv).localIdeal i := by
  have key : (⨅ j : (MaxContactCoverData.chosenCoverData T hv).idx,
      (((MaxContactCoverData.chosenCoverData T hv).localIdeal j).subschemeι ≫
        MaxContactOpenCover.coverPieceι T hv j).ker).comap (MaxContactOpenCover.coverPieceι T hv i) =
      (MaxContactCoverData.chosenCoverData T hv).localIdeal i := by
    rw [comap_iInf]
    refine le_antisymm (le_trans (iInf_le _ i) (le_of_eq (ker_subschemeι_comp_coverPieceι_comap_self T hv i)))
      (le_iInf fun j => ?_)
    rcases eq_or_ne j i with rfl | h
    · exact le_of_eq (ker_subschemeι_comp_coverPieceι_comap_self T hv _).symm
    · rw [ker_subschemeι_comp_coverPieceι_comap_of_ne T hv h.symm]
      exact le_top
  exact key

theorem isMaxContactHypersurface_coverMaxContactIdeal
    [LocallyOfFiniteType (MaxContactCoverData.coverTriple T hv).structMap]
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)) :
    IsMaxContactHypersurface (MaxContactCoverData.coverTriple T hv).base
      (MaxContactCoverData.coverTriple T hv).structMap (MaxContactCoverData.coverTriple T hv).ideal
      (MaxContactCoverData.tunedMult T) (MaxContactCoverData.coverMaxContactIdeal T hv) :=
  FunctorialResolution.EmbeddedResolution.isMaxContactHypersurface_coverMaxContactIdeal_of_comap_eq T hv hgood (comap_coverMaxContactIdeal_coverPieceι T hv)

section
variable (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
include hgood

theorem inStrictNormalCrossingPositionAt_of_isMaxContactCover
    (x : ↥(MaxContactCoverData.coverTriple T hv).scheme) :
    InStrictNormalCrossingPositionAt (MaxContactCoverData.coverTriple T hv).structMap
      [MaxContactCoverData.coverMaxContactIdeal T hv] x :=
  FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPositionAt_coverMaxContactIdeal T hv hgood (comap_coverMaxContactIdeal_coverPieceι T hv) x

theorem inStrictNormalCrossingPosition_of_isMaxContactCover
    (hsm : IsSmoothDivisor (MaxContactCoverData.coverTriple T hv).structMap
      (MaxContactCoverData.coverMaxContactIdeal T hv)) :
    InStrictNormalCrossingPosition (MaxContactCoverData.coverTriple T hv).structMap
      [MaxContactCoverData.coverMaxContactIdeal T hv] :=
  FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPosition_coverMaxContactIdeal T hv hgood (comap_coverMaxContactIdeal_coverPieceι T hv) hsm


end

end FunctorialResolution.EmbeddedResolution.MaxContactCoverGeometry

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MultiplicityOneCover
section


namespace FunctorialResolution.EmbeddedResolution

private theorem balancedTunedSheaf_eq_self_of_mult_eq_one_consolidated447 (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (pp : X ⟶ Spec (CommRingCat.of k)) [Smooth pp]
    [LocallyOfFiniteType pp] (I : X.IdealSheafData) (m : ℕ) (hm : m = 1) :
    balancedTunedSheaf k pp I m = I := by
  subst hm
  exact balancedTunedSheaf_one k pp I

private theorem markedIdealWithBoundary_mk_congr_consolidated447 {k : Type u} [Field k] {X : Scheme.{u}}
    {p p' : X ⟶ Spec (CommRingCat.of k)} {I I' : X.IdealSheafData} {m m' : ℕ}
    {E E' : List X.IdealSheafData}
    (hp : p = p') (hI : I = I') (hm : m = m') (hE : E = E') :
    MarkedIdealWithBoundary.mk k X p I m E = MarkedIdealWithBoundary.mk k X p' I' m' E' := by
  subst hp
  subst hI
  subst hm
  subst hE
  rfl

section
variable (S : MarkedIdealWithBoundary.{u})

private theorem projectionToBase_emptyMarkedBlowupSequenceData_comp_consolidated447 :
    (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).proj
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length ≫ S.structMap
      = S.structMap :=
  Category.id_comp S.structMap

private theorem structureMorphism_derivedTriple_emptyMarkedBlowupSequenceData_consolidated447 (hft : LocallyOfFiniteType
      ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).proj
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length ≫ S.structMap))
    (extra : List ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).obj
      (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length).IdealSheafData)
    (keep : ℕ) :
    (MaxContactCoverData.derivedTriple S (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) hft
      extra keep).structMap = S.structMap := by
  rw [MaxContactCoverData.derivedTriple_structureMorphism]
  exact projectionToBase_emptyMarkedBlowupSequenceData_comp_consolidated447 S

private theorem ideal_derivedTriple_emptyMarkedBlowupSequenceData_consolidated447 (hcz : CharZero S.base)
    (h1 : S.mult = 1)
    (hft : LocallyOfFiniteType
      ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).proj
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length ≫ S.structMap))
    (hsm : Smooth
      ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).proj
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length ≫ S.structMap))
    (extra : List ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).obj
      (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length).IdealSheafData)
    (keep : ℕ) :
    (MaxContactCoverData.derivedTriple S (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) hft
      extra keep).ideal = S.ideal := by
  have := hcz
  have := hft
  have := hsm
  rw [LowerDimReductionPullback.ideal_derivedTriple]
  exact Eq.trans
    (balancedTunedSheaf_eq_self_of_mult_eq_one_consolidated447 S.base
      ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).proj
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length ≫ S.structMap)
      ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).ideal
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length) S.mult h1)
    (emptyMarkedBlowupSequenceData_ideal S.structMap S.ideal S.mult S.boundary
      (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length)

private theorem mult_derivedTriple_emptyMarkedBlowupSequenceData_consolidated447 (h1 : S.mult = 1)
    (hft : LocallyOfFiniteType
      ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).proj
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length ≫ S.structMap))
    (extra : List ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).obj
      (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length).IdealSheafData)
    (keep : ℕ) :
    (MaxContactCoverData.derivedTriple S (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) hft
      extra keep).mult = 1 := by
  rw [MaxContactCoverData.derivedTriple_mult, h1]
  exact tuningExponent_one

private theorem boundary_derivedTriple_emptyMarkedBlowupSequenceData_consolidated447 (hft : LocallyOfFiniteType
      ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).proj
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length ≫ S.structMap))
    (extra : List ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).obj
      (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length).IdealSheafData) :
    (MaxContactCoverData.derivedTriple S (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) hft
      extra S.boundary.length).boundary = extra := by
  have hB : (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).boundary
      (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length = S.boundary :=
    emptyMarkedBlowupSequenceData_boundary S.structMap S.ideal S.mult S.boundary
      (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length
  have hdrop : List.drop S.boundary.length
      ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).boundary
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length) = [] := by
    rw [hB]
    simp
  rw [MaxContactCoverData.derivedTriple_boundary, hdrop]
  exact List.append_nil extra


end

private theorem isomorphic_of_emptyMarkedBlowupSequenceData_append_consolidated447 {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData)
    (t : MarkedBlowupSequenceData
      ((emptyMarkedBlowupSequenceData p I m E).proj (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length ≫ p)
      ((emptyMarkedBlowupSequenceData p I m E).ideal (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length) m
      ((emptyMarkedBlowupSequenceData p I m E).boundary (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length))
    (hinv : ComapIsoInvariance.{u}) :
    ((emptyMarkedBlowupSequenceData p I m E).append t hinv).toSequenceOfBlowups.Isomorphic t.toSequenceOfBlowups := by
  have hmain := MarkedBlowupSequenceData.emptyMarkedBlowupSequenceData_append_isomorphic p I m E t hinv
  have e1 := MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups ((emptyMarkedBlowupSequenceData p I m E).append t hinv)
  have e2 := MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups t
  rw [e1, e2] at hmain
  exact hmain

section
variable (k : Type u) [Field k] [CharZero k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p] (A : P.IdealSheafData)

private theorem derivIdealSheaf_eq_top_of_orderAt_le_one_consolidated447 (hord : ∀ x : ↥P, orderAt A x ≤ ((1 : ℕ) : ℕ∞)) :
    derivIdealSheaf k p A = ⊤ := by
  have hempty : orderAtLeastLocus A 2 = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have h2 : ((2 : ℕ) : ℕ∞) ≤ orderAt A x := (mem_orderAtLeastLocus_iff A 2 x).1 hx
    have h21 : ((2 : ℕ) : ℕ∞) ≤ ((1 : ℕ) : ℕ∞) := le_trans h2 (hord x)
    have h21' : (2 : ℕ) ≤ 1 := by exact_mod_cast h21
    omega
  have h := orderAtLeastLocus_derivIdealSheafIterate k p A (r := 1) (m := 2) (by norm_num)
  rw [hempty] at h
  have h1 : orderAtLeastLocus (derivIdealSheafIterate k p 1 A) 1 = ∅ := h
  have hiter : derivIdealSheaf k p A = derivIdealSheafIterate k p 1 A := rfl
  rw [hiter]
  refine (AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).2 ?_
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  have hy1 : y ∈ orderAtLeastLocus (derivIdealSheafIterate k p 1 A) 1 :=
    (mem_orderAtLeastLocus_one_iff _ y).2 hy
  rw [h1] at hy1
  exact hy1

private theorem isMaxContactInvariant_of_mult_eq_one_consolidated447 (m : ℕ) (hm : m = 1)
    (hord : ∀ x : ↥P, orderAt A x ≤ ((1 : ℕ) : ℕ∞)) :
    IsMaxContactInvariant k p A m := by
  subst hm
  unfold FunctorialResolution.EmbeddedResolution.IsMaxContactInvariant
  rw [derivIdealSheaf_eq_top_of_orderAt_le_one_consolidated447 k p A hord]
  have hmc : maxContactIdeal k p A 1 = A := rfl
  rw [hmc]
  simp


end

private theorem coordIdeal_comp_map_eq_comap_consolidated447 {X Y : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k)}
    {U : X.Opens} {V : Y.Opens} {n : ℕ} (c : EtaleChart p U n)
    (φ : (V : Scheme.{u}) ⟶ (U : Scheme.{u}))
    (hcs : (φ ≫ c.map) ≫ affineSpaceFinToSpec k n = V.ι ≫ q)
    (he : Etale (φ ≫ c.map)) (S : Finset (Fin n)) :
    (⟨φ ≫ c.map, hcs, he⟩ : EtaleChart q V n).coordIdeal S = (c.coordIdeal S).comap φ := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  show (coordSubspaceIdeal k n S).comap (φ ≫ c.map)
      = ((coordSubspaceIdeal k n S).comap c.map).comap φ
  rw [Scheme.IdealSheafData.comap_comp]

section
variable {k : Type u} [Field k] [CharZero k]

theorem isMaxContactHypersurface_one_of_etaleChart {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p]
    [LocallyOfFiniteType p] (A D : P.IdealSheafData)
    (hchart : ∀ x : ↥P, x ∈ D.support →
      ∃ (U : P.Opens) (n : ℕ) (c : EtaleChart p U n) (j : Fin n),
        x ∈ U ∧ restrictIdeal D U = c.coordIdeal ({j} : Finset (Fin n)))
    (hDle : D ≤ A) :
    IsMaxContactHypersurface k p A 1 D := by
  intro x
  by_cases hx : x ∈ D.support
  · obtain ⟨U, n, c, j, hxU, hcoord⟩ := hchart x hx
    obtain ⟨V, hVaff, hxV, hVU⟩ :
        ∃ V : P.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U :=
      exists_isAffineOpen_mem_and_subset hxU
    refine ⟨V, hVaff, hxV, Or.inr ⟨n, c.restrict hVU, j, ?_, ?_⟩⟩
    · exact restrictIdeal_eq_restrict_coordIdeal_of_le hVU c D ({j} : Finset (Fin n)) hcoord
    · rw [isMaxContactCoord_one_iff,
        ← restrictIdeal_eq_restrict_coordIdeal_of_le hVU c D ({j} : Finset (Fin n)) hcoord,
        restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι]
      exact Scheme.IdealSheafData.comap_mono _ hDle
  · have hclosed : IsClosed ((D.support : Set ↥P)) := D.support.isClosed
    obtain ⟨V, hVaff, hxV, hVW⟩ :
        ∃ V : P.Opens, IsAffineOpen V ∧ x ∈ V ∧
          V ≤ (⟨((D.support : Set ↥P))ᶜ, hclosed.isOpen_compl⟩ : P.Opens) :=
      exists_isAffineOpen_mem_and_subset hx
    have hdisj : Disjoint ((D.support : Set ↥P)) ((V : Set ↥P)) := by
      rw [Set.disjoint_right]
      intro y hyV hyD
      exact (hVW hyV) hyD
    have htop : restrictIdeal D V = ⊤ :=
      (FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_top_iff_forall_notMem_support _ _).mpr
        (fun y hyV hyD => Set.disjoint_left.mp hdisj hyD hyV)
    refine ⟨V, hVaff, hxV, Or.inl ⟨?_, htop⟩⟩
    rw [Set.disjoint_left]
    intro y hy hyV
    have h1 : y ∈ D.support :=
      (one_le_orderAt_iff_mem_support D y).1
        (le_trans ((one_le_orderAt_iff_mem_support A y).2 ((mem_orderAtLeastLocus_one_iff A y).1 hy))
          (orderAt_le_of_le hDle y))
    exact (Set.disjoint_left.mp hdisj h1) hyV

theorem IsMaxContactHypersurface.comap_of_isOpenImmersionAtSource {P P' : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p]
    [LocallyOfFiniteType p] {A H : P.IdealSheafData}
    (hH : IsMaxContactHypersurface k p A 1 H) (g : P' ⟶ P) [Smooth g]
    [LocallyOfFiniteType (g ≫ p)]
    (hg : MaxContactFunctoriality.IsLocalIsomorphism g) :
    IsMaxContactHypersurface k (g ≫ p) (A.comap g) 1 (H.comap g) := by
  have : Smooth (g ≫ p) := inferInstance
  intro x'
  obtain ⟨U₀, hxU₀, hoi⟩ := hg x'
  have := hoi
  obtain ⟨U, _, hxU, hcase⟩ := hH (g.base x')
  have hxpre : x' ∈ (g ⁻¹ᵁ U) := hxU
  obtain ⟨V, hVaff, hxV, hVW⟩ :
      ∃ V : P'.Opens, IsAffineOpen V ∧ x' ∈ V ∧ V ≤ U₀ ⊓ (g ⁻¹ᵁ U) :=
    exists_isAffineOpen_mem_and_subset (⟨hxU₀, hxpre⟩ : x' ∈ U₀ ⊓ (g ⁻¹ᵁ U))
  have hVU₀ : V ≤ U₀ := le_trans hVW inf_le_left
  have hVpre : V ≤ (g ⁻¹ᵁ U) := le_trans hVW inf_le_right
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = P'.homOfLE hVpre ≫ (g ∣_ U) := ⟨_, rfl⟩
  have hfac : V.ι ≫ g = φ ≫ U.ι := by
    rw [hφ, Category.assoc, morphismRestrict_ι, ← Category.assoc, P'.homOfLE_ι]
  have hoiV : IsOpenImmersion (V.ι ≫ g) := by
    have hrw : V.ι ≫ g = P'.homOfLE hVU₀ ≫ (U₀.ι ≫ g) := by
      rw [← Category.assoc, P'.homOfLE_ι]
    rw [hrw]
    infer_instance
  have : IsOpenImmersion (φ ≫ U.ι) := by
    rw [← hfac]
    exact hoiV
  have : IsOpenImmersion φ :=
    AlgebraicGeometry.IsOpenImmersion.of_comp φ U.ι
  have : Etale φ := inferInstance
  have hcomapres : ∀ J : P.IdealSheafData,
      restrictIdeal (J.comap g) V = (restrictIdeal J U).comap φ := by
    intro J
    rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, hfac]
  refine ⟨V, hVaff, hxV, ?_⟩
  rcases hcase with ⟨hdisj, htop⟩ | ⟨n, c, j, hcoord, hmc⟩
  · refine Or.inl ⟨?_, ?_⟩
    · rw [orderAtLeastLocus_comap k p g A 1, Set.disjoint_left]
      intro y hy hyV
      exact (Set.disjoint_left.mp hdisj hy) (hVpre hyV)
    · rw [hcomapres H, htop]
      simp
  · have := c.isEtale
    have hcs : (φ ≫ c.map) ≫ affineSpaceFinToSpec k n = V.ι ≫ (g ≫ p) := by
      rw [Category.assoc, c.comp_struct, ← Category.assoc, ← hfac, Category.assoc]
    have he : Etale (φ ≫ c.map) := inferInstance
    refine Or.inr ⟨n, ⟨φ ≫ c.map, hcs, he⟩, j, ?_, ?_⟩
    · rw [hcomapres H, hcoord, coordIdeal_comp_map_eq_comap_consolidated447 c φ hcs he]
    · rw [isMaxContactCoord_one_iff, coordIdeal_comp_map_eq_comap_consolidated447 c φ hcs he, hcomapres A]
      exact Scheme.IdealSheafData.comap_mono _ ((isMaxContactCoord_one_iff k p A c j).1 hmc)


end

private theorem isBalanced_of_eq_derivedTriple_emptyMarkedBlowupSequenceData_consolidated447 (hstar : MaxContactCoverProperties.{u})
    (S : MarkedIdealWithBoundary.{u}) (hSV : S.IsAdmissible)
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hft : LocallyOfFiniteType
      ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).proj
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length ≫ S.structMap))
    (L : List ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).obj
      (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length).IdealSheafData)
    (keep : ℕ) (D : MarkedIdealWithBoundary.{u})
    (hDeq : MaxContactCoverData.derivedTriple S
      (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) hft L keep = D)
    (hVD : D.IsAdmissible) :
    ∀ hft2 : LocallyOfFiniteType D.structMap, D.IsBalanced hft2 := by
  subst hDeq
  intro hft2
  exact LowerDimReductionPullback.isBalanced_derivedTriple hstar S hSV hSV.one_le_mult hord
    (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) hft L keep hVD

private theorem isomorphic_of_isMaxContactHypersurface_singleton_boundary_consolidated447 (hin : OrderReduction.OrderReductionHypotheses.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A0 B : PrincipalizationAssignment.{u})
    (hspec0 : IsBoundaryDivisorReduction P 0 A0 B) (S : MarkedIdealWithBoundary.{u})
    [CharZero S.base] [Smooth S.structMap]
    [LocallyOfFiniteType S.structMap]
    (hSV : S.IsAdmissible) (hP : P S.krullDimSucc)
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hm1 : S.mult = 1) (H₁ H₂ : S.scheme.IdealSheafData) (hbd : S.boundary = [H₁])
    (hD : ∀ hft2 : LocallyOfFiniteType S.structMap, S.IsBalanced hft2)
    (hV₂ : (S.withBoundary [H₂]).IsAdmissible)
    (hH₁ : IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H₁)
    (hH₂ : IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H₂) :
    (A0 S).toSequenceOfBlowups.Isomorphic (A0 (S.withBoundary [H₂])).toSequenceOfBlowups := by
  have hMC : ∀ [LocallyOfFiniteType S.structMap],
      IsMaxContactInvariant S.base S.structMap S.ideal S.mult := by
    intro _i
    refine isMaxContactInvariant_of_mult_eq_one_consolidated447 S.base S.structMap S.ideal S.mult hm1 ?_
    intro x
    have hx := hord x
    rw [hm1] at hx
    exact hx
  exact DivisorReductionIndependence.isomorphic_withBoundary_cons_of_isMaxContactHypersurface hin P hmono A0 B hspec0 S hSV hP hord hD hMC
    [] H₁ H₂ hbd hV₂ (by intro _i; exact hH₁) (by intro _i; exact hH₂)

namespace MaxContactCoverData

section
variable (hstar : MaxContactCoverProperties.{u}) (hin : OrderReduction.OrderReductionHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B) (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T) (hbd : T.boundary = []) (hmult : T.mult = 1) {Y : Scheme.{u}} (e : Y ⟶ T.scheme) [IsClosedImmersion e]
include hstar hin hmono hspec hbd hmult

private theorem isStrictPullbackBlowupSeq_cover_of_eq_append_consolidated447 (hadm : ∀ [LocallyOfFiniteType T.structMap],
      IsMaxContactHypersurface T.base T.structMap T.ideal T.mult
        (AlgebraicGeometry.Scheme.Hom.ker e))
    (hV : (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).IsAdmissible)
    (s : MarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
      (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
    (hs : s = emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
      (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
    (hft : LocallyOfFiniteType
      (s.proj s.length ≫ (coverTriple T h.valid).structMap))
    (hVc : (derivedTriple (coverTriple T h.valid) s hft
      [MaxContactReduction.strictTransformAtLength s (coverMaxContactIdeal T h.valid)]
      (coverTriple T h.valid).boundary.length).IsAdmissible)
    (hmk : (BlowupSequenceData.ofSequenceOfBlowups (A 0 (derivedTriple (coverTriple T h.valid) s hft
        [MaxContactReduction.strictTransformAtLength s (coverMaxContactIdeal T h.valid)]
        (coverTriple T h.valid).boundary.length)).toSequenceOfBlowups).IsMarked
      (s.proj s.length ≫ (coverTriple T h.valid).structMap) (s.ideal s.length)
      (coverTriple T h.valid).mult (s.boundary s.length))
    (heq : coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)
      = s.append ((BlowupSequenceData.ofSequenceOfBlowups (A 0 (derivedTriple (coverTriple T h.valid) s hft
          [MaxContactReduction.strictTransformAtLength s (coverMaxContactIdeal T h.valid)]
          (coverTriple T h.valid).boundary.length)).toSequenceOfBlowups).toMarkedBlowupSequenceData
        (s.proj s.length ≫ (coverTriple T h.valid).structMap) (s.ideal s.length)
        (coverTriple T h.valid).mult (s.boundary s.length) hmk) hinv) :
    IsStrictPullbackBlowupSeq (coverMap T h.valid)
      (coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).toSequenceOfBlowups
      (A 0 (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e])).toSequenceOfBlowups := by
  have := h.valid.locallyOfFiniteType
  have := h.valid.smooth
  have : CharZero T.base := h.valid.charZero
  subst hs
  have := hft
  have hVcover : (coverTriple T h.valid).IsAdmissible :=
    BoundarySeparationByMaxContact.isAdmissible_coverTriple hstar P T h
  have hftC : LocallyOfFiniteType (coverTriple T h.valid).structMap :=
    hVcover.locallyOfFiniteType
  have hsmC : Smooth (coverTriple T h.valid).structMap := hVcover.smooth
  have hczC : CharZero (coverTriple T h.valid).base := hVcover.charZero
  have hczPB : CharZero
      ((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
        (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
        (coverMap T h.valid)).base := h.valid.charZero
  have hsmPB : Smooth
      ((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
        (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
        (coverMap T h.valid)).structMap := hVcover.smooth
  have hftPB : LocallyOfFiniteType
      ((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
        (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
        (coverMap T h.valid)).structMap := hVcover.locallyOfFiniteType
  have hOcover := BoundarySeparationByMaxContact.orderAt_coverTriple_ideal_le_mult hstar P T h
  have hsm : Smooth
      ((emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).proj
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length ≫
        (coverTriple T h.valid).structMap) :=
    BoundarySeparationByMaxContact.smooth_projectionToBase_comp hstar (coverTriple T h.valid) hVcover
      (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
      (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length le_rfl
  have := hsm
  have htunedIdeal : balancedTunedIdeal T h.valid = T.ideal :=
    balancedTunedSheaf_eq_self_of_mult_eq_one_consolidated447 T.base T.structMap T.ideal T.mult hmult
  have hcoverMult : (coverTriple T h.valid).mult = 1 := by
    rw [coverTriple_mult]
    show FunctorialResolution.EmbeddedResolution.tuningExponent T.mult = 1
    rw [hmult]
    exact tuningExponent_one
  have hcoverIdeal : (coverTriple T h.valid).ideal = T.ideal.comap (coverMap T h.valid) := by
    rw [coverTriple_ideal, htunedIdeal]
  have hqc : QuasiCompact (coverTriple T h.valid).structMap :=
    hVcover.quasiCompact
  have hsurj : AlgebraicGeometry.Surjective (coverMap T h.valid) :=
    surjective_coverMap T h.valid (hstar.exists_goodCover T h.valid h.orderLE)
  have hftE : LocallyOfFiniteType
      ((emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).proj
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).length ≫ T.structMap) := by
    have hx : LocallyOfFiniteType T.structMap :=
      h.valid.locallyOfFiniteType
    rw [projectionToBase_emptyMarkedBlowupSequenceData_comp_consolidated447 T]
    exact hx
  have hsmE : Smooth
      ((emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).proj
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).length ≫ T.structMap) := by
    have hx : Smooth T.structMap := h.valid.smooth
    rw [projectionToBase_emptyMarkedBlowupSequenceData_comp_consolidated447 T]
    exact hx
  have hdrop0 : List.drop 0
      ((emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).boundary
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).length) = [] :=
    (congrArg (List.drop 0)
        (emptyMarkedBlowupSequenceData_boundary T.structMap T.ideal T.mult T.boundary
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).length)).trans
      ((congrArg (List.drop 0) hbd).trans rfl)
  have hbdE : (derivedTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hftE
      [AlgebraicGeometry.Scheme.Hom.ker e] 0).boundary
      = [AlgebraicGeometry.Scheme.Hom.ker e] := by
    rw [derivedTriple_boundary, hdrop0]
    exact List.append_nil [AlgebraicGeometry.Scheme.Hom.ker e]
  have hEqT : derivedTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hftE
      [AlgebraicGeometry.Scheme.Hom.ker e] 0
      = T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e] :=
    markedIdealWithBoundary_mk_congr_consolidated447
      (structureMorphism_derivedTriple_emptyMarkedBlowupSequenceData_consolidated447 T hftE [AlgebraicGeometry.Scheme.Hom.ker e] 0)
      (ideal_derivedTriple_emptyMarkedBlowupSequenceData_consolidated447 T h.valid.charZero hmult hftE hsmE
        [AlgebraicGeometry.Scheme.Hom.ker e] 0)
      ((mult_derivedTriple_emptyMarkedBlowupSequenceData_consolidated447 T hmult hftE
        [AlgebraicGeometry.Scheme.Hom.ker e] 0).trans hmult.symm)
      hbdE
  have hbalanced := isBalanced_of_eq_derivedTriple_emptyMarkedBlowupSequenceData_consolidated447 hstar T h.valid h.orderLE hftE
    [AlgebraicGeometry.Scheme.Hom.ker e] 0
    (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]) hEqT hV
  have hpb := DivisorReductionIndependence.isAdmissible_and_isStrictPullbackBlowupSeq_of_etale hin P hmono (A 0) B (hspec 0)
    (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]) hV h.dim_prop h.orderLE hbalanced
    (Nat.succ_pos 0) (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
    (coverMap T h.valid) (etale_coverMap_of_isAdmissible T h.valid) hqc
    (coverTriple_structureMorphism T h.valid).symm (fun x _ => hsurj.1 x)
  have hbdU : (derivedTriple (coverTriple T h.valid)
      (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary) hft
      [(AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)]
      (coverTriple T h.valid).boundary.length).boundary
      = [(AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)] :=
    boundary_derivedTriple_emptyMarkedBlowupSequenceData_consolidated447 (coverTriple T h.valid) hft
      [(AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)]
  have hEqU : derivedTriple (coverTriple T h.valid)
      (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary) hft
      [(AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)]
      (coverTriple T h.valid).boundary.length
      = (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
          (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
          (coverMap T h.valid) :=
    markedIdealWithBoundary_mk_congr_consolidated447
      (structureMorphism_derivedTriple_emptyMarkedBlowupSequenceData_consolidated447 (coverTriple T h.valid) hft
        [(AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)]
        (coverTriple T h.valid).boundary.length)
      ((ideal_derivedTriple_emptyMarkedBlowupSequenceData_consolidated447 (coverTriple T h.valid) hczC hcoverMult hft hsm
        [(AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)]
        (coverTriple T h.valid).boundary.length).trans hcoverIdeal)
      ((mult_derivedTriple_emptyMarkedBlowupSequenceData_consolidated447 (coverTriple T h.valid) hcoverMult hft
        [(AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)]
        (coverTriple T h.valid).boundary.length).trans hmult.symm)
      hbdU
  have hDU := isBalanced_of_eq_derivedTriple_emptyMarkedBlowupSequenceData_consolidated447 hstar (coverTriple T h.valid) hVcover
    hOcover hft
    [(AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)]
    (coverTriple T h.valid).boundary.length
    ((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
      (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
      (coverMap T h.valid)) hEqU hpb.1
  have hbdU2 : (derivedTriple (coverTriple T h.valid)
      (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary) hft
      [MaxContactReduction.strictTransformAtLength
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
        (coverMaxContactIdeal T h.valid)]
      (coverTriple T h.valid).boundary.length).boundary
      = [MaxContactReduction.strictTransformAtLength
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
        (coverMaxContactIdeal T h.valid)] :=
    boundary_derivedTriple_emptyMarkedBlowupSequenceData_consolidated447 (coverTriple T h.valid) hft
      [MaxContactReduction.strictTransformAtLength
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
        (coverMaxContactIdeal T h.valid)]
  have htri : derivedTriple (coverTriple T h.valid)
      (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary) hft
      [MaxContactReduction.strictTransformAtLength
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
        (coverMaxContactIdeal T h.valid)]
      (coverTriple T h.valid).boundary.length
      = ((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
          (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
          (coverMap T h.valid)).withBoundary
        [MaxContactReduction.strictTransformAtLength
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
          (coverMaxContactIdeal T h.valid)] :=
    markedIdealWithBoundary_mk_congr_consolidated447
      (structureMorphism_derivedTriple_emptyMarkedBlowupSequenceData_consolidated447 (coverTriple T h.valid) hft
        [MaxContactReduction.strictTransformAtLength
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
          (coverMaxContactIdeal T h.valid)]
        (coverTriple T h.valid).boundary.length)
      ((ideal_derivedTriple_emptyMarkedBlowupSequenceData_consolidated447 (coverTriple T h.valid) hczC hcoverMult hft hsm
        [MaxContactReduction.strictTransformAtLength
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
          (coverMaxContactIdeal T h.valid)]
        (coverTriple T h.valid).boundary.length).trans hcoverIdeal)
      ((mult_derivedTriple_emptyMarkedBlowupSequenceData_consolidated447 (coverTriple T h.valid) hcoverMult hft
        [MaxContactReduction.strictTransformAtLength
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
          (coverMaxContactIdeal T h.valid)]
        (coverTriple T h.valid).boundary.length).trans hmult.symm)
      hbdU2
  have hV₂ : ((((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
        (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
        (coverMap T h.valid)).withBoundary
      [MaxContactReduction.strictTransformAtLength
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
        (coverMaxContactIdeal T h.valid)])).IsAdmissible := by
    rw [← htri]
    exact hVc
  have hcmp : LocallyOfFiniteType (coverMap T h.valid ≫ T.structMap) := by
    rw [← coverTriple_structureMorphism T h.valid]
    exact hftC
  have hadm1 : IsMaxContactHypersurface T.base T.structMap T.ideal 1
      (AlgebraicGeometry.Scheme.Hom.ker e) := by
    have hx := hadm
    rw [hmult] at hx
    exact hx
  have hkey := IsMaxContactHypersurface.comap_of_isOpenImmersionAtSource T.structMap hadm1
    (coverMap T h.valid) (MaxContactOpenCover.isLocalIsomorphism_coverMap T h.valid)
  have hA1 : ∀ m : ℕ, m = 1 →
      @IsMaxContactHypersurface T.base _ (coverTriple T h.valid).scheme
        (coverTriple T h.valid).structMap hftC
        (T.ideal.comap (coverMap T h.valid)) m
        ((AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)) := by
    rintro m rfl
    exact @isMaxContactHypersurface_of_eq_of_eq_of_eq T.base _ (coverTriple T h.valid).scheme
      (coverMap T h.valid ≫ T.structMap) (coverTriple T h.valid).structMap hcmp hftC
      (T.ideal.comap (coverMap T h.valid)) (T.ideal.comap (coverMap T h.valid))
      ((AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid))
      ((AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)) 1
      (coverTriple_structureMorphism T h.valid).symm rfl rfl hkey
  have hbase := BoundarySeparationByMaxContact.isMaxContactHypersurface_coverMaxContactIdeal hstar P T h
  have htrm : ∀ m : ℕ, (coverTriple T h.valid).mult = m →
      IsMaxContactHypersurface (coverTriple T h.valid).base
        ((emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).proj
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length ≫
          (coverTriple T h.valid).structMap)
        ((emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).ideal
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length) m
        (MaxContactReduction.strictTransformAtLength
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
          (coverMaxContactIdeal T h.valid)) := by
    rintro m rfl
    exact isMaxContactHypersurface_iteratedStrictTransform hstar (coverTriple T h.valid) hVcover hOcover
      (coverMaxContactIdeal T h.valid) hbase
      (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
      (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length le_rfl
  have hA2 : ∀ m : ℕ, m = 1 →
      @IsMaxContactHypersurface T.base _ (coverTriple T h.valid).scheme
        (coverTriple T h.valid).structMap hftC
        (T.ideal.comap (coverMap T h.valid)) m
        (MaxContactReduction.strictTransformAtLength
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
          (coverMaxContactIdeal T h.valid)) := by
    rintro m rfl
    exact @isMaxContactHypersurface_of_eq_of_eq_of_eq T.base _ (coverTriple T h.valid).scheme
      ((emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).proj
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length ≫
        (coverTriple T h.valid).structMap)
      (coverTriple T h.valid).structMap hft hftC
      ((emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).ideal
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length)
      (T.ideal.comap (coverMap T h.valid))
      (MaxContactReduction.strictTransformAtLength
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
        (coverMaxContactIdeal T h.valid))
      (MaxContactReduction.strictTransformAtLength
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
        (coverMaxContactIdeal T h.valid)) 1
      (projectionToBase_emptyMarkedBlowupSequenceData_comp_consolidated447 (coverTriple T h.valid))
      ((emptyMarkedBlowupSequenceData_ideal (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length).trans
        hcoverIdeal)
      rfl (htrm 1 hcoverMult)
  have hTdim : P ((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
      (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
      (coverMap T h.valid)).krullDimSucc :=
    hmono _ _ (hstar.coverTriple_dim_le T h.valid) h.dim_prop
  have hTO : ∀ x : ↥(((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
      (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
      (coverMap T h.valid)).scheme),
      orderAt (((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
        (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
        (coverMap T h.valid)).ideal) x ≤
      (((((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
        (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
        (coverMap T h.valid)).mult) : ℕ) : ℕ∞) := by
    intro x
    show orderAt (T.ideal.comap (coverMap T h.valid)) x ≤ ((T.mult : ℕ) : ℕ∞)
    rw [orderAt_comap T.base T.structMap (coverMap T h.valid) T.ideal x]
    exact h.orderLE _
  have hmultPB : (((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
      (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
      (coverMap T h.valid)).mult) = 1 := hmult
  have hbdPB : (((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
      (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
      (coverMap T h.valid)).boundary)
      = [(AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)] := rfl
  have hAdmEq := isomorphic_of_isMaxContactHypersurface_singleton_boundary_consolidated447 hin P hmono (A 0) B (hspec 0)
    ((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
      (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap (coverMap T h.valid))
    hpb.1 hTdim hTO hmultPB
    ((AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid))
    (MaxContactReduction.strictTransformAtLength
      (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
      (coverMaxContactIdeal T h.valid))
    hbdPB hDU hV₂ (hA1 T.mult hmult) (hA2 T.mult hmult)
  have hEq : (coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).toSequenceOfBlowups.Isomorphic
      (A 0 (derivedTriple (coverTriple T h.valid)
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary) hft
        [MaxContactReduction.strictTransformAtLength
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
          (coverMaxContactIdeal T h.valid)]
        (coverTriple T h.valid).boundary.length)).toSequenceOfBlowups := by
    rw [heq]
    refine SequenceOfBlowups.Isomorphic.trans
      (isomorphic_of_emptyMarkedBlowupSequenceData_append_consolidated447 (coverTriple T h.valid).structMap
        (coverTriple T h.valid).ideal (coverTriple T h.valid).mult
        (coverTriple T h.valid).boundary
        ((BlowupSequenceData.ofSequenceOfBlowups (A 0 (derivedTriple (coverTriple T h.valid)
            (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
              (coverTriple T h.valid).mult (coverTriple T h.valid).boundary) hft
            [MaxContactReduction.strictTransformAtLength
              (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
                (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
              (coverMaxContactIdeal T h.valid)]
            (coverTriple T h.valid).boundary.length)).toSequenceOfBlowups).toMarkedBlowupSequenceData
          ((emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
              (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).proj
            (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
              (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length ≫
            (coverTriple T h.valid).structMap)
          ((emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
              (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).ideal
            (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
              (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length)
          (coverTriple T h.valid).mult
          ((emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
              (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).boundary
            (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
              (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length) hmk)
        hinv) ?_
    exact BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _
  have hheq : HEq ((A 0 (derivedTriple (coverTriple T h.valid)
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary) hft
        [MaxContactReduction.strictTransformAtLength
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
          (coverMaxContactIdeal T h.valid)]
        (coverTriple T h.valid).boundary.length)).toSequenceOfBlowups)
      ((A 0 (((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
          (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
          (coverMap T h.valid)).withBoundary
        [MaxContactReduction.strictTransformAtLength
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
          (coverMaxContactIdeal T h.valid)])).toSequenceOfBlowups) := by
    rw [htri]
  have hcast := eq_of_heq hheq
  rw [hcast] at hEq
  exact hpb.2.of_isomorphic_pullback (hAdmEq.trans hEq.symm)

theorem isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_isMaxContactHypersurface
    (hadm : ∀ [LocallyOfFiniteType T.structMap],
      IsMaxContactHypersurface T.base T.structMap T.ideal T.mult
        (AlgebraicGeometry.Scheme.Hom.ker e))
    (hV : (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).IsAdmissible) :
    IsStrictPullbackBlowupSeq (coverMap T h.valid)
      (coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).toSequenceOfBlowups
      (A 0 (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e])).toSequenceOfBlowups := by
  have hSb : (coverTriple T h.valid).boundary = [] :=
    (coverTriple_boundary T h.valid).trans
      ((congrArg
          (List.map (fun D : T.scheme.IdealSheafData => D.comap (coverMap T h.valid)))
          hbd).trans List.map_nil)
  have hSlen : (coverTriple T h.valid).boundary.length = 0 := congrArg List.length hSb
  have hs : BoundarySeparationByMaxContact.separateAllBoundary T h.valid hinv A
      = emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary := by
    show MaxContactReduction.separateBoundary hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
        (coverTriple T h.valid) ((coverTriple T h.valid).boundary.length) = _
    rw [hSlen]
    exact separateBoundary_zero hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T) _
  obtain ⟨hft, hVc, _, hmk, heq, _⟩ :=
    BoundarySeparationByMaxContact.exists_cover_eq_separateAllBoundary_append hstar hinv P hmono A B hspec T h
  exact isStrictPullbackBlowupSeq_cover_of_eq_append_consolidated447 hstar hin hinv P hmono A B hspec T h hbd hmult
    e hadm hV (BoundarySeparationByMaxContact.separateAllBoundary T h.valid hinv A) hs hft hVc hmk heq

theorem isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_etaleChart
    (hchart : ∀ x : ↥T.scheme, x ∈ (AlgebraicGeometry.Scheme.Hom.ker e).support →
      ∃ (U : T.scheme.Opens) (n : ℕ) (c : EtaleChart T.structMap U n) (j : Fin n),
        x ∈ U ∧ restrictIdeal (AlgebraicGeometry.Scheme.Hom.ker e) U =
          c.coordIdeal ({j} : Finset (Fin n)))
    (hle : AlgebraicGeometry.Scheme.Hom.ker e ≤ T.ideal)
    (hV : (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).IsAdmissible) :
    IsStrictPullbackBlowupSeq (coverMap T h.valid)
      (coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).toSequenceOfBlowups
      (A 0 (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e])).toSequenceOfBlowups := by
  have := h.valid.locallyOfFiniteType
  have := h.valid.smooth
  have : CharZero T.base := h.valid.charZero
  refine isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_isMaxContactHypersurface hstar hin hinv P hmono A B hspec T h hbd
    hmult e ?_ hV
  intro hftinst
  have : LocallyOfFiniteType T.structMap := hftinst
  rw [hmult]
  exact isMaxContactHypersurface_one_of_etaleChart T.structMap T.ideal
    (AlgebraicGeometry.Scheme.Hom.ker e) hchart hle

theorem isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_isSmoothDivisor
    (hdiv : IsSmoothDivisor T.structMap (AlgebraicGeometry.Scheme.Hom.ker e))
    (J : Y.IdealSheafData) (hJ : T.ideal = imageIdealSheaf e J)
    (hV : (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).IsAdmissible) :
    IsStrictPullbackBlowupSeq (coverMap T h.valid)
      (coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).toSequenceOfBlowups
      (A 0 (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e])).toSequenceOfBlowups := by
  have := h.valid.locallyOfFiniteType
  have := h.valid.smooth
  have : CharZero T.base := h.valid.charZero
  refine isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_etaleChart hstar hin hinv P hmono A B hspec T h hbd hmult
    e ?_ ?_ hV
  · intro x hx
    exact exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton T.structMap
      (AlgebraicGeometry.Scheme.Hom.ker e) hdiv x hx
  · rw [hJ, imageIdealSheaf_eq_ker]
    intro U
    exact AlgebraicGeometry.Scheme.Hom.le_ker_comp ..


end

end MaxContactCoverData

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderCertificates
section


section
namespace FunctorialResolution.EmbeddedResolution

def HasOrderCertificateMultOne {k : Type u} [Field k] (D : MarkedSchemeWithCenter.{u} k) : Prop :=
  OrderCertificate D.ambient D.structMap D.ideal 1 D.boundarySupport D.center

theorem isInvariantUnderIso_hasOrderCertificateMultOne (k : Type u) [Field k] :
    IsInvariantUnderIso (fun D : MarkedSchemeWithCenter.{u} k => HasOrderCertificateMultOne D) := by
  intro D A e hD
  show OrderCertificate (D.transport e).ambient (D.transport e).structMap (D.transport e).ideal 1
      (D.transport e).boundarySupport (D.transport e).center
  rw [MarkedSchemeWithCenter.transport_projectionToBase, MarkedSchemeWithCenter.transport_ideal, MarkedSchemeWithCenter.transport_center,
    MarkedSchemeWithCenter.boundarySupport_transport]
  exact OrderCertificate.comap_iso_hom_comp e hD

namespace BoundarySeparationByMaxContact

def ContinuationOrderCertificate (hinv : ComapIsoInvariance.{u}) (A : ℕ → PrincipalizationAssignment.{u}) (P : ℕ → Prop)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T) : Prop :=
  ∀ hft : LocallyOfFiniteType
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap),
    ∀ hmk : (BlowupSequenceData.ofSequenceOfBlowups (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).IsMarked
        ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
          (MaxContactCoverData.coverTriple T h.valid).structMap)
        ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
        (MaxContactCoverData.coverTriple T h.valid).mult
        ((separateAllBoundary T h.valid hinv A).boundary (separateAllBoundary T h.valid hinv A).length),
      ∀ i < (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).length,
        HasOrderCertificateMultOne
          ((continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
              (separateAllBoundary T h.valid hinv A) hft
              [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
                (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
              (MaxContactCoverData.coverTriple T h.valid).boundary.length
              (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).dataAt i)

section
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (u : MarkedBlowupSequenceData p I m E)

private theorem mem_boundary_zero_of_eq_comap_consolidated448 (D : (u.obj 0).IdealSheafData) (C : X.IdealSheafData)
    (hC : C ∈ E) (hD : D = C.comap u.toBlowupSequenceData.isoZero.hom) :
    D ∈ u.boundary 0 := by
  subst hD
  rw [u.boundary_zero]
  exact List.mem_map.2 ⟨C, hC, rfl⟩

private theorem exists_mem_boundary_succ_of_map_mem_support_consolidated448 (hN : ∀ i ≤ u.length, IsLocallyNoetherian (u.obj i))
    {t : ℕ} (ht : t < u.length) (x : ↥(u.obj (t + 1)))
    (hx : ∃ J ∈ u.boundary t, (u.map t) x ∈ (J.support : Set ↥(u.obj t))) :
    ∃ J ∈ u.boundary (t + 1), x ∈ (J.support : Set ↥(u.obj (t + 1))) := by
  obtain ⟨J, hJ, hJx⟩ := hx
  have h1 : x ∈ ⇑(u.map t) ⁻¹' (⋃ C ∈ u.boundary t, (C.support : Set ↥(u.obj t))) := by
    simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
    exact ⟨J, hJ, hJx⟩
  have h2 := u.preimage_iUnion_support_boundary_subset hN ht h1
  simp only [Set.mem_iUnion, exists_prop] at h2
  exact h2


end

section
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (u : MarkedBlowupSequenceData p I m E) (hN : ∀ i ≤ u.length, IsLocallyNoetherian (u.obj i)) (D : ∀ t : ℕ, (u.obj t).IdealSheafData) (hD0 : D 0 ∈ u.boundary 0) (hstep : ∀ t, t < u.length → ∀ x : ↥(u.obj (t + 1)), x ∈ ((D (t + 1)).support : Set ↥(u.obj (t + 1))) → (u.map t) x ∈ ((D t).support : Set ↥(u.obj t)))
include hN hD0 hstep

private theorem exists_mem_boundary_of_mem_support_chain_consolidated448 :
    ∀ t, t ≤ u.length → ∀ x : ↥(u.obj t), x ∈ ((D t).support : Set ↥(u.obj t)) →
      ∃ J ∈ u.boundary t, x ∈ (J.support : Set ↥(u.obj t)) := by
  intro t
  induction t with
  | zero =>
      intro _ x hx
      exact ⟨D 0, hD0, hx⟩
  | succ n ih =>
      intro hn x hx
      have hn' : n < u.length := hn
      exact exists_mem_boundary_succ_of_map_mem_support_consolidated448 u hN hn' x (ih (le_of_lt hn') _ (hstep n hn' x hx))

private theorem hasOrderCertificateMultOne_dataAt_of_center_subset_consolidated448 (hcen : ∀ t, t < u.length →
      ((u.center t).support : Set ↥(u.obj t)) ⊆ ((D t).support : Set ↥(u.obj t))) :
    ∀ i < u.length, HasOrderCertificateMultOne (u.dataAt i) := by
  intro i hi
  refine OrderCertificate.memory ?_
  intro x hx
  have hx' : x ∈ ((u.center i).support : Set ↥(u.obj i)) := hx
  obtain ⟨J, hJ, hJx⟩ := exists_mem_boundary_of_mem_support_chain_consolidated448 u hN D hD0 hstep i (le_of_lt hi) x (hcen i hi hx')
  exact (MarkedSchemeWithCenter.mem_boundarySupport_iff (u.dataAt i) x).2 ⟨J, hJ, hJx⟩


end

section
variable (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
include hstar hmono

private theorem hasOrderCertificateMultOne_appendLowerDimReduction_consolidated448 (j : ℕ) (hspec : IsBoundaryDivisorReduction P j (A j) B)
    (T S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible) (hdim : S.krullDimSucc ≤ T.krullDimSucc) (hPdimT : P T.krullDimSucc)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hj : j < S.boundary.length)
    (hs : ∀ i < s.length, HasOrderCertificateMultOne (s.dataAt i)) :
    ∀ i < (MaxContactReduction.appendLowerDimReduction hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T) S s [] 0 j).length,
      HasOrderCertificateMultOne
        ((MaxContactReduction.appendLowerDimReduction hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T) S s [] 0
          j).dataAt i) := by
  have hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap) :=
    locallyOfFiniteType_projectionToBase_comp hstar S hV s s.length le_rfl
  have hsnc0 : InStrictNormalCrossingPosition (s.proj s.length ≫ S.structMap) (s.boundary s.length) := by
    have h0 := (hstar.valid_level S hV s.toMarkedSequenceOfBlowups s.length le_rfl).snc
    rw [MarkedIdealWithBoundary.transformAt_structureMorphism, MarkedIdealWithBoundary.transformAt_boundary,
      MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec, MarkedBlowupSequenceData.toMarkedSequence_boundary] at h0
    exact h0
  have hsnc : InStrictNormalCrossingPosition (s.proj s.length ≫ S.structMap)
      ([] ++ (s.boundary s.length).drop 0) := by
    rw [List.nil_append, List.drop_zero]
    exact hsnc0
  have hVc : (MaxContactCoverData.derivedTriple S s hft [] 0).IsAdmissible :=
    isAdmissible_derivedTriple hstar S hV s hft [] 0 hsnc
  have hdimC : (MaxContactCoverData.derivedTriple S s hft [] 0).krullDimSucc ≤ T.krullDimSucc :=
    hstar.derivedTriple_dim_le hV s hft [] 0 hdim
  have hPC : P (MaxContactCoverData.derivedTriple S s hft [] 0).krullDimSucc := hmono _ _ hdimC hPdimT
  have hbl : (s.boundary s.length).length = S.boundary.length + s.length :=
    MarkedBlowupSequenceData.boundary_length s s.length le_rfl
  have hjC : j < ([] ++ (s.boundary s.length).drop 0).length := by
    simp only [List.nil_append, List.drop_zero, hbl]
    omega
  have hsep : ∀ C ∈ (s.boundary s.length).take 0,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (C.support : Set ↥(s.obj s.length)) = ∅ := by
    intro C hC
    simp at hC
  have hOB := LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hV.one_le_mult hO s hft [] 0 hVc
  have hbalanced := LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hV.one_le_mult hO s hft [] 0 hVc
  have hjS : j < (MaxContactCoverData.derivedTriple S s hft [] 0).boundary.length := by
    rw [MaxContactCoverData.derivedTriple_boundary]
    exact hjC
  obtain ⟨Dv, bv, -, hD0, hcen, hbt, hDst, -, -⟩ :=
    hspec.shape (MaxContactCoverData.derivedTriple S s hft [] 0) hVc hPC hOB hbalanced hjS
  obtain ⟨hmk, heq, -⟩ :=
    LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A B j hspec
      (MaxContactFunctoriality.lowerDimensionalFamily A T) (fun _ _ _ => rfl) S hV hV.one_le_mult hO s [] 0 hft
      hdimC hPC hVc hjC hsep
  rw [heq]
  intro i hi
  refine MarkedBlowupSequenceData.append_dataAt_of_forall s _ hinv (fun Dd => HasOrderCertificateMultOne Dd)
    (isInvariantUnderIso_hasOrderCertificateMultOne S.base) hs ?_ i hi
  have hbeq : (MaxContactCoverData.derivedTriple S s hft [] 0).boundary = s.boundary s.length := by
    rw [MaxContactCoverData.derivedTriple_boundary]
    simp
  have hmemE : (MaxContactCoverData.derivedTriple S s hft [] 0).boundary.get ⟨j, hjS⟩ ∈
      s.boundary s.length := by
    rw [← hbeq]
    exact List.getElem_mem hjS
  refine hasOrderCertificateMultOne_dataAt_of_center_subset_consolidated448 _ ?_ Dv ?_ ?_ ?_
  · intro n hn
    exact isLocallyNoetherian_tunedMarkedBlowupSeq_schemeAt hstar S hV s hft [] 0 hVc
      (A j (MaxContactCoverData.derivedTriple S s hft [] 0)) n hn
  · exact mem_boundary_zero_of_eq_comap_consolidated448
      ((BlowupSequenceData.ofSequenceOfBlowups (A j (MaxContactCoverData.derivedTriple S s hft [] 0)).toSequenceOfBlowups).toMarkedBlowupSequenceData
        (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult (s.boundary s.length) hmk)
      (Dv 0) ((MaxContactCoverData.derivedTriple S s hft [] 0).boundary.get ⟨j, hjS⟩) hmemE hD0
  · intro n hn x hx
    by_cases hb0 : bv = true ∧ n = 0
    · have hD1' : Dv (n + 1) = (Dv n).comap
          ((A j (MaxContactCoverData.derivedTriple S s hft [] 0)).transitionMapSucc n) := by
        obtain ⟨hbtrue, rfl⟩ := hb0
        exact (hbt hbtrue).2.2
      rw [hD1'] at hx
      have hx2 : x ∈ ((Dv n).comap
          ((A j (MaxContactCoverData.derivedTriple S s hft [] 0)).transitionMapSucc n)).support := hx
      exact (mem_comap_support_iff_base_mem_support _ _ x).1 hx2
    · rw [hDst n hn hb0] at hx
      exact support_strictTransform_subset_preimage _ _ _ hx
  · exact hcen

theorem orderCertificate_coverMarkedBlowupData (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T)
    (hcert : ContinuationOrderCertificate hinv A P T h) (_hmult : T.mult = 1) (t : ℕ)
    (ht : t <
      (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).length) :
    OrderCertificate
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
        (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.schemeAt t)
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
          (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.projectionToBase t ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap)
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
        (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.ideal t) 1
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
        (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.boundaryLocus t)
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
        (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.center t) := by
  have hV : (MaxContactCoverData.coverTriple T h.valid).IsAdmissible := isAdmissible_coverTriple hstar P T h
  have hO := orderAt_coverTriple_ideal_le_mult hstar P T h
  have hdimS : (MaxContactCoverData.coverTriple T h.valid).krullDimSucc ≤ T.krullDimSucc :=
    hstar.coverTriple_dim_le T h.valid
  have main : ∀ j : ℕ, j ≤ (MaxContactCoverData.coverTriple T h.valid).boundary.length →
      ∀ i < (MaxContactReduction.separateBoundary hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
          (MaxContactCoverData.coverTriple T h.valid) j).length,
        HasOrderCertificateMultOne ((MaxContactReduction.separateBoundary hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
          (MaxContactCoverData.coverTriple T h.valid) j).dataAt i) := by
    intro j
    induction j with
    | zero =>
        intro _ i hi
        rw [MaxContactCoverData.separateBoundary_zero] at hi
        exact absurd hi (Nat.not_lt_zero i)
    | succ n ih =>
        intro hn
        have hnlt : n < (MaxContactCoverData.coverTriple T h.valid).boundary.length := hn
        rw [MaxContactCoverData.separateBoundary_succ]
        exact hasOrderCertificateMultOne_appendLowerDimReduction_consolidated448 hstar hinv P hmono A B n (hspec n) T
          (MaxContactCoverData.coverTriple T h.valid) hV hdimS h.dim_prop hO _ hnlt
          (ih (le_of_lt hnlt))
  obtain ⟨hft, -, -, hmk, heq, -⟩ := exists_cover_eq_separateAllBoundary_append hstar hinv P hmono A B hspec T h
  have key : ∀ i < (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
      (MaxContactFunctoriality.lowerDimensionalFamily A T)).length,
      HasOrderCertificateMultOne ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
        (MaxContactFunctoriality.lowerDimensionalFamily A T)).dataAt i) := by
    rw [heq]
    intro i hi
    exact MarkedBlowupSequenceData.append_dataAt_of_forall _ _ hinv (fun Dd => HasOrderCertificateMultOne Dd)
      (isInvariantUnderIso_hasOrderCertificateMultOne (MaxContactCoverData.coverTriple T h.valid).base)
      (main _ le_rfl) (hcert hft hmk) i hi
  have hk := key t ht
  unfold HasOrderCertificateMultOne at hk
  rw [MarkedBlowupSequenceData.boundarySupport_dataAt] at hk
  rw [MarkedBlowupSequenceData.toMarkedSequence_projectionToBase]
  exact hk


end

end BoundarySeparationByMaxContact

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.EtalePullbackOfMaxContact
section

open CategoryTheory.Limits

section
namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactCoverDescent

section
variable {X Y : Scheme.{u}} (g : Y ⟶ X) (Q : MorphismProperty Scheme.{u}) (hQ : Q.IsStableUnderBaseChange) (hg : Q g)
include hQ hg

private theorem morphismProperty_pullback_fst_self_consolidated461 : Q (pullback.fst g g) :=
  hQ.of_isPullback (IsPullback.of_hasPullback g g).flip hg

private theorem morphismProperty_pullback_snd_self_consolidated461 : Q (pullback.snd g g) :=
  hQ.of_isPullback (IsPullback.of_hasPullback g g) hg


end

private theorem morphismProperty_comp_consolidated461 {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p : Y ⟶ Z)
    (Q : MorphismProperty Scheme.{u}) (hQ : Q.IsStableUnderComposition) (hf : Q f) (hp : Q p) :
    Q (f ≫ p) :=
  hQ.comp_mem f p hf hp

private theorem map_comap_map_comap_eq_of_comp_eq_consolidated461 {W X Y : Scheme.{u}} (a b : W ⟶ X) (g : X ⟶ Y)
    (hab : a ≫ g = b ≫ g) (L : List Y.IdealSheafData) :
    List.map (fun D : X.IdealSheafData => D.comap a)
        (List.map (fun D : Y.IdealSheafData => D.comap g) L)
      = List.map (fun D : X.IdealSheafData => D.comap b)
        (List.map (fun D : Y.IdealSheafData => D.comap g) L) := by
  induction L with
  | nil => simp
  | cons D L ih =>
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨?_, ih⟩
      have hD : D.comap (a ≫ g) = D.comap (b ≫ g) := by rw [hab]
      simpa using hD

private theorem heq_reduceAlongHypersurface_of_eq_consolidated461 (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : (S : MarkedIdealWithBoundary.{u}) → S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups)
    {S₁ S₂ : MarkedIdealWithBoundary.{u}} (hS : S₁ = S₂)
    (H₁ : S₁.scheme.IdealSheafData) (H₂ : S₂.scheme.IdealSheafData) (hH : HEq H₁ H₂) :
    HEq (MaxContactReduction.reduceAlongHypersurface hinv T resolveLower S₁ H₁).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv T resolveLower S₂ H₂).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  subst hS
  have hEq : H₁ = H₂ := eq_of_heq hH
  subst hEq
  rfl

private theorem inStrictNormalCrossingPosition_comap_boundary_consolidated461 (hin : OrderReduction.OrderReductionHypotheses.{u})
    (S' : MarkedIdealWithBoundary.{u})
    (hV : S'.IsAdmissible) {Y : Scheme.{u}} (f : Y ⟶ S'.scheme)
    (hf : Smooth f)
    (hq : QuasiCompact (f ≫ S'.structMap)) :
    InStrictNormalCrossingPosition (f ≫ S'.structMap)
      (List.map (fun D : S'.scheme.IdealSheafData => D.comap f) S'.boundary) := by
  have := hf
  have := hq
  have hpb := hin.valid_pullbackAlong S' hV Y (f ≫ S'.structMap) f rfl
  have hs : (S'.pullbackAlong Y (f ≫ S'.structMap) f).structMap = f ≫ S'.structMap :=
    MarkedIdealWithBoundary.pullbackAlong_structureMorphism S' Y (f ≫ S'.structMap) f
  have hb : (S'.pullbackAlong Y (f ≫ S'.structMap) f).boundary
      = List.map (fun D : S'.scheme.IdealSheafData => D.comap f) S'.boundary :=
    MarkedIdealWithBoundary.pullbackAlong_boundary S' Y (f ≫ S'.structMap) f
  have hsnc := hpb.snc
  rw [hs, hb] at hsnc
  exact hsnc

section
variable (hstar : MaxContactCoverProperties.{u}) (hin : OrderReduction.OrderReductionHypotheses.{u}) (hmc : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u}) (hsap : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u}) (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B) (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc) (S : MarkedIdealWithBoundary.{u}) (hSV : S.IsAdmissible) (hSO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) (hSdim : S.krullDimSucc ≤ T.krullDimSucc)
include hstar hin hmc hsap hmono hspec hPdimT hSV hSO hSdim

private theorem isStrictPullbackBlowupSeq_reduceAlongHypersurface_pullback_consolidated461 (H : S.scheme.IdealSheafData)
    (hH : ∀ [LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    {X' : Scheme.{u}} (q : X' ⟶ S.scheme)
    (hqsmooth : Smooth q) (hqflat : Flat q)
    (hqSu : AlgebraicGeometry.Surjective q) (hqEt : Etale q)
    [QuasiCompact (q ≫ S.structMap)]
    [LocallyOfFiniteType (q ≫ S.structMap)]
    (H' : X'.IdealSheafData)
    (hadm' : IsMaxContactHypersurface S.base (q ≫ S.structMap) (S.ideal.comap q) S.mult H')
    (hsnc' : InStrictNormalCrossingPosition (q ≫ S.structMap) [H']) :
    IsStrictPullbackBlowupSeq q
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S')
        (LowerDimReductionPullback.pullbackTriple S q) H').toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have := hqsmooth
  have := hqflat
  have := hqSu
  have := hqEt
  have hNS : IsNoetherian S.scheme := hSV.isNoetherian
  have hLNS : IsLocallyNoetherian S.scheme := inferInstance
  have hV' : (LowerDimReductionPullback.pullbackTriple S q).IsAdmissible :=
    hin.valid_pullbackAlong S hSV X' (q ≫ S.structMap) q rfl
  have hdim' : (LowerDimReductionPullback.pullbackTriple S q).krullDimSucc ≤ T.krullDimSucc :=
    le_trans (hin.schemeDim_le_of_etale X' S.scheme q hSV.topologicalKrullDim_lt_top) hSdim
  refine BoundarySeparationBaseChange.isStrictPullbackBlowupSeq_reduceAlongHypersurface hstar hin hmc hsap hinv P hmono A B hspec T hPdimT
    S hSV hSO hSdim H hH hHsnc q hV' hdim' H' ?_ ?_
  · intro _inst
    exact hadm'
  · exact hsnc'

private theorem exists_isStrictPullbackBlowupSeq_reduceAlongHypersurface_consolidated461 (g : S.scheme ⟶ T.scheme)
    (hgEt : Etale g) (hgsmooth : Smooth g)
    (hgflat : Flat g) (hgSu : AlgebraicGeometry.Surjective g)
    (φ : T.scheme ⟶ Spec (CommRingCat.of S.base)) (hgs : S.structMap = g ≫ φ)
    (J : T.scheme.IdealSheafData) (hgi : S.ideal = J.comap g)
    (E : List T.scheme.IdealSheafData)
    (hgb : S.boundary = List.map (fun D : T.scheme.IdealSheafData => D.comap g) E)
    (H : S.scheme.IdealSheafData)
    (hH : ∀ [LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H]) :
    ∃ d : BlowupSequenceData T.scheme,
      IsStrictPullbackBlowupSeq g
        (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups
        d.toSequenceOfBlowups := by
  classical
  have := hSV.charZero
  have := hSV.smooth
  have := hSV.locallyOfFiniteType
  have := hSV.quasiCompact
  have := hgEt
  have := hgsmooth
  have := hgflat
  have := hgSu
  have hNS : IsNoetherian S.scheme := hSV.isNoetherian
  have hNSp : TopologicalSpace.NoetherianSpace ↥S.scheme := inferInstance
  have hQCg : QuasiCompact g :=
    ⟨fun U _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hcolS : ∀ (W : Scheme.{u}) (a b : W ⟶ S.scheme), a ≫ g = b ≫ g →
      a ≫ S.structMap = b ≫ S.structMap := by
    intro W a b hab
    rw [hgs, ← Category.assoc, ← Category.assoc, hab]
  have hcolI : ∀ (W : Scheme.{u}) (a b : W ⟶ S.scheme), a ≫ g = b ≫ g →
      S.ideal.comap a = S.ideal.comap b := by
    intro W a b hab
    have hD : J.comap (a ≫ g) = J.comap (b ≫ g) := by rw [hab]
    rw [hgi]
    simpa using hD
  have hcolB : ∀ (W : Scheme.{u}) (a b : W ⟶ S.scheme), a ≫ g = b ≫ g →
      List.map (fun D : S.scheme.IdealSheafData => D.comap a) S.boundary
        = List.map (fun D : S.scheme.IdealSheafData => D.comap b) S.boundary := by
    intro W a b hab
    rw [hgb]
    exact map_comap_map_comap_eq_of_comp_eq_consolidated461 a b g hab E
  have hcol : ∀ (W : Scheme.{u}) (a b : W ⟶ S.scheme), a ≫ g = b ≫ g →
      LowerDimReductionPullback.pullbackTriple S a = LowerDimReductionPullback.pullbackTriple S b := by
    intro W a b hab
    simp only [LowerDimReductionPullback.pullbackTriple, MarkedIdealWithBoundary.pullbackAlong]
    rw [hcolS W a b hab, hcolI W a b hab, hcolB W a b hab]
  have hEt1 : Etale (pullback.fst g g) :=
    morphismProperty_pullback_fst_self_consolidated461 g (@Etale : MorphismProperty Scheme.{u}) inferInstance
      inferInstance
  have hEt2 : Etale (pullback.snd g g) :=
    morphismProperty_pullback_snd_self_consolidated461 g (@Etale : MorphismProperty Scheme.{u}) inferInstance
      inferInstance
  have hSm1 : Smooth (pullback.fst g g) :=
    morphismProperty_pullback_fst_self_consolidated461 g (@Smooth : MorphismProperty Scheme.{u}) inferInstance
      inferInstance
  have hSm2 : Smooth (pullback.snd g g) :=
    morphismProperty_pullback_snd_self_consolidated461 g (@Smooth : MorphismProperty Scheme.{u}) inferInstance
      inferInstance
  have hSu1 : AlgebraicGeometry.Surjective (pullback.fst g g) :=
    morphismProperty_pullback_fst_self_consolidated461 g (@AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u}) inferInstance
      inferInstance
  have hSu2 : AlgebraicGeometry.Surjective (pullback.snd g g) :=
    morphismProperty_pullback_snd_self_consolidated461 g (@AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u}) inferInstance
      inferInstance
  have hFl1 : Flat (pullback.fst g g) :=
    morphismProperty_pullback_fst_self_consolidated461 g (@Flat : MorphismProperty Scheme.{u}) inferInstance
      inferInstance
  have hFl2 : Flat (pullback.snd g g) :=
    morphismProperty_pullback_snd_self_consolidated461 g (@Flat : MorphismProperty Scheme.{u}) inferInstance
      inferInstance
  have hQ1 : QuasiCompact (pullback.fst g g) :=
    morphismProperty_pullback_fst_self_consolidated461 g (@QuasiCompact : MorphismProperty Scheme.{u})
      inferInstance inferInstance
  have hQ2 : QuasiCompact (pullback.snd g g) :=
    morphismProperty_pullback_snd_self_consolidated461 g (@QuasiCompact : MorphismProperty Scheme.{u})
      inferInstance inferInstance
  have hSm1' : Smooth (pullback.fst g g) := hSm1
  have hSm2' : Smooth (pullback.snd g g) := hSm2
  have hQC1 : QuasiCompact (pullback.fst g g ≫ S.structMap) :=
    morphismProperty_comp_consolidated461 (pullback.fst g g) S.structMap
      (@QuasiCompact : MorphismProperty Scheme.{u}) inferInstance
      inferInstance inferInstance
  have hQC2 : QuasiCompact (pullback.snd g g ≫ S.structMap) :=
    morphismProperty_comp_consolidated461 (pullback.snd g g) S.structMap
      (@QuasiCompact : MorphismProperty Scheme.{u}) inferInstance
      inferInstance inferInstance
  have hLF1 : LocallyOfFiniteType (pullback.fst g g ≫ S.structMap) :=
    morphismProperty_comp_consolidated461 (pullback.fst g g) S.structMap
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) inferInstance
      inferInstance inferInstance
  have hLF2 : LocallyOfFiniteType (pullback.snd g g ≫ S.structMap) :=
    morphismProperty_comp_consolidated461 (pullback.snd g g) S.structMap
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) inferInstance
      inferInstance inferInstance
  have hcond : pullback.snd g g ≫ g = pullback.fst g g ≫ g := pullback.condition.symm
  have hstruct : pullback.snd g g ≫ S.structMap = pullback.fst g g ≫ S.structMap :=
    hcolS (pullback g g) (pullback.snd g g) (pullback.fst g g) hcond
  have hideal : S.ideal.comap (pullback.snd g g) = S.ideal.comap (pullback.fst g g) :=
    hcolI (pullback g g) (pullback.snd g g) (pullback.fst g g) hcond
  have htriple : LowerDimReductionPullback.pullbackTriple S (pullback.snd g g)
      = LowerDimReductionPullback.pullbackTriple S (pullback.fst g g) :=
    hcol (pullback g g) (pullback.snd g g) (pullback.fst g g) hcond
  have hadm1 : IsMaxContactHypersurface S.base (pullback.fst g g ≫ S.structMap)
      (S.ideal.comap (pullback.fst g g)) S.mult (H.comap (pullback.fst g g)) :=
    hsap S.base S.scheme S.structMap (pullback g g) (pullback.fst g g) S.ideal S.mult
      hSV.one_le_mult H hH
  have hadm2 : IsMaxContactHypersurface S.base (pullback.snd g g ≫ S.structMap)
      (S.ideal.comap (pullback.snd g g)) S.mult (H.comap (pullback.fst g g)) :=
    isMaxContactHypersurface_of_eq_of_eq_of_eq S.base hstruct.symm hideal.symm rfl hadm1
  have hVb : (S.withBoundary [H]).IsAdmissible :=
    { charZero := hSV.charZero
      locallyOfFiniteType := hSV.locallyOfFiniteType
      nonzeroOnComponents := hSV.nonzeroOnComponents
      one_le_mult := hSV.one_le_mult
      quasiCompact := hSV.quasiCompact
      smooth := hSV.smooth
      snc := hHsnc }
  have hsnc1 : InStrictNormalCrossingPosition (pullback.fst g g ≫ S.structMap) [H.comap (pullback.fst g g)] :=
    inStrictNormalCrossingPosition_comap_boundary_consolidated461 hin (S.withBoundary [H]) hVb (pullback.fst g g) hSm1 hQC1
  have hsnc2 : InStrictNormalCrossingPosition (pullback.snd g g ≫ S.structMap) [H.comap (pullback.fst g g)] := by
    rw [hstruct]
    exact hsnc1
  have hs1 := isStrictPullbackBlowupSeq_reduceAlongHypersurface_pullback_consolidated461 hstar hin hmc hsap hinv P hmono A B hspec T hPdimT
    S hSV hSO hSdim H hH hHsnc (pullback.fst g g) hSm1 hFl1 hSu1 hEt1
    (H.comap (pullback.fst g g)) hadm1 hsnc1
  have hs2 := isStrictPullbackBlowupSeq_reduceAlongHypersurface_pullback_consolidated461 hstar hin hmc hsap hinv P hmono A B hspec T hPdimT
    S hSV hSO hSdim H hH hHsnc (pullback.snd g g) hSm2 hFl2 hSu2 hEt2
    (H.comap (pullback.fst g g)) hadm2 hsnc2
  have hseq : (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S')
        (LowerDimReductionPullback.pullbackTriple S (pullback.snd g g))
        (H.comap (pullback.fst g g))).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      = (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S')
        (LowerDimReductionPullback.pullbackTriple S (pullback.fst g g))
        (H.comap (pullback.fst g g))).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
    eq_of_heq (heq_reduceAlongHypersurface_of_eq_consolidated461 hinv T (fun S' _ i => A i S') htriple
      (H.comap (pullback.fst g g)) (H.comap (pullback.fst g g))
      (HEq.refl (H.comap (pullback.fst g g))))
  have hs2' : IsStrictPullbackBlowupSeq (pullback.snd g g)
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S')
        (LowerDimReductionPullback.pullbackTriple S (pullback.fst g g))
        (H.comap (pullback.fst g g))).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
    rw [← hseq]
    exact hs2
  have hbc1 : IsStrictPullbackBlowupSeq (pullback.fst g g)
      ((MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S')
          S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups.baseChange (pullback.fst g g))
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  have hbc2 : IsStrictPullbackBlowupSeq (pullback.snd g g)
      ((MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S')
          S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups.baseChange (pullback.snd g g))
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  have e1 := hbc1.isomorphic hs1
  have e2 := hbc2.isomorphic hs2'
  obtain ⟨s, hs⟩ := exists_isStrictPullback_of_isomorphic_baseChange g
    (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups
    (e1.trans e2.symm)
  exact ⟨BlowupSequenceData.ofSequenceOfBlowups s, hs.of_isomorphic_base (BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic s).symm⟩


end

theorem exists_isStrictPullback_coverMarkedSequence
    (hstar : MaxContactCoverProperties.{u}) (hin : OrderReduction.OrderReductionHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (hmc : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u})
    (hsap : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u})
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T) :
    ∃ d : BlowupSequenceData T.scheme,
      IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
        (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).toSequenceOfBlowups
        d.toSequenceOfBlowups := by
  classical
  obtain ⟨d, hd⟩ :=
    exists_isStrictPullbackBlowupSeq_reduceAlongHypersurface_consolidated461 hstar hin hmc hsap hinv P hmono A B hspec
      T h.dim_prop
      (MaxContactCoverData.coverTriple T h.valid) (BoundarySeparationByMaxContact.isAdmissible_coverTriple hstar P T h)
      (BoundarySeparationByMaxContact.orderAt_coverTriple_ideal_le_mult hstar P T h)
      (hstar.coverTriple_dim_le T h.valid)
      (MaxContactCoverData.coverMap T h.valid)
      (MaxContactCoverData.etale_coverMap_of_isAdmissible T h.valid)
      (MaxContactCoverData.smooth_coverMap_of_isAdmissible T h.valid)
      (MaxContactCoverData.flat_coverMap_of_isAdmissible T h.valid)
      (MaxContactCoverData.surjective_coverMap T h.valid (hstar.exists_goodCover T h.valid h.orderLE))
      T.structMap rfl
      (MaxContactCoverData.balancedTunedIdeal T h.valid) rfl
      T.boundary rfl
      (MaxContactCoverData.coverMaxContactIdeal T h.valid)
      (by
        intro _inst
        exact BoundarySeparationByMaxContact.isMaxContactHypersurface_coverMaxContactIdeal hstar P T h)
      (BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P T h)
  have hcs : MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)
      = MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S')
          (MaxContactCoverData.coverTriple T h.valid)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid) := by
    with_unfolding_all rfl
  refine ⟨d, ?_⟩
  rw [hcs, ← MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups]
  exact hd

end MaxContactCoverDescent

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderCertificatesMultiplicityOne
section


section
namespace FunctorialResolution.EmbeddedResolution

section
variable {k : Type u} [Field k]

private theorem orderCertificate_congr_morphism_ideal_center_consolidated464 {W : Scheme.{u}}
    {p p' : W ⟶ Spec (CommRingCat.of k)} {N N' : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W}
    {Z Z' : W.IdealSheafData} (hp : p = p') (hN : N = N') (hZ : Z = Z')
    (h : OrderCertificate W p N μ Mem Z) : OrderCertificate W p' N' μ Mem Z' := by
  subst hp
  subst hN
  subst hZ
  exact h

private theorem principalizationCertificate_congr_mult_consolidated464 {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m m' : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (hm : m = m') (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W p I m' Mem Z := by
  subst hm
  exact h

private theorem mem_boundarySupport_of_mem_support_of_mem_boundary_consolidated464 {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (i : ℕ) (J : (s.obj i).IdealSheafData)
    (hJ : J ∈ s.boundary i) (x : ↥(s.obj i))
    (hx : x ∈ (J.support : Set ↥(s.obj i))) : x ∈ (s.dataAt i).boundarySupport := by
  refine (MarkedSchemeWithCenter.mem_boundarySupport_iff (s.dataAt i) x).2 ⟨J, ?_, hx⟩
  rw [MarkedBlowupSequenceData.dataAt_boundary]
  exact hJ


end

section
variable {α : Type _} (l : List α) (a : α) (L : List α) (hl : l = a :: L)
include hl

private theorem get_zero_of_eq_cons_consolidated464 (h0 : 0 < l.length) : l.get ⟨0, h0⟩ = a := by
  subst hl
  rfl

private theorem get_mem_of_eq_cons_of_ne_zero_consolidated464 (idx : Fin l.length) (hidx : (idx : ℕ) ≠ 0) : l.get idx ∈ L := by
  subst hl
  obtain ⟨n, hn⟩ := idx
  cases n with
  | zero => exact absurd rfl hidx
  | succ m =>
      have hm : m < L.length := by simpa using hn
      show L.get ⟨m, hm⟩ ∈ L
      simp


end

section
variable {k : Type u} [Field k]

private theorem controlledTransform_eq_ideal_of_eq_consolidated464 {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedSequenceOfBlowups p I m E) (I' : X.IdealSheafData) (m' : ℕ)
    (hI : I' = I) (hm : m' = m) (i : ℕ) (hi : i ≤ s.length) :
    (BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups).controlledTransform I' m' i = s.ideal i := by
  subst hI
  subst hm
  exact MarkedBlowupSequenceData.ofMarkedSequence_controlledTransform s i hi

private theorem isMaxContactHypersurface_congr_consolidated464 {X : Scheme.{u}}
    (p p' : X ⟶ Spec (CommRingCat.of k))
    (hfp : LocallyOfFiniteType p) (hfp' : LocallyOfFiniteType p')
    {A A' H H' : X.IdealSheafData} {μ μ' : ℕ}
    (hp : p = p') (hA : A = A') (hH : H = H') (hμ : μ = μ')
    (hyp : @IsMaxContactHypersurface k _ X p hfp A μ H) :
    @IsMaxContactHypersurface k _ X p' hfp' A' μ' H' := by
  subst hp
  subst hA
  subst hH
  subst hμ
  exact hyp

private theorem balancedTunedSheaf_eq_of_mult_eq_one_consolidated464 [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (hfp : LocallyOfFiniteType p)
    (I : X.IdealSheafData) (m : ℕ) (hm : m = 1) :
    @FunctorialResolution.EmbeddedResolution.balancedTunedSheaf k _ _ X p hfp I m = I := by
  subst hm
  exact FunctorialResolution.EmbeddedResolution.balancedTunedSheaf_one k p I


end

private theorem support_ideal_subset_iteratedStrictTransform_consolidated464 (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u})
    (hv : S.IsAdmissible) [LocallyOfFiniteType S.structMap]
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((S.mult : ℕ) : ℕ∞)) (hm1 : S.mult = 1)
    (H : S.scheme.IdealSheafData)
    (hH : IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (u : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (t : ℕ) (ht : t ≤ u.length)
    (hfti : LocallyOfFiniteType (u.proj t ≫ S.structMap))
    (hsmt : Smooth (u.proj t ≫ S.structMap))
    (hczs : CharZero S.base) :
    ((u.ideal t).support : Set ↥(u.obj t))
      ⊆ ((u.toBlowupSequenceData.iteratedStrictTransform t H).support : Set ↥(u.obj t)) := by
  have := hfti
  have := hsmt
  have := hczs
  have hadm := isMaxContactHypersurface_iteratedStrictTransform hstar S hv hord H hH u t ht
  have hsub := hadm.orderAtLeastLocus_subset_support (le_of_eq hm1.symm)
  rw [BoundarySeparationByMaxContact.iteratedStrictTransform_eq_toBlowupSequenceData u H t] at hsub
  intro x hx
  apply hsub
  rw [FunctorialResolution.EmbeddedResolution.mem_orderAtLeastLocus_iff]
  have hcoe : ((S.mult : ℕ) : ℕ∞) = 1 := by simp [hm1]
  rw [hcoe]
  exact (FunctorialResolution.EmbeddedResolution.one_le_orderAt_iff_mem_support (u.ideal t) x).2 hx

private theorem orderCertificate_one_of_isSmoothDivisor_consolidated464 {k : Type u} [Field k] {W : Scheme.{u}}
    (hin : OpenImmersionStability k) (p : W ⟶ Spec (CommRingCat.of k))
    (N : W.IdealSheafData) (Mem : Set ↥W) (Z : W.IdealSheafData) (Dv : W.IdealSheafData)
    (hDsm : IsSmoothDivisor p Dv)
    (hNsupp : (↑N.support : Set ↥W) ⊆ (↑Dv.support : Set ↥W))
    (hZH : (↑Z.support : Set ↥W) ⊆ (↑Dv.support : Set ↥W))
    (hcase : IsOpen (⇑Dv.subschemeι ⁻¹' (↑Z.support : Set ↥W)) ∨
      ∃ J : Dv.subscheme.IdealSheafData, NonzeroOnComponents J ∧
        (∀ x : ↥Dv.subscheme, Dv.subschemeι x ∉ Mem →
          ∃ V : Dv.subscheme.Opens, x ∈ V ∧
            J.comap V.ι = (N.comap Dv.subschemeι).comap V.ι) ∧
        PrincipalizationCertificate Dv.subscheme (Dv.subschemeι ≫ p) J 1 (⇑Dv.subschemeι ⁻¹' Mem)
          (Z.comap Dv.subschemeι)) :
    OrderCertificate W p N 1 Mem Z := by
  have hoi : IsOpenImmersion (comapSubscheme (⊤ : W.Opens).ι Dv) :=
    hin.isOpenImmersion_comapSubscheme _ _
  have hkey : ∀ x : ↥(Dv.comap (⊤ : W.Opens).ι).subscheme,
      (⊤ : W.Opens).ι ((Dv.comap (⊤ : W.Opens).ι).subschemeι x)
        = Dv.subschemeι ((comapSubscheme (⊤ : W.Opens).ι Dv) x) := by
    intro x
    have hc := comapSubscheme_comp (⊤ : W.Opens).ι Dv
    have h2 := congrArg
      (fun f : (Dv.comap (⊤ : W.Opens).ι).subscheme ⟶ W => f.base x) hc
    simpa using h2.symm
  have hNH' : ∀ y, y ∈ (N.comap (⊤ : W.Opens).ι).support →
      y ∈ (Dv.comap (⊤ : W.Opens).ι).support := by
    intro y hy
    rw [FunctorialResolution.EmbeddedResolution.mem_comap_support_iff_base_mem_support] at hy ⊢
    exact hNsupp hy
  have hZH' : ∀ y, y ∈ (Z.comap (⊤ : W.Opens).ι).support →
      y ∈ (Dv.comap (⊤ : W.Opens).ι).support := by
    intro y hy
    rw [FunctorialResolution.EmbeddedResolution.mem_comap_support_iff_base_mem_support] at hy ⊢
    exact hZH hy
  rcases hcase with hop | ⟨J, hJnz, hJloc, hJcert⟩
  · refine OrderCertificate.descend (fun _ _ => ⊤) (fun _ _ => trivial)
      (fun _ _ => Dv.comap (⊤ : W.Opens).ι)
      (fun _ _ => hin.comap_isSmoothDivisor _ p Dv hDsm)
      (fun _ _ => hNH') (fun _ _ => hZH')
      (fun _ _ => none) ?_ ?_ ?_ ?_
    · intro _ _ _
      have key : IsOpen (⇑(comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹'
          (⇑Dv.subschemeι ⁻¹' (↑Z.support : Set ↥W))) :=
        ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ
          (⟨_, hop⟩ : Dv.subscheme.Opens)).isOpen
      convert key using 1
      ext x
      simp only [Set.mem_preimage]
      rw [← hkey x]
      exact FunctorialResolution.EmbeddedResolution.mem_comap_support_iff_base_mem_support (⊤ : W.Opens).ι Z _
    · intro _ _ _ hJz; exact absurd hJz (by simp)
    · intro _ _ _ hJz; exact absurd hJz (by simp)
    · intro _ _ _ hJz; exact absurd hJz (by simp)
  · refine OrderCertificate.descend (fun _ _ => ⊤) (fun _ _ => trivial)
      (fun _ _ => Dv.comap (⊤ : W.Opens).ι)
      (fun _ _ => hin.comap_isSmoothDivisor _ p Dv hDsm)
      (fun _ _ => hNH') (fun _ _ => hZH')
      (fun _ _ => some (J.comap (comapSubscheme (⊤ : W.Opens).ι Dv))) ?_ ?_ ?_ ?_
    · intro _ _ hcon; exact absurd hcon (by simp)
    · intro _ _ Jz hJz
      obtain rfl : Jz = J.comap (comapSubscheme (⊤ : W.Opens).ι Dv) := by simpa using hJz.symm
      exact hin.comap_nonzeroOnComponents _ J hJnz
    · intro _ _ Jz hJz x hx
      obtain rfl : Jz = J.comap (comapSubscheme (⊤ : W.Opens).ι Dv) := by simpa using hJz.symm
      have hx' : Dv.subschemeι ((comapSubscheme (⊤ : W.Opens).ι Dv) x) ∉ Mem := by
        intro hc
        apply hx
        have hkx := hkey x
        simpa [hkx] using hc
      obtain ⟨V, hV, hVeq⟩ := hJloc _ hx'
      refine ⟨(comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V, hV, ?_⟩
      have e1 : ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V).ι
            ≫ comapSubscheme (⊤ : W.Opens).ι Dv
          = Scheme.Hom.resLE (comapSubscheme (⊤ : W.Opens).ι Dv) V
              ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V) le_rfl ≫ V.ι :=
        (Scheme.Hom.resLE_comp_ι _ _).symm
      calc (J.comap (comapSubscheme (⊤ : W.Opens).ι Dv)).comap
              ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V).ι
          = J.comap (((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V).ι
              ≫ comapSubscheme (⊤ : W.Opens).ι Dv) :=
              (Scheme.IdealSheafData.comap_comp _ _ _).symm
        _ = J.comap (Scheme.Hom.resLE (comapSubscheme (⊤ : W.Opens).ι Dv) V
              ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V) le_rfl ≫ V.ι) := by rw [e1]
        _ = (J.comap V.ι).comap (Scheme.Hom.resLE (comapSubscheme (⊤ : W.Opens).ι Dv) V
              ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V) le_rfl) :=
              Scheme.IdealSheafData.comap_comp _ _ _
        _ = ((N.comap Dv.subschemeι).comap V.ι).comap
              (Scheme.Hom.resLE (comapSubscheme (⊤ : W.Opens).ι Dv) V
                ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V) le_rfl) := by rw [hVeq]
        _ = (N.comap Dv.subschemeι).comap
              (Scheme.Hom.resLE (comapSubscheme (⊤ : W.Opens).ι Dv) V
                ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V) le_rfl ≫ V.ι) :=
              (Scheme.IdealSheafData.comap_comp _ _ _).symm
        _ = (N.comap Dv.subschemeι).comap
              (((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V).ι
                ≫ comapSubscheme (⊤ : W.Opens).ι Dv) := by rw [e1]
        _ = ((N.comap Dv.subschemeι).comap (comapSubscheme (⊤ : W.Opens).ι Dv)).comap
              ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V).ι :=
              Scheme.IdealSheafData.comap_comp _ _ _
        _ = (N.comap (comapSubscheme (⊤ : W.Opens).ι Dv ≫ Dv.subschemeι)).comap
              ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V).ι := by
              rw [Scheme.IdealSheafData.comap_comp]
        _ = (N.comap ((Dv.comap (⊤ : W.Opens).ι).subschemeι ≫ (⊤ : W.Opens).ι)).comap
              ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V).ι := by
              rw [comapSubscheme_comp]
        _ = ((N.comap (⊤ : W.Opens).ι).comap (Dv.comap (⊤ : W.Opens).ι).subschemeι).comap
              ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V).ι := by
              rw [Scheme.IdealSheafData.comap_comp]
    · intro _ _ Jz hJz
      obtain rfl : Jz = J.comap (comapSubscheme (⊤ : W.Opens).ι Dv) := by simpa using hJz.symm
      have hpc := PrincipalizationCertificate.comap_of_openImmersionStability hin hJcert
        (comapSubscheme (⊤ : W.Opens).ι Dv)
      have e2 : comapSubscheme (⊤ : W.Opens).ι Dv ≫ (Dv.subschemeι ≫ p)
          = (Dv.comap (⊤ : W.Opens).ι).subschemeι ≫ ((⊤ : W.Opens).ι ≫ p) :=
        comapSubscheme_comp_assoc _ _ _
      have e3 : (⇑(comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹' (⇑Dv.subschemeι ⁻¹' Mem))
          = ⇑((Dv.comap (⊤ : W.Opens).ι).subschemeι ≫ (⊤ : W.Opens).ι) ⁻¹' Mem := by
        ext x
        simp only [Set.mem_preimage]
        rw [← hkey x]
        simp
      have e4 : (Z.comap Dv.subschemeι).comap (comapSubscheme (⊤ : W.Opens).ι Dv)
          = (Z.comap (⊤ : W.Opens).ι).comap (Dv.comap (⊤ : W.Opens).ι).subschemeι := by
        rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
          comapSubscheme_comp]
      rw [e2, e3, e4] at hpc
      exact hpc

namespace BoundarySeparationByMaxContact

section
variable (hstar : MaxContactCoverProperties.{u}) (hopen : ∀ (k : Type u) [Field k], OpenImmersionStability k) (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B) (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T) (hmult : T.mult = 1)
include hstar hopen hmono hspec hmult

theorem continuationOrderCertificate_of_mult_eq_one :
    ContinuationOrderCertificate hinv A P T h := by
  intro hft hmk i hi
  have hftI : LocallyOfFiniteType ((separateAllBoundary T h.valid hinv A).proj
      (separateAllBoundary T h.valid hinv A).length ≫
      (MaxContactCoverData.coverTriple T h.valid).structMap) := hft
  have hSV : (MaxContactCoverData.coverTriple T h.valid).IsAdmissible := isAdmissible_coverTriple hstar P T h
  have hSO : ∀ x : ↥(MaxContactCoverData.coverTriple T h.valid).scheme,
      orderAt (MaxContactCoverData.coverTriple T h.valid).ideal x
        ≤ (((MaxContactCoverData.coverTriple T h.valid).mult : ℕ) : ℕ∞) :=
    orderAt_coverTriple_ideal_le_mult hstar P T h
  have hS1 : (MaxContactCoverData.coverTriple T h.valid).mult = 1 := by
    simp [MaxContactCoverData.coverTriple_mult, MaxContactCoverData.tunedMult, hmult, FunctorialResolution.EmbeddedResolution.tuningExponent_one]
  have honeLe : 1 ≤ (MaxContactCoverData.coverTriple T h.valid).mult := le_of_eq hS1.symm
  have hcz : CharZero (MaxContactCoverData.coverTriple T h.valid).base := hSV.charZero
  have hsm0 : Smooth ((separateAllBoundary T h.valid hinv A).proj
      (separateAllBoundary T h.valid hinv A).length ≫
      (MaxContactCoverData.coverTriple T h.valid).structMap) :=
    smooth_projectionToBase_comp hstar (MaxContactCoverData.coverTriple T h.valid) hSV
      (separateAllBoundary T h.valid hinv A) (separateAllBoundary T h.valid hinv A).length le_rfl
  have hAdmCover := isMaxContactHypersurface_coverMaxContactIdeal hstar P T h
  have hAdmT := isMaxContactHypersurface_iteratedStrictTransform hstar
    (MaxContactCoverData.coverTriple T h.valid) hSV hSO (MaxContactCoverData.coverMaxContactIdeal T h.valid)
    hAdmCover (separateAllBoundary T h.valid hinv A) (separateAllBoundary T h.valid hinv A).length le_rfl
  have heqT : MaxContactReduction.iteratedStrictTransform (separateAllBoundary T h.valid hinv A)
      (MaxContactCoverData.coverMaxContactIdeal T h.valid) (separateAllBoundary T h.valid hinv A).length
      = MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid) :=
    (MaxContactReduction.strictTransformAtLength_eq _ _).symm
  have hAdm0 : IsMaxContactHypersurface (MaxContactCoverData.coverTriple T h.valid).base
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap)
      ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
      (MaxContactCoverData.coverTriple T h.valid).mult
      (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)) :=
    isMaxContactHypersurface_congr_consolidated464
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap)
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap)
      hftI hftI rfl rfl heqT rfl hAdmT
  obtain ⟨_, hV2, hP2, _, _, _⟩ := exists_cover_eq_separateAllBoundary_append hstar hinv P hmono A B hspec T h
  have hV' : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).IsAdmissible := hV2
  have hP' : P (reduceAlongHypersurfaceTriple T h.valid hinv A hft).krullDimSucc := hP2
  have hftT : LocallyOfFiniteType (reduceAlongHypersurfaceTriple T h.valid hinv A hft).structMap := by
    rw [MaxContactCoverData.derivedTriple_structureMorphism]; exact hft
  have hcz2 : CharZero (reduceAlongHypersurfaceTriple T h.valid hinv A hft).base := hV'.charZero
  have hOB : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).IsOrderBoundedByMult :=
    LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar (MaxContactCoverData.coverTriple T h.valid) hSV honeLe hSO
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length hV'
  have hbalanced : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).IsBalanced hftT :=
    LowerDimReductionPullback.isBalanced_derivedTriple hstar (MaxContactCoverData.coverTriple T h.valid) hSV honeLe hSO
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length hV'
  have hbd : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).boundary
      = MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)
        :: List.drop (MaxContactCoverData.coverTriple T h.valid).boundary.length
            ((separateAllBoundary T h.valid hinv A).boundary
              (separateAllBoundary T h.valid hinv A).length) :=
    MaxContactCoverData.derivedTriple_boundary _ _ _ _ _
  have hjlen : 0 < (reduceAlongHypersurfaceTriple T h.valid hinv A hft).boundary.length := by
    rw [hbd]; simp
  obtain ⟨D, b, hDsm, hD0, hcenter, hbtrue, hDsucc, _hDfin, hJsh⟩ :=
    (hspec 0).shape (reduceAlongHypersurfaceTriple T h.valid hinv A hft) hV' hP' hOB hbalanced hjlen
  have hmu : FunctorialResolution.EmbeddedResolution.tuningExponent (MaxContactCoverData.coverTriple T h.valid).mult
      = (reduceAlongHypersurfaceTriple T h.valid hinv A hft).mult :=
    (MaxContactCoverData.derivedTriple_mult _ _ _ _ _).symm
  have hpeq : ((separateAllBoundary T h.valid hinv A).proj
      (separateAllBoundary T h.valid hinv A).length ≫
      (MaxContactCoverData.coverTriple T h.valid).structMap)
      = (reduceAlongHypersurfaceTriple T h.valid hinv A hft).structMap :=
    (MaxContactCoverData.derivedTriple_structureMorphism _ _ _ _ _).symm
  have htm : FunctorialResolution.EmbeddedResolution.tuningExponent (MaxContactCoverData.coverTriple T h.valid).mult = 1 := by
    rw [hS1]; exact FunctorialResolution.EmbeddedResolution.tuningExponent_one
  have hMultOne : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).mult = 1 := hmu.symm.trans htm
  have hIdeal : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).ideal
      = LowerDimReductionPullback.tunedIdealAtLength (MaxContactCoverData.coverTriple T h.valid)
        (separateAllBoundary T h.valid hinv A) hft :=
    LowerDimReductionPullback.ideal_derivedTriple _ _ hft _ _
  have hIdeal2 : LowerDimReductionPullback.tunedIdealAtLength (MaxContactCoverData.coverTriple T h.valid)
        (separateAllBoundary T h.valid hinv A) hft
      = FunctorialResolution.EmbeddedResolution.balancedTunedSheaf (MaxContactCoverData.coverTriple T h.valid).base
        ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
          (MaxContactCoverData.coverTriple T h.valid).structMap)
        ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
        (MaxContactCoverData.coverTriple T h.valid).mult :=
    LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf _ _ hft
  have hIdealEq : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).ideal
      = (separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length :=
    (hIdeal.trans hIdeal2).trans
      (balancedTunedSheaf_eq_of_mult_eq_one_consolidated464
        ((separateAllBoundary T h.valid hinv A).proj
          (separateAllBoundary T h.valid hinv A).length ≫
          (MaxContactCoverData.coverTriple T h.valid).structMap)
        hftI
        ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
        (MaxContactCoverData.coverTriple T h.valid).mult hS1)
  have hOrderLe : ∀ x : ↥(reduceAlongHypersurfaceTriple T h.valid hinv A hft).scheme,
      orderAt (reduceAlongHypersurfaceTriple T h.valid hinv A hft).ideal x
        ≤ (((reduceAlongHypersurfaceTriple T h.valid hinv A hft).mult : ℕ) : ℕ∞) :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff _).1 hOB
  have hord : ∀ x : ↥((separateAllBoundary T h.valid hinv A).obj
      (separateAllBoundary T h.valid hinv A).length),
      orderAt ((separateAllBoundary T h.valid hinv A).ideal
        (separateAllBoundary T h.valid hinv A).length) x
        ≤ (((MaxContactCoverData.coverTriple T h.valid).mult : ℕ) : ℕ∞) :=
    LowerDimReductionPullback.orderAt_ideal_length_le hstar (MaxContactCoverData.coverTriple T h.valid) hSV hSO
      (separateAllBoundary T h.valid hinv A)
  have key := isMaxContactHypersurface_balancedTunedSheaf hstar (MaxContactCoverData.coverTriple T h.valid).base
    ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
      (MaxContactCoverData.coverTriple T h.valid).structMap)
    ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
    (MaxContactCoverData.coverTriple T h.valid).mult honeLe hord
    (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
      (MaxContactCoverData.coverMaxContactIdeal T h.valid)) hAdm0
  have hMaxContactHyp : IsMaxContactHypersurface (reduceAlongHypersurfaceTriple T h.valid hinv A hft).base
      (reduceAlongHypersurfaceTriple T h.valid hinv A hft).structMap
      (reduceAlongHypersurfaceTriple T h.valid hinv A hft).ideal
      (reduceAlongHypersurfaceTriple T h.valid hinv A hft).mult
      (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)) :=
    isMaxContactHypersurface_congr_consolidated464
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap)
      (reduceAlongHypersurfaceTriple T h.valid hinv A hft).structMap hftI hftT hpeq
      (hIdeal.trans hIdeal2).symm rfl hmu key
  have hNoe : ∀ t, t ≤ (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).length →
      IsLocallyNoetherian ((BlowupSequenceData.ofSequenceOfBlowups
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).obj t) := fun t ht =>
    isLocallyNoetherian_tunedMarkedBlowupSeq_schemeAt hstar (MaxContactCoverData.coverTriple T h.valid) hSV
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length hV'
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) t ht
  have hb0 : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).boundary.get ⟨0, hjlen⟩
      = MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid) :=
    get_zero_of_eq_cons_consolidated464 _ _ _ hbd hjlen
  have hi' : i ≤ (MarkedBlowupSequenceData.ofMarkedSequence
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft))).length := by
    rw [MarkedBlowupSequenceData.ofMarkedSequence_length]
    exact le_of_lt hi
  have hK0 : D 0 = (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
      (MaxContactCoverData.coverMaxContactIdeal T h.valid)).comap
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).isoZero.hom :=
    hD0.trans (congrArg (fun J => J.comap
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).isoZero.hom) hb0)
  have hKstep : ∀ t < (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).length,
      D (t + 1) = Blowup.strictTransform ((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).transitionMapSucc t)
          ((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).center t) (D t)
        ∨ D (t + 1) = (D t).comap
          ((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).transitionMapSucc t) := by
    intro t htlen
    by_cases hbc : b = true ∧ t = 0
    · obtain ⟨hbt, ht0⟩ := hbc
      subst ht0
      exact Or.inr (hbtrue hbt).2.2
    · exact Or.inl (hDsucc t htlen hbc)
  have hNsub : (↑((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).ideal i).support :
        Set ↥((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).schemeAt i))
      ⊆ ↑(D i).support := by
    intro x hx
    have h1 := support_ideal_subset_iteratedStrictTransform_consolidated464 hstar (reduceAlongHypersurfaceTriple T h.valid hinv A hft) hV'
      hOrderLe hMultOne
      (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)) hMaxContactHyp
      (MarkedBlowupSequenceData.ofMarkedSequence (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft))) i hi'
      (locallyOfFiniteType_projectionToBase_comp hstar (reduceAlongHypersurfaceTriple T h.valid hinv A hft) hV'
        (MarkedBlowupSequenceData.ofMarkedSequence (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft))) i hi')
      (smooth_projectionToBase_comp hstar (reduceAlongHypersurfaceTriple T h.valid hinv A hft) hV'
        (MarkedBlowupSequenceData.ofMarkedSequence (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft))) i hi')
      hcz2 hx
    exact BlowupSequenceData.support_iteratedStrictTransform_subset_support
      (MarkedBlowupSequenceData.ofMarkedSequence (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft))).toBlowupSequenceData
      hNoe
      (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)) D hK0 hKstep i hi' h1
  have hctrl : (BlowupSequenceData.ofSequenceOfBlowups
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).controlledTransform
      ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
      (MaxContactCoverData.coverTriple T h.valid).mult i
      = (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).ideal i :=
    controlledTransform_eq_ideal_of_eq_consolidated464 (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft))
      ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
      (MaxContactCoverData.coverTriple T h.valid).mult hIdealEq.symm (hS1.trans hMultOne.symm) i (le_of_lt hi)
  have hctrlR : (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
        (separateAllBoundary T h.valid hinv A) hft
        [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
        (MaxContactCoverData.coverTriple T h.valid).boundary.length
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).controlledTransform
      ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
      (MaxContactCoverData.coverTriple T h.valid).mult i
      = (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).ideal i := hctrl
  have hidR : (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).ideal i
      = (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).ideal i :=
    (MarkedBlowupSequenceData.toBlowupSequenceData_controlledTransform_eq
      (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
        (separateAllBoundary T h.valid hinv A) hft
        [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
        (MaxContactCoverData.coverTriple T h.valid).boundary.length
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk) i (le_of_lt hi)).symm.trans hctrlR
  have hid : ((continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).dataAt i).ideal
      = (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).ideal i :=
    (MarkedBlowupSequenceData.dataAt_ideal
      (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
        (separateAllBoundary T h.valid hinv A) hft
        [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
        (MaxContactCoverData.coverTriple T h.valid).boundary.length
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk) i).trans hidR
  have hceR : (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).center i
      = (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).center i :=
    BlowupSequenceData.ofSequenceOfBlowups_center (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups i
  have hce : ((continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).dataAt i).center
      = (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).center i :=
    (MarkedBlowupSequenceData.dataAt_center
      (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
        (separateAllBoundary T h.valid hinv A) hft
        [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
        (MaxContactCoverData.coverTriple T h.valid).boundary.length
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk) i).trans hceR
  have hprojR : (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).proj i
      = (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).projectionToBase i :=
    BlowupSequenceData.ofSequenceOfBlowups_projectionToBase (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups i
  have hstm : ((continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).dataAt i).structMap
      = MarkedSequenceOfBlowups.projectionToSpec (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) i :=
    ((MarkedBlowupSequenceData.dataAt_structMap
      (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
        (separateAllBoundary T h.valid hinv A) hft
        [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
        (MaxContactCoverData.coverTriple T h.valid).boundary.length
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk) i).trans
      (congrArg (fun f => f ≫ ((separateAllBoundary T h.valid hinv A).proj
        (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap)) hprojR)).trans
      ((congrArg (fun g => (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).projectionToBase i ≫ g)
            hpeq).trans
        (MarkedSequenceOfBlowups.projectionToSpec_eq (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) i).symm)
  have hAb : (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).boundary i
      = (BlowupSequenceData.ofSequenceOfBlowups (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom
          (reduceAlongHypersurfaceTriple T h.valid hinv A hft).boundary i :=
    (MarkedBlowupSequenceData.ofMarkedSequence_boundary (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) i
      (le_of_lt hi)).symm
  have hAb2 : (BlowupSequenceData.ofSequenceOfBlowups
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom
        (reduceAlongHypersurfaceTriple T h.valid hinv A hft).boundary i
      = (BlowupSequenceData.ofSequenceOfBlowups (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom
          (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
            (MaxContactCoverData.coverMaxContactIdeal T h.valid)
            :: List.drop (MaxContactCoverData.coverTriple T h.valid).boundary.length
              ((separateAllBoundary T h.valid hinv A).boundary
                (separateAllBoundary T h.valid hinv A).length)) i :=
    congrArg (fun E => (BlowupSequenceData.ofSequenceOfBlowups
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom E i) hbd
  have hAb3 : (BlowupSequenceData.ofSequenceOfBlowups
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom
        (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)
          :: List.drop (MaxContactCoverData.coverTriple T h.valid).boundary.length
            ((separateAllBoundary T h.valid hinv A).boundary
              (separateAllBoundary T h.valid hinv A).length)) i
      = (BlowupSequenceData.ofSequenceOfBlowups
          (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).iteratedStrictTransform i
          (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
            (MaxContactCoverData.coverMaxContactIdeal T h.valid))
        :: (BlowupSequenceData.ofSequenceOfBlowups (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom
            (List.drop (MaxContactCoverData.coverTriple T h.valid).boundary.length
              ((separateAllBoundary T h.valid hinv A).boundary
                (separateAllBoundary T h.valid hinv A).length)) i :=
    BlowupSequenceData.boundary_cons _ _ _ i
  have hAb4 : (BlowupSequenceData.ofSequenceOfBlowups
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom
        (List.drop (MaxContactCoverData.coverTriple T h.valid).boundary.length
          ((separateAllBoundary T h.valid hinv A).boundary
            (separateAllBoundary T h.valid hinv A).length)) i
      = List.map ((BlowupSequenceData.ofSequenceOfBlowups
            (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).iteratedStrictTransform i)
          (List.drop (MaxContactCoverData.coverTriple T h.valid).boundary.length
            ((separateAllBoundary T h.valid hinv A).boundary
              (separateAllBoundary T h.valid hinv A).length))
        ++ (BlowupSequenceData.ofSequenceOfBlowups
            (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom [] i :=
    BlowupSequenceData.boundary_eq_map_iteratedStrictTransform_append _ _ i
  have hAfull : (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).boundary i
      = (BlowupSequenceData.ofSequenceOfBlowups
          (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).iteratedStrictTransform i
          (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
            (MaxContactCoverData.coverMaxContactIdeal T h.valid))
        :: (List.map ((BlowupSequenceData.ofSequenceOfBlowups
              (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).iteratedStrictTransform i)
            (List.drop (MaxContactCoverData.coverTriple T h.valid).boundary.length
              ((separateAllBoundary T h.valid hinv A).boundary
                (separateAllBoundary T h.valid hinv A).length))
          ++ (BlowupSequenceData.ofSequenceOfBlowups
              (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom [] i) :=
    (hAb.trans hAb2).trans (hAb3.trans (congrArg (fun l =>
      (BlowupSequenceData.ofSequenceOfBlowups (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).iteratedStrictTransform i
        (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)) :: l) hAb4))
  have hRb : (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).boundary i
      = List.map ((BlowupSequenceData.ofSequenceOfBlowups
            (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).iteratedStrictTransform i)
          ((separateAllBoundary T h.valid hinv A).boundary
            (separateAllBoundary T h.valid hinv A).length)
        ++ (BlowupSequenceData.ofSequenceOfBlowups
            (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom [] i :=
    (MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq_boundary_of_le
      (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
        (separateAllBoundary T h.valid hinv A) hft
        [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
        (MaxContactCoverData.coverTriple T h.valid).boundary.length
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk) i (le_of_lt hi)).symm.trans
      (BlowupSequenceData.boundary_eq_map_iteratedStrictTransform_append
        (BlowupSequenceData.ofSequenceOfBlowups (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups)
        ((separateAllBoundary T h.valid hinv A).boundary
          (separateAllBoundary T h.valid hinv A).length) i)
  have hOther : MarkedSequenceOfBlowups.otherBoundaryLocus
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) 0 i
      ⊆ ((continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
          (separateAllBoundary T h.valid hinv A) hft
          [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
            (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
          (MaxContactCoverData.coverTriple T h.valid).boundary.length
          (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).dataAt i).boundarySupport := by
    intro x hx
    obtain ⟨idx, hidx, hxs⟩ :=
      (MarkedSequenceOfBlowups.mem_otherBoundaryLocus_iff
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) 0 i x).1 hx
    have hmem := get_mem_of_eq_cons_of_ne_zero_consolidated464 _ _ _ hAfull idx hidx
    have hmem2 : ((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).boundary i).get idx
        ∈ (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
            (separateAllBoundary T h.valid hinv A) hft
            [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
              (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
            (MaxContactCoverData.coverTriple T h.valid).boundary.length
            (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).boundary i := by
      rw [hRb]
      rcases List.mem_append.1 hmem with h1 | h2
      · obtain ⟨y, hy, hfy⟩ := List.mem_map.1 h1
        exact List.mem_append.2 (Or.inl (List.mem_map.2 ⟨y, List.mem_of_mem_drop hy, hfy⟩))
      · exact List.mem_append.2 (Or.inr h2)
    exact mem_boundarySupport_of_mem_support_of_mem_boundary_consolidated464 _ i _ hmem2 x hxs
  have hmain : OrderCertificate ((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).schemeAt i)
      (MarkedSequenceOfBlowups.projectionToSpec (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) i)
      ((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).ideal i) 1
      ((continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
          (separateAllBoundary T h.valid hinv A) hft
          [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
            (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
          (MaxContactCoverData.coverTriple T h.valid).boundary.length
          (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).dataAt i).boundarySupport
      ((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).center i) := by
    refine orderCertificate_one_of_isSmoothDivisor_consolidated464 (hopen (reduceAlongHypersurfaceTriple T h.valid hinv A hft).base) _ _ _ _ (D i)
      (hDsm i (le_of_lt hi)) hNsub (hcenter i hi) ?_
    by_cases hbc : b = true ∧ i = 0
    · left
      obtain ⟨hbt, hi0⟩ := hbc
      subst hi0
      exact (hbtrue hbt).2.1
    · right
      obtain ⟨J, hJnz, hJl, hJc⟩ := hJsh i hi hbc
      refine ⟨J, hJnz, ?_, ?_⟩
      · intro x hxm
        exact hJl x (fun hc => hxm (hOther hc))
      · exact principalizationCertificate_mono_of_subset (Set.preimage_mono hOther)
          (principalizationCertificate_congr_mult_consolidated464 hMultOne hJc)
  exact orderCertificate_congr_morphism_ideal_center_consolidated464 hstm.symm hid.symm hce.symm hmain

theorem orderCertificate_coverMarkedBlowupData_of_mult_eq_one (t : ℕ)
    (ht : t <
      (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).length) :
    OrderCertificate
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
        (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.schemeAt t)
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
          (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.projectionToBase t ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap)
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
        (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.ideal t) 1
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
        (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.boundaryLocus t)
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
        (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.center t) :=
  orderCertificate_coverMarkedBlowupData hstar hinv P hmono A B hspec T h
    (continuationOrderCertificate_of_mult_eq_one hstar hopen hinv P hmono A B hspec T h hmult) hmult t ht


end

end BoundarySeparationByMaxContact

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SmoothDivisorSmoothPullback
section


section
namespace FunctorialResolution.EmbeddedResolution

def IsSmoothDivisorStableUnderSmoothPullback : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (P Y : Scheme.{u})
    (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p]
    [LocallyOfFiniteType p]
    (g : Y ⟶ P) [Smooth g]
    [LocallyOfFiniteType (g ≫ p)]
    (D : P.IdealSheafData), IsSmoothDivisor p D → IsSmoothDivisor (g ≫ p) (D.comap g)

section
variable {P Y : Scheme.{u}} (g : Y ⟶ P)

private theorem restrictIdeal_comap_eq_comap_restrictIdeal_consolidated460 (I : P.IdealSheafData) {U : P.Opens} {V : Y.Opens} {f : V.toScheme ⟶ U.toScheme}
    (hf : f ≫ U.ι = V.ι ≫ g) :
    restrictIdeal (I.comap g) V = (restrictIdeal I U).comap f := by
  rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, hf]

private theorem restrictIdeal_comap_le_of_restrictIdeal_le_consolidated460 {I J : P.IdealSheafData} {U : P.Opens}
    (hle : restrictIdeal I U ≤ restrictIdeal J U) (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U) :
    restrictIdeal (I.comap g) V ≤ restrictIdeal (J.comap g) V := by
  have hf : (Y.homOfLE hV ≫ (g ∣_ U)) ≫ U.ι = V.ι ≫ g := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  rw [restrictIdeal_comap_eq_comap_restrictIdeal_consolidated460 g I hf,
    restrictIdeal_comap_eq_comap_restrictIdeal_consolidated460 g J hf]
  exact Scheme.IdealSheafData.comap_mono _ hle


end

theorem IsMaxContactHypersurface.isSmoothDivisor {k : Type u} [Field k] [CharZero k]
    {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)} [Smooth p]
    [LocallyOfFiniteType p] {A : P.IdealSheafData} {μ : ℕ}
    {H : P.IdealSheafData} (h : IsMaxContactHypersurface k p A μ H) :
    IsSmoothDivisor p H := by
  refine isSmoothDivisor_of_locally_coordIdeal H ?_
  intro x
  obtain ⟨U, hU, hxU, hcase⟩ := h x
  rcases hcase with ⟨-, htop⟩ | ⟨n, c, j, hHU, -⟩
  · obtain ⟨U', m, hxU', hU'U, -, ⟨c'⟩⟩ := exists_etaleChart_le p x U hxU
    exact ⟨U', hxU', m, c', Or.inl (restrictIdeal_eq_top_of_le H hU'U htop)⟩
  · exact ⟨U, hxU, n, c, Or.inr ⟨j, hHU⟩⟩

section
variable {k : Type u} [Field k] [CharZero k] {P Y : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)} [Smooth p] [LocallyOfFiniteType p] (g : Y ⟶ P) [Smooth g] [LocallyOfFiniteType (g ≫ p)] {A : P.IdealSheafData} {μ : ℕ} {H : P.IdealSheafData}

theorem IsMaxContactHypersurface.comap_of_forall_etaleChart_coordIdeal (h : IsMaxContactHypersurface k p A μ H) (hμ : 1 ≤ μ)
    (hcharts : ∀ y : Y, y ∈ (H.comap g).support →
      ∃ (V : Y.Opens) (n : ℕ) (c : EtaleChart (g ≫ p) V n) (j : Fin n),
        y ∈ V ∧ restrictIdeal (H.comap g) V = c.coordIdeal {j}) :
    IsMaxContactHypersurface k (g ≫ p) (A.comap g) μ (H.comap g) := by
  intro y
  by_cases hy : y ∈ (H.comap g).support
  · obtain ⟨V, n, c, j, hyV, hHV⟩ := hcharts y hy
    have hx : g.base y ∈ H.support := (Scheme.IdealSheafData.mem_support_comap ..).mp hy
    obtain ⟨U, hU, hxU, hcase⟩ := h (g.base y)
    have hle : restrictIdeal H U ≤ restrictIdeal (maxContactIdeal k p A μ) U := by
      rcases hcase with ⟨-, htop⟩ | ⟨n₀, c₀, j₀, hHU, hmc⟩
      · exact absurd hx (notMem_support_of_mem_opens_of_restrictIdeal_eq_top H U htop _ hxU)
      · rw [hHU]
        exact hmc
    have hyVU : y ∈ (V ⊓ g ⁻¹ᵁ U : Y.Opens) := ⟨hyV, hxU⟩
    obtain ⟨V', hV'aff, hyV', hV'le⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hyVU
    have hV'V : V' ≤ V := le_trans hV'le inf_le_left
    have hV'U : V' ≤ g ⁻¹ᵁ U := le_trans hV'le inf_le_right
    have heq : restrictIdeal (H.comap g) V' = (c.restrict hV'V).coordIdeal {j} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hV'V c (H.comap g) {j} hHV
    refine ⟨V', hV'aff, hyV', Or.inr ⟨n, c.restrict hV'V, j, heq, ?_⟩⟩
    have hgoal : (c.restrict hV'V).coordIdeal {j} ≤
        restrictIdeal (maxContactIdeal k (g ≫ p) (A.comap g) μ) V' := by
      rw [← heq, maxContactIdeal_comap k p g A μ]
      exact restrictIdeal_comap_le_of_restrictIdeal_le_consolidated460 g hle V' hV'U
    exact hgoal
  · have hWopen : IsOpen (((H.comap g).support : Set ↥Y)ᶜ) :=
      (H.comap g).support.2.isOpen_compl
    obtain ⟨V, hVaff, hyV, hVW⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
        (show y ∈ (⟨((H.comap g).support : Set ↥Y)ᶜ, hWopen⟩ : Y.Opens) from hy)
    refine ⟨V, hVaff, hyV, Or.inl ⟨?_, ?_⟩⟩
    · rw [Set.disjoint_left]
      intro z hz hzV
      have hz2 := hz
      rw [orderAtLeastLocus_comap k p g A μ] at hz2
      have hz3 : g.base z ∈ H.support := h.orderAtLeastLocus_subset_support hμ hz2
      have hz4 : z ∈ (H.comap g).support :=
        (Scheme.IdealSheafData.mem_support_comap ..).mpr hz3
      exact (hVW hzV) hz4
    · refine (FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_top_iff_forall_notMem_support _ _).mpr ?_
      intro z hzV
      exact hVW hzV

theorem IsMaxContactHypersurface.comap_of_isSmoothDivisorStableUnderSmoothPullback (hdiv : IsSmoothDivisorStableUnderSmoothPullback.{u})
    (hH : IsSmoothDivisor p H)
    (h : IsMaxContactHypersurface k p A μ H) (hμ : 1 ≤ μ) :
    IsMaxContactHypersurface k (g ≫ p) (A.comap g) μ (H.comap g) := by
  refine IsMaxContactHypersurface.comap_of_forall_etaleChart_coordIdeal g h hμ ?_
  intro y hy
  obtain ⟨V, m, c, j, hyV, heq⟩ :=
    exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton (g ≫ p) (H.comap g)
      (hdiv k P Y p g H hH) y hy
  exact ⟨V, m, c, j, hyV, heq⟩


end

theorem maxContactHypersurfaceSmoothPullback_of_isSmoothDivisorStableUnderSmoothPullback
    (hdiv : IsSmoothDivisorStableUnderSmoothPullback.{u}) : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u} := by
  intro k hk hk0 P p hsp hfp Y g hsg hfg A μ hμ H hH
  exact IsMaxContactHypersurface.comap_of_isSmoothDivisorStableUnderSmoothPullback g hdiv
    (IsMaxContactHypersurface.isSmoothDivisor hH) hH hμ

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SmoothPullbackMaxContactCover
section


section
namespace FunctorialResolution.EmbeddedResolution

namespace OrderReduction

def ValidPullbackAlongSmooth : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h] [QuasiCompact q],
      h ≫ T.structMap = q → (T.pullbackAlong Y q h).IsAdmissible

theorem validPullbackAlongSmooth_iff :
    ValidPullbackAlongSmooth.{u} ↔
      ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
        (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [Smooth h] [QuasiCompact q],
        h ≫ T.structMap = q → (T.pullbackAlong Y q h).IsAdmissible :=
  Iff.rfl

end OrderReduction

namespace MaxContactCoverData

section
variable {X : Scheme.{u}}

private theorem support_pow_subset_consolidated459 (I : X.IdealSheafData) (s : ℕ) :
    ((I ^ s).support : Set ↥X) ⊆ (I.support : Set ↥X) := by
  intro x hx
  simp only [SetLike.mem_coe] at hx ⊢
  rw [mem_support_iff_stalkIdeal_ne_top] at hx ⊢
  intro hI
  apply hx
  rw [stalkIdeal_pow, hI, Ideal.top_pow]

private theorem prod_map_range_pow_ite_eq_pow_consolidated459 (A : ℕ → X.IdealSheafData) (n s : ℕ) :
    (List.map (fun j => A j ^ (if j = n then s else 0)) (List.range (n + 1))).prod = A n ^ s := by
  have h1 : (List.map (fun j => A j ^ (if j = n then s else 0)) (List.range n)).prod = 1 := by
    apply List.prod_eq_one
    intro y hy
    simp only [List.mem_map, List.mem_range] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    rw [if_neg (Nat.ne_of_lt hj), pow_zero]
  rw [List.range_succ, List.map_append, List.prod_append, h1, one_mul]
  simp


end

private theorem exists_le_and_pow_le_tunedSheaf_consolidated459 (k : Type u) [Field k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] (I : X.IdealSheafData) (m s : ℕ) (hm : 1 ≤ m) :
    ∃ J : X.IdealSheafData, I ≤ J ∧ J ^ s ≤ tunedSheaf k p I m s := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine ⟨derivIdealSheafIterate k p n I, le_derivIdealSheafIterate k p n I, ?_⟩
  have h0 : (∑ j ∈ Finset.range (n + 1), (n + 1 - j) * (if j = n then s else 0))
      = (n + 1 - n) * (if n = n then s else 0) := by
    refine Finset.sum_eq_single n (fun b _ hb => by simp [hb]) (fun h => ?_)
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h
  have hsum : (∑ j ∈ Finset.range (n + 1), (n + 1 - j) * (if j = n then s else 0)) = s := by
    rw [h0, if_pos rfl, Nat.add_sub_cancel_left, one_mul]
  have h := prod_pow_derivIdealSheafIterate_le_tunedSheaf k p I (n + 1) s
    (fun j => if j = n then s else 0) hsum.ge
  rw [prod_map_range_pow_ite_eq_pow_consolidated459] at h
  exact h

section
variable (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)

theorem balancedTunedIdeal_eq_balancedTunedSheaf [LocallyOfFiniteType T.structMap] :
    balancedTunedIdeal T hv = FunctorialResolution.EmbeddedResolution.balancedTunedSheaf T.base T.structMap T.ideal T.mult :=
  rfl

theorem nonzeroOnComponents_balancedTunedIdeal :
    NonzeroOnComponents (balancedTunedIdeal T hv) := by
  have := hv.locallyOfFiniteType
  obtain ⟨J, hIJ, hJ⟩ :=
    exists_le_and_pow_le_tunedSheaf_consolidated459 T.base T.structMap T.ideal T.mult (tuningExponent T.mult) hv.one_le_mult
  have hle : J ^ tuningExponent T.mult ≤ balancedTunedIdeal T hv := by
    rw [balancedTunedIdeal_eq_balancedTunedSheaf T hv, balancedTunedSheaf_eq]
    exact hJ
  have hnz := hv.nonzeroOnComponents
  rw [nonzeroOnComponents_iff] at hnz ⊢
  intro C hC hsub
  refine hnz C hC ?_
  intro x hx
  have h1 := hsub hx
  have h2 := SetLike.coe_subset_coe.2 (Scheme.IdealSheafData.support_antitone hle) h1
  have h3 := support_pow_subset_consolidated459 J (tuningExponent T.mult) h2
  exact SetLike.coe_subset_coe.2 (Scheme.IdealSheafData.support_antitone hIJ) h3


end

theorem orderAt_balancedTunedIdeal_le_tunedMult (htf : TunedSheafProperties.{u}) (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) (x : ↥T.scheme) :
    orderAt (balancedTunedIdeal T hv) x ≤ ((tunedMult T : ℕ) : ℕ∞) := by
  have := hv.locallyOfFiniteType
  have := hv.charZero
  have := hv.smooth
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  · have htop : balancedTunedIdeal T hv = ⊤ := by
      rw [balancedTunedIdeal_eq_balancedTunedSheaf T hv]
      exact balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty T.base T.structMap T.ideal hv.one_le_mult hemp
    rw [htop, orderAt_top]
    simp
  · have hmax : MaxOrderEq T.ideal T.mult :=
      ⟨(orderLE_iff T.ideal T.mult).2 hord, Set.nonempty_iff_ne_empty.2 hemp⟩
    have hLE := htf.coSupport_tunedSheaf_eq_and_orderLE.orderLE T.base T.scheme T.structMap
      T.ideal T.mult hv.one_le_mult hmax (tuningExponent T.mult) (one_le_tuningExponent T.mult)
    rw [orderLE_iff] at hLE
    have h2 : balancedTunedIdeal T hv = tunedSheaf T.base T.structMap T.ideal T.mult (tuningExponent T.mult) := by
      rw [balancedTunedIdeal_eq_balancedTunedSheaf T hv, balancedTunedSheaf_eq]
    rw [h2]
    exact hLE x

theorem isAdmissible_coverTriple_of_validPullbackAlongSmooth (hpb : OrderReduction.ValidPullbackAlongSmooth.{u})
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hgood : MaxContactReduction.IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType
      (balancedTunedIdeal T hv) (tunedMult T)) :
    (coverTriple T hv).IsAdmissible := by
  have hvt := MaxContactOpenCover.isAdmissible_tunedTriple T hv (nonzeroOnComponents_balancedTunedIdeal T hv)
  have hqc := MaxContactOpenCover.quasiCompact_coverMap_comp_structureMorphism T hv hgood
  rw [MaxContactOpenCover.coverTriple_eq_tunedTriple_pullbackAlong T hv]
  exact @hpb (MaxContactOpenCover.tunedTriple T hv) hvt (chosenCoverData T hv).disjointUnion
    (coverMap T hv ≫ T.structMap) (coverMap T hv) (MaxContactCoverData.instSmoothCoverMap T hv) hqc rfl

theorem isSmoothDivisor_coverMaxContactIdeal (_hpb : OrderReduction.ValidPullbackAlongSmooth.{u})
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hgood : MaxContactReduction.IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType
      (balancedTunedIdeal T hv) (tunedMult T)) :
    IsSmoothDivisor (coverTriple T hv).structMap (coverMaxContactIdeal T hv) := by
  refine FunctorialResolution.EmbeddedResolution.isSmoothDivisor_of_locally_coordIdeal (coverMaxContactIdeal T hv) ?_
  intro x
  obtain ⟨U, hxU, m, c, a, _hinj, hnone, hsome⟩ :=
    (MaxContactCoverGeometry.inStrictNormalCrossingPositionAt_of_isMaxContactCover T hv hgood x).exists_etaleChart
  refine ⟨U, hxU, m, c, ?_⟩
  rcases ha : a 0 with _ | t
  · exact Or.inl (hnone 0 (by simp) ha)
  · exact Or.inr ⟨t, hsome 0 (by simp) t ha⟩

end MaxContactCoverData

namespace OrderReduction

theorem maxContactCoverProperties_of_tunedSheafProperties (htf : TunedSheafProperties.{u}) (hdim : DimensionNonincreasingAlongBlowups.{u})
    (hpb : ValidPullbackAlongSmooth.{u}) : MaxContactCoverProperties.{u} := by
  refine
    { strictTransform_admissible := ?_
      coSupport_le_preimage := ?_
      schemeDim_level_le := ?_
      exists_goodCover := ?_
      hasSNCWith_cons := ?_
      valid_level := ?_
      orderAt_level_le := ?_
      coverTriple_dim_le := ?_
      coverTriple_valid := ?_
      coverContact_admissible := ?_
      coverContact_snc := ?_
      tuning := htf }
  · intro k _ _ P P₁ p _ _ _ π _ Z E hZ hπ A A₁ μ hμ hordA hsupp htr H hH
    exact FunctorialResolution.EmbeddedResolution.isMaxContactHypersurface_strictTransform_of_orderAt_le k p π Z E hZ hπ A A₁ μ hμ hordA
      hsupp htr H hH
  · intro X X₁ π Z hπ A A₁ μ htr hsupp
    exact FunctorialResolution.EmbeddedResolution.OrderLocusBlowup.orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf π Z hπ A A₁ μ htr hsupp
  · intro T hT s i hi
    exact hdim T hT s i hi
  · intro T hv hord
    exact MaxContactOpenCover.exists_isMaxContactCover T hv (MaxContactCoverData.orderAt_balancedTunedIdeal_le_tunedMult htf T hv hord)
  · intro k _ P p _ Z H N _hsmZ hsnc hZN hHZ
    exact FunctorialResolution.EmbeddedResolution.hasStrictNormalCrossingsWith_cons_of_le p Z H N hsnc hZN hHZ
  · intro T hT s i hi
    exact MarkedIdealWithBoundary.IsAdmissible.transformAt effectiveCartierSupportContainsNoComponent hT s i hi
  · intro T hT hord s i hi x
    exact FunctorialResolution.EmbeddedResolution.orderAt_ideal_le_mult_along_sequence T hT hord s i hi x
  · intro T hv
    exact MaxContactOpenCover.krullDimSucc_coverTriple_scheme_le_dim T hv
  · intro T hv _hord hgood
    exact MaxContactCoverData.isAdmissible_coverTriple_of_validPullbackAlongSmooth hpb T hv hgood
  · intro T hv hgood _
    exact MaxContactCoverGeometry.isMaxContactHypersurface_coverMaxContactIdeal T hv hgood
  · intro T hv hgood
    exact MaxContactCoverGeometry.inStrictNormalCrossingPosition_of_isMaxContactCover T hv hgood
      (MaxContactCoverData.isSmoothDivisor_coverMaxContactIdeal hpb T hv hgood)

end OrderReduction

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
section

open CategoryTheory.Limits

section
namespace FunctorialResolution.EmbeddedResolution

structure PrincipalizationGeometryHypotheses : Prop where
  maxContactTransport : OrderCertificateIsoInvariantOfMaxContact.{u}
  exceptional_components_not_subset : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ Z : T.scheme.IdealSheafData,
      Smooth (Z.subschemeι ≫ T.structMap) →
      HasStrictNormalCrossingsWith T.structMap Z T.boundary →
    ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
    ∀ (J : T.scheme.IdealSheafData) (c : ℕ),
      (∀ x : ↥T.scheme, x ∈ Z.support → orderAt J x = (c : ℕ∞)) →
    ∀ J' : X'.IdealSheafData,
      Blowup.exceptionalIdeal π Z ^ c * J' = J.comap π →
    ∀ C' : Set ↥X', IsIrreducibleComponentOf C' (↑(Blowup.exceptionalIdeal π Z).support : Set ↥X') →
      ¬ C' ⊆ (↑J'.support : Set ↥X')
  orderAt_baseChange : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (I : T.scheme.IdealSheafData) (y : ↥(T.baseChange L f).scheme),
      orderAt (I.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f))) y =
        orderAt I ((pullback.fst T.structMap (specMapOfFieldHom T.base L f)).base y)
  controlledTransform_orderAt_le : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ Z : T.scheme.IdealSheafData,
      Smooth (Z.subschemeι ≫ T.structMap) →
      HasStrictNormalCrossingsWith T.structMap Z T.boundary →
    ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
    ∀ (J : T.scheme.IdealSheafData) (c : ℕ),
      (∀ x : ↥T.scheme, x ∈ Z.support → orderAt J x = (c : ℕ∞)) →
    ∀ J' : X'.IdealSheafData,
      Blowup.exceptionalIdeal π Z ^ c * J' = J.comap π →
    ∀ x' : ↥X', x' ∈ (Blowup.exceptionalIdeal π Z).support → orderAt J' x' ≤ (c : ℕ∞)
  splitting_baseChange : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L),
      (T.baseChange L f).IsAdmissible →
    ∀ M N : T.scheme.IdealSheafData,
      IsMonomialSplitting T.boundary T.ideal M N →
      IsMonomialSplitting (T.baseChange L f).boundary (T.baseChange L f).ideal
        (M.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f)))
        (N.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f)))
  splitting_smooth_pullback : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
      (T.pullbackAlong Y q h).IsAdmissible →
    ∀ M N : T.scheme.IdealSheafData,
      IsMonomialSplitting T.boundary T.ideal M N →
      IsMonomialSplitting (T.pullbackAlong Y q h).boundary (T.pullbackAlong Y q h).ideal
        (M.comap h) (N.comap h)
  splitting_exists : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∃ M N : T.scheme.IdealSheafData, IsMonomialSplitting T.boundary T.ideal M N
  splitting_unique : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ M N M' N' : T.scheme.IdealSheafData,
      IsMonomialSplitting T.boundary T.ideal M N →
      IsMonomialSplitting T.boundary T.ideal M' N' →
      M = M' ∧ N = N'
  strictTransform_components : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ Z : T.scheme.IdealSheafData,
      Smooth (Z.subschemeι ≫ T.structMap) →
      HasStrictNormalCrossingsWith T.structMap Z T.boundary →
    ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
    ∀ D ∈ T.boundary,
    ∀ C' : Set ↥X', IsIrreducibleComponentOf C' (↑(Blowup.strictTransform π Z D).support : Set ↥X') →
      ∃ (η' : ↥X') (C : Set ↥T.scheme),
        C' = closure {η'} ∧
        η' ∉ (Blowup.exceptionalIdeal π Z).support ∧
        IsIrreducibleComponentOf C (↑D.support : Set ↥T.scheme) ∧
        ¬ C ⊆ (↑Z.support : Set ↥T.scheme) ∧
        C = closure {π.base η'}
  monomialInputs : MonomialGeometryHypotheses.{u}

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderAlongBlowupSequence
section


namespace FunctorialResolution.EmbeddedResolution

def OrderAtComapOffExceptionalLocus : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (Z : T.scheme.IdealSheafData), Blowup.IsBlowupAlongIdealSheaf π Z →
      ∀ x' : ↥X', x' ∉ (Blowup.exceptionalIdeal π Z).support →
        ∀ A : T.scheme.IdealSheafData, orderAt (A.comap π) x' = orderAt A (π x')

theorem orderAtComapOffExceptionalLocus_of_monomialGeometryHypotheses (h : MonomialGeometryHypotheses.{u}) :
    OrderAtComapOffExceptionalLocus.{u} :=
  h.orderAt_comap_off_exceptional

theorem orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf (hgeom : OrderAtComapOffExceptionalLocus.{u})
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (Z : T.scheme.IdealSheafData)
    (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (J : T.scheme.IdealSheafData) (μ : ℕ)
    (hZ : (↑Z.support : Set ↥T.scheme) ⊆ orderAtLeastLocus J μ)
    (J' : X'.IdealSheafData)
    (hJ' : Blowup.exceptionalIdeal π Z ^ μ * J' = J.comap π)
    (c : ℕ) (hc : c ≤ μ) :
    orderAtLeastLocus J' c ⊆ ⇑π ⁻¹' orderAtLeastLocus J c := by
  intro x' hx'
  rw [Set.mem_preimage, mem_orderAtLeastLocus_iff]
  by_cases hE : x' ∈ (Blowup.exceptionalIdeal π Z).support
  · have hmem : x' ∈ (↑(Z.comap π).support : Set ↥X') := by
      rw [← Blowup.exceptionalIdeal_eq_comap π Z]
      exact hE
    have hπx : π x' ∈ (↑Z.support : Set ↥T.scheme) := by
      simpa [AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap] using hmem
    have h2 : (μ : ℕ∞) ≤ orderAt J (π x') := (mem_orderAtLeastLocus_iff J μ (π x')).1 (hZ hπx)
    exact le_trans (by exact_mod_cast hc) h2
  · have h1 : orderAt (J.comap π) x' = orderAt J (π x') := hgeom T hT X' π Z hπ x' hE J
    have h2 := add_orderAt_le_orderAt_mul (Blowup.exceptionalIdeal π Z ^ μ) J' x'
    rw [hJ', h1] at h2
    have h3 : (c : ℕ∞) ≤ orderAt J' x' := (mem_orderAtLeastLocus_iff J' c x').1 hx'
    exact le_trans h3 (le_trans le_add_self h2)

section
variable {X : Scheme.{u}} (s : SequenceOfBlowups X)

private theorem transitionMap_refl_apply_consolidated358 {i : ℕ} (h : i ≤ i)
    (x : ↥(s.schemeAt i)) : s.transitionMap h x = x :=
  congrFun (congrArg (fun f : s.schemeAt i ⟶ s.schemeAt i => (f : ↥(s.schemeAt i) → ↥(s.schemeAt i)))
    (s.transitionMap_self h)) x

private theorem transitionMap_comp_apply_consolidated358 {i j l : ℕ} (hij : i ≤ j)
    (hjl : j ≤ l) (x : ↥(s.schemeAt l)) :
    s.transitionMap hij (s.transitionMap hjl x) = s.transitionMap (hij.trans hjl) x := by
  have h := s.transitionMap_trans hij hjl
  calc s.transitionMap hij (s.transitionMap hjl x) = (s.transitionMap hjl ≫ s.transitionMap hij) x := rfl
    _ = s.transitionMap (hij.trans hjl) x := by rw [h]


end

namespace MarkedSequenceOfBlowups

section
variable (hgeom : OrderAtComapOffExceptionalLocus.{u}) (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (hval : ∀ i ≤ s.toSequenceOfBlowups.length, (T.transformAt s i).IsAdmissible)
include hgeom hval

theorem orderAtLeastLocus_succ_subset_preimage_blowupMorphism (i : ℕ) (hi : i < s.toSequenceOfBlowups.length) (c : ℕ) (hc : c ≤ T.mult) :
    orderAtLeastLocus (s.ideal (i + 1)) c ⊆
      ⇑(s.toSequenceOfBlowups.transitionMapSucc i) ⁻¹' orderAtLeastLocus (s.ideal i) c := by
  have hvi := hval i (le_of_lt hi)
  exact orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf hgeom (T.transformAt s i) hvi
    (s.toSequenceOfBlowups.center i) (s.toSequenceOfBlowups.schemeAt (i + 1)) (s.toSequenceOfBlowups.transitionMapSucc i)
    (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism i hi) (s.ideal i) T.mult (s.center_order i hi)
    (s.ideal (i + 1)) (s.ideal_succ i hi) c hc

theorem orderAtLeastLocus_subset_preimage_transitionMap (c : ℕ) (hc : c ≤ T.mult) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ s.toSequenceOfBlowups.length) :
    orderAtLeastLocus (s.ideal j) c ⊆ ⇑(s.toSequenceOfBlowups.transitionMap hij) ⁻¹' orderAtLeastLocus (s.ideal i) c := by
  revert hj
  induction j, hij using Nat.le_induction with
  | base =>
      intro _ x hx
      rw [Set.mem_preimage, transitionMap_refl_apply_consolidated358]
      exact hx
  | succ j hij ih =>
      intro hj1
      have hjlt : j < s.toSequenceOfBlowups.length := Nat.lt_of_succ_le hj1
      have hstep := orderAtLeastLocus_succ_subset_preimage_blowupMorphism hgeom T s hval j hjlt c hc
      have hih := ih (le_of_lt hjlt)
      intro x hx
      rw [Set.mem_preimage]
      have h1 : s.toSequenceOfBlowups.transitionMapSucc j x ∈ orderAtLeastLocus (s.ideal j) c := hstep hx
      have h2 : s.toSequenceOfBlowups.transitionMap hij (s.toSequenceOfBlowups.transitionMapSucc j x) ∈
          orderAtLeastLocus (s.ideal i) c := hih h1
      rw [s.toSequenceOfBlowups.blowupMorphism_eq_transitionMap j, transitionMap_comp_apply_consolidated358] at h2
      exact h2


end

end MarkedSequenceOfBlowups

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialSplittingFunctoriality
section

open CategoryTheory.Limits

section
namespace FunctorialResolution.EmbeddedResolution

variable {X : Scheme.{u}}

private theorem mem_closure_image_iff_exists_prod_pow_consolidated385 {α : Type*} {N : Type*} [CommMonoid N]
    (E : List α) (f : α → N) (y : N) :
    y ∈ Submonoid.closure (f '' {D | D ∈ E}) ↔
      ∃ a : Fin E.length → ℕ, y = ∏ i, f (E.get i) ^ a i := by
  constructor
  · intro hy
    induction hy using Submonoid.closure_induction with
    | mem z hz =>
        obtain ⟨D, hD, rfl⟩ := hz
        have hD' : D ∈ E := hD
        obtain ⟨i, hi⟩ := List.get_of_mem hD'
        refine ⟨fun j => if j = i then 1 else 0, ?_⟩
        have h1 : (∏ j, f (E.get j) ^ (if j = i then 1 else 0))
            = f (E.get i) ^ (if i = i then 1 else 0) :=
          Finset.prod_eq_single i (fun j _ hj => by simp [hj])
            (fun h => absurd (Finset.mem_univ i) h)
        rw [h1, hi]
        simp
    | one => exact ⟨fun _ => 0, by simp⟩
    | mul z w hz hw ihz ihw =>
        obtain ⟨a, rfl⟩ := ihz
        obtain ⟨b, rfl⟩ := ihw
        refine ⟨a + b, ?_⟩
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, pow_add]
  · rintro ⟨a, rfl⟩
    apply Submonoid.prod_mem
    intro i _
    exact pow_mem (Submonoid.subset_closure (Set.mem_image_of_mem f (by simp))) _

theorem isMonomialIn_iff_forall_exists_mem_closure (E : List X.IdealSheafData)
    (M : X.IdealSheafData) :
    IsMonomialIn E M ↔ ∀ x : ↥X, ∃ U : X.Opens, x ∈ U ∧
      M.comap U.ι ∈
        Submonoid.closure ((fun D : X.IdealSheafData => D.comap U.ι) '' {D | D ∈ E}) := by
  unfold IsMonomialIn
  refine forall_congr' fun x => exists_congr fun U => and_congr_right fun _ => ?_
  exact (mem_closure_image_iff_exists_prod_pow_consolidated385 E (fun D : X.IdealSheafData => D.comap U.ι)
    (M.comap U.ι)).symm

theorem isMonomialIn_of_mem_of_ne_top {E E' : List X.IdealSheafData}
    (h : ∀ D ∈ E, D ≠ ⊤ → D ∈ E') {M : X.IdealSheafData} (hM : IsMonomialIn E M) :
    IsMonomialIn E' M := by
  rw [isMonomialIn_iff_forall_exists_mem_closure] at hM ⊢
  intro x
  obtain ⟨U, hxU, hMU⟩ := hM x
  refine ⟨U, hxU, Submonoid.mem_closure.mp hMU _ ?_⟩
  rintro y ⟨D, hD, rfl⟩
  by_cases hDtop : D = ⊤
  · have h1 : D.comap U.ι = 1 := by
      rw [hDtop]
      simp
    show D.comap U.ι ∈ _
    rw [h1]
    exact Submonoid.one_mem _
  · exact Submonoid.subset_closure ⟨D, h D hD hDtop, rfl⟩

section
variable {E E' : List X.IdealSheafData} (h : {D : X.IdealSheafData | D ∈ E ∧ D ≠ ⊤} = {D : X.IdealSheafData | D ∈ E' ∧ D ≠ ⊤})
include h

theorem isMonomialIn_of_setOf_mem_ne_top_eq {M : X.IdealSheafData} (hM : IsMonomialIn E M) :
    IsMonomialIn E' M := by
  refine isMonomialIn_of_mem_of_ne_top (fun D hD hDtop => ?_) hM
  have hmem : D ∈ {D : X.IdealSheafData | D ∈ E ∧ D ≠ ⊤} := ⟨hD, hDtop⟩
  rw [h] at hmem
  exact hmem.1

theorem isMonomialSplitting_of_setOf_mem_ne_top_eq {I M N : X.IdealSheafData} (hs : IsMonomialSplitting E I M N) :
    IsMonomialSplitting E' I M N := by
  refine ⟨hs.eq_mul, ?_, isMonomialIn_of_setOf_mem_ne_top_eq h hs.monomial, ?_⟩
  · intro x hx
    obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.1 (hs.monomial_support hx)
    have hDtop : D ≠ ⊤ := by
      intro hDt
      have hempty : (↑D.support : Set ↥X) = ∅ :=
        (AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty D).1 hDt
      rw [hempty] at hxD
      simp at hxD
    have hmem : D ∈ {D : X.IdealSheafData | D ∈ E ∧ D ≠ ⊤} := ⟨hD, hDtop⟩
    rw [h] at hmem
    exact Set.mem_iUnion₂.2 ⟨D, hmem.1, hxD⟩
  · intro D hD C hC hCsubD hCmax
    by_cases hDtop : D = ⊤
    · exfalso
      have hempty : (↑D.support : Set ↥X) = ∅ :=
        (AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty D).1 hDtop
      obtain ⟨y, hy⟩ := hC.nonempty
      have hy' := hCsubD hy
      rw [hempty] at hy'
      simp at hy'
    · have hmem : D ∈ {D : X.IdealSheafData | D ∈ E' ∧ D ≠ ⊤} := ⟨hD, hDtop⟩
      rw [← h] at hmem
      exact hs.transversal D hmem.1 C hC hCsubD hCmax


end

private theorem mem_nontrivialPart_iff_consolidated385 (E : List X.IdealSheafData)
    (D : X.IdealSheafData) :
    D ∈ MarkedIdealWithBoundary.nontrivialPart E ↔ D ∈ E ∧ D ≠ ⊤ := by
  classical
  simp [MarkedIdealWithBoundary.nontrivialPart, List.mem_filter]

section
variable {E E' : List X.IdealSheafData} (h : MarkedIdealWithBoundary.SameNontrivialBoundary E E')
include h

theorem MarkedIdealWithBoundary.SameNontrivialBoundary.setOf_mem_ne_top_eq :
    {D : X.IdealSheafData | D ∈ E ∧ D ≠ ⊤} = {D : X.IdealSheafData | D ∈ E' ∧ D ≠ ⊤} := by
  have hE : MarkedIdealWithBoundary.nontrivialPart E = MarkedIdealWithBoundary.nontrivialPart E' :=
    (MarkedIdealWithBoundary.sameNontrivialBoundary_iff E E').1 h
  ext D
  constructor
  · intro hD
    have hD' := (mem_nontrivialPart_iff_consolidated385 E D).2 hD
    rw [hE] at hD'
    exact (mem_nontrivialPart_iff_consolidated385 E' D).1 hD'
  · intro hD
    have hD' := (mem_nontrivialPart_iff_consolidated385 E' D).2 hD
    rw [← hE] at hD'
    exact (mem_nontrivialPart_iff_consolidated385 E D).1 hD'

theorem isMonomialSplitting_congr (I M N : X.IdealSheafData) :
    IsMonomialSplitting E I M N ↔ IsMonomialSplitting E' I M N :=
  ⟨fun hs => isMonomialSplitting_of_setOf_mem_ne_top_eq h.setOf_mem_ne_top_eq hs,
    fun hs => isMonomialSplitting_of_setOf_mem_ne_top_eq h.symm.setOf_mem_ne_top_eq hs⟩


end

private theorem coe_support_top_eq_empty_consolidated385 {X : Scheme.{u}} :
    ((⊤ : X.IdealSheafData).support : Set ↥X) = ∅ :=
  (AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty
    (⊤ : X.IdealSheafData)).1 rfl

theorem isMonomialSplitting_nil (I : X.IdealSheafData) :
    IsMonomialSplitting ([] : List X.IdealSheafData) I ⊤ I := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Scheme.IdealSheafData.one_eq_top, one_mul]
  · rw [coe_support_top_eq_empty_consolidated385]
    exact Set.empty_subset _
  · intro x
    refine ⟨⊤, by simp, fun _ => 0, ?_⟩
    rw [Scheme.IdealSheafData.comap_top, ← Scheme.IdealSheafData.one_eq_top]
    exact (Fin.prod_univ_zero _).symm
  · intro D hD
    exact absurd hD (by simp)

namespace IsMonomialSplitting

variable {E : List X.IdealSheafData} {I M N : X.IdealSheafData}

section
variable (h : IsMonomialSplitting E I M N)
include h

theorem le_nonMonomial : I ≤ N := by
  rw [h.eq_mul, Scheme.IdealSheafData.le_def]
  intro U
  rw [Scheme.IdealSheafData.ideal_mul]
  exact Ideal.mul_le_right

theorem support_nonMonomial_subset :
    (↑N.support : Set ↥X) ⊆ (↑I.support : Set ↥X) := by
  intro x hx
  have hxN : x ∈ N.support := hx
  have hIN : I ≤ N := h.le_nonMonomial
  have h1 : stalkIdeal N x ≠ ⊤ := (mem_support_iff_stalkIdeal_ne_top N x).1 hxN
  have h2 : stalkIdeal I x ≠ ⊤ := by
    intro hI
    apply h1
    have hle := stalkIdeal_mono hIN x
    rw [hI] at hle
    exact top_le_iff.1 hle
  exact (mem_support_iff_stalkIdeal_ne_top I x).2 h2

theorem nonzeroOnComponents_nonMonomial (hI : NonzeroOnComponents I) : NonzeroOnComponents N := by
  rw [nonzeroOnComponents_iff] at hI ⊢
  intro T hT hTsub
  exact hI T hT (hTsub.trans h.support_nonMonomial_subset)


end

theorem orderAt_eq_add {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [Smooth p]
    {E : List Y.IdealSheafData} {I M N : Y.IdealSheafData}
    (h : IsMonomialSplitting E I M N) (x : ↥Y) :
    orderAt I x = orderAt M x + orderAt N x := by
  rw [h.eq_mul]
  exact orderAt_mul k p M N x

private theorem idealSheafData_comap_prod_consolidated385 {Z W : Scheme.{u}} (f : W ⟶ Z) {κ : Type*}
    (s : Finset κ) (J : κ → Z.IdealSheafData) :
    (∏ i ∈ s, J i).comap f = ∏ i ∈ s, (J i).comap f := by
  induction s using Finset.cons_induction
  · rw [Finset.prod_empty, Finset.prod_empty, Scheme.IdealSheafData.one_eq_top,
      Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.one_eq_top]
  · rename_i b t hb ih
    rw [Finset.prod_cons, Finset.prod_cons, Scheme.IdealSheafData.comap_mul, ih]

theorem exists_comap_eq_prod_pow_of_orderAt_eq_zero (h : IsMonomialSplitting E I M N) {x : ↥X}
    (hx : orderAt N x = 0) :
    ∃ (U : X.Opens) (e : Fin E.length → ℕ), x ∈ U ∧
      I.comap U.ι = ∏ i : Fin E.length, ((E.get i).comap U.ι) ^ e i := by
  have hmon : ∀ y : ↥X, ∃ V : X.Opens, y ∈ V ∧ ∃ c : Fin E.length → ℕ,
      M.comap V.ι = ∏ i : Fin E.length, ((E.get i).comap V.ι) ^ c i := h.monomial
  obtain ⟨U, hxU, a, haM⟩ := hmon x
  have hxN : x ∉ N.support := (orderAt_eq_zero_iff_not_mem_support N x).1 hx
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : X.Opens, (U₀ : Set ↥X) = ((N.support : Set ↥X))ᶜ :=
    ⟨⟨((N.support : Set ↥X))ᶜ, N.support.2.isOpen_compl⟩, rfl⟩
  have hx0 : x ∈ (U₀ : Set ↥X) := by
    rw [hU₀]
    exact hxN
  have hxV : x ∈ U ⊓ U₀ := by
    have hmem : x ∈ ((U ⊓ U₀ : X.Opens) : Set ↥X) := by
      rw [TopologicalSpace.Opens.coe_inf]
      exact ⟨hxU, hx0⟩
    exact hmem
  have hle : U ⊓ U₀ ≤ U := inf_le_left
  have hcomp : X.homOfLE hle ≫ U.ι = (U ⊓ U₀).ι := by simp
  have restr : ∀ J : X.IdealSheafData,
      (J.comap U.ι).comap (X.homOfLE hle) = J.comap (U ⊓ U₀).ι := by
    intro J
    rw [← hcomp, Scheme.IdealSheafData.comap_comp]
  have hNtop : N.comap (U ⊓ U₀).ι = ⊤ := by
    refine Blowup.comap_eq_top_of_notMem_support _ N ?_
    intro y hy
    have hy1 : ((U ⊓ U₀).ι y) ∈ ((U ⊓ U₀ : X.Opens) : Set ↥X) := y.2
    rw [TopologicalSpace.Opens.coe_inf, hU₀] at hy1
    exact hy1.2 hy
  have hM : M.comap (U ⊓ U₀).ι
      = ∏ i : Fin E.length, ((E.get i).comap (U ⊓ U₀).ι) ^ a i := by
    rw [← restr M, haM, idealSheafData_comap_prod_consolidated385]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Scheme.IdealSheafData.comap_pow, restr]
  refine ⟨U ⊓ U₀, a, hxV, ?_⟩
  rw [h.eq_mul, Scheme.IdealSheafData.comap_mul, hNtop,
    ← Scheme.IdealSheafData.one_eq_top, mul_one, hM]

end IsMonomialSplitting

namespace PrincipalizationGeometryHypotheses

section
variable (hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
include hG hT

theorem isMonomialSplitting_monomialPart_nonMonomialPart :
    IsMonomialSplitting T.boundary T.ideal (monomialPart T.boundary T.ideal)
      (nonMonomialPart T.boundary T.ideal) := by
  obtain ⟨M, N, h⟩ := hG.splitting_exists T hT
  exact EmbeddedResolution.isMonomialSplitting_monomialPart_nonMonomialPart T.boundary T.ideal ⟨(M, N), h⟩

theorem nonMonomialPart_eq_of_isMonomialSplitting (M N : T.scheme.IdealSheafData) (h : IsMonomialSplitting T.boundary T.ideal M N) :
    nonMonomialPart T.boundary T.ideal = N :=
  (hG.splitting_unique T hT _ _ M N (hG.isMonomialSplitting_monomialPart_nonMonomialPart T hT) h).2

theorem nonMonomialPart_eq_ideal_of_boundary_eq_nil (hE : T.boundary = []) :
    nonMonomialPart T.boundary T.ideal = T.ideal := by
  have h : IsMonomialSplitting T.boundary T.ideal ⊤ T.ideal := by
    rw [hE]
    exact isMonomialSplitting_nil T.ideal
  exact nonMonomialPart_eq_of_isMonomialSplitting hG T hT ⊤ T.ideal h

theorem nonMonomialPart_eq_of_sameNontrivialBoundary (E' : List T.scheme.IdealSheafData) (hE : MarkedIdealWithBoundary.SameNontrivialBoundary T.boundary E')
    (hT' : (T.withBoundary E').IsAdmissible) :
    nonMonomialPart E' T.ideal = nonMonomialPart T.boundary T.ideal := by
  have h0 : IsMonomialSplitting E' T.ideal (monomialPart E' T.ideal)
      (nonMonomialPart E' T.ideal) :=
    hG.isMonomialSplitting_monomialPart_nonMonomialPart (T.withBoundary E') hT'
  have h1 : IsMonomialSplitting T.boundary T.ideal (monomialPart E' T.ideal)
      (nonMonomialPart E' T.ideal) :=
    (isMonomialSplitting_congr hE T.ideal (monomialPart E' T.ideal)
      (nonMonomialPart E' T.ideal)).mpr h0
  exact (nonMonomialPart_eq_of_isMonomialSplitting hG T hT _ _ h1).symm

theorem nonMonomialPart_comap_of_sameNontrivialBoundary (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [Smooth h] (hq : h ≫ T.structMap = q)
    (hT' : (T.pullbackAlong Y q h).IsAdmissible) (E' : List Y.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
    (hT'' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible) :
    nonMonomialPart E' (T.ideal.comap h) = (nonMonomialPart T.boundary T.ideal).comap h := by
  have h0 : IsMonomialSplitting T.boundary T.ideal (monomialPart T.boundary T.ideal)
      (nonMonomialPart T.boundary T.ideal) :=
    hG.isMonomialSplitting_monomialPart_nonMonomialPart T hT
  have h1 : IsMonomialSplitting (T.pullbackAlong Y q h).boundary (T.pullbackAlong Y q h).ideal
      ((monomialPart T.boundary T.ideal).comap h)
      ((nonMonomialPart T.boundary T.ideal).comap h) :=
    hG.splitting_smooth_pullback T hT Y q h hq hT'
      (monomialPart T.boundary T.ideal) (nonMonomialPart T.boundary T.ideal) h0
  have h2 : nonMonomialPart (T.pullbackAlong Y q h).boundary (T.pullbackAlong Y q h).ideal
      = (nonMonomialPart T.boundary T.ideal).comap h :=
    nonMonomialPart_eq_of_isMonomialSplitting hG (T.pullbackAlong Y q h) hT'
      ((monomialPart T.boundary T.ideal).comap h)
      ((nonMonomialPart T.boundary T.ideal).comap h) h1
  have h3 : nonMonomialPart E' (T.ideal.comap h)
      = nonMonomialPart (T.pullbackAlong Y q h).boundary (T.pullbackAlong Y q h).ideal :=
    nonMonomialPart_eq_of_sameNontrivialBoundary hG (T.pullbackAlong Y q h) hT' E' hE hT''
  exact h3.trans h2


end

end PrincipalizationGeometryHypotheses

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
section


section
namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenter

variable {X : Scheme.{u}}

private theorem foldr_mul_ofFn_eq_prod_consolidated415 {Z : Scheme.{u}} {n : ℕ} (f : Fin n → Z.IdealSheafData) :
    (List.ofFn f).foldr (· * ·) ⊤ = ∏ i, f i := by
  rw [← Scheme.IdealSheafData.one_eq_top]
  exact List.prod_ofFn

private theorem image_comap_eq_range_get_consolidated415 (E : List X.IdealSheafData) (U : X.Opens) :
    (fun D : X.IdealSheafData => D.comap U.ι) '' {D | D ∈ E} =
      Set.range (fun i : Fin E.length => (E.get i).comap U.ι) := by
  ext w
  constructor
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨i, hi, hEi⟩ := List.mem_iff_getElem.mp hD
    exact ⟨⟨i, hi⟩, by simp [hEi]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨E.get i, by simp, rfl⟩

section
variable (E : List X.IdealSheafData) (M : X.IdealSheafData) (x : ↥X)

private theorem isMonomialNear_iff_exists_pow_prod_consolidated415 :
    IsMonomialNear E M x ↔ ∃ U : X.Opens, x ∈ U ∧ ∃ a : Fin E.length → ℕ,
      M.comap U.ι =
        (List.ofFn (fun i : Fin E.length => (E.get i).comap U.ι ^ a i)).foldr (· * ·) ⊤ :=
  Iff.rfl

theorem isMonomialNear_iff_mem_closure :
    IsMonomialNear E M x ↔ ∃ U : X.Opens, x ∈ U ∧
      M.comap U.ι ∈
        Submonoid.closure ((fun D : X.IdealSheafData => D.comap U.ι) '' {D | D ∈ E}) := by
  rw [isMonomialNear_iff_exists_pow_prod_consolidated415]
  constructor
  · rintro ⟨U, hxU, a, ha⟩
    refine ⟨U, hxU, ?_⟩
    rw [image_comap_eq_range_get_consolidated415, ha, foldr_mul_ofFn_eq_prod_consolidated415, Submonoid.mem_closure_range_iff_of_fintype]
    exact ⟨a, rfl⟩
  · rintro ⟨U, hxU, hmem⟩
    rw [image_comap_eq_range_get_consolidated415, Submonoid.mem_closure_range_iff_of_fintype] at hmem
    obtain ⟨a, ha⟩ := hmem
    refine ⟨U, hxU, a, ?_⟩
    rw [foldr_mul_ofFn_eq_prod_consolidated415, ha]


end

section
variable {E E' : List X.IdealSheafData}

theorem IsMonomialNear.mono (h : ∀ D ∈ E, D ≠ ⊤ → D ∈ E') {M : X.IdealSheafData} {x : ↥X}
    (hM : IsMonomialNear E M x) :
    IsMonomialNear E' M x := by
  obtain ⟨U, hxU, hmem⟩ := (isMonomialNear_iff_mem_closure E M x).mp hM
  refine (isMonomialNear_iff_mem_closure E' M x).mpr ⟨U, hxU, ?_⟩
  refine Submonoid.closure_le.mpr ?_ hmem
  rintro w hw
  obtain ⟨D, hD, hDw⟩ := hw
  have hDw' : D.comap U.ι = w := hDw
  subst hDw'
  by_cases hDtop : D = ⊤
  · have hone : D.comap U.ι = 1 := by
      simp [hDtop, Scheme.IdealSheafData.one_eq_top]
    rw [hone]
    exact SetLike.mem_coe.mpr (one_mem _)
  · exact Submonoid.subset_closure ⟨D, h D hD hDtop, rfl⟩

theorem IsMonomialNear.congr_setOf (h : {D : X.IdealSheafData | D ∈ E ∧ D ≠ ⊤} = {D : X.IdealSheafData | D ∈ E' ∧ D ≠ ⊤})
    {M : X.IdealSheafData} {x : ↥X} (hM : IsMonomialNear E M x) :
    IsMonomialNear E' M x :=
  hM.mono fun D hD hne => (((Set.ext_iff.mp h) D).mp ⟨hD, hne⟩).1

theorem IsMonomialNear.congr_sameNontrivialBoundary (h : MarkedIdealWithBoundary.SameNontrivialBoundary E E') {M : X.IdealSheafData} {x : ↥X}
    (hM : IsMonomialNear E M x) :
    IsMonomialNear E' M x :=
  hM.congr_setOf h.setOf_mem_ne_top_eq


end

theorem isLocallyMonomialTriple_withBoundary (hG : MonomialGeometryHypotheses.{u})
    (T : MarkedIdealWithBoundary.{u}) (hT : IsLocallyMonomialTriple T)
    (E' : List T.scheme.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary T.boundary E') :
    IsLocallyMonomialTriple (T.withBoundary E') :=
  { valid := hG.withBoundary_valid T hT.valid E' hE
    monomialNear := fun x hx => (hT.monomialNear x hx).congr_sameNontrivialBoundary hE }

end MonomialCenter

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialInvariantDecrease
section


section
namespace FunctorialResolution.EmbeddedResolution

noncomputable abbrev blowupTripleAtCenterIdeal (T : MarkedIdealWithBoundary.{u}) : MarkedIdealWithBoundary.{u} :=
  @MarkedIdealWithBoundary.mk T.base T.instField
    (Blowup.blowup (monomialCenter T.ideal T.mult T.boundary))
    (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary) ≫ T.structMap)
    (residualByPow (T.ideal.comap (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary)))
      ((monomialCenter T.ideal T.mult T.boundary).comap
        (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) T.mult)
    T.mult
    (transformedBoundary (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))
      (monomialCenter T.ideal T.mult T.boundary) T.boundary)

private theorem foldr_mul_ofFn_eq_prod_consolidated441 {Y : Scheme.{u}} :
    ∀ {n : ℕ} (F : Fin n → Y.IdealSheafData),
      List.foldr (· * ·) (⊤ : Y.IdealSheafData) (List.ofFn F) = ∏ i, F i := by
  intro n
  induction n with
  | zero =>
      intro F
      simp only [List.ofFn_zero, List.foldr_nil, Finset.univ_eq_empty, Finset.prod_empty]
      exact Scheme.IdealSheafData.one_eq_top.symm
  | succ n ih =>
      intro F
      rw [List.ofFn_succ, List.foldr_cons, ih, Fin.prod_univ_succ]

private theorem comap_prod_consolidated441 {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∀ {n : ℕ} (F : Fin n → Y.IdealSheafData),
      (∏ i, F i).comap f = ∏ i, (F i).comap f := by
  intro n
  induction n with
  | zero =>
      intro F
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      rw [Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.comap_top]
      exact Scheme.IdealSheafData.one_eq_top.symm
  | succ n ih =>
      intro F
      rw [Fin.prod_univ_succ, Scheme.IdealSheafData.comap_mul, ih, Fin.prod_univ_succ]

private theorem prod_pow_comap_transformedBoundary_eq_consolidated441 {X X' : Scheme.{u}} (π : X' ⟶ X)
    (Z : X.IdealSheafData) (L : List X.IdealSheafData) (W : X'.Opens)
    (a : Fin L.length → ℕ) (d : ℕ) :
    (∏ i : Fin (transformedBoundary π Z L).length,
        (((transformedBoundary π Z L).get i).comap W.ι) ^
          (if hi : (i : ℕ) < L.length then a ⟨i, hi⟩ else d))
      = (∏ i : Fin L.length, ((Blowup.strictTransform π Z (L.get i)).comap W.ι) ^ a i)
          * ((Blowup.exceptionalIdeal π Z).comap W.ι) ^ d := by
  classical
  have hlen : (transformedBoundary π Z L).length = L.length + 1 := transformedBoundary_length π Z L
  have hg1 : ∀ j : Fin L.length,
      (transformedBoundary π Z L).get (Fin.cast hlen.symm (Fin.castSucc j))
        = Blowup.strictTransform π Z (L.get j) := by
    intro j
    simp [transformedBoundary, List.get_eq_getElem, j.isLt]
  have hg2 : (transformedBoundary π Z L).get (Fin.cast hlen.symm (Fin.last L.length))
      = Blowup.exceptionalIdeal π Z := by
    simp [transformedBoundary, List.get_eq_getElem]
  rw [Fintype.prod_equiv (finCongr hlen)
      (fun i : Fin (transformedBoundary π Z L).length =>
        (((transformedBoundary π Z L).get i).comap W.ι) ^
          (if hi : (i : ℕ) < L.length then a ⟨i, hi⟩ else d))
      (fun j : Fin (L.length + 1) =>
        (((transformedBoundary π Z L).get (Fin.cast hlen.symm j)).comap W.ι) ^
          (if hj : (j : ℕ) < L.length then a ⟨j, hj⟩ else d))
      (fun i => by simp)]
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl ?_
    intro j _
    rw [hg1 j]
    exact congrArg (fun t : ℕ => ((Blowup.strictTransform π Z (L.get j)).comap W.ι) ^ t) (dif_pos j.isLt)
  · rw [hg2, dif_neg (by simp : ¬ ((Fin.last L.length : Fin (L.length + 1)) : ℕ) < L.length)]

section
variable (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
include hGeom hT

private theorem isMonomialNear_transformedBoundary_of_isBlowupAlongIdealSheaf_consolidated441 {X' : Scheme.{u}} (π : X' ⟶ T.scheme) (Z : T.scheme.IdealSheafData)
    (hblow : Blowup.IsBlowupAlongIdealSheaf π Z)
    (hsm : Smooth (Z.subschemeι ≫ T.structMap))
    (hsnc : HasStrictNormalCrossingsWith T.structMap Z T.boundary)
    (hZco : (↑Z.support : Set ↥T.scheme) ⊆ orderAtLeastLocus T.ideal T.mult)
    (hZsupp : (↑Z.support : Set ↥T.scheme) = ⋃₀ centerComponents T.ideal T.mult T.boundary)
    (J : X'.IdealSheafData)
    (hJ : (Z.comap π) ^ T.mult * J = T.ideal.comap π)
    (x' : ↥X') (hx' : x' ∈ orderAtLeastLocus J T.mult) :
    MonomialCenter.IsMonomialNear (transformedBoundary π Z T.boundary) J x' := by
  classical
  have hmemcompl : ∀ y : ↥T.scheme, y ∈ (Z.support.compl : T.scheme.Opens) ↔ y ∉ Z.support :=
    fun y => Iff.rfl
  have hzc : π x' ∈ orderAtLeastLocus T.ideal T.mult := by
    by_cases hxe : x' ∈ (Z.comap π).support
    · exact hZco (by exact Scheme.IdealSheafData.mem_support_comap.1 hxe)
    · have h1 : (T.mult : ℕ∞) ≤ orderAt J x' := (mem_orderAtLeastLocus_iff _ _ _).1 hx'
      have h2 : orderAt J x' ≤ orderAt (T.ideal.comap π) x' := by
        have hmul := add_orderAt_le_orderAt_mul ((Z.comap π) ^ T.mult) J x'
        rw [hJ] at hmul
        exact le_trans le_add_self hmul
      have h3 : orderAt (T.ideal.comap π) x' = orderAt T.ideal (π x') := by
        refine hGeom.orderAt_comap_off_exceptional T hT.valid _ π Z hblow x' ?_ T.ideal
        rw [Blowup.exceptionalIdeal_eq_comap]
        exact hxe
      exact (mem_orderAtLeastLocus_iff _ _ _).2 (by rw [← h3]; exact le_trans h1 h2)
  obtain ⟨U, hzU, a, hmon⟩ := hT.monomialNear (π x') hzc
  have hbt : ∀ i : Fin T.boundary.length, ∃ (V : X'.Opens) (ε : ℕ),
      x' ∈ V ∧ (ε = 0 ∨ ε = 1) ∧
        (ε = 1 ↔ ∃ O : T.scheme.Opens, π x' ∈ O ∧
          (↑Z.support : Set ↥T.scheme) ∩ (↑O : Set ↥T.scheme) ⊆
            (↑(T.boundary.get i).support : Set ↥T.scheme)) ∧
        ((T.boundary.get i).comap π).comap V.ι =
          (Blowup.strictTransform π Z (T.boundary.get i)).comap V.ι *
            (Blowup.exceptionalIdeal π Z).comap V.ι ^ ε := by
    intro i
    exact hGeom.blowup_total_transform T hT.valid Z hsm hsnc
      _ π hblow (T.boundary.get i) (List.getElem_mem i.isLt) x'
  choose Vf ef hxV hef01 hefiff hefeq using hbt
  set e := ∑ i : Fin T.boundary.length, ef i * a i with hedef
  have hme : T.mult ≤ e := by
    by_cases hxe : x' ∈ (Z.comap π).support
    · have hzZ : π x' ∈ Z.support := Scheme.IdealSheafData.mem_support_comap.1 hxe
      obtain ⟨C, hC, hzC⟩ : ∃ C ∈ centerComponents T.ideal T.mult T.boundary, π x' ∈ C := by
        have hmem : π x' ∈ ⋃₀ centerComponents T.ideal T.mult T.boundary := by
          rw [← hZsupp]; exact hzZ
        exact hmem
      have hCc : C ∈ intersectionComponents T.boundary (lexMaxIndices T.ideal T.mult T.boundary) :=
        centerComponents_subset_intersectionComponents _ _ _ hC
      have hord : orderAlong T.ideal C
          = ((∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j : ℕ) : ℕ∞) :=
        orderAlong_eq_sum_of_monomial hGeom hT hCc hzC U hzU a hmon
      have hCmax : orderAlong T.ideal C = maxCandidateOrder T.ideal T.mult T.boundary :=
        ((mem_centerComponents_iff T.ideal T.mult T.boundary C).1 hC).2
      have hmax : (T.mult : ℕ∞) ≤ maxCandidateOrder T.ideal T.mult T.boundary := by
        have hne : minIndexCard T.ideal T.mult T.boundary ≠ 0 := by
          intro h0
          have hemp : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme) :=
            orderAtLeastLocus_eq_empty_of_minIndexCard_eq_zero hGeom hT h0
          have : π x' ∈ (∅ : Set ↥T.scheme) := by rw [← hemp]; exact hzc
          exact this.elim
        exact (maxCandidateOrder_spec hGeom hT hne).2.2.1
      have hsum : T.mult ≤ ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j := by
        have hcast : (T.mult : ℕ∞)
            ≤ ((∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j : ℕ) : ℕ∞) := by
          rw [← hord, hCmax]; exact hmax
        exact_mod_cast hcast
      have hef1 : ∀ j ∈ lexMaxIndices T.ideal T.mult T.boundary, ef j = 1 := by
        intro j hj
        refine (hefiff j).2 ⟨⊤, trivial, ?_⟩
        intro y hy
        have hy1 : y ∈ (↑Z.support : Set ↥T.scheme) := hy.1
        rw [hZsupp] at hy1
        obtain ⟨C', hC', hyC'⟩ := hy1
        exact (subset_support_iff_mem_of_mem_intersectionComponents hGeom hT
          (centerComponents_subset_intersectionComponents _ _ _ hC') j).2 hj hyC'
      calc T.mult ≤ ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j := hsum
        _ = ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, ef j * a j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [hef1 j hj, one_mul]
        _ ≤ e := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    · have hzZ : π x' ∉ Z.support := fun hc => hxe (Scheme.IdealSheafData.mem_support_comap.2 hc)
      have hef1 : ∀ i : Fin T.boundary.length, ef i = 1 := by
        intro i
        refine (hefiff i).2 ⟨Z.support.compl, (hmemcompl (π x')).2 hzZ, ?_⟩
        intro y hy
        have hy2 : y ∉ Z.support := (hmemcompl y).1 hy.2
        exact absurd hy.1 hy2
      have hordz : orderAt T.ideal (π x')
          = ((∑ j ∈ supportIndices T.boundary (π x'), a j : ℕ) : ℕ∞) :=
        orderAt_eq_sum_supportIndices hGeom hT (π x') U hzU a hmon
      have h1 : (T.mult : ℕ∞) ≤ orderAt T.ideal (π x') := (mem_orderAtLeastLocus_iff _ _ _).1 hzc
      have hsum : T.mult ≤ ∑ j ∈ supportIndices T.boundary (π x'), a j := by
        have hcast : (T.mult : ℕ∞)
            ≤ ((∑ j ∈ supportIndices T.boundary (π x'), a j : ℕ) : ℕ∞) := by
          rw [← hordz]; exact h1
        exact_mod_cast hcast
      calc T.mult ≤ ∑ j ∈ supportIndices T.boundary (π x'), a j := hsum
        _ ≤ ∑ j : Fin T.boundary.length, a j :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = e := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [hef1 j, one_mul]
  set W : X'.Opens :=
    ⟨(⋂ i : Fin T.boundary.length, ((Vf i : X'.Opens) : Set ↥X'))
        ∩ ((π ⁻¹ᵁ U : X'.Opens) : Set ↥X'),
      (isOpen_iInter_of_finite fun i => (Vf i).isOpen).inter (π ⁻¹ᵁ U).isOpen⟩ with hWdef
  have hxW : x' ∈ W := ⟨Set.mem_iInter.2 (fun i => hxV i), hzU⟩
  have hWU : W ≤ π ⁻¹ᵁ U := fun y hy => hy.2
  have hbi : ∀ i : Fin T.boundary.length,
      ((T.boundary.get i).comap π).comap W.ι =
        (Blowup.strictTransform π Z (T.boundary.get i)).comap W.ι
          * ((Z.comap π).comap W.ι) ^ ef i := by
    intro i
    have hle : W ≤ Vf i := fun y hy => Set.mem_iInter.1 hy.1 i
    have hcongr := congrArg (fun A => A.comap (X'.homOfLE hle)) (hefeq i)
    simpa [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow,
      ← restrictIdeal_eq_comap_homOfLE_restrictIdeal, Blowup.exceptionalIdeal_eq_comap] using hcongr
  have hcomp : ((X'.homOfLE hWU) ≫ (π ∣_ U)) ≫ U.ι = W.ι ≫ π := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have hg : ∀ A : T.scheme.IdealSheafData,
      (A.comap U.ι).comap ((X'.homOfLE hWU) ≫ (π ∣_ U)) = (A.comap π).comap W.ι := by
    intro A
    simp only [← Scheme.IdealSheafData.comap_comp]
    rw [hcomp]
  rw [foldr_mul_ofFn_eq_prod_consolidated441] at hmon
  have hmonW : (T.ideal.comap π).comap W.ι =
      ∏ i : Fin T.boundary.length, (((T.boundary.get i).comap π).comap W.ι) ^ a i := by
    calc (T.ideal.comap π).comap W.ι
        = (T.ideal.comap U.ι).comap ((X'.homOfLE hWU) ≫ (π ∣_ U)) := (hg _).symm
      _ = (∏ i : Fin T.boundary.length, ((T.boundary.get i).comap U.ι) ^ a i).comap
            ((X'.homOfLE hWU) ≫ (π ∣_ U)) := by rw [hmon]
      _ = ∏ i : Fin T.boundary.length,
            (((T.boundary.get i).comap U.ι) ^ a i).comap
              ((X'.homOfLE hWU) ≫ (π ∣_ U)) := comap_prod_consolidated441 _ _
      _ = ∏ i : Fin T.boundary.length, (((T.boundary.get i).comap π).comap W.ι) ^ a i := by
            refine Finset.prod_congr rfl ?_
            intro i _
            rw [Scheme.IdealSheafData.comap_pow, hg]
  have hprod : (T.ideal.comap π).comap W.ι =
      (∏ i : Fin T.boundary.length,
          ((Blowup.strictTransform π Z (T.boundary.get i)).comap W.ι) ^ a i)
        * ((Z.comap π).comap W.ι) ^ e := by
    rw [hmonW]
    have hterm : ∀ i : Fin T.boundary.length,
        (((T.boundary.get i).comap π).comap W.ι) ^ a i
          = ((Blowup.strictTransform π Z (T.boundary.get i)).comap W.ι) ^ a i
              * (((Z.comap π).comap W.ι) ^ (ef i * a i)) := by
      intro i
      rw [hbi i, mul_pow, ← pow_mul]
    rw [Finset.prod_congr rfl (fun i _ => hterm i), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor ((Z.comap π).comap W.ι) := by
    have h0 : Blowup.IsLocallyGeneratedByNonZeroDivisor (Z.comap π) := by
      have hc := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hblow
      rwa [Blowup.exceptionalIdeal_eq_comap] at hc
    exact h0.comap_of_isOpenImmersion W.ι
  have hcomapJ : ((Z.comap π).comap W.ι) ^ T.mult * J.comap W.ι
      = (T.ideal.comap π).comap W.ι := by
    rw [← Scheme.IdealSheafData.comap_pow, ← Scheme.IdealSheafData.comap_mul, hJ]
  have hrw : ((Z.comap π).comap W.ι) ^ T.mult *
      ((∏ i : Fin T.boundary.length,
          ((Blowup.strictTransform π Z (T.boundary.get i)).comap W.ι) ^ a i)
        * ((Z.comap π).comap W.ι) ^ (e - T.mult))
      = (∏ i : Fin T.boundary.length,
          ((Blowup.strictTransform π Z (T.boundary.get i)).comap W.ι) ^ a i)
        * ((Z.comap π).comap W.ι) ^ e := by
    rw [← mul_assoc, mul_comm (((Z.comap π).comap W.ι) ^ T.mult), mul_assoc, ← pow_add,
      Nat.add_sub_cancel' hme]
  have hfinal : J.comap W.ι =
      (∏ i : Fin T.boundary.length,
          ((Blowup.strictTransform π Z (T.boundary.get i)).comap W.ι) ^ a i)
        * ((Z.comap π).comap W.ι) ^ (e - T.mult) := by
    refine eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul hcart T.mult ?_
    rw [hcomapJ, hrw, hprod]
  refine ⟨W, hxW, fun i => if hi : (i : ℕ) < T.boundary.length then a ⟨i, hi⟩ else e - T.mult, ?_⟩
  rw [foldr_mul_ofFn_eq_prod_consolidated441,
    prod_pow_comap_transformedBoundary_eq_consolidated441 π Z T.boundary W a (e - T.mult), Blowup.exceptionalIdeal_eq_comap]
  exact hfinal

theorem isLocallyMonomialTriple_blowupTripleAtCenterIdeal (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    MonomialCenter.IsLocallyMonomialTriple (blowupTripleAtCenterIdeal T) := by
  refine ⟨?_, ?_⟩
  · have key := hGeom.level_valid T hT.valid
      (MarkedBlowupSequenceData.ofSingleBlowup T.structMap T.ideal T.mult T.boundary
        (monomialCenter T.ideal T.mult T.boundary)
        (smooth_monomialCenter hGeom hT h) (hasStrictNormalCrossingsWith_monomialCenter hGeom hT h)
        (support_monomialCenter_subset_orderAtLeastLocus hGeom hT h)
        (exists_controlledTransform_monomialCenter hGeom hT h)).toMarkedSequenceOfBlowups 1
      (by rw [MarkedBlowupSequenceData.toMarkedSequence_length]; exact Nat.le_refl 1)
    exact key
  · intro x' hx'
    refine isMonomialNear_transformedBoundary_of_isBlowupAlongIdealSheaf_consolidated441 hGeom hT
      (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))
      (monomialCenter T.ideal T.mult T.boundary)
      (Blowup.blowup.isBlowupAlongIdealSheaf_proj _)
      (smooth_monomialCenter hGeom hT h)
      (hasStrictNormalCrossingsWith_monomialCenter hGeom hT h)
      (support_monomialCenter_subset_orderAtLeastLocus hGeom hT h)
      (by
        rw [support_monomialCenter hGeom hT h, monomialCenterSet_eq_sUnion_centerComponents])
      (residualByPow (T.ideal.comap (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary)))
        ((monomialCenter T.ideal T.mult T.boundary).comap
          (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) T.mult)
      (pow_mul_residualByPow _ _ _ (exists_controlledTransform_monomialCenter hGeom hT h))
      x' hx'

private theorem krullDimSucc_schemeAt_one_le_dim_consolidated441 (d : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hlen : 1 ≤ d.length) :
    krullDimSucc (d.obj 1) ≤ T.krullDimSucc := by
  have key := hGeom.level_schemeDim_le T hT.valid d.toMarkedSequenceOfBlowups 1
    (by rw [MarkedBlowupSequenceData.toMarkedSequence_length]; exact hlen)
  rwa [MarkedBlowupSequenceData.toMarkedSequence_schemeAt] at key

theorem krullDimSucc_blowupTripleAtCenterIdeal_le (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    krullDimSucc (blowupTripleAtCenterIdeal T).scheme ≤ T.krullDimSucc :=
  krullDimSucc_schemeAt_one_le_dim_consolidated441 hGeom hT
    (MarkedBlowupSequenceData.ofSingleBlowup T.structMap T.ideal T.mult T.boundary
      (monomialCenter T.ideal T.mult T.boundary)
      (smooth_monomialCenter hGeom hT h) (hasStrictNormalCrossingsWith_monomialCenter hGeom hT h)
      (support_monomialCenter_subset_orderAtLeastLocus hGeom hT h)
      (exists_controlledTransform_monomialCenter hGeom hT h))
    (Nat.le_refl 1)

private theorem orderAt_controlledTransform_eq_of_notMem_support_consolidated441 {X' : Scheme.{u}} (π : X' ⟶ T.scheme)
    (Z : T.scheme.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (I' : X'.IdealSheafData)
    (hI' : (Z.comap π) ^ T.mult * I' = T.ideal.comap π) (x' : ↥X')
    (hx' : x' ∉ (Z.comap π).support) :
    orderAt I' x' = orderAt T.ideal (π x') := by
  have h1 : stalkIdeal (Z.comap π) x' = 1 := by
    rw [Ideal.one_eq_top]
    by_contra hc
    exact hx' ((mem_support_iff_stalkIdeal_ne_top _ _).2 hc)
  have h2 : stalkIdeal (T.ideal.comap π) x' = stalkIdeal I' x' := by
    rw [← hI', stalkIdeal_mul, stalkIdeal_pow, h1, one_pow, one_mul]
  have h3 : orderAt I' x' = orderAt (T.ideal.comap π) x' :=
    orderAt_eq_of_stalkIdeal_eq h2.symm
  rw [h3]
  exact hGeom.orderAt_comap_off_exceptional T hT.valid _ π Z hπ x'
    (by rw [Blowup.exceptionalIdeal_eq_comap]; exact hx') T.ideal


end

section
variable {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData) (L : List X.IdealSheafData)

private theorem get_transformedBoundary_strictTransformIndex_eq_strictTransform_consolidated441 (j : Fin L.length) :
    (transformedBoundary π Z L).get (strictTransformIndex π Z L j) = Blowup.strictTransform π Z (L.get j) := by
  simp [transformedBoundary, List.get_eq_getElem, strictTransformIndex_val, j.isLt]

private theorem get_transformedBoundary_exceptionalIndex_eq_comap_consolidated441 :
    (transformedBoundary π Z L).get (exceptionalIndex π Z L) = Z.comap π := by
  have hlen : (transformedBoundary π Z L).length = L.length + 1 :=
    transformedBoundary_length π Z L
  have hg2 : (transformedBoundary π Z L).get (Fin.cast hlen.symm (Fin.last L.length))
      = Blowup.exceptionalIdeal π Z := by
    simp [transformedBoundary, List.get_eq_getElem]
  have hfin : exceptionalIndex π Z L = Fin.cast hlen.symm (Fin.last L.length) := by
    apply Fin.val_injective
    simp [exceptionalIndex_val]
  rw [hfin, hg2, Blowup.exceptionalIdeal_eq_comap]

private theorem injective_strictTransformIndex_consolidated441 : Function.Injective (strictTransformIndex π Z L) := by
  intro i j hij
  apply Fin.val_injective
  have h := congrArg (fun z : Fin (transformedBoundary π Z L).length => (z : ℕ)) hij
  simpa [strictTransformIndex_val] using h

private theorem strictMono_strictTransformIndex_consolidated441 : StrictMono (strictTransformIndex π Z L) := by
  intro i j hij
  rw [Fin.lt_def, strictTransformIndex_val, strictTransformIndex_val]
  exact hij

private theorem sortedIndices_image_strictTransformIndex_consolidated441 (S : Finset (Fin L.length)) :
    MonomialCenter.sortedIndices (Finset.image (strictTransformIndex π Z L) S)
      = MonomialCenter.sortedIndices S := by
  rw [MonomialCenter.sortedIndices_image_of_strictMono (strictTransformIndex π Z L)
    (strictMono_strictTransformIndex_consolidated441 π Z L) S]
  simp only [strictTransformIndex_val]
  rfl

private theorem image_strictTransformIndex_preimageStrictTransformIndex_eq_erase_consolidated441 (J' : Finset (Fin (transformedBoundary π Z L).length)) :
    Finset.image (strictTransformIndex π Z L) (preimageStrictTransformIndex π Z L J') = J'.erase (exceptionalIndex π Z L) := by
  classical
  have hlen : (transformedBoundary π Z L).length = L.length + 1 :=
    transformedBoundary_length π Z L
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    refine Finset.mem_erase.2 ⟨?_, (mem_preimageStrictTransformIndex_iff π Z L J' j).1 hj⟩
    intro hc
    have h1 : ((strictTransformIndex π Z L j : Fin (transformedBoundary π Z L).length) : ℕ) = L.length := by
      rw [hc, exceptionalIndex_val]
    rw [strictTransformIndex_val] at h1
    exact absurd h1 (Nat.ne_of_lt j.isLt)
  · intro hi
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 hi
    have h1 : (i : ℕ) < (transformedBoundary π Z L).length := i.isLt
    have h2 : (i : ℕ) ≠ L.length := by
      intro hc
      exact hne (Fin.val_injective (by rw [hc, exceptionalIndex_val]))
    have hlt : (i : ℕ) < L.length := by omega
    have hid : strictTransformIndex π Z L ⟨(i : ℕ), hlt⟩ = i := Fin.val_injective (by rw [strictTransformIndex_val])
    refine Finset.mem_image.2 ⟨⟨(i : ℕ), hlt⟩, ?_, hid⟩
    exact (mem_preimageStrictTransformIndex_iff π Z L J' ⟨(i : ℕ), hlt⟩).2 (by rw [hid]; exact hmem)


end

section
variable (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
include hGeom hT

private theorem sum_lt_mult_of_card_lt_minIndexCard_consolidated441 {x : ↥T.scheme} {U : T.scheme.Opens}
    (hxU : x ∈ U) (a : Fin T.boundary.length → ℕ)
    (hmon : T.ideal.comap U.ι =
      (List.ofFn fun i : Fin T.boundary.length =>
        (T.boundary.get i).comap U.ι ^ a i).foldr (· * ·) ⊤)
    (S : Finset (Fin T.boundary.length)) (hS : ∀ j ∈ S, x ∈ (T.boundary.get j).support)
    (hcard : S.card < minIndexCard T.ideal T.mult T.boundary) :
    ∑ j ∈ S, a j < T.mult := by
  classical
  by_contra hc
  push Not at hc
  have hxsupp : x ∈ (↑(intersectionIdeal T.boundary S).support : Set ↥T.scheme) :=
    mem_support_intersectionIdeal T.boundary S x hS
  obtain ⟨C, hxC, hC⟩ := exists_mem_intersectionComponents_of_mem_support T.boundary S x hxsupp
  have hord : orderAlong T.ideal C = ((∑ j ∈ S, a j : ℕ) : ℕ∞) :=
    orderAlong_eq_sum_of_monomial hGeom hT hC hxC U hxU a hmon
  have hcand : IsCandidateComponent T.ideal T.mult T.boundary S.card S C :=
    ⟨rfl, hC, by rw [hord]; exact_mod_cast hc⟩
  have hone : 1 ≤ S.card := by
    rcases Nat.eq_zero_or_pos S.card with h0 | hp
    · exfalso
      have hS0 : S = ∅ := Finset.card_eq_zero.1 h0
      rw [hS0, Finset.sum_empty] at hc
      have hm1 : 1 ≤ T.mult := hT.valid.one_le_mult
      omega
    · exact hp
  have hle := (minIndexCard_spec T.ideal T.mult T.boundary ⟨S.card, hone, S, C, hcand⟩).2.2
    S.card hone S C hcand
  omega

private theorem exists_mem_intersectionComponents_orderAlong_eq_consolidated441 {X' : Scheme.{u}} (π : X' ⟶ T.scheme) (Z : T.scheme.IdealSheafData)
    (hZ : Z = componentUnionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)
      (centerComponents T.ideal T.mult T.boundary)
      (isOpen_preimage_sUnion_centerComponents hGeom hT))
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (I' : X'.IdealSheafData)
    (hI' : (Z.comap π) ^ T.mult * I' = T.ideal.comap π)
    (J' : Finset (Fin (transformedBoundary π Z T.boundary).length))
    (hnew : exceptionalIndex π Z T.boundary ∉ J') {C' : Set ↥X'}
    (hC' : C' ∈ intersectionComponents (transformedBoundary π Z T.boundary) J') :
    ∃ C : Set ↥T.scheme,
      C ∈ intersectionComponents T.boundary (preimageStrictTransformIndex π Z T.boundary J') ∧
        C ∉ centerComponents T.ideal T.mult T.boundary ∧
        orderAlong I' C' = orderAlong T.ideal C := by
  classical
  have himg := (image_strictTransformIndex_preimageStrictTransformIndex_eq_erase_consolidated441 π Z T.boundary J').trans
    (Finset.erase_eq_of_notMem hnew)
  subst hZ
  obtain ⟨hoff, C, hC, hCnot, -, hgen⟩ :=
    hGeom.transformed_components T hT.valid (lexMaxIndices T.ideal T.mult T.boundary)
      (centerComponents T.ideal T.mult T.boundary)
      (centerComponents_subset_intersectionComponents _ _ _)
      (isOpen_preimage_sUnion_centerComponents hGeom hT) X' π hπ
      (preimageStrictTransformIndex π _ T.boundary J') C' (by rw [himg]; exact hC')
      (isIrreducible_of_mem_intersectionComponents hC').genericPoint
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC')
  refine ⟨C, hC, hCnot, ?_⟩
  have hπgen : π (isIrreducible_of_mem_intersectionComponents hC').genericPoint
      = (isIrreducible_of_mem_intersectionComponents hC).genericPoint :=
    hgen _ (isGenericPoint_genericPoint_of_mem_intersectionComponents hC)
  rw [orderAlong_eq_orderAt_of_mem_intersectionComponents I' hC', orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC,
    ← hπgen]
  refine orderAt_controlledTransform_eq_of_notMem_support_consolidated441 hGeom hT π _ hπ I' hI' _ ?_
  rw [Blowup.exceptionalIdeal_eq_comap] at hoff
  exact hoff

private theorem minIndexCard_le_card_add_one_of_exceptionalIndex_mem_consolidated441 (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    {X' : Scheme.{u}} (π : X' ⟶ T.scheme) (q : X' ⟶ Spec (CommRingCat.of T.base))
    (hπ : Blowup.IsBlowupAlongIdealSheaf π (monomialCenter T.ideal T.mult T.boundary))
    (I' : X'.IdealSheafData)
    (hI' : ((monomialCenter T.ideal T.mult T.boundary).comap π) ^ T.mult * I' = T.ideal.comap π)
    (hT' : MonomialCenter.IsLocallyMonomialTriple (blowupTriple T π q I'))
    (J' : Finset (Fin (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
      T.boundary).length))
    (hnew : exceptionalIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary ∈ J')
    {C' : Set ↥X'}
    (hC' : C' ∈ intersectionComponents (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
      T.boundary) J')
    (hord : (T.mult : ℕ∞) ≤ orderAlong I' C') :
    minIndexCard T.ideal T.mult T.boundary
        ≤ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card + 1 ∧
      ((preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card
          < minIndexCard T.ideal T.mult T.boundary →
        orderAlong I' C' < maxCandidateOrder T.ideal T.mult T.boundary) := by
  classical
  have hgenericPtC : IsGenericPoint (isIrreducible_of_mem_intersectionComponents hC').genericPoint C' :=
    isGenericPoint_genericPoint_of_mem_intersectionComponents hC'
  have hξmem : (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈ C' := by
    have h0 : (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈
        closure ({(isIrreducible_of_mem_intersectionComponents hC').genericPoint} : Set ↥X') :=
      subset_closure rfl
    rwa [hgenericPtC] at h0
  have hdiv : ∀ i : Fin (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
      T.boundary).length, i ∈ J' →
      C' ⊆ (↑((transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
        T.boundary).get i).support : Set ↥X') := by
    intro i hi
    exact (hGeom.components_subset_divisor_iff (blowupTriple T π q I') hT'.valid J' C' hC' i).2 hi
  have hξE : (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈
      ((monomialCenter T.ideal T.mult T.boundary).comap π).support := by
    have h1 := hdiv _ hnew
    rw [get_transformedBoundary_exceptionalIndex_eq_comap_consolidated441] at h1
    exact h1 hξmem
  have hπξ : π (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈
      (monomialCenter T.ideal T.mult T.boundary).support :=
    Scheme.IdealSheafData.mem_support_comap.1 hξE
  have hπξset : π (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈
      (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) := hπξ
  rw [support_monomialCenter hGeom hT h, monomialCenterSet_eq_sUnion_centerComponents] at hπξset
  obtain ⟨C₀, hC₀opt, hmem₀⟩ := hπξset
  have hcoS : π (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈ orderAtLeastLocus T.ideal T.mult :=
    support_monomialCenter_subset_orderAtLeastLocus hGeom hT h hπξ
  obtain ⟨U, hU, a, hmon⟩ := hT.monomialNear _ hcoS
  have hkey := orderAlong_transform_add_mult_of_exceptionalIndex_mem hGeom hT h π q hπ I' hI' hT' hnew hC'
    U hU a hmon hC₀opt hmem₀
  have hC₀comp : C₀ ∈ intersectionComponents T.boundary (lexMaxIndices T.ideal T.mult T.boundary) :=
    centerComponents_subset_intersectionComponents _ _ _ hC₀opt
  have hordC₀ : orderAlong T.ideal C₀
      = ((∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j : ℕ) : ℕ∞) :=
    orderAlong_eq_sum_of_monomial hGeom hT hC₀comp hmem₀ U hU a hmon
  have hmaxC₀ : orderAlong T.ideal C₀ = maxCandidateOrder T.ideal T.mult T.boundary :=
    ((mem_centerComponents_iff _ _ _ C₀).1 hC₀opt).2
  rw [hordC₀] at hkey
  obtain ⟨S1, hS1⟩ : ∃ s : ℕ, s = ∑ i ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary)
      T.boundary J', a i := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ s : ℕ, s = ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j :=
    ⟨_, rfl⟩
  rw [← hS1, ← hS2] at hkey
  have hltop : orderAlong I' C' < ⊤ := by
    refine lt_of_le_of_lt ?_ (lt_of_le_of_ne (le_top : ((S1 : ℕ∞) + (S2 : ℕ∞)) ≤ ⊤) ?_)
    · rw [← hkey]
      exact le_self_add
    · intro hc
      have hcc : ((S1 + S2 : ℕ) : ℕ∞) = ⊤ := by rw [Nat.cast_add]; exact hc
      simp at hcc
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (ne_of_lt hltop)
  have hnm : n + T.mult = S1 + S2 := by
    have hc2 : ((n + T.mult : ℕ) : ℕ∞) = ((S1 + S2 : ℕ) : ℕ∞) := by
      rw [Nat.cast_add, Nat.cast_add, hn]
      exact hkey
    exact_mod_cast hc2
  have hmn : T.mult ≤ n := by
    have hc3 : ((T.mult : ℕ) : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := by rw [hn]; exact hord
    exact_mod_cast hc3
  by_cases hk : (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card
      < minIndexCard T.ideal T.mult T.boundary
  · have holdsub : ∀ j ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J',
        π (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈ (T.boundary.get j).support := by
      intro j hj
      have h1 := hdiv _ ((mem_preimageStrictTransformIndex_iff _ _ _ _ j).1 hj)
      rw [get_transformedBoundary_strictTransformIndex_eq_strictTransform_consolidated441] at h1
      have h2 : (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈
          (Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
            (T.boundary.get j)).support := h1 hξmem
      have h3 : (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈
          ((T.boundary.get j).comap π).support :=
        Scheme.IdealSheafData.support_antitone (comap_le_strictTransform π _ _) h2
      exact Scheme.IdealSheafData.mem_support_comap.1 h3
    have hp : S1 < T.mult := by
      rw [hS1]
      exact sum_lt_mult_of_card_lt_minIndexCard_consolidated441 hGeom hT hU a hmon _ holdsub hk
    have hcardch : (lexMaxIndices T.ideal T.mult T.boundary).card
        = minIndexCard T.ideal T.mult T.boundary := card_lexMaxIndices hGeom hT h
    have hchsub : ∀ j ∈ lexMaxIndices T.ideal T.mult T.boundary,
        π (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈ (T.boundary.get j).support := by
      intro j hj
      exact (subset_support_iff_mem_of_mem_intersectionComponents hGeom hT hC₀comp j).2 hj hmem₀
    obtain ⟨j₀, hj₀ch, hj₀old⟩ : ∃ j₀ ∈ lexMaxIndices T.ideal T.mult T.boundary,
        j₀ ∉ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J' := by
      by_contra hc
      push Not at hc
      have hsub : lexMaxIndices T.ideal T.mult T.boundary
          ⊆ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J' :=
        fun j hj => hc j hj
      have hcc := Finset.card_le_card hsub
      omega
    have herase : (∑ j ∈ (lexMaxIndices T.ideal T.mult T.boundary).erase j₀, a j) < T.mult := by
      refine sum_lt_mult_of_card_lt_minIndexCard_consolidated441 hGeom hT hU a hmon _
        (fun j hj => hchsub j (Finset.mem_of_mem_erase hj)) ?_
      have hce := Finset.card_erase_of_mem hj₀ch
      omega
    have hsplit : (∑ j ∈ (lexMaxIndices T.ideal T.mult T.boundary).erase j₀, a j) + a j₀ = S2 := by
      rw [hS2]
      exact Finset.sum_erase_add _ _ hj₀ch
    have hSge : T.mult ≤ ∑ j ∈ insert j₀ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary)
        T.boundary J'), a j := by
      rw [Finset.sum_insert hj₀old, ← hS1]
      omega
    have hmemsupp : π (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈
        (↑(intersectionIdeal T.boundary (insert j₀ (preimageStrictTransformIndex π
          (monomialCenter T.ideal T.mult T.boundary) T.boundary J'))).support : Set ↥T.scheme) := by
      refine mem_support_intersectionIdeal T.boundary _ _ ?_
      intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj2
      · exact hchsub _ hj₀ch
      · exact holdsub _ hj2
    obtain ⟨C, hxC, hCcomp⟩ :=
      exists_mem_intersectionComponents_of_mem_support T.boundary _ _ hmemsupp
    have hordC : orderAlong T.ideal C
        = ((∑ j ∈ insert j₀ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary)
            T.boundary J'), a j : ℕ) : ℕ∞) :=
      orderAlong_eq_sum_of_monomial hGeom hT hCcomp hxC U hU a hmon
    have hcand : IsCandidateComponent T.ideal T.mult T.boundary
        (insert j₀ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J')).card
        (insert j₀ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J')) C :=
      ⟨rfl, hCcomp, by rw [hordC]; exact_mod_cast hSge⟩
    have hone : 1 ≤ (insert j₀ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary)
        T.boundary J')).card := Finset.card_pos.2 ⟨j₀, Finset.mem_insert_self _ _⟩
    have hminle := (minIndexCard_spec T.ideal T.mult T.boundary ⟨_, hone, _, _, hcand⟩).2.2
      _ hone _ _ hcand
    have hcardS : (insert j₀ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary)
        T.boundary J')).card
        ≤ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card + 1 :=
      Finset.card_insert_le _ _
    refine ⟨by omega, fun _ => ?_⟩
    rw [← hn, ← hmaxC₀, hordC₀, ← hS2]
    have hlt : n < S2 := by omega
    exact_mod_cast hlt
  · exact ⟨by omega, fun hc => absurd hc hk⟩

private theorem minIndexCard_lt_or_maxCandidateOrder_lt_of_isBlowupAlongIdealSheaf_consolidated441 (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    {X' : Scheme.{u}} (π : X' ⟶ T.scheme) (q : X' ⟶ Spec (CommRingCat.of T.base))
    (hZp : monomialCenter T.ideal T.mult T.boundary =
      componentUnionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)
        (centerComponents T.ideal T.mult T.boundary)
        (isOpen_preimage_sUnion_centerComponents hGeom hT))
    (hπ : Blowup.IsBlowupAlongIdealSheaf π (monomialCenter T.ideal T.mult T.boundary))
    (I' : X'.IdealSheafData)
    (hI' : ((monomialCenter T.ideal T.mult T.boundary).comap π) ^ T.mult * I' = T.ideal.comap π)
    (hT' : MonomialCenter.IsLocallyMonomialTriple (blowupTriple T π q I'))
    (h' : minIndexCard I' T.mult
      (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) ≠ 0) :
    minIndexCard T.ideal T.mult T.boundary
        < minIndexCard I' T.mult
          (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) ∨
      (minIndexCard T.ideal T.mult T.boundary
          = minIndexCard I' T.mult
            (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) ∧
        (maxCandidateOrder I' T.mult
              (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
            < maxCandidateOrder T.ideal T.mult T.boundary ∨
          (maxCandidateOrder T.ideal T.mult T.boundary
              = maxCandidateOrder I' T.mult
                (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) ∧
            List.Lex (· < ·)
              (MonomialCenter.sortedIndices (lexMaxIndices T.ideal T.mult T.boundary))
              (MonomialCenter.sortedIndices
                (lexMaxIndices I' T.mult
                  (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
                    T.boundary)))))) := by
  classical
  have hA : ∀ (J' : Finset (Fin (transformedBoundary π
        (monomialCenter T.ideal T.mult T.boundary) T.boundary).length)) (C' : Set ↥X'),
      C' ∈ intersectionComponents (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
        T.boundary) J' →
      (T.mult : ℕ∞) ≤ orderAlong I' C' → 1 ≤ J'.card →
      minIndexCard T.ideal T.mult T.boundary ≤ J'.card := by
    intro J' C' hmem hordJ hone
    by_cases hnew : exceptionalIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary ∈ J'
    · have hx := minIndexCard_le_card_add_one_of_exceptionalIndex_mem_consolidated441 hGeom hT h π q hπ I' hI' hT' J' hnew hmem
        hordJ
      have hcarde := Finset.card_erase_of_mem hnew
      have himg := image_strictTransformIndex_preimageStrictTransformIndex_eq_erase_consolidated441 π (monomialCenter T.ideal T.mult T.boundary)
        T.boundary J'
      have hcimg : (Finset.image (strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
            (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J')).card
          = (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card :=
        Finset.card_image_of_injective _
          (injective_strictTransformIndex_consolidated441 π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
      rw [himg] at hcimg
      have h1 := hx.1
      omega
    · obtain ⟨C, hC, -, hordeq⟩ :=
        exists_mem_intersectionComponents_orderAlong_eq_consolidated441 hGeom hT π (monomialCenter T.ideal T.mult T.boundary)
          hZp hπ I' hI' J' hnew hmem
      have himg := (image_strictTransformIndex_preimageStrictTransformIndex_eq_erase_consolidated441 π (monomialCenter T.ideal T.mult T.boundary) T.boundary
        J').trans (Finset.erase_eq_of_notMem hnew)
      have hcimg : (Finset.image (strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
            (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J')).card
          = (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card :=
        Finset.card_image_of_injective _
          (injective_strictTransformIndex_consolidated441 π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
      rw [himg] at hcimg
      have hcand : IsCandidateComponent T.ideal T.mult T.boundary
          (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card
          (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J') C :=
        ⟨rfl, hC, by rw [← hordeq]; exact hordJ⟩
      have hone' : 1 ≤ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary)
          T.boundary J').card := by omega
      have hle := (minIndexCard_spec T.ideal T.mult T.boundary ⟨_, hone', _, _, hcand⟩).2.2
        _ hone' _ _ hcand
      omega
  obtain ⟨J₁, C₁, hcand₁⟩ := exists_isCandidateComponent_minIndexCard I' T.mult
    (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) h'
  have hsplit₁ : J₁.card = minIndexCard I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) ∧
      C₁ ∈ intersectionComponents (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
        T.boundary) J₁ ∧ (T.mult : ℕ∞) ≤ orderAlong I' C₁ := hcand₁
  obtain ⟨hcard₁, hmem₁, hord₁⟩ := hsplit₁
  have hone₁ : 1 ≤ J₁.card := by
    rw [hcard₁]
    exact Nat.pos_of_ne_zero h'
  have hAle : minIndexCard T.ideal T.mult T.boundary
      ≤ minIndexCard I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) := by
    rw [← hcard₁]
    exact hA J₁ C₁ hmem₁ hord₁ hone₁
  rcases lt_or_eq_of_le hAle with hlt | heq
  · exact Or.inl hlt
  refine Or.inr ⟨heq, ?_⟩
  have hbest' : ∃ C : Set ↥X',
      IsCandidateComponent I' T.mult
          (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
          (minIndexCard I' T.mult
            (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))
          (lexMaxIndices I' T.mult
            (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)) C ∧
        orderAlong I' C = maxCandidateOrder I' T.mult
          (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) :=
    (lexMaxIndices_spec hGeom hT' h').1
  obtain ⟨C', hcand', hordC'⟩ := hbest'
  have hsplit' : (lexMaxIndices I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)).card
        = minIndexCard I' T.mult
          (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) ∧
      C' ∈ intersectionComponents (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
        (lexMaxIndices I' T.mult
          (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)) ∧
      (T.mult : ℕ∞) ≤ orderAlong I' C' := hcand'
  obtain ⟨hcardc', hmemc', hordc'⟩ := hsplit'
  by_cases hnew : exceptionalIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary ∈
      lexMaxIndices I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
  · left
    have hx := minIndexCard_le_card_add_one_of_exceptionalIndex_mem_consolidated441 hGeom hT h π q hπ I' hI' hT' _ hnew hmemc'
      hordc'
    have hcarde := Finset.card_erase_of_mem hnew
    have himg := image_strictTransformIndex_preimageStrictTransformIndex_eq_erase_consolidated441 π (monomialCenter T.ideal T.mult T.boundary) T.boundary
      (lexMaxIndices I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))
    have hcimg : (Finset.image (strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
          (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
            (lexMaxIndices I' T.mult
              (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
                T.boundary)))).card
        = (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
            (lexMaxIndices I' T.mult
              (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
                T.boundary))).card :=
      Finset.card_image_of_injective _
        (injective_strictTransformIndex_consolidated441 π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
    rw [himg] at hcimg
    have hmin' : minIndexCard I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) ≠ 0 := h'
    have hpos : 1 ≤ (lexMaxIndices I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)).card := by
      rw [hcardc']
      exact Nat.pos_of_ne_zero hmin'
    have hlt2 : (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
        (lexMaxIndices I' T.mult
          (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))).card
        < minIndexCard T.ideal T.mult T.boundary := by omega
    rw [← hordC']
    exact hx.2 hlt2
  · obtain ⟨C, hC, hCnot, hordeq⟩ :=
      exists_mem_intersectionComponents_orderAlong_eq_consolidated441 hGeom hT π (monomialCenter T.ideal T.mult T.boundary)
        hZp hπ I' hI' _ hnew hmemc'
    have himgc := (image_strictTransformIndex_preimageStrictTransformIndex_eq_erase_consolidated441 π (monomialCenter T.ideal T.mult T.boundary) T.boundary
      (lexMaxIndices I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))).trans
      (Finset.erase_eq_of_notMem hnew)
    have hcimg : (Finset.image (strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
          (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
            (lexMaxIndices I' T.mult
              (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
                T.boundary)))).card
        = (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
            (lexMaxIndices I' T.mult
              (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
                T.boundary))).card :=
      Finset.card_image_of_injective _
        (injective_strictTransformIndex_consolidated441 π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
    rw [himgc] at hcimg
    have hcardJ : (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
        (lexMaxIndices I' T.mult
          (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))).card
        = minIndexCard T.ideal T.mult T.boundary := by
      rw [← hcimg, hcardc']
      exact heq.symm
    have hmC : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
      rw [← hordeq]
      exact hordc'
    have hcandJ : IsCandidateComponent T.ideal T.mult T.boundary
        (minIndexCard T.ideal T.mult T.boundary)
        (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
          (lexMaxIndices I' T.mult
            (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))) C :=
      ⟨hcardJ, hC, hmC⟩
    have hvle : maxCandidateOrder I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
        ≤ maxCandidateOrder T.ideal T.mult T.boundary := by
      rw [← hordC', hordeq]
      exact (maxCandidateOrder_spec hGeom hT h).2.1 _ _ hcandJ
    rcases lt_or_eq_of_le hvle with hv | hv
    · exact Or.inl hv
    refine Or.inr ⟨hv.symm, ?_⟩
    have hordC2 : orderAlong T.ideal C = maxCandidateOrder T.ideal T.mult T.boundary := by
      rw [← hordeq, hordC', hv]
    have hbestJ : IsMaxOrderIndexSet T.ideal T.mult T.boundary
        (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
          (lexMaxIndices I' T.mult
            (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))) :=
      ⟨C, hcandJ, hordC2⟩
    have hnotlex := (lexMaxIndices_spec hGeom hT h).2 _ hbestJ
    have hsp : MonomialCenter.sortedIndices (lexMaxIndices I' T.mult
          (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))
        = MonomialCenter.sortedIndices
          (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
            (lexMaxIndices I' T.mult
              (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))) := by
      conv_lhs => rw [← himgc]
      exact sortedIndices_image_strictTransformIndex_consolidated441 π (monomialCenter T.ideal T.mult T.boundary)
        T.boundary _
    rcases trichotomous_of (List.Lex (· < ·))
        (MonomialCenter.sortedIndices (lexMaxIndices T.ideal T.mult T.boundary))
        (MonomialCenter.sortedIndices
          (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
            (lexMaxIndices I' T.mult
              (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))))
      with hlex | hlexeq | hlex
    · rw [hsp]
      exact hlex
    · exfalso
      have hJeq : preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
            (lexMaxIndices I' T.mult
              (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))
          = lexMaxIndices T.ideal T.mult T.boundary := by
        ext j
        constructor
        · intro hj
          have h1 : (j : ℕ) ∈ MonomialCenter.sortedIndices
              (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
                (lexMaxIndices I' T.mult
                  (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
                    T.boundary))) := (MonomialCenter.mem_sortedIndices _ _).2 ⟨j, hj, rfl⟩
          rw [← hlexeq] at h1
          obtain ⟨j2, hj2, hvv⟩ := (MonomialCenter.mem_sortedIndices _ _).1 h1
          have hje : j2 = j := Fin.val_injective hvv
          rwa [hje] at hj2
        · intro hj
          have h1 : (j : ℕ) ∈ MonomialCenter.sortedIndices
              (lexMaxIndices T.ideal T.mult T.boundary) :=
            (MonomialCenter.mem_sortedIndices _ _).2 ⟨j, hj, rfl⟩
          rw [hlexeq] at h1
          obtain ⟨j2, hj2, hvv⟩ := (MonomialCenter.mem_sortedIndices _ _).1 h1
          have hje : j2 = j := Fin.val_injective hvv
          rwa [hje] at hj2
      apply hCnot
      refine (mem_centerComponents_iff _ _ _ C).2 ⟨⟨?_, ?_, ?_⟩, hordC2⟩
      · exact card_lexMaxIndices hGeom hT h
      · rw [← hJeq]
        exact hC
      · exact hmC
    · exact absurd hlex hnotlex

theorem minIndexCard_blowupTripleAtCenterIdeal_eq_zero_or_centerInvariant_lt (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    minIndexCard (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
        (blowupTripleAtCenterIdeal T).boundary = 0 ∨
      MonomialCenter.CenterInvariant.Lt (MonomialCenter.centerInvariant T.ideal T.mult T.boundary)
        (MonomialCenter.centerInvariant (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
          (blowupTripleAtCenterIdeal T).boundary) := by
  classical
  by_cases h' : minIndexCard (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
      (blowupTripleAtCenterIdeal T).boundary = 0
  · exact Or.inl h'
  refine Or.inr ?_
  have hT' : MonomialCenter.IsLocallyMonomialTriple
      (blowupTriple T (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))
        (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary) ≫ T.structMap)
        (residualByPow (T.ideal.comap (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary)))
          ((monomialCenter T.ideal T.mult T.boundary).comap
            (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) T.mult)) :=
    isLocallyMonomialTriple_blowupTripleAtCenterIdeal hGeom hT h
  have hI' : ((monomialCenter T.ideal T.mult T.boundary).comap
        (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) ^ T.mult *
      residualByPow (T.ideal.comap (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary)))
        ((monomialCenter T.ideal T.mult T.boundary).comap
          (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) T.mult
      = T.ideal.comap (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary)) :=
    pow_mul_residualByPow _ _ _ (exists_controlledTransform_monomialCenter hGeom hT h)
  exact minIndexCard_lt_or_maxCandidateOrder_lt_of_isBlowupAlongIdealSheaf_consolidated441 hGeom hT h
    (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))
    (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary) ≫ T.structMap)
    (monomialCenter_eq_componentUnionIdeal hGeom hT h) (Blowup.blowup.isBlowupAlongIdealSheaf_proj _) _ hI' hT' h'


end

noncomputable def numMaxOrderCandidates (T : MarkedIdealWithBoundary.{u}) : ℕ :=
  {p : Finset (Fin T.boundary.length) × Set ↥T.scheme |
      IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary) p.1 p.2 ∧
        orderAlong T.ideal p.2 = maxCandidateOrder T.ideal T.mult T.boundary}.ncard

noncomputable def monomialInvariant (D : ℕ) (T : MarkedIdealWithBoundary.{u}) :
    Lex (ℕ × Lex (ℕ × ℕ)) :=
  toLex (D - minIndexCard T.ideal T.mult T.boundary,
    toLex ((maxCandidateOrder T.ideal T.mult T.boundary).toNat, numMaxOrderCandidates T))

private theorem toNat_lt_toNat_of_lt_of_ne_top_consolidated441 {a b : ℕ∞} (hab : a < b) (hb : b ≠ ⊤) :
    a.toNat < b.toNat := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hb
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hab)
  subst hn
  subst hm
  have hmn : m < n := by exact_mod_cast hab
  simpa using hmn

private theorem monomialInvariant_lt_of_lex_lt_consolidated441 {D : ℕ} {T1 T2 : MarkedIdealWithBoundary.{u}}
    (hstep :
      D - minIndexCard T1.ideal T1.mult T1.boundary
          < D - minIndexCard T2.ideal T2.mult T2.boundary ∨
        (D - minIndexCard T1.ideal T1.mult T1.boundary
            = D - minIndexCard T2.ideal T2.mult T2.boundary ∧
          ((maxCandidateOrder T1.ideal T1.mult T1.boundary).toNat
              < (maxCandidateOrder T2.ideal T2.mult T2.boundary).toNat ∨
            ((maxCandidateOrder T1.ideal T1.mult T1.boundary).toNat
                = (maxCandidateOrder T2.ideal T2.mult T2.boundary).toNat ∧
              numMaxOrderCandidates T1 < numMaxOrderCandidates T2)))) :
    monomialInvariant D T1 < monomialInvariant D T2 := by
  have hgen : ∀ {a b c a' b' c' : ℕ},
      (a < a' ∨ (a = a' ∧ (b < b' ∨ (b = b' ∧ c < c')))) →
      (toLex (a, toLex (b, c)) : Lex (ℕ × Lex (ℕ × ℕ)))
        < toLex (a', toLex (b', c')) := by
    intro a b c a' b' c' hh
    rcases hh with h1 | ⟨rfl, h1⟩
    · exact Prod.Lex.left _ _ h1
    · refine Prod.Lex.right _ ?_
      rcases h1 with h2 | ⟨rfl, h2⟩
      · exact Prod.Lex.left _ _ h2
      · exact Prod.Lex.right _ h2
  exact hgen hstep

theorem monomialInvariant_blowupTripleAtCenterIdeal_lt (hGeom : MonomialGeometryHypotheses.{u}) {D : ℕ} {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    (hD : krullDimSucc T.scheme ≤ D)
    (h' : minIndexCard (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
      (blowupTripleAtCenterIdeal T).boundary ≠ 0) :
    monomialInvariant D (blowupTripleAtCenterIdeal T) < monomialInvariant D T := by
  classical
  have hTstep : MonomialCenter.IsLocallyMonomialTriple (blowupTripleAtCenterIdeal T) :=
    isLocallyMonomialTriple_blowupTripleAtCenterIdeal hGeom hT h
  have hkey0 := (minIndexCard_blowupTripleAtCenterIdeal_eq_zero_or_centerInvariant_lt hGeom hT h).resolve_left h'
  have hkeyU :
      minIndexCard T.ideal T.mult T.boundary
          < minIndexCard (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
              (blowupTripleAtCenterIdeal T).boundary ∨
        (minIndexCard T.ideal T.mult T.boundary
            = minIndexCard (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
                (blowupTripleAtCenterIdeal T).boundary ∧
          (maxCandidateOrder (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
                (blowupTripleAtCenterIdeal T).boundary
              < maxCandidateOrder T.ideal T.mult T.boundary ∨
            (maxCandidateOrder T.ideal T.mult T.boundary
                = maxCandidateOrder (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
                    (blowupTripleAtCenterIdeal T).boundary ∧
              List.Lex (· < ·)
                (MonomialCenter.sortedIndices (lexMaxIndices T.ideal T.mult T.boundary))
                (MonomialCenter.sortedIndices
                  (lexMaxIndices (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
                    (blowupTripleAtCenterIdeal T).boundary))))) := hkey0
  refine monomialInvariant_lt_of_lex_lt_consolidated441 ?_
  rcases hkeyU with hrank | ⟨hrank, hrest⟩
  · left
    obtain ⟨J, C, hcand⟩ :=
      exists_isCandidateComponent_minIndexCard (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
        (blowupTripleAtCenterIdeal T).boundary h'
    unfold IsCandidateComponent at hcand
    obtain ⟨hcard, hCmem, -⟩ := hcand
    have hlt : J.card < krullDimSucc (blowupTripleAtCenterIdeal T).scheme :=
      hGeom.card_lt_dim (blowupTripleAtCenterIdeal T) hTstep.valid J ⟨C, hCmem⟩
    have hdim : krullDimSucc (blowupTripleAtCenterIdeal T).scheme ≤ D :=
      le_trans (krullDimSucc_blowupTripleAtCenterIdeal_le hGeom hT h) hD
    omega
  · right
    refine ⟨by rw [hrank], ?_⟩
    rcases hrest with hval | ⟨hval, hpos⟩
    · left
      exact toNat_lt_toNat_of_lt_of_ne_top_consolidated441 hval (maxCandidateOrder_spec hGeom hT h).2.2.2.ne
    · right
      refine ⟨by rw [hval], ?_⟩
      exact maxOrderCandidatePairs_ncard_lt_of_blowup hGeom hT h
        (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))
        (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary) ≫ T.structMap)
        (Blowup.blowup.isBlowupAlongIdealSheaf_proj _)
        (residualByPow (T.ideal.comap (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary)))
          ((monomialCenter T.ideal T.mult T.boundary).comap
            (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) T.mult)
        (pow_mul_residualByPow _ _ _ (exists_controlledTransform_monomialCenter hGeom hT h))
        hTstep h' hrank.symm hval.symm

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCasePrincipalization
section


section
namespace FunctorialResolution.EmbeddedResolution

def tripleAtLastBlowup (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) : MarkedIdealWithBoundary.{u} :=
  @MarkedIdealWithBoundary.mk T.base T.instField (s.obj s.length)
    (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length)

@[simp]
theorem tripleAtLastBlowup_scheme (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    (tripleAtLastBlowup T s).scheme = s.obj s.length := rfl

noncomputable abbrev monomialIterateFromEmpty (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) (n : ℕ) :
    MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
  MarkedBlowupSequenceData.monomialBlowupIterate hinv
    (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) n

noncomputable abbrev monomialStallIndexOfTriple (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) : ℕ :=
  monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary

theorem minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (h : MarkedBlowupSequenceData.IsAdmissibleCenter s) :
    minIndexCard (tripleAtLastBlowup T s).ideal (tripleAtLastBlowup T s).mult
      (tripleAtLastBlowup T s).boundary ≠ 0 := by
  intro h0
  exact h.1 (monomialCenter_eq_top_of_minIndexCard_eq_zero (s.ideal s.length) T.mult
    (s.boundary s.length) h0)

theorem isAdmissibleCenter_of_minIndexCard_tripleAtLastBlowup_ne_zero (hGeom : MonomialGeometryHypotheses.{u})
    (T : MarkedIdealWithBoundary.{u}) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hs : MonomialCenter.IsLocallyMonomialTriple (tripleAtLastBlowup T s))
    (h : minIndexCard (tripleAtLastBlowup T s).ideal (tripleAtLastBlowup T s).mult
      (tripleAtLastBlowup T s).boundary ≠ 0) :
    MarkedBlowupSequenceData.IsAdmissibleCenter s :=
  monomialCenter_spec hGeom hs h

private theorem tripleAtLastBlowup_eq_mk_of_length_eq_consolidated455 (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (n : ℕ) (hn : s.length = n) :
    tripleAtLastBlowup T s =
      @MarkedIdealWithBoundary.mk T.base T.instField (s.obj n) (s.proj n ≫ T.structMap) (s.ideal n) T.mult
        (s.boundary n) := by
  subst hn
  rfl

section
variable {k : Type u}

private theorem markedIdealWithBoundary_mk_comap_eqToHom_consolidated455 [instk : Field k] {A B : Scheme.{u}}
    (hAB : A = B) (q : B ⟶ Spec (CommRingCat.of k)) (J : B.IdealSheafData) (m : ℕ)
    (E : List B.IdealSheafData) :
    @MarkedIdealWithBoundary.mk k instk A (eqToHom hAB ≫ q) (J.comap (eqToHom hAB)) m
        (List.map (fun D => D.comap (eqToHom hAB)) E) =
      @MarkedIdealWithBoundary.mk k instk B q J m E := by
  subst hAB
  refine MarkedIdealWithBoundary.mk_eq_mk _ _ ?_ ?_ ?_ <;> simp

private theorem blowupAtCenter_eq_self_of_not_isAdmissibleCenter_consolidated455 [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (h : ¬ MarkedBlowupSequenceData.IsAdmissibleCenter s) :
    MarkedBlowupSequenceData.blowupAtCenter hinv s = s := by
  unfold MarkedBlowupSequenceData.blowupAtCenter
  rw [dif_neg h]


end

section
variable (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
include hGeom

private theorem isLocallyMonomialTriple_tripleAtLastBlowup_blowupAtCenter_consolidated455
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hs : MonomialCenter.IsLocallyMonomialTriple (tripleAtLastBlowup T s)) :
    MonomialCenter.IsLocallyMonomialTriple
      (tripleAtLastBlowup T (MarkedBlowupSequenceData.blowupAtCenter hinv s)) := by
  by_cases hstep : MarkedBlowupSequenceData.IsAdmissibleCenter s
  · have hlen := MarkedBlowupSequenceData.blowupAtCenter_length hinv s hstep
    have hobj := MarkedBlowupSequenceData.blowupAtCenter_schemeAt_succ hinv s hstep
    have hideal := MarkedBlowupSequenceData.blowupAtCenter_ideal_succ hinv s hstep
    have hbdry := MarkedBlowupSequenceData.blowupAtCenter_boundary_succ hinv s hstep
    have hproj := MarkedBlowupSequenceData.blowupAtCenter_projectionToBase_succ hinv s hstep
    have hmin := minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter T s hstep
    have key : tripleAtLastBlowup T (MarkedBlowupSequenceData.blowupAtCenter hinv s) =
        blowupTripleAtCenterIdeal (tripleAtLastBlowup T s) := by
      rw [tripleAtLastBlowup_eq_mk_of_length_eq_consolidated455 T (MarkedBlowupSequenceData.blowupAtCenter hinv s) (s.length + 1)
          hlen, hproj, hideal, hbdry]
      simp only [Category.assoc]
      exact markedIdealWithBoundary_mk_comap_eqToHom_consolidated455 hobj _ _ _ _
    rw [key]
    exact isLocallyMonomialTriple_blowupTripleAtCenterIdeal hGeom hs hmin
  · rw [blowupAtCenter_eq_self_of_not_isAdmissibleCenter_consolidated455 hinv s hstep]
    exact hs

theorem isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate
    (hT : MonomialCenter.IsLocallyMonomialTriple T) (n : ℕ) :
    MonomialCenter.IsLocallyMonomialTriple (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)) := by
  induction n with
  | zero =>
    have h0 : monomialIterateFromEmpty hinv T 0 =
        emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
      MarkedBlowupSequenceData.monomialBlowupIterate_zero hinv _
    rw [h0]
    have hT0 : tripleAtLastBlowup T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) = T := by
      rw [tripleAtLastBlowup_eq_mk_of_length_eq_consolidated455 T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) 0
        (emptyMarkedBlowupSequenceData_length T.structMap T.ideal T.mult T.boundary)]
      exact MarkedIdealWithBoundary.mk_eq_mk T.scheme T.mult (Category.id_comp T.structMap)
        (emptyMarkedBlowupSequenceData_ideal T.structMap T.ideal T.mult T.boundary 0)
        (emptyMarkedBlowupSequenceData_boundary T.structMap T.ideal T.mult T.boundary 0)
    rw [hT0]
    exact hT
  | succ n ih =>
    have hstep : monomialIterateFromEmpty hinv T (n + 1) =
        MarkedBlowupSequenceData.blowupAtCenter hinv (monomialIterateFromEmpty hinv T n) :=
      MarkedBlowupSequenceData.monomialBlowupIterate_succ hinv _ n
    rw [hstep]
    exact isLocallyMonomialTriple_tripleAtLastBlowup_blowupAtCenter_consolidated455 hGeom hinv T
      (monomialIterateFromEmpty hinv T n) ih


end

section
variable (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})

theorem minIndexCard_monomialIterateFromEmpty_ne_zero (n : ℕ) (hn : n < monomialStallIndexOfTriple hinv T) :
    minIndexCard (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)).ideal
        (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)).mult
        (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)).boundary ≠ 0 :=
  minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter T (monomialIterateFromEmpty hinv T n)
    (isAdmissibleCenter_of_lt_monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary n hn)

private theorem tripleAtLastBlowup_blowupAtCenter_consolidated455 (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hstep : MarkedBlowupSequenceData.IsAdmissibleCenter s) :
    tripleAtLastBlowup T (MarkedBlowupSequenceData.blowupAtCenter hinv s) =
      blowupTripleAtCenterIdeal (tripleAtLastBlowup T s) := by
  have hlen := MarkedBlowupSequenceData.blowupAtCenter_length hinv s hstep
  have hobj := MarkedBlowupSequenceData.blowupAtCenter_schemeAt_succ hinv s hstep
  have hideal := MarkedBlowupSequenceData.blowupAtCenter_ideal_succ hinv s hstep
  have hbdry := MarkedBlowupSequenceData.blowupAtCenter_boundary_succ hinv s hstep
  have hproj := MarkedBlowupSequenceData.blowupAtCenter_projectionToBase_succ hinv s hstep
  simp only [tripleAtLastBlowup]
  rw [hlen, hideal, hbdry, hproj]
  simp only [Category.assoc]
  exact @markedIdealWithBoundary_mk_comap_eqToHom_consolidated455 T.base T.instField _ _ hobj _ _ _ _


end

section
variable (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) (hT : MonomialCenter.IsLocallyMonomialTriple T)
include hGeom hT

private theorem exists_isStationaryAt_emptyMarkedBlowupSequenceData_consolidated455 :
    ∃ n : ℕ, MarkedBlowupSequenceData.IsStationaryAt hinv
      (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) n := by
  by_contra hcon
  have hstepAll : ∀ n : ℕ, MarkedBlowupSequenceData.IsAdmissibleCenter (monomialIterateFromEmpty hinv T n) := by
    intro n
    by_contra hn
    exact hcon ⟨n, (MarkedBlowupSequenceData.isStationaryAt_iff_not_isAdmissibleCenter hinv
      (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) n).mpr hn⟩
  have hloc : ∀ n : ℕ, MonomialCenter.IsLocallyMonomialTriple
      (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)) :=
    fun n => isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT n
  have hmin : ∀ n : ℕ,
      minIndexCard (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)).ideal
        (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)).mult
        (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)).boundary ≠ 0 :=
    fun n => minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter T (monomialIterateFromEmpty hinv T n) (hstepAll n)
  have hmono : ∀ n : ℕ, tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (n + 1)) =
      blowupTripleAtCenterIdeal (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)) := by
    intro n
    have hit : monomialIterateFromEmpty hinv T (n + 1) =
        MarkedBlowupSequenceData.blowupAtCenter hinv (monomialIterateFromEmpty hinv T n) :=
      MarkedBlowupSequenceData.monomialBlowupIterate_succ hinv
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) n
    rw [hit]
    exact tripleAtLastBlowup_blowupAtCenter_consolidated455 hinv T (monomialIterateFromEmpty hinv T n) (hstepAll n)
  have hdim : ∀ n : ℕ,
      krullDimSucc (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)).scheme ≤ T.krullDimSucc := by
    intro n
    induction n with
    | zero =>
      have h0 : monomialIterateFromEmpty hinv T 0 = emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
        MarkedBlowupSequenceData.monomialBlowupIterate_zero hinv
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
      have hsc : (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T 0)).scheme = T.scheme := by
        rw [tripleAtLastBlowup_scheme, h0, emptyMarkedBlowupSequenceData_schemeAt]
      exact le_of_eq (congrArg krullDimSucc hsc)
    | succ n ih =>
      rw [hmono n]
      exact le_trans (krullDimSucc_blowupTripleAtCenterIdeal_le hGeom (hloc n) (hmin n)) ih
  have hdec : ∀ n : ℕ,
      monomialInvariant T.krullDimSucc (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (n + 1))) <
        monomialInvariant T.krullDimSucc (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)) := by
    intro n
    have h' : minIndexCard (blowupTripleAtCenterIdeal (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n))).ideal
        (blowupTripleAtCenterIdeal (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n))).mult
        (blowupTripleAtCenterIdeal (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n))).boundary ≠ 0 := by
      rw [← hmono n]
      exact hmin (n + 1)
    rw [hmono n]
    exact monomialInvariant_blowupTripleAtCenterIdeal_lt hGeom (hloc n) (hmin n) (hdim n) h'
  have main : ∀ a : Lex (ℕ × Lex (ℕ × ℕ)), Acc (· < ·) a → ∀ n : ℕ,
      monomialInvariant T.krullDimSucc (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T n)) = a → False := by
    intro a ha
    induction ha with
    | intro x hx ih =>
      intro n hn
      refine ih (monomialInvariant T.krullDimSucc
        (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (n + 1)))) ?_ (n + 1) rfl
      rw [← hn]
      exact hdec n
  exact main (monomialInvariant T.krullDimSucc (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T 0)))
    (wellFounded_lt.apply _) 0 rfl

theorem minIndexCard_monomialIterateFromEmpty_stallIndex_eq_zero :
    minIndexCard (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (monomialStallIndexOfTriple hinv T))).ideal
        (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (monomialStallIndexOfTriple hinv T))).mult
        (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (monomialStallIndexOfTriple hinv T))).boundary = 0 := by
  by_contra hne
  have hstall := isStationaryAt_monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary
    (exists_isStationaryAt_emptyMarkedBlowupSequenceData_consolidated455 hGeom hinv T hT)
  have hnot := (MarkedBlowupSequenceData.isStationaryAt_iff_not_isAdmissibleCenter hinv
    (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (monomialStallIndexOfTriple hinv T)).mp hstall
  exact hnot (isAdmissibleCenter_of_minIndexCard_tripleAtLastBlowup_ne_zero hGeom T
    (monomialIterateFromEmpty hinv T (monomialStallIndexOfTriple hinv T))
    (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT
      (monomialStallIndexOfTriple hinv T)) hne)


end

section
variable (hinv : ComapIsoInvariance.{u})

theorem monomialPrincipalization_length (T : MarkedIdealWithBoundary.{u}) :
    (monomialPrincipalization hinv T).length = monomialStallIndexOfTriple hinv T := by
  rw [monomialPrincipalization_apply, MarkedBlowupSequenceData.toMarkedSequence_length, monomialBlowupSeq_length]

theorem monomialPrincipalization_length_eq_zero_of_empty :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      orderAtLeastLocus T.ideal T.mult = ∅ → (monomialPrincipalization hinv T).length = 0 := by
  intro T hT hcs
  have hmin : minIndexCard T.ideal T.mult T.boundary = 0 :=
    minIndexCard_eq_zero_of_orderAtLeastLocus_eq_empty hT.valid hcs
  have hT0 : tripleAtLastBlowup T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) = T := by
    rw [tripleAtLastBlowup_eq_mk_of_length_eq_consolidated455 T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) 0
      (emptyMarkedBlowupSequenceData_length T.structMap T.ideal T.mult T.boundary)]
    exact MarkedIdealWithBoundary.mk_eq_mk T.scheme T.mult (Category.id_comp T.structMap)
      (emptyMarkedBlowupSequenceData_ideal T.structMap T.ideal T.mult T.boundary 0)
      (emptyMarkedBlowupSequenceData_boundary T.structMap T.ideal T.mult T.boundary 0)
  have hns : ¬ MarkedBlowupSequenceData.IsAdmissibleCenter
      (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) := by
    intro hstep
    have h := minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter T
      (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hstep
    rw [hT0] at h
    exact h hmin
  have hzero : MarkedBlowupSequenceData.monomialStallIndex hinv
      (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) = 0 :=
    MarkedBlowupSequenceData.monomialStallIndex_eq_zero_of_not_isAdmissibleCenter hinv
      (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hns
  rw [monomialPrincipalization_length]
  exact (monomialStallIndex_eq_monomialStallIndex_empty hinv T.structMap T.ideal T.mult T.boundary).trans hzero


end

theorem monomialPrincipalization_isResolution (hGeom : MonomialGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      MarkedSequenceOfBlowups.IsResolution (monomialPrincipalization hinv T) := by
  intro T hT
  have hmon : MonomialCenter.IsLocallyMonomialTriple
      (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (monomialStallIndexOfTriple hinv T))) :=
    isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT (monomialStallIndexOfTriple hinv T)
  have hzero := minIndexCard_monomialIterateFromEmpty_stallIndex_eq_zero hGeom hinv T hT
  have hcs := orderAtLeastLocus_eq_empty_of_minIndexCard_eq_zero hGeom hmon hzero
  refine (MarkedSequenceOfBlowups.isResolution_iff _).mpr ?_
  rw [monomialPrincipalization_apply, MarkedBlowupSequenceData.toMarkedSequence_lastIdeal]
  exact hcs

private theorem support_comap_eqToHom_nonempty_consolidated455 {A B : Scheme.{u}} (h : A = B)
    (J : B.IdealSheafData) (hJ : (J.support : Set ↥B).Nonempty) :
    ((J.comap (eqToHom h)).support : Set ↥A).Nonempty := by
  subst h
  obtain ⟨x, hx⟩ := hJ
  exact ⟨x, Scheme.IdealSheafData.mem_support_comap.mpr (by simpa using hx)⟩

section
variable (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
include hGeom

theorem monomialPrincipalization_center_support_nonempty :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (monomialPrincipalization hinv T).length,
        (((monomialPrincipalization hinv T).center i).support :
          Set ↥((monomialPrincipalization hinv T).schemeAt i)).Nonempty := by
  intro T hT i hi
  rw [monomialPrincipalization_length] at hi
  have hlen : i < monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary := hi
  have hs := isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT i
  have hmin := minIndexCard_monomialIterateFromEmpty_ne_zero hinv T i hlen
  have hne : ((monomialCenter (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T i)).ideal
      (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T i)).mult
      (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T i)).boundary).support :
      Set ↥(tripleAtLastBlowup T (monomialIterateFromEmpty hinv T i)).scheme).Nonempty := by
    rw [support_monomialCenter hGeom hs hmin]
    exact monomialCenterSet_nonempty hGeom hs hmin
  have hsupp : ((MarkedBlowupSequenceData.centerAtLast (monomialIterateFromEmpty hinv T i)).support :
      Set ↥((monomialIterateFromEmpty hinv T i).obj (monomialIterateFromEmpty hinv T i).length)).Nonempty := hne
  rw [monomialPrincipalization_apply, MarkedBlowupSequenceData.toMarkedSequence_center,
    monomialBlowupSeq_center hinv T.structMap T.ideal T.mult T.boundary i hlen]
  exact support_comap_eqToHom_nonempty_consolidated455
    (monomialBlowupSeq_schemeAt hinv T.structMap T.ideal T.mult T.boundary i (Nat.le_of_lt hlen))
    (MarkedBlowupSequenceData.centerAtLast (monomialIterateFromEmpty hinv T i)) hsupp

private theorem support_centerAtLast_subset_iUnion_boundary_consolidated455 (T : MarkedIdealWithBoundary.{u})
    (hT : MonomialCenter.IsLocallyMonomialTriple T) (i : ℕ) (hi : i < monomialStallIndexOfTriple hinv T) :
    ((MarkedBlowupSequenceData.centerAtLast (monomialIterateFromEmpty hinv T i)).support :
        Set ↥((monomialIterateFromEmpty hinv T i).obj (monomialIterateFromEmpty hinv T i).length)) ⊆
      ⋃ D ∈ (monomialIterateFromEmpty hinv T i).boundary (monomialIterateFromEmpty hinv T i).length,
        ((D.support : Set ↥((monomialIterateFromEmpty hinv T i).obj (monomialIterateFromEmpty hinv T i).length))) :=
  support_monomialCenter_subset_boundary hGeom
    (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT i)
    (minIndexCard_monomialIterateFromEmpty_ne_zero hinv T i hi)

theorem monomialPrincipalization_center_subset_boundaryLocus :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (monomialPrincipalization hinv T).length,
        ↑((monomialPrincipalization hinv T).center i).support ⊆
          MarkedSequenceOfBlowups.boundaryLocus (monomialPrincipalization hinv T) i := by
  intro T hT i hi
  have hiN : i < monomialStallIndexOfTriple hinv T := by
    rwa [monomialPrincipalization_length] at hi
  have hcent := monomialBlowupSeq_center hinv T.structMap T.ideal T.mult T.boundary i hiN
  have hbd := monomialBlowupSeq_boundary hinv T.structMap T.ideal T.mult T.boundary i (Nat.le_of_lt hiN)
  rw [monomialPrincipalization_apply]
  intro x hx
  rw [MarkedBlowupSequenceData.toMarkedSequence_center, hcent] at hx
  refine (MarkedSequenceOfBlowups.mem_boundaryLocus_iff _ _ _).mpr ?_
  rw [MarkedBlowupSequenceData.toMarkedSequence_boundary, hbd]
  obtain ⟨D, hD, hxD⟩ :=
    Set.mem_iUnion₂.mp
      (support_centerAtLast_subset_iUnion_boundary_consolidated455 hGeom hinv T hT i hiN
        (Scheme.IdealSheafData.mem_support_comap.mp hx))
  exact ⟨_, List.mem_map.mpr ⟨D, hD, rfl⟩, Scheme.IdealSheafData.mem_support_comap.mpr hxD⟩


end

private theorem centerAtLast_eq_monomialCenter_consolidated455 {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (d : MarkedBlowupSequenceData p I m E) :
    MarkedBlowupSequenceData.centerAtLast d =
      monomialCenter (d.ideal d.length) m (d.boundary d.length) := rfl

private theorem monomialCenter_comap_eqToHom_consolidated455 {X Y : Scheme.{u}} (h : X = Y)
    (J : Y.IdealSheafData) (m : ℕ) (E : List Y.IdealSheafData) :
    monomialCenter (J.comap (eqToHom h)) m (List.map (fun D => D.comap (eqToHom h)) E) =
      (monomialCenter J m E).comap (eqToHom h) := by
  subst h
  simp

theorem monomialPrincipalization_center_eq_monomialCenter (_hGeom : MonomialGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (monomialPrincipalization hinv T).length,
        (monomialPrincipalization hinv T).center i =
          monomialCenter ((monomialPrincipalization hinv T).ideal i) T.mult
            ((monomialPrincipalization hinv T).boundary i) := by
  intro T _ i hi
  rw [monomialPrincipalization_length hinv T] at hi
  have hi' : i < monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary := hi
  have hle : i ≤ monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary := le_of_lt hi'
  have hobj := monomialBlowupSeq_schemeAt hinv T.structMap T.ideal T.mult T.boundary i hle
  rw [monomialPrincipalization_apply, MarkedBlowupSequenceData.toMarkedSequence_center,
    MarkedBlowupSequenceData.toMarkedSequence_ideal, MarkedBlowupSequenceData.toMarkedSequence_boundary,
    monomialBlowupSeq_center hinv T.structMap T.ideal T.mult T.boundary i hi',
    monomialBlowupSeq_ideal hinv T.structMap T.ideal T.mult T.boundary i hle,
    monomialBlowupSeq_boundary hinv T.structMap T.ideal T.mult T.boundary i hle,
    centerAtLast_eq_monomialCenter_consolidated455]
  exact (monomialCenter_comap_eqToHom_consolidated455 hobj _ T.mult _).symm

private theorem minIndexCard_comap_eqToHom_consolidated455 {A B : Scheme.{u}} (h : A = B)
    (J : B.IdealSheafData) (m : ℕ) (E : List B.IdealSheafData) :
    minIndexCard (J.comap (eqToHom h)) m (List.map (fun D => D.comap (eqToHom h)) E) =
      minIndexCard J m E := by
  subst h
  simp

theorem monomialPrincipalization_minIndexCard_ne_zero (_hGeom : MonomialGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (monomialPrincipalization hinv T).length,
        minIndexCard ((monomialPrincipalization hinv T).ideal i) T.mult
          ((monomialPrincipalization hinv T).boundary i) ≠ 0 := by
  intro T _ i hi
  rw [monomialPrincipalization_length] at hi
  have hlt : i < monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary := hi
  have hle : i ≤ monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary := Nat.le_of_lt hlt
  have hmin : minIndexCard
      ((MarkedBlowupSequenceData.monomialBlowupIterate hinv
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) i).ideal
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) i).length) T.mult
      ((MarkedBlowupSequenceData.monomialBlowupIterate hinv
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) i).boundary
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) i).length) ≠ 0 :=
    minIndexCard_monomialIterateFromEmpty_ne_zero hinv T i hlt
  have hEq := minIndexCard_comap_eqToHom_consolidated455
      (monomialBlowupSeq_schemeAt hinv T.structMap T.ideal T.mult T.boundary i hle)
      ((MarkedBlowupSequenceData.monomialBlowupIterate hinv
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) i).ideal
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) i).length) T.mult
      ((MarkedBlowupSequenceData.monomialBlowupIterate hinv
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) i).boundary
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) i).length)
  rw [monomialPrincipalization_apply, MarkedBlowupSequenceData.toMarkedSequence_ideal,
    MarkedBlowupSequenceData.toMarkedSequence_boundary,
    monomialBlowupSeq_ideal hinv T.structMap T.ideal T.mult T.boundary i hle,
    monomialBlowupSeq_boundary hinv T.structMap T.ideal T.mult T.boundary i hle]
  intro h0
  exact hmin (hEq.symm.trans h0)

private theorem isMonomialNear_comap_eqToHom_consolidated455 {X Y : Scheme.{u}} (h : X = Y)
    (J : Y.IdealSheafData) (F : List Y.IdealSheafData) (m : ℕ)
    (hmon : ∀ y ∈ orderAtLeastLocus J m, MonomialCenter.IsMonomialNear F J y)
    (x : ↥X) (hx : x ∈ orderAtLeastLocus (J.comap (eqToHom h)) m) :
    MonomialCenter.IsMonomialNear (List.map (fun D => D.comap (eqToHom h)) F)
      (J.comap (eqToHom h)) x := by
  subst h
  have hx' : x ∈ orderAtLeastLocus J m := by simpa using hx
  simpa using hmon x hx'

section
variable (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
include hGeom

theorem monomialPrincipalization_isMonomialNear :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i ≤ (monomialPrincipalization hinv T).length,
        ∀ x ∈ orderAtLeastLocus ((monomialPrincipalization hinv T).ideal i) T.mult,
          MonomialCenter.IsMonomialNear ((monomialPrincipalization hinv T).boundary i)
            ((monomialPrincipalization hinv T).ideal i) x := by
  intro T hT i hi
  have hiN : i ≤ monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary := by
    rwa [monomialPrincipalization_length] at hi
  have hid := monomialBlowupSeq_ideal hinv T.structMap T.ideal T.mult T.boundary i hiN
  have hbd := monomialBlowupSeq_boundary hinv T.structMap T.ideal T.mult T.boundary i hiN
  have hmon : ∀ y ∈ orderAtLeastLocus ((monomialIterateFromEmpty hinv T i).ideal
        (monomialIterateFromEmpty hinv T i).length) T.mult,
      MonomialCenter.IsMonomialNear
        ((monomialIterateFromEmpty hinv T i).boundary (monomialIterateFromEmpty hinv T i).length)
        ((monomialIterateFromEmpty hinv T i).ideal (monomialIterateFromEmpty hinv T i).length) y :=
    (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT i).monomialNear
  rw [monomialPrincipalization_apply]
  intro x hx
  rw [MarkedBlowupSequenceData.toMarkedSequence_ideal, hid] at hx
  rw [MarkedBlowupSequenceData.toMarkedSequence_ideal, MarkedBlowupSequenceData.toMarkedSequence_boundary, hid, hbd]
  exact isMonomialNear_comap_eqToHom_consolidated455 _ _ _ T.mult hmon x hx

theorem monomialPrincipalization_principalizationCertificate :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (monomialPrincipalization hinv T).length,
        PrincipalizationCertificate ((monomialPrincipalization hinv T).schemeAt i)
          (MarkedSequenceOfBlowups.projectionToSpec (monomialPrincipalization hinv T) i)
          ((monomialPrincipalization hinv T).ideal i) T.mult
          (MarkedSequenceOfBlowups.boundaryLocus (monomialPrincipalization hinv T) i)
          ((monomialPrincipalization hinv T).center i) := by
  intro T hT i hi
  exact PrincipalizationCertificate.memory
    (monomialPrincipalization_center_subset_boundaryLocus hGeom hinv T hT i hi)


end

private theorem centerInvariant_le_of_lt_consolidated455 {n n' : ℕ} {a : MonomialCenter.CenterInvariant n} {b : MonomialCenter.CenterInvariant n'}
    (h : MonomialCenter.CenterInvariant.Lt a b) : MonomialCenter.CenterInvariant.Le a b := by
  unfold MonomialCenter.CenterInvariant.Le
  exact Or.inl h

section
variable {A : Scheme.{u}} (h : A = A)

private theorem comap_eqToHom_refl_consolidated455 (D : A.IdealSheafData) : D.comap (eqToHom h) = D := by
  rw [eqToHom_refl]
  simp

private theorem map_comap_eqToHom_refl_consolidated455 (E : List A.IdealSheafData) :
    List.map (fun D => D.comap (eqToHom h)) E = E := by
  induction E with
  | nil => rfl
  | cons _ _ _ => simp


end

private theorem centerInvariant_le_comap_eqToHom_consolidated455 {A B A' B' : Scheme.{u}} (h : A = B) (h' : A' = B')
    (m : ℕ) (J : B.IdealSheafData) (E : List B.IdealSheafData)
    (J' : B'.IdealSheafData) (E' : List B'.IdealSheafData)
    (hle : MonomialCenter.CenterInvariant.Le (MonomialCenter.centerInvariant J m E) (MonomialCenter.centerInvariant J' m E')) :
    MonomialCenter.CenterInvariant.Le
      (MonomialCenter.centerInvariant (J.comap (eqToHom h)) m (List.map (fun D => D.comap (eqToHom h)) E))
      (MonomialCenter.centerInvariant (J'.comap (eqToHom h')) m
        (List.map (fun D => D.comap (eqToHom h')) E')) := by
  subst h
  subst h'
  rw [map_comap_eqToHom_refl_consolidated455 rfl E, map_comap_eqToHom_refl_consolidated455 rfl E',
    comap_eqToHom_refl_consolidated455 rfl J, comap_eqToHom_refl_consolidated455 rfl J']
  exact hle

theorem monomialPrincipalization_centerInvariant_le_succ (hGeom : MonomialGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ t : ℕ, t + 1 < (monomialPrincipalization hinv T).length →
        (MonomialCenter.centerInvariant ((monomialPrincipalization hinv T).ideal t) T.mult
            ((monomialPrincipalization hinv T).boundary t)).Le
          (MonomialCenter.centerInvariant ((monomialPrincipalization hinv T).ideal (t + 1)) T.mult
            ((monomialPrincipalization hinv T).boundary (t + 1))) := by
  intro T hT t ht
  rw [monomialPrincipalization_length hinv T] at ht
  have ht1 : t + 1 < monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary := ht
  have ht0 : t < monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary :=
    Nat.lt_of_succ_lt ht1
  have hstep : MarkedBlowupSequenceData.IsAdmissibleCenter (monomialIterateFromEmpty hinv T t) :=
    isAdmissibleCenter_of_lt_monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary t ht0
  have hiter : monomialIterateFromEmpty hinv T (t + 1) =
      MarkedBlowupSequenceData.blowupAtCenter hinv (monomialIterateFromEmpty hinv T t) :=
    MarkedBlowupSequenceData.monomialBlowupIterate_succ hinv
      (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) t
  have hlastEq : tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (t + 1)) =
      blowupTripleAtCenterIdeal (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T t)) := by
    rw [hiter]
    exact tripleAtLastBlowup_blowupAtCenter_consolidated455 hinv T (monomialIterateFromEmpty hinv T t) hstep
  have hloc := isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT t
  have hmin := minIndexCard_monomialIterateFromEmpty_ne_zero hinv T t ht0
  have hmin1 := minIndexCard_monomialIterateFromEmpty_ne_zero hinv T (t + 1) ht1
  have hdich := minIndexCard_blowupTripleAtCenterIdeal_eq_zero_or_centerInvariant_lt hGeom hloc hmin
  rw [← hlastEq] at hdich
  have hlt : MonomialCenter.CenterInvariant.Lt
      (MonomialCenter.centerInvariant (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T t)).ideal T.mult
        (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T t)).boundary)
      (MonomialCenter.centerInvariant (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (t + 1))).ideal T.mult
        (tripleAtLastBlowup T (monomialIterateFromEmpty hinv T (t + 1))).boundary) := by
    rcases hdich with h | h
    · exact absurd h hmin1
    · exact h
  have hle := centerInvariant_le_of_lt_consolidated455 hlt
  rw [monomialPrincipalization_apply,
    MarkedBlowupSequenceData.toMarkedSequence_ideal, MarkedBlowupSequenceData.toMarkedSequence_ideal,
    MarkedBlowupSequenceData.toMarkedSequence_boundary, MarkedBlowupSequenceData.toMarkedSequence_boundary,
    monomialBlowupSeq_ideal hinv T.structMap T.ideal T.mult T.boundary t (Nat.le_of_lt ht0),
    monomialBlowupSeq_ideal hinv T.structMap T.ideal T.mult T.boundary (t + 1) (Nat.le_of_lt ht1),
    monomialBlowupSeq_boundary hinv T.structMap T.ideal T.mult T.boundary t (Nat.le_of_lt ht0),
    monomialBlowupSeq_boundary hinv T.structMap T.ideal T.mult T.boundary (t + 1) (Nat.le_of_lt ht1)]
  exact centerInvariant_le_comap_eqToHom_consolidated455 _ _ T.mult _ _ _ _ hle

structure IsMonomialCasePrincipalization (F : PrincipalizationAssignment.{u}) : Prop where
  center_subset_boundaryLocus :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (F T).length,
        ↑((F T).center i).support ⊆ MarkedSequenceOfBlowups.boundaryLocus (F T) i
  cert :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (F T).length,
        PrincipalizationCertificate ((F T).schemeAt i) (MarkedSequenceOfBlowups.projectionToSpec (F T) i) ((F T).ideal i) T.mult
          (MarkedSequenceOfBlowups.boundaryLocus (F T) i) ((F T).center i)
  center_eq :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (F T).length,
        (F T).center i = monomialCenter ((F T).ideal i) T.mult ((F T).boundary i)
  minLevel_ne_zero :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (F T).length, minIndexCard ((F T).ideal i) T.mult ((F T).boundary i) ≠ 0
  key_le :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ t : ℕ, t + 1 < (F T).length →
        (MonomialCenter.centerInvariant ((F T).ideal t) T.mult ((F T).boundary t)).Le
          (MonomialCenter.centerInvariant ((F T).ideal (t + 1)) T.mult ((F T).boundary (t + 1)))
  monomial_near :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i ≤ (F T).length,
        ∀ x ∈ orderAtLeastLocus ((F T).ideal i) T.mult,
          MonomialCenter.IsMonomialNear ((F T).boundary i) ((F T).ideal i) x
  center_nonempty :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i < (F T).length, (((F T).center i).support : Set ↥((F T).schemeAt i)).Nonempty
  resolves :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      MarkedSequenceOfBlowups.IsResolution (F T)
  trivial_of_coSupport_empty :
    ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      orderAtLeastLocus T.ideal T.mult = ∅ → (F T).length = 0

theorem isMonomialCasePrincipalization_monomialPrincipalization (hGeom : MonomialGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) : IsMonomialCasePrincipalization (monomialPrincipalization hinv) :=
  { center_subset_boundaryLocus :=
      monomialPrincipalization_center_subset_boundaryLocus hGeom hinv
    cert := monomialPrincipalization_principalizationCertificate hGeom hinv
    center_eq := monomialPrincipalization_center_eq_monomialCenter hGeom hinv
    minLevel_ne_zero := monomialPrincipalization_minIndexCard_ne_zero hGeom hinv
    key_le := monomialPrincipalization_centerInvariant_le_succ hGeom hinv
    monomial_near := monomialPrincipalization_isMonomialNear hGeom hinv
    center_nonempty := monomialPrincipalization_center_support_nonempty hGeom hinv
    resolves := monomialPrincipalization_isResolution hGeom hinv
    trivial_of_coSupport_empty := monomialPrincipalization_length_eq_zero_of_empty hinv }

end FunctorialResolution.EmbeddedResolution

end
end
end
