import Mathlib
import Core5.M08SmoothCoordinateTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicGeometry
universe u
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IrreducibleComponentsOfSupport
section

open Opposite TopologicalSpace

section

private theorem isPreirreducible_of_isPreirreducible_image_val_consolidated238 {α : Type u} [TopologicalSpace α] {s : Set α}
    {T : Set s} (h : IsPreirreducible (Subtype.val '' T)) : IsPreirreducible T := by
  intro u v hu hv hTu hTv
  obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.mp hv
  obtain ⟨a, haT, hau⟩ := hTu
  obtain ⟨b, hbT, hbv⟩ := hTv
  obtain ⟨w, ⟨t, htT, rfl⟩, hwu, hwv⟩ :=
    h u' v' hu' hv' ⟨(a : α), ⟨a, haT, rfl⟩, hau⟩ ⟨(b : α), ⟨b, hbT, rfl⟩, hbv⟩
  exact ⟨t, htT, hwu, hwv⟩

section
variable {X : Scheme.{u}}

private theorem exists_fromSpec_mem_and_primeIdealOf_eq_consolidated238 {V : X.Opens} (hV : IsAffineOpen V)
    (P : PrimeSpectrum Γ(X, V)) :
    ∃ hz : hV.fromSpec.base P ∈ V, hV.primeIdealOf ⟨hV.fromSpec.base P, hz⟩ = P := by
  have hz : hV.fromSpec.base P ∈ V := by
    have h : hV.fromSpec.base P ∈ Set.range hV.fromSpec.base := ⟨P, rfl⟩
    rwa [hV.range_fromSpec] at h
  refine ⟨hz, hV.fromSpec.isOpenEmbedding.injective ?_⟩
  rw [hV.fromSpec_primeIdealOf]

private theorem mem_support_iff_ideal_le_primeIdealOf_consolidated238 (I : X.IdealSheafData)
    {V : X.Opens} (hV : IsAffineOpen V) {x : ↥X} (hx : x ∈ V) :
    x ∈ I.support ↔ I.ideal ⟨V, hV⟩ ≤ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let _ : Algebra ↑Γ(X, V) ↑(X.presheaf.stalk x) :=
    RingHom.toAlgebra (X.presheaf.germ V x hx).hom
  have : IsLocalization.AtPrime ↑(X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hx⟩
  have hcomap : Ideal.comap (X.presheaf.germ V x hx).hom
      (IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
      = (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
    have h := IsLocalization.AtPrime.under_maximalIdeal (R := ↑Γ(X, V))
      (S := ↑(X.presheaf.stalk x)) (I := (hV.primeIdealOf ⟨x, hx⟩).asIdeal)
    exact h
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_eq_map_germ I x ⟨V, hV⟩ hx,
    Ideal.map_le_iff_le_comap]
  exact iff_of_eq (congrArg (fun J => I.ideal ⟨V, hV⟩ ≤ J) hcomap)

private theorem vanishingIdeal_ideal_le_primeIdealOf_consolidated238 (Z : Closeds ↥X)
    {V : X.Opens} (hV : IsAffineOpen V) {x : ↥X} (hx : x ∈ V) (hxZ : x ∈ (Z : Set ↥X)) :
    (Scheme.IdealSheafData.vanishingIdeal Z).ideal ⟨V, hV⟩
      ≤ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have heq : (Scheme.IdealSheafData.vanishingIdeal Z).ideal ⟨V, hV⟩
      = PrimeSpectrum.vanishingIdeal (hV.fromSpec.base ⁻¹' (Z : Set ↥X)) := rfl
  intro f hf
  rw [heq, PrimeSpectrum.mem_vanishingIdeal] at hf
  refine hf (hV.primeIdealOf ⟨x, hx⟩) ?_
  have : hV.fromSpec.base (hV.primeIdealOf ⟨x, hx⟩) = x := hV.fromSpec_primeIdealOf ⟨x, hx⟩
  show hV.fromSpec.base (hV.primeIdealOf ⟨x, hx⟩) ∈ (Z : Set ↥X)
  rw [this]
  exact hxZ

private theorem le_vanishingIdeal_of_subset_support_consolidated238 (I : X.IdealSheafData)
    (Z : Closeds ↥X) (h : (Z : Set ↥X) ⊆ (I.support : Set ↥X)) :
    I ≤ Scheme.IdealSheafData.vanishingIdeal Z := by
  have key : ∀ U : X.affineOpens,
      I.ideal U ≤ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U := by
    intro U f hf
    have heq : (Scheme.IdealSheafData.vanishingIdeal Z).ideal U
        = PrimeSpectrum.vanishingIdeal (U.2.fromSpec.base ⁻¹' (Z : Set ↥X)) := rfl
    rw [heq, PrimeSpectrum.mem_vanishingIdeal]
    intro P hP
    obtain ⟨hz, hzP⟩ := exists_fromSpec_mem_and_primeIdealOf_eq_consolidated238 U.2 P
    have hzs : U.2.fromSpec.base P ∈ I.support := h hP
    rw [mem_support_iff_ideal_le_primeIdealOf_consolidated238 I U.2 hz, hzP] at hzs
    exact hzs hf
  exact key


end

structure IsIrreducibleComponentOfSupport {X : Scheme.{u}} (D : X.IdealSheafData) (C : Set X) : Prop where
  isIrreducible : IsIrreducible C
  maximal : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (D.support : Set X) → C' = C
  subset_support : C ⊆ (D.support : Set X)

namespace IsIrreducibleComponentOfSupport

variable {X : Scheme.{u}} {D : X.IdealSheafData} {C : Set X}

section
variable (hC : IsIrreducibleComponentOfSupport D C)
include hC

theorem isClosed : IsClosed C :=
  isClosed_of_maximal_irreducible_subset_support D hC.isIrreducible hC.subset_support hC.maximal

theorem closure_genericPoint :
    closure {hC.isIrreducible.genericPoint} = C :=
  hC.isIrreducible.isGenericPoint_genericPoint hC.isClosed

theorem genericPoint_mem :
    hC.isIrreducible.genericPoint ∈ C := by
  have h : hC.isIrreducible.genericPoint ∈ closure {hC.isIrreducible.genericPoint} :=
    subset_closure (Set.mem_singleton _)
  rwa [hC.closure_genericPoint] at h

theorem genericPoint_specializes {x : X} (hx : x ∈ C) :
    hC.isIrreducible.genericPoint ⤳ x := by
  refine specializes_iff_mem_closure.mpr ?_
  rw [hC.closure_genericPoint]
  exact hx

theorem genericPoint_mem_support :
    hC.isIrreducible.genericPoint ∈ (D.support : Set X) :=
  hC.subset_support hC.genericPoint_mem


end

end IsIrreducibleComponentOfSupport

section
variable {X : Scheme.{u}}

theorem exists_isIrreducibleComponentOfSupport (D : X.IdealSheafData) (x : X)
    (hx : x ∈ (D.support : Set X)) :
    ∃ C : Set X, IsIrreducibleComponentOfSupport D C ∧ x ∈ C := by
  have hchain : ∀ c ⊆ {t : Set X | IsIrreducible t ∧ t ⊆ (D.support : Set X)},
      IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ {t : Set X | IsIrreducible t ∧ t ⊆ (D.support : Set X)}, ∀ s ∈ c, s ⊆ ub := by
    intro c hcS hch hne
    refine ⟨⋃₀ c, ⟨⟨?_, ?_⟩, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · obtain ⟨t, ht⟩ := hne
      obtain ⟨y, hy⟩ := (hcS ht).1.nonempty
      exact ⟨y, t, ht, hy⟩
    · rintro u v hu hv ⟨y, ⟨q, hq, hyq⟩, hyu⟩ ⟨z, ⟨r, hr, hzr⟩, hzv⟩
      rcases hch.total hq hr with h | h
      · obtain ⟨w, hw, hwuv⟩ := (hcS hr).1.2 u v hu hv ⟨y, h hyq, hyu⟩ ⟨z, hzr, hzv⟩
        exact ⟨w, ⟨r, hr, hw⟩, hwuv⟩
      · obtain ⟨w, hw, hwuv⟩ := (hcS hq).1.2 u v hu hv ⟨y, hyq, hyu⟩ ⟨z, h hzr, hzv⟩
        exact ⟨w, ⟨q, hq, hw⟩, hwuv⟩
    · exact Set.sUnion_subset fun t ht => (hcS ht).2
  obtain ⟨m, hxm, hm⟩ := zorn_subset_nonempty
    {t : Set X | IsIrreducible t ∧ t ⊆ (D.support : Set X)} hchain {x}
    ⟨isIrreducible_singleton, Set.singleton_subset_iff.mpr hx⟩
  exact ⟨m, ⟨hm.1.1, fun C' hC' hmC' hC'S =>
    Set.Subset.antisymm (hm.2 ⟨hC', hC'S⟩ hmC') hmC', hm.1.2⟩, hxm rfl⟩

theorem finite_isIrreducibleComponentOfSupport [TopologicalSpace.NoetherianSpace ↥X]
    (D : X.IdealSheafData) :
    {C : Set X | IsIrreducibleComponentOfSupport D C}.Finite := by
  have hfin : (irreducibleComponents ↥((D.support : Set X))).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have himg : ∀ C ∈ {C : Set X | IsIrreducibleComponentOfSupport D C},
      (Subtype.val ⁻¹' C : Set ↥((D.support : Set X))) ∈
        irreducibleComponents ↥((D.support : Set X)) := by
    intro C hC
    have hCsub : C ⊆ (D.support : Set X) := hC.subset_support
    have himgC :
        (Subtype.val '' (Subtype.val ⁻¹' C : Set ↥((D.support : Set X))) : Set ↥X) = C :=
      Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hCsub)
    have hirr : IsIrreducible (Subtype.val ⁻¹' C : Set ↥((D.support : Set X))) := by
      obtain ⟨y, hy⟩ := hC.isIrreducible.nonempty
      refine ⟨⟨⟨y, hCsub hy⟩, hy⟩, ?_⟩
      apply isPreirreducible_of_isPreirreducible_image_val_consolidated238
      rw [himgC]
      exact hC.isIrreducible.2
    refine ⟨hirr, ?_⟩
    intro T' hT' hle
    have h1 : IsIrreducible (Subtype.val '' T' : Set ↥X) :=
      hT'.image _ continuous_subtype_val.continuousOn
    have h2 : (Subtype.val '' T' : Set ↥X) ⊆ (D.support : Set X) := by
      rintro _ ⟨t, _, rfl⟩
      exact t.2
    have h3 : C ⊆ (Subtype.val '' T' : Set ↥X) := by
      rw [← himgC]
      exact Set.image_mono hle
    have h4 := hC.maximal _ h1 h3 h2
    intro t ht
    have hmem : (t : ↥X) ∈ C := by rw [← h4]; exact ⟨t, ht, rfl⟩
    exact hmem
  have hsub : (fun C : Set X => (Subtype.val ⁻¹' C : Set ↥((D.support : Set X)))) ''
      {C : Set X | IsIrreducibleComponentOfSupport D C} ⊆ irreducibleComponents ↥((D.support : Set X)) := by
    rintro _ ⟨C, hC, rfl⟩
    exact himg C hC
  have hinj : Set.InjOn (fun C : Set X => (Subtype.val ⁻¹' C : Set ↥((D.support : Set X))))
      {C : Set X | IsIrreducibleComponentOfSupport D C} := by
    intro C1 h1 C2 h2 heq
    have e1 :
        (Subtype.val '' (Subtype.val ⁻¹' C1 : Set ↥((D.support : Set X))) : Set ↥X) = C1 :=
      Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact h1.subset_support)
    have e2 :
        (Subtype.val '' (Subtype.val ⁻¹' C2 : Set ↥((D.support : Set X))) : Set ↥X) = C2 :=
      Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact h2.subset_support)
    rw [← e1, ← e2]
    exact congrArg (Set.image Subtype.val) heq
  exact Set.Finite.of_finite_image (hfin.subset hsub) hinj

theorem stalkIdeal_ne_bot_of_nonzeroOnComponents (I : X.IdealSheafData)
    (hI : NonzeroOnComponents I) (x : X) : stalkIdeal I x ≠ ⊥ := by
  intro hbot
  rw [nonzeroOnComponents_iff] at hI
  refine hI (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x) ?_
  have hTirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hTcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
  have hgen : closure {hTirr.genericPoint} = irreducibleComponent x :=
    hTirr.isGenericPoint_genericPoint hTcl
  have hspec : hTirr.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, hgen]
    exact mem_irreducibleComponent
  obtain ⟨V, hxV⟩ := Scheme.exists_affineOpens_mem x
  have hetaV : hTirr.genericPoint ∈ (V : X.Opens) := hspec.mem_open (V : X.Opens).isOpen hxV
  have hmapeq : CommRingCat.Hom.hom (X.presheaf.germ (V : X.Opens) hTirr.genericPoint hetaV)
      = (CommRingCat.Hom.hom (X.presheaf.stalkSpecializes hspec)).comp
        (CommRingCat.Hom.hom (X.presheaf.germ (V : X.Opens) x hxV)) := by
    rw [← CommRingCat.hom_comp, TopCat.Presheaf.germ_stalkSpecializes]
  have hetabot : stalkIdeal I hTirr.genericPoint = ⊥ := by
    rw [stalkIdeal_eq_map_germ I hTirr.genericPoint V hetaV, hmapeq, ← Ideal.map_map,
      ← stalkIdeal_eq_map_germ I x V hxV, hbot, Ideal.map_bot]
  have hbt : (⊥ : Ideal ↑(X.presheaf.stalk hTirr.genericPoint)) ≠ ⊤ := by
    intro h
    have h1 : (1 : ↑(X.presheaf.stalk hTirr.genericPoint)) ∈
        (⊥ : Ideal ↑(X.presheaf.stalk hTirr.genericPoint)) := by
      rw [h]; exact Submodule.mem_top
    rw [Ideal.mem_bot] at h1
    exact one_ne_zero h1
  have hmem : hTirr.genericPoint ∈ I.support :=
    (mem_support_iff_stalkIdeal_ne_top I _).mpr (by rw [hetabot]; exact hbt)
  calc irreducibleComponent x = closure {hTirr.genericPoint} := hgen.symm
    _ ⊆ closure ((I.support : Set ↥X)) :=
        closure_mono (Set.singleton_subset_iff.mpr hmem)
    _ = (I.support : Set ↥X) := I.support.isClosed.closure_eq

theorem orderAt_ne_top_of_nonzeroOnComponents [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I) (x : X) : orderAt I x ≠ ⊤ :=
  orderAt_ne_top_of_stalkIdeal_ne_bot I x (stalkIdeal_ne_bot_of_nonzeroOnComponents I hI x)

private theorem vanishingIdeal_ideal_eq_of_restrictIdeal_eq_coordIdeal_consolidated238 {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (D : X.IdealSheafData) {C : Set ↥X} (hCcl : IsClosed C)
    (hCsub : C ⊆ (D.support : Set ↥X))
    {W : X.Opens} (hW : IsAffineOpen W) {n : ℕ} (c : EtaleChart p W n) (S : Finset (Fin n))
    (hD : restrictIdeal D W = c.coordIdeal S)
    (hWC : ∀ y : ↥X, y ∈ W → y ∈ (D.support : Set ↥X) → y ∈ C) :
    (Scheme.IdealSheafData.vanishingIdeal (⟨C, hCcl⟩ : Closeds ↥X)).ideal ⟨W, hW⟩
      = D.ideal ⟨W, hW⟩ := by
  refine le_antisymm ?_ ?_
  · have hrad : (D.ideal ⟨W, hW⟩).IsRadical :=
      isRadical_ideal_of_restrictIdeal_eq_coordIdeal p hW c D S hD
    have hJ : D.ideal ⟨W, hW⟩ = sInf {P : Ideal Γ(X, W) | D.ideal ⟨W, hW⟩ ≤ P ∧ P.IsPrime} := by
      rw [← Ideal.radical_eq_sInf, hrad.radical]
    rw [hJ]
    refine le_sInf ?_
    rintro P ⟨hPle, hPprime⟩
    obtain ⟨hz, hzP⟩ := exists_fromSpec_mem_and_primeIdealOf_eq_consolidated238 hW ⟨P, hPprime⟩
    have hzs : hW.fromSpec.base (⟨P, hPprime⟩ : PrimeSpectrum Γ(X, W)) ∈ D.support := by
      rw [mem_support_iff_ideal_le_primeIdealOf_consolidated238 D hW hz, hzP]
      exact hPle
    have hzC : hW.fromSpec.base (⟨P, hPprime⟩ : PrimeSpectrum Γ(X, W)) ∈ C := hWC _ hz hzs
    have hfinal : (Scheme.IdealSheafData.vanishingIdeal (⟨C, hCcl⟩ : Closeds ↥X)).ideal ⟨W, hW⟩
        ≤ (hW.primeIdealOf ⟨_, hz⟩).asIdeal :=
      vanishingIdeal_ideal_le_primeIdealOf_consolidated238 (⟨C, hCcl⟩ : Closeds ↥X) hW hz hzC
    rw [hzP] at hfinal
    exact hfinal
  · exact le_vanishingIdeal_of_subset_support_consolidated238 D (⟨C, hCcl⟩ : Closeds ↥X) hCsub ⟨W, hW⟩


end

namespace IsIrreducibleComponentOfSupport

variable {X : Scheme.{u}} {D : X.IdealSheafData} {C : Set X}

theorem orderAt_genericPoint_ne_top [IsLocallyNoetherian X] (hC : IsIrreducibleComponentOfSupport D C)
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I) :
    orderAt I hC.isIrreducible.genericPoint ≠ ⊤ :=
  orderAt_ne_top_of_nonzeroOnComponents I hI hC.isIrreducible.genericPoint

variable {k : Type u} [Field k]

theorem disjoint {C' : Set X} (hC : IsIrreducibleComponentOfSupport D C) (hC' : IsIrreducibleComponentOfSupport D C')
    (p : X ⟶ Spec (CommRingCat.of k))
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    (hne : C ≠ C') : Disjoint C C' := by
  rw [Set.disjoint_left]
  intro y hyC hyC'
  apply hne
  obtain ⟨V, hV, hyV, hetaV, n, c, j, hD, hspec, hetas, hmin⟩ :=
    exists_etaleChart_genericPoint_mem p D hloc hC.isIrreducible hC.subset_support hC.maximal y hyC
  have hspec' : hC'.isIrreducible.genericPoint ⤳ y := hC'.genericPoint_specializes hyC'
  have heta'V : hC'.isIrreducible.genericPoint ∈ V := hspec'.mem_open V.isOpen hyV
  have heta's : hC'.isIrreducible.genericPoint ∈ D.support := hC'.genericPoint_mem_support
  have hmin' : ∀ P : Ideal Γ(X, V), P.IsPrime → c.coord j ∈ P →
      P ≤ (hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩).asIdeal →
      P = (hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩).asIdeal := by
    intro P hP hcoord hle
    obtain ⟨hz, hzP⟩ := exists_fromSpec_mem_and_primeIdealOf_eq_consolidated238 hV ⟨P, hP⟩
    have hzs : hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) ∈ D.support := by
      rw [mem_support_iff_ideal_le_primeIdealOf_consolidated238 D hV hz, hzP]
      rw [c.ideal_eq_span_coord hV D {j} hD, Ideal.span_le]
      rintro f ⟨i, hi, rfl⟩
      have hij : i = j := by simpa using hi
      subst hij
      exact hcoord
    have hsp : (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) ⤳
        hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩ := by
      rw [specializes_iff_mem_closure, PrimeSpectrum.closure_singleton,
        PrimeSpectrum.mem_zeroLocus]
      exact hle
    have hspz : hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) ⤳
        hC'.isIrreducible.genericPoint := by
      have hmapped := hsp.map hV.fromSpec.base.hom.continuous
      rwa [hV.fromSpec_primeIdealOf] at hmapped
    have hclo : closure {hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V))} = C' := by
      refine hC'.maximal _ isIrreducible_singleton.closure ?_ ?_
      · have h1 : {hC'.isIrreducible.genericPoint} ⊆
            closure {hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V))} :=
          Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hspz)
        have h2 := closure_mono h1
        rw [closure_closure] at h2
        rw [← hC'.closure_genericPoint]
        exact h2
      · have h3 : closure {hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V))}
            ⊆ closure ((D.support : Set ↥X)) :=
          closure_mono (Set.singleton_subset_iff.mpr hzs)
        rwa [D.support.isClosed.closure_eq] at h3
    have hzC' : hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) ∈ C' := by
      rw [← hclo]; exact subset_closure (Set.mem_singleton _)
    have hzeq : hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V))
        = hC'.isIrreducible.genericPoint :=
      (hspz.antisymm (hC'.genericPoint_specializes hzC')).eq
    have hfin : hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩
        = (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) := by
      rw [← hzP]
      congr 1
      exact Subtype.ext hzeq.symm
    exact (congrArg PrimeSpectrum.asIdeal hfin).symm
  have e1 := primeIdealOf_eq_comap_span_germ_coord p hV c j D hD y
    hC.isIrreducible.genericPoint hyV hetaV hspec hetas hmin
  have e2 := primeIdealOf_eq_comap_span_germ_coord p hV c j D hD y
    hC'.isIrreducible.genericPoint hyV heta'V hspec' heta's hmin'
  have hP : hV.primeIdealOf ⟨hC.isIrreducible.genericPoint, hetaV⟩
      = hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩ :=
    PrimeSpectrum.ext (e1.trans e2.symm)
  have hpts : hC.isIrreducible.genericPoint = hC'.isIrreducible.genericPoint := by
    have h := congrArg (fun q => hV.fromSpec.base q) hP
    simpa only [hV.fromSpec_primeIdealOf] using h
  rw [← hC.closure_genericPoint, ← hC'.closure_genericPoint, hpts]

section
variable [TopologicalSpace.NoetherianSpace ↥X] (hC : IsIrreducibleComponentOfSupport D C) (p : X ⟶ Spec (CommRingCat.of k)) (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n), restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j}) (x : X) (hx : x ∈ C)
include hloc hx

theorem exists_affineOpen_etaleChart_coordIdeal :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (_ : x ∈ V) (n : ℕ) (c : EtaleChart p V n) (j : Fin n),
      restrictIdeal D V = c.coordIdeal {j} ∧
      (∀ y : X, y ∈ V → y ∈ (D.support : Set X) → y ∈ C) ∧
      (Scheme.IdealSheafData.vanishingIdeal
          (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)).ideal ⟨V, hV⟩ = D.ideal ⟨V, hV⟩ ∧
      (∀ W : X.affineOpens, (↑W : X.Opens) ≤ V →
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)).ideal W = D.ideal W) ∧
      (∀ y : X, y ∈ V →
        stalkIdeal (Scheme.IdealSheafData.vanishingIdeal
          (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)) y = stalkIdeal D y) := by
  obtain ⟨U, hxU, n, c₀, hU⟩ := hloc x
  have hxs : x ∈ (D.support : Set X) := hC.subset_support hx
  have hDUex : ∃ j : Fin n, restrictIdeal D U = c₀.coordIdeal {j} := by
    rcases hU with h | h
    · exact absurd hxs (notMem_support_of_mem_opens_of_restrictIdeal_eq_top D U h x hxU)
    · exact h
  obtain ⟨j, hDU⟩ := hDUex
  obtain ⟨B, hBclosed, hxB, hBmem⟩ :
      ∃ B : Set ↥X, IsClosed B ∧ x ∉ B ∧
        ∀ y : ↥X, y ∈ (D.support : Set X) → y ∉ B → y ∈ C := by
    refine ⟨⋃ C'' ∈ {C'' : Set X | IsIrreducibleComponentOfSupport D C''} \ {C}, C'', ?_, ?_, ?_⟩
    · refine Set.Finite.isClosed_biUnion
        ((finite_isIrreducibleComponentOfSupport D).subset Set.sdiff_subset) ?_
      intro C'' hC''
      exact hC''.1.isClosed
    · intro hmem
      obtain ⟨C'', hC''mem, hxC''⟩ := Set.mem_iUnion₂.mp hmem
      exact Set.disjoint_left.mp
        (hC.disjoint hC''mem.1 p hloc (fun h => hC''mem.2 h.symm)) hx hxC''
    · intro y hys hyB
      obtain ⟨C'', hC''comp, hyC''⟩ := exists_isIrreducibleComponentOfSupport D y hys
      by_cases h : C'' = C
      · exact h ▸ hyC''
      · exact absurd (Set.mem_iUnion₂.mpr ⟨C'', ⟨hC''comp, h⟩, hyC''⟩) hyB
  have hxUB : x ∈ (⟨(U : Set ↥X) ∩ Bᶜ, U.isOpen.inter hBclosed.isOpen_compl⟩ : X.Opens) :=
    ⟨hxU, hxB⟩
  obtain ⟨V, hxV, hVle⟩ := Scheme.exists_affineOpens_mem_le hxUB
  have hVU : (V : X.Opens) ≤ U := fun y hy => (hVle hy).1
  have hVB : ∀ y : ↥X, y ∈ (V : X.Opens) → y ∉ B := fun y hy => (hVle hy).2
  have hDV : restrictIdeal D (V : X.Opens) = (c₀.restrict hVU).coordIdeal {j} :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU c₀ D {j} hDU
  have hVC : ∀ y : X, y ∈ (V : X.Opens) → y ∈ (D.support : Set X) → y ∈ C :=
    fun y hy hys => hBmem y hys (hVB y hy)
  have key : ∀ W : X.affineOpens, (W : X.Opens) ≤ (V : X.Opens) →
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨C, hC.isClosed⟩ : Closeds ↥X)).ideal W = D.ideal W := by
    intro W hWV
    have hDW : restrictIdeal D (W : X.Opens)
        = ((c₀.restrict hVU).restrict hWV).coordIdeal {j} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hWV (c₀.restrict hVU) D {j} hDV
    exact vanishingIdeal_ideal_eq_of_restrictIdeal_eq_coordIdeal_consolidated238 D hC.isClosed hC.subset_support W.2
      ((c₀.restrict hVU).restrict hWV) {j} hDW
      (fun y hy hys => hVC y (hWV hy) hys)
  refine ⟨(V : X.Opens), V.2, hxV, n, c₀.restrict hVU, j, hDV, hVC, key V le_rfl, ?_, ?_⟩
  · intro W hWV
    exact key W hWV
  · intro y hy
    rw [stalkIdeal_eq_map_germ
        (Scheme.IdealSheafData.vanishingIdeal (⟨C, hC.isClosed⟩ : Closeds ↥X)) y V hy,
      stalkIdeal_eq_map_germ D y V hy, key V le_rfl]

theorem stalkIdeal_vanishingIdeal_eq :
    stalkIdeal (Scheme.IdealSheafData.vanishingIdeal
      (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)) x = stalkIdeal D x := by
  obtain ⟨V, hV, hxV, n, c, j, -, -, -, -, hstalk⟩ := hC.exists_affineOpen_etaleChart_coordIdeal p hloc x hx
  exact hstalk x hxV


end

end IsIrreducibleComponentOfSupport

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.EtaleMaxContactComparison
section

open TopologicalSpace


structure EtaleMaxContactComparison (k : Type u) [Field k] {P : Scheme.{u}}
    (p : P ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (A : P.IdealSheafData) (μ : ℕ) (N : List P.IdealSheafData)
    (H₁ H₂ : P.IdealSheafData) (pt : P) where
  W : Scheme.{u}
  f₁ : W ⟶ P
  f₂ : W ⟶ P
  w : W
  [isAffine : IsAffine W]
  [etale_f₁ : Etale f₁]
  [etale_f₂ : Etale f₂]
  [lft_f₁ : LocallyOfFiniteType (f₁ ≫ p)]
  base_f₁ : f₁.base w = pt
  base_f₂ : f₂.base w = pt
  comap_A : A.comap f₁ = A.comap f₂
  comap_H : H₁.comap f₁ = H₂.comap f₂
  comap_N : ∀ J ∈ N, J.comap f₁ = J.comap f₂
  comp_p : f₁ ≫ p = f₂ ≫ p
  maxContact_comp :
    (@maxContactIdeal k _ _ W (f₁ ≫ p) lft_f₁ (A.comap f₁) μ).subschemeι ≫ f₁ =
      (@maxContactIdeal k _ _ W (f₁ ≫ p) lft_f₁ (A.comap f₁) μ).subschemeι ≫ f₂

private theorem ideal_eq_of_map_eq_of_leftInverse_consolidated240 {R S : Type*} [CommRing R] [CommRing S]
    (σ : R →+* S) (τ : S →+* R) (hτσ : τ.comp σ = RingHom.id R)
    {A B : Ideal R} (hmap : Ideal.map σ A = Ideal.map σ B) : A = B := by
  have h2 := congrArg (Ideal.map τ) hmap
  rwa [Ideal.map_map, Ideal.map_map, hτσ, Ideal.map_id, Ideal.map_id] at h2

theorem idealSheafData_eq_of_forall_comap_eq {X : Scheme.{u}} {ι : Type u} (Y : ι → Scheme.{u})
    (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcov : (⋃ i, Set.range ⇑(f i).base) = Set.univ)
    (I J : X.IdealSheafData) (h : ∀ i, I.comap (f i) = J.comap (f i)) : I = J := by
  have key : ∀ x : X, stalkIdeal I x = stalkIdeal J x := by
    intro x
    have hx : x ∈ (⋃ i, Set.range ⇑(f i).base) := by
      rw [hcov]
      exact Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨y, hy⟩ := Set.mem_range.mp hi
    subst hy
    have hiso : IsIso ((f i).stalkMap y) := inferInstance
    have hinv : (inv ((f i).stalkMap y)).hom.comp ((f i).stalkMap y).hom
        = RingHom.id (X.presheaf.stalk ((f i).base y)) := by
      rw [← CommRingCat.hom_comp, IsIso.hom_inv_id, CommRingCat.hom_id]
    have hmap : Ideal.map ((f i).stalkMap y).hom (stalkIdeal I ((f i).base y))
        = Ideal.map ((f i).stalkMap y).hom (stalkIdeal J ((f i).base y)) := by
      rw [← stalkIdeal_comap (f i) I y, ← stalkIdeal_comap (f i) J y, h i]
    exact ideal_eq_of_map_eq_of_leftInverse_consolidated240 _ _ hinv hmap
  refine le_antisymm ?_ ?_
  · exact (le_iff_forall_stalkIdeal_le I J).mpr fun x => le_of_eq (key x)
  · exact (le_iff_forall_stalkIdeal_le J I).mpr fun x => le_of_eq (key x).symm

private theorem comap_eq_ker_pullback_fst_consolidated240 {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData) :
    I.comap f = Scheme.Hom.ker (Limits.pullback.fst f I.subschemeι) := rfl

open CategoryTheory.Limits in
private theorem iUnion_range_sigmaι_base_eq_univ_consolidated240 {ι : Type u} (X : ι → Scheme.{u}) :
    (⋃ i, Set.range ⇑(Sigma.ι X i).base) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨⟨i, y⟩, hx⟩ := (sigmaMk X).surjective x
  have hx' : (Sigma.ι X i).base y = x := by simpa using hx
  exact Set.mem_iUnion.mpr ⟨i, ⟨y, hx'⟩⟩

private theorem derivIdealSheafIterate_congr_of_eq_of_eq_consolidated240 (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p q : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [LocallyOfFiniteType q] (hpq : p = q) (r : ℕ)
    (I J : X.IdealSheafData) (hIJ : I = J) :
    derivIdealSheafIterate k p r I = derivIdealSheafIterate k q r J := by
  subst hpq
  subst hIJ
  rfl

private theorem hom_ext_of_opens_cover_consolidated240 {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (hcov : ∀ x : ↥X, ∃ i, x ∈ U i) {Q : Scheme.{u}} (a b : X ⟶ Q)
    (hab : ∀ i, (U i).ι ≫ a = (U i).ι ≫ b) : a = b := by
  have hc : ∀ x : ↥X, ∃ i, ∃ y : ↥((U i).toScheme), ((U i).ι).base y = x := by
    intro x
    obtain ⟨i, hi⟩ := hcov x
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  exact Scheme.Cover.hom_ext
    (Scheme.Cover.mkOfCovers ι (fun i => (U i).toScheme) (fun i => (U i).ι) hc) a b
    (fun i => hab i)

open CategoryTheory.Limits in
private theorem subschemeι_comp_eq_of_forall_sigmaι_comap_consolidated240 {ι : Type u} (Wf : ι → Scheme.{u})
    {Q : Scheme.{u}} (M : (∐ Wf).IdealSheafData) (a b : (∐ Wf) ⟶ Q)
    (h : ∀ i, (M.comap (Sigma.ι Wf i)).subschemeι ≫ Sigma.ι Wf i ≫ a
            = (M.comap (Sigma.ι Wf i)).subschemeι ≫ Sigma.ι Wf i ≫ b) :
    M.subschemeι ≫ a = M.subschemeι ≫ b := by
  refine hom_ext_of_opens_cover_consolidated240
    (fun i => M.subschemeι ⁻¹ᵁ (Sigma.ι Wf i).opensRange) ?_ _ _ ?_
  · intro x
    have hx : M.subschemeι.base x ∈ (⋃ i, Set.range ⇑(Sigma.ι Wf i).base) := by
      rw [iUnion_range_sigmaι_base_eq_univ_consolidated240]
      trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, hi⟩
  · intro i
    have hrange : Set.range ⇑((M.subschemeι ⁻¹ᵁ (Sigma.ι Wf i).opensRange).ι
          ≫ M.subschemeι).base ⊆ Set.range ⇑(Sigma.ι Wf i).base := by
      rintro y ⟨z, rfl⟩
      exact z.2
    obtain ⟨α, hα⟩ : ∃ α : (M.subschemeι ⁻¹ᵁ (Sigma.ι Wf i).opensRange).toScheme ⟶ Wf i,
        α ≫ Sigma.ι Wf i
          = (M.subschemeι ⁻¹ᵁ (Sigma.ι Wf i).opensRange).ι ≫ M.subschemeι :=
      ⟨IsOpenImmersion.lift _ _ hrange, IsOpenImmersion.lift_fac _ _ hrange⟩
    obtain ⟨β, hβ⟩ : ∃ β : (M.subschemeι ⁻¹ᵁ (Sigma.ι Wf i).opensRange).toScheme
          ⟶ pullback (Sigma.ι Wf i) M.subschemeι,
        β ≫ pullback.fst (Sigma.ι Wf i) M.subschemeι = α :=
      ⟨pullback.lift α ((M.subschemeι ⁻¹ᵁ (Sigma.ι Wf i).opensRange).ι) hα,
        pullback.lift_fst _ _ _⟩
    have hker : Scheme.Hom.ker ((M.comap (Sigma.ι Wf i)).subschemeι)
        ≤ Scheme.Hom.ker (pullback.fst (Sigma.ι Wf i) M.subschemeι) := by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact le_of_eq (comap_eq_ker_pullback_fst_consolidated240 (Sigma.ι Wf i) M)
    obtain ⟨u, hu⟩ : ∃ u : pullback (Sigma.ι Wf i) M.subschemeι
          ⟶ (M.comap (Sigma.ι Wf i)).subscheme,
        u ≫ (M.comap (Sigma.ι Wf i)).subschemeι
          = pullback.fst (Sigma.ι Wf i) M.subschemeι :=
      ⟨IsClosedImmersion.lift _ _ hker, IsClosedImmersion.lift_fac _ _ hker⟩
    have keyA : (M.subschemeι ⁻¹ᵁ (Sigma.ι Wf i).opensRange).ι ≫ M.subschemeι
        = (β ≫ u) ≫ ((M.comap (Sigma.ι Wf i)).subschemeι ≫ Sigma.ι Wf i) := by
      simp only [Category.assoc]
      rw [← Category.assoc u, hu, ← Category.assoc, hβ, hα]
    have e1 : ((M.subschemeι ⁻¹ᵁ (Sigma.ι Wf i).opensRange).ι ≫ M.subschemeι) ≫ a
        = ((M.subschemeι ⁻¹ᵁ (Sigma.ι Wf i).opensRange).ι ≫ M.subschemeι) ≫ b := by
      rw [keyA]
      simp only [Category.assoc]
      rw [h i]
    simpa only [Category.assoc] using e1

open CategoryTheory.Limits in
private theorem exists_etale_maxContactIdeal_comparison_of_finite_cover_consolidated240 {k : Type u} [Field k] [CharZero k]
    {P : Scheme.{u}}
    (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (A : P.IdealSheafData) (μ : ℕ) (N : List P.IdealSheafData) (H₁ H₂ : P.IdealSheafData)
    {ι : Type u} [Finite ι] (pts : ι → ↥P)
    (c : ∀ i, EtaleMaxContactComparison k p A μ N H₁ H₂ (pts i))
    (hcov : orderAtLeastLocus A μ ⊆ ⋃ i, (Set.range ⇑(c i).f₁.base ∩ Set.range ⇑(c i).f₂.base)) :
    ∃ (V : Scheme.{u}) (g₁ : V ⟶ P) (g₂ : V ⟶ P) (_ : Etale g₁) (_ : Etale g₂)
      (_ : QuasiCompact (g₁ ≫ p)) (hlft : LocallyOfFiniteType (g₁ ≫ p)),
      g₁ ≫ p = g₂ ≫ p ∧
      orderAtLeastLocus A μ ⊆ Set.range ⇑g₁.base ∧
      orderAtLeastLocus A μ ⊆ Set.range ⇑g₂.base ∧
      A.comap g₁ = A.comap g₂ ∧
      H₁.comap g₁ = H₂.comap g₂ ∧
      N.map (fun J => J.comap g₁) = N.map (fun J => J.comap g₂) ∧
      (@maxContactIdeal k _ _ V (g₁ ≫ p) hlft (A.comap g₁) μ).subschemeι ≫ g₁ =
        (@maxContactIdeal k _ _ V (g₁ ≫ p) hlft (A.comap g₁) μ).subschemeι ≫ g₂ := by
  classical
  have hWaff : ∀ i, IsAffine (c i).W := fun i => (c i).isAffine
  have hWe₁ : ∀ i, Etale (c i).f₁ := fun i => (c i).etale_f₁
  have hWe₂ : ∀ i, Etale (c i).f₂ := fun i => (c i).etale_f₂
  have hWlft : ∀ i, LocallyOfFiniteType ((c i).f₁ ≫ p) := fun i => (c i).lft_f₁
  have hoi : ∀ i, IsOpenImmersion (Sigma.ι (fun j => (c j).W) i) := fun i => inferInstance
  have hVaff : IsAffine (∐ fun i => (c i).W) := inferInstance
  have he₁ : Etale (Sigma.desc fun i => (c i).f₁) :=
    etale_sigmaDesc (fun i => (c i).f₁) fun i => (c i).etale_f₁
  have he₂ : Etale (Sigma.desc fun i => (c i).f₂) :=
    etale_sigmaDesc (fun i => (c i).f₂) fun i => (c i).etale_f₂
  have hlft : LocallyOfFiniteType ((Sigma.desc fun i => (c i).f₁) ≫ p) := inferInstance
  have hcsV : CompactSpace ↥(∐ fun i => (c i).W) := inferInstance
  have hss : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstance
  have hqc : QuasiCompact ((Sigma.desc fun i => (c i).f₁) ≫ p) := by
    apply AlgebraicGeometry.quasiCompact_of_compactSpace_of_subsingleton
  refine ⟨∐ (fun i => (c i).W), Sigma.desc (fun i => (c i).f₁), Sigma.desc (fun i => (c i).f₂),
    he₁, he₂, hqc, hlft, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Sigma.hom_ext _ _ fun i => ?_
    simp only [← Category.assoc, Sigma.ι_desc]
    exact (c i).comp_p
  · intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hy)
    obtain ⟨w, hw⟩ := hi.1
    refine ⟨(Sigma.ι (fun j => (c j).W) i).base w, ?_⟩
    show (Sigma.ι (fun j => (c j).W) i ≫ Sigma.desc fun j => (c j).f₁).base w = y
    rw [Sigma.ι_desc]
    exact hw
  · intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hy)
    obtain ⟨w, hw⟩ := hi.2
    refine ⟨(Sigma.ι (fun j => (c j).W) i).base w, ?_⟩
    show (Sigma.ι (fun j => (c j).W) i ≫ Sigma.desc fun j => (c j).f₂).base w = y
    rw [Sigma.ι_desc]
    exact hw
  · refine idealSheafData_eq_of_forall_comap_eq (fun i => (c i).W)
      (fun i => Sigma.ι (fun j => (c j).W) i) (iUnion_range_sigmaι_base_eq_univ_consolidated240 _) _ _ fun i => ?_
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      Sigma.ι_desc, Sigma.ι_desc]
    exact (c i).comap_A
  · refine idealSheafData_eq_of_forall_comap_eq (fun i => (c i).W)
      (fun i => Sigma.ι (fun j => (c j).W) i) (iUnion_range_sigmaι_base_eq_univ_consolidated240 _) _ _ fun i => ?_
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      Sigma.ι_desc, Sigma.ι_desc]
    exact (c i).comap_H
  · refine List.map_congr_left fun J hJ => ?_
    refine idealSheafData_eq_of_forall_comap_eq (fun i => (c i).W)
      (fun i => Sigma.ι (fun j => (c j).W) i) (iUnion_range_sigmaι_base_eq_univ_consolidated240 _) _ _ fun i => ?_
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      Sigma.ι_desc, Sigma.ι_desc]
    exact (c i).comap_N J hJ
  · have hMc : ∀ i, (@maxContactIdeal k _ _ (∐ fun j => (c j).W)
          ((Sigma.desc fun j => (c j).f₁) ≫ p) hlft
          (A.comap (Sigma.desc fun j => (c j).f₁)) μ).comap (Sigma.ι (fun j => (c j).W) i)
        = @maxContactIdeal k _ _ (c i).W ((c i).f₁ ≫ p) (hWlft i) (A.comap (c i).f₁) μ := by
      intro i
      rw [maxContactIdeal_eq_derivIdealSheafIterate, maxContactIdeal_eq_derivIdealSheafIterate,
        ← derivIdealSheafIterate_comap k ((Sigma.desc fun j => (c j).f₁) ≫ p)
          (Sigma.ι (fun j => (c j).W) i) (μ - 1) (A.comap (Sigma.desc fun j => (c j).f₁))]
      refine derivIdealSheafIterate_congr_of_eq_of_eq_consolidated240 k _ _ ?_ (μ - 1) _ _ ?_
      · rw [← Category.assoc, Sigma.ι_desc]
      · rw [← Scheme.IdealSheafData.comap_comp, Sigma.ι_desc]
    refine subschemeι_comp_eq_of_forall_sigmaι_comap_consolidated240 _ _ _ _ fun i => ?_
    rw [hMc i, Sigma.ι_desc, Sigma.ι_desc]
    exact (c i).maxContact_comp

theorem exists_etale_maxContactIdeal_comparison (k : Type u) [Field k] [CharZero k]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p]
    [LocallyOfFiniteType p] [QuasiCompact p] (A : P.IdealSheafData) (μ : ℕ)
    (N : List P.IdealSheafData) (H₁ H₂ : P.IdealSheafData)
    (hloc : ∀ pt ∈ orderAtLeastLocus A μ, Nonempty (EtaleMaxContactComparison k p A μ N H₁ H₂ pt)) :
    ∃ (V : Scheme.{u}) (g₁ : V ⟶ P) (g₂ : V ⟶ P) (_ : Etale g₁) (_ : Etale g₂)
      (_ : QuasiCompact (g₁ ≫ p)) (hlft : LocallyOfFiniteType (g₁ ≫ p)),
      g₁ ≫ p = g₂ ≫ p ∧
      orderAtLeastLocus A μ ⊆ Set.range ⇑g₁.base ∧
      orderAtLeastLocus A μ ⊆ Set.range ⇑g₂.base ∧
      A.comap g₁ = A.comap g₂ ∧
      H₁.comap g₁ = H₂.comap g₂ ∧
      N.map (fun J => J.comap g₁) = N.map (fun J => J.comap g₂) ∧
      (@maxContactIdeal k _ _ V (g₁ ≫ p) hlft (A.comap g₁) μ).subschemeι ≫ g₁ =
        (@maxContactIdeal k _ _ V (g₁ ≫ p) hlft (A.comap g₁) μ).subschemeι ≫ g₂ := by
  classical
  have hsub : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstance
  have hcsS : CompactSpace ↥(Spec (CommRingCat.of k)) := inferInstance
  have hcP : CompactSpace ↥P := by
    constructor
    have h := (‹QuasiCompact p›).isCompact_preimage Set.univ isOpen_univ isCompact_univ
    rwa [Set.preimage_univ] at h
  have hcomp : IsCompact (orderAtLeastLocus A μ) := (isClosed_orderAtLeastLocus k p A μ).isCompact
  have c : ∀ x : ↥(orderAtLeastLocus A μ), EtaleMaxContactComparison k p A μ N H₁ H₂ x.1 :=
    fun x => Classical.choice (hloc x.1 x.2)
  have hopen : ∀ x : ↥(orderAtLeastLocus A μ),
      IsOpen (Set.range ⇑(c x).f₁.base ∩ Set.range ⇑(c x).f₂.base) := by
    intro x
    have := (c x).etale_f₁
    have := (c x).etale_f₂
    exact (c x).f₁.isOpenMap.isOpen_range.inter (c x).f₂.isOpenMap.isOpen_range
  have hsub2 : orderAtLeastLocus A μ ⊆ ⋃ x : ↥(orderAtLeastLocus A μ),
      (Set.range ⇑(c x).f₁.base ∩ Set.range ⇑(c x).f₂.base) := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, ⟨⟨(c ⟨y, hy⟩).w, (c ⟨y, hy⟩).base_f₁⟩,
      ⟨(c ⟨y, hy⟩).w, (c ⟨y, hy⟩).base_f₂⟩⟩⟩
  obtain ⟨T, hT⟩ := hcomp.elim_finite_subcover
    (fun x : ↥(orderAtLeastLocus A μ) => Set.range ⇑(c x).f₁.base ∩ Set.range ⇑(c x).f₂.base)
    hopen hsub2
  refine exists_etale_maxContactIdeal_comparison_of_finite_cover_consolidated240 p A μ N H₁ H₂
    (fun i : {x : ↥(orderAtLeastLocus A μ) // x ∈ T} => (i.1 : ↥P)) (fun i => c i.1) ?_
  intro y hy
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hT hy)
  obtain ⟨hxT, hmem⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨⟨x, hxT⟩, hmem⟩

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedIdealSheaf
section



private theorem ideal_listProd_map_consolidated273 {X : Scheme.{u}} (g : ℕ → X.IdealSheafData) (l : List ℕ)
    (U : X.affineOpens) :
    ((l.map g).prod).ideal U = (l.map (fun j => (g j).ideal U)).prod := by
  induction l with
  | nil =>
      simp only [List.map_nil, List.prod_nil, Scheme.IdealSheafData.one_eq_top,
        Scheme.IdealSheafData.ideal_top]
      exact Ideal.one_eq_top.symm
  | cons a t ih =>
      have hmul : ((g a) * (t.map g).prod).ideal U
          = (g a).ideal U * ((t.map g).prod).ideal U := by
        simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, hmul, ih]

private theorem ideal_map_prod_range_consolidated273 {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (g : ℕ → Ideal R) (n : ℕ) :
    Ideal.map φ (∏ j ∈ Finset.range n, g j) = ∏ j ∈ Finset.range n, Ideal.map φ (g j) :=
  map_prod (Ideal.mapHom φ) g (Finset.range n)

section
variable (k : Type u) [CommRing k] {R S : Type u} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (φ : R →+* S) (J : Ideal R)

private theorem map_tuningMonomial_of_map_derivIdealIterate_consolidated273 (m : ℕ)
    (c : ℕ → ℕ)
    (h : ∀ j : ℕ, Ideal.map φ (derivIdealIterate k j J) = derivIdealIterate k j (Ideal.map φ J)) :
    Ideal.map φ (tuningMonomial k J m c) = tuningMonomial k (Ideal.map φ J) m c := by
  rw [tuningMonomial_eq_prod, tuningMonomial_eq_prod, ideal_map_prod_range_consolidated273]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Ideal.map_pow, h j]

private theorem map_tunedIdeal_of_map_derivIdealIterate_consolidated273 (m s : ℕ)
    (h : ∀ j : ℕ, Ideal.map φ (derivIdealIterate k j J) = derivIdealIterate k j (Ideal.map φ J)) :
    Ideal.map φ (tunedIdeal k J m s) = tunedIdeal k (Ideal.map φ J) m s := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    refine (tunedIdeal_le_iff k J m s _).mpr ?_
    intro c hc
    rw [← Ideal.map_le_iff_le_comap, map_tuningMonomial_of_map_derivIdealIterate_consolidated273 k φ J m c h]
    exact tuningMonomial_le_tunedIdeal k (Ideal.map φ J) m s c hc
  · refine (tunedIdeal_le_iff k (Ideal.map φ J) m s _).mpr ?_
    intro c hc
    rw [← map_tuningMonomial_of_map_derivIdealIterate_consolidated273 k φ J m c h]
    exact Ideal.map_mono (tuningMonomial_le_tunedIdeal k J m s c hc)


end

private theorem pow_derivIdealIterate_pred_le_tunedIdeal_consolidated273 (k : Type u) [CommRing k] {S : Type u}
    [CommRing S] [Algebra k S] (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) (t : ℕ) :
    (derivIdealIterate k (m - 1) J) ^ t ≤ tunedIdeal k J m t := by
  have hmem : m - 1 ∈ Finset.range m := Finset.mem_range.mpr (by omega)
  have h1 : m - (m - 1) = 1 := by omega
  have hmono : tuningMonomial k J m (fun j => if j = m - 1 then t else 0)
      = (derivIdealIterate k (m - 1) J) ^ t := by
    rw [tuningMonomial_eq_prod]
    refine (Finset.prod_eq_single (m - 1) (fun b _ hb => by simp [hb])
      (fun h => absurd hmem h)).trans ?_
    simp
  have hw : tuningWeight m (fun j => if j = m - 1 then t else 0) = t := by
    rw [tuningWeight_eq_sum]
    refine (Finset.sum_eq_single (m - 1) (fun b _ hb => by simp [hb])
      (fun h => absurd hmem h)).trans ?_
    simp [h1]
  rw [← hmono]
  exact tuningMonomial_le_tunedIdeal k J m t _ (le_of_eq hw.symm)

section
variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData)

private theorem ideal_prod_derivIdealSheafIterate_pow_consolidated273 (m : ℕ) (c : ℕ → ℕ) (U : X.affineOpens) :
    (((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ (c j))).prod).ideal U =
      @tuningMonomial k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m c := by
  have hpow : ∀ (J : X.IdealSheafData) (n : ℕ), (J ^ n).ideal U = (J.ideal U) ^ n := by
    intro J n
    exact congrFun (show (J ^ n).ideal = J.ideal ^ n by
      rw [Scheme.IdealSheafData.ideal_pow]) U
  have key : ((List.range m).map
        (fun j =>
          (@derivIdealIterate k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1) j (I.ideal U)) ^ c j)).prod
      = @tuningMonomial k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1) (I.ideal U) m c :=
    listProd_map_range_eq_prod _ m
  simp only [ideal_listProd_map_consolidated273, hpow, derivIdealSheafIterate_ideal]
  exact key

private theorem map_tunedIdeal_basicOpen_consolidated273 (m s : ℕ) :
    ∀ (U : X.affineOpens) (f : Γ(X, U.1)),
      Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
          (@tunedIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m s) =
        @tunedIdeal k _ _ _ (sectionsAlgebra k p (X.affineBasicOpen f).1)
          (I.ideal (X.affineBasicOpen f)) m s := by
  intro U f
  let algU : Algebra k Γ(X, U.1) := sectionsAlgebra k p U.1
  let algV : Algebra k Γ(X, X.basicOpen f) := sectionsAlgebra k p (X.basicOpen f)
  have hI : Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom (I.ideal U) =
      I.ideal (X.affineBasicOpen f) := I.map_ideal_basicOpen U f
  have hd : ∀ j : ℕ,
      Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
          (@derivIdealIterate k _ Γ(X, U.1) _ algU j (I.ideal U)) =
        @derivIdealIterate k _ Γ(X, X.basicOpen f) _ algV j
          (Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom (I.ideal U)) := by
    intro j
    have h1 := (derivIdealSheafIterate k p j I).map_ideal_basicOpen U f
    rw [derivIdealSheafIterate_ideal, derivIdealSheafIterate_ideal] at h1
    exact h1.trans (congrArg (@derivIdealIterate k _ Γ(X, X.basicOpen f) _ algV j) hI.symm)
  have h2 := @map_tunedIdeal_of_map_derivIdealIterate_consolidated273 k _ Γ(X, U.1) Γ(X, X.basicOpen f) _ _ algU algV
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom (I.ideal U) m s hd
  exact h2.trans (congrArg (fun J : Ideal Γ(X, X.basicOpen f) =>
    @tunedIdeal k _ Γ(X, X.basicOpen f) _ algV J m s) hI)


end

private noncomputable def tunedIdealSheafOfSections (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m s : ℕ) :
    X.IdealSheafData where
  ideal U := @tunedIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m s
  map_ideal_basicOpen := map_tunedIdeal_basicOpen_consolidated273 k p I m s

section
variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData)

@[simp] theorem tunedSheaf_ideal (m s : ℕ) (U : X.affineOpens) :
    (tunedSheaf k p I m s).ideal U =
      @tunedIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m s := by
  refine le_antisymm ?_ ?_
  · have hle : tunedSheaf k p I m s ≤ tunedIdealSheafOfSections k p I m s := by
      rw [tunedSheaf_eq_iSup]
      refine iSup_le fun c => ?_
      have key : ∀ V : X.affineOpens,
          (((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ (c.1 j))).prod).ideal V ≤
            (tunedIdealSheafOfSections k p I m s).ideal V := by
        intro V
        rw [ideal_prod_derivIdealSheafIterate_pow_consolidated273 k p I m c.1 V]
        exact @tuningMonomial_le_tunedIdeal k _ Γ(X, V.1) _ (sectionsAlgebra k p V.1)
          (I.ideal V) m s c.1 c.2
      exact key
    exact hle U
  · refine (@tunedIdeal_le_iff k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1)
      (I.ideal U) m s _).mpr ?_
    intro c hc
    rw [← ideal_prod_derivIdealSheafIterate_pow_consolidated273 k p I m c U]
    have hmono : ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ (c j))).prod ≤
        tunedSheaf k p I m s := by
      rw [tunedSheaf_eq_iSup]
      exact le_iSup (fun d : {d : ℕ → ℕ // s ≤ ∑ j ∈ Finset.range m, (m - j) * d j} =>
        ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ (d.1 j))).prod) ⟨c, hc⟩
    exact hmono U

private theorem derivIdealSheafIterate_pow_le_tunedSheaf_consolidated273 (m : ℕ) (hm : 1 ≤ m) (t : ℕ) :
    (derivIdealSheafIterate k p (m - 1) I) ^ t ≤ tunedSheaf k p I m t := by
  have h : ∀ U : X.affineOpens,
      ((derivIdealSheafIterate k p (m - 1) I) ^ t).ideal U ≤ (tunedSheaf k p I m t).ideal U := by
    intro U
    have hpow : ((derivIdealSheafIterate k p (m - 1) I) ^ t).ideal U
        = ((derivIdealSheafIterate k p (m - 1) I).ideal U) ^ t :=
      congrFun (show ((derivIdealSheafIterate k p (m - 1) I) ^ t).ideal
          = (derivIdealSheafIterate k p (m - 1) I).ideal ^ t by
        rw [Scheme.IdealSheafData.ideal_pow]) U
    rw [hpow, derivIdealSheafIterate_ideal, tunedSheaf_ideal]
    exact @pow_derivIdealIterate_pred_le_tunedIdeal_consolidated273 k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1)
      (I.ideal U) m hm t
  exact h

private theorem tunedSheaf_one_eq_derivIdealSheafIterate_consolidated273 (m : ℕ) (hm : 1 ≤ m) :
    tunedSheaf k p I m 1 = derivIdealSheafIterate k p (m - 1) I := by
  refine le_antisymm ?_ ?_
  · have h : ∀ U : X.affineOpens,
        (tunedSheaf k p I m 1).ideal U ≤ (derivIdealSheafIterate k p (m - 1) I).ideal U := by
      intro U
      rw [tunedSheaf_ideal, derivIdealSheafIterate_ideal]
      exact @tunedIdeal_one_le_derivIdealIterate k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1) (I.ideal U) m hm
    exact h
  · have h := derivIdealSheafIterate_pow_le_tunedSheaf_consolidated273 k p I m hm 1
    rwa [pow_one] at h


end

theorem derivIdealSheaf_tunedSheaf_succ : DerivIdealSheafTunedSheafSucc.{u} := by
  intro k _ _ _ X p _ _ I m hm hmax s
  refine le_antisymm ?_ ?_
  · have h : ∀ U : X.affineOpens,
        (derivIdealSheaf k p (tunedSheaf k p I m (s + 1))).ideal U ≤
          (tunedSheaf k p I m s).ideal U := by
      intro U
      rw [derivIdealSheaf_ideal, tunedSheaf_ideal, tunedSheaf_ideal]
      exact @derivIdeal_tunedIdeal_succ_le k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1)
        (I.ideal U) m s
    exact h
  · rw [le_iff_forall_stalkIdeal_le]
    intro x
    have hord : orderAt I x ≤ (m : ℕ∞) := hmax.orderLE x
    rcases eq_or_lt_of_le hord with heq | hlt
    · obtain ⟨U, hU, hxU, n, c, j, hmc, -⟩ := exists_isMaxContactCoord k p I hm x heq
      have hcoord : c.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩ :=
        (isMaxContactCoord_iff_coord_mem k p I m hU c j).mp hmc
      rw [maxContactIdeal_ideal] at hcoord
      have hle : @tunedIdeal k _ Γ(X, U) _ (sectionsAlgebra k p U) (I.ideal ⟨U, hU⟩) m s ≤
          @derivIdeal k _ Γ(X, U) _ (sectionsAlgebra k p U)
            (@tunedIdeal k _ Γ(X, U) _ (sectionsAlgebra k p U)
              (I.ideal ⟨U, hU⟩) m (s + 1)) := by
        let algU : Algebra k Γ(X, U) := sectionsAlgebra k p U
        let algP : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := c.algebra
        have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := c.isScalarTower
        have : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) :=
          c.algebra_formallyEtale hU
        let algQ : Algebra ℚ Γ(X, U) :=
          RingHom.toAlgebra ((algebraMap k Γ(X, U)).comp (algebraMap ℚ k))
        have hδ : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, U) (ULift.up j)
            (c.coord j) = 1 := by
          rw [← EtaleChart.etaleCoordinates_coord c j]
          exact EtaleCoordinates.partialDeriv_coord_self k (ULift.{u} (Fin n)) Γ(X, U)
            (ULift.up j)
        exact tunedIdeal_le_derivIdeal_tunedIdeal_succ k (I.ideal ⟨U, hU⟩) m hm hcoord
          (EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, U) (ULift.up j)) hδ s
      rw [stalkIdeal_eq_map_germ (tunedSheaf k p I m s) x ⟨U, hU⟩ hxU,
        stalkIdeal_eq_map_germ (derivIdealSheaf k p (tunedSheaf k p I m (s + 1))) x ⟨U, hU⟩ hxU]
      refine Ideal.map_mono ?_
      simp only [tunedSheaf_ideal, derivIdealSheaf_ideal]
      exact hle
    · have hxns : x ∉ (derivIdealSheafIterate k p (m - 1) I).support := by
        intro hc
        have hmem : x ∈ orderAtLeastLocus I m := by
          rw [← support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm]
          exact hc
        exact absurd ((mem_orderAtLeastLocus_iff I m x).mp hmem) (not_le.mpr hlt)
      have htop : stalkIdeal (derivIdealSheafIterate k p (m - 1) I) x = ⊤ :=
        not_not.mp fun hne2 => hxns ((mem_support_iff_stalkIdeal_ne_top _ x).mpr hne2)
      have h1 : stalkIdeal ((derivIdealSheafIterate k p (m - 1) I) ^ (s + 1)) x = ⊤ := by
        rw [stalkIdeal_pow, htop, ← Ideal.one_eq_top, one_pow]
      have h2 : stalkIdeal (tunedSheaf k p I m (s + 1)) x ≤
          stalkIdeal (derivIdealSheaf k p (tunedSheaf k p I m (s + 1))) x :=
        stalkIdeal_mono (le_derivIdealSheaf k p (tunedSheaf k p I m (s + 1))) x
      have h3 : (⊤ : Ideal _) ≤
          stalkIdeal (derivIdealSheaf k p (tunedSheaf k p I m (s + 1))) x := by
        rw [← h1]
        exact le_trans
          (stalkIdeal_mono (derivIdealSheafIterate_pow_le_tunedSheaf_consolidated273 k p I m hm (s + 1)) x) h2
      exact le_trans le_top h3

theorem maxContactIdealTunedSheafEq : MaxContactIdealTunedSheafEq.{u} := by
  intro k _ _ _ X p _ _ I m hm hmax s hs
  have h3 : ∀ t : ℕ, derivIdealSheaf k p (tunedSheaf k p I m (t + 1)) = tunedSheaf k p I m t :=
    derivIdealSheaf_tunedSheaf_succ k X p I m hm hmax
  have step : ∀ j t : ℕ, j ≤ t →
      derivIdealSheafIterate k p j (tunedSheaf k p I m t) = tunedSheaf k p I m (t - j) := by
    intro j
    induction j with
    | zero =>
        intro t _
        rw [derivIdealSheafIterate_zero, Nat.sub_zero]
    | succ n ih =>
        intro t ht
        obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        have hn : n ≤ t' := by omega
        have he : t' + 1 - (n + 1) = t' - n := by omega
        rw [he, derivIdealSheafIterate_add k p n 1 (tunedSheaf k p I m (t' + 1)),
          derivIdealSheafIterate_one, h3 t', ih t' hn]
  have hstep := step (s - 1) s (by omega)
  have he2 : s - (s - 1) = 1 := by omega
  rw [hstep, he2, tunedSheaf_one_eq_derivIdealSheafIterate_consolidated273 k p I m hm]

theorem isMaxContactInvariantTunedSheaf :
    IsMaxContactInvariantTunedSheaf.{u} := by
  intro k _ _ _ X p _ _ I m _ _ s hs
  have key : ∀ U : X.affineOpens,
      ((derivIdealSheafIterate k p (s - 1) (tunedSheaf k p I m s)) *
          derivIdealSheaf k p (tunedSheaf k p I m s)).ideal U ≤
        (tunedSheaf k p I m s).ideal U := by
    intro U
    have hmul : ((derivIdealSheafIterate k p (s - 1) (tunedSheaf k p I m s)) *
          derivIdealSheaf k p (tunedSheaf k p I m s)).ideal U =
        (derivIdealSheafIterate k p (s - 1) (tunedSheaf k p I m s)).ideal U *
          (derivIdealSheaf k p (tunedSheaf k p I m s)).ideal U := by
      simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
    rw [hmul, derivIdealSheafIterate_ideal, derivIdealSheaf_ideal, tunedSheaf_ideal]
    exact @derivIdealIterate_mul_derivIdeal_tunedIdeal_le k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1) (I.ideal U) m s hs
  exact key

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactCommonCharts
section

open Opposite TopologicalSpace

section

section

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
  {p : X ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType p] [Smooth p]

private theorem presheaf_map_mem_ideal_of_mem_consolidated290 (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (D : X.IdealSheafData)
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
    {y : Γ(X, U)} (hy : y ∈ D.ideal ⟨U, hU⟩) :
    (X.presheaf.map (homOfLE h).op).hom y ∈ D.ideal ⟨V, hV⟩ := by
  have hcomap : D.ideal ⟨U, hU⟩
      ≤ (D.ideal ⟨V, hV⟩).comap (X.presheaf.map (homOfLE h).op).hom :=
    D.ideal_le_comap_ideal h
  exact hcomap hy

private theorem ideal_le_of_ideal_le_of_le_consolidated290 (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (D E : X.IdealSheafData)
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
    (hDleE : D.ideal ⟨U, hU⟩ ≤ E.ideal ⟨U, hU⟩) : D.ideal ⟨V, hV⟩ ≤ E.ideal ⟨V, hV⟩ := by
  let _ : Algebra k Γ(X, U) := sectionsAlgebra k p U
  have : IsNoetherianRing Γ(X, U) :=
    isNoetherianRing_sections k p ⟨U, hU⟩ (algebraMap_sectionsAlgebra k p U)
  obtain ⟨s, hs⟩ : (D.ideal ⟨U, hU⟩).FG := IsNoetherian.noetherian _
  have hs' : Ideal.span (↑s : Set Γ(X, U)) = D.ideal ⟨U, hU⟩ := hs
  have hspan : D.ideal ⟨V, hV⟩
      = Ideal.span ((X.presheaf.map (homOfLE h).op).hom '' (↑s : Set Γ(X, U))) :=
    ideal_eq_span_image_map_of_le D hU hV h (↑s : Set Γ(X, U)) hs'.symm
  rw [hspan, Ideal.span_le]
  rintro _ ⟨y, hy, rfl⟩
  have hyD : y ∈ D.ideal ⟨U, hU⟩ := by
    rw [← hs']
    exact Ideal.subset_span hy
  exact presheaf_map_mem_ideal_of_mem_consolidated290 k p E hU hV h (hDleE hyD)

private theorem restrictIdeal_eq_coordIdeal_of_coord_eq_consolidated290 {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c c' : EtaleChart p V n) (j : Fin n) (hcoord : c'.coord j = c.coord j)
    (D : X.IdealSheafData) (hD : restrictIdeal D V = c.coordIdeal {j}) :
    restrictIdeal D V = c'.coordIdeal {j} := by
  have h1 : D.ideal ⟨V, hV⟩
      = Ideal.span (c.coord '' ((({j} : Finset (Fin n))) : Set (Fin n))) :=
    c.ideal_eq_span_coord hV D {j} hD
  refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV c' D {j} ?_
  rw [h1, Finset.coe_singleton, Set.image_singleton, Set.image_singleton, hcoord]

theorem exists_common_charts_of_isMaxContactHypersurface (A : X.IdealSheafData) {μ : ℕ}
    (hμ : 1 ≤ μ) (N : List X.IdealSheafData) (H₁ H₂ : X.IdealSheafData)
    (hsnc₁ : InStrictNormalCrossingPosition p (H₁ :: N)) (hsnc₂ : InStrictNormalCrossingPosition p (H₂ :: N))
    (hadm₁ : IsMaxContactHypersurface k p A μ H₁)
    (hadm₂ : IsMaxContactHypersurface k p A μ H₂)
    (x : X) (hx : x ∈ orderAtLeastLocus A μ) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (hxV : x ∈ V) (n : ℕ) (c₁ : EtaleChart p V n)
      (c₂ : EtaleChart p V n) (γ : ℕ → Option (Fin n)) (j₀ : Fin n),
      restrictIdeal H₁ V = c₁.coordIdeal {j₀} ∧
      restrictIdeal H₂ V = c₂.coordIdeal {j₀} ∧
      IsMaxContactCoord k p A μ c₁ j₀ ∧
      IsMaxContactCoord k p A μ c₂ j₀ ∧
      (X.presheaf.germ V x hxV).hom (c₁.coord j₀) ∈
        IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) ∧
      (X.presheaf.germ V x hxV).hom (c₂.coord j₀) ∈
        IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) ∧
      (∀ j : Fin n, j ≠ j₀ → c₂.coord j = c₁.coord j) ∧
      (∀ i : ℕ, ∀ hi : i < N.length,
        (γ i = none → restrictIdeal (N[i]'hi) V = ⊤) ∧
          ∀ j : Fin n, γ i = some j → restrictIdeal (N[i]'hi) V = c₁.coordIdeal {j}) ∧
      (∀ i i' : ℕ, i < N.length → i' < N.length → ∀ j : Fin n,
        γ i = some j → γ i' = some j → i = i') ∧
      (∀ i : ℕ, γ i ≠ some j₀) := by
  classical
  have hxH₁ : x ∈ H₁.support := hadm₁.orderAtLeastLocus_subset_support hμ hx
  have hxH₂ : x ∈ H₂.support := hadm₂.orderAtLeastLocus_subset_support hμ hx
  obtain ⟨U₁, hU₁, hxU₁, hcase₁⟩ := (isMaxContactHypersurface_iff k p A μ H₁).mp hadm₁ x
  obtain ⟨n₁, d₁, i₁, hH₁U₁, hmc₁⟩ :
      ∃ (n : ℕ) (c : EtaleChart p U₁ n) (j : Fin n),
        restrictIdeal H₁ U₁ = c.coordIdeal {j} ∧ IsMaxContactCoord k p A μ c j := by
    rcases hcase₁ with ⟨hdisj, -⟩ | hc
    · exact absurd hxU₁ (Set.disjoint_left.mp hdisj hx)
    · exact hc
  obtain ⟨U₂, hU₂, hxU₂, hcase₂⟩ := (isMaxContactHypersurface_iff k p A μ H₂).mp hadm₂ x
  obtain ⟨n₂, d₂, i₂, hH₂U₂, hmc₂⟩ :
      ∃ (n : ℕ) (c : EtaleChart p U₂ n) (j : Fin n),
        restrictIdeal H₂ U₂ = c.coordIdeal {j} ∧ IsMaxContactCoord k p A μ c j := by
    rcases hcase₂ with ⟨hdisj, -⟩ | hc
    · exact absurd hxU₂ (Set.disjoint_left.mp hdisj hx)
    · exact hc
  have hM₁ : H₁.ideal ⟨U₁, hU₁⟩ ≤ (maxContactIdeal k p A μ).ideal ⟨U₁, hU₁⟩ := by
    have h1 : H₁.ideal ⟨U₁, hU₁⟩
        = Ideal.span (d₁.coord '' ((({i₁} : Finset (Fin n₁))) : Set (Fin n₁))) :=
      d₁.ideal_eq_span_coord hU₁ H₁ {i₁} hH₁U₁
    rw [h1, Finset.coe_singleton, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact (isMaxContactCoord_iff_coord_mem k p A μ hU₁ d₁ i₁).mp hmc₁
  have hM₂ : H₂.ideal ⟨U₂, hU₂⟩ ≤ (maxContactIdeal k p A μ).ideal ⟨U₂, hU₂⟩ := by
    have h1 : H₂.ideal ⟨U₂, hU₂⟩
        = Ideal.span (d₂.coord '' ((({i₂} : Finset (Fin n₂))) : Set (Fin n₂))) :=
      d₂.ideal_eq_span_coord hU₂ H₂ {i₂} hH₂U₂
    rw [h1, Finset.coe_singleton, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact (isMaxContactCoord_iff_coord_mem k p A μ hU₂ d₂ i₂).mp hmc₂
  have hsnc₁' := (inStrictNormalCrossingPosition_iff p (H₁ :: N)).mp hsnc₁
  have hsnc₂' := (inStrictNormalCrossingPosition_iff p (H₂ :: N)).mp hsnc₂
  have hcart₂ : Blowup.IsLocallyGeneratedByNonZeroDivisor H₂ :=
    ((isSmoothDivisor_iff p H₂).mp (hsnc₂'.1 H₂ (by simp))).1
  obtain ⟨⟨W₂, hW₂⟩, f₂, hxW₂, -, hf₂span⟩ := hcart₂ x
  obtain ⟨W, hxW, m₀, c₀, a, hainj, hanone, hasome⟩ := (hsnc₁'.2 x).exists_etaleChart
  obtain ⟨V₀, hV₀b, hxV₀, hV₀W⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxW
  have hV₀ : IsAffineOpen V₀ := hV₀b
  have hdesc0 : ∀ i : ℕ, ∀ hi : i < (H₁ :: N).length,
      (a i = none → restrictIdeal ((H₁ :: N)[i]'hi) V₀ = ⊤) ∧
        ∀ j : Fin m₀, a i = some j →
          restrictIdeal ((H₁ :: N)[i]'hi) V₀ = (c₀.restrict hV₀W).coordIdeal {j} := by
    intro i hi
    refine ⟨fun hn => restrictIdeal_eq_top_of_le _ hV₀W (hanone i hi hn), ?_⟩
    intro j hj
    exact restrictIdeal_eq_restrict_coordIdeal_of_le hV₀W c₀ _ {j} (hasome i hi j hj)
  have hinj0 : ∀ i i' : ℕ, i < (H₁ :: N).length → i' < (H₁ :: N).length →
      ∀ j : Fin m₀, a i = some j → a i' = some j → i = i' := by
    intro i i' hi hi' j h1 h2
    exact hainj i hi i' hi' j h1 h2
  obtain ⟨U', hU', hxU', n', c', a', hdesc', hinj', hprime'⟩ :=
    exists_etaleChart_coord_mem_primeIdealOf (H₁ :: N) x V₀ hV₀ hxV₀ (c₀.restrict hV₀W) a hdesc0 hinj0
  have hlt0 : 0 < (H₁ :: N).length := by simp
  obtain ⟨j₀, hj₀⟩ : ∃ t : Fin n', a' 0 = some t := by
    cases h0 : a' 0 with
    | none =>
      exfalso
      have htop := (hdesc' 0 hlt0).1 h0
      simp only [List.getElem_cons_zero] at htop
      exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top H₁ U' htop x hxU' hxH₁
    | some t => exact ⟨t, rfl⟩
  have hH₁U' : restrictIdeal H₁ U' = c'.coordIdeal {j₀} := by
    have h1 := (hdesc' 0 hlt0).2 j₀ hj₀
    simpa only [List.getElem_cons_zero] using h1
  obtain ⟨γ, hγval, hγnone⟩ :
      ∃ γ : ℕ → Option (Fin n'),
        (∀ i : ℕ, i < N.length → γ i = a' (i + 1)) ∧
        (∀ i : ℕ, ¬ i < N.length → γ i = none) :=
    ⟨fun i => if i < N.length then a' (i + 1) else none, fun i hi => if_pos hi,
      fun i hi => if_neg hi⟩
  have hγinj : LabelingInjective γ N.length := by
    intro i i' hi hi' j hj hj'
    rw [hγval i hi] at hj
    rw [hγval i' hi'] at hj'
    have h1 : i + 1 < (H₁ :: N).length := by
      simp only [List.length_cons]
      omega
    have h2 : i' + 1 < (H₁ :: N).length := by
      simp only [List.length_cons]
      omega
    have h3 := hinj' (i + 1) (i' + 1) h1 h2 j hj hj'
    omega
  have hγj₀ : ∀ i : ℕ, γ i ≠ some j₀ := by
    intro i hcon
    by_cases hi : i < N.length
    · rw [hγval i hi] at hcon
      have h1 : i + 1 < (H₁ :: N).length := by
        simp only [List.length_cons]
        omega
      have h3 := hinj' (i + 1) 0 h1 hlt0 j₀ hcon hj₀
      omega
    · rw [hγnone i hi] at hcon
      exact Option.some_ne_none j₀ hcon.symm
  have hlabU' : IsCoordLabeling c' γ N := by
    intro i hi
    have hiE : i + 1 < (H₁ :: N).length := by
      simp only [List.length_cons]
      omega
    have hget : (H₁ :: N)[i + 1]'hiE = N[i]'hi := by simp
    refine ⟨?_, ?_⟩
    · intro hnone
      have ha' : a' (i + 1) = none := by
        rw [← hγval i hi]
        exact hnone
      have htop := (hdesc' (i + 1) hiE).1 ha'
      rw [hget] at htop
      exact htop
    · intro j hj
      have ha' : a' (i + 1) = some j := by
        rw [← hγval i hi]
        exact hj
      have h2 := (hdesc' (i + 1) hiE).2 j ha'
      rw [hget] at h2
      exact h2
  have hxN : ∀ i : ℕ, ∀ hi : i < N.length, ∀ j : Fin n',
      γ i = some j → x ∈ (N[i]'hi).support := by
    intro i hi j hj
    have hiE : i + 1 < (H₁ :: N).length := by
      simp only [List.length_cons]
      omega
    have ha' : a' (i + 1) = some j := by
      rw [← hγval i hi]
      exact hj
    have h2 := (hlabU' i hi).2 j hj
    have hideal : (N[i]'hi).ideal ⟨U', hU'⟩ = Ideal.span {c'.coord j} := by
      have h3 := c'.ideal_eq_span_coord hU' (N[i]'hi) {j} h2
      rwa [Finset.coe_singleton, Set.image_singleton] at h3
    refine mem_support_of_ideal_le_primeIdealOf (N[i]'hi) hU' hxU' ?_
    rw [hideal, Ideal.span_le, Set.singleton_subset_iff]
    exact hprime' (i + 1) hiE j ha'
  obtain ⟨V, hVb, hxV, hVΩ⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ U' ⊓ U₁ ⊓ U₂ ⊓ W₂ from ⟨⟨⟨hxU', hxU₁⟩, hxU₂⟩, hxW₂⟩)
  have hV : IsAffineOpen V := hVb
  have hVU' : V ≤ U' := le_trans hVΩ (le_trans inf_le_left (le_trans inf_le_left inf_le_left))
  have hVU₁ : V ≤ U₁ := le_trans hVΩ (le_trans inf_le_left (le_trans inf_le_left inf_le_right))
  have hVU₂ : V ≤ U₂ := le_trans hVΩ (le_trans inf_le_left inf_le_right)
  have hVW₂ : V ≤ W₂ := le_trans hVΩ inf_le_right
  have hH₁V : restrictIdeal H₁ V = (c'.restrict hVU').coordIdeal {j₀} :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU' c' H₁ {j₀} hH₁U'
  have hlab : IsCoordLabeling (c'.restrict hVU') γ N := by
    intro i hi
    refine ⟨?_, ?_⟩
    · intro hnone
      exact restrictIdeal_eq_top_of_le (N[i]'hi) hVU' ((hlabU' i hi).1 hnone)
    · intro j hj
      exact restrictIdeal_eq_restrict_coordIdeal_of_le hVU' c' (N[i]'hi) {j} ((hlabU' i hi).2 j hj)
  obtain ⟨g, hg⟩ : ∃ g : Γ(X, V), H₂.ideal ⟨V, hV⟩ = Ideal.span {g} := by
    refine ⟨(X.presheaf.map (homOfLE hVW₂).op).hom f₂, ?_⟩
    have h2 := ideal_eq_span_image_map_of_le H₂ hW₂ hV hVW₂ ({f₂} : Set Γ(X, W₂)) hf₂span
    rwa [Set.image_singleton] at h2
  obtain ⟨jd, hjdlab, hjdpd⟩ :=
    exists_unlabeled_index_partialDeriv_notMem_primeIdealOf hV (c'.restrict hVU') hxV N γ
      H₂ g hlab hγinj (hsnc₂'.2 x) hg hxH₂ hxN
  have hjdpd' :
      chartPartialDeriv hV (c'.restrict hVU') jd g ∉ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := hjdpd
  obtain ⟨c'', hcj₀, hclab, hpd⟩ : ∃ c'' : EtaleChart p V n',
      c''.coord j₀ = (c'.restrict hVU').coord j₀ ∧
      (∀ j : Fin n', (∃ i : ℕ, i < N.length ∧ γ i = some j) →
        c''.coord j = (c'.restrict hVU').coord j) ∧
      chartPartialDeriv hV c'' j₀ g ∉ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    by_cases h0 : chartPartialDeriv hV (c'.restrict hVU') j₀ g ∈
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
    · have hne : j₀ ≠ jd := by
        intro hh
        rw [hh] at h0
        exact hjdpd' h0
      obtain ⟨c'', -, hcother, hderiv, -⟩ :=
        exists_etaleChart_coord_add_smul_chartPartialDeriv hV (c'.restrict hVU') j₀ jd hne (1 : k)
      refine ⟨c'', hcother j₀ hne, ?_, ?_⟩
      · rintro j ⟨i, hi, hγi⟩
        refine hcother j ?_
        intro hjd
        exact hjdlab i hi (by rw [hγi, hjd])
      · rw [hderiv g, map_one, one_mul]
        intro hmem
        apply hjdpd'
        have heq : chartPartialDeriv hV (c'.restrict hVU') jd g
            = chartPartialDeriv hV (c'.restrict hVU') j₀ g
              - (chartPartialDeriv hV (c'.restrict hVU') j₀ g
                 - chartPartialDeriv hV (c'.restrict hVU') jd g) := by ring
        rw [heq]
        exact Submodule.sub_mem _ h0 hmem
    · exact ⟨c'.restrict hVU', rfl, fun j _ => rfl, h0⟩
  have hH₁V'' : restrictIdeal H₁ V = c''.coordIdeal {j₀} :=
    restrictIdeal_eq_coordIdeal_of_coord_eq_consolidated290 hV (c'.restrict hVU') c'' j₀ hcj₀ H₁ hH₁V
  have hlab'' : IsCoordLabeling c'' γ N := by
    intro i hi
    refine ⟨(hlab i hi).1, ?_⟩
    intro j hj
    exact restrictIdeal_eq_coordIdeal_of_coord_eq_consolidated290 hV (c'.restrict hVU') c'' j
      (hclab j ⟨i, hi, hj⟩) (N[i]'hi) ((hlab i hi).2 j hj)
  obtain ⟨V', hV', hV'V, hxV', c₂, hc₂j₀, hc₂other⟩ :=
    exists_etaleChart_update_coord_of_partialDeriv_notMem hV c'' hxV j₀ g hpd
  have hH₁V' : restrictIdeal H₁ V' = (c''.restrict hV'V).coordIdeal {j₀} :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hV'V c'' H₁ {j₀} hH₁V''
  have hH₁id : H₁.ideal ⟨V', hV'⟩ = Ideal.span {(c''.restrict hV'V).coord j₀} := by
    have h1 := (c''.restrict hV'V).ideal_eq_span_coord hV' H₁ {j₀} hH₁V'
    rwa [Finset.coe_singleton, Set.image_singleton] at h1
  have hgV' : H₂.ideal ⟨V', hV'⟩ = Ideal.span {c₂.coord j₀} := by
    have h2 := ideal_eq_span_image_map_of_le H₂ hV hV' hV'V ({g} : Set Γ(X, V)) hg
    rw [Set.image_singleton] at h2
    rw [h2, hc₂j₀]
  have hH₂V' : restrictIdeal H₂ V' = c₂.coordIdeal {j₀} := by
    refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV' c₂ H₂ {j₀} ?_
    rw [hgV', Finset.coe_singleton, Set.image_singleton]
  have hmcc₁ : IsMaxContactCoord k p A μ (c''.restrict hV'V) j₀ := by
    rw [isMaxContactCoord_iff_coord_mem k p A μ hV' (c''.restrict hV'V) j₀]
    have h1 : H₁.ideal ⟨V', hV'⟩ ≤ (maxContactIdeal k p A μ).ideal ⟨V', hV'⟩ :=
      ideal_le_of_ideal_le_of_le_consolidated290 k p H₁ (maxContactIdeal k p A μ) hU₁ hV'
        (le_trans hV'V hVU₁) hM₁
    refine h1 ?_
    rw [hH₁id]
    exact Ideal.mem_span_singleton_self _
  have hmcc₂ : IsMaxContactCoord k p A μ c₂ j₀ := by
    rw [isMaxContactCoord_iff_coord_mem k p A μ hV' c₂ j₀]
    have h1 : H₂.ideal ⟨V', hV'⟩ ≤ (maxContactIdeal k p A μ).ideal ⟨V', hV'⟩ :=
      ideal_le_of_ideal_le_of_le_consolidated290 k p H₂ (maxContactIdeal k p A μ) hU₂ hV'
        (le_trans hV'V hVU₂) hM₂
    refine h1 ?_
    rw [hgV']
    exact Ideal.mem_span_singleton_self _
  have hgerm₁ : (X.presheaf.germ V' x hxV').hom ((c''.restrict hV'V).coord j₀)
      ∈ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) := by
    have hmem : (c''.restrict hV'V).coord j₀ ∈ H₁.ideal ⟨V', hV'⟩ := by
      rw [hH₁id]
      exact Ideal.mem_span_singleton_self _
    have h2 := germ_mem_stalkIdeal H₁ x ⟨V', hV'⟩ hxV' hmem
    exact (mem_support_iff_stalkIdeal_le_maximalIdeal H₁ x).mp hxH₁ h2
  have hgerm₂ : (X.presheaf.germ V' x hxV').hom (c₂.coord j₀)
      ∈ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) := by
    have hmem : c₂.coord j₀ ∈ H₂.ideal ⟨V', hV'⟩ := by
      rw [hgV']
      exact Ideal.mem_span_singleton_self _
    have h2 := germ_mem_stalkIdeal H₂ x ⟨V', hV'⟩ hxV' hmem
    exact (mem_support_iff_stalkIdeal_le_maximalIdeal H₂ x).mp hxH₂ h2
  have hcoords : ∀ j : Fin n', j ≠ j₀ → c₂.coord j = (c''.restrict hV'V).coord j := by
    intro j hj
    rw [hc₂other j hj, EtaleChart.coord_restrict c'' hV'V j]
  have hlabV' : ∀ i : ℕ, ∀ hi : i < N.length,
      (γ i = none → restrictIdeal (N[i]'hi) V' = ⊤) ∧
        ∀ j : Fin n', γ i = some j →
          restrictIdeal (N[i]'hi) V' = (c''.restrict hV'V).coordIdeal {j} := by
    intro i hi
    refine ⟨fun hn => restrictIdeal_eq_top_of_le (N[i]'hi) hV'V ((hlab'' i hi).1 hn), ?_⟩
    intro j hj
    exact restrictIdeal_eq_restrict_coordIdeal_of_le hV'V c'' (N[i]'hi) {j} ((hlab'' i hi).2 j hj)
  exact ⟨V', hV', hxV', n', c''.restrict hV'V, c₂, γ, j₀, hH₁V', hH₂V', hmcc₁, hmcc₂,
    hgerm₁, hgerm₂, hcoords, hlabV', hγinj, hγj₀⟩

end

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafLcm
section



private theorem dvd_foldr_lcm_consolidated299 : ∀ (l : List ℕ) (w : ℕ), w ∈ l → w ∣ l.foldr Nat.lcm 1
  | [], w, h => absurd h (by simp)
  | (a :: l), w, h => by
      show w ∣ Nat.lcm a (l.foldr Nat.lcm 1)
      rcases List.mem_cons.mp h with h | h
      · subst h
        exact Nat.dvd_lcm_left _ _
      · exact dvd_trans (dvd_foldr_lcm_consolidated299 l w h) (Nat.dvd_lcm_right _ _)

theorem dvd_lcmUpTo (m w : ℕ) (hw : 1 ≤ w) (hwm : w ≤ m) : w ∣ lcmUpTo m :=
  dvd_foldr_lcm_consolidated299 _ w (List.mem_range'_1.mpr ⟨hw, by omega⟩)

private theorem foldr_lcm_consecutive_pos_consolidated299 :
    ∀ (n s : ℕ), 0 < s → 0 < (List.range' s n).foldr Nat.lcm 1
  | 0, s, _ => Nat.one_pos
  | (n + 1), s, hs => by
      have h := foldr_lcm_consecutive_pos_consolidated299 n (s + 1) (by omega)
      show 0 < Nat.lcm s ((List.range' (s + 1) n).foldr Nat.lcm 1)
      exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))

theorem lcmUpTo_pos (m : ℕ) : 0 < lcmUpTo m :=
  foldr_lcm_consecutive_pos_consolidated299 m 1 Nat.one_pos

private theorem le_of_not_natCast_succ_le_consolidated299 {a : ℕ∞} {s : ℕ}
    (h : ¬ (((s + 1 : ℕ)) : ℕ∞) ≤ a) : a ≤ (s : ℕ∞) := by
  rcases eq_or_ne a ⊤ with rfl | hne
  · exact absurd le_top h
  · obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hne
    have hn : ¬ (s + 1 ≤ n) := fun hh => h (by exact_mod_cast hh)
    have hns : n ≤ s := by omega
    exact_mod_cast hns

theorem tunedSheaf_mul_eq_add : TunedSheafMulEqAdd.{u} := by
  intro k hk hchar hnoeth X p hsmooth hft I m hm hmax r t ht
  refine Scheme.IdealSheafData.ext (funext ?_)
  intro U
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, tunedSheaf_ideal, tunedSheaf_ideal,
    tunedSheaf_ideal]
  exact @tunedIdeal_mul_eq_tunedIdeal_add k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m (lcmUpTo m)
    (lcmUpTo_pos m) (fun w hw1 hw2 => dvd_lcmUpTo m w hw1 hw2) r t ht

theorem tunedSheaf_pow_eq_mul : TunedSheafPowEqMul.{u} := by
  intro k hk hchar hnoeth X p hsmooth hft I m hm hmax r hr j hj
  refine Scheme.IdealSheafData.ext (funext ?_)
  intro U
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, tunedSheaf_ideal, tunedSheaf_ideal]
  exact @tunedIdeal_pow_eq_tunedIdeal_mul k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m (lcmUpTo m)
    (lcmUpTo_pos m) (fun w hw1 hw2 => dvd_lcmUpTo m w hw1 hw2) r hr j hj

theorem isDerivBalanced_tunedSheaf_mul_lcmUpTo : IsDerivBalancedTunedSheafMulLcm.{u} := by
  intro k hk hchar hnoeth X p hsmooth hft I m hm hmax r hr i hi
  refine Scheme.IdealSheafData.le_def.mpr ?_
  intro U
  rw [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Pi.pow_apply, derivIdealSheafIterate_ideal, tunedSheaf_ideal]
  exact @derivIdealIterate_tunedIdeal_pow_le k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m
    (lcmUpTo m) (lcmUpTo_pos m) (fun w hw1 hw2 => dvd_lcmUpTo m w hw1 hw2) r hr i hi

theorem orderAtLeastLocus_tunedSheaf_eq_and_order_le : CoSupportTunedSheafEqAndOrderLE.{u} := by
  intro k hk hchar hnoeth X p hsmooth hft I m hm hmax s hs
  have hC := maxContactIdealTunedSheafEq k X p I m hm hmax s hs
  refine ⟨?_, ?_⟩
  · have hA := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p (tunedSheaf k p I m s) hs
    have hB := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm
    rw [← hA, hC]
    exact hB
  · intro x
    have hordI : orderAt I x ≤ (m : ℕ∞) := hmax.orderLE x
    have hx2 : x ∉ orderAtLeastLocus I (m + 1) := by
      rw [mem_orderAtLeastLocus_iff]
      intro hcon
      have hle := le_trans hcon hordI
      have hmm : m + 1 ≤ m := by exact_mod_cast hle
      omega
    have hcs : orderAtLeastLocus (derivIdealSheafIterate k p (m - 1) I) ((m + 1) - (m - 1))
        = orderAtLeastLocus I (m + 1) := orderAtLeastLocus_derivIdealSheafIterate k p I (by omega)
    have ha : ¬ (((2 : ℕ) : ℕ∞) ≤ orderAt (derivIdealSheafIterate k p (m - 1) I) x) := by
      rw [← mem_orderAtLeastLocus_iff]
      have h2 : (2 : ℕ) = (m + 1) - (m - 1) := by omega
      rw [h2, hcs]
      exact hx2
    refine le_of_not_natCast_succ_le_consolidated299 ?_
    intro hcon
    have he : 2 + (s - 1) = s + 1 := by omega
    have h1 : (((2 + (s - 1) : ℕ)) : ℕ∞) ≤ orderAt (tunedSheaf k p I m s) x := by
      rw [he]
      exact hcon
    have h2 := le_orderAt_derivIdealSheafIterate k p (tunedSheaf k p I m s) x 2 (s - 1) h1
    rw [hC] at h2
    exact ha h2

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactEtaleUniqueness
section

open TopologicalSpace

section

private theorem comap_comp_eq_of_comap_comap_eq_consolidated306 {A B C : Scheme.{u}} (ι : A ⟶ B) (F G : B ⟶ C)
    (I J : C.IdealSheafData) (h : (I.comap F).comap ι = (J.comap G).comap ι) :
    I.comap (ι ≫ F) = J.comap (ι ≫ G) := by
  have hF : I.comap (ι ≫ F) = (I.comap F).comap ι := by
    simp [Scheme.IdealSheafData.comap_comp]
  have hG : J.comap (ι ≫ G) = (J.comap G).comap ι := by
    simp [Scheme.IdealSheafData.comap_comp]
  rw [hF, hG]
  exact h

private theorem comap_comp_ι_eq_comap_restrictIdeal_consolidated306 {Y Z : Scheme.{u}} (J : Y.IdealSheafData)
    (U : Y.Opens) (g : Z ⟶ U.toScheme) : J.comap (g ≫ U.ι) = (restrictIdeal J U).comap g := by
  show J.comap (g ≫ U.ι) = (J.comap U.ι).comap g
  simp [Scheme.IdealSheafData.comap_comp]

private theorem exists_subscheme_comap_lift_consolidated306 {A B : Scheme.{u}} (f : A ⟶ B) (I : B.IdealSheafData) :
    ∃ θ : (I.comap f).subscheme ⟶ I.subscheme,
      θ ≫ I.subschemeι = (I.comap f).subschemeι ≫ f := by
  have h2 : Scheme.Hom.ker I.subschemeι ≤
      Scheme.Hom.ker ((I.comap f).subschemeι ≫ f) := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι]
    exact Scheme.IdealSheafData.le_map_comap I f
  exact ⟨AlgebraicGeometry.IsClosedImmersion.lift I.subschemeι _ h2,
    AlgebraicGeometry.IsClosedImmersion.lift_fac I.subschemeι _ h2⟩

private theorem range_base_subset_range_preimage_ι_consolidated306 {T W Z S : Scheme.{u}} (tι : T ⟶ W) (ιZ : W ⟶ Z)
    (θ : T ⟶ S) (σ : S ⟶ Z) (hθ : θ ≫ σ = tι ≫ ιZ) (Wop : Z.Opens)
    (hsub : Set.range ⇑ιZ.base ⊆ (Wop : Set ↥Z)) :
    Set.range ⇑θ.base ⊆ Set.range ⇑((σ ⁻¹ᵁ Wop).ι).base := by
  rw [Scheme.Opens.range_ι]
  rintro z ⟨y, rfl⟩
  show σ.base (θ.base y) ∈ Wop
  have hb : (θ ≫ σ).base y = (tι ≫ ιZ).base y := by rw [hθ]
  have hb2 : σ.base (θ.base y) = ιZ.base (tι.base y) := hb
  rw [hb2]
  exact hsub ⟨tι.base y, rfl⟩

private theorem comp_eq_of_lift_comp_eq_consolidated306 {T W Z S S' Q : Scheme.{u}}
    (tι : T ⟶ W) (ιZ : W ⟶ Z) (σ : S ⟶ Z) (j : S' ⟶ S) (θ : T ⟶ S) (δ : T ⟶ S')
    (F G : Z ⟶ Q) (hθ : θ ≫ σ = tι ≫ ιZ) (hδ : δ ≫ j = θ)
    (heq : j ≫ σ ≫ F = j ≫ σ ≫ G) :
    tι ≫ ιZ ≫ F = tι ≫ ιZ ≫ G := by
  have h1 : tι ≫ ιZ ≫ F = δ ≫ j ≫ σ ≫ F := by
    rw [← Category.assoc tι ιZ F, ← hθ, ← hδ]
    simp only [Category.assoc]
  have h2 : tι ≫ ιZ ≫ G = δ ≫ j ≫ σ ≫ G := by
    rw [← Category.assoc tι ιZ G, ← hθ, ← hδ]
    simp only [Category.assoc]
  rw [h1, h2, heq]

section
variable (k : Type u) [Field k] [CharZero k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]

theorem nonempty_etaleMaxContactComparison (A : P.IdealSheafData) {μ : ℕ} (hμ : 1 ≤ μ) (hinv : IsMaxContactInvariant k p A μ)
    (N : List P.IdealSheafData) (H₁ H₂ : P.IdealSheafData)
    (hsnc₁ : InStrictNormalCrossingPosition p (H₁ :: N)) (hsnc₂ : InStrictNormalCrossingPosition p (H₂ :: N))
    (hadm₁ : IsMaxContactHypersurface k p A μ H₁)
    (hadm₂ : IsMaxContactHypersurface k p A μ H₂)
    (pt : P) (hpt : pt ∈ orderAtLeastLocus A μ) :
    Nonempty (EtaleMaxContactComparison k p A μ N H₁ H₂ pt) := by
  obtain ⟨V, hVaff, hptV, n, c₁, c₂, γ, j₀, hH₁, hH₂, hmc₁, hmc₂, hgm₁, hgm₂, hco, hNγ,
      _, hγne⟩ :=
    exists_common_charts_of_isMaxContactHypersurface A hμ N H₁ H₂ hsnc₁ hsnc₂ hadm₁ hadm₂ pt hpt
  have hlftF : LocallyOfFiniteType (chartPullbackFst c₁ c₂ ≫ p) := inferInstance
  have hln1 : IsLocallyNoetherian (chartPullback c₁ c₂) :=
    LocallyOfFiniteType.isLocallyNoetherian (f := chartPullbackFst c₁ c₂ ≫ p)
  have hln2 : IsLocallyNoetherian
      ((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).subscheme := by
    have : LocallyOfFiniteType
        (((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).subschemeι ≫
          (chartPullbackFst c₁ c₂ ≫ p)) := inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian
      (f := ((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).subschemeι ≫
        (chartPullbackFst c₁ c₂ ≫ p))
  obtain ⟨hagree, Wop, hptW, hstalk, _, heqmor, hHcomap, hcoordS⟩ :=
    exists_opens_chartPullback_eq_of_mem_maxContactIdeal k p A hμ hinv hVaff c₁ c₂ j₀
      (fun i hi => (hco i hi).symm) pt hptV
      ((isMaxContactCoord_iff_coord_mem k p A μ hVaff c₁ j₀).mp hmc₁)
      ((isMaxContactCoord_iff_coord_mem k p A μ hVaff c₂ j₀).mp hmc₂)
      hgm₁ hgm₂ (mem_support_maxContactIdeal_of_mem_orderAtLeastLocus k p A hμ hpt)
  obtain ⟨U0, hU0⟩ : ∃ U0 : (chartPullback c₁ c₂).affineOpens,
      chartPullbackPoint c₁ c₂ pt hptV hagree ∈ U0.1 := by
    have hx : chartPullbackPoint c₁ c₂ pt hptV hagree ∈
        (⨆ U : (chartPullback c₁ c₂).affineOpens, (U : (chartPullback c₁ c₂).Opens)) := by
      rw [AlgebraicGeometry.iSup_affineOpens_eq_top (chartPullback c₁ c₂)]
      trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨U, hU⟩
  obtain ⟨g, hgle, hw0W'⟩ :=
    U0.2.exists_basicOpen_le (⟨chartPullbackPoint c₁ c₂ pt hptV hagree, hptW⟩ : Wop) hU0
  have hW'aff : IsAffineOpen ((chartPullback c₁ c₂).basicOpen g) :=
    ((chartPullback c₁ c₂).affineBasicOpen g).2
  have hetale1 : Etale
      (((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂) := inferInstance
  have hetale2 : Etale
      (((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackSnd c₁ c₂) := inferInstance
  have hsmooth1 : Smooth
      (((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂) := inferInstance
  have hlft1 : LocallyOfFiniteType
      ((((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂) ≫ p) := inferInstance
  have e1 : H₁.comap (chartPullbackFst c₁ c₂)
      = (c₁.coordIdeal {j₀}).comap (Limits.pullback.fst c₁.map c₂.map) :=
    (comap_comp_ι_eq_comap_restrictIdeal_consolidated306 H₁ V (Limits.pullback.fst c₁.map c₂.map)).trans
      (congrArg (fun K : V.toScheme.IdealSheafData =>
        K.comap (Limits.pullback.fst c₁.map c₂.map)) hH₁)
  have e2 : H₂.comap (chartPullbackSnd c₁ c₂)
      = (c₂.coordIdeal {j₀}).comap (Limits.pullback.snd c₁.map c₂.map) :=
    (comap_comp_ι_eq_comap_restrictIdeal_consolidated306 H₂ V (Limits.pullback.snd c₁.map c₂.map)).trans
      (congrArg (fun K : V.toScheme.IdealSheafData =>
        K.comap (Limits.pullback.snd c₁.map c₂.map)) hH₂)
  have e3 : H₁.comap (chartPullbackFst c₁ c₂) = H₂.comap (chartPullbackSnd c₁ c₂) :=
    e1.trans (hHcomap.trans e2.symm)
  refine ⟨{ W := ((chartPullback c₁ c₂).basicOpen g).toScheme
          , f₁ := ((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂
          , f₂ := ((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackSnd c₁ c₂
          , w := ⟨chartPullbackPoint c₁ c₂ pt hptV hagree, hw0W'⟩
          , isAffine := hW'aff
          , etale_f₁ := hetale1
          , etale_f₂ := hetale2
          , lft_f₁ := hlft1
          , base_f₁ := ?_
          , base_f₂ := ?_
          , comap_A := ?_
          , comap_H := ?_
          , comap_N := ?_
          , comp_p := ?_
          , maxContact_comp := ?_ }⟩
  · exact chartPullbackFst_base_chartPullbackPoint c₁ c₂ pt hptV hagree
  · exact chartPullbackSnd_base_chartPullbackPoint c₁ c₂ pt hptV hagree
  · refine comap_comp_eq_of_comap_comap_eq_consolidated306 ((chartPullback c₁ c₂).basicOpen g).ι (chartPullbackFst c₁ c₂)
      (chartPullbackSnd c₁ c₂) A A ?_
    exact restrictIdeal_eq_of_stalkIdeal_eq _ _ ((chartPullback c₁ c₂).basicOpen g)
      (fun y hy => hstalk y (hgle hy))
  · refine comap_comp_eq_of_comap_comap_eq_consolidated306 ((chartPullback c₁ c₂).basicOpen g).ι (chartPullbackFst c₁ c₂)
      (chartPullbackSnd c₁ c₂) H₁ H₂ ?_
    exact congrArg (fun J : (chartPullback c₁ c₂).IdealSheafData =>
      J.comap ((chartPullback c₁ c₂).basicOpen g).ι) e3
  · intro J hJ
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hJ
    have key : (N[i]'hi).comap (chartPullbackFst c₁ c₂) = (N[i]'hi).comap (chartPullbackSnd c₁ c₂) := by
      obtain ⟨hnone, hsome⟩ := hNγ i hi
      have h0F : (N[i]'hi).comap (chartPullbackFst c₁ c₂)
          = (restrictIdeal (N[i]'hi) V).comap (Limits.pullback.fst c₁.map c₂.map) :=
        comap_comp_ι_eq_comap_restrictIdeal_consolidated306 _ V _
      have h0G : (N[i]'hi).comap (chartPullbackSnd c₁ c₂)
          = (restrictIdeal (N[i]'hi) V).comap (Limits.pullback.snd c₁.map c₂.map) :=
        comap_comp_ι_eq_comap_restrictIdeal_consolidated306 _ V _
      rw [h0F, h0G]
      cases hγ : γ i with
      | none =>
        rw [hnone hγ, Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.comap_top]
      | some jj =>
        have hjj : jj ≠ j₀ := by
          intro h
          exact hγne i (by rw [hγ, h])
        have hnotmem : j₀ ∉ ({jj} : Finset (Fin n)) := by
          simp only [Finset.mem_singleton]
          exact fun h => hjj h.symm
        rw [hsome jj hγ, chartPullback_comap_coordIdeal_eq c₁ c₂ {jj}, hcoordS {jj} hnotmem]
    refine comap_comp_eq_of_comap_comap_eq_consolidated306 ((chartPullback c₁ c₂).basicOpen g).ι (chartPullbackFst c₁ c₂)
      (chartPullbackSnd c₁ c₂) (N[i]'hi) (N[i]'hi) ?_
    exact congrArg (fun J : (chartPullback c₁ c₂).IdealSheafData =>
      J.comap ((chartPullback c₁ c₂).basicOpen g).ι) key
  · have hcs := chartPullbackFst_comp_eq_chartPullbackSnd_comp c₁ c₂
    simp only [Category.assoc] at hcs ⊢
    rw [hcs]
  · have hNeq : maxContactIdeal k
          ((((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂) ≫ p)
          (A.comap (((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂)) μ
        = ((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).comap
            ((chartPullback c₁ c₂).basicOpen g).ι := by
      simp only [maxContactIdeal_eq_derivIdealSheafIterate]
      rw [derivIdealSheafIterate_comap k p
        (((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂) (μ - 1) A]
      simp [Scheme.IdealSheafData.comap_comp]
    rw [hNeq]
    obtain ⟨θ, hθ⟩ :=
      exists_subscheme_comap_lift_consolidated306 ((chartPullback c₁ c₂).basicOpen g).ι
        ((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂))
    have hsub : Set.range ⇑(((chartPullback c₁ c₂).basicOpen g).ι).base ⊆
        (Wop : Set ↥(chartPullback c₁ c₂)) := by
      rw [Scheme.Opens.range_ι]
      intro z hz
      exact hgle hz
    have hrange := range_base_subset_range_preimage_ι_consolidated306
      ((((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).comap
        ((chartPullback c₁ c₂).basicOpen g).ι).subschemeι)
      ((chartPullback c₁ c₂).basicOpen g).ι θ
      (((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).subschemeι) hθ Wop hsub
    exact comp_eq_of_lift_comp_eq_consolidated306 _ _ _
      ((((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).subschemeι ⁻¹ᵁ Wop).ι)
      θ (IsOpenImmersion.lift _ θ hrange) (chartPullbackFst c₁ c₂) (chartPullbackSnd c₁ c₂)
      hθ (IsOpenImmersion.lift_fac _ θ hrange) heqmor

theorem exists_etale_equalizing_isMaxContactHypersurface [QuasiCompact p]
    (A : P.IdealSheafData) {μ : ℕ} (hμ : 1 ≤ μ) (hinv : IsMaxContactInvariant k p A μ)
    (_horder : ∀ x : P, orderAt A x ≤ (μ : ℕ∞))
    (N : List P.IdealSheafData) (H₁ H₂ : P.IdealSheafData)
    (hsnc₁ : InStrictNormalCrossingPosition p (H₁ :: N)) (hsnc₂ : InStrictNormalCrossingPosition p (H₂ :: N))
    (hadm₁ : IsMaxContactHypersurface k p A μ H₁)
    (hadm₂ : IsMaxContactHypersurface k p A μ H₂) :
    ∃ (V : Scheme.{u}) (g₁ : V ⟶ P) (g₂ : V ⟶ P) (_ : Etale g₁) (_ : Etale g₂)
      (_ : QuasiCompact (g₁ ≫ p)) (hlft : LocallyOfFiniteType (g₁ ≫ p)),
      g₁ ≫ p = g₂ ≫ p ∧
      orderAtLeastLocus A μ ⊆ Set.range ⇑g₁.base ∧
      orderAtLeastLocus A μ ⊆ Set.range ⇑g₂.base ∧
      A.comap g₁ = A.comap g₂ ∧
      H₁.comap g₁ = H₂.comap g₂ ∧
      N.map (fun J => J.comap g₁) = N.map (fun J => J.comap g₂) ∧
      (@maxContactIdeal k _ _ V (g₁ ≫ p) hlft (A.comap g₁) μ).subschemeι ≫ g₁ =
        (@maxContactIdeal k _ _ V (g₁ ≫ p) hlft (A.comap g₁) μ).subschemeι ≫ g₂ :=
  exists_etale_maxContactIdeal_comparison k p A μ N H₁ H₂
    (fun pt hpt =>
      nonempty_etaleMaxContactComparison k p A hμ hinv N H₁ H₂ hsnc₁ hsnc₂ hadm₁ hadm₂ pt hpt)


end

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsEraseMember
section


section

private def natSuccAbove_consolidated180 (j i : ℕ) : ℕ := if i < j then i else i + 1

private theorem natSuccAbove_ne_consolidated180 (j i : ℕ) : natSuccAbove_consolidated180 j i ≠ j := by
  unfold natSuccAbove_consolidated180
  split_ifs with h <;> omega

private theorem natSuccAbove_inj_consolidated180 (j i i' : ℕ) (h : natSuccAbove_consolidated180 j i = natSuccAbove_consolidated180 j i') : i = i' := by
  unfold natSuccAbove_consolidated180 at h
  split_ifs at h <;> omega

private theorem getElem_eraseIdx_natSuccAbove_consolidated180 {α : Type u} (l : List α) (j i : ℕ)
    (hi : i < (l.eraseIdx j).length) (hs : natSuccAbove_consolidated180 j i < l.length) :
    (l.eraseIdx j)[i]'hi = l[natSuccAbove_consolidated180 j i]'hs := by
  unfold natSuccAbove_consolidated180 at hs ⊢
  rw [List.getElem_eraseIdx]
  split <;> simp [*]

private def complOrderEmbPreimage_consolidated180 (m : ℕ) (S : Finset (Fin m)) (s : Fin m) : Option (Fin (m - S.card)) :=
  if hs : s ∈ S then none else some (Classical.choose (exists_complOrderEmb_eq m S hs))

section
variable (m : ℕ) (S : Finset (Fin m)) (s : Fin m)

private theorem mem_of_complOrderEmbPreimage_eq_none_consolidated180 (h : complOrderEmbPreimage_consolidated180 m S s = none) : s ∈ S := by
  by_contra hs
  unfold complOrderEmbPreimage_consolidated180 at h
  rw [dif_neg hs] at h
  simp at h

private theorem complOrderEmb_of_complOrderEmbPreimage_eq_some_consolidated180 (u : Fin (m - S.card)) (h : complOrderEmbPreimage_consolidated180 m S s = some u) : complOrderEmb m S u = s := by
  by_cases hs : s ∈ S
  · exfalso
    unfold complOrderEmbPreimage_consolidated180 at h
    rw [dif_pos hs] at h
    simp at h
  · unfold complOrderEmbPreimage_consolidated180 at h
    rw [dif_neg hs] at h
    have hu : Classical.choose (exists_complOrderEmb_eq m S hs) = u := Option.some.inj h
    rw [← hu]
    exact Classical.choose_spec (exists_complOrderEmb_eq m S hs)


end

private def transportSuccAboveToCompl_consolidated180 {m : ℕ} (S : Finset (Fin m)) (j : ℕ) (a : ℕ → Option (Fin m))
    (i : ℕ) : Option (Fin (m - S.card)) :=
  (a (natSuccAbove_consolidated180 j i)).bind (complOrderEmbPreimage_consolidated180 m S)

section
variable {m : ℕ} (S : Finset (Fin m)) (j : ℕ) (a : ℕ → Option (Fin m)) (i : ℕ)

private theorem transportSuccAboveToCompl_eq_some_consolidated180 (u : Fin (m - S.card))
    (h : transportSuccAboveToCompl_consolidated180 S j a i = some u) : a (natSuccAbove_consolidated180 j i) = some (complOrderEmb m S u) := by
  rcases hs : a (natSuccAbove_consolidated180 j i) with _ | s
  · exfalso
    unfold transportSuccAboveToCompl_consolidated180 at h
    rw [hs] at h
    simp at h
  · have h' : complOrderEmbPreimage_consolidated180 m S s = some u := by
      unfold transportSuccAboveToCompl_consolidated180 at h
      rw [hs] at h
      exact h
    rw [complOrderEmb_of_complOrderEmbPreimage_eq_some_consolidated180 m S s u h']

private theorem transportSuccAboveToCompl_eq_none_consolidated180 (h : transportSuccAboveToCompl_consolidated180 S j a i = none) :
    a (natSuccAbove_consolidated180 j i) = none ∨ ∃ s, a (natSuccAbove_consolidated180 j i) = some s ∧ s ∈ S := by
  rcases hs : a (natSuccAbove_consolidated180 j i) with _ | s
  · exact Or.inl rfl
  · refine Or.inr ⟨s, rfl, ?_⟩
    have h' : complOrderEmbPreimage_consolidated180 m S s = none := by
      unfold transportSuccAboveToCompl_consolidated180 at h
      rw [hs] at h
      exact h
    exact mem_of_complOrderEmbPreimage_eq_none_consolidated180 m S s h'


end

theorem inStrictNormalCrossingPosition_of_forall_etaleChart {Y : Scheme.{u}} {k : Type u} [Field k]
    (q : Y ⟶ Spec (CommRingCat.of k)) (L : List Y.IdealSheafData)
    (h : ∀ x : ↥Y, ∃ (U : Y.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart q U m)
      (a : ℕ → Option (Fin m)),
      (∀ i < L.length, ∀ i' < L.length, ∀ t : Fin m, a i = some t → a i' = some t → i = i') ∧
      (∀ (i : ℕ) (hi : i < L.length), a i = none → restrictIdeal L[i] U = ⊤) ∧
      (∀ (i : ℕ) (hi : i < L.length) (t : Fin m),
        a i = some t → restrictIdeal L[i] U = c.coordIdeal {t})) :
    InStrictNormalCrossingPosition q L := by
  refine (inStrictNormalCrossingPosition_iff q L).mpr ⟨?_, fun x => inStrictNormalCrossingPositionAt_of_exists_etaleChart (h x)⟩
  intro D hD
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hD
  refine isSmoothDivisor_of_locally_coordIdeal _ ?_
  intro x
  obtain ⟨U, hxU, m, c, a, h1, h2, h3⟩ := h x
  refine ⟨U, hxU, m, c, ?_⟩
  rcases hai : a i with _ | t
  · exact Or.inl (h2 i hi hai)
  · exact Or.inr ⟨t, h3 i hi t hai⟩

section
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) (j : ℕ) (hj : j < E.length)
include hE hj

theorem exists_etaleChart_comap_subschemeι_eraseIdx (z : ↥((E[j]'hj).subscheme)) :
    ∃ (U : ((E[j]'hj).subscheme).Opens) (_ : z ∈ U) (m : ℕ)
      (c : EtaleChart ((E[j]'hj).subschemeι ≫ p) U m) (a : ℕ → Option (Fin m)),
      (∀ i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length,
        ∀ i' < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length,
        ∀ t : Fin m, a i = some t → a i' = some t → i = i') ∧
      (∀ (i : ℕ) (hi : i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length),
        a i = none →
          restrictIdeal (((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι)[i]) U = ⊤) ∧
      (∀ (i : ℕ) (hi : i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length)
        (t : Fin m), a i = some t →
          restrictIdeal (((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι)[i]) U =
            c.coordIdeal {t}) := by
  classical
  obtain ⟨-, hpos⟩ := (inStrictNormalCrossingPosition_iff p E).mp hE
  have hx : (E[j]'hj).subschemeι.base z ∈ (E[j]'hj).support := by
    have hmem : (E[j]'hj).subschemeι.base z ∈ Set.range (E[j]'hj).subschemeι.base :=
      Set.mem_range_self z
    simpa using hmem
  obtain ⟨U, hxU, m, c, a, h1, h2, h3⟩ := (hpos ((E[j]'hj).subschemeι.base z)).exists_etaleChart
  obtain ⟨V, hVB, hxV, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU
  have hV : IsAffineOpen V := hVB
  rcases haj : a j with _ | t
  · refine absurd hx ?_
    refine AlgebraicGeometry.Scheme.IdealSheafData.notMem_support_of_comap_ι_eq_top _ ?_ hxU
    rw [← restrictIdeal_eq_comap_ι]
    exact h2 j hj haj
  · have hzmem : z ∈ (E[j]'hj).subschemeι ⁻¹ᵁ V := hxV
    have h2V : ∀ (i : ℕ) (hi : i < E.length), a i = none → restrictIdeal (E[i]'hi) V = ⊤ :=
      fun i hi hn => restrictIdeal_eq_top_of_le _ hVU (h2 i hi hn)
    have h3V : ∀ (i : ℕ) (hi : i < E.length) (s : Fin m), a i = some s →
        restrictIdeal (E[i]'hi) V = (c.restrict hVU).coordIdeal {s} :=
      fun i hi s hsm => restrictIdeal_eq_restrict_coordIdeal_of_le hVU c (E[i]'hi) {s} (h3 i hi s hsm)
    have hZV : restrictIdeal (E[j]'hj) V = (c.restrict hVU).coordIdeal {t} := h3V j hj t haj
    have hlen : ∀ i, i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length →
        natSuccAbove_consolidated180 j i < E.length := by
      intro i hi
      rw [List.length_map] at hi
      have h0 := List.length_eraseIdx_add_one hj
      unfold natSuccAbove_consolidated180
      split_ifs with hc <;> omega
    have helem : ∀ (i : ℕ)
        (hi : i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length),
        ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι)[i]'hi =
          (E[natSuccAbove_consolidated180 j i]'(hlen i hi)).comap (E[j]'hj).subschemeι := by
      intro i hi
      have hi' : i < (E.eraseIdx j).length := by
        rw [List.length_map] at hi
        exact hi
      have he : (E.eraseIdx j)[i]'hi' = E[natSuccAbove_consolidated180 j i]'(hlen i hi) :=
        getElem_eraseIdx_natSuccAbove_consolidated180 E j i hi' (hlen i hi)
      rw [List.getElem_map]
      exact congrArg (fun D => D.comap (E[j]'hj).subschemeι) he
    refine ⟨(E[j]'hj).subschemeι ⁻¹ᵁ V, hzmem, m - ({t} : Finset (Fin m)).card,
      (c.restrict hVU).restrictToSubscheme hV (E[j]'hj) {t} hZV,
      transportSuccAboveToCompl_consolidated180 {t} j a, ?_, ?_, ?_⟩
    · intro i hi i' hi' u hu hu'
      exact natSuccAbove_inj_consolidated180 j i i'
        (h1 (natSuccAbove_consolidated180 j i) (hlen i hi) (natSuccAbove_consolidated180 j i') (hlen i' hi')
          (complOrderEmb m {t} u) (transportSuccAboveToCompl_eq_some_consolidated180 {t} j a i u hu)
          (transportSuccAboveToCompl_eq_some_consolidated180 {t} j a i' u hu'))
    · intro i hi hn
      rw [helem i hi]
      rcases transportSuccAboveToCompl_eq_none_consolidated180 {t} j a i hn with hnone | ⟨s, hsome, hsmem⟩
      · exact restrictIdeal_comap_subschemeι_eq_top (E[j]'hj) V _
          (h2V (natSuccAbove_consolidated180 j i) (hlen i hi) hnone)
      · exfalso
        have h0 : a (natSuccAbove_consolidated180 j i) = some t := by
          rw [hsome, Finset.mem_singleton.mp hsmem]
        exact natSuccAbove_ne_consolidated180 j i (h1 (natSuccAbove_consolidated180 j i) (hlen i hi) j hj t h0 haj)
    · intro i hi u hu
      rw [helem i hi]
      exact (c.restrict hVU).restrictToSubscheme_coordIdeal_singleton hV (E[j]'hj) {t} hZV u
        (E[natSuccAbove_consolidated180 j i]'(hlen i hi))
        (h3V (natSuccAbove_consolidated180 j i) (hlen i hi) (complOrderEmb m {t} u)
          (transportSuccAboveToCompl_eq_some_consolidated180 {t} j a i u hu))

theorem inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx :
    InStrictNormalCrossingPosition ((E[j]'hj).subschemeι ≫ p)
      ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι) :=
  inStrictNormalCrossingPosition_of_forall_etaleChart ((E[j]'hj).subschemeι ≫ p)
    ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι)
    (exists_etaleChart_comap_subschemeι_eraseIdx p E hE j hj)

theorem inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx_of_eq (D : X.IdealSheafData) (hD : E[j]'hj = D) :
    InStrictNormalCrossingPosition (D.subschemeι ≫ p)
      ((E.eraseIdx j).map fun F => F.comap D.subschemeι) := by
  subst hD
  exact inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx p E hE j hj


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
section



variable {X X₁ : Scheme.{u}} {k : Type u} [Field k]
  {p : X ⟶ Spec (CommRingCat.of k)} {π : X₁ ⟶ X} {Z : X.IdealSheafData}
  {E : List X.IdealSheafData}

section
variable (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
include hZ hπ

theorem hasStrictNormalCrossingsWith_exceptionalIdeal :
    HasStrictNormalCrossingsWith (π ≫ p) (Blowup.exceptionalIdeal π Z) [] := by
  rw [hasStrictNormalCrossingsWith_iff]
  intro x hx
  rw [Blowup.exceptionalIdeal_eq_comap] at hx
  have hy : π.base x ∈ Z.support := by
    simp only [Scheme.IdealSheafData.support_comap] at hx
    exact hx
  obtain ⟨U, hyU, m, c, a, S, -, -, -, hZU⟩ := hZ.exists_etaleChart hy
  have hxU : x ∈ (TopologicalSpace.Opens.map π.base).obj U := hyU
  obtain ⟨s, hs, hxs⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZU x hxU
  refine ⟨(blowupChartOfIsBlowup π c S hπ hZU s hs).domain, hxs, m,
    (blowupChartOfIsBlowup π c S hπ hZU s hs).chart, fun _ => none, {s}, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  · exact BlowupChart.restrictIdeal_exceptionalIdeal
      (blowupChartOfIsBlowup π c S hπ hZU s hs) Z hs hZU

theorem isSmoothDivisor_exceptionalIdeal :
    IsSmoothDivisor (π ≫ p) (Blowup.exceptionalIdeal π Z) := by
  have hsmooth : Smooth ((Blowup.exceptionalIdeal π Z).subschemeι ≫ (π ≫ p)) :=
    smooth_subschemeι_comp_of_hasStrictNormalCrossingsWith (Blowup.exceptionalIdeal π Z) []
      (hasStrictNormalCrossingsWith_exceptionalIdeal hZ hπ)
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := by
    rw [Blowup.exceptionalIdeal_eq_comap]
    exact hπ.1
  exact (isSmoothDivisor_iff (π ≫ p) (Blowup.exceptionalIdeal π Z)).mpr ⟨hcart, hsmooth⟩


end

private theorem smooth_ι_comp_of_etaleChart_consolidated268 {Y : Scheme.{u}} {K : Type u}
    [Field K] {q : Y ⟶ Spec (CommRingCat.of K)} {V : Y.Opens} {n : ℕ} (c : EtaleChart q V n) :
    Smooth (V.ι ≫ q) := by
  have := c.isEtale
  have hsm : Smooth c.map := inferInstance
  have hsa : Smooth (affineSpaceFinToSpec K n) := affineSpaceIsSmooth K n
  rw [← c.comp_struct]
  infer_instance

theorem smooth_comp_of_isBlowupAlongIdealSheaf [Smooth p] (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    Smooth (π ≫ p) := by
  have key : ∀ x : ↥X₁, ∃ V : X₁.Opens, x ∈ V ∧ Smooth (V.ι ≫ (π ≫ p)) := by
    intro x
    by_cases hxs : π.base x ∈ Z.support
    · obtain ⟨U, hyU, m, c, a, S, -, -, -, hZU⟩ := hZ.exists_etaleChart hxs
      have hxU : x ∈ (TopologicalSpace.Opens.map π.base).obj U := hyU
      obtain ⟨s, hs, hxB⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZU x hxU
      exact ⟨(blowupChartOfIsBlowup π c S hπ hZU s hs).domain, hxB,
        smooth_ι_comp_of_etaleChart_consolidated268 (blowupChartOfIsBlowup π c S hπ hZU s hs).chart⟩
    · refine ⟨π ⁻¹ᵁ Z.support.compl, hxs, ?_⟩
      have : IsIso (AlgebraicGeometry.morphismRestrict π Z.support.compl) :=
        Blowup.blowupIsIsoOffCenter X X₁ π Z hπ
      have h1 : (π ⁻¹ᵁ Z.support.compl).ι ≫ (π ≫ p) =
          AlgebraicGeometry.morphismRestrict π Z.support.compl ≫
            (Scheme.Opens.ι Z.support.compl ≫ p) := by
        rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
      rw [h1]
      infer_instance
  choose U hU hsm using key
  have hUtop : iSup U = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩
  exact smooth_of_iSup_eq_top (π ≫ p) U hUtop hsm

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.BlowupDerivativeIdealBound
section

open TopologicalSpace


private theorem presheaf_map_eq_consolidated295 {X : Scheme.{u}} {A B : (X.Opens)ᵒᵖ} (f g : A ⟶ B) :
    X.presheaf.map f = X.presheaf.map g := by
  have h : f = g := Quiver.Hom.unop_inj (Subsingleton.elim f.unop g.unop)
  rw [h]

section
variable {Y : Scheme.{u}}

private theorem idealSheafData_mul_le_mul_consolidated295 {A B C D : Y.IdealSheafData}
    (h1 : A ≤ B) (h2 : C ≤ D) : A * C ≤ B * D := by
  refine Scheme.IdealSheafData.le_def.mpr fun U => ?_
  rw [Scheme.IdealSheafData.ideal_mul, Scheme.IdealSheafData.ideal_mul]
  exact Ideal.mul_mono (Scheme.IdealSheafData.le_def.mp h1 U)
    (Scheme.IdealSheafData.le_def.mp h2 U)

private theorem idealSheafData_mul_le_left_consolidated295 (A B : Y.IdealSheafData) :
    A * B ≤ A := by
  refine Scheme.IdealSheafData.le_def.mpr fun U => ?_
  rw [Scheme.IdealSheafData.ideal_mul]
  exact Ideal.mul_le.mpr fun r hr s _ => Ideal.mul_mem_right _ _ hr

private theorem idealSheafData_pow_le_pow_of_le_consolidated295 (A : Y.IdealSheafData) {i j : ℕ}
    (h : j ≤ i) : A ^ i ≤ A ^ j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  calc A ^ (j + d) = A ^ j * A ^ d := by rw [pow_add]
    _ ≤ A ^ j := idealSheafData_mul_le_left_consolidated295 _ _

private theorem appLE_ι_bijective_consolidated295 (V : Y.Opens)
    (e : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V) :
    Function.Bijective (V.ι.appLE V ⊤ e).hom := by
  have h : V.ι.appLE V ⊤ e = V.topIso.inv := by
    simp
    exact presheaf_map_eq_consolidated295 _ _
  rw [h]
  exact ConcreteCategory.bijective_of_isIso _

private theorem ideal_eq_of_comap_ι_eq_consolidated295 {A B : Y.IdealSheafData}
    (V : Y.affineOpens) (h : A.comap (V : Y.Opens).ι = B.comap (V : Y.Opens).ι) :
    A.ideal V = B.ideal V := by
  have : IsAffine (V : Y.Opens).toScheme := V.2
  have e : (⊤ : (V : Y.Opens).toScheme.Opens) ≤ (V : Y.Opens).ι ⁻¹ᵁ (V : Y.Opens) := by simp
  have h1 := A.comap_ideal_eq_map_appLE (V : Y.Opens).ι V ⟨⊤, isAffineOpen_top _⟩ e
  have h2 := B.comap_ideal_eq_map_appLE (V : Y.Opens).ι V ⟨⊤, isAffineOpen_top _⟩ e
  rw [h, h2] at h1
  have hbij := appLE_ι_bijective_consolidated295 (V : Y.Opens) e
  have hbot : Ideal.comap ((V : Y.Opens).ι.appLE (V : Y.Opens) ⊤ e).hom
      (⊥ : Ideal Γ((V : Y.Opens).toScheme, ⊤)) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hbij.1
  have h3 := congrArg (Ideal.comap ((V : Y.Opens).ι.appLE (V : Y.Opens) ⊤ e).hom) h1
  rw [Ideal.comap_map_of_surjective _ hbij.2, Ideal.comap_map_of_surjective _ hbij.2, hbot,
    sup_bot_eq, sup_bot_eq] at h3
  exact h3.symm


end

private theorem exists_affineOpen_le_consolidated295 {X : Scheme.{u}} (x : ↥X) (W : X.Opens)
    (hx : x ∈ W) : ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ W := by
  obtain ⟨U, hU, hxU, hUW⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hx
  exact ⟨⟨U, hU⟩, hxU, hUW⟩

section
variable {Y : Scheme.{u}}

private theorem exists_pow_mul_mem_of_map_mem_basicOpen_consolidated295 (U : Y.affineOpens)
    (f : Γ(Y, U.1)) (J : Ideal Γ(Y, U.1)) (x : Γ(Y, U.1))
    (hx : (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom x ∈
      J.map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom) :
    ∃ n : ℕ, f ^ n * x ∈ J := by
  have := U.2.isLocalization_basicOpen f
  have halg : (algebraMap Γ(Y, U.1) Γ(Y, Y.basicOpen f)) =
      (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom := rfl
  rw [← halg] at hx
  obtain ⟨⟨⟨y, hy⟩, ⟨m, hm⟩⟩, hxy⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) Γ(Y, Y.basicOpen f)).mp hx
  simp only at hxy
  rw [← map_mul] at hxy
  obtain ⟨⟨c, hc⟩, hcc⟩ :=
    (IsLocalization.eq_iff_exists (Submonoid.powers f) Γ(Y, Y.basicOpen f)).mp hxy
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hc
  refine ⟨b + a, ?_⟩
  simp only at hcc
  have h2 : f ^ (b + a) * x = f ^ b * y := by rw [← hcc]; ring
  rw [h2]
  exact J.mul_mem_left _ hy

theorem le_of_forall_exists_affineOpen {A B : Y.IdealSheafData}
    (h : ∀ y : ↥Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧ A.ideal U ≤ B.ideal U) :
    A ≤ B := by
  refine Scheme.IdealSheafData.le_def.mpr fun U => ?_
  refine of_affine_open_cover (P := fun W : Y.affineOpens => A.ideal W ≤ B.ideal W)
    (fun y : ↥Y => (h y).choose) ?_ U ?_ ?_ ?_
  · rw [eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, (h y).choose_spec.1⟩
  · intro W f hW
    rw [← A.map_ideal_basicOpen W f, ← B.map_ideal_basicOpen W f]
    exact Ideal.map_mono hW
  · intro W s hspan hs x hxA
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (B.ideal W) (s : Set Γ(Y, W.1)) hspan x ?_
    rintro ⟨f, hf⟩
    have hmem : (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom x ∈
        (B.ideal W).map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom := by
      rw [B.map_ideal_basicOpen W f]
      refine hs ⟨f, Finset.mem_coe.mp hf⟩ ?_
      rw [← A.map_ideal_basicOpen W f]
      exact Ideal.mem_map_of_mem _ hxA
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_of_map_mem_basicOpen_consolidated295 W f (B.ideal W) x hmem
    exact ⟨n, by simpa [smul_eq_mul] using hn⟩
  · intro y
    exact (h y).choose_spec.2


end

section
variable (k : Type u) [Field k] [CharZero k] {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of k)) [Smooth q] (F J : Y.IdealSheafData)

theorem derivIdealSheaf_pow_succ_mul_le (n : ℕ) :
    derivIdealSheaf k q (F ^ (n + 1) * J) ≤ F ^ n * derivIdealSheaf k q J := by
  refine le_trans (derivIdealSheaf_mul_le k q (F ^ (n + 1)) J) (sup_le ?_ ?_)
  · exact idealSheafData_mul_le_mul_consolidated295 (idealSheafData_pow_le_pow_of_le_consolidated295 F (Nat.le_succ n)) le_rfl
  · calc J * derivIdealSheaf k q (F ^ (n + 1))
        ≤ J * (F ^ n * derivIdealSheaf k q F) :=
          idealSheafData_mul_le_mul_consolidated295 le_rfl (derivIdealSheaf_pow_succ_le k q F n)
      _ = F ^ n * (J * derivIdealSheaf k q F) := mul_left_comm _ _ _
      _ ≤ F ^ n * derivIdealSheaf k q J :=
          idealSheafData_mul_le_mul_consolidated295 le_rfl
            (le_trans (idealSheafData_mul_le_left_consolidated295 J (derivIdealSheaf k q F))
              (le_derivIdealSheaf k q J))

theorem derivIdealSheafIterate_pow_mul_le (m j : ℕ) (hj : j ≤ m) :
    derivIdealSheafIterate k q j (F ^ m * J) ≤ F ^ (m - j) * derivIdealSheafIterate k q j J := by
  revert hj
  induction j with
  | zero =>
    intro _
    rw [derivIdealSheafIterate_zero, derivIdealSheafIterate_zero, Nat.sub_zero]
  | succ j ih =>
    intro hj
    have hj' : j ≤ m := Nat.le_of_succ_le hj
    have h1 : m - j = (m - (j + 1)) + 1 := by omega
    rw [derivIdealSheafIterate_succ, derivIdealSheafIterate_succ]
    refine le_trans (derivIdealSheaf_mono k q (ih hj')) ?_
    rw [h1]
    exact derivIdealSheaf_pow_succ_mul_le k q F (derivIdealSheafIterate k q j J) (m - (j + 1))


end

private theorem derivIdealSheafIterate_congr_hom_consolidated295 (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (q q' : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q]
    [LocallyOfFiniteType q'] (hq : q = q') (r : ℕ) (I : X.IdealSheafData) :
    derivIdealSheafIterate k q r I = derivIdealSheafIterate k q' r I := by
  subst hq
  rfl

section
variable (k : Type u) [Field k] [CharZero k] {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (π : X₁ ⟶ X)

theorem exists_affineOpen_comap_derivIdealSheafIterate_eq [Smooth (π ≫ p)] (W : X.Opens)
    [IsIso (AlgebraicGeometry.morphismRestrict π W)] (x : ↥X₁) (hx : x ∈ π ⁻¹ᵁ W)
    (j : ℕ) (I : X.IdealSheafData) :
    ∃ V : X₁.affineOpens, x ∈ V.1 ∧ V.1 ≤ π ⁻¹ᵁ W ∧
      ((derivIdealSheafIterate k p j I).comap π).ideal V =
        (derivIdealSheafIterate k (π ≫ p) j (I.comap π)).ideal V := by
  obtain ⟨V, hxV, hVW⟩ := exists_affineOpen_le_consolidated295 x (π ⁻¹ᵁ W) hx
  refine ⟨V, hxV, hVW, ?_⟩
  have hfac : (V : X₁.Opens).ι ≫ π
      = X₁.homOfLE hVW ≫ (AlgebraicGeometry.morphismRestrict π W ≫ W.ι) := by
    rw [morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have : IsOpenImmersion ((V : X₁.Opens).ι ≫ π) := by rw [hfac]; infer_instance
  have : Smooth ((V : X₁.Opens).ι ≫ π) := inferInstance
  have hcomp : ∀ A : X.IdealSheafData,
      A.comap ((V : X₁.Opens).ι ≫ π) = (A.comap π).comap (V : X₁.Opens).ι := by
    intro A
    simp [Scheme.IdealSheafData.comap_comp]
  have hassoc : ((V : X₁.Opens).ι ≫ π) ≫ p = (V : X₁.Opens).ι ≫ (π ≫ p) := Category.assoc _ _ _
  have h1 := derivIdealSheafIterate_comap k p ((V : X₁.Opens).ι ≫ π) j I
  have h2 := derivIdealSheafIterate_comap k (π ≫ p) (V : X₁.Opens).ι j (I.comap π)
  rw [hcomp I] at h1
  rw [derivIdealSheafIterate_congr_hom_consolidated295 k (((V : X₁.Opens).ι ≫ π) ≫ p)
      ((V : X₁.Opens).ι ≫ (π ≫ p)) hassoc j ((I.comap π).comap (V : X₁.Opens).ι)] at h1
  have key : ((derivIdealSheafIterate k p j I).comap π).comap (V : X₁.Opens).ι
      = (derivIdealSheafIterate k (π ≫ p) j (I.comap π)).comap (V : X₁.Opens).ι := by
    rw [← hcomp (derivIdealSheafIterate k p j I), ← h1]
    exact h2
  exact ideal_eq_of_comap_ι_eq_consolidated295 V key

theorem comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul [IsLocallyNoetherian X₁] (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (I : X.IdealSheafData) (m : ℕ)
    (hI : I ≤ Z ^ m) (j : ℕ) (hj : j ≤ m) :
    haveI : Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hZ hπ
    (derivIdealSheafIterate k p j I).comap π ≤
      Blowup.exceptionalIdeal π Z ^ (m - j) *
        derivIdealSheafIterate k (π ≫ p) j (controlledTransform π Z I m hπ hI) := by
  have : Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hZ hπ
  refine le_of_forall_exists_affineOpen ?_
  intro x
  by_cases hxs : π.base x ∈ Z.support
  · obtain ⟨U, hxU, n, c, a, S, -, -, -, hZU⟩ := hZ.exists_etaleChart hxs
    obtain ⟨U₀, hxU0, hU0U⟩ := exists_affineOpen_le_consolidated295 (π.base x) U hxU
    have hle : (U₀ : X.Opens) ≤ U := hU0U
    set c₀ := c.restrict hle with hc₀
    have hZU₀ : restrictIdeal Z (U₀ : X.Opens) = c₀.coordIdeal S := by
      rw [hc₀]
      exact restrictIdeal_eq_restrict_coordIdeal_of_le hle c Z S hZU
    have hx' : x ∈ π ⁻¹ᵁ (U₀ : X.Opens) := hxU0
    obtain ⟨s, hs, hxB⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c₀ S hπ hZU₀ x hx'
    set Bc := blowupChartOfIsBlowup π c₀ S hπ hZU₀ s hs with hBc
    obtain ⟨V, hxV, hVle⟩ := exists_affineOpen_le_consolidated295 x Bc.domain hxB
    refine ⟨V, hxV, ?_⟩
    have hVdom : (V : X₁.Opens) ≤ Bc.domain := hVle
    have hVU : (V : X₁.Opens) ≤ π ⁻¹ᵁ (U₀ : X.Opens) := le_trans hVdom Bc.domain_le
    set cV := Bc.chart.restrict hVdom with hcV
    have hcoordres : ∀ i : Fin n,
        cV.coord i = (X₁.presheaf.map (homOfLE hVdom).op).hom (Bc.chart.coord i) := by
      intro i
      rw [hcV]
      exact EtaleChart.coord_restrict Bc.chart hVdom i
    have hE : (Blowup.exceptionalIdeal π Z).ideal V = Ideal.span {cV.coord s} := by
      have h1 : restrictIdeal (Blowup.exceptionalIdeal π Z) (V : X₁.Opens) = cV.coordIdeal {s} := by
        rw [hcV]
        exact restrictIdeal_eq_restrict_coordIdeal_of_le hVdom Bc.chart (Blowup.exceptionalIdeal π Z) {s}
          (Bc.restrictIdeal_exceptionalIdeal Z hs hZU₀)
      have h2 := EtaleChart.ideal_eq_span_coord cV V.2 (Blowup.exceptionalIdeal π Z) {s} h1
      simpa using h2
    have hEpow : ∀ (t : ℕ) (C : X₁.IdealSheafData),
        (Blowup.exceptionalIdeal π Z ^ t * C).ideal V = Ideal.span {cV.coord s ^ t} * C.ideal V := by
      intro t C
      rw [Scheme.IdealSheafData.ideal_mul, Scheme.IdealSheafData.ideal_pow]
      show (Blowup.exceptionalIdeal π Z).ideal V ^ t * C.ideal V
        = Ideal.span {cV.coord s ^ t} * C.ideal V
      rw [hE, Ideal.span_singleton_pow]
    let algU : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, (U₀ : X.Opens)) := c₀.algebra
    let algV : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X₁, (V : X₁.Opens)) := cV.algebra
    let kU : Algebra k Γ(X, (U₀ : X.Opens)) := sectionsAlgebra k p (U₀ : X.Opens)
    let kV : Algebra k Γ(X₁, (V : X₁.Opens)) := sectionsAlgebra k (π ≫ p) (V : X₁.Opens)
    have towerU := c₀.isScalarTower
    have towerV := cV.isScalarTower
    have feU := c₀.algebra_formallyEtale U₀.2
    have feV := cV.algebra_formallyEtale V.2
    let φA : Γ(X, (U₀ : X.Opens)) →ₐ[k] Γ(X₁, (V : X₁.Opens)) :=
      { (π.appLE (U₀ : X.Opens) (V : X₁.Opens) hVU).hom with
        commutes' := fun a => sectionsAlgebraMap_appLE_apply k p π _ _ hVU a }
    have hφ : ∀ y : Γ(X, (U₀ : X.Opens)), φA y
        = (X₁.presheaf.map (homOfLE hVdom).op).hom
            ((π.appLE (U₀ : X.Opens) Bc.domain Bc.domain_le).hom y) := by
      intro y
      show (π.appLE (U₀ : X.Opens) (V : X₁.Opens) hVU).hom y = _
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    have hmap : ∀ J : Ideal Γ(X, (U₀ : X.Opens)),
        Ideal.map φA J
          = Ideal.map (π.appLE (U₀ : X.Opens) (V : X₁.Opens) hVU).hom J := fun J => rfl
    have hcoordU : ∀ i : ULift.{u} (Fin n),
        @EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X, (U₀ : X.Opens)) _ algU i
          = c₀.coord i.down := by
      rintro ⟨i⟩
      exact c₀.etaleCoordinates_coord i
    have hcoordV : ∀ i : ULift.{u} (Fin n),
        @EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X₁, (V : X₁.Opens)) _ algV i
          = cV.coord i.down := by
      rintro ⟨i⟩
      exact cV.etaleCoordinates_coord i
    have hcoordVs :
        @EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X₁, (V : X₁.Opens)) _ algV
          (ULift.up s) = cV.coord s := cV.etaleCoordinates_coord s
    have hin : ∀ i ∈ uliftFinset n S, i ≠ (ULift.up s : ULift.{u} (Fin n)) →
        φA (@EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X, (U₀ : X.Opens)) _ algU i)
          = @EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X₁, (V : X₁.Opens)) _ algV i *
            @EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X₁, (V : X₁.Opens)) _ algV
              (ULift.up s) := by
      intro i hi his
      have hids : i.down ≠ s := fun hh => his (ULift.ext i (ULift.up s) hh)
      have hmem : i.down ∈ S := down_mem_of_mem_uliftFinset hi
      rw [hcoordU i, hcoordV i, hcoordVs]
      rw [hφ, Bc.appLE_coord_of_mem i.down hmem hids, map_mul, hcoordres, hcoordres]
    have hsc : φA (@EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X, (U₀ : X.Opens)) _ algU
          (ULift.up s))
        = @EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X₁, (V : X₁.Opens)) _ algV
            (ULift.up s) := by
      rw [hcoordU (ULift.up s), hcoordVs]
      rw [hφ, Bc.appLE_coord_self, hcoordres]
    have hout : ∀ i ∉ uliftFinset n S,
        φA (@EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X, (U₀ : X.Opens)) _ algU i)
          = @EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X₁, (V : X₁.Opens)) _ algV i := by
      intro i hi
      have hid : i.down ∉ S := fun hh => hi ((mem_uliftFinset S i).mpr hh)
      rw [hcoordU i, hcoordV i]
      rw [hφ, Bc.appLE_coord_of_not_mem i.down hid, hcoordres]
    have hsT : (ULift.up s : ULift.{u} (Fin n)) ∈ uliftFinset n S := up_mem_uliftFinset hs
    have hnzd : @EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X₁, (V : X₁.Opens)) _ algV
        (ULift.up s) ∈ nonZeroDivisors Γ(X₁, (V : X₁.Opens)) := by
      rw [hcoordVs]
      exact coord_mem_nonZeroDivisors V.2 cV s
    have hJ : Ideal.map φA (I.ideal U₀) ≤
        Ideal.span {(@EtaleCoordinates.coord k _ (ULift.{u} (Fin n)) Γ(X₁, (V : X₁.Opens)) _ algV
          (ULift.up s)) ^ m} * (controlledTransform π Z I m hπ hI).ideal V := by
      have h1 : Ideal.map (π.appLE (U₀ : X.Opens) (V : X₁.Opens) hVU).hom (I.ideal U₀)
          ≤ (I.comap π).ideal V :=
        I.map_appLE_le_comap_ideal π U₀ V hVU
      rw [← exceptionalIdeal_pow_mul_controlledTransform π Z I m hπ hI,
        hEpow m (controlledTransform π Z I m hπ hI)] at h1
      rw [hcoordVs, hmap]
      exact h1
    have hring := EtaleCoordinates.map_derivIdealIterate_le_span_pow_mul k (ULift.{u} (Fin n))
      Γ(X, (U₀ : X.Opens)) Γ(X₁, (V : X₁.Opens)) φA (uliftFinset n S) (ULift.up s)
      hin hsc hout hsT hnzd (I.ideal U₀) ((controlledTransform π Z I m hπ hI).ideal V) m hJ j hj
    rw [hcoordVs] at hring
    rw [(derivIdealSheafIterate k p j I).comap_ideal_eq_map_appLE π U₀ V hVU,
      derivIdealSheafIterate_ideal,
      hEpow (m - j) (derivIdealSheafIterate k (π ≫ p) j (controlledTransform π Z I m hπ hI)),
      derivIdealSheafIterate_ideal, ← hmap]
    exact hring
  · have : IsIso (AlgebraicGeometry.morphismRestrict π Z.support.compl) :=
      Blowup.blowupIsIsoOffCenter X X₁ π Z hπ
    have hx : x ∈ π ⁻¹ᵁ Z.support.compl := by exact hxs
    obtain ⟨V, hxV, hVW, heq⟩ :=
      exists_affineOpen_comap_derivIdealSheafIterate_eq k p π Z.support.compl x hx j I
    refine ⟨V, hxV, ?_⟩
    rw [heq]
    have h2 := derivIdealSheafIterate_pow_mul_le k (π ≫ p) (Blowup.exceptionalIdeal π Z)
      (controlledTransform π Z I m hπ hI) m j hj
    rw [exceptionalIdeal_pow_mul_controlledTransform π Z I m hπ hI] at h2
    exact Scheme.IdealSheafData.le_def.mp h2 V


end

theorem derivIdealSheafIterate_le_pow_of_hasStrictNormalCrossingsWith (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (Z I : X.IdealSheafData) (E : List X.IdealSheafData) (hZ : HasStrictNormalCrossingsWith p Z E) (m : ℕ)
    (hI : I ≤ Z ^ m) (j : ℕ) :
    derivIdealSheafIterate k p j I ≤ Z ^ (m - j) :=
  le_pow_of_hasStrictNormalCrossingsWith p Z (derivIdealSheafIterate k p j I) E hZ (m - j)
    (Set.Subset.trans (support_subset_orderAtLeastLocus_of_le_pow Z I m hI)
      (orderAtLeastLocus_subset_orderAtLeastLocus_derivIdealSheafIterate k p I j m))

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.ControlledTransformOrderBound
section

open TopologicalSpace


private theorem le_natCast_iff_not_succ_le_consolidated311 (a : ℕ∞) (m : ℕ) :
    a ≤ (m : ℕ∞) ↔ ¬ ((m + 1 : ℕ) : ℕ∞) ≤ a := by
  induction a using ENat.recTopCoe with
  | top =>
      refine iff_of_false ?_ ?_
      · intro h
        have h1 : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := le_trans le_top h
        have h2 : m + 1 ≤ m := by exact_mod_cast h1
        omega
      · exact fun h => h le_top
  | coe n =>
      constructor
      · intro h h'
        have h1 : n ≤ m := by exact_mod_cast h
        have h2 : m + 1 ≤ n := by exact_mod_cast h'
        omega
      · intro h
        have h2 : n ≤ m := by
          by_contra hc
          exact h (by exact_mod_cast (by omega : m + 1 ≤ n))
        exact_mod_cast h2

theorem orderAt_le_iff_notMem_orderAtLeastLocus {X : Scheme.{u}} (I : X.IdealSheafData) (m : ℕ)
    (x : X) :
    orderAt I x ≤ (m : ℕ∞) ↔ x ∉ orderAtLeastLocus I (m + 1) := by
  rw [mem_orderAtLeastLocus_iff]
  exact le_natCast_iff_not_succ_le_consolidated311 (orderAt I x) m

section
variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (I : X.IdealSheafData) (m : ℕ) (x : X)

theorem notMem_support_derivIdealSheafIterate_iff_orderAt_le :
    x ∉ (derivIdealSheafIterate k p m I).support ↔ orderAt I x ≤ (m : ℕ∞) := by
  have h0 := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I (m := m + 1) (hm := by omega)
  rw [Nat.add_sub_cancel] at h0
  have hiff : x ∈ (derivIdealSheafIterate k p m I).support ↔ x ∈ orderAtLeastLocus I (m + 1) := by
    rw [← SetLike.mem_coe, h0]
  rw [orderAt_le_iff_notMem_orderAtLeastLocus, hiff]

theorem stalkIdeal_derivIdealSheafIterate_eq_top_iff_orderAt_le :
    stalkIdeal (derivIdealSheafIterate k p m I) x = ⊤ ↔ orderAt I x ≤ (m : ℕ∞) := by
  rw [← notMem_support_derivIdealSheafIterate_iff_orderAt_le k p I m x,
    mem_support_iff_stalkIdeal_ne_top]
  simp


end

section
variable (k : Type u) [Field k] [CharZero k] {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (π : X₁ ⟶ X) [IsLocallyNoetherian X₁] (Z : X.IdealSheafData) (E : List X.IdealSheafData) (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (I : X.IdealSheafData) (m : ℕ) (hI : I ≤ Z ^ m)
include hZ

theorem orderAt_controlledTransform_le (z : X) (hz : orderAt I z ≤ (m : ℕ∞)) (x₁ : X₁)
    (hx₁ : π.base x₁ = z) :
    orderAt (controlledTransform π Z I m hπ hI) x₁ ≤ (m : ℕ∞) := by
  subst hx₁
  have hsm : Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hZ hπ
  have h1 : stalkIdeal (derivIdealSheafIterate k p m I) (π.base x₁) = ⊤ :=
    (stalkIdeal_derivIdealSheafIterate_eq_top_iff_orderAt_le k p I m (π.base x₁)).2 hz
  have h2 : (derivIdealSheafIterate k p m I).comap π ≤
      Blowup.exceptionalIdeal π Z ^ (m - m) *
        derivIdealSheafIterate k (π ≫ p) m (controlledTransform π Z I m hπ hI) :=
    comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p π Z E hZ hπ I m hI m le_rfl
  rw [Nat.sub_self, pow_zero, one_mul] at h2
  have h3 : stalkIdeal ((derivIdealSheafIterate k p m I).comap π) x₁ = ⊤ := by
    rw [stalkIdeal_comap, h1, Ideal.map_top]
  have h4 := stalkIdeal_mono h2 x₁
  rw [h3, top_le_iff] at h4
  exact (stalkIdeal_derivIdealSheafIterate_eq_top_iff_orderAt_le k (π ≫ p)
    (controlledTransform π Z I m hπ hI) m x₁).1 h4

theorem orderAt_controlledTransform_le_of_orderAt_image_le (x₁ : X₁) (hx₁ : orderAt I (π.base x₁) ≤ (m : ℕ∞)) :
    orderAt (controlledTransform π Z I m hπ hI) x₁ ≤ (m : ℕ∞) :=
  orderAt_controlledTransform_le k p π Z E hZ hπ I m hI (π.base x₁) hx₁ x₁ rfl

theorem orderAt_controlledTransform_le_of_not_succ_le (z : X) (hz : ¬ (((m + 1 : ℕ) : ℕ∞) ≤ orderAt I z)) (x₁ : X₁)
    (hx₁ : π.base x₁ = z) :
    orderAt (controlledTransform π Z I m hπ hI) x₁ ≤ (m : ℕ∞) :=
  orderAt_controlledTransform_le k p π Z E hZ hπ I m hI z
    ((orderAt_le_iff_notMem_orderAtLeastLocus I m z).2 hz) x₁ hx₁

theorem orderAt_controlledTransform_le_of_forall_le (h : ∀ x : X, orderAt I x ≤ (m : ℕ∞)) (x₁ : X₁) :
    orderAt (controlledTransform π Z I m hπ hI) x₁ ≤ (m : ℕ∞) :=
  orderAt_controlledTransform_le k p π Z E hZ hπ I m hI (π.base x₁) (h (π.base x₁)) x₁ rfl

theorem orderAtLeastLocus_controlledTransform_subset_preimage :
    orderAtLeastLocus (controlledTransform π Z I m hπ hI) (m + 1) ⊆
      ⇑π.base ⁻¹' orderAtLeastLocus I (m + 1) := by
  intro x₁ hx₁
  by_contra hz
  rw [Set.mem_preimage, mem_orderAtLeastLocus_iff] at hz
  have h := orderAt_controlledTransform_le_of_not_succ_le k p π Z E hZ hπ I m hI
    (π.base x₁) hz x₁ rfl
  rw [mem_orderAtLeastLocus_iff] at hx₁
  have hle : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := le_trans hx₁ h
  have hcontra : m + 1 ≤ m := by exact_mod_cast hle
  omega


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.ControlledTransformOrderMonotone
section



private theorem isLocallyNoetherian_of_smooth_over_field_consolidated331 (k : Type u) [Field k]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of k)) [Smooth q] :
    IsLocallyNoetherian Y :=
  AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian q

section
variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (d : BlowupSequenceData X) (hd : d.IsMarked p I m E) (hI : ∀ x : ↥X, orderAt I x ≤ (m : ℕ∞)) (t : ℕ) (ht : t ≤ d.length)
include hd hI ht

theorem smooth_projectionToBase_comp_and_orderAt_controlledTransform_le :
    Smooth (d.projectionToBase t ≫ p) ∧
      ∀ x : ↥(d.obj t), orderAt (d.controlledTransform I m t) x ≤ (m : ℕ∞) := by
  revert ht
  induction t with
  | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · rw [BlowupSequenceData.projectionToBase_zero]
        infer_instance
      · intro x
        rw [BlowupSequenceData.controlledTransform_zero, orderAt_comap_of_isOpenImmersion]
        exact hI _
  | succ s ih =>
      intro hs
      have hs' : s < d.length := hs
      obtain ⟨ihsm, ihord⟩ := ih (le_of_lt hs')
      have : Smooth (d.projectionToBase s ≫ p) := ihsm
      have hπ : Blowup.IsBlowupAlongIdealSheaf (d.map s) (d.center s) := d.isBlowup s hs'
      have hsnc : HasStrictNormalCrossingsWith (d.projectionToBase s ≫ p) (d.center s) (d.boundaryFrom E s) := hd.center_snc s hs'
      have hsm1 : Smooth (d.projectionToBase (s + 1) ≫ p) := by
        rw [BlowupSequenceData.projectionToBase_succ, Category.assoc]
        exact smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
      refine ⟨hsm1, ?_⟩
      have : Smooth (d.projectionToBase (s + 1) ≫ p) := hsm1
      have : IsLocallyNoetherian (d.obj (s + 1)) :=
        isLocallyNoetherian_of_smooth_over_field_consolidated331 k (d.projectionToBase (s + 1) ≫ p)
      have hIle : d.controlledTransform I m s ≤ (d.center s) ^ m :=
        le_pow_of_hasStrictNormalCrossingsWith (d.projectionToBase s ≫ p) (d.center s) (d.controlledTransform I m s) (d.boundaryFrom E s)
          hsnc m (hd.center_order s hs')
      have hEq : d.controlledTransform I m (s + 1)
          = controlledTransform (d.map s) (d.center s) (d.controlledTransform I m s) m hπ hIle :=
        eq_controlledTransform_of_mul_eq_comap (d.map s) (d.center s) (d.controlledTransform I m s) m hπ hIle
          (d.controlledTransform I m (s + 1)) (d.pow_exceptionalIdeal_mul_controlledTransform_succ I m s (hd.divisible s hs'))
      intro x
      rw [hEq]
      exact orderAt_controlledTransform_le_of_forall_le k (d.projectionToBase s ≫ p) (d.map s) (d.center s)
        (d.boundaryFrom E s) hsnc hπ (d.controlledTransform I m s) m hIle ihord x

theorem orderAt_controlledTransform_le_of_isMarked (x : ↥(d.obj t)) :
    orderAt (d.controlledTransform I m t) x ≤ (m : ℕ∞) :=
  (smooth_projectionToBase_comp_and_orderAt_controlledTransform_le k p I m E d hd hI t ht).2 x


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafPullback
section



theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.le_of_pow_mul_le_pow_mul {Y : Scheme.{u}}
    {F B B' : Y.IdealSheafData} (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F) (n : ℕ)
    (h : F ^ n * B ≤ F ^ n * B') : B ≤ B' :=
  (hF.pow n).le_of_mul_le_mul h

theorem comap_prod_map_range {X Y : Scheme.{u}} (π : Y ⟶ X) (f : ℕ → X.IdealSheafData) (m : ℕ) :
    (((List.range m).map f).prod).comap π =
      ((List.range m).map (fun j => (f j).comap π)).prod := by
  induction m with
  | zero =>
    simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_append, List.prod_append,
      AlgebraicGeometry.Scheme.IdealSheafData.comap_mul, ih]
    simp

section
variable {X : Scheme.{u}} (f g : ℕ → X.IdealSheafData)

private theorem prod_map_range_le_consolidated312 :
    ∀ m : ℕ, (∀ j, j < m → f j ≤ g j) →
      ((List.range m).map f).prod ≤ ((List.range m).map g).prod := fun _ h =>
  List.prod_le_prod' fun j hj => h j (List.mem_range.mp hj)

private theorem prod_map_range_congr_consolidated312 :
    ∀ m : ℕ, (∀ j, j < m → f j = g j) →
      ((List.range m).map f).prod = ((List.range m).map g).prod := fun _ h =>
  congrArg List.prod (List.map_congr_left fun j hj => h j (List.mem_range.mp hj))


end

private theorem prod_map_pow_mul_pow_eq_consolidated312 {X : Scheme.{u}} (F : X.IdealSheafData)
    (G : ℕ → X.IdealSheafData) (w c : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map (fun j => (F ^ (w j) * G j) ^ (c j))).prod =
      F ^ (∑ j ∈ Finset.range n, w j * c j) *
        ((List.range n).map (fun j => G j ^ (c j))).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_append, List.prod_append,
      ih, Finset.sum_range_succ, pow_add]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_pow,
      ← pow_mul]
    rw [mul_mul_mul_comm]

section
variable (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k]

theorem comap_tunedSheaf_le_exceptionalIdeal_pow_mul {P P₁ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p] [IsLocallyNoetherian P₁]
    (π : P₁ ⟶ P) [LocallyOfFiniteType (π ≫ p)] (p₁ : P₁ ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p₁] (hp₁ : p₁ = π ≫ p)
    (Z : P.IdealSheafData) (E : List P.IdealSheafData) (hZ : HasStrictNormalCrossingsWith p Z E)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (A : P.IdealSheafData) (m : ℕ) (hA : A ≤ Z ^ m) (u : ℕ) :
    (tunedSheaf k p A m u).comap π ≤
      Blowup.exceptionalIdeal π Z ^ u *
        tunedSheaf k p₁ (controlledTransform π Z A m hπ hA) m u := by
  subst hp₁
  refine le_trans (Scheme.IdealSheafData.comap_iSup π
    (fun c : {c : ℕ → ℕ // u ≤ ∑ j ∈ Finset.range m, (m - j) * c j} =>
      ((List.range m).map (fun j => derivIdealSheafIterate k p j A ^ (c.1 j))).prod)).le
    (iSup_le ?_)
  rintro ⟨c, hc⟩
  refine le_trans (le_of_eq (comap_prod_map_range π
    (fun j => derivIdealSheafIterate k p j A ^ c j) m)) ?_
  refine le_trans (prod_map_range_le_consolidated312 _
    (fun j => (Blowup.exceptionalIdeal π Z ^ (m - j) *
      derivIdealSheafIterate k (π ≫ p) j (controlledTransform π Z A m hπ hA)) ^ c j) m ?_) ?_
  · intro j hj
    refine le_trans (le_of_eq (AlgebraicGeometry.Scheme.IdealSheafData.comap_pow
      (derivIdealSheafIterate k p j A) π (c j))) ?_
    exact pow_le_pow_left'
      (comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p π Z E hZ hπ A m hA j
        (Nat.le_of_lt hj)) (c j)
  · refine le_trans (le_of_eq (prod_map_pow_mul_pow_eq_consolidated312 (Blowup.exceptionalIdeal π Z)
      (fun j => derivIdealSheafIterate k (π ≫ p) j (controlledTransform π Z A m hπ hA))
      (fun j => m - j) c m)) ?_
    refine mul_le_mul' (pow_le_pow_right_of_le_one' le_top hc) ?_
    exact le_iSup (fun d : {c : ℕ → ℕ // u ≤ ∑ j ∈ Finset.range m, (m - j) * c j} =>
      ((List.range m).map (fun j => derivIdealSheafIterate k (π ≫ p) j
        (controlledTransform π Z A m hπ hA) ^ (d.1 j))).prod) ⟨c, hc⟩

theorem comap_tunedSheaf_of_smooth {P Y : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p]
    [LocallyOfFiniteType p] (h : Y ⟶ P) [Smooth h]
    (q : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q] (hq : q = h ≫ p)
    (A : P.IdealSheafData) (m u : ℕ) :
    (tunedSheaf k p A m u).comap h = tunedSheaf k q (A.comap h) m u := by
  subst hq
  refine le_antisymm ?_ ?_
  · refine le_trans (Scheme.IdealSheafData.comap_iSup h
      (fun c : {c : ℕ → ℕ // u ≤ ∑ j ∈ Finset.range m, (m - j) * c j} =>
        ((List.range m).map (fun j => derivIdealSheafIterate k p j A ^ (c.1 j))).prod)).le
      (iSup_le ?_)
    rintro ⟨c, hc⟩
    refine le_trans (le_of_eq (comap_prod_map_range h
      (fun j => derivIdealSheafIterate k p j A ^ c j) m)) ?_
    refine le_trans (prod_map_range_le_consolidated312 _
      (fun j => derivIdealSheafIterate k (h ≫ p) j (A.comap h) ^ c j) m ?_) ?_
    · intro j _
      refine le_of_eq ?_
      show (derivIdealSheafIterate k p j A ^ c j).comap h
          = derivIdealSheafIterate k (h ≫ p) j (A.comap h) ^ c j
      rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_pow,
        derivIdealSheafIterate_comap k p h j A]
    · exact le_iSup (fun d : {c : ℕ → ℕ // u ≤ ∑ j ∈ Finset.range m, (m - j) * c j} =>
        ((List.range m).map (fun j =>
          derivIdealSheafIterate k (h ≫ p) j (A.comap h) ^ (d.1 j))).prod) ⟨c, hc⟩
  · refine le_trans (le_of_eq (tunedSheaf_eq_iSup k (h ≫ p) (A.comap h) m u)) (iSup_le ?_)
    rintro ⟨c, hc⟩
    refine le_trans (le_of_eq ?_) (AlgebraicGeometry.Scheme.IdealSheafData.comap_mono h
      (le_iSup (fun d : {c : ℕ → ℕ // u ≤ ∑ j ∈ Finset.range m, (m - j) * c j} =>
        ((List.range m).map (fun j => derivIdealSheafIterate k p j A ^ (d.1 j))).prod) ⟨c, hc⟩))
    refine Eq.trans (prod_map_range_congr_consolidated312 _
      (fun j => (derivIdealSheafIterate k p j A ^ c j).comap h) m ?_)
      (comap_prod_map_range h (fun j => derivIdealSheafIterate k p j A ^ c j) m).symm
    intro j _
    show derivIdealSheafIterate k (h ≫ p) j (A.comap h) ^ c j
        = (derivIdealSheafIterate k p j A ^ c j).comap h
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_pow, derivIdealSheafIterate_comap k p h j A]


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafBlowupSequence
section



section
variable {X : Scheme.{u}}

private theorem exists_affineOpen_mem_consolidated333 (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1.1 := by
  have hx : x ∈ (⨆ U : X.affineOpens, (U : X.Opens)) := by
    rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
    trivial
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨U, hU⟩

private theorem stalkIdeal_iSup_le_of_forall_consolidated333 {ι : Type}
    (F : ι → X.IdealSheafData) (x : X) (Jd : Ideal (X.presheaf.stalk x))
    (h : ∀ i, stalkIdeal (F i) x ≤ Jd) : stalkIdeal (iSup F) x ≤ Jd := by
  obtain ⟨U, hxU0⟩ := exists_affineOpen_mem_consolidated333 x
  have hxU : x ∈ U.1 := hxU0
  have hUeq : (iSup F).ideal U = ⨆ i, (F i).ideal U := by
    simp only [Scheme.IdealSheafData.ideal_iSup, iSup_apply]
  rw [stalkIdeal_eq_map_germ _ x U hxU, hUeq, (Ideal.gc_map_comap _).l_iSup]
  refine iSup_le fun i => ?_
  rw [← stalkIdeal_eq_map_germ (F i) x U hxU]
  exact h i


end

private theorem sum_map_range_eq_sum_range_consolidated333 (w : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map w).sum = ∑ j ∈ Finset.range n, w j := by
  induction n with
  | zero => simp
  | succ t ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp

section
variable {X : Scheme.{u}}

private theorem prod_map_range_pow_ite_eq_consolidated333 (f : ℕ → X.IdealSheafData) (s n : ℕ) :
    ((List.range (n + 1)).map (fun j => f j ^ (if j = 0 then s else 0))).prod = f 0 ^ s := by
  induction n with
  | zero => simp
  | succ t ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih]
      simp

private theorem mem_orderAtLeastLocus_prod_map_of_forall_consolidated333 (x : X)
    (g : ℕ → X.IdealSheafData) (w : ℕ → ℕ) (h : ∀ j, x ∈ orderAtLeastLocus (g j) (w j)) (l : List ℕ) :
    x ∈ orderAtLeastLocus ((l.map g).prod) ((l.map w).sum) := by
  induction l with
  | nil =>
      simp only [List.map_nil, List.prod_nil, List.sum_nil]
      rw [orderAtLeastLocus_zero]
      exact Set.mem_univ x
  | cons a t ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact inter_orderAtLeastLocus_subset_orderAtLeastLocus_mul _ _ _ _ ⟨h a, ih⟩


end

section
variable (k : Type u) [Field k]

theorem orderAtLeastLocus_subset_orderAtLeastLocus_tunedSheaf [IsNoetherianRing k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (A : Y.IdealSheafData) (m n : ℕ) :
    orderAtLeastLocus A m ⊆ orderAtLeastLocus (tunedSheaf k p A m n) n := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff_stalkIdeal_le_maximalIdeal_pow, tunedSheaf_eq_iSup]
  refine stalkIdeal_iSup_le_of_forall_consolidated333 _ x _ ?_
  rintro ⟨c, hc⟩
  refine (mem_orderAtLeastLocus_iff_stalkIdeal_le_maximalIdeal_pow _ n x).mp ?_
  have key := mem_orderAtLeastLocus_prod_map_of_forall_consolidated333 x (fun j => derivIdealSheafIterate k p j A ^ c j)
      (fun j => c j * (m - j))
      (fun j => orderAtLeastLocus_subset_orderAtLeastLocus_pow _ _ _
        (orderAtLeastLocus_subset_orderAtLeastLocus_derivIdealSheafIterate k p A j m hx)) (List.range m)
  have hn : n ≤ ((List.range m).map (fun j => c j * (m - j))).sum := by
    rw [sum_map_range_eq_sum_range_consolidated333]
    refine le_trans hc (le_of_eq ?_)
    exact Finset.sum_congr rfl fun j _ => Nat.mul_comm _ _
  exact orderAtLeastLocus_subset_of_le _ hn key

theorem orderAtLeastLocus_pow_mul_eq_orderAtLeastLocus [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (A : X.IdealSheafData)
    (m : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    orderAtLeastLocus (A ^ s) (m * s) = orderAtLeastLocus A m := by
  rw [mul_comm]
  exact orderAtLeastLocus_pow_mul k p A hs m

theorem orderAtLeastLocus_eq_of_pow_le_of_le_tunedSheaf [CharZero k]
    [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p] (I J : X.IdealSheafData) (m : ℕ)
    {s : ℕ} (hs : 1 ≤ s) (h1 : I ^ s ≤ J) (h2 : J ≤ tunedSheaf k p I m (m * s)) :
    orderAtLeastLocus J (m * s) = orderAtLeastLocus I m := by
  refine Set.Subset.antisymm ?_ ?_
  · rw [← orderAtLeastLocus_pow_mul_eq_orderAtLeastLocus k p I m hs]
    exact orderAtLeastLocus_subset_of_le_ideal h1 (m * s)
  · exact fun x hx => orderAtLeastLocus_subset_of_le_ideal h2 (m * s)
      (orderAtLeastLocus_subset_orderAtLeastLocus_tunedSheaf k p I m (m * s) hx)

theorem pow_le_tunedSheaf [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData)
    {m : ℕ} (hm : 1 ≤ m) (s : ℕ) :
    I ^ s ≤ tunedSheaf k p I m (m * s) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hsum : (m' + 1) * s ≤
      ∑ j ∈ Finset.range (m' + 1), (m' + 1 - j) * (if j = 0 then s else 0) := by
    have h := Finset.sum_eq_single_of_mem (s := Finset.range (m' + 1))
      (f := fun j => (m' + 1 - j) * (if j = 0 then s else 0)) 0
      (Finset.mem_range.mpr (Nat.succ_pos m'))
      (fun b _ hb => by simp [hb])
    rw [h]
    simp
  have hle := le_iSup
    (fun c : {c : ℕ → ℕ // (m' + 1) * s ≤ ∑ j ∈ Finset.range (m' + 1), (m' + 1 - j) * c j} =>
      ((List.range (m' + 1)).map (fun j => derivIdealSheafIterate k p j I ^ (c.1 j))).prod)
    ⟨fun j => if j = 0 then s else 0, hsum⟩
  rw [tunedSheaf_eq_iSup]
  refine le_trans (le_of_eq ?_) hle
  have := prod_map_range_pow_ite_eq_consolidated333 (fun j => derivIdealSheafIterate k p j I) s m'
  rw [this]
  simp


end

theorem exists_tuningExponent_eq {m : ℕ} (hm : 1 ≤ m) :
    ∃ r s : ℕ, m - 1 ≤ r ∧ tuningExponent m = r * lcmUpTo m ∧ 1 ≤ s ∧ tuningExponent m = m * s := by
  rcases Nat.lt_or_ge m 2 with h | h
  · have hm1 : m = 1 := by omega
    subst hm1
    refine ⟨1, 1, by omega, ?_, le_rfl, ?_⟩
    · rw [tuningExponent_one, lcmUpTo_one]
    · rw [tuningExponent_one]
  · obtain ⟨t, ht⟩ := dvd_lcmUpTo m m (by omega) le_rfl
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0, Nat.mul_zero] at ht
        have hpos := lcmUpTo_pos m
        omega
      · exact h0
    refine ⟨m - 1, (m - 1) * t, le_rfl, tuningExponent_of_two_le h, ?_, ?_⟩
    · have : 0 < (m - 1) * t := Nat.mul_pos (by omega) htpos
      omega
    · rw [tuningExponent_of_two_le h, ht]
      ring

section
variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (E : List X.IdealSheafData) (d : BlowupSequenceData X) (hiso : Smooth d.isoZero.hom) (hsnc : ∀ i, i < d.length → HasStrictNormalCrossingsWith (d.projectionToBase i ≫ p) (d.center i) (d.boundaryFrom E i))
include hiso hsnc

private theorem smooth_projectionToBase_comp_of_snc_consolidated333 :
    ∀ i, i ≤ d.length → Smooth (d.projectionToBase i ≫ p) := by
  intro i
  induction i with
  | zero =>
      intro _
      have := hiso
      rw [BlowupSequenceData.projectionToBase_zero]
      infer_instance
  | succ j ih =>
      intro hj
      have := ih (Nat.le_of_succ_le hj)
      have hb := smooth_comp_of_isBlowupAlongIdealSheaf (hsnc j hj) (d.isBlowup j hj)
      rw [BlowupSequenceData.projectionToBase_succ, Category.assoc]
      exact hb

private theorem locallyOfFiniteType_projectionToBase_comp_of_snc_consolidated333 :
    ∀ i, i ≤ d.length → LocallyOfFiniteType (d.projectionToBase i ≫ p) := by
  intro i hi
  have := smooth_projectionToBase_comp_of_snc_consolidated333 k p E d hiso hsnc i hi
  infer_instance


end

section
variable (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k]

private theorem pow_le_and_le_tunedSheaf_of_isBlowupAlongIdealSheaf_consolidated333 {P P₁ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p] (π : P₁ ⟶ P)
    (p₁ : P₁ ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p₁] (hp₁ : p₁ = π ≫ p)
    (Z : P.IdealSheafData) (E : List P.IdealSheafData) (hZ : HasStrictNormalCrossingsWith p Z E)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (m s : ℕ) (A B : P.IdealSheafData) (A' B' : P₁.IdealSheafData)
    (hA : A ≤ Z ^ m)
    (hA' : Blowup.exceptionalIdeal π Z ^ m * A' = A.comap π)
    (hB' : Blowup.exceptionalIdeal π Z ^ (m * s) * B' = B.comap π)
    (h1 : A ^ s ≤ B) (h2 : B ≤ tunedSheaf k p A m (m * s)) :
    A' ^ s ≤ B' ∧ B' ≤ tunedSheaf k p₁ A' m (m * s) := by
  have : IsLocallyNoetherian P₁ := LocallyOfFiniteType.isLocallyNoetherian p₁
  have : LocallyOfFiniteType (π ≫ p) := by
    rw [← hp₁]
    infer_instance
  have hF : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hπ
  constructor
  · refine hF.le_of_pow_mul_le_pow_mul (m * s) ?_
    have hcm : (A.comap π) ^ s ≤ B.comap π := by
      rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_pow]
      exact Scheme.IdealSheafData.comap_mono π h1
    calc Blowup.exceptionalIdeal π Z ^ (m * s) * A' ^ s
        = (Blowup.exceptionalIdeal π Z ^ m * A') ^ s := by rw [mul_pow, ← pow_mul]
      _ = (A.comap π) ^ s := by rw [hA']
      _ ≤ B.comap π := hcm
      _ = Blowup.exceptionalIdeal π Z ^ (m * s) * B' := hB'.symm
  · refine hF.le_of_pow_mul_le_pow_mul (m * s) ?_
    have hct : A' = controlledTransform π Z A m hπ hA :=
      eq_controlledTransform_of_mul_eq_comap π Z A m hπ hA A' hA'
    calc Blowup.exceptionalIdeal π Z ^ (m * s) * B' = B.comap π := hB'
      _ ≤ (tunedSheaf k p A m (m * s)).comap π := Scheme.IdealSheafData.comap_mono π h2
      _ ≤ Blowup.exceptionalIdeal π Z ^ (m * s) *
            tunedSheaf k p₁ (controlledTransform π Z A m hπ hA) m (m * s) :=
          comap_tunedSheaf_le_exceptionalIdeal_pow_mul k p π p₁ hp₁ Z E hZ hπ A m hA (m * s)
      _ = Blowup.exceptionalIdeal π Z ^ (m * s) * tunedSheaf k p₁ A' m (m * s) := by rw [hct]

private theorem orderAtLeastLocus_eq_and_exceptionalIdeal_dvd_of_blowupSequence_consolidated333 {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p] (I J : X.IdealSheafData) (m s : ℕ)
    (hs : 1 ≤ s) (h1 : I ^ s ≤ J) (h2 : J ≤ tunedSheaf k p I m (m * s))
    (E : List X.IdealSheafData) (d : BlowupSequenceData X)
    (hiso : Smooth d.isoZero.hom)
    (hft : ∀ i, i ≤ d.length → LocallyOfFiniteType (d.projectionToBase i ≫ p))
    (hsnc : ∀ i, i < d.length → HasStrictNormalCrossingsWith (d.projectionToBase i ≫ p) (d.center i) (d.boundaryFrom E i))
    (hord : ∀ i, i < d.length →
      orderAtLeastLocus (d.controlledTransform J (m * s) i) (m * s) = orderAtLeastLocus (d.controlledTransform I m i) m →
      ((d.center i).support : Set ↥(d.obj i)) ⊆ orderAtLeastLocus (d.controlledTransform I m i) m) :
    (∀ i, i ≤ d.length →
        orderAtLeastLocus (d.controlledTransform J (m * s) i) (m * s) = orderAtLeastLocus (d.controlledTransform I m i) m) ∧
    (∀ i, i < d.length → ∃ B : (d.obj (i + 1)).IdealSheafData,
        Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * B = (d.controlledTransform I m i).comap (d.map i)) ∧
    (∀ i, i < d.length → ∃ B : (d.obj (i + 1)).IdealSheafData,
        Blowup.exceptionalIdeal (d.map i) (d.center i) ^ (m * s) * B =
          (d.controlledTransform J (m * s) i).comap (d.map i)) := by
  have hsm : ∀ i, i ≤ d.length → Smooth (d.projectionToBase i ≫ p) :=
    smooth_projectionToBase_comp_of_snc_consolidated333 k p E d hiso hsnc
  have key : ∀ i, i ≤ d.length →
      (d.controlledTransform I m i) ^ s ≤ d.controlledTransform J (m * s) i ∧
      ∀ [_hq : LocallyOfFiniteType (d.projectionToBase i ≫ p)],
        d.controlledTransform J (m * s) i ≤
          tunedSheaf k (d.projectionToBase i ≫ p) (d.controlledTransform I m i) m (m * s) := by
    intro i
    induction i with
    | zero =>
        intro _
        constructor
        · simp only [BlowupSequenceData.controlledTransform_zero]
          rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_pow]
          exact Scheme.IdealSheafData.comap_mono _ h1
        · intro hq0
          have := hq0
          have := hiso
          simp only [BlowupSequenceData.controlledTransform_zero]
          have heq : (tunedSheaf k p I m (m * s)).comap d.isoZero.hom
              = tunedSheaf k (d.projectionToBase 0 ≫ p) (I.comap d.isoZero.hom) m (m * s) :=
            comap_tunedSheaf_of_smooth k p d.isoZero.hom (d.projectionToBase 0 ≫ p) rfl I m (m * s)
          rw [← heq]
          exact Scheme.IdealSheafData.comap_mono _ h2
    | succ j ih =>
        intro hj
        have hj' : j < d.length := hj
        have hjle : j ≤ d.length := Nat.le_of_succ_le hj
        obtain ⟨ih1, ih2⟩ := ih hjle
        have := hsm j hjle
        have := hft j hjle
        have := hft (j + 1) hj
        have hcosj : orderAtLeastLocus (d.controlledTransform J (m * s) j) (m * s)
            = orderAtLeastLocus (d.controlledTransform I m j) m :=
          orderAtLeastLocus_eq_of_pow_le_of_le_tunedSheaf k (d.projectionToBase j ≫ p) _ _ m hs ih1 ih2
        have hordj := hord j hj' hcosj
        have hAZ : d.controlledTransform I m j ≤ d.center j ^ m :=
          le_pow_of_hasStrictNormalCrossingsWith (d.projectionToBase j ≫ p) (d.center j) _ (d.boundaryFrom E j) (hsnc j hj') m hordj
        have hBZ : d.controlledTransform J (m * s) j ≤ d.center j ^ (m * s) := by
          refine le_pow_of_hasStrictNormalCrossingsWith (d.projectionToBase j ≫ p) (d.center j) _ (d.boundaryFrom E j)
            (hsnc j hj') (m * s) ?_
          rw [hcosj]
          exact hordj
        have : IsLocallyNoetherian (d.obj (j + 1)) :=
          LocallyOfFiniteType.isLocallyNoetherian (d.projectionToBase (j + 1) ≫ p)
        obtain ⟨A1, hA1, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map j) (d.center j)
          (d.controlledTransform I m j) m (d.isBlowup j hj') hAZ
        obtain ⟨B1, hB1, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map j) (d.center j)
          (d.controlledTransform J (m * s) j) (m * s) (d.isBlowup j hj') hBZ
        have hA1' : Blowup.exceptionalIdeal (d.map j) (d.center j) ^ m * d.controlledTransform I m (j + 1)
            = (d.controlledTransform I m j).comap (d.map j) :=
          d.pow_exceptionalIdeal_mul_controlledTransform_succ I m j ⟨A1, hA1⟩
        have hB1' : Blowup.exceptionalIdeal (d.map j) (d.center j) ^ (m * s) *
              d.controlledTransform J (m * s) (j + 1)
            = (d.controlledTransform J (m * s) j).comap (d.map j) :=
          d.pow_exceptionalIdeal_mul_controlledTransform_succ J (m * s) j ⟨B1, hB1⟩
        have hp1 : d.projectionToBase (j + 1) ≫ p = d.map j ≫ (d.projectionToBase j ≫ p) := by
          rw [BlowupSequenceData.projectionToBase_succ, Category.assoc]
        obtain ⟨r1, r2⟩ := pow_le_and_le_tunedSheaf_of_isBlowupAlongIdealSheaf_consolidated333 k (d.projectionToBase j ≫ p) (d.map j)
          (d.projectionToBase (j + 1) ≫ p) hp1
          (d.center j) (d.boundaryFrom E j) (hsnc j hj') (d.isBlowup j hj') m s
          (d.controlledTransform I m j) (d.controlledTransform J (m * s) j) (d.controlledTransform I m (j + 1))
          (d.controlledTransform J (m * s) (j + 1)) hAZ hA1' hB1' ih1 ih2
        refine ⟨r1, ?_⟩
        intro _
        exact r2
  have hcos : ∀ i, i ≤ d.length →
      orderAtLeastLocus (d.controlledTransform J (m * s) i) (m * s) = orderAtLeastLocus (d.controlledTransform I m i) m := by
    intro i hi
    have := hsm i hi
    have := hft i hi
    exact orderAtLeastLocus_eq_of_pow_le_of_le_tunedSheaf k (d.projectionToBase i ≫ p) _ _ m hs
      (key i hi).1 (key i hi).2
  have hdiv : ∀ i, i < d.length →
      (d.controlledTransform I m i ≤ d.center i ^ m) ∧
        (d.controlledTransform J (m * s) i ≤ d.center i ^ (m * s)) := by
    intro i hi
    have := hsm i (Nat.le_of_succ_le hi)
    have hordi := hord i hi (hcos i (Nat.le_of_succ_le hi))
    constructor
    · exact le_pow_of_hasStrictNormalCrossingsWith (d.projectionToBase i ≫ p) (d.center i) _ (d.boundaryFrom E i) (hsnc i hi) m hordi
    · refine le_pow_of_hasStrictNormalCrossingsWith (d.projectionToBase i ≫ p) (d.center i) _ (d.boundaryFrom E i)
        (hsnc i hi) (m * s) ?_
      rw [hcos i (Nat.le_of_succ_le hi)]
      exact hordi
  refine ⟨hcos, ?_, ?_⟩
  · intro i hi
    have := hft (i + 1) hi
    have : IsLocallyNoetherian (d.obj (i + 1)) :=
      LocallyOfFiniteType.isLocallyNoetherian (d.projectionToBase (i + 1) ≫ p)
    obtain ⟨B, hB, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map i) (d.center i)
      (d.controlledTransform I m i) m (d.isBlowup i hi) (hdiv i hi).1
    exact ⟨B, hB⟩
  · intro i hi
    have := hft (i + 1) hi
    have : IsLocallyNoetherian (d.obj (i + 1)) :=
      LocallyOfFiniteType.isLocallyNoetherian (d.projectionToBase (i + 1) ≫ p)
    obtain ⟨B, hB, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map i) (d.center i)
      (d.controlledTransform J (m * s) i) (m * s) (d.isBlowup i hi) (hdiv i hi).2
    exact ⟨B, hB⟩


end

theorem isMarked_iff_of_pow_le_of_le_tunedSheaf : IsMarkedIffOfPowLeOfLeTunedSheaf.{u} := by
  intro k hk1 hk2 hk3 X p hp1 hp2 I m _hm _hmax s hs J h1 h2 E d
  have hiso : Smooth d.isoZero.hom := inferInstance
  constructor
  · constructor
    · intro hI
      have hft := locallyOfFiniteType_projectionToBase_comp_of_snc_consolidated333 k p E d hiso hI.center_snc
      obtain ⟨hc, -, hdivJ⟩ := orderAtLeastLocus_eq_and_exceptionalIdeal_dvd_of_blowupSequence_consolidated333 k p I J m s hs h1 h2 E d
        hiso hft hI.center_snc (fun i hi _ => hI.center_order i hi)
      exact { divisible := hdivJ
              center_order := fun i hi => by
                rw [hc i (Nat.le_of_succ_le hi)]
                exact hI.center_order i hi
              center_smooth := hI.center_smooth
              center_snc := hI.center_snc }
    · intro hJ
      have hft := locallyOfFiniteType_projectionToBase_comp_of_snc_consolidated333 k p E d hiso hJ.center_snc
      obtain ⟨hc, hdivI, -⟩ := orderAtLeastLocus_eq_and_exceptionalIdeal_dvd_of_blowupSequence_consolidated333 k p I J m s hs h1 h2 E d
        hiso hft hJ.center_snc
        (fun i hi heq => by
          rw [← heq]
          exact hJ.center_order i hi)
      exact { divisible := hdivI
              center_order := fun i hi => by
                rw [← hc i (Nat.le_of_succ_le hi)]
                exact hJ.center_order i hi
              center_smooth := hJ.center_smooth
              center_snc := hJ.center_snc }
  · intro hI i hi
    have hft := locallyOfFiniteType_projectionToBase_comp_of_snc_consolidated333 k p E d hiso hI.center_snc
    obtain ⟨hc, -, -⟩ := orderAtLeastLocus_eq_and_exceptionalIdeal_dvd_of_blowupSequence_consolidated333 k p I J m s hs h1 h2 E d
      hiso hft hI.center_snc (fun i hi _ => hI.center_order i hi)
    exact hc i hi

theorem isMarked_iff_balanced_tunedSheaf : IsMarkedIffBalancedTunedSheaf.{u} := by
  intro k hk1 hk2 hk3 X p hp1 hp2 I m hm hmax E d
  obtain ⟨r, s, hr, hre, hs, hms⟩ := exists_tuningExponent_eq hm
  have hWe : balancedTunedSheaf k p I m = tunedSheaf k p I m (m * s) := by rw [balancedTunedSheaf_eq, hms]
  have h1 : I ^ s ≤ balancedTunedSheaf k p I m := by
    rw [hWe]
    exact pow_le_tunedSheaf k p I hm s
  have h2 : balancedTunedSheaf k p I m ≤ tunedSheaf k p I m (m * s) := le_of_eq hWe
  have hmarked := isMarked_iff_of_pow_le_of_le_tunedSheaf.{u} k X p I m hm hmax s hs
    (balancedTunedSheaf k p I m) h1 h2 E d
  rw [← hms] at hmarked
  have he1 : 1 ≤ tuningExponent m := by
    rw [hms]
    exact Nat.mul_pos hm hs
  refine ⟨hmarked.1, hmarked.2, ?_, ?_⟩
  · have h5 := isMaxContactInvariantTunedSheaf.{u} k X p I m hm hmax
      (tuningExponent m) he1
    rw [balancedTunedSheaf_eq]
    exact h5
  · have h8 := isDerivBalanced_tunedSheaf_mul_lcmUpTo.{u} k X p I m hm hmax r hr
    rw [← hre] at h8
    rw [balancedTunedSheaf_eq]
    exact h8

theorem tunedSheafProperties_of_succ_le_of_mul_le (h1 : TunedSheafSuccLe.{u}) (h2 : TunedSheafMulLeAdd.{u}) :
    TunedSheafProperties.{u} where
  isMarked_tuned_iff := isMarked_iff_balanced_tunedSheaf.{u}
  tunedSheaf_succ_le := h1
  tunedSheaf_mul_le := h2
  derivIdealSheaf_tunedSheaf_succ := derivIdealSheaf_tunedSheaf_succ.{u}
  derivIdealSheafIter_pred_tunedSheaf := maxContactIdealTunedSheafEq.{u}
  derivIdealSheafIter_mul_derivIdealSheaf_le_tunedSheaf :=
    isMaxContactInvariantTunedSheaf.{u}
  tunedSheaf_mul_eq := tunedSheaf_mul_eq_add.{u}
  tunedSheaf_pow := tunedSheaf_pow_eq_mul.{u}
  derivIdealSheafIter_tunedSheaf_pow_le := isDerivBalanced_tunedSheaf_mul_lcmUpTo.{u}
  coSupport_tunedSheaf_eq_and_orderLE := orderAtLeastLocus_tunedSheaf_eq_and_order_le.{u}
  isMarked_iff_of_pow_le_of_le_tunedSheaf := isMarked_iff_of_pow_le_of_le_tunedSheaf.{u}

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDivisorBlowup
section

open Opposite TopologicalSpace

section

section
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (V : U.toScheme.Opens)

private theorem etaleChart_restrictOpens_map_comp_affineSpaceFinToSpec_consolidated267 :
    (V.ι ≫ c.map) ≫ affineSpaceFinToSpec k m = V.ι ≫ (U.ι ≫ p) := by
  rw [Category.assoc, c.comp_struct]

private theorem etaleChart_restrictOpens_map_etale_consolidated267 :
    Etale (V.ι ≫ c.map) := by
  have : Etale c.map := c.isEtale
  infer_instance


end

def EtaleChart.restrictOpens {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (V : U.toScheme.Opens) : EtaleChart (U.ι ≫ p) V m where
  map := V.ι ≫ c.map
  comp_struct := etaleChart_restrictOpens_map_comp_affineSpaceFinToSpec_consolidated267 c V
  isEtale := etaleChart_restrictOpens_map_etale_consolidated267 c V

@[simp]
theorem EtaleChart.restrictOpens_map {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (V : U.toScheme.Opens) :
    (c.restrictOpens V).map = V.ι ≫ c.map := rfl

section
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ}

theorem EtaleChart.restrictIdeal_coordIdeal (c : EtaleChart p U m)
    (V : U.toScheme.Opens) (T : Finset (Fin m)) :
    restrictIdeal (c.coordIdeal T) V = (c.restrictOpens V).coordIdeal T := by
  simp only [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.restrictOpens_map,
    Scheme.IdealSheafData.comap_comp]

theorem EtaleChart.coordIdeal_ideal_eq_span (c : EtaleChart p U m)
    {V : U.toScheme.Opens} (hV : IsAffineOpen V) (T : Finset (Fin m)) :
    (c.coordIdeal T).ideal ⟨V, hV⟩ = Ideal.span ((c.restrictOpens V).coord '' ↑T) :=
  EtaleChart.ideal_eq_span_coord (c.restrictOpens V) hV (c.coordIdeal T) T
    (c.restrictIdeal_coordIdeal V T)

theorem EtaleChart.coordIdeal_singleton_ideal_eq_span (c : EtaleChart p U m)
    {V : U.toScheme.Opens} (hV : IsAffineOpen V) (i : Fin m) :
    (c.coordIdeal {i}).ideal ⟨V, hV⟩ = Ideal.span {(c.restrictOpens V).coord i} := by
  rw [c.coordIdeal_ideal_eq_span hV {i}, Finset.coe_singleton, Set.image_singleton]

theorem EtaleChart.saturation_mul_coordIdeal (c : EtaleChart p U m)
    (j s : Fin m) (hjs : j ≠ s)
    [QuasiCompact (saturationι (c.coordIdeal {s})
      (c.coordIdeal {j} * c.coordIdeal {s}))] :
    saturation (c.coordIdeal {s}) (c.coordIdeal {j} * c.coordIdeal {s}) = c.coordIdeal {j} := by
  have key : ∀ V : U.toScheme.affineOpens,
      (saturation (c.coordIdeal {s}) (c.coordIdeal {j} * c.coordIdeal {s})).ideal V =
        (c.coordIdeal {j}).ideal V := by
    intro V
    have ht : (c.coordIdeal {s}).ideal V = Ideal.span {(c.restrictOpens V.1).coord s} :=
      c.coordIdeal_singleton_ideal_eq_span V.2 s
    have hu : (c.coordIdeal {j}).ideal V = Ideal.span {(c.restrictOpens V.1).coord j} :=
      c.coordIdeal_singleton_ideal_eq_span V.2 j
    have hfactor : (c.coordIdeal {j} * c.coordIdeal {s}).ideal V =
        Ideal.span {(c.restrictOpens V.1).coord s} * (c.coordIdeal {j}).ideal V := by
      rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, ht]
      exact mul_comm _ _
    have hJ : ∀ g : Γ(U.toScheme, V.1),
        (c.restrictOpens V.1).coord s * g ∈ (c.coordIdeal {j}).ideal V →
          g ∈ (c.coordIdeal {j}).ideal V := by
      intro g hg
      rw [hu] at hg ⊢
      exact mem_span_coord_of_coord_mul_mem V.2 (c.restrictOpens V.1) hjs g hg
    exact saturation_ideal_eq_of_eq_mul _ _ V _ ht _ hfactor hJ
  exact Scheme.IdealSheafData.ext (funext key)

theorem EtaleChart.saturation_coordIdeal_self (c : EtaleChart p U m) (s : Fin m)
    [QuasiCompact (saturationι (c.coordIdeal {s}) (c.coordIdeal {s}))] :
    saturation (c.coordIdeal {s}) (c.coordIdeal {s}) = ⊤ := by
  have key : ∀ V : U.toScheme.affineOpens,
      (saturation (c.coordIdeal {s}) (c.coordIdeal {s})).ideal V = ⊤ := by
    intro V
    have ht : (c.coordIdeal {s}).ideal V = Ideal.span {(c.restrictOpens V.1).coord s} :=
      c.coordIdeal_singleton_ideal_eq_span V.2 s
    exact saturation_ideal_eq_top_of_span_pow_le (c.coordIdeal {s}) (c.coordIdeal {s}) V
      ((c.restrictOpens V.1).coord s) ht 1 (by simp [ht])
  ext V
  simp [key V, Scheme.IdealSheafData.ideal_top, Pi.top_apply]

private theorem mem_span_coord_of_coord_pow_mul_mem_consolidated267 (hU : IsAffineOpen U) (c : EtaleChart p U m) {j s : Fin m} (hjs : j ≠ s) :
    ∀ (n : ℕ) (x : ↑(X.presheaf.obj (op U))),
      c.coord s ^ n * x ∈ Ideal.span {c.coord j} → x ∈ Ideal.span {c.coord j} := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simpa using hx
  | succ n ih =>
      intro x hx
      refine mem_span_coord_of_coord_mul_mem hU c hjs x (ih (c.coord s * x) ?_)
      have h : c.coord s ^ n * (c.coord s * x) = c.coord s ^ (n + 1) * x := by ring
      rw [h]
      exact hx

theorem EtaleChart.saturation_coordIdeal_of_ne (c : EtaleChart p U m)
    (j s : Fin m) (hjs : j ≠ s)
    [QuasiCompact (saturationι (c.coordIdeal {s}) (c.coordIdeal {j}))] :
    saturation (c.coordIdeal {s}) (c.coordIdeal {j}) = c.coordIdeal {j} := by
  ext V f
  have hVs : (c.coordIdeal {s}).ideal V = Ideal.span {(c.restrictOpens V.1).coord s} :=
    c.coordIdeal_singleton_ideal_eq_span V.2 s
  have hVj : (c.coordIdeal {j}).ideal V = Ideal.span {(c.restrictOpens V.1).coord j} :=
    c.coordIdeal_singleton_ideal_eq_span V.2 j
  rw [mem_saturation_ideal_iff (c.coordIdeal {s}) (c.coordIdeal {j}) V
      ((c.restrictOpens V.1).coord s) hVs f, hVj]
  constructor
  · rintro ⟨n, hn⟩
    exact mem_span_coord_of_coord_pow_mul_mem_consolidated267 V.2 (c.restrictOpens V.1) hjs n f hn
  · intro hf
    exact ⟨0, by simpa using hf⟩


end

namespace BlowupChart

variable {X X₁ : Scheme.{u}} {k : Type u} [Field k]
  {p : X ⟶ Spec (CommRingCat.of k)} {π : X₁ ⟶ X} {U : X.Opens} {m : ℕ}
  {c : EtaleChart p U m} {S : Finset (Fin m)} {s : Fin m}

section
variable (B : BlowupChart π c S s) (Z D : X.IdealSheafData) [QuasiCompact (strictTransformι π Z D)] (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
include hs hZ

theorem restrictIdeal_strictTransform_of_mem_of_ne (j : Fin m) (hj : j ∈ S) (hjs : j ≠ s)
    (hD : restrictIdeal D U = c.coordIdeal {j}) :
    restrictIdeal (Blowup.strictTransform π Z D) B.domain = B.chart.coordIdeal {j} := by
  have hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    inferInstanceAs (QuasiCompact (strictTransformι π Z D))
  have hE : restrictIdeal (Z.comap π) B.domain = B.chart.coordIdeal {s} := by
    have h := B.restrictIdeal_exceptionalIdeal Z hs hZ
    rwa [Blowup.exceptionalIdeal_eq_comap] at h
  have hDrestrict : restrictIdeal (D.comap π) B.domain =
      B.chart.coordIdeal {j} * B.chart.coordIdeal {s} :=
    B.restrictIdeal_comap_coordIdeal_of_mem D j hj hjs hD
  have hq := quasiCompact_saturationι_restrictIdeal (Z.comap π) (D.comap π) B.domain
  rw [hE, hDrestrict] at hq
  have := hq
  rw [strictTransform_eq_saturation, restrictIdeal_saturation (Z.comap π) (D.comap π) B.domain,
    hE, hDrestrict]
  exact B.chart.saturation_mul_coordIdeal j s hjs

theorem restrictIdeal_strictTransform_coordIdeal_self (hD : restrictIdeal D U = c.coordIdeal {s}) :
    restrictIdeal (Blowup.strictTransform π Z D) B.domain = ⊤ := by
  have hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    inferInstanceAs (QuasiCompact (strictTransformι π Z D))
  have hE : restrictIdeal (Z.comap π) B.domain = B.chart.coordIdeal {s} := by
    have h := B.restrictIdeal_exceptionalIdeal Z hs hZ
    rwa [Blowup.exceptionalIdeal_eq_comap] at h
  have hDrestrict : restrictIdeal (D.comap π) B.domain = B.chart.coordIdeal {s} :=
    B.restrictIdeal_comap_coordIdeal_self D hD
  have hq := quasiCompact_saturationι_restrictIdeal (Z.comap π) (D.comap π) B.domain
  rw [hE, hDrestrict] at hq
  have := hq
  rw [strictTransform_eq_saturation, restrictIdeal_saturation (Z.comap π) (D.comap π) B.domain,
    hE, hDrestrict]
  exact B.chart.saturation_coordIdeal_self s

theorem restrictIdeal_strictTransform_coordIdeal_of_notMem (j : Fin m) (hj : j ∉ S)
    (hD : restrictIdeal D U = c.coordIdeal {j}) :
    restrictIdeal (Blowup.strictTransform π Z D) B.domain = B.chart.coordIdeal {j} := by
  have hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    inferInstanceAs (QuasiCompact (strictTransformι π Z D))
  have hjs : j ≠ s := by
    rintro rfl
    exact hj hs
  have hE : restrictIdeal (Z.comap π) B.domain = B.chart.coordIdeal {s} := by
    have h := B.restrictIdeal_exceptionalIdeal Z hs hZ
    rwa [Blowup.exceptionalIdeal_eq_comap] at h
  have hDrestrict : restrictIdeal (D.comap π) B.domain = B.chart.coordIdeal {j} :=
    B.restrictIdeal_comap_coordIdeal_of_not_mem D j hj hD
  have hq := quasiCompact_saturationι_restrictIdeal (Z.comap π) (D.comap π) B.domain
  rw [hE, hDrestrict] at hq
  have := hq
  rw [strictTransform_eq_saturation, restrictIdeal_saturation (Z.comap π) (D.comap π) B.domain,
    hE, hDrestrict]
  exact B.chart.saturation_coordIdeal_of_ne j s hjs

theorem restrictIdeal_strictTransform_coordIdeal (j : Fin m) (hD : restrictIdeal D U = c.coordIdeal {j}) :
    restrictIdeal (Blowup.strictTransform π Z D) B.domain =
      if j = s then ⊤ else B.chart.coordIdeal {j} := by
  by_cases hj : j = s
  · rw [if_pos hj]
    have hD' : restrictIdeal D U = c.coordIdeal {s} := by rw [hD, hj]
    exact B.restrictIdeal_strictTransform_coordIdeal_self Z D hs hZ hD'
  · rw [if_neg hj]
    by_cases hjS : j ∈ S
    · exact B.restrictIdeal_strictTransform_of_mem_of_ne Z D hs hZ j hjS hj hD
    · exact B.restrictIdeal_strictTransform_coordIdeal_of_notMem Z D hs hZ j hjS hD


end

theorem restrictIdeal_strictTransform_of_eq_top (B : BlowupChart π c S s)
    (Z D : X.IdealSheafData) (hD : restrictIdeal D U = ⊤) :
    restrictIdeal (Blowup.strictTransform π Z D) B.domain = ⊤ := by
  have h1 : restrictIdeal (D.comap π) B.domain = ⊤ := B.restrictIdeal_comap_top D hD
  have h2 : D.comap π ≤ Blowup.strictTransform π Z D := comap_le_strictTransform π Z D
  have h3 : restrictIdeal (D.comap π) B.domain ≤
      restrictIdeal (Blowup.strictTransform π Z D) B.domain := by
    rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι]
    exact Scheme.IdealSheafData.comap_mono (Scheme.Opens.ι B.domain) h2
  rw [h1] at h3
  exact le_antisymm le_top h3

end BlowupChart


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactStrictTransform
section

open TopologicalSpace


section

variable (k : Type u) [Field k] {P₁ : Scheme.{u}} (q : P₁ ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType q]

def IsMaxContactHypersurfaceAt (A₁ : P₁.IdealSheafData) (m : ℕ) (H₁ : P₁.IdealSheafData) (x : P₁) : Prop :=
  ∃ U : P₁.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ((Disjoint (orderAtLeastLocus A₁ m) (U : Set ↥P₁) ∧ restrictIdeal H₁ U = ⊤) ∨
      (∃ (n : ℕ) (c : EtaleChart q U n) (j : Fin n),
        restrictIdeal H₁ U = c.coordIdeal {j} ∧ IsMaxContactCoord k q A₁ m c j))

end

section

private theorem idealSheafData_eq_of_forall_ideal_eq_consolidated332 {Y : Scheme.{u}} {A B : Y.IdealSheafData}
    (h : ∀ V : Y.affineOpens, A.ideal V = B.ideal V) : A = B :=
  Scheme.IdealSheafData.ext (funext h)

section
variable {X : Scheme.{u}}

private theorem mul_le_right_idealSheafData_consolidated332 (I J : X.IdealSheafData) :
    I * J ≤ J := by
  rw [le_iff_forall_stalkIdeal_le]
  intro x
  rw [stalkIdeal_mul]
  exact Ideal.mul_le.2 fun r _ s hs => Ideal.mul_mem_left _ _ hs

private theorem mul_le_left_idealSheafData_consolidated332 (I J : X.IdealSheafData) :
    I * J ≤ I := by
  rw [le_iff_forall_stalkIdeal_le]
  intro x
  rw [stalkIdeal_mul]
  exact Ideal.mul_le.2 fun r hr s _ => Ideal.mul_mem_right _ _ hr

private theorem restrictIdeal_le_of_le_opens_consolidated332 {I J : X.IdealSheafData}
    {U V : X.Opens} (hVU : V ≤ U) (h : restrictIdeal I U ≤ restrictIdeal J U) :
    restrictIdeal I V ≤ restrictIdeal J V := by
  have hI : ∀ K : X.IdealSheafData,
      restrictIdeal K V = (restrictIdeal K U).comap (X.homOfLE hVU) := by
    intro K
    rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
      Scheme.homOfLE_ι]
  rw [hI I, hI J]
  exact Scheme.IdealSheafData.comap_mono _ h


end

private theorem saturation_of_eq_top_consolidated332 {Y : Scheme.{u}} (F T : Y.IdealSheafData)
    (hqc : QuasiCompact (saturationι F T)) (hF : F = ⊤) :
    saturation F T = T := by
  have := hqc
  refine idealSheafData_eq_of_forall_ideal_eq_consolidated332 (fun V => ?_)
  refine saturation_ideal_eq_of_isUnit F T V 1 ?_ isUnit_one
  rw [hF]
  simp

private theorem restrictIdeal_strictTransform_eq_of_comap_eq_top_consolidated332 {P P₁ : Scheme.{u}} (π : P₁ ⟶ P)
    (Z H : P.IdealSheafData) [QuasiCompact (strictTransformι π Z H)] (V : P.Opens)
    (hZtop : Z.comap ((π ⁻¹ᵁ V).ι ≫ π) = ⊤) :
    restrictIdeal (Blowup.strictTransform π Z H) (π ⁻¹ᵁ V) = restrictIdeal (H.comap π) (π ⁻¹ᵁ V) := by
  have hqc : QuasiCompact (saturationι (Z.comap ((π ⁻¹ᵁ V).ι ≫ π))
      (H.comap ((π ⁻¹ᵁ V).ι ≫ π))) := by
    rw [← strictTransformι_eq_saturationι]
    exact quasiCompact_strictTransformι_comp_ι π Z H (π ⁻¹ᵁ V)
  have hsat : Blowup.strictTransform ((π ⁻¹ᵁ V).ι ≫ π) Z H = H.comap ((π ⁻¹ᵁ V).ι ≫ π) := by
    rw [strictTransform_eq_saturation]
    exact saturation_of_eq_top_consolidated332 _ _ hqc hZtop
  rw [restrictIdeal_strictTransform π Z H (π ⁻¹ᵁ V), hsat, restrictIdeal_eq_comap_ι,
    Scheme.IdealSheafData.comap_comp]

private noncomputable def etaleChartPullbackOfIsIso {P P₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : P ⟶ Spec (CommRingCat.of k)} (π : P₁ ⟶ P) {V : P.Opens} {n : ℕ}
    (c : EtaleChart p V n) [IsIso (π ∣_ V)] : EtaleChart (π ≫ p) (π ⁻¹ᵁ V) n where
  map := (π ∣_ V) ≫ c.map
  comp_struct := by
    rw [Category.assoc, c.comp_struct, ← Category.assoc, morphismRestrict_ι, Category.assoc]
  isEtale := by
    have := c.isEtale
    infer_instance

private theorem pullbackChartIso_coordIdeal_consolidated332 {P P₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : P ⟶ Spec (CommRingCat.of k)} (π : P₁ ⟶ P) {V : P.Opens} {n : ℕ}
    (c : EtaleChart p V n) [IsIso (π ∣_ V)] (T : Finset (Fin n)) :
    (etaleChartPullbackOfIsIso π c).coordIdeal T = (c.coordIdeal T).comap (π ∣_ V) := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  show (coordSubspaceIdeal k n T).comap ((π ∣_ V) ≫ c.map) = _
  rw [Scheme.IdealSheafData.comap_comp]

section
variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [Smooth p] (A : X.IdealSheafData) (μ : ℕ) (H : X.IdealSheafData) (hH : IsMaxContactHypersurface k p A μ H)
include hH

private theorem exists_etaleChart_of_isMaxContactHypersurface_consolidated332 (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal H U = ⊤ ∨ ∃ j, restrictIdeal H U = c.coordIdeal {j} := by
  obtain ⟨U, hU, hxU, hcase⟩ := hH x
  rcases hcase with ⟨-, htop⟩ | ⟨n, c, j, hHU, -⟩
  · obtain ⟨V, nV, hxV, hVU, hVaff, ⟨cV⟩⟩ := exists_etaleChart_le p x U hxU
    exact ⟨V, hxV, nV, cV, Or.inl (restrictIdeal_eq_top_of_le H hVU htop)⟩
  · exact ⟨U, hxU, n, c, Or.inr ⟨j, hHU⟩⟩

private theorem inStrictNormalCrossingPosition_singleton_of_isMaxContactHypersurface_consolidated332 :
    InStrictNormalCrossingPosition p [H] := by
  rw [inStrictNormalCrossingPosition_iff]
  constructor
  · intro D hD
    simp only [List.mem_singleton] at hD
    subst hD
    exact isSmoothDivisor_of_locally_coordIdeal D
      (fun x => exists_etaleChart_of_isMaxContactHypersurface_consolidated332 p A μ D hH x)
  · intro x
    refine inStrictNormalCrossingPositionAt_of_exists_etaleChart ?_
    obtain ⟨U, hxU, n, c, hcase⟩ := exists_etaleChart_of_isMaxContactHypersurface_consolidated332 p A μ H hH x
    rcases hcase with htop | ⟨j, hj⟩
    · refine ⟨U, hxU, n, c, (fun _ => none), ?_, ?_, ?_⟩
      · intro i _ i' _ t h1 _
        simp at h1
      · intro i hi _
        have hi0 : i = 0 := Nat.lt_one_iff.mp hi
        subst hi0
        simpa using htop
      · intro i _ t h
        simp at h
    · refine ⟨U, hxU, n, c, (fun i => match i with | 0 => some j | _ => none), ?_, ?_, ?_⟩
      · intro i hi i' hi' t _ _
        have e1 : i = 0 := Nat.lt_one_iff.mp hi
        have e2 : i' = 0 := Nat.lt_one_iff.mp hi'
        omega
      · intro i hi h
        have hi0 : i = 0 := Nat.lt_one_iff.mp hi
        subst hi0
        exact absurd (show (some j : Option (Fin n)) = none from h) (by simp)
      · intro i hi t h
        have hi0 : i = 0 := Nat.lt_one_iff.mp hi
        subst hi0
        have hjt : j = t := Option.some.inj (show (some j : Option (Fin n)) = some t from h)
        subst hjt
        simpa using hj


end

section
variable (k : Type u) [Field k] [CharZero k] {P P₁ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p] (π : P₁ ⟶ P) [IsLocallyNoetherian P₁] [Smooth (π ≫ p)] [LocallyOfFiniteType (π ≫ p)] (Z : P.IdealSheafData) (E : List P.IdealSheafData) (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (A : P.IdealSheafData) (A₁ : P₁.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ) (hA : A ≤ Z ^ μ) (htr : Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π)
include hZ hπ hμ hA htr

theorem comap_maxContactIdeal_le_exceptionalIdeal_mul :
    (maxContactIdeal k p A μ).comap π ≤
      Blowup.exceptionalIdeal π Z * maxContactIdeal k (π ≫ p) A₁ μ := by
  have hA1 : controlledTransform π Z A μ hπ hA = A₁ :=
    (eq_controlledTransform_of_mul_eq_comap π Z A μ hπ hA A₁ htr).symm
  have h : (derivIdealSheafIterate k p (μ - 1) A).comap π ≤
      Blowup.exceptionalIdeal π Z ^ (μ - (μ - 1)) *
        derivIdealSheafIterate k (π ≫ p) (μ - 1) (controlledTransform π Z A μ hπ hA) :=
    comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p π Z E hZ hπ A μ hA (μ - 1)
      (Nat.sub_le μ 1)
  rw [hA1] at h
  have hμ1 : μ - (μ - 1) = 1 := by omega
  rw [hμ1, pow_one] at h
  rw [maxContactIdeal_eq_derivIdealSheafIterate, maxContactIdeal_eq_derivIdealSheafIterate]
  exact h

theorem mem_orderAtLeastLocus_base_of_mem_orderAtLeastLocus_transform (y : P₁) (hy : y ∈ orderAtLeastLocus A₁ μ) :
    π.base y ∈ orderAtLeastLocus A μ := by
  by_contra hcon
  have hsucc : μ - 1 + 1 = μ := by omega
  have hz : orderAt A (π.base y) ≤ ((μ - 1 : ℕ) : ℕ∞) := by
    rw [orderAt_le_iff_notMem_orderAtLeastLocus, hsucc]
    exact hcon
  have hA' : A ≤ Z ^ (μ - 1) := by
    refine le_trans hA ?_
    have hpow : Z ^ μ = Z ^ (μ - 1) * Z := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow]
    exact mul_le_left_idealSheafData_consolidated332 _ _
  have hEA : Blowup.exceptionalIdeal π Z * A₁ = controlledTransform π Z A (μ - 1) hπ hA' := by
    refine eq_controlledTransform_of_mul_eq_comap π Z A (μ - 1) hπ hA' _ ?_
    calc Blowup.exceptionalIdeal π Z ^ (μ - 1) * (Blowup.exceptionalIdeal π Z * A₁)
        = Blowup.exceptionalIdeal π Z ^ (μ - 1 + 1) * A₁ := by rw [pow_succ, mul_assoc]
      _ = A.comap π := by rw [hsucc]; exact htr
  have h1 := orderAt_controlledTransform_le k p π Z E hZ hπ A (μ - 1) hA' (π.base y) hz y rfl
  rw [← hEA] at h1
  have hle : Blowup.exceptionalIdeal π Z * A₁ ≤ A₁ := mul_le_right_idealSheafData_consolidated332 _ _
  have h2 : orderAt A₁ y ≤ ((μ - 1 : ℕ) : ℕ∞) := le_trans (orderAt_le_of_le hle y) h1
  rw [orderAt_le_iff_notMem_orderAtLeastLocus, hsucc] at h2
  exact h2 hy


end

theorem le_center_of_isMaxContactHypersurface (k : Type u) [Field k] [CharZero k]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p]
    [LocallyOfFiniteType p] (Z : P.IdealSheafData) (E : List P.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith p Z E) (A : P.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ)
    (hsupp : (Z.support : Set ↥P) ⊆ orderAtLeastLocus A μ) (H : P.IdealSheafData)
    (hH : IsMaxContactHypersurface k p A μ H) :
    H ≤ Z := by
  have h1 : (Z.support : Set ↥P) ⊆ (H.support : Set ↥P) :=
    hsupp.trans (hH.orderAtLeastLocus_subset_support hμ)
  have h2 : (Z.support : Set ↥P) ⊆ orderAtLeastLocus H 1 := by
    intro x hx
    rw [mem_orderAtLeastLocus_one_iff]
    exact h1 hx
  have h3 := le_pow_of_hasStrictNormalCrossingsWith p Z H E hZ 1 h2
  rwa [pow_one] at h3

section
variable (k : Type u) [Field k] [CharZero k] {P P₁ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p] (π : P₁ ⟶ P) [IsLocallyNoetherian P₁] [Smooth (π ≫ p)] [LocallyOfFiniteType (π ≫ p)] (Z : P.IdealSheafData) (E : List P.IdealSheafData) (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (A : P.IdealSheafData) (A₁ : P₁.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ)
include hZ hπ hμ

theorem isMaxContactHypersurfaceAt_strictTransform_of_etaleChart (hA : A ≤ Z ^ μ)
    (htr : Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π) (H : P.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)] {U' : P.Opens} (hU' : IsAffineOpen U')
    {m : ℕ} (c : EtaleChart p U' m) (S : Finset (Fin m)) (j₀ : Fin m) (hj₀ : j₀ ∈ S)
    (hZU : restrictIdeal Z U' = c.coordIdeal S)
    (hHU : restrictIdeal H U' = c.coordIdeal {j₀})
    (hcoord : c.coord j₀ ∈ (maxContactIdeal k p A μ).ideal ⟨U', hU'⟩)
    (x₁ : P₁) (hx₁ : x₁ ∈ π ⁻¹ᵁ U') :
    IsMaxContactHypersurfaceAt k (π ≫ p) A₁ μ (Blowup.strictTransform π Z H) x₁ := by
  classical
  obtain ⟨s, hs, hx₁D⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZU x₁ hx₁
  set B := blowupChartOfIsBlowup π c S hπ hZU s hs with hBdef
  obtain ⟨V, _, hxV, hVD, hVaff, -⟩ :=
    exists_etaleChart_le (π ≫ p) x₁ B.domain hx₁D
  have hE : restrictIdeal (Blowup.exceptionalIdeal π Z) B.domain = B.chart.coordIdeal {s} :=
    B.restrictIdeal_exceptionalIdeal Z hs hZU
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (B.chart.coordIdeal {s}) := by
    refine isLocallyGeneratedByNonZeroDivisor_of_locally_coordIdeal (p := B.domain.ι ≫ (π ≫ p)) _ (fun x => ?_)
    exact ⟨⊤, trivial, m, B.chart.restrictOpens ⊤,
      Or.inr ⟨s, B.chart.restrictIdeal_coordIdeal ⊤ {s}⟩⟩
  have key : restrictIdeal (H.comap π) B.domain ≤
      B.chart.coordIdeal {s} * restrictIdeal (maxContactIdeal k (π ≫ p) A₁ μ) B.domain := by
    have h1 : restrictIdeal (H.comap π) B.domain
        ≤ restrictIdeal ((maxContactIdeal k p A μ).comap π) B.domain := by
      rw [B.restrictIdeal_comap H, B.restrictIdeal_comap (maxContactIdeal k p A μ)]
      refine Scheme.IdealSheafData.comap_mono _ ?_
      rw [hHU]
      exact (coordIdeal_singleton_le_restrictIdeal_iff k p hU' c j₀
        (maxContactIdeal k p A μ)).2 hcoord
    have h2 : restrictIdeal ((maxContactIdeal k p A μ).comap π) B.domain ≤
        restrictIdeal (Blowup.exceptionalIdeal π Z * maxContactIdeal k (π ≫ p) A₁ μ) B.domain :=
      Scheme.IdealSheafData.comap_mono _
        (comap_maxContactIdeal_le_exceptionalIdeal_mul k p π Z E hZ hπ A A₁ μ hμ hA htr)
    have hmul : restrictIdeal (Blowup.exceptionalIdeal π Z * maxContactIdeal k (π ≫ p) A₁ μ) B.domain =
        restrictIdeal (Blowup.exceptionalIdeal π Z) B.domain *
          restrictIdeal (maxContactIdeal k (π ≫ p) A₁ μ) B.domain :=
      Scheme.IdealSheafData.comap_mul _ _ _
    rw [hmul, hE] at h2
    exact h1.trans h2
  by_cases hj : j₀ = s
  · have hHU' : restrictIdeal H U' = c.coordIdeal {s} := by rw [hHU, hj]
    have hcomap : restrictIdeal (H.comap π) B.domain = B.chart.coordIdeal {s} :=
      B.restrictIdeal_comap_coordIdeal_self H hHU'
    have hST : restrictIdeal (Blowup.strictTransform π Z H) B.domain = ⊤ :=
      B.restrictIdeal_strictTransform_coordIdeal_self Z H hs hZU hHU'
    have htop : restrictIdeal (maxContactIdeal k (π ≫ p) A₁ μ) B.domain = ⊤ := by
      refine top_le_iff.1 (hcart.le_of_mul_le_mul ?_)
      rw [Scheme.IdealSheafData.mul_top]
      exact le_trans (le_of_eq hcomap.symm) key
    have hdisj : Disjoint (orderAtLeastLocus A₁ μ) ((V : Set ↥P₁)) := by
      rw [Set.disjoint_left]
      intro x hxc hxV
      have hx1 : x ∈ (maxContactIdeal k (π ≫ p) A₁ μ).support :=
        mem_support_maxContactIdeal_of_mem_orderAtLeastLocus k (π ≫ p) A₁ hμ hxc
      exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top _ B.domain htop x (hVD hxV) hx1
    exact ⟨V, hVaff, hxV, Or.inl ⟨hdisj, restrictIdeal_eq_top_of_le _ hVD hST⟩⟩
  · have hcomap : restrictIdeal (H.comap π) B.domain =
        B.chart.coordIdeal {j₀} * B.chart.coordIdeal {s} :=
      B.restrictIdeal_comap_coordIdeal_of_mem H j₀ hj₀ hj hHU
    have hST : restrictIdeal (Blowup.strictTransform π Z H) B.domain = B.chart.coordIdeal {j₀} :=
      B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZU j₀ hj₀ hj hHU
    have hmc : B.chart.coordIdeal {j₀} ≤
        restrictIdeal (maxContactIdeal k (π ≫ p) A₁ μ) B.domain := by
      refine hcart.le_of_mul_le_mul ?_
      rw [mul_comm (B.chart.coordIdeal {s}) (B.chart.coordIdeal {j₀})]
      exact le_trans (le_of_eq hcomap.symm) key
    have hSTV : restrictIdeal (Blowup.strictTransform π Z H) V =
        (B.chart.restrict hVD).coordIdeal {j₀} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hVD B.chart (Blowup.strictTransform π Z H) {j₀} hST
    refine ⟨V, hVaff, hxV, Or.inr ⟨m, B.chart.restrict hVD, j₀, hSTV, ?_⟩⟩
    show (B.chart.restrict hVD).coordIdeal {j₀} ≤
      restrictIdeal (maxContactIdeal k (π ≫ p) A₁ μ) V
    have h4 : restrictIdeal (Blowup.strictTransform π Z H) B.domain ≤
        restrictIdeal (maxContactIdeal k (π ≫ p) A₁ μ) B.domain := by
      rw [hST]; exact hmc
    have h5 := restrictIdeal_le_of_le_opens_consolidated332 hVD h4
    rw [← hSTV]
    exact h5

theorem isMaxContactHypersurfaceAt_strictTransform_of_mem_support (hsupp : (Z.support : Set ↥P) ⊆ orderAtLeastLocus A μ) (hA : A ≤ Z ^ μ)
    (htr : Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π) (H : P.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hH : IsMaxContactHypersurface k p A μ H) (x₁ : P₁) (hx₁ : π.base x₁ ∈ Z.support) :
    IsMaxContactHypersurfaceAt k (π ≫ p) A₁ μ (Blowup.strictTransform π Z H) x₁ := by
  classical
  have hzA : π.base x₁ ∈ orderAtLeastLocus A μ := hsupp hx₁
  have hsm : Smooth (Z.subschemeι ≫ p) :=
    smooth_subschemeι_comp_of_hasStrictNormalCrossingsWith Z E hZ
  have hZnil : HasStrictNormalCrossingsWith p Z ([] : List P.IdealSheafData) := hasStrictNormalCrossingsWith_nil_of_smooth p Z
  have hHZ : H ≤ Z := le_center_of_isMaxContactHypersurface k p Z E hZ A μ hμ hsupp H hH
  have hsnc : InStrictNormalCrossingPosition p (H :: ([] : List P.IdealSheafData)) :=
    inStrictNormalCrossingPosition_singleton_of_isMaxContactHypersurface_consolidated332 p A μ H hH
  obtain ⟨U, hU, hzU, m, c, lab, S, m', c', j0, lab', hZU, hHU, hlab, _, hlab', hj0⟩ :=
    exists_etaleCharts_of_inStrictNormalCrossingPosition_cons p Z H [] hsnc hZnil hHZ (π.base x₁) hx₁
  have hSprime : ∀ i ∈ S, c.coord i ∈ (hU.primeIdealOf ⟨π.base x₁, hzU⟩).asIdeal := by
    intro i hi
    have h1 : Z.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m))) :=
      c.ideal_eq_span_coord hU Z S hZU
    have h2 : c.coord i ∈ Z.ideal ⟨U, hU⟩ := by
      rw [h1]
      exact Ideal.subset_span ⟨i, hi, rfl⟩
    exact ideal_le_primeIdealOf Z hU hzU hx₁ h2
  obtain ⟨a, hcoeff, j, hjS, haj, -⟩ :=
    exists_coord_eq_sum_coeff_not_mem_of_le p hU hzU c lab S c' j0 lab' Z H [] hx₁ hlab hZU hHU hlab'
      hj0 hHZ
  obtain ⟨V, hV, hVU, hzV, cV, hcne, hcj, huj⟩ :=
    exists_etaleChart_update_coord p hU c hzU S a j hjS hSprime haj
  have hZV : restrictIdeal Z V = cV.coordIdeal S := by
    refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV cV Z S ?_
    have h1 : Z.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m))) :=
      c.ideal_eq_span_coord hU Z S hZU
    have h2 := ideal_eq_span_image_map_of_le Z hU hV hVU (c.coord '' (S : Set (Fin m))) h1
    rw [h2, Set.image_image]
    rw [← span_image_update_sum_eq
      (fun i => (P.presheaf.map (homOfLE hVU).op).hom (c.coord i)) S
      (fun i => (P.presheaf.map (homOfLE hVU).op).hom (a i)) j hjS huj]
    congr 1
    refine Set.image_congr ?_
    intro i hi
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self, hcj, map_sum]
      exact Finset.sum_congr rfl (fun t _ => (map_mul _ _ _).symm)
    · rw [Function.update_of_ne hij, hcne i hij]
  have hHV : restrictIdeal H V = cV.coordIdeal {j} := by
    refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV cV H {j} ?_
    have h1 : H.ideal ⟨U, hU⟩ =
        Ideal.span (c'.coord '' ((({j0} : Finset (Fin m')) : Set (Fin m')))) :=
      c'.ideal_eq_span_coord hU H {j0} hHU
    have h2 := ideal_eq_span_image_map_of_le H hU hV hVU _ h1
    have hone : (P.presheaf.map (homOfLE hVU).op).hom (c'.coord j0) = cV.coord j := by
      rw [hcoeff, hcj]
    rw [h2]
    simp only [Finset.coe_singleton, Set.image_singleton, hone]
  obtain ⟨W, hW, hzW, hcase⟩ := hH (π.base x₁)
  have hHmc : restrictIdeal H W ≤ restrictIdeal (maxContactIdeal k p A μ) W := by
    rcases hcase with ⟨hdisj, -⟩ | ⟨nW, cW, jW, hHW, hmcW⟩
    · exact absurd hzW (Set.disjoint_left.mp hdisj hzA)
    · rw [hHW]
      exact hmcW
  obtain ⟨V', _, hzV', hV'le, hV'aff, -⟩ :=
    exists_etaleChart_le p (π.base x₁) (V ⊓ W) ⟨hzV, hzW⟩
  have hV'V : V' ≤ V := fun y hy => (hV'le hy).1
  have hV'W : V' ≤ W := fun y hy => (hV'le hy).2
  have hZV' : restrictIdeal Z V' = (cV.restrict hV'V).coordIdeal S :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hV'V cV Z S hZV
  have hHV' : restrictIdeal H V' = (cV.restrict hV'V).coordIdeal {j} :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hV'V cV H {j} hHV
  have hcoordmem : (cV.restrict hV'V).coord j ∈ (maxContactIdeal k p A μ).ideal ⟨V', hV'aff⟩ := by
    refine (coordIdeal_singleton_le_restrictIdeal_iff k p hV'aff (cV.restrict hV'V) j
      (maxContactIdeal k p A μ)).1 ?_
    rw [← hHV']
    exact restrictIdeal_le_of_le_opens_consolidated332 hV'W hHmc
  exact isMaxContactHypersurfaceAt_strictTransform_of_etaleChart k p π Z E hZ hπ A A₁ μ hμ hA htr H
    hV'aff (cV.restrict hV'V) S j hjS hZV' hHV' hcoordmem x₁ hzV'

theorem isMaxContactHypersurfaceAt_strictTransform_of_notMem_support (hA : A ≤ Z ^ μ)
    (htr : Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π) (H : P.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hH : IsMaxContactHypersurface k p A μ H) (x₁ : P₁) (hx₁ : π.base x₁ ∉ Z.support) :
    IsMaxContactHypersurfaceAt k (π ≫ p) A₁ μ (Blowup.strictTransform π Z H) x₁ := by
  classical
  obtain ⟨U, hU, hxU, hcase⟩ := hH (π.base x₁)
  have hxc : π.base x₁ ∈ Z.support.compl := hx₁
  obtain ⟨V, _, hxV, hVle, hVaff, -⟩ :=
    exists_etaleChart_le p (π.base x₁) (U ⊓ Z.support.compl) ⟨hxU, hxc⟩
  have hVU : V ≤ U := fun y hy => (hVle hy).1
  have hx₁V : x₁ ∈ π ⁻¹ᵁ V := hxV
  have hrestrict : ∀ K : P.IdealSheafData,
      restrictIdeal (K.comap π) (π ⁻¹ᵁ V) = (restrictIdeal K V).comap (π ∣_ V) := by
    intro K
    rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι]
  have hZtop : Z.comap ((π ⁻¹ᵁ V).ι ≫ π) = ⊤ := by
    rw [Scheme.IdealSheafData.comap_comp]
    refine Blowup.comap_eq_top_of_notMem_support _ (Z.comap π) (fun y => ?_)
    show (y.1 : ↥P₁) ∉ (Z.comap π).support
    have hy : π.base y.1 ∈ V := y.2
    rw [Scheme.IdealSheafData.support_comap]
    exact (hVle hy).2
  have hST : restrictIdeal (Blowup.strictTransform π Z H) (π ⁻¹ᵁ V) =
      restrictIdeal (H.comap π) (π ⁻¹ᵁ V) :=
    restrictIdeal_strictTransform_eq_of_comap_eq_top_consolidated332 π Z H V hZtop
  rcases hcase with ⟨hdisj, hHtop⟩ | ⟨n, c, j₀, hHU, hmc⟩
  · obtain ⟨V₁, _, hx₁V₁, hV₁le, hV₁aff, -⟩ :=
      exists_etaleChart_le (π ≫ p) x₁ (π ⁻¹ᵁ V) hx₁V
    refine ⟨V₁, hV₁aff, hx₁V₁, Or.inl ⟨?_, ?_⟩⟩
    · rw [Set.disjoint_left]
      intro y hy hyV
      have h1 : π.base y ∈ orderAtLeastLocus A μ :=
        mem_orderAtLeastLocus_base_of_mem_orderAtLeastLocus_transform k p π Z E hZ hπ A A₁ μ hμ hA htr y hy
      have h2 : π.base y ∈ V := hV₁le hyV
      exact (Set.disjoint_left.mp hdisj h1) (hVU h2)
    · have h3 : restrictIdeal (H.comap π) (π ⁻¹ᵁ V) = ⊤ :=
        restrictIdeal_comap_preimage_eq_top π V H (restrictIdeal_eq_top_of_le H hVU hHtop)
      have h4 : restrictIdeal (Blowup.strictTransform π Z H) (π ⁻¹ᵁ V) = ⊤ := by rw [hST, h3]
      exact restrictIdeal_eq_top_of_le _ hV₁le h4
  · have hHV : restrictIdeal H V = (c.restrict hVU).coordIdeal {j₀} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hVU c H {j₀} hHU
    have hZV : Z.comap V.ι = ⊤ := by
      refine Blowup.comap_eq_top_of_notMem_support V.ι Z (fun y => ?_)
      show (y.1 : ↥P) ∉ Z.support
      exact (hVle y.2).2
    have hbiso : IsIso (π ∣_ V) := by
      have hb := hπ.restrict V
      rw [hZV] at hb
      exact hb.isIso_of_top
    have hSTV : restrictIdeal (Blowup.strictTransform π Z H) (π ⁻¹ᵁ V) =
        (etaleChartPullbackOfIsIso π (c.restrict hVU)).coordIdeal {j₀} := by
      rw [hST, hrestrict H, hHV, pullbackChartIso_coordIdeal_consolidated332]
    have hmcV : (etaleChartPullbackOfIsIso π (c.restrict hVU)).coordIdeal {j₀} ≤
        restrictIdeal (maxContactIdeal k (π ≫ p) A₁ μ) (π ⁻¹ᵁ V) := by
      have h1 : restrictIdeal H V ≤ restrictIdeal (maxContactIdeal k p A μ) V := by
        refine restrictIdeal_le_of_le_opens_consolidated332 hVU ?_
        rw [hHU]
        exact hmc
      have h2 : (etaleChartPullbackOfIsIso π (c.restrict hVU)).coordIdeal {j₀} ≤
          restrictIdeal ((maxContactIdeal k p A μ).comap π) (π ⁻¹ᵁ V) := by
        rw [pullbackChartIso_coordIdeal_consolidated332, hrestrict (maxContactIdeal k p A μ), ← hHV]
        exact Scheme.IdealSheafData.comap_mono _ h1
      refine h2.trans ?_
      refine Scheme.IdealSheafData.comap_mono _ ?_
      refine le_trans (comap_maxContactIdeal_le_exceptionalIdeal_mul k p π Z E hZ hπ A A₁ μ hμ hA htr) ?_
      exact mul_le_right_idealSheafData_consolidated332 _ _
    obtain ⟨V₁, _, hx₁V₁, hV₁le, hV₁aff, -⟩ :=
      exists_etaleChart_le (π ≫ p) x₁ (π ⁻¹ᵁ V) hx₁V
    have hSTV₁ : restrictIdeal (Blowup.strictTransform π Z H) V₁ =
        ((etaleChartPullbackOfIsIso π (c.restrict hVU)).restrict hV₁le).coordIdeal {j₀} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hV₁le (etaleChartPullbackOfIsIso π (c.restrict hVU))
        (Blowup.strictTransform π Z H) {j₀} hSTV
    refine ⟨V₁, hV₁aff, hx₁V₁,
      Or.inr ⟨n, (etaleChartPullbackOfIsIso π (c.restrict hVU)).restrict hV₁le, j₀, hSTV₁, ?_⟩⟩
    show ((etaleChartPullbackOfIsIso π (c.restrict hVU)).restrict hV₁le).coordIdeal {j₀} ≤
      restrictIdeal (maxContactIdeal k (π ≫ p) A₁ μ) V₁
    have h4 : restrictIdeal (Blowup.strictTransform π Z H) (π ⁻¹ᵁ V) ≤
        restrictIdeal (maxContactIdeal k (π ≫ p) A₁ μ) (π ⁻¹ᵁ V) := by
      rw [hSTV]
      exact hmcV
    have h5 := restrictIdeal_le_of_le_opens_consolidated332 hV₁le h4
    rw [← hSTV₁]
    exact h5


end

section
variable (k : Type u) [Field k] [CharZero k] {P P₁ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p] (π : P₁ ⟶ P) [IsLocallyNoetherian P₁] [LocallyOfFiniteType (π ≫ p)] (Z : P.IdealSheafData) (E : List P.IdealSheafData) (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (A : P.IdealSheafData) (A₁ : P₁.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ)
include hZ hπ hμ

theorem isMaxContactHypersurface_strictTransform_of_quasiCompact (hsupp : (Z.support : Set ↥P) ⊆ orderAtLeastLocus A μ)
    (htr : Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π) (H : P.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hH : IsMaxContactHypersurface k p A μ H) :
    IsMaxContactHypersurface k (π ≫ p) A₁ μ (Blowup.strictTransform π Z H) := by
  have : Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hZ hπ
  have hA : A ≤ Z ^ μ := le_pow_of_hasStrictNormalCrossingsWith p Z A E hZ μ hsupp
  intro x₁
  by_cases hx : π.base x₁ ∈ Z.support
  · exact isMaxContactHypersurfaceAt_strictTransform_of_mem_support k p π Z E hZ hπ A A₁ μ hμ hsupp hA
      htr H hH x₁ hx
  · exact isMaxContactHypersurfaceAt_strictTransform_of_notMem_support k p π Z E hZ hπ A A₁ μ hμ hA
      htr H hH x₁ hx

theorem isMaxContactHypersurface_strictTransform_of_orderAt_le (_hord : ∀ x : P, orderAt A x ≤ (μ : ℕ∞))
    (hsupp : (Z.support : Set ↥P) ⊆ orderAtLeastLocus A μ)
    (htr : Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π) (H : P.IdealSheafData) :
    IsMaxContactHypersurface k p A μ H →
      IsMaxContactHypersurface k (π ≫ p) A₁ μ (Blowup.strictTransform π Z H) := by
  intro hH
  exact isMaxContactHypersurface_strictTransform_of_quasiCompact k p π Z E hZ hπ A A₁ μ hμ
    hsupp htr H hH


end

end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ExceptionalMonomialOrder
section

open TopologicalSpace

section

section
variable {X : Scheme.{u}} {C S : Set X} (hC : IsIrreducible C) (hCS : C ⊆ S) (hmax : ∀ T : Set X, IsIrreducible T → T ⊆ S → C ⊆ T → T = C) (hS : IsClosed S)
include hC hCS hmax hS

theorem isClosed_of_maximal_isIrreducible_subset : IsClosed C := by
  have h : closure C = C :=
    hmax (closure C) hC.closure (hS.closure_subset_iff.mpr hCS) subset_closure
  exact closure_eq_iff_isClosed.mp h

theorem exists_closure_singleton_eq_of_maximal_irreducible : ∃ ξ : X, closure ({ξ} : Set X) = C := by
  have hCclosed : IsClosed C := isClosed_of_maximal_isIrreducible_subset hC hCS hmax hS
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hC hCclosed
  exact ⟨ξ, hξ⟩


end

theorem eq_of_mem_closure_singleton_of_maximal_irreducible {X : Scheme.{u}} {C S : Set X}
    (_hC : IsIrreducible C) (_hCS : C ⊆ S)
    (hmax : ∀ T : Set X, IsIrreducible T → T ⊆ S → C ⊆ T → T = C)
    (hS : IsClosed S) {ξ ξ' : X} (hξ : closure ({ξ} : Set X) = C) (hξ' : ξ' ∈ S)
    (hspec : ξ ∈ closure ({ξ'} : Set X)) : ξ' = ξ := by
  have hirr : IsIrreducible (closure ({ξ'} : Set X)) :=
    (isIrreducible_singleton (x := ξ')).closure
  have hsub : closure ({ξ'} : Set X) ⊆ S :=
    hS.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hξ')
  have hCsub : C ⊆ closure ({ξ'} : Set X) := by
    rw [← hξ]
    exact closure_minimal (Set.singleton_subset_iff.mpr hspec) isClosed_closure
  have heq : closure ({ξ'} : Set X) = C := hmax _ hirr hsub hCsub
  have hcl : closure ({ξ'} : Set X) = closure ({ξ} : Set X) := by rw [heq, hξ]
  exact (inseparable_iff_closure_eq.mpr hcl).eq

def totalDegree {T : Type*} (f : T →₀ ℕ) : ℕ := f.sum fun _ n => n

section
variable {T : Type*}

theorem totalDegree_zero : totalDegree (0 : T →₀ ℕ) = 0 := by
  simp [totalDegree]

theorem totalDegree_add (f g : T →₀ ℕ) : totalDegree (f + g) = totalDegree f + totalDegree g := by
  show (f + g).sum (fun _ n => n) = f.sum (fun _ n => n) + g.sum (fun _ n => n)
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

theorem totalDegree_single [DecidableEq T] (t : T) (n : ℕ) :
    totalDegree (Finsupp.single t n) = n := by
  show (Finsupp.single t n).sum (fun _ m => m) = n
  exact Finsupp.sum_single_index rfl


end

def powProd {A : Type*} [CommRing A] {T : Type*} (x : T → A) (f : T →₀ ℕ) : A :=
  f.prod fun t n => x t ^ n

section
variable {A : Type*} [CommRing A] {T : Type*}

theorem powProd_zero (x : T → A) :
    powProd x (0 : T →₀ ℕ) = 1 := by
  simp [powProd]

theorem powProd_add (x : T → A) (f g : T →₀ ℕ) :
    powProd x (f + g) = powProd x f * powProd x g := by
  show (f + g).prod (fun t n => x t ^ n)
      = f.prod (fun t n => x t ^ n) * g.prod (fun t n => x t ^ n)
  exact Finsupp.prod_add_index' (fun a => pow_zero (x a)) (fun a b₁ b₂ => pow_add (x a) b₁ b₂)

theorem powProd_single [DecidableEq T] (x : T → A)
    (t : T) (n : ℕ) : powProd x (Finsupp.single t n) = x t ^ n := by
  show (Finsupp.single t n).prod (fun t m => x t ^ m) = x t ^ n
  exact Finsupp.prod_single_index (pow_zero (x t))


end

theorem map_powProd {A B : Type*} [CommRing A] [CommRing B] {T : Type*} (φ : A →+* B)
    (x : T → A) (f : T →₀ ℕ) : φ (powProd x f) = powProd (fun t => φ (x t)) f := by
  classical
  simp [powProd, Finsupp.prod, map_prod, map_pow]

section
variable {A : Type*} [CommRing A] {T : Type*} (x : T → A) (I : Ideal A) (hx : ∀ t : T, x t ∈ I)
include hx

private theorem prod_pow_mem_pow_sum_consolidated292 (g : T → ℕ) (s : Finset T) :
    (∏ t ∈ s, x t ^ g t) ∈ I ^ (∑ t ∈ s, g t) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (hx a) (g a)) ih

theorem powProd_mem_pow_totalDegree (f : T →₀ ℕ) : powProd x f ∈ I ^ totalDegree f := by
  have h1 : powProd x f = ∏ t ∈ f.support, x t ^ f t := rfl
  have h2 : totalDegree f = ∑ t ∈ f.support, f t := rfl
  rw [h1, h2]
  exact prod_pow_mem_pow_sum_consolidated292 x I hx (fun t => f t) f.support


end

def chartMonomial {A : Type*} [CommRing A] {m : ℕ} (x : Fin m → A) (S : Finset (Fin m))
    (s : Fin m) (c : ℕ) (f : ↥(S.erase s) →₀ ℕ) : A :=
  x s ^ (c - totalDegree f) * powProd (fun t : ↥(S.erase s) => x t.1) f

section
variable {A B : Type*} [CommRing A] [CommRing B]

private theorem map_powProd_eq_powProd_mul_pow_totalDegree_consolidated292 {T : Type*} (φ : A →+* B) (u : T → A) (v : T → B) (b : B)
    (h : ∀ t : T, φ (u t) = v t * b) (f : T →₀ ℕ) :
    φ (powProd u f) = powProd v f * b ^ totalDegree f := by
  classical
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · simp only [powProd_zero, totalDegree_zero, pow_zero, mul_one, map_one]
  · intro p q hp hq
    simp only [powProd_add, totalDegree_add, map_mul, hp, hq, pow_add]
    ring
  · intro t n
    simp only [powProd_single, totalDegree_single, map_pow, h, mul_pow]

theorem map_chartMonomial (φ : A →+* B) {m : ℕ}
    (x : Fin m → A) (y : Fin m → B) (S : Finset (Fin m)) (s : Fin m)
    (hφs : φ (x s) = y s)
    (hφ : ∀ i ∈ S, i ≠ s → φ (x i) = y i * y s)
    (c : ℕ) (f : ↥(S.erase s) →₀ ℕ) (hf : totalDegree f ≤ c) :
    φ (chartMonomial x S s c f) =
      y s ^ c * powProd (fun t : ↥(S.erase s) => y t.1) f := by
  have hfun : ∀ t : ↥(S.erase s), φ (x t.1) = y t.1 * y s := by
    intro t
    obtain ⟨hts, htS⟩ := Finset.mem_erase.mp t.2
    exact hφ t.1 htS hts
  have hmon : chartMonomial x S s c f
      = x s ^ (c - totalDegree f) * powProd (fun t : ↥(S.erase s) => x t.1) f := rfl
  have key := map_powProd_eq_powProd_mul_pow_totalDegree_consolidated292 φ (fun t : ↥(S.erase s) => x t.1)
      (fun t : ↥(S.erase s) => y t.1) (y s) hfun f
  rw [hmon, map_mul, map_pow, hφs, key]
  have hc : y s ^ c = y s ^ (c - totalDegree f) * y s ^ totalDegree f := by
    rw [← pow_add, Nat.sub_add_cancel hf]
  rw [hc]
  ring


end

def chartMonomialIdeal {A : Type*} [CommRing A] {m : ℕ} (x : Fin m → A) (S : Finset (Fin m))
    (s : Fin m) (c : ℕ) : Ideal A :=
  Ideal.span {a : A | ∃ f : ↥(S.erase s) →₀ ℕ, totalDegree f ≤ c ∧ a = chartMonomial x S s c f}

section
variable {A : Type*} [CommRing A] {m : ℕ} (x : Fin m → A) (S : Finset (Fin m)) (s : Fin m)

private theorem chartMonomialIdeal_eq_span_consolidated292 (c : ℕ) :
    chartMonomialIdeal x S s c =
      Ideal.span {a : A | ∃ f : ↥(S.erase s) →₀ ℕ, totalDegree f ≤ c ∧
        a = chartMonomial x S s c f} := rfl

private theorem chartMonomial_mem_chartMonomialIdeal_consolidated292 (c : ℕ) (f : ↥(S.erase s) →₀ ℕ)
    (hf : totalDegree f ≤ c) :
    chartMonomial x S s c f ∈ chartMonomialIdeal x S s c := by
  rw [chartMonomialIdeal_eq_span_consolidated292 x S s c]
  exact Ideal.subset_span ⟨f, hf, rfl⟩

private theorem chartMonomial_mul_coord_self_mem_chartMonomialIdeal_succ_consolidated292 (c : ℕ) (f : ↥(S.erase s) →₀ ℕ) (hf : totalDegree f ≤ c) :
    chartMonomial x S s c f * x s ∈ chartMonomialIdeal x S s (c + 1) := by
  have h1 : c + 1 - totalDegree f = (c - totalDegree f) + 1 := by omega
  have h2 : chartMonomial x S s c f * x s = chartMonomial x S s (c + 1) f := by
    simp only [chartMonomial, h1, pow_succ]
    ring
  rw [h2]
  exact chartMonomial_mem_chartMonomialIdeal_consolidated292 x S s (c + 1) f (hf.trans (Nat.le_succ c))

private theorem chartMonomial_mul_coord_mem_chartMonomialIdeal_succ_consolidated292 (c : ℕ) (f : ↥(S.erase s) →₀ ℕ) (hf : totalDegree f ≤ c)
    (t : ↥(S.erase s)) :
    chartMonomial x S s c f * x t.1 ∈ chartMonomialIdeal x S s (c + 1) := by
  have hdeg : totalDegree (f + Finsupp.single t 1) = totalDegree f + 1 := by
    rw [totalDegree_add, totalDegree_single]
  have h3 : c + 1 - (totalDegree f + 1) = c - totalDegree f := by omega
  have h2 : chartMonomial x S s c f * x t.1
      = chartMonomial x S s (c + 1) (f + Finsupp.single t 1) := by
    simp only [chartMonomial, hdeg, h3, powProd_add, powProd_single, pow_one]
    ring
  rw [h2]
  refine chartMonomial_mem_chartMonomialIdeal_consolidated292 x S s (c + 1) (f + Finsupp.single t 1) ?_
  rw [hdeg]
  omega

private theorem mul_coord_mem_chartMonomialIdeal_succ_consolidated292 (c : ℕ) (i : Fin m) (hi : i ∈ S) (r : A)
    (hr : r ∈ chartMonomialIdeal x S s c) :
    r * x i ∈ chartMonomialIdeal x S s (c + 1) := by
  have key : chartMonomialIdeal x S s c ≤
      Submodule.comap (LinearMap.mulRight A (x i)) (chartMonomialIdeal x S s (c + 1)) := by
    rw [chartMonomialIdeal_eq_span_consolidated292 x S s c]
    refine Ideal.span_le.mpr ?_
    rintro a ⟨f, hf, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply]
    by_cases his : i = s
    · have hx : chartMonomial x S s c f * x i = chartMonomial x S s c f * x s := by rw [his]
      rw [hx]
      exact chartMonomial_mul_coord_self_mem_chartMonomialIdeal_succ_consolidated292 x S s c f hf
    · exact chartMonomial_mul_coord_mem_chartMonomialIdeal_succ_consolidated292 x S s c f hf ⟨i, Finset.mem_erase.mpr ⟨his, hi⟩⟩
  have h := key hr
  rw [Submodule.mem_comap, LinearMap.mulRight_apply] at h
  exact h

private theorem mul_mem_chartMonomialIdeal_succ_consolidated292 (c : ℕ) (r : A) (hr : r ∈ chartMonomialIdeal x S s c)
    (y : A) (hy : y ∈ Ideal.span (x '' (S : Set (Fin m)))) :
    r * y ∈ chartMonomialIdeal x S s (c + 1) := by
  have key : Ideal.span (x '' (S : Set (Fin m))) ≤
      Submodule.comap (LinearMap.mulRight A r) (chartMonomialIdeal x S s (c + 1)) := by
    refine Ideal.span_le.mpr ?_
    rintro a ⟨i, hi, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply]
    rw [mul_comm (x i) r]
    exact mul_coord_mem_chartMonomialIdeal_succ_consolidated292 x S s c i (Finset.mem_coe.mp hi) r hr
  have h := key hy
  rw [Submodule.mem_comap, LinearMap.mulRight_apply] at h
  rw [mul_comm r y]
  exact h

theorem pow_span_image_le_chartMonomialIdeal (_hs : s ∈ S) (c : ℕ) :
    Ideal.span (x '' (S : Set (Fin m))) ^ c ≤ chartMonomialIdeal x S s c := by
  induction c with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]
      have h0 : (1 : A) = chartMonomial x S s 0 0 := by
        simp [chartMonomial, totalDegree_zero, powProd_zero]
      rw [h0]
      exact chartMonomial_mem_chartMonomialIdeal_consolidated292 x S s 0 0 totalDegree_zero.le
  | succ c ih =>
      rw [pow_succ]
      refine Ideal.mul_le.mpr ?_
      intro r hr y hy
      exact mul_mem_chartMonomialIdeal_succ_consolidated292 x S s c r (ih hr) y hy


end

section
variable {R : Type*} [CommRing R]

private theorem map_C_eq_ker_map_quotientMk_consolidated292 (P : Ideal R)
    (σ : Type*) :
    Ideal.map (MvPolynomial.C : R →+* MvPolynomial σ R) P =
      RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk P) :
        MvPolynomial σ R →+* MvPolynomial σ (R ⧸ P)) := by
  rw [MvPolynomial.ker_map, Ideal.mk_ker]

theorem isPrime_map_C (P : Ideal R) [P.IsPrime] (σ : Type*) :
    (Ideal.map (MvPolynomial.C : R →+* MvPolynomial σ R) P).IsPrime := by
  have hdom : IsDomain (R ⧸ P) := inferInstance
  have hdom2 : IsDomain (MvPolynomial σ (R ⧸ P)) := inferInstance
  rw [map_C_eq_ker_map_quotientMk_consolidated292 P σ]
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    intro hmem
    have h1 : (MvPolynomial.map (Ideal.Quotient.mk P) :
        MvPolynomial σ R →+* MvPolynomial σ (R ⧸ P)) 1 = 0 := RingHom.mem_ker.mp hmem
    rw [map_one] at h1
    have h2 := congrArg (fun f : MvPolynomial σ (R ⧸ P) => MvPolynomial.constantCoeff f) h1
    simp only [map_one, map_zero] at h2
    exact one_ne_zero h2
  · intro x y hxy
    rw [RingHom.mem_ker, map_mul] at hxy
    rcases mul_eq_zero.mp hxy with h | h
    · exact Or.inl (RingHom.mem_ker.mpr h)
    · exact Or.inr (RingHom.mem_ker.mpr h)

private theorem C_coeff_mem_of_minimal_prime_consolidated292 {σ : Type*}
    (Pp : Ideal (MvPolynomial σ R)) [Pp.IsPrime]
    (hmin : ∀ K : Ideal (MvPolynomial σ R), K.IsPrime → K ≤ Pp → Pp ≤ K)
    {p : MvPolynomial σ R} (hp : p ∈ Pp) (d : σ →₀ ℕ) :
    MvPolynomial.C (p.coeff d) ∈ Pp := by
  have hq : (Ideal.comap (MvPolynomial.C : R →+* MvPolynomial σ R) Pp).IsPrime :=
    Ideal.comap_isPrime (MvPolynomial.C : R →+* MvPolynomial σ R) Pp
  have hle : Ideal.map (MvPolynomial.C : R →+* MvPolynomial σ R)
      (Ideal.comap (MvPolynomial.C : R →+* MvPolynomial σ R) Pp) ≤ Pp :=
    Ideal.map_le_iff_le_comap.mpr le_rfl
  have hge := hmin _
    (isPrime_map_C (Ideal.comap (MvPolynomial.C : R →+* MvPolynomial σ R) Pp) σ) hle
  exact Ideal.mem_comap.mp ((MvPolynomial.mem_map_C_iff.mp (hge hp)) d)

private theorem C_mul_powProd_X_eq_monomial_consolidated292 {σ : Type*}
    (f : σ →₀ ℕ) (r : R) :
    MvPolynomial.C r * powProd (fun t : σ => (MvPolynomial.X t : MvPolynomial σ R)) f
      = MvPolynomial.monomial f r :=
  MvPolynomial.monomial_eq.symm


end

theorem ideal_le_comap_pow_succ_of_map_le_span_pow_mul {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    {m : ℕ} (x : Fin m → A) (y : Fin m → B) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S)
    (hφs : φ (x s) = y s)
    (hφ : ∀ i ∈ S, i ≠ s → φ (x i) = y i * y s)
    (hy : y s ∈ nonZeroDivisors B)
    (e : (B ⧸ Ideal.span {y s}) ≃+*
      MvPolynomial ↥(S.erase s) (A ⧸ Ideal.span (x '' (S : Set (Fin m)))))
    (heC : ∀ a : A, e (Ideal.Quotient.mk (Ideal.span {y s}) (φ a)) =
      MvPolynomial.C (Ideal.Quotient.mk (Ideal.span (x '' (S : Set (Fin m)))) a))
    (heX : ∀ t : ↥(S.erase s),
      e (Ideal.Quotient.mk (Ideal.span {y s}) (y t.1)) = MvPolynomial.X t)
    (P : Ideal B) [P.IsPrime] (hyP : y s ∈ P)
    (hPmin : ∀ Q : Ideal B, Q.IsPrime → Q ≤ P → y s ∈ Q → P ≤ Q)
    (c : ℕ) (J : Ideal A) (hJ : J ≤ Ideal.span (x '' (S : Set (Fin m))) ^ c)
    (J' : Ideal B) (hJ'P : J' ≤ P)
    (hmap : Ideal.map φ J ≤ Ideal.span {y s ^ c} * J') :
    J ≤ Ideal.comap φ P ^ (c + 1) := by
  classical
  obtain ⟨Ψ, hΨsurj, hΨ⟩ :
      ∃ Ψ : B →+* MvPolynomial ↥(S.erase s) (A ⧸ Ideal.span (x '' (S : Set (Fin m)))),
        Function.Surjective Ψ ∧
          ∀ b : B, Ψ b = e (Ideal.Quotient.mk (Ideal.span {y s}) b) := by
    refine ⟨e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {y s})), ?_, ?_⟩
    · intro q
      obtain ⟨z, hz⟩ := e.surjective q
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective z
      refine ⟨b, ?_⟩
      show e (Ideal.Quotient.mk (Ideal.span {y s}) b) = q
      rw [hb, hz]
    · intro b
      simp
  have hΨ0 : Ψ (y s) = 0 := by
    rw [hΨ, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (y s)), map_zero]
  have hΨC : ∀ a : A, Ψ (φ a)
      = MvPolynomial.C (Ideal.Quotient.mk (Ideal.span (x '' (S : Set (Fin m)))) a) := by
    intro a
    rw [hΨ]
    exact heC a
  have hΨX : ∀ t : ↥(S.erase s), Ψ (y t.1) = MvPolynomial.X t := by
    intro t
    rw [hΨ]
    exact heX t
  have hfun : (fun t : ↥(S.erase s) => Ψ (y t.1))
      = fun t : ↥(S.erase s) => (MvPolynomial.X t :
        MvPolynomial ↥(S.erase s) (A ⧸ Ideal.span (x '' (S : Set (Fin m))))) := funext hΨX
  have hkerP : RingHom.ker Ψ ≤ P := by
    intro b hb
    have hb0 : Ψ b = 0 := RingHom.mem_ker.mp hb
    rw [hΨ] at hb0
    have hb1 : (Ideal.Quotient.mk (Ideal.span {y s})) b = 0 := by
      apply e.injective
      rw [hb0, map_zero]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hyP)
      (Ideal.Quotient.eq_zero_iff_mem.mp hb1)
  have hcomapP : Ideal.comap Ψ (Ideal.map Ψ P) ≤ P := by
    intro b hb
    obtain ⟨p0, hp0P, hp0b⟩ :=
      (Ideal.mem_map_iff_of_surjective Ψ hΨsurj).mp (Ideal.mem_comap.mp hb)
    have hkb : b - p0 ∈ RingHom.ker Ψ := by
      rw [RingHom.mem_ker, map_sub, hp0b, sub_self]
    have hsum2 : (b - p0) + p0 ∈ P := P.add_mem (hkerP hkb) hp0P
    simpa using hsum2
  have hPprime : (Ideal.map Ψ P).IsPrime := by
    constructor
    · intro htop
      have h1 : (1 : MvPolynomial ↥(S.erase s) (A ⧸ Ideal.span (x '' (S : Set (Fin m)))))
          ∈ Ideal.map Ψ P := by
        rw [htop]
        exact Submodule.mem_top
      have h2 : (1 : B) ∈ Ideal.comap Ψ (Ideal.map Ψ P) := by
        rw [Ideal.mem_comap, map_one]
        exact h1
      have hPtop : P = ⊤ := by
        rw [Ideal.eq_top_iff_one]
        exact hcomapP h2
      exact Ideal.IsPrime.ne_top ‹P.IsPrime› hPtop
    · intro p q hpq
      obtain ⟨b, rfl⟩ := hΨsurj p
      obtain ⟨b', rfl⟩ := hΨsurj q
      have hb : b * b' ∈ P := by
        apply hcomapP
        rw [Ideal.mem_comap, map_mul]
        exact hpq
      rcases Ideal.IsPrime.mem_or_mem ‹P.IsPrime› hb with h | h
      · exact Or.inl (Ideal.mem_map_of_mem Ψ h)
      · exact Or.inr (Ideal.mem_map_of_mem Ψ h)
  have hmin : ∀ K : Ideal (MvPolynomial ↥(S.erase s)
      (A ⧸ Ideal.span (x '' (S : Set (Fin m))))),
      K.IsPrime → K ≤ Ideal.map Ψ P → Ideal.map Ψ P ≤ K := by
    intro K hK hle
    have := hK
    have h2 : Ideal.comap Ψ K ≤ P := le_trans (Ideal.comap_mono hle) hcomapP
    have h3 : y s ∈ Ideal.comap Ψ K := by
      rw [Ideal.mem_comap, hΨ0]
      exact K.zero_mem
    have h4 := hPmin (Ideal.comap Ψ K) (Ideal.comap_isPrime Ψ K) h2 h3
    exact le_trans (Ideal.map_mono h4) (Ideal.map_le_iff_le_comap.mpr le_rfl)
  have hxQ : ∀ i ∈ S, x i ∈ Ideal.comap φ P := by
    intro i hi
    rw [Ideal.mem_comap]
    by_cases h : i = s
    · rw [h, hφs]
      exact hyP
    · rw [hφ i hi h]
      exact Ideal.mul_mem_left _ _ hyP
  have hmonQ : ∀ f : ↥(S.erase s) →₀ ℕ, totalDegree f ≤ c →
      chartMonomial x S s c f ∈ Ideal.comap φ P ^ c := by
    intro f hf
    have h1 : x s ^ (c - totalDegree f) ∈ Ideal.comap φ P ^ (c - totalDegree f) :=
      Ideal.pow_mem_pow (hxQ s hs) _
    have h2 : powProd (fun t : ↥(S.erase s) => x t.1) f ∈ Ideal.comap φ P ^ totalDegree f :=
      powProd_mem_pow_totalDegree (fun t : ↥(S.erase s) => x t.1) (Ideal.comap φ P)
        (fun t => hxQ t.1 (Finset.mem_of_mem_erase t.2)) f
    have h3 := Ideal.mul_mem_mul h1 h2
    rw [← pow_add, Nat.sub_add_cancel hf] at h3
    exact h3
  intro a ha
  have haM : a ∈ chartMonomialIdeal x S s c :=
    pow_span_image_le_chartMonomialIdeal x S s hs c (hJ ha)
  have haspan : a ∈ Submodule.span A
      {b : A | ∃ f : ↥(S.erase s) →₀ ℕ, totalDegree f ≤ c ∧ b = chartMonomial x S s c f} := haM
  obtain ⟨cf, hcfsupp, hcfsum⟩ := Submodule.mem_span_set.mp haspan
  have hex : ∀ g ∈ cf.support, ∃ f : ↥(S.erase s) →₀ ℕ,
      totalDegree f ≤ c ∧ g = chartMonomial x S s c f := by
    intro g hg
    exact hcfsupp (Finset.mem_coe.mpr hg)
  choose! fsel hfdeg hfeq using hex
  have hinj : ∀ g ∈ cf.support, ∀ g' ∈ cf.support, fsel g = fsel g' → g = g' := by
    intro g hg g' hg' hgg
    have e1 := hfeq g hg
    rw [hgg] at e1
    exact e1.trans (hfeq g' hg').symm
  have hsum : a = ∑ i ∈ cf.support, cf i * i := by
    rw [← hcfsum]
    simp [Finsupp.sum, smul_eq_mul]
  have ha' : a = ∑ i ∈ cf.support, cf i * chartMonomial x S s c (fsel i) := by
    rw [hsum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← hfeq i hi]
  have hφa : φ a = y s ^ c *
      ∑ i ∈ cf.support, φ (cf i) * powProd (fun t : ↥(S.erase s) => y t.1) (fsel i) := by
    rw [ha', map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [map_mul, map_chartMonomial φ x y S s hφs hφ c (fsel i) (hfdeg i hi)]
    ring
  have hmemJ' : φ a ∈ Ideal.span {y s ^ c} * J' := hmap (Ideal.mem_map_of_mem φ ha)
  obtain ⟨j, hjJ', hjeq⟩ := Ideal.mem_span_singleton_mul.mp hmemJ'
  have hueq : (∑ i ∈ cf.support, φ (cf i) *
      powProd (fun t : ↥(S.erase s) => y t.1) (fsel i)) = j := by
    refine (mul_cancel_left_mem_nonZeroDivisors (pow_mem hy c)).mp ?_
    rw [← hφa]
    exact hjeq.symm
  have huP : (∑ i ∈ cf.support, φ (cf i) *
      powProd (fun t : ↥(S.erase s) => y t.1) (fsel i)) ∈ P := by
    rw [hueq]
    exact hJ'P hjJ'
  have hΨu : Ψ (∑ i ∈ cf.support, φ (cf i) *
        powProd (fun t : ↥(S.erase s) => y t.1) (fsel i))
      = ∑ i ∈ cf.support, MvPolynomial.monomial (fsel i)
          (Ideal.Quotient.mk (Ideal.span (x '' (S : Set (Fin m)))) (cf i)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_mul, hΨC, map_powProd, hfun]
    exact C_mul_powProd_X_eq_monomial_consolidated292 (fsel i) _
  have hcoeff : ∀ g₀ ∈ cf.support,
      (∑ i ∈ cf.support, MvPolynomial.monomial (fsel i)
            (Ideal.Quotient.mk (Ideal.span (x '' (S : Set (Fin m)))) (cf i))).coeff (fsel g₀)
        = Ideal.Quotient.mk (Ideal.span (x '' (S : Set (Fin m)))) (cf g₀) := by
    intro g₀ hg₀
    have hstep : ∀ g ∈ cf.support, g ≠ g₀ →
        (MvPolynomial.monomial (fsel g)
          (Ideal.Quotient.mk (Ideal.span (x '' (S : Set (Fin m)))) (cf g))).coeff (fsel g₀) = 0 := by
      intro g hg hne
      have hne' : fsel g ≠ fsel g₀ := fun hh => hne (hinj g hg g₀ hg₀ hh)
      rw [MvPolynomial.coeff_monomial, if_neg hne']
    rw [MvPolynomial.coeff_sum, Finset.sum_eq_single_of_mem g₀ hg₀ hstep,
      MvPolynomial.coeff_monomial]
    simp
  have hcfQ : ∀ g ∈ cf.support, cf g ∈ Ideal.comap φ P := by
    intro g hg
    have h1 : Ψ (∑ i ∈ cf.support, φ (cf i) *
        powProd (fun t : ↥(S.erase s) => y t.1) (fsel i)) ∈ Ideal.map Ψ P :=
      Ideal.mem_map_of_mem Ψ huP
    rw [hΨu] at h1
    have h2 := C_coeff_mem_of_minimal_prime_consolidated292 (Ideal.map Ψ P) hmin h1 (fsel g)
    rw [hcoeff g hg] at h2
    have h3 : Ψ (φ (cf g)) ∈ Ideal.map Ψ P := by
      rw [hΨC]
      exact h2
    exact Ideal.mem_comap.mpr (hcomapP (Ideal.mem_comap.mpr h3))
  rw [ha']
  refine Ideal.sum_mem _ ?_
  intro i hi
  have h3 : (Ideal.comap φ P) ^ (c + 1)
      = (Ideal.comap φ P) * (Ideal.comap φ P) ^ c := by
    rw [pow_succ, mul_comm]
  rw [h3]
  exact Ideal.mul_mem_mul (hcfQ i hi) (hmonQ (fsel i) (hfdeg i hi))

section
variable {X : Scheme.{u}}

private theorem map_germ_primeIdealOf_le_maximalIdeal_consolidated292 {U : X.Opens}
    (hU : IsAffineOpen U) (x : ↥U) :
    Ideal.map (CommRingCat.Hom.hom (X.presheaf.germ U x.1 x.2)) (hU.primeIdealOf x).asIdeal
      ≤ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x.1) := by
  have := hU.isLocalization_stalk x
  refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
  rw [Ideal.mem_comap]
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ (hU.primeIdealOf x).asIdeal a).mpr ha

private theorem mem_support_iff_ideal_le_primeIdealOf_consolidated292 (I : X.IdealSheafData)
    {U : X.Opens} (hU : IsAffineOpen U) (x : ↥U) :
    (x : X) ∈ I.support ↔ I.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf x).asIdeal := by
  constructor
  · intro hx
    exact ideal_le_primeIdealOf I hU x.2 hx
  · intro hx
    rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_eq_map_germ I (x : X) ⟨U, hU⟩ x.2]
    exact le_trans (Ideal.map_mono hx) (map_germ_primeIdealOf_le_maximalIdeal_consolidated292 hU x)

private theorem le_orderAt_of_ideal_le_pow_consolidated292 (J : X.IdealSheafData) {U : X.Opens}
    (hU : IsAffineOpen U) (x : ↥U) (n : ℕ)
    (h : J.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf x).asIdeal ^ n) :
    ((n : ℕ) : ℕ∞) ≤ orderAt J (x : X) := by
  rw [le_orderAt_iff, stalkIdeal_eq_map_germ J (x : X) ⟨U, hU⟩ x.2]
  calc Ideal.map (CommRingCat.Hom.hom (X.presheaf.germ U x.1 x.2)) (J.ideal ⟨U, hU⟩)
      ≤ Ideal.map (CommRingCat.Hom.hom (X.presheaf.germ U x.1 x.2))
          ((hU.primeIdealOf x).asIdeal ^ n) := Ideal.map_mono h
    _ = (Ideal.map (CommRingCat.Hom.hom (X.presheaf.germ U x.1 x.2))
          (hU.primeIdealOf x).asIdeal) ^ n := Ideal.map_pow _ _ _
    _ ≤ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x.1) ^ n :=
        Ideal.pow_right_mono (map_germ_primeIdealOf_le_maximalIdeal_consolidated292 hU x) n

private theorem exists_primeIdealOf_eq_consolidated292 {U : X.Opens}
    (hU : IsAffineOpen U) (q : PrimeSpectrum Γ(X, U)) :
    ∃ y : ↥U, hU.primeIdealOf y = q := by
  refine ⟨hU.isoSpec.inv.base q, ?_⟩
  have h0 := congrArg (fun f : Spec Γ(X, U) ⟶ Spec Γ(X, U) => f.base q) hU.isoSpec.inv_hom_id
  exact h0


end

theorem controlledTransform_not_subset_support {k : Type u} [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    [IsLocallyNoetherian X] [IsLocallyNoetherian X₁]
    (Z : X.IdealSheafData) (E : List X.IdealSheafData) (hE : HasStrictNormalCrossingsWith p Z E)
    (π : X₁ ⟶ X) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (J : X.IdealSheafData) (c : ℕ)
    (hord : ∀ x : X, x ∈ Z.support → orderAt J x = (c : ℕ∞))
    (J' : X₁.IdealSheafData)
    (htr : Blowup.exceptionalIdeal π Z ^ c * J' = J.comap π)
    (C : Set X₁)
    (hCirr : IsIrreducible C)
    (hCsub : C ⊆ ((Blowup.exceptionalIdeal π Z).support : Set X₁))
    (hCmax : ∀ T : Set X₁, IsIrreducible T →
      T ⊆ ((Blowup.exceptionalIdeal π Z).support : Set X₁) → C ⊆ T → T = C) :
    ¬ (C ⊆ (J'.support : Set X₁)) := by
  classical
  intro hCJ'
  have hZsm : Smooth (Z.subschemeι ≫ p) :=
    smooth_subschemeι_comp_of_hasStrictNormalCrossingsWith Z E hE
  have hclosed : IsClosed ((Blowup.exceptionalIdeal π Z).support : Set X₁) :=
    (Blowup.exceptionalIdeal π Z).support.2
  obtain ⟨ξ, hξ⟩ := exists_closure_singleton_eq_of_maximal_irreducible hCirr hCsub hCmax hclosed
  have hξC : ξ ∈ C := by
    rw [← hξ]
    exact subset_closure rfl
  have hξE : ξ ∈ (Blowup.exceptionalIdeal π Z).support := hCsub hξC
  have hξJ : ξ ∈ J'.support := hCJ' hξC
  have hzZ : π.base ξ ∈ Z.support := by
    have h1 : ξ ∈ (Z.comap π).support := by
      rw [← Blowup.exceptionalIdeal_eq_comap π Z]; exact hξE
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] at h1
    exact h1
  obtain ⟨U, hU, m, cc, S, hzU, hspan⟩ :=
    exists_chart_ideal_eq_span_coord p Z (π.base ξ) hzZ
  have hZU : restrictIdeal Z U = cc.coordIdeal S :=
    restrictIdeal_eq_coordIdeal_of_ideal_eq_span hU cc Z S hspan
  have hξU : ξ ∈ (TopologicalSpace.Opens.map π.base).obj U := hzU
  obtain ⟨s, hs, hξV⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π cc S hπ hZU ξ hξU
  set B := blowupChartOfIsBlowup π cc S hπ hZU s hs with hBdef
  have hV : IsAffineOpen B.domain := isAffineOpen_blowupChart_domain hU hπ hZU hs
  set φ := (π.appLE U B.domain B.domain_le).hom with hφdef
  set P : Ideal Γ(X₁, B.domain) := (hV.primeIdealOf ⟨ξ, hξV⟩).asIdeal with hPdef
  have hPprime : P.IsPrime := (hV.primeIdealOf ⟨ξ, hξV⟩).isPrime
  have hexcid : (Blowup.exceptionalIdeal π Z).ideal ⟨B.domain, hV⟩
      = Ideal.span {B.chart.coord s} :=
    exceptionalIdeal_ideal_blowupChart_domain hU hπ hZU hs
  have hyP : B.chart.coord s ∈ P := by
    have h := (mem_support_iff_ideal_le_primeIdealOf_consolidated292 (Blowup.exceptionalIdeal π Z) hV ⟨ξ, hξV⟩).mp hξE
    rw [hexcid] at h
    exact h (Ideal.mem_span_singleton_self _)
  have hJ'P : J'.ideal ⟨B.domain, hV⟩ ≤ P :=
    (mem_support_iff_ideal_le_primeIdealOf_consolidated292 J' hV ⟨ξ, hξV⟩).mp hξJ
  have hφs : φ (cc.coord s) = B.chart.coord s := B.appLE_coord_self
  have hφ : ∀ i ∈ S, i ≠ s → φ (cc.coord i) = B.chart.coord i * B.chart.coord s := by
    intro i hi his
    exact B.appLE_coord_of_mem i hi his
  have hy : B.chart.coord s ∈ nonZeroDivisors Γ(X₁, B.domain) :=
    coord_mem_nonZeroDivisors hV B.chart s
  set e0 := exceptionalQuotientEquivOfIsBlowup hU hπ hZU hs with he0
  set e : (Γ(X₁, B.domain) ⧸ Ideal.span {B.chart.coord s}) ≃+*
      MvPolynomial ↥(S.erase s)
        (Γ(X, U) ⧸ Ideal.span (cc.coord '' (S : Set (Fin m)))) :=
    e0.trans (MvPolynomial.mapEquiv (↥(S.erase s)) (Ideal.quotEquivOfEq hspan)) with hedef
  have heC : ∀ a : Γ(X, U), e (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}) (φ a)) =
      MvPolynomial.C (Ideal.Quotient.mk (Ideal.span (cc.coord '' (S : Set (Fin m)))) a) := by
    intro a
    have h1 : e0 (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}) (φ a))
        = MvPolynomial.C ((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)) a) :=
      exceptionalQuotientEquiv_mk_appLE hU hπ hZU hs a
    show MvPolynomial.map (Ideal.quotEquivOfEq hspan).toRingHom
        (e0 (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}) (φ a)))
      = MvPolynomial.C (Ideal.Quotient.mk (Ideal.span (cc.coord '' (S : Set (Fin m)))) a)
    rw [h1, MvPolynomial.map_C]
    exact congrArg MvPolynomial.C (Ideal.quotEquivOfEq_mk hspan a)
  have heX : ∀ t : ↥(S.erase s),
      e (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}) (B.chart.coord t.1))
        = MvPolynomial.X t := by
    intro t
    obtain ⟨hts, htS⟩ := Finset.mem_erase.mp t.2
    have h1 : e0 (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}) (B.chart.coord t.1))
        = MvPolynomial.X ⟨t.1, Finset.mem_erase.mpr ⟨hts, htS⟩⟩ :=
      exceptionalQuotientEquiv_mk_coord hU hπ hZU hs t.1 htS hts
    show MvPolynomial.map (Ideal.quotEquivOfEq hspan).toRingHom
        (e0 (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}) (B.chart.coord t.1)))
      = MvPolynomial.X t
    rw [h1]
    exact MvPolynomial.map_X _ _
  have hPmin : ∀ Q : Ideal Γ(X₁, B.domain), Q.IsPrime → Q ≤ P → B.chart.coord s ∈ Q → P ≤ Q := by
    intro Q hQ hQP hyQ
    have := hQ
    obtain ⟨pt, hpt⟩ := exists_primeIdealOf_eq_consolidated292 hV ⟨Q, hQ⟩
    have hptE : (pt : X₁) ∈ (Blowup.exceptionalIdeal π Z).support := by
      rw [mem_support_iff_ideal_le_primeIdealOf_consolidated292 (Blowup.exceptionalIdeal π Z) hV pt, hpt, hexcid]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hyQ)
    have hcont : Continuous (hV.fromSpec.base) := hV.fromSpec.base.hom.continuous
    have hQP' : (⟨Q, hQ⟩ : PrimeSpectrum Γ(X₁, B.domain)) ≤ hV.primeIdealOf ⟨ξ, hξV⟩ := hQP
    have hmem : hV.primeIdealOf ⟨ξ, hξV⟩ ∈
        closure ({(⟨Q, hQ⟩ : PrimeSpectrum Γ(X₁, B.domain))} :
          Set (PrimeSpectrum Γ(X₁, B.domain))) :=
      (PrimeSpectrum.le_iff_mem_closure _ _).mp hQP'
    have hfξ : hV.fromSpec.base (hV.primeIdealOf ⟨ξ, hξV⟩) = ξ :=
      hV.fromSpec_primeIdealOf ⟨ξ, hξV⟩
    have hfQ : hV.fromSpec.base (⟨Q, hQ⟩ : PrimeSpectrum Γ(X₁, B.domain)) = (pt : X₁) := by
      rw [← hpt]
      exact hV.fromSpec_primeIdealOf pt
    have hpre : IsClosed (hV.fromSpec.base ⁻¹' (closure ({(pt : X₁)} : Set X₁))) :=
      IsClosed.preimage hcont isClosed_closure
    have hQin : (⟨Q, hQ⟩ : PrimeSpectrum Γ(X₁, B.domain)) ∈
        hV.fromSpec.base ⁻¹' (closure ({(pt : X₁)} : Set X₁)) := by
      show hV.fromSpec.base (⟨Q, hQ⟩ : PrimeSpectrum Γ(X₁, B.domain))
        ∈ closure ({(pt : X₁)} : Set X₁)
      rw [hfQ]
      exact subset_closure rfl
    have hmem2 := closure_minimal (Set.singleton_subset_iff.mpr hQin) hpre hmem
    have h2 : ξ ∈ closure ({(pt : X₁)} : Set X₁) := by
      have h3 : hV.fromSpec.base (hV.primeIdealOf ⟨ξ, hξV⟩)
          ∈ closure ({(pt : X₁)} : Set X₁) := hmem2
      rwa [hfξ] at h3
    have hxx := eq_of_mem_closure_singleton_of_maximal_irreducible hCirr hCsub hCmax hclosed
      hξ hptE h2
    have hpteq : pt = (⟨ξ, hξV⟩ : ↥(B.domain)) := Subtype.ext hxx
    rw [hpteq] at hpt
    exact le_of_eq (congrArg PrimeSpectrum.asIdeal hpt)
  have hcosupp : ∀ x : X, x ∈ Z.support → x ∈ U → x ∈ orderAtLeastLocus J c := by
    intro x hx _
    rw [mem_orderAtLeastLocus_iff]
    exact le_of_eq (hord x hx).symm
  have hJpow : J.ideal ⟨U, hU⟩ ≤ Ideal.span (cc.coord '' (S : Set (Fin m))) ^ c := by
    have h := ideal_le_pow_of_restrictIdeal_eq_coordIdeal p hU cc Z S hZU c J hcosupp
    rw [hspan] at h
    exact h
  have hmap : Ideal.map φ (J.ideal ⟨U, hU⟩)
      ≤ Ideal.span {B.chart.coord s ^ c} * J'.ideal ⟨B.domain, hV⟩ := by
    have h1 : (J.comap π).ideal ⟨B.domain, hV⟩ = Ideal.map φ (J.ideal ⟨U, hU⟩) :=
      AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE J π ⟨U, hU⟩
        ⟨B.domain, hV⟩ B.domain_le
    have h2 : ((Blowup.exceptionalIdeal π Z) ^ c * J').ideal ⟨B.domain, hV⟩
        = ((Blowup.exceptionalIdeal π Z).ideal ⟨B.domain, hV⟩) ^ c * J'.ideal ⟨B.domain, hV⟩ := by
      rw [show ((Blowup.exceptionalIdeal π Z) ^ c * J').ideal ⟨B.domain, hV⟩
          = ((Blowup.exceptionalIdeal π Z) ^ c).ideal ⟨B.domain, hV⟩ * J'.ideal ⟨B.domain, hV⟩ from rfl,
        AlgebraicGeometry.Scheme.IdealSheafData.ideal_pow]
      rfl
    rw [← h1, ← htr, h2, hexcid, ← Ideal.span_singleton_pow]
  have hle := ideal_le_comap_pow_succ_of_map_le_span_pow_mul φ cc.coord B.chart.coord S s hs hφs hφ hy
    e heC heX P hyP hPmin c (J.ideal ⟨U, hU⟩) hJpow (J'.ideal ⟨B.domain, hV⟩) hJ'P hmap
  have hQcprime : (Ideal.comap φ P).IsPrime := Ideal.comap_isPrime φ P
  obtain ⟨pt', hpt'q⟩ :=
    exists_primeIdealOf_eq_consolidated292 hU ⟨Ideal.comap φ P, hQcprime⟩
  have hz'Z : (pt' : X) ∈ Z.support := by
    rw [mem_support_iff_ideal_le_primeIdealOf_consolidated292 Z hU pt', hpt'q, hspan]
    refine Ideal.span_le.mpr ?_
    rintro a ⟨i, hi, rfl⟩
    have hiS : i ∈ S := hi
    show cc.coord i ∈ Ideal.comap φ P
    rw [Ideal.mem_comap]
    by_cases his : i = s
    · subst his
      rw [hφs]
      exact hyP
    · rw [hφ i hiS his]
      exact Ideal.mul_mem_left _ _ hyP
  have horder : ((c + 1 : ℕ) : ℕ∞) ≤ orderAt J (pt' : X) := by
    refine le_orderAt_of_ideal_le_pow_consolidated292 J hU pt' (c + 1) ?_
    rw [hpt'q]
    exact hle
  rw [hord _ hz'Z] at horder
  have hcc : c + 1 ≤ c := by exact_mod_cast horder
  omega


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
section

open TopologicalSpace

section

section
variable {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)

private theorem comap_comp_eq_top_of_le_preimage_compl_consolidated294 (Z : X.IdealSheafData) (V : X₁.Opens) (hV : V ≤ π ⁻¹ᵁ Z.support.compl) :
    Z.comap (V.ι ≫ π) = ⊤ := by
  refine Blowup.comap_eq_top_of_notMem_support _ Z fun x => ?_
  show π.base x.1 ∉ Z.support
  exact hV x.2

private theorem restrictIdeal_comap_preimage_consolidated294 (D : X.IdealSheafData) (W : X.Opens) :
    restrictIdeal (D.comap π) (π ⁻¹ᵁ W) = (restrictIdeal D W).comap (π ∣_ W) := by
  rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι]


end

section
variable {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData) (E : List X.IdealSheafData)

private theorem length_strictTransform_append_exceptionalIdeal_consolidated294 :
    (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length = E.length + 1 := by
  simp

private theorem getElem_strictTransform_append_exceptionalIdeal_of_lt_consolidated294 (i : ℕ) (hi : i < E.length)
    {h : i < (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length} :
    (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z])[i]'h
      = Blowup.strictTransform π Z (E[i]'hi) := by
  rw [List.getElem_append_left (by simpa using hi)]
  simp

private theorem getElem_length_strictTransform_append_exceptionalIdeal_consolidated294 {h : E.length < (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length} :
    (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z])[E.length]'h
      = Blowup.exceptionalIdeal π Z := by
  rw [List.getElem_append_right (by simp)]
  simp


end

theorem isIso_morphismRestrict_of_isBlowupAlongIdealSheaf {X X₁ : Scheme.{u}} {π : X₁ ⟶ X}
    {Z : X.IdealSheafData} (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (W : X.Opens)
    (hW : ∀ x : X, x ∈ W → x ∉ Z.support) :
    IsIso (π ∣_ W) := by
  have h1 := hπ.restrict W
  have h2 : Z.comap (Scheme.Opens.ι W) = ⊤ := by
    refine Blowup.comap_eq_top_of_notMem_support _ Z fun x => ?_
    show x.1 ∉ Z.support
    exact hW x.1 x.2
  rw [h2] at h1
  exact h1.isIso_of_top

section
variable {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) [QuasiCompact (strictTransformι π Z D)] (V : X₁.Opens)

theorem restrictIdeal_strictTransform_eq_comap_of_le_compl (hV : V ≤ π ⁻¹ᵁ Z.support.compl) :
    restrictIdeal (Blowup.strictTransform π Z D) V = restrictIdeal (D.comap π) V := by
  have := quasiCompact_strictTransformι_comp_ι π Z D V
  have hZ : Z.comap (V.ι ≫ π) = ⊤ := comap_comp_eq_top_of_le_preimage_compl_consolidated294 π Z V hV
  rw [restrictIdeal_strictTransform π Z D V, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp]
  refine Scheme.IdealSheafData.ext ?_
  funext W
  exact strictTransform_ideal_eq_comap_of_isUnit (V.ι ≫ π) Z D W 1 (by simp [hZ]) isUnit_one

theorem restrictIdeal_strictTransform_eq_comap_of_notMem_support (hV : ∀ x : X₁, x ∈ V → π.base x ∉ Z.support) :
    restrictIdeal (Blowup.strictTransform π Z D) V = restrictIdeal (D.comap π) V := by
  refine restrictIdeal_strictTransform_eq_comap_of_le_compl π Z D V ?_
  intro x hx
  exact hV x hx


end

section
variable {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData) (V : X₁.Opens)

theorem restrictIdeal_exceptionalIdeal_eq_top_of_le_compl (hV : V ≤ π ⁻¹ᵁ Z.support.compl) :
    restrictIdeal (Blowup.exceptionalIdeal π Z) V = ⊤ := by
  rw [restrictIdeal_eq_comap_ι, Blowup.exceptionalIdeal_eq_comap, ← Scheme.IdealSheafData.comap_comp]
  exact comap_comp_eq_top_of_le_preimage_compl_consolidated294 π Z V hV

theorem restrictIdeal_exceptionalIdeal_eq_top_of_notMem_support (hV : ∀ x : X₁, x ∈ V → π.base x ∉ Z.support) :
    restrictIdeal (Blowup.exceptionalIdeal π Z) V = ⊤ := by
  refine restrictIdeal_exceptionalIdeal_eq_top_of_le_compl π Z V ?_
  intro x hx
  exact hV x hx


end

section
variable {X X₁ : Scheme.{u}} {k : Type u} [Field k] [NoetherianSpace X₁] (p : X ⟶ Spec (CommRingCat.of k)) (π : X₁ ⟶ X) (Z : X.IdealSheafData)

theorem inStrictNormalCrossingPositionAt_strictTransform_of_mem_support (E : List X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (hZE : HasStrictNormalCrossingsWith p Z E) (x₁ : X₁) (hx₁ : π.base x₁ ∈ Z.support) :
    InStrictNormalCrossingPositionAt (π ≫ p) (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]) x₁ := by
  classical
  have instQuasiCompact : ∀ D : X.IdealSheafData, QuasiCompact (strictTransformι π Z D) :=
    fun D => quasiCompact_strictTransformι_of_noetherianSpace π Z D
  unfold HasStrictNormalCrossingsWith at hZE
  obtain ⟨U, hxU, m, c, a, S, ha1, ha2, ha3, hZU⟩ := hZE _ hx₁
  have hxmem : x₁ ∈ π ⁻¹ᵁ U := hxU
  obtain ⟨s, hs, hx₁B⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZU x₁ hxmem
  set B := blowupChartOfIsBlowup π c S hπ hZU s hs with hBdef
  have hlen : (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length = E.length + 1 :=
    length_strictTransform_append_exceptionalIdeal_consolidated294 π Z E
  unfold InStrictNormalCrossingPositionAt
  refine ⟨B.domain, hx₁B, m, B.chart,
    fun i => if i = E.length then some s else if a i = some s then none else a i, ?_, ?_, ?_⟩
  · intro i hi j hj t hti htj
    have hti' : (if i = E.length then some s else if a i = some s then none else a i) = some t :=
      hti
    have htj' : (if j = E.length then some s else if a j = some s then none else a j) = some t :=
      htj
    rw [hlen] at hi hj
    by_cases hiE : i = E.length
    · by_cases hjE : j = E.length
      · rw [hiE, hjE]
      · exfalso
        rw [if_pos hiE] at hti'
        rw [if_neg hjE] at htj'
        have hts : s = t := Option.some.inj hti'
        by_cases haj : a j = some s
        · rw [if_pos haj] at htj'
          simp at htj'
        · rw [if_neg haj] at htj'
          exact haj (by rw [htj', ← hts])
    · by_cases hjE : j = E.length
      · exfalso
        rw [if_pos hjE] at htj'
        rw [if_neg hiE] at hti'
        have hts : s = t := Option.some.inj htj'
        by_cases hai : a i = some s
        · rw [if_pos hai] at hti'
          simp at hti'
        · rw [if_neg hai] at hti'
          exact hai (by rw [hti', ← hts])
      · rw [if_neg hiE] at hti'
        rw [if_neg hjE] at htj'
        by_cases hai : a i = some s
        · rw [if_pos hai] at hti'
          simp at hti'
        · rw [if_neg hai] at hti'
          by_cases haj : a j = some s
          · rw [if_pos haj] at htj'
            simp at htj'
          · rw [if_neg haj] at htj'
            exact ha1 i (by omega) j (by omega) t hti' htj'
  · intro i h hnone
    have hnone' : (if i = E.length then some s else if a i = some s then none else a i) = none :=
      hnone
    have hcount : i < E.length + 1 := by rw [hlen] at h; exact h
    by_cases hiE : i = E.length
    · rw [if_pos hiE] at hnone'
      simp at hnone'
    · have hi : i < E.length := by omega
      rw [getElem_strictTransform_append_exceptionalIdeal_of_lt_consolidated294 π Z E i hi]
      rw [if_neg hiE] at hnone'
      by_cases hai : a i = some s
      · have hD := ha3 i hi s hai
        have hres := BlowupChart.restrictIdeal_strictTransform_coordIdeal B Z (E[i]'hi) hs hZU s hD
        simpa using hres
      · rw [if_neg hai] at hnone'
        exact BlowupChart.restrictIdeal_strictTransform_of_eq_top B Z (E[i]'hi) (ha2 i hi hnone')
  · intro i h t hti
    have hti' : (if i = E.length then some s else if a i = some s then none else a i) = some t :=
      hti
    have hcount : i < E.length + 1 := by rw [hlen] at h; exact h
    by_cases hiE : i = E.length
    · subst hiE
      rw [getElem_length_strictTransform_append_exceptionalIdeal_consolidated294 π Z E]
      have hts : s = t := by simpa using hti'
      rw [← hts]
      exact BlowupChart.restrictIdeal_exceptionalIdeal B Z hs hZU
    · have hi : i < E.length := by omega
      rw [getElem_strictTransform_append_exceptionalIdeal_of_lt_consolidated294 π Z E i hi]
      rw [if_neg hiE] at hti'
      by_cases hai : a i = some s
      · rw [if_pos hai] at hti'
        simp at hti'
      · rw [if_neg hai] at hti'
        have hD := ha3 i hi t hti'
        have hts : t ≠ s := by
          intro hh
          exact hai (by rw [hti', hh])
        rw [BlowupChart.restrictIdeal_strictTransform_coordIdeal B Z (E[i]'hi) hs hZU t hD,
          if_neg hts]

theorem inStrictNormalCrossingPositionAt_strictTransform_of_notMem_support (E : List X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (hE : InStrictNormalCrossingPosition p E) (x₁ : X₁) (hx₁ : π.base x₁ ∉ Z.support) :
    InStrictNormalCrossingPositionAt (π ≫ p) (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]) x₁ := by
  classical
  have instQuasiCompact : ∀ D : X.IdealSheafData, QuasiCompact (strictTransformι π Z D) :=
    fun D => quasiCompact_strictTransformι_of_noetherianSpace π Z D
  rw [inStrictNormalCrossingPosition_iff] at hE
  obtain ⟨hEdiv, hEpos⟩ := hE
  have hpos := hEpos (π.base x₁)
  unfold InStrictNormalCrossingPositionAt at hpos
  obtain ⟨U, hxU, m, c, a, ha1, ha2, ha3⟩ := hpos
  have hWU : U ⊓ Z.support.compl ≤ U := inf_le_left
  have hiso : IsIso (π ∣_ (U ⊓ Z.support.compl)) :=
    isIso_morphismRestrict_of_isBlowupAlongIdealSheaf hπ (U ⊓ Z.support.compl) (fun x hx => hx.2)
  have hxW : π.base x₁ ∈ U ⊓ Z.support.compl := ⟨hxU, hx₁⟩
  have hVle : (π ⁻¹ᵁ (U ⊓ Z.support.compl)) ≤ π ⁻¹ᵁ Z.support.compl := fun x hx => hx.2
  have hcs : ((π ∣_ (U ⊓ Z.support.compl)) ≫ (c.restrict hWU).map) ≫ affineSpaceFinToSpec k m
      = (π ⁻¹ᵁ (U ⊓ Z.support.compl)).ι ≫ (π ≫ p) := by
    rw [Category.assoc, (c.restrict hWU).comp_struct, ← Category.assoc, morphismRestrict_ι,
      Category.assoc]
  have het : Etale ((π ∣_ (U ⊓ Z.support.compl)) ≫ (c.restrict hWU).map) := by
    have : IsIso (π ∣_ (U ⊓ Z.support.compl)) := hiso
    have : Etale (c.restrict hWU).map := (c.restrict hWU).isEtale
    infer_instance
  have hlen : (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length = E.length + 1 :=
    length_strictTransform_append_exceptionalIdeal_consolidated294 π Z E
  unfold InStrictNormalCrossingPositionAt
  refine ⟨π ⁻¹ᵁ (U ⊓ Z.support.compl), hxW, m,
    ⟨(π ∣_ (U ⊓ Z.support.compl)) ≫ (c.restrict hWU).map, hcs, het⟩,
    fun i => if i = E.length then none else a i, ?_, ?_, ?_⟩
  · intro i hi j hj t hti htj
    have hti' : (if i = E.length then none else a i) = some t := hti
    have htj' : (if j = E.length then none else a j) = some t := htj
    rw [hlen] at hi hj
    have hiE : i ≠ E.length := by
      intro hh
      rw [if_pos hh] at hti'
      simp at hti'
    have hjE : j ≠ E.length := by
      intro hh
      rw [if_pos hh] at htj'
      simp at htj'
    rw [if_neg hiE] at hti'
    rw [if_neg hjE] at htj'
    exact ha1 i (by omega) j (by omega) t hti' htj'
  · intro i h hnone
    have hcount : i < E.length + 1 := by rw [hlen] at h; exact h
    by_cases hiE : i = E.length
    · subst hiE
      rw [getElem_length_strictTransform_append_exceptionalIdeal_consolidated294 π Z E]
      exact restrictIdeal_exceptionalIdeal_eq_top_of_le_compl π Z _ hVle
    · have hi : i < E.length := by omega
      have hnone' : (if i = E.length then none else a i) = none := hnone
      rw [if_neg hiE] at hnone'
      rw [getElem_strictTransform_append_exceptionalIdeal_of_lt_consolidated294 π Z E i hi,
        restrictIdeal_strictTransform_eq_comap_of_le_compl π Z (E[i]'hi) _ hVle,
        restrictIdeal_comap_preimage_consolidated294 π (E[i]'hi) (U ⊓ Z.support.compl),
        restrictIdeal_eq_top_of_le (E[i]'hi) hWU (ha2 i hi hnone')]
      exact Scheme.IdealSheafData.comap_top _
  · intro i h t hti
    have hti' : (if i = E.length then none else a i) = some t := hti
    have hcount : i < E.length + 1 := by rw [hlen] at h; exact h
    have hiE : i ≠ E.length := by
      intro hh
      rw [if_pos hh] at hti'
      simp at hti'
    have hi : i < E.length := by omega
    rw [if_neg hiE] at hti'
    rw [getElem_strictTransform_append_exceptionalIdeal_of_lt_consolidated294 π Z E i hi,
      restrictIdeal_strictTransform_eq_comap_of_le_compl π Z (E[i]'hi) _ hVle,
      restrictIdeal_comap_preimage_consolidated294 π (E[i]'hi) (U ⊓ Z.support.compl),
      restrictIdeal_eq_restrict_coordIdeal_of_le hWU c (E[i]'hi) {t} (ha3 i hi t hti')]
    simp only [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
    exact (Scheme.IdealSheafData.comap_comp ..).symm

theorem inStrictNormalCrossingPosition_strictTransform_append (E : List X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hE : InStrictNormalCrossingPosition p E)
    (hZE : HasStrictNormalCrossingsWith p Z E) :
    InStrictNormalCrossingPosition (π ≫ p) (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]) := by
  classical
  have hat : ∀ x₁ : X₁,
      InStrictNormalCrossingPositionAt (π ≫ p) (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]) x₁ := by
    intro x₁
    by_cases hx : π.base x₁ ∈ Z.support
    · exact inStrictNormalCrossingPositionAt_strictTransform_of_mem_support p π Z E hπ hZE x₁ hx
    · exact inStrictNormalCrossingPositionAt_strictTransform_of_notMem_support p π Z E hπ hE x₁ hx
  rw [inStrictNormalCrossingPosition_iff]
  refine ⟨?_, hat⟩
  intro D hD
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hD
  refine isSmoothDivisor_of_locally_coordIdeal _ fun x₁ => ?_
  have hx := hat x₁
  unfold InStrictNormalCrossingPositionAt at hx
  obtain ⟨U, hxU, m, c, a, h1, h2, h3⟩ := hx
  refine ⟨U, hxU, m, c, ?_⟩
  cases hai : a i with
  | none => exact Or.inl (h2 i hi hai)
  | some t => exact Or.inr ⟨t, h3 i hi t hai⟩

theorem inStrictNormalCrossingPosition_strictTransform_cons_append (H : X.IdealSheafData) (E : List X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (hE : InStrictNormalCrossingPosition p (H :: E)) (hZE : HasStrictNormalCrossingsWith p Z (H :: E)) :
    InStrictNormalCrossingPosition (π ≫ p)
      (Blowup.strictTransform π Z H :: (E.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z])) :=
  inStrictNormalCrossingPosition_strictTransform_append p π Z (H :: E) hπ hE hZE


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformChart
section

open Opposite TopologicalSpace

section

def complEmbPreimage (m : ℕ) (S : Finset (Fin m)) (a : Fin m) :
    Finset (Fin (m - ({a} : Finset (Fin m)).card)) :=
  Finset.filter (fun i => complOrderEmb m {a} i ∈ S) Finset.univ

section
variable (m : ℕ) (S : Finset (Fin m)) (a : Fin m)

theorem mem_complEmbPreimage (i : Fin (m - ({a} : Finset (Fin m)).card)) :
    i ∈ complEmbPreimage m S a ↔ complOrderEmb m {a} i ∈ S := by
  simp [complEmbPreimage]

theorem mem_complEmbPreimage_of_complOrderEmb_eq {s : Fin m} (hs : s ∈ S) {i : Fin (m - ({a} : Finset (Fin m)).card)}
    (hi : complOrderEmb m {a} i = s) : i ∈ complEmbPreimage m S a := by
  rw [mem_complEmbPreimage, hi]
  exact hs


end

variable {X X₁ : Scheme.{u}} {k : Type u} [Field k]
  {p : X ⟶ Spec (CommRingCat.of k)} {π : X₁ ⟶ X} {U : X.Opens} {m : ℕ}
  {c : EtaleChart p U m} {S : Finset (Fin m)} {s : Fin m}

private theorem blowupChart_restrict_map_comp_coordBlowupSubstMap_consolidated293 (B : BlowupChart π c S s) (V : X₁.Opens)
    (hV : V ≤ B.domain) :
    (B.chart.restrict hV).map ≫ coordBlowupSubstMap k m S s =
      π.resLE U V (hV.trans B.domain_le) ≫ c.map := by
  have key : X₁.homOfLE hV ≫ π.resLE U B.domain B.domain_le
      = π.resLE U V (hV.trans B.domain_le) := by
    apply (cancel_mono (Scheme.Opens.ι U)).mp
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.homOfLE_ι,
      Scheme.Hom.resLE_comp_ι]
  rw [EtaleChart.restrict_map, Category.assoc, B.comm, ← Category.assoc, key]

def BlowupChart.restrict (B : BlowupChart π c S s) (V : X₁.Opens) (hV : V ≤ B.domain) :
    BlowupChart π c S s where
  domain := V
  domain_le := hV.trans B.domain_le
  chart := B.chart.restrict hV
  comm := blowupChart_restrict_map_comp_coordBlowupSubstMap_consolidated293 B V hV

section
variable (B : BlowupChart π c S s)

@[simp] theorem BlowupChart.restrict_domain (V : X₁.Opens)
    (hV : V ≤ B.domain) : (B.restrict V hV).domain = V := rfl

theorem BlowupChart.exists_isAffineOpen_mem_le_domain (x : X₁)
    (hx : x ∈ B.domain) :
    ∃ V : X₁.Opens, V ≤ B.domain ∧ IsAffineOpen V ∧ x ∈ V := by
  obtain ⟨V, hV, hxV, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X₁.isBasis_affineOpens hx
  exact ⟨V, hVU, hV, hxV⟩


end

section
variable {Y : Scheme.{u}}

private theorem opensι_appLE_top_eq_topIso_inv_consolidated293 (V : Y.Opens) :
    V.ι.appLE V ⊤ (Scheme.Opens.ι_preimage_self V).ge = V.topIso.inv := by
  simp
  rfl

private theorem coordIdeal_ideal_top_eq_map_consolidated293 {K : Type u} [Field K]
    {p' : Y ⟶ Spec (CommRingCat.of K)} {V : Y.Opens} {n : ℕ} [IsAffine V.toScheme]
    (d : EtaleChart p' V n) (T : Finset (Fin n)) :
    (d.coordIdeal T).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩ =
      Ideal.map V.topIso.inv.hom (Ideal.span (d.coord '' (T : Set (Fin n)))) := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, Scheme.IdealSheafData.comap_ideal_top_eq_map_appTop,
    coordSubspaceIdeal_eq_ofIdealTop_span_coord, Scheme.IdealSheafData.ofIdealTop_ideal_top, Ideal.map_span,
    Ideal.map_span, ← Set.image_comp, ← Set.image_comp]
  refine congrArg Ideal.span (Set.image_congr fun j _ => ?_)
  exact (CommRingCat.inv_hom_apply V.topIso _).symm

private theorem comap_opensι_ideal_top_eq_map_consolidated293 (J : Y.IdealSheafData)
    {V : Y.Opens} (hV : IsAffineOpen V) [IsAffine V.toScheme] :
    (J.comap V.ι).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩
      = Ideal.map V.topIso.inv.hom (J.ideal ⟨V, hV⟩) := by
  rw [← opensι_appLE_top_eq_topIso_inv_consolidated293 V]
  exact Scheme.IdealSheafData.comap_ideal_eq_map_appLE J V.ι ⟨V, hV⟩
    ⟨⊤, isAffineOpen_top V.toScheme⟩ (Scheme.Opens.ι_preimage_self V).ge

private theorem etaleChart_map_appTop_coord_consolidated293 {K : Type u} [Field K]
    {p' : Y ⟶ Spec (CommRingCat.of K)} {V : Y.Opens} {n : ℕ} (d : EtaleChart p' V n)
    (j : Fin n) :
    (Scheme.Hom.appTop d.map).hom (AffineSpace.coord (Spec (CommRingCat.of K)) (ULift.up j))
      = V.topIso.inv.hom (d.coord j) := by
  rw [EtaleChart.coord_def]
  exact (CommRingCat.inv_hom_apply V.topIso _).symm


end

private theorem appLE_top_top_eq_appTop_consolidated293 {A B : Scheme.{u}} (f : A ⟶ B)
    (e : (⊤ : A.Opens) ≤ f ⁻¹ᵁ (⊤ : B.Opens)) :
    f.appLE (⊤ : B.Opens) (⊤ : A.Opens) e = Scheme.Hom.appTop f := by
  have h1 : A.presheaf.map (homOfLE e).op = 𝟙 Γ(A, ⊤) := A.presheaf.map_id (op (⊤ : A.Opens))
  calc f.appLE (⊤ : B.Opens) (⊤ : A.Opens) e
      = f.app (⊤ : B.Opens) ≫ A.presheaf.map (homOfLE e).op := rfl
    _ = f.app (⊤ : B.Opens) ≫ 𝟙 Γ(A, ⊤) := by rw [h1]
    _ = Scheme.Hom.appTop f := Category.comp_id _

theorem restrictIdeal_comap_subschemeι_eq_coordIdeal (c : EtaleChart p U m)
    (hU : IsAffineOpen U) (Z H : X.IdealSheafData) (S : Finset (Fin m)) (a : Fin m)
    (hZ : restrictIdeal Z U = c.coordIdeal S)
    (hH : restrictIdeal H U = c.coordIdeal {a}) :
    restrictIdeal (Z.comap H.subschemeι) (H.subschemeι ⁻¹ᵁ U) =
      (c.restrictToSubscheme hU H {a} hH).coordIdeal (complEmbPreimage m S a) := by
  classical
  have hW : IsAffineOpen (H.subschemeι ⁻¹ᵁ U) := isAffineOpen_preimage_subschemeι H hU
  have : IsAffine (H.subschemeι ⁻¹ᵁ U).toScheme := hW
  have hmem : c.coord a ∈ H.ideal ⟨U, hU⟩ := by
    rw [c.ideal_eq_span_coord hU H {a} hH]
    exact Ideal.subset_span ⟨a, by simp, rfl⟩
  have hφa : (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom (c.coord a) = 0 := by
    have happ := Scheme.IdealSheafData.subschemeι_app H ⟨U, hU⟩
    have hval := congrArg (fun f => (CommRingCat.Hom.hom f) (c.coord a)) happ
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hval
    rw [Scheme.Hom.appLE_eq_app, hval,
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
  have hspan : Ideal.span
        ((H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom ''
          (c.coord '' (S : Set (Fin m))))
      = Ideal.span ((c.restrictToSubscheme hU H {a} hH).coord ''
          ((complEmbPreimage m S a : Finset (Fin (m - ({a} : Finset (Fin m)).card))) :
            Set (Fin (m - ({a} : Finset (Fin m)).card)))) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro x ⟨y, ⟨j, hj, rfl⟩, rfl⟩
      by_cases hja : j = a
      · subst hja
        rw [hφa]
        exact Ideal.zero_mem _
      · have hjnot : j ∉ ({a} : Finset (Fin m)) := by simpa using hja
        obtain ⟨i, hi⟩ := exists_complOrderEmb_eq m ({a} : Finset (Fin m)) hjnot
        have hiT : i ∈ complEmbPreimage m S a :=
          mem_complEmbPreimage_of_complOrderEmb_eq m S a (Finset.mem_coe.mp hj) hi
        refine Ideal.subset_span ⟨i, Finset.mem_coe.mpr hiT, ?_⟩
        rw [c.restrictToSubscheme_coord hU H {a} hH i, hi]
    · rw [Ideal.span_le]
      rintro x ⟨i, hi, rfl⟩
      rw [c.restrictToSubscheme_coord hU H {a} hH i]
      exact Ideal.subset_span ⟨c.coord (complOrderEmb m {a} i),
        ⟨complOrderEmb m {a} i, Finset.mem_coe.mpr ((mem_complEmbPreimage m S a i).mp
          (Finset.mem_coe.mp hi)), rfl⟩, rfl⟩
  have hideal : (restrictIdeal (Z.comap H.subschemeι) (H.subschemeι ⁻¹ᵁ U)).ideal
        ⟨⊤, isAffineOpen_top (H.subschemeι ⁻¹ᵁ U).toScheme⟩
      = ((c.restrictToSubscheme hU H {a} hH).coordIdeal (complEmbPreimage m S a)).ideal
        ⟨⊤, isAffineOpen_top (H.subschemeι ⁻¹ᵁ U).toScheme⟩ := by
    rw [restrictIdeal_eq_comap_ι, comap_opensι_ideal_top_eq_map_consolidated293 (Z.comap H.subschemeι) hW,
      coordIdeal_ideal_top_eq_map_consolidated293,
      Scheme.IdealSheafData.comap_ideal_eq_map_appLE Z H.subschemeι ⟨U, hU⟩
        ⟨H.subschemeι ⁻¹ᵁ U, hW⟩ le_rfl,
      c.ideal_eq_span_coord hU Z S hZ, Ideal.map_span, hspan]
  exact (Scheme.IdealSheafData.equivOfIsAffine
    (X := (H.subschemeι ⁻¹ᵁ U).toScheme)).injective hideal

section
variable (B : BlowupChart π c S s)

private theorem strictTransform_preimage_domain_le_preimage_consolidated293 (Z H : X.IdealSheafData)
    (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π) :
    (Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain ≤ q ⁻¹ᵁ (H.subschemeι ⁻¹ᵁ U) := by
  intro y hy
  have h2 : ((Blowup.strictTransform π Z H).subschemeι ≫ π).base y ∈ U := B.domain_le hy
  rw [← hq] at h2
  exact h2

private theorem restrictToSubscheme_map_comp_affineSpaceFinToSpec_consolidated293 (hB : IsAffineOpen B.domain) (Z H : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (a : Fin m) (ha : a ∈ S) (has : a ≠ s) (hH : restrictIdeal H U = c.coordIdeal {a})
    (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π) :
    (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a}
        (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).map ≫
          affineSpaceFinToSpec k (m - ({a} : Finset (Fin m)).card) =
      ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain).ι ≫ (q ≫ (H.subschemeι ≫ p)) := by
  have h := (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a}
    (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).comp_struct
  rw [h, ← Category.assoc (Blowup.strictTransform π Z H).subschemeι π p, ← hq, Category.assoc]

private theorem restrictToSubscheme_map_comp_coordBlowupSubstMap_consolidated293 (hU : IsAffineOpen U) (hB : IsAffineOpen B.domain) (Z H : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (a : Fin m) (ha : a ∈ S) (has : a ≠ s) (hH : restrictIdeal H U = c.coordIdeal {a})
    (s' : Fin (m - ({a} : Finset (Fin m)).card)) (hs' : complOrderEmb m {a} s' = s)
    (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π) :
    (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a}
        (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).map ≫
          coordBlowupSubstMap k (m - ({a} : Finset (Fin m)).card) (complEmbPreimage m S a) s' =
      q.resLE (H.subschemeι ⁻¹ᵁ U) ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain)
          (strictTransform_preimage_domain_le_preimage_consolidated293 B Z H q hq) ≫
        (c.restrictToSubscheme hU H {a} hH).map := by
  classical
  have hle := strictTransform_preimage_domain_le_preimage_consolidated293 B Z H q hq
  have hr : q.resLE (H.subschemeι ⁻¹ᵁ U)
        ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle ≫ (H.subschemeι ⁻¹ᵁ U).ι
      = ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain).ι ≫ q := by
    rw [Scheme.Hom.resLE_comp_ι]
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, coordBlowupSubstMap_comp_affineSpaceFinToSpec,
      restrictToSubscheme_map_comp_affineSpaceFinToSpec_consolidated293 B hB Z H hs hZ a ha has hH q hq,
      (c.restrictToSubscheme hU H {a} hH).comp_struct]
    simp only [← Category.assoc]
    rw [hr]
  · rintro ⟨i₀⟩
    have hL : ∀ j : Fin (m - ({a} : Finset (Fin m)).card),
        (Scheme.Hom.appTop (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a}
            (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).map).hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j))
          = ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain).topIso.inv.hom
              (((Blowup.strictTransform π Z H).subschemeι.appLE B.domain
                ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) le_rfl).hom
                (B.chart.coord (complOrderEmb m {a} j))) := by
      intro j
      rw [etaleChart_map_appTop_coord_consolidated293, EtaleChart.restrictToSubscheme_coord]
    have hM : ∀ j : Fin (m - ({a} : Finset (Fin m)).card),
        (Scheme.Hom.appTop (c.restrictToSubscheme hU H {a} hH).map).hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j))
          = (H.subschemeι ⁻¹ᵁ U).topIso.inv.hom
              ((H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom
                (c.coord (complOrderEmb m {a} j))) := by
      intro j
      rw [etaleChart_map_appTop_coord_consolidated293, EtaleChart.restrictToSubscheme_coord]
    have hkey : H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl
          ≫ q.appLE (H.subschemeι ⁻¹ᵁ U)
              ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle
        = π.appLE U B.domain B.domain_le
          ≫ (Blowup.strictTransform π Z H).subschemeι.appLE B.domain
              ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) le_rfl := by
      rw [Scheme.Hom.appLE_comp_appLE q H.subschemeι U (H.subschemeι ⁻¹ᵁ U)
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) le_rfl hle,
        Scheme.Hom.appLE_comp_appLE (Blowup.strictTransform π Z H).subschemeι π U B.domain
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) B.domain_le le_rfl]
      exact Scheme.Hom.appLE_congr_hom hq _ _ _ _
    have hkeyfun : ∀ x : Γ(X, U),
        (q.appLE (H.subschemeι ⁻¹ᵁ U)
            ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle).hom
          ((H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom x)
        = ((Blowup.strictTransform π Z H).subschemeι.appLE B.domain
            ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) le_rfl).hom
          ((π.appLE U B.domain B.domain_le).hom x) := by
      intro x
      have h := congrArg (fun f => (CommRingCat.Hom.hom f) x) hkey
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
      exact h
    have e2 : (⊤ : ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain).toScheme.Opens)
        ≤ (q.resLE (H.subschemeι ⁻¹ᵁ U)
            ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle)
            ⁻¹ᵁ (⊤ : (H.subschemeι ⁻¹ᵁ U).toScheme.Opens) := by simp
    have hres : (H.subschemeι ⁻¹ᵁ U).topIso.inv ≫
          Scheme.Hom.appTop (q.resLE (H.subschemeι ⁻¹ᵁ U)
            ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle)
        = q.appLE (H.subschemeι ⁻¹ᵁ U)
            ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle
          ≫ ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain).topIso.inv := by
      rw [← opensι_appLE_top_eq_topIso_inv_consolidated293 (H.subschemeι ⁻¹ᵁ U),
        ← appLE_top_top_eq_appTop_consolidated293 (q.resLE (H.subschemeι ⁻¹ᵁ U)
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle) e2,
        Scheme.Hom.appLE_comp_appLE (q.resLE (H.subschemeι ⁻¹ᵁ U)
            ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle)
          (H.subschemeι ⁻¹ᵁ U).ι (H.subschemeι ⁻¹ᵁ U) ⊤ ⊤ (Scheme.Opens.ι_preimage_self _).ge e2,
        ← opensι_appLE_top_eq_topIso_inv_consolidated293
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain),
        Scheme.Hom.appLE_comp_appLE
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain).ι q (H.subschemeι ⁻¹ᵁ U)
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) ⊤ hle
          (Scheme.Opens.ι_preimage_self _).ge]
      exact Scheme.Hom.appLE_congr_hom hr _ _ _ _
    have hstar : ∀ y : Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U),
        (Scheme.Hom.appTop (q.resLE (H.subschemeι ⁻¹ᵁ U)
            ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle)).hom
          ((H.subschemeι ⁻¹ᵁ U).topIso.inv.hom y)
        = ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain).topIso.inv.hom
            ((q.appLE (H.subschemeι ⁻¹ᵁ U)
              ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) hle).hom y) := by
      intro y
      have h := congrArg (fun f => (CommRingCat.Hom.hom f) y) hres
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
      exact h
    have hcond : (complOrderEmb m {a} i₀ ∈ S ∧ complOrderEmb m {a} i₀ ≠ s)
        ↔ (i₀ ∈ complEmbPreimage m S a ∧ i₀ ≠ s') := by
      rw [mem_complEmbPreimage]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hh => h2 (by rw [hh, hs'])⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hh => h2 ((complOrderEmb m {a}).injective (by rw [hh, hs']))⟩
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    rw [coordBlowupSubstMap_appTop_coord, hM i₀, hstar, hkeyfun,
      BlowupChart.appLE_coord B (complOrderEmb m {a} i₀)]
    by_cases hP : complOrderEmb m {a} i₀ ∈ S ∧ complOrderEmb m {a} i₀ ≠ s
    · rw [if_pos hP, if_pos (hcond.mp hP)]
      simp only [map_mul]
      rw [hL i₀, hL s', hs']
    · rw [if_neg hP, if_neg (fun hh => hP (hcond.mpr hh))]
      exact hL i₀


end

def BlowupChart.restrictToStrictTransform (B : BlowupChart π c S s)
    (hU : IsAffineOpen U) (hB : IsAffineOpen B.domain) (Z H : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (a : Fin m) (ha : a ∈ S) (has : a ≠ s) (hH : restrictIdeal H U = c.coordIdeal {a})
    (s' : Fin (m - ({a} : Finset (Fin m)).card)) (hs' : complOrderEmb m {a} s' = s)
    (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π) :
    BlowupChart q (c.restrictToSubscheme hU H {a} hH) (complEmbPreimage m S a) s' where
  domain := (Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain
  domain_le := strictTransform_preimage_domain_le_preimage_consolidated293 B Z H q hq
  chart :=
    { map := (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a}
        (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).map
      comp_struct :=
        restrictToSubscheme_map_comp_affineSpaceFinToSpec_consolidated293 B hB Z H hs hZ a ha has hH q hq
      isEtale := (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a}
        (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).isEtale }
  comm :=
    restrictToSubscheme_map_comp_coordBlowupSubstMap_consolidated293 B hU hB Z H hs hZ a ha has hH s' hs' q hq

section
variable (B : BlowupChart π c S s)

theorem BlowupChart.restrictToStrictTransform_chart_map (hU : IsAffineOpen U) (hB : IsAffineOpen B.domain) (Z H : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (a : Fin m) (ha : a ∈ S) (has : a ≠ s) (hH : restrictIdeal H U = c.coordIdeal {a})
    (s' : Fin (m - ({a} : Finset (Fin m)).card)) (hs' : complOrderEmb m {a} s' = s)
    (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π) :
    (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s' hs' q hq).chart.map =
      (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a}
        (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).map := rfl

theorem BlowupChart.strictTransform_subschemeι_preimage_domain_eq_bot (Z H : X.IdealSheafData) [QuasiCompact (strictTransformι π Z H)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (hH : restrictIdeal H U = c.coordIdeal {s}) :
    (Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain = ⊥ := by
  have htop : restrictIdeal (Blowup.strictTransform π Z H) B.domain = ⊤ :=
    B.restrictIdeal_strictTransform_coordIdeal_self Z H hs hZ hH
  rw [eq_bot_iff]
  intro y hy
  have hxB : (Blowup.strictTransform π Z H).subschemeι.base y ∈ B.domain := hy
  have hxsupp : (Blowup.strictTransform π Z H).subschemeι.base y ∈ (Blowup.strictTransform π Z H).support := by
    have hr : (Blowup.strictTransform π Z H).subschemeι.base y ∈
        Set.range (Blowup.strictTransform π Z H).subschemeι.base := Set.mem_range_self y
    rwa [Scheme.IdealSheafData.range_subschemeι] at hr
  have h1 : (⟨_, hxB⟩ : ↥B.domain) ∈ ((Blowup.strictTransform π Z H).comap B.domain.ι).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hxsupp
  rw [← restrictIdeal_eq_comap_ι, htop, Scheme.IdealSheafData.support_top] at h1
  have h2 : (⟨_, hxB⟩ : ↥B.domain) ∈ ((⊥ : TopologicalSpace.Closeds ↥B.domain) : Set ↥B.domain) :=
    h1
  simp at h2


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformSubscheme
section

open TopologicalSpace

section

private theorem surjective_hom_iso_inv_consolidated310 {A B : CommRingCat.{u}} (e : A ≅ B) :
    Function.Surjective (CommRingCat.Hom.hom e.inv) := by
  intro a
  refine ⟨CommRingCat.Hom.hom e.hom a, ?_⟩
  simp

section
variable {Y : Scheme.{u}}

private theorem surjective_subschemeι_app_consolidated310 (I : Y.IdealSheafData)
    (U : Y.affineOpens) :
    Function.Surjective (CommRingCat.Hom.hom (I.subschemeι.app (U : Y.Opens))) := by
  rw [Scheme.IdealSheafData.subschemeι_app, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
    RingHom.coe_comp]
  exact (surjective_hom_iso_inv_consolidated310 (I.subschemeObjIso U)).comp Ideal.Quotient.mk_surjective

theorem isLocallyNoetherian_subscheme [IsLocallyNoetherian Y]
    (I : Y.IdealSheafData) : IsLocallyNoetherian I.subscheme := by
  refine isLocallyNoetherian_of_affine_cover
    (S := fun U : Y.affineOpens =>
      (⟨I.subschemeι ⁻¹ᵁ (U : Y.Opens), isAffineOpen_preimage_subschemeι I U.2⟩ :
        I.subscheme.affineOpens)) ?_ ?_
  · ext x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have hx : I.subschemeι.base x ∈ (⨆ V : Y.affineOpens, (V : Y.Opens)) := by
      rw [iSup_affineOpens_eq_top Y]
      trivial
    obtain ⟨V, hV⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨V, hV⟩
  · intro U
    have := IsLocallyNoetherian.component_noetherian U
    exact isNoetherianRing_of_surjective _ _ _ (surjective_subschemeι_app_consolidated310 I U)

theorem notMem_support_of_restrictIdeal_eq_top (D : Y.IdealSheafData)
    (U : Y.Opens) (x : Y) (hx : x ∈ U) (h : restrictIdeal D U = ⊤) : x ∉ D.support :=
  Scheme.IdealSheafData.notMem_support_of_comap_ι_eq_top D h hx


end

private theorem ideal_eq_of_map_eq_of_comp_eq_id_consolidated310 {R S : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ R)
    (hfg : f ≫ g = 𝟙 R) {I J : Ideal R}
    (hIJ : Ideal.map (CommRingCat.Hom.hom f) I = Ideal.map (CommRingCat.Hom.hom f) J) : I = J := by
  have key : ∀ K : Ideal R,
      Ideal.map (CommRingCat.Hom.hom g) (Ideal.map (CommRingCat.Hom.hom f) K) = K := by
    intro K
    rw [Ideal.map_map, ← CommRingCat.hom_comp, hfg, CommRingCat.hom_id, Ideal.map_id]
  rw [← key I, hIJ, key J]

section
variable {Y : Scheme.{u}}

private theorem presheaf_map_eq_id_consolidated310 {P : (Y.Opens)ᵒᵖ} (f : P ⟶ P) :
    Y.presheaf.map f = 𝟙 (Y.presheaf.obj P) := by
  have hf : f = 𝟙 P := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [hf, CategoryTheory.Functor.map_id]

private theorem presheaf_map_comp_comp_eq_id_consolidated310 {P Q R : (Y.Opens)ᵒᵖ}
    (f : P ⟶ Q) (g : Q ⟶ R) (h : R ⟶ P) :
    (Y.presheaf.map f ≫ Y.presheaf.map g) ≫ Y.presheaf.map h = 𝟙 (Y.presheaf.obj P) := by
  rw [← Y.presheaf.map_comp, ← Y.presheaf.map_comp]
  exact presheaf_map_eq_id_consolidated310 _

theorem ideal_eq_of_restrictIdeal_eq (A B : Y.IdealSheafData)
    (V : Y.affineOpens) (h : restrictIdeal A (V : Y.Opens) = restrictIdeal B (V : Y.Opens)) :
    A.ideal V = B.ideal V := by
  have : IsAffine (Scheme.Opens.toScheme (V : Y.Opens)) := V.2
  have e : (⊤ : (Scheme.Opens.toScheme (V : Y.Opens)).Opens) ≤
      Scheme.Opens.ι (V : Y.Opens) ⁻¹ᵁ (V : Y.Opens) := by
    intro x _
    exact x.2
  have h' : A.comap (Scheme.Opens.ι (V : Y.Opens)) = B.comap (Scheme.Opens.ι (V : Y.Opens)) := by
    simpa only [restrictIdeal_eq_comap_ι] using h
  have hA := AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE A
    (Scheme.Opens.ι (V : Y.Opens)) V ⟨⊤, isAffineOpen_top _⟩ e
  have hB := AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE B
    (Scheme.Opens.ι (V : Y.Opens)) V ⟨⊤, isAffineOpen_top _⟩ e
  rw [h'] at hA
  refine (ideal_eq_of_map_eq_of_comp_eq_id_consolidated310
    (Scheme.Hom.appLE (Scheme.Opens.ι (V : Y.Opens)) (V : Y.Opens) ⊤ e)
    (Scheme.Opens.topIso (V : Y.Opens)).hom ?_ (hB.symm.trans hA)).symm
  simp [AlgebraicGeometry.Scheme.Hom.appLE]
  exact presheaf_map_comp_comp_eq_id_consolidated310 _ _ _


end

private def colonSpanSingleton_consolidated310 {R : Type*} [CommRing R] (J : Ideal R) (x : R) : Ideal R where
  carrier := {r | r * x ∈ J}
  add_mem' := fun {a b} ha hb => by
    show (a + b) * x ∈ J
    rw [add_mul]
    exact J.add_mem ha hb
  zero_mem' := by
    show (0 : R) * x ∈ J
    rw [zero_mul]
    exact J.zero_mem
  smul_mem' := fun c a ha => by
    show (c • a) * x ∈ J
    rw [smul_eq_mul, mul_assoc]
    exact J.mul_mem_left c ha

private theorem mem_colonSpanSingleton_consolidated310 {R : Type*} [CommRing R] (J : Ideal R) (x r : R) :
    r ∈ colonSpanSingleton_consolidated310 J x ↔ r * x ∈ J := Iff.rfl

private theorem exists_pow_mul_mem_of_algebraMap_mem_map_of_isLocalizationAway_consolidated310 {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (f : R) [IsLocalization.Away f S] (J : Ideal R) (x : R)
    (hx : algebraMap R S x ∈ Ideal.map (algebraMap R S) J) : ∃ n : ℕ, f ^ n * x ∈ J := by
  rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) S] at hx
  obtain ⟨⟨a, m⟩, hxa⟩ := hx
  rw [← map_mul] at hxa
  obtain ⟨c, hcx⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers f) S).mp hxa
  obtain ⟨q, hq⟩ := m.2
  obtain ⟨p, hp⟩ := c.2
  refine ⟨p + q, ?_⟩
  have key : f ^ (p + q) * x = (c : R) * (x * (m : R)) := by
    rw [← hp, ← hq]; ring
  rw [key, hcx]
  exact J.mul_mem_left _ a.2

section
variable {Y : Scheme.{u}} {ι : Type*} (A B : Y.IdealSheafData) (U : ι → Y.Opens) (hU : (⨆ i, U i) = ⊤) (h : ∀ i, restrictIdeal A (U i) = restrictIdeal B (U i))
include hU h

private theorem ideal_le_of_restrictIdeal_eq_of_iSup_eq_top_consolidated310 (V : Y.affineOpens) : A.ideal V ≤ B.ideal V := by
  intro x hx
  have hV : IsAffineOpen (V : Y.Opens) := V.2
  obtain ⟨T, hT⟩ :
      ∃ T : Ideal ↑(Y.presheaf.obj (Opposite.op (V : Y.Opens))),
        ∀ r, r ∈ T ↔ r * x ∈ B.ideal V :=
    ⟨colonSpanSingleton_consolidated310 (B.ideal V) x, mem_colonSpanSingleton_consolidated310 (B.ideal V) x⟩
  have hcover : (V : Y.Opens) ≤
      ⨆ g : (T : Set ↑(Y.presheaf.obj (Opposite.op (V : Y.Opens)))),
        Y.basicOpen (g : ↑(Y.presheaf.obj (Opposite.op (V : Y.Opens)))) := by
    intro y hy
    have hy' : y ∈ (⨆ i, U i) := by rw [hU]; trivial
    obtain ⟨i, hyi⟩ := Opens.mem_iSup.mp hy'
    obtain ⟨f, hfle, hyf⟩ := hV.exists_basicOpen_le (⟨y, hyi⟩ : ↥(U i)) hy
    have hAB : A.ideal (Y.affineBasicOpen f) = B.ideal (Y.affineBasicOpen f) :=
      ideal_eq_of_restrictIdeal_eq A B (Y.affineBasicOpen f)
        (restrictIdeal_eq_of_le_of_eq hfle (h i))
    have := hV.isLocalization_basicOpen f
    have halg : algebraMap ↑(Y.presheaf.obj (Opposite.op (V : Y.Opens)))
          ↑(Y.presheaf.obj (Opposite.op (Y.basicOpen f))) =
        (Y.presheaf.map (CategoryTheory.homOfLE (Y.basicOpen_le f)).op).hom := rfl
    have hmem : algebraMap ↑(Y.presheaf.obj (Opposite.op (V : Y.Opens)))
          ↑(Y.presheaf.obj (Opposite.op (Y.basicOpen f))) x ∈
        Ideal.map (algebraMap ↑(Y.presheaf.obj (Opposite.op (V : Y.Opens)))
          ↑(Y.presheaf.obj (Opposite.op (Y.basicOpen f)))) (B.ideal V) := by
      rw [halg, B.map_ideal_basicOpen V f, ← hAB, ← A.map_ideal_basicOpen V f]
      exact Ideal.mem_map_of_mem _ hx
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_of_algebraMap_mem_map_of_isLocalizationAway_consolidated310 f (B.ideal V) x hmem
    have hgT : f ^ (n + 1) ∈ T := by
      have hmul : f ^ (n + 1) * x ∈ B.ideal V := by
        have hfx : f ^ (n + 1) * x = f * (f ^ n * x) := by ring
        rw [hfx]
        exact Ideal.mul_mem_left _ _ hn
      exact (hT _).mpr hmul
    have hyg : y ∈ Y.basicOpen (f ^ (n + 1)) := by
      rw [AlgebraicGeometry.Scheme.basicOpen_pow]
      · exact hyf
      · exact Nat.succ_pos n
    exact Opens.mem_iSup.mpr ⟨⟨f ^ (n + 1), hgT⟩, hyg⟩
  have hspan : Ideal.span (T : Set ↑(Y.presheaf.obj (Opposite.op (V : Y.Opens)))) = ⊤ :=
    hV.self_le_iSup_basicOpen_iff.mp hcover
  have hTtop : T = ⊤ := by
    rw [← Ideal.span_eq T, hspan]
  have h1 : (1 : ↑(Y.presheaf.obj (Opposite.op (V : Y.Opens)))) ∈ T := by
    rw [hTtop]; exact Submodule.mem_top
  have h2 := (hT 1).mp h1
  rwa [one_mul] at h2

theorem eq_of_restrictIdeal_eq_of_iSup_eq_top : A = B :=
  AlgebraicGeometry.Scheme.IdealSheafData.ext
    (funext fun V =>
      le_antisymm (ideal_le_of_restrictIdeal_eq_of_iSup_eq_top_consolidated310 A B U hU h V)
        (ideal_le_of_restrictIdeal_eq_of_iSup_eq_top_consolidated310 B A U hU (fun i => (h i).symm) V))


end

theorem eq_of_locally_restrictIdeal_eq {Y : Scheme.{u}} (A B : Y.IdealSheafData)
    (h : ∀ x : Y, ∃ U : Y.Opens, x ∈ U ∧ restrictIdeal A U = restrictIdeal B U) : A = B := by
  choose U hxU hAB using h
  refine eq_of_restrictIdeal_eq_of_iSup_eq_top A B U ?_ hAB
  ext x
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  exact Opens.mem_iSup.mpr ⟨x, hxU x⟩

section
variable {Y : Scheme.{u}} (I : Y.IdealSheafData) (U : Y.affineOpens)

private theorem appLE_subschemeι_apply_eq_zero_of_mem_consolidated310 (V : I.subscheme.Opens)
    (e : V ≤ (Opens.map I.subschemeι.base).obj (U : Y.Opens))
    {t : ↑(Y.presheaf.obj (Opposite.op (U : Y.Opens)))} (ht : t ∈ I.ideal U) :
    (CommRingCat.Hom.hom (I.subschemeι.appLE (U : Y.Opens) V e)) t = 0 := by
  have happ : (CommRingCat.Hom.hom (I.subschemeι.app (U : Y.Opens))) t = 0 := by
    rw [Scheme.IdealSheafData.subschemeι_app, CommRingCat.hom_comp, RingHom.comp_apply,
      CommRingCat.hom_ofHom, Ideal.Quotient.eq_zero_iff_mem.mpr ht, map_zero]
  have hcomp : I.subschemeι.appLE (U : Y.Opens) V e =
      I.subschemeι.app (U : Y.Opens) ≫ I.subscheme.presheaf.map (homOfLE e).op := rfl
  rw [hcomp, CommRingCat.hom_comp, RingHom.comp_apply, happ, map_zero]

private theorem ideal_eq_top_of_one_eq_zero_consolidated310 (h1 : (1 : ↑(I.subscheme.presheaf.obj
      (Opposite.op ((Opens.map I.subschemeι.base).obj (U : Y.Opens))))) = 0) :
    I.ideal U = ⊤ := by
  have happ : (CommRingCat.Hom.hom (I.subschemeι.app (U : Y.Opens))) 1 = 0 := by
    rw [map_one]
    exact h1
  rw [Scheme.IdealSheafData.subschemeι_app, CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.hom_ofHom] at happ
  have h2 := congrArg (CommRingCat.Hom.hom (I.subschemeObjIso U).hom) happ
  have h4 : (CommRingCat.Hom.hom (I.subschemeObjIso U).hom) 0 = 0 := map_zero _
  have h5 := CommRingCat.hom_inv_apply (I.subschemeObjIso U)
      ((Ideal.Quotient.mk (I.ideal U)) (1 : ↑(Y.presheaf.obj (Opposite.op (U : Y.Opens)))))
  have h3 : (Ideal.Quotient.mk (I.ideal U))
      (1 : ↑(Y.presheaf.obj (Opposite.op (U : Y.Opens)))) = 0 :=
    h5.symm.trans (h2.trans h4)
  exact (Ideal.eq_top_iff_one _).mpr (Ideal.Quotient.eq_zero_iff_mem.mp h3)


end

theorem mem_of_restrictIdeal_eq_coordIdeal_of_le {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (hU : IsAffineOpen U)
    (c : EtaleChart p U m) (Z H : X.IdealSheafData) (S : Finset (Fin m)) (a : Fin m)
    (hHZ : H ≤ Z) (hH : restrictIdeal H U = c.coordIdeal {a})
    (hZ : restrictIdeal Z U = c.coordIdeal S)
    (x : X) (hxU : x ∈ U) (hxZ : x ∈ Z.support) : a ∈ S := by
  by_contra ha
  obtain ⟨i, hi⟩ := exists_complOrderEmb_eq m S ha
  have hHid := c.ideal_eq_span_coord hU H {a} hH
  have hmemH : c.coord a ∈ H.ideal ⟨U, hU⟩ := by
    rw [hHid]
    refine Ideal.subset_span ⟨a, ?_, rfl⟩
    simp
  have hmem : c.coord a ∈ Z.ideal ⟨U, hU⟩ := hHZ ⟨U, hU⟩ hmemH
  have hV : IsAffineOpen ((Opens.map Z.subschemeι.base).obj U) :=
    isAffineOpen_preimage_subschemeι Z hU
  have hcoord : (c.restrictToSubscheme hU Z S hZ).coord i = 0 := by
    rw [EtaleChart.restrictToSubscheme_coord, hi]
    exact appLE_subschemeι_apply_eq_zero_of_mem_consolidated310 Z ⟨U, hU⟩ _ _ hmem
  have hnz := coord_mem_nonZeroDivisors hV (c.restrictToSubscheme hU Z S hZ) i
  have h1 := (mem_nonZeroDivisors_iff.mp hnz).1 1 (by rw [hcoord, zero_mul])
  have htop : Z.ideal ⟨U, hU⟩ = ⊤ := ideal_eq_top_of_one_eq_zero_consolidated310 Z ⟨U, hU⟩ h1
  exact notMem_support_of_restrictIdeal_eq_top Z U x hxU
    ((Scheme.IdealSheafData.comap_ι_eq_top_iff_ideal_eq_top Z hU).mpr htop) hxZ

private theorem exists_strictTransform_lift_of_ker_eq_consolidated310 {X X₁ S : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData)
    (j : S ⟶ X) [IsClosedImmersion j] (H : X.IdealSheafData)
    (hker : j.ker = H) :
    ∃ q : (Blowup.strictTransform π Z H).subscheme ⟶ S,
      q ≫ j = (Blowup.strictTransform π Z H).subschemeι ≫ π := by
  subst hker
  exact exists_comp_eq_strictTransform_subschemeι_comp j π Z

theorem exists_strictTransformSubschemeLift {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z H : X.IdealSheafData) :
    ∃ q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme,
      q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π :=
  exists_strictTransform_lift_of_ker_eq_consolidated310 π Z H.subschemeι H
    (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι H)

def strictTransformSubschemeLift {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z H : X.IdealSheafData) :
    (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme :=
  (exists_strictTransformSubschemeLift π Z H).choose

theorem strictTransformSubschemeLift_comp_subschemeι {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z H : X.IdealSheafData) :
    strictTransformSubschemeLift π Z H ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π :=
  (exists_strictTransformSubschemeLift π Z H).choose_spec

private theorem isBlowupAlongIdealSheaf_comap_of_ker_eq_consolidated310 {X X₁ S : Scheme.{u}} [IsLocallyNoetherian X₁]
    (π : X₁ ⟶ X) (Z : X.IdealSheafData) (j : S ⟶ X)
    [IsClosedImmersion j] (H : X.IdealSheafData) (hker : j.ker = H)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (q : (Blowup.strictTransform π Z H).subscheme ⟶ S)
    (hq : q ≫ j = (Blowup.strictTransform π Z H).subschemeι ≫ π) :
    Blowup.IsBlowupAlongIdealSheaf q (Z.comap j) := by
  subst hker
  have h2 : q ≫ j = strictTransformLiftOfClosedImmersion j π Z ≫ j := by
    rw [hq, strictTransformLiftOfClosedImmersion_comp]
  have hqq : q = strictTransformLiftOfClosedImmersion j π Z := (cancel_mono j).mp h2
  rw [hqq]
  exact isBlowupAlongIdealSheaf_strictTransformLiftOfClosedImmersion j π Z hπ

theorem isBlowupAlongIdealSheaf_strictTransformSubschemeLift {X X₁ : Scheme.{u}} [IsLocallyNoetherian X₁]
    (π : X₁ ⟶ X) (Z H : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    Blowup.IsBlowupAlongIdealSheaf (strictTransformSubschemeLift π Z H) (Z.comap H.subschemeι) :=
  isBlowupAlongIdealSheaf_comap_of_ker_eq_consolidated310 π Z H.subschemeι H
    (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι H) hπ
    (strictTransformSubschemeLift π Z H) (strictTransformSubschemeLift_comp_subschemeι π Z H)

private theorem subschemeι_base_mem_support_consolidated310 {X : Scheme.{u}} (I : X.IdealSheafData)
    (x : I.subscheme) : I.subschemeι.base x ∈ (I.support : Set X) := by
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι]
  exact Set.mem_range_self x

section
variable {X : Scheme.{u}} {k : Type u} [Field k]

private theorem coordIdeal_eq_of_map_eq_consolidated310 {p₁ p₂ : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ}
    (c₁ : EtaleChart p₁ U m) (c₂ : EtaleChart p₂ U m) (h : c₁.map = c₂.map) (T : Finset (Fin m)) :
    c₁.coordIdeal T = c₂.coordIdeal T := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  exact congrArg (fun f => (coordSubspaceIdeal k m T).comap f) h

private theorem exists_etaleChart_of_hasStrictNormalCrossingsWith_consolidated310 (p : X ⟶ Spec (CommRingCat.of k)) (Z H : X.IdealSheafData) (E : List X.IdealSheafData)
    (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (D : X.IdealSheafData) (hD : D ∈ E) (y : X)
    (hy : y ∈ Z.support) :
    ∃ (U : X.Opens) (_ : y ∈ U) (_ : IsAffineOpen U) (m : ℕ) (c : EtaleChart p U m)
      (S : Finset (Fin m)) (_ : restrictIdeal Z U = c.coordIdeal S),
      restrictIdeal H U = ⊤ ∨ ∃ a : Fin m, restrictIdeal H U = c.coordIdeal {a} ∧
        (restrictIdeal D U = ⊤ ∨ ∃ b : Fin m, b ≠ a ∧ restrictIdeal D U = c.coordIdeal {b}) := by
  obtain ⟨U, hyU, m, c, av, S, hinj, hnone, hsome, hZ⟩ := hsnc y hy
  obtain ⟨i, hi, hEi⟩ : ∃ (i : ℕ) (h : i < E.length), E[i] = D := List.mem_iff_getElem.mp hD
  have hlt0 : 0 < (H :: E).length := by rw [List.length_cons]; omega
  have hlti : i + 1 < (H :: E).length := by rw [List.length_cons]; omega
  have hH0 : ∀ t : Fin m, av 0 = some t → restrictIdeal H U = c.coordIdeal {t} := by
    intro t ht
    have h := hsome 0 hlt0 t ht
    rw [List.getElem_cons_zero] at h
    exact h
  have hHn : av 0 = none → restrictIdeal H U = ⊤ := by
    intro ht
    have h := hnone 0 hlt0 ht
    rw [List.getElem_cons_zero] at h
    exact h
  have hD0 : ∀ t : Fin m, av (i + 1) = some t → restrictIdeal D U = c.coordIdeal {t} := by
    intro t ht
    have h := hsome (i + 1) hlti t ht
    simp only [List.getElem_cons_succ] at h
    rw [hEi] at h
    exact h
  have hDn : av (i + 1) = none → restrictIdeal D U = ⊤ := by
    intro ht
    have h := hnone (i + 1) hlti ht
    simp only [List.getElem_cons_succ] at h
    rw [hEi] at h
    exact h
  obtain ⟨V, hVaff, hyV, hVle⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hyU
  refine ⟨V, hyV, hVaff, m, c.restrict hVle, S,
    restrictIdeal_eq_restrict_coordIdeal_of_le hVle c Z S hZ, ?_⟩
  cases h0 : av 0 with
  | none => exact Or.inl (restrictIdeal_eq_top_of_le H hVle (hHn h0))
  | some t =>
      refine Or.inr ⟨t, restrictIdeal_eq_restrict_coordIdeal_of_le hVle c H {t} (hH0 t h0), ?_⟩
      cases h1 : av (i + 1) with
      | none => exact Or.inl (restrictIdeal_eq_top_of_le D hVle (hDn h1))
      | some t' =>
          refine Or.inr ⟨t', ?_, restrictIdeal_eq_restrict_coordIdeal_of_le hVle c D {t'} (hD0 t' h1)⟩
          intro htt
          subst htt
          have hz := hinj 0 hlt0 (i + 1) hlti t' h0 h1
          omega


end

section
variable {X X₁ : Scheme.{u}}

private theorem false_of_mem_preimage_of_restrictIdeal_eq_top_consolidated310 {k : Type u}
    [Field k] {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X)
    (Z H : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) {S : Finset (Fin m)}
    (hZ : restrictIdeal Z U = c.coordIdeal S) (hHtop : restrictIdeal H U = ⊤)
    (x : (Blowup.strictTransform π Z H).subscheme)
    (hxU : (Blowup.strictTransform π Z H).subschemeι.base x ∈ π ⁻¹ᵁ U) : False := by
  obtain ⟨s, hs, hmem⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZ
    ((Blowup.strictTransform π Z H).subschemeι.base x) hxU
  have htop : restrictIdeal (Blowup.strictTransform π Z H)
      (blowupChartOfIsBlowup π c S hπ hZ s hs).domain = ⊤ :=
    (blowupChartOfIsBlowup π c S hπ hZ s hs).restrictIdeal_strictTransform_of_eq_top Z H hHtop
  exact notMem_support_of_restrictIdeal_eq_top (Blowup.strictTransform π Z H)
    (blowupChartOfIsBlowup π c S hπ hZ s hs).domain
    ((Blowup.strictTransform π Z H).subschemeι.base x) hmem htop
    (subschemeι_base_mem_support_consolidated310 (Blowup.strictTransform π Z H) x)

private theorem exists_restrictIdeal_eq_of_notMem_support_consolidated310 (π : X₁ ⟶ X)
    [IsLocallyNoetherian X₁] (Z H : X.IdealSheafData)
    (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π)
    (D : X.IdealSheafData) (x : (Blowup.strictTransform π Z H).subscheme)
    (hx : π.base ((Blowup.strictTransform π Z H).subschemeι.base x) ∉ Z.support) :
    ∃ W : (Blowup.strictTransform π Z H).subscheme.Opens, x ∈ W ∧
      restrictIdeal ((Blowup.strictTransform π Z D).comap (Blowup.strictTransform π Z H).subschemeι) W =
        restrictIdeal (Blowup.strictTransform q (Z.comap H.subschemeι) (D.comap H.subschemeι)) W := by
  have : IsLocallyNoetherian (Blowup.strictTransform π Z H).subscheme :=
    isLocallyNoetherian_subscheme _
  have := quasiCompact_strictTransformι_of_isLocallyNoetherian π Z D
  have := quasiCompact_strictTransformι_of_isLocallyNoetherian q
    (Z.comap H.subschemeι) (D.comap H.subschemeι)
  have hZcomap : (Z.comap H.subschemeι).comap q
      = (Z.comap π).comap (Blowup.strictTransform π Z H).subschemeι := by
    rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hq]
  have hVmem : ∀ z : X₁, z ∈ (π ⁻¹ᵁ Z.support.compl) → π.base z ∉ Z.support := fun z hz => hz
  have hWmem : ∀ z : (Blowup.strictTransform π Z H).subscheme,
      z ∈ ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl)) →
        q.base z ∉ (Z.comap H.subschemeι).support := by
    intro z hz hmem
    have h1 : z ∈ ((Z.comap H.subschemeι).comap q).support := by
      rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
      exact hmem
    rw [hZcomap, AlgebraicGeometry.Scheme.IdealSheafData.support_comap] at h1
    have h2 : (Blowup.strictTransform π Z H).subschemeι.base z ∈ (Z.comap π).support := h1
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] at h2
    have h3 : π.base ((Blowup.strictTransform π Z H).subschemeι.base z) ∈ Z.support := h2
    have hz' : π.base ((Blowup.strictTransform π Z H).subschemeι.base z) ∉ Z.support := hz
    exact hz' h3
  refine ⟨(Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl), hx, ?_⟩
  rw [restrictIdeal_comap_eq_comap_resLE_restrictIdeal (Blowup.strictTransform π Z H).subschemeι
      (Blowup.strictTransform π Z D) (π ⁻¹ᵁ Z.support.compl)
      ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl)) le_rfl,
    restrictIdeal_strictTransform_eq_comap_of_notMem_support π Z D _ hVmem,
    ← restrictIdeal_comap_eq_comap_resLE_restrictIdeal (Blowup.strictTransform π Z H).subschemeι
      (D.comap π) (π ⁻¹ᵁ Z.support.compl)
      ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl)) le_rfl,
    restrictIdeal_strictTransform_eq_comap_of_notMem_support q (Z.comap H.subschemeι)
      (D.comap H.subschemeι) _ hWmem,
    ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hq]


end

section
variable {X X₁ : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}

private theorem restrictIdeal_comap_strictTransform_eq_of_blowupChart_consolidated310 {π : X₁ ⟶ X} [IsLocallyNoetherian X₁]
    {U : X.Opens} {m : ℕ} {c : EtaleChart p U m} {S : Finset (Fin m)} {s : Fin m}
    (B : BlowupChart π c S s) (hU : IsAffineOpen U) (hB : IsAffineOpen B.domain)
    (Z H : X.IdealSheafData) (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (a : Fin m) (ha : a ∈ S) (has : a ≠ s) (hH : restrictIdeal H U = c.coordIdeal {a})
    (D : X.IdealSheafData)
    (hDd : restrictIdeal D U = ⊤ ∨ ∃ b : Fin m, b ≠ a ∧ restrictIdeal D U = c.coordIdeal {b})
    (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π) :
    restrictIdeal ((Blowup.strictTransform π Z D).comap (Blowup.strictTransform π Z H).subschemeι)
        ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) =
      restrictIdeal (Blowup.strictTransform q (Z.comap H.subschemeι) (D.comap H.subschemeι))
        ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) := by
  have : IsLocallyNoetherian (Blowup.strictTransform π Z H).subscheme :=
    isLocallyNoetherian_subscheme _
  have := quasiCompact_strictTransformι_of_isLocallyNoetherian π Z D
  have := quasiCompact_strictTransformι_of_isLocallyNoetherian π Z H
  have := quasiCompact_strictTransformι_of_isLocallyNoetherian q
    (Z.comap H.subschemeι) (D.comap H.subschemeι)
  have hsa : s ∉ ({a} : Finset (Fin m)) := by
    simp only [Finset.mem_singleton]
    exact fun h => has h.symm
  obtain ⟨s', hs'⟩ := exists_complOrderEmb_eq m ({a} : Finset (Fin m)) hsa
  have hs'S : s' ∈ complEmbPreimage m S a := mem_complEmbPreimage_of_complOrderEmb_eq m S a hs hs'
  have hZ' : restrictIdeal (Z.comap H.subschemeι) (H.subschemeι ⁻¹ᵁ U)
      = (c.restrictToSubscheme hU H {a} hH).coordIdeal (complEmbPreimage m S a) :=
    restrictIdeal_comap_subschemeι_eq_coordIdeal c hU Z H S a hZ hH
  have hFa : restrictIdeal (Blowup.strictTransform π Z H) B.domain = B.chart.coordIdeal {a} :=
    B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH
  have hBmap : (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s' hs' q hq).chart.map
      = (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a} hFa).map :=
    B.restrictToStrictTransform_chart_map hU hB Z H hs hZ a ha has hH s' hs' q hq
  rcases hDd with hDtop | ⟨b, hba, hDb⟩
  · have hL : restrictIdeal ((Blowup.strictTransform π Z D).comap (Blowup.strictTransform π Z H).subschemeι)
        ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) = ⊤ :=
      restrictIdeal_comap_subschemeι_eq_top (Blowup.strictTransform π Z H) B.domain
        (Blowup.strictTransform π Z D) (B.restrictIdeal_strictTransform_of_eq_top Z D hDtop)
    have hR : restrictIdeal (Blowup.strictTransform q (Z.comap H.subschemeι) (D.comap H.subschemeι))
        ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) = ⊤ := by
      have h := (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s'
          hs' q hq).restrictIdeal_strictTransform_of_eq_top (Z.comap H.subschemeι)
          (D.comap H.subschemeι) (restrictIdeal_comap_subschemeι_eq_top H U D hDtop)
      exact h
    rw [hL, hR]
  · have hb : b ∉ ({a} : Finset (Fin m)) := by
      simp only [Finset.mem_singleton]
      exact hba
    obtain ⟨b', hb'⟩ := exists_complOrderEmb_eq m ({a} : Finset (Fin m)) hb
    have hDb' : restrictIdeal D U = c.coordIdeal {complOrderEmb m {a} b'} := by
      rw [hb']
      exact hDb
    have hRD : restrictIdeal (D.comap H.subschemeι) (H.subschemeι ⁻¹ᵁ U)
        = (c.restrictToSubscheme hU H {a} hH).coordIdeal {b'} :=
      EtaleChart.restrictToSubscheme_coordIdeal_singleton c hU H {a} hH b' D hDb'
    have hiff : (b = s) ↔ (b' = s') := by
      constructor
      · intro h
        apply (complOrderEmb m ({a} : Finset (Fin m))).injective
        rw [hb', hs', h]
      · intro h
        rw [← hb', ← hs', h]
    by_cases hbs : b = s
    · have hL : restrictIdeal ((Blowup.strictTransform π Z D).comap (Blowup.strictTransform π Z H).subschemeι)
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) = ⊤ := by
        refine restrictIdeal_comap_subschemeι_eq_top (Blowup.strictTransform π Z H) B.domain
          (Blowup.strictTransform π Z D) ?_
        rw [B.restrictIdeal_strictTransform_coordIdeal Z D hs hZ b hDb, if_pos hbs]
      have hR : restrictIdeal (Blowup.strictTransform q (Z.comap H.subschemeι) (D.comap H.subschemeι))
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) = ⊤ := by
        have h := (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s'
            hs' q hq).restrictIdeal_strictTransform_coordIdeal (Z.comap H.subschemeι)
            (D.comap H.subschemeι) hs'S hZ' b' hRD
        rw [if_pos (hiff.mp hbs)] at h
        exact h
      rw [hL, hR]
    · have hL : restrictIdeal ((Blowup.strictTransform π Z D).comap (Blowup.strictTransform π Z H).subschemeι)
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain)
          = (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a} hFa).coordIdeal {b'} := by
        refine EtaleChart.restrictToSubscheme_coordIdeal_singleton B.chart hB
          (Blowup.strictTransform π Z H) {a} hFa b' (Blowup.strictTransform π Z D) ?_
        rw [B.restrictIdeal_strictTransform_coordIdeal Z D hs hZ b hDb, if_neg hbs, hb']
      have hR : restrictIdeal (Blowup.strictTransform q (Z.comap H.subschemeι) (D.comap H.subschemeι))
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain)
          = (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s'
              hs' q hq).chart.coordIdeal {b'} := by
        have h := (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s'
            hs' q hq).restrictIdeal_strictTransform_coordIdeal (Z.comap H.subschemeι)
            (D.comap H.subschemeι) hs'S hZ' b' hRD
        rw [if_neg (fun hxx => hbs (hiff.mpr hxx))] at h
        exact h
      rw [hL, hR]
      exact coordIdeal_eq_of_map_eq_consolidated310
        (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a} hFa)
        (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s' hs' q hq).chart
        hBmap.symm {b'}

private theorem exists_restrictIdeal_eq_of_mem_preimage_consolidated310 (π : X₁ ⟶ X) [IsLocallyNoetherian X₁]
    (Z H : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π)
    (D : X.IdealSheafData) {U : X.Opens} (hU : IsAffineOpen U) {m : ℕ} (c : EtaleChart p U m)
    {S : Finset (Fin m)} (hZ : restrictIdeal Z U = c.coordIdeal S) {a : Fin m} (ha : a ∈ S)
    (hH : restrictIdeal H U = c.coordIdeal {a})
    (hDd : restrictIdeal D U = ⊤ ∨ ∃ b : Fin m, b ≠ a ∧ restrictIdeal D U = c.coordIdeal {b})
    (x : (Blowup.strictTransform π Z H).subscheme)
    (hxU : (Blowup.strictTransform π Z H).subschemeι.base x ∈ π ⁻¹ᵁ U) :
    ∃ W : (Blowup.strictTransform π Z H).subscheme.Opens, x ∈ W ∧
      restrictIdeal ((Blowup.strictTransform π Z D).comap (Blowup.strictTransform π Z H).subschemeι) W =
        restrictIdeal (Blowup.strictTransform q (Z.comap H.subschemeι) (D.comap H.subschemeι)) W := by
  have : IsLocallyNoetherian (Blowup.strictTransform π Z H).subscheme :=
    isLocallyNoetherian_subscheme _
  have := quasiCompact_strictTransformι_of_isLocallyNoetherian π Z H
  obtain ⟨s, hs, hmem⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZ
    ((Blowup.strictTransform π Z H).subschemeι.base x) hxU
  have has : a ≠ s := by
    intro hasEq
    have hH' : restrictIdeal H U = c.coordIdeal {s} := by rw [hH, hasEq]
    have hbot := (blowupChartOfIsBlowup π c S hπ hZ s hs).strictTransform_subschemeι_preimage_domain_eq_bot
      Z H hs hZ hH'
    have hx0 : x ∈ (Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ
        (blowupChartOfIsBlowup π c S hπ hZ s hs).domain := hmem
    rw [hbot] at hx0
    exact hx0
  obtain ⟨V, hVle, hVaff, hxV⟩ :=
    (blowupChartOfIsBlowup π c S hπ hZ s hs).exists_isAffineOpen_mem_le_domain
      ((Blowup.strictTransform π Z H).subschemeι.base x) hmem
  refine ⟨(Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ V, hxV, ?_⟩
  exact restrictIdeal_comap_strictTransform_eq_of_blowupChart_consolidated310 ((blowupChartOfIsBlowup π c S hπ hZ s hs).restrict V hVle)
    hU hVaff Z H hs hZ a ha has hH D hDd q hq


end

section
variable {X X₁ : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k)) (π : X₁ ⟶ X) [IsLocallyNoetherian X₁] (Z H : X.IdealSheafData) (E : List X.IdealSheafData) (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (hHZ : H ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
include hsnc hHZ hπ

theorem comap_strictTransform_eq_strictTransform_of_comp_eq (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π)
    (D : X.IdealSheafData) (hD : D ∈ E) :
    (Blowup.strictTransform π Z D).comap (Blowup.strictTransform π Z H).subschemeι =
      Blowup.strictTransform q (Z.comap H.subschemeι) (D.comap H.subschemeι) := by
  refine eq_of_locally_restrictIdeal_eq _ _ (fun x => ?_)
  by_cases hx : π.base ((Blowup.strictTransform π Z H).subschemeι.base x) ∈ Z.support
  · obtain ⟨U, hyU, hU, m, c, S, hZc, hcase⟩ :=
      exists_etaleChart_of_hasStrictNormalCrossingsWith_consolidated310 p Z H E hsnc D hD
        (π.base ((Blowup.strictTransform π Z H).subschemeι.base x)) hx
    rcases hcase with hHtop | ⟨a, hH, hDd⟩
    · exact (false_of_mem_preimage_of_restrictIdeal_eq_top_consolidated310 π Z H hπ c hZc hHtop x hyU).elim
    · exact exists_restrictIdeal_eq_of_mem_preimage_consolidated310 π Z H hπ q hq D hU c hZc
        (mem_of_restrictIdeal_eq_coordIdeal_of_le hU c Z H S a hHZ hH hZc
          (π.base ((Blowup.strictTransform π Z H).subschemeι.base x)) hyU hx) hH hDd x hyU
  · exact exists_restrictIdeal_eq_of_notMem_support_consolidated310 π Z H q hq D x hx

theorem comap_strictTransform_eq_strictTransformSubschemeLift (D : X.IdealSheafData) (hD : D ∈ E) :
    (Blowup.strictTransform π Z D).comap (Blowup.strictTransform π Z H).subschemeι =
      Blowup.strictTransform (strictTransformSubschemeLift π Z H) (Z.comap H.subschemeι) (D.comap H.subschemeι) :=
  comap_strictTransform_eq_strictTransform_of_comp_eq p π Z H E hsnc hHZ hπ
    (strictTransformSubschemeLift π Z H) (strictTransformSubschemeLift_comp_subschemeι π Z H) D hD


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsHypersurfaceRestriction
section

open Opposite TopologicalSpace

section

private theorem appLE_preimage_naturality_consolidated327 {Y Q : Scheme.{u}} (f : Y ⟶ Q) {A B : Q.Opens}
    (h : B ≤ A) (h' : f ⁻¹ᵁ B ≤ f ⁻¹ᵁ A) (z : Γ(Q, A)) :
    (f.appLE B (f ⁻¹ᵁ B) le_rfl).hom ((Q.presheaf.map (homOfLE h).op).hom z)
      = (Y.presheaf.map (homOfLE h').op).hom ((f.appLE A (f ⁻¹ᵁ A) le_rfl).hom z) := by
  have key : Q.presheaf.map (homOfLE h).op ≫ f.appLE B (f ⁻¹ᵁ B) le_rfl
      = f.appLE A (f ⁻¹ᵁ A) le_rfl ≫ Y.presheaf.map (homOfLE h').op := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  have h2 := congrArg (fun φ : Γ(Q, A) ⟶ Γ(Y, f ⁻¹ᵁ B) => CommRingCat.Hom.hom φ z) key
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  exact h2

section

variable {k : Type*} [CommRing k] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_derivation_mul_sub_mem_of_eq_one_or_mem {B : Type*} [CommRing B] [Algebra k B]
    (δ : ι → Derivation k B B) (v x : ι → B) (m : Ideal B)
    (h : ∀ b : ι, v b = 1 ∨ x b ∈ m) :
    (Matrix.of fun a b : ι => δ a (v b * x b)).det
        - (Matrix.of fun a b : ι => δ a (x b)).det * ∏ b : ι, v b ∈ m := by
  have hmat : (Matrix.of fun a b : ι => (Ideal.Quotient.mk m) (δ a (v b * x b)))
      = (Matrix.of fun a b : ι => (Ideal.Quotient.mk m) (δ a (x b)))
        * Matrix.diagonal (fun b : ι => (Ideal.Quotient.mk m) (v b)) := by
    ext a b
    rcases h b with hv | hxb
    · simp [Matrix.mul_diagonal, hv]
    · have hx0 : (Ideal.Quotient.mk m) (x b) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hxb
      simp [Matrix.mul_diagonal, Derivation.leibniz, hx0, mul_comm]
  have h1 : (Ideal.Quotient.mk m) (Matrix.of fun a b : ι => δ a (v b * x b)).det
      = (Matrix.of fun a b : ι => (Ideal.Quotient.mk m) (δ a (v b * x b))).det := by
    rw [RingHom.map_det]
    rfl
  have h2 : (Ideal.Quotient.mk m) (Matrix.of fun a b : ι => δ a (x b)).det
      = (Matrix.of fun a b : ι => (Ideal.Quotient.mk m) (δ a (x b))).det := by
    rw [RingHom.map_det]
    rfl
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_prod, h1, h2, hmat,
    Matrix.det_mul, Matrix.det_diagonal, sub_self]

theorem det_derivation_notMem_comap_of_eq_one_or_mem {R S : Type*} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (q : R →+* S) (δ : ι → Derivation k R R)
    (δ' : ι → Derivation k S S)
    (hcompat : ∀ (a : ι) (r : R), q (δ a r) = δ' a (q r))
    (f : ι → R) (v : ι → Sˣ) (x : ι → S)
    (hf : ∀ b : ι, q (f b) = (v b : S) * x b)
    (m : Ideal S) (hm : m ≠ ⊤)
    (h : ∀ b : ι, v b = 1 ∨ x b ∈ m)
    (hdet : IsUnit (Matrix.of fun a b : ι => δ' a (x b)).det) :
    (Matrix.of fun a b : ι => δ a (f b)).det ∉ Ideal.comap q m := by
  intro hcon
  rw [Ideal.mem_comap] at hcon
  have hmat : q.mapMatrix (Matrix.of fun a b : ι => δ a (f b))
      = Matrix.of fun a b : ι => δ' a ((v b : S) * x b) := by
    ext a b
    show q (δ a (f b)) = δ' a ((v b : S) * x b)
    rw [hcompat, hf]
  have hq : q (Matrix.of fun a b : ι => δ a (f b)).det
      = (Matrix.of fun a b : ι => δ' a ((v b : S) * x b)).det := by
    rw [RingHom.map_det, hmat]
  rw [hq] at hcon
  have hv1 : ∀ b : ι, ((v b : S)) = 1 ∨ x b ∈ m := by
    intro b
    rcases h b with hb | hb
    · exact Or.inl (by rw [hb, Units.val_one])
    · exact Or.inr hb
  have h3 := det_derivation_mul_sub_mem_of_eq_one_or_mem (k := k) δ' (fun b : ι => ((v b : S))) x m hv1
  have h4 : (Matrix.of fun a b : ι => δ' a (x b)).det * ∏ b : ι, ((v b : S)) ∈ m := by
    have h5 := Ideal.sub_mem m hcon h3
    simpa using h5
  have hp : IsUnit (∏ b : ι, ((v b : S))) :=
    Finset.prod_induction (fun b : ι => ((v b : S))) IsUnit (fun r s hr hs => hr.mul hs)
      isUnit_one fun b _ => (v b).isUnit
  exact hm (Ideal.eq_top_of_isUnit_mem m h4 (hdet.mul hp))

end

theorem basisKaehler_det_eq_jacobian_det (k : Type*) [CommRing k] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (S : Type*) [CommRing S] [Algebra (MvPolynomial ι k) S] [Algebra k S]
    [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (w : ι → S) :
    (EtaleCoordinates.basisKaehler k ι S).det
        (fun i : ι => KaehlerDifferential.D k S (w i)) =
      (Matrix.of fun i j : ι => EtaleCoordinates.partialDeriv k ι S i (w j)).det := by
  have hM : (EtaleCoordinates.basisKaehler k ι S).toMatrix
        (fun i : ι => KaehlerDifferential.D k S (w i))
      = Matrix.of fun i j : ι => EtaleCoordinates.partialDeriv k ι S i (w j) := by
    ext i j
    simp only [Matrix.of_apply, Module.Basis.toMatrix_apply]
    rw [EtaleCoordinates.partialDeriv_apply]
  rw [Module.Basis.det_apply, hM]

private theorem primeIdealOf_eq_comap_primeIdealOf_consolidated327 {Y Q : Scheme.{u}} (f : Y ⟶ Q) {U : Q.Opens}
    (hU : IsAffineOpen U) (hW : IsAffineOpen (f ⁻¹ᵁ U)) {y : Y} (hy : y ∈ f ⁻¹ᵁ U) :
    (hU.primeIdealOf ⟨f.base y, hy⟩).asIdeal
      = Ideal.comap (Scheme.Hom.app f U).hom (hW.primeIdealOf ⟨y, hy⟩).asIdeal := by
  have hbo : ∀ s : Γ(Q, U),
      f ⁻¹ᵁ Q.basicOpen s = Y.basicOpen ((Scheme.Hom.app f U).hom s) := by
    intro s
    simp
  ext s
  simp only [Ideal.mem_comap]
  constructor
  · intro hs
    by_contra hcon
    have hyb : y ∈ Y.basicOpen ((Scheme.Hom.app f U).hom s) :=
      mem_basicOpen_of_notMem_primeIdealOf hW hy _ hcon
    rw [← hbo s] at hyb
    exact notMem_basicOpen_of_mem_primeIdealOf hU hy s hs hyb
  · intro hs
    by_contra hcon
    have hxb : f.base y ∈ Q.basicOpen s :=
      mem_basicOpen_of_notMem_primeIdealOf hU hy s hcon
    have hyb : y ∈ f ⁻¹ᵁ Q.basicOpen s := hxb
    rw [hbo s] at hyb
    exact notMem_basicOpen_of_mem_primeIdealOf hW hy _ hs hyb

section
variable {Q : Scheme.{u}} (H : Q.IdealSheafData)

private theorem exists_subschemeι_base_eq_of_mem_support_consolidated327 {x : ↥Q} (hx : x ∈ H.support) : ∃ y : ↥H.subscheme, H.subschemeι.base y = x :=
  (Scheme.IdealSheafData.range_subschemeι H).ge hx

private theorem exists_basicOpen_subschemeι_preimage_le_consolidated327 {U : Q.Opens}
    (hU : IsAffineOpen U) (V : H.subscheme.Opens) {y : ↥H.subscheme}
    (hyU : y ∈ H.subschemeι ⁻¹ᵁ U) (hyV : y ∈ V) :
    ∃ f : Γ(Q, U), y ∈ H.subschemeι ⁻¹ᵁ (Q.basicOpen f) ∧
      H.subschemeι ⁻¹ᵁ (Q.basicOpen f) ≤ V ∧ Q.basicOpen f ≤ U := by
  have hWaff : IsAffineOpen (H.subschemeι ⁻¹ᵁ U) := isAffineOpen_preimage_subschemeι H hU
  obtain ⟨g, hgle, hyg⟩ :=
    hWaff.exists_basicOpen_le (⟨y, ⟨hyV, hyU⟩⟩ : ↥(V ⊓ H.subschemeι ⁻¹ᵁ U)) hyU
  obtain ⟨f, hf⟩ := Scheme.IdealSheafData.subschemeι_app_surjective H ⟨U, hU⟩ g
  have hpre : H.subschemeι ⁻¹ᵁ (Q.basicOpen f) = H.subscheme.basicOpen g := by
    rw [← hf]
    simp
  refine ⟨f, ?_, ?_, Q.basicOpen_le f⟩
  · rw [hpre]
    exact hyg
  · rw [hpre]
    exact le_trans hgle inf_le_left


end

private theorem span_image_eq_of_isUnit_mul_consolidated327 {R : Type*} [CommRing R] {ι : Type*} (s : Set ι)
    (a b : ι → R) (h : ∀ i ∈ s, ∃ u : R, IsUnit u ∧ a i = u * b i) :
    Ideal.span (a '' s) = Ideal.span (b '' s) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z ⟨i, hi, rfl⟩
    obtain ⟨u, -, hu⟩ := h i hi
    rw [hu]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, hi, rfl⟩)
  · rw [Ideal.span_le]
    rintro z ⟨i, hi, rfl⟩
    obtain ⟨u, hunit, hu⟩ := h i hi
    obtain ⟨u', hu'⟩ := hunit.exists_left_inv
    have hb : b i = u' * a i := by
      rw [hu, ← mul_assoc, hu', one_mul]
    rw [hb]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, hi, rfl⟩)

private theorem exists_equiv_subtype_ne_compatible_consolidated327 {n m : ℕ} (hnm : m + 1 = n) (j₀ : Fin n) (len : ℕ)
    (γ : ℕ → Option (Fin n)) (a' : ℕ → Option (Fin m))
    (hinjγ : ∀ i i' : ℕ, i < len → i' < len → ∀ j : Fin n,
      γ i = some j → γ i' = some j → i = i')
    (hinja : ∀ i i' : ℕ, i < len → i' < len → ∀ b : Fin m,
      a' i = some b → a' i' = some b → i = i')
    (hj₀ : ∀ i : ℕ, i < len → γ i ≠ some j₀)
    (hfwd : ∀ i : ℕ, i < len → ∀ j : Fin n, γ i = some j → ∃ b : Fin m, a' i = some b) :
    ∃ ρ : Fin m ≃ {j : Fin n // j ≠ j₀},
      ∀ i : ℕ, i < len → ∀ (j : Fin n) (b : Fin m), γ i = some j → a' i = some b →
        ((ρ b : Fin n) = j) := by
  classical
  have hQ : ∀ jj : {jj : {j : Fin n // j ≠ j₀} //
        ∃ i, i < len ∧ γ i = some ((jj : {j : Fin n // j ≠ j₀}) : Fin n)},
      ∃ b : Fin m, ∀ i, i < len →
        γ i = some (((jj : {j : Fin n // j ≠ j₀}) : Fin n)) → a' i = some b := by
    rintro ⟨jj, i₀, hi₀, hγ₀⟩
    obtain ⟨b, hb⟩ := hfwd i₀ hi₀ _ hγ₀
    refine ⟨b, ?_⟩
    intro i hi hγ
    have : i₀ = i := hinjγ i₀ i hi₀ hi _ hγ₀ hγ
    rw [← this]
    exact hb
  choose g hg using hQ
  have hginj : Function.Injective g := by
    intro j₁ j₂ hgj
    obtain ⟨i₁, hi₁, he₁⟩ := j₁.2
    obtain ⟨i₂, hi₂, he₂⟩ := j₂.2
    have h1 := hg j₁ i₁ hi₁ he₁
    have h2 : a' i₂ = some (g j₁) := by
      rw [hgj]
      exact hg j₂ i₂ hi₂ he₂
    have hii : i₁ = i₂ := hinja i₁ i₂ hi₁ hi₂ (g j₁) h1 h2
    subst hii
    have : (some (((j₁ : {j : Fin n // j ≠ j₀}) : Fin n)))
        = some (((j₂ : {j : Fin n // j ≠ j₀}) : Fin n)) := by rw [← he₁, ← he₂]
    exact Subtype.ext (Subtype.ext (Option.some.inj this))
  have he1 : ∃ e1 : {jj : {j : Fin n // j ≠ j₀} //
        ∃ i, i < len ∧ γ i = some ((jj : {j : Fin n // j ≠ j₀}) : Fin n)}
      ≃ {b : Fin m // ∃ jj, g jj = b}, ∀ jj, ((e1 jj : {b : Fin m // ∃ jj, g jj = b}) : Fin m)
        = g jj := by
    refine ⟨Equiv.ofBijective (fun jj => ⟨g jj, ⟨jj, rfl⟩⟩) ⟨?_, ?_⟩, fun jj => rfl⟩
    · intro a b hab
      exact hginj (congrArg Subtype.val hab)
    · rintro ⟨b, jj, rfl⟩
      exact ⟨jj, rfl⟩
  obtain ⟨e1, he1val⟩ := he1
  have hcardT : Fintype.card {j : Fin n // j ≠ j₀} = m := by
    have h1 : Fintype.card {j : Fin n // ¬ (j = j₀)}
        = Fintype.card (Fin n) - Fintype.card {j : Fin n // j = j₀} :=
      Fintype.card_subtype_compl _
    have h2 : Fintype.card {j : Fin n // j ≠ j₀} = n - 1 := by
      rw [show Fintype.card {j : Fin n // j ≠ j₀}
          = Fintype.card {j : Fin n // ¬ (j = j₀)} from rfl, h1, Fintype.card_subtype_eq,
        Fintype.card_fin]
    omega
  have hA : Fintype.card {jj : {j : Fin n // j ≠ j₀} //
        ¬ ∃ i, i < len ∧ γ i = some ((jj : {j : Fin n // j ≠ j₀}) : Fin n)}
      = Fintype.card {j : Fin n // j ≠ j₀}
        - Fintype.card {jj : {j : Fin n // j ≠ j₀} //
            ∃ i, i < len ∧ γ i = some ((jj : {j : Fin n // j ≠ j₀}) : Fin n)} :=
    Fintype.card_subtype_compl _
  have hB : Fintype.card {b : Fin m // ¬ ∃ jj, g jj = b}
      = Fintype.card (Fin m) - Fintype.card {b : Fin m // ∃ jj, g jj = b} :=
    Fintype.card_subtype_compl _
  have hcard1 := Fintype.card_congr e1
  have hcardm : Fintype.card (Fin m) = m := Fintype.card_fin m
  have hcompl : Fintype.card {jj : {j : Fin n // j ≠ j₀} //
        ¬ ∃ i, i < len ∧ γ i = some ((jj : {j : Fin n // j ≠ j₀}) : Fin n)}
      = Fintype.card {b : Fin m // ¬ ∃ jj, g jj = b} := by
    omega
  have e2 := Fintype.equivOfCardEq hcompl
  obtain ⟨σ, hσ⟩ : ∃ σ : {j : Fin n // j ≠ j₀} ≃ Fin m,
      ∀ (jj : {j : Fin n // j ≠ j₀})
        (hQ : ∃ i, i < len ∧ γ i = some ((jj : Fin n))), σ jj = g ⟨jj, hQ⟩ := by
    refine ⟨(Equiv.sumCompl (fun jj : {j : Fin n // j ≠ j₀} =>
        ∃ i, i < len ∧ γ i = some ((jj : Fin n)))).symm.trans
      ((e1.sumCongr e2).trans (Equiv.sumCompl (fun b : Fin m => ∃ jj, g jj = b))), ?_⟩
    intro jj hQ
    have hsymm : (Equiv.sumCompl (fun jj : {j : Fin n // j ≠ j₀} =>
        ∃ i, i < len ∧ γ i = some ((jj : Fin n)))).symm jj = Sum.inl ⟨jj, hQ⟩ := by
      apply (Equiv.sumCompl _).injective
      rw [Equiv.apply_symm_apply]
      rfl
    show (Equiv.sumCompl (fun b : Fin m => ∃ jj, g jj = b))
      ((e1.sumCongr e2) ((Equiv.sumCompl (fun jj : {j : Fin n // j ≠ j₀} =>
        ∃ i, i < len ∧ γ i = some ((jj : Fin n)))).symm jj)) = g ⟨jj, hQ⟩
    rw [hsymm]
    show ((e1 ⟨jj, hQ⟩ : {b : Fin m // ∃ jj, g jj = b}) : Fin m) = g ⟨jj, hQ⟩
    exact he1val ⟨jj, hQ⟩
  refine ⟨σ.symm, ?_⟩
  intro i hi j b hγ hb
  have hjne : j ≠ j₀ := by
    intro hcon
    exact hj₀ i hi (by rw [hγ, hcon])
  have hQj : ∃ i', i' < len ∧ γ i' = some (((⟨j, hjne⟩ : {j : Fin n // j ≠ j₀}) : Fin n)) :=
    ⟨i, hi, hγ⟩
  have hgb : g ⟨⟨j, hjne⟩, hQj⟩ = b :=
    Option.some.inj ((hg ⟨⟨j, hjne⟩, hQj⟩ i hi hγ).symm.trans hb)
  have hσb : σ ⟨j, hjne⟩ = b := by
    rw [hσ ⟨j, hjne⟩ hQj, hgb]
  have hfin : σ.symm b = ⟨j, hjne⟩ := by
    rw [← hσb, Equiv.symm_apply_apply]
  exact congrArg Subtype.val hfin

section

variable {X : Scheme.{u}} {k : Type u} [Field k]

private theorem appLE_subschemeι_chartPartialDeriv_complOrderEmb_consolidated327 {p : X ⟶ Spec (CommRingCat.of k)}
    [Smooth p]
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (c : EtaleChart p U n)
    (H : X.IdealSheafData) [Smooth (H.subschemeι ≫ p)] (j₀ : Fin n)
    (hH : restrictIdeal H U = c.coordIdeal {j₀})
    (i : Fin (n - ({j₀} : Finset (Fin n)).card)) (r : Γ(X, U)) :
    (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom
        (chartPartialDeriv hU c (complOrderEmb n {j₀} i) r)
      = chartPartialDeriv (isAffineOpen_preimage_subschemeι H hU)
          (c.restrictToSubscheme hU H {j₀} hH) i
          ((H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom r) := by
  classical
  have hWaff : IsAffineOpen (H.subschemeι ⁻¹ᵁ U) := isAffineOpen_preimage_subschemeι H hU
  let instU : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let instW : Algebra k Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U) :=
    sectionsAlgebra k (H.subschemeι ≫ p) (H.subschemeι ⁻¹ᵁ U)
  let instcU : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := c.algebra
  have instTU : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := c.isScalarTower
  have instFEU : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) :=
    c.algebra_formallyEtale hU
  let instcW : Algebra
      (MvPolynomial (ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card))) k)
      Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U) := (c.restrictToSubscheme hU H {j₀} hH).algebra
  have instTW : IsScalarTower k
      (MvPolynomial (ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card))) k)
      Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U) := (c.restrictToSubscheme hU H {j₀} hH).isScalarTower
  have instFEW : Algebra.FormallyEtale
      (MvPolynomial (ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card))) k)
      Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U) :=
    (c.restrictToSubscheme hU H {j₀} hH).algebra_formallyEtale hWaff
  have hcomm : ∀ a : k,
      (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom (algebraMap k Γ(X, U) a)
        = algebraMap k Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U) a := by
    intro a
    exact sectionsAlgebraMap_appLE_apply k p H.subschemeι U (H.subschemeι ⁻¹ᵁ U) le_rfl a
  let π : Γ(X, U) →ₐ[k] Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U) :=
    { (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom with commutes' := hcomm }
  have hπsurj : Function.Surjective π := by
    intro z
    obtain ⟨w, hw⟩ := Scheme.IdealSheafData.subschemeι_app_surjective H ⟨U, hU⟩ z
    refine ⟨w, ?_⟩
    show (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom w = z
    rw [Scheme.Hom.appLE_eq_app]
    exact hw
  have hker : RingHom.ker π.toRingHom = Ideal.span ({c.coord j₀} : Set Γ(X, U)) := by
    have h1 : RingHom.ker (Scheme.Hom.app H.subschemeι U).hom = H.ideal ⟨U, hU⟩ :=
      Scheme.IdealSheafData.ker_subschemeι_app H ⟨U, hU⟩
    have h2 : H.ideal ⟨U, hU⟩
        = Ideal.span (c.coord '' ((({j₀} : Finset (Fin n))) : Set (Fin n))) :=
      c.ideal_eq_span_coord hU H {j₀} hH
    have h3 : (c.coord '' ((({j₀} : Finset (Fin n))) : Set (Fin n)))
        = ({c.coord j₀} : Set Γ(X, U)) := by
      simp
    show RingHom.ker (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom = _
    rw [Scheme.Hom.appLE_eq_app, h1, h2, h3]
  have hne : complOrderEmb n {j₀} i ≠ j₀ := by
    have hnm := complOrderEmb_notMem n {j₀} i
    simpa using hnm
  have hD0 : (EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, U)
      (ULift.up (complOrderEmb n {j₀} i))) (c.coord j₀) = 0 := by
    rw [← c.etaleCoordinates_coord j₀]
    refine EtaleCoordinates.partialDeriv_coord_of_ne k (ULift.{u} (Fin n)) Γ(X, U)
      (ULift.up (complOrderEmb n {j₀} i)) (ULift.up j₀) ?_
    intro hcon
    exact hne (congrArg ULift.down hcon)
  set δ := EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, U)
      (ULift.up (complOrderEmb n {j₀} i)) with hδdef
  set δ' := liftDerivationOfKerEqSpan π hπsurj (c.coord j₀) hker δ hD0 with hδ'def
  have hdesc : ∀ z : Γ(X, U), δ' (π z) = π (δ z) := fun z =>
    liftDerivationOfKerEqSpan_apply π hπsurj (c.coord j₀) hker δ hD0 z
  have hval : ∀ b : ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card)),
      δ' (EtaleCoordinates.coord k (ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card)))
            Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U) b)
        = if b = ULift.up i then (1 : Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U)) else 0 := by
    intro b
    have hcb : EtaleCoordinates.coord k
        (ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card)))
        Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U) b
        = (c.restrictToSubscheme hU H {j₀} hH).coord b.down :=
      (c.restrictToSubscheme hU H {j₀} hH).etaleCoordinates_coord b.down
    have hcd : (c.restrictToSubscheme hU H {j₀} hH).coord b.down
        = π (c.coord (complOrderEmb n {j₀} b.down)) :=
      EtaleChart.restrictToSubscheme_coord c hU H {j₀} hH b.down
    rw [hcb, hcd, hdesc]
    by_cases hb : b.down = i
    · have h1 : δ (c.coord (complOrderEmb n {j₀} b.down)) = 1 := by
        rw [hb, hδdef, ← c.etaleCoordinates_coord (complOrderEmb n {j₀} i)]
        exact EtaleCoordinates.partialDeriv_coord_self k (ULift.{u} (Fin n)) Γ(X, U)
          (ULift.up (complOrderEmb n {j₀} i))
      have h2 : b = ULift.up i := by
        cases b
        exact congrArg ULift.up hb
      rw [h1, h2]
      simp
    · have h1 : δ (c.coord (complOrderEmb n {j₀} b.down)) = 0 := by
        rw [hδdef, ← c.etaleCoordinates_coord (complOrderEmb n {j₀} b.down)]
        refine EtaleCoordinates.partialDeriv_coord_of_ne k (ULift.{u} (Fin n)) Γ(X, U)
          (ULift.up (complOrderEmb n {j₀} i)) (ULift.up (complOrderEmb n {j₀} b.down)) ?_
        intro hcon
        exact hb ((complOrderEmb n {j₀}).injective (congrArg ULift.down hcon)).symm
      have h2 : ¬ (b = ULift.up i) := by
        intro hcon
        exact hb (congrArg ULift.down hcon)
      rw [h1, if_neg h2]
      simp
  have hδ'eq : δ' = EtaleCoordinates.partialDeriv k
      (ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card)))
      Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U) (ULift.up i) := by
    rw [EtaleCoordinates.eq_sum_smul_partialDeriv k
      (ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card)))
      Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U) δ']
    simp [hval]
  show π (δ r) = EtaleCoordinates.partialDeriv k
      (ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card)))
      Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U) (ULift.up i) (π r)
  rw [← hδ'eq]
  exact (hdesc r).symm

end

section

variable {P : Scheme.{u}} {k : Type u} [Field k]

theorem hasLocalCoordsOnSmoothHypersurface_of_comap (p : P ⟶ Spec (CommRingCat.of k))
    [Smooth p] (H : P.IdealSheafData) (N : List P.IdealSheafData)
    (Z : H.subscheme.IdealSheafData)
    (hN : InStrictNormalCrossingPosition p (H :: N))
    (hZ : HasStrictNormalCrossingsWith (H.subschemeι ≫ p) Z (N.map fun D => D.comap H.subschemeι)) :
    HasLocalCoordsOnSmoothHypersurface p H N Z := by
  classical
  intro x hx
  have hxH : x ∈ H.support :=
    Scheme.IdealSheafData.support_antitone (le_ker_comp_subschemeι H Z) hx
  have hHsm : Smooth (H.subschemeι ≫ p) := (hN.1 H (by simp)).2
  have hHft : LocallyOfFiniteType (H.subschemeι ≫ p) := inferInstance
  obtain ⟨y, hyx⟩ := exists_subschemeι_base_eq_of_mem_support_consolidated327 H hxH
  obtain ⟨U₀, hxU₀, n₀, c₀, a₀, hinj₀, hnone₀, hsome₀⟩ := hN.2 x
  obtain ⟨U₁, hU₁, hxU₁, hU₁U₀⟩ := exists_isAffineOpen_mem_and_subset hxU₀
  have hdesc₁ : ∀ i, ∀ hi : i < (H :: N).length,
      ((a₀ i = none → restrictIdeal ((H :: N)[i]'hi) U₁ = ⊤) ∧
        ∀ j, a₀ i = some j →
          restrictIdeal ((H :: N)[i]'hi) U₁ = (c₀.restrict hU₁U₀).coordIdeal {j}) := by
    intro i hi
    exact ⟨fun hn => restrictIdeal_eq_top_of_le _ hU₁U₀ (hnone₀ i hi hn),
      fun j hj => restrictIdeal_eq_restrict_coordIdeal_of_le hU₁U₀ c₀ _ {j} (hsome₀ i hi j hj)⟩
  obtain ⟨U, hU, hxU, n, c, γ, hdesc, hinj, hcoord⟩ :=
    exists_etaleChart_coord_mem_primeIdealOf (H :: N) x U₁ hU₁ hxU₁ (c₀.restrict hU₁U₀) a₀ hdesc₁
      (fun i i' hi hi' j h1 h2 => hinj₀ i hi i' hi' j h1 h2)
  have h0len : 0 < (H :: N).length := by simp
  have hH0 : restrictIdeal ((H :: N)[0]'h0len) U = restrictIdeal H U := by simp
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin n, γ 0 = some j₀ := by
    cases hc : γ 0 with
    | none =>
        refine absurd hxH (notMem_support_of_restrictIdeal_eq_top H U x hxU ?_)
        rw [← hH0]
        exact (hdesc 0 h0len).1 hc
    | some j => exact ⟨j, rfl⟩
  have hHU : restrictIdeal H U = c.coordIdeal {j₀} := by
    rw [← hH0]
    exact (hdesc 0 h0len).2 j₀ hj₀
  have hyU : y ∈ H.subschemeι ⁻¹ᵁ U := by
    show H.subschemeι.base y ∈ U
    rw [hyx]
    exact hxU
  have hWaff : IsAffineOpen (H.subschemeι ⁻¹ᵁ U) := isAffineOpen_preimage_subschemeι H hU
  have hprimeEq : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
      = Ideal.comap (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom
          (hWaff.primeIdealOf ⟨y, hyU⟩).asIdeal := by
    rw [Scheme.Hom.appLE_eq_app]
    have hpt : (⟨H.subschemeι.base y, hyU⟩ : ↥U) = ⟨x, hxU⟩ := Subtype.ext hyx
    rw [← hpt]
    exact primeIdealOf_eq_comap_primeIdealOf_consolidated327 H.subschemeι hU hWaff hyU
  have hyZ : y ∈ Z.support := by
    refine mem_support_of_ideal_le_primeIdealOf Z hWaff hyU ?_
    intro a ha
    obtain ⟨b, hb⟩ : ∃ b, (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom b = a := by
      obtain ⟨b, hb⟩ := Scheme.IdealSheafData.subschemeι_app_surjective H ⟨U, hU⟩ a
      refine ⟨b, ?_⟩
      rw [Scheme.Hom.appLE_eq_app]
      exact hb
    have hbker : b ∈ (Z.subschemeι ≫ H.subschemeι).ker.ideal ⟨U, hU⟩ := by
      rw [ker_comp_subschemeι_ideal_eq_comap H Z hU, Ideal.mem_comap, hb]
      exact ha
    have hmem := ideal_le_primeIdealOf (Z.subschemeι ≫ H.subschemeι).ker hU hxU hx hbker
    rw [hprimeEq, Ideal.mem_comap, hb] at hmem
    exact hmem
  obtain ⟨V, hyV, m, c', a', S', hinj', hnone', hsome', hZV⟩ := hZ y hyZ
  obtain ⟨V₁, hV₁, hyV₁, hV₁V⟩ := exists_isAffineOpen_mem_and_subset hyV
  obtain ⟨U', hU'aff, hyU', hW'V₁, hU'U⟩ :
      ∃ U' : P.Opens, IsAffineOpen U' ∧ y ∈ H.subschemeι ⁻¹ᵁ U' ∧
        (H.subschemeι ⁻¹ᵁ U') ≤ V₁ ∧ U' ≤ U := by
    obtain ⟨g, hyg, hgV, hgU⟩ := exists_basicOpen_subschemeι_preimage_le_consolidated327 H hU V₁ hyU hyV₁
    exact ⟨P.basicOpen g, hU.basicOpen g, hyg, hgV, hgU⟩
  have hxU' : x ∈ U' := by
    rw [← hyx]
    exact hyU'
  have hW'aff : IsAffineOpen (H.subschemeι ⁻¹ᵁ U') := isAffineOpen_preimage_subschemeι H hU'aff
  have hHU' : restrictIdeal H U' = (c.restrict hU'U).coordIdeal {j₀} :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hU'U c H {j₀} hHU
  have hZW' : restrictIdeal Z (H.subschemeι ⁻¹ᵁ U')
      = ((c'.restrict hV₁V).restrict hW'V₁).coordIdeal S' := by
    have h1 : restrictIdeal Z V₁ = (c'.restrict hV₁V).coordIdeal S' :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hV₁V c' Z S' hZV
    exact restrictIdeal_eq_restrict_coordIdeal_of_le hW'V₁ (c'.restrict hV₁V) Z S' h1
  have hmn : m + 1 = n :=
    etaleChart_numCoords_add_one_of_hypersurface p H hU'aff (c.restrict hU'U) j₀ hHU' hW'aff
      ((c'.restrict hV₁V).restrict hW'V₁) y hyU' hyU'
  have hPx' : (hU'aff.primeIdealOf ⟨x, hxU'⟩).asIdeal
      = Ideal.comap (H.subschemeι.appLE U' (H.subschemeι ⁻¹ᵁ U') le_rfl).hom
          (hW'aff.primeIdealOf ⟨y, hyU'⟩).asIdeal := by
    rw [Scheme.Hom.appLE_eq_app]
    have hpt : (⟨H.subschemeι.base y, hyU'⟩ : ↥U') = ⟨x, hxU'⟩ := Subtype.ext hyx
    rw [← hpt]
    exact primeIdealOf_eq_comap_primeIdealOf_consolidated327 H.subschemeι hU'aff hW'aff hyU'
  have hπsurj : Function.Surjective
      (H.subschemeι.appLE U' (H.subschemeι ⁻¹ᵁ U') le_rfl).hom := by
    rw [Scheme.Hom.appLE_eq_app]
    exact Scheme.IdealSheafData.subschemeι_app_surjective H ⟨U', hU'aff⟩
  have hcomapideal : ∀ D : P.IdealSheafData,
      (D.comap H.subschemeι).ideal ⟨H.subschemeι ⁻¹ᵁ U', hW'aff⟩
        = Ideal.map (H.subschemeι.appLE U' (H.subschemeι ⁻¹ᵁ U') le_rfl).hom
            (D.ideal ⟨U', hU'aff⟩) := fun D =>
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE D H.subschemeι ⟨U', hU'aff⟩
      ⟨H.subschemeι ⁻¹ᵁ U', hW'aff⟩ le_rfl
  have hNsome : ∀ (i : ℕ) (hi : i < N.length) (j : Fin n), γ (i + 1) = some j →
      restrictIdeal (N[i]'hi) U' = (c.restrict hU'U).coordIdeal {j} := by
    intro i hi j hij
    refine restrictIdeal_eq_restrict_coordIdeal_of_le hU'U c _ {j} ?_
    have h := (hdesc (i + 1) (by simpa using hi)).2 j hij
    simpa using h
  have hxN : ∀ (i : ℕ) (hi : i < N.length) (j : Fin n), γ (i + 1) = some j →
      x ∈ (N[i]'hi).support := by
    intro i hi j hij
    refine mem_support_of_ideal_le_primeIdealOf _ hU hxU ?_
    have hid : (N[i]'hi).ideal ⟨U, hU⟩
        = Ideal.span (c.coord '' ((({j} : Finset (Fin n))) : Set (Fin n))) := by
      refine c.ideal_eq_span_coord hU _ {j} ?_
      have h := (hdesc (i + 1) (by simpa using hi)).2 j hij
      simpa using h
    rw [hid, Ideal.span_le]
    rintro z ⟨j', hj', rfl⟩
    have hjj : j' = j := by simpa using hj'
    subst hjj
    exact hcoord (i + 1) (by simpa using hi) j' hij
  have hyND : ∀ (i : ℕ) (hi : i < N.length) (j : Fin n), γ (i + 1) = some j →
      y ∈ ((N[i]'hi).comap H.subschemeι).support := by
    intro i hi j hij
    refine mem_support_of_ideal_le_primeIdealOf _ hW'aff hyU' ?_
    rw [hcomapideal, Ideal.map_le_iff_le_comap, ← hPx']
    exact ideal_le_primeIdealOf _ hU'aff hxU' (hxN i hi j hij)
  have ha'some : ∀ (i : ℕ) (hi : i < N.length) (j : Fin n), γ (i + 1) = some j →
      ∃ b : Fin m, a' i = some b := by
    intro i hi j hij
    cases hb : a' i with
    | some b => exact ⟨b, rfl⟩
    | none =>
        exfalso
        have hiE : i < (N.map fun D => D.comap H.subschemeι).length := by simpa using hi
        have htop := hnone' i hiE hb
        have hE : ((N.map fun D => D.comap H.subschemeι)[i]'hiE)
            = (N[i]'hi).comap H.subschemeι := by simp
        rw [hE] at htop
        have htop' : restrictIdeal ((N[i]'hi).comap H.subschemeι) (H.subschemeι ⁻¹ᵁ U') = ⊤ :=
          restrictIdeal_eq_top_of_le _ (le_trans hW'V₁ hV₁V) htop
        exact notMem_support_of_restrictIdeal_eq_top _ _ y hyU' htop' (hyND i hi j hij)
  have hinja : ∀ i i' : ℕ, i < N.length → i' < N.length → ∀ b : Fin m,
      a' i = some b → a' i' = some b → i = i' := by
    intro i i' hi hi' b h1 h2
    exact hinj' i (by simpa using hi) i' (by simpa using hi') b h1 h2
  have hinjγ : ∀ i i' : ℕ, i < N.length → i' < N.length → ∀ j : Fin n,
      γ (i + 1) = some j → γ (i' + 1) = some j → i = i' := by
    intro i i' hi hi' j h1 h2
    have h := hinj (i + 1) (i' + 1) (by simpa using hi) (by simpa using hi') j h1 h2
    omega
  have hj₀ne : ∀ i : ℕ, i < N.length → γ (i + 1) ≠ some j₀ := by
    intro i hi hcon
    have h := hinj 0 (i + 1) h0len (by simpa using hi) j₀ hj₀ hcon
    omega
  obtain ⟨ρ, hρ⟩ := exists_equiv_subtype_ne_compatible_consolidated327 hmn j₀ N.length (fun i => γ (i + 1)) a'
    hinjγ hinja hj₀ne (fun i hi j hij => ha'some i hi j hij)
  have hmatched : ∀ (i : ℕ) (hi : i < N.length) (j : Fin n) (b : Fin m),
      γ (i + 1) = some j → a' i = some b →
      (∃ v : (Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U'))ˣ,
        (H.subschemeι.appLE U' (H.subschemeι ⁻¹ᵁ U') le_rfl).hom ((c.restrict hU'U).coord j)
          = (v : Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U')) *
              ((c'.restrict hV₁V).restrict hW'V₁).coord b) ∧
      ((c'.restrict hV₁V).restrict hW'V₁).coord b ∈
        (hW'aff.primeIdealOf ⟨y, hyU'⟩).asIdeal := by
    intro i hi j b hij hib
    have hiE : i < (N.map fun D => D.comap H.subschemeι).length := by simpa using hi
    have hE : ((N.map fun D => D.comap H.subschemeι)[i]'hiE)
        = (N[i]'hi).comap H.subschemeι := by simp
    have hcoordW : restrictIdeal ((N[i]'hi).comap H.subschemeι) (H.subschemeι ⁻¹ᵁ U')
        = ((c'.restrict hV₁V).restrict hW'V₁).coordIdeal {b} := by
      have h1 := hsome' i hiE b hib
      rw [hE] at h1
      have h2 := restrictIdeal_eq_restrict_coordIdeal_of_le hV₁V c' _ {b} h1
      exact restrictIdeal_eq_restrict_coordIdeal_of_le hW'V₁ (c'.restrict hV₁V) _ {b} h2
    have hspanW : ((N[i]'hi).comap H.subschemeι).ideal ⟨H.subschemeι ⁻¹ᵁ U', hW'aff⟩
        = Ideal.span {((c'.restrict hV₁V).restrict hW'V₁).coord b} := by
      have h := ((c'.restrict hV₁V).restrict hW'V₁).ideal_eq_span_coord hW'aff _ {b} hcoordW
      simpa using h
    have hspanU : (N[i]'hi).ideal ⟨U', hU'aff⟩
        = Ideal.span {(c.restrict hU'U).coord j} := by
      have h := (c.restrict hU'U).ideal_eq_span_coord hU'aff _ {j} (hNsome i hi j hij)
      simpa using h
    have hmapeq : Ideal.span {(H.subschemeι.appLE U' (H.subschemeι ⁻¹ᵁ U') le_rfl).hom
          ((c.restrict hU'U).coord j)}
        = Ideal.span {((c'.restrict hV₁V).restrict hW'V₁).coord b} := by
      rw [← hspanW, hcomapideal, hspanU, Ideal.map_span, Set.image_singleton]
    refine ⟨exists_unit_mul_coord_of_span_eq (H.subschemeι ≫ p) hW'aff
      ((c'.restrict hV₁V).restrict hW'V₁) b _ hmapeq, ?_⟩
    rw [← Ideal.span_singleton_le_iff_mem, ← hspanW]
    exact ideal_le_primeIdealOf _ hW'aff hyU' (hyND i hi j hij)
  have hlift : ∀ b : Fin m, ∃ (wbb : Γ(P, U'))
      (vbb : (Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U'))ˣ),
      (H.subschemeι.appLE U' (H.subschemeι ⁻¹ᵁ U') le_rfl).hom wbb
          = (vbb : Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U')) *
              ((c'.restrict hV₁V).restrict hW'V₁).coord b ∧
      (vbb = 1 ∨ ((c'.restrict hV₁V).restrict hW'V₁).coord b ∈
        (hW'aff.primeIdealOf ⟨y, hyU'⟩).asIdeal) ∧
      (∀ (i : ℕ), i < N.length → ∀ j : Fin n, γ (i + 1) = some j → a' i = some b →
        wbb = (c.restrict hU'U).coord j) := by
    intro b
    by_cases hb : ∃ i, ∃ _ : i < N.length, ∃ j : Fin n, γ (i + 1) = some j ∧ a' i = some b
    · obtain ⟨i, hi, j, hij, hib⟩ := hb
      obtain ⟨⟨v, hv⟩, hmem⟩ := hmatched i hi j b hij hib
      refine ⟨(c.restrict hU'U).coord j, v, hv, Or.inr hmem, ?_⟩
      intro i' hi' j' hij' hib'
      have hii : i' = i := hinja i' i hi' hi b hib' hib
      subst hii
      have hjj : j' = j := Option.some.inj (hij'.symm.trans hij)
      rw [hjj]
    · obtain ⟨wbb, hwbb⟩ := hπsurj (((c'.restrict hV₁V).restrict hW'V₁).coord b)
      refine ⟨wbb, 1, ?_, Or.inl rfl, ?_⟩
      · rw [hwbb]
        simp
      · intro i hi j hij hib
        exact absurd ⟨i, hi, j, hij, hib⟩ hb
  choose wb vb hvb1 hvb2 hvb3 using hlift
  obtain ⟨w, hw0, hwρ⟩ : ∃ w : ULift.{u} (Fin n) → Γ(P, U'),
      w (ULift.up j₀) = (c.restrict hU'U).coord j₀ ∧
      ∀ b : Fin m, w (ULift.up ((ρ b : Fin n))) = wb b := by
    refine ⟨fun t => if h : t.down = j₀ then (c.restrict hU'U).coord j₀
      else wb (ρ.symm ⟨t.down, h⟩), ?_, ?_⟩
    · exact dif_pos rfl
    · intro b
      have hne : ((ρ b : Fin n)) ≠ j₀ := (ρ b).2
      show (if h : ((ρ b : Fin n)) = j₀ then (c.restrict hU'U).coord j₀
        else wb (ρ.symm ⟨((ρ b : Fin n)), h⟩)) = wb b
      rw [dif_neg hne]
      congr 1
      have hsub : (⟨((ρ b : Fin n)), hne⟩ : {j : Fin n // j ≠ j₀}) = ρ b := rfl
      rw [hsub, Equiv.symm_apply_apply]
  let instkU : Algebra k Γ(P, U') := sectionsAlgebra k p U'
  let instcU : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(P, U') :=
    (c.restrict hU'U).algebra
  have instTU : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(P, U') :=
    (c.restrict hU'U).isScalarTower
  have instFEU : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(P, U') :=
    (c.restrict hU'U).algebra_formallyEtale hU'aff
  let instkW : Algebra k Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U') :=
    sectionsAlgebra k (H.subschemeι ≫ p) (H.subschemeι ⁻¹ᵁ U')
  let instcW : Algebra (MvPolynomial (ULift.{u} (Fin m)) k)
      Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U') := ((c'.restrict hV₁V).restrict hW'V₁).algebra
  have instTW : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k)
      Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U') := ((c'.restrict hV₁V).restrict hW'V₁).isScalarTower
  have instFEW : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k)
      Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U') :=
    ((c'.restrict hV₁V).restrict hW'V₁).algebra_formallyEtale hW'aff
  let instcA : Algebra (MvPolynomial (ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card))) k)
      Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U') :=
    ((c.restrict hU'U).restrictToSubscheme hU'aff H {j₀} hHU').algebra
  have instTA : IsScalarTower k
      (MvPolynomial (ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card))) k)
      Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U') :=
    ((c.restrict hU'U).restrictToSubscheme hU'aff H {j₀} hHU').isScalarTower
  have instFEA : Algebra.FormallyEtale
      (MvPolynomial (ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card))) k)
      Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U') :=
    ((c.restrict hU'U).restrictToSubscheme hU'aff H {j₀} hHU').algebra_formallyEtale hW'aff
  have hcard : n - ({j₀} : Finset (Fin n)).card = m := by
    rw [Finset.card_singleton]
    omega
  have hιAex : ∀ b : Fin m, ∃ i : Fin (n - ({j₀} : Finset (Fin n)).card),
      complOrderEmb n {j₀} i = (ρ b : Fin n) := by
    intro b
    exact exists_complOrderEmb_eq n {j₀} (by simpa using (ρ b).2)
  choose ιA hιA using hιAex
  have hιAinj : Function.Injective ιA := by
    intro a b hab
    have h : (ρ a : Fin n) = (ρ b : Fin n) := by rw [← hιA a, ← hιA b, hab]
    exact ρ.injective (Subtype.ext h)
  have hιAbij : Function.Bijective ιA := by
    refine (Fintype.bijective_iff_injective_and_card ιA).mpr ⟨hιAinj, ?_⟩
    rw [Fintype.card_fin, Fintype.card_fin, hcard]
  have hcompat : ∀ (a : Fin m) (r : Γ(P, U')),
      (H.subschemeι.appLE U' (H.subschemeι ⁻¹ᵁ U') le_rfl).hom
        (EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(P, U')
          (ULift.up ((ρ a : Fin n))) r)
      = EtaleCoordinates.partialDeriv k
          (ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card)))
          Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U') (ULift.up (ιA a))
          ((H.subschemeι.appLE U' (H.subschemeι ⁻¹ᵁ U') le_rfl).hom r) := by
    intro a r
    have h := appLE_subschemeι_chartPartialDeriv_complOrderEmb_consolidated327 hU'aff (c.restrict hU'U) H j₀ hHU' (ιA a) r
    rw [hιA a] at h
    exact h
  have hdet : IsUnit (Matrix.of fun a b : Fin m =>
      EtaleCoordinates.partialDeriv k
        (ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card)))
        Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U') (ULift.up (ιA a))
        (((c'.restrict hV₁V).restrict hW'V₁).coord b)).det := by
    have hτ : ∃ τ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card)),
        ∀ t, τ t = ULift.up (ιA t.down) :=
      ⟨Equiv.ulift.trans ((Equiv.ofBijective ιA hιAbij).trans Equiv.ulift.symm), fun t => rfl⟩
    obtain ⟨τ, hτapp⟩ := hτ
    have h1 : IsUnit (((EtaleCoordinates.basisKaehler k
        (ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card)))
        Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U')).reindex τ.symm).det
        ⇑(EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m))
            Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U'))) :=
      Module.Basis.isUnit_det _ _
    have h2 : ((EtaleCoordinates.basisKaehler k
        (ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card)))
        Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U')).reindex τ.symm).det
        ⇑(EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m))
            Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U'))
        = (Matrix.of fun a b : Fin m =>
            EtaleCoordinates.partialDeriv k
              (ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card)))
              Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U') (ULift.up (ιA a))
              (((c'.restrict hV₁V).restrict hW'V₁).coord b)).det := by
      rw [Module.Basis.det_apply, ← Matrix.det_submatrix_equiv_self Equiv.ulift
        (Matrix.of fun a b : Fin m =>
          EtaleCoordinates.partialDeriv k
            (ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card)))
            Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U') (ULift.up (ιA a))
            (((c'.restrict hV₁V).restrict hW'V₁).coord b))]
      congr 1
      ext s t
      rw [Module.Basis.toMatrix_apply, Module.Basis.repr_reindex_apply, Equiv.symm_symm,
        EtaleCoordinates.basisKaehler_apply, hτapp,
        ← EtaleCoordinates.partialDeriv_apply,
        ((c'.restrict hV₁V).restrict hW'V₁).etaleCoordinates_coord t.down]
      rfl
    rwa [h2] at h1
  obtain ⟨F, hF0, hFsucc⟩ : ∃ F : Fin (m + 1) → ULift.{u} (Fin n),
      F 0 = ULift.up j₀ ∧ ∀ b : Fin m, F b.succ = ULift.up ((ρ b : Fin n)) := by
    refine ⟨fun t => if h : t = 0 then ULift.up.{u} j₀
      else ULift.up.{u} ((ρ (t.pred h) : Fin n)), ?_, ?_⟩
    · show (if h : (0 : Fin (m + 1)) = 0 then ULift.up.{u} j₀
        else ULift.up.{u} ((ρ ((0 : Fin (m + 1)).pred h) : Fin n))) = ULift.up j₀
      exact dif_pos rfl
    · intro b
      show (if h : b.succ = 0 then ULift.up.{u} j₀
        else ULift.up.{u} ((ρ (b.succ.pred h) : Fin n))) = ULift.up ((ρ b : Fin n))
      rw [dif_neg (Fin.succ_ne_zero b), Fin.pred_succ]
  have hbij : Function.Bijective F := by
    refine (Fintype.bijective_iff_injective_and_card F).mpr ⟨?_, ?_⟩
    · intro t₁ t₂ ht
      rcases Fin.eq_zero_or_eq_succ t₁ with rfl | ⟨b₁, rfl⟩
      · rcases Fin.eq_zero_or_eq_succ t₂ with rfl | ⟨b₂, rfl⟩
        · rfl
        · rw [hF0, hFsucc] at ht
          exact absurd (congrArg ULift.down ht).symm (ρ b₂).2
      · rcases Fin.eq_zero_or_eq_succ t₂ with rfl | ⟨b₂, rfl⟩
        · rw [hF0, hFsucc] at ht
          exact absurd (congrArg ULift.down ht) (ρ b₁).2
        · rw [hFsucc, hFsucc] at ht
          exact congrArg Fin.succ (ρ.injective (Subtype.ext (congrArg ULift.down ht)))
    · rw [Fintype.card_fin, Fintype.card_ulift, Fintype.card_fin, hmn]
  obtain ⟨e, he0, hesucc⟩ : ∃ e : ULift.{u} (Fin n) ≃ Fin (m + 1),
      e.symm 0 = ULift.up j₀ ∧ ∀ b : Fin m, e.symm b.succ = ULift.up ((ρ b : Fin n)) := by
    refine ⟨(Equiv.ofBijective F hbij).symm, ?_, fun b => ?_⟩
    · rw [Equiv.symm_symm]
      exact hF0
    · rw [Equiv.symm_symm]
      exact hFsucc b
  have hcol : ∀ a : ULift.{u} (Fin n),
      (Matrix.of fun a b : ULift.{u} (Fin n) =>
        EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(P, U') a (w b)) a (e.symm 0)
        = if a = e.symm 0 then (1 : Γ(P, U')) else 0 := by
    intro a
    rw [he0]
    show EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(P, U') a (w (ULift.up j₀))
      = if a = ULift.up j₀ then (1 : Γ(P, U')) else 0
    rw [hw0, ← (c.restrict hU'U).etaleCoordinates_coord j₀]
    exact EtaleCoordinates.partialDeriv_coord k (ULift.{u} (Fin n)) Γ(P, U') a (ULift.up j₀)
  have hsub : (Matrix.of fun a b : ULift.{u} (Fin n) =>
        EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(P, U') a (w b)).submatrix
        (fun i : Fin m => e.symm i.succ) (fun i : Fin m => e.symm i.succ)
      = Matrix.of fun a b : Fin m =>
        EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(P, U')
          (ULift.up ((ρ a : Fin n))) (wb b) := by
    ext a b
    show EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(P, U')
        (e.symm a.succ) (w (e.symm b.succ))
      = EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(P, U')
        (ULift.up ((ρ a : Fin n))) (wb b)
    rw [hesucc a, hesucc b, hwρ b]
  have hM : (Matrix.of fun a b : ULift.{u} (Fin n) =>
        EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(P, U') a (w b)).det
      = (Matrix.of fun a b : Fin m =>
        EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(P, U')
          (ULift.up ((ρ a : Fin n))) (wb b)).det := by
    rw [det_eq_det_submatrix_of_col_eq_single e _ hcol]
    exact congrArg Matrix.det hsub
  have hnotmem := det_derivation_notMem_comap_of_eq_one_or_mem (k := k) (ι := Fin m)
    (H.subschemeι.appLE U' (H.subschemeι ⁻¹ᵁ U') le_rfl).hom
    (fun a : Fin m => EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(P, U')
      (ULift.up ((ρ a : Fin n))))
    (fun a : Fin m => EtaleCoordinates.partialDeriv k
      (ULift.{u} (Fin (n - ({j₀} : Finset (Fin n)).card)))
      Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U') (ULift.up (ιA a)))
    hcompat wb vb (fun b => ((c'.restrict hV₁V).restrict hW'V₁).coord b) hvb1
    (hW'aff.primeIdealOf ⟨y, hyU'⟩).asIdeal
    (hW'aff.primeIdealOf ⟨y, hyU'⟩).isPrime.ne_top hvb2 hdet
  have hdet0 : (Matrix.of fun a b : ULift.{u} (Fin n) =>
      EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(P, U') a (w b)).det
        ∉ (hU'aff.primeIdealOf ⟨x, hxU'⟩).asIdeal := by
    rw [hM, hPx']
    exact hnotmem
  have hdet : ((EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(P, U')).det
      fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(P, U') (w i)) ∉
        (hU'aff.primeIdealOf ⟨x, hxU'⟩).asIdeal := by
    rw [basisKaehler_det_eq_jacobian_det k (ULift.{u} (Fin n)) Γ(P, U') w]
    exact hdet0
  obtain ⟨V', hV'aff, hV'U', hxV', c₃, hc₃⟩ :=
    exists_etaleChart_restrict_coord_eq_of_jacobianDet_notMem hU'aff
      (c.restrict hU'U) hxU' w hdet
  have hV'U : V' ≤ U := le_trans hV'U' hU'U
  have hpreV' : (H.subschemeι ⁻¹ᵁ V') ≤ (H.subschemeι ⁻¹ᵁ U') := fun a ha => hV'U' ha
  refine ⟨V', hV'aff, hxV', n, c₃, j₀, fun i => γ (i + 1),
    S'.image (fun b : Fin m => ((ρ b : Fin n))), ?_, ?_, ?_, ?_, ?_⟩
  · refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV'aff c₃ H {j₀} ?_
    have h1 : H.ideal ⟨U', hU'aff⟩ = Ideal.span {(c.restrict hU'U).coord j₀} := by
      have h := (c.restrict hU'U).ideal_eq_span_coord hU'aff H {j₀} hHU'
      simpa using h
    have h2 := ideal_eq_span_image_map_of_le H hU'aff hV'aff hV'U' _ h1
    rw [h2]
    congr 1
    rw [Finset.coe_singleton, Set.image_singleton, Set.image_singleton, hc₃ j₀, hw0]
  · intro i hi hnone
    have h := (hdesc (i + 1) (by simpa using hi)).1 hnone
    have h' : restrictIdeal (N[i]'hi) U = ⊤ := by simpa using h
    exact restrictIdeal_eq_top_of_le _ hV'U h'
  · intro i hi j hij
    obtain ⟨b, hb⟩ := ha'some i hi j hij
    have hρb : (ρ b : Fin n) = j := hρ i hi j b hij hb
    have hwj : w (ULift.up j) = (c.restrict hU'U).coord j := by
      have h1 : w (ULift.up j) = wb b := by
        rw [← hρb]
        exact hwρ b
      rw [h1]
      exact hvb3 b i hi j hij hb
    refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV'aff c₃ _ {j} ?_
    have h1 : (N[i]'hi).ideal ⟨U', hU'aff⟩ = Ideal.span {(c.restrict hU'U).coord j} := by
      have h := (c.restrict hU'U).ideal_eq_span_coord hU'aff _ {j} (hNsome i hi j hij)
      simpa using h
    have h2 := ideal_eq_span_image_map_of_le (N[i]'hi) hU'aff hV'aff hV'U' _ h1
    rw [h2]
    congr 1
    rw [Finset.coe_singleton, Set.image_singleton, Set.image_singleton, hc₃ j, hwj]
  · intro i i' hi hi' j h1 h2
    exact hinjγ i i' hi hi' j h1 h2
  · have hZideal : Z.ideal ⟨H.subschemeι ⁻¹ᵁ U', hW'aff⟩
        = Ideal.span (((c'.restrict hV₁V).restrict hW'V₁).coord '' (S' : Set (Fin m))) :=
      ((c'.restrict hV₁V).restrict hW'V₁).ideal_eq_span_coord hW'aff Z S' hZW'
    have hZres : Z.ideal ⟨H.subschemeι ⁻¹ᵁ V', isAffineOpen_preimage_subschemeι H hV'aff⟩
        = Ideal.span ((H.subscheme.presheaf.map (homOfLE hpreV').op).hom ''
            (((c'.restrict hV₁V).restrict hW'V₁).coord '' (S' : Set (Fin m)))) :=
      ideal_eq_span_image_map_of_le Z hW'aff (isAffineOpen_preimage_subschemeι H hV'aff)
        hpreV' _ hZideal
    rw [hZres, Finset.coe_image, ← Set.image_comp, ← Set.image_comp]
    refine (span_image_eq_of_isUnit_mul_consolidated327 (S' : Set (Fin m)) _ _ ?_).symm
    intro b hb
    have h1 : (H.subschemeι.appLE V' (H.subschemeι ⁻¹ᵁ V') le_rfl).hom
          (c₃.coord ((ρ b : Fin n)))
        = (H.subscheme.presheaf.map (homOfLE hpreV').op).hom
            ((vb b : Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U'))
              * ((c'.restrict hV₁V).restrict hW'V₁).coord b) := by
      rw [hc₃ ((ρ b : Fin n)), appLE_preimage_naturality_consolidated327 H.subschemeι hV'U' hpreV', hwρ b,
        hvb1 b]
    exact ⟨(H.subscheme.presheaf.map (homOfLE hpreV').op).hom
        ((vb b : Γ(H.subscheme, H.subschemeι ⁻¹ᵁ U'))), IsUnit.map _ (vb b).isUnit,
      h1.trans (map_mul _ _ _)⟩

end

theorem hasStrictNormalCrossingsWith_ker_cons_of_comap :
    ∀ (k : Type u) [Field k] [CharZero k] (P : Scheme.{u})
      (p : P ⟶ Spec (CommRingCat.of k)) [Smooth p]
      (H : P.IdealSheafData) (N : List P.IdealSheafData),
      InStrictNormalCrossingPosition p (H :: N) →
      ∀ Z : H.subscheme.IdealSheafData,
        HasStrictNormalCrossingsWith (H.subschemeι ≫ p) Z (N.map fun D => D.comap H.subschemeι) →
        HasStrictNormalCrossingsWith p (Z.subschemeι ≫ H.subschemeι).ker (H :: N) := by
  intro k _ _ P p _ H N hN Z hZ
  exact hasStrictNormalCrossingsWith_ker_cons_of_hasLocalCoordsOnSmoothHypersurface p H N Z hN hZ
    (hasLocalCoordsOnSmoothHypersurface_of_comap p H N Z hN hZ)


end
end
end FunctorialResolution.EmbeddedResolution
end
