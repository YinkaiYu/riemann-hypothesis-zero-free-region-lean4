import Mathlib
import ComparatorChallenges.RHCore5Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

universe u v w x
noncomputable section
-- Source: Development.ResolutionOfSingularities.Statements
section
end

-- Source: Development.ResolutionOfSingularities.Foundations.Schemes.AffineOpens
section

namespace AlgebraicGeometry.Scheme

section
variable {X : Scheme.{u}}

theorem exists_isAffineOpen_mem (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U := by
  obtain ⟨U, hU, hxU, -⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)
      (show x ∈ (⊤ : X.Opens) from trivial)
  exact ⟨U, hxU, hU⟩

theorem exists_affineOpens_mem (x : X) : ∃ U : X.affineOpens, x ∈ U.1 := by
  have hx : x ∈ (⨆ U : X.affineOpens, (U : X.Opens)) := by
    rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
    trivial
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨U, hU⟩

theorem exists_affineOpens_mem_le {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ U := by
  obtain ⟨V, hV, hxV, hsub⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  obtain ⟨W, hW, rfl⟩ := hV
  exact ⟨⟨W, hW⟩, hxV, hsub⟩


end

end AlgebraicGeometry.Scheme
end

-- Source: Development.ResolutionOfSingularities.Foundations.Schemes.SchemeCoproduct
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.Blowup

section
variable (X Y : Scheme.{u})

theorem range_coprod_inr_eq_compl :
    Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base
      = (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base)ᶜ := by
  have h : IsCompl (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base)
      (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base) := isCompl_range_inl_inr ..
  exact h.compl_eq.symm

theorem isClosed_range_coprod_inl :
    IsClosed (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base) := by
  have h : IsCompl (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base)
      (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base) := isCompl_range_inl_inr X Y
  have hopen : IsOpen (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base) :=
    (coprod.inr : Y ⟶ X ⨿ Y).isOpenEmbedding.isOpen_range
  rw [← isOpen_compl_iff, h.compl_eq]
  exact hopen

private theorem isOpen_range_coprod_inl_consolidated31 :
    IsOpen (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base) :=
  (coprod.inl : X ⟶ X ⨿ Y).isOpenEmbedding.isOpen_range

theorem isClosed_range_coprod_inr :
    IsClosed (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base) := by
  rw [range_coprod_inr_eq_compl X Y, isClosed_compl_iff]
  exact isOpen_range_coprod_inl_consolidated31 X Y


end

instance instIsClosedImmersionCoprodInl (X Y : Scheme.{u}) :
    IsClosedImmersion (coprod.inl : X ⟶ X ⨿ Y) := by
  constructor
  exact ⟨(coprod.inl : X ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding,
    isClosed_range_coprod_inl X Y⟩

instance instIsClosedImmersionCoprodInr (X Y : Scheme.{u}) :
    IsClosedImmersion (coprod.inr : Y ⟶ X ⨿ Y) := by
  constructor
  exact ⟨(coprod.inr : Y ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding,
    isClosed_range_coprod_inr X Y⟩

private theorem isClosedEmbedding_coprod_inl_base_consolidated31 (X Y : Scheme.{u}) :
    Topology.IsClosedEmbedding ⇑(coprod.inl : X ⟶ X ⨿ Y).base :=
  ⟨(coprod.inl : X ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding, isClosed_range_coprod_inl X Y⟩

instance instQuasiCompactCoprodInl (X Y : Scheme.{u}) :
    QuasiCompact (coprod.inl : X ⟶ X ⨿ Y) := by
  constructor
  intro U _ hU
  exact (isClosedEmbedding_coprod_inl_base_consolidated31 X Y).isCompact_preimage hU

private theorem isClosedEmbedding_coprod_inr_base_consolidated31 (X Y : Scheme.{u}) :
    Topology.IsClosedEmbedding ⇑(coprod.inr : Y ⟶ X ⨿ Y).base :=
  ⟨(coprod.inr : Y ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding, isClosed_range_coprod_inr X Y⟩

instance instQuasiCompactCoprodInr (X Y : Scheme.{u}) :
    QuasiCompact (coprod.inr : Y ⟶ X ⨿ Y) := by
  constructor
  intro U _ hU
  exact (isClosedEmbedding_coprod_inr_base_consolidated31 X Y).isCompact_preimage hU

section

variable {ι : Type u} (X : ι → Scheme.{u}) [HasCoproduct X]

theorem sigmaι_base_ne {i j : ι} (hij : i ≠ j) (x : ↥(X i)) (y : ↥(X j)) :
    (Sigma.ι X i).base x ≠ (Sigma.ι X j).base y := by
  intro h
  exact hij (congrArg Sigma.fst ((sigmaι_eq_iff X i j x y).mp h))

private def iSupOpensRangeSigmaι_consolidated31 {κ : Type u} (Y : κ → Scheme.{u}) [HasCoproduct Y] : (∐ Y).Opens :=
  ⟨⋃ i, Set.range ⇑(Sigma.ι Y i).base,
    isOpen_iUnion fun i => (Sigma.ι Y i).isOpenEmbedding.isOpen_range⟩

private theorem range_sigmaι_subset_iUnion_consolidated31 {κ : Type u} (Y : κ → Scheme.{u}) [HasCoproduct Y]
    (i : κ) : Set.range ⇑(Sigma.ι Y i).base ⊆ Set.range ⇑(iSupOpensRangeSigmaι_consolidated31 Y).ι.base := by
  rw [Scheme.Opens.range_ι]
  intro z hz
  show z ∈ ⋃ i, Set.range ⇑(Sigma.ι Y i).base
  exact Set.mem_iUnion.mpr ⟨i, hz⟩

private theorem surjective_base_of_comp_eq_id_consolidated31 {A B : Scheme.{u}} (g : A ⟶ B) (h : B ⟶ A)
    (hgh : g ≫ h = 𝟙 A) : Function.Surjective ⇑h.base := by
  intro x
  refine ⟨g.base x, ?_⟩
  have h1 := congrArg (fun m : A ⟶ A => m.base x) hgh
  simpa using h1

private theorem exists_sigmaι_base_eq_consolidated31 {κ : Type u} (Y : κ → Scheme.{u}) [HasCoproduct Y]
    (x : ↥(∐ Y)) : ∃ (i : κ) (y : ↥(Y i)), (Sigma.ι Y i).base y = x := by
  have hid : (Sigma.desc fun i =>
      IsOpenImmersion.lift (iSupOpensRangeSigmaι_consolidated31 Y).ι (Sigma.ι Y i) (range_sigmaι_subset_iUnion_consolidated31 Y i)) ≫
        (iSupOpensRangeSigmaι_consolidated31 Y).ι = 𝟙 (∐ Y) := by
    apply Sigma.hom_ext
    intro i
    have hfac := IsOpenImmersion.lift_fac (iSupOpensRangeSigmaι_consolidated31 Y).ι (Sigma.ι Y i)
      (range_sigmaι_subset_iUnion_consolidated31 Y i)
    simp [hfac]
  obtain ⟨w, hw⟩ := surjective_base_of_comp_eq_id_consolidated31 _ _ hid x
  have hmem : x ∈ Set.range ⇑(iSupOpensRangeSigmaι_consolidated31 Y).ι.base := ⟨w, hw⟩
  rw [Scheme.Opens.range_ι] at hmem
  have hmem2 : x ∈ ⋃ i, Set.range ⇑(Sigma.ι Y i).base := hmem
  obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hmem2
  exact ⟨i, y, hy⟩

section
variable (j : ι)

theorem isClosed_range_sigmaι : IsClosed (Set.range ⇑(Sigma.ι X j).base) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  rw [Set.mem_compl_iff] at hx
  obtain ⟨i, y, rfl⟩ := exists_sigmaι_base_eq_consolidated31 X x
  have hij : i ≠ j := by
    intro h
    subst h
    exact hx ⟨y, rfl⟩
  refine ⟨Set.range ⇑(Sigma.ι X i).base, ?_,
    (Sigma.ι X i).isOpenEmbedding.isOpen_range, Set.mem_range_self y⟩
  intro u hu
  obtain ⟨z, rfl⟩ := hu
  rw [Set.mem_compl_iff]
  intro hmem
  obtain ⟨w, hw⟩ := hmem
  exact sigmaι_base_ne X hij z w hw.symm

theorem isClosedImmersion_sigmaι : IsClosedImmersion (Sigma.ι X j) := by
  constructor
  exact ⟨(Sigma.ι X j).isOpenEmbedding.toIsEmbedding, isClosed_range_sigmaι X j⟩


end

instance instIsClosedImmersionSigmaι (j : ι) : IsClosedImmersion (Sigma.ι X j) :=
  isClosedImmersion_sigmaι X j

private theorem isClosedEmbedding_sigmaι_base_consolidated31 {κ : Type u} (Y : κ → Scheme.{u})
    [HasCoproduct Y] (j : κ) (hc : IsClosed (Set.range ⇑(Sigma.ι Y j).base)) :
    Topology.IsClosedEmbedding ⇑(Sigma.ι Y j).base :=
  ⟨(Sigma.ι Y j).isOpenEmbedding.toIsEmbedding, hc⟩

theorem quasiCompact_sigmaι (j : ι) : QuasiCompact (Sigma.ι X j) := by
  constructor
  intro U _ hU
  exact (isClosedEmbedding_sigmaι_base_consolidated31 X j (isClosed_range_sigmaι X j)).isCompact_preimage hU

instance instQuasiCompactSigmaι (j : ι) : QuasiCompact (Sigma.ι X j) :=
  quasiCompact_sigmaι X j

end

end FunctorialResolution.Blowup
end

-- Source: Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace FunctorialResolution.Blowup

private theorem small_directedAffineCover_I₀_consolidated16 (X : Scheme.{u}) :
    Small.{u} X.directedAffineCover.I₀ :=
  small_self _

instance instSmallDirectedAffineCoverI₀ (X : Scheme.{u}) :
    Small.{u} X.directedAffineCover.I₀ :=
  small_directedAffineCover_I₀_consolidated16 X

private theorem isThin_directedAffineCover_I₀_consolidated16 (X : Scheme.{u}) :
    Quiver.IsThin X.directedAffineCover.I₀ := by
  intro a b
  refine ⟨fun f g => ?_⟩
  obtain ⟨⟨hf⟩⟩ := f
  obtain ⟨⟨hg⟩⟩ := g
  rfl

instance instIsThinDirectedAffineCoverI₀ (X : Scheme.{u}) :
    Quiver.IsThin X.directedAffineCover.I₀ :=
  isThin_directedAffineCover_I₀_consolidated16 X

theorem noetherianSpace_toScheme (X : Scheme.{u}) [NoetherianSpace ↥X] (U : X.Opens) :
    NoetherianSpace ↥(U.toScheme) := by
  have h : Topology.IsInducing (fun x : { y : ↥X // y ∈ U } => (x : ↥X)) := ⟨rfl⟩
  exact h.noetherianSpace

instance instNoetherianSpaceToScheme (X : Scheme.{u}) [NoetherianSpace ↥X] (U : X.Opens) :
    NoetherianSpace ↥(U.toScheme) :=
  noetherianSpace_toScheme X U

private theorem isAffineHom_specMap_consolidated16 {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    IsAffineHom (Spec.map φ) :=
  inferInstance

private theorem isAffineHom_pullback_fst_consolidated16 {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsAffineHom g] :
    IsAffineHom (pullback.fst f g) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback f g).flip ‹IsAffineHom g›

theorem isAffineHom_pullback_fst_specMap_of_field {k K : Type u} [Field k] [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (φ : CommRingCat.of k ⟶ CommRingCat.of K) :
    IsAffineHom (pullback.fst p (Spec.map φ)) :=
  @isAffineHom_pullback_fst_consolidated16 X _ _ p (Spec.map φ) (isAffineHom_specMap_consolidated16 φ)

instance instIsAffineHomSpecMapPullbackFst {k K : Type u} [Field k] [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (φ : CommRingCat.of k ⟶ CommRingCat.of K) :
    IsAffineHom (pullback.fst p (Spec.map φ)) :=
  isAffineHom_pullback_fst_specMap_of_field p φ

section
variable {S X : Scheme.{u}} (ι : S ⟶ X) [IsClosedImmersion ι] (Z : S.IdealSheafData)

private theorem le_comap_map_of_isClosedImmersion_consolidated16 : Z ≤ (Z.map ι).comap ι := by
  have hmapdef : Z.map ι = Scheme.Hom.ker (Z.subschemeι ≫ ι) := rfl
  have hcomapdef : (Z.map ι).comap ι
      = Scheme.Hom.ker (pullback.fst ι (Z.map ι).subschemeι) := rfl
  have hle : Scheme.Hom.ker (Z.subschemeι ≫ ι)
      ≤ Scheme.Hom.ker (Z.map ι).subschemeι := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← hmapdef]
  have hu : IsClosedImmersion.lift (Z.subschemeι ≫ ι) (Z.map ι).subschemeι hle
      ≫ (Z.subschemeι ≫ ι) = (Z.map ι).subschemeι :=
    IsClosedImmersion.lift_fac _ _ hle
  set u := IsClosedImmersion.lift (Z.subschemeι ≫ ι) (Z.map ι).subschemeι hle with hudef
  have hk : (pullback.snd ι (Z.map ι).subschemeι ≫ u) ≫ Z.subschemeι
      = pullback.fst ι (Z.map ι).subschemeι := by
    have h2 : ((pullback.snd ι (Z.map ι).subschemeι ≫ u) ≫ Z.subschemeι) ≫ ι
        = pullback.fst ι (Z.map ι).subschemeι ≫ ι := by
      rw [Category.assoc, Category.assoc, hu]
      exact pullback.condition.symm
    exact (cancel_mono ι).mp h2
  rw [hcomapdef, ← hk, Scheme.Hom.ker_comp]
  calc Z = (⊥ : Z.subscheme.IdealSheafData).map Z.subschemeι := by
        rw [Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]
    _ ≤ _ := Scheme.IdealSheafData.map_mono Z.subschemeι bot_le

theorem comap_map_of_isClosedImmersion :
    (Z.map ι).comap ι = Z :=
  le_antisymm (Scheme.IdealSheafData.comap_map_le Z ι) (le_comap_map_of_isClosedImmersion_consolidated16 ι Z)


end

theorem isOpen_connectedComponent_of_noetherianSpace (T : Type v) [TopologicalSpace T]
    [TopologicalSpace.NoetherianSpace T] (x : T) : IsOpen (connectedComponent x) := by
  classical
  have hfin : {Z : Set T | Z ∈ irreducibleComponents T ∧ ¬ Z ⊆ connectedComponent x}.Finite := by
    refine Set.Finite.subset
      (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents) ?_
    rintro Z ⟨hZ, -⟩
    exact hZ
  have heq : (connectedComponent x)ᶜ
      = ⋃ Z ∈ {Z : Set T | Z ∈ irreducibleComponents T ∧ ¬ Z ⊆ connectedComponent x}, Z := by
    apply Set.Subset.antisymm
    · intro y hy
      exact Set.mem_biUnion
        (⟨irreducibleComponent_mem_irreducibleComponents y,
          fun h => hy (h mem_irreducibleComponent)⟩ :
          irreducibleComponent y ∈
            {Z : Set T | Z ∈ irreducibleComponents T ∧ ¬ Z ⊆ connectedComponent x})
        mem_irreducibleComponent
    · intro z hz
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hz
      obtain ⟨Z, ⟨hZ, hZ'⟩, hzZ⟩ := hz
      intro hzc
      have h1 : Z ⊆ connectedComponent z :=
        hZ.1.2.isPreconnected.subset_connectedComponent hzZ
      rw [← connectedComponent_eq hzc] at h1
      exact hZ' h1
  rw [← isClosed_compl_iff, heq]
  exact hfin.isClosed_biUnion (fun Z hZ => isClosed_of_mem_irreducibleComponents _ hZ.1)

end FunctorialResolution.Blowup

namespace TopologicalSpace.NoetherianSpace

section
variable (Y : Type*) [TopologicalSpace Y] [NoetherianSpace Y]

theorem finite_range_connectedComponent :
    (Set.range fun x : Y => connectedComponent x).Finite := by
  classical
  have hfin : (irreducibleComponents Y).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  refine Set.Finite.subset (hfin.image fun Z => ⋃ z ∈ Z, connectedComponent z) ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x, ?_⟩
  have hsub : irreducibleComponent x ⊆ connectedComponent x :=
    (irreducibleComponent_mem_irreducibleComponents x).1.2.isPreconnected.subset_connectedComponent
      mem_irreducibleComponent
  show (⋃ z ∈ irreducibleComponent x, connectedComponent z) = connectedComponent x
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp hy
    rwa [← connectedComponent_eq (hsub hz)] at hyz
  · intro y hy
    exact Set.mem_biUnion mem_irreducibleComponent hy

theorem isClosed_setOf_connectedComponent_subset (A : Set Y) : IsClosed {x : Y | connectedComponent x ⊆ A} := by
  classical
  have hfin :
      {C : Set Y | C ∈ Set.range (fun x : Y => connectedComponent x) ∧ C ⊆ A}.Finite := by
    refine (finite_range_connectedComponent Y).subset ?_
    rintro C ⟨hC, -⟩
    exact hC
  have heq : {x : Y | connectedComponent x ⊆ A}
      = ⋃ C ∈ {C : Set Y | C ∈ Set.range (fun x : Y => connectedComponent x) ∧ C ⊆ A}, C := by
    apply Set.Subset.antisymm
    · intro x hx
      have hmem : connectedComponent x ∈
          {C : Set Y | C ∈ Set.range (fun x : Y => connectedComponent x) ∧ C ⊆ A} :=
        ⟨⟨x, rfl⟩, hx⟩
      exact Set.mem_biUnion hmem mem_connectedComponent
    · intro x hx
      obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨⟨y, hy⟩, hCA⟩ := hC
      have hy' : connectedComponent y = C := hy
      rw [← hy'] at hxC hCA
      show connectedComponent x ⊆ A
      rw [← connectedComponent_eq hxC]
      exact hCA
  rw [heq]
  refine hfin.isClosed_biUnion ?_
  rintro C ⟨⟨x, hx⟩, -⟩
  have hC : C = connectedComponent x := hx.symm
  rw [hC]
  exact isClosed_connectedComponent


end

end TopologicalSpace.NoetherianSpace

namespace AlgebraicGeometry

namespace Scheme

theorem presheaf_map_eq_of_parallel (X₁ : Scheme.{u}) {A B : (X₁.Opens)ᵒᵖ} (g₁ g₂ : A ⟶ B) :
    X₁.presheaf.map g₁ = X₁.presheaf.map g₂ :=
  congrArg X₁.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

namespace Hom

theorem appLE_congr_hom {A B : Scheme.{u}} {f g : A ⟶ B} (hfg : f = g) (O : B.Opens)
    (S : A.Opens) (h1 : S ≤ f ⁻¹ᵁ O) (h2 : S ≤ g ⁻¹ᵁ O) :
    Scheme.Hom.appLE f O S h1 = Scheme.Hom.appLE g O S h2 := by
  subst hfg
  rfl

theorem range_comp_base {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range (f ≫ g).base = g.base '' Set.range f.base := by
  have hcomp : ∀ x : A, (f ≫ g).base x = g.base (f.base x) := fun _ => rfl
  apply Set.Subset.antisymm
  · rintro z ⟨x, rfl⟩
    exact ⟨f.base x, ⟨x, rfl⟩, (hcomp x).symm⟩
  · rintro z ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, hcomp x⟩

end Hom

end Scheme

theorem quasiCompact_of_compactSpace_of_subsingleton {W S : Scheme.{u}} (f : W ⟶ S)
    [CompactSpace ↥W] [Subsingleton ↥S] : QuasiCompact f := by
  constructor
  intro U _ _
  rcases Set.eq_empty_or_nonempty (f.base ⁻¹' U) with h | ⟨w, hw⟩
  · rw [h]
    exact isCompact_empty
  · have h2 : f.base ⁻¹' U = Set.univ := by
      refine Set.eq_univ_of_forall fun w' => ?_
      have hww : f.base w' = f.base w := Subsingleton.elim _ _
      show f.base w' ∈ U
      rw [hww]
      exact hw
    rw [h2]
    exact isCompact_univ

end AlgebraicGeometry
end

-- Source: Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
section

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

private theorem comap_ideal_eq_ker_pullbackFst_consolidated46 (I : Y.IdealSheafData) (f : X ⟶ Y)
    (V : X.affineOpens) :
    (I.comap f).ideal V
      = RingHom.ker ((Limits.pullback.fst f I.subschemeι).app (V : X.Opens)).hom := by
  have hc : I.comap f = Scheme.Hom.ker (Limits.pullback.fst f I.subschemeι) := rfl
  rw [hc, ← map_bot, ideal_map_of_isAffineHom,
    show ((⊥ : (Limits.pullback f I.subschemeι).IdealSheafData).ideal) = ⊥ from ideal_bot]
  exact (RingHom.ker_eq_comap_bot _).symm

private theorem appLE_congr_hom_consolidated46 {Z W : Scheme.{u}} {g₁ g₂ : Z ⟶ W} (h : g₁ = g₂)
    (U : W.Opens) (V : Z.Opens) (e₁ : V ≤ g₁ ⁻¹ᵁ U) :
    g₁.appLE U V e₁ = g₂.appLE U V (h ▸ e₁) := by
  subst h; rfl

private theorem map_appLE_le_ker_pullbackFst_consolidated46 (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens) (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)) :
    Ideal.map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom (I.ideal U) ≤
      RingHom.ker ((Limits.pullback.fst f I.subschemeι).app (V : X.Opens)).hom := by
  have hcond : Limits.pullback.fst f I.subschemeι ≫ f
      = Limits.pullback.snd f I.subschemeι ≫ I.subschemeι := Limits.pullback.condition
  have h2 : (Limits.pullback.fst f I.subschemeι) ⁻¹ᵁ (f ⁻¹ᵁ (U : Y.Opens))
      = (Limits.pullback.snd f I.subschemeι) ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ (U : Y.Opens)) := by
    have h3 := congrArg
      (fun g : (Limits.pullback f I.subschemeι) ⟶ Y => g ⁻¹ᵁ (U : Y.Opens)) hcond
    simpa using h3
  have hle : (Limits.pullback.fst f I.subschemeι) ⁻¹ᵁ (V : X.Opens)
      ≤ (Limits.pullback.snd f I.subschemeι) ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ (U : Y.Opens)) := by
    rw [← h2]
    intro x hx
    exact e hx
  have happ : f.appLE (U : Y.Opens) (V : X.Opens) e
        ≫ (Limits.pullback.fst f I.subschemeι).app (V : X.Opens)
      = I.subschemeι.app (U : Y.Opens)
        ≫ (Limits.pullback.snd f I.subschemeι).appLE (I.subschemeι ⁻¹ᵁ (U : Y.Opens))
            ((Limits.pullback.fst f I.subschemeι) ⁻¹ᵁ (V : X.Opens)) hle := by
    rw [← Scheme.Hom.appLE_eq_app (Limits.pullback.fst f I.subschemeι),
      ← Scheme.Hom.appLE_eq_app I.subschemeι, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE, appLE_congr_hom_consolidated46 hcond]
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  have hker : (I.subschemeι.app (U : Y.Opens)).hom a = 0 := by
    have hd := I.ker_subschemeι_app U
    rw [← RingHom.mem_ker, hd]
    exact ha
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, happ, CommRingCat.hom_comp,
    RingHom.comp_apply, hker, map_zero]

private theorem appLE_top_eq_appTop_consolidated46 (f : X ⟶ Y) (e0 : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) :
    f.appLE (⊤ : Y.Opens) (⊤ : X.Opens) e0 = f.appTop := by
  have h1 : X.presheaf.map (homOfLE e0).op = 𝟙 Γ(X, ⊤) := X.presheaf.map_id (op (⊤ : X.Opens))
  calc f.appLE (⊤ : Y.Opens) (⊤ : X.Opens) e0
      = f.app (⊤ : Y.Opens) ≫ X.presheaf.map (homOfLE e0).op := rfl
    _ = f.app (⊤ : Y.Opens) ≫ 𝟙 Γ(X, ⊤) := by rw [h1]
    _ = f.appTop := Category.comp_id _

theorem ofIdealTop_ideal_top {Z : Scheme.{u}} [IsAffine Z] (J : Ideal Γ(Z, ⊤)) :
    (ofIdealTop J).ideal ⟨⊤, isAffineOpen_top Z⟩ = J := by
  have h := (equivOfIsAffine (X := Z)).apply_symm_apply J
  rw [equivOfIsAffine_symm_apply, equivOfIsAffine_apply] at h
  exact h

section
variable (I : Y.IdealSheafData) (f : X ⟶ Y) (U : Y.affineOpens) (V : X.affineOpens) (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens))

private theorem exists_hom_comp_eq_appLE_comp_consolidated46 (C : CommRingCat.{u}) (q : Γ(X, (V : X.Opens)) ⟶ C)
    (hq : Ideal.map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom (I.ideal U)
      ≤ RingHom.ker q.hom) :
    ∃ ψ : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ (U : Y.Opens)) ⟶ C,
      I.subschemeι.app (U : Y.Opens) ≫ ψ = f.appLE (U : Y.Opens) (V : X.Opens) e ≫ q := by
  refine ⟨(I.subschemeObjIso U).hom ≫ CommRingCat.ofHom
      (Ideal.Quotient.lift (I.ideal U)
        (q.hom.comp (f.appLE (U : Y.Opens) (V : X.Opens) e).hom) ?_), ?_⟩
  · intro a ha
    have h := hq (Ideal.mem_map_of_mem _ ha)
    rw [RingHom.mem_ker] at h
    exact h
  · rw [subschemeι_app, Category.assoc, Iso.inv_hom_id_assoc]
    ext a
    rfl

private theorem exists_hom_pullbackFst_app_comp_eq_consolidated46 (C : CommRingCat.{u}) (q : Γ(X, (V : X.Opens)) ⟶ C)
    (ψ : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ (U : Y.Opens)) ⟶ C)
    (hring : I.subschemeι.app (U : Y.Opens) ≫ ψ
      = f.appLE (U : Y.Opens) (V : X.Opens) e ≫ q) :
    ∃ θ : Γ(Limits.pullback f I.subschemeι,
        Limits.pullback.fst f I.subschemeι ⁻¹ᵁ (V : X.Opens)) ⟶ C,
      (Limits.pullback.fst f I.subschemeι).app (V : X.Opens) ≫ θ = q := by
  have hV : IsAffineOpen (V : X.Opens) := V.2
  have hU : IsAffineOpen (U : Y.Opens) := U.2
  have hf := IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e
  have hι := IsAffineOpen.SpecMap_appLE_fromSpec I.subschemeι hU
      (hU.preimage I.subschemeι) (le_refl (I.subschemeι ⁻¹ᵁ (U : Y.Opens)))
  have hsq : (Spec.map q ≫ hV.fromSpec) ≫ f
      = (Spec.map ψ ≫ (hU.preimage I.subschemeι).fromSpec) ≫ I.subschemeι := by
    rw [Category.assoc, Category.assoc, ← hf, ← hι, ← Category.assoc, ← Category.assoc,
      ← Spec.map_comp, ← Spec.map_comp, Scheme.Hom.appLE_eq_app, hring]
  obtain ⟨g, hlift⟩ : ∃ g : Spec C ⟶ Limits.pullback f I.subschemeι,
      g ≫ Limits.pullback.fst f I.subschemeι = Spec.map q ≫ hV.fromSpec :=
    ⟨Limits.pullback.lift _ _ hsq, Limits.pullback.lift_fst _ _ _⟩
  have hpre : (⊤ : (Spec C).Opens)
      ≤ g ⁻¹ᵁ (Limits.pullback.fst f I.subschemeι ⁻¹ᵁ (V : X.Opens)) := by
    have h3 := congrArg (fun h : Spec C ⟶ X => h ⁻¹ᵁ (V : X.Opens)) hlift
    have h4 : g ⁻¹ᵁ (Limits.pullback.fst f I.subschemeι ⁻¹ᵁ (V : X.Opens))
        = Spec.map q ⁻¹ᵁ (hV.fromSpec ⁻¹ᵁ (V : X.Opens)) := by simpa using h3
    rw [h4, hV.fromSpec_preimage_self]
    simp
  have e₁ : (⊤ : (Spec Γ(X, (V : X.Opens))).Opens) ≤ hV.fromSpec ⁻¹ᵁ (V : X.Opens) :=
    le_of_eq (hV.fromSpec_preimage_self).symm
  have e₂ : (⊤ : (Spec C).Opens)
      ≤ Spec.map q ⁻¹ᵁ (⊤ : (Spec Γ(X, (V : X.Opens))).Opens) := by simp
  have hsplit := Scheme.Hom.appLE_comp_appLE (Spec.map q) hV.fromSpec (V : X.Opens)
      (⊤ : (Spec Γ(X, (V : X.Opens))).Opens) (⊤ : (Spec C).Opens) e₁ e₂
  have h0 : ∀ i : (op (⊤ : (Spec Γ(X, (V : X.Opens))).Opens))
      ⟶ op (⊤ : (Spec Γ(X, (V : X.Opens))).Opens),
      (Spec Γ(X, (V : X.Opens))).presheaf.map i = 𝟙 _ := by
    intro i
    have hi : i = 𝟙 _ := rfl
    rw [hi, CategoryTheory.Functor.map_id]
  have hdef : hV.fromSpec.appLE (V : X.Opens) (⊤ : (Spec Γ(X, (V : X.Opens))).Opens) e₁
      = hV.fromSpec.app (V : X.Opens)
        ≫ (Spec Γ(X, (V : X.Opens))).presheaf.map (homOfLE e₁).op := rfl
  have ha : hV.fromSpec.appLE (V : X.Opens) (⊤ : (Spec Γ(X, (V : X.Opens))).Opens) e₁
      = (Scheme.ΓSpecIso Γ(X, (V : X.Opens))).inv := by
    rw [hdef, hV.fromSpec_app_self, Category.assoc, ← Functor.map_comp, ← op_comp,
      h0, Category.comp_id]
  have hb : (Spec.map q).appTop
      = (Scheme.ΓSpecIso Γ(X, (V : X.Opens))).hom ≫ q ≫ (Scheme.ΓSpecIso C).inv := by
    rw [Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  refine ⟨g.appLE (Limits.pullback.fst f I.subschemeι ⁻¹ᵁ (V : X.Opens))
      (⊤ : (Spec C).Opens) hpre ≫ (Scheme.ΓSpecIso C).hom, ?_⟩
  rw [← Category.assoc, ← Scheme.Hom.appLE_eq_app (Limits.pullback.fst f I.subschemeι),
    Scheme.Hom.appLE_comp_appLE, appLE_congr_hom_consolidated46 hlift, ← hsplit, ha, appLE_top_eq_appTop_consolidated46, hb]
  simp

private theorem ker_pullbackFst_le_map_appLE_consolidated46 :
    RingHom.ker ((Limits.pullback.fst f I.subschemeι).app (V : X.Opens)).hom ≤
      Ideal.map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom (I.ideal U) := by
  obtain ⟨C, q, hq⟩ : ∃ (C : CommRingCat.{u}) (q : Γ(X, (V : X.Opens)) ⟶ C),
      RingHom.ker q.hom = Ideal.map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom (I.ideal U) :=
    ⟨_, CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom (I.ideal U))), Ideal.mk_ker⟩
  obtain ⟨ψ, hψ⟩ := exists_hom_comp_eq_appLE_comp_consolidated46 I f U V e C q (le_of_eq hq.symm)
  obtain ⟨θ, hθ⟩ := exists_hom_pullbackFst_app_comp_eq_consolidated46 I f U V e C q ψ hψ
  rw [← hq]
  intro x hx
  rw [RingHom.mem_ker] at hx ⊢
  rw [← hθ, CommRingCat.hom_comp, RingHom.comp_apply, hx, map_zero]

theorem comap_ideal_eq_map_appLE :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom := by
  rw [comap_ideal_eq_ker_pullbackFst_consolidated46 I f V]
  exact le_antisymm (ker_pullbackFst_le_map_appLE_consolidated46 I f U V e)
    (map_appLE_le_ker_pullbackFst_consolidated46 I f U V e)

theorem map_appLE_le_comap_ideal :
    (I.ideal U).map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom ≤ (I.comap f).ideal V :=
  ge_of_eq (comap_ideal_eq_map_appLE I f U V e)


end

theorem comap_ideal_top_eq_map_appTop [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  have e0 : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := by simp
  rw [comap_ideal_eq_map_appLE I f ⟨⊤, isAffineOpen_top Y⟩ ⟨⊤, isAffineOpen_top X⟩ e0]
  exact congrArg
    (fun φ => Ideal.map (CommRingCat.Hom.hom φ) (I.ideal ⟨⊤, isAffineOpen_top Y⟩))
    (appLE_top_eq_appTop_consolidated46 f e0)

theorem comap_ofIdealTop [IsAffine X] [IsAffine Y] (J : Ideal Γ(Y, ⊤)) (f : X ⟶ Y) :
    (ofIdealTop J).comap f = ofIdealTop (J.map f.appTop.hom) := by
  have h : ((ofIdealTop J).comap f).ideal ⟨⊤, isAffineOpen_top X⟩
      = (ofIdealTop (J.map f.appTop.hom)).ideal ⟨⊤, isAffineOpen_top X⟩ := by
    rw [comap_ideal_top_eq_map_appTop, ofIdealTop_ideal_top, ofIdealTop_ideal_top]
  exact (equivOfIsAffine (X := X)).injective h

section
variable (I : Y.IdealSheafData) (f : X ⟶ Y) (U : Y.affineOpens) (V : X.affineOpens) (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens))

theorem appLE_mem_comap_ideal {x : Γ(Y, (U : Y.Opens))}
    (hx : x ∈ I.ideal U) :
    (f.appLE (U : Y.Opens) (V : X.Opens) e).hom x ∈ (I.comap f).ideal V :=
  map_appLE_le_comap_ideal I f U V e (Ideal.mem_map_of_mem _ hx)

theorem comap_ideal_eq_span_image (s : Set Γ(Y, (U : Y.Opens)))
    (hs : I.ideal U = Ideal.span s) :
    (I.comap f).ideal V
      = Ideal.span ((f.appLE (U : Y.Opens) (V : X.Opens) e).hom '' s) := by
  rw [comap_ideal_eq_map_appLE I f U V e, hs, Ideal.map_span]


end

theorem comap_iSup {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Sort*} (I : ι → Y.IdealSheafData) :
    (⨆ i, I i).comap f = ⨆ i, (I i).comap f :=
  (map_gc f).l_iSup

theorem comap_ι_eq_top_iff_ideal_eq_top {Y : Scheme.{u}} (I : Y.IdealSheafData) {V : Y.Opens}
    (hV : IsAffineOpen V) : I.comap V.ι = ⊤ ↔ I.ideal ⟨V, hV⟩ = ⊤ := by
  have hVaff : IsAffine V.toScheme := hV
  have htop : ∀ U : V.toScheme.affineOpens, (⊤ : V.toScheme.IdealSheafData).ideal U = ⊤ := by
    intro U
    simp
  have e : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by simp
  have himg : V.ι ''ᵁ (⊤ : V.toScheme.Opens) = V := by simp
  have hiso : ∀ U : Y.Opens, U = V.ι ''ᵁ (⊤ : V.toScheme.Opens) →
      ∀ e' : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ U,
        IsIso (V.ι.appLE U (⊤ : V.toScheme.Opens) e') := by
    rintro U rfl e'
    rw [← Scheme.Hom.appIso_hom' V.ι (⊤ : V.toScheme.Opens)]
    infer_instance
  obtain ⟨φ, hφ, hmap⟩ : ∃ φ : Γ(Y, V) ⟶ Γ(V.toScheme, ⊤), IsIso φ ∧
      (I.comap V.ι).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩
        = (I.ideal ⟨V, hV⟩).map φ.hom :=
    ⟨V.ι.appLE V (⊤ : V.toScheme.Opens) e, hiso V himg.symm e,
      comap_ideal_eq_map_appLE I V.ι ⟨V, hV⟩ ⟨⊤, isAffineOpen_top V.toScheme⟩ e⟩
  have hcomp : (CommRingCat.Hom.hom (CategoryTheory.inv φ)).comp (CommRingCat.Hom.hom φ)
      = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, IsIso.hom_inv_id, CommRingCat.hom_id]
  constructor
  · intro h
    rw [h, htop] at hmap
    have h3 : ((I.ideal ⟨V, hV⟩).map φ.hom).map (CategoryTheory.inv φ).hom
        = I.ideal ⟨V, hV⟩ := by
      rw [Ideal.map_map, hcomp, Ideal.map_id]
    rw [← hmap, Ideal.map_top] at h3
    exact h3.symm
  · intro h
    have h2 : (I.comap V.ι).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩
        = (⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩ := by
      rw [hmap, h, Ideal.map_top, htop]
    exact (equivOfIsAffine (X := V.toScheme)).injective h2

theorem ofIdealTop_mul [IsAffine X] (I J : Ideal Γ(X, ⊤)) :
    ofIdealTop (I * J) = ofIdealTop I * ofIdealTop J := by
  ext U : 2
  exact Ideal.map_mul _ _ _

theorem comap_mul (I J : Y.IdealSheafData) (f : X ⟶ Y) :
    (I * J).comap f = I.comap f * J.comap f := by
  refine ext_of_iSup_eq_top
    (fun W : {W : X.affineOpens // ∃ U : Y.affineOpens, (W : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)} =>
      W.1) ?_ ?_
  · refine TopologicalSpace.Opens.ext ?_
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top,
      Set.eq_univ_iff_forall, Set.mem_iUnion]
    intro x
    obtain ⟨W, hxW⟩ := Scheme.exists_affineOpens_mem (f.base x)
    obtain ⟨V, hxV, hVW⟩ :
        ∃ V : X.affineOpens, x ∈ (V : X.Opens) ∧ (V : X.Opens) ≤ f ⁻¹ᵁ (W : Y.Opens) :=
      Scheme.exists_affineOpens_mem_le hxW
    exact ⟨⟨V, W, hVW⟩, hxV⟩
  · rintro ⟨V, W, hVW⟩
    show ((I * J).comap f).ideal V = (I.comap f * J.comap f).ideal V
    rw [comap_ideal_eq_map_appLE (I * J) f W V hVW]
    simp only [ideal_mul, Pi.mul_apply]
    rw [Ideal.map_mul, comap_ideal_eq_map_appLE I f W V hVW,
      comap_ideal_eq_map_appLE J f W V hVW]

theorem comap_pow (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) :
    (I ^ n).comap f = I.comap f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, comap_mul, ih]

theorem mem_support_comap {f : X ⟶ Y} {I : Y.IdealSheafData} {x : X} :
    x ∈ (I.comap f).support ↔ f.base x ∈ I.support := by
  constructor
  · intro hx
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] at hx
    exact hx
  · intro hx
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
    exact hx

theorem ne_top_of_mem_support (J : Y.IdealSheafData) (x : ↥Y) (hx : x ∈ J.support) : J ≠ ⊤ := by
  intro hc
  have hb : J.support = ⊥ :=
    (AlgebraicGeometry.Scheme.IdealSheafData.support_eq_bot_iff J).mpr hc
  have hx2 : x ∈ (J.support : Set ↥Y) := hx
  rw [hb] at hx2
  simp at hx2

section
variable {X : Scheme.{u}} (I : X.IdealSheafData)

theorem eq_top_iff_support_eq_empty :
    I = ⊤ ↔ (I.support : Set X) = ∅ := by
  rw [← support_eq_bot_iff, SetLike.ext'_iff]
  simp

theorem support_nonempty_iff_ne_top :
    (I.support : Set X).Nonempty ↔ I ≠ ⊤ := by
  rw [ne_eq, eq_top_iff_support_eq_empty, Set.nonempty_iff_ne_empty, ne_eq]


end

theorem notMem_support_of_comap_ι_eq_top (I : Y.IdealSheafData) {U : Y.Opens}
    (h : I.comap U.ι = ⊤) {x : Y} (hxU : x ∈ U) : x ∉ I.support := by
  intro hx
  have h1 : (⟨x, hxU⟩ : ↥U) ∈ (I.comap U.ι).support := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
    exact hx
  rw [h, AlgebraicGeometry.Scheme.IdealSheafData.support_top] at h1
  have h2 : (⟨x, hxU⟩ : ↥U) ∈ ((⊥ : TopologicalSpace.Closeds ↥U) : Set ↥U) := h1
  simp at h2

section
variable {X : Scheme.{u}}

private theorem mem_basicOpen_iff_notMem_primeIdealOf_consolidated46 {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (g : Γ(X, U)) :
    x ∈ X.basicOpen g ↔ g ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h1 : hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have h2 : hU.fromSpec ⁻¹ᵁ (X.basicOpen g) = PrimeSpectrum.basicOpen g :=
    hU.fromSpec_preimage_basicOpen g
  constructor
  · intro h
    rw [← h1] at h
    have h3 : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ (X.basicOpen g) := h
    rw [h2] at h3
    exact (PrimeSpectrum.mem_basicOpen g _).mp h3
  · intro h
    have h3 : hU.primeIdealOf ⟨x, hx⟩ ∈ PrimeSpectrum.basicOpen g :=
      (PrimeSpectrum.mem_basicOpen g _).mpr h
    rw [← h2] at h3
    have h4 : hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen g := h3
    rwa [h1] at h4

theorem mem_support_iff_ideal_le_primeIdealOf (I : X.IdealSheafData)
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    x ∈ I.support ↔ I.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := ⟨U, hU⟩) hx,
    Scheme.mem_zeroLocus_iff]
  constructor
  · intro h
    rw [SetLike.le_def]
    intro f hf
    have hb := h f hf
    rw [mem_basicOpen_iff_notMem_primeIdealOf_consolidated46 hU hx f] at hb
    exact not_not.mp hb
  · intro h f hf
    rw [mem_basicOpen_iff_notMem_primeIdealOf_consolidated46 hU hx f]
    exact not_not.mpr (h hf)


end

theorem comap_ι_comp_eq_of_comap_ι_eq (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens)
    (hle : U ≤ f ⁻¹ᵁ V) (I J : Y.IdealSheafData)
    (h : I.comap V.ι = J.comap V.ι) : I.comap (U.ι ≫ f) = J.comap (U.ι ≫ f) := by
  have hfac : X.homOfLE hle ≫ ((f ∣_ V) ≫ V.ι) = U.ι ≫ f := by
    rw [AlgebraicGeometry.morphismRestrict_ι, ← CategoryTheory.Category.assoc,
      AlgebraicGeometry.Scheme.homOfLE_ι]
  have e : ∀ K : Y.IdealSheafData,
      ((K.comap V.ι).comap (f ∣_ V)).comap (X.homOfLE hle) = K.comap (U.ι ≫ f) := by
    intro K
    rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, CategoryTheory.Category.assoc, hfac]
  rw [← e I, ← e J, h]

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem comap_listProd (L : List Y.IdealSheafData) :
    L.prod.comap f = (L.map (·.comap f)).prod := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    exact comap_top f
  | cons D E ih => simp only [List.map_cons, List.prod_cons, comap_mul, ih]

theorem comap_finset_prod {ι : Type*} (s : Finset ι)
    (F : ι → Y.IdealSheafData) :
    (∏ i ∈ s, F i).comap f = ∏ i ∈ s, (F i).comap f := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact comap_top f
  · intro a t ha ih
    simp only [Finset.prod_insert ha, comap_mul, ih]


end

private theorem isReduced_of_ringEquiv_consolidated46 {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (h : _root_.IsReduced B) : _root_.IsReduced A := by
  have := h
  exact ⟨fun a ha => e.injective (by simpa using (ha.map (e : A →+* B)).eq_zero)⟩

private theorem isReduced_stalk_of_radical_consolidated46 (I : X.IdealSheafData)
    (hrad : ∀ U : X.affineOpens, (I.ideal U).IsRadical) (y : ↥I.subscheme) :
    _root_.IsReduced (I.subscheme.presheaf.stalk y) := by
  obtain ⟨U, hU⟩ := Scheme.exists_affineOpens_mem (I.subschemeι.base y)
  have hUaff : IsAffineOpen (U : X.Opens) := U.2
  have hy : y ∈ I.subschemeι ⁻¹ᵁ (U : X.Opens) := hU
  have hV : IsAffineOpen (I.subschemeι ⁻¹ᵁ (U : X.Opens)) :=
    IsAffineOpen.preimage hUaff I.subschemeι
  have hquot := (Ideal.isRadical_iff_quotient_reduced (I.ideal U)).mp (hrad U)
  have hGamma := isReduced_of_ringEquiv_consolidated46 (I.subschemeObjIso U).commRingCatIsoToRingEquiv hquot
  have hTop := isReduced_of_ringEquiv_consolidated46 (Scheme.Opens.topIso
    (I.subschemeι ⁻¹ᵁ (U : X.Opens))).commRingCatIsoToRingEquiv hGamma
  have : IsAffine (↑(I.subschemeι ⁻¹ᵁ (U : X.Opens)) : Scheme.{u}) := hV
  have := hTop
  have : IsReduced (↑(I.subschemeι ⁻¹ᵁ (U : X.Opens)) : Scheme.{u}) :=
    isReduced_of_isAffine_isReduced _
  have key : _root_.IsReduced
      ((↑(I.subschemeι ⁻¹ᵁ (U : X.Opens)) : Scheme.{u}).presheaf.stalk
        (⟨y, hy⟩ : ↥(I.subschemeι ⁻¹ᵁ (U : X.Opens)))) :=
    isReduced_stalk_of_isReduced (↑(I.subschemeι ⁻¹ᵁ (U : X.Opens)) : Scheme.{u})
      (⟨y, hy⟩ : ↥(I.subschemeι ⁻¹ᵁ (U : X.Opens)))
  exact isReduced_of_ringEquiv_consolidated46
    (Scheme.Opens.stalkIso (I.subschemeι ⁻¹ᵁ (U : X.Opens))
      (⟨y, hy⟩ : ↥(I.subschemeι ⁻¹ᵁ (U : X.Opens)))).symm.commRingCatIsoToRingEquiv key

theorem isReduced_subscheme_vanishingIdeal
    (W : Scheme.{u}) (Z : TopologicalSpace.Closeds W) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  have : ∀ y : ↥((Scheme.IdealSheafData.vanishingIdeal Z).subscheme),
      _root_.IsReduced
        ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme.presheaf.stalk y) := by
    intro y
    refine isReduced_stalk_of_radical_consolidated46 _ ?_ y
    intro U
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  exact isReduced_of_isReduced_stalk _

theorem comap_subschemeι_self {X : Scheme.{u}} (I : X.IdealSheafData) :
    I.comap I.subschemeι = ⊥ := by
  refine le_antisymm ?_ bot_le
  have h := comap_map_le (⊥ : I.subscheme.IdealSheafData) I.subschemeι
  rwa [map_bot, ker_subschemeι] at h

end AlgebraicGeometry.Scheme.IdealSheafData

namespace FunctorialResolution.Blowup

theorem noetherianSpace_subscheme {X : Scheme.{u}} (I : X.IdealSheafData)
    [TopologicalSpace.NoetherianSpace ↥X] :
    TopologicalSpace.NoetherianSpace ↥I.subscheme :=
  (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding
    I.subschemeι).toIsEmbedding.toIsInducing.noetherianSpace

instance instNoetherianSpaceSubscheme {X : Scheme.{u}} (I : X.IdealSheafData)
    [TopologicalSpace.NoetherianSpace ↥X] :
    TopologicalSpace.NoetherianSpace ↥I.subscheme :=
  noetherianSpace_subscheme I

section
variable (X : Scheme.{u})

theorem idealSheafData_prod_nil :
    ([] : List X.IdealSheafData).prod = ⊤ := by
  rw [List.prod_nil]
  rfl

theorem idealSheafData_prod_cons (D : X.IdealSheafData)
    (E : List X.IdealSheafData) : (D :: E).prod = D * E.prod :=
  List.prod_cons


end

theorem comap_ker_comp_of_isOpenImmersion {A B C : Scheme.{u}} (j : A ⟶ B) (f : B ⟶ C)
    [IsOpenImmersion f] [QuasiCompact j] [QuasiCompact (j ≫ f)] :
    (j ≫ f).ker.comap f = j.ker := by
  refine Scheme.IdealSheafData.ext ?_
  funext V
  have hU : IsAffineOpen (f ''ᵁ V.1) := V.2.image_of_isOpenImmersion f
  have hpre : f ⁻¹ᵁ (f ''ᵁ V.1) = V.1 := f.preimage_image_eq V.1
  have e : (V : B.Opens) ≤ f ⁻¹ᵁ (f ''ᵁ V.1) := hpre.ge
  have hopeq : j ⁻¹ᵁ V.1 = (j ≫ f) ⁻¹ᵁ (f ''ᵁ V.1) := by
    show j ⁻¹ᵁ V.1 = j ⁻¹ᵁ (f ⁻¹ᵁ (f ''ᵁ V.1))
    rw [hpre]
  have hop : j ⁻¹ᵁ V.1 ≤ (j ≫ f) ⁻¹ᵁ (f ''ᵁ V.1) := hopeq.le
  have key : f.appLE (f ''ᵁ V.1) V.1 e ≫ j.app V.1
      = (j ≫ f).app (f ''ᵁ V.1) ≫ A.presheaf.map (homOfLE hop).op := by
    rw [Scheme.Hom.app_eq_appLE j]
    exact Scheme.Hom.appLE_comp_appLE j f (f ''ᵁ V.1) V.1 (j ⁻¹ᵁ V.1) e le_rfl
  have keyr : ∀ x, (CommRingCat.Hom.hom (j.app V.1))
        ((CommRingCat.Hom.hom (f.appLE (f ''ᵁ V.1) V.1 e)) x)
      = (CommRingCat.Hom.hom (A.presheaf.map (homOfLE hop).op))
        ((CommRingCat.Hom.hom ((j ≫ f).app (f ''ᵁ V.1))) x) := by
    intro x
    have h' := congrArg (fun m => (CommRingCat.Hom.hom m) x) key
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h'
  have hρ : ∀ y, (CommRingCat.Hom.hom (A.presheaf.map (homOfLE hop).op)) y = 0 → y = 0 := by
    intro y hy
    have hcomp : A.presheaf.map (homOfLE hop).op ≫ A.presheaf.map (homOfLE hopeq.ge).op
        = 𝟙 (A.presheaf.obj (Opposite.op ((j ≫ f) ⁻¹ᵁ (f ''ᵁ V.1)))) := by
      rw [← CategoryTheory.Functor.map_comp, ← op_comp,
        Subsingleton.elim (homOfLE hopeq.ge ≫ homOfLE hop) (𝟙 _), op_id,
        CategoryTheory.Functor.map_id]
    have h2 := congrArg (fun m => (CommRingCat.Hom.hom m) y) hcomp
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply,
      hy, map_zero] at h2
    exact h2.symm
  have hφ : Function.Surjective (CommRingCat.Hom.hom (f.appLE (f ''ᵁ V.1) V.1 e)) := by
    have : IsIso (f.appLE (f ''ᵁ V.1) V.1 e) := by
      rw [← Scheme.Hom.appIso_hom' f V.1]
      infer_instance
    intro y
    refine ⟨(CommRingCat.Hom.hom (inv (f.appLE (f ''ᵁ V.1) V.1 e))) y, ?_⟩
    have h3 := congrArg (fun m => (CommRingCat.Hom.hom m) y)
      (IsIso.inv_hom_id (f.appLE (f ''ᵁ V.1) V.1 e))
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] using h3
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ f ⟨f ''ᵁ V.1, hU⟩ V e,
    Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
  dsimp only
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, keyr x]
    rw [RingHom.mem_ker] at hx
    rw [hx, map_zero]
  · intro y hy
    obtain ⟨x, rfl⟩ := hφ y
    apply Ideal.mem_map_of_mem
    rw [RingHom.mem_ker] at hy ⊢
    exact hρ _ ((keyr x).symm.trans hy)

end FunctorialResolution.Blowup

namespace AlgebraicGeometry.Scheme.IdealSheafData

theorem exists_iso_subscheme_comap_of_isIso {Y Y' : Scheme.{u}} (g : Y ⟶ Y') [IsIso g]
    (I : Y'.IdealSheafData) :
    ∃ m : (I.comap g).subscheme ⟶ I.subscheme,
      IsIso m ∧ m ≫ I.subschemeι = (I.comap g).subschemeι ≫ g := by
  have : QuasiCompact (I.comap g).subschemeι := inferInstance
  have : QuasiCompact ((I.comap g).subschemeι ≫ g) := inferInstance
  have hq := FunctorialResolution.Blowup.comap_ker_comp_of_isOpenImmersion (I.comap g).subschemeι g
  rw [Scheme.IdealSheafData.ker_subschemeι] at hq
  have e1 : ∀ J : Y'.IdealSheafData, (J.comap g).comap (inv g) = J := by
    intro J
    rw [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  have hkk : ((I.comap g).subschemeι ≫ g).ker = I.subschemeι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι,
      ← e1 (((I.comap g).subschemeι ≫ g).ker), hq, e1]
  refine ⟨IsClosedImmersion.lift I.subschemeι ((I.comap g).subschemeι ≫ g)
      (le_of_eq hkk.symm), ?_, IsClosedImmersion.lift_fac _ _ _⟩
  exact IsClosedImmersion.isIso_of_ker_eq ((I.comap g).subschemeι ≫ g) I.subschemeι _
    (IsClosedImmersion.lift_fac _ _ _) hkk

end AlgebraicGeometry.Scheme.IdealSheafData
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.AffineSpaceJacobson
section

open AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem jacobsonSpace_affineSpace (k : Type u) [Field k] (n : Type u) [Finite n] :
    JacobsonSpace (AffineSpace n (Spec (CommRingCat.of k))) :=
  JacobsonSpace.of_isClosedEmbedding
    (Scheme.homeoOfIso (AffineSpace.SpecIso n (CommRingCat.of k))).isClosedEmbedding

instance instJacobsonSpaceAffineSpace (k : Type u) [Field k] (n : Type u) [Finite n] :
    JacobsonSpace (AffineSpace n (Spec (CommRingCat.of k))) :=
  jacobsonSpace_affineSpace k n

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.ClopenSubscheme
section
open CategoryTheory AlgebraicGeometry TopologicalSpace


namespace AlgebraicGeometry.Scheme.Opens

theorem isClosedImmersion_ι_of_isClosed {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClosed (U : Set X)) : IsClosedImmersion U.ι :=
  IsClosedImmersion.of_isPreimmersion U.ι (by rw [U.range_ι]; exact hU)

end AlgebraicGeometry.Scheme.Opens

namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Scheme} [IsReduced X] (C : X.Opens)

private theorem exists_iso_subscheme_vanishingIdeal_of_coe_eq_consolidated21 (Z : Closeds X) (hZ : (Z : Set X) = (C : Set X)) :
    ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ C.toScheme,
      e.hom ≫ C.ι = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := by
  have hCclosed : IsClosed (C : Set X) := by rw [← hZ]; exact Z.2
  have : IsClosedImmersion C.ι :=
    IsClosedImmersion.of_isPreimmersion C.ι (by rw [C.range_ι]; exact hCclosed)
  have hkersupp : ((Scheme.Hom.ker C.ι).support : Set X) = (Z : Set X) := by
    rw [Scheme.Hom.support_ker, C.range_ι, hCclosed.closure_eq]
    exact hZ.symm
  have hZsupp : (Scheme.Hom.ker C.ι).support = Z := TopologicalSpace.Closeds.ext hkersupp
  have hvan : Scheme.IdealSheafData.vanishingIdeal Z = (Scheme.Hom.ker C.ι).radical := by
    rw [← hZsupp]
    exact Scheme.IdealSheafData.vanishingIdeal_support
  have hsupp : (Scheme.IdealSheafData.vanishingIdeal Z).support = Z := by
    rw [hvan, Scheme.IdealSheafData.support_radical]
    exact hZsupp
  have hrange :
      Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = (C : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, hsupp]
    exact hZ
  have hle : Scheme.Hom.ker C.ι ≤
      Scheme.Hom.ker (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hvan]
    exact Scheme.IdealSheafData.le_radical _
  let φ : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ C.toScheme :=
    IsClosedImmersion.lift C.ι (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι hle
  have hφ : φ ≫ C.ι = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι :=
    IsClosedImmersion.lift_fac _ _ hle
  have hφbase : ∀ x, ⇑C.ι (⇑φ x) =
      ⇑(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι x := by
    intro x
    rw [← hφ]
    simp
  have hinj : Function.Injective ⇑C.ι := C.ι.isOpenEmbedding.injective
  have hsurj : Function.Surjective ⇑φ := by
    intro y
    have hy : ⇑C.ι y ∈ Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := by
      rw [hrange, ← C.range_ι]
      exact Set.mem_range_self y
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, hinj ?_⟩
    rw [hφbase x]
    exact hx
  have : IsPreimmersion (φ ≫ C.ι) := by rw [hφ]; infer_instance
  have : IsPreimmersion φ := IsPreimmersion.of_comp φ C.ι
  have : IsClosedImmersion φ :=
    IsClosedImmersion.of_isPreimmersion φ (by rw [hsurj.range_eq]; exact isClosed_univ)
  have hker : Scheme.Hom.ker φ = ⊥ := by
    rw [← Scheme.IdealSheafData.support_eq_top_iff]
    refine TopologicalSpace.Closeds.ext ?_
    rw [Scheme.Hom.support_ker, hsurj.range_eq, closure_univ]
    simp
  have : IsIso φ := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  exact ⟨asIso φ, hφ⟩

theorem exists_iso_subscheme_vanishingIdeal_of_isClosed
    (hC : IsClosed (C : Set X)) :
    ∃ e : (Scheme.IdealSheafData.vanishingIdeal
        (⟨(C : Set X), hC⟩ : TopologicalSpace.Closeds X)).subscheme ≅ C.toScheme,
      e.hom ≫ C.ι =
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨(C : Set X), hC⟩ : TopologicalSpace.Closeds X)).subschemeι :=
  exists_iso_subscheme_vanishingIdeal_of_coe_eq_consolidated21 C _ rfl


end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.CoproductBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


namespace FunctorialResolution.EmbeddedResolution

section
variable {ι : Type u} [Finite ι]

private theorem isIso_sigmaDesc_of_isPullback_consolidated23 {P : Scheme.{u}}
    (B C : ι → Scheme.{u}) (f : P ⟶ ∐ B) (j : ∀ a, C a ⟶ B a) (u : ∀ a, C a ⟶ P)
    (hsq : ∀ a, IsPullback (u a) (j a) f (Sigma.ι B a)) : IsIso (Sigma.desc u) := by
  have e1 : (Discrete.natTrans (F := Discrete.functor C) (G := Discrete.functor B)
        fun a => j a.as) ≫ (colimit.cocone (Discrete.functor B)).ι
      = (Cofan.mk P u).ι ≫ (Functor.const (Discrete ι)).map f := by
    apply NatTrans.ext
    funext x
    obtain ⟨a⟩ := x
    exact ((hsq a).w).symm
  have hpb : ∀ x : Discrete ι, IsPullback ((Cofan.mk P u).ι.app x)
      ((Discrete.natTrans (F := Discrete.functor C) (G := Discrete.functor B)
        fun a => j a.as).app x) f ((colimit.cocone (Discrete.functor B)).ι.app x) := by
    rintro ⟨a⟩
    exact hsq a
  obtain ⟨hc'⟩ := FinitaryPreExtensive.isUniversal_finiteCoproducts
      (colimit.isColimit (Discrete.functor B)) (Cofan.mk P u)
      (Discrete.natTrans (F := Discrete.functor C) (G := Discrete.functor B) fun a => j a.as)
      f e1 (NatTrans.Equifibered.of_discrete _) hpb
  have key : Sigma.desc u
      = (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (Discrete.functor C)) hc').hom := by
    apply Sigma.hom_ext
    intro a
    rw [Sigma.ι_desc]
    exact (IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (Discrete.functor C)) hc' ⟨a⟩).symm
  rw [key]
  infer_instance

theorem isPullback_sigmaMap_sigmaDesc {A Y : Scheme.{u}} (i : Y ⟶ A)
    (B C : ι → Scheme.{u}) (j : ∀ a, C a ⟶ B a) (q : ∀ a, C a ⟶ Y) (h : ∀ a, B a ⟶ A)
    (hsq : ∀ a, IsPullback (j a) (q a) (h a) i) :
    IsPullback (Limits.Sigma.map j) (Limits.Sigma.desc q) (Limits.Sigma.desc h) i := by
  have hcomm : ∀ a, (j a ≫ Sigma.ι B a) ≫ Sigma.desc h = q a ≫ i := by
    intro a
    rw [Category.assoc, Sigma.ι_desc]
    exact (hsq a).w
  obtain ⟨u, hufst, husnd⟩ : ∃ u : ∀ a, C a ⟶ pullback (Sigma.desc h) i,
      (∀ a, u a ≫ pullback.fst (Sigma.desc h) i = j a ≫ Sigma.ι B a) ∧
        (∀ a, u a ≫ pullback.snd (Sigma.desc h) i = q a) :=
    ⟨fun a => pullback.lift (j a ≫ Sigma.ι B a) (q a) (hcomm a),
      fun a => pullback.lift_fst _ _ _, fun a => pullback.lift_snd _ _ _⟩
  have hP : IsPullback (pullback.fst (Sigma.desc h) i) (pullback.snd (Sigma.desc h) i)
      (Sigma.desc h) i := IsPullback.of_hasPullback _ _
  have hsq2 : ∀ a, IsPullback (j a) (u a) (Sigma.ι B a) (pullback.fst (Sigma.desc h) i) := by
    intro a
    refine IsPullback.of_bot ?_ (hufst a).symm hP
    rw [husnd a, Sigma.ι_desc]
    exact hsq a
  have : IsIso (Sigma.desc u) :=
    isIso_sigmaDesc_of_isPullback_consolidated23 B C (pullback.fst (Sigma.desc h) i) j u
      (fun a => (hsq2 a).flip)
  have hcs : CommSq (Limits.Sigma.map j) (Sigma.desc q) (Sigma.desc h) i := by
    constructor
    apply Sigma.hom_ext
    intro a
    simp [(hsq a).w]
  refine IsPullback.of_iso_pullback hcs (asIso (Sigma.desc u)) ?_ ?_
  · apply Sigma.hom_ext
    intro a
    simp [hufst a]
  · apply Sigma.hom_ext
    intro a
    simp [husnd a]


end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DerivationLocalization
section

variable {R : Type u} {S : Type v} {S' : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [CommRing S'] [AddCommGroup N]
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [Module R N] [Module S N] [Module S' N]
variable [IsScalarTower R S N] [IsScalarTower S S' N] [IsScalarTower R S' N]

namespace Derivation

private theorem isUnit_algebraMap_moduleEnd_consolidated10 (M : Submonoid S) [IsLocalization M S'] (y : M) :
    IsUnit ((algebraMap S (Module.End S N)) (y : S)) := by
  obtain ⟨u, hu⟩ := IsLocalization.map_units (M := M) S' y
  have hcomm : ∀ (s : S) (c : S') (n : N), c • s • n = s • c • n := by
    intro s c n
    rw [← IsScalarTower.algebraMap_smul S' s n, ← IsScalarTower.algebraMap_smul S' s (c • n),
      smul_smul, smul_smul, mul_comm]
  have h1 : ∀ n : N, (y : S) • (((u⁻¹ : S'ˣ) : S') • n) = n := by
    intro n
    rw [← IsScalarTower.algebraMap_smul S' (y : S) (((u⁻¹ : S'ˣ) : S') • n), ← hu, smul_smul,
      u.mul_inv, one_smul]
  have h2 : ∀ n : N, ((u⁻¹ : S'ˣ) : S') • ((y : S) • n) = n := by
    intro n
    rw [← IsScalarTower.algebraMap_smul S' (y : S) n, ← hu, smul_smul, u.inv_mul, one_smul]
  exact ⟨⟨(algebraMap S (Module.End S N)) (y : S),
    { toFun := fun n => ((u⁻¹ : S'ˣ) : S') • n
      map_add' := fun a b => smul_add _ _ _
      map_smul' := fun s n => hcomm s ((u⁻¹ : S'ˣ) : S') n },
    LinearMap.ext fun n => h1 n, LinearMap.ext fun n => h2 n⟩, rfl⟩

private theorem exists_liftToLocalization_consolidated10 (D : Derivation R S N) (M : Submonoid S)
    [IsLocalization M S'] :
    ∃ D' : Derivation R S' N, ∀ s : S, D' (algebraMap S S' s) = D s := by
  have hu : ∀ y : M, IsUnit ((algebraMap S (Module.End S N)) (y : S)) := fun y =>
    isUnit_algebraMap_moduleEnd_consolidated10 (S' := S') M y
  have : IsLocalizedModule M (KaehlerDifferential.map R R S S') := inferInstance
  refine ⟨(LinearMap.extendScalarsOfIsLocalization M S'
      (IsLocalizedModule.lift M (KaehlerDifferential.map R R S S')
        D.liftKaehlerDifferential hu)).compDer (KaehlerDifferential.D R S'), fun s => ?_⟩
  show IsLocalizedModule.lift M (KaehlerDifferential.map R R S S') D.liftKaehlerDifferential hu
      (KaehlerDifferential.D R S' (algebraMap S S' s)) = D s
  have key : IsLocalizedModule.lift M (KaehlerDifferential.map R R S S')
        D.liftKaehlerDifferential hu
        (KaehlerDifferential.map R R S S' (KaehlerDifferential.D R S s))
      = D.liftKaehlerDifferential (KaehlerDifferential.D R S s) :=
    LinearMap.congr_fun
      (IsLocalizedModule.lift_comp M (KaehlerDifferential.map R R S S')
        D.liftKaehlerDifferential hu) (KaehlerDifferential.D R S s)
  rw [← KaehlerDifferential.map_D R R S S' s, key]
  exact D.liftKaehlerDifferential_comp_D s

private theorem exists_mapToLocalization_consolidated10 (D : Derivation R S S) (M : Submonoid S)
    [IsLocalization M S'] :
    ∃ D' : Derivation R S' S', ∀ s : S,
      D' (algebraMap S S' s) = algebraMap S S' (D s) := by
  obtain ⟨D', hD'⟩ :=
    exists_liftToLocalization_consolidated10 (S' := S') (N := S') ((Algebra.linearMap S S').compDer D) M
  exact ⟨D', fun s => hD' s⟩

noncomputable def mapToLocalization (D : Derivation R S S) (M : Submonoid S)
    [IsLocalization M S'] : Derivation R S' S' :=
  (exists_mapToLocalization_consolidated10 (S' := S') D M).choose

@[simp]
theorem mapToLocalization_algebraMap (D : Derivation R S S) (M : Submonoid S)
    [IsLocalization M S'] (s : S) :
    (D.mapToLocalization (S' := S') M) (algebraMap S S' s) = algebraMap S S' (D s) :=
  (exists_mapToLocalization_consolidated10 (S' := S') D M).choose_spec s

section
variable (M : Submonoid S) [IsLocalization M S'] [Module.FinitePresentation S (KaehlerDifferential R S)]

theorem exists_derivation_mul_eq (D : Derivation R S S') :
    ∃ (m : M) (D₀ : Derivation R S S), ∀ s : S,
      algebraMap S S' (m : S) * D s = algebraMap S S' (D₀ s) := by
  obtain ⟨ψ, m, hψ⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    M (Algebra.linearMap S S') D.liftKaehlerDifferential
  refine ⟨m, LinearMap.compDer ψ (KaehlerDifferential.D R S), fun s => ?_⟩
  have h1 : algebraMap S S' (ψ (KaehlerDifferential.D R S s))
      = (m : S) • D.liftKaehlerDifferential (KaehlerDifferential.D R S s) :=
    LinearMap.congr_fun hψ (KaehlerDifferential.D R S s)
  rw [Derivation.liftKaehlerDifferential_comp_D, Algebra.smul_def] at h1
  exact h1.symm

theorem exists_derivation_mul_eq_of_isLocalization (D : Derivation R S' S') :
    ∃ (m : M) (D₀ : Derivation R S S), ∀ s : S,
      algebraMap S S' (m : S) * D (algebraMap S S' s) = algebraMap S S' (D₀ s) := by
  obtain ⟨m, D₀, h⟩ := exists_derivation_mul_eq (S' := S') M (D.compAlgebraMap S)
  exact ⟨m, D₀, fun s => h s⟩


end

end Derivation
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
section
namespace IsOpenMap

theorem mem_closure_singleton_of_apply {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} (hopen : IsOpenMap f) (hinj : Function.Injective f)
    {a b : A} (h : f b ∈ closure ({f a} : Set B)) : b ∈ closure ({a} : Set A) := by
  rw [mem_closure_iff]
  intro O hO hbO
  obtain ⟨y, hymem, hy⟩ := (mem_closure_iff.mp h) (f '' O) (hopen O hO) ⟨b, hbO, rfl⟩
  obtain ⟨z, hzO, hz⟩ := hymem
  rw [Set.mem_singleton_iff] at hy
  have hza : z = a := hinj (hz.trans hy)
  subst hza
  exact ⟨z, hzO, rfl⟩

end IsOpenMap

namespace FunctorialResolution.EmbeddedResolution

section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

section
variable {S U : Set X}

theorem isIrreducible_inter_open (hS : IsIrreducible S) (hU : IsOpen U)
    (hne : (S ∩ U).Nonempty) : IsIrreducible (S ∩ U) := by
  refine ⟨hne, ?_⟩
  rintro u v hu hv ⟨a, ⟨haS, haU⟩, hau⟩ ⟨b, ⟨hbS, hbU⟩, hbv⟩
  obtain ⟨c, hcS, hc⟩ := hS.2 (U ∩ u) (U ∩ v) (hU.inter hu) (hU.inter hv)
    ⟨a, haS, haU, hau⟩ ⟨b, hbS, hbU, hbv⟩
  exact ⟨c, ⟨hcS, hc.1.1⟩, hc.1.2, hc.2.2⟩

theorem closure_inter_open_eq (hS : IsClosed S) (hirr : IsIrreducible S)
    (hU : IsOpen U) (hne : (S ∩ U).Nonempty) : closure (S ∩ U) = S := by
  apply Set.Subset.antisymm
  · exact hS.closure_subset_iff.mpr Set.inter_subset_left
  · intro x hx
    rw [mem_closure_iff]
    intro o ho hxo
    obtain ⟨c, hcS, hc⟩ := hirr.2 o U ho hU ⟨x, hx, hxo⟩ hne
    exact ⟨c, hc.1, hcS, hc.2⟩


end

section
variable {f : Y → X}

theorem isIrreducible_preimage_of_isEmbedding (hf : Topology.IsEmbedding f)
    {T : Set X} (hT : IsIrreducible T) (hTr : T ⊆ Set.range f) :
    IsIrreducible (f ⁻¹' T) := by
  obtain ⟨t, ht⟩ := hT.1
  obtain ⟨y, rfl⟩ := hTr ht
  refine ⟨⟨y, ht⟩, ?_⟩
  rintro u v hu hv ⟨a, haT, hau⟩ ⟨b, hbT, hbv⟩
  obtain ⟨u', hu', rfl⟩ := hf.toIsInducing.isOpen_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := hf.toIsInducing.isOpen_iff.mp hv
  obtain ⟨c, hcT, hcu, hcv⟩ := hT.2 u' v' hu' hv' ⟨f a, haT, hau⟩ ⟨f b, hbT, hbv⟩
  obtain ⟨z, rfl⟩ := hTr hcT
  exact ⟨z, hcT, hcu, hcv⟩

theorem isGenericPoint_preimage_of_isInducing (hf : Topology.IsInducing f)
    {ξ : X} {T : Set X} (h : IsGenericPoint ξ T) {y : Y} (hy : f y = ξ) :
    IsGenericPoint y (f ⁻¹' T) := by
  have h2 : closure ({y} : Set Y) = f ⁻¹' closure (f '' ({y} : Set Y)) :=
    hf.closure_eq_preimage_closure_image _
  rw [Set.image_singleton, hy, IsGenericPoint.def h] at h2
  exact h2

theorem isGenericPoint_image_of_isClosedEmbedding (hf : Topology.IsClosedEmbedding f) {y : Y} {T : Set Y} (h : IsGenericPoint y T) :
    IsGenericPoint (f y) (f '' T) := by
  have hyT : y ∈ T := IsGenericPoint.mem h
  show closure ({f y} : Set X) = f '' T
  apply Set.Subset.antisymm
  · have hcl : IsClosed (f '' T) := by
      rw [← IsGenericPoint.def h]
      exact hf.isClosedMap _ isClosed_closure
    exact hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨y, hyT, rfl⟩)
  · have h2 : f '' closure ({y} : Set Y) ⊆ closure (f '' ({y} : Set Y)) :=
      image_closure_subset_closure_image hf.continuous
    rw [Set.image_singleton] at h2
    rw [← IsGenericPoint.def h]
    exact h2


end

theorem closure_image_genericPoint {f : X → Y} (hcont : Continuous f) {S : Set X} {ξ : X}
    (hξ : IsGenericPoint ξ S) : closure (f '' S) = closure ({f ξ} : Set Y) := by
  refine Set.Subset.antisymm ?_ ?_
  · refine closure_minimal ?_ isClosed_closure
    have hsub := image_closure_subset_closure_image (f := f) (s := ({ξ} : Set X)) hcont
    rw [Set.image_singleton] at hsub
    rw [← hξ]
    exact hsub
  · refine closure_mono ?_
    refine Set.singleton_subset_iff.2 ⟨ξ, ?_, rfl⟩
    rw [← hξ]
    exact subset_closure rfl

theorem isOpen_sUnion_of_irreducibleComponents {Z : Type*} [TopologicalSpace Z]
    [TopologicalSpace.NoetherianSpace Z] (C : Set (Set Z))
    (hdisj : ∀ S ∈ C, ∀ W ∈ irreducibleComponents Z, W ∉ C → Disjoint S W) :
    IsOpen (⋃₀ C) := by
  have hcomp : (irreducibleComponents Z).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hfin : (irreducibleComponents Z \ C).Finite := hcomp.subset Set.sdiff_subset
  have hclosed : IsClosed (⋃₀ (irreducibleComponents Z \ C)) := by
    rw [Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion fun i hi => isClosed_of_mem_irreducibleComponents i hi.1
  have heq : ⋃₀ C = (⋃₀ (irreducibleComponents Z \ C))ᶜ := by
    apply Set.Subset.antisymm
    · rintro x ⟨S, hSmem, hxS⟩
      have hx : x ∉ ⋃₀ (irreducibleComponents Z \ C) := by
        rintro ⟨W, ⟨hW, hWC⟩, hxW⟩
        exact Set.disjoint_left.mp (hdisj S hSmem W hW hWC) hxS hxW
      exact hx
    · intro x hx
      rw [Set.mem_compl_iff] at hx
      by_cases hmem : irreducibleComponent x ∈ C
      · exact Set.mem_sUnion_of_mem mem_irreducibleComponent hmem
      · exact absurd (Set.mem_sUnion_of_mem mem_irreducibleComponent
          (Set.mem_sdiff_of_mem (irreducibleComponent_mem_irreducibleComponents x) hmem)) hx
  rw [heq]
  exact hclosed.isOpen_compl

end

section

open AlgebraicGeometry

theorem support_comap_eq {X Y : Scheme} (f : X ⟶ Y) (I : Y.IdealSheafData) :
    ((I.comap f).support : Set X) = f.base ⁻¹' (I.support : Set Y) :=
  congrArg (fun s : TopologicalSpace.Closeds X => (s : Set X))
    (Scheme.IdealSheafData.support_comap I f)

theorem comap_ι_eq_top_of_disjoint {X : Scheme} (I : X.IdealSheafData) (U : X.Opens)
    (h : Disjoint (U : Set X) (I.support : Set X)) : I.comap U.ι = ⊤ := by
  have hempty : ((I.comap U.ι).support : Set U) = ∅ := by
    rw [support_comap_eq]
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    have hxU : U.ι.base x ∈ (U : Set X) := by
      rw [← Scheme.Opens.range_ι]
      exact ⟨x, rfl⟩
    exact Set.disjoint_left.mp h hxU hx
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  exact SetLike.ext' hempty

end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.IrreducibleComponents
section
namespace FunctorialResolution.EmbeddedResolution

open Set TopologicalSpace

section
variable {X : Type*} [TopologicalSpace X] [NoetherianSpace X]

theorem isClosed_sUnion_of_subset_irreducibleComponents {𝒜 : Set (Set X)} (h𝒜 : ∀ C ∈ 𝒜, C ∈ irreducibleComponents X) :
    IsClosed (⋃₀ 𝒜) := by
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents ..
  have hsub : 𝒜 ⊆ irreducibleComponents X := fun C hC => h𝒜 C hC
  rw [Set.sUnion_eq_biUnion]
  exact (hfin.subset hsub).isClosed_biUnion
    (fun C hC => isClosed_of_mem_irreducibleComponents _ (h𝒜 C hC))

theorem isOpen_sUnion_of_subset_irreducibleComponents (hsep : ∀ C₁ ∈ irreducibleComponents X, ∀ C₂ ∈ irreducibleComponents X,
      (C₁ ∩ C₂).Nonempty → C₁ = C₂)
    {𝒜 : Set (Set X)} (h𝒜 : ∀ C ∈ 𝒜, C ∈ irreducibleComponents X) :
    IsOpen (⋃₀ 𝒜) := by
  have key : (⋃₀ 𝒜)ᶜ = ⋃₀ (irreducibleComponents X \ 𝒜) := by
    apply Set.Subset.antisymm
    · intro y hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents .., ?_⟩,
        mem_irreducibleComponent ..⟩
      intro hmem
      exact hy ⟨irreducibleComponent y, hmem, mem_irreducibleComponent ..⟩
    · intro y hyc
      obtain ⟨C, ⟨hC, hCA⟩, hyC⟩ := hyc
      show y ∉ ⋃₀ 𝒜
      intro hy
      obtain ⟨D, hD, hyD⟩ := hy
      have heq : C = D := hsep C hC D (h𝒜 D hD) ⟨y, hyC, hyD⟩
      rw [heq] at hCA
      exact hCA hD
  rw [← isClosed_compl_iff, key]
  exact isClosed_sUnion_of_subset_irreducibleComponents (fun C hC => hC.1)


end

theorem irreducibleComponents_eq_of_stalk_isDomain (X : AlgebraicGeometry.Scheme)
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) {C₁ C₂ : Set X}
    (h₁ : C₁ ∈ irreducibleComponents X) (h₂ : C₂ ∈ irreducibleComponents X)
    {x : X} (hx₁ : x ∈ C₁) (hx₂ : x ∈ C₂) : C₁ = C₂ := by
  have := hX x
  obtain ⟨ξ₁, hg₁⟩ := QuasiSober.sober h₁.1 (isClosed_of_mem_irreducibleComponents _ h₁)
  obtain ⟨ξ₂, hg₂⟩ := QuasiSober.sober h₂.1 (isClosed_of_mem_irreducibleComponents _ h₂)
  have hξ₁ : closure {ξ₁} = C₁ := hg₁
  have hξ₂ : closure {ξ₂} = C₂ := hg₂
  have hrange : Set.range (X.fromSpecStalk x).base = {y | y ⤳ x} :=
    AlgebraicGeometry.Scheme.range_fromSpecStalk ..
  have hm₁ : ξ₁ ∈ Set.range (X.fromSpecStalk x).base := by
    rw [hrange]
    exact specializes_iff_mem_closure.mpr (by rw [hξ₁]; exact hx₁)
  have hm₂ : ξ₂ ∈ Set.range (X.fromSpecStalk x).base := by
    rw [hrange]
    exact specializes_iff_mem_closure.mpr (by rw [hξ₂]; exact hx₂)
  have hcont : Continuous (X.fromSpecStalk x).base := (X.fromSpecStalk x).continuous
  have hirrU : IsIrreducible (Set.univ : Set (PrimeSpectrum (X.presheaf.stalk x))) :=
    IrreducibleSpace.isIrreducible_univ ..
  have himg : IsIrreducible (Set.range (X.fromSpecStalk x).base) := by
    rw [← Set.image_univ]
    exact hirrU.image _ hcont.continuousOn
  have hcl : IsIrreducible (closure (Set.range (X.fromSpecStalk x).base)) := himg.closure
  have hs₁ : C₁ ⊆ closure (Set.range (X.fromSpecStalk x).base) := by
    rw [← hξ₁]
    exact closure_mono (Set.singleton_subset_iff.mpr hm₁)
  have hs₂ : C₂ ⊆ closure (Set.range (X.fromSpecStalk x).base) := by
    rw [← hξ₂]
    exact closure_mono (Set.singleton_subset_iff.mpr hm₂)
  have e₁ : closure (Set.range (X.fromSpecStalk x).base) ⊆ C₁ := h₁.2 hcl hs₁
  have e₂ : closure (Set.range (X.fromSpecStalk x).base) ⊆ C₂ := h₂.2 hcl hs₂
  exact Set.Subset.antisymm (hs₁.trans e₂) (hs₂.trans e₁)

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelSupport
section
namespace FunctorialResolution.EmbeddedResolution

open CategoryTheory AlgebraicGeometry

theorem support_ker_comp_subset_support_ker {T S Y : Scheme}
    (g : T ⟶ S) (f : S ⟶ Y) :
    ((g ≫ f).ker.support : Set Y) ⊆ (f.ker.support : Set Y) := by
  intro x hx
  exact Scheme.IdealSheafData.support_antitone (Scheme.Hom.le_ker_comp g f) hx

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.OpenImmersionAppLE
section
namespace AlgebraicGeometry

open CategoryTheory


namespace IsOpenImmersion

theorem bijective_appLE_of_image_eq {A B : Scheme.{u}} (f : A ⟶ B) [IsOpenImmersion f]
    (O : B.Opens) (S : A.Opens) (e : S ≤ f ⁻¹ᵁ O) (h : f ''ᵁ S = O) :
    Function.Bijective (CommRingCat.Hom.hom (Scheme.Hom.appLE f O S e)) := by
  subst h
  have : IsIso (Scheme.Hom.appLE f (f ''ᵁ S) S e) := by
    rw [← Scheme.Hom.appIso_hom' f S]
    infer_instance
  constructor
  · intro a b hab
    have h1 : (CommRingCat.Hom.hom (Scheme.Hom.appLE f (f ''ᵁ S) S e ≫
          inv (Scheme.Hom.appLE f (f ''ᵁ S) S e))) a
        = (CommRingCat.Hom.hom (Scheme.Hom.appLE f (f ''ᵁ S) S e ≫
          inv (Scheme.Hom.appLE f (f ''ᵁ S) S e))) b := by
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, hab]
    rw [IsIso.hom_inv_id] at h1
    simpa only [CommRingCat.hom_id, RingHom.id_apply] using h1
  · intro y
    refine ⟨(CommRingCat.Hom.hom (inv (Scheme.Hom.appLE f (f ''ᵁ S) S e))) y, ?_⟩
    have h3 := congrArg (fun mm => (CommRingCat.Hom.hom mm) y)
      (IsIso.inv_hom_id (Scheme.Hom.appLE f (f ''ᵁ S) S e))
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] using h3

end IsOpenImmersion

end AlgebraicGeometry
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.ReducedSubscheme
section
open CategoryTheory

namespace FunctorialResolution.EmbeddedResolution

private theorem isReduced_stalk_of_isAffineOpen_consolidated19 {Z : AlgebraicGeometry.Scheme} {V : Z.Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V)
    (hred : _root_.IsReduced ↥(Z.presheaf.obj (Opposite.op V))) (x : V) :
    _root_.IsReduced ↥(Z.presheaf.stalk x.1) := by
  have := hV.isLocalization_stalk x
  exact isReduced_localizationPreserves (hV.primeIdealOf x).asIdeal.primeCompl
    ↥(Z.presheaf.stalk x.1) hred

section
variable {W X : AlgebraicGeometry.Scheme} (f : W ⟶ X) [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.QuasiCompact f]

private theorem isReduced_presheaf_obj_subscheme_ker_consolidated19 (U : X.affineOpens) :
    _root_.IsReduced ↥((AlgebraicGeometry.Scheme.Hom.ker f).subscheme.presheaf.obj
      (Opposite.op ((TopologicalSpace.Opens.map
        (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base).obj U.1))) := by
  have hid : (AlgebraicGeometry.Scheme.Hom.ker f).ideal U
      = RingHom.ker (AlgebraicGeometry.Scheme.Hom.app f U.1).hom := by
    simp
  have hq : _root_.IsReduced (↥(X.presheaf.obj (Opposite.op U.1)) ⧸
      (AlgebraicGeometry.Scheme.Hom.ker f).ideal U) := by
    rw [hid]
    exact isReduced_of_injective (RingHom.kerLift (AlgebraicGeometry.Scheme.Hom.app f U.1).hom)
      (RingHom.kerLift_injective _)
  have hq' : _root_.IsReduced ↥(CommRingCat.of (↥(X.presheaf.obj (Opposite.op U.1)) ⧸
      (AlgebraicGeometry.Scheme.Hom.ker f).ideal U)) := hq
  exact isReduced_of_injective
    ((AlgebraicGeometry.Scheme.IdealSheafData.subschemeObjIso
      (AlgebraicGeometry.Scheme.Hom.ker f) U).hom.hom)
    (AlgebraicGeometry.Scheme.IdealSheafData.subschemeObjIso
      (AlgebraicGeometry.Scheme.Hom.ker f) U).commRingCatIsoToRingEquiv.injective

private theorem isReduced_stalk_subscheme_ker_consolidated19 (y : (AlgebraicGeometry.Scheme.Hom.ker f).subscheme) :
    _root_.IsReduced ↥((AlgebraicGeometry.Scheme.Hom.ker f).subscheme.presheaf.stalk y) := by
  obtain ⟨U, hU, hyU⟩ : ∃ U : X.Opens, AlgebraicGeometry.IsAffineOpen U ∧
      (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base y ∈ U :=
    ⟨(X.affineCover.f (X.affineCover.idx _)).opensRange,
      AlgebraicGeometry.isAffineOpen_opensRange _, X.affineCover.covers _⟩
  have hVaff : AlgebraicGeometry.IsAffineOpen ((TopologicalSpace.Opens.map
      (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base).obj U) :=
    hU.preimage (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι
  have hyV : y ∈ (TopologicalSpace.Opens.map
      (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base).obj U := hyU
  have hred := isReduced_presheaf_obj_subscheme_ker_consolidated19 f ⟨U, hU⟩
  exact isReduced_stalk_of_isAffineOpen_consolidated19 hVaff hred ⟨y, hyV⟩

theorem isReduced_subscheme_ker :
    AlgebraicGeometry.IsReduced (AlgebraicGeometry.Scheme.Hom.ker f).subscheme := by
  have : ∀ y : (AlgebraicGeometry.Scheme.Hom.ker f).subscheme,
      _root_.IsReduced ↥((AlgebraicGeometry.Scheme.Hom.ker f).subscheme.presheaf.stalk y) :=
    fun y => isReduced_stalk_subscheme_ker_consolidated19 f y
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _


end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.SpanSingletonProduct
section
namespace FunctorialResolution.EmbeddedResolution

section
variable {R : Type*} [CommRing R]

private theorem prod_notMem_of_isPrime_consolidated15 {ι : Type*} [DecidableEq ι]
    {I : Ideal R} (hI : I.IsPrime) (g : ι → R) (t : Finset ι) :
    (∀ j ∈ t, g j ∉ I) → ∏ j ∈ t, g j ∉ I := by
  induction t using Finset.induction_on with
  | empty =>
      intro _ h1
      rw [Finset.prod_empty] at h1
      refine hI.ne_top ?_
      rw [Ideal.eq_top_iff_one]
      exact h1
  | @insert a u ha ih =>
      intro h hmem
      rw [Finset.prod_insert ha] at hmem
      rcases hI.mem_or_mem hmem with h1 | h1
      · exact h a (Finset.mem_insert_self a u) h1
      · exact ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) h1

private theorem span_singleton_mul_eq_inf_consolidated15 {a b : R}
    (hpa : (Ideal.span ({a} : Set R)).IsPrime) (hb : b ∉ Ideal.span ({a} : Set R)) :
    Ideal.span ({a * b} : Set R) = Ideal.span ({a} : Set R) ⊓ Ideal.span ({b} : Set R) := by
  refine le_antisymm (le_inf ?_ ?_) ?_
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_singleton.mpr ⟨b, rfl⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_singleton.mpr ⟨a, mul_comm a b⟩
  · intro z hz
    rw [Submodule.mem_inf] at hz
    obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton.mp hz2
    have hv : v ∈ Ideal.span ({a} : Set R) := (hpa.mem_or_mem hz1).resolve_left hb
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.mp hv
    exact Ideal.mem_span_singleton.mpr ⟨w, by ring⟩

theorem span_singleton_prod_eq_biInf {ι : Type*} [DecidableEq ι]
    (f : ι → R) (s : Finset ι)
    (hp : ∀ i ∈ s, (Ideal.span ({f i} : Set R)).IsPrime)
    (hdvd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f j ∉ Ideal.span ({f i} : Set R)) :
    Ideal.span ({∏ i ∈ s, f i} : Set R) = ⨅ i ∈ s, Ideal.span ({f i} : Set R) := by
  revert hp hdvd
  induction s using Finset.induction_on with
  | empty =>
      intro _ _
      simp
  | @insert a u ha ih =>
      intro hp hdvd
      have hpa : (Ideal.span ({f a} : Set R)).IsPrime := hp a (Finset.mem_insert_self a u)
      have hP : (∏ i ∈ u, f i) ∉ Ideal.span ({f a} : Set R) := by
        refine prod_notMem_of_isPrime_consolidated15 hpa f u ?_
        intro j hj
        exact hdvd a (Finset.mem_insert_self a u) j (Finset.mem_insert_of_mem hj)
          (by rintro rfl; exact ha hj)
      have ihu := ih (fun i hi => hp i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij =>
          hdvd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
      rw [Finset.prod_insert ha, span_singleton_mul_eq_inf_consolidated15 hpa hP, ihu, Finset.iInf_insert]

theorem isRadical_biInf_span_singleton {ι : Type*}
    (f : ι → R) (s : Finset ι)
    (hp : ∀ i ∈ s, (Ideal.span ({f i} : Set R)).IsPrime) :
    (⨅ i ∈ s, Ideal.span ({f i} : Set R)).IsRadical := by
  refine le_iInf fun i => le_iInf fun hi => ?_
  refine le_trans (Ideal.radical_mono ?_) (hp i hi).isRadical
  exact iInf_le_of_le i (iInf_le _ hi)

theorem isRadical_span_singleton_prod_finset {ι : Type*}
    [DecidableEq ι]
    (f : ι → R) (s : Finset ι)
    (hp : ∀ i ∈ s, (Ideal.span ({f i} : Set R)).IsPrime)
    (hdvd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f j ∉ Ideal.span ({f i} : Set R)) :
    (Ideal.span ({∏ i ∈ s, f i} : Set R)).IsRadical := by
  rw [span_singleton_prod_eq_biInf f s hp hdvd]
  exact isRadical_biInf_span_singleton f s hp


end

end FunctorialResolution.EmbeddedResolution

namespace IsLocalization

theorem map_eq_map_of_map_eq_map {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] (M : Submonoid R) [IsLocalization M S]
    [IsLocalization M T] {I J : Ideal R}
    (h : Ideal.map (algebraMap R S) I = Ideal.map (algebraMap R S) J) :
    Ideal.map (algebraMap R T) I = Ideal.map (algebraMap R T) J := by
  have he : ((IsLocalization.algEquiv M S T).toAlgHom.toRingHom).comp (algebraMap R S)
      = algebraMap R T :=
    RingHom.ext fun r => by
      show (IsLocalization.algEquiv M S T) (algebraMap R S r) = algebraMap R T r
      exact (IsLocalization.algEquiv M S T).commutes r
  have hmap : ∀ K : Ideal R, Ideal.map (algebraMap R T) K =
      Ideal.map ((IsLocalization.algEquiv M S T).toAlgHom.toRingHom)
        (Ideal.map (algebraMap R S) K) := by
    intro K
    rw [Ideal.map_map, he]
  rw [hmap, hmap, h]

end IsLocalization

namespace Ideal

theorem list_prod_le_getElem {R : Type*} [CommRing R] (L : List (Ideal R)) (i : ℕ)
    (hi : i < L.length) : L.prod ≤ (L[i]'hi) := by
  revert i hi
  induction L with
  | nil =>
      intro i hi
      simp at hi
  | cons A L ih =>
      intro i hi
      cases i with
      | zero =>
          simp only [List.prod_cons, List.getElem_cons_zero]
          exact le_trans Ideal.mul_le_inf inf_le_left
      | succ i' =>
          have hi' : i' < L.length := by simpa using hi
          simp only [List.prod_cons, List.getElem_cons_succ]
          exact le_trans (le_trans Ideal.mul_le_inf inf_le_right) (ih i' hi')

end Ideal

namespace KaehlerDifferential

theorem residue_tmul_D_mul_of_mem_maximalIdeal (k : Type*) [CommRing k] (A : Type*)
    [CommRing A]
    [Algebra k A] [IsLocalRing A] (x c : A) (hx : x ∈ IsLocalRing.maximalIdeal A) :
    (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (x * c) =
      IsLocalRing.residue A c •
        ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A x) := by
  have hsm : ∀ a : A, a • (1 : IsLocalRing.ResidueField A) = IsLocalRing.residue A a := by
    intro a
    rw [Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq]
  have hx0 : IsLocalRing.residue A x = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hx
  have hstep : IsLocalRing.residue A c •
        ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A x)
      = (IsLocalRing.residue A c * 1) ⊗ₜ[A] KaehlerDifferential.D k A x := rfl
  rw [Derivation.leibniz, TensorProduct.tmul_add, ← TensorProduct.smul_tmul,
    ← TensorProduct.smul_tmul, hsm, hsm, hx0, TensorProduct.zero_tmul, zero_add, hstep,
    mul_one]

end KaehlerDifferential
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.StandardSmoothCharts
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem preimage_comp_consolidated17 {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) :
    (f ≫ g) ⁻¹ᵁ U = f ⁻¹ᵁ (g ⁻¹ᵁ U) := by
  simp

private theorem image_preimage_of_le_consolidated17 {X : Scheme.{u}} (U A : X.Opens) (hA : A ≤ U) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ A) = A := by
  apply le_antisymm
  · rintro z ⟨w, hw, rfl⟩
    exact hw
  · intro z hz
    exact ⟨⟨z, hA hz⟩, hz, rfl⟩

private theorem basicOpen_appLE_consolidated17 {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (s : ↑(Y.presheaf.obj (Opposite.op U))) :
    X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s) =
      V ⊓ f ⁻¹ᵁ Y.basicOpen s := by
  simp [AlgebraicGeometry.Scheme.Hom.appLE, AlgebraicGeometry.Scheme.preimage_basicOpen]

private theorem algebraMap_basicOpen_eq_presheaf_map_consolidated17 {X : Scheme.{u}} {U : X.Opens}
    (s : ↑(X.presheaf.obj (Opposite.op U))) :
    algebraMap ↑(X.presheaf.obj (Opposite.op U))
        ↑(X.presheaf.obj (Opposite.op (X.basicOpen s))) =
      (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom :=
  rfl

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)

private theorem isStandardSmoothOfRelativeDimension_appLE_basicOpen_target_consolidated17 {U : Y.Opens}
    (hU : IsAffineOpen U) {V : X.Opens}
    (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (s : ↑(Y.presheaf.obj (Opposite.op U)))
    (hs : RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom)
    (hle : X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s) ≤
      f ⁻¹ᵁ Y.basicOpen s) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f (Y.basicOpen s)
        (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)) hle).hom := by
  have i1 : IsLocalization.Away s ↑(Y.presheaf.obj (Opposite.op (Y.basicOpen s))) :=
    hU.isLocalization_basicOpen s
  have i2 : IsLocalization.Away ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)
      ↑(X.presheaf.obj (Opposite.op
        (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)))) :=
    hV.isLocalization_basicOpen _
  have i3 : IsLocalization
      (Submonoid.map (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom (Submonoid.powers s))
      ↑(X.presheaf.obj (Opposite.op
        (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)))) := by
    rw [Submonoid.map_powers]
    exact i2
  have key := RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves n
    (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom (Submonoid.powers s)
    ↑(Y.presheaf.obj (Opposite.op (Y.basicOpen s)))
    ↑(X.presheaf.obj (Opposite.op
      (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)))) hs
  convert key using 1
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  rw [IsLocalization.map_comp, algebraMap_basicOpen_eq_presheaf_map_consolidated17,
    algebraMap_basicOpen_eq_presheaf_map_consolidated17, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, AlgebraicGeometry.Scheme.Hom.map_appLE,
    AlgebraicGeometry.Scheme.Hom.appLE_map]

private theorem isStandardSmoothOfRelativeDimension_appLE_basicOpen_source_consolidated17 {U : Y.Opens}
    {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (hs : RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom)
    (t : ↑(X.presheaf.obj (Opposite.op V))) (hle : X.basicOpen t ≤ f ⁻¹ᵁ U) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U (X.basicOpen t) hle).hom := by
  have : IsLocalization.Away t ↑(X.presheaf.obj (Opposite.op (X.basicOpen t))) :=
    hV.isLocalization_basicOpen t
  have h0 : RingHom.IsStandardSmoothOfRelativeDimension 0
      (algebraMap ↑(X.presheaf.obj (Opposite.op V))
        ↑(X.presheaf.obj (Opposite.op (X.basicOpen t)))) :=
    RingHom.isStandardSmoothOfRelativeDimension_holdsForLocalizationAway _ t
  have hcomp := h0.comp hs
  rw [zero_add, algebraMap_basicOpen_eq_presheaf_map_consolidated17, ← CommRingCat.hom_comp,
    AlgebraicGeometry.Scheme.Hom.appLE_map] at hcomp
  exact hcomp

private theorem isStandardSmoothOfRelativeDimension_appLE_congr_consolidated17 {U U' : Y.Opens}
    {V V' : X.Opens} (hU : U' = U) (hV : V' = V) (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U')
    (hstd : RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U' V' e').hom := by
  subst hU
  subst hV
  exact hstd


end

section
variable {X X' : Scheme.{u}} (φ : X' ⟶ X) (r : ℕ) [SmoothOfRelativeDimension r φ]

private theorem exists_affineChart_isStandardSmoothOfRelativeDimension_consolidated17 (A₀ : X.Opens) (B₀ : X'.Opens)
    (hB₀ : B₀ ≤ φ ⁻¹ᵁ A₀) (y : ↥X') (hy : y ∈ B₀) :
    ∃ (A : X.Opens) (B : X'.Opens), IsAffineOpen A ∧
      IsAffineOpen B ∧ A ≤ A₀ ∧ B ≤ B₀ ∧ y ∈ B ∧
      ∃ e : B ≤ φ ⁻¹ᵁ A, RingHom.IsStandardSmoothOfRelativeDimension r
        (AlgebraicGeometry.Scheme.Hom.appLE φ A B e).hom := by
  obtain ⟨U, hU, V, hV, hyV, e, hstd⟩ :=
    (AlgebraicGeometry.smoothOfRelativeDimension_iff r φ).mp inferInstance y
  obtain ⟨s, hsA₀, hys⟩ := hU.exists_basicOpen_le (⟨φ.base y, hB₀ hy⟩ : ↥A₀) (e hyV)
  have hB₁eq : X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s) =
      V ⊓ φ ⁻¹ᵁ X.basicOpen s := basicOpen_appLE_consolidated17 φ e s
  have hB₁le : X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s) ≤
      φ ⁻¹ᵁ X.basicOpen s := by
    rw [hB₁eq]
    exact inf_le_right
  have hB₁aff : IsAffineOpen
      (X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s)) := hV.basicOpen _
  have hyB₁ : y ∈ X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s) := by
    rw [hB₁eq]
    exact ⟨hyV, hys⟩
  have hstd₁ :=
    isStandardSmoothOfRelativeDimension_appLE_basicOpen_target_consolidated17 φ r hU hV e s hstd hB₁le
  obtain ⟨t, htB₀, hyt⟩ := hB₁aff.exists_basicOpen_le (⟨y, hy⟩ : ↥B₀) hyB₁
  have hBle : X'.basicOpen t ≤ φ ⁻¹ᵁ X.basicOpen s :=
    le_trans (X'.basicOpen_le t) hB₁le
  exact ⟨X.basicOpen s, X'.basicOpen t, hU.basicOpen s, hB₁aff.basicOpen t, hsA₀, htB₀, hyt,
    hBle, isStandardSmoothOfRelativeDimension_appLE_basicOpen_source_consolidated17 φ r hB₁aff hB₁le hstd₁ t hBle⟩

theorem smoothOfRelativeDimension_resLE (U₀ : X.Opens) (V₀ : X'.Opens)
    (h : V₀ ≤ φ ⁻¹ᵁ U₀) :
    SmoothOfRelativeDimension r (φ.resLE U₀ V₀ h) := by
  rw [AlgebraicGeometry.smoothOfRelativeDimension_iff]
  intro x
  have hx : V₀.ι.base x ∈ V₀ := by
    have hmem : V₀.ι.base x ∈ AlgebraicGeometry.Scheme.Hom.opensRange V₀.ι := ⟨x, rfl⟩
    rwa [AlgebraicGeometry.Scheme.Opens.opensRange_ι] at hmem
  obtain ⟨A, B, hA, hB, hAU₀, hBV₀, hxB, e, hstd⟩ :=
    exists_affineChart_isStandardSmoothOfRelativeDimension_consolidated17 φ r U₀ V₀ h (V₀.ι.base x) hx
  have hpre : (φ.resLE U₀ V₀ h) ⁻¹ᵁ (U₀.ι ⁻¹ᵁ A) = V₀.ι ⁻¹ᵁ (φ ⁻¹ᵁ A) := by
    rw [← preimage_comp_consolidated17, ← preimage_comp_consolidated17, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι]
  have he' : V₀.ι ⁻¹ᵁ B ≤ (φ.resLE U₀ V₀ h) ⁻¹ᵁ (U₀.ι ⁻¹ᵁ A) := by
    rw [hpre]
    exact fun z hz => e hz
  refine ⟨U₀.ι ⁻¹ᵁ A, hA.preimage_of_isOpenImmersion U₀.ι (by simp [hAU₀]),
    V₀.ι ⁻¹ᵁ B, hB.preimage_of_isOpenImmersion V₀.ι (by simp [hBV₀]), hxB, he', ?_⟩
  rw [AlgebraicGeometry.Scheme.Hom.resLE_appLE]
  exact isStandardSmoothOfRelativeDimension_appLE_congr_consolidated17 φ r (image_preimage_of_le_consolidated17 U₀ A hAU₀)
    (image_preimage_of_le_consolidated17 V₀ B hBV₀) e _ hstd


end

instance instSmoothOfRelativeDimensionResLE {X X' : Scheme.{u}} (φ : X' ⟶ X) (r : ℕ)
    [SmoothOfRelativeDimension r φ] (U₀ : X.Opens) (V₀ : X'.Opens)
    (h : V₀ ≤ φ ⁻¹ᵁ U₀) :
    SmoothOfRelativeDimension r (φ.resLE U₀ V₀ h) :=
  smoothOfRelativeDimension_resLE φ r U₀ V₀ h

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.BinaryCoproductBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


namespace FunctorialResolution.EmbeddedResolution

private def boolFamily_consolidated49 (X₁ X₂ : Scheme.{u}) : ULift.{u} Bool → Scheme.{u} :=
  fun i => cond i.down X₁ X₂

private def boolFamilyMap_consolidated49 {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    ∀ i, boolFamily_consolidated49 X₁ X₂ i ⟶ boolFamily_consolidated49 Y₁ Y₂ i
  | ⟨true⟩ => f₁
  | ⟨false⟩ => f₂

private def boolFamilyDesc_consolidated49 {X₁ X₂ Y : Scheme.{u}} (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) :
    ∀ i, boolFamily_consolidated49 X₁ X₂ i ⟶ Y
  | ⟨true⟩ => f₁
  | ⟨false⟩ => f₂

private noncomputable def sigmaBoolFamilyInl (X₁ X₂ : Scheme.{u}) : X₁ ⟶ ∐ boolFamily_consolidated49 X₁ X₂ :=
  Limits.Sigma.ι (boolFamily_consolidated49 X₁ X₂) ⟨true⟩

private noncomputable def sigmaBoolFamilyInr (X₁ X₂ : Scheme.{u}) : X₂ ⟶ ∐ boolFamily_consolidated49 X₁ X₂ :=
  Limits.Sigma.ι (boolFamily_consolidated49 X₁ X₂) ⟨false⟩

section
variable {X₁ X₂ Y : Scheme.{u}} (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)

private theorem pairInl_comp_desc_consolidated49 :
    sigmaBoolFamilyInl X₁ X₂ ≫ Limits.Sigma.desc (boolFamilyDesc_consolidated49 f₁ f₂) = f₁ :=
  Limits.Sigma.ι_desc (boolFamilyDesc_consolidated49 f₁ f₂) ⟨true⟩

private theorem pairInr_comp_desc_consolidated49 :
    sigmaBoolFamilyInr X₁ X₂ ≫ Limits.Sigma.desc (boolFamilyDesc_consolidated49 f₁ f₂) = f₂ :=
  Limits.Sigma.ι_desc (boolFamilyDesc_consolidated49 f₁ f₂) ⟨false⟩


end

section
variable {X₁ X₂ P₁ P₂ : Scheme.{u}} (a₁ : P₁ ⟶ X₁) (a₂ : P₂ ⟶ X₂)

private theorem pairInl_comp_map_consolidated49 :
    sigmaBoolFamilyInl P₁ P₂ ≫ Limits.Sigma.map (boolFamilyMap_consolidated49 a₁ a₂) = a₁ ≫ sigmaBoolFamilyInl X₁ X₂ :=
  Limits.Sigma.ι_map (boolFamilyMap_consolidated49 a₁ a₂) ⟨true⟩

private theorem pairInr_comp_map_consolidated49 :
    sigmaBoolFamilyInr P₁ P₂ ≫ Limits.Sigma.map (boolFamilyMap_consolidated49 a₁ a₂) = a₂ ≫ sigmaBoolFamilyInr X₁ X₂ :=
  Limits.Sigma.ι_map (boolFamilyMap_consolidated49 a₁ a₂) ⟨false⟩


end

private theorem sigmaPair_hom_ext_consolidated49 {X₁ X₂ Z : Scheme.{u}} (f g : (∐ boolFamily_consolidated49 X₁ X₂) ⟶ Z)
    (ht : sigmaBoolFamilyInl X₁ X₂ ≫ f = sigmaBoolFamilyInl X₁ X₂ ≫ g)
    (hf : sigmaBoolFamilyInr X₁ X₂ ≫ f = sigmaBoolFamilyInr X₁ X₂ ≫ g) : f = g := by
  apply Limits.Sigma.hom_ext
  rintro ⟨(_ | _)⟩
  · exact hf
  · exact ht

private noncomputable def coprodIsoSigmaBoolFamily (X₁ X₂ : Scheme.{u}) : (X₁ ⨿ X₂) ≅ ∐ boolFamily_consolidated49 X₁ X₂ where
  hom := coprod.desc (sigmaBoolFamilyInl X₁ X₂) (sigmaBoolFamilyInr X₁ X₂)
  inv := Limits.Sigma.desc (boolFamilyDesc_consolidated49 (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) (coprod.inr : X₂ ⟶ X₁ ⨿ X₂))
  hom_inv_id := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, pairInl_comp_desc_consolidated49, Category.comp_id]
    · rw [coprod.inr_desc_assoc, pairInr_comp_desc_consolidated49, Category.comp_id]
  inv_hom_id := by
    apply sigmaPair_hom_ext_consolidated49
    · rw [← Category.assoc, pairInl_comp_desc_consolidated49, coprod.inl_desc, Category.comp_id]
    · rw [← Category.assoc, pairInr_comp_desc_consolidated49, coprod.inr_desc, Category.comp_id]

private theorem pairCoprodIso_hom_consolidated49 (X₁ X₂ : Scheme.{u}) :
    (coprodIsoSigmaBoolFamily X₁ X₂).hom = coprod.desc (sigmaBoolFamilyInl X₁ X₂) (sigmaBoolFamilyInr X₁ X₂) := rfl

private noncomputable def isoCoprodInitial (P : Scheme.{u}) : P ≅ P ⨿ (⊥_ Scheme.{u}) where
  hom := coprod.inl
  inv := coprod.desc (𝟙 P) (initial.to P)
  hom_inv_id := coprod.inl_desc (𝟙 P) (initial.to P)
  inv_hom_id := by
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_desc, Category.id_comp, Category.comp_id]
    · exact initial.hom_ext _ _

private theorem coprodInitialIsoRight_hom_consolidated49 (P : Scheme.{u}) :
    (isoCoprodInitial P).hom = (coprod.inl : P ⟶ P ⨿ (⊥_ Scheme.{u})) := rfl

private noncomputable def isInitialOfIsEmptyScheme {X : Scheme.{u}} (h : IsEmpty X) : IsInitial X := by
  haveI := h
  exact isInitialOfIsEmpty

private theorem isPullback_of_isPullback_of_iso_consolidated49 {P X Y Z P' X' : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {fst' : P' ⟶ X'} {snd' : P' ⟶ Y} {f' : X' ⟶ Z}
    (h : IsPullback fst snd f g) (eP : P' ≅ P) (eX : X' ≅ X)
    (h1 : fst' ≫ eX.hom = eP.hom ≫ fst) (h2 : eX.hom ≫ f = f')
    (h3 : eP.hom ≫ snd = snd') : IsPullback fst' snd' f' g := by
  have sq2 : CommSq eX.inv f f' (𝟙 Z) := by
    refine ⟨?_⟩
    rw [← h2, Iso.inv_hom_id_assoc, Category.comp_id]
  have hX : IsPullback eX.inv f f' (𝟙 Z) := IsPullback.of_horiz_isIso sq2
  have step1 := h.paste_horiz hX
  have sq1 : CommSq eP.hom (eP.hom ≫ snd) snd (𝟙 Y) := by
    refine ⟨?_⟩
    rw [Category.comp_id]
  have hP : IsPullback eP.hom (eP.hom ≫ snd) snd (𝟙 Y) := IsPullback.of_horiz_isIso sq1
  have step2 := hP.paste_horiz step1
  have hfst : fst' = eP.hom ≫ fst ≫ eX.inv := by
    rw [← Category.assoc, ← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hfst, ← h3]
  simpa using step2

theorem isPullback_coprodMap_coprodDesc {X₁ X₂ P₁ P₂ Y Y' : Scheme.{u}}
    (a₁ : P₁ ⟶ X₁) (a₂ : P₂ ⟶ X₂) (b₁ : P₁ ⟶ Y') (b₂ : P₂ ⟶ Y')
    (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) (u : Y' ⟶ Y)
    (h₁ : IsPullback a₁ b₁ f₁ u) (h₂ : IsPullback a₂ b₂ f₂ u) :
    IsPullback (coprod.map a₁ a₂) (coprod.desc b₁ b₂) (coprod.desc f₁ f₂) u := by
  have hsq : ∀ i : ULift.{u} Bool,
      IsPullback (boolFamilyMap_consolidated49 a₁ a₂ i) (boolFamilyDesc_consolidated49 b₁ b₂ i) (boolFamilyDesc_consolidated49 f₁ f₂ i) u := by
    rintro ⟨(_ | _)⟩
    · exact h₂
    · exact h₁
  have key := isPullback_sigmaMap_sigmaDesc u (boolFamily_consolidated49 X₁ X₂) (boolFamily_consolidated49 P₁ P₂)
      (boolFamilyMap_consolidated49 a₁ a₂) (boolFamilyDesc_consolidated49 b₁ b₂) (boolFamilyDesc_consolidated49 f₁ f₂) hsq
  have E1 : coprod.map a₁ a₂ ≫ (coprodIsoSigmaBoolFamily X₁ X₂).hom
      = (coprodIsoSigmaBoolFamily P₁ P₂).hom ≫ Limits.Sigma.map (boolFamilyMap_consolidated49 a₁ a₂) := by
    simp only [pairCoprodIso_hom_consolidated49]
    apply coprod.hom_ext
    · rw [coprod.inl_map_assoc, coprod.inl_desc, coprod.inl_desc_assoc, pairInl_comp_map_consolidated49]
    · rw [coprod.inr_map_assoc, coprod.inr_desc, coprod.inr_desc_assoc, pairInr_comp_map_consolidated49]
  have E2 : (coprodIsoSigmaBoolFamily X₁ X₂).hom ≫ Limits.Sigma.desc (boolFamilyDesc_consolidated49 f₁ f₂)
      = coprod.desc f₁ f₂ := by
    simp only [pairCoprodIso_hom_consolidated49]
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, pairInl_comp_desc_consolidated49, coprod.inl_desc]
    · rw [coprod.inr_desc_assoc, pairInr_comp_desc_consolidated49, coprod.inr_desc]
  have E3 : (coprodIsoSigmaBoolFamily P₁ P₂).hom ≫ Limits.Sigma.desc (boolFamilyDesc_consolidated49 b₁ b₂)
      = coprod.desc b₁ b₂ := by
    simp only [pairCoprodIso_hom_consolidated49]
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, pairInl_comp_desc_consolidated49, coprod.inl_desc]
    · rw [coprod.inr_desc_assoc, pairInr_comp_desc_consolidated49, coprod.inr_desc]
  exact isPullback_of_isPullback_of_iso_consolidated49 key (coprodIsoSigmaBoolFamily P₁ P₂) (coprodIsoSigmaBoolFamily X₁ X₂) E1 E2 E3

theorem isPullback_initial_of_isEmpty {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (u : Y' ⟶ Y)
    (h : ∀ (P : Scheme.{u}) (a : P ⟶ X) (b : P ⟶ Y'), a ≫ f = b ≫ u → IsEmpty P) :
    IsPullback (initial.to X) (initial.to Y') f u := by
  have hw : CommSq (initial.to X) (initial.to Y') f u := ⟨initial.hom_ext _ _⟩
  refine IsPullback.of_isLimit' hw (PullbackCone.isLimitAux' _ (fun s => ?_))
  have hinit : IsInitial s.pt := isInitialOfIsEmptyScheme (h s.pt s.fst s.snd s.condition)
  refine ⟨hinit.to _, hinit.hom_ext _ _, hinit.hom_ext _ _, ?_⟩
  intro m _ _
  exact hinit.hom_ext _ _

theorem isPullback_comp_inl_coprodDesc {P X Y Y' F : Scheme.{u}}
    (a : P ⟶ X) (b : P ⟶ Y') (q : X ⟶ Y) (u : Y' ⟶ Y) (r : F ⟶ Y)
    (hsq : IsPullback a b q u)
    (hF : ∀ (Q : Scheme.{u}) (c : Q ⟶ F) (d : Q ⟶ Y'), c ≫ r = d ≫ u → IsEmpty Q) :
    IsPullback (a ≫ coprod.inl) b (coprod.desc q r) u := by
  have hFpb : IsPullback (initial.to F) (initial.to Y') r u :=
    isPullback_initial_of_isEmpty r u hF
  have key := isPullback_coprodMap_coprodDesc a (initial.to F) b (initial.to Y') q r u hsq hFpb
  have E1 : (a ≫ coprod.inl) ≫ (Iso.refl (X ⨿ F)).hom
      = (isoCoprodInitial P).hom ≫ coprod.map a (initial.to F) := by
    rw [Iso.refl_hom, Category.comp_id, coprodInitialIsoRight_hom_consolidated49, coprod.inl_map]
  have E2 : (Iso.refl (X ⨿ F)).hom ≫ coprod.desc q r = coprod.desc q r := by
    rw [Iso.refl_hom, Category.id_comp]
  have E3 : (isoCoprodInitial P).hom ≫ coprod.desc b (initial.to Y') = b := by
    rw [coprodInitialIsoRight_hom_consolidated49, coprod.inl_desc]
  exact isPullback_of_isPullback_of_iso_consolidated49 key (isoCoprodInitial P) (Iso.refl (X ⨿ F)) E1 E2 E3

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution


noncomputable abbrev sigmaOpens (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) : Scheme.{u} :=
  ∐ fun i => (U i).toScheme

noncomputable abbrev sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    sigmaOpens Y U ⟶ Y :=
  Sigma.desc fun i => (U i).ι

section
variable (Y : Scheme.{u}) {ι : Type u}

theorem sigma_ι_sigmaOpensDesc (U : ι → Y.Opens) (i : ι) :
    Sigma.ι (fun i => (U i).toScheme) i ≫ sigmaOpensDesc Y U = (U i).ι := by
  simp

theorem sigma_ι_sigmaOpensDesc_assoc (U : ι → Y.Opens) (i : ι)
    {Z : Scheme.{u}} (h : Y ⟶ Z) :
    Sigma.ι (fun i => (U i).toScheme) i ≫ sigmaOpensDesc Y U ≫ h = (U i).ι ≫ h := by
  simp

theorem isAffine_sigmaOpens [Finite ι] (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) : IsAffine (sigmaOpens Y U) := by
  have : ∀ i, IsAffine (U i).toScheme := fun i => hU i
  exact inferInstanceAs (IsAffine (∐ fun i => (U i).toScheme))


end

private theorem isReduced_of_ringEquiv_consolidated48
    {A B : Type u} [CommRing A] [CommRing B] [_root_.IsReduced B] (e : A ≃+* B) :
    _root_.IsReduced A :=
  ⟨fun _ hx => e.injective (((hx.map e).eq_zero).trans (map_zero e).symm)⟩

private theorem isReduced_of_forall_isReduced_stalk_consolidated48 (X : Scheme.{u})
    (h : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x)) : IsReduced X := by
  have := h
  exact isReduced_of_isReduced_stalk X

theorem isReduced_sigmaOpens (Y : Scheme.{u}) [IsReduced Y] {ι : Type u} (U : ι → Y.Opens) :
    IsReduced (sigmaOpens Y U) := by
  refine isReduced_of_forall_isReduced_stalk_consolidated48 _ ?_
  intro x
  obtain ⟨⟨i, y⟩, hx⟩ := (sigmaMk fun i => (U i).toScheme).surjective x
  have hx' : (Sigma.ι (fun i => (U i).toScheme) i).base y = x := by simpa using hx
  subst hx'
  exact isReduced_of_ringEquiv_consolidated48
    (((asIso ((Sigma.ι (fun i => (U i).toScheme) i).stalkMap y)).commRingCatIsoToRingEquiv).trans
      ((asIso (((U i).ι).stalkMap y)).commRingCatIsoToRingEquiv.symm))

instance instIsReducedOpensCoprod (Y : Scheme.{u}) [IsReduced Y] {ι : Type u} (U : ι → Y.Opens) :
    IsReduced (sigmaOpens Y U) :=
  isReduced_sigmaOpens Y U

theorem etale_isZariskiLocalAtSource : IsZariskiLocalAtSource (@Etale.{u}) := by
  have hrh : HasRingHomProperty (@Etale.{u}) RingHom.Etale := inferInstance
  exact @HasRingHomProperty.instIsZariskiLocalAtSource (@Etale.{u}) _ hrh

theorem etale_sigmaDesc {ι : Type u} {X : ι → Scheme.{u}} {Z : Scheme.{u}}
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, Etale (f i)) : Etale (Sigma.desc f) := by
  have hloc : IsZariskiLocalAtSource (@Etale.{u}) := etale_isZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc hf

theorem etale_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    Etale (sigmaOpensDesc Y U) := by
  have hloc : IsZariskiLocalAtSource (@Etale.{u}) := etale_isZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance

instance instEtaleOpensCoprodDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    Etale (sigmaOpensDesc Y U) :=
  etale_sigmaOpensDesc Y U

theorem locallyOfFiniteType_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    LocallyOfFiniteType (sigmaOpensDesc Y U) := by
  have : Etale (sigmaOpensDesc Y U) := etale_sigmaOpensDesc Y U
  infer_instance

instance instLocallyOfFiniteTypeOpensCoprodDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    LocallyOfFiniteType (sigmaOpensDesc Y U) :=
  locallyOfFiniteType_sigmaOpensDesc Y U

section
variable (Y : Scheme.{u})

theorem surjective_sigmaOpensDesc {ι : Type u} (U : ι → Y.Opens)
    (hU : iSup U = ⊤) : Surjective (sigmaOpensDesc Y U) := by
  constructor
  intro y
  have hy : y ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  refine ⟨(Sigma.ι (fun i => (U i).toScheme) i).base (⟨y, hi⟩ : ↥((U i).toScheme)), ?_⟩
  exact congrArg (fun f : (U i).toScheme ⟶ Y => f.base (⟨y, hi⟩ : ↥((U i).toScheme)))
    (sigma_ι_sigmaOpensDesc Y U i)

private theorem exists_isAffineOpen_mem_consolidated48 (x : Y) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ x ∈ U := by
  refine ⟨(Y.affineOpenCover.3 (Y.affineOpenCover.4 x)).opensRange,
    isAffineOpen_opensRange _, ?_⟩
  exact Y.affineOpenCover.5 x

theorem exists_finite_affine_cover [CompactSpace Y] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → Y.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ iSup U = ⊤ := by
  classical
  choose V hV hxV using exists_isAffineOpen_mem_consolidated48 Y
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : Y => (V x : Set Y))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  refine ⟨{ x : Y // x ∈ t }, inferInstance, fun i => V i.1, fun i => hV i.1, ?_⟩
  refine TopologicalSpace.Opens.ext ?_
  rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
  refine Set.eq_univ_of_univ_subset fun x _ => ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩


end

private theorem subsingleton_spec_of_field_consolidated48 (k : Type u) [Field k] :
    Subsingleton ↥(Spec (CommRingCat.of k)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

theorem exists_affine_etale_cover_of_isReduced {k : Type u} [Field k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [QuasiCompact p] [IsReduced Y] :
    ∃ (W : Scheme.{u}) (q : W ⟶ Spec (CommRingCat.of k)) (g : W ⟶ Y),
      IsAffine W ∧ IsReduced W ∧ LocallyOfFiniteType q ∧ QuasiCompact q ∧
        Etale g ∧ Surjective g ∧ g ≫ p = q := by
  have hsub : Subsingleton ↥(Spec (CommRingCat.of k)) := subsingleton_spec_of_field_consolidated48 k
  have hcs : CompactSpace ↥(Spec (CommRingCat.of k)) := inferInstance
  have hcY : CompactSpace ↥Y := by
    constructor
    have h := (‹QuasiCompact p›).isCompact_preimage Set.univ isOpen_univ isCompact_univ
    rwa [Set.preimage_univ] at h
  obtain ⟨ι, hι, U, hUaff, hUsup⟩ := exists_finite_affine_cover Y
  have : Finite ι := hι
  have hW : IsAffine (sigmaOpens Y U) := isAffine_sigmaOpens Y U hUaff
  have : CompactSpace ↥(sigmaOpens Y U) := inferInstance
  refine ⟨sigmaOpens Y U, sigmaOpensDesc Y U ≫ p, sigmaOpensDesc Y U, hW,
    isReduced_sigmaOpens Y U, ?_, ?_, etale_sigmaOpensDesc Y U,
    surjective_sigmaOpensDesc Y U hUsup, rfl⟩
  · infer_instance
  · exact quasiCompact_of_compactSpace_of_subsingleton _

theorem smooth_isZariskiLocalAtSource : IsZariskiLocalAtSource (@Smooth.{u}) := by
  have hrh : HasRingHomProperty (@Smooth.{u}) RingHom.Smooth := inferInstance
  exact @HasRingHomProperty.instIsZariskiLocalAtSource (@Smooth.{u}) _ hrh

instance instIsZariskiLocalAtSourceSmooth : IsZariskiLocalAtSource (@Smooth.{u}) :=
  smooth_isZariskiLocalAtSource

theorem smooth_sigmaDesc {ι : Type u} {X : ι → Scheme.{u}} {Z : Scheme.{u}}
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, Smooth (f i)) : Smooth (Sigma.desc f) :=
  IsZariskiLocalAtSource.sigmaDesc hf

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.RegularLocalRing
section
namespace IsRegularLocalRing

open IsLocalRing


private theorem spanFinrank_span_finset_le_card_consolidated47 {R : Type*} [CommRing R] (s : Finset R) :
    Submodule.spanFinrank (Ideal.span (s : Set R)) ≤ s.card := by
  have h2 : (Ideal.span (s : Set R)).FG := Submodule.fg_span s.finite_toSet
  have h1 : (Ideal.span (s : Set R)).spanRank ≤ Cardinal.mk ((s : Set R)) :=
    Submodule.spanRank_span_le_card _
  rw [Submodule.FG.spanRank_eq_spanFinrank h2] at h1
  have h3 : Cardinal.mk ((s : Set R)) = (s.card : Cardinal) := by simp
  rw [h3] at h1
  exact_mod_cast h1

private theorem exists_repr_ne_zero_consolidated47 {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Module.Basis ι K V) {v : V} (hv : v ≠ 0) : ∃ j, b.repr v j ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : b.repr v = 0 := by
    ext j
    simp [h j]
  apply hv
  have h1 := congrArg (b.repr.symm) h0
  simpa using h1

private theorem span_insert_image_erase_eq_top_consolidated47 {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {N : ℕ} (b : Module.Basis (Fin N) K V) (v : V) {j : Fin N}
    (hj : b.repr v j ≠ 0) :
    Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) = ⊤ := by
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  simp only [SetLike.mem_coe]
  by_cases hij : i = j
  · rw [hij]
    have hmem1 : v ∈ Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) :=
      Submodule.subset_span (Set.mem_insert _ _)
    have hmem2 : ∑ l ∈ Finset.univ.erase j, b.repr v l • b l ∈
        Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) := by
      refine Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨l, Finset.mem_coe.mpr hl, rfl⟩)
    have hsub : v - ∑ l ∈ Finset.univ.erase j, b.repr v l • b l = b.repr v j • b j := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ j), b.sum_repr v]
      abel
    have hkey : b.repr v j • b j ∈
        Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) := by
      rw [← hsub]
      exact Submodule.sub_mem _ hmem1 hmem2
    have h2 := Submodule.smul_mem _ (b.repr v j)⁻¹ hkey
    rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at h2
  · exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, by simp [hij], rfl⟩)

private theorem isLocalRing_quotient_span_singleton_consolidated47 {R : Type*} [CommRing R] [IsLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) : IsLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  have hIle : Ideal.span ({x} : Set R) ≤ maximalIdeal R := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  have hIne : Ideal.span ({x} : Set R) ≠ ⊤ := by
    intro h
    rw [h, top_le_iff] at hIle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hIle
  have hone : (1 : R ⧸ Ideal.span ({x} : Set R)) ≠ 0 := by
    intro h
    have h1 : (1 : R) ∈ Ideal.span ({x} : Set R) := by
      rwa [← Ideal.Quotient.eq_zero_iff_mem, map_one]
    exact hIne ((Ideal.eq_top_iff_one _).mpr h1)
  have : Nontrivial (R ⧸ Ideal.span ({x} : Set R)) := ⟨⟨1, 0, hone⟩⟩
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

private theorem spanFinrank_maximalIdeal_quotient_add_one_le_finrank_consolidated47 (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) + 1 ≤
      Module.finrank (ResidueField R) (CotangentSpace R) := by
  classical
  have hv0 : (maximalIdeal R).toCotangent ⟨x, hx⟩ ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]
    exact hx2
  obtain ⟨j, hj⟩ := exists_repr_ne_zero_consolidated47 (Module.finBasis (ResidueField R) (CotangentSpace R)) hv0
  obtain ⟨z, hz⟩ : ∃ z : Fin (Module.finrank (ResidueField R) (CotangentSpace R)) →
      (maximalIdeal R), ∀ i, (maximalIdeal R).toCotangent (z i) =
        Module.finBasis (ResidueField R) (CotangentSpace R) i := by
    have hsurj : Function.Surjective (maximalIdeal R).toCotangent :=
      Ideal.toCotangent_surjective _
    choose z hz using fun i => hsurj (Module.finBasis (ResidueField R) (CotangentSpace R) i)
    exact ⟨z, hz⟩
  set s : Set (maximalIdeal R) :=
    insert (⟨x, hx⟩ : maximalIdeal R) (z '' ↑(Finset.univ.erase j)) with hsdef
  have htop : Submodule.span R s = ⊤ := by
    rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff]
    have himg : (maximalIdeal R).toCotangent '' s =
        insert ((maximalIdeal R).toCotangent ⟨x, hx⟩)
          (⇑(Module.finBasis (ResidueField R) (CotangentSpace R)) ''
            ↑(Finset.univ.erase j)) := by
      rw [hsdef, Set.image_insert_eq, Set.image_image]
      simp [hz]
    rw [himg]
    exact span_insert_image_erase_eq_top_consolidated47 _ _ hj
  have hmspan : Ideal.span ((Subtype.val : maximalIdeal R → R) '' s) = maximalIdeal R := by
    have h := congrArg (Submodule.map (maximalIdeal R).subtype) htop
    rw [Submodule.map_span, Submodule.map_subtype_top] at h
    simpa using h
  have hIle : Ideal.span ({x} : Set R) ≤ maximalIdeal R := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  have hmapS : maximalIdeal (R ⧸ Ideal.span ({x} : Set R)) =
      Ideal.map (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) (maximalIdeal R) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      refine Ideal.mem_map_of_mem _ ?_
      by_contra hr
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hr
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy
      exact hy (hr.map (Ideal.Quotient.mk (Ideal.span ({x} : Set R))))
    · refine IsLocalRing.le_maximalIdeal ?_
      intro h
      rw [Ideal.eq_top_iff_one, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h
      obtain ⟨r, hrm, hr1⟩ := h
      have h2 : r - 1 ∈ Ideal.span ({x} : Set R) := by
        rw [← Ideal.Quotient.eq]
        simpa using hr1
      have h3 : (1 : R) ∈ maximalIdeal R := by
        have h4 := sub_mem hrm (hIle h2)
        simp at h4
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
  have hx0 : Ideal.Quotient.mk (Ideal.span ({x} : Set R)) x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
  have himg : (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) ''
      ((Subtype.val : maximalIdeal R → R) '' s) =
      insert 0 ((fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) ((z i : R))) ''
        ↑(Finset.univ.erase j)) := by
    rw [hsdef, Set.image_image, Set.image_insert_eq, Set.image_image]
    simp [hx0]
  have hquot : maximalIdeal (R ⧸ Ideal.span ({x} : Set R)) =
      Ideal.span ((fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) ((z i : R))) ''
        ↑(Finset.univ.erase j)) := by
    rw [hmapS]
    conv_lhs => rw [← hmspan]
    rw [Ideal.map_span, himg]
    exact Submodule.span_insert_zero
  have hcard : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) ≤
      (Finset.univ.erase j).card := by
    rw [hquot, ← Finset.coe_image]
    exact le_trans (spanFinrank_span_finset_le_card_consolidated47 _) Finset.card_image_le
  have hjpos : 0 < Module.finrank (ResidueField R) (CotangentSpace R) := Fin.pos j
  have hcard2 : (Finset.univ.erase j).card =
      Module.finrank (ResidueField R) (CotangentSpace R) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  omega

private theorem eq_natCast_and_add_one_eq_of_le_consolidated47 {a : WithBot ℕ∞} {d n : ℕ}
    (h1 : ((n : ℕ) : WithBot ℕ∞) ≤ a + 1) (h2 : a ≤ ((d : ℕ) : WithBot ℕ∞)) (h3 : d + 1 ≤ n) :
    a = ((d : ℕ) : WithBot ℕ∞) ∧ a + 1 = ((n : ℕ) : WithBot ℕ∞) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, a = ((m : ℕ) : WithBot ℕ∞) := by
    induction a using WithBot.recBotCoe with
    | bot =>
      exfalso
      rw [WithBot.bot_add, le_bot_iff] at h1
      exact WithBot.natCast_ne_bot n h1
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        exfalso
        have h2' : (⊤ : ℕ∞) ≤ (d : ℕ∞) := by exact_mod_cast h2
        simp at h2'
      | coe m => exact ⟨m, by norm_cast⟩
  have hmd : m ≤ d := by exact_mod_cast h2
  have hnm : n ≤ m + 1 := by exact_mod_cast h1
  have hm : m = d := by omega
  have hn : n = m + 1 := by omega
  refine ⟨?_, ?_⟩
  · rw [hm]
  · rw [hn]
    norm_cast

private theorem spanFinrank_quotient_eq_ringKrullDim_and_add_one_eq_consolidated47 (R : Type*) [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    ((Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) : ℕ) : WithBot ℕ∞)
        = ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) ∧
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  have hdn := spanFinrank_maximalIdeal_quotient_add_one_le_finrank_consolidated47 R hx hx2
  have hRdim : ((Module.finrank (ResidueField R) (CotangentSpace R) : ℕ) : WithBot ℕ∞)
      = ringKrullDim R := by
    rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    exact_mod_cast IsRegularLocalRing.spanFinrank_maximalIdeal
  have hdimQuot : ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) ≤
      ((Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) : ℕ) :
        WithBot ℕ∞) := by
    exact_mod_cast ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ Ideal.span ({x} : Set R))
  have hIj : Ideal.span ({x} : Set R) ≤ Ring.jacobson R := by
    refine le_trans ?_ (IsLocalRing.ringJacobson_eq_maximalIdeal R).ge
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  have hdimLe := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank
      (Ideal.span ({x} : Set R)) hIj
  have h1 : Submodule.spanFinrank (Ideal.span ({x} : Set R)) ≤ 1 := by
    have h := spanFinrank_span_finset_le_card_consolidated47 ({x} : Finset R)
    simpa using h
  have hcast : ((Submodule.spanFinrank (Ideal.span ({x} : Set R)) : ℕ) : WithBot ℕ∞) ≤ 1 := by
    exact_mod_cast h1
  have hdimSucc : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 :=
    hdimLe.trans (add_le_add le_rfl hcast)
  obtain ⟨hA, hB⟩ := eq_natCast_and_add_one_eq_of_le_consolidated47
    (d := Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))))
    (n := Module.finrank (ResidueField R) (CotangentSpace R))
    (by rw [hRdim]; exact hdimSucc) hdimQuot hdn
  refine ⟨hA.symm, ?_⟩
  rw [hB, hRdim]

section
variable {R : Type*} [CommRing R]

private theorem isPrime_of_mem_minimalPrimes_consolidated47 {p : Ideal R}
    (hp : p ∈ minimalPrimes R) : p.IsPrime := hp.1.1

private theorem le_of_le_of_mem_minimalPrimes_consolidated47 {p q : Ideal R}
    (hp : p ∈ minimalPrimes R) (hq : q.IsPrime) (hle : q ≤ p) : p ≤ q :=
  hp.2 ⟨hq, bot_le⟩ hle


end

section
variable (R : Type*) [CommRing R] [IsLocalRing R]

private theorem isDomain_of_maximalIdeal_eq_bot_consolidated47 (h : maximalIdeal R = ⊥) : IsDomain R := by
  have hp : (maximalIdeal R).IsPrime := (maximalIdeal.isMaximal R).isPrime
  rw [h] at hp
  have := hp
  exact IsDomain.of_bot_isPrime R

private theorem maximalIdeal_eq_bot_of_le_sq_consolidated47 [IsNoetherianRing R] (h : maximalIdeal R ≤ maximalIdeal R ^ 2) : maximalIdeal R = ⊥ := by
  refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
    (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  show maximalIdeal R ≤ maximalIdeal R * maximalIdeal R
  rw [← pow_two]
  exact h

private theorem exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes_consolidated47 [IsNoetherianRing R] (hsq : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2)
    (hmin : ¬ ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p) :
    ∃ x, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  obtain ⟨t, ht⟩ := (minimalPrimes.finite_of_isNoetherianRing R).exists_finset_coe
  by_contra hcon
  push Not at hcon
  have hsub : (maximalIdeal R : Set R) ⊆
      ⋃ i ∈ ((insert (maximalIdeal R ^ 2) t : Finset (Ideal R)) : Set (Ideal R)), (i : Set R) := by
    intro y hy
    rcases em (y ∈ maximalIdeal R ^ 2) with hm2 | hm2
    · exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)) hm2
    · obtain ⟨p, hp, hyp⟩ := hcon y hy hm2
      have hpt : p ∈ insert (maximalIdeal R ^ 2) t := by
        apply Finset.mem_insert_of_mem
        rw [← Finset.mem_coe, ht]
        exact hp
      exact Set.mem_biUnion (Finset.mem_coe.mpr hpt) hyp
  have hp : ∀ i ∈ (insert (maximalIdeal R ^ 2) t : Finset (Ideal R)),
      i ≠ maximalIdeal R ^ 2 → i ≠ maximalIdeal R ^ 2 → i.IsPrime := by
    intro i hi h1 _
    have hit : i ∈ t := by
      rcases Finset.mem_insert.mp hi with hh | hh
      · exact absurd hh h1
      · exact hh
    refine isPrime_of_mem_minimalPrimes_consolidated47 ?_
    rw [← ht]
    exact Finset.mem_coe.mpr hit
  obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime _ _ hp).mp hsub
  rcases Finset.mem_insert.mp hi with hh | hh
  · subst hh
    exact hsq hle
  · refine hmin ⟨i, ?_, hle⟩
    rw [← ht]
    exact Finset.mem_coe.mpr hh


end

section
variable {R : Type*} [CommRing R] [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2)
include hx hx2

theorem isRegularLocalRing_quotient_span_singleton :
    IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  have := isLocalRing_quotient_span_singleton_consolidated47 hx
  rw [isRegularLocalRing_iff]
  exact_mod_cast (spanFinrank_quotient_eq_ringKrullDim_and_add_one_eq_consolidated47 R hx hx2).1

theorem ringKrullDim_quotient_span_singleton_add_one :
    ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  have := isLocalRing_quotient_span_singleton_consolidated47 hx
  exact (spanFinrank_quotient_eq_ringKrullDim_and_add_one_eq_consolidated47 R hx hx2).2


end

private theorem isDomain_of_forall_spanFinrank_lt_consolidated47 (R : Type u) [CommRing R]
    [IsRegularLocalRing R]
    (IH : ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      Submodule.spanFinrank (maximalIdeal S) < Submodule.spanFinrank (maximalIdeal R) →
        IsDomain S) :
    IsDomain R := by
  classical
  by_cases hsq : maximalIdeal R ≤ maximalIdeal R ^ 2
  · exact isDomain_of_maximalIdeal_eq_bot_consolidated47 R (maximalIdeal_eq_bot_of_le_sq_consolidated47 R hsq)
  by_cases hmin : ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p
  · exfalso
    obtain ⟨p, hp, hple⟩ := hmin
    have hpp : p.IsPrime := isPrime_of_mem_minimalPrimes_consolidated47 hp
    have hpm : p = maximalIdeal R := le_antisymm (IsLocalRing.le_maximalIdeal hpp.ne_top) hple
    have hallideal : ∀ q : Ideal R, q.IsPrime → q = maximalIdeal R := by
      intro q hq
      refine le_antisymm (IsLocalRing.le_maximalIdeal hq.ne_top) ?_
      rw [← hpm]
      exact le_of_le_of_mem_minimalPrimes_consolidated47 hp hq
        (by rw [hpm]; exact IsLocalRing.le_maximalIdeal hq.ne_top)
    have h2 : ringKrullDim R ≤ 0 := by
      have hPQ : ∀ P Q : PrimeSpectrum R, P = Q := by
        intro P Q
        apply PrimeSpectrum.ext
        rw [hallideal P.asIdeal P.isPrime, hallideal Q.asIdeal Q.isPrime]
      have : Subsingleton (PrimeSpectrum R) := ⟨hPQ⟩
      exact Order.krullDim_nonpos_of_subsingleton
    obtain ⟨x, hx, hx2⟩ : ∃ x, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 := by
      by_contra hc
      push Not at hc
      exact hsq fun y hy => hc y hy
    have := isLocalRing_quotient_span_singleton_consolidated47 hx
    have hpos := spanFinrank_maximalIdeal_quotient_add_one_le_finrank_consolidated47 R hx hx2
    have hdim : ringKrullDim R =
        (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) :=
      ((IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance).symm
    rw [hdim] at h2
    have hle0 : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 0 := by exact_mod_cast h2
    omega
  · obtain ⟨x, hx, hx2, hxp⟩ :=
      exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes_consolidated47 R hsq hmin
    have := isLocalRing_quotient_span_singleton_consolidated47 hx
    have hrq : IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) :=
      isRegularLocalRing_quotient_span_singleton hx hx2
    have hlt : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) <
        Submodule.spanFinrank (maximalIdeal R) := by
      have h1 := spanFinrank_maximalIdeal_quotient_add_one_le_finrank_consolidated47 R hx hx2
      have h2 : Submodule.spanFinrank (maximalIdeal R)
          = Module.finrank (ResidueField R) (CotangentSpace R) := by
        rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
      omega
    have hdom := IH (R ⧸ Ideal.span ({x} : Set R)) hlt
    have hprime : (Ideal.span ({x} : Set R)).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp hdom
    obtain ⟨p, hp, hple⟩ :=
      Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal R) ≤ Ideal.span ({x} : Set R))
    have hpp : p.IsPrime := isPrime_of_mem_minimalPrimes_consolidated47 hp
    have hpbot : p = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) p
        (IsNoetherian.noetherian p) ?_ (IsLocalRing.maximalIdeal_le_jacobson ⊥)
      intro y hy
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp (hple hy)
      have ha : a ∈ p := by
        rcases hpp.mem_or_mem hy with hh | hh
        · exact absurd hh (hxp p hp)
        · exact hh
      exact Ideal.mul_mem_mul hx ha
    rw [hpbot] at hpp
    have := hpp
    exact IsDomain.of_bot_isPrime R

private theorem isDomain_of_spanFinrank_le_consolidated47 :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
      Submodule.spanFinrank (maximalIdeal R) ≤ n → IsDomain R := by
  intro n
  induction n with
  | zero =>
    intro R _ _ h
    refine isDomain_of_forall_spanFinrank_lt_consolidated47 R ?_
    intro S _ _ hS
    exact absurd (lt_of_lt_of_le hS h) (Nat.not_lt_zero _)
  | succ n IH =>
    intro R _ _ h
    refine isDomain_of_forall_spanFinrank_lt_consolidated47 R ?_
    intro S _ _ hS
    exact IH S (by omega)

theorem isDomain (R : Type*) [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  isDomain_of_spanFinrank_le_consolidated47 (Submodule.spanFinrank (IsLocalRing.maximalIdeal R)) R le_rfl

instance (priority := 100) instIsDomain {R : Type*} [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  IsRegularLocalRing.isDomain R

private theorem false_of_eq_smul_of_linearIndependent_consolidated47 {K M : Type*} {ι : Type*} [Field K]
    [AddCommGroup M] [Module K M] {v : ι → M} (h : LinearIndependent K v) {i j : ι}
    (hij : i ≠ j) (c : K) (he : v j = c • v i) : False := by
  classical
  have key : ∑ k ∈ ({i, j} : Finset ι),
      (fun k => if k = i then c else if k = j then (-1 : K) else 0) k • v k = 0 := by
    rw [Finset.sum_pair hij]
    simp [Ne.symm hij, he]
  have h2 := linearIndependent_iff'.mp h {i, j}
      (fun k => if k = i then c else if k = j then (-1 : K) else 0) key j (by simp)
  simp [Ne.symm hij] at h2

private theorem toCotangent_mul_eq_smul_consolidated47 {R : Type*} [CommRing R] [IsLocalRing R] (r a : R)
    (ha : a ∈ IsLocalRing.maximalIdeal R) (hra : r * a ∈ IsLocalRing.maximalIdeal R) :
    ((IsLocalRing.maximalIdeal R).toCotangent ⟨r * a, hra⟩ : IsLocalRing.CotangentSpace R) =
      algebraMap R (IsLocalRing.ResidueField R) r •
        ((IsLocalRing.maximalIdeal R).toCotangent ⟨a, ha⟩ : IsLocalRing.CotangentSpace R) := by
  have h1 : (⟨r * a, hra⟩ : IsLocalRing.maximalIdeal R)
      = r • (⟨a, ha⟩ : IsLocalRing.maximalIdeal R) := Subtype.ext rfl
  rw [algebraMap_smul, h1, map_smul]

section
variable {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*} (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R) (hli : LinearIndependent (IsLocalRing.ResidueField R) (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ : ι → IsLocalRing.CotangentSpace R))
include hli

theorem notMem_maximalIdeal_sq (i : ι) : x i ∉ IsLocalRing.maximalIdeal R ^ 2 := by
  intro hmem
  have h0 : ((IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
      IsLocalRing.CotangentSpace R) = 0 := by
    rw [Ideal.toCotangent_eq_zero]
    exact hmem
  exact hli.ne_zero i h0

theorem isPrime_span_singleton (i : ι) : (Ideal.span ({x i} : Set R)).IsPrime := by
  have : IsRegularLocalRing (R ⧸ Ideal.span ({x i} : Set R)) :=
    isRegularLocalRing_quotient_span_singleton (hx i) (notMem_maximalIdeal_sq x hx hli i)
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact IsRegularLocalRing.isDomain _

theorem notMem_span_singleton {i j : ι} (hij : i ≠ j) : x j ∉ Ideal.span ({x i} : Set R) := by
  intro hmem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  have hmem2 : r * x i ∈ IsLocalRing.maximalIdeal R := by
    rw [hr]
    exact hx j
  have key : ((IsLocalRing.maximalIdeal R).toCotangent ⟨x j, hx j⟩ :
      IsLocalRing.CotangentSpace R)
      = algebraMap R (IsLocalRing.ResidueField R) r •
        ((IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
          IsLocalRing.CotangentSpace R) := by
    have hsub : (⟨x j, hx j⟩ : IsLocalRing.maximalIdeal R) = ⟨r * x i, hmem2⟩ :=
      Subtype.ext hr.symm
    rw [hsub]
    exact toCotangent_mul_eq_smul_consolidated47 r (x i) (hx i) hmem2
  exact false_of_eq_smul_of_linearIndependent_consolidated47 hli hij _ key


end

theorem isRadical_span_singleton_prod {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    [Fintype ι] (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R)) :
    (Ideal.span ({∏ i, x i} : Set R)).IsRadical := by
  classical
  exact FunctorialResolution.EmbeddedResolution.isRadical_span_singleton_prod_finset x Finset.univ
    (fun i _ => isPrime_span_singleton x hx hli i)
    (fun i _ j _ hij => notMem_span_singleton x hx hli hij)

end IsRegularLocalRing
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpensPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution


private theorem isReduced_of_isOpenImmersion_cover_consolidated80 {X : Scheme.{u}} {J : Type u} {V : J → Scheme.{u}}
    (m : (j : J) → V j ⟶ X) (hm : ∀ j, IsOpenImmersion (m j))
    (hV : ∀ j, IsReduced (V j))
    (hcov : ∀ x : ↥X, ∃ (j : J) (y : ↥(V j)), (m j).base y = x) :
    IsReduced X := by
  have : ∀ x : ↥X, _root_.IsReduced ↥(X.presheaf.stalk x) := by
    intro x
    obtain ⟨j, y, hy⟩ := hcov x
    have := hm j
    have := hV j
    subst hy
    exact isReduced_of_injective (CommRingCat.Hom.hom ((m j).stalkMap y))
      (asIso ((m j).stalkMap y)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk X

private theorem exists_sigma_ι_base_eq_consolidated80 {J : Type u} (f : J → Scheme.{u}) (x : ↥(∐ f)) :
    ∃ (j : J) (y : ↥(f j)), (Sigma.ι f j).base y = x := by
  refine ⟨((sigmaMk f).symm x).1, ((sigmaMk f).symm x).2, ?_⟩
  rw [← sigmaMk_mk]
  simp

section
variable {k : Type u} [Field k]

private theorem quasiCompact_of_compactSpace_to_spec_field_consolidated80 {V : Scheme.{u}}
    [CompactSpace ↥V] (f : V ⟶ Spec (CommRingCat.of k)) : QuasiCompact f := by
  have : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstance
  refine ⟨fun W hW hW' => ?_⟩
  rcases Set.eq_empty_or_nonempty W with rfl | ⟨z, hz⟩
  · simp
  · have hW2 : W = Set.univ := Set.eq_univ_of_forall fun w => by
      rw [Subsingleton.elim w z]; exact hz
    rw [hW2]
    simpa using isCompact_univ

private theorem quasiCompact_of_isAffine_of_locallyOfFiniteType_consolidated80 {W' : Scheme.{u}}
    [IsAffine W'] (q : W' ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q]
    {Z : Scheme.{u}} (g : W' ⟶ Z) : QuasiCompact g := by
  have hft : RingHom.FiniteType (q.appTop).hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)
      (Q := @RingHom.FiniteType) (f := q)).mp inferInstance
  let : Algebra ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(W', ⊤) := (q.appTop).hom.toAlgebra
  have : Algebra.FiniteType ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(W', ⊤) := hft
  have hk : IsNoetherianRing ↥(CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  have : IsNoetherianRing ↥Γ(Spec (CommRingCat.of k), ⊤) := by
    have e : ↥(CommRingCat.of k) ≃+* ↥Γ(Spec (CommRingCat.of k), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    exact isNoetherianRing_of_surjective ↥(CommRingCat.of k) ↥Γ(Spec (CommRingCat.of k), ⊤)
      e.toRingHom e.surjective
  have : IsNoetherianRing ↥Γ(W', ⊤) :=
    Algebra.FiniteType.isNoetherianRing ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(W', ⊤)
  have : TopologicalSpace.NoetherianSpace ↥(Spec Γ(W', ⊤)) :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (PrimeSpectrum ↥Γ(W', ⊤)))
  have e : ↥W' ≃ₜ ↥(Spec Γ(W', ⊤)) :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso W'.isoSpec)
  refine ⟨fun Vo hVo hVc => ?_⟩
  have he : IsCompact (e '' (⇑g ⁻¹' Vo)) := TopologicalSpace.NoetherianSpace.isCompact _
  rwa [Homeomorph.isCompact_image] at he


end

section
variable (Y : Scheme.{u}) {ι : Type u}

theorem isReduced_pullback_sigmaOpensDesc (U : ι → Y.Opens)
    (W' : Scheme.{u}) [IsReduced W'] (g' : W' ⟶ Y) :
    IsReduced (pullback g' (sigmaOpensDesc Y U)) := by
  refine isReduced_of_isOpenImmersion_cover_consolidated80
    (fun i => pullback.fst (pullback.snd g' (sigmaOpensDesc Y U))
      (Sigma.ι (fun j => (U j).toScheme) i)) (fun i => inferInstance) ?_ ?_
  · intro i
    have hoi : IsOpenImmersion
        (Sigma.ι (fun j => (U j).toScheme) i ≫ sigmaOpensDesc Y U) := by
      rw [sigma_ι_sigmaOpensDesc]
      infer_instance
    have : IsReduced
        (pullback g' (Sigma.ι (fun j => (U j).toScheme) i ≫ sigmaOpensDesc Y U)) :=
      isReduced_of_isOpenImmersion
        (pullback.fst g' (Sigma.ι (fun j => (U j).toScheme) i ≫ sigmaOpensDesc Y U))
    exact isReduced_of_isOpenImmersion
      (pullbackLeftPullbackSndIso g' (sigmaOpensDesc Y U)
        (Sigma.ι (fun j => (U j).toScheme) i)).hom
  · intro x
    obtain ⟨i, y, hy⟩ :=
      exists_sigma_ι_base_eq_consolidated80 (fun j => (U j).toScheme)
        ((pullback.snd g' (sigmaOpensDesc Y U)).base x)
    obtain ⟨z, hz1, _⟩ :=
      Scheme.Pullback.exists_preimage_pullback
        (f := pullback.snd g' (sigmaOpensDesc Y U))
        (g := Sigma.ι (fun j => (U j).toScheme) i) x y hy.symm
    exact ⟨i, z, hz1⟩

theorem compactSpace_pullback_sigmaOpensDesc [Finite ι]
    (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (W' : Scheme.{u}) (g' : W' ⟶ Y) [QuasiCompact g'] :
    CompactSpace ↥(pullback g' (sigmaOpensDesc Y U)) := by
  have : IsAffine (sigmaOpens Y U) := isAffine_sigmaOpens Y U hU
  have : CompactSpace ↥(sigmaOpens Y U) := inferInstance
  have : QuasiCompact (pullback.snd g' (sigmaOpensDesc Y U)) := inferInstance
  constructor
  have hcp := QuasiCompact.isCompact_preimage (f := pullback.snd g' (sigmaOpensDesc Y U))
    Set.univ isOpen_univ isCompact_univ
  simpa using hcp


end

theorem exists_affine_etale_cover_pullback_sigmaOpensDesc {k : Type u} [Field k]
    (Y : Scheme.{u}) (p : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [QuasiCompact p]
    {ι : Type u} [Finite ι] (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (W' : Scheme.{u}) [IsAffine W'] [IsReduced W'] (q : W' ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType q] [QuasiCompact q] (g' : W' ⟶ Y) [Etale g'] (_hg : g' ≫ p = q) :
    ∃ (V : Scheme.{u}) (s : V ⟶ Spec (CommRingCat.of k))
      (r : V ⟶ pullback g' (sigmaOpensDesc Y U)),
      IsAffine V ∧ IsReduced V ∧ LocallyOfFiniteType s ∧ QuasiCompact s ∧
        Etale r ∧ Surjective r ∧
        r ≫ pullback.fst g' (sigmaOpensDesc Y U) ≫ q = s := by
  have : QuasiCompact g' := quasiCompact_of_isAffine_of_locallyOfFiniteType_consolidated80 q g'
  have : IsReduced (pullback g' (sigmaOpensDesc Y U)) :=
    isReduced_pullback_sigmaOpensDesc Y U W' g'
  have : CompactSpace ↥(pullback g' (sigmaOpensDesc Y U)) :=
    compactSpace_pullback_sigmaOpensDesc Y U hU W' g'
  have : LocallyOfFiniteType (pullback.fst g' (sigmaOpensDesc Y U)) := inferInstance
  have : LocallyOfFiniteType (pullback.fst g' (sigmaOpensDesc Y U) ≫ q) := inferInstance
  have : QuasiCompact (pullback.fst g' (sigmaOpensDesc Y U) ≫ q) :=
    quasiCompact_of_compactSpace_to_spec_field_consolidated80 _
  obtain ⟨V, s, r, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_affine_etale_cover_of_isReduced (pullback g' (sigmaOpensDesc Y U))
      (pullback.fst g' (sigmaOpensDesc Y U) ≫ q)
  exact ⟨V, s, r, h1, h2, h3, h4, h5, h6, h7⟩

section
variable (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens)

theorem etale_comp_fst_pullback_sigmaOpensDesc (W' : Scheme.{u}) (g' : W' ⟶ Y) (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Etale r] :
    Etale (r ≫ pullback.fst g' (sigmaOpensDesc Y U)) := by
  have : Etale (pullback.fst g' (sigmaOpensDesc Y U)) := inferInstance
  infer_instance

theorem etale_comp_snd_pullback_sigmaOpensDesc (W' : Scheme.{u}) (g' : W' ⟶ Y) [Etale g'] (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Etale r] :
    Etale (r ≫ pullback.snd g' (sigmaOpensDesc Y U)) := by
  have : Etale (pullback.snd g' (sigmaOpensDesc Y U)) := inferInstance
  infer_instance

theorem surjective_comp_fst_pullback_sigmaOpensDesc (hU : iSup U = ⊤)
    (W' : Scheme.{u}) (g' : W' ⟶ Y) (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Surjective r] :
    Surjective (r ≫ pullback.fst g' (sigmaOpensDesc Y U)) := by
  have := surjective_sigmaOpensDesc Y U hU
  have : Surjective (pullback.fst g' (sigmaOpensDesc Y U)) := inferInstance
  infer_instance

theorem surjective_comp_snd_pullback_sigmaOpensDesc (W' : Scheme.{u}) (g' : W' ⟶ Y) [Surjective g'] (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Surjective r] :
    Surjective (r ≫ pullback.snd g' (sigmaOpensDesc Y U)) := by
  have : Surjective (pullback.snd g' (sigmaOpensDesc Y U)) := inferInstance
  infer_instance

theorem comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc (W' : Scheme.{u}) (g' : W' ⟶ Y) (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) :
    r ≫ pullback.fst g' (sigmaOpensDesc Y U) ≫ g' =
      r ≫ pullback.snd g' (sigmaOpensDesc Y U) ≫ sigmaOpensDesc Y U := by
  rw [pullback.condition]


end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
section

open CategoryTheory AlgebraicGeometry TensorProduct

namespace FunctorialResolution.EmbeddedResolution

private theorem lid_rTensor_subtype_mem_map_consolidated76 {R A' : Type*} [CommRing R] [CommRing A'] [Algebra R A']
    (K : Ideal R) (y : K ⊗[R] A') :
    (TensorProduct.lid R A') (LinearMap.rTensor A' K.subtype y) ∈ K.map (algebraMap R A') := by
  induction y using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero]
      exact Submodule.zero_mem _
  | tmul k a =>
      have hka : (TensorProduct.lid R A') (LinearMap.rTensor A' K.subtype (k ⊗ₜ[R] a))
          = (k : R) • a := by simp
      rw [hka, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ k.2)
  | add y z hy hz =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hy hz

private theorem algebraMap_tmul_one_eq_one_tmul_algebraMap_consolidated76 {A B A' : Type*} [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] (a : A) :
    (algebraMap A B a) ⊗ₜ[A] (1 : A') = (1 : B) ⊗ₜ[A] (algebraMap A A' a) := by
  calc (algebraMap A B a) ⊗ₜ[A] (1 : A') = (a • (1 : B)) ⊗ₜ[A] (1 : A') := by
        rw [Algebra.algebraMap_eq_smul_one]
    _ = a • ((1 : B) ⊗ₜ[A] (1 : A')) := TensorProduct.smul_tmul' a (1 : B) (1 : A')
    _ = (1 : B) ⊗ₜ[A] (a • (1 : A')) := (TensorProduct.tmul_smul a (1 : B) (1 : A')).symm
    _ = (1 : B) ⊗ₜ[A] (algebraMap A A' a) := by rw [Algebra.algebraMap_eq_smul_one]

theorem ker_includeRight_eq_map_ker (R B A' : Type*) [CommRing R] [CommRing B] [CommRing A']
    [Algebra R B] [Algebra R A'] [Module.Flat R A'] :
    RingHom.ker (Algebra.TensorProduct.includeRight : A' →ₐ[R] B ⊗[R] A').toRingHom =
      (RingHom.ker (algebraMap R B)).map (algebraMap R A') := by
  have hex : Function.Exact ((RingHom.ker (algebraMap R B)).subtype) (Algebra.linearMap R B) := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
    ext r
    simp [RingHom.mem_ker]
  have hflat : Function.Exact
      (LinearMap.rTensor A' ((RingHom.ker (algebraMap R B)).subtype))
      (LinearMap.rTensor A' (Algebra.linearMap R B)) :=
    Module.Flat.rTensor_exact (R := R) (M := A') hex
  apply le_antisymm
  · intro x hx
    have hx0 : (1 : B) ⊗ₜ[R] x = 0 := by
      simpa [RingHom.mem_ker, Algebra.TensorProduct.includeRight_apply,
        AlgHom.toRingHom_eq_coe] using hx
    have key : (LinearMap.rTensor A' (Algebra.linearMap R B)) ((1 : R) ⊗ₜ[R] x) = 0 := by
      simpa using hx0
    have hmem : (1 : R) ⊗ₜ[R] x ∈
        LinearMap.range (LinearMap.rTensor A' ((RingHom.ker (algebraMap R B)).subtype)) := by
      rw [← LinearMap.exact_iff.mp hflat]
      exact LinearMap.mem_ker.mpr key
    obtain ⟨y, hy⟩ := hmem
    have hx1 : x = (TensorProduct.lid R A') ((1 : R) ⊗ₜ[R] x) := by simp
    rw [hx1, ← hy]
    exact lid_rTensor_subtype_mem_map_consolidated76 _ y
  · rw [Ideal.map_le_iff_le_comap]
    intro k hk
    have hk0 : algebraMap R B k = 0 := RingHom.mem_ker.mp hk
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have e1 : (Algebra.TensorProduct.includeRight : A' →ₐ[R] B ⊗[R] A')
        (algebraMap R A' k) = 0 := by
      rw [Algebra.TensorProduct.includeRight_apply, ← algebraMap_tmul_one_eq_one_tmul_algebraMap_consolidated76, hk0,
        TensorProduct.zero_tmul]
    exact e1

theorem quasiCompact_of_isPullback {Z X X' Z' : Scheme.{u}} {h : Z ⟶ X} {g : X' ⟶ X}
    {g' : Z' ⟶ Z} {h' : Z' ⟶ X'} (H : IsPullback g' h' h g) [QuasiCompact h] :
    QuasiCompact h' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) H ‹QuasiCompact h›

private theorem exists_pow_mul_mem_of_map_le_consolidated76 {A Af : Type*} [CommRing A] [CommRing Af]
    [Algebra A Af] (f : A) [IsLocalization.Away f Af] {I J : Ideal A}
    (hle : I.map (algebraMap A Af) ≤ J.map (algebraMap A Af)) {x : A} (hx : x ∈ I) :
    ∃ n : ℕ, f ^ n * x ∈ J := by
  have hmem : algebraMap A Af x ∈ J.map (algebraMap A Af) :=
    hle (Ideal.mem_map_of_mem _ hx)
  rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) Af] at hmem
  obtain ⟨⟨⟨y, hy⟩, ⟨m, hm⟩⟩, hxy⟩ := hmem
  obtain ⟨k, hk⟩ := hm
  have hk' : f ^ k = m := hk
  rw [← map_mul] at hxy
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers f) Af).mp hxy
  obtain ⟨l, hl⟩ := c.2
  have hl' : f ^ l = (c : A) := hl
  have hc' : (c : A) * (x * m) = (c : A) * y := hc
  refine ⟨l + k, ?_⟩
  have key : f ^ (l + k) * x = (c : A) * (x * m) := by
    rw [pow_add, hl', ← hk']; ring
  rw [key, hc']
  exact Ideal.mul_mem_left _ _ hy

private theorem ideal_eq_of_span_eq_top_consolidated76 {A : Type*} [CommRing A] {I J : Ideal A} {s : Set A}
    (hspan : Ideal.span s = ⊤)
    (hIJ : ∀ f ∈ s, ∀ x ∈ I, ∃ n : ℕ, f ^ n * x ∈ J)
    (hJI : ∀ f ∈ s, ∀ x ∈ J, ∃ n : ℕ, f ^ n * x ∈ I) : I = J := by
  apply le_antisymm
  · intro x hx
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem J s hspan x ?_
    rintro ⟨f, hf⟩
    obtain ⟨n, hn⟩ := hIJ f hf x hx
    exact ⟨n, by simpa [smul_eq_mul] using hn⟩
  · intro x hx
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem I s hspan x ?_
    rintro ⟨f, hf⟩
    obtain ⟨n, hn⟩ := hJI f hf x hx
    exact ⟨n, by simpa [smul_eq_mul] using hn⟩

section
variable {X : Scheme.{u}}

private theorem ideal_eq_of_ideal_affineBasicOpen_eq_consolidated76 (I J : X.IdealSheafData) (V : X.affineOpens)
    (s : Set Γ(X, (V : X.Opens))) (hspan : Ideal.span s = ⊤)
    (hs : ∀ f ∈ s, I.ideal (X.affineBasicOpen f) = J.ideal (X.affineBasicOpen f)) :
    I.ideal V = J.ideal V := by
  have key : ∀ I J : X.IdealSheafData,
      (∀ f ∈ s, I.ideal (X.affineBasicOpen f) = J.ideal (X.affineBasicOpen f)) →
      ∀ f ∈ s, ∀ x ∈ I.ideal V, ∃ n : ℕ, f ^ n * x ∈ J.ideal V := by
    intro I J hs f hf x hx
    have := V.2.isLocalization_basicOpen f
    have hmap : (I.ideal V).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
        = (J.ideal V).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom := by
      rw [I.map_ideal_basicOpen V f, J.map_ideal_basicOpen V f, hs f hf]
    exact exists_pow_mul_mem_of_map_le_consolidated76 (Af := ↑Γ(X, X.basicOpen f)) f (le_of_eq hmap) hx
  exact ideal_eq_of_span_eq_top_consolidated76 hspan (key I J hs) (key J I fun f hf => (hs f hf).symm)

private theorem span_eq_top_of_le_iSup_basicOpen_consolidated76 (V : X.affineOpens)
    (s : Set ↑Γ(X, (V : X.Opens)))
    (hcov : (V : X.Opens) ≤ ⨆ f : s, X.basicOpen (f : ↑Γ(X, (V : X.Opens)))) :
    Ideal.span s = ⊤ :=
  (V.2.self_le_iSup_basicOpen_iff (s := s)).mp hcov


end

private theorem appLE_congr_of_eq_consolidated76 {X Y : Scheme.{u}} {f f' : X ⟶ Y} (hf : f = f')
    (U : Y.Opens) (W : X.Opens) (e : W ≤ f ⁻¹ᵁ U) (e' : W ≤ f' ⁻¹ᵁ U) :
    f.appLE U W e = f'.appLE U W e' := by
  subst hf; rfl

section
variable {R A' : Type*} [CommRing R] [CommRing A'] [Algebra R A']

private theorem pi_one_tmul_eq_zero_of_forall_consolidated76 {ι : Type*} [Fintype ι] [DecidableEq ι] (B : ι → Type*) [∀ j, CommRing (B j)]
    [∀ j, Algebra R (B j)] (s : A') (hs : ∀ j, (1 : B j) ⊗ₜ[R] s = 0) :
    (1 : ∀ j, B j) ⊗ₜ[R] s = 0 := by
  have h1 : (1 : ∀ j, B j) = ∑ j : ι, Pi.single j (1 : B j) := by
    ext k
    simp [Finset.sum_apply]
  rw [h1, TensorProduct.sum_tmul]
  refine Finset.sum_eq_zero ?_
  intro j _
  have h2 : (Pi.single j (1 : B j)) ⊗ₜ[R] s
      = LinearMap.rTensor A' (LinearMap.single R B j) ((1 : B j) ⊗ₜ[R] s) := by
    simp
  rw [h2, hs j, map_zero]

private theorem mem_map_iInf_ker_of_forall_one_tmul_eq_zero_consolidated76 [Module.Flat R A'] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ι → Type*) [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)] (s : A')
    (hs : ∀ j, (1 : B j) ⊗ₜ[R] s = 0) :
    s ∈ Ideal.map (algebraMap R A') (⨅ j, RingHom.ker (algebraMap R (B j))) := by
  have h0 : (1 : ∀ j, B j) ⊗ₜ[R] s = 0 := pi_one_tmul_eq_zero_of_forall_consolidated76 B s hs
  have hk : RingHom.ker (algebraMap R (∀ j, B j)) = ⨅ j, RingHom.ker (algebraMap R (B j)) := by
    ext r
    simp [RingHom.mem_ker, Submodule.mem_iInf, funext_iff]
  rw [← hk, ← ker_includeRight_eq_map_ker R (∀ j, B j) A']
  simpa [RingHom.mem_ker] using h0


end

private theorem exists_affineOpen_le_of_mem_consolidated76 {Z : Scheme.{u}} (K : Z.Opens) (z : Z) (hz : z ∈ K) :
    ∃ W : Z.affineOpens, (W : Z.Opens) ≤ K ∧ z ∈ (W : Z.Opens) := by
  obtain ⟨y, hy⟩ := Z.affineCover.covers z
  have hWaff : IsAffineOpen (Z.affineCover.f (Z.affineCover.idx z)).opensRange :=
    isAffineOpen_opensRange _
  have hz1 : z ∈ (Z.affineCover.f (Z.affineCover.idx z)).opensRange := ⟨y, hy⟩
  obtain ⟨f, hfle, hzf⟩ := hWaff.exists_basicOpen_le (V := K) ⟨z, hz⟩ hz1
  exact ⟨⟨Z.basicOpen f, hWaff.basicOpen f⟩, hfle, hzf⟩

private theorem appLE_top_comp_ΓSpecIso_hom_consolidated76 {Y : Scheme.{u}} {V : Y.Opens} (hV : IsAffineOpen V)
    {S : CommRingCat.{u}} (ρ : Γ(Y, V) ⟶ S) (q : Spec S ⟶ Y)
    (hqe : q = Spec.map ρ ≫ hV.fromSpec) (e : (⊤ : (Spec S).Opens) ≤ q ⁻¹ᵁ V) :
    q.appLE V ⊤ e ≫ (Scheme.ΓSpecIso S).hom = ρ := by
  subst hqe
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  have h1 : Spec.map ((Spec.map ρ ≫ hV.fromSpec).appLE V ⊤ e) ≫ hV.fromSpec
      = (isAffineOpen_top (Spec S)).fromSpec ≫ (Spec.map ρ ≫ hV.fromSpec) :=
    IsAffineOpen.SpecMap_appLE_fromSpec _ hV (isAffineOpen_top (Spec S)) e
  have h2 : (isAffineOpen_top (Spec S)).fromSpec = Spec.map (Scheme.ΓSpecIso S).inv := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  rw [h2, ← Category.assoc, ← Spec.map_comp] at h1
  have h3 := (cancel_mono hV.fromSpec).mp h1
  have h4 := Spec.map_injective h3
  rw [h4, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem one_tmul_eq_zero_of_app_eq_zero_consolidated76 {Z X X' Z' : Scheme.{u}} {h : Z ⟶ X} {g : X' ⟶ X}
    {g' : Z' ⟶ Z} {h' : Z' ⟶ X'} (H : IsPullback g' h' h g)
    (U : X.affineOpens) (V : X'.affineOpens) (e : (V : X'.Opens) ≤ g ⁻¹ᵁ (U : X.Opens))
    (W : Z.affineOpens) (hW : (W : Z.Opens) ≤ h ⁻¹ᵁ (U : X.Opens))
    [Algebra ↑Γ(X, (U : X.Opens)) ↑Γ(X', (V : X'.Opens))]
    [Algebra ↑Γ(X, (U : X.Opens)) ↑Γ(Z, (W : Z.Opens))]
    (hVa : (algebraMap ↑Γ(X, (U : X.Opens)) ↑Γ(X', (V : X'.Opens)))
        = (g.appLE (U : X.Opens) (V : X'.Opens) e).hom)
    (hWa : (algebraMap ↑Γ(X, (U : X.Opens)) ↑Γ(Z, (W : Z.Opens)))
        = (h.appLE (U : X.Opens) (W : Z.Opens) hW).hom)
    (s : ↑Γ(X', (V : X'.Opens))) (hs : (h'.app (V : X'.Opens)).hom s = 0) :
    (1 : ↑Γ(Z, (W : Z.Opens))) ⊗ₜ[↑Γ(X, (U : X.Opens))] s = 0 := by
  have hUaff : IsAffineOpen (U : X.Opens) := U.2
  have hVaff : IsAffineOpen (V : X'.Opens) := V.2
  have hWaff : IsAffineOpen (W : Z.Opens) := W.2
  set T : CommRingCat.{u} :=
    CommRingCat.of (↑Γ(Z, (W : Z.Opens)) ⊗[↑Γ(X, (U : X.Opens))] ↑Γ(X', (V : X'.Opens))) with hT
  set il : Γ(Z, (W : Z.Opens)) ⟶ T :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom) with hil
  set ir : Γ(X', (V : X'.Opens)) ⟶ T :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight).toRingHom with hir
  have h3 : h.appLE (U : X.Opens) (W : Z.Opens) hW ≫ il
      = g.appLE (U : X.Opens) (V : X'.Opens) e ≫ ir := by
    ext a
    show ((h.appLE (U : X.Opens) (W : Z.Opens) hW).hom a) ⊗ₜ[↑Γ(X, (U : X.Opens))]
        (1 : ↑Γ(X', (V : X'.Opens)))
      = (1 : ↑Γ(Z, (W : Z.Opens))) ⊗ₜ[↑Γ(X, (U : X.Opens))]
        ((g.appLE (U : X.Opens) (V : X'.Opens) e).hom a)
    rw [← hWa, ← hVa]
    exact algebraMap_tmul_one_eq_one_tmul_algebraMap_consolidated76 a
  set p : Spec T ⟶ Z := Spec.map il ≫ hWaff.fromSpec with hp
  set q : Spec T ⟶ X' := Spec.map ir ≫ hVaff.fromSpec with hq
  have hcomm : p ≫ h = q ≫ g := by
    have h1 : Spec.map (h.appLE (U : X.Opens) (W : Z.Opens) hW) ≫ hUaff.fromSpec
        = hWaff.fromSpec ≫ h := IsAffineOpen.SpecMap_appLE_fromSpec h hUaff hWaff hW
    have h2 : Spec.map (g.appLE (U : X.Opens) (V : X'.Opens) e) ≫ hUaff.fromSpec
        = hVaff.fromSpec ≫ g := IsAffineOpen.SpecMap_appLE_fromSpec g hUaff hVaff e
    calc p ≫ h = Spec.map il ≫ (hWaff.fromSpec ≫ h) := by rw [hp, Category.assoc]
      _ = Spec.map il ≫ Spec.map (h.appLE (U : X.Opens) (W : Z.Opens) hW) ≫ hUaff.fromSpec := by
          rw [h1]
      _ = Spec.map (h.appLE (U : X.Opens) (W : Z.Opens) hW ≫ il) ≫ hUaff.fromSpec := by
          rw [Spec.map_comp, Category.assoc]
      _ = Spec.map (g.appLE (U : X.Opens) (V : X'.Opens) e ≫ ir) ≫ hUaff.fromSpec := by rw [h3]
      _ = Spec.map ir ≫ Spec.map (g.appLE (U : X.Opens) (V : X'.Opens) e) ≫ hUaff.fromSpec := by
          rw [Spec.map_comp, Category.assoc]
      _ = Spec.map ir ≫ (hVaff.fromSpec ≫ g) := by rw [h2]
      _ = q ≫ g := by rw [hq, Category.assoc]
  have hr : H.lift p q hcomm ≫ h' = q := H.lift_snd p q hcomm
  have hqpre : q ⁻¹ᵁ (V : X'.Opens) = ⊤ := by
    rw [hq, Scheme.Hom.comp_preimage, hVaff.fromSpec_preimage_self, Scheme.Hom.preimage_top]
  have e1 : (⊤ : (Spec T).Opens) ≤ q ⁻¹ᵁ (V : X'.Opens) := hqpre.ge
  have hrp : H.lift p q hcomm ⁻¹ᵁ (h' ⁻¹ᵁ (V : X'.Opens)) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, hr, hqpre]
  have e2 : (⊤ : (Spec T).Opens) ≤ H.lift p q hcomm ⁻¹ᵁ (h' ⁻¹ᵁ (V : X'.Opens)) := hrp.ge
  have hsplit : q.appLE (V : X'.Opens) ⊤ e1
      = h'.appLE (V : X'.Opens) (h' ⁻¹ᵁ (V : X'.Opens)) le_rfl
        ≫ (H.lift p q hcomm).appLE (h' ⁻¹ᵁ (V : X'.Opens)) ⊤ e2 := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr_of_eq_consolidated76 hr.symm _ _ _ _
  have hA : (q.appLE (V : X'.Opens) ⊤ e1).hom s = 0 := by
    rw [hsplit]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [← Scheme.Hom.app_eq_appLE h' (U := (V : X'.Opens)), hs, map_zero]
  have hfin : q.appLE (V : X'.Opens) ⊤ e1 ≫ (Scheme.ΓSpecIso T).hom = ir :=
    appLE_top_comp_ΓSpecIso_hom_consolidated76 hVaff ir q hq e1
  have step : ir.hom s = 0 := by
    rw [← hfin]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [hA, map_zero]
  exact step

section
variable {Z X X' Z' : Scheme.{u}} {h : Z ⟶ X} {g : X' ⟶ X} {g' : Z' ⟶ Z} {h' : Z' ⟶ X'} (H : IsPullback g' h' h g) [QuasiCompact h]
include H

private theorem ker_app_eq_map_ker_of_isPullback_of_flat_consolidated76 [Flat g] (U : X.affineOpens) (V : X'.affineOpens)
    (e : (V : X'.Opens) ≤ g ⁻¹ᵁ (U : X.Opens)) :
    RingHom.ker (h'.app (V : X'.Opens)).hom =
      Ideal.map (g.appLE (U : X.Opens) (V : X'.Opens) e).hom
        (RingHom.ker (h.app (U : X.Opens)).hom) := by
  classical
  have hpre : h' ⁻¹ᵁ (V : X'.Opens) ≤ g' ⁻¹ᵁ (h ⁻¹ᵁ (U : X.Opens)) := by
    rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
    exact fun x hx => e hx
  have hcomm : h.appLE (U : X.Opens) (h ⁻¹ᵁ (U : X.Opens)) le_rfl
      ≫ g'.appLE (h ⁻¹ᵁ (U : X.Opens)) (h' ⁻¹ᵁ (V : X'.Opens)) hpre
      = g.appLE (U : X.Opens) (V : X'.Opens) e
        ≫ h'.appLE (V : X'.Opens) (h' ⁻¹ᵁ (V : X'.Opens)) le_rfl := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr_of_eq_consolidated76 H.w _ _ _ _
  apply le_antisymm
  · intro s hs
    have hs0 : (h'.app (V : X'.Opens)).hom s = 0 := RingHom.mem_ker.mp hs
    have hKc : IsCompact (((h ⁻¹ᵁ (U : X.Opens)) : Z.Opens) : Set Z) :=
      QuasiCompact.isCompact_preimage (f := h) (((U : X.Opens)) : Set X)
        (U : X.Opens).isOpen U.2.isCompact
    have hcov : (((h ⁻¹ᵁ (U : X.Opens)) : Z.Opens) : Set Z)
        ⊆ ⋃ W : {W : Z.affineOpens // (W : Z.Opens) ≤ h ⁻¹ᵁ (U : X.Opens)},
            (((W.1 : Z.affineOpens) : Z.Opens) : Set Z) := by
      intro z hz
      obtain ⟨W, hW1, hW2⟩ := exists_affineOpen_le_of_mem_consolidated76 (h ⁻¹ᵁ (U : X.Opens)) z hz
      exact Set.mem_iUnion.mpr ⟨⟨W, hW1⟩, hW2⟩
    obtain ⟨t, ht⟩ := hKc.elim_finite_subcover
      (fun W : {W : Z.affineOpens // (W : Z.Opens) ≤ h ⁻¹ᵁ (U : X.Opens)} =>
        (((W.1 : Z.affineOpens) : Z.Opens) : Set Z))
      (fun W => ((W.1 : Z.affineOpens) : Z.Opens).isOpen) hcov
    let _ : Algebra ↑Γ(X, (U : X.Opens)) ↑Γ(X', (V : X'.Opens)) :=
      (g.appLE (U : X.Opens) (V : X'.Opens) e).hom.toAlgebra
    have hflat : RingHom.Flat (g.appLE (U : X.Opens) (V : X'.Opens) e).hom :=
      AlgebraicGeometry.HasRingHomProperty.appLE (P := @Flat) g ‹_› U V e
    have : Module.Flat ↑Γ(X, (U : X.Opens)) ↑Γ(X', (V : X'.Opens)) := hflat
    let _ : ∀ j : {x // x ∈ t},
        Algebra ↑Γ(X, (U : X.Opens)) ↑Γ(Z, ((j.1.1 : Z.affineOpens) : Z.Opens)) :=
      fun j => (h.appLE (U : X.Opens) ((j.1.1 : Z.affineOpens) : Z.Opens) j.1.2).hom.toAlgebra
    have hzero : ∀ j : {x // x ∈ t},
        (1 : ↑Γ(Z, ((j.1.1 : Z.affineOpens) : Z.Opens)))
          ⊗ₜ[↑Γ(X, (U : X.Opens))] s = 0 := by
      intro j
      exact one_tmul_eq_zero_of_app_eq_zero_consolidated76 H U V e j.1.1 j.1.2 rfl rfl s hs0
    have hmem := mem_map_iInf_ker_of_forall_one_tmul_eq_zero_consolidated76
      (fun j : {x // x ∈ t} => ↑Γ(Z, ((j.1.1 : Z.affineOpens) : Z.Opens))) s hzero
    have hcover2 : (h ⁻¹ᵁ (U : X.Opens))
        ≤ ⨆ j : {x // x ∈ t}, ((j.1.1 : Z.affineOpens) : Z.Opens) := by
      intro z hz
      obtain ⟨W, hW1, hW2⟩ := Set.mem_iUnion₂.mp (ht hz)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hW1⟩, hW2⟩
    have hker : (⨅ j : {x // x ∈ t}, RingHom.ker
          (algebraMap ↑Γ(X, (U : X.Opens)) ↑Γ(Z, ((j.1.1 : Z.affineOpens) : Z.Opens))))
        ≤ RingHom.ker (h.app (U : X.Opens)).hom := by
      intro a ha
      rw [RingHom.mem_ker]
      refine Z.sheaf.eq_of_locally_eq'
        (fun j : {x // x ∈ t} => ((j.1.1 : Z.affineOpens) : Z.Opens))
        (h ⁻¹ᵁ (U : X.Opens)) (fun j => homOfLE j.1.2) hcover2 _ 0 ?_
      intro j
      have ha' : (algebraMap ↑Γ(X, (U : X.Opens))
          ↑Γ(Z, ((j.1.1 : Z.affineOpens) : Z.Opens))) a = 0 :=
        RingHom.mem_ker.mp ((Submodule.mem_iInf _).mp ha j)
      have ha3 : (Z.presheaf.map (homOfLE j.1.2).op).hom
          ((h.app (U : X.Opens)).hom a) = 0 := ha'
      refine ha3.trans ?_
      exact (map_zero _).symm
    exact Ideal.map_mono hker hmem
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have h1 := congrArg (fun m : Γ(X, (U : X.Opens)) ⟶ Γ(Z', h' ⁻¹ᵁ (V : X'.Opens)) =>
      (CommRingCat.Hom.hom m) a) hcomm
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h1
    have hzero : (h.appLE (U : X.Opens) (h ⁻¹ᵁ (U : X.Opens)) le_rfl).hom a = 0 := by
      rw [← Scheme.Hom.app_eq_appLE h (U := (U : X.Opens))]
      exact RingHom.mem_ker.mp ha
    rw [Scheme.Hom.app_eq_appLE h' (U := (V : X'.Opens)), ← h1, hzero, map_zero]

theorem ker_eq_comap_ker_of_isPullback_of_flat [QuasiCompact h'] [Flat g] :
    h'.ker = h.ker.comap g := by
  classical
  apply Scheme.IdealSheafData.ext
  funext V
  set s : Set Γ(X', (V : X'.Opens)) :=
    {f | ∃ U : X.affineOpens, X'.basicOpen f ≤ g ⁻¹ᵁ (U : X.Opens)} with hsdef
  have hs : ∀ f ∈ s, h'.ker.ideal (X'.affineBasicOpen f)
      = (h.ker.comap g).ideal (X'.affineBasicOpen f) := by
    rintro f ⟨U, hU⟩
    have hV' : ((X'.affineBasicOpen f : X'.affineOpens) : X'.Opens) ≤ g ⁻¹ᵁ (U : X.Opens) := hU
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE h.ker g U
      (X'.affineBasicOpen f) hV', Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
    exact ker_app_eq_map_ker_of_isPullback_of_flat_consolidated76 H U (X'.affineBasicOpen f) hV'
  have hspan : Ideal.span s = ⊤ := by
    refine span_eq_top_of_le_iSup_basicOpen_consolidated76 V s ?_
    intro x hx
    obtain ⟨y, hy⟩ := X.affineCover.covers (g.base x)
    have hUaff : IsAffineOpen (X.affineCover.f (X.affineCover.idx (g.base x))).opensRange :=
      isAffineOpen_opensRange _
    have hgx : g.base x ∈ (X.affineCover.f (X.affineCover.idx (g.base x))).opensRange := ⟨y, hy⟩
    have hx2 : x ∈ ((V : X'.Opens) ⊓
        g ⁻¹ᵁ (X.affineCover.f (X.affineCover.idx (g.base x))).opensRange) := ⟨hx, hgx⟩
    obtain ⟨f, hfle, hxf⟩ := V.2.exists_basicOpen_le
      (V := (V : X'.Opens) ⊓ g ⁻¹ᵁ (X.affineCover.f (X.affineCover.idx (g.base x))).opensRange)
      ⟨x, hx2⟩ hx
    have hfs : f ∈ s :=
      ⟨⟨(X.affineCover.f (X.affineCover.idx (g.base x))).opensRange, hUaff⟩,
        le_trans hfle inf_le_right⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hfs⟩, hxf⟩
  exact ideal_eq_of_ideal_affineBasicOpen_eq_consolidated76 _ _ V s hspan hs


end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
section
section


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

section
namespace FunctorialResolution.Blowup

def IsLocallyGeneratedByNonZeroDivisor {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ (U : X.affineOpens) (f : Γ(X, U.1)),
    x ∈ U.1 ∧ f ∈ nonZeroDivisors Γ(X, U.1) ∧ I.ideal U = Ideal.span {f}

def IsBlowupAlongIdealSheaf {X X' : Scheme.{u}} (π : X' ⟶ X) (I : X.IdealSheafData) : Prop :=
  IsLocallyGeneratedByNonZeroDivisor (I.comap π) ∧
    ∀ (W : Scheme.{u}) (g : W ⟶ X), IsLocallyGeneratedByNonZeroDivisor (I.comap g) →
      ∃! h : W ⟶ X', h ≫ π = g

end FunctorialResolution.Blowup

end

end
end

-- Source: Development.ResolutionOfSingularities.Foundations.Blowup.ReesGrading
section
open Polynomial

namespace FunctorialResolution.Blowup

variable {R : Type*} [CommRing R]

section
variable (I : Ideal R)

private theorem mem_pow_one_consolidated33 {a : R} (ha : a ∈ I) : a ∈ I ^ 1 := by
  rwa [pow_one]

private theorem mem_pow_zero_consolidated33 (r : R) : r ∈ I ^ 0 := by
  rw [pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top


end

noncomputable def reesGrading (I : Ideal R) (n : ℕ) : Submodule R ↥(reesAlgebra I) :=
  Submodule.comap (reesAlgebra I).val.toLinearMap
    (LinearMap.range (Polynomial.monomial (R := R) n))

section
variable (I : Ideal R) (n : ℕ) (p : ↥(reesAlgebra I))

theorem mem_reesGrading_iff_monomial :
    p ∈ reesGrading I n ↔ ∃ r ∈ I ^ n, (p : R[X]) = Polynomial.monomial n r := by
  have hmem : p ∈ reesGrading I n ↔ ∃ r : R, Polynomial.monomial n r = (p : R[X]) := Iff.rfl
  rw [hmem]
  constructor
  · rintro ⟨r, hr⟩
    have hp : (p : R[X]).coeff n ∈ I ^ n := (mem_reesAlgebra_iff I _).mp p.2 n
    have hcoef : (Polynomial.monomial n r : R[X]).coeff n = r := by simp
    rw [← hr, hcoef] at hp
    exact ⟨r, hp, hr.symm⟩
  · rintro ⟨r, -, hpr⟩
    exact ⟨r, hpr.symm⟩

theorem mem_reesGrading_iff_coeff :
    p ∈ reesGrading I n ↔ ∀ i, i ≠ n → (p : R[X]).coeff i = 0 := by
  have key : p ∈ reesGrading I n ↔ ∃ r : R, Polynomial.monomial n r = (p : R[X]) := Iff.rfl
  rw [key]
  constructor
  · rintro ⟨r, hr⟩ i hi
    rw [← hr, Polynomial.coeff_monomial, if_neg (Ne.symm hi)]
  · intro h
    refine ⟨(p : R[X]).coeff n, ?_⟩
    ext i
    rcases eq_or_ne i n with rfl | hi
    · simp
    · simp [Polynomial.coeff_monomial, Ne.symm hi, h i hi]


end

section
variable (I : Ideal R)

theorem reesGrading_one_mem : (1 : ↥(reesAlgebra I)) ∈ reesGrading I 0 := by
  show ((1 : ↥(reesAlgebra I)) : R[X]) ∈ LinearMap.range (Polynomial.monomial (R := R) 0)
  refine LinearMap.mem_range.2 ⟨1, ?_⟩
  simp

theorem reesGrading_mul_mem {m n : ℕ} {p q : ↥(reesAlgebra I)}
    (hp : p ∈ reesGrading I m) (hq : q ∈ reesGrading I n) :
    p * q ∈ reesGrading I (m + n) := by
  have key : ∀ (k : ℕ) (x : ↥(reesAlgebra I)),
      x ∈ reesGrading I k ↔ ∃ r : R, Polynomial.monomial k r = (x : R[X]) :=
    fun _ _ => Iff.rfl
  obtain ⟨a, ha⟩ := (key m p).1 hp
  obtain ⟨b, hb⟩ := (key n q).1 hq
  refine (key (m + n) (p * q)).2 ⟨a * b, ?_⟩
  have hpq : ((p * q : ↥(reesAlgebra I)) : R[X]) = (p : R[X]) * (q : R[X]) := rfl
  rw [hpq, ← ha, ← hb, Polynomial.monomial_mul_monomial]


end

instance instGradedMonoidReesGrading (I : Ideal R) : SetLike.GradedMonoid (reesGrading I) where
  one_mem := reesGrading_one_mem I
  mul_mem := @fun _ _ _ _ hp hq => reesGrading_mul_mem I hp hq

section
variable (I : Ideal R)

theorem reesGrading_iSupIndep : iSupIndep (reesGrading I) := by
  intro n
  rw [Submodule.disjoint_def]
  intro p hp hp'
  have hcoeff : ∀ i, i ≠ n → (p : R[X]).coeff i = 0 :=
    (mem_reesGrading_iff_coeff I n p).1 hp
  have hker : (⨆ (j : ℕ) (_ : j ≠ n), reesGrading I j) ≤
      LinearMap.ker ((Polynomial.lcoeff R n).comp ((reesAlgebra I).val.toLinearMap)) := by
    refine iSup_le fun j => iSup_le fun hj => ?_
    intro x hx
    have hx' := (mem_reesGrading_iff_coeff I j x).1 hx n (Ne.symm hj)
    simpa [LinearMap.mem_ker, Polynomial.lcoeff_apply] using hx'
  have hpn : (p : R[X]).coeff n = 0 := by
    have h := hker hp'
    simpa [LinearMap.mem_ker, Polynomial.lcoeff_apply] using h
  have hp0 : (p : R[X]) = 0 := by
    ext i
    rcases eq_or_ne i n with rfl | hi
    · simpa using hpn
    · simpa using hcoeff i hi
  exact Subtype.ext (by simpa using hp0)

private theorem coeff_mem_pow_consolidated33 (p : ↥(reesAlgebra I)) (i : ℕ) :
    ((p : R[X])).coeff i ∈ I ^ i := p.2 i

private theorem monomial_mem_reesGrading_consolidated33 {n : ℕ} {r : R} (hr : r ∈ I ^ n) :
    (⟨Polynomial.monomial n r, reesAlgebra.monomial_mem.mpr hr⟩ : ↥(reesAlgebra I))
      ∈ reesGrading I n := by
  refine (mem_reesGrading_iff_coeff I n _).2 fun i hi => ?_
  show (Polynomial.monomial n r : R[X]).coeff i = 0
  rw [Polynomial.coeff_monomial, if_neg (Ne.symm hi)]

theorem reesGrading_iSup_eq_top : (⨆ n : ℕ, reesGrading I n) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun p => ?_
  have hval : ∀ x y : ↥(reesAlgebra I),
      (reesAlgebra I).val x = (reesAlgebra I).val y → x = y := fun _ _ h => Subtype.ext h
  have hsum : p = ∑ i ∈ (p : R[X]).support,
      (⟨Polynomial.monomial i ((p : R[X]).coeff i),
        reesAlgebra.monomial_mem.mpr (coeff_mem_pow_consolidated33 I p i)⟩ : ↥(reesAlgebra I)) :=
    hval _ _ (by rw [map_sum]; exact Polynomial.as_sum_support _)
  rw [hsum]
  exact sum_mem fun i _ => Submodule.mem_iSup_of_mem i
    (monomial_mem_reesGrading_consolidated33 I (coeff_mem_pow_consolidated33 I p i))

theorem reesGrading_isInternal : DirectSum.IsInternal (reesGrading I) := by
  exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (reesGrading I)).2
    ⟨reesGrading_iSupIndep I, reesGrading_iSup_eq_top I⟩


end

private noncomputable def directSumReesGradingEquiv (I : Ideal R) :
    DirectSum ℕ (fun n => ↥(reesGrading I n)) ≃ ↥(reesAlgebra I) :=
  Equiv.ofBijective (DirectSum.coeAddMonoidHom (reesGrading I)) (reesGrading_isInternal I)

section
variable (I : Ideal R)

private theorem leftInverse_coeAddMonoidHom_reesGrading_consolidated33 :
    Function.LeftInverse (DirectSum.coeAddMonoidHom (reesGrading I))
      ⇑(directSumReesGradingEquiv I).symm :=
  fun x => (directSumReesGradingEquiv I).apply_symm_apply x

private theorem rightInverse_coeAddMonoidHom_reesGrading_consolidated33 :
    Function.RightInverse (DirectSum.coeAddMonoidHom (reesGrading I))
      ⇑(directSumReesGradingEquiv I).symm :=
  fun x => (directSumReesGradingEquiv I).symm_apply_apply x


end

noncomputable instance instGradedAlgebraReesGrading (I : Ideal R) :
    GradedAlgebra (reesGrading I) where
  __ := instGradedMonoidReesGrading I
  decompose' := ⇑(directSumReesGradingEquiv I).symm
  left_inv := leftInverse_coeAddMonoidHom_reesGrading_consolidated33 I
  right_inv := rightInverse_coeAddMonoidHom_reesGrading_consolidated33 I






noncomputable def reesMonomial (I : Ideal R) (n : ℕ) (r : R) (hr : r ∈ I ^ n) :
    ↥(reesAlgebra I) :=
  ⟨Polynomial.monomial n r, reesAlgebra.monomial_mem.mpr hr⟩

section
variable (I : Ideal R)

@[simp] theorem reesMonomial_coe (n : ℕ) (r : R) (hr : r ∈ I ^ n) :
    ((reesMonomial I n r hr : ↥(reesAlgebra I)) : R[X]) = Polynomial.monomial n r := rfl

theorem reesMonomial_mem_reesGrading {n : ℕ} {r : R} (hr : r ∈ I ^ n) :
    reesMonomial I n r hr ∈ reesGrading I n := by
  rw [mem_reesGrading_iff_monomial]
  exact ⟨r, hr, reesMonomial_coe I n r hr⟩


end

noncomputable def reesDegreeOneMonomial (I : Ideal R) (a : R) (ha : a ∈ I) : ↥(reesAlgebra I) :=
  reesMonomial I 1 a (mem_pow_one_consolidated33 I ha)

section
variable (I : Ideal R)

@[simp] theorem reesDegreeOneMonomial_coe (a : R) (ha : a ∈ I) :
    ((reesDegreeOneMonomial I a ha : ↥(reesAlgebra I)) : R[X]) = Polynomial.monomial 1 a := rfl

theorem reesDegreeOneMonomial_mem_reesGrading {a : R} (ha : a ∈ I) :
    reesDegreeOneMonomial I a ha ∈ reesGrading I 1 :=
  reesMonomial_mem_reesGrading I (mem_pow_one_consolidated33 I ha)


end

noncomputable def reesGenerator (I : Ideal R) (a : ↥I) : ↥(reesAlgebra I) :=
  reesDegreeOneMonomial I (a : R) a.2

section
variable (I : Ideal R) (a : ↥I)

@[simp] theorem reesGenerator_coe :
    ((reesGenerator I a : ↥(reesAlgebra I)) : R[X]) = Polynomial.monomial 1 (a : R) := rfl

theorem reesGenerator_mem_reesGrading : reesGenerator I a ∈ reesGrading I 1 :=
  reesDegreeOneMonomial_mem_reesGrading I a.2


end

private noncomputable def reesMonomialOfCoeff (I : Ideal R) (p : ↥(reesAlgebra I)) (i : ℕ) :
    ↥(reesAlgebra I) :=
  reesMonomial I i ((p : R[X]).coeff i) (coeff_mem_pow_consolidated33 I p i)

section
variable (I : Ideal R) (p : ↥(reesAlgebra I))

private theorem reesComponent_coe_consolidated33 (i : ℕ) :
    ((reesMonomialOfCoeff I p i : ↥(reesAlgebra I)) : R[X])
      = Polynomial.monomial i ((p : R[X]).coeff i) := rfl

private theorem reesComponent_mem_reesGrading_consolidated33 (i : ℕ) :
    reesMonomialOfCoeff I p i ∈ reesGrading I i := by
  refine (mem_reesGrading_iff_coeff I i _).2 fun j hj => ?_
  rw [reesComponent_coe_consolidated33, Polynomial.coeff_monomial, if_neg (Ne.symm hj)]

private theorem eq_sum_reesComponent_consolidated33 :
    p = ∑ i ∈ (p : R[X]).support, reesMonomialOfCoeff I p i := by
  have hval : ∀ x y : ↥(reesAlgebra I),
      (reesAlgebra I).val x = (reesAlgebra I).val y → x = y := fun _ _ h => Subtype.ext h
  exact hval _ _ (by rw [map_sum]; exact Polynomial.as_sum_support _)


end

section
variable (I : Ideal R)

private theorem mem_span_reesGenerator_of_eq_monomial_succ_consolidated33 :
    ∀ (n : ℕ) (r : R), r ∈ I ^ (n + 1) →
      ∀ x : ↥(reesAlgebra I), (x : R[X]) = Polynomial.monomial (n + 1) r →
        x ∈ Ideal.span (Set.range (reesGenerator I)) := by
  intro n
  induction n with
  | zero =>
    intro r hr x hx
    have hr' : r ∈ I := by simpa using hr
    have hxe : x = reesGenerator I ⟨r, hr'⟩ := Subtype.ext (hx.trans rfl)
    rw [hxe]
    exact Ideal.subset_span (Set.mem_range_self _)
  | succ n ih =>
    intro r hr
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on'
      (C := fun s _ => ∀ x : ↥(reesAlgebra I),
        (x : R[X]) = Polynomial.monomial (n + 1 + 1) s →
          x ∈ Ideal.span (Set.range (reesGenerator I))) ?_ ?_ hr
    · intro m hm a ha x hx
      have hy : reesMonomial I (n + 1) m hm ∈ Ideal.span (Set.range (reesGenerator I)) :=
        ih m hm (reesMonomial I (n + 1) m hm) rfl
      have hco : ((reesMonomial I (n + 1) m hm * reesGenerator I ⟨a, ha⟩ : ↥(reesAlgebra I)) : R[X])
          = Polynomial.monomial (n + 1 + 1) (m * a) := by
        show (Polynomial.monomial (n + 1) m : R[X]) * Polynomial.monomial 1 a
            = Polynomial.monomial (n + 1 + 1) (m * a)
        rw [Polynomial.monomial_mul_monomial]
      have hxe : x = reesMonomial I (n + 1) m hm * reesGenerator I ⟨a, ha⟩ :=
        Subtype.ext (hx.trans hco.symm)
      rw [hxe]
      exact Ideal.mul_mem_right _ _ hy
    · intro s hs t ht hs' ht' x hx
      have hsm : s ∈ I ^ (n + 1 + 1) := by rw [pow_succ]; exact hs
      have htm : t ∈ I ^ (n + 1 + 1) := by rw [pow_succ]; exact ht
      have hxe : x = reesMonomial I (n + 1 + 1) s hsm
          + reesMonomial I (n + 1 + 1) t htm := by
        refine Subtype.ext ?_
        show (x : R[X]) = Polynomial.monomial (n + 1 + 1) s + Polynomial.monomial (n + 1 + 1) t
        rw [hx]
        exact map_add (Polynomial.monomial (R := R) (n + 1 + 1)) s t
      rw [hxe]
      exact add_mem (hs' _ rfl) (ht' _ rfl)

theorem reesGrading_irrelevant_le_span :
    (HomogeneousIdeal.irrelevant (reesGrading I)).toIdeal ≤
      Ideal.span (Set.range (reesGenerator I)) := by
  intro p hp
  have hp1 : p ∈ HomogeneousIdeal.irrelevant (reesGrading I) := hp
  rw [HomogeneousIdeal.mem_irrelevant_iff] at hp1
  have hsum : p = ∑ i ∈ (p : R[X]).support, reesMonomialOfCoeff I p i := eq_sum_reesComponent_consolidated33 I p
  have hmapsum : (GradedRing.proj (reesGrading I) 0)
        (∑ i ∈ (p : R[X]).support, reesMonomialOfCoeff I p i)
      = ∑ i ∈ (p : R[X]).support, (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p i) :=
    map_sum (GradedRing.proj (reesGrading I) 0) (fun i => reesMonomialOfCoeff I p i)
      ((p : R[X]).support)
  have hprojsum : ∑ i ∈ (p : R[X]).support,
      (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p i) = 0 := by
    rw [← hmapsum, ← hsum]
    exact hp1
  have hsingle : ∑ i ∈ (p : R[X]).support,
      (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p i)
      = (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p 0) := by
    refine Finset.sum_eq_single 0 (fun i _ hi => ?_) (fun h0 => ?_)
    · rw [GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_ne (reesGrading I) (reesComponent_mem_reesGrading_consolidated33 I p i) hi
    · have hc : (p : R[X]).coeff 0 = 0 :=
        not_not.mp (fun h => h0 (Polynomial.mem_support_iff.mpr h))
      have hz : reesMonomialOfCoeff I p 0 = 0 := by
        refine Subtype.ext ?_
        show Polynomial.monomial 0 ((p : R[X]).coeff 0) = (0 : R[X])
        rw [hc, map_zero]
      rw [hz, map_zero]
  have hz0 : reesMonomialOfCoeff I p 0 = 0 := by
    have h1 : (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p 0) = 0 := by
      rw [← hsingle]
      exact hprojsum
    rw [GradedRing.proj_apply,
      DirectSum.decompose_of_mem_same (reesGrading I) (reesComponent_mem_reesGrading_consolidated33 I p 0)] at h1
    exact h1
  rw [hsum]
  refine sum_mem fun i _ => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [hz0]
    exact zero_mem _
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    exact mem_span_reesGenerator_of_eq_monomial_succ_consolidated33 I k ((p : R[X]).coeff (k + 1))
      (coeff_mem_pow_consolidated33 I p (k + 1)) (reesMonomialOfCoeff I p (k + 1))
      (reesComponent_coe_consolidated33 I p (k + 1))


end

noncomputable def reesDegreeZeroMonomial (I : Ideal R) (r : R) : ↥(reesGrading I 0) :=
  ⟨reesMonomial I 0 r (mem_pow_zero_consolidated33 I r),
    reesMonomial_mem_reesGrading I (mem_pow_zero_consolidated33 I r)⟩

section
variable (I : Ideal R)

private theorem reesDegreeZeroMonomial_one_consolidated33 : reesDegreeZeroMonomial I 1 = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  show (Polynomial.monomial 0 (1 : R) : R[X]) = _
  exact Polynomial.monomial_zero_one

private theorem reesDegreeZeroMonomial_mul_consolidated33 (r s : R) :
    reesDegreeZeroMonomial I (r * s) = reesDegreeZeroMonomial I r * reesDegreeZeroMonomial I s := by
  refine Subtype.ext (Subtype.ext ?_)
  show (Polynomial.monomial 0 (r * s) : R[X])
      = (Polynomial.monomial 0 r : R[X]) * (Polynomial.monomial 0 s : R[X])
  exact (Polynomial.monomial_mul_monomial 0 0 r s).symm

private theorem reesDegreeZeroMonomial_zero_consolidated33 : reesDegreeZeroMonomial I 0 = 0 := by
  refine Subtype.ext (Subtype.ext ?_)
  show (Polynomial.monomial 0 (0 : R) : R[X]) = 0
  rw [map_zero]

private theorem reesDegreeZeroMonomial_add_consolidated33 (r s : R) :
    reesDegreeZeroMonomial I (r + s) = reesDegreeZeroMonomial I r + reesDegreeZeroMonomial I s := by
  refine Subtype.ext (Subtype.ext ?_)
  show (Polynomial.monomial 0 (r + s) : R[X])
      = (Polynomial.monomial 0 r : R[X]) + (Polynomial.monomial 0 s : R[X])
  exact map_add (Polynomial.monomial (R := R) 0) r s


end

noncomputable def reesDegreeZeroRingHom (I : Ideal R) : R →+* ↥(reesGrading I 0) where
  toFun := reesDegreeZeroMonomial I
  map_one' := reesDegreeZeroMonomial_one_consolidated33 I
  map_mul' := reesDegreeZeroMonomial_mul_consolidated33 I
  map_zero' := reesDegreeZeroMonomial_zero_consolidated33 I
  map_add' := reesDegreeZeroMonomial_add_consolidated33 I

section
variable (I : Ideal R)

@[simp] theorem reesDegreeZeroRingHom_coe_coe (r : R) :
    ((reesDegreeZeroRingHom I r : ↥(reesAlgebra I)) : R[X]) = Polynomial.C r := by
  show (Polynomial.monomial 0 r : R[X]) = Polynomial.C r
  simp

theorem reesDegreeZeroRingHom_injective :
    Function.Injective (reesDegreeZeroRingHom I) := by
  intro r s h
  have h1 := congrArg (fun x : ↥(reesGrading I 0) => ((x : ↥(reesAlgebra I)) : R[X])) h
  have h2 : (Polynomial.monomial 0 r : R[X]) = Polynomial.monomial 0 s := h1
  have h3 : (Polynomial.monomial 0 r : R[X]).coeff 0 = (Polynomial.monomial 0 s : R[X]).coeff 0 :=
    congrArg (fun p : R[X] => p.coeff 0) h2
  simpa using h3

theorem reesDegreeZeroRingHom_surjective :
    Function.Surjective (reesDegreeZeroRingHom I) := by
  rintro ⟨x, hx⟩
  have hco : ∀ i, i ≠ 0 → ((x : ↥(reesAlgebra I)) : R[X]).coeff i = 0 :=
    (mem_reesGrading_iff_coeff I 0 x).1 hx
  refine ⟨((x : ↥(reesAlgebra I)) : R[X]).coeff 0, Subtype.ext (Subtype.ext ?_)⟩
  show (Polynomial.monomial 0 (((x : ↥(reesAlgebra I)) : R[X]).coeff 0) : R[X])
      = ((x : ↥(reesAlgebra I)) : R[X])
  ext i
  rcases eq_or_ne i 0 with rfl | hi
  · simp
  · rw [Polynomial.coeff_monomial, if_neg (Ne.symm hi)]
    exact (hco i hi).symm

theorem reesDegreeZeroRingHom_bijective :
    Function.Bijective (reesDegreeZeroRingHom I) :=
  ⟨reesDegreeZeroRingHom_injective I, reesDegreeZeroRingHom_surjective I⟩


end

noncomputable def reesDegreeZeroEquiv (I : Ideal R) : R ≃+* ↥(reesGrading I 0) :=
  RingEquiv.ofBijective (reesDegreeZeroRingHom I) (reesDegreeZeroRingHom_bijective I)

section
variable (I : Ideal R) (r : R)

@[simp] theorem reesDegreeZeroEquiv_apply :
    reesDegreeZeroEquiv I r = reesDegreeZeroRingHom I r := rfl

theorem reesDegreeZeroEquiv_coe_coe :
    ((reesDegreeZeroEquiv I r : ↥(reesAlgebra I)) : R[X]) = Polynomial.C r := by
  simp only [reesDegreeZeroEquiv_apply, reesDegreeZeroRingHom_coe_coe]


end

end FunctorialResolution.Blowup
end

-- Source: Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace FunctorialResolution.Blowup

section
def exceptionalIdeal {X' X : Scheme.{u}} (f : X' ⟶ X) (Z : X.IdealSheafData) :
    X'.IdealSheafData :=
  Z.comap f

theorem exceptionalIdeal_eq_comap {X' X : Scheme.{u}} (f : X' ⟶ X) (Z : X.IdealSheafData) :
    exceptionalIdeal f Z = Z.comap f := rfl

def strictTransformOpens {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    ((J.comap f).subscheme).Opens :=
  (J.comap f).subschemeι ⁻¹ᵁ (Z.comap f).support.compl

theorem strictTransformOpens_eq {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    strictTransformOpens f Z J =
      (J.comap f).subschemeι ⁻¹ᵁ (Z.comap f).support.compl := rfl

def strictTransformImmersion {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    (strictTransformOpens f Z J).toScheme ⟶ X' :=
  (strictTransformOpens f Z J).ι ≫ (J.comap f).subschemeι

theorem strictTransformImmersion_eq {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    strictTransformImmersion f Z J =
      (strictTransformOpens f Z J).ι ≫ (J.comap f).subschemeι := rfl

def strictTransform {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    X'.IdealSheafData :=
  (strictTransformImmersion f Z J).ker

theorem strictTransform_eq_ker {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    strictTransform f Z J = (strictTransformImmersion f Z J).ker := rfl

def schemeImageIdeal {X Y : Scheme.{u}} (f : X ⟶ Y) (I : X.IdealSheafData) : Y.IdealSheafData :=
  (I.subschemeι ≫ f).ker

private theorem isClosedImmersion_lift_comp_consolidated27 {X Y Z : Scheme.{u}} (f : X ⟶ Z) [IsClosedImmersion f] (g : Y ⟶ Z)
    (h : Scheme.Hom.ker f ≤ Scheme.Hom.ker g) : IsClosedImmersion.lift f g h ≫ f = g := by
  simp

private theorem ker_le_ker_pullbackFst_consolidated27 {X Y W Z : Scheme.{u}} (f : X ⟶ Y) [Mono f] (g : Z ⟶ Y)
    (ι : W ⟶ X) (m : Z ⟶ W) (hfac : m ≫ ι ≫ f = g) :
    Scheme.Hom.ker ι ≤ Scheme.Hom.ker (pullback.fst f g) := by
  have hu : pullback.snd f g ≫ m ≫ ι = pullback.fst f g := by
    rw [← cancel_mono f]
    simp only [Category.assoc]
    rw [hfac, pullback.condition]
  rw [← hu]
  exact le_trans (Scheme.Hom.le_ker_comp m ι)
    (Scheme.Hom.le_ker_comp (pullback.snd f g) (m ≫ ι))

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (I : X.IdealSheafData)

theorem comap_ker_subschemeι_comp :
    ((I.subschemeι ≫ f).ker).comap f = I := by
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι]
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le I f) ?_
  have hle : Scheme.Hom.ker (I.subschemeι ≫ f) ≤ Scheme.Hom.ker (I.map f).subschemeι :=
    le_of_eq (by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_comp,
        Scheme.IdealSheafData.ker_subschemeι])
  have hcomap : (I.map f).comap f =
      Scheme.Hom.ker (pullback.fst f (I.map f).subschemeι) := rfl
  rw [hcomap]
  refine le_trans (le_of_eq (Scheme.IdealSheafData.ker_subschemeι I).symm) ?_
  exact ker_le_ker_pullbackFst_consolidated27 f (I.map f).subschemeι I.subschemeι
    (IsClosedImmersion.lift (I.subschemeι ≫ f) (I.map f).subschemeι hle)
    (isClosedImmersion_lift_comp_consolidated27 (I.subschemeι ≫ f) (I.map f).subschemeι hle)

theorem comap_schemeImageIdeal : (schemeImageIdeal f I).comap f = I :=
  comap_ker_subschemeι_comp f I


end

theorem comap_le_strictTransform {X X₁ : Scheme.{u}} (p : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    D.comap p ≤ strictTransform p Z D := by
  rw [strictTransform_eq_ker, strictTransformImmersion_eq]
  have h := Scheme.Hom.le_ker_comp (strictTransformOpens p Z D).ι (D.comap p).subschemeι
  rwa [Scheme.IdealSheafData.ker_subschemeι] at h

end

end FunctorialResolution.Blowup
end

-- Source: Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowup
section
open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.Blowup


variable {R : Type u} [CommRing R]

private theorem reesGenerator_coe_eq_C_mul_X_consolidated55 (I : Ideal R) (a : ↥I) :
    ((reesGenerator I a : ↥(reesAlgebra I)) : Polynomial R) =
      Polynomial.C (a : R) * Polynomial.X := by
  rw [reesGenerator_coe, ← Polynomial.C_mul_X_pow_eq_monomial, pow_one]

private theorem localization_mk_eq_zero_iff_consolidated55 {A : Type u} [CommRing A] {M : Submonoid A} (x : A)
    (s : ↥M) : Localization.mk x s = (0 : Localization M) ↔ ∃ c : ↥M, (c : A) * x = 0 := by
  rw [Localization.mk_eq_mk']
  exact IsLocalization.mk'_eq_zero_iff x s

noncomputable def affineBlowup (I : Ideal R) : Scheme.{u} :=
  AlgebraicGeometry.Proj (reesGrading I)

namespace AffineBlowup

noncomputable def toSpec (I : Ideal R) :
    affineBlowup I ⟶ AlgebraicGeometry.Spec (CommRingCat.of R) :=
  AlgebraicGeometry.Proj.toSpecZero (reesGrading I) ≫
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom
        ((reesDegreeZeroEquiv I : R ≃+* ↥(reesGrading I 0)) : R →+* ↥(reesGrading I 0)))

theorem toSpec_eq_toSpecZero_comp (I : Ideal R) :
    toSpec I =
      AlgebraicGeometry.Proj.toSpecZero (reesGrading I) ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            ((reesDegreeZeroEquiv I : R ≃+* ↥(reesGrading I 0)) : R →+* ↥(reesGrading I 0))) := rfl

end AffineBlowup

noncomputable def affineBlowupChart (I : Ideal R) (a : ↥I) :
    AlgebraicGeometry.Spec
        (CommRingCat.of (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a))) ⟶
      affineBlowup I :=
  AlgebraicGeometry.Proj.awayι (reesGrading I) (reesGenerator I a) (reesGenerator_mem_reesGrading I a)
    Nat.one_pos

theorem affineBlowupChart_eq_awayι (I : Ideal R) (a : ↥I) :
    affineBlowupChart I a =
      AlgebraicGeometry.Proj.awayι (reesGrading I) (reesGenerator I a) (reesGenerator_mem_reesGrading I a)
        Nat.one_pos := rfl

instance instIsOpenImmersionAffineBlowupChart (I : Ideal R) (a : ↥I) :
    IsOpenImmersion (affineBlowupChart I a) :=
  inferInstanceAs (IsOpenImmersion
    (AlgebraicGeometry.Proj.awayι (reesGrading I) (reesGenerator I a) (reesGenerator_mem_reesGrading I a)
      Nat.one_pos))

section
variable (I : Ideal R)

theorem opensRange_affineBlowupChart_eq_basicOpen (a : ↥I) :
    (affineBlowupChart I a).opensRange =
      AlgebraicGeometry.Proj.basicOpen (reesGrading I) (reesGenerator I a) :=
  AlgebraicGeometry.Proj.opensRange_awayι ..

theorem iSup_proj_basicOpen_reesGenerator_eq_top :
    (⨆ a : ↥I, AlgebraicGeometry.Proj.basicOpen (reesGrading I) (reesGenerator I a)) = ⊤ := by
  apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
  exact reesGrading_irrelevant_le_span I

private theorem exists_mem_range_affineBlowupChart_consolidated55 (x : ↥(affineBlowup I)) :
    ∃ a : ↥I, x ∈ Set.range (affineBlowupChart I a).base := by
  have h2 : (⋃ a : ↥I,
      ((AlgebraicGeometry.Proj.basicOpen (reesGrading I) (reesGenerator I a) :
          (AlgebraicGeometry.Proj (reesGrading I)).Opens) :
        Set ↥(AlgebraicGeometry.Proj (reesGrading I)))) = Set.univ := by
    rw [← TopologicalSpace.Opens.coe_iSup, iSup_proj_basicOpen_reesGenerator_eq_top]
    simp
  have hx : x ∈ (⋃ a : ↥I,
      ((AlgebraicGeometry.Proj.basicOpen (reesGrading I) (reesGenerator I a) :
          (AlgebraicGeometry.Proj (reesGrading I)).Opens) :
        Set ↥(AlgebraicGeometry.Proj (reesGrading I)))) := by
    rw [h2]
    exact Set.mem_univ _
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
  refine ⟨a, ?_⟩
  have hs : Set.range (affineBlowupChart I a).base =
      ((AlgebraicGeometry.Proj.basicOpen (reesGrading I) (reesGenerator I a) :
          (AlgebraicGeometry.Proj (reesGrading I)).Opens) :
        Set ↥(AlgebraicGeometry.Proj (reesGrading I))) :=
    congrArg (fun U : (affineBlowup I).Opens => (U : Set ↥(affineBlowup I)))
      (opensRange_affineBlowupChart_eq_basicOpen I a)
  rw [hs]
  exact ha


end

noncomputable def affineBlowupAffineOpenCover (I : Ideal R) : (affineBlowup I).AffineOpenCover where
  I₀ := ↥I
  X a := CommRingCat.of (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a))
  f a := affineBlowupChart I a
  idx x := (exists_mem_range_affineBlowupChart_consolidated55 I x).choose
  covers x := (exists_mem_range_affineBlowupChart_consolidated55 I x).choose_spec
  map_prop a := instIsOpenImmersionAffineBlowupChart I a

noncomputable def chartRingHom (I : Ideal R) (a : ↥I) :
    R →+* HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a) :=
  (HomogeneousLocalization.fromZeroRingHom (reesGrading I)
      (Submonoid.powers (reesGenerator I a))).comp
    ((reesDegreeZeroEquiv I : R ≃+* ↥(reesGrading I 0)) : R →+* ↥(reesGrading I 0))

section
variable (I : Ideal R) (a : ↥I) (r : R)

theorem chartRingHom_apply :
    chartRingHom I a r =
      HomogeneousLocalization.fromZeroRingHom (reesGrading I) (Submonoid.powers (reesGenerator I a))
        (reesDegreeZeroEquiv I r) := rfl

private theorem val_chartRingHom_consolidated55 :
    HomogeneousLocalization.val (chartRingHom I a r) =
      Localization.mk ((reesDegreeZeroEquiv I r : ↥(reesAlgebra I)))
        (1 : ↥(Submonoid.powers (reesGenerator I a))) := rfl


end

noncomputable instance AffineBlowup.instAlgebraChart (I : Ideal R) (a : ↥I) :
    Algebra R (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) :=
  RingHom.toAlgebra (chartRingHom I a)

section
variable (I : Ideal R) (a : ↥I)

theorem algebraMap_chart_eq_chartRingHom :
    @algebraMap R (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) _ _
        (AffineBlowup.instAlgebraChart I a) =
      chartRingHom I a := rfl

theorem affineBlowupChart_comp_toSpec :
    affineBlowupChart I a ≫ AffineBlowup.toSpec I =
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom
          (@algebraMap R (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) _ _
            (AffineBlowup.instAlgebraChart I a))) := by
  show AlgebraicGeometry.Proj.awayι (reesGrading I) (reesGenerator I a) (reesGenerator_mem_reesGrading I a)
        Nat.one_pos ≫
      (AlgebraicGeometry.Proj.toSpecZero (reesGrading I) ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            ((reesDegreeZeroEquiv I : R ≃+* ↥(reesGrading I 0)) : R →+* ↥(reesGrading I 0)))) =
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom
          (@algebraMap R (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) _ _
            (AffineBlowup.instAlgebraChart I a)))
  rw [← Category.assoc, AlgebraicGeometry.Proj.awayι_toSpecZero,
    ← AlgebraicGeometry.Spec.map_comp]
  rfl

private theorem reesGenerator_pow_one_mem_reesGrading_one_consolidated55 :
    reesGenerator I a ^ 1 ∈ reesGrading I 1 := by
  rw [pow_one]
  exact reesGenerator_mem_reesGrading I a

private theorem reesGenerator_pow_one_mem_powers_consolidated55 :
    reesGenerator I a ^ 1 ∈ Submonoid.powers (reesGenerator I a) :=
  Submonoid.pow_mem _ (Submonoid.mem_powers _) 1


end

noncomputable def chartFraction (I : Ideal R) (a b : ↥I) :
    HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a) :=
  HomogeneousLocalization.mk
    { deg := 1
      num := ⟨reesGenerator I b, reesGenerator_mem_reesGrading I b⟩
      den := ⟨reesGenerator I a ^ 1, reesGenerator_pow_one_mem_reesGrading_one_consolidated55 I a⟩
      den_mem := reesGenerator_pow_one_mem_powers_consolidated55 I a }

section
variable (I : Ideal R) (a b : ↥I)

theorem chartFraction_eq_mk :
    chartFraction I a b =
      HomogeneousLocalization.mk
        { deg := 1
          num := ⟨reesGenerator I b, reesGenerator_mem_reesGrading I b⟩
          den := ⟨reesGenerator I a ^ 1, reesGenerator_pow_one_mem_reesGrading_one_consolidated55 I a⟩
          den_mem := reesGenerator_pow_one_mem_powers_consolidated55 I a } := rfl

theorem chartRingHom_coe_eq_chartFraction_mul :
    chartRingHom I a (b : R) = chartFraction I a b * chartRingHom I a (a : R) := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    val_chartRingHom_consolidated55, val_chartRingHom_consolidated55, chartFraction_eq_mk, HomogeneousLocalization.val_mk,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  apply Subtype.ext
  push_cast [reesGenerator_coe_eq_C_mul_X_consolidated55, reesDegreeZeroEquiv_coe_coe]
  ring


end

section
variable (I : Ideal R) (a : ↥I)

theorem map_chartRingHom_eq_span_singleton :
    Ideal.map (chartRingHom I a) I = Ideal.span {chartRingHom I a (a : R)} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    exact ⟨chartFraction I a ⟨x, hx⟩, (chartRingHom_coe_eq_chartFraction_mul I a ⟨x, hx⟩).symm⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ a.2

theorem chartRingHom_mem_nonZeroDivisors :
    chartRingHom I a (a : R) ∈
      nonZeroDivisors (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) := by
  have key : ∀ z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a),
      chartRingHom I a (a : R) * z = 0 → z = 0 := by
    intro z hz
    have hz' : HomogeneousLocalization.val (chartRingHom I a (a : R) * z) = 0 := by
      rw [hz, HomogeneousLocalization.val_zero]
    rw [HomogeneousLocalization.val_mul, val_chartRingHom_consolidated55,
      HomogeneousLocalization.eq_num_div_den z, Localization.mk_mul,
      localization_mk_eq_zero_iff_consolidated55] at hz'
    obtain ⟨c, hc⟩ := hz'
    obtain ⟨m, hm⟩ : ∃ m : ℕ, reesGenerator I a ^ m = (c : ↥(reesAlgebra I)) := c.2
    rw [← hm] at hc
    have hP : reesGenerator I a ^ (m + 1) * HomogeneousLocalization.num z = 0 := by
      apply Subtype.ext
      have h1 := congrArg (fun p : ↥(reesAlgebra I) => (p : Polynomial R)) hc
      push_cast [reesGenerator_coe_eq_C_mul_X_consolidated55, reesDegreeZeroEquiv_coe_coe] at h1
      push_cast [reesGenerator_coe_eq_C_mul_X_consolidated55]
      linear_combination (Polynomial.X : Polynomial R) * h1
    rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_zero,
      HomogeneousLocalization.eq_num_div_den z, localization_mk_eq_zero_iff_consolidated55]
    exact ⟨⟨reesGenerator I a ^ (m + 1), Submonoid.pow_mem _ (Submonoid.mem_powers _) (m + 1)⟩, hP⟩
  rw [mem_nonZeroDivisors_iff]
  exact ⟨key, fun z hz => key z ((mul_comm (chartRingHom I a (a : R)) z).trans hz)⟩


end

end FunctorialResolution.Blowup
end

-- Source: Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.Blowup

def StrictTransformIsBlowupOfClosedSubscheme : Prop :=
  ∀ (X X₁ S : Scheme.{u}) [IsLocallyNoetherian X]
    (j : S ⟶ X) [IsClosedImmersion j] (π : X₁ ⟶ X)
    (Z : X.IdealSheafData), IsBlowupAlongIdealSheaf π Z →
    (∀ T ∈ irreducibleComponents (↥S), ¬ (j.base '' T) ⊆ (Z.support : Set ↥X)) →
    ∃ ψ : (strictTransform π Z j.ker).subscheme ⟶ S,
      ψ ≫ j = (strictTransform π Z j.ker).subschemeι ≫ π ∧
        IsBlowupAlongIdealSheaf ψ (Z.comap j)

def BlowupIsProper : Prop :=
  ∀ (X X' : Scheme.{u}) [IsLocallyNoetherian X] (π : X' ⟶ X)
    (Z : X.IdealSheafData), IsBlowupAlongIdealSheaf π Z → IsProper π

def BlowupIsIsoOffCenter : Prop :=
  ∀ (X X' : Scheme.{u}) (π : X' ⟶ X) (Z : X.IdealSheafData),
    IsBlowupAlongIdealSheaf π Z →
      CategoryTheory.IsIso (AlgebraicGeometry.morphismRestrict π Z.support.compl)

end FunctorialResolution.Blowup
end
end

-- Source: Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupProper
section
open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.Blowup


variable {R : Type u} [CommRing R]

section
variable (I : Ideal R)

private theorem algebraMap_degreeZero_apply_consolidated88 (x : ↥(reesGrading I 0)) :
    algebraMap ↥(reesGrading I 0) ↥(reesAlgebra I) x = (x : ↥(reesAlgebra I)) := rfl

private theorem algebraMap_reesAlgebra_eq_algebraMap_degreeZero_consolidated88 (r : R) :
    algebraMap R ↥(reesAlgebra I) r =
      algebraMap ↥(reesGrading I 0) ↥(reesAlgebra I) (reesDegreeZeroEquiv I r) := by
  apply Subtype.ext
  rw [algebraMap_degreeZero_apply_consolidated88, reesDegreeZeroEquiv_coe_coe]
  rfl


end

private noncomputable def adjoinOverDegreeZero (I : Ideal R) (s : Set ↥(reesAlgebra I)) :
    Subalgebra R ↥(reesAlgebra I) where
  toSubsemiring := (Algebra.adjoin ↥(reesGrading I 0) s).toSubsemiring
  algebraMap_mem' := fun r => by
    rw [algebraMap_reesAlgebra_eq_algebraMap_degreeZero_consolidated88]
    exact Subalgebra.algebraMap_mem (Algebra.adjoin ↥(reesGrading I 0) s) _

section
variable (I : Ideal R) (s : Set ↥(reesAlgebra I))

private theorem mem_adjoin_degreeZero_of_mem_restrictScalars_consolidated88 (x : ↥(reesAlgebra I)) (hx : x ∈ adjoinOverDegreeZero I s) :
    x ∈ Algebra.adjoin ↥(reesGrading I 0) s := hx

private theorem mem_restrictScalars_of_mem_adjoin_degreeZero_consolidated88 (x : ↥(reesAlgebra I)) (hx : x ∈ Algebra.adjoin ↥(reesGrading I 0) s) :
    x ∈ adjoinOverDegreeZero I s := hx

private theorem adjoin_le_adjoin_degreeZero_consolidated88 :
    Algebra.adjoin R s ≤ adjoinOverDegreeZero I s := by
  refine Algebra.adjoin_le ?_
  intro y hy
  rw [SetLike.mem_coe]
  exact mem_restrictScalars_of_mem_adjoin_degreeZero_consolidated88 I s y (Algebra.subset_adjoin hy)

private theorem adjoin_degreeZero_eq_top_of_adjoin_eq_top_consolidated88 (hs : Algebra.adjoin R s = ⊤) : Algebra.adjoin ↥(reesGrading I 0) s = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Algebra.adjoin R s := by
    rw [hs]
    exact Algebra.mem_top
  exact mem_adjoin_degreeZero_of_mem_restrictScalars_consolidated88 I s x (adjoin_le_adjoin_degreeZero_consolidated88 I s hx)


end

theorem finiteType_reesAlgebra_degreeZero (I : Ideal R) [IsNoetherianRing R] :
    Algebra.FiniteType ↥(reesGrading I 0) ↥(reesAlgebra I) := by
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R ↥(reesAlgebra I)).out
  exact ⟨⟨s, adjoin_degreeZero_eq_top_of_adjoin_eq_top_consolidated88 I (↑s : Set ↥(reesAlgebra I)) hs⟩⟩

instance instFiniteTypeReesAlgebraOverDegZero (I : Ideal R) [IsNoetherianRing R] :
    Algebra.FiniteType ↥(reesGrading I 0) ↥(reesAlgebra I) :=
  finiteType_reesAlgebra_degreeZero I

private theorem isProper_comp_of_isIso_consolidated88 {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProper f) (hg : IsIso g) :
    IsProper (f ≫ g) := by
  have := hf
  have := hg
  infer_instance

theorem isProper_affineBlowup_toSpec (I : Ideal R) [IsNoetherianRing R] :
    IsProper (AffineBlowup.toSpec I) := by
  have hft : Algebra.FiniteType ↥(reesGrading I 0) ↥(reesAlgebra I) :=
    finiteType_reesAlgebra_degreeZero I
  have h1 : IsProper (AlgebraicGeometry.Proj.toSpecZero (reesGrading I)) :=
    inferInstance
  rw [AffineBlowup.toSpec_eq_toSpecZero_comp]
  exact isProper_comp_of_isIso_consolidated88 _ _ h1 (isIso_SpecMap_iff.mpr (reesDegreeZeroEquiv I).bijective)

instance instIsProperAffineBlowupToSpec (I : Ideal R) [IsNoetherianRing R] :
    IsProper (AffineBlowup.toSpec I) :=
  isProper_affineBlowup_toSpec I

theorem locallyOfFiniteType_affineBlowup_toSpec (I : Ideal R) [IsNoetherianRing R] :
    LocallyOfFiniteType (AffineBlowup.toSpec I) := by
  have := isProper_affineBlowup_toSpec I
  infer_instance

instance instLocallyOfFiniteTypeAffineBlowupToSpec (I : Ideal R) [IsNoetherianRing R] :
    LocallyOfFiniteType (AffineBlowup.toSpec I) :=
  locallyOfFiniteType_affineBlowup_toSpec I

theorem universallyClosed_affineBlowup_toSpec (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.UniversallyClosed (AffineBlowup.toSpec I) := by
  have := isProper_affineBlowup_toSpec I
  infer_instance

instance instUniversallyClosedAffineBlowupToSpec (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.UniversallyClosed (AffineBlowup.toSpec I) :=
  universallyClosed_affineBlowup_toSpec I

theorem quasiCompact_affineBlowup_toSpec (I : Ideal R) [IsNoetherianRing R] :
    QuasiCompact (AffineBlowup.toSpec I) := by
  have := isProper_affineBlowup_toSpec I
  infer_instance

instance instQuasiCompactAffineBlowupToSpec (I : Ideal R) [IsNoetherianRing R] :
    QuasiCompact (AffineBlowup.toSpec I) :=
  quasiCompact_affineBlowup_toSpec I

end FunctorialResolution.Blowup
end

-- Source: Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupUniversalLift
section
open CategoryTheory AlgebraicGeometry

section
namespace FunctorialResolution.Blowup


section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

def polynomialEvalInvSelf (φ : R →+* S) (s : S) : Polynomial R →+* Localization.Away s :=
  Polynomial.eval₂RingHom
    (((algebraMap S (Localization.Away s)) : S →+* Localization.Away s).comp φ)
    (Localization.Away.invSelf s)

theorem polynomialEvalInvSelf_monomial (φ : R →+* S) (s : S) (n : ℕ) (r : R) :
    polynomialEvalInvSelf φ s (Polynomial.monomial n r) =
      algebraMap S (Localization.Away s) (φ r) * Localization.Away.invSelf s ^ n := by
  simp [polynomialEvalInvSelf]

theorem exists_mul_pow_of_mem_pow (I : Ideal R) (φ : R →+* S) (s : S)
    (hI : Ideal.map φ I = Ideal.span {s}) (n : ℕ) (r : R) (hr : r ∈ I ^ n) :
    ∃ c : S, φ r = c * s ^ n := by
  have hmem : φ r ∈ Ideal.span {s ^ n} := by
    have h1 : φ r ∈ Ideal.map φ (I ^ n) := Ideal.mem_map_of_mem φ hr
    rwa [Ideal.map_pow, hI, Ideal.span_singleton_pow] at h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
  exact ⟨c, by rw [hc, mul_comm]⟩

private theorem algebraMap_mul_invSelf_consolidated87 {T : Type v} [CommRing T] (t : T) :
    algebraMap T (Localization.Away t) t * Localization.Away.invSelf t = 1 := by
  have h : Localization.Away.invSelf t
      = Localization.mk 1 ⟨t, Submonoid.mem_powers t⟩ := rfl
  rw [h, Localization.mk_eq_mk', mul_comm, IsLocalization.mk'_spec, map_one]

theorem exists_algebraMap_eq_polynomialEvalInvSelf (I : Ideal R) (φ : R →+* S) (s : S)
    (hI : Ideal.map φ I = Ideal.span {s}) (p : ↥(reesAlgebra I)) :
    ∃ c : S, algebraMap S (Localization.Away s) c = polynomialEvalInvSelf φ s (p : Polynomial R) := by
  have hmem : ∀ i : ℕ, (p : Polynomial R).coeff i ∈ I ^ i := by
    have hp := p.2
    rw [mem_reesAlgebra_iff] at hp
    exact hp
  have key : ∀ i : ℕ, ∃ c : S, φ ((p : Polynomial R).coeff i) = c * s ^ i := fun i =>
    exists_mul_pow_of_mem_pow I φ s hI i ((p : Polynomial R).coeff i) (hmem i)
  choose c hc using key
  refine ⟨∑ i ∈ Finset.range ((p : Polynomial R).natDegree + 1), c i, ?_⟩
  have hEval : polynomialEvalInvSelf φ s (p : Polynomial R) =
      Polynomial.eval₂
        (((algebraMap S (Localization.Away s)) : S →+* Localization.Away s).comp φ)
        (Localization.Away.invSelf s) (p : Polynomial R) := rfl
  rw [map_sum, hEval, Polynomial.eval₂_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.comp_apply, hc i, map_mul, map_pow, mul_assoc, ← mul_pow,
    algebraMap_mul_invSelf_consolidated87 s, one_pow, mul_one]

def reesAlgebraLiftFun (I : Ideal R) (φ : R →+* S) (s : S)
    (hI : Ideal.map φ I = Ideal.span {s}) (_hs : s ∈ nonZeroDivisors S)
    (p : ↥(reesAlgebra I)) : S :=
  (exists_algebraMap_eq_polynomialEvalInvSelf I φ s hI p).choose

section
variable (I : Ideal R) (φ : R →+* S) (s : S) (hI : Ideal.map φ I = Ideal.span {s}) (hs : s ∈ nonZeroDivisors S)

theorem algebraMap_reesAlgebraLiftFun (p : ↥(reesAlgebra I)) :
    algebraMap S (Localization.Away s) (reesAlgebraLiftFun I φ s hI hs p) =
      polynomialEvalInvSelf φ s (p : Polynomial R) :=
  (exists_algebraMap_eq_polynomialEvalInvSelf I φ s hI p).choose_spec

private theorem reesAlgebraLiftFun_one_consolidated87 :
    reesAlgebraLiftFun I φ s hI hs 1 = 1 := by
  have hinj : Function.Injective (algebraMap S (Localization.Away s)) :=
    IsLocalization.injective (Localization.Away s) (Submonoid.powers_le.mpr hs)
  apply hinj
  rw [algebraMap_reesAlgebraLiftFun I φ s hI hs 1]
  simp

private theorem reesAlgebraLiftFun_mul_consolidated87 (p q : ↥(reesAlgebra I)) :
    reesAlgebraLiftFun I φ s hI hs (p * q) = reesAlgebraLiftFun I φ s hI hs p * reesAlgebraLiftFun I φ s hI hs q := by
  have hM : Submonoid.powers s ≤ nonZeroDivisors S := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact pow_mem hs n
  have hinj : Function.Injective (algebraMap S (Localization.Away s)) :=
    IsLocalization.injective (S := Localization.Away s) (M := Submonoid.powers s) hM
  apply hinj
  have hcoe : ((p * q : ↥(reesAlgebra I)) : Polynomial R)
      = (p : Polynomial R) * (q : Polynomial R) := rfl
  rw [map_mul, algebraMap_reesAlgebraLiftFun, algebraMap_reesAlgebraLiftFun, algebraMap_reesAlgebraLiftFun, hcoe, map_mul]

private theorem reesAlgebraLiftFun_zero_consolidated87 :
    reesAlgebraLiftFun I φ s hI hs 0 = 0 := by
  have hinj : Function.Injective (algebraMap S (Localization.Away s)) :=
    IsLocalization.injective (Localization.Away s) (Submonoid.powers_le.mpr hs)
  apply hinj
  rw [algebraMap_reesAlgebraLiftFun I φ s hI hs 0]
  simp

private theorem reesAlgebraLiftFun_add_consolidated87 (p q : ↥(reesAlgebra I)) :
    reesAlgebraLiftFun I φ s hI hs (p + q) = reesAlgebraLiftFun I φ s hI hs p + reesAlgebraLiftFun I φ s hI hs q := by
  have hM : Submonoid.powers s ≤ nonZeroDivisors S := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact pow_mem hs n
  have hinj : Function.Injective (algebraMap S (Localization.Away s)) :=
    IsLocalization.injective (S := Localization.Away s) (M := Submonoid.powers s) hM
  apply hinj
  have hcoe : ((p + q : ↥(reesAlgebra I)) : Polynomial R)
      = (p : Polynomial R) + (q : Polynomial R) := rfl
  rw [map_add, algebraMap_reesAlgebraLiftFun, algebraMap_reesAlgebraLiftFun, algebraMap_reesAlgebraLiftFun, hcoe, map_add]


end

def reesAlgebraLift (I : Ideal R) (φ : R →+* S) (s : S)
    (hI : Ideal.map φ I = Ideal.span {s}) (hs : s ∈ nonZeroDivisors S) :
    ↥(reesAlgebra I) →+* S where
  toFun := reesAlgebraLiftFun I φ s hI hs
  map_one' := reesAlgebraLiftFun_one_consolidated87 I φ s hI hs
  map_mul' := reesAlgebraLiftFun_mul_consolidated87 I φ s hI hs
  map_zero' := reesAlgebraLiftFun_zero_consolidated87 I φ s hI hs
  map_add' := reesAlgebraLiftFun_add_consolidated87 I φ s hI hs

section
variable (I : Ideal R) (φ : R →+* S) (s : S) (hI : Ideal.map φ I = Ideal.span {s}) (hs : s ∈ nonZeroDivisors S)

theorem reesAlgebraLift_apply (p : ↥(reesAlgebra I)) :
    reesAlgebraLift I φ s hI hs p = reesAlgebraLiftFun I φ s hI hs p := rfl

theorem reesAlgebraLift_algebraMap (r : R) :
    reesAlgebraLift I φ s hI hs (algebraMap R ↥(reesAlgebra I) r) = φ r := by
  have hinj : Function.Injective (algebraMap S (Localization.Away s)) :=
    IsLocalization.injective (Localization.Away s) (Submonoid.powers_le.mpr hs)
  apply hinj
  rw [reesAlgebraLift_apply, algebraMap_reesAlgebraLiftFun I φ s hI hs]
  have hcoe : ((algebraMap R ↥(reesAlgebra I) r : ↥(reesAlgebra I)) : Polynomial R)
      = Polynomial.C r := rfl
  rw [hcoe]
  simp [polynomialEvalInvSelf]

theorem reesAlgebraLift_reesGenerator (a : ↥I) (ha : φ (a : R) = s) :
    reesAlgebraLift I φ s hI hs (reesGenerator I a) = 1 := by
  have hinj : Function.Injective (algebraMap S (Localization.Away s)) :=
    IsLocalization.injective (Localization.Away s) (Submonoid.powers_le.mpr hs)
  apply hinj
  rw [reesAlgebraLift_apply, algebraMap_reesAlgebraLiftFun I φ s hI hs, reesGenerator_coe, polynomialEvalInvSelf_monomial, ha,
    pow_one, algebraMap_mul_invSelf_consolidated87,
    map_one (algebraMap S (Localization.Away s))]


end

end

section

variable {R : Type u} [CommRing R]

def globalSectionsRingHom {W : Scheme.{u}} (g : W ⟶ Spec (CommRingCat.of R)) : R →+* Γ(W, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom

theorem globalSectionsRingHom_eq {W : Scheme.{u}} (g : W ⟶ Spec (CommRingCat.of R)) :
    globalSectionsRingHom g = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom := rfl

private def homogeneousLocalizationAwayVal_consolidated87 {B : Type u} [CommRing B] (J : Ideal B) (a : ↥J) :
    HomogeneousLocalization.Away (reesGrading J) (reesGenerator J a) →+*
      Localization.Away (reesGenerator J a) where
  toFun := HomogeneousLocalization.val
  map_one' := by simp
  map_mul' := fun p q => by simp
  map_zero' := by simp
  map_add' := fun p q => by simp

section
variable {B : Type u} [CommRing B] (J : Ideal B)

private theorem homogeneousLocalizationAwayVal_apply_consolidated87 (a : ↥J)
    (p : HomogeneousLocalization.Away (reesGrading J) (reesGenerator J a)) :
    homogeneousLocalizationAwayVal_consolidated87 J a p = HomogeneousLocalization.val p := rfl

private theorem isUnit_reesAlgebraLift_powers_consolidated87 {T : Type v} [CommRing T] (φ : B →+* T) (a : ↥J)
    (hgen : Ideal.map φ J = Ideal.span {φ (a : B)})
    (hnzd : φ (a : B) ∈ nonZeroDivisors T) :
    ∀ y : Submonoid.powers (reesGenerator J a),
      IsUnit (reesAlgebraLift J φ (φ (a : B)) hgen hnzd (y : ↥(reesAlgebra J))) := by
  intro y
  obtain ⟨n, hn⟩ := y.2
  have hy : (y : ↥(reesAlgebra J)) = reesGenerator J a ^ n := hn.symm
  rw [hy, map_pow, reesAlgebraLift_reesGenerator J φ (φ (a : B)) hgen hnzd a rfl, one_pow]
  exact isUnit_one


end

private def homogeneousAwayLift_consolidated87 {B : Type u} [CommRing B] (J : Ideal B)
    {T : Type v} [CommRing T] (φ : B →+* T) (a : ↥J)
    (hgen : Ideal.map φ J = Ideal.span {φ (a : B)})
    (hnzd : φ (a : B) ∈ nonZeroDivisors T) :
    HomogeneousLocalization.Away (reesGrading J) (reesGenerator J a) →+* T :=
  RingHom.comp
    (IsLocalization.lift (S := Localization.Away (reesGenerator J a))
      (g := reesAlgebraLift J φ (φ (a : B)) hgen hnzd) (isUnit_reesAlgebraLift_powers_consolidated87 J φ a hgen hnzd))
    (homogeneousLocalizationAwayVal_consolidated87 J a)

private theorem homogeneousAwayLift_chartRingHom_consolidated87 {B : Type u} [CommRing B] (J : Ideal B)
    {T : Type v} [CommRing T] (φ : B →+* T) (a : ↥J)
    (hgen : Ideal.map φ J = Ideal.span {φ (a : B)})
    (hnzd : φ (a : B) ∈ nonZeroDivisors T) (r : B) :
    homogeneousAwayLift_consolidated87 J φ a hgen hnzd (chartRingHom J a r) = φ r := by
  have hcoe : ((algebraMap B ↥(reesAlgebra J) r : ↥(reesAlgebra J)) : Polynomial B)
      = Polynomial.C r := rfl
  have h1 : ((reesDegreeZeroEquiv J r : ↥(reesGrading J 0)) : ↥(reesAlgebra J))
      = algebraMap B ↥(reesAlgebra J) r := by
    apply Subtype.ext
    rw [reesDegreeZeroEquiv_coe_coe, hcoe]
  have hz : HomogeneousLocalization.val
        (HomogeneousLocalization.fromZeroRingHom (reesGrading J)
          (Submonoid.powers (reesGenerator J a)) (reesDegreeZeroEquiv J r))
      = Localization.mk ((reesDegreeZeroEquiv J r : ↥(reesGrading J 0)) : ↥(reesAlgebra J)) 1 := rfl
  have hval : HomogeneousLocalization.val (chartRingHom J a r)
      = algebraMap ↥(reesAlgebra J) (Localization.Away (reesGenerator J a))
          (algebraMap B ↥(reesAlgebra J) r) := by
    rw [chartRingHom_apply, hz, h1, Localization.mk_one_eq_algebraMap]
  unfold homogeneousAwayLift_consolidated87
  rw [RingHom.comp_apply, homogeneousLocalizationAwayVal_apply_consolidated87, hval, IsLocalization.lift_eq,
    reesAlgebraLift_algebraMap]

theorem exists_lift_affineBlowup (I : Ideal R) {W : Scheme.{u}} [IsAffine W]
    (g : W ⟶ Spec (CommRingCat.of R)) (a : ↥I)
    (hgen : Ideal.map (globalSectionsRingHom g) I = Ideal.span {globalSectionsRingHom g (a : R)})
    (hnzd : globalSectionsRingHom g (a : R) ∈ nonZeroDivisors Γ(W, ⊤)) :
    ∃ h : W ⟶ affineBlowup I,
      h ≫ AffineBlowup.toSpec I = g ∧
        Set.range h.base ⊆ Set.range (affineBlowupChart I a).base := by
  refine ⟨W.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (homogeneousAwayLift_consolidated87 I (globalSectionsRingHom g) a hgen hnzd)) ≫
        affineBlowupChart I a, ?_, ?_⟩
  · have h2 : affineBlowupChart I a ≫ AffineBlowup.toSpec I
        = Spec.map (CommRingCat.ofHom (chartRingHom I a)) := by
      rw [affineBlowupChart_comp_toSpec, algebraMap_chart_eq_chartRingHom]
    have h3 : CommRingCat.ofHom (chartRingHom I a) ≫
          CommRingCat.ofHom (homogeneousAwayLift_consolidated87 I (globalSectionsRingHom g) a hgen hnzd)
        = CommRingCat.ofHom (globalSectionsRingHom g) := by
      rw [← CommRingCat.ofHom_comp]
      exact congrArg CommRingCat.ofHom
        (RingHom.ext fun r => homogeneousAwayLift_chartRingHom_consolidated87 I (globalSectionsRingHom g) a hgen hnzd r)
    have nat : W.toSpecΓ ≫ Spec.map g.appTop = g ≫ (Spec (CommRingCat.of R)).toSpecΓ := by
      rw [Scheme.toSpecΓ_naturality]
    have tri : (Spec (CommRingCat.of R)).toSpecΓ ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv = 𝟙 (Spec (CommRingCat.of R)) := by
      simp
    rw [Category.assoc, Category.assoc, h2, ← Spec.map_comp, h3, globalSectionsRingHom_eq,
      CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc, nat, Category.assoc, tri,
      Category.comp_id]
  · rintro x ⟨w, rfl⟩
    exact ⟨(W.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (homogeneousAwayLift_consolidated87 I (globalSectionsRingHom g) a hgen hnzd))).base w,
      by simp⟩

end

end FunctorialResolution.Blowup
end
end

-- Source: Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
section

open CategoryTheory AlgebraicGeometry Opposite

namespace FunctorialResolution.Blowup

theorem map_mem_nonZeroDivisors_of_iso {A B : CommRingCat.{u}} (e : A ≅ B) {x : A}
    (hx : x ∈ nonZeroDivisors A) : e.hom.hom x ∈ nonZeroDivisors B := by
  obtain ⟨hx1, hx2⟩ := mem_nonZeroDivisors_iff.mp hx
  have h2 : ∀ z : A, e.inv.hom (e.hom.hom z) = z := by
    intro z
    simp
  have h3 : ∀ y : B, e.hom.hom (e.inv.hom y) = y := by
    intro y
    simp
  have key : ∀ y : B, e.hom.hom x * y = 0 → y = 0 := by
    intro y hy
    have h1 : e.inv.hom (e.hom.hom x * y) = 0 := by rw [hy, map_zero]
    rw [map_mul, h2 x] at h1
    have h4 := hx1 _ h1
    rw [← h3 y, h4, map_zero]
  rw [mem_nonZeroDivisors_iff]
  refine ⟨key, fun y hy => key y ?_⟩
  rw [mul_comm]
  exact hy

private theorem exists_affineOpen_le_consolidated79 (X : Scheme.{u}) (x : X) (W : X.Opens) (hx : x ∈ W) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ (U : X.Opens) ≤ W := by
  obtain ⟨V, hV, hxV, hVW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  exact ⟨⟨V, hV⟩, hxV, hVW⟩

private theorem appLE_eq_id_of_eq_id_consolidated79 {Z : Scheme.{u}} (g : Z ⟶ Z) (hg : g = 𝟙 Z) (U : Z.Opens)
    (h : U ≤ g ⁻¹ᵁ U) : g.appLE U U h = 𝟙 _ := by
  subst hg
  simp [Scheme.Hom.appLE]
  exact (Category.id_comp _).trans (Z.presheaf.map_id _)

private theorem le_preimage_inv_preimage_hom_consolidated79 {A B : Scheme.{u}} (e : A ≅ B) (U : B.Opens) :
    U ≤ e.inv ⁻¹ᵁ (e.hom ⁻¹ᵁ U) := by
  intro y hy
  show e.hom.base (e.inv.base y) ∈ U
  have hb : e.hom.base (e.inv.base y) = y := by simp
  rw [hb]
  exact hy

private noncomputable def sectionsIsoPreimage {A B : Scheme.{u}} (e : A ≅ B) (U : B.Opens) :
    Γ(B, U) ≅ Γ(A, e.hom ⁻¹ᵁ U) where
  hom := e.hom.appLE U (e.hom ⁻¹ᵁ U) le_rfl
  inv := e.inv.appLE (e.hom ⁻¹ᵁ U) U (le_preimage_inv_preimage_hom_consolidated79 e U)
  hom_inv_id := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_id_of_eq_id_consolidated79 _ e.inv_hom_id U _
  inv_hom_id := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_id_of_eq_id_consolidated79 _ e.hom_inv_id _ _

private theorem isLocallyGeneratedByNonZeroDivisor_comap_id_consolidated79 {X : Scheme.{u}} {I : X.IdealSheafData}
    (hI : IsLocallyGeneratedByNonZeroDivisor I) : IsLocallyGeneratedByNonZeroDivisor (I.comap (𝟙 X)) := by
  intro x
  obtain ⟨U, f, hxU, hf, hIspan⟩ := hI x
  refine ⟨U, f, hxU, hf, ?_⟩
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I (𝟙 X) U U le_rfl,
    appLE_eq_id_of_eq_id_consolidated79 (𝟙 X) rfl (U : X.Opens) le_rfl, hIspan]
  simp

theorem isLocallyGeneratedByNonZeroDivisor_top (X : Scheme.{u}) :
    IsLocallyGeneratedByNonZeroDivisor (⊤ : X.IdealSheafData) := by
  intro x
  obtain ⟨U, hxU, -⟩ := exists_affineOpen_le_consolidated79 X x ⊤ trivial
  refine ⟨U, 1, hxU, one_mem _, ?_⟩
  simp

theorem isLocallyGeneratedByNonZeroDivisor_comap_top {X X' : Scheme.{u}} (f : X' ⟶ X) :
    IsLocallyGeneratedByNonZeroDivisor ((⊤ : X.IdealSheafData).comap f) := by
  intro x
  obtain ⟨U, hU, -⟩ := exists_affineOpen_le_consolidated79 X (f.base x) ⊤ trivial
  obtain ⟨V, hV, hVU⟩ := exists_affineOpen_le_consolidated79 X' x (f ⁻¹ᵁ (U : X.Opens)) hU
  refine ⟨V, 1, hV, one_mem _, ?_⟩
  have h1 : ((⊤ : X.IdealSheafData).ideal U) = ⊤ := by simp
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (⊤ : X.IdealSheafData) f U V hVU, h1,
    Ideal.map_top, Ideal.span_singleton_one]

theorem IsLocallyGeneratedByNonZeroDivisor.comap_iso {X' X'' : Scheme.{u}} {J : X'.IdealSheafData}
    (hJ : IsLocallyGeneratedByNonZeroDivisor J) (e : X'' ≅ X') :
    IsLocallyGeneratedByNonZeroDivisor (J.comap e.hom) := by
  intro x
  obtain ⟨U, f, hxU, hf, hJU⟩ := hJ (e.hom.base x)
  refine ⟨⟨e.hom ⁻¹ᵁ (U : X'.Opens), IsAffineOpen.preimage_of_isIso U.2 e.hom⟩,
    (e.hom.appLE (U : X'.Opens) (e.hom ⁻¹ᵁ (U : X'.Opens)) le_rfl).hom f, hxU, ?_, ?_⟩
  · exact FunctorialResolution.Blowup.map_mem_nonZeroDivisors_of_iso (sectionsIsoPreimage e (U : X'.Opens)) hf
  · rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE J e.hom U
      ⟨e.hom ⁻¹ᵁ (U : X'.Opens), IsAffineOpen.preimage_of_isIso U.2 e.hom⟩ le_rfl, hJU,
      Ideal.map_span, Set.image_singleton]

section
variable {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData} (h : IsBlowupAlongIdealSheaf π I)
include h

theorem IsBlowupAlongIdealSheaf.isLocallyGeneratedByNonZeroDivisor_comap : IsLocallyGeneratedByNonZeroDivisor (I.comap π) :=
  h.1

theorem IsBlowupAlongIdealSheaf.existsUnique_lift (W : Scheme.{u}) (g : W ⟶ X) (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) :
    ∃! k : W ⟶ X', k ≫ π = g :=
  h.2 W g hg

theorem IsBlowupAlongIdealSheaf.hom_ext_of_comp_eq {W : Scheme.{u}} {g : W ⟶ X} (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g))
    {a b : W ⟶ X'} (ha : a ≫ π = g) (hb : b ≫ π = g) : a = b :=
  (h.2 W g hg).unique ha hb

theorem IsBlowupAlongIdealSheaf.isIso_of_isLocallyGeneratedByNonZeroDivisor (hI : IsLocallyGeneratedByNonZeroDivisor I) : IsIso π := by
  obtain ⟨s, hs, -⟩ := h.2 X (𝟙 X) (isLocallyGeneratedByNonZeroDivisor_comap_id_consolidated79 hI)
  refine ⟨⟨s, ?_, hs⟩⟩
  exact h.hom_ext_of_comp_eq h.1 (by rw [Category.assoc, hs, Category.comp_id]) (Category.id_comp π)


end

theorem IsBlowupAlongIdealSheaf.isIso_of_top {X X' : Scheme.{u}} {π : X' ⟶ X}
    (h : IsBlowupAlongIdealSheaf π (⊤ : X.IdealSheafData)) : IsIso π :=
  h.isIso_of_isLocallyGeneratedByNonZeroDivisor (isLocallyGeneratedByNonZeroDivisor_top X)

theorem isBlowupAlongIdealSheaf_id_of_isLocallyGeneratedByNonZeroDivisor {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : IsLocallyGeneratedByNonZeroDivisor I) : IsBlowupAlongIdealSheaf (𝟙 X) I := by
  constructor
  · rwa [Scheme.IdealSheafData.comap_id]
  · intro W g _
    refine ⟨g, Category.comp_id g, ?_⟩
    intro y hy
    rw [← hy, Category.comp_id]

theorem IsBlowupAlongIdealSheaf.exists_iso {X X₁ X₂ : Scheme.{u}} {π₁ : X₁ ⟶ X} {π₂ : X₂ ⟶ X}
    {I : X.IdealSheafData} (h₁ : IsBlowupAlongIdealSheaf π₁ I) (h₂ : IsBlowupAlongIdealSheaf π₂ I) :
    ∃ e : X₁ ≅ X₂, e.hom ≫ π₂ = π₁ := by
  obtain ⟨a, ha, -⟩ := h₂.2 X₁ π₁ h₁.1
  obtain ⟨b, hb, -⟩ := h₁.2 X₂ π₂ h₂.1
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · exact h₁.hom_ext_of_comp_eq h₁.1 (by rw [Category.assoc, hb, ha]) (Category.id_comp π₁)
  · exact h₂.hom_ext_of_comp_eq h₂.1 (by rw [Category.assoc, ha, hb]) (Category.id_comp π₂)

theorem IsBlowupAlongIdealSheaf.iso_hom_comp {X X' X'' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) (e : X'' ≅ X') : IsBlowupAlongIdealSheaf (e.hom ≫ π) I := by
  have hcomp : I.comap (e.hom ≫ π) = (I.comap π).comap e.hom := by
    simp [Scheme.IdealSheafData.comap_comp]
  refine ⟨?_, ?_⟩
  · rw [hcomp]
    exact h.1.comap_iso e
  · intro W g hg
    obtain ⟨k, hk, hk'⟩ := h.2 W g hg
    refine ⟨k ≫ e.inv, ?_, ?_⟩
    · show (k ≫ e.inv) ≫ e.hom ≫ π = g
      rw [Category.assoc, ← Category.assoc e.inv e.hom π, e.inv_hom_id, Category.id_comp, hk]
    · intro m hm
      have hm' : m ≫ e.hom ≫ π = g := hm
      have hme : m ≫ e.hom = k := hk' _ ((Category.assoc m e.hom π).trans hm')
      rw [← hme, Category.assoc, e.hom_inv_id, Category.comp_id]

end FunctorialResolution.Blowup
end

-- Source: Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupCartier
section
open CategoryTheory AlgebraicGeometry Opposite

section
namespace FunctorialResolution.Blowup


variable {R : Type u} [CommRing R]

def specIdealSheaf (I : Ideal R) : (Spec (CommRingCat.of R)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I)

section
variable (I : Ideal R)

theorem specIdealSheaf_eq_ofIdealTop :
    specIdealSheaf I =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I) := rfl

theorem specIdealSheaf_ideal_top :
    (specIdealSheaf I).ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ =
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I :=
  Scheme.IdealSheafData.ofIdealTop_ideal_top _


end

def chartSectionsIso (I : Ideal R) (a : ↥I) :
    CommRingCat.of (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) ≅
      Γ(affineBlowup I, affineBlowupChart I a ''ᵁ ⊤) :=
  (Scheme.ΓSpecIso
      (CommRingCat.of (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)))).symm ≪≫
    ((affineBlowupChart I a).appIso ⊤).symm

section
variable (I : Ideal R) (a : ↥I)

theorem chartSectionsIso_hom :
    (chartSectionsIso I a).hom =
      (Scheme.ΓSpecIso
          (CommRingCat.of
            (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)))).inv ≫
        ((affineBlowupChart I a).appIso ⊤).inv := rfl

theorem chartSectionsIso_hom_apply (x : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) :
    (chartSectionsIso I a).hom.hom x =
      ((affineBlowupChart I a).appIso ⊤).inv.hom
        ((Scheme.ΓSpecIso
            (CommRingCat.of
              (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)))).inv.hom x) := rfl


end

private theorem comp_presheaf_map_eq_of_heq_consolidated113 {Z : Scheme.{u}} {A : CommRingCat.{u}} (U : Z.Opens) (hU : U = ⊤)
    (φ : A ⟶ Γ(Z, U)) (h : (⊤ : Z.Opens) ≤ U) (ψ : A ⟶ Γ(Z, (⊤ : Z.Opens)))
    (hφ : HEq φ ψ) : φ ≫ Z.presheaf.map (homOfLE h).op = ψ := by
  subst hU
  obtain rfl : φ = ψ := eq_of_heq hφ
  rw [show (homOfLE h : (⊤ : Z.Opens) ⟶ ⊤) = 𝟙 (⊤ : Z.Opens) from rfl]
  simp

private theorem appTop_eq_appLE_top_top_consolidated113 {Z S : Scheme.{u}} (f : Z ⟶ S)
    (h : (⊤ : Z.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens)) : f.appLE ⊤ ⊤ h = f.appTop :=
  comp_presheaf_map_eq_of_heq_consolidated113 (f ⁻¹ᵁ (⊤ : S.Opens)) (le_antisymm le_top h) (f.app ⊤) h f.appTop HEq.rfl

private theorem appLE_image_top_comp_appIso_hom_consolidated113 {Z X S : Scheme.{u}} (g : Z ⟶ X)
    [IsOpenImmersion g] (p : X ⟶ S)
    (e : (g ''ᵁ (⊤ : Z.Opens)) ≤ p ⁻¹ᵁ (⊤ : S.Opens)) :
    p.appLE ⊤ (g ''ᵁ ⊤) e ≫ (g.appIso ⊤).hom = (g ≫ p).appTop := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
  exact appTop_eq_appLE_top_top_consolidated113 (g ≫ p) _

section
variable (I : Ideal R) (a : ↥I)

theorem chartRingHom_comp_chartSectionsIso_hom :
    CommRingCat.ofHom (chartRingHom I a) ≫ (chartSectionsIso I a).hom =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (AffineBlowup.toSpec I).appLE ⊤ (affineBlowupChart I a ''ᵁ ⊤)
          (le_top.trans_eq (Scheme.Hom.preimage_top (AffineBlowup.toSpec I)).symm) := by
  rw [chartSectionsIso_hom, ← Category.assoc, Iso.comp_inv_eq, Category.assoc,
    appLE_image_top_comp_appIso_hom_consolidated113, affineBlowupChart_comp_toSpec, algebraMap_chart_eq_chartRingHom]
  exact Scheme.ΓSpecIso_inv_naturality _

theorem ideal_comap_toSpec_chart_eq_span (hW : IsAffineOpen (affineBlowupChart I a ''ᵁ ⊤)) :
    ((specIdealSheaf I).comap (AffineBlowup.toSpec I)).ideal ⟨_, hW⟩ =
      Ideal.span {(chartSectionsIso I a).hom.hom (chartRingHom I a (a : R))} := by
  have hcomp := congrArg CommRingCat.Hom.hom (chartRingHom_comp_chartSectionsIso_hom I a)
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hcomp
  have key : Ideal.map ((AffineBlowup.toSpec I).appLE ⊤ (affineBlowupChart I a ''ᵁ ⊤)
        (le_top.trans_eq (Scheme.Hom.preimage_top (AffineBlowup.toSpec I)).symm)).hom
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I)
      = Ideal.span {(chartSectionsIso I a).hom.hom (chartRingHom I a (a : R))} := by
    rw [Ideal.map_map, ← hcomp, ← Ideal.map_map, map_chartRingHom_eq_span_singleton, Ideal.map_span,
      Set.image_singleton]
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (specIdealSheaf I) (AffineBlowup.toSpec I)
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ ⟨_, hW⟩
      (le_top.trans_eq (Scheme.Hom.preimage_top (AffineBlowup.toSpec I)).symm)]
  rw [specIdealSheaf_ideal_top]
  exact key


end

theorem isLocallyGeneratedByNonZeroDivisor_comap_toSpec (I : Ideal R) :
    IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (AffineBlowup.toSpec I)) := by
  intro x
  obtain ⟨a, hx⟩ : ∃ a : ↥I, x ∈ Set.range (affineBlowupChart I a).base :=
    ⟨(affineBlowupAffineOpenCover I).idx x, (affineBlowupAffineOpenCover I).covers x⟩
  have hW := (isAffineOpen_top (Spec (CommRingCat.of
      (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a))))).image_of_isOpenImmersion
      (affineBlowupChart I a)
  refine ⟨⟨_, hW⟩, (chartSectionsIso I a).hom.hom (chartRingHom I a (a : R)), ?_, ?_,
    ideal_comap_toSpec_chart_eq_span I a hW⟩
  · obtain ⟨y, hy⟩ := hx
    exact ⟨y, trivial, hy⟩
  · exact map_mem_nonZeroDivisors_of_iso (chartSectionsIso I a) (chartRingHom_mem_nonZeroDivisors I a)

end FunctorialResolution.Blowup
end
end

-- Source: Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

namespace FunctorialResolution.Blowup

private theorem eq_span_inv_of_map_eq_span_consolidated114 {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsIso φ]
    (J : Ideal R) (s : S) (h : J.map φ.hom = Ideal.span {s}) :
    J = Ideal.span {(CategoryTheory.inv φ).hom s} := by
  have hcomp : (CategoryTheory.inv φ).hom.comp φ.hom = RingHom.id R := by
    ext x
    simp
  calc J = (J.map φ.hom).map (CategoryTheory.inv φ).hom := by
        rw [Ideal.map_map, hcomp, Ideal.map_id]
    _ = (Ideal.span {s}).map (CategoryTheory.inv φ).hom := by rw [h]
    _ = Ideal.span {(CategoryTheory.inv φ).hom s} := by rw [Ideal.map_span, Set.image_singleton]

private theorem isIso_appLE_of_image_eq_consolidated114 {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {W : X.Opens} {V : Y.Opens} (hV : f ''ᵁ W = V) (e : W ≤ f ⁻¹ᵁ V) :
    IsIso (f.appLE V W e) := by
  subst hV
  rw [← Scheme.Hom.appIso_hom']
  infer_instance

private theorem exists_affineOpen_mem_le_consolidated114 {X : Scheme.{u}} (x : X) (W : X.Opens) (hx : x ∈ W) :
    ∃ V : X.affineOpens, x ∈ (V : X.Opens) ∧ (V : X.Opens) ≤ W := by
  obtain ⟨Vs, hVs, hxV, hVW⟩ :=
    (Scheme.isBasis_affineOpens X).exists_subset_of_mem_open
      (show x ∈ (W : Set X) from hx) W.isOpen
  obtain ⟨V, hVmem, rfl⟩ := hVs
  exact ⟨⟨V, hVmem⟩, hxV, fun y hy => hVW hy⟩

theorem IsLocallyGeneratedByNonZeroDivisor.comap_of_isOpenImmersion {X U : Scheme.{u}}
    {I : X.IdealSheafData} (hI : IsLocallyGeneratedByNonZeroDivisor I) (f : U ⟶ X) [IsOpenImmersion f] :
    IsLocallyGeneratedByNonZeroDivisor (I.comap f) := by
  intro x
  obtain ⟨V, g, hxV, hg, hVg⟩ := hI (f.base x)
  have hVa : IsAffineOpen (V : X.Opens) := V.2
  obtain ⟨W, hxW, hWle⟩ := exists_affineOpen_mem_le_consolidated114 x (f ⁻¹ᵁ (V : X.Opens)) hxV
  have hWa : IsAffineOpen (W : U.Opens) := W.2
  have hximg : f.base x ∈ (f ''ᵁ (W : U.Opens)) := ⟨x, hxW, rfl⟩
  obtain ⟨r, hr1, hr2⟩ := hVa.exists_basicOpen_le (⟨f.base x, hximg⟩ : (f ''ᵁ (W : U.Opens))) hxV
  have hW'le : f ⁻¹ᵁ (X.basicOpen r) ≤ (W : U.Opens) := by
    rw [← Scheme.Hom.preimage_image_eq f (W : U.Opens)]
    exact fun y hy => hr1 hy
  have hbas : U.basicOpen ((f.appLE (V : X.Opens) (W : U.Opens) hWle).hom r)
      = f ⁻¹ᵁ (X.basicOpen r) := by
    rw [show (f.appLE (V : X.Opens) (W : U.Opens) hWle).hom r
          = (U.presheaf.map (homOfLE hWle).op).hom ((f.app (V : X.Opens)).hom r) from rfl,
      Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact inf_eq_right.mpr hW'le
  have hW'aff : IsAffineOpen (f ⁻¹ᵁ (X.basicOpen r)) := by
    rw [← hbas]
    exact hWa.basicOpen _
  have hBrange : X.basicOpen r ≤ f.opensRange := by
    intro y hy
    obtain ⟨z, _, hz⟩ := hr1 hy
    exact ⟨z, hz⟩
  have himg : f ''ᵁ (f ⁻¹ᵁ (X.basicOpen r)) = X.basicOpen r :=
    (f.image_preimage_eq_opensRange_inf (X.basicOpen r)).trans (inf_eq_right.mpr hBrange)
  have : IsIso (f.appLE (X.basicOpen r) (f ⁻¹ᵁ (X.basicOpen r)) le_rfl) :=
    isIso_appLE_of_image_eq_consolidated114 f himg le_rfl
  have e1 : (I.ideal V).map (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
      = I.ideal ⟨X.basicOpen r, hVa.basicOpen r⟩ := I.map_ideal_basicOpen V r
  rw [hVg, Ideal.map_span, Set.image_singleton] at e1
  refine ⟨⟨f ⁻¹ᵁ (X.basicOpen r), hW'aff⟩,
    (f.appLE (X.basicOpen r) (f ⁻¹ᵁ (X.basicOpen r)) le_rfl).hom
      ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom g), hr2, ?_, ?_⟩
  · refine map_mem_nonZeroDivisors_of_iso
      (asIso (f.appLE (X.basicOpen r) (f ⁻¹ᵁ (X.basicOpen r)) le_rfl)) ?_
    have := hVa.isLocalization_basicOpen r
    exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers r) Γ(X, X.basicOpen r) hg
  · have hmap := I.comap_ideal_eq_map_appLE f ⟨X.basicOpen r, hVa.basicOpen r⟩
      ⟨f ⁻¹ᵁ (X.basicOpen r), hW'aff⟩ le_rfl
    rw [← e1, Ideal.map_span, Set.image_singleton] at hmap
    exact hmap

theorem IsLocallyGeneratedByNonZeroDivisor.of_isOpenImmersion_cover {X : Scheme.{u}} (I : X.IdealSheafData)
    {ι : Type v} (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range ⇑(f i).base)
    (h : ∀ i, IsLocallyGeneratedByNonZeroDivisor (I.comap (f i))) :
    IsLocallyGeneratedByNonZeroDivisor I := by
  intro x
  obtain ⟨i, u, hu⟩ := hcover x
  obtain ⟨W, s, hxW, hs, hWs⟩ := h i u
  have hWa : IsAffineOpen (W : (U i).Opens) := W.2
  have hVaff : IsAffineOpen (f i ''ᵁ (W : (U i).Opens)) := hWa.image_of_isOpenImmersion (f i)
  have hpre : (f i) ⁻¹ᵁ (f i ''ᵁ (W : (U i).Opens)) = (W : (U i).Opens) :=
    Scheme.Hom.preimage_image_eq (f i) _
  have e : (W : (U i).Opens) ≤ (f i) ⁻¹ᵁ (f i ''ᵁ (W : (U i).Opens)) := hpre.ge
  have : IsIso ((f i).appLE (f i ''ᵁ (W : (U i).Opens)) (W : (U i).Opens) e) :=
    isIso_appLE_of_image_eq_consolidated114 (f i) rfl e
  have key := I.comap_ideal_eq_map_appLE (f i) ⟨f i ''ᵁ (W : (U i).Opens), hVaff⟩ W e
  rw [hWs] at key
  refine ⟨⟨f i ''ᵁ (W : (U i).Opens), hVaff⟩,
    (CategoryTheory.inv ((f i).appLE (f i ''ᵁ (W : (U i).Opens)) (W : (U i).Opens) e)).hom s,
    ?_, ?_, ?_⟩
  · exact ⟨u, hxW, hu⟩
  · exact map_mem_nonZeroDivisors_of_iso
      (asIso (CategoryTheory.inv
        ((f i).appLE (f i ''ᵁ (W : (U i).Opens)) (W : (U i).Opens) e))) hs
  · exact eq_span_inv_of_map_eq_span_consolidated114 _ _ _ key.symm

theorem IsBlowupAlongIdealSheaf.restrict {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) (U : X.Opens) :
    IsBlowupAlongIdealSheaf (π ∣_ U) (I.comap U.ι) := by
  have key : ∀ {W : Scheme.{u}} (g : W ⟶ U.toScheme),
      (I.comap U.ι).comap g = I.comap (g ≫ U.ι) := by
    intro W g
    rw [Scheme.IdealSheafData.comap_comp]
  constructor
  · rw [key (π ∣_ U), morphismRestrict_ι, Scheme.IdealSheafData.comap_comp]
    exact h.1.comap_of_isOpenImmersion (π ⁻¹ᵁ U).ι
  · intro W g hg
    rw [key g] at hg
    obtain ⟨k, hk, hk'⟩ := h.2 W (g ≫ U.ι) hg
    have hrange : Set.range ⇑k.base ⊆ Set.range ⇑(π ⁻¹ᵁ U).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      show π.base (k.base w) ∈ U
      have h1 : (k ≫ π).base w = (g ≫ U.ι).base w := by rw [hk]
      have h2 : π.base (k.base w) = U.ι.base (g.base w) := h1
      rw [h2]
      exact (g.base w).2
    refine ⟨IsOpenImmersion.lift (π ⁻¹ᵁ U).ι k hrange, ?_, ?_⟩
    · show IsOpenImmersion.lift (π ⁻¹ᵁ U).ι k hrange ≫ π ∣_ U = g
      rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
        IsOpenImmersion.lift_fac]
      exact hk
    · intro y hy
      have hy' : y ≫ π ∣_ U = g := hy
      rw [← cancel_mono (π ⁻¹ᵁ U).ι, IsOpenImmersion.lift_fac]
      refine hk' _ ?_
      show (y ≫ (π ⁻¹ᵁ U).ι) ≫ π = g ≫ U.ι
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy']

private theorem exists_pullback_fst_base_eq_consolidated114 {W U X : Scheme.{u}} (g : W ⟶ X) (f : U ⟶ X)
    [IsOpenImmersion f] (w : W) (hw : g.base w ∈ Set.range ⇑f.base) :
    ∃ z : ↥(pullback g f), (pullback.fst g f).base z = w := by
  have hrange : Set.range ⇑((g ⁻¹ᵁ f.opensRange).ι ≫ g).base ⊆ Set.range ⇑f.base := by
    rintro _ ⟨v, rfl⟩
    exact v.2
  have hl : IsOpenImmersion.lift f ((g ⁻¹ᵁ f.opensRange).ι ≫ g) hrange ≫ f
      = (g ⁻¹ᵁ f.opensRange).ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  have hm := pullback.lift_fst (g ⁻¹ᵁ f.opensRange).ι
    (IsOpenImmersion.lift f ((g ⁻¹ᵁ f.opensRange).ι ≫ g) hrange) hl.symm
  refine ⟨(pullback.lift (g ⁻¹ᵁ f.opensRange).ι
    (IsOpenImmersion.lift f ((g ⁻¹ᵁ f.opensRange).ι ≫ g) hrange) hl.symm).base
      ⟨w, show w ∈ g ⁻¹ᵁ f.opensRange from hw⟩, ?_⟩
  have h3 := congrArg (fun t : (g ⁻¹ᵁ f.opensRange).toScheme ⟶ W => t.base
    ⟨w, show w ∈ g ⁻¹ᵁ f.opensRange from hw⟩) hm
  exact h3

private noncomputable def pullbackOpenCoverOfCovers {X W : Scheme.{u}} {ι : Type v} (U : ι → Scheme.{u})
    (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range ⇑(f i).base) (g : W ⟶ X) : W.OpenCover :=
  Scheme.Cover.mkOfCovers ι (fun i => pullback g (f i)) (fun i => pullback.fst g (f i))
    (fun w => by
      obtain ⟨i, hi⟩ := hcover (g.base w)
      obtain ⟨z, hz⟩ := exists_pullback_fst_base_eq_consolidated114 g (f i) w hi
      exact ⟨i, z, hz⟩)
    (fun i => inferInstance)

section
variable {X W T : Scheme.{u}} {ι : Type v} (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)] (hcover : ∀ x : X, ∃ i, x ∈ Set.range ⇑(f i).base) (g : W ⟶ X)
include hcover

private theorem hom_ext_of_isOpenImmersion_cover_consolidated114 {a b : W ⟶ T}
    (h : ∀ i, pullback.fst g (f i) ≫ a = pullback.fst g (f i) ≫ b) : a = b := by
  refine Scheme.Cover.hom_ext (pullbackOpenCoverOfCovers U f hcover g) a b (fun i => ?_)
  exact h i

private theorem exists_hom_of_isOpenImmersion_cover_consolidated114 (k : ∀ i, pullback g (f i) ⟶ T)
    (hk : ∀ i j, pullback.fst (pullback.fst g (f i)) (pullback.fst g (f j)) ≫ k i
        = pullback.snd (pullback.fst g (f i)) (pullback.fst g (f j)) ≫ k j) :
    ∃ φ : W ⟶ T, ∀ i, pullback.fst g (f i) ≫ φ = k i := by
  have hk' : ∀ i j,
      pullback.fst ((pullbackOpenCoverOfCovers U f hcover g).f i) ((pullbackOpenCoverOfCovers U f hcover g).f j) ≫ k i
        = pullback.snd ((pullbackOpenCoverOfCovers U f hcover g).f i)
            ((pullbackOpenCoverOfCovers U f hcover g).f j) ≫ k j :=
    fun i j => hk i j
  refine ⟨Scheme.Cover.glueMorphisms (pullbackOpenCoverOfCovers U f hcover g) k hk', fun i => ?_⟩
  exact Scheme.Cover.ι_glueMorphisms (pullbackOpenCoverOfCovers U f hcover g) k hk' i


end

private theorem eq_of_comp_eq_of_isBlowupAlongIdealSheaf_openCover_consolidated114 {X X' T : Scheme.{u}} (π : X' ⟶ X)
    (I : X.IdealSheafData)
    {ι : Type v} (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range ⇑(f i).base)
    (h : ∀ i, IsBlowupAlongIdealSheaf (pullback.snd π (f i)) (I.comap (f i)))
    {a b : T ⟶ X'} (hab : a ≫ π = b ≫ π) (hc : IsLocallyGeneratedByNonZeroDivisor (I.comap (a ≫ π))) :
    a = b := by
  refine hom_ext_of_isOpenImmersion_cover_consolidated114 U f hcover (a ≫ π) fun i => ?_
  have hcond : pullback.fst (a ≫ π) (f i) ≫ (a ≫ π) = pullback.snd (a ≫ π) (f i) ≫ f i :=
    pullback.condition
  have ha' : (pullback.fst (a ≫ π) (f i) ≫ a) ≫ π = pullback.snd (a ≫ π) (f i) ≫ f i := by
    rw [Category.assoc]; exact hcond
  have hb' : (pullback.fst (a ≫ π) (f i) ≫ b) ≫ π = pullback.snd (a ≫ π) (f i) ≫ f i := by
    rw [Category.assoc, ← hab]; exact hcond
  have hEC : IsLocallyGeneratedByNonZeroDivisor ((I.comap (f i)).comap (pullback.snd (a ≫ π) (f i))) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← hcond, Scheme.IdealSheafData.comap_comp]
    exact hc.comap_of_isOpenImmersion _
  have hAB := (h i).hom_ext_of_comp_eq hEC
    (pullback.lift_snd (pullback.fst (a ≫ π) (f i) ≫ a) (pullback.snd (a ≫ π) (f i)) ha')
    (pullback.lift_snd (pullback.fst (a ≫ π) (f i) ≫ b) (pullback.snd (a ≫ π) (f i)) hb')
  have h1 := pullback.lift_fst (pullback.fst (a ≫ π) (f i) ≫ a) (pullback.snd (a ≫ π) (f i)) ha'
  have h2 := pullback.lift_fst (pullback.fst (a ≫ π) (f i) ≫ b) (pullback.snd (a ≫ π) (f i)) hb'
  rw [← h1, ← h2, hAB]

theorem IsBlowupAlongIdealSheaf.of_comap_of_isOpenImmersion_cover {X X' : Scheme.{u}} (π : X' ⟶ X)
    (I : X.IdealSheafData) {ι : Type v} (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range ⇑(f i).base)
    (h : ∀ i, IsBlowupAlongIdealSheaf (pullback.snd π (f i)) (I.comap (f i))) :
    IsBlowupAlongIdealSheaf π I := by
  constructor
  · refine IsLocallyGeneratedByNonZeroDivisor.of_isOpenImmersion_cover (I.comap π) (fun i => pullback π (f i))
      (fun i => pullback.fst π (f i)) (fun x' => ?_) ?_
    · obtain ⟨i, hi⟩ := hcover (π.base x')
      obtain ⟨z, hz⟩ := exists_pullback_fst_base_eq_consolidated114 π (f i) x' hi
      exact ⟨i, z, hz⟩
    · intro i
      have hq : (I.comap π).comap (pullback.fst π (f i))
          = (I.comap (f i)).comap (pullback.snd π (f i)) := by
        rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
          pullback.condition]
      rw [hq]
      exact (h i).1
  · intro W g hg
    have hEC : ∀ i, IsLocallyGeneratedByNonZeroDivisor ((I.comap (f i)).comap (pullback.snd g (f i))) := by
      intro i
      have hq : (I.comap (f i)).comap (pullback.snd g (f i))
          = (I.comap g).comap (pullback.fst g (f i)) := by
        rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
          pullback.condition]
      rw [hq]
      exact hg.comap_of_isOpenImmersion _
    choose k hk1 _ using fun i => (h i).2 (pullback g (f i)) (pullback.snd g (f i)) (hEC i)
    have hapi : ∀ i, k i ≫ pullback.fst π (f i) ≫ π = pullback.fst g (f i) ≫ g := by
      intro i
      rw [pullback.condition, ← Category.assoc, hk1 i, ← pullback.condition]
    have hglue : ∀ i j, pullback.fst (pullback.fst g (f i)) (pullback.fst g (f j)) ≫
          (k i ≫ pullback.fst π (f i))
        = pullback.snd (pullback.fst g (f i)) (pullback.fst g (f j)) ≫
          (k j ≫ pullback.fst π (f j)) := by
      intro i j
      refine eq_of_comp_eq_of_isBlowupAlongIdealSheaf_openCover_consolidated114 π I U f hcover h ?_ ?_
      · simp only [Category.assoc]
        rw [hapi i, hapi j, ← Category.assoc, ← Category.assoc, pullback.condition]
      · have heq : (pullback.fst (pullback.fst g (f i)) (pullback.fst g (f j)) ≫
              (k i ≫ pullback.fst π (f i))) ≫ π
            = (pullback.fst (pullback.fst g (f i)) (pullback.fst g (f j)) ≫
              pullback.fst g (f i)) ≫ g := by
          rw [Category.assoc, Category.assoc, hapi i, ← Category.assoc]
        rw [heq, Scheme.IdealSheafData.comap_comp]
        exact hg.comap_of_isOpenImmersion _
    obtain ⟨φ, hφ⟩ :=
      exists_hom_of_isOpenImmersion_cover_consolidated114 U f hcover g
        (fun i => k i ≫ pullback.fst π (f i)) hglue
    have hφπ : φ ≫ π = g := by
      refine hom_ext_of_isOpenImmersion_cover_consolidated114 U f hcover g fun i => ?_
      rw [← Category.assoc, hφ i, Category.assoc, hapi i]
    refine ⟨φ, hφπ, fun y hy => ?_⟩
    have hy' : y ≫ π = g := hy
    refine eq_of_comp_eq_of_isBlowupAlongIdealSheaf_openCover_consolidated114 π I U f hcover h (by rw [hy', hφπ]) ?_
    rw [hy']
    exact hg

end FunctorialResolution.Blowup
end

-- Source: Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupChartPreimages
section
open CategoryTheory AlgebraicGeometry Opposite

section
namespace FunctorialResolution.Blowup


def sectionsRingHom {A : Type u} [CommRing A] {W : Scheme.{u}}
    (g : W ⟶ Spec (CommRingCat.of A)) (V : W.Opens) : A →+* ↥Γ(W, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
    g.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top g).ge)).hom

section
variable {A : Type u} [CommRing A] {W : Scheme.{u}} (g : W ⟶ Spec (CommRingCat.of A))

theorem sectionsRingHom_apply (V : W.Opens) (r : A) :
    sectionsRingHom g V r =
      (g.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top g).ge)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r) := rfl

theorem sectionsRingHom_restrict {V V' : W.Opens} (hV : V' ≤ V) (r : A) :
    sectionsRingHom g V' r =
      (W.presheaf.map (homOfLE hV).op).hom (sectionsRingHom g V r) := by
  have hmap : W.presheaf.map
        (homOfLE (le_top.trans (Scheme.Hom.preimage_top g).ge : V' ≤ g ⁻¹ᵁ ⊤)).op
      = W.presheaf.map
          (homOfLE (le_top.trans (Scheme.Hom.preimage_top g).ge : V ≤ g ⁻¹ᵁ ⊤)).op ≫
        W.presheaf.map (homOfLE hV).op :=
    W.presheaf.map_comp
      (homOfLE (le_top.trans (Scheme.Hom.preimage_top g).ge : V ≤ g ⁻¹ᵁ ⊤)).op
      (homOfLE hV).op
  have key : g.appLE ⊤ V' (le_top.trans (Scheme.Hom.preimage_top g).ge) =
      g.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top g).ge) ≫
        W.presheaf.map (homOfLE hV).op := by
    show g.app ⊤ ≫ W.presheaf.map
          (homOfLE (le_top.trans (Scheme.Hom.preimage_top g).ge : V' ≤ g ⁻¹ᵁ ⊤)).op
        = (g.app ⊤ ≫ W.presheaf.map
            (homOfLE (le_top.trans (Scheme.Hom.preimage_top g).ge : V ≤ g ⁻¹ᵁ ⊤)).op) ≫
          W.presheaf.map (homOfLE hV).op
    rw [Category.assoc, ← hmap]
  exact congrArg
    (fun φ : Γ(Spec (CommRingCat.of A), (⊤ : (Spec (CommRingCat.of A)).Opens)) ⟶ Γ(W, V') =>
      φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r)) key


end

theorem comap_specIdealSheaf_ideal {R : Type u} [CommRing R] (I : Ideal R) {W : Scheme.{u}}
    (g : W ⟶ Spec (CommRingCat.of R)) (V : W.affineOpens) :
    ((specIdealSheaf I).comap g).ideal V = Ideal.map (sectionsRingHom g (V : W.Opens)) I := by
  have h1 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE (specIdealSheaf I) g
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ V
      (le_top.trans (Scheme.Hom.preimage_top g).ge)
  rw [specIdealSheaf_ideal_top, Ideal.map_map] at h1
  exact h1

private theorem localization_mk_one_pow_consolidated145 {A : Type u} [CommRing A] (S : Submonoid A) (x : A)
    (n : ℕ) :
    Localization.mk x (1 : S) ^ n = Localization.mk (x ^ n) (1 : S) := by
  rw [Localization.mk_one_eq_algebraMap, Localization.mk_one_eq_algebraMap, map_pow]

section
variable {R : Type u} [CommRing R] (I : Ideal R) (a : ↥I)

private theorem val_chartRingHom_consolidated145 (r : R) :
    (chartRingHom I a r).val =
      Localization.mk ((reesDegreeZeroEquiv I r : ↥(reesGrading I 0)) : ↥(reesAlgebra I))
        (1 : ↥(Submonoid.powers (reesGenerator I a))) := by
  rw [chartRingHom_apply]
  rfl

theorem exists_mul_pow_eq_chartRingHom (z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) :
    ∃ (n : ℕ) (r : R), z * chartRingHom I a (a : R) ^ n = chartRingHom I a r := by
  obtain ⟨k, hk⟩ := z.den_mem
  obtain ⟨s, hs, hnum⟩ := (mem_reesGrading_iff_monomial I z.deg z.num).mp z.num_mem_deg
  have hdencoe : ((z.den : ↥(reesAlgebra I)) : Polynomial R)
      = Polynomial.monomial k ((a : R) ^ k) := by
    rw [← hk]
    simp [reesGenerator_coe, Polynomial.monomial_pow]
  by_cases hik : z.deg = k
  · refine ⟨k, s, ?_⟩
    apply HomogeneousLocalization.val_injective
    have key : z.num * ((reesDegreeZeroEquiv I (a : R) : ↥(reesGrading I 0)) : ↥(reesAlgebra I)) ^ k
        = z.den * ((reesDegreeZeroEquiv I s : ↥(reesGrading I 0)) : ↥(reesAlgebra I)) := by
      apply Subtype.ext
      push_cast
      rw [hnum, hdencoe, hik, reesDegreeZeroEquiv_coe_coe, reesDegreeZeroEquiv_coe_coe,
        ← Polynomial.C_pow, ← Polynomial.monomial_zero_left, ← Polynomial.monomial_zero_left,
        Polynomial.monomial_mul_monomial, Polynomial.monomial_mul_monomial, mul_comm]
    simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
      z.eq_num_div_den, val_chartRingHom_consolidated145, localization_mk_one_pow_consolidated145, Localization.mk_mul, mul_one]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simpa using key⟩
  · refine ⟨0, 0, ?_⟩
    apply HomogeneousLocalization.val_injective
    have hak : (a : R) ^ k = 0 := by
      have h0 := (mem_reesGrading_iff_coeff I z.deg z.den).mp z.den_mem_deg k (Ne.symm hik)
      rw [hdencoe] at h0
      simpa using h0
    have hden0 : (z.den : ↥(reesAlgebra I)) = 0 := by
      apply Subtype.ext
      rw [hdencoe, hak]
      simp
    have h0S : (0 : ↥(reesAlgebra I)) ∈ Submonoid.powers (reesGenerator I a) := ⟨k, hk.trans hden0⟩
    simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
      z.eq_num_div_den, val_chartRingHom_consolidated145, localization_mk_one_pow_consolidated145, Localization.mk_mul, mul_one]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨⟨0, h0S⟩, by simp [hden0]⟩


end

def chartSectionsRingHom {R : Type u} [CommRing R] (I : Ideal R) {W : Scheme.{u}}
    (h : W ⟶ affineBlowup I) (b : ↥I) (V : W.Opens)
    (hV : V ≤ h ⁻¹ᵁ (affineBlowupChart I b ''ᵁ ⊤)) :
    HomogeneousLocalization.Away (reesGrading I) (reesGenerator I b) →+* ↥Γ(W, V) :=
  ((chartSectionsIso I b).hom ≫ h.appLE (affineBlowupChart I b ''ᵁ ⊤) V hV).hom

section
variable {R : Type u} [CommRing R] (I : Ideal R) {W : Scheme.{u}} (h : W ⟶ affineBlowup I)

theorem chartSectionsRingHom_apply (b : ↥I) (V : W.Opens)
    (hV : V ≤ h ⁻¹ᵁ (affineBlowupChart I b ''ᵁ ⊤))
    (z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I b)) :
    chartSectionsRingHom I h b V hV z =
      (h.appLE (affineBlowupChart I b ''ᵁ ⊤) V hV).hom ((chartSectionsIso I b).hom.hom z) :=
  rfl

theorem chartSectionsRingHom_chartRingHom (b : ↥I) (V : W.Opens)
    (hV : V ≤ h ⁻¹ᵁ (affineBlowupChart I b ''ᵁ ⊤)) (r : R) :
    chartSectionsRingHom I h b V hV (chartRingHom I b r) =
      sectionsRingHom (h ≫ AffineBlowup.toSpec I) V r := by
  have key : CommRingCat.ofHom (chartRingHom I b) ≫ ((chartSectionsIso I b).hom ≫
        h.appLE (affineBlowupChart I b ''ᵁ ⊤) V hV)
      = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (h ≫ AffineBlowup.toSpec I).appLE ⊤ V
          (le_top.trans (Scheme.Hom.preimage_top (h ≫ AffineBlowup.toSpec I)).ge) := by
    rw [← Category.assoc, chartRingHom_comp_chartSectionsIso_hom, Category.assoc,
      Scheme.Hom.appLE_comp_appLE]
  exact congrArg (fun φ : CommRingCat.of R ⟶ Γ(W, V) => φ.hom r) key

theorem comap_specIdealSheaf_ideal_eq_span (a : ↥I) (V : W.affineOpens)
    (hV : (V : W.Opens) ≤ h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤)) :
    ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)).ideal V =
      Ideal.span
        {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens) (a : R)} := by
  have hfac : sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens)
      = RingHom.comp (chartSectionsRingHom I h a (V : W.Opens) hV) (chartRingHom I a) := by
    ext r
    exact (chartSectionsRingHom_chartRingHom I h a (V : W.Opens) hV r).symm
  have h2 : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens)) I
      = Ideal.span
          {chartSectionsRingHom I h a (V : W.Opens) hV (chartRingHom I a (a : R))} := by
    rw [hfac, ← Ideal.map_map, map_chartRingHom_eq_span_singleton I a, Ideal.map_span, Set.image_singleton]
  rw [comap_specIdealSheaf_ideal I (h ≫ AffineBlowup.toSpec I) V, h2,
    chartSectionsRingHom_chartRingHom I h a (V : W.Opens) hV (a : R)]


end

private theorem mem_nonZeroDivisors_of_span_singleton_eq_consolidated145 {B : Type u} [CommRing B] {s t : B}
    (hs : s ∈ nonZeroDivisors B)
    (hst : Ideal.span ({s} : Set B) = Ideal.span ({t} : Set B)) :
    t ∈ nonZeroDivisors B := by
  obtain ⟨hs1, hs2⟩ := mem_nonZeroDivisors_iff.mp hs
  have h1 : t ∈ Ideal.span ({s} : Set B) := by
    rw [hst]; exact Ideal.mem_span_singleton_self t
  have h2 : s ∈ Ideal.span ({t} : Set B) := by
    rw [← hst]; exact Ideal.mem_span_singleton_self s
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp h2
  have h3 : v * (u * s) = s := by rw [hu, hv]
  have hss : s * (1 - v * u) = 0 := by linear_combination -h3
  have h4 : (1 : B) - v * u = 0 := hs1 _ hss
  have hvu : v * u = 1 := by linear_combination -h4
  have key : ∀ y : B, t * y = 0 → y = 0 := by
    intro y hy
    have h5 : s * (u * y) = 0 := by linear_combination hy + y * hu
    have h6 : u * y = 0 := hs1 _ h5
    linear_combination v * h6 - y * hvu
  rw [mem_nonZeroDivisors_iff]
  exact ⟨key, fun y hy => key y (by rw [mul_comm]; exact hy)⟩

section
variable {R : Type u} [CommRing R] (I : Ideal R)

private theorem map_sectionsRingHom_restrict_consolidated145 {W : Scheme.{u}} (g : W ⟶ Spec (CommRingCat.of R)) {V V' : W.Opens} (hV : V' ≤ V) :
    Ideal.map (sectionsRingHom g V') I
      = Ideal.map (W.presheaf.map (homOfLE hV).op).hom (Ideal.map (sectionsRingHom g V) I) := by
  have e : (W.presheaf.map (homOfLE hV).op).hom.comp (sectionsRingHom g V) = sectionsRingHom g V' :=
    RingHom.ext fun x => (sectionsRingHom_restrict g hV x).symm
  rw [Ideal.map_map, e]

private theorem exists_mem_opensRange_affineBlowupChart_consolidated145 (p : ↥(affineBlowup I)) :
    ∃ c : ↥I, p ∈ (affineBlowupChart I c).opensRange := by
  have hcov : (⨆ c : ↥I, (affineBlowupChart I c).opensRange) = ⊤ := by
    simp only [opensRange_affineBlowupChart_eq_basicOpen]
    exact iSup_proj_basicOpen_reesGenerator_eq_top I
  have hp : p ∈ (⨆ c : ↥I, (affineBlowupChart I c).opensRange) := by
    rw [hcov]; trivial
  simpa using hp


end

private theorem restrict_basicOpen_mem_nonZeroDivisors_consolidated145 {W : Scheme.{u}} {U : W.Opens}
    (hU : IsAffineOpen U) (r : ↥Γ(W, U)) {s : ↥Γ(W, U)} (hs : s ∈ nonZeroDivisors ↥Γ(W, U))
    (hle : W.basicOpen r ≤ U) :
    (W.presheaf.map (homOfLE hle).op).hom s ∈ nonZeroDivisors ↥Γ(W, W.basicOpen r) := by
  have := hU.isLocalization_basicOpen r
  exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers r)
    ↥Γ(W, W.basicOpen r) hs

section
variable {R : Type u} [CommRing R] (I : Ideal R)

private theorem isLocalizationElem_eq_chartFraction_consolidated145 (c a : ↥I) :
    HomogeneousLocalization.Away.isLocalizationElem
        (reesGenerator_mem_reesGrading I c) (reesGenerator_mem_reesGrading I a)
      = chartFraction I c a := by
  apply HomogeneousLocalization.val_injective
  rw [chartFraction_eq_mk]
  simp [HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.val_mk, pow_one]

private theorem affineBlowupChart_preimage_basicOpen_consolidated145 (c : ↥I) (z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)) :
    affineBlowupChart I c ⁻¹ᵁ
        ((affineBlowup I).basicOpen ((chartSectionsIso I c).hom.hom z))
      = PrimeSpectrum.basicOpen z := by
  have e : (⊤ : (Spec (CommRingCat.of
        (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)))).Opens)
      ≤ affineBlowupChart I c ⁻¹ᵁ (affineBlowupChart I c ''ᵁ ⊤) := by
    intro x _
    exact ⟨x, trivial, rfl⟩
  have happ : (affineBlowupChart I c).appLE (affineBlowupChart I c ''ᵁ ⊤) ⊤ e
      = ((affineBlowupChart I c).appIso ⊤).hom := by
    rw [Scheme.Hom.appIso_hom]
    rfl
  have hiso : (((affineBlowupChart I c).appIso ⊤).hom).hom ((chartSectionsIso I c).hom.hom z)
      = (Scheme.ΓSpecIso (CommRingCat.of
          (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)))).inv.hom z := by
    rw [chartSectionsIso_hom_apply]
    exact congrArg
      (fun φ : Γ(Spec (CommRingCat.of
            (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c))), ⊤) ⟶
          Γ(Spec (CommRingCat.of
            (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c))), ⊤) =>
        φ.hom ((Scheme.ΓSpecIso (CommRingCat.of
          (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)))).inv.hom z))
      ((affineBlowupChart I c).appIso ⊤).inv_hom_id
  have h2 : (Spec (CommRingCat.of
        (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)))).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of
          (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)))).inv.hom z)
      = PrimeSpectrum.basicOpen z :=
    basicOpen_eq_of_affine
      (R := CommRingCat.of (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c))) z
  have h1 : (Spec (CommRingCat.of
        (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)))).basicOpen
        (((affineBlowupChart I c).appLE (affineBlowupChart I c ''ᵁ ⊤) ⊤ e).hom
          ((chartSectionsIso I c).hom.hom z))
      = ⊤ ⊓ affineBlowupChart I c ⁻¹ᵁ
          ((affineBlowup I).basicOpen ((chartSectionsIso I c).hom.hom z)) :=
    Scheme.basicOpen_appLE (affineBlowupChart I c) ⊤ (affineBlowupChart I c ''ᵁ ⊤) e
      ((chartSectionsIso I c).hom.hom z)
  rw [happ, hiso, h2, top_inf_eq] at h1
  exact h1.symm

private theorem basicOpen_chartFraction_le_opensRange_consolidated145 (c a : ↥I) :
    (affineBlowup I).basicOpen ((chartSectionsIso I c).hom.hom (chartFraction I c a))
      ≤ (affineBlowupChart I a).opensRange := by
  have hpre : affineBlowupChart I c ⁻¹ᵁ (affineBlowupChart I a).opensRange
      = PrimeSpectrum.basicOpen (chartFraction I c a) := by
    rw [opensRange_affineBlowupChart_eq_basicOpen, affineBlowupChart_eq_awayι, ← isLocalizationElem_eq_chartFraction_consolidated145 I c a]
    exact Proj.awayι_preimage_basicOpen (reesGrading I) (reesGenerator_mem_reesGrading I c) Nat.one_pos
      (reesGenerator_mem_reesGrading I a) Nat.one_pos
  intro p hp
  have hsub : (affineBlowup I).basicOpen ((chartSectionsIso I c).hom.hom (chartFraction I c a))
      ≤ affineBlowupChart I c ''ᵁ ⊤ := Scheme.basicOpen_le _ _
  obtain ⟨q, -, hq⟩ := hsub hp
  rw [← hq] at hp
  have hq2 : q ∈ affineBlowupChart I c ⁻¹ᵁ
      ((affineBlowup I).basicOpen ((chartSectionsIso I c).hom.hom (chartFraction I c a))) := hp
  rw [affineBlowupChart_preimage_basicOpen_consolidated145, ← hpre] at hq2
  rw [← hq]
  exact hq2


end

section
variable {R : Type u} [CommRing R] (I : Ideal R) {W : Scheme.{u}} (h : W ⟶ affineBlowup I)

private theorem basicOpen_chartSectionsRingHom_consolidated145 (c : ↥I) (V : W.Opens)
    (hV : V ≤ h ⁻¹ᵁ (affineBlowupChart I c ''ᵁ ⊤))
    (z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)) :
    W.basicOpen (chartSectionsRingHom I h c V hV z)
      = V ⊓ h ⁻¹ᵁ ((affineBlowup I).basicOpen ((chartSectionsIso I c).hom.hom z)) := by
  rw [chartSectionsRingHom_apply]
  exact Scheme.basicOpen_appLE h V (affineBlowupChart I c ''ᵁ ⊤) hV
    ((chartSectionsIso I c).hom.hom z)

private theorem mem_opensRange_of_mem_basicOpen_chartSectionsRingHom_consolidated145 (c a : ↥I) (V : W.Opens)
    (hV : V ≤ h ⁻¹ᵁ (affineBlowupChart I c ''ᵁ ⊤)) {w : ↥W}
    (hw : w ∈ W.basicOpen (chartSectionsRingHom I h c V hV (chartFraction I c a))) :
    h.base w ∈ (affineBlowupChart I a).opensRange := by
  rw [basicOpen_chartSectionsRingHom_consolidated145 I h c V hV (chartFraction I c a)] at hw
  have hw2 : h.base w ∈
      (affineBlowup I).basicOpen ((chartSectionsIso I c).hom.hom (chartFraction I c a)) := hw.2
  exact basicOpen_chartFraction_le_opensRange_consolidated145 I c a hw2

theorem mem_opensRange_affineBlowupChart_of_ideal_eq_span (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)))
    (w : ↥W) (a : ↥I)
    (hex : ∃ V : W.affineOpens, w ∈ (V : W.Opens) ∧
      ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)).ideal V =
        Ideal.span
          {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens) (a : R)}) :
    h.base w ∈ (affineBlowupChart I a).opensRange := by
  obtain ⟨V, hwV, hVspan⟩ := hex
  obtain ⟨c, hc⟩ := exists_mem_opensRange_affineBlowupChart_consolidated145 I (h.base w)
  obtain ⟨Uaff, g, hwU, hgnzd, hUspan⟩ := hcart w
  have hwpre : w ∈ ((V : W.Opens) ⊓ h ⁻¹ᵁ (affineBlowupChart I c ''ᵁ ⊤) : W.Opens) := by
    refine ⟨hwV, ?_⟩
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact hc
  obtain ⟨r, hrle, hwr⟩ := Uaff.2.exists_basicOpen_le
    (⟨w, hwpre⟩ : ↥((V : W.Opens) ⊓ h ⁻¹ᵁ (affineBlowupChart I c ''ᵁ ⊤) : W.Opens)) hwU
  have hbaff : IsAffineOpen (W.basicOpen r) := Uaff.2.basicOpen r
  have hVV : W.basicOpen r ≤ (V : W.Opens) := le_trans hrle inf_le_left
  have hVc : W.basicOpen r ≤ h ⁻¹ᵁ (affineBlowupChart I c ''ᵁ ⊤) := le_trans hrle inf_le_right
  have hVU : W.basicOpen r ≤ (Uaff : W.Opens) := W.basicOpen_le r
  have hmapSpan : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r)) I
      = Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r) (c : R)} := by
    have e1 := comap_specIdealSheaf_ideal I (h ≫ AffineBlowup.toSpec I)
      (⟨W.basicOpen r, hbaff⟩ : W.affineOpens)
    have e2 := comap_specIdealSheaf_ideal_eq_span I h c
      (⟨W.basicOpen r, hbaff⟩ : W.affineOpens) hVc
    exact e1.symm.trans e2
  have hmapPow : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r)) I
      = Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r) (a : R)} := by
    have e1 : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens)) I
        = Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens) (a : R)} :=
      (comap_specIdealSheaf_ideal I (h ≫ AffineBlowup.toSpec I) V).symm.trans hVspan
    rw [map_sectionsRingHom_restrict_consolidated145 I (h ≫ AffineBlowup.toSpec I) hVV, e1, Ideal.map_span,
      Set.image_singleton, ← sectionsRingHom_restrict (h ≫ AffineBlowup.toSpec I) hVV (a : R)]
  have hmapEq : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r)) I
      = Ideal.span {(W.presheaf.map (homOfLE hVU).op).hom g} := by
    have e1 : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (Uaff : W.Opens)) I
        = Ideal.span {g} :=
      (comap_specIdealSheaf_ideal I (h ≫ AffineBlowup.toSpec I) Uaff).symm.trans hUspan
    rw [map_sectionsRingHom_restrict_consolidated145 I (h ≫ AffineBlowup.toSpec I) hVU, e1, Ideal.map_span,
      Set.image_singleton]
  have hcnzd : sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r) (c : R)
      ∈ nonZeroDivisors ↥Γ(W, W.basicOpen r) :=
    mem_nonZeroDivisors_of_span_singleton_eq_consolidated145 (restrict_basicOpen_mem_nonZeroDivisors_consolidated145 Uaff.2 r hgnzd hVU)
      (hmapEq.symm.trans hmapSpan)
  have hkey : sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r) (a : R)
      = chartSectionsRingHom I h c (W.basicOpen r) hVc (chartFraction I c a) *
        sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r) (c : R) := by
    rw [← chartSectionsRingHom_chartRingHom I h c (W.basicOpen r) hVc (a : R),
      ← chartSectionsRingHom_chartRingHom I h c (W.basicOpen r) hVc (c : R), ← map_mul,
      chartRingHom_coe_eq_chartFraction_mul I c a]
  have hcmem : sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r) (c : R)
      ∈ Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r) (a : R)} := by
    rw [← hmapPow]
    exact Ideal.mem_map_of_mem _ c.2
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hcmem
  have hnz := mem_nonZeroDivisors_iff.mp hcnzd
  have h1 : sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen r) (c : R) *
      (1 - d * chartSectionsRingHom I h c (W.basicOpen r) hVc (chartFraction I c a)) = 0 := by
    linear_combination -hd + d * hkey
  have h2 : (1 : ↥Γ(W, W.basicOpen r)) -
      d * chartSectionsRingHom I h c (W.basicOpen r) hVc (chartFraction I c a) = 0 := hnz.1 _ h1
  have hunit : IsUnit (chartSectionsRingHom I h c (W.basicOpen r) hVc (chartFraction I c a)) :=
    ⟨⟨chartSectionsRingHom I h c (W.basicOpen r) hVc (chartFraction I c a), d,
      by linear_combination -h2, by linear_combination -h2⟩, rfl⟩
  have hmem : w ∈ W.basicOpen (chartSectionsRingHom I h c (W.basicOpen r) hVc (chartFraction I c a)) := by
    rw [W.basicOpen_of_isUnit hunit]
    exact hwr
  exact mem_opensRange_of_mem_basicOpen_chartSectionsRingHom_consolidated145 I h c a (W.basicOpen r) hVc hmem

private theorem mem_preimage_affineBlowupChart_iff_consolidated145 (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)))
    (a : ↥I) (w : ↥W) :
    w ∈ h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) ↔
      ∃ V : W.affineOpens, w ∈ (V : W.Opens) ∧
        ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)).ideal V =
          Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens) (a : R)} := by
  constructor
  · intro hw
    have hw' : w ∈ ((h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) : W.Opens) : Set ↥W) := hw
    obtain ⟨v, hv, hwV, hVle⟩ :=
      (W.isBasis_affineOpens).exists_subset_of_mem_open hw'
        (TopologicalSpace.Opens.isOpen (h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤)))
    obtain ⟨V, hVmem, rfl⟩ := hv
    have hle : ((⟨V, hVmem⟩ : W.affineOpens) : W.Opens)
        ≤ h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) := SetLike.coe_subset_coe.mp hVle
    exact ⟨⟨V, hVmem⟩, hwV, comap_specIdealSheaf_ideal_eq_span I h a ⟨V, hVmem⟩ hle⟩
  · intro hex
    have hmem := mem_opensRange_affineBlowupChart_of_ideal_eq_span I h hcart w a hex
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact hmem


end

theorem preimage_affineBlowupChart_eq_of_toSpec_eq {R : Type u} [CommRing R] {I : Ideal R} {W : Scheme.{u}}
    (h₁ h₂ : W ⟶ affineBlowup I)
    (he : h₁ ≫ AffineBlowup.toSpec I = h₂ ≫ AffineBlowup.toSpec I)
    (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h₁ ≫ AffineBlowup.toSpec I)))
    (a : ↥I) :
    h₁ ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) = h₂ ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) := by
  have hcart₂ : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h₂ ≫ AffineBlowup.toSpec I)) := by
    rw [← he]
    exact hcart
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro w
  have e1 := mem_preimage_affineBlowupChart_iff_consolidated145 I h₁ hcart a w
  have e2 := mem_preimage_affineBlowupChart_iff_consolidated145 I h₂ hcart₂ a w
  rw [he] at e1
  exact e1.trans e2.symm

section
variable {R : Type u} [CommRing R] (I : Ideal R) {W : Scheme.{u}} (h : W ⟶ affineBlowup I)

theorem exists_chart_affineOpen_mem_nonZeroDivisors (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)))
    (w : ↥W) :
    ∃ (a : ↥I) (V : W.affineOpens), w ∈ (V : W.Opens) ∧
      (V : W.Opens) ≤ h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) ∧
      sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens) (a : R) ∈
        nonZeroDivisors ↥Γ(W, (V : W.Opens)) := by
  obtain ⟨a, ha⟩ := exists_mem_opensRange_affineBlowupChart_consolidated145 I (h.base w)
  have hwU₀ : w ∈ h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) := by
    have h1 := ha
    rw [← Scheme.Hom.image_top_eq_opensRange (affineBlowupChart I a)] at h1
    exact h1
  obtain ⟨U, c, hwU, hcnzd, hideal⟩ := hcart w
  have hUaff : IsAffineOpen (U : W.Opens) := U.2
  obtain ⟨t, htle, hwt⟩ :=
    hUaff.exists_basicOpen_le (V := h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤)) ⟨w, hwU₀⟩ hwU
  have hwt' : w ∈ W.basicOpen t := hwt
  have : IsLocalization.Away t ↥Γ(W, W.basicOpen t) := hUaff.isLocalization_basicOpen t
  have hres : sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t)
      = RingHom.comp (algebraMap (↥Γ(W, (U : W.Opens))) (↥Γ(W, W.basicOpen t)))
          (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (U : W.Opens)) := by
    ext r
    exact sectionsRingHom_restrict (h ≫ AffineBlowup.toSpec I) (W.basicOpen_le t) r
  have hmapU : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (U : W.Opens)) I
      = Ideal.span {c} := by
    rw [← comap_specIdealSheaf_ideal I (h ≫ AffineBlowup.toSpec I) U]
    exact hideal
  have hmapV : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t)) I
      = Ideal.span {algebraMap (↥Γ(W, (U : W.Opens))) (↥Γ(W, W.basicOpen t)) c} := by
    rw [hres, ← Ideal.map_map, hmapU, Ideal.map_span, Set.image_singleton]
  have e1 : ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)).ideal
        ⟨W.basicOpen t, hUaff.basicOpen t⟩
      = Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t)) I :=
    comap_specIdealSheaf_ideal I (h ≫ AffineBlowup.toSpec I) ⟨W.basicOpen t, hUaff.basicOpen t⟩
  have e2 : ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)).ideal
        ⟨W.basicOpen t, hUaff.basicOpen t⟩
      = Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t) (a : R)} :=
    comap_specIdealSheaf_ideal_eq_span I h a ⟨W.basicOpen t, hUaff.basicOpen t⟩ htle
  have hspan : Ideal.span {algebraMap (↥Γ(W, (U : W.Opens))) (↥Γ(W, W.basicOpen t)) c}
      = Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t) (a : R)} :=
    hmapV.symm.trans (e1.symm.trans e2)
  have hmem2 : algebraMap (↥Γ(W, (U : W.Opens))) (↥Γ(W, W.basicOpen t)) c
      ∈ Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t) (a : R)} := by
    rw [← hspan]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hmem2
  have hcnzd' : algebraMap (↥Γ(W, (U : W.Opens))) (↥Γ(W, W.basicOpen t)) c
      ∈ nonZeroDivisors ↥Γ(W, W.basicOpen t) :=
    IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers t)
      ↥Γ(W, W.basicOpen t) hcnzd
  have hdnzd : d * sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t) (a : R)
      ∈ nonZeroDivisors ↥Γ(W, W.basicOpen t) := by
    rw [hd]
    exact hcnzd'
  exact ⟨a, ⟨W.basicOpen t, hUaff.basicOpen t⟩, hwt', htle,
    (mul_mem_nonZeroDivisors.mp hdnzd).2⟩

private theorem chartSectionsRingHom_mul_pow_eq_consolidated145 (a : ↥I) (V : W.Opens)
    (hV : V ≤ h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤))
    (z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) (n : ℕ) (r : R)
    (hnr : z * chartRingHom I a (a : R) ^ n = chartRingHom I a r) :
    chartSectionsRingHom I h a V hV z * sectionsRingHom (h ≫ AffineBlowup.toSpec I) V (a : R) ^ n
      = sectionsRingHom (h ≫ AffineBlowup.toSpec I) V r := by
  have hpow : chartSectionsRingHom I h a V hV (chartRingHom I a (a : R) ^ n)
      = chartSectionsRingHom I h a V hV (chartRingHom I a (a : R)) ^ n :=
    map_pow (chartSectionsRingHom I h a V hV) (chartRingHom I a (a : R)) n
  have h0 : chartSectionsRingHom I h a V hV (z * chartRingHom I a (a : R) ^ n)
      = chartSectionsRingHom I h a V hV (chartRingHom I a r) := by rw [hnr]
  rw [map_mul, hpow, chartSectionsRingHom_chartRingHom, chartSectionsRingHom_chartRingHom] at h0
  exact h0


end

private def openCoverBySpecOfIsAffineOpen_consolidated145 {W : Scheme.{u}} (VV : ↥W → W.Opens)
    (hVaff : ∀ w : ↥W, IsAffineOpen (VV w)) (hmem : ∀ w : ↥W, w ∈ VV w) : W.OpenCover :=
  Scheme.Cover.mkOfCovers ↥W (fun w => Spec Γ(W, VV w)) (fun w => (hVaff w).fromSpec)
    (fun x => by
      have hx : x ∈ Set.range ((hVaff x).fromSpec).base := by
        rw [(hVaff x).range_fromSpec]
        exact hmem x
      obtain ⟨y, hy⟩ := hx
      exact ⟨x, y, hy⟩)
    (fun w => inferInstance)

section
variable {R : Type u} [CommRing R] {I : Ideal R} {W : Scheme.{u}} (h₁ h₂ : W ⟶ affineBlowup I) (he : h₁ ≫ AffineBlowup.toSpec I = h₂ ≫ AffineBlowup.toSpec I) (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h₁ ≫ AffineBlowup.toSpec I)))
include he hcart

private theorem fromSpec_comp_eq_of_toSpec_eq_consolidated145 (a : ↥I) (V : W.Opens) (hVaff : IsAffineOpen V)
    (hle : V ≤ h₁ ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤))
    (hnzd : sectionsRingHom (h₁ ≫ AffineBlowup.toSpec I) V (a : R) ∈
      nonZeroDivisors ↥Γ(W, V)) :
    hVaff.fromSpec ≫ h₁ = hVaff.fromSpec ≫ h₂ := by
  have hle₂ : V ≤ h₂ ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) := by
    rw [← preimage_affineBlowupChart_eq_of_toSpec_eq h₁ h₂ he hcart a]
    exact hle
  have hTaff : IsAffineOpen (affineBlowupChart I a ''ᵁ ⊤) :=
    (isAffineOpen_top _).image_of_isOpenImmersion (affineBlowupChart I a)
  have hcp : chartSectionsRingHom I h₁ a V hle = chartSectionsRingHom I h₂ a V hle₂ := by
    refine RingHom.ext fun z => ?_
    obtain ⟨n, r, hnr⟩ := exists_mul_pow_eq_chartRingHom I a z
    have k1 := chartSectionsRingHom_mul_pow_eq_consolidated145 I h₁ a V hle z n r hnr
    have k2 := chartSectionsRingHom_mul_pow_eq_consolidated145 I h₂ a V hle₂ z n r hnr
    rw [← he] at k2
    exact (mul_cancel_right_mem_nonZeroDivisors (pow_mem hnzd n)).mp (k1.trans k2.symm)
  have hmor : (chartSectionsIso I a).hom ≫ h₁.appLE (affineBlowupChart I a ''ᵁ ⊤) V hle
      = (chartSectionsIso I a).hom ≫ h₂.appLE (affineBlowupChart I a ''ᵁ ⊤) V hle₂ :=
    CommRingCat.hom_ext hcp
  have happ : h₁.appLE (affineBlowupChart I a ''ᵁ ⊤) V hle
      = h₂.appLE (affineBlowupChart I a ''ᵁ ⊤) V hle₂ := by
    calc h₁.appLE (affineBlowupChart I a ''ᵁ ⊤) V hle
        = (chartSectionsIso I a).inv ≫ (chartSectionsIso I a).hom ≫
            h₁.appLE (affineBlowupChart I a ''ᵁ ⊤) V hle := by
          rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = (chartSectionsIso I a).inv ≫ (chartSectionsIso I a).hom ≫
            h₂.appLE (affineBlowupChart I a ''ᵁ ⊤) V hle₂ := by rw [hmor]
      _ = h₂.appLE (affineBlowupChart I a ''ᵁ ⊤) V hle₂ := by
          rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have E₁ := IsAffineOpen.SpecMap_appLE_fromSpec h₁ hTaff hVaff hle
  have E₂ := IsAffineOpen.SpecMap_appLE_fromSpec h₂ hTaff hVaff hle₂
  rw [← E₁, ← E₂, happ]

theorem affineBlowup_hom_ext :
    h₁ = h₂ := by
  classical
  choose aa VV hmem hle hnzd using exists_chart_affineOpen_mem_nonZeroDivisors I h₁ hcart
  refine (openCoverBySpecOfIsAffineOpen_consolidated145 (fun w => (VV w : W.Opens)) (fun w => (VV w).2) hmem).hom_ext
    h₁ h₂ fun w => ?_
  exact fromSpec_comp_eq_of_toSpec_eq_consolidated145 h₁ h₂ he hcart (aa w) ((VV w : W.Opens)) (VV w).2
    (hle w) (hnzd w)


end

end FunctorialResolution.Blowup
end
end

-- Source: Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace FunctorialResolution.Blowup

theorem IsBlowupAlongIdealSheaf.of_isIso {X X' : Scheme.{u}} (f : X' ⟶ X) [IsIso f] :
    IsBlowupAlongIdealSheaf f (⊤ : X.IdealSheafData) := by
  refine And.intro (isLocallyGeneratedByNonZeroDivisor_comap_top f) ?_
  intro W g _
  refine ExistsUnique.intro (g ≫ inv f) ?_ ?_
  · simp
  · intro a ha
    rw [← ha]
    simp

theorem isBlowupAlongIdealSheaf_id_top (X : Scheme.{u}) : IsBlowupAlongIdealSheaf (𝟙 X) (⊤ : X.IdealSheafData) :=
  IsBlowupAlongIdealSheaf.of_isIso (𝟙 X)

theorem comap_eq_top_of_notMem_support {X X' : Scheme.{u}} (f : X' ⟶ X)
    (I : X.IdealSheafData) (h : ∀ x : X', f.base x ∉ I.support) :
    I.comap f = ⊤ := by
  have hs : (I.comap f).support = ⊥ := by
    rw [Scheme.IdealSheafData.support_comap]
    refine SetLike.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · exact absurd (show f.base x ∈ I.support from hx) (h x)
    · exact (show False from hx).elim
  exact (Scheme.IdealSheafData.support_eq_bot_iff _).mp hs

private theorem range_comp_coprod_inl_subset_consolidated147 {X Y Z : Scheme.{u}} (f : Z ⟶ X) :
    Set.range ⇑(f ≫ (coprod.inl : X ⟶ X ⨿ Y)).base
      ⊆ Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base := by
  rintro _ ⟨z, rfl⟩
  exact ⟨f.base z, by simp⟩

theorem ker_comp_coprod_inl_comap_inr {X Y Z : Scheme.{u}} (f : Z ⟶ X)
    [QuasiCompact (f ≫ (coprod.inl : X ⟶ X ⨿ Y))] :
    (f ≫ (coprod.inl : X ⟶ X ⨿ Y)).ker.comap (coprod.inr : Y ⟶ X ⨿ Y) = ⊤ := by
  refine comap_eq_top_of_notMem_support (coprod.inr : Y ⟶ X ⨿ Y)
    ((f ≫ (coprod.inl : X ⟶ X ⨿ Y)).ker) ?_
  intro y hy
  have hy' : (coprod.inr : Y ⟶ X ⨿ Y).base y ∈
      ((f ≫ (coprod.inl : X ⟶ X ⨿ Y)).ker.support : Set ↥(X ⨿ Y)) := hy
  rw [Scheme.Hom.support_ker] at hy'
  have hsub : closure (Set.range ⇑(f ≫ (coprod.inl : X ⟶ X ⨿ Y)).base)
      ⊆ Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base :=
    closure_minimal (range_comp_coprod_inl_subset_consolidated147 f) (isClosed_range_coprod_inl X Y)
  have h2 : (coprod.inr : Y ⟶ X ⨿ Y).base y ∈ Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base :=
    Set.mem_range_self y
  rw [range_coprod_inr_eq_compl X Y] at h2
  exact h2 (hsub hy')

private theorem map_ker_comp_of_surjective_consolidated147 {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (hφ : Function.Surjective φ) :
    Ideal.map φ (RingHom.ker (ψ.comp φ)) = RingHom.ker ψ := by
  rw [RingHom.ker_eq_comap_bot (ψ.comp φ), ← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot]
  exact Ideal.map_comap_of_surjective φ hφ _

private theorem surjective_of_isIso_consolidated147 {A B : CommRingCat.{u}} (φ : A ⟶ B) (hφ : IsIso φ) :
    Function.Surjective (CommRingCat.Hom.hom φ) := by
  have := hφ
  intro y
  exact ⟨CommRingCat.Hom.hom (inv φ) y,
    congrArg (fun ψ : B ⟶ B => CommRingCat.Hom.hom ψ y) (IsIso.inv_hom_id φ)⟩

section
variable {W Z : Scheme.{u}} (g : W ⟶ Z) [IsOpenImmersion g] (V : W.Opens)

private theorem isAffineOpen_image_consolidated147 (hV : IsAffineOpen V) : IsAffineOpen (g ''ᵁ V) :=
  hV.image_of_isOpenImmersion g

private theorem preimage_image_opens_consolidated147 : g ⁻¹ᵁ (g ''ᵁ V) = V := by
  refine TopologicalSpace.Opens.ext ?_
  show ⇑g.base ⁻¹' (⇑g.base '' (V : Set ↥W)) = (V : Set ↥W)
  exact Set.preimage_image_eq _ g.isOpenEmbedding.injective


end

private theorem ker_ideal_eq_ker_app_consolidated147 {T W : Scheme.{u}} (f : T ⟶ W) [QuasiCompact f]
    (U : W.affineOpens) :
    f.ker.ideal U = RingHom.ker (CommRingCat.Hom.hom (f.app (U : W.Opens))) := by
  simp

section
variable {T W Z : Scheme.{u}} (f : T ⟶ W) (g : W ⟶ Z)

private theorem map_appLE_ker_comp_consolidated147 (U : Z.Opens) (V : W.Opens) (hUV : g ⁻¹ᵁ U = V) (e : V ≤ g ⁻¹ᵁ U)
    (hsurj : Function.Surjective (CommRingCat.Hom.hom (g.app U))) :
    Ideal.map (CommRingCat.Hom.hom (g.appLE U V e))
        (RingHom.ker (CommRingCat.Hom.hom ((f ≫ g).app U)))
      = RingHom.ker (CommRingCat.Hom.hom (f.app V)) := by
  subst hUV
  have hid : g.appLE U (g ⁻¹ᵁ U) e = g.app U := by
    show g.app U ≫ W.presheaf.map (homOfLE e).op = g.app U
    have h1 : (homOfLE e).op = 𝟙 (Opposite.op (g ⁻¹ᵁ U)) := rfl
    rw [h1, W.presheaf.map_id, Category.comp_id]
  have hcomp : CommRingCat.Hom.hom ((f ≫ g).app U)
      = RingHom.comp (CommRingCat.Hom.hom (f.app (g ⁻¹ᵁ U)))
          (CommRingCat.Hom.hom (g.app U)) := rfl
  rw [hid, hcomp]
  exact map_ker_comp_of_surjective_consolidated147 _ _ hsurj

private theorem ker_comap_of_isOpenImmersion_consolidated147 [IsOpenImmersion g] [QuasiCompact f] [QuasiCompact (f ≫ g)] :
    (f ≫ g).ker.comap g = f.ker := by
  have key : ∀ V : W.affineOpens, ((f ≫ g).ker.comap g).ideal V = f.ker.ideal V := by
    intro V
    have hU : IsAffineOpen (g ''ᵁ (V : W.Opens)) := isAffineOpen_image_consolidated147 g (V : W.Opens) V.2
    have hpre : g ⁻¹ᵁ (g ''ᵁ (V : W.Opens)) = (V : W.Opens) :=
      preimage_image_opens_consolidated147 g (V : W.Opens)
    have e : (V : W.Opens) ≤ g ⁻¹ᵁ (g ''ᵁ (V : W.Opens)) := hpre.ge
    have h1 : ((f ≫ g).ker.comap g).ideal V
        = Ideal.map (CommRingCat.Hom.hom (g.appLE (g ''ᵁ (V : W.Opens)) (V : W.Opens) e))
            ((f ≫ g).ker.ideal ⟨g ''ᵁ (V : W.Opens), hU⟩) :=
      Scheme.IdealSheafData.comap_ideal_eq_map_appLE ((f ≫ g).ker) g
        ⟨g ''ᵁ (V : W.Opens), hU⟩ V e
    rw [h1, ker_ideal_eq_ker_app_consolidated147 (f ≫ g) ⟨g ''ᵁ (V : W.Opens), hU⟩, ker_ideal_eq_ker_app_consolidated147 f V]
    exact map_appLE_ker_comp_consolidated147 f g (g ''ᵁ (V : W.Opens)) (V : W.Opens) hpre e
      (surjective_of_isIso_consolidated147 (g.app (g ''ᵁ (V : W.Opens))) inferInstance)
  ext V
  rw [key V]


end

theorem ker_comp_coprod_inl_comap_inl {X Y Z : Scheme.{u}} (f : Z ⟶ X)
    [QuasiCompact f] [QuasiCompact (f ≫ (coprod.inl : X ⟶ X ⨿ Y))] :
    (f ≫ (coprod.inl : X ⟶ X ⨿ Y)).ker.comap (coprod.inl : X ⟶ X ⨿ Y) = f.ker :=
  ker_comap_of_isOpenImmersion_consolidated147 f (coprod.inl : X ⟶ X ⨿ Y)

private theorem ideal_eq_of_map_eq_of_bijective_consolidated147 {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Bijective φ) {K L : Ideal A}
    (h : Ideal.map φ K = Ideal.map φ L) : K = L := by
  have key : ∀ K' L' : Ideal A, Ideal.map φ K' = Ideal.map φ L' → K' ≤ L' := by
    intro K' L' h' x hx
    have hx' : φ x ∈ Ideal.map φ L' := by
      rw [← h']
      exact Ideal.mem_map_of_mem φ hx
    obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective φ hφ.2).mp hx'
    rwa [← hφ.1 hxy]
  exact le_antisymm (key K L h) (key L K h.symm)

private theorem bijective_of_isIso_consolidated147 {A B : CommRingCat.{u}} (φ : A ⟶ B) [IsIso φ] :
    Function.Bijective (CommRingCat.Hom.hom φ) := by
  have h3 : ∀ c : A, CommRingCat.Hom.hom (inv φ) (CommRingCat.Hom.hom φ c) = c := fun c =>
    congrArg (fun ψ : A ⟶ A => CommRingCat.Hom.hom ψ c) (IsIso.hom_inv_id φ)
  constructor
  · intro a a' h
    have h2 : CommRingCat.Hom.hom (inv φ) (CommRingCat.Hom.hom φ a)
        = CommRingCat.Hom.hom (inv φ) (CommRingCat.Hom.hom φ a') := by rw [h]
    simp only [h3] at h2
    exact h2
  · intro b
    exact ⟨CommRingCat.Hom.hom (inv φ) b,
      congrArg (fun ψ : B ⟶ B => CommRingCat.Hom.hom ψ b) (IsIso.inv_hom_id φ)⟩

section
variable {W Z : Scheme.{u}} (g : W ⟶ Z) [IsOpenImmersion g]

private theorem appLE_image_bijective_of_isOpenImmersion_consolidated147 (V : W.Opens) (e : V ≤ g ⁻¹ᵁ (g ''ᵁ V)) :
    Function.Bijective (CommRingCat.Hom.hom (g.appLE (g ''ᵁ V) V e)) := by
  have hpre : g ⁻¹ᵁ (g ''ᵁ V) = V := preimage_image_opens_consolidated147 g V
  have : IsIso (homOfLE e) := ⟨homOfLE hpre.le, rfl, rfl⟩
  have : IsIso (g.appLE (g ''ᵁ V) V e) := by
    show IsIso (g.app (g ''ᵁ V) ≫ W.presheaf.map (homOfLE e).op)
    infer_instance
  exact bijective_of_isIso_consolidated147 (g.appLE (g ''ᵁ V) V e)

private theorem ideal_image_eq_of_comap_eq_consolidated147 {I J : Z.IdealSheafData} (h : I.comap g = J.comap g) (V : ↥(W.affineOpens)) :
    I.ideal ⟨g ''ᵁ (V : W.Opens), isAffineOpen_image_consolidated147 g (V : W.Opens) V.2⟩
      = J.ideal ⟨g ''ᵁ (V : W.Opens), isAffineOpen_image_consolidated147 g (V : W.Opens) V.2⟩ := by
  have e : (V : W.Opens) ≤ g ⁻¹ᵁ (g ''ᵁ (V : W.Opens)) :=
    (preimage_image_opens_consolidated147 g (V : W.Opens)).ge
  have h1 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE I g
    ⟨g ''ᵁ (V : W.Opens), isAffineOpen_image_consolidated147 g (V : W.Opens) V.2⟩ V e
  have h2 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE J g
    ⟨g ''ᵁ (V : W.Opens), isAffineOpen_image_consolidated147 g (V : W.Opens) V.2⟩ V e
  have h3 : (I.comap g).ideal V = (J.comap g).ideal V := by rw [h]
  rw [h1, h2] at h3
  exact ideal_eq_of_map_eq_of_bijective_consolidated147 _ (appLE_image_bijective_of_isOpenImmersion_consolidated147 g (V : W.Opens) e) h3


end

private theorem exists_affineOpen_mem_consolidated147 (X : Scheme.{u}) (x : ↥X) :
    ∃ V : ↥(X.affineOpens), x ∈ ((V : X.Opens) : Set ↥X) := by
  have h : x ∈ (⨆ V : ↥(X.affineOpens), (V : X.Opens)) := by
    rw [iSup_affineOpens_eq_top X]
    exact trivial
  obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp h
  exact ⟨V, SetLike.mem_coe.mpr hV⟩

theorem idealSheafData_ext_coprod {X Y : Scheme.{u}} (I J : (X ⨿ Y).IdealSheafData)
    (hl : I.comap (coprod.inl : X ⟶ X ⨿ Y) = J.comap (coprod.inl : X ⟶ X ⨿ Y))
    (hr : I.comap (coprod.inr : Y ⟶ X ⨿ Y) = J.comap (coprod.inr : Y ⟶ X ⨿ Y)) :
    I = J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (Sum.elim
      (fun V : ↥(X.affineOpens) =>
        (⟨(coprod.inl : X ⟶ X ⨿ Y) ''ᵁ (V : X.Opens),
          isAffineOpen_image_consolidated147 (coprod.inl : X ⟶ X ⨿ Y) (V : X.Opens) V.2⟩ :
            ↥((X ⨿ Y).affineOpens)))
      (fun V : ↥(Y.affineOpens) =>
        (⟨(coprod.inr : Y ⟶ X ⨿ Y) ''ᵁ (V : Y.Opens),
          isAffineOpen_image_consolidated147 (coprod.inr : Y ⟶ X ⨿ Y) (V : Y.Opens) V.2⟩ :
            ↥((X ⨿ Y).affineOpens)))) ?_ ?_
  · rw [eq_top_iff]
    intro z _
    by_cases hz : z ∈ Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base
    · obtain ⟨x, rfl⟩ := hz
      obtain ⟨V, hV⟩ := exists_affineOpen_mem_consolidated147 X x
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨Sum.inl V, ?_⟩
      exact SetLike.mem_coe.mp (Set.mem_image_of_mem _ hV)
    · have hz' : z ∈ Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base := by
        rw [range_coprod_inr_eq_compl X Y]
        exact hz
      obtain ⟨y, rfl⟩ := hz'
      obtain ⟨V, hV⟩ := exists_affineOpen_mem_consolidated147 Y y
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨Sum.inr V, ?_⟩
      exact SetLike.mem_coe.mp (Set.mem_image_of_mem _ hV)
  · rintro (V | V)
    · exact ideal_image_eq_of_comap_eq_consolidated147 (coprod.inl : X ⟶ X ⨿ Y) hl V
    · exact ideal_image_eq_of_comap_eq_consolidated147 (coprod.inr : Y ⟶ X ⨿ Y) hr V

private theorem base_comp_apply_consolidated147 {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W) (x : U) :
    (f ≫ g).base x = g.base (f.base x) := by simp

section
variable {A B A' B' : Scheme.{u}} (p : A' ⟶ A) (q : B' ⟶ B)

private theorem range_fst_subset_range_inl_consolidated147 (s : PullbackCone (coprod.map p q) (coprod.inl : A ⟶ A ⨿ B)) :
    Set.range ⇑(PullbackCone.fst s).base ⊆ Set.range ⇑(coprod.inl : A' ⟶ A' ⨿ B').base := by
  rintro _ ⟨t, rfl⟩
  by_contra hmem
  have hy : (PullbackCone.fst s).base t ∈ Set.range ⇑(coprod.inr : B' ⟶ A' ⨿ B').base := by
    rw [range_coprod_inr_eq_compl A' B', Set.mem_compl_iff]
    exact hmem
  obtain ⟨b, hb⟩ := hy
  have e1 : (coprod.map p q).base ((PullbackCone.fst s).base t)
      = (coprod.inl : A ⟶ A ⨿ B).base ((PullbackCone.snd s).base t) := by
    have h := congrArg (fun m : s.pt ⟶ A ⨿ B => m.base t) s.condition
    simpa using h
  have hmapr : ((coprod.inr : B' ⟶ A' ⨿ B') ≫ coprod.map p q)
      = q ≫ (coprod.inr : B ⟶ A ⨿ B) := by simp
  have e2 : (coprod.map p q).base ((coprod.inr : B' ⟶ A' ⨿ B').base b)
      = (coprod.inr : B ⟶ A ⨿ B).base (q.base b) := by
    rw [← base_comp_apply_consolidated147, hmapr, base_comp_apply_consolidated147]
  have key : (coprod.map p q).base ((PullbackCone.fst s).base t)
      = (coprod.map p q).base ((coprod.inr : B' ⟶ A' ⨿ B').base b) := by rw [hb]
  have hfin : (coprod.inl : A ⟶ A ⨿ B).base ((PullbackCone.snd s).base t)
      = (coprod.inr : B ⟶ A ⨿ B).base (q.base b) := by rw [← e1, key, e2]
  have hmem2 : (coprod.inl : A ⟶ A ⨿ B).base ((PullbackCone.snd s).base t)
      ∈ Set.range ⇑(coprod.inr : B ⟶ A ⨿ B).base := ⟨q.base b, hfin.symm⟩
  rw [range_coprod_inr_eq_compl A B] at hmem2
  exact hmem2 ⟨(PullbackCone.snd s).base t, rfl⟩

private theorem range_fst_subset_range_inr_consolidated147 (s : PullbackCone (coprod.map p q) (coprod.inr : B ⟶ A ⨿ B)) :
    Set.range ⇑(PullbackCone.fst s).base ⊆ Set.range ⇑(coprod.inr : B' ⟶ A' ⨿ B').base := by
  rintro _ ⟨t, rfl⟩
  rw [range_coprod_inr_eq_compl A' B', Set.mem_compl_iff]
  intro hy
  obtain ⟨a, ha⟩ := hy
  have e1 : (coprod.map p q).base ((PullbackCone.fst s).base t)
      = (coprod.inr : B ⟶ A ⨿ B).base ((PullbackCone.snd s).base t) := by
    have h := congrArg (fun m : s.pt ⟶ A ⨿ B => m.base t) s.condition
    simpa using h
  have hmapl : ((coprod.inl : A' ⟶ A' ⨿ B') ≫ coprod.map p q)
      = p ≫ (coprod.inl : A ⟶ A ⨿ B) := by simp
  have e2 : (coprod.map p q).base ((coprod.inl : A' ⟶ A' ⨿ B').base a)
      = (coprod.inl : A ⟶ A ⨿ B).base (p.base a) := by
    rw [← base_comp_apply_consolidated147, hmapl, base_comp_apply_consolidated147]
  have key : (coprod.map p q).base ((PullbackCone.fst s).base t)
      = (coprod.map p q).base ((coprod.inl : A' ⟶ A' ⨿ B').base a) := by rw [ha]
  have hfin : (coprod.inr : B ⟶ A ⨿ B).base ((PullbackCone.snd s).base t)
      = (coprod.inl : A ⟶ A ⨿ B).base (p.base a) := by rw [← e1, key, e2]
  have hmem2 : (coprod.inr : B ⟶ A ⨿ B).base ((PullbackCone.snd s).base t)
      ∈ Set.range ⇑(coprod.inr : B ⟶ A ⨿ B).base := ⟨(PullbackCone.snd s).base t, rfl⟩
  rw [range_coprod_inr_eq_compl A B, hfin] at hmem2
  exact hmem2 ⟨p.base a, rfl⟩

private theorem isPullback_coprod_inl_map_consolidated147 :
    IsPullback (coprod.inl : A' ⟶ A' ⨿ B') p (coprod.map p q) (coprod.inl : A ⟶ A ⨿ B) := by
  have hw : (coprod.inl : A' ⟶ A' ⨿ B') ≫ coprod.map p q
      = p ≫ (coprod.inl : A ⟶ A ⨿ B) := by simp
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s)
      (range_fst_subset_range_inl_consolidated147 p q s)) ?_ ?_ ?_)
  · intro s
    simp [IsOpenImmersion.lift_fac]
  · intro s
    have hl : IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s)
        (range_fst_subset_range_inl_consolidated147 p q s) ≫ (coprod.inl : A' ⟶ A' ⨿ B')
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : (IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s)
          (range_fst_subset_range_inl_consolidated147 p q s) ≫ p) ≫ (coprod.inl : A ⟶ A ⨿ B)
        = PullbackCone.snd s ≫ (coprod.inl : A ⟶ A ⨿ B) := by
      rw [Category.assoc, ← hw, ← Category.assoc, hl]
      exact s.condition
    exact (cancel_mono _).mp h2
  · intro s m hm _
    have hl : IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s)
        (range_fst_subset_range_inl_consolidated147 p q s) ≫ (coprod.inl : A' ⟶ A' ⨿ B')
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : m ≫ (coprod.inl : A' ⟶ A' ⨿ B')
        = IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s)
            (range_fst_subset_range_inl_consolidated147 p q s) ≫ (coprod.inl : A' ⟶ A' ⨿ B') := by
      rw [hm, hl]
    exact (cancel_mono _).mp h2

private theorem isPullback_coprod_inr_map_consolidated147 :
    IsPullback (coprod.inr : B' ⟶ A' ⨿ B') q (coprod.map p q) (coprod.inr : B ⟶ A ⨿ B) := by
  have hw : (coprod.inr : B' ⟶ A' ⨿ B') ≫ coprod.map p q
      = q ≫ (coprod.inr : B ⟶ A ⨿ B) := by simp
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s)
      (range_fst_subset_range_inr_consolidated147 p q s)) ?_ ?_ ?_)
  · intro s
    simp [IsOpenImmersion.lift_fac]
  · intro s
    have hl : IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s)
        (range_fst_subset_range_inr_consolidated147 p q s) ≫ (coprod.inr : B' ⟶ A' ⨿ B')
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : (IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s)
          (range_fst_subset_range_inr_consolidated147 p q s) ≫ q) ≫ (coprod.inr : B ⟶ A ⨿ B)
        = PullbackCone.snd s ≫ (coprod.inr : B ⟶ A ⨿ B) := by
      rw [Category.assoc, ← hw, ← Category.assoc, hl]
      exact s.condition
    exact (cancel_mono _).mp h2
  · intro s m hm _
    have hl : IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s)
        (range_fst_subset_range_inr_consolidated147 p q s) ≫ (coprod.inr : B' ⟶ A' ⨿ B')
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : m ≫ (coprod.inr : B' ⟶ A' ⨿ B')
        = IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s)
            (range_fst_subset_range_inr_consolidated147 p q s) ≫ (coprod.inr : B' ⟶ A' ⨿ B') := by
      rw [hm, hl]
    exact (cancel_mono _).mp h2


end

theorem IsBlowupAlongIdealSheaf.coprod {X₁ X₂ X₁' X₂' : Scheme.{u}} {π₁ : X₁' ⟶ X₁} {π₂ : X₂' ⟶ X₂}
    {I : (X₁ ⨿ X₂).IdealSheafData}
    (h₁ : IsBlowupAlongIdealSheaf π₁ (I.comap (coprod.inl : X₁ ⟶ X₁ ⨿ X₂)))
    (h₂ : IsBlowupAlongIdealSheaf π₂ (I.comap (coprod.inr : X₂ ⟶ X₁ ⨿ X₂))) :
    IsBlowupAlongIdealSheaf (coprod.map π₁ π₂) I := by
  have hb₁ : IsBlowupAlongIdealSheaf (pullback.snd (coprod.map π₁ π₂) (coprod.inl : X₁ ⟶ X₁ ⨿ X₂))
      (I.comap (coprod.inl : X₁ ⟶ X₁ ⨿ X₂)) := by
    have hpb := isPullback_coprod_inl_map_consolidated147 π₁ π₂
    have hfac : hpb.isoPullback.symm.hom ≫ π₁
        = pullback.snd (coprod.map π₁ π₂) (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) := by
      rw [Iso.symm_hom, Iso.inv_comp_eq]
      exact hpb.isoPullback_hom_snd.symm
    have hbl := h₁.iso_hom_comp hpb.isoPullback.symm
    rwa [hfac] at hbl
  have hb₂ : IsBlowupAlongIdealSheaf (pullback.snd (coprod.map π₁ π₂) (coprod.inr : X₂ ⟶ X₁ ⨿ X₂))
      (I.comap (coprod.inr : X₂ ⟶ X₁ ⨿ X₂)) := by
    have hpb := isPullback_coprod_inr_map_consolidated147 π₁ π₂
    have hfac : hpb.isoPullback.symm.hom ≫ π₂
        = pullback.snd (coprod.map π₁ π₂) (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) := by
      rw [Iso.symm_hom, Iso.inv_comp_eq]
      exact hpb.isoPullback_hom_snd.symm
    have hbl := h₂.iso_hom_comp hpb.isoPullback.symm
    rwa [hfac] at hbl
  have hoi : ∀ b : Bool, IsOpenImmersion
      (Bool.rec (motive := fun b : Bool => (cond b X₁ X₂) ⟶ X₁ ⨿ X₂)
        (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) b) := by
    intro b
    cases b
    · exact (inferInstance : IsOpenImmersion (coprod.inr : X₂ ⟶ X₁ ⨿ X₂))
    · exact (inferInstance : IsOpenImmersion (coprod.inl : X₁ ⟶ X₁ ⨿ X₂))
  refine IsBlowupAlongIdealSheaf.of_comap_of_isOpenImmersion_cover (coprod.map π₁ π₂) I
    (fun b : Bool => cond b X₁ X₂)
    (Bool.rec (motive := fun b : Bool => (cond b X₁ X₂) ⟶ X₁ ⨿ X₂)
      (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) (coprod.inl : X₁ ⟶ X₁ ⨿ X₂)) ?_ ?_
  · intro x
    by_cases hx : x ∈ Set.range ⇑(coprod.inl : X₁ ⟶ X₁ ⨿ X₂).base
    · exact ⟨true, hx⟩
    · refine ⟨false, ?_⟩
      have hx' : x ∈ Set.range ⇑(coprod.inr : X₂ ⟶ X₁ ⨿ X₂).base := by
        rw [range_coprod_inr_eq_compl X₁ X₂]
        exact hx
      exact hx'
  · intro b
    cases b
    · exact hb₂
    · exact hb₁

private theorem range_ι_disjoint_consolidated147 {X : Scheme.{u}} {U V : X.Opens} (h : IsCompl U V)
    (x : ↥X) (hU : x ∈ Set.range ⇑U.ι.base) (hV : x ∈ Set.range ⇑V.ι.base) : False := by
  rw [Scheme.Opens.range_ι] at hU
  rw [Scheme.Opens.range_ι] at hV
  have h1 : U ⊓ V = ⊥ := h.inf_eq_bot
  have h2 : x ∈ ((U ⊓ V : X.Opens) : Set ↥X) := by
    simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff]
    exact ⟨hU, hV⟩
  rw [h1] at h2
  simp at h2

private theorem range_fst_subset_range_inl_of_isCompl_consolidated147 {X A F : Scheme.{u}} (f : A ⟶ X)
    (g : F ⟶ X) {U V : X.Opens} (h : IsCompl U V)
    (hg : Set.range ⇑g.base ⊆ Set.range ⇑V.ι.base)
    (s : PullbackCone (coprod.desc f g) U.ι) :
    Set.range ⇑(PullbackCone.fst s).base ⊆ Set.range ⇑(coprod.inl : A ⟶ A ⨿ F).base := by
  rintro _ ⟨t, rfl⟩
  by_contra hmem
  have hy : (PullbackCone.fst s).base t ∈ Set.range ⇑(coprod.inr : F ⟶ A ⨿ F).base := by
    rw [range_coprod_inr_eq_compl A F, Set.mem_compl_iff]
    exact hmem
  obtain ⟨b, hb⟩ := hy
  have e1 : (coprod.desc f g).base ((PullbackCone.fst s).base t)
      = U.ι.base ((PullbackCone.snd s).base t) := by
    have hc := congrArg (fun m : s.pt ⟶ X => m.base t) s.condition
    simpa using hc
  have e2 : (coprod.desc f g).base ((coprod.inr : F ⟶ A ⨿ F).base b) = g.base b := by
    rw [← base_comp_apply_consolidated147, coprod.inr_desc]
  have hfin : U.ι.base ((PullbackCone.snd s).base t) = g.base b := by
    rw [← e1, ← hb]
    exact e2
  have hmemV : U.ι.base ((PullbackCone.snd s).base t) ∈ Set.range ⇑V.ι.base := by
    rw [hfin]
    exact hg (Set.mem_range_self b)
  exact range_ι_disjoint_consolidated147 h (U.ι.base ((PullbackCone.snd s).base t))
    (Set.mem_range_self _) hmemV

section
variable {X A F : Scheme.{u}} (f : A ⟶ X) (g : F ⟶ X) {U V : X.Opens} (h : IsCompl U V) (hf : Set.range ⇑f.base ⊆ Set.range ⇑U.ι.base) (hg : Set.range ⇑g.base ⊆ Set.range ⇑V.ι.base)
include h hg

private theorem isPullback_inl_coprod_desc_consolidated147 :
    IsPullback (coprod.inl : A ⟶ A ⨿ F) (IsOpenImmersion.lift U.ι f hf)
      (coprod.desc f g) U.ι := by
  have hw : (coprod.inl : A ⟶ A ⨿ F) ≫ coprod.desc f g
      = IsOpenImmersion.lift U.ι f hf ≫ U.ι := by
    rw [coprod.inl_desc, IsOpenImmersion.lift_fac]
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s)
      (range_fst_subset_range_inl_of_isCompl_consolidated147 f g h hg s)) ?_ ?_ ?_)
  · intro s
    simp [IsOpenImmersion.lift_fac]
  · intro s
    have hl : IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s)
        (range_fst_subset_range_inl_of_isCompl_consolidated147 f g h hg s) ≫ (coprod.inl : A ⟶ A ⨿ F)
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : (IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s)
          (range_fst_subset_range_inl_of_isCompl_consolidated147 f g h hg s) ≫
            IsOpenImmersion.lift U.ι f hf) ≫ U.ι
        = PullbackCone.snd s ≫ U.ι := by
      rw [Category.assoc, ← hw, ← Category.assoc, hl]
      exact s.condition
    exact (cancel_mono _).mp h2
  · intro s m hm _
    have hl : IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s)
        (range_fst_subset_range_inl_of_isCompl_consolidated147 f g h hg s) ≫ (coprod.inl : A ⟶ A ⨿ F)
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : m ≫ (coprod.inl : A ⟶ A ⨿ F)
        = IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s)
            (range_fst_subset_range_inl_of_isCompl_consolidated147 f g h hg s) ≫ (coprod.inl : A ⟶ A ⨿ F) := by
      rw [hm, hl]
    exact (cancel_mono _).mp h2

theorem exists_iso_pullback_coprod_desc_left :
    ∃ e : pullback (coprod.desc f g) U.ι ≅ A,
      e.hom ≫ IsOpenImmersion.lift U.ι f hf
          = pullback.snd (coprod.desc f g) U.ι ∧
        e.inv ≫ pullback.fst (coprod.desc f g) U.ι = (coprod.inl : A ⟶ A ⨿ F) := by
  have hpb := isPullback_inl_coprod_desc_consolidated147 f g h hf hg
  refine ⟨hpb.isoPullback.symm, ?_, ?_⟩
  · rw [Iso.symm_hom, Iso.inv_comp_eq]
    exact hpb.isoPullback_hom_snd.symm
  · rw [Iso.symm_inv]
    exact hpb.isoPullback_hom_fst


end

section
variable {X : Scheme.{u}}

private theorem range_opens_ι_consolidated147 (U : X.Opens) :
    Set.range ⇑U.ι.base = (U : Set ↥X) := by
  simp

private theorem notMem_of_isCompl_consolidated147 {U V : X.Opens} (h : IsCompl U V)
    (x : ↥X) (hU : x ∈ (U : Set ↥X)) (hV : x ∈ (V : Set ↥X)) : False := by
  have h1 : U ⊓ V = ⊥ := h.inf_eq_bot
  have h2 : ((U ⊓ V : X.Opens) : Set ↥X) = ((⊥ : X.Opens) : Set ↥X) := by rw [h1]
  have hd : (U : Set ↥X) ∩ (V : Set ↥X) = (∅ : Set ↥X) := by simpa using h2
  have hx : x ∈ (∅ : Set ↥X) := by
    rw [← hd]
    exact ⟨hU, hV⟩
  simp at hx


end

section
variable {X A F : Scheme.{u}} (f : A ⟶ X) (g : F ⟶ X) {U V : X.Opens} (h : IsCompl U V) (hf : Set.range ⇑f.base ⊆ Set.range ⇑U.ι.base)
include h hf

private theorem range_fst_subset_range_inr_of_isCompl_consolidated147 (s : PullbackCone (coprod.desc f g) V.ι) :
    Set.range ⇑(PullbackCone.fst s).base ⊆ Set.range ⇑(coprod.inr : F ⟶ A ⨿ F).base := by
  rintro _ ⟨t, rfl⟩
  rw [range_coprod_inr_eq_compl A F, Set.mem_compl_iff]
  rintro ⟨a, ha⟩
  have hc := congrArg (fun m : s.pt ⟶ X => m.base t) s.condition
  have e1 : (coprod.desc f g).base ((PullbackCone.fst s).base t)
      = V.ι.base ((PullbackCone.snd s).base t) := by
    rw [← base_comp_apply_consolidated147, ← base_comp_apply_consolidated147]
    exact hc
  have hd : (coprod.inl : A ⟶ A ⨿ F) ≫ coprod.desc f g = f := coprod.inl_desc f g
  have e2 : (coprod.desc f g).base ((coprod.inl : A ⟶ A ⨿ F).base a) = f.base a := by
    rw [← base_comp_apply_consolidated147, hd]
  have hfa : f.base a = V.ι.base ((PullbackCone.snd s).base t) := by
    rw [← e2, ha, e1]
  refine notMem_of_isCompl_consolidated147 h (f.base a) ?_ ?_
  · rw [← range_opens_ι_consolidated147 U]
    exact hf (Set.mem_range_self a)
  · rw [hfa, ← range_opens_ι_consolidated147 V]
    exact Set.mem_range_self _

private theorem isPullback_inr_coprod_desc_consolidated147 (hg : Set.range ⇑g.base ⊆ Set.range ⇑V.ι.base) :
    IsPullback (coprod.inr : F ⟶ A ⨿ F) (IsOpenImmersion.lift V.ι g hg)
      (coprod.desc f g) V.ι := by
  have hinr : (coprod.inr : F ⟶ A ⨿ F) ≫ coprod.desc f g = g := coprod.inr_desc f g
  have hliftfac : IsOpenImmersion.lift V.ι g hg ≫ V.ι = g :=
    IsOpenImmersion.lift_fac V.ι g hg
  have hw : (coprod.inr : F ⟶ A ⨿ F) ≫ coprod.desc f g
      = IsOpenImmersion.lift V.ι g hg ≫ V.ι := hinr.trans hliftfac.symm
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s)
      (range_fst_subset_range_inr_of_isCompl_consolidated147 f g h hf s)) ?_ ?_ ?_)
  · intro s
    simp [IsOpenImmersion.lift_fac]
  · intro s
    have hl : IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s)
        (range_fst_subset_range_inr_of_isCompl_consolidated147 f g h hf s) ≫ (coprod.inr : F ⟶ A ⨿ F)
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : (IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s)
          (range_fst_subset_range_inr_of_isCompl_consolidated147 f g h hf s) ≫
            IsOpenImmersion.lift V.ι g hg) ≫ V.ι
        = PullbackCone.snd s ≫ V.ι := by
      rw [Category.assoc, ← hw, ← Category.assoc, hl]
      exact s.condition
    exact (cancel_mono _).mp h2
  · intro s m hm _
    have hl : IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s)
        (range_fst_subset_range_inr_of_isCompl_consolidated147 f g h hf s) ≫ (coprod.inr : F ⟶ A ⨿ F)
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : m ≫ (coprod.inr : F ⟶ A ⨿ F)
        = IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s)
            (range_fst_subset_range_inr_of_isCompl_consolidated147 f g h hf s) ≫ (coprod.inr : F ⟶ A ⨿ F) := by
      rw [hm, hl]
    exact (cancel_mono _).mp h2

theorem exists_iso_pullback_coprod_desc_right (hg : Set.range ⇑g.base ⊆ Set.range ⇑V.ι.base) :
    ∃ e : pullback (coprod.desc f g) V.ι ≅ F,
      e.hom ≫ IsOpenImmersion.lift V.ι g hg
          = pullback.snd (coprod.desc f g) V.ι ∧
        e.inv ≫ pullback.fst (coprod.desc f g) V.ι = (coprod.inr : F ⟶ A ⨿ F) := by
  have hpb := isPullback_inr_coprod_desc_consolidated147 f g h hf hg
  refine ⟨hpb.isoPullback.symm, ?_, ?_⟩
  · rw [Iso.symm_hom, Iso.inv_comp_eq]
    exact hpb.isoPullback_hom_snd.symm
  · rw [Iso.symm_inv]
    exact hpb.isoPullback_hom_fst


end

private theorem isZariskiLocalAtSource_smooth_consolidated147 : IsZariskiLocalAtSource (@Smooth.{u}) :=
  @HasRingHomProperty.instIsZariskiLocalAtSource (@Smooth.{u}) RingHom.Smooth inferInstance

theorem smooth_coprod_desc {X A B : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X)
    (hf : Smooth f) (hg : Smooth g) : Smooth (coprod.desc f g) := by
  refine isZariskiLocalAtSource_smooth_consolidated147.of_openCover (coprodOpenCover.{u, u} A B) ?_
  intro i
  cases i with
  | inl _ =>
      show Smooth ((coprod.inl : A ⟶ A ⨿ B) ≫ coprod.desc f g)
      rw [coprod.inl_desc]
      exact hf
  | inr _ =>
      show Smooth ((coprod.inr : B ⟶ A ⨿ B) ≫ coprod.desc f g)
      rw [coprod.inr_desc]
      exact hg

private theorem subsingleton_presheaf_of_isEmpty_consolidated147 {X : Scheme.{u}} [IsEmpty ↥X] {V : X.Opens}
    (hV : IsAffineOpen V) : Subsingleton ↥(X.presheaf.obj (Opposite.op V)) := by
  by_contra hcon
  have : Nontrivial ↥(X.presheaf.obj (Opposite.op V)) :=
    not_subsingleton_iff_nontrivial.mp hcon
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum ↥(X.presheaf.obj (Opposite.op V))) := inferInstance
  exact IsEmpty.false (hV.fromSpec.base p)

private theorem algebra_smooth_of_subsingleton_consolidated147 (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Subsingleton S] : Algebra.Smooth R S := by
  have hloc : IsLocalization.Away (0 : R) S :=
    { map_units := fun y => ⟨1, Subsingleton.elim _ _⟩
      surj := fun z => ⟨⟨0, 1⟩, Subsingleton.elim _ _⟩
      exists_of_eq := fun _ => ⟨⟨0, Submonoid.mem_powers 0⟩, by simp⟩ }
  exact ⟨Algebra.FormallySmooth.of_isLocalization (Submonoid.powers (0 : R)),
    IsLocalization.Away.finitePresentation (0 : R)⟩

private theorem ringHom_smooth_of_subsingleton_consolidated147 {R S : Type u} [CommRing R] [CommRing S]
    (hS : Subsingleton S) (φ : R →+* S) : RingHom.Smooth φ :=
  @algebra_smooth_of_subsingleton_consolidated147 R S _ _ φ.toAlgebra hS

theorem smooth_of_isEmpty {X Y : Scheme.{u}} (f : X ⟶ Y) [IsEmpty ↥X] : Smooth f := by
  constructor
  intro U _ V hV e
  exact ringHom_smooth_of_subsingleton_consolidated147 (subsingleton_presheaf_of_isEmpty_consolidated147 hV)
    (CommRingCat.Hom.hom (Scheme.Hom.appLE f U V e))

end FunctorialResolution.Blowup
end

-- Source: Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupUniversal
section
open CategoryTheory AlgebraicGeometry

section
namespace FunctorialResolution.Blowup


private theorem exists_sum_mul_eq_one_of_map_eq_span_consolidated167 {R A : Type u} [CommRing R] [CommRing A]
    (I : Ideal R) (φ : R →+* A) (s : A) (hmap : Ideal.map φ I = Ideal.span {s})
    (hs : s ∈ nonZeroDivisors A) :
    ∃ (n : ℕ) (a : Fin n → ↥I) (c d : Fin n → A),
      (∀ i, φ (a i : R) = d i * s) ∧ ∑ i, c i * d i = 1 := by
  have hsmem : s ∈ Ideal.map φ I := by
    rw [hmap]; exact Ideal.subset_span rfl
  rw [← Ideal.span_eq I, Ideal.map_span] at hsmem
  obtain ⟨n, c, gg, hsum⟩ := Submodule.mem_span_set'.mp hsmem
  choose a ha hφa using fun i => (gg i).2
  have hdex : ∀ i, ∃ e : A, φ (a i) = e * s := by
    intro i
    have hmem : φ (a i) ∈ Ideal.span {s} := by
      rw [← hmap]
      exact Ideal.mem_map_of_mem _ (ha i)
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hmem
    exact ⟨e, he.symm⟩
  choose d hdd using hdex
  refine ⟨n, fun i => ⟨a i, ha i⟩, c, d, fun i => hdd i, ?_⟩
  have hss : (∑ i, c i * d i) * s = s := by
    rw [Finset.sum_mul]
    conv_rhs => rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, ← hφa i, hdd i, mul_assoc]
  have h1 : ((∑ i, c i * d i) - 1) * s = 0 := by
    rw [sub_mul, hss, one_mul, sub_self]
  have h2 := mem_nonZeroDivisors_iff_right.mp hs _ h1
  linear_combination h2

private theorem exists_mem_basicOpen_of_sum_mul_eq_one_consolidated167 {X : Scheme.{u}} {V : X.Opens} {n : ℕ}
    (c d : Fin n → ↥Γ(X, V)) (hsum : ∑ i, c i * d i = 1) (w : ↥X) (hw : w ∈ V) :
    ∃ i, w ∈ X.basicOpen (d i) := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ i, (X.presheaf.germ V w hw).hom (d i)
      ∈ IsLocalRing.maximalIdeal ↥(X.presheaf.stalk w) := by
    intro i
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hcon i ((X.mem_basicOpen (d i) w hw).mpr hu)
  have h1 : (1 : ↥(X.presheaf.stalk w)) ∈ IsLocalRing.maximalIdeal ↥(X.presheaf.stalk w) := by
    have hone : (X.presheaf.germ V w hw).hom (1 : ↥Γ(X, V)) = 1 := map_one _
    rw [← hone, ← hsum, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (hmem i)
  exact (IsLocalRing.maximalIdeal.isMaximal ↥(X.presheaf.stalk w)).ne_top
    ((Ideal.eq_top_iff_one _).mpr h1)

private theorem appLE_top_top_eq_appTop_consolidated167 {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) : f.appLE ⊤ ⊤ h = f.appTop := by
  have h2 : X.presheaf.map (homOfLE h).op = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  simp only [Scheme.Hom.appLE, h2]
  rfl

private theorem appLE_comp_consolidated167 {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    (V : Y.Opens) (V' : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : V' ≤ f ⁻¹ᵁ V)
    (e : V' ≤ (f ≫ g) ⁻¹ᵁ U) :
    (f ≫ g).appLE U V' e = g.appLE U V e₁ ≫ f.appLE V V' e₂ := by
  rw [Scheme.Hom.appLE_comp_appLE]

private theorem isIso_ι_appLE_consolidated167 {W : Scheme.{u}} (U : W.Opens)
    (hle : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U) : IsIso (U.ι.appLE U ⊤ hle) := by
  have h1 : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by simp
  have h2 : U.ι.appLE U ⊤ hle
      = W.presheaf.map (eqToHom h1).op ≫ (U.ι.appIso ⊤).hom := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  rw [h2, eqToHom_op, eqToHom_map]
  infer_instance

section
variable {R : Type u} [CommRing R] {W : Scheme.{u}} (U : W.Opens) (g : W ⟶ Spec (CommRingCat.of R))

private theorem appTop_ι_comp_eq_appLE_comp_consolidated167 (hle : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U)
    (hle' : U ≤ g ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)) :
    (U.ι ≫ g).appTop = g.appLE ⊤ U hle' ≫ U.ι.appLE U ⊤ hle := by
  rw [← appLE_top_top_eq_appTop_consolidated167 (U.ι ≫ g) (by simp)]
  exact appLE_comp_consolidated167 U.ι g ⊤ U ⊤ hle' hle (by simp)

private theorem exists_sections_iso_globalSectionsRingHom_consolidated167 :
    ∃ e : Γ(W, U) ≅ Γ(U.toScheme, ⊤),
      ∀ r : R, globalSectionsRingHom (U.ι ≫ g) r
        = (CommRingCat.Hom.hom e.hom) (sectionsRingHom g U r) := by
  have hle : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := by simp
  have hle' : U ≤ g ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) := by simp
  have := isIso_ι_appLE_consolidated167 U hle
  refine ⟨asIso (U.ι.appLE U ⊤ hle), fun r => ?_⟩
  have hcomp := appTop_ι_comp_eq_appLE_comp_consolidated167 U g hle hle'
  simp only [globalSectionsRingHom_eq, hcomp, asIso_hom, CommRingCat.hom_comp, RingHom.comp_apply,
    sectionsRingHom_apply]


end

theorem exists_local_lift_toSpec_of_isLocallyGeneratedByNonZeroDivisor {R : Type u} [CommRing R] (I : Ideal R)
    {W : Scheme.{u}} (g : W ⟶ Spec (CommRingCat.of R))
    (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap g)) (w : ↥W) :
    ∃ (U : W.Opens) (_ : w ∈ U) (h : U.toScheme ⟶ affineBlowup I),
      h ≫ AffineBlowup.toSpec I = U.ι ≫ g := by
  obtain ⟨V, s, hwV, hs, hspan⟩ := hcart w
  have hmap : Ideal.map (sectionsRingHom g (V : W.Opens)) I = Ideal.span {s} :=
    (comap_specIdealSheaf_ideal I g V).symm.trans hspan
  obtain ⟨n, a, c, d, hd, hsum⟩ :=
    exists_sum_mul_eq_one_of_map_eq_span_consolidated167 I (sectionsRingHom g (V : W.Opens)) s hmap hs
  obtain ⟨i, hi⟩ := exists_mem_basicOpen_of_sum_mul_eq_one_consolidated167 c d hsum w hwV
  have hLoc : IsLocalization.Away (d i) ↥Γ(W, W.basicOpen (d i)) :=
    V.2.isLocalization_basicOpen (d i)
  have hUV : W.basicOpen (d i) ≤ (V : W.Opens) := W.basicOpen_le (d i)
  have : IsAffine (W.basicOpen (d i)).toScheme := V.2.basicOpen (d i)
  have hunit : IsUnit ((W.presheaf.map (homOfLE hUV).op).hom (d i)) :=
    IsLocalization.map_units (M := Submonoid.powers (d i)) _ ⟨d i, Submonoid.mem_powers _⟩
  have hrs : (W.presheaf.map (homOfLE hUV).op).hom s
      ∈ nonZeroDivisors ↥Γ(W, W.basicOpen (d i)) :=
    IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers (d i)) _ hs
  have hres : ∀ r : R, sectionsRingHom g (W.basicOpen (d i)) r
      = (W.presheaf.map (homOfLE hUV).op).hom (sectionsRingHom g (V : W.Opens) r) :=
    fun r => sectionsRingHom_restrict g hUV r
  have hcomp : sectionsRingHom g (W.basicOpen (d i))
      = (W.presheaf.map (homOfLE hUV).op).hom.comp (sectionsRingHom g (V : W.Opens)) :=
    RingHom.ext hres
  have hmapSpan : Ideal.map (sectionsRingHom g (W.basicOpen (d i))) I
      = Ideal.span {sectionsRingHom g (W.basicOpen (d i)) (a i : R)} := by
    have h1 : Ideal.map (sectionsRingHom g (W.basicOpen (d i))) I
        = Ideal.span {(W.presheaf.map (homOfLE hUV).op).hom (d i)
            * (W.presheaf.map (homOfLE hUV).op).hom s} := by
      rw [hcomp, ← Ideal.map_map, hmap, Ideal.map_span, Set.image_singleton]
      exact (Ideal.span_singleton_mul_left_unit hunit _).symm
    rw [h1, hres (a i : R), hd i, map_mul]
  have hnonZeroDivU : sectionsRingHom g (W.basicOpen (d i)) (a i : R)
      ∈ nonZeroDivisors ↥Γ(W, W.basicOpen (d i)) := by
    rw [hres, hd i, map_mul]
    exact mul_mem hunit.mem_nonZeroDivisors hrs
  obtain ⟨e, he⟩ := exists_sections_iso_globalSectionsRingHom_consolidated167 (W.basicOpen (d i)) g
  have hgen' : Ideal.map (globalSectionsRingHom ((W.basicOpen (d i)).ι ≫ g)) I
      = Ideal.span {globalSectionsRingHom ((W.basicOpen (d i)).ι ≫ g) (a i : R)} := by
    have e1 : Ideal.map (globalSectionsRingHom ((W.basicOpen (d i)).ι ≫ g)) I
        = Ideal.map (CommRingCat.Hom.hom e.hom)
            (Ideal.map (sectionsRingHom g (W.basicOpen (d i))) I) := by
      rw [Ideal.map_map]
      exact congrArg (fun ϕ => Ideal.map ϕ I) (RingHom.ext he)
    rw [e1, hmapSpan, Ideal.map_span, Set.image_singleton, he]
  have hnonZeroDiv' : globalSectionsRingHom ((W.basicOpen (d i)).ι ≫ g) (a i : R)
      ∈ nonZeroDivisors ↥Γ((W.basicOpen (d i)).toScheme, ⊤) := by
    rw [he]
    exact map_mem_nonZeroDivisors_of_iso e hnonZeroDivU
  obtain ⟨h, hh, -⟩ :=
    exists_lift_affineBlowup I ((W.basicOpen (d i)).ι ≫ g) (a i) hgen' hnonZeroDiv'
  exact ⟨W.basicOpen (d i), hi, h, hh⟩

private def openCoverOfForallMem_consolidated167 {W : Scheme.{u}} (U : ↥W → W.Opens) (hU : ∀ w, w ∈ U w) :
    W.OpenCover :=
  Scheme.Cover.mkOfCovers (↥W) (fun w => (U w).toScheme) (fun w => (U w).ι)
    (fun x => ⟨x, ⟨x, hU x⟩, rfl⟩)

section
variable {R : Type u} [CommRing R] (I : Ideal R)

theorem exists_lift_toSpec_of_isLocallyGeneratedByNonZeroDivisor {W : Scheme.{u}} (g : W ⟶ Spec (CommRingCat.of R))
    (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap g)) :
    ∃ h : W ⟶ affineBlowup I, h ≫ AffineBlowup.toSpec I = g := by
  choose U hU h hh using fun w => exists_local_lift_toSpec_of_isLocallyGeneratedByNonZeroDivisor I g hcart w
  have hcompat : ∀ x y : ↥W,
      Limits.pullback.fst ((U x).ι) ((U y).ι) ≫ h x
        = Limits.pullback.snd ((U x).ι) ((U y).ι) ≫ h y := by
    intro x y
    refine affineBlowup_hom_ext _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, hh x, hh y, ← Category.assoc, ← Category.assoc,
        Limits.pullback.condition]
    · have h1 : (Limits.pullback.fst ((U x).ι) ((U y).ι) ≫ h x) ≫ AffineBlowup.toSpec I
          = (Limits.pullback.fst ((U x).ι) ((U y).ι) ≫ (U x).ι) ≫ g := by
        rw [Category.assoc, hh x, ← Category.assoc]
      have h2 : (specIdealSheaf I).comap
            ((Limits.pullback.fst ((U x).ι) ((U y).ι) ≫ (U x).ι) ≫ g)
          = ((specIdealSheaf I).comap g).comap
              (Limits.pullback.fst ((U x).ι) ((U y).ι) ≫ (U x).ι) := by
        simp [Scheme.IdealSheafData.comap_comp]
      rw [h1, h2]
      exact IsLocallyGeneratedByNonZeroDivisor.comap_of_isOpenImmersion hcart _
  refine ⟨(openCoverOfForallMem_consolidated167 U hU).glueMorphisms h (fun x y => hcompat x y), ?_⟩
  refine (openCoverOfForallMem_consolidated167 U hU).hom_ext _ _ fun x => ?_
  rw [← Category.assoc, (openCoverOfForallMem_consolidated167 U hU).ι_glueMorphisms h (fun x y => hcompat x y) x]
  exact hh x

theorem isBlowupAlongIdealSheaf_affineBlowup_toSpec :
    IsBlowupAlongIdealSheaf (AffineBlowup.toSpec I) (specIdealSheaf I) := by
  refine And.intro (isLocallyGeneratedByNonZeroDivisor_comap_toSpec I) ?_
  intro W g hg
  obtain ⟨h, hh⟩ := exists_lift_toSpec_of_isLocallyGeneratedByNonZeroDivisor I g hg
  refine ⟨h, hh, fun h' hh' => ?_⟩
  refine affineBlowup_hom_ext h' h (by rw [hh', hh]) ?_
  rw [hh']
  exact hg


end

end FunctorialResolution.Blowup
end
end

-- Source: Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.Blowup

theorem comap_ι_support_compl_eq_top {X : Scheme.{u}} (Z : X.IdealSheafData) :
    Z.comap (Scheme.Opens.ι Z.support.compl) = ⊤ := by
  refine comap_eq_top_of_notMem_support _ Z fun x => ?_
  show x.1 ∉ Z.support
  exact x.2

theorem blowupIsIsoOffCenter : BlowupIsIsoOffCenter.{u} := by
  intro X X' π Z h
  have h1 := h.restrict Z.support.compl
  rw [comap_ι_support_compl_eq_top Z] at h1
  exact h1.isIso_of_top

end FunctorialResolution.Blowup
end

-- Source: Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace FunctorialResolution.Blowup

private theorem ideal_map_inv_map_hom_consolidated190 {A B : CommRingCat.{u}} (e : A ≅ B) (K : Ideal A) :
    Ideal.map e.inv.hom (Ideal.map e.hom.hom K) = K := by
  rw [Ideal.map_map, ← CommRingCat.hom_comp, e.hom_inv_id, CommRingCat.hom_id, Ideal.map_id]

theorem IsBlowupAlongIdealSheaf.exists_lift {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) {W : Scheme.{u}} (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) :
    ∃ a : W ⟶ X', a ≫ π = g :=
  (h.2 W g hg).exists

section
noncomputable def IsBlowupAlongIdealSheaf.lift {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) {W : Scheme.{u}} (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) : W ⟶ X' :=
  (h.exists_lift g hg).choose

theorem IsBlowupAlongIdealSheaf.lift_comp {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) {W : Scheme.{u}} (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) :
    h.lift g hg ≫ π = g :=
  (h.exists_lift g hg).choose_spec

end

theorem IsBlowupAlongIdealSheaf.hom_ext {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) {W : Scheme.{u}} {g : W ⟶ X}
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) {a b : W ⟶ X'}
    (ha : a ≫ π = g) (hb : b ≫ π = g) : a = b :=
  h.hom_ext_of_comp_eq hg ha hb

theorem IsBlowupAlongIdealSheaf.comp_iso_hom {X X' Y : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) (e : X ≅ Y) :
    IsBlowupAlongIdealSheaf (π ≫ e.hom) (I.comap e.inv) := by
  constructor
  · rw [← Scheme.IdealSheafData.comap_comp, Category.assoc, e.hom_inv_id, Category.comp_id]
    exact h.1
  · intro W g hg
    rw [← Scheme.IdealSheafData.comap_comp] at hg
    obtain ⟨a, ha, hu⟩ := h.2 W (g ≫ e.inv) hg
    refine ⟨a, ?_, ?_⟩
    · show a ≫ π ≫ e.hom = g
      rw [← Category.assoc, ha, Category.assoc, e.inv_hom_id, Category.comp_id]
    · intro b hb
      have hb' : b ≫ π ≫ e.hom = g := hb
      refine hu b ?_
      show b ≫ π = g ≫ e.inv
      rw [← hb']
      simp

theorem IsBlowupAlongIdealSheaf.pullback_snd_of_isOpenImmersion {X X' U : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) (f : U ⟶ X) [IsOpenImmersion f] :
    IsBlowupAlongIdealSheaf (pullback.snd π f) (I.comap f) := by
  constructor
  · have h1 : (I.comap f).comap (pullback.snd π f)
        = (I.comap π).comap (pullback.fst π f) := by
      rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        pullback.condition]
    rw [h1]
    exact h.1.comap_of_isOpenImmersion (pullback.fst π f)
  · intro W g hg
    rw [← Scheme.IdealSheafData.comap_comp] at hg
    obtain ⟨a, ha, hu⟩ := h.2 W (g ≫ f) hg
    refine ⟨pullback.lift a g ha, pullback.lift_snd _ _ _, ?_⟩
    intro b hb
    have hb' : b ≫ pullback.snd π f = g := hb
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst]
      refine hu _ ?_
      show (b ≫ pullback.fst π f) ≫ π = g ≫ f
      rw [Category.assoc, pullback.condition, ← Category.assoc, hb']
    · rw [pullback.lift_snd, hb']

private theorem exists_isBlowupAlongIdealSheaf_spec_of_commRing_consolidated190 (R : Type u) [CommRing R]
    (I : (Spec (CommRingCat.of R)).IdealSheafData) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ Spec (CommRingCat.of R)), IsBlowupAlongIdealSheaf π I := by
  obtain ⟨J, hJ⟩ : ∃ J : Ideal R, specIdealSheaf J = I := by
    refine ⟨Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (I.ideal ⟨⊤, isAffineOpen_top _⟩), ?_⟩
    refine Scheme.IdealSheafData.ext_of_isAffine ?_
    rw [specIdealSheaf_ideal_top, ideal_map_inv_map_hom_consolidated190]
  refine ⟨affineBlowup J, AffineBlowup.toSpec J, ?_⟩
  rw [← hJ]
  exact isBlowupAlongIdealSheaf_affineBlowup_toSpec J

theorem exists_isBlowupAlongIdealSheaf_spec (R : CommRingCat.{u}) (I : (Spec R).IdealSheafData) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ Spec R), IsBlowupAlongIdealSheaf π I :=
  exists_isBlowupAlongIdealSheaf_spec_of_commRing_consolidated190 (R : Type u) I

theorem exists_isBlowupAlongIdealSheaf_of_isAffine (X : Scheme.{u}) [IsAffine X] (I : X.IdealSheafData) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X), IsBlowupAlongIdealSheaf π I := by
  obtain ⟨Y, π, hπ⟩ := exists_isBlowupAlongIdealSheaf_spec Γ(X, ⊤) (I.comap X.isoSpec.inv)
  refine ⟨Y, π ≫ X.isoSpec.inv, ?_⟩
  have h2 := hπ.comp_iso_hom X.isoSpec.symm
  simp only [Iso.symm_hom, Iso.symm_inv] at h2
  rwa [← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id,
    Scheme.IdealSheafData.comap_id] at h2

private theorem comp_base_apply_consolidated190 {A B C : Scheme.{u}} (u : A ⟶ B) (z : B ⟶ C) (p : A) :
    (u ≫ z).base p = z.base (u.base p) := by simp

private theorem ι_base_mem_consolidated190 {X : Scheme.{u}} (U : X.Opens) (v : U.toScheme) :
    U.ι.base v ∈ U := by
  have h : U.ι.base v ∈ Set.range ⇑U.ι.base := Set.mem_range_self v
  rwa [Scheme.Opens.range_ι] at h

private theorem isLocallyGeneratedByNonZeroDivisor_comap_openImmersion_comp_consolidated190 {X P Z : Scheme.{u}} (I : X.IdealSheafData)
    (u : P ⟶ Z) [IsOpenImmersion u] (z : Z ⟶ X) (hz : IsLocallyGeneratedByNonZeroDivisor (I.comap z)) :
    IsLocallyGeneratedByNonZeroDivisor (I.comap (u ≫ z)) := by
  rw [Scheme.IdealSheafData.comap_comp]
  exact hz.comap_of_isOpenImmersion u

private theorem range_id_base_consolidated190 (Z : Scheme.{u}) :
    Set.range ⇑(𝟙 Z : Z ⟶ Z).base = Set.univ := by
  refine Set.eq_univ_of_forall (fun v => ⟨v, ?_⟩)
  simp

private theorem pullback_hom_ext_of_mono_consolidated190 {Z A B : Scheme.{u}} (a : A ⟶ Z) (b : B ⟶ Z)
    [Mono a] [Mono b] {P : Scheme.{u}} {u v : P ⟶ pullback a b}
    (h : u ≫ pullback.fst a b ≫ a = v ≫ pullback.fst a b ≫ a) : u = v := by
  have h1 : u ≫ pullback.fst a b = v ≫ pullback.fst a b := by
    rw [← cancel_mono a, Category.assoc, Category.assoc]
    exact h
  have h2 : u ≫ pullback.snd a b = v ≫ pullback.snd a b := by
    rw [← cancel_mono b, Category.assoc, Category.assoc, ← pullback.condition]
    exact h
  exact pullback.hom_ext h1 h2

private def IsBlowupAlongIdealSheafOver_consolidated190 {X : Scheme.{u}} (I : X.IdealSheafData) (S : X.Opens) {Z : Scheme.{u}}
    (z : Z ⟶ X) : Prop :=
  Set.range ⇑z.base ⊆ (S : Set X) ∧ IsLocallyGeneratedByNonZeroDivisor (I.comap z) ∧
    ∀ {Y : Scheme.{u}} (y : Y ⟶ X), IsLocallyGeneratedByNonZeroDivisor (I.comap y) →
      Set.range ⇑y.base ⊆ (S : Set X) → ∃! a : Y ⟶ Z, a ≫ z = y

private theorem blowupOver_hom_ext_consolidated190 {X Z : Scheme.{u}} {I : X.IdealSheafData} {S : X.Opens}
    {z : Z ⟶ X} (hz : IsBlowupAlongIdealSheafOver_consolidated190 I S z) {Y : Scheme.{u}} (y : Y ⟶ X)
    (hy : IsLocallyGeneratedByNonZeroDivisor (I.comap y)) (hr : Set.range ⇑y.base ⊆ (S : Set X))
    {a b : Y ⟶ Z} (ha : a ≫ z = y) (hb : b ≫ z = y) : a = b := by
  obtain ⟨c, -, hu⟩ := hz.2.2 y hy hr
  rw [hu a ha, hu b hb]

private noncomputable def liftOfIsBlowupAlongIdealSheafOver {X Z : Scheme.{u}} {I : X.IdealSheafData} {S : X.Opens}
    {z : Z ⟶ X} (hz : IsBlowupAlongIdealSheafOver_consolidated190 I S z) {Y : Scheme.{u}} (y : Y ⟶ X)
    (hy : IsLocallyGeneratedByNonZeroDivisor (I.comap y)) (hr : Set.range ⇑y.base ⊆ (S : Set X)) : Y ⟶ Z :=
  (hz.2.2 y hy hr).choose

section
variable {X Z : Scheme.{u}} {I : X.IdealSheafData}

private theorem blowupOverLift_comp_consolidated190 {S : X.Opens}
    {z : Z ⟶ X} (hz : IsBlowupAlongIdealSheafOver_consolidated190 I S z) {Y : Scheme.{u}} (y : Y ⟶ X)
    (hy : IsLocallyGeneratedByNonZeroDivisor (I.comap y)) (hr : Set.range ⇑y.base ⊆ (S : Set X)) :
    liftOfIsBlowupAlongIdealSheafOver hz y hy hr ≫ z = y :=
  (hz.2.2 y hy hr).choose_spec.1

private theorem blowupOver_of_isBlowupAlongIdealSheaf_consolidated190 {W : X.Opens}
    {p : Z ⟶ W.toScheme} (h : IsBlowupAlongIdealSheaf p (I.comap W.ι)) : IsBlowupAlongIdealSheafOver_consolidated190 I W (p ≫ W.ι) := by
  have hrange : Set.range ⇑(W.ι).base = (W : Set X) := W.range_ι
  refine ⟨?_, ?_, ?_⟩
  · rw [← hrange]
    rintro _ ⟨v, rfl⟩
    exact ⟨p.base v, by simp⟩
  · rw [Scheme.IdealSheafData.comap_comp]
    exact h.1
  · intro Y y hy hry
    have hr : Set.range ⇑y.base ⊆ Set.range ⇑W.ι.base := by
      rw [hrange]; exact hry
    have hfac : IsOpenImmersion.lift W.ι y hr ≫ W.ι = y := IsOpenImmersion.lift_fac W.ι y hr
    have hy2 : IsLocallyGeneratedByNonZeroDivisor ((I.comap W.ι).comap (IsOpenImmersion.lift W.ι y hr)) := by
      rw [← Scheme.IdealSheafData.comap_comp, hfac]; exact hy
    obtain ⟨a, ha, hu⟩ := h.2 Y (IsOpenImmersion.lift W.ι y hr) hy2
    refine ⟨a, ?_, ?_⟩
    · show a ≫ p ≫ W.ι = y
      rw [← Category.assoc, ha, hfac]
    · intro b hb
      have hbb : b ≫ (p ≫ W.ι) = y := hb
      refine hu b ?_
      have hbb2 : (b ≫ p) ≫ W.ι = IsOpenImmersion.lift W.ι y hr ≫ W.ι := by
        rw [Category.assoc, hbb, hfac]
      exact (cancel_mono W.ι).mp hbb2

private theorem blowupOver_inf_preimage_consolidated190 {S : X.Opens}
    {z : Z ⟶ X} (hz : IsBlowupAlongIdealSheafOver_consolidated190 I S z) (T : X.Opens) :
    IsBlowupAlongIdealSheafOver_consolidated190 I (S ⊓ T) ((z ⁻¹ᵁ T).ι ≫ z) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩
    rw [comp_base_apply_consolidated190]
    refine TopologicalSpace.Opens.mem_inf.mpr ⟨hz.1 (Set.mem_range_self _), ?_⟩
    exact ι_base_mem_consolidated190 (z ⁻¹ᵁ T) p
  · exact isLocallyGeneratedByNonZeroDivisor_comap_openImmersion_comp_consolidated190 I _ z hz.2.1
  · intro Y y hy hr
    have hrS : Set.range ⇑y.base ⊆ (S : Set X) := fun p hp =>
      (TopologicalSpace.Opens.mem_inf.mp (hr hp)).1
    obtain ⟨a, ha, hu⟩ := hz.2.2 y hy hrS
    have hra : Set.range ⇑a.base ⊆ Set.range ⇑(z ⁻¹ᵁ T).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      show z.base (a.base p) ∈ T
      rw [← comp_base_apply_consolidated190, ha]
      exact (TopologicalSpace.Opens.mem_inf.mp (hr (Set.mem_range_self p))).2
    refine ⟨IsOpenImmersion.lift _ a hra, ?_, ?_⟩
    · show IsOpenImmersion.lift (z ⁻¹ᵁ T).ι a hra ≫ ((z ⁻¹ᵁ T).ι ≫ z) = y
      rw [← Category.assoc, IsOpenImmersion.lift_fac, ha]
    · intro b hb
      have hbb : b ≫ ((z ⁻¹ᵁ T).ι ≫ z) = y := hb
      have hb' : (b ≫ (z ⁻¹ᵁ T).ι) ≫ z = y := by rw [Category.assoc]; exact hbb
      have h1 : b ≫ (z ⁻¹ᵁ T).ι = a := hu _ hb'
      have h2 : IsOpenImmersion.lift (z ⁻¹ᵁ T).ι a hra ≫ (z ⁻¹ᵁ T).ι = a :=
        IsOpenImmersion.lift_fac _ _ _
      exact (cancel_mono (z ⁻¹ᵁ T).ι).mp (by rw [h1, h2])


end

private theorem exists_isBlowupAlongIdealSheaf_affineOpen_consolidated190 {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    ∃ (Z : Scheme.{u}) (p : Z ⟶ (U : X.Opens).toScheme),
      IsBlowupAlongIdealSheaf p (I.comap (U : X.Opens).ι) := by
  have : IsAffine (U : X.Opens).toScheme := U.2
  exact exists_isBlowupAlongIdealSheaf_of_isAffine _ _

private noncomputable def localBlowup {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    Scheme.{u} :=
  (exists_isBlowupAlongIdealSheaf_affineOpen_consolidated190 I U).choose

private noncomputable def localBlowupProjection {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    localBlowup I U ⟶ (U : X.Opens).toScheme :=
  (exists_isBlowupAlongIdealSheaf_affineOpen_consolidated190 I U).choose_spec.choose

private theorem isBlowupAlongIdealSheaf_localBlowupProj_consolidated190 {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    IsBlowupAlongIdealSheaf (localBlowupProjection I U) (I.comap (U : X.Opens).ι) :=
  (exists_isBlowupAlongIdealSheaf_affineOpen_consolidated190 I U).choose_spec.choose_spec

private noncomputable def localBlowupToBase {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    localBlowup I U ⟶ X :=
  localBlowupProjection I U ≫ (U : X.Opens).ι

private theorem blowupOver_localBlowupMap_consolidated190 {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    IsBlowupAlongIdealSheafOver_consolidated190 I (U : X.Opens) (localBlowupToBase I U) :=
  blowupOver_of_isBlowupAlongIdealSheaf_consolidated190 (isBlowupAlongIdealSheaf_localBlowupProj_consolidated190 I U)

private noncomputable def overlap {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j : X.affineOpens) : (localBlowup I i).Opens :=
  (localBlowupToBase I i) ⁻¹ᵁ (j : X.Opens)

private noncomputable def overlapInclusion {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j : X.affineOpens) : (overlap I i j).toScheme ⟶ localBlowup I i :=
  (overlap I i j).ι

section
variable {X : Scheme.{u}} (I : X.IdealSheafData) (i j : X.affineOpens)

private theorem overlapIncl_eq_consolidated190 :
    overlapInclusion I i j = (overlap I i j).ι := rfl

private theorem isOpenImmersion_overlapIncl_consolidated190 : IsOpenImmersion (overlapInclusion I i j) := by
  rw [overlapIncl_eq_consolidated190]
  infer_instance


end

private noncomputable def overlapToBase {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j : X.affineOpens) : (overlap I i j).toScheme ⟶ X :=
  overlapInclusion I i j ≫ localBlowupToBase I i

section
variable {X : Scheme.{u}} (I : X.IdealSheafData) (i j : X.affineOpens)

private theorem overlapMap_eq_consolidated190 :
    overlapToBase I i j = overlapInclusion I i j ≫ localBlowupToBase I i := rfl

private theorem blowupOver_overlapMap_consolidated190 :
    IsBlowupAlongIdealSheafOver_consolidated190 I ((i : X.Opens) ⊓ (j : X.Opens)) (overlapToBase I i j) :=
  blowupOver_inf_preimage_consolidated190 (blowupOver_localBlowupMap_consolidated190 I i) (j : X.Opens)

private theorem overlapMap_base_mem_inf_consolidated190 (p : (overlap I i j).toScheme) :
    (overlapToBase I i j).base p ∈ ((i : X.Opens) ⊓ (j : X.Opens)) :=
  (blowupOver_overlapMap_consolidated190 I i j).1 (Set.mem_range_self p)

private theorem range_overlapMap_subset_inf_swap_consolidated190 :
    Set.range ⇑(overlapToBase I i j).base ⊆ (((j : X.Opens) ⊓ (i : X.Opens)) : Set X) := by
  rintro _ ⟨p, rfl⟩
  exact TopologicalSpace.Opens.mem_inf.mpr
    ⟨(TopologicalSpace.Opens.mem_inf.mp (overlapMap_base_mem_inf_consolidated190 I i j p)).2,
      (TopologicalSpace.Opens.mem_inf.mp (overlapMap_base_mem_inf_consolidated190 I i j p)).1⟩


end

private noncomputable def overlapTransition {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j : X.affineOpens) : (overlap I i j).toScheme ⟶ (overlap I j i).toScheme :=
  liftOfIsBlowupAlongIdealSheafOver (blowupOver_overlapMap_consolidated190 I j i) (overlapToBase I i j)
    (blowupOver_overlapMap_consolidated190 I i j).2.1 (range_overlapMap_subset_inf_swap_consolidated190 I i j)

section
variable {X : Scheme.{u}} (I : X.IdealSheafData)

private theorem overlapTrans_comp_overlapMap_consolidated190 (i j : X.affineOpens) :
    overlapTransition I i j ≫ overlapToBase I j i = overlapToBase I i j :=
  blowupOverLift_comp_consolidated190 _ _ _ _

private theorem isIso_overlapIncl_self_consolidated190 (i : X.affineOpens) : IsIso (overlapInclusion I i i) := by
  have := isOpenImmersion_overlapIncl_consolidated190 I i i
  have e2 : ((overlap I i i : (localBlowup I i).Opens) : Set (localBlowup I i)) = Set.univ := by
    ext v
    simp only [Set.mem_univ, iff_true]
    show (localBlowupToBase I i).base v ∈ (i : X.Opens)
    exact (blowupOver_localBlowupMap_consolidated190 I i).1 (Set.mem_range_self v)
  have h1 : Set.range ⇑(overlapInclusion I i i).base
      = Set.range ⇑(𝟙 (localBlowup I i) : localBlowup I i ⟶ localBlowup I i).base := by
    rw [overlapIncl_eq_consolidated190, Scheme.Opens.range_ι, e2, range_id_base_consolidated190]
  have h2 := IsOpenImmersion.isoOfRangeEq_hom_fac (overlapInclusion I i i) (𝟙 (localBlowup I i)) h1
  rw [Category.comp_id] at h2
  rw [← h2]
  infer_instance

private theorem overlapTrans_self_consolidated190 (i : X.affineOpens) :
    overlapTransition I i i = 𝟙 ((overlap I i i).toScheme) := by
  have := isOpenImmersion_overlapIncl_consolidated190 I i i
  rw [← cancel_mono (overlapInclusion I i i)]
  refine blowupOver_hom_ext_consolidated190 (blowupOver_localBlowupMap_consolidated190 I i) (overlapToBase I i i)
    (blowupOver_overlapMap_consolidated190 I i i).2.1 ?_ ?_ ?_
  · rintro _ ⟨p, rfl⟩
    exact (TopologicalSpace.Opens.mem_inf.mp (overlapMap_base_mem_inf_consolidated190 I i i p)).1
  · rw [Category.assoc, ← overlapMap_eq_consolidated190, overlapTrans_comp_overlapMap_consolidated190]
  · rw [Category.id_comp, ← overlapMap_eq_consolidated190]


end

private noncomputable def tripleOverlapToBase {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j k : X.affineOpens) : pullback (overlapInclusion I i j) (overlapInclusion I i k) ⟶ X :=
  pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapToBase I i j

section
variable {X : Scheme.{u}} (I : X.IdealSheafData) (i j k : X.affineOpens)

private theorem overlapPullbackMap_eq_consolidated190 :
    tripleOverlapToBase I i j k
      = pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapToBase I i j := rfl

private theorem isLocallyGeneratedByNonZeroDivisor_comap_overlapPullbackMap_consolidated190 :
    IsLocallyGeneratedByNonZeroDivisor (I.comap (tripleOverlapToBase I i j k)) := by
  have := isOpenImmersion_overlapIncl_consolidated190 I i j
  have := isOpenImmersion_overlapIncl_consolidated190 I i k
  have h : tripleOverlapToBase I i j k
      = (pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapInclusion I i j)
        ≫ localBlowupToBase I i := by
    rw [overlapPullbackMap_eq_consolidated190, overlapMap_eq_consolidated190, Category.assoc]
  rw [h]
  exact isLocallyGeneratedByNonZeroDivisor_comap_openImmersion_comp_consolidated190 I _ (localBlowupToBase I i) (blowupOver_localBlowupMap_consolidated190 I i).2.1

private theorem overlapPullbackMap_base_mem_inf_left_consolidated190 (p : ↥(pullback (overlapInclusion I i j) (overlapInclusion I i k))) :
    (tripleOverlapToBase I i j k).base p ∈ ((i : X.Opens) ⊓ (j : X.Opens)) := by
  rw [overlapPullbackMap_eq_consolidated190, comp_base_apply_consolidated190]
  exact (blowupOver_overlapMap_consolidated190 I i j).1 (Set.mem_range_self _)

private theorem overlapPullbackMap_base_mem_inf_right_consolidated190 (p : ↥(pullback (overlapInclusion I i j) (overlapInclusion I i k))) :
    (tripleOverlapToBase I i j k).base p ∈ ((i : X.Opens) ⊓ (k : X.Opens)) := by
  have h : tripleOverlapToBase I i j k
      = pullback.snd (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapToBase I i k := by
    rw [overlapPullbackMap_eq_consolidated190, overlapMap_eq_consolidated190, overlapMap_eq_consolidated190, ← Category.assoc,
      ← Category.assoc, pullback.condition]
  rw [h, comp_base_apply_consolidated190]
  exact (blowupOver_overlapMap_consolidated190 I i k).1 (Set.mem_range_self _)

private theorem range_overlapPullbackMap_subset_source_consolidated190 :
    Set.range ⇑(tripleOverlapToBase I i j k).base ⊆ ((i : X.Opens) : Set X) := by
  rintro _ ⟨p, rfl⟩
  exact (TopologicalSpace.Opens.mem_inf.mp (overlapPullbackMap_base_mem_inf_left_consolidated190 I i j k p)).1

private theorem range_overlapPullbackMap_subset_target_consolidated190 :
    Set.range ⇑(tripleOverlapToBase I i j k).base ⊆ ((j : X.Opens) : Set X) := by
  rintro _ ⟨p, rfl⟩
  exact (TopologicalSpace.Opens.mem_inf.mp (overlapPullbackMap_base_mem_inf_left_consolidated190 I i j k p)).2

private theorem range_overlapPullbackMap_subset_inf_consolidated190 :
    Set.range ⇑(tripleOverlapToBase I i j k).base
      ⊆ (((j : X.Opens) ⊓ (k : X.Opens)) : Set X) := by
  rintro _ ⟨p, rfl⟩
  exact TopologicalSpace.Opens.mem_inf.mpr
    ⟨(TopologicalSpace.Opens.mem_inf.mp (overlapPullbackMap_base_mem_inf_left_consolidated190 I i j k p)).2,
      (TopologicalSpace.Opens.mem_inf.mp (overlapPullbackMap_base_mem_inf_right_consolidated190 I i j k p)).2⟩


end

private noncomputable def tripleOverlapLift {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j k : X.affineOpens) :
    pullback (overlapInclusion I i j) (overlapInclusion I i k) ⟶ (overlap I j k).toScheme :=
  liftOfIsBlowupAlongIdealSheafOver (blowupOver_overlapMap_consolidated190 I j k) (tripleOverlapToBase I i j k)
    (isLocallyGeneratedByNonZeroDivisor_comap_overlapPullbackMap_consolidated190 I i j k) (range_overlapPullbackMap_subset_inf_consolidated190 I i j k)

section
variable {X : Scheme.{u}} (I : X.IdealSheafData) (i j k : X.affineOpens)

private theorem overlapPullbackLift_comp_overlapMap_consolidated190 :
    tripleOverlapLift I i j k ≫ overlapToBase I j k = tripleOverlapToBase I i j k :=
  blowupOverLift_comp_consolidated190 _ _ _ _

private theorem overlapPullbackLift_comp_overlapIncl_consolidated190 :
    tripleOverlapLift I i j k ≫ overlapInclusion I j k
      = (pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapTransition I i j)
        ≫ overlapInclusion I j i := by
  refine blowupOver_hom_ext_consolidated190 (blowupOver_localBlowupMap_consolidated190 I j) (tripleOverlapToBase I i j k)
    (isLocallyGeneratedByNonZeroDivisor_comap_overlapPullbackMap_consolidated190 I i j k) (range_overlapPullbackMap_subset_target_consolidated190 I i j k) ?_ ?_
  · rw [Category.assoc, ← overlapMap_eq_consolidated190, overlapPullbackLift_comp_overlapMap_consolidated190]
  · rw [Category.assoc, ← overlapMap_eq_consolidated190, Category.assoc, overlapTrans_comp_overlapMap_consolidated190,
      overlapPullbackMap_eq_consolidated190]


end

private noncomputable def tripleOverlapTransition {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j k : X.affineOpens) :
    pullback (overlapInclusion I i j) (overlapInclusion I i k)
      ⟶ pullback (overlapInclusion I j k) (overlapInclusion I j i) :=
  pullback.lift (tripleOverlapLift I i j k)
    (pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapTransition I i j)
    (overlapPullbackLift_comp_overlapIncl_consolidated190 I i j k)

section
variable {X : Scheme.{u}} (I : X.IdealSheafData) (i j k : X.affineOpens)

private theorem overlapTransPullback_eq_consolidated190 :
    tripleOverlapTransition I i j k
      = pullback.lift (tripleOverlapLift I i j k)
          (pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapTransition I i j)
          (overlapPullbackLift_comp_overlapIncl_consolidated190 I i j k) := rfl

private theorem overlapTransPullback_comp_snd_consolidated190 :
    tripleOverlapTransition I i j k ≫ pullback.snd (overlapInclusion I j k) (overlapInclusion I j i)
      = pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapTransition I i j := by
  rw [overlapTransPullback_eq_consolidated190]
  exact pullback.lift_snd _ _ _

private theorem overlapTransPullback_comp_overlapPullbackMap_consolidated190 :
    tripleOverlapTransition I i j k ≫ tripleOverlapToBase I j k i
      = tripleOverlapToBase I i j k := by
  rw [overlapPullbackMap_eq_consolidated190, overlapTransPullback_eq_consolidated190, ← Category.assoc, pullback.lift_fst,
    overlapPullbackLift_comp_overlapMap_consolidated190]

private theorem overlapTransPullback_cocycle_consolidated190 :
    tripleOverlapTransition I i j k ≫ tripleOverlapTransition I j k i ≫ tripleOverlapTransition I k i j
      = 𝟙 (pullback (overlapInclusion I i j) (overlapInclusion I i k)) := by
  have := isOpenImmersion_overlapIncl_consolidated190 I i j
  have := isOpenImmersion_overlapIncl_consolidated190 I i k
  refine pullback_hom_ext_of_mono_consolidated190 (overlapInclusion I i j) (overlapInclusion I i k) ?_
  refine blowupOver_hom_ext_consolidated190 (blowupOver_localBlowupMap_consolidated190 I i) (tripleOverlapToBase I i j k)
    (isLocallyGeneratedByNonZeroDivisor_comap_overlapPullbackMap_consolidated190 I i j k) (range_overlapPullbackMap_subset_source_consolidated190 I i j k) ?_ ?_
  · simp only [Category.assoc]
    rw [← overlapMap_eq_consolidated190, ← overlapPullbackMap_eq_consolidated190, overlapTransPullback_comp_overlapPullbackMap_consolidated190,
      overlapTransPullback_comp_overlapPullbackMap_consolidated190, overlapTransPullback_comp_overlapPullbackMap_consolidated190]
  · simp only [Category.id_comp, Category.assoc]
    rw [← overlapMap_eq_consolidated190, ← overlapPullbackMap_eq_consolidated190]


end

private noncomputable def blowupGlueData {X : Scheme.{u}} (I : X.IdealSheafData) : Scheme.GlueData where
  toGlueData :=
    { J := X.affineOpens
      U := fun i => localBlowup I i
      V := fun p => (overlap I p.1 p.2).toScheme
      f := fun i j => overlapInclusion I i j
      f_mono := fun i j => by
        have := isOpenImmersion_overlapIncl_consolidated190 I i j
        infer_instance
      f_hasPullback := fun i j k => by
        have := isOpenImmersion_overlapIncl_consolidated190 I i j
        have := isOpenImmersion_overlapIncl_consolidated190 I i k
        infer_instance
      f_id := fun i => isIso_overlapIncl_self_consolidated190 I i
      t := fun i j => overlapTransition I i j
      t_id := fun i => overlapTrans_self_consolidated190 I i
      t' := fun i j k => tripleOverlapTransition I i j k
      t_fac := fun i j k => overlapTransPullback_comp_snd_consolidated190 I i j k
      cocycle := fun i j k => overlapTransPullback_cocycle_consolidated190 I i j k }
  f_open := fun i j => isOpenImmersion_overlapIncl_consolidated190 I i j

private noncomputable def gluedBlowup {X : Scheme.{u}} (I : X.IdealSheafData) : Scheme.{u} :=
  (blowupGlueData I).glued

private noncomputable def localBlowupToGlued {X : Scheme.{u}} (I : X.IdealSheafData)
    (i : X.affineOpens) : localBlowup I i ⟶ gluedBlowup I :=
  (blowupGlueData I).ι i

section
variable {X : Scheme.{u}} (I : X.IdealSheafData)

private theorem isOpenImmersion_gluedIncl_consolidated190 (i : X.affineOpens) : IsOpenImmersion (localBlowupToGlued I i) :=
  (blowupGlueData I).ι_isOpenImmersion i

private theorem overlapTrans_comp_gluedIncl_consolidated190 (i j : X.affineOpens) :
    overlapTransition I i j ≫ overlapInclusion I j i ≫ localBlowupToGlued I j
      = overlapInclusion I i j ≫ localBlowupToGlued I i :=
  (blowupGlueData I).glue_condition i j

private theorem gluedIncl_jointly_surjective_consolidated190 (p : gluedBlowup I) :
    ∃ (j : X.affineOpens) (y : localBlowup I j), (localBlowupToGlued I j).base y = p := by
  obtain ⟨j, y, hy⟩ := (blowupGlueData I).ι_jointly_surjective p
  exact ⟨j, y, hy⟩

private theorem pullback_fst_comp_localBlowupMap_eq_consolidated190 (x y : X.affineOpens) :
    pullback.fst (localBlowupToGlued I x) (localBlowupToGlued I y) ≫ localBlowupToBase I x
      = pullback.snd (localBlowupToGlued I x) (localBlowupToGlued I y) ≫ localBlowupToBase I y := by
  obtain ⟨m, hm1, hm2⟩ := PullbackCone.IsLimit.lift' ((blowupGlueData I).vPullbackConeIsLimit x y)
    (pullback.fst (localBlowupToGlued I x) (localBlowupToGlued I y))
    (pullback.snd (localBlowupToGlued I x) (localBlowupToGlued I y)) pullback.condition
  have e1 : m ≫ overlapInclusion I x y = pullback.fst (localBlowupToGlued I x) (localBlowupToGlued I y) := hm1
  have e2 : m ≫ (overlapTransition I x y ≫ overlapInclusion I y x)
      = pullback.snd (localBlowupToGlued I x) (localBlowupToGlued I y) := hm2
  have key : overlapInclusion I x y ≫ localBlowupToBase I x
      = (overlapTransition I x y ≫ overlapInclusion I y x) ≫ localBlowupToBase I y := by
    rw [Category.assoc]
    exact (overlapTrans_comp_overlapMap_consolidated190 I x y).symm
  have A : pullback.fst (localBlowupToGlued I x) (localBlowupToGlued I y) ≫ localBlowupToBase I x
      = m ≫ (overlapInclusion I x y ≫ localBlowupToBase I x) :=
    (congrArg (fun t => t ≫ localBlowupToBase I x) e1).symm.trans
      (Category.assoc m (overlapInclusion I x y) (localBlowupToBase I x))
  have B : pullback.snd (localBlowupToGlued I x) (localBlowupToGlued I y) ≫ localBlowupToBase I y
      = m ≫ ((overlapTransition I x y ≫ overlapInclusion I y x) ≫ localBlowupToBase I y) :=
    (congrArg (fun t => t ≫ localBlowupToBase I y) e2).symm.trans
      (Category.assoc m (overlapTransition I x y ≫ overlapInclusion I y x) (localBlowupToBase I y))
  exact A.trans ((congrArg (fun t => m ≫ t) key).trans B.symm)


end

private noncomputable def gluedBlowupProjection {X : Scheme.{u}} (I : X.IdealSheafData) :
    gluedBlowup I ⟶ X :=
  (blowupGlueData I).openCover.glueMorphisms (fun i => localBlowupToBase I i)
    (fun x y => pullback_fst_comp_localBlowupMap_eq_consolidated190 I x y)

section
variable {X : Scheme.{u}} (I : X.IdealSheafData) (i : X.affineOpens)

private theorem gluedIncl_comp_gluedProj_consolidated190 : localBlowupToGlued I i ≫ gluedBlowupProjection I = localBlowupToBase I i :=
  (blowupGlueData I).openCover.ι_glueMorphisms _ _ i

private theorem gluedProj_base_gluedIncl_consolidated190 (v : localBlowup I i) :
    (gluedBlowupProjection I).base ((localBlowupToGlued I i).base v) = (localBlowupToBase I i).base v := by
  rw [← comp_base_apply_consolidated190, gluedIncl_comp_gluedProj_consolidated190]

private theorem mem_range_gluedIncl_of_mem_consolidated190 (p : gluedBlowup I) (hp : (gluedBlowupProjection I).base p ∈ (i : X.Opens)) :
    p ∈ Set.range ⇑(localBlowupToGlued I i).base := by
  obtain ⟨j, y, hy⟩ := gluedIncl_jointly_surjective_consolidated190 I p
  have h1 : (localBlowupToBase I j).base y ∈ (i : X.Opens) := by
    rw [← gluedProj_base_gluedIncl_consolidated190 I j y, hy]
    exact hp
  have h2 : y ∈ Set.range ⇑(overlapInclusion I j i).base := by
    rw [overlapIncl_eq_consolidated190, Scheme.Opens.range_ι]
    exact h1
  obtain ⟨v, hv⟩ := h2
  have hcb : (overlapTransition I j i ≫ overlapInclusion I i j ≫ localBlowupToGlued I i).base v
      = (overlapInclusion I j i ≫ localBlowupToGlued I j).base v := by
    rw [overlapTrans_comp_gluedIncl_consolidated190 I j i]
  rw [comp_base_apply_consolidated190, comp_base_apply_consolidated190, comp_base_apply_consolidated190] at hcb
  refine ⟨(overlapInclusion I i j).base ((overlapTransition I j i).base v), ?_⟩
  rw [hcb, hv]
  exact hy


end

private theorem comp_gluedIncl_eq_of_comp_localBlowupMap_consolidated190 {X P : Scheme.{u}} (I : X.IdealSheafData)
    (x y : X.affineOpens) (q : P ⟶ X) (hq : IsLocallyGeneratedByNonZeroDivisor (I.comap q))
    (hx : Set.range ⇑q.base ⊆ ((x : X.Opens) : Set X))
    (hy : Set.range ⇑q.base ⊆ ((y : X.Opens) : Set X))
    {ax : P ⟶ localBlowup I x} {ay : P ⟶ localBlowup I y}
    (hax : ax ≫ localBlowupToBase I x = q) (hay : ay ≫ localBlowupToBase I y = q) :
    ax ≫ localBlowupToGlued I x = ay ≫ localBlowupToGlued I y := by
  have hxy : Set.range ⇑q.base ⊆ (((x : X.Opens) ⊓ (y : X.Opens)) : Set X) :=
    fun w hw => TopologicalSpace.Opens.mem_inf.mpr ⟨hx hw, hy hw⟩
  have hb1 : liftOfIsBlowupAlongIdealSheafOver (blowupOver_overlapMap_consolidated190 I x y) q hq hxy ≫ overlapToBase I x y = q :=
    blowupOverLift_comp_consolidated190 _ _ _ _
  have e1 : ax = liftOfIsBlowupAlongIdealSheafOver (blowupOver_overlapMap_consolidated190 I x y) q hq hxy ≫ overlapInclusion I x y := by
    refine blowupOver_hom_ext_consolidated190 (blowupOver_localBlowupMap_consolidated190 I x) q hq hx hax ?_
    rw [Category.assoc, ← overlapMap_eq_consolidated190, hb1]
  have e2 : ay = (liftOfIsBlowupAlongIdealSheafOver (blowupOver_overlapMap_consolidated190 I x y) q hq hxy ≫ overlapTransition I x y)
      ≫ overlapInclusion I y x := by
    refine blowupOver_hom_ext_consolidated190 (blowupOver_localBlowupMap_consolidated190 I y) q hq hy hay ?_
    rw [Category.assoc, ← overlapMap_eq_consolidated190, Category.assoc, overlapTrans_comp_overlapMap_consolidated190, hb1]
  rw [e1, e2]
  simp only [Category.assoc, ← overlapTrans_comp_gluedIncl_consolidated190 I x y]

private noncomputable def preimageAffineOpen {X W : Scheme.{u}} (g : W ⟶ X) (i : X.affineOpens) :
    W.Opens :=
  g ⁻¹ᵁ (i : X.Opens)

private noncomputable def preimageAffineOpenToBase {X W : Scheme.{u}} (g : W ⟶ X) (i : X.affineOpens) :
    (preimageAffineOpen g i).toScheme ⟶ X :=
  (preimageAffineOpen g i).ι ≫ g

section
variable {X W : Scheme.{u}}

private theorem preimageAffineOpenToBase_eq_consolidated190 (g : W ⟶ X) (i : X.affineOpens) :
    preimageAffineOpenToBase g i = (preimageAffineOpen g i).ι ≫ g := rfl

private theorem isLocallyGeneratedByNonZeroDivisor_comap_preimageAffineOpenToBase_consolidated190 (I : X.IdealSheafData) (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) (i : X.affineOpens) :
    IsLocallyGeneratedByNonZeroDivisor (I.comap (preimageAffineOpenToBase g i)) :=
  isLocallyGeneratedByNonZeroDivisor_comap_openImmersion_comp_consolidated190 I _ g hg

private theorem range_preimageAffineOpenToBase_subset_consolidated190 (g : W ⟶ X) (i : X.affineOpens) :
    Set.range ⇑(preimageAffineOpenToBase g i).base ⊆ ((i : X.Opens) : Set X) := by
  rintro _ ⟨p, rfl⟩
  rw [preimageAffineOpenToBase_eq_consolidated190, comp_base_apply_consolidated190]
  exact ι_base_mem_consolidated190 (preimageAffineOpen g i) p


end

private noncomputable def localBlowupLift {X W : Scheme.{u}} (I : X.IdealSheafData) (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) (i : X.affineOpens) :
    (preimageAffineOpen g i).toScheme ⟶ localBlowup I i :=
  liftOfIsBlowupAlongIdealSheafOver (blowupOver_localBlowupMap_consolidated190 I i) (preimageAffineOpenToBase g i) (isLocallyGeneratedByNonZeroDivisor_comap_preimageAffineOpenToBase_consolidated190 I g hg i)
    (range_preimageAffineOpenToBase_subset_consolidated190 g i)

private theorem liftChart_comp_localBlowupMap_consolidated190 {X W : Scheme.{u}} (I : X.IdealSheafData) (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) (i : X.affineOpens) :
    localBlowupLift I g hg i ≫ localBlowupToBase I i = preimageAffineOpenToBase g i :=
  blowupOverLift_comp_consolidated190 _ _ _ _

private noncomputable def preimageAffineOpensCover {X W : Scheme.{u}} (g : W ⟶ X) : W.OpenCover :=
  Scheme.Cover.mkOfCovers X.affineOpens (fun i => (preimageAffineOpen g i).toScheme)
    (fun i => (preimageAffineOpen g i).ι)
    (fun w => by
      obtain ⟨i, hi⟩ := X.exists_affineOpens_mem (g.base w)
      have hw : w ∈ Set.range ⇑(preimageAffineOpen g i).ι.base := by
        rw [Scheme.Opens.range_ι]
        exact hi
      obtain ⟨v, hv⟩ := hw
      exact ⟨i, v, hv⟩)

section
variable {X W : Scheme.{u}}

private theorem hom_ext_of_preimageAffineOpen_ι_comp_consolidated190 (g : W ⟶ X) {Z : Scheme.{u}} (a b : W ⟶ Z)
    (h : ∀ i : X.affineOpens, (preimageAffineOpen g i).ι ≫ a = (preimageAffineOpen g i).ι ≫ b) : a = b := by
  refine (preimageAffineOpensCover g).hom_ext a b (fun i => ?_)
  exact h i

private theorem liftChart_pullback_condition_consolidated190 (I : X.IdealSheafData) (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) (x y : X.affineOpens) :
    pullback.fst (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι ≫ (localBlowupLift I g hg x ≫ localBlowupToGlued I x)
      = pullback.snd (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι
        ≫ (localBlowupLift I g hg y ≫ localBlowupToGlued I y) := by
  have hxy : pullback.fst (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι ≫ preimageAffineOpenToBase g x
      = pullback.snd (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι ≫ preimageAffineOpenToBase g y := by
    rw [preimageAffineOpenToBase_eq_consolidated190, preimageAffineOpenToBase_eq_consolidated190, ← Category.assoc, ← Category.assoc, pullback.condition]
  have hcart : IsLocallyGeneratedByNonZeroDivisor (I.comap
      (pullback.fst (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι ≫ preimageAffineOpenToBase g x)) := by
    have h : pullback.fst (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι ≫ preimageAffineOpenToBase g x
        = (pullback.fst (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι ≫ (preimageAffineOpen g x).ι) ≫ g := by
      rw [preimageAffineOpenToBase_eq_consolidated190, Category.assoc]
    rw [h]
    exact isLocallyGeneratedByNonZeroDivisor_comap_openImmersion_comp_consolidated190 I _ g hg
  have hrx : Set.range ⇑(pullback.fst (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι ≫ preimageAffineOpenToBase g x).base
      ⊆ ((x : X.Opens) : Set X) := by
    rintro _ ⟨p, rfl⟩
    rw [comp_base_apply_consolidated190]
    exact range_preimageAffineOpenToBase_subset_consolidated190 g x (Set.mem_range_self _)
  have hry : Set.range ⇑(pullback.fst (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι ≫ preimageAffineOpenToBase g x).base
      ⊆ ((y : X.Opens) : Set X) := by
    rw [hxy]
    rintro _ ⟨p, rfl⟩
    rw [comp_base_apply_consolidated190]
    exact range_preimageAffineOpenToBase_subset_consolidated190 g y (Set.mem_range_self _)
  rw [← Category.assoc, ← Category.assoc]
  refine comp_gluedIncl_eq_of_comp_localBlowupMap_consolidated190 I x y
    (pullback.fst (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι ≫ preimageAffineOpenToBase g x) hcart hrx hry ?_ ?_
  · rw [Category.assoc, liftChart_comp_localBlowupMap_consolidated190]
  · rw [Category.assoc, liftChart_comp_localBlowupMap_consolidated190, hxy]


end

private noncomputable def gluedBlowupLift {X W : Scheme.{u}} (I : X.IdealSheafData) (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) : W ⟶ gluedBlowup I :=
  (preimageAffineOpensCover g).glueMorphisms (fun i => localBlowupLift I g hg i ≫ localBlowupToGlued I i)
    (fun x y => liftChart_pullback_condition_consolidated190 I g hg x y)

section
variable {X W : Scheme.{u}} (I : X.IdealSheafData) (g : W ⟶ X) (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g))

private theorem ι_comp_liftGlued_consolidated190 (i : X.affineOpens) :
    (preimageAffineOpen g i).ι ≫ gluedBlowupLift I g hg = localBlowupLift I g hg i ≫ localBlowupToGlued I i :=
  (preimageAffineOpensCover g).ι_glueMorphisms _ _ i

private theorem liftGlued_comp_gluedProj_consolidated190 : gluedBlowupLift I g hg ≫ gluedBlowupProjection I = g := by
  refine hom_ext_of_preimageAffineOpen_ι_comp_consolidated190 g (gluedBlowupLift I g hg ≫ gluedBlowupProjection I) g (fun i => ?_)
  rw [← Category.assoc, ι_comp_liftGlued_consolidated190, Category.assoc, gluedIncl_comp_gluedProj_consolidated190, liftChart_comp_localBlowupMap_consolidated190,
    preimageAffineOpenToBase_eq_consolidated190]

private theorem eq_liftGlued_of_comp_eq_consolidated190 (b : W ⟶ gluedBlowup I)
    (hb : b ≫ gluedBlowupProjection I = g) : b = gluedBlowupLift I g hg := by
  refine hom_ext_of_preimageAffineOpen_ι_comp_consolidated190 g b (gluedBlowupLift I g hg) (fun i => ?_)
  rw [ι_comp_liftGlued_consolidated190]
  have hr : Set.range ⇑((preimageAffineOpen g i).ι ≫ b).base ⊆ Set.range ⇑(localBlowupToGlued I i).base := by
    rintro _ ⟨p, rfl⟩
    refine mem_range_gluedIncl_of_mem_consolidated190 I i _ ?_
    rw [← comp_base_apply_consolidated190, Category.assoc, hb]
    exact range_preimageAffineOpenToBase_subset_consolidated190 g i (Set.mem_range_self p)
  have := isOpenImmersion_gluedIncl_consolidated190 I i
  have hc : IsOpenImmersion.lift (localBlowupToGlued I i) ((preimageAffineOpen g i).ι ≫ b) hr ≫ localBlowupToGlued I i
      = (preimageAffineOpen g i).ι ≫ b := IsOpenImmersion.lift_fac _ _ _
  have hc2 : IsOpenImmersion.lift (localBlowupToGlued I i) ((preimageAffineOpen g i).ι ≫ b) hr ≫ localBlowupToBase I i
      = preimageAffineOpenToBase g i := by
    rw [← gluedIncl_comp_gluedProj_consolidated190 I i, ← Category.assoc, hc, Category.assoc, hb, preimageAffineOpenToBase_eq_consolidated190]
  have hc3 : IsOpenImmersion.lift (localBlowupToGlued I i) ((preimageAffineOpen g i).ι ≫ b) hr
      = localBlowupLift I g hg i :=
    blowupOver_hom_ext_consolidated190 (blowupOver_localBlowupMap_consolidated190 I i) (preimageAffineOpenToBase g i) (isLocallyGeneratedByNonZeroDivisor_comap_preimageAffineOpenToBase_consolidated190 I g hg i)
      (range_preimageAffineOpenToBase_subset_consolidated190 g i) hc2 (liftChart_comp_localBlowupMap_consolidated190 I g hg i)
  rw [← hc, hc3]


end

private theorem isBlowupAlongIdealSheaf_gluedProj_consolidated190 {X : Scheme.{u}} (I : X.IdealSheafData) :
    IsBlowupAlongIdealSheaf (gluedBlowupProjection I) I := by
  constructor
  · have : ∀ i : X.affineOpens, IsOpenImmersion (localBlowupToGlued I i) := fun i =>
      isOpenImmersion_gluedIncl_consolidated190 I i
    refine IsLocallyGeneratedByNonZeroDivisor.of_isOpenImmersion_cover (I.comap (gluedBlowupProjection I))
      (fun i => localBlowup I i) (fun i => localBlowupToGlued I i) ?_ ?_
    · intro p
      obtain ⟨j, y, hy⟩ := gluedIncl_jointly_surjective_consolidated190 I p
      exact ⟨j, y, hy⟩
    · intro i
      rw [← Scheme.IdealSheafData.comap_comp, gluedIncl_comp_gluedProj_consolidated190]
      exact (blowupOver_localBlowupMap_consolidated190 I i).2.1
  · intro W g hg
    exact ⟨gluedBlowupLift I g hg, liftGlued_comp_gluedProj_consolidated190 I g hg,
      fun b hb => eq_liftGlued_of_comp_eq_consolidated190 I g hg b hb⟩

theorem exists_isBlowupAlongIdealSheaf (X : Scheme.{u}) (I : X.IdealSheafData) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X), IsBlowupAlongIdealSheaf π I :=
  ⟨gluedBlowup I, gluedBlowupProjection I, isBlowupAlongIdealSheaf_gluedProj_consolidated190 I⟩

section
noncomputable def blowup {X : Scheme.{u}} (I : X.IdealSheafData) : Scheme.{u} :=
  (exists_isBlowupAlongIdealSheaf X I).choose

noncomputable def blowup.proj {X : Scheme.{u}} (I : X.IdealSheafData) : blowup I ⟶ X :=
  (exists_isBlowupAlongIdealSheaf X I).choose_spec.choose

end

theorem blowup.isBlowupAlongIdealSheaf_proj {X : Scheme.{u}} (I : X.IdealSheafData) :
    IsBlowupAlongIdealSheaf (blowup.proj I) I :=
  (exists_isBlowupAlongIdealSheaf X I).choose_spec.choose_spec

end FunctorialResolution.Blowup
end

-- Source: Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProper
section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace FunctorialResolution.Blowup

private theorem ofIdealTop_ideal_top_eq_self_consolidated213 {X : Scheme.{u}} [IsAffine X] (I : X.IdealSheafData) :
    AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
      (I.ideal ⟨⊤, isAffineOpen_top X⟩) = I :=
  Scheme.IdealSheafData.ext_of_isAffine (by simp)

private theorem map_inv_map_hom_eq_self_consolidated213 {A B : CommRingCat.{u}} (e : A ≅ B) (K : Ideal ↑A) :
    Ideal.map (CommRingCat.Hom.hom e.inv) (Ideal.map (CommRingCat.Hom.hom e.hom) K) = K := by
  rw [Ideal.map_map, ← CommRingCat.hom_comp, e.hom_inv_id, CommRingCat.hom_id, Ideal.map_id]

private theorem exists_isBlowupAlongIdealSheaf_isProper_spec_of_isNoetherianRing_consolidated213 (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : (Spec (CommRingCat.of A)).IdealSheafData) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ Spec (CommRingCat.of A)),
      IsBlowupAlongIdealSheaf π I ∧ IsProper π := by
  obtain ⟨J, hJ⟩ : ∃ J : Ideal A, FunctorialResolution.Blowup.specIdealSheaf J = I := by
    refine ⟨Ideal.map (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of A)).hom)
      (I.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩), ?_⟩
    rw [FunctorialResolution.Blowup.specIdealSheaf_eq_ofIdealTop, map_inv_map_hom_eq_self_consolidated213 (Scheme.ΓSpecIso (CommRingCat.of A))]
    exact ofIdealTop_ideal_top_eq_self_consolidated213 I
  refine ⟨FunctorialResolution.Blowup.affineBlowup J, FunctorialResolution.Blowup.AffineBlowup.toSpec J, ?_,
    FunctorialResolution.Blowup.isProper_affineBlowup_toSpec J⟩
  rw [← hJ]
  exact FunctorialResolution.Blowup.isBlowupAlongIdealSheaf_affineBlowup_toSpec J

theorem exists_isBlowupAlongIdealSheaf_isProper_spec (R : CommRingCat.{u}) [IsNoetherianRing ↑R]
    (I : (Spec R).IdealSheafData) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ Spec R), IsBlowupAlongIdealSheaf π I ∧ IsProper π :=
  exists_isBlowupAlongIdealSheaf_isProper_spec_of_isNoetherianRing_consolidated213 (↑R) I

theorem isProper_of_isBlowupAlongIdealSheaf_of_isAffine {Y B : Scheme.{u}} [IsAffine Y]
    [IsNoetherianRing Γ(Y, ⊤)] (J : Y.IdealSheafData) {p : B ⟶ Y} (h : IsBlowupAlongIdealSheaf p J) :
    IsProper p := by
  obtain ⟨Y', π, hπ, hproper⟩ :=
    exists_isBlowupAlongIdealSheaf_isProper_spec Γ(Y, ⊤) (J.comap Y.isoSpec.inv)
  have hq : IsBlowupAlongIdealSheaf (p ≫ Y.isoSpec.hom) (J.comap Y.isoSpec.inv) := h.comp_iso_hom Y.isoSpec
  obtain ⟨b, hb⟩ := hπ.exists_lift (p ≫ Y.isoSpec.hom) hq.1
  obtain ⟨a, ha⟩ := hq.exists_lift π hπ.1
  have hab : a ≫ b = 𝟙 Y' := by
    refine hπ.hom_ext hπ.1 ?_ ?_
    · rw [Category.assoc, hb, ha]
    · rw [Category.id_comp]
  have hba : b ≫ a = 𝟙 B := by
    refine hq.hom_ext hq.1 ?_ ?_
    · rw [Category.assoc, ha, hb]
    · rw [Category.id_comp]
  have : IsIso b := ⟨a, hba, hab⟩
  have : IsProper π := hproper
  have hp : b ≫ π ≫ Y.isoSpec.inv = p := by
    rw [← Category.assoc, hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← hp]
  infer_instance

private theorem isProper_morphismRestrict_of_isProper_pullbackSnd_consolidated213 {X X' : Scheme.{u}} (f : X' ⟶ X)
    (U : X.Opens) (h : IsProper (pullback.snd f U.ι)) :
    IsProper (AlgebraicGeometry.morphismRestrict f U) := by
  have key : (AlgebraicGeometry.pullbackRestrictIsoRestrict f U).hom ≫
      AlgebraicGeometry.morphismRestrict f U = pullback.snd f U.ι := by
    simp [AlgebraicGeometry.morphismRestrict]
  have h2 : IsProper
      ((AlgebraicGeometry.pullbackRestrictIsoRestrict f U).hom ≫
        AlgebraicGeometry.morphismRestrict f U) := by
    rw [key]; exact h
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)
    (AlgebraicGeometry.pullbackRestrictIsoRestrict f U).hom
    (AlgebraicGeometry.morphismRestrict f U)).mp h2

private theorem isNoetherianRing_sections_top_of_affineOpen_consolidated213 {X : Scheme.{u}}
    [IsLocallyNoetherian X] (U : X.affineOpens) :
    IsNoetherianRing Γ((U : X.Opens).toScheme, ⊤) := by
  have : IsNoetherianRing Γ(X, (U : X.Opens)) :=
    AlgebraicGeometry.IsLocallyNoetherian.component_noetherian U
  exact isNoetherianRing_of_ringEquiv _
    (CategoryTheory.Iso.commRingCatIsoToRingEquiv ((U : X.Opens).topIso)).symm

theorem blowupIsProper : BlowupIsProper.{u} := by
  intro X X' hX π Z hZ
  have := hX
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper)
    (fun U : X.affineOpens => (U : X.Opens)) (AlgebraicGeometry.iSup_affineOpens_eq_top X) ?_
  intro U
  have : IsAffine (U : X.Opens).toScheme := U.2
  have : IsNoetherianRing Γ((U : X.Opens).toScheme, ⊤) := isNoetherianRing_sections_top_of_affineOpen_consolidated213 U
  exact isProper_morphismRestrict_of_isProper_pullbackSnd_consolidated213 π (U : X.Opens)
    (isProper_of_isBlowupAlongIdealSheaf_of_isAffine (Z.comap (U : X.Opens).ι)
      (hZ.pullback_snd_of_isOpenImmersion (U : X.Opens).ι))

end FunctorialResolution.Blowup
end

-- Source: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SaturationByPowers
section
noncomputable def UpperTheory.Reformulated.B.SaturationByPowers.saturationByPowers.{u_1} :
    {A : Type u_1} → [inst : CommRing A] → Ideal A → A → Ideal A :=
  fun {A} _ J a =>
    { carrier := {x : A | ∃ n : ℕ, a ^ n * x ∈ J}
      add_mem' := by
        rintro x y ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        have h : a ^ (m + n) * (x + y) = a ^ n * (a ^ m * x) + a ^ m * (a ^ n * y) := by ring
        rw [h]
        exact J.add_mem (J.mul_mem_left _ hm) (J.mul_mem_left _ hn)
      zero_mem' := ⟨0, by rw [mul_zero]; exact J.zero_mem⟩
      smul_mem' := by
        rintro c x ⟨n, hn⟩
        refine ⟨n, ?_⟩
        have h : a ^ n * (c • x) = c * (a ^ n * x) := by rw [smul_eq_mul]; ring
        rw [h]
        exact J.mul_mem_left _ hn }
end
end
