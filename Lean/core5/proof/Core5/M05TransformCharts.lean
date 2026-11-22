import Mathlib
import Core5.M04DescentInterfaces

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

universe u v
noncomputable section
-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

private theorem algebraMap_quotient_map_mk_consolidated161 {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (I : Ideal R) (r : R) :
    algebraMap (R ⧸ I) (A ⧸ Ideal.map (algebraMap R A) I) (Ideal.Quotient.mk I r)
      = Ideal.Quotient.mk (Ideal.map (algebraMap R A) I) (algebraMap R A r) := rfl

private theorem algebraMap_quotient_apply_consolidated161 {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (I : Ideal R) (a : k) :
    algebraMap k (R ⧸ I) a = Ideal.Quotient.mk I (algebraMap k R a) := rfl

private theorem formallySmooth_quotient_map_of_isLocalization_consolidated161 (k : Type u) [CommRing k] {R : Type u} [CommRing R]
    [Algebra k R] (M : Submonoid R) (A : Type u) [CommRing A] [Algebra R A] [IsLocalization M A]
    [Algebra k A] [IsScalarTower k R A] (I : Ideal R)
    (h : Algebra.FormallySmooth k (R ⧸ I)) :
    Algebra.FormallySmooth k (A ⧸ Ideal.map (algebraMap R A) I) := by
  have := h
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) M)
      (A ⧸ Ideal.map (algebraMap R A) I) := inferInstance
  have : Algebra.FormallyEtale (R ⧸ I) (A ⧸ Ideal.map (algebraMap R A) I) :=
    Algebra.FormallyEtale.of_isLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) M)
  have : IsScalarTower k (R ⧸ I) (A ⧸ Ideal.map (algebraMap R A) I) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    rw [algebraMap_quotient_apply_consolidated161 I a, algebraMap_quotient_map_mk_consolidated161 I (algebraMap k R a),
      algebraMap_quotient_apply_consolidated161 (Ideal.map (algebraMap R A) I) a, IsScalarTower.algebraMap_apply k R A]
  exact Algebra.FormallySmooth.comp k (R ⧸ I) (A ⧸ Ideal.map (algebraMap R A) I)

private theorem map_algebraMap_eq_map_map_of_algEquiv_consolidated161 {R L M : Type u} [CommRing R] [CommRing L]
    [CommRing M] [Algebra R L] [Algebra R M] (e : L ≃ₐ[R] M) (J : Ideal R) :
    Ideal.map (algebraMap R M) J
      = Ideal.map e.toAlgHom.toRingHom (Ideal.map (algebraMap R L) J) := by
  rw [Ideal.map_map]
  refine congrArg (fun φ : R →+* M => Ideal.map φ J) ?_
  exact RingHom.ext fun r => (e.commutes r).symm

private theorem ι_appLE_eq_topIso_inv_consolidated161 {X : Scheme.{u}} (U : X.Opens)
    (e : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U) : U.ι.appLE U ⊤ e = U.topIso.inv := by
  rw [Scheme.Opens.ι_appLE U U ⊤ e, Scheme.Opens.topIso_inv]
  refine congrArg (fun h => X.presheaf.map h) ?_
  exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)

private theorem ofIdealTop_ideal_top_consolidated161 {Y : Scheme.{u}} (J : Ideal Γ(Y, ⊤))
    (hY : IsAffineOpen (⊤ : Y.Opens)) :
    (Scheme.IdealSheafData.ofIdealTop J).ideal ⟨⊤, hY⟩ = J := by
  rw [Scheme.IdealSheafData.ofIdealTop_ideal]
  have h1 : (homOfLE (le_refl (⊤ : Y.Opens)) : (⊤ : Y.Opens) ⟶ ⊤) = 𝟙 _ := rfl
  rw [h1, op_id, CategoryTheory.Functor.map_id]
  exact Ideal.map_id J

section
variable (k : Type u) [Field k] (m : ℕ)

private theorem affineSpaceGlobalSectionsHom_eq_eval₂Hom_consolidated161 :
    affineSpaceGlobalSectionsHom k m =
      MvPolynomial.eval₂Hom
        (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (affineSpaceFinToSpec k m).appTop).hom)
        (fun i : ULift.{u} (Fin m) => AffineSpace.coord (Spec (CommRingCat.of k)) i) := by
  show ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop).hom = _
  rw [AffineSpace.SpecIso_hom_appTop, ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    CommRingCat.hom_ofHom]

private theorem affineSpaceGlobalSectionsHom_X_consolidated161 (i : ULift.{u} (Fin m)) :
    affineSpaceGlobalSectionsHom k m (MvPolynomial.X i) = AffineSpace.coord (Spec (CommRingCat.of k)) i := by
  rw [affineSpaceGlobalSectionsHom_eq_eval₂Hom_consolidated161, MvPolynomial.eval₂Hom_X']

private theorem affineSpaceGlobalSectionsHom_C_consolidated161 (b : k) :
    affineSpaceGlobalSectionsHom k m (MvPolynomial.C b) =
      (affineSpaceFinToSpec k m).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom b) := by
  rw [affineSpaceGlobalSectionsHom_eq_eval₂Hom_consolidated161, MvPolynomial.eval₂Hom_C]
  rfl


end

private def affineSpaceGlobalSectionsEquiv_consolidated161 (k : Type u) [Field k] (m : ℕ) :
    MvPolynomial (ULift.{u} (Fin m)) k ≃+* Γ(affineSpaceFin k m, ⊤) where
  toFun := affineSpaceGlobalSectionsHom k m
  invFun := fun z =>
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).hom.hom
      ((AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).inv.appTop.hom z)
  left_inv := by
    intro x
    have e : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv ≫
        ((AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop ≫
          (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).inv.appTop) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).hom = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop, Category.id_comp,
        Iso.inv_hom_id]
    exact congrArg
      (fun φ : CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k) ⟶
        CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k) => φ.hom x) e
  right_inv := by
    intro z
    have e : (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).inv.appTop ≫
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).hom ≫
          (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv) ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop = 𝟙 _ := by
      rw [Iso.hom_inv_id, Category.id_comp, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id,
        Scheme.Hom.id_appTop]
    exact congrArg
      (fun φ : Γ(affineSpaceFin k m, ⊤) ⟶ Γ(affineSpaceFin k m, ⊤) => φ.hom z) e
  map_mul' := (affineSpaceGlobalSectionsHom k m).map_mul
  map_add' := (affineSpaceGlobalSectionsHom k m).map_add

theorem sectionsAlgebraMap_apply_eq (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (a : k) :
    sectionsAlgebraMap k p U a =
      (p.appLE ⊤ U (le_preimage_top k p U)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a) := by
  rw [sectionsAlgebraMap_eq]
  rfl

section
variable (k : Type u) [CommRing k] {X W : Scheme.{u}} (f : W ⟶ X) (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens)

private theorem appLE_top_comp_app_consolidated161 :
    p.appLE ⊤ U (le_preimage_top k p U) ≫ f.app U
      = (f ≫ p).appLE ⊤ (f ⁻¹ᵁ U) (le_preimage_top k (f ≫ p) (f ⁻¹ᵁ U)) := by
  have hn := f.c.naturality (homOfLE (le_preimage_top k p U)).op
  show (p.app ⊤ ≫ X.presheaf.map (homOfLE (le_preimage_top k p U)).op) ≫ f.app U
      = (f ≫ p).app ⊤ ≫ W.presheaf.map (homOfLE (le_preimage_top k (f ≫ p) (f ⁻¹ᵁ U))).op
  rw [Category.assoc]
  exact congrArg (fun t => p.app ⊤ ≫ t) hn

private theorem app_sectionsAlgebraMap_consolidated161 (a : k) :
    (f.app U).hom (sectionsAlgebraMap k p U a)
      = sectionsAlgebraMap k (f ≫ p) (f ⁻¹ᵁ U) a := by
  rw [sectionsAlgebraMap_apply_eq, sectionsAlgebraMap_apply_eq]
  exact congrArg
    (fun φ : Γ(Spec (CommRingCat.of k), ⊤) ⟶ Γ(W, f ⁻¹ᵁ U) =>
      φ.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)) (appLE_top_comp_app_consolidated161 k f p U)


end

section
variable {X : Scheme.{u}}

theorem mem_basicOpen_of_notMem_primeIdealOf {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (g : Γ(X, U))
    (hg : g ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) : x ∈ X.basicOpen g := by
  have h1 : hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have h2 : hU.fromSpec ⁻¹ᵁ (X.basicOpen g) = PrimeSpectrum.basicOpen g :=
    hU.fromSpec_preimage_basicOpen g
  have h3 : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ (X.basicOpen g) := by
    rw [h2]
    exact (PrimeSpectrum.mem_basicOpen g _).mpr hg
  have h4 : hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen g := h3
  rwa [h1] at h4

theorem ideal_le_primeIdealOf (Z : X.IdealSheafData) {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (hxZ : x ∈ Z.support) :
    Z.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h : x ∈ X.zeroLocus (↑(Z.ideal ⟨U, hU⟩) : Set Γ(X, U)) :=
    (Scheme.IdealSheafData.mem_support_iff_of_mem (I := Z) (U := ⟨U, hU⟩) hx).mp hxZ
  intro f hf
  by_contra hfp
  have hx' : x ∈ X.basicOpen f := mem_basicOpen_of_notMem_primeIdealOf hU hx f hfp
  rw [Scheme.mem_zeroLocus_iff] at h
  exact h f hf hx'

theorem restrictIdeal_eq_coordIdeal_of_ideal_eq_span {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} (hU : IsAffineOpen U) {m : ℕ}
    (c : EtaleChart p U m) (Z : X.IdealSheafData) (S : Finset (Fin m))
    (h : Z.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m)))) :
    restrictIdeal Z U = c.coordIdeal S := by
  have : IsAffine U.toScheme := hU
  have hTop : IsAffineOpen (⊤ : U.toScheme.Opens) := isAffineOpen_top U.toScheme
  have e : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := fun z _ => z.2
  have hsets : (U.topIso.inv.hom) '' (c.coord '' (S : Set (Fin m)))
      = (c.map.appTop.hom) ''
        ((fun i : Fin m => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
          (S : Set (Fin m))) := by
    rw [Set.image_image, Set.image_image]
    refine congrArg (fun g : Fin m → Γ(U.toScheme, ⊤) => g '' (S : Set (Fin m))) ?_
    funext j
    rw [EtaleChart.coord_def]
    exact Iso.hom_inv_id_apply U.topIso _
  rw [restrictIdeal_eq_comap_ι, c.coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_eq_ofIdealTop_span_coord]
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE Z U.ι ⟨U, hU⟩ ⟨⊤, hTop⟩ e,
    Scheme.IdealSheafData.comap_ideal_top_eq_map_appTop, ofIdealTop_ideal_top_consolidated161, h,
    ι_appLE_eq_topIso_inv_consolidated161, Ideal.map_span, Ideal.map_span]
  exact congrArg Ideal.span hsets


end

section
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens} (hU : IsAffineOpen U) {m : ℕ} (y : ULift.{u} (Fin m) → Γ(X, U)) (f : MvPolynomial (ULift.{u} (Fin m)) k →+* Γ(X, U)) (hC : ∀ a : k, f (MvPolynomial.C a) = sectionsAlgebraMap k p U a) (hX : ∀ i : ULift.{u} (Fin m), f (MvPolynomial.X i) = y i) (hf : f.Etale)
include hU hC hX hf

theorem etale_homOfVector_of_ringHom_etale :
    Etale
      (AffineSpace.homOfVector (U.ι ≫ p) (fun i => U.topIso.inv.hom (y i))) := by
  have : IsAffine U.toScheme := hU
  have hresp : RingHom.RespectsIso @RingHom.Etale :=
    (AlgebraicGeometry.HasRingHomProperty.isLocal_ringHomProperty
      (P := @Etale)).respectsIso
  have hover : AffineSpace.homOfVector (U.ι ≫ p) (fun i => U.topIso.inv.hom (y i)) ≫
      affineSpaceFinToSpec k m = U.ι ≫ p := by simp
  have e1 : (affineSpaceFinToSpec k m).appTop ≫
      (AffineSpace.homOfVector (U.ι ≫ p) (fun i => U.topIso.inv.hom (y i))).appTop
        = (U.ι ≫ p).appTop := by
    rw [← Scheme.Hom.comp_appTop, hover]
  have e2 : p.appLE ⊤ U (le_preimage_top k p U) ≫ U.topIso.inv = (U.ι ≫ p).appTop :=
    appLE_top_comp_topIso_inv p U (le_preimage_top k p U)
  have key : ((AffineSpace.homOfVector (U.ι ≫ p)
        (fun i => U.topIso.inv.hom (y i))).appTop.hom).comp (affineSpaceGlobalSectionsHom k m)
      = (U.topIso.inv.hom).comp f := by
    apply MvPolynomial.ringHom_ext
    · intro b
      show (AffineSpace.homOfVector (U.ι ≫ p) (fun i => U.topIso.inv.hom (y i))).appTop.hom
          (affineSpaceGlobalSectionsHom k m (MvPolynomial.C b))
          = U.topIso.inv.hom (f (MvPolynomial.C b))
      rw [affineSpaceGlobalSectionsHom_C_consolidated161, hC, sectionsAlgebraMap_apply_eq]
      exact congrArg (fun φ : Γ(Spec (CommRingCat.of k), ⊤) ⟶ Γ(U.toScheme, ⊤) =>
        φ.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom b)) (e1.trans e2.symm)
    · intro i
      show (AffineSpace.homOfVector (U.ι ≫ p) (fun i => U.topIso.inv.hom (y i))).appTop.hom
          (affineSpaceGlobalSectionsHom k m (MvPolynomial.X i))
          = U.topIso.inv.hom (f (MvPolynomial.X i))
      rw [affineSpaceGlobalSectionsHom_X_consolidated161, hX]
      exact AffineSpace.homOfVector_appTop_coord (U.ι ≫ p)
        (fun i => U.topIso.inv.hom (y i)) i
  have hA : (AffineSpace.homOfVector (U.ι ≫ p) (fun i => U.topIso.inv.hom (y i))).appTop.hom
      = ((U.topIso.inv.hom).comp f).comp (affineSpaceGlobalSectionsEquiv_consolidated161 k m).symm.toRingHom := by
    refine RingHom.ext fun z => ?_
    have h1 := DFunLike.congr_fun key ((affineSpaceGlobalSectionsEquiv_consolidated161 k m).symm z)
    simp only [RingHom.comp_apply] at h1 ⊢
    rw [show affineSpaceGlobalSectionsHom k m ((affineSpaceGlobalSectionsEquiv_consolidated161 k m).symm z) = z from
      (affineSpaceGlobalSectionsEquiv_consolidated161 k m).apply_symm_apply z] at h1
    exact h1
  rw [AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine (P := @Etale), hA]
  exact hresp.right _ (affineSpaceGlobalSectionsEquiv_consolidated161 k m).symm
    (hresp.left f U.topIso.commRingCatIsoToRingEquiv.symm hf)

theorem exists_etaleChart_coord_eq :
    ∃ c : EtaleChart p U m, ∀ j : Fin m, c.coord j = y (ULift.up j) := by
  refine ⟨EtaleChart.ofCoords p U (fun i => U.topIso.inv.hom (y i))
      (etale_homOfVector_of_ringHom_etale p hU y f hC hX hf), fun j => ?_⟩
  rw [EtaleChart.coord_def, EtaleChart.ofCoords_map, AffineSpace.homOfVector_appTop_coord]
  exact Iso.inv_hom_id_apply U.topIso (y (ULift.up j))


end

section
variable {X : Scheme.{u}} {k : Type u} [Field k] [CharZero k] (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ p)]

theorem exists_chart_ideal_eq_span_coord (x : X) (hx : x ∈ Z.support) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U) (m : ℕ) (c : EtaleChart p U m) (S : Finset (Fin m)),
      x ∈ U ∧ Z.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m))) := by
  obtain ⟨U₀, m, hxU₀, hU₀, ⟨c⟩⟩ := exists_etaleChart p x
  let _ : Algebra k Γ(X, U₀) := sectionsAlgebra k p U₀
  have hk : (algebraMap k Γ(X, U₀)) = sectionsAlgebraMap k p U₀ :=
    algebraMap_sectionsAlgebra k p U₀
  let _ : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U₀) := c.algebra
  have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U₀) := c.isScalarTower
  have : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U₀) :=
    c.algebra_formallyEtale hU₀
  have : IsNoetherianRing Γ(X, U₀) := isNoetherianRing_sections k p ⟨U₀, hU₀⟩ hk
  have : DecidableEq (ULift.{u} (Fin m)) := Classical.decEq _
  let P : PrimeSpectrum Γ(X, U₀) := hU₀.primeIdealOf ⟨x, hxU₀⟩
  have hIq : Z.ideal ⟨U₀, hU₀⟩ ≤ P.asIdeal := ideal_le_primeIdealOf Z hU₀ hxU₀ hx
  have : IsNoetherianRing (Localization.AtPrime P.asIdeal) :=
    IsLocalization.isNoetherianRing P.asIdeal.primeCompl
      (Localization.AtPrime P.asIdeal) inferInstance
  have hVaff : IsAffineOpen (Z.subschemeι ⁻¹ᵁ U₀) := isAffineOpen_preimage_subschemeι Z hU₀
  let _ : Algebra k Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ U₀) :=
    sectionsAlgebra k (Z.subschemeι ≫ p) (Z.subschemeι ⁻¹ᵁ U₀)
  have : Algebra.FormallySmooth k Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ U₀) :=
    formallySmooth_sections k (Z.subschemeι ≫ p) (Z.subschemeι ⁻¹ᵁ U₀) hVaff
      (algebraMap_sectionsAlgebra k (Z.subschemeι ≫ p) (Z.subschemeι ⁻¹ᵁ U₀))
  have hker : RingHom.ker (Z.subschemeι.app U₀).hom = Z.ideal ⟨U₀, hU₀⟩ :=
    Z.ker_subschemeι_app ⟨U₀, hU₀⟩
  have hsurj : Function.Surjective ⇑((Z.subschemeι.app U₀).hom) :=
    Z.subschemeι_app_surjective ⟨U₀, hU₀⟩
  let Φ : Γ(X, U₀) →ₐ[k] Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ U₀) :=
    { (Z.subschemeι.app U₀).hom with
      commutes' := fun a => app_sectionsAlgebraMap_consolidated161 k Z.subschemeι p U₀ a }
  have hΦsurj : Function.Surjective ⇑Φ := hsurj
  have hkerΦ : RingHom.ker (Φ : Γ(X, U₀) →+* Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ U₀))
      = Z.ideal ⟨U₀, hU₀⟩ := hker
  have hfs : Algebra.FormallySmooth k (Γ(X, U₀) ⧸ Z.ideal ⟨U₀, hU₀⟩) := by
    have e1 : (Γ(X, U₀) ⧸ Z.ideal ⟨U₀, hU₀⟩) ≃ₐ[k]
        (Γ(X, U₀) ⧸ RingHom.ker (Φ : Γ(X, U₀) →+* Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ U₀))) :=
      Ideal.quotientEquivAlgOfEq k hkerΦ.symm
    have e2 : (Γ(X, U₀) ⧸ RingHom.ker (Φ : Γ(X, U₀) →+* Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ U₀)))
        ≃ₐ[k] Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ U₀) :=
      Ideal.quotientKerAlgEquivOfSurjective hΦsurj
    exact Algebra.FormallySmooth.of_equiv (e1.trans e2).symm
  have : Algebra.FormallySmooth k
      ((Localization.AtPrime P.asIdeal) ⧸
        Ideal.map (algebraMap Γ(X, U₀) (Localization.AtPrime P.asIdeal))
          (Z.ideal ⟨U₀, hU₀⟩)) :=
    formallySmooth_quotient_map_of_isLocalization_consolidated161 k P.asIdeal.primeCompl
      (Localization.AtPrime P.asIdeal) (Z.ideal ⟨U₀, hU₀⟩) hfs
  obtain ⟨g, w, T, hgq, hwI, hspanmap, hcoords, hfe⟩ :=
    EtaleCoordinates.exists_away_ideal_eq_span_and_formallyEtale k (ULift.{u} (Fin m)) Γ(X, U₀)
      (Z.ideal ⟨U₀, hU₀⟩) P.asIdeal (Localization.AtPrime P.asIdeal) hIq
  have hxU : x ∈ X.basicOpen g := mem_basicOpen_of_notMem_primeIdealOf hU₀ hxU₀ g hgq
  let _ : Algebra k Γ(X, X.basicOpen g) := sectionsAlgebra k p (X.basicOpen g)
  let _ : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) (Localization.Away g) :=
    RingHom.toAlgebra (MvPolynomial.eval₂Hom
      ((algebraMap Γ(X, U₀) (Localization.Away g)).comp (algebraMap k Γ(X, U₀)))
      (fun j : ULift.{u} (Fin m) => algebraMap Γ(X, U₀) (Localization.Away g) (w j)))
  have : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) (Localization.Away g) := hfe
  let _ : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, X.basicOpen g) :=
    RingHom.toAlgebra (MvPolynomial.eval₂Hom
      ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀)))
      (fun j : ULift.{u} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j)))
  have : IsLocalization.Away g Γ(X, X.basicOpen g) := hU₀.isLocalization_basicOpen g
  let e : Localization.Away g ≃ₐ[Γ(X, U₀)] Γ(X, X.basicOpen g) :=
    IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(X, X.basicOpen g)
  have hcomm : (e.toAlgHom.toRingHom).comp
      (MvPolynomial.eval₂Hom
        ((algebraMap Γ(X, U₀) (Localization.Away g)).comp (algebraMap k Γ(X, U₀)))
        (fun j : ULift.{u} (Fin m) => algebraMap Γ(X, U₀) (Localization.Away g) (w j)))
      = MvPolynomial.eval₂Hom
        ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀)))
        (fun j : ULift.{u} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact e.commutes _
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact e.commutes _
  let E : Localization.Away g ≃ₐ[MvPolynomial (ULift.{u} (Fin m)) k] Γ(X, X.basicOpen g) :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv)
      (fun z => congrArg
        (fun φ : MvPolynomial (ULift.{u} (Fin m)) k →+* Γ(X, X.basicOpen g) => φ z) hcomm)
  have : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, X.basicOpen g) :=
    Algebra.FormallyEtale.of_equiv E
  have : Algebra.FiniteType k Γ(X, X.basicOpen g) :=
    finiteType_sections k p ⟨X.basicOpen g, hU₀.basicOpen g⟩
      (algebraMap_sectionsAlgebra k p (X.basicOpen g))
  have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, X.basicOpen g) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    have h1 : algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, X.basicOpen g)
        (algebraMap k (MvPolynomial (ULift.{u} (Fin m)) k) a)
        = algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (algebraMap k Γ(X, U₀) a) := by
      rw [MvPolynomial.algebraMap_eq]
      exact MvPolynomial.eval₂Hom_C _ _ a
    rw [h1]
    exact (sectionsAlgebraMap_restrict_apply k p (X.basicOpen_le g) a).symm
  have : Algebra.FiniteType (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, X.basicOpen g) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k
      (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, X.basicOpen g)
  have : Algebra.FinitePresentation (MvPolynomial (ULift.{u} (Fin m)) k)
      Γ(X, X.basicOpen g) := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, X.basicOpen g) := by
    constructor <;> infer_instance
  have hC : ∀ a : k, (MvPolynomial.eval₂Hom
      ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀)))
      (fun j : ULift.{u} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j)))
        (MvPolynomial.C a) = sectionsAlgebraMap k p (X.basicOpen g) a := by
    intro a
    rw [MvPolynomial.eval₂Hom_C]
    exact sectionsAlgebraMap_restrict_apply k p (X.basicOpen_le g) a
  have hX : ∀ i : ULift.{u} (Fin m), (MvPolynomial.eval₂Hom
      ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀)))
      (fun j : ULift.{u} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j)))
        (MvPolynomial.X i) = algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w i) :=
    fun i => MvPolynomial.eval₂Hom_X' _ _ i
  have hf : (MvPolynomial.eval₂Hom
      ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀)))
      (fun j : ULift.{u} (Fin m) =>
        algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j))).Etale :=
    ‹Algebra.Etale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, X.basicOpen g)›
  obtain ⟨c', hc'⟩ := exists_etaleChart_coord_eq p (hU₀.basicOpen g)
    (fun i : ULift.{u} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w i))
    (MvPolynomial.eval₂Hom
      ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀)))
      (fun j : ULift.{u} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j)))
    hC hX hf
  refine ⟨X.basicOpen g, hU₀.basicOpen g, m, c', T.image ULift.down, hxU, ?_⟩
  have hmap : Ideal.map (algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)) (Z.ideal ⟨U₀, hU₀⟩)
      = Z.ideal ⟨X.basicOpen g, hU₀.basicOpen g⟩ := Z.map_ideal_basicOpen ⟨U₀, hU₀⟩ g
  have htrans : Ideal.map (algebraMap Γ(X, U₀) Γ(X, X.basicOpen g))
        (Ideal.span (w '' (↑T : Set (ULift.{u} (Fin m)))))
      = Ideal.map (algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)) (Z.ideal ⟨U₀, hU₀⟩) := by
    rw [map_algebraMap_eq_map_map_of_algEquiv_consolidated161 e, map_algebraMap_eq_map_map_of_algEquiv_consolidated161 e, hspanmap]
  have hSset : ((T.image ULift.down : Finset (Fin m)) : Set (Fin m))
      = ULift.down '' (↑T : Set (ULift.{u} (Fin m))) := Finset.coe_image
  have himg : (fun i : ULift.{u} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w i))
      = c'.coord ∘ ULift.down := by
    funext i
    show algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w i) = c'.coord i.down
    rw [hc' i.down]
  rw [← hmap, ← htrans, Ideal.map_span]
  refine congrArg Ideal.span ?_
  rw [Set.image_image, hSset, ← Set.image_comp]
  exact congrArg (fun h : ULift.{u} (Fin m) → Γ(X, X.basicOpen g) =>
    h '' (↑T : Set (ULift.{u} (Fin m)))) himg

theorem exists_chart_restrictIdeal_eq_coordIdeal (x : X)
    (hx : x ∈ Z.support) :
    ∃ (U : X.Opens) (m : ℕ) (c : EtaleChart p U m) (S : Finset (Fin m)),
      x ∈ U ∧ IsAffineOpen U ∧ restrictIdeal Z U = c.coordIdeal S := by
  obtain ⟨U, hU, m, c, S, hxU, hspan⟩ := exists_chart_ideal_eq_span_coord p Z x hx
  exact ⟨U, m, c, S, hxU, hU, restrictIdeal_eq_coordIdeal_of_ideal_eq_span hU c Z S hspan⟩

theorem hasStrictNormalCrossingsWith_nil_of_smooth :
    HasStrictNormalCrossingsWith p Z [] := by
  unfold HasStrictNormalCrossingsWith
  intro x hx
  obtain ⟨U, m, c, S, hxU, hU, hres⟩ := exists_chart_restrictIdeal_eq_coordIdeal p Z x hx
  refine ⟨U, hxU, m, c, fun _ => none, S, ?_, ?_, ?_, hres⟩
  · intro i hi
    simp at hi
  · intro i hi
    simp at hi
  · intro i hi
    simp at hi


end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothHypersurfaceLocalCoordinates
section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

section

variable {P : Scheme.{u}}

section
variable {A B : Scheme.{u}} (f : A ⟶ B)

private theorem ker_ideal_eq_ker_appLE_consolidated162 [QuasiCompact f]
    (V : B.affineOpens) :
    f.ker.ideal V = RingHom.ker (f.appLE (V : B.Opens) (f ⁻¹ᵁ (V : B.Opens)) le_rfl).hom := by
  simp only [Scheme.Hom.appLE_eq_app]
  simp

private theorem ker_appLE_congr_consolidated162 (W : B.Opens)
    {V₁ V₂ : A.Opens} (h : V₁ = V₂) (e₁ : V₁ ≤ f ⁻¹ᵁ W) (e₂ : V₂ ≤ f ⁻¹ᵁ W) :
    RingHom.ker (f.appLE W V₁ e₁).hom = RingHom.ker (f.appLE W V₂ e₂).hom := by
  subst h
  rfl


end

theorem ker_comp_subschemeι_ideal_eq_comap (H : P.IdealSheafData) (Z : H.subscheme.IdealSheafData)
    {U : P.Opens} (hU : IsAffineOpen U) :
    (Z.subschemeι ≫ H.subschemeι).ker.ideal ⟨U, hU⟩ =
      Ideal.comap (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom
        (Z.ideal ⟨H.subschemeι ⁻¹ᵁ U, isAffineOpen_preimage_subschemeι H hU⟩) := by
  have hqcZ : QuasiCompact Z.subschemeι := inferInstance
  have hqcf : QuasiCompact (Z.subschemeι ≫ H.subschemeι) := inferInstance
  have hopen : (Z.subschemeι ≫ H.subschemeι) ⁻¹ᵁ U
      = Z.subschemeι ⁻¹ᵁ (H.subschemeι ⁻¹ᵁ U) :=
    Scheme.Hom.comp_preimage ..
  have hle : Z.subschemeι ⁻¹ᵁ (H.subschemeι ⁻¹ᵁ U)
      ≤ (Z.subschemeι ≫ H.subschemeι) ⁻¹ᵁ U := le_of_eq hopen.symm
  have h1 : (Z.subschemeι ≫ H.subschemeι).ker.ideal ⟨U, hU⟩ =
      RingHom.ker ((Z.subschemeι ≫ H.subschemeι).appLE U
        (Z.subschemeι ⁻¹ᵁ (H.subschemeι ⁻¹ᵁ U)) hle).hom :=
    (ker_ideal_eq_ker_appLE_consolidated162 (Z.subschemeι ≫ H.subschemeι) ⟨U, hU⟩).trans
      (ker_appLE_congr_consolidated162 (Z.subschemeι ≫ H.subschemeι) U hopen le_rfl hle)
  have h2 : Z.ideal ⟨H.subschemeι ⁻¹ᵁ U, isAffineOpen_preimage_subschemeι H hU⟩ =
      RingHom.ker (Z.subschemeι.appLE (H.subschemeι ⁻¹ᵁ U)
        (Z.subschemeι ⁻¹ᵁ (H.subschemeι ⁻¹ᵁ U)) le_rfl).hom :=
    (congrArg (fun I : H.subscheme.IdealSheafData =>
        I.ideal ⟨H.subschemeι ⁻¹ᵁ U, isAffineOpen_preimage_subschemeι H hU⟩)
      (Scheme.IdealSheafData.ker_subschemeι Z)).symm.trans
      (ker_ideal_eq_ker_appLE_consolidated162 Z.subschemeι
        ⟨H.subschemeι ⁻¹ᵁ U, isAffineOpen_preimage_subschemeι H hU⟩)
  have hcomp : H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl ≫
      Z.subschemeι.appLE (H.subschemeι ⁻¹ᵁ U)
        (Z.subschemeι ⁻¹ᵁ (H.subschemeι ⁻¹ᵁ U)) le_rfl
      = (Z.subschemeι ≫ H.subschemeι).appLE U
        (Z.subschemeι ⁻¹ᵁ (H.subschemeι ⁻¹ᵁ U)) hle := by
    simp only [Scheme.Hom.appLE_comp_appLE]
  rw [h1, h2, ← hcomp, CommRingCat.hom_comp]
  ext x
  simp only [RingHom.mem_ker, Ideal.mem_comap, RingHom.comp_apply]

private theorem comp_app_apply_consolidated162 {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (U : C.Opens) (x : Γ(C, U)) :
    ((f ≫ g).app U).hom x = (f.app (g ⁻¹ᵁ U)).hom ((g.app U).hom x) := rfl

private theorem subschemeι_app_apply_eq_zero_consolidated162 {P : Scheme.{u}} (H : P.IdealSheafData)
    (U : P.affineOpens) (x : Γ(P, U.1)) (hx : x ∈ H.ideal U) :
    (H.subschemeι.app U.1).hom x = 0 := by
  have hpt : (H.subschemeι.app U.1).hom x
      = (H.subschemeObjIso U).inv.hom (Ideal.Quotient.mk (H.ideal U) x) :=
    congrArg (fun g => CommRingCat.Hom.hom g x) (Scheme.IdealSheafData.subschemeι_app H U)
  rw [hpt, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

theorem le_ker_comp_subschemeι (H : P.IdealSheafData) (Z : H.subscheme.IdealSheafData) :
    H ≤ (Z.subschemeι ≫ H.subschemeι).ker := by
  simp only [Scheme.Hom.ker]
  refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr ?_
  intro U x hx
  simp only [RingHom.mem_ker]
  rw [comp_app_apply_consolidated162 Z.subschemeι H.subschemeι U.1 x,
    subschemeι_app_apply_eq_zero_consolidated162 H U x hx]
  exact map_zero _

variable {k : Type u} [Field k]

theorem ker_comp_subschemeι_ideal_eq_span_coord (p : P ⟶ Spec (CommRingCat.of k)) (H : P.IdealSheafData)
    (Z : H.subscheme.IdealSheafData) {U : P.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (c : EtaleChart p U n) (j₀ : Fin n) (S : Finset (Fin n))
    (hH : restrictIdeal H U = c.coordIdeal {j₀})
    (hZ : Z.ideal ⟨H.subschemeι ⁻¹ᵁ U, isAffineOpen_preimage_subschemeι H hU⟩ =
      Ideal.span
        ((fun j : Fin n =>
          (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom (c.coord j)) ''
            (S : Set (Fin n)))) :
    (Z.subschemeι ≫ H.subschemeι).ker.ideal ⟨U, hU⟩ =
      Ideal.span (c.coord '' ((insert j₀ S : Finset (Fin n)) : Set (Fin n))) := by
  classical
  have happ : H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl = H.subschemeι.app U := by
    rw [Scheme.Hom.appLE_eq_app]
  have hsurj : Function.Surjective (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom := by
    rw [happ]
    exact Scheme.IdealSheafData.subschemeι_app_surjective H ⟨U, hU⟩
  have hcomap : Ideal.comap (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom ⊥
      = H.ideal ⟨U, hU⟩ := by
    rw [happ, ← RingHom.ker_eq_comap_bot]
    exact Scheme.IdealSheafData.ker_subschemeι_app H ⟨U, hU⟩
  have hHspan : H.ideal ⟨U, hU⟩ = Ideal.span {c.coord j₀} := by
    rw [c.ideal_eq_span_coord hU H {j₀} hH, Finset.coe_singleton, Set.image_singleton]
  have key := ker_comp_subschemeι_ideal_eq_comap H Z hU
  rw [hZ] at key
  have himg : ((fun j : Fin n =>
        (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom (c.coord j)) ''
          (S : Set (Fin n)))
      = (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom ''
          (c.coord '' (S : Set (Fin n))) :=
    (Set.image_image _ _ _).symm
  have hmap : Ideal.map (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom
        (Ideal.span (c.coord '' (S : Set (Fin n))))
      = Ideal.span ((H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom ''
          (c.coord '' (S : Set (Fin n)))) :=
    Ideal.map_span _ _
  rw [key, himg, ← hmap, Ideal.comap_map_of_surjective _ hsurj, hcomap, hHspan,
    Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert]
  exact le_antisymm (sup_le le_sup_right le_sup_left) (sup_le le_sup_right le_sup_left)

end

section

variable {X : Scheme.{u}} {k : Type u} [Field k]

theorem etaleChart_numCoords_eq (p : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) {m m' : ℕ} (c : EtaleChart p U m) (c' : EtaleChart p U m') : m = m' := by
  let instk : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra
  let instc' : Algebra (MvPolynomial (ULift.{u} (Fin m')) k) Γ(X, U) := c'.algebra
  have instt : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) :=
    c.isScalarTower
  have instt' : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m')) k) Γ(X, U) :=
    c'.isScalarTower
  have instfe : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) :=
    c.algebra_formallyEtale hU
  have instfe' : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m')) k) Γ(X, U) :=
    c'.algebra_formallyEtale hU
  have instnt : Nontrivial Γ(X, U) :=
    RingHom.domain_nontrivial (X.presheaf.germ U x hx).hom
  have h1 : Module.finrank Γ(X, U) (KaehlerDifferential k Γ(X, U))
      = Fintype.card (ULift.{u} (Fin m)) :=
    Module.finrank_eq_card_basis (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m)) Γ(X, U))
  have h2 : Module.finrank Γ(X, U) (KaehlerDifferential k Γ(X, U))
      = Fintype.card (ULift.{u} (Fin m')) :=
    Module.finrank_eq_card_basis (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m')) Γ(X, U))
  have h3 : Fintype.card (ULift.{u} (Fin m)) = Fintype.card (ULift.{u} (Fin m')) :=
    h1.symm.trans h2
  simpa using h3

end

section

variable {P : Scheme.{u}} {k : Type u} [Field k]

theorem etaleChart_numCoords_add_one_of_hypersurface (p : P ⟶ Spec (CommRingCat.of k))
    (H : P.IdealSheafData)
    [LocallyOfFiniteType (H.subschemeι ≫ p)]
    {U : P.Opens} (hU : IsAffineOpen U) {n : ℕ} (c : EtaleChart p U n) (j₁ : Fin n)
    (hH : restrictIdeal H U = c.coordIdeal {j₁})
    {V : H.subscheme.Opens} (_hV : IsAffineOpen V) {m' : ℕ}
    (c' : EtaleChart (H.subschemeι ≫ p) V m')
    (y : H.subscheme) (hyU : y ∈ H.subschemeι ⁻¹ᵁ U) (hyV : y ∈ V) :
    m' + 1 = n := by
  have hymem : y ∈ (H.subschemeι ⁻¹ᵁ U) ⊓ V := ⟨hyU, hyV⟩
  obtain ⟨W, hWmem, hyW, hWle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp H.subscheme.isBasis_affineOpens hymem
  have hW : IsAffineOpen W := hWmem
  have hle1 : W ≤ H.subschemeι ⁻¹ᵁ U := le_trans hWle inf_le_left
  have hle2 : W ≤ V := le_trans hWle inf_le_right
  have key := etaleChart_numCoords_eq (H.subschemeι ≫ p) hW y hyW
    ((c.restrictToSubscheme hU H {j₁} hH).restrict hle1) (c'.restrict hle2)
  have hcard : ({j₁} : Finset (Fin n)).card = 1 := Finset.card_singleton j₁
  have hlt : (j₁ : ℕ) < n := j₁.isLt
  omega

def HasLocalCoordsOnSmoothHypersurface (p : P ⟶ Spec (CommRingCat.of k)) (H : P.IdealSheafData)
    (N : List P.IdealSheafData) (Z : H.subscheme.IdealSheafData) : Prop :=
  ∀ x ∈ (Z.subschemeι ≫ H.subschemeι).ker.support,
    ∃ (U : P.Opens) (hU : IsAffineOpen U) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n)
      (j₀ : Fin n) (lab : ℕ → Option (Fin n)) (S : Finset (Fin n)),
      restrictIdeal H U = c.coordIdeal {j₀} ∧
      (∀ i, ∀ hi : i < N.length, lab i = none → restrictIdeal (N[i]'hi) U = ⊤) ∧
      (∀ i, ∀ hi : i < N.length, ∀ j : Fin n, lab i = some j →
        restrictIdeal (N[i]'hi) U = c.coordIdeal {j}) ∧
      (∀ i i' : ℕ, i < N.length → i' < N.length → ∀ j : Fin n,
        lab i = some j → lab i' = some j → i = i') ∧
      Z.ideal ⟨H.subschemeι ⁻¹ᵁ U, isAffineOpen_preimage_subschemeι H hU⟩ =
        Ideal.span
          ((fun j : Fin n =>
            (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom (c.coord j)) ''
              (S : Set (Fin n)))

private theorem comp_presheaf_map_comp_map_consolidated162 {X₁ : Scheme.{u}} {R : CommRingCat.{u}}
    {A B C : (X₁.Opens)ᵒᵖ} (h : R ⟶ X₁.presheaf.obj A) (g₁ : A ⟶ B) (g₂ : B ⟶ C) (g₃ : A ⟶ C) :
    (h ≫ X₁.presheaf.map g₁) ≫ X₁.presheaf.map g₂ = h ≫ X₁.presheaf.map g₃ := by
  rw [Category.assoc, ← Functor.map_comp, X₁.presheaf_map_eq_of_parallel (g₁ ≫ g₂) g₃]

private theorem appLE_eq_appLE_comp_presheaf_map_consolidated162 {X₁ Y₁ : Scheme.{u}} (f : X₁ ⟶ Y₁) (U : Y₁.Opens)
    {A B : X₁.Opens} (e : A ≤ f ⁻¹ᵁ U) (e' : B ≤ f ⁻¹ᵁ U) (hAB : A ≤ B) :
    f.appLE U A e = f.appLE U B e' ≫ X₁.presheaf.map (homOfLE hAB).op := by
  have h1 : f.appLE U A e = f.app U ≫ X₁.presheaf.map (homOfLE e).op := rfl
  have h2 : f.appLE U B e' = f.app U ≫ X₁.presheaf.map (homOfLE e').op := rfl
  rw [h1, h2]
  exact (comp_presheaf_map_comp_map_consolidated162 (f.app U) (homOfLE e').op (homOfLE hAB).op (homOfLE e).op).symm

private theorem ι_appLE_self_top_eq_topIso_inv_consolidated162 {X₁ : Scheme.{u}} (V : X₁.Opens)
    (e : (⊤ : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ e = V.topIso.inv := by
  simp
  exact X₁.presheaf_map_eq_of_parallel _ _

private theorem ι_appLE_apply_topIso_hom_consolidated162 {X₁ Y₁ : Scheme.{u}} (V : X₁.Opens)
    (g : V.toScheme ⟶ Y₁) {W : V.toScheme.Opens} (e1 : W ≤ V.ι ⁻¹ᵁ V)
    (e2 : W ≤ g ⁻¹ᵁ (⊤ : Y₁.Opens)) (x : Γ(Y₁, ⊤)) :
    (V.ι.appLE V W e1).hom (V.topIso.hom.hom (g.appTop.hom x))
      = (g.appLE ⊤ W e2).hom x := by
  have htop : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by
    intro y _
    exact y.2
  have ha : V.ι.appLE V W e1
      = V.topIso.inv ≫ V.toScheme.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op := by
    rw [appLE_eq_appLE_comp_presheaf_map_consolidated162 V.ι V e1 htop le_top, ι_appLE_self_top_eq_topIso_inv_consolidated162 V htop]
  have hb : g.appLE (⊤ : Y₁.Opens) W e2
      = g.appTop ≫ V.toScheme.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op := by
    have h1 : g.appLE (⊤ : Y₁.Opens) W e2
        = g.appTop ≫ V.toScheme.presheaf.map (homOfLE e2).op := rfl
    rw [h1]
    exact congrArg (fun z => g.appTop ≫ z) (V.toScheme.presheaf_map_eq_of_parallel _ _)
  rw [ha, hb]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [Iso.hom_inv_id_apply]

private theorem ofIdealTop_ideal_top_consolidated162 {Y : Scheme.{u}} [IsAffine Y] (J : Ideal Γ(Y, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop J).ideal ⟨⊤, isAffineOpen_top Y⟩ = J := by
  simp

section
variable {X₁ : Scheme.{u}} {K : Type u} [Field K] {q : X₁ ⟶ Spec (CommRingCat.of K)} {U : X₁.Opens} {m : ℕ} (c : EtaleChart q U m)

private theorem ι_appLE_coord_consolidated162 {W : U.toScheme.Opens} (e1 : W ≤ U.ι ⁻¹ᵁ U)
    (e2 : W ≤ c.map ⁻¹ᵁ (⊤ : (affineSpaceFin K m).Opens)) (j : Fin m) :
    (U.ι.appLE U W e1).hom (c.coord j)
      = (c.map.appLE ⊤ W e2).hom
          (AffineSpace.coord (Spec (CommRingCat.of K)) (ULift.up j : ULift.{u} (Fin m))) := by
  rw [EtaleChart.coord_def]
  exact ι_appLE_apply_topIso_hom_consolidated162 U c.map e1 e2 _

private theorem restrictIdeal_eq_coordIdeal_of_isAffineOpen_ideal_eq_span_consolidated162 (hU : IsAffineOpen U) (I : X₁.IdealSheafData) (S : Finset (Fin m))
    (h : I.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m)))) :
    restrictIdeal I U = c.coordIdeal S := by
  have hAaff : IsAffine (affineSpaceFin K m) := inferInstance
  have hcoord : (coordSubspaceIdeal K m S).ideal ⟨⊤, isAffineOpen_top (affineSpaceFin K m)⟩
      = Ideal.span ((fun i : Fin m =>
          AffineSpace.coord (Spec (CommRingCat.of K)) (ULift.up i)) '' (S : Set (Fin m))) := by
    rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord]
    exact ofIdealTop_ideal_top_consolidated162 _
  refine Scheme.IdealSheafData.ext (funext ?_)
  intro W
  have htop : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := by
    intro y _
    exact y.2
  have eW : (W.1 : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := le_trans le_top htop
  have eW' : (W.1 : U.toScheme.Opens) ≤ c.map ⁻¹ᵁ (⊤ : (affineSpaceFin K m).Opens) := by
    intro y _
    trivial
  show (I.comap U.ι).ideal W = ((coordSubspaceIdeal K m S).comap c.map).ideal W
  rw [I.comap_ideal_eq_map_appLE U.ι ⟨U, hU⟩ W eW,
    (coordSubspaceIdeal K m S).comap_ideal_eq_map_appLE c.map
      ⟨⊤, isAffineOpen_top (affineSpaceFin K m)⟩ W eW',
    h, hcoord, Ideal.map_span, Ideal.map_span, ← Set.image_comp, ← Set.image_comp]
  refine congrArg Ideal.span (Set.image_congr fun j _ => ?_)
  exact ι_appLE_coord_consolidated162 c eW eW' j


end

section
variable {Y : Scheme.{u}} (I : Y.IdealSheafData)

private theorem ideal_ne_top_of_mem_support_consolidated162 {V : Y.Opens}
    (hV : IsAffineOpen V) {x : Y} (hxV : x ∈ V) (hx : x ∈ I.support) :
    I.ideal ⟨V, hV⟩ ≠ ⊤ := by
  obtain ⟨y, hy⟩ : ∃ y : I.subscheme, I.subschemeι.base y = x := by
    have hxs : x ∈ (I.support : Set Y) := hx
    have hxr : x ∈ Set.range I.subschemeι.base := by simpa using hxs
    exact hxr
  have hyV : y ∈ I.subschemeι ⁻¹ᵁ V := by
    show I.subschemeι.base y ∈ V
    rw [hy]
    exact hxV
  have hnt : Nontrivial Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V) :=
    RingHom.domain_nontrivial (I.subscheme.presheaf.germ (I.subschemeι ⁻¹ᵁ V) y hyV).hom
  intro htop
  have hker : RingHom.ker (I.subschemeι.app V).hom = I.ideal ⟨V, hV⟩ :=
    Scheme.IdealSheafData.ker_subschemeι_app I ⟨V, hV⟩
  have hmem1 : (1 : Γ(Y, V)) ∈ RingHom.ker (I.subschemeι.app V).hom := by
    rw [hker, htop]
    exact Submodule.mem_top
  have hzero : (1 : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V)) = 0 := by
    have h' := RingHom.mem_ker.mp hmem1
    rwa [map_one] at h'
  exact one_ne_zero hzero

private theorem ideal_eq_top_of_restrictIdeal_eq_top_consolidated162 {V : Y.Opens} (hV : IsAffineOpen V) (h : restrictIdeal I V = ⊤) :
    I.ideal ⟨V, hV⟩ = ⊤ := by
  have hVaff : IsAffine V.toScheme := hV
  have htop : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by
    intro y _
    exact y.2
  have key := I.comap_ideal_eq_map_appLE V.ι ⟨V, hV⟩ ⟨⊤, isAffineOpen_top V.toScheme⟩ htop
  rw [ι_appLE_self_top_eq_topIso_inv_consolidated162 V htop] at key
  have h' : I.comap V.ι = ⊤ := h
  rw [h'] at key
  have h0 : ((⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩) = ⊤ := by
    simp
  rw [h0] at key
  rw [Ideal.eq_top_iff_one]
  have hone : (1 : Γ(V.toScheme, ⊤)) ∈ Ideal.map V.topIso.inv.hom (I.ideal ⟨V, hV⟩) := by
    rw [← key]
    exact Submodule.mem_top
  have hsurj : Function.Surjective V.topIso.inv.hom :=
    V.topIso.symm.commRingCatIsoToRingEquiv.surjective
  have hinj : Function.Injective V.topIso.inv.hom :=
    V.topIso.symm.commRingCatIsoToRingEquiv.injective
  obtain ⟨a, haI, hfa⟩ :=
    (Ideal.mem_map_iff_of_surjective _ hsurj).mp hone
  have ha1 : a = 1 := hinj (by rw [hfa, map_one])
  exact ha1 ▸ haI

private theorem restrictIdeal_eq_top_of_le_of_eq_top_consolidated162 {U V : Y.Opens}
    (hVU : V ≤ U) (h : restrictIdeal I U = ⊤) : restrictIdeal I V = ⊤ := by
  have e1 : I.comap V.ι = (I.comap U.ι).comap (Y.homOfLE hVU) := by
    rw [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]
  have h' : I.comap U.ι = ⊤ := h
  show I.comap V.ι = ⊤
  rw [e1, h']
  simp


end

private theorem restrictIdeal_eq_coordIdeal_restrict_consolidated162 {X₁ : Scheme.{u}} {K : Type u} [Field K]
    {q : X₁ ⟶ Spec (CommRingCat.of K)} {U V : X₁.Opens} (hVU : V ≤ U) {m : ℕ}
    (c : EtaleChart q U m) (I : X₁.IdealSheafData) (S : Finset (Fin m))
    (h : restrictIdeal I U = c.coordIdeal S) :
    restrictIdeal I V = (c.restrict hVU).coordIdeal S := by
  have h' : I.comap U.ι = (coordSubspaceIdeal K m S).comap c.map := by
    rw [← restrictIdeal_eq_comap_ι, h, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.restrict_map,
    Scheme.IdealSheafData.comap_comp, ← h', ← Scheme.IdealSheafData.comap_comp,
    Scheme.homOfLE_ι]

section
variable {σ : Type u} {K : Type u} [Field K] {j s : σ} (hjs : j ≠ s)
include hjs

private theorem mem_span_X_of_mul_X_mem_consolidated162 (r : MvPolynomial σ K)
    (hr : MvPolynomial.X s * r ∈ Ideal.span {(MvPolynomial.X j : MvPolynomial σ K)}) :
    r ∈ Ideal.span {(MvPolynomial.X j : MvPolynomial σ K)} := by
  classical
  obtain ⟨ψ, hψC, hψXj, hψXi⟩ : ∃ ψ : MvPolynomial σ K →+* MvPolynomial σ K,
      (∀ a : K, ψ (MvPolynomial.C a) = MvPolynomial.C a) ∧
        ψ (MvPolynomial.X j) = 0 ∧
        ∀ i : σ, i ≠ j → ψ (MvPolynomial.X i) = MvPolynomial.X i := by
    refine ⟨MvPolynomial.eval₂Hom (MvPolynomial.C : K →+* MvPolynomial σ K)
        (fun i : σ => if i = j then (0 : MvPolynomial σ K) else MvPolynomial.X i), ?_, ?_, ?_⟩
    · intro a
      simp
    · simp
    · intro i hi
      simp [hi]
  have hXjmem : (MvPolynomial.X j : MvPolynomial σ K)
      ∈ Ideal.span {(MvPolynomial.X j : MvPolynomial σ K)} := Ideal.mem_span_singleton_self _
  have key : (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ K)})).comp ψ
      = Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ K)}) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, hψC]
    · intro i
      rw [RingHom.comp_apply]
      by_cases h : i = j
      · subst h
        rw [hψXj, map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr hXjmem).symm
      · rw [hψXi i h]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hr
  have h0 : ψ (MvPolynomial.X s * r) = 0 := by
    rw [ht, map_mul, hψXj, zero_mul]
  rw [map_mul, hψXi s (Ne.symm hjs)] at h0
  have hXs : (MvPolynomial.X s : MvPolynomial σ K) ≠ 0 := MvPolynomial.X_ne_zero _
  have hψr : ψ r = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hXs
    · exact h
  have h3 := DFunLike.congr_fun key r
  rw [RingHom.comp_apply, hψr, map_zero] at h3
  exact Ideal.Quotient.eq_zero_iff_mem.mp h3.symm

private theorem quotient_span_X_mul_X_cancel_consolidated162 (a b : MvPolynomial σ K ⧸ Ideal.span {(MvPolynomial.X j : MvPolynomial σ K)})
    (h : (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ K)}))
            (MvPolynomial.X s) * a
        = (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ K)}))
            (MvPolynomial.X s) * b) : a = b := by
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub] at h
  exact Ideal.Quotient.eq.mpr (mem_span_X_of_mul_X_mem_consolidated162 hjs (a' - b') h)


end

private theorem mem_map_of_mul_mem_of_etale_consolidated162 {Pr A : Type u} [CommRing Pr] [CommRing A]
    {f : Pr →+* A} (hf : f.Etale) (I : Ideal Pr) (w : Pr)
    (hw : ∀ a b : Pr ⧸ I,
      (Ideal.Quotient.mk I) w * a = (Ideal.Quotient.mk I) w * b → a = b)
    (x : A) (hx : f w * x ∈ Ideal.map f I) : x ∈ Ideal.map f I := by
  have hg : (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).Etale :=
    etale_quotientMap hf I
  have hy : (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map)
        ((Ideal.Quotient.mk I) w) * (Ideal.Quotient.mk (Ideal.map f I)) x = 0 := by
    rw [Ideal.quotientMap_mk, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  let algInst : Algebra (Pr ⧸ I) (A ⧸ Ideal.map f I) :=
    (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).toAlgebra
  have instEt : Algebra.Etale (Pr ⧸ I) (A ⧸ Ideal.map f I) := hg
  have instFlat : Module.Flat (Pr ⧸ I) (A ⧸ Ideal.map f I) := inferInstance
  have hreg : IsSMulRegular (Pr ⧸ I) ((Ideal.Quotient.mk I) w) := fun a b h => hw a b h
  have hregA : IsSMulRegular (A ⧸ Ideal.map f I) ((Ideal.Quotient.mk I) w) := hreg.of_flat
  have hsmul : (Ideal.Quotient.mk I) w • (Ideal.Quotient.mk (Ideal.map f I)) x
      = (Ideal.Quotient.mk I) w • (0 : A ⧸ Ideal.map f I) := by
    rw [smul_zero]
    exact hy
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hregA hsmul)

private theorem span_coord_eq_top_of_mem_span_consolidated162 {X₁ : Scheme.{u}} {K : Type u} [Field K]
    {q : X₁ ⟶ Spec (CommRingCat.of K)} {V : X₁.Opens} (hV : IsAffineOpen V) {m : ℕ}
    (c : EtaleChart q V m) {j s : Fin m} (hjs : j ≠ s)
    (hmem : c.coord s ∈ Ideal.span {c.coord j}) :
    Ideal.span {c.coord j} = (⊤ : Ideal Γ(X₁, V)) := by
  classical
  have hmapspan : Ideal.map c.coordRingHom
      (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) K)})
      = Ideal.span {c.coord j} := by
    rw [Ideal.map_span, Set.image_singleton, c.coordRingHom_X]
  have hju : (ULift.up j : ULift.{u} (Fin m)) ≠ ULift.up s := by
    intro h
    exact hjs (congrArg ULift.down h)
  have hu : ∀ a b : MvPolynomial (ULift.{u} (Fin m)) K ⧸
        Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) K)},
      (Ideal.Quotient.mk
          (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) K)}))
          (MvPolynomial.X (ULift.up s)) * a
        = (Ideal.Quotient.mk
          (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) K)}))
          (MvPolynomial.X (ULift.up s)) * b → a = b :=
    fun a b h => quotient_span_X_mul_X_cancel_consolidated162 hju a b h
  have hx' : c.coordRingHom (MvPolynomial.X (ULift.up s)) * 1
      ∈ Ideal.map c.coordRingHom
        (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) K)}) := by
    rw [hmapspan, c.coordRingHom_X, mul_one]
    exact hmem
  have hfin := mem_map_of_mul_mem_of_etale_consolidated162 (c.coordRingHom_etale hV)
    (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) K)})
    (MvPolynomial.X (ULift.up s)) hu 1 hx'
  rw [hmapspan] at hfin
  exact (Ideal.eq_top_iff_one _).mpr hfin

theorem hasStrictNormalCrossingsWith_ker_cons_of_hasLocalCoordsOnSmoothHypersurface [CharZero k] (p : P ⟶ Spec (CommRingCat.of k))
    [Smooth p] (H : P.IdealSheafData) (N : List P.IdealSheafData)
    (Z : H.subscheme.IdealSheafData)
    (hN : InStrictNormalCrossingPosition p (H :: N))
    (_hZ : HasStrictNormalCrossingsWith (H.subschemeι ≫ p) Z (N.map fun D => D.comap H.subschemeι))
    (hdata : HasLocalCoordsOnSmoothHypersurface p H N Z) :
    HasStrictNormalCrossingsWith p (Z.subschemeι ≫ H.subschemeι).ker (H :: N) := by
  classical
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hU, hxU, n, c, j₀, lab, S, h1, h2, h3, h4, h5⟩ := hdata x hx
  obtain ⟨-, hNpos⟩ := (inStrictNormalCrossingPosition_iff p (H :: N)).mp hN
  have hclash : ∀ i : ℕ, i < N.length → lab i ≠ some j₀ := by
    intro i hi hlabi
    obtain ⟨U', hxU', m', c', a', hinj', hnone', hsome'⟩ := (hNpos x).exists_etaleChart
    obtain ⟨V, hVb, hxV, hVle⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp P.isBasis_affineOpens
        (show x ∈ U ⊓ U' from ⟨hxU, hxU'⟩)
    have hV : IsAffineOpen V := hVb
    have hVU : V ≤ U := le_trans hVle inf_le_left
    have hVU' : V ≤ U' := le_trans hVle inf_le_right
    have hEqU : restrictIdeal (N[i]'hi) U = restrictIdeal H U := by
      rw [h3 i hi j₀ hlabi, h1]
    have hEqV : restrictIdeal (N[i]'hi) V = restrictIdeal H V :=
      restrictIdeal_eq_of_le_of_eq hVU hEqU
    have hKne : (Z.subschemeι ≫ H.subschemeι).ker.ideal ⟨V, hV⟩ ≠ ⊤ :=
      ideal_ne_top_of_mem_support_consolidated162 _ hV hxV hx
    have hproper : H.ideal ⟨V, hV⟩ ≠ ⊤ := by
      intro htop
      have hle := le_ker_comp_subschemeι H Z ⟨V, hV⟩
      rw [htop] at hle
      exact hKne (top_le_iff.mp hle)
    have hlen0 : 0 < (H :: N).length := by simp
    have hleni : i + 1 < (H :: N).length := by simpa using hi
    cases hop : a' 0 with
    | none =>
      have hHtop : restrictIdeal H U' = ⊤ := by simpa using hnone' 0 hlen0 hop
      exact hproper (ideal_eq_top_of_restrictIdeal_eq_top_consolidated162 H hV
        (restrictIdeal_eq_top_of_le_of_eq_top_consolidated162 H hVU' hHtop))
    | some t₀ =>
      cases hop1 : a' (i + 1) with
      | none =>
        have hNtop : restrictIdeal (N[i]'hi) U' = ⊤ := by
          simpa using hnone' (i + 1) hleni hop1
        have hVtop : restrictIdeal (N[i]'hi) V = ⊤ := restrictIdeal_eq_top_of_le_of_eq_top_consolidated162 _ hVU' hNtop
        rw [hEqV] at hVtop
        exact hproper (ideal_eq_top_of_restrictIdeal_eq_top_consolidated162 H hV hVtop)
      | some t₁ =>
        have hne : t₀ ≠ t₁ := by
          intro hteq
          have h00 := hinj' 0 hlen0 (i + 1) hleni t₀ hop (by rw [hop1, hteq])
          exact absurd h00 (by omega)
        have hHU' : restrictIdeal H U' = c'.coordIdeal {t₀} := by
          simpa using hsome' 0 hlen0 t₀ hop
        have hNU' : restrictIdeal (N[i]'hi) U' = c'.coordIdeal {t₁} := by
          simpa using hsome' (i + 1) hleni t₁ hop1
        have hHV1 : restrictIdeal H V = (c'.restrict hVU').coordIdeal {t₀} :=
          restrictIdeal_eq_coordIdeal_restrict_consolidated162 hVU' c' H {t₀} hHU'
        have hHV2 : restrictIdeal H V = (c'.restrict hVU').coordIdeal {t₁} := by
          rw [← hEqV]
          exact restrictIdeal_eq_coordIdeal_restrict_consolidated162 hVU' c' (N[i]'hi) {t₁} hNU'
        have hA : H.ideal ⟨V, hV⟩ = Ideal.span {(c'.restrict hVU').coord t₀} := by
          simpa using (c'.restrict hVU').ideal_eq_span_coord hV H {t₀} hHV1
        have hB : H.ideal ⟨V, hV⟩ = Ideal.span {(c'.restrict hVU').coord t₁} := by
          simpa using (c'.restrict hVU').ideal_eq_span_coord hV H {t₁} hHV2
        have hmem : (c'.restrict hVU').coord t₁
            ∈ Ideal.span {(c'.restrict hVU').coord t₀} := by
          rw [← hA, hB]
          exact Ideal.mem_span_singleton_self _
        exact hproper (hA.trans (span_coord_eq_top_of_mem_span_consolidated162 hV (c'.restrict hVU') hne hmem))
  obtain ⟨a, ha0, has⟩ : ∃ a : ℕ → Option (Fin n), a 0 = some j₀ ∧ ∀ i, a (i + 1) = lab i :=
    ⟨fun i => if i = 0 then some j₀ else lab (i - 1), if_pos rfl, fun i => by
      show (if i + 1 = 0 then some j₀ else lab (i + 1 - 1)) = lab i
      rw [if_neg (by omega : ¬ (i + 1 = 0)), Nat.add_sub_cancel]⟩
  refine ⟨U, hxU, n, c, a, insert j₀ S, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj t hti htj
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        have heq : j₀ = t := by
          rw [ha0] at hti
          exact Option.some.inj hti
        rw [has j'] at htj
        rw [← heq] at htj
        exact absurd htj (hclash j' (by simpa using hj))
    | succ i' =>
      cases j with
      | zero =>
        have heq : j₀ = t := by
          rw [ha0] at htj
          exact Option.some.inj htj
        rw [has i'] at hti
        rw [← heq] at hti
        exact absurd hti (hclash i' (by simpa using hi))
      | succ j' =>
        rw [has i'] at hti
        rw [has j'] at htj
        have hij := h4 i' j' (by simpa using hi) (by simpa using hj) t hti htj
        omega
  · intro i hi hn
    cases i with
    | zero =>
      rw [ha0] at hn
      exact absurd hn (by simp)
    | succ i' =>
      rw [has i'] at hn
      have hi' : i' < N.length := by simpa using hi
      simpa using h2 i' hi' hn
  · intro i hi t ht
    cases i with
    | zero =>
      have heq : j₀ = t := by
        rw [ha0] at ht
        exact Option.some.inj ht
      rw [← heq]
      simpa using h1
    | succ i' =>
      rw [has i'] at ht
      have hi' : i' < N.length := by simpa using hi
      simpa using h3 i' hi' t ht
  · exact restrictIdeal_eq_coordIdeal_of_isAffineOpen_ideal_eq_span_consolidated162 c hU _ (insert j₀ S)
      (ker_comp_subschemeι_ideal_eq_span_coord p H Z hU c j₀ S h1 h5)

end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsOpenImmersion
section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section
namespace FunctorialResolution.EmbeddedResolution

def closedPreimage {X X' : Scheme.{u}} (f : X' ⟶ X) (S : TopologicalSpace.Closeds X) :
    TopologicalSpace.Closeds X' :=
  ⟨f.base ⁻¹' (S : Set X), S.isClosed.preimage f.continuous⟩

section
variable {X X' : Scheme.{u}} (f : X' ⟶ X) (S : TopologicalSpace.Closeds X)

theorem closedPreimage_coe :
    (closedPreimage f S : Set X') = f.base ⁻¹' (S : Set X) := rfl

theorem reducedInverseImage_eq_vanishingIdeal_closedPreimage :
    reducedInverseImage f S = Scheme.IdealSheafData.vanishingIdeal (closedPreimage f S) := rfl


end

private theorem support_vanishingIdeal_consolidated168 {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z := rfl

section
variable {R S : Type u} [CommRing R] [CommRing S]

private theorem isRadical_map_of_bijective_consolidated168 (φ : R →+* S)
    (hφ : Function.Bijective φ) {I : Ideal R} (hI : I.radical = I) :
    (Ideal.map φ I).radical = Ideal.map φ I := by
  refine le_antisymm ?_ Ideal.le_radical
  intro y hy
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hy
  obtain ⟨z, rfl⟩ := hφ.2 y
  rw [← map_pow] at hm
  obtain ⟨w, hw, hw2⟩ := (Ideal.mem_map_iff_of_surjective φ hφ.2).mp hm
  have hz : z ^ m ∈ I := by
    have hwz : w = z ^ m := hφ.1 hw2
    rwa [hwz] at hw
  have hzI : z ∈ I := by
    rw [← hI]
    exact Ideal.mem_radical_iff.mpr ⟨m, hz⟩
  exact Ideal.mem_map_of_mem _ hzI

private theorem ideal_eq_span_of_map_eq_span_consolidated168 (φ : R →+* S)
    (ψ : S →+* R) (hψφ : ∀ r, ψ (φ r) = r) (I : Ideal R) (b : S)
    (hb : Ideal.map φ I = Ideal.span {b}) : I = Ideal.span {ψ b} := by
  have h2 : Ideal.map ψ (Ideal.map φ I) = I := by
    rw [Ideal.map_map, show ψ.comp φ = RingHom.id R from RingHom.ext hψφ, Ideal.map_id]
  rw [← h2, hb, Ideal.map_span, Set.image_singleton]

private theorem isRegularParameterSystem_of_ringEquiv_consolidated168 [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (v : Fin n → R) (w : Fin n → S)
    (hvw : ∀ i, e (v i) = w i) (hv : IsRegularParameterSystem R n v) :
    IsRegularParameterSystem S n w := by
  have h1 := hv.1
  have h2 := hv.2
  refine ⟨?_, ?_⟩
  · have hw : w = fun i => (e : R →+* S) (v i) := funext fun i => (hvw i).symm
    rw [hw, show (Set.range fun i => (e : R →+* S) (v i)) = (e : R →+* S) '' Set.range v from
      Set.range_comp _ _, ← Ideal.map_span, h1]
    exact IsLocalRing.map_ringEquiv_maximalIdeal e
  · rw [h2]
    exact ringKrullDim_eq_of_ringEquiv e


end

section
variable {X Y : Scheme.{u}}

private theorem isIso_appLE_image_consolidated168 (h : X ⟶ Y) [IsOpenImmersion h] (U : X.Opens)
    (e : U ≤ (TopologicalSpace.Opens.map h.base).obj (h ''ᵁ U)) :
    IsIso (h.appLE (h ''ᵁ U) U e) := by
  rw [show h.appLE (h ''ᵁ U) U e = (h.appIso U).hom from (Scheme.Hom.appIso_hom' h U).symm]
  infer_instance

private theorem stalkMap_germ_eq_germ_appLE_consolidated168 (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ (TopologicalSpace.Opens.map f.base).obj U) (x : X) (hx : x ∈ V)
    (hfx : f.base x ∈ U) (s : Γ(Y, U)) :
    f.stalkMap x (Y.presheaf.germ U (f.base x) hfx s)
      = X.presheaf.germ V x hx (f.appLE U V e s) := by
  have key : Y.presheaf.germ U (f.base x) hfx ≫ f.stalkMap x
      = f.app U ≫ X.presheaf.germ ((TopologicalSpace.Opens.map f.base).obj U) x hfx := by
    simp
  have key2 : f.stalkMap x (Y.presheaf.germ U (f.base x) hfx s)
      = X.presheaf.germ ((TopologicalSpace.Opens.map f.base).obj U) x hfx (f.app U s) := by
    rw [← CommRingCat.comp_apply, key, CommRingCat.comp_apply]
  have h1 : f.appLE U V e s = X.presheaf.map (homOfLE e).op (f.app U s) := rfl
  rw [key2, h1, TopCat.Presheaf.germ_res_apply]


end

section
variable {X' Y' : Scheme.{u}} (h : X' ⟶ Y') [IsOpenImmersion h]

private theorem comap_ideal_radical_eq_of_isOpenImmersion_consolidated168 (I : Y'.IdealSheafData) (hI : I.radical = I) (V : X'.affineOpens) :
    ((I.comap h).ideal V).radical = (I.comap h).ideal V := by
  have hU : IsAffineOpen (h ''ᵁ V.1) := V.2.image_of_isOpenImmersion h
  have he : V.1 ≤ (TopologicalSpace.Opens.map h.base).obj (h ''ᵁ V.1) :=
    le_of_eq (Scheme.Hom.preimage_image_eq h V.1).symm
  have : IsIso (h.appLE (h ''ᵁ V.1) V.1 he) := isIso_appLE_image_consolidated168 h V.1 he
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I h ⟨h ''ᵁ V.1, hU⟩ V he]
  refine isRadical_map_of_bijective_consolidated168 _
    (ConcreteCategory.bijective_of_isIso (h.appLE (h ''ᵁ V.1) V.1 he)) ?_
  rw [← Scheme.IdealSheafData.radical_ideal, hI]

theorem comap_vanishingIdeal_of_isOpenImmersion (Z : TopologicalSpace.Closeds Y') :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap h
      = Scheme.IdealSheafData.vanishingIdeal (closedPreimage h Z) := by
  have hZrad : (Scheme.IdealSheafData.vanishingIdeal Z).radical
      = Scheme.IdealSheafData.vanishingIdeal Z := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support, support_vanishingIdeal_consolidated168]
  have hrad : ((Scheme.IdealSheafData.vanishingIdeal Z).comap h).radical
      = (Scheme.IdealSheafData.vanishingIdeal Z).comap h := by
    refine Scheme.IdealSheafData.ext (funext fun V => ?_)
    rw [Scheme.IdealSheafData.radical_ideal]
    exact comap_ideal_radical_eq_of_isOpenImmersion_consolidated168 h _ hZrad V
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal Z).comap h).support
      = closedPreimage h Z := by
    refine SetLike.ext fun x => ?_
    simp only [Scheme.IdealSheafData.mem_support_comap]
    exact Iff.rfl
  calc (Scheme.IdealSheafData.vanishingIdeal Z).comap h
      = ((Scheme.IdealSheafData.vanishingIdeal Z).comap h).radical := hrad.symm
    _ = Scheme.IdealSheafData.vanishingIdeal
          ((Scheme.IdealSheafData.vanishingIdeal Z).comap h).support := by
        rw [Scheme.IdealSheafData.vanishingIdeal_support]
    _ = Scheme.IdealSheafData.vanishingIdeal (closedPreimage h Z) := by rw [hsupp]

theorem comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq (Z : TopologicalSpace.Closeds Y') (Z' : TopologicalSpace.Closeds X')
    (hZ' : (Z' : Set X') = h.base ⁻¹' (Z : Set Y')) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap h
      = Scheme.IdealSheafData.vanishingIdeal Z' := by
  have h1 : closedPreimage h Z = Z' := SetLike.ext' (by rw [closedPreimage_coe, hZ'])
  rw [comap_vanishingIdeal_of_isOpenImmersion, h1]

theorem isStrictNormalCrossingsAt_base_of_comap (E : Y'.IdealSheafData) (hE : IsStrictNormalCrossingsDivisor (E.comap h)) (x : X') :
    IsRegularLocalRing (Y'.presheaf.stalk (h.base x)) ∧
      ∃ (U : Y'.affineOpens) (hy : h.base x ∈ U.1) (n : ℕ) (f : Fin n → Γ(Y', U.1))
        (J : Finset (Fin n)),
        IsRegularParameterSystem (Y'.presheaf.stalk (h.base x)) n
            (fun i => Y'.presheaf.germ U.1 (h.base x) hy (f i)) ∧
          E.ideal U = Ideal.span {∏ i ∈ J, f i} := by
  obtain ⟨hreg, U', hx, n, g, J, hparams, hideal⟩ := hE x
  have : IsRegularLocalRing (X'.presheaf.stalk x) := hreg
  have hU : IsAffineOpen (h ''ᵁ U'.1) := U'.2.image_of_isOpenImmersion h
  have he : U'.1 ≤ (TopologicalSpace.Opens.map h.base).obj (h ''ᵁ U'.1) :=
    le_of_eq (Scheme.Hom.preimage_image_eq h U'.1).symm
  have hy : h.base x ∈ h ''ᵁ U'.1 := ⟨x, hx, rfl⟩
  have : IsIso (h.appLE (h ''ᵁ U'.1) U'.1 he) := isIso_appLE_image_consolidated168 h U'.1 he
  have : IsIso (h.stalkMap x) := inferInstance
  let ε : Γ(Y', h ''ᵁ U'.1) ≃+* Γ(X', U'.1) :=
    (asIso (h.appLE (h ''ᵁ U'.1) U'.1 he)).commRingCatIsoToRingEquiv
  let τ : Y'.presheaf.stalk (h.base x) ≃+* X'.presheaf.stalk x :=
    (asIso (h.stalkMap x)).commRingCatIsoToRingEquiv
  have hgerm : ∀ i, τ (Y'.presheaf.germ (h ''ᵁ U'.1) (h.base x) hy (ε.symm (g i)))
      = X'.presheaf.germ U'.1 x hx (g i) := by
    intro i
    have h1 := stalkMap_germ_eq_germ_appLE_consolidated168 h (h ''ᵁ U'.1) U'.1 he x hx hy (ε.symm (g i))
    have h2 : (h.appLE (h ''ᵁ U'.1) U'.1 he) (ε.symm (g i)) = g i := ε.apply_symm_apply (g i)
    rw [h2] at h1
    exact h1
  refine ⟨IsRegularLocalRing.of_ringEquiv τ.symm, ⟨h ''ᵁ U'.1, hU⟩, hy, n,
    fun i => ε.symm (g i), J, ?_, ?_⟩
  · refine isRegularParameterSystem_of_ringEquiv_consolidated168 τ.symm n
      (fun i => X'.presheaf.germ U'.1 x hx (g i))
      (fun i => Y'.presheaf.germ (h ''ᵁ U'.1) (h.base x) hy (ε.symm (g i))) ?_ hparams
    intro i
    rw [← hgerm i, τ.symm_apply_apply]
  · have hmap := Scheme.IdealSheafData.comap_ideal_eq_map_appLE E h ⟨h ''ᵁ U'.1, hU⟩ U' he
    rw [hideal] at hmap
    have hprod : (ε.symm : Γ(X', U'.1) →+* Γ(Y', h ''ᵁ U'.1)) (∏ i ∈ J, g i)
        = ∏ i ∈ J, ε.symm (g i) := map_prod _ _ _
    rw [ideal_eq_span_of_map_eq_span_consolidated168 ((h.appLE (h ''ᵁ U'.1) U'.1 he).hom)
      (ε.symm : Γ(X', U'.1) →+* Γ(Y', h ''ᵁ U'.1)) (fun r => ε.symm_apply_apply r)
      (E.ideal ⟨h ''ᵁ U'.1, hU⟩) (∏ i ∈ J, g i) hmap.symm, hprod]


end

section
variable {A B Z : Scheme.{u}}

theorem reducedInverseImage_comp (g : A ⟶ B) (f : B ⟶ Z)
    (W : TopologicalSpace.Closeds Z) :
    reducedInverseImage (g ≫ f) W
      = Scheme.IdealSheafData.vanishingIdeal (closedPreimage g (closedPreimage f W)) := by
  have h : closedPreimage (g ≫ f) W = closedPreimage g (closedPreimage f W) := by
    apply SetLike.ext'
    show (g ≫ f).base ⁻¹' (W : Set Z) = g.base ⁻¹' (f.base ⁻¹' (W : Set Z))
    ext p
    simp
  rw [reducedInverseImage_eq_vanishingIdeal_closedPreimage, h]

theorem comap_reducedInverseImage_of_isOpenImmersion (h : A ⟶ B)
    [IsOpenImmersion h] (f : B ⟶ Z) (W : TopologicalSpace.Closeds Z) :
    (reducedInverseImage f W).comap h = reducedInverseImage (h ≫ f) W := by
  rw [reducedInverseImage_eq_vanishingIdeal_closedPreimage, comap_vanishingIdeal_of_isOpenImmersion,
    reducedInverseImage_comp]


end

theorem reducedInverseImage_eq_radical {T Y : Scheme.{u}} (f : T ⟶ Y)
    (W : TopologicalSpace.Closeds Y) (J : T.IdealSheafData)
    (hJ : (J.support : Set T) = f.base ⁻¹' (W : Set Y)) :
    reducedInverseImage f W = J.radical := by
  have h : J.support = closedPreimage f W := SetLike.ext' hJ
  rw [reducedInverseImage_eq_vanishingIdeal_closedPreimage, ← h,
    Scheme.IdealSheafData.vanishingIdeal_support]

theorem IsStrictNormalCrossingsDivisor.of_isOpenImmersion_jointly_surjective {X : Scheme.{u}} (D : X.IdealSheafData) {ι : Type v}
    (Y : ι → Scheme.{u}) (p : ∀ i, Y i ⟶ X) (hp : ∀ i, IsOpenImmersion (p i))
    (hsurj : ∀ x : X, ∃ (i : ι) (y : Y i), (p i).base y = x)
    (hD : ∀ i, IsStrictNormalCrossingsDivisor (D.comap (p i))) : IsStrictNormalCrossingsDivisor D := by
  intro x
  obtain ⟨i, y, hy⟩ := hsurj x
  subst hy
  have := hp i
  exact isStrictNormalCrossingsAt_base_of_comap (p i) D (hD i) y

theorem IsStrictNormalCrossingsDivisor.reducedInverseImage_coprod {A B Z : Scheme.{u}} (g : (A ⨿ B) ⟶ Z)
    (W : TopologicalSpace.Closeds Z)
    (hA : IsStrictNormalCrossingsDivisor (reducedInverseImage ((coprod.inl : A ⟶ A ⨿ B) ≫ g) W))
    (hB : IsStrictNormalCrossingsDivisor (reducedInverseImage ((coprod.inr : B ⟶ A ⨿ B) ≫ g) W)) :
    IsStrictNormalCrossingsDivisor (reducedInverseImage g W) := by
  intro z
  by_cases hz : z ∈ Set.range ⇑(coprod.inl : A ⟶ A ⨿ B).base
  · obtain ⟨a, rfl⟩ := hz
    have h1 : (reducedInverseImage g W).comap (coprod.inl : A ⟶ A ⨿ B)
        = reducedInverseImage ((coprod.inl : A ⟶ A ⨿ B) ≫ g) W :=
      comap_reducedInverseImage_of_isOpenImmersion _ g W
    refine isStrictNormalCrossingsAt_base_of_comap (coprod.inl : A ⟶ A ⨿ B) (reducedInverseImage g W) ?_ a
    rw [h1]
    exact hA
  · have hz' : z ∈ Set.range ⇑(coprod.inr : B ⟶ A ⨿ B).base := by
      rw [Blowup.range_coprod_inr_eq_compl]
      exact hz
    obtain ⟨b, rfl⟩ := hz'
    have h1 : (reducedInverseImage g W).comap (coprod.inr : B ⟶ A ⨿ B)
        = reducedInverseImage ((coprod.inr : B ⟶ A ⨿ B) ≫ g) W :=
      comap_reducedInverseImage_of_isOpenImmersion _ g W
    refine isStrictNormalCrossingsAt_base_of_comap (coprod.inr : B ⟶ A ⨿ B) (reducedInverseImage g W) ?_ b
    rw [h1]
    exact hB

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorRadical
section

namespace FunctorialResolution.EmbeddedResolution

private theorem algebraMap_coordPolynomialRing_injective_of_etale_consolidated182 (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    [Nontrivial S] : Function.Injective (algebraMap (CoordPolynomialRing k m) S) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro a ha
  by_contra h
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := S)
    (mem_nonZeroDivisors_of_ne_zero h)
  have h1 : (1 : S) = 0 := by
    apply hreg
    show a • (1 : S) = a • (0 : S)
    rw [smul_zero, Algebra.smul_def, ha, zero_mul]
  exact one_ne_zero h1

private theorem isRadical_span_singleton_of_isRadical_map_atPrime_consolidated182 {S : Type u} [CommRing S] (a : S)
    (h : ∀ (Q : Ideal S) [Q.IsPrime],
      (Ideal.map (algebraMap S (Localization.AtPrime Q)) (Ideal.span ({a} : Set S))).IsRadical) :
    (Ideal.span ({a} : Set S)).IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hx
  by_contra hxI
  obtain ⟨K, hKmem⟩ : ∃ K : Ideal S, ∀ b : S, b ∈ K ↔ b * x ∈ Ideal.span ({a} : Set S) :=
    ⟨{ carrier := {s : S | s * x ∈ Ideal.span ({a} : Set S)}
       zero_mem' := by
         show (0 : S) * x ∈ Ideal.span ({a} : Set S)
         rw [zero_mul]
         exact Ideal.zero_mem _
       add_mem' := by
         intro b c hb hc
         show (b + c) * x ∈ Ideal.span ({a} : Set S)
         rw [add_mul]
         exact Ideal.add_mem _ hb hc
       smul_mem' := by
         intro c b hb
         show (c • b) * x ∈ Ideal.span ({a} : Set S)
         rw [smul_eq_mul, mul_assoc]
         exact Ideal.mul_mem_left _ c hb },
     fun b => Iff.rfl⟩
  have hKne : K ≠ ⊤ := by
    intro htop
    have h1 : (1 : S) ∈ K := by rw [htop]; exact Submodule.mem_top
    have h2 := (hKmem 1).mp h1
    rw [one_mul] at h2
    exact hxI h2
  obtain ⟨Q, hQmax, hKQ⟩ := Ideal.exists_le_maximal K hKne
  have hQp : Q.IsPrime := hQmax.isPrime
  have hrad := h Q
  have hpow : (algebraMap S (Localization.AtPrime Q) x) ^ n ∈
      Ideal.map (algebraMap S (Localization.AtPrime Q)) (Ideal.span ({a} : Set S)) := by
    rw [← map_pow]
    exact Ideal.mem_map_of_mem _ hn
  have hxmem : algebraMap S (Localization.AtPrime Q) x ∈
      Ideal.map (algebraMap S (Localization.AtPrime Q)) (Ideal.span ({a} : Set S)) :=
    hrad (Ideal.mem_radical_iff.mpr ⟨n, hpow⟩)
  rw [Ideal.map_span, Set.image_singleton] at hxmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hxmem
  obtain ⟨⟨y, s⟩, hys⟩ := IsLocalization.surj (M := Q.primeCompl) c
  have key : algebraMap S (Localization.AtPrime Q) (x * (s : S)) =
      algebraMap S (Localization.AtPrime Q) (a * y) := by
    have h1 : algebraMap S (Localization.AtPrime Q) (x * (s : S))
        = (c * algebraMap S (Localization.AtPrime Q) (s : S)) *
            algebraMap S (Localization.AtPrime Q) a := by
      rw [map_mul, ← hc]; ring
    rw [h1, hys, map_mul]; ring
  obtain ⟨dd, hd⟩ := (IsLocalization.eq_iff_exists Q.primeCompl (Localization.AtPrime Q)).mp key
  have hmem0 : ((dd : S) * (s : S)) * x ∈ Ideal.span ({a} : Set S) := by
    have heq : ((dd : S) * (s : S)) * x = (dd : S) * (x * (s : S)) := by ring
    rw [heq, hd]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self a))
  have hmem : ((dd : S) * (s : S)) ∈ K := (hKmem _).mpr hmem0
  have hQmem : ((dd : S) * (s : S)) ∈ Q := hKQ hmem
  rcases hQp.mem_or_mem hQmem with hcase | hcase
  · exact dd.2 hcase
  · exact s.2 hcase

section
variable (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]

theorem etaleChartCoord_injective [Nontrivial S] : Function.Injective (etaleChartCoord k m S) := by
  have hinj := algebraMap_coordPolynomialRing_injective_of_etale_consolidated182 k m S
  intro i j hij
  have h : (MvPolynomial.X (ULift.up i) : CoordPolynomialRing k m)
      = MvPolynomial.X (ULift.up j) := by
    apply hinj
    rw [← etaleChartCoord_def, ← etaleChartCoord_def]
    exact hij
  exact congrArg ULift.down (MvPolynomial.X_injective h)

theorem linearIndependent_toCotangent_etaleChartCoord (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A] [Algebra S A]
    [IsLocalization q.primeCompl A] [IsLocalRing A] (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q)
    (hJA : ∀ j ∈ J, algebraMap S A (etaleChartCoord k m S j) ∈ IsLocalRing.maximalIdeal A) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun j : { x : Fin m // x ∈ J } =>
          (IsLocalRing.maximalIdeal A).toCotangent
            ⟨algebraMap S A (etaleChartCoord k m S (j : Fin m)), hJA (j : Fin m) j.2⟩ :
        { x : Fin m // x ∈ J } → IsLocalRing.CotangentSpace A) := by
  classical
  have hreg : IsRegularLocalRing A := isRegularLocalRing_of_isLocalization_etale k m S q A
  have hnt : Nontrivial S := by
    rcases subsingleton_or_nontrivial S with hs | hs
    · exfalso
      have := hs
      have h10 : (1 : S) = (0 : S) := Subsingleton.elim _ _
      have hA : (1 : A) = 0 := by
        calc (1 : A) = algebraMap S A 1 := (map_one _).symm
          _ = algebraMap S A 0 := by rw [h10]
          _ = 0 := map_zero _
      exact one_ne_zero hA
    · exact hs
  obtain ⟨d, w, hwq, hwJ, hspan, hdim⟩ :=
    exists_regularSystemOfParameters_containing_etaleChartCoords k m S q A J hJ
  have hwm : ∀ i, algebraMap S A (w i) ∈ IsLocalRing.maximalIdeal A := by
    intro i
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin d → IsLocalRing.CotangentSpace A,
      ∀ i, y i = (IsLocalRing.maximalIdeal A).toCotangent ⟨algebraMap S A (w i), hwm i⟩ :=
    ⟨_, fun i => rfl⟩
  have key : ∀ (b : A), b ∈ Ideal.span (Set.range fun i => algebraMap S A (w i)) →
      ∀ (hb : b ∈ IsLocalRing.maximalIdeal A),
        (IsLocalRing.maximalIdeal A).toCotangent ⟨b, hb⟩ ∈
          Submodule.span (IsLocalRing.ResidueField A) (Set.range y) := by
    intro b hb0
    have hb' : b ∈ Submodule.span A (Set.range fun i => algebraMap S A (w i)) := hb0
    clear hb0
    induction hb' using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        intro hz'
        exact Submodule.subset_span ⟨i, by rw [hy i]⟩
    | zero =>
        intro hz'
        have h0 : (⟨(0 : A), hz'⟩ : IsLocalRing.maximalIdeal A) = 0 := rfl
        rw [h0, map_zero]
        exact Submodule.zero_mem _
    | add z z' hz hz' ihz ihz' =>
        intro hbb
        have hzm : z ∈ IsLocalRing.maximalIdeal A := by rw [← hspan]; exact hz
        have hzm' : z' ∈ IsLocalRing.maximalIdeal A := by rw [← hspan]; exact hz'
        have hsum : (⟨z + z', hbb⟩ : IsLocalRing.maximalIdeal A) = ⟨z, hzm⟩ + ⟨z', hzm'⟩ := rfl
        rw [hsum, map_add]
        exact Submodule.add_mem _ (ihz hzm) (ihz' hzm')
    | smul c z hz ih =>
        intro hbb
        have hzm : z ∈ IsLocalRing.maximalIdeal A := by rw [← hspan]; exact hz
        have hsm : (⟨c • z, hbb⟩ : IsLocalRing.maximalIdeal A) = c • ⟨z, hzm⟩ := rfl
        rw [hsm, map_smul, ← IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField A) c]
        exact Submodule.smul_mem _ _ (ih hzm)
  have hspanY : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField A) (Set.range y) := by
    intro v _
    obtain ⟨⟨b, hb⟩, rfl⟩ := Ideal.toCotangent_surjective (IsLocalRing.maximalIdeal A) v
    exact key b (by rw [hspan]; exact hb) hb
  have hcard0 : ((d : ℕ) : WithBot ℕ∞) =
      ((Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) : ℕ) :
        WithBot ℕ∞) :=
    hdim.trans ((IsRegularLocalRing.iff_finrank_cotangentSpace A).mp ‹_›).symm
  have hcard : Fintype.card (Fin d) =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) := by
    rw [Fintype.card_fin]
    exact_mod_cast hcard0
  have hliY : LinearIndependent (IsLocalRing.ResidueField A) y :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspanY hcard
  have hchoice : ∀ j : { x : Fin m // x ∈ J },
      ∃ i : Fin d, w i = etaleChartCoord k m S (j : Fin m) := fun j => hwJ (j : Fin m) j.2
  choose f hf using hchoice
  have hfinj : Function.Injective f := by
    intro j₁ j₂ hjj
    have h1 : etaleChartCoord k m S (j₁ : Fin m) = etaleChartCoord k m S (j₂ : Fin m) := by
      rw [← hf j₁, ← hf j₂, hjj]
    exact Subtype.ext (etaleChartCoord_injective k m S h1)
  have hcomp := hliY.comp f hfinj
  have heq : y ∘ f = fun j : { x : Fin m // x ∈ J } =>
      (IsLocalRing.maximalIdeal A).toCotangent
        ⟨algebraMap S A (etaleChartCoord k m S (j : Fin m)), hJA (j : Fin m) j.2⟩ := by
    funext j
    have h1 : (⟨algebraMap S A (w (f j)), hwm (f j)⟩ : IsLocalRing.maximalIdeal A)
        = ⟨algebraMap S A (etaleChartCoord k m S (j : Fin m)), hJA (j : Fin m) j.2⟩ :=
      Subtype.ext (congrArg (algebraMap S A) (hf j))
    show y (f j) = _
    rw [hy (f j)]
    exact congrArg _ h1
  rw [← heq]
  exact hcomp

theorem isRadical_span_singleton_prod_algebraMap_etaleChartCoord (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] [IsLocalRing A] (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q) :
    (Ideal.span ({∏ j ∈ J, algebraMap S A (etaleChartCoord k m S j)} : Set A)).IsRadical := by
  classical
  have hreg : IsRegularLocalRing A := isRegularLocalRing_of_isLocalization_etale k m S q A
  have hJA : ∀ j ∈ J, algebraMap S A (etaleChartCoord k m S j) ∈ IsLocalRing.maximalIdeal A := by
    intro j hj
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A q
      (etaleChartCoord k m S j)).mpr (hJ j hj)
  have hli := linearIndependent_toCotangent_etaleChartCoord k m S q A J hJ hJA
  have hmain := _root_.IsRegularLocalRing.isRadical_span_singleton_prod
    (fun j : { x : Fin m // x ∈ J } => algebraMap S A (etaleChartCoord k m S (j : Fin m)))
    (fun j => hJA (j : Fin m) j.2) hli
  rw [← Finset.prod_coe_sort J (fun j => algebraMap S A (etaleChartCoord k m S j))]
  exact hmain

theorem isRadical_map_span_singleton_prod_etaleChartCoord (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] [IsLocalRing A] (T : Finset (Fin m)) :
    (Ideal.map (algebraMap S A)
      (Ideal.span ({∏ j ∈ T, etaleChartCoord k m S j} : Set S))).IsRadical := by
  classical
  obtain ⟨J, hJdef⟩ : ∃ J : Finset (Fin m),
      J = T.filter (fun j => etaleChartCoord k m S j ∈ q) := ⟨_, rfl⟩
  have hJsub : J ⊆ T := by rw [hJdef]; exact Finset.filter_subset _ _
  have hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q := by
    intro j hj
    rw [hJdef] at hj
    exact (Finset.mem_filter.mp hj).2
  have hunit : IsUnit (∏ j ∈ T \ J, algebraMap S A (etaleChartCoord k m S j)) := by
    refine Finset.prod_induction _ _ (fun u v hu hv => hu.mul hv) isUnit_one ?_
    intro j hj
    have h1 := Finset.mem_sdiff.mp hj
    have hj' : etaleChartCoord k m S j ∉ q := by
      intro hmem
      exact h1.2 (by rw [hJdef]; exact Finset.mem_filter.mpr ⟨h1.1, hmem⟩)
    exact IsLocalization.map_units A (⟨etaleChartCoord k m S j, hj'⟩ : q.primeCompl)
  have hsplit : ∏ j ∈ T, algebraMap S A (etaleChartCoord k m S j)
      = (∏ j ∈ T \ J, algebraMap S A (etaleChartCoord k m S j)) *
        ∏ j ∈ J, algebraMap S A (etaleChartCoord k m S j) := by
    rw [← Finset.prod_union Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hJsub]
  rw [Ideal.map_span, Set.image_singleton, map_prod, hsplit,
    Ideal.span_singleton_mul_left_unit hunit _]
  exact isRadical_span_singleton_prod_algebraMap_etaleChartCoord k m S q A J hJ

theorem isRadical_span_singleton_prod_etaleChartCoord (T : Finset (Fin m)) :
    (Ideal.span ({∏ j ∈ T, etaleChartCoord k m S j} : Set S)).IsRadical := by
  refine isRadical_span_singleton_of_isRadical_map_atPrime_consolidated182 (∏ j ∈ T, etaleChartCoord k m S j) ?_
  intro Q hQ
  have : Q.IsPrime := hQ
  exact isRadical_map_span_singleton_prod_etaleChartCoord k m S Q (Localization.AtPrime Q) T


end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.GermRegularParameters
section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

theorem germ_mem_maximalIdeal_iff {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    X.presheaf.germ U x hx s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
      s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let instSt : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hx).hom.toAlgebra
  have instLoc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal s

variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}

section
variable (hU : IsAffineOpen U) (c : EtaleChart p U m) (x : X) (hx : x ∈ U) (J₀ : Finset (Fin m))
include hU

theorem exists_sections_span_eq_maximalIdeal_with_coords (hJ₀ : ∀ j ∈ J₀, X.presheaf.germ U x hx (c.coord j) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    ∃ (d : ℕ) (f : Fin d → Γ(X, U)),
      (∀ i, X.presheaf.germ U x hx (f i) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ∧
      (∀ j ∈ J₀, ∃ i, f i = c.coord j) ∧
      Ideal.span (Set.range fun i => X.presheaf.germ U x hx (f i)) =
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
      (d : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x) := by
  let instAlg : Algebra (CoordPolynomialRing k m) Γ(X, U) := c.algebra
  have instEt : Algebra.Etale (CoordPolynomialRing k m) Γ(X, U) := c.algebra_etale hU
  let instSt : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hx).hom.toAlgebra
  have instLoc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  have halg : ∀ t : Γ(X, U),
      algebraMap Γ(X, U) (X.presheaf.stalk x) t = X.presheaf.germ U x hx t := fun _ => rfl
  have hcoord : ∀ j : Fin m, etaleChartCoord k m Γ(X, U) j = c.coord j := by
    intro j
    show c.coordRingHom (MvPolynomial.X (ULift.up j : ULift.{u} (Fin m))) = c.coord j
    exact c.coordRingHom_X j
  have hq : ∀ j ∈ J₀, etaleChartCoord k m Γ(X, U) j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    intro j hj
    rw [hcoord j]
    exact (germ_mem_maximalIdeal_iff hU x hx (c.coord j)).mp (hJ₀ j hj)
  obtain ⟨d, f, hf1, hf2, hf3, hf4⟩ :=
    exists_regularSystemOfParameters_containing_etaleChartCoords k m Γ(X, U)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal (X.presheaf.stalk x) J₀ hq
  refine ⟨d, f, ?_, ?_, ?_, hf4⟩
  · intro i
    exact (germ_mem_maximalIdeal_iff hU x hx (f i)).mpr (hf1 i)
  · intro j hj
    obtain ⟨i, hi⟩ := hf2 j hj
    exact ⟨i, by rw [hi, hcoord j]⟩
  · simpa only [halg] using hf3

theorem exists_isRegularParameterSystem_with_coords_of_mem_prime (hJ₀ : ∀ j ∈ J₀, c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ (n : ℕ) (f : Fin n → Γ(X, U)),
      (∀ j ∈ J₀, ∃ i, f i = c.coord j) ∧
      IsRegularParameterSystem (X.presheaf.stalk x) n
        (fun i => X.presheaf.germ U x hx (f i)) := by
  obtain ⟨d, f, -, h2, h3, h4⟩ :=
    exists_sections_span_eq_maximalIdeal_with_coords hU c x hx J₀
      (fun j hj => (germ_mem_maximalIdeal_iff hU x hx (c.coord j)).mpr (hJ₀ j hj))
  exact ⟨d, f, h2, h3, h4⟩


end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothDivisorEtaleChart
section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

section
variable {k : Type u} [Field k]

private theorem one_mem_of_mul_mem_of_dual_derivations_consolidated184 {B : Type u} [CommRing B]
    [Algebra k B] (I : Ideal B) (y₁ y₂ f a b : B) (δ₁ δ₂ : Derivation k B B)
    (hf : f ∈ I) (hy₁ : y₁ = a * f) (hy₂ : y₂ = b * f)
    (e11 : δ₁ y₁ = 1) (e12 : δ₁ y₂ = 0) (e21 : δ₂ y₁ = 0) (e22 : δ₂ y₂ = 1) :
    (1 : B) ∈ I := by
  have hπf : (Ideal.Quotient.mk I) f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hf
  have key : ∀ (δ : Derivation k B B) (c : B),
      (Ideal.Quotient.mk I) (δ (c * f)) =
        (Ideal.Quotient.mk I) c * (Ideal.Quotient.mk I) (δ f) := by
    intro δ c
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hπf,
      zero_mul, add_zero]
  have k11 : (Ideal.Quotient.mk I) a * (Ideal.Quotient.mk I) (δ₁ f) = 1 := by
    rw [← key δ₁ a, ← hy₁, e11, map_one]
  have k12 : (Ideal.Quotient.mk I) a * (Ideal.Quotient.mk I) (δ₂ f) = 0 := by
    rw [← key δ₂ a, ← hy₁, e21, map_zero]
  have k21 : (Ideal.Quotient.mk I) b * (Ideal.Quotient.mk I) (δ₁ f) = 0 := by
    rw [← key δ₁ b, ← hy₂, e12, map_zero]
  have k22 : (Ideal.Quotient.mk I) b * (Ideal.Quotient.mk I) (δ₂ f) = 1 := by
    rw [← key δ₂ b, ← hy₂, e22, map_one]
  have hone : (1 : B ⧸ I) = 0 := by
    calc (1 : B ⧸ I)
        = ((Ideal.Quotient.mk I) a * (Ideal.Quotient.mk I) (δ₁ f)) *
            ((Ideal.Quotient.mk I) b * (Ideal.Quotient.mk I) (δ₂ f)) := by
          rw [k11, k22, one_mul]
      _ = ((Ideal.Quotient.mk I) a * (Ideal.Quotient.mk I) (δ₂ f)) *
            ((Ideal.Quotient.mk I) b * (Ideal.Quotient.mk I) (δ₁ f)) := by ring
      _ = 0 := by rw [k12, k21, mul_zero]
  refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
  rw [map_one]
  exact hone

private theorem one_mem_of_coord_mem_span_singleton_of_ne_consolidated184 {m : ℕ} {B : Type u} [CommRing B]
    [Algebra (MvPolynomial (ULift.{u} (Fin m)) k) B] [Algebra k B]
    [IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) B]
    [Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) B]
    (I : Ideal B) (h : B) (hI : I = Ideal.span ({h} : Set B))
    (j₁ j₂ : Fin m) (hne : j₁ ≠ j₂)
    (hm1 : EtaleCoordinates.coord k (ULift.{u} (Fin m)) B (ULift.up j₁) ∈ I)
    (hm2 : EtaleCoordinates.coord k (ULift.{u} (Fin m)) B (ULift.up j₂) ∈ I) :
    (1 : B) ∈ I := by
  have hh : h ∈ I := by
    rw [hI]; exact Ideal.mem_span_singleton_self h
  rw [hI] at hm1 hm2
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hm1
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hm2
  have hne' : (ULift.up j₁ : ULift.{u} (Fin m)) ≠ ULift.up j₂ := fun hc =>
    hne (congrArg ULift.down hc)
  exact one_mem_of_mul_mem_of_dual_derivations_consolidated184 I _ _ h a b
    (EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) B (ULift.up j₁))
    (EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) B (ULift.up j₂))
    hh ha.symm hb.symm
    (EtaleCoordinates.partialDeriv_coord_self k (ULift.{u} (Fin m)) B (ULift.up j₁))
    (EtaleCoordinates.partialDeriv_coord_of_ne k (ULift.{u} (Fin m)) B _ _ hne')
    (EtaleCoordinates.partialDeriv_coord_of_ne k (ULift.{u} (Fin m)) B _ _ hne'.symm)
    (EtaleCoordinates.partialDeriv_coord_self k (ULift.{u} (Fin m)) B (ULift.up j₂))


end

section
variable {X : Scheme.{u}} (D : X.IdealSheafData) (W₁ W₂ : X.affineOpens) (hW : (W₁ : X.Opens) = (W₂ : X.Opens))
include hW

private theorem ideal_eq_bot_of_opens_eq_consolidated184 (h : D.ideal W₁ = ⊥) : D.ideal W₂ = ⊥ := by
  obtain rfl : W₁ = W₂ := Subtype.ext hW
  exact h

private theorem exists_ideal_eq_span_singleton_of_opens_eq_consolidated184 (h : ∃ f, D.ideal W₂ = Ideal.span ({f} : Set Γ(X, (W₂ : X.Opens)))) :
    ∃ f, D.ideal W₁ = Ideal.span ({f} : Set Γ(X, (W₁ : X.Opens))) := by
  obtain rfl : W₁ = W₂ := Subtype.ext hW
  exact h


end

section
variable {X : Scheme.{u}} {k : Type u} [Field k] [CharZero k] (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (D : X.IdealSheafData) (hD : IsSmoothDivisor p D)
include hD

theorem exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton (x : X) (hx : x ∈ D.support) :
    ∃ (U : X.Opens) (m : ℕ) (c : EtaleChart p U m) (j : Fin m),
      x ∈ U ∧ restrictIdeal D U = c.coordIdeal ({j} : Finset (Fin m)) := by
  rw [isSmoothDivisor_iff] at hD
  obtain ⟨hcart, hsm⟩ := hD
  have : Smooth (D.subschemeι ≫ p) := hsm
  obtain ⟨U, m, c, S, hxU, hU, hDU⟩ := exists_chart_restrictIdeal_eq_coordIdeal p D x hx
  have hideal : D.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m))) :=
    c.ideal_eq_span_coord hU D S hDU
  obtain ⟨V, f, hxV, hfnzd, hVf⟩ := hcart x
  obtain ⟨g, g', hgg', hxg⟩ := exists_basicOpen_le_affine_inter hU V.2 x ⟨hxU, hxV⟩
  have hWaff : IsAffineOpen (X.basicOpen g) := hU.basicOpen g
  have hresU : Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
      (D.ideal ⟨U, hU⟩) = D.ideal ⟨X.basicOpen g, hWaff⟩ :=
    D.map_ideal_basicOpen ⟨U, hU⟩ g
  have hspan : D.ideal ⟨X.basicOpen g, hWaff⟩ =
      Ideal.span ((fun j : Fin m =>
        (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (c.coord j)) ''
          (S : Set (Fin m))) := by
    rw [← hresU, hideal, Ideal.map_span, ← Set.image_comp]
    rfl
  have hxg' : x ∈ X.basicOpen g' := hgg' ▸ hxg
  have hmap := D.map_ideal_basicOpen V g'
  rw [hVf, Ideal.map_span, Set.image_singleton] at hmap
  have hSne : S.Nonempty := by
    rcases Finset.eq_empty_or_nonempty S with rfl | hne
    · exfalso
      have h0 : D.ideal ⟨X.basicOpen g, hWaff⟩ = ⊥ := by
        rw [hspan]; simp
      have h0' : D.ideal (X.affineBasicOpen g') = ⊥ :=
        ideal_eq_bot_of_opens_eq_consolidated184 D ⟨X.basicOpen g, hWaff⟩ (X.affineBasicOpen g') hgg' h0
      have hfzero := Ideal.span_singleton_eq_bot.mp (hmap.trans h0')
      have instLoc' : IsLocalization.Away g' Γ(X, X.basicOpen g') :=
        V.2.isLocalization_basicOpen g'
      have hfa : algebraMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen g') f = 0 := hfzero
      obtain ⟨cc, hcc⟩ :=
        (IsLocalization.eq_iff_exists (Submonoid.powers g')
          Γ(X, X.basicOpen g')).mp (show
            algebraMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen g') f =
              algebraMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen g') 0 by
            rw [hfa, map_zero])
      have hz : (cc : Γ(X, (V : X.Opens))) = 0 :=
        (mem_nonZeroDivisors_iff.mp hfnzd).2 _ (by rw [hcc, mul_zero])
      have hunit : IsUnit (algebraMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen g')
          (cc : Γ(X, (V : X.Opens)))) :=
        IsLocalization.map_units Γ(X, X.basicOpen g') cc
      rw [hz, map_zero] at hunit
      have h01 : (0 : Γ(X, X.basicOpen g')) = 1 := isUnit_zero_iff.mp hunit
      have h10 : (0 : X.presheaf.stalk x) = 1 := by
        have hq := congrArg (X.presheaf.germ (X.basicOpen g') x hxg').hom h01
        rwa [map_zero, map_one] at hq
      exact zero_ne_one h10
    · exact hne
  have hcard1 : ∀ j₁ ∈ S, ∀ j₂ ∈ S, j₁ = j₂ := by
    intro j₁ hj₁ j₂ hj₂
    by_contra hne
    obtain ⟨h, hI⟩ : ∃ h, D.ideal ⟨X.basicOpen g, hWaff⟩ =
        Ideal.span ({h} : Set Γ(X, X.basicOpen g)) :=
      exists_ideal_eq_span_singleton_of_opens_eq_consolidated184 D ⟨X.basicOpen g, hWaff⟩ (X.affineBasicOpen g') hgg'
        ⟨_, hmap.symm⟩
    let instPB : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, X.basicOpen g) :=
      (((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom).comp c.coordRingHom).toAlgebra
    let instkB : Algebra k Γ(X, X.basicOpen g) :=
      ((((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom).comp c.coordRingHom).comp
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k)).toAlgebra
    have instTower : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k)
        Γ(X, X.basicOpen g) :=
      IsScalarTower.of_algebraMap_eq fun _ => by
        rw [MvPolynomial.algebraMap_eq]
        rfl
    let instPA : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra
    have instFE1 : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) :=
      c.algebra_formallyEtale hU
    have instScalarTower : IsScalarTower (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U)
        Γ(X, X.basicOpen g) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    have instLoc : IsLocalization.Away g Γ(X, X.basicOpen g) := hU.isLocalization_basicOpen g
    have instFE2 : Algebra.FormallyEtale Γ(X, U) Γ(X, X.basicOpen g) :=
      Algebra.FormallyEtale.of_isLocalization (Submonoid.powers g)
    have instFE3 : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k)
        Γ(X, X.basicOpen g) :=
      Algebra.FormallyEtale.comp (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U)
        Γ(X, X.basicOpen g)
    have hcoord : ∀ j : Fin m,
        EtaleCoordinates.coord k (ULift.{u} (Fin m)) Γ(X, X.basicOpen g) (ULift.up j) =
          (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (c.coord j) := by
      intro j
      rw [EtaleCoordinates.coord_def]
      show (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
          (c.coordRingHom (MvPolynomial.X (ULift.up j))) = _
      rw [c.coordRingHom_X]
    have hm1 : EtaleCoordinates.coord k (ULift.{u} (Fin m)) Γ(X, X.basicOpen g) (ULift.up j₁) ∈
        D.ideal ⟨X.basicOpen g, hWaff⟩ := by
      rw [hcoord, hspan]
      exact Ideal.subset_span ⟨j₁, hj₁, rfl⟩
    have hm2 : EtaleCoordinates.coord k (ULift.{u} (Fin m)) Γ(X, X.basicOpen g) (ULift.up j₂) ∈
        D.ideal ⟨X.basicOpen g, hWaff⟩ := by
      rw [hcoord, hspan]
      exact Ideal.subset_span ⟨j₂, hj₂, rfl⟩
    have hone : (1 : Γ(X, X.basicOpen g)) ∈ D.ideal ⟨X.basicOpen g, hWaff⟩ :=
      one_mem_of_coord_mem_span_singleton_of_ne_consolidated184 (D.ideal ⟨X.basicOpen g, hWaff⟩) h hI j₁ j₂ hne hm1 hm2
    have htop : D.ideal ⟨X.basicOpen g, hWaff⟩ = ⊤ := (Ideal.eq_top_iff_one _).mpr hone
    have hle := ideal_le_primeIdealOf D hWaff hxg hx
    rw [htop] at hle
    exact (hWaff.primeIdealOf ⟨x, hxg⟩).isPrime.ne_top (top_le_iff.mp hle)
  obtain ⟨j, hj⟩ :=
    Finset.card_eq_one.mp
      (le_antisymm (Finset.card_le_one.mpr hcard1) (Finset.card_pos.mpr hSne))
  exact ⟨U, m, c, j, hxU, by rw [hDU, hj]⟩

theorem inStrictNormalCrossingPosition_singleton_of_isSmoothDivisor :
    InStrictNormalCrossingPosition p [D] := by
  rw [inStrictNormalCrossingPosition_iff]
  refine ⟨?_, fun x => ?_⟩
  · intro D' hD'
    simp only [List.mem_singleton] at hD'
    subst hD'
    exact hD
  · by_cases hx : x ∈ D.support
    · obtain ⟨U, m, c, j, hxU, hDU⟩ :=
        exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton p D hD x hx
      refine ⟨U, hxU, m, c, fun _ => some j, ?_, ?_, ?_⟩
      · intro i hi i' hi' t _ _
        simp only [List.length_singleton] at hi hi'
        omega
      · intro i hi hnone
        simp at hnone
      · intro i hi t ht
        have htj : t = j := (Option.some.inj ht).symm
        subst htj
        have hi0 : i = 0 := by
          simp only [List.length_singleton] at hi
          omega
        subst hi0
        simpa using hDU
    · obtain ⟨U, m, hxU, hUW, hUaff, hc⟩ :=
        exists_etaleChart_le p x
          (⟨((D.support : Set X))ᶜ, D.support.2.isOpen_compl⟩ : X.Opens) hx
      obtain ⟨c⟩ := hc
      have hbot : (D.comap U.ι).support = ⊥ := by
        rw [Scheme.IdealSheafData.support_comap]
        refine le_antisymm ?_ bot_le
        intro y hy
        have h1 : U.ι.base y ∈ D.support := hy
        have h2 : U.ι.base y ∈ (U : Set ↥X) := by
          rw [← Scheme.Opens.range_ι U]
          exact Set.mem_range_self y
        exact absurd h1 (hUW h2)
      have htop : restrictIdeal D U = ⊤ := by
        rw [restrictIdeal_eq_comap_ι]
        exact (Scheme.IdealSheafData.support_eq_bot_iff _).mp hbot
      refine ⟨U, hxU, m, c, fun _ => none, ?_, ?_, ?_⟩
      · intro i hi i' hi' t ht _
        simp at ht
      · intro i hi _
        have hi0 : i = 0 := by
          simp only [List.length_singleton] at hi
          omega
        subst hi0
        simpa using htop
      · intro i hi t ht
        simp at ht


end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisibility
section

namespace FunctorialResolution.EmbeddedResolution

theorem isPrime_span_singleton_algebraMap_etaleChartCoord (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] [IsLocalRing A] (j : Fin m)
    (hj : etaleChartCoord k m S j ∈ q) :
    (Ideal.span ({algebraMap S A (etaleChartCoord k m S j)} : Set A)).IsPrime := by
  have : IsRegularLocalRing A := isRegularLocalRing_of_isLocalization_etale k m S q A
  have hJ : ∀ i ∈ ({j} : Finset (Fin m)), etaleChartCoord k m S i ∈ q := by
    intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact hj
  have hJA : ∀ i ∈ ({j} : Finset (Fin m)),
      algebraMap S A (etaleChartCoord k m S i) ∈ IsLocalRing.maximalIdeal A := by
    intro i hi
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A q _).mpr (hJ i hi)
  have hli := linearIndependent_toCotangent_etaleChartCoord k m S q A {j} hJ hJA
  exact IsRegularLocalRing.isPrime_span_singleton
    (fun i : { x : Fin m // x ∈ ({j} : Finset (Fin m)) } =>
      algebraMap S A (etaleChartCoord k m S (i : Fin m)))
    (fun i => hJA (i : Fin m) i.2) hli ⟨j, Finset.mem_singleton_self j⟩

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution.SequenceOfBlowups

variable {X : Scheme.{u}}

section
variable (s : SequenceOfBlowups X)

theorem transitionMap_def {i i' : ℕ} (h : i ≤ i') :
    s.transitionMap h = s.tower.map (homOfLE h).op := rfl

theorem transitionMap_trans {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) :
    s.transitionMap hjl ≫ s.transitionMap hij = s.transitionMap (hij.trans hjl) :=
  (s.tower.map_comp (homOfLE hjl).op (homOfLE hij).op).symm

theorem transitionMap_self {i : ℕ} (h : i ≤ i) : s.transitionMap h = 𝟙 (s.schemeAt i) := by
  rw [transitionMap_def, show (homOfLE h).op = 𝟙 (op i) from rfl, s.tower.map_id]

theorem blowupMorphism_eq_transitionMap (i : ℕ) :
    s.transitionMapSucc i = s.transitionMap (Nat.le_succ i) := rfl

theorem isBlowupAlongIdealSheaf_blowupMorphism (i : ℕ) (h : i < s.length) :
    Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc i) (s.center i) := s.isBlowup i h

theorem projectionToBase_def (i : ℕ) :
    s.projectionToBase i = s.transitionMap (Nat.zero_le i) ≫ s.isoZero.hom := rfl

theorem projectionToBase_zero : s.projectionToBase 0 = s.isoZero.hom := by
  rw [projectionToBase_def, s.transitionMap_self, Category.id_comp]

theorem projectionToBase_succ (i : ℕ) :
    s.projectionToBase (i + 1) = s.transitionMapSucc i ≫ s.projectionToBase i := by
  rw [blowupMorphism_eq_transitionMap]
  exact (s.transitionMap_comp_projectionToBase (Nat.le_succ i)).symm

theorem lastStructMap_eq_projectionToBase : s.lastStructMap = s.projectionToBase s.length := rfl


end

section
variable (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) {i i' : ℕ} (h : i ≤ i')

theorem pullbackTransitionMap_fst :
    s.pullbackTransitionMap φ h ≫ pullback.fst φ (s.projectionToBase i) = pullback.fst φ (s.projectionToBase i') :=
  Eq.trans (pullback.lift_fst _ _ _) (Category.comp_id _)

theorem pullbackTransitionMap_snd :
    s.pullbackTransitionMap φ h ≫ pullback.snd φ (s.projectionToBase i)
      = pullback.snd φ (s.projectionToBase i') ≫ s.transitionMap h :=
  pullback.lift_snd _ _ _


end

end FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
section

open CategoryTheory AlgebraicGeometry

section
namespace FunctorialResolution.EmbeddedResolution

def imageIdealSheaf {S X : Scheme.{u}} (σ : S ⟶ X) (I : S.IdealSheafData) : X.IdealSheafData :=
  (I.subschemeι ≫ σ).ker

theorem map_eq_imageIdealSheaf {S X : Scheme.{u}} (f : S ⟶ X) (I : S.IdealSheafData) :
    I.map f = imageIdealSheaf f I := rfl

theorem imageIdealSheaf_comp {W A B : Scheme.{u}} (g : W ⟶ A) (w : A ⟶ B) (I : W.IdealSheafData) :
    imageIdealSheaf (g ≫ w) I = imageIdealSheaf w (imageIdealSheaf g I) := by
  simp only [← map_eq_imageIdealSheaf, Scheme.IdealSheafData.map_comp]

theorem imageIdealSheaf_eq_ker {S X : Scheme.{u}} (σ : S ⟶ X) (I : S.IdealSheafData) :
    imageIdealSheaf σ I = (I.subschemeι ≫ σ).ker := rfl

def SequenceOfBlowups.Isomorphic {X : Scheme.{u}} (B B' : SequenceOfBlowups X) : Prop :=
  B.length = B'.length ∧
    ∃ e : ∀ i : ℕ, i ≤ B.length → (B.schemeAt i ≅ B'.schemeAt i),
      ((e 0 (Nat.zero_le _)).hom ≫ B'.isoZero.hom = B.isoZero.hom) ∧
      (∀ i : ℕ, ∀ hi : i < B.length,
        (e (i + 1) hi).hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ (e i hi.le).hom) ∧
      (∀ i : ℕ, ∀ hi : i < B.length,
        (B'.center i).comap (e i hi.le).hom = B.center i)

theorem SequenceOfBlowups.isomorphic_refl {X : Scheme.{u}} (B : SequenceOfBlowups X) : B.Isomorphic B := by
  refine ⟨rfl, fun i _ => Iso.refl _, ?_, ?_, ?_⟩ <;> simp

def IsPushforwardBlowupSeq {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X) : Prop :=
  BS.length = B.length ∧
    ∃ σ : ∀ i : ℕ, i ≤ BS.length → (BS.schemeAt i ⟶ B.schemeAt i),
      (∀ i : ℕ, ∀ hi : i ≤ BS.length, IsClosedImmersion (σ i hi)) ∧
      (σ 0 (Nat.zero_le _) ≫ B.isoZero.hom = BS.isoZero.hom ≫ j) ∧
      (∀ i : ℕ, ∀ hi : i < BS.length,
        σ (i + 1) hi ≫ B.transitionMapSucc i = BS.transitionMapSucc i ≫ σ i hi.le) ∧
      (∀ i : ℕ, ∀ hi : i < BS.length,
        B.center i = imageIdealSheaf (σ i hi.le) (BS.center i)) ∧
      (∀ i : ℕ, ∀ hi : i < BS.length,
        (σ (i + 1) hi).ker =
          Blowup.strictTransform (B.transitionMapSucc i) (B.center i) (σ i hi.le).ker)

def IsStrictPullbackBlowupSeq {X' X : Scheme.{u}} (φ : X' ⟶ X)
    (B' : SequenceOfBlowups X') (B : SequenceOfBlowups X) : Prop :=
  B'.length = B.length ∧
    ∃ σ : ∀ i : ℕ, i ≤ B'.length → (B'.schemeAt i ⟶ B.schemeAt i),
      (σ 0 (Nat.zero_le _) ≫ B.isoZero.hom = B'.isoZero.hom ≫ φ) ∧
      (∀ i : ℕ, ∀ hi : i < B'.length,
        IsPullback (σ (i + 1) hi) (B'.transitionMapSucc i) (B.transitionMapSucc i) (σ i hi.le)) ∧
      (∀ i : ℕ, ∀ hi : i < B'.length,
        B'.center i = (B.center i).comap (σ i hi.le))

private def schemeAtHomOfEqZero_consolidated57 {X' X : Scheme.{u}} (g : X' ⟶ X) (t : SequenceOfBlowups X') (s : SequenceOfBlowups X)
    (i : ℕ) (hi0 : i = 0) : t.schemeAt i ⟶ s.schemeAt i :=
  eqToHom (congrArg t.schemeAt hi0) ≫ t.isoZero.hom ≫ g ≫ s.isoZero.inv ≫
    eqToHom (congrArg s.schemeAt hi0).symm

section
variable {X' X : Scheme.{u}}

theorem IsStrictPullbackBlowupSeq.of_length_zero (g : X' ⟶ X) (t : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) (ht : t.length = 0) (hs : s.length = 0) :
    IsStrictPullbackBlowupSeq g t s := by
  refine ⟨ht.trans hs.symm,
    fun i hi => schemeAtHomOfEqZero_consolidated57 g t s i (Nat.eq_zero_of_le_zero (le_of_le_of_eq hi ht)),
    ?_, ?_, ?_⟩
  · simp [schemeAtHomOfEqZero_consolidated57]
  · intro i hi
    exact absurd (lt_of_lt_of_eq hi ht) (Nat.not_lt_zero i)
  · intro i hi
    exact absurd (lt_of_lt_of_eq hi ht) (Nat.not_lt_zero i)

theorem IsStrictPullbackBlowupSeq.length_eq {φ : X' ⟶ X}
    {B' : SequenceOfBlowups X'} {B : SequenceOfBlowups X} (h : IsStrictPullbackBlowupSeq φ B' B) :
    B'.length = B.length := h.1


end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

def StrictNormalCrossingsRestrictToClopen : Prop :=
  ∀ (k : Type u) [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))
    [Smooth p] (E : List W.IdealSheafData) (Z : W.IdealSheafData),
    InStrictNormalCrossingPosition p E → HasStrictNormalCrossingsWith p Z E →
    ∀ U : (Z.subscheme).Opens, IsClosed (U : Set ↥(Z.subscheme)) →
    (∀ D ∈ E, ∀ T ∈ irreducibleComponents (↥(U.toScheme)),
        ¬ ((U.ι ≫ Z.subschemeι).base '' T) ⊆ (D.support : Set ↥W)) →
    IsStrictNormalCrossingsDivisor ((E.prod.comap (U.ι ≫ Z.subschemeι)).radical)

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.RemoveIsoBlowups
section

open CategoryTheory AlgebraicGeometry Opposite

namespace FunctorialResolution.EmbeddedResolution

namespace SequenceOfBlowups

variable {X : Scheme.{u}}

section
variable (s : SequenceOfBlowups X)

private theorem isIso_transitionMap_refl_consolidated112 {i : ℕ} (h : i ≤ i) :
    IsIso (s.transitionMap h) := by
  have he : (homOfLE h : i ⟶ i).op = 𝟙 (Opposite.op i) := rfl
  have hid : s.transitionMap h = 𝟙 (s.schemeAt i) := by
    rw [SequenceOfBlowups.transitionMap_def, he]
    exact s.tower.map_id (Opposite.op i)
  rw [hid]
  infer_instance

theorem isIso_transitionMap_of_center_eq_top {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ s.length) (h : ∀ i, a ≤ i → i < b → s.center i = ⊤) :
    IsIso (s.transitionMap hab) := by
  revert hb h
  induction b, hab using Nat.le_induction with
  | base =>
    intro _ _
    exact isIso_transitionMap_refl_consolidated112 s _
  | succ b hab ih =>
    intro hb h
    have hbl : b ≤ s.length := le_trans (Nat.le_succ b) hb
    have hlt : b < s.length := lt_of_lt_of_le (Nat.lt_succ_self b) hb
    have hcen : s.center b = ⊤ := h b hab (Nat.lt_succ_self b)
    have : IsIso (s.transitionMap hab) :=
      ih hbl fun i hi hib => h i hi (Nat.lt_succ_of_lt hib)
    have hB : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc b) (s.center b) := s.isBlowupAlongIdealSheaf_blowupMorphism b hlt
    rw [hcen] at hB
    have : IsIso (s.transitionMap (Nat.le_succ b)) := by
      have h4 := hB.isIso_of_top
      rw [s.blowupMorphism_eq_transitionMap b] at h4
      exact h4
    have h3 : IsIso (s.transitionMap (Nat.le_succ b) ≫ s.transitionMap hab) := inferInstance
    rw [s.transitionMap_trans hab (Nat.le_succ b)] at h3
    exact h3

theorem exists_le_center_ne_top_or_length_le (a : ℕ) :
    ∃ i, a ≤ i ∧ (s.center i ≠ ⊤ ∨ s.length ≤ i) :=
  ⟨max a s.length, le_max_left _ _, Or.inr (le_max_right _ _)⟩


end

noncomputable def nextNontrivialIndex (s : SequenceOfBlowups X) (a : ℕ) : ℕ :=
  @Nat.find _ (fun _ => Classical.propDecidable _) (s.exists_le_center_ne_top_or_length_le a)

section
variable (s : SequenceOfBlowups X) (a : ℕ)

theorem nextNontrivialIndex_spec :
    a ≤ s.nextNontrivialIndex a ∧ (s.center (s.nextNontrivialIndex a) ≠ ⊤ ∨ s.length ≤ s.nextNontrivialIndex a) :=
  @Nat.find_spec _ (fun _ => Classical.propDecidable _) (s.exists_le_center_ne_top_or_length_le a)

theorem le_nextNontrivialIndex : a ≤ s.nextNontrivialIndex a :=
  (s.nextNontrivialIndex_spec a).1

theorem center_nextNontrivialIndex_ne_top_or_length_le :
    s.center (s.nextNontrivialIndex a) ≠ ⊤ ∨ s.length ≤ s.nextNontrivialIndex a :=
  (s.nextNontrivialIndex_spec a).2


end

section
variable (s : SequenceOfBlowups X)

theorem nextNontrivialIndex_le {a i : ℕ} (hi : a ≤ i)
    (h : s.center i ≠ ⊤ ∨ s.length ≤ i) : s.nextNontrivialIndex a ≤ i :=
  @Nat.find_min' _ (fun _ => Classical.propDecidable _) (s.exists_le_center_ne_top_or_length_le a) i ⟨hi, h⟩

theorem nextNontrivialIndex_le_length {a : ℕ} (h : a ≤ s.length) :
    s.nextNontrivialIndex a ≤ s.length :=
  s.nextNontrivialIndex_le h (Or.inr le_rfl)

theorem center_eq_top_of_lt_nextNontrivialIndex {a i : ℕ} (hai : a ≤ i)
    (h : i < s.nextNontrivialIndex a) : s.center i = ⊤ := by
  by_contra hc
  exact absurd (s.nextNontrivialIndex_le hai (Or.inl hc)) (not_le.mpr h)


end

noncomputable def nontrivialIndex (s : SequenceOfBlowups X) (j : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (s.nextNontrivialIndex 0) (fun _ ih => s.nextNontrivialIndex (ih + 1)) j

section
variable (s : SequenceOfBlowups X)

@[simp] theorem nontrivialIndex_zero : s.nontrivialIndex 0 = s.nextNontrivialIndex 0 := rfl

@[simp] theorem nontrivialIndex_succ (j : ℕ) :
    s.nontrivialIndex (j + 1) = s.nextNontrivialIndex (s.nontrivialIndex j + 1) := rfl

theorem nontrivialIndex_lt_succ (j : ℕ) : s.nontrivialIndex j < s.nontrivialIndex (j + 1) := by
  have h := s.le_nextNontrivialIndex (s.nontrivialIndex j + 1)
  rw [nontrivialIndex_succ]
  exact h

theorem succ_le_nontrivialIndex_succ (j : ℕ) :
    s.nontrivialIndex j + 1 ≤ s.nontrivialIndex (j + 1) :=
  s.nontrivialIndex_lt_succ j

theorem nontrivialIndex_strictMono : StrictMono s.nontrivialIndex :=
  strictMono_nat_of_lt_succ s.nontrivialIndex_lt_succ

theorem nontrivialIndex_monotone : Monotone s.nontrivialIndex :=
  s.nontrivialIndex_strictMono.monotone

theorem le_nontrivialIndex (j : ℕ) : j ≤ s.nontrivialIndex j :=
  s.nontrivialIndex_strictMono.le_apply

theorem center_nontrivialIndex_ne_top_or_length_le (j : ℕ) :
    s.center (s.nontrivialIndex j) ≠ ⊤ ∨ s.length ≤ s.nontrivialIndex j := by
  cases j with
  | zero => exact s.center_nextNontrivialIndex_ne_top_or_length_le 0
  | succ j => exact s.center_nextNontrivialIndex_ne_top_or_length_le (s.nontrivialIndex j + 1)

theorem center_eq_top_of_lt_nontrivialIndex_zero {i : ℕ} (h : i < s.nontrivialIndex 0) :
    s.center i = ⊤ :=
  s.center_eq_top_of_lt_nextNontrivialIndex (Nat.zero_le i) h

theorem center_eq_top_of_nontrivialIndex_lt {i j : ℕ} (h1 : s.nontrivialIndex j < i)
    (h2 : i < s.nontrivialIndex (j + 1)) : s.center i = ⊤ :=
  s.center_eq_top_of_lt_nextNontrivialIndex h1 h2

theorem exists_length_le_nontrivialIndex : ∃ j, s.length ≤ s.nontrivialIndex j :=
  ⟨s.length, s.le_nontrivialIndex s.length⟩


end

noncomputable def lengthWithoutIsoBlowups (s : SequenceOfBlowups X) : ℕ :=
  @Nat.find _ (fun _ => Classical.propDecidable _) s.exists_length_le_nontrivialIndex

section
variable (s : SequenceOfBlowups X)

theorem length_le_nontrivialIndex_lengthWithoutIsoBlowups :
    s.length ≤ s.nontrivialIndex s.lengthWithoutIsoBlowups :=
  @Nat.find_spec _ (fun _ => Classical.propDecidable _) s.exists_length_le_nontrivialIndex

private theorem nontrivialIndex_le_length_of_forall_lt_consolidated112 (j : ℕ)
    (h : ∀ i, i < j → s.nontrivialIndex i < s.length) : s.nontrivialIndex j ≤ s.length := by
  cases j with
  | zero =>
      show s.nextNontrivialIndex 0 ≤ s.length
      exact s.nextNontrivialIndex_le_length (Nat.zero_le _)
  | succ j =>
      have hj : s.nontrivialIndex j < s.length := h j (Nat.lt_succ_self j)
      show s.nextNontrivialIndex (s.nontrivialIndex j + 1) ≤ s.length
      exact s.nextNontrivialIndex_le_length hj

theorem nontrivialIndex_lengthWithoutIsoBlowups : s.nontrivialIndex s.lengthWithoutIsoBlowups = s.length := by
  refine le_antisymm (nontrivialIndex_le_length_of_forall_lt_consolidated112 s s.lengthWithoutIsoBlowups ?_)
    s.length_le_nontrivialIndex_lengthWithoutIsoBlowups
  intro i hi
  have hmin := @Nat.find_min _ (fun _ => Classical.propDecidable _)
    s.exists_length_le_nontrivialIndex i hi
  exact not_le.mp hmin

theorem nontrivialIndex_lt_length {j : ℕ} (h : j < s.lengthWithoutIsoBlowups) :
    s.nontrivialIndex j < s.length := by
  have h' : ¬ (s.length ≤ s.nontrivialIndex j) :=
    @Nat.find_min _ (fun _ => Classical.propDecidable _) s.exists_length_le_nontrivialIndex j h
  exact not_le.mp h'

theorem nontrivialIndex_le_length {j : ℕ} (h : j ≤ s.lengthWithoutIsoBlowups) :
    s.nontrivialIndex j ≤ s.length := by
  cases j with
  | zero => exact s.nextNontrivialIndex_le_length (Nat.zero_le _)
  | succ i =>
    have hi : i < s.lengthWithoutIsoBlowups := lt_of_lt_of_le (Nat.lt_succ_self i) h
    have hlt : s.nontrivialIndex i + 1 ≤ s.length := s.nontrivialIndex_lt_length hi
    exact s.nextNontrivialIndex_le_length hlt

theorem center_nontrivialIndex_ne_top {j : ℕ} (h : j < s.lengthWithoutIsoBlowups) :
    s.center (s.nontrivialIndex j) ≠ ⊤ := by
  rcases s.center_nontrivialIndex_ne_top_or_length_le j with hc | hc
  · exact hc
  · exact absurd hc (not_le.mpr (s.nontrivialIndex_lt_length h))

theorem isIso_transitionMap_nontrivialIndex_zero :
    IsIso (s.transitionMap (Nat.zero_le (s.nontrivialIndex 0))) := by
  refine s.isIso_transitionMap_of_center_eq_top (Nat.zero_le (s.nontrivialIndex 0)) ?_ ?_
  · exact s.nextNontrivialIndex_le_length (Nat.zero_le _)
  · intro i _ hi
    exact s.center_eq_top_of_lt_nontrivialIndex_zero hi

theorem isIso_transitionMap_nontrivialIndex_succ {j : ℕ} (h : j < s.lengthWithoutIsoBlowups) :
    IsIso (s.transitionMap (s.succ_le_nontrivialIndex_succ j)) := by
  refine s.isIso_transitionMap_of_center_eq_top (s.succ_le_nontrivialIndex_succ j)
    (s.nontrivialIndex_le_length (Nat.succ_le_of_lt h)) ?_
  intro i hi hib
  exact s.center_eq_top_of_nontrivialIndex_lt (Nat.lt_of_succ_le hi) hib


end

noncomputable def objNontrivialIndexZeroIso (s : SequenceOfBlowups X) : s.schemeAt (s.nontrivialIndex 0) ≅ X :=
  haveI : IsIso (s.transitionMap (Nat.zero_le (s.nontrivialIndex 0))) := s.isIso_transitionMap_nontrivialIndex_zero
  (asIso (s.transitionMap (Nat.zero_le (s.nontrivialIndex 0)))).trans s.isoZero

theorem objNontrivialIndexZeroIso_hom (s : SequenceOfBlowups X) :
    s.objNontrivialIndexZeroIso.hom = s.projectionToBase (s.nontrivialIndex 0) := by
  rw [projectionToBase_def]
  rfl

noncomputable def towerWithoutIsoBlowups (s : SequenceOfBlowups X) : ℕᵒᵖ ⥤ Scheme.{u} :=
  (Monotone.functor s.nontrivialIndex_monotone).op ⋙ s.tower

private theorem isBlowupAlongIdealSheaf_towerWithoutIsoBlowups_map_consolidated112 (s : SequenceOfBlowups X) (i : ℕ) (hi : i < s.lengthWithoutIsoBlowups) :
    Blowup.IsBlowupAlongIdealSheaf (s.towerWithoutIsoBlowups.map (homOfLE (Nat.le_succ i)).op) (s.center (s.nontrivialIndex i)) := by
  have : IsIso (s.transitionMap (s.succ_le_nontrivialIndex_succ i)) := s.isIso_transitionMap_nontrivialIndex_succ hi
  have hB : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc (s.nontrivialIndex i)) (s.center (s.nontrivialIndex i)) :=
    s.isBlowupAlongIdealSheaf_blowupMorphism (s.nontrivialIndex i) (s.nontrivialIndex_lt_length hi)
  have hcomp := hB.iso_hom_comp (asIso (s.transitionMap (s.succ_le_nontrivialIndex_succ i)))
  have heq : (asIso (s.transitionMap (s.succ_le_nontrivialIndex_succ i))).hom ≫ s.transitionMapSucc (s.nontrivialIndex i)
      = s.transitionMap (s.nontrivialIndex_monotone (Nat.le_succ i)) := by
    rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
    exact s.transitionMap_trans (Nat.le_succ (s.nontrivialIndex i)) (s.succ_le_nontrivialIndex_succ i)
  rw [heq] at hcomp
  show Blowup.IsBlowupAlongIdealSheaf (s.transitionMap (s.nontrivialIndex_monotone (Nat.le_succ i))) (s.center (s.nontrivialIndex i))
  exact hcomp

noncomputable def withoutIsoBlowups (s : SequenceOfBlowups X) : SequenceOfBlowups X where
  length := s.lengthWithoutIsoBlowups
  tower := s.towerWithoutIsoBlowups
  isoZero := s.objNontrivialIndexZeroIso
  center := fun j => s.center (s.nontrivialIndex j)
  isBlowup := s.isBlowupAlongIdealSheaf_towerWithoutIsoBlowups_map_consolidated112

section
variable (s : SequenceOfBlowups X)

@[simp] theorem withoutIsoBlowups_length : s.withoutIsoBlowups.length = s.lengthWithoutIsoBlowups := rfl

@[simp] theorem withoutIsoBlowups_center (j : ℕ) :
    s.withoutIsoBlowups.center j = s.center (s.nontrivialIndex j) := rfl

theorem withoutIsoBlowups_isoObjZero : s.withoutIsoBlowups.isoZero = s.objNontrivialIndexZeroIso := rfl

theorem withoutIsoBlowups_transitionMap {j j' : ℕ} (h : j ≤ j') :
    s.withoutIsoBlowups.transitionMap h = s.transitionMap (s.nontrivialIndex_monotone h) := by
  rw [SequenceOfBlowups.transitionMap_def, SequenceOfBlowups.transitionMap_def]
  rfl

theorem withoutIsoBlowups_blowupMorphism (j : ℕ) :
    s.withoutIsoBlowups.transitionMapSucc j = s.transitionMap (s.nontrivialIndex_monotone (Nat.le_succ j)) := by
  rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, withoutIsoBlowups_transitionMap]

theorem withoutIsoBlowups_center_ne_top {j : ℕ} (h : j < s.withoutIsoBlowups.length) :
    s.withoutIsoBlowups.center j ≠ ⊤ := by
  exact s.center_nontrivialIndex_ne_top h

theorem withoutIsoBlowups_lastObj : s.withoutIsoBlowups.lastObj = s.lastObj :=
  congrArg s.schemeAt s.nontrivialIndex_lengthWithoutIsoBlowups

private theorem projectionToBase_eq_eqToHom_comp_consolidated112 {a b : ℕ} (h : a = b) :
    s.projectionToBase a = eqToHom (congrArg s.schemeAt h) ≫ s.projectionToBase b := by
  subst h
  simp

theorem withoutIsoBlowups_projectionToBase_eq_nontrivialIndex (j : ℕ) :
    s.withoutIsoBlowups.projectionToBase j = s.projectionToBase (s.nontrivialIndex j) := by
  have h0 : s.withoutIsoBlowups.isoZero.hom = s.projectionToBase (s.nontrivialIndex 0) := s.objNontrivialIndexZeroIso_hom
  rw [projectionToBase_def, withoutIsoBlowups_transitionMap, h0]
  exact s.transitionMap_comp_projectionToBase _

theorem withoutIsoBlowups_lastStructMap :
    s.withoutIsoBlowups.lastStructMap = eqToHom s.withoutIsoBlowups_lastObj ≫ s.lastStructMap := by
  have h0 : s.withoutIsoBlowups.isoZero.hom = s.projectionToBase (s.nontrivialIndex 0) := s.objNontrivialIndexZeroIso_hom
  have h1 : s.withoutIsoBlowups.lastStructMap = s.projectionToBase (s.nontrivialIndex s.withoutIsoBlowups.length) := by
    rw [lastStructMap_eq_projectionToBase, projectionToBase_def, withoutIsoBlowups_transitionMap, h0]
    exact s.transitionMap_comp_projectionToBase _
  rw [h1, lastStructMap_eq_projectionToBase]
  exact projectionToBase_eq_eqToHom_comp_consolidated112 s s.nontrivialIndex_lengthWithoutIsoBlowups

theorem withoutIsoBlowups_centersLieOver {S : Set X} (h : s.CentersLieOver S) :
    s.withoutIsoBlowups.CentersLieOver S := by
  intro j hj x hx
  have hx' : x ∈ (s.center (s.nontrivialIndex j)).support := hx
  have h2 := h (s.nontrivialIndex j) (s.nontrivialIndex_lt_length hj) x hx'
  rw [withoutIsoBlowups_projectionToBase_eq_nontrivialIndex]
  exact h2


end

end SequenceOfBlowups

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.IsoAwayFromCenters
section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

namespace FunctorialResolution.EmbeddedResolution

private theorem isIso_restrict_comp_consolidated169 {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (V : Z.Opens)
    (h1 : IsIso (f ∣_ (g ⁻¹ᵁ V))) (h2 : IsIso (g ∣_ V)) : IsIso ((f ≫ g) ∣_ V) := by
  have := h1
  have := h2
  have h : IsIso (f ∣_ (g ⁻¹ᵁ V) ≫ g ∣_ V) := inferInstance
  rw [morphismRestrict_comp]
  exact h

section
variable {X : Scheme.{u}} (s : SequenceOfBlowups X) (S : Set X) (U : X.Opens) (hU : Disjoint (U : Set X) S) (hs : s.CentersLieOver S)
include hU hs

private theorem isIso_restrict_projectionToBase_of_centersLieOver_consolidated169 (i : ℕ) (hi : i ≤ s.length) :
    IsIso (s.projectionToBase i ∣_ U) := by
  revert hi
  induction i with
  | zero =>
    intro _
    show IsIso (s.projectionToBase 0 ∣_ U)
    have h0 : (homOfLE (Nat.zero_le 0) : (0 : ℕ) ⟶ 0).op = 𝟙 (op (0 : ℕ)) := rfl
    have : IsIso (s.projectionToBase 0) := by
      rw [SequenceOfBlowups.projectionToBase_def, SequenceOfBlowups.transitionMap_def, h0, CategoryTheory.Functor.map_id,
        Category.id_comp]
      infer_instance
    infer_instance
  | succ i ih =>
    intro hi
    have hi' : i < s.length := hi
    have h2 : IsIso (s.projectionToBase i ∣_ U) := ih (Nat.le_of_succ_le hi)
    have hcomp : s.transitionMapSucc i ≫ s.projectionToBase i = s.projectionToBase (i + 1) :=
      s.transitionMap_comp_projectionToBase (Nat.le_succ i)
    have hb : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc i) (s.center i) := s.isBlowupAlongIdealSheaf_blowupMorphism i hi'
    have hres := hb.restrict (s.projectionToBase i ⁻¹ᵁ U)
    have htop : (s.center i).comap (s.projectionToBase i ⁻¹ᵁ U).ι = ⊤ := by
      apply Blowup.comap_eq_top_of_notMem_support
      intro x hx
      have h1 := hs i hi' ((s.projectionToBase i ⁻¹ᵁ U).ι.base x) hx
      have hxV : (s.projectionToBase i ⁻¹ᵁ U).ι.base x
          ∈ ((s.projectionToBase i ⁻¹ᵁ U : (s.schemeAt i).Opens) : Set (s.schemeAt i)) := by
        rw [← Scheme.Opens.range_ι]
        exact Set.mem_range_self x
      have h2' : (s.projectionToBase i).base ((s.projectionToBase i ⁻¹ᵁ U).ι.base x) ∈ (U : Set X) := hxV
      exact Set.disjoint_left.mp hU h2' h1
    rw [htop] at hres
    have h1 : IsIso (s.transitionMapSucc i ∣_ (s.projectionToBase i ⁻¹ᵁ U)) := hres.isIso_of_top
    have key : IsIso ((s.transitionMapSucc i ≫ s.projectionToBase i) ∣_ U) :=
      isIso_restrict_comp_consolidated169 (s.transitionMapSucc i) (s.projectionToBase i) U h1 h2
    rw [hcomp] at key
    exact key

theorem isIso_restrict_lastStructMap_of_centersLieOver :
    IsIso (s.lastStructMap ∣_ U) := by
  rw [SequenceOfBlowups.lastStructMap_eq_projectionToBase]
  exact isIso_restrict_projectionToBase_of_centersLieOver_consolidated169 s S U hU hs s.length le_rfl


end

theorem isIso_restrict_lastStructMap_smoothLocus {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFinitePresentation f] (s : SequenceOfBlowups X)
    (hs : s.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds X) : Set X)) :
    IsIso (s.lastStructMap ∣_ f.smoothLocus) := by
  refine isIso_restrict_lastStructMap_of_centersLieOver s _ f.smoothLocus ?_ hs
  show Disjoint (f.smoothLocus : Set X) ((f.smoothLocus : Set X)ᶜ)
  exact disjoint_compl_right

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

def strictTransformOpens {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    ((D.comap π).subscheme).Opens :=
  (D.comap π).subschemeι ⁻¹ᵁ (Z.comap π).support.compl

theorem coe_strictTransformOpens {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    ((strictTransformOpens π Z D : ((D.comap π).subscheme).Opens) :
        Set ((D.comap π).subscheme)) =
      ⇑(D.comap π).subschemeι.base ⁻¹' ((Z.comap π).support.compl : Set X₁) := rfl

def strictTransformι {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    (strictTransformOpens π Z D).toScheme ⟶ X₁ :=
  Scheme.Opens.ι (strictTransformOpens π Z D) ≫ (D.comap π).subschemeι

section
variable {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData)

theorem strictTransformι_eq_ι_comp_subschemeι :
    strictTransformι π Z D =
      Scheme.Opens.ι (strictTransformOpens π Z D) ≫ (D.comap π).subschemeι := rfl





theorem strictTransform_eq_ker_strictTransformι :
    Blowup.strictTransform π Z D = (strictTransformι π Z D).ker := rfl


end

private theorem ker_ideal_eq_ker_app_consolidated191 {W Z : Scheme.{u}} (g : W ⟶ Z) [QuasiCompact g]
    (U : Z.affineOpens) :
    (Scheme.Hom.ker g).ideal U = RingHom.ker (CommRingCat.Hom.hom (g.app U.1)) := by
  simp

private theorem range_comp_eq_image_range_consolidated191 {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range ⇑(f ≫ g) = ⇑g '' Set.range ⇑f := by
  ext x
  simp [Set.range_comp]

theorem ker_eq_ker_of_isIso_comp {A B T : Scheme.{u}} (f : A ⟶ T) (g : B ⟶ T) (e : A ⟶ B)
    [IsIso e] (h : e ≫ g = f) : f.ker = g.ker := by
  subst h; exact Scheme.Hom.ker_comp_of_isIso e g

private theorem image_preimage_ι_of_le_consolidated191 {X : Scheme.{u}} (U O : X.Opens) (h : O ≤ U) :
    Scheme.Opens.ι U ''ᵁ (Scheme.Opens.ι U ⁻¹ᵁ O) = O := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    exact hy
  · intro x hx
    exact ⟨⟨x, h hx⟩, hx, rfl⟩

theorem ker_comap_ι_eq_ker_morphismRestrict {W T : Scheme.{u}} (m : W ⟶ T) [QuasiCompact m]
    (V : T.Opens) :
    (Scheme.Hom.ker m).comap (Scheme.Opens.ι V) = Scheme.Hom.ker (m ∣_ V) := by
  refine Scheme.IdealSheafData.ext ?_
  funext P
  have hQaff : IsAffineOpen (Scheme.Opens.ι V ''ᵁ P.1) :=
    P.2.image_of_isOpenImmersion (Scheme.Opens.ι V)
  have hpre : Scheme.Opens.ι V ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) = P.1 :=
    (Scheme.Opens.ι V).preimage_image_eq P.1
  have e : P.1 ≤ Scheme.Opens.ι V ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) := hpre.ge
  have hpre2 : ((m ∣_ V) ⁻¹ᵁ P.1)
      = Scheme.Opens.ι (m ⁻¹ᵁ V) ⁻¹ᵁ (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) := by
    rw [← Scheme.Hom.comp_preimage, ← morphismRestrict_ι, Scheme.Hom.comp_preimage, hpre]
  have hQV : (Scheme.Opens.ι V ''ᵁ P.1) ≤ V := Scheme.Opens.ι_image_le V P.1
  have hle : m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) ≤ m ⁻¹ᵁ V := fun x hx => hQV hx
  have himg : Scheme.Opens.ι (m ⁻¹ᵁ V) ''ᵁ ((m ∣_ V) ⁻¹ᵁ P.1)
      = m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) := by
    rw [hpre2]
    exact image_preimage_ι_of_le_consolidated191 (m ⁻¹ᵁ V) (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) hle
  have hbij := IsOpenImmersion.bijective_appLE_of_image_eq (Scheme.Opens.ι V)
    (Scheme.Opens.ι V ''ᵁ P.1) P.1 e rfl
  have hinj := (IsOpenImmersion.bijective_appLE_of_image_eq (Scheme.Opens.ι (m ⁻¹ᵁ V))
    (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le himg).1
  have hsq : Scheme.Hom.appLE (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1 e ≫
        (m ∣_ V).app P.1
      = m.app (Scheme.Opens.ι V ''ᵁ P.1) ≫
        Scheme.Hom.appLE (Scheme.Opens.ι (m ⁻¹ᵁ V))
          (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le := by
    rw [Scheme.Hom.app_eq_appLE (m ∣_ V), Scheme.Hom.app_eq_appLE m,
      Scheme.Hom.appLE_comp_appLE (m ∣_ V) (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1
        ((m ∣_ V) ⁻¹ᵁ P.1) e le_rfl,
      Scheme.Hom.appLE_comp_appLE (Scheme.Opens.ι (m ⁻¹ᵁ V)) m (Scheme.Opens.ι V ''ᵁ P.1)
        (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) le_rfl hpre2.le]
    exact Scheme.Hom.appLE_congr_hom (morphismRestrict_ι m V) ..
  have hsqr : ∀ x, (CommRingCat.Hom.hom ((m ∣_ V).app P.1))
        ((CommRingCat.Hom.hom
          (Scheme.Hom.appLE (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1 e)) x)
      = (CommRingCat.Hom.hom (Scheme.Hom.appLE (Scheme.Opens.ι (m ⁻¹ᵁ V))
          (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le))
        ((CommRingCat.Hom.hom (m.app (Scheme.Opens.ι V ''ᵁ P.1))) x) := by
    intro x
    have h' := congrArg (fun mm => (CommRingCat.Hom.hom mm) x) hsq
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h'
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ (Scheme.Opens.ι V)
      ⟨Scheme.Opens.ι V ''ᵁ P.1, hQaff⟩ P e,
    ker_ideal_eq_ker_app_consolidated191 m ⟨Scheme.Opens.ι V ''ᵁ P.1, hQaff⟩, ker_ideal_eq_ker_app_consolidated191 (m ∣_ V) P]
  dsimp only
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, hsqr x]
    rw [RingHom.mem_ker] at hx
    rw [hx, map_zero]
  · intro y hy
    rw [RingHom.mem_ker] at hy
    obtain ⟨x, rfl⟩ := hbij.2 y
    refine Ideal.mem_map_of_mem _ ?_
    rw [RingHom.mem_ker]
    apply hinj
    rw [← hsqr x, hy, map_zero]

theorem ker_comap_ι_eq_ker_of_isIso_comp {W T S : Scheme.{u}} (m : W ⟶ T) [QuasiCompact m]
    (V : T.Opens) (n : S ⟶ V.toScheme) (e : S ⟶ (m ⁻¹ᵁ V).toScheme) [IsIso e]
    (h : e ≫ (m ∣_ V) = n) :
    (Scheme.Hom.ker m).comap (Scheme.Opens.ι V) = Scheme.Hom.ker n := by
  rw [ker_comap_ι_eq_ker_morphismRestrict m V, ker_eq_ker_of_isIso_comp n (m ∣_ V) e h]

section
variable {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData)

theorem support_strictTransform_eq_closure_preimage [QuasiCompact (strictTransformι π Z D)] :
    ((Blowup.strictTransform π Z D).support : Set X₁) =
      closure (⇑π.base ⁻¹' ((D.support : Set X) \ (Z.support : Set X))) := by
  have h1 : (((Z.comap π).support.compl : X₁.Opens) : Set X₁) =
      (⇑π.base ⁻¹' (Z.support : Set X))ᶜ := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have h2 : (((D.comap π).support : Closeds X₁) : Set X₁) =
      ⇑π.base ⁻¹' (D.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  rw [strictTransform_eq_ker_strictTransformι, Scheme.Hom.support_ker]
  congr 1
  rw [strictTransformι_eq_ι_comp_subschemeι, range_comp_eq_image_range_consolidated191, Scheme.Opens.range_ι,
    coe_strictTransformOpens, Set.image_preimage_eq_inter_range,
    Scheme.IdealSheafData.range_subschemeι, h1, h2]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage, Set.mem_sdiff]
  tauto

theorem support_strictTransform_eq_closure_sdiff [QuasiCompact (strictTransformι π Z D)] :
    ((Blowup.strictTransform π Z D).support : Set X₁) =
      closure (((D.comap π).support : Set X₁) \ ((Z.comap π).support : Set X₁)) := by
  have h1 : (((Z.comap π).support : Closeds X₁) : Set X₁) =
      ⇑π.base ⁻¹' (Z.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have h2 : (((D.comap π).support : Closeds X₁) : Set X₁) =
      ⇑π.base ⁻¹' (D.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  rw [support_strictTransform_eq_closure_preimage π Z D, h1, h2, Set.preimage_sdiff]

theorem comap_le_strictTransform :
    D.comap π ≤ Blowup.strictTransform π Z D := by
  rw [strictTransform_eq_ker_strictTransformι, strictTransformι_eq_ι_comp_subschemeι]
  calc D.comap π = (D.comap π).subschemeι.ker :=
        (Scheme.IdealSheafData.ker_subschemeι _).symm
    _ ≤ _ := Scheme.Hom.le_ker_comp _ _


end

theorem strictTransform_top {X' X : Scheme.{u}} (f : X' ⟶ X) (Z : X.IdealSheafData) :
    Blowup.strictTransform f Z (⊤ : X.IdealSheafData) = ⊤ := by
  have h := comap_le_strictTransform f Z ⊤
  rw [Scheme.IdealSheafData.comap_top] at h
  exact le_antisymm le_top h

theorem comap_ker_subschemeι_comp {A B : Scheme.{u}} (K : A.IdealSheafData) (f : A ⟶ B)
    [IsOpenImmersion f] [QuasiCompact K.subschemeι] [QuasiCompact (K.subschemeι ≫ f)] :
    (K.subschemeι ≫ f).ker.comap f = K := by
  rw [Blowup.comap_ker_comp_of_isOpenImmersion, Scheme.IdealSheafData.ker_subschemeι]

section
variable {T : Scheme.{u}} (K : T.IdealSheafData) (V : T.Opens)

private theorem ker_morphismRestrict_subschemeι_consolidated191 :
    (K.subschemeι ∣_ V).ker = K.comap (Scheme.Opens.ι V) := by
  have h := isPullback_morphismRestrict K.subschemeι V
  have hfac : h.isoPullback.hom ≫ Limits.pullback.fst (Scheme.Opens.ι V) K.subschemeι
      = K.subschemeι ∣_ V := h.isoPullback_hom_fst
  show (K.subschemeι ∣_ V).ker = (Limits.pullback.fst (Scheme.Opens.ι V) K.subschemeι).ker
  rw [← hfac, Scheme.Hom.ker_comp_of_isIso]

private theorem exists_isIso_subschemeι_preimage_comap_consolidated191 :
    ∃ e : (K.subschemeι ⁻¹ᵁ V).toScheme ⟶ (K.comap (Scheme.Opens.ι V)).subscheme,
      IsIso e ∧ e ≫ (K.comap (Scheme.Opens.ι V)).subschemeι = K.subschemeι ∣_ V := by
  have hk : (K.subschemeι ∣_ V).ker = (K.comap (Scheme.Opens.ι V)).subschemeι.ker := by
    rw [ker_morphismRestrict_subschemeι_consolidated191, Scheme.IdealSheafData.ker_subschemeι]
  refine ⟨IsClosedImmersion.lift (K.comap (Scheme.Opens.ι V)).subschemeι
      (K.subschemeι ∣_ V) (le_of_eq hk.symm), ?_, IsClosedImmersion.lift_fac _ _ _⟩
  exact IsClosedImmersion.isIso_of_ker_eq (K.subschemeι ∣_ V)
    (K.comap (Scheme.Opens.ι V)).subschemeι _ (IsClosedImmersion.lift_fac _ _ _) hk

theorem ker_ι_preimage_comp_subschemeι_eq_ker_comap :
    (Scheme.Opens.ι (K.subschemeι ⁻¹ᵁ V) ≫ K.subschemeι).ker =
      ((K.comap (Scheme.Opens.ι V)).subschemeι ≫ Scheme.Opens.ι V).ker := by
  obtain ⟨e, he, hfac⟩ := exists_isIso_subschemeι_preimage_comap_consolidated191 K V
  have := he
  rw [← morphismRestrict_ι K.subschemeι V, ← hfac, Category.assoc]
  exact Scheme.Hom.ker_comp_of_isIso e _


end

section
variable {X X₁ : Scheme.{u}}

theorem isReduced_subscheme_strictTransform (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) (h : Blowup.IsBlowupAlongIdealSheaf π Z) [IsReduced D.subscheme]
    [QuasiCompact (strictTransformι π Z D)] :
    IsReduced (Blowup.strictTransform π Z D).subscheme := by
  have h1 := h.restrict Z.support.compl
  rw [Blowup.comap_ι_support_compl_eq_top Z] at h1
  have : IsIso (π ∣_ Z.support.compl) := h1.isIso_of_top
  have hsupp : (Z.comap π).support.compl = π ⁻¹ᵁ Z.support.compl := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hcc : (D.comap π).comap (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl))
      = (D.comap (Scheme.Opens.ι Z.support.compl)).comap (π ∣_ Z.support.compl) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  obtain ⟨e₁, he₁, -⟩ := exists_isIso_subschemeι_preimage_comap_consolidated191 (D.comap π) (π ⁻¹ᵁ Z.support.compl)
  obtain ⟨e₂, he₂, -⟩ :=
    Scheme.IdealSheafData.exists_iso_subscheme_comap_of_isIso (π ∣_ Z.support.compl)
      (D.comap (Scheme.Opens.ι Z.support.compl))
  obtain ⟨e₃, he₃, -⟩ := exists_isIso_subschemeι_preimage_comap_consolidated191 D Z.support.compl
  have := he₁
  have := he₂
  have := he₃
  have : IsReduced (D.subschemeι ⁻¹ᵁ Z.support.compl).toScheme :=
    isReduced_of_isOpenImmersion (Scheme.Opens.ι (D.subschemeι ⁻¹ᵁ Z.support.compl))
  have : IsReduced (D.comap (Scheme.Opens.ι Z.support.compl)).subscheme :=
    isReduced_of_isOpenImmersion (inv e₃)
  have : IsReduced
      ((D.comap (Scheme.Opens.ι Z.support.compl)).comap (π ∣_ Z.support.compl)).subscheme :=
    isReduced_of_isOpenImmersion e₂
  have : IsReduced ((D.comap π).comap (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl))).subscheme := by
    rw [hcc]; infer_instance
  have : IsReduced (strictTransformOpens π Z D).toScheme := by
    have hrw : strictTransformOpens π Z D
        = (D.comap π).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl) := by
      show (D.comap π).subschemeι ⁻¹ᵁ (Z.comap π).support.compl
          = (D.comap π).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl)
      rw [hsupp]
    rw [hrw]
    exact isReduced_of_isOpenImmersion e₁
  rw [strictTransform_eq_ker_strictTransformι]
  exact isReduced_subscheme_ker _

theorem strictTransform_eq_ker_restrict (f : X₁ ⟶ X)
    (W D₁ : X.IdealSheafData) :
    Blowup.strictTransform f W D₁ =
      (((D₁.comap (Scheme.Opens.ι W.support.compl)).comap
            (f ∣_ W.support.compl)).subschemeι ≫
          Scheme.Opens.ι (f ⁻¹ᵁ W.support.compl)).ker := by
  have hUV : (W.comap f).support.compl = f ⁻¹ᵁ W.support.compl := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hcomap : (D₁.comap f).comap (Scheme.Opens.ι (f ⁻¹ᵁ W.support.compl))
      = (D₁.comap (Scheme.Opens.ι W.support.compl)).comap (f ∣_ W.support.compl) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  rw [strictTransform_eq_ker_strictTransformι, strictTransformι_eq_ι_comp_subschemeι]
  show (Scheme.Opens.ι ((D₁.comap f).subschemeι ⁻¹ᵁ (W.comap f).support.compl) ≫
      (D₁.comap f).subschemeι).ker = _
  rw [hUV, ker_ι_preimage_comp_subschemeι_eq_ker_comap, hcomap]

theorem strictTransform_congr_of_comap_ι_eq (f : X₁ ⟶ X)
    (W D₁ D₂ : X.IdealSheafData)
    (h : D₁.comap (Scheme.Opens.ι W.support.compl) =
      D₂.comap (Scheme.Opens.ι W.support.compl)) :
    Blowup.strictTransform f W D₁ = Blowup.strictTransform f W D₂ := by
  rw [strictTransform_eq_ker_restrict f W D₁, strictTransform_eq_ker_restrict f W D₂, h]


end

theorem isBlowupAlongIdealSheaf_of_isIso_comp {X A B : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X) (e : A ⟶ B)
    [IsIso e] (hfac : e ≫ g = f) (I : X.IdealSheafData) (hg : Blowup.IsBlowupAlongIdealSheaf g I) :
    Blowup.IsBlowupAlongIdealSheaf f I := by
  obtain ⟨hcart, huniv⟩ := hg
  have h1 : I.comap f = (I.comap g).comap e := by
    rw [← Scheme.IdealSheafData.comap_comp, hfac]
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact hcart.comap_of_isOpenImmersion e
  · intro Y q hq
    obtain ⟨t, ht, huniq⟩ := huniv Y q hq
    have ht' : t ≫ g = q := ht
    refine ⟨t ≫ inv e, ?_, ?_⟩
    · show (t ≫ inv e) ≫ f = q
      rw [← hfac, Category.assoc, IsIso.inv_hom_id_assoc]
      exact ht'
    · intro y hy
      have hy' : y ≫ f = q := hy
      have hye : y ≫ e = t := by
        refine huniq _ ?_
        show (y ≫ e) ≫ g = q
        rw [Category.assoc, hfac]
        exact hy'
      rw [← hye, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem isCompact_of_subset_noetherianSpace_consolidated191 {α : Type u} [TopologicalSpace α] (s : Set α)
    [NoetherianSpace s] (t : Set α) (ht : t ⊆ s) : IsCompact t := by
  have h1 : IsCompact ((Subtype.val : s → α) ⁻¹' t) := NoetherianSpace.isCompact _
  have h2 := h1.image continuous_subtype_val
  have h3 : (Subtype.val : s → α) '' ((Subtype.val : s → α) ⁻¹' t) = t := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hy
    · intro x hx
      exact ⟨⟨x, ht hx⟩, hx, rfl⟩
  rwa [h3] at h2

private theorem isCompact_of_subset_isCompact_consolidated191 {B : Scheme.{u}} [IsLocallyNoetherian B]
    {U : Set B} (hc : IsCompact U) {T : Set B} (hT : T ⊆ U) : IsCompact T := by
  have hcov : U ⊆ ⋃ W : B.affineOpens, (W.1 : Set B) := by
    intro x _
    have hx : x ∈ (⊤ : B.Opens) := Set.mem_univ x
    rw [← iSup_affineOpens_eq_top B] at hx
    obtain ⟨W, hW⟩ := Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨W, hW⟩
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover
    (fun W : B.affineOpens => (W.1 : Set B)) (fun W => W.1.isOpen) hcov
  have hTeq : T = ⋃ W ∈ (s : Set B.affineOpens), (T ∩ (W.1 : Set B)) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨W, hWs, hxW⟩ := Set.mem_iUnion₂.mp (hs (hT hx))
      exact Set.mem_biUnion (show W ∈ (s : Set B.affineOpens) from hWs) ⟨hx, hxW⟩
    · intro x hx
      obtain ⟨W, -, hx'⟩ := Set.mem_iUnion₂.mp hx
      exact hx'.1
  rw [hTeq]
  refine (Finset.finite_toSet s).isCompact_biUnion ?_
  intro W _
  have : IsNoetherianRing (B.presheaf.obj (Opposite.op (W.1 : B.Opens))) :=
    IsLocallyNoetherian.component_noetherian W
  have : NoetherianSpace (W.1 : Set B) := noetherianSpace_of_isAffineOpen W.1 W.2
  exact isCompact_of_subset_noetherianSpace_consolidated191 (W.1 : Set B) (T ∩ (W.1 : Set B)) Set.inter_subset_right

private theorem quasiCompact_of_isInducing_consolidated191 {A B : Scheme.{u}} [IsLocallyNoetherian B]
    (f : A ⟶ B) (hf : Topology.IsInducing ⇑f.base) : QuasiCompact f := by
  refine ⟨fun U _ hU' => ?_⟩
  refine hf.isCompact_iff.mpr ?_
  exact isCompact_of_subset_isCompact_consolidated191 hU' (Set.image_preimage_subset _ _)

theorem quasiCompact_strictTransformι_of_isLocallyNoetherian {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [IsLocallyNoetherian X₁] :
    QuasiCompact (strictTransformι π Z D) := by
  refine quasiCompact_of_isInducing_consolidated191 _ ?_
  have h1 : Topology.IsInducing ⇑(Scheme.Opens.ι (strictTransformOpens π Z D)).base :=
    (Scheme.Opens.ι (strictTransformOpens π Z D)).isEmbedding.toIsInducing
  have h2 : Topology.IsInducing ⇑(D.comap π).subschemeι.base :=
    (D.comap π).subschemeι.isEmbedding.toIsInducing
  have heq : ⇑(strictTransformι π Z D).base
      = ⇑(D.comap π).subschemeι.base ∘
        ⇑(Scheme.Opens.ι (strictTransformOpens π Z D)).base := rfl
  rw [heq]
  exact h2.comp h1

instance instQuasiCompactStrictTransformMorphism {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [IsLocallyNoetherian X₁] :
    QuasiCompact (strictTransformι π Z D) :=
  quasiCompact_strictTransformι_of_isLocallyNoetherian π Z D

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.RemoveIsoBlowupsComparison
section

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace SequenceOfBlowups

variable {X Y : Scheme.{u}}

section
variable (s : SequenceOfBlowups X) (t : SequenceOfBlowups Y) (hlen : s.length = t.length) (htriv : ∀ i, i < s.length → (s.center i = ⊤ ↔ t.center i = ⊤))
include hlen htriv

private theorem nextNontrivialIndex_le_of_center_eq_top_iff_consolidated217 (a : ℕ) :
    s.nextNontrivialIndex a ≤ t.nextNontrivialIndex a := by
  refine s.nextNontrivialIndex_le (t.le_nextNontrivialIndex a) ?_
  rcases Nat.lt_or_ge (t.nextNontrivialIndex a) s.length with h | h
  · refine Or.inl ?_
    have hlt : t.nextNontrivialIndex a < t.length := by rw [← hlen]; exact h
    rcases t.center_nextNontrivialIndex_ne_top_or_length_le a with hd | hd
    · intro hc
      exact hd ((htriv _ h).1 hc)
    · exact absurd hd (not_le.mpr hlt)
  · exact Or.inr h

theorem nextNontrivialIndex_congr_of_center_eq_top_iff (a : ℕ) :
    s.nextNontrivialIndex a = t.nextNontrivialIndex a := by
  refine le_antisymm (nextNontrivialIndex_le_of_center_eq_top_iff_consolidated217 s t hlen htriv a) ?_
  refine nextNontrivialIndex_le_of_center_eq_top_iff_consolidated217 t s hlen.symm ?_ a
  intro i hi
  have hi' : i < s.length := by rw [hlen]; exact hi
  exact (htriv i hi').symm

theorem nontrivialIndex_congr_of_center_eq_top_iff :
    s.nontrivialIndex = t.nontrivialIndex := by
  funext j
  induction j with
  | zero =>
      rw [nontrivialIndex_zero, nontrivialIndex_zero]
      exact nextNontrivialIndex_congr_of_center_eq_top_iff s t hlen htriv 0
  | succ j ih =>
      rw [nontrivialIndex_succ, nontrivialIndex_succ, ih]
      exact nextNontrivialIndex_congr_of_center_eq_top_iff s t hlen htriv _


end

section
variable (s : SequenceOfBlowups X) (t : SequenceOfBlowups Y) (hlen : s.length = t.length)
include hlen

private theorem lengthWithoutIsoBlowups_le_of_nontrivialIndex_eq_consolidated217 (hret : s.nontrivialIndex = t.nontrivialIndex) :
    s.lengthWithoutIsoBlowups ≤ t.lengthWithoutIsoBlowups := by
  by_contra hc
  push Not at hc
  have h1 : s.nontrivialIndex t.lengthWithoutIsoBlowups < s.length := s.nontrivialIndex_lt_length hc
  have h2 : t.length ≤ t.nontrivialIndex t.lengthWithoutIsoBlowups := t.length_le_nontrivialIndex_lengthWithoutIsoBlowups
  rw [← hret, ← hlen] at h2
  exact absurd h2 (not_le.mpr h1)

theorem lengthWithoutIsoBlowups_congr_of_center_eq_top_iff (htriv : ∀ i, i < s.length → (s.center i = ⊤ ↔ t.center i = ⊤)) :
    s.lengthWithoutIsoBlowups = t.lengthWithoutIsoBlowups := by
  have hret : s.nontrivialIndex = t.nontrivialIndex := nontrivialIndex_congr_of_center_eq_top_iff s t hlen htriv
  exact le_antisymm (lengthWithoutIsoBlowups_le_of_nontrivialIndex_eq_consolidated217 s t hlen hret)
    (lengthWithoutIsoBlowups_le_of_nontrivialIndex_eq_consolidated217 t s hlen.symm hret.symm)


end

end SequenceOfBlowups

private theorem preimage_inv_eq_consolidated217 {P Q : Scheme.{u}} (m : P ⟶ Q) [IsIso m] {V : Q.Opens}
    {U : P.Opens} (h : m ⁻¹ᵁ V = U) : (inv m) ⁻¹ᵁ U = V := by
  rw [← h, ← Scheme.Hom.comp_preimage, IsIso.inv_hom_id, Scheme.Hom.id_preimage]

section
variable {A B C : Scheme.{u}} (e : C ⟶ B) [IsIso e] (π : B ⟶ A)

private theorem exists_isIso_subscheme_comap_of_isIso_consolidated217 (D : A.IdealSheafData) :
    ∃ m : (D.comap (e ≫ π)).subscheme ⟶ (D.comap π).subscheme,
      IsIso m ∧ m ≫ (D.comap π).subschemeι = (D.comap (e ≫ π)).subschemeι ≫ e := by
  rw [Scheme.IdealSheafData.comap_comp]
  exact Scheme.IdealSheafData.exists_iso_subscheme_comap_of_isIso e (D.comap π)

private theorem exists_isIso_strictTransformOpens_of_isIso_consolidated217 (Z D : A.IdealSheafData) :
    ∃ φ : (strictTransformOpens (e ≫ π) Z D).toScheme ⟶
        (strictTransformOpens π Z D).toScheme,
      IsIso φ ∧ φ ≫ strictTransformι π Z D
        = strictTransformι (e ≫ π) Z D ≫ e := by
  obtain ⟨μ, hμiso, hμfac⟩ := exists_isIso_subscheme_comap_of_isIso_consolidated217 e π D
  have := hμiso
  have hbase : ∀ T : Set B, ⇑μ.base ⁻¹' (⇑(D.comap π).subschemeι.base ⁻¹' T)
      = ⇑(D.comap (e ≫ π)).subschemeι.base ⁻¹' (⇑e.base ⁻¹' T) := by
    intro T
    have h := congrArg (fun m : (D.comap (e ≫ π)).subscheme ⟶ B => ⇑m.base ⁻¹' T) hμfac
    simpa [Set.preimage_comp] using h
  have hsupp : (((Z.comap (e ≫ π)).support.compl : C.Opens) : Set C)
      = ⇑e.base ⁻¹' (((Z.comap π).support.compl : B.Opens) : Set B) := by
    have h1 : (((Z.comap π).support : TopologicalSpace.Closeds B) : Set B)
        = ⇑π.base ⁻¹' (Z.support : Set A) := by
      rw [Scheme.IdealSheafData.support_comap]; rfl
    have h2 : (((Z.comap (e ≫ π)).support : TopologicalSpace.Closeds C) : Set C)
        = ⇑(e ≫ π).base ⁻¹' (Z.support : Set A) := by
      rw [Scheme.IdealSheafData.support_comap]; rfl
    show (((Z.comap (e ≫ π)).support : TopologicalSpace.Closeds C) : Set C)ᶜ
        = ⇑e.base ⁻¹' ((((Z.comap π).support : TopologicalSpace.Closeds B) : Set B)ᶜ)
    rw [h1, h2, Set.preimage_compl]
    simp [Set.preimage_comp]
  have hset : ⇑μ.base ⁻¹' ((strictTransformOpens π Z D :
        ((D.comap π).subscheme).Opens) : Set ((D.comap π).subscheme))
      = ((strictTransformOpens (e ≫ π) Z D :
        ((D.comap (e ≫ π)).subscheme).Opens) : Set ((D.comap (e ≫ π)).subscheme)) := by
    rw [coe_strictTransformOpens, coe_strictTransformOpens, hbase, hsupp]
  have hopens : μ ⁻¹ᵁ (strictTransformOpens π Z D)
      = strictTransformOpens (e ≫ π) Z D := TopologicalSpace.Opens.ext hset
  have hopens2 : (inv μ) ⁻¹ᵁ (strictTransformOpens (e ≫ π) Z D)
      = strictTransformOpens π Z D := preimage_inv_eq_consolidated217 μ hopens
  refine ⟨μ.resLE (strictTransformOpens π Z D) (strictTransformOpens (e ≫ π) Z D)
      hopens.ge, ?_, ?_⟩
  · refine ⟨(inv μ).resLE (strictTransformOpens (e ≫ π) Z D)
      (strictTransformOpens π Z D) hopens2.ge, ?_, ?_⟩
    · rw [← cancel_mono (Scheme.Opens.ι (strictTransformOpens (e ≫ π) Z D)),
        Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.Hom.resLE_comp_ι,
        Category.assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
    · rw [← cancel_mono (Scheme.Opens.ι (strictTransformOpens π Z D)),
        Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.Hom.resLE_comp_ι,
        Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
  · rw [strictTransformι_eq_ι_comp_subschemeι, strictTransformι_eq_ι_comp_subschemeι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, hμfac, ← Category.assoc]


end

theorem strictTransform_top_eq_comap {A B : Scheme.{u}} (π : B ⟶ A) (D : A.IdealSheafData)
    [QuasiCompact (strictTransformι π ⊤ D)] :
    Blowup.strictTransform π ⊤ D = D.comap π := by
  have hs : (((⊤ : A.IdealSheafData).support : TopologicalSpace.Closeds A) : Set A) = ∅ := by
    simp
  have hsupp : ((((⊤ : A.IdealSheafData).comap π).support :
        TopologicalSpace.Closeds B) : Set B)
      = ⇑π.base ⁻¹' (((⊤ : A.IdealSheafData).support : TopologicalSpace.Closeds A) : Set A) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hc : ((((⊤ : A.IdealSheafData).comap π).support.compl : B.Opens) : Set B) = Set.univ := by
    show (((((⊤ : A.IdealSheafData).comap π).support : TopologicalSpace.Closeds B) : Set B))ᶜ
        = Set.univ
    rw [hsupp, hs]
    simp
  have hU : ((strictTransformOpens π ⊤ D : ((D.comap π).subscheme).Opens) :
      Set ((D.comap π).subscheme)) = Set.univ := by
    rw [coe_strictTransformOpens, hc, Set.preimage_univ]
  have hrange : ∀ g : (D.comap π).subscheme ⟶ (D.comap π).subscheme,
      Set.range ⇑g.base
        ⊆ Set.range ⇑(Scheme.Opens.ι (strictTransformOpens π ⊤ D)).base := by
    intro g
    rw [Scheme.Opens.range_ι, hU]
    exact Set.subset_univ _
  have : IsIso (Scheme.Opens.ι (strictTransformOpens π ⊤ D)) := by
    refine ⟨IsOpenImmersion.lift (Scheme.Opens.ι (strictTransformOpens π ⊤ D)) (𝟙 _)
      (hrange (𝟙 _)), ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rw [← cancel_mono (Scheme.Opens.ι (strictTransformOpens π ⊤ D)), Category.assoc,
      IsOpenImmersion.lift_fac, Category.comp_id, Category.id_comp]
  rw [strictTransform_eq_ker_strictTransformι, strictTransformι_eq_ι_comp_subschemeι,
    Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

theorem strictTransform_isIso_comp {A B C : Scheme.{u}} [IsLocallyNoetherian B]
    [IsLocallyNoetherian C] (e : C ⟶ B) [IsIso e] (π : B ⟶ A) (Z D : A.IdealSheafData)
    (_hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    Blowup.strictTransform (e ≫ π) Z D = (Blowup.strictTransform π Z D).comap e := by
  have : QuasiCompact (strictTransformι (e ≫ π) Z D) := inferInstance
  have : QuasiCompact (strictTransformι (e ≫ π) Z D ≫ e) := inferInstance
  obtain ⟨φ, hφiso, hφfac⟩ := exists_isIso_strictTransformOpens_of_isIso_consolidated217 e π Z D
  have := hφiso
  have hker : (strictTransformι (e ≫ π) Z D ≫ e).ker
      = (strictTransformι π Z D).ker :=
    ker_eq_ker_of_isIso_comp _ _ φ hφfac
  have h2 := Blowup.comap_ker_comp_of_isOpenImmersion (strictTransformι (e ≫ π) Z D) e
  rw [strictTransform_eq_ker_strictTransformι, strictTransform_eq_ker_strictTransformι, ← h2, hker]

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

def saturationOpens {Y : Scheme.{u}} (F T : Y.IdealSheafData) : (T.subscheme).Opens :=
  T.subschemeι ⁻¹ᵁ F.support.compl

theorem coe_saturationOpens {Y : Scheme.{u}} (F T : Y.IdealSheafData) :
    ((saturationOpens F T : (T.subscheme).Opens) : Set (T.subscheme)) =
      ⇑T.subschemeι.base ⁻¹' ((F.support.compl : Y.Opens) : Set Y) := rfl

def saturationι {Y : Scheme.{u}} (F T : Y.IdealSheafData) :
    (saturationOpens F T).toScheme ⟶ Y :=
  Scheme.Opens.ι (saturationOpens F T) ≫ T.subschemeι

theorem saturationι_eq_ι_comp_subschemeι {Y : Scheme.{u}} (F T : Y.IdealSheafData) :
    saturationι F T = Scheme.Opens.ι (saturationOpens F T) ≫ T.subschemeι := rfl

def saturation {Y : Scheme.{u}} (F T : Y.IdealSheafData) : Y.IdealSheafData :=
  (saturationι F T).ker

theorem saturation_eq_ker_saturationι {Y : Scheme.{u}} (F T : Y.IdealSheafData) :
    saturation F T = (saturationι F T).ker := rfl

section
variable {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData)

theorem strictTransformι_eq_saturationι :
    strictTransformι π Z D = saturationι (Z.comap π) (D.comap π) := rfl

theorem strictTransform_eq_saturation :
    Blowup.strictTransform π Z D = saturation (Z.comap π) (D.comap π) := rfl


end

section
variable {Y : Scheme.{u}}

private theorem range_saturationι_consolidated215 (F T : Y.IdealSheafData) :
    Set.range ⇑(saturationι F T) = (T.support : Set ↥Y) \ (F.support : Set ↥Y) := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    have hp : Scheme.Opens.ι (saturationOpens F T) p ∈
        ((saturationOpens F T : (T.subscheme).Opens) : Set ↥(T.subscheme)) := by
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self p
    rw [coe_saturationOpens] at hp
    show T.subschemeι (Scheme.Opens.ι (saturationOpens F T) p) ∈
        (T.support : Set ↥Y) \ (F.support : Set ↥Y)
    refine ⟨?_, hp⟩
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact Set.mem_range_self _
  · rintro ⟨hy1, hy2⟩
    rw [← Scheme.IdealSheafData.range_subschemeι] at hy1
    obtain ⟨q, rfl⟩ := hy1
    have hq : q ∈ ((saturationOpens F T : (T.subscheme).Opens) : Set ↥(T.subscheme)) := by
      rw [coe_saturationOpens]
      exact hy2
    rw [← Scheme.Opens.range_ι] at hq
    obtain ⟨p, hp⟩ := hq
    refine ⟨p, ?_⟩
    show T.subschemeι (Scheme.Opens.ι (saturationOpens F T) p) = T.subschemeι q
    rw [hp]

theorem quasiCompact_saturationι_restrictIdeal (F T : Y.IdealSheafData)
    [QuasiCompact (saturationι F T)] (V : Y.Opens) :
    QuasiCompact (saturationι (restrictIdeal F V) (restrictIdeal T V)) := by
  constructor
  intro U hU hUc
  have hV := Scheme.Hom.isEmbedding (f := Scheme.Opens.ι V)
  have hg := Scheme.Hom.isEmbedding
    (f := Scheme.Opens.ι (saturationOpens F T) ≫ T.subschemeι)
  have hg' := Scheme.Hom.isEmbedding
    (f := Scheme.Opens.ι (saturationOpens (restrictIdeal F V) (restrictIdeal T V)) ≫
      (restrictIdeal T V).subschemeι)
  have hrange' : Set.range ⇑(saturationι (restrictIdeal F V) (restrictIdeal T V))
      = ⇑(Scheme.Opens.ι V) ⁻¹' ((T.support : Set ↥Y) \ (F.support : Set ↥Y)) := by
    rw [range_saturationι_consolidated215, restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, Set.preimage_sdiff]
    ext x
    simp only [Set.mem_sdiff, Set.mem_preimage, SetLike.mem_coe,
      Scheme.IdealSheafData.mem_support_comap]
  have hUo : IsOpen (⇑(Scheme.Opens.ι V) '' U) := by
    obtain ⟨W, hW, hWU⟩ := hV.toIsInducing.isOpen_iff.mp hU
    rw [← hWU, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    exact hW.inter V.isOpen
  have hUk : IsCompact (⇑(Scheme.Opens.ι V) '' U) := hUc.image hV.continuous
  have hmain : IsCompact (⇑(saturationι F T) ⁻¹' (⇑(Scheme.Opens.ι V) '' U)) :=
    QuasiCompact.isCompact_preimage _ hUo hUk
  have himg : IsCompact (⇑(saturationι F T) ''
      (⇑(saturationι F T) ⁻¹' (⇑(Scheme.Opens.ι V) '' U))) := hmain.image hg.continuous
  rw [Set.image_preimage_eq_inter_range, range_saturationι_consolidated215] at himg
  have h2 : IsCompact (⇑(Scheme.Opens.ι V) '' (U ∩ ⇑(Scheme.Opens.ι V) ⁻¹'
      ((T.support : Set ↥Y) \ (F.support : Set ↥Y)))) := by
    rw [Set.image_inter_preimage]
    exact himg
  have h3 := hV.toIsInducing.isCompact_iff.mpr h2
  have hfinal : IsCompact (⇑(saturationι (restrictIdeal F V) (restrictIdeal T V)) ''
      (⇑(saturationι (restrictIdeal F V) (restrictIdeal T V)) ⁻¹' U)) := by
    rw [Set.image_preimage_eq_inter_range, hrange']
    exact h3
  exact hg'.toIsInducing.isCompact_iff.mpr hfinal

private theorem isCompact_of_subset_affineOpen_consolidated215 [IsLocallyNoetherian Y]
    {U : Y.Opens} (hU : IsAffineOpen U) {S : Set ↥Y} (hS : S ⊆ (U : Set ↥Y)) :
    IsCompact S := by
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : NoetherianSpace ↥U := noetherianSpace_of_isAffineOpen U hU
  have h1 : IsCompact ((Subtype.val : ↥U → ↥Y) ⁻¹' S) := NoetherianSpace.isCompact _
  have h2 := h1.image continuous_subtype_val
  have hsub : S ⊆ Set.range (Subtype.val : ↥U → ↥Y) := fun x hx => ⟨⟨x, hS hx⟩, rfl⟩
  rwa [Set.image_preimage_eq_of_subset hsub] at h2

private theorem exists_isOpen_mem_forall_subset_isCompact_consolidated215 [IsLocallyNoetherian Y] (y : ↥Y) :
    ∃ V : Set ↥Y, IsOpen V ∧ y ∈ V ∧ ∀ S ⊆ V, IsCompact S := by
  have h : (⨆ i : Y.affineOpens, (i : Y.Opens)) = ⊤ := iSup_affineOpens_eq_top Y
  have hy : y ∈ (⨆ i : Y.affineOpens, (i : Y.Opens)) := by
    rw [h]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  exact ⟨((i : Y.Opens) : Set ↥Y), (i : Y.Opens).isOpen, hi,
    fun S hS => isCompact_of_subset_affineOpen_consolidated215 i.2 hS⟩

private theorem isCompact_of_subset_isCompact_consolidated215 [IsLocallyNoetherian Y]
    {K S : Set ↥Y} (hK : IsCompact K) (hS : S ⊆ K) : IsCompact S := by
  have key : ∀ y : ↥Y, ∃ V : Set ↥Y, IsOpen V ∧ y ∈ V ∧ ∀ S' ⊆ V, IsCompact S' :=
    fun y => exists_isOpen_mem_forall_subset_isCompact_consolidated215 y
  choose V hVopen hVmem hVcomp using key
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hVopen
    (fun y _ => Set.mem_iUnion.2 ⟨y, hVmem y⟩)
  have hEq : S = ⋃ y ∈ (t : Set ↥Y), (S ∩ V y) := by
    refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (hS hx))
      exact Set.mem_iUnion₂.2 ⟨y, Finset.mem_coe.2 hy, hx, hxy⟩
    · obtain ⟨y, -, hx1, -⟩ := Set.mem_iUnion₂.1 hx
      exact hx1
  rw [hEq]
  exact t.finite_toSet.isCompact_biUnion fun y _ => hVcomp y _ Set.inter_subset_right

theorem quasiCompact_saturationι_of_isLocallyNoetherian [IsLocallyNoetherian Y] (F T : Y.IdealSheafData) :
    QuasiCompact (saturationι F T) := by
  constructor
  intro U _ hUc
  have hg := Scheme.Hom.isEmbedding
    (f := Scheme.Opens.ι (saturationOpens F T) ≫ T.subschemeι)
  have hfinal : IsCompact (⇑(saturationι F T) '' (⇑(saturationι F T) ⁻¹' U)) := by
    rw [Set.image_preimage_eq_inter_range, range_saturationι_consolidated215]
    exact isCompact_of_subset_isCompact_consolidated215 hUc Set.inter_subset_left
  exact hg.toIsInducing.isCompact_iff.mpr hfinal

theorem quasiCompact_saturationι_of_noetherianSpace [NoetherianSpace Y] (F T : Y.IdealSheafData) :
    QuasiCompact (saturationι F T) := by
  have hemb := Scheme.Hom.isEmbedding
    (f := Scheme.Opens.ι (saturationOpens F T) ≫ T.subschemeι)
  have : NoetherianSpace ((saturationOpens F T).toScheme) :=
    hemb.toIsInducing.noetherianSpace
  exact ⟨fun U _ _ => NoetherianSpace.isCompact _⟩


end

private theorem ideal_comap_hom_id_consolidated215 {R : CommRingCat.{u}} (I : Ideal R) :
    Ideal.comap (CommRingCat.Hom.hom (𝟙 R)) I = I := by
  ext x
  simp only [Ideal.mem_comap, CommRingCat.hom_id, RingHom.id_apply]

private theorem ker_comp_map_eqToHom_consolidated215 {A : Scheme.{u}} {R : CommRingCat.{u}}
    {P Q : A.Opens} (e : P = Q) (φ : R ⟶ A.presheaf.obj (Opposite.op Q)) :
    RingHom.ker (CommRingCat.Hom.hom (φ ≫ A.presheaf.map (eqToHom e).op))
      = RingHom.ker φ.hom := by
  subst e
  simp

private theorem ker_comap_ι_consolidated215 {A B : Scheme.{u}} (m : A ⟶ B) [QuasiCompact m]
    (V : B.Opens) : m.ker.comap V.ι = (m ∣_ V).ker := by
  have : QuasiCompact (m ∣_ V) := inferInstance
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.Hom.ker_apply,
    Scheme.Hom.ker_apply, morphismRestrict_app]
  refine Eq.trans ?_ (ker_comp_map_eqToHom_consolidated215 _ _).symm
  simp
  exact ideal_comap_hom_id_consolidated215 _

private theorem quasiCompact_of_eq_consolidated215 {A C : Scheme.{u}} {f g : A ⟶ C} (h : f = g)
    (hf : QuasiCompact g) : QuasiCompact f := by
  subst h
  exact hf

section
variable {A B C : Scheme.{u}}

private theorem ker_le_ker_comp_consolidated215 (a : A ⟶ B) (m : B ⟶ C)
    [QuasiCompact m] [QuasiCompact (a ≫ m)] : m.ker ≤ (a ≫ m).ker := by
  rw [Scheme.IdealSheafData.le_def]
  intro U
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
  intro x hx
  rw [RingHom.mem_ker] at hx
  have key : ((a ≫ m).app U.1).hom x = (a.app (m ⁻¹ᵁ U.1)).hom ((m.app U.1).hom x) :=
    congrArg (fun φ => (CommRingCat.Hom.hom φ) x) (Scheme.Hom.comp_app a m U.1)
  refine RingHom.mem_ker.mpr ?_
  rw [key, hx]
  exact map_zero _

private theorem ker_eq_ker_of_factorizations_consolidated215 (u : A ⟶ C) (v : B ⟶ C)
    (hu : QuasiCompact u) (hv : QuasiCompact v) (a : A ⟶ B) (b : B ⟶ A)
    (ha : a ≫ v = u) (hb : b ≫ u = v) : u.ker = v.ker := by
  have := hu
  have := hv
  have h1 : QuasiCompact (a ≫ v) := quasiCompact_of_eq_consolidated215 ha hu
  have h2 : QuasiCompact (b ≫ u) := quasiCompact_of_eq_consolidated215 hb hv
  refine le_antisymm ?_ ?_
  · rw [← hb]
    exact ker_le_ker_comp_consolidated215 b u
  · rw [← ha]
    exact ker_le_ker_comp_consolidated215 a v


end

private theorem base_apply_congr_consolidated215 {A B : Scheme.{u}} {φ ψ : A ⟶ B} (h : φ = ψ) (x : ↥A) :
    φ x = ψ x := by rw [h]

section
variable {Y : Scheme.{u}}

private theorem mem_saturationOpens_consolidated215 (F T : Y.IdealSheafData)
    (z : ↥(T.subscheme)) :
    z ∈ ((saturationOpens F T : (T.subscheme).Opens) : Set ↥(T.subscheme))
      ↔ T.subschemeι z ∉ ((F.support : TopologicalSpace.Closeds ↥Y) : Set ↥Y) := by
  rw [coe_saturationOpens]
  exact Iff.rfl

private theorem exists_factorizations_subscheme_restrict_consolidated215 (T : Y.IdealSheafData)
    (V : Y.Opens) :
    (∃ p : ((T.comap V.ι).subscheme) ⟶ (T.subschemeι ⁻¹ᵁ V).toScheme,
        p ≫ (T.subschemeι ∣_ V) = (T.comap V.ι).subschemeι) ∧
      (∃ q : (T.subschemeι ⁻¹ᵁ V).toScheme ⟶ ((T.comap V.ι).subscheme),
        q ≫ (T.comap V.ι).subschemeι = T.subschemeι ∣_ V) := by
  have : IsClosedImmersion (T.subschemeι ∣_ V) := inferInstance
  have hker : (T.subschemeι ∣_ V).ker = ((T.comap V.ι).subschemeι).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← ker_comap_ι_consolidated215,
      Scheme.IdealSheafData.ker_subschemeι]
  refine ⟨⟨IsClosedImmersion.lift (T.subschemeι ∣_ V) ((T.comap V.ι).subschemeι) hker.le,
      by simp⟩,
    ⟨IsClosedImmersion.lift ((T.comap V.ι).subschemeι) (T.subschemeι ∣_ V) hker.ge, by simp⟩⟩

private theorem exists_comp_morphismRestrict_eq_saturationι_consolidated215 (F T : Y.IdealSheafData) (V : Y.Opens) :
    ∃ a : (saturationOpens (F.comap V.ι) (T.comap V.ι)).toScheme ⟶
        (saturationι F T ⁻¹ᵁ V).toScheme,
      a ≫ (saturationι F T ∣_ V) = saturationι (F.comap V.ι) (T.comap V.ι) := by
  obtain ⟨⟨p, hp⟩, -⟩ := exists_factorizations_subscheme_restrict_consolidated215 T V
  have hdT : (Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) ≫ p ≫
        Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V)) ≫ T.subschemeι
      = saturationι (F.comap V.ι) (T.comap V.ι) ≫ V.ι := by
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι T.subschemeι V,
      ← Category.assoc p, hp, saturationι_eq_ι_comp_subschemeι (F.comap V.ι) (T.comap V.ι), Category.assoc]
  have hrangeD : Set.range ⇑(Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) ≫ p ≫
        Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V))
      ⊆ Set.range ⇑(Scheme.Opens.ι (saturationOpens F T)) := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, mem_saturationOpens_consolidated215]
    have hx : Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) x
        ∈ ((saturationOpens (F.comap V.ι) (T.comap V.ι) :
            ((T.comap V.ι).subscheme).Opens) : Set ↥((T.comap V.ι).subscheme)) := by
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self _
    have key : T.subschemeι
          ((Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) ≫ p ≫
            Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V)) x)
        = V.ι (saturationι (F.comap V.ι) (T.comap V.ι) x) := base_apply_congr_consolidated215 hdT x
    rw [key]
    intro hcon
    refine (mem_saturationOpens_consolidated215 (F.comap V.ι) (T.comap V.ι) _).mp hx ?_
    rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_comap]
    exact SetLike.mem_coe.mp hcon
  obtain ⟨c, hc⟩ : ∃ c : (saturationOpens (F.comap V.ι) (T.comap V.ι)).toScheme ⟶
      (saturationOpens F T).toScheme,
      c ≫ Scheme.Opens.ι (saturationOpens F T)
        = Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) ≫ p ≫
            Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V) :=
    ⟨IsOpenImmersion.lift (Scheme.Opens.ι (saturationOpens F T))
      (Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) ≫ p ≫
        Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V)) hrangeD, by simp⟩
  have hc' : c ≫ saturationι F T
      = saturationι (F.comap V.ι) (T.comap V.ι) ≫ V.ι := by
    have h0 : (c ≫ Scheme.Opens.ι (saturationOpens F T)) ≫ T.subschemeι
        = saturationι (F.comap V.ι) (T.comap V.ι) ≫ V.ι := by
      rw [hc]
      exact hdT
    rw [saturationι_eq_ι_comp_subschemeι F T, ← Category.assoc]
    exact h0
  have hrangeC : Set.range ⇑c
      ⊆ Set.range ⇑(Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V)) := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    show saturationι F T (c x) ∈ ((V : Y.Opens) : Set ↥Y)
    have key : saturationι F T (c x)
        = V.ι (saturationι (F.comap V.ι) (T.comap V.ι) x) := base_apply_congr_consolidated215 hc' x
    rw [key, ← Scheme.Opens.range_ι]
    exact Set.mem_range_self _
  obtain ⟨a, ha⟩ : ∃ a : (saturationOpens (F.comap V.ι) (T.comap V.ι)).toScheme ⟶
      (saturationι F T ⁻¹ᵁ V).toScheme,
      a ≫ Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) = c :=
    ⟨IsOpenImmersion.lift (Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V)) c hrangeC, by simp⟩
  refine ⟨a, ?_⟩
  rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, ha]
  exact hc'

private theorem exists_comp_saturationι_eq_morphismRestrict_consolidated215 (F T : Y.IdealSheafData) (V : Y.Opens) :
    ∃ b : (saturationι F T ⁻¹ᵁ V).toScheme ⟶
        (saturationOpens (F.comap V.ι) (T.comap V.ι)).toScheme,
      b ≫ saturationι (F.comap V.ι) (T.comap V.ι) = saturationι F T ∣_ V := by
  obtain ⟨-, ⟨q, hq⟩⟩ := exists_factorizations_subscheme_restrict_consolidated215 T V
  have hrangeW : Set.range ⇑(Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) ≫
        Scheme.Opens.ι (saturationOpens F T))
      ⊆ Set.range ⇑(Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V)) := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hy : Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) y
        ∈ ((saturationι F T ⁻¹ᵁ V : ((saturationOpens F T).toScheme).Opens) :
            Set ↥((saturationOpens F T).toScheme)) := by
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self _
    exact hy
  obtain ⟨w, hw⟩ : ∃ w : (saturationι F T ⁻¹ᵁ V).toScheme ⟶
      (T.subschemeι ⁻¹ᵁ V).toScheme,
      w ≫ Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V)
        = Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) ≫
            Scheme.Opens.ι (saturationOpens F T) :=
    ⟨IsOpenImmersion.lift (Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V))
      (Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) ≫
        Scheme.Opens.ι (saturationOpens F T)) hrangeW, by simp⟩
  have hrangeQ : Set.range ⇑(w ≫ q)
      ⊆ Set.range ⇑(Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι))) := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, mem_saturationOpens_consolidated215, SetLike.mem_coe,
      Scheme.IdealSheafData.mem_support_comap]
    have hy : Scheme.Opens.ι (saturationOpens F T)
          (Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) y)
        ∈ ((saturationOpens F T : (T.subscheme).Opens) : Set ↥(T.subscheme)) := by
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self _
    have key : V.ι ((T.comap V.ι).subschemeι ((w ≫ q) y))
        = T.subschemeι (Scheme.Opens.ι (saturationOpens F T)
            (Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) y)) := by
      have e1 : (T.comap V.ι).subschemeι ((w ≫ q) y) = (T.subschemeι ∣_ V) (w y) :=
        base_apply_congr_consolidated215 hq (w y)
      have e2 : V.ι ((T.subschemeι ∣_ V) (w y))
          = T.subschemeι (Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V) (w y)) :=
        base_apply_congr_consolidated215 (morphismRestrict_ι T.subschemeι V) (w y)
      have e3 : Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V) (w y)
          = Scheme.Opens.ι (saturationOpens F T)
              (Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) y) :=
        base_apply_congr_consolidated215 hw y
      rw [e1, e2, e3]
    rw [key]
    exact (mem_saturationOpens_consolidated215 F T _).mp hy
  obtain ⟨b, hb0⟩ : ∃ b : (saturationι F T ⁻¹ᵁ V).toScheme ⟶
      (saturationOpens (F.comap V.ι) (T.comap V.ι)).toScheme,
      b ≫ Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) = w ≫ q :=
    ⟨IsOpenImmersion.lift (Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)))
      (w ≫ q) hrangeQ, by simp⟩
  have hb' : (w ≫ q) ≫ ((T.comap V.ι).subschemeι ≫ V.ι)
      = Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) ≫
          (Scheme.Opens.ι (saturationOpens F T) ≫ T.subschemeι) := by
    rw [Category.assoc, ← Category.assoc q, hq, morphismRestrict_ι, ← Category.assoc w, hw,
      Category.assoc]
  refine ⟨b, ?_⟩
  rw [← cancel_mono V.ι, saturationι_eq_ι_comp_subschemeι (F.comap V.ι) (T.comap V.ι),
    ← Category.assoc b, hb0, Category.assoc, morphismRestrict_ι]
  exact hb'

theorem restrictIdeal_saturation (F T : Y.IdealSheafData)
    [QuasiCompact (saturationι F T)] (V : Y.Opens) :
    restrictIdeal (saturation F T) V = saturation (restrictIdeal F V) (restrictIdeal T V) := by
  have hqcR := quasiCompact_saturationι_restrictIdeal F T V
  rw [restrictIdeal_eq_comap_ι, saturation_eq_ker_saturationι, ker_comap_ι_consolidated215, saturation_eq_ker_saturationι]
  obtain ⟨a, ha⟩ := exists_comp_morphismRestrict_eq_saturationι_consolidated215 F T V
  obtain ⟨b, hb⟩ := exists_comp_saturationι_eq_morphismRestrict_consolidated215 F T V
  exact ker_eq_ker_of_factorizations_consolidated215 _ _ inferInstance hqcR b a hb ha

private theorem support_compl_inf_eq_basicOpen_consolidated215 (F : Y.IdealSheafData)
    (V : Y.affineOpens) (t : Γ(Y, V.1)) (ht : F.ideal V = Ideal.span {t}) :
    F.support.compl ⊓ V.1 = Y.basicOpen t := by
  have key : ∀ (x : ↥Y), x ∈ V.1 → (x ∈ F.support ↔ x ∉ Y.basicOpen t) := by
    intro x hx
    rw [F.mem_support_iff_of_mem hx, ht, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
  refine le_antisymm (fun x hx => ?_) (le_inf (fun x hx => ?_) (Y.basicOpen_le t))
  · have hx1 : x ∈ F.support.compl := hx.1
    have hx2 : x ∈ V.1 := hx.2
    by_contra hb
    exact hx1 ((key x hx2).mpr hb)
  · exact fun hs => ((key x (Y.basicOpen_le t hx)).mp hs) hx


end

section
variable {S : Scheme.{u}}

private theorem image_preimage_ι_le_consolidated215 (W V' : S.Opens) :
    Scheme.Opens.ι W ''ᵁ (Scheme.Opens.ι W ⁻¹ᵁ V') ≤ V' := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_le_right

private theorem map_eq_zero_congr_consolidated215 {A B P : S.Opens} (e : A = B) (hA : A ≤ P)
    (hB : B ≤ P) (z : Γ(S, P)) :
    ((S.presheaf.map (homOfLE hA).op).hom z = 0) ↔
      ((S.presheaf.map (homOfLE hB).op).hom z = 0) := by
  subst e
  rfl

private theorem map_basicOpen_eq_zero_iff_consolidated215 {P : S.Opens} (hP : IsAffineOpen P)
    (s y : Γ(S, P)) :
    (S.presheaf.map (homOfLE (S.basicOpen_le s)).op).hom y = 0 ↔ ∃ n : ℕ, s ^ n * y = 0 := by
  have := hP.isLocalization_basicOpen s
  have halg : ∀ z : Γ(S, P), algebraMap Γ(S, P) Γ(S, S.basicOpen s) z
      = (S.presheaf.map (homOfLE (S.basicOpen_le s)).op).hom z := fun _ => rfl
  rw [← halg y]
  constructor
  · intro hy
    have h0 : algebraMap Γ(S, P) Γ(S, S.basicOpen s) y
        = algebraMap Γ(S, P) Γ(S, S.basicOpen s) 0 := by
      rw [map_zero]
      exact hy
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers s)
      Γ(S, S.basicOpen s)).mp h0
    obtain ⟨n, hn⟩ := c.2
    refine ⟨n, ?_⟩
    rw [mul_zero] at hc
    rw [← hn] at hc
    exact hc
  · rintro ⟨n, hn⟩
    have hu : IsUnit (algebraMap Γ(S, P) Γ(S, S.basicOpen s) s) :=
      IsLocalization.map_units (M := Submonoid.powers s) Γ(S, S.basicOpen s)
        ⟨s, Submonoid.mem_powers s⟩
    have h2 := congrArg (algebraMap Γ(S, P) Γ(S, S.basicOpen s)) hn
    rw [map_mul, map_pow, map_zero] at h2
    obtain ⟨v, hv⟩ := hu.pow n
    have h4 : (v : Γ(S, S.basicOpen s)) * algebraMap Γ(S, P) Γ(S, S.basicOpen s) y = 0 := by
      rw [hv]
      exact h2
    have h5 := congrArg
      (fun z => ((v⁻¹ : (Γ(S, S.basicOpen s))ˣ) : Γ(S, S.basicOpen s)) * z) h4
    simpa using h5


end

private theorem ker_app_subschemeι_consolidated215 {Y : Scheme.{u}} (T : Y.IdealSheafData) (U : Y.affineOpens) :
    RingHom.ker ((T.subschemeι.app U.1)).hom = T.ideal U := by
  have : QuasiCompact T.subschemeι := inferInstance
  rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]

section
variable {Y : Scheme.{u}} (F T : Y.IdealSheafData) [QuasiCompact (saturationι F T)] (V : Y.affineOpens) (t : Γ(Y, V.1)) (ht : F.ideal V = Ideal.span {t})
include ht

theorem mem_saturation_ideal_iff (f : Γ(Y, V.1)) :
    f ∈ (saturation F T).ideal V ↔ ∃ n : ℕ, t ^ n * f ∈ T.ideal V := by
  have hPaff : IsAffineOpen (T.subschemeι ⁻¹ᵁ V.1) := V.2.preimage T.subschemeι
  have hbasic : Scheme.Opens.ι (saturationOpens F T) ''ᵁ
        (Scheme.Opens.ι (saturationOpens F T) ⁻¹ᵁ (T.subschemeι ⁻¹ᵁ V.1)) =
      T.subscheme.basicOpen ((T.subschemeι.app V.1).hom t) := by
    have h1 : (T.subschemeι ⁻¹ᵁ F.support.compl) ⊓ (T.subschemeι ⁻¹ᵁ V.1)
        = T.subschemeι ⁻¹ᵁ (F.support.compl ⊓ V.1) := rfl
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    show (T.subschemeι ⁻¹ᵁ F.support.compl) ⊓ (T.subschemeι ⁻¹ᵁ V.1) = _
    rw [h1, support_compl_inf_eq_basicOpen_consolidated215 F V t ht, Scheme.preimage_basicOpen]
  have hcongr : ∀ z : Γ(T.subscheme, T.subschemeι ⁻¹ᵁ V.1),
      ((Scheme.Opens.ι (saturationOpens F T)).app (T.subschemeι ⁻¹ᵁ V.1)).hom z = 0 ↔
      (T.subscheme.presheaf.map (homOfLE
        (T.subscheme.basicOpen_le ((T.subschemeι.app V.1).hom t))).op).hom z = 0 := by
    intro z
    have e1 : ((Scheme.Opens.ι (saturationOpens F T)).app (T.subschemeι ⁻¹ᵁ V.1)).hom z
        = (T.subscheme.presheaf.map (homOfLE
            (image_preimage_ι_le_consolidated215 (saturationOpens F T) (T.subschemeι ⁻¹ᵁ V.1))).op).hom z := rfl
    rw [e1]
    exact map_eq_zero_congr_consolidated215 hbasic _ _ z
  have hS : f ∈ (saturation F T).ideal V ↔ ((saturationι F T).app V.1).hom f = 0 := by
    rw [saturation_eq_ker_saturationι, Scheme.Hom.ker_apply]
    exact RingHom.mem_ker
  have hT : ∀ a : Γ(Y, V.1), a ∈ T.ideal V ↔ (T.subschemeι.app V.1).hom a = 0 := by
    intro a
    rw [← ker_app_subschemeι_consolidated215 T V]
    exact RingHom.mem_ker
  have hmul : ∀ (n : ℕ) (a : Γ(Y, V.1)),
      (T.subschemeι.app V.1).hom (t ^ n * a)
        = ((T.subschemeι.app V.1).hom t) ^ n * ((T.subschemeι.app V.1).hom a) := by
    intro n a
    rw [map_mul, map_pow]
  have main : ((Scheme.Opens.ι (saturationOpens F T)).app (T.subschemeι ⁻¹ᵁ V.1)).hom
      ((T.subschemeι.app V.1).hom f) = 0 ↔ ∃ n : ℕ, t ^ n * f ∈ T.ideal V := by
    rw [hcongr ((T.subschemeι.app V.1).hom f),
      map_basicOpen_eq_zero_iff_consolidated215 hPaff ((T.subschemeι.app V.1).hom t)
        ((T.subschemeι.app V.1).hom f)]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, (hT _).mpr ?_⟩
      rw [hmul]
      exact hn
    · rintro ⟨n, hn⟩
      have h := (hT _).mp hn
      rw [hmul] at h
      exact ⟨n, h⟩
  exact hS.trans main

theorem saturation_ideal_eq_of_eq_mul (J : Ideal Γ(Y, V.1))
    (hTfactor : T.ideal V = Ideal.span {t} * J)
    (hJ : ∀ g : Γ(Y, V.1), t * g ∈ J → g ∈ J) :
    (saturation F T).ideal V = J := by
  have hsub : Ideal.span {t} * J ≤ J :=
    Ideal.mul_le.2 (fun r _ s hs => J.mul_mem_left r hs)
  have hdown : ∀ (n : ℕ) (g : Γ(Y, V.1)), t ^ n * g ∈ J → g ∈ J := by
    intro n
    induction n with
    | zero =>
        intro g hg
        simpa using hg
    | succ m ih =>
        intro g hg
        refine hJ g (ih (t * g) ?_)
        have hrw : t ^ m * (t * g) = t ^ (m + 1) * g := by ring
        rw [hrw]
        exact hg
  ext f
  rw [mem_saturation_ideal_iff F T V t ht f]
  constructor
  · rintro ⟨n, hn⟩
    rw [hTfactor] at hn
    exact hdown n f (hsub hn)
  · intro hf
    refine ⟨1, ?_⟩
    rw [hTfactor, pow_one]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self t) hf

theorem saturation_ideal_eq_top_of_span_pow_le (m : ℕ)
    (hm : Ideal.span {t ^ m} ≤ T.ideal V) :
    (saturation F T).ideal V = ⊤ := by
  have htm : t ^ m ∈ T.ideal V := hm (Ideal.mem_span_singleton_self _)
  rw [Ideal.eq_top_iff_one, mem_saturation_ideal_iff F T V t ht 1]
  exact ⟨m, by simpa using htm⟩

theorem saturation_ideal_eq_of_isUnit (hu : IsUnit t) :
    (saturation F T).ideal V = T.ideal V := by
  ext f
  rw [mem_saturation_ideal_iff F T V t ht f]
  constructor
  · rintro ⟨n, hn⟩
    exact ((T.ideal V).unit_mul_mem_iff_mem (hu.pow n)).mp hn
  · intro hf
    exact ⟨0, by simpa using hf⟩


end

theorem strictTransform_eq_of_comap_eq {X X' X₁ : Scheme.{u}} (π : X₁ ⟶ X) (π' : X₁ ⟶ X')
    (Z D : X.IdealSheafData) (Z' D' : X'.IdealSheafData)
    (hZ : Z.comap π = Z'.comap π') (hD : D.comap π = D'.comap π') :
    Blowup.strictTransform π Z D = Blowup.strictTransform π' Z' D' := by
  rw [strictTransform_eq_saturation π Z D, strictTransform_eq_saturation π' Z' D', hZ, hD]

theorem strictTransform_comp_ι {X V' : Scheme.{u}} (U : X.Opens) (g : V' ⟶ U.toScheme)
    (Z D : X.IdealSheafData) :
    Blowup.strictTransform (g ≫ U.ι) Z D = Blowup.strictTransform g (restrictIdeal Z U) (restrictIdeal D U) := by
  refine strictTransform_eq_of_comap_eq (g ≫ U.ι) g Z D (restrictIdeal Z U)
    (restrictIdeal D U) ?_ ?_
  · simp [restrictIdeal_eq_comap_ι, Scheme.IdealSheafData.comap_comp]
  · simp [restrictIdeal_eq_comap_ι, Scheme.IdealSheafData.comap_comp]

theorem restrictIdeal_strictTransform {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z D)] (V : X₁.Opens) :
    restrictIdeal (Blowup.strictTransform π Z D) V = Blowup.strictTransform (V.ι ≫ π) Z D := by
  have hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    (inferInstance : QuasiCompact (strictTransformι π Z D))
  rw [strictTransform_eq_saturation π Z D, strictTransform_eq_saturation (V.ι ≫ π) Z D,
    restrictIdeal_saturation (Z.comap π) (D.comap π) V, restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι,
    Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]

private theorem quasiCompact_saturationι_congr_consolidated215 {Y : Scheme.{u}}
    {F F' T T' : Y.IdealSheafData} (hF : F = F') (hT : T = T')
    (h : QuasiCompact (saturationι F T)) :
    QuasiCompact (saturationι F' T') := by
  subst hF
  subst hT
  exact h

theorem quasiCompact_strictTransformι_comp_ι {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [QuasiCompact (strictTransformι π Z D)] (V : X₁.Opens) :
    QuasiCompact (strictTransformι (V.ι ≫ π) Z D) := by
  have hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    (inferInstance : QuasiCompact (strictTransformι π Z D))
  have h2 : QuasiCompact (saturationι (restrictIdeal (Z.comap π) V)
      (restrictIdeal (D.comap π) V)) :=
    quasiCompact_saturationι_restrictIdeal (Z.comap π) (D.comap π) V
  have hZ : restrictIdeal (Z.comap π) V = Z.comap (V.ι ≫ π) := by
    rw [restrictIdeal_eq_comap_ι, Scheme.IdealSheafData.comap_comp]
  have hD : restrictIdeal (D.comap π) V = D.comap (V.ι ≫ π) := by
    rw [restrictIdeal_eq_comap_ι, Scheme.IdealSheafData.comap_comp]
  show QuasiCompact (saturationι (Z.comap (V.ι ≫ π)) (D.comap (V.ι ≫ π)))
  exact quasiCompact_saturationι_congr_consolidated215 hZ hD h2

section
variable {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) [QuasiCompact (strictTransformι π Z D)] (V : X₁.affineOpens) (t : Γ(X₁, V.1)) (ht : (Z.comap π).ideal V = Ideal.span {t})
include ht

theorem mem_strictTransform_ideal_iff (f : Γ(X₁, V.1)) :
    f ∈ (Blowup.strictTransform π Z D).ideal V ↔ ∃ n : ℕ, t ^ n * f ∈ (D.comap π).ideal V := by
  have hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    (inferInstance : QuasiCompact (strictTransformι π Z D))
  rw [strictTransform_eq_saturation π Z D]
  exact mem_saturation_ideal_iff (Z.comap π) (D.comap π) V t ht f

theorem strictTransform_ideal_eq_comap_of_isUnit (hu : IsUnit t) :
    (Blowup.strictTransform π Z D).ideal V = (D.comap π).ideal V := by
  have hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    (inferInstance : QuasiCompact (strictTransformι π Z D))
  rw [strictTransform_eq_saturation π Z D]
  exact saturation_ideal_eq_of_isUnit (Z.comap π) (D.comap π) V t ht hu


end

theorem quasiCompact_strictTransformι_of_noetherianSpace {X X₁ : Scheme.{u}}
    [NoetherianSpace X₁] (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    QuasiCompact (strictTransformι π Z D) := by
  show QuasiCompact (saturationι (Z.comap π) (D.comap π))
  exact quasiCompact_saturationι_of_noetherianSpace (Z.comap π) (D.comap π)

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransformOffCenter
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

def complComapSupport {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData) : X₁.Opens :=
  (Z.comap π).support.compl

section
variable {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData)

theorem complComapSupport_eq :
    complComapSupport π Z = (Z.comap π).support.compl := rfl

theorem coe_complComapSupport :
    ((complComapSupport π Z : X₁.Opens) : Set X₁) = ((Z.comap π).support : Set X₁)ᶜ := rfl


end

theorem strictTransform_comap_complComapSupport_ι {X X₁ : Scheme.{u}} [IsNoetherian X₁]
    (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    (Blowup.strictTransform π Z D).comap (Scheme.Opens.ι (complComapSupport π Z)) =
      (D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z)) := by
  have hqι : QuasiCompact (Scheme.Opens.ι (complComapSupport π Z)) := inferInstance
  have hq1 : QuasiCompact
      (((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι) := inferInstance
  have hq2 : QuasiCompact
      ((((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι) ≫
        Scheme.Opens.ι (complComapSupport π Z)) := inferInstance
  have h1 : Blowup.strictTransform π Z D =
      ((((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι) ≫
        Scheme.Opens.ι (complComapSupport π Z)).ker :=
    ker_ι_preimage_comp_subschemeι_eq_ker_comap (D.comap π) (complComapSupport π Z)
  rw [h1]
  exact comap_ker_subschemeι_comp
    ((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z)))
    (Scheme.Opens.ι (complComapSupport π Z))

theorem strictTransform_comap_of_comap_center_eq_top {X X₁ B : Scheme.{u}} [IsNoetherian X₁]
    (π : X₁ ⟶ X) (Z D : X.IdealSheafData) (g : B ⟶ X₁)
    (hg : (Z.comap π).comap g = ⊤) :
    (Blowup.strictTransform π Z D).comap g = (D.comap π).comap g := by
  have hsupp : ((((Z.comap π).comap g).support : Closeds B) : Set B)
      = ⇑g.base ⁻¹' (((Z.comap π).support : Closeds X₁) : Set X₁) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hempty : ⇑g.base ⁻¹' (((Z.comap π).support : Closeds X₁) : Set X₁) = ∅ := by
    rw [← hsupp, hg]
    simp
  have hbase : ∀ b : B, ⇑g.base b ∈ ((complComapSupport π Z : X₁.Opens) : Set X₁) := by
    intro b
    rw [coe_complComapSupport]
    simp only [Set.mem_compl_iff]
    intro hmem
    have hb : b ∈ ⇑g.base ⁻¹' (((Z.comap π).support : Closeds X₁) : Set X₁) := hmem
    rw [hempty] at hb
    simp at hb
  have hrange : Set.range ⇑g.base ⊆
      Set.range ⇑(Scheme.Opens.ι (complComapSupport π Z)).base := by
    rintro x ⟨b, rfl⟩
    have h0 : ⇑g.base b ∈ ((complComapSupport π Z : X₁.Opens) : Set X₁) := hbase b
    simpa [Scheme.Opens.range_ι] using h0
  have hfac := IsOpenImmersion.lift_fac (Scheme.Opens.ι (complComapSupport π Z)) g hrange
  rw [← hfac, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
    strictTransform_comap_complComapSupport_ι]

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.CoordinateIdealOrderOne
section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))

private theorem le_one_of_not_two_le_consolidated196 {a : ℕ∞} (h : ¬ ((2 : ℕ) : ℕ∞) ≤ a) : a ≤ 1 := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · exact absurd le_top h
  · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp ha
    have hm : ¬ (2 ≤ m) := fun hh => h (by exact_mod_cast hh)
    have hm1 : m ≤ 1 := by omega
    exact_mod_cast hm1

section
variable {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ} (c : EtaleChart p V n)
include hV

theorem germ_coord_notMem_maximalIdeal_sq (j : Fin n) (y : X) (hy : y ∈ V)
    (hmem : c.coord j ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal) :
    (X.presheaf.germ V y hy).hom (c.coord j) ∉
      IsLocalRing.maximalIdeal (X.presheaf.stalk y) ^ 2 := by
  classical
  let instS : Algebra (CoordPolynomialRing k n) Γ(X, V) := c.algebra
  have instEt : Algebra.Etale (CoordPolynomialRing k n) Γ(X, V) :=
    EtaleChart.algebra_etale c hV
  let instAlg : Algebra Γ(X, V) (X.presheaf.stalk y) :=
    (X.presheaf.germ V y hy).hom.toAlgebra
  have hloc : IsLocalization (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
      (X.presheaf.stalk y) := hV.isLocalization_stalk ⟨y, hy⟩
  have hreg : IsRegularLocalRing (X.presheaf.stalk y) :=
    isRegularLocalRing_of_isLocalization_etale k n Γ(X, V)
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal (X.presheaf.stalk y)
  have hcoord : ∀ i : Fin n, etaleChartCoord k n Γ(X, V) i = c.coord i := fun i =>
    EtaleChart.coordRingHom_X c i
  have hJ : ∀ i ∈ ({j} : Finset (Fin n)),
      etaleChartCoord k n Γ(X, V) i ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := by
    intro i hi
    have hij : i = j := Finset.mem_singleton.mp hi
    rw [hij, hcoord j]
    exact hmem
  have hJA : ∀ i ∈ ({j} : Finset (Fin n)),
      algebraMap Γ(X, V) (X.presheaf.stalk y) (etaleChartCoord k n Γ(X, V) i)
        ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
    intro i hi
    have hij : i = j := Finset.mem_singleton.mp hi
    rw [hij, hcoord j]
    exact (germ_mem_maximalIdeal_iff hV y hy (c.coord j)).mpr hmem
  have hli := linearIndependent_toCotangent_etaleChartCoord k n Γ(X, V)
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal (X.presheaf.stalk y) ({j} : Finset (Fin n)) hJ hJA
  have hnot := IsRegularLocalRing.notMem_maximalIdeal_sq
    (fun i : {x : Fin n // x ∈ ({j} : Finset (Fin n))} =>
      algebraMap Γ(X, V) (X.presheaf.stalk y) (etaleChartCoord k n Γ(X, V) (i : Fin n)))
    (fun i => hJA (i : Fin n) i.2) hli ⟨j, Finset.mem_singleton_self j⟩
  intro hcon
  have h2 : algebraMap Γ(X, V) (X.presheaf.stalk y) (etaleChartCoord k n Γ(X, V) j)
      ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) ^ 2 := by
    rw [hcoord j]
    exact hcon
  exact hnot h2

private theorem orderAt_le_one_of_mem_of_restrictIdeal_eq_coordIdeal_consolidated196 (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S) (D : X.IdealSheafData)
    (hD : restrictIdeal D V = c.coordIdeal S) (y : X) (hy : y ∈ V) :
    orderAt D y ≤ 1 := by
  classical
  by_cases hys : y ∈ D.support
  · have hgerm : (X.presheaf.germ V y hy).hom (c.coord j) ∈ stalkIdeal D y := by
      refine germ_mem_stalkIdeal D y ⟨V, hV⟩ hy ?_
      rw [EtaleChart.ideal_eq_span_coord c hV D S hD]
      exact Ideal.subset_span ⟨j, Finset.mem_coe.mpr hj, rfl⟩
    have hmax : stalkIdeal D y ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
      (mem_support_iff_stalkIdeal_le_maximalIdeal D y).mp hys
    have hmem : c.coord j ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal :=
      (germ_mem_maximalIdeal_iff hV y hy (c.coord j)).mp (hmax hgerm)
    refine le_one_of_not_two_le_consolidated196 ?_
    intro h2
    rw [le_orderAt_iff] at h2
    exact germ_coord_notMem_maximalIdeal_sq p hV c j y hy hmem (h2 hgerm)
  · rw [(orderAt_eq_zero_iff_not_mem_support D y).mpr hys]
    exact zero_le_one

theorem orderAt_eq_one_of_restrictIdeal_eq_coordIdeal_singleton (j : Fin n) (D : X.IdealSheafData)
    (hD : restrictIdeal D V = c.coordIdeal {j}) (y : X) (hy : y ∈ V) (hys : y ∈ D.support) :
    orderAt D y = 1 :=
  le_antisymm (orderAt_le_one_of_mem_of_restrictIdeal_eq_coordIdeal_consolidated196 p hV c {j} j (Finset.mem_singleton_self j) D hD y hy)
    ((one_le_orderAt_iff_mem_support D y).mpr hys)


end

section
variable {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ} (c : EtaleChart p V n) (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S) (D : X.IdealSheafData) (hD : restrictIdeal D V = c.coordIdeal S) (y : X) (hy : y ∈ V)
include hV hj hD hy

theorem orderAt_le_one_of_restrictIdeal_eq_coordIdeal :
    orderAt D y ≤ 1 :=
  orderAt_le_one_of_mem_of_restrictIdeal_eq_coordIdeal_consolidated196 p hV c S j hj D hD y hy

theorem orderAt_eq_one_of_restrictIdeal_eq_coordIdeal (hys : y ∈ D.support) :
    orderAt D y = 1 :=
  le_antisymm (orderAt_le_one_of_mem_of_restrictIdeal_eq_coordIdeal_consolidated196 p hV c S j hj D hD y hy)
    ((one_le_orderAt_iff_mem_support D y).mpr hys)


end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactChartUniqueness
section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

section

variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}

section
variable {X₁ : Scheme.{u}} (V : X₁.Opens)

private theorem opensι_appLE_self_top_eq_topIso_inv_consolidated174 (e : (⊤ : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ e = V.topIso.inv := by
  simp
  exact AlgebraicGeometry.Scheme.presheaf_map_eq_of_parallel ..

private theorem germ_topIso_inv_mem_maximalIdeal_consolidated174 (y : ↥X₁)
    (hy : y ∈ V) (htop : pointOfMem V y hy ∈ (⊤ : (V.toScheme).Opens)) (s : Γ(X₁, V))
    (hs : (X₁.presheaf.germ V y hy).hom s ∈ IsLocalRing.maximalIdeal ↑(X₁.presheaf.stalk y)) :
    (V.toScheme.presheaf.germ ⊤ (pointOfMem V y hy) htop).hom (V.topIso.inv.hom s) ∈
      IsLocalRing.maximalIdeal ↑(V.toScheme.presheaf.stalk (pointOfMem V y hy)) := by
  have e : (⊤ : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ V := fun z _ => z.2
  have hy' : pointOfMem V y hy ∈ V.ι ⁻¹ᵁ V := hy
  have hnu : ¬ IsUnit ((X₁.presheaf.germ V y hy).hom s) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs
    exact hs
  have happ : V.topIso.inv = V.ι.app V ≫ V.toScheme.presheaf.map (homOfLE e).op :=
    (opensι_appLE_self_top_eq_topIso_inv_consolidated174 V e).symm
  have h1 : V.topIso.inv ≫ V.toScheme.presheaf.germ ⊤ (pointOfMem V y hy) htop
      = V.ι.app V ≫ V.toScheme.presheaf.germ (V.ι ⁻¹ᵁ V) (pointOfMem V y hy) hy' := by
    rw [happ, Category.assoc, TopCat.Presheaf.germ_res]
  have h2 : (V.toScheme.presheaf.germ ⊤ (pointOfMem V y hy) htop).hom (V.topIso.inv.hom s)
      = (V.toScheme.presheaf.germ (V.ι ⁻¹ᵁ V) (pointOfMem V y hy) hy').hom
          ((V.ι.app V).hom s) := by
    have h := congrArg
      (fun f : Γ(X₁, V) ⟶ V.toScheme.presheaf.stalk (pointOfMem V y hy) =>
        CommRingCat.Hom.hom f s) h1
    exact h
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, h2]
  intro hu
  apply hnu
  have hmem : pointOfMem V y hy ∈ V.ι ⁻¹ᵁ (X₁.basicOpen s) := by
    rw [Scheme.preimage_basicOpen]
    exact (V.toScheme.mem_basicOpen ((V.ι.app V).hom s) (pointOfMem V y hy) hy').2 hu
  exact (X₁.mem_basicOpen s y hy).1 hmem


end

section
variable {n : ℕ}

theorem chartsAgreeAt_of_coord_eq_of_germ_mem (c₁ c₂ : EtaleChart p U n) (j : Fin n)
    (x : X) (hx : x ∈ U)
    (hcoord : ∀ i : Fin n, i ≠ j → c₁.coord i = c₂.coord i)
    (hg₁ : (X.presheaf.germ U x hx).hom (c₁.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    (hg₂ : (X.presheaf.germ U x hx).hom (c₂.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x)) :
    ChartsAgreeAt c₁ c₂ x hx := by
  refine chartsAgreeAt_of_germ_sub_mem_maximalIdeal c₁ c₂ x hx ?_
  intro i
  by_cases hij : i = j
  · rw [hij]
    have e1 : U.topIso.inv.hom (c₁.coord j) = c₁.coordTop j :=
      Iso.hom_inv_id_apply U.topIso (c₁.coordTop j)
    have e2 : U.topIso.inv.hom (c₂.coord j) = c₂.coordTop j :=
      Iso.hom_inv_id_apply U.topIso (c₂.coordTop j)
    have h1 := germ_topIso_inv_mem_maximalIdeal_consolidated174 U x hx (by trivial) (c₁.coord j) hg₁
    have h2 := germ_topIso_inv_mem_maximalIdeal_consolidated174 U x hx (by trivial) (c₂.coord j) hg₂
    rw [e1] at h1
    rw [e2] at h2
    rw [map_sub]
    exact Submodule.sub_mem _ h1 h2
  · have hc := hcoord i hij
    have h' : U.topIso.inv.hom (U.topIso.hom.hom (c₁.coordTop i))
        = U.topIso.inv.hom (U.topIso.hom.hom (c₂.coordTop i)) :=
      congrArg (fun z => U.topIso.inv.hom z) hc
    have h'' : c₁.coordTop i = c₂.coordTop i :=
      (Iso.hom_inv_id_apply U.topIso (c₁.coordTop i)).symm.trans
        (h'.trans (Iso.hom_inv_id_apply U.topIso (c₂.coordTop i)))
    rw [h'', sub_self, map_zero]
    exact Submodule.zero_mem _

theorem coordIdeal_eq_of_coord_eq (hU : IsAffineOpen U) (c₁ c₂ : EtaleChart p U n)
    (S : Finset (Fin n)) (h : ∀ i ∈ S, c₁.coord i = c₂.coord i) :
    c₁.coordIdeal S = c₂.coordIdeal S := by
  have hUaff : IsAffine U.toScheme := hU
  have hcf : ∀ i ∈ S,
      (c₁.map.appTop).hom (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up i : ULift.{u} (Fin n)))
        = (c₂.map.appTop).hom (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up i : ULift.{u} (Fin n))) := by
    intro i hi
    have h1 := congrArg (fun z : Γ(X, U) => U.topIso.inv.hom z) (h i hi)
    have key : c₁.coordTop i = c₂.coordTop i :=
      (Iso.hom_inv_id_apply U.topIso (c₁.coordTop i)).symm.trans
        (h1.trans (Iso.hom_inv_id_apply U.topIso (c₂.coordTop i)))
    exact key
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_eq_ofIdealTop_span_coord,
    Scheme.IdealSheafData.comap_ofIdealTop, Scheme.IdealSheafData.comap_ofIdealTop,
    Ideal.map_span, Ideal.map_span]
  refine congrArg Scheme.IdealSheafData.ofIdealTop (congrArg Ideal.span ?_)
  refine Set.image_congr ?_
  rintro _ ⟨i, hi, rfl⟩
  exact hcf i (Finset.mem_coe.mp hi)


end

end

private theorem mem_maximalIdeal_of_map_eq_zero_consolidated174 {A C : Type*} [CommRing A] [CommRing C]
    [IsLocalRing A] [Nontrivial C] (σ : A →+* C) {a : A} (ha : σ a = 0) :
    a ∈ IsLocalRing.maximalIdeal A := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 : IsUnit (σ a) := hu.map σ
  rw [ha] at h1
  exact zero_ne_one (isUnit_zero_iff.mp h1)

section
variable {X W : Scheme.{u}}

private theorem eqToHom_comp_stalkMap_congr_consolidated174 (f g : W ⟶ X) (hfg : f = g)
    (z : ↥W) (x : ↥X) (hf : f.base z = x) (hg : g.base z = x) :
    eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hf.symm) ≫ f.stalkMap z
      = eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hg.symm) ≫ g.stalkMap z := by
  subst hfg
  rfl

private theorem map_stalkMap_stalkIdeal_eq_consolidated174 (f : W ⟶ X) (I : X.IdealSheafData)
    (z : ↥W) (x : ↥X) (hfz : f.base z = x) :
    Ideal.map ((f.stalkMap z).hom) (stalkIdeal I (f.base z))
      = Ideal.map ((eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hfz.symm)
          ≫ f.stalkMap z).hom) (stalkIdeal I x) := by
  subst hfz
  rw [eqToHom_refl, Category.id_comp]


end

section
variable {X W : Scheme.{u}} (f : W ⟶ X) (z : ↥W) (x : ↥X) (hfz : f.base z = x)

private theorem eqToHom_comp_stalkMap_germ_consolidated174 (U : X.Opens) (hxU : x ∈ U) (V : W.Opens) (hzV : z ∈ V)
    (e : V ≤ f ⁻¹ᵁ U) (s : Γ(X, U)) :
    (eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hfz.symm) ≫ f.stalkMap z).hom
        ((X.presheaf.germ U x hxU).hom s)
      = (W.presheaf.germ V z hzV).hom ((f.appLE U V e).hom s) := by
  subst hfz
  have key : X.presheaf.germ U (f.base z) hxU ≫ f.stalkMap z
      = f.appLE U V e ≫ W.presheaf.germ V z hzV := by
    rw [Scheme.Hom.appLE, Category.assoc, W.presheaf.germ_res (homOfLE e) z hzV]
    simp
  have h2 := congrArg (fun t : Γ(X, U) ⟶ W.presheaf.stalk z => CommRingCat.Hom.hom t s) key
  rw [eqToHom_refl, Category.id_comp]
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h2

private theorem eqToHom_comp_stalkMap_mem_maximalIdeal_consolidated174 {a : ↥(X.presheaf.stalk x)}
    (ha : a ∈ IsLocalRing.maximalIdeal ↥(X.presheaf.stalk x)) :
    (eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hfz.symm) ≫ f.stalkMap z).hom a
      ∈ IsLocalRing.maximalIdeal ↥(W.presheaf.stalk z) := by
  subst hfz
  rw [eqToHom_refl, Category.id_comp]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
  intro hu
  exact ha (isUnit_of_map_unit ((f.stalkMap z).hom) a hu)


end

private theorem appLE_topIso_hom_eq_appTop_consolidated174 {X W : Scheme.{u}} (U : X.Opens) (f : W ⟶ X)
    (g : W ⟶ U.toScheme) (hfg : f = g ≫ U.ι) (e : (⊤ : W.Opens) ≤ f ⁻¹ᵁ U)
    (t : Γ(U.toScheme, ⊤)) :
    (f.appLE U ⊤ e).hom (U.topIso.hom.hom t) = (g.appTop).hom t := by
  subst hfg
  have e₀ : (⊤ : (U.toScheme).Opens) ≤ U.ι ⁻¹ᵁ U := fun z _ => z.2
  have e' : (⊤ : W.Opens) ≤ g ⁻¹ᵁ (⊤ : (U.toScheme).Opens) := fun z _ => trivial
  have hcomp : (g ≫ U.ι).appLE U ⊤ e = U.ι.appLE U ⊤ e₀ ≫ g.appLE ⊤ ⊤ e' :=
    (Scheme.Hom.appLE_comp_appLE ..).symm
  have hpar : W.presheaf.map (homOfLE e').op
      = W.presheaf.map (𝟙 (Opposite.op (⊤ : W.Opens))) :=
    AlgebraicGeometry.Scheme.presheaf_map_eq_of_parallel ..
  have hmapid : W.presheaf.map (homOfLE e').op = 𝟙 Γ(W, ⊤) := by
    rw [hpar, CategoryTheory.Functor.map_id]
  have happ : g.appLE (⊤ : (U.toScheme).Opens) (⊤ : W.Opens) e' = g.appTop := by
    show g.app ⊤ ≫ W.presheaf.map (homOfLE e').op = g.appTop
    rw [hmapid]
    exact Category.comp_id _
  rw [hcomp, opensι_appLE_self_top_eq_topIso_inv_consolidated174 U e₀, happ]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  exact congrArg ((g.appTop).hom) (Iso.hom_inv_id_apply U.topIso t)

private theorem map_le_map_and_sub_mem_of_etaleCoordinates_shift_consolidated174 (kk : Type u) [Field kk] {ι : Type u} {R : Type u}
    [CommRing R] {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra ℚ B]
    [Algebra kk R] [Algebra (MvPolynomial ι kk) R] [IsScalarTower kk (MvPolynomial ι kk) R]
    [Algebra.FormallyEtale (MvPolynomial ι kk) R]
    (φ φ' : R →+* B) (j : ι) (b : R)
    (hcong : ∀ f : R, φ f - φ' f ∈ IsLocalRing.maximalIdeal B)
    (hβ : φ b ∈ IsLocalRing.maximalIdeal B)
    (hconst : ∀ c : kk, φ (algebraMap (MvPolynomial ι kk) R (MvPolynomial.C c))
      = φ' (algebraMap (MvPolynomial ι kk) R (MvPolynomial.C c)))
    (hne : ∀ i : ι, i ≠ j → φ (EtaleCoordinates.coord kk ι R i)
      = φ' (EtaleCoordinates.coord kk ι R i))
    (hj : φ (EtaleCoordinates.coord kk ι R j) + φ b
      = φ' (EtaleCoordinates.coord kk ι R j)) :
    (∀ M J : Ideal R, b ∈ M → M * derivIdeal kk J ≤ J → Ideal.map φ' J ≤ Ideal.map φ J)
      ∧ (∀ Iid : Ideal B, φ b ∈ Iid → ∀ f : R, φ f - φ' f ∈ Iid) := by
  classical
  have hD1 : (EtaleCoordinates.partialDeriv kk ι R j) (EtaleCoordinates.coord kk ι R j) = 1 :=
    EtaleCoordinates.partialDeriv_coord_self kk ι R j
  have hD0 : ∀ i : ι, i ≠ j →
      (EtaleCoordinates.partialDeriv kk ι R j) (EtaleCoordinates.coord kk ι R i) = 0 :=
    fun i hi => EtaleCoordinates.partialDeriv_coord_of_ne kk ι R j i (Ne.symm hi)
  have hderivConst : ∀ c : kk, (EtaleCoordinates.partialDeriv kk ι R j)
      (algebraMap (MvPolynomial ι kk) R (MvPolynomial.C c)) = 0 := by
    intro c
    have hmap : algebraMap (MvPolynomial ι kk) R (MvPolynomial.C c) = algebraMap kk R c := by
      rw [IsScalarTower.algebraMap_apply kk (MvPolynomial ι kk) R c]
      simp [MvPolynomial.algebraMap_eq]
    rw [hmap]
    exact Derivation.map_algebraMap _ c
  have hvar : ∀ (i : ι) (N : ℕ), 1 ≤ N →
      TaylorExpansion.truncatedSeries φ (EtaleCoordinates.partialDeriv kk ι R j) (φ b) N
          (algebraMap (MvPolynomial ι kk) R (MvPolynomial.X i)) -
        φ' (algebraMap (MvPolynomial ι kk) R (MvPolynomial.X i))
          ∈ IsLocalRing.maximalIdeal B ^ N := by
    intro i N hN
    have hco : algebraMap (MvPolynomial ι kk) R (MvPolynomial.X i)
        = EtaleCoordinates.coord kk ι R i := rfl
    rcases Nat.lt_or_ge N 2 with h2 | h2
    · have hN1 : N = 1 := by omega
      subst hN1
      rw [hco, truncatedSeries_length_one, pow_one]
      rcases eq_or_ne i j with hij | hij
      · subst hij
        have hsub : φ (EtaleCoordinates.coord kk ι R i)
            - φ' (EtaleCoordinates.coord kk ι R i) = -(φ b) := by
          rw [← hj]; ring
        rw [hsub]
        exact Submodule.neg_mem _ hβ
      · rw [hne i hij, sub_self]
        exact Submodule.zero_mem _
    · rcases eq_or_ne i j with hij | hij
      · subst hij
        rw [hco, truncatedSeries_of_deriv_deriv_eq_zero φ _ (φ b) N h2 _
            (by rw [hD1]; simp), hD1, map_one, one_mul, hj, sub_self]
        exact Submodule.zero_mem _
      · rw [hco, truncatedSeries_of_deriv_deriv_eq_zero φ _ (φ b) N h2 _
            (by rw [hD0 i hij]; simp), hD0 i hij, map_zero, zero_mul, add_zero,
          hne i hij, sub_self]
        exact Submodule.zero_mem _
  have hrep := isTaylorExpansionOn_mvPolynomial (k := kk) (ι := ι) φ φ'
    (EtaleCoordinates.partialDeriv kk ι R j) (φ b) hβ hconst hderivConst hvar
  have : Algebra.FormallyUnramified (MvPolynomial ι kk) R := inferInstance
  refine ⟨fun M J hbM hMJ => ?_, fun Iid hbI f => ?_⟩
  · exact map_le_map_of_pow_mul_iterate_deriv_mem (MvPolynomial ι kk) φ φ'
      (EtaleCoordinates.partialDeriv kk ι R j) (φ b) b J hcong hβ hrep rfl
      (pow_mul_iterate_deriv_mem_of_mul_derivIdeal_le kk M J (EtaleCoordinates.partialDeriv kk ι R j) b hMJ hbM)
  · exact sub_mem_of_isTaylorExpansionOn (MvPolynomial ι kk) φ φ'
      (EtaleCoordinates.partialDeriv kk ι R j) (φ b) hcong hβ hrep Iid hbI f

section
variable (k : Type u) [Field k]

private theorem map_le_map_and_sub_mem_of_etaleChart_coord_shift_consolidated174 [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (c : EtaleChart p U n) (j : Fin n)
    (x : X) (hx : x ∈ U) [Algebra k ↥(X.presheaf.stalk x)]
    (halg : ∀ a : k, algebraMap k ↥(X.presheaf.stalk x) a = stalkAlgebraMap k p x a)
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra ℚ B]
    (φ φ' : ↥(X.presheaf.stalk x) →+* B) (b : ↥(X.presheaf.stalk x))
    (hcong : ∀ f : ↥(X.presheaf.stalk x), φ f - φ' f ∈ IsLocalRing.maximalIdeal B)
    (hβ : φ b ∈ IsLocalRing.maximalIdeal B)
    (hconst : ∀ a : k, φ (stalkAlgebraMap k p x a) = φ' (stalkAlgebraMap k p x a))
    (hne : ∀ i : Fin n, i ≠ j → φ ((X.presheaf.germ U x hx).hom (c.coord i))
      = φ' ((X.presheaf.germ U x hx).hom (c.coord i)))
    (hj : φ ((X.presheaf.germ U x hx).hom (c.coord j)) + φ b
      = φ' ((X.presheaf.germ U x hx).hom (c.coord j))) :
    (∀ M J : Ideal ↥(X.presheaf.stalk x), b ∈ M → M * derivIdeal k J ≤ J →
        Ideal.map φ' J ≤ Ideal.map φ J)
      ∧ (∀ Iid : Ideal B, φ b ∈ Iid → ∀ f : ↥(X.presheaf.stalk x), φ f - φ' f ∈ Iid) := by
  classical
  let instP : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) ↥(X.presheaf.stalk x) :=
    RingHom.toAlgebra ((X.presheaf.germ U x hx).hom.comp c.coordRingHom)
  have instScalarTower : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k)
      ↥(X.presheaf.stalk x) := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [MvPolynomial.algebraMap_eq, halg a]
    show stalkAlgebraMap k p x a
      = (X.presheaf.germ U x hx).hom (c.coordRingHom (MvPolynomial.C a))
    rw [EtaleChart.coordRingHom_C, germ_sectionsAlgebraMap_apply]
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k)
      ↥(X.presheaf.stalk x) := by
    let instChart : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := c.algebra
    let instGerm : Algebra Γ(X, U) ↥(X.presheaf.stalk x) :=
      (X.presheaf.germ U x hx).hom.toAlgebra
    have : IsScalarTower (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U)
        ↥(X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) :=
      c.algebra_formallyEtale hU
    have : IsLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
        ↥(X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hx⟩
    have : Algebra.FormallyEtale Γ(X, U) ↥(X.presheaf.stalk x) :=
      Algebra.FormallyEtale.of_isLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    exact Algebra.FormallyEtale.comp (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U)
      ↥(X.presheaf.stalk x)
  have hcd : ∀ i : Fin n,
      EtaleCoordinates.coord k (ULift.{u} (Fin n)) ↥(X.presheaf.stalk x) (ULift.up i)
        = (X.presheaf.germ U x hx).hom (c.coord i) := by
    intro i
    show (X.presheaf.germ U x hx).hom (c.coordRingHom (MvPolynomial.X (ULift.up i))) = _
    rw [EtaleChart.coordRingHom_X]
  have hconst' : ∀ a : k,
      φ (algebraMap (MvPolynomial (ULift.{u} (Fin n)) k) ↥(X.presheaf.stalk x)
            (MvPolynomial.C a))
        = φ' (algebraMap (MvPolynomial (ULift.{u} (Fin n)) k) ↥(X.presheaf.stalk x)
            (MvPolynomial.C a)) := by
    intro a
    have hA : algebraMap (MvPolynomial (ULift.{u} (Fin n)) k) ↥(X.presheaf.stalk x)
        (MvPolynomial.C a) = stalkAlgebraMap k p x a := by
      show (X.presheaf.germ U x hx).hom (c.coordRingHom (MvPolynomial.C a)) = _
      rw [EtaleChart.coordRingHom_C, germ_sectionsAlgebraMap_apply]
    rw [hA, hconst a]
  have hne' : ∀ i : ULift.{u} (Fin n), i ≠ ULift.up j →
      φ (EtaleCoordinates.coord k (ULift.{u} (Fin n)) ↥(X.presheaf.stalk x) i)
        = φ' (EtaleCoordinates.coord k (ULift.{u} (Fin n)) ↥(X.presheaf.stalk x) i) := by
    rintro ⟨i⟩ hi
    have hij : i ≠ j := fun hc => hi (by rw [hc])
    rw [hcd i]
    exact hne i hij
  have hj' : φ (EtaleCoordinates.coord k (ULift.{u} (Fin n)) ↥(X.presheaf.stalk x)
        (ULift.up j)) + φ b
      = φ' (EtaleCoordinates.coord k (ULift.{u} (Fin n)) ↥(X.presheaf.stalk x)
        (ULift.up j)) := by
    rw [hcd j]
    exact hj
  exact map_le_map_and_sub_mem_of_etaleCoordinates_shift_consolidated174 k φ φ' (ULift.up j) b hcong hβ hconst' hne' hj'

private theorem chartPullbackStalkMap_compat_consolidated174 {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    {U : X.Opens} {n : ℕ} (c₁ c₂ : EtaleChart p U n) (x : X) (hx : x ∈ U)
    (h : ChartsAgreeAt c₁ c₂ x hx) :
    (∀ i : Fin n,
        (chartPullbackFstStalkMap c₁ c₂ x hx h).hom ((X.presheaf.germ U x hx).hom (c₁.coord i))
          = (chartPullbackSndStalkMap c₁ c₂ x hx h).hom
              ((X.presheaf.germ U x hx).hom (c₂.coord i)))
      ∧ (∀ a : k, (chartPullbackFstStalkMap c₁ c₂ x hx h).hom (stalkAlgebraMap k p x a)
          = (chartPullbackSndStalkMap c₁ c₂ x hx h).hom (stalkAlgebraMap k p x a))
      ∧ (∀ a : ↥(X.presheaf.stalk x),
          (chartPullbackSndStalkMap c₁ c₂ x hx h).hom a - (chartPullbackFstStalkMap c₁ c₂ x hx h).hom a
            ∈ IsLocalRing.maximalIdeal
                ↥((chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h))) := by
  have hfb : (chartPullbackFst c₁ c₂).base (chartPullbackPoint c₁ c₂ x hx h) = x :=
    chartPullbackFst_base_chartPullbackPoint c₁ c₂ x hx h
  have hsb : (chartPullbackSnd c₁ c₂).base (chartPullbackPoint c₁ c₂ x hx h) = x :=
    chartPullbackSnd_base_chartPullbackPoint c₁ c₂ x hx h
  have e₁ : (⊤ : (chartPullback c₁ c₂).Opens) ≤ (chartPullbackFst c₁ c₂) ⁻¹ᵁ U :=
    fun z _ => ((pullback.fst c₁.map c₂.map).base z).2
  have e₂ : (⊤ : (chartPullback c₁ c₂).Opens) ≤ (chartPullbackSnd c₁ c₂) ⁻¹ᵁ U :=
    fun z _ => ((pullback.snd c₁.map c₂.map).base z).2
  have hcoordEach : ∀ i : Fin n,
      (chartPullbackFstStalkMap c₁ c₂ x hx h).hom ((X.presheaf.germ U x hx).hom (c₁.coord i))
        = (chartPullbackSndStalkMap c₁ c₂ x hx h).hom
            ((X.presheaf.germ U x hx).hom (c₂.coord i)) := by
    intro i
    rw [chartPullbackFstStalkMap_eq, chartPullbackSndStalkMap_eq,
      eqToHom_comp_stalkMap_germ_consolidated174 (chartPullbackFst c₁ c₂) (chartPullbackPoint c₁ c₂ x hx h) x hfb U hx ⊤
        trivial e₁ (c₁.coord i),
      eqToHom_comp_stalkMap_germ_consolidated174 (chartPullbackSnd c₁ c₂) (chartPullbackPoint c₁ c₂ x hx h) x hsb U hx ⊤
        trivial e₂ (c₂.coord i)]
    have hc₁ : c₁.coord i = U.topIso.hom.hom (c₁.coordTop i) := rfl
    have hc₂ : c₂.coord i = U.topIso.hom.hom (c₂.coordTop i) := rfl
    rw [hc₁, hc₂,
      appLE_topIso_hom_eq_appTop_consolidated174 U (chartPullbackFst c₁ c₂) (pullback.fst c₁.map c₂.map) rfl e₁
        (c₁.coordTop i),
      appLE_topIso_hom_eq_appTop_consolidated174 U (chartPullbackSnd c₁ c₂) (pullback.snd c₁.map c₂.map) rfl e₂
        (c₂.coordTop i)]
    exact congrArg _ (chartPullback_coordTop_eq c₁ c₂ i)
  have hscalar : ∀ a : k,
      (chartPullbackFstStalkMap c₁ c₂ x hx h).hom (stalkAlgebraMap k p x a)
        = (chartPullbackSndStalkMap c₁ c₂ x hx h).hom (stalkAlgebraMap k p x a) := by
    intro a
    rw [← germ_sectionsAlgebraMap_apply k p U x hx a, chartPullbackFstStalkMap_eq,
      chartPullbackSndStalkMap_eq,
      eqToHom_comp_stalkMap_germ_consolidated174 (chartPullbackFst c₁ c₂) (chartPullbackPoint c₁ c₂ x hx h) x hfb U hx ⊤
        trivial e₁ (sectionsAlgebraMap k p U a),
      eqToHom_comp_stalkMap_germ_consolidated174 (chartPullbackSnd c₁ c₂) (chartPullbackPoint c₁ c₂ x hx h) x hsb U hx ⊤
        trivial e₂ (sectionsAlgebraMap k p U a),
      sectionsAlgebraMap_appLE_apply k p (chartPullbackFst c₁ c₂) U ⊤ e₁ a,
      sectionsAlgebraMap_appLE_apply k p (chartPullbackSnd c₁ c₂) U ⊤ e₂ a,
      chartPullbackFst_comp_eq_chartPullbackSnd_comp c₁ c₂]
  refine ⟨hcoordEach, hscalar, ?_⟩
  have hmor : chartPullbackLift c₁ c₂ x hx h ≫ chartPullbackFst c₁ c₂
      = chartPullbackLift c₁ c₂ x hx h ≫ chartPullbackSnd c₁ c₂ := by
    show chartPullbackLift c₁ c₂ x hx h ≫ (pullback.fst c₁.map c₂.map ≫ U.ι)
      = chartPullbackLift c₁ c₂ x hx h ≫ (pullback.snd c₁.map c₂.map ≫ U.ι)
    rw [chartPullbackLift_fst_assoc, chartPullbackLift_snd_assoc]
  have hbf : (chartPullbackLift c₁ c₂ x hx h ≫ chartPullbackFst c₁ c₂).base
      (specResidueFieldPoint (pointOfMem U x hx)) = x := hfb
  have hbs : (chartPullbackLift c₁ c₂ x hx h ≫ chartPullbackSnd c₁ c₂).base
      (specResidueFieldPoint (pointOfMem U x hx)) = x := hsb
  have hstalkeq := eqToHom_comp_stalkMap_congr_consolidated174 (chartPullbackLift c₁ c₂ x hx h ≫ chartPullbackFst c₁ c₂)
    (chartPullbackLift c₁ c₂ x hx h ≫ chartPullbackSnd c₁ c₂) hmor
    (specResidueFieldPoint (pointOfMem U x hx)) x hbf hbs
  obtain ⟨σ, hσ⟩ : ∃ σ : (chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h) ⟶
      (Spec (U.toScheme.residueField (pointOfMem U x hx))).presheaf.stalk
        (specResidueFieldPoint (pointOfMem U x hx)),
      σ = (chartPullbackLift c₁ c₂ x hx h).stalkMap (specResidueFieldPoint (pointOfMem U x hx)) :=
    ⟨_, rfl⟩
  have hcomp1 : (chartPullbackLift c₁ c₂ x hx h ≫ chartPullbackFst c₁ c₂).stalkMap
        (specResidueFieldPoint (pointOfMem U x hx))
      = (chartPullbackFst c₁ c₂).stalkMap (chartPullbackPoint c₁ c₂ x hx h) ≫ σ := by
    rw [hσ]
    exact Scheme.Hom.stalkMap_comp _ _ _
  have hcomp2 : (chartPullbackLift c₁ c₂ x hx h ≫ chartPullbackSnd c₁ c₂).stalkMap
        (specResidueFieldPoint (pointOfMem U x hx))
      = (chartPullbackSnd c₁ c₂).stalkMap (chartPullbackPoint c₁ c₂ x hx h) ≫ σ := by
    rw [hσ]
    exact Scheme.Hom.stalkMap_comp _ _ _
  have hkey : chartPullbackFstStalkMap c₁ c₂ x hx h ≫ σ
      = chartPullbackSndStalkMap c₁ c₂ x hx h ≫ σ := by
    rw [chartPullbackFstStalkMap_eq, chartPullbackSndStalkMap_eq, Category.assoc, Category.assoc,
      ← hcomp1, ← hcomp2]
    exact hstalkeq
  intro a
  have hc := congrArg CommRingCat.Hom.hom hkey
  have h0 : σ.hom ((chartPullbackFstStalkMap c₁ c₂ x hx h).hom a)
      = σ.hom ((chartPullbackSndStalkMap c₁ c₂ x hx h).hom a) := DFunLike.congr_fun hc a
  refine mem_maximalIdeal_of_map_eq_zero_consolidated174 σ.hom ?_
  rw [map_sub, ← h0, sub_self]

theorem stalkIdeal_comap_chartPullbackPoint_eq
    [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) {m : ℕ} (_hm : 1 ≤ m)
    (hinv : IsMaxContactInvariant k p I m)
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (c₁ c₂ : EtaleChart p U n) (j : Fin n)
    (hcoord : ∀ i : Fin n, i ≠ j → c₁.coord i = c₂.coord i)
    (x : X) (hx : x ∈ U)
    (hmem₁ : c₁.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩)
    (hmem₂ : c₂.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩)
    (hg₁ : (X.presheaf.germ U x hx).hom (c₁.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    (hg₂ : (X.presheaf.germ U x hx).hom (c₂.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    [IsLocallyNoetherian (chartPullback c₁ c₂)]
    (h : ChartsAgreeAt c₁ c₂ x hx) :
    stalkIdeal (I.comap (chartPullbackFst c₁ c₂)) (chartPullbackPoint c₁ c₂ x hx h) =
      stalkIdeal (I.comap (chartPullbackSnd c₁ c₂)) (chartPullbackPoint c₁ c₂ x hx h) := by
  classical
  obtain ⟨hcoordEach, hscalar, hcong21⟩ := chartPullbackStalkMap_compat_consolidated174 k p c₁ c₂ x hx h
  have hcong12 : ∀ a : ↥(X.presheaf.stalk x),
      (chartPullbackFstStalkMap c₁ c₂ x hx h).hom a - (chartPullbackSndStalkMap c₁ c₂ x hx h).hom a
        ∈ IsLocalRing.maximalIdeal
            ↥((chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h)) := by
    intro a
    have hneg := Submodule.neg_mem _ (hcong21 a)
    rwa [neg_sub] at hneg
  have hfb : (chartPullbackFst c₁ c₂).base (chartPullbackPoint c₁ c₂ x hx h) = x :=
    chartPullbackFst_base_chartPullbackPoint c₁ c₂ x hx h
  have hsb : (chartPullbackSnd c₁ c₂).base (chartPullbackPoint c₁ c₂ x hx h) = x :=
    chartPullbackSnd_base_chartPullbackPoint c₁ c₂ x hx h
  let instRk : Algebra k ↥(X.presheaf.stalk x) := stalkAlgebra k p x
  have instBnoeth : IsNoetherianRing
      ↥((chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h)) := inferInstance
  let instAlgebraRat : Algebra ℚ ↥((chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h)) :=
    RingHom.toAlgebra
      ((stalkAlgebraMap k (chartPullbackFst c₁ c₂ ≫ p) (chartPullbackPoint c₁ c₂ x hx h)).comp
        (algebraMap ℚ k))
  have hinv' : maxContactIdeal k p I m * derivIdealSheaf k p I ≤ I := hinv
  have hMJ : stalkIdeal (maxContactIdeal k p I m) x * derivIdeal k (stalkIdeal I x)
      ≤ stalkIdeal I x := by
    have h0 := stalkIdeal_mono hinv' x
    rw [stalkIdeal_mul, stalkIdeal_derivIdealSheaf k p I x] at h0
    exact h0
  have hM₁ : (X.presheaf.germ U x hx).hom (c₁.coord j)
      ∈ stalkIdeal (maxContactIdeal k p I m) x :=
    germ_mem_stalkIdeal (maxContactIdeal k p I m) x ⟨U, hU⟩ hx hmem₁
  have hM₂ : (X.presheaf.germ U x hx).hom (c₂.coord j)
      ∈ stalkIdeal (maxContactIdeal k p I m) x :=
    germ_mem_stalkIdeal (maxContactIdeal k p I m) x ⟨U, hU⟩ hx hmem₂
  have hcoordNe : ∀ i : Fin n, i ≠ j →
      (X.presheaf.germ U x hx).hom (c₁.coord i) = (X.presheaf.germ U x hx).hom (c₂.coord i) :=
    fun i hi => congrArg _ (hcoord i hi)
  have h12 : Ideal.map (chartPullbackFstStalkMap c₁ c₂ x hx h).hom (stalkIdeal I x)
      ≤ Ideal.map (chartPullbackSndStalkMap c₁ c₂ x hx h).hom (stalkIdeal I x) := by
    have hne : ∀ i : Fin n, i ≠ j →
        (chartPullbackSndStalkMap c₁ c₂ x hx h).hom ((X.presheaf.germ U x hx).hom (c₁.coord i))
          = (chartPullbackFstStalkMap c₁ c₂ x hx h).hom
              ((X.presheaf.germ U x hx).hom (c₁.coord i)) := by
      intro i hi
      rw [hcoordNe i hi, ← hcoordEach i, hcoordNe i hi]
    have hj' : (chartPullbackSndStalkMap c₁ c₂ x hx h).hom
          ((X.presheaf.germ U x hx).hom (c₁.coord j))
        + (chartPullbackSndStalkMap c₁ c₂ x hx h).hom
            ((X.presheaf.germ U x hx).hom (c₂.coord j)
              - (X.presheaf.germ U x hx).hom (c₁.coord j))
        = (chartPullbackFstStalkMap c₁ c₂ x hx h).hom
            ((X.presheaf.germ U x hx).hom (c₁.coord j)) := by
      rw [map_sub, hcoordEach j]
      ring
    have hβ : (chartPullbackSndStalkMap c₁ c₂ x hx h).hom
        ((X.presheaf.germ U x hx).hom (c₂.coord j)
          - (X.presheaf.germ U x hx).hom (c₁.coord j))
        ∈ IsLocalRing.maximalIdeal
            ↥((chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h)) :=
      eqToHom_comp_stalkMap_mem_maximalIdeal_consolidated174 (chartPullbackSnd c₁ c₂) (chartPullbackPoint c₁ c₂ x hx h) x
        hsb (Submodule.sub_mem _ hg₂ hg₁)
    exact (map_le_map_and_sub_mem_of_etaleChart_coord_shift_consolidated174 k p hU c₁ j x hx (fun _ => rfl)
      (chartPullbackSndStalkMap c₁ c₂ x hx h).hom (chartPullbackFstStalkMap c₁ c₂ x hx h).hom
      ((X.presheaf.germ U x hx).hom (c₂.coord j) - (X.presheaf.germ U x hx).hom (c₁.coord j))
      hcong21 hβ (fun a => (hscalar a).symm) hne hj').1
      (stalkIdeal (maxContactIdeal k p I m) x) (stalkIdeal I x)
      (Submodule.sub_mem _ hM₂ hM₁) hMJ
  have h21 : Ideal.map (chartPullbackSndStalkMap c₁ c₂ x hx h).hom (stalkIdeal I x)
      ≤ Ideal.map (chartPullbackFstStalkMap c₁ c₂ x hx h).hom (stalkIdeal I x) := by
    have hne : ∀ i : Fin n, i ≠ j →
        (chartPullbackFstStalkMap c₁ c₂ x hx h).hom ((X.presheaf.germ U x hx).hom (c₂.coord i))
          = (chartPullbackSndStalkMap c₁ c₂ x hx h).hom
              ((X.presheaf.germ U x hx).hom (c₂.coord i)) := by
      intro i hi
      rw [← hcoordNe i hi, hcoordEach i, hcoordNe i hi]
    have hj' : (chartPullbackFstStalkMap c₁ c₂ x hx h).hom
          ((X.presheaf.germ U x hx).hom (c₂.coord j))
        + (chartPullbackFstStalkMap c₁ c₂ x hx h).hom
            ((X.presheaf.germ U x hx).hom (c₁.coord j)
              - (X.presheaf.germ U x hx).hom (c₂.coord j))
        = (chartPullbackSndStalkMap c₁ c₂ x hx h).hom
            ((X.presheaf.germ U x hx).hom (c₂.coord j)) := by
      rw [map_sub, ← hcoordEach j]
      ring
    have hβ : (chartPullbackFstStalkMap c₁ c₂ x hx h).hom
        ((X.presheaf.germ U x hx).hom (c₁.coord j)
          - (X.presheaf.germ U x hx).hom (c₂.coord j))
        ∈ IsLocalRing.maximalIdeal
            ↥((chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h)) :=
      eqToHom_comp_stalkMap_mem_maximalIdeal_consolidated174 (chartPullbackFst c₁ c₂) (chartPullbackPoint c₁ c₂ x hx h) x
        hfb (Submodule.sub_mem _ hg₁ hg₂)
    exact (map_le_map_and_sub_mem_of_etaleChart_coord_shift_consolidated174 k p hU c₂ j x hx (fun _ => rfl)
      (chartPullbackFstStalkMap c₁ c₂ x hx h).hom (chartPullbackSndStalkMap c₁ c₂ x hx h).hom
      ((X.presheaf.germ U x hx).hom (c₁.coord j) - (X.presheaf.germ U x hx).hom (c₂.coord j))
      hcong12 hβ hscalar hne hj').1
      (stalkIdeal (maxContactIdeal k p I m) x) (stalkIdeal I x)
      (Submodule.sub_mem _ hM₁ hM₂) hMJ
  have key : Ideal.map (chartPullbackFstStalkMap c₁ c₂ x hx h).hom (stalkIdeal I x)
      = Ideal.map (chartPullbackSndStalkMap c₁ c₂ x hx h).hom (stalkIdeal I x) :=
    le_antisymm h12 h21
  rw [stalkIdeal_comap, stalkIdeal_comap,
    map_stalkMap_stalkIdeal_eq_consolidated174 (chartPullbackFst c₁ c₂) I (chartPullbackPoint c₁ c₂ x hx h) x hfb,
    map_stalkMap_stalkIdeal_eq_consolidated174 (chartPullbackSnd c₁ c₂) I (chartPullbackPoint c₁ c₂ x hx h) x hsb]
  exact key


end

private theorem spec_map_comp_fromSpecStalk_eq_consolidated174 {X Z : Scheme.{u}} (z : ↥Z) {x₁ x₂ : ↥X}
    (hx : x₁ = x₂) (α : X.presheaf.stalk x₁ ⟶ Z.presheaf.stalk z)
    (β : X.presheaf.stalk x₂ ⟶ Z.presheaf.stalk z)
    (hαβ : α = eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hx) ≫ β) :
    Spec.map α ≫ X.fromSpecStalk x₁ = Spec.map β ≫ X.fromSpecStalk x₂ := by
  subst hx
  rw [hαβ, eqToHom_refl, Category.id_comp]

private theorem fromSpecStalk_comp_eq_of_stalkMap_eq_consolidated174 {X Y Z : Scheme.{u}} (ιm : Z ⟶ Y) (f g : Y ⟶ X) (z : ↥Z)
    (w : ↥Y) (hw : ιm.base z = w) (x : ↥X) (hf : f.base w = x) (hg : g.base w = x)
    (φ₁ φ₂ : X.presheaf.stalk x ⟶ Y.presheaf.stalk w)
    (hφ₁ : φ₁ = eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hf.symm) ≫ f.stalkMap w)
    (hφ₂ : φ₂ = eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hg.symm) ≫ g.stalkMap w)
    (ρ : Y.presheaf.stalk w ⟶ Z.presheaf.stalk z)
    (hρ : ρ = eqToHom (congrArg (fun y : ↥Y => Y.presheaf.stalk y) hw.symm) ≫ ιm.stalkMap z)
    (hker : ∀ a : ↥(X.presheaf.stalk x), ρ.hom (φ₁.hom a) = ρ.hom (φ₂.hom a)) :
    Z.fromSpecStalk z ≫ ιm ≫ f = Z.fromSpecStalk z ≫ ιm ≫ g := by
  subst hφ₁
  subst hφ₂
  subst hρ
  subst hw
  subst hf
  have hstalk : f.stalkMap (ιm.base z) ≫ ιm.stalkMap z
      = eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hg.symm)
          ≫ (g.stalkMap (ιm.base z) ≫ ιm.stalkMap z) := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    have ha := hker a
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, eqToHom_refl,
      CommRingCat.hom_id, RingHom.id_apply] at ha ⊢
    exact ha
  have key := spec_map_comp_fromSpecStalk_eq_consolidated174 (X := X) z hg.symm
    (f.stalkMap (ιm.base z) ≫ ιm.stalkMap z) (g.stalkMap (ιm.base z) ≫ ιm.stalkMap z) hstalk
  have L : ∀ u : Y ⟶ X, Z.fromSpecStalk z ≫ ιm ≫ u
      = Spec.map (u.stalkMap (ιm.base z) ≫ ιm.stalkMap z)
        ≫ X.fromSpecStalk (u.base (ιm.base z)) := by
    intro u
    rw [← Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk ιm (x := z), Category.assoc,
      ← Scheme.SpecMap_stalkMap_fromSpecStalk u (x := ιm.base z), ← Category.assoc,
      ← Spec.map_comp]
  rw [L f, L g]
  exact key

private theorem subschemeι_appLE_eq_zero_consolidated174 {Y : Scheme.{u}} (J : Y.IdealSheafData)
    (V : Y.affineOpens) {s : Γ(Y, V.1)} (hs : s ∈ J.ideal V) :
    (J.subschemeι.appLE V.1 (J.subschemeι ⁻¹ᵁ V.1) le_rfl).hom s = 0 := by
  have hker : J.subschemeι.ker = J := Scheme.IdealSheafData.ker_subschemeι ..
  have h2 : s ∈ (J.subschemeι.ker).ideal V := by rw [hker]; exact hs
  have h3 : (J.subschemeι.app V.1).hom s = 0 :=
    RingHom.mem_ker.mp (J.subschemeι.ideal_ker_le V h2)
  rw [Scheme.Hom.appLE]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, h3, map_zero]

private theorem stalkMap_germ_eq_zero_of_mem_ideal_consolidated174 {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.IdealSheafData)
    (z : ↥((M.comap f).subscheme)) (w : ↥Y)
    (hw : (M.comap f).subschemeι.base z = w)
    (x : ↥X) (hf : f.base w = x) (U : X.Opens) (hU : IsAffineOpen U) (hxU : x ∈ U)
    (V : Y.Opens) (hV : IsAffineOpen V) (hwV : w ∈ V) (eV : V ≤ f ⁻¹ᵁ U)
    (s : Γ(X, U)) (hs : s ∈ M.ideal ⟨U, hU⟩) :
    (eqToHom (congrArg (fun y : ↥Y => Y.presheaf.stalk y) hw.symm)
        ≫ (M.comap f).subschemeι.stalkMap z).hom
      ((eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hf.symm) ≫ f.stalkMap w).hom
        ((X.presheaf.germ U x hxU).hom s)) = 0 := by
  rw [eqToHom_comp_stalkMap_germ_consolidated174 f w x hf U hxU V hwV eV s]
  have hzV : z ∈ (M.comap f).subschemeι ⁻¹ᵁ V := by
    show (M.comap f).subschemeι.base z ∈ V
    rw [hw]
    exact hwV
  rw [eqToHom_comp_stalkMap_germ_consolidated174 (M.comap f).subschemeι z w hw V hwV
      ((M.comap f).subschemeι ⁻¹ᵁ V) hzV le_rfl ((f.appLE U V eV).hom s)]
  have h3 : (f.appLE U V eV).hom s ∈ (M.comap f).ideal ⟨V, hV⟩ :=
    Scheme.IdealSheafData.appLE_mem_comap_ideal M f ⟨U, hU⟩ ⟨V, hV⟩ eV hs
  rw [subschemeι_appLE_eq_zero_consolidated174 (M.comap f) ⟨V, hV⟩ h3, map_zero]

section
variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]

private theorem chartPullbackFstStalkMap_eq_snd_of_coord_eq_zero_consolidated174
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (c₁ c₂ : EtaleChart p U n) (j : Fin n)
    (hcoord : ∀ i : Fin n, i ≠ j → c₁.coord i = c₂.coord i)
    (x : X) (hx : x ∈ U)
    (hg₁ : (X.presheaf.germ U x hx).hom (c₁.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    (hg₂ : (X.presheaf.germ U x hx).hom (c₂.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    [IsLocallyNoetherian (chartPullback c₁ c₂)]
    (h : ChartsAgreeAt c₁ c₂ x hx)
    (C : CommRingCat.{u})
    (ρ : (chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h) ⟶ C)
    (hv₁ : ρ.hom ((chartPullbackFstStalkMap c₁ c₂ x hx h).hom
      ((X.presheaf.germ U x hx).hom (c₁.coord j))) = 0)
    (hv₂ : ρ.hom ((chartPullbackFstStalkMap c₁ c₂ x hx h).hom
      ((X.presheaf.germ U x hx).hom (c₂.coord j))) = 0) :
    ∀ a : ↥(X.presheaf.stalk x),
      ρ.hom ((chartPullbackFstStalkMap c₁ c₂ x hx h).hom a)
        = ρ.hom ((chartPullbackSndStalkMap c₁ c₂ x hx h).hom a) := by
  classical
  obtain ⟨hcoordEach, hscalar, hcong21⟩ := chartPullbackStalkMap_compat_consolidated174 k p c₁ c₂ x hx h
  have hcong12 : ∀ a : ↥(X.presheaf.stalk x),
      (chartPullbackFstStalkMap c₁ c₂ x hx h).hom a - (chartPullbackSndStalkMap c₁ c₂ x hx h).hom a
        ∈ IsLocalRing.maximalIdeal
            ↥((chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h)) := by
    intro a
    have hneg := Submodule.neg_mem _ (hcong21 a)
    rwa [neg_sub] at hneg
  have hfb : (chartPullbackFst c₁ c₂).base (chartPullbackPoint c₁ c₂ x hx h) = x :=
    chartPullbackFst_base_chartPullbackPoint c₁ c₂ x hx h
  have hcoordNe : ∀ i : Fin n, i ≠ j →
      (X.presheaf.germ U x hx).hom (c₁.coord i) = (X.presheaf.germ U x hx).hom (c₂.coord i) :=
    fun i hi => congrArg _ (hcoord i hi)
  let instRk : Algebra k ↥(X.presheaf.stalk x) := stalkAlgebra k p x
  have instBnoeth : IsNoetherianRing
      ↥((chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h)) := inferInstance
  let instAlgebraRat : Algebra ℚ ↥((chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h)) :=
    RingHom.toAlgebra
      ((stalkAlgebraMap k (chartPullbackFst c₁ c₂ ≫ p) (chartPullbackPoint c₁ c₂ x hx h)).comp
        (algebraMap ℚ k))
  have hne : ∀ i : Fin n, i ≠ j →
      (chartPullbackFstStalkMap c₁ c₂ x hx h).hom ((X.presheaf.germ U x hx).hom (c₂.coord i))
        = (chartPullbackSndStalkMap c₁ c₂ x hx h).hom
            ((X.presheaf.germ U x hx).hom (c₂.coord i)) := by
    intro i hi
    rw [← hcoordNe i hi, hcoordEach i, hcoordNe i hi]
  have hj' : (chartPullbackFstStalkMap c₁ c₂ x hx h).hom
        ((X.presheaf.germ U x hx).hom (c₂.coord j))
      + (chartPullbackFstStalkMap c₁ c₂ x hx h).hom
          ((X.presheaf.germ U x hx).hom (c₁.coord j)
            - (X.presheaf.germ U x hx).hom (c₂.coord j))
      = (chartPullbackSndStalkMap c₁ c₂ x hx h).hom
          ((X.presheaf.germ U x hx).hom (c₂.coord j)) := by
    rw [map_sub, ← hcoordEach j]
    ring
  have hβ : (chartPullbackFstStalkMap c₁ c₂ x hx h).hom
      ((X.presheaf.germ U x hx).hom (c₁.coord j)
        - (X.presheaf.germ U x hx).hom (c₂.coord j))
      ∈ IsLocalRing.maximalIdeal
          ↥((chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ x hx h)) :=
    eqToHom_comp_stalkMap_mem_maximalIdeal_consolidated174 (chartPullbackFst c₁ c₂) (chartPullbackPoint c₁ c₂ x hx h) x
      hfb (Submodule.sub_mem _ hg₁ hg₂)
  have hbI : (chartPullbackFstStalkMap c₁ c₂ x hx h).hom
      ((X.presheaf.germ U x hx).hom (c₁.coord j)
        - (X.presheaf.germ U x hx).hom (c₂.coord j)) ∈ RingHom.ker ρ.hom := by
    rw [RingHom.mem_ker, map_sub, map_sub, hv₁, hv₂, sub_zero]
  have hsub := (map_le_map_and_sub_mem_of_etaleChart_coord_shift_consolidated174 k p hU c₂ j x hx (fun _ => rfl)
    (chartPullbackFstStalkMap c₁ c₂ x hx h).hom (chartPullbackSndStalkMap c₁ c₂ x hx h).hom
    ((X.presheaf.germ U x hx).hom (c₁.coord j) - (X.presheaf.germ U x hx).hom (c₂.coord j))
    hcong12 hβ hscalar hne hj').2 (RingHom.ker ρ.hom) hbI
  intro a
  have ha := hsub a
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at ha
  exact ha

theorem fromSpecStalk_comp_subschemeι_chartPullback_eq
    (I : X.IdealSheafData) {m : ℕ} (_hm : 1 ≤ m)
    (_hinv : IsMaxContactInvariant k p I m)
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (c₁ c₂ : EtaleChart p U n) (j : Fin n)
    (hcoord : ∀ i : Fin n, i ≠ j → c₁.coord i = c₂.coord i)
    (x : X) (hx : x ∈ U)
    (hmem₁ : c₁.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩)
    (hmem₂ : c₂.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩)
    (hg₁ : (X.presheaf.germ U x hx).hom (c₁.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    (hg₂ : (X.presheaf.germ U x hx).hom (c₂.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    (_hsupp : x ∈ (maxContactIdeal k p I m).support)
    [IsLocallyNoetherian (chartPullback c₁ c₂)]
    [IsLocallyNoetherian ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subscheme]
    (h : ChartsAgreeAt c₁ c₂ x hx)
    (z : ↥(((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subscheme))
    (hz : ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι.base z =
      chartPullbackPoint c₁ c₂ x hx h) :
    (((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subscheme).fromSpecStalk z ≫
        ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ≫
          chartPullbackFst c₁ c₂ =
      (((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subscheme).fromSpecStalk z ≫
        ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ≫
          chartPullbackSnd c₁ c₂ := by
  classical
  obtain ⟨V₀, hwV₀, hV₀⟩ :=
    AlgebraicGeometry.Scheme.exists_isAffineOpen_mem (chartPullbackPoint c₁ c₂ x hx h)
  have hwpre : chartPullbackPoint c₁ c₂ x hx h ∈ (chartPullbackFst c₁ c₂) ⁻¹ᵁ U := by
    show (chartPullbackFst c₁ c₂).base (chartPullbackPoint c₁ c₂ x hx h) ∈ U
    rw [chartPullbackFst_base_chartPullbackPoint c₁ c₂ x hx h]
    exact hx
  obtain ⟨t, htle, hwt⟩ := hV₀.exists_basicOpen_le
    (V := (V₀ ⊓ ((chartPullbackFst c₁ c₂) ⁻¹ᵁ U) : (chartPullback c₁ c₂).Opens))
    ⟨chartPullbackPoint c₁ c₂ x hx h, ⟨hwV₀, hwpre⟩⟩ hwV₀
  have hVaff : IsAffineOpen ((chartPullback c₁ c₂).basicOpen t) := hV₀.basicOpen t
  have hVle : ((chartPullback c₁ c₂).basicOpen t) ≤ (chartPullbackFst c₁ c₂) ⁻¹ᵁ U :=
    fun y hy => (htle hy).2
  refine fromSpecStalk_comp_eq_of_stalkMap_eq_consolidated174
    ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι
    (chartPullbackFst c₁ c₂) (chartPullbackSnd c₁ c₂) z (chartPullbackPoint c₁ c₂ x hx h) hz x
    (chartPullbackFst_base_chartPullbackPoint c₁ c₂ x hx h) (chartPullbackSnd_base_chartPullbackPoint c₁ c₂ x hx h)
    (chartPullbackFstStalkMap c₁ c₂ x hx h) (chartPullbackSndStalkMap c₁ c₂ x hx h)
    (chartPullbackFstStalkMap_eq c₁ c₂ x hx h) (chartPullbackSndStalkMap_eq c₁ c₂ x hx h) _ rfl ?_
  refine chartPullbackFstStalkMap_eq_snd_of_coord_eq_zero_consolidated174 k p hU c₁ c₂ j hcoord x hx hg₁ hg₂ h _ _ ?_ ?_
  · exact stalkMap_germ_eq_zero_of_mem_ideal_consolidated174 (chartPullbackFst c₁ c₂) (maxContactIdeal k p I m) z
      (chartPullbackPoint c₁ c₂ x hx h) hz x (chartPullbackFst_base_chartPullbackPoint c₁ c₂ x hx h) U hU hx
      ((chartPullback c₁ c₂).basicOpen t) hVaff hwt hVle (c₁.coord j) hmem₁
  · exact stalkMap_germ_eq_zero_of_mem_ideal_consolidated174 (chartPullbackFst c₁ c₂) (maxContactIdeal k p I m) z
      (chartPullbackPoint c₁ c₂ x hx h) hz x (chartPullbackFst_base_chartPullbackPoint c₁ c₂ x hx h) U hU hx
      ((chartPullback c₁ c₂).basicOpen t) hVaff hwt hVle (c₂.coord j) hmem₂


end

private theorem exists_preimage_eq_of_isClosedImmersion_consolidated174 {Y Z : Scheme.{u}} (f : Z ⟶ Y) [IsClosedImmersion f]
    (W : Z.Opens) : ∃ V : Y.Opens, f ⁻¹ᵁ V = W := by
  have hind := (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding f).toIsEmbedding.toIsInducing
  obtain ⟨t, ht, hteq⟩ := hind.isOpen_iff.mp W.2
  exact ⟨⟨t, ht⟩, TopologicalSpace.Opens.ext hteq⟩

private theorem ι_comp_eq_of_le_consolidated174 {Z Y : Scheme.{u}} {W₀ W' : Z.Opens} (hle : W₀ ≤ W')
    {f g : Z ⟶ Y} (hfg : W'.ι ≫ f = W'.ι ≫ g) : W₀.ι ≫ f = W₀.ι ≫ g := by
  rw [← Scheme.homOfLE_ι _ hle, Category.assoc, hfg, Category.assoc]

theorem exists_opens_chartPullback_eq_of_mem_maxContactIdeal
    (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m)
    (hinv : IsMaxContactInvariant k p I m)
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (c₁ c₂ : EtaleChart p U n) (j : Fin n)
    (hcoord : ∀ i : Fin n, i ≠ j → c₁.coord i = c₂.coord i)
    (x : X) (hx : x ∈ U)
    (hmem₁ : c₁.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩)
    (hmem₂ : c₂.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩)
    (hg₁ : (X.presheaf.germ U x hx).hom (c₁.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    (hg₂ : (X.presheaf.germ U x hx).hom (c₂.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    (hsupp : x ∈ (maxContactIdeal k p I m).support)
    [IsLocallyNoetherian (chartPullback c₁ c₂)]
    [IsLocallyNoetherian ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subscheme] :
    ∃ h : ChartsAgreeAt c₁ c₂ x hx,
      ∃ W : (chartPullback c₁ c₂).Opens, chartPullbackPoint c₁ c₂ x hx h ∈ W ∧
        (∀ y : ↥(chartPullback c₁ c₂), y ∈ W →
            stalkIdeal (I.comap (chartPullbackFst c₁ c₂)) y =
              stalkIdeal (I.comap (chartPullbackSnd c₁ c₂)) y) ∧
        restrictIdeal (I.comap (chartPullbackFst c₁ c₂)) W =
          restrictIdeal (I.comap (chartPullbackSnd c₁ c₂)) W ∧
        ((((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ⁻¹ᵁ W).ι ≫
              ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ≫
                chartPullbackFst c₁ c₂ =
            (((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ⁻¹ᵁ W).ι ≫
              ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ≫
                chartPullbackSnd c₁ c₂) ∧
        ((c₁.coordIdeal {j}).comap (pullback.fst c₁.map c₂.map) =
          (c₂.coordIdeal {j}).comap (pullback.snd c₁.map c₂.map)) ∧
        ∀ S : Finset (Fin n), j ∉ S → c₁.coordIdeal S = c₂.coordIdeal S := by
  classical
  have hagree : ChartsAgreeAt c₁ c₂ x hx :=
    chartsAgreeAt_of_coord_eq_of_germ_mem c₁ c₂ j x hx hcoord hg₁ hg₂
  have hst : stalkIdeal (I.comap (chartPullbackFst c₁ c₂)) (chartPullbackPoint c₁ c₂ x hx hagree) =
      stalkIdeal (I.comap (chartPullbackSnd c₁ c₂)) (chartPullbackPoint c₁ c₂ x hx hagree) :=
    stalkIdeal_comap_chartPullbackPoint_eq k p I hm hinv hU c₁ c₂ j hcoord x hx hmem₁ hmem₂ hg₁ hg₂
      hagree
  obtain ⟨W₁, hW₁mem, hW₁⟩ :=
    exists_opens_stalkIdeal_eq (I.comap (chartPullbackFst c₁ c₂)) (I.comap (chartPullbackSnd c₁ c₂))
      (chartPullbackPoint c₁ c₂ x hx hagree) hst
  have hsupp' : chartPullbackPoint c₁ c₂ x hx hagree ∈
      ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).support := by
    have hz : (chartPullbackFst c₁ c₂).base (chartPullbackPoint c₁ c₂ x hx hagree) ∈
        (maxContactIdeal k p I m).support := by
      rw [chartPullbackFst_base_chartPullbackPoint c₁ c₂ x hx hagree]
      exact hsupp
    rw [Scheme.IdealSheafData.support_comap]
    exact hz
  have hrange : chartPullbackPoint c₁ c₂ x hx hagree ∈
      Set.range (((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι.base) := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hsupp'
  obtain ⟨z, hz⟩ := hrange
  have hmor := fromSpecStalk_comp_subschemeι_chartPullback_eq k p I hm hinv hU c₁ c₂ j hcoord x hx
    hmem₁ hmem₂ hg₁ hg₂ hsupp hagree z hz
  obtain ⟨W', hzW', hW'⟩ :=
    AlgebraicGeometry.spread_out_unique_of_isGermInjective'
      (((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ≫ chartPullbackFst c₁ c₂)
      (((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ≫ chartPullbackSnd c₁ c₂)
      hmor
  obtain ⟨V, hV⟩ :=
    _root_.FunctorialResolution.EmbeddedResolution.exists_preimage_eq_of_isClosedImmersion_consolidated174 ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι W'
  have hptV : chartPullbackPoint c₁ c₂ x hx hagree ∈ V := by
    have h1 : z ∈ ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ⁻¹ᵁ V := by
      rw [hV]
      exact hzW'
    have h2 : ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι.base z ∈ V := h1
    rw [hz] at h2
    exact h2
  have hstalk : ∀ y : ↥(chartPullback c₁ c₂), y ∈ W₁ ⊓ V →
      stalkIdeal (I.comap (chartPullbackFst c₁ c₂)) y =
        stalkIdeal (I.comap (chartPullbackSnd c₁ c₂)) y := fun y hy => hW₁ y hy.1
  have hle : (((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ⁻¹ᵁ (W₁ ⊓ V))
      ≤ W' := by
    rw [← hV]
    intro w hw
    exact hw.2
  exact ⟨hagree, W₁ ⊓ V, ⟨hW₁mem, hptV⟩, hstalk,
    restrictIdeal_eq_of_stalkIdeal_eq _ _ (W₁ ⊓ V) hstalk,
    ι_comp_eq_of_le_consolidated174 hle hW',
    chartPullback_comap_coordIdeal_eq c₁ c₂ {j},
    fun S hS => coordIdeal_eq_of_coord_eq hU c₁ c₂ S (by
      intro i hi
      refine hcoord i ?_
      rintro rfl
      exact hS hi)⟩

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactCoordinate
section

open AlgebraicGeometry CategoryTheory TopologicalSpace

open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Scheme.{u}}

private theorem presheaf_map_op_eq_map_op_consolidated186 {A B : X.Opens} (f g : B ⟶ A) :
    X.presheaf.map f.op = X.presheaf.map g.op := by
  rw [Subsingleton.elim f g]

private theorem topIso_hom_comp_inv_consolidated186 (U : X.Opens) :
    (U.topIso.hom.hom).comp (U.topIso.inv.hom) = RingHom.id _ := by
  rw [← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id]

private theorem topIso_inv_comp_hom_consolidated186 (U : X.Opens) :
    (U.topIso.inv.hom).comp (U.topIso.hom.hom) = RingHom.id _ := by
  rw [← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id]


end

section
variable {X : Scheme.{u}} (U : X.Opens) (h : (⊤ : (↑U : Scheme.{u}).Opens) ≤ U.ι ⁻¹ᵁ U)

private theorem appLE_opensι_top_eq_topIso_inv_consolidated186 :
    Scheme.Hom.appLE U.ι U ⊤ h = U.topIso.inv := by
  rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  exact presheaf_map_op_eq_map_op_consolidated186 _ _

private theorem topIso_hom_comp_appLE_ι_consolidated186 :
    (U.topIso.hom.hom).comp ((Scheme.Hom.appLE U.ι U ⊤ h).hom) = RingHom.id _ := by
  rw [appLE_opensι_top_eq_topIso_inv_consolidated186]
  exact topIso_hom_comp_inv_consolidated186 U


end

private theorem basis_det_D_update_eq_coeff_consolidated186 {k : Type*} {S : Type*} [CommRing k] [CommRing S] [Algebra k S]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι S (KaehlerDifferential k S))
    (y : ι → S) (hb : ∀ i, b i = KaehlerDifferential.D k S (y i))
    (i0 : ι) (z : S) (a : ι → S)
    (hz : KaehlerDifferential.D k S z = ∑ i, a i • b i) :
    b.det (fun i => KaehlerDifferential.D k S (Function.update y i0 z i)) = a i0 := by
  have hmat : b.toMatrix (fun i => KaehlerDifferential.D k S (Function.update y i0 z i))
      = Matrix.updateCol (1 : Matrix ι ι S) i0 a := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Matrix.updateCol_apply]
    by_cases hj : j = i0
    · subst hj
      rw [if_pos rfl, Function.update_self, hz]
      simp [Finsupp.single_apply]
    · rw [if_neg hj, Function.update_of_ne hj, ← hb, Matrix.one_apply]
      simp [Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
  rw [Module.Basis.det_apply, hmat, ← Matrix.cramer_apply]
  simp [Matrix.cramer_one]

section

private theorem one_tmul_ne_zero_of_notMem_maximalIdeal_sq_consolidated186 {A : Type*} [CommRing A] [IsLocalRing A]
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (ha2 : a ∉ IsLocalRing.maximalIdeal A ^ 2) :
    (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      (⟨a, ha⟩ : ↥(IsLocalRing.maximalIdeal A)) ≠ 0 := by
  intro h
  apply ha2
  have hker : IsLocalRing.maximalIdeal A ≤ LinearMap.ker
      (LinearMap.toSpanSingleton A
        (↥(IsLocalRing.maximalIdeal A) →ₗ[A] (IsLocalRing.maximalIdeal A).Cotangent)
        (Ideal.toCotangent (IsLocalRing.maximalIdeal A))) := by
    intro b hb
    rw [LinearMap.mem_ker]
    ext y
    have hy : ((b • y : ↥(IsLocalRing.maximalIdeal A)) : A) ∈
        IsLocalRing.maximalIdeal A ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul hb y.2
    have h0 : (Ideal.toCotangent (IsLocalRing.maximalIdeal A)) (b • y) = 0 :=
      (Ideal.toCotangent_eq_zero (IsLocalRing.maximalIdeal A) (b • y)).mpr hy
    rw [map_smul] at h0
    show b • (Ideal.toCotangent (IsLocalRing.maximalIdeal A)) y = 0
    exact h0
  have h' : (1 : A ⧸ IsLocalRing.maximalIdeal A) ⊗ₜ[A]
      (⟨a, ha⟩ : ↥(IsLocalRing.maximalIdeal A)) = 0 := h
  have key := congrArg (TensorProduct.lift
      (Submodule.liftQ (IsLocalRing.maximalIdeal A) _ hker)) h'
  rw [TensorProduct.lift.tmul, map_zero] at key
  have h1 : (Submodule.liftQ (IsLocalRing.maximalIdeal A)
      (LinearMap.toSpanSingleton A
        (↥(IsLocalRing.maximalIdeal A) →ₗ[A] (IsLocalRing.maximalIdeal A).Cotangent)
        (Ideal.toCotangent (IsLocalRing.maximalIdeal A))) hker)
      (1 : A ⧸ IsLocalRing.maximalIdeal A)
      = Ideal.toCotangent (IsLocalRing.maximalIdeal A) := by
    have e1 : (1 : A ⧸ IsLocalRing.maximalIdeal A) = Submodule.Quotient.mk (1 : A) := rfl
    rw [e1, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
  rw [h1] at key
  exact (Ideal.toCotangent_eq_zero (IsLocalRing.maximalIdeal A) ⟨a, ha⟩).mp key

theorem linearIndependent_one_tmul_D_of_notMem_maximalIdeal_sq
    (k : Type*) (A : Type*) [CommRing k] [CommRing A] [Algebra k A] [IsLocalRing A]
    [IsNoetherianRing A] [Algebra.FormallySmooth k A]
    [Module.Free A (KaehlerDifferential k A)] [Module.Finite A (KaehlerDifferential k A)]
    [Algebra k (IsLocalRing.ResidueField A)] [IsScalarTower k A (IsLocalRing.ResidueField A)]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)]
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (ha2 : a ∉ IsLocalRing.maximalIdeal A ^ 2) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun _ : Fin 1 =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A a) := by
  have key : LinearIndependent (IsLocalRing.ResidueField A)
      (fun _ : Fin 1 => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        (⟨a, ha⟩ : ↥(IsLocalRing.maximalIdeal A))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [Fin.sum_univ_one] at hg
    rcases smul_eq_zero.mp hg with hzero | hzero
    · rw [Subsingleton.elim i 0]
      exact hzero
    · exact absurd hzero (one_tmul_ne_zero_of_notMem_maximalIdeal_sq_consolidated186 a ha ha2)
  exact linearIndependent_tensor_D_of_maximalIdeal k A
    (fun _ : Fin 1 => (⟨a, ha⟩ : ↥(IsLocalRing.maximalIdeal A))) key

end

section

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))

theorem coordIdeal_singleton_le_restrictIdeal_iff {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (c : EtaleChart p U n) (j : Fin n) (J : X.IdealSheafData) :
    c.coordIdeal {j} ≤ restrictIdeal J U ↔ c.coord j ∈ J.ideal ⟨U, hU⟩ := by
  have : IsAffine (↑U : Scheme.{u}) := hU
  have htop : IsAffineOpen (⊤ : (↑U : Scheme.{u}).Opens) := isAffineOpen_top _
  obtain ⟨t, htdef⟩ : ∃ t : Γ((↑U : Scheme.{u}), ⊤), t = (c.map.appTop).hom
      (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) := ⟨_, rfl⟩
  have hcoord : c.coord j = U.topIso.hom.hom t := by rw [htdef]; rfl
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_eq_ofIdealTop_span_coord, restrictIdeal_eq_comap_ι,
    Scheme.IdealSheafData.comap_ofIdealTop]
  simp only [Ideal.map_span, Set.image_singleton, Finset.coe_singleton]
  rw [← htdef]
  constructor
  · intro h
    have h2 := h ⟨⊤, htop⟩
    rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE J U.ι ⟨U, hU⟩ ⟨⊤, htop⟩ (by simp),
      Scheme.IdealSheafData.ofIdealTop_ideal_top] at h2
    have ht := h2 (Ideal.mem_span_singleton_self t)
    have hmem2 := Ideal.mem_map_of_mem (U.topIso.hom.hom) ht
    rw [Ideal.map_map, topIso_hom_comp_appLE_ι_consolidated186 U (by simp), Ideal.map_id] at hmem2
    rw [hcoord]
    exact hmem2
  · intro h V
    rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE J U.ι ⟨U, hU⟩ V (by simp),
      Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton,
      Ideal.span_le, Set.singleton_subset_iff]
    have hmorph : Scheme.Hom.appLE U.ι U (V : (↑U : Scheme.{u}).Opens) (by simp)
        = U.topIso.inv ≫ (↑U : Scheme.{u}).presheaf.map
          (homOfLE (le_top : (V : (↑U : Scheme.{u}).Opens) ≤ ⊤)).op := by
      rw [← appLE_opensι_top_eq_topIso_inv_consolidated186 U (by simp), Scheme.Hom.appLE_map]
    rw [hmorph, CommRingCat.hom_comp, ← Ideal.map_map]
    refine Ideal.mem_map_of_mem _ ?_
    have e2 : U.topIso.inv.hom (c.coord j) = t := by
      rw [hcoord]
      exact DFunLike.congr_fun (topIso_inv_comp_hom_consolidated186 U) t
    rw [← e2]
    exact Ideal.mem_map_of_mem _ h

variable [LocallyOfFiniteType p]

def IsMaxContactCoord (I : X.IdealSheafData) (m : ℕ) {U : X.Opens} {n : ℕ}
    (c : EtaleChart p U n) (j : Fin n) : Prop :=
  c.coordIdeal {j} ≤ restrictIdeal (maxContactIdeal k p I m) U

section
variable (I : X.IdealSheafData)

theorem isMaxContactCoord_iff (m : ℕ) {U : X.Opens} {n : ℕ}
    (c : EtaleChart p U n) (j : Fin n) :
    IsMaxContactCoord k p I m c j ↔
      c.coordIdeal {j} ≤ restrictIdeal (maxContactIdeal k p I m) U :=
  Iff.rfl

theorem isMaxContactCoord_one_iff {U : X.Opens} {n : ℕ}
    (c : EtaleChart p U n) (j : Fin n) :
    IsMaxContactCoord k p I 1 c j ↔ c.coordIdeal {j} ≤ restrictIdeal I U := by
  rw [isMaxContactCoord_iff, maxContactIdeal_one k p I]

theorem isMaxContactCoord_iff_coord_mem (m : ℕ) {U : X.Opens}
    (hU : IsAffineOpen U) {n : ℕ} (c : EtaleChart p U n) (j : Fin n) :
    IsMaxContactCoord k p I m c j ↔ c.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩ :=
  coordIdeal_singleton_le_restrictIdeal_iff k p hU c j (maxContactIdeal k p I m)


end

variable [CharZero k] [Smooth p]

section
variable (I : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m)
include hm

theorem mem_support_maxContactIdeal_of_mem_orderAtLeastLocus {x : X} (hx : x ∈ orderAtLeastLocus I m) :
    x ∈ (maxContactIdeal k p I m).support := by
  have h := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm
  have hx' : x ∈ ((derivIdealSheafIterate k p (m - 1) I).support : Set X) := by
    rw [h]; exact hx
  exact hx'

theorem orderAt_maxContactIdeal_eq_one {x : X}
    (hx : orderAt I x = (m : ℕ∞)) :
    orderAt (maxContactIdeal k p I m) x = (1 : ℕ∞) := by
  have h := orderAt_derivIdealSheafIterate_eq_sub k p I x hx (Nat.sub_le m 1)
  rw [maxContactIdeal_eq_derivIdealSheafIterate, h, show m - (m - 1) = 1 from by omega, Nat.cast_one]

theorem stalkIdeal_maxContactIdeal_le_maximalIdeal {x : X} (hx : orderAt I x = (m : ℕ∞)) :
    stalkIdeal (maxContactIdeal k p I m) x ≤
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) := by
  have h1 : orderAt (maxContactIdeal k p I m) x = (1 : ℕ∞) :=
    orderAt_maxContactIdeal_eq_one k p I hm hx
  have h2 := (le_orderAt_iff (maxContactIdeal k p I m) x 1).mp (by rw [Nat.cast_one, h1])
  rw [pow_one] at h2
  exact h2

theorem exists_section_maxContactIdeal_notMem_maximalIdeal_sq {x : X} (hx : orderAt I x = (m : ℕ∞)) {U : X.Opens} (hU : IsAffineOpen U)
    (hxU : x ∈ U) :
    ∃ s ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩,
      (X.presheaf.germ U x hxU).hom s ∈ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) ∧
        (X.presheaf.germ U x hxU).hom s ∉
          IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) ^ 2 := by
  have h1 : orderAt (maxContactIdeal k p I m) x = (1 : ℕ∞) :=
    orderAt_maxContactIdeal_eq_one k p I hm hx
  have hle : stalkIdeal (maxContactIdeal k p I m) x ≤
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) :=
    stalkIdeal_maxContactIdeal_le_maximalIdeal k p I hm hx
  have hmap : stalkIdeal (maxContactIdeal k p I m) x =
      Ideal.map (X.presheaf.germ U x hxU).hom ((maxContactIdeal k p I m).ideal ⟨U, hU⟩) :=
    stalkIdeal_eq_map_germ _ x ⟨U, hU⟩ hxU
  by_contra hno
  push Not at hno
  have h2 : stalkIdeal (maxContactIdeal k p I m) x ≤
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) ^ 2 := by
    rw [hmap, Ideal.map_le_iff_le_comap]
    intro s hs
    simp only [Ideal.mem_comap]
    exact hno s hs (hle (germ_mem_stalkIdeal _ x ⟨U, hU⟩ hxU hs))
  have h3 := (le_orderAt_iff (maxContactIdeal k p I m) x 2).mpr h2
  rw [h1] at h3
  simp at h3

theorem exists_isMaxContactCoord (x : X)
    (hx : orderAt I x = (m : ℕ∞)) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (hxU : x ∈ U) (n : ℕ) (c : EtaleChart p U n)
      (j : Fin n),
      IsMaxContactCoord k p I m c j ∧
        (X.presheaf.germ U x hxU).hom (c.coord j) ∈
          IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) := by
  classical
  obtain ⟨U, n, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p x
  obtain ⟨s, hs, hs1, hs2⟩ :=
    exists_section_maxContactIdeal_notMem_maximalIdeal_sq k p I hm hx hU hxU
  let _instSections : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let _instChart : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := c.algebra
  have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := c.isScalarTower
  have : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) :=
    c.algebra_formallyEtale hU
  let _instStalk : Algebra k ↑(X.presheaf.stalk x) := stalkAlgebra k p x
  let _instGerm : Algebra Γ(X, U) ↑(X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  have : IsScalarTower k Γ(X, U) ↑(X.presheaf.stalk x) :=
    isScalarTower_stalk k p U x hxU (algebraMap_sectionsAlgebra k p U)
      (algebraMap_stalkAlgebra k p x) rfl
  have : IsNoetherianRing ↑(X.presheaf.stalk x) := isNoetherianRing_stalk k p x
  have : Algebra.FormallySmooth k ↑(X.presheaf.stalk x) := formallySmooth_stalk k p x
  have : Module.Finite ↑(X.presheaf.stalk x) (KaehlerDifferential k ↑(X.presheaf.stalk x)) :=
    finite_kaehlerDifferential_stalk k p x
  have : Module.Free ↑(X.presheaf.stalk x) (KaehlerDifferential k ↑(X.presheaf.stalk x)) :=
    free_kaehlerDifferential_stalk k p x
  let _instResidue : Algebra k (IsLocalRing.ResidueField ↑(X.presheaf.stalk x)) :=
    ((IsLocalRing.residue ↑(X.presheaf.stalk x)).comp (stalkAlgebraMap k p x)).toAlgebra
  have : IsScalarTower k ↑(X.presheaf.stalk x)
      (IsLocalRing.ResidueField ↑(X.presheaf.stalk x)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FormallySmooth k (IsLocalRing.ResidueField ↑(X.presheaf.stalk x)) :=
    formallySmooth_residueField k p x rfl
  have hli := linearIndependent_one_tmul_D_of_notMem_maximalIdeal_sq k ↑(X.presheaf.stalk x)
    ((X.presheaf.germ U x hxU).hom s) hs1 hs2
  have hne : (1 : IsLocalRing.ResidueField ↑(X.presheaf.stalk x)) ⊗ₜ[↑(X.presheaf.stalk x)]
      KaehlerDifferential.D k ↑(X.presheaf.stalk x)
        ((X.presheaf.germ U x hxU).hom s) ≠ 0 := hli.ne_zero 0
  obtain ⟨a, ha⟩ : ∃ a : ULift.{u} (Fin n) → Γ(X, U), ∀ i,
      a i = (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U)).repr
        (KaehlerDifferential.D k Γ(X, U) s) i := ⟨_, fun i => rfl⟩
  have hrepr : KaehlerDifferential.D k Γ(X, U) s
      = ∑ i, a i • (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U) i) := by
    have h := (Module.Basis.sum_repr
      (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U))
      (KaehlerDifferential.D k Γ(X, U) s)).symm
    simpa only [← ha] using h
  have hex : ∃ i : ULift.{u} (Fin n), IsUnit ((X.presheaf.germ U x hxU).hom (a i)) := by
    by_contra hcon
    push Not at hcon
    apply hne
    show (1 : IsLocalRing.ResidueField ↑(X.presheaf.stalk x)) ⊗ₜ[↑(X.presheaf.stalk x)]
      KaehlerDifferential.D k ↑(X.presheaf.stalk x)
        (algebraMap Γ(X, U) ↑(X.presheaf.stalk x) s) = 0
    have h0 : KaehlerDifferential.D k ↑(X.presheaf.stalk x)
        (algebraMap Γ(X, U) ↑(X.presheaf.stalk x) s)
        = ∑ i, (KaehlerDifferential.map k k Γ(X, U) ↑(X.presheaf.stalk x))
            (a i • (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U) i)) := by
      rw [← KaehlerDifferential.map_D k k Γ(X, U) ↑(X.presheaf.stalk x) s, hrepr, map_sum]
    rw [h0, TensorProduct.tmul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : (KaehlerDifferential.map k k Γ(X, U) ↑(X.presheaf.stalk x))
        (a i • (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U) i))
        = ((X.presheaf.germ U x hxU).hom (a i)) •
          (KaehlerDifferential.map k k Γ(X, U) ↑(X.presheaf.stalk x))
            (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U) i) := by
      rw [map_smul]
      exact (algebraMap_smul (↑(X.presheaf.stalk x)) (a i) _).symm
    rw [h1, ← TensorProduct.smul_tmul]
    have h2 : ((X.presheaf.germ U x hxU).hom (a i)) •
        (1 : IsLocalRing.ResidueField ↑(X.presheaf.stalk x)) = 0 := by
      rw [Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq,
        IsLocalRing.residue_eq_zero_iff]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (hcon i))
    rw [h2, TensorProduct.zero_tmul]
  obtain ⟨i0, hunit⟩ := hex
  have hV : IsAffineOpen (X.basicOpen (a i0)) := hU.basicOpen (a i0)
  have hxV : x ∈ X.basicOpen (a i0) :=
    (X.toLocallyRingedSpace.toRingedSpace.mem_basicOpen (a i0) x hxU).mpr hunit
  let _instBasicOpen : Algebra k Γ(X, X.basicOpen (a i0)) :=
    sectionsAlgebra k p (X.basicOpen (a i0))
  let _instRestrict : Algebra Γ(X, U) Γ(X, X.basicOpen (a i0)) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le (a i0))).op).hom.toAlgebra
  have : IsScalarTower k Γ(X, U) Γ(X, X.basicOpen (a i0)) :=
    isScalarTower_sections k p U (a i0) (algebraMap_sectionsAlgebra k p U)
      (algebraMap_sectionsAlgebra k p (X.basicOpen (a i0))) rfl
  have : IsLocalization.Away (a i0) Γ(X, X.basicOpen (a i0)) :=
    hU.isLocalization_basicOpen (a i0)
  have : Algebra.FormallyEtale Γ(X, U) Γ(X, X.basicOpen (a i0)) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (a i0))
  have : Algebra.FormallySmooth k Γ(X, X.basicOpen (a i0)) :=
    formallySmooth_sections k p (X.basicOpen (a i0)) hV
      (algebraMap_sectionsAlgebra k p (X.basicOpen (a i0)))
  obtain ⟨e, he⟩ : ∃ e : Module.Basis (ULift.{u} (Fin n)) Γ(X, X.basicOpen (a i0))
      (KaehlerDifferential k Γ(X, X.basicOpen (a i0))),
      e = JacobianCriterion.inducedBasis k (ULift.{u} (Fin n)) Γ(X, U)
        Γ(X, X.basicOpen (a i0))
        (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U)) := ⟨_, rfl⟩
  have he_apply : ∀ i, e i = (KaehlerDifferential.map k k Γ(X, U) Γ(X, X.basicOpen (a i0)))
      (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U) i) := by
    intro i
    rw [he]
    exact JacobianCriterion.inducedBasis_apply k (ULift.{u} (Fin n)) Γ(X, U)
      Γ(X, X.basicOpen (a i0))
      (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U)) i
  have hbT : ∀ i, e i = KaehlerDifferential.D k Γ(X, X.basicOpen (a i0))
      (algebraMap Γ(X, U) Γ(X, X.basicOpen (a i0))
        (EtaleCoordinates.coord k (ULift.{u} (Fin n)) Γ(X, U) i)) := by
    intro i
    rw [he]
    exact JacobianCriterion.inducedBasis_apply_D k (ULift.{u} (Fin n)) Γ(X, U)
      Γ(X, X.basicOpen (a i0))
      (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, U))
      (fun i => EtaleCoordinates.coord k (ULift.{u} (Fin n)) Γ(X, U) i)
      (fun i => EtaleCoordinates.basisKaehler_apply k (ULift.{u} (Fin n)) Γ(X, U) i) i
  have hz : KaehlerDifferential.D k Γ(X, X.basicOpen (a i0))
      (algebraMap Γ(X, U) Γ(X, X.basicOpen (a i0)) s)
      = ∑ i, (algebraMap Γ(X, U) Γ(X, X.basicOpen (a i0)) (a i)) • e i := by
    rw [← KaehlerDifferential.map_D k k Γ(X, U) Γ(X, X.basicOpen (a i0)) s, hrepr, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, he_apply i, algebraMap_smul]
  obtain ⟨w, hw⟩ : ∃ w : ULift.{u} (Fin n) → Γ(X, X.basicOpen (a i0)),
      w = Function.update (fun i => algebraMap Γ(X, U) Γ(X, X.basicOpen (a i0))
        (EtaleCoordinates.coord k (ULift.{u} (Fin n)) Γ(X, U) i)) i0
        (algebraMap Γ(X, U) Γ(X, X.basicOpen (a i0)) s) := ⟨_, rfl⟩
  have hdet0 : (e.det fun i => KaehlerDifferential.D k Γ(X, X.basicOpen (a i0)) (w i))
      = algebraMap Γ(X, U) Γ(X, X.basicOpen (a i0)) (a i0) := by
    rw [hw]
    exact basis_det_D_update_eq_coeff_consolidated186 e _ hbT i0 _
      (fun i => algebraMap Γ(X, U) Γ(X, X.basicOpen (a i0)) (a i)) hz
  have hdet : IsUnit (e.det fun i => KaehlerDifferential.D k Γ(X, X.basicOpen (a i0)) (w i)) := by
    rw [hdet0]
    exact IsLocalization.map_units Γ(X, X.basicOpen (a i0))
      (⟨a i0, Submonoid.mem_powers _⟩ : Submonoid.powers (a i0))
  obtain ⟨f, hf⟩ : ∃ f : MvPolynomial (ULift.{u} (Fin n)) k →+* Γ(X, X.basicOpen (a i0)),
      f = (MvPolynomial.aeval w :
        MvPolynomial (ULift.{u} (Fin n)) k →ₐ[k] Γ(X, X.basicOpen (a i0))).toRingHom := ⟨_, rfl⟩
  have hC : ∀ b : k, f (MvPolynomial.C b) = sectionsAlgebraMap k p (X.basicOpen (a i0)) b := by
    intro b
    rw [hf]
    show MvPolynomial.aeval w (MvPolynomial.C b) = _
    rw [MvPolynomial.aeval_C, algebraMap_sectionsAlgebra]
  have hXc : ∀ i : ULift.{u} (Fin n), f (MvPolynomial.X i) = w i := by
    intro i
    rw [hf]
    show MvPolynomial.aeval w (MvPolynomial.X i) = _
    rw [MvPolynomial.aeval_X]
  have hfet : f.Etale := by
    subst hf
    let inst : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, X.basicOpen (a i0)) :=
      (MvPolynomial.aeval w :
        MvPolynomial (ULift.{u} (Fin n)) k →ₐ[k] Γ(X, X.basicOpen (a i0))).toRingHom.toAlgebra
    have : @Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k)
        Γ(X, X.basicOpen (a i0)) _ _ inst :=
      EtaleCoordinates.formallyEtale_aeval_of_isUnit_det e w hdet
    have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k)
        Γ(X, X.basicOpen (a i0)) :=
      IsScalarTower.of_algebraMap_eq fun r => (hC r).symm
    have : Algebra.FiniteType k Γ(X, X.basicOpen (a i0)) :=
      finiteType_sections k p ⟨X.basicOpen (a i0), hV⟩
        (algebraMap_sectionsAlgebra k p (X.basicOpen (a i0)))
    have : Algebra.FiniteType (MvPolynomial (ULift.{u} (Fin n)) k)
        Γ(X, X.basicOpen (a i0)) :=
      Algebra.FiniteType.of_restrictScalars_finiteType k
        (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, X.basicOpen (a i0))
    have : Algebra.FinitePresentation (MvPolynomial (ULift.{u} (Fin n)) k)
        Γ(X, X.basicOpen (a i0)) := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact (⟨inferInstance, inferInstance⟩ :
      Algebra.Etale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, X.basicOpen (a i0)))
  obtain ⟨c', hc'⟩ := exists_etaleChart_coord_eq p hV w f hC hXc hfet
  have hwi : w (ULift.up i0.down) = algebraMap Γ(X, U) Γ(X, X.basicOpen (a i0)) s := by
    rw [ULift.up_down, hw, Function.update_self]
  refine ⟨X.basicOpen (a i0), hV, hxV, n, c', i0.down, ?_, ?_⟩
  · rw [isMaxContactCoord_iff_coord_mem k p I m hV c' i0.down, hc' i0.down, hwi]
    have h2 : Ideal.map ((X.presheaf.map (homOfLE (X.basicOpen_le (a i0))).op).hom)
        ((maxContactIdeal k p I m).ideal ⟨U, hU⟩)
        = (maxContactIdeal k p I m).ideal ⟨X.basicOpen (a i0), hV⟩ :=
      Scheme.IdealSheafData.map_ideal_basicOpen _ ⟨U, hU⟩ (a i0)
    rw [← h2]
    exact Ideal.mem_map_of_mem _ hs
  · rw [hc' i0.down, hwi]
    have h3 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (X.presheaf.germ_res (homOfLE (X.basicOpen_le (a i0))) x hxV)) s
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h3
    have h4 : (X.presheaf.germ (X.basicOpen (a i0)) x hxV).hom
        (algebraMap Γ(X, U) Γ(X, X.basicOpen (a i0)) s)
        = (X.presheaf.germ U x hxU).hom s := h3
    rw [h4]
    exact hs1


end

end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

section

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType p]

def IsMaxContactHypersurface (A : X.IdealSheafData) (m : ℕ) (H : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ((Disjoint (orderAtLeastLocus A m) (U : Set ↥X) ∧ restrictIdeal H U = ⊤) ∨
      (∃ (n : ℕ) (c : EtaleChart p U n) (j : Fin n),
        restrictIdeal H U = c.coordIdeal {j} ∧ IsMaxContactCoord k p A m c j))

theorem isMaxContactHypersurface_iff (A : X.IdealSheafData) (m : ℕ) (H : X.IdealSheafData) :
    IsMaxContactHypersurface k p A m H ↔
      ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
        ((Disjoint (orderAtLeastLocus A m) (U : Set ↥X) ∧ restrictIdeal H U = ⊤) ∨
          (∃ (n : ℕ) (c : EtaleChart p U n) (j : Fin n),
            restrictIdeal H U = c.coordIdeal {j} ∧ IsMaxContactCoord k p A m c j)) :=
  Iff.rfl

end

section

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
  {p : X ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType p] [Smooth p]

theorem IsMaxContactHypersurface.orderAtLeastLocus_subset_support {A : X.IdealSheafData} {m : ℕ}
    {H : X.IdealSheafData} (h : IsMaxContactHypersurface k p A m H) (hm : 1 ≤ m) :
    orderAtLeastLocus A m ⊆ (H.support : Set ↥X) := by
  intro x hx
  obtain ⟨U, hU, hxU, hcase⟩ := h x
  rcases hcase with ⟨hdisj, -⟩ | ⟨n, c, j, hH, hmc⟩
  · exact absurd hxU (Set.disjoint_left.mp hdisj hx)
  · have hmem : c.coord j ∈ (maxContactIdeal k p A m).ideal ⟨U, hU⟩ :=
      (isMaxContactCoord_iff_coord_mem k p A m hU c j).mp hmc
    have hHideal :
        H.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (({j} : Finset (Fin n)) : Set (Fin n))) :=
      c.ideal_eq_span_coord hU H {j} hH
    have hle : H.ideal ⟨U, hU⟩ ≤ (maxContactIdeal k p A m).ideal ⟨U, hU⟩ := by
      rw [hHideal, Finset.coe_singleton, Set.image_singleton, Ideal.span_le,
        Set.singleton_subset_iff]
      exact hmem
    have hst : stalkIdeal H x ≤ stalkIdeal (maxContactIdeal k p A m) x := by
      rw [stalkIdeal_eq_map_germ H x ⟨U, hU⟩ hxU,
        stalkIdeal_eq_map_germ (maxContactIdeal k p A m) x ⟨U, hU⟩ hxU]
      exact Ideal.map_mono hle
    have hx' : x ∈ (maxContactIdeal k p A m).support :=
      mem_support_maxContactIdeal_of_mem_orderAtLeastLocus k p A hm hx
    rw [mem_support_iff_stalkIdeal_le_maximalIdeal] at hx'
    have hfin : x ∈ H.support := by
      rw [mem_support_iff_stalkIdeal_le_maximalIdeal]
      exact hst.trans hx'
    exact hfin

end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.AffineSpaceCoordinateBlowup
section
open CategoryTheory AlgebraicGeometry

section
namespace FunctorialResolution.EmbeddedResolution


def uliftFinset (m : ℕ) (S : Finset (Fin m)) : Finset (ULift.{u} (Fin m)) :=
  S.map ⟨fun j => (ULift.up j : ULift.{u} (Fin m)), fun _ _ h => congrArg ULift.down h⟩

section
variable {m : ℕ}

@[simp] theorem mem_uliftFinset (S : Finset (Fin m)) (x : ULift.{u} (Fin m)) :
    x ∈ uliftFinset.{u} m S ↔ x.down ∈ S := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp h
    exact ha
  · intro h
    exact Finset.mem_map.mpr ⟨x.down, h, rfl⟩

theorem up_mem_uliftFinset {S : Finset (Fin m)} {j : Fin m} (hj : j ∈ S) :
    (ULift.up j : ULift.{u} (Fin m)) ∈ uliftFinset.{u} m S :=
  (mem_uliftFinset S _).mpr hj

theorem down_mem_of_mem_uliftFinset {S : Finset (Fin m)} {x : ULift.{u} (Fin m)}
    (hx : x ∈ uliftFinset.{u} m S) : x.down ∈ S :=
  (mem_uliftFinset S x).mp hx


end

abbrev finCoordIdeal (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    Ideal (MvPolynomial (ULift.{u} (Fin m)) k) :=
  coordIdeal k (uliftFinset.{u} m S)

def affineSpaceSpecIso (k : Type u) [Field k] (m : ℕ) :
    affineSpaceFin k m ≅ Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k)) :=
  AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)

private theorem appTop_comp_apply_eq_appTop_appTop_consolidated207 {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Γ(Z, ⊤)) : (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := rfl

private theorem appTop_specMap_ΓSpecIso_inv_apply_consolidated207 {R S : CommRingCat.{u}} (f : R ⟶ S) (x : R) :
    (Spec.map f).appTop.hom ((Scheme.ΓSpecIso R).inv.hom x)
      = (Scheme.ΓSpecIso S).inv.hom (f.hom x) := by
  have h : (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop = f ≫ (Scheme.ΓSpecIso S).inv := by
    rw [← cancel_mono (Scheme.ΓSpecIso S).hom]
    simp [Scheme.ΓSpecIso_naturality]
  have h2 : ((Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop).hom x
      = (f ≫ (Scheme.ΓSpecIso S).inv).hom x := by rw [h]
  exact h2

section
variable (k : Type u) [Field k] (m : ℕ)

private theorem affineSpaceSpecIso_inv_appTop_coord_consolidated207 (j : ULift.{u} (Fin m)) :
    (affineSpaceSpecIso k m).inv.appTop.hom (AffineSpace.coord (Spec (CommRingCat.of k)) j)
      = (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv.hom
          (MvPolynomial.X j) := by
  apply AlgebraicGeometry.AffineSpace.SpecIso_inv_appTop_coord

private theorem affineSpaceSpecIso_hom_appTop_X_consolidated207 (j : ULift.{u} (Fin m)) :
    (affineSpaceSpecIso k m).hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv.hom
          (MvPolynomial.X j))
      = AffineSpace.coord (Spec (CommRingCat.of k)) j := by
  rw [← affineSpaceSpecIso_inv_appTop_coord_consolidated207 k m j, ← appTop_comp_apply_eq_appTop_appTop_consolidated207, Iso.hom_inv_id]
  simp

private theorem affineSpaceSpecIso_inv_comp_affineSpaceFinToSpec_consolidated207 :
    (affineSpaceSpecIso k m).inv ≫ affineSpaceFinToSpec k m
      = Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k)) := by
  simp [affineSpaceSpecIso, affineSpaceFinToSpec]


end

abbrev affineSpaceCoordBlowup (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) : Scheme.{u} :=
  Blowup.affineBlowup (finCoordIdeal k m S)

def affineSpaceCoordBlowupMap (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    affineSpaceCoordBlowup k m S ⟶ affineSpaceFin k m :=
  Blowup.AffineBlowup.toSpec (finCoordIdeal k m S) ≫ (affineSpaceSpecIso k m).inv

section
variable (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))

private theorem comap_specIdealSheaf_finCoordIdeal_consolidated207 :
    (Blowup.specIdealSheaf (finCoordIdeal k m S)).comap (affineSpaceSpecIso k m).hom
      = coordSubspaceIdeal k m S := by
  have : IsAffine (affineSpaceFin k m) := inferInstance
  have hset : ((affineSpaceSpecIso k m).hom.appTop.hom) ''
      (((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv.hom) ''
        ((MvPolynomial.X : ULift.{u} (Fin m) → MvPolynomial (ULift.{u} (Fin m)) k) ''
          (↑(uliftFinset.{u} m S) : Set (ULift.{u} (Fin m)))))
      = (fun i => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
          (↑S : Set (Fin m)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, ⟨j, hj, rfl⟩, rfl⟩, rfl⟩
      exact ⟨j.down, Finset.mem_coe.mpr (down_mem_of_mem_uliftFinset (Finset.mem_coe.mp hj)),
        (affineSpaceSpecIso_hom_appTop_X_consolidated207 k m j).symm⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv.hom
          (MvPolynomial.X (ULift.up i)),
        ⟨MvPolynomial.X (ULift.up i),
          ⟨ULift.up i, Finset.mem_coe.mpr (up_mem_uliftFinset (Finset.mem_coe.mp hi)), rfl⟩, rfl⟩,
        ?_⟩
      exact affineSpaceSpecIso_hom_appTop_X_consolidated207 k m (ULift.up i)
  have hI : (finCoordIdeal k m S : Ideal (MvPolynomial (ULift.{u} (Fin m)) k))
      = Ideal.span ((MvPolynomial.X : ULift.{u} (Fin m) → MvPolynomial (ULift.{u} (Fin m)) k) ''
          (↑(uliftFinset.{u} m S) : Set (ULift.{u} (Fin m)))) :=
    coordIdeal_eq_span k (uliftFinset.{u} m S)
  rw [Blowup.specIdealSheaf_eq_ofIdealTop, Scheme.IdealSheafData.comap_ofIdealTop, coordSubspaceIdeal_eq_ofIdealTop_span_coord, hI,
    Ideal.map_span, Ideal.map_span, hset]

theorem isBlowupAlongIdealSheaf_affineSpaceCoordBlowupMap :
    Blowup.IsBlowupAlongIdealSheaf (affineSpaceCoordBlowupMap k m S) (coordSubspaceIdeal k m S) := by
  rw [← comap_specIdealSheaf_finCoordIdeal_consolidated207 k m S]
  exact (Blowup.isBlowupAlongIdealSheaf_affineBlowup_toSpec (finCoordIdeal k m S)).comp_iso_hom
    (affineSpaceSpecIso k m).symm


end

abbrev finCoordIdealGen (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    ↥(finCoordIdeal k m S) :=
  coordIdealGen k (uliftFinset.{u} m S) (ULift.up s) (up_mem_uliftFinset hs)

abbrev coordBlowupChartRing (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :=
  HomogeneousLocalization.Away (Blowup.reesGrading (finCoordIdeal k m S))
    (Blowup.reesGenerator (finCoordIdeal k m S) (finCoordIdealGen k m S s hs))

def coordBlowupChartRingEquiv (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    coordBlowupChartRing k m S s hs ≃+* MvPolynomial (ULift.{u} (Fin m)) k :=
  @awayCoordGenEquivMvPolynomial k _ (ULift.{u} (Fin m)) (Classical.decEq _) (uliftFinset.{u} m S) (ULift.up s)
    (up_mem_uliftFinset hs)

def coordBlowupChartRingCatIso (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    CommRingCat.of (coordBlowupChartRing k m S s hs) ≅
      CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k) :=
  (coordBlowupChartRingEquiv k m S s hs).toCommRingCatIso

def specCoordBlowupChartRingIso (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    Spec (CommRingCat.of (coordBlowupChartRing k m S s hs)) ≅
      Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k)) where
  hom := Spec.map (coordBlowupChartRingCatIso k m S s hs).inv
  inv := Spec.map (coordBlowupChartRingCatIso k m S s hs).hom
  hom_inv_id := by rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
  inv_hom_id := by rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]

def specCoordBlowupChartRingIsoAffineSpace (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    Spec (CommRingCat.of (coordBlowupChartRing k m S s hs)) ≅ affineSpaceFin k m :=
  specCoordBlowupChartRingIso k m S s hs ≪≫ (affineSpaceSpecIso k m).symm

def affineSpaceCoordBlowupChart (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m)
    (hs : s ∈ S) :
    Spec (CommRingCat.of (coordBlowupChartRing k m S s hs)) ⟶ affineSpaceCoordBlowup k m S :=
  Blowup.affineBlowupChart (finCoordIdeal k m S) (finCoordIdealGen k m S s hs)

instance instIsOpenImmersionModelBlowupChart (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))
    (s : Fin m) (hs : s ∈ S) : IsOpenImmersion (affineSpaceCoordBlowupChart k m S s hs) :=
  Blowup.instIsOpenImmersionAffineBlowupChart (finCoordIdeal k m S) (finCoordIdealGen k m S s hs)

private def coordBlowupSubstUliftFin_consolidated207 (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) :
    MvPolynomial (ULift.{u} (Fin m)) k →ₐ[k] MvPolynomial (ULift.{u} (Fin m)) k :=
  @coordBlowupSubst k _ (ULift.{u} (Fin m)) (Classical.decEq _) (uliftFinset.{u} m S) (ULift.up s)

section
variable (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))

private theorem specMap_coordBlowupSubstUliftFin_comp_affineSpaceSpecIso_inv_consolidated207 (s : Fin m) :
    Spec.map (CommRingCat.ofHom (coordBlowupSubstUliftFin_consolidated207 k m S s).toRingHom)
        ≫ (affineSpaceSpecIso k m).inv
      = (affineSpaceSpecIso k m).inv ≫ coordBlowupSubstMap k m S s := by
  refine AffineSpace.hom_ext ?_ ?_
  · show (Spec.map (CommRingCat.ofHom (coordBlowupSubstUliftFin_consolidated207 k m S s).toRingHom)
          ≫ (affineSpaceSpecIso k m).inv) ≫ affineSpaceFinToSpec k m
      = ((affineSpaceSpecIso k m).inv ≫ coordBlowupSubstMap k m S s) ≫ affineSpaceFinToSpec k m
    rw [Category.assoc, Category.assoc, coordBlowupSubstMap_comp_affineSpaceFinToSpec, affineSpaceSpecIso_inv_comp_affineSpaceFinToSpec_consolidated207,
      ← Spec.map_comp]
    congr 1
    ext r
    simp [coordBlowupSubstUliftFin_consolidated207]
  · intro i
    show (Spec.map (CommRingCat.ofHom (coordBlowupSubstUliftFin_consolidated207 k m S s).toRingHom)
          ≫ (affineSpaceSpecIso k m).inv).appTop.hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) i)
      = ((affineSpaceSpecIso k m).inv ≫ coordBlowupSubstMap k m S s).appTop.hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) i)
    rw [appTop_comp_apply_eq_appTop_appTop_consolidated207, appTop_comp_apply_eq_appTop_appTop_consolidated207, affineSpaceSpecIso_inv_appTop_coord_consolidated207,
      appTop_specMap_ΓSpecIso_inv_apply_consolidated207, coordBlowupSubstMap_appTop_coord]
    by_cases hc : i.down ∈ S ∧ i.down ≠ s
    · rw [if_pos hc, map_mul, affineSpaceSpecIso_inv_appTop_coord_consolidated207, affineSpaceSpecIso_inv_appTop_coord_consolidated207]
      simp [coordBlowupSubstUliftFin_consolidated207, ULift.ext_iff, hc.1, hc.2]
    · rw [if_neg hc, affineSpaceSpecIso_inv_appTop_coord_consolidated207]
      simp [coordBlowupSubstUliftFin_consolidated207, ULift.ext_iff, hc]

theorem affineSpaceCoordBlowupChart_comp_affineSpaceCoordBlowupMap (s : Fin m) (hs : s ∈ S) :
    affineSpaceCoordBlowupChart k m S s hs ≫ affineSpaceCoordBlowupMap k m S =
      (specCoordBlowupChartRingIsoAffineSpace k m S s hs).hom ≫ coordBlowupSubstMap k m S s := by
  have hcomp : (coordBlowupChartRingEquiv k m S s hs).symm.toRingHom.comp
      (coordBlowupSubstUliftFin_consolidated207 k m S s).toRingHom
      = Blowup.chartRingHom (finCoordIdeal k m S) (finCoordIdealGen k m S s hs) :=
    @awayCoordGenEquivMvPolynomial_symm_comp_coordBlowupSubst k _ (ULift.{u} (Fin m)) (Classical.decEq _)
      (uliftFinset.{u} m S) (ULift.up s) (up_mem_uliftFinset hs)
  have hring : CommRingCat.ofHom (Blowup.chartRingHom (finCoordIdeal k m S) (finCoordIdealGen k m S s hs))
      = CommRingCat.ofHom (coordBlowupSubstUliftFin_consolidated207 k m S s).toRingHom ≫
        CommRingCat.ofHom (coordBlowupChartRingEquiv k m S s hs).symm.toRingHom := by
    rw [← hcomp]
    rfl
  show Blowup.affineBlowupChart (finCoordIdeal k m S) (finCoordIdealGen k m S s hs) ≫
      (Blowup.AffineBlowup.toSpec (finCoordIdeal k m S) ≫ (affineSpaceSpecIso k m).inv)
    = (specCoordBlowupChartRingIsoAffineSpace k m S s hs).hom ≫ coordBlowupSubstMap k m S s
  rw [← Category.assoc, Blowup.affineBlowupChart_comp_toSpec, Blowup.algebraMap_chart_eq_chartRingHom, hring,
    Spec.map_comp, Category.assoc, specMap_coordBlowupSubstUliftFin_comp_affineSpaceSpecIso_inv_consolidated207 k m S s, ← Category.assoc]
  rfl

theorem iSup_opensRange_affineSpaceCoordBlowupChart :
    (⨆ i : ↥S, Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S i.1 i.2))
      = (⊤ : (affineSpaceCoordBlowup k m S).Opens) := by
  refine le_antisymm le_top ?_
  rw [← iSup_opensRange_affineBlowupChart_coordIdealGen k (uliftFinset.{u} m S)]
  refine iSup_le fun j => ?_
  refine le_iSup_of_le ⟨j.1.down, down_mem_of_mem_uliftFinset j.2⟩ ?_
  exact le_rfl


end

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDimensionBound
section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}

private theorem nontrivial_sections_of_mem_consolidated195 (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    Nontrivial Γ(X, U) := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hs
  have := hs
  have h1 : (1 : Γ(X, U)) ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    rw [Subsingleton.elim (1 : Γ(X, U)) 0]
    exact Ideal.zero_mem _
  exact (hU.primeIdealOf ⟨x, hx⟩).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

private theorem ideal_le_primeIdealOf_of_mem_support_consolidated195 (I : X.IdealSheafData)
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (hxI : x ∈ I.support) :
    I.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h1 := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := ⟨U, hU⟩) hx).mp hxI
  rw [Scheme.mem_zeroLocus_iff] at h1
  intro f hf
  rw [← germ_mem_maximalIdeal_iff hU x hx f, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact h1 f hf ((X.mem_basicOpen f x hx).mpr hu)

section
variable (hU : IsAffineOpen U) (c : EtaleChart p U m)
include hU

private theorem coord_injective_consolidated195 (x : X) (hx : x ∈ U) : Function.Injective c.coord := by
  let inst : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra
  have : Algebra.Etale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra_etale hU
  have : Nontrivial Γ(X, U) := nontrivial_sections_of_mem_consolidated195 hU x hx
  have : Module.Flat (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := inferInstance
  have := Module.Flat.isTorsionFree (R := MvPolynomial (ULift.{u} (Fin m)) k) (M := Γ(X, U))
  have hinj0 : Function.Injective
      (algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hinj : Function.Injective ⇑c.coordRingHom := hinj0
  intro a b hab
  have h1 : (MvPolynomial.X (ULift.up a) : MvPolynomial (ULift.{u} (Fin m)) k)
      = MvPolynomial.X (ULift.up b) := by
    apply hinj
    rw [EtaleChart.coordRingHom_X, EtaleChart.coordRingHom_X, hab]
  have h2 : (ULift.up a : ULift.{u} (Fin m)) = ULift.up b := MvPolynomial.X_injective h1
  exact congrArg ULift.down h2

theorem card_le_ringKrullDim_stalk (x : X) (hx : x ∈ U) (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    (J.card : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
  classical
  obtain ⟨d, f, -, hf2, -, hd⟩ :=
    exists_sections_span_eq_maximalIdeal_with_coords hU c x hx J
      (fun j hj => (germ_mem_maximalIdeal_iff hU x hx (c.coord j)).mpr (hJ j hj))
  rw [← hd]
  rcases Finset.eq_empty_or_nonempty J with rfl | hJne
  · simp only [Finset.card_empty]
    exact_mod_cast Nat.zero_le d
  · obtain ⟨j₀, hj₀⟩ := hJne
    obtain ⟨i₀, -⟩ := hf2 j₀ hj₀
    have hch : ∀ j : Fin m, ∃ i : Fin d, j ∈ J → f i = c.coord j := by
      intro j
      by_cases hj : j ∈ J
      · obtain ⟨i, hi⟩ := hf2 j hj
        exact ⟨i, fun _ => hi⟩
      · exact ⟨i₀, fun h => absurd h hj⟩
    choose g hg using hch
    have hmap : ∀ a ∈ J, g a ∈ (Finset.univ : Finset (Fin d)) := fun a _ => Finset.mem_univ _
    have hinjOn : Set.InjOn g (J : Set (Fin m)) := by
      intro a ha b hb hab
      have h1 : c.coord a = c.coord b := by
        rw [← hg a (Finset.mem_coe.mp ha), ← hg b (Finset.mem_coe.mp hb), hab]
      exact coord_injective_consolidated195 hU c x hx h1
    have hcard : J.card ≤ (Finset.univ : Finset (Fin d)).card :=
      Finset.card_le_card_of_injOn g hmap hinjOn
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    exact_mod_cast hcard

theorem coord_mem_primeIdealOf_of_restrictIdeal_eq_coordIdeal_singleton
    (j : Fin m) (D : X.IdealSheafData) (hD : restrictIdeal D U = c.coordIdeal {j})
    (x : X) (hx : x ∈ U) (hxD : x ∈ D.support) :
    c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h1 : D.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' ((({j} : Finset (Fin m))) : Set (Fin m))) :=
    EtaleChart.ideal_eq_span_coord c hU D {j} hD
  have h2 : D.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    ideal_le_primeIdealOf_of_mem_support_consolidated195 D hU hx hxD
  refine h2 ?_
  rw [h1]
  exact Ideal.subset_span ⟨j, by simp, rfl⟩


end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

section
namespace FunctorialResolution.EmbeddedResolution


structure BlowupChart {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) (s : Fin m) where
  domain : X₁.Opens
  domain_le : domain ≤ π ⁻¹ᵁ U
  chart : EtaleChart (π ≫ p) domain m
  comm : chart.map ≫ coordBlowupSubstMap k m S s = π.resLE U domain domain_le ≫ c.map

private theorem exists_opens_isPullback_of_opens_consolidated225 {X₁ M : Scheme.{u}} (V : X₁.Opens)
    (q : V.toScheme ⟶ M) (W : M.Opens) :
    ∃ (dom : X₁.Opens) (_hle : dom ≤ V) (g : dom.toScheme ⟶ W.toScheme)
      (r : dom.toScheme ⟶ V.toScheme),
      IsPullback g r W.ι q ∧ r ≫ V.ι = dom.ι ∧
        ∀ y, q.base y ∈ W → V.ι.base y ∈ dom := by
  classical
  have hdle : Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι) ≤ V := by
    rintro x ⟨y, rfl⟩
    have h1 : V.ι.base ((q ⁻¹ᵁ W).ι.base y) ∈ Set.range V.ι.base := ⟨_, rfl⟩
    rw [Scheme.Opens.range_ι] at h1
    exact h1
  obtain ⟨e, he⟩ : ∃ e : (Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι)).toScheme ≅
      (q ⁻¹ᵁ W).toScheme,
      e.hom ≫ ((q ⁻¹ᵁ W).ι ≫ V.ι) = (Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι)).ι :=
    ⟨IsOpenImmersion.isoOfRangeEq (Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι)).ι
        ((q ⁻¹ᵁ W).ι ≫ V.ι) (Scheme.Opens.range_ι _),
      IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩
  refine ⟨Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι), hdle, e.hom ≫ (q ∣_ W),
    e.hom ≫ (q ⁻¹ᵁ W).ι, ?_, ?_, ?_⟩
  · have h1 : IsPullback e.hom (e.hom ≫ (q ⁻¹ᵁ W).ι) ((q ⁻¹ᵁ W).ι) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by simp⟩
    have h2 := h1.paste_horiz (isPullback_morphismRestrict q W)
    rwa [Category.id_comp] at h2
  · rw [Category.assoc]
    exact he
  · intro y hy
    exact ⟨⟨y, hy⟩, rfl⟩

private theorem exists_blowupChart_family_isPullback_covering_consolidated225 {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) (Z : X.IdealSheafData)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S) :
    ∃ F : ∀ s : Fin m, s ∈ S → BlowupChart π c S s,
      (∀ (s : Fin m) (hs : s ∈ S),
          IsPullback (F s hs).chart.map
            (π.resLE U (F s hs).domain (F s hs).domain_le)
            (coordBlowupSubstMap k m S s) c.map) ∧
      (∀ x : ↥X₁, x ∈ π ⁻¹ᵁ U → ∃ (s : Fin m) (hs : s ∈ S), x ∈ (F s hs).domain) := by
  classical
  have : Etale c.map := c.isEtale
  have : Flat c.map := inferInstance
  have hcomap : Z.comap U.ι = (coordSubspaceIdeal k m S).comap c.map := by
    rw [← restrictIdeal_eq_comap_ι, hZ, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  have hres : Blowup.IsBlowupAlongIdealSheaf (π ∣_ U) ((coordSubspaceIdeal k m S).comap c.map) := by
    have h1 := hπ.restrict U
    rwa [hcomap] at h1
  obtain ⟨q, -, hq⟩ := (isBlowupAlongIdealSheaf_affineSpaceCoordBlowupMap k m S).exists_isPullback_of_flat c.map hres
  have key : ∀ (s : Fin m) (hs : s ∈ S), ∃ B : BlowupChart π c S s,
      IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map ∧
        ∀ y, q.base y ∈ Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs) →
          (π ⁻¹ᵁ U).ι.base y ∈ B.domain := by
    intro s hs
    obtain ⟨dom, hle, g, r, hpb, hrι, hmem⟩ :=
      exists_opens_isPullback_of_opens_consolidated225 (π ⁻¹ᵁ U) q (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs))
    have hrange : Set.range (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι.base
        = Set.range (affineSpaceCoordBlowupChart k m S s hs).base :=
      Scheme.Opens.range_ι (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs))
    obtain ⟨eW, heW⟩ : ∃ e : (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).toScheme ≅
        affineSpaceFin k m,
        e.hom ≫ coordBlowupSubstMap k m S s =
          (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι ≫ affineSpaceCoordBlowupMap k m S := by
      refine ⟨IsOpenImmersion.isoOfRangeEq
          (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι
          (affineSpaceCoordBlowupChart k m S s hs) hrange ≪≫ specCoordBlowupChartRingIsoAffineSpace k m S s hs, ?_⟩
      have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac
        (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι
        (affineSpaceCoordBlowupChart k m S s hs) hrange
      rw [Iso.trans_hom, Category.assoc, ← affineSpaceCoordBlowupChart_comp_affineSpaceCoordBlowupMap,
        ← Category.assoc, hfac]
    have heW' : eW.inv ≫ (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι ≫
        affineSpaceCoordBlowupMap k m S = coordBlowupSubstMap k m S s := by
      rw [← heW, Iso.inv_hom_id_assoc]
    have hleft : r ≫ (π ∣_ U) = π.resLE U dom hle := by
      rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι,
        ← Category.assoc, hrι]
    have hsq : IsPullback (g ≫ eW.hom) (π.resLE U dom hle) (coordBlowupSubstMap k m S s) c.map := by
      have h1 : IsPullback (g ≫ eW.hom) (𝟙 _) eW.inv g :=
        IsPullback.of_vert_isIso ⟨by simp⟩
      have h2 := h1.paste_vert (hpb.paste_vert hq)
      rwa [Category.id_comp, hleft, heW'] at h2
    have hetale : Etale (g ≫ eW.hom) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip c.isEtale
    refine ⟨⟨dom, hle, ⟨g ≫ eW.hom, ?_, hetale⟩, hsq.w⟩, hsq, hmem⟩
    calc (g ≫ eW.hom) ≫ affineSpaceFinToSpec k m
        = (g ≫ eW.hom) ≫ coordBlowupSubstMap k m S s ≫ affineSpaceFinToSpec k m := by
          rw [coordBlowupSubstMap_comp_affineSpaceFinToSpec]
      _ = ((g ≫ eW.hom) ≫ coordBlowupSubstMap k m S s) ≫ affineSpaceFinToSpec k m := by
          simp only [Category.assoc]
      _ = (π.resLE U dom hle ≫ c.map) ≫ affineSpaceFinToSpec k m := by rw [hsq.w]
      _ = π.resLE U dom hle ≫ c.map ≫ affineSpaceFinToSpec k m := by simp only [Category.assoc]
      _ = π.resLE U dom hle ≫ U.ι ≫ p := by rw [c.comp_struct]
      _ = (π.resLE U dom hle ≫ U.ι) ≫ p := by simp only [Category.assoc]
      _ = (dom.ι ≫ π) ≫ p := by rw [Scheme.Hom.resLE_comp_ι]
      _ = dom.ι ≫ π ≫ p := by simp only [Category.assoc]
  choose F hF1 hF2 using key
  refine ⟨F, hF1, ?_⟩
  intro x hx
  have hx' : x ∈ Set.range (π ⁻¹ᵁ U).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  have hy : q.base y ∈
      (⨆ i : ↥S, Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S i.1 i.2)) := by
    rw [iSup_opensRange_affineSpaceCoordBlowupChart k m S]
    simp
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  exact ⟨i.1, i.2, hF2 i.1 i.2 y hi⟩

def blowupChartOfIsBlowup {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) {Z : X.IdealSheafData}
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (s : Fin m) (hs : s ∈ S) : BlowupChart π c S s :=
  (exists_blowupChart_family_isPullback_covering_consolidated225 π c S Z hπ hZ).choose s hs

section
variable {X X₁ : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (S : Finset (Fin m)) {Z : X.IdealSheafData} (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S)

theorem isPullback_blowupChart_of_isBlowupAlongIdealSheaf (s : Fin m) (hs : s ∈ S) :
    IsPullback (blowupChartOfIsBlowup π c S hπ hZ s hs).chart.map
      (π.resLE U (blowupChartOfIsBlowup π c S hπ hZ s hs).domain
        (blowupChartOfIsBlowup π c S hπ hZ s hs).domain_le)
      (coordBlowupSubstMap k m S s) c.map :=
  (exists_blowupChart_family_isPullback_covering_consolidated225 π c S Z hπ hZ).choose_spec.1 s hs

theorem exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf (x : ↥X₁) (hx : x ∈ π ⁻¹ᵁ U) :
    ∃ (s : Fin m) (hs : s ∈ S), x ∈ (blowupChartOfIsBlowup π c S hπ hZ s hs).domain :=
  (exists_blowupChart_family_isPullback_covering_consolidated225 π c S Z hπ hZ).choose_spec.2 x hx


end

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupClosedSubscheme
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

private theorem mem_strictTransform_of_mul_mem_consolidated234 {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [QuasiCompact (strictTransformι π Z D)]
    (V : X₁.affineOpens) (t : Γ(X₁, V.1))
    (ht : (Z.comap π).ideal V = Ideal.span {t}) (f : Γ(X₁, V.1))
    (hf : t * f ∈ (Blowup.strictTransform π Z D).ideal V) :
    f ∈ (Blowup.strictTransform π Z D).ideal V := by
  obtain ⟨n, hn⟩ := (mem_strictTransform_ideal_iff π Z D V t ht (t * f)).mp hf
  refine (mem_strictTransform_ideal_iff π Z D V t ht f).mpr ⟨n + 1, ?_⟩
  rw [pow_succ, mul_assoc]
  exact hn

private theorem exists_ideal_eq_span_singleton_of_le_consolidated234 {X : Scheme.{u}} (I : X.IdealSheafData)
    (U V : X.affineOpens) (e : (V : X.Opens) ≤ (U : X.Opens)) (t : Γ(X, (U : X.Opens)))
    (ht : I.ideal U = Ideal.span {t}) :
    ∃ t' : Γ(X, (V : X.Opens)), I.ideal V = Ideal.span {t'} := by
  have e' : (V : X.Opens) ≤ (𝟙 X) ⁻¹ᵁ (U : X.Opens) := e
  have h := Scheme.IdealSheafData.comap_ideal_eq_map_appLE I (𝟙 X) U V e'
  rw [Scheme.IdealSheafData.comap_id] at h
  refine ⟨(Scheme.Hom.appLE (𝟙 X) (U : X.Opens) (V : X.Opens) e').hom t, ?_⟩
  rw [h, ht, Ideal.map_span, Set.image_singleton]

private theorem restrict_basicOpen_mem_nonZeroDivisors_consolidated234 {W : Scheme.{u}} (P : W.affineOpens)
    (d : Γ(W, (P : W.Opens))) {u : Γ(W, (P : W.Opens))}
    (hu : u ∈ nonZeroDivisors Γ(W, (P : W.Opens))) :
    (W.presheaf.map (homOfLE (W.basicOpen_le d)).op).hom u
      ∈ nonZeroDivisors Γ(W, W.basicOpen d) := by
  have := P.2.isLocalization_basicOpen d
  have halg : (algebraMap Γ(W, (P : W.Opens)) Γ(W, W.basicOpen d))
      = (W.presheaf.map (homOfLE (W.basicOpen_le d)).op).hom := rfl
  have h : algebraMap Γ(W, (P : W.Opens)) Γ(W, W.basicOpen d) u
      ∈ nonZeroDivisors Γ(W, W.basicOpen d) :=
    IsLocalization.nonZeroDivisors_le_comap (M := Submonoid.powers d)
      (S := Γ(W, W.basicOpen d)) hu
  rwa [halg] at h

private theorem mem_nonZeroDivisors_of_dvd_consolidated234 {R : Type u} [CommRing R] {a b : R}
    (hb : b ∈ nonZeroDivisors R) (hab : a ∣ b) : a ∈ nonZeroDivisors R := by
  obtain ⟨c, hc⟩ := hab
  have key : ∀ z : R, a * z = 0 → z = 0 := by
    intro z hz
    refine (mem_nonZeroDivisors_iff.mp hb).1 z ?_
    rw [hc, mul_assoc, mul_comm c z, ← mul_assoc, hz, zero_mul]
  exact mem_nonZeroDivisors_iff.mpr ⟨key, fun z hz => key z (by rw [mul_comm]; exact hz)⟩

private theorem eq_zero_of_locally_eq_zero_consolidated234 {W : Scheme.{u}} (U : W.Opens) (x : Γ(W, U))
    (h : ∀ w ∈ U, ∃ (P : W.Opens) (hP : P ≤ U), w ∈ P ∧
      (W.presheaf.map (homOfLE hP).op).hom x = 0) : x = 0 := by
  classical
  choose P hP hmem hzero using h
  refine TopCat.Sheaf.eq_of_locally_eq' W.sheaf
    (fun w : { w : ↥W // w ∈ U } => P w.1 w.2) U
    (fun w => homOfLE (hP w.1 w.2)) ?_ x 0 ?_
  · exact fun w hw => Opens.mem_iSup.mpr ⟨⟨w, hw⟩, hmem w hw⟩
  · intro w
    rw [map_zero]
    exact hzero w.1 w.2

section
variable {X X₁ S : Scheme.{u}} (j : S ⟶ X)

theorem ker_le_ker_strictTransform_subschemeι_comp (π : X₁ ⟶ X) (Z : X.IdealSheafData) :
    j.ker ≤ ((Blowup.strictTransform π Z j.ker).subschemeι ≫ π).ker := by
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.le_map_iff_comap_le]
  exact comap_le_strictTransform π Z j.ker

theorem exists_comp_eq_strictTransform_subschemeι_comp [IsClosedImmersion j] (π : X₁ ⟶ X) (Z : X.IdealSheafData) :
    ∃ q : (Blowup.strictTransform π Z j.ker).subscheme ⟶ S,
      q ≫ j = (Blowup.strictTransform π Z j.ker).subschemeι ≫ π :=
  ⟨AlgebraicGeometry.IsClosedImmersion.lift j ((Blowup.strictTransform π Z j.ker).subschemeι ≫ π)
      (ker_le_ker_strictTransform_subschemeι_comp j π Z),
    AlgebraicGeometry.IsClosedImmersion.lift_fac j _ _⟩


end

def strictTransformLiftOfClosedImmersion {X X₁ S : Scheme.{u}} (j : S ⟶ X)
    [IsClosedImmersion j] (π : X₁ ⟶ X) (Z : X.IdealSheafData) :
    (Blowup.strictTransform π Z j.ker).subscheme ⟶ S :=
  (exists_comp_eq_strictTransform_subschemeι_comp j π Z).choose

section
variable {X X₁ S : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]

theorem strictTransformLiftOfClosedImmersion_comp (π : X₁ ⟶ X) (Z : X.IdealSheafData) :
    strictTransformLiftOfClosedImmersion j π Z ≫ j = (Blowup.strictTransform π Z j.ker).subschemeι ≫ π :=
  (exists_comp_eq_strictTransform_subschemeι_comp j π Z).choose_spec

theorem isBlowupAlongIdealSheaf_strictTransformLiftOfClosedImmersion [IsLocallyNoetherian X₁]
    (π : X₁ ⟶ X) (Z : X.IdealSheafData) (h : Blowup.IsBlowupAlongIdealSheaf π Z) :
    Blowup.IsBlowupAlongIdealSheaf (strictTransformLiftOfClosedImmersion j π Z) (Z.comap j) := by
  have : QuasiCompact (strictTransformι π Z j.ker) :=
    FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian π Z j.ker
  have hcomap : (Z.comap j).comap (strictTransformLiftOfClosedImmersion j π Z)
      = (Z.comap π).comap (Blowup.strictTransform π Z j.ker).subschemeι := by
    rw [← Scheme.IdealSheafData.comap_comp, strictTransformLiftOfClosedImmersion_comp,
      Scheme.IdealSheafData.comap_comp]
  refine ⟨?_, ?_⟩
  · rw [hcomap]
    intro x
    obtain ⟨V, t, hxV, -, hVspan⟩ := h.1 ((Blowup.strictTransform π Z j.ker).subschemeι.base x)
    refine ⟨⟨(Blowup.strictTransform π Z j.ker).subschemeι ⁻¹ᵁ (V : X₁.Opens),
      V.2.preimage (Blowup.strictTransform π Z j.ker).subschemeι⟩,
      ((Blowup.strictTransform π Z j.ker).subschemeι.app (V : X₁.Opens)).hom t, hxV, ?_, ?_⟩
    · have key : ∀ z : Γ((Blowup.strictTransform π Z j.ker).subscheme,
          (Blowup.strictTransform π Z j.ker).subschemeι ⁻¹ᵁ (V : X₁.Opens)),
          z * ((Blowup.strictTransform π Z j.ker).subschemeι.app (V : X₁.Opens)).hom t = 0 → z = 0 := by
        intro z hz
        have hinj : Function.Injective
            ⇑(((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom.hom) := by
          intro A B hAB
          have h1 : ((((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom ≫
              ((Blowup.strictTransform π Z j.ker).subschemeObjIso V).inv).hom) A
              = ((((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom ≫
              ((Blowup.strictTransform π Z j.ker).subschemeObjIso V).inv).hom) B := by
            simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hAB]
          simpa using h1
        have hcompo : ((Blowup.strictTransform π Z j.ker).subschemeι.app (V : X₁.Opens))
            ≫ ((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom
            = CommRingCat.ofHom (Ideal.Quotient.mk ((Blowup.strictTransform π Z j.ker).ideal V)) := by
          rw [Scheme.IdealSheafData.subschemeι_app, Category.assoc, Iso.inv_hom_id,
            Category.comp_id]
        have hft : (((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom.hom)
            (((Blowup.strictTransform π Z j.ker).subschemeι.app (V : X₁.Opens)).hom t)
            = Ideal.Quotient.mk ((Blowup.strictTransform π Z j.ker).ideal V) t := by
          have h2 : ((((Blowup.strictTransform π Z j.ker).subschemeι.app (V : X₁.Opens))
              ≫ ((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom).hom) t
              = (((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom.hom)
                (((Blowup.strictTransform π Z j.ker).subschemeι.app (V : X₁.Opens)).hom t) := by
            rw [CommRingCat.hom_comp]; rfl
          rw [← h2, hcompo]
          rfl
        obtain ⟨z₀, hz₀⟩ := Ideal.Quotient.mk_surjective
          ((((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom.hom) z)
        have h1 : (((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom.hom) z *
            (((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom.hom)
              (((Blowup.strictTransform π Z j.ker).subschemeι.app (V : X₁.Opens)).hom t) = 0 := by
          rw [← map_mul, hz, map_zero]
        rw [hft, ← hz₀] at h1
        have h2 : Ideal.Quotient.mk ((Blowup.strictTransform π Z j.ker).ideal V) (z₀ * t) = 0 := by
          rw [map_mul]; exact h1
        have h3 : z₀ * t ∈ (Blowup.strictTransform π Z j.ker).ideal V :=
          (Ideal.Quotient.eq_zero_iff_mem).mp h2
        have h4 : z₀ ∈ (Blowup.strictTransform π Z j.ker).ideal V :=
          mem_strictTransform_of_mul_mem_consolidated234 π Z j.ker V t hVspan z₀ (by rwa [mul_comm] at h3)
        have h5 : (((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom.hom) z = 0 := by
          rw [← hz₀]
          exact (Ideal.Quotient.eq_zero_iff_mem).mpr h4
        refine hinj ?_
        rw [h5, map_zero]
      rw [mem_nonZeroDivisors_iff]
      exact ⟨fun z hz => key z (by rw [mul_comm]; exact hz), key⟩
    · rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (Z.comap π)
          (Blowup.strictTransform π Z j.ker).subschemeι V
          ⟨(Blowup.strictTransform π Z j.ker).subschemeι ⁻¹ᵁ (V : X₁.Opens),
            V.2.preimage (Blowup.strictTransform π Z j.ker).subschemeι⟩ le_rfl,
        hVspan, Ideal.map_span, Scheme.Hom.appLE_eq_app, Set.image_singleton]
  · intro W g hg
    have hECg : Blowup.IsLocallyGeneratedByNonZeroDivisor (Z.comap (g ≫ j)) := by
      rw [Scheme.IdealSheafData.comap_comp]
      exact hg
    obtain ⟨a, hacomp⟩ : ∃ a : W ⟶ X₁, a ≫ π = g ≫ j :=
      ⟨h.lift (g ≫ j) hECg, h.lift_comp (g ≫ j) hECg⟩
    have hWcomap : (Z.comap j).comap g = (Z.comap π).comap a := by
      rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hacomp]
    have hDker : (j.ker).comap π ≤ Scheme.Hom.ker a := by
      rw [← Scheme.IdealSheafData.le_map_iff_comap_le, ← Scheme.Hom.ker_comp, hacomp]
      apply Scheme.Hom.le_ker_comp
    have hD'ker : Blowup.strictTransform π Z j.ker ≤ Scheme.Hom.ker a := by
      have hker : Scheme.Hom.ker a = Scheme.IdealSheafData.ofIdeals
          (fun U : X₁.affineOpens => RingHom.ker ((a.app (U : X₁.Opens)).hom)) := rfl
      rw [hker, Scheme.IdealSheafData.le_ofIdeals_iff]
      intro V s hs
      rw [RingHom.mem_ker]
      refine eq_zero_of_locally_eq_zero_consolidated234 (a ⁻¹ᵁ (V : X₁.Opens)) ((a.app (V : X₁.Opens)).hom s) ?_
      intro w hw
      obtain ⟨V₀, t₀, hyV₀, -, hV₀span⟩ := h.1 (a.base w)
      obtain ⟨c, hcle, hcmem⟩ :=
        V.2.exists_basicOpen_le (⟨a.base w, hyV₀⟩ : ↥(V₀ : X₁.Opens)) hw
      obtain ⟨P₀, u, hwP₀, hunzd, hP₀span⟩ := hg w
      have hwc : w ∈ a ⁻¹ᵁ (X₁.basicOpen c) := hcmem
      obtain ⟨d, hdle, hdmem⟩ :=
        P₀.2.exists_basicOpen_le (⟨w, hwc⟩ : ↥(a ⁻¹ᵁ (X₁.basicOpen c))) hwP₀
      have hcle' : ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
          ≤ ((V₀ : X₁.affineOpens) : X₁.Opens) := hcle
      have hdle' : ((W.affineBasicOpen d : W.affineOpens) : W.Opens)
          ≤ a ⁻¹ᵁ ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens) := hdle
      have hPU' : ((W.affineBasicOpen d : W.affineOpens) : W.Opens) ≤ a ⁻¹ᵁ (V : X₁.Opens) :=
        fun z hz => X₁.basicOpen_le c (hdle hz)
      have hCV : ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens) ≤ (V : X₁.Opens) :=
        X₁.basicOpen_le c
      obtain ⟨t', ht'⟩ :=
        exists_ideal_eq_span_singleton_of_le_consolidated234 (Z.comap π) V₀ (X₁.affineBasicOpen c) hcle' t₀ hV₀span
      have hs₁ : (X₁.presheaf.map (homOfLE hCV).op).hom s
          ∈ (Blowup.strictTransform π Z j.ker).ideal (X₁.affineBasicOpen c) := by
        rw [← Scheme.IdealSheafData.map_ideal_basicOpen]
        exact Ideal.mem_map_of_mem _ hs
      obtain ⟨n, hn⟩ := (mem_strictTransform_ideal_iff π Z j.ker (X₁.affineBasicOpen c) t' ht'
        ((X₁.presheaf.map (homOfLE hCV).op).hom s)).mp hs₁
      have hkerapp : (a.app ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)).hom
          (t' ^ n * (X₁.presheaf.map (homOfLE hCV).op).hom s) = 0 := by
        have h1 := (Scheme.IdealSheafData.le_def.mp hDker) (X₁.affineBasicOpen c) hn
        exact RingHom.mem_ker.mp (Scheme.Hom.ideal_ker_le a _ h1)
      have hφ : Scheme.Hom.appLE a ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
            ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hdle'
          = a.app ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
            ≫ W.presheaf.map (homOfLE hdle').op := rfl
      have hzero1 : (Scheme.Hom.appLE a ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
            ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hdle').hom
          (t' ^ n * (X₁.presheaf.map (homOfLE hCV).op).hom s) = 0 := by
        rw [hφ, CommRingCat.hom_comp, RingHom.comp_apply, hkerapp, map_zero]
      have hmulzero : ((Scheme.Hom.appLE a
              ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
              ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hdle').hom t') ^ n *
          (Scheme.Hom.appLE a ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
              ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hdle').hom
            ((X₁.presheaf.map (homOfLE hCV).op).hom s) = 0 := by
        rw [← map_pow, ← map_mul]
        exact hzero1
      have hPspan : ((Z.comap π).comap a).ideal (W.affineBasicOpen d)
          = Ideal.span {(W.presheaf.map (homOfLE (W.basicOpen_le d)).op).hom u} := by
        rw [← Scheme.IdealSheafData.map_ideal_basicOpen, ← hWcomap, hP₀span, Ideal.map_span,
          Set.image_singleton]
      have hPspan' : ((Z.comap π).comap a).ideal (W.affineBasicOpen d)
          = Ideal.span {(Scheme.Hom.appLE a
              ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
              ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hdle').hom t'} := by
        rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (Z.comap π) a
            (X₁.affineBasicOpen c) (W.affineBasicOpen d) hdle', ht', Ideal.map_span,
          Set.image_singleton]
      have hu'nzd : (W.presheaf.map (homOfLE (W.basicOpen_le d)).op).hom u
          ∈ nonZeroDivisors _ := restrict_basicOpen_mem_nonZeroDivisors_consolidated234 P₀ d hunzd
      have hdvd : (Scheme.Hom.appLE a ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
            ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hdle').hom t' ∣
          (W.presheaf.map (homOfLE (W.basicOpen_le d)).op).hom u := by
        have hmem : (W.presheaf.map (homOfLE (W.basicOpen_le d)).op).hom u
            ∈ Ideal.span {(Scheme.Hom.appLE a
                ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
                ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hdle').hom t'} := by
          rw [← hPspan', hPspan]
          exact Ideal.mem_span_singleton_self _
        exact Ideal.mem_span_singleton.mp hmem
      have htnzd := mem_nonZeroDivisors_of_dvd_consolidated234 hu'nzd hdvd
      have hpownzd := Submonoid.pow_mem (nonZeroDivisors _) htnzd n
      have happLE : (Scheme.Hom.appLE a ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
            ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hdle').hom
          ((X₁.presheaf.map (homOfLE hCV).op).hom s) = 0 :=
        (mem_nonZeroDivisors_iff.mp hpownzd).1 _ hmulzero
      refine ⟨((W.affineBasicOpen d : W.affineOpens) : W.Opens), hPU', hdmem, ?_⟩
      have hsplit := Scheme.Hom.map_appLE a hdle' (homOfLE hCV).op
      have h0 : ((X₁.presheaf.map (homOfLE hCV).op
            ≫ Scheme.Hom.appLE a ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
                ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hdle').hom) s = 0 := by
        rw [CommRingCat.hom_comp, RingHom.comp_apply]
        exact happLE
      rw [hsplit] at h0
      have hEq : (W.presheaf.map (homOfLE hPU').op).hom ((a.app (V : X₁.Opens)).hom s)
          = (Scheme.Hom.appLE a (V : X₁.Opens)
              ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hPU').hom s := rfl
      rw [hEq]
      exact h0
    have hkerι : Scheme.Hom.ker (Blowup.strictTransform π Z j.ker).subschemeι
        ≤ Scheme.Hom.ker a := by
      rwa [Scheme.IdealSheafData.ker_subschemeι]
    have hbι : AlgebraicGeometry.IsClosedImmersion.lift
        (Blowup.strictTransform π Z j.ker).subschemeι a hkerι
        ≫ (Blowup.strictTransform π Z j.ker).subschemeι = a :=
      AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
    refine ⟨AlgebraicGeometry.IsClosedImmersion.lift
      (Blowup.strictTransform π Z j.ker).subschemeι a hkerι, ?_, ?_⟩
    · have hfac : (AlgebraicGeometry.IsClosedImmersion.lift
          (Blowup.strictTransform π Z j.ker).subschemeι a hkerι
          ≫ strictTransformLiftOfClosedImmersion j π Z) ≫ j = g ≫ j := by
        rw [Category.assoc, strictTransformLiftOfClosedImmersion_comp, ← Category.assoc, hbι, hacomp]
      exact (cancel_mono j).mp hfac
    · intro y hy
      have h1 : (y ≫ (Blowup.strictTransform π Z j.ker).subschemeι) ≫ π = g ≫ j := by
        rw [Category.assoc, ← strictTransformLiftOfClosedImmersion_comp, ← Category.assoc, hy]
      have h2 : ((AlgebraicGeometry.IsClosedImmersion.lift
          (Blowup.strictTransform π Z j.ker).subschemeι a hkerι)
          ≫ (Blowup.strictTransform π Z j.ker).subschemeι) ≫ π = g ≫ j := by
        rw [hbι, hacomp]
      have h3 := h.hom_ext_of_comp_eq hECg h1 h2
      exact (cancel_mono (Blowup.strictTransform π Z j.ker).subschemeι).mp h3


end

theorem isLocallyNoetherian_of_isBlowupAlongIdealSheaf {X X₁ : Scheme.{u}}
    [IsLocallyNoetherian X] (π : X₁ ⟶ X) (Z : X.IdealSheafData)
    (h : Blowup.IsBlowupAlongIdealSheaf π Z) : IsLocallyNoetherian X₁ := by
  have : IsProper π := Blowup.blowupIsProper X X₁ π Z h
  exact AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian π

theorem strictTransformIsBlowupOfClosedSubscheme : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u} := by
  intro X X₁ S hX j hj π Z hπ _
  have := hX
  have := hj
  have := isLocallyNoetherian_of_isBlowupAlongIdealSheaf π Z hπ
  exact ⟨strictTransformLiftOfClosedImmersion j π Z, strictTransformLiftOfClosedImmersion_comp j π Z,
    isBlowupAlongIdealSheaf_strictTransformLiftOfClosedImmersion j π Z hπ⟩

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange
section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

section
namespace FunctorialResolution.EmbeddedResolution

noncomputable def saturationByPowers {A : Type*} [CommRing A] (J : Ideal A) (a : A) : Ideal A :=
  _root_.UpperTheory.Reformulated.B.SaturationByPowers.saturationByPowers J a

theorem mem_saturationByPowers_iff {A : Type*} [CommRing A] (J : Ideal A) (a x : A) :
    x ∈ saturationByPowers J a ↔ ∃ n : ℕ, a ^ n * x ∈ J := Iff.rfl

section
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

private theorem map_saturationByPowers_le_consolidated233 (J : Ideal A) (a : A) :
    (saturationByPowers J a).map (algebraMap A B) ≤
      saturationByPowers (J.map (algebraMap A B)) (algebraMap A B a) := by
  rw [Ideal.map_le_iff_le_comap]
  rintro x ⟨n, hn⟩
  rw [Ideal.mem_comap, mem_saturationByPowers_iff]
  refine ⟨n, ?_⟩
  have h := Ideal.mem_map_of_mem (algebraMap A B) hn
  rwa [map_mul, map_pow] at h

theorem map_saturationByPowers_of_flat [Module.Flat A B] (J : Ideal A) (a : A) :
    (saturationByPowers J a).map (algebraMap A B) =
      saturationByPowers (J.map (algebraMap A B)) (algebraMap A B a) := by
  refine le_antisymm (map_saturationByPowers_le_consolidated233 J a) ?_
  rintro y ⟨n, hy⟩
  obtain ⟨u, hu⟩ : ∃ u : A →ₗ[A] (A ⧸ J), u = J.mkQ ∘ₗ LinearMap.lsmul A A (a ^ n) := ⟨_, rfl⟩
  have hker : ∀ c : A, u c = 0 ↔ a ^ n * c ∈ J := by
    intro c
    rw [hu, LinearMap.comp_apply, LinearMap.lsmul_apply, Submodule.mkQ_apply, smul_eq_mul,
      Submodule.Quotient.mk_eq_zero]
  have hex : Function.Exact (LinearMap.ker u).subtype u := by
    intro c
    constructor
    · intro hc
      exact ⟨⟨c, hc⟩, rfl⟩
    · rintro ⟨⟨c, hc⟩, rfl⟩
      exact hc
  have hflat : Function.Exact (LinearMap.lTensor B (LinearMap.ker u).subtype)
      (LinearMap.lTensor B u) := Module.Flat.lTensor_exact B hex
  have key : LinearMap.lTensor B u (y ⊗ₜ[A] (1 : A)) = 0 := by
    have hmapJ : (Ideal.map (algebraMap A B) J : Ideal B)
        = Ideal.span (⇑(algebraMap A B) '' (J : Set A)) := rfl
    rw [hmapJ] at hy
    obtain ⟨k, cf, gg, hsum⟩ := Submodule.mem_span_set'.1 hy
    have hgg : ∀ i, ∃ c : A, c ∈ J ∧ algebraMap A B c = (gg i : B) := by
      intro i
      obtain ⟨c, hc1, hc2⟩ := (gg i).2
      exact ⟨c, hc1, hc2⟩
    choose c hcJ hcmap using hgg
    have e1 : LinearMap.lTensor B u (y ⊗ₜ[A] (1 : A)) = y ⊗ₜ[A] (J.mkQ (a ^ n)) := by
      rw [LinearMap.lTensor_tmul, hu]
      simp
    have e2 : (J.mkQ (a ^ n) : A ⧸ J) = (a ^ n) • (J.mkQ (1 : A)) := by
      rw [← map_smul]
      simp
    have e3 : algebraMap A B (a ^ n) * y = ∑ i, c i • cf i := by
      rw [map_pow, ← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hcmap i, smul_eq_mul, Algebra.smul_def]
      ring
    rw [e1, e2, ← TensorProduct.smul_tmul, Algebra.smul_def, e3, TensorProduct.sum_tmul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [TensorProduct.smul_tmul]
    have hz : (c i) • (J.mkQ (1 : A)) = 0 := by
      have hz1 : (c i) • (J.mkQ (1 : A)) = J.mkQ (c i) := by
        rw [← map_smul, smul_eq_mul, mul_one]
      rw [hz1, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hcJ i
    rw [hz, TensorProduct.tmul_zero]
  obtain ⟨w, hw⟩ := (hflat (y ⊗ₜ[A] (1 : A))).1 key
  have main : ∀ z : TensorProduct A B (LinearMap.ker u),
      TensorProduct.rid A B (LinearMap.lTensor B (LinearMap.ker u).subtype z) ∈
        (saturationByPowers J a).map (algebraMap A B) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b cc =>
        have hcc : (cc : A) ∈ saturationByPowers J a := ⟨n, (hker _).1 cc.2⟩
        have h2 : algebraMap A B (cc : A) * b ∈ (saturationByPowers J a).map (algebraMap A B) :=
          Ideal.mul_mem_right b _ (Ideal.mem_map_of_mem (algebraMap A B) hcc)
        simpa [Algebra.smul_def] using h2
    | add z₁ z₂ h₁ h₂ =>
        rw [map_add, map_add]
        exact Ideal.add_mem _ h₁ h₂
  have hy2 : y = TensorProduct.rid A B (LinearMap.lTensor B (LinearMap.ker u).subtype w) := by
    rw [hw]
    simp
  rw [hy2]
  exact main w

private theorem exists_pow_mul_mem_of_mem_map_away_consolidated233 (f : A) [IsLocalization.Away f B] (I : Ideal A) (x : A)
    (hx : algebraMap A B x ∈ I.map (algebraMap A B)) : ∃ n : ℕ, f ^ n * x ∈ I := by
  rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) B] at hx
  obtain ⟨⟨i, m⟩, hxe⟩ := hx
  obtain ⟨p, hp⟩ := m.2
  have hp' : f ^ p = (m : A) := hp
  have h2 : algebraMap A B (x * (m : A)) = algebraMap A B (i : A) := by
    rw [map_mul]
    exact hxe
  obtain ⟨cc, hcc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers f) B).1 h2
  obtain ⟨q, hq⟩ := cc.2
  have hq' : f ^ q = (cc : A) := hq
  refine ⟨q + p, ?_⟩
  have h3 : f ^ (q + p) * x = (cc : A) * (x * (m : A)) := by
    rw [pow_add, hp', hq']; ring
  rw [h3, hcc]
  exact I.mul_mem_left _ i.2


end

section
variable {X : Scheme.{u}}

private theorem exists_pow_mul_mem_of_mem_map_basicOpen_consolidated233 (U : X.affineOpens)
    (f : Γ(X, U.1)) (I : Ideal Γ(X, U.1)) (x : Γ(X, U.1))
    (hx : (CommRingCat.Hom.hom (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)) x ∈
      Ideal.map (CommRingCat.Hom.hom (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)) I) :
    ∃ n : ℕ, f ^ n * x ∈ I := by
  have := U.2.isLocalization_basicOpen f
  exact exists_pow_mul_mem_of_mem_map_away_consolidated233 (A := Γ(X, U.1)) (B := Γ(X, X.basicOpen f)) f I x hx

private theorem span_eq_top_of_basicOpen_cover_consolidated233 (U : X.Opens)
    (hU : IsAffineOpen U) (s : Set Γ(X, U))
    (hcov : ∀ y : X, y ∈ U → ∃ f ∈ s, y ∈ X.basicOpen f) :
    Ideal.span s = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
  have hmp : m.IsPrime := hm.isPrime
  have hy : (IsAffineOpen.fromSpec hU).base ⟨m, hmp⟩ ∈ U := by
    have hr : (IsAffineOpen.fromSpec hU).base ⟨m, hmp⟩ ∈
        Set.range (IsAffineOpen.fromSpec hU).base := Set.mem_range_self _
    rwa [IsAffineOpen.range_fromSpec] at hr
  obtain ⟨f, hfs, hf⟩ := hcov _ hy
  have h1 : (⟨m, hmp⟩ : PrimeSpectrum Γ(X, U)) ∈
      (IsAffineOpen.fromSpec hU) ⁻¹ᵁ X.basicOpen f := hf
  rw [IsAffineOpen.fromSpec_preimage_basicOpen hU f] at h1
  exact ((PrimeSpectrum.mem_basicOpen f _).1 h1) (hsm (Ideal.subset_span hfs))

private theorem ideal_eq_of_ideal_basicOpen_eq_of_span_eq_top_consolidated233 (I J : X.IdealSheafData)
    (U : X.affineOpens) (s : Set Γ(X, U.1)) (hs : Ideal.span s = ⊤)
    (h : ∀ f ∈ s, I.ideal (X.affineBasicOpen f) = J.ideal (X.affineBasicOpen f)) :
    I.ideal U = J.ideal U := by
  have key : ∀ P Q : X.IdealSheafData,
      (∀ f ∈ s, P.ideal (X.affineBasicOpen f) = Q.ideal (X.affineBasicOpen f)) →
      P.ideal U ≤ Q.ideal U := by
    intro P Q hPQ x hx
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ s hs x ?_
    rintro ⟨f, hf⟩
    have h1 : (CommRingCat.Hom.hom (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)) x ∈
        Ideal.map (CommRingCat.Hom.hom (X.presheaf.map (homOfLE (X.basicOpen_le f)).op))
          (Q.ideal U) := by
      rw [Q.2 U f, ← hPQ f hf, ← P.2 U f]
      exact Ideal.mem_map_of_mem _ hx
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_of_mem_map_basicOpen_consolidated233 U f (Q.ideal U) x h1
    exact ⟨m, by simpa [smul_eq_mul] using hm⟩
  exact le_antisymm (key I J h) (key J I fun f hf => (h f hf).symm)


end

section
variable {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) [Flat g] (F T : Y.IdealSheafData)

private theorem ideal_comap_saturation_of_ideal_eq_span_singleton_consolidated233 [QuasiCompact (saturationι F T)]
    [QuasiCompact (saturationι (F.comap g) (T.comap g))]
    (U : Y.affineOpens) (V : Y'.affineOpens)
    (e : (V : Y'.Opens) ≤ (TopologicalSpace.Opens.map g.base).obj (U : Y.Opens))
    (t : Γ(Y, U.1)) (ht : F.ideal U = Ideal.span {t}) :
    ((saturation F T).comap g).ideal V = (saturation (F.comap g) (T.comap g)).ideal V := by
  let _ : Algebra Γ(Y, U.1) Γ(Y', V.1) := (CommRingCat.Hom.hom (g.appLE U.1 V.1 e)).toAlgebra
  have halg : algebraMap Γ(Y, U.1) Γ(Y', V.1) = CommRingCat.Hom.hom (g.appLE U.1 V.1 e) := rfl
  have : Module.Flat Γ(Y, U.1) Γ(Y', V.1) :=
    (inferInstance : Flat g).1 U.2 V.2 e
  have h1 : ((saturation F T).comap g).ideal V
      = Ideal.map (algebraMap Γ(Y, U.1) Γ(Y', V.1)) ((saturation F T).ideal U) := by
    rw [halg]
    exact Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ g U V e
  have h3 : (T.comap g).ideal V
      = Ideal.map (algebraMap Γ(Y, U.1) Γ(Y', V.1)) (T.ideal U) := by
    rw [halg]
    exact Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ g U V e
  have h2 : (saturation F T).ideal U = saturationByPowers (T.ideal U) t := by
    ext w
    rw [mem_saturationByPowers_iff]
    exact mem_saturation_ideal_iff F T U t ht w
  have h4 : (F.comap g).ideal V = Ideal.span {algebraMap Γ(Y, U.1) Γ(Y', V.1) t} := by
    rw [halg]
    have hh := Scheme.IdealSheafData.comap_ideal_eq_span_image F g U V e {t} ht
    simpa using hh
  have h5 : (saturation (F.comap g) (T.comap g)).ideal V
      = saturationByPowers ((T.comap g).ideal V) (algebraMap Γ(Y, U.1) Γ(Y', V.1) t) := by
    ext w
    rw [mem_saturationByPowers_iff]
    exact mem_saturation_ideal_iff (F.comap g) (T.comap g) V _ h4 w
  rw [h1, h2, h5, h3]
  exact map_saturationByPowers_of_flat (T.ideal U) t

theorem comap_saturation_of_flat (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F)
    [QuasiCompact (saturationι F T)]
    [QuasiCompact (saturationι (F.comap g) (T.comap g))] :
    (saturation F T).comap g = saturation (F.comap g) (T.comap g) := by
  classical
  refine Scheme.IdealSheafData.ext (funext fun V => ?_)
  refine ideal_eq_of_ideal_basicOpen_eq_of_span_eq_top_consolidated233 _ _ V
    {f : Γ(Y', V.1) | ∃ (U : Y.affineOpens) (t : Γ(Y, U.1)), F.ideal U = Ideal.span {t} ∧
      Y'.basicOpen f ≤ (TopologicalSpace.Opens.map g.base).obj U.1} ?_ ?_
  · refine span_eq_top_of_basicOpen_cover_consolidated233 V.1 V.2 _ ?_
    intro y hy
    obtain ⟨U, t, hUmem, -, ht⟩ := hF (g.base y)
    obtain ⟨f, hf1, hf2⟩ := IsAffineOpen.exists_basicOpen_le V.2
      (⟨y, ⟨hy, hUmem⟩⟩ : (V.1 ⊓ (TopologicalSpace.Opens.map g.base).obj U.1 : Y'.Opens)) hy
    exact ⟨f, ⟨U, t, ht, le_trans hf1 inf_le_right⟩, hf2⟩
  · rintro f ⟨U, t, ht, hle⟩
    exact ideal_comap_saturation_of_ideal_eq_span_singleton_consolidated233 g F T U (Y'.affineBasicOpen f) hle t ht


end

section
variable {X X₁ X' X₁' : Scheme.{u}} (π : X₁ ⟶ X) (g : X' ⟶ X) (π' : X₁' ⟶ X') (g₁ : X₁' ⟶ X₁) [Flat g]

theorem comap_strictTransform_of_flat (hsq : IsPullback g₁ π' π g)
    (Z D : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    [QuasiCompact (strictTransformι π Z D)]
    [QuasiCompact (strictTransformι π' (Z.comap g) (D.comap g))] :
    (Blowup.strictTransform π Z D).comap g₁ = Blowup.strictTransform π' (Z.comap g) (D.comap g) := by
  have hZ : (Z.comap π).comap g₁ = (Z.comap g).comap π' := by
    rw [← Scheme.IdealSheafData.comap_comp, hsq.w, Scheme.IdealSheafData.comap_comp]
  have hD : (D.comap π).comap g₁ = (D.comap g).comap π' := by
    rw [← Scheme.IdealSheafData.comap_comp, hsq.w, Scheme.IdealSheafData.comap_comp]
  have : Flat g₁ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat)
      hsq.flip inferInstance
  have i1 : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    inferInstanceAs (QuasiCompact (strictTransformι π Z D))
  have i2 : QuasiCompact (saturationι ((Z.comap π).comap g₁) ((D.comap π).comap g₁)) := by
    rw [hZ, hD]
    exact inferInstanceAs (QuasiCompact (strictTransformι π' (Z.comap g) (D.comap g)))
  have h := comap_saturation_of_flat g₁ (Z.comap π) (D.comap π) hπ.1
  simp only [strictTransform_eq_saturation]
  rw [h, hZ, hD]

theorem comap_strictTransform_of_flat_of_isLocallyNoetherian [IsLocallyNoetherian X₁] [IsLocallyNoetherian X₁']
    (hsq : IsPullback g₁ π' π g)
    (Z D : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    (Blowup.strictTransform π Z D).comap g₁ = Blowup.strictTransform π' (Z.comap g) (D.comap g) := by
  have := FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian π Z D
  have := FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian π' (Z.comap g) (D.comap g)
  exact comap_strictTransform_of_flat π g π' g₁ hsq Z D hπ


end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
section

open CategoryTheory AlgebraicGeometry

section
namespace FunctorialResolution.EmbeddedResolution

namespace BlowupChart

variable {X X₁ : Scheme.{u}} {k : Type u} [Field k]
  {p : X ⟶ Spec (CommRingCat.of k)} {π : X₁ ⟶ X} {U : X.Opens} {m : ℕ}
  {c : EtaleChart p U m} {S : Finset (Fin m)} {s : Fin m}

private theorem comp_hom_apply_consolidated246 {R₁ R₂ R₃ : CommRingCat.{u}} (a : R₁ ⟶ R₂)
    (b : R₂ ⟶ R₃) (x : R₁) : (a ≫ b).hom x = b.hom (a.hom x) := rfl

private theorem comp_appTop_apply_consolidated246 {A B C : Scheme.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (t : Γ(C, ⊤)) :
    ((φ ≫ ψ).appTop).hom t = (φ.appTop).hom ((ψ.appTop).hom t) := rfl

section
variable {T : Type u} [TopologicalSpace T] (F : (TopologicalSpace.Opens T)ᵒᵖ ⥤ CommRingCat.{u})

private theorem presheaf_map_eq_consolidated246 {A B : (TopologicalSpace.Opens T)ᵒᵖ} (α β : A ⟶ B) : F.map α = F.map β := by
  rw [Quiver.Hom.unop_inj (Subsingleton.elim α.unop β.unop)]

private theorem presheaf_map_comp_eq_consolidated246 {A B C : (TopologicalSpace.Opens T)ᵒᵖ} (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) :
    F.map a ≫ F.map b = F.map c := by
  rw [← F.map_comp]
  exact presheaf_map_eq_consolidated246 F _ c


end

private theorem top_le_ι_preimage_consolidated246 {Y : Scheme.{u}} (W : Y.Opens) :
    (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W := by
  intro x _
  exact x.2

private theorem top_le_preimage_top_consolidated246 {Y Y₁ : Scheme.{u}} (g : Y₁ ⟶ Y) :
    (⊤ : Y₁.Opens) ≤ g ⁻¹ᵁ (⊤ : Y.Opens) := by
  simp

private theorem topIso_inv_eq_ι_appLE_consolidated246 {Y : Scheme.{u}} (W : Y.Opens) :
    W.topIso.inv = W.ι.appLE W ⊤ (top_le_ι_preimage_consolidated246 W) := by
  simp [Scheme.Hom.appLE]
  exact (presheaf_map_comp_eq_consolidated246 Y.presheaf _ _ _).symm

private theorem appLE_congr_consolidated246 {Y Y₁ : Scheme.{u}} (g₁ g₂ : Y₁ ⟶ Y) (h : g₁ = g₂)
    (W : Y.Opens) (V : Y₁.Opens) (e₁ : V ≤ g₁ ⁻¹ᵁ W) (e₂ : V ≤ g₂ ⁻¹ᵁ W) :
    g₁.appLE W V e₁ = g₂.appLE W V e₂ := by
  subst h
  rfl

section
variable {Y Y₁ : Scheme.{u}} (f : Y₁ ⟶ Y) (W : Y.Opens) (V : Y₁.Opens) (hV : V ≤ f ⁻¹ᵁ W)

private theorem appLE_topIso_inv_comp_consolidated246 :
    f.appLE W V hV ≫ V.topIso.inv = W.topIso.inv ≫ (f.resLE W V hV).appTop := by
  have happ : (f.resLE W V hV).appTop
      = (f.resLE W V hV).appLE ⊤ ⊤ (top_le_preimage_top_consolidated246 (f.resLE W V hV)) :=
    (Scheme.Hom.appLE_eq_app (f.resLE W V hV)).symm
  rw [topIso_inv_eq_ι_appLE_consolidated246, topIso_inv_eq_ι_appLE_consolidated246, happ,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact appLE_congr_consolidated246 (V.ι ≫ f) (f.resLE W V hV ≫ W.ι) (by simp) W ⊤ _ _

private theorem topIso_hom_comp_appLE_consolidated246 :
    W.topIso.hom ≫ f.appLE W V hV = (f.resLE W V hV).appTop ≫ V.topIso.hom := by
  have h := appLE_topIso_inv_comp_consolidated246 f W V hV
  calc W.topIso.hom ≫ f.appLE W V hV
      = W.topIso.hom ≫ (f.appLE W V hV ≫ V.topIso.inv) ≫ V.topIso.hom := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = W.topIso.hom ≫ (W.topIso.inv ≫ (f.resLE W V hV).appTop) ≫ V.topIso.hom := by rw [h]
    _ = (f.resLE W V hV).appTop ≫ V.topIso.hom := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem appLE_topIso_hom_apply_consolidated246 (y : Γ(W.toScheme, ⊤)) :
    (f.appLE W V hV).hom (W.topIso.hom.hom y)
      = V.topIso.hom.hom ((f.resLE W V hV).appTop.hom y) := by
  have h2 : (W.topIso.hom ≫ f.appLE W V hV).hom y
      = ((f.resLE W V hV).appTop ≫ V.topIso.hom).hom y := by
    rw [topIso_hom_comp_appLE_consolidated246 f W V hV]
  rw [comp_hom_apply_consolidated246, comp_hom_apply_consolidated246] at h2
  exact h2

private theorem topIso_inv_appLE_apply_consolidated246 (a : Γ(Y, W)) :
    V.topIso.inv.hom ((f.appLE W V hV).hom a)
      = ((f.resLE W V hV).appTop).hom (W.topIso.inv.hom a) := by
  have h := appLE_topIso_inv_comp_consolidated246 f W V hV
  have h2 := congrArg (fun φ : Γ(Y, W) ⟶ Γ(V.toScheme, ⊤) => CommRingCat.Hom.hom φ a) h
  rw [comp_hom_apply_consolidated246, comp_hom_apply_consolidated246] at h2
  exact h2


end

section
variable (B : BlowupChart π c S s)

theorem restrictIdeal_comap (D : X.IdealSheafData) :
    restrictIdeal (D.comap π) B.domain =
      (restrictIdeal D U).comap (π.resLE U B.domain B.domain_le) := by
  rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι,
    ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    AlgebraicGeometry.Scheme.Hom.resLE_comp_ι]

theorem restrictIdeal_exceptionalIdeal (Z : X.IdealSheafData) (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S) :
    restrictIdeal (Blowup.exceptionalIdeal π Z) B.domain = B.chart.coordIdeal {s} := by
  have h1 := restrictIdeal_comap B Z
  rw [Blowup.exceptionalIdeal_eq_comap, h1, hZ]
  exact comap_coordIdeal_center c B.chart (π.resLE U B.domain B.domain_le) B.comm hs

theorem restrictIdeal_comap_coordIdeal_of_mem (D : X.IdealSheafData) (j : Fin m) (hj : j ∈ S) (hjs : j ≠ s)
    (hD : restrictIdeal D U = c.coordIdeal {j}) :
    restrictIdeal (D.comap π) B.domain =
      B.chart.coordIdeal {j} * B.chart.coordIdeal {s} := by
  rw [restrictIdeal_comap B D, hD]
  exact comap_coordIdeal_singleton_of_mem c B.chart
    (π.resLE U B.domain B.domain_le) B.comm j hj hjs

theorem restrictIdeal_comap_coordIdeal_self (D : X.IdealSheafData) (hD : restrictIdeal D U = c.coordIdeal {s}) :
    restrictIdeal (D.comap π) B.domain = B.chart.coordIdeal {s} := by
  rw [restrictIdeal_comap B D, hD]
  exact comap_coordIdeal_singleton_self c B.chart
    (π.resLE U B.domain B.domain_le) B.comm

theorem restrictIdeal_comap_coordIdeal_of_not_mem (D : X.IdealSheafData) (j : Fin m) (hj : j ∉ S)
    (hD : restrictIdeal D U = c.coordIdeal {j}) :
    restrictIdeal (D.comap π) B.domain = B.chart.coordIdeal {j} := by
  rw [restrictIdeal_comap B D, hD]
  exact comap_coordIdeal_singleton_of_notMem c B.chart
    (π.resLE U B.domain B.domain_le) B.comm j hj

theorem restrictIdeal_comap_top (D : X.IdealSheafData) (hD : restrictIdeal D U = ⊤) :
    restrictIdeal (D.comap π) B.domain = ⊤ := by
  rw [restrictIdeal_comap B D, hD, Scheme.IdealSheafData.comap_top]

theorem appLE_coord_of_mem (i : Fin m)
    (hi : i ∈ S) (his : i ≠ s) :
    (π.appLE U B.domain B.domain_le).hom (c.coord i) =
      B.chart.coord i * B.chart.coord s := by
  have h0 : ((B.chart.map ≫ coordBlowupSubstMap k m S s).appTop).hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i : ULift.{u} (Fin m)))
      = ((π.resLE U B.domain B.domain_le ≫ c.map).appTop).hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i : ULift.{u} (Fin m))) :=
    congrArg (fun φ : B.domain.toScheme ⟶ affineSpaceFin k m =>
      (φ.appTop).hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i : ULift.{u} (Fin m)))) B.comm
  rw [comp_appTop_apply_consolidated246, comp_appTop_apply_consolidated246,
    coordBlowupSubstMap_appTop_coord_of_mem k m S s i hi his, map_mul] at h0
  have hkey := h0.symm
  rw [EtaleChart.coord_def c i, EtaleChart.coord_def B.chart i, EtaleChart.coord_def B.chart s,
    appLE_topIso_hom_apply_consolidated246 π U B.domain B.domain_le, hkey, map_mul]

theorem appLE_coord_self :
    (π.appLE U B.domain B.domain_le).hom (c.coord s) = B.chart.coord s := by
  have h1 : (coordBlowupSubstMap k m S s).appTop ≫ B.chart.map.appTop
      = c.map.appTop ≫ (π.resLE U B.domain B.domain_le).appTop := by
    refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
    exact congrArg (fun φ : B.domain.toScheme ⟶ affineSpaceFin k m => (φ.appTop).hom z) B.comm
  have h2 : B.chart.map.appTop.hom
        ((coordBlowupSubstMap k m S s).appTop.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s : ULift.{u} (Fin m))))
      = (π.resLE U B.domain B.domain_le).appTop.hom
          (c.map.appTop.hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s : ULift.{u} (Fin m)))) := by
    have h3 : ((coordBlowupSubstMap k m S s).appTop ≫ B.chart.map.appTop).hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s : ULift.{u} (Fin m)))
        = (c.map.appTop ≫ (π.resLE U B.domain B.domain_le).appTop).hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s : ULift.{u} (Fin m))) := by
      rw [h1]
    exact h3
  rw [coordBlowupSubstMap_appTop_coord_self] at h2
  rw [EtaleChart.coord_def c s, EtaleChart.coord_def B.chart s, h2]
  exact appLE_topIso_hom_apply_consolidated246 π U B.domain B.domain_le _

theorem appLE_coord_of_not_mem (i : Fin m) (hi : i ∉ S) :
    (π.appLE U B.domain B.domain_le).hom (c.coord i) = B.chart.coord i := by
  have hcomm : (coordBlowupSubstMap k m S s).appTop ≫ (B.chart.map).appTop
      = (c.map).appTop ≫ (π.resLE U B.domain B.domain_le).appTop := by
    refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
    exact congrArg (fun φ : B.domain.toScheme ⟶ affineSpaceFin k m => (φ.appTop).hom z) B.comm
  have hx : (B.chart.map).appTop.hom
        ((coordBlowupSubstMap k m S s).appTop.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i : ULift.{u} (Fin m))))
      = (π.resLE U B.domain B.domain_le).appTop.hom
        ((c.map).appTop.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i : ULift.{u} (Fin m)))) := by
    have h2 : ((coordBlowupSubstMap k m S s).appTop ≫ (B.chart.map).appTop).hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i : ULift.{u} (Fin m)))
        = ((c.map).appTop ≫ (π.resLE U B.domain B.domain_le).appTop).hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i : ULift.{u} (Fin m))) := by
      rw [hcomm]
    rw [comp_hom_apply_consolidated246, comp_hom_apply_consolidated246] at h2
    exact h2
  rw [coordBlowupSubstMap_appTop_coord_of_notMem k m S s i hi] at hx
  simp only [EtaleChart.coord_def]
  rw [hx]
  exact appLE_topIso_hom_apply_consolidated246 π U B.domain B.domain_le _

theorem appLE_coord (i : Fin m) :
    (π.appLE U B.domain B.domain_le).hom (c.coord i) =
      if i ∈ S ∧ i ≠ s then B.chart.coord i * B.chart.coord s else B.chart.coord i := by
  by_cases h : i ∈ S ∧ i ≠ s
  · rw [if_pos h]
    exact B.appLE_coord_of_mem i h.1 h.2
  · rw [if_neg h]
    by_cases hi : i ∈ S
    · have hieq : i = s := by
        by_contra hne
        exact h ⟨hi, hne⟩
      rw [hieq]
      exact B.appLE_coord_self
    · exact B.appLE_coord_of_not_mem i hi


end

def coordEvalHom (B : BlowupChart π c S s) :
    MvPolynomial (ULift.{u} (Fin m)) Γ(X, U) →+* Γ(X₁, B.domain) :=
  MvPolynomial.eval₂Hom (π.appLE U B.domain B.domain_le).hom
    (fun i : ULift.{u} (Fin m) => B.chart.coord i.down)

section
variable (B : BlowupChart π c S s)

theorem coordEvalHom_C (a : Γ(X, U)) :
    B.coordEvalHom (MvPolynomial.C a) = (π.appLE U B.domain B.domain_le).hom a := by
  simp [coordEvalHom]

theorem coordEvalHom_X (i : Fin m) :
    B.coordEvalHom (MvPolynomial.X (ULift.up i : ULift.{u} (Fin m))) = B.chart.coord i := by
  simp [coordEvalHom]


end

def coordRelation (_B : BlowupChart π c S s) (i : Fin m) :
    MvPolynomial (ULift.{u} (Fin m)) Γ(X, U) :=
  (if i ∈ S ∧ i ≠ s then
      MvPolynomial.X (ULift.up i : ULift.{u} (Fin m)) *
        MvPolynomial.X (ULift.up s : ULift.{u} (Fin m))
    else MvPolynomial.X (ULift.up i : ULift.{u} (Fin m))) - MvPolynomial.C (c.coord i)

section
variable (B : BlowupChart π c S s)

theorem coordRelation_def (i : Fin m) :
    B.coordRelation i =
      (if i ∈ S ∧ i ≠ s then
          MvPolynomial.X (ULift.up i : ULift.{u} (Fin m)) *
            MvPolynomial.X (ULift.up s : ULift.{u} (Fin m))
        else MvPolynomial.X (ULift.up i : ULift.{u} (Fin m))) -
        MvPolynomial.C (c.coord i) := rfl

theorem coordEvalHom_coordRelation (i : Fin m) :
    B.coordEvalHom (B.coordRelation i) = 0 := by
  rw [coordRelation_def]
  by_cases h : i ∈ S ∧ i ≠ s
  · rw [if_pos h, map_sub, map_mul, coordEvalHom_X, coordEvalHom_X, coordEvalHom_C, B.appLE_coord i,
      if_pos h, sub_self]
  · rw [if_neg h, map_sub, coordEvalHom_X, coordEvalHom_C, B.appLE_coord i, if_neg h, sub_self]

theorem coordEvalHom_eq_zero_of_mem_span (a : MvPolynomial (ULift.{u} (Fin m)) Γ(X, U))
    (ha : a ∈ Ideal.span (Set.range B.coordRelation)) : B.coordEvalHom a = 0 := by
  have h : Ideal.span (Set.range B.coordRelation) ≤ RingHom.ker B.coordEvalHom := by
    rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    exact RingHom.mem_ker.mpr (B.coordEvalHom_coordRelation i)
  exact RingHom.mem_ker.mp (h ha)


end

def coordEvalQuotientHom (B : BlowupChart π c S s) :
    (MvPolynomial (ULift.{u} (Fin m)) Γ(X, U) ⧸ Ideal.span (Set.range B.coordRelation)) →+*
      Γ(X₁, B.domain) :=
  Ideal.Quotient.lift (Ideal.span (Set.range B.coordRelation)) B.coordEvalHom
    B.coordEvalHom_eq_zero_of_mem_span

theorem coordEvalQuotientHom_mk (B : BlowupChart π c S s)
    (a : MvPolynomial (ULift.{u} (Fin m)) Γ(X, U)) :
    B.coordEvalQuotientHom (Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation)) a) = B.coordEvalHom a := rfl

section
variable {R T : CommRingCat.{u}} (e : R ≅ T)

private theorem iso_inv_hom_apply_consolidated246 (x : R) :
    e.inv.hom (e.hom.hom x) = x := by
  have h := congrArg (fun φ : R ⟶ R => CommRingCat.Hom.hom φ x) e.hom_inv_id
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id,
    RingHom.id_apply] using h

private theorem iso_hom_inv_apply_consolidated246 (x : T) :
    e.hom.hom (e.inv.hom x) = x := by
  have h := congrArg (fun φ : T ⟶ T => CommRingCat.Hom.hom φ x) e.inv_hom_id
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id,
    RingHom.id_apply] using h


end

private def mvPolynomialIsoGlobalSectionsAffineSpace_consolidated246 (k : Type u) [Field k] (m : ℕ) :
    CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k) ≅ Γ(affineSpaceFin k m, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).symm ≪≫
    Scheme.Γ.mapIso (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).op

section
variable (k : Type u) [Field k] (m : ℕ)

private theorem mvPolynomialIsoGlobalSectionsAffineSpace_hom_apply_consolidated246 (x : MvPolynomial (ULift.{u} (Fin m)) k) :
    (mvPolynomialIsoGlobalSectionsAffineSpace_consolidated246 k m).hom.hom x = affineSpaceGlobalSectionsHom k m x := rfl

private theorem mvPolynomialIsoGlobalSectionsAffineSpace_hom_X_consolidated246 (i : ULift.{u} (Fin m)) :
    (mvPolynomialIsoGlobalSectionsAffineSpace_consolidated246 k m).hom.hom (MvPolynomial.X i)
      = AffineSpace.coord (Spec (CommRingCat.of k)) i := by
  have hcancel : ∀ x : Γ(affineSpaceFin k m, ⊤),
      ((AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop).hom
        (((AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).inv.appTop).hom x) = x := by
    intro x
    exact iso_hom_inv_apply_consolidated246
      (Scheme.Γ.mapIso (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).op) x
  have h := AffineSpace.SpecIso_inv_appTop_coord (CommRingCat.of k) i
  have h2 : (mvPolynomialIsoGlobalSectionsAffineSpace_consolidated246 k m).hom.hom (MvPolynomial.X i)
      = ((AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop).hom
        (((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv).hom
          (MvPolynomial.X i)) := rfl
  rw [h2, ← h, hcancel]

private theorem specIso_hom_comp_map_C_consolidated246 :
    (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k)) =
      affineSpaceFinToSpec k m := by
  have h : (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).inv ≫
      affineSpaceFinToSpec k m =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k)) := by
    simp
  rw [← h, Iso.hom_inv_id_assoc]

private theorem mvPolynomialIsoGlobalSectionsAffineSpace_hom_C_consolidated246 (a : k) :
    (mvPolynomialIsoGlobalSectionsAffineSpace_consolidated246 k m).hom.hom (MvPolynomial.C a)
      = ((affineSpaceFinToSpec k m).appTop).hom
        (((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom a) := by
  have h0 : (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k))).appTop ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop
      = (affineSpaceFinToSpec k m).appTop := by
    refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
    exact congrArg (fun φ : affineSpaceFin k m ⟶ Spec (CommRingCat.of k) =>
      (φ.appTop).hom z) (specIso_hom_comp_map_C_consolidated246 k m)
  have key : (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop
      = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (affineSpaceFinToSpec k m).appTop := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc, h0]
  have e1 : (mvPolynomialIsoGlobalSectionsAffineSpace_consolidated246 k m).hom.hom (MvPolynomial.C a)
      = ((CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k)) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv ≫
            (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop).hom a := rfl
  rw [e1, key]
  rfl

private theorem affineSpaceFin_globalSections_hom_ext_consolidated246 {T : CommRingCat.{u}}
    (u v : Γ(affineSpaceFin k m, ⊤) ⟶ T)
    (hτ : ∀ t : Γ(Spec (CommRingCat.of k), ⊤),
      u.hom (((affineSpaceFinToSpec k m).appTop).hom t)
        = v.hom (((affineSpaceFinToSpec k m).appTop).hom t))
    (hc : ∀ j : Fin m,
      u.hom (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m)))
        = v.hom (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m)))) :
    u = v := by
  have key : ∀ w : MvPolynomial (ULift.{u} (Fin m)) k,
      u.hom ((mvPolynomialIsoGlobalSectionsAffineSpace_consolidated246 k m).hom.hom w) = v.hom ((mvPolynomialIsoGlobalSectionsAffineSpace_consolidated246 k m).hom.hom w) := by
    intro w
    refine MvPolynomial.induction_on
      (motive := fun z : MvPolynomial (ULift.{u} (Fin m)) k =>
        u.hom ((mvPolynomialIsoGlobalSectionsAffineSpace_consolidated246 k m).hom.hom z) = v.hom ((mvPolynomialIsoGlobalSectionsAffineSpace_consolidated246 k m).hom.hom z))
      w (fun a => ?_) (fun q r hq hr => ?_) (fun q i hq => ?_)
    · rw [mvPolynomialIsoGlobalSectionsAffineSpace_hom_C_consolidated246]
      exact hτ _
    · simp only [map_add]
      rw [hq, hr]
    · obtain ⟨j⟩ := i
      simp only [map_mul]
      rw [hq, mvPolynomialIsoGlobalSectionsAffineSpace_hom_X_consolidated246, hc j]
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  have h := key ((mvPolynomialIsoGlobalSectionsAffineSpace_consolidated246 k m).inv.hom z)
  rwa [iso_hom_inv_apply_consolidated246] at h


end

private theorem coordBlowupSubstMap_appTop_affineSpaceFinToSpec_consolidated246 (t : Γ(Spec (CommRingCat.of k), ⊤)) :
    ((coordBlowupSubstMap k m S s).appTop).hom (((affineSpaceFinToSpec k m).appTop).hom t)
      = ((affineSpaceFinToSpec k m).appTop).hom t := by
  have h : ((coordBlowupSubstMap k m S s ≫ affineSpaceFinToSpec k m).appTop).hom t
      = ((affineSpaceFinToSpec k m).appTop).hom t :=
    congrArg (fun φ : affineSpaceFin k m ⟶ Spec (CommRingCat.of k) => (φ.appTop).hom t)
      (coordBlowupSubstMap_comp_affineSpaceFinToSpec k m S s)
  rw [comp_appTop_apply_consolidated246] at h
  exact h

private theorem chart_appTop_coordBlowupSubstMap_apply_consolidated246 (B : BlowupChart π c S s) (z : Γ(affineSpaceFin k m, ⊤)) :
    (B.chart.map.appTop).hom (((coordBlowupSubstMap k m S s).appTop).hom z)
      = ((π.resLE U B.domain B.domain_le).appTop).hom ((c.map.appTop).hom z) := by
  have h : ((B.chart.map ≫ coordBlowupSubstMap k m S s).appTop).hom z
      = ((π.resLE U B.domain B.domain_le ≫ c.map).appTop).hom z :=
    congrArg (fun φ : B.domain.toScheme ⟶ affineSpaceFin k m => (φ.appTop).hom z) B.comm
  rw [comp_appTop_apply_consolidated246, comp_appTop_apply_consolidated246] at h
  exact h

private theorem etaleChart_appTop_affineSpaceFinToSpec_apply_consolidated246 {Y : Scheme.{u}} {q : Y ⟶ Spec (CommRingCat.of k)}
    {W : Y.Opens} (d : EtaleChart q W m) (t : Γ(Spec (CommRingCat.of k), ⊤)) :
    W.topIso.hom.hom ((d.map.appTop).hom (((affineSpaceFinToSpec k m).appTop).hom t))
      = sectionsAlgebraMap k q W (((Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom t) := by
  have ha : affineSpaceGlobalSectionsHom k m
      (MvPolynomial.C (((Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom t))
      = ((affineSpaceFinToSpec k m).appTop).hom t := by
    rw [← mvPolynomialIsoGlobalSectionsAffineSpace_hom_apply_consolidated246 k m, mvPolynomialIsoGlobalSectionsAffineSpace_hom_C_consolidated246, iso_inv_hom_apply_consolidated246]
  rw [← ha]
  exact EtaleChart.coordRingHom_C d _

private def constToCoordRelationQuotient_consolidated246 (B : BlowupChart π c S s) :
    Γ(X, U) →+*
      (MvPolynomial (ULift.{u} (Fin m)) Γ(X, U) ⧸ Ideal.span (Set.range B.coordRelation)) :=
  (Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation))).comp MvPolynomial.C

section
variable (B : BlowupChart π c S s) (y : Γ(X, U))

private theorem constToCoordRelationQuotient_apply_consolidated246 :
    constToCoordRelationQuotient_consolidated246 B y = Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation)) (MvPolynomial.C y) := rfl

private theorem coordEvalQuotientHom_constToCoordRelationQuotient_consolidated246 :
    B.coordEvalQuotientHom (constToCoordRelationQuotient_consolidated246 B y) = (π.appLE U B.domain B.domain_le).hom y := by
  rw [constToCoordRelationQuotient_apply_consolidated246, coordEvalQuotientHom_mk, coordEvalHom_C]


end

private def affineSectionsToCoordRelationQuotient_consolidated246 (B : BlowupChart π c S s) :
    Γ(affineSpaceFin k m, ⊤) ⟶
      CommRingCat.of
        (MvPolynomial (ULift.{u} (Fin m)) Γ(X, U) ⧸ Ideal.span (Set.range B.coordRelation)) :=
  CommRingCat.ofHom
    ((MvPolynomial.eval₂Hom ((constToCoordRelationQuotient_consolidated246 B).comp (sectionsAlgebraMap k p U))
        (fun i : ULift.{u} (Fin m) =>
          Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation)) (MvPolynomial.X i))).comp
      (mvPolynomialIsoGlobalSectionsAffineSpace_consolidated246 k m).inv.hom)

private def openSectionsToCoordRelationQuotient_consolidated246 (B : BlowupChart π c S s) :
    Γ(U.toScheme, ⊤) ⟶
      CommRingCat.of
        (MvPolynomial (ULift.{u} (Fin m)) Γ(X, U) ⧸ Ideal.span (Set.range B.coordRelation)) :=
  CommRingCat.ofHom ((constToCoordRelationQuotient_consolidated246 B).comp (U.topIso.hom.hom))

section
variable (B : BlowupChart π c S s)

private theorem openSectionsToCoordRelationQuotient_apply_consolidated246 (y : Γ(U.toScheme, ⊤)) :
    (openSectionsToCoordRelationQuotient_consolidated246 B).hom y
      = Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation))
        (MvPolynomial.C (U.topIso.hom.hom y)) := rfl

private theorem affineSectionsToCoordRelationQuotient_coord_consolidated246 (j : Fin m) :
    (affineSectionsToCoordRelationQuotient_consolidated246 B).hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m)))
      = Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation))
        (MvPolynomial.X (ULift.up j : ULift.{u} (Fin m))) := by
  have h : (mvPolynomialIsoGlobalSectionsAffineSpace_consolidated246 k m).inv.hom
      (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m)))
      = MvPolynomial.X (ULift.up j : ULift.{u} (Fin m)) := by
    rw [← mvPolynomialIsoGlobalSectionsAffineSpace_hom_X_consolidated246 k m (ULift.up j : ULift.{u} (Fin m)), iso_inv_hom_apply_consolidated246]
  have h2 : (affineSectionsToCoordRelationQuotient_consolidated246 B).hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m)))
      = (MvPolynomial.eval₂Hom ((constToCoordRelationQuotient_consolidated246 B).comp (sectionsAlgebraMap k p U))
          (fun i : ULift.{u} (Fin m) =>
            Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation)) (MvPolynomial.X i)))
        ((mvPolynomialIsoGlobalSectionsAffineSpace_consolidated246 k m).inv.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m)))) := rfl
  rw [h2, h, MvPolynomial.eval₂Hom_X']

private theorem affineSectionsToCoordRelationQuotient_affineSpaceFinToSpec_consolidated246 (t : Γ(Spec (CommRingCat.of k), ⊤)) :
    (affineSectionsToCoordRelationQuotient_consolidated246 B).hom (((affineSpaceFinToSpec k m).appTop).hom t)
      = constToCoordRelationQuotient_consolidated246 B (sectionsAlgebraMap k p U
          (((Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom t)) := by
  have ha : (mvPolynomialIsoGlobalSectionsAffineSpace_consolidated246 k m).hom.hom
      (MvPolynomial.C (((Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom t))
      = ((affineSpaceFinToSpec k m).appTop).hom t := by
    rw [mvPolynomialIsoGlobalSectionsAffineSpace_hom_C_consolidated246, iso_inv_hom_apply_consolidated246]
  have h : (mvPolynomialIsoGlobalSectionsAffineSpace_consolidated246 k m).inv.hom (((affineSpaceFinToSpec k m).appTop).hom t)
      = MvPolynomial.C (((Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom t) := by
    rw [← ha, iso_inv_hom_apply_consolidated246]
  have h2 : (affineSectionsToCoordRelationQuotient_consolidated246 B).hom (((affineSpaceFinToSpec k m).appTop).hom t)
      = (MvPolynomial.eval₂Hom ((constToCoordRelationQuotient_consolidated246 B).comp (sectionsAlgebraMap k p U))
          (fun i : ULift.{u} (Fin m) =>
            Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation)) (MvPolynomial.X i)))
        ((mvPolynomialIsoGlobalSectionsAffineSpace_consolidated246 k m).inv.hom (((affineSpaceFinToSpec k m).appTop).hom t)) := rfl
  rw [h2, h, MvPolynomial.eval₂Hom_C]
  rfl

private theorem openSectionsToCoordRelationQuotient_coord_consolidated246 (j : Fin m) :
    (openSectionsToCoordRelationQuotient_consolidated246 B).hom
        ((c.map.appTop).hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m))))
      = Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation))
        (MvPolynomial.C (c.coord j)) := by
  rw [openSectionsToCoordRelationQuotient_apply_consolidated246, ← EtaleChart.coord_def c j]

private theorem mk_eq_mk_C_coord_consolidated246 (j : Fin m) :
    Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation))
        ((if j ∈ S ∧ j ≠ s then
            MvPolynomial.X (ULift.up j : ULift.{u} (Fin m)) *
              MvPolynomial.X (ULift.up s : ULift.{u} (Fin m))
          else MvPolynomial.X (ULift.up j : ULift.{u} (Fin m))) :
            MvPolynomial (ULift.{u} (Fin m)) Γ(X, U))
      = Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation))
        (MvPolynomial.C (c.coord j)) := by
  have h : Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation)) (B.coordRelation j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
  rw [coordRelation_def, map_sub, sub_eq_zero] at h
  exact h

private theorem appTop_comp_affineSectionsToCoordRelationQuotient_consolidated246 :
    (coordBlowupSubstMap k m S s).appTop ≫ affineSectionsToCoordRelationQuotient_consolidated246 B = c.map.appTop ≫ openSectionsToCoordRelationQuotient_consolidated246 B := by
  refine affineSpaceFin_globalSections_hom_ext_consolidated246 k m _ _ (fun t => ?_) (fun j => ?_)
  · rw [comp_hom_apply_consolidated246, comp_hom_apply_consolidated246, coordBlowupSubstMap_appTop_affineSpaceFinToSpec_consolidated246,
      affineSectionsToCoordRelationQuotient_affineSpaceFinToSpec_consolidated246, openSectionsToCoordRelationQuotient_apply_consolidated246, etaleChart_appTop_affineSpaceFinToSpec_apply_consolidated246 c t]
    rfl
  · rw [comp_hom_apply_consolidated246, comp_hom_apply_consolidated246, openSectionsToCoordRelationQuotient_coord_consolidated246]
    by_cases hjS : j ∈ S
    · by_cases hjs : j = s
      · subst hjs
        rw [coordBlowupSubstMap_appTop_coord_self, affineSectionsToCoordRelationQuotient_coord_consolidated246]
        have hrel := mk_eq_mk_C_coord_consolidated246 B j
        rw [if_neg (by simp)] at hrel
        exact hrel
      · rw [coordBlowupSubstMap_appTop_coord_of_mem k m S s j hjS hjs, map_mul, affineSectionsToCoordRelationQuotient_coord_consolidated246,
          affineSectionsToCoordRelationQuotient_coord_consolidated246, ← map_mul]
        have hrel := mk_eq_mk_C_coord_consolidated246 B j
        rw [if_pos ⟨hjS, hjs⟩] at hrel
        exact hrel
    · rw [coordBlowupSubstMap_appTop_coord_of_notMem k m S s j hjS, affineSectionsToCoordRelationQuotient_coord_consolidated246]
      have hrel := mk_eq_mk_C_coord_consolidated246 B j
      rw [if_neg (by tauto)] at hrel
      exact hrel


end

section
variable (B : BlowupChart π c S s) (hU : IsAffineOpen U) (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map)
include hU hB

private theorem bijective_coordEvalQuotientHom_of_isPullback_consolidated246 :
    Function.Bijective B.coordEvalQuotientHom := by
  have hUaff : IsAffine U.toScheme := hU
  have hPaff : IsAffine (CategoryTheory.Limits.pullback (coordBlowupSubstMap k m S s) c.map) :=
    inferInstance
  have hDaff : IsAffine B.domain.toScheme := IsAffine.of_isIso hB.isoPullback.hom
  have HP : IsPushout (coordBlowupSubstMap k m S s).appTop c.map.appTop B.chart.map.appTop
      (π.resLE U B.domain B.domain_le).appTop :=
    AlgebraicGeometry.isPushout_appTop_of_isPullback hB
  obtain ⟨Δ, hinl, hinr⟩ :
      ∃ Δ : Γ(B.domain.toScheme, ⊤) ⟶
          CommRingCat.of
            (MvPolynomial (ULift.{u} (Fin m)) Γ(X, U) ⧸ Ideal.span (Set.range B.coordRelation)),
        B.chart.map.appTop ≫ Δ = affineSectionsToCoordRelationQuotient_consolidated246 B ∧
          (π.resLE U B.domain B.domain_le).appTop ≫ Δ = openSectionsToCoordRelationQuotient_consolidated246 B :=
    ⟨HP.desc (affineSectionsToCoordRelationQuotient_consolidated246 B) (openSectionsToCoordRelationQuotient_consolidated246 B) (appTop_comp_affineSectionsToCoordRelationQuotient_consolidated246 B),
      HP.inl_desc _ _ _, HP.inr_desc _ _ _⟩
  have hinl' : ∀ z, Δ.hom ((B.chart.map.appTop).hom z) = (affineSectionsToCoordRelationQuotient_consolidated246 B).hom z := by
    intro z
    have h := congrArg (fun φ => CommRingCat.Hom.hom φ z) hinl
    rw [comp_hom_apply_consolidated246] at h
    exact h
  have hinr' : ∀ y, Δ.hom (((π.resLE U B.domain B.domain_le).appTop).hom y)
      = (openSectionsToCoordRelationQuotient_consolidated246 B).hom y := by
    intro y
    have h := congrArg (fun φ => CommRingCat.Hom.hom φ y) hinr
    rw [comp_hom_apply_consolidated246] at h
    exact h
  have hbeta : Δ ≫ CommRingCat.ofHom B.coordEvalQuotientHom = B.domain.topIso.hom := by
    refine HP.hom_ext ?_ ?_
    · rw [← Category.assoc, hinl]
      refine affineSpaceFin_globalSections_hom_ext_consolidated246 k m _ _ (fun t => ?_) (fun j => ?_)
      · rw [comp_hom_apply_consolidated246, comp_hom_apply_consolidated246, affineSectionsToCoordRelationQuotient_affineSpaceFinToSpec_consolidated246,
          ← etaleChart_appTop_affineSpaceFinToSpec_apply_consolidated246 c t, CommRingCat.hom_ofHom, coordEvalQuotientHom_constToCoordRelationQuotient_consolidated246,
          appLE_topIso_hom_apply_consolidated246 π U B.domain B.domain_le,
          ← chart_appTop_coordBlowupSubstMap_apply_consolidated246 B (((affineSpaceFinToSpec k m).appTop).hom t),
          coordBlowupSubstMap_appTop_affineSpaceFinToSpec_consolidated246]
      · rw [comp_hom_apply_consolidated246, comp_hom_apply_consolidated246, affineSectionsToCoordRelationQuotient_coord_consolidated246,
          CommRingCat.hom_ofHom, coordEvalQuotientHom_mk, coordEvalHom_X, EtaleChart.coord_def B.chart j]
    · rw [← Category.assoc, hinr]
      refine CommRingCat.hom_ext (RingHom.ext fun y => ?_)
      rw [comp_hom_apply_consolidated246, comp_hom_apply_consolidated246, CommRingCat.hom_ofHom,
        openSectionsToCoordRelationQuotient_apply_consolidated246, coordEvalQuotientHom_mk, coordEvalHom_C,
        appLE_topIso_hom_apply_consolidated246 π U B.domain B.domain_le]
  have hbeta' : ∀ z, B.coordEvalQuotientHom (Δ.hom z) = B.domain.topIso.hom.hom z := by
    intro z
    have h := congrArg (fun φ => CommRingCat.Hom.hom φ z) hbeta
    rw [comp_hom_apply_consolidated246] at h
    exact h
  have hring : (Δ.hom).comp ((B.domain.topIso.inv.hom).comp B.coordEvalQuotientHom)
      = RingHom.id _ := by
    refine Ideal.Quotient.ringHom_ext ?_
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [coordEvalQuotientHom_mk, coordEvalHom_C, topIso_inv_appLE_apply_consolidated246, hinr', openSectionsToCoordRelationQuotient_apply_consolidated246,
        iso_hom_inv_apply_consolidated246]
    · obtain ⟨j⟩ := i
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [coordEvalQuotientHom_mk, coordEvalHom_X, EtaleChart.coord_def B.chart j, iso_inv_hom_apply_consolidated246,
        hinl', affineSectionsToCoordRelationQuotient_coord_consolidated246]
  have halpha : ∀ q, Δ.hom (B.domain.topIso.inv.hom (B.coordEvalQuotientHom q)) = q := by
    intro q
    have h := RingHom.congr_fun hring q
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  refine ⟨fun x y hxy => ?_, fun y => ⟨Δ.hom (B.domain.topIso.inv.hom y), ?_⟩⟩
  · rw [← halpha x, ← halpha y, hxy]
  · rw [hbeta', iso_hom_inv_apply_consolidated246]

theorem surjective_coordEvalHom :
    Function.Surjective B.coordEvalHom := by
  intro y
  obtain ⟨q, hq⟩ := (bijective_coordEvalQuotientHom_of_isPullback_consolidated246 B hU hB).2 y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨a, hq⟩

theorem bijective_coordEvalQuotientHom :
    Function.Bijective B.coordEvalQuotientHom :=
  bijective_coordEvalQuotientHom_of_isPullback_consolidated246 B hU hB


end

end BlowupChart

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ExceptionalDivisorChart
section

open CategoryTheory AlgebraicGeometry

section
namespace FunctorialResolution.EmbeddedResolution

variable {X X₁ : Scheme.{u}} {k : Type u} [Field k]
  {p : X ⟶ Spec (CommRingCat.of k)} {π : X₁ ⟶ X} {U : X.Opens} {m : ℕ}
  {c : EtaleChart p U m} {S : Finset (Fin m)} {s : Fin m}

section
variable (hU : IsAffineOpen U) (Z : X.IdealSheafData) (hZ : restrictIdeal Z U = c.coordIdeal S) (i : Fin m) (hi : i ∈ S)
include hZ hi

theorem coord_mem_ideal_of_mem :
    c.coord i ∈ Z.ideal ⟨U, hU⟩ := by
  rw [EtaleChart.ideal_eq_span_coord c hU Z S hZ]
  exact Ideal.subset_span (Set.mem_image_of_mem c.coord (Finset.mem_coe.mpr hi))

theorem mk_coord_eq_zero_of_mem :
    (Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)) (c.coord i) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact coord_mem_ideal_of_mem hU Z hZ i hi


end

section
variable (hU : IsAffineOpen U)
include hU

theorem isAffineOpen_domain_of_isPullback (B : BlowupChart π c S s)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map) :
    IsAffineOpen B.domain := by
  have hUaff : IsAffine U.toScheme := hU
  have hA : IsAffine (affineSpaceFin k m) := inferInstance
  have hP : IsAffine (Limits.pullback (coordBlowupSubstMap k m S s) c.map) := inferInstance
  exact IsAffine.of_isIso hB.isoPullback.hom

private theorem quotientMk_comp_appLE_eq_zero_of_mem_consolidated266 (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) :
    ∀ a ∈ Z.ideal ⟨U, hU⟩,
      ((Ideal.Quotient.mk (Ideal.span {B.chart.coord s})).comp
          (π.appLE U B.domain B.domain_le).hom) a = 0 := by
  have key : Ideal.span (c.coord '' (S : Set (Fin m))) ≤
      Ideal.comap (π.appLE U B.domain B.domain_le).hom
        (Ideal.span {B.chart.coord s}) := by
    rw [Ideal.span_le]
    rintro x ⟨i, hi, rfl⟩
    have hmem : (π.appLE U B.domain B.domain_le).hom (c.coord i) ∈
        Ideal.span {B.chart.coord s} := by
      by_cases his : i = s
      · subst his
        rw [BlowupChart.appLE_coord_self B]
        exact Ideal.mem_span_singleton_self _
      · rw [BlowupChart.appLE_coord_of_mem B i (Finset.mem_coe.mp hi) his]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    exact hmem
  intro a ha
  rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  rw [EtaleChart.ideal_eq_span_coord c hU Z S hZ] at ha
  exact Ideal.mem_comap.mp (key ha)


end

def exceptionalQuotientBaseHom (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (_hs : s ∈ S) :
    (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) →+* (Γ(X₁, B.domain) ⧸ Ideal.span {B.chart.coord s}) :=
  Ideal.Quotient.lift (Z.ideal ⟨U, hU⟩)
    ((Ideal.Quotient.mk (Ideal.span {B.chart.coord s})).comp
      (π.appLE U B.domain B.domain_le).hom)
    (quotientMk_comp_appLE_eq_zero_of_mem_consolidated266 hU Z hZ B)

theorem exceptionalQuotientBaseHom_mk (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (a : Γ(X, U)) :
    exceptionalQuotientBaseHom hU Z hZ B hs ((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)) a) =
      (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}))
        ((π.appLE U B.domain B.domain_le).hom a) :=
  rfl

def mvPolynomialToExceptionalQuotient (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S) :
    MvPolynomial ↥(S.erase s) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) →+*
      (Γ(X₁, B.domain) ⧸ Ideal.span {B.chart.coord s}) :=
  MvPolynomial.eval₂Hom (exceptionalQuotientBaseHom hU Z hZ B hs)
    (fun t => (Ideal.Quotient.mk (Ideal.span {B.chart.coord s})) (B.chart.coord t.1))

section
variable (hU : IsAffineOpen U) (Z : X.IdealSheafData) (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)

theorem mvPolynomialToExceptionalQuotient_C (r : Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) :
    mvPolynomialToExceptionalQuotient hU Z hZ B hs (MvPolynomial.C r) = exceptionalQuotientBaseHom hU Z hZ B hs r :=
  MvPolynomial.eval₂Hom_C _ _ r

theorem mvPolynomialToExceptionalQuotient_X (t : ↥(S.erase s)) :
    mvPolynomialToExceptionalQuotient hU Z hZ B hs (MvPolynomial.X t) =
      (Ideal.Quotient.mk (Ideal.span {B.chart.coord s})) (B.chart.coord t.1) :=
  MvPolynomial.eval₂Hom_X' _ _ t


end

private def exceptionalVar_consolidated266 (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (cc : EtaleChart p U m) (SS : Finset (Fin m)) (ss : Fin m) (j : Fin m) :
    MvPolynomial ↥(SS.erase ss) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) :=
  if h : j ∈ SS.erase ss then MvPolynomial.X ⟨j, h⟩
  else MvPolynomial.C ((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)) (cc.coord j))

section
variable (hU : IsAffineOpen U) (Z : X.IdealSheafData) (cc : EtaleChart p U m) (SS : Finset (Fin m)) (ss : Fin m) (j : Fin m)

private theorem exceptionalVar_of_mem_consolidated266 (h : j ∈ SS.erase ss) :
    exceptionalVar_consolidated266 hU Z cc SS ss j = MvPolynomial.X ⟨j, h⟩ :=
  dif_pos h

private theorem exceptionalVar_of_not_mem_consolidated266 (h : j ∉ SS.erase ss) :
    exceptionalVar_consolidated266 hU Z cc SS ss j =
      MvPolynomial.C ((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)) (cc.coord j)) :=
  dif_neg h


end

private def exceptionalEvalHom_consolidated266 (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (cc : EtaleChart p U m) (SS : Finset (Fin m)) (ss : Fin m) :
    MvPolynomial (ULift.{u} (Fin m)) Γ(X, U) →+*
      MvPolynomial ↥(SS.erase ss) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C : (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) →+*
        MvPolynomial ↥(SS.erase ss) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩)).comp
      (Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)))
    (fun i => exceptionalVar_consolidated266 hU Z cc SS ss i.down)

section
variable (hU : IsAffineOpen U) (Z : X.IdealSheafData) (cc : EtaleChart p U m) (SS : Finset (Fin m)) (ss : Fin m)

private theorem exceptionalEval_C_consolidated266 (a : Γ(X, U)) :
    exceptionalEvalHom_consolidated266 hU Z cc SS ss (MvPolynomial.C a) =
      MvPolynomial.C ((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)) a) :=
  MvPolynomial.eval₂Hom_C _ _ a

private theorem exceptionalEval_X_consolidated266 (j : Fin m) :
    exceptionalEvalHom_consolidated266 hU Z cc SS ss (MvPolynomial.X (ULift.up j)) = exceptionalVar_consolidated266 hU Z cc SS ss j :=
  MvPolynomial.eval₂Hom_X' _ _ (ULift.up j)


end

section
variable (hU : IsAffineOpen U) (Z : X.IdealSheafData) (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
include hZ hs

private theorem exceptionalEval_coordRelation_consolidated266 (i : Fin m) :
    exceptionalEvalHom_consolidated266 hU Z c S s (B.coordRelation i) = 0 := by
  have hpr : B.coordRelation i =
      (if i ∈ S ∧ i ≠ s then
          MvPolynomial.X (ULift.up i) * MvPolynomial.X (ULift.up s)
        else MvPolynomial.X (ULift.up i)) - MvPolynomial.C (c.coord i) := rfl
  have hsnot : s ∉ S.erase s := fun hc => (Finset.mem_erase.mp hc).1 rfl
  rw [hpr]
  by_cases h : i ∈ S ∧ i ≠ s
  · rw [if_pos h, map_sub, map_mul, exceptionalEval_X_consolidated266, exceptionalEval_X_consolidated266, exceptionalEval_C_consolidated266,
      exceptionalVar_of_not_mem_consolidated266 hU Z c S s s hsnot,
      mk_coord_eq_zero_of_mem hU Z hZ s hs, mk_coord_eq_zero_of_mem hU Z hZ i h.1, map_zero,
      mul_zero, sub_zero]
  · have hnot : i ∉ S.erase s := fun hc =>
      h ⟨(Finset.mem_erase.mp hc).2, (Finset.mem_erase.mp hc).1⟩
    rw [if_neg h, map_sub, exceptionalEval_X_consolidated266, exceptionalEval_C_consolidated266,
      exceptionalVar_of_not_mem_consolidated266 hU Z c S s i hnot, sub_self]

private theorem exceptionalEval_eq_zero_of_mem_span_coordRelation_consolidated266 :
    ∀ a ∈ Ideal.span (Set.range B.coordRelation), exceptionalEvalHom_consolidated266 hU Z c S s a = 0 := by
  have hsub : Ideal.span (Set.range B.coordRelation) ≤ RingHom.ker (exceptionalEvalHom_consolidated266 hU Z c S s) := by
    rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker]
    exact exceptionalEval_coordRelation_consolidated266 hU Z hZ B hs i
  intro a ha
  exact RingHom.mem_ker.mp (hsub ha)


end

private def exceptionalHomOfChart_consolidated266 (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map) :
    Γ(X₁, B.domain) →+* MvPolynomial ↥(S.erase s) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) :=
  (Ideal.Quotient.lift (Ideal.span (Set.range B.coordRelation)) (exceptionalEvalHom_consolidated266 hU Z c S s)
      (exceptionalEval_eq_zero_of_mem_span_coordRelation_consolidated266 hU Z hZ B hs)).comp
    (RingEquiv.ofBijective B.coordEvalQuotientHom (B.bijective_coordEvalQuotientHom hU hB)).symm.toRingHom

section
variable (hU : IsAffineOpen U) (Z : X.IdealSheafData) (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S) (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map)

private theorem exceptionalHomOfChart_coordEvalHom_consolidated266 (f : MvPolynomial (ULift.{u} (Fin m)) Γ(X, U)) :
    exceptionalHomOfChart_consolidated266 hU Z hZ B hs hB (B.coordEvalHom f) = exceptionalEvalHom_consolidated266 hU Z c S s f := by
  have h1 : (RingEquiv.ofBijective B.coordEvalQuotientHom (B.bijective_coordEvalQuotientHom hU hB)).symm
      (B.coordEvalHom f) = (Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation))) f := by
    apply (RingEquiv.ofBijective B.coordEvalQuotientHom (B.bijective_coordEvalQuotientHom hU hB)).injective
    rw [RingEquiv.apply_symm_apply]
    exact (BlowupChart.coordEvalQuotientHom_mk B f).symm
  have h2 : exceptionalHomOfChart_consolidated266 hU Z hZ B hs hB (B.coordEvalHom f)
      = (Ideal.Quotient.lift (Ideal.span (Set.range B.coordRelation)) (exceptionalEvalHom_consolidated266 hU Z c S s)
          (exceptionalEval_eq_zero_of_mem_span_coordRelation_consolidated266 hU Z hZ B hs))
          ((RingEquiv.ofBijective B.coordEvalQuotientHom (B.bijective_coordEvalQuotientHom hU hB)).symm
            (B.coordEvalHom f)) := rfl
  simp only [h2, h1, Ideal.Quotient.lift_mk]

private theorem exceptionalHomOfChart_coord_consolidated266 (i : Fin m) :
    exceptionalHomOfChart_consolidated266 hU Z hZ B hs hB (B.chart.coord i) = exceptionalVar_consolidated266 hU Z c S s i := by
  rw [← BlowupChart.coordEvalHom_X B i, exceptionalHomOfChart_coordEvalHom_consolidated266, exceptionalEval_X_consolidated266]

private theorem exceptionalHomOfChart_coord_self_consolidated266 :
    exceptionalHomOfChart_consolidated266 hU Z hZ B hs hB (B.chart.coord s) = 0 := by
  rw [exceptionalHomOfChart_coord_consolidated266 hU Z hZ B hs hB s,
    exceptionalVar_of_not_mem_consolidated266 hU Z c S s s (fun hc => (Finset.mem_erase.mp hc).1 rfl),
    mk_coord_eq_zero_of_mem hU Z hZ s hs, map_zero]


end

private def exceptionalHomOfQuotientCoord_consolidated266 (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map) :
    (Γ(X₁, B.domain) ⧸ Ideal.span {B.chart.coord s}) →+*
      MvPolynomial ↥(S.erase s) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) :=
  Ideal.Quotient.lift (Ideal.span {B.chart.coord s}) (exceptionalHomOfChart_consolidated266 hU Z hZ B hs hB)
    (by
      intro a ha
      obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, exceptionalHomOfChart_coord_self_consolidated266 hU Z hZ B hs hB, mul_zero])

section
variable (hU : IsAffineOpen U) (Z : X.IdealSheafData) (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S) (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map)
include hB

private theorem exceptionalHomOfQuotientCoord_mk_consolidated266 (a : Γ(X₁, B.domain)) :
    exceptionalHomOfQuotientCoord_consolidated266 hU Z hZ B hs hB ((Ideal.Quotient.mk (Ideal.span {B.chart.coord s})) a)
      = exceptionalHomOfChart_consolidated266 hU Z hZ B hs hB a :=
  rfl

theorem bijective_mvPolynomialToExceptionalQuotient :
    Function.Bijective (mvPolynomialToExceptionalQuotient hU Z hZ B hs) := by
  have hcomp : (mvPolynomialToExceptionalQuotient hU Z hZ B hs).comp (exceptionalEvalHom_consolidated266 hU Z c S s)
      = (Ideal.Quotient.mk (Ideal.span {B.chart.coord s})).comp B.coordEvalHom := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro a
      simp only [RingHom.comp_apply]
      rw [exceptionalEval_C_consolidated266, BlowupChart.coordEvalHom_C B a, mvPolynomialToExceptionalQuotient_C, exceptionalQuotientBaseHom_mk]
    · rintro ⟨i⟩
      simp only [RingHom.comp_apply]
      rw [exceptionalEval_X_consolidated266, BlowupChart.coordEvalHom_X B i]
      by_cases h : i ∈ S.erase s
      · rw [exceptionalVar_of_mem_consolidated266 hU Z c S s i h, mvPolynomialToExceptionalQuotient_X]
      · have hEq : (π.appLE U B.domain B.domain_le).hom (c.coord i) = B.chart.coord i := by
          by_cases his : i = s
          · subst his
            exact BlowupChart.appLE_coord_self B
          · exact BlowupChart.appLE_coord_of_not_mem B i
              (fun hi => h (Finset.mem_erase.mpr ⟨his, hi⟩))
        rw [exceptionalVar_of_not_mem_consolidated266 hU Z c S s i h, mvPolynomialToExceptionalQuotient_C, exceptionalQuotientBaseHom_mk, hEq]
  constructor
  · have hleft : (exceptionalHomOfQuotientCoord_consolidated266 hU Z hZ B hs hB).comp (mvPolynomialToExceptionalQuotient hU Z hZ B hs)
        = RingHom.id (MvPolynomial ↥(S.erase s) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩)) := by
      refine MvPolynomial.ringHom_ext ?_ ?_
      · intro r
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [mvPolynomialToExceptionalQuotient_C, exceptionalQuotientBaseHom_mk, exceptionalHomOfQuotientCoord_mk_consolidated266, ← BlowupChart.coordEvalHom_C B a,
          exceptionalHomOfChart_coordEvalHom_consolidated266, exceptionalEval_C_consolidated266]
      · intro t
        simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [mvPolynomialToExceptionalQuotient_X, exceptionalHomOfQuotientCoord_mk_consolidated266, exceptionalHomOfChart_coord_consolidated266]
        exact exceptionalVar_of_mem_consolidated266 hU Z c S s t.1 t.2
    intro x y hxy
    have hx : exceptionalHomOfQuotientCoord_consolidated266 hU Z hZ B hs hB ((mvPolynomialToExceptionalQuotient hU Z hZ B hs) x) = x :=
      DFunLike.congr_fun hleft x
    have hy : exceptionalHomOfQuotientCoord_consolidated266 hU Z hZ B hs hB ((mvPolynomialToExceptionalQuotient hU Z hZ B hs) y) = y :=
      DFunLike.congr_fun hleft y
    rw [← hx, ← hy, hxy]
  · intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨f, rfl⟩ := B.surjective_coordEvalHom hU hB b
    exact ⟨exceptionalEvalHom_consolidated266 hU Z c S s f, DFunLike.congr_fun hcomp f⟩


end

def exceptionalQuotientEquivMvPolynomial (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map) :
    (Γ(X₁, B.domain) ⧸ Ideal.span {B.chart.coord s}) ≃+*
      MvPolynomial ↥(S.erase s) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) :=
  (RingEquiv.ofBijective (mvPolynomialToExceptionalQuotient hU Z hZ B hs) (bijective_mvPolynomialToExceptionalQuotient hU Z hZ B hs hB)).symm

section
variable (hU : IsAffineOpen U) (Z : X.IdealSheafData) (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S) (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map)

theorem exceptionalQuotientEquivMvPolynomial_symm_apply (f : MvPolynomial ↥(S.erase s) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩)) :
    (exceptionalQuotientEquivMvPolynomial hU Z hZ B hs hB).symm f = mvPolynomialToExceptionalQuotient hU Z hZ B hs f :=
  rfl

theorem exceptionalQuotientEquivMvPolynomial_mk_appLE (a : Γ(X, U)) :
    exceptionalQuotientEquivMvPolynomial hU Z hZ B hs hB
        ((Ideal.Quotient.mk (Ideal.span {B.chart.coord s}))
          ((π.appLE U B.domain B.domain_le).hom a)) =
      MvPolynomial.C ((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)) a) := by
  apply (exceptionalQuotientEquivMvPolynomial hU Z hZ B hs hB).symm.injective
  rw [RingEquiv.symm_apply_apply, exceptionalQuotientEquivMvPolynomial_symm_apply, mvPolynomialToExceptionalQuotient_C, exceptionalQuotientBaseHom_mk]

theorem exceptionalQuotientEquivMvPolynomial_mk_coord (i : Fin m) (hi : i ∈ S) (his : i ≠ s) :
    exceptionalQuotientEquivMvPolynomial hU Z hZ B hs hB
        ((Ideal.Quotient.mk (Ideal.span {B.chart.coord s})) (B.chart.coord i)) =
      MvPolynomial.X ⟨i, Finset.mem_erase.mpr ⟨his, hi⟩⟩ := by
  apply (exceptionalQuotientEquivMvPolynomial hU Z hZ B hs hB).symm.injective
  rw [RingEquiv.symm_apply_apply, exceptionalQuotientEquivMvPolynomial_symm_apply]
  exact (mvPolynomialToExceptionalQuotient_X hU Z hZ B hs ⟨i, Finset.mem_erase.mpr ⟨his, hi⟩⟩).symm


end

theorem isAffineOpen_blowupChart_domain (hU : IsAffineOpen U) {Z : X.IdealSheafData}
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S) (hs : s ∈ S) :
    IsAffineOpen (blowupChartOfIsBlowup π c S hπ hZ s hs).domain :=
  isAffineOpen_domain_of_isPullback hU (blowupChartOfIsBlowup π c S hπ hZ s hs)
    (isPullback_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZ s hs)

def exceptionalQuotientEquivOfIsBlowup (hU : IsAffineOpen U) {Z : X.IdealSheafData}
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S) (hs : s ∈ S) :
    (Γ(X₁, (blowupChartOfIsBlowup π c S hπ hZ s hs).domain) ⧸
        Ideal.span {(blowupChartOfIsBlowup π c S hπ hZ s hs).chart.coord s}) ≃+*
      MvPolynomial ↥(S.erase s) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) :=
  exceptionalQuotientEquivMvPolynomial hU Z hZ (blowupChartOfIsBlowup π c S hπ hZ s hs) hs
    (isPullback_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZ s hs)

section
variable (hU : IsAffineOpen U) {Z : X.IdealSheafData} (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S) (hs : s ∈ S)

theorem exceptionalQuotientEquiv_mk_appLE (a : Γ(X, U)) :
    exceptionalQuotientEquivOfIsBlowup hU hπ hZ hs
        ((Ideal.Quotient.mk
            (Ideal.span {(blowupChartOfIsBlowup π c S hπ hZ s hs).chart.coord s}))
          ((π.appLE U (blowupChartOfIsBlowup π c S hπ hZ s hs).domain
            (blowupChartOfIsBlowup π c S hπ hZ s hs).domain_le).hom a)) =
      MvPolynomial.C ((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)) a) :=
  exceptionalQuotientEquivMvPolynomial_mk_appLE hU Z hZ (blowupChartOfIsBlowup π c S hπ hZ s hs) hs
    (isPullback_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZ s hs) a

theorem exceptionalQuotientEquiv_mk_coord (i : Fin m) (hi : i ∈ S) (his : i ≠ s) :
    exceptionalQuotientEquivOfIsBlowup hU hπ hZ hs
        ((Ideal.Quotient.mk
            (Ideal.span {(blowupChartOfIsBlowup π c S hπ hZ s hs).chart.coord s}))
          ((blowupChartOfIsBlowup π c S hπ hZ s hs).chart.coord i)) =
      MvPolynomial.X ⟨i, Finset.mem_erase.mpr ⟨his, hi⟩⟩ :=
  exceptionalQuotientEquivMvPolynomial_mk_coord hU Z hZ (blowupChartOfIsBlowup π c S hπ hZ s hs) hs
    (isPullback_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZ s hs) i hi his

theorem exceptionalIdeal_ideal_blowupChart_domain :
    (Blowup.exceptionalIdeal π Z).ideal
        ⟨(blowupChartOfIsBlowup π c S hπ hZ s hs).domain,
          isAffineOpen_blowupChart_domain hU hπ hZ hs⟩ =
      Ideal.span {(blowupChartOfIsBlowup π c S hπ hZ s hs).chart.coord s} := by
  rw [EtaleChart.ideal_eq_span_coord (blowupChartOfIsBlowup π c S hπ hZ s hs).chart
      (isAffineOpen_blowupChart_domain hU hπ hZ hs) (Blowup.exceptionalIdeal π Z) {s}
      (BlowupChart.restrictIdeal_exceptionalIdeal (blowupChartOfIsBlowup π c S hπ hZ s hs) Z hs hZ),
    Finset.coe_singleton, Set.image_singleton]


end

end FunctorialResolution.EmbeddedResolution

end
end
end
