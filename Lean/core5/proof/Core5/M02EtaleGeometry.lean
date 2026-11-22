import Mathlib
import Core5.M01Foundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

universe u v
noncomputable section
-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

abbrev affineSpaceIndexedBy (k : Type u) [Field k] (n : Type u) : Scheme.{u} :=
  AlgebraicGeometry.AffineSpace n (Spec (CommRingCat.of k))

abbrev affineSpaceIndexedByToSpec (k : Type u) [Field k] (n : Type u) :
    affineSpaceIndexedBy k n ⟶ Spec (CommRingCat.of k) :=
  affineSpaceIndexedBy k n ↘ Spec (CommRingCat.of k)

def pullbackCoord {k : Type u} [Field k] {Y : Scheme.{u}} {n : Type u}
    (f : Y ⟶ affineSpaceIndexedBy k n) (i : n) : Γ(Y, ⊤) :=
  f.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i)

@[simp]
theorem pullbackCoord_def {k : Type u} [Field k] {Y : Scheme.{u}} {n : Type u}
    (f : Y ⟶ affineSpaceIndexedBy k n) (i : n) :
    pullbackCoord f i = f.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i) := rfl

def coordVectorInl {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))) :
    ULift.{u} (Fin n ⊕ Fin m) → Γ(Y, ⊤) :=
  fun i => Sum.elim (fun a => pullbackCoord f (ULift.up a)) (fun _ => 0) i.down

def coordVectorInr {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m))) :
    ULift.{u} (Fin n ⊕ Fin m) → Γ(Y, ⊤) :=
  fun i => Sum.elim (fun _ => 0) (fun b => pullbackCoord f (ULift.up b)) i.down

@[simp]
theorem coordVectorInr_inl {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m))) (a : Fin n) :
    coordVectorInr n m f (ULift.up (Sum.inl a)) = 0 := rfl

@[simp]
theorem coordVectorInr_inr {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m))) (b : Fin m) :
    coordVectorInr n m f (ULift.up (Sum.inr b)) = pullbackCoord f (ULift.up b) := rfl

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartAlgebra
section
open CategoryTheory AlgebraicGeometry TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

variable {X Y : Scheme.{u}} {W : X.Opens} {V : Y.Opens} {n : Type u}

noncomputable def chartCoeffHom (g : V.toScheme ⟶ AffineSpace n W.toScheme) :
    Γ(X, W) →+* Γ(Y, V) :=
  (W.topIso.inv ≫ (g ≫ (AffineSpace n W.toScheme ↘ W.toScheme)).appTop ≫ V.topIso.hom).hom

noncomputable def chartVar (g : V.toScheme ⟶ AffineSpace n W.toScheme) (j : n) : Γ(Y, V) :=
  V.topIso.hom.hom (g.appTop.hom (AffineSpace.coord (S := W.toScheme) j))

noncomputable def chartEvalHom (_hW : IsAffineOpen W) (g : V.toScheme ⟶ AffineSpace n W.toScheme) :
    MvPolynomial n Γ(X, W) →+* Γ(Y, V) :=
  MvPolynomial.eval₂Hom (chartCoeffHom g) (chartVar g)

section
variable {X' Y' : Scheme.{u}} (h : Y' ⟶ X') (W' : X'.Opens) (V' : Y'.Opens) (e : V' ≤ h ⁻¹ᵁ W')

private theorem resLE_appTop_eq_consolidated5 :
    (h.resLE W' V' e).appTop = W'.topIso.hom ≫ h.appLE W' V' e ≫ V'.topIso.inv := by
  simp

private theorem resLE_appTop_conj_topIso_eq_appLE_consolidated5 :
    W'.topIso.inv ≫ (h.resLE W' V' e).appTop ≫ V'.topIso.hom = h.appLE W' V' e := by
  rw [resLE_appTop_eq_consolidated5]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]


end

section
variable (hW : IsAffineOpen W) (h : Y ⟶ X) (e : V ≤ h ⁻¹ᵁ W) (g : V.toScheme ⟶ AffineSpace n W.toScheme) (hg : g ≫ (AffineSpace n W.toScheme ↘ W.toScheme) = h.resLE W V e)
include hg

theorem chartEvalHom_comp_C :
    (chartEvalHom hW g).comp (MvPolynomial.C : Γ(X, W) →+* MvPolynomial n Γ(X, W)) =
      (h.appLE W V e).hom := by
  have key : chartCoeffHom g = (h.appLE W V e).hom := by
    simp only [chartCoeffHom, hg, resLE_appTop_conj_topIso_eq_appLE_consolidated5]
  refine RingHom.ext fun a => ?_
  have h1 : chartEvalHom hW g (MvPolynomial.C a) = chartCoeffHom g a := by simp [chartEvalHom]
  rw [RingHom.comp_apply, h1, key]

theorem chartEvalHom_C (a : Γ(X, W)) :
    chartEvalHom hW g (MvPolynomial.C a) = (h.appLE W V e).hom a :=
  RingHom.congr_fun (chartEvalHom_comp_C hW h e g hg) a


end

@[reducible]
noncomputable def chartAlgebra (hW : IsAffineOpen W)
    (g : V.toScheme ⟶ AffineSpace n W.toScheme) :
    Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) :=
  (chartEvalHom hW g).toAlgebra

theorem chartAlgebra_isScalarTower (hW : IsAffineOpen W) (h : Y ⟶ X) (e : V ≤ h ⁻¹ᵁ W)
    (g : V.toScheme ⟶ AffineSpace n W.toScheme)
    (hg : g ≫ (AffineSpace n W.toScheme ↘ W.toScheme) = h.resLE W V e) :
    letI : Algebra Γ(X, W) Γ(Y, V) := (h.appLE W V e).hom.toAlgebra
    letI : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
    IsScalarTower Γ(X, W) (MvPolynomial n Γ(X, W)) Γ(Y, V) := by
  let : Algebra Γ(X, W) Γ(Y, V) := (h.appLE W V e).hom.toAlgebra
  let : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  show (h.appLE W V e).hom a = chartEvalHom hW g (algebraMap Γ(X, W) (MvPolynomial n Γ(X, W)) a)
  rw [MvPolynomial.algebraMap_eq, chartEvalHom_C hW h e g hg]

section
variable {R S : Type u} [CommRing R] [CommRing S]

private theorem algebraEtale_congr_consolidated5 {f f' : R →+* S}
    (h : f = f') (hf : @Algebra.Etale R S _ _ f.toAlgebra) :
    @Algebra.Etale R S _ _ f'.toAlgebra := by
  subst h
  exact hf

private theorem algebraEtale_of_ringHomEtale_consolidated5 (f : R →+* S)
    (h : RingHom.Etale f) : @Algebra.Etale R S _ _ f.toAlgebra := h


end

private theorem algebraEtale_comp_equiv_consolidated5 {R R' S S' : Type u} [CommRing R] [CommRing R']
    [CommRing S] [CommRing S'] (eR : R' ≃+* R) (f : R →+* S) (eS : S ≃+* S')
    (hf : @Algebra.Etale R S _ _ f.toAlgebra) :
    @Algebra.Etale R' S' _ _ (((eS : S →+* S').comp (f.comp (eR : R' →+* R))).toAlgebra) := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.Etale R S := hf
  let : Algebra R' R := (eR : R' →+* R).toAlgebra
  let : Algebra R S' := ((eS : S →+* S').comp f).toAlgebra
  let : Algebra R' S' := ((eS : S →+* S').comp (f.comp (eR : R' →+* R))).toAlgebra
  have : IsScalarTower R' R S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.Etale R' R' := inferInstance
  have : Algebra.Etale R' R :=
    Algebra.Etale.of_equiv (R := R') (A := R') (AlgEquiv.ofRingEquiv (f := eR) fun _ => rfl)
  have : Algebra.Etale R S' :=
    Algebra.Etale.of_equiv (R := R) (A := S) (AlgEquiv.ofRingEquiv (f := eS) fun _ => rfl)
  exact Algebra.Etale.comp R' R S'

private theorem comp_appTop_apply_consolidated5 {A B C : Scheme.{u}} (f : A ⟶ B) (k : B ⟶ C) (z : Γ(C, ⊤)) :
    (f ≫ k).appTop.hom z = f.appTop.hom (k.appTop.hom z) :=
  congrArg (fun m : Γ(C, ⊤) ⟶ Γ(A, ⊤) => CommRingCat.Hom.hom m z) (Scheme.Hom.comp_appTop f k)

private theorem specMap_appTop_apply_consolidated5 {R S : CommRingCat.{u}} (u : R ⟶ S) (a : R) :
    (Spec.map u).appTop.hom ((Scheme.ΓSpecIso R).inv.hom a) =
      (Scheme.ΓSpecIso S).inv.hom (u.hom a) :=
  (congrArg (fun m : R ⟶ Γ(Spec S, ⊤) => CommRingCat.Hom.hom m a)
    (Scheme.ΓSpecIso_inv_naturality u)).symm

private theorem isoSpec_hom_appTop_apply_consolidated5 (Z : Scheme.{u}) [IsAffine Z] (a : Γ(Z, ⊤)) :
    Z.isoSpec.hom.appTop.hom ((Scheme.ΓSpecIso Γ(Z, ⊤)).inv.hom a) = a := by
  rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
  exact congrArg (fun m : Γ(Z, ⊤) ⟶ Γ(Z, ⊤) => CommRingCat.Hom.hom m a)
    (Scheme.ΓSpecIso Γ(Z, ⊤)).inv_hom_id

private noncomputable def affineOpenIsoSpec {X' : Scheme.{u}} {W' : X'.Opens} (hW : IsAffineOpen W') :
    W'.toScheme ≅ Spec Γ(X', W') :=
  haveI : IsAffine W'.toScheme := hW
  W'.toScheme.isoSpec ≪≫ Scheme.Spec.mapIso W'.topIso.symm.op

private theorem affineOpenIsoSpec_hom_appTop_apply_consolidated5 {X' : Scheme.{u}} {W' : X'.Opens}
    (hW : IsAffineOpen W') (a : Γ(X', W')) :
    (affineOpenIsoSpec hW).hom.appTop.hom ((Scheme.ΓSpecIso Γ(X', W')).inv.hom a) =
      W'.topIso.inv.hom a := by
  have : IsAffine W'.toScheme := hW
  show (W'.toScheme.isoSpec.hom ≫ Spec.map W'.topIso.symm.hom).appTop.hom
      ((Scheme.ΓSpecIso Γ(X', W')).inv.hom a) = W'.topIso.inv.hom a
  rw [comp_appTop_apply_consolidated5, specMap_appTop_apply_consolidated5, isoSpec_hom_appTop_apply_consolidated5]
  rfl

private noncomputable def affineSpaceOpenIsoSpecMvPolynomial {X' : Scheme.{u}} {W' : X'.Opens} (hW : IsAffineOpen W')
    (m : Type u) :
    AffineSpace m W'.toScheme ≅ Spec (CommRingCat.of (MvPolynomial m Γ(X', W'))) :=
  (AffineSpace.functor.obj (Opposite.op m)).mapIso (affineOpenIsoSpec hW) ≪≫
    AffineSpace.SpecIso m Γ(X', W')

section
variable {X' : Scheme.{u}} {W' : X'.Opens} (hW : IsAffineOpen W') (m : Type u)

private theorem affineSpaceOpenIsoSpecMvPolynomial_hom_appTop_X_consolidated5 (j : m) :
    (affineSpaceOpenIsoSpecMvPolynomial hW m).hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
          (MvPolynomial.X j)) =
      AffineSpace.coord W'.toScheme j := by
  have key : (AffineSpace.SpecIso m Γ(X', W')).hom.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
        (MvPolynomial.X j)) = AffineSpace.coord (Spec Γ(X', W')) j := by
    rw [← AffineSpace.SpecIso_inv_appTop_coord, ← comp_appTop_apply_consolidated5, Iso.hom_inv_id]
    simp
  show ((AffineSpace.map m (affineOpenIsoSpec hW).hom) ≫
      (AffineSpace.SpecIso m Γ(X', W')).hom).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
        (MvPolynomial.X j)) = AffineSpace.coord W'.toScheme j
  rw [comp_appTop_apply_consolidated5, key, AffineSpace.map_appTop_coord]

private theorem affineSpaceOpenIsoSpecMvPolynomial_hom_appTop_C_consolidated5 (a : Γ(X', W')) :
    (affineSpaceOpenIsoSpecMvPolynomial hW m).hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
          (MvPolynomial.C a)) =
      (AffineSpace m W'.toScheme ↘ W'.toScheme).appTop.hom (W'.topIso.inv.hom a) := by
  have h1 : (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : Γ(X', W') →+* MvPolynomial m Γ(X', W')))).appTop.hom
        ((Scheme.ΓSpecIso Γ(X', W')).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
        (MvPolynomial.C a) :=
    specMap_appTop_apply_consolidated5 _ a
  have key : (AffineSpace.SpecIso m Γ(X', W')).hom.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
        (MvPolynomial.C a)) =
      (AffineSpace m (Spec Γ(X', W')) ↘ Spec Γ(X', W')).appTop.hom
        ((Scheme.ΓSpecIso Γ(X', W')).inv.hom a) := by
    rw [← h1, ← comp_appTop_apply_consolidated5, ← AffineSpace.SpecIso_inv_over, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  show ((AffineSpace.map m (affineOpenIsoSpec hW).hom) ≫
      (AffineSpace.SpecIso m Γ(X', W')).hom).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
        (MvPolynomial.C a)) =
      (AffineSpace m W'.toScheme ↘ W'.toScheme).appTop.hom (W'.topIso.inv.hom a)
  rw [comp_appTop_apply_consolidated5, key, ← comp_appTop_apply_consolidated5, AffineSpace.map_over, comp_appTop_apply_consolidated5,
    affineOpenIsoSpec_hom_appTop_apply_consolidated5]


end

section
variable (hW : IsAffineOpen W) (hV : IsAffineOpen V) (g : V.toScheme ⟶ AffineSpace n W.toScheme) [Etale g]
include hW hV g

theorem chartAlgebra_etale :
    letI : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
    Algebra.Etale (MvPolynomial n Γ(X, W)) Γ(Y, V) := by
  let : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
  have : IsAffine V.toScheme := hV
  have : IsAffine W.toScheme := hW
  have hEt : Etale (g ≫ (affineSpaceOpenIsoSpecMvPolynomial hW n).hom) := inferInstance
  have hr : RingHom.Etale (g ≫ (affineSpaceOpenIsoSpecMvPolynomial hW n).hom).appTop.hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp hEt
  have hAlg := algebraEtale_of_ringHomEtale_consolidated5 _ hr
  have h2 := algebraEtale_comp_equiv_consolidated5
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial n Γ(X, W)))).symm.commRingCatIsoToRingEquiv
    (g ≫ (affineSpaceOpenIsoSpecMvPolynomial hW n).hom).appTop.hom V.topIso.commRingCatIsoToRingEquiv hAlg
  refine algebraEtale_congr_consolidated5 ?_ h2
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
  · have hC : chartEvalHom hW g (MvPolynomial.C a) = chartCoeffHom g a := by simp [chartEvalHom]
    show V.topIso.hom.hom ((g ≫ (affineSpaceOpenIsoSpecMvPolynomial hW n).hom).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial n Γ(X, W)))).inv.hom
          (MvPolynomial.C a))) = chartEvalHom hW g (MvPolynomial.C a)
    rw [comp_appTop_apply_consolidated5, affineSpaceOpenIsoSpecMvPolynomial_hom_appTop_C_consolidated5, ← comp_appTop_apply_consolidated5, hC]
    rfl
  · show V.topIso.hom.hom ((g ≫ (affineSpaceOpenIsoSpecMvPolynomial hW n).hom).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial n Γ(X, W)))).inv.hom
          (MvPolynomial.X j))) = chartEvalHom hW g (MvPolynomial.X j)
    rw [comp_appTop_apply_consolidated5, affineSpaceOpenIsoSpecMvPolynomial_hom_appTop_X_consolidated5]
    simp [chartEvalHom, chartVar]

theorem chartAlgebra_formallyEtale :
    letI : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
    Algebra.FormallyEtale (MvPolynomial n Γ(X, W)) Γ(Y, V) := by
  let : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
  have : Algebra.Etale (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra_etale hW hV g
  infer_instance


end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
section
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]

section

variable [Algebra (MvPolynomial ι k) S]

noncomputable def coord (i : ι) : S := algebraMap (MvPolynomial ι k) S (MvPolynomial.X i)

theorem coord_def (i : ι) :
    coord k ι S i = algebraMap (MvPolynomial ι k) S (MvPolynomial.X i) := rfl

end

section

variable [Algebra (MvPolynomial ι k) S] [Algebra k S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]

include ι

private theorem exists_basisKaehler_consolidated8 :
    ∃ b : Module.Basis ι S (KaehlerDifferential k S),
      ∀ i : ι, b i = KaehlerDifferential.D k S (coord k ι S i) := by
  have h : IsBaseChange S (KaehlerDifferential.map k k (MvPolynomial ι k) S) :=
    KaehlerDifferential.isBaseChange_of_formallyEtale k (MvPolynomial ι k) S
  refine ⟨(Algebra.TensorProduct.basis S
    (KaehlerDifferential.mvPolynomialBasis k ι)).map h.equiv, fun i => ?_⟩
  simp only [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
    KaehlerDifferential.mvPolynomialBasis_apply, IsBaseChange.equiv_tmul, one_smul,
    KaehlerDifferential.map_D]
  rfl

noncomputable def basisKaehler : Module.Basis ι S (KaehlerDifferential k S) :=
  (exists_basisKaehler_consolidated8 k ι S).choose

@[simp] theorem basisKaehler_apply (i : ι) :
    basisKaehler k ι S i = KaehlerDifferential.D k S (coord k ι S i) :=
  (exists_basisKaehler_consolidated8 k ι S).choose_spec i

private noncomputable def partialDerivFun (i : ι) (s : S) : S :=
  (basisKaehler k ι S).repr (KaehlerDifferential.D k S s) i

section
variable (i : ι)

private theorem partialFun_map_add_consolidated8 :
    ∀ x y : S, partialDerivFun k ι S i (x + y) = partialDerivFun k ι S i x + partialDerivFun k ι S i y := by
  intro x y
  show (basisKaehler k ι S).repr (KaehlerDifferential.D k S (x + y)) i
      = (basisKaehler k ι S).repr (KaehlerDifferential.D k S x) i
        + (basisKaehler k ι S).repr (KaehlerDifferential.D k S y) i
  rw [map_add, map_add, Finsupp.add_apply]

private theorem partialFun_map_smul_consolidated8 :
    ∀ (c : k) (x : S),
      partialDerivFun k ι S i (c • x) = (RingHom.id k) c • partialDerivFun k ι S i x := by
  intro c x
  have h1 : c • x = algebraMap k S c * x := Algebra.smul_def c x
  have h2 : KaehlerDifferential.D k S (c • x)
      = algebraMap k S c • KaehlerDifferential.D k S x := by
    rw [h1, Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero]
  show (basisKaehler k ι S).repr (KaehlerDifferential.D k S (c • x)) i
      = c • (basisKaehler k ι S).repr (KaehlerDifferential.D k S x) i
  rw [h2, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, ← Algebra.smul_def]


end

private noncomputable def partialDerivLinear (i : ι) : S →ₗ[k] S where
  toFun := partialDerivFun k ι S i
  map_add' := partialFun_map_add_consolidated8 k ι S i
  map_smul' := partialFun_map_smul_consolidated8 k ι S i

private theorem partialLinear_leibniz_consolidated8 (i : ι) :
    ∀ a b : S, partialDerivLinear k ι S i (a * b)
      = a • partialDerivLinear k ι S i b + b • partialDerivLinear k ι S i a := by
  intro a b
  have h : KaehlerDifferential.D k S (a * b)
      = a • KaehlerDifferential.D k S b + b • KaehlerDifferential.D k S a :=
    (KaehlerDifferential.D k S).leibniz a b
  have h2 : (basisKaehler k ι S).repr (KaehlerDifferential.D k S (a * b)) i
      = a * (basisKaehler k ι S).repr (KaehlerDifferential.D k S b) i
        + b * (basisKaehler k ι S).repr (KaehlerDifferential.D k S a) i := by
    rw [h, map_add, Finsupp.add_apply, LinearEquiv.map_smul, LinearEquiv.map_smul,
      Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
  exact h2

noncomputable def partialDeriv (i : ι) : Derivation k S S :=
  Derivation.mk' (partialDerivLinear k ι S i) (partialLinear_leibniz_consolidated8 k ι S i)

theorem partialDeriv_apply (i : ι) (s : S) :
    partialDeriv k ι S i s = (basisKaehler k ι S).repr (KaehlerDifferential.D k S s) i := rfl

@[simp] theorem partialDeriv_coord [DecidableEq ι] (i j : ι) :
    partialDeriv k ι S i (coord k ι S j) = if i = j then (1 : S) else 0 := by
  rw [partialDeriv_apply, ← basisKaehler_apply k ι S j, Module.Basis.repr_self,
    Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

theorem partialDeriv_coord_self (i : ι) :
    partialDeriv k ι S i (coord k ι S i) = 1 := by
  rw [partialDeriv_apply, ← basisKaehler_apply k ι S i, Module.Basis.repr_self,
    Finsupp.single_eq_same]

theorem partialDeriv_coord_of_ne (i j : ι) (h : i ≠ j) :
    partialDeriv k ι S i (coord k ι S j) = 0 := by
  classical
  rw [partialDeriv_coord k ι S i j, if_neg h]

omit [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S] in
private theorem sum_smul_derivation_apply_consolidated8 (c : ι → S) (f : ι → Derivation k S S)
    (s : S) (t : Finset ι) :
    (∑ i ∈ t, c i • f i) s = ∑ i ∈ t, c i * f i s := by
  induction t using Finset.cons_induction_on
  · simp
  · rename_i a u hu ih
    rw [Finset.sum_cons, Finset.sum_cons, ← ih]
    rfl

theorem span_range_partialDeriv [Finite ι] :
    Submodule.span S (Set.range (partialDeriv k ι S)) = (⊤ : Submodule S (Derivation k S S)) := by
  obtain ⟨hι⟩ := nonempty_fintype ι
  refine Submodule.eq_top_iff'.mpr fun D => ?_
  have key : D = ∑ i : ι, D (coord k ι S i) • partialDeriv k ι S i := by
    ext s
    have h1 : ∑ i : ι, partialDeriv k ι S i s • KaehlerDifferential.D k S (coord k ι S i)
        = KaehlerDifferential.D k S s := by
      rw [← Module.Basis.sum_repr (basisKaehler k ι S) (KaehlerDifferential.D k S s)]
      exact Finset.sum_congr rfl fun i _ => by rw [basisKaehler_apply, partialDeriv_apply]
    have h2 : D.liftKaehlerDifferential
        (∑ i : ι, partialDeriv k ι S i s • KaehlerDifferential.D k S (coord k ι S i))
        = D.liftKaehlerDifferential (KaehlerDifferential.D k S s) := by rw [h1]
    simp only [map_sum, map_smul, Derivation.liftKaehlerDifferential_comp_D] at h2
    rw [sum_smul_derivation_apply_consolidated8, ← h2]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]
  rw [key]
  exact sum_mem fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

theorem eq_sum_smul_partialDeriv [Fintype ι] (D : Derivation k S S) :
    D = ∑ i : ι, D (coord k ι S i) • partialDeriv k ι S i := by
  ext s
  have hsum : (∑ i : ι, D (coord k ι S i) • partialDeriv k ι S i) s
      = ∑ i : ι, D (coord k ι S i) * partialDeriv k ι S i s :=
    sum_smul_derivation_apply_consolidated8 k ι S (fun i => D (coord k ι S i))
      (partialDeriv k ι S) s Finset.univ
  rw [hsum]
  have h1 : D s = D.liftKaehlerDifferential (KaehlerDifferential.D k S s) := by
    rw [Derivation.liftKaehlerDifferential_comp_D]
  have h2 : KaehlerDifferential.D k S s
      = ∑ i : ι, (basisKaehler k ι S).repr (KaehlerDifferential.D k S s) i
          • basisKaehler k ι S i :=
    ((basisKaehler k ι S).sum_repr (KaehlerDifferential.D k S s)).symm
  rw [h1, h2, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, basisKaehler_apply, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul,
    ← partialDeriv_apply]
  exact mul_comm _ _

end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.IdealGeneratorsFromBase
section
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

section
variable {S : Type*} [CommRing S]

private theorem algebraMap_mem_map_of_mul_mem_consolidated25 (G : S) (T : Type*)
    [CommRing T] [Algebra S T] [IsLocalization (Submonoid.powers G) T] (J : Ideal S) (g r x : S)
    (hG : G = g * r) (hgx : g * x ∈ J) :
    algebraMap S T x ∈ Ideal.map (algebraMap S T) J := by
  have hGu : IsUnit (algebraMap S T G) :=
    IsLocalization.map_units T (⟨G, Submonoid.mem_powers G⟩ : Submonoid.powers G)
  rw [hG, map_mul] at hGu
  obtain ⟨u, hu⟩ := isUnit_of_mul_isUnit_left hGu
  have hx : algebraMap S T x = (↑u⁻¹ : T) * algebraMap S T (g * x) := by
    rw [map_mul, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [hx]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hgx)

theorem exists_away_map_ideal_eq (q : Ideal S) [q.IsPrime]
    (A : Type*) [CommRing A] [Algebra S A] [IsLocalization q.primeCompl A]
    (I J : Ideal S) (hI : I.FG) (hJ : J.FG)
    (h : Ideal.map (algebraMap S A) I = Ideal.map (algebraMap S A) J) :
    ∃ g : S, g ∉ q ∧
      Ideal.map (algebraMap S (Localization.Away g)) I =
        Ideal.map (algebraMap S (Localization.Away g)) J := by
  classical
  obtain ⟨tI, htI⟩ := hI
  obtain ⟨tJ, htJ⟩ := hJ
  have keyI : ∀ u : S, ∃ g : S, g ∈ q.primeCompl ∧ (u ∈ I → g * u ∈ J) := by
    intro u
    by_cases hu : u ∈ I
    · have hmem : algebraMap S A u ∈ Ideal.map (algebraMap S A) J := by
        rw [← h]
        exact Ideal.mem_map_of_mem _ hu
      rw [IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl A] at hmem
      obtain ⟨g, hg, hgu⟩ := hmem
      exact ⟨g, hg, fun _ => hgu⟩
    · exact ⟨1, Submonoid.one_mem _, fun hh => absurd hh hu⟩
  have keyJ : ∀ v : S, ∃ g : S, g ∈ q.primeCompl ∧ (v ∈ J → g * v ∈ I) := by
    intro v
    by_cases hv : v ∈ J
    · have hmem : algebraMap S A v ∈ Ideal.map (algebraMap S A) I := by
        rw [h]
        exact Ideal.mem_map_of_mem _ hv
      rw [IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl A] at hmem
      obtain ⟨g, hg, hgv⟩ := hmem
      exact ⟨g, hg, fun _ => hgv⟩
    · exact ⟨1, Submonoid.one_mem _, fun hh => absurd hh hv⟩
  choose gI hgI hgIu using keyI
  choose gJ hgJ hgJu using keyJ
  let G : S := (∏ u ∈ tI, gI u) * ∏ v ∈ tJ, gJ v
  have hGmem : G ∈ q.primeCompl :=
    Submonoid.mul_mem _ (Submonoid.prod_mem _ fun u _ => hgI u)
      (Submonoid.prod_mem _ fun v _ => hgJ v)
  refine ⟨G, hGmem, le_antisymm ?_ ?_⟩
  · rw [← htI, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨u, hu, rfl⟩
    have hu' : u ∈ tI := Finset.mem_coe.mp hu
    have huI : u ∈ I := by
      rw [← htI]
      exact Ideal.subset_span hu
    have hGeq : G = gI u * ((∏ z ∈ tI.erase u, gI z) * ∏ v ∈ tJ, gJ v) := by
      show (∏ z ∈ tI, gI z) * (∏ v ∈ tJ, gJ v) = _
      rw [← Finset.mul_prod_erase tI gI hu']
      ring
    exact algebraMap_mem_map_of_mul_mem_consolidated25 G (Localization.Away G) J (gI u)
      ((∏ z ∈ tI.erase u, gI z) * ∏ v ∈ tJ, gJ v) u hGeq (hgIu u huI)
  · rw [← htJ, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈ tJ := Finset.mem_coe.mp hv
    have hvJ : v ∈ J := by
      rw [← htJ]
      exact Ideal.subset_span hv
    have hGeq : G = gJ v * ((∏ u ∈ tI, gI u) * ∏ z ∈ tJ.erase v, gJ z) := by
      show (∏ u ∈ tI, gI u) * (∏ z ∈ tJ, gJ z) = _
      rw [← Finset.mul_prod_erase tJ gJ hv']
      ring
    exact algebraMap_mem_map_of_mul_mem_consolidated25 G (Localization.Away G) I (gJ v)
      ((∏ u ∈ tI, gI u) * ∏ z ∈ tJ.erase v, gJ z) v hGeq (hgJu v hvJ)


end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianCriterion
section
open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution
namespace JacobianCriterion

section

variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
variable [Algebra (MvPolynomial ι k) S]

noncomputable def coord (i : ι) : S := algebraMap (MvPolynomial ι k) S (MvPolynomial.X i)

end

section

variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
variable [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]

omit [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S] in
private theorem linearIndependent_one_tmul_D_X_consolidated26 :
    LinearIndependent S fun i : ι =>
      (1 : S) ⊗ₜ[MvPolynomial ι k]
        (KaehlerDifferential.D k (MvPolynomial ι k) (MvPolynomial.X i)) := by
  have hfun : (fun i : ι => (1 : S) ⊗ₜ[MvPolynomial ι k]
        (KaehlerDifferential.D k (MvPolynomial ι k) (MvPolynomial.X i))) =
      ⇑(Algebra.TensorProduct.basis S (KaehlerDifferential.mvPolynomialBasis k ι)) := by
    funext i
    rw [Algebra.TensorProduct.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply]
  rw [hfun]
  exact (Algebra.TensorProduct.basis S
    (KaehlerDifferential.mvPolynomialBasis k ι)).linearIndependent

section
variable (K : Type*) [CommRing K] (σ : Type*)

private theorem D_mem_span_range_D_X_consolidated26 (f : MvPolynomial σ K) :
    KaehlerDifferential.D K (MvPolynomial σ K) f ∈
      Submodule.span (MvPolynomial σ K)
        (Set.range fun i : σ =>
          KaehlerDifferential.D K (MvPolynomial σ K) (MvPolynomial.X i)) := by
  induction f using MvPolynomial.induction_on
  · rename_i a
    rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap]
    exact Submodule.zero_mem _
  · rename_i p q hp hq
    rw [map_add]
    exact Submodule.add_mem _ hp hq
  · rename_i p i hp
    rw [Derivation.leibniz]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
      (Submodule.smul_mem _ _ hp)

private theorem span_range_D_X_eq_top_consolidated26 :
    Submodule.span (MvPolynomial σ K)
        (Set.range fun i : σ =>
          KaehlerDifferential.D K (MvPolynomial σ K) (MvPolynomial.X i)) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact D_mem_span_range_D_X_consolidated26 K σ f


end

section
variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A] (M : Type*) [AddCommGroup M] [Module R M]

private theorem smul_one_tmul_consolidated26
    (a : A) (m : M) :
    a • ((1 : A) ⊗ₜ[R] m) = a ⊗ₜ[R] m := by
  have h2 : a • (1 : A) = a := by rw [smul_eq_mul, mul_one]
  have h1 : ((a • (1 : A)) ⊗ₜ[R] m : A ⊗[R] M) = a • ((1 : A) ⊗ₜ[R] m) := by
    rw [TensorProduct.smul_tmul']
  rw [h2] at h1
  exact h1.symm

private theorem top_le_span_range_one_tmul_consolidated26
    (τ : Type*) (g : τ → M)
    (hs : Submodule.span R (Set.range g) = ⊤) :
    ⊤ ≤ Submodule.span A (Set.range fun i : τ => (1 : A) ⊗ₜ[R] g i) := by
  have key : ∀ m : M, ∀ a : A,
      a ⊗ₜ[R] m ∈ Submodule.span A (Set.range fun i : τ => (1 : A) ⊗ₜ[R] g i) := by
    intro m
    have hm : m ∈ Submodule.span R (Set.range g) := by
      rw [hs]; exact Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hm
    · rintro x ⟨i, rfl⟩ a
      rw [← smul_one_tmul_consolidated26 R A M a (g i)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro a
      rw [TensorProduct.tmul_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy a
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ (hx a) (hy a)
    · intro r x _ hx a
      have e : a ⊗ₜ[R] (r • x) = (r • a) ⊗ₜ[R] x := by
        rw [TensorProduct.smul_tmul]
      rw [e]
      exact hx (r • a)
  intro w _
  refine TensorProduct.induction_on w ?_ ?_ ?_
  · exact Submodule.zero_mem _
  · intro a m
    exact key m a
  · intro u v hu hv
    exact Submodule.add_mem _ hu hv


end

omit [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S] in
private theorem top_le_span_one_tmul_D_X_consolidated26 :
    ⊤ ≤ Submodule.span S (Set.range fun i : ι =>
        (1 : S) ⊗ₜ[MvPolynomial ι k]
          (KaehlerDifferential.D k (MvPolynomial ι k) (MvPolynomial.X i))) :=
  top_le_span_range_one_tmul_consolidated26 (MvPolynomial ι k) S (KaehlerDifferential k (MvPolynomial ι k)) ι
    (fun i : ι => KaehlerDifferential.D k (MvPolynomial ι k) (MvPolynomial.X i))
    (span_range_D_X_eq_top_consolidated26 k ι)

noncomputable def tensorKaehlerBasis :
    Module.Basis ι S (S ⊗[MvPolynomial ι k] KaehlerDifferential k (MvPolynomial ι k)) :=
  Module.Basis.mk (linearIndependent_one_tmul_D_X_consolidated26 k ι S) (top_le_span_one_tmul_D_X_consolidated26 k ι S)

@[simp]
theorem tensorKaehlerBasis_mapBaseChange (i : ι) :
    KaehlerDifferential.mapBaseChange k (MvPolynomial ι k) S (tensorKaehlerBasis k ι S i) =
      KaehlerDifferential.D k S (coord k ι S i) := by
  have h : tensorKaehlerBasis k ι S i =
      (1 : S) ⊗ₜ[MvPolynomial ι k]
        (KaehlerDifferential.D k (MvPolynomial ι k) (MvPolynomial.X i)) :=
    Module.Basis.mk_apply (linearIndependent_one_tmul_D_X_consolidated26 k ι S) (top_le_span_one_tmul_D_X_consolidated26 k ι S) i
  have h2 : coord k ι S i = algebraMap (MvPolynomial ι k) S (MvPolynomial.X i) := rfl
  rw [h, KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D, h2]

theorem formallyUnramified_of_mapBaseChange_surjective
    (h : Function.Surjective (KaehlerDifferential.mapBaseChange k (MvPolynomial ι k) S)) :
    Algebra.FormallyUnramified (MvPolynomial ι k) S := by
  have hexact := KaehlerDifferential.exact_mapBaseChange_map k (MvPolynomial ι k) S
  have hD : ∀ s : S, KaehlerDifferential.D (MvPolynomial ι k) S s = 0 := by
    intro s
    obtain ⟨y, hy⟩ := h (KaehlerDifferential.D k S s)
    have h2 := hexact.apply_apply_eq_zero y
    rw [hy, KaehlerDifferential.map_D] at h2
    simpa using h2
  have key : ∀ x : KaehlerDifferential (MvPolynomial ι k) S, x = 0 := by
    intro x
    have hx : x ∈ Submodule.span S
        (Set.range (KaehlerDifferential.D (MvPolynomial ι k) S)) := by
      rw [KaehlerDifferential.span_range_derivation]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨s, rfl⟩ := hy
        exact hD s
    | zero => rfl
    | add a b _ _ ha hb => rw [ha, hb, add_zero]
    | smul c a _ ha => rw [ha, smul_zero]
  exact Algebra.FormallyUnramified.mk ⟨fun a b => by rw [key a, key b]⟩

theorem mapBaseChange_bijective_of_basis
    (b : Module.Basis ι S (KaehlerDifferential k S))
    (hb : ∀ i : ι, b i = KaehlerDifferential.D k S (coord k ι S i)) :
    Function.Bijective (KaehlerDifferential.mapBaseChange k (MvPolynomial ι k) S) := by
  have h : (KaehlerDifferential.mapBaseChange k (MvPolynomial ι k) S) =
      (((tensorKaehlerBasis k ι S).equiv b (Equiv.refl ι)) :
        (S ⊗[MvPolynomial ι k] KaehlerDifferential k (MvPolynomial ι k)) →ₗ[S]
          KaehlerDifferential k S) := by
    refine (tensorKaehlerBasis k ι S).ext fun i => ?_
    rw [tensorKaehlerBasis_mapBaseChange]
    simp [hb i]
  have hx : ∀ x, KaehlerDifferential.mapBaseChange k (MvPolynomial ι k) S x =
      ((tensorKaehlerBasis k ι S).equiv b (Equiv.refl ι)) x := by
    intro x
    have h2 := congrArg
      (fun f : (S ⊗[MvPolynomial ι k] KaehlerDifferential k (MvPolynomial ι k)) →ₗ[S]
        KaehlerDifferential k S => f x) h
    simpa using h2
  constructor
  · intro x y hxy
    apply ((tensorKaehlerBasis k ι S).equiv b (Equiv.refl ι)).injective
    rw [← hx, ← hx, hxy]
  · intro y
    obtain ⟨x, hxe⟩ := ((tensorKaehlerBasis k ι S).equiv b (Equiv.refl ι)).surjective y
    exact ⟨x, (hx x).trans hxe⟩

theorem formallyEtale_of_basis [Algebra.FormallySmooth k S]
    (b : Module.Basis ι S (KaehlerDifferential k S))
    (hb : ∀ i : ι, b i = KaehlerDifferential.D k S (coord k ι S i)) :
    Algebra.FormallyEtale (MvPolynomial ι k) S := by
  have hbij := mapBaseChange_bijective_of_basis k ι S b hb
  have hfu : Algebra.FormallyUnramified (MvPolynomial ι k) S :=
    formallyUnramified_of_mapBaseChange_surjective k ι S hbij.2
  have hh1 : Subsingleton (Algebra.H1Cotangent (MvPolynomial ι k) S) := by
    have key : ∀ z : Algebra.H1Cotangent (MvPolynomial ι k) S, z = 0 := by
      intro z
      have hz : Algebra.H1Cotangent.δ k (MvPolynomial ι k) S z = 0 := by
        have h0 := (Algebra.H1Cotangent.exact_δ_mapBaseChange k (MvPolynomial ι k)
          S).apply_apply_eq_zero z
        refine hbij.1 ?_
        rw [h0, map_zero]
      obtain ⟨w, hw⟩ := (Algebra.H1Cotangent.exact_map_δ k (MvPolynomial ι k) S z).mp hz
      rw [← hw, Subsingleton.elim w 0, map_zero]
    exact ⟨fun x y => by rw [key x, key y]⟩
  refine ⟨?_, ?_⟩
  · infer_instance
  · infer_instance

end

section

variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
variable (S : Type*) [CommRing S]
variable [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]

omit [IsScalarTower k (MvPolynomial ι k) S] in
private theorem linearIndependent_D_coord_of_isUnit_det_consolidated26 (b : Module.Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S (coord k ι S i))) :
    LinearIndependent S fun i : ι => KaehlerDifferential.D k S (coord k ι S i) :=
  (b.is_basis_iff_det.mpr h).1

omit [IsScalarTower k (MvPolynomial ι k) S] in
private theorem top_le_span_D_coord_of_isUnit_det_consolidated26 (b : Module.Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S (coord k ι S i))) :
    ⊤ ≤ Submodule.span S
        (Set.range fun i : ι => KaehlerDifferential.D k S (coord k ι S i)) := by
  have hb := b.is_basis_iff_det.mpr h
  have h2 : Submodule.span S
      (Set.range fun i : ι => KaehlerDifferential.D k S (coord k ι S i)) = ⊤ := hb.2
  exact h2.ge

noncomputable def coordBasis (b : Module.Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S (coord k ι S i))) :
    Module.Basis ι S (KaehlerDifferential k S) :=
  Module.Basis.mk (linearIndependent_D_coord_of_isUnit_det_consolidated26 k ι S b h) (top_le_span_D_coord_of_isUnit_det_consolidated26 k ι S b h)

omit [IsScalarTower k (MvPolynomial ι k) S] in
@[simp]
theorem coordBasis_apply (b : Module.Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S (coord k ι S i))) (i : ι) :
    coordBasis k ι S b h i = KaehlerDifferential.D k S (coord k ι S i) :=
  Module.Basis.mk_apply (linearIndependent_D_coord_of_isUnit_det_consolidated26 k ι S b h) (top_le_span_D_coord_of_isUnit_det_consolidated26 k ι S b h) i

theorem formallyEtale_of_isUnit_det [Algebra.FormallySmooth k S]
    (b : Module.Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S (coord k ι S i))) :
    Algebra.FormallyEtale (MvPolynomial ι k) S :=
  formallyEtale_of_basis k ι S (coordBasis k ι S b h) (coordBasis_apply k ι S b h)

end

section

variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S] [Algebra k S]
variable (S' : Type*) [CommRing S'] [Algebra k S'] [Algebra S S'] [IsScalarTower k S S']
variable [Algebra.FormallyEtale S S']

section
variable (b : Module.Basis ι S (KaehlerDifferential k S))

private theorem linearIndependent_kaehlerMap_basis_consolidated26
    :
    LinearIndependent S' fun i : ι => KaehlerDifferential.map k k S S' (b i) := by
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale k S S'
  have hfun : (fun i : ι => KaehlerDifferential.map k k S S' (b i)) =
      ⇑((Algebra.TensorProduct.basis S' b).map hbc.equiv) := by
    funext i
    rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, hbc.equiv_tmul, one_smul]
  rw [hfun]
  exact ((Algebra.TensorProduct.basis S' b).map hbc.equiv).linearIndependent

private theorem top_le_span_kaehlerMap_basis_consolidated26 :
    ⊤ ≤ Submodule.span S'
        (Set.range fun i : ι => KaehlerDifferential.map k k S S' (b i)) := by
  have hsub : Subsingleton (KaehlerDifferential S S') :=
    Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  have hexact := KaehlerDifferential.exact_mapBaseChange_map k S S'
  have hsurj : Function.Surjective (KaehlerDifferential.mapBaseChange k S S') := by
    intro x
    obtain ⟨y, hy⟩ := (hexact x).mp (Subsingleton.elim _ _)
    exact ⟨y, hy⟩
  have hspan : ⊤ ≤ Submodule.span S' (Set.range fun i : ι => (1 : S') ⊗ₜ[S] b i) :=
    top_le_span_range_one_tmul_consolidated26 S S' (KaehlerDifferential k S) ι (⇑b) b.span_eq
  have hle : Submodule.span S' (Set.range fun i : ι => (1 : S') ⊗ₜ[S] b i) ≤
      Submodule.comap (KaehlerDifferential.mapBaseChange k S S')
        (Submodule.span S'
          (Set.range fun i : ι => KaehlerDifferential.map k k S S' (b i))) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : KaehlerDifferential.mapBaseChange k S S' ((1 : S') ⊗ₜ[S] b i) ∈
        Submodule.span S'
          (Set.range fun j : ι => KaehlerDifferential.map k k S S' (b j)) := by
      rw [KaehlerDifferential.mapBaseChange_tmul, one_smul]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact h1
  intro x _
  obtain ⟨y, rfl⟩ := hsurj x
  exact hle (hspan Submodule.mem_top)


end

noncomputable def inducedBasis (b : Module.Basis ι S (KaehlerDifferential k S)) :
    Module.Basis ι S' (KaehlerDifferential k S') :=
  Module.Basis.mk (linearIndependent_kaehlerMap_basis_consolidated26 k ι S S' b) (top_le_span_kaehlerMap_basis_consolidated26 k ι S S' b)

@[simp]
theorem inducedBasis_apply (b : Module.Basis ι S (KaehlerDifferential k S)) (i : ι) :
    inducedBasis k ι S S' b i = KaehlerDifferential.map k k S S' (b i) :=
  Module.Basis.mk_apply (linearIndependent_kaehlerMap_basis_consolidated26 k ι S S' b)
    (top_le_span_kaehlerMap_basis_consolidated26 k ι S S' b) i

theorem inducedBasis_apply_D (b : Module.Basis ι S (KaehlerDifferential k S)) (x : ι → S)
    (hx : ∀ i : ι, b i = KaehlerDifferential.D k S (x i)) (i : ι) :
    inducedBasis k ι S S' b i = KaehlerDifferential.D k S' (algebraMap S S' (x i)) := by
  rw [inducedBasis_apply, hx i, KaehlerDifferential.map_D]

end

end JacobianCriterion
end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalParameters
section
open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution

private noncomputable def residueFieldExtension (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [Algebra k (IsLocalRing.ResidueField A)]
    [IsScalarTower k A (IsLocalRing.ResidueField A)] :
    Algebra.Extension k (IsLocalRing.ResidueField A) :=
  { Ring := A
    σ := Function.surjInv (Ideal.Quotient.mk_surjective :
      Function.Surjective (algebraMap A (IsLocalRing.ResidueField A)))
    algebraMap_σ := Function.surjInv_eq _ }

section
variable (A : Type*) [CommRing A] [IsLocalRing A]

private theorem one_tmul_residueField_surjective_consolidated4 (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Surjective (fun x : M => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a x =>
      obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective a
      refine ⟨a₀ • x, ?_⟩
      have h1 : (a₀ • (1 : IsLocalRing.ResidueField A)) = IsLocalRing.residue A a₀ := by
        rw [Algebra.smul_def, mul_one]; rfl
      show (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (a₀ • x) = _
      rw [← TensorProduct.smul_tmul, h1]
  | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      refine ⟨u + v, ?_⟩
      show (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (u + v) = _
      rw [TensorProduct.tmul_add]
      rw [show (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] u = x from hu,
        show (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] v = y from hv]

private theorem tmul_eq_zero_of_toCotangent_eq_zero_consolidated4 (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) (x : ↥I)
    (hx : I.toCotangent x = 0) :
    (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x
      = (0 : IsLocalRing.ResidueField A ⊗[A] ↥I) := by
  rw [Ideal.toCotangent_eq_zero] at hx
  have key : ∀ t : A, t ∈ I ^ 2 →
      t ∈ I ∧ ∀ ht : t ∈ I, (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (⟨t, ht⟩ : ↥I) = 0 := by
    intro t ht
    rw [sq] at ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro a ha b hb
      refine ⟨Ideal.mul_mem_right _ _ ha, ?_⟩
      intro hab
      have h2 : (⟨a * b, hab⟩ : ↥I) = a • (⟨b, hb⟩ : ↥I) := by
        ext
        simp [smul_eq_mul]
      have h3 : a • (1 : IsLocalRing.ResidueField A) = 0 := by
        rw [Algebra.smul_def, mul_one]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (hI ha)
      rw [h2, ← TensorProduct.smul_tmul, h3, TensorProduct.zero_tmul]
    · rintro u v ⟨hu, hu2⟩ ⟨hv, hv2⟩
      refine ⟨Ideal.add_mem _ hu hv, ?_⟩
      intro huv
      have h4 : (⟨u + v, huv⟩ : ↥I) = (⟨u, hu⟩ : ↥I) + ⟨v, hv⟩ := rfl
      rw [h4, TensorProduct.tmul_add, hu2, hv2, add_zero]
  exact (key x hx).2 x.2


end

private noncomputable def kerToTensorResidueField (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    [IsLocalRing A] :
    ↥(RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))) →ₗ[A]
      IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A :=
  KaehlerDifferential.kerToTensor k A (IsLocalRing.ResidueField A)

private theorem dTensor_apply_consolidated4 (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    [IsLocalRing A] (x : ↥(RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)))) :
    kerToTensorResidueField k A x
      = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (x : A)) := rfl

section
variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A] [IsLocalRing A] [Algebra k (IsLocalRing.ResidueField A)] [IsScalarTower k A (IsLocalRing.ResidueField A)] [Algebra.FormallySmooth k A] [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)]

private theorem mem_ker_sq_of_tmul_D_eq_zero_consolidated4 (x : ↥(RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))))
    (hx : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (x : A))
      = (0 : IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A)) :
    (x : A) ∈ (RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))) ^ 2 := by
  have : Algebra.FormallySmooth k (residueFieldExtension k A).Ring :=
    inferInstanceAs (Algebra.FormallySmooth k A)
  have hs0 : Subsingleton (Algebra.H1Cotangent k (IsLocalRing.ResidueField A)) :=
    Algebra.FormallySmooth.subsingleton_h1Cotangent
  have hsub : Subsingleton (residueFieldExtension k A).H1Cotangent :=
    (Algebra.Extension.equivH1CotangentOfFormallySmooth (residueFieldExtension k A)).toEquiv.subsingleton
  have hsub2 : Subsingleton ↥(LinearMap.ker (residueFieldExtension k A).cotangentComplex) := hsub
  have hbot : LinearMap.ker (residueFieldExtension k A).cotangentComplex = ⊥ :=
    Submodule.eq_bot_of_subsingleton
  have hx2 : (x : A) ∈ (residueFieldExtension k A).ker := x.2
  have h0 : (residueFieldExtension k A).cotangentComplex
      (Algebra.Extension.Cotangent.mk ⟨(x : A), hx2⟩) = 0 := by
    rw [Algebra.Extension.cotangentComplex_mk]
    exact hx
  have hinj := LinearMap.ker_eq_bot.mp hbot
  have h1 : Algebra.Extension.Cotangent.mk (⟨(x : A), hx2⟩ : (residueFieldExtension k A).ker) = 0 :=
    hinj (by rw [h0, map_zero])
  rw [Algebra.Extension.Cotangent.mk_eq_zero_iff] at h1
  exact h1

private theorem injective_liftBaseChange_dTensor_consolidated4 :
    Function.Injective (LinearMap.liftBaseChange (IsLocalRing.ResidueField A)
      (kerToTensorResidueField k A)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨x, rfl⟩ := one_tmul_residueField_surjective_consolidated4 A
    (↥(RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)))) z
  have h1 : LinearMap.liftBaseChange (IsLocalRing.ResidueField A) (kerToTensorResidueField k A)
      ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x)
      = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (x : A)) := by
    rw [LinearMap.liftBaseChange_tmul, one_smul, dTensor_apply_consolidated4]
  have h2 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (x : A))
      = (0 : IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A) := by
    rw [← h1]; exact hz
  have h3 : (x : A) ∈ (RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))) ^ 2 :=
    mem_ker_sq_of_tmul_D_eq_zero_consolidated4 k A x h2
  have hle : RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))
      ≤ IsLocalRing.maximalIdeal A := by
    intro a ha
    have ha' : algebraMap A (IsLocalRing.ResidueField A) a = 0 := ha
    exact Ideal.Quotient.eq_zero_iff_mem.mp ha'
  refine tmul_eq_zero_of_toCotangent_eq_zero_consolidated4 A
    (RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))) hle x ?_
  rw [Ideal.toCotangent_eq_zero]
  exact h3


end

section

variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A] [IsLocalRing A]
  [IsNoetherianRing A] [Algebra.FormallySmooth k A]
  [Module.Free A (KaehlerDifferential k A)] [Module.Finite A (KaehlerDifferential k A)]
  [Algebra k (IsLocalRing.ResidueField A)]
  [IsScalarTower k A (IsLocalRing.ResidueField A)]
  [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)]

omit [IsNoetherianRing A] [Module.Free A (KaehlerDifferential k A)]
  [Module.Finite A (KaehlerDifferential k A)] in
theorem linearIndependent_tensor_D_of_ker {ι : Type*}
    (m : ι → (RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)) : Ideal A))
    (hm : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (m i))) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A ((m i : A)))) := by
  classical
  have hT0 : LinearMap.ker (LinearMap.liftBaseChange (IsLocalRing.ResidueField A)
      (kerToTensorResidueField k A)) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (injective_liftBaseChange_dTensor_consolidated4 k A)
  have hmain := hm.map' (LinearMap.liftBaseChange (IsLocalRing.ResidueField A)
      (kerToTensorResidueField k A)) hT0
  have heq : (⇑(LinearMap.liftBaseChange (IsLocalRing.ResidueField A) (kerToTensorResidueField k A)) ∘
      fun i : ι => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (m i))
      = fun i : ι =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A ((m i : A))) := by
    funext i
    simp only [Function.comp_apply, LinearMap.liftBaseChange_tmul, one_smul, dTensor_apply_consolidated4]
  rw [heq] at hmain
  exact hmain

omit [IsNoetherianRing A] [Module.Free A (KaehlerDifferential k A)]
  [Module.Finite A (KaehlerDifferential k A)] in
private theorem linearIndependent_tensor_D_of_ideal_eq_ker_consolidated4 {ι : Type*} (I : Ideal A)
    (hI : I = RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)))
    (m : ι → ↥I)
    (hm : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (m i))) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A ((m i : A)))) := by
  subst hI
  exact linearIndependent_tensor_D_of_ker k A m hm

omit [IsNoetherianRing A] [Module.Free A (KaehlerDifferential k A)]
  [Module.Finite A (KaehlerDifferential k A)] in
theorem linearIndependent_tensor_D_of_maximalIdeal {ι : Type*}
    (m : ι → (IsLocalRing.maximalIdeal A : Ideal A))
    (hm : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (m i))) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A ((m i : A)))) :=
  linearIndependent_tensor_D_of_ideal_eq_ker_consolidated4 k A (IsLocalRing.maximalIdeal A)
    (Ideal.mk_ker).symm m hm

omit [Module.Free A (KaehlerDifferential k A)] [Module.Finite A (KaehlerDifferential k A)] in
theorem exists_local_parameters :
    ∃ (h : ℕ) (y : Fin h → A),
      Ideal.span (Set.range y) = IsLocalRing.maximalIdeal A ∧
      LinearIndependent (IsLocalRing.ResidueField A)
        (fun i : Fin h =>
          (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (y i))) := by
  classical
  have hfin : Module.Finite A ↥(IsLocalRing.maximalIdeal A) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  have hfin2 : Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A)) := inferInstance
  obtain ⟨y, hy⟩ : ∃ y : Fin (Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A))) →
      ↥(IsLocalRing.maximalIdeal A),
      ∀ i, (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (y i)
        = Module.finBasis (IsLocalRing.ResidueField A)
            (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A)) i := by
    choose y hy using fun i => one_tmul_residueField_surjective_consolidated4 A (↥(IsLocalRing.maximalIdeal A))
      (Module.finBasis (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A)) i)
    exact ⟨y, hy⟩
  have hspan : Submodule.span A (Set.range y) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis y
      (Module.finBasis (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A)))
      (fun i => hy i)
  refine ⟨_, fun i => ((y i : A)), ?_, ?_⟩
  · have h3 := congrArg (Submodule.map (IsLocalRing.maximalIdeal A).subtype) hspan
    rw [Submodule.map_span, Submodule.map_subtype_top] at h3
    have himg : ((IsLocalRing.maximalIdeal A).subtype '' Set.range y)
        = Set.range (fun i => ((y i : A))) := by
      ext t
      simp
    rw [himg] at h3
    exact h3
  · have hfun : (fun i => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (y i))
        = ⇑(Module.finBasis (IsLocalRing.ResidueField A)
            (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A))) := funext hy
    refine linearIndependent_tensor_D_of_maximalIdeal k A y ?_
    rw [hfun]
    exact Module.Basis.linearIndependent _

theorem exists_local_parameters_and_dual_derivations :
    ∃ (h : ℕ) (y : Fin h → A) (δ : Fin h → Derivation k A A),
      Ideal.span (Set.range y) = IsLocalRing.maximalIdeal A ∧
      ∀ i j : Fin h, δ i (y j) = if i = j then 1 else 0 := by
  classical
  obtain ⟨h, y, hspan, hind⟩ := exists_local_parameters k A
  obtain ⟨v, hv⟩ : ∃ v : Fin h → (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A),
      v = fun i => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (y i)) :=
    ⟨_, rfl⟩
  rw [← hv] at hind
  have hψ : ∀ i : Fin h, ∃ ψ : (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A)
      →ₗ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField A,
      ∀ j, ψ (v j) = if i = j then 1 else 0 := by
    intro i
    obtain ⟨g, hg⟩ := LinearMap.exists_extend
      ((Finsupp.lapply i).comp (hind.repr : _ →ₗ[IsLocalRing.ResidueField A] _))
    refine ⟨g, fun j => ?_⟩
    have hmem : v j ∈ Submodule.span (IsLocalRing.ResidueField A) (Set.range v) :=
      Submodule.subset_span (Set.mem_range_self j)
    have h1 : hind.repr ⟨v j, hmem⟩ = Finsupp.single j 1 := hind.repr_eq_single j _ rfl
    have h2 := LinearMap.congr_fun hg ⟨v j, hmem⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      h1, Finsupp.lapply_apply, Finsupp.single_apply] at h2
    rw [h2]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  choose ψ hψ' using hψ
  simp only [hv] at hψ'
  have hsurj : Function.Surjective (algebraMap A (IsLocalRing.ResidueField A)) :=
    Ideal.Quotient.mk_surjective
  have hσ : ∀ c, algebraMap A (IsLocalRing.ResidueField A) (Function.surjInv hsurj c) = c :=
    Function.surjInv_eq hsurj
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin h → (KaehlerDifferential k A →ₗ[A] A),
      ∀ i j, φ i (Module.Free.chooseBasis A (KaehlerDifferential k A) j)
        = Function.surjInv hsurj (ψ i ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
            (Module.Free.chooseBasis A (KaehlerDifferential k A) j))) :=
    ⟨fun i => (Module.Free.chooseBasis A (KaehlerDifferential k A)).constr A
        (fun j => Function.surjInv hsurj (ψ i ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          (Module.Free.chooseBasis A (KaehlerDifferential k A) j)))),
      fun i j => by simp⟩
  have hres : ∀ (i : Fin h) (ω : KaehlerDifferential k A),
      algebraMap A (IsLocalRing.ResidueField A) (φ i ω)
        = ψ i ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] ω) := by
    intro i
    have hmaps : (Algebra.linearMap A (IsLocalRing.ResidueField A)).comp (φ i)
        = ((ψ i).restrictScalars A).comp
            (TensorProduct.mk A (IsLocalRing.ResidueField A) (KaehlerDifferential k A) 1) := by
      refine (Module.Free.chooseBasis A (KaehlerDifferential k A)).ext (fun j => ?_)
      simp only [LinearMap.comp_apply, Algebra.linearMap_apply, hφ, hσ,
        LinearMap.coe_restrictScalars, TensorProduct.mk_apply]
    intro ω
    have hh := LinearMap.congr_fun hmaps ω
    simpa using hh
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin h) (Fin h) A,
      M = Matrix.of fun i j => φ i (KaehlerDifferential.D k A (y j)) := ⟨_, rfl⟩
  have hMapp : ∀ a b, M a b = φ a (KaehlerDifferential.D k A (y b)) := by
    intro a b; rw [hMdef]; rfl
  have hMres : ∀ a b, algebraMap A (IsLocalRing.ResidueField A) (M a b)
      = if a = b then 1 else 0 := by
    intro a b
    rw [hMapp, hres a, hψ' a b]
  have hmapM : M.map (algebraMap A (IsLocalRing.ResidueField A)) = 1 := by
    ext a b
    rw [Matrix.map_apply, hMres, Matrix.one_apply]
  have hdet1 : algebraMap A (IsLocalRing.ResidueField A) M.det = 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmapM, Matrix.det_one]
  have hdet : IsUnit M.det := by
    by_contra hcon
    have h1 : Ideal.span ({M.det} : Set A) ≠ ⊤ := fun hq =>
      hcon (Ideal.span_singleton_eq_top.mp hq)
    have hmem : M.det ∈ IsLocalRing.maximalIdeal A :=
      IsLocalRing.le_maximalIdeal h1 (Ideal.mem_span_singleton_self _)
    have hzero : algebraMap A (IsLocalRing.ResidueField A) M.det = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [hdet1] at hzero
    exact one_ne_zero hzero
  have hinvMul : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
  refine ⟨h, y, fun i => (∑ l : Fin h, (M⁻¹ i l) • φ l).compDer (KaehlerDifferential.D k A),
    hspan, ?_⟩
  intro i j
  have hsum : (∑ l : Fin h, M⁻¹ i l * M l j) = if i = j then 1 else 0 := by
    rw [← Matrix.mul_apply, hinvMul, Matrix.one_apply]
  show (∑ l : Fin h, (M⁻¹ i l) • φ l) (KaehlerDifferential.D k A (y j)) = if i = j then 1 else 0
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  calc (∑ l : Fin h, M⁻¹ i l * φ l (KaehlerDifferential.D k A (y j)))
      = ∑ l : Fin h, M⁻¹ i l * M l j := by
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [hMapp]
    _ = if i = j then 1 else 0 := hsum

end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothEtaleChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

namespace SmoothEtaleChart

private theorem exists_etale_mvPolynomial_ulift_consolidated6 {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}
    (g : MvPolynomial (Fin n) R →+* S) (hg : g.Etale) (f : R →+* S)
    (hf : g.comp MvPolynomial.C = f) :
    ∃ g' : MvPolynomial (ULift.{u} (Fin n)) R →+* S,
      g'.comp MvPolynomial.C = f ∧ g'.Etale := by
  set E : MvPolynomial (ULift.{u} (Fin n)) R ≃+* MvPolynomial (Fin n) R :=
    (MvPolynomial.renameEquiv R (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n)).toRingEquiv with hE
  refine ⟨g.comp E.toRingHom, ?_, RingHom.Etale.respectsIso.right g E hg⟩
  refine RingHom.ext fun a => ?_
  have h1 : E (MvPolynomial.C a) = MvPolynomial.C a := by
    simp [hE]
  have h2 : g (MvPolynomial.C a) = f a := by rw [← hf]; rfl
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, h1, h2]

private theorem exists_etale_over_affineSpace_of_isStandardSmooth_consolidated6 {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (hφ : RingHom.IsStandardSmooth (CommRingCat.Hom.hom φ)) :
    ∃ (d : ℕ) (g : Spec S ⟶ AffineSpace (ULift.{u} (Fin d)) (Spec R)),
      Etale g ∧
        g ≫ (AffineSpace (ULift.{u} (Fin d)) (Spec R) ↘ Spec R) = Spec.map φ := by
  obtain ⟨n, gr, hgrC, hgrEt⟩ := hφ.exists_etale_mvPolynomial
  obtain ⟨g', hg'C, hg'Et⟩ := exists_etale_mvPolynomial_ulift_consolidated6 gr hgrEt _ hgrC
  have hSpecEt : Etale (Spec.map (CommRingCat.ofHom g')) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact hg'Et
  have hcomp : CommRingCat.ofHom (MvPolynomial.C :
      ↑R →+* MvPolynomial (ULift.{u} (Fin n)) ↑R) ≫ CommRingCat.ofHom g' = φ :=
    CommRingCat.hom_ext hg'C
  refine ⟨n, Spec.map (CommRingCat.ofHom g') ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin n)) R).inv, inferInstance, ?_⟩
  rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
  exact congrArg Spec.map hcomp

section
variable {X Y : Scheme.{u}} (h : Y ⟶ X) {W : X.Opens} {V : Y.Opens} (hW : IsAffineOpen W) (hV : IsAffineOpen V) (e : V ≤ h ⁻¹ᵁ W)
include hW hV

private theorem resLE_eq_isoSpec_conj_SpecMap_appLE_consolidated6 :
    hV.isoSpec.hom ≫ Spec.map (h.appLE W V e) ≫ hW.isoSpec.inv = h.resLE W V e := by
  rw [← cancel_mono W.ι, Scheme.Hom.resLE_comp_ι]
  simp only [Category.assoc]
  rw [hW.isoSpec_inv_ι, IsAffineOpen.SpecMap_appLE_fromSpec h hW hV e, ← hV.isoSpec_inv_ι]
  simp

private theorem exists_etale_over_affineSpace_resLE_of_isStandardSmooth_consolidated6 (hstd : RingHom.IsStandardSmooth (CommRingCat.Hom.hom (h.appLE W V e))) :
    ∃ (d : ℕ) (g : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) W.toScheme),
      Etale g ∧
        g ≫ (AffineSpace (ULift.{u} (Fin d)) W.toScheme ↘ W.toScheme) = h.resLE W V e := by
  obtain ⟨d, g₀, hg₀et, hg₀⟩ :=
    exists_etale_over_affineSpace_of_isStandardSmooth_consolidated6 (h.appLE W V e) hstd
  have := hg₀et
  have : IsIso (AffineSpace.map (ULift.{u} (Fin d)) hW.isoSpec.inv) :=
    ⟨⟨AffineSpace.map (ULift.{u} (Fin d)) hW.isoSpec.hom, by
        rw [← AffineSpace.map_comp, Iso.inv_hom_id, AffineSpace.map_id], by
        rw [← AffineSpace.map_comp, Iso.hom_inv_id, AffineSpace.map_id]⟩⟩
  have : Etale hV.isoSpec.hom := inferInstance
  have : Etale (AffineSpace.map (ULift.{u} (Fin d)) hW.isoSpec.inv) := inferInstance
  refine ⟨d, hV.isoSpec.hom ≫ g₀ ≫ AffineSpace.map (ULift.{u} (Fin d)) hW.isoSpec.inv,
    inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, AffineSpace.map_over, ← Category.assoc g₀, hg₀]
  exact resLE_eq_isoSpec_conj_SpecMap_appLE_consolidated6 h hW hV e


end

private theorem smooth_resLE_consolidated6 {X Y : Scheme.{u}} (h : Y ⟶ X) [Smooth h] (W : X.Opens)
    (V : Y.Opens) (e : V ≤ h ⁻¹ᵁ W) : Smooth (h.resLE W V e) := by
  rw [HasRingHomProperty.iff_appLE (P := @Smooth)]
  intro U U' e'
  rw [Scheme.Hom.resLE_appLE]
  exact HasRingHomProperty.appLE @Smooth h ‹Smooth h›
    ⟨W.ι ''ᵁ U.1, U.2.image_of_isOpenImmersion _⟩
    ⟨V.ι ''ᵁ U'.1, U'.2.image_of_isOpenImmersion _⟩ _

section
variable {X Y : Scheme.{u}} (h : Y ⟶ X) [Smooth h] (y : Y) (W₀ : X.Opens) (hW₀ : h.base y ∈ W₀) (V₀ : Y.Opens) (hV₀ : y ∈ V₀)
include hW₀ hV₀

private theorem exists_affineOpen_etale_over_affineSpace_resLE_le_consolidated6 :
    ∃ (W : X.Opens) (V : Y.Opens) (d : ℕ) (e : V ≤ h ⁻¹ᵁ W),
      IsAffineOpen W ∧ IsAffineOpen V ∧ y ∈ V ∧ W ≤ W₀ ∧ V ≤ V₀ ∧
      ∃ g : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) W.toScheme,
        Etale g ∧
        g ≫ (AffineSpace (ULift.{u} (Fin d)) W.toScheme ↘ W.toScheme) = h.resLE W V e := by
  have e₀ : (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens) ≤ h ⁻¹ᵁ W₀ := inf_le_right
  have hy' : y ∈ (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens) := ⟨hV₀, hW₀⟩
  have : Smooth (h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀) := smooth_resLE_consolidated6 h W₀ _ e₀
  obtain ⟨W', hW', V', hV', hyV', e', hstd⟩ :=
    Smooth.exists_isStandardSmooth (h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀) ⟨y, hy'⟩
  have h1 : h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀ ≫ W₀.ι = (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ≫ h := by
    rw [Scheme.Hom.resLE_comp_ι]
  have hb : ∀ z : ↥(V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens),
      h.base ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι.base z)
        = W₀.ι.base ((h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀).base z) := by
    intro z
    exact (congrArg (fun m : (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).toScheme ⟶ X => m.base z) h1).symm
  have hWle : (W₀.ι ''ᵁ W' : X.Opens) ≤ W₀ := by
    rintro x ⟨z, -, rfl⟩
    exact z.2
  have hVle : ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V' : Y.Opens) ≤ V₀ := by
    rintro x ⟨z, -, rfl⟩
    exact z.2.1
  have e : ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V' : Y.Opens) ≤ h ⁻¹ᵁ (W₀.ι ''ᵁ W') := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨(h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀).base z, e' hz, (hb z).symm⟩
  have hWaff : IsAffineOpen (W₀.ι ''ᵁ W' : X.Opens) := hW'.image_of_isOpenImmersion W₀.ι
  have hVaff : IsAffineOpen ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V' : Y.Opens) :=
    hV'.image_of_isOpenImmersion _
  have happ : (h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀).appLE W' V' e'
      = h.appLE (W₀.ι ''ᵁ W') ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V') e :=
    Scheme.Hom.resLE_appLE h e₀ W' V' e'
  rw [happ] at hstd
  obtain ⟨d, g, hg, hgπ⟩ := exists_etale_over_affineSpace_resLE_of_isStandardSmooth_consolidated6 h hWaff hVaff e hstd
  exact ⟨W₀.ι ''ᵁ W', (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V', d, e, hWaff, hVaff,
    ⟨⟨y, hy'⟩, hyV', rfl⟩, hWle, hVle, g, hg, hgπ⟩

theorem exists_isAffineOpen_etale_resLE_le :
    ∃ (W : X.Opens) (V : Y.Opens) (d : ℕ) (e : V ≤ h ⁻¹ᵁ W),
      IsAffineOpen W ∧ IsAffineOpen V ∧ y ∈ V ∧ W ≤ W₀ ∧ V ≤ V₀ ∧
      ∃ g : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) W.toScheme,
        Etale g ∧
        g ≫ (AffineSpace (ULift.{u} (Fin d)) W.toScheme ↘ W.toScheme) = h.resLE W V e :=
  exists_affineOpen_etale_over_affineSpace_resLE_le_consolidated6 h y W₀ hW₀ V₀ hV₀


end

end SmoothEtaleChart

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
section
open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

section

section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {ι : Type*}

private theorem exists_minimal_spanning_finset_consolidated51 [DecidableEq ι] (C : Set V) (bb : ι → V) :
    ∀ (n : ℕ) (J : Finset ι), J.card ≤ n →
      Submodule.span K (C ∪ bb '' (↑J : Set ι)) = ⊤ →
      ∃ J' : Finset ι, Submodule.span K (C ∪ bb '' (↑J' : Set ι)) = ⊤ ∧
        ∀ j ∈ J', Submodule.span K (C ∪ bb '' (↑(J'.erase j) : Set ι)) ≠ ⊤ := by
  intro n
  induction n with
  | zero =>
      intro J hcard hJ
      refine ⟨J, hJ, fun j hj => ?_⟩
      have hpos : 0 < J.card := Finset.card_pos.mpr ⟨j, hj⟩
      exact absurd hcard (by omega)
  | succ n ih =>
      intro J hcard hJ
      by_cases hs : ∃ j ∈ J, Submodule.span K (C ∪ bb '' (↑(J.erase j) : Set ι)) = ⊤
      · obtain ⟨j, hjJ, hPj⟩ := hs
        refine ih (J.erase j) ?_ hPj
        have hce : (J.erase j).card = J.card - 1 := Finset.card_erase_of_mem hjJ
        omega
      · push Not at hs
        exact ⟨J, hJ, hs⟩

private theorem span_union_image_erase_eq_top_consolidated51 [DecidableEq ι] {C : Set V} {bb : ι → V} {J : Finset ι} {j0 : ι}
    (hJtop : Submodule.span K (C ∪ bb '' (↑J : Set ι)) = ⊤)
    (hb : bb j0 ∈ Submodule.span K (C ∪ bb '' (↑(J.erase j0) : Set ι))) :
    Submodule.span K (C ∪ bb '' (↑(J.erase j0) : Set ι)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hJtop, Submodule.span_le]
  rintro v (hv | ⟨j, hj, rfl⟩)
  · exact Submodule.subset_span (Set.mem_union_left _ hv)
  · by_cases hjj : j = j0
    · rw [hjj]
      exact hb
    · exact Submodule.subset_span (Set.mem_union_right _
        ⟨j, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hjj, Finset.mem_coe.mp hj⟩), rfl⟩)

theorem exists_basis_sum_of_linearIndependent [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (h : ℕ)
    (c : Fin h → V) (hc : LinearIndependent K c) :
    ∃ (J : Finset ι) (B : Module.Basis (Fin h ⊕ {j : ι // j ∈ J}) K V),
      (∀ i : Fin h, B (Sum.inl i) = c i) ∧
        ∀ j : {j : ι // j ∈ J}, B (Sum.inr j) = b (j : ι) := by
  classical
  have hPuniv : Submodule.span K
      (Set.range c ∪ (⇑b) '' (↑(Finset.univ : Finset ι) : Set ι)) = ⊤ := by
    refine le_antisymm le_top ?_
    have hsub : Set.range (⇑b) ⊆ Set.range c ∪ (⇑b) '' (↑(Finset.univ : Finset ι) : Set ι) := by
      rintro _ ⟨i, rfl⟩
      exact Set.mem_union_right _ ⟨i, Finset.mem_coe.mpr (Finset.mem_univ i), rfl⟩
    calc (⊤ : Submodule K V) = Submodule.span K (Set.range (⇑b)) := b.span_eq.symm
      _ ≤ _ := Submodule.span_mono hsub
  obtain ⟨J, hJtop, hJmin⟩ :=
    exists_minimal_spanning_finset_consolidated51 (K := K) (Set.range c) (⇑b)
      (Finset.univ : Finset ι).card Finset.univ le_rfl hPuniv
  have hrange : Set.range (Sum.elim c (fun j : {j : ι // j ∈ J} => b (j : ι)))
      = Set.range c ∪ (⇑b) '' (↑J : Set ι) := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      cases x with
      | inl i => exact Set.mem_union_left _ ⟨i, rfl⟩
      | inr j => exact Set.mem_union_right _ ⟨(j : ι), Finset.mem_coe.mpr j.2, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr ⟨j, Finset.mem_coe.mp hj⟩, rfl⟩
  have hli : LinearIndependent K (Sum.elim c (fun j : {j : ι // j ∈ J} => b (j : ι))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : (∑ i : Fin h, g (Sum.inl i) • c i)
        + (∑ j : {j : ι // j ∈ J}, g (Sum.inr j) • b (j : ι)) = 0 := by
      rw [Fintype.sum_sum_type] at hg
      exact hg
    have hz : ∀ j : {j : ι // j ∈ J}, g (Sum.inr j) = 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨j0, hj0⟩ := hcon
      have hsplit : (∑ j : {j : ι // j ∈ J}, g (Sum.inr j) • b (j : ι))
          = g (Sum.inr j0) • b (j0 : ι)
            + ∑ j ∈ Finset.univ.erase j0, g (Sum.inr j) • b (j : ι) :=
        (Finset.add_sum_erase Finset.univ
          (fun j : {j : ι // j ∈ J} => g (Sum.inr j) • b (j : ι)) (Finset.mem_univ j0)).symm
      rw [hsplit] at hg'
      have hA : (∑ i : Fin h, g (Sum.inl i) • c i)
          ∈ Submodule.span K (Set.range c ∪ (⇑b) '' (↑(J.erase (j0 : ι)) : Set ι)) := by
        refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
        exact Submodule.subset_span (Set.mem_union_left _ ⟨i, rfl⟩)
      have hB : (∑ j ∈ Finset.univ.erase j0, g (Sum.inr j) • b (j : ι))
          ∈ Submodule.span K (Set.range c ∪ (⇑b) '' (↑(J.erase (j0 : ι)) : Set ι)) := by
        refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
        have hne : (j : ι) ≠ (j0 : ι) := by
          intro hh
          exact (Finset.ne_of_mem_erase hj) (Subtype.ext hh)
        exact Submodule.subset_span (Set.mem_union_right _
          ⟨(j : ι), Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, j.2⟩), rfl⟩)
      have hxmem : g (Sum.inr j0) • b (j0 : ι)
          ∈ Submodule.span K (Set.range c ∪ (⇑b) '' (↑(J.erase (j0 : ι)) : Set ι)) := by
        have hid : g (Sum.inr j0) • b (j0 : ι)
            = ((∑ i : Fin h, g (Sum.inl i) • c i)
                + (g (Sum.inr j0) • b (j0 : ι)
                  + ∑ j ∈ Finset.univ.erase j0, g (Sum.inr j) • b (j : ι)))
              - (∑ i : Fin h, g (Sum.inl i) • c i)
              - ∑ j ∈ Finset.univ.erase j0, g (Sum.inr j) • b (j : ι) := by
          abel
        rw [hid, hg']
        exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.zero_mem _) hA) hB
      have hbj0 : b (j0 : ι)
          ∈ Submodule.span K (Set.range c ∪ (⇑b) '' (↑(J.erase (j0 : ι)) : Set ι)) := by
        have hsm := Submodule.smul_mem _ (g (Sum.inr j0))⁻¹ hxmem
        rwa [smul_smul, inv_mul_cancel₀ hj0, one_smul] at hsm
      exact hJmin (j0 : ι) j0.2 (span_union_image_erase_eq_top_consolidated51 hJtop hbj0)
    intro x
    cases x with
    | inl i =>
        have hzero : (∑ j : {j : ι // j ∈ J}, g (Sum.inr j) • b (j : ι)) = 0 :=
          Finset.sum_eq_zero fun j _ => by rw [hz j, zero_smul]
        rw [hzero, add_zero] at hg'
        exact Fintype.linearIndependent_iff.mp hc (fun i => g (Sum.inl i)) hg' i
    | inr j => exact hz j
  have hsp : (⊤ : Submodule K V)
      ≤ Submodule.span K (Set.range (Sum.elim c (fun j : {j : ι // j ∈ J} => b (j : ι)))) := by
    rw [hrange]
    exact le_of_eq hJtop.symm
  refine ⟨J, Module.Basis.mk hli hsp, fun i => ?_, fun j => ?_⟩
  · exact Module.Basis.mk_apply hli hsp (Sum.inl i)
  · exact Module.Basis.mk_apply hli hsp (Sum.inr j)


end

end

section

variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S] (S' : Type*) [CommRing S']
  [Algebra (MvPolynomial ι k) S] [Algebra (MvPolynomial ι k) S'] [Algebra S S']
  [IsScalarTower (MvPolynomial ι k) S S']

theorem algebraMap_coord (i : ι) :
    algebraMap S S' (coord k ι S i) = coord k ι S' i := by
  rw [coord_def, coord_def]
  exact (IsScalarTower.algebraMap_apply (MvPolynomial ι k) S S' (MvPolynomial.X i)).symm

end

section

variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
  (S : Type*) [CommRing S] (S' : Type*) [CommRing S']
  [Algebra k S] [Algebra k S'] [Algebra (MvPolynomial ι k) S] [Algebra (MvPolynomial ι k) S']
  [Algebra S S'] [IsScalarTower k (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S']
  [IsScalarTower k S S'] [IsScalarTower (MvPolynomial ι k) S S']
  [Algebra.FormallyEtale (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S']

private theorem repr_map_basisKaehler_consolidated51
    (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (S : Type*) [CommRing S] (S' : Type*) [CommRing S']
    [Algebra k S] [Algebra k S'] [Algebra (MvPolynomial ι k) S] [Algebra (MvPolynomial ι k) S']
    [Algebra S S'] [IsScalarTower k (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S']
    [IsScalarTower k S S'] [IsScalarTower (MvPolynomial ι k) S S']
    [Algebra.FormallyEtale (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S']
    (ω : KaehlerDifferential k S) (i : ι) :
    (basisKaehler k ι S').repr (KaehlerDifferential.map k k S S' ω) i
      = algebraMap S S' ((basisKaehler k ι S).repr ω i) := by
  have hb : ∀ j : ι, KaehlerDifferential.map k k S S' (basisKaehler k ι S j)
      = basisKaehler k ι S' j := by
    intro j
    simp only [basisKaehler_apply, KaehlerDifferential.map_D,
      algebraMap_coord]
  have hω : ω = ∑ j : ι, (basisKaehler k ι S).repr ω j • basisKaehler k ι S j :=
    ((basisKaehler k ι S).sum_repr ω).symm
  have key : KaehlerDifferential.map k k S S' ω
      = ∑ j : ι, algebraMap S S' ((basisKaehler k ι S).repr ω j) • basisKaehler k ι S' j := by
    conv_lhs => rw [hω]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [map_smul, hb j]
    exact algebra_compatible_smul S' ((basisKaehler k ι S).repr ω j) (basisKaehler k ι S' j)
  rw [key]
  simp only [Module.Basis.repr_sum_self]

theorem algebraMap_det_basisKaehler (v : ι → S) :
    algebraMap S S' ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (v i)) =
      (basisKaehler k ι S').det
        fun i : ι => KaehlerDifferential.D k S' (algebraMap S S' (v i)) := by
  have hmat : (algebraMap S S').mapMatrix
        ((basisKaehler k ι S).toMatrix fun i : ι => KaehlerDifferential.D k S (v i))
      = (basisKaehler k ι S').toMatrix
        fun i : ι => KaehlerDifferential.D k S' (algebraMap S S' (v i)) := by
    ext i j
    have h0 : KaehlerDifferential.D k S' (algebraMap S S' (v j))
        = KaehlerDifferential.map k k S S' (KaehlerDifferential.D k S (v j)) := by
      simp only [KaehlerDifferential.map_D]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, h0]
    exact (repr_map_basisKaehler_consolidated51 k ι S S' (KaehlerDifferential.D k S (v j)) i).symm
  rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det, hmat]

end

section

theorem formallyEtale_of_isUnit_det_of_eq_coord (k : Type*) [CommRing k] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (T : Type*) [CommRing T] [Algebra k T] [Algebra (MvPolynomial ι k) T]
    [IsScalarTower k (MvPolynomial ι k) T] [Algebra.FormallySmooth k T]
    (e : Module.Basis ι T (KaehlerDifferential k T)) (w : ι → T)
    (hw : ∀ i : ι, w i = JacobianCriterion.coord k ι T i)
    (hdet : IsUnit (e.det fun i : ι => KaehlerDifferential.D k T (w i))) :
    Algebra.FormallyEtale (MvPolynomial ι k) T := by
  have hfun : (fun i : ι => KaehlerDifferential.D k T (JacobianCriterion.coord k ι T i)) =
      fun i : ι => KaehlerDifferential.D k T (w i) := by
    funext i
    rw [hw i]
  have h : IsUnit (e.det fun i : ι =>
      KaehlerDifferential.D k T (JacobianCriterion.coord k ι T i)) := by
    rw [hfun]
    exact hdet
  exact JacobianCriterion.formallyEtale_of_isUnit_det k ι T e h

theorem formallyEtale_aeval_of_isUnit_det {k : Type*} [CommRing k] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {T : Type*} [CommRing T] [Algebra k T] [Algebra.FormallySmooth k T]
    (e : Module.Basis ι T (KaehlerDifferential k T)) (w : ι → T)
    (hdet : IsUnit (e.det fun i : ι => KaehlerDifferential.D k T (w i))) :
    letI : Algebra (MvPolynomial ι k) T :=
      (MvPolynomial.aeval w : MvPolynomial ι k →ₐ[k] T).toRingHom.toAlgebra
    Algebra.FormallyEtale (MvPolynomial ι k) T := by
  let instAeval : Algebra (MvPolynomial ι k) T :=
    (MvPolynomial.aeval w : MvPolynomial ι k →ₐ[k] T).toRingHom.toAlgebra
  have hmap : ∀ p : MvPolynomial ι k,
      algebraMap (MvPolynomial ι k) T p = MvPolynomial.aeval w p := fun _ => rfl
  have instTower : IsScalarTower k (MvPolynomial ι k) T :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [hmap, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C]
  show Algebra.FormallyEtale (MvPolynomial ι k) T
  refine formallyEtale_of_isUnit_det_of_eq_coord k ι T e w (fun i => ?_) hdet
  show w i = algebraMap (MvPolynomial ι k) T (MvPolynomial.X i)
  rw [hmap, MvPolynomial.aeval_X]

end

section

theorem span_range_eq_span_range_of_eq_mul_isUnit {A : Type*} [CommRing A] {n : ℕ}
    (y z c : Fin n → A) (hc : ∀ i, IsUnit (c i)) (hz : ∀ i, z i = y i * c i) :
    Ideal.span (Set.range z) = Ideal.span (Set.range y) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro w ⟨i, rfl⟩
    rw [SetLike.mem_coe, hz i]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro w ⟨i, rfl⟩
    obtain ⟨v, hv⟩ := hc i
    have hy : y i = z i * (↑v⁻¹ : A) := by
      rw [hz i, ← hv, mul_assoc, Units.mul_inv, mul_one]
    rw [SetLike.mem_coe, hy]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem exists_generators_maximalIdeal_of_linearIndependent_D (k : Type*) [CommRing k] (S : Type*) [CommRing S] [Algebra k S]
    (q : Ideal S) [q.IsPrime] (A : Type*) [CommRing A] [Algebra S A] [Algebra k A]
    [IsLocalization q.primeCompl A] [IsLocalRing A] (h : ℕ) (y : Fin h → A)
    (hspan : Ideal.span (Set.range y) = IsLocalRing.maximalIdeal A)
    (hindep : LinearIndependent (IsLocalRing.ResidueField A)
      fun i : Fin h =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (y i)) :
    ∃ s : Fin h → S,
      (∀ i : Fin h, s i ∈ q) ∧
      Ideal.span (Set.range fun i : Fin h => algebraMap S A (s i)) =
        IsLocalRing.maximalIdeal A ∧
      LinearIndependent (IsLocalRing.ResidueField A)
        fun i : Fin h =>
          (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
            KaehlerDifferential.D k A (algebraMap S A (s i)) := by
  classical
  choose p hp using fun i : Fin h =>
    IsLocalization.surj (M := q.primeCompl) (S := A) (y i)
  obtain ⟨s, c, hcu, hmul⟩ : ∃ (s : Fin h → S) (c : Fin h → A),
      (∀ i, IsUnit (c i)) ∧ ∀ i, algebraMap S A (s i) = y i * c i :=
    ⟨fun i => (p i).1, fun i => algebraMap S A ((p i).2 : S),
      fun i => IsLocalization.map_units (M := q.primeCompl) (S := A) ((p i).2),
      fun i => (hp i).symm⟩
  have hymem : ∀ i : Fin h, y i ∈ IsLocalRing.maximalIdeal A := by
    intro i
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  refine ⟨s, ?_, ?_, ?_⟩
  · intro i
    by_contra hni
    have hunit : IsUnit (algebraMap S A (s i)) :=
      IsLocalization.map_units (M := q.primeCompl) (S := A) ⟨s i, hni⟩
    have hmem : algebraMap S A (s i) ∈ IsLocalRing.maximalIdeal A := by
      rw [hmul i]
      exact Ideal.mul_mem_right _ _ (hymem i)
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem) hunit
  · refine Eq.trans ?_ hspan
    exact span_range_eq_span_range_of_eq_mul_isUnit y
      (fun i : Fin h => algebraMap S A (s i)) c hcu hmul
  · have hne : ∀ i : Fin h, IsLocalRing.residue A (c i) ≠ 0 := fun i =>
      ((hcu i).map (IsLocalRing.residue A)).ne_zero
    have hfun : (fun i : Fin h => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A (s i))) =
        fun i : Fin h => IsLocalRing.residue A (c i) •
          ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (y i)) := by
      funext i
      rw [hmul i]
      exact KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal k A (y i) (c i) (hymem i)
    have hsmul : ((fun i : Fin h => Units.mk0 (IsLocalRing.residue A (c i)) (hne i)) •
        fun i : Fin h => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (y i)) =
        fun i : Fin h => IsLocalRing.residue A (c i) •
          ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (y i)) := by
      funext i
      simp [Units.smul_def]
    have key := hindep.units_smul
      (fun i : Fin h => Units.mk0 (IsLocalRing.residue A (c i)) (hne i))
    rw [hfun, ← hsmul]
    exact key

end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.PolynomialCoordinateExtension
section
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

open MvPolynomial

section

variable (k : Type*) [CommRing k] (ι κ : Type*)

noncomputable def sumEvalIter :
    MvPolynomial (ι ⊕ κ) k →ₐ[k] MvPolynomial κ (MvPolynomial ι k) :=
  aeval (Sum.elim (fun i : ι => (C (X i) : MvPolynomial κ (MvPolynomial ι k)))
    (fun j : κ => (X j : MvPolynomial κ (MvPolynomial ι k))))

@[reducible] noncomputable def sumEvalIterAlgebra :
    Algebra (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k)) :=
  (sumEvalIter k ι κ).toRingHom.toAlgebra

end

section

variable (k : Type*) [CommRing k] (ι κ : Type*)

private noncomputable def iterToSumRingHom :
    MvPolynomial κ (MvPolynomial ι k) →+* MvPolynomial (ι ⊕ κ) k :=
  eval₂Hom (eval₂Hom (C : k →+* MvPolynomial (ι ⊕ κ) k)
      (fun i : ι => (X (Sum.inl i) : MvPolynomial (ι ⊕ κ) k)))
    (fun j : κ => (X (Sum.inr j) : MvPolynomial (ι ⊕ κ) k))

private theorem iterToSumHom_C_C_consolidated41 (a : k) :
    iterToSumRingHom k ι κ (C (C a)) = C a := by
  simp [iterToSumRingHom]

private theorem iterToSumHom_C_X_consolidated41 (i : ι) :
    iterToSumRingHom k ι κ (C (X i)) = X (Sum.inl i) := by
  simp [iterToSumRingHom]

private theorem iterToSumHom_X_consolidated41 (j : κ) :
    iterToSumRingHom k ι κ (X j) = X (Sum.inr j) := by
  simp [iterToSumRingHom]

private theorem sumEvalIter_C_consolidated41 (a : k) :
    sumEvalIter k ι κ (C a) = C (C a) := by
  simp only [sumEvalIter, MvPolynomial.aeval_C]
  rfl

private theorem sumEvalIter_X_inl_consolidated41 (i : ι) :
    sumEvalIter k ι κ (X (Sum.inl i)) = C (X i) := by
  simp [sumEvalIter]

private theorem sumEvalIter_X_inr_consolidated41 (j : κ) :
    sumEvalIter k ι κ (X (Sum.inr j)) = X j := by
  simp [sumEvalIter]

private theorem iterToSumHom_sumEvalIter_consolidated41 (p : MvPolynomial (ι ⊕ κ) k) :
    iterToSumRingHom k ι κ (sumEvalIter k ι κ p) = p := by
  induction p using MvPolynomial.induction_on
  next a => rw [sumEvalIter_C_consolidated41, iterToSumHom_C_C_consolidated41]
  next q r hq hr => simp only [map_add, hq, hr]
  next q v hq =>
    rcases v with i | j
    · simp only [map_mul, hq, sumEvalIter_X_inl_consolidated41, iterToSumHom_C_X_consolidated41]
    · simp only [map_mul, hq, sumEvalIter_X_inr_consolidated41, iterToSumHom_X_consolidated41]

private theorem sumEvalIter_iterToSumHom_C_consolidated41 (r : MvPolynomial ι k) :
    sumEvalIter k ι κ (iterToSumRingHom k ι κ (C r)) = C r := by
  induction r using MvPolynomial.induction_on
  next a => rw [iterToSumHom_C_C_consolidated41, sumEvalIter_C_consolidated41]
  next p q hp hq => simp only [map_add, hp, hq]
  next p i hp => simp only [map_mul, hp, iterToSumHom_C_X_consolidated41, sumEvalIter_X_inl_consolidated41]

private theorem sumEvalIter_iterToSumHom_consolidated41 (q : MvPolynomial κ (MvPolynomial ι k)) :
    sumEvalIter k ι κ (iterToSumRingHom k ι κ q) = q := by
  induction q using MvPolynomial.induction_on
  next r => exact sumEvalIter_iterToSumHom_C_consolidated41 k ι κ r
  next p p' hp hp' => simp only [map_add, hp, hp']
  next p j hp => simp only [map_mul, hp, iterToSumHom_X_consolidated41, sumEvalIter_X_inr_consolidated41]

private theorem bijective_sumEvalIter_consolidated41 :
    Function.Bijective (sumEvalIter k ι κ) := by
  constructor
  · exact Function.LeftInverse.injective (iterToSumHom_sumEvalIter_consolidated41 k ι κ)
  · exact fun q => ⟨iterToSumRingHom k ι κ q, sumEvalIter_iterToSumHom_consolidated41 k ι κ q⟩

attribute [local instance] sumEvalIterAlgebra

private theorem formallyEtale_sumEvalIter_consolidated41 :
    Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k)) := by
  have hb : Function.Bijective
      (algebraMap (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k))) :=
    bijective_sumEvalIter_consolidated41 k ι κ
  exact Algebra.FormallyEtale.of_equiv
    (AlgEquiv.ofBijective
      (Algebra.ofId (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k))) hb)

end

section

variable (k : Type*) [CommRing k] (ι κ : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S]

@[reducible] noncomputable def mapCoeffAlgebra :
    Algebra (MvPolynomial κ (MvPolynomial ι k)) (MvPolynomial κ S) :=
  (MvPolynomial.map (algebraMap (MvPolynomial ι k) S)).toAlgebra

attribute [local instance] mapCoeffAlgebra

theorem algebraMap_eq_mvPolynomial_map (p : MvPolynomial κ (MvPolynomial ι k)) :
    algebraMap (MvPolynomial κ (MvPolynomial ι k)) (MvPolynomial κ S) p
      = MvPolynomial.map (algebraMap (MvPolynomial ι k) S) p := rfl

end

section


private theorem formallyEtale_mvPolynomial_map_consolidated41 (R : Type u) [CommRing R] (A : Type v) [CommRing A]
    [Algebra R A] [Algebra.FormallyEtale R A] (σ : Type*) :
    @Algebra.FormallyEtale (MvPolynomial σ R) (MvPolynomial σ A) _ _
      (RingHom.toAlgebra (MvPolynomial.map (algebraMap R A))) := by
  let : Algebra (MvPolynomial σ R) (MvPolynomial σ A) :=
    RingHom.toAlgebra (MvPolynomial.map (algebraMap R A))
  have : Algebra.FormallyEtale (MvPolynomial σ R)
      (TensorProduct R (MvPolynomial σ R) A) := inferInstance
  have e : TensorProduct R (MvPolynomial σ R) A ≃ₐ[MvPolynomial σ R] MvPolynomial σ A :=
    AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.comm R (MvPolynomial σ R) A).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv R A).toRingEquiv)
      (fun p => by
        have hp : algebraMap (MvPolynomial σ R) (TensorProduct R (MvPolynomial σ R) A) p
            = p ⊗ₜ[R] (1 : A) := rfl
        have hq : algebraMap (MvPolynomial σ R) (MvPolynomial σ A) p
            = MvPolynomial.map (algebraMap R A) p := rfl
        rw [hp, hq]
        simp)
  exact Algebra.FormallyEtale.of_equiv e

end

section

variable (k : Type*) [CommRing k] (ι κ : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S]

noncomputable def sumEval : MvPolynomial (ι ⊕ κ) k →ₐ[k] MvPolynomial κ S :=
  aeval (Sum.elim (fun i : ι => (C (coord k ι S i) : MvPolynomial κ S))
    (fun j : κ => (X j : MvPolynomial κ S)))

@[reducible] noncomputable def sumEvalAlgebra :
    Algebra (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) :=
  (sumEval k ι κ S).toRingHom.toAlgebra

attribute [local instance] sumEvalAlgebra
attribute [local instance] sumEvalIterAlgebra
attribute [local instance] mapCoeffAlgebra

theorem sumEvalAlgebra_isScalarTower :
    IsScalarTower k (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) :=
  IsScalarTower.of_algebraMap_eq fun x => ((sumEval k ι κ S).commutes x).symm

theorem algebraMap_eq_sumEval (p : MvPolynomial (ι ⊕ κ) k) :
    algebraMap (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) p = sumEval k ι κ S p := rfl

@[simp] theorem algebraMap_X_inl (i : ι) :
    algebraMap (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) (X (Sum.inl i))
      = C (coord k ι S i) := by
  simp [algebraMap_eq_sumEval, sumEval]

@[simp] theorem algebraMap_X_inr (j : κ) :
    algebraMap (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) (X (Sum.inr j))
      = (X j : MvPolynomial κ S) := by
  simp [algebraMap_eq_sumEval, sumEval]

@[simp] theorem coord_inl (i : ι) :
    coord k (ι ⊕ κ) (MvPolynomial κ S) (Sum.inl i) = C (coord k ι S i) :=
  (coord_def k (ι ⊕ κ) (MvPolynomial κ S) (Sum.inl i)).trans (algebraMap_X_inl k ι κ S i)

@[simp] theorem coord_inr (j : κ) :
    coord k (ι ⊕ κ) (MvPolynomial κ S) (Sum.inr j) = (X j : MvPolynomial κ S) :=
  (coord_def k (ι ⊕ κ) (MvPolynomial κ S) (Sum.inr j)).trans (algebraMap_X_inr k ι κ S j)

private theorem algebraMap_eq_sumEvalIter_consolidated41 (p : MvPolynomial (ι ⊕ κ) k) :
    algebraMap (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k)) p
      = sumEvalIter k ι κ p := rfl

theorem mapCoeffAlgebra_isScalarTower_of_isScalarTower [IsScalarTower k (MvPolynomial ι k) S] :
    IsScalarTower k (MvPolynomial κ (MvPolynomial ι k)) (MvPolynomial κ S) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    have h1 : algebraMap k (MvPolynomial κ (MvPolynomial ι k)) x
        = C (algebraMap k (MvPolynomial ι k) x) := rfl
    have h2 : algebraMap k (MvPolynomial κ S) x = C (algebraMap k S x) := rfl
    rw [h2, h1, algebraMap_eq_mvPolynomial_map, MvPolynomial.map_C,
      IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S]

theorem mapCoeffAlgebra_isScalarTower [IsScalarTower k (MvPolynomial ι k) S] :
    IsScalarTower (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k))
      (MvPolynomial κ S) := by
  have := mapCoeffAlgebra_isScalarTower_of_isScalarTower k ι κ S
  refine IsScalarTower.of_algebraMap_eq' ?_
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
  · simp only [algebraMap_eq_sumEval, RingHom.comp_apply, algebraMap_eq_sumEvalIter_consolidated41,
      sumEval, sumEvalIter, MvPolynomial.aeval_C]
    exact IsScalarTower.algebraMap_apply k (MvPolynomial κ (MvPolynomial ι k)) (MvPolynomial κ S) r
  · rcases v with i | j <;>
      simp [RingHom.comp_apply, algebraMap_eq_sumEval, algebraMap_eq_sumEvalIter_consolidated41,
        sumEval, sumEvalIter, algebraMap_eq_mvPolynomial_map, coord_def]

theorem formallyEtale_mvPolynomial_sum [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S] :
    Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) := by
  have := mapCoeffAlgebra_isScalarTower_of_isScalarTower k ι κ S
  have := mapCoeffAlgebra_isScalarTower k ι κ S
  have h1 : Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k)
      (MvPolynomial κ (MvPolynomial ι k)) := formallyEtale_sumEvalIter_consolidated41 k ι κ
  have h2 : Algebra.FormallyEtale (MvPolynomial κ (MvPolynomial ι k)) (MvPolynomial κ S) :=
    formallyEtale_mvPolynomial_map_consolidated41 (MvPolynomial ι k) S κ
  exact Algebra.FormallyEtale.comp (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k))
    (MvPolynomial κ S)

variable (T : Type*) [CommRing T]

theorem formallyEtale_trans [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra (MvPolynomial κ S) T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) T]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial κ S) T] :
    Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T := by
  have := formallyEtale_mvPolynomial_sum k ι κ S
  exact Algebra.FormallyEtale.comp (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) T

end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

abbrev restrictIdeal {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens) :
    U.toScheme.IdealSheafData :=
  I.comap U.ι

section
variable {X : Scheme.{u}} (I : X.IdealSheafData)

theorem restrictIdeal_eq_comap_ι (U : X.Opens) :
    restrictIdeal I U = I.comap U.ι := rfl

theorem restrictIdeal_eq_top_iff_forall_notMem_support (U : X.Opens) :
    restrictIdeal I U = ⊤ ↔ ∀ x : X, x ∈ U → x ∉ I.support := by
  have hbot : ((⊥ : TopologicalSpace.Closeds U.toScheme) : Set U.toScheme) = ∅ := rfl
  have hbot' : ∀ A : TopologicalSpace.Closeds U.toScheme,
      (A = ⊥ ↔ ∀ y : U.toScheme, y ∉ A) := by
    intro A
    constructor
    · rintro rfl y hy
      have hy' : y ∈ ((⊥ : TopologicalSpace.Closeds U.toScheme) : Set U.toScheme) := hy
      rw [hbot] at hy'
      exact hy'
    · intro hall
      have hA : (A : Set U.toScheme) = ∅ :=
        Set.Subset.antisymm (fun y hy => absurd hy (hall y)) (Set.empty_subset _)
      exact SetLike.coe_injective (hA.trans hbot.symm)
  have key : ∀ (x : X) (hx : x ∈ U),
      ((⟨x, hx⟩ : U.toScheme) ∈ (I.comap U.ι).support ↔ x ∈ I.support) := by
    intro x hx
    simp only [Scheme.IdealSheafData.support_comap]
    rfl
  rw [restrictIdeal_eq_comap_ι]
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, hbot']
  constructor
  · intro h x hx hmem
    exact h ⟨x, hx⟩ ((key x hx).mpr hmem)
  · rintro h ⟨x, hx⟩ hy
    exact h x hx ((key x hx).mp hy)

theorem restrictIdeal_eq_comap_homOfLE_restrictIdeal {U V : X.Opens} (h : V ≤ U) :
    restrictIdeal I V = (restrictIdeal I U).comap (X.homOfLE h) := by
  have hcomp : X.homOfLE h ≫ U.ι = V.ι := by simp
  show I.comap V.ι = (I.comap U.ι).comap (X.homOfLE h)
  rw [← Scheme.IdealSheafData.comap_comp, hcomp]


end

theorem restrictIdeal_eq_of_le_of_eq {X : Scheme.{u}} {I J : X.IdealSheafData} {U V : X.Opens}
    (h : V ≤ U) (hU : restrictIdeal I U = restrictIdeal J U) :
    restrictIdeal I V = restrictIdeal J V := by
  rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal I h,
    restrictIdeal_eq_comap_homOfLE_restrictIdeal J h, hU]

theorem restrictIdeal_comap_eq_comap_resLE_restrictIdeal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    restrictIdeal (I.comap f) V = (restrictIdeal I U).comap (f.resLE U V h) := by
  have hcomp : f.resLE U V h ≫ U.ι = V.ι ≫ f := by simp
  show (I.comap f).comap V.ι = (I.comap U.ι).comap (f.resLE U V h)
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcomp]

abbrev zeroLocus {X : Scheme.{u}} (I : X.IdealSheafData) : TopologicalSpace.Closeds X :=
  I.support

def VanishesAlong {X : Scheme.{u}} (I J : X.IdealSheafData) : Prop := I ≤ J

theorem vanishesAlong_iff_le {X : Scheme.{u}} (I J : X.IdealSheafData) :
    VanishesAlong I J ↔ I ≤ J := Iff.rfl

def NonzeroOnComponents {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ T ∈ irreducibleComponents (↥X), ¬ T ⊆ (I.support : Set ↥X)

theorem nonzeroOnComponents_iff {X : Scheme.{u}} (I : X.IdealSheafData) :
    NonzeroOnComponents I ↔ ∀ T ∈ irreducibleComponents (↥X), ¬ T ⊆ (I.support : Set ↥X) :=
  Iff.rfl

def IsSmoothDivisor {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (D : X.IdealSheafData) : Prop :=
  Blowup.IsLocallyGeneratedByNonZeroDivisor D ∧ Smooth (D.subschemeι ≫ p)

theorem isSmoothDivisor_iff {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (D : X.IdealSheafData) :
    IsSmoothDivisor p D ↔
      Blowup.IsLocallyGeneratedByNonZeroDivisor D ∧ Smooth (D.subschemeι ≫ p) :=
  Iff.rfl

abbrev affineSpaceFin (k : Type u) [Field k] (m : ℕ) : Scheme.{u} :=
  AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))

abbrev affineSpaceFinToSpec (k : Type u) [Field k] (m : ℕ) :
    affineSpaceFin k m ⟶ Spec (CommRingCat.of k) :=
  (affineSpaceFin k m ↘ Spec (CommRingCat.of k))

structure EtaleChart {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (m : ℕ) : Type u where
  map : U.toScheme ⟶ affineSpaceFin k m
  comp_struct : map ≫ affineSpaceFinToSpec k m = U.ι ≫ p
  isEtale : Etale map

def coordSubspaceIdeal (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    (affineSpaceFin k m).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (Ideal.span
      ((fun i : Fin m => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
        (S : Set (Fin m))))

theorem coordSubspaceIdeal_eq_ofIdealTop_span_coord (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    coordSubspaceIdeal k m S =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span
          ((fun i : Fin m => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
            (S : Set (Fin m)))) := rfl

def EtaleChart.coordIdeal {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) : U.toScheme.IdealSheafData :=
  (coordSubspaceIdeal k m S).comap c.map

theorem EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) :
    c.coordIdeal S = (coordSubspaceIdeal k m S).comap c.map := rfl

def InStrictNormalCrossingPositionAt {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (x : X) : Prop :=
  ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m)),
    (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
    (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
    (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
      restrictIdeal (E[i]'h) U = c.coordIdeal {t})

def InStrictNormalCrossingPosition {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) : Prop :=
  (∀ D ∈ E, IsSmoothDivisor p D) ∧ ∀ x : X, InStrictNormalCrossingPositionAt p E x

theorem inStrictNormalCrossingPosition_iff {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) :
    InStrictNormalCrossingPosition p E ↔
      (∀ D ∈ E, IsSmoothDivisor p D) ∧ ∀ x : X, InStrictNormalCrossingPositionAt p E x :=
  Iff.rfl

def HasStrictNormalCrossingsWith {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData)
    (E : List X.IdealSheafData) : Prop :=
  ∀ x ∈ Z.support,
    ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
      (S : Finset (Fin m)),
      (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
      (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
        restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
      restrictIdeal Z U = c.coordIdeal S

theorem hasStrictNormalCrossingsWith_iff {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData)
    (E : List X.IdealSheafData) :
    HasStrictNormalCrossingsWith p Z E ↔
      ∀ x ∈ Z.support,
        ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
          (S : Finset (Fin m)),
          (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
          (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
          (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
            restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
          restrictIdeal Z U = c.coordIdeal S :=
  Iff.rfl

section
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}

theorem HasStrictNormalCrossingsWith.exists_etaleChart {Z : X.IdealSheafData}
    {E : List X.IdealSheafData} (h : HasStrictNormalCrossingsWith p Z E) {x : X} (hx : x ∈ Z.support) :
    ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
      (S : Finset (Fin m)),
      (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
      (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
        restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
      restrictIdeal Z U = c.coordIdeal S :=
  h x hx

theorem hasStrictNormalCrossingsWith_of_forall_exists_etaleChart {Z : X.IdealSheafData}
    {E : List X.IdealSheafData}
    (h : ∀ x ∈ Z.support,
      ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
        (S : Finset (Fin m)),
        (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
        (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
        (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
          restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
        restrictIdeal Z U = c.coordIdeal S) :
    HasStrictNormalCrossingsWith p Z E :=
  h

theorem inStrictNormalCrossingPositionAt_of_exists_etaleChart {E : List X.IdealSheafData} {x : X}
    (h : ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m)),
      (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
      (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
        restrictIdeal (E[i]'h) U = c.coordIdeal {t})) :
    InStrictNormalCrossingPositionAt p E x :=
  h

theorem InStrictNormalCrossingPositionAt.exists_etaleChart {E : List X.IdealSheafData} {x : X}
    (h : InStrictNormalCrossingPositionAt p E x) :
    ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m)),
      (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
      (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
        restrictIdeal (E[i]'h) U = c.coordIdeal {t}) :=
  h

theorem HasStrictNormalCrossingsWith.exists_etaleChart_of_cons {Z : X.IdealSheafData}
    {H : X.IdealSheafData} {E : List X.IdealSheafData}
    (h : HasStrictNormalCrossingsWith p Z (H :: E)) {x : X} (hx : x ∈ Z.support) :
    ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (S : Finset (Fin m))
      (aH : Option (Fin m)) (a : ℕ → Option (Fin m)),
      restrictIdeal Z U = c.coordIdeal S ∧
      (aH = none → restrictIdeal H U = ⊤) ∧
      (∀ t : Fin m, aH = some t → restrictIdeal H U = c.coordIdeal {t}) ∧
      (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
        restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
      (∀ i < E.length, ∀ t : Fin m, a i = some t → aH ≠ some t) ∧
      (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) := by
  obtain ⟨U, hU, m, c, a, S, h1, h2, h3, h4⟩ := h x hx
  have hzero : 0 < (H :: E).length := by simp
  refine ⟨U, hU, m, c, S, a 0, fun i => a (i + 1), h4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    have hres := h2 0 hzero h0
    simpa using hres
  · intro t ht
    have hres := h3 0 hzero t ht
    simpa using hres
  · intro i hi hni
    have hi' : i + 1 < (H :: E).length := by
      simp only [List.length_cons]; omega
    have hres := h2 (i + 1) hi' hni
    simpa using hres
  · intro i hi t ht
    have hi' : i + 1 < (H :: E).length := by
      simp only [List.length_cons]; omega
    have hres := h3 (i + 1) hi' t ht
    simpa using hres
  · intro i hi t ht hc
    have hi' : i + 1 < (H :: E).length := by
      simp only [List.length_cons]; omega
    have := h1 (i + 1) hi' 0 hzero t ht hc
    omega
  · intro i hi j hj t hti htj
    have hi' : i + 1 < (H :: E).length := by
      simp only [List.length_cons]; omega
    have hj' : j + 1 < (H :: E).length := by
      simp only [List.length_cons]; omega
    have := h1 (i + 1) hi' (j + 1) hj' t hti htj
    omega


end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AdaptedParameters
section
open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

section

section
variable (k : Type*) [CommRing k] (A : Type*) [CommRing A] [Algebra k A] [IsLocalRing A] [Algebra k (IsLocalRing.ResidueField A)] [IsScalarTower k A (IsLocalRing.ResidueField A)] [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)]

private theorem exists_section_mod_maximalIdeal_sq_consolidated83 :
    ∃ w : A → A,
      (∀ a : A, a - w a ∈ IsLocalRing.maximalIdeal A) ∧
      (∀ a b : A, w a + w b - w (a + b) ∈ IsLocalRing.maximalIdeal A ^ 2) ∧
      (∀ (c : k) (a : A), c • w a - w (c • a) ∈ IsLocalRing.maximalIdeal A ^ 2) ∧
      (∀ a b : A, w a * w b - w (a * b) ∈ IsLocalRing.maximalIdeal A ^ 2) ∧
      (∀ a : A, a ∈ IsLocalRing.maximalIdeal A → w a ∈ IsLocalRing.maximalIdeal A ^ 2) := by
  classical
  have hsq : ∀ a ∈ IsLocalRing.maximalIdeal A ^ 2,
      (IsScalarTower.toAlgHom k A (IsLocalRing.ResidueField A)) a = 0 := by
    intro a ha
    show algebraMap A (IsLocalRing.ResidueField A) a = 0
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
    exact Ideal.pow_le_self (by norm_num) ha
  obtain ⟨ρ, hρmk⟩ : ∃ ρ : (A ⧸ IsLocalRing.maximalIdeal A ^ 2) →ₐ[k]
      IsLocalRing.ResidueField A,
      ∀ a : A, ρ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ 2) a)
        = IsLocalRing.residue A a := by
    refine ⟨Ideal.Quotient.liftₐ (IsLocalRing.maximalIdeal A ^ 2)
      (IsScalarTower.toAlgHom k A (IsLocalRing.ResidueField A)) hsq, fun a => ?_⟩
    show algebraMap A (IsLocalRing.ResidueField A) a = IsLocalRing.residue A a
    rw [IsLocalRing.ResidueField.algebraMap_eq]
  have hρsurj : Function.Surjective ρ := by
    intro c
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := A) c
    exact ⟨Ideal.Quotient.mk _ a, by rw [hρmk a]; exact ha⟩
  have hker2 : RingHom.ker (ρ : (A ⧸ IsLocalRing.maximalIdeal A ^ 2) →+*
      IsLocalRing.ResidueField A) ^ 2 = ⊥ := by
    have hexp : RingHom.ker (ρ : (A ⧸ IsLocalRing.maximalIdeal A ^ 2) →+*
        IsLocalRing.ResidueField A) ^ 2
        = RingHom.ker (ρ : (A ⧸ IsLocalRing.maximalIdeal A ^ 2) →+*
            IsLocalRing.ResidueField A)
          * RingHom.ker (ρ : (A ⧸ IsLocalRing.maximalIdeal A ^ 2) →+*
            IsLocalRing.ResidueField A) := pow_two _
    rw [hexp]
    refine le_antisymm ?_ bot_le
    rw [Ideal.mul_le]
    intro u hu v hv
    have hu' : ρ u = 0 := RingHom.mem_ker.mp hu
    have hv' : ρ v = 0 := RingHom.mem_ker.mp hv
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
    have ha : a ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff, ← hρmk a]
      exact hu'
    have hb : b ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff, ← hρmk b]
      exact hv'
    refine (Submodule.mem_bot _).mpr ?_
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_two]
    exact Ideal.mul_mem_mul ha hb
  obtain ⟨σ, hσ⟩ : ∃ σ : IsLocalRing.ResidueField A →ₐ[k]
      (A ⧸ IsLocalRing.maximalIdeal A ^ 2), ∀ c, ρ (σ c) = c := by
    refine ⟨Algebra.FormallySmooth.liftOfSurjective
      (AlgHom.id k (IsLocalRing.ResidueField A)) ρ hρsurj ⟨2, hker2⟩, fun c => ?_⟩
    have h := Algebra.FormallySmooth.comp_liftOfSurjective
      (AlgHom.id k (IsLocalRing.ResidueField A)) ρ hρsurj ⟨2, hker2⟩
    have h2 := DFunLike.congr_fun h c
    simpa using h2
  obtain ⟨w, hw⟩ : ∃ w : A → A, ∀ a : A,
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ 2) (w a)
        = σ (IsLocalRing.residue A a) := by
    refine ⟨fun a => Function.surjInv Ideal.Quotient.mk_surjective
      (σ (IsLocalRing.residue A a)), fun a => ?_⟩
    exact Function.surjInv_eq Ideal.Quotient.mk_surjective _
  refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hρmk (w a), hw a,
      hσ (IsLocalRing.residue A a)]
  · intro a b
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, hw a, hw b, hw (a + b), map_add,
      map_add, sub_self]
  · intro c a
    have hres : IsLocalRing.residue A (c • a) = c • IsLocalRing.residue A a := by
      rw [Algebra.smul_def, map_mul, Algebra.smul_def,
        ← IsLocalRing.ResidueField.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply k A (IsLocalRing.ResidueField A)]
    have hmk : Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ 2) (c • w a)
        = c • Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ 2) (w a) := by
      rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply k A (A ⧸ IsLocalRing.maximalIdeal A ^ 2)]
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hw (c • a), hmk, hres, map_smul, hw a,
      sub_self]
  · intro a b
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hw a, hw b, hw (a * b), map_mul,
      map_mul, sub_self]
  · intro a ha
    have hres : IsLocalRing.residue A a = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff]
      exact ha
    rw [← Ideal.Quotient.eq_zero_iff_mem, hw a, hres, map_zero]

private theorem mem_maximalIdeal_sq_of_tmul_D_eq_zero_consolidated83 (x : A) (hx : x ∈ IsLocalRing.maximalIdeal A)
    (h0 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A x = 0) :
    x ∈ IsLocalRing.maximalIdeal A ^ 2 := by
  classical
  obtain ⟨w, h1, h2, h3, h4, h5⟩ := exists_section_mod_maximalIdeal_sq_consolidated83 k A
  have hco : ∀ (a b : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
      (hb : b ∈ IsLocalRing.maximalIdeal A),
      a - b ∈ IsLocalRing.maximalIdeal A ^ 2 →
      Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a, ha⟩
        = Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨b, hb⟩ := by
    intro a b ha hb hab
    exact (Ideal.toCotangent_eq _).mpr hab
  have hadd : ∀ a b : A,
      Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a + b - w (a + b), h1 (a + b)⟩
        = Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a - w a, h1 a⟩
          + Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨b - w b, h1 b⟩ := by
    intro a b
    rw [← map_add]
    refine hco _ _ _ _ ?_
    show a + b - w (a + b) - ((a - w a) + (b - w b)) ∈ IsLocalRing.maximalIdeal A ^ 2
    have heq : a + b - w (a + b) - ((a - w a) + (b - w b)) = w a + w b - w (a + b) := by ring
    rw [heq]
    exact h2 a b
  have hsmul : ∀ (c : k) (a : A),
      Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨c • a - w (c • a), h1 (c • a)⟩
        = (RingHom.id k) c •
          Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a - w a, h1 a⟩ := by
    intro c a
    show Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨c • a - w (c • a), h1 (c • a)⟩
      = c • Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a - w a, h1 a⟩
    rw [← algebraMap_smul A c
      (Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a - w a, h1 a⟩), ← map_smul]
    refine hco _ _ _ _ ?_
    show c • a - w (c • a) - (algebraMap k A c) • (a - w a)
      ∈ IsLocalRing.maximalIdeal A ^ 2
    have heq : c • a - w (c • a) - (algebraMap k A c) • (a - w a)
        = c • w a - w (c • a) := by
      rw [Algebra.smul_def c a, Algebra.smul_def c (w a), smul_eq_mul]
      ring
    rw [heq]
    exact h3 c a
  have hleib : ∀ a b : A,
      Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a * b - w (a * b), h1 (a * b)⟩
        = a • Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨b - w b, h1 b⟩
          + b • Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a - w a, h1 a⟩ := by
    intro a b
    rw [← map_smul, ← map_smul, ← map_add]
    refine hco _ _ _ _ ?_
    show a * b - w (a * b) - (a • (b - w b) + b • (a - w a))
      ∈ IsLocalRing.maximalIdeal A ^ 2
    have heq : a * b - w (a * b) - (a • (b - w b) + b • (a - w a))
        = -((a - w a) * (b - w b)) + (w a * w b - w (a * b)) := by
      simp only [smul_eq_mul]
      ring
    rw [heq]
    refine Submodule.add_mem _ (neg_mem ?_) (h4 a b)
    rw [pow_two]
    exact Ideal.mul_mem_mul (h1 a) (h1 b)
  obtain ⟨Dder, hDderapp⟩ : ∃ D : Derivation k A (IsLocalRing.maximalIdeal A).Cotangent,
      ∀ a : A, D a = Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a - w a, h1 a⟩ :=
    ⟨Derivation.mk'
      { toFun := fun a => Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a - w a, h1 a⟩
        map_add' := hadd
        map_smul' := hsmul } hleib, fun a => rfl⟩
  have hDx : Dder x = Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨x, hx⟩ := by
    rw [hDderapp x]
    refine hco _ _ _ _ ?_
    show x - w x - x ∈ IsLocalRing.maximalIdeal A ^ 2
    have heq : x - w x - x = -(w x) := by ring
    rw [heq]
    exact neg_mem (h5 x hx)
  let instModKappa : Module (IsLocalRing.ResidueField A)
      (IsLocalRing.maximalIdeal A).Cotangent :=
    inferInstanceAs (Module (A ⧸ IsLocalRing.maximalIdeal A) _)
  let instTowerKappa : IsScalarTower A (IsLocalRing.ResidueField A)
      (IsLocalRing.maximalIdeal A).Cotangent :=
    inferInstanceAs (IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A) _)
  have hlin := congrArg (fun z => (Dder.liftKaehlerDifferential.liftBaseChange
    (IsLocalRing.ResidueField A)) z) h0
  have hDx0 : Dder x = 0 := by
    simpa [LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D] using hlin
  have hz : Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨x, hx⟩ = 0 := by
    rw [← hDx]
    exact hDx0
  exact (Ideal.toCotangent_eq_zero _ ⟨x, hx⟩).mp hz


end

private theorem exists_fun_sum_smul_eq_of_mem_span_consolidated83 {K M : Type*} [CommRing K] [AddCommGroup M]
    [Module K M] {n : ℕ} (v : Fin n → M) {x : M}
    (hx : x ∈ Submodule.span K (Set.range v)) :
    ∃ c : Fin n → K, ∑ i, c i • v i = x := by
  classical
  let P : Submodule K M :=
    { carrier := {y : M | ∃ c : Fin n → K, ∑ i, c i • v i = y}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        intro a b ha hb
        obtain ⟨ca, hca⟩ := ha
        obtain ⟨cb, hcb⟩ := hb
        refine ⟨ca + cb, ?_⟩
        rw [← hca, ← hcb, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.add_apply, add_smul]
      smul_mem' := by
        intro r a ha
        obtain ⟨ca, hca⟩ := ha
        refine ⟨r • ca, ?_⟩
        rw [← hca, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, smul_assoc] }
  have hsub : Set.range v ⊆ (P : Set M) := by
    rintro _ ⟨i, rfl⟩
    show ∃ c : Fin n → K, ∑ j, c j • v j = v i
    refine ⟨Pi.single i 1, ?_⟩
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp
    · intro j _ hj
      simp [hj]
  exact (Submodule.span_le.mpr hsub) hx

private theorem exists_local_parameters_consolidated83 (k : Type*) [CommRing k] (A : Type*) [CommRing A]
    [Algebra k A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k (IsLocalRing.ResidueField A)]
    [IsScalarTower k A (IsLocalRing.ResidueField A)]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] :
    ∃ (h : ℕ) (y : Fin h → A),
      Ideal.span (Set.range y) = IsLocalRing.maximalIdeal A ∧
      LinearIndependent (IsLocalRing.ResidueField A)
        (fun i : Fin h => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (y i)) := by
  classical
  obtain ⟨sF, hsF0⟩ : (IsLocalRing.maximalIdeal A).FG := IsNoetherian.noetherian _
  have hsF : Ideal.span (↑sF : Set A) = IsLocalRing.maximalIdeal A := hsF0
  obtain ⟨b, hbsub, hbspan, hbind⟩ :=
    exists_linearIndependent (K := IsLocalRing.ResidueField A)
      (t := ((fun a : A => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A a) '' (↑sF : Set A)))
  have hbfin : b.Finite := Set.Finite.subset (Set.Finite.image _ sF.finite_toSet) hbsub
  let instFintypeB : Fintype b := hbfin.fintype
  choose pre hpre1 hpre2 using fun x : b => hbsub x.2
  obtain ⟨y, hy⟩ : ∃ y : Fin (Fintype.card b) → A,
      ∀ i, y i = pre ((Fintype.equivFin b).symm i) := ⟨_, fun _ => rfl⟩
  have hfun : (fun i : Fin (Fintype.card b) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      KaehlerDifferential.D k A (y i))
      = fun i : Fin (Fintype.card b) =>
        ((((Fintype.equivFin b).symm i : b) : IsLocalRing.ResidueField A ⊗[A]
          KaehlerDifferential k A)) := by
    funext i
    rw [hy i]
    exact hpre2 _
  have hind : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : Fin (Fintype.card b) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A (y i)) := by
    rw [hfun]
    exact hbind.comp _ (Fintype.equivFin b).symm.injective
  have hrange : Set.range (fun i : Fin (Fintype.card b) =>
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (y i)) = b := by
    rw [hfun]
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin b).symm i).2
    · intro hv
      exact ⟨(Fintype.equivFin b) ⟨v, hv⟩, by simp⟩
  have hymem : ∀ i, y i ∈ IsLocalRing.maximalIdeal A := by
    intro i
    rw [← hsF, hy i]
    exact Submodule.subset_span (hpre1 _)
  refine ⟨Fintype.card b, y, ?_, hind⟩
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hymem i
  · have hkey : ∀ a ∈ (↑sF : Set A),
        a ∈ Ideal.span (Set.range y) ⊔ IsLocalRing.maximalIdeal A ^ 2 := by
      intro a ha
      have hav : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A a
          ∈ Submodule.span (IsLocalRing.ResidueField A)
            (Set.range (fun i : Fin (Fintype.card b) =>
              (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
                KaehlerDifferential.D k A (y i))) := by
        rw [hrange, hbspan]
        exact Submodule.subset_span ⟨a, ha, rfl⟩
      obtain ⟨c, hc0⟩ := exists_fun_sum_smul_eq_of_mem_span_consolidated83
        (fun i : Fin (Fintype.card b) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (y i)) hav
      have hc : (∑ i, c i • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (y i)))
          = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A a := hc0
      obtain ⟨c', hc'⟩ : ∃ c' : Fin (Fintype.card b) → A,
          ∀ i, IsLocalRing.residue A (c' i) = c i := by
        have hsurj : Function.Surjective (IsLocalRing.residue A) :=
          Ideal.Quotient.mk_surjective
        choose c' hc' using fun i => hsurj (c i)
        exact ⟨c', hc'⟩
      have hsum : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (∑ i, c' i * y i)
          = ∑ i, c i • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
            KaehlerDifferential.D k A (y i)) := by
        rw [map_sum, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm (c' i) (y i),
          KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal k A (y i) (c' i) (hymem i),
          hc' i]
      have hx0 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (a - ∑ i, c' i * y i) = 0 := by
        rw [map_sub, TensorProduct.tmul_sub, hsum, hc, sub_self]
      have hxm : a - ∑ i, c' i * y i ∈ IsLocalRing.maximalIdeal A := by
        refine Submodule.sub_mem _ ?_
          (Submodule.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hymem i))
        rw [← hsF]
        exact Submodule.subset_span ha
      have hxsq := mem_maximalIdeal_sq_of_tmul_D_eq_zero_consolidated83 k A _ hxm hx0
      have hrewrite : a = (a - ∑ i, c' i * y i) + ∑ i, c' i * y i := by ring
      rw [hrewrite]
      refine Submodule.add_mem _ (Submodule.mem_sup_right hxsq) (Submodule.mem_sup_left ?_)
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    have hsmul : (IsLocalRing.maximalIdeal A • IsLocalRing.maximalIdeal A : Ideal A)
        = IsLocalRing.maximalIdeal A ^ 2 := by
      rw [Ideal.smul_eq_mul, pow_two]
    have hstep : Ideal.span (↑sF : Set A) ≤ Ideal.span (Set.range y)
        ⊔ IsLocalRing.maximalIdeal A • IsLocalRing.maximalIdeal A := by
      rw [Ideal.span_le]
      intro a ha
      rw [SetLike.mem_coe, hsmul]
      exact hkey a ha
    rw [hsF] at hstep
    have hbotne : (⊥ : Ideal A) ≠ ⊤ := by
      intro hcon
      have hmem1 : (1 : A) ∈ (⊥ : Ideal A) := by
        rw [hcon]; exact Submodule.mem_top
      simp at hmem1
    exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) hbotne).ge hstep

private theorem residue_det_ne_zero_of_basis_tmul_consolidated83 {A : Type*} [CommRing A] [IsLocalRing A]
    {M : Type*} [AddCommGroup M] [Module A M] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bA : Module.Basis ι A M) (G : ι → M)
    (B' : Module.Basis ι (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] M))
    (hB' : ∀ i, B' i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] G i) :
    IsLocalRing.residue A (bA.det G) ≠ 0 := by
  classical
  obtain ⟨bk, hbk⟩ : ∃ bk : Module.Basis ι (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] M),
      ∀ i, bk i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] bA i :=
    ⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) bA, fun i => by simp⟩
  have hkey : ∀ (c : A) (m : M), (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m)
      = IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m) := by
    intro c m
    have hA1 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m)
        = (c • (1 : IsLocalRing.ResidueField A)) ⊗ₜ[A] m := (TensorProduct.smul_tmul c 1 m).symm
    have hA2 : c • (1 : IsLocalRing.ResidueField A) = IsLocalRing.residue A c := by
      rw [Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq]
    have hA3 : IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m)
        = (IsLocalRing.residue A c * 1) ⊗ₜ[A] m := rfl
    rw [hA1, hA2, hA3, mul_one]
  have hmat : ∀ i j : ι, bk.repr (B' j) i = IsLocalRing.residue A (bA.toMatrix G i j) := by
    intro i j
    have hGj : B' j = ∑ l : ι, IsLocalRing.residue A (bA.repr (G j) l) • bk l := by
      rw [hB' j]
      conv_lhs => rw [← bA.sum_repr (G j)]
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hkey, hbk l]
    rw [hGj, Module.Basis.toMatrix_apply]
    simp only [Module.Basis.repr_sum_self]
  have hdet : bk.det (⇑B') = IsLocalRing.residue A (bA.det G) := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
    congr 1
    ext i j
    simp only [Module.Basis.toMatrix_apply]
    exact hmat i j
  rw [← hdet]
  exact (bk.isUnit_det B').ne_zero

theorem exists_adapted_parameters (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (q : Ideal S) [q.IsPrime] (A : Type*) [CommRing A] [Algebra S A] [Algebra k A]
    [IsScalarTower k S A] [IsLocalization q.primeCompl A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k (IsLocalRing.ResidueField A)] [IsScalarTower k A (IsLocalRing.ResidueField A)]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] :
    ∃ (g : S) (w : ι → S) (J : Finset ι),
      g ∉ q ∧
      (∀ j ∈ J, w j ∈ q) ∧
      Ideal.map (algebraMap S A) (Ideal.span (w '' (↑J : Set ι))) =
        IsLocalRing.maximalIdeal A ∧
      (∀ j ∉ J, ∃ i : ι, w j = coord k ι S i) ∧
      g = (basisKaehler k ι S).det (fun i : ι => KaehlerDifferential.D k S (w i)) ∧
      IsUnit (algebraMap S (Localization.Away g)
        ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i))) := by
  classical
  have instFEloc : Algebra.FormallyEtale S A :=
    Algebra.FormallyEtale.of_isLocalization (M := q.primeCompl)
  let instPA : Algebra (MvPolynomial ι k) A :=
    ((algebraMap S A).comp (algebraMap (MvPolynomial ι k) S)).toAlgebra
  have instT1 : IsScalarTower (MvPolynomial ι k) S A :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have t2Space_cuspAdeles : IsScalarTower k (MvPolynomial ι k) A :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply k S A x,
        IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S x]
      rfl
  have instFEPA : Algebra.FormallyEtale (MvPolynomial ι k) A :=
    Algebra.FormallyEtale.comp (MvPolynomial ι k) S A
  obtain ⟨h, y, hyspan, hyind⟩ := exists_local_parameters_consolidated83 k A
  obtain ⟨s, hsq, hsspan, hsind⟩ := exists_generators_maximalIdeal_of_linearIndependent_D k S q A h y hyspan hyind
  obtain ⟨bk, hbk⟩ : ∃ bk : Module.Basis ι (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A),
      ∀ i, bk i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (basisKaehler k ι A i) :=
    ⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) (basisKaehler k ι A),
      fun i => by simp⟩
  obtain ⟨Jst, B, hbasisInl, hbasisInr⟩ := exists_basis_sum_of_linearIndependent bk h
    (fun i : Fin h => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A (s i))) hsind
  have hcard1 : Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A)
      = Fintype.card (Fin h ⊕ {j : ι // j ∈ Jst}) := Module.finrank_eq_card_basis B
  have hcard2 : Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A) = Fintype.card ι :=
    Module.finrank_eq_card_basis bk
  have hcard3 : Fintype.card {j : ι // j ∈ Jst} + Fintype.card {j : ι // ¬ (j ∈ Jst)}
      = Fintype.card ι := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl (fun j : ι => j ∈ Jst))
  rw [Fintype.card_sum, Fintype.card_fin] at hcard1
  have hcard4 : Fintype.card {j : ι // ¬ (j ∈ Jst)} = h := by omega
  have e : {j : ι // ¬ (j ∈ Jst)} ≃ Fin h := Fintype.equivFinOfCardEq hcard4
  obtain ⟨τ, hτl, hτr⟩ : ∃ τ : Fin h ⊕ {j : ι // j ∈ Jst} ≃ ι,
      (∀ l : Fin h, τ (Sum.inl l) = ((e.symm l : ι))) ∧
      (∀ j : {j : ι // j ∈ Jst}, τ (Sum.inr j) = (j : ι)) :=
    ⟨(Equiv.sumCongr e.symm (Equiv.refl {j : ι // j ∈ Jst})).trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCompl (fun j : ι => j ∈ Jst))),
      fun l => rfl, fun j => rfl⟩
  obtain ⟨w, hwJ, hwn⟩ : ∃ w : ι → S, (∀ j, j ∈ Jst → w j = coord k ι S j) ∧
      (∀ x : {j : ι // ¬ (j ∈ Jst)}, w (x : ι) = s (e x)) := by
    refine ⟨fun j => if hj : j ∈ Jst then coord k ι S j else s (e ⟨j, hj⟩),
      fun j hj => ?_, fun x => ?_⟩
    · exact dif_pos hj
    · exact dif_neg x.2
  have hbasisApply : ∀ x : Fin h ⊕ {j : ι // j ∈ Jst},
      B x = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A (w (τ x))) := by
    rintro (l | j)
    · rw [hbasisInl l, hτl l, hwn (e.symm l), Equiv.apply_symm_apply]
    · rw [hbasisInr j, hτr j, hwJ (j : ι) j.2, hbk (j : ι), basisKaehler_apply,
        algebraMap_coord]
  have hB'G : ∀ i : ι, (B.reindex τ) i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A (w i)) := by
    intro i
    rw [Module.Basis.reindex_apply, hbasisApply (τ.symm i), Equiv.apply_symm_apply]
  have hdetne := residue_det_ne_zero_of_basis_tmul_consolidated83 (basisKaehler k ι A)
    (fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i))) (B.reindex τ) hB'G
  have hdetA : algebraMap S A ((basisKaehler k ι S).det
      (fun i : ι => KaehlerDifferential.D k S (w i)))
      = (basisKaehler k ι A).det
        (fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i))) :=
    algebraMap_det_basisKaehler k ι S A w
  have hmapq : Ideal.map (algebraMap S A) q = IsLocalRing.maximalIdeal A :=
    IsLocalization.AtPrime.map_eq_maximalIdeal q A
  refine ⟨(basisKaehler k ι S).det (fun i : ι => KaehlerDifferential.D k S (w i)), w, Jstᶜ,
    ?_, ?_, ?_, ?_, rfl, ?_⟩
  · intro hgq
    apply hdetne
    rw [← hdetA, IsLocalRing.residue_eq_zero_iff, ← hmapq]
    exact Ideal.mem_map_of_mem _ hgq
  · intro j hj
    have hj' : ¬ (j ∈ Jst) := Finset.mem_compl.mp hj
    have hwj : w j = s (e ⟨j, hj'⟩) := hwn ⟨j, hj'⟩
    rw [hwj]
    exact hsq _
  · rw [Ideal.map_span, ← hsspan]
    congr 1
    ext x
    constructor
    · rintro ⟨u, ⟨j, hj, rfl⟩, rfl⟩
      have hj' : ¬ (j ∈ Jst) := Finset.mem_compl.mp (Finset.mem_coe.mp hj)
      have hwj : w j = s (e ⟨j, hj'⟩) := hwn ⟨j, hj'⟩
      exact ⟨e ⟨j, hj'⟩, by rw [hwj]⟩
    · rintro ⟨i, rfl⟩
      refine ⟨w ((e.symm i : ι)), ⟨(e.symm i : ι), ?_, rfl⟩, ?_⟩
      · exact Finset.mem_coe.mpr (Finset.mem_compl.mpr (e.symm i).2)
      · have hwj : w ((e.symm i : ι)) = s (e (e.symm i)) := hwn (e.symm i)
        rw [hwj, Equiv.apply_symm_apply]
  · intro j hj
    have hj' : j ∈ Jst := by
      by_contra hc
      exact hj (Finset.mem_compl.mpr hc)
    exact ⟨j, hwJ j hj'⟩
  · exact IsLocalization.map_units
      (Localization.Away ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)))
      ⟨_, Submonoid.mem_powers _⟩

end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ConstantCodimension
section

open CategoryTheory AlgebraicGeometry

section
namespace FunctorialResolution.EmbeddedResolution

def HasEtaleCoordCodim {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X') (c : ℕ) : Prop :=
  ∀ x : X, ∃ (U : X'.Opens) (_ : τ.base x ∈ U) (m : ℕ) (ch : EtaleChart p U m)
    (S : Finset (Fin m)), S.card = c ∧ restrictIdeal τ.ker U = ch.coordIdeal S

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Scheme.{u}} {A B : (X.Opens)ᵒᵖ} (f g : A ⟶ B)

private theorem opens_op_hom_ext_consolidated60 : f = g := by
  apply Quiver.Hom.unop_inj
  apply Subsingleton.elim

private theorem presheaf_map_eq_consolidated60 :
    X.presheaf.map f = X.presheaf.map g := by
  rw [opens_op_hom_ext_consolidated60 f g]


end

section
variable {X : Scheme.{u}}

private theorem appTop_homOfLE_comp_topIso_hom_consolidated60 {V W : X.Opens} (h : W ≤ V) :
    Scheme.Hom.appTop (X.homOfLE h) ≫ W.topIso.hom =
      V.topIso.hom ≫ X.presheaf.map (homOfLE h).op := by
  simp
  exact (X.presheaf.map_comp _ _).symm.trans
    ((presheaf_map_eq_consolidated60 _ _).trans (X.presheaf.map_comp _ _))

private theorem smooth_ΓSpecIso_inv_comp_appTop_consolidated60 {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (V : X.Opens)
    (hV : IsAffineOpen V) :
    RingHom.Smooth (CommRingCat.Hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p))) := by
  have : IsAffine V.toScheme := hV
  have hfac : V.toScheme.isoSpec.hom ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p)) =
        V.ι ≫ p := by
    rw [Scheme.isoSpec_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  have h3 := congrArg
    (fun f : V.toScheme ⟶ Spec (CommRingCat.of k) => V.toScheme.isoSpec.inv ≫ f) hfac
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at h3
  have h2 : Smooth
      (Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p))) := by
    rw [h3]
    infer_instance
  exact AlgebraicGeometry.HasRingHomProperty.Spec_iff.mp h2

private theorem exists_mem_basicOpen_of_span_eq_top_consolidated60 {U : X.Opens}
    (x : X) (hx : x ∈ U) (s : Set Γ(X, U)) (hs : Ideal.span s = ⊤) :
    ∃ t ∈ s, x ∈ X.basicOpen t := by
  by_contra hcon
  push Not at hcon
  have : IsLocalRing (X.presheaf.stalk x) := inferInstance
  have hnu : ∀ t ∈ s, t ∈ Ideal.comap (X.presheaf.germ U x hx).hom
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) := by
    intro t ht
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    refine hcon t ht ((X.mem_basicOpen t x hx).mpr ?_)
    exact hunit
  have hle := Ideal.span_le.mpr hnu
  rw [hs] at hle
  have h1 := hle (Submodule.mem_top : (1 : Γ(X, U)) ∈ ⊤)
  rw [Ideal.mem_comap, map_one] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top
    ((Ideal.eq_top_iff_one _).mpr h1)


end

private theorem exists_etale_eval₂Hom_of_submersivePresentation_consolidated60 {k S : Type u} [CommRing k] [CommRing S] [Algebra k S]
    {ι σ : Type} [Finite ι] [Finite σ] (P : Algebra.SubmersivePresentation k S ι σ) :
    ∃ (n : ℕ) (v : ULift.{u} (Fin n) → S),
      RingHom.Etale (MvPolynomial.eval₂Hom (algebraMap k S) v) := by
  classical
  have : Fintype σ := Fintype.ofFinite σ
  obtain ⟨n, ⟨g0⟩⟩ := Finite.exists_equiv_fin ((Set.range P.map)ᶜ : Set ι)
  obtain ⟨e, he⟩ : ∃ e : σ ⊕ ULift.{u} (Fin n) ≃ ι, ∀ s, e (Sum.inl s) = P.map s :=
    ⟨(Equiv.sumCongr (Equiv.ofInjective P.map P.map_inj)
        ((g0.trans (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n).symm).symm)).trans
          (Equiv.Set.sumCompl (Set.range P.map)), fun s => rfl⟩
  refine ⟨n, fun t => P.val (e (Sum.inr t)), ?_⟩
  let : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) S :=
    (MvPolynomial.eval₂Hom (algebraMap k S) fun t => P.val (e (Sum.inr t))).toAlgebra
  have halg : ∀ z : MvPolynomial (ULift.{u} (Fin n)) k,
      algebraMap (MvPolynomial (ULift.{u} (Fin n)) k) S z =
        MvPolynomial.eval₂Hom (algebraMap k S) (fun t => P.val (e (Sum.inr t))) z := fun _ => rfl
  have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) S := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [halg]
    simp
  obtain ⟨Φ, hΦl, hΦr, hΦC⟩ :
      ∃ Φ : MvPolynomial ι k →+* MvPolynomial σ (MvPolynomial (ULift.{u} (Fin n)) k),
        (∀ s, Φ (MvPolynomial.X (e (Sum.inl s))) = MvPolynomial.X s) ∧
        (∀ t, Φ (MvPolynomial.X (e (Sum.inr t))) = MvPolynomial.C (MvPolynomial.X t)) ∧
        (∀ a : k, Φ (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a)) := by
    refine ⟨((MvPolynomial.aeval (fun i => Sum.elim (fun s => MvPolynomial.X s)
        (fun t => MvPolynomial.C (MvPolynomial.X t)) (e.symm i)) :
          MvPolynomial ι k →ₐ[k] MvPolynomial σ (MvPolynomial (ULift.{u} (Fin n)) k))).toRingHom,
      ?_, ?_, ?_⟩
    · intro s; simp
    · intro t; simp
    · intro a
      simp [MvPolynomial.algebraMap_eq,
        IsScalarTower.algebraMap_apply k (MvPolynomial (ULift.{u} (Fin n)) k)
          (MvPolynomial σ (MvPolynomial (ULift.{u} (Fin n)) k))]
  have hecases : ∀ i : ι, (∃ s, i = e (Sum.inl s)) ∨ (∃ t, i = e (Sum.inr t)) := by
    intro i
    rcases h : e.symm i with s | t
    · exact Or.inl ⟨s, by rw [← h, e.apply_symm_apply]⟩
    · exact Or.inr ⟨t, by rw [← h, e.apply_symm_apply]⟩
  have hΦsurj : Function.Surjective Φ := by
    intro z
    induction z using MvPolynomial.induction_on with
    | C q =>
        induction q using MvPolynomial.induction_on with
        | C a => exact ⟨MvPolynomial.C a, hΦC a⟩
        | add q₁ q₂ h₁ h₂ =>
            obtain ⟨x, hx⟩ := h₁
            obtain ⟨y, hy⟩ := h₂
            exact ⟨x + y, by rw [map_add, hx, hy, ← map_add]⟩
        | mul_X q t hq =>
            obtain ⟨x, hx⟩ := hq
            exact ⟨x * MvPolynomial.X (e (Sum.inr t)), by rw [map_mul, hx, hΦr, ← map_mul]⟩
    | add z₁ z₂ h₁ h₂ =>
        obtain ⟨x, hx⟩ := h₁
        obtain ⟨y, hy⟩ := h₂
        exact ⟨x + y, by rw [map_add, hx, hy]⟩
    | mul_X z s hz =>
        obtain ⟨x, hx⟩ := hz
        exact ⟨x * MvPolynomial.X (e (Sum.inl s)), by rw [map_mul, hx, hΦl]⟩
  have hA : ∀ y : P.Ring, algebraMap P.Ring S y = MvPolynomial.aeval P.val y :=
    fun y => Algebra.Generators.algebraMap_apply _ y
  have hcompX : ∀ i : ι,
      (MvPolynomial.aeval (fun s => P.val (e (Sum.inl s)))) (Φ (MvPolynomial.X i)) = P.val i := by
    intro i
    rcases hecases i with ⟨s, rfl⟩ | ⟨t, rfl⟩
    · rw [hΦl, MvPolynomial.aeval_X]
    · rw [hΦr, MvPolynomial.aeval_C, halg]
      simp
  have hcomp : ∀ z : MvPolynomial ι k,
      (MvPolynomial.aeval (fun s => P.val (e (Sum.inl s)))) (Φ z) =
        MvPolynomial.aeval P.val z := by
    intro z
    induction z using MvPolynomial.induction_on with
    | C a =>
        rw [hΦC, MvPolynomial.aeval_C, halg, MvPolynomial.aeval_C]
        simp
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | mul_X z i hz => simp only [map_mul, hz, hcompX, MvPolynomial.aeval_X]
  have hpdX : ∀ (s : σ) (i : ι),
      MvPolynomial.pderiv s (Φ (MvPolynomial.X i)) =
        Φ (MvPolynomial.pderiv (P.map s) (MvPolynomial.X i)) := by
    intro s i
    rcases hecases i with ⟨s', rfl⟩ | ⟨t, rfl⟩
    · rw [hΦl, he]
      by_cases hss : s = s'
      · subst hss
        rw [MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_self, map_one]
      · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hss),
          MvPolynomial.pderiv_X_of_ne (fun hh => hss (P.map_inj hh).symm), map_zero]
    · have hne : e (Sum.inr t) ≠ P.map s := by
        intro hh
        have hsum : (Sum.inr t : σ ⊕ ULift.{u} (Fin n)) = Sum.inl s := by
          apply e.injective
          rw [hh, he]
        simp at hsum
      rw [hΦr, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X_of_ne hne, map_zero]
  have hpd : ∀ (s : σ) (q : MvPolynomial ι k),
      MvPolynomial.pderiv s (Φ q) = Φ (MvPolynomial.pderiv (P.map s) q) := by
    intro s q
    induction q using MvPolynomial.induction_on with
    | C a => rw [hΦC, MvPolynomial.pderiv_C, MvPolynomial.pderiv_C, map_zero]
    | add q₁ q₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | mul_X q i hq => simp only [map_mul, MvPolynomial.pderiv_mul, map_add, hq, hpdX]
  have hsurjW : Function.Surjective
      (MvPolynomial.aeval (R := MvPolynomial (ULift.{u} (Fin n)) k)
        (fun s => P.val (e (Sum.inl s)))) := by
    intro s
    exact ⟨Φ (P.σ' s), by rw [hcomp, P.aeval_val_σ']⟩
  let G : Algebra.Generators (MvPolynomial (ULift.{u} (Fin n)) k) S σ :=
    Algebra.Generators.ofSurjective (fun s => P.val (e (Sum.inl s))) hsurjW
  have hGval : G.val = fun s => P.val (e (Sum.inl s)) := rfl
  have hspanQ : Ideal.span (Set.range fun j => Φ (P.relation j)) = G.ker := by
    have h1 : (Set.range fun j => Φ (P.relation j)) = ⇑Φ '' Set.range P.relation :=
      Set.range_comp _ _
    have h2 : P.ker = Ideal.comap Φ G.ker := by
      rw [Algebra.Generators.ker_eq_ker_aeval_val, Algebra.Generators.ker_eq_ker_aeval_val]
      ext z
      simp only [Ideal.mem_comap, RingHom.mem_ker, hGval, hcomp]
    rw [h1, ← Ideal.map_span, P.span_range_relation_eq_ker, h2,
      Ideal.map_comap_of_surjective Φ hΦsurj]
  obtain ⟨Q, hQmap, hQrel, hQalg⟩ :
      ∃ Q : Algebra.PreSubmersivePresentation (MvPolynomial (ULift.{u} (Fin n)) k) S σ σ,
        (∀ i, Q.map i = i) ∧ (∀ j, Q.relation j = Φ (P.relation j)) ∧
        (∀ z, algebraMap Q.Ring S z =
          MvPolynomial.aeval (fun s => P.val (e (Sum.inl s))) z) :=
    ⟨{ toGenerators := G
       relation := fun j => Φ (P.relation j)
       span_range_relation_eq_ker := hspanQ
       map := id
       map_inj := Function.injective_id },
      fun i => rfl, fun j => rfl, fun z => Algebra.Generators.algebraMap_apply G z⟩
  have hmat : ∀ i j, Q.jacobiMatrix i j = Φ (P.jacobiMatrix i j) := by
    intro i j
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
      Algebra.PreSubmersivePresentation.jacobiMatrix_apply, hQmap, hQrel]
    exact hpd i (P.relation j)
  have hdet : Φ P.jacobiMatrix.det = Q.jacobiMatrix.det := by
    rw [RingHom.map_det Φ P.jacobiMatrix,
      show Q.jacobiMatrix = P.jacobiMatrix.map ⇑Φ from Matrix.ext fun i j => hmat i j]
    rfl
  have hjac : Q.jacobian = P.jacobian := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hA, hQalg, ← hdet, hcomp]
  have hunit : IsUnit Q.jacobian := by
    rw [hjac]
    exact P.jacobian_isUnit
  have : Algebra.IsStandardSmoothOfRelativeDimension 0
      (MvPolynomial (ULift.{u} (Fin n)) k) S := by
    refine ⟨σ, σ, inferInstance, inferInstance, ⟨Q, hunit⟩, ?_⟩
    simp [Algebra.Presentation.dimension]
  show Algebra.Etale (MvPolynomial (ULift.{u} (Fin n)) k) S
  infer_instance

section
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) {V : X.Opens} (hVU : V ≤ U)

private theorem homOfLE_comp_map_comp_affineSpaceFinToSpec_consolidated60 :
    (X.homOfLE hVU ≫ c.map) ≫ affineSpaceFinToSpec k m = V.ι ≫ p := by
  rw [Category.assoc, c.comp_struct, ← Category.assoc, Scheme.homOfLE_ι]

private theorem etale_homOfLE_comp_map_consolidated60 :
    Etale (X.homOfLE hVU ≫ c.map) := by
  have := c.isEtale
  infer_instance


end

def EtaleChart.restrict {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    {V : X.Opens} (hVU : V ≤ U) : EtaleChart p V m where
  map := X.homOfLE hVU ≫ c.map
  comp_struct := homOfLE_comp_map_comp_affineSpaceFinToSpec_consolidated60 c hVU
  isEtale := etale_homOfLE_comp_map_consolidated60 c hVU

@[simp]
theorem EtaleChart.restrict_map {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    {V : X.Opens} (hVU : V ≤ U) :
    (c.restrict hVU).map = X.homOfLE hVU ≫ c.map := rfl

private theorem homOfVector_comp_affineSpaceFinToSpec_consolidated60 {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) {m : ℕ}
    (v : ULift.{u} (Fin m) → U.toScheme.presheaf.obj (op ⊤)) :
    AffineSpace.homOfVector (U.ι ≫ p) v ≫ affineSpaceFinToSpec k m = U.ι ≫ p := by
  simp

def EtaleChart.ofCoords {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) {m : ℕ}
    (v : ULift.{u} (Fin m) → U.toScheme.presheaf.obj (op ⊤))
    (he : Etale (AffineSpace.homOfVector (U.ι ≫ p) v)) :
    EtaleChart p U m where
  map := AffineSpace.homOfVector (U.ι ≫ p) v
  comp_struct := homOfVector_comp_affineSpaceFinToSpec_consolidated60 p U v
  isEtale := he

@[simp]
theorem EtaleChart.ofCoords_map {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) {m : ℕ}
    (v : ULift.{u} (Fin m) → U.toScheme.presheaf.obj (op ⊤))
    (he : Etale (AffineSpace.homOfVector (U.ι ≫ p) v)) :
    (EtaleChart.ofCoords p U v he).map = AffineSpace.homOfVector (U.ι ≫ p) v := rfl

section
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (x : X)

theorem exists_etaleChart :
    ∃ (U : X.Opens) (m : ℕ), x ∈ U ∧ IsAffineOpen U ∧ Nonempty (EtaleChart p U m) := by
  classical
  obtain ⟨V, hxV, hV⟩ := Scheme.exists_isAffineOpen_mem (X := X) x
  have : IsAffine V.toScheme := hV
  set θV : CommRingCat.of k ⟶ Γ(V.toScheme, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p) with hθVdef
  set ψV : CommRingCat.of k ⟶ Γ(X, V) := θV ≫ V.topIso.hom with hψVdef
  have hsmV : RingHom.Smooth ψV.hom := by
    have h1 : RingHom.Smooth θV.hom := smooth_ΓSpecIso_inv_comp_appTop_consolidated60 p V hV
    have h2 := RingHom.Smooth.respectsIso.left θV.hom V.topIso.commRingCatIsoToRingEquiv h1
    rw [hψVdef, CommRingCat.hom_comp]
    exact h2
  obtain ⟨s, hspan, hloc⟩ := RingHom.Smooth.locally_isStandardSmooth hsmV
  obtain ⟨t, hts, hxt⟩ := exists_mem_basicOpen_of_span_eq_top_consolidated60 x hxV s hspan
  have hUV : X.basicOpen t ≤ V := X.basicOpen_le t
  have hU : IsAffineOpen (X.basicOpen t) := hV.basicOpen t
  have : IsAffine (X.basicOpen t).toScheme := hU
  set θU : CommRingCat.of k ⟶ Γ((X.basicOpen t).toScheme, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      Scheme.Hom.appTop ((X.basicOpen t).ι ≫ p) with hθUdef
  set ψU : CommRingCat.of k ⟶ Γ(X, X.basicOpen t) :=
    θU ≫ (X.basicOpen t).topIso.hom with hψUdef
  have hψUeq : ψU = ψV ≫ X.presheaf.map (homOfLE hUV).op := by
    have e1 : (X.basicOpen t).ι ≫ p = X.homOfLE hUV ≫ (V.ι ≫ p) := by
      rw [← Category.assoc, Scheme.homOfLE_ι]
    rw [hψUdef, hθUdef, e1, Scheme.Hom.comp_appTop, hψVdef, hθVdef]
    simp only [Category.assoc]
    rw [appTop_homOfLE_comp_topIso_hom_consolidated60]
  have hstdψU : RingHom.IsStandardSmooth ψU.hom := by
    have := hV.isLocalization_basicOpen t
    have h1 := RingHom.isStandardSmooth_respectsIso.left
      ((algebraMap Γ(X, V) (Localization.Away t)).comp ψV.hom)
      (IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t)
        Γ(X, X.basicOpen t)).toRingEquiv (hloc t hts)
    have h2 : (((IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t)
        Γ(X, X.basicOpen t)).toRingEquiv : Localization.Away t →+* Γ(X, X.basicOpen t)).comp
        ((algebraMap Γ(X, V) (Localization.Away t)).comp ψV.hom)) = ψU.hom := by
      rw [hψUeq, CommRingCat.hom_comp]
      apply RingHom.ext
      intro a
      exact (IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t)
        Γ(X, X.basicOpen t)).commutes (ψV.hom a)
    rw [← h2]
    exact h1
  have hstdθU : RingHom.IsStandardSmooth θU.hom := by
    have h1 := RingHom.isStandardSmooth_respectsIso.left ψU.hom
      (X.basicOpen t).topIso.symm.commRingCatIsoToRingEquiv hstdψU
    have h3 : θU = ψU ≫ (X.basicOpen t).topIso.inv := by
      rw [hψUdef, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h2 : (((X.basicOpen t).topIso.symm.commRingCatIsoToRingEquiv :
        Γ(X, X.basicOpen t) →+* Γ((X.basicOpen t).toScheme, ⊤)).comp ψU.hom) = θU.hom := by
      rw [h3, CommRingCat.hom_comp]
      rfl
    rw [← h2]
    exact h1
  let : Algebra (CommRingCat.of k) Γ((X.basicOpen t).toScheme, ⊤) := θU.hom.toAlgebra
  have hAlg : Algebra.IsStandardSmooth (CommRingCat.of k) Γ((X.basicOpen t).toScheme, ⊤) :=
    hstdθU
  obtain ⟨⟨ι, σ, hσ, hι, ⟨P⟩⟩⟩ := hAlg
  have : Finite σ := hσ
  have : Finite ι := hι
  obtain ⟨n, v, hv⟩ := exists_etale_eval₂Hom_of_submersivePresentation_consolidated60 P
  set φ : CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) (CommRingCat.of k)) ⟶
      Γ((X.basicOpen t).toScheme, ⊤) :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom
      (algebraMap (CommRingCat.of k) Γ((X.basicOpen t).toScheme, ⊤)) v) with hφdef
  have : Etale (Spec.map φ) :=
    AlgebraicGeometry.HasRingHomProperty.Spec_iff.mpr hv
  have hφC : CommRingCat.ofHom MvPolynomial.C ≫ φ = θU := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    show MvPolynomial.eval₂
        (algebraMap (CommRingCat.of k) Γ((X.basicOpen t).toScheme, ⊤)) v (MvPolynomial.C a)
      = θU.hom a
    exact MvPolynomial.eval₂_C _ _ a
  have hcs : ((X.basicOpen t).toScheme.isoSpec.hom ≫ Spec.map φ ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).inv) ≫
        affineSpaceFinToSpec k n = (X.basicOpen t).ι ≫ p := by
    rw [Category.assoc, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp, hφC,
      hθUdef]
    rw [Scheme.isoSpec_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  exact ⟨X.basicOpen t, n, hxt, hU,
    ⟨⟨(X.basicOpen t).toScheme.isoSpec.hom ≫ Spec.map φ ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).inv, hcs, inferInstance⟩⟩⟩

theorem exists_etaleChart_le (W : X.Opens) (hx : x ∈ W) :
    ∃ (U : X.Opens) (m : ℕ), x ∈ U ∧ U ≤ W ∧ IsAffineOpen U ∧ Nonempty (EtaleChart p U m) := by
  obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p x
  have hxUW : x ∈ (U ⊓ W : X.Opens) := ⟨hxU, hx⟩
  obtain ⟨f, hfle, hxf⟩ := hU.exists_basicOpen_le (⟨x, hxUW⟩ : (U ⊓ W : X.Opens)) hxU
  have hle : X.basicOpen f ≤ U := X.basicOpen_le f
  exact ⟨X.basicOpen f, m, hxf, le_trans hfle inf_le_right, hU.basicOpen f, ⟨c.restrict hle⟩⟩


end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.IdealSheafOpenRestriction
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

def openSubschemeKer {X : Scheme.{u}} (Z : X.IdealSheafData) (W : Z.subscheme.Opens) :
    X.IdealSheafData :=
  (Scheme.Opens.ι W ≫ Z.subschemeι).ker

section
variable {X : Scheme.{u}} (Z : X.IdealSheafData) (W : Z.subscheme.Opens)

theorem openSubschemeKer_eq_ker :
    openSubschemeKer Z W = (Scheme.Opens.ι W ≫ Z.subschemeι).ker := rfl

theorem support_openSubschemeKer (hW : IsClosed (W : Set Z.subscheme)) :
    ((openSubschemeKer Z W).support : Set X) = ⇑Z.subschemeι.base '' (W : Set Z.subscheme) := by
  have hindW : Topology.IsInducing ⇑(Scheme.Opens.ι W).base :=
    (Scheme.Opens.ι W).isEmbedding.toIsInducing
  have hrangeW : Set.range ⇑(Scheme.Opens.ι W).base = (W : Set Z.subscheme) := by
    rw [Scheme.Opens.range_ι]
  have hqcW : QuasiCompact (Scheme.Opens.ι W) := by
    refine ⟨fun U _ hUc => ?_⟩
    refine hindW.isCompact_iff.mpr ?_
    rw [Set.image_preimage_eq_inter_range, hrangeW]
    exact hUc.inter_right hW
  have hqc : QuasiCompact (Scheme.Opens.ι W ≫ Z.subschemeι) := inferInstance
  have hclosed : IsClosed (⇑Z.subschemeι.base '' (W : Set Z.subscheme)) :=
    Z.subschemeι.isClosedEmbedding.isClosedMap _ hW
  have hcomp : ⇑(Scheme.Opens.ι W ≫ Z.subschemeι).base
      = ⇑Z.subschemeι.base ∘ ⇑(Scheme.Opens.ι W).base := rfl
  have hrange : Set.range ⇑(Scheme.Opens.ι W ≫ Z.subschemeι).base
      = ⇑Z.subschemeι.base '' (W : Set Z.subscheme) := by
    rw [hcomp, Set.range_comp, hrangeW]
  rw [openSubschemeKer_eq_ker, Scheme.Hom.support_ker]
  show closure (Set.range ⇑(Scheme.Opens.ι W ≫ Z.subschemeι).base)
      = ⇑Z.subschemeι.base '' (W : Set Z.subscheme)
  rw [hrange]
  exact hclosed.closure_eq

private theorem exists_isIso_openSubschemeKer_subscheme_consolidated59 (hW : IsClosed (W : Set Z.subscheme)) :
    ∃ e : W.toScheme ⟶ (openSubschemeKer Z W).subscheme, IsIso e ∧
      e ≫ (openSubschemeKer Z W).subschemeι = Scheme.Opens.ι W ≫ Z.subschemeι := by
  have : IsClosedImmersion (Scheme.Opens.ι W) := W.isClosedImmersion_ι_of_isClosed hW
  have : IsClosedImmersion (Scheme.Opens.ι W ≫ Z.subschemeι) := inferInstance
  have hker : (Scheme.Opens.ι W ≫ Z.subschemeι).ker = (openSubschemeKer Z W).subschemeι.ker :=
    (Scheme.IdealSheafData.ker_subschemeι (openSubschemeKer Z W)).symm
  refine ⟨IsClosedImmersion.lift (openSubschemeKer Z W).subschemeι
      (Scheme.Opens.ι W ≫ Z.subschemeι) (le_of_eq hker.symm), ?_,
    IsClosedImmersion.lift_fac _ _ _⟩
  exact IsClosedImmersion.isIso_of_ker_eq (Scheme.Opens.ι W ≫ Z.subschemeι)
    (openSubschemeKer Z W).subschemeι _ (IsClosedImmersion.lift_fac _ _ _) hker


end

theorem smooth_subschemeι_openSubschemeKer_comp {X S : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (hW : IsClosed (W : Set Z.subscheme)) (g : X ⟶ S)
    [Smooth (Z.subschemeι ≫ g)] :
    Smooth ((openSubschemeKer Z W).subschemeι ≫ g) := by
  obtain ⟨e, he, hfac⟩ := exists_isIso_openSubschemeKer_subscheme_consolidated59 Z W hW
  have := he
  have hsm : Smooth (Scheme.Opens.ι W ≫ Z.subschemeι ≫ g) := inferInstance
  have hfac2 : inv e ≫ Scheme.Opens.ι W ≫ Z.subschemeι ≫ g
      = (openSubschemeKer Z W).subschemeι ≫ g := by
    rw [← Category.assoc (Scheme.Opens.ι W) Z.subschemeι g, ← hfac, Category.assoc,
      IsIso.inv_hom_id_assoc]
  have key : Smooth (inv e ≫ Scheme.Opens.ι W ≫ Z.subschemeι ≫ g) := inferInstance
  rwa [hfac2] at key

private theorem comap_eq_ker_fst_consolidated59 {A B : Scheme.{u}} (f : A ⟶ B) (I : B.IdealSheafData) :
    I.comap f = (Limits.pullback.fst f I.subschemeι).ker := rfl

private theorem comap_opensι_eq_ker_morphismRestrict_consolidated59 {T : Scheme.{u}} (K : T.IdealSheafData)
    (V : T.Opens) : K.comap (Scheme.Opens.ι V) = (K.subschemeι ∣_ V).ker := by
  have h := isPullback_morphismRestrict K.subschemeι V
  have hfac : h.isoPullback.hom ≫ Limits.pullback.fst (Scheme.Opens.ι V) K.subschemeι
      = K.subschemeι ∣_ V := h.isoPullback_hom_fst
  rw [comap_eq_ker_fst_consolidated59, ← hfac, Scheme.Hom.ker_comp_of_isIso]

section
variable {Y : Scheme.{u}} (V O : Y.Opens) (h : O ≤ V)
include h

private theorem image_preimage_opensι_of_le_consolidated59 :
    Scheme.Opens.ι V ''ᵁ (Scheme.Opens.ι V ⁻¹ᵁ O) = O := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
  refine inf_eq_right.mpr ?_
  intro x hx
  show x ∈ Set.range ⇑(Scheme.Opens.ι V).base
  rw [Scheme.Opens.range_ι]
  exact h hx

private theorem injective_app_opensι_of_le_consolidated59 :
    Function.Injective (CommRingCat.Hom.hom ((Scheme.Opens.ι V).app O)) := by
  have hb := AlgebraicGeometry.IsOpenImmersion.bijective_appLE_of_image_eq (Scheme.Opens.ι V) O
    (Scheme.Opens.ι V ⁻¹ᵁ O) le_rfl (image_preimage_opensι_of_le_consolidated59 V O h)
  rw [Scheme.Hom.app_eq_appLE]
  exact hb.1


end

private theorem ker_app_morphismRestrict_eq_map_ker_consolidated59 {Y T : Scheme.{u}} (m : Y ⟶ T) (V : T.Opens)
    (P : V.toScheme.affineOpens)
    (e : P.1 ≤ Scheme.Opens.ι V ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) :
    RingHom.ker (CommRingCat.Hom.hom ((m ∣_ V).app P.1))
      = Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appLE (Scheme.Opens.ι V)
            (Scheme.Opens.ι V ''ᵁ P.1) P.1 e))
          (RingHom.ker (CommRingCat.Hom.hom (m.app (Scheme.Opens.ι V ''ᵁ P.1)))) := by
  have hpre : Scheme.Opens.ι V ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) = P.1 :=
    (Scheme.Opens.ι V).preimage_image_eq P.1
  have hpre2 : ((m ∣_ V) ⁻¹ᵁ P.1)
      = Scheme.Opens.ι (m ⁻¹ᵁ V) ⁻¹ᵁ (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) := by
    rw [← Scheme.Hom.comp_preimage, ← morphismRestrict_ι, Scheme.Hom.comp_preimage, hpre]
  have hQV : (Scheme.Opens.ι V ''ᵁ P.1) ≤ V := Scheme.Opens.ι_image_le ..
  have hle : m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) ≤ m ⁻¹ᵁ V := fun x hx => hQV hx
  have himg : Scheme.Opens.ι (m ⁻¹ᵁ V) ''ᵁ ((m ∣_ V) ⁻¹ᵁ P.1)
      = m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) := by
    rw [hpre2]
    exact image_preimage_opensι_of_le_consolidated59 (m ⁻¹ᵁ V) (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) hle
  have hbij := AlgebraicGeometry.IsOpenImmersion.bijective_appLE_of_image_eq (Scheme.Opens.ι V)
    (Scheme.Opens.ι V ''ᵁ P.1) P.1 e rfl
  have hinj := (AlgebraicGeometry.IsOpenImmersion.bijective_appLE_of_image_eq
    (Scheme.Opens.ι (m ⁻¹ᵁ V)) (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1))
    ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le himg).1
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
    exact AlgebraicGeometry.Scheme.Hom.appLE_congr_hom (morphismRestrict_ι m V) _ _ _ _
  have hsqr : ∀ x, (CommRingCat.Hom.hom ((m ∣_ V).app P.1))
        ((CommRingCat.Hom.hom
          (Scheme.Hom.appLE (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1 e)) x)
      = (CommRingCat.Hom.hom (Scheme.Hom.appLE (Scheme.Opens.ι (m ⁻¹ᵁ V))
          (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le))
        ((CommRingCat.Hom.hom (m.app (Scheme.Opens.ι V ''ᵁ P.1))) x) := by
    intro x
    have h' := congrArg (fun mm => (CommRingCat.Hom.hom mm) x) hsq
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h'
  refine le_antisymm ?_ ?_
  · intro y hy
    rw [RingHom.mem_ker] at hy
    obtain ⟨x, rfl⟩ := hbij.2 y
    refine Ideal.mem_map_of_mem _ ?_
    rw [RingHom.mem_ker]
    apply hinj
    rw [← hsqr x, hy, map_zero]
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, hsqr x]
    rw [RingHom.mem_ker] at hx
    rw [hx, map_zero]

theorem restrictIdeal_openSubschemeKer_of_preimage_le {X : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (hW : IsClosed (W : Set Z.subscheme)) (U : X.Opens)
    (hU : (Z.subschemeι ⁻¹ᵁ U) ≤ W) :
    restrictIdeal (openSubschemeKer Z W) U = restrictIdeal Z U := by
  have hindW : Topology.IsInducing ⇑(Scheme.Opens.ι W).base :=
    (Scheme.Opens.ι W).isEmbedding.toIsInducing
  have hrangeW : Set.range ⇑(Scheme.Opens.ι W).base = (W : Set Z.subscheme) := by
    rw [Scheme.Opens.range_ι]
  have hqcW : QuasiCompact (Scheme.Opens.ι W) := by
    refine ⟨fun V _ hVc => ?_⟩
    refine hindW.isCompact_iff.mpr ?_
    rw [Set.image_preimage_eq_inter_range, hrangeW]
    exact hVc.inter_right hW
  have hqc : QuasiCompact (Scheme.Opens.ι W ≫ Z.subschemeι) := inferInstance
  have hqc1 : QuasiCompact ((openSubschemeKer Z W).subschemeι ∣_ U) := inferInstance
  have hqc2 : QuasiCompact (Z.subschemeι ∣_ U) := inferInstance
  rw [restrictIdeal_eq_comap_ι (openSubschemeKer Z W) U, restrictIdeal_eq_comap_ι Z U,
    comap_opensι_eq_ker_morphismRestrict_consolidated59 (openSubschemeKer Z W) U,
    comap_opensι_eq_ker_morphismRestrict_consolidated59 Z U]
  refine Scheme.IdealSheafData.ext ?_
  funext P
  have hQaff : IsAffineOpen (Scheme.Opens.ι U ''ᵁ P.1) :=
    P.2.image_of_isOpenImmersion (Scheme.Opens.ι U)
  have hpre : Scheme.Opens.ι U ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1) = P.1 :=
    (Scheme.Opens.ι U).preimage_image_eq P.1
  have e : P.1 ≤ Scheme.Opens.ι U ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1) := hpre.ge
  have hQU : (Scheme.Opens.ι U ''ᵁ P.1) ≤ U := Scheme.Opens.ι_image_le ..
  have hmono : (Z.subschemeι ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1)) ≤ (Z.subschemeι ⁻¹ᵁ U) :=
    fun x hx => hQU hx
  have hOW : (Z.subschemeι ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1)) ≤ W := le_trans hmono hU
  have hinjW := injective_app_opensι_of_le_consolidated59 W (Z.subschemeι ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1)) hOW
  have hkerA : RingHom.ker (CommRingCat.Hom.hom
        ((openSubschemeKer Z W).subschemeι.app (Scheme.Opens.ι U ''ᵁ P.1)))
      = RingHom.ker (CommRingCat.Hom.hom
        ((Scheme.Opens.ι W ≫ Z.subschemeι).app (Scheme.Opens.ι U ''ᵁ P.1))) := by
    have h1 := AlgebraicGeometry.Scheme.Hom.ker_apply (openSubschemeKer Z W).subschemeι
      ⟨Scheme.Opens.ι U ''ᵁ P.1, hQaff⟩
    have h2 := AlgebraicGeometry.Scheme.Hom.ker_apply (Scheme.Opens.ι W ≫ Z.subschemeι)
      ⟨Scheme.Opens.ι U ''ᵁ P.1, hQaff⟩
    rw [Scheme.IdealSheafData.ker_subschemeι] at h1
    rw [← h1, ← h2, openSubschemeKer_eq_ker]
  have hmain : RingHom.ker (CommRingCat.Hom.hom
        ((openSubschemeKer Z W).subschemeι.app (Scheme.Opens.ι U ''ᵁ P.1)))
      = RingHom.ker (CommRingCat.Hom.hom
        (Z.subschemeι.app (Scheme.Opens.ι U ''ᵁ P.1))) := by
    rw [hkerA]
    ext x
    have hfac : (CommRingCat.Hom.hom
          ((Scheme.Opens.ι W ≫ Z.subschemeι).app (Scheme.Opens.ι U ''ᵁ P.1))) x
        = (CommRingCat.Hom.hom ((Scheme.Opens.ι W).app
            (Z.subschemeι ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1))))
          ((CommRingCat.Hom.hom (Z.subschemeι.app (Scheme.Opens.ι U ''ᵁ P.1))) x) := by
      show (CommRingCat.Hom.hom (Z.subschemeι.app (Scheme.Opens.ι U ''ᵁ P.1) ≫
        (Scheme.Opens.ι W).app (Z.subschemeι ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1)))) x = _
      rw [CommRingCat.hom_comp, RingHom.comp_apply]
    simp only [RingHom.mem_ker, hfac]
    constructor
    · intro hx
      exact hinjW (hx.trans (map_zero _).symm)
    · intro hx
      exact (congrArg _ hx).trans (map_zero _)
  rw [AlgebraicGeometry.Scheme.Hom.ker_apply ((openSubschemeKer Z W).subschemeι ∣_ U) P,
    AlgebraicGeometry.Scheme.Hom.ker_apply (Z.subschemeι ∣_ U) P,
    ker_app_morphismRestrict_eq_map_ker_consolidated59 (openSubschemeKer Z W).subschemeι U P e,
    ker_app_morphismRestrict_eq_map_ker_consolidated59 Z.subschemeι U P e, hmain]

private theorem subsingleton_sections_of_eq_bot_consolidated59 {Y : Scheme.{u}} (V : Y.Opens)
    (hV : V = ⊥) : Subsingleton ↥(Y.presheaf.obj (Opposite.op V)) := by
  have h : CategoryTheory.Limits.IsTerminal (Y.presheaf.obj (Opposite.op V)) :=
    Y.sheaf.isTerminalOfEqEmpty hV
  exact CommRingCat.subsingleton_of_isTerminal h

section
variable {X : Scheme.{u}} (Z : X.IdealSheafData) (W : Z.subscheme.Opens)

theorem restrictIdeal_openSubschemeKer_eq_top (hW : IsClosed (W : Set Z.subscheme)) (U : X.Opens)
    (hU : ∀ w : Z.subscheme, w ∈ W → Z.subschemeι.base w ∉ U) :
    restrictIdeal (openSubschemeKer Z W) U = ⊤ := by
  have hnot : ∀ y : (openSubschemeKer Z W).subscheme,
      (openSubschemeKer Z W).subschemeι.base y ∉ U := by
    intro y hy
    have hmem : (openSubschemeKer Z W).subschemeι.base y ∈ ((openSubschemeKer Z W).support : Set X) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact Set.mem_range_self y
    rw [support_openSubschemeKer Z W hW] at hmem
    obtain ⟨w, hwW, hw⟩ := hmem
    refine hU w hwW ?_
    rw [hw]
    exact hy
  have hempty : ∀ _y : ((openSubschemeKer Z W).subschemeι ⁻¹ᵁ U).toScheme, False := by
    intro y
    have h1 : (Scheme.Opens.ι ((openSubschemeKer Z W).subschemeι ⁻¹ᵁ U)).base y ∈
        ((openSubschemeKer Z W).subschemeι ⁻¹ᵁ U : Set (openSubschemeKer Z W).subscheme) := by
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self y
    exact hnot _ h1
  have hObot : ∀ O : (((openSubschemeKer Z W).subschemeι ⁻¹ᵁ U).toScheme).Opens, O = ⊥ := by
    intro O
    refine le_antisymm ?_ bot_le
    intro y _
    exact (hempty y).elim
  have hqcm : QuasiCompact ((openSubschemeKer Z W).subschemeι ∣_ U) := by
    refine ⟨fun O _ _ => ?_⟩
    have hE : (⇑((openSubschemeKer Z W).subschemeι ∣_ U).base ⁻¹' O) = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false]
      intro _
      exact hempty y
    rw [hE]
    exact isCompact_empty
  rw [restrictIdeal_eq_comap_ι, comap_opensι_eq_ker_morphismRestrict_consolidated59 (openSubschemeKer Z W) U]
  refine Scheme.IdealSheafData.ext ?_
  funext V
  have hker : RingHom.ker (CommRingCat.Hom.hom
      (((openSubschemeKer Z W).subschemeι ∣_ U).app V.1)) = ⊤ := by
    have := subsingleton_sections_of_eq_bot_consolidated59
      (((openSubschemeKer Z W).subschemeι ∣_ U) ⁻¹ᵁ V.1) (hObot _)
    rw [Ideal.eq_top_iff_one, RingHom.mem_ker]
    exact Subsingleton.elim _ _
  rw [AlgebraicGeometry.Scheme.Hom.ker_apply ((openSubschemeKer Z W).subschemeι ∣_ U) V, hker]
  simp

theorem exists_opens_preimage_subschemeι_le (x : X)
    (hx : x ∈ ⇑Z.subschemeι.base '' (W : Set Z.subscheme)) :
    ∃ U : X.Opens, x ∈ U ∧ (Z.subschemeι ⁻¹ᵁ U) ≤ W := by
  have hind : Topology.IsInducing ⇑Z.subschemeι.base :=
    Z.subschemeι.isEmbedding.toIsInducing
  obtain ⟨t, ht, hteq⟩ := hind.isOpen_iff.mp W.isOpen
  obtain ⟨w, hw, rfl⟩ := hx
  refine ⟨⟨t, ht⟩, ?_, ?_⟩
  · have hwt : w ∈ ⇑Z.subschemeι.base ⁻¹' t := by
      rw [hteq]
      exact hw
    exact hwt
  · intro y hy
    have hy' : y ∈ ⇑Z.subschemeι.base ⁻¹' t := hy
    rw [hteq] at hy'
    exact hy'

theorem exists_opens_notMem_image (hW : IsClosed (W : Set Z.subscheme)) (x : X)
    (hx : x ∉ ⇑Z.subschemeι.base '' (W : Set Z.subscheme)) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ w : Z.subscheme, w ∈ W → Z.subschemeι.base w ∉ U := by
  have hclosed : IsClosed (⇑Z.subschemeι.base '' (W : Set Z.subscheme)) :=
    Z.subschemeι.isClosedEmbedding.isClosedMap _ hW
  refine ⟨⟨(⇑Z.subschemeι.base '' (W : Set Z.subscheme))ᶜ, hclosed.isOpen_compl⟩, hx, ?_⟩
  intro w hw hmem
  exact hmem ⟨w, hw, rfl⟩

private theorem ker_app_opensι_comp_subschemeι_eq_of_preimage_le_consolidated59 (V : X.Opens) (hVW : (Z.subschemeι ⁻¹ᵁ V) ≤ W) :
    RingHom.ker (CommRingCat.Hom.hom ((Scheme.Opens.ι W ≫ Z.subschemeι).app V))
      = RingHom.ker (CommRingCat.Hom.hom (Z.subschemeι.app V)) := by
  have hinjW := injective_app_opensι_of_le_consolidated59 W (Z.subschemeι ⁻¹ᵁ V) hVW
  ext a
  have hfac : (CommRingCat.Hom.hom ((Scheme.Opens.ι W ≫ Z.subschemeι).app V)) a
      = (CommRingCat.Hom.hom ((Scheme.Opens.ι W).app (Z.subschemeι ⁻¹ᵁ V)))
        ((CommRingCat.Hom.hom (Z.subschemeι.app V)) a) := by
    show (CommRingCat.Hom.hom (Z.subschemeι.app V ≫
      (Scheme.Opens.ι W).app (Z.subschemeι ⁻¹ᵁ V))) a = _
    rw [CommRingCat.hom_comp, RingHom.comp_apply]
  simp only [RingHom.mem_ker, hfac]
  constructor
  · intro ha
    exact hinjW (ha.trans (map_zero _).symm)
  · intro ha
    exact (congrArg _ ha).trans (map_zero _)


end

private theorem exists_ideal_basicOpen_eq_span_singleton_of_eq_span_consolidated59 {X : Scheme.{u}} (J : X.IdealSheafData)
    (U : X.affineOpens) (s f : Γ(X, U.1)) (hf : f ∈ nonZeroDivisors Γ(X, U.1))
    (hJ : J.ideal U = Ideal.span {f}) :
    ∃ f' : Γ(X, X.basicOpen s), f' ∈ nonZeroDivisors Γ(X, X.basicOpen s) ∧
      J.ideal ⟨X.basicOpen s, U.2.basicOpen s⟩ = Ideal.span {f'} := by
  have hmap := J.map_ideal_basicOpen U s
  rw [hJ, Ideal.map_span, Set.image_singleton] at hmap
  have := U.2.isLocalization_basicOpen s
  refine ⟨_, ?_, hmap.symm⟩
  exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers s) Γ(X, X.basicOpen s) hf

private theorem one_eq_zero_sections_of_eq_bot_consolidated59 {Y : Scheme.{u}} (V : Y.Opens) (hV : V = ⊥) :
    (1 : Γ(Y, V)) = 0 := by
  have := subsingleton_sections_of_eq_bot_consolidated59 V hV
  exact Subsingleton.elim _ _

theorem isLocallyGeneratedByNonZeroDivisor_openSubschemeKer {X : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (hW : IsClosed (W : Set Z.subscheme))
    (hZ : Blowup.IsLocallyGeneratedByNonZeroDivisor Z) : Blowup.IsLocallyGeneratedByNonZeroDivisor (openSubschemeKer Z W) := by
  have hindW : Topology.IsInducing ⇑(Scheme.Opens.ι W).base :=
    (Scheme.Opens.ι W).isEmbedding.toIsInducing
  have hrangeW : Set.range ⇑(Scheme.Opens.ι W).base = (W : Set Z.subscheme) := by
    rw [Scheme.Opens.range_ι]
  have hqcW : QuasiCompact (Scheme.Opens.ι W) := by
    refine ⟨fun U _ hUc => ?_⟩
    refine hindW.isCompact_iff.mpr ?_
    rw [Set.image_preimage_eq_inter_range, hrangeW]
    exact hUc.inter_right hW
  have hqc : QuasiCompact (Scheme.Opens.ι W ≫ Z.subschemeι) := inferInstance
  have hpiece : ∀ V : X.affineOpens, (Z.subschemeι ⁻¹ᵁ V.1) ≤ W →
      (openSubschemeKer Z W).ideal V = Z.ideal V := by
    intro V hVW
    have h2 : RingHom.ker (CommRingCat.Hom.hom (Z.subschemeι.app V.1)) = Z.ideal V := by
      rw [← AlgebraicGeometry.Scheme.Hom.ker_apply Z.subschemeι V,
        Scheme.IdealSheafData.ker_subschemeι]
    rw [openSubschemeKer_eq_ker, AlgebraicGeometry.Scheme.Hom.ker_apply, ker_app_opensι_comp_subschemeι_eq_of_preimage_le_consolidated59 Z W V.1 hVW, h2]
  have hpiecetop : ∀ V : X.affineOpens,
      ((Scheme.Opens.ι W ≫ Z.subschemeι) ⁻¹ᵁ V.1) = ⊥ → (openSubschemeKer Z W).ideal V = ⊤ := by
    intro V hbot
    rw [openSubschemeKer_eq_ker, AlgebraicGeometry.Scheme.Hom.ker_apply, Ideal.eq_top_iff_one,
      RingHom.mem_ker, map_one]
    exact one_eq_zero_sections_of_eq_bot_consolidated59 _ hbot
  intro x
  by_cases hx : x ∈ ⇑Z.subschemeι.base '' (W : Set Z.subscheme)
  · obtain ⟨N, hxN, hNle⟩ := exists_opens_preimage_subschemeι_le Z W x hx
    obtain ⟨U₁, f₁, hxU₁, hf₁, hZU₁⟩ := hZ x
    have hU₁ : IsAffineOpen U₁.1 := U₁.2
    obtain ⟨s, hsN, hxs⟩ := hU₁.exists_basicOpen_le (⟨x, hxN⟩ : ↥N) hxU₁
    obtain ⟨f, hf, hZU⟩ := exists_ideal_basicOpen_eq_span_singleton_of_eq_span_consolidated59 Z U₁ s f₁ hf₁ hZU₁
    have hVW : (Z.subschemeι ⁻¹ᵁ (X.basicOpen s)) ≤ W := fun v hv => hNle (hsN hv)
    refine ⟨⟨X.basicOpen s, hU₁.basicOpen s⟩, f, hxs, hf, ?_⟩
    exact (hpiece ⟨X.basicOpen s, hU₁.basicOpen s⟩ hVW).trans hZU
  · obtain ⟨N, hxN, hNno⟩ := exists_opens_notMem_image Z W hW x hx
    obtain ⟨U₀, hxU₀⟩ : ∃ U₀ : X.affineOpens, x ∈ U₀.1 := by
      have hx' : x ∈ (⊤ : X.Opens) := Set.mem_univ x
      rw [← iSup_affineOpens_eq_top X] at hx'
      obtain ⟨U₀, hU₀⟩ := Opens.mem_iSup.mp hx'
      exact ⟨U₀, hU₀⟩
    have hU₀ : IsAffineOpen U₀.1 := U₀.2
    obtain ⟨s, hsN, hxs⟩ := hU₀.exists_basicOpen_le (⟨x, hxN⟩ : ↥N) hxU₀
    refine ⟨⟨X.basicOpen s, hU₀.basicOpen s⟩, 1, hxs, one_mem _, ?_⟩
    have hbot : (Scheme.Opens.ι W ≫ Z.subschemeι) ⁻¹ᵁ (X.basicOpen s) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro w hw
      have hw2 : Z.subschemeι.base ((Scheme.Opens.ι W).base w) ∈ X.basicOpen s := hw
      have hmem : (Scheme.Opens.ι W).base w ∈ (W : Set Z.subscheme) := by
        rw [← Scheme.Opens.range_ι W]
        exact ⟨w, rfl⟩
      exact absurd (hsN hw2) (hNno _ hmem)
    rw [Ideal.span_singleton_one]
    exact hpiecetop ⟨X.basicOpen s, hU₀.basicOpen s⟩ hbot

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalNormalForm
section
open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

section

section
variable {A : Type*} [CommRing A] [IsLocalRing A] {M : Type*} [AddCommGroup M] [Module A M]

private theorem repr_mem_maximalIdeal_of_tmul_eq_zero_consolidated84 {n : Type*} [Fintype n]
    (bb : Module.Basis n A M) (x : M)
    (h : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x = 0) (i : n) :
    bb.repr x i ∈ IsLocalRing.maximalIdeal A := by
  classical
  obtain ⟨bk, hbk⟩ : ∃ bk : Module.Basis n (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] M),
      ∀ j, bk j = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] bb j :=
    ⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) bb, fun j => by simp⟩
  have hkey : ∀ (c : A) (m : M), (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m)
      = IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m) := by
    intro c m
    have hA1 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m)
        = (c • (1 : IsLocalRing.ResidueField A)) ⊗ₜ[A] m := (TensorProduct.smul_tmul c 1 m).symm
    have hA2 : c • (1 : IsLocalRing.ResidueField A) = IsLocalRing.residue A c := by
      rw [Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq]
    have hA3 : IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m)
        = (IsLocalRing.residue A c * 1) ⊗ₜ[A] m := rfl
    rw [hA1, hA2, hA3, mul_one]
  have hxsum : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x
      = ∑ j : n, IsLocalRing.residue A (bb.repr x j) • bk j := by
    conv_lhs => rw [← bb.sum_repr x]
    rw [TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hkey, hbk j]
  have h2 : bk.repr ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x) i = 0 := by
    rw [h]
    simp
  rw [hxsum, Module.Basis.repr_sum_self] at h2
  rw [← IsLocalRing.residue_eq_zero_iff]
  exact h2

private theorem residue_det_ne_zero_of_tmul_eq_basis_consolidated84 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bA : Module.Basis ι A M) (G : ι → M)
    (B' : Module.Basis ι (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] M))
    (hB' : ∀ i, B' i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] G i) :
    IsLocalRing.residue A (bA.det G) ≠ 0 := by
  classical
  obtain ⟨bk, hbk⟩ : ∃ bk : Module.Basis ι (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] M),
      ∀ i, bk i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] bA i :=
    ⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) bA, fun i => by simp⟩
  have hkey : ∀ (c : A) (m : M), (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m)
      = IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m) := by
    intro c m
    have hA1 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m)
        = (c • (1 : IsLocalRing.ResidueField A)) ⊗ₜ[A] m := (TensorProduct.smul_tmul c 1 m).symm
    have hA2 : c • (1 : IsLocalRing.ResidueField A) = IsLocalRing.residue A c := by
      rw [Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq]
    have hA3 : IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m)
        = (IsLocalRing.residue A c * 1) ⊗ₜ[A] m := rfl
    rw [hA1, hA2, hA3, mul_one]
  have hmat : ∀ i j : ι, bk.repr (B' j) i = IsLocalRing.residue A (bA.toMatrix G i j) := by
    intro i j
    have hGj : B' j = ∑ l : ι, IsLocalRing.residue A (bA.repr (G j) l) • bk l := by
      rw [hB' j]
      conv_lhs => rw [← bA.sum_repr (G j)]
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hkey, hbk l]
    rw [hGj, Module.Basis.repr_sum_self, Module.Basis.toMatrix_apply]
  have hdet : bk.det (⇑B') = IsLocalRing.residue A (bA.det G) := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
    congr 1
    ext i j
    simp only [Module.Basis.toMatrix_apply]
    exact hmat i j
  rw [← hdet]
  exact (bk.isUnit_det B').ne_zero


end

section
variable (k : Type*) [CommRing k] (A : Type*) [CommRing A] [Algebra k A] [IsLocalRing A] {n : Type*} [Fintype n] (bb : Module.Basis n A (KaehlerDifferential k A)) (J : Ideal A)
include bb

private theorem mem_maximalIdeal_mul_of_tmul_D_eq_zero_consolidated84 (hJmax : J ≤ IsLocalRing.maximalIdeal A)
    [Algebra.FormallySmooth k (A ⧸ J)] (z : A) (hz : z ∈ J)
    (h0 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A z = 0) :
    z ∈ IsLocalRing.maximalIdeal A * J := by
  classical
  obtain ⟨Jm, hJmdef⟩ : ∃ Jm : Ideal A, Jm = IsLocalRing.maximalIdeal A * J := ⟨_, rfl⟩
  have hmulJ : ∀ c ∈ IsLocalRing.maximalIdeal A, ∀ u ∈ J, c * u ∈ Jm := by
    intro c hc u hu
    rw [hJmdef]
    exact Ideal.mul_mem_mul hc hu
  have hJmle : Jm ≤ J := by
    rw [hJmdef]
    exact Ideal.mul_le_right
  have hsmulg : ∀ (c : A) (x : A ⧸ Jm), c • x = Ideal.Quotient.mk Jm c * x := by
    intro c x
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  have hsmulmk : ∀ c u : A,
      c • (Ideal.Quotient.mk Jm u) = Ideal.Quotient.mk Jm (c * u) := by
    intro c u
    rw [hsmulg, ← map_mul]
  have hρ0 : ∀ a ∈ Jm, (Ideal.Quotient.mkₐ A J) a = 0 := by
    intro a ha
    show Ideal.Quotient.mk J a = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hJmle ha)
  let ρA : (A ⧸ Jm) →ₐ[A] (A ⧸ J) :=
    Ideal.Quotient.liftₐ Jm (Ideal.Quotient.mkₐ A J) hρ0
  let ρ : (A ⧸ Jm) →ₐ[k] (A ⧸ J) := ρA.restrictScalars k
  have hρmkA : ∀ a : A, ρA (Ideal.Quotient.mk Jm a) = Ideal.Quotient.mk J a := fun _ => rfl
  have hρmk : ∀ a : A, ρ (Ideal.Quotient.mk Jm a) = Ideal.Quotient.mk J a := fun _ => rfl
  have hρsurj : Function.Surjective ρ := by
    intro c
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨Ideal.Quotient.mk Jm a, hρmk a⟩
  have hker2 : RingHom.ker (ρ : (A ⧸ Jm) →+* (A ⧸ J)) ^ 2 = ⊥ := by
    rw [pow_two]
    refine le_antisymm (Ideal.mul_le.mpr ?_) bot_le
    intro u hu v hv
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
    have ha : a ∈ J := by
      have h1 : Ideal.Quotient.mk J a = 0 := by
        rw [← hρmk a]
        exact RingHom.mem_ker.mp hu
      exact Ideal.Quotient.eq_zero_iff_mem.mp h1
    have hb : b ∈ J := by
      have h1 : Ideal.Quotient.mk J b = 0 := by
        rw [← hρmk b]
        exact RingHom.mem_ker.mp hv
      exact Ideal.Quotient.eq_zero_iff_mem.mp h1
    refine (Submodule.mem_bot _).mpr ?_
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hmulJ a (hJmax ha) b hb
  have hprod : ∀ u v : A ⧸ Jm, ρA u = 0 → ρA v = 0 → u * v = 0 := by
    intro u v hu hv
    have hmem : u * v ∈ RingHom.ker (ρ : (A ⧸ Jm) →+* (A ⧸ J)) ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (RingHom.mem_ker.mpr hu) (RingHom.mem_ker.mpr hv)
    rw [hker2] at hmem
    simpa using hmem
  obtain ⟨σ, hσ⟩ : ∃ σ : (A ⧸ J) →ₐ[k] (A ⧸ Jm), ∀ c, ρ (σ c) = c := by
    refine ⟨Algebra.FormallySmooth.liftOfSurjective
      (AlgHom.id k (A ⧸ J)) ρ hρsurj ⟨2, hker2⟩, fun c => ?_⟩
    have h := Algebra.FormallySmooth.comp_liftOfSurjective
      (AlgHom.id k (A ⧸ J)) ρ hρsurj ⟨2, hker2⟩
    have h2 := DFunLike.congr_fun h c
    simpa using h2
  have hρσ : ∀ c : A ⧸ J, ρA (σ c) = c := fun c => hσ c
  have hkerel : ∀ a : A,
      ρA (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a)) = 0 := by
    intro a
    rw [map_sub, hρmkA a, hρσ (Ideal.Quotient.mk J a), sub_self]
  have hmkJmsmul : ∀ (c : k) (a : A),
      Ideal.Quotient.mk Jm (c • a) = c • Ideal.Quotient.mk Jm a := by
    intro c a
    rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← Ideal.Quotient.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply k A (A ⧸ Jm)]
  have hmkJsmul : ∀ (c : k) (a : A),
      Ideal.Quotient.mk J (c • a) = c • Ideal.Quotient.mk J a := by
    intro c a
    rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← Ideal.Quotient.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply k A (A ⧸ J)]
  have hadd : ∀ a b : A,
      Ideal.Quotient.mk Jm (a + b) - σ (Ideal.Quotient.mk J (a + b))
        = (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a))
          + (Ideal.Quotient.mk Jm b - σ (Ideal.Quotient.mk J b)) := by
    intro a b
    simp only [map_add]
    ring
  have hsmulk : ∀ (c : k) (a : A),
      Ideal.Quotient.mk Jm (c • a) - σ (Ideal.Quotient.mk J (c • a))
        = (RingHom.id k) c • (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a)) := by
    intro c a
    show Ideal.Quotient.mk Jm (c • a) - σ (Ideal.Quotient.mk J (c • a))
      = c • (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a))
    rw [hmkJmsmul c a, hmkJsmul c a, map_smul, smul_sub]
  have hleib : ∀ a b : A,
      Ideal.Quotient.mk Jm (a * b) - σ (Ideal.Quotient.mk J (a * b))
        = a • (Ideal.Quotient.mk Jm b - σ (Ideal.Quotient.mk J b))
          + b • (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a)) := by
    intro a b
    have hz2 := hprod (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a))
      (Ideal.Quotient.mk Jm b - σ (Ideal.Quotient.mk J b)) (hkerel a) (hkerel b)
    rw [hsmulg a, hsmulg b]
    simp only [map_mul]
    linear_combination -hz2
  obtain ⟨Dder, hDapp⟩ : ∃ D : Derivation k A (A ⧸ Jm),
      ∀ a : A, D a = Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a) :=
    ⟨Derivation.mk'
      { toFun := fun a => Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a)
        map_add' := hadd
        map_smul' := hsmulk } hleib, fun _ => rfl⟩
  have hderivLift : ∀ a : A,
      Dder.liftKaehlerDifferential (KaehlerDifferential.D k A a) = Dder a := by
    intro a
    simp [Derivation.liftKaehlerDifferential_comp_D]
  have hcomp : ∀ ω : KaehlerDifferential k A,
      ρA (Dder.liftKaehlerDifferential ω) = 0 := by
    have hker : (⊤ : Submodule A (KaehlerDifferential k A)) ≤
        LinearMap.ker (ρA.toLinearMap.comp Dder.liftKaehlerDifferential) := by
      rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
      rintro y ⟨a, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply]
      show ρA (Dder.liftKaehlerDifferential (KaehlerDifferential.D k A a)) = 0
      rw [hderivLift a, hDapp a]
      exact hkerel a
    intro ω
    have h2 := hker (Submodule.mem_top : ω ∈ ⊤)
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at h2
    exact h2
  have hcoef : ∀ i : n,
      bb.repr (KaehlerDifferential.D k A z) i ∈ IsLocalRing.maximalIdeal A :=
    fun i => repr_mem_maximalIdeal_of_tmul_eq_zero_consolidated84 bb (KaehlerDifferential.D k A z) h0 i
  have hLb : ∀ i : n, ∃ u : A, u ∈ J ∧
      Dder.liftKaehlerDifferential (bb i) = Ideal.Quotient.mk Jm u := by
    intro i
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (Dder.liftKaehlerDifferential (bb i))
    refine ⟨u, ?_, hu.symm⟩
    have h1 : ρA (Ideal.Quotient.mk Jm u) = 0 := by
      rw [hu]
      exact hcomp (bb i)
    rw [hρmkA u] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  have hsum : Dder.liftKaehlerDifferential (KaehlerDifferential.D k A z) = 0 := by
    conv_lhs => rw [← bb.sum_repr (KaehlerDifferential.D k A z)]
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨u, huJ, hu⟩ := hLb i
    rw [map_smul, hu, hsmulmk, Ideal.Quotient.eq_zero_iff_mem]
    exact hmulJ _ (hcoef i) u huJ
  have hzval : Ideal.Quotient.mk Jm z
      = Dder.liftKaehlerDifferential (KaehlerDifferential.D k A z) := by
    rw [hderivLift z, hDapp z, Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero, sub_zero]
  have hfinal : Ideal.Quotient.mk Jm z = 0 := by
    rw [hzval, hsum]
  rw [← hJmdef]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hfinal

private theorem ideal_eq_span_of_tmul_D_mem_span_consolidated84 (hJfg : J.FG)
    (hJmax : J ≤ IsLocalRing.maximalIdeal A) [Algebra.FormallySmooth k (A ⧸ J)] (r : ℕ)
    (x : Fin r → A) (hxJ : ∀ i : Fin r, x i ∈ J)
    (hspan : ∀ y ∈ J,
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A y ∈
        Submodule.span (IsLocalRing.ResidueField A)
          (Set.range fun i : Fin r =>
            (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (x i))) :
    J = Ideal.span (Set.range x) := by
  classical
  have hsmeq : (IsLocalRing.maximalIdeal A • J : Ideal A)
      = IsLocalRing.maximalIdeal A * J := by
    rw [Ideal.smul_eq_mul]
  refine le_antisymm ?_ ?_
  · have hstep : J ≤ Ideal.span (Set.range x) ⊔ IsLocalRing.maximalIdeal A • J := by
      rw [hsmeq]
      intro y hy
      have hy' := hspan y hy
      rw [Submodule.mem_span_range_iff_exists_fun] at hy'
      obtain ⟨c, hc⟩ := hy'
      obtain ⟨c', hc'⟩ : ∃ c' : Fin r → A, ∀ i, IsLocalRing.residue A (c' i) = c i := by
        have hsurj : Function.Surjective (IsLocalRing.residue A) :=
          Ideal.Quotient.mk_surjective
        choose c' hc' using fun i => hsurj (c i)
        exact ⟨c', hc'⟩
      have hsum : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (∑ i, c' i * x i)
          = ∑ i, c i • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
            KaehlerDifferential.D k A (x i)) := by
        rw [map_sum, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm (c' i) (x i),
          KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal, hc' i]
        exact hJmax (hxJ i)
      have h0 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (y - ∑ i, c' i * x i) = 0 := by
        rw [map_sub, TensorProduct.tmul_sub, hsum, hc, sub_self]
      have hmemJ : y - ∑ i, c' i * x i ∈ J :=
        Submodule.sub_mem _ hy
          (Submodule.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hxJ i))
      have hsq := mem_maximalIdeal_mul_of_tmul_D_eq_zero_consolidated84 k A bb J hJmax _ hmemJ h0
      have hrw : y = (y - ∑ i, c' i * x i) + ∑ i, c' i * x i := by ring
      rw [hrw]
      refine Submodule.add_mem _ (Submodule.mem_sup_right hsq) (Submodule.mem_sup_left ?_)
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    have hbotne : (⊥ : Ideal A) ≠ ⊤ := by
      intro hcon
      have hmem1 : (1 : A) ∈ (⊥ : Ideal A) := by
        rw [hcon]; exact Submodule.mem_top
      have hz : (1 : A) = 0 := by simp at hmem1
      exact one_ne_zero hz
    exact Submodule.le_of_le_smul_of_le_jacobson_bot hJfg
      (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) hbotne).ge hstep
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hxJ i


end

private theorem map_eq_of_map_eq_of_away_mul_consolidated84 {S : Type*} [CommRing S] {T₁ T₂ : Type*}
    [CommRing T₁] [CommRing T₂] [Algebra S T₁] [Algebra S T₂] (g₁ d : S)
    [IsLocalization (Submonoid.powers g₁) T₁]
    [IsLocalization (Submonoid.powers (g₁ * d)) T₂] (I J : Ideal S)
    (h : Ideal.map (algebraMap S T₁) I = Ideal.map (algebraMap S T₁) J) :
    Ideal.map (algebraMap S T₂) I = Ideal.map (algebraMap S T₂) J := by
  have hgu : IsUnit (algebraMap S T₂ (g₁ * d)) :=
    IsLocalization.map_units (M := Submonoid.powers (g₁ * d)) T₂
      ⟨g₁ * d, Submonoid.mem_powers _⟩
  rw [map_mul] at hgu
  have hg1u : IsUnit (algebraMap S T₂ g₁) := isUnit_of_mul_isUnit_left hgu
  have hFu : ∀ y : Submonoid.powers g₁, IsUnit (algebraMap S T₂ (y : S)) := by
    rintro ⟨y, m, rfl⟩
    show IsUnit (algebraMap S T₂ (g₁ ^ m))
    rw [map_pow]
    exact hg1u.pow m
  obtain ⟨F, hF⟩ : ∃ F : T₁ →+* T₂, F.comp (algebraMap S T₁) = algebraMap S T₂ :=
    ⟨IsLocalization.lift (M := Submonoid.powers g₁) (S := T₁) hFu,
      RingHom.ext fun x => IsLocalization.lift_eq hFu x⟩
  calc Ideal.map (algebraMap S T₂) I
      = Ideal.map F (Ideal.map (algebraMap S T₁) I) := by rw [Ideal.map_map, hF]
    _ = Ideal.map F (Ideal.map (algebraMap S T₁) J) := by rw [h]
    _ = Ideal.map (algebraMap S T₂) J := by rw [Ideal.map_map, hF]

private theorem formallyEtale_away_of_isUnit_det_consolidated84 (k : Type*) [CommRing k] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (g : S) (T : Type*) [CommRing T] [Algebra S T] [IsLocalization (Submonoid.powers g) T]
    (w : ι → S)
    (hdet : IsUnit (algebraMap S T
      ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)))) :
    @Algebra.FormallyEtale (MvPolynomial ι k) T _ _
      (RingHom.toAlgebra
        (MvPolynomial.eval₂Hom ((algebraMap S T).comp (algebraMap k S))
          (fun j : ι => algebraMap S T (w j)))) := by
  classical
  let instKT : Algebra k T := ((algebraMap S T).comp (algebraMap k S)).toAlgebra
  let instAlgebraMvPolynomial : Algebra (MvPolynomial ι k) T :=
    ((algebraMap S T).comp (algebraMap (MvPolynomial ι k) S)).toAlgebra
  have instTkS : IsScalarTower k S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have instTPS : IsScalarTower (MvPolynomial ι k) S T :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have instTkP : IsScalarTower k (MvPolynomial ι k) T :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply k S T x,
        IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S x]
      rfl
  have instFEST : Algebra.FormallyEtale S T :=
    Algebra.FormallyEtale.of_isLocalization (M := Submonoid.powers g)
  have instFEPT : Algebra.FormallyEtale (MvPolynomial ι k) T :=
    Algebra.FormallyEtale.comp (MvPolynomial ι k) S T
  have instFSkT : Algebra.FormallySmooth k T :=
    Algebra.FormallySmooth.comp k (MvPolynomial ι k) T
  have hdet' : IsUnit ((basisKaehler k ι T).det
      fun i : ι => KaehlerDifferential.D k T (algebraMap S T (w i))) := by
    rw [← algebraMap_det_basisKaehler k ι S T w]
    exact hdet
  have h := formallyEtale_aeval_of_isUnit_det (basisKaehler k ι T)
    (fun i : ι => algebraMap S T (w i)) hdet'
  exact h

end

section

variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  [IsNoetherianRing S] (I q : Ideal S) [q.IsPrime]

section
variable (A : Type*) [CommRing A] [Algebra S A] [Algebra k A] [IsScalarTower k S A] [IsLocalization q.primeCompl A] [IsLocalRing A] [IsNoetherianRing A] [Algebra.FormallySmooth k (A ⧸ Ideal.map (algebraMap S A) I)] (hIq : I ≤ q)
include A hIq

theorem exists_away_ideal_eq_span_and_isUnit_det
    :
    ∃ (g : S) (w : ι → S) (T : Finset ι),
      g ∉ q ∧
      (∀ j ∈ T, w j ∈ I) ∧
      Ideal.map (algebraMap S (Localization.Away g)) (Ideal.span (w '' (↑T : Set ι))) =
        Ideal.map (algebraMap S (Localization.Away g)) I ∧
      (∀ j ∉ T, ∃ i : ι, w j = coord k ι S i) ∧
      IsUnit (algebraMap S (Localization.Away g)
        ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i))) := by
  classical
  have instFEloc : Algebra.FormallyEtale S A :=
    Algebra.FormallyEtale.of_isLocalization (M := q.primeCompl)
  let instPA : Algebra (MvPolynomial ι k) A :=
    ((algebraMap S A).comp (algebraMap (MvPolynomial ι k) S)).toAlgebra
  have instT1 : IsScalarTower (MvPolynomial ι k) S A :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have t2Space_cuspAdeles : IsScalarTower k (MvPolynomial ι k) A :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply k S A x,
        IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S x]
      rfl
  have instFEPA : Algebra.FormallyEtale (MvPolynomial ι k) A :=
    Algebra.FormallyEtale.comp (MvPolynomial ι k) S A
  have hmapq : Ideal.map (algebraMap S A) q = IsLocalRing.maximalIdeal A :=
    IsLocalization.AtPrime.map_eq_maximalIdeal q A
  have hJAm : Ideal.map (algebraMap S A) I ≤ IsLocalRing.maximalIdeal A := by
    rw [← hmapq]
    exact Ideal.map_mono hIq
  obtain ⟨tF, htF⟩ : I.FG := IsNoetherian.noetherian I
  have hspanI : Ideal.span (↑(tF.image (algebraMap S A)) : Set A)
      = Ideal.map (algebraMap S A) I := by
    rw [Finset.coe_image, ← htF, Ideal.map_span]
  obtain ⟨bset, hbsub, hbspan, hbind⟩ :=
    exists_linearIndependent (K := IsLocalRing.ResidueField A)
      (t := ((fun a : A => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A a) '' (↑(tF.image (algebraMap S A)) : Set A)))
  have hbfin : bset.Finite :=
    Set.Finite.subset (Set.Finite.image _ (Finset.finite_toSet _)) hbsub
  let _ : Fintype bset := hbfin.fintype
  choose pre hpre1 hpre2 using fun v : bset => hbsub v.2
  have hpre1' : ∀ v : bset, ∃ t : S, t ∈ tF ∧ algebraMap S A t = pre v := by
    intro v
    have hv := hpre1 v
    rw [Finset.mem_coe, Finset.mem_image] at hv
    obtain ⟨t, ht, hts⟩ := hv
    exact ⟨t, ht, hts⟩
  choose pres hpres1 hpres2 using hpre1'
  obtain ⟨s, hs⟩ : ∃ s : Fin (Fintype.card bset) → S,
      ∀ i, s i = pres ((Fintype.equivFin bset).symm i) := ⟨_, fun _ => rfl⟩
  have hsI : ∀ i, s i ∈ I := by
    intro i
    rw [hs i, ← htF]
    exact Submodule.subset_span (Finset.mem_coe.mpr (hpres1 _))
  have hfun : (fun i : Fin (Fintype.card bset) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A (s i)))
      = fun i : Fin (Fintype.card bset) =>
        (((Fintype.equivFin bset).symm i : bset) :
          IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A) := by
    funext i
    rw [hs i, hpres2]
    exact hpre2 _
  have hind : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : Fin (Fintype.card bset) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A (s i))) := by
    rw [hfun]
    exact hbind.comp _ (Fintype.equivFin bset).symm.injective
  have hrange : Set.range (fun i : Fin (Fintype.card bset) =>
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A (s i))) = bset := by
    rw [hfun]
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin bset).symm i).2
    · intro hv
      exact ⟨(Fintype.equivFin bset) ⟨v, hv⟩, by simp⟩
  have hxJ : ∀ i, algebraMap S A (s i) ∈ Ideal.map (algebraMap S A) I := fun i =>
    Ideal.mem_map_of_mem _ (hsI i)
  have hgen : ∀ y ∈ Ideal.map (algebraMap S A) I,
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A y ∈
        Submodule.span (IsLocalRing.ResidueField A)
          ((fun a : A => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
            KaehlerDifferential.D k A a) '' (↑(tF.image (algebraMap S A)) : Set A)) := by
    intro y hy
    rw [← hspanI] at hy
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hy
    rw [← hf, map_sum, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun a ha => ?_
    have ham : a ∈ IsLocalRing.maximalIdeal A := by
      refine hJAm ?_
      rw [← hspanI]
      exact Submodule.subset_span (Finset.mem_coe.mpr ha)
    have heq : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (f a • a)
        = IsLocalRing.residue A (f a) •
          ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A a) := by
      rw [smul_eq_mul, mul_comm,
        KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal]
      exact ham
    rw [heq]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨a, Finset.mem_coe.mpr ha, rfl⟩)
  have hspanx : ∀ y ∈ Ideal.map (algebraMap S A) I,
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A y ∈
        Submodule.span (IsLocalRing.ResidueField A)
          (Set.range fun i : Fin (Fintype.card bset) =>
            (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
              KaehlerDifferential.D k A (algebraMap S A (s i))) := by
    intro y hy
    rw [hrange, hbspan]
    exact hgen y hy
  have hJAeq : Ideal.map (algebraMap S A) I
      = Ideal.span (Set.range fun i : Fin (Fintype.card bset) => algebraMap S A (s i)) :=
    ideal_eq_span_of_tmul_D_mem_span_consolidated84 k A (basisKaehler k ι A) (Ideal.map (algebraMap S A) I)
      (IsNoetherian.noetherian _) hJAm
      (Fintype.card bset) (fun i => algebraMap S A (s i)) hxJ hspanx
  obtain ⟨bkk, hbk⟩ : ∃ bkk : Module.Basis ι (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A),
      ∀ i, bkk i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (basisKaehler k ι A i) :=
    ⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) (basisKaehler k ι A),
      fun i => by simp⟩
  obtain ⟨Jst, B, hbasisInl, hbasisInr⟩ := exists_basis_sum_of_linearIndependent bkk (Fintype.card bset)
    (fun i : Fin (Fintype.card bset) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A (s i))) hind
  have hcard1 : Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A)
      = Fintype.card (Fin (Fintype.card bset) ⊕ {j : ι // j ∈ Jst}) :=
    Module.finrank_eq_card_basis B
  have hcard2 : Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A) = Fintype.card ι :=
    Module.finrank_eq_card_basis bkk
  have hcard3 : Fintype.card {j : ι // j ∈ Jst} + Fintype.card {j : ι // ¬ (j ∈ Jst)}
      = Fintype.card ι := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl (fun j : ι => j ∈ Jst))
  rw [Fintype.card_sum, Fintype.card_fin] at hcard1
  have hcard4 : Fintype.card {j : ι // ¬ (j ∈ Jst)} = Fintype.card bset := by omega
  have e : {j : ι // ¬ (j ∈ Jst)} ≃ Fin (Fintype.card bset) := Fintype.equivFinOfCardEq hcard4
  obtain ⟨τ, hτl, hτr⟩ : ∃ τ : Fin (Fintype.card bset) ⊕ {j : ι // j ∈ Jst} ≃ ι,
      (∀ l : Fin (Fintype.card bset), τ (Sum.inl l) = ((e.symm l : ι))) ∧
      (∀ j : {j : ι // j ∈ Jst}, τ (Sum.inr j) = (j : ι)) :=
    ⟨(Equiv.sumCongr e.symm (Equiv.refl {j : ι // j ∈ Jst})).trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCompl (fun j : ι => j ∈ Jst))),
      fun l => rfl, fun j => rfl⟩
  obtain ⟨w, hwJ, hwn⟩ : ∃ w : ι → S, (∀ j, j ∈ Jst → w j = coord k ι S j) ∧
      (∀ x : {j : ι // ¬ (j ∈ Jst)}, w (x : ι) = s (e x)) := by
    refine ⟨fun j => if hj : j ∈ Jst then coord k ι S j else s (e ⟨j, hj⟩),
      fun j hj => ?_, fun x => ?_⟩
    · exact dif_pos hj
    · exact dif_neg x.2
  have hbasisApply : ∀ x : Fin (Fintype.card bset) ⊕ {j : ι // j ∈ Jst},
      B x = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A (w (τ x))) := by
    rintro (l | j)
    · rw [hbasisInl l, hτl l, hwn (e.symm l), Equiv.apply_symm_apply]
    · rw [hbasisInr j, hτr j, hwJ (j : ι) j.2, hbk (j : ι), basisKaehler_apply,
        algebraMap_coord]
  have hB'G : ∀ i : ι, (B.reindex τ) i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A (w i)) := by
    intro i
    rw [Module.Basis.reindex_apply, hbasisApply (τ.symm i), Equiv.apply_symm_apply]
  have hdetne := residue_det_ne_zero_of_tmul_eq_basis_consolidated84 (basisKaehler k ι A)
    (fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i))) (B.reindex τ) hB'G
  have hdetA : algebraMap S A ((basisKaehler k ι S).det
      (fun i : ι => KaehlerDifferential.D k S (w i)))
      = (basisKaehler k ι A).det
        (fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i))) :=
    algebraMap_det_basisKaehler k ι S A w
  have hg₀q : ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)) ∉ q := by
    intro hgq
    apply hdetne
    rw [← hdetA, IsLocalRing.residue_eq_zero_iff, ← hmapq]
    exact Ideal.mem_map_of_mem _ hgq
  have hspanA : Ideal.map (algebraMap S A) (Ideal.span (w '' (↑(Jstᶜ) : Set ι)))
      = Ideal.map (algebraMap S A) I := by
    rw [Ideal.map_span, hJAeq]
    congr 1
    ext v
    constructor
    · rintro ⟨u, ⟨j, hj, rfl⟩, rfl⟩
      have hj' : ¬ (j ∈ Jst) := Finset.mem_compl.mp (Finset.mem_coe.mp hj)
      have hwj : w j = s (e ⟨j, hj'⟩) := hwn ⟨j, hj'⟩
      exact ⟨e ⟨j, hj'⟩, by rw [hwj]⟩
    · rintro ⟨i, rfl⟩
      refine ⟨w ((e.symm i : ι)), ⟨(e.symm i : ι), ?_, rfl⟩, ?_⟩
      · exact Finset.mem_coe.mpr (Finset.mem_compl.mpr (e.symm i).2)
      · have hwj : w ((e.symm i : ι)) = s (e (e.symm i)) := hwn (e.symm i)
        rw [hwj, Equiv.apply_symm_apply]
  obtain ⟨g₁, hg₁q, hg₁eq⟩ := exists_away_map_ideal_eq q A
    (Ideal.span (w '' (↑(Jstᶜ) : Set ι))) I
    (Submodule.fg_span (Set.Finite.image w (Finset.finite_toSet _)))
    (IsNoetherian.noetherian I) hspanA
  refine ⟨g₁ * ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)), w,
    Jstᶜ, ?_, ?_, ?_, ?_, ?_⟩
  · intro hmem
    rcases Ideal.IsPrime.mem_or_mem ‹q.IsPrime› hmem with h1 | h2
    · exact hg₁q h1
    · exact hg₀q h2
  · intro j hj
    have hj' : ¬ (j ∈ Jst) := Finset.mem_compl.mp hj
    have hwj : w j = s (e ⟨j, hj'⟩) := hwn ⟨j, hj'⟩
    rw [hwj]
    exact hsI _
  · exact map_eq_of_map_eq_of_away_mul_consolidated84 g₁
      ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)) _ _ hg₁eq
  · intro j hj
    have hj' : j ∈ Jst := by
      by_contra hc
      exact hj (Finset.mem_compl.mpr hc)
    exact ⟨j, hwJ j hj'⟩
  · have hu : IsUnit (algebraMap S
        (Localization.Away (g₁ *
          ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i))))
        (g₁ * ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)))) :=
      IsLocalization.map_units _ ⟨_, Submonoid.mem_powers _⟩
    rw [map_mul] at hu
    exact isUnit_of_mul_isUnit_right hu

theorem exists_away_ideal_eq_span_and_formallyEtale
    :
    ∃ (g : S) (w : ι → S) (T : Finset ι),
      g ∉ q ∧
      (∀ j ∈ T, w j ∈ I) ∧
      Ideal.map (algebraMap S (Localization.Away g)) (Ideal.span (w '' (↑T : Set ι))) =
        Ideal.map (algebraMap S (Localization.Away g)) I ∧
      (∀ j ∉ T, ∃ i : ι, w j = coord k ι S i) ∧
      @Algebra.FormallyEtale (MvPolynomial ι k) (Localization.Away g) _ _
        (RingHom.toAlgebra
          (MvPolynomial.eval₂Hom
            ((algebraMap S (Localization.Away g)).comp (algebraMap k S))
            (fun j : ι => algebraMap S (Localization.Away g) (w j)))) := by
  classical
  obtain ⟨g, w, T, hgq, hwI, hmap, hcoord, hdet⟩ :=
    exists_away_ideal_eq_span_and_isUnit_det k ι S I q A hIq
  exact ⟨g, w, T, hgq, hwI, hmap, hcoord,
    formallyEtale_away_of_isUnit_det_consolidated84 k ι S g (Localization.Away g) w hdet⟩


end

end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimension
section

open CategoryTheory AlgebraicGeometry

section
namespace FunctorialResolution.EmbeddedResolution

def HasSmoothCoordCodim {X Y : Scheme.{u}} {k : Type u} [Field k]
    (s : Y ⟶ Spec (CommRingCat.of k)) (t : X ⟶ Y) (c : ℕ) : Prop :=
  ∀ x : X, ∃ (U : Y.Opens) (_ : t.base x ∈ U)
    (q : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c))),
    Smooth q ∧
      q ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) = U.ι ≫ s ∧
      restrictIdeal t.ker U = (coordSubspaceIdeal k c Finset.univ).comap q

theorem hasSmoothCoordCodim_iff {X Y : Scheme.{u}} {k : Type u} [Field k]
    (s : Y ⟶ Spec (CommRingCat.of k)) (t : X ⟶ Y) (c : ℕ) :
    HasSmoothCoordCodim s t c ↔
      ∀ x : X, ∃ (U : Y.Opens) (_ : t.base x ∈ U)
        (q : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c))),
        Smooth q ∧
          q ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) = U.ι ≫ s ∧
          restrictIdeal t.ker U = (coordSubspaceIdeal k c Finset.univ).comap q :=
  Iff.rfl

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimensionPullback
section

open CategoryTheory AlgebraicGeometry

section
namespace FunctorialResolution.EmbeddedResolution

namespace HasSmoothCoordCodim

variable {k : Type u} [Field k]

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private theorem smooth_resLE_consolidated110 [Smooth f]
    (U : Y.Opens) : Smooth (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact MorphismProperty.of_isPullback (P := @Smooth)
    (isPullback_morphismRestrict f U).flip ‹Smooth f›

private theorem resLE_comp_ι_consolidated110 (U : Y.Opens) :
    f.resLE U (f ⁻¹ᵁ U) le_rfl ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := by
  simp [Scheme.Hom.resLE_comp_ι]


end

private theorem ker_eq_comap_of_isPullback_consolidated110 {X X' X'' X₂ : Scheme.{u}} {τ : X ⟶ X'} [IsClosedImmersion τ]
    {g : X'' ⟶ X'} {τ'' : X₂ ⟶ X''} {p : X₂ ⟶ X} (H : IsPullback p τ'' τ g) :
    τ''.ker = τ.ker.comap g := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion τ g, ← H.flip.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

private theorem ker_resLE_consolidated110 {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (U : Y.Opens) :
    (f.resLE U (f ⁻¹ᵁ U) le_rfl).ker = f.ker.comap U.ι := by
  have H := (isPullback_morphismRestrict f U).flip
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact ker_eq_comap_of_isPullback_consolidated110 H

private theorem ker_comp_iso_consolidated110 {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (φ : Y ≅ Z) :
    (f ≫ φ.hom).ker = f.ker.comap φ.inv :=
  ker_eq_comap_of_isPullback_consolidated110 (p := 𝟙 X) (IsPullback.of_horiz_isIso ⟨by simp⟩)

theorem resLE_open {X X' : Scheme.{u}}
    {s : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} [IsClosedImmersion τ] {c : ℕ}
    (h : HasSmoothCoordCodim s τ c) (O : X'.Opens) :
    HasSmoothCoordCodim (O.ι ≫ s) (τ.resLE O (τ ⁻¹ᵁ O) le_rfl) c := by
  intro x
  obtain ⟨U, hU, q, hq, hqs, hker⟩ := h ((τ ⁻¹ᵁ O).ι.base x)
  have : Smooth q := hq
  have : Smooth O.ι := inferInstance
  have : Smooth (O.ι.resLE U (O.ι ⁻¹ᵁ U) le_rfl) := smooth_resLE_consolidated110 O.ι U
  have hw : O.ι.base ((τ.resLE O (τ ⁻¹ᵁ O) le_rfl).base x) = τ.base ((τ ⁻¹ᵁ O).ι.base x) :=
    congrArg (fun m : (τ ⁻¹ᵁ O).toScheme ⟶ X' => m.base x) (resLE_comp_ι_consolidated110 τ O)
  refine ⟨O.ι ⁻¹ᵁ U, ?_, O.ι.resLE U (O.ι ⁻¹ᵁ U) le_rfl ≫ q, inferInstance, ?_, ?_⟩
  · show O.ι.base ((τ.resLE O (τ ⁻¹ᵁ O) le_rfl).base x) ∈ U
    rw [hw]
    exact hU
  · rw [Category.assoc, hqs, ← Category.assoc, resLE_comp_ι_consolidated110 O.ι U, Category.assoc]
  · calc restrictIdeal (τ.resLE O (τ ⁻¹ᵁ O) le_rfl).ker (O.ι ⁻¹ᵁ U)
        = (τ.ker.comap O.ι).comap (O.ι ⁻¹ᵁ U).ι := by
          rw [restrictIdeal_eq_comap_ι, ker_resLE_consolidated110]
      _ = τ.ker.comap ((O.ι ⁻¹ᵁ U).ι ≫ O.ι) := by rw [Scheme.IdealSheafData.comap_comp]
      _ = τ.ker.comap (O.ι.resLE U (O.ι ⁻¹ᵁ U) le_rfl ≫ U.ι) := by rw [resLE_comp_ι_consolidated110 O.ι U]
      _ = (τ.ker.comap U.ι).comap (O.ι.resLE U (O.ι ⁻¹ᵁ U) le_rfl) := by
          rw [Scheme.IdealSheafData.comap_comp]
      _ = ((coordSubspaceIdeal k c Finset.univ).comap q).comap
            (O.ι.resLE U (O.ι ⁻¹ᵁ U) le_rfl) := by rw [← restrictIdeal_eq_comap_ι, hker]
      _ = (coordSubspaceIdeal k c Finset.univ).comap
            (O.ι.resLE U (O.ι ⁻¹ᵁ U) le_rfl ≫ q) := by rw [Scheme.IdealSheafData.comap_comp]

theorem comp_iso_hom {X X' X'' : Scheme.{u}}
    {s : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} [IsClosedImmersion τ] {c : ℕ}
    (h : HasSmoothCoordCodim s τ c) (φ : X' ≅ X'')
    (s' : X'' ⟶ Spec (CommRingCat.of k)) (hφ : φ.hom ≫ s' = s) :
    HasSmoothCoordCodim s' (τ ≫ φ.hom) c := by
  intro x
  obtain ⟨U, hU, q, hq, hqs, hker⟩ := h x
  have : Smooth q := hq
  have : Smooth φ.inv := inferInstance
  have : Smooth (φ.inv.resLE U (φ.inv ⁻¹ᵁ U) le_rfl) := smooth_resLE_consolidated110 φ.inv U
  have hs' : φ.inv ≫ s = s' := by rw [← hφ, Iso.inv_hom_id_assoc]
  refine ⟨φ.inv ⁻¹ᵁ U, ?_, φ.inv.resLE U (φ.inv ⁻¹ᵁ U) le_rfl ≫ q, inferInstance, ?_, ?_⟩
  · show φ.inv.base ((τ ≫ φ.hom).base x) ∈ U
    have hb : φ.inv.base ((τ ≫ φ.hom).base x) = τ.base x :=
      congrArg (fun m : X ⟶ X' => m.base x) (by simp : (τ ≫ φ.hom) ≫ φ.inv = τ)
    rw [hb]
    exact hU
  · rw [Category.assoc, hqs, ← Category.assoc, resLE_comp_ι_consolidated110 φ.inv U, Category.assoc, hs']
  · calc restrictIdeal (τ ≫ φ.hom).ker (φ.inv ⁻¹ᵁ U)
        = (τ.ker.comap φ.inv).comap (φ.inv ⁻¹ᵁ U).ι := by
          rw [restrictIdeal_eq_comap_ι, ker_comp_iso_consolidated110]
      _ = τ.ker.comap ((φ.inv ⁻¹ᵁ U).ι ≫ φ.inv) := by rw [Scheme.IdealSheafData.comap_comp]
      _ = τ.ker.comap (φ.inv.resLE U (φ.inv ⁻¹ᵁ U) le_rfl ≫ U.ι) := by
          rw [resLE_comp_ι_consolidated110 φ.inv U]
      _ = (τ.ker.comap U.ι).comap (φ.inv.resLE U (φ.inv ⁻¹ᵁ U) le_rfl) := by
          rw [Scheme.IdealSheafData.comap_comp]
      _ = ((coordSubspaceIdeal k c Finset.univ).comap q).comap
            (φ.inv.resLE U (φ.inv ⁻¹ᵁ U) le_rfl) := by rw [← restrictIdeal_eq_comap_ι, hker]
      _ = (coordSubspaceIdeal k c Finset.univ).comap
            (φ.inv.resLE U (φ.inv ⁻¹ᵁ U) le_rfl ≫ q) := by rw [Scheme.IdealSheafData.comap_comp]

theorem iso_hom_comp {X X' X₀ : Scheme.{u}}
    {s : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} {c : ℕ}
    (h : HasSmoothCoordCodim s τ c) (e : X₀ ≅ X) :
    HasSmoothCoordCodim s (e.hom ≫ τ) c := by
  intro x
  obtain ⟨U, hU, q, hq, hqs, hker⟩ := h (e.hom.base x)
  refine ⟨U, hU, q, hq, hqs, ?_⟩
  rw [restrictIdeal_eq_comap_ι, Scheme.Hom.ker_comp_of_isIso, ← restrictIdeal_eq_comap_ι, hker]

end HasSmoothCoordCodim

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
section

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

section
variable (R S : Type*) [CommRing R] [CommRing S]

private theorem exists_prime_le_under_eq_of_hasGoingDown_consolidated97 [Algebra R S]
    [Algebra.HasGoingDown R S] (p : Ideal R) [p.IsPrime] (Q : Ideal S) [Q.IsPrime]
    (hle : p ≤ Ideal.under R Q) :
    ∃ P : Ideal S, P ≤ Q ∧ P.IsPrime ∧ Ideal.under R P = p := by
  rcases eq_or_lt_of_le hle with h | h
  · exact ⟨Q, le_rfl, ‹Q.IsPrime›, h.symm⟩
  · obtain ⟨P, hPQ, hP, hlo⟩ :=
      Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt (R := R) Q h
    exact ⟨P, hPQ, hP, hlo.over.symm⟩

private theorem exists_ltSeries_le_of_hasGoingDown_consolidated97 [Algebra R S] [Algebra.HasGoingDown R S] (n : ℕ) :
    ∀ (p : LTSeries (PrimeSpectrum R)), p.length = n →
      ∀ (Q : Ideal S), Q.IsPrime → p.last.asIdeal ≤ Ideal.under R Q →
        ∃ q : LTSeries (PrimeSpectrum S), q.length = n ∧ q.last.asIdeal ≤ Q ∧
          Ideal.under R q.last.asIdeal = p.last.asIdeal := by
  induction n with
  | zero =>
      intro p hp Q hQ hle
      have := hQ
      have : p.last.asIdeal.IsPrime := p.last.isPrime
      obtain ⟨P, hPQ, hP, hunder⟩ := exists_prime_le_under_eq_of_hasGoingDown_consolidated97 R S p.last.asIdeal Q hle
      exact ⟨RelSeries.singleton _ ⟨P, hP⟩, rfl, hPQ, hunder⟩
  | succ n ih =>
      intro p hp Q hQ hle
      have := hQ
      have : p.last.asIdeal.IsPrime := p.last.isPrime
      obtain ⟨P, hPQ, hP, hunder⟩ := exists_prime_le_under_eq_of_hasGoingDown_consolidated97 R S p.last.asIdeal Q hle
      have hlen : p.length ≠ 0 := by omega
      have hlt : p.eraseLast.last < p.last := p.eraseLast_last_rel_last hlen
      have hltI : p.eraseLast.last.asIdeal < p.last.asIdeal :=
        (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt
      have hlen' : p.eraseLast.length = n := by
        have := RelSeries.eraseLast_length p
        omega
      have hle' : p.eraseLast.last.asIdeal ≤ Ideal.under R P := by
        rw [hunder]
        exact le_of_lt hltI
      obtain ⟨q, hq1, hq2, hq3⟩ := ih p.eraseLast hlen' P hP hle'
      have hne : q.last.asIdeal ≠ P := by
        intro h
        rw [h, hunder] at hq3
        exact (ne_of_lt hltI) hq3.symm
      have hrel : q.last < (⟨P, hP⟩ : PrimeSpectrum S) :=
        (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp (lt_of_le_of_ne hq2 hne)
      refine ⟨q.snoc ⟨P, hP⟩ hrel, ?_, ?_, ?_⟩
      · rw [RelSeries.snoc_length, hq1]
      · rw [RelSeries.last_snoc]; exact hPQ
      · rw [RelSeries.last_snoc]; exact hunder

private theorem ringKrullDim_le_of_hasGoingDown_consolidated97 [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.HasGoingDown R S] :
    ringKrullDim R ≤ ringKrullDim S := by
  have key : ∀ p : LTSeries (PrimeSpectrum R), (p.length : WithBot ℕ∞) ≤ ringKrullDim S := by
    intro p
    have hmax : p.last.asIdeal ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal p.last.isPrime.ne_top
    have hp : p.last.asIdeal ≤ Ideal.under R (IsLocalRing.maximalIdeal S) := by
      intro x hx
      exact map_nonunit (algebraMap R S) x (hmax hx)
    obtain ⟨q, hq1, -, -⟩ :=
      exists_ltSeries_le_of_hasGoingDown_consolidated97 R S p.length p rfl (IsLocalRing.maximalIdeal S)
        inferInstance hp
    calc (p.length : WithBot ℕ∞) = (q.length : WithBot ℕ∞) := by rw [hq1]
      _ ≤ ringKrullDim S := Order.LTSeries.length_le_krullDim q
  exact iSup_le key

private theorem spanFinrank_map_le_consolidated97 [IsNoetherianRing R]
    [Algebra R S] (I : Ideal R) :
    (Ideal.map (algebraMap R S) I).spanFinrank ≤ I.spanFinrank := by
  obtain ⟨s, hcard, hspan⟩ := Submodule.exists_span_set_card_eq_spanRank I
  have hIfg : Submodule.FG (I : Submodule R R) := IsNoetherian.noetherian I
  have hrank : I.spanRank = (I.spanFinrank : Cardinal) :=
    Submodule.FG.spanRank_eq_spanFinrank hIfg
  have hslt : Cardinal.mk s < Cardinal.aleph0 := by
    rw [hcard, hrank]
    exact Cardinal.natCast_lt_aleph0
  have hspan' : Ideal.span s = I := hspan
  have hmapspan : Ideal.map (algebraMap R S) I = Ideal.span ((algebraMap R S) '' s) := by
    rw [← hspan', Ideal.map_span]
  have h1 : (Ideal.map (algebraMap R S) I).spanRank ≤ Cardinal.mk ((algebraMap R S) '' s) := by
    rw [hmapspan]
    exact Submodule.spanRank_span_le_card _
  have h2 := Cardinal.mk_image_le_lift (f := (algebraMap R S : R → S)) (s := s)
  have hliftlt : Cardinal.lift.{_, _} (Cardinal.mk s) < Cardinal.aleph0 :=
    Cardinal.lift_lt_aleph0.mpr hslt
  have h4 : Cardinal.mk ((algebraMap R S) '' s) < Cardinal.aleph0 :=
    Cardinal.lift_lt_aleph0.mp (lt_of_le_of_lt h2 hliftlt)
  have h3 : Cardinal.toNat (Cardinal.mk ((algebraMap R S) '' s)) ≤
      Cardinal.toNat (Cardinal.mk s) := by
    have := Cardinal.toNat_le_toNat h2 hliftlt
    rwa [Cardinal.toNat_lift, Cardinal.toNat_lift] at this
  calc (Ideal.map (algebraMap R S) I).spanFinrank
      = Cardinal.toNat (Ideal.map (algebraMap R S) I).spanRank :=
        Submodule.spanFinrank.eq_def _
    _ ≤ Cardinal.toNat (Cardinal.mk ((algebraMap R S) '' s)) := Cardinal.toNat_le_toNat h1 h4
    _ ≤ Cardinal.toNat (Cardinal.mk s) := h3
    _ = I.spanFinrank := by rw [hcard, ← Submodule.spanFinrank.eq_def]

private theorem ringKrullDim_le_of_map_maximalIdeal_consolidated97 [IsLocalRing S] [IsNoetherianRing S] [_root_.IsRegularLocalRing R] [Algebra R S]
    (hmax : IsLocalRing.maximalIdeal S = (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :
    ringKrullDim S ≤ ringKrullDim R := by
  have : IsNoetherianRing R := inferInstance
  have hne : IsLocalRing.maximalIdeal S ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  have hh : (IsLocalRing.maximalIdeal S).height ≤ ((IsLocalRing.maximalIdeal S).spanFinrank : ℕ∞) :=
    Ideal.height_le_spanFinrank _ hne
  have hfr : (IsLocalRing.maximalIdeal S).spanFinrank ≤
      (IsLocalRing.maximalIdeal R).spanFinrank := by
    rw [hmax]
    exact spanFinrank_map_le_consolidated97 R S _
  have hR := (_root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := R))
  rw [← hR, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := S)]
  have h : (IsLocalRing.maximalIdeal S).height ≤ ((IsLocalRing.maximalIdeal R).spanFinrank : ℕ∞) :=
    le_trans hh (Nat.cast_le.mpr hfr)
  exact_mod_cast h


end

section
variable (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [_root_.IsRegularLocalRing R] [Algebra R S] [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] [Module.Flat R S]
include R

theorem ringKrullDim_eq_of_flat_formallyUnramified :
    ringKrullDim S = ringKrullDim R := by
  have : IsLocalRing R := inferInstance
  have : IsNoetherianRing R := inferInstance
  have : Algebra.HasGoingDown R S := inferInstance
  have h1 : ringKrullDim R ≤ ringKrullDim S := ringKrullDim_le_of_hasGoingDown_consolidated97 R S
  have hmax : IsLocalRing.maximalIdeal S = (IsLocalRing.maximalIdeal R).map (algebraMap R S) :=
    (Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)).symm
  exact le_antisymm (ringKrullDim_le_of_map_maximalIdeal_consolidated97 R S hmax) h1

theorem isRegularLocalRing_of_flat_formallyUnramified :
    _root_.IsRegularLocalRing S := by
  have : IsLocalRing R := inferInstance
  have : IsNoetherianRing R := inferInstance
  have hdim : ringKrullDim S = ringKrullDim R := ringKrullDim_eq_of_flat_formallyUnramified R S
  have hR : ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    (isRegularLocalRing_iff R).mp inferInstance
  have hmax : IsLocalRing.maximalIdeal S = (IsLocalRing.maximalIdeal R).map (algebraMap R S) :=
    (Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)).symm
  have h4 : (IsLocalRing.maximalIdeal S).spanFinrank
      ≤ (IsLocalRing.maximalIdeal R).spanFinrank := by
    rw [hmax]
    exact spanFinrank_map_le_consolidated97 R S _
  have hh : (IsLocalRing.maximalIdeal S).height
      ≤ ((IsLocalRing.maximalIdeal S).spanFinrank : ℕ∞) :=
    Ideal.height_le_spanFinrank _ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  have hle1 : ringKrullDim S ≤ ((IsLocalRing.maximalIdeal S).spanFinrank : WithBot ℕ∞) := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := S)]
    exact_mod_cast hh
  refine (isRegularLocalRing_iff S).mpr (le_antisymm ?_ hle1)
  rw [hdim, ← hR]
  exact_mod_cast h4


end

private theorem isRegularLocalRing_stalk_of_iso_spec_consolidated97 {X : Scheme.{u}} (R : Type u) [CommRing R]
    (hreg : ∀ (p : Ideal R) (hp : p.IsPrime),
      _root_.IsRegularLocalRing (@Localization.AtPrime R _ p hp))
    (e : X ≅ Spec (CommRingCat.of R)) (x : X) :
    _root_.IsRegularLocalRing (X.presheaf.stalk x) := by
  let y : PrimeSpectrum R := e.hom.base x
  have hp : y.asIdeal.IsPrime := y.isPrime
  have h1 : _root_.IsRegularLocalRing (@Localization.AtPrime R _ y.asIdeal hp) :=
    hreg y.asIdeal hp
  have h2 : IsLocalization.AtPrime ((Spec.structureSheaf R).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y
  have e2 : Localization.AtPrime y.asIdeal ≃+* ((Spec.structureSheaf R).presheaf.stalk y) :=
    (IsLocalization.algEquiv y.asIdeal.primeCompl (Localization.AtPrime y.asIdeal)
      ((Spec.structureSheaf R).presheaf.stalk y)).toRingEquiv
  have h3 : _root_.IsRegularLocalRing ((Spec.structureSheaf R).presheaf.stalk y) :=
    IsRegularLocalRing.of_ringEquiv e2
  have h4 : IsIso (e.hom.stalkMap x) := inferInstance
  have e3 : ((Spec.structureSheaf R).presheaf.stalk y) ≃+* (X.presheaf.stalk x) :=
    (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv
  exact IsRegularLocalRing.of_ringEquiv e3

theorem isRegularLocalRing_stalk_affineSpace (k : Type u) [Field k] (n : Type u) [Finite n]
    (x : AffineSpace n (Spec (CommRingCat.of k))) :
    _root_.IsRegularLocalRing ((AffineSpace n (Spec (CommRingCat.of k))).presheaf.stalk x) :=
  isRegularLocalRing_stalk_of_iso_spec_consolidated97 (MvPolynomial n k)
    (fun p hp => by have := hp; infer_instance)
    (AffineSpace.SpecIso n (CommRingCat.of k)) x

private theorem isRegularLocalRing_stalk_of_stalkMap_flat_formallyUnramified_consolidated97 {Y Z : Scheme.{u}} (f : Y ⟶ Z) (y : Y)
    (hZ : _root_.IsRegularLocalRing (Z.presheaf.stalk (f.base y)))
    (hflat : (f.stalkMap y).hom.Flat)
    (heft : (f.stalkMap y).hom.EssFiniteType)
    (hfu : (f.stalkMap y).hom.FormallyUnramified) :
    _root_.IsRegularLocalRing (Y.presheaf.stalk y) := by
  have := hZ
  let _ : Algebra (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
    (f.stalkMap y).hom.toAlgebra
  have : IsLocalHom (algebraMap (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
  have : Module.Flat (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := hflat
  have : Algebra.EssFiniteType (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := heft
  have : Algebra.FormallyUnramified (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := hfu
  have : IsNoetherianRing (Y.presheaf.stalk y) :=
    Algebra.EssFiniteType.isNoetherianRing
      (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)
  exact isRegularLocalRing_of_flat_formallyUnramified
    (Z.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)

private theorem isRegularLocalRing_stalk_of_opens_consolidated97 {X : Scheme.{u}} (U : X.Opens) (y : U)
    (h : _root_.IsRegularLocalRing (U.toScheme.presheaf.stalk y)) :
    _root_.IsRegularLocalRing (X.presheaf.stalk y.1) := by
  have := h
  exact IsRegularLocalRing.of_ringEquiv (U.stalkIso y).commRingCatIsoToRingEquiv

section
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))

theorem isRegularLocalRing_stalk_of_smooth [Smooth p] (x : X) :
    _root_.IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, m, hxU, -, ⟨c⟩⟩ := exists_etaleChart p x
  have := c.isEtale
  have hreg : _root_.IsRegularLocalRing
      ((affineSpaceFin k m).presheaf.stalk (c.map.base (⟨x, hxU⟩ : U))) :=
    isRegularLocalRing_stalk_affineSpace k (ULift.{u} (Fin m)) _
  have h2 : _root_.IsRegularLocalRing (U.toScheme.presheaf.stalk (⟨x, hxU⟩ : U)) :=
    isRegularLocalRing_stalk_of_stalkMap_flat_formallyUnramified_consolidated97 c.map (⟨x, hxU⟩ : U) hreg
      (AlgebraicGeometry.Flat.stalkMap c.map (⟨x, hxU⟩ : U))
      (AlgebraicGeometry.LocallyOfFiniteType.stalkMap c.map (⟨x, hxU⟩ : U))
      (AlgebraicGeometry.FormallyUnramified.stalkMap c.map (⟨x, hxU⟩ : U))
  exact isRegularLocalRing_stalk_of_opens_consolidated97 U (⟨x, hxU⟩ : U) h2

theorem isDomain_stalk_of_smooth [Smooth p] (x : X) :
    IsDomain (X.presheaf.stalk x) := by
  have : _root_.IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth p x
  exact IsRegularLocalRing.isDomain _

theorem smooth_isDomain_stalk (hp : Smooth p) (x : X) :
    IsDomain (X.presheaf.stalk x) := by
  have := hp
  exact isDomain_stalk_of_smooth p x

theorem isReduced_of_smooth [Smooth p] :
    IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    have := isDomain_stalk_of_smooth p x
    infer_instance
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk X

theorem smooth_isReduced (hp : Smooth p) :
    IsReduced X := by
  have := hp
  exact isReduced_of_smooth p


end

private noncomputable def pointOfIsoSpec {Y : Scheme.{u}} (R : CommRingCat.{u}) (e : Y ≅ Spec R) (y : Y) :
    PrimeSpectrum ↥R :=
  e.hom.base y

section
variable {α : Type*} [TopologicalSpace α]

private theorem eq_closure_of_mem_irreducibleComponents_consolidated97 {V : Set α} (hVopen : IsOpen V) (hVirr : IsIrreducible V) {T : Set α}
    (hT : T ∈ irreducibleComponents α) {x : α} (hxV : x ∈ V) (hxT : x ∈ T) : T = closure V := by
  have hsub : T ⊆ closure V := by
    intro y hy
    rw [mem_closure_iff]
    intro o ho hyo
    obtain ⟨z, -, hzo, hzV⟩ := hT.1.2 o V ho hVopen ⟨y, hy, hyo⟩ ⟨x, hxT, hxV⟩
    exact ⟨z, hzo, hzV⟩
  exact le_antisymm hsub (hT.2 hVirr.closure hsub)

private theorem exists_isOpen_isIrreducible_of_unique_irreducibleComponent_consolidated97 (hfin : (irreducibleComponents α).Finite) {T₀ : Set α} (hT₀ : IsIrreducible T₀) {z : α}
    (_hz : z ∈ T₀) (huniq : ∀ T ∈ irreducibleComponents α, z ∈ T → T = T₀) :
    ∃ W : Set α, IsOpen W ∧ IsIrreducible W ∧ z ∈ W := by
  have hSfin : Set.Finite {T : Set α | T ∈ irreducibleComponents α ∧ z ∉ T} :=
    Set.Finite.subset hfin (fun T hT => hT.1)
  have hScl : IsClosed (⋃₀ {T : Set α | T ∈ irreducibleComponents α ∧ z ∉ T}) := by
    rw [Set.sUnion_eq_biUnion]
    exact Set.Finite.isClosed_biUnion hSfin
      (fun T hT => isClosed_of_mem_irreducibleComponents _ hT.1)
  have hzW : z ∈ (⋃₀ {T : Set α | T ∈ irreducibleComponents α ∧ z ∉ T})ᶜ := by
    intro hcon
    obtain ⟨T, hTS, hzT⟩ := hcon
    exact hTS.2 hzT
  have hWT : (⋃₀ {T : Set α | T ∈ irreducibleComponents α ∧ z ∉ T})ᶜ ⊆ T₀ := by
    intro y hy
    have hc : irreducibleComponent y ∈ irreducibleComponents α :=
      irreducibleComponent_mem_irreducibleComponents y
    have hzc : z ∈ irreducibleComponent y := by
      by_contra hcon
      exact hy ⟨irreducibleComponent y, ⟨hc, hcon⟩, mem_irreducibleComponent⟩
    rw [← huniq _ hc hzc]
    exact mem_irreducibleComponent
  refine ⟨_, hScl.isOpen_compl, ⟨⟨z, hzW⟩, ?_⟩, hzW⟩
  intro u v hu hv hu' hv'
  obtain ⟨a, haW, hau⟩ := hu'
  obtain ⟨b, hbW, hbv⟩ := hv'
  obtain ⟨c, -, ⟨hcu, hcW⟩, hcv, -⟩ :=
    hT₀.2 (u ∩ (⋃₀ {T : Set α | T ∈ irreducibleComponents α ∧ z ∉ T})ᶜ)
      (v ∩ (⋃₀ {T : Set α | T ∈ irreducibleComponents α ∧ z ∉ T})ᶜ)
      (hu.inter hScl.isOpen_compl) (hv.inter hScl.isOpen_compl)
      ⟨a, hWT haW, hau, haW⟩ ⟨b, hWT hbW, hbv, hbW⟩
  exact ⟨c, hcW, hcu, hcv⟩


end

private theorem exists_isOpen_isIrreducible_of_unique_minimal_prime_le_consolidated97 {A : Type u} [CommRing A]
    [IsNoetherianRing A] (P : PrimeSpectrum A) (K : Ideal A) (hK : K.IsPrime)
    (hmin : ∀ q : Ideal A, q.IsPrime → q ≤ P.asIdeal → K ≤ q) :
    ∃ W : Set (PrimeSpectrum A), IsOpen W ∧ IsIrreducible W ∧ P ∈ W := by
  have hT₀irr : IsIrreducible (PrimeSpectrum.zeroLocus (K : Set A)) := by
    rw [PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime,
      PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hK.radical]
    exact hK
  have hPT₀ : P ∈ PrimeSpectrum.zeroLocus (K : Set A) := by
    rw [PrimeSpectrum.mem_zeroLocus]
    exact fun a ha => hmin P.asIdeal P.isPrime le_rfl ha
  have hcomp : ∀ T ∈ irreducibleComponents (PrimeSpectrum A), P ∈ T →
      T = PrimeSpectrum.zeroLocus (K : Set A) := by
    intro T hT hPmem
    have hTcl : IsClosed T := isClosed_of_mem_irreducibleComponents _ hT
    have hq : (PrimeSpectrum.vanishingIdeal T).IsPrime :=
      PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hT.1
    have hTeq : PrimeSpectrum.zeroLocus ((PrimeSpectrum.vanishingIdeal T : Ideal A) : Set A)
        = T := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hTcl.closure_eq]
    have hqP : PrimeSpectrum.vanishingIdeal T ≤ P.asIdeal := fun a ha =>
      (PrimeSpectrum.mem_vanishingIdeal T a).mp ha P hPmem
    have hKq : K ≤ PrimeSpectrum.vanishingIdeal T := hmin _ hq hqP
    have hTsub : T ⊆ PrimeSpectrum.zeroLocus (K : Set A) := by
      rw [← hTeq]
      exact PrimeSpectrum.zeroLocus_anti_mono (SetLike.coe_subset_coe.mpr hKq)
    exact le_antisymm hTsub (hT.2 hT₀irr hTsub)
  have hfin : (irreducibleComponents (PrimeSpectrum A)).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  exact exists_isOpen_isIrreducible_of_unique_irreducibleComponent_consolidated97 hfin hT₀irr hPT₀ hcomp

section
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (V : X.Opens) (hV : IsAffineOpen V)
include p hV

private theorem finiteType_appTop_of_isAffineOpen_of_smooth_consolidated97 :
    RingHom.FiniteType (CommRingCat.Hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p))) := by
  have : IsAffine V.toScheme := hV
  have hfac : V.toScheme.isoSpec.hom ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p))
        = V.ι ≫ p := by
    rw [Scheme.isoSpec_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  have h3 := congrArg
    (fun f : V.toScheme ⟶ Spec (CommRingCat.of k) => V.toScheme.isoSpec.inv ≫ f) hfac
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at h3
  have h2 : LocallyOfFiniteType
      (Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p))) := by
    rw [h3]
    infer_instance
  exact AlgebraicGeometry.HasRingHomProperty.Spec_iff.mp h2

private theorem isNoetherianRing_sections_of_isAffineOpen_of_smooth_consolidated97 : IsNoetherianRing ↥Γ(V.toScheme, ⊤) := by
  have hft := finiteType_appTop_of_isAffineOpen_of_smooth_consolidated97 p V hV
  let _ : Algebra ↥(CommRingCat.of k) ↥Γ(V.toScheme, ⊤) :=
    (CommRingCat.Hom.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      Scheme.Hom.appTop (V.ι ≫ p))).toAlgebra
  have : Algebra.FiniteType ↥(CommRingCat.of k) ↥Γ(V.toScheme, ⊤) := hft
  have : IsNoetherianRing ↥(CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  exact Algebra.FiniteType.isNoetherianRing ↥(CommRingCat.of k) ↥Γ(V.toScheme, ⊤)


end

section
variable {Y : Scheme.{u}} (R : CommRingCat.{u})

private theorem isDomain_localization_of_iso_spec_consolidated97 (e : Y ≅ Spec R) (y : Y) (hdom : IsDomain ↥(Y.presheaf.stalk y)) :
    IsDomain (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal) := by
  have := hdom
  have hp : (pointOfIsoSpec R e y).asIdeal.IsPrime := (pointOfIsoSpec R e y).isPrime
  have h2 : IsLocalization.AtPrime
      ((Spec.structureSheaf ↥R).presheaf.stalk (pointOfIsoSpec R e y))
      (pointOfIsoSpec R e y).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk ↥R (pointOfIsoSpec R e y)
  have e2 : Localization.AtPrime (pointOfIsoSpec R e y).asIdeal ≃+*
      ((Spec.structureSheaf ↥R).presheaf.stalk (pointOfIsoSpec R e y)) :=
    (IsLocalization.algEquiv (pointOfIsoSpec R e y).asIdeal.primeCompl
      (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal)
      ((Spec.structureSheaf ↥R).presheaf.stalk (pointOfIsoSpec R e y))).toRingEquiv
  have h4 : IsIso (e.hom.stalkMap y) := inferInstance
  have e3 : ((Spec.structureSheaf ↥R).presheaf.stalk (pointOfIsoSpec R e y)) ≃+*
      ↥(Y.presheaf.stalk y) :=
    (asIso (e.hom.stalkMap y)).commRingCatIsoToRingEquiv
  exact (e2.trans e3).toMulEquiv.isDomain _

private theorem exists_isOpen_isIrreducible_of_iso_spec_of_isDomain_stalk_consolidated97 [IsNoetherianRing ↥R] (e : Y ≅ Spec R) (y : Y)
    (hdom : IsDomain ↥(Y.presheaf.stalk y)) :
    ∃ V : Set Y, IsOpen V ∧ IsIrreducible V ∧ y ∈ V := by
  have hPp : (pointOfIsoSpec R e y).asIdeal.IsPrime := (pointOfIsoSpec R e y).isPrime
  have hdomL : IsDomain (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal) :=
    isDomain_localization_of_iso_spec_consolidated97 R e y hdom
  have hbot : (⊥ : Ideal (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal)).IsPrime :=
    Ideal.isPrime_bot
  have hKp : (Ideal.comap
      (algebraMap ↥R (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal))
      (⊥ : Ideal (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal))).IsPrime :=
    Ideal.comap_isPrime _ _
  have hmin : ∀ q : Ideal ↥R, q.IsPrime → q ≤ (pointOfIsoSpec R e y).asIdeal →
      Ideal.comap (algebraMap ↥R (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal))
        (⊥ : Ideal (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal)) ≤ q := by
    intro q hq hqP a ha
    have h0 : algebraMap ↥R (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal) a = 0 := by
      simpa [Ideal.mem_comap, Submodule.mem_bot] using ha
    have h1 : algebraMap ↥R (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal) a
        = algebraMap ↥R (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal) 0 := by
      rw [h0, map_zero]
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists
      (pointOfIsoSpec R e y).asIdeal.primeCompl
      (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal)).mp h1
    rw [mul_zero] at hc
    have hmem : (c : ↥R) * a ∈ q := by
      rw [hc]
      exact q.zero_mem
    rcases hq.mem_or_mem hmem with h | h
    · exact absurd (hqP h) c.2
    · exact h
  obtain ⟨W, hWopen, hWirr, hPW⟩ :=
    exists_isOpen_isIrreducible_of_unique_minimal_prime_le_consolidated97 (pointOfIsoSpec R e y)
      (Ideal.comap (algebraMap ↥R (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal))
        (⊥ : Ideal (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal))) hKp hmin
  refine ⟨(Scheme.homeoOfIso e).symm '' W,
    (Scheme.homeoOfIso e).symm.isOpenMap W hWopen,
    hWirr.image _ (Scheme.homeoOfIso e).symm.continuous.continuousOn,
    ⟨pointOfIsoSpec R e y, hPW, (Scheme.homeoOfIso e).symm_apply_apply y⟩⟩


end

section
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))

private theorem exists_isOpen_isIrreducible_mem_of_smooth_consolidated97 [Smooth p] (x : X) :
    ∃ V : Set X, IsOpen V ∧ IsIrreducible V ∧ x ∈ V := by
  obtain ⟨U, hxU, hU'⟩ := Scheme.exists_isAffineOpen_mem x
  have : IsAffine U.toScheme := hU'
  have hnoeth : IsNoetherianRing ↥Γ(U.toScheme, ⊤) := isNoetherianRing_sections_of_isAffineOpen_of_smooth_consolidated97 p U hU'
  have hdomX : IsDomain ↥(X.presheaf.stalk x) := isDomain_stalk_of_smooth p x
  have hdomU : IsDomain ↥(U.toScheme.presheaf.stalk (⟨x, hxU⟩ : U)) :=
    (U.stalkIso (⟨x, hxU⟩ : U)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  obtain ⟨V, hVopen, hVirr, hyV⟩ :=
    exists_isOpen_isIrreducible_of_iso_spec_of_isDomain_stalk_consolidated97 Γ(U.toScheme, ⊤) U.toScheme.isoSpec
      (⟨x, hxU⟩ : U) hdomU
  have hoe := U.ι.isOpenEmbedding
  exact ⟨U.ι.base '' V, hoe.isOpenMap V hVopen,
    hVirr.image _ hoe.continuous.continuousOn, ⟨(⟨x, hxU⟩ : U), hyV, rfl⟩⟩

theorem isClopen_irreducibleComponent_of_smooth (hp : Smooth p)
    {T : Set ↥X} (hT : T ∈ irreducibleComponents ↥X) : IsClopen T := by
  have := hp
  have hclosed : IsClosed T := isClosed_of_mem_irreducibleComponents _ hT
  have hopen : IsOpen T := by
    rw [isOpen_iff_forall_mem_open]
    intro z hzT
    obtain ⟨W, hWopen, hWirr, hzW⟩ := exists_isOpen_isIrreducible_mem_of_smooth_consolidated97 p z
    refine ⟨W, ?_, hWopen, hzW⟩
    rw [eq_closure_of_mem_irreducibleComponents_consolidated97 hWopen hWirr hT hzW hzT]
    exact subset_closure
  exact ⟨hclosed, hopen⟩


end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsNil
section

open CategoryTheory AlgebraicGeometry

section
namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]

theorem inStrictNormalCrossingPositionAt_nil (x : X) :
    InStrictNormalCrossingPositionAt p ([] : List X.IdealSheafData) x := by
  obtain ⟨U, m, hxU, _, hc⟩ := exists_etaleChart p x
  obtain ⟨c⟩ := hc
  refine ⟨U, hxU, m, c, fun _ => none, ?_, ?_, ?_⟩
  · intro i hi
    simp at hi
  · intro i hi
    simp at hi
  · intro i hi
    simp at hi

theorem inStrictNormalCrossingPosition_nil :
    InStrictNormalCrossingPosition p ([] : List X.IdealSheafData) := by
  rw [inStrictNormalCrossingPosition_iff]
  refine ⟨?_, fun x => inStrictNormalCrossingPositionAt_nil p x⟩
  intro D hD
  simp at hD


end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SubschemeMapFlatness
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

theorem exists_comp_subschemeι_eq_subschemeι_comp {X Y : Scheme.{u}} (g : Y ⟶ X) (Z : X.IdealSheafData) :
    ∃ q : (Z.comap g).subscheme ⟶ Z.subscheme,
      q ≫ Z.subschemeι = (Z.comap g).subschemeι ≫ g := by
  have : IsClosedImmersion (Limits.pullback.fst g Z.subschemeι) := inferInstance
  have hle : Scheme.Hom.ker (Limits.pullback.fst g Z.subschemeι) ≤
      Scheme.Hom.ker (Z.comap g).subschemeι :=
    le_of_eq (Scheme.IdealSheafData.ker_subschemeι (Z.comap g)).symm
  refine ⟨IsClosedImmersion.lift (Limits.pullback.fst g Z.subschemeι)
      (Z.comap g).subschemeι hle ≫ Limits.pullback.snd g Z.subschemeι, ?_⟩
  rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc,
    IsClosedImmersion.lift_fac]

def subschemeMapOfComap {X Y : Scheme.{u}} (g : Y ⟶ X) (Z : X.IdealSheafData) :
    (Z.comap g).subscheme ⟶ Z.subscheme :=
  (exists_comp_subschemeι_eq_subschemeι_comp g Z).choose

@[reassoc]
theorem subschemeMapOfComap_comp {X Y : Scheme.{u}} (g : Y ⟶ X) (Z : X.IdealSheafData) :
    subschemeMapOfComap g Z ≫ Z.subschemeι = (Z.comap g).subschemeι ≫ g :=
  (exists_comp_subschemeι_eq_subschemeι_comp g Z).choose_spec

section
variable {X Y : Scheme.{u}} (g : Y ⟶ X) [Flat g] (Z : X.IdealSheafData)

private theorem flat_of_comp_subschemeι_eq_of_iso_pullback_consolidated95 (e : (Z.comap g).subscheme ≅ Limits.pullback g Z.subschemeι)
    (he : e.hom ≫ Limits.pullback.fst g Z.subschemeι = (Z.comap g).subschemeι)
    (q : (Z.comap g).subscheme ⟶ Z.subscheme)
    (hq : q ≫ Z.subschemeι = (Z.comap g).subschemeι ≫ g) :
    Flat q := by
  have hq' : q = e.hom ≫ Limits.pullback.snd g Z.subschemeι := by
    rw [← cancel_mono Z.subschemeι, hq, Category.assoc, ← Limits.pullback.condition,
      ← Category.assoc, he]
  rw [hq']
  infer_instance

theorem flat_subschemeMapOfComap :
    Flat (subschemeMapOfComap g Z) := by
  refine flat_of_comp_subschemeι_eq_of_iso_pullback_consolidated95 g Z (Scheme.IdealSheafData.comapIso ..) ?_ _
    (subschemeMapOfComap_comp g Z)
  exact Scheme.IdealSheafData.comapIso_hom_fst ..


end

instance instFlatComapSubschemeMap {X Y : Scheme.{u}} (g : Y ⟶ X)
    [Flat g] (Z : X.IdealSheafData) :
    Flat (subschemeMapOfComap g Z) :=
  flat_subschemeMapOfComap g Z

section
variable {X Y : Scheme.{u}} (g : Y ⟶ X)

theorem subschemeMapOfComap_base (Z : X.IdealSheafData)
    (y : (Z.comap g).subscheme) :
    Z.subschemeι.base ((subschemeMapOfComap g Z).base y) =
      g.base ((Z.comap g).subschemeι.base y) := by
  have h := subschemeMapOfComap_comp g Z
  have h2 : (subschemeMapOfComap g Z ≫ Z.subschemeι).base y
      = ((Z.comap g).subschemeι ≫ g).base y := by rw [h]
  simpa using h2

theorem generalizing_subschemeMapOfComap [Flat g] (Z : X.IdealSheafData)
    (y : (Z.comap g).subscheme) (x : Z.subscheme)
    (hx : x ⤳ (subschemeMapOfComap g Z).base y) :
    ∃ y' : (Z.comap g).subscheme, y' ⤳ y ∧ (subschemeMapOfComap g Z).base y' = x := by
  exact AlgebraicGeometry.Flat.generalizingMap (subschemeMapOfComap g Z) hx


end

theorem mem_connectedComponent_of_specializes {α : Type*} [TopologicalSpace α] {x y z : α}
    (hy : y ∈ connectedComponent x) (h : y ⤳ z) : z ∈ connectedComponent x := by
  have hzy : z ∈ closure ({y} : Set α) := specializes_iff_mem_closure.mp h
  have hpc : _root_.IsPreconnected (closure ({y} : Set α)) :=
    (isPreconnected_singleton : _root_.IsPreconnected ({y} : Set α)).closure
  have hsub : closure ({y} : Set α) ⊆ connectedComponent y :=
    hpc.subset_connectedComponent (subset_closure (Set.mem_singleton y))
  have hz : z ∈ connectedComponent y := hsub hzy
  rwa [← connectedComponent_eq hy] at hz

section
variable {X : Scheme.{u}}

private theorem ideal_eq_of_comap_opensι_eq_consolidated95 (I J : X.IdealSheafData)
    (V : X.Opens) (hV : IsAffineOpen V) (hIJ : I.comap V.ι = J.comap V.ι) :
    I.ideal ⟨V, hV⟩ = J.ideal ⟨V, hV⟩ := by
  have : IsAffine V.toScheme := hV
  have main : ∀ W : X.affineOpens, (W : X.Opens) = V → I.ideal W = J.ideal W →
      I.ideal ⟨V, hV⟩ = J.ideal ⟨V, hV⟩ := by
    rintro ⟨W, hWaff⟩ rfl hW
    exact hW
  refine main ⟨V.ι ''ᵁ (⊤ : V.toScheme.Opens),
    (isAffineOpen_top V.toScheme).image_of_isOpenImmersion V.ι⟩
    (Scheme.Opens.ι_image_top V) ?_
  have h3 : (I.comap V.ι).ideal ⟨⊤, isAffineOpen_top _⟩
      = (J.comap V.ι).ideal ⟨⊤, isAffineOpen_top _⟩ := by rw [hIJ]
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at h3
  have hid : (CommRingCat.Hom.hom (Scheme.Hom.appIso V.ι (⊤ : V.toScheme.Opens)).inv).comp
      (CommRingCat.Hom.hom (Scheme.Hom.appIso V.ι (⊤ : V.toScheme.Opens)).hom)
      = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, (Scheme.Hom.appIso V.ι (⊤ : V.toScheme.Opens)).hom_inv_id,
      CommRingCat.hom_id]
  have hsurj : Function.Surjective
      ⇑(CommRingCat.Hom.hom (Scheme.Hom.appIso V.ι (⊤ : V.toScheme.Opens)).inv) := fun y =>
    ⟨CommRingCat.Hom.hom (Scheme.Hom.appIso V.ι (⊤ : V.toScheme.Opens)).hom y,
      DFunLike.congr_fun hid y⟩
  exact Ideal.comap_injective_of_surjective _ hsurj h3

private theorem span_eq_top_of_basicOpen_cover_consolidated95 (W : X.affineOpens)
    (S : Set Γ(X, (W : X.Opens)))
    (hcov : ∀ x ∈ (W : X.Opens), ∃ f ∈ S, x ∈ X.basicOpen f) :
    Ideal.span S = ⊤ := by
  rw [← W.2.iSup_basicOpen_eq_self_iff]
  refine le_antisymm (iSup_le fun f => X.basicOpen_le (f : Γ(X, (W : X.Opens)))) ?_
  rw [SetLike.le_def]
  intro x hx
  obtain ⟨f, hfS, hxf⟩ := hcov x hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hfS⟩, hxf⟩

private theorem exists_pow_mul_mem_of_ideal_basicOpen_eq_consolidated95 (A B : X.IdealSheafData) (W : X.affineOpens)
    (f : Γ(X, (W : X.Opens)))
    (hf : A.ideal (X.affineBasicOpen f) = B.ideal (X.affineBasicOpen f))
    (s : Γ(X, (W : X.Opens))) (hs : s ∈ A.ideal W) :
    ∃ n : ℕ, f ^ n * s ∈ B.ideal W := by
  have := W.2.isLocalization_basicOpen f
  have hA := A.map_ideal_basicOpen W f
  have hB := B.map_ideal_basicOpen W f
  rw [hf, ← hB] at hA
  have halg : (algebraMap Γ(X, (W : X.Opens)) Γ(X, X.basicOpen f))
      = CommRingCat.Hom.hom (X.presheaf.map (homOfLE (X.basicOpen_le f)).op) := rfl
  have hmem : (algebraMap Γ(X, (W : X.Opens)) Γ(X, X.basicOpen f)) s
      ∈ Ideal.map (algebraMap Γ(X, (W : X.Opens)) Γ(X, X.basicOpen f)) (B.ideal W) := by
    rw [halg, ← hA]
    exact Ideal.mem_map_of_mem _ hs
  obtain ⟨⟨y, m⟩, hym⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) Γ(X, X.basicOpen f)).mp hmem
  rw [← map_mul] at hym
  obtain ⟨c, hc⟩ :=
    (IsLocalization.eq_iff_exists (Submonoid.powers f) Γ(X, X.basicOpen f)).mp hym
  obtain ⟨n1, hn1⟩ := (Submonoid.mem_powers_iff (m : Γ(X, (W : X.Opens))) f).mp m.2
  obtain ⟨n2, hn2⟩ := (Submonoid.mem_powers_iff (c : Γ(X, (W : X.Opens))) f).mp c.2
  refine ⟨n2 + n1, ?_⟩
  have hrw : f ^ (n2 + n1) * s
      = (c : Γ(X, (W : X.Opens))) * (s * (m : Γ(X, (W : X.Opens)))) := by
    rw [← hn1, ← hn2]; ring
  rw [hrw, hc]
  exact Ideal.mul_mem_left _ _ y.2

private theorem ideal_le_of_basicOpen_cover_consolidated95 (A B : X.IdealSheafData)
    (W : X.affineOpens)
    (hcov : ∀ x ∈ (W : X.Opens), ∃ f : Γ(X, (W : X.Opens)), x ∈ X.basicOpen f ∧
      A.ideal (X.affineBasicOpen f) = B.ideal (X.affineBasicOpen f)) :
    A.ideal W ≤ B.ideal W := by
  intro s hs
  have hspan : Ideal.span {f : Γ(X, (W : X.Opens)) |
      A.ideal (X.affineBasicOpen f) = B.ideal (X.affineBasicOpen f)} = ⊤ := by
    refine span_eq_top_of_basicOpen_cover_consolidated95 W _ (fun x hx => ?_)
    obtain ⟨f, hxf, hf⟩ := hcov x hx
    exact ⟨f, hf, hxf⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hspan s ?_
  rintro ⟨f, hf⟩
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_of_ideal_basicOpen_eq_consolidated95 A B W f hf s hs
  exact ⟨n, by rwa [smul_eq_mul]⟩

theorem idealSheafData_eq_of_forall_restrictIdeal_eq (I J : X.IdealSheafData)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ restrictIdeal I U = restrictIdeal J U) : I = J := by
  have hloc : ∀ W : X.affineOpens, ∀ x ∈ (W : X.Opens),
      ∃ f : Γ(X, (W : X.Opens)), x ∈ X.basicOpen f ∧
        I.ideal (X.affineBasicOpen f) = J.ideal (X.affineBasicOpen f) := by
    intro W x hx
    obtain ⟨U, hxU, hU⟩ := h x
    have hU' : I.comap U.ι = J.comap U.ι := hU
    obtain ⟨f, hfU, hxf⟩ := W.2.exists_basicOpen_le (⟨x, hxU⟩ : ↥U) hx
    refine ⟨f, hxf, ?_⟩
    have hbo : I.comap (X.basicOpen f).ι = J.comap (X.basicOpen f).ι := by
      rw [← Scheme.homOfLE_ι X hfU, Scheme.IdealSheafData.comap_comp,
        Scheme.IdealSheafData.comap_comp, hU']
    exact ideal_eq_of_comap_opensι_eq_consolidated95 I J (X.basicOpen f) (W.2.basicOpen f) hbo
  refine Scheme.IdealSheafData.ext
    (funext fun W => le_antisymm (ideal_le_of_basicOpen_cover_consolidated95 I J W (hloc W)) ?_)
  refine ideal_le_of_basicOpen_cover_consolidated95 J I W (fun x hx => ?_)
  obtain ⟨f, hxf, hf⟩ := hloc W x hx
  exact ⟨f, hxf, hf.symm⟩


end

section
variable {X Y : Scheme.{u}} (g : Y ⟶ X)

theorem mem_of_subschemeMapOfComap_apply_mem (Z : X.IdealSheafData)
    (A : Set X) (W : Z.subscheme.Opens) (W' : (Z.comap g).subscheme.Opens)
    (hW : (W : Set Z.subscheme) = {w | connectedComponent w ⊆ ⇑Z.subschemeι.base ⁻¹' A})
    (hW' : (W' : Set (Z.comap g).subscheme) =
      {w | connectedComponent w ⊆ ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)})
    (y : (Z.comap g).subscheme) (hy : (subschemeMapOfComap g Z).base y ∈ W) : y ∈ W' := by
  have hcont : Continuous ⇑(subschemeMapOfComap g Z).base :=
    (subschemeMapOfComap g Z).base.hom.continuous
  have hyW : connectedComponent ((subschemeMapOfComap g Z).base y) ⊆ ⇑Z.subschemeι.base ⁻¹' A := by
    have h0 : (subschemeMapOfComap g Z).base y ∈ (W : Set Z.subscheme) := hy
    rw [hW] at h0
    exact h0
  have himg : ⇑(subschemeMapOfComap g Z).base '' connectedComponent y ⊆
      connectedComponent ((subschemeMapOfComap g Z).base y) :=
    IsPreconnected.subset_connectedComponent
      (isPreconnected_connectedComponent.image _ hcont.continuousOn)
      ⟨y, mem_connectedComponent, rfl⟩
  have hmem : y ∈ (W' : Set (Z.comap g).subscheme) := by
    rw [hW']
    intro z hz
    have h1 : (subschemeMapOfComap g Z).base z ∈
        connectedComponent ((subschemeMapOfComap g Z).base y) := himg ⟨z, hz, rfl⟩
    have h2 : Z.subschemeι.base ((subschemeMapOfComap g Z).base z) ∈ A := hyW h1
    rw [subschemeMapOfComap_base g Z z] at h2
    exact h2
  exact hmem

theorem subschemeMapOfComap_apply_mem_of_mem [Flat g] (Z : X.IdealSheafData)
    (A : Set X) (hA : IsClosed A) (W : Z.subscheme.Opens) (W' : (Z.comap g).subscheme.Opens)
    (hW : (W : Set Z.subscheme) = {w | connectedComponent w ⊆ ⇑Z.subschemeι.base ⁻¹' A})
    (hW' : (W' : Set (Z.comap g).subscheme) =
      {w | connectedComponent w ⊆ ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)})
    (hirr : ∀ w : Z.subscheme, IsIrreducible (connectedComponent w))
    (y : (Z.comap g).subscheme) (hy : y ∈ W') : (subschemeMapOfComap g Z).base y ∈ W := by
  have hyset : connectedComponent y ⊆
      ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A) := by
    have h0 : y ∈ (W' : Set (Z.comap g).subscheme) := hy
    rw [hW'] at h0
    exact h0
  have hcont : Continuous ⇑Z.subschemeι.base := Z.subschemeι.base.hom.continuous
  have hmem : (subschemeMapOfComap g Z).base y ∈ (W : Set Z.subscheme) := by
    rw [hW]
    have hC : IsIrreducible (connectedComponent ((subschemeMapOfComap g Z).base y)) :=
      hirr ((subschemeMapOfComap g Z).base y)
    obtain ⟨η, hηmem, hηspec⟩ :
        ∃ η, η ∈ connectedComponent ((subschemeMapOfComap g Z).base y) ∧
          ∀ z ∈ connectedComponent ((subschemeMapOfComap g Z).base y), η ⤳ z :=
      ⟨hC.genericPoint, (hC.isGenericPoint_genericPoint isClosed_connectedComponent).mem,
        fun z hz => (hC.isGenericPoint_genericPoint isClosed_connectedComponent).specializes hz⟩
    have hspec1 : η ⤳ (subschemeMapOfComap g Z).base y := hηspec _ mem_connectedComponent
    obtain ⟨y', hy'spec, hy'eq⟩ := generalizing_subschemeMapOfComap g Z y η hspec1
    have hy'cc : y' ∈ connectedComponent y := by
      have h1 : y ∈ connectedComponent y' :=
        mem_connectedComponent_of_specializes mem_connectedComponent hy'spec
      rw [← connectedComponent_eq h1]
      exact mem_connectedComponent
    have h3 : y' ∈ ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A) := hyset hy'cc
    have h3' : g.base ((Z.comap g).subschemeι.base y') ∈ A := h3
    have h4 : Z.subschemeι.base η ∈ A := by
      rw [← hy'eq, subschemeMapOfComap_base g Z y']
      exact h3'
    intro x hx
    have hx2 : η ⤳ x := hηspec x hx
    have hx3 : Z.subschemeι.base η ⤳ Z.subschemeι.base x := hx2.map hcont
    exact hx3.mem_closed hA h4
  exact hmem

private theorem restrictIdeal_comap_preimage_eq_comap_restrict_consolidated95 (I : X.IdealSheafData) (U : X.Opens) :
    restrictIdeal (I.comap g) (g ⁻¹ᵁ U) = (restrictIdeal I U).comap (g ∣_ U) := by
  rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι]

theorem openSubschemeKer_comap [Flat g]
    (Z : X.IdealSheafData) (A : Set X) (hA : IsClosed A)
    (W : Z.subscheme.Opens) (W' : (Z.comap g).subscheme.Opens)
    (hW : (W : Set Z.subscheme) = {w | connectedComponent w ⊆ ⇑Z.subschemeι.base ⁻¹' A})
    (hW' : (W' : Set (Z.comap g).subscheme) =
      {w | connectedComponent w ⊆ ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)})
    (hWc : IsClosed (W : Set Z.subscheme))
    (hW'c : IsClosed (W' : Set (Z.comap g).subscheme))
    (hirr : ∀ w : Z.subscheme, IsIrreducible (connectedComponent w)) :
    openSubschemeKer (Z.comap g) W' = (openSubschemeKer Z W).comap g := by
  apply idealSheafData_eq_of_forall_restrictIdeal_eq
  intro y
  by_cases hy : g.base y ∈ ⇑Z.subschemeι.base '' (W : Set Z.subscheme)
  · obtain ⟨U, hxU, hUW⟩ := exists_opens_preimage_subschemeι_le Z W (g.base y) hy
    refine ⟨g ⁻¹ᵁ U, hxU, ?_⟩
    have hsub : ((Z.comap g).subschemeι ⁻¹ᵁ (g ⁻¹ᵁ U)) ≤ W' := by
      intro y' hy'
      have h0 : g.base ((Z.comap g).subschemeι.base y') ∈ U := hy'
      have h1 : (subschemeMapOfComap g Z).base y' ∈ (Z.subschemeι ⁻¹ᵁ U) := by
        show Z.subschemeι.base ((subschemeMapOfComap g Z).base y') ∈ U
        rw [subschemeMapOfComap_base g Z y']
        exact h0
      exact mem_of_subschemeMapOfComap_apply_mem g Z A W W' hW hW' y' (hUW h1)
    have e1 : restrictIdeal (openSubschemeKer (Z.comap g) W') (g ⁻¹ᵁ U)
        = restrictIdeal (Z.comap g) (g ⁻¹ᵁ U) :=
      restrictIdeal_openSubschemeKer_of_preimage_le (Z.comap g) W' hW'c (g ⁻¹ᵁ U) hsub
    have e2 : restrictIdeal (openSubschemeKer Z W) U = restrictIdeal Z U :=
      restrictIdeal_openSubschemeKer_of_preimage_le Z W hWc U hUW
    rw [e1, restrictIdeal_comap_preimage_eq_comap_restrict_consolidated95 g Z U,
      restrictIdeal_comap_preimage_eq_comap_restrict_consolidated95 g (openSubschemeKer Z W) U, e2]
  · obtain ⟨U, hxU, hUn⟩ := exists_opens_notMem_image Z W hWc (g.base y) hy
    refine ⟨g ⁻¹ᵁ U, hxU, ?_⟩
    have e1 : restrictIdeal (openSubschemeKer (Z.comap g) W') (g ⁻¹ᵁ U) = ⊤ := by
      refine restrictIdeal_openSubschemeKer_eq_top (Z.comap g) W' hW'c (g ⁻¹ᵁ U) ?_
      intro w' hw'
      have hw : (subschemeMapOfComap g Z).base w' ∈ W :=
        subschemeMapOfComap_apply_mem_of_mem g Z A hA W W' hW hW' hirr w' hw'
      have h2 := hUn _ hw
      rw [subschemeMapOfComap_base g Z w'] at h2
      exact h2
    have e2 : restrictIdeal (openSubschemeKer Z W) U = ⊤ :=
      restrictIdeal_openSubschemeKer_eq_top Z W hWc U hUn
    rw [e1, restrictIdeal_comap_preimage_eq_comap_restrict_consolidated95 g (openSubschemeKer Z W) U, e2]
    simp


end

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinatePolynomialRing
section

namespace FunctorialResolution.EmbeddedResolution

@[reducible] def CoordPolynomialRing (k : Type u) [Field k] (m : ℕ) : Type u :=
  MvPolynomial (ULift.{u} (Fin m)) k

noncomputable def etaleChartCoord (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] (j : Fin m) : S :=
  algebraMap (CoordPolynomialRing k m) S (MvPolynomial.X (ULift.up.{u} j))

section
variable (k : Type u) [Field k] (m : ℕ)

theorem etaleChartCoord_def (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] (j : Fin m) :
    etaleChartCoord k m S j =
      algebraMap (CoordPolynomialRing k m) S (MvPolynomial.X (ULift.up.{u} j)) :=
  rfl

private theorem isRegularLocalRing_localization_coordPolynomialRing_consolidated129 (p : Ideal (CoordPolynomialRing k m)) (hp : p.IsPrime) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  have := hp
  infer_instance


end

private theorem isRegularLocalRing_and_ringKrullDim_eq_of_etale_consolidated129 (P S : Type u) [CommRing P] [CommRing S] [Algebra P S]
    [Algebra.Etale P S] [IsNoetherianRing P]
    (hreg : ∀ (p : Ideal P) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime p))
    (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A] [Algebra S A]
    [IsLocalization q.primeCompl A] :
    IsRegularLocalRing A ∧
      ringKrullDim A = ringKrullDim (Localization.AtPrime (q.comap (algebraMap P S))) := by
  have : Algebra.FiniteType P S := inferInstance
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing P S
  have : IsNoetherianRing A := IsLocalization.isNoetherianRing q.primeCompl A inferInstance
  have : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A q
  let : Algebra P A := ((algebraMap S A).comp (algebraMap P S)).toAlgebra
  have : IsScalarTower P S A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Flat P S := inferInstance
  have : Module.Flat S A := IsLocalization.flat A q.primeCompl
  have : Module.Flat P A := Module.Flat.trans P S A
  have : Algebra.FormallyUnramified P S := inferInstance
  have : Algebra.FormallyUnramified S A :=
    Algebra.FormallyUnramified.of_isLocalization q.primeCompl
  have : Algebra.FormallyUnramified P A := Algebra.FormallyUnramified.comp P S A
  have : Algebra.EssFiniteType P S := inferInstance
  have : Algebra.EssFiniteType S A := Algebra.EssFiniteType.of_isLocalization A q.primeCompl
  have : Algebra.EssFiniteType P A := Algebra.EssFiniteType.comp P S A
  have hunits : ∀ y : (q.comap (algebraMap P S)).primeCompl, IsUnit (algebraMap P A (y : P)) := by
    rintro ⟨y, hy⟩
    have hy' : algebraMap P S y ∈ q.primeCompl := hy
    have h := IsLocalization.map_units A ⟨algebraMap P S y, hy'⟩
    rw [IsScalarTower.algebraMap_apply P S A]
    exact h
  let : Algebra (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    (IsLocalization.lift hunits).toAlgebra
  have : IsScalarTower P (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunits x).symm
  have : Module.Flat (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.comap (algebraMap P S)))
      (q.comap (algebraMap P S)).primeCompl A).mpr ‹_›
  have : Algebra.FormallyUnramified (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    Algebra.FormallyUnramified.localization_base (M := (q.comap (algebraMap P S)).primeCompl)
  have : Algebra.EssFiniteType (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    Algebra.EssFiniteType.of_comp P (Localization.AtPrime (q.comap (algebraMap P S))) A
  have : IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap P S))) :=
    hreg _
  have : IsLocalHom (algebraMap (Localization.AtPrime (q.comap (algebraMap P S))) A) := by
    constructor
    intro r hr
    obtain ⟨⟨x, s⟩, hx⟩ :=
      IsLocalization.surj (M := (q.comap (algebraMap P S)).primeCompl) r
    have hxA : algebraMap (Localization.AtPrime (q.comap (algebraMap P S))) A r
        * algebraMap P A (s : P) = algebraMap P A x := by
      have h := congrArg (algebraMap (Localization.AtPrime (q.comap (algebraMap P S))) A) hx
      rw [map_mul] at h
      rw [IsScalarTower.algebraMap_apply P
            (Localization.AtPrime (q.comap (algebraMap P S))) A (s : P),
        IsScalarTower.algebraMap_apply P
            (Localization.AtPrime (q.comap (algebraMap P S))) A x]
      exact h
    have h2 : IsUnit (algebraMap P A x) := by
      rw [← hxA]
      exact hr.mul (hunits s)
    have h3 : IsUnit (algebraMap S A (algebraMap P S x)) := by
      rw [← IsScalarTower.algebraMap_apply P S A]
      exact h2
    have h4 : algebraMap P S x ∈ q.primeCompl :=
      (IsLocalization.AtPrime.isUnit_to_map_iff A q (algebraMap P S x)).mp h3
    have h5 : x ∈ (q.comap (algebraMap P S)).primeCompl := h4
    have h6 : IsUnit (algebraMap P (Localization.AtPrime (q.comap (algebraMap P S))) x) :=
      IsLocalization.map_units _ ⟨x, h5⟩
    rw [← hx] at h6
    exact (IsUnit.mul_iff.mp h6).1
  exact ⟨isRegularLocalRing_of_flat_formallyUnramified
      (Localization.AtPrime (q.comap (algebraMap P S))) A,
    ringKrullDim_eq_of_flat_formallyUnramified
      (Localization.AtPrime (q.comap (algebraMap P S))) A⟩

section
variable (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime]
include k m

theorem isRegularLocalRing_of_isLocalization_etale (A : Type u) [CommRing A] [Algebra S A]
    [IsLocalization q.primeCompl A] :
    IsRegularLocalRing A :=
  (isRegularLocalRing_and_ringKrullDim_eq_of_etale_consolidated129 (CoordPolynomialRing k m) S
    (by intro p hp; exact isRegularLocalRing_localization_coordPolynomialRing_consolidated129 k m p hp) q A).1

theorem isRegularLocalRing_localization_atPrime_etale :
    IsRegularLocalRing (Localization.AtPrime q) :=
  isRegularLocalRing_of_isLocalization_etale k m S q (Localization.AtPrime q)


end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StalkKrullDimension
section

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private noncomputable def fromSpecStalkPoint (X : Scheme.{u}) (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) : X :=
  (X.fromSpecStalk x).base p

section
variable (X : Scheme.{u}) (x : X)

private theorem fromSpecStalkPoint_specializes_iff_consolidated130 (p q : PrimeSpectrum (X.presheaf.stalk x)) :
    fromSpecStalkPoint X x p ⤳ fromSpecStalkPoint X x q ↔ p ⤳ q :=
  (AlgebraicGeometry.Scheme.Hom.isEmbedding (X.fromSpecStalk x)).toIsInducing.specializes_iff

private theorem exists_fromSpecStalkPoint_eq_of_specializes_consolidated130 {y : X} (h : y ⤳ x) :
    ∃ p : PrimeSpectrum (X.presheaf.stalk x), fromSpecStalkPoint X x p = y := by
  have hy : y ∈ Set.range (X.fromSpecStalk x).base := by
    rw [AlgebraicGeometry.Scheme.range_fromSpecStalk]; exact h
  obtain ⟨p, hp⟩ := hy
  exact ⟨p, hp⟩

theorem ringKrullDim_stalk_le_topologicalKrullDim :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  have hemb : Topology.IsEmbedding (X.fromSpecStalk x).base :=
    AlgebraicGeometry.Scheme.Hom.isEmbedding (X.fromSpecStalk x)
  have h1 : ringKrullDim (X.presheaf.stalk x) ≤
      topologicalKrullDim (PrimeSpectrum (X.presheaf.stalk x)) :=
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).ge
  have h2 : topologicalKrullDim ↥(Spec (X.presheaf.stalk x)) ≤ topologicalKrullDim ↥X :=
    hemb.toIsInducing.topologicalKrullDim_le
  exact le_trans h1 h2


end

private theorem specializes_of_fromSpecStalk_base_specializes_consolidated130 {X : Scheme.{u}} (x : X)
    {a b : PrimeSpectrum (X.presheaf.stalk x)}
    (hab : (X.fromSpecStalk x).base a ⤳ (X.fromSpecStalk x).base b) : a ⤳ b := by
  have hemb : Topology.IsEmbedding (X.fromSpecStalk x).base :=
    AlgebraicGeometry.Scheme.Hom.isEmbedding (X.fromSpecStalk x)
  exact hemb.toIsInducing.specializes_iff.mp hab

theorem topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le (X : Scheme.{u}) (d : WithBot ℕ∞)
    (h : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ d) :
    topologicalKrullDim X ≤ d := by
  unfold topologicalKrullDim
  refine iSup_le fun p => ?_
  have hSM := p.strictMono
  have key : ∀ i : Fin (p.length + 1), ∃ z : X, closure ({z} : Set X) = (p i : Set X) := by
    intro i
    obtain ⟨z, hz⟩ := QuasiSober.sober (p i).isIrreducible' (p i).isClosed'
    exact ⟨z, hz⟩
  choose y hy using key
  have hspec : ∀ i j : Fin (p.length + 1), i ≤ j → y j ⤳ y i := by
    intro i j hij
    have hsub : (p i : Set X) ⊆ (p j : Set X) :=
      SetLike.coe_subset_coe.mpr (hSM.monotone hij)
    have hmem : y i ∈ closure ({y j} : Set X) := by
      rw [hy j]
      apply hsub
      rw [← hy i]
      exact subset_closure rfl
    exact specializes_iff_mem_closure.mpr hmem
  have hinj : Function.Injective y := by
    intro i j hij
    apply hSM.injective
    apply SetLike.coe_injective
    rw [← hy i, ← hy j, hij]
  have hrange : ∀ i : Fin (p.length + 1),
      ∃ z : PrimeSpectrum (X.presheaf.stalk (y 0)), (X.fromSpecStalk (y 0)).base z = y i := by
    intro i
    have hmem : y i ∈ Set.range (X.fromSpecStalk (y 0)).base := by
      rw [Scheme.range_fromSpecStalk]
      exact hspec 0 i (Fin.zero_le i)
    exact hmem
  choose q hq using hrange
  have hg : StrictMono (fun i : Fin (p.length + 1) => q i.rev) := by
    intro i j hij
    have hlt : j.rev < i.rev := Fin.rev_lt_rev.mpr hij
    have hsp : (X.fromSpecStalk (y 0)).base (q i.rev) ⤳ (X.fromSpecStalk (y 0)).base (q j.rev) := by
      rw [hq i.rev, hq j.rev]
      exact hspec j.rev i.rev hlt.le
    have hle : q i.rev ≤ q j.rev :=
      (PrimeSpectrum.le_iff_specializes _ _).mpr
        (specializes_of_fromSpecStalk_base_specializes_consolidated130 (y 0) hsp)
    refine lt_of_le_of_ne hle ?_
    intro hcon
    have hcon' : q i.rev = q j.rev := hcon
    have hyy : y i.rev = y j.rev :=
      (hq i.rev).symm.trans
        ((congrArg (fun z : PrimeSpectrum (X.presheaf.stalk (y 0)) =>
          (X.fromSpecStalk (y 0)).base z) hcon').trans (hq j.rev))
    have h4 := congrArg Fin.rev (hinj hyy)
    rw [Fin.rev_rev, Fin.rev_rev] at h4
    exact absurd h4 (ne_of_lt hij)
  have hlen : (p.length : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk (y 0)) :=
    le_iSup (fun t : LTSeries (PrimeSpectrum (X.presheaf.stalk (y 0))) => (t.length : WithBot ℕ∞))
      ⟨p.length, fun i => q i.rev, fun i => hg Fin.castSucc_lt_succ⟩
  exact le_trans hlen (h (y 0))

section
variable {Y W : Scheme.{u}} (f : Y ⟶ W) [Etale f] (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)] [_root_.IsRegularLocalRing (W.presheaf.stalk (f.base y))]

theorem ringKrullDim_stalk_le_of_etale :
    ringKrullDim (Y.presheaf.stalk y) ≤ ringKrullDim (W.presheaf.stalk (f.base y)) := by
  have hft : (f.stalkMap y).hom.EssFiniteType :=
    AlgebraicGeometry.LocallyOfFiniteType.stalkMap f y
  have hfu : (f.stalkMap y).hom.FormallyUnramified :=
    AlgebraicGeometry.FormallyUnramified.stalkMap f y
  let algStalk : Algebra (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
    (f.stalkMap y).hom.toAlgebra
  have : IsLocalHom (algebraMap (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
  have : Module.Flat (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
    AlgebraicGeometry.Flat.stalkMap f y
  have : Algebra.EssFiniteType (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := hft
  have : Algebra.FormallyUnramified (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := hfu
  exact le_of_eq (FunctorialResolution.EmbeddedResolution.ringKrullDim_eq_of_flat_formallyUnramified
    (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y))

theorem ringKrullDim_stalk_eq_of_etale :
    ringKrullDim (Y.presheaf.stalk y) = ringKrullDim (W.presheaf.stalk (f.base y)) := by
  have hft : (f.stalkMap y).hom.EssFiniteType :=
    AlgebraicGeometry.LocallyOfFiniteType.stalkMap f y
  have hfu : (f.stalkMap y).hom.FormallyUnramified :=
    AlgebraicGeometry.FormallyUnramified.stalkMap f y
  let algStalk : Algebra (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
    (f.stalkMap y).hom.toAlgebra
  have : IsLocalHom (algebraMap (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
  have : Module.Flat (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
    AlgebraicGeometry.Flat.stalkMap f y
  have : Algebra.EssFiniteType (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := hft
  have : Algebra.FormallyUnramified (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := hfu
  exact FunctorialResolution.EmbeddedResolution.ringKrullDim_eq_of_flat_formallyUnramified
    (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)


end

private theorem exists_isClosed_singleton_of_isAffine_consolidated130 (A : Scheme.{u}) [IsAffine A] (a : A) :
    ∃ x : A, IsClosed ({x} : Set A) := by
  have h : ↥A ≃ₜ PrimeSpectrum ↥Γ(A, ⊤) := Scheme.homeoOfIso A.isoSpec
  have hp : PrimeSpectrum ↥Γ(A, ⊤) := h a
  obtain ⟨M, hM, -⟩ := Ideal.exists_le_maximal hp.asIdeal hp.isPrime.ne_top
  refine ⟨h.symm ⟨M, hM.isPrime⟩, ?_⟩
  have hq : IsClosed ({(⟨M, hM.isPrime⟩ : PrimeSpectrum ↥Γ(A, ⊤))} :
      Set (PrimeSpectrum ↥Γ(A, ⊤))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hM
  have h2 := h.symm.isClosedMap _ hq
  rwa [Set.image_singleton] at h2

section
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty)
include hU hne

theorem exists_isClosed_singleton_of_isAffineOpen :
    ∃ x : U.toScheme, IsClosed ({x} : Set U.toScheme) := by
  have : IsAffine U.toScheme := hU
  obtain ⟨x0, hx0⟩ := hne
  exact exists_isClosed_singleton_of_isAffine_consolidated130 U.toScheme ⟨x0, hx0⟩

theorem exists_mem_isClosed_singleton_of_isAffineOpen :
    ∃ x : X, ∃ hx : x ∈ U, IsClosed ({(⟨x, hx⟩ : U.toScheme)} : Set U.toScheme) := by
  obtain ⟨x, hx⟩ := exists_isClosed_singleton_of_isAffineOpen U hU hne
  obtain ⟨y, hy⟩ := x
  exact ⟨y, hy, hx⟩


end

private theorem topologicalKrullDim_spec_le_ringKrullDim_consolidated130 (R : CommRingCat.{u}) :
    topologicalKrullDim ↥(Spec R) ≤ ringKrullDim ↥R := by
  have h : topologicalKrullDim (PrimeSpectrum ↥R) = ringKrullDim ↥R :=
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim ↥R
  exact le_of_eq h

section
variable (k : Type u) [Field k] (m : ℕ)

private theorem topologicalKrullDim_affineSpace_le_ringKrullDim_consolidated130 :
    topologicalKrullDim ↥(AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))) ≤
      ringKrullDim (MvPolynomial (ULift.{u} (Fin m)) k) := by
  let e := Scheme.homeoOfIso (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k))
  have h3 := (Homeomorph.isEmbedding e).toIsInducing.topologicalKrullDim_le
  exact h3.trans
    (topologicalKrullDim_spec_le_ringKrullDim_consolidated130
      (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k)))

private theorem ringKrullDim_mvPolynomial_uLift_le_consolidated130 :
    ringKrullDim (MvPolynomial (ULift.{u} (Fin m)) k) ≤ ((m : ℕ∞) : WithBot ℕ∞) := by
  have he : ringKrullDim (MvPolynomial (ULift.{u} (Fin m)) k)
      = ringKrullDim (MvPolynomial (Fin m) k) :=
    ringKrullDim_eq_of_ringEquiv
      (MvPolynomial.renameEquiv k (Equiv.ulift : ULift.{u} (Fin m) ≃ Fin m)).toRingEquiv
  rw [he]
  simp


end

theorem ringKrullDim_stalk_le_of_etale_affineSpace {k : Type u} [Field k] {m : ℕ} {Y : Scheme.{u}}
    (c : Y ⟶ AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k)))
    [Etale c] (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)] :
    ringKrullDim (Y.presheaf.stalk y) ≤ ((m : ℕ∞) : WithBot ℕ∞) := by
  have hreg : _root_.IsRegularLocalRing
      ((AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))).presheaf.stalk (c.base y)) :=
    isRegularLocalRing_stalk_affineSpace k (ULift.{u} (Fin m)) (c.base y)
  have h1 : ringKrullDim (Y.presheaf.stalk y) ≤
      ringKrullDim ((AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))).presheaf.stalk
        (c.base y)) := ringKrullDim_stalk_le_of_etale c y
  have h2 := ringKrullDim_stalk_le_topologicalKrullDim
      (AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))) (c.base y)
  exact h1.trans (h2.trans ((topologicalKrullDim_affineSpace_le_ringKrullDim_consolidated130 k m).trans
    (ringKrullDim_mvPolynomial_uLift_le_consolidated130 k m)))

section
variable {A B : Type u} [CommRing A] [CommRing B] (φ : A ≃+* B)

private theorem comap_comap_symm_consolidated130 (I : Ideal A) : Ideal.comap (φ : A →+* B) (Ideal.comap (φ.symm : B →+* A) I) = I := by
  refine Ideal.ext fun a => ?_
  have h : (φ.symm : B →+* A) ((φ : A →+* B) a) = a := φ.symm_apply_apply a
  constructor
  · intro hmem
    have hmem' : (φ.symm : B →+* A) ((φ : A →+* B) a) ∈ I := hmem
    rwa [h] at hmem'
  · intro hmem
    show (φ.symm : B →+* A) ((φ : A →+* B) a) ∈ I
    rw [h]
    exact hmem

private theorem comap_symm_comap_consolidated130 (J : Ideal B) : Ideal.comap (φ.symm : B →+* A) (Ideal.comap (φ : A →+* B) J) = J := by
  refine Ideal.ext fun b => ?_
  have h : (φ : A →+* B) ((φ.symm : B →+* A) b) = b := φ.apply_symm_apply b
  constructor
  · intro hmem
    have hmem' : (φ : A →+* B) ((φ.symm : B →+* A) b) ∈ J := hmem
    rwa [h] at hmem'
  · intro hmem
    show (φ : A →+* B) ((φ.symm : B →+* A) b) ∈ J
    rw [h]
    exact hmem

private theorem exists_ltSeries_comap_consolidated130 (s : LTSeries (PrimeSpectrum B)) :
    ∃ t : LTSeries (PrimeSpectrum A), t.length = s.length ∧
      t.last.asIdeal = Ideal.comap (φ : A →+* B) s.last.asIdeal := by
  have hmono : Monotone (PrimeSpectrum.comap (φ : A →+* B)) := by
    intro p q h
    rw [← PrimeSpectrum.asIdeal_le_asIdeal, PrimeSpectrum.comap_asIdeal,
      PrimeSpectrum.comap_asIdeal]
    exact Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal p q).mpr h)
  have hinj : Function.Injective (PrimeSpectrum.comap (φ : A →+* B)) := by
    intro p q h
    have h' : Ideal.comap (φ : A →+* B) p.asIdeal = Ideal.comap (φ : A →+* B) q.asIdeal := by
      rw [← PrimeSpectrum.comap_asIdeal, ← PrimeSpectrum.comap_asIdeal, h]
    have h2 := congrArg (Ideal.comap (φ.symm : B →+* A)) h'
    rw [comap_symm_comap_consolidated130 φ p.asIdeal, comap_symm_comap_consolidated130 φ q.asIdeal] at h2
    exact PrimeSpectrum.ext h2
  have hstrict := hmono.strictMono_of_injective hinj
  exact ⟨⟨s.length, fun i => PrimeSpectrum.comap (φ : A →+* B) (s i), fun i => hstrict (s.step i)⟩,
    rfl, rfl⟩


end

section
variable {S : Type u} [CommRing S]

private theorem comap_C_map_C_consolidated130 (I : Ideal S) :
    Ideal.comap (Polynomial.C : S →+* Polynomial S) (I.map (Polynomial.C : S →+* Polynomial S))
      = I := by
  refine Ideal.ext fun a => ?_
  constructor
  · intro h
    have h2 : (Polynomial.C a) ∈ I.map (Polynomial.C : S →+* Polynomial S) := h
    have h3 := (Ideal.mem_map_C_iff).mp h2 0
    simpa using h3
  · intro h
    exact Ideal.mem_map_of_mem _ h

private theorem isMaximal_comap_C_consolidated130 [IsJacobsonRing S]
    (M' : Ideal (Polynomial S)) (hM' : M'.IsMaximal) :
    (Ideal.comap (Polynomial.C : S →+* Polynomial S) M').IsMaximal := by
  have := hM'
  have hint : ((Ideal.Quotient.mk M').comp (Polynomial.C : S →+* Polynomial S)).IsIntegral :=
    Polynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing M'
  have hbot : (⊥ : Ideal (Polynomial S ⧸ M')).IsMaximal := by
    let fieldQuot : Field (Polynomial S ⧸ M') := Ideal.Quotient.field M'
    exact Ideal.bot_isMaximal
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
    ((Ideal.Quotient.mk M').comp (Polynomial.C : S →+* Polynomial S)) hint
    (⊥ : Ideal (Polynomial S ⧸ M'))
  have hker : Ideal.comap ((Ideal.Quotient.mk M').comp (Polynomial.C : S →+* Polynomial S))
      (⊥ : Ideal (Polynomial S ⧸ M')) = Ideal.comap (Polynomial.C : S →+* Polynomial S) M' := by
    refine Ideal.ext fun a => ?_
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_bot, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
  rw [← hker]
  exact hmax

private theorem map_C_ne_of_isMaximal_consolidated130 (N : Ideal S) (hN : N.IsMaximal)
    (M' : Ideal (Polynomial S)) (hM' : M'.IsMaximal) :
    N.map (Polynomial.C : S →+* Polynomial S) ≠ M' := by
  intro h
  have hX : (Polynomial.X : Polynomial S) ∉ M' := by
    rw [← h]
    intro hmem
    have h1 := (Ideal.mem_map_C_iff).mp hmem 1
    rw [Polynomial.coeff_X_one] at h1
    exact hN.ne_top ((Ideal.eq_top_iff_one N).mpr h1)
  obtain ⟨y, i, hi, hyi⟩ := hM'.exists_inv hX
  rw [← h] at hi
  have hc := (Ideal.mem_map_C_iff).mp hi 0
  have h0 : (y * Polynomial.X + i).coeff 0 = (1 : Polynomial S).coeff 0 := by rw [hyi]
  rw [Polynomial.coeff_add, Polynomial.coeff_one_zero, Polynomial.mul_coeff_zero,
    Polynomial.coeff_X_zero, mul_zero, zero_add] at h0
  have hone : (1 : S) ∈ N := by rw [← h0]; exact hc
  exact hN.ne_top ((Ideal.eq_top_iff_one N).mpr hone)


end

section
variable (k : Type u) [Field k]

private theorem exists_ltSeries_of_isMaximal_mvPolynomial_consolidated130 :
    ∀ (m : ℕ) (M : Ideal (MvPolynomial (Fin m) k)), M.IsMaximal →
      ∃ s : LTSeries (PrimeSpectrum (MvPolynomial (Fin m) k)),
        s.length = m ∧ s.last.asIdeal = M := by
  intro m
  induction m with
  | zero =>
    intro M hM
    exact ⟨RelSeries.singleton _ ⟨M, hM.isPrime⟩, rfl, rfl⟩
  | succ n ih =>
    intro M hM
    have := hM
    have hJ : IsJacobsonRing (MvPolynomial (Fin n) k) := by
      have : Algebra.FiniteType k (MvPolynomial (Fin n) k) := inferInstance
      exact isJacobsonRing_of_finiteType (A := k)
    let φ : MvPolynomial (Fin (n + 1)) k ≃+* Polynomial (MvPolynomial (Fin n) k) :=
      (MvPolynomial.finSuccEquiv k n).toRingEquiv
    let M' : Ideal (Polynomial (MvPolynomial (Fin n) k)) :=
      Ideal.comap
        (φ.symm : Polynomial (MvPolynomial (Fin n) k) →+* MvPolynomial (Fin (n + 1)) k) M
    have hM'max : M'.IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ (RingEquiv.surjective φ.symm)
    let N : Ideal (MvPolynomial (Fin n) k) :=
      Ideal.comap
        (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k)) M'
    have hNmax : N.IsMaximal := isMaximal_comap_C_consolidated130 M' hM'max
    obtain ⟨t, htlen, htlast⟩ := ih N hNmax
    have hFs : StrictMono (fun p : PrimeSpectrum (MvPolynomial (Fin n) k) =>
        (⟨p.asIdeal.map
            (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k)),
          (Ideal.isPrime_map_C_iff_isPrime p.asIdeal).mpr p.isPrime⟩ :
          PrimeSpectrum (Polynomial (MvPolynomial (Fin n) k)))) := by
      refine Monotone.strictMono_of_injective ?_ ?_
      · intro p q hpq
        rw [← PrimeSpectrum.asIdeal_le_asIdeal]
        exact Ideal.map_mono ((PrimeSpectrum.asIdeal_le_asIdeal p q).mpr hpq)
      · intro p q hpq
        have h' : p.asIdeal.map
              (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k))
            = q.asIdeal.map
              (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k)) :=
          congrArg PrimeSpectrum.asIdeal hpq
        refine PrimeSpectrum.ext ?_
        rw [← comap_C_map_C_consolidated130 p.asIdeal, ← comap_C_map_C_consolidated130 q.asIdeal, h']
    let t1 : LTSeries (PrimeSpectrum (Polynomial (MvPolynomial (Fin n) k))) :=
      ⟨t.length, fun i => ⟨(t i).asIdeal.map
          (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k)),
        (Ideal.isPrime_map_C_iff_isPrime (t i).asIdeal).mpr (t i).isPrime⟩,
        fun i => hFs (t.step i)⟩
    have ht1last : t1.last.asIdeal = N.map
        (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k)) := by
      show (t.last).asIdeal.map
          (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k)) = _
      rw [htlast]
    have hle : t1.last.asIdeal ≤ M' := by
      rw [ht1last]
      exact Ideal.map_le_iff_le_comap.mpr le_rfl
    have hlt : t1.last <
        (⟨M', hM'max.isPrime⟩ : PrimeSpectrum (Polynomial (MvPolynomial (Fin n) k))) := by
      refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hle) ?_
      intro hEq
      have hEq' : t1.last.asIdeal = M' := congrArg PrimeSpectrum.asIdeal hEq
      rw [ht1last] at hEq'
      exact map_C_ne_of_isMaximal_consolidated130 N hNmax M' hM'max hEq'
    obtain ⟨s, hslen, hslast⟩ := exists_ltSeries_comap_consolidated130 φ (t1.snoc _ hlt)
    refine ⟨s, ?_, ?_⟩
    · rw [hslen]
      show t.length + 1 = n + 1
      rw [htlen]
    · rw [hslast, RelSeries.last_snoc]
      exact comap_comap_symm_consolidated130 φ M

private theorem exists_ltSeries_of_isMaximal_mvPolynomial_uLift_consolidated130 (m : ℕ)
    (M : Ideal (MvPolynomial (ULift.{u} (Fin m)) k)) (hM : M.IsMaximal) :
    ∃ s : LTSeries (PrimeSpectrum (MvPolynomial (ULift.{u} (Fin m)) k)),
      s.length = m ∧ s.last.asIdeal = M := by
  have := hM
  let φ : MvPolynomial (ULift.{u} (Fin m)) k ≃+* MvPolynomial (Fin m) k :=
    (MvPolynomial.renameEquiv k (Equiv.ulift : ULift.{u} (Fin m) ≃ Fin m)).toRingEquiv
  have hmax :
      (Ideal.comap (φ.symm : MvPolynomial (Fin m) k →+* MvPolynomial (ULift.{u} (Fin m)) k)
        M).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ (RingEquiv.surjective φ.symm)
  obtain ⟨t, htlen, htlast⟩ := exists_ltSeries_of_isMaximal_mvPolynomial_consolidated130 k m _ hmax
  obtain ⟨s, hslen, hslast⟩ := exists_ltSeries_comap_consolidated130 φ t
  refine ⟨s, by rw [hslen, htlen], ?_⟩
  rw [hslast, htlast]
  exact comap_comap_symm_consolidated130 φ M


end

private theorem le_ringKrullDim_stalk_of_chain_consolidated130 (X : Scheme.{u}) (x : X) (n : ℕ)
    (z : Fin (n + 1) → X) (hspec : ∀ i, z i ⤳ x)
    (hmono : ∀ i j : Fin (n + 1), i < j → z i ⤳ z j) (hinj : Function.Injective z) :
    ((n : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
  choose q hq using fun i => exists_fromSpecStalkPoint_eq_of_specializes_consolidated130 X x (hspec i)
  have hstep : ∀ i : Fin n, q i.castSucc < q i.succ := by
    intro i
    have h1 : fromSpecStalkPoint X x (q i.castSucc) ⤳ fromSpecStalkPoint X x (q i.succ) := by
      rw [hq i.castSucc, hq i.succ]
      exact hmono _ _ Fin.castSucc_lt_succ
    have hle : q i.castSucc ≤ q i.succ :=
      (PrimeSpectrum.le_iff_specializes _ _).mpr
        ((fromSpecStalkPoint_specializes_iff_consolidated130 X x _ _).mp h1)
    refine lt_of_le_of_ne hle ?_
    intro hEq
    have hz : z i.castSucc = z i.succ := by
      rw [← hq i.castSucc, ← hq i.succ, hEq]
    exact absurd (hinj hz) Fin.castSucc_lt_succ.ne
  have hlen : ((n : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) :=
    le_iSup (fun t : LTSeries (PrimeSpectrum (X.presheaf.stalk x)) => (t.length : WithBot ℕ∞))
      ⟨n, q, hstep⟩
  have hcast : ((n : ℕ∞) : WithBot ℕ∞) = ((n : ℕ) : WithBot ℕ∞) := by norm_cast
  rw [hcast]
  exact hlen

private theorem le_ringKrullDim_stalk_affineSpace_consolidated130 (k : Type u) [Field k] (m : ℕ)
    (x : ↥(AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))))
    (hx : IsClosed ({x} : Set ↥(AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))))) :
    ((m : ℕ∞) : WithBot ℕ∞) ≤
      ringKrullDim
        ((AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))).presheaf.stalk x) := by
  let e : ↥(AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))) ≃ₜ
      PrimeSpectrum (MvPolynomial (ULift.{u} (Fin m)) k) :=
    Scheme.homeoOfIso (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k))
  have hclosed : IsClosed ({e x} : Set (PrimeSpectrum (MvPolynomial (ULift.{u} (Fin m)) k))) := by
    have h2 := e.isClosedMap _ hx
    rwa [Set.image_singleton] at h2
  have hmax : (e x).asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal (e x)).mp hclosed
  obtain ⟨s, hslen, hslast⟩ := exists_ltSeries_of_isMaximal_mvPolynomial_uLift_consolidated130 k m (e x).asIdeal
    hmax
  have hlast : s.last = e x := PrimeSpectrum.ext hslast
  have hspec : ∀ i, (fun j => e.symm (s j)) i ⤳ x := by
    intro i
    have h1 : s i ≤ s.last := s.strictMono.monotone (Fin.le_last i)
    have h2 : (s i) ⤳ s.last := (PrimeSpectrum.le_iff_specializes _ _).mp h1
    have h3 := h2.map e.symm.continuous
    rw [hlast, e.symm_apply_apply] at h3
    exact h3
  have hmono : ∀ i j, i < j → (fun l => e.symm (s l)) i ⤳ (fun l => e.symm (s l)) j := by
    intro i j hij
    have h1 : s i < s j := s.strictMono hij
    exact ((PrimeSpectrum.le_iff_specializes _ _).mp h1.le).map e.symm.continuous
  have hinj : Function.Injective (fun i => e.symm (s i)) := by
    intro i j hij
    exact s.strictMono.injective (e.symm.injective hij)
  have key := le_ringKrullDim_stalk_of_chain_consolidated130
    (AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))) x s.length
    (fun i => e.symm (s i)) hspec hmono hinj
  rw [hslen] at key
  exact key

theorem ringKrullDim_stalk_eq_of_etale_affineSpace {k : Type u} [Field k] {m : ℕ} {Y : Scheme.{u}}
    (c : Y ⟶ AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k)))
    [Etale c] (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)]
    (hy : IsClosed ({y} : Set Y)) :
    ringKrullDim (Y.presheaf.stalk y) = ((m : ℕ∞) : WithBot ℕ∞) := by
  have hreg : _root_.IsRegularLocalRing
      ((AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))).presheaf.stalk (c.base y)) :=
    isRegularLocalRing_stalk_affineSpace k (ULift.{u} (Fin m)) (c.base y)
  refine le_antisymm (ringKrullDim_stalk_le_of_etale_affineSpace c y) ?_
  have heq := ringKrullDim_stalk_eq_of_etale c y
  rw [heq]
  exact le_ringKrullDim_stalk_affineSpace_consolidated130 k m (c.base y)
    (AlgebraicGeometry.Scheme.Hom.closePoints_subset_preimage_closedPoints c hy)

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.CartierDivisorComponents
section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

private theorem mem_closure_singleton_iff_fromSpec_consolidated37 (a b : PrimeSpectrum Γ(X, U)) :
    a ∈ closure ({b} : Set (PrimeSpectrum Γ(X, U))) ↔
      hU.fromSpec a ∈ closure ({hU.fromSpec b} : Set (X : Type u)) := by
  have hoi : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have hind := (Scheme.Hom.isOpenEmbedding hU.fromSpec).toIsEmbedding.toIsInducing
  constructor
  · intro hab
    have h1 : b ⤳ a := specializes_iff_mem_closure.mpr hab
    exact specializes_iff_mem_closure.mp (hind.specializes_iff.mpr h1)
  · intro hab
    have h1 : hU.fromSpec b ⤳ hU.fromSpec a := specializes_iff_mem_closure.mpr hab
    exact specializes_iff_mem_closure.mp (hind.specializes_iff.mp h1)

private theorem mem_primeIdealOf_of_notMem_basicOpen_consolidated37 {x : (X : Type u)} (hx : x ∈ U) {f : Γ(X, U)}
    (hb : x ∉ X.basicOpen f) : f ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  by_contra hfn
  apply hb
  have h1 : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
    rw [hU.fromSpec_preimage_basicOpen f]
    exact (PrimeSpectrum.mem_basicOpen f _).mpr hfn
  have h2 : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f := h1
  rw [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h2
  exact h2


end

section
variable {X : Scheme.{u}}

private theorem mem_primeIdealOf_of_mem_support_consolidated37 {I : X.IdealSheafData}
    {U : X.affineOpens} {x : (X : Type u)} (hx : x ∈ U.1) {f : Γ(X, U.1)}
    (hf : f ∈ I.ideal U) (hxs : x ∈ I.support) :
    f ∈ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have hz : x ∈ X.zeroLocus (I.ideal U : Set Γ(X, U.1)) :=
    (Scheme.IdealSheafData.mem_support_iff_of_mem hx).mp hxs
  rw [Scheme.mem_zeroLocus_iff] at hz
  exact mem_primeIdealOf_of_notMem_basicOpen_consolidated37 U.2 hx (hz f hf)

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.not_irreducibleComponent_subset_support
    {D : X.IdealSheafData} (hD : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor D)
    {Z : Set (X : Type u)} (hZ : Z ∈ irreducibleComponents (X : Type u)) :
    ¬ Z ⊆ (D.support : Set (X : Type u)) := by
  intro hsub
  have hZcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hZ.1 hZcl
  have hξ' : closure ({ξ} : Set (X : Type u)) = Z := hξ
  have hξZ : ξ ∈ Z := by rw [← hξ']; exact subset_closure rfl
  obtain ⟨U, f, hxU, hf, hDU⟩ := hD ξ
  have hfD : f ∈ D.ideal U := by rw [hDU]; exact Ideal.subset_span rfl
  have hfp : f ∈ (U.2.primeIdealOf ⟨ξ, hxU⟩).asIdeal :=
    EmbeddedResolution.mem_primeIdealOf_of_mem_support_consolidated37 hxU hfD (hsub hξZ)
  have hmin : (U.2.primeIdealOf ⟨ξ, hxU⟩).asIdeal ∈ minimalPrimes Γ(X, U.1) := by
    refine ⟨⟨(U.2.primeIdealOf ⟨ξ, hxU⟩).isPrime, bot_le⟩, ?_⟩
    rintro q ⟨hq, -⟩ hqle
    have hqle' : (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ≤ U.2.primeIdealOf ⟨ξ, hxU⟩ := hqle
    have hxy : (U.2.primeIdealOf ⟨ξ, hxU⟩) ∈
        closure ({(⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))} : Set (PrimeSpectrum Γ(X, U.1))) :=
      (PrimeSpectrum.le_iff_mem_closure ⟨q, hq⟩ (U.2.primeIdealOf ⟨ξ, hxU⟩)).mp hqle'
    have hξcl : ξ ∈ closure ({U.2.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))}
        : Set (X : Type u)) := by
      have h2 := (_root_.FunctorialResolution.EmbeddedResolution.mem_closure_singleton_iff_fromSpec_consolidated37 U.2 (U.2.primeIdealOf ⟨ξ, hxU⟩) ⟨q, hq⟩).mp hxy
      rw [U.2.fromSpec_primeIdealOf ⟨ξ, hxU⟩] at h2
      exact h2
    have hZsub : Z ⊆ closure ({U.2.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))}
        : Set (X : Type u)) := by
      rw [← hξ']
      exact closure_minimal (Set.singleton_subset_iff.mpr hξcl) isClosed_closure
    have hyZ : U.2.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ∈ Z :=
      hZ.2 isIrreducible_singleton.closure hZsub (subset_closure rfl)
    have hy : U.2.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))
        ∈ closure ({ξ} : Set (X : Type u)) := by
      rw [hξ']; exact hyZ
    have hprimeLe : (U.2.primeIdealOf ⟨ξ, hxU⟩) ≤ (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) := by
      refine (PrimeSpectrum.le_iff_mem_closure (U.2.primeIdealOf ⟨ξ, hxU⟩) ⟨q, hq⟩).mpr ?_
      refine (_root_.FunctorialResolution.EmbeddedResolution.mem_closure_singleton_iff_fromSpec_consolidated37 U.2 ⟨q, hq⟩ (U.2.primeIdealOf ⟨ξ, hxU⟩)).mpr ?_
      rw [U.2.fromSpec_primeIdealOf ⟨ξ, hxU⟩]
      exact hy
    exact hprimeLe
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hfp hmin hf


end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivationOfSurjective
section
namespace FunctorialResolution.EmbeddedResolution

variable {k S T : Type*} [CommRing k] [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T]

theorem map_derivation_eq_of_map_eq (f : S →ₐ[k] T) (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom)
    {s s' : S} (h : f s = f s') : f (D s) = f (D s') := by
  have hker : s - s' ∈ RingHom.ker f.toRingHom := by
    simp [RingHom.mem_ker, h]
  have hD' := hD _ hker
  rw [RingHom.mem_ker, map_sub D s s'] at hD'
  have h2 : f (D s) - f (D s') = 0 := by
    rw [← map_sub f (D s) (D s')]
    exact hD'
  exact eq_of_sub_eq_zero h2

noncomputable def derivationOfSurjectiveFun (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S) : T → T :=
  fun t => f (D (Function.surjInv hf t))

section
variable (f : S →ₐ[k] T) (hf : Function.Surjective f) (D : Derivation k S S) (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom)
include hD

theorem derivationOfSurjectiveFun_apply (s : S) :
    derivationOfSurjectiveFun f hf D (f s) = f (D s) := by
  have h : f (Function.surjInv hf (f s)) = f s := Function.surjInv_eq hf (f s)
  exact map_derivation_eq_of_map_eq f D hD h

theorem derivationOfSurjectiveFun_add :
    ∀ t t' : T, derivationOfSurjectiveFun f hf D (t + t')
      = derivationOfSurjectiveFun f hf D t + derivationOfSurjectiveFun f hf D t' := by
  intro t t'
  obtain ⟨a, rfl⟩ := hf t
  obtain ⟨b, rfl⟩ := hf t'
  rw [← map_add f a b]
  simp only [derivationOfSurjectiveFun_apply f hf D hD]
  rw [map_add D a b, map_add f (D a) (D b)]

theorem derivationOfSurjectiveFun_smul :
    ∀ (c : k) (t : T), derivationOfSurjectiveFun f hf D (c • t) = c • derivationOfSurjectiveFun f hf D t := by
  intro c t
  obtain ⟨a, rfl⟩ := hf t
  have h1 : f (c • a) = c • f a := map_smul f c a
  have h2 : D (c • a) = c • D a := by
    simp
  have h3 : f (c • D a) = c • f (D a) := map_smul f c (D a)
  rw [← h1]
  simp only [derivationOfSurjectiveFun_apply f hf D hD]
  rw [h2]
  exact h3


end

noncomputable def derivationOfSurjectiveLinearMap (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) : T →ₗ[k] T where
  toFun := derivationOfSurjectiveFun f hf D
  map_add' := derivationOfSurjectiveFun_add f hf D hD
  map_smul' := derivationOfSurjectiveFun_smul f hf D hD

section
variable (f : S →ₐ[k] T) (hf : Function.Surjective f) (D : Derivation k S S) (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom)
include hD

theorem derivationOfSurjectiveFun_one :
    derivationOfSurjectiveFun f hf D 1 = 0 := by
  have h : (1 : T) = f 1 := (map_one f).symm
  rw [h]
  rw [derivationOfSurjectiveFun_apply f hf D hD, D.map_one_eq_zero, map_zero]

theorem derivationOfSurjectiveFun_mul :
    ∀ a b : T, derivationOfSurjectiveFun f hf D (a * b)
      = a • derivationOfSurjectiveFun f hf D b + b • derivationOfSurjectiveFun f hf D a := by
  intro a b
  obtain ⟨x, rfl⟩ := hf a
  obtain ⟨y, rfl⟩ := hf b
  rw [← map_mul f x y]
  simp only [derivationOfSurjectiveFun_apply f hf D hD]
  rw [D.leibniz]
  simp [smul_eq_mul]


end

noncomputable def derivationOfSurjective (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) :
    Derivation k T T where
  toLinearMap := derivationOfSurjectiveLinearMap f hf D hD
  map_one_eq_zero' := derivationOfSurjectiveFun_one f hf D hD
  leibniz' := derivationOfSurjectiveFun_mul f hf D hD

@[simp]
theorem derivationOfSurjective_apply (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) (s : S) :
    derivationOfSurjective f hf D hD (f s) = f (D s) :=
  derivationOfSurjectiveFun_apply f hf D hD s

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
section
namespace FunctorialResolution.EmbeddedResolution

theorem derivation_apply_mem_of_mem_span {k : Type*} [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (D : Derivation k S S) {G : Set S} {T : Ideal S} (hGT : Ideal.span G ≤ T)
    (hD : ∀ g ∈ G, D g ∈ T) {x : S} (hx : x ∈ Ideal.span G) : D x ∈ T := by
  induction hx using Submodule.span_induction with
  | mem g hg => exact hD g hg
  | zero => simp
  | add a b _ _ iha ihb => simpa using Submodule.add_mem T iha ihb
  | smul a b hb ihb =>
      have hb' : b ∈ T := hGT hb
      have hD' : D (a • b) = a • D b + b • D a := by
        rw [smul_eq_mul, D.leibniz]
      rw [hD', smul_eq_mul, smul_eq_mul]
      exact Submodule.add_mem T (Ideal.mul_mem_left T a ihb) (Ideal.mul_mem_right (D a) T hb')

def derivIdeal (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (J : Ideal S) : Ideal S :=
  J ⊔ Ideal.span {x : S | ∃ D : Derivation k S S, ∃ y ∈ J, D y = x}

section
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]

private theorem derivIdeal_eq_sup_span_consolidated7 (J : Ideal S) :
    derivIdeal k J = J ⊔ Ideal.span {x : S | ∃ D : Derivation k S S, ∃ y ∈ J, D y = x} := rfl

theorem le_derivIdeal (J : Ideal S) : J ≤ derivIdeal k J := by
  rw [derivIdeal_eq_sup_span_consolidated7]
  exact le_sup_left

theorem derivation_apply_mem_derivIdeal (J : Ideal S) (D : Derivation k S S) {x : S} (hx : x ∈ J) :
    D x ∈ derivIdeal k J := by
  rw [derivIdeal_eq_sup_span_consolidated7]
  exact Submodule.mem_sup_right (Ideal.subset_span ⟨D, x, hx, rfl⟩)

theorem derivIdeal_le_iff (J K : Ideal S) :
    derivIdeal k J ≤ K ↔ J ≤ K ∧ ∀ D : Derivation k S S, ∀ x ∈ J, D x ∈ K := by
  rw [derivIdeal_eq_sup_span_consolidated7, sup_le_iff, Ideal.span_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun D x hx => h2 ⟨D, x, hx, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro x ⟨D, y, hy, rfl⟩
    exact h2 D y hy

theorem derivIdeal_mono :
    Monotone (derivIdeal k : Ideal S → Ideal S) := by
  intro I J h
  rw [derivIdeal_le_iff]
  exact ⟨h.trans (le_derivIdeal k J), fun D x hx => derivation_apply_mem_derivIdeal k J D (h hx)⟩

theorem derivIdeal_le_derivIdeal {I J : Ideal S} (h : I ≤ J) : derivIdeal k I ≤ derivIdeal k J :=
  derivIdeal_mono k h

theorem derivIdeal_top :
    derivIdeal k (⊤ : Ideal S) = ⊤ :=
  eq_top_iff.mpr (le_derivIdeal k ⊤)

theorem derivIdeal_bot :
    derivIdeal k (⊥ : Ideal S) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [derivIdeal_le_iff]
  refine ⟨le_rfl, fun D x hx => ?_⟩
  rw [Ideal.mem_bot] at hx
  subst hx
  simp

theorem derivIdeal_iSup_le {ι : Sort*} (J : ι → Ideal S) :
    derivIdeal k (⨆ i, J i) ≤ ⨆ i, derivIdeal k (J i) := by
  have hspan : (⨆ i, J i) = Ideal.span (⋃ i, (J i : Set S)) := Submodule.iSup_eq_span J
  have hle : (⨆ i, J i) ≤ ⨆ i, derivIdeal k (J i) :=
    iSup_le fun i => (le_derivIdeal k (J i)).trans (le_iSup (fun j => derivIdeal k (J j)) i)
  rw [derivIdeal_le_iff]
  refine ⟨hle, ?_⟩
  intro D x hx
  rw [hspan] at hx
  refine derivation_apply_mem_of_mem_span D ?_ ?_ hx
  · rw [← hspan]
    exact hle
  · intro g hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    have hi' : g ∈ J i := hi
    exact le_iSup (fun j => derivIdeal k (J j)) i
      (derivation_apply_mem_derivIdeal k (J i) D hi')

theorem derivIdeal_mul_le (I J : Ideal S) :
    derivIdeal k (I * J) ≤ I * derivIdeal k J ⊔ J * derivIdeal k I := by
  rw [derivIdeal_le_iff]
  constructor
  · rw [Ideal.mul_le]
    intro r hr s hs
    exact Submodule.mem_sup_left (Ideal.mul_mem_mul hr (le_derivIdeal k J hs))
  · intro D x hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro m hm n hn
      simp only [Derivation.leibniz, smul_eq_mul]
      refine Submodule.add_mem _ ?_ ?_
      · exact Submodule.mem_sup_left
          (Ideal.mul_mem_mul hm (derivation_apply_mem_derivIdeal k J D hn))
      · exact Submodule.mem_sup_right
          (Ideal.mul_mem_mul hn (derivation_apply_mem_derivIdeal k I D hm))
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb

private theorem derivation_apply_mem_pow_mul_derivIdeal_consolidated7 (J : Ideal S) (D : Derivation k S S) :
    ∀ n : ℕ, ∀ x ∈ J ^ (n + 1), D x ∈ J ^ n * derivIdeal k J := by
  intro n
  induction n with
  | zero =>
      intro x hx
      have hx' : x ∈ J := by simpa using hx
      have h := derivation_apply_mem_derivIdeal k J D hx'
      simpa using h
  | succ n ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        have hL : D (a * b) = a * D b + b * D a := by
          rw [D.leibniz, smul_eq_mul, smul_eq_mul]
        rw [hL]
        refine Submodule.add_mem _ ?_ ?_
        · exact Ideal.mul_mem_mul ha (derivation_apply_mem_derivIdeal k J D hb)
        · have h2 : b * D a ∈ J * (J ^ n * derivIdeal k J) :=
            Ideal.mul_mem_mul hb (ih a ha)
          have h3 : J * (J ^ n * derivIdeal k J) = J ^ (n + 1) * derivIdeal k J := by
            rw [← mul_assoc, pow_succ, mul_comm J (J ^ n)]
          rwa [h3] at h2
      · intro y z hy hz
        simpa using Submodule.add_mem _ hy hz

theorem derivIdeal_pow_succ_le (J : Ideal S) (n : ℕ) : derivIdeal k (J ^ (n + 1)) ≤ J ^ n * derivIdeal k J := by
  rw [derivIdeal_le_iff]
  refine ⟨?_, ?_⟩
  · rw [pow_succ]
    exact Ideal.mul_le.mpr fun a ha b hb => Ideal.mul_mem_mul ha (le_derivIdeal k J hb)
  · intro D x hx
    exact derivation_apply_mem_pow_mul_derivIdeal_consolidated7 k J D n x hx


end

private theorem derivation_apply_mem_pow_of_mem_pow_succ_consolidated7 {k : Type*} [CommRing k] {S : Type*}
    [CommRing S] [Algebra k S] (J : Ideal S) (D : Derivation k S S) :
    ∀ n : ℕ, ∀ x ∈ J ^ (n + 1), D x ∈ J ^ n := by
  intro n
  induction n with
  | zero =>
      intro x _
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  | succ n ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        simp only [Derivation.leibniz, smul_eq_mul]
        refine Submodule.add_mem _ (Ideal.mul_mem_right _ _ ha) ?_
        have hb' : D a * b ∈ J ^ n * J := Ideal.mul_mem_mul (ih a ha) hb
        rw [← pow_succ] at hb'
        rw [mul_comm b (D a)]
        exact hb'
      · intro a b ha hb
        rw [map_add]
        exact Submodule.add_mem _ ha hb

theorem derivIdeal_pow_succ_le_pow (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (J : Ideal S) (n : ℕ) : derivIdeal k (J ^ (n + 1)) ≤ J ^ n := by
  rw [derivIdeal_le_iff]
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro m hm y _
      exact Ideal.mul_mem_right _ _ hm
    · intro a b ha hb
      exact Submodule.add_mem _ ha hb
  · intro D x hx
    exact derivation_apply_mem_pow_of_mem_pow_succ_consolidated7 J D n x hx

private theorem pow_succ_le_pow_consolidated7 {S : Type*} [CommRing S] (J : Ideal S) (m : ℕ) :
    J ^ (m + 1) ≤ J ^ m := by
  rw [pow_succ]
  exact Ideal.mul_le.mpr fun r hr s _ => Ideal.mul_mem_right s _ hr

section
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]

theorem derivIdeal_pow_le (J : Ideal S) (n : ℕ) : derivIdeal k (J ^ n) ≤ J ^ (n - 1) := by
  obtain _ | m := n
  · have h : (J ^ (0 - 1 : ℕ) : Ideal S) = ⊤ := by simp
    exact le_top.trans h.ge
  · have key : derivIdeal k (J ^ (m + 1)) ≤ J ^ m := by
      rw [derivIdeal_le_iff]
      exact ⟨pow_succ_le_pow_consolidated7 J m,
        fun D x hx => derivation_apply_mem_pow_of_mem_pow_succ_consolidated7 J D m x hx⟩
    exact key

theorem derivIdeal_le_pow_of_le_pow {I P : Ideal S} {n : ℕ} (h : I ≤ P ^ n) : derivIdeal k I ≤ P ^ (n - 1) := by
  cases n with
  | zero =>
      have hP : P ^ (0 - 1) = (⊤ : Ideal S) := by
        rw [Nat.zero_sub, pow_zero, Ideal.one_eq_top]
      exact le_of_le_of_eq le_top hP.symm
  | succ m =>
      have h2 : derivIdeal k I ≤ P ^ m :=
        (derivIdeal_mono k h).trans (derivIdeal_pow_succ_le_pow k P m)
      have hm : m + 1 - 1 = m := by omega
      exact le_of_le_of_eq h2 (congrArg (fun i => P ^ i) hm.symm)


end

def derivIdealIterate (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S] :
    ℕ → Ideal S → Ideal S
  | 0, J => J
  | r + 1, J => derivIdeal k (derivIdealIterate k r J)

section
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]

theorem derivIdealIterate_zero (J : Ideal S) : derivIdealIterate k 0 J = J := rfl

theorem derivIdealIterate_succ (r : ℕ) (J : Ideal S) :
    derivIdealIterate k (r + 1) J = derivIdeal k (derivIdealIterate k r J) := rfl

theorem derivIdealIterate_one (J : Ideal S) : derivIdealIterate k 1 J = derivIdeal k J := rfl

theorem derivIdealIterate_add (r s : ℕ) (J : Ideal S) :
    derivIdealIterate k (r + s) J = derivIdealIterate k r (derivIdealIterate k s J) := by
  induction r with
  | zero => rw [Nat.zero_add, derivIdealIterate_zero]
  | succ r ih => rw [Nat.succ_add, derivIdealIterate_succ, derivIdealIterate_succ, ih]

theorem le_derivIdealIterate (r : ℕ) (J : Ideal S) : J ≤ derivIdealIterate k r J := by
  induction r with
  | zero => exact (derivIdealIterate_zero k J).ge
  | succ r ih =>
      rw [derivIdealIterate_succ]
      exact ih.trans (le_derivIdeal k _)

theorem derivIdealIterate_le_of_le {r r' : ℕ} (h : r ≤ r') (J : Ideal S) :
    derivIdealIterate k r J ≤ derivIdealIterate k r' J := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm r d, derivIdealIterate_add]
  exact le_derivIdealIterate k d _

theorem derivIdealIterate_le_pow_of_le_pow {I P : Ideal S} {n : ℕ} (r : ℕ) (h : I ≤ P ^ n) :
    derivIdealIterate k r I ≤ P ^ (n - r) := by
  induction r with
  | zero =>
      rw [derivIdealIterate_zero, Nat.sub_zero]
      exact h
  | succ r ih =>
      rw [derivIdealIterate_succ]
      have h1 : derivIdeal k (derivIdealIterate k r I) ≤ derivIdeal k (P ^ (n - r)) :=
        derivIdeal_mono k ih
      have h2 : derivIdeal k (P ^ (n - r)) ≤ P ^ (n - r - 1) := derivIdeal_pow_le k P (n - r)
      have h3 : n - r - 1 = n - (r + 1) := by omega
      rw [h3] at h2
      exact h1.trans h2


end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealOrder
section
namespace FunctorialResolution.EmbeddedResolution

open IsLocalRing

variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

noncomputable def idealOrder (I : Ideal R) : ℕ∞ :=
  sSup ((fun n : ℕ => (n : ℕ∞)) '' {n : ℕ | I ≤ IsLocalRing.maximalIdeal R ^ n})

section
variable (I : Ideal R)

theorem le_idealOrder_iff (n : ℕ) :
    (n : ℕ∞) ≤ idealOrder I ↔ I ≤ IsLocalRing.maximalIdeal R ^ n := by
  have hdef : idealOrder I
      = sSup ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | I ≤ IsLocalRing.maximalIdeal R ^ k}) := rfl
  constructor
  · intro h
    by_contra hI
    rw [hdef] at h
    have hn : n ≠ 0 := by
      rintro rfl
      apply hI
      rw [pow_zero, Ideal.one_eq_top]
      exact le_top
    have hsup : sSup ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | I ≤ IsLocalRing.maximalIdeal R ^ k})
        ≤ ((n - 1 : ℕ) : ℕ∞) := by
      apply sSup_le
      rintro x ⟨k, hk, rfl⟩
      have hk' : I ≤ IsLocalRing.maximalIdeal R ^ k := hk
      have hkn : k < n := by
        by_contra hkn
        push Not at hkn
        exact hI (le_trans hk' (Ideal.pow_le_pow_right hkn))
      have hk2 : k ≤ n - 1 := by omega
      show (k : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞)
      exact_mod_cast hk2
    have hcon : n ≤ n - 1 := by exact_mod_cast h.trans hsup
    omega
  · intro h
    rw [hdef]
    exact le_sSup ⟨n, h, rfl⟩

theorem idealOrder_eq_top_iff :
    idealOrder I = ⊤ ↔ ∀ n : ℕ, I ≤ IsLocalRing.maximalIdeal R ^ n := by
  constructor
  · intro h n
    rw [← le_idealOrder_iff, h]
    exact le_top
  · intro h
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    exact (le_idealOrder_iff I n).mpr (h n)

theorem one_le_idealOrder_iff :
    1 ≤ idealOrder I ↔ I ≤ IsLocalRing.maximalIdeal R := by
  have h := le_idealOrder_iff I 1
  rw [Nat.cast_one, pow_one] at h
  exact h

theorem one_le_idealOrder_iff_ne_top :
    1 ≤ idealOrder I ↔ I ≠ ⊤ := by
  rw [one_le_idealOrder_iff]
  constructor
  · intro h hI
    rw [hI] at h
    exact (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp h)
  · intro h
    exact IsLocalRing.le_maximalIdeal h

theorem idealOrder_eq_zero_iff :
    idealOrder I = 0 ↔ ¬ I ≤ IsLocalRing.maximalIdeal R := by
  rw [← one_le_idealOrder_iff, not_le, Order.lt_one_iff]


end

theorem idealOrder_top : idealOrder (⊤ : Ideal R) = 0 := by
  by_contra h
  have h1 : (1 : ℕ∞) ≤ idealOrder (⊤ : Ideal R) := by
    rw [Order.one_le_iff_ne_zero]
    exact h
  rw [one_le_idealOrder_iff_ne_top] at h1
  exact h1 rfl

theorem idealOrder_bot : idealOrder (⊥ : Ideal R) = ⊤ := by
  rw [idealOrder_eq_top_iff]
  intro n
  exact bot_le

section
variable [IsNoetherianRing R] {I : Ideal R} (hI : I ≠ ⊥)
include hI

theorem idealOrder_ne_top_of_ne_bot :
    idealOrder I ≠ ⊤ := by
  intro h
  rw [idealOrder_eq_top_iff] at h
  have key : (⨅ n : ℕ, IsLocalRing.maximalIdeal R ^ n) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing (I := IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hle : I ≤ ⊥ := by
    rw [← key]
    exact le_iInf h
  exact hI (le_bot_iff.mp hle)

theorem exists_idealOrder_eq_coe :
    ∃ n : ℕ, idealOrder I = (n : ℕ∞) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (idealOrder_ne_top_of_ne_bot hI)
  exact ⟨n, hn.symm⟩


end

theorem idealOrder_le_of_le {I J : Ideal R} (h : I ≤ J) : idealOrder J ≤ idealOrder I := by
  have hI : idealOrder I
      = sSup ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | I ≤ IsLocalRing.maximalIdeal R ^ k}) := rfl
  have hJ : idealOrder J
      = sSup ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | J ≤ IsLocalRing.maximalIdeal R ^ k}) := rfl
  rw [hI, hJ]
  apply sSup_le
  rintro x ⟨n, hn, rfl⟩
  have hn' : I ≤ IsLocalRing.maximalIdeal R ^ n := le_trans h hn
  exact le_sSup ⟨n, hn', rfl⟩

theorem idealOrder_sup (I J : Ideal R) :
    idealOrder (I ⊔ J) = min (idealOrder I) (idealOrder J) := by
  apply le_antisymm
  · exact le_min (idealOrder_le_of_le (le_sup_left : I ≤ I ⊔ J))
      (idealOrder_le_of_le (le_sup_right : J ≤ I ⊔ J))
  · apply ENat.forall_natCast_le_iff_le.mp
    intro n hn
    rw [le_min_iff] at hn
    rw [le_idealOrder_iff]
    exact sup_le ((le_idealOrder_iff I n).mp hn.1) ((le_idealOrder_iff J n).mp hn.2)

private theorem enat_add_le_of_forall_natCast_add_le_consolidated11 {a b c : ℕ∞}
    (h : ∀ m n : ℕ, (m : ℕ∞) ≤ a → (n : ℕ∞) ≤ b → ((m + n : ℕ) : ℕ∞) ≤ c) : a + b ≤ c := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · have hc : c = ⊤ := by
      rw [ENat.eq_top_iff_forall_ge]
      intro n
      have hn := h n 0 le_top (by simp)
      simpa using hn
    rw [hc]
    exact le_top
  rcases eq_or_ne b ⊤ with rfl | hb
  · have hc : c = ⊤ := by
      rw [ENat.eq_top_iff_forall_ge]
      intro n
      have hn := h 0 n (by simp) le_top
      simpa using hn
    rw [hc]
    exact le_top
  lift a to ℕ using ha
  lift b to ℕ using hb
  have hab := h a b le_rfl le_rfl
  simpa using hab

theorem add_idealOrder_le_idealOrder_mul (I J : Ideal R) :
    idealOrder I + idealOrder J ≤ idealOrder (I * J) := by
  refine enat_add_le_of_forall_natCast_add_le_consolidated11 (fun m n hm hn => ?_)
  rw [le_idealOrder_iff] at hm hn ⊢
  rw [pow_add]
  exact Ideal.mul_mono hm hn

theorem mul_idealOrder_le_idealOrder_pow (I : Ideal R) (c : ℕ) :
    (c : ℕ∞) * idealOrder I ≤ idealOrder (I ^ c) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [Nat.cast_zero, zero_mul]
    exact zero_le
  · have hc1 : 1 ≤ c := hc
    rcases eq_or_ne (idealOrder I) ⊤ with hI | hI
    · have hIall : ∀ n : ℕ, I ≤ IsLocalRing.maximalIdeal R ^ n :=
        (idealOrder_eq_top_iff I).mp hI
      have htop : idealOrder (I ^ c) = ⊤ := by
        rw [idealOrder_eq_top_iff]
        intro n
        have h1 : I ^ c ≤ I ^ 1 := Ideal.pow_le_pow_right hc1
        rw [pow_one] at h1
        exact le_trans h1 (hIall n)
      rw [htop]
      exact le_top
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hI
      have hIk : I ≤ IsLocalRing.maximalIdeal R ^ k := (le_idealOrder_iff I k).mp hk.le
      rw [← hk, ← Nat.cast_mul, le_idealOrder_iff]
      calc I ^ c ≤ (IsLocalRing.maximalIdeal R ^ k) ^ c :=
            Ideal.pow_right_mono hIk c
        _ = IsLocalRing.maximalIdeal R ^ (c * k) := by rw [← pow_mul, mul_comm k c]

section
variable (f : R →+* S) (hf : (IsLocalRing.maximalIdeal R).map f ≤ IsLocalRing.maximalIdeal S)
include hf

private theorem map_maximalIdeal_pow_le_pow_consolidated11 (n : ℕ) :
    ((IsLocalRing.maximalIdeal R) ^ n).map f ≤ (IsLocalRing.maximalIdeal S) ^ n := by
  induction n with
  | zero =>
      have hS : (IsLocalRing.maximalIdeal S) ^ 0 = (⊤ : Ideal S) := by
        rw [pow_zero, Ideal.one_eq_top]
      rw [hS]
      exact le_top
  | succ n ih =>
      rw [pow_succ, pow_succ, Ideal.map_mul]
      exact Ideal.mul_mono ih hf

theorem idealOrder_le_idealOrder_map (I : Ideal R) :
    idealOrder I ≤ idealOrder (I.map f) := by
  refine ENat.forall_natCast_le_iff_le.mp (fun n hn => ?_)
  rw [le_idealOrder_iff] at hn ⊢
  exact le_trans (Ideal.map_mono hn) (map_maximalIdeal_pow_le_pow_consolidated11 f hf n)


end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.MultiIndexDerivation
section
namespace FunctorialResolution.EmbeddedResolution

section

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

def multiIndexDeriv {h : ℕ} (D : Fin h → Derivation k R R) (α : Fin h → ℕ) (x : R) : R :=
  Fin.foldr h (fun i y => (⇑(D i))^[α i] y) x

@[simp]
theorem multiIndexDeriv_of_isEmpty (D : Fin 0 → Derivation k R R) (α : Fin 0 → ℕ) :
    multiIndexDeriv D α = id := by
  funext x
  simp [multiIndexDeriv]

private theorem foldr_eq_self_of_forall_eq_self_consolidated2 {A : Type*} :
    ∀ (n : ℕ) (f : Fin n → A → A), (∀ (i : Fin n) (y : A), f i y = y) →
      ∀ x : A, Fin.foldr n f x = x := by
  intro n
  induction n with
  | zero =>
      intro f hf x
      simp
  | succ n ih =>
      intro f hf x
      rw [Fin.foldr_succ, ih (fun i => f i.succ) (fun i y => hf i.succ y) x]
      exact hf 0 x

@[simp]
theorem multiIndexDeriv_zero {h : ℕ} (D : Fin h → Derivation k R R) (f : R) :
    multiIndexDeriv D (0 : Fin h → ℕ) f = f := by
  unfold multiIndexDeriv
  exact foldr_eq_self_of_forall_eq_self_consolidated2 h (fun i y => (⇑(D i))^[(0 : Fin h → ℕ) i] y)
    (fun i y => by simp) f

@[simp]
theorem multiIndexDeriv_fun_zero {h : ℕ} (D : Fin h → Derivation k R R) (f : R) :
    multiIndexDeriv D (fun _ => 0) f = f :=
  multiIndexDeriv_zero D f

section
variable (J : Ideal R)

private theorem mul_pow_sub_one_le_consolidated2 (n : ℕ) :
    J * J ^ (n - 1) ≤ J ^ n := by
  cases n with
  | zero =>
      show J * J ^ 0 ≤ J ^ 0
      rw [pow_zero, Ideal.one_eq_top]
      exact le_top
  | succ m =>
      show J * J ^ m ≤ J ^ (m + 1)
      exact le_of_eq (by rw [mul_comm, ← pow_succ])

private theorem derivation_mem_pow_sub_one_consolidated2 (D : Derivation k R R) :
    ∀ (n : ℕ) (f : R), f ∈ J ^ n → D f ∈ J ^ (n - 1) := by
  intro n
  induction n with
  | zero =>
      intro f _
      show D f ∈ J ^ 0
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  | succ m ih =>
      intro f hf
      rw [pow_succ] at hf
      show D f ∈ J ^ m
      refine Submodule.mul_induction_on (C := fun x => D x ∈ J ^ m) hf ?_ ?_
      · intro a ha b hb
        have hDa : D a ∈ J ^ (m - 1) := ih a ha
        have hL : D (a * b) = a * D b + b * D a := by
          rw [D.leibniz, smul_eq_mul, smul_eq_mul]
        show D (a * b) ∈ J ^ m
        rw [hL]
        refine Submodule.add_mem _ (Ideal.mul_mem_right _ _ ha) ?_
        exact mul_pow_sub_one_le_consolidated2 J m (Ideal.mul_mem_mul hb hDa)
      · intro x y hx hy
        show D (x + y) ∈ J ^ m
        rw [map_add]
        exact Submodule.add_mem _ hx hy

private theorem iterate_derivation_mem_pow_sub_consolidated2 (D : Derivation k R R) :
    ∀ (m n : ℕ) (f : R), f ∈ J ^ n → (⇑D)^[m] f ∈ J ^ (n - m) := by
  intro m
  induction m with
  | zero =>
      intro n f hf
      rw [Function.iterate_zero_apply, Nat.sub_zero]
      exact hf
  | succ m ih =>
      intro n f hf
      rw [Function.iterate_succ_apply]
      have h1 : D f ∈ J ^ (n - 1) := derivation_mem_pow_sub_one_consolidated2 J D n f hf
      have h2 := ih (n - 1) (D f) h1
      have h3 : n - 1 - m = n - (m + 1) := by omega
      rw [h3] at h2
      exact h2

private theorem foldr_iterate_mem_pow_sub_consolidated2 :
    ∀ (h : ℕ) (D : Fin h → Derivation k R R) (α : Fin h → ℕ) (n : ℕ) (f : R), f ∈ J ^ n →
      Fin.foldr h (fun i y => (⇑(D i))^[α i] y) f ∈ J ^ (n - ∑ i, α i) := by
  intro h
  induction h with
  | zero =>
      intro D α n f hf
      have hz : ∑ i : Fin 0, α i = 0 := by simp
      rw [Fin.foldr_zero, hz, Nat.sub_zero]
      exact hf
  | succ h ih =>
      intro D α n f hf
      have hinner : Fin.foldr h (fun i y => (⇑(D i.succ))^[α i.succ] y) f
          ∈ J ^ (n - ∑ i : Fin h, α i.succ) :=
        ih (fun i => D i.succ) (fun i => α i.succ) n f hf
      have h2 := iterate_derivation_mem_pow_sub_consolidated2 J (D 0) (α 0)
        (n - ∑ i : Fin h, α i.succ) _ hinner
      have hs0 : ∑ i, α i = α 0 + ∑ i : Fin h, α i.succ := Fin.sum_univ_succ α
      have hs : n - ∑ i, α i = n - (∑ i : Fin h, α i.succ) - α 0 := by
        rw [hs0]; omega
      rw [Fin.foldr_succ, hs]
      exact h2


end

theorem multiIndexDeriv_mem_pow_sub {h : ℕ} (D : Fin h → Derivation k R R) (J : Ideal R) (n : ℕ)
    {f : R} (hf : f ∈ J ^ n) (α : Fin h → ℕ) :
    multiIndexDeriv D α f ∈ J ^ (n - ∑ i, α i) := by
  exact foldr_iterate_mem_pow_sub_consolidated2 J h D α n f hf

section
variable {B S : Type*} [CommRing B] [CommRing S] [Algebra B S] (D : Derivation B S S)

private theorem derivation_natCast_mul_consolidated2 (m : ℕ) (x : S) : D ((m : S) * x) = (m : S) * D x := by
  have h1 : ((m : S) * x) = m • x := by rw [nsmul_eq_mul]
  have h2 : ((m : S) * D x) = m • D x := by rw [nsmul_eq_mul]
  rw [h1, h2, map_nsmul]

private theorem iterate_derivation_natCast_mul_consolidated2 (m c : ℕ) (x : S) :
    (⇑D)^[m] ((c : S) * x) = (c : S) * (⇑D)^[m] x := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, derivation_natCast_mul_consolidated2]

private theorem iterate_derivation_sum_consolidated2 (m : ℕ) {ι : Type*} (s : Finset ι) (F : ι → S) :
    (⇑D)^[m] (∑ i ∈ s, F i) = ∑ i ∈ s, (⇑D)^[m] (F i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, map_sum]


end

private theorem sum_choose_succ_mul_eq_consolidated2 {S : Type*} [CommRing S] (u v : ℕ → S) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : S) * (u (i + 1) * v (n - i)))
        + (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : S) * (u i * v (n + 1 - i)))
      = ∑ i ∈ Finset.range (n + 1 + 1), (((n + 1).choose i : ℕ) : S) * (u i * v (n + 1 - i)) := by
  have e1 : (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : S) * (u (i + 1) * v (n - i)))
      = (∑ i ∈ Finset.range n, ((n.choose i : ℕ) : S) * (u (i + 1) * v (n - i)))
        + u (n + 1) * v 0 := by
    rw [Finset.sum_range_succ]
    simp
  have e2 : (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : S) * (u i * v (n + 1 - i)))
      = (∑ i ∈ Finset.range n, ((n.choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
        + u 0 * v (n + 1) := by
    rw [Finset.sum_range_succ']
    simp
  have e3 : (∑ i ∈ Finset.range (n + 1 + 1), (((n + 1).choose i : ℕ) : S) * (u i * v (n + 1 - i)))
      = (∑ i ∈ Finset.range (n + 1), (((n + 1).choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
        + u 0 * v (n + 1) := by
    rw [Finset.sum_range_succ']
    simp
  have e4 : (∑ i ∈ Finset.range (n + 1),
        (((n + 1).choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
      = (∑ i ∈ Finset.range n, (((n + 1).choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
        + u (n + 1) * v 0 := by
    rw [Finset.sum_range_succ]
    simp
  have e5 : (∑ i ∈ Finset.range n,
        (((n + 1).choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
      = (∑ i ∈ Finset.range n, ((n.choose i : ℕ) : S) * (u (i + 1) * v (n - i)))
        + (∑ i ∈ Finset.range n, ((n.choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hc : ((n + 1).choose (i + 1) : ℕ) = n.choose i + n.choose (i + 1) :=
      Nat.choose_succ_succ n i
    rw [hc]
    push_cast
    ring
  rw [e1, e2, e3, e4, e5]
  ring

section
variable {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]

private theorem iterate_derivation_mul_consolidated2 (D : Derivation B S S) (n : ℕ) (x y : S) :
    (⇑D)^[n] (x * y)
      = ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : S) * ((⇑D)^[i] x * (⇑D)^[n - i] y) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : ∀ i ∈ Finset.range (n + 1),
          D (((n.choose i : ℕ) : S) * ((⇑D)^[i] x * (⇑D)^[n - i] y))
            = ((n.choose i : ℕ) : S) * ((⇑D)^[i + 1] x * (⇑D)^[n - i] y)
              + ((n.choose i : ℕ) : S) * ((⇑D)^[i] x * (⇑D)^[n + 1 - i] y) := by
        intro i hi
        rw [Finset.mem_range] at hi
        have e1 : D ((⇑D)^[i] x) = (⇑D)^[i + 1] x := (Function.iterate_succ_apply' (⇑D) i x).symm
        have e2 : D ((⇑D)^[n - i] y) = (⇑D)^[n + 1 - i] y := by
          have hni : n + 1 - i = n - i + 1 := by omega
          rw [hni]
          exact (Function.iterate_succ_apply' (⇑D) (n - i) y).symm
        rw [derivation_natCast_mul_consolidated2, D.leibniz, e1, e2]
        simp only [smul_eq_mul]
        ring
      rw [Function.iterate_succ_apply', ih, map_sum]
      refine Eq.trans (Finset.sum_congr rfl hstep) ?_
      rw [Finset.sum_add_distrib]
      exact sum_choose_succ_mul_eq_consolidated2 (fun i => (⇑D)^[i] x) (fun i => (⇑D)^[i] y) n

private theorem multiIndexDeriv_succ_consolidated2 {m : ℕ} (D : Fin (m + 1) → Derivation B S S) (α : Fin (m + 1) → ℕ) (x : S) :
    multiIndexDeriv D α x
      = (⇑(D 0))^[α 0] (multiIndexDeriv (fun i => D i.succ) (fun i => α i.succ) x) := by
  simp only [multiIndexDeriv, Fin.foldr_succ]


end

private theorem fin_cons_self_tail_consolidated2 {m : ℕ} (β : Fin (m + 1) → ℕ) :
    Fin.cons (β 0) (fun i => β i.succ) = β := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp
  · intro j
    simp

private def finSuccFunEquivProd_consolidated2 (m : ℕ) : (Fin (m + 1) → ℕ) ≃ ℕ × (Fin m → ℕ) where
  toFun β := (β 0, fun i => β i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv β := fin_cons_self_tail_consolidated2 β
  right_inv p := by
    rcases p with ⟨a, b⟩
    simp

private theorem sum_piFinset_succ_consolidated2 {M : Type*} [AddCommMonoid M] {m : ℕ}
    (s : Fin (m + 1) → Finset ℕ) (F : (Fin (m + 1) → ℕ) → M) :
    ∑ β ∈ Fintype.piFinset s, F β
      = ∑ j ∈ s 0, ∑ γ ∈ Fintype.piFinset (fun i => s i.succ), F (Fin.cons j γ) := by
  rw [← Finset.sum_product']
  refine Finset.sum_equiv (finSuccFunEquivProd_consolidated2 m) ?_ ?_
  · intro β
    constructor
    · intro hβ
      have hβ' := Fintype.mem_piFinset.1 hβ
      exact Finset.mem_product.2 ⟨hβ' 0, Fintype.mem_piFinset.2 (fun i => hβ' i.succ)⟩
    · intro hβ
      have h1 := Finset.mem_product.1 hβ
      refine Fintype.mem_piFinset.2 (fun i => ?_)
      refine Fin.cases ?_ ?_ i
      · exact h1.1
      · intro j
        exact Fintype.mem_piFinset.1 h1.2 j
  · intro β _
    exact congrArg F (fin_cons_self_tail_consolidated2 β).symm

section
variable {h : ℕ} (D : Fin h → Derivation k R R)

theorem multiIndexDeriv_mul (α : Fin h → ℕ) (f g : R) :
    multiIndexDeriv D α (f * g) =
      ∑ β ∈ Fintype.piFinset fun i => Finset.range (α i + 1),
        ((∏ i, (α i).choose (β i) : ℕ) : R) * multiIndexDeriv D β f *
          multiIndexDeriv D (fun i => α i - β i) g := by
  induction h with
  | zero =>
      have hset : (Fintype.piFinset fun i : Fin 0 => Finset.range (α i + 1))
          = {fun _ => 0} := by
        refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
        · exact Fintype.mem_piFinset.2 (fun i => i.elim0)
        · intro x _
          funext i
          exact i.elim0
      rw [hset, Finset.sum_singleton]
      simp
  | succ h ih =>
      have hcons : ∀ (j : ℕ) (γ : Fin h → ℕ) (x : R),
          multiIndexDeriv D (Fin.cons j γ) x
            = (⇑(D 0))^[j] (multiIndexDeriv (fun i => D i.succ) γ x) := by
        intro j γ x
        rw [multiIndexDeriv_succ_consolidated2 D (Fin.cons j γ) x]
        simp
      have hcons2 : ∀ (j : ℕ) (γ : Fin h → ℕ) (x : R),
          multiIndexDeriv D (fun i => α i - (Fin.cons j γ : Fin (h + 1) → ℕ) i) x
            = (⇑(D 0))^[α 0 - j]
                (multiIndexDeriv (fun i => D i.succ) (fun i => α i.succ - γ i) x) := by
        intro j γ x
        rw [multiIndexDeriv_succ_consolidated2 D (fun i => α i - (Fin.cons j γ : Fin (h + 1) → ℕ) i) x]
        simp
      have key : ∀ γ : Fin h → ℕ,
          (⇑(D 0))^[α 0] (((∏ i, (α i.succ).choose (γ i) : ℕ) : R)
              * multiIndexDeriv (fun i => D i.succ) γ f
              * multiIndexDeriv (fun i => D i.succ) (fun i => α i.succ - γ i) g)
            = ∑ j ∈ Finset.range (α 0 + 1),
                ((∏ i, (α i).choose ((Fin.cons j γ : Fin (h + 1) → ℕ) i) : ℕ) : R)
                  * multiIndexDeriv D (Fin.cons j γ) f
                  * multiIndexDeriv D (fun i => α i - (Fin.cons j γ : Fin (h + 1) → ℕ) i) g := by
        intro γ
        have hA : ((∏ i, (α i.succ).choose (γ i) : ℕ) : R)
              * multiIndexDeriv (fun i => D i.succ) γ f
              * multiIndexDeriv (fun i => D i.succ) (fun i => α i.succ - γ i) g
            = ((∏ i, (α i.succ).choose (γ i) : ℕ) : R)
              * (multiIndexDeriv (fun i => D i.succ) γ f
                * multiIndexDeriv (fun i => D i.succ) (fun i => α i.succ - γ i) g) :=
          mul_assoc _ _ _
        rw [hA, iterate_derivation_natCast_mul_consolidated2, iterate_derivation_mul_consolidated2, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hcons j γ f, hcons2 j γ g, Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        push_cast
        ring
      rw [multiIndexDeriv_succ_consolidated2 D α (f * g), ih (fun i => D i.succ) (fun i => α i.succ),
        iterate_derivation_sum_consolidated2]
      refine Eq.trans (Finset.sum_congr rfl (fun γ _ => key γ)) ?_
      rw [Finset.sum_comm]
      exact (sum_piFinset_succ_consolidated2 (fun i : Fin (h + 1) => Finset.range (α i + 1))
        (fun β => ((∏ i, (α i).choose (β i) : ℕ) : R) * multiIndexDeriv D β f *
          multiIndexDeriv D (fun i => α i - β i) g)).symm

theorem multiIndexDeriv_mul_sub_sum_mem (J : Ideal R)
    (r s : ℕ) (α : Fin h → ℕ) (hα : ∑ i, α i = r + s) {f g : R}
    (hf : f ∈ J ^ r) (hg : g ∈ J ^ s) :
    multiIndexDeriv D α (f * g) -
        ∑ β ∈ (Fintype.piFinset fun i => Finset.range (α i + 1)).filter
            (fun β => ∑ i, β i = r),
          ((∏ i, (α i).choose (β i) : ℕ) : R) * multiIndexDeriv D β f *
            multiIndexDeriv D (fun i => α i - β i) g ∈ J := by
  rw [multiIndexDeriv_mul D α f g,
    ← Finset.sum_filter_add_sum_filter_not
      (Fintype.piFinset fun i => Finset.range (α i + 1)) (fun β => ∑ i, β i = r),
    add_sub_cancel_left]
  refine Ideal.sum_mem _ ?_
  intro β hβ
  rw [Finset.mem_filter] at hβ
  obtain ⟨hβmem, hβne⟩ := hβ
  have hβi : ∀ i, β i ≤ α i := fun i =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Fintype.mem_piFinset.mp hβmem i))
  have h1 : (∑ i, (α i - β i)) + ∑ i, β i = r + s := by
    rw [← hα, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hβi i)
  by_cases hlt : ∑ i, β i < r
  · have hmem : multiIndexDeriv D β f ∈ J ^ (r - ∑ i, β i) :=
      multiIndexDeriv_mem_pow_sub D J r hf β
    have hx : multiIndexDeriv D β f ∈ J := by
      have hpos : 0 < r - ∑ i, β i := by omega
      exact Ideal.pow_le_self hpos.ne' hmem
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hx)
  · have hmem : multiIndexDeriv D (fun i => α i - β i) g ∈ J ^ (s - ∑ i, (α i - β i)) :=
      multiIndexDeriv_mem_pow_sub D J s hg (fun i => α i - β i)
    have hy : multiIndexDeriv D (fun i => α i - β i) g ∈ J := by
      have hpos : 0 < s - ∑ i, (α i - β i) := by omega
      exact Ideal.pow_le_self hpos.ne' hmem
    exact Ideal.mul_mem_left _ _ hy


end

private theorem foldr_comm_of_comm_consolidated2 {A : Type*} (E : A → A) :
    ∀ (n : ℕ) (F : Fin n → A → A), (∀ (i : Fin n) (y : A), E (F i y) = F i (E y)) →
      ∀ x : A, E (Fin.foldr n F x) = Fin.foldr n F (E x) := by
  intro n
  induction n with
  | zero =>
      intro F _ x
      simp
  | succ n ih =>
      intro F hF x
      rw [Fin.foldr_succ, Fin.foldr_succ, hF 0,
        ih (fun i => F i.succ) (fun i y => hF i.succ y) x]

private theorem multiIndexDeriv_add_of_comm_forall_consolidated2 :
    ∀ (n : ℕ) (D : Fin n → Derivation k R R),
      (∀ i j : Fin n, ∀ x : R, D i (D j x) = D j (D i x)) →
      ∀ (α β : Fin n → ℕ) (x : R),
        multiIndexDeriv D (α + β) x = multiIndexDeriv D α (multiIndexDeriv D β x) := by
  intro n
  induction n with
  | zero =>
      intro D _ α β x
      simp
  | succ n ih =>
      intro D hD α β x
      have key : ∀ (γ : Fin (n + 1) → ℕ) (y : R),
          multiIndexDeriv D γ y =
            (⇑(D 0))^[γ 0]
              (multiIndexDeriv (fun i : Fin n => D i.succ) (fun i : Fin n => γ i.succ) y) := by
        intro γ y
        exact Fin.foldr_succ (fun (i : Fin (n + 1)) (z : R) => (⇑(D i))^[γ i] z) y
      have hcomm0 : ∀ (γ : Fin n → ℕ) (y : R),
          (⇑(D 0)) (multiIndexDeriv (fun i : Fin n => D i.succ) γ y) =
            multiIndexDeriv (fun i : Fin n => D i.succ) γ ((⇑(D 0)) y) := by
        intro γ y
        have hc : ∀ (i : Fin n) (z : R),
            (⇑(D 0)) ((⇑(D i.succ))^[γ i] z) = (⇑(D i.succ))^[γ i] ((⇑(D 0)) z) := by
          intro i z
          have hcomm : Function.Commute (⇑(D 0) : R → R) (⇑(D i.succ) : R → R) :=
            fun w => hD 0 i.succ w
          exact hcomm.iterate_right (γ i) z
        exact foldr_comm_of_comm_consolidated2 (⇑(D 0)) n (fun i z => (⇑(D i.succ))^[γ i] z) hc y
      have hcomm : ∀ (m : ℕ) (γ : Fin n → ℕ) (y : R),
          (⇑(D 0))^[m] (multiIndexDeriv (fun i : Fin n => D i.succ) γ y) =
            multiIndexDeriv (fun i : Fin n => D i.succ) γ ((⇑(D 0))^[m] y) := by
        intro m γ y
        have hc : Function.Commute (multiIndexDeriv (fun i : Fin n => D i.succ) γ)
            (⇑(D 0) : R → R) := fun w => (hcomm0 γ w).symm
        exact (hc.iterate_right m y).symm
      have hidx : (fun i : Fin n => (α + β) i.succ)
          = (fun i : Fin n => α i.succ) + (fun i : Fin n => β i.succ) := by
        funext i
        simp
      rw [key (α + β) x, hidx,
        ih (fun i : Fin n => D i.succ) (fun i j w => hD i.succ j.succ w)
          (fun i : Fin n => α i.succ) (fun i : Fin n => β i.succ) x,
        key β x, key α, Pi.add_apply, Function.iterate_add_apply,
        hcomm (β 0) (fun i : Fin n => α i.succ)
          (multiIndexDeriv (fun i : Fin n => D i.succ) (fun i : Fin n => β i.succ) x)]

theorem multiIndexDeriv_add {h : ℕ} (D : Fin h → Derivation k R R)
    (hD : ∀ i j : Fin h, ∀ x : R, D i (D j x) = D j (D i x)) (α β : Fin h → ℕ) (x : R) :
    multiIndexDeriv D (α + β) x = multiIndexDeriv D α (multiIndexDeriv D β x) :=
  multiIndexDeriv_add_of_comm_forall_consolidated2 h D hD α β x

def unitMultiIndex {h : ℕ} (i : Fin h) : Fin h → ℕ := fun j => if j = i then 1 else 0

@[simp]
theorem unitMultiIndex_apply {h : ℕ} (i j : Fin h) :
    unitMultiIndex i j = if j = i then 1 else 0 := rfl

theorem sum_unitMultiIndex {h : ℕ} (i : Fin h) : ∑ j, unitMultiIndex i j = 1 := by
  simp [unitMultiIndex]

private theorem foldr_eq_of_eq_id_of_ne_consolidated2 {A : Type*} :
    ∀ (n : ℕ) (F : Fin n → A → A) (i : Fin n) (f : A → A),
      (∀ j : Fin n, j ≠ i → ∀ y : A, F j y = y) → (∀ y : A, F i y = f y) →
      ∀ x : A, Fin.foldr n F x = f x := by
  intro n
  induction n with
  | zero =>
      intro F i
      exact i.elim0
  | succ m ih =>
      intro F i
      induction i using Fin.cases with
      | zero =>
          intro f hne heq x
          have hinner : Fin.foldr m (fun j : Fin m => F j.succ) x = x :=
            foldr_eq_self_of_forall_eq_self_consolidated2 m (fun j : Fin m => F j.succ)
              (fun j y => hne j.succ (Fin.succ_ne_zero j) y) x
          rw [Fin.foldr_succ]
          show F 0 (Fin.foldr m (fun j : Fin m => F j.succ) x) = f x
          rw [hinner]
          exact heq x
      | succ j =>
          intro f hne heq x
          have hinner : Fin.foldr m (fun j' : Fin m => F j'.succ) x = f x :=
            ih (fun j' : Fin m => F j'.succ) j f
              (fun j' hj' y => hne j'.succ (fun hc => hj' (Fin.succ_injective m hc)) y)
              (fun y => heq y) x
          rw [Fin.foldr_succ]
          show F 0 (Fin.foldr m (fun j' : Fin m => F j'.succ) x) = f x
          rw [hinner]
          exact hne 0 (Ne.symm (Fin.succ_ne_zero j)) (f x)

section
variable {h : ℕ} (D : Fin h → Derivation k R R)

theorem multiIndexDeriv_unitMultiIndex (i : Fin h) (x : R) :
    multiIndexDeriv D (unitMultiIndex i) x = D i x := by
  show Fin.foldr h (fun j y => (⇑(D j))^[unitMultiIndex i j] y) x = D i x
  refine foldr_eq_of_eq_id_of_ne_consolidated2 h (fun j y => (⇑(D j))^[unitMultiIndex i j] y) i
    (⇑(D i)) ?_ ?_ x
  · intro j hj y
    simp [unitMultiIndex, hj]
  · intro y
    simp [unitMultiIndex]

theorem multiIndexDeriv_add_unitMultiIndex_apply_first (hD : ∀ i j : Fin h, ∀ x : R, D i (D j x) = D j (D i x)) (α : Fin h → ℕ) (i : Fin h) (x : R) :
    multiIndexDeriv D (α + unitMultiIndex i) x = multiIndexDeriv D α (D i x) := by
  rw [multiIndexDeriv_add D hD α (unitMultiIndex i) x, multiIndexDeriv_unitMultiIndex D i x]


end

end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.TaylorExpansion
section
namespace FunctorialResolution.EmbeddedResolution.TaylorExpansion

section

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

section
variable (D : Derivation A R R) (n : ℕ) (f g : R)

private theorem iterate_deriv_mul_eq_sum_nsmul_consolidated9 :
    (⇑D)^[n] (f * g) =
      ∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i] g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have key : ∀ i : ℕ,
        ⇑D (n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i] g))
          = n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i + 1] g)
            + n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) := by
      intro i
      rw [map_nsmul, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
        ← Function.iterate_succ_apply' (⇑D) (n - i) g,
        ← Function.iterate_succ_apply' (⇑D) i f,
        mul_comm ((⇑D)^[n - i] g) ((⇑D)^[i + 1] f), smul_add]
    have e3 : ∑ i ∈ Finset.range (n + 1), n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g)
        = ∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) := by
      rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show n < n + 1 by omega), zero_smul,
        add_zero]
    have e1 : ∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i + 1] g)
        = (∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g))
          + f * (⇑D)^[n + 1] g := by
      have inner : ∑ i ∈ Finset.range n,
            n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - (i + 1) + 1] g)
          = ∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have h := Finset.mem_range.mp hi
        have hi' : n - (i + 1) + 1 = n - i := by omega
        rw [hi']
      rw [Finset.sum_range_succ', inner]
      simp only [Nat.choose_zero_right, one_smul, Function.iterate_zero_apply, Nat.sub_zero]
    have e2 : ∑ i ∈ Finset.range (n + 1 + 1),
          (n + 1).choose i • ((⇑D)^[i] f * (⇑D)^[n + 1 - i] g)
        = ((∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g))
            + ∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g))
          + f * (⇑D)^[n + 1] g := by
      have inner2 : ∑ i ∈ Finset.range (n + 1),
            (n + 1).choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n + 1 - (i + 1)] g)
          = (∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g))
            + ∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) := by
        rw [← e3, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hc : (n + 1).choose (i + 1) = n.choose i + n.choose (i + 1) :=
          Nat.choose_succ_succ n i
        have hs : n + 1 - (i + 1) = n - i := by omega
        rw [hc, hs, add_smul]
      rw [Finset.sum_range_succ', inner2]
      simp only [Nat.choose_zero_right, one_smul, Function.iterate_zero_apply, Nat.sub_zero]
    calc (⇑D)^[n + 1] (f * g)
        = ⇑D ((⇑D)^[n] (f * g)) := Function.iterate_succ_apply' _ _ _
      _ = ⇑D (∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i] g)) := by
            rw [ih]
      _ = ∑ i ∈ Finset.range (n + 1), ⇑D (n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i] g)) := by
            rw [map_sum]
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i + 1] g)
            + n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g)) :=
            Finset.sum_congr rfl fun i _ => key i
      _ = (∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i + 1] g))
            + ∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) :=
            Finset.sum_add_distrib
      _ = ∑ i ∈ Finset.range (n + 1 + 1),
            (n + 1).choose i • ((⇑D)^[i] f * (⇑D)^[n + 1 - i] g) := by
            rw [e1, e2]; ring

theorem iterate_deriv_mul :
    (⇑D)^[n] (f * g) =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : R) * ((⇑D)^[i] f * (⇑D)^[n - i] g) := by
  rw [iterate_deriv_mul_eq_sum_nsmul_consolidated9 D n f g]
  exact Finset.sum_congr rfl fun i _ => by rw [nsmul_eq_mul]


end

end

section

variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]

def coeff (σ : R →+* S) (D : Derivation A R R) (i : ℕ) (f : R) : S :=
  algebraMap ℚ S ((i.factorial : ℚ)⁻¹) * σ ((⇑D)^[i] f)

def truncatedSeries (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (f : R) : S :=
  ∑ j ∈ Finset.range N, algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * β ^ j

@[simp]
theorem truncatedSeries_apply (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (f : R) :
    truncatedSeries σ D β N f =
      ∑ j ∈ Finset.range N, algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * β ^ j :=
  rfl

section
variable (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (hN : 1 ≤ N) (f : R)
include hN

theorem truncatedSeries_of_deriv_eq_zero (hf : D f = 0) : truncatedSeries σ D β N f = σ f := by
  have hz : (⇑D) (0 : R) = 0 := by simp
  have key : ∀ k : ℕ, (⇑D)^[k + 1] f = 0 := by
    intro k
    rw [Function.iterate_succ_apply, hf]
    exact Function.iterate_fixed hz k
  rw [truncatedSeries_apply, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb0
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb0
    rw [key k]
    simp
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega : 0 < N)) h

theorem truncatedSeries_sub_mem_span_singleton :
    truncatedSeries σ D β N f - σ f ∈ Ideal.span ({β} : Set S) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos hN).symm⟩
  have key : truncatedSeries σ D β (M + 1) f - σ f =
      ∑ j ∈ Finset.range M,
        algebraMap ℚ S (((j + 1).factorial : ℚ)⁻¹) * σ ((⇑D)^[j + 1] f) * β ^ (j + 1) := by
    rw [truncatedSeries_apply, Finset.sum_range_succ']
    simp
  rw [key]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Ideal.mem_span_singleton]
  exact dvd_mul_of_dvd_right (dvd_pow_self β j.succ_ne_zero) _


end

private theorem factorial_inv_mul_choose_consolidated9 {S' : Type*} [CommRing S'] [Algebra ℚ S'] (j i : ℕ)
    (h : i ≤ j) :
    algebraMap ℚ S' ((j.factorial : ℚ)⁻¹) * (j.choose i : S')
      = algebraMap ℚ S' ((i.factorial : ℚ)⁻¹) * algebraMap ℚ S' (((j - i).factorial : ℚ)⁻¹) := by
  have hj : ((j.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos j).ne'
  have hi : ((i.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos i).ne'
  have hji : (((j - i).factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos (j - i)).ne'
  have h1 : (j.choose i : ℚ) * (i.factorial : ℚ) * ((j - i).factorial : ℚ)
      = (j.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  have key : ((j.factorial : ℚ))⁻¹ * (j.choose i : ℚ)
      = ((i.factorial : ℚ))⁻¹ * (((j - i).factorial : ℚ))⁻¹ := by
    field_simp
    linear_combination h1
  have h2 := congrArg (algebraMap ℚ S') key
  simpa only [map_mul, map_natCast] using h2

private theorem coeff_eq_consolidated9 {A' R' S' : Type*} [CommRing A'] [CommRing R'] [CommRing S']
    [Algebra A' R'] [Algebra ℚ S'] (σ : R' →+* S') (D : Derivation A' R' R') (i : ℕ) (f : R') :
    coeff σ D i f = algebraMap ℚ S' ((i.factorial : ℚ)⁻¹) * σ ((⇑D)^[i] f) := rfl

section
variable (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)

theorem truncatedSeries_mul (f g : R) :
    truncatedSeries σ D β N (f * g) =
      ∑ j ∈ Finset.range N,
        β ^ j * ∑ i ∈ Finset.range (j + 1),
          coeff σ D i f * coeff σ D (j - i) g := by
  rw [truncatedSeries_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iterate_deriv_mul D j f g, map_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have key := factorial_inv_mul_choose_consolidated9 (S' := S) j i hij
  simp only [coeff_eq_consolidated9, map_mul, map_natCast]
  linear_combination (σ ((⇑D)^[i] f) * σ ((⇑D)^[j - i] g) * β ^ j) * key

theorem truncatedSeries_zero :
    truncatedSeries σ D β N 0 = 0 := by
  have hz : (⇑D) (0 : R) = 0 := by simp
  rw [truncatedSeries_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Function.iterate_fixed hz j]
  simp

theorem truncatedSeries_add (f g : R) :
    truncatedSeries σ D β N (f + g) = truncatedSeries σ D β N f + truncatedSeries σ D β N g := by
  have key : ∀ j : ℕ, (⇑D)^[j] (f + g) = (⇑D)^[j] f + (⇑D)^[j] g := by
    intro j
    induction j with
    | zero => simp
    | succ k ih =>
      simp only [Function.iterate_succ_apply', ih, map_add]
  simp only [truncatedSeries_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [key j, map_add]
  ring

theorem truncatedSeries_one (hN : 1 ≤ N) :
    truncatedSeries σ D β N 1 = 1 := by
  have h1 : D (1 : R) = 0 := by simp
  rw [truncatedSeries_of_deriv_eq_zero σ D β N hN 1 h1, map_one]


end

section
variable {T : Type*}

private theorem sum_range_sum_range_succ_eq_sum_sum_Ico_consolidated9 [AddCommMonoid T] (N : ℕ) (h : ℕ → ℕ → T) :
    ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), h i j
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico i N, h i j := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hL : ∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (j + 1), h i j
        = (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), h i j)
          + ∑ i ∈ Finset.range (N + 1), h i N :=
      Finset.sum_range_succ (fun j => ∑ i ∈ Finset.range (j + 1), h i j) N
    have hR1 : ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.Ico i (N + 1), h i j
        = (∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico i (N + 1), h i j)
          + ∑ j ∈ Finset.Ico N (N + 1), h N j :=
      Finset.sum_range_succ (fun i => ∑ j ∈ Finset.Ico i (N + 1), h i j) N
    have hR2 : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico i (N + 1), h i j
        = (∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico i N, h i j)
          + ∑ i ∈ Finset.range N, h i N := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiN : i ≤ N := le_of_lt (Finset.mem_range.mp hi)
      exact Finset.sum_Ico_succ_top hiN (fun j => h i j)
    have hR3 : ∑ j ∈ Finset.Ico N (N + 1), h N j = h N N := by
      rw [Finset.sum_Ico_succ_top (le_refl N) (fun j => h N j), Finset.Ico_self,
        Finset.sum_empty, zero_add]
    have hlast : ∑ i ∈ Finset.range (N + 1), h i N
        = (∑ i ∈ Finset.range N, h i N) + h N N :=
      Finset.sum_range_succ (fun i => h i N) N
    rw [hL, hR1, hR2, hR3, ih, hlast, add_assoc]

private theorem sum_Ico_mul_pow_eq_sum_range_consolidated9 [CommRing T] (a b : ℕ → T) (β : T) (N i : ℕ) :
    ∑ j ∈ Finset.Ico i N, a i * b (j - i) * β ^ j
      = ∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k) := by
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : i + k - i = k := by omega
  simp only [hk]

private theorem sum_convolution_sub_mul_mem_consolidated9 [CommRing T] (β : T) (N : ℕ) (J : Ideal T)
    (hβ : β ^ N ∈ J) (a b : ℕ → T) :
    (∑ j ∈ Finset.range N, β ^ j * ∑ i ∈ Finset.range (j + 1), a i * b (j - i))
      - (∑ j ∈ Finset.range N, a j * β ^ j) * (∑ j ∈ Finset.range N, b j * β ^ j) ∈ J := by
  have hprod : (∑ j ∈ Finset.range N, a j * β ^ j) * (∑ j ∈ Finset.range N, b j * β ^ j)
      = ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N, a i * b k * β ^ (i + k) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have htri : (∑ j ∈ Finset.range N, β ^ j * ∑ i ∈ Finset.range (j + 1), a i * b (j - i))
      = ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k) := by
    have e1 : (∑ j ∈ Finset.range N, β ^ j * ∑ i ∈ Finset.range (j + 1), a i * b (j - i))
        = ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), a i * b (j - i) * β ^ j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    refine e1.trans ((sum_range_sum_range_succ_eq_sum_sum_Ico_consolidated9 N (fun i j => a i * b (j - i) * β ^ j)).trans ?_)
    exact Finset.sum_congr rfl fun i _ => sum_Ico_mul_pow_eq_sum_range_consolidated9 a b β N i
  have hdist : (∑ i ∈ Finset.range N, ∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
      - (∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N, a i * b k * β ^ (i + k))
      = ∑ i ∈ Finset.range N, ((∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
          - ∑ k ∈ Finset.range N, a i * b k * β ^ (i + k)) := by
    refine (eq_sub_of_add_eq ?_).symm
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hprod, htri, hdist]
  refine Ideal.sum_mem _ fun i hi => ?_
  have hiN : i < N := Finset.mem_range.mp hi
  have hsplit : ∑ k ∈ Finset.range N, a i * b k * β ^ (i + k)
      = (∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
        + ∑ k ∈ Finset.Ico (N - i) N, a i * b k * β ^ (i + k) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le (N - i)) (Nat.sub_le N i)).symm
  rw [hsplit]
  have hre : (∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
      - ((∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
        + ∑ k ∈ Finset.Ico (N - i) N, a i * b k * β ^ (i + k))
      = -(∑ k ∈ Finset.Ico (N - i) N, a i * b k * β ^ (i + k)) := by ring
  rw [hre]
  refine neg_mem (Ideal.sum_mem _ fun k hk => ?_)
  have hk1 : N - i ≤ k := (Finset.mem_Ico.mp hk).1
  have hpow : β ^ (i + k) ∈ J := by
    have he : i + k = N + (i + k - N) := by omega
    rw [he, pow_add]
    exact Ideal.mul_mem_right _ _ hβ
  exact Ideal.mul_mem_left _ _ hpow


end

section
variable (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (J : Ideal S)

theorem truncatedSeries_mul_sub_mem (hβ : β ^ N ∈ J) (f g : R) :
    truncatedSeries σ D β N (f * g) - truncatedSeries σ D β N f * truncatedSeries σ D β N g ∈ J := by
  have hf : truncatedSeries σ D β N f
      = ∑ j ∈ Finset.range N, coeff σ D j f * β ^ j := rfl
  have hg : truncatedSeries σ D β N g
      = ∑ j ∈ Finset.range N, coeff σ D j g * β ^ j := rfl
  rw [truncatedSeries_mul σ D β N f g, hf, hg]
  exact sum_convolution_sub_mul_mem_consolidated9 β N J hβ (fun i => coeff σ D i f)
    (fun i => coeff σ D i g)

private theorem mk_truncatedSeries_one_consolidated9 (hN : 1 ≤ N) :
    Ideal.Quotient.mk J (truncatedSeries σ D β N 1) = 1 := by
  have h1 : D 1 = 0 := by simp
  rw [truncatedSeries_of_deriv_eq_zero σ D β N hN 1 h1]
  simp

private theorem mk_truncatedSeries_mul_consolidated9 (hβ : β ^ N ∈ J) (f g : R) :
    Ideal.Quotient.mk J (truncatedSeries σ D β N (f * g)) =
      Ideal.Quotient.mk J (truncatedSeries σ D β N f) *
        Ideal.Quotient.mk J (truncatedSeries σ D β N g) := by
  have h : truncatedSeries σ D β N (f * g)
      - truncatedSeries σ D β N f * truncatedSeries σ D β N g ∈ J :=
    truncatedSeries_mul_sub_mem σ D β N J hβ f g
  have h2 : Ideal.Quotient.mk J (truncatedSeries σ D β N (f * g))
      = Ideal.Quotient.mk J (truncatedSeries σ D β N f * truncatedSeries σ D β N g) :=
    Ideal.Quotient.eq.mpr h
  rw [h2, map_mul]

private theorem mk_truncatedSeries_zero_consolidated9 :
    Ideal.Quotient.mk J (truncatedSeries σ D β N 0) = 0 := by
  rw [truncatedSeries_zero, map_zero]

private theorem mk_truncatedSeries_add_consolidated9 (f g : R) :
    Ideal.Quotient.mk J (truncatedSeries σ D β N (f + g)) =
      Ideal.Quotient.mk J (truncatedSeries σ D β N f) +
        Ideal.Quotient.mk J (truncatedSeries σ D β N g) := by
  rw [truncatedSeries_add, map_add]


end

def truncatedSeriesRingHom (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (J : Ideal S)
    (hN : 1 ≤ N) (hβ : β ^ N ∈ J) : R →+* S ⧸ J :=
  { toFun := fun f => Ideal.Quotient.mk J (truncatedSeries σ D β N f)
    map_one' := mk_truncatedSeries_one_consolidated9 σ D β N J hN
    map_mul' := mk_truncatedSeries_mul_consolidated9 σ D β N J hβ
    map_zero' := mk_truncatedSeries_zero_consolidated9 σ D β N J
    map_add' := mk_truncatedSeries_add_consolidated9 σ D β N J }

@[simp]
theorem truncatedSeriesRingHom_apply (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (J : Ideal S)
    (hN : 1 ≤ N) (hβ : β ^ N ∈ J) (f : R) :
    truncatedSeriesRingHom σ D β N J hN hβ f = Ideal.Quotient.mk J (truncatedSeries σ D β N f) :=
  rfl

end

end FunctorialResolution.EmbeddedResolution.TaylorExpansion
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealEtaleBaseChange
section
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

private def derivationCompAlgebraMap_consolidated40 (k : Type*) [CommRing k] (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T] (D : Derivation k T T) :
    Derivation k S T :=
  Derivation.mk' (D.toLinearMap.comp (IsScalarTower.toAlgHom k S T).toLinearMap) (by
    intro a b
    show D (algebraMap S T (a * b)) = a • D (algebraMap S T b) + b • D (algebraMap S T a)
    rw [map_mul, D.leibniz, smul_eq_mul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def])

private theorem derivation_comp_algebraMap_apply_consolidated40 (k : Type*) [CommRing k] (S : Type*) [CommRing S]
    (T : Type*) [CommRing T] [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (D : Derivation k T T) (s : S) :
    derivationCompAlgebraMap_consolidated40 k S T D s = D (algebraMap S T s) := rfl

private def algebraMapCompDerivation_consolidated40 (k : Type*) [CommRing k] (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T] (D : Derivation k S S) :
    Derivation k S T :=
  Derivation.mk' ((IsScalarTower.toAlgHom k S T).toLinearMap.comp D.toLinearMap) (by
    intro a b
    show algebraMap S T (D (a * b)) = a • algebraMap S T (D b) + b • algebraMap S T (D a)
    rw [D.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, Algebra.smul_def,
      Algebra.smul_def])

section
variable (k : Type*) [CommRing k]

private theorem algebraMap_comp_derivation_apply_consolidated40 (S : Type*) [CommRing S]
    (T : Type*) [CommRing T] [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (D : Derivation k S S) (s : S) :
    algebraMapCompDerivation_consolidated40 k S T D s = algebraMap S T (D s) := rfl

theorem derivation_ext_of_coord (ι : Type*) (S : Type*) [CommRing S]
    [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (M : Type*) [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    (D₁ D₂ : Derivation k S M)
    (h : ∀ i : ι, D₁ (coord k ι S i) = D₂ (coord k ι S i)) : D₁ = D₂ := by
  have key : D₁.liftKaehlerDifferential = D₂.liftKaehlerDifferential := by
    refine (basisKaehler k ι S).ext ?_
    intro i
    rw [basisKaehler_apply, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    exact h i
  refine Derivation.ext fun x => ?_
  rw [← Derivation.liftKaehlerDifferential_comp_D D₁ x,
    ← Derivation.liftKaehlerDifferential_comp_D D₂ x, key]


end

section
variable (k : Type*) [CommRing k] (ι : Type*) (κ : Type*)

theorem partialDeriv_inr_algebraMap (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (j : κ) (s : S) :
    partialDeriv k (ι ⊕ κ) T (Sum.inr j) (algebraMap S T s) = 0 := by
  have key : derivationCompAlgebraMap_consolidated40 k S T (partialDeriv k (ι ⊕ κ) T (Sum.inr j)) = 0 := by
    refine derivation_ext_of_coord k ι S T _ _ ?_
    intro i
    rw [derivation_comp_algebraMap_apply_consolidated40, hcoord i,
      partialDeriv_coord_of_ne k (ι ⊕ κ) T (Sum.inr j) (Sum.inl i) (by simp)]
    have h0 : ((0 : Derivation k S T)) (coord k ι S i) = 0 := rfl
    rw [h0]
  have h2 := DFunLike.congr_fun key s
  rw [derivation_comp_algebraMap_apply_consolidated40] at h2
  have h0 : ((0 : Derivation k S T)) s = 0 := rfl
  rw [h0] at h2
  exact h2

theorem partialDeriv_inl_algebraMap [DecidableEq ι] [DecidableEq κ]
    (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (i : ι) (s : S) :
    partialDeriv k (ι ⊕ κ) T (Sum.inl i) (algebraMap S T s)
      = algebraMap S T (partialDeriv k ι S i s) := by
  have key : derivationCompAlgebraMap_consolidated40 k S T (partialDeriv k (ι ⊕ κ) T (Sum.inl i))
      = algebraMapCompDerivation_consolidated40 k S T (partialDeriv k ι S i) := by
    refine derivation_ext_of_coord k ι S T _ _ ?_
    intro j
    rw [derivation_comp_algebraMap_apply_consolidated40, algebraMap_comp_derivation_apply_consolidated40, hcoord j]
    by_cases hij : i = j
    · subst hij
      rw [partialDeriv_coord_self, partialDeriv_coord_self, map_one]
    · rw [partialDeriv_coord_of_ne k (ι ⊕ κ) T (Sum.inl i) (Sum.inl j) (by simpa using hij),
        partialDeriv_coord_of_ne k ι S i j hij, map_zero]
  have h2 := DFunLike.congr_fun key s
  rw [derivation_comp_algebraMap_apply_consolidated40, algebraMap_comp_derivation_apply_consolidated40] at h2
  exact h2

theorem map_derivIdeal_sum [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (J : Ideal S) :
    Ideal.map (algebraMap S T) (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S T) J) := by
  have key1 : ∀ (D : Derivation k S S) (y : S), y ∈ J →
      algebraMap S T (D y) ∈ derivIdeal k (Ideal.map (algebraMap S T) J) := by
    intro D y hy
    have hsp : D ∈ Submodule.span S (Set.range (partialDeriv k ι S)) := by
      rw [span_range_partialDeriv]
      exact Submodule.mem_top
    induction hsp using Submodule.span_induction with
    | mem D hD =>
        obtain ⟨i, rfl⟩ := hD
        rw [← partialDeriv_inl_algebraMap k ι κ S T hcoord i y]
        exact derivation_apply_mem_derivIdeal k _ _ (Ideal.mem_map_of_mem _ hy)
    | zero =>
        have h0 : ((0 : Derivation k S S)) y = 0 := rfl
        rw [h0, map_zero]
        exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
        have h0 : (a + b) y = a y + b y := rfl
        rw [h0, map_add]
        exact Ideal.add_mem _ ha hb
    | smul c a _ ha =>
        have h0 : (c • a) y = c * a y := rfl
        rw [h0, map_mul]
        exact Ideal.mul_mem_left _ _ ha
  have key2 : ∀ (D' : Derivation k T T) (y : S), y ∈ J →
      D' (algebraMap S T y) ∈ Ideal.map (algebraMap S T) (derivIdeal k J) := by
    intro D' y hy
    have hsp : D' ∈ Submodule.span T (Set.range (partialDeriv k (ι ⊕ κ) T)) := by
      rw [span_range_partialDeriv]
      exact Submodule.mem_top
    induction hsp using Submodule.span_induction with
    | mem D hD =>
        obtain ⟨x, rfl⟩ := hD
        cases x with
        | inl i =>
            rw [partialDeriv_inl_algebraMap k ι κ S T hcoord i y]
            exact Ideal.mem_map_of_mem _
              (derivation_apply_mem_derivIdeal k J (partialDeriv k ι S i) hy)
        | inr j =>
            rw [partialDeriv_inr_algebraMap k ι κ S T hcoord j y]
            exact Submodule.zero_mem _
    | zero =>
        have h0 : ((0 : Derivation k T T)) (algebraMap S T y) = 0 := rfl
        rw [h0]
        exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
        have h0 : (a + b) (algebraMap S T y)
            = a (algebraMap S T y) + b (algebraMap S T y) := rfl
        rw [h0]
        exact Ideal.add_mem _ ha hb
    | smul c a _ ha =>
        have h0 : (c • a) (algebraMap S T y) = c * a (algebraMap S T y) := rfl
        rw [h0]
        exact Ideal.mul_mem_left _ _ ha
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap, derivIdeal_le_iff]
    refine ⟨fun y hy => Ideal.mem_comap.mpr (le_derivIdeal k _ (Ideal.mem_map_of_mem _ hy)), ?_⟩
    intro D y hy
    exact Ideal.mem_comap.mpr (key1 D y hy)
  · rw [derivIdeal_le_iff]
    refine ⟨Ideal.map_mono (le_derivIdeal k J), ?_⟩
    intro D' z hz
    have hspan : Ideal.map (algebraMap S T) J
        = Ideal.span ((algebraMap S T) '' (J : Set S)) := by
      rw [← Ideal.map_span, Ideal.span_eq]
    rw [hspan] at hz
    refine derivation_apply_mem_of_mem_span D' ?_ ?_ hz
    · rw [← hspan]
      exact Ideal.map_mono (le_derivIdeal k J)
    · rintro g ⟨y, hy, rfl⟩
      exact key2 D' y hy


end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end
end
