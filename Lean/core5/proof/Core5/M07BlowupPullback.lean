import Mathlib
import Core5.M06MarkedSequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicGeometry
universe u
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothLocalChart
section


section

structure SmoothLocalChart {k : Type u} [Field k] [CharZero k] {Y V : Scheme.{u}}
    {pY : Y ⟶ Spec (CommRingCat.of k)} {pV : V ⟶ Spec (CommRingCat.of k)}
    (G : EmbeddingDatum k Y pY) (H : EmbeddingDatum k V pV) (u : V ⟶ Y) (y : ↥V) where
  func : Γ(H.ambient, ⊤)
  mem_domain : y ∈ (H.emb ⁻¹ᵁ H.ambient.basicOpen func)
  ambient : Scheme.{u}
  ambientStruct : ambient ⟶ Spec (CommRingCat.of k)
  isAffine_ambient : IsAffine ambient
  smooth_ambientStruct : Smooth ambientStruct
  locallyOfFiniteType_ambientStruct : LocallyOfFiniteType ambientStruct
  quasiCompact_ambientStruct : QuasiCompact ambientStruct
  toAmbient : ambient ⟶ G.ambient
  smooth_toAmbient : Smooth toAmbient
  comp_eq : toAmbient ≫ G.ambientStruct = ambientStruct
  imm : (H.emb ⁻¹ᵁ H.ambient.basicOpen func).toScheme ⟶ ambient
  isClosedImmersion_imm : IsClosedImmersion imm
  isPullback :
    CategoryTheory.IsPullback imm ((H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι ≫ u) toAmbient
      G.emb

namespace SmoothLocalChart

variable {k : Type u} [Field k] [CharZero k] {Y V : Scheme.{u}}
  {pY : Y ⟶ Spec (CommRingCat.of k)} {pV : V ⟶ Spec (CommRingCat.of k)}
  {G : EmbeddingDatum k Y pY} {H : EmbeddingDatum k V pV} {u : V ⟶ Y} {y : ↥V}

abbrev chartDomain (C : SmoothLocalChart G H u y) : V.Opens :=
  H.emb ⁻¹ᵁ H.ambient.basicOpen C.func

instance instIsAffineAmbient (C : SmoothLocalChart G H u y) :
    IsAffine C.ambient := C.isAffine_ambient

instance instSmoothAmbientStruct (C : SmoothLocalChart G H u y) :
    Smooth C.ambientStruct := C.smooth_ambientStruct

instance instLocallyOfFiniteTypeAmbientStruct (C : SmoothLocalChart G H u y) :
    LocallyOfFiniteType C.ambientStruct :=
  C.locallyOfFiniteType_ambientStruct

instance instQuasiCompactAmbientStruct (C : SmoothLocalChart G H u y) :
    QuasiCompact C.ambientStruct := C.quasiCompact_ambientStruct

instance instSmoothToAmbient (C : SmoothLocalChart G H u y) :
    Smooth C.toAmbient := C.smooth_toAmbient

instance instIsClosedImmersionImm (C : SmoothLocalChart G H u y) :
    IsClosedImmersion C.imm := C.isClosedImmersion_imm

theorem isAffineOpen_chartDomain [IsAffine V]
    (C : SmoothLocalChart G H u y) :
    IsAffineOpen C.chartDomain := by
  show IsAffineOpen (H.emb ⁻¹ᵁ H.ambient.basicOpen C.func)
  have h : (H.emb ⁻¹ᵁ H.ambient.basicOpen C.func) = V.basicOpen (H.emb.app ⊤ C.func) :=
    Scheme.preimage_basicOpen H.emb C.func
  rw [h]
  exact (isAffineOpen_top V).basicOpen _

theorem isPullback_morphismRestrict_basicOpen (C : SmoothLocalChart G H u y) :
    CategoryTheory.IsPullback
      (AlgebraicGeometry.morphismRestrict H.emb (H.ambient.basicOpen C.func))
      C.chartDomain.ι (H.ambient.basicOpen C.func).ι H.emb :=
  AlgebraicGeometry.isPullback_morphismRestrict H.emb (H.ambient.basicOpen C.func)

end SmoothLocalChart


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphChartSmooth
section

open TopologicalSpace

section

def polynomialOfSection (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (j : Fin q) : MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k :=
  (mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))).symm (F j)

theorem mvPolynomialEquivGlobalSections_polynomialOfSection (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (j : Fin q) :
    mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n)) (polynomialOfSection k M n q F j) = F j :=
  (mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))).apply_symm_apply (F j)

def sumVariableMap (M n q : ℕ) (s : Fin q → Fin n) :
    ULift.{u, 0} (Fin M ⊕ Fin q) → ULift.{u, 0} (Fin M ⊕ Fin n) :=
  fun i =>
    ULift.up (Sum.elim (fun a : Fin M => Sum.inl a) (fun j : Fin q => Sum.inr (s j)) i.down)

theorem sumVariableMap_injective (M n q : ℕ) (s : Fin q → Fin n) (hs : Function.Injective s) :
    Function.Injective (sumVariableMap.{u} M n q s) := by
  rintro ⟨x⟩ ⟨y⟩ h
  have h' : Sum.elim (fun a : Fin M => Sum.inl a) (fun j : Fin q => Sum.inr (s j)) x
      = Sum.elim (fun a : Fin M => Sum.inl a) (fun j : Fin q => Sum.inr (s j)) y :=
    congrArg ULift.down h
  have hxy : x = y := by
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        have hab : a = b := by simpa using h'
        exact congrArg Sum.inl hab
      | inr j => simp at h'
    | inr i =>
      cases y with
      | inl b => simp at h'
      | inr j =>
        simp only [Sum.elim_inr, Sum.inr.injEq] at h'
        exact congrArg Sum.inr (hs h')
  exact congrArg ULift.up hxy

def jacobianMatrixOfSections (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    Matrix (Fin q) (Fin q) (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k) :=
  Matrix.of fun i j =>
    (MvPolynomial.pderiv (ULift.up (Sum.inr (s i)) : ULift.{u, 0} (Fin M ⊕ Fin n)))
      (polynomialOfSection k M n q F j)

theorem jacobianMatrixOfSections_apply (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) (i j : Fin q) :
    jacobianMatrixOfSections k M n q F s i j =
      (MvPolynomial.pderiv (ULift.up (Sum.inr (s i)) : ULift.{u, 0} (Fin M ⊕ Fin n)))
        (polynomialOfSection k M n q F j) := rfl

def graphCoordinates (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤))) :
    ULift.{u, 0} (Fin M ⊕ Fin q) → MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k :=
  fun i =>
    Sum.elim
      (fun a : Fin M => MvPolynomial.X (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin n)))
      (fun j : Fin q => polynomialOfSection k M n q F j) i.down

section
variable (k : Type u) [Field k] (M n q : ℕ) (F : Fin q → ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))

theorem graphCoordinates_inl (a : Fin M) :
    graphCoordinates k M n q F (ULift.up (Sum.inl a)) =
      MvPolynomial.X (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin n)) := rfl

theorem graphCoordinates_inr (j : Fin q) :
    graphCoordinates k M n q F (ULift.up (Sum.inr j)) = polynomialOfSection k M n q F j := rfl

private theorem det_graphJacobianMinorMatrix_eq_det_jacobianMatrix_consolidated171 (s : Fin q → Fin n) :
    (graphJacobianMinorMatrix (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)).det =
      (jacobianMatrixOfSections k M n q F s).det := by
  have hup : ∀ x y : Fin M ⊕ Fin n,
      (ULift.up x : ULift.{u, 0} (Fin M ⊕ Fin n)) = ULift.up y → x = y :=
    fun _ _ h => congrArg ULift.down h
  have hXne : ∀ i j : ULift.{u, 0} (Fin M ⊕ Fin n), i ≠ j →
      (MvPolynomial.pderiv i)
          (MvPolynomial.X j : MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k) = 0 := by
    intro i j h
    simp [MvPolynomial.pderiv_X, Ne.symm h]
  have key :
      (graphJacobianMinorMatrix (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)).submatrix
          ⇑(Equiv.ulift.symm : (Fin M ⊕ Fin q) ≃ ULift.{u, 0} (Fin M ⊕ Fin q))
          ⇑(Equiv.ulift.symm : (Fin M ⊕ Fin q) ≃ ULift.{u, 0} (Fin M ⊕ Fin q)) =
        Matrix.fromBlocks
          (1 : Matrix (Fin M) (Fin M) (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k))
          (Matrix.of fun (a : Fin M) (j : Fin q) =>
            (MvPolynomial.pderiv (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin n)))
              (polynomialOfSection k M n q F j))
          0 (jacobianMatrixOfSections k M n q F s) := by
    apply Matrix.ext
    intro x y
    simp only [Matrix.submatrix_apply, graphJacobianMinorMatrix_apply]
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        show (MvPolynomial.pderiv (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin n)))
              (MvPolynomial.X (ULift.up (Sum.inl b) : ULift.{u, 0} (Fin M ⊕ Fin n))) =
            (1 : Matrix (Fin M) (Fin M) (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k)) a b
        by_cases h : a = b
        · subst h
          rw [MvPolynomial.pderiv_X_self, Matrix.one_apply_eq]
        · rw [Matrix.one_apply_ne h]
          exact hXne _ _ fun hc => h (Sum.inl_injective (hup _ _ hc))
      | inr j => rfl
    | inr i =>
      cases y with
      | inl b =>
        show (MvPolynomial.pderiv (ULift.up (Sum.inr (s i)) : ULift.{u, 0} (Fin M ⊕ Fin n)))
              (MvPolynomial.X (ULift.up (Sum.inl b) : ULift.{u, 0} (Fin M ⊕ Fin n))) = 0
        refine hXne _ _ ?_
        intro hc
        have hc' := hup _ _ hc
        simp at hc'
      | inr j => rfl
  have hdet := Matrix.det_submatrix_equiv_self
      (Equiv.ulift.symm : (Fin M ⊕ Fin q) ≃ ULift.{u, 0} (Fin M ⊕ Fin q))
      (graphJacobianMinorMatrix (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))
  rw [key, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul] at hdet
  exact hdet.symm

theorem graphJacobianMinorDet_graphCoordinates (s : Fin q → Fin n) :
    graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s) =
      graphAlgebraEquiv (graphCoordinates k M n q F) (jacobianMatrixOfSections k M n q F s).det := by
  have h := det_graphJacobianMinorMatrix_eq_det_jacobianMatrix_consolidated171 k M n q F s
  show graphAlgebraEquiv (graphCoordinates k M n q F)
      (graphJacobianMinorMatrix (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)).det =
    graphAlgebraEquiv (graphCoordinates k M n q F) (jacobianMatrixOfSections k M n q F s).det
  rw [h]


end

def jacobianDetSection (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)) :=
  mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n)) (jacobianMatrixOfSections k M n q F s).det

def specGraphAwayToSpecGraphAlgebra (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    Spec (CommRingCat.of (GraphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))) ⟶
      Spec (CommRingCat.of (GraphAlgebra (graphCoordinates k M n q F))) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (GraphAlgebra (graphCoordinates k M n q F))
      (GraphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))))

theorem isOpenImmersion_specGraphAwayToSpecGraphAlgebra (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    IsOpenImmersion (specGraphAwayToSpecGraphAlgebra k M n q F s) := by
  unfold specGraphAwayToSpecGraphAlgebra
  infer_instance

instance instIsOpenImmersionGraphAwaySpecHom (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    IsOpenImmersion (specGraphAwayToSpecGraphAlgebra k M n q F s) :=
  isOpenImmersion_specGraphAwayToSpecGraphAlgebra k M n q F s

def basicOpenToSpecGraphAlgebra (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
        (jacobianDetSection k M n q F s)).toScheme ⟶
      Spec (CommRingCat.of (GraphAlgebra (graphCoordinates k M n q F))) :=
  ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
      (jacobianDetSection k M n q F s)).ι ≫
    (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ≫
      Spec.map (CommRingCat.ofHom
        ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom))

private def specIsoOfRingEquiv_consolidated171 {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) :
    Spec (CommRingCat.of B) ≅ Spec (CommRingCat.of A) :=
  Scheme.Spec.mapIso e.toCommRingCatIso.op

private theorem isIso_spec_map_ringEquiv_consolidated171 {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) := by
  refine ⟨(specIsoOfRingEquiv_consolidated171 e).inv, ?_, ?_⟩
  · exact (specIsoOfRingEquiv_consolidated171 e).hom_inv_id
  · exact (specIsoOfRingEquiv_consolidated171 e).inv_hom_id

theorem isOpenImmersion_basicOpenToSpecGraphAlgebra (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    IsOpenImmersion (basicOpenToSpecGraphAlgebra k M n q F s) := by
  have : IsIso (Spec.map (CommRingCat.ofHom
      ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom))) :=
    isIso_spec_map_ringEquiv_consolidated171 ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv)
  unfold basicOpenToSpecGraphAlgebra
  infer_instance

instance instIsOpenImmersionGraphChartHom (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    IsOpenImmersion (basicOpenToSpecGraphAlgebra k M n q F s) :=
  isOpenImmersion_basicOpenToSpecGraphAlgebra k M n q F s

section
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

private theorem base_comp_apply_consolidated171 (x : ↥X) :
    ⇑(f ≫ g).base x = ⇑g.base (⇑f.base x) := rfl

private theorem range_base_comp_consolidated171 :
    Set.range ⇑(f ≫ g).base = ⇑g.base '' Set.range ⇑f.base := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⇑f.base x, ⟨x, rfl⟩, (base_comp_apply_consolidated171 f g x).symm⟩
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, base_comp_apply_consolidated171 f g x⟩

private theorem image_base_comp_consolidated171 (S : Set ↥X) :
    ⇑(f ≫ g).base '' S = ⇑g.base '' (⇑f.base '' S) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⇑f.base x, ⟨x, hx, rfl⟩, (base_comp_apply_consolidated171 f g x).symm⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, base_comp_apply_consolidated171 f g x⟩


end

section
variable {X Y : Scheme.{u}} (e : X ≅ Y)

private theorem image_hom_preimage_eq_consolidated171 (U : Y.Opens) :
    ⇑e.hom.base '' ((e.hom ⁻¹ᵁ U : X.Opens) : Set ↥X) = (U : Set ↥Y) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    refine ⟨⇑e.inv.base y, ?_, Scheme.inv_hom_apply e y⟩
    show ⇑e.hom.base (⇑e.inv.base y) ∈ (U : Set ↥Y)
    rw [Scheme.inv_hom_apply e y]
    exact hy

private theorem image_hom_eq_preimage_inv_consolidated171 (U : X.Opens) :
    ⇑e.hom.base '' ((U : X.Opens) : Set ↥X) = ((e.inv ⁻¹ᵁ U : Y.Opens) : Set ↥Y) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show ⇑e.inv.base (⇑e.hom.base x) ∈ ((U : X.Opens) : Set ↥X)
    rw [Scheme.hom_inv_apply e x]
    exact hx
  · intro hy
    exact ⟨⇑e.inv.base y, hy, Scheme.inv_hom_apply e y⟩


end

private theorem image_basicOpen_spec_map_ringEquiv_consolidated171 {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (a : A) :
    ⇑(Spec.map (CommRingCat.ofHom e.toRingHom)).base ''
        (PrimeSpectrum.basicOpen (e a) : Set (PrimeSpectrum B))
      = (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
  have h2 : (PrimeSpectrum.basicOpen (e a) : Opens (PrimeSpectrum B))
      = (Spec (CommRingCat.of B)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (e a)) := by
    have h2' : (Spec (CommRingCat.of B)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (e a))
        = (PrimeSpectrum.basicOpen (e a) : Opens (PrimeSpectrum B)) :=
      basicOpen_eq_of_affine _
    exact h2'.symm
  have h3 : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ⁻¹ᵁ
        ((Spec (CommRingCat.of B)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (e a)))
      = (Spec (CommRingCat.of A)).basicOpen
          ((Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom e.symm.toRingHom)))
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (e a))) :=
    Scheme.preimage_basicOpen (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) _
  have h4 : (Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom e.symm.toRingHom)))
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (e a))
      = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ((e.symm.toRingHom) (e a)) :=
    (RingHom.congr_fun (congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom e.symm.toRingHom))) (e a)).symm
  have h5 : (e.symm.toRingHom) (e a) = a := by simp
  have h6 : (Spec (CommRingCat.of A)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)
      = (PrimeSpectrum.basicOpen a : Opens (PrimeSpectrum A)) :=
    basicOpen_eq_of_affine _
  have hop : (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen (e a) : Opens (PrimeSpectrum B)))
      = (PrimeSpectrum.basicOpen a : Opens (PrimeSpectrum A)) := by
    rw [h2, h3, h4, h5]
    exact h6
  have h1 : ⇑(Spec.map (CommRingCat.ofHom e.toRingHom)).base ''
        (PrimeSpectrum.basicOpen (e a) : Set (PrimeSpectrum B))
      = ((Spec.map (CommRingCat.ofHom e.symm.toRingHom) ⁻¹ᵁ
          (PrimeSpectrum.basicOpen (e a) : Opens (PrimeSpectrum B))) :
          Set ↥(Spec (CommRingCat.of A))) :=
    image_hom_eq_preimage_inv_consolidated171 (specIsoOfRingEquiv_consolidated171 e) (PrimeSpectrum.basicOpen (e a))
  exact h1.trans (congrArg (fun U : (Spec (CommRingCat.of A)).Opens =>
    (U : Set ↥(Spec (CommRingCat.of A)))) hop)

theorem range_specGraphAwayToSpecGraphAlgebra_eq (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    Set.range ⇑(specGraphAwayToSpecGraphAlgebra k M n q F s).base =
      Set.range ⇑(basicOpenToSpecGraphAlgebra k M n q F s).base := by
  have hL : Set.range ⇑(specGraphAwayToSpecGraphAlgebra k M n q F s).base =
      (PrimeSpectrum.basicOpen
          (graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)) :
        Set (PrimeSpectrum (GraphAlgebra (graphCoordinates k M n q F)))) :=
    range_specMap_algebraMap_graphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)
  have hR1 : Set.range ⇑(basicOpenToSpecGraphAlgebra k M n q F s).base
      = ⇑((affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ≫
            Spec.map (CommRingCat.ofHom
              ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom))).base ''
          Set.range ⇑(((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s)).ι).base :=
    range_base_comp_consolidated171
      (((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
        (jacobianDetSection k M n q F s)).ι)
      ((affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ≫
        Spec.map (CommRingCat.ofHom
          ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom)))
  have hD : Set.range ⇑(((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
        (jacobianDetSection k M n q F s)).ι).base
      = (((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s) :
          (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens) :
          Set ↥(affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n)))) :=
    Scheme.Opens.range_ι _
  have hDopen : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
        (jacobianDetSection k M n q F s)
      = (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ⁻¹ᵁ
          (PrimeSpectrum.basicOpen (jacobianMatrixOfSections k M n q F s).det) :=
    mvPolynomialEquivGlobalSections_basicOpen_primeSpectrum k (ULift.{u, 0} (Fin M ⊕ Fin n))
      (jacobianMatrixOfSections k M n q F s).det
  have himg1 : ⇑(affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom.base ''
        (((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s) :
          (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens) :
          Set ↥(affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))))
      = (PrimeSpectrum.basicOpen (jacobianMatrixOfSections k M n q F s).det :
          Set (PrimeSpectrum (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k))) := by
    rw [hDopen]
    exact image_hom_preimage_eq_consolidated171 (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n)))
      (PrimeSpectrum.basicOpen (jacobianMatrixOfSections k M n q F s).det)
  have hdet : (jacobianMatrixOfSections k M n q F s).det
      = ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv)
          (graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)) := by
    rw [graphJacobianMinorDet_graphCoordinates]
    simp
  have himg2 : ⇑(Spec.map (CommRingCat.ofHom
        ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom))).base ''
        (PrimeSpectrum.basicOpen (jacobianMatrixOfSections k M n q F s).det :
          Set (PrimeSpectrum (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k)))
      = (PrimeSpectrum.basicOpen
            (graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)) :
          Set (PrimeSpectrum (GraphAlgebra (graphCoordinates k M n q F)))) := by
    rw [hdet]
    exact image_basicOpen_spec_map_ringEquiv_consolidated171 ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv)
      (graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))
  have hrange : Set.range ⇑(basicOpenToSpecGraphAlgebra k M n q F s).base
      = (PrimeSpectrum.basicOpen
            (graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)) :
          Set (PrimeSpectrum (GraphAlgebra (graphCoordinates k M n q F)))) := by
    rw [hR1, hD, image_base_comp_consolidated171, himg1]
    exact himg2
  exact hL.trans hrange.symm

def specGraphAwayIsoBasicOpen (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    Spec (CommRingCat.of (GraphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))) ≅
      ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
        (jacobianDetSection k M n q F s)).toScheme :=
  IsOpenImmersion.isoOfRangeEq (specGraphAwayToSpecGraphAlgebra k M n q F s) (basicOpenToSpecGraphAlgebra k M n q F s)
    (range_specGraphAwayToSpecGraphAlgebra_eq k M n q F s)

theorem specGraphAwayIsoBasicOpen_inv_comp (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    (specGraphAwayIsoBasicOpen k M n q F s).inv ≫ specGraphAwayToSpecGraphAlgebra k M n q F s =
      basicOpenToSpecGraphAlgebra k M n q F s := by
  exact IsOpenImmersion.isoOfRangeEq_inv_fac (specGraphAwayToSpecGraphAlgebra k M n q F s)
    (basicOpenToSpecGraphAlgebra k M n q F s) (range_specGraphAwayToSpecGraphAlgebra_eq k M n q F s)

def specGraphAwayToAffineSpace (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    Spec (CommRingCat.of (GraphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))) ⟶
      Spec (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
      (GraphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))))

section
variable (k : Type u) [Field k] (M n q : ℕ) (F : Fin q → ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))

private theorem graphAlgebraEquiv_symm_comp_algebraMap_X_consolidated171 (i : ULift.{u, 0} (Fin M ⊕ Fin q)) :
    (((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom).comp
        (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
          (GraphAlgebra (graphCoordinates k M n q F)))) (MvPolynomial.X i)
      = graphCoordinates k M n q F i := by
  simp [algebraMap_graphAlgebra]

private theorem graphAlgebraEquiv_symm_comp_algebraMap_comp_C_consolidated171 :
    ((((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom).comp
        (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
          (GraphAlgebra (graphCoordinates k M n q F)))).comp
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k))
      = (MvPolynomial.C : k →+* MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k) := by
  ext c
  simp [algebraMap_graphAlgebra, MvPolynomial.algebraMap_eq]


end

private theorem appTop_comp_apply_consolidated171 {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (x : ↑(Z.presheaf.obj (Opposite.op ⊤))) :
    (Scheme.Hom.appTop (a ≫ b)) x
      = (Scheme.Hom.appTop a) ((Scheme.Hom.appTop b) x) := rfl

section
variable (k : Type u) [Field k] (M n q : ℕ) (F : Fin q → ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤))) (s : Fin q → Fin n)

theorem graphMorphismToAffineSpace_basicOpen_jacobianDetSection_eq :
    graphMorphismToAffineSpace k M n q F
        ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
          (jacobianDetSection k M n q F s)) =
      (specGraphAwayIsoBasicOpen k M n q F s).inv ≫ specGraphAwayToAffineSpace k M n q F s ≫
        (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin q))).inv := by
  have hgc : basicOpenToSpecGraphAlgebra k M n q F s =
      ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
          (jacobianDetSection k M n q F s)).ι ≫
        (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ≫
          Spec.map (CommRingCat.ofHom
            ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom)) := rfl
  have h1 : specGraphAwayToAffineSpace k M n q F s =
      specGraphAwayToSpecGraphAlgebra k M n q F s ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
            (GraphAlgebra (graphCoordinates k M n q F)))) :=
    specMap_algebraMap_graphAlgebraAway_eq_comp (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)
  have hre : ∀ {Z : Scheme.{u}}
      (g : Spec (CommRingCat.of (GraphAlgebra (graphCoordinates k M n q F))) ⟶ Z),
      (specGraphAwayIsoBasicOpen k M n q F s).inv ≫ specGraphAwayToSpecGraphAlgebra k M n q F s ≫ g
        = basicOpenToSpecGraphAlgebra k M n q F s ≫ g := by
    intro Z g
    rw [← Category.assoc, specGraphAwayIsoBasicOpen_inv_comp]
  have key : (specGraphAwayIsoBasicOpen k M n q F s).inv ≫ specGraphAwayToAffineSpace k M n q F s ≫
        (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin q))).inv
      = ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s)).ι ≫
          (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ≫
            Spec.map (CommRingCat.ofHom
              (((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom).comp
                (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
                  (GraphAlgebra (graphCoordinates k M n q F))))) ≫
              (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin q))).inv := by
    rw [h1, Category.assoc, hre, hgc, CommRingCat.ofHom_comp, Spec.map_comp]
    simp only [Category.assoc]
  have hτ : (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin q))).inv ≫
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin q))
      = Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)) := by
    simp
  have hσ : (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).inv ≫
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin n))
      = Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k)) := by
    simp
  have hA : (((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s)).ι ≫
          (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ≫
            Spec.map (CommRingCat.ofHom
              (((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom).comp
                (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
                  (GraphAlgebra (graphCoordinates k M n q F))))) ≫
              (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin q))).inv) ≫
        affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin q))
      = ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s)).ι ≫
          affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin n)) := by
    simp only [Category.assoc]
    rw [hτ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, graphAlgebraEquiv_symm_comp_algebraMap_comp_C_consolidated171 k M n q F, ← hσ,
      Iso.hom_inv_id_assoc]
  have hB : ∀ i : ULift.{u, 0} (Fin M ⊕ Fin q),
      (Scheme.Hom.appTop (graphMorphismToAffineSpace k M n q F
          ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s))))
        (AffineSpace.coord (Spec (CommRingCat.of k)) i)
      = (Scheme.Hom.appTop (((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s)).ι ≫
          (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ≫
            Spec.map (CommRingCat.ofHom
              (((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom).comp
                (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
                  (GraphAlgebra (graphCoordinates k M n q F))))) ≫
              (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin q))).inv))
          (AffineSpace.coord (Spec (CommRingCat.of k)) i) := by
    intro i
    have e1 : (Scheme.Hom.appTop (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin q))).inv)
          (AffineSpace.coord (Spec (CommRingCat.of k)) i)
        = (Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k))).inv
            (MvPolynomial.X i) := by
      have h : (Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k))).hom
          ((Scheme.Hom.appTop (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin q))).inv)
            (AffineSpace.coord (Spec (CommRingCat.of k)) i))
          = MvPolynomial.X i :=
        (mvPolynomialEquivGlobalSections_symm_apply k (ULift.{u, 0} (Fin M ⊕ Fin q))
            (AffineSpace.coord (Spec (CommRingCat.of k)) i)).symm.trans
          (mvPolynomialEquivGlobalSections_symm_coord k (ULift.{u, 0} (Fin M ⊕ Fin q)) i)
      rw [← h, Iso.hom_inv_id_apply]
    have e2 : (Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom
          (((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom).comp
            (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
              (GraphAlgebra (graphCoordinates k M n q F)))))))
          ((Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k))).inv
            (MvPolynomial.X i))
        = (Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k))).inv
            (graphCoordinates k M n q F i) := by
      rw [← graphAlgebraEquiv_symm_comp_algebraMap_X_consolidated171 k M n q F i]
      exact (RingHom.congr_fun (congrArg CommRingCat.Hom.hom
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
          (((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom).comp
            (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
              (GraphAlgebra (graphCoordinates k M n q F)))))))
        (MvPolynomial.X i)).symm
    have e3 : (Scheme.Hom.appTop (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom)
          ((Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k))).inv
            (graphCoordinates k M n q F i))
        = mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n)) (graphCoordinates k M n q F i) :=
      (mvPolynomialEquivGlobalSections_apply k (ULift.{u, 0} (Fin M ⊕ Fin n)) (graphCoordinates k M n q F i)).symm
    rw [appTop_comp_apply_consolidated171, appTop_comp_apply_consolidated171, appTop_comp_apply_consolidated171, e1, e2, e3]
    obtain ⟨i⟩ := i
    cases i with
    | inl a =>
      rw [graphCoordinates_inl, mvPolynomialEquivGlobalSections_X]
      exact graphMorphismToAffineSpace_appTop_coord_inl k M n q F _ a
    | inr j =>
      rw [graphCoordinates_inr, mvPolynomialEquivGlobalSections_polynomialOfSection]
      exact graphMorphismToAffineSpace_appTop_coord_inr k M n q F _ j
  rw [key]
  apply AffineSpace.hom_ext
  · exact (graphMorphismToAffineSpace_comp_affineSpaceIndexedByToSpec k M n q F _).trans hA.symm
  · exact hB

theorem smooth_graphMorphismToAffineSpace_basicOpen (hs : Function.Injective s) :
    Smooth (graphMorphismToAffineSpace k M n q F
      ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
        (jacobianDetSection k M n q F s))) := by
  have hsm : Smooth (specGraphAwayToAffineSpace k M n q F s) :=
    smooth_specMap_algebraMap_graphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)
      (sumVariableMap_injective M n q s hs)
  rw [graphMorphismToAffineSpace_basicOpen_jacobianDetSection_eq k M n q F s]
  infer_instance


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PolynomialRingOverGlobalSections
section

open TopologicalSpace

section

def mvPolynomialToSumCoordinateRing (k : Type u) [Field k] (M n : ℕ) :
    MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
      Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n)), ⊤) :=
  MvPolynomial.eval₂Hom ((projLeft k M n).appTop).hom
    (fun i : Fin n =>
      AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n)))

@[simp]
theorem mvPolynomialToSumCoordinateRing_C (k : Type u) [Field k] (M n : ℕ)
    (t : Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    mvPolynomialToSumCoordinateRing k M n (MvPolynomial.C t) = (projLeft k M n).appTop t := by
  simp [mvPolynomialToSumCoordinateRing]

@[simp]
theorem mvPolynomialToSumCoordinateRing_X (k : Type u) [Field k] (M n : ℕ) (i : Fin n) :
    mvPolynomialToSumCoordinateRing k M n (MvPolynomial.X i) =
      AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n)) := by
  simp [mvPolynomialToSumCoordinateRing]

private theorem comp_appTop_apply_eq_consolidated172 {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (t : Γ(Z, ⊤)) :
    (f ≫ g).appTop t = f.appTop (g.appTop t) := rfl

private theorem id_appTop_apply_consolidated172 (X : Scheme.{u}) (t : Γ(X, ⊤)) :
    (𝟙 X : X ⟶ X).appTop t = t := by simp

theorem specToAffineSpaceExtendCoords_appTop_mvPolynomial (k : Type u) [Field k] (A : Scheme.{u})
    [IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B')
    (he : e ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) = pA)
    (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop (mvPolynomialToSumCoordinateRing k M n p) =
      (Scheme.ΓSpecIso B').inv
        (MvPolynomial.eval₂ σ.hom b (MvPolynomial.map (e.appTop).hom p)) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have h1 : (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop ((projLeft k M n).appTop a)
          = (Scheme.ΓSpecIso B').inv (σ (e.appTop a)) := by
        rw [← comp_appTop_apply_eq_consolidated172, specToAffineSpaceExtendCoords_comp_projLeft k A pA M e σ n b he,
          comp_appTop_apply_eq_consolidated172, specHomOfGlobalSections_appTop]
      rw [mvPolynomialToSumCoordinateRing_C, h1]
      simp
  | add p q hp hq =>
      simp only [map_add, MvPolynomial.eval₂_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.eval₂_mul, mvPolynomialToSumCoordinateRing_X, hp,
        specToAffineSpaceExtendCoords_appTop_coord_inr, MvPolynomial.map_X, MvPolynomial.eval₂_X]

section
variable {X Y : Scheme.{u}}

private theorem appTop_surjective_of_isClosedImmersion_consolidated172 (f : X ⟶ Y) [IsAffine Y] [IsClosedImmersion f] :
    Function.Surjective ⇑((f.appTop).hom) :=
  (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine (f := f)).2

private theorem appTop_ext_consolidated172 {f g : X ⟶ Y}
    (h : ∀ t : Γ(Y, ⊤), f.appTop t = g.appTop t) : f.appTop = g.appTop := by
  ext t
  exact h t


end

private theorem specMap_appTop_ΓSpecIso_inv_consolidated172 {R S : CommRingCat.{u}} (f : R ⟶ S) (r : R) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (f r) := by
  have h := congrArg (fun m : R ⟶ Γ(Spec S, ⊤) => CommRingCat.Hom.hom m r)
    (Scheme.ΓSpecIso_inv_naturality f)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  exact h.symm

private def polynomialRingOverGlobalSections_consolidated172 (k : Type u) [Field k] (M n : ℕ) : CommRingCat.{u} :=
  CommRingCat.of (MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤))

private def globalSectionsToPolynomialRing_consolidated172 (k : Type u) [Field k] (M n : ℕ) :
    Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) ⟶ polynomialRingOverGlobalSections_consolidated172 k M n :=
  CommRingCat.ofHom
    (MvPolynomial.C :
      Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
        MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤))

private theorem globalSectionsToPolynomialRing_apply_consolidated172 (k : Type u) [Field k] (M n : ℕ)
    (t : Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    globalSectionsToPolynomialRing_consolidated172 k M n t = MvPolynomial.C t := rfl

private def polynomialRingVariables_consolidated172 (k : Type u) [Field k] (M n : ℕ) : Fin n → polynomialRingOverGlobalSections_consolidated172 k M n :=
  fun i => MvPolynomial.X i

private def specPolynomialRingToAffineSpaceSum_consolidated172 (k : Type u) [Field k] (M n : ℕ) :
    Spec (polynomialRingOverGlobalSections_consolidated172 k M n) ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n)) :=
  specToAffineSpaceExtendCoords k (affineSpaceIndexedBy k (ULift.{u} (Fin M)))
    (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))) M (𝟙 _) (globalSectionsToPolynomialRing_consolidated172 k M n) n (polynomialRingVariables_consolidated172 k M n)

private def affineSpaceSumToSpecPolynomialRing_consolidated172 (k : Type u) [Field k] (M n : ℕ) :
    affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n)) ⟶ Spec (polynomialRingOverGlobalSections_consolidated172 k M n) :=
  (affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n))).isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom (mvPolynomialToSumCoordinateRing k M n))

section
variable (k : Type u) [Field k] (M n : ℕ)

private theorem comp_affineSpaceIndexedByToSpec_eq_consolidated172 :
    specPolynomialRingToAffineSpaceSum_consolidated172 k M n ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M ⊕ Fin n)) =
      specHomOfGlobalSections (affineSpaceIndexedBy k (ULift.{u} (Fin M))) (globalSectionsToPolynomialRing_consolidated172 k M n) ≫
        affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) :=
  specToAffineSpaceExtendCoords_comp_toSpec k (affineSpaceIndexedBy k (ULift.{u} (Fin M)))
    (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))) M (𝟙 _) (globalSectionsToPolynomialRing_consolidated172 k M n) n (polynomialRingVariables_consolidated172 k M n)

private theorem appTop_coord_inl_eq_C_consolidated172 (a : Fin M) :
    (specPolynomialRingToAffineSpaceSum_consolidated172 k M n).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inl a) : ULift.{u} (Fin M ⊕ Fin n))) =
      (Scheme.ΓSpecIso (polynomialRingOverGlobalSections_consolidated172 k M n)).inv
        (MvPolynomial.C (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up a))) := by
  have h := specToAffineSpaceExtendCoords_appTop_coord_inl k (affineSpaceIndexedBy k (ULift.{u} (Fin M)))
    (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))) M (𝟙 _) (globalSectionsToPolynomialRing_consolidated172 k M n) n (polynomialRingVariables_consolidated172 k M n) a
  rw [Category.comp_id, specHomOfGlobalSections_appTop] at h
  exact h

private theorem appTop_coord_inr_eq_X_consolidated172 (j : Fin n) :
    (specPolynomialRingToAffineSpaceSum_consolidated172 k M n).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n))) =
      (Scheme.ΓSpecIso (polynomialRingOverGlobalSections_consolidated172 k M n)).inv (MvPolynomial.X j) :=
  specToAffineSpaceExtendCoords_appTop_coord_inr k (affineSpaceIndexedBy k (ULift.{u} (Fin M)))
    (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))) M (𝟙 _) (globalSectionsToPolynomialRing_consolidated172 k M n) n (polynomialRingVariables_consolidated172 k M n) j

private theorem appTop_ΓSpecIso_inv_eq_mvPolynomialToSumCoordinateRing_consolidated172 (r : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    (affineSpaceSumToSpecPolynomialRing_consolidated172 k M n).appTop ((Scheme.ΓSpecIso (polynomialRingOverGlobalSections_consolidated172 k M n)).inv r) =
      mvPolynomialToSumCoordinateRing k M n r := by
  have h1 : (Spec.map (CommRingCat.ofHom (mvPolynomialToSumCoordinateRing k M n))).appTop
        ((Scheme.ΓSpecIso (polynomialRingOverGlobalSections_consolidated172 k M n)).inv r) =
      (Scheme.ΓSpecIso Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n)), ⊤)).inv
        (mvPolynomialToSumCoordinateRing k M n r) :=
    specMap_appTop_ΓSpecIso_inv_consolidated172 (CommRingCat.ofHom (mvPolynomialToSumCoordinateRing k M n)) r
  have h2 : (affineSpaceSumToSpecPolynomialRing_consolidated172 k M n).appTop ((Scheme.ΓSpecIso (polynomialRingOverGlobalSections_consolidated172 k M n)).inv r) =
      ((affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n))).isoSpec.hom).appTop
        ((Spec.map (CommRingCat.ofHom (mvPolynomialToSumCoordinateRing k M n))).appTop
          ((Scheme.ΓSpecIso (polynomialRingOverGlobalSections_consolidated172 k M n)).inv r)) := rfl
  rw [h2, h1]
  simp [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]

private theorem mvPolynomialToSumCoordinateRing_surjective_consolidated172 :
    Function.Surjective ⇑(mvPolynomialToSumCoordinateRing k M n) := by
  have hcomp : affineSpaceSumToSpecPolynomialRing_consolidated172 k M n ≫ specPolynomialRingToAffineSpaceSum_consolidated172 k M n =
      𝟙 (affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n))) := by
    refine AffineSpace.hom_ext ?_ ?_
    · apply AlgebraicGeometry.ext_of_isAffine
      apply appTop_ext_consolidated172
      intro t
      rw [Category.assoc, Category.id_comp, comp_affineSpaceIndexedByToSpec_eq_consolidated172, comp_appTop_apply_eq_consolidated172,
        comp_appTop_apply_eq_consolidated172, specHomOfGlobalSections_appTop, globalSectionsToPolynomialRing_apply_consolidated172, appTop_ΓSpecIso_inv_eq_mvPolynomialToSumCoordinateRing_consolidated172,
        mvPolynomialToSumCoordinateRing_C, ← comp_appTop_apply_eq_consolidated172, projLeft_comp_affineSpaceIndexedByToSpec]
    · rintro ⟨i⟩
      obtain a | j := i
      · rw [comp_appTop_apply_eq_consolidated172, appTop_coord_inl_eq_C_consolidated172, appTop_ΓSpecIso_inv_eq_mvPolynomialToSumCoordinateRing_consolidated172, mvPolynomialToSumCoordinateRing_C,
          projLeft_appTop_coord, id_appTop_apply_consolidated172]
      · rw [comp_appTop_apply_eq_consolidated172, appTop_coord_inr_eq_X_consolidated172, appTop_ΓSpecIso_inv_eq_mvPolynomialToSumCoordinateRing_consolidated172, mvPolynomialToSumCoordinateRing_X,
          id_appTop_apply_consolidated172]
  intro x
  refine ⟨(Scheme.ΓSpecIso (polynomialRingOverGlobalSections_consolidated172 k M n)).hom ((specPolynomialRingToAffineSpaceSum_consolidated172 k M n).appTop x), ?_⟩
  have hx : (affineSpaceSumToSpecPolynomialRing_consolidated172 k M n).appTop ((specPolynomialRingToAffineSpaceSum_consolidated172 k M n).appTop x) = x := by
    rw [← comp_appTop_apply_eq_consolidated172, hcomp, id_appTop_apply_consolidated172]
  rw [← appTop_ΓSpecIso_inv_eq_mvPolynomialToSumCoordinateRing_consolidated172 k M n
    ((Scheme.ΓSpecIso (polynomialRingOverGlobalSections_consolidated172 k M n)).hom ((specPolynomialRingToAffineSpaceSum_consolidated172 k M n).appTop x)),
    Iso.hom_inv_id_apply]
  exact hx


end

theorem exists_mvPolynomial_map_appTop_eq (k : Type u) [Field k] (A : Scheme.{u}) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M)))
    [IsClosedImmersion e] (n q : ℕ)
    (rel : Fin q → MvPolynomial (Fin n) Γ(A, ⊤)) (j : Fin q) :
    ∃ P : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤),
      MvPolynomial.map (e.appTop).hom P = rel j := by
  obtain ⟨P, hP⟩ := MvPolynomial.map_surjective ((e.appTop).hom)
    (appTop_surjective_of_isClosedImmersion_consolidated172 e) (rel j)
  exact ⟨P, hP⟩

section
variable (k : Type u) [Field k] (A : Scheme.{u}) [IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ) (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M)))

theorem ker_specToAffineSpaceExtendCoords_appTop [IsClosedImmersion e] {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B')
    (he : e ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) = pA)
    (q : ℕ) (rel : Fin q → MvPolynomial (Fin n) Γ(A, ⊤))
    (hrel : RingHom.ker (MvPolynomial.eval₂Hom σ.hom b) = Ideal.span (Set.range rel))
    (lift : Fin q → MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤))
    (hlift : ∀ j, MvPolynomial.map (e.appTop).hom (lift j) = rel j) :
    RingHom.ker ((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop).hom =
      Ideal.map ((projLeft k M n).appTop).hom (RingHom.ker (e.appTop).hom)
        ⊔ Ideal.span (Set.range fun j : Fin q => mvPolynomialToSumCoordinateRing k M n (lift j)) := by
  have hsurje : Function.Surjective ⇑((e.appTop).hom) :=
    appTop_surjective_of_isClosedImmersion_consolidated172 e
  have hmap : Function.Surjective ⇑(MvPolynomial.map ((e.appTop).hom) :
      MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
        MvPolynomial (Fin n) Γ(A, ⊤)) :=
    MvPolynomial.map_surjective _ hsurje
  have hsurjS : Function.Surjective ⇑(mvPolynomialToSumCoordinateRing k M n) := mvPolynomialToSumCoordinateRing_surjective_consolidated172 k M n
  have hι : Function.Injective ⇑((Scheme.ΓSpecIso B').inv) := by
    intro x y hxy
    have h := congrArg (fun z => (Scheme.ΓSpecIso B').hom z) hxy
    simpa using h
  have key : ∀ p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤),
      ((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop).hom (mvPolynomialToSumCoordinateRing k M n p) =
        (Scheme.ΓSpecIso B').inv
          (MvPolynomial.eval₂ σ.hom b (MvPolynomial.map (e.appTop).hom p)) :=
    fun p => specToAffineSpaceExtendCoords_appTop_mvPolynomial k A pA M e σ n b he p
  have step1 : RingHom.ker (((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop).hom.comp
        (mvPolynomialToSumCoordinateRing k M n)) =
      Ideal.comap (MvPolynomial.map ((e.appTop).hom)) (Ideal.span (Set.range rel)) := by
    rw [← hrel]
    ext p
    simp only [RingHom.mem_ker, RingHom.comp_apply, Ideal.mem_comap]
    rw [key p]
    constructor
    · intro h
      have h0 : MvPolynomial.eval₂ σ.hom b (MvPolynomial.map ((e.appTop).hom) p) = 0 := by
        apply hι
        rw [h]
        simp
      simpa [RingHom.mem_ker] using h0
    · intro h
      have h0 : MvPolynomial.eval₂ σ.hom b (MvPolynomial.map ((e.appTop).hom) p) = 0 := by
        simpa [RingHom.mem_ker] using h
      rw [h0]
      simp
  have step2 : Ideal.span (Set.range rel) =
      Ideal.map (MvPolynomial.map ((e.appTop).hom)) (Ideal.span (Set.range lift)) := by
    rw [Ideal.map_span]
    congr 1
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun j => (hlift j).symm)
  have step3 : Ideal.comap (MvPolynomial.map ((e.appTop).hom))
        (Ideal.map (MvPolynomial.map ((e.appTop).hom)) (Ideal.span (Set.range lift))) =
      Ideal.span (Set.range lift) ⊔
        RingHom.ker (MvPolynomial.map ((e.appTop).hom) :
          MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
            MvPolynomial (Fin n) Γ(A, ⊤)) :=
    Ideal.comap_map_of_surjective _ hmap _
  have step4 : RingHom.ker (MvPolynomial.map ((e.appTop).hom) :
        MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
          MvPolynomial (Fin n) Γ(A, ⊤)) =
      Ideal.map
        (MvPolynomial.C :
          Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
            MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤))
        (RingHom.ker ((e.appTop).hom)) :=
    MvPolynomial.ker_map _
  have hcomapker : Ideal.comap (mvPolynomialToSumCoordinateRing k M n)
        (RingHom.ker ((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop).hom) =
      RingHom.ker (((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop).hom.comp (mvPolynomialToSumCoordinateRing k M n)) := by
    ext p
    simp [RingHom.mem_ker, Ideal.mem_comap]
  have hcompEq : (mvPolynomialToSumCoordinateRing k M n).comp
      (MvPolynomial.C :
        Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
          MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤))
      = ((projLeft k M n).appTop).hom := by
    ext t
    exact mvPolynomialToSumCoordinateRing_C k M n t
  have main := Ideal.map_comap_of_surjective (mvPolynomialToSumCoordinateRing k M n) hsurjS
    (RingHom.ker ((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop).hom)
  rw [hcomapker, step1, step2, step3, step4] at main
  rw [← main, Ideal.map_sup, Ideal.map_span, Ideal.map_map, hcompEq]
  have hrange : (⇑(mvPolynomialToSumCoordinateRing k M n) '' Set.range lift)
      = Set.range (fun j : Fin q => mvPolynomialToSumCoordinateRing k M n (lift j)) := by
    rw [← Set.range_comp]
    rfl
  rw [hrange, sup_comm]

theorem preimage_basicOpen_specToAffineSpaceExtendCoords {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B')
    (f : Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n)), ⊤))
    (hf : IsUnit ((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop f)) :
    (Opens.map (specToAffineSpaceExtendCoords k A pA M e σ n b).base).obj
        ((affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n))).basicOpen f) = ⊤ := by
  have h1 : (Opens.map (specToAffineSpaceExtendCoords k A pA M e σ n b).base).obj
        ((affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n))).basicOpen f) =
      (Spec B').basicOpen ((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop f) :=
    Scheme.preimage_basicOpen ..
  have h2 : (Spec B').basicOpen ((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop f) = ⊤ :=
    Scheme.basicOpen_of_isUnit (Spec B') hf
  rw [h1, h2]


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatDescent
section


section

variable {W Y : Scheme.{u}}

section
variable {X₁ X₂ X₃ X₄ : Scheme.{u}} {p : X₁ ⟶ X₂} {q : X₁ ⟶ X₃} {f : X₂ ⟶ X₄} {h : X₃ ⟶ X₄} (sq : IsPullback p q f h)
include sq

private theorem flat_of_isPullback_of_flat_consolidated205 (hh : Flat h) : Flat p :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Flat) sq.flip hh

private theorem surjective_of_isPullback_consolidated205 (hh : AlgebraicGeometry.Surjective h) : AlgebraicGeometry.Surjective p :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Surjective) sq.flip hh


end

theorem flat_and_surjective_of_isPullback_blowupMorphism (g : W ⟶ Y) [Flat g]
    [AlgebraicGeometry.Surjective g] (t : SequenceOfBlowups W) (s : SequenceOfBlowups Y) (L : ℕ)
    (γ : ∀ i : ℕ, i ≤ L → (t.schemeAt i ⟶ s.schemeAt i))
    (hzero : γ 0 (Nat.zero_le _) ≫ s.isoZero.hom = t.isoZero.hom ≫ g)
    (hsq : ∀ i : ℕ, ∀ hi : i < L,
      IsPullback (γ (i + 1) hi) (t.transitionMapSucc i) (s.transitionMapSucc i) (γ i hi.le)) :
    ∀ i : ℕ, ∀ hi : i ≤ L,
      Flat (γ i hi) ∧ AlgebraicGeometry.Surjective (γ i hi) := by
  intro i
  induction i with
  | zero =>
    intro hi
    have sq0 : IsPullback (γ 0 hi) t.isoZero.hom s.isoZero.hom g :=
      (IsPullback.of_horiz_isIso (CommSq.mk hzero.symm)).flip
    exact ⟨flat_of_isPullback_of_flat_consolidated205 sq0 inferInstance, surjective_of_isPullback_consolidated205 sq0 inferInstance⟩
  | succ n ih =>
    intro hi
    have hn : n < L := hi
    obtain ⟨hf, hs⟩ := ih hn.le
    exact ⟨flat_of_isPullback_of_flat_consolidated205 (hsq n hn) hf, surjective_of_isPullback_consolidated205 (hsq n hn) hs⟩

structure CompatibleBaseIsoAt (t₁ t₂ : SequenceOfBlowups W) (s₁ s₂ : SequenceOfBlowups Y) (L : ℕ)
    (γ₁ : ∀ i : ℕ, i ≤ L → (t₁.schemeAt i ⟶ s₁.schemeAt i))
    (γ₂ : ∀ i : ℕ, i ≤ L → (t₂.schemeAt i ⟶ s₂.schemeAt i))
    (φ : ∀ i : ℕ, i ≤ L → (t₁.schemeAt i ≅ t₂.schemeAt i)) (i : ℕ) where
  iso : s₁.schemeAt i ≅ s₂.schemeAt i
  compat : ∀ hi : i ≤ L, γ₁ i hi ≫ iso.hom = (φ i hi).hom ≫ γ₂ i hi

structure BlowupDescentData (g : W ⟶ Y) (t₁ t₂ : SequenceOfBlowups W) (s₁ s₂ : SequenceOfBlowups Y) (L : ℕ)
    (γ₁ : ∀ i : ℕ, i ≤ L → (t₁.schemeAt i ⟶ s₁.schemeAt i))
    (γ₂ : ∀ i : ℕ, i ≤ L → (t₂.schemeAt i ⟶ s₂.schemeAt i))
    (φ : ∀ i : ℕ, i ≤ L → (t₁.schemeAt i ≅ t₂.schemeAt i)) : Prop where
  isBlowup_s₁ : ∀ i : ℕ, i < L → Blowup.IsBlowupAlongIdealSheaf (s₁.transitionMapSucc i) (s₁.center i)
  isBlowup_s₂ : ∀ i : ℕ, i < L → Blowup.IsBlowupAlongIdealSheaf (s₂.transitionMapSucc i) (s₂.center i)
  center_t₁ : ∀ i : ℕ, ∀ hi : i < L, t₁.center i = (s₁.center i).comap (γ₁ i hi.le)
  center_t₂ : ∀ i : ℕ, ∀ hi : i < L, t₂.center i = (s₂.center i).comap (γ₂ i hi.le)
  flat_γ₁ : ∀ i : ℕ, ∀ hi : i ≤ L, Flat (γ₁ i hi)
  pullback_γ₁ : ∀ i : ℕ, ∀ hi : i < L,
    IsPullback (γ₁ (i + 1) hi) (t₁.transitionMapSucc i) (s₁.transitionMapSucc i) (γ₁ i hi.le)
  pullback_γ₂ : ∀ i : ℕ, ∀ hi : i < L,
    IsPullback (γ₂ (i + 1) hi) (t₂.transitionMapSucc i) (s₂.transitionMapSucc i) (γ₂ i hi.le)
  zero_γ₁ : γ₁ 0 (Nat.zero_le _) ≫ s₁.isoZero.hom = t₁.isoZero.hom ≫ g
  zero_γ₂ : γ₂ 0 (Nat.zero_le _) ≫ s₂.isoZero.hom = t₂.isoZero.hom ≫ g
  surjective_γ₁ : ∀ i : ℕ, ∀ hi : i ≤ L, AlgebraicGeometry.Surjective (γ₁ i hi)
  isBlowup_t₁ : ∀ i : ℕ, i < L → Blowup.IsBlowupAlongIdealSheaf (t₁.transitionMapSucc i) (t₁.center i)
  center_φ : ∀ i : ℕ, ∀ hi : i < L, (t₂.center i).comap (φ i hi.le).hom = t₁.center i
  zero_φ : (φ 0 (Nat.zero_le _)).hom ≫ t₂.isoZero.hom = t₁.isoZero.hom
  step_φ : ∀ i : ℕ, ∀ hi : i < L,
    (φ (i + 1) hi).hom ≫ t₂.transitionMapSucc i = t₁.transitionMapSucc i ≫ (φ i hi.le).hom

section
variable {g : W ⟶ Y} {t₁ t₂ : SequenceOfBlowups W} {s₁ s₂ : SequenceOfBlowups Y} {L : ℕ} {γ₁ : ∀ i : ℕ, i ≤ L → (t₁.schemeAt i ⟶ s₁.schemeAt i)} {γ₂ : ∀ i : ℕ, i ≤ L → (t₂.schemeAt i ⟶ s₂.schemeAt i)} {φ : ∀ i : ℕ, i ≤ L → (t₁.schemeAt i ≅ t₂.schemeAt i)} (hd : BlowupDescentData g t₁ t₂ s₁ s₂ L γ₁ γ₂ φ)
include hd

theorem comp_isoObjZero_trans_symm_eq :
    ∀ hi : (0 : ℕ) ≤ L,
      γ₁ 0 hi ≫ (s₁.isoZero ≪≫ s₂.isoZero.symm).hom = (φ 0 hi).hom ≫ γ₂ 0 hi := by
  intro hi
  have h1 : γ₁ 0 hi ≫ s₁.isoZero.hom = t₁.isoZero.hom ≫ g := hd.zero_γ₁
  have h2 : γ₂ 0 hi ≫ s₂.isoZero.hom = t₂.isoZero.hom ≫ g := hd.zero_γ₂
  have h3 : (φ 0 hi).hom ≫ t₂.isoZero.hom = t₁.isoZero.hom := hd.zero_φ
  have key : (γ₁ 0 hi ≫ (s₁.isoZero ≪≫ s₂.isoZero.symm).hom) ≫ s₂.isoZero.hom
      = ((φ 0 hi).hom ≫ γ₂ 0 hi) ≫ s₂.isoZero.hom := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h1, h2, ← Category.assoc, h3]
  exact (cancel_mono s₂.isoZero.hom).mp key

theorem CompatibleBaseIsoAt.center_comap_eq {i : ℕ} (hi : i < L)
    (st : CompatibleBaseIsoAt t₁ t₂ s₁ s₂ L γ₁ γ₂ φ i) :
    (s₂.center i).comap st.iso.hom = s₁.center i := by
  have := hd.flat_γ₁ i hi.le
  have := hd.surjective_γ₁ i hi.le
  refine FlatDescentIdealSheaf.eq_of_comap_eq (γ₁ i hi.le) _ _ ?_
  rw [← Scheme.IdealSheafData.comap_comp, st.compat hi.le, Scheme.IdealSheafData.comap_comp,
    ← hd.center_t₂ i hi, hd.center_φ i hi]
  exact hd.center_t₁ i hi

theorem CompatibleBaseIsoAt.exists_iso_succ_blowupMorphism_comm {i : ℕ} (hi : i < L)
    (st : CompatibleBaseIsoAt t₁ t₂ s₁ s₂ L γ₁ γ₂ φ i) :
    ∃ e : s₁.schemeAt (i + 1) ≅ s₂.schemeAt (i + 1),
      e.hom ≫ s₂.transitionMapSucc i ≫ st.iso.inv = s₁.transitionMapSucc i := by
  have h2 := (hd.isBlowup_s₂ i hi).comp_iso_hom st.iso.symm
  simp only [Iso.symm_hom, Iso.symm_inv] at h2
  rw [CompatibleBaseIsoAt.center_comap_eq hd hi st] at h2
  exact (hd.isBlowup_s₁ i hi).exists_iso h2


end

theorem CompatibleBaseIsoAt.blowupMorphism_square_comm {t₁ t₂ : SequenceOfBlowups W} {s₁ s₂ : SequenceOfBlowups Y}
    {L : ℕ}
    {γ₁ : ∀ i : ℕ, i ≤ L → (t₁.schemeAt i ⟶ s₁.schemeAt i)}
    {γ₂ : ∀ i : ℕ, i ≤ L → (t₂.schemeAt i ⟶ s₂.schemeAt i)}
    {φ : ∀ i : ℕ, i ≤ L → (t₁.schemeAt i ≅ t₂.schemeAt i)}
    {i : ℕ} (st : CompatibleBaseIsoAt t₁ t₂ s₁ s₂ L γ₁ γ₂ φ i)
    (e : s₁.schemeAt (i + 1) ≅ s₂.schemeAt (i + 1))
    (he : e.hom ≫ s₂.transitionMapSucc i ≫ st.iso.inv = s₁.transitionMapSucc i) :
    e.hom ≫ s₂.transitionMapSucc i = s₁.transitionMapSucc i ≫ st.iso.hom := by
  rw [← he]
  simp

private def isoFamilyOfZero_consolidated205 {A B : ℕ → Scheme.{u}} (x : A 0 ≅ B 0) (i : ℕ) (hi : i ≤ 0) : A i ≅ B i :=
  Eq.mpr (congrArg (fun j : ℕ => (A j ≅ B j)) (Nat.le_zero.mp hi)) x

private theorem isoFamilyOfZero_zero_consolidated205 {A B : ℕ → Scheme.{u}} (x : A 0 ≅ B 0) {hi : (0 : ℕ) ≤ 0} :
    isoFamilyOfZero_consolidated205 x 0 hi = x := rfl

private def extendIsoFamilySucc_consolidated205 {A B : ℕ → Scheme.{u}} (N : ℕ) (e : ∀ i : ℕ, i ≤ N → (A i ≅ B i))
    (x : A (N + 1) ≅ B (N + 1)) (i : ℕ) (hi : i ≤ N + 1) : A i ≅ B i :=
  if h : i ≤ N then e i h
  else Eq.mpr (congrArg (fun j : ℕ => (A j ≅ B j))
    (Nat.le_antisymm hi (Nat.not_le.mp h))) x

section
variable {A B : ℕ → Scheme.{u}} (N : ℕ) (e : ∀ i : ℕ, i ≤ N → (A i ≅ B i)) (x : A (N + 1) ≅ B (N + 1))

private theorem extendIsoFamilySucc_of_le_consolidated205 {i : ℕ} {hi : i ≤ N + 1}
    (h : i ≤ N) : extendIsoFamilySucc_consolidated205 N e x i hi = e i h := dif_pos h

private theorem extendIsoFamilySucc_self_consolidated205 {hi : N + 1 ≤ N + 1} :
    extendIsoFamilySucc_consolidated205 N e x (N + 1) hi = x := dif_neg (Nat.not_succ_le_self N)


end

section
variable {g : W ⟶ Y}

private theorem exists_compatible_isos_of_le_consolidated205 {t₁ t₂ : SequenceOfBlowups W} {s₁ s₂ : SequenceOfBlowups Y} {L : ℕ}
    {γ₁ : ∀ i : ℕ, i ≤ L → (t₁.schemeAt i ⟶ s₁.schemeAt i)}
    {γ₂ : ∀ i : ℕ, i ≤ L → (t₂.schemeAt i ⟶ s₂.schemeAt i)}
    {φ : ∀ i : ℕ, i ≤ L → (t₁.schemeAt i ≅ t₂.schemeAt i)}
    (hd : BlowupDescentData g t₁ t₂ s₁ s₂ L γ₁ γ₂ φ) (N : ℕ) :
    ∀ hN : N ≤ L, ∃ e : ∀ i : ℕ, i ≤ N → (s₁.schemeAt i ≅ s₂.schemeAt i),
      ((e 0 (Nat.zero_le _)).hom ≫ s₂.isoZero.hom = s₁.isoZero.hom) ∧
      (∀ i : ℕ, ∀ hi : i < N,
        (e (i + 1) hi).hom ≫ s₂.transitionMapSucc i = s₁.transitionMapSucc i ≫ (e i hi.le).hom) ∧
      (∀ i : ℕ, ∀ hi : i ≤ N,
        γ₁ i (hi.trans hN) ≫ (e i hi).hom
          = (φ i (hi.trans hN)).hom ≫ γ₂ i (hi.trans hN)) := by
  induction N with
  | zero =>
    intro hN
    refine ⟨isoFamilyOfZero_consolidated205 (A := fun i : ℕ => s₁.schemeAt i) (B := fun i : ℕ => s₂.schemeAt i)
      (s₁.isoZero ≪≫ s₂.isoZero.symm), ?_, ?_, ?_⟩
    · rw [isoFamilyOfZero_zero_consolidated205]
      simp
    · intro i hi
      exact absurd hi (Nat.not_lt_zero i)
    · intro i hi
      obtain rfl : i = 0 := Nat.le_zero.mp hi
      rw [isoFamilyOfZero_zero_consolidated205]
      exact comp_isoObjZero_trans_symm_eq hd (hi.trans hN)
  | succ N ih =>
    intro hN
    have hNlt : N < L := hN
    obtain ⟨e, h0, hsqe, hc⟩ := ih hNlt.le
    have hstN : γ₁ N hNlt.le ≫ (e N (Nat.le_refl N)).hom
        = (φ N hNlt.le).hom ≫ γ₂ N hNlt.le := hc N (Nat.le_refl N)
    let st : CompatibleBaseIsoAt t₁ t₂ s₁ s₂ L γ₁ γ₂ φ N :=
      { iso := e N (Nat.le_refl N)
        compat := fun _ => hstN }
    obtain ⟨x, hx⟩ := CompatibleBaseIsoAt.exists_iso_succ_blowupMorphism_comm hd hNlt st
    have hxsq : x.hom ≫ s₂.transitionMapSucc N = s₁.transitionMapSucc N ≫ (e N (Nat.le_refl N)).hom :=
      CompatibleBaseIsoAt.blowupMorphism_square_comm st x hx
    refine ⟨extendIsoFamilySucc_consolidated205 (A := fun i : ℕ => s₁.schemeAt i) (B := fun i : ℕ => s₂.schemeAt i) N e x,
      ?_, ?_, ?_⟩
    · rw [extendIsoFamilySucc_of_le_consolidated205 N e x (Nat.zero_le N)]
      exact h0
    · intro i hi
      rcases Nat.lt_or_ge i N with h | h
      · rw [extendIsoFamilySucc_of_le_consolidated205 N e x (Nat.succ_le_of_lt h), extendIsoFamilySucc_of_le_consolidated205 N e x h.le]
        exact hsqe i h
      · obtain rfl : i = N := Nat.le_antisymm (Nat.lt_succ_iff.mp hi) h
        rw [extendIsoFamilySucc_self_consolidated205, extendIsoFamilySucc_of_le_consolidated205 _ _ _ (Nat.le_refl _)]
        exact hxsq
    · intro i hi
      rcases Nat.lt_or_ge i (N + 1) with h | h
      · have hiN : i ≤ N := Nat.lt_succ_iff.mp h
        rw [extendIsoFamilySucc_of_le_consolidated205 N e x hiN]
        exact hc i hiN
      · obtain rfl : i = N + 1 := Nat.le_antisymm hi h
        rw [extendIsoFamilySucc_self_consolidated205]
        have ha : (γ₁ (N + 1) hNlt ≫ x.hom) ≫ s₂.transitionMapSucc N
            = t₁.transitionMapSucc N ≫ (φ N hNlt.le).hom ≫ γ₂ N hNlt.le := by
          rw [Category.assoc, hxsq, ← Category.assoc, (hd.pullback_γ₁ N hNlt).w,
            Category.assoc, hstN]
        have hb : ((φ (N + 1) hNlt).hom ≫ γ₂ (N + 1) hNlt) ≫ s₂.transitionMapSucc N
            = t₁.transitionMapSucc N ≫ (φ N hNlt.le).hom ≫ γ₂ N hNlt.le := by
          rw [Category.assoc, (hd.pullback_γ₂ N hNlt).w, ← Category.assoc,
            hd.step_φ N hNlt, Category.assoc]
        have hide : (s₂.center N).comap
            (t₁.transitionMapSucc N ≫ (φ N hNlt.le).hom ≫ γ₂ N hNlt.le)
            = (t₁.center N).comap (t₁.transitionMapSucc N) := by
          rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
            ← hd.center_t₂ N hNlt, hd.center_φ N hNlt]
        have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor ((s₂.center N).comap
            (t₁.transitionMapSucc N ≫ (φ N hNlt.le).hom ≫ γ₂ N hNlt.le)) := by
          rw [hide]
          exact (hd.isBlowup_t₁ N hNlt).1
        exact (hd.isBlowup_s₂ N hNlt).hom_ext_of_comp_eq hcart ha hb

theorem IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic [Flat g]
    [AlgebraicGeometry.Surjective g] {t₁ t₂ : SequenceOfBlowups W} {s₁ s₂ : SequenceOfBlowups Y}
    (h₁ : IsStrictPullbackBlowupSeq g t₁ s₁) (h₂ : IsStrictPullbackBlowupSeq g t₂ s₂)
    (he : t₁.Isomorphic t₂) : s₁.Isomorphic s₂ := by
  obtain ⟨hlen₁, σ₁, hσ₁0, hσ₁sq, hσ₁c⟩ := h₁
  obtain ⟨hlen₂, σ₂, hσ₂0, hσ₂sq, hσ₂c⟩ := h₂
  obtain ⟨hlent, φ, hφ0, hφstep, hφc⟩ := he
  have hfs := flat_and_surjective_of_isPullback_blowupMorphism g t₁ s₁ t₁.length σ₁ hσ₁0 hσ₁sq
  have hd : BlowupDescentData g t₁ t₂ s₁ s₂ t₁.length σ₁
      (fun i hi => σ₂ i (le_of_le_of_eq hi hlent)) φ := by
    refine ⟨fun i hi => s₁.isBlowupAlongIdealSheaf_blowupMorphism i (by omega),
      fun i hi => s₂.isBlowupAlongIdealSheaf_blowupMorphism i (by omega),
      hσ₁c, fun i hi => hσ₂c i (by omega),
      fun i hi => (hfs i hi).1, hσ₁sq, fun i hi => hσ₂sq i (by omega),
      hσ₁0, hσ₂0, fun i hi => (hfs i hi).2,
      fun i hi => t₁.isBlowupAlongIdealSheaf_blowupMorphism i hi, hφc, hφ0, hφstep⟩
  obtain ⟨e, h0, hsqe, hc⟩ := exists_compatible_isos_of_le_consolidated205 hd t₁.length (Nat.le_refl _)
  refine ⟨by omega, fun i hi => e i (by omega), h0, ?_, ?_⟩
  · intro i hi
    exact hsqe i (by omega)
  · intro i hi
    have hiT : i < t₁.length := by omega
    exact CompatibleBaseIsoAt.center_comap_eq hd hiT
      { iso := e i hiT.le, compat := fun _ => hc i hiT.le }


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.StrictPullbackBlowupSeq
section


section

structure StrictPullbackBlowupSeq {X' X : Scheme.{u}} (g : X' ⟶ X)
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) where
  comp : ∀ i : ℕ, i ≤ t.length → (t.schemeAt i ⟶ s.schemeAt i)
  comp_zero : comp 0 (Nat.zero_le _) ≫ s.isoZero.hom = t.isoZero.hom ≫ g
  pullback : ∀ i : ℕ, ∀ hi : i < t.length,
    IsPullback (comp (i + 1) hi) (t.transitionMapSucc i) (s.transitionMapSucc i) (comp i hi.le)
  length_eq : t.length = s.length
  center_eq : ∀ i : ℕ, ∀ hi : i < t.length,
    t.center i = (s.center i).comap (comp i hi.le)

namespace StrictPullbackBlowupSeq

variable {X' X : Scheme.{u}} {g : X' ⟶ X} {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}

section
variable (D : StrictPullbackBlowupSeq g t s)
include D

theorem isStrictPullback : IsStrictPullbackBlowupSeq g t s :=
  ⟨D.length_eq, D.comp, D.comp_zero, D.pullback, D.center_eq⟩

theorem map_zero_eq :
    D.comp 0 (Nat.zero_le _) = t.isoZero.hom ≫ g ≫ s.isoZero.inv := by
  rw [← Category.assoc, ← D.comp_zero, Category.assoc, Iso.hom_inv_id, Category.comp_id]


end

private theorem flat_snd_of_isPullback_consolidated256 {W₁ W₂ W₃ W₄ : Scheme.{u}}
    {fst : W₁ ⟶ W₂} {snd : W₁ ⟶ W₃} {f : W₂ ⟶ W₄} {gg : W₃ ⟶ W₄}
    (sq : IsPullback fst snd f gg) (hf : Flat f) :
    Flat snd :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Flat) sq hf

theorem flat_map [Flat g] (D : StrictPullbackBlowupSeq g t s)
    (i : ℕ) (hi : i ≤ t.length) : Flat (D.comp i hi) := by
  revert hi
  induction i with
  | zero =>
      intro hi
      have sq : IsPullback t.isoZero.hom (D.comp 0 hi) g s.isoZero.hom :=
        IsPullback.of_horiz_isIso ⟨D.comp_zero.symm⟩
      exact flat_snd_of_isPullback_consolidated256 sq inferInstance
  | succ j ih =>
      intro hi
      have hjl : j < t.length := hi
      exact flat_snd_of_isPullback_consolidated256 (D.pullback j hjl).flip (ih hjl.le)

theorem surjective_map [Flat g] [AlgebraicGeometry.Surjective g]
    (D : StrictPullbackBlowupSeq g t s) (i : ℕ) (hi : i ≤ t.length) :
    AlgebraicGeometry.Surjective (D.comp i hi) :=
  (flat_and_surjective_of_isPullback_blowupMorphism g t s t.length D.comp D.comp_zero D.pullback i hi).2

end StrictPullbackBlowupSeq

noncomputable def IsStrictPullbackBlowupSeq.toStrictPullbackBlowupSeq {X' X : Scheme.{u}} {g : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (h : IsStrictPullbackBlowupSeq g t s) :
    StrictPullbackBlowupSeq g t s where
  comp := h.2.choose
  comp_zero := h.2.choose_spec.1
  pullback := h.2.choose_spec.2.1
  length_eq := h.length_eq
  center_eq := h.2.choose_spec.2.2

section
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (t : MarkedBlowupSequenceData p I m E) {i : ℕ}

theorem MarkedBlowupSequenceData.le_toSequenceOfBlowups_length (hi : i ≤ t.length) :
    i ≤ t.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length := by
  rw [MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups, BlowupSequenceData.toSequenceOfBlowups_length]
  exact hi

theorem MarkedBlowupSequenceData.lt_toSequenceOfBlowups_length (hi : i < t.length) :
    i < t.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length := by
  rw [MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups, BlowupSequenceData.toSequenceOfBlowups_length]
  exact hi


end

section

variable {k : Type u} [Field k] {X' X : Scheme.{u}} {q : X' ⟶ Spec (CommRingCat.of k)}
  {g : X' ⟶ X} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} {d : BlowupSequenceData X}

def MarkedBlowupSequenceData.strictPullbackComparisonMap
    (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (i : ℕ) (hi : i ≤ t.length) : t.obj i ⟶ d.obj i :=
  D.comp i (t.le_toSequenceOfBlowups_length hi)

section
variable (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g)) (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)

theorem MarkedBlowupSequenceData.strictPullbackComparisonMap_eq_map
    (i : ℕ) (hi : i ≤ t.length) :
    t.strictPullbackComparisonMap D i hi = D.comp i (t.le_toSequenceOfBlowups_length hi) := rfl

theorem MarkedBlowupSequenceData.strictPullbackComparisonMap_zero
    :
    t.strictPullbackComparisonMap D 0 (Nat.zero_le _) ≫ d.isoZero.hom = t.isoZero.hom ≫ g :=
  D.comp_zero


end

theorem MarkedBlowupSequenceData.flat_strictPullbackComparisonMap [Flat g]
    (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (i : ℕ) (hi : i ≤ t.length) : Flat (t.strictPullbackComparisonMap D i hi) := by
  rw [MarkedBlowupSequenceData.strictPullbackComparisonMap_eq_map]
  exact D.flat_map i (t.le_toSequenceOfBlowups_length hi)

theorem MarkedBlowupSequenceData.surjective_strictPullbackComparisonMap [Flat g]
    [AlgebraicGeometry.Surjective g]
    (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (i : ℕ) (hi : i ≤ t.length) : AlgebraicGeometry.Surjective (t.strictPullbackComparisonMap D i hi) := by
  rw [MarkedBlowupSequenceData.strictPullbackComparisonMap_eq_map]
  exact D.surjective_map i (t.le_toSequenceOfBlowups_length hi)

section
variable (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g)) (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
include D

theorem MarkedBlowupSequenceData.length_eq_of_strictPullbackBlowupSeq
    :
    t.length = d.length := by
  have h := D.length_eq
  rw [MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups] at h
  simpa only [BlowupSequenceData.toSequenceOfBlowups_length] using h

theorem MarkedBlowupSequenceData.isPullback_strictPullbackComparisonMap
    (i : ℕ) (hi : i < t.length) :
    IsPullback (t.strictPullbackComparisonMap D (i + 1) (show i + 1 ≤ t.length from hi)) (t.map i) (d.map i)
      (t.strictPullbackComparisonMap D i hi.le) := by
  have h := D.pullback i (t.lt_toSequenceOfBlowups_length hi)
  rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, BlowupSequenceData.toSequenceOfBlowups_blowupMorphism] at h
  exact h

theorem MarkedBlowupSequenceData.strictPullbackComparisonMap_comp_blowupMorphism
    (i : ℕ) (hi : i < t.length) :
    t.strictPullbackComparisonMap D (i + 1) (show i + 1 ≤ t.length from hi) ≫ d.map i =
      t.map i ≫ t.strictPullbackComparisonMap D i hi.le :=
  (t.isPullback_strictPullbackComparisonMap D i hi).w

theorem MarkedBlowupSequenceData.center_eq_comap_strictPullbackComparisonMap
    (i : ℕ) (hi : i < t.length) :
    t.center i = (d.center i).comap (t.strictPullbackComparisonMap D i hi.le) :=
  D.center_eq i (t.lt_toSequenceOfBlowups_length hi)

theorem MarkedBlowupSequenceData.exceptionalIdeal_eq_comap_strictPullbackComparisonMap
    (i : ℕ) (hi : i < t.length) :
    Blowup.exceptionalIdeal (t.map i) (t.center i) =
      (Blowup.exceptionalIdeal (d.map i) (d.center i)).comap
        (t.strictPullbackComparisonMap D (i + 1) (show i + 1 ≤ t.length from hi)) := by
  have hc : t.center i = (d.center i).comap (t.strictPullbackComparisonMap D i hi.le) := t.center_eq_comap_strictPullbackComparisonMap D i hi
  have hsq : t.strictPullbackComparisonMap D (i + 1) (show i + 1 ≤ t.length from hi) ≫ d.map i =
      t.map i ≫ t.strictPullbackComparisonMap D i hi.le := t.strictPullbackComparisonMap_comp_blowupMorphism D i hi
  rw [Blowup.exceptionalIdeal_eq_comap, Blowup.exceptionalIdeal_eq_comap, hc, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, hsq]

theorem MarkedBlowupSequenceData.ideal_eq_comap_controlledTransform
    (hdiv : ∀ i < d.length, ∃ B : (d.obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * B =
        (d.controlledTransform I m i).comap (d.map i))
    (i : ℕ) (hi : i ≤ t.length) :
    t.ideal i = (d.controlledTransform I m i).comap (t.strictPullbackComparisonMap D i hi) := by
  revert hi
  induction i with
  | zero =>
      intro hi
      have h0 : t.strictPullbackComparisonMap D 0 hi ≫ d.isoZero.hom = t.isoZero.hom ≫ g := t.strictPullbackComparisonMap_zero D
      rw [t.ideal_zero, d.controlledTransform_zero I m, ← Scheme.IdealSheafData.comap_comp,
        ← Scheme.IdealSheafData.comap_comp, h0]
  | succ j ih =>
      intro hi
      have hj : j < t.length := hi
      have hjd : j < d.length := by
        have hlen := t.length_eq_of_strictPullbackBlowupSeq D
        omega
      have hct : Blowup.exceptionalIdeal (d.map j) (d.center j) ^ m * d.controlledTransform I m (j + 1) =
          (d.controlledTransform I m j).comap (d.map j) :=
        d.pow_exceptionalIdeal_mul_controlledTransform_succ I m j (hdiv j hjd)
      have hexc : Blowup.exceptionalIdeal (t.map j) (t.center j) =
          (Blowup.exceptionalIdeal (d.map j) (d.center j)).comap (t.strictPullbackComparisonMap D (j + 1) hi) :=
        t.exceptionalIdeal_eq_comap_strictPullbackComparisonMap D j hj
      have hcomp : t.strictPullbackComparisonMap D (j + 1) hi ≫ d.map j = t.map j ≫ t.strictPullbackComparisonMap D j hj.le :=
        t.strictPullbackComparisonMap_comp_blowupMorphism D j hj
      have hih : t.ideal j = (d.controlledTransform I m j).comap (t.strictPullbackComparisonMap D j hj.le) := ih hj.le
      have hsucc : Blowup.exceptionalIdeal (t.map j) (t.center j) ^ m * t.ideal (j + 1) =
          (t.ideal j).comap (t.map j) := t.ideal_succ j hj
      have main : Blowup.exceptionalIdeal (t.map j) (t.center j) ^ m *
          (d.controlledTransform I m (j + 1)).comap (t.strictPullbackComparisonMap D (j + 1) hi) =
          Blowup.exceptionalIdeal (t.map j) (t.center j) ^ m * t.ideal (j + 1) := by
        rw [hsucc, hih, hexc, ← Scheme.IdealSheafData.comap_pow,
          ← Scheme.IdealSheafData.comap_mul, hct, ← Scheme.IdealSheafData.comap_comp,
          ← Scheme.IdealSheafData.comap_comp, hcomp]
      exact (((isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal
        (t.isBlowup j hj)).pow m).eq_of_mul_eq_mul main).symm


end

theorem MarkedBlowupSequenceData.boundary_eq_comap_strictPullbackComparisonMap [Flat g]
    (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (hNd : ∀ i ≤ d.length, IsLocallyNoetherian (d.obj i))
    (hNt : ∀ i ≤ t.length, IsLocallyNoetherian (t.obj i))
    (i : ℕ) (hi : i ≤ t.length) :
    t.boundary i = (d.boundaryFrom E i).map (fun A => A.comap (t.strictPullbackComparisonMap D i hi)) := by
  revert hi
  induction i with
  | zero =>
      intro hi
      have h0 : t.strictPullbackComparisonMap D 0 hi ≫ d.isoZero.hom = t.isoZero.hom ≫ g := t.strictPullbackComparisonMap_zero D
      have key : ∀ A : X.IdealSheafData,
          (A.comap g).comap t.isoZero.hom =
            (A.comap d.isoZero.hom).comap (t.strictPullbackComparisonMap D 0 hi) := by
        intro A
        rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, h0]
      rw [MarkedBlowupSequenceData.boundary_zero, BlowupSequenceData.boundary_zero]
      simp only [List.map_map, Function.comp_def, key]
  | succ j ih =>
      intro hi
      have hj : j < t.length := hi
      have hlen : t.length = d.length := t.length_eq_of_strictPullbackBlowupSeq D
      have hjd : j < d.length := by omega
      have : IsLocallyNoetherian (d.obj (j + 1)) := hNd (j + 1) hjd
      have : IsLocallyNoetherian (t.obj (j + 1)) := hNt (j + 1) hi
      have : Flat (t.strictPullbackComparisonMap D j hj.le) := t.flat_strictPullbackComparisonMap D j hj.le
      have hst : ∀ A : (d.obj j).IdealSheafData,
          Blowup.strictTransform (t.map j) (t.center j) (A.comap (t.strictPullbackComparisonMap D j hj.le)) =
            (Blowup.strictTransform (d.map j) (d.center j) A).comap (t.strictPullbackComparisonMap D (j + 1) hi) := by
        intro A
        have h := comap_strictTransform_of_flat_of_isLocallyNoetherian (d.map j)
          (t.strictPullbackComparisonMap D j hj.le) (t.map j) (t.strictPullbackComparisonMap D (j + 1) hi)
          (t.isPullback_strictPullbackComparisonMap D j hj) (d.center j) A (d.isBlowup j hjd)
        rw [h, t.center_eq_comap_strictPullbackComparisonMap D j hj]
      have hexc : Blowup.exceptionalIdeal (t.map j) (t.center j) =
          (Blowup.exceptionalIdeal (d.map j) (d.center j)).comap (t.strictPullbackComparisonMap D (j + 1) hi) :=
        t.exceptionalIdeal_eq_comap_strictPullbackComparisonMap D j hj
      rw [t.boundary_succ j hj, ih hj.le, d.boundary_succ E j]
      simp only [List.map_append, List.map_map, List.map_cons, List.map_nil,
        Function.comp_def, hst, hexc]

end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SumCoordinatePartialDerivatives
section

open TopologicalSpace

section

def renameSumInl (k : Type u) [Field k] (M n : ℕ) :
    MvPolynomial (ULift.{u} (Fin M)) k →+* MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k :=
  (MvPolynomial.rename
      (fun a : ULift.{u} (Fin M) =>
        (ULift.up (Sum.inl a.down) : ULift.{u} (Fin M ⊕ Fin n)))).toRingHom

section
variable (k : Type u) [Field k] (M n : ℕ)

theorem renameSumInl_C (c : k) :
    renameSumInl k M n (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [renameSumInl]

theorem renameSumInl_X (a : Fin M) :
    renameSumInl k M n (MvPolynomial.X (ULift.up a)) =
      MvPolynomial.X (ULift.up (Sum.inl a) : ULift.{u} (Fin M ⊕ Fin n)) := by
  simp [renameSumInl]

private theorem pderiv_inr_X_inl_consolidated193 (i : Fin n) (a : Fin M) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.X (ULift.up (Sum.inl a) : ULift.{u} (Fin M ⊕ Fin n)) :
          MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k) = 0 := by
  classical
  simp [MvPolynomial.pderiv_X]

theorem pderiv_inr_renameSumInl (i : Fin n)
    (p : MvPolynomial (ULift.{u} (Fin M)) k) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (renameSumInl k M n p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on
  · rename_i c
    simp [renameSumInl_C]
  · rename_i q r hq hr
    simp [hq, hr]
  · rename_i q a hq
    obtain ⟨a⟩ := a
    rw [map_mul, renameSumInl_X, MvPolynomial.pderiv_mul, hq, pderiv_inr_X_inl_consolidated193]
    simp

private theorem projLeft_appTop_affineSpaceIndexedByToSpec_appTop_consolidated193 (y : Γ(Spec (CommRingCat.of k), ⊤)) :
    (projLeft k M n).appTop ((affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))).appTop y) =
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M ⊕ Fin n))).appTop y := by
  have h2 : ((projLeft k M n) ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))).appTop y
      = (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M ⊕ Fin n))).appTop y := by
    rw [projLeft_comp_affineSpaceIndexedByToSpec]
  exact h2

private theorem projLeft_appTop_mvPolynomialEquivGlobalSections_C_consolidated193 (c : k) :
    (projLeft k M n).appTop (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.C c)) =
      mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n)) (MvPolynomial.C c) := by
  rw [mvPolynomialEquivGlobalSections_C, mvPolynomialEquivGlobalSections_C, projLeft_appTop_affineSpaceIndexedByToSpec_appTop_consolidated193]

private theorem projLeft_appTop_mvPolynomialEquivGlobalSections_X_consolidated193 (a : ULift.{u} (Fin M)) :
    (projLeft k M n).appTop (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.X a)) =
      mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.X (ULift.up (Sum.inl a.down) : ULift.{u} (Fin M ⊕ Fin n))) := by
  obtain ⟨a⟩ := a
  simp

theorem mvPolynomialEquivGlobalSections_symm_projLeft_appTop (p : MvPolynomial (ULift.{u} (Fin M)) k) :
    (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
        ((projLeft k M n).appTop (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) p)) =
      renameSumInl k M n p := by
  have key :
      ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm.toRingHom).comp
          ((((projLeft k M n).appTop).hom).comp
            ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).toRingHom))
        = renameSumInl k M n := by
    apply MvPolynomial.ringHom_ext
    · intro c
      show (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
          ((projLeft k M n).appTop
            (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.C c)))
          = renameSumInl k M n (MvPolynomial.C c)
      rw [projLeft_appTop_mvPolynomialEquivGlobalSections_C_consolidated193, RingEquiv.symm_apply_apply, renameSumInl_C]
    · intro a
      show (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
          ((projLeft k M n).appTop
            (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.X a)))
          = renameSumInl k M n (MvPolynomial.X a)
      rw [projLeft_appTop_mvPolynomialEquivGlobalSections_X_consolidated193, RingEquiv.symm_apply_apply]
      simp [renameSumInl]
  exact RingHom.congr_fun key p

theorem mvPolynomialEquivGlobalSections_symm_comp_mvPolynomialToSumCoordinateRing :
    ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm.toRingHom).comp (mvPolynomialToSumCoordinateRing k M n) =
      MvPolynomial.eval₂Hom
        ((renameSumInl k M n).comp ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).symm.toRingHom))
        (fun i : Fin n =>
          MvPolynomial.X (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))) := by
  apply MvPolynomial.ringHom_ext
  · intro t
    have h := mvPolynomialEquivGlobalSections_symm_projLeft_appTop k M n
      ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).symm t)
    simp only [RingEquiv.apply_symm_apply] at h
    simpa using h
  · intro i
    simp

theorem mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm (mvPolynomialToSumCoordinateRing k M n p) =
      MvPolynomial.eval₂
        ((renameSumInl k M n).comp ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).symm.toRingHom))
        (fun i : Fin n =>
          MvPolynomial.X (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))) p :=
  RingHom.congr_fun (mvPolynomialEquivGlobalSections_symm_comp_mvPolynomialToSumCoordinateRing k M n) p

private theorem pderiv_inr_eval₂_X_inr_consolidated193 (f : Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
      MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k) (i : Fin n)
    (hf : ∀ t, MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n)) (f t) = 0)
    (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.eval₂ f
          (fun j : Fin n =>
            MvPolynomial.X (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n))) p) =
      MvPolynomial.eval₂ f
        (fun j : Fin n =>
          MvPolynomial.X (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n)))
        (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on
  · rename_i t
    rw [MvPolynomial.eval₂_C, MvPolynomial.pderiv_C, MvPolynomial.eval₂_zero]
    exact hf t
  · rename_i q r hq hr
    simp [MvPolynomial.eval₂_add, hq, hr]
  · rename_i q j hq
    have hX : MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.X (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n)) :
          MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k) =
        MvPolynomial.eval₂ f
          (fun l : Fin n =>
            MvPolynomial.X (ULift.up (Sum.inr l) : ULift.{u} (Fin M ⊕ Fin n)))
          (MvPolynomial.pderiv i (MvPolynomial.X j)) := by
      by_cases h : i = j
      · subst h
        simp
      · simp [MvPolynomial.pderiv_X, h]
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.pderiv_mul,
      MvPolynomial.eval₂_add, hq, hX]

theorem pderiv_mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing (i : Fin n)
    (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm (mvPolynomialToSumCoordinateRing k M n p)) =
      (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
        (mvPolynomialToSumCoordinateRing k M n (MvPolynomial.pderiv i p)) := by
  rw [mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing, mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing]
  refine pderiv_inr_eval₂_X_inr_consolidated193 k M n
    ((renameSumInl k M n).comp ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).symm.toRingHom)) i ?_ p
  intro t
  rw [RingHom.comp_apply]
  exact pderiv_inr_renameSumInl k M n i _


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupFlatDescent
section

open CategoryTheory.Limits

section

abbrev pullbackFstSchemeAt {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W) (i : ℕ) : Scheme.{u} :=
  pullback (pullback.fst g g) (t.projectionToBase i)

abbrev pullbackSndSchemeAt {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W) (i : ℕ) : Scheme.{u} :=
  pullback (pullback.snd g g) (t.projectionToBase i)

private theorem flat_fst_of_isPullback_consolidated223 {A B C D : Scheme.{u}} {p : A ⟶ B} {q : A ⟶ C}
    {f : B ⟶ D} {h : C ⟶ D} (H : IsPullback p q f h) [Flat h] :
    Flat p :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Flat) H.flip inferInstance

private theorem isPullback_iso_hom_comp_consolidated223 {P P' A B C : Scheme.{u}} {pf : P' ⟶ A} {ps : P' ⟶ B}
    {f : A ⟶ C} {g : B ⟶ C} (H : IsPullback pf ps f g) (e : P ≅ P') :
    IsPullback (e.hom ≫ pf) (e.hom ≫ ps) f g := by
  have E : IsPullback e.hom (e.hom ≫ ps) ps (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have h := E.paste_horiz H
  rwa [Category.id_comp] at h

theorem comap_map_center_eq_center_of_isPullback {W Y : Scheme.{u}} (g : W ⟶ Y) [Flat g]
    [QuasiCompact g] (t : SequenceOfBlowups W) (n : ℕ) {X : Scheme.{u}} (π : X ⟶ Y)
    (γ : t.schemeAt n ⟶ X) [Flat γ] [QuasiCompact γ]
    (hsq : IsPullback γ (t.projectionToBase n) π g)
    (e : pullbackFstSchemeAt g t n ≅ pullbackSndSchemeAt g t n)
    (hcenter : ((t.center n).comap (pullback.snd (pullback.snd g g) (t.projectionToBase n))).comap e.hom
      = (t.center n).comap (pullback.snd (pullback.fst g g) (t.projectionToBase n)))
    (hbase : e.hom ≫ pullback.fst (pullback.snd g g) (t.projectionToBase n)
      = pullback.fst (pullback.fst g g) (t.projectionToBase n))
    (hgamma : e.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n) ≫ γ
      = pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ γ) :
    ((t.center n).map γ).comap γ = t.center n := by
  have hpbSnd : IsPullback (e.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n))
      (pullback.fst (pullback.fst g g) (t.projectionToBase n)) (t.projectionToBase n) (pullback.snd g g) := by
    have h := isPullback_iso_hom_comp_consolidated223
      (IsPullback.of_hasPullback (pullback.snd g g) (t.projectionToBase n)).flip e
    rwa [hbase] at h
  have Big := hpbSnd.paste_vert (IsPullback.of_hasPullback g g).flip
  have hcond : pullback.fst (pullback.fst g g) (t.projectionToBase n) ≫ pullback.fst g g
      = pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ t.projectionToBase n := pullback.condition
  rw [hcond, ← hsq.w] at Big
  have comm : (e.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n)) ≫ γ
      = pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ γ := by
    rw [Category.assoc]
    exact hgamma
  have key : IsPullback (e.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n))
      (pullback.snd (pullback.fst g g) (t.projectionToBase n)) γ γ :=
    IsPullback.of_bot Big comm hsq
  refine comap_map_eq_self_of_isPullback γ key (t.center n) ?_
  rw [Scheme.IdealSheafData.comap_comp]
  exact hcenter

theorem exists_isPullback_blowup_proj_map_center {W X : Scheme.{u}} {t : SequenceOfBlowups W} {n : ℕ}
    (hn : n < t.length) {γ : t.schemeAt n ⟶ X} (hflat : Flat γ)
    (hc : ((t.center n).map γ).comap γ = t.center n) :
    ∃ q : t.schemeAt (n + 1) ⟶ Blowup.blowup ((t.center n).map γ),
      q ≫ Blowup.blowup.proj ((t.center n).map γ) = t.transitionMapSucc n ≫ γ ∧
        IsPullback q (t.transitionMapSucc n) (Blowup.blowup.proj ((t.center n).map γ)) γ := by
  have := hflat
  have h' : Blowup.IsBlowupAlongIdealSheaf (t.transitionMapSucc n) (((t.center n).map γ).comap γ) := by
    rw [hc]
    exact t.isBlowupAlongIdealSheaf_blowupMorphism n hn
  exact (Blowup.blowup.isBlowupAlongIdealSheaf_proj ((t.center n).map γ)).exists_isPullback_of_flat γ h'

def toBlowupOfMapCenter {W X : Scheme.{u}} {t : SequenceOfBlowups W} {n : ℕ}
    (hn : n < t.length) {γ : t.schemeAt n ⟶ X} (hflat : Flat γ)
    (hc : ((t.center n).map γ).comap γ = t.center n) :
    t.schemeAt (n + 1) ⟶ Blowup.blowup ((t.center n).map γ) :=
  (exists_isPullback_blowup_proj_map_center hn hflat hc).choose

section
variable {W X : Scheme.{u}} {t : SequenceOfBlowups W} {n : ℕ} (hn : n < t.length) {γ : t.schemeAt n ⟶ X} (hflat : Flat γ) (hc : ((t.center n).map γ).comap γ = t.center n)

theorem toBlowupOfMapCenter_comp_proj :
    toBlowupOfMapCenter hn hflat hc ≫ Blowup.blowup.proj ((t.center n).map γ) = t.transitionMapSucc n ≫ γ :=
  (exists_isPullback_blowup_proj_map_center hn hflat hc).choose_spec.1

theorem isPullback_toBlowupOfMapCenter :
    IsPullback (toBlowupOfMapCenter hn hflat hc) (t.transitionMapSucc n)
      (Blowup.blowup.proj ((t.center n).map γ)) γ :=
  (exists_isPullback_blowup_proj_map_center hn hflat hc).choose_spec.2


end

section
variable {W Y X : Scheme.{u}} (g : W ⟶ Y)

theorem isPullback_toBlowupOfMapCenter_projectionToBase (t : SequenceOfBlowups W)
    {n : ℕ} (hn : n < t.length) (π : X ⟶ Y) {γ : t.schemeAt n ⟶ X}
    (hflat : Flat γ) (hc : ((t.center n).map γ).comap γ = t.center n)
    (hsq : IsPullback γ (t.projectionToBase n) π g) :
    IsPullback (toBlowupOfMapCenter hn hflat hc) (t.projectionToBase (n + 1))
      (Blowup.blowup.proj ((t.center n).map γ) ≫ π) g := by
  have h := (isPullback_toBlowupOfMapCenter hn hflat hc).paste_vert hsq
  rwa [← t.projectionToBase_succ n] at h

theorem toBlowupOfMapCenter_cocycle [Flat g]
    [QuasiCompact g] (t : SequenceOfBlowups W) {n : ℕ} (hn : n < t.length) (π : X ⟶ Y)
    {γ : t.schemeAt n ⟶ X} (hflat : Flat γ)
    (hc : ((t.center n).map γ).comap γ = t.center n)
    (_hsq : IsPullback γ (t.projectionToBase n) π g)
    (e : pullbackFstSchemeAt g t n ≅ pullbackSndSchemeAt g t n)
    (e' : pullbackFstSchemeAt g t (n + 1) ≅ pullbackSndSchemeAt g t (n + 1))
    (hee : e'.hom ≫ t.pullbackTransitionMap (pullback.snd g g) (Nat.le_succ n)
      = t.pullbackTransitionMap (pullback.fst g g) (Nat.le_succ n) ≫ e.hom)
    (hgamma : e.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n) ≫ γ
      = pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ γ) :
    e'.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase (n + 1)) ≫ toBlowupOfMapCenter hn hflat hc
      = pullback.snd (pullback.fst g g) (t.projectionToBase (n + 1)) ≫ toBlowupOfMapCenter hn hflat hc := by
  have := hflat
  have hfst : Flat (pullback.fst g g) :=
    flat_fst_of_isPullback_consolidated223 (IsPullback.of_hasPullback g g)
  have hdc : Flat (toBlowupOfMapCenter hn hflat hc) :=
    flat_fst_of_isPullback_consolidated223 (isPullback_toBlowupOfMapCenter hn hflat hc)
  have hsnd1 : pullback.snd (pullback.fst g g) (t.projectionToBase (n + 1)) ≫ t.transitionMapSucc n
      = t.pullbackTransitionMap (pullback.fst g g) (Nat.le_succ n)
        ≫ pullback.snd (pullback.fst g g) (t.projectionToBase n) :=
    (t.pullbackTransitionMap_snd (pullback.fst g g) (Nat.le_succ n)).symm
  have hsnd2 : pullback.snd (pullback.snd g g) (t.projectionToBase (n + 1)) ≫ t.transitionMapSucc n
      = t.pullbackTransitionMap (pullback.snd g g) (Nat.le_succ n)
        ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n) :=
    (t.pullbackTransitionMap_snd (pullback.snd g g) (Nat.le_succ n)).symm
  have hsnd1' : pullback.snd (pullback.fst g g) (t.projectionToBase (n + 1)) ≫ t.transitionMapSucc n ≫ γ
      = t.pullbackTransitionMap (pullback.fst g g) (Nat.le_succ n)
        ≫ pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ γ := by
    rw [← Category.assoc, ← Category.assoc, hsnd1]
  have hsnd2' : pullback.snd (pullback.snd g g) (t.projectionToBase (n + 1)) ≫ t.transitionMapSucc n ≫ γ
      = t.pullbackTransitionMap (pullback.snd g g) (Nat.le_succ n)
        ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n) ≫ γ := by
    rw [← Category.assoc, ← Category.assoc, hsnd2]
  have hk : Blowup.IsLocallyGeneratedByNonZeroDivisor (((t.center n).map γ).comap
      (pullback.snd (pullback.fst g g) (t.projectionToBase (n + 1)) ≫
        toBlowupOfMapCenter hn hflat hc ≫ Blowup.blowup.proj ((t.center n).map γ))) := by
    rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    exact Blowup.IsLocallyGeneratedByNonZeroDivisor.comap_of_flat
      (Blowup.IsLocallyGeneratedByNonZeroDivisor.comap_of_flat (Blowup.blowup.isBlowupAlongIdealSheaf_proj ((t.center n).map γ)).1
        (toBlowupOfMapCenter hn hflat hc)) _
  refine Blowup.IsBlowupAlongIdealSheaf.hom_ext_of_comp_eq (Blowup.blowup.isBlowupAlongIdealSheaf_proj ((t.center n).map γ)) hk ?_ ?_
  · simp only [Category.assoc]
    rw [toBlowupOfMapCenter_comp_proj hn hflat hc, hsnd2', hsnd1', ← Category.assoc, hee,
      Category.assoc, hgamma]
  · rw [Category.assoc]


end

structure DescendedBlowupData {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W) (n : ℕ)
    {X : Scheme.{u}} (π : X ⟶ Y) (γ : t.schemeAt n ⟶ X)
    (e' : pullbackFstSchemeAt g t (n + 1) ≅ pullbackSndSchemeAt g t (n + 1)) where
  total : Scheme.{u}
  totalStruct : total ⟶ Y
  down : total ⟶ X
  totalCenter : X.IdealSheafData
  totalComparison : t.schemeAt (n + 1) ⟶ total
  center_comap : totalCenter.comap γ = t.center n
  isBlowup_down : Blowup.IsBlowupAlongIdealSheaf down totalCenter
  sq_comm : totalComparison ≫ down = t.transitionMapSucc n ≫ γ
  isPullback_sq : IsPullback totalComparison (t.transitionMapSucc n) down γ
  isPullback_base : IsPullback totalComparison (t.projectionToBase (n + 1)) totalStruct g
  hom_comparison :
    e'.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase (n + 1)) ≫ totalComparison
      = pullback.snd (pullback.fst g g) (t.projectionToBase (n + 1)) ≫ totalComparison
  structY_eq : totalStruct = down ≫ π

def descendedBlowupData {W Y : Scheme.{u}} (g : W ⟶ Y) [Flat g]
    [QuasiCompact g] (t : SequenceOfBlowups W) {n : ℕ} (hn : n < t.length)
    {X : Scheme.{u}} (π : X ⟶ Y) (γ : t.schemeAt n ⟶ X)
    (hsq : IsPullback γ (t.projectionToBase n) π g)
    (e : pullbackFstSchemeAt g t n ≅ pullbackSndSchemeAt g t n)
    (e' : pullbackFstSchemeAt g t (n + 1) ≅ pullbackSndSchemeAt g t (n + 1))
    (hee : e'.hom ≫ t.pullbackTransitionMap (pullback.snd g g) (Nat.le_succ n)
      = t.pullbackTransitionMap (pullback.fst g g) (Nat.le_succ n) ≫ e.hom)
    (hcenter : ((t.center n).comap (pullback.snd (pullback.snd g g) (t.projectionToBase n))).comap e.hom
      = (t.center n).comap (pullback.snd (pullback.fst g g) (t.projectionToBase n)))
    (hbase : e.hom ≫ pullback.fst (pullback.snd g g) (t.projectionToBase n)
      = pullback.fst (pullback.fst g g) (t.projectionToBase n))
    (hgamma : e.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n) ≫ γ
      = pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ γ) :
    DescendedBlowupData g t n π γ e' :=
  haveI hfl : Flat γ := flat_fst_of_isPullback_consolidated223 hsq
  haveI _hqc : QuasiCompact γ := quasiCompact_of_isPullback hsq.flip
  have hc : ((t.center n).map γ).comap γ = t.center n :=
    comap_map_center_eq_center_of_isPullback g t n π γ hsq e hcenter hbase hgamma
  { total := Blowup.blowup ((t.center n).map γ)
    totalStruct := Blowup.blowup.proj ((t.center n).map γ) ≫ π
    down := Blowup.blowup.proj ((t.center n).map γ)
    totalCenter := (t.center n).map γ
    totalComparison := toBlowupOfMapCenter hn hfl hc
    center_comap := hc
    isBlowup_down := Blowup.blowup.isBlowupAlongIdealSheaf_proj ((t.center n).map γ)
    sq_comm := toBlowupOfMapCenter_comp_proj hn hfl hc
    isPullback_sq := isPullback_toBlowupOfMapCenter hn hfl hc
    isPullback_base := isPullback_toBlowupOfMapCenter_projectionToBase g t hn π hfl hc hsq
    hom_comparison := toBlowupOfMapCenter_cocycle g t hn π hfl hc hsq e e' hee hgamma
    structY_eq := rfl }

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
section

open CategoryTheory.Limits Opposite

section

namespace SequenceOfBlowups

variable {X : Scheme.{u}}

@[simp]
theorem transitionMap_self_eq_id (s : SequenceOfBlowups X) {i : ℕ} (h : i ≤ i) :
    s.transitionMap h = 𝟙 (s.schemeAt i) := by
  rw [s.transitionMap_def, show ((homOfLE h).op : op i ⟶ op i) = 𝟙 (op i) from rfl, s.tower.map_id]

instance instIsIsoStructMapZero (s : SequenceOfBlowups X) : IsIso (s.projectionToBase 0) := by
  rw [s.projectionToBase_zero]
  infer_instance

@[reassoc, simp]
theorem pullbackTransitionMap_comp_fst (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) {i i' : ℕ}
    (h : i ≤ i') :
    s.pullbackTransitionMap φ h ≫ pullback.fst φ (s.projectionToBase i) = pullback.fst φ (s.projectionToBase i') :=
  s.pullbackTransitionMap_fst φ h

@[reassoc, simp]
theorem pullbackTransitionMap_comp_snd (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) {i i' : ℕ}
    (h : i ≤ i') :
    s.pullbackTransitionMap φ h ≫ pullback.snd φ (s.projectionToBase i) =
      pullback.snd φ (s.projectionToBase i') ≫ s.transitionMap h :=
  s.pullbackTransitionMap_snd φ h

section
variable (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X)

private theorem pullbackTransitionMap_refl_consolidated224 {a : ℕ} (h : a ≤ a) :
    s.pullbackTransitionMap φ h = 𝟙 (pullback φ (s.projectionToBase a)) := by
  refine pullback.hom_ext ?_ ?_
  · rw [s.pullbackTransitionMap_fst, Category.id_comp]
  · rw [s.pullbackTransitionMap_snd, s.transitionMap_self_eq_id, Category.comp_id, Category.id_comp]

private theorem pullbackTransitionMap_eq_comp_consolidated224 {a b c : ℕ} (hba : b ≤ a) (hcb : c ≤ b) (hca : c ≤ a) :
    s.pullbackTransitionMap φ hca = s.pullbackTransitionMap φ hba ≫ s.pullbackTransitionMap φ hcb := by
  refine pullback.hom_ext ?_ ?_
  · rw [s.pullbackTransitionMap_fst, Category.assoc, s.pullbackTransitionMap_fst, s.pullbackTransitionMap_fst]
  · rw [s.pullbackTransitionMap_snd, Category.assoc, s.pullbackTransitionMap_snd, ← Category.assoc,
      s.pullbackTransitionMap_snd, Category.assoc, s.transitionMap_trans]


end

def baseChangeTower (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) : ℕᵒᵖ ⥤ Scheme.{u} where
  obj i := pullback φ (s.projectionToBase i.unop)
  map {_ _} f := s.pullbackTransitionMap φ (leOfHom f.unop)
  map_id i := pullbackTransitionMap_refl_consolidated224 s φ (leOfHom (𝟙 i).unop)
  map_comp {_ _ _} f g :=
    pullbackTransitionMap_eq_comp_consolidated224 s φ (leOfHom f.unop) (leOfHom g.unop) (leOfHom (f ≫ g).unop)

@[simp]
theorem baseChangeTower_obj (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) (i : ℕ) :
    (s.baseChangeTower φ).obj (op i) = pullback φ (s.projectionToBase i) := rfl

@[simp]
theorem baseChangeTower_map (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) {i i' : ℕ}
    (h : i ≤ i') :
    (s.baseChangeTower φ).map (homOfLE h).op = s.pullbackTransitionMap φ h := rfl

theorem isIso_pullback_fst_projectionToBase_zero (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) :
    IsIso (pullback.fst φ (s.projectionToBase 0)) := by
  have hcomm : (𝟙 X') ≫ φ = (φ ≫ inv (s.projectionToBase 0)) ≫ s.projectionToBase 0 := by
    simp
  refine ⟨pullback.lift (𝟙 X') (φ ≫ inv (s.projectionToBase 0)) hcomm, ?_, ?_⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, ← Category.assoc,
        pullback.condition, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · rw [pullback.lift_fst]

instance instIsIsoPullbackFstStructMapZero (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) :
    IsIso (pullback.fst φ (s.projectionToBase 0)) :=
  s.isIso_pullback_fst_projectionToBase_zero φ

def baseChangeTowerObjZeroIso (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) :
    (s.baseChangeTower φ).obj (op 0) ≅ X' :=
  @asIso Scheme.{u} _ _ _ (pullback.fst φ (s.projectionToBase 0)) (s.isIso_pullback_fst_projectionToBase_zero φ)

@[simp]
theorem baseChangeTowerObjZeroIso_hom (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) :
    (s.baseChangeTowerObjZeroIso φ).hom = pullback.fst φ (s.projectionToBase 0) := rfl

section
variable (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X)

theorem isPullback_pullbackTransitionMap (i : ℕ) :
    IsPullback (pullback.snd φ (s.projectionToBase (i + 1))) (s.pullbackTransitionMap φ (Nat.le_succ i))
      (s.transitionMapSucc i) (pullback.snd φ (s.projectionToBase i)) := by
  have t : IsPullback (pullback.snd φ (s.projectionToBase i)) (pullback.fst φ (s.projectionToBase i))
      (s.projectionToBase i) φ := (IsPullback.of_hasPullback φ (s.projectionToBase i)).flip
  have hfst : s.pullbackTransitionMap φ (Nat.le_succ i) ≫ pullback.fst φ (s.projectionToBase i)
      = pullback.fst φ (s.projectionToBase (i + 1)) := s.pullbackTransitionMap_fst φ (Nat.le_succ i)
  have hstruct : s.transitionMapSucc i ≫ s.projectionToBase i = s.projectionToBase (i + 1) := by
    rw [s.blowupMorphism_eq_transitionMap, s.transitionMap_comp_projectionToBase]
  have hsnd : pullback.snd φ (s.projectionToBase (i + 1)) ≫ s.transitionMapSucc i
      = s.pullbackTransitionMap φ (Nat.le_succ i) ≫ pullback.snd φ (s.projectionToBase i) := by
    rw [s.pullbackTransitionMap_snd, s.blowupMorphism_eq_transitionMap]
  have sq : IsPullback (pullback.snd φ (s.projectionToBase (i + 1)))
      (s.pullbackTransitionMap φ (Nat.le_succ i) ≫ pullback.fst φ (s.projectionToBase i))
      (s.transitionMapSucc i ≫ s.projectionToBase i) φ := by
    rw [hfst, hstruct]
    exact (IsPullback.of_hasPullback φ (s.projectionToBase (i + 1))).flip
  exact sq.of_bot hsnd t

private theorem isBlowupAlongIdealSheaf_baseChangeTower_map_consolidated224 [Flat φ] (i : ℕ) (hi : i < s.length) :
    Blowup.IsBlowupAlongIdealSheaf ((s.baseChangeTower φ).map (homOfLE (Nat.le_succ i)).op)
      ((s.center i).comap (pullback.snd φ (s.projectionToBase i))) :=
  (s.isBlowupAlongIdealSheaf_blowupMorphism i hi).of_isPullback_of_flat (pullback.snd φ (s.projectionToBase i))
    (s.isPullback_pullbackTransitionMap φ i)


end

def baseChange (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) [Flat φ] :
    SequenceOfBlowups X' where
  length := s.length
  tower := s.baseChangeTower φ
  isoZero := s.baseChangeTowerObjZeroIso φ
  center i := (s.center i).comap (pullback.snd φ (s.projectionToBase i))
  isBlowup i hi := isBlowupAlongIdealSheaf_baseChangeTower_map_consolidated224 s φ i hi

@[simp]
theorem baseChange_length (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X)
    [Flat φ] : (s.baseChange φ).length = s.length := rfl

@[simp]
theorem baseChange_schemeAt (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X)
    [Flat φ] (i : ℕ) :
    (s.baseChange φ).schemeAt i = pullback φ (s.projectionToBase i) := rfl

@[simp]
theorem baseChange_blowupMorphism (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X)
    [Flat φ] (i : ℕ) :
    (s.baseChange φ).transitionMapSucc i = s.pullbackTransitionMap φ (Nat.le_succ i) := rfl

@[simp]
theorem baseChange_isoObjZero_hom (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X)
    [Flat φ] :
    (s.baseChange φ).isoZero.hom = pullback.fst φ (s.projectionToBase 0) := rfl

@[simp]
theorem baseChange_center (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X)
    [Flat φ] (i : ℕ) :
    (s.baseChange φ).center i = (s.center i).comap (pullback.snd φ (s.projectionToBase i)) := rfl

end SequenceOfBlowups

theorem isStrictPullbackSequenceOfBlowups_baseChange {X X' : Scheme.{u}} (s : SequenceOfBlowups X) (φ : X' ⟶ X)
    [Flat φ] : IsStrictPullbackBlowupSeq φ (s.baseChange φ) s := by
  refine ⟨rfl, fun i _ => pullback.snd φ (s.projectionToBase i), ?_, ?_, ?_⟩
  · show pullback.snd φ (s.projectionToBase 0) ≫ s.isoZero.hom
      = pullback.fst φ (s.projectionToBase 0) ≫ φ
    rw [← s.projectionToBase_zero, pullback.condition]
  · intro i _
    exact s.isPullback_pullbackTransitionMap φ i
  · intro i _
    rfl

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
section

open CategoryTheory.Limits Opposite

section

namespace BlowupSequenceData

variable {X : Scheme.{u}}

def transitionMap (d : BlowupSequenceData X) {i i' : ℕ} (h : i ≤ i') : d.obj i' ⟶ d.obj i :=
  d.toSequenceOfBlowups.transitionMap h

section
variable (d : BlowupSequenceData X)

theorem toSequenceOfBlowups_transitionMap {i i' : ℕ} (h : i ≤ i') :
    d.toSequenceOfBlowups.transitionMap h = d.transitionMap h := rfl

theorem transitionMap_comp_transitionMap {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) :
    d.transitionMap hjl ≫ d.transitionMap hij = d.transitionMap (hij.trans hjl) :=
  d.toSequenceOfBlowups.transitionMap_trans hij hjl

theorem transitionMap_refl (i : ℕ) : d.transitionMap (le_refl i) = 𝟙 (d.obj i) := by
  exact d.toSequenceOfBlowups.transitionMap_self_eq_id (le_refl i)

theorem transitionMap_succ (i : ℕ) : d.transitionMap (Nat.le_succ i) = d.map i := by
  have h1 : d.toSequenceOfBlowups.transitionMapSucc i = d.map i := d.toSequenceOfBlowups_blowupMorphism i
  have h2 : d.toSequenceOfBlowups.transitionMapSucc i = d.toSequenceOfBlowups.transitionMap (Nat.le_succ i) :=
    d.toSequenceOfBlowups.blowupMorphism_eq_transitionMap i
  exact h2.symm.trans h1


end

@[reassoc]
theorem transitionMap_zero_comp_isoObjZero_hom (d : BlowupSequenceData X) (n : ℕ) :
    d.transitionMap (Nat.zero_le n) ≫ d.isoZero.hom = d.projectionToBase n := by
  have h := d.toSequenceOfBlowups.projectionToBase_def n
  rw [BlowupSequenceData.toSequenceOfBlowups_projectionToBase, BlowupSequenceData.toSequenceOfBlowups_transitionMap, BlowupSequenceData.toSequenceOfBlowups_isoObjZero] at h
  exact h.symm

section
variable (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))

private theorem append_schemeAt_length_add_zero_consolidated245 :
    (s.append t).obj (s.length + 0) = s.obj s.length := by
  have h : s.length + 0 ≤ s.length := le_of_eq (Nat.add_zero _)
  exact (append_schemeAt_of_le_length s t h).trans (congrArg s.obj (Nat.add_zero _))

private theorem append_schemeAt_length_add_succ_consolidated245 (i : ℕ) : (s.append t).obj (s.length + (i + 1)) = t.obj (i + 1) := by
  have h : s.length < s.length + (i + 1) := by omega
  have h2 : s.length + (i + 1) - s.length = i + 1 := by omega
  rw [append_schemeAt_of_length_lt s t h, h2]


end

def concatObjAddIso (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) :
    ∀ i : ℕ, (s.append t).obj (s.length + i) ≅ t.obj i
  | 0 => eqToIso (append_schemeAt_length_add_zero_consolidated245 s t) ≪≫ t.isoZero.symm
  | (i + 1) => eqToIso (append_schemeAt_length_add_succ_consolidated245 s t i)

section
variable {Y : Scheme.{u}} (d : BlowupSequenceData Y)

private theorem eqToHom_comp_blowupMorphism_zero_isoObjZero_cancel_consolidated245 {U V : Scheme.{u}}
    (h1 : U = d.obj 1) (h2 : Y = V) (h3 : V = Y) (h4 : U = d.obj 1) :
    (eqToHom h1 ≫ d.map 0 ≫ d.isoZero.hom ≫ eqToHom h2) ≫ eqToHom h3 ≫ d.isoZero.inv =
      eqToHom h4 ≫ d.map 0 := by
  subst h2
  simp

private theorem eqToHom_comp_blowupMorphism_congr_consolidated245 {a b : ℕ} (hab : a = b)
    {U V : Scheme.{u}} (hU : U = d.obj (a + 1)) (hV : V = d.obj a)
    (e1 : V = d.obj b) (e2 : U = d.obj (b + 1)) :
    (eqToHom hU ≫ d.map a ≫ eqToHom hV.symm) ≫ eqToHom e1 = eqToHom e2 ≫ d.map b := by
  subst hab
  subst hU
  subst hV
  simp


end

section
variable (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))

private theorem append_blowupMorphism_zero_comp_concatObjAddIso_consolidated245 :
    (s.append t).map s.length ≫ (concatObjAddIso s t 0).hom =
      (concatObjAddIso s t 1).hom ≫ t.map 0 := by
  rw [append_blowupMorphism_length s t]
  exact eqToHom_comp_blowupMorphism_zero_isoObjZero_cancel_consolidated245 t (append_schemeAt_length_succ s t)
    (append_schemeAt_of_le_length s t (le_refl s.length)).symm (append_schemeAt_length_add_zero_consolidated245 s t)
    (append_schemeAt_length_add_succ_consolidated245 s t 0)

private theorem append_blowupMorphism_succ_comp_concatObjAddIso_consolidated245 (k : ℕ) :
    (s.append t).map (s.length + (k + 1)) ≫ (concatObjAddIso s t (k + 1)).hom =
      (concatObjAddIso s t (k + 1 + 1)).hom ≫ t.map (k + 1) := by
  have hgt : s.length < s.length + (k + 1) := by omega
  have hab : s.length + (k + 1) - s.length = k + 1 := by omega
  rw [append_blowupMorphism_of_length_lt s t hgt]
  exact eqToHom_comp_blowupMorphism_congr_consolidated245 t hab (append_schemeAt_succ_of_length_lt s t hgt) (append_schemeAt_of_length_lt s t hgt)
    (append_schemeAt_length_add_succ_consolidated245 s t k) (append_schemeAt_length_add_succ_consolidated245 s t (k + 1))


end

@[reassoc]
theorem append_blowupMorphism_comp_concatObjAddIso (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) (i : ℕ) :
    (s.append t).map (s.length + i) ≫ (concatObjAddIso s t i).hom =
      (concatObjAddIso s t (i + 1)).hom ≫ t.map i := by
  cases i with
  | zero => exact append_blowupMorphism_zero_comp_concatObjAddIso_consolidated245 s t
  | succ k => exact append_blowupMorphism_succ_comp_concatObjAddIso_consolidated245 s t k

@[reassoc]
theorem append_transitionMap_comp_concatObjAddIso (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) {i i' : ℕ}
    (h : i ≤ i') :
    (s.append t).transitionMap (Nat.add_le_add_left h s.length) ≫ (concatObjAddIso s t i).hom =
      (concatObjAddIso s t i').hom ≫ t.transitionMap h := by
  induction i', h using Nat.le_induction with
  | base =>
      rw [transitionMap_refl, transitionMap_refl, Category.id_comp, Category.comp_id]
  | succ n hn ih =>
      have e1 : (s.append t).transitionMap (Nat.le_succ (s.length + n)) ≫
            (s.append t).transitionMap (Nat.add_le_add_left hn s.length) =
          (s.append t).transitionMap (Nat.add_le_add_left (Nat.le_succ_of_le hn) s.length) :=
        (s.append t).transitionMap_comp_transitionMap (Nat.add_le_add_left hn s.length) (Nat.le_succ (s.length + n))
      have e2 : (s.append t).transitionMap (Nat.le_succ (s.length + n)) =
          (s.append t).map (s.length + n) :=
        (s.append t).transitionMap_succ (s.length + n)
      have e3 : t.transitionMap (Nat.le_succ n) ≫ t.transitionMap hn = t.transitionMap (Nat.le_succ_of_le hn) :=
        t.transitionMap_comp_transitionMap hn (Nat.le_succ n)
      have e4 : t.transitionMap (Nat.le_succ n) = t.map n := t.transitionMap_succ n
      calc (s.append t).transitionMap (Nat.add_le_add_left (Nat.le_succ_of_le hn) s.length) ≫
            (concatObjAddIso s t i).hom
          = ((s.append t).map (s.length + n) ≫
              (s.append t).transitionMap (Nat.add_le_add_left hn s.length)) ≫
              (concatObjAddIso s t i).hom := by
            rw [← e2, e1]
        _ = (s.append t).map (s.length + n) ≫
              ((s.append t).transitionMap (Nat.add_le_add_left hn s.length) ≫ (concatObjAddIso s t i).hom) :=
            Category.assoc _ _ _
        _ = (s.append t).map (s.length + n) ≫ ((concatObjAddIso s t n).hom ≫ t.transitionMap hn) := by
            rw [ih]
        _ = ((s.append t).map (s.length + n) ≫ (concatObjAddIso s t n).hom) ≫ t.transitionMap hn :=
            (Category.assoc _ _ _).symm
        _ = ((concatObjAddIso s t (n + 1)).hom ≫ t.map n) ≫ t.transitionMap hn := by
            rw [append_blowupMorphism_comp_concatObjAddIso]
        _ = (concatObjAddIso s t (n + 1)).hom ≫ (t.map n ≫ t.transitionMap hn) := Category.assoc _ _ _
        _ = (concatObjAddIso s t (n + 1)).hom ≫ t.transitionMap (Nat.le_succ_of_le hn) := by
            rw [← e4, e3]

end BlowupSequenceData

structure SequenceOfBlowupsPullback {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) where
  idx : ℕ → ℕ
  map : ∀ j : ℕ, j ≤ s'.length → (s'.schemeAt j ⟶ s.schemeAt (idx j))
  idx_length : idx s'.length = s.length
  idx_lt : ∀ j : ℕ, j < s'.length → idx j < s.length
  idx_strictMono : ∀ j : ℕ, j < s'.length → idx j < idx (j + 1)
  isPullback : ∀ (j : ℕ) (hj : j ≤ s'.length),
    IsPullback (map j hj) (s'.projectionToBase j) (s.projectionToBase (idx j)) φ
  step : ∀ (j : ℕ) (hj : j < s'.length),
    s'.transitionMapSucc j ≫ map j (le_of_lt hj) =
      map (j + 1) hj ≫ s.transitionMap (le_of_lt (idx_strictMono j hj))
  center_comap : ∀ (j : ℕ) (hj : j < s'.length),
    s'.center j = (s.center (idx j)).comap (map j (le_of_lt hj))
  center_ne_top : ∀ j : ℕ, j < s'.length → s'.center j ≠ ⊤
  omitted : ∀ (i : ℕ), i < s.length → (∀ j : ℕ, j < s'.length → idx j ≠ i) →
    ∀ z : ↥(s.schemeAt i), z ∈ (s.center i).support → ∀ x' : ↥X',
      φ.base x' ≠ (s.projectionToBase i).base z

namespace SequenceOfBlowupsPullback

variable {X X' : Scheme.{u}} {φ : X' ⟶ X}

def lastMap {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s) :
    s'.schemeAt s'.length ⟶ s.schemeAt s.length :=
  c.map s'.length le_rfl ≫ eqToHom (congrArg s.schemeAt c.idx_length)

private theorem isPullback_comp_eqToHom_consolidated245 {A B Y : Scheme.{u}} {ψ : B ⟶ A} {t : SequenceOfBlowups A}
    {n m : ℕ} (hn : n = m) (f : Y ⟶ t.schemeAt n) (g : Y ⟶ B)
    (h : IsPullback f g (t.projectionToBase n) ψ) :
    IsPullback (f ≫ eqToHom (congrArg t.schemeAt hn)) g (t.projectionToBase m) ψ := by
  subst hn
  rw [eqToHom_refl, Category.comp_id]
  exact h

section
variable {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s)

theorem isPullback_lastMap :
    IsPullback c.lastMap (s'.projectionToBase s'.length) (s.projectionToBase s.length) φ := by
  show IsPullback (c.map s'.length le_rfl ≫ eqToHom (congrArg s.schemeAt c.idx_length))
      (s'.projectionToBase s'.length) (s.projectionToBase s.length) φ
  exact isPullback_comp_eqToHom_consolidated245 c.idx_length _ _ (c.isPullback s'.length le_rfl)

private theorem index_lt_index_of_lt_consolidated245 :
    ∀ i j : ℕ, j ≤ s'.length → i < j → c.idx i < c.idx j := by
  intro i j
  induction j with
  | zero => intro _ h; exact absurd h (Nat.not_lt_zero i)
  | succ n ih =>
      intro hn hij
      have hn' : n < s'.length := Nat.lt_of_succ_le hn
      have hstep : c.idx n < c.idx (n + 1) := c.idx_strictMono n hn'
      by_cases hcase : i < n
      · exact lt_trans (ih (le_of_lt hn') hcase) hstep
      · have hie : i = n := by omega
        subst hie
        exact hstep


end

private theorem pullback_condition_base_apply_consolidated245 {Y Z W : Scheme.{u}} (f : Y ⟶ W) (g : Z ⟶ W)
    (x : ↥(pullback f g)) :
    f.base ((pullback.fst f g).base x) = g.base ((pullback.snd f g).base x) := by
  have h : (pullback.fst f g ≫ f).base x = (pullback.snd f g ≫ g).base x := by
    rw [pullback.condition]
  simpa using h

private theorem exists_mem_support_of_ne_top_consolidated245 {Y : Scheme.{u}} (J : Y.IdealSheafData) (h : J ≠ ⊤) :
    ∃ x : ↥Y, x ∈ J.support := by
  by_contra hc
  push Not at hc
  have hb : J.support = ⊥ := by
    ext y
    simpa using hc y
  exact h ((AlgebraicGeometry.Scheme.IdealSheafData.support_eq_bot_iff J).mp hb)

private def isoPullback_consolidated245 {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s)
    (i : ℕ) (hi : i ≤ s'.length) : s'.schemeAt i ≅ pullback φ (s.projectionToBase (c.idx i)) :=
  CategoryTheory.IsPullback.isoPullback ((c.isPullback i hi).flip)

section
variable {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s)
include c

private theorem pullbackIso_hom_fst_consolidated245 (i : ℕ) (hi : i ≤ s'.length) :
    (isoPullback_consolidated245 c i hi).hom ≫ pullback.fst φ (s.projectionToBase (c.idx i)) = s'.projectionToBase i :=
  IsPullback.isoPullback_hom_fst _

private theorem pullbackIso_hom_snd_consolidated245 (i : ℕ) (hi : i ≤ s'.length) :
    (isoPullback_consolidated245 c i hi).hom ≫ pullback.snd φ (s.projectionToBase (c.idx i)) = c.map i hi :=
  IsPullback.isoPullback_hom_snd _

theorem isPullbackSequenceOfBlowups : IsPullbackBlowupSequence φ s' s := by
  refine ⟨c.idx, fun i hi => isoPullback_consolidated245 c i hi, c.idx_lt, index_lt_index_of_lt_consolidated245 c, c.idx_length,
    ?_, ?_, ?_, ?_⟩
  · intro i hi
    constructor
    · rintro ⟨x, hx⟩
      by_contra hcon
      push Not at hcon
      exact c.omitted i hi hcon _ (Scheme.IdealSheafData.mem_support_comap.mp hx) _
        (pullback_condition_base_apply_consolidated245 φ (s.projectionToBase i) x)
    · rintro ⟨j, hj, rfl⟩
      refine exists_mem_support_of_ne_top_consolidated245 _ ?_
      intro htop
      refine c.center_ne_top j hj ?_
      rw [c.center_comap j hj, ← pullbackIso_hom_snd_consolidated245 c j (le_of_lt hj),
        Scheme.IdealSheafData.comap_comp, htop,
        AlgebraicGeometry.Scheme.IdealSheafData.comap_top]
  · intro i hi
    exact pullbackIso_hom_fst_consolidated245 c i hi
  · intro i hi hr
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullbackIso_hom_fst_consolidated245, Category.assoc, SequenceOfBlowups.pullbackTransitionMap_comp_fst,
        pullbackIso_hom_fst_consolidated245, SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_comp_projectionToBase]
    · rw [Category.assoc, pullbackIso_hom_snd_consolidated245, Category.assoc, SequenceOfBlowups.pullbackTransitionMap_comp_snd,
        ← Category.assoc, pullbackIso_hom_snd_consolidated245]
      exact c.step i hi
  · intro i hi
    rw [pullbackIso_hom_snd_consolidated245]
    exact c.center_comap i hi


end

section
variable {d' : BlowupSequenceData X'} {d : BlowupSequenceData X} (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups)

theorem blowupSequenceData_index_lt_length (j : ℕ) (hj : j < d'.length) :
    c.idx j < d.length := by
  have h : j < d'.toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length]
    exact hj
  have h2 := c.idx_lt j h
  rwa [BlowupSequenceData.toSequenceOfBlowups_length] at h2

theorem blowupSequenceData_index_lt_index_succ (j : ℕ) (hj : j < d'.length) :
    c.idx j < c.idx (j + 1) :=
  c.idx_strictMono j (by rw [BlowupSequenceData.toSequenceOfBlowups_length]; exact hj)

theorem index_length_eq_length : c.idx d'.length = d.length := by
  simpa only [BlowupSequenceData.toSequenceOfBlowups_length] using c.idx_length


end

@[reassoc]
theorem blowupSequenceData_blowupMorphism_comp_map {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (j : ℕ) (hj : j < d'.length) :
    d'.map j ≫ c.map j (le_of_lt hj) =
      c.map (j + 1) hj ≫ d.transitionMap (le_of_lt (c.blowupSequenceData_index_lt_index_succ j hj)) := by
  have hj' : j < d'.toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length]
    exact hj
  have h := c.step j hj'
  rw [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism] at h
  exact h

section

def concatIndex (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ) : ℕ :=
  if j < s'.length then c.idx j else s.length + e.idx (j - s'.length)

section
variable (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length)) (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups) (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ)

theorem concatIndex_of_lt (h : j < s'.length) :
    concatIndex s t s' t' c e j = c.idx j := if_pos h

theorem concatIndex_of_ge (h : s'.length ≤ j) :
    concatIndex s t s' t' c e j = s.length + e.idx (j - s'.length) := if_neg (not_lt.2 h)

private theorem append_schemeAt_concatIndex_of_lt_consolidated245 (h : j < s'.length) :
    s.obj (c.idx j) = (s.append t).obj (concatIndex s t s' t' c e j) := by
  rw [concatIndex_of_lt s t s' t' c e j h]
  exact (BlowupSequenceData.append_schemeAt_of_le_length s t (le_of_lt (c.blowupSequenceData_index_lt_length j h))).symm


end

private theorem append_schemeAt_eq_length_add_sub_consolidated245 (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (j : ℕ) (h : s'.length ≤ j) :
    (s'.append t').obj j = (s'.append t').obj (s'.length + (j - s'.length)) := by
  have h2 : s'.length + (j - s'.length) = j := by omega
  rw [h2]

private theorem append_schemeAt_concatIndex_of_le_consolidated245 (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ) (h : s'.length ≤ j) :
    (s.append t).obj (s.length + e.idx (j - s'.length)) =
      (s.append t).obj (concatIndex s t s' t' c e j) := by
  rw [concatIndex_of_ge s t s' t' c e j h]

private theorem sub_length_le_of_le_length_add_consolidated245 (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (j : ℕ) (hj : j ≤ s'.length + t'.length) : j - s'.length ≤ t'.length := by
  omega

def concatMapOfLtLength (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ) (h : j < s'.length) :
    (s'.append t').obj j ⟶ (s.append t).obj (concatIndex s t s' t' c e j) :=
  eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt h)) ≫ c.map j (le_of_lt h) ≫
    eqToHom (append_schemeAt_concatIndex_of_lt_consolidated245 s t s' t' c e j h)

def concatMapAddLength (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (i : ℕ) (hi : i ≤ t'.length) :
    (s'.append t').obj (s'.length + i) ⟶ (s.append t).obj (s.length + e.idx i) :=
  (BlowupSequenceData.concatObjAddIso s' t' i).hom ≫ e.map i hi ≫ (BlowupSequenceData.concatObjAddIso s t (e.idx i)).inv

def concatMap (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ)
    (hj : j ≤ s'.length + t'.length) :
    (s'.append t').obj j ⟶ (s.append t).obj (concatIndex s t s' t' c e j) :=
  if h : j < s'.length then concatMapOfLtLength s t s' t' c e j h
  else
    eqToHom (append_schemeAt_eq_length_add_sub_consolidated245 s' t' j (not_lt.1 h)) ≫
      concatMapAddLength s t s' t' c e (j - s'.length) (sub_length_le_of_le_length_add_consolidated245 s' t' j hj) ≫
      eqToHom (append_schemeAt_concatIndex_of_le_consolidated245 s t s' t' c e j (not_lt.1 h))

section
variable (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length)) (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups) (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)

private theorem concatIndex_length_add_length_consolidated245 :
    concatIndex s t s' t' c e (s'.length + t'.length) = s.length + t.length := by
  rw [concatIndex_of_ge s t s' t' c e (s'.length + t'.length) (Nat.le_add_right _ _)]
  have h : s'.length + t'.length - s'.length = t'.length := by omega
  rw [h, e.index_length_eq_length]

private theorem concatIndex_lt_length_add_length_consolidated245 (j : ℕ)
    (hj : j < s'.length + t'.length) :
    concatIndex s t s' t' c e j < s.length + t.length := by
  by_cases h : j < s'.length
  · rw [concatIndex_of_lt s t s' t' c e j h]
    have hc := c.blowupSequenceData_index_lt_length j h
    omega
  · have hge : s'.length ≤ j := not_lt.1 h
    rw [concatIndex_of_ge s t s' t' c e j hge]
    have hlt : j - s'.length < t'.length := by omega
    have he := e.blowupSequenceData_index_lt_length (j - s'.length) hlt
    omega

private theorem concatIndex_lt_concatIndex_succ_consolidated245 (j : ℕ)
    (hj : j < s'.length + t'.length) :
    concatIndex s t s' t' c e j < concatIndex s t s' t' c e (j + 1) := by
  by_cases h : j < s'.length
  · rw [concatIndex_of_lt s t s' t' c e j h]
    by_cases h2 : j + 1 < s'.length
    · rw [concatIndex_of_lt s t s' t' c e (j + 1) h2]
      exact c.blowupSequenceData_index_lt_index_succ j h
    · rw [concatIndex_of_ge s t s' t' c e (j + 1) (by omega)]
      have hlt : c.idx j < s.length := c.blowupSequenceData_index_lt_length j h
      omega
  · have hge : s'.length ≤ j := by omega
    rw [concatIndex_of_ge s t s' t' c e j hge,
      concatIndex_of_ge s t s' t' c e (j + 1) (by omega)]
    have hsub : j + 1 - s'.length = (j - s'.length) + 1 := by omega
    rw [hsub]
    have hlt : j - s'.length < t'.length := by omega
    have hstep : e.idx (j - s'.length) < e.idx ((j - s'.length) + 1) :=
      e.blowupSequenceData_index_lt_index_succ (j - s'.length) hlt
    omega


end

private theorem isPullback_iso_hom_comp_consolidated245 {A A' B Y Z : Scheme.{u}} (u : A' ≅ A)
    {f : A ⟶ B} {g : A ⟶ Y} {k : B ⟶ Z} {ψ : Y ⟶ Z} (h : IsPullback f g k ψ) :
    IsPullback (u.hom ≫ f) (u.hom ≫ g) k ψ := by
  have h1 : IsPullback u.hom (u.hom ≫ g) g (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have h2 := h1.paste_horiz h
  simpa using h2

private theorem isPullback_comp_iso_hom_consolidated245 {A B B' Y Z : Scheme.{u}} (v : B ≅ B')
    {f : A ⟶ B} {g : A ⟶ Y} {k : B ⟶ Z} {ψ : Y ⟶ Z} (h : IsPullback f g k ψ) :
    IsPullback (f ≫ v.hom) g (v.inv ≫ k) ψ := by
  have h1 : IsPullback v.hom k (v.inv ≫ k) (𝟙 Z) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have h2 := h.paste_horiz h1
  simpa using h2

private theorem isPullback_of_iso_consolidated245 {A A' B B' Y Z : Scheme.{u}} (u : A' ≅ A) (v : B ≅ B')
    {f : A ⟶ B} {g : A ⟶ Y} {k : B ⟶ Z} {ψ : Y ⟶ Z}
    {F : A' ⟶ B'} {G : A' ⟶ Y} {K : B' ⟶ Z} (h : IsPullback f g k ψ)
    (hF : F = u.hom ≫ f ≫ v.hom) (hG : G = u.hom ≫ g) (hK : K = v.inv ≫ k) :
    IsPullback F G K ψ := by
  subst hF
  subst hG
  subst hK
  exact isPullback_iso_hom_comp_consolidated245 u (isPullback_comp_iso_hom_consolidated245 v h)

private theorem comp_assoc_outer_consolidated245 {A B C D E F : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C)
    (f : C ⟶ D) (g : D ⟶ E) (w : E ⟶ F) :
    p ≫ (q ≫ f ≫ g) ≫ w = (p ≫ q) ≫ f ≫ g ≫ w := by
  simp

section
variable {Y : Scheme.{u}} (a : BlowupSequenceData Y) (b : BlowupSequenceData (a.obj a.length))

private theorem append_projectionToBase_length_add_zero_consolidated245 :
    (a.append b).projectionToBase (a.length + 0) =
      (BlowupSequenceData.concatObjAddIso a b 0).hom ≫ b.projectionToBase 0 ≫ a.projectionToBase a.length := by
  have h1 := BlowupSequenceData.projectionToBase_append_of_le_length a b (le_refl a.length)
  have h2 : (BlowupSequenceData.concatObjAddIso a b 0).hom =
      eqToHom (BlowupSequenceData.append_schemeAt_length_add_zero_consolidated245 a b) ≫ b.isoZero.inv := rfl
  show (a.append b).projectionToBase a.length =
      (BlowupSequenceData.concatObjAddIso a b 0).hom ≫ b.projectionToBase 0 ≫ a.projectionToBase a.length
  rw [h1, h2, b.projectionToBase_zero]
  simp

private theorem append_projectionToBase_length_add_succ_consolidated245 (n : ℕ) :
    (a.append b).projectionToBase (a.length + (n + 1)) =
      (BlowupSequenceData.concatObjAddIso a b (n + 1)).hom ≫ b.projectionToBase (n + 1) ≫ a.projectionToBase a.length := by
  have hgt : a.length < a.length + (n + 1) := by omega
  have hsub : a.length + (n + 1) - a.length = n + 1 := by omega
  have h1 := BlowupSequenceData.projectionToBase_append_of_length_lt a b hgt
  have h2 := BlowupSequenceData.projectionToBase_congr b hsub
  have h3 : (BlowupSequenceData.concatObjAddIso a b (n + 1)).hom =
      eqToHom (BlowupSequenceData.append_schemeAt_length_add_succ_consolidated245 a b n) := rfl
  rw [h1, h2, h3]
  simp

private theorem append_projectionToBase_length_add_consolidated245 (i : ℕ) :
    (a.append b).projectionToBase (a.length + i) =
      (BlowupSequenceData.concatObjAddIso a b i).hom ≫ b.projectionToBase i ≫ a.projectionToBase a.length := by
  cases i with
  | zero => exact append_projectionToBase_length_add_zero_consolidated245 a b
  | succ n => exact append_projectionToBase_length_add_succ_consolidated245 a b n

private theorem append_projectionToBase_eq_of_le_length_consolidated245 {n i : ℕ} (hni : n = i) (hi : i ≤ a.length)
    (hobj : a.obj i = (a.append b).obj n) :
    (a.append b).toSequenceOfBlowups.projectionToBase n = eqToHom hobj.symm ≫ a.toSequenceOfBlowups.projectionToBase i := by
  subst hni
  have h1 := BlowupSequenceData.projectionToBase_append_of_le_length a b hi
  simp only [BlowupSequenceData.toSequenceOfBlowups_projectionToBase, h1]
  rfl

private theorem append_projectionToBase_eq_of_eq_length_add_consolidated245 {n i : ℕ} (hni : n = a.length + i)
    (hobj : (a.append b).obj n = (a.append b).obj (a.length + i)) :
    (a.append b).toSequenceOfBlowups.projectionToBase n =
      (eqToHom hobj ≫ (BlowupSequenceData.concatObjAddIso a b i).hom) ≫
        b.toSequenceOfBlowups.projectionToBase i ≫ a.toSequenceOfBlowups.projectionToBase a.length := by
  subst hni
  simp only [BlowupSequenceData.toSequenceOfBlowups_projectionToBase, append_projectionToBase_length_add_consolidated245 a b i, eqToHom_refl, Category.id_comp]
  rfl


end

private theorem isPullback_concatMap_consolidated245 (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ)
    (hj : j ≤ s'.length + t'.length) :
    IsPullback (concatMap s t s' t' c e j hj) ((s'.append t').toSequenceOfBlowups.projectionToBase j)
      ((s.append t).toSequenceOfBlowups.projectionToBase (concatIndex s t s' t' c e j)) φ := by
  by_cases h : j < s'.length
  · have hmap : concatMap s t s' t' c e j hj = concatMapOfLtLength s t s' t' c e j h := dif_pos h
    have hidx : concatIndex s t s' t' c e j = c.idx j := concatIndex_of_lt s t s' t' c e j h
    have hobj : s.obj (c.idx j) = (s.append t).obj (concatIndex s t s' t' c e j) :=
      append_schemeAt_concatIndex_of_lt_consolidated245 s t s' t' c e j h
    refine isPullback_of_iso_consolidated245 (eqToIso (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt h)))
      (eqToIso hobj) (c.isPullback j (le_of_lt h)) ?_ ?_ ?_
    · exact hmap
    · exact append_projectionToBase_eq_of_le_length_consolidated245 s' t' (show j = j from rfl) (le_of_lt h)
        (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt h)).symm
    · exact append_projectionToBase_eq_of_le_length_consolidated245 s t hidx (le_of_lt (c.blowupSequenceData_index_lt_length j h)) hobj
  · have hge : s'.length ≤ j := not_lt.1 h
    have hji : j = s'.length + (j - s'.length) := by omega
    have hidx : concatIndex s t s' t' c e j = s.length + e.idx (j - s'.length) :=
      concatIndex_of_ge s t s' t' c e j hge
    have hmap : concatMap s t s' t' c e j hj =
        eqToHom (append_schemeAt_eq_length_add_sub_consolidated245 s' t' j hge) ≫
          concatMapAddLength s t s' t' c e (j - s'.length) (sub_length_le_of_le_length_add_consolidated245 s' t' j hj) ≫
          eqToHom (append_schemeAt_concatIndex_of_le_consolidated245 s t s' t' c e j hge) := dif_neg h
    refine isPullback_of_iso_consolidated245
      (eqToIso (append_schemeAt_eq_length_add_sub_consolidated245 s' t' j hge) ≪≫
        BlowupSequenceData.concatObjAddIso s' t' (j - s'.length))
      ((BlowupSequenceData.concatObjAddIso s t (e.idx (j - s'.length))).symm ≪≫
        eqToIso (append_schemeAt_concatIndex_of_le_consolidated245 s t s' t' c e j hge))
      ((e.isPullback (j - s'.length) (sub_length_le_of_le_length_add_consolidated245 s' t' j hj)).paste_vert
        c.isPullback_lastMap) ?_ ?_ ?_
    · rw [hmap]
      simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
      exact comp_assoc_outer_consolidated245 _ _ _ _ _
    · exact append_projectionToBase_eq_of_eq_length_add_consolidated245 s' t' hji (append_schemeAt_eq_length_add_sub_consolidated245 s' t' j hge)
    · exact append_projectionToBase_eq_of_eq_length_add_consolidated245 s t hidx (append_schemeAt_concatIndex_of_le_consolidated245 s t s' t' c e j hge).symm

private theorem comp_assoc_inner_pair_consolidated245 {A B C D E F : Scheme.{u}}
    (f1 : A ⟶ B) (f2 : B ⟶ C) (f3 : C ⟶ D) (f4 : D ⟶ E) (f5 : E ⟶ F) :
    f1 ≫ f2 ≫ f3 ≫ f4 ≫ f5 = f1 ≫ (f2 ≫ f3) ≫ f4 ≫ f5 := by
  rw [Category.assoc]

private def mapOfToSequenceOfBlowups_consolidated245 {s' : BlowupSequenceData X'} {s : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups) (j : ℕ) (hj : j ≤ s'.length) :
    s'.obj j ⟶ s.obj (c.idx j) := c.map j hj

private def mapOverLastMap_consolidated245 {s' : BlowupSequenceData X'} {s : BlowupSequenceData X}
    {t' : BlowupSequenceData (s'.obj s'.length)} {t : BlowupSequenceData (s.obj s.length)}
    {c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups}
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (i : ℕ) (hi : i ≤ t'.length) :
    t'.obj i ⟶ t.obj (e.idx i) := e.map i hi

section
variable {s' : BlowupSequenceData X'} {s : BlowupSequenceData X} (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)

private theorem blowupMorphism_comp_lowerMap_consolidated245 (j : ℕ) (hj : j < s'.length) :
    s'.map j ≫ mapOfToSequenceOfBlowups_consolidated245 c j (le_of_lt hj) =
      mapOfToSequenceOfBlowups_consolidated245 c (j + 1) hj ≫ s.transitionMap (le_of_lt (c.blowupSequenceData_index_lt_index_succ j hj)) :=
  c.blowupSequenceData_blowupMorphism_comp_map j hj

private theorem blowupMorphism_comp_lowerMap_assoc_consolidated245 (j : ℕ) (hj : j < s'.length)
    {W : Scheme.{u}} (g : s.obj (c.idx j) ⟶ W) :
    s'.map j ≫ mapOfToSequenceOfBlowups_consolidated245 c j (le_of_lt hj) ≫ g =
      mapOfToSequenceOfBlowups_consolidated245 c (j + 1) hj ≫ s.transitionMap (le_of_lt (c.blowupSequenceData_index_lt_index_succ j hj)) ≫ g := by
  rw [← Category.assoc, blowupMorphism_comp_lowerMap_consolidated245, Category.assoc]

private theorem lowerMap_congr_consolidated245 {a b : ℕ} (hab : a = b)
    (ha : a ≤ s'.length) (hb : b ≤ s'.length)
    (E1 : s'.obj a = s'.obj b) (E2 : s.obj (c.idx b) = s.obj (c.idx a)) :
    mapOfToSequenceOfBlowups_consolidated245 c a ha = eqToHom E1 ≫ mapOfToSequenceOfBlowups_consolidated245 c b hb ≫ eqToHom E2 := by
  subst hab
  simp

private theorem lastMap_eq_lowerMap_consolidated245 (E : s.obj (c.idx s'.length) = s.obj s.length) :
    c.lastMap = mapOfToSequenceOfBlowups_consolidated245 c s'.length le_rfl ≫ eqToHom E := rfl


end

section
variable {s' : BlowupSequenceData X'} {s : BlowupSequenceData X} {t' : BlowupSequenceData (s'.obj s'.length)} {t : BlowupSequenceData (s.obj s.length)} {c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups} (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)

private theorem blowupMorphism_comp_upperMap_consolidated245 (i : ℕ) (hi : i < t'.length) :
    t'.map i ≫ mapOverLastMap_consolidated245 e i (le_of_lt hi) =
      mapOverLastMap_consolidated245 e (i + 1) hi ≫ t.transitionMap (le_of_lt (e.blowupSequenceData_index_lt_index_succ i hi)) :=
  e.blowupSequenceData_blowupMorphism_comp_map i hi

private theorem blowupMorphism_comp_upperMap_assoc_consolidated245 (i : ℕ) (hi : i < t'.length)
    {W : Scheme.{u}} (g : t.obj (e.idx i) ⟶ W) :
    t'.map i ≫ mapOverLastMap_consolidated245 e i (le_of_lt hi) ≫ g =
      mapOverLastMap_consolidated245 e (i + 1) hi ≫ t.transitionMap (le_of_lt (e.blowupSequenceData_index_lt_index_succ i hi)) ≫ g := by
  rw [← Category.assoc, blowupMorphism_comp_upperMap_consolidated245, Category.assoc]

private theorem upperMap_zero_comp_isoObjZero_consolidated245 :
    mapOverLastMap_consolidated245 e 0 (Nat.zero_le _) ≫ t.transitionMap (Nat.zero_le (e.idx 0)) ≫ t.isoZero.hom =
      t'.isoZero.hom ≫ c.lastMap := by
  have e1 : t.transitionMap (Nat.zero_le (e.idx 0)) ≫ t.isoZero.hom = t.toSequenceOfBlowups.projectionToBase (e.idx 0) :=
    (BlowupSequenceData.transitionMap_zero_comp_isoObjZero_hom t (e.idx 0)).trans
      (BlowupSequenceData.toSequenceOfBlowups_projectionToBase t (e.idx 0)).symm
  have e2 : t'.toSequenceOfBlowups.projectionToBase 0 = t'.isoZero.hom :=
    (BlowupSequenceData.toSequenceOfBlowups_projectionToBase t' 0).trans (BlowupSequenceData.projectionToBase_zero t')
  have hw := (e.isPullback 0 (Nat.zero_le _)).w
  have A : mapOverLastMap_consolidated245 e 0 (Nat.zero_le _) ≫ t.transitionMap (Nat.zero_le (e.idx 0)) ≫ t.isoZero.hom =
      e.map 0 (Nat.zero_le _) ≫ t.toSequenceOfBlowups.projectionToBase (e.idx 0) :=
    congrArg (fun g => e.map 0 (Nat.zero_le _) ≫ g) e1
  have B : t'.toSequenceOfBlowups.projectionToBase 0 ≫ c.lastMap = t'.isoZero.hom ≫ c.lastMap :=
    congrArg (fun g => g ≫ c.lastMap) e2
  exact A.trans (hw.trans B)

private theorem upperMap_zero_comp_isoObjZero_assoc_consolidated245 {W : Scheme.{u}}
    (g : s.obj s.length ⟶ W) :
    mapOverLastMap_consolidated245 e 0 (Nat.zero_le _) ≫ t.transitionMap (Nat.zero_le (e.idx 0)) ≫ t.isoZero.hom ≫ g =
      t'.isoZero.hom ≫ c.lastMap ≫ g := by
  have h := upperMap_zero_comp_isoObjZero_consolidated245 e
  calc mapOverLastMap_consolidated245 e 0 (Nat.zero_le _) ≫ t.transitionMap (Nat.zero_le (e.idx 0)) ≫ t.isoZero.hom ≫ g
      = (mapOverLastMap_consolidated245 e 0 (Nat.zero_le _) ≫ t.transitionMap (Nat.zero_le (e.idx 0)) ≫
          t.isoZero.hom) ≫ g := by
        simp only [Category.assoc]
    _ = (t'.isoZero.hom ≫ c.lastMap) ≫ g := congrArg (fun m => m ≫ g) h
    _ = t'.isoZero.hom ≫ c.lastMap ≫ g := Category.assoc _ _ _


end

private theorem transitionMap_congr_consolidated245 {Y : Scheme.{u}} (d : BlowupSequenceData Y) {a b a' b' : ℕ}
    (ha : a = a') (hb : b = b') (h : a ≤ b) (h' : a' ≤ b')
    (E1 : d.obj b = d.obj b') (E2 : d.obj a' = d.obj a) :
    d.transitionMap h = eqToHom E1 ≫ d.transitionMap h' ≫ eqToHom E2 := by
  subst ha
  subst hb
  simp

section
variable {Y : Scheme.{u}} (s : BlowupSequenceData Y) (t : BlowupSequenceData (s.obj s.length))

private theorem append_transitionMap_of_le_length_consolidated245 {a b : ℕ} (hab : a ≤ b) (hb : b ≤ s.length) :
    (s.append t).transitionMap hab =
      eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t hb) ≫ s.transitionMap hab ≫
        eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t (le_trans hab hb)).symm := by
  revert hb
  induction b, hab using Nat.le_induction with
  | base =>
      intro hb
      rw [BlowupSequenceData.transitionMap_refl, BlowupSequenceData.transitionMap_refl]
      simp
  | succ m hm ih =>
      intro hb
      have hmlt : m < s.length := hb
      have hm' : m ≤ s.length := le_of_lt hmlt
      rw [← BlowupSequenceData.transitionMap_comp_transitionMap (s.append t) hm (Nat.le_succ m), BlowupSequenceData.transitionMap_succ,
        BlowupSequenceData.append_blowupMorphism_of_lt_length s t hmlt, ih hm', ← BlowupSequenceData.transitionMap_comp_transitionMap s hm (Nat.le_succ m),
        ← BlowupSequenceData.transitionMap_succ s m]
      simp

private theorem concatObjAddIso_inv_comp_transitionMap_consolidated245 {a b : ℕ} (h : a ≤ b) (hd : s.length + a ≤ s.length + b) :
    (BlowupSequenceData.concatObjAddIso s t b).inv ≫ (s.append t).transitionMap hd =
      t.transitionMap h ≫ (BlowupSequenceData.concatObjAddIso s t a).inv := by
  have key := BlowupSequenceData.append_transitionMap_comp_concatObjAddIso s t h
  calc (BlowupSequenceData.concatObjAddIso s t b).inv ≫ (s.append t).transitionMap hd
      = (BlowupSequenceData.concatObjAddIso s t b).inv ≫
          ((s.append t).transitionMap hd ≫ (BlowupSequenceData.concatObjAddIso s t a).hom) ≫
            (BlowupSequenceData.concatObjAddIso s t a).inv := by simp
    _ = (BlowupSequenceData.concatObjAddIso s t b).inv ≫
          ((BlowupSequenceData.concatObjAddIso s t b).hom ≫ t.transitionMap h) ≫
            (BlowupSequenceData.concatObjAddIso s t a).inv := by rw [key]
    _ = t.transitionMap h ≫ (BlowupSequenceData.concatObjAddIso s t a).inv := by simp

private theorem concatObjAddIso_inv_comp_transitionMap_assoc_consolidated245 {a b : ℕ} (h : a ≤ b) (hd : s.length + a ≤ s.length + b)
    {W : Scheme.{u}} (g : (s.append t).obj (s.length + a) ⟶ W) :
    (BlowupSequenceData.concatObjAddIso s t b).inv ≫ (s.append t).transitionMap hd ≫ g =
      t.transitionMap h ≫ (BlowupSequenceData.concatObjAddIso s t a).inv ≫ g := by
  rw [← Category.assoc, concatObjAddIso_inv_comp_transitionMap_consolidated245 s t h hd, Category.assoc]

private theorem concatObjAddIso_inv_comp_transitionMap_of_le_length_consolidated245 {m i : ℕ} (hm : m ≤ s.length) (h : m ≤ s.length + i) :
    (BlowupSequenceData.concatObjAddIso s t i).inv ≫ (s.append t).transitionMap h =
      t.transitionMap (Nat.zero_le i) ≫ t.isoZero.hom ≫ s.transitionMap hm ≫
        eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t hm).symm := by
  have h2 : (BlowupSequenceData.concatObjAddIso s t 0).inv =
      t.isoZero.hom ≫ eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t (le_refl s.length)).symm := rfl
  have h1 : (BlowupSequenceData.concatObjAddIso s t i).inv ≫ (s.append t).transitionMap (Nat.le_add_right s.length i) =
      t.transitionMap (Nat.zero_le i) ≫ (BlowupSequenceData.concatObjAddIso s t 0).inv :=
    concatObjAddIso_inv_comp_transitionMap_consolidated245 s t (Nat.zero_le i) (Nat.le_add_right s.length i)
  have h3 : (s.append t).transitionMap hm =
      eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t (le_refl s.length)) ≫ s.transitionMap hm ≫
        eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t hm).symm :=
    append_transitionMap_of_le_length_consolidated245 s t hm (le_refl s.length)
  calc (BlowupSequenceData.concatObjAddIso s t i).inv ≫ (s.append t).transitionMap h
      = (BlowupSequenceData.concatObjAddIso s t i).inv ≫
          (s.append t).transitionMap (Nat.le_add_right s.length i) ≫ (s.append t).transitionMap hm := by
        rw [BlowupSequenceData.transitionMap_comp_transitionMap]
    _ = (t.transitionMap (Nat.zero_le i) ≫ (BlowupSequenceData.concatObjAddIso s t 0).inv) ≫
          (s.append t).transitionMap hm := by
        rw [← Category.assoc, h1]
    _ = t.transitionMap (Nat.zero_le i) ≫ t.isoZero.hom ≫ s.transitionMap hm ≫
          eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t hm).symm := by
        rw [h2, h3]
        simp

private theorem concatObjAddIso_inv_comp_transitionMap_of_le_length_assoc_consolidated245 {m i : ℕ} (hm : m ≤ s.length) (h : m ≤ s.length + i)
    {W : Scheme.{u}} (g : (s.append t).obj m ⟶ W) :
    (BlowupSequenceData.concatObjAddIso s t i).inv ≫ (s.append t).transitionMap h ≫ g =
      t.transitionMap (Nat.zero_le i) ≫ t.isoZero.hom ≫ s.transitionMap hm ≫
        eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t hm).symm ≫ g := by
  rw [← Category.assoc, concatObjAddIso_inv_comp_transitionMap_of_le_length_consolidated245 s t hm h]
  simp

private theorem concatObjAddIso_zero_hom_consolidated245 :
    (BlowupSequenceData.concatObjAddIso s t 0).hom =
      eqToHom (BlowupSequenceData.append_schemeAt_length_add_zero_consolidated245 s t) ≫ t.isoZero.inv := rfl


end

private def appendMapAdd_consolidated245 (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (i : ℕ) (hi : i ≤ t'.length) :
    (s'.append t').obj (s'.length + i) ⟶ (s.append t).obj (s.length + e.idx i) :=
  (BlowupSequenceData.concatObjAddIso s' t' i).hom ≫ mapOverLastMap_consolidated245 e i hi ≫
    (BlowupSequenceData.concatObjAddIso s t (e.idx i)).inv

section
variable (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length)) (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups) (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)

private theorem upperConcatMap_congr_consolidated245 {j r q : ℕ} (hr : r = q)
    (hrle : r ≤ t'.length) (hq : q ≤ t'.length)
    (A : (s'.append t').obj j = (s'.append t').obj (s'.length + r))
    (B : (s.append t).obj (s.length + e.idx r) = (s.append t).obj (concatIndex s t s' t' c e j))
    (E1 : (s'.append t').obj j = (s'.append t').obj (s'.length + q))
    (E2 : (s.append t).obj (s.length + e.idx q) =
      (s.append t).obj (concatIndex s t s' t' c e j)) :
    eqToHom A ≫ appendMapAdd_consolidated245 s t s' t' c e r hrle ≫ eqToHom B =
      eqToHom E1 ≫ appendMapAdd_consolidated245 s t s' t' c e q hq ≫ eqToHom E2 := by
  subst hr
  rfl

private theorem concatMap_eq_lowerMap_of_lt_consolidated245 (j : ℕ)
    (hj : j ≤ s'.length + t'.length) (h : j < s'.length)
    (A : (s'.append t').obj j = s'.obj j)
    (B : s.obj (c.idx j) = (s.append t).obj (concatIndex s t s' t' c e j)) :
    concatMap s t s' t' c e j hj = eqToHom A ≫ mapOfToSequenceOfBlowups_consolidated245 c j (le_of_lt h) ≫ eqToHom B :=
  dif_pos h

private theorem concatMap_eq_upperConcatMap_of_le_consolidated245 (j q : ℕ)
    (hj : j ≤ s'.length + t'.length) (hge : s'.length ≤ j) (hjq : j - s'.length = q)
    (hq : q ≤ t'.length)
    (E1 : (s'.append t').obj j = (s'.append t').obj (s'.length + q))
    (E2 : (s.append t).obj (s.length + e.idx q) =
      (s.append t).obj (concatIndex s t s' t' c e j)) :
    concatMap s t s' t' c e j hj =
      eqToHom E1 ≫ appendMapAdd_consolidated245 s t s' t' c e q hq ≫ eqToHom E2 := by
  have h0 : concatMap s t s' t' c e j hj =
      eqToHom (append_schemeAt_eq_length_add_sub_consolidated245 s' t' j hge) ≫
        appendMapAdd_consolidated245 s t s' t' c e (j - s'.length) (sub_length_le_of_le_length_add_consolidated245 s' t' j hj) ≫
        eqToHom (append_schemeAt_concatIndex_of_le_consolidated245 s t s' t' c e j hge) := dif_neg (not_lt.2 hge)
  exact h0.trans (upperConcatMap_congr_consolidated245 s t s' t' c e hjq (sub_length_le_of_le_length_add_consolidated245 s' t' j hj) hq
    (append_schemeAt_eq_length_add_sub_consolidated245 s' t' j hge) (append_schemeAt_concatIndex_of_le_consolidated245 s t s' t' c e j hge) E1 E2)

private theorem blowupMorphism_comp_concatMap_consolidated245 (j : ℕ)
    (hj : j < s'.length + t'.length)
    (hd : concatIndex s t s' t' c e j ≤ concatIndex s t s' t' c e (j + 1)) :
    (s'.append t').map j ≫ concatMap s t s' t' c e j (le_of_lt hj) =
      concatMap s t s' t' c e (j + 1) hj ≫ (s.append t).transitionMap hd := by
  by_cases hlt : j < s'.length
  · by_cases h1 : j + 1 < s'.length
    · have hcj : c.idx j < s.length := c.blowupSequenceData_index_lt_length j hlt
      have hc1 : c.idx (j + 1) < s.length := c.blowupSequenceData_index_lt_length (j + 1) h1
      have hmono : c.idx j ≤ c.idx (j + 1) := le_of_lt (c.blowupSequenceData_index_lt_index_succ j hlt)
      rw [BlowupSequenceData.append_blowupMorphism_of_lt_length s' t' hlt,
        concatMap_eq_lowerMap_of_lt_consolidated245 s t s' t' c e j (le_of_lt hj) hlt
          (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt hlt))
          (append_schemeAt_concatIndex_of_lt_consolidated245 s t s' t' c e j hlt),
        concatMap_eq_lowerMap_of_lt_consolidated245 s t s' t' c e (j + 1) hj h1
          (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt h1))
          (append_schemeAt_concatIndex_of_lt_consolidated245 s t s' t' c e (j + 1) h1),
        transitionMap_congr_consolidated245 (s.append t) (concatIndex_of_lt s t s' t' c e j hlt)
          (concatIndex_of_lt s t s' t' c e (j + 1) h1) hd hmono
          (congrArg (s.append t).obj (concatIndex_of_lt s t s' t' c e (j + 1) h1))
          (congrArg (s.append t).obj (concatIndex_of_lt s t s' t' c e j hlt)).symm,
        append_transitionMap_of_le_length_consolidated245 s t hmono (le_of_lt hc1)]
      simp [blowupMorphism_comp_lowerMap_assoc_consolidated245 c j hlt]
    · have hjn : j + 1 = s'.length := by omega
      have hcj : c.idx j < s.length := c.blowupSequenceData_index_lt_length j hlt
      have hidxlen' : c.idx s'.length = s.length := c.index_length_eq_length
      have hidxlen : c.idx (j + 1) = s.length := by rw [hjn]; exact hidxlen'
      have hidx0 : concatIndex s t s' t' c e j = c.idx j := concatIndex_of_lt s t s' t' c e j hlt
      have hidx1 : concatIndex s t s' t' c e (j + 1) = s.length + e.idx 0 := by
        rw [concatIndex_of_ge s t s' t' c e (j + 1) (le_of_eq hjn.symm),
          show j + 1 - s'.length = 0 by omega]
      have hdle : c.idx j ≤ s.length + e.idx 0 :=
        le_trans (le_of_lt hcj) (Nat.le_add_right _ _)
      rw [BlowupSequenceData.append_blowupMorphism_of_lt_length s' t' hlt,
        concatMap_eq_lowerMap_of_lt_consolidated245 s t s' t' c e j (le_of_lt hj) hlt
          (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt hlt))
          (append_schemeAt_concatIndex_of_lt_consolidated245 s t s' t' c e j hlt),
        concatMap_eq_upperConcatMap_of_le_consolidated245 s t s' t' c e (j + 1) 0 hj (le_of_eq hjn.symm)
          (show j + 1 - s'.length = 0 by omega) (Nat.zero_le _)
          (congrArg (s'.append t').obj (show j + 1 = s'.length + 0 by omega))
          (congrArg (s.append t).obj hidx1.symm),
        transitionMap_congr_consolidated245 (s.append t) hidx0 hidx1 hd hdle
          (congrArg (s.append t).obj hidx1)
          (congrArg (s.append t).obj hidx0).symm]
      simp only [appendMapAdd_consolidated245, concatObjAddIso_zero_hom_consolidated245, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp]
      rw [concatObjAddIso_inv_comp_transitionMap_of_le_length_assoc_consolidated245 s t (le_of_lt hcj) hdle, upperMap_zero_comp_isoObjZero_assoc_consolidated245 e,
        blowupMorphism_comp_lowerMap_assoc_consolidated245 c j hlt,
        lowerMap_congr_consolidated245 c hjn hlt le_rfl (congrArg s'.obj hjn)
          (congrArg (fun n => s.obj (c.idx n)) hjn.symm),
        transitionMap_congr_consolidated245 s (rfl : c.idx j = c.idx j) hidxlen
          (le_of_lt (c.blowupSequenceData_index_lt_index_succ j hlt)) (le_of_lt hcj)
          (congrArg s.obj hidxlen) rfl,
        lastMap_eq_lowerMap_consolidated245 c (congrArg s.obj hidxlen')]
      simp
      all_goals exact comp_assoc_inner_pair_consolidated245 _ _ _ _ _
  · have hge : s'.length ≤ j := not_lt.1 hlt
    obtain ⟨q, rfl⟩ : ∃ q, j = s'.length + q := ⟨j - s'.length, by omega⟩
    have hq1 : q < t'.length := by omega
    have hmono : e.idx q < e.idx (q + 1) := e.blowupSequenceData_index_lt_index_succ q hq1
    have hidxj : concatIndex s t s' t' c e (s'.length + q) = s.length + e.idx q := by
      rw [concatIndex_of_ge s t s' t' c e (s'.length + q) (Nat.le_add_right _ _),
        show s'.length + q - s'.length = q by omega]
    have hidxj1 : concatIndex s t s' t' c e (s'.length + q + 1) = s.length + e.idx (q + 1) := by
      rw [concatIndex_of_ge s t s' t' c e (s'.length + q + 1) (by omega),
        show s'.length + q + 1 - s'.length = q + 1 by omega]
    rw [concatMap_eq_upperConcatMap_of_le_consolidated245 s t s' t' c e (s'.length + q) q (le_of_lt hj)
        (Nat.le_add_right _ _)
        (show s'.length + q - s'.length = q by omega) (le_of_lt hq1) rfl
        (congrArg (s.append t).obj hidxj.symm),
      concatMap_eq_upperConcatMap_of_le_consolidated245 s t s' t' c e (s'.length + q + 1) (q + 1) hj (by omega)
        (show s'.length + q + 1 - s'.length = q + 1 by omega) hq1 rfl
        (congrArg (s.append t).obj hidxj1.symm),
      transitionMap_congr_consolidated245 (s.append t) hidxj hidxj1 hd
        (show s.length + e.idx q ≤ s.length + e.idx (q + 1) by omega)
        (congrArg (s.append t).obj hidxj1) (congrArg (s.append t).obj hidxj).symm]
    simp only [appendMapAdd_consolidated245, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    rw [BlowupSequenceData.append_blowupMorphism_comp_concatObjAddIso_assoc, blowupMorphism_comp_upperMap_assoc_consolidated245 e q hq1,
      concatObjAddIso_inv_comp_transitionMap_assoc_consolidated245 s t (le_of_lt hmono)]

private theorem toSequenceOfBlowups_blowupMorphism_comp_concatMap_consolidated245 (j : ℕ)
    (hj : j < s'.length + t'.length) :
    (s'.append t').toSequenceOfBlowups.transitionMapSucc j ≫ concatMap s t s' t' c e j (le_of_lt hj) =
      concatMap s t s' t' c e (j + 1) hj ≫
        (s.append t).toSequenceOfBlowups.transitionMap (le_of_lt (concatIndex_lt_concatIndex_succ_consolidated245 s t s' t' c e j hj)) := by
  rw [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism]
  exact blowupMorphism_comp_concatMap_consolidated245 s t s' t' c e j hj _


end

section
variable {A B C D : Scheme.{u}} (g : A ⟶ B)

private theorem comp_comp_inv_comp_hom_consolidated245 (m : B ⟶ C) (ι : D ≅ C) :
    (g ≫ m ≫ ι.inv) ≫ ι.hom = g ≫ m := by
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem comp_comp_eqToHom_comp_eqToHom_consolidated245 (f : B ⟶ C)
    (h1 : C = D) (h2 : D = C) :
    (g ≫ f ≫ eqToHom h1) ≫ eqToHom h2 = g ≫ f := by
  subst h1
  simp only [eqToHom_refl, Category.comp_id]


end

private theorem concatMapAddLength_comp_concatObjAddIso_hom_consolidated245 (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (i : ℕ) (hi : i ≤ t'.length) :
    concatMapAddLength s t s' t' c e i hi ≫ (BlowupSequenceData.concatObjAddIso s t (e.idx i)).hom =
      (BlowupSequenceData.concatObjAddIso s' t' i).hom ≫ e.map i hi :=
  comp_comp_inv_comp_hom_consolidated245 (BlowupSequenceData.concatObjAddIso s' t' i).hom (e.map i hi)
    (BlowupSequenceData.concatObjAddIso s t (e.idx i))

section
variable {Y : Scheme.{u}} (d : BlowupSequenceData Y) {a b : ℕ}

private theorem center_comap_eqToHom_congr_consolidated245 (hab : a = b) {W : Scheme.{u}} (hW : W = d.obj a) (hW' : W = d.obj b) :
    (d.center a).comap (eqToHom hW) = (d.center b).comap (eqToHom hW') := by
  subst hab
  rfl

private theorem center_comap_comp_eqToHom_congr_consolidated245 (hab : a = b) {Z Z' W : Scheme.{u}} (p : Z ⟶ Z') (f : Z' ⟶ W)
    (hW : W = d.obj a) (hW' : W = d.obj b) :
    (d.center a).comap (p ≫ f ≫ eqToHom hW) = (d.center b).comap (p ≫ f ≫ eqToHom hW') := by
  subst hab
  rfl

private theorem center_comap_comp_eqToHom_consolidated245 (hab : b = a) {Z : Scheme.{u}} (v : Z ⟶ d.obj b) (q : d.obj b = d.obj a) :
    (d.center a).comap (v ≫ eqToHom q) = (d.center b).comap v := by
  subst hab
  simp


end

private theorem append_center_length_add_consolidated245 (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (n : ℕ) :
    (s.append t).center (s.length + n) =
      (t.center n).comap (BlowupSequenceData.concatObjAddIso s t n).hom := by
  cases n with
  | zero =>
    refine Eq.trans (BlowupSequenceData.append_center_length s t) ?_
    exact (Scheme.IdealSheafData.comap_comp (t.center 0)
      (eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t (le_refl s.length))) t.isoZero.inv).symm
  | succ k =>
    have hlt : s.length < s.length + (k + 1) := by omega
    have hsub : s.length + (k + 1) - s.length = k + 1 := by omega
    refine Eq.trans (BlowupSequenceData.append_center_of_length_lt s t hlt) ?_
    exact center_comap_eqToHom_congr_consolidated245 t hsub (BlowupSequenceData.append_schemeAt_of_length_lt s t hlt)
      (BlowupSequenceData.append_schemeAt_length_add_succ_consolidated245 s t k)

section
variable (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length)) (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups) (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)

private theorem concatMapAddLength_congr_consolidated245 {a b : ℕ} (hab : a = b)
    (ha : a ≤ t'.length) (hb : b ≤ t'.length) {W : Scheme.{u}}
    (h1 : (s'.append t').obj (s'.length + b) = (s'.append t').obj (s'.length + a))
    (h2 : (s.append t).obj (s.length + e.idx a) = W)
    (h2' : (s.append t).obj (s.length + e.idx b) = W) :
    eqToHom h1 ≫ concatMapAddLength s t s' t' c e a ha ≫ eqToHom h2 =
      concatMapAddLength s t s' t' c e b hb ≫ eqToHom h2' := by
  subst hab
  rw [eqToHom_refl, Category.id_comp]

private theorem concatMap_eq_map_of_lt_consolidated245 (j : ℕ)
    (hj : j ≤ s'.length + t'.length) (h : j < s'.length) :
    concatMap s t s' t' c e j hj =
      eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt h)) ≫ c.map j (le_of_lt h) ≫
        eqToHom (append_schemeAt_concatIndex_of_lt_consolidated245 s t s' t' c e j h) := dif_pos h

private theorem append_center_eq_comap_concatMap_consolidated245 (j : ℕ)
    (hj : j < s'.length + t'.length) :
    (s'.append t').toSequenceOfBlowups.center j =
      ((s.append t).toSequenceOfBlowups.center (concatIndex s t s' t' c e j)).comap
        (concatMap s t s' t' c e j (le_of_lt hj)) := by
  show (s'.append t').center j =
      ((s.append t).center (concatIndex s t s' t' c e j)).comap
        (concatMap s t s' t' c e j (le_of_lt hj))
  by_cases h : j < s'.length
  · have hci : c.idx j < s.length := c.blowupSequenceData_index_lt_length j h
    have hidxA : concatIndex s t s' t' c e j = c.idx j := concatIndex_of_lt s t s' t' c e j h
    have hc : s'.center j = (s.center (c.idx j)).comap (c.map j (le_of_lt h)) :=
      c.center_comap j (by rw [BlowupSequenceData.toSequenceOfBlowups_length]; exact h)
    have hmA : (eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt h)) ≫ c.map j (le_of_lt h) ≫
          eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t (le_of_lt hci)).symm) ≫
          eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t (le_of_lt hci)) =
        eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt h)) ≫ c.map j (le_of_lt h) :=
      comp_comp_eqToHom_comp_eqToHom_consolidated245 _ _ _ _
    rw [concatMap_eq_map_of_lt_consolidated245 s t s' t' c e j (le_of_lt hj) h,
      center_comap_comp_eqToHom_congr_consolidated245 (s.append t) hidxA
        (eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s' t' (le_of_lt h))) (c.map j (le_of_lt h))
        (append_schemeAt_concatIndex_of_lt_consolidated245 s t s' t' c e j h)
        (BlowupSequenceData.append_schemeAt_of_le_length s t (le_of_lt hci)).symm,
      BlowupSequenceData.append_center_of_lt_length s t hci, ← Scheme.IdealSheafData.comap_comp, hmA,
      BlowupSequenceData.append_center_of_lt_length s' t' h, hc]
    exact (Scheme.IdealSheafData.comap_comp _ _ _).symm
  · have hge : s'.length ≤ j := not_lt.1 h
    obtain ⟨i, rfl⟩ : ∃ i, j = s'.length + i := ⟨j - s'.length, by omega⟩
    have hit : i < t'.length := by omega
    have hile : i ≤ t'.length := le_of_lt hit
    have hsub : s'.length + i - s'.length = i := by omega
    have hidx : concatIndex s t s' t' c e (s'.length + i) = s.length + e.idx i := by
      rw [concatIndex_of_ge s t s' t' c e (s'.length + i) hge, hsub]
    have hmapGe : concatMap s t s' t' c e (s'.length + i) (le_of_lt hj) =
        eqToHom (append_schemeAt_eq_length_add_sub_consolidated245 s' t' (s'.length + i) hge) ≫
          concatMapAddLength s t s' t' c e (s'.length + i - s'.length)
            (sub_length_le_of_le_length_add_consolidated245 s' t' (s'.length + i) (le_of_lt hj)) ≫
          eqToHom (append_schemeAt_concatIndex_of_le_consolidated245 s t s' t' c e (s'.length + i) hge) :=
      dif_neg (not_lt.2 hge)
    have hshift := concatMapAddLength_congr_consolidated245 s t s' t' c e hsub
      (sub_length_le_of_le_length_add_consolidated245 s' t' (s'.length + i) (le_of_lt hj)) hile
      (append_schemeAt_eq_length_add_sub_consolidated245 s' t' (s'.length + i) hge)
      (append_schemeAt_concatIndex_of_le_consolidated245 s t s' t' c e (s'.length + i) hge)
      (congrArg (s.append t).obj hidx.symm)
    have hmor : concatMapAddLength s t s' t' c e i hile ≫ (BlowupSequenceData.concatObjAddIso s t (e.idx i)).hom =
        (BlowupSequenceData.concatObjAddIso s' t' i).hom ≫ e.map i hile :=
      concatMapAddLength_comp_concatObjAddIso_hom_consolidated245 s t s' t' c e i hile
    have hcen : t'.center i = (t.center (e.idx i)).comap (e.map i hile) :=
      e.center_comap i (by rw [BlowupSequenceData.toSequenceOfBlowups_length]; exact hit)
    rw [hmapGe, hshift,
      center_comap_comp_eqToHom_consolidated245 (s.append t) hidx.symm (concatMapAddLength s t s' t' c e i hile)
        (congrArg (s.append t).obj hidx.symm),
      append_center_length_add_consolidated245 s t (e.idx i), ← Scheme.IdealSheafData.comap_comp, hmor,
      append_center_length_add_consolidated245 s' t' i, hcen]
    exact (Scheme.IdealSheafData.comap_comp _ _ _).symm


end

section
variable {Y Z : Scheme.{u}}

private theorem comap_iso_hom_ne_top_consolidated245 (g : Y ≅ Z) (J : Z.IdealSheafData)
    (hJ : J ≠ ⊤) : J.comap g.hom ≠ ⊤ := by
  obtain ⟨x, hx⟩ := exists_mem_support_of_ne_top_consolidated245 J hJ
  have h1 : (g.inv ≫ g.hom).base x ∈ J.support := by
    rw [g.inv_hom_id]
    simpa using hx
  have h2 : g.hom.base (g.inv.base x) ∈ J.support := by simpa using h1
  exact AlgebraicGeometry.Scheme.IdealSheafData.ne_top_of_mem_support (J.comap g.hom)
    (g.inv.base x) (AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.mpr h2)

private theorem comap_eqToHom_ne_top_consolidated245 (h : Y = Z) (J : Z.IdealSheafData)
    (hJ : J ≠ ⊤) : J.comap (eqToHom h) ≠ ⊤ :=
  comap_iso_hom_ne_top_consolidated245 (eqToIso h) J hJ


end

private theorem append_center_ne_top_consolidated245 (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ)
    (hj : j < s'.length + t'.length) : (s'.append t').toSequenceOfBlowups.center j ≠ ⊤ := by
  show (s'.append t').center j ≠ ⊤
  rcases lt_trichotomy j s'.length with h | h | h
  · have hne : s'.center j ≠ ⊤ :=
      c.center_ne_top j (by rw [BlowupSequenceData.toSequenceOfBlowups_length]; exact h)
    rw [BlowupSequenceData.append_center_of_lt_length s' t' h]
    exact comap_eqToHom_ne_top_consolidated245 _ _ hne
  · subst h
    have ht : 0 < t'.length := by omega
    have h0 : t'.center 0 ≠ ⊤ :=
      e.center_ne_top 0 (by rw [BlowupSequenceData.toSequenceOfBlowups_length]; exact ht)
    have h2' : (t'.center 0).comap t'.isoZero.inv ≠ ⊤ :=
      comap_iso_hom_ne_top_consolidated245 t'.isoZero.symm (t'.center 0) h0
    rw [BlowupSequenceData.append_center_length s' t']
    exact comap_eqToHom_ne_top_consolidated245 _ _ h2'
  · have hsub : j - s'.length < t'.length := by omega
    have hne : t'.center (j - s'.length) ≠ ⊤ :=
      e.center_ne_top (j - s'.length) (by rw [BlowupSequenceData.toSequenceOfBlowups_length]; exact hsub)
    rw [BlowupSequenceData.append_center_of_length_lt s' t' h]
    exact comap_eqToHom_ne_top_consolidated245 _ _ hne

private theorem exists_preimage_of_isPullback_consolidated245 {A A' Z Z' : Scheme.{u}} {p : A' ⟶ A} {q : A' ⟶ Z'}
    {f : A ⟶ Z} {g : Z' ⟶ Z} (h : IsPullback p q f g) (a : ↥A) (b : ↥Z')
    (hab : f.base a = g.base b) : ∃ a' : ↥A', p.base a' = a := by
  obtain ⟨w, hw1, _hw2⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback a b hab
  refine ⟨h.isoPullback.inv.base w, ?_⟩
  have h2 : h.isoPullback.hom ≫ pullback.fst f g = p := h.isoPullback_hom_fst
  have key : h.isoPullback.inv ≫ p = pullback.fst f g := by
    calc h.isoPullback.inv ≫ p
        = h.isoPullback.inv ≫ h.isoPullback.hom ≫ pullback.fst f g := by rw [h2]
      _ = pullback.fst f g := by rw [Iso.inv_hom_id_assoc]
  calc p.base (h.isoPullback.inv.base w)
      = (h.isoPullback.inv ≫ p).base w := rfl
    _ = (pullback.fst f g).base w := by rw [key]
    _ = a := hw1

private theorem mem_toSequenceOfBlowups_center_support_consolidated245 {Y : Scheme.{u}} (d : BlowupSequenceData Y) (i : ℕ)
    (w : ↥(d.toSequenceOfBlowups.schemeAt i)) (hw : w ∈ (d.center i).support) :
    w ∈ (d.toSequenceOfBlowups.center i).support := by
  rw [BlowupSequenceData.toSequenceOfBlowups_center]
  exact hw

section
variable {Y : Scheme.{u}} (s : BlowupSequenceData Y) (t : BlowupSequenceData (s.obj s.length))

private theorem eqToHom_comp_projectionToBase_length_add_zero_consolidated245 (h1 : (s.append t).obj (s.length + 0) = s.obj (s.length + 0))
    (h2 : (s.append t).obj (s.length + 0) = s.obj s.length) :
    eqToHom h1 ≫ s.projectionToBase (s.length + 0) = eqToHom h2 ≫ s.projectionToBase s.length := rfl

private theorem projectionToBase_append_length_add_consolidated245 (n : ℕ) :
    (s.append t).projectionToBase (s.length + n) =
      (BlowupSequenceData.concatObjAddIso s t n).hom ≫ t.projectionToBase n ≫ s.projectionToBase s.length := by
  induction n with
  | zero =>
      have hA : (BlowupSequenceData.concatObjAddIso s t 0).hom ≫ t.projectionToBase 0 ≫ s.projectionToBase s.length =
          eqToHom (BlowupSequenceData.append_schemeAt_length_add_zero_consolidated245 s t) ≫ s.projectionToBase s.length := by
        rw [concatObjAddIso_zero_hom_consolidated245, BlowupSequenceData.projectionToBase_zero, Category.assoc, Iso.inv_hom_id_assoc]
      exact ((BlowupSequenceData.projectionToBase_append_of_le_length s t (le_of_eq (Nat.add_zero s.length))).trans
        (eqToHom_comp_projectionToBase_length_add_zero_consolidated245 s t _ _)).trans hA.symm
  | succ n ih =>
      have hs : (s.append t).projectionToBase (s.length + (n + 1)) =
          (s.append t).map (s.length + n) ≫ (s.append t).projectionToBase (s.length + n) :=
        BlowupSequenceData.projectionToBase_succ (s.append t) (s.length + n)
      rw [hs, ih, BlowupSequenceData.append_blowupMorphism_comp_concatObjAddIso_assoc, ← Category.assoc (t.map n),
        ← BlowupSequenceData.projectionToBase_succ]


end

private theorem append_projectionToBase_ne_of_forall_concatIndex_ne_consolidated245 (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (i : ℕ)
    (hi : i < s.length + t.length)
    (hmiss : ∀ j : ℕ, j < s'.length + t'.length → concatIndex s t s' t' c e j ≠ i)
    (z : ↥((s.append t).toSequenceOfBlowups.schemeAt i)) (hz : z ∈ ((s.append t).toSequenceOfBlowups.center i).support)
    (x' : ↥X') :
    φ.base x' ≠ ((s.append t).toSequenceOfBlowups.projectionToBase i).base z := by
  intro heq
  have hzc : z ∈ ((s.append t).center i).support := by
    rw [BlowupSequenceData.toSequenceOfBlowups_center] at hz
    exact hz
  have heqp : φ.base x' = ((s.append t).projectionToBase i).base z :=
    heq.trans (congrArg (fun m : (s.append t).toSequenceOfBlowups.schemeAt i ⟶ X => m.base z)
      (BlowupSequenceData.toSequenceOfBlowups_projectionToBase (s.append t) i))
  by_cases hlt : i < s.length
  · have hobj : (s.append t).obj i = s.obj i := BlowupSequenceData.append_schemeAt_of_le_length s t (le_of_lt hlt)
    rw [BlowupSequenceData.append_center_of_lt_length s t hlt] at hzc
    have hzs : (eqToHom hobj).base z ∈ (s.center i).support :=
      Scheme.IdealSheafData.mem_support_comap.mp hzc
    have heq2 : φ.base x' = (s.projectionToBase i).base ((eqToHom hobj).base z) :=
      (heqp.trans (congrArg (fun m : (s.append t).obj i ⟶ X => m.base z)
          (BlowupSequenceData.projectionToBase_append_of_le_length s t (le_of_lt hlt)))).trans rfl
    refine c.omitted i ?_ ?_ ((eqToHom hobj).base z) ?_ x' ?_
    · rw [BlowupSequenceData.toSequenceOfBlowups_length]
      exact hlt
    · intro j hj hji
      rw [BlowupSequenceData.toSequenceOfBlowups_length] at hj
      exact hmiss j (by omega) ((concatIndex_of_lt s t s' t' c e j hj).trans hji)
    · exact mem_toSequenceOfBlowups_center_support_consolidated245 s i _ hzs
    · exact heq2.trans (congrArg (fun m : s.obj i ⟶ X => m.base ((eqToHom hobj).base z))
        (BlowupSequenceData.toSequenceOfBlowups_projectionToBase s i)).symm
  · have hge : s.length ≤ i := not_lt.1 hlt
    obtain ⟨n, rfl⟩ : ∃ n, i = s.length + n := ⟨i - s.length, by omega⟩
    have hn : n < t.length := by omega
    rw [append_center_length_add_consolidated245 s t n] at hzc
    have hzt : ((BlowupSequenceData.concatObjAddIso s t n).hom).base z ∈ (t.center n).support :=
      Scheme.IdealSheafData.mem_support_comap.mp hzc
    have heq2 : φ.base x' =
        (s.projectionToBase s.length).base ((t.projectionToBase n).base (((BlowupSequenceData.concatObjAddIso s t n).hom).base z)) :=
      (heqp.trans (congrArg (fun m : (s.append t).obj (s.length + n) ⟶ X => m.base z)
          (projectionToBase_append_length_add_consolidated245 s t n))).trans rfl
    have hsm : (s.toSequenceOfBlowups.projectionToBase s.toSequenceOfBlowups.length).base
        ((t.projectionToBase n).base (((BlowupSequenceData.concatObjAddIso s t n).hom).base z)) = φ.base x' :=
      (congrArg (fun m : s.obj s.length ⟶ X =>
          m.base ((t.projectionToBase n).base (((BlowupSequenceData.concatObjAddIso s t n).hom).base z)))
        (BlowupSequenceData.toSequenceOfBlowups_projectionToBase s s.toSequenceOfBlowups.length)).trans heq2.symm
    obtain ⟨a', ha'⟩ := exists_preimage_of_isPullback_consolidated245 c.isPullback_lastMap
      ((t.projectionToBase n).base (((BlowupSequenceData.concatObjAddIso s t n).hom).base z)) x' hsm
    refine e.omitted n ?_ ?_ (((BlowupSequenceData.concatObjAddIso s t n).hom).base z) ?_ a' ?_
    · rw [BlowupSequenceData.toSequenceOfBlowups_length]
      exact hn
    · intro m hm hmn
      rw [BlowupSequenceData.toSequenceOfBlowups_length] at hm
      refine hmiss (s'.length + m) (by omega) ?_
      rw [concatIndex_of_ge s t s' t' c e (s'.length + m) (Nat.le_add_right _ _),
        show s'.length + m - s'.length = m by omega, hmn]
    · exact mem_toSequenceOfBlowups_center_support_consolidated245 t n _ hzt
    · exact ha'.trans (congrArg (fun m : t.obj n ⟶ s.obj s.length =>
        m.base (((BlowupSequenceData.concatObjAddIso s t n).hom).base z))
        (BlowupSequenceData.toSequenceOfBlowups_projectionToBase t n)).symm

def concat (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) :
    SequenceOfBlowupsPullback φ (s'.append t').toSequenceOfBlowups (s.append t).toSequenceOfBlowups where
  idx := concatIndex s t s' t' c e
  map := concatMap s t s' t' c e
  idx_length := concatIndex_length_add_length_consolidated245 s t s' t' c e
  idx_lt := concatIndex_lt_length_add_length_consolidated245 s t s' t' c e
  idx_strictMono := concatIndex_lt_concatIndex_succ_consolidated245 s t s' t' c e
  isPullback := isPullback_concatMap_consolidated245 s t s' t' c e
  step := toSequenceOfBlowups_blowupMorphism_comp_concatMap_consolidated245 s t s' t' c e
  center_comap := append_center_eq_comap_concatMap_consolidated245 s t s' t' c e
  center_ne_top := append_center_ne_top_consolidated245 s t s' t' c e
  omitted := append_projectionToBase_ne_of_forall_concatIndex_ne_consolidated245 s t s' t' c e

end

end SequenceOfBlowupsPullback

theorem IsPullbackBlowupSequence.nonempty_sequenceOfBlowupsPullback {X X' : Scheme.{u}} {φ : X' ⟶ X}
    {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (h : IsPullbackBlowupSequence φ s' s) :
    Nonempty (SequenceOfBlowupsPullback φ s' s) := by
  obtain ⟨idx, e, hlt, hmono, hlen, hsup, hfst, hstep, hcen⟩ := h
  refine ⟨{
    idx := idx
    map := fun j hj => (e j hj).hom ≫ pullback.snd φ (s.projectionToBase (idx j))
    idx_length := hlen
    idx_lt := hlt
    idx_strictMono := fun j hj => hmono j (j + 1) hj (Nat.lt_succ_self j)
    isPullback := ?_
    step := ?_
    center_comap := ?_
    center_ne_top := ?_
    omitted := ?_ }⟩
  · intro j hj
    have hp : IsPullback ((e j hj).hom ≫ pullback.snd φ (s.projectionToBase (idx j)))
        ((e j hj).hom ≫ pullback.fst φ (s.projectionToBase (idx j))) (s.projectionToBase (idx j)) φ :=
      SequenceOfBlowupsPullback.isPullback_iso_hom_comp_consolidated245 (e j hj)
        (IsPullback.of_hasPullback φ (s.projectionToBase (idx j))).flip
    rw [hfst j hj] at hp
    exact hp
  · intro j hj
    have hr : idx j ≤ idx (j + 1) := le_of_lt (hmono j (j + 1) hj (Nat.lt_succ_self j))
    have hs2 : (s'.transitionMapSucc j ≫ (e j (le_of_lt hj)).hom) ≫
          pullback.snd φ (s.projectionToBase (idx j)) =
        ((e (j + 1) hj).hom ≫ s.pullbackTransitionMap φ hr) ≫ pullback.snd φ (s.projectionToBase (idx j)) :=
      congrArg (fun m => m ≫ pullback.snd φ (s.projectionToBase (idx j))) (hstep j hj hr)
    calc s'.transitionMapSucc j ≫ ((e j (le_of_lt hj)).hom ≫ pullback.snd φ (s.projectionToBase (idx j)))
        = (s'.transitionMapSucc j ≫ (e j (le_of_lt hj)).hom) ≫
            pullback.snd φ (s.projectionToBase (idx j)) := (Category.assoc _ _ _).symm
      _ = ((e (j + 1) hj).hom ≫ s.pullbackTransitionMap φ hr) ≫
            pullback.snd φ (s.projectionToBase (idx j)) := hs2
      _ = (e (j + 1) hj).hom ≫
            (s.pullbackTransitionMap φ hr ≫ pullback.snd φ (s.projectionToBase (idx j))) := Category.assoc _ _ _
      _ = (e (j + 1) hj).hom ≫
            (pullback.snd φ (s.projectionToBase (idx (j + 1))) ≫ s.transitionMap hr) := by
              rw [SequenceOfBlowups.pullbackTransitionMap_comp_snd]
      _ = ((e (j + 1) hj).hom ≫ pullback.snd φ (s.projectionToBase (idx (j + 1)))) ≫
            s.transitionMap hr := (Category.assoc _ _ _).symm
  · exact hcen
  · intro j hj htop
    obtain ⟨x, hx⟩ := (hsup (idx j) (hlt j hj)).mpr ⟨j, hj, rfl⟩
    refine AlgebraicGeometry.Scheme.IdealSheafData.ne_top_of_mem_support _ x hx ?_
    have h1 : (s.center (idx j)).comap
        ((e j (le_of_lt hj)).hom ≫ pullback.snd φ (s.projectionToBase (idx j))) = ⊤ :=
      (hcen j hj).symm.trans htop
    have h2 : ((s.center (idx j)).comap
          ((e j (le_of_lt hj)).hom ≫ pullback.snd φ (s.projectionToBase (idx j)))).comap
          (e j (le_of_lt hj)).inv =
        (⊤ : (s'.schemeAt j).IdealSheafData).comap (e j (le_of_lt hj)).inv := by
      rw [h1]
    rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id_assoc,
      AlgebraicGeometry.Scheme.IdealSheafData.comap_top] at h2
    exact h2
  · intro i hi hmiss z hz x' heq
    obtain ⟨w, _, hw2⟩ :=
      AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback x' z heq
    have hmem : w ∈ ((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support := by
      have hw : (pullback.snd φ (s.projectionToBase i)).base w ∈ (s.center i).support := by
        rw [hw2]
        exact hz
      exact AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.mpr hw
    obtain ⟨j, hj, hji⟩ := (hsup i hi).mp ⟨w, hmem⟩
    exact hmiss j hj hji

theorem isPullbackBlowupSequence_append_same_field {k : Type u} [Field k] {X X' : Scheme.{u}} (φ : X' ⟶ X)
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData}
    {p' : X' ⟶ Spec (CommRingCat.of k)} {I' : X'.IdealSheafData} {m' : ℕ}
    {E' : List X'.IdealSheafData}
    (S : MarkedBlowupSequenceData p I m E)
    (T : MarkedBlowupSequenceData (S.proj S.toBlowupSequenceData.length ≫ p) (S.ideal S.toBlowupSequenceData.length) m
      (S.boundary S.toBlowupSequenceData.length))
    (S' : MarkedBlowupSequenceData p' I' m' E')
    (T' : MarkedBlowupSequenceData (S'.proj S'.toBlowupSequenceData.length ≫ p') (S'.ideal S'.toBlowupSequenceData.length)
      m' (S'.boundary S'.toBlowupSequenceData.length))
    (hinv : ComapIsoInvariance.{u})
    (c : SequenceOfBlowupsPullback φ S'.toBlowupSequenceData.toSequenceOfBlowups S.toBlowupSequenceData.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap T'.toBlowupSequenceData.toSequenceOfBlowups T.toBlowupSequenceData.toSequenceOfBlowups) :
    IsPullbackBlowupSequence φ (S'.append T' hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (S.append T hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have C : SequenceOfBlowupsPullback φ (S'.toBlowupSequenceData.append T'.toBlowupSequenceData).toSequenceOfBlowups
      (S.toBlowupSequenceData.append T.toBlowupSequenceData).toSequenceOfBlowups :=
    SequenceOfBlowupsPullback.concat S.toBlowupSequenceData T.toBlowupSequenceData S'.toBlowupSequenceData T'.toBlowupSequenceData c e
  have h1 : (S.append T hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups =
      (S.toBlowupSequenceData.append T.toBlowupSequenceData).toSequenceOfBlowups :=
    MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups (S.append T hinv)
  have h2 : (S'.append T' hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups =
      (S'.toBlowupSequenceData.append T'.toBlowupSequenceData).toSequenceOfBlowups :=
    MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups (S'.append T' hinv)
  rw [h1, h2]
  exact C.isPullbackSequenceOfBlowups

theorem isPullbackBlowupSequence_append_of_two_fields {k k' : Type u} [Field k] [Field k']
    {X X' : Scheme.{u}} (φ : X' ⟶ X)
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData}
    {p' : X' ⟶ Spec (CommRingCat.of k')} {I' : X'.IdealSheafData} {m' : ℕ}
    {E' : List X'.IdealSheafData}
    (S : MarkedBlowupSequenceData p I m E)
    (T : MarkedBlowupSequenceData (S.proj S.toBlowupSequenceData.length ≫ p) (S.ideal S.toBlowupSequenceData.length) m
      (S.boundary S.toBlowupSequenceData.length))
    (S' : MarkedBlowupSequenceData p' I' m' E')
    (T' : MarkedBlowupSequenceData (S'.proj S'.toBlowupSequenceData.length ≫ p') (S'.ideal S'.toBlowupSequenceData.length)
      m' (S'.boundary S'.toBlowupSequenceData.length))
    (hinv : ComapIsoInvariance.{u})
    (c : SequenceOfBlowupsPullback φ S'.toBlowupSequenceData.toSequenceOfBlowups S.toBlowupSequenceData.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap T'.toBlowupSequenceData.toSequenceOfBlowups T.toBlowupSequenceData.toSequenceOfBlowups) :
    IsPullbackBlowupSequence φ (S'.append T' hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (S.append T hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have C : SequenceOfBlowupsPullback φ (S'.toBlowupSequenceData.append T'.toBlowupSequenceData).toSequenceOfBlowups
      (S.toBlowupSequenceData.append T.toBlowupSequenceData).toSequenceOfBlowups :=
    SequenceOfBlowupsPullback.concat S.toBlowupSequenceData T.toBlowupSequenceData S'.toBlowupSequenceData T'.toBlowupSequenceData c e
  have h1 : (S.append T hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups =
      (S.toBlowupSequenceData.append T.toBlowupSequenceData).toSequenceOfBlowups :=
    MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups (S.append T hinv)
  have h2 : (S'.append T' hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups =
      (S'.toBlowupSequenceData.append T'.toBlowupSequenceData).toSequenceOfBlowups :=
    MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups (S'.append T' hinv)
  rw [h1, h2]
  exact C.isPullbackSequenceOfBlowups


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.DisjointCentersPullback
section

open CategoryTheory.Limits

section

namespace SequenceOfBlowupsPullback

section
variable {A B C : Scheme.{u}}

private theorem base_comp_apply_consolidated265 (f : A ⟶ B) (g : B ⟶ C) (x : ↥A) :
    (f ≫ g).base x = g.base (f.base x) := by
  simp

private theorem eqToHom_base_trans_consolidated265 (h : A = B) (h' : B = C)
    (x : ↥A) : (eqToHom h').base ((eqToHom h).base x) = (eqToHom (h.trans h')).base x := by
  subst h
  subst h'
  simp


end

private theorem eqToHom_base_self_consolidated265 {A : Scheme.{u}} (h : A = A) (x : ↥A) :
    (eqToHom h).base x = x := by
  simp

private theorem inv_base_hom_base_consolidated265 {A B : Scheme.{u}} (e : A ≅ B) (x : ↥A) :
    e.inv.base (e.hom.base x) = x := by
  simp

section
variable {X : Scheme.{u}} (d : BlowupSequenceData X) {a b : ℕ} (hab : a = b) (h : d.obj a = d.obj b) (z : ↥(d.obj a))
include hab

private theorem eqToHom_base_mem_support_center_consolidated265 (hz : z ∈ (d.center a).support) : (eqToHom h).base z ∈ (d.center b).support := by
  subst hab
  simpa using hz

private theorem projectionToBase_base_eqToHom_base_consolidated265 :
    (d.projectionToBase b).base ((eqToHom h).base z) = (d.projectionToBase a).base z := by
  subst hab
  simp


end

section

private def mapOfLengthEqOne_consolidated265 {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X) (t' : BlowupSequenceData Y)
    (ht' : t'.length = 1) (q : t'.obj 1 ⟶ t.obj 1) :
    (j : ℕ) → j ≤ t'.toSequenceOfBlowups.length → (t'.toSequenceOfBlowups.schemeAt j ⟶ t.toSequenceOfBlowups.schemeAt j)
  | 0, _ =>
      eqToHom (t'.toSequenceOfBlowups_schemeAt 0) ≫ (t'.isoZero.hom ≫ g ≫ t.isoZero.inv) ≫
        eqToHom (t.toSequenceOfBlowups_schemeAt 0).symm
  | 1, _ => eqToHom (t'.toSequenceOfBlowups_schemeAt 1) ≫ q ≫ eqToHom (t.toSequenceOfBlowups_schemeAt 1).symm
  | (_ + 2), h => absurd h (by rw [BlowupSequenceData.toSequenceOfBlowups_length, ht']; omega)

section
variable {X Y : Scheme.{u}} (t : BlowupSequenceData X) (t' : BlowupSequenceData Y) (ht : t.length = 1) (ht' : t'.length = 1)
include ht ht'

private theorem length_eq_of_length_eq_one_consolidated265 : t'.toSequenceOfBlowups.length = t.toSequenceOfBlowups.length := by
  rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.toSequenceOfBlowups_length, ht', ht]

private theorem lt_length_of_length_eq_one_consolidated265 :
    ∀ j : ℕ, j < t'.toSequenceOfBlowups.length → j < t.toSequenceOfBlowups.length := by
  intro j hj
  rw [length_eq_of_length_eq_one_consolidated265 t t' ht ht'] at hj
  exact hj


end

private theorem index_strictMono_of_length_eq_one_consolidated265 {Y : Scheme.{u}} (t' : BlowupSequenceData Y)
    (_ht' : t'.length = 1) : ∀ j : ℕ, j < t'.toSequenceOfBlowups.length → j < j + 1 :=
  fun j _ => Nat.lt_succ_self j

section
variable {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X) (t' : BlowupSequenceData Y) (_ht : t.length = 1) (ht' : t'.length = 1) (q : t'.obj 1 ⟶ t.obj 1)
include _ht

private theorem isPullback_of_length_eq_one_consolidated265 (hq : IsPullback q (t'.map 0) (t.map 0) (t'.isoZero.hom ≫ g ≫ t.isoZero.inv)) :
    ∀ (j : ℕ) (hj : j ≤ t'.toSequenceOfBlowups.length),
      IsPullback (mapOfLengthEqOne_consolidated265 g t t' ht' q j hj) (t'.toSequenceOfBlowups.projectionToBase j) (t.toSequenceOfBlowups.projectionToBase j) g := by
  have hlen : t'.toSequenceOfBlowups.length = 1 := by rw [BlowupSequenceData.toSequenceOfBlowups_length, ht']
  have hzero : IsPullback (t'.isoZero.hom ≫ g ≫ t.isoZero.inv) t'.isoZero.hom
      t.isoZero.hom g := by
    have hsq : CommSq t'.isoZero.hom (t'.isoZero.hom ≫ g ≫ t.isoZero.inv) g t.isoZero.hom := by
      constructor
      simp
    exact (IsPullback.of_horiz_isIso hsq).flip
  have hs0' : t'.toSequenceOfBlowups.projectionToBase 0 = t'.isoZero.hom := by
    rw [BlowupSequenceData.toSequenceOfBlowups_projectionToBase, BlowupSequenceData.projectionToBase_zero]
  have hs0 : t.toSequenceOfBlowups.projectionToBase 0 = t.isoZero.hom := by
    rw [BlowupSequenceData.toSequenceOfBlowups_projectionToBase, BlowupSequenceData.projectionToBase_zero]
  have hs1' : t'.toSequenceOfBlowups.projectionToBase 1 = t'.map 0 ≫ t'.isoZero.hom := by
    rw [BlowupSequenceData.toSequenceOfBlowups_projectionToBase]
    show t'.projectionToBase (0 + 1) = t'.map 0 ≫ t'.isoZero.hom
    rw [BlowupSequenceData.projectionToBase_succ, BlowupSequenceData.projectionToBase_zero]
  have hs1 : t.toSequenceOfBlowups.projectionToBase 1 = t.map 0 ≫ t.isoZero.hom := by
    rw [BlowupSequenceData.toSequenceOfBlowups_projectionToBase]
    show t.projectionToBase (0 + 1) = t.map 0 ≫ t.isoZero.hom
    rw [BlowupSequenceData.projectionToBase_succ, BlowupSequenceData.projectionToBase_zero]
  intro j hj
  have hj1 : j = 0 ∨ j = 1 := by omega
  rcases hj1 with rfl | rfl
  · have hmap : mapOfLengthEqOne_consolidated265 g t t' ht' q 0 hj = t'.isoZero.hom ≫ g ≫ t.isoZero.inv :=
      (Category.id_comp ((t'.isoZero.hom ≫ g ≫ t.isoZero.inv) ≫
          eqToHom (t.toSequenceOfBlowups_schemeAt 0).symm)).trans
        (Category.comp_id (t'.isoZero.hom ≫ g ≫ t.isoZero.inv))
    rw [hmap, hs0, hs0']
    exact hzero
  · have hmap : mapOfLengthEqOne_consolidated265 g t t' ht' q 1 hj = q :=
      (Category.id_comp (q ≫ eqToHom (t.toSequenceOfBlowups_schemeAt 1).symm)).trans (Category.comp_id q)
    rw [hmap, hs1, hs1']
    exact hq.paste_vert hzero

private theorem blowupMorphism_comp_of_length_eq_one_consolidated265 (hq : IsPullback q (t'.map 0) (t.map 0) (t'.isoZero.hom ≫ g ≫ t.isoZero.inv)) :
    ∀ (j : ℕ) (hj : j < t'.toSequenceOfBlowups.length),
      t'.toSequenceOfBlowups.transitionMapSucc j ≫ mapOfLengthEqOne_consolidated265 g t t' ht' q j (le_of_lt hj) =
        mapOfLengthEqOne_consolidated265 g t t' ht' q (j + 1) hj ≫
          t.toSequenceOfBlowups.transitionMap (le_of_lt (index_strictMono_of_length_eq_one_consolidated265 t' ht' j hj)) := by
  intro j hj
  have hlen : t'.toSequenceOfBlowups.length = t'.length := t'.toSequenceOfBlowups_length
  have hj0 : j = 0 := by omega
  subst hj0
  have h1 : t'.toSequenceOfBlowups.transitionMapSucc 0 = t'.map 0 := t'.toSequenceOfBlowups_blowupMorphism 0
  have h2 : t.toSequenceOfBlowups.transitionMap (le_of_lt (index_strictMono_of_length_eq_one_consolidated265 t' ht' 0 hj)) = t.map 0 :=
    (t.toSequenceOfBlowups.blowupMorphism_eq_transitionMap 0).symm.trans (t.toSequenceOfBlowups_blowupMorphism 0)
  rw [h1, h2]
  show t'.map 0 ≫ (𝟙 (t'.obj 0) ≫ (t'.isoZero.hom ≫ g ≫ t.isoZero.inv) ≫ 𝟙 (t.obj 0)) =
    (𝟙 (t'.obj 1) ≫ q ≫ 𝟙 (t.obj 1)) ≫ t.map 0
  simp only [Category.id_comp, Category.comp_id]
  exact hq.w.symm

private theorem center_eq_comap_of_length_eq_one_consolidated265 (hcen : t'.center 0 = (t.center 0).comap (t'.isoZero.hom ≫ g ≫ t.isoZero.inv)) :
    ∀ (j : ℕ) (hj : j < t'.toSequenceOfBlowups.length),
      t'.toSequenceOfBlowups.center j = (t.toSequenceOfBlowups.center j).comap (mapOfLengthEqOne_consolidated265 g t t' ht' q j (le_of_lt hj)) := by
  have hlen : t'.toSequenceOfBlowups.length = 1 := by rw [BlowupSequenceData.toSequenceOfBlowups_length, ht']
  intro j hj
  have hj0 : j = 0 := by omega
  subst hj0
  have hmap : mapOfLengthEqOne_consolidated265 g t t' ht' q 0 (le_of_lt hj) =
      t'.isoZero.hom ≫ g ≫ t.isoZero.inv :=
    (Category.id_comp ((t'.isoZero.hom ≫ g ≫ t.isoZero.inv) ≫
        eqToHom (t.toSequenceOfBlowups_schemeAt 0).symm)).trans
      (Category.comp_id (t'.isoZero.hom ≫ g ≫ t.isoZero.inv))
  rw [hmap, BlowupSequenceData.toSequenceOfBlowups_center, BlowupSequenceData.toSequenceOfBlowups_center]
  exact hcen


end

private theorem center_ne_top_of_length_eq_one_consolidated265 {Y : Scheme.{u}} (t' : BlowupSequenceData Y)
    (ht' : t'.length = 1) (hne : t'.center 0 ≠ ⊤) :
    ∀ j : ℕ, j < t'.toSequenceOfBlowups.length → t'.toSequenceOfBlowups.center j ≠ ⊤ := by
  have hlen : t'.toSequenceOfBlowups.length = 1 := by rw [BlowupSequenceData.toSequenceOfBlowups_length, ht']
  intro j hj
  rw [hlen] at hj
  have hj0 : j = 0 := by omega
  subst hj0
  rw [BlowupSequenceData.toSequenceOfBlowups_center]
  exact hne

private theorem disjoint_omitted_centers_of_length_eq_one_consolidated265 {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (t' : BlowupSequenceData Y) (ht : t.length = 1) (ht' : t'.length = 1) :
    ∀ i : ℕ, i < t.toSequenceOfBlowups.length → (∀ j : ℕ, j < t'.toSequenceOfBlowups.length → j ≠ i) →
      ∀ z : ↥(t.toSequenceOfBlowups.schemeAt i), z ∈ (t.toSequenceOfBlowups.center i).support →
        ∀ x' : ↥Y, g.base x' ≠ (t.toSequenceOfBlowups.projectionToBase i).base z := by
  have hlen : t.toSequenceOfBlowups.length = 1 := t.toSequenceOfBlowups_length.trans ht
  have hlen' : t'.toSequenceOfBlowups.length = 1 := t'.toSequenceOfBlowups_length.trans ht'
  intro i hi hmiss
  have hi0 : i = 0 := by omega
  have h0 : (0 : ℕ) < t'.toSequenceOfBlowups.length := by omega
  exact absurd hi0.symm (hmiss 0 h0)

def ofLengthOne {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X) (t' : BlowupSequenceData Y)
    (ht : t.length = 1) (ht' : t'.length = 1) (q : t'.obj 1 ⟶ t.obj 1)
    (hq : IsPullback q (t'.map 0) (t.map 0) (t'.isoZero.hom ≫ g ≫ t.isoZero.inv))
    (hcen : t'.center 0 = (t.center 0).comap (t'.isoZero.hom ≫ g ≫ t.isoZero.inv))
    (hne : t'.center 0 ≠ ⊤) :
    SequenceOfBlowupsPullback g t'.toSequenceOfBlowups t.toSequenceOfBlowups where
  idx := fun j => j
  map := mapOfLengthEqOne_consolidated265 g t t' ht' q
  idx_length := length_eq_of_length_eq_one_consolidated265 t t' ht ht'
  idx_lt := lt_length_of_length_eq_one_consolidated265 t t' ht ht'
  idx_strictMono := index_strictMono_of_length_eq_one_consolidated265 t' ht'
  isPullback := isPullback_of_length_eq_one_consolidated265 g t t' ht ht' q hq
  step := blowupMorphism_comp_of_length_eq_one_consolidated265 g t t' ht ht' q hq
  center_comap := center_eq_comap_of_length_eq_one_consolidated265 g t t' ht ht' q hcen
  center_ne_top := center_ne_top_of_length_eq_one_consolidated265 t' ht' hne
  omitted := disjoint_omitted_centers_of_length_eq_one_consolidated265 g t t' ht ht'

end

theorem comap_eq_top_of_forall_support_not_mem_range {X Y T : Scheme.{u}} (g : Y ⟶ X) (π : T ⟶ X)
    (I : T.IdealSheafData)
    (hmiss : ∀ z : ↥T, z ∈ I.support → ∀ y : ↥Y, g.base y ≠ π.base z)
    (u : Y ⟶ T) (hu : IsPullback u (𝟙 Y) π g) : I.comap u = ⊤ := by
  have hcomm : u ≫ π = g := by
    have h := hu.w
    rwa [Category.id_comp] at h
  have hb : ∀ y : ↥Y, π.base (u.base y) = g.base y := by
    intro y
    have h1 : (u ≫ π).base y = g.base y := by rw [hcomm]
    simpa using h1
  have hsupp : (I.comap u).support = ⊥ := by
    rw [Scheme.IdealSheafData.support_comap]
    refine le_antisymm ?_ bot_le
    intro y hy
    have hz : u.base y ∈ I.support := hy
    exact absurd (hb y).symm (hmiss (u.base y) hz y)
  exact (Scheme.IdealSheafData.support_eq_bot_iff _).mp hsupp

section

private def IsDisjointFromCenters_consolidated265 {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X) : Prop :=
  ∀ i : ℕ, i < t.length → ∀ z : ↥(t.obj i), z ∈ (t.center i).support →
    ∀ y : ↥Y, g.base y ≠ (t.projectionToBase i).base z

private theorem isIso_pullbackSnd_of_flat_of_disjoint_consolidated265 {X Y : Scheme.{u}} (g : Y ⟶ X) [Flat g]
    (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters_consolidated265 g t) (i : ℕ) (hi : i < t.length) (u : Y ⟶ t.obj i)
    (hu : IsPullback u (𝟙 Y) (t.projectionToBase i) g) : IsIso (pullback.snd (t.map i) u) := by
  have hB : Blowup.IsBlowupAlongIdealSheaf (t.map i) (t.center i) := t.isBlowup i hi
  have htop : (t.center i).comap u = ⊤ :=
    comap_eq_top_of_forall_support_not_mem_range g (t.projectionToBase i) (t.center i) (hmiss i hi) u hu
  have hEC : Blowup.IsLocallyGeneratedByNonZeroDivisor ((t.center i).comap u) := by
    rw [htop]
    exact Blowup.isLocallyGeneratedByNonZeroDivisor_top Y
  obtain ⟨k, hk, -⟩ := hB.existsUnique_lift Y u hEC
  have hw : k ≫ t.map i = 𝟙 Y ≫ u := by rw [hk, Category.id_comp]
  have hEC2 : Blowup.IsLocallyGeneratedByNonZeroDivisor ((t.center i).comap (pullback.snd (t.map i) u ≫ u)) := by
    have hc : (t.center i).comap (pullback.snd (t.map i) u ≫ u) =
        ((t.center i).comap u).comap (pullback.snd (t.map i) u) := by
      simp [Scheme.IdealSheafData.comap_comp]
    rw [hc, htop]
    exact Blowup.isLocallyGeneratedByNonZeroDivisor_comap_top _
  refine ⟨⟨pullback.lift k (𝟙 Y) hw, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      refine hB.hom_ext_of_comp_eq hEC2 ?_ pullback.condition
      rw [Category.assoc, hk]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  · rw [pullback.lift_snd]

private noncomputable def liftSuccOfIsDisjointFromCenters {X Y : Scheme.{u}} (g : Y ⟶ X) [Flat g]
    (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters_consolidated265 g t) (i : ℕ) (hi : i < t.length) (u : Y ⟶ t.obj i)
    (hu : IsPullback u (𝟙 Y) (t.projectionToBase i) g) : Y ⟶ t.obj (i + 1) :=
  letI := isIso_pullbackSnd_of_flat_of_disjoint_consolidated265 g t hmiss i hi u hu
  inv (pullback.snd (t.map i) u) ≫ pullback.fst (t.map i) u

section
variable {X Y : Scheme.{u}} (g : Y ⟶ X)

private theorem isPullback_liftSuccOfIsDisjointFromCenters_consolidated265 [Flat g]
    (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters_consolidated265 g t) (i : ℕ) (hi : i < t.length) (u : Y ⟶ t.obj i)
    (hu : IsPullback u (𝟙 Y) (t.projectionToBase i) g) :
    IsPullback (liftSuccOfIsDisjointFromCenters g t hmiss i hi u hu) (𝟙 Y) (t.projectionToBase (i + 1)) g := by
  have hiso : IsIso (pullback.snd (t.map i) u) := isIso_pullbackSnd_of_flat_of_disjoint_consolidated265 g t hmiss i hi u hu
  have hsq : IsPullback (inv (pullback.snd (t.map i) u) ≫ pullback.fst (t.map i) u) (𝟙 Y)
      (t.map i) u := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso (pullback.snd (t.map i) u)).symm ?_ ?_
    · rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc, Category.id_comp]
    · simp
    · simp
  have hpaste := hsq.paste_vert hu
  simp only [Category.comp_id] at hpaste
  rw [BlowupSequenceData.projectionToBase_succ]
  exact hpaste

private theorem isPullback_comp_isoObjZero_inv_consolidated265 (t : BlowupSequenceData X) :
    IsPullback (g ≫ t.isoZero.inv) (𝟙 Y) (t.projectionToBase 0) g := by
  have hiso : IsIso (t.projectionToBase 0) := by
    rw [t.projectionToBase_zero]
    infer_instance
  have hsq : CommSq (𝟙 Y) (g ≫ t.isoZero.inv) g (t.projectionToBase 0) := by
    constructor
    simp [t.projectionToBase_zero]
  exact (IsPullback.of_horiz_isIso hsq).flip


end

private noncomputable def liftOfIsDisjointFromCenters {X Y : Scheme.{u}} (g : Y ⟶ X) [Flat g]
    (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters_consolidated265 g t) :
    (i : ℕ) → i ≤ t.length → {u : Y ⟶ t.obj i // IsPullback u (𝟙 Y) (t.projectionToBase i) g}
  | 0, _ => ⟨g ≫ t.isoZero.inv, isPullback_comp_isoObjZero_inv_consolidated265 g t⟩
  | (i + 1), h =>
      let hi : i < t.length := by omega
      let prev := liftOfIsDisjointFromCenters g t hmiss i hi.le
      ⟨liftSuccOfIsDisjointFromCenters g t hmiss i hi prev.1 prev.2, isPullback_liftSuccOfIsDisjointFromCenters_consolidated265 g t hmiss i hi prev.1 prev.2⟩

private noncomputable def liftToLastOfFlatOfIsDisjointFromCenters {X Y : Scheme.{u}} (g : Y ⟶ X) [Flat g]
    (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters_consolidated265 g t) : Y ⟶ t.obj t.length :=
  (liftOfIsDisjointFromCenters g t hmiss t.length le_rfl).1

private theorem schemeAt_eq_schemeAt_zero_of_length_eq_zero_consolidated265 {Y : Scheme.{u}} (e : BlowupSequenceData Y) (he : e.length = 0) (j : ℕ)
    (hj : j ≤ e.toSequenceOfBlowups.length) : e.toSequenceOfBlowups.schemeAt j = e.obj 0 := by
  have hlen : e.toSequenceOfBlowups.length = 0 := e.toSequenceOfBlowups_length.trans he
  have hj0 : j = 0 := by omega
  subst hj0
  exact e.toSequenceOfBlowups_schemeAt 0

private noncomputable def mapToLastOfFlatOfLengthEqZero {X Y : Scheme.{u}} (g : Y ⟶ X) [Flat g]
    (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters_consolidated265 g t) (e : BlowupSequenceData Y) (he : e.length = 0)
    (j : ℕ) (hj : j ≤ e.toSequenceOfBlowups.length) : e.toSequenceOfBlowups.schemeAt j ⟶ t.toSequenceOfBlowups.schemeAt t.length :=
  eqToHom (schemeAt_eq_schemeAt_zero_of_length_eq_zero_consolidated265 e he j hj) ≫ e.isoZero.hom ≫ liftToLastOfFlatOfIsDisjointFromCenters g t hmiss ≫
    eqToHom (t.toSequenceOfBlowups_schemeAt t.length).symm

private theorem length_eq_toSequenceOfBlowups_length_consolidated265 {X : Scheme.{u}} (t : BlowupSequenceData X) :
    t.length = t.toSequenceOfBlowups.length := (t.toSequenceOfBlowups_length).symm

section
variable {X Y : Scheme.{u}} (t : BlowupSequenceData X) (e : BlowupSequenceData Y) (he : e.length = 0)
include he

private theorem length_lt_toSequenceOfBlowups_length_of_lt_consolidated265 : ∀ j : ℕ, j < e.toSequenceOfBlowups.length → t.length < t.toSequenceOfBlowups.length := by
  intro j hj
  rw [BlowupSequenceData.toSequenceOfBlowups_length, he] at hj
  exact absurd hj (Nat.not_lt_zero j)

private theorem length_lt_length_of_lt_length_of_eq_zero_consolidated265 : ∀ j : ℕ, j < e.toSequenceOfBlowups.length → t.length < t.length := by
  intro j hj
  rw [BlowupSequenceData.toSequenceOfBlowups_length, he] at hj
  exact absurd hj (Nat.not_lt_zero j)


end

section
variable {X Y : Scheme.{u}} (g : Y ⟶ X) [Flat g] (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters_consolidated265 g t) (e : BlowupSequenceData Y) (he : e.length = 0)

private theorem isPullback_of_disjoint_centers_consolidated265 :
    ∀ (j : ℕ) (hj : j ≤ e.toSequenceOfBlowups.length),
      IsPullback (mapToLastOfFlatOfLengthEqZero g t hmiss e he j hj) (e.toSequenceOfBlowups.projectionToBase j)
        (t.toSequenceOfBlowups.projectionToBase t.length) g := by
  have hlen : e.toSequenceOfBlowups.length = 0 := e.toSequenceOfBlowups_length.trans he
  intro j hj
  have hj0 : j = 0 := by omega
  subst hj0
  have hpb : IsPullback (liftToLastOfFlatOfIsDisjointFromCenters g t hmiss) (𝟙 Y) (t.projectionToBase t.length) g :=
    (liftOfIsDisjointFromCenters g t hmiss t.length le_rfl).2
  have hiso : IsPullback e.isoZero.hom e.isoZero.hom (𝟙 Y) (𝟙 Y) :=
    IsPullback.of_horiz_isIso ⟨rfl⟩
  have hcomp := hiso.paste_horiz hpb
  simp only [Category.id_comp] at hcomp
  have hmap : mapToLastOfFlatOfLengthEqZero g t hmiss e he 0 hj = e.isoZero.hom ≫ liftToLastOfFlatOfIsDisjointFromCenters g t hmiss := by
    show 𝟙 (e.obj 0) ≫ e.isoZero.hom ≫ liftToLastOfFlatOfIsDisjointFromCenters g t hmiss ≫ 𝟙 (t.obj t.length) =
      e.isoZero.hom ≫ liftToLastOfFlatOfIsDisjointFromCenters g t hmiss
    simp
  have hs : e.toSequenceOfBlowups.projectionToBase 0 = e.isoZero.hom :=
    (e.toSequenceOfBlowups_projectionToBase 0).trans e.projectionToBase_zero
  have hf : t.toSequenceOfBlowups.projectionToBase t.length = t.projectionToBase t.length := t.toSequenceOfBlowups_projectionToBase t.length
  rw [hmap, hs, hf]
  exact hcomp

private theorem blowupMorphism_comp_of_disjoint_centers_consolidated265 :
    ∀ (j : ℕ) (hj : j < e.toSequenceOfBlowups.length),
      e.toSequenceOfBlowups.transitionMapSucc j ≫ mapToLastOfFlatOfLengthEqZero g t hmiss e he j (le_of_lt hj) =
        mapToLastOfFlatOfLengthEqZero g t hmiss e he (j + 1) hj ≫
          t.toSequenceOfBlowups.transitionMap (le_of_lt (length_lt_length_of_lt_length_of_eq_zero_consolidated265 t e he j hj)) := by
  intro j hj
  have hlen : e.toSequenceOfBlowups.length = 0 := e.toSequenceOfBlowups_length.trans he
  exact absurd hj (by rw [hlen]; exact Nat.not_lt_zero j)

private theorem center_eq_comap_lastCenter_of_disjoint_of_flat_consolidated265 :
    ∀ (j : ℕ) (hj : j < e.toSequenceOfBlowups.length),
      e.toSequenceOfBlowups.center j =
        (t.toSequenceOfBlowups.center t.length).comap (mapToLastOfFlatOfLengthEqZero g t hmiss e he j (le_of_lt hj)) := by
  have hlen : e.toSequenceOfBlowups.length = 0 := e.toSequenceOfBlowups_length.trans he
  intro j hj
  exact absurd hj (by omega)


end

private theorem center_ne_top_of_length_eq_zero_consolidated265 {Y : Scheme.{u}} (e : BlowupSequenceData Y) (he : e.length = 0) :
    ∀ j : ℕ, j < e.toSequenceOfBlowups.length → e.toSequenceOfBlowups.center j ≠ ⊤ := by
  intro j hj
  rw [BlowupSequenceData.toSequenceOfBlowups_length, he] at hj
  exact absurd hj (Nat.not_lt_zero j)

private theorem disjoint_omitted_centers_of_disjoint_centers_consolidated265 {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (hmiss : IsDisjointFromCenters_consolidated265 g t) (e : BlowupSequenceData Y) (_he : e.length = 0) :
    ∀ i : ℕ, i < t.toSequenceOfBlowups.length → (∀ j : ℕ, j < e.toSequenceOfBlowups.length → t.length ≠ i) →
      ∀ z : ↥(t.toSequenceOfBlowups.schemeAt i), z ∈ (t.toSequenceOfBlowups.center i).support →
        ∀ x' : ↥Y, g.base x' ≠ (t.toSequenceOfBlowups.projectionToBase i).base z := by
  intro i hi _hmiss z hz x'
  have hi' : i < t.length := by
    rwa [BlowupSequenceData.toSequenceOfBlowups_length] at hi
  have hz' : z ∈ (t.center i).support := by
    rwa [BlowupSequenceData.toSequenceOfBlowups_center] at hz
  have hne := hmiss i hi' z hz' x'
  rwa [BlowupSequenceData.toSequenceOfBlowups_projectionToBase]

noncomputable def ofCentersMissImage {X Y : Scheme.{u}} (g : Y ⟶ X) [Flat g]
    (t : BlowupSequenceData X)
    (hmiss : ∀ i : ℕ, i < t.length → ∀ z : ↥(t.obj i), z ∈ (t.center i).support →
      ∀ y : ↥Y, g.base y ≠ (t.projectionToBase i).base z)
    (e : BlowupSequenceData Y) (he : e.length = 0) :
    SequenceOfBlowupsPullback g e.toSequenceOfBlowups t.toSequenceOfBlowups where
  idx := fun _ => t.length
  map := mapToLastOfFlatOfLengthEqZero g t hmiss e he
  idx_length := length_eq_toSequenceOfBlowups_length_consolidated265 t
  idx_lt := length_lt_toSequenceOfBlowups_length_of_lt_consolidated265 t e he
  idx_strictMono := length_lt_length_of_lt_length_of_eq_zero_consolidated265 t e he
  isPullback := isPullback_of_disjoint_centers_consolidated265 g t hmiss e he
  step := blowupMorphism_comp_of_disjoint_centers_consolidated265 g t hmiss e he
  center_comap := center_eq_comap_lastCenter_of_disjoint_of_flat_consolidated265 g t hmiss e he
  center_ne_top := center_ne_top_of_length_eq_zero_consolidated265 e he
  omitted := disjoint_omitted_centers_of_disjoint_centers_consolidated265 g t hmiss e he

end

section

section
variable {X' : Scheme.{u}} (s' : BlowupSequenceData X') (n : BlowupSequenceData (s'.obj s'.length))

private theorem schemeAt_eq_schemeAt_append_consolidated265 (j : ℕ) (hj : j ≤ s'.toSequenceOfBlowups.length) :
    s'.toSequenceOfBlowups.schemeAt j = (s'.append n).toSequenceOfBlowups.schemeAt j := by
  rw [BlowupSequenceData.toSequenceOfBlowups_length] at hj
  rw [BlowupSequenceData.toSequenceOfBlowups_schemeAt s' j, BlowupSequenceData.toSequenceOfBlowups_schemeAt (s'.append n) j,
    BlowupSequenceData.append_schemeAt_of_le_length s' n hj]

private theorem le_length_append_of_length_eq_zero_consolidated265 (hn : n.length = 0) (j : ℕ) (hj : j ≤ s'.toSequenceOfBlowups.length) :
    j ≤ (s'.append n).toSequenceOfBlowups.length := by
  rw [BlowupSequenceData.toSequenceOfBlowups_length] at hj
  rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.append_length, hn]
  omega


end

private noncomputable def mapOfAppendLengthEqZero {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X')
    (s : SequenceOfBlowups X) (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0)
    (c : SequenceOfBlowupsPullback φ (s'.append n).toSequenceOfBlowups s) (j : ℕ) (hj : j ≤ s'.toSequenceOfBlowups.length) :
    s'.toSequenceOfBlowups.schemeAt j ⟶ s.schemeAt (c.idx j) :=
  eqToHom (schemeAt_eq_schemeAt_append_consolidated265 s' n j hj) ≫ c.map j (le_length_append_of_length_eq_zero_consolidated265 s' n hn j hj)

section
variable {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X') (s : SequenceOfBlowups X) (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0) (c : SequenceOfBlowupsPullback φ (s'.append n).toSequenceOfBlowups s)
include hn

private theorem index_length_of_append_length_eq_zero_consolidated265 : c.idx s'.toSequenceOfBlowups.length = s.length := by
  have h1 : (s'.append n).toSequenceOfBlowups.length = s'.toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.append_length, hn]
    omega
  rw [← h1]
  exact c.idx_length

private theorem index_lt_length_of_append_length_eq_zero_consolidated265 :
    ∀ j : ℕ, j < s'.toSequenceOfBlowups.length → c.idx j < s.length := by
  intro j hj
  rw [BlowupSequenceData.toSequenceOfBlowups_length] at hj
  have h : j < (s'.append n).toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.append_length, hn]
    omega
  exact c.idx_lt j h

private theorem index_lt_index_succ_of_append_length_eq_zero_consolidated265 :
    ∀ j : ℕ, j < s'.toSequenceOfBlowups.length → c.idx j < c.idx (j + 1) := by
  intro j hj
  rw [BlowupSequenceData.toSequenceOfBlowups_length] at hj
  refine c.idx_strictMono j ?_
  rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.append_length, hn]
  omega


end

private theorem eqToHom_comp_eqToHom_comp_eq_consolidated265 {A B C : Scheme.{u}} (h : A = B) (h' : B = A)
    (g : A ⟶ C) : eqToHom h ≫ eqToHom h' ≫ g = g := by
  subst h
  simp

private theorem eqToHom_comp_append_projectionToBase_consolidated265 {X' : Scheme.{u}} (s' : BlowupSequenceData X')
    (n : BlowupSequenceData (s'.obj s'.length)) (j : ℕ) (hj : j ≤ s'.toSequenceOfBlowups.length) :
    eqToHom (schemeAt_eq_schemeAt_append_consolidated265 s' n j hj) ≫ (s'.append n).toSequenceOfBlowups.projectionToBase j = s'.toSequenceOfBlowups.projectionToBase j := by
  have hjl : j ≤ s'.length := by rwa [BlowupSequenceData.toSequenceOfBlowups_length] at hj
  have h1 : (s'.append n).toSequenceOfBlowups.projectionToBase j = (s'.append n).projectionToBase j :=
    BlowupSequenceData.toSequenceOfBlowups_projectionToBase (s'.append n) j
  have h2 : s'.toSequenceOfBlowups.projectionToBase j = s'.projectionToBase j := BlowupSequenceData.toSequenceOfBlowups_projectionToBase s' j
  rw [h1, h2, BlowupSequenceData.projectionToBase_append_of_le_length s' n hjl]
  exact eqToHom_comp_eqToHom_comp_eq_consolidated265 _ _ _

private theorem isPullback_of_append_length_eq_zero_consolidated265 {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X')
    (s : SequenceOfBlowups X) (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0)
    (c : SequenceOfBlowupsPullback φ (s'.append n).toSequenceOfBlowups s) :
    ∀ (j : ℕ) (hj : j ≤ s'.toSequenceOfBlowups.length),
      IsPullback (mapOfAppendLengthEqZero φ s' s n hn c j hj) (s'.toSequenceOfBlowups.projectionToBase j) (s.projectionToBase (c.idx j)) φ := by
  intro j hj
  have hc := c.isPullback j (le_length_append_of_length_eq_zero_consolidated265 s' n hn j hj)
  have hsq : CommSq (eqToHom (schemeAt_eq_schemeAt_append_consolidated265 s' n j hj)) (s'.toSequenceOfBlowups.projectionToBase j)
      ((s'.append n).toSequenceOfBlowups.projectionToBase j) (𝟙 X') := by
    constructor
    rw [Category.comp_id]
    exact eqToHom_comp_append_projectionToBase_consolidated265 s' n j hj
  have hiso : IsPullback (eqToHom (schemeAt_eq_schemeAt_append_consolidated265 s' n j hj)) (s'.toSequenceOfBlowups.projectionToBase j)
      ((s'.append n).toSequenceOfBlowups.projectionToBase j) (𝟙 X') := IsPullback.of_horiz_isIso hsq
  have hpaste := hiso.paste_horiz hc
  rw [Category.id_comp] at hpaste
  exact hpaste

private theorem comp_eqToHom_eq_eqToHom_comp_consolidated265 {A B A' B' : Scheme.{u}} (f : A ⟶ B) (f' : A' ⟶ B')
    (hA : A = A') (hB : B = B') (h : f' = eqToHom hA.symm ≫ f ≫ eqToHom hB) :
    f ≫ eqToHom hB = eqToHom hA ≫ f' := by
  subst hA
  subst hB
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h ⊢
  exact h.symm

private theorem blowupMorphism_comp_of_append_length_eq_zero_consolidated265 {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X')
    (s : SequenceOfBlowups X) (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0)
    (c : SequenceOfBlowupsPullback φ (s'.append n).toSequenceOfBlowups s) :
    ∀ (j : ℕ) (hj : j < s'.toSequenceOfBlowups.length),
      s'.toSequenceOfBlowups.transitionMapSucc j ≫ mapOfAppendLengthEqZero φ s' s n hn c j (le_of_lt hj) =
        mapOfAppendLengthEqZero φ s' s n hn c (j + 1) hj ≫
          s.transitionMap (le_of_lt (index_lt_index_succ_of_append_length_eq_zero_consolidated265 φ s' s n hn c j hj)) := by
  intro j hj
  have hjl : j < s'.length := by rwa [BlowupSequenceData.toSequenceOfBlowups_length] at hj
  have hjc : j < (s'.append n).toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.append_length, hn]
    omega
  have hkey : s'.toSequenceOfBlowups.transitionMapSucc j ≫ eqToHom (schemeAt_eq_schemeAt_append_consolidated265 s' n j (le_of_lt hj)) =
      eqToHom (schemeAt_eq_schemeAt_append_consolidated265 s' n (j + 1) hj) ≫ (s'.append n).toSequenceOfBlowups.transitionMapSucc j := by
    refine comp_eqToHom_eq_eqToHom_comp_consolidated265 (s'.toSequenceOfBlowups.transitionMapSucc j) ((s'.append n).toSequenceOfBlowups.transitionMapSucc j)
      (schemeAt_eq_schemeAt_append_consolidated265 s' n (j + 1) hj) (schemeAt_eq_schemeAt_append_consolidated265 s' n j (le_of_lt hj)) ?_
    rw [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.toSequenceOfBlowups_blowupMorphism]
    exact BlowupSequenceData.append_blowupMorphism_of_lt_length s' n hjl
  have hstep : (s'.append n).toSequenceOfBlowups.transitionMapSucc j ≫ c.map j (le_length_append_of_length_eq_zero_consolidated265 s' n hn j (le_of_lt hj)) =
      c.map (j + 1) (le_length_append_of_length_eq_zero_consolidated265 s' n hn (j + 1) hj) ≫
        s.transitionMap (le_of_lt (index_lt_index_succ_of_append_length_eq_zero_consolidated265 φ s' s n hn c j hj)) := c.step j hjc
  show s'.toSequenceOfBlowups.transitionMapSucc j ≫
      eqToHom (schemeAt_eq_schemeAt_append_consolidated265 s' n j (le_of_lt hj)) ≫ c.map j (le_length_append_of_length_eq_zero_consolidated265 s' n hn j (le_of_lt hj)) =
    (eqToHom (schemeAt_eq_schemeAt_append_consolidated265 s' n (j + 1) hj) ≫ c.map (j + 1) (le_length_append_of_length_eq_zero_consolidated265 s' n hn (j + 1) hj)) ≫
      s.transitionMap (le_of_lt (index_lt_index_succ_of_append_length_eq_zero_consolidated265 φ s' s n hn c j hj))
  rw [← Category.assoc, hkey, Category.assoc, hstep, Category.assoc]

private theorem comap_eqToHom_comap_eqToHom_consolidated265 {A B : Scheme.{u}} (h : A = B) (h' : B = A)
    (I : A.IdealSheafData) : (I.comap (eqToHom h')).comap (eqToHom h) = I := by
  subst h
  simp

section
variable {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X') (s : SequenceOfBlowups X) (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0) (c : SequenceOfBlowupsPullback φ (s'.append n).toSequenceOfBlowups s)
include hn c

private theorem center_eq_comap_of_append_length_eq_zero_consolidated265 :
    ∀ (j : ℕ) (hj : j < s'.toSequenceOfBlowups.length),
      s'.toSequenceOfBlowups.center j = (s.center (c.idx j)).comap (mapOfAppendLengthEqZero φ s' s n hn c j (le_of_lt hj)) := by
  intro j hj
  have hjl : j < s'.length := by rwa [BlowupSequenceData.toSequenceOfBlowups_length] at hj
  have hj' : j < (s'.append n).toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.append_length, hn]
    omega
  have hc : (s'.append n).toSequenceOfBlowups.center j =
      (s.center (c.idx j)).comap (c.map j (le_length_append_of_length_eq_zero_consolidated265 s' n hn j (le_of_lt hj))) :=
    c.center_comap j hj'
  show s'.toSequenceOfBlowups.center j =
      (s.center (c.idx j)).comap
        (eqToHom (schemeAt_eq_schemeAt_append_consolidated265 s' n j (le_of_lt hj)) ≫ c.map j (le_length_append_of_length_eq_zero_consolidated265 s' n hn j (le_of_lt hj)))
  rw [Scheme.IdealSheafData.comap_comp, ← hc, BlowupSequenceData.toSequenceOfBlowups_center s' j,
    BlowupSequenceData.toSequenceOfBlowups_center (s'.append n) j, BlowupSequenceData.append_center_of_lt_length s' n hjl]
  exact (comap_eqToHom_comap_eqToHom_consolidated265 _ _ _).symm

private theorem center_ne_top_of_append_length_eq_zero_consolidated265 :
    ∀ j : ℕ, j < s'.toSequenceOfBlowups.length → s'.toSequenceOfBlowups.center j ≠ ⊤ := by
  intro j hj
  have hjl : j < s'.length := by rwa [BlowupSequenceData.toSequenceOfBlowups_length] at hj
  have hjc : j < (s'.append n).toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.append_length, hn]
    omega
  have hne := c.center_ne_top j hjc
  rw [BlowupSequenceData.toSequenceOfBlowups_center, BlowupSequenceData.append_center_of_lt_length s' n hjl] at hne
  rw [BlowupSequenceData.toSequenceOfBlowups_center]
  intro htop
  rw [htop] at hne
  exact hne (Scheme.IdealSheafData.comap_top _)

private theorem disjoint_omitted_centers_of_append_length_eq_zero_consolidated265 :
    ∀ i : ℕ, i < s.length → (∀ j : ℕ, j < s'.toSequenceOfBlowups.length → c.idx j ≠ i) →
      ∀ z : ↥(s.schemeAt i), z ∈ (s.center i).support →
        ∀ x' : ↥X', φ.base x' ≠ (s.projectionToBase i).base z := by
  intro i hi hmiss
  refine c.omitted i hi ?_
  intro j hj
  refine hmiss j ?_
  rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.append_length, hn] at hj
  rw [BlowupSequenceData.toSequenceOfBlowups_length]
  omega


end

noncomputable def ofConcatLengthZero {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X')
    (s : SequenceOfBlowups X) (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0)
    (c : SequenceOfBlowupsPullback φ (s'.append n).toSequenceOfBlowups s) :
    SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s where
  idx := c.idx
  map := mapOfAppendLengthEqZero φ s' s n hn c
  idx_length := index_length_of_append_length_eq_zero_consolidated265 φ s' s n hn c
  idx_lt := index_lt_length_of_append_length_eq_zero_consolidated265 φ s' s n hn c
  idx_strictMono := index_lt_index_succ_of_append_length_eq_zero_consolidated265 φ s' s n hn c
  isPullback := isPullback_of_append_length_eq_zero_consolidated265 φ s' s n hn c
  step := blowupMorphism_comp_of_append_length_eq_zero_consolidated265 φ s' s n hn c
  center_comap := center_eq_comap_of_append_length_eq_zero_consolidated265 φ s' s n hn c
  center_ne_top := center_ne_top_of_append_length_eq_zero_consolidated265 φ s' s n hn c
  omitted := disjoint_omitted_centers_of_append_length_eq_zero_consolidated265 φ s' s n hn c

end

section

section
variable {Y T T' : Scheme.{u}} {π : T' ⟶ T} {I : T.IdealSheafData} (hB : Blowup.IsBlowupAlongIdealSheaf π I) (u : Y ⟶ T) (htop : I.comap u = ⊤)
include hB htop

theorem isIso_pullback_snd_of_comap_eq_top :
    IsIso (pullback.snd π u) := by
  have hEC : Blowup.IsLocallyGeneratedByNonZeroDivisor (I.comap u) := by
    rw [htop]
    exact Blowup.isLocallyGeneratedByNonZeroDivisor_top Y
  obtain ⟨k, hk, -⟩ := hB.existsUnique_lift Y u hEC
  have hw : k ≫ π = 𝟙 Y ≫ u := by rw [hk, Category.id_comp]
  have hEC2 : Blowup.IsLocallyGeneratedByNonZeroDivisor (I.comap (pullback.snd π u ≫ u)) := by
    have hc : I.comap (pullback.snd π u ≫ u) = (I.comap u).comap (pullback.snd π u) := by
      simp [Scheme.IdealSheafData.comap_comp]
    rw [hc, htop]
    exact Blowup.isLocallyGeneratedByNonZeroDivisor_comap_top _
  refine ⟨⟨pullback.lift k (𝟙 Y) hw, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      refine hB.hom_ext_of_comp_eq hEC2 ?_ pullback.condition
      rw [Category.assoc, hk]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  · rw [pullback.lift_snd]

theorem exists_lift_of_comap_eq_top :
    ∃ v : Y ⟶ T', IsPullback v (𝟙 Y) π u ∧ v ≫ π = u := by
  have hiso : IsIso (pullback.snd π u) := isIso_pullback_snd_of_comap_eq_top hB u htop
  refine ⟨inv (pullback.snd π u) ≫ pullback.fst π u, ?_, ?_⟩
  · refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso (pullback.snd π u)).symm ?_ ?_
    · rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc, Category.id_comp]
    · simp
    · simp
  · rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]


end

section
variable {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)

theorem exists_lift_succ_of_comap_center_eq_top (i : ℕ) (hi : i < t.length) (u : Y ⟶ t.obj i)
    (hu : IsPullback u (𝟙 Y) (t.projectionToBase i) g) (htop : (t.center i).comap u = ⊤) :
    ∃ v : Y ⟶ t.obj (i + 1), IsPullback v (𝟙 Y) (t.projectionToBase (i + 1)) g ∧ v ≫ t.map i = u := by
  obtain ⟨v, hv, hvc⟩ := exists_lift_of_comap_eq_top (t.isBlowup i hi) u htop
  refine ⟨v, ?_, hvc⟩
  have hpaste := hv.paste_vert hu
  simp only [Category.comp_id] at hpaste
  rw [BlowupSequenceData.projectionToBase_succ]
  exact hpaste

theorem exists_lift_of_forall_comap_eq_top (h : ∀ i : ℕ, i < t.length → ∀ u : Y ⟶ t.obj i, IsPullback u (𝟙 Y) (t.projectionToBase i) g →
      (t.center i).comap u = ⊤) :
    ∀ i : ℕ, i ≤ t.length → ∃ u : Y ⟶ t.obj i, IsPullback u (𝟙 Y) (t.projectionToBase i) g := by
  intro i
  induction i with
  | zero =>
      intro _
      exact ⟨g ≫ t.isoZero.inv, isPullback_comp_isoObjZero_inv_consolidated265 g t⟩
  | succ i ih =>
      intro hi
      have hi' : i < t.length := by omega
      obtain ⟨u, hu⟩ := ih (le_of_lt hi')
      obtain ⟨v, hv, -⟩ :=
        exists_lift_succ_of_comap_center_eq_top g t i hi' u hu (h i hi' u hu)
      exact ⟨v, hv⟩


end

end

section

private theorem exists_mem_support_center_append_consolidated265 {X : Scheme.{u}} (s : BlowupSequenceData X)
    (n : BlowupSequenceData (s.obj s.length)) :
    ∀ (i : ℕ) (z : ↥(n.obj i)), z ∈ (n.center i).support →
      ∃ z' : ↥((s.append n).obj (s.length + i)),
        z' ∈ ((s.append n).center (s.length + i)).support ∧
          ((s.append n).projectionToBase (s.length + i)).base z' =
            (s.projectionToBase s.length).base ((n.projectionToBase i).base z) := by
  intro i
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · intro z hz
    simp only [Nat.add_zero]
    have hh : (s.append n).obj s.length = s.obj s.length :=
      BlowupSequenceData.append_schemeAt_of_le_length s n (le_refl s.length)
    refine ⟨(eqToHom hh.symm).base (n.isoZero.hom.base z), ?_, ?_⟩
    · rw [BlowupSequenceData.append_center_length]
      refine Scheme.IdealSheafData.mem_support_comap.mpr ?_
      rw [eqToHom_base_trans_consolidated265, eqToHom_base_self_consolidated265]
      refine Scheme.IdealSheafData.mem_support_comap.mpr ?_
      rw [inv_base_hom_base_consolidated265]
      exact hz
    · rw [BlowupSequenceData.projectionToBase_append_of_le_length s n (le_refl s.length), base_comp_apply_consolidated265,
        eqToHom_base_trans_consolidated265, eqToHom_base_self_consolidated265, BlowupSequenceData.projectionToBase_zero]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = k + 1 := ⟨i - 1, by omega⟩
    intro z hz
    have hgt : s.length < s.length + (k + 1) := by omega
    have h1 : (s.append n).obj (s.length + (k + 1)) =
        n.obj (s.length + (k + 1) - s.length) := BlowupSequenceData.append_schemeAt_of_length_lt s n hgt
    have hsub : s.length + (k + 1) - s.length = k + 1 := by omega
    have hobj : n.obj (k + 1) = (s.append n).obj (s.length + (k + 1)) := by
      rw [h1, hsub]
    refine ⟨(eqToHom hobj).base z, ?_, ?_⟩
    · rw [BlowupSequenceData.append_center_of_length_lt s n hgt]
      refine Scheme.IdealSheafData.mem_support_comap.mpr ?_
      rw [eqToHom_base_trans_consolidated265]
      exact eqToHom_base_mem_support_center_consolidated265 n hsub.symm _ z hz
    · rw [BlowupSequenceData.projectionToBase_append_of_length_lt s n hgt, base_comp_apply_consolidated265, base_comp_apply_consolidated265,
        eqToHom_base_trans_consolidated265, projectionToBase_base_eqToHom_base_consolidated265 n hsub.symm]

private theorem disjoint_centers_lastMap_of_append_consolidated265 {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X')
    (s : BlowupSequenceData X) (n : BlowupSequenceData (s.obj s.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (hmiss : ∀ i : ℕ, s.length ≤ i → i < s.length + n.length →
      ∀ z : ↥((s.append n).obj i), z ∈ ((s.append n).center i).support →
        ∀ x' : ↥X', φ.base x' ≠ ((s.append n).projectionToBase i).base z) :
    IsDisjointFromCenters_consolidated265 c.lastMap n := by
  intro i hi z hz y hyeq
  obtain ⟨z', hz', hp⟩ := exists_mem_support_center_append_consolidated265 s n i z hz
  have hst : s.toSequenceOfBlowups.projectionToBase s.toSequenceOfBlowups.length = s.projectionToBase s.length :=
    BlowupSequenceData.toSequenceOfBlowups_projectionToBase s s.length
  have hw : c.lastMap ≫ s.toSequenceOfBlowups.projectionToBase s.toSequenceOfBlowups.length
      = s'.toSequenceOfBlowups.projectionToBase s'.toSequenceOfBlowups.length ≫ φ := c.isPullback_lastMap.w
  have h0 := congrArg (fun f : s'.toSequenceOfBlowups.schemeAt s'.toSequenceOfBlowups.length ⟶ X => f.base y) hw
  have hA := base_comp_apply_consolidated265 c.lastMap (s.toSequenceOfBlowups.projectionToBase s.toSequenceOfBlowups.length) y
  have hB := base_comp_apply_consolidated265 (s'.toSequenceOfBlowups.projectionToBase s'.toSequenceOfBlowups.length) φ y
  have h1 : (s.toSequenceOfBlowups.projectionToBase s.toSequenceOfBlowups.length).base (c.lastMap.base y)
      = φ.base ((s'.toSequenceOfBlowups.projectionToBase s'.toSequenceOfBlowups.length).base y) :=
    hA.symm.trans (h0.trans hB)
  have h3 : (s.toSequenceOfBlowups.projectionToBase s.toSequenceOfBlowups.length).base (c.lastMap.base y)
      = (s.projectionToBase s.length).base (c.lastMap.base y) :=
    congrArg (fun f : s.obj s.length ⟶ X => f.base (c.lastMap.base y)) hst
  refine hmiss (s.length + i) (Nat.le_add_right _ _) (by omega) z' hz'
      ((s'.toSequenceOfBlowups.projectionToBase s'.toSequenceOfBlowups.length).base y) ?_
  exact (h1.symm.trans h3).trans
    ((congrArg (fun w : ↥(s.obj s.length) => (s.projectionToBase s.length).base w) hyeq).trans hp.symm)

private theorem exists_lift_schemeAt_length_of_disjoint_centers_consolidated265 {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (hmiss : IsDisjointFromCenters_consolidated265 g t) :
    ∃ u : Y ⟶ t.obj t.length, IsPullback u (𝟙 Y) (t.projectionToBase t.length) g :=
  exists_lift_of_forall_comap_eq_top g t
    (fun i hi u hu => comap_eq_top_of_forall_support_not_mem_range g (t.projectionToBase i) (t.center i) (hmiss i hi) u hu)
    t.length le_rfl

private noncomputable def chosenLiftToLastOfIsDisjointFromCenters {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (hmiss : IsDisjointFromCenters_consolidated265 g t) : Y ⟶ t.obj t.length :=
  (exists_lift_schemeAt_length_of_disjoint_centers_consolidated265 g t hmiss).choose

private theorem isPullback_chosenLiftToLastOfIsDisjointFromCenters_consolidated265 {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (hmiss : IsDisjointFromCenters_consolidated265 g t) :
    IsPullback (chosenLiftToLastOfIsDisjointFromCenters g t hmiss) (𝟙 Y) (t.projectionToBase t.length) g :=
  (exists_lift_schemeAt_length_of_disjoint_centers_consolidated265 g t hmiss).choose_spec

private noncomputable def mapToLastOfLengthEqZero {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (hmiss : IsDisjointFromCenters_consolidated265 g t) (e : BlowupSequenceData Y) (he : e.length = 0)
    (j : ℕ) (hj : j ≤ e.toSequenceOfBlowups.length) : e.toSequenceOfBlowups.schemeAt j ⟶ t.toSequenceOfBlowups.schemeAt t.length :=
  eqToHom (schemeAt_eq_schemeAt_zero_of_length_eq_zero_consolidated265 e he j hj) ≫ e.isoZero.hom ≫ chosenLiftToLastOfIsDisjointFromCenters g t hmiss ≫
    eqToHom (t.toSequenceOfBlowups_schemeAt t.length).symm

section
variable {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters_consolidated265 g t) (e : BlowupSequenceData Y) (he : e.length = 0)

private theorem isPullback_mapToLastOfLengthEqZero_consolidated265 :
    ∀ (j : ℕ) (hj : j ≤ e.toSequenceOfBlowups.length),
      IsPullback (mapToLastOfLengthEqZero g t hmiss e he j hj) (e.toSequenceOfBlowups.projectionToBase j)
        (t.toSequenceOfBlowups.projectionToBase t.length) g := by
  have hlen : e.toSequenceOfBlowups.length = 0 := e.toSequenceOfBlowups_length.trans he
  intro j hj
  have hj0 : j = 0 := by omega
  subst hj0
  have hpb : IsPullback (chosenLiftToLastOfIsDisjointFromCenters g t hmiss) (𝟙 Y) (t.projectionToBase t.length) g :=
    isPullback_chosenLiftToLastOfIsDisjointFromCenters_consolidated265 g t hmiss
  have hiso : IsPullback e.isoZero.hom e.isoZero.hom (𝟙 Y) (𝟙 Y) :=
    IsPullback.of_horiz_isIso ⟨rfl⟩
  have hcomp := hiso.paste_horiz hpb
  simp only [Category.id_comp] at hcomp
  have hmap : mapToLastOfLengthEqZero g t hmiss e he 0 hj =
      e.isoZero.hom ≫ chosenLiftToLastOfIsDisjointFromCenters g t hmiss := by
    show 𝟙 (e.obj 0) ≫ e.isoZero.hom ≫ chosenLiftToLastOfIsDisjointFromCenters g t hmiss ≫ 𝟙 (t.obj t.length) =
      e.isoZero.hom ≫ chosenLiftToLastOfIsDisjointFromCenters g t hmiss
    simp
  have hs : e.toSequenceOfBlowups.projectionToBase 0 = e.isoZero.hom :=
    (e.toSequenceOfBlowups_projectionToBase 0).trans e.projectionToBase_zero
  have hf : t.toSequenceOfBlowups.projectionToBase t.length = t.projectionToBase t.length := t.toSequenceOfBlowups_projectionToBase t.length
  rw [hmap, hs, hf]
  exact hcomp

private theorem blowupMorphism_comp_mapToLastOfLengthEqZero_consolidated265 :
    ∀ (j : ℕ) (hj : j < e.toSequenceOfBlowups.length),
      e.toSequenceOfBlowups.transitionMapSucc j ≫ mapToLastOfLengthEqZero g t hmiss e he j (le_of_lt hj) =
        mapToLastOfLengthEqZero g t hmiss e he (j + 1) hj ≫
          t.toSequenceOfBlowups.transitionMap (le_of_lt (length_lt_length_of_lt_length_of_eq_zero_consolidated265 t e he j hj)) := by
  intro j hj
  have hlen : e.toSequenceOfBlowups.length = 0 := e.toSequenceOfBlowups_length.trans he
  exact absurd hj (by rw [hlen]; exact Nat.not_lt_zero j)

private theorem center_eq_comap_lastCenter_of_disjoint_consolidated265 :
    ∀ (j : ℕ) (hj : j < e.toSequenceOfBlowups.length),
      e.toSequenceOfBlowups.center j =
        (t.toSequenceOfBlowups.center t.length).comap (mapToLastOfLengthEqZero g t hmiss e he j (le_of_lt hj)) := by
  have hlen : e.toSequenceOfBlowups.length = 0 := e.toSequenceOfBlowups_length.trans he
  intro j hj
  exact absurd hj (by omega)


end

private noncomputable def ofIsDisjointFromCenters {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (hmiss : IsDisjointFromCenters_consolidated265 g t) (e : BlowupSequenceData Y) (he : e.length = 0) :
    SequenceOfBlowupsPullback g e.toSequenceOfBlowups t.toSequenceOfBlowups where
  idx := fun _ => t.length
  map := mapToLastOfLengthEqZero g t hmiss e he
  idx_length := length_eq_toSequenceOfBlowups_length_consolidated265 t
  idx_lt := length_lt_toSequenceOfBlowups_length_of_lt_consolidated265 t e he
  idx_strictMono := length_lt_length_of_lt_length_of_eq_zero_consolidated265 t e he
  isPullback := isPullback_mapToLastOfLengthEqZero_consolidated265 g t hmiss e he
  step := blowupMorphism_comp_mapToLastOfLengthEqZero_consolidated265 g t hmiss e he
  center_comap := center_eq_comap_lastCenter_of_disjoint_consolidated265 g t hmiss e he
  center_ne_top := center_ne_top_of_length_eq_zero_consolidated265 e he
  omitted := disjoint_omitted_centers_of_disjoint_centers_consolidated265 g t hmiss e he

theorem nonempty_append_of_disjoint_centers {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X')
    (s : BlowupSequenceData X) (n : BlowupSequenceData (s.obj s.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (hmiss : ∀ i : ℕ, s.length ≤ i → i < s.length + n.length →
      ∀ z : ↥((s.append n).obj i), z ∈ ((s.append n).center i).support →
        ∀ x' : ↥X', φ.base x' ≠ ((s.append n).projectionToBase i).base z) :
    Nonempty (SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups (s.append n).toSequenceOfBlowups) := by
  have hmiss : IsDisjointFromCenters_consolidated265 c.lastMap n := disjoint_centers_lastMap_of_append_consolidated265 φ s' s n c hmiss
  have hE : (emptyBlowupSequenceData (s'.obj s'.length)).length = 0 :=
    emptyBlowupSequenceData_length (s'.obj s'.length)
  have e₀ : SequenceOfBlowupsPullback c.lastMap (emptyBlowupSequenceData (s'.obj s'.length)).toSequenceOfBlowups n.toSequenceOfBlowups :=
    ofIsDisjointFromCenters c.lastMap n hmiss (emptyBlowupSequenceData (s'.obj s'.length)) hE
  exact ⟨ofConcatLengthZero φ s' (s.append n).toSequenceOfBlowups (emptyBlowupSequenceData (s'.obj s'.length)) hE
    (SequenceOfBlowupsPullback.concat s n s' (emptyBlowupSequenceData (s'.obj s'.length)) c e₀)⟩

end

end SequenceOfBlowupsPullback


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothPullbackGraphChart
section

open TopologicalSpace

section

section
variable (k : Type u) [Field k]

private theorem jacobianDetSection_mvPolynomialToSumCoordinateRing_consolidated218 (M n q : ℕ)
    (lift : Fin q → MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)), ⊤))
    (s : Fin q → Fin n) :
    jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s =
      mvPolynomialToSumCoordinateRing k M n
        (Matrix.det (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (lift j))) := by
  have key : ∀ i j : Fin q,
      jacobianMatrixOfSections k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s i j =
        (mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))).symm
          (mvPolynomialToSumCoordinateRing k M n (MvPolynomial.pderiv (s i) (lift j))) := by
    intro i j
    have h0 : polynomialOfSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) j
        = (mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))).symm (mvPolynomialToSumCoordinateRing k M n (lift j)) := rfl
    rw [jacobianMatrixOfSections_apply, h0]
    exact pderiv_mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing k M n (s i) (lift j)
  have hmat : jacobianMatrixOfSections k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s =
      ((((mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))).symm.toRingHom).comp
          (mvPolynomialToSumCoordinateRing k M n)).mapMatrix)
        (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (lift j)) := by
    refine Matrix.ext fun i j => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, RingHom.coe_comp,
      Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    exact key i j
  show mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))
      (jacobianMatrixOfSections k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s).det = _
  rw [hmat, ← RingHom.map_det]
  simp

theorem appTop_specToAffineSpaceExtendCoords_jacobianDetSection (A : Scheme.{u})
    [IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)))
    [IsClosedImmersion e] {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n q : ℕ) (b : Fin n → B')
    (he : e ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) = pA)
    (rel : Fin q → MvPolynomial (Fin n) Γ(A, ⊤))
    (lift : Fin q → MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)), ⊤))
    (hlift : ∀ j, MvPolynomial.map (e.appTop).hom (lift j) = rel j)
    (s : Fin q → Fin n) :
    (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop
        (jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s) =
      (Scheme.ΓSpecIso B').inv
        (Matrix.det (Matrix.of fun i j : Fin q =>
          MvPolynomial.eval₂ σ.hom b ((MvPolynomial.pderiv (s i)) (rel j)))) := by
  have hmap : ∀ i j : Fin q,
      (MvPolynomial.map (CommRingCat.Hom.hom (Scheme.Hom.appTop e)))
          (MvPolynomial.pderiv (s i) (lift j)) = MvPolynomial.pderiv (s i) (rel j) := by
    intro i j
    rw [← MvPolynomial.pderiv_map, hlift j]
  have hM1 : ((MvPolynomial.map (CommRingCat.Hom.hom (Scheme.Hom.appTop e))).mapMatrix
        (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (lift j)))
      = Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (rel j) := by
    refine Matrix.ext fun i j => ?_
    simpa [RingHom.mapMatrix_apply] using hmap i j
  have hM2 : ((MvPolynomial.eval₂Hom (CommRingCat.Hom.hom σ) b).mapMatrix
        (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (rel j)))
      = Matrix.of fun i j : Fin q =>
          MvPolynomial.eval₂ (CommRingCat.Hom.hom σ) b (MvPolynomial.pderiv (s i) (rel j)) := by
    refine Matrix.ext fun i j => ?_
    simp [RingHom.mapMatrix_apply]
  rw [jacobianDetSection_mvPolynomialToSumCoordinateRing_consolidated218 k M n q lift s,
    specToAffineSpaceExtendCoords_appTop_mvPolynomial k A pA M e σ n b he]
  congr 1
  rw [RingHom.map_det, hM1]
  show (MvPolynomial.eval₂Hom (CommRingCat.Hom.hom σ) b)
      (Matrix.det (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (rel j))) = _
  rw [RingHom.map_det, hM2]


end

theorem smoothPullbackHasGraphChart : SmoothPullbackHasGraphChart.{u} := by
  intro k _ _ X Y A pX pY pA _ _ _ _ i _ _ M ρ _ hρ r h _ _ y
  have : IsAffine X := isAffine_of_isAffineHom (f := i)
  obtain ⟨V, hyV, hVaff, B', τ, jV, hτ, hjV, hpb⟩ :=
    PresentedSmoothChart.exists_affineOpen_isPullback_specMap i r h y
  have := hjV
  let _ : Algebra Γ(A, ⊤) B' := (CommRingCat.Hom.hom τ).toAlgebra
  have halg : (algebraMap Γ(A, ⊤) B') = CommRingCat.Hom.hom τ := rfl
  obtain ⟨⟨ι, κ, hκ, hι, P, hPdim⟩⟩ := hτ
  have := hι
  have := hκ
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  have hA : Algebra.IsStandardSmooth Γ(A, ⊤) B' := ⟨⟨ι, κ, hκ, hι, ⟨P⟩⟩⟩
  have hss : RingHom.IsStandardSmooth (CommRingCat.Hom.hom τ) := hA
  have hgsmooth : Smooth (specHomOfGlobalSections A τ) :=
    PresentedSmoothChart.smooth_specMap_comp_isoSpec_inv τ hss
  have := hgsmooth
  obtain ⟨n, ev, hn⟩ : ∃ (n : ℕ) (_ : ι ≃ Fin n), Nat.card ι = n :=
    ⟨_, Finite.equivFin ι, rfl⟩
  obtain ⟨q, er, hq⟩ : ∃ (q : ℕ) (_ : κ ≃ Fin q), Nat.card κ = q :=
    ⟨_, Finite.equivFin κ, rfl⟩
  have hdim' : Nat.card ι - Nat.card κ = r := hPdim
  have hle : Nat.card κ ≤ Nat.card ι := Nat.card_le_card_of_injective P.map P.map_inj
  have hnq : n = q + r := by omega
  obtain ⟨b, hb⟩ : ∃ b : Fin n → B', b = fun t => P.val (ev.symm t) := ⟨_, rfl⟩
  obtain ⟨rel, hrel_def⟩ : ∃ rel : Fin q → MvPolynomial (Fin n) Γ(A, ⊤),
      rel = fun j => MvPolynomial.rename ⇑ev (P.relation (er.symm j)) := ⟨_, rfl⟩
  obtain ⟨s, hs_def⟩ : ∃ s : Fin q → Fin n, s = fun j => ev (P.map (er.symm j)) := ⟨_, rfl⟩
  have hsinj : Function.Injective s := by
    intro a₁ a₂ hab
    simp only [hs_def] at hab
    exact er.symm.injective (P.map_inj (ev.injective hab))
  have hbev : (b ∘ ⇑ev) = P.val := by
    funext x
    simp [hb]
  have hvb : (P.val ∘ ⇑ev.symm) = b := by
    funext t
    simp [hb]
  have heval : ∀ p : MvPolynomial ι Γ(A, ⊤),
      MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b (MvPolynomial.rename ⇑ev p) =
        MvPolynomial.aeval P.val p := by
    intro p
    rw [MvPolynomial.eval₂_rename, hbev, MvPolynomial.aeval_def, halg]
  have hE : ∀ x : MvPolynomial (Fin n) Γ(A, ⊤),
      MvPolynomial.aeval P.val (MvPolynomial.rename ⇑ev.symm x) =
        MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b x := by
    intro x
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_rename, hvb, halg]
  have hkerP : ∀ x : MvPolynomial ι Γ(A, ⊤),
      MvPolynomial.aeval P.val x = 0 ↔ x ∈ Ideal.span (Set.range P.relation) := by
    intro x
    rw [P.span_range_relation_eq_ker, Algebra.Generators.ker_eq_ker_aeval_val]
    simp [RingHom.mem_ker]
  have hrel0 : ∀ j : κ, MvPolynomial.aeval P.val (P.relation j) = 0 := fun j =>
    (hkerP _).mpr (Ideal.subset_span ⟨j, rfl⟩)
  have hsub : Ideal.map (MvPolynomial.rename ⇑ev) (Ideal.span (Set.range P.relation))
      ≤ Ideal.span (Set.range rel) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro z ⟨j, rfl⟩
    simp only [SetLike.mem_coe, Ideal.mem_comap]
    exact Ideal.subset_span ⟨er j, by simp [hrel_def]⟩
  have hker : RingHom.ker (MvPolynomial.eval₂Hom (CommRingCat.Hom.hom τ) b) =
      Ideal.span (Set.range rel) := by
    apply le_antisymm
    · intro x hx
      have hx' : MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b x = 0 := by
        simpa [RingHom.mem_ker] using hx
      have h1 : MvPolynomial.rename ⇑ev.symm x ∈ Ideal.span (Set.range P.relation) :=
        (hkerP _).mp (by rw [hE x]; exact hx')
      have h2 := hsub (Ideal.mem_map_of_mem _ h1)
      rw [MvPolynomial.rename_rename, Equiv.self_comp_symm] at h2
      simpa using h2
    · rw [Ideal.span_le]
      rintro z ⟨j, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, hrel_def]
      rw [heval]
      exact hrel0 _
  have hjacEntry : ∀ i₀ j₀ : Fin q,
      MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b (MvPolynomial.pderiv (s i₀) (rel j₀)) =
        MvPolynomial.aeval P.val (P.jacobiMatrix (er.symm i₀) (er.symm j₀)) := by
    intro i₀ j₀
    simp only [hs_def, hrel_def]
    rw [MvPolynomial.pderiv_rename (f := ⇑ev) ev.injective, heval, P.jacobiMatrix_apply]
  have hj := P.jacobian_eq_jacobiMatrix_det
  have hdet : (Matrix.of fun i₀ j₀ : Fin q =>
        MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b
          (MvPolynomial.pderiv (s i₀) (rel j₀))).det = P.jacobian := by
    have h1 : (Matrix.of fun i₀ j₀ : Fin q =>
          MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b
            (MvPolynomial.pderiv (s i₀) (rel j₀)))
        = (P.jacobiMatrix.map ⇑(MvPolynomial.aeval P.val).toRingHom).submatrix
            ⇑er.symm ⇑er.symm := by
      refine Matrix.ext fun i₀ j₀ => ?_
      simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.map_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      exact hjacEntry i₀ j₀
    rw [h1, Matrix.det_submatrix_equiv_self, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa [Algebra.Generators.algebraMap_apply] using hj.symm
  have hgen : ∀ x : B', ∃ p : MvPolynomial (Fin n) Γ(A, ⊤),
      MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b p = x := by
    intro x
    refine ⟨MvPolynomial.rename ⇑ev (P.σ x), ?_⟩
    rw [heval]
    exact P.aeval_val_σ x
  choose lift hliftmap using fun j : Fin q => exists_mvPolynomial_map_appTop_eq k A M ρ n q rel j
  have hΔ : IsUnit ((specToAffineSpaceExtendCoords k A pA M ρ τ n b).appTop
      (jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s)) := by
    rw [appTop_specToAffineSpaceExtendCoords_jacobianDetSection k A pA M ρ τ n q b hρ rel lift hliftmap s]
    have h2 : IsUnit ((Matrix.of fun i₀ j₀ : Fin q =>
        MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b
          ((MvPolynomial.pderiv (s i₀)) (rel j₀))).det) := by
      rw [hdet]
      exact P.jacobian_isUnit
    exact h2.map ((Scheme.ΓSpecIso B').inv).hom
  have hpA'Sm : Smooth (specHomOfGlobalSections A τ ≫ pA) := by infer_instance
  have hpA'ft : LocallyOfFiniteType (specHomOfGlobalSections A τ ≫ pA) := by infer_instance
  have hpA'qc : QuasiCompact (specHomOfGlobalSections A τ ≫ pA) := by infer_instance
  refine ⟨V, hyV, hVaff, Spec B', specHomOfGlobalSections A τ ≫ pA, inferInstance, hpA'Sm,
    hpA'ft, hpA'qc, specHomOfGlobalSections A τ, hgsmooth, rfl, jV, hjV, hpb, n, q, hnq,
    specToAffineSpaceExtendCoords k A pA M ρ τ n b, ?_, ?_, (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)),
    jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s, ?_, ?_, ?_⟩
  · exact isClosedImmersion_specToAffineSpaceExtendCoords k A pA M ρ τ n b hρ hgen
  · exact specToAffineSpaceExtendCoords_comp_projLeft k A pA M ρ τ n b hρ
  · exact ker_specToAffineSpaceExtendCoords_appTop k A pA M ρ τ n b hρ q rel hker lift hliftmap
  · exact preimage_basicOpen_specToAffineSpaceExtendCoords k A pA M ρ τ n b _ hΔ
  · exact smooth_graphMorphismToAffineSpace_basicOpen k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s hsinj


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceTransitions
section

open CategoryTheory.Limits Opposite


namespace SequenceOfBlowups

variable {X : Scheme.{u}}

section
variable (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X)

theorem pullbackTransitionMap_self_eq_id {i : ℕ} (h : i ≤ i) :
    s.pullbackTransitionMap φ h = 𝟙 (pullback φ (s.projectionToBase i)) := by
  refine pullback.hom_ext ?_ ?_
  · rw [s.pullbackTransitionMap_fst, Category.id_comp]
  · rw [s.pullbackTransitionMap_snd, s.transitionMap_self_eq_id, Category.comp_id, Category.id_comp]

theorem pullbackTransitionMap_trans {i j l : ℕ}
    (hij : i ≤ j) (hjl : j ≤ l) :
    s.pullbackTransitionMap φ hjl ≫ s.pullbackTransitionMap φ hij = s.pullbackTransitionMap φ (hij.trans hjl) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, s.pullbackTransitionMap_fst, s.pullbackTransitionMap_fst, s.pullbackTransitionMap_fst]
  · rw [Category.assoc, s.pullbackTransitionMap_snd, ← Category.assoc, s.pullbackTransitionMap_snd, Category.assoc,
      s.transitionMap_trans, s.pullbackTransitionMap_snd]

private theorem isIso_pullbackTransitionMap_add_consolidated244 (n : ℕ) :
    ∀ (k : ℕ) (h : n ≤ n + k),
      (∀ m, n ≤ m → m < n + k → IsIso (s.pullbackTransitionMap φ (Nat.le_succ m))) →
      IsIso (s.pullbackTransitionMap φ h) := by
  intro k
  induction k with
  | zero =>
      intro h _
      have hid : s.pullbackTransitionMap φ h = 𝟙 (pullback φ (s.projectionToBase n)) := s.pullbackTransitionMap_self_eq_id φ h
      rw [hid]
      infer_instance
  | succ k ih =>
      intro h hstep
      have h1 : IsIso (s.pullbackTransitionMap φ (Nat.le_add_right n k)) :=
        ih (Nat.le_add_right n k) (fun m hm hmk => hstep m hm (by omega))
      have h2 : IsIso (s.pullbackTransitionMap φ (Nat.le_succ (n + k))) :=
        hstep (n + k) (Nat.le_add_right n k) (by omega)
      have key : IsIso (s.pullbackTransitionMap φ (Nat.le_succ (n + k)) ≫
          s.pullbackTransitionMap φ (Nat.le_add_right n k)) := inferInstance
      rw [s.pullbackTransitionMap_trans φ (Nat.le_add_right n k) (Nat.le_succ (n + k))] at key
      exact key

theorem isIso_pullbackTransitionMap {n n' : ℕ}
    (h : n ≤ n') (hstep : ∀ m, n ≤ m → m < n' → IsIso (s.pullbackTransitionMap φ (Nat.le_succ m))) :
    IsIso (s.pullbackTransitionMap φ h) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact isIso_pullbackTransitionMap_add_consolidated244 s φ n k h hstep


end

end SequenceOfBlowups

private theorem idealSheafData_eq_top_of_support_empty_consolidated244 {X : Scheme.{u}} (I : X.IdealSheafData)
    (h : ∀ x : X, x ∉ I.support) : I = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  ext x
  simp [h x]

private theorem isPullback_of_iso_pullback_consolidated244 {P Z A A' : Scheme.{u}} (f : A' ⟶ A) (h : Z ⟶ A)
    (ε : P ≅ pullback f h) {a : P ⟶ Z} {b : P ⟶ A'}
    (ha : ε.hom ≫ pullback.snd f h = a) (hb : ε.hom ≫ pullback.fst f h = b) :
    IsPullback a b h f := by
  refine (IsPullback.of_iso_pullback ⟨?_⟩ ε hb ha).flip
  rw [← ha, ← hb, Category.assoc, Category.assoc, pullback.condition]

theorem IsPullbackBlowupSequence.exists_reindexing_of_flat {A A' : Scheme.{u}} (f : A' ⟶ A)
    [Flat f] {t' : SequenceOfBlowups A'} {t : SequenceOfBlowups A}
    (hpb : IsPullbackBlowupSequence f t' t) :
    ∃ (σ : ℕ → ℕ) (g : ∀ j, j ≤ t'.length → (t'.schemeAt j ⟶ t.schemeAt (σ j))),
      (∀ j, j < t'.length → σ j < t.length) ∧
      (∀ j, j < t'.length → σ j < σ (j + 1)) ∧
      σ t'.length = t.length ∧
      (∀ (j : ℕ) (hj : j ≤ t'.length),
        IsPullback (g j hj) (t'.projectionToBase j) (t.projectionToBase (σ j)) f) ∧
      (∀ (j : ℕ) (hj : j ≤ t'.length) (i : ℕ) (hi : i ≤ σ j),
        (∀ m, i ≤ m → m < σ j → ∀ j', j' < t'.length → σ j' ≠ m) →
        IsPullback (g j hj ≫ t.transitionMap hi) (t'.projectionToBase j) (t.projectionToBase i) f) ∧
      (∀ (j : ℕ) (hj : j < t'.length) (hσ : σ j + 1 ≤ σ (j + 1)),
        IsPullback (g (j + 1) (Nat.succ_le_of_lt hj) ≫ t.transitionMap hσ) (t'.transitionMapSucc j)
          (t.transitionMapSucc (σ j)) (g j (Nat.le_of_lt hj))) ∧
      (∀ (j : ℕ) (hj : j < t'.length),
        t'.center j = (t.center (σ j)).comap (g j (Nat.le_of_lt hj))) ∧
      (∀ i, i < t.length → (∀ j, j < t'.length → σ j ≠ i) →
        ∀ (P : Scheme.{u}) (q : P ⟶ t.schemeAt i) (p : P ⟶ A'),
          IsPullback q p (t.projectionToBase i) f → (t.center i).comap q = ⊤) := by
  obtain ⟨r, e, hrlt, hrmono, hrlen, hsupp, hfst, hblow, hcen⟩ := hpb
  have hmono : ∀ i j : ℕ, j ≤ t'.length → i ≤ j → r i ≤ r j := by
    intro i j hj hij
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · exact (hrmono i j hj hlt).le
  have hrle : ∀ j : ℕ, j ≤ t'.length → r j ≤ t.length := by
    intro j hj
    rcases eq_or_lt_of_le hj with rfl | hlt
    · exact le_of_eq hrlen
    · exact (hrlt j hlt).le
  have htop : ∀ m : ℕ, m < t.length → (∀ j', j' < t'.length → r j' ≠ m) →
      (t.center m).comap (pullback.snd f (t.projectionToBase m)) = ⊤ := by
    intro m hm hskip
    refine idealSheafData_eq_top_of_support_empty_consolidated244 _ ?_
    intro x hx
    obtain ⟨j', hj', hrj'⟩ := (hsupp m hm).mp ⟨x, hx⟩
    exact hskip j' hj' hrj'
  have hiso : ∀ m : ℕ, m < t.length → (∀ j', j' < t'.length → r j' ≠ m) →
      IsIso (t.pullbackTransitionMap f (Nat.le_succ m)) := by
    intro m hm hskip
    have hb := (t.baseChange f).isBlowupAlongIdealSheaf_blowupMorphism m hm
    rw [SequenceOfBlowups.baseChange_blowupMorphism, SequenceOfBlowups.baseChange_center,
      htop m hm hskip] at hb
    exact hb.isIso_of_top
  have hD : ∀ (j : ℕ) (hj : j ≤ t'.length),
      IsPullback ((e j hj).hom ≫ pullback.snd f (t.projectionToBase (r j))) (t'.projectionToBase j)
        (t.projectionToBase (r j)) f := fun j hj =>
    isPullback_of_iso_pullback_consolidated244 f (t.projectionToBase (r j)) (e j hj) rfl (hfst j hj)
  have hE : ∀ (j : ℕ) (hj : j ≤ t'.length) (i : ℕ) (hi : i ≤ r j),
      (∀ m, i ≤ m → m < r j → ∀ j', j' < t'.length → r j' ≠ m) →
      IsPullback (((e j hj).hom ≫ pullback.snd f (t.projectionToBase (r j))) ≫ t.transitionMap hi)
        (t'.projectionToBase j) (t.projectionToBase i) f := by
    intro j hj i hi hskip
    have hiso' : IsIso (t.pullbackTransitionMap f hi) := by
      refine SequenceOfBlowups.isIso_pullbackTransitionMap t f hi ?_
      intro m him hmrj
      exact hiso m (lt_of_lt_of_le hmrj (hrle j hj)) (fun j' hj' => hskip m him hmrj j' hj')
    refine isPullback_of_iso_pullback_consolidated244 f (t.projectionToBase i) ((e j hj) ≪≫ asIso (t.pullbackTransitionMap f hi)) ?_ ?_
    · show ((e j hj).hom ≫ t.pullbackTransitionMap f hi) ≫ pullback.snd f (t.projectionToBase i) = _
      rw [Category.assoc, t.pullbackTransitionMap_snd, ← Category.assoc]
    · show ((e j hj).hom ≫ t.pullbackTransitionMap f hi) ≫ pullback.fst f (t.projectionToBase i) = _
      rw [Category.assoc, t.pullbackTransitionMap_fst]
      exact hfst j hj
  have hF : ∀ (j : ℕ) (hj : j < t'.length) (hsig : r j + 1 ≤ r (j + 1)),
      IsPullback
        (((e (j + 1) (Nat.succ_le_of_lt hj)).hom ≫ pullback.snd f (t.projectionToBase (r (j + 1))))
          ≫ t.transitionMap hsig)
        (t'.transitionMapSucc j) (t.transitionMapSucc (r j))
        ((e j (Nat.le_of_lt hj)).hom ≫ pullback.snd f (t.projectionToBase (r j))) := by
    intro j hj hsig
    have hskip : ∀ m, r j + 1 ≤ m → m < r (j + 1) → ∀ j', j' < t'.length → r j' ≠ m := by
      intro m hm1 hm2 j' hj' hrj'
      rcases Nat.lt_or_ge j j' with hlt | hle
      · have h1 := hmono (j + 1) j' (le_of_lt hj') (Nat.succ_le_of_lt hlt)
        omega
      · have h1 := hmono j' j (le_of_lt hj) hle
        omega
    have s0 := hE (j + 1) (Nat.succ_le_of_lt hj) (r j + 1) hsig hskip
    rw [t'.projectionToBase_succ j, t.projectionToBase_succ (r j)] at s0
    have hdown : t.transitionMap hsig ≫ t.transitionMapSucc (r j) = t.transitionMap ((Nat.le_succ (r j)).trans hsig) :=
      t.transitionMap_trans (Nat.le_succ (r j)) hsig
    have hp : (((e (j + 1) (Nat.succ_le_of_lt hj)).hom ≫
          pullback.snd f (t.projectionToBase (r (j + 1)))) ≫ t.transitionMap hsig) ≫ t.transitionMapSucc (r j)
        = t'.transitionMapSucc j ≫ ((e j (Nat.le_of_lt hj)).hom ≫
          pullback.snd f (t.projectionToBase (r j))) := by
      simp only [Category.assoc]
      rw [hdown, ← Category.assoc (t'.transitionMapSucc j),
        hblow j hj ((Nat.le_succ (r j)).trans hsig), Category.assoc, t.pullbackTransitionMap_snd]
    exact IsPullback.of_bot s0 hp (hD j (Nat.le_of_lt hj))
  have hH : ∀ i, i < t.length → (∀ j, j < t'.length → r j ≠ i) →
      ∀ (P : Scheme.{u}) (q : P ⟶ t.schemeAt i) (p : P ⟶ A'),
        IsPullback q p (t.projectionToBase i) f → (t.center i).comap q = ⊤ := by
    intro i hi hskip P q p hsq
    have hw : p ≫ f = q ≫ t.projectionToBase i := hsq.w.symm
    let u : P ⟶ pullback f (t.projectionToBase i) := pullback.lift p q hw
    have hu2 : u ≫ pullback.snd f (t.projectionToBase i) = q := pullback.lift_snd _ _ _
    have hcomp : (t.center i).comap q
        = ((t.center i).comap (pullback.snd f (t.projectionToBase i))).comap u := by
      rw [← hu2]
      simp [Scheme.IdealSheafData.comap_comp]
    rw [hcomp, htop i hi hskip]
    exact Scheme.IdealSheafData.comap_top u
  exact ⟨r, fun j hj => (e j hj).hom ≫ pullback.snd f (t.projectionToBase (r j)),
    hrlt, fun j hj => hrmono j (j + 1) hj (Nat.lt_succ_self j), hrlen, hD, hE, hF, hcen, hH⟩

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackCriterion
section

open CategoryTheory.Limits

section

private theorem apply_eq_self_of_strictMono_of_surjective_consolidated243 (L L' : ℕ) (r : ℕ → ℕ)
    (h1 : ∀ i, i < L' → r i < L)
    (h2 : ∀ i j, j ≤ L' → i < j → r i < r j)
    (h3 : r L' = L)
    (hsurj : ∀ i, i < L → ∃ j, j < L' ∧ r j = i) :
    ∀ i, i ≤ L' → r i = i := by
  have hA : ∀ i, i ≤ L' → i ≤ r i := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have hstep := h2 n (n + 1) hn (Nat.lt_succ_self n)
      have hprev := ih (Nat.le_of_succ_le hn)
      omega
  have key : ∀ i, (∀ j, j < i → j ≤ L' → r j ≤ j) → i ≤ L' → r i ≤ i := by
    intro i ih hi
    by_contra hcon
    have hlt : i < r i := by omega
    have hle : r i ≤ L := by
      rcases Nat.lt_or_ge i L' with hc | hc
      · exact le_of_lt (h1 i hc)
      · have hEq : i = L' := le_antisymm hi hc
        subst hEq
        exact le_of_eq h3
    obtain ⟨j, hjL, hrj⟩ := hsurj i (by omega)
    have hjle : j ≤ r j := hA j (le_of_lt hjL)
    rcases Nat.lt_or_ge j i with hji | hji
    · have hij := ih j hji (le_of_lt hjL)
      omega
    · have hEq : j = i := by omega
      subst hEq
      omega
  have hB' : ∀ n i, i ≤ n → i ≤ L' → r i ≤ i := by
    intro n
    induction n with
    | zero =>
      intro i hi hiL
      exact key i (fun j hj _ => by omega) hiL
    | succ n ih =>
      intro i hi hiL
      exact key i (fun j _ hjL => ih j (by omega) hjL) hiL
  intro i hi
  exact le_antisymm (hB' i i le_rfl hi) (hA i hi)

private theorem isPullback_pullbackTransitionMap_comp_transitionMap_consolidated243 {X X' : Scheme.{u}} (s : SequenceOfBlowups X)
    (φ : X' ⟶ X) (i j j' : ℕ) (hj : j = i) (hj' : j' = i + 1) (hjj' : j ≤ j')
    (hij : i ≤ j) (hij' : i + 1 ≤ j') :
    IsPullback (pullback.snd φ (s.projectionToBase j') ≫ s.transitionMap hij')
      (s.pullbackTransitionMap φ hjj') (s.transitionMapSucc i)
      (pullback.snd φ (s.projectionToBase j) ≫ s.transitionMap hij) := by
  subst hj
  subst hj'
  simp only [SequenceOfBlowups.transitionMap_self_eq_id, Category.comp_id]
  exact s.isPullback_pullbackTransitionMap φ _

private theorem center_comap_eq_comap_comp_transitionMap_of_eq_consolidated243 {X W V : Scheme.{u}} (s : SequenceOfBlowups X) {i j : ℕ}
    (hij : i ≤ j) (hji : j = i) (f : W ⟶ V) (g : V ⟶ s.schemeAt j) :
    (s.center j).comap (f ≫ g) = (s.center i).comap (f ≫ g ≫ s.transitionMap hij) := by
  subst hji
  rw [SequenceOfBlowups.transitionMap_self_eq_id, Category.comp_id]

private theorem support_nonempty_of_ne_top_consolidated243 {Y : Scheme.{u}} (I : Y.IdealSheafData) (h : I ≠ ⊤) :
    ((I.support : Set ↥Y)).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro he
  apply h
  have hbot : I.support = ⊥ := SetLike.ext' (by rw [he]; rfl)
  exact (Scheme.IdealSheafData.support_eq_bot_iff I).mp hbot

section
variable {X X' : Scheme.{u}}

theorem support_comap_center_nonempty_of_mem_range (φ : X' ⟶ X) (s : SequenceOfBlowups X)
    (hne : ∀ i : ℕ, i < s.length → (((s.center i).support : Set ↥(s.schemeAt i))).Nonempty)
    (hran : ∀ i : ℕ, i < s.length → ∀ x ∈ ((s.center i).support : Set ↥(s.schemeAt i)),
      (s.projectionToBase i).base x ∈ Set.range (⇑φ.base)) :
    ∀ i : ℕ, i < s.length →
      ((((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support :
        Set ↥(pullback φ (s.projectionToBase i)))).Nonempty := by
  intro i hi
  obtain ⟨x, hx⟩ := hne i hi
  obtain ⟨y, hy⟩ := hran i hi x hx
  obtain ⟨z, hz1, hz2⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := φ) (g := s.projectionToBase i) y x hy
  refine ⟨z, ?_⟩
  have hmem : (pullback.snd φ (s.projectionToBase i)) z ∈ ((s.center i).support : Set ↥(s.schemeAt i)) := by
    rw [hz2]; exact hx
  rw [Scheme.IdealSheafData.support_comap]
  exact hmem

theorem IsPullbackBlowupSequence.isStrictPullback_of_support_comap_center_nonempty {φ : X' ⟶ X} {s' : SequenceOfBlowups X'}
    {s : SequenceOfBlowups X} (h : IsPullbackBlowupSequence φ s' s)
    (hhit : ∀ i : ℕ, i < s.length →
      ((((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support :
        Set ↥(pullback φ (s.projectionToBase i)))).Nonempty) :
    IsStrictPullbackBlowupSeq φ s' s := by
  obtain ⟨r, e, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hsurj : ∀ i, i < s.length → ∃ j, j < s'.length ∧ r j = i := by
    intro i hi
    obtain ⟨x, hx⟩ := hhit i hi
    exact (h4 i hi).mp ⟨x, hx⟩
  have hid : ∀ i, i ≤ s'.length → r i = i :=
    apply_eq_self_of_strictMono_of_surjective_consolidated243 s.length s'.length r h1 h2 h3 hsurj
  have hlen : s'.length = s.length := by
    have hfin := hid s'.length le_rfl
    omega
  refine ⟨hlen, fun i hi => (e i hi).hom ≫ pullback.snd φ (s.projectionToBase (r i)) ≫
      s.transitionMap (le_of_eq (hid i hi).symm), ?_, ?_, ?_⟩
  · have h0 := h5 0 (Nat.zero_le s'.length)
    simp only [Category.assoc]
    rw [← s.projectionToBase_zero, s.transitionMap_comp_projectionToBase, ← pullback.condition,
      ← Category.assoc, h0, s'.projectionToBase_zero]
  · intro i hi
    have hile : i ≤ s'.length := le_of_lt hi
    have hi1 : i + 1 ≤ s'.length := hi
    have hrle : r i ≤ r (i + 1) := le_of_lt (h2 i (i + 1) hi1 (Nat.lt_succ_self i))
    have sq1 : IsPullback (e (i + 1) hi).hom (s'.transitionMapSucc i) (s.pullbackTransitionMap φ hrle)
        (e i hile).hom := by
      refine IsPullback.of_horiz_isIso ⟨?_⟩
      exact (h6 i hi hrle).symm
    have sq2 : IsPullback
        (pullback.snd φ (s.projectionToBase (r (i + 1))) ≫ s.transitionMap (le_of_eq (hid (i + 1) hi1).symm))
        (s.pullbackTransitionMap φ hrle) (s.transitionMapSucc i)
        (pullback.snd φ (s.projectionToBase (r i)) ≫ s.transitionMap (le_of_eq (hid i hile).symm)) :=
      isPullback_pullbackTransitionMap_comp_transitionMap_consolidated243 s φ i (r i) (r (i + 1)) (hid i hile) (hid (i + 1) hi1) hrle
        (le_of_eq (hid i hile).symm) (le_of_eq (hid (i + 1) hi1).symm)
    exact sq1.paste_horiz sq2
  · intro i hi
    have hile : i ≤ s'.length := le_of_lt hi
    rw [h7 i hi]
    exact center_comap_eq_comap_comp_transitionMap_of_eq_consolidated243 s (le_of_eq (hid i hile).symm) (hid i hile) (e i hile).hom
      (pullback.snd φ (s.projectionToBase (r i)))

theorem IsPullbackBlowupSequence.isStrictPullback_of_surjective {φ : X' ⟶ X}
    [AlgebraicGeometry.Surjective φ] {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsPullbackBlowupSequence φ s' s) (hc : ∀ i : ℕ, i < s.length → s.center i ≠ ⊤) :
    IsStrictPullbackBlowupSeq φ s' s := by
  refine h.isStrictPullback_of_support_comap_center_nonempty ?_
  refine support_comap_center_nonempty_of_mem_range φ s
    (fun i hi => support_nonempty_of_ne_top_consolidated243 (s.center i) (hc i hi)) ?_
  intro i _ x _
  exact φ.surjective _


end

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
section


section

def IsStrongResolution (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (s : SequenceOfBlowups X) : Prop :=
  Smooth (s.lastStructMap ≫ f) ∧
  IsProper s.lastStructMap ∧
  CategoryTheory.IsIso
    (AlgebraicGeometry.morphismRestrict s.lastStructMap f.smoothLocus) ∧
  Dense (s.lastStructMap.base ⁻¹' (f.smoothLocus : Set X)) ∧
  s.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds X) : Set X) ∧
  IsStrictNormalCrossingsDivisor (reducedInverseImage s.lastStructMap (smoothLocusComplement f))

theorem isStrongResolutionRule_iff (R : ResolutionRule.{u}) :
    IsStrongResolutionRule R ↔
      ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
        (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
        [QuasiCompact f] [IsReduced X],
        IsStrongResolution k X f (R k X f) :=
  Iff.rfl


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionData
section

open CategoryTheory.Limits

section

section

variable {X : Scheme.{u}}

def SequenceOfBlowups.schemeAtIsoOfEq (s : SequenceOfBlowups X) {i j : ℕ} (h : i = j) : s.schemeAt i ≅ s.schemeAt j :=
  eqToIso (congrArg s.schemeAt h)

theorem SequenceOfBlowups.schemeAtIsoOfEq_hom_projectionToBase (s : SequenceOfBlowups X) {i j : ℕ} (h : i = j) :
    (s.schemeAtIsoOfEq h).hom ≫ s.projectionToBase j = s.projectionToBase i := by
  subst h
  simp [SequenceOfBlowups.schemeAtIsoOfEq]

end

structure BlowupSequencePullbackComparison {S T : Scheme.{u}} (φ : T ⟶ S) (s' : SequenceOfBlowups T)
    (s : SequenceOfBlowups S) where
  reindex : ℕ → ℕ
  iso : ∀ i : ℕ, i ≤ s'.length →
    (s'.schemeAt i ≅ (pullback φ (s.projectionToBase (reindex i)) : Scheme.{u}))
  reindex_length : reindex s'.length = s.length
  retention : ∀ i : ℕ, i < s.length →
    ((∃ j : ℕ, ∃ _ : j < s'.length, reindex j = i) ↔
      ∃ x, x ∈ ((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support)
  iso_hom_fst : ∀ (i : ℕ) (h : i ≤ s'.length),
    (iso i h).hom ≫ pullback.fst φ (s.projectionToBase (reindex i)) = s'.projectionToBase i
  center_eq : ∀ (i : ℕ) (h : i < s'.length),
    s'.center i =
      (s.center (reindex i)).comap
        ((iso i h.le).hom ≫ pullback.snd φ (s.projectionToBase (reindex i)))

theorem nonempty_pullbackComparison_of_isPullback {S T : Scheme.{u}} (φ : T ⟶ S) (s' : SequenceOfBlowups T)
    (s : SequenceOfBlowups S) (h : IsPullbackBlowupSequence φ s' s) : Nonempty (BlowupSequencePullbackComparison φ s' s) := by
  unfold IsPullbackBlowupSequence at h
  obtain ⟨r, e, hlt, hmono, hlen, hret, hfst, hblow, hcen⟩ := h
  have hret' : ∀ i : ℕ, i < s.length →
      ((∃ j : ℕ, ∃ _ : j < s'.length, r j = i) ↔
        ∃ x, x ∈ ((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support) := by
    intro i hi
    refine ⟨fun hj => (hret i hi).2 ?_, fun hx => ?_⟩
    · obtain ⟨j, hj1, hj2⟩ := hj
      exact ⟨j, hj1, hj2⟩
    · obtain ⟨j, hj1, hj2⟩ := (hret i hi).1 hx
      exact ⟨j, hj1, hj2⟩
  exact ⟨⟨r, e, hlen, hret', hfst, hcen⟩⟩

structure LocalResolutionData (k : Type u) [instFieldk : Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (s : SequenceOfBlowups X) where
  cover : Scheme.OpenCover.{u, u} X
  seq : ∀ i : cover.I₀, SequenceOfBlowups (cover.X i)
  isPullback : ∀ i : cover.I₀, IsPullbackBlowupSequence (cover.f i) (seq i) s
  finiteType : ∀ i : cover.I₀, LocallyOfFiniteType (cover.f i ≫ f)
  isResolution : ∀ i : cover.I₀,
    @IsStrongResolution k instFieldk (cover.X i) (cover.f i ≫ f) (finiteType i) (seq i)

attribute [instance] LocalResolutionData.finiteType

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

def comparison (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    BlowupSequencePullbackComparison (d.cover.f i) (d.seq i) s :=
  (nonempty_pullbackComparison_of_isPullback (d.cover.f i) (d.seq i) s (d.isPullback i)).some

def reindex (d : LocalResolutionData k f s) (i : d.cover.I₀) : ℕ → ℕ := (d.comparison i).reindex

def schemeAtIsoPullback (d : LocalResolutionData k f s) (i : d.cover.I₀) (j : ℕ) (hj : j ≤ (d.seq i).length) :
    ((d.seq i).schemeAt j ≅ (pullback (d.cover.f i) (s.projectionToBase (d.reindex i j)) : Scheme.{u})) :=
  (d.comparison i).iso j hj

section
variable (d : LocalResolutionData k f s) (i : d.cover.I₀)

theorem reindex_length :
    d.reindex i (d.seq i).length = s.length :=
  (d.comparison i).reindex_length

theorem schemeAtIsoPullback_hom_fst (j : ℕ)
    (hj : j ≤ (d.seq i).length) :
    (d.schemeAtIsoPullback i j hj).hom ≫ pullback.fst (d.cover.f i) (s.projectionToBase (d.reindex i j))
      = (d.seq i).projectionToBase j :=
  (d.comparison i).iso_hom_fst j hj

theorem localSequence_center_eq_comap (j : ℕ)
    (hj : j < (d.seq i).length) :
    (d.seq i).center j =
      (s.center (d.reindex i j)).comap
        ((d.schemeAtIsoPullback i j hj.le).hom ≫
          pullback.snd (d.cover.f i) (s.projectionToBase (d.reindex i j))) :=
  (d.comparison i).center_eq j hj

theorem exists_reindex_eq_iff_exists_mem_support (j : ℕ) (hj : j < s.length) :
    ((∃ l : ℕ, ∃ _ : l < (d.seq i).length, d.reindex i l = j) ↔
      ∃ x, x ∈ ((s.center j).comap (pullback.snd (d.cover.f i) (s.projectionToBase j))).support) :=
  (d.comparison i).retention j hj

theorem pullback_projectionToBase_eq_pullback_lastStructMap :
    (pullback (d.cover.f i) (s.projectionToBase (d.reindex i (d.seq i).length)) : Scheme.{u})
      = (pullback (d.cover.f i) s.lastStructMap : Scheme.{u}) := by
  have h1 : (pullback (d.cover.f i) (s.projectionToBase (d.reindex i (d.seq i).length)) : Scheme.{u})
      = (pullback (d.cover.f i) (s.projectionToBase s.length) : Scheme.{u}) :=
    congrArg (fun n : ℕ => (pullback (d.cover.f i) (s.projectionToBase n) : Scheme.{u}))
      (d.reindex_length i)
  have h2 : (pullback (d.cover.f i) (s.projectionToBase s.length) : Scheme.{u})
      = (pullback (d.cover.f i) s.lastStructMap : Scheme.{u}) :=
    congrArg (fun g : s.lastObj ⟶ X => (pullback (d.cover.f i) g : Scheme.{u}))
      s.lastStructMap_eq_projectionToBase.symm
  exact h1.trans h2


end

def lastObjIsoPullback (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    ((d.seq i).lastObj ≅ (pullback (d.cover.f i) s.lastStructMap : Scheme.{u})) :=
  (d.schemeAtIsoPullback i (d.seq i).length le_rfl).trans (eqToIso (d.pullback_projectionToBase_eq_pullback_lastStructMap i))

private theorem eqToHom_comp_pullback_fst_consolidated91 {X₀ X₁ Y₀ Y₁ : Scheme.{u}} (φ : X₁ ⟶ X₀)
    {g : Y₀ ⟶ X₀} {g' : Y₁ ⟶ X₀} (hY : Y₀ = Y₁) (hg : eqToHom hY ≫ g' = g)
    (e : (pullback φ g : Scheme.{u}) = (pullback φ g' : Scheme.{u})) :
    eqToHom e ≫ pullback.fst φ g' = pullback.fst φ g := by
  subst hY
  simp only [eqToHom_refl, Category.id_comp] at hg
  subst hg
  simp

private theorem base_comp_apply_consolidated91 {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (t : ↥A) :
    (a ≫ b).base t = b.base (a.base t) := by
  simp

theorem lastObjIsoPullback_hom_fst (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    (d.lastObjIsoPullback i).hom ≫ pullback.fst (d.cover.f i) s.lastStructMap = (d.seq i).lastStructMap := by
  have hg : eqToHom (congrArg s.schemeAt (d.reindex_length i)) ≫ s.lastStructMap
      = s.projectionToBase (d.reindex i (d.seq i).length) := by
    rw [s.lastStructMap_eq_projectionToBase]
    exact s.schemeAtIsoOfEq_hom_projectionToBase (d.reindex_length i)
  have key := eqToHom_comp_pullback_fst_consolidated91 (d.cover.f i)
    (congrArg s.schemeAt (d.reindex_length i)) hg (d.pullback_projectionToBase_eq_pullback_lastStructMap i)
  have e1 : (d.lastObjIsoPullback i).hom
      = (d.schemeAtIsoPullback i (d.seq i).length le_rfl).hom ≫ eqToHom (d.pullback_projectionToBase_eq_pullback_lastStructMap i) := rfl
  rw [e1, Category.assoc, key, d.schemeAtIsoPullback_hom_fst i (d.seq i).length le_rfl,
    (d.seq i).lastStructMap_eq_projectionToBase]

def chartToLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀) : (d.seq i).lastObj ⟶ s.lastObj :=
  (d.lastObjIsoPullback i).hom ≫ pullback.snd (d.cover.f i) s.lastStructMap

section
variable (d : LocalResolutionData k f s) (i : d.cover.I₀)

theorem chartToLastObj_eq :
    d.chartToLastObj i = (d.lastObjIsoPullback i).hom ≫ pullback.snd (d.cover.f i) s.lastStructMap :=
  rfl

theorem isOpenImmersion_chartToLastObj :
    IsOpenImmersion (d.chartToLastObj i) := by
  have : IsOpenImmersion (d.cover.f i) := d.cover.map_prop i
  rw [d.chartToLastObj_eq i]
  infer_instance


end

instance instIsOpenImmersionChartEmbedding (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    IsOpenImmersion (d.chartToLastObj i) :=
  d.isOpenImmersion_chartToLastObj i

section
variable (d : LocalResolutionData k f s)

theorem chartToLastObj_comp_lastStructMap (i : d.cover.I₀) :
    d.chartToLastObj i ≫ s.lastStructMap = (d.seq i).lastStructMap ≫ d.cover.f i := by
  rw [d.chartToLastObj_eq i, Category.assoc, ← pullback.condition, ← Category.assoc,
    d.lastObjIsoPullback_hom_fst i]

theorem exists_chartToLastObj_eq (x : ↥(s.lastObj)) :
    ∃ (i : d.cover.I₀) (y : ↥((d.seq i).lastObj)), (d.chartToLastObj i).base y = x := by
  obtain ⟨w, hw⟩ := d.cover.covers (s.lastStructMap.base x)
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback w x hw
  refine ⟨d.cover.idx (s.lastStructMap.base x), (d.lastObjIsoPullback _).inv.base p, ?_⟩
  have h2 : (d.lastObjIsoPullback (d.cover.idx (s.lastStructMap.base x))).inv ≫
      d.chartToLastObj (d.cover.idx (s.lastStructMap.base x))
      = pullback.snd (d.cover.f (d.cover.idx (s.lastStructMap.base x))) s.lastStructMap := by
    rw [d.chartToLastObj_eq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have h3 := congrArg
    (fun m : (pullback (d.cover.f (d.cover.idx (s.lastStructMap.base x))) s.lastStructMap : Scheme.{u}) ⟶ s.lastObj
      => m.base p) h2
  simp only [base_comp_apply_consolidated91] at h3
  exact h3.trans hp2

private theorem exists_chartToLastObj_apply_eq_consolidated91 :
    ∀ x : ↥(s.lastObj), ∃ (i : d.cover.I₀) (y : ↥((d.seq i).lastObj)), (d.chartToLastObj i) y = x :=
  fun x => d.exists_chartToLastObj_eq x


end

def lastObjCover (d : LocalResolutionData k f s) : Scheme.OpenCover.{u, u} s.lastObj :=
  Scheme.Cover.mkOfCovers d.cover.I₀ (fun i => (d.seq i).lastObj)
    (fun i => d.chartToLastObj i) d.exists_chartToLastObj_apply_eq_consolidated91
    (fun i => d.isOpenImmersion_chartToLastObj i)

section
variable (d : LocalResolutionData k f s) (i : d.cover.I₀) [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (d.cover.f i ≫ f)]

theorem preimage_smoothLocus_cover_map :
    (d.cover.f i) ⁻¹ᵁ f.smoothLocus = (d.cover.f i ≫ f).smoothLocus := by
  have : IsOpenImmersion (d.cover.f i) := d.cover.map_prop i
  exact Scheme.Hom.preimage_smoothLocus_eq _ _

theorem preimage_smoothLocusComplement_cover_map :
    (d.cover.f i).base ⁻¹' ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X)
      = ((smoothLocusComplement (d.cover.f i ≫ f) :
          TopologicalSpace.Closeds ↥(d.cover.X i)) : Set ↥(d.cover.X i)) := by
  have h : ((d.cover.f i).base ⁻¹' (f.smoothLocus : Set ↥X))
      = ((d.cover.f i ≫ f).smoothLocus : Set ↥(d.cover.X i)) :=
    congrArg (fun U : TopologicalSpace.Opens ↥(d.cover.X i) => (U : Set ↥(d.cover.X i)))
      (d.preimage_smoothLocus_cover_map i)
  show (d.cover.f i).base ⁻¹' ((f.smoothLocus : Set ↥X))ᶜ
      = ((d.cover.f i ≫ f).smoothLocus : Set ↥(d.cover.X i))ᶜ
  rw [Set.preimage_compl, h]


end

end LocalResolutionData


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
section


section

section
variable {A B : CommRingCat.{u}}

private theorem mem_specMap_asIdeal_consolidated92 (ψ : A ⟶ B)
    (q : PrimeSpectrum B) (a : A) :
    a ∈ ((Spec.map ψ) q).asIdeal ↔ (ConcreteCategory.hom ψ) a ∈ q.asIdeal := Iff.rfl

private theorem vanishingIdeal_preimage_specMap_consolidated92 (φ : A ⟶ B) [IsIso φ]
    (W : Set (PrimeSpectrum A)) :
    PrimeSpectrum.vanishingIdeal (⇑(Spec.map φ) ⁻¹' W)
      = Ideal.map (ConcreteCategory.hom φ) (PrimeSpectrum.vanishingIdeal W) := by
  have hinv : ∀ p : PrimeSpectrum (A : Type u),
      ((Spec.map φ) ((Spec.map (inv φ)) p) : PrimeSpectrum (A : Type u)) = p := by
    intro p
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro a
    constructor
    · intro hmem
      have h1 : (ConcreteCategory.hom (inv φ)) ((ConcreteCategory.hom φ) a) ∈ p.asIdeal :=
        (mem_specMap_asIdeal_consolidated92 (inv φ) p _).mp ((mem_specMap_asIdeal_consolidated92 φ _ a).mp hmem)
      rwa [IsIso.hom_inv_id_apply] at h1
    · intro hmem
      refine (mem_specMap_asIdeal_consolidated92 φ _ a).mpr ?_
      refine (mem_specMap_asIdeal_consolidated92 (inv φ) p _).mpr ?_
      rw [IsIso.hom_inv_id_apply]
      exact hmem
  apply le_antisymm
  · intro a ha
    rw [PrimeSpectrum.mem_vanishingIdeal] at ha
    have hmem : (ConcreteCategory.hom (inv φ)) a ∈ PrimeSpectrum.vanishingIdeal W := by
      rw [PrimeSpectrum.mem_vanishingIdeal]
      intro p hp
      have h1 : (Spec.map φ) ((Spec.map (inv φ)) p) ∈ W :=
        cast (congrArg (fun x : PrimeSpectrum (A : Type u) => x ∈ W) (hinv p)).symm hp
      exact (mem_specMap_asIdeal_consolidated92 (inv φ) p a).mp (ha _ h1)
    have h3 : (ConcreteCategory.hom φ) ((ConcreteCategory.hom (inv φ)) a) = a := by
      rw [IsIso.inv_hom_id_apply]
    have h5 := Ideal.mem_map_of_mem (ConcreteCategory.hom φ) hmem
    rwa [h3] at h5
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [PrimeSpectrum.mem_vanishingIdeal] at ha
    rw [Ideal.mem_comap, PrimeSpectrum.mem_vanishingIdeal]
    intro q hq
    exact (mem_specMap_asIdeal_consolidated92 φ q a).mp (ha _ hq)


end

private theorem vanishingIdeal_preimage_fromSpec_of_isIso_consolidated92 {Y Y' : Scheme.{u}} (ψ : Y' ⟶ Y) [IsIso ψ]
    (T : Set Y) (U : Y.affineOpens) (hV : IsAffineOpen (ψ ⁻¹ᵁ (U : Y.Opens))) :
    PrimeSpectrum.vanishingIdeal (⇑hV.fromSpec ⁻¹' (⇑ψ ⁻¹' T))
      = Ideal.map (ConcreteCategory.hom (ψ.app (U : Y.Opens)))
          (PrimeSpectrum.vanishingIdeal (⇑U.2.fromSpec ⁻¹' T)) := by
  have : IsIso (ψ.app (U : Y.Opens)) := inferInstance
  have hU : IsAffineOpen (U : Y.Opens) := U.2
  have happ : ψ.appLE (U : Y.Opens) (ψ ⁻¹ᵁ (U : Y.Opens)) le_rfl = ψ.app (U : Y.Opens) := by
    simp [Scheme.Hom.appLE]
  have hsq : Spec.map (ψ.app (U : Y.Opens)) ≫ hU.fromSpec = hV.fromSpec ≫ ψ := by
    rw [← happ]
    exact AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec ψ hU hV le_rfl
  have hpt : ∀ z, ψ (hV.fromSpec z) = hU.fromSpec ((Spec.map (ψ.app (U : Y.Opens))) z) := by
    intro z
    have h := congrArg
      (fun m : Spec Γ(Y', ψ ⁻¹ᵁ (U : Y.Opens)) ⟶ Y => ⇑m z) hsq
    simpa using h.symm
  refine Eq.trans ?_ (vanishingIdeal_preimage_specMap_consolidated92 (ψ.app (U : Y.Opens)) (⇑hU.fromSpec ⁻¹' T))
  exact congrArg PrimeSpectrum.vanishingIdeal
    (Set.ext fun z => iff_of_eq (congrArg (fun y => y ∈ T) (hpt z)))

section
variable {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S)

private theorem map_mem_maximalIdeal_ringEquiv_consolidated92 {a : R}
    (h : a ∈ IsLocalRing.maximalIdeal R) : e a ∈ IsLocalRing.maximalIdeal S := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h
  intro hu
  exact h (by simpa using hu.map (e.symm : S →+* R))

private theorem isRegularParameterSystem_ringEquiv_consolidated92 (n : ℕ) (x : Fin n → R)
    (h : IsRegularParameterSystem R n x) :
    IsRegularParameterSystem S n (fun i => e (x i)) := by
  obtain ⟨hspan, hdim⟩ := h
  have hle : Ideal.span (Set.range fun i => e (x i)) ≤ IsLocalRing.maximalIdeal S := by
    rw [Ideal.span_le]
    rintro z ⟨i, rfl⟩
    show e (x i) ∈ IsLocalRing.maximalIdeal S
    refine map_mem_maximalIdeal_ringEquiv_consolidated92 e ?_
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hge : IsLocalRing.maximalIdeal S ≤ Ideal.span (Set.range fun i => e (x i)) := by
    intro y hy
    have h1 : Ideal.span (Set.range x)
        ≤ Ideal.comap (e : R →+* S) (Ideal.span (Set.range fun i => e (x i))) := by
      rw [Ideal.span_le]
      rintro z ⟨i, rfl⟩
      simp only [SetLike.mem_coe, Ideal.mem_comap, RingHom.coe_coe]
      exact Ideal.subset_span ⟨i, rfl⟩
    have h2 : e.symm y ∈ IsLocalRing.maximalIdeal R := map_mem_maximalIdeal_ringEquiv_consolidated92 e.symm hy
    have h3 : e.symm y ∈ Ideal.span (Set.range x) := by rw [hspan]; exact h2
    have h4 := h1 h3
    rw [Ideal.mem_comap] at h4
    simpa using h4
  exact ⟨le_antisymm hle hge, hdim.trans (ringKrullDim_eq_of_ringEquiv e)⟩


end

private theorem isRegularParameterSystem_congr_consolidated92 {R : Type u} [CommRing R] [IsLocalRing R]
    (n : ℕ) {x y : Fin n → R} (h : ∀ i, x i = y i) (hy : IsRegularParameterSystem R n y) :
    IsRegularParameterSystem R n x := by
  have hxy : x = y := funext h
  rw [hxy]
  exact hy

private theorem iso_inv_comp_eq_comp_inv_consolidated92 {W Y Z T : Scheme.{u}} (a : W ≅ Y) (b : Z ≅ T)
    (p : W ⟶ Z) (q : Y ⟶ T) (hw : a.hom ≫ q = p ≫ b.hom) :
    a.inv ≫ p = q ≫ b.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, hw, Category.assoc, Iso.hom_inv_id, Category.comp_id]

section
variable {X : Scheme.{u}}

private theorem eqToIso_hom_comp_projectionToBase_of_eq_consolidated92 (s : SequenceOfBlowups X) {i j : ℕ}
    (hij : i = j) : (eqToIso (congrArg s.schemeAt hij)).hom ≫ s.projectionToBase j = s.projectionToBase i := by
  subst hij
  simp

private theorem iso_hom_comp_projectionToBase_of_commute_blowupMorphism_consolidated92 {B B' : SequenceOfBlowups X}
    (e : ∀ i : ℕ, i ≤ B.length → (B.schemeAt i ≅ B'.schemeAt i))
    (h0 : (e 0 (Nat.zero_le _)).hom ≫ B'.isoZero.hom = B.isoZero.hom)
    (hstep : ∀ i : ℕ, ∀ hi : i < B.length,
        (e (i + 1) hi).hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ (e i hi.le).hom) :
    ∀ (i : ℕ) (hi : i ≤ B.length), (e i hi).hom ≫ B'.projectionToBase i = B.projectionToBase i := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [B'.projectionToBase_zero, B.projectionToBase_zero]
    exact h0
  | succ n ih =>
    intro hi
    have hn : n < B.length := hi
    rw [B'.projectionToBase_succ, B.projectionToBase_succ, ← Category.assoc]
    show ((e (n + 1) hn).hom ≫ B'.transitionMapSucc n) ≫ B'.projectionToBase n
      = B.transitionMapSucc n ≫ B.projectionToBase n
    rw [hstep n hn, Category.assoc, ih hn.le]


end

section
variable {Y Z : Scheme.{u}}

private theorem mem_support_of_mem_support_comap_consolidated92 (g : Y ⟶ Z)
    (I : Z.IdealSheafData) {x : Y} (hx : x ∈ (I.comap g).support) : g x ∈ I.support := by
  have h := Scheme.IdealSheafData.support_comap I g
  rw [h] at hx
  exact hx

private theorem inv_mem_support_comap_of_iso_consolidated92 (g : Y ≅ Z) (I : Z.IdealSheafData)
    {x : Z} (hx : x ∈ I.support) : g.inv x ∈ (I.comap g.hom).support := by
  have hI : (I.comap g.hom).comap g.inv = I := by
    rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  have hx' : x ∈ ((I.comap g.hom).comap g.inv).support := by rw [hI]; exact hx
  exact mem_support_of_mem_support_comap_consolidated92 g.inv (I.comap g.hom) hx'

private theorem isIso_restrict_of_eq_consolidated92 {f₁ f₂ : Y ⟶ Z} (hf : f₁ = f₂)
    (U : Z.Opens) (h : IsIso (f₁ ∣_ U)) : IsIso (f₂ ∣_ U) := by
  subst hf
  exact h

private theorem isOpenMap_iso_hom_consolidated92 (g : Y ≅ Z) : IsOpenMap (⇑g.hom) :=
  (Scheme.homeoOfIso g).isOpenMap


end

private theorem isStrictNormalCrossingsDivisor_reducedInverseImage_iso_inv_comp_consolidated92 {Y Y' X : Scheme.{u}} (g : Y ≅ Y') (p : Y ⟶ X)
    (S : TopologicalSpace.Closeds X) (hS : IsStrictNormalCrossingsDivisor (reducedInverseImage p S)) :
    IsStrictNormalCrossingsDivisor (reducedInverseImage (g.inv ≫ p) S) := by
  intro y'
  obtain ⟨hreg, U, hy, n, fs, J, hrsp, hideal⟩ := hS (g.inv.base y')
  have hsi : IsIso (g.inv.stalkMap y') := inferInstance
  have hV : IsAffineOpen (g.inv ⁻¹ᵁ (U : Y.Opens)) := U.2.preimage_of_isIso g.inv
  have he : ∀ t, (asIso (g.inv.stalkMap y')).commRingCatIsoToRingEquiv t
      = (ConcreteCategory.hom (g.inv.stalkMap y')) t := fun _ => rfl
  have hnat : ∀ s : Γ(Y, (U : Y.Opens)),
      (ConcreteCategory.hom (Y'.presheaf.germ (g.inv ⁻¹ᵁ (U : Y.Opens)) y' hy))
          ((ConcreteCategory.hom (g.inv.app (U : Y.Opens))) s)
        = (asIso (g.inv.stalkMap y')).commRingCatIsoToRingEquiv
            ((ConcreteCategory.hom (Y.presheaf.germ (U : Y.Opens) (g.inv.base y') hy)) s) := by
    intro s
    rw [he]
    simp
  refine ⟨?_, ⟨g.inv ⁻¹ᵁ (U : Y.Opens), hV⟩, hy, n,
    fun i => (ConcreteCategory.hom (g.inv.app (U : Y.Opens))) (fs i), J, ?_, ?_⟩
  · have := hreg
    exact IsRegularLocalRing.of_ringEquiv (asIso (g.inv.stalkMap y')).commRingCatIsoToRingEquiv
  · refine isRegularParameterSystem_congr_consolidated92 n (fun i => hnat (fs i)) ?_
    exact isRegularParameterSystem_ringEquiv_consolidated92
      (asIso (g.inv.stalkMap y')).commRingCatIsoToRingEquiv n
      (fun i => (ConcreteCategory.hom
        (Y.presheaf.germ (U : Y.Opens) (g.inv.base y') hy)) (fs i)) hrsp
  · have h1 : (reducedInverseImage (g.inv ≫ p) S).ideal ⟨g.inv ⁻¹ᵁ (U : Y.Opens), hV⟩
        = PrimeSpectrum.vanishingIdeal
            (⇑hV.fromSpec ⁻¹' (⇑(g.inv ≫ p) ⁻¹' (S : Set X))) := by
      simp [reducedInverseImage, Scheme.IdealSheafData.vanishingIdeal_ideal]
    have h2 : (reducedInverseImage p S).ideal U
        = PrimeSpectrum.vanishingIdeal (⇑U.2.fromSpec ⁻¹' (⇑p ⁻¹' (S : Set X))) := by
      simp [reducedInverseImage, Scheme.IdealSheafData.vanishingIdeal_ideal]
    have hcomp : (⇑(g.inv ≫ p) ⁻¹' (S : Set X)) = ⇑g.inv ⁻¹' (⇑p ⁻¹' (S : Set X)) := by
      ext z
      simp
    rw [h1, hcomp, vanishingIdeal_preimage_fromSpec_of_isIso_consolidated92 g.inv (⇑p ⁻¹' (S : Set X)) U hV, ← h2, hideal,
      Ideal.map_span]
    simp [map_prod]

section
variable {X : Scheme.{u}}

theorem SequenceOfBlowups.Isomorphic.symm {B B' : SequenceOfBlowups X}
    (h : B.Isomorphic B') : B'.Isomorphic B := by
  obtain ⟨hL, e, h0, hstep, hcen⟩ := h
  have p1 : (e 0 (Nat.zero_le _)).inv ≫ B.isoZero.hom = B'.isoZero.hom := by
    rw [Iso.inv_comp_eq]
    exact h0.symm
  have p2 : ∀ (i : ℕ) (hi : i < B'.length),
      (e (i + 1) (by omega)).inv ≫ B.transitionMapSucc i
        = B'.transitionMapSucc i ≫ (e i (by omega)).inv := by
    intro i hi
    have hi' : i < B.length := by omega
    exact iso_inv_comp_eq_comp_inv_consolidated92 (e (i + 1) hi') (e i hi'.le) (B.transitionMapSucc i)
      (B'.transitionMapSucc i) (hstep i hi')
  have p3 : ∀ (i : ℕ) (hi : i < B'.length),
      (B.center i).comap (e i (by omega)).inv = B'.center i := by
    intro i hi
    have hi' : i < B.length := by omega
    rw [← hcen i hi', ← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  exact ⟨hL.symm, fun i hi => (e i (by omega)).symm, p1, p2, p3⟩

theorem SequenceOfBlowups.Isomorphic.trans {B B' B'' : SequenceOfBlowups X}
    (h : B.Isomorphic B') (h' : B'.Isomorphic B'') : B.Isomorphic B'' := by
  obtain ⟨hL, e, h0, hstep, hcen⟩ := h
  obtain ⟨hL', g, g0, gstep, gcen⟩ := h'
  have p1 : ((e 0 (Nat.zero_le _)).hom ≫ (g 0 (Nat.zero_le _)).hom) ≫ B''.isoZero.hom
      = B.isoZero.hom := by
    rw [Category.assoc, g0, h0]
  have p2 : ∀ (i : ℕ) (hi : i < B.length),
      ((e (i + 1) hi).hom ≫ (g (i + 1) (by omega)).hom) ≫ B''.transitionMapSucc i
        = B.transitionMapSucc i ≫ ((e i hi.le).hom ≫ (g i (by omega)).hom) := by
    intro i hi
    have hi' : i < B'.length := by omega
    rw [Category.assoc, gstep i hi', ← Category.assoc, hstep i hi, Category.assoc]
  have p3 : ∀ (i : ℕ) (hi : i < B.length),
      (B''.center i).comap ((e i hi.le).hom ≫ (g i (by omega)).hom) = B.center i := by
    intro i hi
    have hi' : i < B'.length := by omega
    rw [Scheme.IdealSheafData.comap_comp, gcen i hi', hcen i hi]
  exact ⟨hL.trans hL', fun i hi => (e i hi) ≪≫ (g i (by omega)), p1, p2, p3⟩

theorem SequenceOfBlowups.Isomorphic.exists_lastObjIso {B B' : SequenceOfBlowups X}
    (h : B.Isomorphic B') :
    ∃ e : B.lastObj ≅ B'.lastObj, e.hom ≫ B'.lastStructMap = B.lastStructMap := by
  obtain ⟨hL, e, h0, hstep, _⟩ := h
  refine ⟨e B.length le_rfl ≪≫ eqToIso (congrArg B'.schemeAt hL), ?_⟩
  rw [SequenceOfBlowups.lastStructMap_eq_projectionToBase, SequenceOfBlowups.lastStructMap_eq_projectionToBase, Iso.trans_hom,
    Category.assoc, eqToIso_hom_comp_projectionToBase_of_eq_consolidated92 B' hL]
  exact iso_hom_comp_projectionToBase_of_commute_blowupMorphism_consolidated92 e h0 hstep B.length le_rfl


end

theorem IsStrongResolution.of_isomorphic (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    {B B' : SequenceOfBlowups X} (h : B.Isomorphic B') (hB : IsStrongResolution k X f B) :
    IsStrongResolution k X f B' := by
  obtain ⟨ε, hε⟩ := h.exists_lastObjIso
  obtain ⟨hs, hp, hiso, hd, hc, hsnc⟩ := hB
  have hmap : B'.lastStructMap = ε.inv ≫ B.lastStructMap := by
    rw [← hε, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have q1 : Smooth (B'.lastStructMap ≫ f) := by
    have := hs
    rw [hmap, Category.assoc]
    infer_instance
  have q2 : IsProper B'.lastStructMap := by
    have := hp
    rw [hmap]
    infer_instance
  have q3 : CategoryTheory.IsIso
      (AlgebraicGeometry.morphismRestrict B'.lastStructMap f.smoothLocus) := by
    have hres : IsIso (ε.hom ∣_ (B'.lastStructMap ⁻¹ᵁ f.smoothLocus)) := inferInstance
    have hA : IsIso (ε.hom ∣_ (B'.lastStructMap ⁻¹ᵁ f.smoothLocus) ≫ B'.lastStructMap ∣_ f.smoothLocus) := by
      have h0 : IsIso ((ε.hom ≫ B'.lastStructMap) ∣_ f.smoothLocus) :=
        isIso_restrict_of_eq_consolidated92 hε.symm f.smoothLocus hiso
      rw [AlgebraicGeometry.morphismRestrict_comp] at h0
      exact h0
    exact IsIso.of_isIso_comp_left (ε.hom ∣_ (B'.lastStructMap ⁻¹ᵁ f.smoothLocus))
      (B'.lastStructMap ∣_ f.smoothLocus)
  have q4 : Dense (⇑B'.lastStructMap ⁻¹' (f.smoothLocus : Set X)) := by
    have hpre : ⇑B'.lastStructMap ⁻¹' (f.smoothLocus : Set X)
        = ⇑ε.inv ⁻¹' (⇑B.lastStructMap ⁻¹' (f.smoothLocus : Set X)) := by
      rw [hmap]
      ext x
      simp
    rw [hpre]
    exact hd.preimage (isOpenMap_iso_hom_consolidated92 ε.symm)
  have q5 : B'.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds X) : Set X) := by
    obtain ⟨hL, eiso, h0, hstep, hcen⟩ := h
    intro i hi x hx
    have hi' : i < B.length := by omega
    have hy := inv_mem_support_comap_of_iso_consolidated92 (eiso i hi'.le) (B'.center i) hx
    rw [hcen i hi'] at hy
    have hpt := hc i hi' _ hy
    have hkey : (eiso i hi'.le).hom ≫ B'.projectionToBase i = B.projectionToBase i :=
      iso_hom_comp_projectionToBase_of_commute_blowupMorphism_consolidated92 eiso h0 hstep i hi'.le
    have hinv : (eiso i hi'.le).inv ≫ B.projectionToBase i = B'.projectionToBase i := by
      rw [← hkey, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    have hval : B'.projectionToBase i x = B.projectionToBase i ((eiso i hi'.le).inv x) := by
      rw [← hinv]
      simp
    rw [hval]
    exact hpt
  have q6 : IsStrictNormalCrossingsDivisor (reducedInverseImage B'.lastStructMap (smoothLocusComplement f)) := by
    rw [hmap]
    exact isStrictNormalCrossingsDivisor_reducedInverseImage_iso_inv_comp_consolidated92 ε B.lastStructMap (smoothLocusComplement f) hsnc
  exact ⟨q1, q2, q3, q4, q5, q6⟩


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.ConcatComparisonMap
section


section

namespace BlowupSequenceData

section
variable {X : Scheme.{u}}

theorem toSequenceOfBlowups_isomorphic_of_iso (d d' : BlowupSequenceData X)
    (hlen : d.length = d'.length)
    (e : ∀ i : ℕ, i ≤ d.length → (d.obj i ≅ d'.obj i))
    (hzero : (e 0 (Nat.zero_le _)).hom ≫ d'.isoZero.hom = d.isoZero.hom)
    (hmap : ∀ (i : ℕ) (hi : i < d.length),
      (e (i + 1) hi).hom ≫ d'.map i = d.map i ≫ (e i hi.le).hom)
    (hcenter : ∀ (i : ℕ) (hi : i < d.length),
      (d'.center i).comap (e i hi.le).hom = d.center i) :
    d.toSequenceOfBlowups.Isomorphic d'.toSequenceOfBlowups := by
  refine ⟨?_, fun i hi => e i (hi.trans_eq d.toSequenceOfBlowups_length), ?_, ?_, ?_⟩
  · rw [d.toSequenceOfBlowups_length, d'.toSequenceOfBlowups_length]
    exact hlen
  · rw [d'.toSequenceOfBlowups_isoObjZero, d.toSequenceOfBlowups_isoObjZero]
    exact hzero
  · intro i hi
    rw [d'.toSequenceOfBlowups_blowupMorphism, d.toSequenceOfBlowups_blowupMorphism]
    exact hmap i (lt_of_lt_of_eq hi d.toSequenceOfBlowups_length)
  · intro i hi
    rw [d'.toSequenceOfBlowups_center, d.toSequenceOfBlowups_center]
    exact hcenter i (lt_of_lt_of_eq hi d.toSequenceOfBlowups_length)

theorem ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic (s : SequenceOfBlowups X) :
    (ofSequenceOfBlowups s).toSequenceOfBlowups.Isomorphic s := by
  refine ⟨(toSequenceOfBlowups_length (ofSequenceOfBlowups s)).trans (ofSequenceOfBlowups_length s), fun i _ => Iso.refl _, ?_, ?_, ?_⟩
  · have hz0 : (ofSequenceOfBlowups s).toSequenceOfBlowups.isoZero = s.isoZero :=
      (toSequenceOfBlowups_isoObjZero (ofSequenceOfBlowups s)).trans (ofSequenceOfBlowups_isoObjZero s)
    have hz : (ofSequenceOfBlowups s).toSequenceOfBlowups.isoZero.hom = s.isoZero.hom :=
      congrArg (fun e : (ofSequenceOfBlowups s).toSequenceOfBlowups.schemeAt 0 ≅ X => e.hom) hz0
    exact (Category.id_comp s.isoZero.hom).trans hz.symm
  · intro i _
    have hb : (ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMapSucc i = s.transitionMapSucc i :=
      (toSequenceOfBlowups_blowupMorphism (ofSequenceOfBlowups s) i).trans (ofSequenceOfBlowups_blowupMorphism s i)
    exact (Category.id_comp (s.transitionMapSucc i)).trans
      ((Category.comp_id ((ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMapSucc i)).trans hb).symm
  · intro i _
    have hc : (ofSequenceOfBlowups s).toSequenceOfBlowups.center i = s.center i :=
      (toSequenceOfBlowups_center (ofSequenceOfBlowups s) i).trans (ofSequenceOfBlowups_center s i)
    rw [hc]
    show (s.center i).comap (𝟙 (s.schemeAt i)) = s.center i
    simp


end

@[reducible]
def empty (X : Scheme.{u}) : BlowupSequenceData X := emptyBlowupSequenceData X

@[simp]
theorem empty_length (X : Scheme.{u}) : (empty X).length = 0 :=
  emptyBlowupSequenceData_length X

section
variable {X : Scheme.{u}} (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))

theorem append_schemeAt_eq_last_of_eq_length {j : ℕ} (h : j = s.length) :
    (s.append t).obj j = s.obj s.length := by
  subst h
  exact append_schemeAt_of_le_length s t le_rfl

theorem append_schemeAt_eq_right_of_pos {i j : ℕ} (hi : 0 < i) (h : j = s.length + i) :
    (s.append t).obj j = t.obj i := by
  have h2 : j - s.length = i := by omega
  rw [append_schemeAt_of_length_lt s t (by omega), h2]


end

def concatObjIsoRight {X : Scheme.{u}} (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (i j : ℕ) (h : j = s.length + i) : (s.append t).obj j ≅ t.obj i :=
  if hi : 0 < i then eqToIso (append_schemeAt_eq_right_of_pos s t hi h)
  else
    eqToIso (append_schemeAt_eq_last_of_eq_length s t (by omega)) ≪≫ t.isoZero.symm ≪≫
      eqToIso (congrArg (fun n => t.obj n) (show (0 : ℕ) = i by omega))

section
variable {X : Scheme.{u}} (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))

private theorem concatObjIsoRight_hom_of_pos_consolidated284 (i j : ℕ) (hi : 0 < i) (h : j = s.length + i) :
    (s.concatObjIsoRight t i j h).hom = eqToHom (append_schemeAt_eq_right_of_pos s t hi h) := by
  unfold concatObjIsoRight
  rw [dif_pos hi, eqToIso.hom]

private theorem concatObjIsoRight_hom_succ_consolidated284 (i j : ℕ) (h : j + 1 = s.length + (i + 1)) :
    (s.concatObjIsoRight t (i + 1) (j + 1) h).hom =
      eqToHom (append_schemeAt_eq_right_of_pos s t (Nat.succ_pos i) h) :=
  concatObjIsoRight_hom_of_pos_consolidated284 s t (i + 1) (j + 1) (Nat.succ_pos i) h

private theorem concatObjIsoRight_hom_zero_consolidated284 (j : ℕ) (h : j = s.length + 0) :
    (s.concatObjIsoRight t 0 j h).hom =
      eqToHom (append_schemeAt_eq_last_of_eq_length s t (show j = s.length by omega)) ≫ t.isoZero.inv := by
  unfold concatObjIsoRight
  rw [dif_neg (Nat.lt_irrefl 0)]
  simp


end

private theorem blowupMorphism_eq_eqToHom_conj_consolidated284 {Y : Scheme.{u}} (d : BlowupSequenceData Y) {a b : ℕ}
    (hab : a = b) :
    d.map a = eqToHom (congrArg d.obj (congrArg (fun n => n + 1) hab)) ≫ d.map b ≫
      eqToHom (congrArg d.obj hab.symm) := by
  subst hab
  simp

theorem concatObjIsoRight_hom_comm_blowupMorphism {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (i j : ℕ) (h : j = s.length + i) :
    (s.append t).map j ≫ (s.concatObjIsoRight t i j h).hom =
      (s.concatObjIsoRight t (i + 1) (j + 1) (by omega)).hom ≫ t.map i := by
  by_cases hi : 0 < i
  · have hgt : s.length < j := by omega
    rw [concatObjIsoRight_hom_of_pos_consolidated284 s t i j hi h,
      concatObjIsoRight_hom_succ_consolidated284 s t i j (by omega),
      append_blowupMorphism_of_length_lt s t hgt,
      blowupMorphism_eq_eqToHom_conj_consolidated284 t (show j - s.length = i by omega)]
    simp
  · have hi0 : i = 0 := by omega
    subst hi0
    have hj : j = s.length := by omega
    subst hj
    rw [concatObjIsoRight_hom_zero_consolidated284 s t s.length h,
      concatObjIsoRight_hom_succ_consolidated284 s t 0 s.length (by omega),
      append_blowupMorphism_length s t]
    simp

private theorem center_comap_eqToHom_congr_consolidated284 {Z Y : Scheme.{u}} (t : BlowupSequenceData Z)
    {a b : ℕ} (e : a = b) (h1 : Y = t.obj a) (h2 : Y = t.obj b) :
    (t.center a).comap (eqToHom h1) = (t.center b).comap (eqToIso h2).hom := by
  subst e
  rfl

private theorem comap_eqToHom_comap_eq_consolidated284 {A B C : Scheme.{u}} (e : A = B)
    (f : B ⟶ C) (I : C.IdealSheafData) (e' : A = B) :
    (I.comap f).comap (eqToHom e') = I.comap (eqToHom e ≫ f) := by
  subst e
  simp

theorem append_center_eq_comap_concatObjIsoRight {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (i j : ℕ) (h : j = s.length + i) :
    (s.append t).center j = (t.center i).comap (s.concatObjIsoRight t i j h).hom := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    obtain rfl : j = s.length := by omega
    have hiso : (s.concatObjIsoRight t 0 s.length h).hom =
        eqToHom (append_schemeAt_eq_last_of_eq_length s t rfl) ≫ t.isoZero.inv := by
      unfold concatObjIsoRight
      rw [dif_neg (Nat.lt_irrefl 0)]
      simp
    rw [append_center_length, hiso]
    exact comap_eqToHom_comap_eq_consolidated284 _ _ _ _
  · have hj : s.length < j := by omega
    have hiso : s.concatObjIsoRight t i j h = eqToIso (append_schemeAt_eq_right_of_pos s t hi h) := by
      unfold concatObjIsoRight
      exact dif_pos hi
    rw [append_center_of_length_lt s t hj, hiso]
    exact center_comap_eqToHom_congr_consolidated284 t (show j - s.length = i by omega) _ _

def toSeqComparisonMap {X' X : Scheme.{u}} (d' : BlowupSequenceData X') (d : BlowupSequenceData X)
    (c : ∀ i : ℕ, i ≤ d'.length → (d'.obj i ⟶ d.obj i)) (i : ℕ)
    (hi : i ≤ d'.toSequenceOfBlowups.length) : d'.toSequenceOfBlowups.schemeAt i ⟶ d.toSequenceOfBlowups.schemeAt i :=
  eqToHom (toSequenceOfBlowups_schemeAt d' i) ≫ c i (hi.trans_eq (toSequenceOfBlowups_length d')) ≫
    eqToHom (toSequenceOfBlowups_schemeAt d i).symm

section
variable {X' X : Scheme.{u}}

private theorem toSequenceOfBlowups_length_eq_of_length_eq_consolidated284 {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (hlen : d'.length = d.length) : d'.toSequenceOfBlowups.length = d.toSequenceOfBlowups.length := by
  rw [toSequenceOfBlowups_length, toSequenceOfBlowups_length]
  exact hlen

private theorem toSeqComparisonMap_zero_comp_isoObjZero_consolidated284 {g : X' ⟶ X} {d' : BlowupSequenceData X'}
    {d : BlowupSequenceData X} (c : ∀ i : ℕ, i ≤ d'.length → (d'.obj i ⟶ d.obj i))
    (hzero : c 0 (Nat.zero_le _) ≫ d.isoZero.hom = d'.isoZero.hom ≫ g) :
    toSeqComparisonMap d' d c 0 (Nat.zero_le _) ≫ d.toSequenceOfBlowups.isoZero.hom = d'.toSequenceOfBlowups.isoZero.hom ≫ g := by
  have hp : toSeqComparisonMap d' d c 0 (Nat.zero_le _) = c 0 (Nat.zero_le _) :=
    (Category.id_comp (c 0 (Nat.zero_le _) ≫ 𝟙 (d.obj 0))).trans (Category.comp_id _)
  have hz : d.toSequenceOfBlowups.isoZero.hom = d.isoZero.hom :=
    congrArg (fun e : d.toSequenceOfBlowups.schemeAt 0 ≅ X => e.hom) (toSequenceOfBlowups_isoObjZero d)
  have hz' : d'.toSequenceOfBlowups.isoZero.hom = d'.isoZero.hom :=
    congrArg (fun e : d'.toSequenceOfBlowups.schemeAt 0 ≅ X' => e.hom) (toSequenceOfBlowups_isoObjZero d')
  rw [hp, hz, hz']
  exact hzero

private theorem isPullback_toSeqComparisonMap_consolidated284 {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : ∀ i : ℕ, i ≤ d'.length → (d'.obj i ⟶ d.obj i))
    (hpb : ∀ (i : ℕ) (hi : i < d'.length),
      IsPullback (c (i + 1) hi) (d'.map i) (d.map i) (c i hi.le))
    (i : ℕ) (hi : i < d'.toSequenceOfBlowups.length) :
    IsPullback (toSeqComparisonMap d' d c (i + 1) hi) (d'.toSequenceOfBlowups.transitionMapSucc i) (d.toSequenceOfBlowups.transitionMapSucc i)
      (toSeqComparisonMap d' d c i hi.le) := by
  have hi' : i < d'.length := hi.trans_eq (toSequenceOfBlowups_length d')
  have h1 : toSeqComparisonMap d' d c (i + 1) hi = c (i + 1) hi' := by
    show 𝟙 (d'.obj (i + 1)) ≫ c (i + 1) hi' ≫ 𝟙 (d.obj (i + 1)) = c (i + 1) hi'
    rw [Category.id_comp, Category.comp_id]
  have h2 : toSeqComparisonMap d' d c i hi.le = c i hi'.le := by
    show 𝟙 (d'.obj i) ≫ c i hi'.le ≫ 𝟙 (d.obj i) = c i hi'.le
    rw [Category.id_comp, Category.comp_id]
  rw [h1, h2, toSequenceOfBlowups_blowupMorphism, toSequenceOfBlowups_blowupMorphism]
  exact hpb i hi'


end

private theorem eq_comap_eqToHom_conj_of_heq_consolidated284 {A A' B B' : Scheme.{u}} (e1 : A = A') (e2 : B = B')
    (f : A' ⟶ B') (I : B.IdealSheafData) (I' : B'.IdealSheafData)
    (J : A.IdealSheafData) (J' : A'.IdealSheafData)
    (hI : HEq I I') (hJ : HEq J J') (h : J' = I'.comap f) :
    J = I.comap (eqToHom e1 ≫ f ≫ eqToHom e2.symm) := by
  subst e1
  subst e2
  have hI2 : I = I' := eq_of_heq hI
  have hJ2 : J = J' := eq_of_heq hJ
  rw [hI2, hJ2, h]
  simp

private theorem toSequenceOfBlowups_center_eq_comap_toSeqComparisonMap_consolidated284 {X' X : Scheme.{u}} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : ∀ i : ℕ, i ≤ d'.length → (d'.obj i ⟶ d.obj i))
    (hc : ∀ (i : ℕ) (hi : i < d'.length), d'.center i = (d.center i).comap (c i hi.le))
    (i : ℕ) (hi : i < d'.toSequenceOfBlowups.length) :
    d'.toSequenceOfBlowups.center i = (d.toSequenceOfBlowups.center i).comap (toSeqComparisonMap d' d c i hi.le) := by
  have h1 : i < d'.length := lt_of_lt_of_eq hi (toSequenceOfBlowups_length d')
  exact eq_comap_eqToHom_conj_of_heq_consolidated284 (toSequenceOfBlowups_schemeAt d' i) (toSequenceOfBlowups_schemeAt d i) (c i h1.le)
    (d.toSequenceOfBlowups.center i) (d.center i) (d'.toSequenceOfBlowups.center i) (d'.center i)
    (heq_of_eq (toSequenceOfBlowups_center d i)) (heq_of_eq (toSequenceOfBlowups_center d' i)) (hc i h1)

def toStrictPullbackSeq {X' X : Scheme.{u}} (g : X' ⟶ X) (d' : BlowupSequenceData X')
    (d : BlowupSequenceData X) (hlen : d'.length = d.length)
    (c : ∀ i : ℕ, i ≤ d'.length → (d'.obj i ⟶ d.obj i))
    (hzero : c 0 (Nat.zero_le _) ≫ d.isoZero.hom = d'.isoZero.hom ≫ g)
    (hpb : ∀ (i : ℕ) (hi : i < d'.length),
      IsPullback (c (i + 1) hi) (d'.map i) (d.map i) (c i hi.le))
    (hc : ∀ (i : ℕ) (hi : i < d'.length), d'.center i = (d.center i).comap (c i hi.le)) :
    StrictPullbackBlowupSeq g d'.toSequenceOfBlowups d.toSequenceOfBlowups where
  comp := toSeqComparisonMap d' d c
  comp_zero := toSeqComparisonMap_zero_comp_isoObjZero_consolidated284 c hzero
  pullback := isPullback_toSeqComparisonMap_consolidated284 c hpb
  length_eq := toSequenceOfBlowups_length_eq_of_length_eq_consolidated284 hlen
  center_eq := toSequenceOfBlowups_center_eq_comap_toSeqComparisonMap_consolidated284 c hc

end BlowupSequenceData

namespace StrictPullbackBlowupSeq

def lastMap {X' X : Scheme.{u}} {g : X' ⟶ X} {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (D : StrictPullbackBlowupSeq g t s) : t.schemeAt t.length ⟶ s.schemeAt s.length :=
  D.comp t.length le_rfl ≫ eqToHom (congrArg (fun n => s.schemeAt n) D.length_eq)

theorem lastMap_eq {X' X : Scheme.{u}} {g : X' ⟶ X} {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (D : StrictPullbackBlowupSeq g t s) :
    D.lastMap = D.comp t.length le_rfl ≫ eqToHom (congrArg (fun n => s.schemeAt n) D.length_eq) :=
  rfl

end StrictPullbackBlowupSeq

namespace BlowupSequenceData

def concatComparisonMap {X' X : Scheme.{u}} (g : X' ⟶ X) (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData (s'.obj s'.length))
    (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)
    (i : ℕ) (hi : i ≤ (s'.append t').length) :
    (s'.append t').obj i ⟶ (s.append t).obj i :=
  have hlen : s'.length = s.length :=
    (toSequenceOfBlowups_length s').symm.trans (D.length_eq.trans (toSequenceOfBlowups_length s))
  have hi2 : i ≤ s'.length + t'.length := hi
  if h : i ≤ s'.length then
    eqToHom (append_schemeAt_of_le_length s' t' h) ≫ eqToHom (toSequenceOfBlowups_schemeAt s' i).symm ≫
      D.comp i (h.trans_eq (toSequenceOfBlowups_length s').symm) ≫ eqToHom (toSequenceOfBlowups_schemeAt s i) ≫
        eqToHom (append_schemeAt_of_le_length s t (show i ≤ s.length by omega)).symm
  else
    (s'.concatObjIsoRight t' (i - s'.length) i (by omega)).hom ≫
      eqToHom (toSequenceOfBlowups_schemeAt t' (i - s'.length)).symm ≫
        D'.comp (i - s'.length)
            ((show i - s'.length ≤ t'.length by omega).trans_eq (toSequenceOfBlowups_length t').symm) ≫
          eqToHom (toSequenceOfBlowups_schemeAt t (i - s'.length)) ≫
            (s.concatObjIsoRight t (i - s'.length) i (by omega)).inv

theorem append_length_eq_of_strictPullbackBlowupSeq {X' X : Scheme.{u}} (g : X' ⟶ X) (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData (s'.obj s'.length))
    (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) :
    (s'.append t').length = (s.append t).length := by
  have h1 : s'.length = s.length :=
    (toSequenceOfBlowups_length s').symm.trans (D.length_eq.trans (toSequenceOfBlowups_length s))
  have h2 : t'.length = t.length :=
    (toSequenceOfBlowups_length t').symm.trans (D'.length_eq.trans (toSequenceOfBlowups_length t))
  show s'.length + t'.length = s.length + t.length
  omega

private theorem eqToHom_conj_comp_eq_comp_of_heq_consolidated284 {P Q Q' R R' S X' X : Scheme.{u}}
    (a₁ : P = Q) (a₂ : Q = Q') (a₃ : R' = R) (a₄ : R = S) (a₅ : S = R)
    (u : Q' ⟶ R') (izs : R ⟶ X) (izsT : R' ⟶ X) (izs' : Q ⟶ X') (izs'T : Q' ⟶ X')
    (g : X' ⟶ X) (h1 : HEq izsT izs) (h2 : HEq izs'T izs')
    (key : u ≫ izsT = izs'T ≫ g) :
    (eqToHom a₁ ≫ eqToHom a₂ ≫ u ≫ eqToHom a₃ ≫ eqToHom a₄) ≫ eqToHom a₅ ≫ izs =
      (eqToHom a₁ ≫ izs') ≫ g := by
  subst a₄
  subst a₃
  subst a₂
  subst a₁
  have e1 : izsT = izs := eq_of_heq h1
  have e2 : izs'T = izs' := eq_of_heq h2
  subst e1
  subst e2
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact key

private theorem concatComparisonMap_zero_comp_isoObjZero_consolidated284 {X' X : Scheme.{u}} (g : X' ⟶ X) (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData (s'.obj s'.length))
    (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) :
    concatComparisonMap g s t s' t' D D' 0 (Nat.zero_le _) ≫ (s.append t).isoZero.hom =
      (s'.append t').isoZero.hom ≫ g := by
  rw [append_isoObjZero_hom s t, append_isoObjZero_hom s' t']
  refine eqToHom_conj_comp_eq_comp_of_heq_consolidated284 (append_schemeAt_of_le_length s' t' (Nat.zero_le _))
    (toSequenceOfBlowups_schemeAt s' 0).symm (toSequenceOfBlowups_schemeAt s 0) (append_schemeAt_of_le_length s t (Nat.zero_le _)).symm
    (append_schemeAt_zero s t) (D.comp 0 (Nat.zero_le _)) s.isoZero.hom s.toSequenceOfBlowups.isoZero.hom
    s'.isoZero.hom s'.toSequenceOfBlowups.isoZero.hom g ?_ ?_ D.comp_zero
  · exact heq_of_eq (congrArg (fun e : s.toSequenceOfBlowups.schemeAt 0 ≅ X => e.hom) (toSequenceOfBlowups_isoObjZero s))
  · exact heq_of_eq (congrArg (fun e : s'.toSequenceOfBlowups.schemeAt 0 ≅ X' => e.hom) (toSequenceOfBlowups_isoObjZero s'))

section
variable {Pa Xa Ya Za Pb Xb Yb Z₂ : Scheme.{u}} {fst : Pa ⟶ Xa} {snd : Pa ⟶ Ya} {f : Xa ⟶ Za} {gg : Ya ⟶ Za} (h : IsPullback fst snd f gg)
include h

private theorem isPullback_of_conj_iso_consolidated284 (eP : Pa ≅ Pb) (eA : Xa ≅ Xb) (eB : Ya ≅ Yb) (eC : Za ≅ Z₂)
    {fst' : Pb ⟶ Xb} {snd' : Pb ⟶ Yb} {f' : Xb ⟶ Z₂} {gg' : Yb ⟶ Z₂}
    (h1 : fst' = eP.inv ≫ fst ≫ eA.hom) (h2 : snd' = eP.inv ≫ snd ≫ eB.hom)
    (h3 : f' = eA.inv ≫ f ≫ eC.hom) (h4 : gg' = eB.inv ≫ gg ≫ eC.hom) :
    IsPullback fst' snd' f' gg' := by
  subst h1
  subst h2
  subst h3
  subst h4
  refine h.of_iso eP eA eB eC ?_ ?_ ?_ ?_ <;> simp

private theorem isPullback_of_conj_eqToHom_consolidated284 (ep : Pb = Pa) (ex : Xa = Xb) (ey : Ya = Yb) (ez : Za = Z₂)
    {fst' : Pb ⟶ Xb} {snd' : Pb ⟶ Yb} {f' : Xb ⟶ Z₂} {gg' : Yb ⟶ Z₂}
    (h1 : fst' = eqToHom ep ≫ fst ≫ eqToHom ex)
    (h2 : snd' = eqToHom ep ≫ snd ≫ eqToHom ey)
    (h3 : f' = eqToHom ex.symm ≫ f ≫ eqToHom ez)
    (h4 : gg' = eqToHom ey.symm ≫ gg ≫ eqToHom ez) :
    IsPullback fst' snd' f' gg' := by
  subst ep
  subst ex
  subst ey
  subst ez
  subst h1
  subst h2
  subst h3
  subst h4
  simpa using h

private theorem isPullback_of_conj_eqToHom_iso_consolidated284 (ep : Pb = Pa) (ex : Xa = Xb) (ey : Ya ≅ Yb) (ez : Za ≅ Z₂)
    {fst' : Pb ⟶ Xb} {snd' : Pb ⟶ Yb} {f' : Xb ⟶ Z₂} {gg' : Yb ⟶ Z₂}
    (h1 : fst' = eqToHom ep ≫ fst ≫ eqToHom ex)
    (h2 : snd' = eqToHom ep ≫ snd ≫ ey.hom)
    (h3 : f' = eqToHom ex.symm ≫ f ≫ ez.hom)
    (h4 : gg' = ey.inv ≫ gg ≫ ez.hom) :
    IsPullback fst' snd' f' gg' := by
  subst ep
  subst ex
  subst h1
  subst h2
  subst h3
  subst h4
  refine isPullback_of_conj_iso_consolidated284 h (Iso.refl _) (Iso.refl _) ey ez ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · simp


end

private theorem eqToHom_comp_eqToHom_conj_eq_consolidated284 {A B R1 R1' R2 R2' C Dd : Scheme.{u}} (f : R1 ⟶ R2)
    (a1 : A = B) (a2 : B = R1') (e1 : R1' = R1) (e2 : R2 = R2') (b1 : R2' = C) (b2 : C = Dd)
    (c1 : A = R1) (c2 : R2 = Dd) :
    eqToHom a1 ≫ eqToHom a2 ≫ (eqToHom e1 ≫ f ≫ eqToHom e2) ≫ eqToHom b1 ≫ eqToHom b2
      = eqToHom c1 ≫ f ≫ eqToHom c2 := by
  subst a1
  subst a2
  subst e1
  subst e2
  subst b1
  subst b2
  simp

private theorem eq_iso_inv_comp_comp_hom_of_comm_sq_consolidated284 {P Q R1 R2 S1 S2 : Scheme.{u}}
    (tm : R1 ⟶ R2) (z1 : S1 ≅ R1) (z2 : S2 ≅ R2) (u : S1 ⟶ S2)
    (hz : u ≫ z2.hom = z1.hom ≫ tm)
    (c1 : R1 = P) (c2 : R2 = Q) (lhs : P ⟶ Q)
    (hl : lhs = eqToHom c1.symm ≫ tm ≫ eqToHom c2) :
    lhs = (z1 ≪≫ eqToIso c1).inv ≫ u ≫ (z2 ≪≫ eqToIso c2).hom := by
  subst c1
  subst c2
  subst hl
  simp only [Iso.trans_inv, Iso.trans_hom, eqToIso.inv, eqToIso.hom, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  rw [hz]
  simp

section
variable {Y' Y : Scheme.{u}} {gg : Y' ⟶ Y} {d' : BlowupSequenceData Y'} {d : BlowupSequenceData Y} (E : StrictPullbackBlowupSeq gg d'.toSequenceOfBlowups d.toSequenceOfBlowups)

private theorem isPullback_blowupMorphism_of_strictPullbackBlowupSeq_consolidated284 (i : ℕ)
    (hi : i < d'.toSequenceOfBlowups.length) (h1 : i + 1 ≤ d'.toSequenceOfBlowups.length) (h2 : i ≤ d'.toSequenceOfBlowups.length) :
    IsPullback ((E.comp (i + 1) h1 : d'.obj (i + 1) ⟶ d.obj (i + 1))) (d'.map i) (d.map i)
      ((E.comp i h2 : d'.obj i ⟶ d.obj i)) := by
  rw [← toSequenceOfBlowups_blowupMorphism d' i, ← toSequenceOfBlowups_blowupMorphism d i]
  exact E.pullback i hi

private theorem isPullback_blowupMorphism_zero_of_strictPullbackBlowupSeq_consolidated284 (hi : 0 < d'.toSequenceOfBlowups.length) (h1 : 1 ≤ d'.toSequenceOfBlowups.length) (h2 : 0 ≤ d'.toSequenceOfBlowups.length) :
    IsPullback ((E.comp 1 h1 : d'.obj 1 ⟶ d.obj 1)) (d'.map 0) (d.map 0)
      ((E.comp 0 h2 : d'.obj 0 ⟶ d.obj 0)) :=
  isPullback_blowupMorphism_of_strictPullbackBlowupSeq_consolidated284 E 0 hi h1 h2


end

private theorem blowupMorphism_eqToHom_congr_consolidated284 {Y : Scheme.{u}} (d : BlowupSequenceData Y) {a b : ℕ} (hab : a = b)
    {A B : Scheme.{u}} (e1 : A = d.obj (a + 1)) (e2 : d.obj a = B)
    (f1 : A = d.obj (b + 1)) (f2 : d.obj b = B) :
    eqToHom e1 ≫ d.map a ≫ eqToHom e2 = eqToHom f1 ≫ d.map b ≫ eqToHom f2 := by
  subst hab
  rfl

private theorem strictPullback_map_eqToHom_congr_consolidated284 {X' X : Scheme.{u}} {g : X' ⟶ X} {u : SequenceOfBlowups X'}
    {v : SequenceOfBlowups X} (D : StrictPullbackBlowupSeq g u v) {a b : ℕ} (hab : a = b)
    (ha : a ≤ u.length) (hb : b ≤ u.length)
    {A A2 B2 B : Scheme.{u}} (e1 : A = A2) (e2 : A2 = u.schemeAt a) (e3 : v.schemeAt a = B2) (e4 : B2 = B)
    (f1 : A = u.schemeAt b) (f2 : v.schemeAt b = B) :
    eqToHom e1 ≫ eqToHom e2 ≫ D.comp a ha ≫ eqToHom e3 ≫ eqToHom e4
      = eqToHom f1 ≫ D.comp b hb ≫ eqToHom f2 := by
  subst hab
  subst e1
  subst e2
  subst e3
  subst e4
  simp

section
variable {X : Scheme.{u}} (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))

private theorem concatObjIsoRight_inv_of_pos_consolidated284 (i j : ℕ) (hi : 0 < i) (h : j = s.length + i) :
    (s.concatObjIsoRight t i j h).inv = eqToHom (append_schemeAt_eq_right_of_pos s t hi h).symm := by
  unfold concatObjIsoRight
  rw [dif_pos hi, eqToIso.inv]

private theorem append_blowupMorphism_of_eq_length_consolidated284 (j : ℕ) (hj : j = s.length)
    (f1 : (s.append t).obj (j + 1) = t.obj 1) (f2 : s.obj s.length = (s.append t).obj j) :
    (s.append t).map j = eqToHom f1 ≫ t.map 0 ≫ t.isoZero.hom ≫ eqToHom f2 := by
  subst hj
  exact append_blowupMorphism_length s t


end

private theorem comp_eq_of_eq_of_eq_consolidated284 {A B C : Scheme.{u}} {u : A ⟶ B} {p p' : B ⟶ C}
    {q q' : A ⟶ C} (h : u ≫ p = q) (hp : p = p') (hq : q = q') : u ≫ p' = q' := by
  subst hp
  subst hq
  exact h

private theorem strictPullback_map_eq_lastMap_of_eq_consolidated284 {X' X : Scheme.{u}} {g : X' ⟶ X} {u : SequenceOfBlowups X'}
    {v : SequenceOfBlowups X} (D : StrictPullbackBlowupSeq g u v) (a : ℕ) (ha : a ≤ u.length)
    (h : a = u.length) :
    D.comp a ha = eqToHom (congrArg u.schemeAt h) ≫ D.lastMap ≫
      eqToHom (congrArg v.schemeAt (h.trans D.length_eq)).symm := by
  subst h
  rw [StrictPullbackBlowupSeq.lastMap_eq]
  simp

section
variable {X' X : Scheme.{u}} (g : X' ⟶ X) (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length)) (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups) (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)

private theorem concatComparisonMap_of_le_consolidated284 (i : ℕ) (hi : i ≤ (s'.append t').length) (h : i ≤ s'.length) (h2 : i ≤ s.length)
    (h3 : i ≤ s'.toSequenceOfBlowups.length) :
    concatComparisonMap g s t s' t' D D' i hi =
      eqToHom (append_schemeAt_of_le_length s' t' h) ≫ eqToHom (toSequenceOfBlowups_schemeAt s' i).symm ≫
        D.comp i h3 ≫ eqToHom (toSequenceOfBlowups_schemeAt s i) ≫ eqToHom (append_schemeAt_of_le_length s t h2).symm := by
  unfold concatComparisonMap
  exact dif_pos h

private theorem concatComparisonMap_of_not_le_consolidated284 (i a : ℕ) (hi : i ≤ (s'.append t').length) (h : ¬ i ≤ s'.length)
    (ha : i - s'.length = a) (pf1 : i = s'.length + a) (pf2 : a ≤ t'.toSequenceOfBlowups.length)
    (pf3 : i = s.length + a) :
    concatComparisonMap g s t s' t' D D' i hi =
      (s'.concatObjIsoRight t' a i pf1).hom ≫ eqToHom (toSequenceOfBlowups_schemeAt t' a).symm ≫
        D'.comp a pf2 ≫ eqToHom (toSequenceOfBlowups_schemeAt t a) ≫ (s.concatObjIsoRight t a i pf3).inv := by
  subst ha
  unfold concatComparisonMap
  exact dif_neg h

private theorem isPullback_concatComparisonMap_consolidated284 (i : ℕ) (hi : i < (s'.append t').length) :
    IsPullback (concatComparisonMap g s t s' t' D D' (i + 1) hi) ((s'.append t').map i)
      ((s.append t).map i) (concatComparisonMap g s t s' t' D D' i hi.le) := by
  have hlen : s'.length = s.length :=
    (toSequenceOfBlowups_length s').symm.trans (D.length_eq.trans (toSequenceOfBlowups_length s))
  have hlen2 : t'.length = t.length :=
    (toSequenceOfBlowups_length t').symm.trans (D'.length_eq.trans (toSequenceOfBlowups_length t))
  have hsl : s'.toSequenceOfBlowups.length = s'.length := toSequenceOfBlowups_length s'
  have htl : t'.toSequenceOfBlowups.length = t'.length := toSequenceOfBlowups_length t'
  have hlt : i < s'.length + t'.length := hi
  rcases lt_trichotomy i s'.length with hc | hc | hc
  · have hiS : i < s.length := by omega
    have h1le : i + 1 ≤ s'.length := hc
    have h1leS : i + 1 ≤ s.length := by omega
    have h0le : i ≤ s'.length := hc.le
    have h0leS : i ≤ s.length := by omega
    have h1ts : i + 1 ≤ s'.toSequenceOfBlowups.length := by omega
    have h0ts : i ≤ s'.toSequenceOfBlowups.length := by omega
    have hlt' : i < s'.toSequenceOfBlowups.length := by omega
    have hpb := isPullback_blowupMorphism_of_strictPullbackBlowupSeq_consolidated284 D i hlt' h1ts h0ts
    refine isPullback_of_conj_eqToHom_consolidated284 hpb (append_schemeAt_of_le_length s' t' h1le)
      (append_schemeAt_of_le_length s t h1leS).symm (append_schemeAt_of_le_length s' t' h0le).symm
      (append_schemeAt_of_le_length s t h0leS).symm ?_ ?_ ?_ ?_
    · rw [concatComparisonMap_of_le_consolidated284 g s t s' t' D D' (i + 1) hi h1le h1leS h1ts]
      exact strictPullback_map_eqToHom_congr_consolidated284 D (rfl : i + 1 = i + 1) h1ts h1ts _ _ _ _ _ _
    · exact append_blowupMorphism_of_lt_length s' t' hc
    · exact append_blowupMorphism_of_lt_length s t hiS
    · rw [concatComparisonMap_of_le_consolidated284 g s t s' t' D D' i hi.le h0le h0leS h0ts]
      exact strictPullback_map_eqToHom_congr_consolidated284 D (rfl : i = i) h0ts h0ts _ _ _ _ _ _
  · have ht0 : 0 < t'.length := by omega
    have hup : ¬ (i + 1 ≤ s'.length) := by omega
    have ha1 : i + 1 - s'.length = 1 := by omega
    have pfA : i + 1 = s'.length + 1 := by omega
    have pfB : i + 1 = s.length + 1 := by omega
    have pf2' : (1 : ℕ) ≤ t'.toSequenceOfBlowups.length := by omega
    have h00 : (0 : ℕ) ≤ t'.toSequenceOfBlowups.length := Nat.zero_le _
    have h0lt : (0 : ℕ) < t'.toSequenceOfBlowups.length := by omega
    have hts0 : i ≤ s'.toSequenceOfBlowups.length := by omega
    have hileS : i ≤ s.length := by omega
    have hpb := isPullback_blowupMorphism_zero_of_strictPullbackBlowupSeq_consolidated284 D' h0lt pf2' h00
    have htz : t.toSequenceOfBlowups.isoZero.hom = t.isoZero.hom :=
      congrArg (fun e : t.toSequenceOfBlowups.schemeAt 0 ≅ s.obj s.length => e.hom) (toSequenceOfBlowups_isoObjZero t)
    have htz' : t'.toSequenceOfBlowups.isoZero.hom = t'.isoZero.hom :=
      congrArg (fun e : t'.toSequenceOfBlowups.schemeAt 0 ≅ s'.obj s'.length => e.hom) (toSequenceOfBlowups_isoObjZero t')
    have hz : D'.comp 0 h00 ≫ t.isoZero.hom = t'.isoZero.hom ≫ D.lastMap :=
      comp_eq_of_eq_of_eq_consolidated284 D'.comp_zero htz (congrArg (fun x => x ≫ D.lastMap) htz')
    have hcomp : D.comp i hts0
        = eqToHom (congrArg s'.toSequenceOfBlowups.schemeAt (hc.trans hsl.symm)) ≫ D.lastMap ≫
          eqToHom (congrArg s.toSequenceOfBlowups.schemeAt ((hc.trans hsl.symm).trans D.length_eq)).symm :=
      strictPullback_map_eq_lastMap_of_eq_consolidated284 D i hts0 (hc.trans hsl.symm)
    refine isPullback_of_conj_eqToHom_iso_consolidated284 hpb
      (append_schemeAt_eq_right_of_pos s' t' Nat.one_pos pfA)
      (append_schemeAt_eq_right_of_pos s t Nat.one_pos pfB).symm
      (t'.isoZero ≪≫ eqToIso (append_schemeAt_eq_last_of_eq_length s' t' hc).symm)
      (t.isoZero ≪≫ eqToIso (append_schemeAt_eq_last_of_eq_length s t (hc.trans hlen)).symm) ?_ ?_ ?_ ?_
    · rw [concatComparisonMap_of_not_le_consolidated284 g s t s' t' D D' (i + 1) 1 hi hup ha1 pfA pf2' pfB,
        concatObjIsoRight_hom_of_pos_consolidated284 s' t' 1 (i + 1) Nat.one_pos pfA,
        concatObjIsoRight_inv_of_pos_consolidated284 s t 1 (i + 1) Nat.one_pos pfB]
      exact strictPullback_map_eqToHom_congr_consolidated284 D' (rfl : (1 : ℕ) = 1) pf2' pf2' _ _ _ _ _ _
    · rw [Iso.trans_hom, eqToIso.hom]
      exact append_blowupMorphism_of_eq_length_consolidated284 s' t' i hc _ _
    · rw [Iso.trans_hom, eqToIso.hom]
      exact append_blowupMorphism_of_eq_length_consolidated284 s t i (hc.trans hlen) _ _
    · have hl : concatComparisonMap g s t s' t' D D' i hi.le =
          eqToHom (append_schemeAt_eq_last_of_eq_length s' t' hc) ≫ D.lastMap ≫
            eqToHom (append_schemeAt_eq_last_of_eq_length s t (hc.trans hlen)).symm := by
        rw [concatComparisonMap_of_le_consolidated284 g s t s' t' D D' i hi.le hc.le hileS hts0, hcomp]
        exact eqToHom_comp_eqToHom_conj_eq_consolidated284 D.lastMap _ _ _ _ _ _ _ _
      exact eq_iso_inv_comp_comp_hom_of_comm_sq_consolidated284 D.lastMap t'.isoZero t.isoZero (D'.comp 0 h00) hz
        (append_schemeAt_eq_last_of_eq_length s' t' hc).symm (append_schemeAt_eq_last_of_eq_length s t (hc.trans hlen)).symm _ hl
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, i = s'.length + (a + 1) := ⟨i - s'.length - 1, by omega⟩
    have hgt' : s'.length < s'.length + (a + 1) := by omega
    have hgtS : s.length < s'.length + (a + 1) := by omega
    have hne : ¬ (s'.length + (a + 1) ≤ s'.length) := by omega
    have hne1 : ¬ (s'.length + (a + 1) + 1 ≤ s'.length) := by omega
    have hA : s'.length + (a + 1) - s'.length = a + 1 := by omega
    have hA2 : s'.length + (a + 1) + 1 - s'.length = a + 1 + 1 := by omega
    have hB : s'.length + (a + 1) - s.length = a + 1 := by omega
    have pfU1 : s'.length + (a + 1) = s'.length + (a + 1) := rfl
    have pfU1' : s'.length + (a + 1) + 1 = s'.length + (a + 1 + 1) := by omega
    have pfU3 : s'.length + (a + 1) = s.length + (a + 1) := by omega
    have pfU3' : s'.length + (a + 1) + 1 = s.length + (a + 1 + 1) := by omega
    have pfT : a + 1 ≤ t'.toSequenceOfBlowups.length := by omega
    have pfT' : a + 1 + 1 ≤ t'.toSequenceOfBlowups.length := by omega
    have halt : a + 1 < t'.toSequenceOfBlowups.length := by omega
    have hpb := isPullback_blowupMorphism_of_strictPullbackBlowupSeq_consolidated284 D' (a + 1) halt pfT' pfT
    refine isPullback_of_conj_eqToHom_consolidated284 hpb
      (append_schemeAt_eq_right_of_pos s' t' (Nat.succ_pos (a + 1)) pfU1')
      (append_schemeAt_eq_right_of_pos s t (Nat.succ_pos (a + 1)) pfU3').symm
      (append_schemeAt_eq_right_of_pos s' t' (Nat.succ_pos a) pfU1).symm
      (append_schemeAt_eq_right_of_pos s t (Nat.succ_pos a) pfU3).symm ?_ ?_ ?_ ?_
    · rw [concatComparisonMap_of_not_le_consolidated284 g s t s' t' D D' (s'.length + (a + 1) + 1) (a + 1 + 1) hi hne1
          hA2 pfU1' pfT' pfU3',
        concatObjIsoRight_hom_of_pos_consolidated284 s' t' (a + 1 + 1) (s'.length + (a + 1) + 1)
          (Nat.succ_pos (a + 1)) pfU1',
        concatObjIsoRight_inv_of_pos_consolidated284 s t (a + 1 + 1) (s'.length + (a + 1) + 1)
          (Nat.succ_pos (a + 1)) pfU3']
      exact strictPullback_map_eqToHom_congr_consolidated284 D' (rfl : a + 1 + 1 = a + 1 + 1) pfT' pfT' _ _ _ _ _ _
    · rw [append_blowupMorphism_of_length_lt s' t' hgt']
      exact blowupMorphism_eqToHom_congr_consolidated284 t' hA _ _ _ _
    · rw [append_blowupMorphism_of_length_lt s t hgtS]
      exact blowupMorphism_eqToHom_congr_consolidated284 t hB _ _ _ _
    · rw [concatComparisonMap_of_not_le_consolidated284 g s t s' t' D D' (s'.length + (a + 1)) (a + 1) hi.le hne hA pfU1
          pfT pfU3,
        concatObjIsoRight_hom_of_pos_consolidated284 s' t' (a + 1) (s'.length + (a + 1)) (Nat.succ_pos a) pfU1,
        concatObjIsoRight_inv_of_pos_consolidated284 s t (a + 1) (s'.length + (a + 1)) (Nat.succ_pos a) pfU3]
      exact strictPullback_map_eqToHom_congr_consolidated284 D' (rfl : a + 1 = a + 1) pfT pfT _ _ _ _ _ _


end

private theorem eqToHom_trans_comp_comp_eqToHom_trans_consolidated284 {A A₁ A₂ B₂ B₁ B : Scheme.{u}}
    (a1 : A = A₁) (a2 : A₁ = A₂) (b1 : B₂ = B₁) (b2 : B₁ = B)
    (a : A = A₂) (b : B₂ = B) (c : A₂ ⟶ B₂) :
    eqToHom a1 ≫ eqToHom a2 ≫ c ≫ eqToHom b1 ≫ eqToHom b2 =
      eqToHom a ≫ c ≫ eqToHom b := by
  subst a1
  subst a2
  subst b1
  subst b2
  simp

private theorem eqToHom_trans_comp_comp_eqToHom_trans_eq_assoc_consolidated284 {A A₁ A₂ B₂ B₃ B₁ B : Scheme.{u}}
    (a1 : A = A₁) (a2 : A₁ = A₂) (b1 : B₂ = B₁) (b2 : B₁ = B)
    (a : A = A₂) (b3 : B₂ = B₃) (b4 : B₃ = B) (c : A₂ ⟶ B₂) :
    eqToHom a1 ≫ eqToHom a2 ≫ c ≫ eqToHom b1 ≫ eqToHom b2 =
      eqToHom a ≫ (c ≫ eqToHom b3) ≫ eqToHom b4 := by
  subst a1
  subst a2
  subst b1
  subst b2
  subst b3
  simp

section
variable {A A₁ B B₁ : Scheme.{u}}

private theorem comap_eqToHom_eq_comap_of_eq_comap_consolidated284 (e1 : A = A₁) (e2 : B = B₁)
    (c : A₁ ⟶ B₁) (f : A ⟶ B) (hf : f = eqToHom e1 ≫ c ≫ eqToHom e2.symm)
    (J : A₁.IdealSheafData) (K : B₁.IdealSheafData) (hJ : J = K.comap c) :
    J.comap (eqToHom e1) = (K.comap (eqToHom e2)).comap f := by
  subst hf
  subst hJ
  subst e1
  subst e2
  simp

private theorem comap_eq_comap_iso_hom_of_eq_comap_consolidated284 (u : A ⟶ A₁) (β : B ≅ B₁)
    (c : A₁ ⟶ B₁) (J : A₁.IdealSheafData) (K : B₁.IdealSheafData) (hJ : J = K.comap c)
    (p1 : A₁ = A₁) (p2 : B₁ = B₁) :
    J.comap u = (K.comap β.hom).comap (u ≫ eqToHom p1 ≫ c ≫ eqToHom p2 ≫ β.inv) := by
  subst hJ
  have hb : u ≫ eqToHom p1 ≫ c ≫ eqToHom p2 ≫ β.inv = u ≫ c ≫ β.inv := by simp
  have hb2 : (u ≫ c ≫ β.inv) ≫ β.hom = u ≫ c := by simp
  rw [hb, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hb2]


end

private theorem comap_iso_inv_eq_comap_of_comm_sq_consolidated284 {P Q A B : Scheme.{u}} (u : P ⟶ Q)
    (α : P ≅ A) (β : Q ≅ B) (G : A ⟶ B)
    (hz : u ≫ β.hom = α.hom ≫ G)
    (J : P.IdealSheafData) (K : Q.IdealSheafData) (hJ : J = K.comap u) :
    J.comap α.inv = (K.comap β.inv).comap G := by
  have h1 : α.inv ≫ u ≫ β.hom = G := by
    rw [hz, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hkey : α.inv ≫ u = G ≫ β.inv := by
    rw [← h1, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  subst hJ
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hkey]

private theorem append_center_of_eq_length_consolidated284 {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (j : ℕ) (hj : j = s.length) :
    (s.append t).center j =
      ((t.center 0).comap t.isoZero.inv).comap (eqToHom (append_schemeAt_eq_last_of_eq_length s t hj)) := by
  subst hj
  exact append_center_length s t

section
variable {X' X : Scheme.{u}} (g : X' ⟶ X) (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length)) (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups) (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (i : ℕ)

private theorem concatComparisonMap_eq_dite_consolidated284 (hi : i ≤ (s'.append t').length)
    (hlen : s'.length = s.length) (hi2 : i ≤ s'.length + t'.length) :
    concatComparisonMap g s t s' t' D D' i hi =
      (if h : i ≤ s'.length then
        eqToHom (append_schemeAt_of_le_length s' t' h) ≫ eqToHom (toSequenceOfBlowups_schemeAt s' i).symm ≫
          D.comp i (h.trans_eq (toSequenceOfBlowups_length s').symm) ≫ eqToHom (toSequenceOfBlowups_schemeAt s i) ≫
            eqToHom (append_schemeAt_of_le_length s t (show i ≤ s.length by omega)).symm
      else
        (s'.concatObjIsoRight t' (i - s'.length) i (by omega)).hom ≫
          eqToHom (toSequenceOfBlowups_schemeAt t' (i - s'.length)).symm ≫
            D'.comp (i - s'.length)
                ((show i - s'.length ≤ t'.length by omega).trans_eq (toSequenceOfBlowups_length t').symm) ≫
              eqToHom (toSequenceOfBlowups_schemeAt t (i - s'.length)) ≫
                (s.concatObjIsoRight t (i - s'.length) i (by omega)).inv) :=
  rfl

private theorem append_center_eq_comap_concatComparisonMap_consolidated284 (hi : i < (s'.append t').length) :
    (s'.append t').center i =
      ((s.append t).center i).comap (concatComparisonMap g s t s' t' D D' i hi.le) := by
  have hlen : s'.length = s.length :=
    (toSequenceOfBlowups_length s').symm.trans (D.length_eq.trans (toSequenceOfBlowups_length s))
  have hilt : i < s'.length + t'.length := hi
  rw [concatComparisonMap_eq_dite_consolidated284 g s t s' t' D D' i hi.le hlen hilt.le]
  by_cases h : i ≤ s'.length
  · rw [dif_pos h]
    rcases h.lt_or_eq with hlt | heq
    · have hs : i < s.length := hlt.trans_eq hlen
      have hlt' : i < s'.toSequenceOfBlowups.length := hlt.trans_eq (toSequenceOfBlowups_length s').symm
      have hJ : s'.center i = (s.center i).comap (D.comp i hlt'.le) :=
        (toSequenceOfBlowups_center s' i).symm.trans
          ((D.center_eq i hlt').trans
            (congrArg (fun I : (s.toSequenceOfBlowups.schemeAt i).IdealSheafData => I.comap (D.comp i hlt'.le))
              (toSequenceOfBlowups_center s i)))
      rw [append_center_of_lt_length s' t' hlt, append_center_of_lt_length s t hs]
      refine comap_eqToHom_eq_comap_of_eq_comap_consolidated284 (append_schemeAt_of_le_length s' t' hlt.le)
        (append_schemeAt_of_le_length s t hs.le) (D.comp i hlt'.le) _ ?_ _ _ hJ
      exact eqToHom_trans_comp_comp_eqToHom_trans_consolidated284 _ _ _ _ _ _ _
    · subst heq
      have h0 : (0 : ℕ) < t'.toSequenceOfBlowups.length := by
        rw [toSequenceOfBlowups_length]
        omega
      have hz1 : t.toSequenceOfBlowups.isoZero.hom = t.isoZero.hom :=
        congrArg (fun e : t.toSequenceOfBlowups.schemeAt 0 ≅ s.obj s.length => e.hom) (toSequenceOfBlowups_isoObjZero t)
      have hz2 : t'.toSequenceOfBlowups.isoZero.hom = t'.isoZero.hom :=
        congrArg (fun e : t'.toSequenceOfBlowups.schemeAt 0 ≅ s'.obj s'.length => e.hom) (toSequenceOfBlowups_isoObjZero t')
      have hz : D'.comp 0 h0.le ≫ t.isoZero.hom = t'.isoZero.hom ≫ D.lastMap := by
        rw [← hz1, ← hz2]
        exact D'.comp_zero
      have hc0 : t'.center 0 = (t.center 0).comap (D'.comp 0 h0.le) :=
        (toSequenceOfBlowups_center t' 0).symm.trans
          ((D'.center_eq 0 h0).trans
            (congrArg (fun I : (t.toSequenceOfBlowups.schemeAt 0).IdealSheafData => I.comap (D'.comp 0 h0.le))
              (toSequenceOfBlowups_center t 0)))
      obtain ⟨u, hzu, hcu⟩ : ∃ u : t'.obj 0 ⟶ t.obj 0,
          u ≫ t.isoZero.hom = t'.isoZero.hom ≫ D.lastMap ∧
            t'.center 0 = (t.center 0).comap u :=
        ⟨D'.comp 0 h0.le, hz, hc0⟩
      have hJ : (t'.center 0).comap t'.isoZero.inv =
          ((t.center 0).comap t.isoZero.inv).comap D.lastMap :=
        comap_iso_inv_eq_comap_of_comm_sq_consolidated284 u t'.isoZero t.isoZero D.lastMap hzu (t'.center 0)
          (t.center 0) hcu
      rw [append_center_of_eq_length_consolidated284 s' t' s'.length rfl,
        append_center_of_eq_length_consolidated284 s t s'.length hlen]
      refine comap_eqToHom_eq_comap_of_eq_comap_consolidated284 (append_schemeAt_eq_last_of_eq_length s' t' rfl)
        (append_schemeAt_eq_last_of_eq_length s t hlen) D.lastMap _ ?_ _ _ hJ
      rw [StrictPullbackBlowupSeq.lastMap_eq]
      exact eqToHom_trans_comp_comp_eqToHom_trans_eq_assoc_consolidated284 _ _ _ _ _ _ _ _
  · rw [dif_neg h]
    have hk1 : i = s'.length + (i - s'.length) := by omega
    have hk2 : i = s.length + (i - s'.length) := by omega
    have hk : i - s'.length < t'.toSequenceOfBlowups.length := by
      rw [toSequenceOfBlowups_length]
      omega
    have hJ : t'.center (i - s'.length) =
        (t.center (i - s'.length)).comap (D'.comp (i - s'.length) hk.le) :=
      (toSequenceOfBlowups_center t' (i - s'.length)).symm.trans
        ((D'.center_eq (i - s'.length) hk).trans
          (congrArg
            (fun I : (t.toSequenceOfBlowups.schemeAt (i - s'.length)).IdealSheafData =>
              I.comap (D'.comp (i - s'.length) hk.le))
            (toSequenceOfBlowups_center t (i - s'.length))))
    rw [append_center_eq_comap_concatObjIsoRight s' t' (i - s'.length) i hk1,
      append_center_eq_comap_concatObjIsoRight s t (i - s'.length) i hk2]
    exact comap_eq_comap_iso_hom_of_eq_comap_consolidated284 (s'.concatObjIsoRight t' (i - s'.length) i hk1).hom
      (s.concatObjIsoRight t (i - s'.length) i hk2) (D'.comp (i - s'.length) hk.le)
      (t'.center (i - s'.length)) (t.center (i - s'.length)) hJ
      (toSequenceOfBlowups_schemeAt t' (i - s'.length)).symm (toSequenceOfBlowups_schemeAt t (i - s'.length))


end

end BlowupSequenceData

namespace StrictPullbackBlowupSeq

def concat {X' X : Scheme.{u}} {g : X' ⟶ X} (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData (s'.obj s'.length))
    (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) :
    StrictPullbackBlowupSeq g (s'.append t').toSequenceOfBlowups (s.append t).toSequenceOfBlowups :=
  BlowupSequenceData.toStrictPullbackSeq g (s'.append t') (s.append t)
    (BlowupSequenceData.append_length_eq_of_strictPullbackBlowupSeq g s t s' t' D D')
    (BlowupSequenceData.concatComparisonMap g s t s' t' D D')
    (BlowupSequenceData.concatComparisonMap_zero_comp_isoObjZero_consolidated284 g s t s' t' D D')
    (BlowupSequenceData.isPullback_concatComparisonMap_consolidated284 g s t s' t' D D')
    (BlowupSequenceData.append_center_eq_comap_concatComparisonMap_consolidated284 g s t s' t' D D')

end StrictPullbackBlowupSeq

theorem isStrictPullbackBlowupSeq_append {X' X : Scheme.{u}} {g : X' ⟶ X} (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData (s'.obj s'.length))
    (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq g (s'.append t').toSequenceOfBlowups (s.append t).toSequenceOfBlowups :=
  (StrictPullbackBlowupSeq.concat s t s' t' D D').isStrictPullback

theorem emptyMarkedBlowupSequenceData_toBlowupSequenceData {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) :
    (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData = BlowupSequenceData.empty X :=
  emptyMarkedBlowupSequenceData_toBlowupSequenceData_eq p I m E

namespace MarkedBlowupSequenceData

section
variable {k : Type u} [Field k]

theorem emptyMarkedBlowupSequenceData_append_isomorphic {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData)
    (t : MarkedBlowupSequenceData
      ((emptyMarkedBlowupSequenceData p I m E).proj (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length ≫ p)
      ((emptyMarkedBlowupSequenceData p I m E).ideal (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length) m
      ((emptyMarkedBlowupSequenceData p I m E).boundary (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length))
    (hinv : ComapIsoInvariance.{u}) :
    ((emptyMarkedBlowupSequenceData p I m E).append t hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups.Isomorphic
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have h0 : (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length = 0 :=
    emptyMarkedBlowupSequenceData_length p I m E
  have hpf : ∀ i : ℕ, i = (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length + i := by
    intro i
    omega
  have hlen : ((emptyMarkedBlowupSequenceData p I m E).append t hinv).toBlowupSequenceData.length
      = t.toBlowupSequenceData.length := by
    have h1 : ((emptyMarkedBlowupSequenceData p I m E).append t hinv).toBlowupSequenceData.length
        = (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length + t.toBlowupSequenceData.length :=
      MarkedBlowupSequenceData.append_length _ _ hinv
    omega
  have hzero : ((emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.concatObjIsoRight t.toBlowupSequenceData 0 0
        (hpf 0)).hom ≫ t.toBlowupSequenceData.isoZero.hom
      = eqToHom (BlowupSequenceData.append_schemeAt_eq_last_of_eq_length (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData
          t.toBlowupSequenceData h0.symm) := by
    rw [BlowupSequenceData.concatObjIsoRight_hom_zero_consolidated284, Category.assoc, Iso.inv_hom_id]
    exact Category.comp_id _
  refine BlowupSequenceData.toSequenceOfBlowups_isomorphic_of_iso
    ((emptyMarkedBlowupSequenceData p I m E).append t hinv).toBlowupSequenceData t.toBlowupSequenceData hlen
    (fun i _ => (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.concatObjIsoRight t.toBlowupSequenceData i i
      (hpf i)) ?_ ?_ ?_
  · exact hzero.trans (Category.comp_id _).symm
  · intro i _
    exact (BlowupSequenceData.concatObjIsoRight_hom_comm_blowupMorphism (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData t.toBlowupSequenceData
      i i (hpf i)).symm
  · intro i _
    exact (BlowupSequenceData.append_center_eq_comap_concatObjIsoRight (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData
      t.toBlowupSequenceData i i (hpf i)).symm

theorem append_isomorphic_of_length_eq_zero {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (S : MarkedBlowupSequenceData p I m E)
    (T : MarkedBlowupSequenceData (S.proj S.toBlowupSequenceData.length ≫ p) (S.ideal S.toBlowupSequenceData.length) m
      (S.boundary S.toBlowupSequenceData.length))
    (hinv : ComapIsoInvariance.{u}) (h : T.toBlowupSequenceData.length = 0) :
    ((S.append T hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups).Isomorphic S.toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have hlen : (S.toBlowupSequenceData.append T.toBlowupSequenceData).length = S.toBlowupSequenceData.length := by
    rw [BlowupSequenceData.append_length, h, Nat.add_zero]
  have key : (S.toBlowupSequenceData.append T.toBlowupSequenceData).toSequenceOfBlowups.Isomorphic S.toBlowupSequenceData.toSequenceOfBlowups := by
    refine BlowupSequenceData.toSequenceOfBlowups_isomorphic_of_iso (S.toBlowupSequenceData.append T.toBlowupSequenceData) S.toBlowupSequenceData
      hlen
      (fun i hi => eqToIso (BlowupSequenceData.append_schemeAt_of_le_length S.toBlowupSequenceData T.toBlowupSequenceData
        (hi.trans_eq hlen))) ?_ ?_ ?_
    · simp only [eqToIso.hom]
      rw [BlowupSequenceData.append_isoObjZero_hom]
    · intro i hi
      have hilt : i < S.toBlowupSequenceData.length := lt_of_lt_of_eq hi hlen
      simp only [eqToIso.hom]
      rw [BlowupSequenceData.append_blowupMorphism_of_lt_length S.toBlowupSequenceData T.toBlowupSequenceData hilt]
      simp
    · intro i hi
      have hilt : i < S.toBlowupSequenceData.length := lt_of_lt_of_eq hi hlen
      simp only [eqToIso.hom]
      rw [BlowupSequenceData.append_center_of_lt_length S.toBlowupSequenceData T.toBlowupSequenceData hilt]
  have e1 : (S.append T hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      = (S.toBlowupSequenceData.append T.toBlowupSequenceData).toSequenceOfBlowups :=
    MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups (S.append T hinv)
  have e2 : S.toMarkedSequenceOfBlowups.toSequenceOfBlowups = S.toBlowupSequenceData.toSequenceOfBlowups :=
    MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups S
  rw [e1, e2]
  exact key

theorem isStrictPullbackBlowupSeq_append {X' X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {p' : X' ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {I' : X'.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} {E' : List X'.IdealSheafData} (g : X' ⟶ X)
    (S : MarkedBlowupSequenceData p I m E)
    (T : MarkedBlowupSequenceData (S.proj S.toBlowupSequenceData.length ≫ p) (S.ideal S.toBlowupSequenceData.length) m
      (S.boundary S.toBlowupSequenceData.length))
    (S' : MarkedBlowupSequenceData p' I' m E')
    (T' : MarkedBlowupSequenceData (S'.proj S'.toBlowupSequenceData.length ≫ p')
      (S'.ideal S'.toBlowupSequenceData.length) m (S'.boundary S'.toBlowupSequenceData.length))
    (hinv : ComapIsoInvariance.{u})
    (D : StrictPullbackBlowupSeq g S'.toMarkedSequenceOfBlowups.toSequenceOfBlowups S.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap T'.toMarkedSequenceOfBlowups.toSequenceOfBlowups T.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq g ((S'.append T' hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups)
      ((S.append T hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  exact _root_.FunctorialResolution.EmbeddedResolution.isStrictPullbackBlowupSeq_append (g := g) S.toBlowupSequenceData T.toBlowupSequenceData
    S'.toBlowupSequenceData T'.toBlowupSequenceData D D'


end

end MarkedBlowupSequenceData


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.AppendIsomorphism
section



namespace BlowupSequenceData

private noncomputable def appendSchemeAtIsoOfLengthLt {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t₁ t₂ : BlowupSequenceData (s.obj s.length))
    (e : ∀ i : ℕ, i ≤ t₁.length → (t₁.obj i ≅ t₂.obj i))
    (j i : ℕ) (hij : i = s.length + j) (hj : 0 < j) (hjl : j ≤ t₁.length) :
    (s.append t₁).obj i ≅ (s.append t₂).obj i :=
  eqToIso (append_schemeAt_eq_right_of_pos s t₁ hj hij) ≪≫ e j hjl ≪≫
    (eqToIso (append_schemeAt_eq_right_of_pos s t₂ hj hij)).symm

section
variable {X : Scheme.{u}} (s : BlowupSequenceData X) (t₁ t₂ : BlowupSequenceData (s.obj s.length)) (e : ∀ i : ℕ, i ≤ t₁.length → (t₁.obj i ≅ t₂.obj i))

private theorem appendObjIsoRight_hom_consolidated304 (j i : ℕ) (hij : i = s.length + j) (hj : 0 < j) (hjl : j ≤ t₁.length) :
    (appendSchemeAtIsoOfLengthLt s t₁ t₂ e j i hij hj hjl).hom =
      eqToHom (append_schemeAt_eq_right_of_pos s t₁ hj hij) ≫ (e j hjl).hom ≫
        eqToHom (append_schemeAt_eq_right_of_pos s t₂ hj hij).symm := rfl

private theorem appendObjIsoRight_congr_consolidated304 (j j' i : ℕ) (h : j = j')
    (hij : i = s.length + j) (hj : 0 < j) (hjl : j ≤ t₁.length)
    (hij' : i = s.length + j') (hj' : 0 < j') (hjl' : j' ≤ t₁.length) :
    appendSchemeAtIsoOfLengthLt s t₁ t₂ e j i hij hj hjl = appendSchemeAtIsoOfLengthLt s t₁ t₂ e j' i hij' hj' hjl' := by
  subst h
  rfl


end

private noncomputable def appendSchemeAtIso {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t₁ t₂ : BlowupSequenceData (s.obj s.length))
    (e : ∀ i : ℕ, i ≤ t₁.length → (t₁.obj i ≅ t₂.obj i))
    (i : ℕ) (hi : i ≤ s.length + t₁.length) :
    (s.append t₁).obj i ≅ (s.append t₂).obj i :=
  if h : i ≤ s.length then
    eqToIso ((append_schemeAt_of_le_length s t₁ h).trans (append_schemeAt_of_le_length s t₂ h).symm)
  else
    appendSchemeAtIsoOfLengthLt s t₁ t₂ e (i - s.length) i (by omega) (by omega) (by omega)

section
variable {X : Scheme.{u}} (s : BlowupSequenceData X) (t₁ t₂ : BlowupSequenceData (s.obj s.length))

private theorem appendObjIso_hom_of_le_consolidated304 (e : ∀ i : ℕ, i ≤ t₁.length → (t₁.obj i ≅ t₂.obj i))
    (i : ℕ) (h : i ≤ s.length) (hi : i ≤ s.length + t₁.length) :
    (appendSchemeAtIso s t₁ t₂ e i hi).hom =
      eqToHom ((append_schemeAt_of_le_length s t₁ h).trans (append_schemeAt_of_le_length s t₂ h).symm) := by
  unfold appendSchemeAtIso
  simp only [dif_pos h, eqToIso.hom]

private theorem appendObjIso_eq_right_of_pos_consolidated304 (e : ∀ i : ℕ, i ≤ t₁.length → (t₁.obj i ≅ t₂.obj i))
    (i j : ℕ) (hij : i = s.length + j) (hj : 0 < j) (hjl : j ≤ t₁.length)
    (hi : i ≤ s.length + t₁.length) :
    appendSchemeAtIso s t₁ t₂ e i hi = appendSchemeAtIsoOfLengthLt s t₁ t₂ e j i hij hj hjl := by
  have hne : ¬ i ≤ s.length := by omega
  unfold appendSchemeAtIso
  rw [dif_neg hne]
  exact appendObjIsoRight_congr_consolidated304 s t₁ t₂ e (i - s.length) j i (by omega) (by omega) (by omega)
    (by omega) hij hj hjl

theorem append_isomorphic_of_iso (hlen : t₁.length = t₂.length)
    (e : ∀ i : ℕ, i ≤ t₁.length → (t₁.obj i ≅ t₂.obj i))
    (hzero : (e 0 (Nat.zero_le _)).hom ≫ t₂.isoZero.hom = t₁.isoZero.hom)
    (hmap : ∀ (i : ℕ) (hi : i < t₁.length),
      (e (i + 1) hi).hom ≫ t₂.map i = t₁.map i ≫ (e i hi.le).hom)
    (hcenter : ∀ (i : ℕ) (hi : i < t₁.length),
      (t₂.center i).comap (e i hi.le).hom = t₁.center i) :
    (s.append t₁).toSequenceOfBlowups.Isomorphic (s.append t₂).toSequenceOfBlowups := by
  have hlenc : (s.append t₁).length = (s.append t₂).length := by
    rw [append_length, append_length, hlen]
  refine toSequenceOfBlowups_isomorphic_of_iso (s.append t₁) (s.append t₂) hlenc
    (fun i hi => appendSchemeAtIso s t₁ t₂ e i (hi.trans_eq (append_length s t₁))) ?_ ?_ ?_
  · simp only [appendObjIso_hom_of_le_consolidated304 s t₁ t₂ e 0 (Nat.zero_le s.length), append_isoObjZero_hom,
      eqToHom_trans_assoc]
  · intro i hi
    have hi' : i < s.length + t₁.length := hi.trans_eq (append_length s t₁)
    rcases lt_trichotomy i s.length with hlt | heq | hgt
    · have h1 : i + 1 ≤ s.length := by omega
      simp only [appendObjIso_hom_of_le_consolidated304 s t₁ t₂ e (i + 1) h1, appendObjIso_hom_of_le_consolidated304 s t₁ t₂ e i hlt.le,
        append_blowupMorphism_of_lt_length s t₂ hlt, append_blowupMorphism_of_lt_length s t₁ hlt,
        Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    · subst heq
      have h0lt : 0 < t₁.length := by omega
      have h1le : 1 ≤ t₁.length := by omega
      have hm0 : (e 1 h1le).hom ≫ t₂.map 0 = t₁.map 0 ≫ (e 0 (Nat.zero_le _)).hom :=
        hmap 0 h0lt
      simp only [appendObjIso_eq_right_of_pos_consolidated304 s t₁ t₂ e (s.length + 1) 1 rfl Nat.one_pos h1le, appendObjIsoRight_hom_consolidated304,
        appendObjIso_hom_of_le_consolidated304 s t₁ t₂ e s.length le_rfl, append_blowupMorphism_length,
        Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [reassoc_of% hm0, reassoc_of% hzero]
    · have hj1 : 0 < i - s.length := by omega
      have hj2 : i - s.length ≤ t₁.length := by omega
      have hj3 : i - s.length < t₁.length := by omega
      simp only [appendObjIso_eq_right_of_pos_consolidated304 s t₁ t₂ e (i + 1) (i - s.length + 1) (by omega) (by omega) (by omega),
        appendObjIso_eq_right_of_pos_consolidated304 s t₁ t₂ e i (i - s.length) (by omega) hj1 hj2, appendObjIsoRight_hom_consolidated304,
        append_blowupMorphism_of_length_lt s t₂ hgt, append_blowupMorphism_of_length_lt s t₁ hgt,
        Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [reassoc_of% (hmap (i - s.length) hj3)]
  · intro i hi
    have hi' : i < s.length + t₁.length := hi.trans_eq (append_length s t₁)
    rcases lt_trichotomy i s.length with hlt | heq | hgt
    · simp only [appendObjIso_hom_of_le_consolidated304 s t₁ t₂ e i hlt.le, append_center_of_lt_length s t₂ hlt,
        append_center_of_lt_length s t₁ hlt, ← Scheme.IdealSheafData.comap_comp, eqToHom_trans]
    · subst heq
      have h0lt : 0 < t₁.length := by omega
      have hz2 : t₁.isoZero.inv ≫ (e 0 (Nat.zero_le _)).hom = t₂.isoZero.inv := by
        rw [Iso.inv_comp_eq, ← hzero, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      simp only [appendObjIso_hom_of_le_consolidated304 s t₁ t₂ e s.length le_rfl, append_center_length,
        ← Scheme.IdealSheafData.comap_comp, eqToHom_trans_assoc]
      rw [← hcenter 0 h0lt]
      simp only [← Scheme.IdealSheafData.comap_comp, Category.assoc, hz2]
    · have hj1 : 0 < i - s.length := by omega
      have hj2 : i - s.length ≤ t₁.length := by omega
      have hj3 : i - s.length < t₁.length := by omega
      simp only [appendObjIso_eq_right_of_pos_consolidated304 s t₁ t₂ e i (i - s.length) (by omega) hj1 hj2, appendObjIsoRight_hom_consolidated304,
        append_center_of_length_lt s t₂ hgt, append_center_of_length_lt s t₁ hgt,
        ← Scheme.IdealSheafData.comap_comp,
        Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      rw [← hcenter (i - s.length) hj3]
      simp only [← Scheme.IdealSheafData.comap_comp]

theorem append_isomorphic_of_isomorphic (h : t₁.toSequenceOfBlowups.Isomorphic t₂.toSequenceOfBlowups) :
    (s.append t₁).toSequenceOfBlowups.Isomorphic (s.append t₂).toSequenceOfBlowups := by
  obtain ⟨hlen, e, hzero, hmap, hcenter⟩ := h
  have hl1 : t₁.toSequenceOfBlowups.length = t₁.length := toSequenceOfBlowups_length t₁
  have hl2 : t₂.toSequenceOfBlowups.length = t₂.length := toSequenceOfBlowups_length t₂
  refine append_isomorphic_of_iso s t₁ t₂ (by omega) (fun i hi => e i (by omega)) ?_ ?_ ?_
  · rw [← toSequenceOfBlowups_isoObjZero t₂, ← toSequenceOfBlowups_isoObjZero t₁]
    exact hzero
  · intro i hi
    rw [← toSequenceOfBlowups_blowupMorphism t₂ i, ← toSequenceOfBlowups_blowupMorphism t₁ i]
    exact hmap i (by omega)
  · intro i hi
    rw [← toSequenceOfBlowups_center t₂ i, ← toSequenceOfBlowups_center t₁ i]
    exact hcenter i (by omega)


end

end BlowupSequenceData

namespace MarkedBlowupSequenceData

theorem append_isomorphic_of_isomorphic {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (S : MarkedBlowupSequenceData p I m E)
    (T₁ T₂ : MarkedBlowupSequenceData (S.proj S.length ≫ p) (S.ideal S.length) m (S.boundary S.length))
    (hinv : ComapIsoInvariance.{u})
    (h : T₁.toMarkedSequenceOfBlowups.toSequenceOfBlowups.Isomorphic T₂.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    ((S.append T₁ hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups).Isomorphic
      ((S.append T₂ hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  rw [toMarkedSequence_toSequenceOfBlowups, toMarkedSequence_toSequenceOfBlowups] at h
  have key := BlowupSequenceData.append_isomorphic_of_isomorphic S.toBlowupSequenceData T₁.toBlowupSequenceData
    T₂.toBlowupSequenceData h
  rw [toMarkedSequence_toSequenceOfBlowups, toMarkedSequence_toSequenceOfBlowups, append_toBlowupSequenceData,
    append_toBlowupSequenceData]
  exact key

end MarkedBlowupSequenceData

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
section



private theorem transitionMap_self_consolidated128 {X : Scheme.{u}} (u : SequenceOfBlowups X) {a : ℕ}
    (h : a ≤ a) : u.transitionMap h = 𝟙 (u.schemeAt a) := by
  have h0 : (CategoryTheory.homOfLE h).op = 𝟙 (Opposite.op a) := rfl
  rw [u.transitionMap_def, h0, CategoryTheory.Functor.map_id]

section
variable {X : Scheme.{u}} (s t : SequenceOfBlowups X) (L : ℕ) (e : ∀ i : ℕ, i ≤ L → (s.schemeAt i ≅ t.schemeAt i)) (hstep : ∀ i : ℕ, ∀ hi : i < L, (e (i + 1) hi).hom ≫ t.transitionMapSucc i = s.transitionMapSucc i ≫ (e i hi.le).hom)
include hstep

theorem SequenceOfBlowups.iso_hom_comp_transitionMap :
    ∀ a b : ℕ, ∀ hab : a ≤ b, ∀ hb : b ≤ L,
      (e b hb).hom ≫ t.transitionMap hab = s.transitionMap hab ≫ (e a (hab.trans hb)).hom := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base =>
      intro hb
      have ht : t.transitionMap (le_refl a) = 𝟙 (t.schemeAt a) := transitionMap_self_consolidated128 t (le_refl a)
      have hs : s.transitionMap (le_refl a) = 𝟙 (s.schemeAt a) := transitionMap_self_consolidated128 s (le_refl a)
      rw [ht, hs, Category.comp_id, Category.id_comp]
  | succ n hn ih =>
      intro hb
      have hn' : n ≤ L := Nat.le_of_succ_le hb
      have h1 : n ≤ n + 1 := Nat.le_succ n
      rw [← t.transitionMap_trans hn h1, ← s.transitionMap_trans hn h1, ← t.blowupMorphism_eq_transitionMap n,
        ← s.blowupMorphism_eq_transitionMap n, ← Category.assoc, hstep n hb, Category.assoc, ih hn']
      simp

theorem SequenceOfBlowups.iso_hom_comp_projectionToBase (hzero : (e 0 (Nat.zero_le _)).hom ≫ t.isoZero.hom = s.isoZero.hom) :
    ∀ b : ℕ, ∀ hb : b ≤ L, (e b hb).hom ≫ t.projectionToBase b = s.projectionToBase b := by
  intro b hb
  have hd := FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.iso_hom_comp_transitionMap s t L e hstep 0 b (Nat.zero_le b) hb
  have h0 : (e 0 ((Nat.zero_le b).trans hb)).hom ≫ t.isoZero.hom = s.isoZero.hom := hzero
  rw [FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_def, FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_def, ← Category.assoc,
    hd, Category.assoc, h0]


end

section
variable {X' X : Scheme.{u}}

theorem isPullback_transitionMap_of_isPullback_blowupMorphism (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (L : ℕ)
    (σ : ∀ i : ℕ, i ≤ L → (t.schemeAt i ⟶ s.schemeAt i))
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      IsPullback (σ (i + 1) hi) (t.transitionMapSucc i) (s.transitionMapSucc i) (σ i hi.le)) :
    ∀ a b : ℕ, ∀ hab : a ≤ b, ∀ hb : b ≤ L,
      IsPullback (σ b hb) (t.transitionMap hab) (s.transitionMap hab) (σ a (hab.trans hb)) := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base =>
      intro hb
      rw [transitionMap_self_consolidated128, transitionMap_self_consolidated128]
      exact (IsPullback.of_horiz_isIso ⟨by simp⟩).flip
  | succ b hab ih =>
      intro hb
      have hlt : b < L := hb
      have key := (hstep b hlt).paste_vert (ih hlt.le)
      have e₁ : t.transitionMapSucc b ≫ t.transitionMap hab = t.transitionMap (hab.trans (Nat.le_succ b)) := by
        rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_trans]
      have e₂ : s.transitionMapSucc b ≫ s.transitionMap hab = s.transitionMap (hab.trans (Nat.le_succ b)) := by
        rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_trans]
      rw [e₁, e₂] at key
      exact key

theorem isPullback_projectionToBase_of_isPullback_blowupMorphism (g : X' ⟶ X)
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (L : ℕ)
    (σ : ∀ i : ℕ, i ≤ L → (t.schemeAt i ⟶ s.schemeAt i))
    (hzero : σ 0 (Nat.zero_le _) ≫ s.isoZero.hom = t.isoZero.hom ≫ g)
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      IsPullback (σ (i + 1) hi) (t.transitionMapSucc i) (s.transitionMapSucc i) (σ i hi.le)) :
    ∀ b : ℕ, ∀ hb : b ≤ L,
      IsPullback (σ b hb) (t.projectionToBase b) (s.projectionToBase b) g := by
  intro b hb
  have hA := isPullback_transitionMap_of_isPullback_blowupMorphism t s L σ hstep 0 b (Nat.zero_le b) hb
  have hsq : CommSq t.isoZero.hom (σ 0 ((Nat.zero_le b).trans hb)) g s.isoZero.hom :=
    ⟨hzero.symm⟩
  have hB : IsPullback (σ 0 ((Nat.zero_le b).trans hb)) t.isoZero.hom s.isoZero.hom g :=
    (IsPullback.of_horiz_isIso hsq).flip
  rw [t.projectionToBase_def b, s.projectionToBase_def b]
  exact hA.paste_vert hB

theorem surjective_of_isPullback_blowupMorphism (g : X' ⟶ X)
    [AlgebraicGeometry.Surjective g]
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (L : ℕ)
    (σ : ∀ i : ℕ, i ≤ L → (t.schemeAt i ⟶ s.schemeAt i))
    (hzero : σ 0 (Nat.zero_le _) ≫ s.isoZero.hom = t.isoZero.hom ≫ g)
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      IsPullback (σ (i + 1) hi) (t.transitionMapSucc i) (s.transitionMapSucc i) (σ i hi.le)) :
    ∀ i : ℕ, ∀ hi : i ≤ L, AlgebraicGeometry.Surjective (σ i hi) := by
  intro i hi
  have hsq : IsPullback (σ i hi) (t.projectionToBase i) (s.projectionToBase i) g :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism g t s L σ hzero hstep i hi
  have hg : AlgebraicGeometry.Surjective g := inferInstance
  exact MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) hsq.flip hg


end

namespace IsStrictPullbackBlowupSeq

theorem comp {X'' X' X : Scheme.{u}} {ψ : X'' ⟶ X'} {φ : X' ⟶ X}
    {u : SequenceOfBlowups X''} {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (hu : IsStrictPullbackBlowupSeq ψ u t) (ht : IsStrictPullbackBlowupSeq φ t s) :
    IsStrictPullbackBlowupSeq (ψ ≫ φ) u s := by
  obtain ⟨hl1, σ, hz1, hp1, hc1⟩ := hu
  obtain ⟨hl2, τ, hz2, hp2, hc2⟩ := ht
  have hle : ∀ i : ℕ, i ≤ u.length → i ≤ t.length := fun i hi => by omega
  have hlt : ∀ i : ℕ, i < u.length → i < t.length := fun i hi => by omega
  refine ⟨hl1.trans hl2, fun i hi => σ i hi ≫ τ i (hle i hi), ?_, ?_, ?_⟩
  · rw [Category.assoc, hz2, ← Category.assoc, hz1, Category.assoc]
  · intro i hi
    exact (hp1 i hi).paste_horiz (hp2 i (hlt i hi))
  · intro i hi
    rw [hc1 i hi, hc2 i (hlt i hi)]
    simp [Scheme.IdealSheafData.comap_comp]

section
variable {X' X : Scheme.{u}} {g : X' ⟶ X}

theorem of_isomorphic_pullback {t t' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (he : t.Isomorphic t') :
    IsStrictPullbackBlowupSeq g t' s := by
  have hlen : t.length = s.length := h.1
  obtain ⟨σ, hzero, hpb, hcen⟩ := h.2
  have hlen' : t.length = t'.length := he.1
  obtain ⟨e, hezero, hestep, hecen⟩ := he.2
  have hconv : ∀ i : ℕ, i ≤ t'.length → i ≤ t.length := fun i hi => by omega
  refine ⟨hlen'.symm.trans hlen,
    fun i hi => (e i (hconv i hi)).inv ≫ σ i (hconv i hi), ?_, ?_, ?_⟩
  · have key : ((e 0 (hconv 0 (Nat.zero_le t'.length))).inv ≫
        σ 0 (hconv 0 (Nat.zero_le t'.length))) ≫ s.isoZero.hom = t'.isoZero.hom ≫ g := by
      rw [Category.assoc, hzero, Iso.inv_comp_eq, ← Category.assoc, hezero]
    exact key
  · intro i hi
    have hi' : i < t.length := by omega
    have hsq : CommSq (e (i + 1) hi').inv (t'.transitionMapSucc i) (t.transitionMapSucc i) (e i hi'.le).inv := by
      refine ⟨?_⟩
      rw [Iso.inv_comp_eq, ← Category.assoc, hestep i hi', Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    exact (IsPullback.of_horiz_isIso hsq).paste_horiz (hpb i hi')
  · intro i hi
    have hi' : i < t.length := by omega
    have key : t'.center i = (s.center i).comap ((e i hi'.le).inv ≫ σ i hi'.le) := by
      rw [Scheme.IdealSheafData.comap_comp, ← hcen i hi', ← hecen i hi',
        ← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]
    exact key

theorem of_isomorphic_base {t : SequenceOfBlowups X'} {s s' : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (he : s.Isomorphic s') :
    IsStrictPullbackBlowupSeq g t s' := by
  obtain ⟨hl1, σ, hz1, hp1, hc1⟩ := h
  obtain ⟨hl2, e, hz2, hp2, hc2⟩ := he
  have hle : ∀ i : ℕ, i ≤ t.length → i ≤ s.length := fun i hi => by omega
  have hlt : ∀ i : ℕ, i < t.length → i < s.length := fun i hi => by omega
  refine ⟨hl1.trans hl2, fun i hi => σ i hi ≫ (e i (hle i hi)).hom, ?_, ?_, ?_⟩
  · rw [Category.assoc, hz2]
    exact hz1
  · intro i hi
    refine (hp1 i hi).paste_horiz ?_
    exact IsPullback.of_horiz_isIso ⟨hp2 i (hlt i hi)⟩
  · intro i hi
    have h2 := hc2 i (hlt i hi)
    rw [hc1 i hi, ← h2]
    simp [Scheme.IdealSheafData.comap_comp]


end

section
variable {X : Scheme.{u}} (s : SequenceOfBlowups X)

private theorem projectionToBase_zero_consolidated128 :
    s.projectionToBase 0 = s.isoZero.hom := by
  rw [SequenceOfBlowups.projectionToBase_def, transitionMap_self_consolidated128 s (le_refl 0), Category.id_comp]

private theorem blowupMorphism_comp_projectionToBase_consolidated128 (i : ℕ) :
    s.transitionMapSucc i ≫ s.projectionToBase i = s.projectionToBase (i + 1) := by
  rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_comp_projectionToBase]


end

theorem isomorphic {X' X : Scheme.{u}} {g : X' ⟶ X}
    {t t' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (h' : IsStrictPullbackBlowupSeq g t' s) :
    t.Isomorphic t' := by
  obtain ⟨hl, σ, hz, hp, hc⟩ := h
  obtain ⟨hl', τ, hz', hp', hc'⟩ := h'
  have hlen : t.length ≤ t'.length := le_of_eq (hl.trans hl'.symm)
  have hA : ∀ i : ℕ, ∀ hi : i ≤ t.length,
      IsPullback (σ i hi) (t.projectionToBase i) (s.projectionToBase i) g :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism g t s t.length σ hz hp
  have hB : ∀ i : ℕ, ∀ hi : i ≤ t'.length,
      IsPullback (τ i hi) (t'.projectionToBase i) (s.projectionToBase i) g :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism g t' s t'.length τ hz' hp'
  have key : ∀ i : ℕ, ∀ hi : i ≤ t.length, ∃ e : t.schemeAt i ≅ t'.schemeAt i,
      e.hom ≫ τ i (hi.trans hlen) = σ i hi ∧ e.hom ≫ t'.projectionToBase i = t.projectionToBase i :=
    fun i hi =>
      ⟨(hA i hi).isoIsPullback _ _ (hB i (hi.trans hlen)),
        (hA i hi).isoIsPullback_hom_fst _ _ (hB i (hi.trans hlen)),
        (hA i hi).isoIsPullback_hom_snd _ _ (hB i (hi.trans hlen))⟩
  choose e he1 he2 using key
  refine ⟨hl.trans hl'.symm, e, ?_, ?_, ?_⟩
  · have h0 := he2 0 (Nat.zero_le t.length)
    rwa [projectionToBase_zero_consolidated128 t', projectionToBase_zero_consolidated128 t] at h0
  · intro i hi
    have hi2 : i < t'.length := lt_of_lt_of_le hi hlen
    refine (hB i (hi.le.trans hlen)).hom_ext ?_ ?_
    · have w1 : τ (i + 1) hi2 ≫ s.transitionMapSucc i = t'.transitionMapSucc i ≫ τ i hi2.le :=
        (hp' i hi2).w
      have w2 : σ (i + 1) hi ≫ s.transitionMapSucc i = t.transitionMapSucc i ≫ σ i hi.le := (hp i hi).w
      rw [Category.assoc, Category.assoc, ← w1, he1 i hi.le, ← Category.assoc,
        he1 (i + 1) hi]
      exact w2
    · rw [Category.assoc, Category.assoc, blowupMorphism_comp_projectionToBase_consolidated128 t' i,
        he2 (i + 1) hi, he2 i hi.le, blowupMorphism_comp_projectionToBase_consolidated128 t i]
  · intro i hi
    have hi2 : i < t'.length := lt_of_lt_of_le hi hlen
    rw [hc' i hi2, hc i hi, ← he1 i hi.le]
    simp [Scheme.IdealSheafData.comap_comp]

section
variable {X' X : Scheme.{u}} {g : X' ⟶ X} {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (h : IsStrictPullbackBlowupSeq g t s)
include h

theorem center_eq_top (i : ℕ) (hi : i < s.length)
    (hs : s.center i = ⊤) : t.center i = ⊤ := by
  obtain ⟨hlen, σ, -, -, hcen⟩ := h
  have hi' : i < t.length := by omega
  rw [hcen i hi', hs, Scheme.IdealSheafData.comap_top]

theorem center_ne_top_of_forall_center_ne_top (ht : ∀ i : ℕ, i < t.length → t.center i ≠ ⊤) :
    ∀ i : ℕ, i < s.length → s.center i ≠ ⊤ := by
  obtain ⟨hlen, _, _, _, hcen⟩ := h
  intro i hi htop
  have hi' : i < t.length := by omega
  refine ht i hi' ?_
  rw [hcen i hi', htop]
  simp


end

private theorem idealSheafData_eq_top_of_comap_eq_top_consolidated128 {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [AlgebraicGeometry.Surjective f] (I : Z.IdealSheafData)
    (h : I.comap f = ⊤) : I = ⊤ := by
  refine (Scheme.IdealSheafData.support_eq_bot_iff I).mp ?_
  have hsup := Scheme.IdealSheafData.support_comap I f
  rw [h, Scheme.IdealSheafData.support_top] at hsup
  refine TopologicalSpace.Closeds.coe_eq_empty.mp (Set.eq_empty_of_forall_notMem ?_)
  intro z hz
  obtain ⟨y, hy⟩ := f.surjective z
  rw [← hy] at hz
  have h2 : y ∈ (⊥ : TopologicalSpace.Closeds ↥Y) := by
    rw [hsup]
    exact hz
  exact h2

theorem center_eq_top_iff {X' X : Scheme.{u}} {g : X' ⟶ X}
    [AlgebraicGeometry.Surjective g]
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (i : ℕ) (hi : i < s.length) :
    t.center i = ⊤ ↔ s.center i = ⊤ := by
  refine ⟨?_, fun hs => center_eq_top h i hi hs⟩
  intro ht
  obtain ⟨hlen, σ, hzero, hpb, hcen⟩ := h
  have hi' : i < t.length := by omega
  have hsurj : AlgebraicGeometry.Surjective (σ i hi'.le) :=
    surjective_of_isPullback_blowupMorphism g t s t.length σ hzero hpb i hi'.le
  have hc := hcen i hi'
  rw [ht] at hc
  exact idealSheafData_eq_top_of_comap_eq_top_consolidated128 (σ i hi'.le) (s.center i) hc.symm

end IsStrictPullbackBlowupSeq

end
end FunctorialResolution.EmbeddedResolution
end
