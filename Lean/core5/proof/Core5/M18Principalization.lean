import Mathlib
import Core5.M17DimensionRecursion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicGeometry
universe u v w
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.KrullDimEtaleBaseChange
section

open CategoryTheory.Limits TopologicalSpace


theorem krullDimSucc_eq_of_topologicalKrullDim_eq {V P : Scheme.{u}}
    (h : topologicalKrullDim ↥V = topologicalKrullDim ↥P) :
    krullDimSucc V = krullDimSucc P := by
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, h]

theorem ringKrullDim_stalk_opens (X : Scheme.{u}) (U : X.Opens) (x : U.toScheme) :
    ringKrullDim (U.toScheme.presheaf.stalk x) = ringKrullDim (X.presheaf.stalk (U.ι.base x)) := by
  have : IsIso (Scheme.Hom.stalkMap U.ι x) := inferInstance
  exact (ringKrullDim_eq_of_ringEquiv
    (asIso (Scheme.Hom.stalkMap U.ι x)).commRingCatIsoToRingEquiv).symm

private theorem isNoetherianRing_stalk_of_opens_consolidated201 {X : Scheme.{u}} (U : X.Opens)
    (y : U.toScheme) (h : IsNoetherianRing (X.presheaf.stalk (U.ι.base y))) :
    IsNoetherianRing (U.toScheme.presheaf.stalk y) := by
  have : IsIso (Scheme.Hom.stalkMap U.ι y) := inferInstance
  have := h
  exact isNoetherianRing_of_ringEquiv _
    (asIso (Scheme.Hom.stalkMap U.ι y)).commRingCatIsoToRingEquiv

section
variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [IsLocallyNoetherian X] {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
include c

theorem ringKrullDim_stalk_le_of_etaleChart_of_isLocallyNoetherian (x : X) (hx : x ∈ U) :
    ringKrullDim (X.presheaf.stalk x) ≤ ((m : ℕ∞) : WithBot ℕ∞) := by
  have := c.isEtale
  have : IsNoetherianRing (U.toScheme.presheaf.stalk (⟨x, hx⟩ : U.toScheme)) :=
    isNoetherianRing_stalk_of_opens_consolidated201 U _ inferInstance
  have h1 : ringKrullDim (U.toScheme.presheaf.stalk (⟨x, hx⟩ : U.toScheme))
      ≤ ((m : ℕ∞) : WithBot ℕ∞) :=
    ringKrullDim_stalk_le_of_etale_affineSpace c.map (⟨x, hx⟩ : U.toScheme)
  rw [ringKrullDim_stalk_opens X U (⟨x, hx⟩ : U.toScheme)] at h1
  exact h1

theorem etaleChart_dim_le_topologicalKrullDim (hU : IsAffineOpen U)
    (hne : (U : Set ↥X).Nonempty) :
    ((m : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim ↥X := by
  obtain ⟨x, hx, hcl⟩ := exists_mem_isClosed_singleton_of_isAffineOpen U hU hne
  have : IsAffine U.toScheme := hU
  have := c.isEtale
  have : IsNoetherianRing (U.toScheme.presheaf.stalk (⟨x, hx⟩ : U.toScheme)) :=
    isNoetherianRing_stalk_of_opens_consolidated201 U _ inferInstance
  have h1 : ringKrullDim (U.toScheme.presheaf.stalk (⟨x, hx⟩ : U.toScheme))
      = ((m : ℕ∞) : WithBot ℕ∞) :=
    ringKrullDim_stalk_eq_of_etale_affineSpace c.map (⟨x, hx⟩ : U.toScheme) hcl
  have h2 := ringKrullDim_stalk_opens X U (⟨x, hx⟩ : U.toScheme)
  have h3 := ringKrullDim_stalk_le_topologicalKrullDim X (U.ι.base (⟨x, hx⟩ : U.toScheme))
  calc ((m : ℕ∞) : WithBot ℕ∞)
      = ringKrullDim (U.toScheme.presheaf.stalk (⟨x, hx⟩ : U.toScheme)) := h1.symm
    _ = ringKrullDim (X.presheaf.stalk (U.ι.base (⟨x, hx⟩ : U.toScheme))) := h2
    _ ≤ topologicalKrullDim ↥X := h3


end

private theorem isField_of_formallyUnramified_consolidated201 (K : Type v) (D : Type w) [Field K]
    [CommRing D] [IsDomain D] [Algebra K D] [Algebra.EssFiniteType K D]
    [Algebra.FormallyUnramified K D] : IsField D := by
  have : Algebra.FormallyUnramified D (FractionRing D) :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors D)
  have : Algebra.EssFiniteType D (FractionRing D) :=
    Algebra.EssFiniteType.of_isLocalization (FractionRing D) (nonZeroDivisors D)
  have : Algebra.FormallyUnramified K (FractionRing D) :=
    Algebra.FormallyUnramified.comp K D (FractionRing D)
  have : Algebra.EssFiniteType K (FractionRing D) :=
    Algebra.EssFiniteType.comp K D (FractionRing D)
  have : Algebra.IsSeparable K (FractionRing D) :=
    (Algebra.FormallyUnramified.iff_isSeparable K (FractionRing D)).mp inferInstance
  have : Algebra.IsIntegral K D :=
    ⟨fun y => (Algebra.IsSeparable.isIntegral K (algebraMap D (FractionRing D) y)).tower_bot
      (IsFractionRing.injective D (FractionRing D))⟩
  exact isField_of_isIntegral_of_isField' (Field.toIsField K)

private theorem eq_bot_of_formallyUnramified_of_comap_le_consolidated201 (R : Type v) (D : Type w) [CommRing R]
    [CommRing D] [IsDomain D] [Algebra R D] [Algebra.EssFiniteType R D]
    [Algebra.FormallyUnramified R D]
    (p : Ideal R) (hp : p.IsPrime) (hker : ∀ r : R, algebraMap R D r = 0 ↔ r ∈ p)
    (Q : Ideal D) (hQ : Q.IsPrime) (hQc : ∀ r : R, algebraMap R D r ∈ Q → r ∈ p) :
    Q = ⊥ := by
  have := hp
  have := hQ
  have : IsDomain (R ⧸ p) := Ideal.Quotient.isDomain p
  obtain ⟨M, hMdef⟩ : ∃ M : Submonoid D, M = Submonoid.map (algebraMap R D) p.primeCompl :=
    ⟨_, rfl⟩
  have hmemM : ∀ r : R, r ∈ p.primeCompl → algebraMap R D r ∈ M := by
    intro r hr
    rw [hMdef]
    exact Submonoid.mem_map.mpr ⟨r, hr, rfl⟩
  have hMle : M ≤ nonZeroDivisors D := by
    intro z hz
    rw [hMdef] at hz
    obtain ⟨r, hr, rfl⟩ := Submonoid.mem_map.mp hz
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    exact hr ((hker r).mp h0)
  have : IsDomain (Localization M) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization M) hMle
  have : Algebra.FormallyUnramified D (Localization M) :=
    Algebra.FormallyUnramified.of_isLocalization M
  have : Algebra.EssFiniteType D (Localization M) :=
    Algebra.EssFiniteType.of_isLocalization (Localization M) M
  have : Algebra.FormallyUnramified R (Localization M) :=
    Algebra.FormallyUnramified.comp R D (Localization M)
  have : Algebra.EssFiniteType R (Localization M) :=
    Algebra.EssFiniteType.comp R D (Localization M)
  have hzero : ∀ a : R, a ∈ p → algebraMap R (Localization M) a = 0 := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply R D (Localization M) a, (hker a).mpr ha, map_zero]
  have hunits : ∀ z : nonZeroDivisors (R ⧸ p),
      IsUnit (Ideal.Quotient.lift p (algebraMap R (Localization M)) hzero (z : R ⧸ p)) := by
    rintro ⟨z, hz⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hne : (Ideal.Quotient.mk p r) ≠ 0 := nonZeroDivisors.ne_zero hz
    have hrp : r ∈ p.primeCompl := fun hmem => hne (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
    have h1 : Ideal.Quotient.lift p (algebraMap R (Localization M)) hzero
        (Ideal.Quotient.mk p r) = algebraMap D (Localization M) (algebraMap R D r) := by
      rw [Ideal.Quotient.lift_mk, IsScalarTower.algebraMap_apply R D (Localization M) r]
    rw [h1]
    exact IsLocalization.map_units (Localization M) ⟨algebraMap R D r, hmemM r hrp⟩
  let _ : Algebra (FractionRing (R ⧸ p)) (Localization M) :=
    RingHom.toAlgebra (IsLocalization.lift hunits : FractionRing (R ⧸ p) →+* Localization M)
  have : IsScalarTower R (FractionRing (R ⧸ p)) (Localization M) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    have h3 : algebraMap R (FractionRing (R ⧸ p)) r
        = algebraMap (R ⧸ p) (FractionRing (R ⧸ p)) (Ideal.Quotient.mk p r) :=
      IsScalarTower.algebraMap_apply R (R ⧸ p) (FractionRing (R ⧸ p)) r
    rw [h3, RingHom.algebraMap_toAlgebra, IsLocalization.lift_eq, Ideal.Quotient.lift_mk]
  have : Algebra.EssFiniteType (FractionRing (R ⧸ p)) (Localization M) :=
    Algebra.EssFiniteType.of_comp R (FractionRing (R ⧸ p)) (Localization M)
  have : Algebra.FormallyUnramified (FractionRing (R ⧸ p)) (Localization M) := by
    apply Algebra.FormallyUnramified.of_restrictScalars (R := R)
  have hfield : IsField (Localization M) :=
    isField_of_formallyUnramified_consolidated201 (FractionRing (R ⧸ p)) (Localization M)
  by_contra hQne
  obtain ⟨y, hyQ, hy0⟩ : ∃ y ∈ Q, y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hQne ((Submodule.eq_bot_iff Q).mpr hcon)
  have hdisj : Disjoint (M : Set D) ((Q : Set D)) := by
    rw [Set.disjoint_left]
    intro z hzM hzQ
    rw [hMdef] at hzM
    obtain ⟨r, hr, rfl⟩ := Submonoid.mem_map.mp hzM
    exact hr (hQc r hzQ)
  have hQP : (Q.map (algebraMap D (Localization M))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M (Localization M) Q hQ hdisj
  have hyL : algebraMap D (Localization M) y ≠ 0 := by
    intro h0
    refine hy0 (IsLocalization.injective (Localization M) hMle ?_)
    rw [h0, map_zero]
  obtain ⟨z, hz⟩ := hfield.mul_inv_cancel hyL
  have hmem : algebraMap D (Localization M) y ∈ Q.map (algebraMap D (Localization M)) :=
    Ideal.mem_map_of_mem _ hyQ
  have hone : (1 : Localization M) ∈ Q.map (algebraMap D (Localization M)) := by
    rw [← hz]
    exact Ideal.mul_mem_right z _ hmem
  exact hQP.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

section
variable (R : Type v) (S : Type w) [CommRing R] [CommRing S]

private theorem eq_of_le_of_comap_eq_consolidated201 [Algebra R S] [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    (q q' : Ideal S) (hq : q.IsPrime) (hq' : q'.IsPrime) (hle : q ≤ q')
    (hc : q.comap (algebraMap R S) = q'.comap (algebraMap R S)) : q = q' := by
  have := hq
  have := hq'
  have : IsDomain (S ⧸ q) := Ideal.Quotient.isDomain q
  have : Algebra.FormallyUnramified R (S ⧸ q) :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ R q) Ideal.Quotient.mk_surjective
  have : Algebra.EssFiniteType S (S ⧸ q) :=
    Algebra.EssFiniteType.of_surjective (Ideal.Quotient.mkₐ S q) Ideal.Quotient.mk_surjective
  have : Algebra.EssFiniteType R (S ⧸ q) := Algebra.EssFiniteType.comp R S (S ⧸ q)
  have hmk : ∀ r : R, algebraMap R (S ⧸ q) r = Ideal.Quotient.mk q (algebraMap R S r) :=
    fun r => IsScalarTower.algebraMap_apply R S (S ⧸ q) r
  have hQ : (q'.map (Ideal.Quotient.mk q)).IsPrime := by
    refine Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective ?_
    rw [Ideal.mk_ker]
    exact hle
  have hbot : q'.map (Ideal.Quotient.mk q) = ⊥ := by
    refine eq_bot_of_formallyUnramified_of_comap_le_consolidated201 R (S ⧸ q) (q.comap (algebraMap R S))
      inferInstance ?_ (q'.map (Ideal.Quotient.mk q)) hQ ?_
    · intro r
      rw [hmk r, Ideal.Quotient.eq_zero_iff_mem]
      exact Iff.rfl
    · intro r hr
      rw [hmk r] at hr
      have hmem : algebraMap R S r ∈ q' := (Ideal.mem_quotient_iff_mem hle).mp hr
      rw [hc]
      exact hmem
  refine le_antisymm hle ?_
  intro z hz
  have hzz : Ideal.Quotient.mk q z ∈ q'.map (Ideal.Quotient.mk q) := Ideal.mem_map_of_mem _ hz
  rw [hbot] at hzz
  exact Ideal.Quotient.eq_zero_iff_mem.mp (Ideal.mem_bot.mp hzz)

private theorem strictMono_comap_of_formallyUnramified_consolidated201 [Algebra R S] [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
  intro a b hab
  have hle : a.asIdeal ≤ b.asIdeal := hab.le
  refine lt_of_le_of_ne ?_ ?_
  · exact Ideal.comap_mono hle
  · intro heq
    refine absurd ?_ (ne_of_lt hab)
    exact PrimeSpectrum.ext (eq_of_le_of_comap_eq_consolidated201 R S a.asIdeal b.asIdeal a.isPrime b.isPrime hle
      (congrArg PrimeSpectrum.asIdeal heq))

theorem ringKrullDim_le_of_essFiniteType_formallyUnramified [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R]
    [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]
    [Algebra.FormallyUnramified R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  exact Order.krullDim_le_of_strictMono _ (strictMono_comap_of_formallyUnramified_consolidated201 R S)


end

private theorem ringKrullDim_le_of_isLocalization_etale_consolidated201 {A B R S : Type u} [CommRing A]
    [CommRing B] [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R]
    [IsNoetherianRing S] (φ : A →+* B) (gA : A →+* R) (gB : B →+* S) (ψ : R →+* S)
    (MA : Submonoid A) (MB : Submonoid B) (hφ : RingHom.Etale φ)
    (hlocA : @IsLocalization A _ MA R _ gA.toAlgebra)
    (hlocB : @IsLocalization B _ MB S _ gB.toAlgebra)
    (hcomm : ∀ a : A, ψ (gA a) = gB (φ a)) (hlocal : IsLocalHom ψ) :
    ringKrullDim S ≤ ringKrullDim R := by
  let _ : Algebra A B := φ.toAlgebra
  let _ : Algebra A R := gA.toAlgebra
  let _ : Algebra B S := gB.toAlgebra
  let _ : Algebra R S := ψ.toAlgebra
  let _ : Algebra A S := (gB.comp φ).toAlgebra
  have : IsLocalization MA R := hlocA
  have : IsLocalization MB S := hlocB
  have : Algebra.Etale A B := hφ
  have : IsLocalHom (algebraMap R S) := hlocal
  have : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq fun a => (hcomm a).symm
  have : Algebra.FormallyUnramified A B := inferInstance
  have : Algebra.FiniteType A B := inferInstance
  have : Algebra.EssFiniteType A B := inferInstance
  have : Algebra.FormallyUnramified B S := Algebra.FormallyUnramified.of_isLocalization (M := MB)
  have : Algebra.EssFiniteType B S := Algebra.EssFiniteType.of_isLocalization S MB
  have : Algebra.FormallyUnramified A S := Algebra.FormallyUnramified.comp A B S
  have : Algebra.EssFiniteType A S := Algebra.EssFiniteType.comp A B S
  have : Algebra.FormallyUnramified R S := Algebra.FormallyUnramified.localization_base MA
  have : Algebra.EssFiniteType R S := Algebra.EssFiniteType.of_comp A R S
  exact ringKrullDim_le_of_essFiniteType_formallyUnramified R S

theorem ringKrullDim_stalk_le_of_etale_of_isNoetherianRing {Y W : Scheme.{u}} (f : Y ⟶ W)
    [Etale f] (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)]
    [IsNoetherianRing (W.presheaf.stalk (f.base y))] :
    ringKrullDim (Y.presheaf.stalk y) ≤ ringKrullDim (W.presheaf.stalk (f.base y)) := by
  have hf : Etale f := inferInstance
  obtain ⟨U, hxU, hU⟩ := Scheme.exists_isAffineOpen_mem (X := W) (f.base y)
  obtain ⟨V₀, hyV₀, hV₀⟩ := Scheme.exists_isAffineOpen_mem (X := Y) y
  have hymem : y ∈ (V₀ ⊓ f ⁻¹ᵁ U : Y.Opens) := ⟨hyV₀, hxU⟩
  obtain ⟨g, hgle, hyg⟩ :=
    hV₀.exists_basicOpen_le (⟨y, hymem⟩ : (V₀ ⊓ f ⁻¹ᵁ U : Y.Opens)) hyV₀
  have hV : IsAffineOpen (Y.basicOpen g) := hV₀.basicOpen g
  have hVU : Y.basicOpen g ≤ f ⁻¹ᵁ U := le_trans hgle inf_le_right
  have hyV : y ∈ Y.basicOpen g := hyg
  have hgerm : f.appLE U (Y.basicOpen g) hVU ≫ Y.presheaf.germ (Y.basicOpen g) y hyV
      = W.presheaf.germ U (f.base y) hxU ≫ f.stalkMap y := by
    simp [Scheme.Hom.appLE]
  have hetale : RingHom.Etale (f.appLE U (Y.basicOpen g) hVU).hom :=
    AlgebraicGeometry.HasRingHomProperty.appLE (P := @Etale) f hf
      ⟨U, hU⟩ ⟨Y.basicOpen g, hV⟩ hVU
  refine ringKrullDim_le_of_isLocalization_etale_consolidated201 (f.appLE U (Y.basicOpen g) hVU).hom
    (W.presheaf.germ U (f.base y) hxU).hom
    (Y.presheaf.germ (Y.basicOpen g) y hyV).hom (f.stalkMap y).hom
    (hU.primeIdealOf ⟨f.base y, hxU⟩).asIdeal.primeCompl
    (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl hetale
    (hU.isLocalization_stalk ⟨f.base y, hxU⟩)
    (hV.isLocalization_stalk ⟨y, hyV⟩) (fun a => ?_) inferInstance
  exact congrArg (fun t : Γ(W, U) ⟶ Y.presheaf.stalk y => t.hom a) hgerm.symm

section
variable {V P : Scheme.{u}} (f : V ⟶ P) [Etale f] [IsLocallyNoetherian P]
include f

theorem topologicalKrullDim_le_of_etale :
    topologicalKrullDim ↥V ≤ topologicalKrullDim ↥P := by
  have : IsLocallyNoetherian V :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f
  refine topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le V
    (topologicalKrullDim ↥P) ?_
  intro y
  have : IsNoetherianRing (V.presheaf.stalk y) := inferInstance
  have : IsNoetherianRing (P.presheaf.stalk (f.base y)) := inferInstance
  exact le_trans (ringKrullDim_stalk_le_of_etale_of_isNoetherianRing f y)
    (ringKrullDim_stalk_le_topologicalKrullDim P (f.base y))

theorem krullDimSucc_le_of_etale (hP : topologicalKrullDim ↥P < ⊤) :
    krullDimSucc V ≤ krullDimSucc P :=
  krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le _ _ (topologicalKrullDim_le_of_etale f) hP


end

private theorem isLocallyNoetherian_of_smooth_over_field_consolidated201 {k : Type u} [Field k]
    {P : Scheme.{u}} (pP : P ⟶ Spec (CommRingCat.of k)) [Smooth pP] :
    IsLocallyNoetherian P := by
  refine ⟨fun U => ?_⟩
  exact @isNoetherianRing_sections k _ _ P pP _ U (sectionsAlgebra k pP U.1)
    (algebraMap_sectionsAlgebra k pP U.1)

section
variable {k K : Type u} [Field k] [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))

private theorem surjective_base_pullback_fst_specMapOfFieldHom_consolidated201 (f : k →+* K) :
    Function.Surjective (pullback.fst p (specMapOfFieldHom k K f)).base := by
  have hsq := isPullback_pullback_specMap p (CommRingCat.ofHom f)
  have hS : AlgebraicGeometry.Surjective (specMapOfFieldHom k K f) :=
    FunctorialResolution.EmbeddedResolution.instSurjectiveSpecMapOfFieldHom k K f
  have : AlgebraicGeometry.Surjective (pullback.fst p (specMapOfFieldHom k K f)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.Surjective) hsq hS
  exact Scheme.Hom.surjective _

private theorem topologicalKrullDim_pullback_spec_map_of_surjective_consolidated201 [Smooth p]
    (φ : CommRingCat.of k ⟶ CommRingCat.of K)
    (hsurj : Function.Surjective (pullback.fst p (Spec.map φ)).base) :
    topologicalKrullDim ↥(pullback p (Spec.map φ)) = topologicalKrullDim ↥X := by
  have : IsLocallyNoetherian X :=
    isLocallyNoetherian_of_smooth_over_field_consolidated201 p
  have : IsLocallyNoetherian (pullback p (Spec.map φ)) :=
    isLocallyNoetherian_of_smooth_over_field_consolidated201 (pullback.snd p (Spec.map φ))
  refine le_antisymm ?_ ?_
  · refine topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le _ _ ?_
    intro y
    obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p ((pullback.fst p (Spec.map φ)).base y)
    obtain ⟨V, -, c', -, hyV, -⟩ := exists_etaleChart_pullback_specMap p φ c y hxU
    exact le_trans
      (ringKrullDim_stalk_le_of_etaleChart_of_isLocallyNoetherian (pullback.snd p (Spec.map φ)) c' y hyV)
      (etaleChart_dim_le_topologicalKrullDim p c hU
        ⟨(pullback.fst p (Spec.map φ)).base y, hxU⟩)
  · refine topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le _ _ ?_
    intro x
    obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p x
    obtain ⟨y, rfl⟩ := hsurj x
    obtain ⟨V, -, c', hVaff, hyV, -⟩ := exists_etaleChart_pullback_specMap p φ c y hxU
    exact le_trans (ringKrullDim_stalk_le_of_etaleChart_of_isLocallyNoetherian p c _ hxU)
      (etaleChart_dim_le_topologicalKrullDim (pullback.snd p (Spec.map φ)) c' hVaff ⟨y, hyV⟩)

theorem topologicalKrullDim_pullback_specMapOfFieldHom [Smooth p]
    (f : k →+* K) :
    topologicalKrullDim ↥(pullback p (specMapOfFieldHom k K f)) = topologicalKrullDim ↥X :=
  topologicalKrullDim_pullback_spec_map_of_surjective_consolidated201 p (CommRingCat.ofHom f)
    (surjective_base_pullback_fst_specMapOfFieldHom_consolidated201 p f)


end

theorem MarkedIdealWithBoundary.dim_baseChange (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (L : Type u) [Field L]
    [CharZero L] (f : T.base →+* L) :
    (T.baseChange L f).krullDimSucc = T.krullDimSucc := by
  have : Smooth T.structMap := hT.smooth
  have h : topologicalKrullDim ↥(T.baseChange L f).scheme = topologicalKrullDim ↥T.scheme :=
    topologicalKrullDim_pullback_specMapOfFieldHom T.structMap f
  exact krullDimSucc_eq_of_topologicalKrullDim_eq h

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationConstruction
section


section

def markedTripleOrderOne (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) : MarkedIdealWithBoundary.{u} :=
  MarkedIdealWithBoundary.mk k X p I 1 E

section
variable (k : Type u) [Field k]

@[simp] theorem markedTripleOrderOne_dim (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) :
    (markedTripleOrderOne k X p I E).krullDimSucc = krullDimSucc X := rfl

theorem markedTripleOrderOne_isAdmissible [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p]
    [QuasiCompact p]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) :
    (markedTripleOrderOne k X p I E).IsAdmissible where
  charZero := inferInstanceAs (CharZero k)
  locallyOfFiniteType := inferInstanceAs (LocallyOfFiniteType p)
  nonzeroOnComponents := hI
  one_le_mult := le_refl 1
  quasiCompact := inferInstanceAs (QuasiCompact p)
  smooth := inferInstanceAs (Smooth p)
  snc := hE


end

def SmoothSubschemeIdealIsRadical : Prop :=
  ∀ (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (Z : X.IdealSheafData)
    [Smooth (Z.subschemeι ≫ p)] (J : X.IdealSheafData),
    (↑Z.support : Set ↥X) ⊆ (↑J.support : Set ↥X) → J ≤ Z

namespace PrincipalizationRules

def markedBlowupSeq (B : PrincipalizationRules.{u}) (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) : MarkedSequenceOfBlowups p I 1 E :=
  (B.outputLevelData (krullDimSucc X)).maxOrderRed (markedTripleOrderOne k X p I E)

end PrincipalizationRules

def CommutesWithClosedImmersion (B : PrincipalizationRules.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X X' : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p]
    [QuasiCompact p]
    (p' : X' ⟶ Spec (CommRingCat.of k))
    [Smooth p'] [LocallyOfFiniteType p']
    [QuasiCompact p']
    (j : X ⟶ X') [IsClosedImmersion j],
    j ≫ p' = p →
    ∀ (c : ℕ), 1 ≤ c → HasEtaleCoordCodim p' j c →
    ∀ (I : X.IdealSheafData), NonzeroOnComponents I →
      NonzeroOnComponents (imageIdealSheaf j I) →
      InStrictNormalCrossingPosition p ([] : List X.IdealSheafData) →
      InStrictNormalCrossingPosition p' ([] : List X'.IdealSheafData) →
      IsPushforwardBlowupSeq j (B.markedBlowupSeq k X p I []).toSequenceOfBlowups
        (B.markedBlowupSeq k X' p' (imageIdealSheaf j I) []).toSequenceOfBlowups

namespace PrincipalizationRules

section
variable (B : PrincipalizationRules.{u})

private theorem markedBlowupSeq_toSequenceOfBlowups_eq_of_le_consolidated187 (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) {N : ℕ} (h : krullDimSucc X ≤ N) :
    (B.markedBlowupSeq k X p I E).toSequenceOfBlowups
      = ((B.outputLevelData N).maxOrderRed (markedTripleOrderOne k X p I E)).toSequenceOfBlowups := by
  have hs : (B.outputLevelData (krullDimSucc X)).maxOrderRed (markedTripleOrderOne k X p I E)
      = (B.outputLevelData N).maxOrderRed (markedTripleOrderOne k X p I E) :=
    (B.outputLevelData_maxOrderReduction_eq_of_le h (markedTripleOrderOne k X p I E)
      (le_of_eq (markedTripleOrderOne_dim k X p I E))).symm
  exact congrArg (fun s : (markedTripleOrderOne k X p I E).SequenceOfBlowups => s.toSequenceOfBlowups) hs

theorem hasReducedCenters_markedBlowupSeq (hrad : SmoothSubschemeIdealIsRadical.{u})
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p]
    [QuasiCompact p]
    (I : X.IdealSheafData) (_hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (_hE : InStrictNormalCrossingPosition p E) :
    HasReducedCenters (B.markedBlowupSeq k X p I E) := by
  intro i hi J hJ
  have hsm : Smooth
      (((B.markedBlowupSeq k X p I E).center i).subschemeι ≫ (B.markedBlowupSeq k X p I E).projectionToSpec i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact (B.markedBlowupSeq k X p I E).center_smooth i hi
  exact hrad k ((B.markedBlowupSeq k X p I E).schemeAt i) ((B.markedBlowupSeq k X p I E).projectionToSpec i)
    ((B.markedBlowupSeq k X p I E).center i) J hJ


end

def principalizationSeq (B : PrincipalizationRules.{u}) (hrad : SmoothSubschemeIdealIsRadical.{u})
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p]
    [QuasiCompact p]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) : IdealBlowupSequence p I E :=
  (B.markedBlowupSeq k X p I E).toIdealBlowupSequence (B.hasReducedCenters_markedBlowupSeq hrad k X p I hI E hE)

def principalization (B : PrincipalizationRules.{u}) (hrad : SmoothSubschemeIdealIsRadical.{u}) :
    PrincipalizationAlgorithm.{u} :=
  fun k ik icz X p ism ift iqc I hI E hE =>
    @principalizationSeq B hrad k ik icz X p ism ift iqc I hI E hE

section
variable (B : PrincipalizationRules.{u}) (hrad : SmoothSubschemeIdealIsRadical.{u}) (k : Type u) [Field k] [CharZero k] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p] (I : X.IdealSheafData) (hI : NonzeroOnComponents I) (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)

theorem principalization_toSequenceOfBlowups :
    (B.principalization hrad k X p I hI E hE).toSequenceOfBlowups
      = (B.markedBlowupSeq k X p I E).toSequenceOfBlowups :=
  MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups (B.markedBlowupSeq k X p I E)
    (B.hasReducedCenters_markedBlowupSeq hrad k X p I hI E hE)

theorem principalization_lastIdeal :
    (B.principalization hrad k X p I hI E hE).lastIdeal
      = (B.markedBlowupSeq k X p I E).lastIdeal :=
  MarkedSequenceOfBlowups.toMarkedSequence_lastIdeal (B.markedBlowupSeq k X p I E)
    (B.hasReducedCenters_markedBlowupSeq hrad k X p I hI E hE)


end

section
variable (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension) (k : Type u) [Field k] [CharZero k] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p] (I : X.IdealSheafData) (hI : NonzeroOnComponents I) (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) (X' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k)) [Smooth p'] [LocallyOfFiniteType p'] [QuasiCompact p'] (φ : X' ⟶ X) [Smooth φ]
include hB hI hE

private theorem markedBlowupSeq_smoothPullback_isPullback_consolidated187 (hφ : φ ≫ p = p')
    (hI' : NonzeroOnComponents (I.comap φ))
    (hE' : InStrictNormalCrossingPosition p' (E.map fun D => D.comap φ)) :
    IsPullbackBlowupSequence φ
      (B.markedBlowupSeq k X' p' (I.comap φ) (E.map fun D => D.comap φ)).toSequenceOfBlowups
      (B.markedBlowupSeq k X p I E).toSequenceOfBlowups := by
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  have hV' := markedTripleOrderOne_isAdmissible k X' p' (I.comap φ) hI' (E.map fun D => D.comap φ) hE'
  have hdimLe : (markedTripleOrderOne k X p I E).krullDimSucc ≤ max (krullDimSucc X) (krullDimSucc X') :=
    le_max_left _ _
  have hPY : (markedTripleOrderOne k X' p' (I.comap φ) (E.map fun D => D.comap φ)).krullDimSucc
      ≤ max (krullDimSucc X) (krullDimSucc X') := le_max_right _ _
  rw [B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le_consolidated187 k X p I E (le_max_left (krullDimSucc X) (krullDimSucc X')),
    B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le_consolidated187 k X' p' (I.comap φ) (E.map fun D => D.comap φ)
      (le_max_right (krullDimSucc X) (krullDimSucc X'))]
  exact @IsMaxOrderReduction.isPullbackBlowupSequence_of_smooth
    (fun d => d ≤ max (krullDimSucc X) (krullDimSucc X'))
    ((B.outputLevelData (max (krullDimSucc X) (krullDimSucc X'))).maxOrderRed)
    ((B.outputLevelData (max (krullDimSucc X) (krullDimSucc X'))).orderRed)
    (B.isMaxOrderReduction_outputLevelData hB (max (krullDimSucc X) (krullDimSucc X')))
    (markedTripleOrderOne k X p I E) hV hdimLe X' p' φ
    (inferInstanceAs (Smooth φ)) hφ hV' hPY

private theorem markedBlowupSeq_smoothPullback_isStrictPullback_consolidated187 [AlgebraicGeometry.Surjective φ]
    (hφ : φ ≫ p = p')
    (hI' : NonzeroOnComponents (I.comap φ))
    (hE' : InStrictNormalCrossingPosition p' (E.map fun D => D.comap φ)) :
    IsStrictPullbackBlowupSeq φ
      (B.markedBlowupSeq k X' p' (I.comap φ) (E.map fun D => D.comap φ)).toSequenceOfBlowups
      (B.markedBlowupSeq k X p I E).toSequenceOfBlowups := by
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  have hV' := markedTripleOrderOne_isAdmissible k X' p' (I.comap φ) hI' (E.map fun D => D.comap φ) hE'
  have hdimLe : (markedTripleOrderOne k X p I E).krullDimSucc ≤ max (krullDimSucc X) (krullDimSucc X') :=
    le_max_left _ _
  have hPY : (markedTripleOrderOne k X' p' (I.comap φ) (E.map fun D => D.comap φ)).krullDimSucc
      ≤ max (krullDimSucc X) (krullDimSucc X') := le_max_right _ _
  rw [B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le_consolidated187 k X p I E (le_max_left (krullDimSucc X) (krullDimSucc X')),
    B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le_consolidated187 k X' p' (I.comap φ) (E.map fun D => D.comap φ)
      (le_max_right (krullDimSucc X) (krullDimSucc X'))]
  exact @IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective
    (fun d => d ≤ max (krullDimSucc X) (krullDimSucc X'))
    ((B.outputLevelData (max (krullDimSucc X) (krullDimSucc X'))).maxOrderRed)
    ((B.outputLevelData (max (krullDimSucc X) (krullDimSucc X'))).orderRed)
    (B.isMaxOrderReduction_outputLevelData hB (max (krullDimSucc X) (krullDimSucc X')))
    (markedTripleOrderOne k X p I E) hV hdimLe X' p' φ
    (inferInstanceAs (Smooth φ))
    (inferInstanceAs (AlgebraicGeometry.Surjective φ)) hφ hV' hPY


end

section
variable (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension) (k : Type u) [Field k] [CharZero k] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p] (I : X.IdealSheafData) (hI : NonzeroOnComponents I) (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) (K : Type u) [Field K] [CharZero K] (f : k →+* K) [Smooth (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))] [LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))] [QuasiCompact (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))] (hI' : NonzeroOnComponents (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))) (hE' : InStrictNormalCrossingPosition (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f)) (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))))
include hB hI hE hI' hE'

private theorem markedBlowupSeq_baseChange_isPullback_consolidated187 :
    IsPullbackBlowupSequence (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))
      (B.markedBlowupSeq K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
        (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
        (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
        (E.map fun D =>
          D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))).toSequenceOfBlowups
      (B.markedBlowupSeq k X p I E).toSequenceOfBlowups := by
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  have hV' := markedTripleOrderOne_isAdmissible K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
    (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
    (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hI'
    (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hE'
  have hdimLe : (markedTripleOrderOne k X p I E).krullDimSucc
      ≤ max (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))) :=
    le_max_left _ _
  have hPY : (markedTripleOrderOne K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
      (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
      (E.map fun D =>
        D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))).krullDimSucc
      ≤ max (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))) :=
    le_max_right _ _
  rw [B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le_consolidated187 k X p I E
      (le_max_left (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f)))),
    B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le_consolidated187 K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
      (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
      (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
      (le_max_right (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))))]
  exact (B.isMaxOrderReduction_outputLevelData hB
      (max (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))))).isPullbackBlowupSequence_baseChange
    (markedTripleOrderOne k X p I E) hV hdimLe K f hV' hPY

private theorem markedBlowupSeq_baseChange_isStrictPullback_consolidated187 :
    IsStrictPullbackBlowupSeq (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))
      (B.markedBlowupSeq K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
        (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
        (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
        (E.map fun D =>
          D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))).toSequenceOfBlowups
      (B.markedBlowupSeq k X p I E).toSequenceOfBlowups := by
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  have hV' := markedTripleOrderOne_isAdmissible K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
    (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
    (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hI'
    (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hE'
  have hdimLe : (markedTripleOrderOne k X p I E).krullDimSucc
      ≤ max (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))) :=
    le_max_left _ _
  have hPY : (markedTripleOrderOne K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
      (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
      (E.map fun D =>
        D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))).krullDimSucc
      ≤ max (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))) :=
    le_max_right _ _
  rw [B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le_consolidated187 k X p I E
      (le_max_left (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f)))),
    B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le_consolidated187 K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
      (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
      (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
      (le_max_right (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))))]
  exact (B.isMaxOrderReduction_outputLevelData hB
      (max (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p
          (specMapOfFieldHom k K f))))).isStrictPullbackBlowupSeq_baseChange
    (markedTripleOrderOne k X p I E) hV hdimLe K f hV' hPY


end

section
variable (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension)
include hB

private theorem markedBlowupSeq_lastIdeal_eq_top_consolidated187 (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p]
    [QuasiCompact p]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) :
    (B.markedBlowupSeq k X p I E).lastIdeal = ⊤ := by
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  have hP : (markedTripleOrderOne k X p I E).krullDimSucc ≤ krullDimSucc X := le_refl _
  have hres : MarkedSequenceOfBlowups.IsResolution (B.markedBlowupSeq k X p I E) :=
    (B.isMaxOrderReduction_outputLevelData hB (krullDimSucc X)).resolves (markedTripleOrderOne k X p I E) hV hP
  have h1 : FunctorialResolution.EmbeddedResolution.orderAtLeastLocus (B.markedBlowupSeq k X p I E).lastIdeal 1 = ∅ :=
    (MarkedSequenceOfBlowups.isResolution_iff (B.markedBlowupSeq k X p I E)).mp hres
  apply (AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).mpr
  apply Set.eq_empty_of_subset_empty
  intro x hx
  have hx' : x ∈ FunctorialResolution.EmbeddedResolution.orderAtLeastLocus (B.markedBlowupSeq k X p I E).lastIdeal 1 :=
    (mem_orderAtLeastLocus_one_iff (B.markedBlowupSeq k X p I E).lastIdeal x).mpr hx
  rw [h1] at hx'
  exact hx'

theorem isFunctorialPrincipalization_principalization (hrad : SmoothSubschemeIdealIsRadical.{u}) (hemb : CommutesWithClosedImmersion.{u} B) :
    IsFunctorialPrincipalization (B.principalization hrad) where
  pushforward := by
    intro k _ _ S X pS p _ _ _ _ _ _ j _ hjp c hc hcc I hI hIX hES hEX
    rw [B.principalization_toSequenceOfBlowups hrad k S pS I hI [] hES,
      B.principalization_toSequenceOfBlowups hrad k X p (imageIdealSheaf j I) hIX [] hEX]
    exact hemb k S X pS p j hjp c hc hcc I hI hIX hES hEX
  base_change := by
    intro k _ _ X p _ _ _ I hI E hE K _ _ f _ _ _ hI' hE'
    rw [B.principalization_toSequenceOfBlowups hrad K
        (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
        (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
        (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hI'
        (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hE',
      B.principalization_toSequenceOfBlowups hrad k X p I hI E hE]
    exact B.markedBlowupSeq_baseChange_isPullback_consolidated187 hB k X p I hI E hE K f hI' hE'
  base_change_strict := by
    intro k _ _ X p _ _ _ I hI E hE K _ _ f _ _ _ hI' hE'
    rw [B.principalization_toSequenceOfBlowups hrad K
        (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
        (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
        (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hI'
        (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hE',
      B.principalization_toSequenceOfBlowups hrad k X p I hI E hE]
    exact B.markedBlowupSeq_baseChange_isStrictPullback_consolidated187 hB k X p I hI E hE K f hI' hE'
  lastIdeal_eq_top := by
    intro k _ _ X p _ _ _ I hI E hE
    rw [B.principalization_lastIdeal hrad k X p I hI E hE]
    exact B.markedBlowupSeq_lastIdeal_eq_top_consolidated187 hB k X p I hI E hE
  smooth_pullback := by
    intro k _ _ X p _ _ _ I hI E hE X' p' _ _ _ φ _ hφ hI' hE'
    rw [B.principalization_toSequenceOfBlowups hrad k X' p' (I.comap φ) hI'
        (E.map fun D => D.comap φ) hE',
      B.principalization_toSequenceOfBlowups hrad k X p I hI E hE]
    exact B.markedBlowupSeq_smoothPullback_isPullback_consolidated187 hB k X p I hI E hE X' p' φ hφ hI' hE'
  smooth_pullback_strict := by
    intro k _ _ X p _ _ _ I hI E hE X' p' _ _ _ φ _ _ hφ hI' hE'
    rw [B.principalization_toSequenceOfBlowups hrad k X' p' (I.comap φ) hI'
        (E.map fun D => D.comap φ) hE',
      B.principalization_toSequenceOfBlowups hrad k X p I hI E hE]
    exact B.markedBlowupSeq_smoothPullback_isStrictPullback_consolidated187 hB k X p I hI E hE X' p' φ hφ hI' hE'


end

end PrincipalizationRules

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
section


section

theorem blowupPreservesNoetherian : BlowupPreservesNoetherian.{u} := by
  repeat intro _
  rename_i h
  exact isNoetherian_of_isBlowupAlongIdealSheaf h

def canonicalAlgorithmRules (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) : PrincipalizationRules.{u} where
  divisorRed := fun T alg j =>
    DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T alg j
  maxOrderRed := fun T rc => orderReductionSeq comapIsoInvariance T rc
  orderRed := fun T rc => MaxContactReduction.reduceOrder comapIsoInvariance T rc

def canonicalPrincipalization (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hrad : SmoothSubschemeIdealIsRadical.{u}) : PrincipalizationAlgorithm.{u} :=
  (canonicalAlgorithmRules hres).principalization hrad

theorem isFunctorialPrincipalization_canonicalPrincipalization (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension) (hrad : SmoothSubschemeIdealIsRadical.{u})
    (hemb : CommutesWithClosedImmersion.{u} (canonicalAlgorithmRules hres)) :
    IsFunctorialPrincipalization (canonicalPrincipalization hres hrad) :=
  PrincipalizationRules.isFunctorialPrincipalization_principalization (canonicalAlgorithmRules hres) hB hrad hemb


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.ClosedImmersionCommutation
section



def AdmissibilityStableUnderSmoothPullback : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h] [QuasiCompact q],
      h ≫ T.structMap = q → (T.pullbackAlong Y q h).IsAdmissible

theorem isAdmissible_pullbackAlong_of_smooth : AdmissibilityStableUnderSmoothPullback.{u} := by
  intro T hV Y q h hs hqc hq
  have := hs
  have := hqc
  exact MarkedIdealWithBoundary.isAdmissible_pullbackAlong_of_smooth T hV Y q h hq

private theorem maxOrderReduction_outputLevelData_eq_markedBlowupSeq_consolidated434 (rules : PrincipalizationRules.{u}) (k : Type u) [Field k]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) (N : ℕ) (h : krullDimSucc X ≤ N) :
    (rules.outputLevelData N).maxOrderRed (markedTripleOrderOne k X p I E) = rules.markedBlowupSeq k X p I E :=
  rules.outputLevelData_maxOrderReduction_eq_at_dim (markedTripleOrderOne k X p I E) h

private theorem ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic_consolidated434 {X : Scheme.{u}} (s : SequenceOfBlowups X) :
    (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.Isomorphic s := by
  refine ⟨rfl, fun i _ => Iso.refl _, ?_, ?_, ?_⟩
  · exact Category.id_comp _
  · intro i hi
    simp only [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.ofSequenceOfBlowups_blowupMorphism, Iso.refl_hom]
    exact (Category.id_comp (s.transitionMapSucc i)).trans (Category.comp_id (s.transitionMapSucc i)).symm
  · intro i hi
    exact Scheme.IdealSheafData.comap_id _

private theorem isPushforwardSequenceOfBlowups_congr_hom_consolidated434 {S X : Scheme.{u}} {f g : S ⟶ X}
    [IsClosedImmersion f] [IsClosedImmersion g]
    (h : f = g) {BS : SequenceOfBlowups S} {Bs : SequenceOfBlowups X}
    (hp : IsPushforwardBlowupSeq f BS Bs) : IsPushforwardBlowupSeq g BS Bs := by
  subst h
  exact hp

private theorem isLocallyNoetherian_schemeAt_consolidated434 {X : Scheme.{u}} (s : SequenceOfBlowups X)
    [IsNoetherian X] (i : ℕ) (hi : i ≤ s.length) :
    IsLocallyNoetherian (s.schemeAt i) := by
  have := isNoetherian_schemeAt s i hi
  infer_instance

private theorem nonzeroOnComponents_ker_of_hasEtaleCoordCodim_consolidated434 {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X')
    [IsClosedImmersion τ] [IsNoetherian X'] {c : ℕ}
    (hc : 1 ≤ c) (hcod : HasEtaleCoordCodim p τ c) :
    NonzeroOnComponents (Scheme.Hom.ker τ) := by
  refine nonzeroOnComponents_of_locally_eq_coordIdeal p (Scheme.Hom.ker τ)
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents ?_
  intro y hy
  have hsupp := Scheme.Hom.support_ker τ
  have hy' : y ∈ closure (Set.range (⇑τ)) := by
    rw [← hsupp]
    exact hy
  have hcl : IsClosed (Set.range (⇑τ)) :=
    (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding τ).isClosed_range
  rw [hcl.closure_eq] at hy'
  obtain ⟨x, rfl⟩ := hy'
  obtain ⟨U, hxU, mm, ch, S, hcard, heq⟩ := hcod x
  exact ⟨U, hxU, mm, ch, S, Finset.card_pos.mp (by omega), heq⟩

namespace MaximalContactCover

variable {X X' : Scheme.{u}} {k : Type u} [Field k] {p : X' ⟶ Spec (CommRingCat.of k)}
  {τ : X ⟶ X'} {I : X.IdealSheafData} {c : ℕ}

theorem isNoetherian_disjointUnion [LocallyOfFiniteType p]
    (C : MaximalContactCover p τ I c) :
    IsNoetherian C.toCoverData.disjointUnion :=
  isNoetherian_of_locallyOfFiniteType (C.projection ≫ p)

instance instIsNoetherianTotal [LocallyOfFiniteType p]
    (C : MaximalContactCover p τ I c) :
    IsNoetherian C.toCoverData.disjointUnion :=
  isNoetherian_disjointUnion C

theorem isNoetherian_subscheme_iInfImageIdeal [LocallyOfFiniteType p]
    (C : MaximalContactCover p τ I c) :
    IsNoetherian C.toCoverData.iInfImageIdeal.subscheme := by
  have := isNoetherian_disjointUnion C
  exact isNoetherian_of_locallyOfFiniteType C.toCoverData.iInfImageIdeal.subschemeι

instance instIsNoetherianSubschemeGlueIdeal [LocallyOfFiniteType p]
    (C : MaximalContactCover p τ I c) :
    IsNoetherian C.toCoverData.iInfImageIdeal.subscheme :=
  isNoetherian_subscheme_iInfImageIdeal C

end MaximalContactCover

private def IsClosedEmbeddingCompatibleInCodim_consolidated434 (rules : PrincipalizationRules.{u}) (c : ℕ) : Prop :=
  ∀ (k : Type u) [Field k], CharZero k → ∀ (X X' : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (p' : X' ⟶ Spec (CommRingCat.of k)) (j : X ⟶ X')
    [IsClosedImmersion j],
    Smooth p → LocallyOfFiniteType p →
    QuasiCompact p → Smooth p' →
    LocallyOfFiniteType p' → QuasiCompact p' →
    j ≫ p' = p → 1 ≤ c → HasEtaleCoordCodim p' j c →
    ∀ I : X.IdealSheafData, NonzeroOnComponents I → NonzeroOnComponents (imageIdealSheaf j I) →
      IsPushforwardBlowupSeq j (rules.markedBlowupSeq k X p I []).toSequenceOfBlowups
        (rules.markedBlowupSeq k X' p' (imageIdealSheaf j I) []).toSequenceOfBlowups

private theorem commutesWithClosedImmersion_forall_codim_consolidated434 (rules : PrincipalizationRules.{u}) (hB : rules.ReducesInductivelyOnDimension)
    (hpv : AdmissibilityStableUnderSmoothPullback.{u}) : ∀ c : ℕ, IsClosedEmbeddingCompatibleInCodim_consolidated434 rules c := by
  intro c
  induction c with
  | zero =>
      intro k _ _ X X' p p' j _ _ _ _ _ _ _ _ hc
      exact absurd hc (by omega)
  | succ c' ih =>
      intro k _ hcz X X' p p' j hji hsm hft hqc hsm' hft' hqc' hjp hc hcod I hI hIim
      have := hcz
      have := hsm
      have := hft
      have := hqc
      have := hsm'
      have := hft'
      have := hqc'
      have hNX : IsNoetherian X := isNoetherian_of_locallyOfFiniteType p
      have hNX' : IsNoetherian X' := isNoetherian_of_locallyOfFiniteType p'
      have hvX : (markedTripleOrderOne k X p I []).IsAdmissible :=
        markedTripleOrderOne_isAdmissible k X p I hI [] (inStrictNormalCrossingPosition_nil p)
      have hvX' : (markedTripleOrderOne k X' p' (imageIdealSheaf j I) []).IsAdmissible :=
        markedTripleOrderOne_isAdmissible k X' p' (imageIdealSheaf j I) hIim [] (inStrictNormalCrossingPosition_nil p')
      rcases isEmpty_or_nonempty ↥X with hXe | hXne
      · have := hXe
        have hIsub : IsEmpty ↥I.subscheme := Function.isEmpty (fun y => I.subschemeι y)
        have himg : imageIdealSheaf j I = ⊤ := by
          rw [Scheme.IdealSheafData.eq_top_iff_support_eq_empty, imageIdealSheaf_eq_ker j I,
            Scheme.Hom.support_ker (I.subschemeι ≫ j), Set.range_eq_empty, closure_empty]
        have hcs1 : orderAtLeastLocus I 1 = (∅ : Set ↥X) := Set.eq_empty_of_isEmpty _
        have hcs2 : orderAtLeastLocus (imageIdealSheaf j I) 1 = (∅ : Set ↥X') := by
          rw [himg]
          exact orderAtLeastLocus_top_eq_empty 1 le_rfl
        have hspec := rules.isMaxOrderReduction_outputLevelData hB (krullDimSucc X + krullDimSucc X')
        have h1 := hspec.trivial_of_coSupport_empty (markedTripleOrderOne k X p I []) hvX
          (show krullDimSucc X ≤ krullDimSucc X + krullDimSucc X' by omega) hcs1
        have h2 := hspec.trivial_of_coSupport_empty
          (markedTripleOrderOne k X' p' (imageIdealSheaf j I) []) hvX'
          (show krullDimSucc X' ≤ krullDimSucc X + krullDimSucc X' by omega) hcs2
        rw [maxOrderReduction_outputLevelData_eq_markedBlowupSeq_consolidated434 rules k X p I [] (krullDimSucc X + krullDimSucc X')
          (show krullDimSucc X ≤ krullDimSucc X + krullDimSucc X' by omega)] at h1
        rw [maxOrderReduction_outputLevelData_eq_markedBlowupSeq_consolidated434 rules k X' p' (imageIdealSheaf j I) [] (krullDimSucc X + krullDimSucc X')
          (show krullDimSucc X' ≤ krullDimSucc X + krullDimSucc X' by omega)] at h2
        exact IsPushforwardBlowupSeq.of_length_eq_zero j _ _ h1 h2
      · have hch : HasLocalEtaleCharts p' := by
          intro y
          obtain ⟨U, mm, hyU, haff, hne⟩ := exists_etaleChart p' y
          exact ⟨U, hyU, mm, hne⟩
        obtain ⟨C⟩ := nonempty_maximalContactCover p' j I (c' + 1) hc hcod hch
        have hNW : IsNoetherian C.toCoverData.disjointUnion :=
          MaximalContactCover.isNoetherian_disjointUnion C
        have hnoeth : IsNoetherian C.toCoverData.iInfImageIdeal.subscheme :=
          MaximalContactCover.isNoetherian_subscheme_iInfImageIdeal C
        have hNSW : TopologicalSpace.NoetherianSpace ↥C.toCoverData.disjointUnion := inferInstance
        have hNSH : TopologicalSpace.NoetherianSpace ↥C.hypersurfaceScheme := inferInstance
        have hsmH : Smooth C.hypersurfaceStructureMap := C.smooth_hypersurfaceStructureMap
        have hsmP : Smooth C.projection := by
          rw [C.projection_eq]
          exact C.toCoverData.smooth_disjointUnionMap
        have hsuP : AlgebraicGeometry.Surjective C.projection := C.surjective_projection
        have hsmSB : Smooth C.pullbackFiberToBase := C.smooth_pullbackFiberToBase
        have hsuSB : AlgebraicGeometry.Surjective C.pullbackFiberToBase := C.surjective_pullbackFiberToBase
        have hqcH : QuasiCompact C.hypersurfaceStructureMap := inferInstance
        have hqcWp : QuasiCompact (C.projection ≫ p') := C.quasiCompact_projection_comp
        have hCI : IsClosedImmersion C.toCoverData.iInfImageIdeal.subschemeι :=
          inferInstance
        have hstarw : C.pullbackFiberToBase ≫ j = C.pullbackFiberToTotal ≫ C.projection := C.isPullback_pullbackFiber.w
        have hcompeq : C.pullbackFiberToBase ≫ p = C.pullbackFiberToTotal ≫ (C.projection ≫ p') := by
          rw [← hjp, ← Category.assoc, hstarw, Category.assoc]
        have hqcS : QuasiCompact (C.pullbackFiberToBase ≫ p) := by
          rw [hcompeq]
          infer_instance
        obtain ⟨x0⟩ := hXne
        have hNEs : Nonempty ↥C.pullbackFiber := by
          obtain ⟨y, -⟩ := AlgebraicGeometry.Surjective.surj (f := C.pullbackFiberToBase) x0
          exact ⟨y⟩
        have hNEH : Nonempty ↥C.hypersurfaceScheme := by
          obtain ⟨y⟩ := hNEs
          exact ⟨C.pullbackFiberToHypersurface.base y⟩
        have hHW : krullDimSucc C.hypersurfaceScheme < krullDimSucc C.toCoverData.disjointUnion :=
          C.krullDimSucc_hypersurfaceScheme_lt
        obtain ⟨m, hm⟩ : ∃ m : ℕ, m = krullDimSucc X + krullDimSucc X'
            + krullDimSucc C.toCoverData.disjointUnion + krullDimSucc C.pullbackFiber
            + krullDimSucc C.hypersurfaceScheme := ⟨_, rfl⟩
        have hsmjp : Smooth (j ≫ p') := by
          rw [hjp]
          infer_instance
        have hkerNZ : NonzeroOnComponents (Scheme.Hom.ker j) :=
          nonzeroOnComponents_ker_of_hasEtaleCoordCodim_consolidated434 p' j hc hcod
        have horder : ∀ x : ↥X', orderAt (imageIdealSheaf j I) x ≤ 1 := by
          intro x
          exact orderAt_map_le_one_of_isClosedImmersion p' j hkerNZ I x
        have hfacH : C.pullbackFiberToHypersurface ≫ C.hypersurfaceStructureMap = C.pullbackFiberToBase ≫ p := by
          show C.pullbackFiberToHypersurface ≫ (C.toCoverData.iInfImageIdeal.subschemeι ≫ C.projection ≫ p')
            = C.pullbackFiberToBase ≫ p
          rw [C.pullbackFiberToHypersurface_comp_subschemeι_assoc (C.projection ≫ p'), ← Category.assoc, ← hstarw,
            Category.assoc, hjp]
        have hWideal : (imageIdealSheaf j I).comap C.projection
            = imageIdealSheaf C.toCoverData.iInfImageIdeal.subschemeι C.idealOnHypersurface := by
          rw [← C.comapImageIdealSheaf_eq]
          exact C.comapImageIdealSheaf_eq_imageIdealSheaf_idealOnHypersurface
        have hHideal : C.idealOnHypersurface = imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase) :=
          C.idealOnHypersurface_eq_imageIdealSheaf
        have hvW : (markedTripleOrderOne k C.toCoverData.disjointUnion (C.projection ≫ p')
            ((imageIdealSheaf j I).comap C.projection) []).IsAdmissible :=
          @hpv (markedTripleOrderOne k X' p' (imageIdealSheaf j I) []) hvX' C.toCoverData.disjointUnion
            (C.projection ≫ p') C.projection hsmP hqcWp rfl
        have hvS : (markedTripleOrderOne k C.pullbackFiber (C.pullbackFiberToBase ≫ p)
            (I.comap C.pullbackFiberToBase) []).IsAdmissible :=
          @hpv (markedTripleOrderOne k X p I []) hvX C.pullbackFiber (C.pullbackFiberToBase ≫ p)
            C.pullbackFiberToBase hsmSB hqcS rfl
        have hNZS : NonzeroOnComponents (I.comap C.pullbackFiberToBase) := hvS.nonzeroOnComponents
        have hcontactNZ : NonzeroOnComponents C.idealOnHypersurface := by
          rcases Nat.eq_zero_or_pos c' with hc0 | hc1
          · have hiso : IsIso C.pullbackFiberToHypersurface := C.isIso_pullbackFiberToHypersurface_of_eq_one (by omega)
            have hinv : imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase)
                = (I.comap C.pullbackFiberToBase).comap (CategoryTheory.inv C.pullbackFiberToHypersurface) :=
              imageIdealSheaf_eq_comap_inv C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase)
            have h2 : NonzeroOnComponents
                ((I.comap C.pullbackFiberToBase).comap (asIso C.pullbackFiberToHypersurface).symm.hom) :=
              nonzeroOnComponents_comap_iso_hom (asIso C.pullbackFiberToHypersurface).symm
                (I.comap C.pullbackFiberToBase) hNZS
            rw [hHideal, hinv]
            exact h2
          · have hcc0 : HasEtaleCoordCodim C.hypersurfaceStructureMap C.pullbackFiberToHypersurface c' :=
              C.hasEtaleCoordCodim_pullbackFiberToHypersurface
            refine C.nonzeroOnComponents_idealOnHypersurface ?_
            intro x
            obtain ⟨U, hxU, mm, ch, S, hcard, heq⟩ := hcc0 x
            exact ⟨U, hxU, mm, ch, S, Finset.card_pos.mp (by omega), heq⟩
        have hvH : (markedTripleOrderOne k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface []).IsAdmissible :=
          markedTripleOrderOne_isAdmissible k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface hcontactNZ []
            (inStrictNormalCrossingPosition_nil C.hypersurfaceStructureMap)
        have hspec := rules.isMaxOrderReduction_outputLevelData hB (m + 1)
        have hordspec := rules.isOrderReduction_outputLevelData hB (m + 1)
        have hpushFiber : IsPushforwardBlowupSeq C.pullbackFiberToHypersurface
            (rules.markedBlowupSeq k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (I.comap C.pullbackFiberToBase) []).toSequenceOfBlowups
            (rules.markedBlowupSeq k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface []).toSequenceOfBlowups := by
          rcases Nat.eq_zero_or_pos c' with hc0 | hc1
          · have hiso : IsIso C.pullbackFiberToHypersurface := C.isIso_pullbackFiberToHypersurface_of_eq_one (by omega)
            have hsmooth : Smooth C.pullbackFiberToHypersurface := inferInstance
            have hsurj : AlgebraicGeometry.Surjective C.pullbackFiberToHypersurface := inferInstance
            have hcomap : C.idealOnHypersurface.comap C.pullbackFiberToHypersurface = I.comap C.pullbackFiberToBase := by
              rw [hHideal]
              exact comap_imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase)
            have hvS' : (markedTripleOrderOne k C.pullbackFiber (C.pullbackFiberToBase ≫ p)
                (C.idealOnHypersurface.comap C.pullbackFiberToHypersurface) []).IsAdmissible := by
              rw [hcomap]
              exact hvS
            have hsp : IsStrictPullbackBlowupSeq C.pullbackFiberToHypersurface
                ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.pullbackFiber
                  (C.pullbackFiberToBase ≫ p) (C.idealOnHypersurface.comap C.pullbackFiberToHypersurface) [])).toSequenceOfBlowups
                ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.hypersurfaceScheme
                  C.hypersurfaceStructureMap C.idealOnHypersurface [])).toSequenceOfBlowups :=
              @IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective _ _ _ hspec
                (markedTripleOrderOne k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface []) hvH
                (show krullDimSucc C.hypersurfaceScheme ≤ m + 1 by omega)
                C.pullbackFiber (C.pullbackFiberToBase ≫ p) C.pullbackFiberToHypersurface hsmooth hsurj hfacH hvS'
                (show krullDimSucc C.pullbackFiber ≤ m + 1 by omega)
            rw [hcomap] at hsp
            rw [maxOrderReduction_outputLevelData_eq_markedBlowupSeq_consolidated434 rules k C.pullbackFiber (C.pullbackFiberToBase ≫ p)
                (I.comap C.pullbackFiberToBase) [] (m + 1) (by omega),
              maxOrderReduction_outputLevelData_eq_markedBlowupSeq_consolidated434 rules k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface []
                (m + 1) (by omega)] at hsp
            exact IsPushforwardBlowupSeq.of_isStrictPullback_of_isIso C.pullbackFiberToHypersurface hsp
          · have hcc0 : HasEtaleCoordCodim C.hypersurfaceStructureMap C.pullbackFiberToHypersurface c' :=
              C.hasEtaleCoordCodim_pullbackFiberToHypersurface
            rw [hHideal]
            exact ih k hcz C.pullbackFiber C.hypersurfaceScheme (C.pullbackFiberToBase ≫ p) C.hypersurfaceStructureMap
              C.pullbackFiberToHypersurface inferInstance inferInstance hqcS hsmH inferInstance hqcH
              hfacH hc1 hcc0 (I.comap C.pullbackFiberToBase) hNZS
              (by rw [← hHideal]; exact hcontactNZ)
        have hOBW : (markedTripleOrderOne k C.toCoverData.disjointUnion (C.projection ≫ p')
            ((imageIdealSheaf j I).comap C.projection) []).IsOrderBoundedByMult := by
          rw [MarkedIdealWithBoundary.isOrderBoundedByMult_iff]
          intro x
          have h1 : orderAt ((imageIdealSheaf j I).comap C.projection) x ≤ 1 := by
            rw [orderAt_comap k p' C.projection (imageIdealSheaf j I) x]
            exact horder (C.projection.base x)
          refine le_trans h1 (le_of_eq ?_)
          exact Nat.cast_one.symm
        have hdiv : IsSmoothDivisor (C.projection ≫ p')
            (Scheme.Hom.ker C.toCoverData.iInfImageIdeal.subschemeι) := by
          rw [Scheme.IdealSheafData.ker_subschemeι]
          exact C.isSmoothDivisor_iInfImageIdeal
        have hpushHW : IsPushforwardBlowupSeq C.toCoverData.iInfImageIdeal.subschemeι
            ((rules.inputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.hypersurfaceScheme C.hypersurfaceStructureMap
              C.idealOnHypersurface [])).toSequenceOfBlowups
            ((rules.outputLevelData (m + 1)).orderRed (markedTripleOrderOne k C.toCoverData.disjointUnion
              (C.projection ≫ p') ((imageIdealSheaf j I).comap C.projection) [])).toSequenceOfBlowups :=
          @IsOrderReduction.pushforward _ _ _ hordspec
            (markedTripleOrderOne k C.toCoverData.disjointUnion (C.projection ≫ p')
              ((imageIdealSheaf j I).comap C.projection) []) hvW
            (show krullDimSucc C.toCoverData.disjointUnion ≤ m + 1 by omega) hOBW rfl rfl
            C.hypersurfaceScheme C.hypersurfaceStructureMap C.toCoverData.iInfImageIdeal.subschemeι hCI rfl hdiv
            C.idealOnHypersurface hvH hHW hWideal
        rw [rules.inputLevelData_succ m, maxOrderReduction_outputLevelData_eq_markedBlowupSeq_consolidated434 rules k C.hypersurfaceScheme C.hypersurfaceStructureMap
          C.idealOnHypersurface [] m (by omega)] at hpushHW
        have hequivW : ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k
            C.toCoverData.disjointUnion (C.projection ≫ p') ((imageIdealSheaf j I).comap C.projection) [])).Isomorphic
            ((rules.outputLevelData (m + 1)).orderRed (markedTripleOrderOne k C.toCoverData.disjointUnion
              (C.projection ≫ p') ((imageIdealSheaf j I).comap C.projection) [])).toSequenceOfBlowups :=
          hspec.orderRed_equiv (markedTripleOrderOne k C.toCoverData.disjointUnion (C.projection ≫ p')
            ((imageIdealSheaf j I).comap C.projection) []) hvW
            (show krullDimSucc C.toCoverData.disjointUnion ≤ m + 1 by omega) rfl hOBW
        rw [maxOrderReduction_outputLevelData_eq_markedBlowupSeq_consolidated434 rules k C.toCoverData.disjointUnion (C.projection ≫ p')
          ((imageIdealSheaf j I).comap C.projection) [] (m + 1) (by omega)] at hequivW
        have hpushSubscheme := IsPushforwardBlowupSeq.of_isomorphic C.toCoverData.iInfImageIdeal.subschemeι
          hpushHW (SequenceOfBlowups.Isomorphic.symm hequivW)
        have hNtH : ∀ i : ℕ, i ≤ (rules.markedBlowupSeq k C.hypersurfaceScheme C.hypersurfaceStructureMap
            C.idealOnHypersurface []).toSequenceOfBlowups.length →
            IsNoetherian ((rules.markedBlowupSeq k C.hypersurfaceScheme C.hypersurfaceStructureMap
              C.idealOnHypersurface []).toSequenceOfBlowups.schemeAt i) :=
          fun i hi => isNoetherian_schemeAt _ i hi
        have hNtW : ∀ i : ℕ, i ≤ (rules.markedBlowupSeq k C.toCoverData.disjointUnion (C.projection ≫ p')
            ((imageIdealSheaf j I).comap C.projection) []).toSequenceOfBlowups.length →
            IsNoetherian ((rules.markedBlowupSeq k C.toCoverData.disjointUnion (C.projection ≫ p')
              ((imageIdealSheaf j I).comap C.projection) []).toSequenceOfBlowups.schemeAt i) :=
          fun i hi => isNoetherian_schemeAt _ i hi
        have hcomp := IsPushforwardBlowupSeq.comp C.pullbackFiberToHypersurface C.toCoverData.iInfImageIdeal.subschemeι
          hNtH hNtW hpushFiber hpushSubscheme
        have hcomp' : IsPushforwardBlowupSeq C.pullbackFiberToTotal
            (rules.markedBlowupSeq k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (I.comap C.pullbackFiberToBase) []).toSequenceOfBlowups
            (rules.markedBlowupSeq k C.toCoverData.disjointUnion (C.projection ≫ p')
              ((imageIdealSheaf j I).comap C.projection) []).toSequenceOfBlowups :=
          isPushforwardSequenceOfBlowups_congr_hom_consolidated434 C.pullbackFiberToHypersurface_comp_subschemeι hcomp
        have hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u} := strictTransformIsBlowupOfClosedSubscheme
        have hcart : EffectiveCartierSupportContainsNoComponent.{u} := effectiveCartierSupportContainsNoComponent
        have hproper := MarkedSequenceOfBlowups.centersContainNoComponent_ofMarkedSequence hcart hvX
          (rules.markedBlowupSeq k X p I [])
        have htower := isPushforwardBlowupSeq_ambientBlowupSequence j
          (BlowupSequenceData.ofSequenceOfBlowups (rules.markedBlowupSeq k X p I []).toSequenceOfBlowups) hres
          blowupPreservesNoetherian hproper
        obtain ⟨u0, hpf0⟩ : ∃ u0 : SequenceOfBlowups X',
            IsPushforwardBlowupSeq j (rules.markedBlowupSeq k X p I []).toSequenceOfBlowups u0 :=
          ⟨_, IsPushforwardBlowupSeq.of_isomorphic_source j (ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic_consolidated434 _) htower⟩
        have ht' : IsStrictPullbackBlowupSeq C.projection (u0.baseChange C.projection) u0 :=
          isStrictPullbackSequenceOfBlowups_baseChange u0 C.projection
        have hsS : IsStrictPullbackBlowupSeq C.pullbackFiberToBase
            ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.pullbackFiber
              (C.pullbackFiberToBase ≫ p) (I.comap C.pullbackFiberToBase) [])).toSequenceOfBlowups
            ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k X p I [])).toSequenceOfBlowups :=
          @IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective _ _ _ hspec
            (markedTripleOrderOne k X p I []) hvX (show krullDimSucc X ≤ m + 1 by omega)
            C.pullbackFiber (C.pullbackFiberToBase ≫ p) C.pullbackFiberToBase hsmSB hsuSB rfl hvS
            (show krullDimSucc C.pullbackFiber ≤ m + 1 by omega)
        rw [maxOrderReduction_outputLevelData_eq_markedBlowupSeq_consolidated434 rules k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (I.comap C.pullbackFiberToBase) []
            (m + 1) (by omega),
          maxOrderReduction_outputLevelData_eq_markedBlowupSeq_consolidated434 rules k X p I [] (m + 1) (by omega)] at hsS
        have hSW : IsStrictPullbackBlowupSeq C.projection
            ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.toCoverData.disjointUnion
              (C.projection ≫ p') ((imageIdealSheaf j I).comap C.projection) [])).toSequenceOfBlowups
            ((rules.outputLevelData (m + 1)).maxOrderRed
              (markedTripleOrderOne k X' p' (imageIdealSheaf j I) [])).toSequenceOfBlowups :=
          @IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective _ _ _ hspec
            (markedTripleOrderOne k X' p' (imageIdealSheaf j I) []) hvX'
            (show krullDimSucc X' ≤ m + 1 by omega) C.toCoverData.disjointUnion (C.projection ≫ p')
            C.projection hsmP hsuP rfl hvW
            (show krullDimSucc C.toCoverData.disjointUnion ≤ m + 1 by omega)
        rw [maxOrderReduction_outputLevelData_eq_markedBlowupSeq_consolidated434 rules k C.toCoverData.disjointUnion (C.projection ≫ p')
            ((imageIdealSheaf j I).comap C.projection) [] (m + 1) (by omega),
          maxOrderReduction_outputLevelData_eq_markedBlowupSeq_consolidated434 rules k X' p' (imageIdealSheaf j I) [] (m + 1) (by omega)] at hSW
        have hup := IsPushforwardBlowupSeq.of_flat_isPullback j C.pullbackFiberToTotal C.projection C.pullbackFiberToBase
          C.isPullback_pullbackFiber.flip (rules.markedBlowupSeq k X p I []).toSequenceOfBlowups u0
          (rules.markedBlowupSeq k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (I.comap C.pullbackFiberToBase) []).toSequenceOfBlowups
          (u0.baseChange C.projection)
          (fun i hi => isLocallyNoetherian_schemeAt_consolidated434 u0 i hi)
          (fun i hi => isLocallyNoetherian_schemeAt_consolidated434 (u0.baseChange C.projection) i hi)
          hpf0 hsS ht'
        have huniq := IsPushforwardBlowupSeq.isomorphic C.pullbackFiberToTotal hup hcomp'
        have hdesc := IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic ht' hSW huniq
        exact IsPushforwardBlowupSeq.of_isomorphic j hpf0 hdesc

section
variable (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension)
include hB

theorem commutesWithClosedImmersion_of_isCorrect_of_smoothPullback (hpv : AdmissibilityStableUnderSmoothPullback.{u}) : CommutesWithClosedImmersion.{u} B := by
  intro k ik icz X X' p ism ift iqc p' ism' ift' iqc' j ij hjp c hc hcod I hI hIim _ _
  exact commutesWithClosedImmersion_forall_codim_consolidated434 B hB hpv c k icz X X' p p' j ism ift iqc ism' ift' iqc' hjp hc hcod I hI hIim

theorem commutesWithClosedImmersion_of_isCorrect :
    CommutesWithClosedImmersion.{u} B :=
  commutesWithClosedImmersion_of_isCorrect_of_smoothPullback B hB isAdmissible_pullbackAlong_of_smooth


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MaxOrderReduction
section


section

namespace MaxOrderReduction

section
variable (hG : PrincipalizationGeometryHypotheses.{u})
include hG

private theorem orderAtBaseFieldChangeInvariance_of_geometryHypotheses_consolidated491 :
    OrderAtBaseFieldChangeInvariance.{u} := by
  intro T hT L _ _ f B b pB hpB IB EB hTB Q a b' hpb A y
  subst hpB
  have hQ : IsPullback
      (Limits.pullback.fst b (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f)))
      (Limits.pullback.snd b (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f))) b
      (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    IsPullback.of_hasPullback _ _
  let E : Q ≅ Limits.pullback (b ≫ T.structMap) (specMapOfFieldHom T.base L f) :=
    hpb.isoIsPullback B (Limits.pullback T.structMap (specMapOfFieldHom T.base L f)) hQ ≪≫
      Limits.pullbackRightPullbackFstIso T.structMap (specMapOfFieldHom T.base L f) b
  have he : E.hom ≫ Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f) = a := by
    simp [E, Iso.trans_hom]
  have hcomp : A.comap a =
      (A.comap
        (Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f))).comap E.hom := by
    rw [← he]
    simp [Scheme.IdealSheafData.comap_comp]
  have h1 : orderAt (A.comap a) y
      = orderAt (A.comap (Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f)))
          (E.hom.base y) := by
    rw [hcomp]
    exact FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isIso E.hom _ y
  have h2 := hG.orderAt_baseChange
    (MarkedIdealWithBoundary.mk T.base B (b ≫ T.structMap) IB T.mult EB) hTB L f A (E.hom.base y)
  have h3 : orderAt A
      ((Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f)).base (E.hom.base y))
      = orderAt A (a y) := by
    rw [← he]
    simp
  exact h1.trans (h2.trans h3)

theorem monomialPrincipalization_spec (hinv : ComapIsoInvariance.{u}) : MonomialPrincipalizationHypotheses hinv := by
  have h := isLocallyMonomialPrincipalization_monomialPrincipalization hG.monomialInputs hinv
      (orderAtBaseFieldChangeInvariance_of_geometryHypotheses_consolidated491 hG) (fun _ => True)
  exact
    { cert := fun T hTm i hi => h.cert T hTm trivial i hi
      center_nonempty := fun T hTm i hi => h.center_nonempty T hTm trivial i hi
      resolves := fun T hTm => h.resolves T hTm trivial
      trivial_of_coSupport_empty := fun T hTm hc => h.trivial_of_coSupport_empty T hTm trivial hc }

theorem isMaxOrderReduction_orderReductionSeq (hinv : ComapIsoInvariance.{u}) (n : ℕ)
    (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B) :
    IsMaxOrderReduction (fun d => d ≤ n) (fun T => orderReductionSeq hinv T (principalizationOfDimLe T A)) A := by
  have hmon : MonomialPrincipalizationHypotheses hinv := monomialPrincipalization_spec hG hinv
  refine
    { cert := fun T hT hdim i hi => certificate_orderReductionSeq hG hinv hmon hspec hT hdim i hi
      orderRed_equiv := fun T hT hdim hE hord =>
        orderReductionSeq_isomorphic_of_boundary_nil hG hinv hmon hspec hT hdim hE hord
      center_nonempty := fun T hT hdim i hi =>
        center_support_nonempty_orderReductionSeq hG hinv hmon hspec hT hdim i hi
      resolves := fun T hT hdim => isResolution_orderReductionSeq hG hinv hmon hspec hT hdim
      trivial_of_coSupport_empty := fun T hT hdim hc =>
        orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T A hc
      base_change := ?_
      base_change_strict := ?_
      smooth_pullback := ?_
      smooth_pullback_strict := ?_ }
  · intro T hT hdim L _ _ f E' hE hT' hdim'
    exact orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim L
      (baseChangeStructMap T L f) (baseChangeProj T L f) E' hE.symm hT' hdim'
      (baseChangeCompatible_baseChangeProj_of_isOrderReduction hG hinv n A B hspec T hT hdim L f)
  · intro T hT hdim L _ _ f E' hE hT' hdim'
    have hp := orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim L
      (baseChangeStructMap T L f) (baseChangeProj T L f) E' hE.symm hT' hdim'
      (baseChangeCompatible_baseChangeProj_of_isOrderReduction hG hinv n A B hspec T hT hdim L f)
    have hsurj : AlgebraicGeometry.Surjective (baseChangeProj T L f) :=
      instSurjectivePullbackFstSpecMapField T.base L f T.scheme T.structMap
    exact hp.isStrictPullback_of_surjective fun i hi =>
      (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp
        (center_support_nonempty_orderReductionSeq hG hinv hmon hspec hT hdim i hi)
  · intro T hT hdim Y q h hsm hq E' hE hT' hdim'
    have := hsm
    exact orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim T.base q h E'
      hE.symm hT' hdim' (baseChangeCompatible_of_smooth hG hinv n A B hspec T hT hdim h q hq)
  · intro T hT hdim Y q h hsm hsurj hq E' hE hT' hdim'
    have := hsm
    have := hsurj
    have hp := orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim T.base q h E'
      hE.symm hT' hdim' (baseChangeCompatible_of_smooth hG hinv n A B hspec T hT hdim h q hq)
    exact hp.isStrictPullback_of_surjective fun i hi =>
      (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp
        (center_support_nonempty_orderReductionSeq hG hinv hmon hspec hT hdim i hi)

theorem isMaxOrderReduction_canonicalAlgorithmRules (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (n : ℕ) (A B : PrincipalizationAssignment.{u})
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) :
    IsMaxOrderReduction (fun d => d ≤ n) ((canonicalAlgorithmRules hres).maxOrderFamily A) A :=
  isMaxOrderReduction_orderReductionSeq hG comapIsoInvariance n A B hspec


end

end MaxOrderReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorFamilyCenters
section


section

theorem divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (L : PrincipalizationAssignment.{u}) (j : ℕ) (T : MarkedIdealWithBoundary.{u}) :
    (canonicalAlgorithmRules hres).divisorFamily L j T =
      DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T (fun S _ => L S) j := by
  rw [PrincipalizationRules.divisorFamily_apply]
  rfl

private theorem support_imageIdealSheaf_nonempty_consolidated318 {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsClosedImmersion f) (J : X.IdealSheafData)
    (h : ((J.support : Set ↥X)).Nonempty) :
    (((imageIdealSheaf f J).support : Set ↥Y)).Nonempty := by
  have := hf
  obtain ⟨x, hx⟩ := h
  have hmem : x ∈ Set.range ⇑J.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hx
  obtain ⟨z, -⟩ := hmem
  refine ⟨(J.subschemeι ≫ f) z, ?_⟩
  rw [imageIdealSheaf_eq_ker, Scheme.Hom.support_ker]
  exact subset_closure (Set.mem_range_self z)

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})

theorem DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (L : PrincipalizationAssignment.{u}) (j : ℕ) (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme]
    (hV : T.IsAdmissible) (hj : j < T.boundary.length) (hO : T.IsOrderBoundedByMult)
    (hD : T.IsBalanced hV.locallyOfFiniteType)
    (hcs : orderAtLeastLocus T.ideal T.mult ≠ (∅ : Set ↥T.scheme)) :
    (DivisorReduction.containedComponentsIdeal T j hj = ⊤ ∧
        ∃ hpr : (MarkedBlowupSequenceData.ofMarkedSequence
            (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData.CentersContainNoComponent,
          ∃ _hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)
                (L (DivisorReduction.restrictToDivisor T j hj)) hpr).IsMarked
              T.structMap T.ideal T.mult T.boundary,
            ∀ hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)
                (L (DivisorReduction.restrictToDivisor T j hj)) hpr).IsMarked
              T.structMap T.ideal T.mult T.boundary,
              DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T (fun S _ => L S) j =
                ((DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                    (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)
                    (L (DivisorReduction.restrictToDivisor T j hj)) hpr).toMarkedBlowupSequenceData
                  T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups) ∨
      (DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ ∧
        ∃ hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj),
          ∃ hpr : (MarkedBlowupSequenceData.ofMarkedSequence
              (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData.CentersContainNoComponent,
            ∃ _hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                  (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
                  (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr)).IsMarked
                T.structMap T.ideal T.mult T.boundary,
              ∀ hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                  (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
                  (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr)).IsMarked
                T.structMap T.ideal T.mult T.boundary,
                DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T (fun S _ => L S) j =
                  ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                      (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                        (DivisorReduction.lowerIdealAfterBlowup T j hj)
                        (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
                        (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr)).toMarkedBlowupSequenceData
                    T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups) := by
  have hcsne : (orderAtLeastLocus T.ideal T.mult).Nonempty := Set.nonempty_iff_ne_empty.mpr hcs
  by_cases hZ : DivisorReduction.containedComponentsIdeal T j hj = ⊤
  · have hvalid := hfacts.valid_lowerTop T hV hO hD j hj hZ
    have hpr : (MarkedBlowupSequenceData.ofMarkedSequence
        (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData.CentersContainNoComponent :=
      hfacts.properCenters (DivisorReduction.restrictToDivisor T j hj) hvalid hvalid.one_le_mult
        (L (DivisorReduction.restrictToDivisor T j hj))
    refine Or.inl ⟨hZ, hpr,
      hfacts.isMarked_pushedTop T hV hO hD j hj hZ hvalid
        (L (DivisorReduction.restrictToDivisor T j hj)) hpr, ?_⟩
    intro hmk
    exact DivisorReduction.divisorReductionSeq_eq_of_containedComponentsIdeal_eq_top hres
      blowupPreservesNoetherian T (fun S _ => L S) j hj hcs hZ
      ⟨hfacts.lowerTriple_dim_lt T hV hcsne j hj (DivisorReduction.lowerIdealWithoutBlowup T)
        (DivisorReduction.lowerBoundaryWithoutBlowup T), inferInstance⟩ hpr hmk
  · have hb := hfacts.isBlowup_id_preIdeal T hV j hj
    have hvalid := hfacts.valid_lowerPre T hV hO hD j hj hZ
    have hpr : (MarkedBlowupSequenceData.ofMarkedSequence
        (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData.CentersContainNoComponent :=
      hfacts.properCenters (DivisorReduction.restrictTwistedToDivisor T j hj) hvalid hvalid.one_le_mult
        (L (DivisorReduction.restrictTwistedToDivisor T j hj))
    refine Or.inr ⟨hZ, hb, hpr,
      hfacts.isMarked_pushedPre T hV hO hD j hj hZ hb hvalid
        (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr, ?_⟩
    intro hmk
    exact DivisorReduction.divisorReductionSeq_eq_of_isBlowupAlongIdealSheaf hres
      blowupPreservesNoetherian T (fun S _ => L S) j hj hcs hZ hb
      ⟨hfacts.lowerTriple_dim_lt T hV hcsne j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
        (DivisorReduction.lowerBoundaryAfterBlowup T j hj), inferInstance⟩ hpr hmk

theorem DivisorReduction.divisorReductionSeq_center_nonempty (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ) (T : MarkedIdealWithBoundary.{u})
    (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hD : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) :
    ∀ i < (DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T
        (fun S _ => L S) j).length,
      (((DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T
          (fun S _ => L S) j).center i).support :
        Set ↥((DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T
          (fun S _ => L S) j).schemeAt i)).Nonempty := by
  have := DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)
  · rw [DivisorReduction.divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian T
      (fun S _ => L S) j hj hcs]
    intro i hi
    rw [emptyMarkedSequenceOfBlowups_length] at hi
    exact absurd hi (Nat.not_lt_zero i)
  · have hcsne : (orderAtLeastLocus T.ideal T.mult).Nonempty := Set.nonempty_iff_ne_empty.mpr hcs
    rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO hD hcs with
      ⟨hZ, hpr, hmk, heq⟩ | ⟨hZ, hb, hpr, hmk, heq⟩
    · have hvalid := hfacts.valid_lowerTop T hV hO hD j hj hZ
      have hdlt : (DivisorReduction.restrictToDivisor T j hj).krullDimSucc < n :=
        lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcsne j hj
          (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)) hdim
      have hlen : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)
          (L (DivisorReduction.restrictToDivisor T j hj)) hpr).length
          = (L (DivisorReduction.restrictToDivisor T j hj)).length := by
        have h := ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData
          hres blowupPreservesNoetherian hpr
        calc (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
              (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)
              (L (DivisorReduction.restrictToDivisor T j hj)) hpr).length
            = (MarkedBlowupSequenceData.ofMarkedSequence
                (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData.length := h
          _ = (L (DivisorReduction.restrictToDivisor T j hj)).length :=
              MarkedBlowupSequenceData.ofMarkedSequence_length _
      rw [heq hmk]
      intro i hi
      rw [MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length, hlen] at hi
      have hcenter : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
            (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)
            (L (DivisorReduction.restrictToDivisor T j hj)) hpr).center i
          = imageIdealSheaf (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
              (MarkedBlowupSequenceData.ofMarkedSequence
                (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData
              hres blowupPreservesNoetherian hpr i)
            ((L (DivisorReduction.restrictToDivisor T j hj)).center i) := by
        have h := ambientBlowupSequence_center (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData
          hres blowupPreservesNoetherian hpr i
        simp only [MarkedBlowupSequenceData.ofMarkedSequence_center] at h
        exact h
      simp only [MarkedBlowupSequenceData.toMarkedSequence_center, BlowupSequenceData.toMarkedBlowupSequenceData_center, hcenter]
      exact support_imageIdealSheaf_nonempty_consolidated318 _
        (isClosedImmersion_embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData
          hres blowupPreservesNoetherian hpr i) _
        (hL.center_nonempty (DivisorReduction.restrictToDivisor T j hj) hvalid hdlt i hi)
    · have hvalid := hfacts.valid_lowerPre T hV hO hD j hj hZ
      have hdlt : (DivisorReduction.restrictTwistedToDivisor T j hj).krullDimSucc < n :=
        lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcsne j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)) hdim
      have hlen : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
          (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr).length
          = (L (DivisorReduction.restrictTwistedToDivisor T j hj)).length := by
        have h := ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData
          hres blowupPreservesNoetherian hpr
        calc (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
              (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
              (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr).length
            = (MarkedBlowupSequenceData.ofMarkedSequence
                (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData.length := h
          _ = (L (DivisorReduction.restrictTwistedToDivisor T j hj)).length :=
              MarkedBlowupSequenceData.ofMarkedSequence_length _
      rw [heq hmk]
      intro i hi
      rw [MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length,
        BlowupSequenceData.prepend_length, hlen] at hi
      simp only [MarkedBlowupSequenceData.toMarkedSequence_center, BlowupSequenceData.toMarkedBlowupSequenceData_center]
      cases i with
      | zero =>
        rw [BlowupSequenceData.prepend_center_zero]
        refine Set.nonempty_iff_ne_empty.mpr ?_
        intro hE
        exact hZ ((Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).mpr hE)
      | succ k =>
        rw [BlowupSequenceData.prepend_center_succ]
        have hk : k < (L (DivisorReduction.restrictTwistedToDivisor T j hj)).length := Nat.lt_of_succ_lt_succ hi
        have hcenter : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
              (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
              (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr).center k
            = imageIdealSheaf (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
                (MarkedBlowupSequenceData.ofMarkedSequence
                  (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData
                hres blowupPreservesNoetherian hpr k)
              ((L (DivisorReduction.restrictTwistedToDivisor T j hj)).center k) := by
          have h := ambientBlowupSequence_center (T.boundary.get ⟨j, hj⟩).subschemeι
            (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData
            hres blowupPreservesNoetherian hpr k
          simp only [MarkedBlowupSequenceData.ofMarkedSequence_center] at h
          exact h
        rw [hcenter]
        exact support_imageIdealSheaf_nonempty_consolidated318 _
          (isClosedImmersion_embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
            (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData
            hres blowupPreservesNoetherian hpr k) _
          (hL.center_nonempty (DivisorReduction.restrictTwistedToDivisor T j hj) hvalid hdlt k hk)

theorem DivisorReduction.divisorReductionSeq_orderAt_le_mult (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (n : ℕ) (L : PrincipalizationAssignment.{u}) (j : ℕ) (T : MarkedIdealWithBoundary.{u})
    (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hD : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) :
    ∀ i ≤ (DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T (fun S _ => L S) j).length,
      ∀ x : ↥((DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T
          (fun S _ => L S) j).schemeAt i),
        orderAt ((DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T
          (fun S _ => L S) j).ideal i) x ≤ (T.mult : ℕ∞) := by
  have := DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)
  · rw [DivisorReduction.divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian T
      (fun S _ => L S) j hj hcs]
    intro i hi x
    rw [emptyMarkedSequenceOfBlowups_length] at hi
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    have hid : (emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary).ideal 0
        = T.ideal := by
      rw [MarkedSequenceOfBlowups.ideal_zero]
      exact Scheme.IdealSheafData.comap_id _
    rw [hid]
    exact (T.isOrderBoundedByMult_iff.mp hO) x
  · rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO hD hcs with
      ⟨hZ, hpr, hmk, heq⟩ | ⟨hZ, hb, hpr, hmk, heq⟩
    · have hvalid := hfacts.valid_lowerTop T hV hO hD j hj hZ
      have hlen : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)
          (L (DivisorReduction.restrictToDivisor T j hj)) hpr).length
          = (L (DivisorReduction.restrictToDivisor T j hj)).length := by
        have h := ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData
          hres blowupPreservesNoetherian hpr
        calc (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
              (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)
              (L (DivisorReduction.restrictToDivisor T j hj)) hpr).length
            = (MarkedBlowupSequenceData.ofMarkedSequence
                (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData.length := h
          _ = (L (DivisorReduction.restrictToDivisor T j hj)).length :=
              MarkedBlowupSequenceData.ofMarkedSequence_length _
      rw [heq hmk]
      intro i hi x
      rw [MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length, hlen] at hi
      simp only [MarkedBlowupSequenceData.toMarkedSequence_ideal, BlowupSequenceData.toMarkedBlowupSequenceData_ideal]
      exact hfacts.orderAt_ctrlIdeal_le_top T hV hO hD j hj hZ hvalid
        (L (DivisorReduction.restrictToDivisor T j hj)) hpr i hi x
    · have hvalid := hfacts.valid_lowerPre T hV hO hD j hj hZ
      have hlen : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
          (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr).length
          = (L (DivisorReduction.restrictTwistedToDivisor T j hj)).length := by
        have h := ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData
          hres blowupPreservesNoetherian hpr
        calc (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
              (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
              (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr).length
            = (MarkedBlowupSequenceData.ofMarkedSequence
                (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData.length := h
          _ = (L (DivisorReduction.restrictTwistedToDivisor T j hj)).length :=
              MarkedBlowupSequenceData.ofMarkedSequence_length _
      rw [heq hmk]
      intro i hi x
      rw [MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length,
        BlowupSequenceData.prepend_length, hlen] at hi
      simp only [MarkedBlowupSequenceData.toMarkedSequence_ideal, BlowupSequenceData.toMarkedBlowupSequenceData_ideal]
      exact hfacts.orderAt_ctrlIdeal_le_pre T hV hO hD j hj hZ hb hvalid
        (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr i hi x

theorem divisorFamily_canonicalAlgorithmRules_length_eq_zero (n : ℕ) (L : PrincipalizationAssignment.{u}) (j : ℕ) (T : MarkedIdealWithBoundary.{u})
    (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
    (_hD : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
    (hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)) :
    ((canonicalAlgorithmRules hres).divisorFamily L j T).length = 0 := by
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq,
    DivisorReduction.divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian T
      (fun S _ => L S) j hj hcs]
  exact emptyMarkedSequenceOfBlowups_length T.structMap T.ideal T.mult T.boundary

theorem divisorFamily_canonicalAlgorithmRules_center_nonempty (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ) (T : MarkedIdealWithBoundary.{u})
    (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hD : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) :
    ∀ i < ((canonicalAlgorithmRules hres).divisorFamily L j T).length,
      ((((canonicalAlgorithmRules hres).divisorFamily L j T).center i).support :
        Set ↥(((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt i)).Nonempty := by
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq]
  exact DivisorReduction.divisorReductionSeq_center_nonempty hres hfacts n L O hL j T hV hdim hO hD hj

theorem divisorFamily_canonicalAlgorithmRules_orderAt_le_mult (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (n : ℕ) (L : PrincipalizationAssignment.{u}) (j : ℕ) (T : MarkedIdealWithBoundary.{u})
    (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hD : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) :
    ∀ i ≤ ((canonicalAlgorithmRules hres).divisorFamily L j T).length,
      ∀ x : ↥(((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt i),
        orderAt (((canonicalAlgorithmRules hres).divisorFamily L j T).ideal i) x ≤ (T.mult : ℕ∞) := by
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq]
  exact DivisorReduction.divisorReductionSeq_orderAt_le_mult hres hfacts n L j T hV hdim hO hD hj


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
section


section

section
variable {α : Type*}

private theorem cons_take_succ_inj_consolidated319 (j : ℕ) (a b : α) (t₁ t₂ : List α)
    (h : List.take (j + 1) (a :: t₁) = List.take (j + 1) (b :: t₂)) :
    a = b ∧ List.take j t₁ = List.take j t₂ :=
  Eq.mp (List.cons.injEq a (List.take j t₁) b (List.take j t₂)) h

private theorem get_eq_get_of_take_add_one_eq_consolidated319 :
    ∀ (j : ℕ) (l₁ l₂ : List α), List.take (j + 1) l₁ = List.take (j + 1) l₂ →
      ∀ (h₁ : j < l₁.length) (h₂ : j < l₂.length), l₁.get ⟨j, h₁⟩ = l₂.get ⟨j, h₂⟩ := by
  intro j
  induction j with
  | zero =>
    intro l₁ l₂ htake h₁ h₂
    cases l₁ with
    | nil => exact absurd h₁ (Nat.not_lt_zero 0)
    | cons a t₁ =>
      cases l₂ with
      | nil => exact absurd h₂ (Nat.not_lt_zero 0)
      | cons b t₂ => exact (cons_take_succ_inj_consolidated319 0 a b t₁ t₂ htake).1
  | succ j ih =>
    intro l₁ l₂ htake h₁ h₂
    cases l₁ with
    | nil => exact absurd h₁ (Nat.not_lt_zero (j + 1))
    | cons a t₁ =>
      cases l₂ with
      | nil => exact absurd h₂ (Nat.not_lt_zero (j + 1))
      | cons b t₂ =>
        exact ih t₁ t₂ (cons_take_succ_inj_consolidated319 (j + 1) a b t₁ t₂ htake).2
          (Nat.lt_of_succ_lt_succ h₁) (Nat.lt_of_succ_lt_succ h₂)

theorem get_eq_get_of_take_succ_eq (l₁ l₂ : List α) (j : ℕ)
    (htake : List.take (j + 1) l₁ = List.take (j + 1) l₂)
    (h₁ : j < l₁.length) (h₂ : j < l₂.length) :
    l₁.get ⟨j, h₁⟩ = l₂.get ⟨j, h₂⟩ :=
  get_eq_get_of_take_add_one_eq_consolidated319 j l₁ l₂ htake h₁ h₂


end

section
variable {X Y : Scheme.{u}} (f : Y ⟶ X)

private theorem nontrivialPart_map_comap_consolidated319 (l : List X.IdealSheafData) :
    MarkedIdealWithBoundary.nontrivialPart (l.map fun D => D.comap f) =
      MarkedIdealWithBoundary.nontrivialPart ((MarkedIdealWithBoundary.nontrivialPart l).map fun D => D.comap f) := by
  unfold MarkedIdealWithBoundary.nontrivialPart
  induction l with
  | nil => simp
  | cons D l ih =>
    by_cases hD : D = ⊤
    · subst hD
      simp [AlgebraicGeometry.Scheme.IdealSheafData.comap_top, ih]
    · simp [List.filter_cons, hD, ih]

theorem MarkedIdealWithBoundary.SameNontrivialBoundary.comap {E E' : List X.IdealSheafData} (h : MarkedIdealWithBoundary.SameNontrivialBoundary E E') :
    MarkedIdealWithBoundary.SameNontrivialBoundary (E.map fun D => D.comap f) (E'.map fun D => D.comap f) := by
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff] at h ⊢
  rw [nontrivialPart_map_comap_consolidated319 f E, nontrivialPart_map_comap_consolidated319 f E', h]


end

section
variable {X : Scheme.{u}} {a : X.IdealSheafData} {s t : List X.IdealSheafData}

private theorem nontrivialPart_cons_congr_consolidated319 (h : MarkedIdealWithBoundary.nontrivialPart s = MarkedIdealWithBoundary.nontrivialPart t) :
    MarkedIdealWithBoundary.nontrivialPart (a :: s) = MarkedIdealWithBoundary.nontrivialPart (a :: t) := by
  simp only [MarkedIdealWithBoundary.nontrivialPart] at h
  simp only [MarkedIdealWithBoundary.nontrivialPart]
  rw [List.filter_cons, List.filter_cons, h]

private theorem nontrivialPart_eq_of_cons_eq_consolidated319 (h : MarkedIdealWithBoundary.nontrivialPart (a :: s) = MarkedIdealWithBoundary.nontrivialPart (a :: t)) :
    MarkedIdealWithBoundary.nontrivialPart s = MarkedIdealWithBoundary.nontrivialPart t := by
  simp only [MarkedIdealWithBoundary.nontrivialPart] at h
  simp only [MarkedIdealWithBoundary.nontrivialPart]
  rw [List.filter_cons, List.filter_cons] at h
  split_ifs at h with hp
  · simpa using h
  · exact h


end

section
variable {X : Scheme.{u}}

private theorem nontrivialPart_eraseIdx_eq_of_take_succ_eq_consolidated319 (j : ℕ) :
    ∀ E E' : List X.IdealSheafData,
      MarkedIdealWithBoundary.nontrivialPart E = MarkedIdealWithBoundary.nontrivialPart E' →
      List.take (j + 1) E = List.take (j + 1) E' →
      MarkedIdealWithBoundary.nontrivialPart (E.eraseIdx j) = MarkedIdealWithBoundary.nontrivialPart (E'.eraseIdx j) := by
  induction j with
  | zero =>
    intro E E' h htake
    cases E with
    | nil =>
      cases E' with
      | nil => rfl
      | cons b t => simp at htake
    | cons a s =>
      cases E' with
      | nil => simp at htake
      | cons b t =>
        rw [List.take_succ_cons, List.take_succ_cons, List.cons.injEq] at htake
        obtain ⟨hab, -⟩ := htake
        subst hab
        exact nontrivialPart_eq_of_cons_eq_consolidated319 h
  | succ j ih =>
    intro E E' h htake
    cases E with
    | nil =>
      cases E' with
      | nil => rfl
      | cons b t => simp at htake
    | cons a s =>
      cases E' with
      | nil => simp at htake
      | cons b t =>
        rw [List.take_succ_cons, List.take_succ_cons, List.cons.injEq] at htake
        obtain ⟨hab, htl⟩ := htake
        subst hab
        exact nontrivialPart_cons_congr_consolidated319 (ih s t (nontrivialPart_eq_of_cons_eq_consolidated319 h) htl)

theorem MarkedIdealWithBoundary.SameNontrivialBoundary.eraseIdx {E E' : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary E E') (j : ℕ)
    (htake : List.take (j + 1) E = List.take (j + 1) E') :
    MarkedIdealWithBoundary.SameNontrivialBoundary (E.eraseIdx j) (E'.eraseIdx j) :=
  (MarkedIdealWithBoundary.sameNontrivialBoundary_iff _ _).2
    (nontrivialPart_eraseIdx_eq_of_take_succ_eq_consolidated319 j E E' ((MarkedIdealWithBoundary.sameNontrivialBoundary_iff _ _).1 h) htake)


end

theorem surjective_snd_of_isPullback_of_surjective {X Y S S' : Scheme.{u}} (σ : S ⟶ X) (σ' : S' ⟶ Y) (φ : Y ⟶ X)
    (ψ : S' ⟶ S) [AlgebraicGeometry.Surjective φ] (hpb : IsPullback σ' ψ φ σ) :
    AlgebraicGeometry.Surjective ψ := by
  have hφ : AlgebraicGeometry.Surjective φ := inferInstance
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hφ

namespace DivisorReduction

section
variable {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData) (D' : Y.IdealSheafData) (hD : D' = D.comap h)
include hD

private theorem ker_subschemeι_le_ker_comp_consolidated319 :
    Scheme.Hom.ker D.subschemeι ≤ Scheme.Hom.ker (D'.subschemeι ≫ h) := by
  subst hD
  rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι, AlgebraicGeometry.Scheme.Hom.ker_comp,
    AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]
  exact AlgebraicGeometry.Scheme.IdealSheafData.le_map_comap D h

private theorem exists_subscheme_hom_comp_subschemeι_eq_consolidated319 :
    ∃ g : D'.subscheme ⟶ D.subscheme,
      g ≫ D.subschemeι = D'.subschemeι ≫ h ∧
        ∀ I₀ : X.IdealSheafData,
          (I₀.comap D.subschemeι).comap g = (I₀.comap h).comap D'.subschemeι := by
  have hsq : AlgebraicGeometry.IsClosedImmersion.lift D.subschemeι (D'.subschemeι ≫ h)
      (ker_subschemeι_le_ker_comp_consolidated319 h D D' hD) ≫ D.subschemeι = D'.subschemeι ≫ h :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac ..
  refine ⟨AlgebraicGeometry.IsClosedImmersion.lift D.subschemeι (D'.subschemeι ≫ h)
      (ker_subschemeι_le_ker_comp_consolidated319 h D D' hD), hsq, fun I₀ => ?_⟩
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hsq,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_comp]


end

def subschemeMapOfComap {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData) (D' : Y.IdealSheafData)
    (hD : D' = D.comap h) : D'.subscheme ⟶ D.subscheme :=
  (exists_subscheme_hom_comp_subschemeι_eq_consolidated319 h D D' hD).choose

section
variable {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData) (D' : Y.IdealSheafData) (hD : D' = D.comap h)

theorem subschemeMapOfComap_comp :
    subschemeMapOfComap h D D' hD ≫ D.subschemeι = D'.subschemeι ≫ h :=
  (exists_subscheme_hom_comp_subschemeι_eq_consolidated319 h D D' hD).choose_spec.1

theorem comap_subschemeMapOfComap (I₀ : X.IdealSheafData) :
    (I₀.comap D.subschemeι).comap (subschemeMapOfComap h D D' hD) = (I₀.comap h).comap D'.subschemeι :=
  (exists_subscheme_hom_comp_subschemeι_eq_consolidated319 h D D' hD).choose_spec.2 I₀

private theorem map_comap_comap_subschemeι_consolidated319 (M : List X.IdealSheafData) :
    ((M.map fun I => I.comap h).map fun I => I.comap D'.subschemeι)
      = (M.map fun I => I.comap D.subschemeι).map fun I => I.comap (subschemeMapOfComap h D D' hD) := by
  induction M with
  | nil => rfl
  | cons I t ih =>
    simp only [List.map_cons]
    rw [comap_subschemeMapOfComap h D D' hD I, ih]

theorem sameNontrivialBoundary_comap_subschemeι (M : List X.IdealSheafData)
    (M' : List Y.IdealSheafData)
    (hM : MarkedIdealWithBoundary.SameNontrivialBoundary M' (M.map fun I => I.comap h)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary (M'.map fun I => I.comap D'.subschemeι)
      ((M.map fun I => I.comap D.subschemeι).map fun I => I.comap (subschemeMapOfComap h D D' hD)) := by
  rw [← map_comap_comap_subschemeι_consolidated319 h D D' hD M]
  exact hM.comap D'.subschemeι


end

def componentsInOrderLocusIdeal {X : Scheme.{u}} (I : X.IdealSheafData) (m : ℕ) (D : X.IdealSheafData) :
    X.IdealSheafData :=
  @dite X.IdealSheafData
    (IsOpen {x : ↥D.subscheme | connectedComponent x ⊆ ⇑D.subschemeι ⁻¹' orderAtLeastLocus I m})
    (Classical.propDecidable _)
    (fun hop =>
      Scheme.Hom.ker
        (Scheme.Opens.ι
            ({ carrier := {x : ↥D.subscheme |
                  connectedComponent x ⊆ ⇑D.subschemeι ⁻¹' orderAtLeastLocus I m},
                is_open' := hop } : D.subscheme.Opens) ≫
          D.subschemeι))
    (fun _ => ⊤)

theorem containedComponentsIdeal_eq_componentsInOrderLocusIdeal (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) :
    containedComponentsIdeal T j hj = componentsInOrderLocusIdeal T.ideal T.mult (T.boundary.get ⟨j, hj⟩) := by
  unfold componentsInOrderLocusIdeal
  split_ifs with h
  · exact containedComponentsIdeal_eq_ker T j hj h
  · exact containedComponentsIdeal_eq_top_of_not_isOpen T j hj h

structure SmoothPullbackCompatibility : Prop where
  comap_ne_top : ∀ (X Y : Scheme.{u}) (h : Y ⟶ X) [AlgebraicGeometry.Surjective h]
    (Z : X.IdealSheafData), Z ≠ ⊤ → Z.comap h ≠ ⊤
  coSupport_comap : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
      ∀ m : ℕ, orderAtLeastLocus (T.ideal.comap h) m = ⇑h ⁻¹' orderAtLeastLocus T.ideal m
  isPullback_inducedHom : ∀ (X Y : Scheme.{u}) (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h),
      IsPullback (subschemeMapOfComap h D D' hD) D'.subschemeι D.subschemeι h
  smooth_of_isPullback : ∀ (X Y S S' : Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y) (φ : Y ⟶ X)
    (ψ : S' ⟶ S), IsPullback σ' ψ φ σ → Smooth φ → Smooth ψ
  lowerIdealPre_comap : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
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
              (lowerIdealAfterBlowup T j hj).comap h
  boundaryEquiv_restrictedBoundary_comap : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
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
                (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j)))
  preIdeal_comap : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
      ∀ (E' : List Y.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
        ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
          List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
          ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
            containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = (containedComponentsIdeal T j hj).comap h

def divisorPullbackMap (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData) (Y : Scheme.{u})
    (h : Y ⟶ T.scheme) (D' : Y.IdealSheafData) (hD : D' = (T.boundary.get ⟨j, hj⟩).comap h) :
    D'.subscheme ⟶ (restrictToBoundaryDivisor T j hj I₀ E₀).scheme :=
  subschemeMapOfComap h (T.boundary.get ⟨j, hj⟩) D' hD

theorem isPullback_divisorPullbackMap (hbc : SmoothPullbackCompatibility.{u}) (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData)
    (E₀ : List T.scheme.IdealSheafData) (Y : Scheme.{u}) (h : Y ⟶ T.scheme)
    (D' : Y.IdealSheafData) (hD : D' = (T.boundary.get ⟨j, hj⟩).comap h) :
    IsPullback (divisorPullbackMap T j hj I₀ E₀ Y h D' hD) D'.subschemeι
      (T.boundary.get ⟨j, hj⟩).subschemeι h :=
  hbc.isPullback_inducedHom _ _ h _ D' hD

theorem get_eq_comap_get_boundary (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) (E' : List Y.IdealSheafData)
    (hjE : j < E'.length)
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary) :
    E'.get ⟨j, hjE⟩ = (T.boundary.get ⟨j, hj⟩).comap h := by
  have hb : (T.pullbackAlong Y q h).boundary = List.map (fun D => D.comap h) T.boundary :=
    MarkedIdealWithBoundary.pullbackAlong_boundary T Y q h
  have htake' : List.take (j + 1) E' =
      List.take (j + 1) (List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary) := by
    rw [htake, hb]
    rfl
  have hlen : j < (List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary).length := by
    simpa using hj
  rw [get_eq_get_of_take_succ_eq E'
    (List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary) j htake' hjE hlen]
  simp

private theorem componentsInOrderLocusIdeal_congr_consolidated319 {X : Scheme.{u}} (I : X.IdealSheafData) (m : ℕ)
    {D D' : X.IdealSheafData} (hD : D = D') :
    componentsInOrderLocusIdeal I m D = componentsInOrderLocusIdeal I m D' := by
  rw [hD]

theorem containedComponentsIdeal_withBoundary (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) (E' : List Y.IdealSheafData)
    (hjE : j < E'.length) (hj' : j < (T.pullbackAlong Y q h).boundary.length)
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary) :
    containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE =
      containedComponentsIdeal (T.pullbackAlong Y q h) j hj' := by
  have hget : E'.get ⟨j, hjE⟩ = ((T.pullbackAlong Y q h).boundary).get ⟨j, hj'⟩ :=
    get_eq_get_of_take_succ_eq E' ((T.pullbackAlong Y q h).boundary) j htake hjE hj'
  rw [containedComponentsIdeal_eq_componentsInOrderLocusIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE,
    containedComponentsIdeal_eq_componentsInOrderLocusIdeal (T.pullbackAlong Y q h) j hj']
  exact componentsInOrderLocusIdeal_congr_consolidated319 _ _ hget

section
variable (hbc : SmoothPullbackCompatibility.{u})
include hbc

theorem comap_ne_top_of_surjective {X Y : Scheme.{u}} (h : Y ⟶ X)
    [AlgebraicGeometry.Surjective h] (Z : X.IdealSheafData) (hZ : Z ≠ ⊤) : Z.comap h ≠ ⊤ :=
  hbc.comap_ne_top _ _ h Z hZ

theorem orderAtLeastLocus_withBoundary_pullbackAlong (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [Smooth h] (hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
    (m : ℕ) :
    orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal m = ⇑h ⁻¹' orderAtLeastLocus T.ideal m :=
  hbc.coSupport_comap T hV Y q h hq m


end

theorem lowerIdealWithoutBlowup_withBoundary (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) (E' : List Y.IdealSheafData) :
    lowerIdealWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E') = (lowerIdealWithoutBlowup T).comap h := by
  have h1 : ((T.pullbackAlong Y q h).withBoundary E').ideal = (T.pullbackAlong Y q h).ideal :=
    MarkedIdealWithBoundary.withBoundary_ideal (T.pullbackAlong Y q h) E'
  have h2 : (T.pullbackAlong Y q h).ideal = T.ideal.comap h :=
    MarkedIdealWithBoundary.pullbackAlong_ideal T Y q h
  simp [lowerIdealWithoutBlowup, h1, h2]
  exact AlgebraicGeometry.Scheme.IdealSheafData.comap_id ..

private theorem take_length_sub_one_eraseIdx_consolidated319 {α : Type*} (l : List α) (j : ℕ) (hj : j < l.length) :
    List.take (l.length - 1) (l.eraseIdx j) = l.eraseIdx j := by
  refine List.take_of_length_le ?_
  have h2 := List.length_eraseIdx_add_one hj
  omega

theorem sameNontrivialBoundary_lowerBoundaryWithoutBlowup (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    (E' : List Y.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary)
    (hjE : j < E'.length) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (E'.length - 1)
        ((lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E')).eraseIdx j))
      (List.map (fun D => D.comap h)
        (List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j))) := by
  have hpb : List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary
      = ((T.pullbackAlong Y q h).boundary : List Y.IdealSheafData) :=
    (MarkedIdealWithBoundary.pullbackAlong_boundary T Y q h).symm
  have hBE' : MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary) E' :=
    (MarkedIdealWithBoundary.sameNontrivialBoundary_iff _ _).2
      ((congrArg (fun l : List Y.IdealSheafData => MarkedIdealWithBoundary.nontrivialPart l) hpb).trans
        ((MarkedIdealWithBoundary.sameNontrivialBoundary_iff _ _).1 hBE))
  have htake' : List.take (j + 1) E'
      = List.take (j + 1) (List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary) :=
    htake.trans (congrArg (fun l : List Y.IdealSheafData => List.take (j + 1) l) hpb.symm)
  have hmid : MarkedIdealWithBoundary.nontrivialPart (E'.eraseIdx j)
      = MarkedIdealWithBoundary.nontrivialPart
        ((List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary).eraseIdx j) :=
    (MarkedIdealWithBoundary.sameNontrivialBoundary_iff _ _).1 (hBE'.symm.eraseIdx j htake')
  have hmap : (List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary).eraseIdx j
      = List.map (fun D : T.scheme.IdealSheafData => D.comap h) (T.boundary.eraseIdx j) :=
    List.eraseIdx_map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary j
  have hA0 : ((lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E')) : List Y.IdealSheafData)
      = E' :=
    (lowerBoundaryWithoutBlowup_eq ((T.pullbackAlong Y q h).withBoundary E')).trans
      (MarkedIdealWithBoundary.withBoundary_boundary (T.pullbackAlong Y q h) E')
  have hLeq : List.take (E'.length - 1)
        (((lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E')) :
          List Y.IdealSheafData).eraseIdx j)
      = E'.eraseIdx j :=
    (congrArg (fun l : List Y.IdealSheafData =>
        List.take (E'.length - 1) (l.eraseIdx j)) hA0).trans
      (take_length_sub_one_eraseIdx_consolidated319 E' j hjE)
  have hCeq : List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j)
      = T.boundary.eraseIdx j :=
    (congrArg (fun l : List T.scheme.IdealSheafData =>
        List.take (T.boundary.length - 1) (l.eraseIdx j)) (lowerBoundaryWithoutBlowup_eq T)).trans
      (take_length_sub_one_eraseIdx_consolidated319 T.boundary j hj)
  exact (MarkedIdealWithBoundary.sameNontrivialBoundary_iff _ _).2
    (((congrArg (fun l : List Y.IdealSheafData => MarkedIdealWithBoundary.nontrivialPart l) hLeq).trans
        (hmid.trans
          (congrArg (fun l : List Y.IdealSheafData => MarkedIdealWithBoundary.nontrivialPart l) hmap))).trans
      (congrArg (fun l : List T.scheme.IdealSheafData =>
          MarkedIdealWithBoundary.nontrivialPart
            (List.map (fun D : T.scheme.IdealSheafData => D.comap h) l)) hCeq.symm))

theorem isBlowupAlongIdealSheaf_id_comap_containedComponentsIdeal (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) (j : ℕ)
    (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base))
    (h : Y ⟶ T.scheme) (E' : List Y.IdealSheafData)
    (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible) (hj : j < T.boundary.length)
    (hjE : j < E'.length)
    (heq : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = (containedComponentsIdeal T j hj).comap h) :
    Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) ((containedComponentsIdeal T j hj).comap h) := by
  rw [← heq]
  exact hfacts.isBlowup_id_preIdeal _ hV' j hjE

private theorem heq_toSequenceOfBlowups_of_eq_consolidated319 (L : PrincipalizationAssignment.{u}) {S₁ S₂ : MarkedIdealWithBoundary.{u}}
    (hS : S₁ = S₂) : HEq (L S₁).toSequenceOfBlowups (L S₂).toSequenceOfBlowups := by
  cases hS
  exact HEq.refl _

private theorem isStrictPullbackSequenceOfBlowups_of_heq_consolidated319 {X' X : Scheme.{u}} (φ : X' ⟶ X) (B : SequenceOfBlowups X)
    {B₁ B₂ : SequenceOfBlowups X'} (hB : HEq B₁ B₂) (h : IsStrictPullbackBlowupSeq φ B₁ B) :
    IsStrictPullbackBlowupSeq φ B₂ B := by
  have hB' : B₁ = B₂ := eq_of_heq hB
  rw [← hB']
  exact h

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ) (hbc : SmoothPullbackCompatibility.{u}) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult) (hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) (hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty) (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [Smooth h] [AlgebraicGeometry.Surjective h] (hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData) (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E') (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary) (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible) (hdim' : ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc ≤ n) (hO' : ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult) (hDB' : ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType) (hjE : j < E'.length) (hcs' : (orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult).Nonempty)
include hfacts hL hbc hdim hO hbal hcs hq hBE hdim' hO' hDB' hcs'

theorem isStrictPullbackBlowupSeq_restrictToDivisor_of_eq_top (hZ : containedComponentsIdeal T j hj = ⊤)
    (hZ' : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = ⊤) :
    IsStrictPullbackBlowupSeq
      (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩)
        (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
      (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE)).toSequenceOfBlowups
      (L (restrictToDivisor T j hj)).toSequenceOfBlowups := by
  have hD : E'.get ⟨j, hjE⟩ = (T.boundary.get ⟨j, hj⟩).comap h :=
    get_eq_comap_get_boundary T j hj Y q h E' hjE htake
  have hpb : IsPullback
      (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩) hD)
      (E'.get ⟨j, hjE⟩).subschemeι (T.boundary.get ⟨j, hj⟩).subschemeι h :=
    isPullback_divisorPullbackMap hbc T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
      (E'.get ⟨j, hjE⟩) hD
  have hsm : Smooth
      (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩) hD) :=
    hbc.smooth_of_isPullback T.scheme Y (T.boundary.get ⟨j, hj⟩).subscheme
      (E'.get ⟨j, hjE⟩).subscheme (T.boundary.get ⟨j, hj⟩).subschemeι
      (E'.get ⟨j, hjE⟩).subschemeι h
      (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩) hD)
      hpb.flip inferInstance
  have hsj : AlgebraicGeometry.Surjective
      (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩) hD) :=
    surjective_snd_of_isPullback_of_surjective (T.boundary.get ⟨j, hj⟩).subschemeι (E'.get ⟨j, hjE⟩).subschemeι h
      (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩) hD)
      hpb.flip
  have hq₀ : (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
        (E'.get ⟨j, hjE⟩) hD) ≫ (restrictToDivisor T j hj).structMap
      = (E'.get ⟨j, hjE⟩).subschemeι ≫ q := by
    have key : subschemeMapOfComap h (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hD ≫
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
          = (E'.get ⟨j, hjE⟩).subschemeι ≫ q := by
      rw [← Category.assoc, subschemeMapOfComap_comp, Category.assoc, hq]
    exact key
  have hideal : ((restrictToDivisor T j hj).ideal).comap
        (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩) hD)
      = (lowerIdealWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E')).comap
          (E'.get ⟨j, hjE⟩).subschemeι := by
    rw [lowerIdealWithoutBlowup_withBoundary T Y q h E']
    exact comap_subschemeMapOfComap h (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hD (lowerIdealWithoutBlowup T)
  have hTriple : ((restrictToDivisor T j hj).pullbackAlong (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
          (E'.get ⟨j, hjE⟩) hD)).withBoundary
        ((restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary)
      = restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE :=
    congrArg
      (fun J => T.withSchemeIdealBoundary (E'.get ⟨j, hjE⟩).subscheme ((E'.get ⟨j, hjE⟩).subschemeι ≫ q) J
        ((restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary)) hideal
  have hBE₀ : MarkedIdealWithBoundary.SameNontrivialBoundary
      (((restrictToDivisor T j hj).pullbackAlong (E'.get ⟨j, hjE⟩).subscheme
          ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
          (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
            (E'.get ⟨j, hjE⟩) hD)).boundary)
      ((restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary) := by
    rw [MarkedIdealWithBoundary.pullbackAlong_boundary]
    exact (sameNontrivialBoundary_comap_subschemeι h (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hD
      (List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j))
      (List.take (E'.length - 1)
        ((lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E')).eraseIdx j))
      (sameNontrivialBoundary_lowerBoundaryWithoutBlowup T j hj Y q h E' hBE htake hjE)).symm
  have hValid₀ : (((restrictToDivisor T j hj).pullbackAlong (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
          (E'.get ⟨j, hjE⟩) hD)).withBoundary
        ((restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary)).IsAdmissible := by
    rw [hTriple]
    exact hfacts.valid_lowerTop ((T.pullbackAlong Y q h).withBoundary E') hV' hO' hDB' j hjE hZ'
  have hdim₀ : (((restrictToDivisor T j hj).pullbackAlong (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
          (E'.get ⟨j, hjE⟩) hD)).withBoundary
        ((restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary)).krullDimSucc < n := by
    rw [hTriple]
    exact lt_of_lt_of_le
      (hfacts.lowerTriple_dim_lt ((T.pullbackAlong Y q h).withBoundary E') hV' hcs' j hjE
        (lowerIdealWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))
        (lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))) hdim'
  have hmain := hL.smooth_pullback_strict (restrictToDivisor T j hj)
    (hfacts.valid_lowerTop T hV hO hbal j hj hZ)
    (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcs j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T))
      hdim)
    (E'.get ⟨j, hjE⟩).subscheme ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
    (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩) hD)
    hq₀ ((restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary) hBE₀ hValid₀ hdim₀
  exact isStrictPullbackSequenceOfBlowups_of_heq_consolidated319 _ _ (heq_toSequenceOfBlowups_of_eq_consolidated319 L hTriple) hmain

theorem isStrictPullbackBlowupSeq_restrictTwistedToDivisor (hZ : containedComponentsIdeal T j hj ≠ ⊤)
    (hZ' : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE =
      (containedComponentsIdeal T j hj).comap h) :
    IsStrictPullbackBlowupSeq
      (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h (E'.get ⟨j, hjE⟩)
        (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
      (L (restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE)).toSequenceOfBlowups
      (L (restrictTwistedToDivisor T j hj)).toSequenceOfBlowups := by
  have hD : E'.get ⟨j, hjE⟩ = (T.boundary.get ⟨j, hj⟩).comap h :=
    get_eq_comap_get_boundary T j hj Y q h E' hjE htake
  have hZ'ne : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE ≠ ⊤ := by
    rw [hZ']
    exact comap_ne_top_of_surjective hbc h (containedComponentsIdeal T j hj) hZ
  have hpb : IsPullback
      (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
        (E'.get ⟨j, hjE⟩) hD)
      (E'.get ⟨j, hjE⟩).subschemeι (T.boundary.get ⟨j, hj⟩).subschemeι h :=
    isPullback_divisorPullbackMap hbc T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
      (E'.get ⟨j, hjE⟩) hD
  have hsm : Smooth
      (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
        (E'.get ⟨j, hjE⟩) hD) :=
    hbc.smooth_of_isPullback T.scheme Y (T.boundary.get ⟨j, hj⟩).subscheme
      (E'.get ⟨j, hjE⟩).subscheme (T.boundary.get ⟨j, hj⟩).subschemeι
      (E'.get ⟨j, hjE⟩).subschemeι h
      (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
        (E'.get ⟨j, hjE⟩) hD)
      hpb.flip inferInstance
  have hsj : AlgebraicGeometry.Surjective
      (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
        (E'.get ⟨j, hjE⟩) hD) :=
    surjective_snd_of_isPullback_of_surjective (T.boundary.get ⟨j, hj⟩).subschemeι (E'.get ⟨j, hjE⟩).subschemeι h
      (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
        (E'.get ⟨j, hjE⟩) hD)
      hpb.flip
  have hq₀ : (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
        (E'.get ⟨j, hjE⟩) hD) ≫ (restrictTwistedToDivisor T j hj).structMap
      = (E'.get ⟨j, hjE⟩).subschemeι ≫ q := by
    have key : subschemeMapOfComap h (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hD ≫
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
          = (E'.get ⟨j, hjE⟩).subschemeι ≫ q := by
      rw [← Category.assoc, subschemeMapOfComap_comp, Category.assoc, hq]
    exact key
  have hideal : ((restrictTwistedToDivisor T j hj).ideal).comap
        (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
          (E'.get ⟨j, hjE⟩) hD)
      = (lowerIdealAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE).comap
          (E'.get ⟨j, hjE⟩).subschemeι := by
    rw [hbc.lowerIdealPre_comap T hV Y q h hq E' hBE j hj hjE htake hV' hO hZ']
    exact comap_subschemeMapOfComap h (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hD (lowerIdealAfterBlowup T j hj)
  have hTriple : ((restrictTwistedToDivisor T j hj).pullbackAlong (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
          (E'.get ⟨j, hjE⟩) hD)).withBoundary
        ((restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary)
      = restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE :=
    congrArg
      (fun J => T.withSchemeIdealBoundary (E'.get ⟨j, hjE⟩).subscheme ((E'.get ⟨j, hjE⟩).subschemeι ≫ q) J
        ((restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary)) hideal
  have hBE₀ : MarkedIdealWithBoundary.SameNontrivialBoundary
      (((restrictTwistedToDivisor T j hj).pullbackAlong (E'.get ⟨j, hjE⟩).subscheme
          ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
          (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
            (E'.get ⟨j, hjE⟩) hD)).boundary)
      ((restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary) := by
    rw [MarkedIdealWithBoundary.pullbackAlong_boundary]
    exact (sameNontrivialBoundary_comap_subschemeι h (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hD
      (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j))
      (List.take (E'.length - 1)
        ((lowerBoundaryAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE).eraseIdx j))
      (hbc.boundaryEquiv_restrictedBoundary_comap T hV Y q h hq E' hBE j hj hjE htake hV' hO hZ')).symm
  have hValid₀ : (((restrictTwistedToDivisor T j hj).pullbackAlong (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
          (E'.get ⟨j, hjE⟩) hD)).withBoundary
        ((restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary)).IsAdmissible := by
    rw [hTriple]
    exact hfacts.valid_lowerPre ((T.pullbackAlong Y q h).withBoundary E') hV' hO' hDB' j hjE hZ'ne
  have hdim₀ : (((restrictTwistedToDivisor T j hj).pullbackAlong (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
          (E'.get ⟨j, hjE⟩) hD)).withBoundary
        ((restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary)).krullDimSucc < n := by
    rw [hTriple]
    exact lt_of_lt_of_le
      (hfacts.lowerTriple_dim_lt ((T.pullbackAlong Y q h).withBoundary E') hV' hcs' j hjE
        (lowerIdealAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE)
        (lowerBoundaryAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE)) hdim'
  have hmain := hL.smooth_pullback_strict (restrictTwistedToDivisor T j hj)
    (hfacts.valid_lowerPre T hV hO hbal j hj hZ)
    (lt_of_lt_of_le
      (hfacts.lowerTriple_dim_lt T hV hcs j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj))
      hdim)
    (E'.get ⟨j, hjE⟩).subscheme ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
    (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h (E'.get ⟨j, hjE⟩) hD)
    hq₀ ((restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE).boundary) hBE₀ hValid₀ hdim₀
  exact isStrictPullbackSequenceOfBlowups_of_heq_consolidated319 _ _ (heq_toSequenceOfBlowups_of_eq_consolidated319 L hTriple) hmain


end

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionPushforward
section


section

private theorem isPushforwardBlowupSeq_of_ofSequenceOfBlowups_consolidated343 {S X : Scheme.{u}} (ι : S ⟶ X) [IsClosedImmersion ι]
    (B : SequenceOfBlowups S) (B' : SequenceOfBlowups X)
    (h : IsPushforwardBlowupSeq ι (BlowupSequenceData.ofSequenceOfBlowups B).toSequenceOfBlowups B') : IsPushforwardBlowupSeq ι B B' := by
  unfold IsPushforwardBlowupSeq at h ⊢
  simp only [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism] at h
  exact h

private theorem heq_toSequenceOfBlowups_of_eq_consolidated343 (L : PrincipalizationAssignment.{u}) {A B : MarkedIdealWithBoundary.{u}} (h : A = B) :
    HEq ((L A).toSequenceOfBlowups) ((L B).toSequenceOfBlowups) := by
  subst h
  rfl

theorem isPushforwardSequenceOfBlowups_of_length_eq_zero {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X)
    (hlenZero : BS.length = 0) (hB : B.length = 0) :
    IsPushforwardBlowupSeq ι BS B := by
  have key : ∀ i : ℕ, i ≤ BS.length → i = 0 := by
    intro i hi
    omega
  unfold IsPushforwardBlowupSeq
  refine ⟨by omega, fun i hi =>
      eqToHom (congrArg BS.schemeAt (key i hi)) ≫ BS.isoZero.hom ≫ ι ≫ B.isoZero.inv ≫
        eqToHom (congrArg B.schemeAt (key i hi)).symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro i _
    infer_instance
  · simp
  · intro i hi
    exact absurd hi (by omega)
  · intro i hi
    exact absurd hi (by omega)
  · intro i hi
    exact absurd hi (by omega)

theorem isPushforwardBlowupSeq_toSequenceOfBlowups_of_ofMarkedSequence (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups)
    {Y : Scheme.{u}} (ι : T.scheme ⟶ Y) [IsClosedImmersion ι] (B : SequenceOfBlowups Y)
    (h : IsPushforwardBlowupSeq ι (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.toSequenceOfBlowups B) :
    IsPushforwardBlowupSeq ι s.toSequenceOfBlowups B := by
  rw [MarkedBlowupSequenceData.blowupSequenceData_ofMarkedSequence] at h
  exact isPushforwardBlowupSeq_of_ofSequenceOfBlowups_consolidated343 ι s.toSequenceOfBlowups B h

namespace DivisorReduction

section
variable (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)

theorem comap_lowerIdealWithoutBlowup_of_eq_imageIdealSheaf (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData)
    (him : T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J) :
    (DivisorReduction.lowerIdealWithoutBlowup T).comap (T.boundary.get ⟨j, hj⟩).subschemeι = J := by
  unfold DivisorReduction.lowerIdealWithoutBlowup
  rw [Scheme.IdealSheafData.comap_id, him]
  exact Blowup.comap_map_of_isClosedImmersion _ J

theorem map_comap_take_eraseIdx_lowerBoundaryWithoutBlowup :
    List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
        (List.take (T.boundary.length - 1) ((DivisorReduction.lowerBoundaryWithoutBlowup T).eraseIdx j)) =
      List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) (T.boundary.eraseIdx j) := by
  unfold DivisorReduction.lowerBoundaryWithoutBlowup
  have h1 : List.map (fun D : T.scheme.IdealSheafData => D.comap (𝟙 T.scheme)) T.boundary
      = T.boundary := by
    simp [Scheme.IdealSheafData.comap_id]
  rw [h1]
  have hlen : (T.boundary.eraseIdx j).length = T.boundary.length - 1 := by
    simp [List.length_eraseIdx, hj]
  rw [← hlen, List.take_length]

theorem restrictToDivisor_eq_withSchemeIdealBoundary (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData)
    (him : T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J) :
    DivisorReduction.restrictToDivisor T j hj =
      T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
        (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (T.boundary.eraseIdx j)) := by
  have h1 := DivisorReduction.comap_lowerIdealWithoutBlowup_of_eq_imageIdealSheaf T j hj J him
  have h2 := DivisorReduction.map_comap_take_eraseIdx_lowerBoundaryWithoutBlowup T j hj
  unfold DivisorReduction.restrictToDivisor DivisorReduction.restrictToBoundaryDivisor MarkedIdealWithBoundary.withSchemeIdealBoundary
  rw [h1, h2]


end

end DivisorReduction

theorem isPushforwardBlowupSeq_divisorFamily_canonicalAlgorithmRules (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hD : ∀ hft : LocallyOfFiniteType T.structMap, T.IsBalanced hft)
    (hj : j < T.boundary.length) (hm : T.mult = 1)
    (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData)
    (hVJ : (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
        (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (T.boundary.eraseIdx j))).IsAdmissible)
    (hdimJ : (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
        (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (T.boundary.eraseIdx j))).krullDimSucc < T.krullDimSucc)
    (him : T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J) :
    IsPushforwardBlowupSeq (T.boundary.get ⟨j, hj⟩).subschemeι
      (L (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
            (T.boundary.eraseIdx j)))).toSequenceOfBlowups
      ((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups := by
  have : IsNoetherian T.scheme :=
    DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)
  · have hsub : (↑T.ideal.support : Set ↥T.scheme) ⊆ orderAtLeastLocus T.ideal T.mult := by
      intro x hx
      rw [hm]
      exact (mem_orderAtLeastLocus_one_iff T.ideal x).mpr hx
    rw [hcs] at hsub
    have hsupp : (↑T.ideal.support : Set ↥T.scheme) = ∅ := Set.subset_empty_iff.mp hsub
    have hItop : T.ideal = ⊤ :=
      (Scheme.IdealSheafData.eq_top_iff_support_eq_empty T.ideal).mpr hsupp
    have hJtop : J = ⊤ := by
      have h2 : (imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J).comap
          (T.boundary.get ⟨j, hj⟩).subschemeι = J :=
        Blowup.comap_map_of_isClosedImmersion (T.boundary.get ⟨j, hj⟩).subschemeι J
      rw [← him, hItop] at h2
      rw [← h2]
      simp
    have h0 : orderAtLeastLocus (⊤ : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData) 1
        = (∅ : Set ↥(T.boundary.get ⟨j, hj⟩).subscheme) := by
      simp [orderAtLeastLocus_top_eq_empty]
    have hcsJ : orderAtLeastLocus
        (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
            (T.boundary.eraseIdx j))).ideal
        (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
            (T.boundary.eraseIdx j))).mult =
        (∅ : Set ↥(T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
            (T.boundary.eraseIdx j))).scheme) := by
      rw [MarkedIdealWithBoundary.withSchemeIdealBoundary_ideal, MarkedIdealWithBoundary.withSchemeIdealBoundary_mult, hJtop, hm]
      exact h0
    refine isPushforwardSequenceOfBlowups_of_length_eq_zero _ _ _ ?_ ?_
    · exact hL.trivial_of_coSupport_empty _ hVJ (lt_of_lt_of_le hdimJ hdim) hcsJ
    · exact divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO
        (hD hV.locallyOfFiniteType) hj hcs
  · have hpretop : DivisorReduction.containedComponentsIdeal T j hj = ⊤ :=
      hfacts.preIdeal_eq_top_of_imageIdeal T hV j hj J hm hVJ him
    rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO
        (hD hV.locallyOfFiniteType) hcs with
      ⟨-, hpr, hmk0, hstep⟩ | ⟨hne, -⟩
    · have hT : DivisorReduction.restrictToDivisor T j hj =
          T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
            ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
            (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
              (T.boundary.eraseIdx j)) :=
        DivisorReduction.restrictToDivisor_eq_withSchemeIdealBoundary T j hj J him
      have hHeq : HEq ((L (DivisorReduction.restrictToDivisor T j hj)).toSequenceOfBlowups)
          ((L (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
            ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
            (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
              (T.boundary.eraseIdx j)))).toSequenceOfBlowups) := heq_toSequenceOfBlowups_of_eq_consolidated343 L hT
      have hE : (L (DivisorReduction.restrictToDivisor T j hj)).toSequenceOfBlowups =
          (L (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
            ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
            (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
              (T.boundary.eraseIdx j)))).toSequenceOfBlowups := eq_of_heq hHeq
      rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq, hstep hmk0, ← hE,
        BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
      have inst : IsClosedImmersion (T.boundary.get ⟨j, hj⟩).subschemeι := inferInstance
      exact @isPushforwardBlowupSeq_toSequenceOfBlowups_of_ofMarkedSequence (DivisorReduction.restrictToDivisor T j hj)
        (L (DivisorReduction.restrictToDivisor T j hj)) T.scheme
        (T.boundary.get ⟨j, hj⟩).subschemeι inst _
        (isPushforwardBlowupSeq_ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData
          hres blowupPreservesNoetherian hpr)
    · exact absurd hpretop hne


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.InducedSubschemePullback
section


section

namespace DivisorReduction

private theorem exists_lift_pullback_subschemeι_comap_consolidated346 {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) :
    ∃ ψ : Limits.pullback h D.subschemeι ⟶ D'.subscheme,
      ψ ≫ D'.subschemeι = Limits.pullback.fst h D.subschemeι := by
  have hle : D'.subschemeι.ker ≤ (Limits.pullback.fst h D.subschemeι).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hD]
    exact le_rfl
  exact ⟨AlgebraicGeometry.IsClosedImmersion.lift D'.subschemeι
      (Limits.pullback.fst h D.subschemeι) hle, by simp⟩

theorem isPullback_subschemeMapOfComap (X Y : Scheme.{u}) (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) :
    IsPullback (subschemeMapOfComap h D D' hD) D'.subschemeι D.subschemeι h := by
  have hcomm : subschemeMapOfComap h D D' hD ≫ D.subschemeι = D'.subschemeι ≫ h :=
    subschemeMapOfComap_comp h D D' hD
  obtain ⟨ψ, hψ⟩ := exists_lift_pullback_subschemeι_comap_consolidated346 h D D' hD
  have h1 : Limits.pullback.lift D'.subschemeι (subschemeMapOfComap h D D' hD) hcomm.symm ≫ ψ = 𝟙 _ := by
    rw [← cancel_mono D'.subschemeι, Category.assoc, hψ, Category.id_comp]
    exact Limits.pullback.lift_fst _ _ _
  have h2 : ψ ≫ Limits.pullback.lift D'.subschemeι (subschemeMapOfComap h D D' hD) hcomm.symm = 𝟙 _ := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, Category.id_comp]
      exact hψ
    · rw [Category.assoc, Limits.pullback.lift_snd, Category.id_comp,
        ← cancel_mono D.subschemeι, Category.assoc, hcomm, ← Category.assoc, hψ]
      exact Limits.pullback.condition
  refine (IsPullback.of_iso_pullback ⟨hcomm.symm⟩
    { hom := Limits.pullback.lift D'.subschemeι (subschemeMapOfComap h D D' hD) hcomm.symm
      inv := ψ
      hom_inv_id := h1
      inv_hom_id := h2 } ?_ ?_).flip
  · exact Limits.pullback.lift_fst _ _ _
  · exact Limits.pullback.lift_snd _ _ _

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PushedBlowupSequence
section


section

namespace DivisorReduction

abbrev pushedMarkedSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    T.SequenceOfBlowups :=
  ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).toMarkedBlowupSequenceData
      T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups

abbrev prependedPushedMarkedSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    T.SequenceOfBlowups :=
  ((BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).toMarkedBlowupSequenceData
      T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups

end DivisorReduction

structure PushedBlowupSequenceProperties (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) : Prop where
  isOpen_preimage_preIdeal :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (j : ℕ) (hj : j < T.boundary.length),
      IsOpen (⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹'
        ((DivisorReduction.containedComponentsIdeal T j hj).support : Set ↥T.scheme))
  ker_pushedEmb_zero_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ)
      (hj : j < T.boundary.length) (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
      (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
      (hmk : (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
          (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
            T.structMap T.ideal T.mult T.boundary),
      AlgebraicGeometry.Scheme.Hom.ker
          (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr 0) =
        (T.boundary.get ⟨j, hj⟩).comap
          (DivisorReduction.pushedMarkedSeq hres hno T j hj s hpr hmk).isoZero.hom
  ker_pushedEmb_zero_pre :
    ∀ (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ)
      (hj : j < T.boundary.length) (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
      (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
      (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
      (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
          (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
            (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
            T.structMap T.ideal T.mult T.boundary),
      AlgebraicGeometry.Scheme.Hom.ker
          (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
            (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr 0) =
        ((T.boundary.get ⟨j, hj⟩).comap
            (DivisorReduction.prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).isoZero.hom).comap
          ((DivisorReduction.prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc 0)
  isSmoothDivisor_boundary_comap :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (j : ℕ) (hj : j < T.boundary.length) (S : T.SequenceOfBlowups),
      IsSmoothDivisor (S.projectionToSpec 0) ((T.boundary.get ⟨j, hj⟩).comap S.isoZero.hom)
  boundaryLocus_subset_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ)
      (hj : j < T.boundary.length) (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
      (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
      (hmk : (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
          (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
            T.structMap T.ideal T.mult T.boundary),
      ∀ t < s.length,
        s.boundaryLocus t ⊆
          ⇑(DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
              (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t) ⁻¹'
            ((DivisorReduction.pushedMarkedSeq hres hno T j hj s hpr hmk).otherBoundaryLocus j t)
  boundaryLocus_subset_pre :
    ∀ (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ)
      (hj : j < T.boundary.length) (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
      (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
      (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
      (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
          (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
            (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
            T.structMap T.ideal T.mult T.boundary),
      ∀ t < s.length,
        s.boundaryLocus t ⊆
          ⇑(DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t) ⁻¹'
            ((DivisorReduction.prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).otherBoundaryLocus j (t + 1))
  one_le_mult : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → 1 ≤ T.mult
  isSmoothDivisor_ker_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
      ∀ (j : ℕ) (hj : j < T.boundary.length), DivisorReduction.containedComponentsIdeal T j hj = ⊤ →
        (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
        ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
          (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
          (hmk : (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
              (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
                T.structMap T.ideal T.mult T.boundary),
        ∀ t ≤ s.length,
          IsSmoothDivisor ((DivisorReduction.pushedMarkedSeq hres hno T j hj s hpr hmk).projectionToSpec t)
            (AlgebraicGeometry.Scheme.Hom.ker
              (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
                (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t))
  isSmoothDivisor_ker_pre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
      ∀ (j : ℕ) (hj : j < T.boundary.length), DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
        ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)),
        (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
        ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
          (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
          (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
              (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
                T.structMap T.ideal T.mult T.boundary),
        ∀ t ≤ s.length,
          IsSmoothDivisor ((DivisorReduction.prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToSpec (t + 1))
            (AlgebraicGeometry.Scheme.Hom.ker
              (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t))
  compositeMap_eq_restrictedEmptyCenter :
    ∀ (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ)
      (hj : j < T.boundary.length) (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
      (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
      (hmk : (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
          (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
            T.structMap T.ideal T.mult T.boundary),
      ∀ t : ℕ,
        s.projectionToSpec t =
          DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
              (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t ≫
            (DivisorReduction.pushedMarkedSeq hres hno T j hj s hpr hmk).projectionToSpec t
  compositeMap_eq_restricted :
    ∀ (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ)
      (hj : j < T.boundary.length) (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
      (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
      (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
      (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
          (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
            (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
            T.structMap T.ideal T.mult T.boundary),
      ∀ t : ℕ,
        s.projectionToSpec t =
          DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t ≫
            (DivisorReduction.prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToSpec (t + 1)
  support_imageIdeal_subset_ker :
    ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsClosedImmersion f]
      (I : X.IdealSheafData),
      ((imageIdealSheaf f I).support : Set ↥Y) ⊆
        ((AlgebraicGeometry.Scheme.Hom.ker f).support : Set ↥Y)
  support_preIdeal_subset_boundary :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (j : ℕ) (hj : j < T.boundary.length),
      ((DivisorReduction.containedComponentsIdeal T j hj).support : Set ↥T.scheme) ⊆
        ((T.boundary.get ⟨j, hj⟩).support : Set ↥T.scheme)

private def HasSmoothDivisorTransforms_consolidated344 (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (S : T.SequenceOfBlowups) : Prop :=
  ∃ (D : (t : ℕ) → (S.schemeAt t).IdealSheafData) (b : Bool),
    (∀ t ≤ S.length, IsSmoothDivisor (S.projectionToSpec t) (D t)) ∧
    D 0 = (T.boundary.get ⟨j, hj⟩).comap S.isoZero.hom ∧
    (∀ t < S.length,
        ((S.center t).support : Set ↥(S.schemeAt t)) ⊆ ((D t).support : Set ↥(S.schemeAt t))) ∧
    (b = true →
      0 < S.length ∧
      IsOpen (⇑(D 0).subschemeι ⁻¹' (((S.center 0).support : Set ↥(S.schemeAt 0)))) ∧
      D 1 = (D 0).comap (S.transitionMapSucc 0)) ∧
    (∀ t < S.length, (b = true → t ≠ 0) →
        D (t + 1) = Blowup.strictTransform (S.transitionMapSucc t) (S.center t) (D t)) ∧
    (orderAtLeastLocus S.lastIdeal T.mult ∩ ((D S.length).support : Set ↥(S.schemeAt S.length)) = ∅) ∧
    (∀ t < S.length, (b = true → t ≠ 0) →
      ∃ J : (D t).subscheme.IdealSheafData,
        NonzeroOnComponents J ∧
        (∀ x : ↥(D t).subscheme,
            (D t).subschemeι x ∉ S.otherBoundaryLocus j t →
              ∃ V : (D t).subscheme.Opens, x ∈ V ∧
                J.comap V.ι = ((S.ideal t).comap (D t).subschemeι).comap V.ι) ∧
        PrincipalizationCertificate (D t).subscheme ((D t).subschemeι ≫ S.projectionToSpec t) J T.mult
          (⇑(D t).subschemeι ⁻¹' S.otherBoundaryLocus j t)
          ((S.center t).comap (D t).subschemeι))

section
variable {T : MarkedIdealWithBoundary.{u}} (j : ℕ) (hj : j < T.boundary.length) (S : T.SequenceOfBlowups) (len : ℕ)

private theorem divisorReductionShape_of_strictTransforms_consolidated344 (D : (t : ℕ) → (S.schemeAt t).IdealSheafData) (hlen : S.length = len)
    (h1 : ∀ t ≤ len, IsSmoothDivisor (S.projectionToSpec t) (D t))
    (h2 : D 0 = (T.boundary.get ⟨j, hj⟩).comap S.isoZero.hom)
    (h3 : ∀ t < len, ((S.center t).support : Set ↥(S.schemeAt t)) ⊆ ((D t).support : Set ↥(S.schemeAt t)))
    (h5 : ∀ t < len, D (t + 1) = Blowup.strictTransform (S.transitionMapSucc t) (S.center t) (D t))
    (h6 : orderAtLeastLocus (S.ideal len) T.mult ∩ ((D len).support : Set ↥(S.schemeAt len)) = ∅)
    (h7 : ∀ t < len, ∃ J : (D t).subscheme.IdealSheafData,
        NonzeroOnComponents J ∧
        (∀ x : ↥(D t).subscheme,
            (D t).subschemeι x ∉ S.otherBoundaryLocus j t →
              ∃ V : (D t).subscheme.Opens, x ∈ V ∧
                J.comap V.ι = ((S.ideal t).comap (D t).subschemeι).comap V.ι) ∧
        PrincipalizationCertificate (D t).subscheme ((D t).subschemeι ≫ S.projectionToSpec t) J T.mult
          (⇑(D t).subschemeι ⁻¹' S.otherBoundaryLocus j t)
          ((S.center t).comap (D t).subschemeι)) :
    HasSmoothDivisorTransforms_consolidated344 T j hj S := by
  subst hlen
  refine ⟨D, false, h1, h2, h3, fun hbb => Bool.noConfusion hbb, fun t ht _ => h5 t ht, ?_,
    fun t ht _ => h7 t ht⟩
  rw [MarkedSequenceOfBlowups.lastIdeal_eq]
  exact h6

private theorem divisorReductionShape_of_pullback_then_strictTransforms_consolidated344 (hlen : S.length = len + 1)
    (D0 : (S.schemeAt 0).IdealSheafData) (Dd : (t : ℕ) → (S.schemeAt (t + 1)).IdealSheafData)
    (h1a : IsSmoothDivisor (S.projectionToSpec 0) D0)
    (h1b : ∀ t ≤ len, IsSmoothDivisor (S.projectionToSpec (t + 1)) (Dd t))
    (h2 : D0 = (T.boundary.get ⟨j, hj⟩).comap S.isoZero.hom)
    (h3a : ((S.center 0).support : Set ↥(S.schemeAt 0)) ⊆ (D0.support : Set ↥(S.schemeAt 0)))
    (h3b : ∀ t < len, ((S.center (t + 1)).support : Set ↥(S.schemeAt (t + 1))) ⊆
        ((Dd t).support : Set ↥(S.schemeAt (t + 1))))
    (h4 : IsOpen (⇑D0.subschemeι ⁻¹' ((S.center 0).support : Set ↥(S.schemeAt 0))))
    (h4' : Dd 0 = D0.comap (S.transitionMapSucc 0))
    (h5 : ∀ t < len, Dd (t + 1) =
        Blowup.strictTransform (S.transitionMapSucc (t + 1)) (S.center (t + 1)) (Dd t))
    (h6 : orderAtLeastLocus (S.ideal (len + 1)) T.mult ∩
        ((Dd len).support : Set ↥(S.schemeAt (len + 1))) = ∅)
    (h7 : ∀ t < len, ∃ J : (Dd t).subscheme.IdealSheafData,
        NonzeroOnComponents J ∧
        (∀ x : ↥(Dd t).subscheme,
            (Dd t).subschemeι x ∉ S.otherBoundaryLocus j (t + 1) →
              ∃ V : (Dd t).subscheme.Opens, x ∈ V ∧
                J.comap V.ι = ((S.ideal (t + 1)).comap (Dd t).subschemeι).comap V.ι) ∧
        PrincipalizationCertificate (Dd t).subscheme ((Dd t).subschemeι ≫ S.projectionToSpec (t + 1)) J T.mult
          (⇑(Dd t).subschemeι ⁻¹' S.otherBoundaryLocus j (t + 1))
          ((S.center (t + 1)).comap (Dd t).subschemeι)) :
    HasSmoothDivisorTransforms_consolidated344 T j hj S := by
  refine ⟨fun t => Nat.rec (motive := fun t => (S.schemeAt t).IdealSheafData) D0
      (fun t' _ => Dd t') t, true, ?_, h2, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (_ | t) ht
    · exact h1a
    · rw [hlen] at ht
      exact h1b t (by omega)
  · rintro (_ | t) ht
    · exact h3a
    · rw [hlen] at ht
      exact h3b t (by omega)
  · intro _
    refine ⟨?_, h4, h4'⟩
    rw [hlen]
    exact Nat.succ_pos len
  · rintro (_ | t) ht hbz
    · exact absurd rfl (hbz rfl)
    · rw [hlen] at ht
      exact h5 t (by omega)
  · rw [MarkedSequenceOfBlowups.lastIdeal_eq, hlen]
    exact h6
  · rintro (_ | t) ht hbz
    · exact absurd rfl (hbz rfl)
    · rw [hlen] at ht
      exact h7 t (by omega)


end

section
variable {X Y : Scheme.{u}}

private theorem comap_imageIdealSheaf_eq_self_of_isClosedImmersion_consolidated344 (f : X ⟶ Y)
    [IsClosedImmersion f] (I : X.IdealSheafData) :
    (imageIdealSheaf f I).comap f = I :=
  Blowup.comap_map_of_isClosedImmersion f I

private theorem orderAtLeastLocus_comap_iso_eq_empty_consolidated344 (e : X ≅ Y)
    (I : Y.IdealSheafData) (m : ℕ) (h : orderAtLeastLocus I m = (∅ : Set ↥Y)) :
    orderAtLeastLocus (I.comap e.hom) m = (∅ : Set ↥X) := by
  rw [orderAtLeastLocus_comap_iso_hom_eq_preimage, h, Set.preimage_empty]


end

private theorem exists_principalizationCertificate_ker_of_isClosedImmersion_consolidated344 {k : Type u} [Field k]
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f]
    (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of k))
    (I Z : X.IdealSheafData) (m : ℕ) (Mem : Set ↥X) (MemY : Set ↥Y)
    (IY ZY : Y.IdealSheafData)
    (hp : pX = f ≫ pY)
    (hMem : Mem ⊆ ⇑f ⁻¹' MemY)
    (hIY : IY.comap f = I)
    (hZY : ZY = imageIdealSheaf f Z)
    (hnz : NonzeroOnComponents I)
    (hcert : PrincipalizationCertificate X pX I m Mem Z) :
    ∃ J : (AlgebraicGeometry.Scheme.Hom.ker f).subscheme.IdealSheafData,
      NonzeroOnComponents J ∧
      (∀ x : ↥(AlgebraicGeometry.Scheme.Hom.ker f).subscheme,
          (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι x ∉ MemY →
            ∃ V : (AlgebraicGeometry.Scheme.Hom.ker f).subscheme.Opens, x ∈ V ∧
              J.comap V.ι =
                (IY.comap (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι).comap V.ι) ∧
      PrincipalizationCertificate (AlgebraicGeometry.Scheme.Hom.ker f).subscheme
        ((AlgebraicGeometry.Scheme.Hom.ker f).subschemeι ≫ pY) J m
        (⇑(AlgebraicGeometry.Scheme.Hom.ker f).subschemeι ⁻¹' MemY)
        (ZY.comap (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι) := by
  have hpe : (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι ≫ pY =
      (kerSubschemeIso f).hom ≫ pX := by
    rw [hp, ← Category.assoc, kerSubschemeIso_hom_comp]
  have hid : I.comap (kerSubschemeIso f).hom =
      IY.comap (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι := by
    rw [← hIY, ← kerSubschemeIso_hom_comp f, Scheme.IdealSheafData.comap_comp]
  refine ⟨I.comap (kerSubschemeIso f).hom,
    nonzeroOnComponents_comap_iso_hom (kerSubschemeIso f) I hnz, ?_, ?_⟩
  · intro x _
    refine ⟨⊤, trivial, ?_⟩
    exact congrArg
      (fun J => J.comap (⊤ : (AlgebraicGeometry.Scheme.Hom.ker f).subscheme.Opens).ι) hid
  · have hcert1 := PrincipalizationCertificate.comap_iso_of_eq_iso_hom_comp (kerSubschemeIso f) hpe hcert
    have hsub : ⇑(kerSubschemeIso f).hom ⁻¹' Mem ⊆
        ⇑(AlgebraicGeometry.Scheme.Hom.ker f).subschemeι ⁻¹' MemY := by
      intro x hx
      rw [Set.mem_preimage] at hx
      have h2 := hMem hx
      rw [Set.mem_preimage] at h2
      have hb0 : ⇑(AlgebraicGeometry.Scheme.Hom.ker f).subschemeι x
          = ⇑f (⇑(kerSubschemeIso f).hom x) := by
        rw [← kerSubschemeIso_hom_comp f]
        simp
      rw [Set.mem_preimage, hb0]
      exact h2
    have hZe : ZY.comap (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι
        = Z.comap (kerSubschemeIso f).hom := by
      rw [hZY, ← kerSubschemeIso_hom_comp f, Scheme.IdealSheafData.comap_comp,
        comap_imageIdealSheaf_eq_self_of_isClosedImmersion_consolidated344 f Z]
    rw [hZe]
    exact principalizationCertificate_mono_of_subset hsub hcert1

private theorem divisorReductionShape_of_orderAtLeastLocus_empty_consolidated344 {T : MarkedIdealWithBoundary.{u}} (j : ℕ)
    (hj : j < T.boundary.length) (S : T.SequenceOfBlowups) (hlen : S.length = 0)
    (hsm : IsSmoothDivisor (S.projectionToSpec 0) ((T.boundary.get ⟨j, hj⟩).comap S.isoZero.hom))
    (hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)) :
    HasSmoothDivisorTransforms_consolidated344 T j hj S := by
  refine divisorReductionShape_of_strictTransforms_consolidated344 j hj S 0
    (fun t => Nat.rec (motive := fun t => (S.schemeAt t).IdealSheafData)
      ((T.boundary.get ⟨j, hj⟩).comap S.isoZero.hom) (fun _ _ => ⊤) t) hlen ?_ rfl ?_ ?_ ?_ ?_
  · intro t ht
    obtain rfl : t = 0 := Nat.le_zero.mp ht
    exact hsm
  · intro t ht
    exact absurd ht (Nat.not_lt_zero t)
  · intro t ht
    exact absurd ht (Nat.not_lt_zero t)
  · have hz : orderAtLeastLocus (S.ideal 0) T.mult = (∅ : Set ↥(S.schemeAt 0)) := by
      rw [MarkedSequenceOfBlowups.ideal_zero]
      exact orderAtLeastLocus_comap_iso_eq_empty_consolidated344 S.isoZero T.ideal T.mult hcs
    rw [hz, Set.empty_inter]
  · intro t ht
    exact absurd ht (Nat.not_lt_zero t)

private theorem ker_embeddingIntoAmbient_succ_eq_strictTransform_consolidated344 (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData)
    (E₀ : List T.scheme.IdealSheafData)
    (s : (DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (t : ℕ) (ht : t < s.length) :
    AlgebraicGeometry.Scheme.Hom.ker
        (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj I₀ E₀ s hpr
          (t + 1)) =
      Blowup.strictTransform
        ((DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj I₀ E₀ s hpr).map t)
        ((DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj I₀ E₀ s hpr).center t)
        (AlgebraicGeometry.Scheme.Hom.ker
          (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj I₀ E₀ s hpr
            t)) := by
  have hlt : t < (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.length := by
    rw [show (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.length = s.length from
      MarkedBlowupSequenceData.ofMarkedSequence_length s]
    exact ht
  exact ker_embeddingIntoAmbientBlowupSequence_succ (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres blowupPreservesNoetherian hpr t hlt

private def divisorIdealWithoutBlowup_consolidated344 (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    ((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk).schemeAt
      t).IdealSheafData :=
  AlgebraicGeometry.Scheme.Hom.ker
    (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
      (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t)

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})

private theorem length_ambientMarkedSeq_consolidated344 (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary) :
    (DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk).length =
      s.length :=
  DivisorReduction.ambientBlowupSeq_length hres blowupPreservesNoetherian T j hj
    (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr

private theorem isSmoothDivisor_ambientMarkedSeq_consolidated344 (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (hO : T.IsOrderBoundedByMult) (hD : T.IsBalanced hV.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length)
    (htop : DivisorReduction.containedComponentsIdeal T j hj = ⊤)
    (hvl : (DivisorReduction.restrictToDivisor T j hj).IsAdmissible)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary) :
    ∀ t ≤ s.length,
      IsSmoothDivisor
        ((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk).projectionToSpec t)
        (divisorIdealWithoutBlowup_consolidated344 hres T j hj s hpr hmk t) :=
  hshape.isSmoothDivisor_ker_top T hV hO hD j hj htop hvl s hpr hmk

private theorem divisorTransform_zero_eq_comap_isoObjZero_consolidated344 (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary) :
    divisorIdealWithoutBlowup_consolidated344 hres T j hj s hpr hmk 0 =
      (T.boundary.get ⟨j, hj⟩).comap
        (DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
          hmk).isoZero.hom :=
  hshape.ker_pushedEmb_zero_top T j hj s hpr hmk

private theorem center_ambientMarkedSeq_eq_imageIdealSheaf_consolidated344 (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    (DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk).center t =
      imageIdealSheaf (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t)
        (s.center t) :=
  DivisorReduction.ambientBlowupSeq_center_eq_imageIdealSheaf hres blowupPreservesNoetherian
    T j hj (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t

private theorem support_center_ambientBlowupSeq_subset_consolidated344 (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    (((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
          hmk).center t).support :
        Set ↥((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
          hmk).schemeAt t)) ⊆
      ((divisorIdealWithoutBlowup_consolidated344 hres T j hj s hpr hmk t).support :
        Set ↥((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
          hmk).schemeAt t)) := by
  have := DivisorReduction.isClosedImmersion_embeddingIntoAmbient hres
    blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
    (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t
  rw [center_ambientMarkedSeq_eq_imageIdealSheaf_consolidated344 hres T j hj s hpr hmk t]
  exact hshape.support_imageIdeal_subset_ker _ _
    (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
      (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t) (s.center t)

private theorem divisorTransform_succ_eq_strictTransform_consolidated344 (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary) :
    ∀ t < s.length,
      divisorIdealWithoutBlowup_consolidated344 hres T j hj s hpr hmk (t + 1) =
        Blowup.strictTransform
          (((DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s
                hpr).toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary
              hmk).toMarkedSequenceOfBlowups.transitionMapSucc t)
          (((DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s
                hpr).toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary
              hmk).toMarkedSequenceOfBlowups.center t)
          (divisorIdealWithoutBlowup_consolidated344 hres T j hj s hpr hmk t) := by
  intro t ht
  rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, MarkedBlowupSequenceData.toMarkedSequence_center]
  exact ker_embeddingIntoAmbient_succ_eq_strictTransform_consolidated344 hres T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
    (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t ht

private theorem orderAtLeastLocus_inter_divisorTransform_eq_empty_consolidated344
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (hO : T.IsOrderBoundedByMult) (hD : T.IsBalanced hV.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length)
    (htop : DivisorReduction.containedComponentsIdeal T j hj = ⊤)
    (hvl : (DivisorReduction.restrictToDivisor T j hj).IsAdmissible)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary)
    (hfin : orderAtLeastLocus (s.ideal s.length) T.mult = ∅) :
    orderAtLeastLocus
        ((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk).ideal
          s.length) T.mult ∩
      ((divisorIdealWithoutBlowup_consolidated344 hres T j hj s hpr hmk s.length).support :
        Set ↥((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
          hmk).schemeAt s.length)) = ∅ :=
  hfacts.coSupport_inter_ker_eq_empty_top T hV hO hD j hj htop hvl s hpr hfin


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (hV : T.IsAdmissible) (hO : T.IsOrderBoundedByMult) (hD : T.IsBalanced hV.locallyOfFiniteType) (j : ℕ) (hj : j < T.boundary.length) (htop : DivisorReduction.containedComponentsIdeal T j hj = ⊤) (hvl : (DivisorReduction.restrictToDivisor T j hj).IsAdmissible) (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups) (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked T.structMap T.ideal T.mult T.boundary) (hcert : ∀ t < s.length, PrincipalizationCertificate (s.schemeAt t) (s.projectionToSpec t) (s.ideal t) T.mult (s.boundaryLocus t) (s.center t))
include hfacts hshape hO hD htop hvl hcert

private theorem exists_nonzeroOnComponents_certificate_ambientMarkedSeq_consolidated344 :
    ∀ t < s.length,
      ∃ J : (divisorIdealWithoutBlowup_consolidated344 hres T j hj s hpr hmk t).subscheme.IdealSheafData,
        NonzeroOnComponents J ∧
        (∀ x : ↥(divisorIdealWithoutBlowup_consolidated344 hres T j hj s hpr hmk t).subscheme,
            (divisorIdealWithoutBlowup_consolidated344 hres T j hj s hpr hmk t).subschemeι x ∉
                (DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
                  hmk).otherBoundaryLocus j t →
              ∃ V : (divisorIdealWithoutBlowup_consolidated344 hres T j hj s hpr hmk t).subscheme.Opens, x ∈ V ∧
                J.comap V.ι =
                  (((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
                      hmk).ideal t).comap
                    (divisorIdealWithoutBlowup_consolidated344 hres T j hj s hpr hmk t).subschemeι).comap V.ι) ∧
        PrincipalizationCertificate (divisorIdealWithoutBlowup_consolidated344 hres T j hj s hpr hmk t).subscheme
          ((divisorIdealWithoutBlowup_consolidated344 hres T j hj s hpr hmk t).subschemeι ≫
            (DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
              hmk).projectionToSpec t) J T.mult
          (⇑(divisorIdealWithoutBlowup_consolidated344 hres T j hj s hpr hmk t).subschemeι ⁻¹'
            (DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
              hmk).otherBoundaryLocus j t)
          (((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
            hmk).center t).comap (divisorIdealWithoutBlowup_consolidated344 hres T j hj s hpr hmk t).subschemeι) := by
  intro t ht
  have := DivisorReduction.isClosedImmersion_embeddingIntoAmbient hres
    blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
    (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t
  exact exists_principalizationCertificate_ker_of_isClosedImmersion_consolidated344
    (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
      (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t)
    (s.projectionToSpec t)
    ((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk).projectionToSpec t)
    (s.ideal t) (s.center t) T.mult (s.boundaryLocus t)
    ((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
      hmk).otherBoundaryLocus j t)
    ((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk).ideal t)
    ((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk).center t)
    (hshape.compositeMap_eq_restrictedEmptyCenter T j hj s hpr hmk t)
    (hshape.boundaryLocus_subset_top T j hj s hpr hmk t ht)
    (hfacts.comap_ctrlIdeal_top T hV hO hD j hj htop hvl s hpr t (le_of_lt ht))
    (center_ambientMarkedSeq_eq_imageIdealSheaf_consolidated344 hres T j hj s hpr hmk t)
    (MarkedSequenceOfBlowups.nonzeroOnComponents_ideal_of_isAdmissible effectiveCartierSupportContainsNoComponent hvl s t (le_of_lt ht))
    (hcert t ht)

private theorem divisorReductionShape_ambientBlowupSeq_consolidated344 (hfin : orderAtLeastLocus (s.ideal s.length) T.mult = ∅) :
    HasSmoothDivisorTransforms_consolidated344 T j hj
      (DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk) :=
  divisorReductionShape_of_strictTransforms_consolidated344 j hj _ s.length (divisorIdealWithoutBlowup_consolidated344 hres T j hj s hpr hmk)
    (length_ambientMarkedSeq_consolidated344 hres T j hj s hpr hmk)
    (isSmoothDivisor_ambientMarkedSeq_consolidated344 hres hshape T hV hO hD j hj htop hvl s hpr hmk)
    (divisorTransform_zero_eq_comap_isoObjZero_consolidated344 hres hshape T j hj s hpr hmk)
    (fun t _ => support_center_ambientBlowupSeq_subset_consolidated344 hres hshape T j hj s hpr hmk t)
    (divisorTransform_succ_eq_strictTransform_consolidated344 hres T j hj s hpr hmk)
    (orderAtLeastLocus_inter_divisorTransform_eq_empty_consolidated344 hres hfacts T hV hO hD j hj htop hvl s hpr hmk hfin)
    (exists_nonzeroOnComponents_certificate_ambientMarkedSeq_consolidated344 hres hfacts hshape T hV hO hD j hj htop hvl s hpr hmk hcert)


end

private def divisorIdealAfterBlowup_consolidated344 (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    ((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk).schemeAt
      (t + 1)).IdealSheafData :=
  AlgebraicGeometry.Scheme.Hom.ker
    (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
      (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t)

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length) (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)) (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups) (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked T.structMap T.ideal T.mult T.boundary)

private theorem length_prependedAmbientSeq_consolidated344 :
    (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk).length =
      s.length + 1 :=
  congrArg (fun m => m + 1)
    (DivisorReduction.ambientBlowupSeq_length hres blowupPreservesNoetherian T j hj
      (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)

private theorem isoObjZero_prependedAmbientSeq_eq_refl_consolidated344 :
    (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk).isoZero =
      Iso.refl T.scheme :=
  BlowupSequenceData.prepend_isoObjZero (DivisorReduction.containedComponentsIdeal T j hj) hb
    (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
      (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)

private theorem center_prependedAmbientSeq_zero_consolidated344 :
    (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk).center 0 =
      DivisorReduction.containedComponentsIdeal T j hj :=
  BlowupSequenceData.prepend_center_zero (DivisorReduction.containedComponentsIdeal T j hj) hb
    (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
      (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)

private theorem comap_boundary_isoObjZero_prependedAmbientSeq_consolidated344 :
    (T.boundary.get ⟨j, hj⟩).comap
        (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).isoZero.hom = T.boundary.get ⟨j, hj⟩ :=
  (congrArg (fun e => (T.boundary.get ⟨j, hj⟩).comap (Iso.hom e))
      (isoObjZero_prependedAmbientSeq_eq_refl_consolidated344 hres T j hj hb s hpr hmk)).trans
    (Scheme.IdealSheafData.comap_id _)


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (hV : T.IsAdmissible) (j : ℕ) (hj : j < T.boundary.length) (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)) (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups) (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked T.structMap T.ideal T.mult T.boundary)
include hshape hV

private theorem support_center_zero_prependedAmbientBlowupSeq_subset_consolidated344 :
    (((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).center 0).support :
        Set ↥((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).schemeAt 0)) ⊆
      ((((T.boundary.get ⟨j, hj⟩).comap
          (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
            hmk).isoZero.hom).support) :
        Set ↥((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).schemeAt 0)) := by
  rw [center_prependedAmbientSeq_zero_consolidated344 hres T j hj hb s hpr hmk,
    comap_boundary_isoObjZero_prependedAmbientSeq_consolidated344 hres T j hj hb s hpr hmk]
  exact hshape.support_preIdeal_subset_boundary T hV j hj

private theorem isOpen_preimage_support_center_zero_prependedAmbientSeq_consolidated344
    :
    IsOpen (⇑((T.boundary.get ⟨j, hj⟩).comap
        (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).isoZero.hom).subschemeι ⁻¹'
      ((((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).center 0).support) :
        Set ↥((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).schemeAt 0))) := by
  rw [center_prependedAmbientSeq_zero_consolidated344 hres T j hj hb s hpr hmk,
    comap_boundary_isoObjZero_prependedAmbientSeq_consolidated344 hres T j hj hb s hpr hmk]
  exact hshape.isOpen_preimage_preIdeal T hV j hj


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})

private theorem center_prependedAmbientSeq_succ_eq_imageIdealSheaf_consolidated344 (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
        hmk).center (t + 1) =
      imageIdealSheaf (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t)
        (s.center t) :=
  DivisorReduction.ambientBlowupSeq_center_eq_imageIdealSheaf hres blowupPreservesNoetherian
    T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t

private theorem support_center_succ_prependedAmbientBlowupSeq_subset_consolidated344 (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    (((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).center (t + 1)).support :
        Set ↥((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).schemeAt (t + 1))) ⊆
      ((divisorIdealAfterBlowup_consolidated344 hres T j hj hb s hpr hmk t).support :
        Set ↥((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).schemeAt (t + 1))) := by
  have := DivisorReduction.isClosedImmersion_embeddingIntoAmbient hres
    blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
    (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t
  rw [center_prependedAmbientSeq_succ_eq_imageIdealSheaf_consolidated344 hres T j hj hb s hpr hmk t]
  exact hshape.support_imageIdeal_subset_ker _ _
    (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
      (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t)
    (s.center t)


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length) (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)) (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups) (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)

private theorem ker_embeddingIntoAmbient_succ_eq_strictTransform_prepend_consolidated344 :
    ∀ t < s.length,
      AlgebraicGeometry.Scheme.Hom.ker
          (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
            (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr
            (t + 1)) =
        Blowup.strictTransform
          ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
              (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                (DivisorReduction.lowerIdealAfterBlowup T j hj)
                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).map (t + 1))
          ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
              (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                (DivisorReduction.lowerIdealAfterBlowup T j hj)
                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).center (t + 1))
          (AlgebraicGeometry.Scheme.Hom.ker
            (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
              (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr
              t)) := by
  intro t ht
  rw [BlowupSequenceData.prepend_blowupMorphism_succ, BlowupSequenceData.prepend_center_succ]
  exact ker_embeddingIntoAmbient_succ_eq_strictTransform_consolidated344 hres T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
    (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t ht

private theorem prependedDivisorTransform_succ_eq_strictTransform_consolidated344 (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    ∀ t < s.length,
      divisorIdealAfterBlowup_consolidated344 hres T j hj hb s hpr hmk (t + 1) =
        Blowup.strictTransform
          (((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                  (DivisorReduction.lowerIdealAfterBlowup T j hj)
                  (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).toMarkedBlowupSequenceData
              T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.transitionMapSucc (t + 1))
          (((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                  (DivisorReduction.lowerIdealAfterBlowup T j hj)
                  (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).toMarkedBlowupSequenceData
              T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.center (t + 1))
          (divisorIdealAfterBlowup_consolidated344 hres T j hj hb s hpr hmk t) := by
  intro t ht
  rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, MarkedBlowupSequenceData.toMarkedSequence_center]
  exact ker_embeddingIntoAmbient_succ_eq_strictTransform_prepend_consolidated344 hres T j hj hb s hpr t ht


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme]
include hshape

private theorem isSmoothDivisor_prependedAmbientSeq_consolidated344 (hV : T.IsAdmissible)
    (hO : T.IsOrderBoundedByMult) (hD : T.IsBalanced hV.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length)
    (hne : DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (hvl : (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible)
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    ∀ t ≤ s.length,
      IsSmoothDivisor
        ((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).projectionToSpec (t + 1))
        (divisorIdealAfterBlowup_consolidated344 hres T j hj hb s hpr hmk t) :=
  hshape.isSmoothDivisor_ker_pre T hV hO hD j hj hne hb hvl s hpr hmk

private theorem prependedDivisorTransform_zero_eq_comap_blowupMorphism_consolidated344 (j : ℕ)
    (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    divisorIdealAfterBlowup_consolidated344 hres T j hj hb s hpr hmk 0 =
      ((T.boundary.get ⟨j, hj⟩).comap
          (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
            hmk).isoZero.hom).comap
        ((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).transitionMapSucc 0) :=
  hshape.ker_pushedEmb_zero_pre T j hj hb s hpr hmk


end

private theorem orderAtLeastLocus_inter_prependedDivisorTransform_eq_empty_consolidated344
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (hO : T.IsOrderBoundedByMult) (hD : T.IsBalanced hV.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length)
    (hne : DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (hvl : (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible)
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary)
    (hfin : orderAtLeastLocus (s.ideal s.length) T.mult = ∅) :
    orderAtLeastLocus
        ((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).ideal (s.length + 1)) T.mult ∩
      ((divisorIdealAfterBlowup_consolidated344 hres T j hj hb s hpr hmk s.length).support :
        Set ↥((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).schemeAt (s.length + 1))) = ∅ :=
  hfacts.coSupport_inter_ker_eq_empty_pre T hV hO hD j hj hne hb hvl s hpr hfin

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (hV : T.IsAdmissible) (hO : T.IsOrderBoundedByMult) (hD : T.IsBalanced hV.locallyOfFiniteType) (j : ℕ) (hj : j < T.boundary.length) (hne : DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤) (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)) (hvl : (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible) (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups) (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) (hcert : ∀ t < s.length, PrincipalizationCertificate (s.schemeAt t) (s.projectionToSpec t) (s.ideal t) T.mult (s.boundaryLocus t) (s.center t))
include hfacts hshape hO hD hne hvl hcert

private theorem exists_nonzeroOnComponents_certificate_prependedAmbientSeq_consolidated344 :
    ∀ t < s.length,
      ∃ J : (divisorIdealAfterBlowup_consolidated344 hres T j hj hb s hpr hmk t).subscheme.IdealSheafData,
        NonzeroOnComponents J ∧
        (∀ x : ↥(divisorIdealAfterBlowup_consolidated344 hres T j hj hb s hpr hmk t).subscheme,
            (divisorIdealAfterBlowup_consolidated344 hres T j hj hb s hpr hmk t).subschemeι x ∉
                (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
                  hmk).otherBoundaryLocus j (t + 1) →
              ∃ V : (divisorIdealAfterBlowup_consolidated344 hres T j hj hb s hpr hmk t).subscheme.Opens, x ∈ V ∧
                J.comap V.ι =
                  (((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
                      hmk).ideal (t + 1)).comap
                    (divisorIdealAfterBlowup_consolidated344 hres T j hj hb s hpr hmk t).subschemeι).comap V.ι) ∧
        PrincipalizationCertificate (divisorIdealAfterBlowup_consolidated344 hres T j hj hb s hpr hmk t).subscheme
          ((divisorIdealAfterBlowup_consolidated344 hres T j hj hb s hpr hmk t).subschemeι ≫
            (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
              hmk).projectionToSpec (t + 1)) J T.mult
          (⇑(divisorIdealAfterBlowup_consolidated344 hres T j hj hb s hpr hmk t).subschemeι ⁻¹'
            (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
              hmk).otherBoundaryLocus j (t + 1))
          (((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
            hmk).center (t + 1)).comap
              (divisorIdealAfterBlowup_consolidated344 hres T j hj hb s hpr hmk t).subschemeι) := by
  intro t ht
  have := DivisorReduction.isClosedImmersion_embeddingIntoAmbient hres
    blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
    (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t
  exact exists_principalizationCertificate_ker_of_isClosedImmersion_consolidated344
    (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
      (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t)
    (s.projectionToSpec t)
    ((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
      hmk).projectionToSpec (t + 1))
    (s.ideal t) (s.center t) T.mult (s.boundaryLocus t)
    ((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
      hmk).otherBoundaryLocus j (t + 1))
    ((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
      hmk).ideal (t + 1))
    ((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
      hmk).center (t + 1))
    (hshape.compositeMap_eq_restricted T j hj hb s hpr hmk t)
    (hshape.boundaryLocus_subset_pre T j hj hb s hpr hmk t ht)
    (hfacts.comap_ctrlIdeal_pre T hV hO hD j hj hne hb hvl s hpr t (le_of_lt ht))
    (center_prependedAmbientSeq_succ_eq_imageIdealSheaf_consolidated344 hres T j hj hb s hpr hmk t)
    (MarkedSequenceOfBlowups.nonzeroOnComponents_ideal_of_isAdmissible effectiveCartierSupportContainsNoComponent hvl s t (le_of_lt ht))
    (hcert t ht)

private theorem divisorReductionShape_prependedAmbientBlowupSeq_consolidated344 (hfin : orderAtLeastLocus (s.ideal s.length) T.mult = ∅) :
    HasSmoothDivisorTransforms_consolidated344 T j hj
      (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk) :=
  divisorReductionShape_of_pullback_then_strictTransforms_consolidated344 j hj _ s.length (length_prependedAmbientSeq_consolidated344 hres T j hj hb s hpr hmk)
    ((T.boundary.get ⟨j, hj⟩).comap
      (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk).isoZero.hom)
    (divisorIdealAfterBlowup_consolidated344 hres T j hj hb s hpr hmk)
    (hshape.isSmoothDivisor_boundary_comap T hV j hj
      (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk))
    (isSmoothDivisor_prependedAmbientSeq_consolidated344 hres hshape T hV hO hD j hj hne hb hvl s hpr hmk)
    rfl
    (support_center_zero_prependedAmbientBlowupSeq_subset_consolidated344 hres hshape T hV j hj hb s hpr hmk)
    (fun t _ => support_center_succ_prependedAmbientBlowupSeq_subset_consolidated344 hres hshape T j hj hb s hpr hmk t)
    (isOpen_preimage_support_center_zero_prependedAmbientSeq_consolidated344 hres hshape T hV j hj hb s hpr hmk)
    (prependedDivisorTransform_zero_eq_comap_blowupMorphism_consolidated344 hres hshape T j hj hb s hpr hmk)
    (prependedDivisorTransform_succ_eq_strictTransform_consolidated344 hres T j hj hb s hpr hmk)
    (orderAtLeastLocus_inter_prependedDivisorTransform_eq_empty_consolidated344 hres hfacts T hV hO hD j hj hne hb hvl s hpr hmk hfin)
    (exists_nonzeroOnComponents_certificate_prependedAmbientSeq_consolidated344 hres hfacts hshape T hV hO hD j hj hne hb hvl s hpr hmk hcert)


end

theorem exists_smoothDivisorSeq_divisorFamily_canonicalAlgorithmRules
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
    (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ) :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.krullDimSucc ≤ n → T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType → ∀ hj : j < T.boundary.length,
        ∃ (D : (t : ℕ) → (((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt t).IdealSheafData)
          (b : Bool),
          (∀ t ≤ ((canonicalAlgorithmRules hres).divisorFamily L j T).length,
              IsSmoothDivisor (((canonicalAlgorithmRules hres).divisorFamily L j T).projectionToSpec t) (D t)) ∧
          D 0 = (T.boundary.get ⟨j, hj⟩).comap
              ((canonicalAlgorithmRules hres).divisorFamily L j T).isoZero.hom ∧
          (∀ t < ((canonicalAlgorithmRules hres).divisorFamily L j T).length,
              ((((canonicalAlgorithmRules hres).divisorFamily L j T).center t).support :
                  Set ↥(((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt t)) ⊆
                ((D t).support : Set ↥(((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt t))) ∧
          (b = true →
            0 < ((canonicalAlgorithmRules hres).divisorFamily L j T).length ∧
            IsOpen (⇑(D 0).subschemeι ⁻¹'
              (((((canonicalAlgorithmRules hres).divisorFamily L j T).center 0).support :
                Set ↥(((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt 0)))) ∧
            D 1 = (D 0).comap (((canonicalAlgorithmRules hres).divisorFamily L j T).transitionMapSucc 0)) ∧
          (∀ t < ((canonicalAlgorithmRules hres).divisorFamily L j T).length, (b = true → t ≠ 0) →
              D (t + 1) =
                Blowup.strictTransform (((canonicalAlgorithmRules hres).divisorFamily L j T).transitionMapSucc t)
                  (((canonicalAlgorithmRules hres).divisorFamily L j T).center t) (D t)) ∧
          (orderAtLeastLocus ((canonicalAlgorithmRules hres).divisorFamily L j T).lastIdeal T.mult ∩
              ((D ((canonicalAlgorithmRules hres).divisorFamily L j T).length).support :
                Set ↥(((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt
                  ((canonicalAlgorithmRules hres).divisorFamily L j T).length)) = ∅) ∧
          (∀ t < ((canonicalAlgorithmRules hres).divisorFamily L j T).length, (b = true → t ≠ 0) →
            ∃ J : (D t).subscheme.IdealSheafData,
              NonzeroOnComponents J ∧
              (∀ x : ↥(D t).subscheme,
                  (D t).subschemeι x ∉
                      ((canonicalAlgorithmRules hres).divisorFamily L j T).otherBoundaryLocus j t →
                    ∃ V : (D t).subscheme.Opens, x ∈ V ∧
                      J.comap V.ι =
                        ((((canonicalAlgorithmRules hres).divisorFamily L j T).ideal t).comap
                          (D t).subschemeι).comap V.ι) ∧
              PrincipalizationCertificate (D t).subscheme
                ((D t).subschemeι ≫ ((canonicalAlgorithmRules hres).divisorFamily L j T).projectionToSpec t) J T.mult
                (⇑(D t).subschemeι ⁻¹'
                  ((canonicalAlgorithmRules hres).divisorFamily L j T).otherBoundaryLocus j t)
                ((((canonicalAlgorithmRules hres).divisorFamily L j T).center t).comap (D t).subschemeι)) := by
  intro T hV hdim hO hD hj
  have hNoe : IsNoetherian T.scheme :=
    DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
  show HasSmoothDivisorTransforms_consolidated344 T j hj ((canonicalAlgorithmRules hres).divisorFamily L j T)
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j T]
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)
  · rw [DivisorReduction.divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian T
      (fun S _ => L S) j hj hcs]
    exact divisorReductionShape_of_orderAtLeastLocus_empty_consolidated344 j hj
      (emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary)
      (emptyMarkedSequenceOfBlowups_length T.structMap T.ideal T.mult T.boundary)
      (hshape.isSmoothDivisor_boundary_comap T hV j hj
        (emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary)) hcs
  · have hcoNE : (orderAtLeastLocus T.ideal T.mult).Nonempty := Set.nonempty_iff_ne_empty.mpr hcs
    rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO hD hcs with
      ⟨htop, hpr, hmk0, heq⟩ | ⟨hne, hb, hpr, hmk0, heq⟩
    · have hvl : (DivisorReduction.restrictToDivisor T j hj).IsAdmissible :=
        hfacts.valid_lowerTop T hV hO hD j hj htop
      have hdimlow : (DivisorReduction.restrictToDivisor T j hj).krullDimSucc < n :=
        lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcoNE j hj
          (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)) hdim
      have hfin : orderAtLeastLocus ((L (DivisorReduction.restrictToDivisor T j hj)).ideal
          (L (DivisorReduction.restrictToDivisor T j hj)).length) T.mult = ∅ := by
        have hr := hL.resolves (DivisorReduction.restrictToDivisor T j hj) hvl hdimlow
        rw [MarkedSequenceOfBlowups.isResolution_iff, MarkedSequenceOfBlowups.lastIdeal_eq] at hr
        exact hr
      rw [heq hmk0]
      exact divisorReductionShape_ambientBlowupSeq_consolidated344 hres hfacts hshape T hV hO hD j hj htop hvl
        (L (DivisorReduction.restrictToDivisor T j hj)) hpr hmk0
        (fun t ht => hL.cert (DivisorReduction.restrictToDivisor T j hj) hvl hdimlow t ht) hfin
    · have hvl : (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible :=
        hfacts.valid_lowerPre T hV hO hD j hj hne
      have hdimlow : (DivisorReduction.restrictTwistedToDivisor T j hj).krullDimSucc < n :=
        lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcoNE j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)) hdim
      have hfin : orderAtLeastLocus ((L (DivisorReduction.restrictTwistedToDivisor T j hj)).ideal
          (L (DivisorReduction.restrictTwistedToDivisor T j hj)).length) T.mult = ∅ := by
        have hr := hL.resolves (DivisorReduction.restrictTwistedToDivisor T j hj) hvl hdimlow
        rw [MarkedSequenceOfBlowups.isResolution_iff, MarkedSequenceOfBlowups.lastIdeal_eq] at hr
        exact hr
      rw [heq hmk0]
      exact divisorReductionShape_prependedAmbientBlowupSeq_consolidated344 hres hfacts hshape T hV hO hD j hj hne hb hvl
        (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr hmk0
        (fun t ht => hL.cert (DivisorReduction.restrictTwistedToDivisor T j hj) hvl hdimlow t ht) hfin


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothBaseChangeOnDivisor
section


section

private theorem isStrictPullbackBlowupSeq_ofSequenceOfBlowups_consolidated345 {X X' : Scheme.{u}} (φ : X' ⟶ X) (B' : SequenceOfBlowups X')
    (B : SequenceOfBlowups X) (h : IsStrictPullbackBlowupSeq φ B' B) :
    IsStrictPullbackBlowupSeq φ (BlowupSequenceData.ofSequenceOfBlowups B').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups B).toSequenceOfBlowups := by
  obtain ⟨hlen, σ, h0, hpb, hc⟩ := h
  have hlA : (BlowupSequenceData.ofSequenceOfBlowups B').toSequenceOfBlowups.length = B'.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.ofSequenceOfBlowups_length]
  have hlB : (BlowupSequenceData.ofSequenceOfBlowups B).toSequenceOfBlowups.length = B.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.ofSequenceOfBlowups_length]
  refine ⟨by rw [hlA, hlB, hlen], fun i hi => σ i (hi.trans_eq hlA), ?_, ?_, ?_⟩
  · simp only [BlowupSequenceData.toSequenceOfBlowups_isoObjZero, BlowupSequenceData.ofSequenceOfBlowups_isoObjZero]
    exact h0
  · intro i hi
    simp only [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.ofSequenceOfBlowups_blowupMorphism]
    exact hpb i (hi.trans_eq hlA)
  · intro i hi
    simp only [BlowupSequenceData.toSequenceOfBlowups_center, BlowupSequenceData.ofSequenceOfBlowups_center]
    exact hc i (hi.trans_eq hlA)

theorem IsStrictPullbackBlowupSeq.ofMarkedSequence {A B : MarkedIdealWithBoundary.{u}} (φ : A.scheme ⟶ B.scheme)
    (sA : A.SequenceOfBlowups) (sB : B.SequenceOfBlowups)
    (h : IsStrictPullbackBlowupSeq φ sA.toSequenceOfBlowups sB.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq φ (MarkedBlowupSequenceData.ofMarkedSequence sA).toBlowupSequenceData.toSequenceOfBlowups
      (MarkedBlowupSequenceData.ofMarkedSequence sB).toBlowupSequenceData.toSequenceOfBlowups := by
  rw [MarkedBlowupSequenceData.blowupSequenceData_ofMarkedSequence sA,
    MarkedBlowupSequenceData.blowupSequenceData_ofMarkedSequence sB]
  exact isStrictPullbackBlowupSeq_ofSequenceOfBlowups_consolidated345 φ _ _ h

theorem BlowupSequenceData.prepend_toSequenceOfBlowups_congr {X : Scheme.{u}} {Z Z' : X.IdealSheafData} (hZZ : Z = Z')
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z') (d : BlowupSequenceData X) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups = (BlowupSequenceData.prepend Z' hZ' d).toSequenceOfBlowups := by
  subst hZZ
  rfl

structure FlatOfSmooth : Prop where
  flat_of_smooth : ∀ (X Y : Scheme.{u}) (f : Y ⟶ X), Smooth f →
    Flat f

namespace DivisorReduction

structure StrictPullbackOfSmoothBaseChangeOnDivisor (n : ℕ) (L : PrincipalizationAssignment.{u}) (j : ℕ) : Prop where
  isStrictPullbackSeq_lowerTop :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
      (_hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
      (_hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty) (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h] [AlgebraicGeometry.Surjective h]
      (_hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
      (_hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
      (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary)
      (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible)
      (_hdim' : ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc ≤ n)
      (_hO' : ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult)
      (_hDB' : ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
      (hjE : j < E'.length)
      (_hcs' : (orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult).Nonempty)
      (_hZ : containedComponentsIdeal T j hj = ⊤)
      (_hZ' : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = ⊤),
      IsStrictPullbackBlowupSeq
        (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩)
          (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
        (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE)).toSequenceOfBlowups
        (L (restrictToDivisor T j hj)).toSequenceOfBlowups
  isStrictPullbackSeq_lowerPre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
      (_hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
      (_hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty) (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h] [AlgebraicGeometry.Surjective h]
      (_hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
      (_hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
      (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary)
      (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible)
      (_hdim' : ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc ≤ n)
      (_hO' : ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult)
      (_hDB' : ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
      (hjE : j < E'.length)
      (_hcs' : (orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult).Nonempty)
      (_hZ : containedComponentsIdeal T j hj ≠ ⊤)
      (_hZ' : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE =
        (containedComponentsIdeal T j hj).comap h),
      IsStrictPullbackBlowupSeq
        (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h (E'.get ⟨j, hjE⟩)
          (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
        (L (restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE)).toSequenceOfBlowups
        (L (restrictTwistedToDivisor T j hj)).toSequenceOfBlowups

def DivisorReductionSeqEqAmbient (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (L : PrincipalizationAssignment.{u}) (j : ℕ)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length) : Prop :=
  letI : IsNoetherian T.scheme := isNoetherian_scheme_of_isAdmissible T hV
  (containedComponentsIdeal T j hj = ⊤ ∧
      ∃ (hpr : (MarkedBlowupSequenceData.ofMarkedSequence (L (restrictToDivisor T j hj))).CentersContainNoComponent)
        (hmk : (ambientBlowupSeq hres blowupPreservesNoetherian T j hj (lowerIdealWithoutBlowup T)
            (lowerBoundaryWithoutBlowup T) (L (restrictToDivisor T j hj)) hpr).IsMarked
            T.structMap T.ideal T.mult T.boundary),
        divisorReductionSeq hres blowupPreservesNoetherian T (fun S _ => L S) j =
          ((ambientBlowupSeq hres blowupPreservesNoetherian T j hj (lowerIdealWithoutBlowup T)
              (lowerBoundaryWithoutBlowup T) (L (restrictToDivisor T j hj)) hpr).toMarkedBlowupSequenceData
              T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups) ∨
    (containedComponentsIdeal T j hj ≠ ⊤ ∧
      ∃ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence (L (restrictTwistedToDivisor T j hj))).CentersContainNoComponent)
        (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
            (ambientBlowupSeq hres blowupPreservesNoetherian T j hj (lowerIdealAfterBlowup T j hj)
              (lowerBoundaryAfterBlowup T j hj) (L (restrictTwistedToDivisor T j hj)) hpr)).IsMarked
            T.structMap T.ideal T.mult T.boundary),
        divisorReductionSeq hres blowupPreservesNoetherian T (fun S _ => L S) j =
          ((BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
              (ambientBlowupSeq hres blowupPreservesNoetherian T j hj (lowerIdealAfterBlowup T j hj)
                (lowerBoundaryAfterBlowup T j hj) (L (restrictTwistedToDivisor T j hj)) hpr)).toMarkedBlowupSequenceData
              T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups)

theorem divisorFamily_isStrictPullbackBlowupSeq_of_smooth (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : SmoothPullbackCompatibility.{u}) (hsf : FlatOfSmooth.{u}) (n : ℕ) (L : PrincipalizationAssignment.{u})
    (j : ℕ) (hlow : StrictPullbackOfSmoothBaseChangeOnDivisor n L j)
    (hshape : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReductionSeqEqAmbient hres L j T hV hj)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [Smooth h] [AlgebraicGeometry.Surjective h]
    (hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary)
    (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible)
    (hdim' : ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc ≤ n)
    (hO' : ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult)
    (hDB' : ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
    (hjE : j < E'.length) :
    IsStrictPullbackBlowupSeq h
      (((canonicalAlgorithmRules hres).divisorFamily L j
        ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) := by
  classical
  have : IsNoetherian T.scheme := isNoetherian_scheme_of_isAdmissible T hV
  have : IsNoetherian
      ((T.pullbackAlong Y q h).withBoundary E').scheme :=
    isNoetherian_scheme_of_isAdmissible _ hV'
  have : IsNoetherian Y := isNoetherian_scheme_of_isAdmissible _ hV'
  have : Flat h := hsf.flat_of_smooth T.scheme Y h inferInstance
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j ((T.pullbackAlong Y q h).withBoundary E'),
    divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j T]
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = ∅
  · have hcs2 : orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hx
      rw [orderAtLeastLocus_withBoundary_pullbackAlong hbc T hV Y q h hq E' T.mult, hcs] at hx
      exact hx
    rw [divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian
        ((T.pullbackAlong Y q h).withBoundary E') (fun S _ => L S) j hjE hcs2,
      divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian T
        (fun S _ => L S) j hj hcs]
    exact IsStrictPullbackBlowupSeq.of_length_zero h _ _ rfl rfl
  · have hcsne : (orderAtLeastLocus T.ideal T.mult).Nonempty := Set.nonempty_iff_ne_empty.mpr hcs
    have hcsne' : (orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult).Nonempty := by
      obtain ⟨x, hx⟩ := hcsne
      obtain ⟨y, rfl⟩ := h.surjective x
      refine ⟨y, ?_⟩
      rw [orderAtLeastLocus_withBoundary_pullbackAlong hbc T hV Y q h hq E' T.mult]
      exact hx
    have hpre : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE
        = (containedComponentsIdeal T j hj).comap h :=
      hbc.preIdeal_comap T hV Y q h hq E' hBE j hj hjE htake hV'
    have hsT := hshape T hV hj hdim hO hbal hcsne
    have hsT' := hshape ((T.pullbackAlong Y q h).withBoundary E') hV' hjE hdim' hO' hDB' hcsne'
    unfold DivisorReductionSeqEqAmbient at hsT hsT'
    rcases hsT with ⟨hZ, hpr, _hmk, hstep⟩ | ⟨hZ, hb, hpr, _hmk, hstep⟩
    · rcases hsT' with ⟨hZ', hpr', _hmk', hstep'⟩ | ⟨hZ', _hb', _hpr', _hmk', _hstep'⟩
      · rw [hstep, hstep', BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
          BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
        exact hfacts.isStrictPullbackSeq_ambientTower _ _ _ _
          (T.boundary.get ⟨j, hj⟩).subschemeι (E'.get ⟨j, hjE⟩).subschemeι h
          (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩)
            (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
          ((isPullback_divisorPullbackMap hbc T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
            (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake)).flip)
          (MarkedBlowupSequenceData.ofMarkedSequence (L (restrictToDivisor T j hj))).toBlowupSequenceData
          (MarkedBlowupSequenceData.ofMarkedSequence
            (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE))).toBlowupSequenceData
          hpr hpr'
          (IsStrictPullbackBlowupSeq.ofMarkedSequence _ _ _
            (hlow.isStrictPullbackSeq_lowerTop T hV hdim hO hbal hj hcsne Y q h hq E' hBE htake
              hV' hdim' hO' hDB' hjE hcsne' hZ hZ'))
      · exfalso
        have htc : (containedComponentsIdeal T j hj).comap h = ⊤ := by
          rw [hZ]
          simp
        exact hZ' (hpre.trans htc)
    · rcases hsT' with ⟨hZ', _hpr', _hmk', _hstep'⟩ | ⟨_hZ', hb', hpr', _hmk', hstep'⟩
      · have hcontra : (containedComponentsIdeal T j hj).comap h = ⊤ := by rw [← hpre]; exact hZ'
        exact absurd hcontra (comap_ne_top_of_surjective hbc h (containedComponentsIdeal T j hj) hZ)
      · rw [hstep, hstep', BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
          BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
        have hb'' : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) ((containedComponentsIdeal T j hj).comap h) :=
          isBlowupAlongIdealSheaf_id_comap_containedComponentsIdeal hres hfacts j T Y q h E' hV' hj hjE hpre
        have hamb := hfacts.isStrictPullbackSeq_ambientTower _ _ _ _
          (T.boundary.get ⟨j, hj⟩).subschemeι (E'.get ⟨j, hjE⟩).subschemeι h
          (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
            (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
          ((isPullback_divisorPullbackMap hbc T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
            (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake)).flip)
          (MarkedBlowupSequenceData.ofMarkedSequence (L (restrictTwistedToDivisor T j hj))).toBlowupSequenceData
          (MarkedBlowupSequenceData.ofMarkedSequence
            (L (restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE))).toBlowupSequenceData
          hpr hpr'
          (IsStrictPullbackBlowupSeq.ofMarkedSequence _ _ _
            (hlow.isStrictPullbackSeq_lowerPre T hV hdim hO hbal hj hcsne Y q h hq E' hBE htake
              hV' hdim' hO' hDB' hjE hcsne' hZ hpre))
        have key := hamb.prepend (containedComponentsIdeal T j hj) hb hb''
        rw [BlowupSequenceData.prepend_toSequenceOfBlowups_congr hpre hb' hb''
          (ambientBlowupSeq hres blowupPreservesNoetherian
            ((T.pullbackAlong Y q h).withBoundary E') j hjE
            (lowerIdealAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE)
            (lowerBoundaryAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE)
            (L (restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE)) hpr')]
        exact key

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryReindexing
section


section

theorem map_comap_id (X : Scheme.{u}) (E : List X.IdealSheafData) :
    E.map (fun D => D.comap (𝟙 X)) = E := by
  induction E with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, Scheme.IdealSheafData.comap_id, ih]

section
variable {X : Scheme.{u}}

theorem get_eq_comap_id (E₁ E₂ : List X.IdealSheafData) (j₁ j₂ : ℕ)
    (hj₁ : j₁ < E₁.length) (hj₂ : j₂ < E₂.length)
    (heq : E₁.get ⟨j₁, hj₁⟩ = E₂.get ⟨j₂, hj₂⟩) :
    E₂.get ⟨j₂, hj₂⟩ = (E₁.get ⟨j₁, hj₁⟩).comap (𝟙 X) := by
  rw [Scheme.IdealSheafData.comap_id, heq]

private theorem eq_comap_id_of_eq_consolidated376 {A B : X.IdealSheafData} (h : A = B) :
    A = B.comap (𝟙 X) := by
  rw [Scheme.IdealSheafData.comap_id]
  exact h

private theorem sameNontrivialBoundary_map_comap_id_consolidated376 {A B : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary A B) :
    MarkedIdealWithBoundary.SameNontrivialBoundary A (B.map fun D => D.comap (𝟙 X)) := by
  rw [map_comap_id]
  exact h


end

section
variable {X : Scheme.{u}} (E₁ : List X.IdealSheafData) (D : X.IdealSheafData) (E₂ : List X.IdealSheafData)

private theorem get_append_cons_length_consolidated376 (h : E₁.length < (E₁ ++ D :: E₂).length) :
    (E₁ ++ D :: E₂).get ⟨E₁.length, h⟩ = D := by
  induction E₁ with
  | nil => rfl
  | cons a l ih => exact ih _

private theorem eraseIdx_append_cons_length_consolidated376 :
    (E₁ ++ D :: E₂).eraseIdx E₁.length = E₁ ++ E₂ := by
  induction E₁ with
  | nil => rfl
  | cons a l ih => simp [ih]


end

private theorem isomorphic_of_isStrictPullbackAlongId_consolidated376 {X : Scheme.{u}} (A B : SequenceOfBlowups X)
    (h : IsStrictPullbackBlowupSeq (𝟙 X) A B) : A.Isomorphic B := by
  unfold IsStrictPullbackBlowupSeq at h
  obtain ⟨hlen, σ, h0, hpb, hc⟩ := h
  have hiso : ∀ (i : ℕ) (hi : i ≤ A.length), IsIso (σ i hi) := by
    intro i
    induction i with
    | zero =>
        intro hi
        have hh : σ 0 hi = A.isoZero.hom ≫ B.isoZero.inv := by
          rw [Iso.eq_comp_inv]
          simpa using h0
        rw [hh]
        infer_instance
    | succ k ih =>
        intro hi
        have hk : k < A.length := hi
        exact (hpb k hk).isIso_fst_of_isIso (ih (le_of_lt hk))
  unfold SequenceOfBlowups.Isomorphic
  exact ⟨hlen, fun i hi => @asIso Scheme _ _ _ (σ i hi) (hiso i hi), by simpa using h0,
    fun i hi => (hpb i hi).w, fun i hi => (hc i hi).symm⟩

namespace DivisorReduction

theorem containedComponentsIdeal_withBoundary_congr (T : MarkedIdealWithBoundary.{u})
    (L₁ L₂ : List T.scheme.IdealSheafData) (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ)
    (hj₂ : j₂ < L₂.length) (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩) :
    containedComponentsIdeal (T.withBoundary L₁) j₁ hj₁ = containedComponentsIdeal (T.withBoundary L₂) j₂ hj₂ := by
  rw [containedComponentsIdeal_eq_componentsInOrderLocusIdeal (T.withBoundary L₁) j₁ hj₁,
    containedComponentsIdeal_eq_componentsInOrderLocusIdeal (T.withBoundary L₂) j₂ hj₂]
  show componentsInOrderLocusIdeal T.ideal T.mult (L₁.get ⟨j₁, hj₁⟩)
      = componentsInOrderLocusIdeal T.ideal T.mult (L₂.get ⟨j₂, hj₂⟩)
  rw [heq]

structure BoundaryReindexingInvariance : Prop where
  smooth_id : ∀ X : Scheme.{u}, Smooth (𝟙 X)
  surjective_id : ∀ X : Scheme.{u}, AlgebraicGeometry.Surjective (𝟙 X)
  lowerIdealPre_shift :
    ∀ (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData) (j₁ : ℕ)
      (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length),
      L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩ →
      lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hj₂ = lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hj₁
  boundaryEquiv_restrictedBoundary_reindex :
    ∀ (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData) (j₁ : ℕ)
      (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length),
      L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩ →
      MarkedIdealWithBoundary.SameNontrivialBoundary (L₂.eraseIdx j₂) (L₁.eraseIdx j₁) →
      MarkedIdealWithBoundary.SameNontrivialBoundary
        (List.take (L₂.length - 1) ((lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hj₂).eraseIdx j₂))
        (List.take (L₁.length - 1) ((lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hj₁).eraseIdx j₁))

private theorem isStrictPullbackBlowupSeq_restrictToBoundaryDivisor_of_smooth_consolidated376 (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (S : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < S.boundary.length)
    (I₀ : S.scheme.IdealSheafData) (E₀ : List S.scheme.IdealSheafData)
    (D' : S.scheme.IdealSheafData)
    (ψ : D'.subscheme ⟶ (restrictToBoundaryDivisor S j hj I₀ E₀).scheme)
    [Smooth ψ] [AlgebraicGeometry.Surjective ψ]
    (hq : ψ ≫ (restrictToBoundaryDivisor S j hj I₀ E₀).structMap = D'.subschemeι ≫ S.structMap)
    (I₀' : S.scheme.IdealSheafData) (F : List S.scheme.IdealSheafData)
    (hid : (I₀.comap (S.boundary.get ⟨j, hj⟩).subschemeι).comap ψ = I₀'.comap D'.subschemeι)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.map (fun Dd => Dd.comap ψ)
        (List.map (fun Dd => Dd.comap (S.boundary.get ⟨j, hj⟩).subschemeι)
          (List.take (S.boundary.length - 1) (E₀.eraseIdx j))))
      (List.map (fun Dd => Dd.comap D'.subschemeι) F))
    (hV₁ : (restrictToBoundaryDivisor S j hj I₀ E₀).IsAdmissible)
    (hd₁ : (restrictToBoundaryDivisor S j hj I₀ E₀).krullDimSucc < n)
    (hV₂ : (S.withSchemeIdealBoundary D'.subscheme (D'.subschemeι ≫ S.structMap) (I₀'.comap D'.subschemeι)
      (List.map (fun Dd => Dd.comap D'.subschemeι) F)).IsAdmissible)
    (hd₂ : (S.withSchemeIdealBoundary D'.subscheme (D'.subschemeι ≫ S.structMap) (I₀'.comap D'.subschemeι)
      (List.map (fun Dd => Dd.comap D'.subschemeι) F)).krullDimSucc < n) :
    IsStrictPullbackBlowupSeq ψ
      (L (S.withSchemeIdealBoundary D'.subscheme (D'.subschemeι ≫ S.structMap) (I₀'.comap D'.subschemeι)
        (List.map (fun Dd => Dd.comap D'.subschemeι) F))).toSequenceOfBlowups
      (L (restrictToBoundaryDivisor S j hj I₀ E₀)).toSequenceOfBlowups := by
  rw [← hid] at hV₂ hd₂ ⊢
  have hBE' : MarkedIdealWithBoundary.SameNontrivialBoundary
      ((restrictToBoundaryDivisor S j hj I₀ E₀).pullbackAlong D'.subscheme
        (D'.subschemeι ≫ S.structMap) ψ).boundary
      (List.map (fun Dd => Dd.comap D'.subschemeι) F) := hBE
  have hVp : (((restrictToBoundaryDivisor S j hj I₀ E₀).pullbackAlong D'.subscheme
      (D'.subschemeι ≫ S.structMap) ψ).withBoundary
      (List.map (fun Dd => Dd.comap D'.subschemeι) F)).IsAdmissible := hV₂
  have hdp : (((restrictToBoundaryDivisor S j hj I₀ E₀).pullbackAlong D'.subscheme
      (D'.subschemeι ≫ S.structMap) ψ).withBoundary
      (List.map (fun Dd => Dd.comap D'.subschemeι) F)).krullDimSucc < n := hd₂
  exact hL.smooth_pullback_strict (restrictToBoundaryDivisor S j hj I₀ E₀) hV₁ hd₁ D'.subscheme
    (D'.subschemeι ≫ S.structMap) ψ hq (List.map (fun Dd => Dd.comap D'.subschemeι) F)
    hBE' hVp hdp

theorem isStrictPullbackBlowupSeq_restrictToBoundaryDivisor_of_get_eq
    (hbc : SmoothPullbackCompatibility.{u}) (hsh : BoundaryReindexingInvariance.{u})
    (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData)
    (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length)
    (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (I₀' : T.scheme.IdealSheafData) (E₀' : List T.scheme.IdealSheafData)
    (hI : I₀' = I₀.comap (𝟙 T.scheme))
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (L₂.length - 1) (E₀'.eraseIdx j₂))
      (List.map (fun D => D.comap (𝟙 T.scheme))
        (List.take (L₁.length - 1) (E₀.eraseIdx j₁))))
    (hV₁ : (restrictToBoundaryDivisor (T.withBoundary L₁) j₁ hj₁ I₀ E₀).IsAdmissible)
    (hd₁ : (restrictToBoundaryDivisor (T.withBoundary L₁) j₁ hj₁ I₀ E₀).krullDimSucc < n)
    (hV₂ : (restrictToBoundaryDivisor (T.withBoundary L₂) j₂ hj₂ I₀' E₀').IsAdmissible)
    (hd₂ : (restrictToBoundaryDivisor (T.withBoundary L₂) j₂ hj₂ I₀' E₀').krullDimSucc < n) :
    IsStrictPullbackBlowupSeq
      (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme (𝟙 T.scheme)
        (L₂.get ⟨j₂, hj₂⟩) (get_eq_comap_id L₁ L₂ j₁ j₂ hj₁ hj₂ heq))
      (L (restrictToBoundaryDivisor (T.withBoundary L₂) j₂ hj₂ I₀' E₀')).toSequenceOfBlowups
      (L (restrictToBoundaryDivisor (T.withBoundary L₁) j₁ hj₁ I₀ E₀)).toSequenceOfBlowups := by
  have hD : L₂.get ⟨j₂, hj₂⟩ = (L₁.get ⟨j₁, hj₁⟩).comap (𝟙 T.scheme) :=
    get_eq_comap_id L₁ L₂ j₁ j₂ hj₁ hj₂ heq
  have hsmid : Smooth (𝟙 T.scheme) := hsh.smooth_id T.scheme
  have hsuid : AlgebraicGeometry.Surjective (𝟙 T.scheme) := hsh.surjective_id T.scheme
  have hsq := isPullback_divisorPullbackMap hbc (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme
    (𝟙 T.scheme) (L₂.get ⟨j₂, hj₂⟩) hD
  have hsmo : Smooth
      (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme (𝟙 T.scheme)
        (L₂.get ⟨j₂, hj₂⟩) hD) :=
    hbc.smooth_of_isPullback T.scheme T.scheme
      ((T.withBoundary L₁).boundary.get ⟨j₁, hj₁⟩).subscheme (L₂.get ⟨j₂, hj₂⟩).subscheme
      ((T.withBoundary L₁).boundary.get ⟨j₁, hj₁⟩).subschemeι (L₂.get ⟨j₂, hj₂⟩).subschemeι
      (𝟙 T.scheme)
      (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme (𝟙 T.scheme)
        (L₂.get ⟨j₂, hj₂⟩) hD) hsq.flip hsmid
  have hsur : AlgebraicGeometry.Surjective
      (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme (𝟙 T.scheme)
        (L₂.get ⟨j₂, hj₂⟩) hD) :=
    @surjective_snd_of_isPullback_of_surjective T.scheme T.scheme
      ((T.withBoundary L₁).boundary.get ⟨j₁, hj₁⟩).subscheme (L₂.get ⟨j₂, hj₂⟩).subscheme
      ((T.withBoundary L₁).boundary.get ⟨j₁, hj₁⟩).subschemeι (L₂.get ⟨j₂, hj₂⟩).subschemeι
      (𝟙 T.scheme)
      (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme (𝟙 T.scheme)
        (L₂.get ⟨j₂, hj₂⟩) hD) hsuid hsq.flip
  have hw : (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme (𝟙 T.scheme)
      (L₂.get ⟨j₂, hj₂⟩) hD) ≫ ((T.withBoundary L₁).boundary.get ⟨j₁, hj₁⟩).subschemeι
      = (L₂.get ⟨j₂, hj₂⟩).subschemeι := by
    exact hsq.w.trans (Category.comp_id (L₂.get ⟨j₂, hj₂⟩).subschemeι)
  have h2 : ((divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme (𝟙 T.scheme)
        (L₂.get ⟨j₂, hj₂⟩) hD) ≫ ((T.withBoundary L₁).boundary.get ⟨j₁, hj₁⟩).subschemeι)
        ≫ (T.withBoundary L₁).structMap
      = (L₂.get ⟨j₂, hj₂⟩).subschemeι ≫ (T.withBoundary L₁).structMap :=
    congrArg (fun f => f ≫ (T.withBoundary L₁).structMap) hw
  have hq : (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme (𝟙 T.scheme)
      (L₂.get ⟨j₂, hj₂⟩) hD) ≫ (restrictToBoundaryDivisor (T.withBoundary L₁) j₁ hj₁ I₀ E₀).structMap
      = (L₂.get ⟨j₂, hj₂⟩).subschemeι ≫ (T.withBoundary L₁).structMap :=
    (Category.assoc _ _ _).symm.trans h2
  refine @isStrictPullbackBlowupSeq_restrictToBoundaryDivisor_of_smooth_consolidated376 n L O hL (T.withBoundary L₁) j₁ hj₁ I₀ E₀
    (L₂.get ⟨j₂, hj₂⟩)
    (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ I₀ E₀ T.scheme (𝟙 T.scheme)
      (L₂.get ⟨j₂, hj₂⟩) hD) hsmo hsur hq I₀'
    (List.take (L₂.length - 1) (E₀'.eraseIdx j₂)) ?_ ?_ hV₁ hd₁ hV₂ hd₂
  · rw [hI]
    exact comap_subschemeMapOfComap (𝟙 T.scheme) ((T.withBoundary L₁).boundary.get ⟨j₁, hj₁⟩)
      (L₂.get ⟨j₂, hj₂⟩) hD I₀
  · exact (sameNontrivialBoundary_comap_subschemeι (𝟙 T.scheme)
      ((T.withBoundary L₁).boundary.get ⟨j₁, hj₁⟩) (L₂.get ⟨j₂, hj₂⟩) hD
      (List.take (L₁.length - 1) (E₀.eraseIdx j₁))
      (List.take (L₂.length - 1) (E₀'.eraseIdx j₂)) hE).symm

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O) (hbc : SmoothPullbackCompatibility.{u}) (hsh : BoundaryReindexingInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData) (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length) (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩) (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (L₂.eraseIdx j₂) (L₁.eraseIdx j₁)) (hV₁ : (T.withBoundary L₁).IsAdmissible) (hdim₁ : (T.withBoundary L₁).krullDimSucc ≤ n) (hO₁ : (T.withBoundary L₁).IsOrderBoundedByMult) (hDB₁ : (T.withBoundary L₁).IsBalanced hV₁.locallyOfFiniteType) (hcs₁ : (orderAtLeastLocus (T.withBoundary L₁).ideal (T.withBoundary L₁).mult).Nonempty) (hV₂ : (T.withBoundary L₂).IsAdmissible) (hdim₂ : (T.withBoundary L₂).krullDimSucc ≤ n) (hO₂ : (T.withBoundary L₂).IsOrderBoundedByMult) (hDB₂ : (T.withBoundary L₂).IsBalanced hV₂.locallyOfFiniteType) (hcs₂ : (orderAtLeastLocus (T.withBoundary L₂).ideal (T.withBoundary L₂).mult).Nonempty)
include hfacts hL hbc hsh hBE hdim₁ hO₁ hDB₁ hcs₁ hdim₂ hO₂ hDB₂ hcs₂

theorem isStrictPullbackBlowupSeq_restrictToDivisor_of_get_eq_of_eq_top
    (hZ : containedComponentsIdeal (T.withBoundary L₁) j₁ hj₁ = ⊤) :
    IsStrictPullbackBlowupSeq
      (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ (lowerIdealWithoutBlowup (T.withBoundary L₁))
        (lowerBoundaryWithoutBlowup (T.withBoundary L₁)) T.scheme (𝟙 T.scheme) (L₂.get ⟨j₂, hj₂⟩)
        (get_eq_comap_id L₁ L₂ j₁ j₂ hj₁ hj₂ heq))
      (L (restrictToDivisor (T.withBoundary L₂) j₂ hj₂)).toSequenceOfBlowups
      (L (restrictToDivisor (T.withBoundary L₁) j₁ hj₁)).toSequenceOfBlowups := by
  have hZ₂ : containedComponentsIdeal (T.withBoundary L₂) j₂ hj₂ = ⊤ := by
    rw [← containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq]
    exact hZ
  have hlen₁ : (L₁.eraseIdx j₁).length = L₁.length - 1 := by
    simp [List.length_eraseIdx, hj₁]
  have hlen₂ : (L₂.eraseIdx j₂).length = L₂.length - 1 := by
    simp [List.length_eraseIdx, hj₂]
  have ht₁ : List.take (L₁.length - 1) (L₁.eraseIdx j₁) = L₁.eraseIdx j₁ := by
    rw [← hlen₁]; simp
  have ht₂ : List.take (L₂.length - 1) (L₂.eraseIdx j₂) = L₂.eraseIdx j₂ := by
    rw [← hlen₂]; simp
  have hI : lowerIdealWithoutBlowup (T.withBoundary L₂)
      = (lowerIdealWithoutBlowup (T.withBoundary L₁)).comap (𝟙 T.scheme) :=
    (Scheme.IdealSheafData.comap_id _).symm
  have hE : MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (L₂.length - 1) ((lowerBoundaryWithoutBlowup (T.withBoundary L₂)).eraseIdx j₂))
      (List.map (fun D => D.comap (𝟙 T.scheme))
        (List.take (L₁.length - 1) ((lowerBoundaryWithoutBlowup (T.withBoundary L₁)).eraseIdx j₁))) := by
    rw [lowerBoundaryWithoutBlowup_eq (T.withBoundary L₂), lowerBoundaryWithoutBlowup_eq (T.withBoundary L₁)]
    show MarkedIdealWithBoundary.SameNontrivialBoundary (List.take (L₂.length - 1) (L₂.eraseIdx j₂))
        (List.map (fun D => D.comap (𝟙 T.scheme)) (List.take (L₁.length - 1) (L₁.eraseIdx j₁)))
    rw [ht₁, ht₂, map_comap_id]
    exact hBE
  have hVa : (restrictToDivisor (T.withBoundary L₁) j₁ hj₁).IsAdmissible :=
    hfacts.valid_lowerTop (T.withBoundary L₁) hV₁ hO₁ hDB₁ j₁ hj₁ hZ
  have hVb : (restrictToDivisor (T.withBoundary L₂) j₂ hj₂).IsAdmissible :=
    hfacts.valid_lowerTop (T.withBoundary L₂) hV₂ hO₂ hDB₂ j₂ hj₂ hZ₂
  have hda : (restrictToDivisor (T.withBoundary L₁) j₁ hj₁).krullDimSucc < n :=
    lt_of_lt_of_le (hfacts.lowerTriple_dim_lt (T.withBoundary L₁) hV₁ hcs₁ j₁ hj₁
      (lowerIdealWithoutBlowup (T.withBoundary L₁)) (lowerBoundaryWithoutBlowup (T.withBoundary L₁))) hdim₁
  have hdb : (restrictToDivisor (T.withBoundary L₂) j₂ hj₂).krullDimSucc < n :=
    lt_of_lt_of_le (hfacts.lowerTriple_dim_lt (T.withBoundary L₂) hV₂ hcs₂ j₂ hj₂
      (lowerIdealWithoutBlowup (T.withBoundary L₂)) (lowerBoundaryWithoutBlowup (T.withBoundary L₂))) hdim₂
  exact isStrictPullbackBlowupSeq_restrictToBoundaryDivisor_of_get_eq hbc hsh n L O hL T L₁ L₂ j₁ hj₁ j₂ hj₂ heq
    (lowerIdealWithoutBlowup (T.withBoundary L₁)) (lowerBoundaryWithoutBlowup (T.withBoundary L₁))
    (lowerIdealWithoutBlowup (T.withBoundary L₂)) (lowerBoundaryWithoutBlowup (T.withBoundary L₂))
    hI hE hVa hda hVb hdb

theorem isStrictPullbackBlowupSeq_restrictTwistedToDivisor_of_get_eq
    (hZ : containedComponentsIdeal (T.withBoundary L₁) j₁ hj₁ ≠ ⊤) :
    IsStrictPullbackBlowupSeq
      (divisorPullbackMap (T.withBoundary L₁) j₁ hj₁ (lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hj₁)
        (lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hj₁) T.scheme (𝟙 T.scheme) (L₂.get ⟨j₂, hj₂⟩)
        (get_eq_comap_id L₁ L₂ j₁ j₂ hj₁ hj₂ heq))
      (L (restrictTwistedToDivisor (T.withBoundary L₂) j₂ hj₂)).toSequenceOfBlowups
      (L (restrictTwistedToDivisor (T.withBoundary L₁) j₁ hj₁)).toSequenceOfBlowups := by
  have hZ₂ : containedComponentsIdeal (T.withBoundary L₂) j₂ hj₂ ≠ ⊤ := by
    rw [← containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq]
    exact hZ
  have hI := eq_comap_id_of_eq_consolidated376 (hsh.lowerIdealPre_shift T L₁ L₂ j₁ hj₁ j₂ hj₂ heq)
  have hE := sameNontrivialBoundary_map_comap_id_consolidated376 (hsh.boundaryEquiv_restrictedBoundary_reindex T L₁ L₂ j₁ hj₁ j₂ hj₂ heq hBE)
  have hVa : (restrictTwistedToDivisor (T.withBoundary L₁) j₁ hj₁).IsAdmissible :=
    hfacts.valid_lowerPre (T.withBoundary L₁) hV₁ hO₁ hDB₁ j₁ hj₁ hZ
  have hVb : (restrictTwistedToDivisor (T.withBoundary L₂) j₂ hj₂).IsAdmissible :=
    hfacts.valid_lowerPre (T.withBoundary L₂) hV₂ hO₂ hDB₂ j₂ hj₂ hZ₂
  have hda : (restrictTwistedToDivisor (T.withBoundary L₁) j₁ hj₁).krullDimSucc < n :=
    lt_of_lt_of_le (hfacts.lowerTriple_dim_lt (T.withBoundary L₁) hV₁ hcs₁ j₁ hj₁
      (lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hj₁)
      (lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hj₁)) hdim₁
  have hdb : (restrictTwistedToDivisor (T.withBoundary L₂) j₂ hj₂).krullDimSucc < n :=
    lt_of_lt_of_le (hfacts.lowerTriple_dim_lt (T.withBoundary L₂) hV₂ hcs₂ j₂ hj₂
      (lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hj₂)
      (lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hj₂)) hdim₂
  exact isStrictPullbackBlowupSeq_restrictToBoundaryDivisor_of_get_eq hbc hsh n L O hL T L₁ L₂ j₁ hj₁ j₂ hj₂ heq
    (lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hj₁) (lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hj₁)
    (lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hj₂) (lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hj₂)
    hI hE hVa hda hVb hdb


end

structure StrictBoundaryReindexingInvariance (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (n : ℕ)
    (L : PrincipalizationAssignment.{u}) : Prop where
  isStrictPullbackSeq_divisorFamily :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
      (_hbal : T.IsBalanced hV.locallyOfFiniteType) (L₁ L₂ : List T.scheme.IdealSheafData)
      (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length),
      L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩ →
      MarkedIdealWithBoundary.SameNontrivialBoundary (L₂.eraseIdx j₂) (L₁.eraseIdx j₁) →
      (T.withBoundary L₁).IsAdmissible → (T.withBoundary L₂).IsAdmissible →
      IsStrictPullbackBlowupSeq (𝟙 T.scheme)
        (((canonicalAlgorithmRules hres).divisorFamily L j₂ (T.withBoundary L₂)).toSequenceOfBlowups)
        (((canonicalAlgorithmRules hres).divisorFamily L j₁ (T.withBoundary L₁)).toSequenceOfBlowups)

theorem isBoundaryPositionInvariant_divisorFamily (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (n : ℕ)
    (L : PrincipalizationAssignment.{u}) (hsh : StrictBoundaryReindexingInvariance hres n L) :
    IsBoundaryPositionInvariant (fun d => d ≤ n) fun j => (canonicalAlgorithmRules hres).divisorFamily L j := by
  refine ⟨?_⟩
  intro T hdim hO hft hbal E₁ E₂ E₁' E₂' D hBE1 hBE2 hV1 hV2
  have hlen1 : E₁.length < (E₁ ++ D :: E₂).length := by simp
  have hlen2 : E₁'.length < (E₁' ++ D :: E₂').length := by simp
  have hget : (E₁' ++ D :: E₂').get ⟨E₁'.length, hlen2⟩
      = (E₁ ++ D :: E₂).get ⟨E₁.length, hlen1⟩ := by
    rw [get_append_cons_length_consolidated376, get_append_cons_length_consolidated376]
  have hbe : MarkedIdealWithBoundary.SameNontrivialBoundary ((E₁ ++ D :: E₂).eraseIdx E₁.length)
      ((E₁' ++ D :: E₂').eraseIdx E₁'.length) := by
    rw [eraseIdx_append_cons_length_consolidated376, eraseIdx_append_cons_length_consolidated376]
    exact hBE1.append hBE2
  have hmain := hsh.isStrictPullbackSeq_divisorFamily (T.withBoundary (E₁' ++ D :: E₂')) hV2
    hdim hO hbal (E₁' ++ D :: E₂') (E₁ ++ D :: E₂) E₁'.length hlen2 E₁.length hlen1
    hget hbe hV2 hV1
  exact isomorphic_of_isStrictPullbackAlongId_consolidated376 _ _ hmain

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsSmoothPullback
section



namespace DivisorReduction

theorem smooth_of_isPullback (X Y S S' : Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y) (φ : Y ⟶ X)
    (ψ : S' ⟶ S) (hpb : IsPullback σ' ψ φ σ) (hφ : Smooth φ) :
    Smooth ψ :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Smooth) hpb hφ

section
variable (T : MarkedIdealWithBoundary.{u})

theorem orderAtLeastLocus_comap_of_smooth (hV : T.IsAdmissible) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [Smooth h]
    (_hq : h ≫ T.structMap = q) (m : ℕ) :
    orderAtLeastLocus (T.ideal.comap h) m = ⇑h ⁻¹' orderAtLeastLocus T.ideal m := by
  have : CharZero T.base := hV.charZero
  have : Smooth T.structMap := hV.smooth
  exact FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_comap T.base T.structMap h T.ideal m

private theorem withBoundary_withBoundary_consolidated356 (E F : List T.scheme.IdealSheafData) :
    (T.withBoundary E).withBoundary F = T.withBoundary F := rfl


end

private theorem isAdmissible_of_withBoundary_isAdmissible_consolidated356 (S : MarkedIdealWithBoundary.{u})
    (E : List S.scheme.IdealSheafData) (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary S.boundary E)
    (hV : (S.withBoundary E).IsAdmissible) : S.IsAdmissible := by
  have h1 : ((S.withBoundary E).withBoundary S.boundary).IsAdmissible :=
    MarkedIdealWithBoundary.validOfSameNontrivialBoundary _ _ hV hBE.symm
  rw [withBoundary_withBoundary_consolidated356, MarkedIdealWithBoundary.withBoundary_self] at h1
  exact h1

theorem isAdmissible_pullbackAlong_of_withBoundary_isAdmissible :
    ∀ (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base))
      (h : Y ⟶ T.scheme) (E' : List Y.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
        ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible → (T.pullbackAlong Y q h).IsAdmissible := by
  intro T Y q h E' hBE hV
  exact isAdmissible_of_withBoundary_isAdmissible_consolidated356 (T.pullbackAlong Y q h) E' hBE hV

section
variable {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}} {hno : BlowupPreservesNoetherian.{u}} (hfacts : DivisorReductionTerminationProperties hres hno)
include hfacts

theorem containedComponentsIdeal_pullbackAlong_of_isAdmissible_pullbackAlong
    (hvbr : ∀ (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base))
      (h : Y ⟶ T.scheme) (E' : List Y.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
        ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible → (T.pullbackAlong Y q h).IsAdmissible) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [Smooth h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
            List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
            ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
              containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE =
                (containedComponentsIdeal T j hj).comap h := by
  intro T hV Y q h hsm hq E' hBE j hj hjE htake hV'
  have : Smooth h := hsm
  have hj' : j < (T.pullbackAlong Y q h).boundary.length := by
    change j < (T.boundary.map (fun D => D.comap h)).length
    rw [List.length_map]
    exact hj
  have hVal : (T.pullbackAlong Y q h).IsAdmissible := hvbr T Y q h E' hBE hV'
  rw [containedComponentsIdeal_withBoundary T j Y q h E' hjE hj' htake]
  exact hfacts.preIdeal_pullbackAlong T hV Y q h hq hVal j hj hj'

theorem containedComponentsIdeal_pullbackAlong_of_smooth :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [Smooth h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
            List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
            ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
              containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE =
                (containedComponentsIdeal T j hj).comap h :=
  containedComponentsIdeal_pullbackAlong_of_isAdmissible_pullbackAlong hfacts
    isAdmissible_pullbackAlong_of_withBoundary_isAdmissible


end

end DivisorReduction

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.EmptyPulledBackCenter
section


section

namespace DivisorReduction

structure EmptyPulledBackCenterCompatibility : Prop where
  lowerIdealPre_comap_eq_lowerIdealTop_comap :
    ∀ (T : MarkedIdealWithBoundary.{u}) (_hV : T.IsAdmissible) (_hO : T.IsOrderBoundedByMult) (j : ℕ)
      (hj : j < T.boundary.length) (Y : Scheme.{u}) (h : Y ⟶ T.scheme),
      (containedComponentsIdeal T j hj).comap h = ⊤ →
      (lowerIdealAfterBlowup T j hj).comap h = (lowerIdealWithoutBlowup T).comap h
  boundaryEquiv_restrictedBoundary_comap_of_center_comap_eq_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (_hV : T.IsAdmissible) (j : ℕ) (hj : j < T.boundary.length)
      (Y : Scheme.{u}) (h : Y ⟶ T.scheme),
      (containedComponentsIdeal T j hj).comap h = ⊤ →
      MarkedIdealWithBoundary.SameNontrivialBoundary
        (List.map (fun D => D.comap h)
          (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j)))
        (List.map (fun D => D.comap h)
          (List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j)))

structure IsPullbackSeqOfEmptyBlowupSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (L : PrincipalizationAssignment.{u}) (j : ℕ) : Prop where
  isPullbackSeq_of_coSupport_empty :
    ∀ (T : MarkedIdealWithBoundary.{u}) (_hV : T.IsAdmissible) (_hj : j < T.boundary.length) (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [Smooth h],
      h ≫ T.structMap = q →
      ∀ (E' : List Y.IdealSheafData),
        ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
        (orderAtLeastLocus T.ideal T.mult).Nonempty →
        orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult = ∅ →
        ∀ (B' : SequenceOfBlowups Y), B'.length = 0 →
          IsPullbackBlowupSequence h B' (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups)
  isPullbackSeq_of_length_eq_zero :
    ∀ (X X' : Scheme.{u}) (φ : X' ⟶ X) (B' : SequenceOfBlowups X') (B : SequenceOfBlowups X),
      B'.length = 0 → B.length = 0 → IsPullbackBlowupSequence φ B' B
  isPullbackSeq_ofMarkedSeq :
    ∀ (A B : MarkedIdealWithBoundary.{u}) (φ : A.scheme ⟶ B.scheme) (sA : A.SequenceOfBlowups) (sB : B.SequenceOfBlowups),
      IsPullbackBlowupSequence φ sA.toSequenceOfBlowups sB.toSequenceOfBlowups →
      IsPullbackBlowupSequence φ (MarkedBlowupSequenceData.ofMarkedSequence sA).toBlowupSequenceData.toSequenceOfBlowups
        (MarkedBlowupSequenceData.ofMarkedSequence sB).toBlowupSequenceData.toSequenceOfBlowups

structure RestrictedPrincipalizationSmoothPullback (n : ℕ) (L : PrincipalizationAssignment.{u}) (j : ℕ) : Prop where
  isPullbackSeq_lowerMixed :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
      (_hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
      (_hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty) (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h]
      (_hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
      (_hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
      (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary)
      (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible)
      (_hdim' : ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc ≤ n)
      (_hO' : ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult)
      (_hDB' : ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
      (hjE : j < E'.length)
      (_hcs' : (orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult).Nonempty)
      (_hZ : containedComponentsIdeal T j hj ≠ ⊤)
      (_hZc : (containedComponentsIdeal T j hj).comap h = ⊤)
      (_hZ' : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = ⊤),
      IsPullbackBlowupSequence
        (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
          (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
        (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE)).toSequenceOfBlowups
        (L (restrictTwistedToDivisor T j hj)).toSequenceOfBlowups
  isPullbackSeq_lowerTop :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
      (_hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
      (_hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty) (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h]
      (_hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
      (_hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
      (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary)
      (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible)
      (_hdim' : ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc ≤ n)
      (_hO' : ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult)
      (_hDB' : ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
      (hjE : j < E'.length)
      (_hcs' : (orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult).Nonempty)
      (_hZ : containedComponentsIdeal T j hj = ⊤)
      (_hZ' : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = ⊤),
      IsPullbackBlowupSequence
        (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩)
          (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
        (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE)).toSequenceOfBlowups
        (L (restrictToDivisor T j hj)).toSequenceOfBlowups
  isPullbackSeq_lowerPre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
      (_hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
      (_hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty) (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h]
      (_hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
      (_hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
      (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary)
      (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible)
      (_hdim' : ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc ≤ n)
      (_hO' : ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult)
      (_hDB' : ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
      (hjE : j < E'.length)
      (_hcs' : (orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult).Nonempty)
      (_hZ : containedComponentsIdeal T j hj ≠ ⊤)
      (_hZc : (containedComponentsIdeal T j hj).comap h ≠ ⊤)
      (_hZ' : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE =
        (containedComponentsIdeal T j hj).comap h),
      IsPullbackBlowupSequence
        (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
          (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
        (L (restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE)).toSequenceOfBlowups
        (L (restrictTwistedToDivisor T j hj)).toSequenceOfBlowups

theorem divisorFamily_isPullbackBlowupSequence (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : SmoothPullbackCompatibility.{u}) (hsf : FlatOfSmooth.{u}) (n : ℕ) (L : PrincipalizationAssignment.{u})
    (j : ℕ) (hdel : IsPullbackSeqOfEmptyBlowupSeq hres L j)
    (hlow : RestrictedPrincipalizationSmoothPullback n L j)
    (hshape : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReductionSeqEqAmbient hres L j T hV hj)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [Smooth h]
    (hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary)
    (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible)
    (hdim' : ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc ≤ n)
    (hO' : ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult)
    (hDB' : ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
    (hjE : j < E'.length) :
    IsPullbackBlowupSequence h
      (((canonicalAlgorithmRules hres).divisorFamily L j
        ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) := by
  classical
  have hmult : ((T.pullbackAlong Y q h).withBoundary E').mult = T.mult := rfl
  by_cases hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty
  · by_cases hcs' : (orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult).Nonempty
    · have hZeq : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE
          = (containedComponentsIdeal T j hj).comap h :=
        hbc.preIdeal_comap T hV Y q h hq E' hBE j hj hjE htake hV'
      have _hNT : IsNoetherian T.scheme := isNoetherian_scheme_of_isAdmissible T hV
      have _hNY : IsNoetherian Y :=
        isNoetherian_scheme_of_isAdmissible ((T.pullbackAlong Y q h).withBoundary E') hV'
      have _hfl : Flat h := hsf.flat_of_smooth T.scheme Y h inferInstance
      rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j T,
        divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j ((T.pullbackAlong Y q h).withBoundary E')]
      rcases hshape T hV hj hdim hO hbal hcs with ⟨hZ, hpr, hmk, heq⟩ | ⟨hZ, hb, hpr, hmk, heq⟩
      · rcases hshape ((T.pullbackAlong Y q h).withBoundary E') hV' hjE hdim' hO' hDB' hcs' with
          ⟨hZ', hpr', hmk', heq'⟩ | ⟨hZ', hb', hpr', hmk', heq'⟩
        · rw [heq, heq', BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
            BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
          exact hfacts.isPullbackSeq_ambientTower T.scheme Y
            (T.boundary.get ⟨j, hj⟩).subscheme (E'.get ⟨j, hjE⟩).subscheme
            (T.boundary.get ⟨j, hj⟩).subschemeι (E'.get ⟨j, hjE⟩).subschemeι h
            (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩)
              (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
            ((isPullback_divisorPullbackMap hbc T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
              (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake)).flip)
            (MarkedBlowupSequenceData.ofMarkedSequence (L (restrictToDivisor T j hj))).toBlowupSequenceData
            (MarkedBlowupSequenceData.ofMarkedSequence
              (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE))).toBlowupSequenceData
            hpr hpr'
            (hdel.isPullbackSeq_ofMarkedSeq
              (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE) (restrictToDivisor T j hj)
              (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩)
                (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
              (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE))
              (L (restrictToDivisor T j hj))
              (hlow.isPullbackSeq_lowerTop T hV hdim hO hbal hj hcs Y q h hq E' hBE htake hV'
                hdim' hO' hDB' hjE hcs' hZ hZ'))
        · refine absurd ?_ hZ'
          rw [hZeq, hZ]
          exact AlgebraicGeometry.Scheme.IdealSheafData.comap_top ..
      · rcases hshape ((T.pullbackAlong Y q h).withBoundary E') hV' hjE hdim' hO' hDB' hcs' with
          ⟨hZ', hpr', hmk', heq'⟩ | ⟨hZ', hb', hpr', hmk', heq'⟩
        · have htop : (containedComponentsIdeal T j hj).comap h = ⊤ := hZeq.symm.trans hZ'
          rw [heq, heq', BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
            BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
          refine IsPullbackBlowupSequence.prepend_of_comap_eq_top ?_ (containedComponentsIdeal T j hj) hb htop
          exact hfacts.isPullbackSeq_ambientTower T.scheme Y
            (T.boundary.get ⟨j, hj⟩).subscheme (E'.get ⟨j, hjE⟩).subscheme
            (T.boundary.get ⟨j, hj⟩).subschemeι (E'.get ⟨j, hjE⟩).subschemeι h
            (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
              (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
            ((isPullback_divisorPullbackMap hbc T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
              Y h (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake)).flip)
            (MarkedBlowupSequenceData.ofMarkedSequence (L (restrictTwistedToDivisor T j hj))).toBlowupSequenceData
            (MarkedBlowupSequenceData.ofMarkedSequence
              (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE))).toBlowupSequenceData
            hpr hpr'
            (hdel.isPullbackSeq_ofMarkedSeq
              (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE) (restrictTwistedToDivisor T j hj)
              (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
                (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
              (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE))
              (L (restrictTwistedToDivisor T j hj))
              (hlow.isPullbackSeq_lowerMixed T hV hdim hO hbal hj hcs Y q h hq E' hBE htake hV'
                hdim' hO' hDB' hjE hcs' hZ htop hZ'))
        · have hne : (containedComponentsIdeal T j hj).comap h ≠ ⊤ := fun hcc => hZ' (hZeq.trans hcc)
          have hbb : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) ((containedComponentsIdeal T j hj).comap h) :=
            isBlowupAlongIdealSheaf_id_comap_containedComponentsIdeal hres hfacts j T Y q h E' hV' hj hjE hZeq
          rw [heq, heq', BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
            BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
            BlowupSequenceData.prepend_toSequenceOfBlowups_congr hZeq hb' hbb]
          refine IsPullbackBlowupSequence.prepend_of_comap_ne_top ?_ (containedComponentsIdeal T j hj) hb hbb hne
          exact hfacts.isPullbackSeq_ambientTower T.scheme Y
            (T.boundary.get ⟨j, hj⟩).subscheme (E'.get ⟨j, hjE⟩).subscheme
            (T.boundary.get ⟨j, hj⟩).subschemeι (E'.get ⟨j, hjE⟩).subschemeι h
            (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
              (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
            ((isPullback_divisorPullbackMap hbc T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
              Y h (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake)).flip)
            (MarkedBlowupSequenceData.ofMarkedSequence (L (restrictTwistedToDivisor T j hj))).toBlowupSequenceData
            (MarkedBlowupSequenceData.ofMarkedSequence
              (L (restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE))).toBlowupSequenceData
            hpr hpr'
            (hdel.isPullbackSeq_ofMarkedSeq
              (restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE) (restrictTwistedToDivisor T j hj)
              (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
                (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
              (L (restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE))
              (L (restrictTwistedToDivisor T j hj))
              (hlow.isPullbackSeq_lowerPre T hV hdim hO hbal hj hcs Y q h hq E' hBE htake hV'
                hdim' hO' hDB' hjE hcs' hZ hne hZeq))
    · have hempty : orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hcs'
      have hlen' : (((canonicalAlgorithmRules hres).divisorFamily L j
          ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups).length = 0 := by
        refine divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j _ hV' hdim' hO' hDB' hjE ?_
        rw [hmult]
        exact hempty
      exact hdel.isPullbackSeq_of_coSupport_empty T hV hj Y q h hq E' hV' hcs hempty _ hlen'
  · have hempty : orderAtLeastLocus T.ideal T.mult = ∅ := Set.not_nonempty_iff_eq_empty.mp hcs
    have hempty' : orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult = ∅ := by
      rw [orderAtLeastLocus_withBoundary_pullbackAlong hbc T hV Y q h hq E' T.mult, hempty]
      exact Set.preimage_empty
    have hlen : (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups).length = 0 :=
      divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO hbal hj hempty
    have hlen' : (((canonicalAlgorithmRules hres).divisorFamily L j
        ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups).length = 0 := by
      refine divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j _ hV' hdim' hO' hDB' hjE ?_
      rw [hmult]
      exact hempty'
    exact hdel.isPullbackSeq_of_length_eq_zero T.scheme Y h _ _ hlen' hlen

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.FieldBaseChangeCompatibility
section



noncomputable abbrev fieldBaseChangeProjection (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K]
    (f : T.base →+* K) :=
  CategoryTheory.Limits.pullback.fst T.structMap (FunctorialResolution.EmbeddedResolution.specMapOfFieldHom T.base K f)

theorem get_eq_comap_fieldBaseChangeProjection (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (K : Type u) [Field K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData) (hjE : j < E'.length)
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary) :
    E'.get ⟨j, hjE⟩ = (T.boundary.get ⟨j, hj⟩).comap (fieldBaseChangeProjection T K f) := by
  have hj' : j < (T.baseChange K f).boundary.length := by
    have h := congrArg List.length htake
    simp only [List.length_take] at h
    omega
  have h1 : E'.get ⟨j, hjE⟩ = (T.baseChange K f).boundary.get ⟨j, hj'⟩ :=
    get_eq_get_of_take_succ_eq E' (T.baseChange K f).boundary j htake hjE hj'
  have key : ∀ (hh :
      j < (List.map (fun D => D.comap (fieldBaseChangeProjection T K f)) T.boundary).length),
      (List.map (fun D => D.comap (fieldBaseChangeProjection T K f)) T.boundary)[j]'hh
        = (T.boundary[j]'hj).comap (fieldBaseChangeProjection T K f) := by
    intro hh
    simp
  exact h1.trans (key hj')

structure FieldBaseChangeCompatibility : Prop where
  coSupport_baseChange :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (K : Type u) [Field K] (f : T.base →+* K)
      (E' : List (T.baseChange K f).scheme.IdealSheafData) (m : ℕ),
      orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal m =
        (fieldBaseChangeProjection T K f) ⁻¹' orderAtLeastLocus T.ideal m
  flat_proj :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K),
      Flat (fieldBaseChangeProjection T K f)
  surjective_proj :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K),
      AlgebraicGeometry.Surjective (fieldBaseChangeProjection T K f)
  withBoundary_preIdeal :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
      (E' : List (T.baseChange K f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E' →
      ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
        List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary →
        ((T.baseChange K f).withBoundary E').IsAdmissible →
        DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
          (DivisorReduction.containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f)

structure RestrictedPrincipalizationFieldBaseChange (n : ℕ) (L : PrincipalizationAssignment.{u}) (j : ℕ) : Prop where
  isStrictPullbackSeq_lowerTop :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
      (_hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
      (_hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty) (K : Type u) [Field K] [CharZero K]
      (f : T.base →+* K) (E' : List (T.baseChange K f).scheme.IdealSheafData)
      (_hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E')
      (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
      (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
      (_hdim' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n)
      (_hO' : ((T.baseChange K f).withBoundary E').IsOrderBoundedByMult)
      (_hDB' : ((T.baseChange K f).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
      (hjE : j < E'.length)
      (_hcs' : (orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal T.mult).Nonempty)
      (_hZ : DivisorReduction.containedComponentsIdeal T j hj = ⊤)
      (_hZ' : DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE = ⊤),
      IsStrictPullbackBlowupSeq
        (DivisorReduction.divisorPullbackMap T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
          (DivisorReduction.lowerBoundaryWithoutBlowup T) (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
          (E'.get ⟨j, hjE⟩) (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake))
        (L (DivisorReduction.restrictToDivisor ((T.baseChange K f).withBoundary E') j hjE)).toSequenceOfBlowups
        (L (DivisorReduction.restrictToDivisor T j hj)).toSequenceOfBlowups
  isStrictPullbackSeq_lowerPre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
      (_hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
      (_hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty) (K : Type u) [Field K] [CharZero K]
      (f : T.base →+* K) (E' : List (T.baseChange K f).scheme.IdealSheafData)
      (_hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E')
      (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
      (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
      (_hdim' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n)
      (_hO' : ((T.baseChange K f).withBoundary E').IsOrderBoundedByMult)
      (_hDB' : ((T.baseChange K f).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
      (hjE : j < E'.length)
      (_hcs' : (orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal T.mult).Nonempty)
      (_hZ : DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤)
      (_hZ' : DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
        (DivisorReduction.containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f)),
      IsStrictPullbackBlowupSeq
        (DivisorReduction.divisorPullbackMap T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
          (DivisorReduction.lowerBoundaryAfterBlowup T j hj) (T.baseChange K f).scheme
          (fieldBaseChangeProjection T K f) (E'.get ⟨j, hjE⟩)
          (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake))
        (L (DivisorReduction.restrictTwistedToDivisor ((T.baseChange K f).withBoundary E') j hjE)).toSequenceOfBlowups
        (L (DivisorReduction.restrictTwistedToDivisor T j hj)).toSequenceOfBlowups

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (hfbc : FieldBaseChangeCompatibility.{u}) (n : ℕ) (L : PrincipalizationAssignment.{u}) (j : ℕ) (hlow : RestrictedPrincipalizationFieldBaseChange n L j)
include hfacts hbc hfbc hlow

theorem divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange (_hshape : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      orderAtLeastLocus T.ideal T.mult ≠ ∅ → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
    (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hdim' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n)
    (hO' : ((T.baseChange K f).withBoundary E').IsOrderBoundedByMult)
    (hDB' : ((T.baseChange K f).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
    (hjE : j < E'.length) :
    IsStrictPullbackBlowupSeq (fieldBaseChangeProjection T K f)
      (((canonicalAlgorithmRules hres).divisorFamily L j ((T.baseChange K f).withBoundary E')).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) := by
  have : IsNoetherian T.scheme :=
    DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
  have hNTb : IsNoetherian ((T.baseChange K f).withBoundary E').scheme :=
    DivisorReduction.isNoetherian_scheme_of_isAdmissible _ hV'
  have : IsNoetherian (T.baseChange K f).scheme := hNTb
  have : IsNoetherian
      (CategoryTheory.Limits.pullback T.structMap (specMapOfFieldHom T.base K f)) := hNTb
  have : Flat (fieldBaseChangeProjection T K f) := hfbc.flat_proj T K f
  have : Flat
      (show (T.baseChange K f).scheme ⟶ T.scheme from fieldBaseChangeProjection T K f) :=
    hfbc.flat_proj T K f
  have : Flat
      (show ((T.baseChange K f).withBoundary E').scheme ⟶ T.scheme from
        fieldBaseChangeProjection T K f) := hfbc.flat_proj T K f
  have hsurj0 : AlgebraicGeometry.Surjective (fieldBaseChangeProjection T K f) :=
    hfbc.surjective_proj T K f
  have : AlgebraicGeometry.Surjective
      (show (T.baseChange K f).scheme ⟶ T.scheme from fieldBaseChangeProjection T K f) :=
    hfbc.surjective_proj T K f
  have : AlgebraicGeometry.Surjective
      (show ((T.baseChange K f).withBoundary E').scheme ⟶ T.scheme from
        fieldBaseChangeProjection T K f) := hfbc.surjective_proj T K f
  have hmult : ((T.baseChange K f).withBoundary E').mult = T.mult := by
    rw [MarkedIdealWithBoundary.withBoundary_mult, MarkedIdealWithBoundary.baseChange_mult]
  have hcsEq : orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal T.mult =
      (fieldBaseChangeProjection T K f) ⁻¹' orderAtLeastLocus T.ideal T.mult :=
    hfbc.coSupport_baseChange T hV K f E' T.mult
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = ∅
  · have hcs'' : orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal
        ((T.baseChange K f).withBoundary E').mult = ∅ := by
      rw [hmult, hcsEq, hcs]
      exact Set.preimage_empty
    exact IsStrictPullbackBlowupSeq.of_length_zero _ _ _
      (divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j _ hV' hdim' hO' hDB' hjE hcs'')
      (divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO hbal hj hcs)
  · have hcsne : (orderAtLeastLocus T.ideal T.mult).Nonempty := Set.nonempty_iff_ne_empty.2 hcs
    have hcsne' : (orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal T.mult).Nonempty := by
      rw [hcsEq]
      exact hcsne.preimage hsurj0.surj
    have hcs' : orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal
        ((T.baseChange K f).withBoundary E').mult ≠ ∅ := by
      rw [hmult]
      exact Set.nonempty_iff_ne_empty.1 hcsne'
    have hpre : DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
        (DivisorReduction.containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f) :=
      hfbc.withBoundary_preIdeal T hV K f E' hBE j hj hjE htake hV'
    rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j ((T.baseChange K f).withBoundary E'),
      divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j T]
    rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO hbal hcs with
      ⟨hZ, hpr, hmk0, heq⟩ | ⟨hZ, hb, hpr, hmk0, heq⟩
    · have hZ' : DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE = ⊤ := by
        rw [hpre, hZ]
        simp
        rfl
      rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j ((T.baseChange K f).withBoundary E')
          hV' hjE hO' hDB' hcs' with ⟨-, hpr2, hmk2, heq2⟩ | ⟨hZ2, -⟩
      · have hlower := hlow.isStrictPullbackSeq_lowerTop T hV hdim hO hbal hj hcsne K f E' hBE
          htake hV' hdim' hO' hDB' hjE hcsne' hZ hZ'
        have hlower2 := IsStrictPullbackBlowupSeq.ofMarkedSequence
          (DivisorReduction.divisorPullbackMap T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) (T.baseChange K f).scheme
            (fieldBaseChangeProjection T K f) (E'.get ⟨j, hjE⟩)
            (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake))
          (L (DivisorReduction.restrictToDivisor ((T.baseChange K f).withBoundary E') j hjE))
          (L (DivisorReduction.restrictToDivisor T j hj)) hlower
        rw [heq hmk0, heq2 hmk2, BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
          BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
        exact hfacts.isStrictPullbackSeq_ambientTower T.scheme (T.baseChange K f).scheme
          (T.boundary.get ⟨j, hj⟩).subscheme (E'.get ⟨j, hjE⟩).subscheme
          (T.boundary.get ⟨j, hj⟩).subschemeι (E'.get ⟨j, hjE⟩).subschemeι
          (fieldBaseChangeProjection T K f)
          (DivisorReduction.divisorPullbackMap T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) (T.baseChange K f).scheme
            (fieldBaseChangeProjection T K f) (E'.get ⟨j, hjE⟩)
            (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake))
          ((DivisorReduction.isPullback_divisorPullbackMap hbc T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) (T.baseChange K f).scheme
            (fieldBaseChangeProjection T K f) (E'.get ⟨j, hjE⟩)
            (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake)).flip)
          (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData
          (MarkedBlowupSequenceData.ofMarkedSequence
            (L (DivisorReduction.restrictToDivisor ((T.baseChange K f).withBoundary E') j hjE))).toBlowupSequenceData
          hpr hpr2 hlower2
      · exact absurd hZ' hZ2
    · have hZ' : DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE ≠ ⊤ := by
        rw [hpre]
        exact DivisorReduction.comap_ne_top_of_surjective hbc (fieldBaseChangeProjection T K f)
          (DivisorReduction.containedComponentsIdeal T j hj) hZ
      rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j ((T.baseChange K f).withBoundary E')
          hV' hjE hO' hDB' hcs' with ⟨hZ2, -⟩ | ⟨-, hb2, hpr2, hmk2, heq2⟩
      · exact absurd hZ2 hZ'
      · have hlower := hlow.isStrictPullbackSeq_lowerPre T hV hdim hO hbal hj hcsne K f E' hBE
          htake hV' hdim' hO' hDB' hjE hcsne' hZ hpre
        have hlower2 := IsStrictPullbackBlowupSeq.ofMarkedSequence
          (DivisorReduction.divisorPullbackMap T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
            (DivisorReduction.lowerBoundaryAfterBlowup T j hj) (T.baseChange K f).scheme
            (fieldBaseChangeProjection T K f) (E'.get ⟨j, hjE⟩)
            (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake))
          (L (DivisorReduction.restrictTwistedToDivisor ((T.baseChange K f).withBoundary E') j hjE))
          (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hlower
        have key : IsStrictPullbackBlowupSeq (fieldBaseChangeProjection T K f)
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian
              ((T.baseChange K f).withBoundary E') j hjE
              (DivisorReduction.lowerIdealAfterBlowup ((T.baseChange K f).withBoundary E') j hjE)
              (DivisorReduction.lowerBoundaryAfterBlowup ((T.baseChange K f).withBoundary E') j hjE)
              (L (DivisorReduction.restrictTwistedToDivisor ((T.baseChange K f).withBoundary E') j hjE))
              hpr2).toSequenceOfBlowups
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
              (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
              (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr).toSequenceOfBlowups :=
          hfacts.isStrictPullbackSeq_ambientTower T.scheme (T.baseChange K f).scheme
            (T.boundary.get ⟨j, hj⟩).subscheme (E'.get ⟨j, hjE⟩).subscheme
            (T.boundary.get ⟨j, hj⟩).subschemeι (E'.get ⟨j, hjE⟩).subschemeι
            (fieldBaseChangeProjection T K f)
            (DivisorReduction.divisorPullbackMap T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) (T.baseChange K f).scheme
              (fieldBaseChangeProjection T K f) (E'.get ⟨j, hjE⟩)
              (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake))
            ((DivisorReduction.isPullback_divisorPullbackMap hbc T j hj
              (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
              (T.baseChange K f).scheme (fieldBaseChangeProjection T K f) (E'.get ⟨j, hjE⟩)
              (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake)).flip)
            (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData
            (MarkedBlowupSequenceData.ofMarkedSequence
              (L (DivisorReduction.restrictTwistedToDivisor ((T.baseChange K f).withBoundary E') j
                hjE))).toBlowupSequenceData
            hpr hpr2 hlower2
        have hb2' : Blowup.IsBlowupAlongIdealSheaf (𝟙 ((T.baseChange K f).withBoundary E').scheme)
            (DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE) := hb2
        rw [hpre] at hb2'
        rw [heq hmk0, heq2 hmk2, BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
          BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
          BlowupSequenceData.prepend_toSequenceOfBlowups_congr hpre hb2 hb2'
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian
              ((T.baseChange K f).withBoundary E') j hjE
              (DivisorReduction.lowerIdealAfterBlowup ((T.baseChange K f).withBoundary E') j hjE)
              (DivisorReduction.lowerBoundaryAfterBlowup ((T.baseChange K f).withBoundary E') j hjE)
              (L (DivisorReduction.restrictTwistedToDivisor ((T.baseChange K f).withBoundary E') j hjE)) hpr2)]
        exact key.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb hb2'

theorem divisorFamily_isPullbackSequenceOfBlowups_fieldBaseChange (hshape : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      orderAtLeastLocus T.ideal T.mult ≠ ∅ → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj)
    (hcenters : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.krullDimSucc ≤ n → T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
      ∀ i, i < ((canonicalAlgorithmRules hres).divisorFamily L j T).length →
        ((((canonicalAlgorithmRules hres).divisorFamily L j T).center i).support.carrier).Nonempty)
    (hprune : ∀ (Y : Scheme.{u}) (s : SequenceOfBlowups Y),
      (∀ i, i < s.length → s.center i ≠ ⊤) → s.withoutIsoBlowups.Isomorphic s)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
    (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hdim' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n)
    (hO' : ((T.baseChange K f).withBoundary E').IsOrderBoundedByMult)
    (hDB' : ((T.baseChange K f).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
    (hjE : j < E'.length) :
    IsPullbackBlowupSequence (fieldBaseChangeProjection T K f)
      (((canonicalAlgorithmRules hres).divisorFamily L j ((T.baseChange K f).withBoundary E')).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) := by
  have hstrict := divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange hres hfacts hbc hfbc n L j hlow hshape
    T hV hdim hO hbal hj K f E' hBE htake hV' hdim' hO' hDB' hjE
  refine hstrict.isPullbackSequenceOfBlowups_withoutIsoBlowups.of_isomorphic ?_
  refine hprune _ _ ?_
  intro i hi
  exact (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp
    (hcenters ((T.baseChange K f).withBoundary E') hV' hdim' hO' hDB' hjE i hi)


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.KernelOfAmbientEmbedding
section


section

section
variable {S X : Scheme.{u}} (ι : S ⟶ X) [IsClosedImmersion ι] [IsNoetherian X] (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (hcen : ∀ i < s.length, ∀ T ∈ irreducibleComponents ↥(s.obj i), ¬T ⊆ ↑(s.center i).support)

theorem ker_embeddingIntoAmbientBlowupSequence_zero :
    AlgebraicGeometry.Scheme.Hom.ker (embeddingIntoAmbientBlowupSequence ι s hres hno hcen 0) =
      (AlgebraicGeometry.Scheme.Hom.ker ι).comap
        (ambientBlowupSequence ι s hres hno hcen).isoZero.hom := by
  have h1 : embeddingIntoAmbientBlowupSequence ι s hres hno hcen 0 = s.isoZero.hom ≫ ι :=
    embeddingIntoAmbientBlowupSequence_zero ι s hres hno hcen
  have h2 : (AlgebraicGeometry.Scheme.Hom.ker ι).comap
      (ambientBlowupSequence ι s hres hno hcen).isoZero.hom
      = AlgebraicGeometry.Scheme.Hom.ker ι := by
    rw [ambientBlowupSequence_isoObjZero]
    exact AlgebraicGeometry.Scheme.IdealSheafData.comap_id _
  rw [h1, h2]
  exact Scheme.Hom.ker_comp_of_isIso s.isoZero.hom ι

private theorem forall_le_ker_embeddingIntoAmbient_eq_boundary_get_consolidated373 (E : List X.IdealSheafData) (j : ℕ) (hj : j < E.length)
    (hE : E.get ⟨j, hj⟩ = AlgebraicGeometry.Scheme.Hom.ker ι) :
    ∀ t : ℕ, t ≤ s.length →
      ∀ hjt : j < ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).length,
        AlgebraicGeometry.Scheme.Hom.ker (embeddingIntoAmbientBlowupSequence ι s hres hno hcen t) =
          ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).get ⟨j, hjt⟩ := by
  intro t
  induction t with
  | zero =>
      intro _ hjt
      simp only [List.get_eq_getElem] at hE ⊢
      rw [ker_embeddingIntoAmbientBlowupSequence_zero]
      simp only [BlowupSequenceData.boundary_zero, List.getElem_map, hE]
  | succ n ih =>
      intro hn hjt
      have hn' : n < s.length := hn
      have hjn : j < ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E n).length := by
        rw [BlowupSequenceData.boundary_length]; omega
      rw [ker_embeddingIntoAmbientBlowupSequence_succ ι s hres hno hcen n hn', ih (le_of_lt hn') hjn]
      simp only [List.get_eq_getElem, BlowupSequenceData.boundary_succ]
      rw [List.getElem_append_left (by simpa using hjn), List.getElem_map]

theorem ker_embeddingIntoAmbientBlowupSequence_eq_boundary_get (E : List X.IdealSheafData) (j : ℕ) (hj : j < E.length)
    (hE : E.get ⟨j, hj⟩ = AlgebraicGeometry.Scheme.Hom.ker ι)
    (t : ℕ) (ht : t ≤ s.length)
    (hjt : j < ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).length) :
    AlgebraicGeometry.Scheme.Hom.ker (embeddingIntoAmbientBlowupSequence ι s hres hno hcen t) =
      ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).get ⟨j, hjt⟩ :=
  forall_le_ker_embeddingIntoAmbient_eq_boundary_get_consolidated373 ι s hres hno hcen E j hj hE t ht hjt


end

namespace DivisorReduction

variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})

section
variable (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)

theorem ker_embeddingIntoAmbient_zero_eq_comap_isoObjZero (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    AlgebraicGeometry.Scheme.Hom.ker
        (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr 0) =
      (T.boundary.get ⟨j, hj⟩).comap (pushedMarkedSeq hres hno T j hj s hpr hmk).isoZero.hom := by
  have h0 := ker_embeddingIntoAmbientBlowupSequence_zero (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
  rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι] at h0
  exact h0

theorem ker_embeddingIntoAmbient_zero_eq_comap_blowupMorphism (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    AlgebraicGeometry.Scheme.Hom.ker
        (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr 0) =
      ((T.boundary.get ⟨j, hj⟩).comap
          (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).isoZero.hom).comap
        ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc 0) := by
  have h0 := ker_embeddingIntoAmbientBlowupSequence_zero (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
  rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι] at h0
  have hA : (T.boundary.get ⟨j, hj⟩).comap
      (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).isoZero.hom = T.boundary.get ⟨j, hj⟩ :=
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id _
  have hB : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc 0
      = (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).isoZero.hom := by
    rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, BlowupSequenceData.toMarkedBlowupSequenceData_blowupMorphism,
      BlowupSequenceData.prepend_blowupMorphism_zero]
    exact rfl
  rw [hA, hB]
  exact h0


end

theorem isSmoothDivisor_ker_embeddingIntoAmbient_of_eq_top (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (_hob : T.IsOrderBoundedByMult) (_hbal : T.IsBalanced hV.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length) (_hpre : containedComponentsIdeal T j hj = ⊤)
    (_hlow : (restrictToDivisor T j hj).IsAdmissible)
    [IsNoetherian T.scheme] (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary)
    (t : ℕ) (ht : t ≤ s.length) :
    IsSmoothDivisor ((pushedMarkedSeq hres hno T j hj s hpr hmk).projectionToSpec t)
      (AlgebraicGeometry.Scheme.Hom.ker
        (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t)) := by
  have hjt : j < ((ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t).length := by
    rw [BlowupSequenceData.boundary_length]; omega
  have htS : t ≤ (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.length := by
    rw [MarkedBlowupSequenceData.ofMarkedSequence_length]; exact ht
  have hker : AlgebraicGeometry.Scheme.Hom.ker
      (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t) =
      ((ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t).get
          ⟨j, hjt⟩ :=
    ker_embeddingIntoAmbientBlowupSequence_eq_boundary_get (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr T.boundary j hj
      (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι _).symm t htS hjt
  have hbd : (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t =
      (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t := by
    rw [MarkedBlowupSequenceData.toMarkedSequence_boundary, BlowupSequenceData.toMarkedBlowupSequenceData_boundary]
    exact rfl
  have hpl : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).length =
      s.toSequenceOfBlowups.length := by
    have hh := ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
    rw [MarkedBlowupSequenceData.ofMarkedSequence_length] at hh
    exact hh
  have htlen : t ≤ (pushedMarkedSeq hres hno T j hj s hpr hmk).toSequenceOfBlowups.length := by
    rw [MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length, hpl]
    exact ht
  have hsnc := MarkedSequenceOfBlowups.inStrictNormalCrossingPosition_projectionToSpec_boundary effectiveCartierSupportContainsNoComponent hV
    (pushedMarkedSeq hres hno T j hj s hpr hmk) t htlen
  have key : AlgebraicGeometry.Scheme.Hom.ker
      (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t) ∈
      (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t := by
    rw [hker]
    exact List.getElem_mem _
  have key2 : AlgebraicGeometry.Scheme.Hom.ker
      (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t) ∈
      (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t := by
    rw [hbd]
    exact key
  exact ((inStrictNormalCrossingPosition_iff _ _).mp hsnc).1 _ key2

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BaseChangeMorphismProperties
section



theorem smooth_id :
    ∀ (X : Scheme.{u}), Smooth (CategoryTheory.CategoryStruct.id X) := by
  intro X
  infer_instance

theorem surjective_id :
    ∀ (X : Scheme.{u}), AlgebraicGeometry.Surjective (CategoryTheory.CategoryStruct.id X) := by
  intro X
  constructor
  intro x
  exact ⟨x, rfl⟩

theorem comap_comap :
    ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (I : Z.IdealSheafData),
      (I.comap g).comap f = I.comap (f ≫ g) := by
  intro X Y Z f g I
  simp

theorem comap_ne_top_of_surjective :
    ∀ (X Y : Scheme.{u}) (h : Y ⟶ X) [AlgebraicGeometry.Surjective h] (Z : X.IdealSheafData),
      Z ≠ ⊤ → Z.comap h ≠ ⊤ := by
  intro X Y h hsurj Z hZ
  have hne : (↑Z.support : Set ↥X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro he
    exact hZ ((Scheme.IdealSheafData.eq_top_iff_support_eq_empty Z).mpr he)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy⟩ := hsurj.1 x
  subst hy
  refine (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp ⟨y, ?_⟩
  simpa [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] using hx

theorem flat_fieldBaseChangeProjection :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K),
      Flat (fieldBaseChangeProjection T K f) := by
  intro T K _ f
  have hflat : Flat (specMapOfFieldHom T.base K f) := instFlatSpecMapOfFieldHom ..
  exact MorphismProperty.of_isPullback
    ((CategoryTheory.IsPullback.of_hasPullback T.structMap (specMapOfFieldHom T.base K f)).flip)
    hflat

theorem surjective_fieldBaseChangeProjection :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K),
      AlgebraicGeometry.Surjective (fieldBaseChangeProjection T K f) := by
  intro T K _ f
  have hsurj : AlgebraicGeometry.Surjective (specMapOfFieldHom T.base K f) :=
    instSurjectiveSpecMapOfFieldHom ..
  exact surjective_snd_of_isPullback_of_surjective T.structMap
    (CategoryTheory.Limits.pullback.snd T.structMap (specMapOfFieldHom T.base K f))
    (specMapOfFieldHom T.base K f) (fieldBaseChangeProjection T K f)
    (CategoryTheory.IsPullback.of_hasPullback T.structMap (specMapOfFieldHom T.base K f)).flip

theorem comap_fieldBaseChangeProjection_ne_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K)
      (I : T.scheme.IdealSheafData), I ≠ ⊤ → I.comap (fieldBaseChangeProjection T K f) ≠ ⊤ := by
  intro T K _ f I hI
  have : AlgebraicGeometry.Surjective (fieldBaseChangeProjection T K f) :=
    surjective_fieldBaseChangeProjection T K f
  exact comap_ne_top_of_surjective _ _ (fieldBaseChangeProjection T K f) I hI

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryPositionInvariance
section


section

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (hsh : DivisorReduction.BoundaryReindexingInvariance.{u}) (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O) (hshape : ∀ (j : ℕ) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length), T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType → (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj)
include hfacts hbc hsh hL hshape

theorem isStrictPullbackBlowupSeq_id_divisorFamily_of_get_eq
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) (L₁ L₂ : List T.scheme.IdealSheafData)
    (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length)
    (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (L₂.eraseIdx j₂) (L₁.eraseIdx j₁))
    (hV₁ : (T.withBoundary L₁).IsAdmissible) (hV₂ : (T.withBoundary L₂).IsAdmissible) :
    IsStrictPullbackBlowupSeq (𝟙 T.scheme)
      (((canonicalAlgorithmRules hres).divisorFamily L j₂ (T.withBoundary L₂)).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j₁ (T.withBoundary L₁)).toSequenceOfBlowups) := by
  classical
  by_cases hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty
  · have hN : IsNoetherian T.scheme :=
      DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
    have hN₁ : IsNoetherian (T.withBoundary L₁).scheme :=
      DivisorReduction.isNoetherian_scheme_of_isAdmissible _ hV₁
    have hN₂ : IsNoetherian (T.withBoundary L₂).scheme :=
      DivisorReduction.isNoetherian_scheme_of_isAdmissible _ hV₂
    have hflat : Flat (𝟙 T.scheme) := inferInstance
    have hjb₁ : j₁ < (T.withBoundary L₁).boundary.length := hj₁
    have hjb₂ : j₂ < (T.withBoundary L₂).boundary.length := hj₂
    have hpre : DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁ =
        DivisorReduction.containedComponentsIdeal (T.withBoundary L₂) j₂ hjb₂ :=
      DivisorReduction.containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq
    have hs₁ : _ ∨ _ := hshape j₁ (T.withBoundary L₁) hV₁ hjb₁ hdim hO hbal hcs
    have hs₂ : _ ∨ _ := hshape j₂ (T.withBoundary L₂) hV₂ hjb₂ hdim hO hbal hcs
    simp only [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq]
    rcases hs₁ with ⟨hZ₁, hpr₁, hmk₁, he₁⟩ | ⟨hZ₁, hb₁, hpr₁, hmk₁, he₁⟩
    · rcases hs₂ with ⟨hZ₂, hpr₂, hmk₂, he₂⟩ | ⟨hZ₂, hb₂, hpr₂, hmk₂, he₂⟩
      · have hstep : IsStrictPullbackBlowupSeq (𝟙 T.scheme)
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₂) j₂ hjb₂
              (DivisorReduction.lowerIdealWithoutBlowup (T.withBoundary L₂))
              (DivisorReduction.lowerBoundaryWithoutBlowup (T.withBoundary L₂))
              (L (DivisorReduction.restrictToDivisor (T.withBoundary L₂) j₂ hjb₂)) hpr₂).toSequenceOfBlowups
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₁) j₁ hjb₁
              (DivisorReduction.lowerIdealWithoutBlowup (T.withBoundary L₁))
              (DivisorReduction.lowerBoundaryWithoutBlowup (T.withBoundary L₁))
              (L (DivisorReduction.restrictToDivisor (T.withBoundary L₁) j₁ hjb₁)) hpr₁).toSequenceOfBlowups :=
          hfacts.isStrictPullbackSeq_ambientTower T.scheme T.scheme
            ((L₁.get ⟨j₁, hj₁⟩).subscheme) ((L₂.get ⟨j₂, hj₂⟩).subscheme)
            ((L₁.get ⟨j₁, hj₁⟩).subschemeι) ((L₂.get ⟨j₂, hj₂⟩).subschemeι)
            (𝟙 T.scheme) _
            ((DivisorReduction.isPullback_divisorPullbackMap hbc (T.withBoundary L₁) j₁ hjb₁
              (DivisorReduction.lowerIdealWithoutBlowup (T.withBoundary L₁))
              (DivisorReduction.lowerBoundaryWithoutBlowup (T.withBoundary L₁)) T.scheme (𝟙 T.scheme)
              (L₂.get ⟨j₂, hj₂⟩) (get_eq_comap_id L₁ L₂ j₁ j₂ hj₁ hj₂ heq)).flip)
            _ _ hpr₁ hpr₂
            (IsStrictPullbackBlowupSeq.ofMarkedSequence
              (A := DivisorReduction.restrictToDivisor (T.withBoundary L₂) j₂ hjb₂)
              (B := DivisorReduction.restrictToDivisor (T.withBoundary L₁) j₁ hjb₁) _ _ _
              (DivisorReduction.isStrictPullbackBlowupSeq_restrictToDivisor_of_get_eq_of_eq_top hres hfacts n L O hL hbc hsh
                T L₁ L₂ j₁ hj₁ j₂ hj₂ heq hBE hV₁ hdim hO hbal hcs hV₂ hdim hO hbal hcs hZ₁))
        rw [he₁, he₂]
        simp only [BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
        exact hstep
      · exact absurd (hpre.symm.trans hZ₁) hZ₂
    · rcases hs₂ with ⟨hZ₂, hpr₂, hmk₂, he₂⟩ | ⟨hZ₂, hb₂, hpr₂, hmk₂, he₂⟩
      · exact absurd (hpre.trans hZ₂) hZ₁
      · have hcomap : (DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁).comap
            (𝟙 (T.withBoundary L₁).scheme) =
            DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁ := by
          rw [Scheme.IdealSheafData.comap_id]
        have hZZ : DivisorReduction.containedComponentsIdeal (T.withBoundary L₂) j₂ hjb₂ =
            (DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁).comap
              (𝟙 (T.withBoundary L₁).scheme) := hpre.symm.trans hcomap.symm
        have hb₁' : Blowup.IsBlowupAlongIdealSheaf (𝟙 (T.withBoundary L₁).scheme)
            ((DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁).comap
              (𝟙 (T.withBoundary L₁).scheme)) := by
          rw [hcomap]
          exact hb₁
        have hstep : IsStrictPullbackBlowupSeq (𝟙 T.scheme)
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₂) j₂ hjb₂
              (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
              (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
              (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₂) j₂ hjb₂)) hpr₂).toSequenceOfBlowups
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₁) j₁ hjb₁
              (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
              (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
              (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₁) j₁ hjb₁)) hpr₁).toSequenceOfBlowups :=
          hfacts.isStrictPullbackSeq_ambientTower T.scheme T.scheme
            ((L₁.get ⟨j₁, hj₁⟩).subscheme) ((L₂.get ⟨j₂, hj₂⟩).subscheme)
            ((L₁.get ⟨j₁, hj₁⟩).subschemeι) ((L₂.get ⟨j₂, hj₂⟩).subschemeι)
            (𝟙 T.scheme) _
            ((DivisorReduction.isPullback_divisorPullbackMap hbc (T.withBoundary L₁) j₁ hjb₁
              (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
              (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hjb₁) T.scheme (𝟙 T.scheme)
              (L₂.get ⟨j₂, hj₂⟩) (get_eq_comap_id L₁ L₂ j₁ j₂ hj₁ hj₂ heq)).flip)
            _ _ hpr₁ hpr₂
            (IsStrictPullbackBlowupSeq.ofMarkedSequence
              (A := DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₂) j₂ hjb₂)
              (B := DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₁) j₁ hjb₁) _ _ _
              (DivisorReduction.isStrictPullbackBlowupSeq_restrictTwistedToDivisor_of_get_eq hres hfacts n L O hL hbc hsh
                T L₁ L₂ j₁ hj₁ j₂ hj₂ heq hBE hV₁ hdim hO hbal hcs hV₂ hdim hO hbal hcs hZ₁))
        have hfin : IsStrictPullbackBlowupSeq (𝟙 T.scheme)
            (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal (T.withBoundary L₂) j₂ hjb₂) hb₂
              (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₂) j₂
                hjb₂ (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
                (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
                (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₂) j₂ hjb₂)) hpr₂)).toSequenceOfBlowups
            (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁) hb₁
              (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₁) j₁
                hjb₁ (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
                (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
                (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₁) j₁ hjb₁)) hpr₁)).toSequenceOfBlowups := by
          rw [BlowupSequenceData.prepend_toSequenceOfBlowups_congr hZZ hb₂ hb₁'
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₂) j₂ hjb₂
              (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
              (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
              (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₂) j₂ hjb₂)) hpr₂)]
          exact IsStrictPullbackBlowupSeq.prepend hstep _ hb₁ hb₁'
        rw [he₁, he₂]
        simp only [BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
        exact hfin
  · have hcs0 : orderAtLeastLocus T.ideal T.mult = ∅ := Set.not_nonempty_iff_eq_empty.mp hcs
    exact IsStrictPullbackBlowupSeq.of_length_zero _ _ _
      (divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j₂ (T.withBoundary L₂) hV₂ hdim hO hbal
        hj₂ hcs0)
      (divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j₁ (T.withBoundary L₁) hV₁ hdim hO hbal
        hj₁ hcs0)

theorem strictBoundaryReindexingInvariance_of_divisorReductionSeqEqAmbient
    :
    DivisorReduction.StrictBoundaryReindexingInvariance hres n L :=
  ⟨fun T hV hdim hO hbal L₁ L₂ j₁ hj₁ j₂ hj₂ heq hBE hV₁ hV₂ =>
    isStrictPullbackBlowupSeq_id_divisorFamily_of_get_eq hres hfacts hbc hsh n L O hL hshape T hV hdim hO hbal
      L₁ L₂ j₁ hj₁ j₂ hj₂ heq hBE hV₁ hV₂⟩

theorem isBoundaryPositionInvariant_divisorFamily_of_divisorReductionSeqEqAmbient
    :
    IsBoundaryPositionInvariant (fun d => d ≤ n) fun j => (canonicalAlgorithmRules hres).divisorFamily L j :=
  DivisorReduction.isBoundaryPositionInvariant_divisorFamily hres n L
    (strictBoundaryReindexingInvariance_of_divisorReductionSeqEqAmbient hres hfacts hbc hsh n L O hL hshape)


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsFieldBaseChange
section



theorem isAdmissible_of_withBoundary_isAdmissible
    (hvbr : ∀ (S : MarkedIdealWithBoundary.{u}) (F : List S.scheme.IdealSheafData), S.IsAdmissible →
      MarkedIdealWithBoundary.SameNontrivialBoundary S.boundary F → (S.withBoundary F).IsAdmissible)
    (T : MarkedIdealWithBoundary.{u}) (E' : List T.scheme.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary T.boundary E')
    (hV : (T.withBoundary E').IsAdmissible) : T.IsAdmissible := by
  have hBE' : MarkedIdealWithBoundary.SameNontrivialBoundary (T.withBoundary E').boundary T.boundary := hBE.symm
  have h := hvbr (T.withBoundary E') T.boundary hV hBE'
  have he : (T.withBoundary E').withBoundary T.boundary = T := MarkedIdealWithBoundary.withBoundary_self T
  rwa [he] at h

section
variable (S : MarkedIdealWithBoundary.{u})

private theorem containedComponentsIdeal_withBoundary_of_get_eq_consolidated403 (E' : List S.scheme.IdealSheafData) (j : ℕ) (hjE : j < E'.length)
    (hj : j < S.boundary.length)
    (hget : E'.get ⟨j, hjE⟩ = S.boundary.get ⟨j, hj⟩) :
    DivisorReduction.containedComponentsIdeal (S.withBoundary E') j hjE = DivisorReduction.containedComponentsIdeal S j hj := by
  rw [DivisorReduction.containedComponentsIdeal_eq_componentsInOrderLocusIdeal (S.withBoundary E') j hjE,
    DivisorReduction.containedComponentsIdeal_eq_componentsInOrderLocusIdeal S j hj]
  exact congrArg (fun D => DivisorReduction.componentsInOrderLocusIdeal S.ideal S.mult D) hget

private theorem lowerIdealWithoutBlowup_eq_ideal_consolidated403 :
    DivisorReduction.lowerIdealWithoutBlowup S = S.ideal := by
  unfold DivisorReduction.lowerIdealWithoutBlowup
  simp [Scheme.IdealSheafData.comap_id]


end

theorem containedComponentsIdeal_withBoundary_baseChange
    {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}} {hno : BlowupPreservesNoetherian.{u}}
    (hfacts : DivisorReductionTerminationProperties hres hno)
    (hvbr : ∀ (S : MarkedIdealWithBoundary.{u}) (F : List S.scheme.IdealSheafData), S.IsAdmissible →
      MarkedIdealWithBoundary.SameNontrivialBoundary S.boundary F → (S.withBoundary F).IsAdmissible) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
        (E' : List (T.baseChange K f).scheme.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E' →
        ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
          List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary →
          ((T.baseChange K f).withBoundary E').IsAdmissible →
            DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
              (DivisorReduction.containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f) := by
  intro T hV K iK iCZ f E' hBE j hj hjE htake hV'
  have hVb : (T.baseChange K f).IsAdmissible :=
    isAdmissible_of_withBoundary_isAdmissible hvbr (T.baseChange K f) E' hBE hV'
  have hj' : j < (T.baseChange K f).boundary.length := by
    have h := congrArg List.length htake
    rw [List.length_take, List.length_take] at h
    omega
  have hget : E'.get ⟨j, hjE⟩ = (T.baseChange K f).boundary.get ⟨j, hj'⟩ :=
    get_eq_get_of_take_succ_eq E' (T.baseChange K f).boundary j htake hjE hj'
  rw [containedComponentsIdeal_withBoundary_of_get_eq_consolidated403 (T.baseChange K f) E' j hjE hj' hget]
  exact hfacts.preIdeal_baseChange T hV K f hVb j hj hj'

theorem lowerIdealWithoutBlowup_withBoundary_baseChange :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
      (E' : List (T.baseChange K f).scheme.IdealSheafData),
      DivisorReduction.lowerIdealWithoutBlowup ((T.baseChange K f).withBoundary E') =
        (DivisorReduction.lowerIdealWithoutBlowup T).comap (fieldBaseChangeProjection T K f) := by
  intro T K iK iCZ f E'
  rw [lowerIdealWithoutBlowup_eq_ideal_consolidated403, lowerIdealWithoutBlowup_eq_ideal_consolidated403, MarkedIdealWithBoundary.withBoundary_ideal]
  exact MarkedIdealWithBoundary.baseChange_ideal T K f

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorRestrictionFieldBaseChange
section



namespace DivisorReduction

def StrictPullbackFieldBaseChangeOfDimLT (n : ℕ) (L : PrincipalizationAssignment.{u}) : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → T.krullDimSucc < n →
    ∀ (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
      (E' : List (T.baseChange K f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E' →
      ((T.baseChange K f).withBoundary E').IsAdmissible →
      ((T.baseChange K f).withBoundary E').krullDimSucc < n →
      IsStrictPullbackBlowupSeq (fieldBaseChangeProjection T K f)
        (L ((T.baseChange K f).withBoundary E')).toSequenceOfBlowups (L T).toSequenceOfBlowups

def StrictPullbackSmoothSurjectiveOfDimLT (n : ℕ) (L : PrincipalizationAssignment.{u}) : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → T.krullDimSucc < n →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h] [AlgebraicGeometry.Surjective h],
      h ≫ T.structMap = q →
      ∀ (E' : List Y.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
        ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
        ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc < n →
        IsStrictPullbackBlowupSeq h
          (L ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups (L T).toSequenceOfBlowups

section
variable (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O)
include hL

theorem strictPullbackFieldBaseChangeOfDimLT_of_isMaxOrderReduction : StrictPullbackFieldBaseChangeOfDimLT n L :=
  hL.base_change_strict

theorem strictPullbackSmoothSurjectiveOfDimLT_of_isMaxOrderReduction : StrictPullbackSmoothSurjectiveOfDimLT n L :=
  hL.smooth_pullback_strict


end

private theorem toSequenceOfBlowups_heq_of_eq_consolidated407 (L : PrincipalizationAssignment.{u}) {A B : MarkedIdealWithBoundary.{u}} (h : A = B) :
    HEq (L A).toSequenceOfBlowups (L B).toSequenceOfBlowups := by
  subst h; rfl

structure DivisorRestrictionFieldBaseChange : Prop where
  comap_comap :
    ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (I : Z.IdealSheafData),
      (I.comap g).comap f = I.comap (f ≫ g)
  comap_baseChangeFieldProj_ne_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K)
      (I : T.scheme.IdealSheafData), I ≠ ⊤ → I.comap (fieldBaseChangeProjection T K f) ≠ ⊤
  lowerTriple_baseChange_comparison :
    ∀ (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) (K : Type u) [Field K]
      [CharZero K] (f : T.base →+* K) (E' : List (T.baseChange K f).scheme.IdealSheafData)
      (hjE : j < E'.length)
      (hD : E'.get ⟨j, hjE⟩ = (T.boundary.get ⟨j, hj⟩).comap (fieldBaseChangeProjection T K f))
      (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
      (I₀' : (T.baseChange K f).scheme.IdealSheafData)
      (E₀' : List (T.baseChange K f).scheme.IdealSheafData)
      (_hI : I₀' = I₀.comap (fieldBaseChangeProjection T K f))
      (_hE : MarkedIdealWithBoundary.SameNontrivialBoundary
        (List.take (E'.length - 1) (E₀'.eraseIdx j))
        (List.map (fun D => D.comap (fieldBaseChangeProjection T K f))
          (List.take (T.boundary.length - 1) (E₀.eraseIdx j)))),
      ∃ (E'' : List ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).scheme.IdealSheafData)
        (e : (E'.get ⟨j, hjE⟩).subscheme ⟶ ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).scheme)
        (_ : Smooth e) (_ : AlgebraicGeometry.Surjective e),
        MarkedIdealWithBoundary.SameNontrivialBoundary ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).boundary E'' ∧
        e ≫ fieldBaseChangeProjection (restrictToBoundaryDivisor T j hj I₀ E₀) K f =
          divisorPullbackMap T j hj I₀ E₀ (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
            (E'.get ⟨j, hjE⟩) hD ∧
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
                (List.take (E'.length - 1) (E₀'.eraseIdx j)))).krullDimSucc
  lowerIdealTop_baseChange :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
      (E' : List (T.baseChange K f).scheme.IdealSheafData),
      lowerIdealWithoutBlowup ((T.baseChange K f).withBoundary E') =
        (lowerIdealWithoutBlowup T).comap (fieldBaseChangeProjection T K f)
  restrictedBoundaryEmptyCenter_baseChange :
    ∀ (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (_hj : j < T.boundary.length) (K : Type u) [Field K]
      [CharZero K] (f : T.base →+* K) (E' : List (T.baseChange K f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E' →
      List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary →
      j < E'.length →
      MarkedIdealWithBoundary.SameNontrivialBoundary
        (List.take (E'.length - 1)
          ((lowerBoundaryWithoutBlowup ((T.baseChange K f).withBoundary E')).eraseIdx j))
        (List.map (fun D => D.comap (fieldBaseChangeProjection T K f))
          (List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j)))
  lowerIdealPre_baseChange :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → T.IsOrderBoundedByMult →
      ∀ (j : ℕ) (hj : j < T.boundary.length) (K : Type u) [Field K] [CharZero K]
        (f : T.base →+* K) (E' : List (T.baseChange K f).scheme.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E' →
        ∀ (hjE : j < E'.length),
          List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary →
          ((T.baseChange K f).withBoundary E').IsAdmissible →
          containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
            (containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f) →
          lowerIdealAfterBlowup ((T.baseChange K f).withBoundary E') j hjE =
            (lowerIdealAfterBlowup T j hj).comap (fieldBaseChangeProjection T K f)
  restrictedBoundary_baseChange :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → T.IsOrderBoundedByMult →
      ∀ (j : ℕ) (hj : j < T.boundary.length) (K : Type u) [Field K] [CharZero K]
        (f : T.base →+* K) (E' : List (T.baseChange K f).scheme.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E' →
        ∀ (hjE : j < E'.length),
          List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary →
          ((T.baseChange K f).withBoundary E').IsAdmissible →
          containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
            (containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f) →
          MarkedIdealWithBoundary.SameNontrivialBoundary
            (List.take (E'.length - 1)
              ((lowerBoundaryAfterBlowup ((T.baseChange K f).withBoundary E') j hjE).eraseIdx j))
            (List.map (fun D => D.comap (fieldBaseChangeProjection T K f))
              (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j)))

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) (hflf : DivisorRestrictionFieldBaseChange.{u}) (n : ℕ) (L : PrincipalizationAssignment.{u}) (hfe : StrictPullbackFieldBaseChangeOfDimLT n L) (hsm : StrictPullbackSmoothSurjectiveOfDimLT n L) (j : ℕ)
include hfacts hflf hfe hsm

private theorem restrictToBoundaryDivisor_isStrictPullbackBlowupSeq_baseChange_consolidated407 (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    (hj : j < T.boundary.length) (hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty)
    (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hdim' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n)
    (hjE : j < E'.length)
    (hcs' : (orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal T.mult).Nonempty)
    (hD : E'.get ⟨j, hjE⟩ = (T.boundary.get ⟨j, hj⟩).comap (fieldBaseChangeProjection T K f))
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (I₀' : (T.baseChange K f).scheme.IdealSheafData)
    (E₀' : List (T.baseChange K f).scheme.IdealSheafData)
    (hI : I₀' = I₀.comap (fieldBaseChangeProjection T K f))
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (List.take (E'.length - 1) (E₀'.eraseIdx j))
      (List.map (fun D => D.comap (fieldBaseChangeProjection T K f))
        (List.take (T.boundary.length - 1) (E₀.eraseIdx j))))
    (hvT : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible)
    (hvS : (restrictToBoundaryDivisor ((T.baseChange K f).withBoundary E') j hjE I₀' E₀').IsAdmissible) :
    IsStrictPullbackBlowupSeq
      (divisorPullbackMap T j hj I₀ E₀ (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
        (E'.get ⟨j, hjE⟩) hD)
      (L (restrictToBoundaryDivisor ((T.baseChange K f).withBoundary E') j hjE I₀' E₀')).toSequenceOfBlowups
      (L (restrictToBoundaryDivisor T j hj I₀ E₀)).toSequenceOfBlowups := by
  obtain ⟨E'', e, hsme, hsue, ha, hb, hc, hdbe, heV, hfd⟩ :=
    hflf.lowerTriple_baseChange_comparison T j hj K f E' hjE hD I₀ E₀ I₀' E₀' hI hE
  have hMV : (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').IsAdmissible := heV hvS
  have hMd : (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').krullDimSucc < n := by
    rw [hfd]
    exact lt_of_lt_of_le
      (hfacts.lowerTriple_dim_lt ((T.baseChange K f).withBoundary E') hV' hcs' j hjE I₀' E₀')
      hdim'
  have hdimT : (restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < n :=
    lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcs j hj I₀ E₀) hdim
  have h1 := hfe (restrictToBoundaryDivisor T j hj I₀ E₀) hvT hdimT K f E'' ha hMV hMd
  have hsq : divisorPullbackMap T j hj I₀ E₀ (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
        (E'.get ⟨j, hjE⟩) hD ≫ (T.boundary.get ⟨j, hj⟩).subschemeι
      = (E'.get ⟨j, hjE⟩).subschemeι ≫ fieldBaseChangeProjection T K f :=
    subschemeMapOfComap_comp (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hD
  have hid : (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').ideal.comap e
      = I₀'.comap (E'.get ⟨j, hjE⟩).subschemeι := by
    have k1 := hflf.comap_comap _ _ _ e
      (fieldBaseChangeProjection (restrictToBoundaryDivisor T j hj I₀ E₀) K f)
      (I₀.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
    have k2 := congrArg
      (fun (φ : (E'.get ⟨j, hjE⟩).subscheme ⟶ (restrictToBoundaryDivisor T j hj I₀ E₀).scheme) =>
        (I₀.comap (T.boundary.get ⟨j, hj⟩).subschemeι).comap φ) hb
    have k3 := hflf.comap_comap _ _ _
      (divisorPullbackMap T j hj I₀ E₀ (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
        (E'.get ⟨j, hjE⟩) hD)
      (T.boundary.get ⟨j, hj⟩).subschemeι I₀
    have k4 := congrArg
      (fun (φ : (E'.get ⟨j, hjE⟩).subscheme ⟶ T.scheme) => I₀.comap φ) hsq
    have k5 := hflf.comap_comap _ _ _ (E'.get ⟨j, hjE⟩).subschemeι
      (fieldBaseChangeProjection T K f) I₀
    have k6 := congrArg
      (fun (I : (T.baseChange K f).scheme.IdealSheafData) =>
        I.comap (E'.get ⟨j, hjE⟩).subschemeι) hI
    exact k1.trans (k2.trans (k3.trans (k4.trans (k5.symm.trans k6.symm))))
  have htriple : ((((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').pullbackAlong
        (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) e).withBoundary
        (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j)))
      = restrictToBoundaryDivisor ((T.baseChange K f).withBoundary E') j hjE I₀' E₀' :=
    congrArg (fun I => (T.baseChange K f).withSchemeIdealBoundary (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) I
        (List.map (fun (D : (T.baseChange K f).scheme.IdealSheafData) =>
            D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j)))) hid
  have hbe : MarkedIdealWithBoundary.SameNontrivialBoundary
      ((((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').pullbackAlong
        (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) e).boundary
      (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
        (List.take (E'.length - 1) (E₀'.eraseIdx j))) := hdbe.symm
  have hva : (((((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').pullbackAlong
        (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) e).withBoundary
        (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j)))).IsAdmissible := by
    rw [htriple]; exact hvS
  have hdd : (((((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').pullbackAlong
        (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) e).withBoundary
        (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j)))).krullDimSucc < n := by
    rw [htriple]
    exact lt_of_lt_of_le
      (hfacts.lowerTriple_dim_lt ((T.baseChange K f).withBoundary E') hV' hcs' j hjE I₀' E₀')
      hdim'
  have h2 := @hsm (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'') hMV hMd
      (E'.get ⟨j, hjE⟩).subscheme
      ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) e hsme hsue hc
      (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
        (List.take (E'.length - 1) (E₀'.eraseIdx j))) hbe hva hdd
  have h4 : IsStrictPullbackBlowupSeq
      (divisorPullbackMap T j hj I₀ E₀ (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
        (E'.get ⟨j, hjE⟩) hD)
      (L (((((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').pullbackAlong
          (E'.get ⟨j, hjE⟩).subscheme
          ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) e).withBoundary
          (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
            (List.take (E'.length - 1) (E₀'.eraseIdx j))))).toSequenceOfBlowups
      (L (restrictToBoundaryDivisor T j hj I₀ E₀)).toSequenceOfBlowups := by
    rw [← hb]
    exact h2.comp h1
  have hLe : (L (((((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').pullbackAlong
        (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) e).withBoundary
        (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j))))).toSequenceOfBlowups
      = (L (restrictToBoundaryDivisor ((T.baseChange K f).withBoundary E') j hjE I₀' E₀')).toSequenceOfBlowups :=
    eq_of_heq (toSequenceOfBlowups_heq_of_eq_consolidated407 L htriple)
  exact (congrArg (fun t : SequenceOfBlowups (E'.get ⟨j, hjE⟩).subscheme =>
      IsStrictPullbackBlowupSeq
        (divisorPullbackMap T j hj I₀ E₀ (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
          (E'.get ⟨j, hjE⟩) hD) t (L (restrictToBoundaryDivisor T j hj I₀ E₀)).toSequenceOfBlowups) hLe).mp h4

theorem restrictedFieldBaseChange_of_strictPullback :
    RestrictedPrincipalizationFieldBaseChange n L j := by
  constructor
  · intro T hV hdim hO hbal hj hcs K instK instC f E' hBE htake hV' hdim' hO' hDB' hjE hcs'
      hZ hZ'
    exact restrictToBoundaryDivisor_isStrictPullbackBlowupSeq_baseChange_consolidated407 hres hfacts hflf n L hfe hsm j T hV hdim hj hcs K f E' hV' hdim'
      hjE hcs' (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake)
      (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T)
      (lowerIdealWithoutBlowup ((T.baseChange K f).withBoundary E'))
      (lowerBoundaryWithoutBlowup ((T.baseChange K f).withBoundary E'))
      (hflf.lowerIdealTop_baseChange T K f E')
      (hflf.restrictedBoundaryEmptyCenter_baseChange T j hj K f E' hBE htake hjE)
      (hfacts.valid_lowerTop T hV hO hbal j hj hZ)
      (hfacts.valid_lowerTop ((T.baseChange K f).withBoundary E') hV' hO' hDB' j hjE hZ')
  · intro T hV hdim hO hbal hj hcs K instK instC f E' hBE htake hV' hdim' hO' hDB' hjE hcs'
      hZ hZ'
    have hZ2 : containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE ≠ ⊤ := by
      rw [hZ']
      exact hflf.comap_baseChangeFieldProj_ne_top T K f (containedComponentsIdeal T j hj) hZ
    exact restrictToBoundaryDivisor_isStrictPullbackBlowupSeq_baseChange_consolidated407 hres hfacts hflf n L hfe hsm j T hV hdim hj hcs K f E' hV' hdim'
      hjE hcs' (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake)
      (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
      (lowerIdealAfterBlowup ((T.baseChange K f).withBoundary E') j hjE)
      (lowerBoundaryAfterBlowup ((T.baseChange K f).withBoundary E') j hjE)
      (hflf.lowerIdealPre_baseChange T hV hO j hj K f E' hBE hjE htake hV' hZ')
      (hflf.restrictedBoundary_baseChange T hV hO j hj K f E' hBE hjE htake hV' hZ')
      (hfacts.valid_lowerPre T hV hO hbal j hj hZ)
      (hfacts.valid_lowerPre ((T.baseChange K f).withBoundary E') hV' hO' hDB' j hjE hZ2)


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (hfbc : FieldBaseChangeCompatibility.{u}) (hflf : DivisorRestrictionFieldBaseChange.{u}) (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ) (hshape : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length), T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType → orderAtLeastLocus T.ideal T.mult ≠ ∅ → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult) (hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K) (E' : List (T.baseChange K f).scheme.IdealSheafData) (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E') (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary) (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible) (hdim' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n) (hO' : ((T.baseChange K f).withBoundary E').IsOrderBoundedByMult) (hDB' : ((T.baseChange K f).withBoundary E').IsBalanced hV'.locallyOfFiniteType) (hjE : j < E'.length)
include hfacts hbc hfbc hflf hL hshape hdim hO hbal hBE htake hdim' hO' hDB' hjE hj

theorem divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange_of_isMaxOrderReduction
    :
    IsStrictPullbackBlowupSeq (fieldBaseChangeProjection T K f)
      (((canonicalAlgorithmRules hres).divisorFamily L j ((T.baseChange K f).withBoundary E')).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) :=
  divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange hres hfacts hbc hfbc n L j
    (restrictedFieldBaseChange_of_strictPullback hres hfacts hflf n L
      (strictPullbackFieldBaseChangeOfDimLT_of_isMaxOrderReduction n L O hL)
      (strictPullbackSmoothSurjectiveOfDimLT_of_isMaxOrderReduction n L O hL) j)
    hshape T hV hdim hO hbal hj K f E' hBE htake hV' hdim' hO' hDB' hjE

theorem divisorFamily_isPullbackBlowupSequence_fieldBaseChange_of_isMaxOrderReduction
    :
    IsPullbackBlowupSequence (fieldBaseChangeProjection T K f)
      (((canonicalAlgorithmRules hres).divisorFamily L j ((T.baseChange K f).withBoundary E')).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) :=
  divisorFamily_isPullbackSequenceOfBlowups_fieldBaseChange hres hfacts hbc hfbc n L j
    (restrictedFieldBaseChange_of_strictPullback hres hfacts hflf n L
      (strictPullbackFieldBaseChangeOfDimLT_of_isMaxOrderReduction n L O hL)
      (strictPullbackSmoothSurjectiveOfDimLT_of_isMaxOrderReduction n L O hL) j)
    hshape
    (fun S hS hdS hboundS hDS hjS i hi =>
      divisorFamily_canonicalAlgorithmRules_center_nonempty hres hfacts n L O hL j S hS hdS hboundS hDS hjS i hi)
    (fun _Y s hs => SequenceOfBlowups.withoutIsoBlowups_isomorphic_self s hs)
    T hV hdim hO hbal hj K f E' hBE htake hV' hdim' hO' hDB' hjE


end

end DivisorReduction

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryFieldBaseChange
section



namespace DivisorReduction

private theorem sameNontrivialBoundary_take_eraseIdx_comap_consolidated404 {X Y : Scheme.{u}} (p : Y ⟶ X)
    (B : List X.IdealSheafData) (E' : List Y.IdealSheafData) (j : ℕ)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap p) B) E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (List.map (fun D => D.comap p) B))
    (hj : j < B.length) (hjE : j < E'.length) :
    MarkedIdealWithBoundary.SameNontrivialBoundary (List.take (E'.length - 1) (E'.eraseIdx j))
      (List.map (fun D => D.comap p) (List.take (B.length - 1) (B.eraseIdx j))) := by
  have hE : List.take (E'.length - 1) (E'.eraseIdx j) = E'.eraseIdx j :=
    List.take_of_length_le (le_of_eq (List.length_eraseIdx_of_lt hjE))
  have hB : List.take (B.length - 1) (B.eraseIdx j) = B.eraseIdx j :=
    List.take_of_length_le (le_of_eq (List.length_eraseIdx_of_lt hj))
  rw [hE, hB, ← List.eraseIdx_map]
  exact hBE.symm.eraseIdx j htake

private theorem isClosed_setOf_connectedComponent_subset_consolidated404 {X : Type u} [TopologicalSpace X]
    (hop : ∀ x : X, IsOpen (connectedComponent x)) (P : Set X) :
    IsClosed {x : X | connectedComponent x ⊆ P} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨connectedComponent x, ?_, hop x, mem_connectedComponent⟩
  intro y hy
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hx ⊢
  intro hsub
  apply hx
  rw [connectedComponent_eq hy]
  exact hsub

section
variable (T : MarkedIdealWithBoundary.{u})

theorem lowerBoundaryWithoutBlowup_baseChange_sameNontrivialBoundary (j : ℕ)
    (hj : j < T.boundary.length) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
    (hjE : j < E'.length) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (E'.length - 1)
        ((lowerBoundaryWithoutBlowup ((T.baseChange K f).withBoundary E')).eraseIdx j))
      (List.map (fun D => D.comap (fieldBaseChangeProjection T K f))
        (List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j))) := by
  rw [lowerBoundaryWithoutBlowup_eq ((T.baseChange K f).withBoundary E'), lowerBoundaryWithoutBlowup_eq T]
  exact sameNontrivialBoundary_take_eraseIdx_comap_consolidated404 (fieldBaseChangeProjection T K f) T.boundary E' j hBE htake hj hjE

theorem preimageSupportEqComponentsInOrderLocus_of_isAdmissible (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) : PreimageSupportEqComponentsInOrderLocus T j hj := by
  intro h
  have := hV.isNoetherian
  have := FunctorialResolution.Blowup.noetherianSpace_subscheme (T.boundary.get ⟨j, hj⟩)
  have hnsU : TopologicalSpace.NoetherianSpace
      ↥((boundaryComponentsInOrderLocusOpens T j hj h).toScheme) :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace ↥(boundaryComponentsInOrderLocus T j hj))
  have hqc : QuasiCompact
      ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) := by
    constructor
    intro V _ _
    exact TopologicalSpace.NoetherianSpace.isCompact _
  have hclosed : IsClosed (boundaryComponentsInOrderLocus T j hj) :=
    isClosed_setOf_connectedComponent_subset_consolidated404
      (fun x => Blowup.isOpen_connectedComponent_of_noetherianSpace _ x) _
  have hinj : Function.Injective ⇑(T.boundary.get ⟨j, hj⟩).subschemeι :=
    (Scheme.Hom.isClosedEmbedding (T.boundary.get ⟨j, hj⟩).subschemeι).injective
  have himg : IsClosed (⇑(T.boundary.get ⟨j, hj⟩).subschemeι '' boundaryComponentsInOrderLocus T j hj) :=
    (Scheme.Hom.isClosedEmbedding (T.boundary.get ⟨j, hj⟩).subschemeι).isClosedMap _ hclosed
  have hU : Set.range ⇑(boundaryComponentsInOrderLocusOpens T j hj h).ι = boundaryComponentsInOrderLocus T j hj :=
    Scheme.Opens.range_ι _
  have hcomp : ⇑((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)
      = ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ∘ ⇑(boundaryComponentsInOrderLocusOpens T j hj h).ι := by
    funext x
    simp
  have hrange :
      Set.range ⇑((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)
        = ⇑(T.boundary.get ⟨j, hj⟩).subschemeι '' boundaryComponentsInOrderLocus T j hj := by
    rw [hcomp, Set.range_comp, hU]
  have hsupp : ((AlgebraicGeometry.Scheme.Hom.ker
        ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫
          (T.boundary.get ⟨j, hj⟩).subschemeι)).support : Set ↥T.scheme)
      = closure (Set.range
          ⇑((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)) := by
    rw [AlgebraicGeometry.Scheme.Hom.support_ker]
  rw [hsupp, hrange, himg.closure_eq]
  exact Set.preimage_image_eq _ hinj


end

end DivisorReduction

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerDimensionSmoothPullback
section



def PullbackSmoothOfDimLT (n : ℕ) (L : PrincipalizationAssignment.{u}) : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → T.krullDimSucc < n →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
      ∀ (E' : List Y.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
        ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
        ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc < n →
        IsPullbackBlowupSequence h (L ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
          (L T).toSequenceOfBlowups

theorem pullbackSmoothOfDimLT_of_isMaxOrderReduction (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) : PullbackSmoothOfDimLT n L := by
  intro T hV hdim Y q h hsm hq E' hBE hV' hdim'
  have := hsm
  exact hL.smooth_pullback T hV hdim Y q h hq E' hBE hV' hdim'

theorem isPullbackSequenceOfBlowups_of_length_eq_zero (X X' : Scheme.{u}) (φ : X' ⟶ X) (B' : SequenceOfBlowups X')
    (B : SequenceOfBlowups X) (hB' : B'.length = 0) (hB : B.length = 0) : IsPullbackBlowupSequence φ B' B := by
  unfold IsPullbackBlowupSequence
  refine ⟨fun _ => 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    cases i with
    | zero => exact B'.isoZero ≪≫ (asIso (Limits.pullback.fst φ (B.projectionToBase 0))).symm
    | succ k => exact absurd hi (by rw [hB']; exact Nat.not_succ_le_zero k)
  · intro i hi
    rw [hB'] at hi
    exact absurd hi (Nat.not_lt_zero i)
  · intro i k hk hik
    rw [hB'] at hk
    exact absurd hik (by omega)
  · exact hB.symm
  · intro i hi
    rw [hB] at hi
    exact absurd hi (Nat.not_lt_zero i)
  · rintro (_ | k) hi
    · show (B'.isoZero ≪≫ (asIso (Limits.pullback.fst φ (B.projectionToBase 0))).symm).hom ≫
          Limits.pullback.fst φ (B.projectionToBase 0) = B'.projectionToBase 0
      simp [SequenceOfBlowups.projectionToBase_zero]
    · exact absurd hi (by rw [hB']; exact Nat.not_succ_le_zero k)
  · intro i hi _
    exact absurd hi (by rw [hB']; exact Nat.not_lt_zero i)
  · intro i hi
    exact absurd hi (by rw [hB']; exact Nat.not_lt_zero i)

section
variable {X : Scheme.{u}} (s : SequenceOfBlowups X)

private theorem forall_ofSequenceOfBlowups_transitionMap_eq_consolidated402 :
    ∀ (j i : ℕ) (h : i ≤ j), (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap h = s.transitionMap h := by
  intro j
  induction j with
  | zero =>
    intro i h
    have hi : i = 0 := Nat.le_zero.mp h
    subst hi
    exact (SequenceOfBlowups.transitionMap_self _ h).trans (SequenceOfBlowups.transitionMap_self s h).symm
  | succ k ih =>
    intro i h
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · subst heq
      exact (SequenceOfBlowups.transitionMap_self _ h).trans (SequenceOfBlowups.transitionMap_self s h).symm
    · have hik : i ≤ k := Nat.lt_succ_iff.mp hlt
      have hb : (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap (Nat.le_succ k) = s.transitionMap (Nat.le_succ k) := by
        have e1 : (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMapSucc k = s.transitionMapSucc k :=
          (BlowupSequenceData.toSequenceOfBlowups_blowupMorphism (BlowupSequenceData.ofSequenceOfBlowups s) k).trans (BlowupSequenceData.ofSequenceOfBlowups_blowupMorphism s k)
        exact ((SequenceOfBlowups.blowupMorphism_eq_transitionMap _ k).symm.trans e1).trans
          (SequenceOfBlowups.blowupMorphism_eq_transitionMap s k)
      have E1 : (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap h
          = (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap (Nat.le_succ k) ≫
            (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap hik :=
        (SequenceOfBlowups.transitionMap_trans _ hik (Nat.le_succ k)).symm
      have E2 : s.transitionMap h = s.transitionMap (Nat.le_succ k) ≫ s.transitionMap hik :=
        (SequenceOfBlowups.transitionMap_trans s hik (Nat.le_succ k)).symm
      have c1 := congrArg (fun g => g ≫ (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap hik) hb
      have c2 := congrArg (fun g => s.transitionMap (Nat.le_succ k) ≫ g) (ih i hik)
      exact E1.trans ((c1.trans c2).trans E2.symm)

private theorem ofSequenceOfBlowups_transitionMap_consolidated402 {i j : ℕ} (h : i ≤ j) :
    (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap h = s.transitionMap h :=
  forall_ofSequenceOfBlowups_transitionMap_eq_consolidated402 s j i h

private theorem ofSequenceOfBlowups_tower_consolidated402 :
    (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.tower = s.tower := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro a b f
  have hf : (homOfLE (leOfHom f.unop)).op = f :=
    congrArg (fun g => Quiver.Hom.op g) (homOfLE_leOfHom f.unop)
  have h1 : (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.tower.map f
      = (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap (leOfHom f.unop) := by
    rw [SequenceOfBlowups.transitionMap_def, hf]
  have h2 : s.tower.map f = s.transitionMap (leOfHom f.unop) := by
    rw [SequenceOfBlowups.transitionMap_def, hf]
  have key : (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.tower.map f = s.tower.map f :=
    h1.trans ((ofSequenceOfBlowups_transitionMap_consolidated402 s (leOfHom f.unop)).trans h2.symm)
  have hid : s.tower.map f
      = 𝟙 (s.tower.obj a) ≫ s.tower.map f ≫ 𝟙 (s.tower.obj b) := by
    simp
  exact key.trans hid


end

section
variable {X : Scheme.{u}}

private theorem sequenceOfBlowups_eq_of_tower_eq_consolidated402 (s t : SequenceOfBlowups X)
    (ht : s.tower = t.tower) (hl : s.length = t.length)
    (hiso : HEq s.isoZero t.isoZero) (hc : HEq s.center t.center) : s = t := by
  obtain ⟨l₁, F, i₁, c₁, b₁⟩ := s
  obtain ⟨l₂, G, i₂, c₂, b₂⟩ := t
  have hl' : l₁ = l₂ := hl
  have ht' : F = G := ht
  subst hl'
  subst ht'
  have hiso' : HEq i₁ i₂ := hiso
  have hc' : HEq c₁ c₂ := hc
  obtain rfl := eq_of_heq hiso'
  obtain rfl := eq_of_heq hc'
  rfl

private theorem ofSequenceOfBlowups_toSequenceOfBlowups_consolidated402 (s : SequenceOfBlowups X) :
    (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups = s :=
  sequenceOfBlowups_eq_of_tower_eq_consolidated402 _ _ (ofSequenceOfBlowups_tower_consolidated402 s) rfl (HEq.refl _) (HEq.refl _)


end

theorem isPullbackBlowupSequence_ofMarkedSequence (A B : MarkedIdealWithBoundary.{u})
    (φ : A.scheme ⟶ B.scheme) (sA : A.SequenceOfBlowups) (sB : B.SequenceOfBlowups)
    (hs : IsPullbackBlowupSequence φ sA.toSequenceOfBlowups sB.toSequenceOfBlowups) :
    IsPullbackBlowupSequence φ (MarkedBlowupSequenceData.ofMarkedSequence sA).toBlowupSequenceData.toSequenceOfBlowups
      (MarkedBlowupSequenceData.ofMarkedSequence sB).toBlowupSequenceData.toSequenceOfBlowups := by
  have hA : (MarkedBlowupSequenceData.ofMarkedSequence sA).toBlowupSequenceData.toSequenceOfBlowups = sA.toSequenceOfBlowups :=
    ofSequenceOfBlowups_toSequenceOfBlowups_consolidated402 _
  have hB : (MarkedBlowupSequenceData.ofMarkedSequence sB).toBlowupSequenceData.toSequenceOfBlowups = sB.toSequenceOfBlowups :=
    ofSequenceOfBlowups_toSequenceOfBlowups_consolidated402 _
  rw [hA, hB]
  exact hs

private theorem markedIdealWithBoundary_mk_ideal_congr_consolidated402 {k : Type u} [inst : Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ} {E : List X.IdealSheafData}
    {I₁ I₂ : X.IdealSheafData} (hI : I₁ = I₂) :
    (@MarkedIdealWithBoundary.mk k inst X p I₁ m E) = (@MarkedIdealWithBoundary.mk k inst X p I₂ m E) := by
  rw [hI]

private theorem isPullbackSequenceOfBlowups_apply_congr_consolidated402 (L : PrincipalizationAssignment.{u})
    {X : Scheme.{u}} (B : SequenceOfBlowups X) (S S' : MarkedIdealWithBoundary.{u}) (hS : S = S')
    (φ : S.scheme ⟶ X) (φ' : S'.scheme ⟶ X) (hφ : HEq φ φ')
    (hpb : IsPullbackBlowupSequence φ (L S).toSequenceOfBlowups B) :
    IsPullbackBlowupSequence φ' (L S').toSequenceOfBlowups B := by
  subst hS
  have hee : φ = φ' := eq_of_heq hφ
  subst hee
  exact hpb

private theorem isPullbackBlowupSequence_restrictToBoundaryDivisor_consolidated402 (n : ℕ) (L : PrincipalizationAssignment.{u})
    (hL : PullbackSmoothOfDimLT n L) (hbc : DivisorReduction.SmoothPullbackCompatibility.{u})
    (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    (hsm : Smooth h) (hq : h ≫ T.structMap = q)
    (E' : List Y.IdealSheafData) (hjE : j < E'.length)
    (hD : E'.get ⟨j, hjE⟩ = (T.boundary.get ⟨j, hj⟩).comap h)
    (I₀' : Y.IdealSheafData) (E₀' : List Y.IdealSheafData)
    (hI : I₀' = I₀.comap h)
    (hEq : MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (E'.length - 1) (E₀'.eraseIdx j))
      (List.map (fun D => D.comap h)
        (List.take (T.boundary.length - 1) (E₀.eraseIdx j))))
    (hadmissible : (DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible)
    (hdS : (DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < n)
    (hVS' : (DivisorReduction.restrictToBoundaryDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE
      I₀' E₀').IsAdmissible)
    (hdS' : (DivisorReduction.restrictToBoundaryDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE
      I₀' E₀').krullDimSucc < n) :
    IsPullbackBlowupSequence (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD)
      (L (DivisorReduction.restrictToBoundaryDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE
        I₀' E₀')).toSequenceOfBlowups
      (L (DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀)).toSequenceOfBlowups := by
  have := hsm
  have hsm0 : Smooth
      (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD) :=
    hbc.smooth_of_isPullback T.scheme Y (T.boundary.get ⟨j, hj⟩).subscheme
      (E'.get ⟨j, hjE⟩).subscheme (T.boundary.get ⟨j, hj⟩).subschemeι
      (E'.get ⟨j, hjE⟩).subschemeι h
      (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD)
      ((hbc.isPullback_inducedHom T.scheme Y h (T.boundary.get ⟨j, hj⟩)
        (E'.get ⟨j, hjE⟩) hD).flip) hsm
  have hic : (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD) ≫
      (T.boundary.get ⟨j, hj⟩).subschemeι = (E'.get ⟨j, hjE⟩).subschemeι ≫ h :=
    DivisorReduction.subschemeMapOfComap_comp h (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hD
  have a1 : (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD) ≫
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
      = ((DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD) ≫
        (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap :=
    (Category.assoc _ _ _).symm
  have a2 : ((DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD) ≫
      (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap
      = ((E'.get ⟨j, hjE⟩).subschemeι ≫ h) ≫ T.structMap :=
    congrArg (fun g => g ≫ T.structMap) hic
  have a3 : ((E'.get ⟨j, hjE⟩).subschemeι ≫ h) ≫ T.structMap
      = (E'.get ⟨j, hjE⟩).subschemeι ≫ (h ≫ T.structMap) := Category.assoc _ _ _
  have a4 : (E'.get ⟨j, hjE⟩).subschemeι ≫ (h ≫ T.structMap)
      = (E'.get ⟨j, hjE⟩).subschemeι ≫ q :=
    congrArg (fun g => (E'.get ⟨j, hjE⟩).subschemeι ≫ g) hq
  have hq₀ : (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD) ≫
      (DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).structMap
      = (E'.get ⟨j, hjE⟩).subschemeι ≫ q :=
    a1.trans (a2.trans (a3.trans a4))
  have hIdeal : ((DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).ideal).comap
      (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD)
      = I₀'.comap (E'.get ⟨j, hjE⟩).subschemeι := by
    rw [hI]
    exact DivisorReduction.comap_subschemeMapOfComap h (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hD I₀
  have heq : (((DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).pullbackAlong
        (E'.get ⟨j, hjE⟩).subscheme ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD)).withBoundary
        (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j))))
      = DivisorReduction.restrictToBoundaryDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE I₀' E₀' :=
    markedIdealWithBoundary_mk_ideal_congr_consolidated402 hIdeal
  have hBE₀ : MarkedIdealWithBoundary.SameNontrivialBoundary
      (((DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).pullbackAlong
        (E'.get ⟨j, hjE⟩).subscheme ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD)).boundary)
      (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
        (List.take (E'.length - 1) (E₀'.eraseIdx j))) :=
    (DivisorReduction.sameNontrivialBoundary_comap_subschemeι h (T.boundary.get ⟨j, hj⟩)
      (E'.get ⟨j, hjE⟩) hD (List.take (T.boundary.length - 1) (E₀.eraseIdx j))
      (List.take (E'.length - 1) (E₀'.eraseIdx j)) hEq).symm
  have hV₀ : ((((DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).pullbackAlong
        (E'.get ⟨j, hjE⟩).subscheme ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD)).withBoundary
        (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j))))).IsAdmissible := by
    rw [heq]; exact hVS'
  have hd₀ : ((((DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).pullbackAlong
        (E'.get ⟨j, hjE⟩).subscheme ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
        (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD)).withBoundary
        (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j))))).krullDimSucc < n := by
    rw [heq]; exact hdS'
  have hmain := hL (DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀) hadmissible hdS
    (E'.get ⟨j, hjE⟩).subscheme ((E'.get ⟨j, hjE⟩).subschemeι ≫ q)
    (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD) hq₀
    (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
      (List.take (E'.length - 1) (E₀'.eraseIdx j))) hBE₀ hV₀ hd₀
  exact isPullbackSequenceOfBlowups_apply_congr_consolidated402 L
    (L (DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀)).toSequenceOfBlowups _ _ heq _ _
    (HEq.refl (DivisorReduction.divisorPullbackMap T j hj I₀ E₀ Y h (E'.get ⟨j, hjE⟩) hD)) hmain

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (hdt : DivisorReduction.EmptyPulledBackCenterCompatibility.{u}) (n : ℕ)
include hfacts hbc hdt

theorem restrictedSmoothPullback_of_pullbackSmoothOfDimLT
    (L : PrincipalizationAssignment.{u}) (j : ℕ) (hL : PullbackSmoothOfDimLT n L) :
    DivisorReduction.RestrictedPrincipalizationSmoothPullback n L j := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hV hdim hO hbal hj hcs Y q h hsm hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZc
      hZ'
    have := hsm
    have hIc : DivisorReduction.lowerIdealWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E')
        = (DivisorReduction.lowerIdealAfterBlowup T j hj).comap h := by
      rw [DivisorReduction.lowerIdealWithoutBlowup_withBoundary T Y q h E']
      exact (hdt.lowerIdealPre_comap_eq_lowerIdealTop_comap T hV hO j hj Y h hZc).symm
    have hEc : MarkedIdealWithBoundary.SameNontrivialBoundary
        (List.take (E'.length - 1)
          ((DivisorReduction.lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E')).eraseIdx j))
        (List.map (fun D => D.comap h)
          (List.take (T.boundary.length - 1)
            ((DivisorReduction.lowerBoundaryAfterBlowup T j hj).eraseIdx j))) :=
      (DivisorReduction.sameNontrivialBoundary_lowerBoundaryWithoutBlowup T j hj Y q h E' hBE htake hjE).trans
        (hdt.boundaryEquiv_restrictedBoundary_comap_of_center_comap_eq_top T hV j hj Y h hZc).symm
    exact isPullbackBlowupSequence_restrictToBoundaryDivisor_consolidated402 n L hL hbc T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
      (DivisorReduction.lowerBoundaryAfterBlowup T j hj) Y q h hsm hq E' hjE
      (DivisorReduction.get_eq_comap_get_boundary T j hj Y q h E' hjE htake)
      (DivisorReduction.lowerIdealWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))
      (DivisorReduction.lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))
      hIc hEc
      (hfacts.valid_lowerPre T hV hO hbal j hj hZ)
      (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcs j hj
        (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)) hdim)
      (hfacts.valid_lowerTop ((T.pullbackAlong Y q h).withBoundary E') hV' hO' hDB' j hjE hZ')
      (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt ((T.pullbackAlong Y q h).withBoundary E')
        hV' hcs' j hjE
        (DivisorReduction.lowerIdealWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))
        (DivisorReduction.lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))) hdim')
  · intro T hV hdim hO hbal hj hcs Y q h hsm hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'
    have := hsm
    exact isPullbackBlowupSequence_restrictToBoundaryDivisor_consolidated402 n L hL hbc T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
      (DivisorReduction.lowerBoundaryWithoutBlowup T) Y q h hsm hq E' hjE
      (DivisorReduction.get_eq_comap_get_boundary T j hj Y q h E' hjE htake)
      (DivisorReduction.lowerIdealWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))
      (DivisorReduction.lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))
      (DivisorReduction.lowerIdealWithoutBlowup_withBoundary T Y q h E')
      (DivisorReduction.sameNontrivialBoundary_lowerBoundaryWithoutBlowup T j hj Y q h E' hBE htake hjE)
      (hfacts.valid_lowerTop T hV hO hbal j hj hZ)
      (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcs j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)) hdim)
      (hfacts.valid_lowerTop ((T.pullbackAlong Y q h).withBoundary E') hV' hO' hDB' j hjE hZ')
      (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt ((T.pullbackAlong Y q h).withBoundary E')
        hV' hcs' j hjE
        (DivisorReduction.lowerIdealWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))
        (DivisorReduction.lowerBoundaryWithoutBlowup ((T.pullbackAlong Y q h).withBoundary E'))) hdim')
  · intro T hV hdim hO hbal hj hcs Y q h hsm hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZc
      hZ'
    have := hsm
    have hZ'' : DivisorReduction.containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE ≠ ⊤ := by
      rw [hZ']; exact hZc
    exact isPullbackBlowupSequence_restrictToBoundaryDivisor_consolidated402 n L hL hbc T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
      (DivisorReduction.lowerBoundaryAfterBlowup T j hj) Y q h hsm hq E' hjE
      (DivisorReduction.get_eq_comap_get_boundary T j hj Y q h E' hjE htake)
      (DivisorReduction.lowerIdealAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE)
      (DivisorReduction.lowerBoundaryAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE)
      (hbc.lowerIdealPre_comap T hV Y q h hq E' hBE j hj hjE htake hV' hO hZ')
      (hbc.boundaryEquiv_restrictedBoundary_comap T hV Y q h hq E' hBE j hj hjE htake hV' hO hZ')
      (hfacts.valid_lowerPre T hV hO hbal j hj hZ)
      (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcs j hj
        (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)) hdim)
      (hfacts.valid_lowerPre ((T.pullbackAlong Y q h).withBoundary E') hV' hO' hDB' j hjE hZ'')
      (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt ((T.pullbackAlong Y q h).withBoundary E')
        hV' hcs' j hjE
        (DivisorReduction.lowerIdealAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE)
        (DivisorReduction.lowerBoundaryAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE)) hdim')

theorem restrictedSmoothPullback_of_isMaxOrderReduction
    (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ) :
    DivisorReduction.RestrictedPrincipalizationSmoothPullback n L j :=
  restrictedSmoothPullback_of_pullbackSmoothOfDimLT hres hfacts hbc hdt n L j
    (pullbackSmoothOfDimLT_of_isMaxOrderReduction n L O hL)


end

theorem pullbackOfEmptySequence_of_isPullbackSequenceOfBlowups (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (L : PrincipalizationAssignment.{u}) (j : ℕ)
    (hdel : ∀ (T : MarkedIdealWithBoundary.{u}) (_hV : T.IsAdmissible) (_hj : j < T.boundary.length)
      (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [Smooth h],
      h ≫ T.structMap = q →
      ∀ (E' : List Y.IdealSheafData),
        ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
        (orderAtLeastLocus T.ideal T.mult).Nonempty →
        orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult = ∅ →
        ∀ (B' : SequenceOfBlowups Y), B'.length = 0 →
          IsPullbackBlowupSequence h B' (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups)) :
    DivisorReduction.IsPullbackSeqOfEmptyBlowupSeq hres L j :=
  { isPullbackSeq_of_coSupport_empty := hdel
    isPullbackSeq_of_length_eq_zero := fun X X' φ B' B hB' hB =>
      isPullbackSequenceOfBlowups_of_length_eq_zero X X' φ B' B hB' hB
    isPullbackSeq_ofMarkedSeq := fun A B φ sA sB hs =>
      isPullbackBlowupSequence_ofMarkedSequence A B φ sA sB hs }

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.OrderLocusFieldBaseChange
section



theorem orderAtLeastLocus_withBoundary_baseChange_eq_preimage (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (K : Type u) [Field K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData) (m : ℕ) :
    orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal m =
      (fieldBaseChangeProjection T K f) ⁻¹' orderAtLeastLocus T.ideal m := by
  haveI : CharZero T.base := hV.charZero
  haveI : CharZero K := (RingHom.charZero_iff f.injective).mp hV.charZero
  haveI : Smooth T.structMap := hV.smooth
  exact orderAtLeastLocus_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal m

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PrependedAmbientSequence
section


section

private theorem not_natCast_add_one_le_self_consolidated401 (n : ℕ) : ¬ ((n : ℕ∞) + 1 ≤ (n : ℕ∞)) := by
  rw [ENat.add_one_le_iff (ENat.natCast_ne_top n)]
  exact lt_irrefl _

private def iteratedStrictTransform_consolidated401 {X : Scheme.{u}} (d : BlowupSequenceData X)
    (A0 : (d.obj 0).IdealSheafData) (t : ℕ) : (d.obj t).IdealSheafData :=
  Nat.rec (motive := fun n => (d.obj n).IdealSheafData) A0
    (fun n ih => Blowup.strictTransform (d.map n) (d.center n) ih) t

private theorem strictTransformIter_succ_consolidated401 {X : Scheme.{u}} (d : BlowupSequenceData X)
    (A0 : (d.obj 0).IdealSheafData) (t : ℕ) :
    iteratedStrictTransform_consolidated401 d A0 (t + 1) =
      Blowup.strictTransform (d.map t) (d.center t) (iteratedStrictTransform_consolidated401 d A0 t) := rfl

section
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (S : MarkedSequenceOfBlowups p I m E)

private theorem length_le_length_boundary_consolidated401 (n : ℕ) :
    n ≤ S.length → E.length ≤ (S.boundary n).length := by
  induction n with
  | zero =>
    intro _
    simp [S.boundary_zero]
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 : (S.boundary (n + 1)).length = (S.boundary n).length + 1 := by
      rw [S.boundary_succ n (by omega)]
      simp
    omega

private theorem boundary_zero_get_eq_comap_consolidated401 (j : ℕ) (hj : j < E.length)
    (h : j < (S.boundary 0).length) :
    (S.boundary 0).get ⟨j, h⟩ = (E.get ⟨j, hj⟩).comap S.isoZero.hom := by
  have hb := S.boundary_zero
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_of_eq hb h, List.getElem_map]

private theorem boundary_succ_get_eq_strictTransform_consolidated401 (j n : ℕ) (hn : n < S.length)
    (hjn : j < (S.boundary n).length) (h : j < (S.boundary (n + 1)).length) :
    (S.boundary (n + 1)).get ⟨j, h⟩ =
      Blowup.strictTransform (S.transitionMapSucc n) (S.center n) ((S.boundary n).get ⟨j, hjn⟩) := by
  have hb := S.boundary_succ n hn
  have hlen : j < (List.map (Blowup.strictTransform (S.transitionMapSucc n) (S.center n))
      (S.boundary n)).length := by
    rw [List.length_map]
    exact hjn
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_of_eq hb h]
  simp [List.getElem_append_left hlen]


end

private theorem containedComponentsIdeal_pow_mul_lowerIdealAfterBlowup_consolidated401 (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    DivisorReduction.containedComponentsIdeal T j hj ^ T.mult * DivisorReduction.lowerIdealAfterBlowup T j hj = T.ideal := by
  obtain ⟨J, hJ⟩ := exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj
  have hex : Blowup.exceptionalIdeal (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
      = DivisorReduction.containedComponentsIdeal T j hj := by
    rw [Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id]
  have hA : (T.ideal.comap (𝟙 T.scheme)).comap (𝟙 T.scheme) = T.ideal := by
    rw [Scheme.IdealSheafData.comap_id, Scheme.IdealSheafData.comap_id]
  have h1 : ∃ B, Blowup.exceptionalIdeal (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) ^ T.mult * B
      = (T.ideal.comap (𝟙 T.scheme)).comap (𝟙 T.scheme) := by
    refine ⟨J, ?_⟩
    rw [hex, hA]
    exact hJ
  have h2 := pow_mul_residualByPow ((T.ideal.comap (𝟙 T.scheme)).comap (𝟙 T.scheme))
    (Blowup.exceptionalIdeal (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)) T.mult h1
  rw [hex, hA] at h2
  unfold DivisorReduction.lowerIdealAfterBlowup
  rw [hex, hA]
  exact h2

namespace TransportedDivisor

theorem support_iteratedComap {X : Scheme.{u}} (d : BlowupSequenceData X) (B : (d.obj 0).IdealSheafData)
    (t : ℕ) :
    (↑(iteratedComap d B t).support : Set ↥(d.obj t)) =
      ⇑(d.projectionToBase t ≫ d.isoZero.inv) ⁻¹' (↑B.support : Set ↥(d.obj 0)) := by
  induction t with
  | zero =>
    have h0 : d.projectionToBase 0 ≫ d.isoZero.inv = 𝟙 (d.obj 0) := by
      rw [BlowupSequenceData.projectionToBase_zero]
      exact d.isoZero.hom_inv_id
    rw [iteratedComap_zero, h0]
    ext x
    simp only [Set.mem_preimage, Scheme.Hom.id_base, TopCat.id_app]
  | succ t ih =>
    have hcomp : d.projectionToBase (t + 1) ≫ d.isoZero.inv
        = d.map t ≫ (d.projectionToBase t ≫ d.isoZero.inv) := by
      rw [BlowupSequenceData.projectionToBase_succ, Category.assoc]
    ext x
    rw [iteratedComap_succ]
    have hmem : x ∈ (↑((iteratedComap d B t).comap (d.map t)).support :
          Set ↥(d.obj (t + 1))) ↔
        d.map t x ∈ (↑(iteratedComap d B t).support : Set ↥(d.obj t)) :=
      Scheme.IdealSheafData.mem_support_comap
    rw [hmem, ih, hcomp]
    simp only [Set.mem_preimage, Scheme.Hom.comp_apply]

end TransportedDivisor

namespace DivisorReduction

theorem disjoint_support_lowerIdealAfterBlowup_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (j : ℕ) (hj : j < T.boundary.length) :
    Disjoint ((lowerIdealAfterBlowup T j hj).support : Set ↥T.scheme)
      ((containedComponentsIdeal T j hj).support : Set ↥T.scheme) := by
  have := hV.charZero
  have := hV.smooth
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have hkey := containedComponentsIdeal_pow_mul_lowerIdealAfterBlowup_consolidated401 T hV j hj
  have ha : 1 ≤ orderAt (containedComponentsIdeal T j hj) x :=
    (one_le_orderAt_iff_mem_support _ _).2 hx2
  have hbb : 1 ≤ orderAt (lowerIdealAfterBlowup T j hj) x :=
    (one_le_orderAt_iff_mem_support _ _).2 hx1
  have h3 : orderAt T.ideal x
      = (T.mult : ℕ∞) * orderAt (containedComponentsIdeal T j hj) x
        + orderAt (lowerIdealAfterBlowup T j hj) x := by
    rw [← hkey, orderAt_mul T.base T.structMap, orderAt_pow T.base T.structMap]
  have hm : (T.mult : ℕ∞) ≤ (T.mult : ℕ∞) * orderAt (containedComponentsIdeal T j hj) x := by
    calc (T.mult : ℕ∞) = (T.mult : ℕ∞) * 1 := (mul_one _).symm
      _ ≤ (T.mult : ℕ∞) * orderAt (containedComponentsIdeal T j hj) x := by gcongr
  have hordGe : (T.mult : ℕ∞) + 1 ≤ orderAt T.ideal x := by
    rw [h3]
    exact add_le_add hm hbb
  exact not_natCast_add_one_le_self_consolidated401 T.mult (le_trans hordGe (hord x))

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups) (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)

private theorem ambientBlowupSeq_isoObjZero_hom_consolidated401 :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom = 𝟙 T.scheme :=
  congrArg Iso.hom (ambientBlowupSequence_isoObjZero (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr)

private theorem ambientBlowupSeq_isoObjZero_inv_consolidated401 :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.inv = 𝟙 T.scheme :=
  congrArg Iso.inv (ambientBlowupSequence_isoObjZero (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr)

private theorem ambientBlowupSeq_projectionToBase_zero_comp_structureMorphism_consolidated401 :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase 0 ≫ T.structMap = T.structMap := by
  have h1 : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase 0 = 𝟙 T.scheme :=
    (BlowupSequenceData.projectionToBase_zero _).trans (ambientBlowupSeq_isoObjZero_hom_consolidated401 hres hno T j hj I₀ E₀ s hpr)
  rw [h1]
  exact Category.id_comp T.structMap

private theorem ambientBlowupSeq_projectionToBase_comp_isoObjZero_inv_consolidated401 (n : ℕ) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase n ≫
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.inv
      = (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase n := by
  rw [ambientBlowupSeq_isoObjZero_inv_consolidated401 hres hno T j hj I₀ E₀ s hpr]
  exact Category.comp_id ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase n)


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length) (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj)) (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups) (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked T.structMap T.ideal T.mult T.boundary)
include hmk

private theorem prependedAmbientSeq_length_consolidated401 :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).length = s.length + 1 := by
  have h1 : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).length
      = s.length + 1 := by
    rw [BlowupSequenceData.prepend_length,
      ambientBlowupSeq_length hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr]
  exact h1

private theorem prependedAmbientSeq_blowupMorphism_consolidated401 (n : ℕ) :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc n =
      (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).map n :=
  MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism
    ((BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).toMarkedBlowupSequenceData
      T.structMap T.ideal T.mult T.boundary hmk) n

private theorem prependedAmbientSeq_center_consolidated401 (n : ℕ) :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).center n =
      (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).center n :=
  MarkedBlowupSequenceData.toMarkedSequence_center
    ((BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).toMarkedBlowupSequenceData
      T.structMap T.ideal T.mult T.boundary hmk) n

private theorem prependedAmbientSeq_blowupMorphism_zero_consolidated401 :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc 0 = 𝟙 T.scheme := by
  rw [prependedAmbientSeq_blowupMorphism_consolidated401 hres hno T j hj hb s hpr hmk 0, BlowupSequenceData.prepend_blowupMorphism_zero]
  exact ambientBlowupSeq_isoObjZero_hom_consolidated401 hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr

private theorem prependedAmbientSeq_blowupMorphism_succ_consolidated401 (n : ℕ) :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc (n + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).map n :=
  (prependedAmbientSeq_blowupMorphism_consolidated401 hres hno T j hj hb s hpr hmk (n + 1)).trans
    (BlowupSequenceData.prepend_blowupMorphism_succ (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr) n)

private theorem prependedAmbientSeq_center_zero_consolidated401 :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).center 0 = containedComponentsIdeal T j hj :=
  (prependedAmbientSeq_center_consolidated401 hres hno T j hj hb s hpr hmk 0).trans
    (BlowupSequenceData.prepend_center_zero (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr))

private theorem prependedAmbientSeq_center_succ_consolidated401 (n : ℕ) :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).center (n + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).center n :=
  (prependedAmbientSeq_center_consolidated401 hres hno T j hj hb s hpr hmk (n + 1)).trans
    (BlowupSequenceData.prepend_center_succ (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr) n)

private theorem prependedAmbientSeq_isoObjZero_hom_consolidated401 :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).isoZero.hom = 𝟙 T.scheme :=
  congrArg Iso.hom (BlowupSequenceData.prepend_isoObjZero (containedComponentsIdeal T j hj) hb
    (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr))

private theorem prependedAmbientSeq_projectionToSpec_succ_consolidated401 (n : ℕ) :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToSpec (n + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase n ≫
        T.structMap := by
  have h1 := MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec
    ((BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).toMarkedBlowupSequenceData
      T.structMap T.ideal T.mult T.boundary hmk) (n + 1)
  have h2 := BlowupSequenceData.projectionToBase_prepend_succ (containedComponentsIdeal T j hj) hb
    (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr) n
  exact h1.trans (congrArg (fun f => f ≫ T.structMap) h2)

private theorem ker_embeddingIntoAmbient_zero_consolidated401 :
    AlgebraicGeometry.Scheme.Hom.ker
        (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr 0)
      = T.boundary.get ⟨j, hj⟩ := by
  have h2 := ker_embeddingIntoAmbient_zero_eq_comap_blowupMorphism hres hno T j hj hb s hpr hmk
  rw [prependedAmbientSeq_isoObjZero_hom_consolidated401 hres hno T j hj hb s hpr hmk,
    prependedAmbientSeq_blowupMorphism_zero_consolidated401 hres hno T j hj hb s hpr hmk] at h2
  have h3 : ((T.boundary.get ⟨j, hj⟩).comap (𝟙 T.scheme)).comap (𝟙 T.scheme)
      = T.boundary.get ⟨j, hj⟩ := by
    rw [Scheme.IdealSheafData.comap_id, Scheme.IdealSheafData.comap_id]
  exact h2.trans h3


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme]

private theorem isSmoothDivisor_prependedAmbientSeq_boundary_get_consolidated401 (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary)
    (i : ℕ) (hi : i ≤ s.length + 1)
    (h : j < ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary i).length) :
    IsSmoothDivisor ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToSpec i)
      (((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary i).get ⟨j, h⟩) := by
  have hvl : (T.transformAt (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) i).IsAdmissible :=
    MarkedIdealWithBoundary.IsAdmissible.transformAt effectiveCartierSupportContainsNoComponent hV
      (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) i
      (by rw [prependedAmbientSeq_length_consolidated401 hres hno T j hj hb s hpr hmk]; omega)
  have h2 : j < (T.transformAt (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) i).boundary.length := by
    rw [MarkedIdealWithBoundary.transformAt_boundary]
    exact h
  have h3 := isSmoothDivisor_boundary_get
    (T.transformAt (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) i) hvl j h2
  rw [MarkedIdealWithBoundary.transformAt_structureMorphism] at h3
  exact h3

private theorem prependedAmbientSeq_boundary_succ_get_consolidated401
    (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    ∀ n, n ≤ s.length →
      ∀ h : j < ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary (n + 1)).length,
        ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary (n + 1)).get ⟨j, h⟩ =
          iteratedStrictTransform_consolidated401
            (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)
            (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)
              ((T.boundary.get ⟨j, hj⟩).comap (𝟙 T.scheme))) n := by
  intro n
  induction n with
  | zero =>
    intro _ h
    have hz0 : j < ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary 0).length :=
      lt_of_lt_of_le hj
        (length_le_length_boundary_consolidated401 (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) 0 (Nat.zero_le _))
    rw [boundary_succ_get_eq_strictTransform_consolidated401 (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) j 0
        (by rw [prependedAmbientSeq_length_consolidated401 hres hno T j hj hb s hpr hmk]; omega) hz0 h,
      boundary_zero_get_eq_comap_consolidated401 (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) j hj hz0,
      prependedAmbientSeq_isoObjZero_hom_consolidated401 hres hno T j hj hb s hpr hmk,
      prependedAmbientSeq_blowupMorphism_zero_consolidated401 hres hno T j hj hb s hpr hmk,
      prependedAmbientSeq_center_zero_consolidated401 hres hno T j hj hb s hpr hmk]
    rfl
  | succ n ih =>
    intro hn h
    have hn1 : j < ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary (n + 1)).length :=
      lt_of_lt_of_le hj (length_le_length_boundary_consolidated401 (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) (n + 1)
        (by rw [prependedAmbientSeq_length_consolidated401 hres hno T j hj hb s hpr hmk]; omega))
    rw [boundary_succ_get_eq_strictTransform_consolidated401 (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) j (n + 1)
        (by rw [prependedAmbientSeq_length_consolidated401 hres hno T j hj hb s hpr hmk]; omega) hn1 h,
      ih (by omega) hn1,
      prependedAmbientSeq_blowupMorphism_succ_consolidated401 hres hno T j hj hb s hpr hmk n,
      prependedAmbientSeq_center_succ_consolidated401 hres hno T j hj hb s hpr hmk n]
    rfl


end

private theorem projectionToBase_mem_support_of_mem_support_ideal_consolidated401 (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups) :
    ∀ n, n ≤ s.length → ∀ y : ↥((MarkedBlowupSequenceData.ofMarkedSequence s).obj n),
      y ∈ (↑((MarkedBlowupSequenceData.ofMarkedSequence s).ideal n).support :
          Set ↥((MarkedBlowupSequenceData.ofMarkedSequence s).obj n)) →
      (MarkedBlowupSequenceData.ofMarkedSequence s).proj n y ∈
        (↑(restrictTwistedToDivisor T j hj).ideal.support : Set ↥(restrictTwistedToDivisor T j hj).scheme) := by
  intro n
  induction n with
  | zero =>
    intro _ y hy
    have h1 : (MarkedBlowupSequenceData.ofMarkedSequence s).ideal 0
        = (restrictTwistedToDivisor T j hj).ideal.comap (MarkedBlowupSequenceData.ofMarkedSequence s).isoZero.hom :=
      (MarkedBlowupSequenceData.ofMarkedSequence s).ideal_zero
    rw [h1] at hy
    have h2 : (MarkedBlowupSequenceData.ofMarkedSequence s).isoZero.hom y ∈
        (↑(restrictTwistedToDivisor T j hj).ideal.support : Set ↥(restrictTwistedToDivisor T j hj).scheme) :=
      Scheme.IdealSheafData.mem_support_comap.mp hy
    have h3 : (MarkedBlowupSequenceData.ofMarkedSequence s).proj 0
        = (MarkedBlowupSequenceData.ofMarkedSequence s).isoZero.hom :=
      (MarkedBlowupSequenceData.ofMarkedSequence s).proj_zero
    rw [h3]
    exact h2
  | succ n ih =>
    intro hn y hy
    have hn' : n < (MarkedBlowupSequenceData.ofMarkedSequence s).length := by
      rw [MarkedBlowupSequenceData.ofMarkedSequence_length]
      omega
    have h2 := (MarkedBlowupSequenceData.ofMarkedSequence s).ideal_succ n hn'
    have h1 : (1 : ℕ∞) ≤ orderAt ((MarkedBlowupSequenceData.ofMarkedSequence s).ideal (n + 1)) y :=
      (one_le_orderAt_iff_mem_support _ _).2 hy
    have h5 : orderAt (Blowup.exceptionalIdeal ((MarkedBlowupSequenceData.ofMarkedSequence s).map n)
            ((MarkedBlowupSequenceData.ofMarkedSequence s).center n) ^ (restrictTwistedToDivisor T j hj).mult) y
          + orderAt ((MarkedBlowupSequenceData.ofMarkedSequence s).ideal (n + 1)) y
        ≤ orderAt (Blowup.exceptionalIdeal ((MarkedBlowupSequenceData.ofMarkedSequence s).map n)
            ((MarkedBlowupSequenceData.ofMarkedSequence s).center n) ^ (restrictTwistedToDivisor T j hj).mult
            * (MarkedBlowupSequenceData.ofMarkedSequence s).ideal (n + 1)) y := by
      apply add_orderAt_le_orderAt_mul
    rw [h2] at h5
    have h6 : (1 : ℕ∞) ≤ orderAt (((MarkedBlowupSequenceData.ofMarkedSequence s).ideal n).comap
        ((MarkedBlowupSequenceData.ofMarkedSequence s).map n)) y :=
      le_trans (le_trans h1 le_add_self) h5
    have h7 : y ∈ (↑(((MarkedBlowupSequenceData.ofMarkedSequence s).ideal n).comap
        ((MarkedBlowupSequenceData.ofMarkedSequence s).map n)).support :
          Set ↥((MarkedBlowupSequenceData.ofMarkedSequence s).obj (n + 1))) :=
      (one_le_orderAt_iff_mem_support _ _).1 h6
    have h8 : (MarkedBlowupSequenceData.ofMarkedSequence s).map n y ∈
        (↑((MarkedBlowupSequenceData.ofMarkedSequence s).ideal n).support :
          Set ↥((MarkedBlowupSequenceData.ofMarkedSequence s).obj n)) :=
      Scheme.IdealSheafData.mem_support_comap.mp h7
    have h9 := ih (by omega) _ h8
    have h10 : (MarkedBlowupSequenceData.ofMarkedSequence s).proj (n + 1)
        = (MarkedBlowupSequenceData.ofMarkedSequence s).map n ≫ (MarkedBlowupSequenceData.ofMarkedSequence s).proj n :=
      (MarkedBlowupSequenceData.ofMarkedSequence s).proj_succ n
    rw [h10]
    exact h9

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})

private theorem disjoint_support_center_iteratedComap_containedComponentsIdeal_consolidated401
    (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (j : ℕ) (hj : j < T.boundary.length) (hlow : (restrictTwistedToDivisor T j hj).IsAdmissible)
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hcomp : ∀ t ≤ s.length,
      embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t =
        (MarkedBlowupSequenceData.ofMarkedSequence s).proj t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)
    (n : ℕ) (hn : n < s.length) :
    Disjoint
      (↑((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hpr).center n).support :
        Set ↥((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).obj n))
      (↑(TransportedDivisor.iteratedComap
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)
          (containedComponentsIdeal T j hj) n).support :
        Set ↥((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hpr).obj n)) := by
  rw [Set.disjoint_left]
  intro y hy1 hy2
  rw [support_ambientBlowupSeq_center_eq_image hres hno T j hj (lowerIdealAfterBlowup T j hj)
    (lowerBoundaryAfterBlowup T j hj) s hpr n] at hy1
  obtain ⟨z, hz, rfl⟩ := hy1
  have hn' : n < (MarkedBlowupSequenceData.ofMarkedSequence s).length := by
    rw [MarkedBlowupSequenceData.ofMarkedSequence_length]
    exact hn
  have hzco := (MarkedBlowupSequenceData.ofMarkedSequence s).center_order n hn' hz
  rw [mem_orderAtLeastLocus_iff] at hzco
  have hz2 : (1 : ℕ∞) ≤ orderAt ((MarkedBlowupSequenceData.ofMarkedSequence s).ideal n) z :=
    le_trans (by exact_mod_cast hlow.one_le_mult) hzco
  have hzs : z ∈ (↑((MarkedBlowupSequenceData.ofMarkedSequence s).ideal n).support :
      Set ↥((MarkedBlowupSequenceData.ofMarkedSequence s).obj n)) :=
    (one_le_orderAt_iff_mem_support _ _).1 hz2
  have hw1 := projectionToBase_mem_support_of_mem_support_ideal_consolidated401 T j hj s n (le_of_lt hn) z hzs
  have hw2 : (T.boundary.get ⟨j, hj⟩).subschemeι ((MarkedBlowupSequenceData.ofMarkedSequence s).proj n z)
      ∈ (↑(lowerIdealAfterBlowup T j hj).support : Set ↥T.scheme) :=
    Scheme.IdealSheafData.mem_support_comap.mp hw1
  have hsupp := TransportedDivisor.support_iteratedComap
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)
      (containedComponentsIdeal T j hj) n
  rw [ambientBlowupSeq_projectionToBase_comp_isoObjZero_inv_consolidated401 hres hno T j hj (lowerIdealAfterBlowup T j hj)
    (lowerBoundaryAfterBlowup T j hj) s hpr n] at hsupp
  rw [hsupp] at hy2
  have hz' : z ∈ ⇑(embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj)
        (lowerBoundaryAfterBlowup T j hj) s hpr n ≫
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase n) ⁻¹'
      (↑(containedComponentsIdeal T j hj).support : Set ↥T.scheme) := hy2
  rw [hcomp n (le_of_lt hn)] at hz'
  exact (Set.disjoint_left.1
    (disjoint_support_lowerIdealAfterBlowup_containedComponentsIdeal T hV hord j hj)) hw2 hz'

theorem isSmoothDivisor_ker_embeddingIntoAmbient (_hgeom : OrderAtComapOffExceptionalLocus.{u})
    (T : MarkedIdealWithBoundary.{u}) [IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (hlow : (restrictTwistedToDivisor T j hj).IsAdmissible)
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary)
    (hcomp : ∀ t ≤ s.length,
      embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t =
        (MarkedBlowupSequenceData.ofMarkedSequence s).proj t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) :
    ∀ t ≤ s.length,
      IsSmoothDivisor ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToSpec (t + 1))
        (AlgebraicGeometry.Scheme.Hom.ker
          (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t)) := by
  classical
  have := hV.charZero
  have := hV.smooth
  have hL : s.length ≤ (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
      (lowerBoundaryAfterBlowup T j hj) s hpr).length :=
    le_of_eq (ambientBlowupSeq_length hres hno T j hj (lowerIdealAfterBlowup T j hj)
      (lowerBoundaryAfterBlowup T j hj) s hpr).symm
  have hnoeth : ∀ t, t ≤ s.length → IsLocallyNoetherian
      ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).obj t) := by
    intro t htt
    have : IsNoetherian
        ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).obj t) :=
      isNoetherian_ambientBlowupSequence_schemeAt (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t
        (le_of_le_of_eq htt (MarkedBlowupSequenceData.ofMarkedSequence_length s).symm)
    infer_instance
  have hsm : ∀ t, t ≤ s.length → Smooth
      ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t ≫
        T.structMap) := by
    intro t htt
    have h1 := MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hV
      (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) (t + 1)
      (by rw [prependedAmbientSeq_length_consolidated401 hres hno T j hj hb s hpr hmk]; omega)
    rw [prependedAmbientSeq_projectionToSpec_succ_consolidated401 hres hno T j hj hb s hpr hmk t] at h1
    exact h1
  intro t ht
  rw [prependedAmbientSeq_projectionToSpec_succ_consolidated401 hres hno T j hj hb s hpr hmk t]
  refine TransportedDivisor.isSmoothDivisor_strictTransform_of_disjoint_center T.structMap
    (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)
    s.length hL hnoeth hsm
    (fun n => AlgebraicGeometry.Scheme.Hom.ker
      (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr n))
    (iteratedStrictTransform_consolidated401
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)
      (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)
        ((T.boundary.get ⟨j, hj⟩).comap (𝟙 T.scheme))))
    (containedComponentsIdeal T j hj) ?_ ?_ ?_ ?_ ?_ ?_ ?_ t ht
  · rw [ker_embeddingIntoAmbient_zero_consolidated401 hres hno T j hj hb s hpr hmk]
    exact (DivisorReductionBoundary.strictTransform_mul_containedComponentsIdeal T hV j hj).symm
  · exact DivisorReductionBoundary.disjoint_support_strictTransform_containedComponentsIdeal T hV j hj
  · intro n hn
    exact ker_embeddingIntoAmbientBlowupSequence_succ (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr n
      (by rw [MarkedBlowupSequenceData.ofMarkedSequence_length]; exact hn)
  · intro n _
    exact strictTransformIter_succ_consolidated401 _ _ n
  · rw [ambientBlowupSeq_projectionToBase_zero_comp_structureMorphism_consolidated401 hres hno T j hj (lowerIdealAfterBlowup T j hj)
      (lowerBoundaryAfterBlowup T j hj) s hpr]
    exact DivisorReductionBoundary.isSmoothDivisor_containedComponentsIdeal T hV j hj
  · intro n hn
    have hlt : j < ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary (n + 1)).length :=
      lt_of_lt_of_le hj (length_le_length_boundary_consolidated401 (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) (n + 1)
        (by rw [prependedAmbientSeq_length_consolidated401 hres hno T j hj hb s hpr hmk]; omega))
    have h1 := isSmoothDivisor_prependedAmbientSeq_boundary_get_consolidated401 hres hno T hV j hj hb s hpr hmk (n + 1)
      (by omega) hlt
    rw [prependedAmbientSeq_boundary_succ_get_consolidated401 hres hno T j hj hb s hpr hmk n hn hlt,
      prependedAmbientSeq_projectionToSpec_succ_consolidated401 hres hno T j hj hb s hpr hmk n] at h1
    exact h1
  · intro n hn
    exact disjoint_support_center_iteratedComap_containedComponentsIdeal_consolidated401 hres hno T hV hord j hj
      hlow s hpr hcomp n hn


end

end DivisorReduction


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsFunctoriality
section

open CategoryTheory.Limits TopologicalSpace

section

theorem isIrreducible_connectedComponent_boundary_subscheme (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) (z : ↥(T.boundary.get ⟨j, hj⟩).subscheme) :
    IsIrreducible (connectedComponent z) := by
  have : TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    noetherianSpace_boundary_subscheme T hV j hj
  have hsd : IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) :=
    isSmoothDivisor_boundary_get T hV j hj
  have hsm : Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    ((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).mp hsd).2
  have hsep := irreducibleComponentsDisjointOfSmooth T.base (T.boundary.get ⟨j, hj⟩).subscheme
    ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) hsm
  have h1 : connectedComponent z ⊆ irreducibleComponent z :=
    connectedComponent_subset_of_mem_irreducibleComponents hsep
      (irreducibleComponent_mem_irreducibleComponents z) mem_irreducibleComponent
  have h2 : irreducibleComponent z ⊆ connectedComponent z :=
    (isIrreducible_irreducibleComponent (x := z)).2.isPreconnected.subset_connectedComponent
      mem_irreducibleComponent
  rw [Set.Subset.antisymm h1 h2]
  exact isIrreducible_irreducibleComponent

section
variable {X Y : Scheme.{u}} (g : Y ⟶ X)

theorem openSubschemeKer_comap_of_flat_of_noetherian [Flat g] (D : X.IdealSheafData) (A : Set X) (hA : IsClosed A)
    (hirr : ∀ w : ↥D.subscheme, IsIrreducible (connectedComponent w))
    (hN : TopologicalSpace.NoetherianSpace ↥D.subscheme)
    (hN' : TopologicalSpace.NoetherianSpace ↥(D.comap g).subscheme)
    (hopen : IsOpen {w : ↥D.subscheme | connectedComponent w ⊆ ⇑D.subschemeι.base ⁻¹' A})
    (hopen' : IsOpen {w : ↥(D.comap g).subscheme |
      connectedComponent w ⊆ ⇑(D.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)}) :
    openSubschemeKer (D.comap g)
        ⟨{w : ↥(D.comap g).subscheme |
            connectedComponent w ⊆ ⇑(D.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)}, hopen'⟩ =
      (openSubschemeKer D
        ⟨{w : ↥D.subscheme | connectedComponent w ⊆ ⇑D.subschemeι.base ⁻¹' A}, hopen⟩).comap g := by
  have := hN
  have := hN'
  exact openSubschemeKer_comap g D A hA ⟨_, hopen⟩ ⟨_, hopen'⟩ rfl rfl
    (TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset ↥D.subscheme
      (⇑D.subschemeι.base ⁻¹' A))
    (TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset
      ↥(D.comap g).subscheme
      (⇑(D.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A))) hirr

private theorem get_eq_comap_get_of_eq_map_consolidated430 (E : List X.IdealSheafData)
    (F : List Y.IdealSheafData) (hF : F = E.map (fun D => D.comap g)) (j : ℕ)
    (hj : j < E.length) (hj' : j < F.length) :
    F.get ⟨j, hj'⟩ = (E.get ⟨j, hj⟩).comap g := by
  subst hF
  simp [List.get_eq_getElem]


end

private theorem containedComponentsIdeal_comap_of_flat_consolidated430 (T T' : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hV' : T'.IsAdmissible) (g : T'.scheme ⟶ T.scheme) (hflat : Flat g) (j : ℕ)
    (hj : j < T.boundary.length) (hj' : j < T'.boundary.length)
    (hD : T'.boundary.get ⟨j, hj'⟩ = (T.boundary.get ⟨j, hj⟩).comap g)
    (hcs : orderAtLeastLocus T'.ideal T'.mult = ⇑g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)
    (hcl : IsClosed (orderAtLeastLocus T.ideal T.mult)) :
    DivisorReduction.containedComponentsIdeal T' j hj' = (DivisorReduction.containedComponentsIdeal T j hj).comap g := by
  have := hflat
  have hopen := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T hV j hj
  have hopen' := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T' hV' j hj'
  have hirr : ∀ w : ↥(T.boundary.get ⟨j, hj⟩).subscheme, IsIrreducible (connectedComponent w) :=
    fun w => isIrreducible_connectedComponent_boundary_subscheme T hV j hj w
  have hN : TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    noetherianSpace_boundary_subscheme T hV j hj
  have hN' : TopologicalSpace.NoetherianSpace ↥(T'.boundary.get ⟨j, hj'⟩).subscheme :=
    noetherianSpace_boundary_subscheme T' hV' j hj'
  have key : ∀ (D' : T'.scheme.IdealSheafData), D' = (T.boundary.get ⟨j, hj⟩).comap g →
      ∀ (S' : Set ↥D'.subscheme),
        S' = {w : ↥D'.subscheme | connectedComponent w ⊆
            ⇑D'.subschemeι.base ⁻¹' (⇑g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)} →
        ∀ (hop' : IsOpen S'), TopologicalSpace.NoetherianSpace ↥D'.subscheme →
          openSubschemeKer D' ⟨S', hop'⟩ =
            (openSubschemeKer (T.boundary.get ⟨j, hj⟩) ⟨divisorComponentsInOrderLocus T j hj, hopen⟩).comap g := by
    rintro D' rfl S' rfl hop' hNN
    exact openSubschemeKer_comap_of_flat_of_noetherian g (T.boundary.get ⟨j, hj⟩)
      (orderAtLeastLocus T.ideal T.mult) hcl hirr hN hNN hopen hop'
  have hset : divisorComponentsInOrderLocus T' j hj' =
      {w : ↥(T'.boundary.get ⟨j, hj'⟩).subscheme | connectedComponent w ⊆
        ⇑(T'.boundary.get ⟨j, hj'⟩).subschemeι.base ⁻¹'
          (⇑g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)} :=
    congrArg (fun A : Set ↥T'.scheme =>
      {w : ↥(T'.boundary.get ⟨j, hj'⟩).subscheme | connectedComponent w ⊆
        ⇑(T'.boundary.get ⟨j, hj'⟩).subschemeι.base ⁻¹' A}) hcs
  rw [containedComponentsIdeal_eq_openSubschemeKer T j hj hopen, containedComponentsIdeal_eq_openSubschemeKer T' j hj' hopen']
  exact key _ hD _ hset hopen' hN'

section
variable (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
include hV

theorem containedComponentsIdeal_pullbackAlong_of_smooth (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [Smooth h]
    (hq : h ≫ T.structMap = q) (hV' : (T.pullbackAlong Y q h).IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (hj' : j < (T.pullbackAlong Y q h).boundary.length) :
    DivisorReduction.containedComponentsIdeal (T.pullbackAlong Y q h) j hj' =
      (DivisorReduction.containedComponentsIdeal T j hj).comap h := by
  have : CharZero T.base := hV.charZero
  have : Smooth T.structMap := hV.smooth
  have hfl : Flat h := inferInstance
  have hD : (T.pullbackAlong Y q h).boundary.get ⟨j, hj'⟩ =
      (T.boundary.get ⟨j, hj⟩).comap h :=
    get_eq_comap_get_of_eq_map_consolidated430 h T.boundary (T.pullbackAlong Y q h).boundary
      (MarkedIdealWithBoundary.pullbackAlong_boundary T Y q h) j hj hj'
  have hcs : orderAtLeastLocus (T.pullbackAlong Y q h).ideal (T.pullbackAlong Y q h).mult =
      ⇑h.base ⁻¹' orderAtLeastLocus T.ideal T.mult :=
    DivisorReduction.orderAtLeastLocus_comap_of_smooth T hV Y q h hq T.mult
  have hcl : IsClosed (orderAtLeastLocus T.ideal T.mult) :=
    isClosed_orderAtLeastLocus T.base T.structMap T.ideal T.mult
  exact containedComponentsIdeal_comap_of_flat_consolidated430 T (T.pullbackAlong Y q h) hV hV' h hfl j hj hj' hD hcs hcl

theorem containedComponentsIdeal_baseChange (L : Type u) [Field L]
    [CharZero L] (f : T.base →+* L) (hV' : (T.baseChange L f).IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (hj' : j < (T.baseChange L f).boundary.length) :
    DivisorReduction.containedComponentsIdeal (T.baseChange L f) j hj' =
      (DivisorReduction.containedComponentsIdeal T j hj).comap
        (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) := by
  have : CharZero T.base := hV.charZero
  have : Smooth T.structMap := hV.smooth
  have hfl : Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    flat_fieldBaseChangeProjection T L f
  have hD : (T.baseChange L f).boundary.get ⟨j, hj'⟩ =
      (T.boundary.get ⟨j, hj⟩).comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    get_eq_comap_get_of_eq_map_consolidated430 (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) T.boundary
      (T.baseChange L f).boundary (MarkedIdealWithBoundary.baseChange_boundary T L f) j hj hj'
  have hcs : orderAtLeastLocus (T.baseChange L f).ideal (T.baseChange L f).mult =
      ⇑(pullback.fst T.structMap (specMapOfFieldHom T.base L f)).base ⁻¹'
        orderAtLeastLocus T.ideal T.mult :=
    orderAtLeastLocus_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal T.mult
  have hcl : IsClosed (orderAtLeastLocus T.ideal T.mult) :=
    isClosed_orderAtLeastLocus T.base T.structMap T.ideal T.mult
  exact containedComponentsIdeal_comap_of_flat_consolidated430 T (T.baseChange L f) hV hV'
    (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) hfl j hj hj' hD hcs hcl


end


end
end
end FunctorialResolution.EmbeddedResolution
end
