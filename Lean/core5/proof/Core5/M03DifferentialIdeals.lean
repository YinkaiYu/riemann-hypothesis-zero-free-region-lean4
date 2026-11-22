import Mathlib
import Core5.M02EtaleGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

universe u v w
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealLocalization
section


variable {k : Type u} {S : Type v} {S' : Type w}

section
variable [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S'] (M : Submonoid S) [IsLocalization M S']
include M

theorem map_derivIdeal_le (J : Ideal S) :
    Ideal.map (algebraMap S S') (derivIdeal k J) ≤
      derivIdeal k (Ideal.map (algebraMap S S') J) := by
  rw [Ideal.map_le_iff_le_comap, derivIdeal_le_iff]
  constructor
  · intro x hx
    refine Ideal.mem_comap.mpr ?_
    exact le_derivIdeal k _ (Ideal.mem_map_of_mem (algebraMap S S') hx)
  · intro D x hx
    refine Ideal.mem_comap.mpr ?_
    have h := derivation_apply_mem_derivIdeal k (Ideal.map (algebraMap S S') J)
      (D.mapToLocalization (S' := S') M) (Ideal.mem_map_of_mem (algebraMap S S') hx)
    rwa [Derivation.mapToLocalization_algebraMap] at h

private theorem derivation_algebraMap_mem_map_derivIdeal_consolidated43 [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S)
    (D : Derivation k S' S') {a : S} (ha : a ∈ J) :
    D (algebraMap S S' a) ∈ Ideal.map (algebraMap S S') (derivIdeal k J) := by
  obtain ⟨m, D₀, hm⟩ := Derivation.exists_derivation_mul_eq_of_isLocalization (R := k) M D
  refine (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S' m)).mp ?_
  rw [hm a]
  exact Ideal.mem_map_of_mem _ (derivation_apply_mem_derivIdeal k J D₀ ha)

theorem derivIdeal_map_le [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S) :
    derivIdeal k (Ideal.map (algebraMap S S') J) ≤
      Ideal.map (algebraMap S S') (derivIdeal k J) := by
  rw [derivIdeal_le_iff]
  refine ⟨Ideal.map_mono (le_derivIdeal k J), ?_⟩
  intro D x hx
  rw [IsLocalization.mem_map_algebraMap_iff M S'] at hx
  obtain ⟨⟨a, m⟩, hax⟩ := hx
  have h1 : D (x * algebraMap S S' (m : S)) = D (algebraMap S S' (a : S)) := by rw [hax]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1
  have hA : D (algebraMap S S' (a : S)) ∈ Ideal.map (algebraMap S S') (derivIdeal k J) :=
    derivation_algebraMap_mem_map_derivIdeal_consolidated43 M J D a.2
  have hmem1 : algebraMap S S' (m : S) * D (algebraMap S S' (a : S)) ∈
      Ideal.map (algebraMap S S') (derivIdeal k J) := Ideal.mul_mem_left _ _ hA
  have hmem2 : algebraMap S S' (a : S) * D (algebraMap S S' (m : S)) ∈
      Ideal.map (algebraMap S S') (derivIdeal k J) :=
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (le_derivIdeal k J a.2))
  have h3 : algebraMap S S' (m : S) * (algebraMap S S' (m : S) * D x) ∈
      Ideal.map (algebraMap S S') (derivIdeal k J) := by
    have h2 : algebraMap S S' (m : S) * (algebraMap S S' (m : S) * D x) =
        algebraMap S S' (m : S) * D (algebraMap S S' (a : S)) -
          algebraMap S S' (a : S) * D (algebraMap S S' (m : S)) := by
      linear_combination (algebraMap S S' (m : S)) * h1 - (D (algebraMap S S' (m : S))) * hax
    rw [h2]
    exact sub_mem hmem1 hmem2
  exact (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S' m)).mp
    ((Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S' m)).mp h3)

theorem map_derivIdeal [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S) :
    Ideal.map (algebraMap S S') (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S S') J) :=
  le_antisymm (map_derivIdeal_le M J) (derivIdeal_map_le M J)


end

theorem map_derivIdeal_away [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S']
    [Algebra k S'] [IsScalarTower k S S'] (g : S) [IsLocalization.Away g S']
    [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S) :
    Ideal.map (algebraMap S S') (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S S') J) :=
  map_derivIdeal (Submonoid.powers g) J

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealOrderDecrease
section

open IsLocalRing

noncomputable def eulerDerivation (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R]
    {ι : Type*} [Fintype ι] (x : ι → R) (D : ι → Derivation k R R) : Derivation k R R :=
  ∑ i, x i • D i

section
variable (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R] {ι : Type*}

private theorem sum_smul_derivation_apply_consolidated44 (s : Finset ι) (x : ι → R) (D : ι → Derivation k R R) (a : R) :
    (∑ i ∈ s, x i • D i) a = ∑ i ∈ s, x i * D i a := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply,
        Derivation.smul_apply, smul_eq_mul, ih]

theorem eulerDerivation_apply [Fintype ι] (x : ι → R) (D : ι → Derivation k R R) (a : R) :
    eulerDerivation k x D a = ∑ i, x i * D i a := by
  show (∑ i, x i • D i) a = ∑ i, x i * D i a
  exact sum_smul_derivation_apply_consolidated44 k Finset.univ x D a

theorem eulerDerivation_apply_mem_span [Fintype ι] (x : ι → R) (D : ι → Derivation k R R) (a : R) :
    eulerDerivation k x D a ∈ Ideal.span (Set.range x) := by
  rw [eulerDerivation_apply]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)


end

section
variable (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R) (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
include hD

theorem eulerDerivation_apply_generator (j : ι) :
    eulerDerivation k x D (x j) = x j := by
  rw [eulerDerivation_apply]
  simp [hD]

private theorem eulerDerivation_sub_self_mem_sq_consolidated44 {f : R}
    (hf : f ∈ Ideal.span (Set.range x)) :
    eulerDerivation k x D f - f ∈ Ideal.span (Set.range x) ^ 2 := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨j, rfl⟩ := hg
      rw [eulerDerivation_apply_generator k x D hD j, sub_self]
      exact Submodule.zero_mem _
  | zero =>
      rw [map_zero, sub_zero]
      exact Submodule.zero_mem _
  | add a b _ _ iha ihb =>
      have key : eulerDerivation k x D (a + b) - (a + b)
          = (eulerDerivation k x D a - a) + (eulerDerivation k x D b - b) := by
        rw [map_add]; ring
      rw [key]
      exact Submodule.add_mem _ iha ihb
  | smul c a ha iha =>
      have key : eulerDerivation k x D (c • a) - c • a
          = c * (eulerDerivation k x D a - a) + a * eulerDerivation k x D c := by
        rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
      rw [key]
      refine Submodule.add_mem _ (Ideal.mul_mem_left _ _ iha) ?_
      have h2 := Ideal.mul_mem_mul ha (eulerDerivation_apply_mem_span k x D c)
      rwa [← pow_two] at h2

private theorem forall_eulerDerivation_sub_natCast_mul_mem_consolidated44 (r : ℕ) :
    ∀ f : R, f ∈ Ideal.span (Set.range x) ^ r →
      eulerDerivation k x D f - (r : R) * f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
  induction r with
  | zero =>
      intro f _
      have h := eulerDerivation_apply_mem_span k x D f
      simpa using h
  | succ r ih =>
      intro f hf
      rw [pow_succ] at hf
      refine Submodule.mul_induction_on hf ?_ ?_
      · intro a ha b hb
        have hEb := eulerDerivation_sub_self_mem_sq_consolidated44 k x D hD hb
        have hEa := ih a ha
        have h1 : a * (eulerDerivation k x D b - b) ∈ Ideal.span (Set.range x) ^ (r + 2) := by
          have h := Ideal.mul_mem_mul ha hEb
          rwa [← pow_add] at h
        have h2 : (eulerDerivation k x D a - (r : R) * a) * b
            ∈ Ideal.span (Set.range x) ^ (r + 2) := by
          have hb1 : b ∈ Ideal.span (Set.range x) ^ 1 := by rwa [pow_one]
          have h := Ideal.mul_mem_mul hEa hb1
          have e : r + 1 + 1 = r + 2 := by omega
          rw [← pow_add, e] at h
          exact h
        have key : eulerDerivation k x D (a * b) - ((r + 1 : ℕ) : R) * (a * b)
            = a * (eulerDerivation k x D b - b) + (eulerDerivation k x D a - (r : R) * a) * b := by
          rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
          push_cast
          ring
        have hres : eulerDerivation k x D (a * b) - ((r + 1 : ℕ) : R) * (a * b)
            ∈ Ideal.span (Set.range x) ^ (r + 2) := by
          rw [key]
          exact Submodule.add_mem _ h1 h2
        exact hres
      · intro y z hy hz
        have key : eulerDerivation k x D (y + z) - ((r + 1 : ℕ) : R) * (y + z)
            = (eulerDerivation k x D y - ((r + 1 : ℕ) : R) * y)
              + (eulerDerivation k x D z - ((r + 1 : ℕ) : R) * z) := by
          rw [map_add]; ring
        have hres : eulerDerivation k x D (y + z) - ((r + 1 : ℕ) : R) * (y + z)
            ∈ Ideal.span (Set.range x) ^ (r + 1 + 1) := by
          rw [key]
          exact Submodule.add_mem _ hy hz
        exact hres

theorem eulerDerivation_sub_natCast_mul_mem_pow_succ (r : ℕ) {f : R}
    (hf : f ∈ Ideal.span (Set.range x) ^ r) :
    eulerDerivation k x D f - (r : R) * f ∈ Ideal.span (Set.range x) ^ (r + 1) :=
  forall_eulerDerivation_sub_natCast_mul_mem_consolidated44 k x D hD r f hf

theorem mem_pow_succ_of_deriv_mem_pow {r : ℕ} (hr : IsUnit ((r : ℕ) : R))
    {f : R} (hf : f ∈ Ideal.span (Set.range x) ^ r)
    (hdf : ∀ i, D i f ∈ Ideal.span (Set.range x) ^ r) :
    f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
  have hgen : ∀ i, x i * D i f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
    intro i
    have hx1 : x i ∈ Ideal.span (Set.range x) ^ 1 := by
      rw [pow_one]
      exact Ideal.subset_span ⟨i, rfl⟩
    have h := Ideal.mul_mem_mul hx1 (hdf i)
    rw [← pow_add, Nat.add_comm 1 r] at h
    exact h
  have h1 : eulerDerivation k x D f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
    rw [eulerDerivation_apply]
    exact Ideal.sum_mem _ fun i _ => hgen i
  have h2 := eulerDerivation_sub_natCast_mul_mem_pow_succ k x D hD r hf
  have h3 : (r : R) * f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
    have h := Submodule.sub_mem _ h1 h2
    simpa using h
  obtain ⟨u, hu⟩ := hr
  have key : (↑u⁻¹ : R) * ((r : R) * f) = f := by
    rw [← hu, ← mul_assoc, u.inv_mul, one_mul]
  rw [← key]
  exact Ideal.mul_mem_left _ _ h3

theorem not_derivIdeal_le_pow {r : ℕ} (hr : IsUnit ((r : ℕ) : R))
    {I : Ideal R} (h1 : I ≤ Ideal.span (Set.range x) ^ r)
    (h2 : ¬ I ≤ Ideal.span (Set.range x) ^ (r + 1)) :
    ¬ derivIdeal k I ≤ Ideal.span (Set.range x) ^ r := by
  intro h
  apply h2
  intro f hf
  exact mem_pow_succ_of_deriv_mem_pow k x D hD hr (h1 hf)
    (fun i => h (derivation_apply_mem_derivIdeal k I (D i) hf))


end

private theorem eq_natCast_of_le_of_not_succ_le_consolidated44 (n : ℕ) (a : ℕ∞) (h1 : (n : ℕ∞) ≤ a)
    (h2 : ¬ ((n + 1 : ℕ) : ℕ∞) ≤ a) : a = (n : ℕ∞) := by
  rcases eq_top_or_lt_top a with rfl | hlt
  · exact absurd le_top h2
  · lift a to ℕ using hlt.ne
    have hn : n ≤ a := by exact_mod_cast h1
    have hn2 : ¬ (n + 1 ≤ a) := by
      intro hc
      exact h2 (by exact_mod_cast hc)
    have ha : a = n := by omega
    exact_mod_cast ha

section
variable (k : Type*) [CommRing k] {R : Type*} [CommRing R] [IsLocalRing R] [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R) (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R) (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R)) {I : Ideal R} {r : ℕ}
include hD hx hunit

theorem idealOrder_derivIdeal_of_isUnit_natCast (hr : 1 ≤ r) (hI : idealOrder I = (r : ℕ∞)) :
    idealOrder (derivIdeal k I) = ((r - 1 : ℕ) : ℕ∞) := by
  have hIr : I ≤ IsLocalRing.maximalIdeal R ^ r := (le_idealOrder_iff I r).mp hI.ge
  have hIr1 : ¬ I ≤ IsLocalRing.maximalIdeal R ^ (r + 1) := by
    intro hc
    have h := (le_idealOrder_iff I (r + 1)).mpr hc
    rw [hI] at h
    have h' : r + 1 ≤ r := by exact_mod_cast h
    omega
  have hunitr : IsUnit ((r : ℕ) : R) := hunit r hr
  have hnot : ¬ derivIdeal k I ≤ Ideal.span (Set.range x) ^ r :=
    not_derivIdeal_le_pow k x D hD hunitr (by rw [hx]; exact hIr) (by rw [hx]; exact hIr1)
  have hle : derivIdeal k I ≤ IsLocalRing.maximalIdeal R ^ (r - 1) :=
    derivIdeal_le_pow_of_le_pow k hIr
  have h1 : ((r - 1 : ℕ) : ℕ∞) ≤ idealOrder (derivIdeal k I) :=
    (le_idealOrder_iff _ (r - 1)).mpr hle
  have h2 : ¬ (((r - 1) + 1 : ℕ) : ℕ∞) ≤ idealOrder (derivIdeal k I) := by
    intro hc
    have h := (le_idealOrder_iff _ ((r - 1) + 1)).mp hc
    apply hnot
    rw [hx]
    have hrr : (r - 1) + 1 = r := by omega
    rwa [hrr] at h
  exact eq_natCast_of_le_of_not_succ_le_consolidated44 (r - 1) _ h1 h2

theorem idealOrder_derivIdealIterate_of_isUnit_natCast (hI : idealOrder I = (r : ℕ∞)) {j : ℕ} (hj : j ≤ r) :
    idealOrder (derivIdealIterate k j I) = ((r - j : ℕ) : ℕ∞) := by
  revert hj
  induction j with
  | zero =>
      intro _
      rw [derivIdealIterate_zero, Nat.sub_zero]
      exact hI
  | succ j ih =>
      intro hj
      have hj' : j ≤ r := by omega
      have hprev := ih hj'
      have h1 : 1 ≤ r - j := by omega
      have h := idealOrder_derivIdeal_of_isUnit_natCast k x D hD hx hunit h1 hprev
      rw [derivIdealIterate_succ]
      have heq : r - j - 1 = r - (j + 1) := by omega
      rwa [heq] at h


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
section

open AlgebraicGeometry TopologicalSpace


variable {X : Scheme.{u}}

noncomputable def stalkIdeal (I : X.IdealSheafData) (x : X) : Ideal (X.presheaf.stalk x) :=
  ⨆ U : {U : X.affineOpens // x ∈ U.1.1},
    Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (I.ideal U.1)

private theorem map_germ_ideal_congr_consolidated45 {X : Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (W W' : X.affineOpens) (h : W = W') (hW : x ∈ W.1) (hW' : x ∈ W'.1) :
    Ideal.map (X.presheaf.germ W.1 x hW).hom (I.ideal W)
      = Ideal.map (X.presheaf.germ W'.1 x hW').hom (I.ideal W') := by
  subst h
  rfl

open CategoryTheory in
private theorem map_germ_ideal_affineBasicOpen_consolidated45 {X : Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (U : X.affineOpens) (f : Γ(X, U.1)) (hxU : x ∈ U.1)
    (hxf : x ∈ (X.affineBasicOpen f).1) :
    Ideal.map (X.presheaf.germ U.1 x hxU).hom (I.ideal U)
      = Ideal.map (X.presheaf.germ (X.affineBasicOpen f).1 x hxf).hom
          (I.ideal (X.affineBasicOpen f)) := by
  have hxf' : x ∈ X.basicOpen f := hxf
  have hgerm : (X.presheaf.germ (X.basicOpen f) x hxf').hom.comp
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
      = (X.presheaf.germ U.1 x hxU).hom := by
    rw [← CommRingCat.hom_comp, X.presheaf.germ_res]
  have h1 : Ideal.map (X.presheaf.germ (X.basicOpen f) x hxf').hom
      (Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom (I.ideal U))
      = Ideal.map (X.presheaf.germ U.1 x hxU).hom (I.ideal U) := by
    rw [Ideal.map_map, hgerm]
  rw [← h1]
  exact congrArg (fun J : Ideal Γ(X, X.basicOpen f) =>
    Ideal.map (X.presheaf.germ (X.basicOpen f) x hxf').hom J) (I.map_ideal_basicOpen U f)

private theorem map_germ_ideal_eq_consolidated45 {X : Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (V U : X.affineOpens) (hxV : x ∈ V.1) (hxU : x ∈ U.1) :
    Ideal.map (X.presheaf.germ V.1 x hxV).hom (I.ideal V)
      = Ideal.map (X.presheaf.germ U.1 x hxU).hom (I.ideal U) := by
  obtain ⟨f, g, hfg, hxf⟩ :=
    AlgebraicGeometry.exists_basicOpen_le_affine_inter V.2 U.2 x ⟨hxV, hxU⟩
  have hxg : x ∈ X.basicOpen g := by rw [← hfg]; exact hxf
  have hW : X.affineBasicOpen f = X.affineBasicOpen g := Subtype.ext hfg
  rw [map_germ_ideal_affineBasicOpen_consolidated45 I x V f hxV hxf,
    map_germ_ideal_affineBasicOpen_consolidated45 I x U g hxU hxg]
  exact map_germ_ideal_congr_consolidated45 I x (X.affineBasicOpen f) (X.affineBasicOpen g) hW hxf hxg

section
variable (I : X.IdealSheafData) (x : X) (U : X.affineOpens) (hx : x ∈ U.1)

theorem stalkIdeal_eq_map_germ :
    stalkIdeal I x = Ideal.map (X.presheaf.germ U.1 x hx).hom (I.ideal U) := by
  have h : stalkIdeal I x = ⨆ V : {V : X.affineOpens // x ∈ V.1.1},
      Ideal.map (X.presheaf.germ V.1.1 x V.2).hom (I.ideal V.1) := rfl
  rw [h]
  refine le_antisymm (iSup_le ?_) ?_
  · rintro ⟨V, hxV⟩
    exact le_of_eq (map_germ_ideal_eq_consolidated45 I x V U hxV hx)
  · exact le_iSup (fun V : {V : X.affineOpens // x ∈ V.1.1} =>
      Ideal.map (X.presheaf.germ V.1.1 x V.2).hom (I.ideal V.1)) ⟨U, hx⟩

theorem germ_mem_stalkIdeal {s : Γ(X, U.1)} (hs : s ∈ I.ideal U) :
    (X.presheaf.germ U.1 x hx).hom s ∈ stalkIdeal I x := by
  have h : Ideal.map (X.presheaf.germ U.1 x hx).hom (I.ideal U) ≤ stalkIdeal I x :=
    le_iSup (fun V : {V : X.affineOpens // x ∈ V.1.1} =>
      Ideal.map (X.presheaf.germ V.1.1 x V.2).hom (I.ideal V.1)) ⟨U, hx⟩
  exact SetLike.le_def.mp h (Ideal.mem_map_of_mem _ hs)


end

section
variable (x : X)

theorem stalkIdeal_top : stalkIdeal (⊤ : X.IdealSheafData) x = ⊤ := by
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  have h1 : (1 : Γ(X, U.1)) ∈ (⊤ : X.IdealSheafData).ideal U := by simp
  have h3 : Ideal.map (X.presheaf.germ U.1 x hxU).hom ((⊤ : X.IdealSheafData).ideal U) ≤
      stalkIdeal (⊤ : X.IdealSheafData) x :=
    le_iSup (fun V : {V : X.affineOpens // x ∈ V.1.1} =>
      Ideal.map (X.presheaf.germ V.1.1 x V.2).hom ((⊤ : X.IdealSheafData).ideal V.1)) ⟨U, hxU⟩
  have h2 := Ideal.mem_map_of_mem (X.presheaf.germ U.1 x hxU).hom h1
  rw [map_one] at h2
  exact (Ideal.eq_top_iff_one _).mpr (SetLike.le_def.mp h3 h2)

theorem stalkIdeal_bot : stalkIdeal (⊥ : X.IdealSheafData) x = ⊥ := by
  have h : ∀ U : X.affineOpens, (⊥ : X.IdealSheafData).ideal U = ⊥ := fun U => by simp
  simp only [stalkIdeal, h, Ideal.map_bot, iSup_bot]


end

theorem stalkIdeal_mono {I J : X.IdealSheafData} (h : I ≤ J) (x : X) :
    stalkIdeal I x ≤ stalkIdeal J x := by
  show (⨆ U : {U : X.affineOpens // x ∈ U.1.1},
        Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (I.ideal U.1)) ≤
      ⨆ U : {U : X.affineOpens // x ∈ U.1.1},
        Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (J.ideal U.1)
  exact iSup_mono fun U => Ideal.map_mono (h U.1)

section
variable {X : Scheme.{u}}

private theorem map_germ_le_stalkIdeal_consolidated45 (I : X.IdealSheafData) (x : X)
    (U : {U : X.affineOpens // x ∈ U.1.1}) :
    Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (I.ideal U.1) ≤ stalkIdeal I x :=
  le_iSup (fun V : {V : X.affineOpens // x ∈ V.1.1} =>
    Ideal.map (X.presheaf.germ V.1.1 x V.2).hom (I.ideal V.1)) U

private theorem stalkIdeal_sup_le_consolidated45 (I J : X.IdealSheafData) (x : X) :
    stalkIdeal (I ⊔ J) x ≤ stalkIdeal I x ⊔ stalkIdeal J x := by
  show (⨆ U : {U : X.affineOpens // x ∈ U.1.1},
      Ideal.map (X.presheaf.germ U.1.1 x U.2).hom ((I ⊔ J).ideal U.1)) ≤
      stalkIdeal I x ⊔ stalkIdeal J x
  refine iSup_le fun U => ?_
  have h1 : (I ⊔ J).ideal U.1 = I.ideal U.1 ⊔ J.ideal U.1 := rfl
  rw [h1, Ideal.map_sup]
  exact sup_le (le_sup_of_le_left (map_germ_le_stalkIdeal_consolidated45 I x U))
    (le_sup_of_le_right (map_germ_le_stalkIdeal_consolidated45 J x U))


end

section
variable (I J : X.IdealSheafData) (x : X)

theorem stalkIdeal_sup :
    stalkIdeal (I ⊔ J) x = stalkIdeal I x ⊔ stalkIdeal J x :=
  le_antisymm (stalkIdeal_sup_le_consolidated45 I J x)
    (sup_le (stalkIdeal_mono le_sup_left x) (stalkIdeal_mono le_sup_right x))

theorem stalkIdeal_mul :
    stalkIdeal (I * J) x = stalkIdeal I x * stalkIdeal J x := by
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  have hmul : (I * J).ideal U = I.ideal U * J.ideal U :=
    congrFun (Scheme.IdealSheafData.ideal_mul ..) U
  rw [stalkIdeal_eq_map_germ (I * J) x U hxU, stalkIdeal_eq_map_germ I x U hxU,
    stalkIdeal_eq_map_germ J x U hxU, hmul, Ideal.map_mul]


end

private theorem idealSheafData_one_eq_top_consolidated45 {X : Scheme.{u}} :
    (1 : X.IdealSheafData) = ⊤ := rfl

theorem stalkIdeal_pow (I : X.IdealSheafData) (n : ℕ) (x : X) :
    stalkIdeal (I ^ n) x = stalkIdeal I x ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, idealSheafData_one_eq_top_consolidated45, stalkIdeal_top, Ideal.one_eq_top]
  | succ n ih =>
    rw [pow_succ, pow_succ, stalkIdeal_mul, ih]

section
variable {X : Scheme.{u}}

private theorem germ_mem_maximalIdeal_iff_not_mem_basicOpen_consolidated45 (x : X) (U : X.Opens) (hxU : x ∈ U)
    (f : Γ(X, U)) :
    (X.presheaf.germ U x hxU).hom f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
      x ∉ X.basicOpen f := by
  have h := AlgebraicGeometry.Scheme.mem_basicOpen X f x hxU
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hn hx
    exact hn (h.mp hx)
  · intro hn hu
    exact hn (h.mpr hu)

private theorem mem_support_iff_forall_germ_mem_maximalIdeal_consolidated45 (I : X.IdealSheafData) (x : X) (U : X.affineOpens) (hxU : x ∈ U.1) :
    x ∈ I.support ↔ ∀ f ∈ I.ideal U,
      (X.presheaf.germ U.1 x hxU).hom f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  rw [AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := U) hxU,
    AlgebraicGeometry.Scheme.mem_zeroLocus_iff]
  constructor
  · intro h f hf
    exact (germ_mem_maximalIdeal_iff_not_mem_basicOpen_consolidated45 x U.1 hxU f).mpr (h f hf)
  · intro h f hf
    exact (germ_mem_maximalIdeal_iff_not_mem_basicOpen_consolidated45 x U.1 hxU f).mp (h f hf)


end

section
variable (I : X.IdealSheafData) (x : X)

theorem mem_support_iff_stalkIdeal_le_maximalIdeal :
    x ∈ I.support ↔ stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨U, hxU0⟩ := X.exists_affineOpens_mem x
  have hxU : x ∈ U.1 := hxU0
  rw [stalkIdeal_eq_map_germ I x U hxU, Ideal.map_le_iff_le_comap,
    mem_support_iff_forall_germ_mem_maximalIdeal_consolidated45 I x U hxU]
  constructor
  · intro h f hf
    exact h f hf
  · intro h f hf
    exact h hf

theorem mem_support_iff_stalkIdeal_ne_top :
    x ∈ I.support ↔ stalkIdeal I x ≠ ⊤ := by
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal]
  refine ⟨fun h htop => ?_, fun h => IsLocalRing.le_maximalIdeal h⟩
  rw [htop, top_le_iff] at h
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top h


end

noncomputable def orderAt (I : X.IdealSheafData) (x : X) : ℕ∞ :=
  idealOrder (stalkIdeal I x)

section
variable (I : X.IdealSheafData) (x : X)

theorem orderAt_eq_idealOrder :
    orderAt I x = idealOrder (stalkIdeal I x) := rfl

theorem le_orderAt_iff (n : ℕ) :
    (n : ℕ∞) ≤ orderAt I x ↔
      stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n :=
  le_idealOrder_iff (stalkIdeal I x) n


end

section
variable (x : X)

theorem orderAt_top : orderAt (⊤ : X.IdealSheafData) x = 0 := by
  rw [orderAt_eq_idealOrder, stalkIdeal_top, idealOrder_top]

theorem orderAt_bot : orderAt (⊥ : X.IdealSheafData) x = ⊤ := by
  rw [orderAt_eq_idealOrder, stalkIdeal_bot, idealOrder_bot]


end

theorem orderAt_le_of_le {I J : X.IdealSheafData} (h : I ≤ J) (x : X) :
    orderAt J x ≤ orderAt I x :=
  idealOrder_le_of_le (stalkIdeal_mono h x)

section
variable (I J : X.IdealSheafData) (x : X)

theorem orderAt_sup :
    orderAt (I ⊔ J) x = min (orderAt I x) (orderAt J x) := by
  rw [orderAt_eq_idealOrder, stalkIdeal_sup, idealOrder_sup]
  rfl

theorem add_orderAt_le_orderAt_mul :
    orderAt I x + orderAt J x ≤ orderAt (I * J) x := by
  rw [orderAt_eq_idealOrder (I * J), stalkIdeal_mul]
  exact add_idealOrder_le_idealOrder_mul (stalkIdeal I x) (stalkIdeal J x)


end

section
variable (I : X.IdealSheafData)

theorem mul_orderAt_le_orderAt_pow (c : ℕ) (x : X) :
    (c : ℕ∞) * orderAt I x ≤ orderAt (I ^ c) x := by
  rw [orderAt_eq_idealOrder (I ^ c), stalkIdeal_pow]
  exact mul_idealOrder_le_idealOrder_pow (stalkIdeal I x) c

theorem one_le_orderAt_iff_mem_support (x : X) :
    1 ≤ orderAt I x ↔ x ∈ I.support := by
  rw [orderAt_eq_idealOrder, one_le_idealOrder_iff, mem_support_iff_stalkIdeal_le_maximalIdeal]

theorem orderAt_eq_zero_iff_not_mem_support (x : X) :
    orderAt I x = 0 ↔ x ∉ I.support := by
  rw [orderAt_eq_idealOrder, idealOrder_eq_zero_iff,
    mem_support_iff_stalkIdeal_le_maximalIdeal]


end

section
variable [IsLocallyNoetherian X] (I : X.IdealSheafData) (x : X)

theorem orderAt_ne_top_of_stalkIdeal_ne_bot (h : stalkIdeal I x ≠ ⊥) : orderAt I x ≠ ⊤ := by
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  have hxU' : x ∈ U.1 := hxU
  have hnoeth : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let germAlgebra : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    (X.presheaf.germ U.1 x hxU').hom.toAlgebra
  have hloc : IsLocalization (U.2.primeIdealOf ⟨x, hxU'⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) := U.2.isLocalization_stalk ⟨x, hxU'⟩
  have : IsNoetherianRing (X.presheaf.stalk x) :=
    IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨x, hxU'⟩).asIdeal.primeCompl _ hnoeth
  rw [orderAt_eq_idealOrder]
  exact idealOrder_ne_top_of_ne_bot h

theorem orderAt_eq_top_iff :
    orderAt I x = ⊤ ↔ stalkIdeal I x = ⊥ := by
  constructor
  · intro h
    by_contra hne
    exact orderAt_ne_top_of_stalkIdeal_ne_bot I x hne h
  · intro h
    rw [orderAt_eq_idealOrder, h, idealOrder_bot]


end

theorem orderAt_eq_of_stalkIdeal_eq {I J : X.IdealSheafData} {x : X}
    (h : stalkIdeal I x = stalkIdeal J x) : orderAt I x = orderAt J x := by
  rw [orderAt_eq_idealOrder, orderAt_eq_idealOrder, h]

theorem orderAt_eq_one_iff (I : X.IdealSheafData) (x : X) :
    orderAt I x = 1 ↔
      stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
        ¬ stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2 := by
  constructor
  · intro h
    constructor
    · have ha : ((1 : ℕ) : ℕ∞) ≤ orderAt I x := by rw [h]; simp
      simpa using (le_orderAt_iff I x 1).mp ha
    · intro hle
      have h2 := (le_orderAt_iff I x 2).mpr hle
      rw [h] at h2
      have h3 : (2 : ℕ) ≤ 1 := by exact_mod_cast h2
      omega
  · rintro ⟨ha, hb⟩
    have ha' : ((1 : ℕ) : ℕ∞) ≤ orderAt I x := (le_orderAt_iff I x 1).mpr (by simpa using ha)
    have hb' : ¬ ((2 : ℕ) : ℕ∞) ≤ orderAt I x := fun hc => hb ((le_orderAt_iff I x 2).mp hc)
    rcases eq_or_ne (orderAt I x) ⊤ with htop | hfin
    · exact absurd (htop ▸ le_top) hb'
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
      rw [← hn] at ha' hb' ⊢
      have hn1 : 1 ≤ n := by exact_mod_cast ha'
      have hn2 : ¬ (2 ≤ n) := fun hc => hb' (by exact_mod_cast hc)
      have hn3 : n = 1 := by omega
      rw [hn3, Nat.cast_one]

private theorem maximalIdeal_not_le_sq_consolidated45 {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : IsLocalRing.maximalIdeal R ≠ ⊥) :
    ¬ IsLocalRing.maximalIdeal R ≤ IsLocalRing.maximalIdeal R ^ 2 := by
  intro hle
  refine h (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal R) (IsNoetherian.noetherian _) ?_ ?_)
  · rw [Ideal.smul_eq_mul, ← pow_two]
    exact hle
  · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge

theorem orderAt_eq_one_of_stalkIdeal_eq_maximalIdeal [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (x : X)
    (h : stalkIdeal I x = IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hne : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≠ ⊥) :
    orderAt I x = 1 := by
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  have hxU' : x ∈ U.1 := hxU
  have hnoeth : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let germAlgebra : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    (X.presheaf.germ U.1 x hxU').hom.toAlgebra
  have hloc : IsLocalization (U.2.primeIdealOf ⟨x, hxU'⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) := U.2.isLocalization_stalk ⟨x, hxU'⟩
  have : IsNoetherianRing (X.presheaf.stalk x) :=
    IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨x, hxU'⟩).asIdeal.primeCompl _ hnoeth
  rw [orderAt_eq_one_iff]
  refine ⟨h.le, ?_⟩
  rw [h]
  exact maximalIdeal_not_le_sq_consolidated45 hne

private theorem mem_of_vanishingIdeal_le_consolidated45 {R : Type*} [CommRing R]
    (W : Set (PrimeSpectrum R)) (hW : IsClosed W) (q : PrimeSpectrum R)
    (h : PrimeSpectrum.vanishingIdeal W ≤ q.asIdeal) : q ∈ W := by
  have h0 : q ∈ PrimeSpectrum.zeroLocus
      ((PrimeSpectrum.vanishingIdeal W : Ideal R) : Set R) :=
    (PrimeSpectrum.mem_zeroLocus _ _).mpr (fun y hy => h hy)
  rwa [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hW.closure_eq] at h0

private theorem map_algebraMap_eq_maximalIdeal_consolidated45 {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing S] (p : Ideal R) [p.IsPrime] [IsLocalization p.primeCompl S]
    (J : Ideal R) (hJ : J.IsRadical) (hJp : J ≤ p)
    (hmin : ∀ q : Ideal R, q.IsPrime → J ≤ q → q ≤ p → q = p) :
    Ideal.map (algebraMap R S) J = IsLocalRing.maximalIdeal S := by
  have hmap : Ideal.map (algebraMap R S) p = IsLocalRing.maximalIdeal S :=
    IsLocalization.AtPrime.map_eq_maximalIdeal ..
  have hcomap_le : Ideal.comap (algebraMap R S) (IsLocalRing.maximalIdeal S) ≤ p := by
    intro r hr
    by_contra hrp
    rw [Ideal.mem_comap] at hr
    have hrp' : r ∈ p.primeCompl := hrp
    have hunit : IsUnit (algebraMap R S r) := IsLocalization.map_units S ⟨r, hrp'⟩
    have hnu := (IsLocalRing.mem_maximalIdeal _).mp hr
    rw [mem_nonunits_iff] at hnu
    exact hnu hunit
  refine le_antisymm (le_trans (Ideal.map_mono hJp) (le_of_eq hmap)) ?_
  have hle : IsLocalRing.maximalIdeal S ≤ (Ideal.map (algebraMap R S) J).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hPle, hPprime⟩
    have : P.IsPrime := hPprime
    have hPmax : P ≤ IsLocalRing.maximalIdeal S := IsLocalRing.le_maximalIdeal hPprime.ne_top
    have h1 : Ideal.comap (algebraMap R S) P = p := by
      refine hmin _ (Ideal.comap_isPrime (algebraMap R S) P) ?_ ?_
      · rw [← Ideal.map_le_iff_le_comap]
        exact hPle
      · exact le_trans (Ideal.comap_mono hPmax) hcomap_le
    have heq : IsLocalRing.maximalIdeal S = P := by
      rw [← hmap, ← h1]
      exact IsLocalization.map_under p.primeCompl S P
    exact heq.le
  refine hle.trans ?_
  rw [← IsLocalization.map_radical p.primeCompl S J]
  exact Ideal.map_mono hJ

theorem stalkIdeal_vanishingIdeal_eq_maximalIdeal_of_isGenericPoint (Z : TopologicalSpace.Closeds X) (ξ : X)
    (T : Set X) (hT : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (Z : Set X)) T)
    (hξ : IsGenericPoint ξ T) :
    stalkIdeal (Scheme.IdealSheafData.vanishingIdeal Z) ξ
      = IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) := by
  obtain ⟨U, hxU0⟩ := X.exists_affineOpens_mem ξ
  have hxU : ξ ∈ U.1 := hxU0
  have hU : IsAffineOpen U.1 := U.2
  have hZcl : IsClosed (Z : Set X) := Z.2
  have hcont : Continuous (⇑(hU.fromSpec)) := (hU.fromSpec).continuous
  have hξT : ξ ∈ T := by
    rw [← hξ]
    exact subset_closure (Set.mem_singleton ξ)
  have hξZ : ξ ∈ (Z : Set X) := hT.1.2 hξT
  have hWclosed : IsClosed ((⇑hU.fromSpec ⁻¹' (Z : Set X)) : Set (PrimeSpectrum Γ(X, U.1))) :=
    hZcl.preimage hcont
  have hJdef : (Scheme.IdealSheafData.vanishingIdeal Z).ideal U
      = PrimeSpectrum.vanishingIdeal (⇑hU.fromSpec ⁻¹' (Z : Set X)) := rfl
  have hfp : (⇑(hU.fromSpec)) (hU.primeIdealOf ⟨ξ, hxU⟩) = ξ :=
    hU.fromSpec_primeIdealOf ⟨ξ, hxU⟩
  have hmemW : hU.primeIdealOf ⟨ξ, hxU⟩ ∈ (⇑(hU.fromSpec) ⁻¹' (Z : Set X)) := by
    show (⇑(hU.fromSpec)) (hU.primeIdealOf ⟨ξ, hxU⟩) ∈ (Z : Set X)
    rw [hfp]
    exact hξZ
  rw [stalkIdeal_eq_map_germ _ ξ U hxU, hJdef]
  let germAlgebra : Algebra Γ(X, U.1) (X.presheaf.stalk ξ) :=
    (X.presheaf.germ U.1 ξ hxU).hom.toAlgebra
  have hloc : IsLocalization (hU.primeIdealOf ⟨ξ, hxU⟩).asIdeal.primeCompl
      (X.presheaf.stalk ξ) := hU.isLocalization_stalk ⟨ξ, hxU⟩
  have halg : (X.presheaf.germ U.1 ξ hxU).hom
      = algebraMap Γ(X, U.1) (X.presheaf.stalk ξ) := rfl
  rw [halg]
  refine map_algebraMap_eq_maximalIdeal_consolidated45 (hU.primeIdealOf ⟨ξ, hxU⟩).asIdeal _
    (PrimeSpectrum.isRadical_vanishingIdeal _) ?_ ?_
  · intro f hf
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp hf _ hmemW
  · intro q hq hJq hqp
    have hQW : (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ∈
        ((⇑hU.fromSpec ⁻¹' (Z : Set X)) : Set (PrimeSpectrum Γ(X, U.1))) :=
      mem_of_vanishingIdeal_le_consolidated45 _ hWclosed ⟨q, hq⟩ hJq
    have hQP : (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ⤳ hU.primeIdealOf ⟨ξ, hxU⟩ := by
      rw [specializes_iff_mem_closure, PrimeSpectrum.closure_singleton,
        PrimeSpectrum.mem_zeroLocus]
      exact fun y hy => hqp hy
    have hzspec : (⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ⤳ ξ := by
      have hmapped := hQP.map hcont
      rwa [hfp] at hmapped
    have hzZ : (⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ∈ (Z : Set X) := hQW
    have hirr : IsIrreducible
        (closure {(⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))}) :=
      isIrreducible_singleton.closure
    have hsubZ : closure {(⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))} ⊆ (Z : Set X) :=
      hZcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hzZ)
    have hTsub : T ⊆ closure {(⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))} := by
      rw [← hξ]
      exact closure_minimal
        (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hzspec)) isClosed_closure
    have hmax := hT.2 ⟨hirr, hsubZ⟩ hTsub
    have hzT : (⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ∈ T :=
      hmax (subset_closure (Set.mem_singleton _))
    have hξz : ξ ⤳ (⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) :=
      specializes_iff_mem_closure.mpr (by rw [hξ]; exact hzT)
    have hind : Topology.IsInducing (⇑(hU.fromSpec)) :=
      (hU.fromSpec).isOpenEmbedding.toIsEmbedding.toIsInducing
    have h3 : (⇑(hU.fromSpec)) (hU.primeIdealOf ⟨ξ, hxU⟩) ⤳
        (⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) := by
      rw [hfp]
      exact hξz
    have hPQ : hU.primeIdealOf ⟨ξ, hxU⟩ ⤳ (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) :=
      hind.specializes_iff.mp h3
    have hpq : (hU.primeIdealOf ⟨ξ, hxU⟩).asIdeal ≤ q := by
      have h2 := specializes_iff_mem_closure.mp hPQ
      rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.mem_zeroLocus] at h2
      exact fun y hy => h2 hy
    exact le_antisymm hqp hpq

theorem orderAt_vanishingIdeal_eq_one [IsLocallyNoetherian X] (Z : TopologicalSpace.Closeds X)
    (ξ : X) (T : Set X) (hT : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (Z : Set X)) T)
    (hξ : IsGenericPoint ξ T)
    (hne : IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ≠ ⊥) :
    orderAt (Scheme.IdealSheafData.vanishingIdeal Z) ξ = 1 :=
  orderAt_eq_one_of_stalkIdeal_eq_maximalIdeal _ ξ
    (stalkIdeal_vanishingIdeal_eq_maximalIdeal_of_isGenericPoint Z ξ T hT hξ) hne

private theorem maximalIdeal_ne_bot_of_not_isField_consolidated45 {R : Type*} [CommRing R] [IsLocalRing R]
    (h : ¬ IsField R) : IsLocalRing.maximalIdeal R ≠ ⊥ :=
  fun hb => h (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hb)

theorem orderAt_vanishingIdeal_eq_one_of_not_isField [IsLocallyNoetherian X]
    (Z : TopologicalSpace.Closeds X) (ξ : X) (T : Set X)
    (hT : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (Z : Set X)) T)
    (hξ : IsGenericPoint ξ T)
    (hfield : ¬ IsField (X.presheaf.stalk ξ)) :
    orderAt (Scheme.IdealSheafData.vanishingIdeal Z) ξ = 1 :=
  orderAt_vanishingIdeal_eq_one Z ξ T hT hξ (maximalIdeal_ne_bot_of_not_isField_consolidated45 hfield)

section
variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (f : R →+* S) (g : S →+* R) (hgf : ∀ x, g (f x) = x) (hfg : ∀ x, f (g x) = x)
include hgf hfg

private theorem map_maximalIdeal_of_inverse_consolidated45 :
    Ideal.map f (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hx
    have h2 := hu.map g
    rwa [hgf] at h2
  · intro z hz
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz
    have hgz : g z ∈ IsLocalRing.maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply hz
      have h2 := hu.map f
      rwa [hfg] at h2
    have h3 : f (g z) ∈ Ideal.map f (IsLocalRing.maximalIdeal R) := Ideal.mem_map_of_mem _ hgz
    rwa [hfg] at h3

private theorem idealOrder_map_of_inverse_consolidated45 (J : Ideal R) :
    idealOrder (Ideal.map f J) = idealOrder J := by
  have hf := map_maximalIdeal_of_inverse_consolidated45 f g hgf hfg
  have hg := map_maximalIdeal_of_inverse_consolidated45 g f hfg hgf
  have h1 : idealOrder J ≤ idealOrder (Ideal.map f J) :=
    idealOrder_le_idealOrder_map f hf.le J
  have hcomp : g.comp f = RingHom.id R := RingHom.ext hgf
  have h2 : Ideal.map g (Ideal.map f J) = J := by
    rw [Ideal.map_map, hcomp, Ideal.map_id]
  have h3 : idealOrder (Ideal.map f J) ≤ idealOrder (Ideal.map g (Ideal.map f J)) :=
    idealOrder_le_idealOrder_map g hg.le (Ideal.map f J)
  rw [h2] at h3
  exact le_antisymm h3 h1


end

open CategoryTheory in
private theorem hom_hom_apply_of_comp_eq_consolidated45 {A B C : CommRingCat} (f : A ⟶ B) (g : B ⟶ C)
    (k : A ⟶ C) (hk : f ≫ g = k) (x : A) : g.hom (f.hom x) = k.hom x := by
  rw [← hk, CommRingCat.hom_comp]
  rfl

open CategoryTheory in
theorem orderAt_comap_of_isOpenImmersion {Y : Scheme.{u}} (h : Y ⟶ X) [IsOpenImmersion h]
    (I : X.IdealSheafData) (y : Y) :
    orderAt (I.comap h) y = orderAt I (h.base y) := by
  obtain ⟨U, sectionFrameQuotient⟩ := Y.exists_affineOpens_mem y
  have hyU : y ∈ U.1 := sectionFrameQuotient
  have hVaff : IsAffineOpen (h ''ᵁ U.1) := U.2.image_of_isOpenImmersion h
  have hxV : h.base y ∈ (h ''ᵁ U.1) := ⟨y, hyU, rfl⟩
  let appEquiv : Γ(X, h ''ᵁ U.1) ≃+* Γ(Y, U.1) := (h.appIso U.1).commRingCatIsoToRingEquiv
  have hid : (I.comap h).ideal U
      = Ideal.map ((h.appIso U.1).hom).hom (I.ideal ⟨h ''ᵁ U.1, hVaff⟩) := by
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I h U]
    exact Ideal.comap_symm appEquiv ..
  have key : (h.appIso U.1).inv ≫
        (h.app (h ''ᵁ U.1) ≫ Y.presheaf.germ (h ⁻¹ᵁ h ''ᵁ U.1) y hxV)
      = Y.presheaf.germ U.1 y hyU := by
    rw [← Category.assoc, Scheme.Hom.appIso_inv_app]
    exact Y.presheaf.germ_res _ y hxV
  have hcat : (h.appIso U.1).hom ≫ Y.presheaf.germ U.1 y hyU
      = X.presheaf.germ (h ''ᵁ U.1) (h.base y) hxV ≫ h.stalkMap y := by
    calc (h.appIso U.1).hom ≫ Y.presheaf.germ U.1 y hyU
        = (h.appIso U.1).hom ≫ ((h.appIso U.1).inv ≫
            (h.app (h ''ᵁ U.1) ≫ Y.presheaf.germ (h ⁻¹ᵁ h ''ᵁ U.1) y hxV)) := by rw [key]
      _ = h.app (h ''ᵁ U.1) ≫ Y.presheaf.germ (h ⁻¹ᵁ h ''ᵁ U.1) y hxV := by
          rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      _ = X.presheaf.germ (h ''ᵁ U.1) (h.base y) hxV ≫ h.stalkMap y :=
          (Scheme.Hom.germ_stalkMap h (h ''ᵁ U.1) y hxV).symm
  have hcomp : (Y.presheaf.germ U.1 y hyU).hom.comp ((h.appIso U.1).hom).hom
      = ((h.stalkMap y).hom).comp (X.presheaf.germ (h ''ᵁ U.1) (h.base y) hxV).hom := by
    have h4 := congrArg CommRingCat.Hom.hom hcat
    rwa [CommRingCat.hom_comp, CommRingCat.hom_comp] at h4
  have hsgf : ∀ x, ((inv (h.stalkMap y)).hom) ((h.stalkMap y).hom x) = x := fun x => by
    rw [hom_hom_apply_of_comp_eq_consolidated45 _ _ _ (IsIso.hom_inv_id (h.stalkMap y)) x, CommRingCat.hom_id]
    rfl
  have hsfg : ∀ x, ((h.stalkMap y).hom) ((inv (h.stalkMap y)).hom x) = x := fun x => by
    rw [hom_hom_apply_of_comp_eq_consolidated45 _ _ _ (IsIso.inv_hom_id (h.stalkMap y)) x, CommRingCat.hom_id]
    rfl
  rw [orderAt_eq_idealOrder, orderAt_eq_idealOrder,
    stalkIdeal_eq_map_germ (I.comap h) y U hyU,
    stalkIdeal_eq_map_germ I (h.base y) ⟨h ''ᵁ U.1, hVaff⟩ hxV, hid, Ideal.map_map, hcomp,
    ← Ideal.map_map]
  exact idealOrder_map_of_inverse_consolidated45 (h.stalkMap y).hom (inv (h.stalkMap y)).hom hsgf hsfg _

open CategoryTheory in
theorem orderAt_comap_of_isIso {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f] (J : B.IdealSheafData)
    (x : ↥A) : orderAt (J.comap f) x = orderAt J (f.base x) :=
  orderAt_comap_of_isOpenImmersion f J x

noncomputable def orderAtLeastLocus (I : X.IdealSheafData) (m : ℕ) : Set X :=
  {x : X | (m : ℕ∞) ≤ orderAt I x}

section
variable (I : X.IdealSheafData) (m : ℕ) (x : X)

theorem mem_orderAtLeastLocus_iff :
    x ∈ orderAtLeastLocus I m ↔ (m : ℕ∞) ≤ orderAt I x := Iff.rfl

theorem mem_orderAtLeastLocus_iff_stalkIdeal_le_maximalIdeal_pow :
    x ∈ orderAtLeastLocus I m ↔
      stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ m := by
  rw [mem_orderAtLeastLocus_iff, le_orderAt_iff]


end

section
variable (I : X.IdealSheafData)

theorem orderAtLeastLocus_zero : orderAtLeastLocus I 0 = Set.univ := by
  ext x
  simp [mem_orderAtLeastLocus_iff]

theorem mem_orderAtLeastLocus_one_iff (x : X) :
    x ∈ orderAtLeastLocus I 1 ↔ x ∈ I.support := by
  rw [mem_orderAtLeastLocus_iff, Nat.cast_one, one_le_orderAt_iff_mem_support]

theorem orderAtLeastLocus_one : orderAtLeastLocus I 1 = {x : X | x ∈ I.support} := by
  ext x
  exact mem_orderAtLeastLocus_one_iff I x


end

theorem orderAtLeastLocus_top_eq_empty (m : ℕ) (hm : 1 ≤ m) :
    orderAtLeastLocus (⊤ : X.IdealSheafData) m = ∅ := by
  ext x
  simp only [mem_orderAtLeastLocus_iff, Set.mem_empty_iff_false, iff_false, not_le, orderAt_top]
  have h : 0 < m := hm
  exact_mod_cast h

theorem orderAtLeastLocus_subset_of_le (I : X.IdealSheafData) {m m' : ℕ} (h : m ≤ m') :
    orderAtLeastLocus I m' ⊆ orderAtLeastLocus I m := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx ⊢
  refine le_trans ?_ hx
  exact_mod_cast h

theorem orderAtLeastLocus_subset_of_le_ideal {I J : X.IdealSheafData} (h : I ≤ J) (m : ℕ) :
    orderAtLeastLocus J m ⊆ orderAtLeastLocus I m := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx ⊢
  exact le_trans hx (orderAt_le_of_le h x)

theorem inter_orderAtLeastLocus_subset_orderAtLeastLocus_mul (I J : X.IdealSheafData) (m m' : ℕ) :
    orderAtLeastLocus I m ∩ orderAtLeastLocus J m' ⊆ orderAtLeastLocus (I * J) (m + m') := by
  rintro x ⟨hx, hx'⟩
  rw [mem_orderAtLeastLocus_iff] at hx hx' ⊢
  calc ((m + m' : ℕ) : ℕ∞) = (m : ℕ∞) + (m' : ℕ∞) := by push_cast; ring
    _ ≤ orderAt I x + orderAt J x := add_le_add hx hx'
    _ ≤ orderAt (I * J) x := add_orderAt_le_orderAt_mul I J x

theorem orderAtLeastLocus_subset_orderAtLeastLocus_pow (I : X.IdealSheafData) (c m : ℕ) :
    orderAtLeastLocus I m ⊆ orderAtLeastLocus (I ^ c) (c * m) := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx ⊢
  calc ((c * m : ℕ) : ℕ∞) = (c : ℕ∞) * (m : ℕ∞) := by push_cast; ring
    _ ≤ (c : ℕ∞) * orderAt I x := by gcongr
    _ ≤ orderAt (I ^ c) x := mul_orderAt_le_orderAt_pow I c x

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdeal
section

variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]

def tangentDerivations (P : Ideal S) : Submodule S (Derivation k S S) where
  carrier := {D : Derivation k S S | ∀ x ∈ P, D x ∈ P}
  add_mem' := by
    intro D D' hD hD' x hx
    have h := P.add_mem (hD x hx) (hD' x hx)
    simpa using h
  zero_mem' := by
    intro x _
    simp
  smul_mem' := by
    intro a D hD x hx
    have h := Ideal.mul_mem_left P a (hD x hx)
    simpa [smul_eq_mul] using h

section
variable (P : Ideal S)

theorem mem_tangentDerivations (D : Derivation k S S) :
    D ∈ tangentDerivations k P ↔ ∀ x ∈ P, D x ∈ P := Iff.rfl

theorem smul_mem_tangentDerivations {p : S} (hp : p ∈ P)
    (D : Derivation k S S) : p • D ∈ tangentDerivations k P := by
  rw [mem_tangentDerivations]
  intro x _
  have h := Ideal.mul_mem_right (D x) P hp
  simpa [smul_eq_mul] using h


end

theorem mem_tangentDerivations_span_singleton (x : S) (D : Derivation k S S) :
    D ∈ tangentDerivations k (Ideal.span ({x} : Set S)) ↔
      D x ∈ Ideal.span ({x} : Set S) := by
  rw [mem_tangentDerivations]
  constructor
  · intro hD
    exact hD x (Ideal.subset_span (Set.mem_singleton x))
  · intro hD y hy
    refine derivation_apply_mem_of_mem_span D le_rfl ?_ hy
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hD

def logDerivIdeal (P J : Ideal S) : Ideal S :=
  J ⊔ Ideal.span {x : S | ∃ D ∈ tangentDerivations k P, ∃ y ∈ J, D y = x}

section
variable (P J : Ideal S)

private theorem logDerivIdeal_eq_sup_span_consolidated38 :
    logDerivIdeal k P J =
      J ⊔ Ideal.span {x : S | ∃ D ∈ tangentDerivations k P, ∃ y ∈ J, D y = x} := rfl

theorem le_logDerivIdeal : J ≤ logDerivIdeal k P J := by
  rw [logDerivIdeal_eq_sup_span_consolidated38]
  exact le_sup_left

theorem derivation_apply_mem_logDerivIdeal (D : Derivation k S S)
    (hD : D ∈ tangentDerivations k P) {x : S} (hx : x ∈ J) :
    D x ∈ logDerivIdeal k P J := by
  rw [logDerivIdeal_eq_sup_span_consolidated38]
  exact Submodule.mem_sup_right (Ideal.subset_span ⟨D, hD, x, hx, rfl⟩)


end

theorem logDerivIdeal_le_iff (P J K : Ideal S) :
    logDerivIdeal k P J ≤ K ↔
      J ≤ K ∧ ∀ D ∈ tangentDerivations k P, ∀ x ∈ J, D x ∈ K := by
  rw [logDerivIdeal_eq_sup_span_consolidated38, sup_le_iff, Ideal.span_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun D hD x hx => h2 ⟨D, hD, x, hx, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro x ⟨D, hD, y, hy, rfl⟩
    exact h2 D hD y hy

section
variable (P : Ideal S)

theorem logDerivIdeal_mono : Monotone (logDerivIdeal k P : Ideal S → Ideal S) := by
  intro I J h
  rw [logDerivIdeal_le_iff]
  refine ⟨h.trans (le_logDerivIdeal k P J), fun D hD x hx => ?_⟩
  exact derivation_apply_mem_logDerivIdeal k P J D hD (h hx)

theorem logDerivIdeal_le_logDerivIdeal {I J : Ideal S} (h : I ≤ J) :
    logDerivIdeal k P I ≤ logDerivIdeal k P J :=
  logDerivIdeal_mono k P h


end

theorem logDerivIdeal_le_derivIdeal (P J : Ideal S) :
    logDerivIdeal k P J ≤ derivIdeal k J := by
  rw [logDerivIdeal_le_iff]
  refine ⟨le_derivIdeal k J, fun D _ x hx => ?_⟩
  exact derivation_apply_mem_derivIdeal k J D hx

theorem logDerivIdeal_top_eq_derivIdeal (J : Ideal S) :
    logDerivIdeal k (⊤ : Ideal S) J = derivIdeal k J := by
  refine le_antisymm (logDerivIdeal_le_derivIdeal k ⊤ J) ?_
  rw [derivIdeal_le_iff]
  refine ⟨le_logDerivIdeal k ⊤ J, fun D x hx => ?_⟩
  refine derivation_apply_mem_logDerivIdeal k ⊤ J D ?_ hx
  rw [mem_tangentDerivations]
  intro y _
  exact Submodule.mem_top

theorem logDerivIdeal_iSup_le {ι : Sort*} (P : Ideal S) (J : ι → Ideal S) :
    logDerivIdeal k P (⨆ i, J i) ≤ ⨆ i, logDerivIdeal k P (J i) := by
  rw [logDerivIdeal_le_iff]
  refine ⟨iSup_mono fun i => le_logDerivIdeal k P (J i), ?_⟩
  intro D hD x hx
  refine Submodule.iSup_induction
    (motive := fun z : S => D z ∈ ⨆ i, logDerivIdeal k P (J i)) J hx ?_ ?_ ?_
  · intro i y hy
    exact le_iSup (fun i => logDerivIdeal k P (J i)) i
      (derivation_apply_mem_logDerivIdeal k P (J i) D hD hy)
  · simpa only [map_zero] using Submodule.zero_mem (⨆ i, logDerivIdeal k P (J i))
  · intro a b ha hb
    simpa only [map_add] using Submodule.add_mem (⨆ i, logDerivIdeal k P (J i)) ha hb

def logDerivIdealIterate (P : Ideal S) : ℕ → Ideal S → Ideal S
  | 0, J => J
  | r + 1, J => logDerivIdeal k P (logDerivIdealIterate P r J)

theorem logDerivIdealIterate_zero (P J : Ideal S) : logDerivIdealIterate k P 0 J = J := rfl

section
variable (P : Ideal S)

theorem logDerivIdealIterate_succ (r : ℕ) (J : Ideal S) :
    logDerivIdealIterate k P (r + 1) J = logDerivIdeal k P (logDerivIdealIterate k P r J) := rfl

theorem logDerivIdealIterate_add (r s : ℕ) (J : Ideal S) :
    logDerivIdealIterate k P (r + s) J =
      logDerivIdealIterate k P r (logDerivIdealIterate k P s J) := by
  induction r with
  | zero => rw [Nat.zero_add, logDerivIdealIterate_zero]
  | succ r ih => rw [Nat.succ_add, logDerivIdealIterate_succ, logDerivIdealIterate_succ, ih]

theorem le_logDerivIdealIterate (r : ℕ) (J : Ideal S) :
    J ≤ logDerivIdealIterate k P r J := by
  induction r with
  | zero => exact (logDerivIdealIterate_zero k P J).ge
  | succ r ih =>
      rw [logDerivIdealIterate_succ]
      exact ih.trans (le_logDerivIdeal k P _)

theorem logDerivIdealIterate_mono (r : ℕ) :
    Monotone (logDerivIdealIterate k P r : Ideal S → Ideal S) := by
  induction r with
  | zero =>
      intro I J h
      rw [logDerivIdealIterate_zero, logDerivIdealIterate_zero]
      exact h
  | succ r ih =>
      intro I J h
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ]
      exact logDerivIdeal_mono k P (ih h)

theorem logDerivIdealIterate_le_of_le {r r' : ℕ} (h : r ≤ r') (J : Ideal S) :
    logDerivIdealIterate k P r J ≤ logDerivIdealIterate k P r' J := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm r d, logDerivIdealIterate_add]
  exact le_logDerivIdealIterate k P d _


end

theorem logDerivIdealIterate_top_eq_derivIdealIterate (r : ℕ) (J : Ideal S) :
    logDerivIdealIterate k (⊤ : Ideal S) r J = derivIdealIterate k r J := by
  induction r with
  | zero => rw [logDerivIdealIterate_zero, derivIdealIterate_zero]
  | succ r ih =>
      rw [logDerivIdealIterate_succ, derivIdealIterate_succ, ih, logDerivIdeal_top_eq_derivIdeal]

theorem logDerivIdealIterate_iSup_le {ι : Sort*} (P : Ideal S) (r : ℕ) (J : ι → Ideal S) :
    logDerivIdealIterate k P r (⨆ i, J i) ≤ ⨆ i, logDerivIdealIterate k P r (J i) := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
      rw [logDerivIdealIterate_succ]
      refine le_trans (logDerivIdeal_mono k P ih) ?_
      refine le_trans (logDerivIdeal_iSup_le k P fun i => logDerivIdealIterate k P r (J i)) ?_
      exact iSup_mono fun i => le_of_eq (logDerivIdealIterate_succ k P r (J i)).symm

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.TaylorExpansionComparison
section

section

variable {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]

private theorem exists_mul_deriv_pow_eq_pow_mul_consolidated42 {k : Type*} [CommRing k] {S : Type*}
    [CommRing S] [Algebra k S] (Δ : Derivation k S S) (b : S) (n : ℕ) :
    ∃ c : S, b * Δ (b ^ n) = b ^ n * c := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c + Δ b, ?_⟩
      have hbp : b ^ (m + 1) = b * b ^ m := by ring
      have hl : Δ (b * b ^ m) = b * Δ (b ^ m) + b ^ m * Δ b := by
        simp
      rw [hbp, hl]
      linear_combination b * hc

theorem pow_mul_iterate_deriv_mem_of_mul_derivIdeal_le (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (M J : Ideal S) (Δ : Derivation k S S) (b : S)
    (hMJ : M * derivIdeal k J ≤ J) (hb : b ∈ M) :
    ∀ (j : ℕ) (g : S), g ∈ J → b ^ j * (⇑Δ)^[j] g ∈ J := by
  intro j
  induction j with
  | zero =>
      intro g hg
      simpa using hg
  | succ j ih =>
      intro g hg
      have hIH : b ^ j * (⇑Δ)^[j] g ∈ J := ih g hg
      have hkey : b * Δ (b ^ j * (⇑Δ)^[j] g) ∈ J :=
        hMJ (Ideal.mul_mem_mul hb (derivation_apply_mem_derivIdeal k J Δ hIH))
      obtain ⟨c, hc⟩ := exists_mul_deriv_pow_eq_pow_mul_consolidated42 Δ b j
      have hleib : Δ (b ^ j * (⇑Δ)^[j] g)
          = b ^ j * Δ ((⇑Δ)^[j] g) + (⇑Δ)^[j] g * Δ (b ^ j) := by
        simp
      have hiter : (⇑Δ)^[j + 1] g = Δ ((⇑Δ)^[j] g) := Function.iterate_succ_apply' (⇑Δ) j g
      have hEq : b ^ (j + 1) * (⇑Δ)^[j + 1] g
          = b * Δ (b ^ j * (⇑Δ)^[j] g) - c * (b ^ j * (⇑Δ)^[j] g) := by
        rw [hiter, hleib]
        linear_combination (-((⇑Δ)^[j] g)) * hc
      rw [hEq]
      exact Submodule.sub_mem J hkey (Ideal.mul_mem_left J c hIH)

end

section

variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]

section
variable (σ : R →+* S) (D : Derivation A R R) (β : S)

theorem truncatedSeries_length_one (f : R) :
    TaylorExpansion.truncatedSeries σ D β 1 f = σ f := by
  simp [TaylorExpansion.truncatedSeries_apply]

theorem truncatedSeries_of_deriv_deriv_eq_zero (N : ℕ)
    (hN : 2 ≤ N) (f : R) (hf : D (D f) = 0) :
    TaylorExpansion.truncatedSeries σ D β N f = σ f + σ (D f) * β := by
  have h2 : (⇑D)^[2] f = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]
    simp [hf]
  have hvan : ∀ j : ℕ, 2 ≤ j → (⇑D)^[j] f = 0 := by
    intro j hj
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [Nat.add_comm, Function.iterate_add_apply, h2]
    exact Function.iterate_fixed (by simp) m
  have hsub : Finset.range 2 ⊆ Finset.range N := fun j hj =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hN)
  have hsum : ∑ j ∈ Finset.range 2,
        algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * β ^ j
      = ∑ j ∈ Finset.range N,
        algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * β ^ j := by
    refine Finset.sum_subset hsub ?_
    intro j _ hj
    have hj2 : 2 ≤ j := by
      rcases Nat.lt_or_ge j 2 with h | h
      · exact absurd (Finset.mem_range.mpr h) hj
      · exact h
    rw [hvan j hj2]
    simp
  rw [TaylorExpansion.truncatedSeries_apply, ← hsum]
  simp [Finset.sum_range_succ]


end

theorem truncatedSeries_mem_map {A R B : Type*} [CommRing A] [CommRing R] [CommRing B] [Algebra A R]
    [Algebra ℚ B] (φ : R →+* B) (D : Derivation A R R) (b : R) (J : Ideal R)
    (hstab : ∀ (j : ℕ) (g : R), g ∈ J → b ^ j * (⇑D)^[j] g ∈ J)
    (N : ℕ) (g : R) (hg : g ∈ J) :
    TaylorExpansion.truncatedSeries φ D (φ b) N g ∈ Ideal.map φ J := by
  rw [TaylorExpansion.truncatedSeries_apply]
  refine Ideal.sum_mem _ fun j _ => ?_
  have h : φ (b ^ j * (⇑D)^[j] g) ∈ Ideal.map φ J :=
    Ideal.mem_map_of_mem φ (hstab j g hg)
  rw [map_mul, map_pow] at h
  have h2 := Ideal.mul_mem_left (Ideal.map φ J) (algebraMap ℚ B ((j.factorial : ℚ)⁻¹)) h
  have h3 : algebraMap ℚ B ((j.factorial : ℚ)⁻¹) * φ ((⇑D)^[j] g) * φ b ^ j
      = algebraMap ℚ B ((j.factorial : ℚ)⁻¹) * (φ b ^ j * φ ((⇑D)^[j] g)) := by
    ring
  rw [h3]
  exact h2

end

section

open IsLocalRing

def IsTaylorExpansionOn (P : Type*) [CommRing P] {A R B : Type*} [CommRing A] [CommRing R]
    [CommRing B] [Algebra P R] [Algebra A R] [IsLocalRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ x : P,
    TaylorExpansion.truncatedSeries φ D β N (algebraMap P R x) - φ' (algebraMap P R x) ∈ maximalIdeal B ^ N

theorem isTaylorExpansionOn_mvPolynomial {k : Type*} [CommRing k] {ι : Type*}
    {A R B : Type*} [CommRing A] [CommRing R] [CommRing B]
    [Algebra (MvPolynomial ι k) R] [Algebra A R] [IsLocalRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hβ : β ∈ maximalIdeal B)
    (hconst : ∀ c : k,
      φ (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) =
        φ' (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)))
    (hDconst : ∀ c : k, D (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) = 0)
    (hvar : ∀ (i : ι) (N : ℕ), 1 ≤ N →
      TaylorExpansion.truncatedSeries φ D β N (algebraMap (MvPolynomial ι k) R (MvPolynomial.X i)) -
          φ' (algebraMap (MvPolynomial ι k) R (MvPolynomial.X i)) ∈ maximalIdeal B ^ N) :
    IsTaylorExpansionOn (MvPolynomial ι k) φ φ' D β := by
  intro N hN x
  have hβN : β ^ N ∈ maximalIdeal B ^ N := Ideal.pow_mem_pow hβ N
  have key :
      (TaylorExpansion.truncatedSeriesRingHom φ D β N (maximalIdeal B ^ N) hN hβN).comp
          (algebraMap (MvPolynomial ι k) R) =
        ((Ideal.Quotient.mk (maximalIdeal B ^ N)).comp φ').comp
          (algebraMap (MvPolynomial ι k) R) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have h1 : TaylorExpansion.truncatedSeries φ D β N
            (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c))
          = φ' (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) := by
        rw [TaylorExpansion.truncatedSeries_of_deriv_eq_zero φ D β N hN
          (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) (hDconst c)]
        exact hconst c
      simp only [RingHom.coe_comp, Function.comp_apply, TaylorExpansion.truncatedSeriesRingHom_apply, h1]
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply, TaylorExpansion.truncatedSeriesRingHom_apply]
      exact Ideal.Quotient.eq.2 (hvar i N hN)
  have h := RingHom.congr_fun key x
  simp only [RingHom.coe_comp, Function.comp_apply, TaylorExpansion.truncatedSeriesRingHom_apply] at h
  exact Ideal.Quotient.eq.1 h

private theorem derivation_apply_eq_zero_of_formallyUnramified_consolidated42 {P R : Type*} [CommRing P]
    [CommRing R] [Algebra P R] [Algebra.FormallyUnramified P R] {M : Type*} [AddCommGroup M]
    [Module P M] [Module R M] [IsScalarTower P R M] (d : Derivation P R M) (x : R) : d x = 0 := by
  have h0 : KaehlerDifferential.D P R x = 0 := Subsingleton.elim _ _
  have h1 : (Derivation.liftKaehlerDifferential d) (KaehlerDifferential.D P R x) = d x :=
    Derivation.liftKaehlerDifferential_comp_D d x
  rw [h0, map_zero] at h1
  exact h1.symm

private theorem sub_mem_pow_succ_of_sub_mem_pow_consolidated42 (P : Type*) {R B : Type*} [CommRing P] [CommRing R]
    [CommRing B] [Algebra P R] [Algebra.FormallyUnramified P R]
    (φ' : R →+* B) (m : Ideal B) (T : R → B) (k : ℕ) (hk : 1 ≤ k)
    (hadd : ∀ x y : R, T (x + y) = T x + T y)
    (hone : T 1 = 1)
    (hmul : ∀ x y : R, T (x * y) - T x * T y ∈ m ^ (k + 1))
    (hP : ∀ x : P, T (algebraMap P R x) - φ' (algebraMap P R x) ∈ m ^ (k + 1))
    (hind : ∀ x : R, T x - φ' x ∈ m ^ k) (x : R) :
    T x - φ' x ∈ m ^ (k + 1) := by
  let _ : Algebra R B := φ'.toAlgebra
  let _ : Algebra P B := (φ'.comp (algebraMap P R)).toAlgebra
  have : IsScalarTower P R B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower P R (B ⧸ m ^ (k + 1)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hleib : ∀ a b : R,
      T (a * b) - φ' (a * b) - (φ' a * (T b - φ' b) + φ' b * (T a - φ' a)) ∈ m ^ (k + 1) := by
    intro a b
    have h1 : T (a * b) - T a * T b ∈ m ^ (k + 1) := hmul a b
    have h2 : (T a - φ' a) * (T b - φ' b) ∈ m ^ (k + 1) := by
      have h3 : (T a - φ' a) * (T b - φ' b) ∈ m ^ k * m ^ k :=
        Ideal.mul_mem_mul (hind a) (hind b)
      have h4 : m ^ k * m ^ k ≤ m ^ (k + 1) := by
        rw [← pow_add]
        exact Ideal.pow_le_pow_right (by omega)
      exact h4 h3
    have heq : T (a * b) - φ' (a * b) - (φ' a * (T b - φ' b) + φ' b * (T a - φ' a))
        = T (a * b) - T a * T b + (T a - φ' a) * (T b - φ' b) := by
      rw [map_mul]
      ring
    rw [heq]
    exact Ideal.add_mem _ h1 h2
  let d : Derivation P R (B ⧸ m ^ (k + 1)) :=
    { toFun := fun y => Ideal.Quotient.mk (m ^ (k + 1)) (T y - φ' y)
      map_add' := by
        intro a b
        show Ideal.Quotient.mk (m ^ (k + 1)) (T (a + b) - φ' (a + b))
            = Ideal.Quotient.mk (m ^ (k + 1)) (T a - φ' a)
              + Ideal.Quotient.mk (m ^ (k + 1)) (T b - φ' b)
        have harg : T (a + b) - φ' (a + b) = T a - φ' a + (T b - φ' b) := by
          rw [hadd, map_add]
          ring
        rw [harg, map_add]
      map_smul' := by
        intro p a
        show Ideal.Quotient.mk (m ^ (k + 1)) (T (p • a) - φ' (p • a))
            = p • Ideal.Quotient.mk (m ^ (k + 1)) (T a - φ' a)
        simp only [Algebra.smul_def]
        have halg : (algebraMap P (B ⧸ m ^ (k + 1))) p
            = Ideal.Quotient.mk (m ^ (k + 1)) (φ' (algebraMap P R p)) := rfl
        rw [halg, ← map_mul]
        refine Ideal.Quotient.eq.mpr ?_
        have h1 := hleib (algebraMap P R p) a
        have h2 : φ' a * (T (algebraMap P R p) - φ' (algebraMap P R p)) ∈ m ^ (k + 1) :=
          Ideal.mul_mem_left _ _ (hP p)
        have h3 := Ideal.add_mem _ h1 h2
        have heq : T (algebraMap P R p * a) - φ' (algebraMap P R p * a)
              - (φ' (algebraMap P R p) * (T a - φ' a)
                + φ' a * (T (algebraMap P R p) - φ' (algebraMap P R p)))
              + φ' a * (T (algebraMap P R p) - φ' (algebraMap P R p))
            = T (algebraMap P R p * a) - φ' (algebraMap P R p * a)
              - φ' (algebraMap P R p) * (T a - φ' a) := by
          ring
        rw [heq] at h3
        exact h3
      map_one_eq_zero' := by
        show Ideal.Quotient.mk (m ^ (k + 1)) (T 1 - φ' 1) = 0
        rw [hone, map_one, sub_self, map_zero]
      leibniz' := by
        intro a b
        show Ideal.Quotient.mk (m ^ (k + 1)) (T (a * b) - φ' (a * b))
            = a • Ideal.Quotient.mk (m ^ (k + 1)) (T b - φ' b)
              + b • Ideal.Quotient.mk (m ^ (k + 1)) (T a - φ' a)
        simp only [Algebra.smul_def]
        have halg : ∀ y : R, (algebraMap R (B ⧸ m ^ (k + 1))) y
            = Ideal.Quotient.mk (m ^ (k + 1)) (φ' y) := fun _ => rfl
        rw [halg a, halg b, ← map_mul, ← map_mul, ← map_add]
        exact Ideal.Quotient.eq.mpr (hleib a b) }
  have hdx : Ideal.Quotient.mk (m ^ (k + 1)) (T x - φ' x) = 0 :=
    derivation_apply_eq_zero_of_formallyUnramified_consolidated42 d x
  exact Ideal.Quotient.eq_zero_iff_mem.mp hdx

section
variable (P : Type*) [CommRing P] {A R B : Type*} [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R] [Algebra.FormallyUnramified P R] [IsLocalRing B] [Algebra ℚ B] (φ φ' : R →+* B) (D : Derivation A R R) (β : B) (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B) (hβ : β ∈ maximalIdeal B) (hrep : IsTaylorExpansionOn P φ φ' D β)
include hcong hβ hrep

theorem truncatedSeries_sub_mem_maximalIdeal_pow (N : ℕ) (hN : 1 ≤ N) (f : R) :
    TaylorExpansion.truncatedSeries φ D β N f - φ' f ∈ maximalIdeal B ^ N := by
  have hβN : β ^ N ∈ maximalIdeal B ^ N := Ideal.pow_mem_pow hβ N
  have hmulN : ∀ x y : R,
      TaylorExpansion.truncatedSeries φ D β N (x * y)
        - TaylorExpansion.truncatedSeries φ D β N x * TaylorExpansion.truncatedSeries φ D β N y
        ∈ maximalIdeal B ^ N :=
    fun x y => TaylorExpansion.truncatedSeries_mul_sub_mem φ D β N (maximalIdeal B ^ N) hβN x y
  have hbound : ∀ x : P,
      TaylorExpansion.truncatedSeries φ D β N (algebraMap P R x) - φ' (algebraMap P R x)
        ∈ maximalIdeal B ^ N := fun x => hrep N hN x
  have hbase : ∀ x : R, TaylorExpansion.truncatedSeries φ D β N x - φ' x ∈ maximalIdeal B ^ 1 := by
    intro x
    rw [pow_one]
    have h1 : TaylorExpansion.truncatedSeries φ D β N x - φ x ∈ Ideal.span ({β} : Set B) :=
      TaylorExpansion.truncatedSeries_sub_mem_span_singleton φ D β N hN x
    have h2 : Ideal.span ({β} : Set B) ≤ maximalIdeal B := by
      rw [Ideal.span_le]
      simpa using hβ
    have h4 : TaylorExpansion.truncatedSeries φ D β N x - φ' x
        = TaylorExpansion.truncatedSeries φ D β N x - φ x + (φ x - φ' x) := by ring
    rw [h4]
    exact Ideal.add_mem _ (h2 h1) (hcong x)
  have key : ∀ k : ℕ, 1 ≤ k → k ≤ N →
      ∀ x : R, TaylorExpansion.truncatedSeries φ D β N x - φ' x ∈ maximalIdeal B ^ k := by
    intro k
    induction k with
    | zero => intro h; exact absurd h (by omega)
    | succ k ih =>
      intro _ hkN
      rcases Nat.eq_zero_or_pos k with hk0 | hk1
      · subst hk0
        exact hbase
      · have hk1' : 1 ≤ k := hk1
        have hkle : maximalIdeal B ^ N ≤ maximalIdeal B ^ (k + 1) :=
          Ideal.pow_le_pow_right hkN
        exact fun x =>
          sub_mem_pow_succ_of_sub_mem_pow_consolidated42 P φ' (maximalIdeal B) (TaylorExpansion.truncatedSeries φ D β N) k hk1'
            (fun a b => TaylorExpansion.truncatedSeries_add φ D β N a b)
            (TaylorExpansion.truncatedSeries_one φ D β N hN)
            (fun a b => hkle (hmulN a b))
            (fun p => hkle (hbound p))
            (ih hk1' (by omega)) x
  exact key N hN le_rfl f

theorem sub_mem_span_sup_maximalIdeal_pow (N : ℕ) (hN : 1 ≤ N) (f : R) :
    φ f - φ' f ∈ Ideal.span ({β} : Set B) ⊔ maximalIdeal B ^ N := by
  have h1 : TaylorExpansion.truncatedSeries φ D β N f - φ f ∈ Ideal.span ({β} : Set B) :=
    TaylorExpansion.truncatedSeries_sub_mem_span_singleton φ D β N hN f
  have h2 : TaylorExpansion.truncatedSeries φ D β N f - φ' f ∈ maximalIdeal B ^ N :=
    truncatedSeries_sub_mem_maximalIdeal_pow P φ φ' D β hcong hβ hrep N hN f
  have hEq : φ f - φ' f
      = (TaylorExpansion.truncatedSeries φ D β N f - φ' f) - (TaylorExpansion.truncatedSeries φ D β N f - φ f) := by
    ring
  rw [hEq]
  exact Submodule.sub_mem _ (Submodule.mem_sup_right h2) (Submodule.mem_sup_left h1)

theorem sub_mem_iInf_span_sup_maximalIdeal_pow (f : R) :
    φ f - φ' f ∈ ⨅ N : ℕ, (Ideal.span ({β} : Set B) ⊔ maximalIdeal B ^ N) := by
  refine Submodule.mem_iInf _ |>.2 ?_
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : (Ideal.span ({β} : Set B) ⊔ maximalIdeal B ^ 0) = ⊤ := by
      rw [pow_zero, Ideal.one_eq_top, sup_top_eq]
    rw [h0]
    exact Submodule.mem_top
  · exact sub_mem_span_sup_maximalIdeal_pow P φ φ' D β hcong hβ hrep N hN f


end

private theorem mem_of_forall_mem_sup_maximalIdeal_pow_consolidated42 {B : Type*} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] (J : Ideal B) (hJ : J ≤ IsLocalRing.maximalIdeal B) (x : B)
    (hx : ∀ N : ℕ, x ∈ J ⊔ IsLocalRing.maximalIdeal B ^ N) : x ∈ J := by
  have hmne : IsLocalRing.maximalIdeal B ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal B).ne_top
  have hJne : J ≠ ⊤ := by
    intro h
    apply hmne
    rw [eq_top_iff]
    rw [h] at hJ
    exact hJ
  have : Nontrivial (B ⧸ J) := by
    refine ⟨0, 1, fun h => hJne ?_⟩
    rw [Ideal.eq_top_iff_one]
    refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [map_one]
    exact h.symm
  have : IsLocalRing (B ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hIne : Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B) ≠ ⊤ := by
    intro h
    have h1 : (1 : B ⧸ J) ∈ Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B) := by
      rw [h]
      exact Submodule.mem_top
    obtain ⟨y, hy, hy1⟩ :=
      (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).1 h1
    have h2 : (1 : B) - y ∈ J := by
      refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
      rw [map_sub, hy1, map_one, sub_self]
    have h3 : (1 : B) ∈ IsLocalRing.maximalIdeal B := by
      have h4 := Submodule.add_mem (IsLocalRing.maximalIdeal B) (hJ h2) hy
      simp at h4
    exact hmne ((Ideal.eq_top_iff_one _).2 h3)
  have hbot : (⨅ i : ℕ,
      (Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B)) ^ i) = ⊥ := by
    apply Ideal.iInf_pow_eq_bot_of_isLocalRing
    exact hIne
  have hmem : ∀ N : ℕ, Ideal.Quotient.mk J x ∈
      (Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B)) ^ N := by
    intro N
    obtain ⟨j, hj, y, hy, hxy⟩ := Submodule.mem_sup.1 (hx N)
    have hxe : Ideal.Quotient.mk J x = Ideal.Quotient.mk J y := by
      rw [← hxy, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add]
    rw [hxe]
    exact (Ideal.map_pow (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B) N).le
      (Ideal.mem_map_of_mem _ hy)
  have hfin : Ideal.Quotient.mk J x ∈
      (⨅ i : ℕ, (Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B)) ^ i) :=
    (Submodule.mem_iInf _).2 hmem
  rw [hbot, Ideal.mem_bot] at hfin
  exact Ideal.Quotient.eq_zero_iff_mem.1 hfin

section
variable (P : Type*) [CommRing P] {A R B : Type*} [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R] [Algebra.FormallyUnramified P R] [IsLocalRing B] [IsNoetherianRing B] [Algebra ℚ B] (φ φ' : R →+* B) (D : Derivation A R R) (β : B)

theorem sub_mem_span_singleton_of_isTaylorExpansionOn (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (f : R) :
    φ f - φ' f ∈ Ideal.span ({β} : Set B) := by
  have h := sub_mem_iInf_span_sup_maximalIdeal_pow P φ φ' D β hcong hβ hrep f
  have hall : ∀ N : ℕ, φ f - φ' f ∈ Ideal.span ({β} : Set B) ⊔ maximalIdeal B ^ N :=
    (Submodule.mem_iInf _).1 h
  exact mem_of_forall_mem_sup_maximalIdeal_pow_consolidated42 (Ideal.span ({β} : Set B))
    (Ideal.span_le.2 (Set.singleton_subset_iff.2 hβ)) (φ f - φ' f) hall

theorem sub_mem_of_isTaylorExpansionOn (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (I : Ideal B) (hI : β ∈ I) (f : R) :
    φ f - φ' f ∈ I := by
  have hmem : φ f - φ' f ∈ Ideal.span ({β} : Set B) :=
    sub_mem_span_singleton_of_isTaylorExpansionOn P φ φ' D β hcong hβ hrep f
  have hle : Ideal.span ({β} : Set B) ≤ I :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hI)
  exact hle hmem

theorem map_le_map_of_pow_mul_iterate_deriv_mem (b : R) (J : Ideal R)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (hb : φ b = β)
    (hstab : ∀ (j : ℕ) (g : R), g ∈ J → b ^ j * (⇑D)^[j] g ∈ J) :
    Ideal.map φ' J ≤ Ideal.map φ J := by
  refine Ideal.map_le_iff_le_comap.mpr fun g hg => ?_
  refine Ideal.mem_comap.mpr ?_
  by_cases htop : Ideal.map φ J = ⊤
  · rw [htop]
    exact Submodule.mem_top
  · refine mem_of_forall_mem_sup_maximalIdeal_pow_consolidated42 (Ideal.map φ J)
      (IsLocalRing.le_maximalIdeal htop) (φ' g) ?_
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [pow_zero, Ideal.one_eq_top, sup_top_eq]
      exact Submodule.mem_top
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have h1 : TaylorExpansion.truncatedSeries φ D β n g ∈ Ideal.map φ J := by
        have hmem := truncatedSeries_mem_map φ D b J hstab n g hg
        rwa [hb] at hmem
      have h2 : TaylorExpansion.truncatedSeries φ D β n g - φ' g ∈ maximalIdeal B ^ n :=
        truncatedSeries_sub_mem_maximalIdeal_pow P φ φ' D β hcong hβ hrep n hn1 g
      have hEq : φ' g = TaylorExpansion.truncatedSeries φ D β n g - (TaylorExpansion.truncatedSeries φ D β n g - φ' g) := by
        ring
      rw [hEq]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)


end

end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealFieldExtension
section
namespace DerivIdealBaseChange

open FunctorialResolution.EmbeddedResolution.EtaleCoordinates

private theorem apply_mem_of_forall_partialDeriv_mem_consolidated72 {k : Type*} [CommRing k] {ι : Type*} [Finite ι]
    {S : Type*} [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (X : Set S) (K : Ideal S)
    (h : ∀ i : ι, ∀ x ∈ X, partialDeriv k ι S i x ∈ K)
    (D : Derivation k S S) {x : S} (hx : x ∈ X) : D x ∈ K := by
  classical
  let N : Submodule S (Derivation k S S) :=
    { carrier := {D : Derivation k S S | ∀ y ∈ X, D y ∈ K}
      add_mem' := by
        intro a b ha hb
        show ∀ y ∈ X, (a + b) y ∈ K
        intro y hy
        have hab : (a + b) y = a y + b y := rfl
        rw [hab]
        exact Ideal.add_mem K (ha y hy) (hb y hy)
      zero_mem' := by
        show ∀ y ∈ X, (0 : Derivation k S S) y ∈ K
        intro y _
        have h0 : (0 : Derivation k S S) y = 0 := rfl
        rw [h0]
        exact Ideal.zero_mem K
      smul_mem' := by
        intro c a ha
        show ∀ y ∈ X, (c • a) y ∈ K
        intro y hy
        have hc : (c • a) y = c * a y := rfl
        rw [hc]
        exact Ideal.mul_mem_left K _ (ha y hy) }
  have hspan : (⊤ : Submodule S (Derivation k S S)) ≤ N := by
    rw [← span_range_partialDeriv k ι S, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  have hDN : D ∈ N := hspan Submodule.mem_top
  exact hDN x hx

section

variable (k : Type*) [CommRing k] (L : Type*) [CommRing L] [Algebra k L]
  (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S' : Type*) [CommRing S'] [Algebra L S'] [Algebra (MvPolynomial ι L) S']
  [IsScalarTower L (MvPolynomial ι L) S'] [Algebra.FormallyEtale (MvPolynomial ι L) S']
  [Algebra k S'] [IsScalarTower k L S']

theorem partialDeriv_algHom_apply (φ : S →ₐ[k] S')
    (hφ : ∀ i : ι, φ (coord k ι S i) = coord L ι S' i) (i : ι) (f : S) :
    partialDeriv L ι S' i (φ f) = φ (partialDeriv k ι S i f) := by
  let _ : Algebra S S' := φ.toRingHom.toAlgebra
  have htow : IsScalarTower k S S' := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have hsmul : ∀ (s : S) (x : S'), s • x = φ s * x := fun _ _ => rfl
  have hφsmul : ∀ (c : k) (x : S), φ (c • x) = c • φ x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, φ.commutes]
  have hcomp : ∀ (c : k) (y : S'), c • y = (algebraMap k L c) • y := by
    intro c y
    rw [Algebra.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply k L S']
  have hadd1 : ∀ x y : S', partialDeriv L ι S' i (x + y)
      = partialDeriv L ι S' i x + partialDeriv L ι S' i y :=
    fun x y => (partialDeriv L ι S' i).toLinearMap.map_add x y
  have hadd2 : ∀ x y : S, partialDeriv k ι S i (x + y)
      = partialDeriv k ι S i x + partialDeriv k ι S i y :=
    fun x y => (partialDeriv k ι S i).toLinearMap.map_add x y
  have hsm1 : ∀ (c : L) (y : S'), partialDeriv L ι S' i (c • y) = c • partialDeriv L ι S' i y :=
    fun c y => (partialDeriv L ι S' i).toLinearMap.map_smul c y
  have hsm2 : ∀ (c : k) (x : S), partialDeriv k ι S i (c • x) = c • partialDeriv k ι S i x :=
    fun c x => (partialDeriv k ι S i).toLinearMap.map_smul c x
  have hpsmul : ∀ (c : k) (y : S'),
      partialDeriv L ι S' i (c • y) = c • partialDeriv L ι S' i y := by
    intro c y
    rw [hcomp c y, hsm1, ← hcomp]
  let F₁ : S →ₗ[k] S' :=
    { toFun := fun s => partialDeriv L ι S' i (φ s)
      map_add' := by
        intro x y
        show partialDeriv L ι S' i (φ (x + y))
            = partialDeriv L ι S' i (φ x) + partialDeriv L ι S' i (φ y)
        rw [map_add, hadd1]
      map_smul' := by
        intro c x
        show partialDeriv L ι S' i (φ (c • x)) = c • partialDeriv L ι S' i (φ x)
        rw [hφsmul, hpsmul] }
  let F₂ : S →ₗ[k] S' :=
    { toFun := fun s => φ (partialDeriv k ι S i s)
      map_add' := by
        intro x y
        show φ (partialDeriv k ι S i (x + y))
            = φ (partialDeriv k ι S i x) + φ (partialDeriv k ι S i y)
        rw [hadd2, map_add]
      map_smul' := by
        intro c x
        show φ (partialDeriv k ι S i (c • x)) = c • φ (partialDeriv k ι S i x)
        rw [hsm2, hφsmul] }
  let D₁ : Derivation k S S' := Derivation.mk' F₁ (by
    intro a b
    show partialDeriv L ι S' i (φ (a * b))
        = a • partialDeriv L ι S' i (φ b) + b • partialDeriv L ι S' i (φ a)
    rw [map_mul, (partialDeriv L ι S' i).leibniz]
    simp only [hsmul, smul_eq_mul])
  let D₂ : Derivation k S S' := Derivation.mk' F₂ (by
    intro a b
    show φ (partialDeriv k ι S i (a * b))
        = a • φ (partialDeriv k ι S i b) + b • φ (partialDeriv k ι S i a)
    rw [(partialDeriv k ι S i).leibniz]
    simp only [hsmul, smul_eq_mul, map_add, map_mul])
  have hcoords : ∀ j : ι, D₁ (coord k ι S j) = D₂ (coord k ι S j) := by
    intro j
    show partialDeriv L ι S' i (φ (coord k ι S j)) = φ (partialDeriv k ι S i (coord k ι S j))
    rw [hφ j, partialDeriv_coord, partialDeriv_coord]
    split_ifs with hij
    · exact (map_one φ).symm
    · exact (map_zero φ).symm
  have hD : D₁ = D₂ := derivation_ext_of_coord k ι S S' D₁ D₂ hcoords
  exact DFunLike.congr_fun hD f

theorem map_derivIdeal_le [Fintype ι] (φ : S →ₐ[k] S')
    (hφ : ∀ i : ι, φ (coord k ι S i) = coord L ι S' i) (J : Ideal S) :
    Ideal.map φ (derivIdeal k J) ≤ derivIdeal L (Ideal.map φ J) := by
  rw [Ideal.map_le_iff_le_comap, derivIdeal_le_iff]
  constructor
  · intro y hy
    rw [Ideal.mem_comap]
    exact le_derivIdeal L (Ideal.map φ J) (Ideal.mem_map_of_mem φ hy)
  · intro D x hx
    have key : ∀ i : ι, ∀ y ∈ (J : Set S),
        partialDeriv k ι S i y ∈ Ideal.comap φ (derivIdeal L (Ideal.map φ J)) := by
      intro i y hy
      rw [Ideal.mem_comap,
        ← partialDeriv_algHom_apply (k := k) (L := L) (ι := ι) (S := S) (S' := S') φ hφ i y]
      exact derivation_apply_mem_derivIdeal L (Ideal.map φ J) (partialDeriv L ι S' i)
        (Ideal.mem_map_of_mem φ (show y ∈ J from hy))
    exact apply_mem_of_forall_partialDeriv_mem_consolidated72 (ι := ι) (J : Set S)
      (Ideal.comap φ (derivIdeal L (Ideal.map φ J))) key D (show x ∈ (J : Set S) from hx)

theorem partialDeriv_mem_map_derivIdeal (φ : S →ₐ[k] S')
    (hφ : ∀ i : ι, φ (coord k ι S i) = coord L ι S' i) (i : ι) (J : Ideal S)
    {g : S'} (hg : g ∈ Ideal.map φ J) :
    partialDeriv L ι S' i g ∈ Ideal.map φ (derivIdeal k J) := by
  have hle : Ideal.map φ J ≤ Ideal.span (⇑φ '' (J : Set S)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap]
    exact Ideal.subset_span ⟨y, hy, rfl⟩
  have hGT : Ideal.span (⇑φ '' (J : Set S)) ≤ Ideal.map φ (derivIdeal k J) := by
    rw [Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact Ideal.mem_map_of_mem φ (le_derivIdeal k J (show y ∈ J from hy))
  have hD : ∀ z ∈ (⇑φ '' (J : Set S)),
      partialDeriv L ι S' i z ∈ Ideal.map φ (derivIdeal k J) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [partialDeriv_algHom_apply (k := k) (L := L) (ι := ι) (S := S) (S' := S') φ hφ i y]
    exact Ideal.mem_map_of_mem φ
      (derivation_apply_mem_derivIdeal k J (partialDeriv k ι S i) (show y ∈ J from hy))
  exact derivation_apply_mem_of_mem_span (partialDeriv L ι S' i) hGT hD (hle hg)

section
variable [Fintype ι] (φ : S →ₐ[k] S') (hφ : ∀ i : ι, φ (coord k ι S i) = coord L ι S' i) (J : Ideal S)
include hφ

theorem derivIdeal_map_le :
    derivIdeal L (Ideal.map φ J) ≤ Ideal.map φ (derivIdeal k J) := by
  rw [derivIdeal_le_iff]
  refine ⟨Ideal.map_mono (le_derivIdeal k J), ?_⟩
  intro D g hg
  have key : ∀ i : ι, ∀ y ∈ ((Ideal.map φ J : Ideal S') : Set S'),
      partialDeriv L ι S' i y ∈ Ideal.map φ (derivIdeal k J) := by
    intro i y hy
    exact partialDeriv_mem_map_derivIdeal (k := k) (L := L) (ι := ι) (S := S) (S' := S')
      φ hφ i J (show y ∈ Ideal.map φ J from hy)
  exact apply_mem_of_forall_partialDeriv_mem_consolidated72 (ι := ι) ((Ideal.map φ J : Ideal S') : Set S')
    (Ideal.map φ (derivIdeal k J)) key D
    (show g ∈ ((Ideal.map φ J : Ideal S') : Set S') from hg)

theorem map_derivIdeal :
    Ideal.map φ (derivIdeal k J) = derivIdeal L (Ideal.map φ J) :=
  le_antisymm
    (map_derivIdeal_le (k := k) (L := L) (ι := ι) (S := S) (S' := S') φ hφ J)
    (derivIdeal_map_le (k := k) (L := L) (ι := ι) (S := S) (S' := S') φ hφ J)


end

end

end DerivIdealBaseChange
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
section

open AlgebraicGeometry CategoryTheory TopologicalSpace


theorem le_preimage_top (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) :
    U ≤ p ⁻¹ᵁ ⊤ := by
  intro _ _
  trivial

noncomputable def sectionsAlgebraMap (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) : k →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U)).hom

section
variable (k : Type u) [CommRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))

theorem sectionsAlgebraMap_eq (U : X.Opens) :
    sectionsAlgebraMap k p U =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U)).hom :=
  rfl

theorem sectionsAlgebraMap_comp_restrict {U V : X.Opens} (h : V ≤ U) :
    (X.presheaf.map (homOfLE h).op).hom.comp (sectionsAlgebraMap k p U) =
      sectionsAlgebraMap k p V := by
  have key : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U)) ≫
      X.presheaf.map (homOfLE h).op =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V (le_preimage_top k p V) := by
    rw [Category.assoc, Scheme.Hom.appLE_map]
  rw [sectionsAlgebraMap_eq k p U, sectionsAlgebraMap_eq k p V, ← CommRingCat.hom_comp, key]

theorem sectionsAlgebraMap_restrict_apply {U V : X.Opens} (h : V ≤ U) (a : k) :
    (X.presheaf.map (homOfLE h).op).hom (sectionsAlgebraMap k p U a) =
      sectionsAlgebraMap k p V a :=
  DFunLike.congr_fun (sectionsAlgebraMap_comp_restrict k p h) a


end

@[reducible] noncomputable def sectionsAlgebra (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) : Algebra k Γ(X, U) :=
  (sectionsAlgebraMap k p U).toAlgebra

theorem algebraMap_sectionsAlgebra (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) :
    @algebraMap k Γ(X, U) _ _ (sectionsAlgebra k p U) = sectionsAlgebraMap k p U :=
  rfl

section
variable (k : Type u) [CommRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))

theorem isScalarTower_sections (U : X.Opens) (f : Γ(X, U))
    [Algebra k Γ(X, U)] [Algebra k Γ(X, X.basicOpen f)]
    [Algebra Γ(X, U) Γ(X, X.basicOpen f)]
    (hU : algebraMap k Γ(X, U) = sectionsAlgebraMap k p U)
    (hV : algebraMap k Γ(X, X.basicOpen f) = sectionsAlgebraMap k p (X.basicOpen f))
    (hres : algebraMap Γ(X, U) Γ(X, X.basicOpen f) =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom) :
    IsScalarTower k Γ(X, U) Γ(X, X.basicOpen f) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [hV, hres, hU, sectionsAlgebraMap_restrict_apply]

theorem finiteType_sections [LocallyOfFiniteType p] (U : X.affineOpens)
    [Algebra k Γ(X, U.1)] (h : algebraMap k Γ(X, U.1) = sectionsAlgebraMap k p U.1) :
    Algebra.FiniteType k Γ(X, U.1) := by
  have hft : (p.appLE ⊤ U.1 (le_preimage_top k p U.1)).hom.FiniteType := by
    apply Scheme.Hom.finiteType_appLE p (isAffineOpen_top _) U.2
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id]
  have hsurj : Function.Surjective ⇑(Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom := fun y =>
    ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom y, DFunLike.congr_fun hcomp y⟩
  have hiso : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ hsurj
  have hst : (sectionsAlgebraMap k p U.1).FiniteType := by
    rw [sectionsAlgebraMap_eq, CommRingCat.hom_comp]
    exact hft.comp hiso
  have hinst : ‹Algebra k Γ(X, U.1)› = (sectionsAlgebraMap k p U.1).toAlgebra :=
    Algebra.algebra_ext _ _ fun r => DFunLike.congr_fun h r
  rw [hinst]
  exact hst


end

section
variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]

theorem isNoetherianRing_sections (U : X.affineOpens)
    [Algebra k Γ(X, U.1)] (h : algebraMap k Γ(X, U.1) = sectionsAlgebraMap k p U.1) :
    IsNoetherianRing Γ(X, U.1) := by
  have : Algebra.FiniteType k Γ(X, U.1) := finiteType_sections k p U h
  exact Algebra.FiniteType.isNoetherianRing k Γ(X, U.1)

theorem finitePresentation_kaehlerDifferential_sections (U : X.affineOpens) [Algebra k Γ(X, U.1)]
    (h : algebraMap k Γ(X, U.1) = sectionsAlgebraMap k p U.1) :
    Module.FinitePresentation Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) := by
  have : Algebra.FiniteType k Γ(X, U.1) := finiteType_sections k p U h
  have : IsNoetherianRing Γ(X, U.1) := isNoetherianRing_sections k p U h
  have : Module.Finite Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) := inferInstance
  exact Module.finitePresentation_of_finite ..

private theorem derivIdealSheaf_map_ideal_basicOpen_consolidated73 (I : X.IdealSheafData) :
    ∀ (U : X.affineOpens) (f : Γ(X, U.1)),
      Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
          (@derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U)) =
        @derivIdeal k _ _ _ (sectionsAlgebra k p (X.affineBasicOpen f).1)
          (I.ideal (X.affineBasicOpen f)) := by
  intro U f
  let algU : Algebra k Γ(X, U.1) := sectionsAlgebra k p U.1
  let algV : Algebra k Γ(X, X.basicOpen f) := sectionsAlgebra k p (X.basicOpen f)
  let algUV : Algebra Γ(X, U.1) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  have htower : IsScalarTower k Γ(X, U.1) Γ(X, X.basicOpen f) :=
    isScalarTower_sections k p U.1 f rfl rfl rfl
  have hloc : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  have hfp : Module.FinitePresentation Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) :=
    finitePresentation_kaehlerDifferential_sections k p U rfl
  have hI : Ideal.map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f)) (I.ideal U) =
      I.ideal (X.affineBasicOpen f) := I.map_ideal_basicOpen U f
  have key := map_derivIdeal_away (k := k) (S' := Γ(X, X.basicOpen f)) f (I.ideal U)
  exact key.trans (congrArg (@derivIdeal k _ Γ(X, X.basicOpen f) _ algV) hI)


end

noncomputable def derivIdealSheaf (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData) :
    X.IdealSheafData where
  ideal U := @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U)
  map_ideal_basicOpen := derivIdealSheaf_map_ideal_basicOpen_consolidated73 k p I

section
variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]

@[simp] theorem derivIdealSheaf_ideal (I : X.IdealSheafData) (U : X.affineOpens) :
    (derivIdealSheaf k p I).ideal U = @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) :=
  rfl

theorem le_derivIdealSheaf (I : X.IdealSheafData) :
    I ≤ derivIdealSheaf k p I := by
  have h : ∀ U : X.affineOpens, I.ideal U ≤ (derivIdealSheaf k p I).ideal U := by
    intro U
    exact @le_derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U)
  exact h

theorem derivIdealSheaf_mono :
    Monotone (derivIdealSheaf k p) := by
  intro I J h
  have key : ∀ U : X.affineOpens,
      (derivIdealSheaf k p I).ideal U ≤ (derivIdealSheaf k p J).ideal U := by
    intro U
    have hU : I.ideal U ≤ J.ideal U := h U
    rw [derivIdealSheaf_ideal, derivIdealSheaf_ideal]
    exact @derivIdeal_le_derivIdeal k _ _ _ (sectionsAlgebra k p U.1) _ _ hU
  exact key

theorem derivIdealSheaf_mul_le (I J : X.IdealSheafData) :
    derivIdealSheaf k p (I * J) ≤ I * derivIdealSheaf k p J ⊔ J * derivIdealSheaf k p I := by
  have h : ∀ U : X.affineOpens,
      (derivIdealSheaf k p (I * J)).ideal U ≤
        (I * derivIdealSheaf k p J ⊔ J * derivIdealSheaf k p I).ideal U := by
    intro U
    have hmul : ∀ A B : X.IdealSheafData, (A * B).ideal U = A.ideal U * B.ideal U := by
      intro A B
      simp [Scheme.IdealSheafData.ideal_mul]
    have key := @derivIdeal_mul_le k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1)
      (I.ideal U) (J.ideal U)
    have h1 : (derivIdealSheaf k p (I * J)).ideal U =
        @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U * J.ideal U) := by
      rw [derivIdealSheaf_ideal, hmul]
    have h2 : @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) =
        (derivIdealSheaf k p I).ideal U := (derivIdealSheaf_ideal k p I U).symm
    have h3 : @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (J.ideal U) =
        (derivIdealSheaf k p J).ideal U := (derivIdealSheaf_ideal k p J U).symm
    rw [h1]
    refine key.trans (sup_le ?_ ?_)
    · rw [h3, ← hmul]
      exact Scheme.IdealSheafData.le_def.mp le_sup_left U
    · rw [h2, ← hmul]
      exact Scheme.IdealSheafData.le_def.mp le_sup_right U
  exact h

theorem derivIdealSheaf_pow_succ_le (I : X.IdealSheafData) (n : ℕ) :
    derivIdealSheaf k p (I ^ (n + 1)) ≤ I ^ n * derivIdealSheaf k p I := by
  have key : ∀ U : X.affineOpens,
      (derivIdealSheaf k p (I ^ (n + 1))).ideal U ≤ (I ^ n * derivIdealSheaf k p I).ideal U := by
    intro U
    have hmul : ∀ A B : X.IdealSheafData, (A * B).ideal U = A.ideal U * B.ideal U := by
      intro A B
      simp [Scheme.IdealSheafData.ideal_mul]
    have hpow : ∀ m : ℕ, (I ^ m).ideal U = I.ideal U ^ m := fun m =>
      congrFun (Scheme.IdealSheafData.ideal_pow I m) U
    rw [hmul, derivIdealSheaf_ideal, derivIdealSheaf_ideal, hpow, hpow]
    exact @derivIdeal_pow_succ_le k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) n
  exact key


end

noncomputable def derivIdealSheafIterate (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    ℕ → X.IdealSheafData → X.IdealSheafData
  | 0, I => I
  | (r + 1), I => derivIdealSheaf k p (derivIdealSheafIterate k p r I)

section
variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]

@[simp] theorem derivIdealSheafIterate_zero (I : X.IdealSheafData) : derivIdealSheafIterate k p 0 I = I :=
  rfl

theorem derivIdealSheafIterate_succ (r : ℕ) (I : X.IdealSheafData) :
    derivIdealSheafIterate k p (r + 1) I = derivIdealSheaf k p (derivIdealSheafIterate k p r I) :=
  rfl

theorem derivIdealSheafIterate_one (I : X.IdealSheafData) :
    derivIdealSheafIterate k p 1 I = derivIdealSheaf k p I :=
  rfl

theorem derivIdealSheafIterate_add (r s : ℕ) (I : X.IdealSheafData) :
    derivIdealSheafIterate k p (r + s) I =
      derivIdealSheafIterate k p r (derivIdealSheafIterate k p s I) := by
  induction r with
  | zero => rw [Nat.zero_add, derivIdealSheafIterate_zero]
  | succ n ih =>
      rw [add_right_comm, derivIdealSheafIterate_succ, derivIdealSheafIterate_succ, ih]

@[simp] theorem derivIdealSheafIterate_ideal (r : ℕ)
    (I : X.IdealSheafData) (U : X.affineOpens) :
    (derivIdealSheafIterate k p r I).ideal U =
      @derivIdealIterate k _ _ _ (sectionsAlgebra k p U.1) r (I.ideal U) := by
  induction r with
  | zero =>
      rw [derivIdealSheafIterate_zero,
        @derivIdealIterate_zero k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U)]
  | succ n ih =>
      rw [derivIdealSheafIterate_succ, derivIdealSheaf_ideal, ih,
        @derivIdealIterate_succ k _ _ _ (sectionsAlgebra k p U.1) n (I.ideal U)]

theorem le_derivIdealSheafIterate (r : ℕ) (I : X.IdealSheafData) :
    I ≤ derivIdealSheafIterate k p r I := by
  induction r with
  | zero => exact le_rfl
  | succ n ih =>
    rw [derivIdealSheafIterate_succ]
    exact le_trans ih (le_derivIdealSheaf k p (derivIdealSheafIterate k p n I))


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

section

private theorem comp_presheafMap_comp_presheafMap_consolidated104 {X₁ : Scheme.{u}} {R : CommRingCat.{u}}
    {A B C : (X₁.Opens)ᵒᵖ} (h : R ⟶ X₁.presheaf.obj A) (g₁ : A ⟶ B) (g₂ : B ⟶ C) (g₃ : A ⟶ C) :
    (h ≫ X₁.presheaf.map g₁) ≫ X₁.presheaf.map g₂ = h ≫ X₁.presheaf.map g₃ := by
  rw [Category.assoc, ← Functor.map_comp, Scheme.presheaf_map_eq_of_parallel X₁ (g₁ ≫ g₂) g₃]

private theorem appTop_comp_topIso_hom_consolidated104 {X₁ Y₁ : Scheme.{u}} (f : X₁ ⟶ Y₁) (V : X₁.Opens)
    (hV : V ≤ f ⁻¹ᵁ (⊤ : Y₁.Opens)) :
    (V.ι ≫ f).appTop ≫ V.topIso.hom = f.appLE ⊤ V hV := by
  have hR : f.appLE ⊤ V hV = f.app ⊤ ≫ X₁.presheaf.map (homOfLE hV).op := rfl
  simp
  rw [hR]
  exact comp_presheafMap_comp_presheafMap_consolidated104 _ _ _ _

theorem appLE_top_comp_topIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Opens)
    (hV : V ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) :
    f.appLE ⊤ V hV ≫ V.topIso.inv = (V.ι ≫ f).appTop := by
  rw [← appTop_comp_topIso_hom_consolidated104 f V hV, Category.assoc, Iso.hom_inv_id, Category.comp_id]

def affineSpaceGlobalSectionsHom (k : Type u) [Field k] (m : ℕ) :
    MvPolynomial (ULift.{u} (Fin m)) k →+* Γ(affineSpaceFin k m, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop).hom

variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}

def EtaleChart.coord (c : EtaleChart p U m) (j : Fin m) : Γ(X, U) :=
  U.topIso.hom.hom
    (c.map.appTop.hom
      (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m))))

theorem EtaleChart.coord_def (c : EtaleChart p U m) (j : Fin m) :
    c.coord j =
      U.topIso.hom.hom
        (c.map.appTop.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m)))) :=
  rfl

def EtaleChart.coordRingHom (c : EtaleChart p U m) :
    MvPolynomial (ULift.{u} (Fin m)) k →+* Γ(X, U) :=
  (U.topIso.hom.hom.comp c.map.appTop.hom).comp (affineSpaceGlobalSectionsHom k m)

theorem EtaleChart.coordRingHom_def (c : EtaleChart p U m) :
    c.coordRingHom = (U.topIso.hom.hom.comp c.map.appTop.hom).comp (affineSpaceGlobalSectionsHom k m) :=
  rfl

private theorem appTop_hom_appTop_inv_apply_consolidated104 {A B : Scheme.{u}} (e : A ≅ B) (x : Γ(A, ⊤)) :
    (Scheme.Hom.appTop e.hom).hom ((Scheme.Hom.appTop e.inv).hom x) = x := by
  have h : Scheme.Hom.appTop e.inv ≫ Scheme.Hom.appTop e.hom = 𝟙 Γ(A, ⊤) := by
    rw [← Scheme.Hom.comp_appTop, e.hom_inv_id]
    simp
  have h2 := congrArg (fun f : Γ(A, ⊤) ⟶ Γ(A, ⊤) => CommRingCat.Hom.hom f x) h
  simpa using h2

section
variable (K : Type u) [Field K] (n : ℕ) (j : Fin n)

private theorem affineSpace_specIso_inv_appTop_coord_consolidated104 :
    ((AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).inv.appTop).hom
        (AffineSpace.coord (Spec (CommRingCat.of K)) (ULift.up j : ULift.{u} (Fin n)))
      = ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv).hom
          (MvPolynomial.X (ULift.up j : ULift.{u} (Fin n))) := by
  exact AffineSpace.SpecIso_inv_appTop_coord (CommRingCat.of K) (ULift.up j)

private theorem affineSpaceGlobalSectionsHom_X_consolidated104 :
    affineSpaceGlobalSectionsHom K n (MvPolynomial.X (ULift.up j : ULift.{u} (Fin n)))
      = AffineSpace.coord (Spec (CommRingCat.of K)) (ULift.up j : ULift.{u} (Fin n)) := by
  simp only [affineSpaceGlobalSectionsHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← affineSpace_specIso_inv_appTop_coord_consolidated104 K n j]
  exact appTop_hom_appTop_inv_apply_consolidated104 _ _


end

@[simp] theorem EtaleChart.coordRingHom_X (c : EtaleChart p U m) (j : Fin m) :
    c.coordRingHom (MvPolynomial.X (ULift.up j : ULift.{u} (Fin m))) = c.coord j := by
  rw [EtaleChart.coordRingHom_def, EtaleChart.coord_def]
  simp only [RingHom.comp_apply, affineSpaceGlobalSectionsHom_X_consolidated104]

private theorem affineSpace_specIso_hom_comp_specMap_C_consolidated104 (K : Type u) [Field K] (n : ℕ) :
    (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).hom ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin n)) K)) =
      affineSpaceFinToSpec K n := by
  have h : (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).inv ≫
      affineSpaceFinToSpec K n =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin n)) K)) := by
    simp
  rw [← h, Iso.hom_inv_id_assoc]

section
variable (c : EtaleChart p U m)

theorem EtaleChart.coordRingHom_comp_C :
    c.coordRingHom.comp (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k) =
      sectionsAlgebraMap k p U := by
  have hC : CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k))).appTop :=
    Scheme.ΓSpecIso_inv_naturality _
  have key : CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv ≫
          (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop ≫
            c.map.appTop ≫ U.topIso.hom =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U) := by
    rw [← Category.assoc, hC, Category.assoc,
      ← Category.assoc _ _ (c.map.appTop ≫ U.topIso.hom), ← Scheme.Hom.comp_appTop,
      affineSpace_specIso_hom_comp_specMap_C_consolidated104 k m, ← Category.assoc _ _ U.topIso.hom,
      ← Scheme.Hom.comp_appTop, c.comp_struct, appTop_comp_topIso_hom_consolidated104 p U (le_preimage_top k p U)]
  have h := congrArg CommRingCat.Hom.hom key
  exact RingHom.ext fun x => DFunLike.congr_fun h x

theorem EtaleChart.coordRingHom_C (a : k) :
    c.coordRingHom (MvPolynomial.C a) = sectionsAlgebraMap k p U a :=
  DFunLike.congr_fun (EtaleChart.coordRingHom_comp_C c) a

theorem EtaleChart.coordRingHom_etale (hU : IsAffineOpen U) :
    c.coordRingHom.Etale := by
  have hUaff : IsAffine U.toScheme := hU
  have hEt : Etale c.map := c.isEtale
  have hAaff : IsAffine (affineSpaceFin k m) := inferInstance
  have hbeta : IsIso (Scheme.Hom.appTop
      (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom) :=
    inferInstanceAs (IsIso
      ((AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.app ⊤))
  have hResp : RingHom.RespectsIso @RingHom.Etale := RingHom.Etale.respectsIso
  have hmap : RingHom.Etale (Scheme.Hom.appTop c.map).hom :=
    AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine.mp c.isEtale
  exact (hResp.cancel_left_isIso
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv)
      (Scheme.Hom.appTop (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom ≫
        Scheme.Hom.appTop c.map ≫ U.topIso.hom)).mpr
    ((hResp.cancel_left_isIso
        (Scheme.Hom.appTop (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom)
        (Scheme.Hom.appTop c.map ≫ U.topIso.hom)).mpr
      ((hResp.cancel_right_isIso (Scheme.Hom.appTop c.map) U.topIso.hom).mpr hmap))


end

@[reducible] def EtaleChart.algebra (c : EtaleChart p U m) :
    Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) :=
  c.coordRingHom.toAlgebra

theorem EtaleChart.algebraMap_eq_coordRingHom (c : EtaleChart p U m) :
    @algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) _ _ c.algebra = c.coordRingHom :=
  rfl

section
variable (c : EtaleChart p U m)

theorem EtaleChart.algebra_etale (hU : IsAffineOpen U) :
    @Algebra.Etale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) _ _ c.algebra := by
  have h : c.coordRingHom.Etale := EtaleChart.coordRingHom_etale c hU
  exact h

theorem EtaleChart.algebra_formallyEtale (hU : IsAffineOpen U) :
    @Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) _ _ c.algebra := by
  have h := EtaleChart.algebra_etale c hU
  exact h.1

theorem EtaleChart.isScalarTower :
    @IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U)
      (@Algebra.toSMul k (MvPolynomial (ULift.{u} (Fin m)) k) _ _ _)
      (@Algebra.toSMul (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) _ _ c.algebra)
      (@Algebra.toSMul k Γ(X, U) _ _ (sectionsAlgebra k p U)) := by
  let instPoly : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra
  let instBase : Algebra k Γ(X, U) := sectionsAlgebra k p U
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  exact (EtaleChart.coordRingHom_C c x).symm


end

section
variable {X₁ : Scheme.{u}} (V : X₁.Opens)

private theorem ideal_map_topIso_inv_injective_consolidated104 {J₁ J₂ : Ideal Γ(X₁, V)}
    (hJ : Ideal.map V.topIso.inv.hom J₁ = Ideal.map V.topIso.inv.hom J₂) : J₁ = J₂ := by
  have hid : (V.topIso.hom.hom).comp (V.topIso.inv.hom) = RingHom.id _ := by
    ext x
    exact Iso.inv_hom_id_apply V.topIso x
  have key : ∀ J : Ideal Γ(X₁, V),
      Ideal.map V.topIso.hom.hom (Ideal.map V.topIso.inv.hom J) = J := by
    intro J
    rw [Ideal.map_map, hid, Ideal.map_id]
  rw [← key J₁, hJ, key J₂]

private theorem ι_appLE_top_eq_topIso_inv_consolidated104 (e : (⊤ : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ e = V.topIso.inv := by
  simp
  exact Scheme.presheaf_map_eq_of_parallel X₁ _ _


end

section
variable (c : EtaleChart p U m)

theorem EtaleChart.ideal_eq_span_coord (hU : IsAffineOpen U)
    (I : X.IdealSheafData) (S : Finset (Fin m))
    (h : restrictIdeal I U = c.coordIdeal S) :
    I.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m))) := by
  have hUaff : IsAffine U.toScheme := hU
  have e : (⊤ : (U.toScheme).Opens) ≤ U.ι ⁻¹ᵁ U := by
    intro x _
    exact x.2
  have hL : (restrictIdeal I U).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩
      = Ideal.map U.topIso.inv.hom (I.ideal ⟨U, hU⟩) := by
    rw [restrictIdeal_eq_comap_ι, ← ι_appLE_top_eq_topIso_inv_consolidated104 U e]
    exact Scheme.IdealSheafData.comap_ideal_eq_map_appLE I U.ι ⟨U, hU⟩
      ⟨⊤, isAffineOpen_top U.toScheme⟩ e
  have hR : (c.coordIdeal S).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩
      = Ideal.map U.topIso.inv.hom (Ideal.span (c.coord '' (S : Set (Fin m)))) := by
    rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, Scheme.IdealSheafData.comap_ideal_top_eq_map_appTop,
      coordSubspaceIdeal_eq_ofIdealTop_span_coord, AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_ideal_top,
      Ideal.map_span, Ideal.map_span, ← Set.image_comp, ← Set.image_comp]
    refine congrArg Ideal.span (Set.image_congr fun j _ => ?_)
    exact (Iso.hom_inv_id_apply U.topIso _).symm
  have hfin : Ideal.map U.topIso.inv.hom (I.ideal ⟨U, hU⟩)
      = Ideal.map U.topIso.inv.hom (Ideal.span (c.coord '' (S : Set (Fin m)))) := by
    rw [← hL, ← hR, h]
  exact ideal_map_topIso_inv_injective_consolidated104 U hfin

theorem EtaleChart.etaleCoordinates_coord (j : Fin m) :
    @EtaleCoordinates.coord k _ (ULift.{u} (Fin m)) Γ(X, U) _ c.algebra
      (ULift.up j : ULift.{u} (Fin m)) = c.coord j := by
  have h : c.coordRingHom (MvPolynomial.X (ULift.up j : ULift.{u} (Fin m))) = c.coord j :=
    EtaleChart.coordRingHom_X c j
  exact h


end

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.DerivationLiftAndDeterminant
section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

section

section

private theorem algebraMap_mem_nonZeroDivisors_of_flat_consolidated140 {R A : Type u} [CommRing R]
    [CommRing A] [Algebra R A] [Module.Flat R A] {r : R} (hr : r ∈ nonZeroDivisors R) :
    algebraMap R A r ∈ nonZeroDivisors A := by
  have key : ∀ x : A, algebraMap R A r * x = 0 → x = 0 := by
    intro x hx
    have hsm : r • x = r • (0 : A) := by
      rw [smul_zero, Algebra.smul_def]
      exact hx
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors hr hsm
  rw [mem_nonZeroDivisors_iff]
  exact ⟨key, fun x hx => key x (by rw [mul_comm]; exact hx)⟩

private theorem coord_mem_nonZeroDivisors_of_isAffineOpen_consolidated140 {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (hU : IsAffineOpen U)
    (c : EtaleChart p U m) (j : Fin m) :
    c.coord j ∈ nonZeroDivisors ↑(X.presheaf.obj (op U)) := by
  let _ : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U)) := c.algebra
  have : Algebra.Etale (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U)) :=
    c.algebra_etale hU
  have : Module.Flat (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U)) :=
    inferInstance
  have halg : (algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U)))
      = c.coordRingHom := c.algebraMap_eq_coordRingHom
  have hXne : (MvPolynomial.X (ULift.up.{u} j) : MvPolynomial (ULift.{u} (Fin m)) k) ≠ 0 :=
    MvPolynomial.X_ne_zero _
  have hXnzd : (MvPolynomial.X (ULift.up.{u} j) : MvPolynomial (ULift.{u} (Fin m)) k)
      ∈ nonZeroDivisors (MvPolynomial (ULift.{u} (Fin m)) k) :=
    mem_nonZeroDivisors_of_ne_zero hXne
  have key : (algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U)))
      (MvPolynomial.X (ULift.up.{u} j)) ∈ nonZeroDivisors ↑(X.presheaf.obj (op U)) :=
    algebraMap_mem_nonZeroDivisors_of_flat_consolidated140 hXnzd
  rw [halg] at key
  rwa [c.coordRingHom_X j] at key

end

section

variable {R : Type*} [CommRing R]

theorem exists_unit_mul_of_span_eq {a b : R} (hb : b ∈ nonZeroDivisors R)
    (h : Ideal.span ({a} : Set R) = Ideal.span ({b} : Set R)) :
    ∃ u : Rˣ, a = (u : R) * b := by
  have ha : a ∈ Ideal.span ({b} : Set R) := by
    rw [← h]
    exact Ideal.mem_span_singleton_self a
  have hb' : b ∈ Ideal.span ({a} : Set R) := by
    rw [h]
    exact Ideal.mem_span_singleton_self b
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hb'
  have hcancel : ∀ z : R, z * b = 0 → z = 0 := (mem_nonZeroDivisors_iff.mp hb).2
  have hzero : (d * c - 1) * b = 0 := by
    have hx : d * c * b = b := by rw [mul_assoc, hc, hd]
    rw [sub_mul, one_mul, hx, sub_self]
  have hdc : d * c = 1 := sub_eq_zero.mp (hcancel _ hzero)
  refine ⟨⟨c, d, by rw [mul_comm]; exact hdc, hdc⟩, hc.symm⟩

end

section

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

theorem derivation_mapsTo_span_self {B : Type*} [CommRing B] [Algebra k B]
    (D : Derivation k B B) (h : B) (hD : D h = 0) :
    ∀ x ∈ Ideal.span ({h} : Set B), D x ∈ Ideal.span ({h} : Set B) := by
  intro x hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [Derivation.leibniz, hD, smul_zero, zero_add, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self h)

theorem algHom_map_derivation_eq_zero (π : R →ₐ[k] S) (h : R)
    (hker : RingHom.ker π.toRingHom = Ideal.span ({h} : Set R))
    (D : Derivation k R R) (hD : D h = 0) :
    ∀ r : R, π r = 0 → π (D r) = 0 := by
  intro r hr
  have hrk : r ∈ Ideal.span ({h} : Set R) := by
    rw [← hker]
    exact hr
  have h2 : D r ∈ Ideal.span ({h} : Set R) := derivation_mapsTo_span_self D h hD r hrk
  rw [← hker] at h2
  have h3 : π.toRingHom (D r) = 0 := RingHom.mem_ker.mp h2
  exact h3

def liftDerivationOfKerEqSpan (π : R →ₐ[k] S) (hπ : Function.Surjective π) (h : R)
    (hker : RingHom.ker π.toRingHom = Ideal.span ({h} : Set R))
    (D : Derivation k R R) (hD : D h = 0) : Derivation k S S :=
  D.liftOfSurjective hπ (algHom_map_derivation_eq_zero π h hker D hD)

theorem liftDerivationOfKerEqSpan_apply (π : R →ₐ[k] S) (hπ : Function.Surjective π)
    (h : R) (hker : RingHom.ker π.toRingHom = Ideal.span ({h} : Set R))
    (D : Derivation k R R) (hD : D h = 0) (r : R) :
    liftDerivationOfKerEqSpan π hπ h hker D hD (π r) = π (D r) :=
  D.liftOfSurjective_apply hπ (algHom_map_derivation_eq_zero π h hker D hD) r

end

section

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

private theorem det_eq_det_submatrix_succ_consolidated140 (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : ∀ b : Fin (n + 1), M 0 b = if b = 0 then (1 : R) else 0) :
    M.det = (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_row_zero]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp [h, Fin.succAbove_zero]
  · intro b _ hb
    simp [h b, hb]
  · intro hb
    exact absurd (Finset.mem_univ (0 : Fin (n + 1))) hb

section
variable (e : ι ≃ Fin (n + 1)) (M : Matrix ι ι R)

theorem det_eq_det_submatrix_of_row_eq_single (h : ∀ b : ι, M (e.symm 0) b = if b = e.symm 0 then (1 : R) else 0) :
    M.det =
      (M.submatrix (fun i : Fin n => e.symm i.succ) (fun i : Fin n => e.symm i.succ)).det := by
  have hN : ∀ b : Fin (n + 1),
      (M.submatrix e.symm e.symm) 0 b = if b = 0 then (1 : R) else 0 := by
    intro b
    simp only [Matrix.submatrix_apply]
    rw [h (e.symm b)]
    by_cases hb : b = 0
    · simp [hb]
    · have hne : ¬ (e.symm b = e.symm 0) := fun hc => hb (e.symm.injective hc)
      rw [if_neg hne, if_neg hb]
  have h2 := det_eq_det_submatrix_succ_consolidated140 (M.submatrix e.symm e.symm) hN
  rw [Matrix.det_submatrix_equiv_self] at h2
  rw [h2, Matrix.submatrix_submatrix]
  rfl

theorem det_eq_det_submatrix_of_col_eq_single (h : ∀ a : ι, M a (e.symm 0) = if a = e.symm 0 then (1 : R) else 0) :
    M.det =
      (M.submatrix (fun i : Fin n => e.symm i.succ) (fun i : Fin n => e.symm i.succ)).det := by
  have h' : ∀ b : ι, M.transpose (e.symm 0) b = if b = e.symm 0 then (1 : R) else 0 :=
    fun b => h b
  have h1 := det_eq_det_submatrix_of_row_eq_single e M.transpose h'
  rw [Matrix.det_transpose] at h1
  rw [h1, ← Matrix.transpose_submatrix, Matrix.det_transpose]


end

end

section

variable {X : Scheme.{u}} {k : Type u} [Field k]

theorem exists_unit_mul_coord_of_span_eq (p : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens}
    (hU : IsAffineOpen U) {n : ℕ} (c : EtaleChart p U n) (j : Fin n) (g : Γ(X, U))
    (h : Ideal.span ({g} : Set Γ(X, U)) = Ideal.span ({c.coord j} : Set Γ(X, U))) :
    ∃ v : (Γ(X, U))ˣ, g = (v : Γ(X, U)) * c.coord j :=
  exists_unit_mul_of_span_eq (coord_mem_nonZeroDivisors_of_isAffineOpen_consolidated140 hU c j) h

end

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativesInBlowupCharts
section
namespace EtaleCoordinates

variable (k : Type*) [CommRing k] (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S₁ : Type*) [CommRing S₁] [Algebra k S₁] [Algebra (MvPolynomial ι k) S₁]
  [IsScalarTower k (MvPolynomial ι k) S₁] [Algebra.FormallyEtale (MvPolynomial ι k) S₁]
  (φ : S →ₐ[k] S₁) (T : Finset ι) (s : ι)

section
variable (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s) (hs : φ (coord k ι S s) = coord k ι S₁ s) (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
include hin hs hout

theorem partialDeriv_map_of_mem
    (i : ι) (hiT : i ∈ T) (his : i ≠ s) (f : S) :
    partialDeriv k ι S₁ i (φ f)
      = coord k ι S₁ s * φ (partialDeriv k ι S i f) := by
  let _ : Algebra S S₁ := φ.toRingHom.toAlgebra
  have : IsScalarTower k S S₁ := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    show algebraMap k S₁ x = φ (algebraMap k S x)
    exact (φ.commutes x).symm
  have hsmul : ∀ (a : S) (z : S₁), a • z = φ a * z := fun _ _ => rfl
  let L₁ : S →ₗ[k] S₁ := (partialDeriv k ι S₁ i).toLinearMap.comp φ.toLinearMap
  let L₂ : S →ₗ[k] S₁ :=
    (LinearMap.mulLeft k (coord k ι S₁ s)).comp
      (φ.toLinearMap.comp (partialDeriv k ι S i).toLinearMap)
  have h₁ : ∀ a b : S, L₁ (a * b) = a • L₁ b + b • L₁ a := by
    intro a b
    show partialDeriv k ι S₁ i (φ (a * b))
        = a • partialDeriv k ι S₁ i (φ b) + b • partialDeriv k ι S₁ i (φ a)
    simp only [hsmul, map_mul, (partialDeriv k ι S₁ i).leibniz, smul_eq_mul]
  have h₂ : ∀ a b : S, L₂ (a * b) = a • L₂ b + b • L₂ a := by
    intro a b
    show coord k ι S₁ s * φ (partialDeriv k ι S i (a * b))
        = a • (coord k ι S₁ s * φ (partialDeriv k ι S i b))
          + b • (coord k ι S₁ s * φ (partialDeriv k ι S i a))
    simp only [hsmul, (partialDeriv k ι S i).leibniz, smul_eq_mul, map_add, map_mul]
    ring
  have hD : Derivation.mk' L₁ h₁ = Derivation.mk' L₂ h₂ := by
    refine derivation_ext_of_coord k ι S S₁ _ _ ?_
    intro j
    show partialDeriv k ι S₁ i (φ (coord k ι S j))
        = coord k ι S₁ s * φ (partialDeriv k ι S i (coord k ι S j))
    by_cases hjT : j ∈ T
    · by_cases hjs : j = s
      · subst hjs
        rw [hs]
        simp only [partialDeriv_coord, if_neg his, map_zero, mul_zero]
      · rw [hin j hjT hjs, (partialDeriv k ι S₁ i).leibniz]
        simp only [smul_eq_mul, partialDeriv_coord, if_neg his, mul_zero, zero_add]
        by_cases hij : i = j
        · simp [hij]
        · simp [hij]
    · rw [hout j hjT]
      have hij : i ≠ j := by rintro rfl; exact hjT hiT
      simp only [partialDeriv_coord, if_neg hij, map_zero, mul_zero]
  exact DFunLike.congr_fun hD f

theorem partialDeriv_map_of_notMem
    (hsT : s ∈ T) (i : ι) (hiT : i ∉ T) (f : S) :
    partialDeriv k ι S₁ i (φ f) = φ (partialDeriv k ι S i f) := by
  let _ : Algebra S S₁ := φ.toRingHom.toAlgebra
  have halg : ∀ x : S, algebraMap S S₁ x = φ x := fun x => rfl
  have : IsScalarTower k S S₁ :=
    IsScalarTower.of_algebraMap_eq fun x => by rw [halg]; exact (φ.commutes x).symm
  have hsmul : ∀ (a : S) (x : S₁), a • x = φ a * x := by
    intro a x
    rw [Algebra.smul_def, halg]
  have his : i ≠ s := fun h => hiT (by rw [h]; exact hsT)
  have h₁ : ∀ a b : S,
      ((partialDeriv k ι S₁ i).toLinearMap.comp (φ.toLinearMap : S →ₗ[k] S₁)) (a * b)
        = a • ((partialDeriv k ι S₁ i).toLinearMap.comp (φ.toLinearMap : S →ₗ[k] S₁)) b
          + b • ((partialDeriv k ι S₁ i).toLinearMap.comp (φ.toLinearMap : S →ₗ[k] S₁)) a := by
    intro a b
    show partialDeriv k ι S₁ i (φ (a * b))
        = a • partialDeriv k ι S₁ i (φ b) + b • partialDeriv k ι S₁ i (φ a)
    rw [map_mul, Derivation.leibniz]
    simp only [hsmul, smul_eq_mul]
  have h₂ : ∀ a b : S,
      ((φ.toLinearMap : S →ₗ[k] S₁).comp (partialDeriv k ι S i).toLinearMap) (a * b)
        = a • ((φ.toLinearMap : S →ₗ[k] S₁).comp (partialDeriv k ι S i).toLinearMap) b
          + b • ((φ.toLinearMap : S →ₗ[k] S₁).comp (partialDeriv k ι S i).toLinearMap) a := by
    intro a b
    show φ (partialDeriv k ι S i (a * b))
        = a • φ (partialDeriv k ι S i b) + b • φ (partialDeriv k ι S i a)
    rw [Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, hsmul]
  have key :
      Derivation.mk' ((partialDeriv k ι S₁ i).toLinearMap.comp (φ.toLinearMap : S →ₗ[k] S₁)) h₁
        = Derivation.mk' ((φ.toLinearMap : S →ₗ[k] S₁).comp
            (partialDeriv k ι S i).toLinearMap) h₂ := by
    refine derivation_ext_of_coord k ι S S₁ _ _ ?_
    intro j
    show partialDeriv k ι S₁ i (φ (coord k ι S j)) = φ (partialDeriv k ι S i (coord k ι S j))
    by_cases hj : j ∈ T
    · by_cases hjs : j = s
      · rw [hjs, hs, partialDeriv_coord_of_ne k ι S₁ i s his,
          partialDeriv_coord_of_ne k ι S i s his, map_zero]
      · have hij : i ≠ j := fun h => hiT (by rw [h]; exact hj)
        rw [hin j hj hjs, Derivation.leibniz, partialDeriv_coord_of_ne k ι S₁ i s his,
          partialDeriv_coord_of_ne k ι S₁ i j hij, partialDeriv_coord_of_ne k ι S i j hij,
          smul_zero, smul_zero, add_zero, map_zero]
    · rw [hout j hj, partialDeriv_coord, partialDeriv_coord]
      split_ifs with h
      · exact (map_one φ).symm
      · exact (map_zero φ).symm
  exact DFunLike.congr_fun key f

theorem coord_mul_partialDeriv_map_eq_map_sum
    (hsT : s ∈ T) (f : S) :
    coord k ι S₁ s * partialDeriv k ι S₁ s (φ f)
      = φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i f) := by
  let _ : Algebra S S₁ := φ.toRingHom.toAlgebra
  have : IsScalarTower k S S₁ :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have hsmul : ∀ (a : S) (z : S₁), a • z = φ a * z := fun a z => Algebra.smul_def a z
  have hsum_add : ∀ x y : S,
      (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (x + y))
        = (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x)
          + (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i y) := by
    intro x y
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, mul_add]
  have hsum_smul : ∀ (c : k) (x : S),
      (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (c • x))
        = c • (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x) := by
    intro c x
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Derivation.map_smul, mul_smul_comm]
  have hsum_leib : ∀ a b : S,
      (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (a * b))
        = a * (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i b)
          + b * (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i a) := by
    intro a b
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    ring
  let L₁ : S →ₗ[k] S₁ :=
    { toFun := fun x => coord k ι S₁ s * partialDeriv k ι S₁ s (φ x)
      map_add' := by
        intro x y
        show coord k ι S₁ s * partialDeriv k ι S₁ s (φ (x + y))
          = coord k ι S₁ s * partialDeriv k ι S₁ s (φ x)
            + coord k ι S₁ s * partialDeriv k ι S₁ s (φ y)
        rw [map_add, map_add, mul_add]
      map_smul' := by
        intro c x
        show coord k ι S₁ s * partialDeriv k ι S₁ s (φ (c • x))
          = c • (coord k ι S₁ s * partialDeriv k ι S₁ s (φ x))
        rw [map_smul, Derivation.map_smul, mul_smul_comm] }
  let L₂ : S →ₗ[k] S₁ :=
    { toFun := fun x => φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x)
      map_add' := by
        intro x y
        show φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (x + y))
          = φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x)
            + φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i y)
        rw [hsum_add, map_add]
      map_smul' := by
        intro c x
        show φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (c • x))
          = c • φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x)
        rw [hsum_smul, map_smul] }
  have hleib1 : ∀ a b : S, L₁ (a * b) = a • L₁ b + b • L₁ a := by
    intro a b
    show coord k ι S₁ s * partialDeriv k ι S₁ s (φ (a * b))
      = a • (coord k ι S₁ s * partialDeriv k ι S₁ s (φ b))
        + b • (coord k ι S₁ s * partialDeriv k ι S₁ s (φ a))
    rw [map_mul, Derivation.leibniz, hsmul a, hsmul b]
    simp only [smul_eq_mul]
    ring
  have hleib2 : ∀ a b : S, L₂ (a * b) = a • L₂ b + b • L₂ a := by
    intro a b
    show φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (a * b))
      = a • φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i b)
        + b • φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i a)
    rw [hsum_leib, map_add, map_mul, map_mul, hsmul a, hsmul b]
  have hD : Derivation.mk' L₁ hleib1 = Derivation.mk' L₂ hleib2 := by
    refine derivation_ext_of_coord k ι S S₁ _ _ fun j => ?_
    show coord k ι S₁ s * partialDeriv k ι S₁ s (φ (coord k ι S j))
      = φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (coord k ι S j))
    have hsum : (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (coord k ι S j))
        = if j ∈ T then coord k ι S j else 0 := by
      have hterm : ∀ i ∈ T, coord k ι S i * partialDeriv k ι S i (coord k ι S j)
          = if i = j then coord k ι S j else 0 := by
        intro i _
        rw [partialDeriv_coord]
        by_cases h : i = j
        · subst h
          simp
        · simp [h]
      rw [Finset.sum_congr rfl hterm]
      by_cases hj : j ∈ T
      · rw [Finset.sum_eq_single j]
        · simp [hj]
        · intro i _ hij
          rw [if_neg hij]
        · intro h
          exact absurd hj h
      · rw [if_neg hj]
        refine Finset.sum_eq_zero fun i hi => ?_
        have hij : i ≠ j := by
          rintro rfl
          exact hj hi
        rw [if_neg hij]
    rw [hsum]
    by_cases hjs : j = s
    · subst hjs
      rw [hs, if_pos hsT, hs, partialDeriv_coord_self, mul_one]
    · by_cases hjT : j ∈ T
      · have h1 : partialDeriv k ι S₁ s (coord k ι S₁ s) = 1 :=
          partialDeriv_coord_self k ι S₁ s
        have h2 : partialDeriv k ι S₁ s (coord k ι S₁ j) = 0 :=
          partialDeriv_coord_of_ne k ι S₁ s j (Ne.symm hjs)
        rw [if_pos hjT, hin j hjT hjs, Derivation.leibniz, h1, h2]
        simp only [smul_eq_mul]
        ring
      · have hne : s ≠ j := by
          rintro rfl
          exact hjT hsT
        rw [if_neg hjT, map_zero, hout j hjT,
          partialDeriv_coord_of_ne k ι S₁ s j hne, mul_zero]
  exact DFunLike.congr_fun hD f

theorem coord_mul_partialDeriv_map_eq_map_add_sum_erase
    (hsT : s ∈ T) (f : S) :
    coord k ι S₁ s * partialDeriv k ι S₁ s (φ f)
      = φ (coord k ι S s * partialDeriv k ι S s f
          + ∑ i ∈ T.erase s, coord k ι S i * partialDeriv k ι S i f) := by
  rw [coord_mul_partialDeriv_map_eq_map_sum k ι S S₁ φ T s hin hs hout hsT f]
  refine congrArg φ ?_
  exact (Finset.add_sum_erase T (fun i => coord k ι S i * partialDeriv k ι S i f) hsT).symm

theorem map_partialDeriv_eq_pow_mul_of_mem
    (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (i : ι) (hiT : i ∈ T) (his : i ≠ s)
    (f : S) (g : S₁) (e : ℕ) (hfg : φ f = coord k ι S₁ s ^ (e + 1) * g) :
    φ (partialDeriv k ι S i f) = coord k ι S₁ s ^ e * partialDeriv k ι S₁ i g := by
  have h1 : partialDeriv k ι S₁ i (φ f)
      = coord k ι S₁ s * φ (partialDeriv k ι S i f) :=
    partialDeriv_map_of_mem k ι S S₁ φ T s hin hs hout i hiT his f
  have hy : partialDeriv k ι S₁ i (coord k ι S₁ s) = 0 :=
    partialDeriv_coord_of_ne k ι S₁ i s his
  have hpow : partialDeriv k ι S₁ i (coord k ι S₁ s ^ (e + 1)) = 0 := by
    rw [Derivation.leibniz_pow, hy, smul_zero, smul_zero]
  rw [hfg, Derivation.leibniz, hpow, smul_zero, add_zero, smul_eq_mul] at h1
  have key : (φ (partialDeriv k ι S i f)
      - coord k ι S₁ s ^ e * partialDeriv k ι S₁ i g) * coord k ι S₁ s = 0 := by
    linear_combination -h1
  have h3 : φ (partialDeriv k ι S i f)
      - coord k ι S₁ s ^ e * partialDeriv k ι S₁ i g = 0 :=
    (mem_nonZeroDivisors_iff.mp hnzd).2 _ key
  linear_combination h3

theorem map_partialDeriv_eq_pow_mul_of_notMem
    (hsT : s ∈ T) (i : ι) (hiT : i ∉ T)
    (f : S) (g : S₁) (e : ℕ) (hfg : φ f = coord k ι S₁ s ^ (e + 1) * g) :
    φ (partialDeriv k ι S i f) = coord k ι S₁ s ^ (e + 1) * partialDeriv k ι S₁ i g := by
  have his : i ≠ s := fun h => hiT (by rw [h]; exact hsT)
  have hz : partialDeriv k ι S₁ i (coord k ι S₁ s) = 0 :=
    partialDeriv_coord_of_ne k ι S₁ i s his
  have hpow : partialDeriv k ι S₁ i (coord k ι S₁ s ^ (e + 1)) = 0 := by
    rw [Derivation.leibniz_pow, hz, smul_zero, smul_zero]
  rw [← partialDeriv_map_of_notMem k ι S S₁ φ T s hin hs hout hsT i hiT f, hfg,
    Derivation.leibniz, hpow, smul_zero, add_zero, smul_eq_mul]

theorem map_partialDeriv_self_eq_pow_mul
    (hsT : s ∈ T) (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (f : S) (g : S₁) (e : ℕ) (hfg : φ f = coord k ι S₁ s ^ (e + 1) * g) :
    φ (partialDeriv k ι S s f)
      = coord k ι S₁ s ^ e
        * (coord k ι S₁ s * partialDeriv k ι S₁ s g + ((e + 1 : ℕ) : S₁) * g
            - ∑ i ∈ T.erase s, coord k ι S₁ i * partialDeriv k ι S₁ i g) := by
  have hpow : partialDeriv k ι S₁ s (coord k ι S₁ s ^ (e + 1))
      = ((e + 1 : ℕ) : S₁) * coord k ι S₁ s ^ e := by
    rw [Derivation.leibniz_pow, partialDeriv_coord_self, Nat.add_sub_cancel]
    simp only [smul_eq_mul, mul_one, nsmul_eq_mul]
  have h2 : partialDeriv k ι S₁ s (φ f)
      = coord k ι S₁ s ^ (e + 1) * partialDeriv k ι S₁ s g
        + ((e + 1 : ℕ) : S₁) * coord k ι S₁ s ^ e * g := by
    rw [hfg, Derivation.leibniz, hpow]
    simp only [smul_eq_mul]
    ring
  have hsum2 : ∑ i ∈ T.erase s, φ (coord k ι S i * partialDeriv k ι S i f)
      = coord k ι S₁ s ^ (e + 1)
        * ∑ i ∈ T.erase s, coord k ι S₁ i * partialDeriv k ι S₁ i g := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiT : i ∈ T := Finset.mem_of_mem_erase hi
    have his : i ≠ s := Finset.ne_of_mem_erase hi
    rw [map_mul, hin i hiT his,
      map_partialDeriv_eq_pow_mul_of_mem k ι S S₁ φ T s hin hs hout hnzd i hiT his f g e hfg]
    ring
  have h1 : coord k ι S₁ s * partialDeriv k ι S₁ s (φ f)
      = coord k ι S₁ s * φ (partialDeriv k ι S s f)
        + coord k ι S₁ s ^ (e + 1)
          * ∑ i ∈ T.erase s, coord k ι S₁ i * partialDeriv k ι S₁ i g := by
    rw [coord_mul_partialDeriv_map_eq_map_add_sum_erase k ι S S₁ φ T s hin hs hout hsT f, map_add, map_mul, hs, map_sum, hsum2]
  rw [h2] at h1
  have h0 : (φ (partialDeriv k ι S s f)
      - coord k ι S₁ s ^ e
        * (coord k ι S₁ s * partialDeriv k ι S₁ s g + ((e + 1 : ℕ) : S₁) * g
            - ∑ i ∈ T.erase s, coord k ι S₁ i * partialDeriv k ι S₁ i g))
      * coord k ι S₁ s = 0 := by
    linear_combination -h1
  have h3 := (mem_nonZeroDivisors_iff.mp hnzd).2 _ h0
  linear_combination h3


end

private theorem mul_mem_span_singleton_mul_consolidated71 {R : Type*} [CommRing R] (a : R) (I : Ideal R)
    {g : R} (hg : g ∈ I) : a * g ∈ Ideal.span ({a} : Set R) * I :=
  Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton_iff.mpr rfl)) hg

private theorem finset_sum_smul_derivation_apply_consolidated71 {k : Type*} [CommRing k] {S : Type*} [CommRing S]
    [Algebra k S] {ι : Type*} (t : Finset ι) (c : ι → S) (D : ι → Derivation k S S) (x : S) :
    (∑ i ∈ t, c i • D i) x = ∑ i ∈ t, c i * D i x := by
  refine Finset.cons_induction_on t ?_ ?_
  · simp
  · intro a u ha ih
    rw [Finset.sum_cons, Finset.sum_cons]
    simp [ih]

section
variable [Fintype ι] (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s) (hs : φ (coord k ι S s) = coord k ι S₁ s) (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i) (hsT : s ∈ T) (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁) (J : Ideal S) (J₁ : Ideal S₁) (m : ℕ)
include hin hs hout hsT hnzd

theorem map_derivIdeal_le_span_pow_mul (hm : 1 ≤ m)
    (hJ : Ideal.map φ J ≤ Ideal.span {coord k ι S₁ s ^ m} * J₁) :
    Ideal.map φ (derivIdeal k J)
      ≤ Ideal.span {coord k ι S₁ s ^ (m - 1)} * derivIdeal k J₁ := by
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, m = e + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hmem : ∀ x ∈ J, ∃ g ∈ J₁, φ x = coord k ι S₁ s ^ (e + 1) * g := by
    intro x hx
    obtain ⟨g, hg, hgx⟩ := Ideal.mem_span_singleton_mul.1 (hJ (Ideal.mem_map_of_mem φ hx))
    exact ⟨g, hg, hgx.symm⟩
  have hkey : ∀ x ∈ J, ∀ i : ι,
      φ (partialDeriv k ι S i x) ∈ Ideal.span {coord k ι S₁ s ^ e} * derivIdeal k J₁ := by
    intro x hx i
    obtain ⟨g, hg, hgx⟩ := hmem x hx
    by_cases hiT : i ∈ T
    · by_cases his : i = s
      · have hbr : coord k ι S₁ s * partialDeriv k ι S₁ s g + ((e + 1 : ℕ) : S₁) * g
            - ∑ j ∈ T.erase s, coord k ι S₁ j * partialDeriv k ι S₁ j g
              ∈ derivIdeal k J₁ := by
          refine sub_mem (add_mem ?_ ?_) ?_
          · exact Ideal.mul_mem_left _ _
              (derivation_apply_mem_derivIdeal k J₁ (partialDeriv k ι S₁ s) hg)
          · exact Ideal.mul_mem_left _ _ (le_derivIdeal k J₁ hg)
          · refine sum_mem fun j _ => ?_
            exact Ideal.mul_mem_left _ _
              (derivation_apply_mem_derivIdeal k J₁ (partialDeriv k ι S₁ j) hg)
        rw [his, map_partialDeriv_self_eq_pow_mul k ι S S₁ φ T s hin hs hout hsT hnzd x g e hgx]
        exact mul_mem_span_singleton_mul_consolidated71 _ _ hbr
      · rw [map_partialDeriv_eq_pow_mul_of_mem k ι S S₁ φ T s hin hs hout hnzd i hiT his x g e hgx]
        exact mul_mem_span_singleton_mul_consolidated71 _ _
          (derivation_apply_mem_derivIdeal k J₁ (partialDeriv k ι S₁ i) hg)
    · rw [map_partialDeriv_eq_pow_mul_of_notMem k ι S S₁ φ T s hin hs hout hsT i hiT x g e hgx,
        pow_succ, mul_assoc]
      exact mul_mem_span_singleton_mul_consolidated71 _ _
        (Ideal.mul_mem_left _ _
          (derivation_apply_mem_derivIdeal k J₁ (partialDeriv k ι S₁ i) hg))
  rw [Ideal.map_le_iff_le_comap, derivIdeal_le_iff]
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨g, hg, hgx⟩ := hmem x hx
    refine Ideal.mem_comap.mpr ?_
    rw [hgx, pow_succ, mul_assoc]
    exact mul_mem_span_singleton_mul_consolidated71 _ _
      (Ideal.mul_mem_left _ _ (le_derivIdeal k J₁ hg))
  · intro D x hx
    refine Ideal.mem_comap.mpr ?_
    have h1 : D x = (∑ i : ι, D (coord k ι S i) • partialDeriv k ι S i) x :=
      congrArg (fun E : Derivation k S S => E x) (eq_sum_smul_partialDeriv k ι S D)
    have hDx : D x = ∑ i : ι, D (coord k ι S i) * partialDeriv k ι S i x := by
      rw [h1]
      exact finset_sum_smul_derivation_apply_consolidated71 Finset.univ (fun i => D (coord k ι S i))
        (fun i => partialDeriv k ι S i) x
    rw [hDx, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (hkey x hx i)

theorem map_derivIdealIterate_le_span_pow_mul (hJ : Ideal.map φ J ≤ Ideal.span {coord k ι S₁ s ^ m} * J₁)
    (j : ℕ) (hj : j ≤ m) :
    Ideal.map φ (derivIdealIterate k j J)
      ≤ Ideal.span {coord k ι S₁ s ^ (m - j)} * derivIdealIterate k j J₁ := by
  have key : ∀ r : ℕ, r ≤ m → Ideal.map φ (derivIdealIterate k r J)
      ≤ Ideal.span {coord k ι S₁ s ^ (m - r)} * derivIdealIterate k r J₁ := by
    intro r
    induction r with
    | zero =>
        intro _
        rw [derivIdealIterate_zero k J, derivIdealIterate_zero k J₁, Nat.sub_zero]
        exact hJ
    | succ r ih =>
        intro hr
        have hrm : r ≤ m := Nat.le_of_succ_le hr
        have h1 : 1 ≤ m - r := by omega
        have hstep := map_derivIdeal_le_span_pow_mul k ι S S₁ φ T s hin hs hout hsT hnzd
          (derivIdealIterate k r J) (derivIdealIterate k r J₁) (m - r) h1 (ih hrm)
        have hmm : m - r - 1 = m - (r + 1) := by omega
        rw [hmm] at hstep
        rw [derivIdealIterate_succ k r J, derivIdealIterate_succ k r J₁]
        exact hstep
  exact key j hj


end

end EtaleCoordinates
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LeadingForm
section

open IsLocalRing

def multiIndicesOfDegree (h r : ℕ) : Finset (Fin h → ℕ) :=
  (Fintype.piFinset fun _ : Fin h => Finset.range (r + 1)).filter fun β => ∑ i, β i = r

theorem mem_multiIndicesOfDegree {h r : ℕ} (β : Fin h → ℕ) :
    β ∈ multiIndicesOfDegree h r ↔ ∑ i, β i = r := by
  simp only [multiIndicesOfDegree, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun hβ => hβ.2
  · intro hs
    refine ⟨fun i => ?_, hs⟩
    have h1 : β i ≤ r := by
      rw [← hs]
      exact Finset.single_le_sum (f := β) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

section
variable {k R : Type*} [CommRing k] [CommRing R] [IsLocalRing R] [Algebra k R] {h : ℕ} (x : Fin h → R) (D : Fin h → Derivation k R R) (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R) (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) (hDD : ∀ i j : Fin h, ∀ a : R, D i (D j a) = D j (D i a)) (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R)) (r : ℕ)
include hx hD hDD hunit

private theorem mem_maximalIdeal_pow_succ_of_multiIndexDeriv_mem_consolidated74 :
    ∀ f : R, f ∈ IsLocalRing.maximalIdeal R ^ r →
      (∀ β : Fin h → ℕ, (∑ i, β i = r) → multiIndexDeriv D β f ∈ IsLocalRing.maximalIdeal R) →
      f ∈ IsLocalRing.maximalIdeal R ^ (r + 1) := by
  induction r with
  | zero =>
    intro f _ hβ
    have h0 := hβ (fun _ => 0) (by simp)
    rw [multiIndexDeriv_fun_zero] at h0
    simpa using h0
  | succ r ih =>
    intro f hf hβ
    have key : ∀ i, D i f ∈ IsLocalRing.maximalIdeal R ^ (r + 1) := by
      intro i
      refine ih (D i f) ?_ ?_
      · have h1 := multiIndexDeriv_mem_pow_sub D (IsLocalRing.maximalIdeal R) (r + 1) hf
          (unitMultiIndex i)
        rw [multiIndexDeriv_unitMultiIndex, sum_unitMultiIndex] at h1
        simpa using h1
      · intro β hβ'
        have hsum : ∑ j, (β + unitMultiIndex i) j = r + 1 := by
          simp only [Pi.add_apply]
          rw [Finset.sum_add_distrib, hβ', sum_unitMultiIndex]
        have h2 := hβ (β + unitMultiIndex i) hsum
        rwa [multiIndexDeriv_add_unitMultiIndex_apply_first D hDD β i f] at h2
    have hfx : f ∈ Ideal.span (Set.range x) ^ (r + 1) := by rw [hx]; exact hf
    have hdx : ∀ i, D i f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
      intro i; rw [hx]; exact key i
    have hres := mem_pow_succ_of_deriv_mem_pow k x D hD (hunit (r + 1) (by omega)) hfx hdx
    rw [hx] at hres
    exact hres

theorem mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem {f : R} (hf : f ∈ IsLocalRing.maximalIdeal R ^ r) :
    f ∈ IsLocalRing.maximalIdeal R ^ (r + 1) ↔
      ∀ β ∈ multiIndicesOfDegree h r, multiIndexDeriv D β f ∈ IsLocalRing.maximalIdeal R := by
  constructor
  · intro hfs β hβ
    have hβ' : ∑ i, β i = r := (mem_multiIndicesOfDegree β).mp hβ
    have hm := multiIndexDeriv_mem_pow_sub D (IsLocalRing.maximalIdeal R) (r + 1) hfs β
    rw [hβ'] at hm
    have hr1 : r + 1 - r = 1 := by omega
    rw [hr1, pow_one] at hm
    exact hm
  · intro hall
    exact mem_maximalIdeal_pow_succ_of_multiIndexDeriv_mem_consolidated74 x D hx hD hDD hunit r f hf
      (fun β hb => hall β ((mem_multiIndicesOfDegree β).mpr hb))


end

private theorem idealOrder_eq_of_le_of_not_le_consolidated74 {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ}
    {I : Ideal R} (h1 : I ≤ IsLocalRing.maximalIdeal R ^ n)
    (h2 : ¬ I ≤ IsLocalRing.maximalIdeal R ^ (n + 1)) : idealOrder I = (n : ℕ∞) := by
  have h3 : (n : ℕ∞) ≤ idealOrder I := (le_idealOrder_iff I n).mpr h1
  have h4 : ¬ (((n + 1 : ℕ) : ℕ∞) ≤ idealOrder I) := fun hc =>
    h2 ((le_idealOrder_iff I (n + 1)).mp hc)
  rw [not_le] at h4
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt h4)
  rw [← hm] at h3 h4 ⊢
  have hle : n ≤ m := by exact_mod_cast h3
  have hlt : m < n + 1 := by exact_mod_cast h4
  have hme : m = n := by omega
  exact_mod_cast hme

private def ofDigitsFin_consolidated74 (N : ℕ) {h : ℕ} (β : Fin h → ℕ) : ℕ := ∑ i, β i * N ^ (i : ℕ)

section
variable (N : ℕ)

private theorem ofDigits_add_consolidated74 {h : ℕ} (β γ : Fin h → ℕ) :
    ofDigitsFin_consolidated74 N (fun i => β i + γ i) = ofDigitsFin_consolidated74 N β + ofDigitsFin_consolidated74 N γ := by
  simp only [ofDigitsFin_consolidated74, add_mul]
  rw [Finset.sum_add_distrib]

private theorem ofDigits_fin_succ_consolidated74 {n : ℕ} (δ : Fin (n + 1) → ℕ) :
    ofDigitsFin_consolidated74 N δ = δ 0 + (ofDigitsFin_consolidated74 N fun i : Fin n => δ i.succ) * N := by
  simp only [ofDigitsFin_consolidated74]
  rw [Fin.sum_univ_succ, Finset.sum_mul]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.val_succ, pow_succ, mul_assoc]

private theorem ofDigits_injective_of_lt_consolidated74 (hN : 0 < N) : ∀ (h : ℕ) (β γ : Fin h → ℕ),
    (∀ i, β i < N) → (∀ i, γ i < N) → ofDigitsFin_consolidated74 N β = ofDigitsFin_consolidated74 N γ → β = γ := by
  intro h
  induction h with
  | zero =>
    intro β γ _ _ _
    funext i
    exact i.elim0
  | succ n ih =>
    intro β γ hβ hγ hsum
    rw [ofDigits_fin_succ_consolidated74 N β, ofDigits_fin_succ_consolidated74 N γ] at hsum
    have h0 : β 0 = γ 0 := by
      have hmod : (β 0 + (ofDigitsFin_consolidated74 N fun i : Fin n => β i.succ) * N) % N
          = (γ 0 + (ofDigitsFin_consolidated74 N fun i : Fin n => γ i.succ) * N) % N := by rw [hsum]
      rwa [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (hβ 0), Nat.mod_eq_of_lt (hγ 0)] at hmod
    rw [h0] at hsum
    have h1 : (ofDigitsFin_consolidated74 N fun i : Fin n => β i.succ) = ofDigitsFin_consolidated74 N fun i : Fin n => γ i.succ :=
      Nat.eq_of_mul_eq_mul_right hN (Nat.add_left_cancel hsum)
    have h2 := ih _ _ (fun i => hβ i.succ) (fun i => hγ i.succ) h1
    funext i
    refine Fin.cases ?_ ?_ i
    · exact h0
    · intro j
      exact congrFun h2 j


end

private theorem exists_ofDigits_le_of_sum_eq_consolidated74 {h : ℕ} (P : (Fin h → ℕ) → Prop) (r N : ℕ)
    (hex : ∃ β : Fin h → ℕ, (∑ i, β i = r) ∧ P β) :
    ∃ β₀ : Fin h → ℕ, (∑ i, β₀ i = r) ∧ P β₀ ∧
      ∀ β : Fin h → ℕ, (∑ i, β i = r) → P β → ofDigitsFin_consolidated74 N β₀ ≤ ofDigitsFin_consolidated74 N β := by
  classical
  obtain ⟨β₁, hβ₁, hP₁⟩ := hex
  obtain ⟨β₀, hmem, hmin⟩ := Finset.exists_min_image
    ((multiIndicesOfDegree h r).filter P) (ofDigitsFin_consolidated74 N)
    ⟨β₁, Finset.mem_filter.mpr ⟨(mem_multiIndicesOfDegree β₁).mpr hβ₁, hP₁⟩⟩
  rw [Finset.mem_filter, mem_multiIndicesOfDegree] at hmem
  exact ⟨β₀, hmem.1, hmem.2, fun β hβ hPβ =>
    hmin β (Finset.mem_filter.mpr ⟨(mem_multiIndicesOfDegree β).mpr hβ, hPβ⟩)⟩

private theorem sum_notMem_of_unique_notMem_consolidated74 {R : Type*} [CommRing R] {I : Ideal R} {ι : Type*}
    [DecidableEq ι] (t : Finset ι) (F : ι → R) (a : ι) (ha : a ∈ t) (hFa : F a ∉ I)
    (hrest : ∀ b ∈ t, b ≠ a → F b ∈ I) : (∑ b ∈ t, F b) ∉ I := by
  intro hsum
  refine hFa ?_
  have h1 : (∑ b ∈ t.erase a, F b) ∈ I :=
    Ideal.sum_mem _ fun b hb => hrest b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)
  have h2 : F a + ∑ b ∈ t.erase a, F b = ∑ b ∈ t, F b := Finset.add_sum_erase t F ha
  have h3 := sub_mem hsum h1
  rw [← h2, add_sub_cancel_right] at h3
  exact h3

private theorem mul_notMem_maximalIdeal_pow_add_succ_consolidated74 {k R : Type*} [CommRing k] [CommRing R]
    [IsLocalRing R] [Algebra k R] {h : ℕ} (x : Fin h → R) (D : Fin h → Derivation k R R)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hDD : ∀ i j : Fin h, ∀ a : R, D i (D j a) = D j (D i a))
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R))
    {r s : ℕ} {f g : R} (hf : f ∈ IsLocalRing.maximalIdeal R ^ r)
    (hnf : f ∉ IsLocalRing.maximalIdeal R ^ (r + 1))
    (hg : g ∈ IsLocalRing.maximalIdeal R ^ s)
    (hng : g ∉ IsLocalRing.maximalIdeal R ^ (s + 1)) :
    f * g ∉ IsLocalRing.maximalIdeal R ^ (r + s + 1) := by
  have hfex : ∃ β : Fin h → ℕ, (∑ i, β i = r) ∧
      multiIndexDeriv D β f ∉ IsLocalRing.maximalIdeal R := by
    by_contra hcon
    push Not at hcon
    refine hnf ((mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem x D hx hD hDD hunit r hf).mpr ?_)
    intro β hβ
    exact hcon β ((mem_multiIndicesOfDegree β).mp hβ)
  have hgex : ∃ γ : Fin h → ℕ, (∑ i, γ i = s) ∧
      multiIndexDeriv D γ g ∉ IsLocalRing.maximalIdeal R := by
    by_contra hcon
    push Not at hcon
    refine hng ((mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem x D hx hD hDD hunit s hg).mpr ?_)
    intro γ hγ
    exact hcon γ ((mem_multiIndicesOfDegree γ).mp hγ)
  obtain ⟨β₀, hβ₀deg, hβ₀f, hβ₀min⟩ := exists_ofDigits_le_of_sum_eq_consolidated74
    (fun β => multiIndexDeriv D β f ∉ IsLocalRing.maximalIdeal R) r (r + s + 1) hfex
  obtain ⟨γ₀, hγ₀deg, hγ₀g, hγ₀min⟩ := exists_ofDigits_le_of_sum_eq_consolidated74
    (fun γ => multiIndexDeriv D γ g ∉ IsLocalRing.maximalIdeal R) s (r + s + 1) hgex
  obtain ⟨α, hα⟩ : ∃ α : Fin h → ℕ, ∀ i, α i = β₀ i + γ₀ i := ⟨_, fun _ => rfl⟩
  have hαsum : ∑ i, α i = r + s := by
    have hc : ∑ i, α i = ∑ i, (β₀ i + γ₀ i) := Finset.sum_congr rfl fun i _ => hα i
    rw [hc, Finset.sum_add_distrib, hβ₀deg, hγ₀deg]
  have hbase : ofDigitsFin_consolidated74 (r + s + 1) α
      = ofDigitsFin_consolidated74 (r + s + 1) β₀ + ofDigitsFin_consolidated74 (r + s + 1) γ₀ := by
    rw [← ofDigits_add_consolidated74]
    exact congrArg (ofDigitsFin_consolidated74 (r + s + 1)) (funext hα)
  intro hmem
  have hfg : f * g ∈ IsLocalRing.maximalIdeal R ^ (r + s) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hf hg
  have hkey := (mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem x D hx hD hDD hunit (r + s) hfg).mp hmem
    α ((mem_multiIndicesOfDegree α).mpr hαsum)
  have hsub := multiIndexDeriv_mul_sub_sum_mem D (IsLocalRing.maximalIdeal R) r s α hαsum hf hg
  have hT := sub_mem hkey hsub
  rw [sub_sub_cancel] at hT
  refine (sum_notMem_of_unique_notMem_consolidated74 _ _ β₀ ?_ ?_ ?_) hT
  · rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => Finset.mem_range.mpr ?_, hβ₀deg⟩
    have := hα i
    omega
  · have hγeq : (fun i => α i - β₀ i) = γ₀ := by
      funext i
      have := hα i
      omega
    rw [hγeq]
    have hcne : (∏ i, (α i).choose (β₀ i)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro i _
      refine (Nat.choose_pos ?_).ne'
      have := hα i
      omega
    exact IsLocalRing.notMem_maximalIdeal.mpr
      (((hunit _ (Nat.one_le_iff_ne_zero.mpr hcne)).mul
        (IsLocalRing.notMem_maximalIdeal.mp hβ₀f)).mul
        (IsLocalRing.notMem_maximalIdeal.mp hγ₀g))
  · intro β hβt hβne
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hβt
    obtain ⟨hβrange, hβsum⟩ := hβt
    have hβle : ∀ i, β i ≤ α i := fun i =>
      Nat.lt_succ_iff.mp (Finset.mem_range.mp (hβrange i))
    by_cases hcase : multiIndexDeriv D β f ∈ IsLocalRing.maximalIdeal R
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hcase)
    · have hmin1 : ofDigitsFin_consolidated74 (r + s + 1) β₀ ≤ ofDigitsFin_consolidated74 (r + s + 1) β := hβ₀min β hβsum hcase
      have hbβ : ∀ i, β i < r + s + 1 := by
        intro i
        have h1 : β i ≤ r := by
          rw [← hβsum]
          exact Finset.single_le_sum (f := β) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      have hbβ₀ : ∀ i, β₀ i < r + s + 1 := by
        intro i
        have h1 : β₀ i ≤ r := by
          rw [← hβ₀deg]
          exact Finset.single_le_sum (f := β₀) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      have hne : ofDigitsFin_consolidated74 (r + s + 1) β₀ ≠ ofDigitsFin_consolidated74 (r + s + 1) β := fun heq =>
        hβne (ofDigits_injective_of_lt_consolidated74 (r + s + 1) (by omega) h β β₀ hbβ hbβ₀ heq.symm)
      have hstrict : ofDigitsFin_consolidated74 (r + s + 1) β₀ < ofDigitsFin_consolidated74 (r + s + 1) β :=
        lt_of_le_of_ne hmin1 hne
      have hγsum : ∑ i, (α i - β i) = s := by
        have h1 : ∑ i, ((α i - β i) + β i) = ∑ i, α i :=
          Finset.sum_congr rfl fun i _ => by
            have := hβle i
            omega
        rw [Finset.sum_add_distrib, hβsum, hαsum] at h1
        omega
      have hsplit : ofDigitsFin_consolidated74 (r + s + 1) β + ofDigitsFin_consolidated74 (r + s + 1) (fun i => α i - β i)
          = ofDigitsFin_consolidated74 (r + s + 1) α := by
        rw [← ofDigits_add_consolidated74]
        exact congrArg (ofDigitsFin_consolidated74 (r + s + 1)) (funext fun i => by
          show β i + (α i - β i) = α i
          have := hβle i
          omega)
      have hγlt : ofDigitsFin_consolidated74 (r + s + 1) (fun i => α i - β i) < ofDigitsFin_consolidated74 (r + s + 1) γ₀ := by
        omega
      have hgmem : multiIndexDeriv D (fun i => α i - β i) g ∈ IsLocalRing.maximalIdeal R := by
        by_contra hcon2
        exact absurd (hγ₀min _ hγsum hcon2) (by omega)
      exact Ideal.mul_mem_left _ _ hgmem

section
variable {k R : Type*} [CommRing k] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra k R] {h : ℕ} (x : Fin h → R) (D : Fin h → Derivation k R R) (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R) (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) (hDD : ∀ i j : Fin h, ∀ a : R, D i (D j a) = D j (D i a)) (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R))
include hx hD hDD hunit

theorem idealOrder_mul (I J : Ideal R) :
    idealOrder (I * J) = idealOrder I + idealOrder J := by
  by_cases hI : I = ⊥
  · subst hI
    have hbm : (⊥ : Ideal R) * J = ⊥ := by
      refine le_antisymm (Ideal.mul_le.mpr ?_) bot_le
      intro a ha b _
      rw [Ideal.mem_bot] at ha ⊢
      rw [ha, zero_mul]
    rw [hbm, idealOrder_bot]
    exact le_antisymm le_self_add le_top
  · by_cases hJ : J = ⊥
    · subst hJ
      have hbm : I * (⊥ : Ideal R) = ⊥ := by
        refine le_antisymm (Ideal.mul_le.mpr ?_) bot_le
        intro a _ b hb
        rw [Ideal.mem_bot] at hb ⊢
        rw [hb, mul_zero]
      rw [hbm, idealOrder_bot]
      exact le_antisymm le_add_self le_top
    · obtain ⟨r, hr⟩ := exists_idealOrder_eq_coe hI
      obtain ⟨s, hs⟩ := exists_idealOrder_eq_coe hJ
      have hIr : I ≤ IsLocalRing.maximalIdeal R ^ r :=
        (le_idealOrder_iff I r).mp (le_of_eq hr.symm)
      have hJs : J ≤ IsLocalRing.maximalIdeal R ^ s :=
        (le_idealOrder_iff J s).mp (le_of_eq hs.symm)
      have hIn : ¬ I ≤ IsLocalRing.maximalIdeal R ^ (r + 1) := by
        intro hc
        have hle := (le_idealOrder_iff I (r + 1)).mpr hc
        rw [hr] at hle
        have hnat : r + 1 ≤ r := by exact_mod_cast hle
        omega
      have hJn : ¬ J ≤ IsLocalRing.maximalIdeal R ^ (s + 1) := by
        intro hc
        have hle := (le_idealOrder_iff J (s + 1)).mpr hc
        rw [hs] at hle
        have hnat : s + 1 ≤ s := by exact_mod_cast hle
        omega
      obtain ⟨a, haI, han⟩ : ∃ a ∈ I, a ∉ IsLocalRing.maximalIdeal R ^ (r + 1) := by
        by_contra hc
        push Not at hc
        exact hIn fun y hy => hc y hy
      obtain ⟨b, hbJ, hbn⟩ : ∃ b ∈ J, b ∉ IsLocalRing.maximalIdeal R ^ (s + 1) := by
        by_contra hc
        push Not at hc
        exact hJn fun y hy => hc y hy
      have hmul : a * b ∉ IsLocalRing.maximalIdeal R ^ (r + s + 1) :=
        mul_notMem_maximalIdeal_pow_add_succ_consolidated74 x D hx hD hDD hunit (hIr haI) han (hJs hbJ) hbn
      have h1 : ¬ I * J ≤ IsLocalRing.maximalIdeal R ^ (r + s + 1) := fun hc =>
        hmul (hc (Ideal.mul_mem_mul haI hbJ))
      have h2 : I * J ≤ IsLocalRing.maximalIdeal R ^ (r + s) := by
        rw [pow_add]
        exact Ideal.mul_mono hIr hJs
      rw [idealOrder_eq_of_le_of_not_le_consolidated74 h2 h1, hr, hs]
      exact Nat.cast_add r s

theorem idealOrder_pow (I : Ideal R) (c : ℕ) :
    idealOrder (I ^ c) = (c : ℕ∞) * idealOrder I := by
  induction c with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, idealOrder_top]
    simp
  | succ c ih =>
    rw [pow_succ, idealOrder_mul x D hx hD hDD hunit, ih, Nat.cast_add, Nat.cast_one, add_mul,
      one_mul]


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealLocalization
section

variable (k : Type*) [CommRing k]
variable {S : Type*} [CommRing S] [Algebra k S]
variable {S' : Type*} [CommRing S'] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']

section
variable {R : Type*} [CommRing R] {A : Type*} [CommRing A]

private theorem derivation_mem_map_of_forall_mem_consolidated69 {B : Type*} [CommRing B] [Algebra A B] [Algebra R B]
    (D' : Derivation R B B) {P : Ideal A}
    (hgen : ∀ p ∈ P, D' (algebraMap A B p) ∈ P.map (algebraMap A B)) :
    ∀ x ∈ P.map (algebraMap A B), D' x ∈ P.map (algebraMap A B) := by
  intro x hx
  have hx' : x ∈ Ideal.span ((algebraMap A B) '' (P : Set A)) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      exact hgen p hp
  | zero => simp
  | add y z hy hz ihy ihz =>
      have h : D' (y + z) = D' y + D' z := by simp
      rw [h]
      exact Ideal.add_mem _ ihy ihz
  | smul a y hy ih =>
      have hy' : y ∈ P.map (algebraMap A B) := hy
      rw [smul_eq_mul, D'.leibniz]
      simp only [smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) (Ideal.mul_mem_right _ _ hy')

private theorem derivation_smul_apply_consolidated69 [Algebra R A] (c : A) (D₀ : Derivation R A A) (x : A) : (c • D₀) x = c * D₀ x := rfl

private theorem mul_derivation_mem_of_span_eq_consolidated69 [Algebra R A] {G : Set A} {P : Ideal A} (hP : Ideal.span G = P) (D₀ : Derivation R A A)
    (c : A) (hG : ∀ g ∈ G, c * D₀ g ∈ P) : ∀ x ∈ P, c * D₀ x ∈ P := by
  intro x hx
  rw [← hP] at hx
  induction hx using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add y z hy hz ihy ihz =>
      have h : D₀ (y + z) = D₀ y + D₀ z := by simp
      rw [h, mul_add]
      exact P.add_mem ihy ihz
  | smul a y hy ih =>
      have hyP : y ∈ P := by rw [← hP]; exact hy
      rw [smul_eq_mul, D₀.leibniz]
      simp only [smul_eq_mul, mul_add]
      refine P.add_mem ?_ ?_
      · have h1 : c * (a * D₀ y) = a * (c * D₀ y) := by ring
        rw [h1]
        exact P.mul_mem_left a ih
      · exact P.mul_mem_left c (P.mul_mem_right (D₀ a) hyP)


end

section
variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B] (M : Submonoid A) [IsLocalization M B]

private theorem exists_mem_mul_algebraMap_eq_of_mem_map_consolidated69 (J : Ideal A) {x : B}
    (hx : x ∈ J.map (algebraMap A B)) :
    ∃ (y : A) (t : M), y ∈ J ∧ x * algebraMap A B (t : A) = algebraMap A B y := by
  obtain ⟨u, hu⟩ := (IsLocalization.mem_map_algebraMap_iff (M := M) (S := B)).mp hx
  exact ⟨u.1, u.2, u.1.2, hu⟩

private theorem exists_mul_mem_of_algebraMap_mem_map_consolidated69 (P : Ideal A) {y : A}
    (hy : algebraMap A B y ∈ P.map (algebraMap A B)) :
    ∃ m : M, (m : A) * y ∈ P := by
  obtain ⟨p, t, hp, h⟩ := exists_mem_mul_algebraMap_eq_of_mem_map_consolidated69 M P hy
  have h2 : algebraMap A B (y * (t : A)) = algebraMap A B p := by
    rw [map_mul]; linear_combination h
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (M := M) (S := B)).mp h2
  refine ⟨c * t, ?_⟩
  have heq : ((c * t : M) : A) * y = (c : A) * p := by
    push_cast
    linear_combination hc
  rw [heq]
  exact P.mul_mem_left _ hp


end

section
variable (M : Submonoid S) [IsLocalization M S']
include M

theorem mapToLocalization_mem_tangentDerivations {P : Ideal S} {D : Derivation k S S} (hD : D ∈ tangentDerivations k P) :
    (D.mapToLocalization (S' := S') M) ∈
      tangentDerivations k (P.map (algebraMap S S')) := by
  have hD' := (mem_tangentDerivations k P D).mp hD
  rw [mem_tangentDerivations]
  refine derivation_mem_map_of_forall_mem_consolidated69 (D.mapToLocalization (S' := S') M) ?_
  intro p hp
  rw [Derivation.mapToLocalization_algebraMap]
  exact Ideal.mem_map_of_mem _ (hD' p hp)

theorem map_logDerivIdeal_le (P J : Ideal S) :
    (logDerivIdeal k P J).map (algebraMap S S') ≤
      logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) := by
  rw [Ideal.map_le_iff_le_comap, logDerivIdeal_le_iff]
  constructor
  · intro x hx
    rw [Ideal.mem_comap]
    exact le_logDerivIdeal k _ _ (Ideal.mem_map_of_mem _ hx)
  · intro D hD x hx
    rw [Ideal.mem_comap]
    have h : algebraMap S S' (D x) =
        (D.mapToLocalization (S' := S') M) (algebraMap S S' x) := by
      rw [Derivation.mapToLocalization_algebraMap]
    rw [h]
    exact derivation_apply_mem_logDerivIdeal k _ _ _
      (mapToLocalization_mem_tangentDerivations (S' := S') k M hD)
      (Ideal.mem_map_of_mem _ hx)


end

section
variable (M : Submonoid S) [IsLocalization M S'] [Module.FinitePresentation S (KaehlerDifferential k S)] {P : Ideal S} (hP : P.FG)
include M hP

theorem exists_mem_tangentDerivations_mul_eq (D : Derivation k S' S')
    (hD : D ∈ tangentDerivations k (P.map (algebraMap S S'))) :
    ∃ (m : M) (D₁ : Derivation k S S), D₁ ∈ tangentDerivations k P ∧
      ∀ s : S, algebraMap S S' (m : S) * D (algebraMap S S' s) = algebraMap S S' (D₁ s) := by
  have hDt := (mem_tangentDerivations k (P.map (algebraMap S S')) D).mp hD
  obtain ⟨m₀, D₀, hD₀⟩ :=
    Derivation.exists_derivation_mul_eq_of_isLocalization (S' := S') M D
  obtain ⟨G, hG⟩ := hP
  have key : ∀ g : S, ∃ n : M, g ∈ G → (n : S) * D₀ g ∈ P := by
    intro g
    by_cases hg : g ∈ G
    · have hgP : g ∈ P := by
        rw [← hG]
        exact Ideal.subset_span (Finset.mem_coe.mpr hg)
      have h1 : algebraMap S S' g ∈ P.map (algebraMap S S') := Ideal.mem_map_of_mem _ hgP
      have h2 : D (algebraMap S S' g) ∈ P.map (algebraMap S S') := hDt _ h1
      have h3 : algebraMap S S' (D₀ g) ∈ P.map (algebraMap S S') := by
        rw [← hD₀ g]
        exact Ideal.mul_mem_left _ _ h2
      obtain ⟨n, hn⟩ := exists_mul_mem_of_algebraMap_mem_map_consolidated69 M P h3
      exact ⟨n, fun _ => hn⟩
    · exact ⟨1, fun h => absurd h hg⟩
  choose f hf using key
  obtain ⟨c, hcM, hcP⟩ : ∃ c : S, c ∈ M ∧ ∀ g ∈ G, c * D₀ g ∈ P := by
    refine ⟨Finset.prod G (fun g => ((f g : S))),
      Submonoid.prod_mem M (fun g _ => (f g).2), ?_⟩
    intro g hg
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun g => ((f g : S))) hg
    have h4 : ((f g : S)) * r * D₀ g = r * (((f g : S)) * D₀ g) := by ring
    rw [hr, h4]
    exact P.mul_mem_left _ (hf g hg)
  refine ⟨⟨c * (m₀ : S), M.mul_mem hcM m₀.2⟩, c • D₀, ?_, ?_⟩
  · have hgen : ∀ g ∈ (↑G : Set S), c * D₀ g ∈ P := fun g hg => hcP g (Finset.mem_coe.mp hg)
    rw [mem_tangentDerivations]
    intro x hx
    have h := mul_derivation_mem_of_span_eq_consolidated69 hG D₀ c hgen x hx
    rw [derivation_smul_apply_consolidated69]
    exact h
  · intro s
    show algebraMap S S' (c * (m₀ : S)) * D (algebraMap S S' s)
        = algebraMap S S' ((c • D₀) s)
    rw [derivation_smul_apply_consolidated69, map_mul, map_mul, mul_assoc, hD₀ s]

theorem logDerivIdeal_map_le_map_logDerivIdeal (J : Ideal S) :
    logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) ≤
      (logDerivIdeal k P J).map (algebraMap S S') := by
  rw [logDerivIdeal_le_iff]
  refine ⟨Ideal.map_mono (le_logDerivIdeal k P J), ?_⟩
  intro D hD x hx
  obtain ⟨m, D₁, hD₁, hm⟩ := exists_mem_tangentDerivations_mul_eq k M hP D hD
  obtain ⟨y, t, hy, hxt⟩ := exists_mem_mul_algebraMap_eq_of_mem_map_consolidated69 M J hx
  have hxL : x ∈ (logDerivIdeal k P J).map (algebraMap S S') :=
    Ideal.map_mono (le_logDerivIdeal k P J) hx
  have h1 : D (x * algebraMap S S' (t : S)) = D (algebraMap S S' y) := by rw [hxt]
  rw [D.leibniz] at h1
  simp only [smul_eq_mul] at h1
  have e1 := hm y
  have e2 := hm (t : S)
  have hmul : algebraMap S S' ((m : S) * (t : S)) * D x
      = algebraMap S S' (D₁ y) - x * algebraMap S S' (D₁ (t : S)) := by
    rw [map_mul]
    linear_combination algebraMap S S' (m : S) * h1 + e1 - x * e2
  have hmem : algebraMap S S' ((m : S) * (t : S)) * D x ∈
      (logDerivIdeal k P J).map (algebraMap S S') := by
    rw [hmul]
    refine sub_mem ?_ ?_
    · exact Ideal.mem_map_of_mem _ (derivation_apply_mem_logDerivIdeal k P J D₁ hD₁ hy)
    · exact Ideal.mul_mem_right _ _ hxL
  have hu : IsUnit (algebraMap S S' ((m : S) * (t : S))) := by
    rw [map_mul]
    exact (IsLocalization.map_units (M := M) (S := S') m).mul
      (IsLocalization.map_units (M := M) (S := S') t)
  obtain ⟨u, hu'⟩ := hu
  have hrw : D x = (↑u⁻¹ : S') * (algebraMap S S' ((m : S) * (t : S)) * D x) := by
    rw [← hu', ← mul_assoc, Units.inv_mul, one_mul]
  rw [hrw]
  exact Ideal.mul_mem_left _ _ hmem

theorem logDerivIdeal_map (J : Ideal S) :
    (logDerivIdeal k P J).map (algebraMap S S') =
      logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) :=
  le_antisymm (map_logDerivIdeal_le k M P J) (logDerivIdeal_map_le_map_logDerivIdeal k M hP J)

theorem logDerivIdealIterate_map (r : ℕ) (J : Ideal S) :
    (logDerivIdealIterate k P r J).map (algebraMap S S') =
      logDerivIdealIterate k (P.map (algebraMap S S')) r (J.map (algebraMap S S')) := by
  induction r with
  | zero => rw [logDerivIdealIterate_zero, logDerivIdealIterate_zero]
  | succ r ih =>
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ, logDerivIdeal_map k M hP, ih]


end

section
variable (g : S) [IsLocalization.Away g S'] [Module.FinitePresentation S (KaehlerDifferential k S)] {P : Ideal S} (hP : P.FG)
include g hP

theorem logDerivIdeal_map_away (J : Ideal S) :
    (logDerivIdeal k P J).map (algebraMap S S') =
      logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) :=
  logDerivIdeal_map k (Submonoid.powers g) hP J

theorem logDerivIdealIterate_map_away (r : ℕ) (J : Ideal S) :
    (logDerivIdealIterate k P r J).map (algebraMap S S') =
      logDerivIdealIterate k (P.map (algebraMap S S')) r (J.map (algebraMap S S')) :=
  logDerivIdealIterate_map k (Submonoid.powers g) hP r J


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealQuotient
section

variable (k : Type*) [CommRing k] {S T : Type*} [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T]

section
variable (f : S →ₐ[k] T) (hf : Function.Surjective f)
include hf

theorem map_logDerivIdeal_ker_le_derivIdeal_map (J : Ideal S) :
    Ideal.map f.toRingHom (logDerivIdeal k (RingHom.ker f.toRingHom) J)
      ≤ derivIdeal k (Ideal.map f.toRingHom J) := by
  rw [Ideal.map_le_iff_le_comap, logDerivIdeal_le_iff]
  constructor
  · intro x hx
    rw [Ideal.mem_comap]
    exact le_derivIdeal k (Ideal.map f.toRingHom J) (Ideal.mem_map_of_mem f.toRingHom hx)
  · intro D hD x hx
    have hD' : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom :=
      (mem_tangentDerivations k (RingHom.ker f.toRingHom) D).mp hD
    have hmem : f x ∈ Ideal.map f.toRingHom J := Ideal.mem_map_of_mem f.toRingHom hx
    have h2 := derivation_apply_mem_derivIdeal k (Ideal.map f.toRingHom J)
      (derivationOfSurjective f hf D hD') hmem
    rw [derivationOfSurjective_apply] at h2
    rw [Ideal.mem_comap]
    exact h2

theorem map_logDerivIdealIterate_ker_le_derivIdealIterate_map (r : ℕ) (J : Ideal S) :
    Ideal.map f.toRingHom (logDerivIdealIterate k (RingHom.ker f.toRingHom) r J)
      ≤ derivIdealIterate k r (Ideal.map f.toRingHom J) := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
      rw [logDerivIdealIterate_succ, derivIdealIterate_succ]
      exact (map_logDerivIdeal_ker_le_derivIdeal_map k f hf _).trans (derivIdeal_mono k ih)

theorem map_logDerivIdealIterate_le_derivIdealIterate_map_of_eq_ker {P : Ideal S} (hP : P = RingHom.ker f.toRingHom)
    (r : ℕ) (J : Ideal S) :
    Ideal.map f.toRingHom (logDerivIdealIterate k P r J)
      ≤ derivIdealIterate k r (Ideal.map f.toRingHom J) := by
  subst hP
  exact map_logDerivIdealIterate_ker_le_derivIdealIterate_map k f hf r J


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
section

open AlgebraicGeometry CategoryTheory TopologicalSpace


noncomputable def stalkAlgebraMap (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (x : X) : k →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x (Opens.mem_top x)).hom.comp (sectionsAlgebraMap k p ⊤)

@[reducible] noncomputable def stalkAlgebra (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (x : X) : Algebra k (X.presheaf.stalk x) :=
  (stalkAlgebraMap k p x).toAlgebra

theorem algebraMap_stalkAlgebra (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    @algebraMap k (X.presheaf.stalk x) _ _ (stalkAlgebra k p x) = stalkAlgebraMap k p x :=
  rfl

section
variable (k : Type u) [CommRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (x : X) (hx : x ∈ U)

theorem sectionsAlgebraMap_comp_germ :
    (X.presheaf.germ U x hx).hom.comp (sectionsAlgebraMap k p U) = stalkAlgebraMap k p x := by
  have hle : U ≤ (⊤ : X.Opens) := le_top
  have key : X.presheaf.map (homOfLE hle).op ≫ X.presheaf.germ U x hx
      = X.presheaf.germ (⊤ : X.Opens) x (Opens.mem_top x) := by
    simp
  have key' : (X.presheaf.germ U x hx).hom.comp (X.presheaf.map (homOfLE hle).op).hom
      = (X.presheaf.germ (⊤ : X.Opens) x (Opens.mem_top x)).hom := by
    rw [← CommRingCat.hom_comp, key]
  show (X.presheaf.germ U x hx).hom.comp (sectionsAlgebraMap k p U)
      = (X.presheaf.germ (⊤ : X.Opens) x (Opens.mem_top x)).hom.comp (sectionsAlgebraMap k p ⊤)
  rw [← key', RingHom.comp_assoc, sectionsAlgebraMap_comp_restrict k p hle]

theorem germ_sectionsAlgebraMap_apply (a : k) :
    (X.presheaf.germ U x hx).hom (sectionsAlgebraMap k p U a) = stalkAlgebraMap k p x a :=
  DFunLike.congr_fun (sectionsAlgebraMap_comp_germ k p U x hx) a

theorem isScalarTower_stalk [Algebra k Γ(X, U)] [Algebra k (X.presheaf.stalk x)] [Algebra Γ(X, U) (X.presheaf.stalk x)]
    (hU : algebraMap k Γ(X, U) = sectionsAlgebraMap k p U)
    (hstalk : algebraMap k (X.presheaf.stalk x) = stalkAlgebraMap k p x)
    (hgerm : algebraMap Γ(X, U) (X.presheaf.stalk x) = (X.presheaf.germ U x hx).hom) :
    IsScalarTower k Γ(X, U) (X.presheaf.stalk x) := by
  refine IsScalarTower.of_algebraMap_eq' ?_
  rw [hstalk, hgerm, hU, sectionsAlgebraMap_comp_germ]


end

section
variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]

theorem stalkIdeal_derivIdealSheaf (I : X.IdealSheafData) (x : X) :
    stalkIdeal (derivIdealSheaf k p I) x =
      @derivIdeal k _ _ _ (stalkAlgebra k p x) (stalkIdeal I x) := by
  rcases isEmpty_or_nonempty {U : X.affineOpens // x ∈ U.1.1} with hE | ⟨⟨U, hx⟩⟩
  · have h1 : ∀ J : X.IdealSheafData, stalkIdeal J x = ⊥ := fun J =>
      iSup_of_empty (fun U : {U : X.affineOpens // x ∈ U.1.1} =>
        Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (J.ideal U.1))
    rw [h1 (derivIdealSheaf k p I), h1 I]
    exact (@derivIdeal_bot k _ _ _ (stalkAlgebra k p x)).symm
  · have hU : IsAffineOpen U.1 := U.2
    let algk : Algebra k Γ(X, U.1) := sectionsAlgebra k p U.1
    let algst : Algebra k (X.presheaf.stalk x) := stalkAlgebra k p x
    let algS : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
      (X.presheaf.germ U.1 x hx).hom.toAlgebra
    have : IsScalarTower k Γ(X, U.1) (X.presheaf.stalk x) :=
      isScalarTower_stalk k p U.1 x hx rfl rfl rfl
    have : Module.FinitePresentation Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) :=
      finitePresentation_kaehlerDifferential_sections k p U rfl
    have _hloc : IsLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
        (X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hx⟩
    rw [stalkIdeal_eq_map_germ (derivIdealSheaf k p I) x U hx,
      stalkIdeal_eq_map_germ I x U hx, derivIdealSheaf_ideal]
    exact map_derivIdeal (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (I.ideal U)

theorem stalkIdeal_derivIdealSheafIterate (r : ℕ)
    (I : X.IdealSheafData) (x : X) :
    stalkIdeal (derivIdealSheafIterate k p r I) x =
      @derivIdealIterate k _ _ _ (stalkAlgebra k p x) r (stalkIdeal I x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      have h := stalkIdeal_derivIdealSheaf k p (derivIdealSheafIterate k p r I) x
      rw [derivIdealSheafIterate_succ, h, ih, derivIdealIterate_succ]

theorem le_orderAt_derivIdealSheafIterate (I : X.IdealSheafData) (x : X) (n r : ℕ) (h : ((n + r : ℕ) : ℕ∞) ≤ orderAt I x) :
    (n : ℕ∞) ≤ orderAt (derivIdealSheafIterate k p r I) x := by
  rw [le_orderAt_iff] at h ⊢
  rw [stalkIdeal_derivIdealSheafIterate k p r I x]
  have key := @derivIdealIterate_le_pow_of_le_pow k _ _ _ (stalkAlgebra k p x)
    (stalkIdeal I x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (n + r) r h
  rwa [Nat.add_sub_cancel] at key

theorem orderAtLeastLocus_subset_orderAtLeastLocus_derivIdealSheafIterate (I : X.IdealSheafData) (r m : ℕ) :
    orderAtLeastLocus I m ⊆ orderAtLeastLocus (derivIdealSheafIterate k p r I) (m - r) := by
  rcases Nat.lt_or_ge m r with h | h
  · rw [show m - r = 0 from Nat.sub_eq_zero_of_le (le_of_lt h), orderAtLeastLocus_zero]
    exact Set.subset_univ _
  · intro x hx
    rw [mem_orderAtLeastLocus_iff] at hx ⊢
    refine le_orderAt_derivIdealSheafIterate k p I x (m - r) r ?_
    rw [Nat.sub_add_cancel h]
    exact hx


end

private theorem formallySmooth_of_ringEquiv_consolidated102 (k : Type u) [CommRing k] (R : Type u)
    [CommRing R] [Algebra k R] (e : k ≃+* R) (he : ∀ x : k, e x = algebraMap k R x) :
    Algebra.FormallySmooth k R := by
  have : Algebra.FormallySmooth k k := inferInstance
  exact Algebra.FormallySmooth.of_equiv (AlgEquiv.ofRingEquiv (f := e) (fun x => he x))

section
variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
include p

theorem formallySmooth_sections (U : X.Opens)
    (hU : IsAffineOpen U) [Algebra k Γ(X, U)]
    (h : algebraMap k Γ(X, U) = sectionsAlgebraMap k p U) :
    Algebra.FormallySmooth k Γ(X, U) := by
  have hQ : RingHom.Smooth (p.appLE ⊤ U (le_preimage_top k p U)).hom :=
    (AlgebraicGeometry.smooth_iff p).mp ‹Smooth p›
      (isAffineOpen_top (Spec (CommRingCat.of k))) hU (le_preimage_top k p U)
  let algSections : Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) :=
    (p.appLE ⊤ U (le_preimage_top k p U)).hom.toAlgebra
  have hS : Algebra.Smooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) := hQ
  have : Algebra.FormallySmooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) := hS.formallySmooth
  let algGlobal : Algebra k Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toAlgebra
  have : Algebra.FormallySmooth k Γ(Spec (CommRingCat.of k), ⊤) :=
    formallySmooth_of_ringEquiv_consolidated102 k Γ(Spec (CommRingCat.of k), ⊤)
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv (fun _ => rfl)
  have : IsScalarTower k Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq' (h.trans rfl)
  exact Algebra.FormallySmooth.comp k Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U)

private theorem isNoetherianRing_sections_of_smooth_consolidated102 (U : X.Opens)
    (hU : IsAffineOpen U) : IsNoetherianRing Γ(X, U) := by
  have : IsNoetherianRing k := inferInstance
  have hQ : RingHom.Smooth (p.appLE ⊤ U (le_preimage_top k p U)).hom :=
    (AlgebraicGeometry.smooth_iff p).mp ‹Smooth p›
      (isAffineOpen_top (Spec (CommRingCat.of k))) hU (le_preimage_top k p U)
  let algSections : Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) :=
    (p.appLE ⊤ U (le_preimage_top k p U)).hom.toAlgebra
  have hS : Algebra.Smooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) := hQ
  have e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ(Spec (CommRingCat.of k), ⊤) :=
    isNoetherianRing_of_surjective k (↥Γ(Spec (CommRingCat.of k), ⊤)) e.toRingHom e.surjective
  obtain ⟨n, f, hf, -⟩ := hS.finitePresentation
  exact isNoetherianRing_of_surjective
    (MvPolynomial (Fin n) (↥Γ(Spec (CommRingCat.of k), ⊤))) (↥Γ(X, U)) f.toRingHom hf

theorem isNoetherianRing_stalk (x : X) :
    IsNoetherianRing (X.presheaf.stalk x) := by
  have : IsLocallyNoetherian X := ⟨fun U => isNoetherianRing_sections_of_smooth_consolidated102 k p U.1 U.2⟩
  infer_instance


end

private theorem exists_isAffineOpen_mem_consolidated102 (X : Scheme.{u}) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U :=
  ⟨(X.affineCover.f (X.affineCover.idx x)).opensRange, X.affineCover.covers x,
    isAffineOpen_opensRange _⟩

theorem formallySmooth_stalk (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (x : X) :
    @Algebra.FormallySmooth k _ _ _ (stalkAlgebra k p x) := by
  obtain ⟨U, hxU, hU⟩ := exists_isAffineOpen_mem_consolidated102 X x
  let algU : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let algStalk : Algebra k (X.presheaf.stalk x) := stalkAlgebra k p x
  let algGerm : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  have _tower : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) :=
    isScalarTower_stalk k p U x hxU rfl rfl rfl
  have _fsU : Algebra.FormallySmooth k Γ(X, U) := formallySmooth_sections k p U hU rfl
  have _loc : IsLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hxU⟩
  have _fsStalk : Algebra.FormallySmooth Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.FormallySmooth.of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  exact Algebra.FormallySmooth.comp k Γ(X, U) (X.presheaf.stalk x)

private theorem finite_kaehlerDifferential_of_isLocalization_consolidated102 (k A B : Type u) [CommRing k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (M : Submonoid A) [IsLocalization M B]
    (hfin : Module.Finite A (KaehlerDifferential k A)) :
    Module.Finite B (KaehlerDifferential k B) := by
  have := hfin
  have : IsLocalizedModule M (KaehlerDifferential.map k k A B) := inferInstance
  have hbc : IsBaseChange B (KaehlerDifferential.map k k A B) :=
    IsLocalizedModule.isBaseChange M B (KaehlerDifferential.map k k A B)
  have : Module.Finite B (TensorProduct A B (KaehlerDifferential k A)) := inferInstance
  exact Module.Finite.equiv hbc.equiv

section
variable (k : Type u) [Field k]

theorem finite_kaehlerDifferential_stalk {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (x : X) :
    letI := stalkAlgebra k p x
    Module.Finite (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) := by
  let algStalk : Algebra k (X.presheaf.stalk x) := stalkAlgebra k p x
  show Module.Finite (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x))
  obtain ⟨U, hxU, hUaff⟩ := exists_isAffineOpen_mem_consolidated102 X x
  let algSections : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let algGerm : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  have : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) :=
    isScalarTower_stalk k p U x hxU rfl rfl rfl
  have : IsLocalization (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) := hUaff.isLocalization_stalk ⟨x, hxU⟩
  have : Module.FinitePresentation Γ(X, U) (KaehlerDifferential k Γ(X, U)) :=
    finitePresentation_kaehlerDifferential_sections k p ⟨U, hUaff⟩ rfl
  exact finite_kaehlerDifferential_of_isLocalization_consolidated102 k Γ(X, U) (X.presheaf.stalk x)
    (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl inferInstance

private theorem free_kaehlerDifferential_of_formallySmooth_consolidated102 (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FormallySmooth k A]
    [Module.Finite A (KaehlerDifferential k A)] :
    Module.Free A (KaehlerDifferential k A) := by
  have _h1 : Module.FinitePresentation A (KaehlerDifferential k A) :=
    Module.finitePresentation_of_finite ..
  have _h2 : Module.Projective A (KaehlerDifferential k A) := inferInstance
  have _h3 : Module.Flat A (KaehlerDifferential k A) := inferInstance
  exact Module.free_of_flat_of_isLocalRing

theorem free_kaehlerDifferential_stalk {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (x : X) :
    letI := stalkAlgebra k p x
    Module.Free (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) := by
  let algst : Algebra k (X.presheaf.stalk x) := stalkAlgebra k p x
  have _hN : IsNoetherianRing (X.presheaf.stalk x) := isNoetherianRing_stalk k p x
  have _hFS : Algebra.FormallySmooth k (X.presheaf.stalk x) := formallySmooth_stalk k p x
  have _hFin : Module.Finite (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) :=
    finite_kaehlerDifferential_stalk k p x
  exact free_kaehlerDifferential_of_formallySmooth_consolidated102 k (X.presheaf.stalk x)

theorem isUnit_natCast_stalk [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (x : X) {n : ℕ} (hn : 1 ≤ n) :
    IsUnit ((n : ℕ) : X.presheaf.stalk x) := by
  have hne : ((n : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk : IsUnit ((n : ℕ) : k) := IsUnit.mk0 _ hne
  have h := hk.map (stalkAlgebraMap k p x)
  rwa [map_natCast] at h


end

section
variable (k : Type u) [Field k] [CharZero k] (L : Type u) [Field L] [Algebra k L]

private theorem formallySmooth_of_isAlgebraic_consolidated102 (A₀ : Type u) [CommRing A₀] [IsDomain A₀] [Algebra k A₀] [Algebra A₀ L]
    [IsScalarTower k A₀ L] [Algebra.FormallySmooth k A₀] [Algebra.IsAlgebraic A₀ L]
    (hinj : Function.Injective (algebraMap A₀ L)) :
    Algebra.FormallySmooth k L := by
  have hunit : ∀ y : nonZeroDivisors A₀, IsUnit (algebraMap A₀ L y) := by
    intro y
    refine isUnit_iff_ne_zero.mpr (fun hy => ?_)
    have h0 : (y : A₀) = 0 := hinj (by rw [hy, map_zero])
    exact nonZeroDivisors.coe_ne_zero y h0
  let algFL : Algebra (FractionRing A₀) L := (IsLocalization.lift hunit).toAlgebra
  have _twr1 : IsScalarTower k A₀ (FractionRing A₀) := inferInstance
  have _twr2 : IsScalarTower A₀ (FractionRing A₀) L :=
    IsScalarTower.of_algebraMap_eq (fun a => (IsLocalization.lift_eq hunit a).symm)
  have _twr3 : IsScalarTower k (FractionRing A₀) L := by
    refine IsScalarTower.of_algebraMap_eq (fun c => ?_)
    rw [IsScalarTower.algebraMap_apply k A₀ (FractionRing A₀) c,
      ← IsScalarTower.algebraMap_apply A₀ (FractionRing A₀) L,
      ← IsScalarTower.algebraMap_apply k A₀ L]
  have _fs1 : Algebra.FormallySmooth A₀ (FractionRing A₀) :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors A₀)
  have _fs2 : Algebra.FormallySmooth k (FractionRing A₀) :=
    Algebra.FormallySmooth.comp k A₀ (FractionRing A₀)
  have _hchar : CharZero (FractionRing A₀) :=
    charZero_of_injective_algebraMap (RingHom.injective (algebraMap k (FractionRing A₀)))
  have _halgF : Algebra.IsAlgebraic (FractionRing A₀) L := by
    refine ⟨fun a => ?_⟩
    obtain ⟨q, hq0, hqa⟩ := (Algebra.IsAlgebraic.isAlgebraic a : IsAlgebraic A₀ a)
    refine ⟨q.map (algebraMap A₀ (FractionRing A₀)), ?_, ?_⟩
    · exact (Polynomial.map_ne_zero_iff
        (IsFractionRing.injective A₀ (FractionRing A₀))).mpr hq0
    · rw [Polynomial.aeval_map_algebraMap]
      exact hqa
  have _hsep : Algebra.IsSeparable (FractionRing A₀) L := by
    refine ⟨fun a => ?_⟩
    exact (minpoly.irreducible
      ((Algebra.IsAlgebraic.isAlgebraic a : IsAlgebraic (FractionRing A₀) a).isIntegral)).separable
  have _fet : Algebra.FormallyEtale (FractionRing A₀) L :=
    Algebra.FormallyEtale.of_isSeparable ..
  have _fs3 : Algebra.FormallySmooth (FractionRing A₀) L := inferInstance
  exact Algebra.FormallySmooth.comp k (FractionRing A₀) L

private theorem formallySmooth_of_isTranscendenceBasis_consolidated102 {ι : Type u} {x : ι → L}
    (hx : IsTranscendenceBasis k x) : Algebra.FormallySmooth k L := by
  have hai : AlgebraicIndependent k x := hx.1
  have _fsA : Algebra.FormallySmooth k ↥(Algebra.adjoin k (Set.range x)) :=
    Algebra.FormallySmooth.of_equiv hai.aevalEquiv
  have _halg : Algebra.IsAlgebraic ↥(Algebra.adjoin k (Set.range x)) L := hx.isAlgebraic
  have _hdom : IsDomain ↥(Algebra.adjoin k (Set.range x)) := inferInstance
  exact formallySmooth_of_isAlgebraic_consolidated102 k L ↥(Algebra.adjoin k (Set.range x))
    (fun a b h => Subtype.ext h)

private theorem formallySmooth_of_charZero_consolidated102 : Algebra.FormallySmooth k L := by
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis k L
  exact formallySmooth_of_isTranscendenceBasis_consolidated102 k L hB


end

section
variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]

theorem formallySmooth_residueField (x : X)
    [Algebra k (IsLocalRing.ResidueField (X.presheaf.stalk x))]
    (_h : algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x)) =
      (IsLocalRing.residue (X.presheaf.stalk x)).comp (stalkAlgebraMap k p x)) :
    Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
  formallySmooth_of_charZero_consolidated102 k (IsLocalRing.ResidueField (X.presheaf.stalk x))

theorem orderAt_derivIdealSheafIterate_eq_sub (I : X.IdealSheafData)
    (x : X) {r : ℕ} (hr : orderAt I x = (r : ℕ∞)) {j : ℕ} (hj : j ≤ r) :
    orderAt (derivIdealSheafIterate k p j I) x = ((r - j : ℕ) : ℕ∞) := by
  let algst : Algebra k (X.presheaf.stalk x) := stalkAlgebra k p x
  have _hN : IsNoetherianRing (X.presheaf.stalk x) := isNoetherianRing_stalk k p x
  have _hFS : Algebra.FormallySmooth k (X.presheaf.stalk x) := formallySmooth_stalk k p x
  have _hFin : Module.Finite (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) :=
    finite_kaehlerDifferential_stalk k p x
  have _hFree : Module.Free (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) :=
    free_kaehlerDifferential_stalk k p x
  let algres : Algebra k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    ((IsLocalRing.residue (X.presheaf.stalk x)).comp (stalkAlgebraMap k p x)).toAlgebra
  have _tower : IsScalarTower k (X.presheaf.stalk x)
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have _hFSres : Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    formallySmooth_residueField k p x rfl
  obtain ⟨h, y, δ, hspan, hδ⟩ := exists_local_parameters_and_dual_derivations k (X.presheaf.stalk x)
  have hI' : idealOrder (stalkIdeal I x) = (r : ℕ∞) := by
    rw [← orderAt_eq_idealOrder]; exact hr
  rw [orderAt_eq_idealOrder, stalkIdeal_derivIdealSheafIterate k p j I x]
  exact idealOrder_derivIdealIterate_of_isUnit_natCast k y δ hδ hspan
    (fun n hn => isUnit_natCast_stalk k p x hn) hI' hj


end

private theorem eq_top_or_exists_eq_natCast_consolidated102 (a : ℕ∞) : a = ⊤ ∨ ∃ n : ℕ, a = (n : ℕ∞) := by
  rcases eq_or_ne a ⊤ with h | h
  · exact Or.inl h
  · exact Or.inr ⟨a.toNat, (ENat.natCast_toNat h).symm⟩

section
variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (I : X.IdealSheafData)
include p

theorem orderAtLeastLocus_derivIdealSheafIterate {r m : ℕ} (h : r < m) :
    orderAtLeastLocus (derivIdealSheafIterate k p r I) (m - r) = orderAtLeastLocus I m := by
  refine Set.Subset.antisymm ?_ (orderAtLeastLocus_subset_orderAtLeastLocus_derivIdealSheafIterate k p I r m)
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx ⊢
  rcases eq_top_or_exists_eq_natCast_consolidated102 (orderAt I x) with htop | ⟨n, hn⟩
  · rw [htop]
    exact le_top
  · rcases Nat.lt_or_ge n r with hnr | hrn
    · exfalso
      have hzero : orderAt (derivIdealSheafIterate k p n I) x = ((n - n : ℕ) : ℕ∞) :=
        orderAt_derivIdealSheafIterate_eq_sub k p I x hn le_rfl
      simp only [Nat.sub_self, Nat.cast_zero] at hzero
      have hsplit : r - n + n = r := by omega
      have hadd : derivIdealSheafIterate k p (r - n + n) I =
          derivIdealSheafIterate k p (r - n) (derivIdealSheafIterate k p n I) :=
        derivIdealSheafIterate_add k p (r - n) n I
      rw [hsplit] at hadd
      have hle : derivIdealSheafIterate k p n I ≤ derivIdealSheafIterate k p r I := by
        rw [hadd]
        exact le_derivIdealSheafIterate k p (r - n) (derivIdealSheafIterate k p n I)
      have h1 : orderAt (derivIdealSheafIterate k p r I) x ≤ 0 := by
        have h2 := orderAt_le_of_le hle x
        rwa [hzero] at h2
      have h3 : ((m - r : ℕ) : ℕ∞) ≤ 0 := le_trans hx h1
      have h4 : m - r ≤ 0 := by exact_mod_cast h3
      omega
    · have key : orderAt (derivIdealSheafIterate k p r I) x = ((n - r : ℕ) : ℕ∞) :=
        orderAt_derivIdealSheafIterate_eq_sub k p I x hn hrn
      rw [key] at hx
      have hmn : m - r ≤ n - r := by exact_mod_cast hx
      have hmn' : m ≤ n := by omega
      rw [hn]
      exact_mod_cast hmn'

theorem support_derivIdealSheafIterate_eq_orderAtLeastLocus {m : ℕ} (hm : 1 ≤ m) :
    ((derivIdealSheafIterate k p (m - 1) I).support : Set X) = orderAtLeastLocus I m := by
  have h1 : m - 1 < m := by omega
  have h2 : m - (m - 1) = 1 := by omega
  have h3 := orderAtLeastLocus_derivIdealSheafIterate k p I (r := m - 1) (m := m) h1
  rw [h2] at h3
  rw [← h3]
  ext x
  exact (mem_orderAtLeastLocus_one_iff (derivIdealSheafIterate k p (m - 1) I) x).symm

theorem isClosed_orderAtLeastLocus (m : ℕ) : IsClosed (orderAtLeastLocus I m) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [orderAtLeastLocus_zero]
    exact isClosed_univ
  · have hm1 : 1 ≤ m := by omega
    rw [← support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm1]
    exact (derivIdealSheafIterate k p (m - 1) I).support.2


end

private theorem ideal_eq_top_of_support_eq_empty_consolidated102 {X : Scheme.{u}} (J : X.IdealSheafData)
    (hJ : (J.support : Set X) = (∅ : Set X)) (U : X.affineOpens) :
    J.ideal U = ⊤ := by
  have hcover : (⨆ f : (J.ideal U : Set Γ(X, U.1)), X.basicOpen (f : Γ(X, U.1))) = U.1 := by
    refine le_antisymm (iSup_le fun f => X.basicOpen_le (f : Γ(X, U.1))) ?_
    rw [SetLike.le_def]
    intro x hxU
    have hxs : x ∉ J.support := by
      intro hc
      have hmem : x ∈ (J.support : Set X) := hc
      rw [hJ] at hmem
      simp at hmem
    have hnle : ¬ stalkIdeal J x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := fun hc =>
      hxs ((mem_support_iff_stalkIdeal_le_maximalIdeal J x).mpr hc)
    rw [stalkIdeal_eq_map_germ J x U hxU, Ideal.map_le_iff_le_comap,
      SetLike.not_le_iff_exists] at hnle
    obtain ⟨a, ha, ha2⟩ := hnle
    have hbo : x ∈ X.basicOpen a := by
      refine (X.mem_basicOpen a x hxU).mpr ?_
      by_contra hc
      exact ha2 (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr
        (mem_nonunits_iff.mpr hc)))
    exact Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hbo⟩
  have hspan := (IsAffineOpen.iSup_basicOpen_eq_self_iff U.2).mp hcover
  rwa [Ideal.span_eq] at hspan

theorem derivIdealSheafIterate_eq_top_of_orderAtLeastLocus_eq_empty (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (I : X.IdealSheafData)
    (m : ℕ) (h : orderAtLeastLocus I (m + 1) = (∅ : Set X)) :
    derivIdealSheafIterate k p m I = ⊤ := by
  have hsupp : ((derivIdealSheafIterate k p m I).support : Set X) = (∅ : Set X) := by
    have h2 := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I (m := m + 1) (Nat.le_add_left 1 m)
    simp only [Nat.add_sub_cancel] at h2
    exact h2.trans h
  refine le_antisymm le_top ?_
  intro U
  rw [ideal_eq_top_of_support_eq_empty_consolidated102 (derivIdealSheafIterate k p m I) hsupp U]
  exact le_top

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealSheaf
section

open AlgebraicGeometry CategoryTheory TopologicalSpace


private theorem map_logDerivIdeal_basicOpen_consolidated103 (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P I : X.IdealSheafData) :
    ∀ (U : X.affineOpens) (f : Γ(X, U.1)),
      Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
          (@logDerivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U)) =
        @logDerivIdeal k _ _ _ (sectionsAlgebra k p (X.affineBasicOpen f).1)
          (P.ideal (X.affineBasicOpen f)) (I.ideal (X.affineBasicOpen f)) := by
  intro U f
  have hUaff : IsAffineOpen U.1 := U.2
  let algU : Algebra k Γ(X, U.1) := sectionsAlgebra k p U.1
  let algV : Algebra k Γ(X, X.basicOpen f) := sectionsAlgebra k p (X.basicOpen f)
  let algUV : Algebra Γ(X, U.1) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  have tower : IsScalarTower k Γ(X, U.1) Γ(X, X.basicOpen f) :=
    isScalarTower_sections k p U.1 f rfl rfl rfl
  have loc : IsLocalization.Away f Γ(X, X.basicOpen f) := hUaff.isLocalization_basicOpen f
  have fp : Module.FinitePresentation Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) :=
    finitePresentation_kaehlerDifferential_sections k p U rfl
  have noeth : IsNoetherianRing Γ(X, U.1) := isNoetherianRing_sections k p U rfl
  have hP : (P.ideal U).FG := IsNoetherian.noetherian _
  have key := logDerivIdeal_map_away (S' := Γ(X, X.basicOpen f)) k f hP (I.ideal U)
  rw [← P.map_ideal_basicOpen U f, ← I.map_ideal_basicOpen U f]
  exact key

noncomputable def logDerivIdealSheaf (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P I : X.IdealSheafData) : X.IdealSheafData where
  ideal U := @logDerivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U)
  map_ideal_basicOpen := map_logDerivIdeal_basicOpen_consolidated103 k p P I

section
variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]

@[simp] theorem logDerivIdealSheaf_ideal (P I : X.IdealSheafData) (U : X.affineOpens) :
    (logDerivIdealSheaf k p P I).ideal U =
      @logDerivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U) :=
  rfl

theorem logDerivIdealSheaf_mono (P : X.IdealSheafData) :
    Monotone (logDerivIdealSheaf k p P) := by
  intro I J h U
  exact @logDerivIdeal_le_logDerivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U)
    (I.ideal U) (J.ideal U) (h U)

theorem logDerivIdealSheaf_le_derivIdealSheaf (P I : X.IdealSheafData) :
    logDerivIdealSheaf k p P I ≤ derivIdealSheaf k p I := by
  intro U
  exact @logDerivIdeal_le_derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U)


end

noncomputable def logDerivIdealSheafIterate (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P : X.IdealSheafData) : ℕ → X.IdealSheafData → X.IdealSheafData
  | 0, I => I
  | (r + 1), I => logDerivIdealSheaf k p P (logDerivIdealSheafIterate k p P r I)

section
variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]

@[simp] theorem logDerivIdealSheafIterate_zero (P I : X.IdealSheafData) : logDerivIdealSheafIterate k p P 0 I = I :=
  rfl

theorem logDerivIdealSheafIterate_succ (P : X.IdealSheafData) (r : ℕ) (I : X.IdealSheafData) :
    logDerivIdealSheafIterate k p P (r + 1) I =
      logDerivIdealSheaf k p P (logDerivIdealSheafIterate k p P r I) :=
  rfl

theorem logDerivIdealSheafIterate_add (P : X.IdealSheafData) (r s : ℕ) (I : X.IdealSheafData) :
    logDerivIdealSheafIterate k p P (r + s) I =
      logDerivIdealSheafIterate k p P r (logDerivIdealSheafIterate k p P s I) := by
  induction r with
  | zero =>
      rw [Nat.zero_add, logDerivIdealSheafIterate_zero]
  | succ r ih =>
      have hrs : r + 1 + s = (r + s) + 1 := by omega
      rw [hrs, logDerivIdealSheafIterate_succ, logDerivIdealSheafIterate_succ, ih]

@[simp] theorem logDerivIdealSheafIterate_ideal (P : X.IdealSheafData) (r : ℕ) (I : X.IdealSheafData) (U : X.affineOpens) :
    (logDerivIdealSheafIterate k p P r I).ideal U =
      @logDerivIdealIterate k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) r (I.ideal U) := by
  induction r with
  | zero =>
      rw [logDerivIdealSheafIterate_zero,
        @logDerivIdealIterate_zero k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U)]
  | succ r ih =>
      rw [logDerivIdealSheafIterate_succ, logDerivIdealSheaf_ideal, ih,
        @logDerivIdealIterate_succ k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) r (I.ideal U)]

theorem logDerivIdealSheafIterate_mono (P : X.IdealSheafData) (r : ℕ) :
    Monotone (logDerivIdealSheafIterate k p P r) := by
  induction r with
  | zero =>
      intro I J h
      rw [logDerivIdealSheafIterate_zero, logDerivIdealSheafIterate_zero]
      exact h
  | succ r ih =>
      intro I J h
      rw [logDerivIdealSheafIterate_succ, logDerivIdealSheafIterate_succ]
      exact logDerivIdealSheaf_mono k p P (ih h)

theorem logDerivIdealSheafIterate_le_derivIdealSheafIterate (P : X.IdealSheafData) (r : ℕ) (I : X.IdealSheafData) :
    logDerivIdealSheafIterate k p P r I ≤ derivIdealSheafIterate k p r I := by
  induction r with
  | zero =>
      exact le_of_eq
        ((logDerivIdealSheafIterate_zero k p P I).trans (derivIdealSheafIterate_zero k p I).symm)
  | succ r ih =>
      rw [logDerivIdealSheafIterate_succ, derivIdealSheafIterate_succ]
      exact le_trans
        (logDerivIdealSheaf_le_derivIdealSheaf k p P (logDerivIdealSheafIterate k p P r I))
        (derivIdealSheaf_mono k p ih)


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativesInBlowupCharts
section
namespace EtaleCoordinates

section
variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]

private theorem finset_sum_derivation_apply_consolidated101 {μ : Type*} (u : Finset μ) (D : μ → Derivation R A A) (x : A) :
    (∑ j ∈ u, D j) x = ∑ j ∈ u, (D j) x := by
  classical
  refine Finset.induction_on u ?_ ?_
  · simp
  · intro b t hb ih
    rw [Finset.sum_insert hb, Finset.sum_insert hb, ← ih]
    simp

private theorem smul_derivation_apply_consolidated101 (a : A) (D : Derivation R A A) (x : A) : (a • D) x = a * D x := by
  simp


end

variable (k : Type*) [CommRing k] (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S₁ : Type*) [CommRing S₁] [Algebra k S₁] [Algebra (MvPolynomial ι k) S₁]
  [IsScalarTower k (MvPolynomial ι k) S₁] [Algebra.FormallyEtale (MvPolynomial ι k) S₁]
  (φ : S →ₐ[k] S₁) (T : Finset ι) (s : ι)

theorem partialDeriv_mem_sup_of_span_pow_mul_eq_map
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (i : ι) (hiT : i ∈ T) (his : i ≠ s)
    (J : Ideal S) (L L' : Ideal S₁) (c : ℕ)
    (hJ : Ideal.span {coord k ι S₁ s ^ (c + 1)} * L = Ideal.map φ J)
    (hD : Ideal.map φ (derivIdeal k J) ≤ Ideal.span {coord k ι S₁ s ^ c} * L')
    (g : S₁) (hg : g ∈ L) :
    partialDeriv k ι S₁ i g ∈ L ⊔ L' := by
  have hmapspan : Ideal.span (⇑φ '' (J : Set S)) = Ideal.map φ J := by
    rw [← Ideal.map_span, Ideal.span_eq]
  have hgen : ∀ x ∈ (⇑φ '' (J : Set S)),
      partialDeriv k ι S₁ i x ∈ Ideal.span {coord k ι S₁ s ^ (c + 1)} * (L ⊔ L') := by
    rintro _ ⟨f, hf, rfl⟩
    have h1 : partialDeriv k ι S₁ i (φ f)
        = coord k ι S₁ s * φ (partialDeriv k ι S i f) :=
      partialDeriv_map_of_mem k ι S S₁ φ T s hin hs hout i hiT his f
    have h2 : φ (partialDeriv k ι S i f) ∈ Ideal.map φ (derivIdeal k J) :=
      Ideal.mem_map_of_mem φ
        (derivation_apply_mem_derivIdeal k J (partialDeriv k ι S i) (SetLike.mem_coe.mp hf))
    obtain ⟨z, hz, hzeq⟩ := Ideal.mem_span_singleton_mul.mp (hD h2)
    rw [h1, ← hzeq]
    exact Ideal.mem_span_singleton_mul.mpr ⟨z, Submodule.mem_sup_right hz, by ring⟩
  have hGT : Ideal.span (⇑φ '' (J : Set S))
      ≤ Ideal.span {coord k ι S₁ s ^ (c + 1)} * (L ⊔ L') := by
    rw [hmapspan, ← hJ]
    exact Ideal.mul_mono_right le_sup_left
  have hmem : coord k ι S₁ s ^ (c + 1) * g ∈ Ideal.span (⇑φ '' (J : Set S)) := by
    rw [hmapspan, ← hJ]
    exact Ideal.mem_span_singleton_mul.mpr ⟨g, hg, rfl⟩
  have key := derivation_apply_mem_of_mem_span (partialDeriv k ι S₁ i) hGT hgen hmem
  have hDy : partialDeriv k ι S₁ i (coord k ι S₁ s) = 0 :=
    partialDeriv_coord_of_ne k ι S₁ i s his
  have hDypow : partialDeriv k ι S₁ i (coord k ι S₁ s ^ (c + 1)) = 0 := by
    rw [Derivation.leibniz_pow, hDy, smul_zero, smul_zero]
  have hexp : partialDeriv k ι S₁ i (coord k ι S₁ s ^ (c + 1) * g)
      = coord k ι S₁ s ^ (c + 1) * partialDeriv k ι S₁ i g := by
    rw [Derivation.leibniz, hDypow, smul_zero, add_zero, smul_eq_mul]
  rw [hexp] at key
  obtain ⟨w, hw, hweq⟩ := Ideal.mem_span_singleton_mul.mp key
  have hnz : coord k ι S₁ s ^ (c + 1) ∈ nonZeroDivisors S₁ := pow_mem hnzd (c + 1)
  have h0 : (partialDeriv k ι S₁ i g - w) * coord k ι S₁ s ^ (c + 1) = 0 := by
    linear_combination -hweq
  have h1 : partialDeriv k ι S₁ i g - w = 0 :=
    (mem_nonZeroDivisors_iff.mp hnz).2 _ h0
  have h2 : partialDeriv k ι S₁ i g = w := sub_eq_zero.mp h1
  rw [h2]
  exact hw

section
variable [Fintype ι] (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s) (hs : φ (coord k ι S s) = coord k ι S₁ s) (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i) (hsT : s ∈ T) (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁) (i : ι) (hiT : i ∈ T) (his : i ≠ s) (J : Ideal S) (J₁ : Ideal S₁) (m : ℕ)
include hin hs hout hsT hnzd hiT his

theorem map_logDerivIdeal_le_span_pow_mul (hm : 1 ≤ m)
    (hJ : Ideal.map φ J ≤ Ideal.span {coord k ι S₁ s ^ m} * J₁) :
    Ideal.map φ (logDerivIdeal k (Ideal.span {coord k ι S i}) J)
      ≤ Ideal.span {coord k ι S₁ s ^ (m - 1)}
          * logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
  obtain ⟨e, rfl⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hJmem : ∀ f ∈ J, ∃ f₁ ∈ J₁, φ f = coord k ι S₁ s ^ (e + 1) * f₁ := by
    intro f hf
    obtain ⟨f₁, hf₁, hfe⟩ := Ideal.mem_span_singleton_mul.mp (hJ (Ideal.mem_map_of_mem φ hf))
    exact ⟨f₁, hf₁, hfe.symm⟩
  have htan : ∀ j : ι, j ≠ i →
      partialDeriv k ι S₁ j ∈ tangentDerivations k (Ideal.span {coord k ι S₁ i}) := by
    intro j hj
    rw [mem_tangentDerivations_span_singleton]
    rw [partialDeriv_coord_of_ne k ι S₁ j i hj]
    exact Submodule.zero_mem _
  have htanmul : (coord k ι S₁ i) • partialDeriv k ι S₁ i
      ∈ tangentDerivations k (Ideal.span {coord k ι S₁ i}) :=
    smul_mem_tangentDerivations k (Ideal.span {coord k ι S₁ i})
      (Ideal.subset_span (Set.mem_singleton _)) (partialDeriv k ι S₁ i)
  rw [Ideal.map_le_iff_le_comap, logDerivIdeal_le_iff]
  refine ⟨?_, ?_⟩
  · intro f hf
    rw [Ideal.mem_comap]
    obtain ⟨f₁, hf₁, hfe⟩ := hJmem f hf
    refine Ideal.mem_span_singleton_mul.mpr ⟨coord k ι S₁ s * f₁, ?_, ?_⟩
    · exact le_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ (J₁.mul_mem_left _ hf₁)
    · rw [hfe]; ring
  · intro D hD f hf
    rw [Ideal.mem_comap]
    obtain ⟨f₁, hf₁, hfe⟩ := hJmem f hf
    have hpd : ∀ j : ι, j ≠ i →
        partialDeriv k ι S₁ j f₁ ∈ logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
      intro j hj
      exact derivation_apply_mem_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁
        (partialDeriv k ι S₁ j) (htan j hj) hf₁
    have hpdi : coord k ι S₁ i * partialDeriv k ι S₁ i f₁
        ∈ logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
      have h := derivation_apply_mem_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁
        ((coord k ι S₁ i) • partialDeriv k ι S₁ i) htanmul hf₁
      rwa [smul_derivation_apply_consolidated101] at h
    have hDi : D (coord k ι S i) ∈ Ideal.span {coord k ι S i} :=
      (mem_tangentDerivations_span_singleton k (coord k ι S i) D).mp hD
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hDi
    have hDf : φ (D f) = ∑ j : ι, φ (D (coord k ι S j)) * φ (partialDeriv k ι S j f) := by
      have h0 : D f = ∑ j : ι, D (coord k ι S j) * partialDeriv k ι S j f := by
        conv_lhs => rw [eq_sum_smul_partialDeriv k ι S D]
        rw [finset_sum_derivation_apply_consolidated101]
        exact Finset.sum_congr rfl (fun j _ => smul_derivation_apply_consolidated101 _ _ _)
      rw [h0, map_sum]
      exact Finset.sum_congr rfl (fun j _ => map_mul φ _ _)
    rw [hDf]
    refine Ideal.sum_mem _ ?_
    intro j _
    by_cases hji : j = i
    · rw [hji]
      have h1 : φ (partialDeriv k ι S i f)
          = coord k ι S₁ s ^ e * partialDeriv k ι S₁ i f₁ :=
        map_partialDeriv_eq_pow_mul_of_mem k ι S S₁ φ T s hin hs hout hnzd i hiT his f f₁ e hfe
      have h2 : φ (D (coord k ι S i)) = φ a * (coord k ι S₁ i * coord k ι S₁ s) := by
        rw [← ha, map_mul, hin i hiT his]
      rw [h1, h2]
      exact Ideal.mem_span_singleton_mul.mpr
        ⟨φ a * coord k ι S₁ s * (coord k ι S₁ i * partialDeriv k ι S₁ i f₁),
          Ideal.mul_mem_left _ _ hpdi, by ring⟩
    · have hkey : φ (partialDeriv k ι S j f)
          ∈ Ideal.span {coord k ι S₁ s ^ e}
              * logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
        by_cases hjT : j ∈ T
        · by_cases hjs : j = s
          · rw [hjs]
            have h1 := map_partialDeriv_self_eq_pow_mul k ι S S₁ φ T s hin hs hout hsT hnzd f f₁ e hfe
            have hbr : coord k ι S₁ s * partialDeriv k ι S₁ s f₁ + ((e + 1 : ℕ) : S₁) * f₁
                - ∑ l ∈ T.erase s, coord k ι S₁ l * partialDeriv k ι S₁ l f₁
                ∈ logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
              refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
              · exact Ideal.mul_mem_left _ _ (hpd s his.symm)
              · exact Ideal.mul_mem_left _ _
                  (le_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ hf₁)
              · refine Ideal.sum_mem _ ?_
                intro l _
                by_cases hli : l = i
                · rw [hli]; exact hpdi
                · exact Ideal.mul_mem_left _ _ (hpd l hli)
            rw [h1]
            exact Ideal.mem_span_singleton_mul.mpr ⟨_, hbr, rfl⟩
          · have h1 :=
              map_partialDeriv_eq_pow_mul_of_mem k ι S S₁ φ T s hin hs hout hnzd j hjT hjs f f₁ e hfe
            rw [h1]
            exact Ideal.mem_span_singleton_mul.mpr ⟨_, hpd j hji, rfl⟩
        · have h1 :=
            map_partialDeriv_eq_pow_mul_of_notMem k ι S S₁ φ T s hin hs hout hsT j hjT f f₁ e hfe
          rw [h1]
          exact Ideal.mem_span_singleton_mul.mpr
            ⟨coord k ι S₁ s * partialDeriv k ι S₁ j f₁,
              Ideal.mul_mem_left _ _ (hpd j hji), by ring⟩
      exact Ideal.mul_mem_left _ _ hkey

theorem map_logDerivIdealIterate_le_span_pow_mul (hJ : Ideal.map φ J ≤ Ideal.span {coord k ι S₁ s ^ m} * J₁)
    (j : ℕ) (hj : j ≤ m) :
    Ideal.map φ (logDerivIdealIterate k (Ideal.span {coord k ι S i}) j J)
      ≤ Ideal.span {coord k ι S₁ s ^ (m - j)}
          * logDerivIdealIterate k (Ideal.span {coord k ι S₁ i}) j J₁ := by
  revert hj
  induction j with
  | zero =>
      intro _
      rw [logDerivIdealIterate_zero, logDerivIdealIterate_zero, Nat.sub_zero]
      exact hJ
  | succ j ih =>
      intro hj
      have h1 := ih (Nat.le_of_succ_le hj)
      have h2 := map_logDerivIdeal_le_span_pow_mul k ι S S₁ φ T s hin hs hout hsT hnzd i hiT his
        (logDerivIdealIterate k (Ideal.span {coord k ι S i}) j J)
        (logDerivIdealIterate k (Ideal.span {coord k ι S₁ i}) j J₁) (m - j) (by omega) h1
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ]
      have hsub : m - j - 1 = m - (j + 1) := by omega
      rwa [hsub] at h2


end

end EtaleCoordinates
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
section

open CategoryTheory AlgebraicGeometry TopologicalSpace


section
variable (k : Type u) [CommRing k] {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) (h : Y ⟶ X) (W : X.Opens) (V : Y.Opens) (e : V ≤ h ⁻¹ᵁ W)

theorem sectionsAlgebraMap_comp_appLE :
    (h.appLE W V e).hom.comp (sectionsAlgebraMap k p W) = sectionsAlgebraMap k (h ≫ p) V := by
  rw [sectionsAlgebraMap_eq, sectionsAlgebraMap_eq, ← CommRingCat.hom_comp, Category.assoc,
    Scheme.Hom.appLE_comp_appLE]

theorem sectionsAlgebraMap_appLE_apply (a : k) :
    (h.appLE W V e).hom (sectionsAlgebraMap k p W a) = sectionsAlgebraMap k (h ≫ p) V a :=
  DFunLike.congr_fun (sectionsAlgebraMap_comp_appLE k p h W V e) a


end

private theorem exists_pow_mul_mem_of_mem_map_consolidated138 {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (f : R) [IsLocalization.Away f S] (N : Ideal R) (x : R)
    (hx : algebraMap R S x ∈ N.map (algebraMap R S)) : ∃ n : ℕ, f ^ n * x ∈ N := by
  obtain ⟨⟨a, t⟩, hmul⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (M := Submonoid.powers f) (S := S)).mp hx
  have hmul' : algebraMap R S (x * (t : R)) = algebraMap R S (a : R) := by
    rw [map_mul]
    exact hmul
  obtain ⟨c, hceq⟩ :=
    (IsLocalization.eq_iff_exists (M := Submonoid.powers f) (S := S)).mp hmul'
  obtain ⟨i, hi⟩ := t.2
  obtain ⟨j, hj⟩ := c.2
  have hi' : f ^ i = (t : R) := hi
  have hj' : f ^ j = (c : R) := hj
  refine ⟨i + j, ?_⟩
  have key : f ^ (i + j) * x = f ^ j * (x * f ^ i) := by ring
  rw [key, hi', hj', hceq]
  exact N.mul_mem_left _ a.2

section
variable {Y : Scheme.{u}} (J₁ J₂ : Y.IdealSheafData)

private theorem idealSheafData_ideal_le_congr_consolidated138 {A B : Y.affineOpens} (hAB : A = B) (h : J₁.ideal B ≤ J₂.ideal B) :
    J₁.ideal A ≤ J₂.ideal A := by
  subst hAB
  exact h

private theorem idealSheafData_ideal_le_of_locally_le_consolidated138 (H : ∀ y : Y, ∃ (V : Y.Opens) (hV : IsAffineOpen V), y ∈ V ∧
      J₁.ideal ⟨V, hV⟩ ≤ J₂.ideal ⟨V, hV⟩) (U : Y.affineOpens) :
    J₁.ideal U ≤ J₂.ideal U := by
  intro x hx
  set s : Set Γ(Y, U.1) := {f : Γ(Y, U.1) | ∃ n : ℕ, f ^ n * x ∈ J₂.ideal U} with hs
  have hcover : U.1 ≤ ⨆ f : s, Y.basicOpen (f : Γ(Y, U.1)) := by
    intro z hz
    obtain ⟨V, hV, hzV, hle⟩ := H z
    obtain ⟨f, g, hfg, hzf⟩ := exists_basicOpen_le_affine_inter U.2 hV z ⟨hz, hzV⟩
    have hres : Ideal.map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom (J₁.ideal U)
        ≤ Ideal.map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom (J₂.ideal U) := by
      rw [J₁.map_ideal_basicOpen U f, J₂.map_ideal_basicOpen U f]
      have hABO : Y.affineBasicOpen f = Y.affineBasicOpen (U := ⟨V, hV⟩) g := Subtype.ext hfg
      refine idealSheafData_ideal_le_congr_consolidated138 J₁ J₂ hABO ?_
      rw [← J₁.map_ideal_basicOpen ⟨V, hV⟩ g, ← J₂.map_ideal_basicOpen ⟨V, hV⟩ g]
      exact Ideal.map_mono hle
    have hfs : f ∈ s := by
      have := U.2.isLocalization_basicOpen f
      rw [hs]
      refine exists_pow_mul_mem_of_mem_map_consolidated138 (S := Γ(Y, Y.basicOpen f)) f (J₂.ideal U) x ?_
      have halg : (algebraMap Γ(Y, U.1) Γ(Y, Y.basicOpen f))
          = (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom := rfl
      rw [halg]
      exact hres (Ideal.mem_map_of_mem _ hx)
    exact Opens.mem_iSup.mpr ⟨⟨f, hfs⟩, hzf⟩
  have hspan : Ideal.span s = ⊤ := (U.2.self_le_iSup_basicOpen_iff).mp hcover
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (J₂.ideal U) s hspan x ?_
  rintro ⟨f, hf⟩
  rw [hs] at hf
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, by rw [smul_eq_mul]; exact hn⟩

private theorem idealSheafData_eq_of_locally_eq_consolidated138 (H : ∀ y : Y, ∃ (V : Y.Opens) (hV : IsAffineOpen V), y ∈ V ∧
      J₁.ideal ⟨V, hV⟩ = J₂.ideal ⟨V, hV⟩) : J₁ = J₂ := by
  have key : ∀ U : Y.affineOpens, J₁.ideal U = J₂.ideal U := by
    intro U
    refine le_antisymm (idealSheafData_ideal_le_of_locally_le_consolidated138 J₁ J₂ ?_ U)
      (idealSheafData_ideal_le_of_locally_le_consolidated138 J₂ J₁ ?_ U)
    · intro y
      obtain ⟨V, hV, h1, h2⟩ := H y
      exact ⟨V, hV, h1, h2.le⟩
    · intro y
      obtain ⟨V, hV, h1, h2⟩ := H y
      exact ⟨V, hV, h1, h2.ge⟩
  exact Scheme.IdealSheafData.ext (funext key)


end

attribute [local instance] EtaleCoordinates.sumEvalAlgebra in
private theorem exists_affineOpen_derivIdealSheaf_comap_ideal_eq_consolidated138 (k : Type u) [Field k] [IsNoetherianRing k]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (h : Y ⟶ X) [Smooth h] [LocallyOfFiniteType (h ≫ p)] (I : X.IdealSheafData) (y : Y) :
    ∃ (V : Y.Opens) (hV : IsAffineOpen V), y ∈ V ∧
      (derivIdealSheaf k (h ≫ p) (I.comap h)).ideal ⟨V, hV⟩
        = ((derivIdealSheaf k p I).comap h).ideal ⟨V, hV⟩ := by
  classical
  obtain ⟨W₀, m, hxW₀, -, ⟨c₀⟩⟩ := exists_etaleChart p (h.base y)
  obtain ⟨W, V, d, e, hW, hV, hyV, hWW₀, -, g, hgE, hg⟩ :=
    SmoothEtaleChart.exists_isAffineOpen_etale_resLE_le h y W₀ hxW₀ ⊤ (by trivial)
  refine ⟨V, hV, hyV, ?_⟩
  have : Etale g := hgE
  let c : EtaleChart p W m := c₀.restrict hWW₀
  let instkS : Algebra k Γ(X, W) := sectionsAlgebra k p W
  let instkT : Algebra k Γ(Y, V) := sectionsAlgebra k (h ≫ p) V
  let instPS : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W) := c.algebra
  let instTow1 : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W) := c.isScalarTower
  have instFE1 : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W) :=
    c.algebra_formallyEtale hW
  let instChartAlgebra : Algebra (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
  have instFE2 : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) :=
    chartAlgebra_formallyEtale hW hV g
  let instST : Algebra Γ(X, W) Γ(Y, V) := (h.appLE W V e).hom.toAlgebra
  let instTowkST : IsScalarTower k Γ(X, W) Γ(Y, V) :=
    IsScalarTower.of_algebraMap_eq fun a => (sectionsAlgebraMap_appLE_apply k p h W V e a).symm
  let instScalarTowerChart : IsScalarTower Γ(X, W) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) :=
    chartAlgebra_isScalarTower hW h e g hg
  let instSumT : Algebra (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V) :=
    ((algebraMap (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V)).comp
      (algebraMap (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)))).toAlgebra
  let instScalarTowerSum : IsScalarTower (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
      (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have instTowkSum : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
      Γ(Y, V) := by
    have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) :=
      EtaleCoordinates.sumEvalAlgebra_isScalarTower k (ULift.{u} (Fin m)) (ULift.{u} (Fin d))
        Γ(X, W)
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V)
        (algebraMap k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) a),
      ← IsScalarTower.algebraMap_apply k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) a,
      IsScalarTower.algebraMap_apply k Γ(X, W) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) a,
      ← IsScalarTower.algebraMap_apply Γ(X, W) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V),
      ← IsScalarTower.algebraMap_apply k Γ(X, W) Γ(Y, V)]
  have instFE3 : Algebra.FormallyEtale
      (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V) :=
    EtaleCoordinates.formallyEtale_trans k (ULift.{u} (Fin m)) (ULift.{u} (Fin d))
      Γ(X, W) Γ(Y, V)
  have hcoord : ∀ i : ULift.{u} (Fin m),
      algebraMap Γ(X, W) Γ(Y, V) (EtaleCoordinates.coord k (ULift.{u} (Fin m)) Γ(X, W) i)
        = EtaleCoordinates.coord k (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) Γ(Y, V)
            (Sum.inl i) := by
    intro i
    rw [EtaleCoordinates.coord_def k (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) Γ(Y, V) (Sum.inl i),
      IsScalarTower.algebraMap_apply (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V),
      EtaleCoordinates.algebraMap_X_inl k (ULift.{u} (Fin m)) (ULift.{u} (Fin d)) Γ(X, W),
      ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply Γ(X, W) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V)]
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (derivIdealSheaf k p I) h ⟨W, hW⟩ ⟨V, hV⟩ e]
  simp only [derivIdealSheaf_ideal]
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I h ⟨W, hW⟩ ⟨V, hV⟩ e]
  exact (EtaleCoordinates.map_derivIdeal_sum k (ULift.{u} (Fin m)) (ULift.{u} (Fin d))
    Γ(X, W) Γ(Y, V) hcoord (I.ideal ⟨W, hW⟩)).symm

section
variable (k : Type u) [Field k] [IsNoetherianRing k] {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p] (h : Y ⟶ X) [Smooth h] [LocallyOfFiniteType (h ≫ p)]

theorem derivIdealSheaf_comap (I : X.IdealSheafData) :
    derivIdealSheaf k (h ≫ p) (I.comap h) = (derivIdealSheaf k p I).comap h :=
  idealSheafData_eq_of_locally_eq_consolidated138 _ _ fun y => exists_affineOpen_derivIdealSheaf_comap_ideal_eq_consolidated138 k p h I y

theorem derivIdealSheafIterate_comap (r : ℕ) (I : X.IdealSheafData) :
    derivIdealSheafIterate k (h ≫ p) r (I.comap h) = (derivIdealSheafIterate k p r I).comap h := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [derivIdealSheafIterate_succ, derivIdealSheafIterate_succ, ih,
      derivIdealSheaf_comap k p h (derivIdealSheafIterate k p r I)]


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealSheafClosedSubscheme
section

open AlgebraicGeometry CategoryTheory TopologicalSpace


private theorem comp_app_apply_consolidated137 {X Y Z : Scheme.{u}} (u : X ⟶ Y) (q : Y ⟶ Z) (U : Z.Opens)
    (a : Γ(Z, U)) : ((u ≫ q).app U).hom a = (u.app (q ⁻¹ᵁ U)).hom ((q.app U).hom a) := by
  have h : (u ≫ q).app U = q.app U ≫ u.app (q ⁻¹ᵁ U) := Scheme.Hom.comp_app u q U
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) a

private theorem comap_le_of_map_ideal_le_consolidated137 {S X : Scheme.{u}} (ι : S ⟶ X) [IsAffineHom ι]
    (L : X.IdealSheafData) (D : S.IdealSheafData)
    (h : ∀ U : X.affineOpens, Ideal.map (ι.app (U : X.Opens)).hom (L.ideal U)
        ≤ D.ideal ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩) :
    L.comap ι ≤ D := by
  have key : ∀ (U : X.affineOpens), L.ideal U
      ≤ RingHom.ker ((D.subschemeι ≫ ι).app (U : X.Opens)).hom := by
    intro U a ha
    have h1 := h U (Ideal.mem_map_of_mem _ ha)
    have h2 : (Scheme.Hom.ker D.subschemeι).ideal ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩
        = RingHom.ker (D.subschemeι.app (ι ⁻¹ᵁ (U : X.Opens))).hom := by
      rw [Scheme.Hom.ker_apply]
    rw [Scheme.IdealSheafData.ker_subschemeι] at h2
    rw [h2] at h1
    refine RingHom.mem_ker.mpr ?_
    rw [comp_app_apply_consolidated137]
    exact RingHom.mem_ker.mp h1
  have hle : L ≤ Scheme.Hom.ker (D.subschemeι ≫ ι) := by
    unfold Scheme.Hom.ker
    exact Scheme.IdealSheafData.le_ofIdeals_iff.mpr key
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
  exact hle

private theorem derivIdealIterate_mono_of_le_consolidated137 (k : Type u) [CommRing k] {T : Type u} [CommRing T]
    [Algebra k T] (r : ℕ) {I J : Ideal T} (h : I ≤ J) :
    derivIdealIterate k r I ≤ derivIdealIterate k r J := by
  induction r with
  | zero => exact h
  | succ r ih =>
      rw [derivIdealIterate_succ, derivIdealIterate_succ]
      exact derivIdeal_mono k ih

section
variable (k : Type u) [CommRing k] {X S : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) (ι : S ⟶ X) (U : X.Opens)

private theorem app_comp_sectionsAlgebraMap_consolidated137 :
    (ι.app U).hom.comp (sectionsAlgebraMap k p U) = sectionsAlgebraMap k (ι ≫ p) (ι ⁻¹ᵁ U) := by
  have happ : ι.appLE U (ι ⁻¹ᵁ U) le_rfl = ι.app U := Scheme.Hom.appLE_eq_app ι
  have hc : p.appLE ⊤ U (le_preimage_top k p U) ≫ ι.appLE U (ι ⁻¹ᵁ U) le_rfl
      = (ι ≫ p).appLE ⊤ (ι ⁻¹ᵁ U) (le_preimage_top k (ι ≫ p) (ι ⁻¹ᵁ U)) :=
    Scheme.Hom.appLE_comp_appLE ι p ⊤ U (ι ⁻¹ᵁ U) (le_preimage_top k p U) le_rfl
  have hmor : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U))
        ≫ ι.app U
      = (Scheme.ΓSpecIso (CommRingCat.of k)).inv
        ≫ (ι ≫ p).appLE ⊤ (ι ⁻¹ᵁ U) (le_preimage_top k (ι ≫ p) (ι ⁻¹ᵁ U)) := by
    rw [Category.assoc, ← happ, hc]
  rw [sectionsAlgebraMap_eq k p U, sectionsAlgebraMap_eq k (ι ≫ p) (ι ⁻¹ᵁ U)]
  exact congrArg CommRingCat.Hom.hom hmor

private theorem app_sectionsAlgebraMap_consolidated137 (a : k) :
    (ι.app U).hom (sectionsAlgebraMap k p U a) = sectionsAlgebraMap k (ι ≫ p) (ι ⁻¹ᵁ U) a :=
  DFunLike.congr_fun (app_comp_sectionsAlgebraMap_consolidated137 k p ι U) a


end

section
variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X S : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (ι : S ⟶ X) [IsClosedImmersion ι] [LocallyOfFiniteType (ι ≫ p)] (A : X.IdealSheafData) (r : ℕ)

private theorem map_logDerivIdealSheafIterate_ideal_le_consolidated137
    (U : X.affineOpens) :
    Ideal.map (ι.app (U : X.Opens)).hom ((logDerivIdealSheafIterate k p ι.ker r A).ideal U)
      ≤ (derivIdealSheafIterate k (ι ≫ p) r (A.comap ι)).ideal
          ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩ := by
  have hcomm : ∀ a : k,
      (ι.app (U : X.Opens)).hom
          (@algebraMap k _ _ _ (sectionsAlgebra k p (U : X.Opens)) a)
        = @algebraMap k _ _ _ (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) a := by
    intro a
    have e1 : @algebraMap k _ _ _ (sectionsAlgebra k p (U : X.Opens))
        = sectionsAlgebraMap k p (U : X.Opens) :=
      algebraMap_sectionsAlgebra k p (U : X.Opens)
    have e2 : @algebraMap k _ _ _ (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens)))
        = sectionsAlgebraMap k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens)) :=
      algebraMap_sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))
    rw [e1, e2]
    exact app_sectionsAlgebraMap_consolidated137 k p ι (U : X.Opens) a
  have hmapLE : ∀ (V : S.affineOpens) (e : (V : S.Opens) ≤ ι ⁻¹ᵁ (U : X.Opens)),
      Ideal.map (ι.appLE (U : X.Opens) (V : S.Opens) e).hom (A.ideal U)
        ≤ (A.comap ι).ideal V := by
    intro V e
    apply Scheme.IdealSheafData.map_appLE_le_comap_ideal
  have hmap : Ideal.map (ι.app (U : X.Opens)).hom (A.ideal U)
      ≤ (A.comap ι).ideal ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩ := by
    rw [Scheme.Hom.app_eq_appLE]
    exact hmapLE ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩ le_rfl
  have halg := @map_logDerivIdealIterate_le_derivIdealIterate_map_of_eq_ker k _ _ _ _ _
      (sectionsAlgebra k p (U : X.Opens))
      (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens)))
      (@AlgHom.mk k _ _ _ _ _ (sectionsAlgebra k p (U : X.Opens))
        (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) (ι.app (U : X.Opens)).hom hcomm)
      (Scheme.Hom.app_surjective ι (U : X.Opens) U.2) _ rfl r (A.ideal U)
  rw [logDerivIdealSheafIterate_ideal, Scheme.Hom.ker_apply, derivIdealSheafIterate_ideal]
  refine le_trans halg ?_
  exact @derivIdealIterate_mono_of_le_consolidated137 k _ _ _ (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) r _ _
    hmap

private theorem logDerivIdealSheafIterate_comap_le_derivIdealSheafIterate_consolidated137
    :
    (logDerivIdealSheafIterate k p ι.ker r A).comap ι
      ≤ derivIdealSheafIterate k (ι ≫ p) r (A.comap ι) :=
  comap_le_of_map_ideal_le_consolidated137 ι (logDerivIdealSheafIterate k p ι.ker r A)
    (derivIdealSheafIterate k (ι ≫ p) r (A.comap ι))
    (map_logDerivIdealSheafIterate_ideal_le_consolidated137 k p ι A r)

theorem comap_logDerivIdealSheafIterate_ker_le_derivIdealSheafIterate
    :
    (logDerivIdealSheafIterate k p ι.ker r A).comap ι
      ≤ derivIdealSheafIterate k (ι ≫ p) r (A.comap ι) :=
  logDerivIdealSheafIterate_comap_le_derivIdealSheafIterate_consolidated137 k p ι A r


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealSheafOpenImmersion
section

open AlgebraicGeometry CategoryTheory TopologicalSpace


private theorem bijective_hom_of_iso_consolidated136 {A B : CommRingCat.{u}} (i : A ≅ B) :
    Function.Bijective i.hom.hom :=
  ConcreteCategory.bijective_of_isIso i.hom

private theorem map_eq_comap_of_inverse_consolidated136 {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (ψ : B →+* A) (h1 : ∀ a, ψ (φ a) = a) (h2 : ∀ b, φ (ψ b) = b) (J : Ideal A) :
    Ideal.map φ J = Ideal.comap ψ J := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, h1]
    exact ha
  · intro x hx
    rw [Ideal.mem_comap] at hx
    have hmem := Ideal.mem_map_of_mem φ hx
    rwa [h2 x] at hmem

private theorem ideal_comap_eq_map_appLE_consolidated136 {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (V : X.affineOpens) (hU : IsAffineOpen (f ''ᵁ (V : X.Opens)))
    (e : (V : X.Opens) ≤ f ⁻¹ᵁ (f ''ᵁ (V : X.Opens))) :
    (I.comap f).ideal V =
      (I.ideal ⟨f ''ᵁ (V : X.Opens), hU⟩).map
        (f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e).hom := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I f V]
  have happ : f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e = (f.appIso (V : X.Opens)).hom :=
    (Scheme.Hom.appIso_hom' f (V : X.Opens)).symm
  rw [happ]
  have h1 : ∀ a, (f.appIso (V : X.Opens)).inv.hom ((f.appIso (V : X.Opens)).hom.hom a) = a :=
    fun a => CommRingCat.inv_hom_apply (f.appIso (V : X.Opens)) a
  have h2 : ∀ b, (f.appIso (V : X.Opens)).hom.hom ((f.appIso (V : X.Opens)).inv.hom b) = b :=
    fun b => CommRingCat.hom_inv_apply (f.appIso (V : X.Opens)) b
  exact (map_eq_comap_of_inverse_consolidated136 _ _ h1 h2 _).symm

private theorem bijective_appLE_image_of_isOpenImmersion_consolidated136 {Z W : Scheme.{u}} (f : W ⟶ Z) [IsOpenImmersion f]
    (V : W.Opens) (e : V ≤ f ⁻¹ᵁ (f ''ᵁ V)) :
    Function.Bijective (f.appLE (f ''ᵁ V) V e).hom := by
  have h : f.appLE (f ''ᵁ V) V e = (f.appIso V).hom := (Scheme.Hom.appIso_hom' f V).symm
  rw [h]
  exact bijective_hom_of_iso_consolidated136 (f.appIso V)

section
variable (K : Type u) [CommRing K]

private theorem appLE_sectionsAlgebraMap_consolidated136 {Z W : Scheme.{u}}
    (q : Z ⟶ Spec (CommRingCat.of K)) (f : W ⟶ Z) (U : Z.Opens) (V : W.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (a : K) :
    (f.appLE U V e).hom (sectionsAlgebraMap K q U a) = sectionsAlgebraMap K (f ≫ q) V a := by
  have key : (f.appLE U V e).hom.comp (sectionsAlgebraMap K q U)
      = sectionsAlgebraMap K (f ≫ q) V := by
    rw [sectionsAlgebraMap_eq, sectionsAlgebraMap_eq, ← CommRingCat.hom_comp, Category.assoc,
      Scheme.Hom.appLE_comp_appLE]
  exact DFunLike.congr_fun key a

private theorem map_logDerivIdealIterate_of_bijective_consolidated136 {S S' : Type u} [CommRing S] [CommRing S'] [Algebra K S] [Algebra K S']
    (φ : S →+* S') (hφ : Function.Bijective φ)
    (hcomp : ∀ a : K, φ (algebraMap K S a) = algebraMap K S' a)
    [Module.FinitePresentation S Ω[S⁄K]]
    {P : Ideal S} (hP : P.FG) (r : ℕ) (J : Ideal S) :
    Ideal.map φ (logDerivIdealIterate K P r J) =
      logDerivIdealIterate K (Ideal.map φ P) r (Ideal.map φ J) := by
  let _ : Algebra S S' := φ.toAlgebra
  have : IsScalarTower K S S' := IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
  have : IsLocalization.Away (1 : S) S' :=
    IsLocalization.away_of_isUnit_of_bijective (hr := isUnit_one) (H := hφ)
  exact logDerivIdealIterate_map_away K (1 : S) hP r J

private theorem map_appLE_logDerivIdealIterate_of_bijective_consolidated136 [IsNoetherianRing K]
    {Z W : Scheme.{u}} (q : Z ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType q]
    (f : W ⟶ Z) [LocallyOfFiniteType (f ≫ q)]
    (U : Z.affineOpens) (V : W.affineOpens) (e : (V : W.Opens) ≤ f ⁻¹ᵁ (U : Z.Opens))
    (hbij : Function.Bijective (f.appLE (U : Z.Opens) (V : W.Opens) e).hom)
    (P A : Ideal Γ(Z, (U : Z.Opens))) (r : ℕ) :
    Ideal.map (f.appLE (U : Z.Opens) (V : W.Opens) e).hom
        (@logDerivIdealIterate K _ _ _ (sectionsAlgebra K q (U : Z.Opens)) P r A) =
      @logDerivIdealIterate K _ _ _ (sectionsAlgebra K (f ≫ q) (V : W.Opens))
        (Ideal.map (f.appLE (U : Z.Opens) (V : W.Opens) e).hom P) r
        (Ideal.map (f.appLE (U : Z.Opens) (V : W.Opens) e).hom A) := by
  have hfp := @finitePresentation_kaehlerDifferential_sections K _ _ Z q _ U
    (sectionsAlgebra K q (U : Z.Opens)) (algebraMap_sectionsAlgebra K q (U : Z.Opens))
  have hno := @isNoetherianRing_sections K _ _ Z q _ U
    (sectionsAlgebra K q (U : Z.Opens)) (algebraMap_sectionsAlgebra K q (U : Z.Opens))
  have hP : P.FG := IsNoetherian.noetherian P
  have hcomp : ∀ a : K, (f.appLE (U : Z.Opens) (V : W.Opens) e).hom
      (@algebraMap K Γ(Z, (U : Z.Opens)) _ _ (sectionsAlgebra K q (U : Z.Opens)) a) =
      @algebraMap K Γ(W, (V : W.Opens)) _ _ (sectionsAlgebra K (f ≫ q) (V : W.Opens)) a := by
    intro a
    rw [algebraMap_sectionsAlgebra, algebraMap_sectionsAlgebra]
    exact appLE_sectionsAlgebraMap_consolidated136 K q f (U : Z.Opens) (V : W.Opens) e a
  exact @map_logDerivIdealIterate_of_bijective_consolidated136 K _ Γ(Z, (U : Z.Opens)) Γ(W, (V : W.Opens)) _ _
    (sectionsAlgebra K q (U : Z.Opens)) (sectionsAlgebra K (f ≫ q) (V : W.Opens))
    (f.appLE (U : Z.Opens) (V : W.Opens) e).hom hbij hcomp hfp P hP r A


end

variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X Y : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
  (g : Y ⟶ X) [IsOpenImmersion g] [LocallyOfFiniteType (g ≫ p)]

section
variable (P A : X.IdealSheafData) (r : ℕ)

theorem logDerivIdealSheafIterate_comap_ideal_of_isOpenImmersion
    (V : Y.affineOpens) :
    ((logDerivIdealSheafIterate k p P r A).comap g).ideal V =
      (logDerivIdealSheafIterate k (g ≫ p) (P.comap g) r (A.comap g)).ideal V := by
  have hU : IsAffineOpen (g ''ᵁ (V : Y.Opens)) := V.2.image_of_isOpenImmersion g
  have e : (V : Y.Opens) ≤ g ⁻¹ᵁ (g ''ᵁ (V : Y.Opens)) := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  have hbij : Function.Bijective
      (g.appLE (g ''ᵁ (V : Y.Opens)) (V : Y.Opens) e).hom :=
    bijective_appLE_image_of_isOpenImmersion_consolidated136 g (V : Y.Opens) e
  rw [ideal_comap_eq_map_appLE_consolidated136 _ g V hU e, logDerivIdealSheafIterate_ideal,
    logDerivIdealSheafIterate_ideal, ideal_comap_eq_map_appLE_consolidated136 P g V hU e,
    ideal_comap_eq_map_appLE_consolidated136 A g V hU e]
  exact map_appLE_logDerivIdealIterate_of_bijective_consolidated136 k p g ⟨g ''ᵁ (V : Y.Opens), hU⟩ V e hbij _ _ r

theorem logDerivIdealSheafIterate_comap_of_isOpenImmersion
    :
    (logDerivIdealSheafIterate k p P r A).comap g =
      logDerivIdealSheafIterate k (g ≫ p) (P.comap g) r (A.comap g) :=
  Scheme.IdealSheafData.ext
    (funext fun V => logDerivIdealSheafIterate_comap_ideal_of_isOpenImmersion k p g P A r V)


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
section

open AlgebraicGeometry CategoryTheory TopologicalSpace


namespace EtaleCoordinates

theorem partialDeriv_comm (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (T : Type*) [CommRing T] [Algebra k T] [Algebra (MvPolynomial ι k) T]
    [IsScalarTower k (MvPolynomial ι k) T] [Algebra.FormallyEtale (MvPolynomial ι k) T]
    (i j : ι) (a : T) :
    partialDeriv k ι T i (partialDeriv k ι T j a)
      = partialDeriv k ι T j (partialDeriv k ι T i a) := by
  have hzero : ⁅partialDeriv k ι T i, partialDeriv k ι T j⁆ = (0 : Derivation k T T) := by
    refine derivation_ext_of_coord k ι T T _ _ ?_
    intro l
    rw [Derivation.commutator_apply]
    simp only [partialDeriv_coord]
    split_ifs <;> simp
  have h2 : ⁅partialDeriv k ι T i, partialDeriv k ι T j⁆ a = 0 := by
    rw [hzero]; simp
  rw [Derivation.commutator_apply] at h2
  linear_combination h2

end EtaleCoordinates

section
variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]

private theorem exists_commuting_dual_derivations_consolidated139 (A : Type*) [CommRing A] [Algebra k A] [Algebra.FormallySmooth k A]
    (e : Module.Basis ι A (KaehlerDifferential k A)) (w : ι → A)
    (hdet : IsUnit (e.det fun i : ι => KaehlerDifferential.D k A (w i))) :
    ∃ D : ι → Derivation k A A,
      (∀ i j : ι, D i (w j) = if i = j then 1 else 0) ∧
      (∀ i j : ι, ∀ a : A, D i (D j a) = D j (D i a)) := by
  let _ : Algebra (MvPolynomial ι k) A :=
    (MvPolynomial.aeval w : MvPolynomial ι k →ₐ[k] A).toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial ι k) A :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [RingHom.algebraMap_toAlgebra]
      simp [MvPolynomial.algebraMap_eq]
  have : Algebra.FormallyEtale (MvPolynomial ι k) A :=
    EtaleCoordinates.formallyEtale_aeval_of_isUnit_det e w hdet
  have hcoord : ∀ i : ι, EtaleCoordinates.coord k ι A i = w i := by
    intro i
    rw [EtaleCoordinates.coord_def, RingHom.algebraMap_toAlgebra]
    simp
  refine ⟨fun i => EtaleCoordinates.partialDeriv k ι A i, ?_, ?_⟩
  · intro i j
    rw [← hcoord j]
    exact EtaleCoordinates.partialDeriv_coord k ι A i j
  · intro i j a
    exact EtaleCoordinates.partialDeriv_comm k ι A i j a

theorem exists_regularParameters_of_formallyEtale (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (q : Ideal S) [q.IsPrime] (A : Type*) [CommRing A] [Algebra S A] [Algebra k A]
    [IsScalarTower k S A] [IsLocalization q.primeCompl A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k (IsLocalRing.ResidueField A)] [IsScalarTower k A (IsLocalRing.ResidueField A)]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] :
    ∃ (h : ℕ) (x : Fin h → A) (D : Fin h → Derivation k A A),
      Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A ∧
      (∀ i j : Fin h, D i (x j) = if i = j then 1 else 0) ∧
      (∀ i j : Fin h, ∀ a : A, D i (D j a) = D j (D i a)) := by
  obtain ⟨g, w, J, hgq, -, hspan, -, hgdet, -⟩ :=
    EtaleCoordinates.exists_adapted_parameters k ι S q A
  let _ : Algebra (MvPolynomial ι k) A :=
    ((algebraMap S A).comp (algebraMap (MvPolynomial ι k) S)).toAlgebra
  have halg : (algebraMap (MvPolynomial ι k) A)
      = (algebraMap S A).comp (algebraMap (MvPolynomial ι k) S) := rfl
  have : IsScalarTower (MvPolynomial ι k) S A :=
    IsScalarTower.of_algebraMap_eq fun z => by rw [halg]; rfl
  have : IsScalarTower k (MvPolynomial ι k) A :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [halg, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S,
        ← IsScalarTower.algebraMap_apply k S A]
  have : Algebra.FormallyEtale S A := Algebra.FormallyEtale.of_isLocalization q.primeCompl
  have : Algebra.FormallyEtale (MvPolynomial ι k) A :=
    Algebra.FormallyEtale.comp (MvPolynomial ι k) S A
  have : Algebra.FormallySmooth k A := Algebra.FormallySmooth.comp k (MvPolynomial ι k) A
  obtain ⟨e, he⟩ : ∃ e : Module.Basis ι A (KaehlerDifferential k A),
      IsUnit (e.det fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i))) := by
    refine ⟨EtaleCoordinates.basisKaehler k ι A, ?_⟩
    rw [← EtaleCoordinates.algebraMap_det_basisKaehler k ι S A w, ← hgdet]
    exact IsLocalization.map_units (M := q.primeCompl) A ⟨g, hgq⟩
  obtain ⟨D, hD, hDD⟩ :=
    exists_commuting_dual_derivations_consolidated139 k ι A e (fun i => algebraMap S A (w i)) he
  obtain ⟨h, ix, hix, hrange⟩ :
      ∃ (h : ℕ) (ix : Fin h → ι), Function.Injective ix ∧ Set.range ix = (↑J : Set ι) := by
    refine ⟨J.card, fun i => ((J.equivFin.symm i : {a : ι // a ∈ J}) : ι), ?_, ?_⟩
    · intro a b hab
      exact J.equivFin.symm.injective (Subtype.ext hab)
    · ext l
      simp only [Set.mem_range, Finset.mem_coe]
      constructor
      · rintro ⟨i, rfl⟩
        exact (J.equivFin.symm i).2
      · intro hl
        exact ⟨J.equivFin ⟨l, hl⟩, by simp⟩
  have hset : (algebraMap S A) '' (w '' (↑J : Set ι))
      = Set.range fun i => algebraMap S A (w (ix i)) := by
    rw [← hrange]
    ext a
    constructor
    · rintro ⟨b, ⟨l, ⟨i, rfl⟩, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨w (ix i), ⟨ix i, ⟨i, rfl⟩, rfl⟩, rfl⟩
  refine ⟨h, fun i => algebraMap S A (w (ix i)), fun i => D (ix i), ?_, ?_, ?_⟩
  · rw [← hspan, Ideal.map_span, hset]
  · intro i j
    rw [hD]
    simp only [show (ix i = ix j) ↔ (i = j) from ⟨fun hc => hix hc, fun hc => by rw [hc]⟩]
  · intro i j a
    exact hDD (ix i) (ix j) a


end

section
variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
include p

theorem exists_regularParameters_stalk_of_smooth (x : X) :
    letI := stalkAlgebra k p x
    ∃ (h : ℕ) (y : Fin h → X.presheaf.stalk x)
      (D : Fin h → Derivation k (X.presheaf.stalk x) (X.presheaf.stalk x)),
      Ideal.span (Set.range y) = IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
      (∀ i j : Fin h, D i (y j) = if i = j then 1 else 0) ∧
      (∀ i j : Fin h, ∀ a : X.presheaf.stalk x, D i (D j a) = D j (D i a)) := by
  let _ := stalkAlgebra k p x
  obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p x
  let _ := sectionsAlgebra k p U
  let _ := c.algebra
  let _ : DecidableEq (ULift.{u} (Fin m)) := Classical.decEq _
  have := c.algebra_formallyEtale hU
  have := c.isScalarTower
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  have : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) :=
    isScalarTower_stalk k p U x hxU (algebraMap_sectionsAlgebra k p U)
      (algebraMap_stalkAlgebra k p x) rfl
  have : IsLocalization ((hU.primeIdealOf ⟨x, hxU⟩).asIdeal).primeCompl
      (X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hxU⟩
  have := isNoetherianRing_stalk k p x
  let _ : Algebra k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    ((IsLocalRing.residue (X.presheaf.stalk x)).comp (stalkAlgebraMap k p x)).toAlgebra
  have : IsScalarTower k (X.presheaf.stalk x)
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsLocalRing.ResidueField.algebraMap_eq]
      rfl
  have := formallySmooth_residueField k p x rfl
  exact exists_regularParameters_of_formallyEtale k (ULift.{u} (Fin m)) Γ(X, U)
    ((hU.primeIdealOf ⟨x, hxU⟩).asIdeal) (X.presheaf.stalk x)

theorem orderAt_mul (I J : X.IdealSheafData) (x : X) :
    orderAt (I * J) x = orderAt I x + orderAt J x := by
  let _ := stalkAlgebra k p x
  have := isNoetherianRing_stalk k p x
  obtain ⟨h, y, D, hspan, hD, hDD⟩ := exists_regularParameters_stalk_of_smooth k p x
  simp only [orderAt_eq_idealOrder, stalkIdeal_mul]
  exact idealOrder_mul y D hspan hD hDD (fun n hn => isUnit_natCast_stalk k p x hn)
    (stalkIdeal I x) (stalkIdeal J x)

theorem orderAt_pow (I : X.IdealSheafData) (c : ℕ) (x : X) :
    orderAt (I ^ c) x = (c : ℕ∞) * orderAt I x := by
  let _ := stalkAlgebra k p x
  have := isNoetherianRing_stalk k p x
  obtain ⟨h, y, D, hspan, hD, hDD⟩ := exists_regularParameters_stalk_of_smooth k p x
  simp only [orderAt_eq_idealOrder, stalkIdeal_pow]
  exact idealOrder_pow y D hspan hD hDD (fun n hn => isUnit_natCast_stalk k p x hn)
    (stalkIdeal I x) c


end

theorem natCast_mul_le_mul_iff {c : ℕ} (hc : 1 ≤ c) (m : ℕ) (a : ℕ∞) :
    (c : ℕ∞) * (m : ℕ∞) ≤ (c : ℕ∞) * a ↔ (m : ℕ∞) ≤ a := by
  induction a using ENat.recTopCoe with
  | top =>
    have hc0 : (c : ℕ∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have htop : (c : ℕ∞) * ⊤ = ⊤ := by simp [hc0]
    simp [htop]
  | coe n =>
    constructor
    · intro hle
      have h' : c * m ≤ c * n := by exact_mod_cast hle
      have h'' : m ≤ n := Nat.le_of_mul_le_mul_left h' (by omega)
      exact_mod_cast h''
    · intro hle
      have h' : m ≤ n := by exact_mod_cast hle
      have h'' : c * m ≤ c * n := Nat.mul_le_mul (le_refl c) h'
      exact_mod_cast h''

theorem orderAtLeastLocus_pow_mul (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (I : X.IdealSheafData) {c : ℕ} (hc : 1 ≤ c) (m : ℕ) :
    orderAtLeastLocus (I ^ c) (c * m) = orderAtLeastLocus I m := by
  ext x
  rw [mem_orderAtLeastLocus_iff, mem_orderAtLeastLocus_iff, orderAt_pow k p I c x, Nat.cast_mul]
  exact natCast_mul_le_mul_iff hc m (orderAt I x)

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
section

open CategoryTheory AlgebraicGeometry TopologicalSpace


private theorem le_natCast_or_succ_le_consolidated156 (a : ℕ∞) (r : ℕ) :
    a ≤ (r : ℕ∞) ∨ ((r + 1 : ℕ) : ℕ∞) ≤ a := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · exact Or.inr le_top
  · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 ha
    rcases Nat.lt_or_ge r m with hm | hm
    · exact Or.inr (by exact_mod_cast hm)
    · exact Or.inl (by exact_mod_cast hm)

section
variable {X Y : Scheme.{u}} (h : Y ⟶ X)

private theorem germ_comp_appLE_consolidated156 (U : X.Opens) (V : Y.Opens)
    (e : V ≤ h ⁻¹ᵁ U) (y : Y) (hy : y ∈ V) :
    (Y.presheaf.germ V y hy).hom.comp (h.appLE U V e).hom
      = (h.stalkMap y).hom.comp (X.presheaf.germ U (h.base y) (e hy)).hom := by
  have key : h.appLE U V e ≫ Y.presheaf.germ V y hy
      = X.presheaf.germ U (h.base y) (e hy) ≫ h.stalkMap y := by
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    exact (Scheme.Hom.germ_stalkMap ..).symm
  simpa only [CommRingCat.hom_comp] using congrArg CommRingCat.Hom.hom key

theorem stalkIdeal_comap (I : X.IdealSheafData) (y : Y) :
    stalkIdeal (I.comap h) y =
      Ideal.map (h.stalkMap y).hom (stalkIdeal I (h.base y)) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
      (show h.base y ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨V, hV, hyV, e⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (show y ∈ h ⁻¹ᵁ U from hxU)
  have hcomp : (Y.presheaf.germ V y hyV).hom.comp (h.appLE U V e).hom
      = (h.stalkMap y).hom.comp (X.presheaf.germ U (h.base y) hxU).hom :=
    germ_comp_appLE_consolidated156 h U V e y hyV
  rw [stalkIdeal_eq_map_germ (I.comap h) y ⟨V, hV⟩ hyV,
    stalkIdeal_eq_map_germ I (h.base y) ⟨U, hU⟩ hxU,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE I h ⟨U, hU⟩ ⟨V, hV⟩ e,
    Ideal.map_map, Ideal.map_map]
  exact congrArg (fun φ => Ideal.map φ (I.ideal ⟨U, hU⟩)) hcomp

theorem orderAt_le_orderAt_comap (I : X.IdealSheafData) (y : Y) :
    orderAt I (h.base y) ≤ orderAt (I.comap h) y := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  rw [le_orderAt_iff] at hn ⊢
  rw [stalkIdeal_comap]
  have hmono : Ideal.map (h.stalkMap y).hom (stalkIdeal I (h.base y))
      ≤ Ideal.map (h.stalkMap y).hom
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (h.base y)) ^ n) := Ideal.map_mono hn
  exact le_trans hmono
    (le_trans (Ideal.map_pow ..).le
      (Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le ..) n))

private theorem one_le_orderAt_of_one_le_orderAt_comap_consolidated156 (J : X.IdealSheafData)
    (y : Y) (hy : (1 : ℕ∞) ≤ orderAt (J.comap h) y) : (1 : ℕ∞) ≤ orderAt J (h.base y) := by
  have h1 : ((1 : ℕ) : ℕ∞) ≤ orderAt (J.comap h) y := by exact_mod_cast hy
  suffices hs : ((1 : ℕ) : ℕ∞) ≤ orderAt J (h.base y) by exact_mod_cast hs
  rw [le_orderAt_iff] at h1 ⊢
  rw [stalkIdeal_comap, pow_one] at h1
  rw [pow_one]
  simpa only [IsLocalRing.maximalIdeal_comap] using
    Ideal.le_comap_map.trans (Ideal.comap_mono h1)


end

section
variable (k : Type u) [Field k] [CharZero k] {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (h : Y ⟶ X) [Smooth h] (I : X.IdealSheafData)
include p

theorem orderAt_comap (y : Y) :
    orderAt (I.comap h) y = orderAt I (h.base y) := by
  have : LocallyOfFiniteType p := inferInstance
  have : LocallyOfFiniteType (h ≫ p) := inferInstance
  refine le_antisymm ?_ (orderAt_le_orderAt_comap h I y)
  rcases eq_or_ne (orderAt I (h.base y)) ⊤ with hI | hI
  · rw [hI]; exact le_top
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 hI
  rw [← hr]
  rcases le_natCast_or_succ_le_consolidated156 (orderAt (I.comap h) y) r with hle | hlt
  · exact hle
  exfalso
  have h1 : ((1 : ℕ) : ℕ∞) ≤ orderAt (derivIdealSheafIterate k (h ≫ p) r (I.comap h)) y :=
    le_orderAt_derivIdealSheafIterate k (h ≫ p) (I.comap h) y 1 r (by
      rw [Nat.add_comm]; exact hlt)
  rw [derivIdealSheafIterate_comap k p h r I] at h1
  have h2 : (1 : ℕ∞) ≤ orderAt ((derivIdealSheafIterate k p r I).comap h) y := by exact_mod_cast h1
  have h3 := one_le_orderAt_of_one_le_orderAt_comap_consolidated156 h (derivIdealSheafIterate k p r I) y h2
  have h4 : orderAt (derivIdealSheafIterate k p r I) (h.base y) = ((r - r : ℕ) : ℕ∞) :=
    orderAt_derivIdealSheafIterate_eq_sub k p I (h.base y) hr.symm (le_refl r)
  rw [h4, Nat.sub_self] at h3
  simp at h3

theorem orderAtLeastLocus_comap (m : ℕ) :
    orderAtLeastLocus (I.comap h) m = ⇑h.base ⁻¹' orderAtLeastLocus I m := by
  ext y
  simp only [Set.mem_preimage, mem_orderAtLeastLocus_iff, orderAt_comap k p h I y]


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PartialDerivativeIdeal
section

namespace EtaleCoordinates

variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S]

theorem coord_smul_partialDeriv_mem_tangentDerivations (h : ι) :
    coord k ι S h • partialDeriv k ι S h ∈
      tangentDerivations k (Ideal.span ({coord k ι S h} : Set S)) :=
  smul_mem_tangentDerivations k (Ideal.span ({coord k ι S h} : Set S))
    (Ideal.mem_span_singleton_self (coord k ι S h)) (partialDeriv k ι S h)

theorem partialDeriv_mem_tangentDerivations_of_ne {i h : ι} (hih : i ≠ h) :
    partialDeriv k ι S i ∈ tangentDerivations k (Ideal.span ({coord k ι S h} : Set S)) := by
  rw [mem_tangentDerivations_span_singleton, partialDeriv_coord_of_ne k ι S i h hih]
  exact Submodule.zero_mem _

theorem coord_mul_partialDeriv_mem_logDerivIdeal (h : ι) (J : Ideal S) {g : S} (hg : g ∈ J) :
    coord k ι S h * partialDeriv k ι S h g ∈
      logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) J := by
  have hmem := derivation_apply_mem_logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) J
    (coord k ι S h • partialDeriv k ι S h)
    (coord_smul_partialDeriv_mem_tangentDerivations k ι S h) hg
  simpa [smul_eq_mul] using hmem

theorem partialDeriv_mem_logDerivIdeal_of_ne {i h : ι} (hih : i ≠ h) (J : Ideal S) {g : S}
    (hg : g ∈ J) :
    partialDeriv k ι S i g ∈ logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) J :=
  derivation_apply_mem_logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) J
    (partialDeriv k ι S i) (partialDeriv_mem_tangentDerivations_of_ne k ι S hih) hg

def partialDerivIdeal (h : ι) (J : Ideal S) : Ideal S :=
  J ⊔ Ideal.span {x : S | ∃ g ∈ J, partialDeriv k ι S h g = x}

section
variable (h : ι) (J : Ideal S)

private theorem partialDerivIdeal_def_consolidated158 :
    partialDerivIdeal k ι S h J =
      J ⊔ Ideal.span {x : S | ∃ g ∈ J, partialDeriv k ι S h g = x} := rfl

theorem le_partialDerivIdeal : J ≤ partialDerivIdeal k ι S h J := by
  rw [partialDerivIdeal_def_consolidated158]
  exact le_sup_left

theorem partialDeriv_mem_partialDerivIdeal {g : S} (hg : g ∈ J) :
    partialDeriv k ι S h g ∈ partialDerivIdeal k ι S h J := by
  rw [partialDerivIdeal_def_consolidated158]
  exact Submodule.mem_sup_right (Ideal.subset_span ⟨g, hg, rfl⟩)


end

section
variable (h : ι)

theorem partialDerivIdeal_le_iff (J K : Ideal S) :
    partialDerivIdeal k ι S h J ≤ K ↔ J ≤ K ∧ ∀ g ∈ J, partialDeriv k ι S h g ∈ K := by
  rw [partialDerivIdeal_def_consolidated158, sup_le_iff, Ideal.span_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun g hg => h2 ⟨g, hg, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro x hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact h2 g hg

theorem partialDerivIdeal_le {J K : Ideal S} (hJK : J ≤ K)
    (hD : ∀ g ∈ J, partialDeriv k ι S h g ∈ K) : partialDerivIdeal k ι S h J ≤ K :=
  (partialDerivIdeal_le_iff k ι S h J K).mpr ⟨hJK, hD⟩

theorem partialDerivIdeal_mono : Monotone (partialDerivIdeal k ι S h) := by
  intro I J hIJ
  rw [partialDerivIdeal_le_iff]
  refine ⟨hIJ.trans (le_partialDerivIdeal k ι S h J), fun g hg => ?_⟩
  exact partialDeriv_mem_partialDerivIdeal k ι S h J (hIJ hg)


end

def partialDerivIdealIterate (h : ι) : ℕ → Ideal S → Ideal S
  | 0, J => J
  | l + 1, J => partialDerivIdeal k ι S h (partialDerivIdealIterate h l J)

section
variable (h : ι)

theorem partialDerivIdealIterate_zero (J : Ideal S) :
    partialDerivIdealIterate k ι S h 0 J = J := rfl

theorem partialDerivIdealIterate_succ (l : ℕ) (J : Ideal S) :
    partialDerivIdealIterate k ι S h (l + 1) J =
      partialDerivIdeal k ι S h (partialDerivIdealIterate k ι S h l J) := rfl


end

private def evalDerivationAddHom_consolidated158 (g : S) : Derivation k S S →+ S where
  toFun D := D g
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S] in
private theorem derivation_sum_apply_consolidated158 (s : Finset ι) (f : ι → Derivation k S S) (g : S) :
    (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g :=
  map_sum (evalDerivationAddHom_consolidated158 k S g) f s

theorem derivation_apply_eq_sum_partialDeriv [Fintype ι] (D : Derivation k S S) (g : S) :
    D g = ∑ i, D (coord k ι S i) * partialDeriv k ι S i g := by
  have h1 : D g = (∑ i, D (coord k ι S i) • partialDeriv k ι S i : Derivation k S S) g :=
    congrArg (fun E : Derivation k S S => E g) (eq_sum_smul_partialDeriv k ι S D)
  have h2 : (∑ i, D (coord k ι S i) • partialDeriv k ι S i : Derivation k S S) g
      = ∑ i, D (coord k ι S i) * partialDeriv k ι S i g :=
    derivation_sum_apply_consolidated158 k ι S Finset.univ (fun i => D (coord k ι S i) • partialDeriv k ι S i) g
  exact h1.trans h2

private theorem derivIdeal_le_logDerivIdeal_sup_partialDerivIdeal_consolidated158 [Fintype ι] (h : ι) (I : Ideal S) :
    derivIdeal k I ≤
      logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) I ⊔ partialDerivIdeal k ι S h I := by
  rw [derivIdeal_le_iff]
  refine ⟨(le_logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) I).trans le_sup_left, ?_⟩
  intro D g hg
  rw [derivation_apply_eq_sum_partialDeriv k ι S D g]
  refine Ideal.sum_mem _ ?_
  intro i _
  by_cases hi : i = h
  · rw [hi]
    exact Submodule.mem_sup_right
      (Ideal.mul_mem_left _ _ (partialDeriv_mem_partialDerivIdeal k ι S h I hg))
  · exact Submodule.mem_sup_left
      (Ideal.mul_mem_left _ _ (partialDeriv_mem_logDerivIdeal_of_ne k ι S hi I hg))

private def idealInfComapPartialDeriv_consolidated158 (h : ι) (K : Ideal S) : Ideal S where
  carrier := {g : S | g ∈ K ∧ partialDeriv k ι S h g ∈ K}
  add_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨Submodule.add_mem K ha1 hb1, ?_⟩
    rw [map_add]
    exact Submodule.add_mem K ha2 hb2
  zero_mem' := by
    refine ⟨Submodule.zero_mem K, ?_⟩
    rw [map_zero]
    exact Submodule.zero_mem K
  smul_mem' := by
    intro c x hx
    obtain ⟨hx1, hx2⟩ := hx
    refine ⟨Ideal.mul_mem_left K c hx1, ?_⟩
    have hl : partialDeriv k ι S h (c * x)
        = c * partialDeriv k ι S h x + x * partialDeriv k ι S h c := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    show partialDeriv k ι S h (c * x) ∈ K
    rw [hl]
    exact Submodule.add_mem K (Ideal.mul_mem_left K c hx2) (Ideal.mul_mem_right _ K hx1)

private theorem mem_idealInfComapPartialDeriv_iff_consolidated158 (h : ι) (K : Ideal S) (g : S) :
    g ∈ idealInfComapPartialDeriv_consolidated158 k ι S h K ↔ g ∈ K ∧ partialDeriv k ι S h g ∈ K := Iff.rfl

section
variable [Fintype ι] [DecidableEq ι] (h : ι)

private theorem partialDerivIdeal_logDerivIdeal_le_consolidated158 (I : Ideal S) :
    partialDerivIdeal k ι S h
        (logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) I) ≤
      logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) (partialDerivIdeal k ι S h I) := by
  have key : logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) I ≤
      idealInfComapPartialDeriv_consolidated158 k ι S h
        (logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S))
          (partialDerivIdeal k ι S h I)) := by
    rw [logDerivIdeal_le_iff]
    constructor
    · intro g hg
      rw [mem_idealInfComapPartialDeriv_iff_consolidated158]
      refine ⟨?_, ?_⟩
      · exact le_logDerivIdeal k _ _ (le_partialDerivIdeal k ι S h I hg)
      · exact le_logDerivIdeal k _ _ (partialDeriv_mem_partialDerivIdeal k ι S h I hg)
    · intro D hD y hy
      rw [mem_idealInfComapPartialDeriv_iff_consolidated158]
      have hDmem : D (coord k ι S h) ∈ Ideal.span ({coord k ι S h} : Set S) :=
        (mem_tangentDerivations_span_singleton k (coord k ι S h) D).mp hD
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hDmem
      refine ⟨?_, ?_⟩
      · exact logDerivIdeal_mono k _ (le_partialDerivIdeal k ι S h I)
          (derivation_apply_mem_logDerivIdeal k _ I D hD hy)
      · rw [derivation_apply_eq_sum_partialDeriv k ι S D y]
        rw [map_sum]
        refine Ideal.sum_mem _ ?_
        intro i _
        rw [Derivation.leibniz]
        refine Submodule.add_mem _ ?_ ?_
        · by_cases hi : i = h
          · rw [hi, smul_eq_mul, ← hc, mul_assoc]
            refine Ideal.mul_mem_left _ _ ?_
            exact coord_mul_partialDeriv_mem_logDerivIdeal k ι S h
              (partialDerivIdeal k ι S h I)
              (partialDeriv_mem_partialDerivIdeal k ι S h I hy)
          · rw [smul_eq_mul, partialDeriv_comm k ι S h i y]
            refine Ideal.mul_mem_left _ _ ?_
            exact partialDeriv_mem_logDerivIdeal_of_ne k ι S hi
              (partialDerivIdeal k ι S h I)
              (partialDeriv_mem_partialDerivIdeal k ι S h I hy)
        · by_cases hi : i = h
          · rw [hi, smul_eq_mul]
            refine Ideal.mul_mem_right _ _ ?_
            exact le_logDerivIdeal k _ _ (partialDeriv_mem_partialDerivIdeal k ι S h I hy)
          · rw [smul_eq_mul]
            refine Ideal.mul_mem_right _ _ ?_
            exact logDerivIdeal_mono k _ (le_partialDerivIdeal k ι S h I)
              (partialDeriv_mem_logDerivIdeal_of_ne k ι S hi I hy)
  refine partialDerivIdeal_le k ι S h ?_ ?_
  · intro g hg
    exact ((mem_idealInfComapPartialDeriv_iff_consolidated158 k ι S h _ g).mp (key hg)).1
  · intro g hg
    exact ((mem_idealInfComapPartialDeriv_iff_consolidated158 k ι S h _ g).mp (key hg)).2

private theorem partialDerivIdeal_logDerivIdealIterate_le_consolidated158 (m : ℕ)
    (I : Ideal S) :
    partialDerivIdeal k ι S h
        (logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) m I) ≤
      logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) m
        (partialDerivIdeal k ι S h I) := by
  induction m with
  | zero => exact le_of_eq (by simp only [logDerivIdealIterate_zero])
  | succ m ih =>
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ]
      exact (partialDerivIdeal_logDerivIdeal_le_consolidated158 k ι S h _).trans (logDerivIdeal_mono k _ ih)

theorem derivIdealIterate_le_iSup_logDerivIdealIterate_partialDerivIdealIterate (n : ℕ) (J : Ideal S) :
    derivIdealIterate k n J ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) (n - l)
          (partialDerivIdealIterate k ι S h l J) := by
  induction n with
  | zero =>
      rw [derivIdealIterate_zero]
      exact le_iSup₂ (f := fun m (_ : m ≤ 0) =>
        logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) (0 - m)
          (partialDerivIdealIterate k ι S h m J)) 0 le_rfl
  | succ n ih =>
      rw [derivIdealIterate_succ]
      refine le_trans (derivIdeal_mono k ih) ?_
      refine le_trans (derivIdeal_iSup_le k _) ?_
      refine iSup_le fun l => ?_
      refine le_trans (derivIdeal_iSup_le k _) ?_
      refine iSup_le fun hl => ?_
      refine le_trans (derivIdeal_le_logDerivIdeal_sup_partialDerivIdeal_consolidated158 k ι S h _) ?_
      refine sup_le ?_ ?_
      · rw [← logDerivIdealIterate_succ, show n - l + 1 = n + 1 - l from by omega]
        exact le_iSup₂ (f := fun m (_ : m ≤ n + 1) =>
          logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) (n + 1 - m)
            (partialDerivIdealIterate k ι S h m J)) l (by omega)
      · refine le_trans (partialDerivIdeal_logDerivIdealIterate_le_consolidated158 k ι S h (n - l) _) ?_
        rw [← partialDerivIdealIterate_succ, show n - l = n + 1 - (l + 1) from by omega]
        exact le_iSup₂ (f := fun m (_ : m ≤ n + 1) =>
          logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) (n + 1 - m)
            (partialDerivIdealIterate k ι S h m J)) (l + 1) (by omega)


end

end EtaleCoordinates

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.ControlledTransformLogDerivativesInCharts
section
namespace EtaleCoordinates

section

variable (k : Type*) [CommRing k] (ι : Type*)
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]

theorem partialDerivIdeal_iSup_le {κ : Sort*} (h : ι) (F : κ → Ideal S) :
    partialDerivIdeal k ι S h (⨆ j, F j) ≤ ⨆ j, partialDerivIdeal k ι S h (F j) := by
  refine partialDerivIdeal_le k ι S h (iSup_mono fun j => le_partialDerivIdeal k ι S h (F j)) ?_
  intro g hg
  refine Submodule.iSup_induction (motive := fun x =>
      partialDeriv k ι S h x ∈ ⨆ j, partialDerivIdeal k ι S h (F j)) (fun j => F j) hg ?_ ?_ ?_
  · intro j x hx
    exact le_iSup (fun j => partialDerivIdeal k ι S h (F j)) j
      (partialDeriv_mem_partialDerivIdeal k ι S h (F j) hx)
  · simp only [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy
    simp only [map_add]
    exact Submodule.add_mem _ hx hy

theorem partialDerivIdeal_biSup_le (h : ι) (n : ℕ) (F : ℕ → Ideal S) :
    partialDerivIdeal k ι S h (⨆ i, ⨆ _ : i ≤ n, F i) ≤
      ⨆ i, ⨆ _ : i ≤ n, partialDerivIdeal k ι S h (F i) :=
  (partialDerivIdeal_iSup_le k ι S h (fun i => ⨆ _ : i ≤ n, F i)).trans
    (iSup_mono fun i => partialDerivIdeal_iSup_le k ι S h (fun _ : i ≤ n => F i))

end

section

variable (k : Type*) [CommRing k] (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S₁ : Type*) [CommRing S₁] [Algebra k S₁] [Algebra (MvPolynomial ι k) S₁]
  [IsScalarTower k (MvPolynomial ι k) S₁] [Algebra.FormallyEtale (MvPolynomial ι k) S₁]
  (φ : S →ₐ[k] S₁) (T : Finset ι) (s h : ι)

theorem partialDerivIdeal_controlledTransform_le_sup
    (_hsT : s ∈ T)
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (hhT : h ∈ T) (hhs : h ≠ s)
    (J : Ideal S) (L : ℕ → Ideal S₁) (m : ℕ)
    (hL : ∀ i ≤ m,
      Ideal.span {coord k ι S₁ s ^ (m - i)} * L i = Ideal.map φ (derivIdealIterate k i J))
    (i : ℕ) (hi : i < m) :
    partialDerivIdeal k ι S₁ h (L i) ≤ L i ⊔ L (i + 1) := by
  refine partialDerivIdeal_le k ι S₁ h le_sup_left ?_
  intro g hg
  have hc : m - i = (m - i - 1) + 1 := by omega
  have hJ : Ideal.span {coord k ι S₁ s ^ ((m - i - 1) + 1)} * L i
      = Ideal.map φ (derivIdealIterate k i J) := by
    rw [← hc]
    exact hL i (le_of_lt hi)
  have hD : Ideal.map φ (derivIdeal k (derivIdealIterate k i J)) ≤
      Ideal.span {coord k ι S₁ s ^ (m - i - 1)} * L (i + 1) := by
    have h2 := hL (i + 1) (by omega)
    have h3 : m - (i + 1) = m - i - 1 := by omega
    rw [h3] at h2
    rw [← derivIdealIterate_succ]
    exact le_of_eq h2.symm
  exact partialDeriv_mem_sup_of_span_pow_mul_eq_map k ι S S₁ φ T s hin hs hout hnzd h hhT hhs
    (derivIdealIterate k i J) (L i) (L (i + 1)) (m - i - 1) hJ hD g hg

theorem partialDerivIdealIterate_controlledTransform_le_iSup
    (hsT : s ∈ T)
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (hhT : h ∈ T) (hhs : h ≠ s)
    (J : Ideal S) (L : ℕ → Ideal S₁) (m : ℕ)
    (hL : ∀ i ≤ m,
      Ideal.span {coord k ι S₁ s ^ (m - i)} * L i = Ideal.map φ (derivIdealIterate k i J))
    (l : ℕ) (hl : l ≤ m) :
    partialDerivIdealIterate k ι S₁ h l (L 0) ≤ ⨆ i, ⨆ _ : i ≤ l, L i := by
  revert hl
  induction l with
  | zero =>
      intro _
      rw [partialDerivIdealIterate_zero]
      exact le_iSup₂ (f := fun i (_ : i ≤ 0) => L i) 0 le_rfl
  | succ l ih =>
      intro hl
      rw [partialDerivIdealIterate_succ]
      have hlm : l ≤ m := Nat.le_of_succ_le hl
      have h1 := ih hlm
      refine le_trans (partialDerivIdeal_mono k ι S₁ h h1) ?_
      refine le_trans (partialDerivIdeal_biSup_le k ι S₁ h l L) ?_
      refine iSup_le fun i => iSup_le fun hi => ?_
      have him : i < m := lt_of_le_of_lt hi (by omega)
      have hstep := partialDerivIdeal_controlledTransform_le_sup k ι S S₁ φ T s h
        hsT hin hs hout hnzd hhT hhs J L m hL i him
      refine hstep.trans (sup_le ?_ ?_)
      · exact le_iSup₂ (f := fun j (_ : j ≤ l + 1) => L j) i (by omega)
      · exact le_iSup₂ (f := fun j (_ : j ≤ l + 1) => L j) (i + 1) (by omega)

theorem derivIdealIterate_le_iSup_logDerivIdealIterate_controlledTransform [Fintype ι]
    (hsT : s ∈ T)
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (hhT : h ∈ T) (hhs : h ≠ s)
    (J : Ideal S) (L : ℕ → Ideal S₁) (m : ℕ)
    (hL : ∀ i ≤ m,
      Ideal.span {coord k ι S₁ s ^ (m - i)} * L i = Ideal.map φ (derivIdealIterate k i J))
    (n : ℕ) (hn : n ≤ m) :
    derivIdealIterate k n (L 0) ≤
      ⨆ i, ⨆ _ : i ≤ n,
        logDerivIdealIterate k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - i) (L i) := by
  refine (derivIdealIterate_le_iSup_logDerivIdealIterate_partialDerivIdealIterate k ι S₁ h n (L 0)).trans ?_
  refine iSup_le fun l => iSup_le fun hln => ?_
  have hlm : l ≤ m := hln.trans hn
  have h1 : partialDerivIdealIterate k ι S₁ h l (L 0) ≤ ⨆ i, ⨆ _ : i ≤ l, L i :=
    partialDerivIdealIterate_controlledTransform_le_iSup k ι S S₁ φ T s h
      hsT hin hs hout hnzd hhT hhs J L m hL l hlm
  refine (logDerivIdealIterate_mono k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - l) h1).trans ?_
  refine (logDerivIdealIterate_iSup_le k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - l)
    (fun i => ⨆ _ : i ≤ l, L i)).trans ?_
  refine iSup_le fun i => ?_
  refine (logDerivIdealIterate_iSup_le k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - l)
    (fun _ : i ≤ l => L i)).trans ?_
  refine iSup_le fun hi => ?_
  have h2 : logDerivIdealIterate k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - l) (L i) ≤
      logDerivIdealIterate k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - i) (L i) :=
    logDerivIdealIterate_le_of_le k (Ideal.span ({coord k ι S₁ h} : Set S₁))
      (by omega : n - l ≤ n - i) (L i)
  exact h2.trans (le_iSup₂
    (f := fun j (_ : j ≤ n) =>
      logDerivIdealIterate k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - j) (L j))
    i (hi.trans hln))

end

end EtaleCoordinates
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedIdeal
section

def tuningWeight (m : ℕ) (c : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range m, (m - j) * c j

theorem tuningWeight_eq_sum (m : ℕ) (c : ℕ → ℕ) :
    tuningWeight m c = ∑ j ∈ Finset.range m, (m - j) * c j := rfl

section
variable (m : ℕ) (c d : ℕ → ℕ)

theorem tuningWeight_fun_add :
    tuningWeight m (fun j => c j + d j) = tuningWeight m c + tuningWeight m d := by
  simp [tuningWeight, Nat.mul_add, Finset.sum_add_distrib]

theorem tuningWeight_add :
    tuningWeight m (c + d) = tuningWeight m c + tuningWeight m d :=
  tuningWeight_fun_add m c d


end

section
variable (m n : ℕ) (c : ℕ → ℕ)

theorem tuningWeight_mul_left :
    tuningWeight m (fun j => n * c j) = n * tuningWeight m c := by
  simp [tuningWeight, Finset.mul_sum, Nat.mul_left_comm]

theorem tuningWeight_nsmul :
    tuningWeight m (n • c) = n * tuningWeight m c := by
  have : (n • c) = fun j => n * c j := by
    funext j
    simp [Pi.smul_apply, smul_eq_mul]
  rw [this, tuningWeight_mul_left]


end

theorem tuningWeight_single (m i : ℕ) (hi : i ∈ Finset.range m) :
    tuningWeight m (Pi.single i 1) = m - i := by
  rw [tuningWeight_eq_sum, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hni
    exact absurd hi hni

theorem listProd_map_range_eq_prod {M : Type*} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    (List.map f (List.range m)).prod = ∏ j ∈ Finset.range m, f j := by
  induction m with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]
      simp

section

variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]

def tuningMonomial (J : Ideal S) (m : ℕ) (c : ℕ → ℕ) : Ideal S :=
  ∏ j ∈ Finset.range m, derivIdealIterate k j J ^ c j

section
variable (J : Ideal S) (m : ℕ)

theorem tuningMonomial_eq_prod (c : ℕ → ℕ) :
    tuningMonomial k J m c = ∏ j ∈ Finset.range m, derivIdealIterate k j J ^ c j := rfl

theorem tuningMonomial_zero :
    tuningMonomial k J m (fun _ => 0) = ⊤ := by
  simp [tuningMonomial_eq_prod, Ideal.one_eq_top]

theorem tuningMonomial_mul_fun_add (c d : ℕ → ℕ) :
    tuningMonomial k J m c * tuningMonomial k J m d = tuningMonomial k J m (fun j => c j + d j) := by
  rw [tuningMonomial_eq_prod, tuningMonomial_eq_prod, tuningMonomial_eq_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => (pow_add _ _ _).symm

theorem tuningMonomial_mul (c d : ℕ → ℕ) :
    tuningMonomial k J m c * tuningMonomial k J m d = tuningMonomial k J m (c + d) :=
  tuningMonomial_mul_fun_add k J m c d


end

section
variable (J : Ideal S) (m n : ℕ) (c : ℕ → ℕ)

private theorem prod_derivIdealIterate_pow_pow_consolidated39 :
    (∏ j ∈ Finset.range m, derivIdealIterate k j J ^ c j) ^ n
      = ∏ j ∈ Finset.range m, derivIdealIterate k j J ^ (n * c j) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ, mul_pow, ih, Finset.prod_range_succ, ← pow_mul,
        Nat.mul_comm (c m) n]

theorem tuningMonomial_pow_fun_mul :
    tuningMonomial k J m c ^ n = tuningMonomial k J m (fun j => n * c j) := by
  rw [tuningMonomial_eq_prod, tuningMonomial_eq_prod]
  exact prod_derivIdealIterate_pow_pow_consolidated39 k J m n c

theorem tuningMonomial_pow :
    tuningMonomial k J m c ^ n = tuningMonomial k J m (n • c) := by
  have h : (n • c) = fun j => n * c j := by
    funext j
    simp [Pi.smul_apply, smul_eq_mul]
  rw [h, tuningMonomial_pow_fun_mul]


end

theorem tuningMonomial_single (J : Ideal S) (m i : ℕ) (hi : i ∈ Finset.range m) :
    tuningMonomial k J m (Pi.single i 1) = derivIdealIterate k i J := by
  rw [tuningMonomial_eq_prod, Finset.prod_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hni
    exact absurd hi hni

def tunedIdeal (J : Ideal S) (m s : ℕ) : Ideal S :=
  ⨆ c : ℕ → ℕ, ⨆ _ : s ≤ tuningWeight m c, tuningMonomial k J m c

section
variable (J : Ideal S) (m s : ℕ)

theorem tunedIdeal_eq_iSup :
    tunedIdeal k J m s = ⨆ c : ℕ → ℕ, ⨆ _ : s ≤ tuningWeight m c, tuningMonomial k J m c := rfl

theorem tuningMonomial_le_tunedIdeal (c : ℕ → ℕ)
    (hc : s ≤ tuningWeight m c) : tuningMonomial k J m c ≤ tunedIdeal k J m s :=
  le_iSup_of_le c (le_iSup_of_le hc le_rfl)

theorem tunedIdeal_le_iff (K : Ideal S) :
    tunedIdeal k J m s ≤ K ↔ ∀ c : ℕ → ℕ, s ≤ tuningWeight m c → tuningMonomial k J m c ≤ K := by
  constructor
  · intro h c hc
    exact le_trans (tuningMonomial_le_tunedIdeal k J m s c hc) h
  · intro h
    exact iSup_le fun c => iSup_le fun hc => h c hc


end

section
variable (J : Ideal S)

theorem tunedIdeal_zero (m : ℕ) : tunedIdeal k J m 0 = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← tuningMonomial_zero k J m]
  exact tuningMonomial_le_tunedIdeal k J m 0 (fun _ => 0) (Nat.zero_le _)

theorem tunedIdeal_antitone (m : ℕ) {s t : ℕ} (h : s ≤ t) :
    tunedIdeal k J m t ≤ tunedIdeal k J m s := by
  rw [tunedIdeal_le_iff]
  intro c hc
  exact tuningMonomial_le_tunedIdeal k J m s c (le_trans h hc)

theorem tunedIdeal_mul_le (m s t : ℕ) :
    tunedIdeal k J m s * tunedIdeal k J m t ≤ tunedIdeal k J m (s + t) := by
  rw [tunedIdeal_eq_iSup, tunedIdeal_eq_iSup, Submodule.iSup_mul]
  refine iSup_le fun c => ?_
  rw [Submodule.iSup_mul]
  refine iSup_le fun hc => ?_
  rw [Submodule.mul_iSup]
  refine iSup_le fun d => ?_
  rw [Submodule.mul_iSup]
  refine iSup_le fun hd => ?_
  rw [tuningMonomial_mul_fun_add]
  refine tuningMonomial_le_tunedIdeal k J m _ _ ?_
  rw [tuningWeight_fun_add]
  exact Nat.add_le_add hc hd


end

private theorem mul_sup_le_consolidated39 {R : Type*} [CommRing R] (B X Y T : Ideal R)
    (hX : B * X ≤ T) (hY : B * Y ≤ T) : B * (X ⊔ Y) ≤ T := by
  refine Ideal.mul_le.mpr ?_
  intro b hb z hz
  rcases Submodule.mem_sup.mp hz with ⟨x, hx, y, hy, rfl⟩
  rw [mul_add]
  exact Submodule.add_mem T (hX (Ideal.mul_mem_mul hb hx)) (hY (Ideal.mul_mem_mul hb hy))

private theorem derivIdeal_one_consolidated39 {A : Type*} [CommRing A] {R : Type*} [CommRing R]
    [Algebra A R] : derivIdeal A (1 : Ideal R) = 1 := by
  rw [Ideal.one_eq_top]
  exact derivIdeal_top A

private theorem tuningWeight_eq_add_sub_of_succ_consolidated39 (m i : ℕ) (hi : i < m) (c d : ℕ → ℕ)
    (hne : ∀ j, j ≠ i → d j = c j) (hdi : d i + 1 = c i) :
    tuningWeight m c = tuningWeight m d + (m - i) := by
  have hmem : i ∈ Finset.range m := Finset.mem_range.mpr hi
  have keyc : tuningWeight m c
      = (m - i) * c i + ∑ j ∈ (Finset.range m).erase i, (m - j) * c j := by
    rw [tuningWeight_eq_sum]
    exact (Finset.add_sum_erase (Finset.range m) (fun j => (m - j) * c j) hmem).symm
  have keyd : tuningWeight m d
      = (m - i) * d i + ∑ j ∈ (Finset.range m).erase i, (m - j) * d j := by
    rw [tuningWeight_eq_sum]
    exact (Finset.add_sum_erase (Finset.range m) (fun j => (m - j) * d j) hmem).symm
  have h3 : ∑ j ∈ (Finset.range m).erase i, (m - j) * d j
      = ∑ j ∈ (Finset.range m).erase i, (m - j) * c j :=
    Finset.sum_congr rfl fun j hj => by rw [hne j (Finset.ne_of_mem_erase hj)]
  rw [keyc, keyd, h3, ← hdi]
  ring

section
variable {A : Type*} [CommRing A] {R : Type*} [CommRing R] [Algebra A R]

private theorem tuningMonomial_eq_derivIdealIterate_mul_of_succ_consolidated39 (J : Ideal R) (m i : ℕ) (hi : i < m) (c d : ℕ → ℕ)
    (hne : ∀ j, j ≠ i → d j = c j) (hdi : d i = c i + 1) :
    tuningMonomial A J m d = derivIdealIterate A i J * tuningMonomial A J m c := by
  have hmem : i ∈ Finset.range m := Finset.mem_range.mpr hi
  have keyd : tuningMonomial A J m d
      = derivIdealIterate A i J ^ d i *
        ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ d j := by
    rw [tuningMonomial_eq_prod]
    exact (Finset.mul_prod_erase (Finset.range m) (fun j => derivIdealIterate A j J ^ d j) hmem).symm
  have keyc : tuningMonomial A J m c
      = derivIdealIterate A i J ^ c i *
        ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ c j := by
    rw [tuningMonomial_eq_prod]
    exact (Finset.mul_prod_erase (Finset.range m) (fun j => derivIdealIterate A j J ^ c j) hmem).symm
  have h3 : ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ d j
      = ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ c j :=
    Finset.prod_congr rfl fun j hj => by rw [hne j (Finset.ne_of_mem_erase hj)]
  rw [keyd, keyc, h3, hdi, pow_succ]
  simp only [mul_comm, mul_assoc]

private theorem derivIdealIterate_succ_mul_tuningMonomial_le_consolidated39 (J : Ideal R) (m s i : ℕ) (hi : i < m) (c d : ℕ → ℕ)
    (hne : ∀ j, j ≠ i → d j = c j) (hdi : d i + 1 = c i) (hc : s + 1 ≤ tuningWeight m c) :
    derivIdealIterate A (i + 1) J * tuningMonomial A J m d ≤ tunedIdeal A J m s := by
  have hw : tuningWeight m c = tuningWeight m d + (m - i) :=
    tuningWeight_eq_add_sub_of_succ_consolidated39 m i hi c d hne hdi
  rcases Nat.lt_or_ge (i + 1) m with hlt | hge
  · have hmono : tuningMonomial A J m (fun j => if j = i + 1 then d j + 1 else d j)
        = derivIdealIterate A (i + 1) J * tuningMonomial A J m d :=
      tuningMonomial_eq_derivIdealIterate_mul_of_succ_consolidated39 J m (i + 1) hlt d (fun j => if j = i + 1 then d j + 1 else d j)
        (fun j hj => by simp [hj]) (by simp)
    have hw' : tuningWeight m (fun j => if j = i + 1 then d j + 1 else d j)
        = tuningWeight m d + (m - (i + 1)) :=
      tuningWeight_eq_add_sub_of_succ_consolidated39 m (i + 1) hlt (fun j => if j = i + 1 then d j + 1 else d j) d
        (fun j hj => by simp [hj]) (by simp)
    refine le_trans (le_of_eq hmono.symm)
      (tuningMonomial_le_tunedIdeal A J m s (fun j => if j = i + 1 then d j + 1 else d j) ?_)
    omega
  · have hle : derivIdealIterate A (i + 1) J * tuningMonomial A J m d ≤ tuningMonomial A J m d :=
      Ideal.mul_le.mpr fun r _ t ht => Ideal.mul_mem_left _ r ht
    refine le_trans hle (tuningMonomial_le_tunedIdeal A J m s d ?_)
    omega

private theorem mul_derivIdeal_prod_le_consolidated39 (J T : Ideal R) (c : ℕ → ℕ) :
    ∀ (n : ℕ) (B : Ideal R),
      B * (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) ≤ T →
      (∀ i, i < n → ∀ d : ℕ → ℕ, (∀ j, j ≠ i → d j = c j) → d i + 1 = c i →
        B * (derivIdealIterate A (i + 1) J *
          ∏ j ∈ Finset.range n, derivIdealIterate A j J ^ d j) ≤ T) →
      B * derivIdeal A (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) ≤ T := by
  intro n
  induction n with
  | zero =>
      intro B h1 _
      rw [Finset.range_zero, Finset.prod_empty, derivIdeal_one_consolidated39, mul_one]
      rw [Finset.range_zero, Finset.prod_empty, mul_one] at h1
      exact h1
  | succ n ih =>
      intro B h1 h2
      rw [Finset.prod_range_succ] at h1
      rw [Finset.prod_range_succ]
      refine le_trans (Ideal.mul_mono le_rfl (derivIdeal_mul_le A _ _)) ?_
      refine mul_sup_le_consolidated39 B _ _ T ?_ ?_
      · rcases Nat.eq_zero_or_pos (c n) with h0 | hpos
        · rw [h0, pow_zero, mul_one] at h1
          rw [h0, pow_zero, derivIdeal_one_consolidated39, mul_one]
          exact h1
        · obtain ⟨e, he⟩ : ∃ e, c n = e + 1 := ⟨c n - 1, by omega⟩
          have hq1 : (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ (if j = n then e else c j))
              = ∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j :=
            Finset.prod_congr rfl fun j hj => by
              rw [if_neg (Nat.ne_of_lt (Finset.mem_range.mp hj))]
          have hq2 : derivIdealIterate A n J ^ (if n = n then e else c n)
              = derivIdealIterate A n J ^ e := by simp
          have hprod : (∏ j ∈ Finset.range (n + 1),
                derivIdealIterate A j J ^ (if j = n then e else c j))
              = (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) *
                derivIdealIterate A n J ^ e := by
            rw [Finset.prod_range_succ, hq1, hq2]
          have hd : B * (derivIdealIterate A (n + 1) J *
              ((∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) *
                derivIdealIterate A n J ^ e)) ≤ T := by
            rw [← hprod]
            exact h2 n (Nat.lt_succ_self n) (fun j => if j = n then e else c j)
              (fun j hj => by simp [hj]) (by simp [he])
          have hstep : derivIdeal A (derivIdealIterate A n J ^ c n)
              ≤ derivIdealIterate A n J ^ e * derivIdealIterate A (n + 1) J := by
            rw [he, derivIdealIterate_succ]
            exact derivIdeal_pow_succ_le A (derivIdealIterate A n J) e
          refine le_trans (Ideal.mul_mono le_rfl (Ideal.mul_mono le_rfl hstep)) ?_
          refine le_trans (le_of_eq ?_) hd
          simp only [mul_comm, mul_left_comm, mul_assoc]
      · have heq : B * (derivIdealIterate A n J ^ c n *
            derivIdeal A (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j))
            = (B * derivIdealIterate A n J ^ c n) *
              derivIdeal A (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) :=
          (mul_assoc _ _ _).symm
        rw [heq]
        refine ih (B * derivIdealIterate A n J ^ c n) ?_ ?_
        · refine le_trans (le_of_eq ?_) h1
          simp only [mul_comm, mul_assoc]
        · intro i hi d hne hdi
          have hd := h2 i (Nat.lt_succ_of_lt hi) d hne hdi
          rw [Finset.prod_range_succ, hne n (by omega : n ≠ i)] at hd
          refine le_trans (le_of_eq ?_) hd
          simp only [mul_comm, mul_left_comm, mul_assoc]


end

section
variable (J : Ideal S)

theorem derivIdeal_tunedIdeal_succ_le (m s : ℕ) :
    derivIdeal k (tunedIdeal k J m (s + 1)) ≤ tunedIdeal k J m s := by
  rw [tunedIdeal_eq_iSup k J m (s + 1)]
  refine (derivIdeal_iSup_le k _).trans (iSup_le ?_)
  intro c
  refine (derivIdeal_iSup_le k _).trans (iSup_le ?_)
  intro hc
  rw [tuningMonomial_eq_prod]
  refine le_trans (le_of_eq (one_mul _).symm) ?_
  refine mul_derivIdeal_prod_le_consolidated39 J (tunedIdeal k J m s) c m 1 ?_ ?_
  · rw [one_mul]
    exact tuningMonomial_le_tunedIdeal k J m s c (by omega)
  · intro i hi d hne hdi
    rw [one_mul]
    exact derivIdealIterate_succ_mul_tuningMonomial_le_consolidated39 J m s i hi c d hne hdi hc

theorem derivIdealIterate_tunedIdeal_le (m s j : ℕ) :
    derivIdealIterate k j (tunedIdeal k J m s) ≤ tunedIdeal k J m (s - j) := by
  induction j with
  | zero =>
      simp only [derivIdealIterate_zero, Nat.sub_zero]
      exact le_rfl
  | succ j ih =>
      rw [derivIdealIterate_succ]
      refine le_trans (derivIdeal_mono k ih) ?_
      rcases Nat.eq_zero_or_pos (s - j) with h | h
      · have hsj : s - (j + 1) = 0 := by omega
        rw [hsj, tunedIdeal_zero]
        exact le_top
      · obtain ⟨t, ht⟩ : ∃ t, s - j = t + 1 := ⟨s - j - 1, by omega⟩
        have hsj : s - (j + 1) = t := by omega
        rw [ht, hsj]
        exact derivIdeal_tunedIdeal_succ_le k J m t

theorem derivIdealIterate_mul_derivIdeal_tunedIdeal_le (m s : ℕ) (hs : 1 ≤ s) :
    derivIdealIterate k (s - 1) (tunedIdeal k J m s) * derivIdeal k (tunedIdeal k J m s) ≤
      tunedIdeal k J m s := by
  have hss : s - (s - 1) = 1 := by omega
  have hsum : 1 + (s - 1) = s := by omega
  have h1 : derivIdealIterate k (s - 1) (tunedIdeal k J m s) ≤ tunedIdeal k J m 1 := by
    have h := derivIdealIterate_tunedIdeal_le k J m s (s - 1)
    rwa [hss] at h
  have h2 : derivIdeal k (tunedIdeal k J m s) ≤ tunedIdeal k J m (s - 1) := by
    have h := derivIdealIterate_tunedIdeal_le k J m s 1
    rwa [derivIdealIterate_one] at h
  refine le_trans (Ideal.mul_mono h1 h2) ?_
  have h3 := tunedIdeal_mul_le k J m 1 (s - 1)
  rwa [hsum] at h3


end

private theorem exists_ne_zero_of_one_le_tuningWeight_consolidated39 {m : ℕ} {c : ℕ → ℕ}
    (hc : 1 ≤ tuningWeight m c) : ∃ j ∈ Finset.range m, c j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hz : tuningWeight m c = 0 := by
    rw [tuningWeight_eq_sum]
    exact Finset.sum_eq_zero fun j hj => by rw [hcon j hj, Nat.mul_zero]
  rw [hz] at hc
  exact Nat.not_succ_le_zero 0 hc

theorem tunedIdeal_one_le_derivIdealIterate (J : Ideal S) (m : ℕ) (_hm : 1 ≤ m) :
    tunedIdeal k J m 1 ≤ derivIdealIterate k (m - 1) J := by
  rw [tunedIdeal_le_iff]
  intro c hc
  obtain ⟨j, hj, hcj⟩ := exists_ne_zero_of_one_le_tuningWeight_consolidated39 hc
  have hjm : j ≤ m - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hj)
  refine le_trans ?_ (derivIdealIterate_le_of_le k hjm J)
  have hsplit : derivIdealIterate k j J ^ c j *
      ∏ x ∈ (Finset.range m).erase j, derivIdealIterate k x J ^ c x =
      ∏ x ∈ Finset.range m, derivIdealIterate k x J ^ c x :=
    Finset.mul_prod_erase (Finset.range m) (fun x => derivIdealIterate k x J ^ c x) hj
  rw [tuningMonomial_eq_prod, ← hsplit]
  exact le_trans Ideal.mul_le_left (Ideal.pow_le_self hcj)

theorem mul_tunedIdeal_le_iff (I J : Ideal S) (m s : ℕ) (K : Ideal S) :
    I * tunedIdeal k J m s ≤ K ↔
      ∀ c : ℕ → ℕ, s ≤ tuningWeight m c → I * tuningMonomial k J m c ≤ K := by
  constructor
  · intro h c hc
    exact le_trans (Ideal.mul_mono le_rfl (tuningMonomial_le_tunedIdeal k J m s c hc)) h
  · intro h
    rw [tunedIdeal_eq_iSup, Submodule.mul_iSup]
    refine iSup_le fun c => ?_
    rw [Submodule.mul_iSup]
    exact iSup_le fun hc => h c hc

section
variable (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) {x : S} (hx : x ∈ derivIdealIterate k (m - 1) J)
include hm hx

theorem span_pow_mul_tuningMonomial_le (n : ℕ) (c : ℕ → ℕ) :
    Ideal.span {x ^ n} * tuningMonomial k J m c ≤ tunedIdeal k J m (tuningWeight m c + n) := by
  have hmem : (m - 1) ∈ Finset.range m := Finset.mem_range.mpr (by omega)
  have hspan : Ideal.span {x ^ n} ≤ tuningMonomial k J m (n • Pi.single (m - 1) 1) := by
    rw [← tuningMonomial_pow, tuningMonomial_single k J m (m - 1) hmem,
      Ideal.span_singleton_le_iff_mem]
    exact Ideal.pow_mem_pow hx n
  refine le_trans (Ideal.mul_mono hspan le_rfl) ?_
  rw [tuningMonomial_mul]
  refine tuningMonomial_le_tunedIdeal k J m _ _ ?_
  rw [tuningWeight_add, tuningWeight_nsmul, tuningWeight_single m (m - 1) hmem]
  have hmm : m - (m - 1) = 1 := by omega
  rw [hmm]
  omega

theorem span_pow_mul_tunedIdeal_le (n t : ℕ) :
    Ideal.span {x ^ n} * tunedIdeal k J m t ≤ tunedIdeal k J m (t + n) := by
  rw [mul_tunedIdeal_le_iff]
  intro c hc
  refine le_trans (span_pow_mul_tuningMonomial_le k J m hm hx n c) ?_
  exact tunedIdeal_antitone k J m (Nat.add_le_add_right hc n)


end

section

variable [Algebra ℚ S]

private theorem mem_of_natCast_add_one_mul_mem_consolidated39 {A : Type*} [CommRing A] [Algebra ℚ A] (n : ℕ)
    (I : Ideal A) (y : A) (h : ((n : A) + 1) * y ∈ I) : y ∈ I := by
  have hpos : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  have hq : ((n : ℚ) + 1) ≠ 0 := hpos.ne'
  have hmap : algebraMap ℚ A ((n : ℚ) + 1) = (n : A) + 1 := by
    rw [map_add, map_one, map_natCast]
  have h1 : algebraMap ℚ A ((n : ℚ) + 1)⁻¹ * (((n : A) + 1) * y) ∈ I :=
    Ideal.mul_mem_left I _ h
  rw [← hmap, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hq, map_one, one_mul] at h1
  exact h1

section
variable (R : Type*) [CommRing R] {A : Type*} [CommRing A] [Algebra R A]

private theorem pow_mul_mem_tunedIdeal_consolidated39 (J : Ideal A) (m : ℕ) (hm : 1 ≤ m) {x : A}
    (hx : x ∈ derivIdealIterate R (m - 1) J) (s n p : ℕ) {g : A}
    (hg : g ∈ derivIdealIterate R n (tunedIdeal R J m s)) :
    x ^ p * g ∈ tunedIdeal R J m ((s - n) + p) := by
  have hg' : g ∈ tunedIdeal R J m (s - n) := derivIdealIterate_tunedIdeal_le R J m s n hg
  exact span_pow_mul_tunedIdeal_le R J m hm hx p (s - n)
    (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self (x ^ p)) hg')

private theorem pow_mul_mem_derivIdeal_tunedIdeal_succ_consolidated39 [Algebra ℚ A] (J : Ideal A) (m : ℕ) (hm : 1 ≤ m) {x : A}
    (hx : x ∈ derivIdealIterate R (m - 1) J) (δ : Derivation R A A) (hδ : δ x = 1) (s : ℕ) :
    ∀ d n : ℕ, s + 1 ≤ n + d → ∀ g : A, g ∈ derivIdealIterate R n (tunedIdeal R J m s) →
      x ^ n * g ∈ derivIdeal R (tunedIdeal R J m (s + 1)) := by
  intro d
  induction d with
  | zero =>
      intro n hn g hg
      have h1 : x ^ n * g ∈ tunedIdeal R J m ((s - n) + n) :=
        pow_mul_mem_tunedIdeal_consolidated39 R J m hm hx s n n hg
      have h2 : s + 1 ≤ (s - n) + n := by omega
      exact le_derivIdeal R _ (tunedIdeal_antitone R J m h2 h1)
  | succ d ih =>
      intro n hn g hg
      have h1 : x ^ (n + 1) * g ∈ tunedIdeal R J m ((s - n) + (n + 1)) :=
        pow_mul_mem_tunedIdeal_consolidated39 R J m hm hx s n (n + 1) hg
      have h2 : s + 1 ≤ (s - n) + (n + 1) := by omega
      have h3 : x ^ (n + 1) * g ∈ tunedIdeal R J m (s + 1) :=
        tunedIdeal_antitone R J m h2 h1
      have h4 : δ (x ^ (n + 1) * g) ∈ derivIdeal R (tunedIdeal R J m (s + 1)) :=
        derivation_apply_mem_derivIdeal R (tunedIdeal R J m (s + 1)) δ h3
      have h5 : δ g ∈ derivIdealIterate R (n + 1) (tunedIdeal R J m s) := by
        rw [derivIdealIterate_succ]
        exact derivation_apply_mem_derivIdeal R (derivIdealIterate R n (tunedIdeal R J m s)) δ hg
      have h6 : x ^ (n + 1) * δ g ∈ derivIdeal R (tunedIdeal R J m (s + 1)) :=
        ih (n + 1) (by omega) (δ g) h5
      have hd1 : δ (x ^ (n + 1)) = ((n : A) + 1) * x ^ n := by
        have hpow := δ.leibniz_pow x (n + 1)
        rw [hδ] at hpow
        simpa using hpow
      have hkey : ((n : A) + 1) * (x ^ n * g)
          = δ (x ^ (n + 1) * g) - x ^ (n + 1) * δ g := by
        rw [Derivation.leibniz, hd1]
        simp only [smul_eq_mul]
        ring
      refine mem_of_natCast_add_one_mul_mem_consolidated39 n (derivIdeal R (tunedIdeal R J m (s + 1)))
        (x ^ n * g) ?_
      rw [hkey]
      exact Submodule.sub_mem _ h4 h6


end

theorem tunedIdeal_le_derivIdeal_tunedIdeal_succ (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) {x : S}
    (hx : x ∈ derivIdealIterate k (m - 1) J) (δ : Derivation k S S) (hδ : δ x = 1) (s : ℕ) :
    tunedIdeal k J m s ≤ derivIdeal k (tunedIdeal k J m (s + 1)) := by
  intro g hg
  have h := pow_mul_mem_derivIdeal_tunedIdeal_succ_consolidated39 k J m hm hx δ hδ s (s + 1) 0 (by omega) g
    (by rw [derivIdealIterate_zero]; exact hg)
  rwa [pow_zero, one_mul] at h

end

end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedIdealPowers
section

theorem tuningWeight_sub (m : ℕ) (c c' : ℕ → ℕ) (h : ∀ j, c' j ≤ c j) :
    tuningWeight m (fun j => c j - c' j) = tuningWeight m c - tuningWeight m c' := by
  have h2 : (fun j => (c j - c' j) + c' j) = c := funext fun j => Nat.sub_add_cancel (h j)
  have key : tuningWeight m (fun j => c j - c' j) + tuningWeight m c' = tuningWeight m c := by
    rw [← tuningWeight_fun_add m (fun j => c j - c' j) c', h2]
  omega

private theorem tuningWeight_ite_consolidated70 (m j q : ℕ) (hj : j ∈ Finset.range m) :
    tuningWeight m (fun i => if i = j then q else 0) = (m - j) * q := by
  simp only [tuningWeight_eq_sum]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hcon
    exact absurd hj hcon

theorem exists_le_tuningWeight_eq_mul (m L r : ℕ) (hL : 0 < L)
    (hdvd : ∀ w : ℕ, 1 ≤ w → w ≤ m → w ∣ L) (c : ℕ → ℕ)
    (hc : r * L + (m - 1) * L ≤ tuningWeight m c) :
    ∃ c' : ℕ → ℕ, (∀ j, c' j ≤ c j) ∧ tuningWeight m c' = r * L := by
  induction r generalizing c with
  | zero =>
      refine ⟨fun _ => 0, fun i => Nat.zero_le _, ?_⟩
      simp [tuningWeight_eq_sum]
  | succ r ih =>
      have hWpos : 0 < tuningWeight m c :=
        lt_of_lt_of_le (mul_pos (Nat.succ_pos r) hL) (le_trans (Nat.le_add_right _ _) hc)
      have hm : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0] at hWpos
          simp [tuningWeight_eq_sum] at hWpos
        · exact h0
      have hlt1 : ∀ a b : ℕ, a < b → a ≤ b - 1 := by
        intro a b h
        omega
      have hex : ∃ j ∈ Finset.range m, L ≤ (m - j) * c j := by
        by_contra hcon
        push Not at hcon
        have h1 : tuningWeight m c ≤ ∑ _x ∈ Finset.range m, (L - 1) := by
          rw [tuningWeight_eq_sum]
          refine Finset.sum_le_sum ?_
          intro i hi
          exact hlt1 _ _ (hcon i hi)
        have h2 : ∑ _x ∈ Finset.range m, (L - 1) = m * (L - 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        rw [h2] at h1
        have hA : m * (L - 1) + m = m * L := by
          have h' : L - 1 + 1 = L := Nat.sub_add_cancel hL
          calc m * (L - 1) + m = m * (L - 1 + 1) := by ring
            _ = m * L := by rw [h']
        have hB : (m - 1) * L + L = m * L := by
          have h' : m - 1 + 1 = m := Nat.sub_add_cancel hm
          calc (m - 1) * L + L = (m - 1 + 1) * L := by ring
            _ = m * L := by rw [h']
        have hC : L ≤ (r + 1) * L := by
          calc L = 1 * L := (one_mul L).symm
            _ ≤ (r + 1) * L := Nat.mul_le_mul (by omega) (le_refl L)
        have key : ∀ X Y Z W mm p : ℕ,
            X + Y ≤ Z → Z + mm = W → Y + p = W → p ≤ X → 1 ≤ mm → False := by
          intro X Y Z W mm p k1 k2 k3 k4 k5
          omega
        exact key ((r + 1) * L) ((m - 1) * L) (m * (L - 1)) (m * L) m L
          (le_trans hc h1) hA hB hC hm
      obtain ⟨j, hjmem, hjL⟩ := hex
      have hjm : j < m := Finset.mem_range.mp hjmem
      have hw0 : 0 < m - j := Nat.sub_pos_of_lt hjm
      have hw1 : 1 ≤ m - j := hw0
      obtain ⟨q, hq⟩ := hdvd (m - j) hw1 (Nat.sub_le m j)
      have hqc : q ≤ c j := by
        refine Nat.le_of_mul_le_mul_left ?_ hw0
        rw [← hq]
        exact hjL
      have hule : ∀ i, (if i = j then q else 0) ≤ c i := by
        intro i
        by_cases hij : i = j
        · rw [if_pos hij, hij]
          exact hqc
        · rw [if_neg hij]
          exact Nat.zero_le _
      have hu : tuningWeight m (fun i => if i = j then q else 0) = L := by
        rw [tuningWeight_ite_consolidated70 m j q hjmem]
        exact hq.symm
      have hd : tuningWeight m (fun i => c i - (if i = j then q else 0)) = tuningWeight m c - L := by
        have h := tuningWeight_sub m c (fun i => if i = j then q else 0) hule
        rw [hu] at h
        exact h
      have hc2 : r * L + L + (m - 1) * L ≤ tuningWeight m c := by
        calc r * L + L + (m - 1) * L = (r + 1) * L + (m - 1) * L := by ring
          _ ≤ tuningWeight m c := hc
      have hc' : r * L + (m - 1) * L
          ≤ tuningWeight m (fun i => c i - (if i = j then q else 0)) := by
        rw [hd]
        have h9 : ∀ A B C W : ℕ, A + C + B ≤ W → A + B ≤ W - C := by
          intro A B C W h
          omega
        exact h9 _ _ _ _ hc2
      obtain ⟨e, he1, he2⟩ := ih (fun i => c i - (if i = j then q else 0)) hc'
      refine ⟨fun i => e i + (if i = j then q else 0), ?_, ?_⟩
      · intro i
        have h1 : e i ≤ c i - (if i = j then q else 0) := he1 i
        have h2 : (if i = j then q else 0) ≤ c i := hule i
        show e i + (if i = j then q else 0) ≤ c i
        by_cases hij : i = j
        · rw [if_pos hij] at h1 h2 ⊢
          omega
        · rw [if_neg hij] at h1 h2 ⊢
          omega
      · have hsplit : tuningWeight m (fun i => e i + (if i = j then q else 0))
            = tuningWeight m e + tuningWeight m (fun i => if i = j then q else 0) :=
          tuningWeight_fun_add m e (fun i => if i = j then q else 0)
        rw [hsplit, he2, hu]
        ring

section

variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]

theorem tunedIdeal_pow_le (J : Ideal S) (m a n : ℕ) :
    tunedIdeal k J m a ^ n ≤ tunedIdeal k J m (n * a) := by
  induction n with
  | zero => simp [tunedIdeal_zero]
  | succ n ih =>
      calc tunedIdeal k J m a ^ (n + 1)
          = tunedIdeal k J m a ^ n * tunedIdeal k J m a := pow_succ _ _
        _ ≤ tunedIdeal k J m (n * a) * tunedIdeal k J m a := Ideal.mul_mono ih le_rfl
        _ ≤ tunedIdeal k J m (n * a + a) := tunedIdeal_mul_le k J m _ _
        _ = tunedIdeal k J m ((n + 1) * a) := by
            rw [(by ring : n * a + a = (n + 1) * a)]

section
variable (J : Ideal S) (m L : ℕ) (hL : 0 < L) (hdvd : ∀ w : ℕ, 1 ≤ w → w ≤ m → w ∣ L)
include hL hdvd

theorem tunedIdeal_mul_eq_tunedIdeal_add (r t : ℕ) (ht : (m - 1) * L ≤ t) :
    tunedIdeal k J m (r * L) * tunedIdeal k J m t = tunedIdeal k J m (r * L + t) := by
  refine le_antisymm (tunedIdeal_mul_le k J m _ _) ?_
  rw [tunedIdeal_le_iff]
  intro c hc
  have hc2 : r * L + (m - 1) * L ≤ tuningWeight m c :=
    le_trans (Nat.add_le_add_left ht (r * L)) hc
  obtain ⟨c', hc'le, hc'w⟩ := exists_le_tuningWeight_eq_mul m L r hL hdvd c hc2
  have h2 : (fun j => c' j + (c j - c' j)) = c := funext fun j => Nat.add_sub_cancel' (hc'le j)
  have hsplit : tuningMonomial k J m c' * tuningMonomial k J m (fun j => c j - c' j)
      = tuningMonomial k J m c := by
    rw [tuningMonomial_mul_fun_add k J m c' (fun j => c j - c' j), h2]
  rw [← hsplit]
  refine Ideal.mul_mono ?_ ?_
  · exact tuningMonomial_le_tunedIdeal k J m (r * L) c' (le_of_eq hc'w.symm)
  · refine tuningMonomial_le_tunedIdeal k J m t _ ?_
    rw [tuningWeight_sub m c c' hc'le, hc'w]
    have h9 : ∀ A B W : ℕ, A + B ≤ W → B ≤ W - A := by
      intro A B W h
      omega
    exact h9 (r * L) t (tuningWeight m c) hc

theorem tunedIdeal_pow_eq_tunedIdeal_mul (r : ℕ) (hr : m - 1 ≤ r) (j : ℕ) (hj : 1 ≤ j) :
    tunedIdeal k J m (r * L) ^ j = tunedIdeal k J m (j * (r * L)) := by
  induction j with
  | zero => exact absurd hj (by omega)
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp
      · have hn1 : 1 ≤ n := hn
        have ihn := ih hn1
        have hmt : (m - 1) * L ≤ n * (r * L) := by
          calc (m - 1) * L ≤ r * L := Nat.mul_le_mul hr (le_refl L)
            _ = 1 * (r * L) := (one_mul _).symm
            _ ≤ n * (r * L) := Nat.mul_le_mul hn1 (le_refl (r * L))
        calc tunedIdeal k J m (r * L) ^ (n + 1)
            = tunedIdeal k J m (r * L) ^ n * tunedIdeal k J m (r * L) := pow_succ _ _
          _ = tunedIdeal k J m (n * (r * L)) * tunedIdeal k J m (r * L) := by rw [ihn]
          _ = tunedIdeal k J m (r * L) * tunedIdeal k J m (n * (r * L)) := mul_comm _ _
          _ = tunedIdeal k J m (r * L + n * (r * L)) :=
              tunedIdeal_mul_eq_tunedIdeal_add k J m L hL hdvd r (n * (r * L)) hmt
          _ = tunedIdeal k J m ((n + 1) * (r * L)) := by
              rw [(by ring : r * L + n * (r * L) = (n + 1) * (r * L))]

theorem derivIdealIterate_tunedIdeal_pow_le (r : ℕ) (hr : m - 1 ≤ r) (i : ℕ) (hi : i < r * L) :
    derivIdealIterate k i (tunedIdeal k J m (r * L)) ^ (r * L) ≤
      tunedIdeal k J m (r * L) ^ (r * L - i) := by
  have hi' : 1 ≤ r * L - i := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hi)
  calc derivIdealIterate k i (tunedIdeal k J m (r * L)) ^ (r * L)
      ≤ tunedIdeal k J m (r * L - i) ^ (r * L) :=
        Ideal.pow_right_mono (derivIdealIterate_tunedIdeal_le k J m (r * L) i) (r * L)
    _ ≤ tunedIdeal k J m (r * L * (r * L - i)) := tunedIdeal_pow_le k J m (r * L - i) (r * L)
    _ = tunedIdeal k J m ((r * L - i) * (r * L)) := by
        rw [Nat.mul_comm (r * L) (r * L - i)]
    _ = tunedIdeal k J m (r * L) ^ (r * L - i) :=
        (tunedIdeal_pow_eq_tunedIdeal_mul k J m L hL hdvd r hr (r * L - i) hi').symm


end

end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
section

open AlgebraicGeometry CategoryTheory TopologicalSpace


variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]

def IsDerivBalanced (I : X.IdealSheafData) (m : ℕ) : Prop :=
  ∀ i < m, derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i)

theorem isDerivBalanced_iff (I : X.IdealSheafData) (m : ℕ) :
    IsDerivBalanced k p I m ↔ ∀ i < m, derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i) :=
  Iff.rfl

section
variable {I : X.IdealSheafData} {m : ℕ}

theorem IsDerivBalanced.derivIdealSheafIterate_pow_le (h : IsDerivBalanced k p I m)
    {i : ℕ} (hi : i < m) : derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i) :=
  h i hi

theorem isDerivBalanced_of_pow_le (h : ∀ i < m, derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i)) : IsDerivBalanced k p I m :=
  h


end

theorem isDerivBalanced_one (I : X.IdealSheafData) : IsDerivBalanced k p I 1 := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  have h : derivIdealSheafIterate k p 0 I = I := derivIdealSheafIterate_zero k p I
  exact le_of_eq (by rw [h, Nat.sub_zero])

noncomputable def maxContactIdeal (I : X.IdealSheafData) (m : ℕ) : X.IdealSheafData :=
  derivIdealSheafIterate k p (m - 1) I

section
variable (I : X.IdealSheafData)

@[simp] theorem maxContactIdeal_eq_derivIdealSheafIterate (m : ℕ) :
    maxContactIdeal k p I m = derivIdealSheafIterate k p (m - 1) I :=
  rfl

theorem maxContactIdeal_one : maxContactIdeal k p I 1 = I :=
  rfl

theorem maxContactIdeal_ideal (m : ℕ) (U : X.affineOpens) :
    (maxContactIdeal k p I m).ideal U =
      @derivIdealIterate k _ _ _ (sectionsAlgebra k p U.1) (m - 1) (I.ideal U) :=
  derivIdealSheafIterate_ideal k p (m - 1) I U


end

def IsMaxContactInvariant (I : X.IdealSheafData) (m : ℕ) : Prop :=
  maxContactIdeal k p I m * derivIdealSheaf k p I ≤ I

theorem isMaxContactInvariant_of_mul_le {I : X.IdealSheafData} {m : ℕ}
    (h : maxContactIdeal k p I m * derivIdealSheaf k p I ≤ I) : IsMaxContactInvariant k p I m :=
  h

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivBalancedOrderLocus
section

open AlgebraicGeometry CategoryTheory TopologicalSpace


variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
  (I : X.IdealSheafData) (m : ℕ)

section
variable (h : IsDerivBalanced k p I m)
include h

theorem orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced
    (x : X) :
    orderAt I x = 0 ∨ (m : ℕ∞) ≤ orderAt I x := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · right
    simp
  have hm1 : 1 ≤ m := hpos
  by_cases h0 : orderAt I x = 0
  · exact Or.inl h0
  right
  have hlt : m - 1 < m := by omega
  have hle : derivIdealSheafIterate k p (m - 1) I ^ m ≤ I ^ (m - (m - 1)) :=
    IsDerivBalanced.derivIdealSheafIterate_pow_le k p h hlt
  have hsub : m - (m - 1) = 1 := by omega
  rw [hsub, pow_one] at hle
  have hord : orderAt I x ≤ orderAt (derivIdealSheafIterate k p (m - 1) I ^ m) x :=
    orderAt_le_of_le hle x
  rw [orderAt_pow k p (derivIdealSheafIterate k p (m - 1) I) m x] at hord
  have hne : orderAt (derivIdealSheafIterate k p (m - 1) I) x ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hord
    exact h0 (le_antisymm hord (by exact zero_le))
  have hmem : x ∈ (derivIdealSheafIterate k p (m - 1) I).support := by
    by_contra hc
    exact hne ((orderAt_eq_zero_iff_not_mem_support _ x).mpr hc)
  have heq := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm1
  have hx : x ∈ orderAtLeastLocus I m := by
    rw [← heq]
    exact hmem
  exact (mem_orderAtLeastLocus_iff I m x).mp hx

theorem orderAtLeastLocus_eq_support_of_isDerivBalanced
    (hm : 1 ≤ m) :
    orderAtLeastLocus I m = (I.support : Set X) := by
  ext x
  rw [mem_orderAtLeastLocus_iff]
  constructor
  · intro hx
    have h1 : (1 : ℕ∞) ≤ orderAt I x := le_trans (by exact_mod_cast hm) hx
    exact (one_le_orderAt_iff_mem_support I x).mp h1
  · intro hx
    have hx' : x ∈ I.support := hx
    have hne : orderAt I x ≠ 0 := fun h0 =>
      (orderAt_eq_zero_iff_not_mem_support I x).mp h0 hx'
    rcases orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced k p I m h x with h0 | h0
    · exact absurd h0 hne
    · exact h0


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.StalkIdealSpreadOut
section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

section

section
variable {R S : Type u} [CommRing R] [CommRing S]

private theorem exists_mem_mul_mem_of_map_le_consolidated134 [Algebra R S] (M : Submonoid R) (hM : IsLocalization M S) (A B : Ideal R)
    (hA : Submodule.FG A)
    (hAB : Ideal.map (algebraMap R S) A ≤ Ideal.map (algebraMap R S) B) :
    ∃ u : R, u ∈ M ∧ ∀ a ∈ A, u * a ∈ B := by
  classical
  have := hM
  obtain ⟨G, hG⟩ := hA
  have key : ∀ a : R, ∃ u : R, u ∈ M ∧ (a ∈ A → u * a ∈ B) := by
    intro a
    by_cases ha : a ∈ A
    · have h1 : algebraMap R S a ∈ Ideal.map (algebraMap R S) B :=
        hAB (Ideal.mem_map_of_mem _ ha)
      rw [IsLocalization.mem_map_algebraMap_iff (M := M) (S := S)] at h1
      obtain ⟨⟨b, s⟩, hEq⟩ := h1
      rw [← map_mul] at hEq
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (M := M) (S := S)).mp hEq
      refine ⟨(c : R) * (s : R), M.mul_mem c.2 s.2, fun _ => ?_⟩
      have hcalc : (c : R) * (s : R) * a = (c : R) * (b : R) := by linear_combination hc
      rw [hcalc]
      exact Ideal.mul_mem_left B _ b.2
    · exact ⟨1, M.one_mem, fun hmem => absurd hmem ha⟩
  choose u huM huB using key
  refine ⟨∏ g ∈ G, u g, (Submonoid.prod_mem M fun g _ => huM g), ?_⟩
  intro a ha
  rw [← hG] at ha
  induction ha using Submodule.span_induction with
  | mem z hz =>
      have hzG : z ∈ G := Finset.mem_coe.mp hz
      have hzA : z ∈ A := by rw [← hG]; exact Submodule.subset_span hz
      rw [← Finset.mul_prod_erase G u hzG]
      have hre : u z * (∏ g ∈ G.erase z, u g) * z
          = (∏ g ∈ G.erase z, u g) * (u z * z) := by ring
      rw [hre]
      exact Ideal.mul_mem_left B _ (huB z hzA)
  | zero => rw [mul_zero]; exact B.zero_mem
  | add y z _ _ hy hz => rw [mul_add]; exact B.add_mem hy hz
  | smul c y _ hy =>
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left B c hy

private theorem map_le_map_of_isUnit_mul_mem_consolidated134 (φ : R →+* S) (w : R) (hw : IsUnit (φ w)) (A B : Ideal R)
    (hAB : ∀ a ∈ A, w * a ∈ B) :
    Ideal.map φ A ≤ Ideal.map φ B := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  obtain ⟨t, ht⟩ := hw.exists_right_inv
  have h1 : φ (w * a) ∈ Ideal.map φ B := Ideal.mem_map_of_mem φ (hAB a ha)
  have h4 : t * φ (w * a) ∈ Ideal.map φ B := Ideal.mul_mem_left _ _ h1
  rw [map_mul, ← mul_assoc, mul_comm t (φ w), ht, one_mul] at h4
  exact Ideal.mem_comap.mpr h4


end

theorem exists_opens_stalkIdeal_eq {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (x : X) (h : stalkIdeal I x = stalkIdeal J x) :
    ∃ W : X.Opens, x ∈ W ∧ ∀ y : X, y ∈ W → stalkIdeal I y = stalkIdeal J y := by
  obtain ⟨U, hxU, hU⟩ := Scheme.exists_isAffineOpen_mem x
  have hUaff : IsAffineOpen U := hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let instAlg : Algebra Γ(X, U) ↑(X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  have halg : (algebraMap Γ(X, U) ↑(X.presheaf.stalk x)) = (X.presheaf.germ U x hxU).hom := rfl
  have hloc : IsLocalization (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      ↑(X.presheaf.stalk x) := hUaff.isLocalization_stalk ⟨x, hxU⟩
  have hmapeq : Ideal.map (algebraMap Γ(X, U) ↑(X.presheaf.stalk x)) (I.ideal ⟨U, hU⟩)
      = Ideal.map (algebraMap Γ(X, U) ↑(X.presheaf.stalk x)) (J.ideal ⟨U, hU⟩) := by
    have h1 := stalkIdeal_eq_map_germ I x ⟨U, hU⟩ hxU
    have h2 := stalkIdeal_eq_map_germ J x ⟨U, hU⟩ hxU
    rw [h1, h2] at h
    rw [halg]
    exact h
  obtain ⟨u₁, hu₁M, hu₁⟩ := exists_mem_mul_mem_of_map_le_consolidated134 _ hloc (I.ideal ⟨U, hU⟩)
    (J.ideal ⟨U, hU⟩) (IsNoetherian.noetherian _) (le_of_eq hmapeq)
  obtain ⟨u₂, hu₂M, hu₂⟩ := exists_mem_mul_mem_of_map_le_consolidated134 _ hloc (J.ideal ⟨U, hU⟩)
    (I.ideal ⟨U, hU⟩) (IsNoetherian.noetherian _) (le_of_eq hmapeq.symm)
  have hmb : ∀ (z : ↥X) (hz : z ∈ U),
      z ∈ X.basicOpen (u₁ * u₂) ↔ IsUnit ((X.presheaf.germ U z hz).hom (u₁ * u₂)) := by
    intro z hz
    exact X.mem_basicOpen (u₁ * u₂) z hz
  have hxunit : IsUnit ((X.presheaf.germ U x hxU).hom (u₁ * u₂)) := by
    have hmem : u₁ * u₂ ∈ (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl :=
      Submonoid.mul_mem _ hu₁M hu₂M
    have hone := IsLocalization.map_units
      (M := (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl)
      (S := ↑(X.presheaf.stalk x)) ⟨u₁ * u₂, hmem⟩
    rw [halg] at hone
    exact hone
  refine ⟨X.basicOpen (u₁ * u₂), (hmb x hxU).mpr hxunit, ?_⟩
  intro y hy
  have hyU : y ∈ U := X.basicOpen_le (u₁ * u₂) hy
  have hyunit : IsUnit ((X.presheaf.germ U y hyU).hom (u₁ * u₂)) := (hmb y hyU).mp hy
  have hv1 : ∀ a ∈ I.ideal ⟨U, hU⟩, u₁ * u₂ * a ∈ J.ideal ⟨U, hU⟩ := by
    intro a ha
    have he : u₁ * u₂ * a = u₂ * (u₁ * a) := by ring
    rw [he]
    exact Ideal.mul_mem_left _ _ (hu₁ a ha)
  have hv2 : ∀ a ∈ J.ideal ⟨U, hU⟩, u₁ * u₂ * a ∈ I.ideal ⟨U, hU⟩ := by
    intro a ha
    have he : u₁ * u₂ * a = u₁ * (u₂ * a) := by ring
    rw [he]
    exact Ideal.mul_mem_left _ _ (hu₂ a ha)
  rw [stalkIdeal_eq_map_germ I y ⟨U, hU⟩ hyU, stalkIdeal_eq_map_germ J y ⟨U, hU⟩ hyU]
  exact le_antisymm
    (map_le_map_of_isUnit_mul_mem_consolidated134 (X.presheaf.germ U y hyU).hom (u₁ * u₂) hyunit _ _ hv1)
    (map_le_map_of_isUnit_mul_mem_consolidated134 (X.presheaf.germ U y hyU).hom (u₁ * u₂) hyunit _ _ hv2)

section
variable {R : Type*} [CommRing R]

private theorem notMem_of_mem_primeCompl_consolidated134 {m : Ideal R} [m.IsPrime]
    {x : R} (hx : x ∈ m.primeCompl) : x ∉ m := hx

private theorem exists_notMem_mul_mem_of_map_le_consolidated134 (S : Type*) [CommRing S]
    [Algebra R S] (m : Ideal R) [hmp : m.IsPrime] [IsLocalization m.primeCompl S]
    {A B : Ideal R} (hAB : Ideal.map (algebraMap R S) A ≤ Ideal.map (algebraMap R S) B)
    {a : R} (ha : a ∈ A) : ∃ t : R, t ∉ m ∧ t * a ∈ B := by
  have hmem : algebraMap R S a ∈ Ideal.map (algebraMap R S) B :=
    hAB (Ideal.mem_map_of_mem _ ha)
  obtain ⟨⟨b, s⟩, hbs⟩ := (IsLocalization.mem_map_algebraMap_iff m.primeCompl S).mp hmem
  have hbs' : algebraMap R S (a * (s : R)) = algebraMap R S (b : R) := by
    rw [map_mul]
    exact hbs
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists m.primeCompl S).mp hbs'
  have hc2 : (c : R) ∉ m := notMem_of_mem_primeCompl_consolidated134 c.2
  have hs2 : (s : R) ∉ m := notMem_of_mem_primeCompl_consolidated134 s.2
  refine ⟨(c : R) * (s : R), ?_, ?_⟩
  · intro hcs
    rcases hmp.mem_or_mem hcs with h1 | h1
    · exact hc2 h1
    · exact hs2 h1
  · have hEq : ((c : R) * (s : R)) * a = (c : R) * (b : R) := by
      rw [← hc]
      ring
    rw [hEq]
    exact Ideal.mul_mem_left _ _ b.2

private theorem le_of_forall_isMaximal_exists_mul_mem_consolidated134 {A B : Ideal R}
    (h : ∀ m : Ideal R, m.IsMaximal → ∀ a ∈ A, ∃ t : R, t ∉ m ∧ t * a ∈ B) : A ≤ B := by
  intro a ha
  by_contra hab
  obtain ⟨C, hCmem⟩ : ∃ C : Ideal R, ∀ r : R, r ∈ C ↔ r * a ∈ B := by
    refine ⟨{ carrier := {r : R | r * a ∈ B}
              add_mem' := ?_
              zero_mem' := ?_
              smul_mem' := ?_ }, fun r => Iff.rfl⟩
    · intro x y hx hy
      show (x + y) * a ∈ B
      rw [add_mul]
      exact B.add_mem hx hy
    · show (0 : R) * a ∈ B
      rw [zero_mul]
      exact B.zero_mem
    · intro c x hx
      show (c • x) * a ∈ B
      rw [smul_eq_mul, mul_assoc]
      exact Ideal.mul_mem_left _ _ hx
  have hCne : C ≠ ⊤ := by
    intro hCtop
    have h1 : (1 : R) ∈ C := by
      rw [hCtop]
      exact Submodule.mem_top
    have h2 := (hCmem 1).mp h1
    rw [one_mul] at h2
    exact hab h2
  obtain ⟨m, hm, hCm⟩ := Ideal.exists_le_maximal C hCne
  obtain ⟨t, htm, htB⟩ := h m hm a ha
  exact htm (hCm ((hCmem t).mpr htB))


end

section
variable {Y : Scheme.{u}} (A B : Y.IdealSheafData) (W : Y.affineOpens)

private theorem ideal_le_of_stalkIdeal_le_consolidated134 (h : ∀ x : ↥Y, x ∈ W.1 → stalkIdeal A x ≤ stalkIdeal B x) :
    A.ideal W ≤ B.ideal W := by
  refine le_of_forall_isMaximal_exists_mul_mem_consolidated134 ?_
  intro m hm a ha
  have hmp : m.IsPrime := hm.isPrime
  set y : PrimeSpectrum Γ(Y, W.1) := ⟨m, hmp⟩ with hydef
  set x : ↥Y := W.2.fromSpec.base y with hxdef
  have hy : x ∈ W.1 := by
    have hmem : x ∈ Set.range (W.2.fromSpec.base) := ⟨y, rfl⟩
    rw [W.2.range_fromSpec] at hmem
    exact hmem
  let algI : Algebra Γ(Y, W.1) ↑(Y.presheaf.stalk x) :=
    (Y.presheaf.germ W.1 x hy).hom.toAlgebra
  have hloc : IsLocalization m.primeCompl ↑(Y.presheaf.stalk x) :=
    W.2.isLocalization_stalk' y hy
  refine exists_notMem_mul_mem_of_map_le_consolidated134 (↑(Y.presheaf.stalk x)) m ?_ ha
  have halg : (algebraMap Γ(Y, W.1) ↑(Y.presheaf.stalk x))
      = (Y.presheaf.germ W.1 x hy).hom := rfl
  rw [halg, ← stalkIdeal_eq_map_germ A x W hy, ← stalkIdeal_eq_map_germ B x W hy]
  exact h x hy

private theorem ideal_eq_of_stalkIdeal_eq_consolidated134 (h : ∀ x : ↥Y, x ∈ W.1 → stalkIdeal A x = stalkIdeal B x) :
    A.ideal W = B.ideal W :=
  le_antisymm (ideal_le_of_stalkIdeal_le_consolidated134 A B W fun x hx => le_of_eq (h x hx))
    (ideal_le_of_stalkIdeal_le_consolidated134 B A W fun x hx => le_of_eq (h x hx).symm)


end

theorem restrictIdeal_eq_of_stalkIdeal_eq {X : Scheme.{u}} (I J : X.IdealSheafData) (U : X.Opens)
    (h : ∀ y : X, y ∈ U → stalkIdeal I y = stalkIdeal J y) :
    restrictIdeal I U = restrictIdeal J U := by
  have key : ∀ V : U.toScheme.affineOpens,
      (restrictIdeal I U).ideal V = (restrictIdeal J U).ideal V := by
    intro V
    have hWaff : IsAffineOpen (U.ι ''ᵁ V.1) := V.2.image_of_isOpenImmersion U.ι
    have hWU : (U.ι ''ᵁ V.1) ≤ U := by
      intro z hz
      have hz' : z ∈ (fun w => U.ι.base w) '' (↑V.1 : Set U.toScheme) := hz
      obtain ⟨v, -, rfl⟩ := hz'
      exact v.2
    have e : V.1 ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V.1) := by
      intro v hv
      have h2 : U.ι.base v ∈ (fun w => U.ι.base w) '' (↑V.1 : Set U.toScheme) := ⟨v, hv, rfl⟩
      exact h2
    have hIJ : I.ideal ⟨U.ι ''ᵁ V.1, hWaff⟩ = J.ideal ⟨U.ι ''ᵁ V.1, hWaff⟩ := by
      refine ideal_eq_of_stalkIdeal_eq_consolidated134 I J ⟨U.ι ''ᵁ V.1, hWaff⟩ ?_
      intro z hz
      exact h z (hWU hz)
    show (I.comap U.ι).ideal V = (J.comap U.ι).ideal V
    rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I U.ι ⟨U.ι ''ᵁ V.1, hWaff⟩ V e,
      Scheme.IdealSheafData.comap_ideal_eq_map_appLE J U.ι ⟨U.ι ''ᵁ V.1, hWaff⟩ V e, hIJ]
  have h1 : ∀ V : U.toScheme.affineOpens,
      (restrictIdeal I U).ideal V ≤ (restrictIdeal J U).ideal V := fun V => le_of_eq (key V)
  have h2 : ∀ V : U.toScheme.affineOpens,
      (restrictIdeal J U).ideal V ≤ (restrictIdeal I U).ideal V := fun V => le_of_eq (key V).symm
  exact le_antisymm h1 h2

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
section

open CategoryTheory AlgebraicGeometry Opposite

section

section
variable (k : Type u) [Field k] (m : ℕ)

theorem coordSubspaceIdeal_empty :
    coordSubspaceIdeal k m (∅ : Finset (Fin m)) = ⊥ := by
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord]
  simp only [Finset.coe_empty, Set.image_empty, Ideal.span_empty]
  ext U
  simp [Ideal.map_bot]

theorem coordSubspaceIdeal_singleton (j : Fin m) :
    coordSubspaceIdeal k m {j} =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)}) := by
  have h : ((fun i : Fin m => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
      (({j} : Finset (Fin m)) : Set (Fin m))) =
      {AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)} := by
    rw [Finset.coe_singleton, Set.image_singleton]
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, h]


end

def coordBlowupSubstMap (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) :
    affineSpaceFin k m ⟶ affineSpaceFin k m :=
  AffineSpace.homOfVector (affineSpaceFinToSpec k m)
    (fun i : ULift.{u} (Fin m) =>
      if i.down ∈ S ∧ i.down ≠ s then
        AffineSpace.coord (Spec (CommRingCat.of k)) i *
          AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s)
      else AffineSpace.coord (Spec (CommRingCat.of k)) i)

@[simp]
theorem coordBlowupSubstMap_comp_affineSpaceFinToSpec (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) :
    coordBlowupSubstMap k m S s ≫ affineSpaceFinToSpec k m = affineSpaceFinToSpec k m := by
  apply AffineSpace.homOfVector_over

@[simp]
theorem coordBlowupSubstMap_appTop_coord (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m)
    (i : ULift.{u} (Fin m)) :
    (coordBlowupSubstMap k m S s).appTop.hom (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
      if i.down ∈ S ∧ i.down ≠ s then
        AffineSpace.coord (Spec (CommRingCat.of k)) i *
          AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s)
      else AffineSpace.coord (Spec (CommRingCat.of k)) i := by
  exact AffineSpace.homOfVector_appTop_coord ..

section
variable (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m)

theorem coordBlowupSubstMap_appTop_coord_of_mem (j : Fin m) (hj : j ∈ S) (hjs : j ≠ s) :
    (coordBlowupSubstMap k m S s).appTop.hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) =
      AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j) *
        AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s) := by
  have hc : (ULift.up j : ULift.{u} (Fin m)).down ∈ S ∧
      (ULift.up j : ULift.{u} (Fin m)).down ≠ s := ⟨hj, hjs⟩
  rw [coordBlowupSubstMap_appTop_coord k m S s (ULift.up j : ULift.{u} (Fin m)), if_pos hc]

theorem coordBlowupSubstMap_appTop_coord_self :
    (coordBlowupSubstMap k m S s).appTop.hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s)) =
      AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s) := by
  have hc : ¬ ((ULift.up s : ULift.{u} (Fin m)).down ∈ S ∧
      (ULift.up s : ULift.{u} (Fin m)).down ≠ s) := by
    rintro ⟨-, h⟩
    exact h rfl
  rw [coordBlowupSubstMap_appTop_coord k m S s (ULift.up s : ULift.{u} (Fin m)), if_neg hc]

theorem coordBlowupSubstMap_appTop_coord_of_notMem (j : Fin m) (hj : j ∉ S) :
    (coordBlowupSubstMap k m S s).appTop.hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) =
      AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j) := by
  have hc : ¬ ((ULift.up j : ULift.{u} (Fin m)).down ∈ S ∧
      (ULift.up j : ULift.{u} (Fin m)).down ≠ s) := fun h => hj h.1
  rw [coordBlowupSubstMap_appTop_coord k m S s (ULift.up j : ULift.{u} (Fin m)), if_neg hc]

theorem comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_of_mem (j : Fin m) (hj : j ∈ S) (hjs : j ≠ s) :
    (coordSubspaceIdeal k m {j}).comap (coordBlowupSubstMap k m S s) =
      coordSubspaceIdeal k m {j} * coordSubspaceIdeal k m {s} := by
  rw [coordSubspaceIdeal_singleton, coordSubspaceIdeal_singleton,
    Scheme.IdealSheafData.comap_ofIdealTop,
    ← Scheme.IdealSheafData.ofIdealTop_mul, Ideal.map_span, Set.image_singleton,
    coordBlowupSubstMap_appTop_coord_of_mem k m S s j hj hjs,
    Ideal.span_singleton_mul_span_singleton]

theorem comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_self :
    (coordSubspaceIdeal k m {s}).comap (coordBlowupSubstMap k m S s) = coordSubspaceIdeal k m {s} := by
  rw [coordSubspaceIdeal_singleton, Scheme.IdealSheafData.comap_ofIdealTop,
    Ideal.map_span, Set.image_singleton, coordBlowupSubstMap_appTop_coord_self k m S s]

theorem comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_of_notMem (j : Fin m) (hj : j ∉ S) :
    (coordSubspaceIdeal k m {j}).comap (coordBlowupSubstMap k m S s) = coordSubspaceIdeal k m {j} := by
  rw [coordSubspaceIdeal_singleton, Scheme.IdealSheafData.comap_ofIdealTop,
    Ideal.map_span, Set.image_singleton, coordBlowupSubstMap_appTop_coord_of_notMem k m S s j hj]

theorem comap_coordBlowupSubstMap_coordSubspaceIdeal_center (hs : s ∈ S) :
    (coordSubspaceIdeal k m S).comap (coordBlowupSubstMap k m S s) = coordSubspaceIdeal k m {s} := by
  have key : Ideal.map ((coordBlowupSubstMap k m S s).appTop.hom)
      (Ideal.span
        ((fun i : Fin m => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
          (S : Set (Fin m)))) =
      Ideal.span {AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s)} := by
    rw [Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro y ⟨z, ⟨i, hi, rfl⟩, rfl⟩
      have hiS : i ∈ S := Finset.mem_coe.mp hi
      show (coordBlowupSubstMap k m S s).appTop.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ∈
          Ideal.span {AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s)}
      by_cases h : i = s
      · have h2 : (coordBlowupSubstMap k m S s).appTop.hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) =
            AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s) := by
          rw [h]
          exact coordBlowupSubstMap_appTop_coord_self k m S s
        rw [h2]
        exact Ideal.mem_span_singleton_self _
      · rw [coordBlowupSubstMap_appTop_coord_of_mem k m S s i hiS h]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have hmem : (coordBlowupSubstMap k m S s).appTop.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s)) ∈
          ((coordBlowupSubstMap k m S s).appTop.hom ''
            ((fun i : Fin m => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
              (S : Set (Fin m)))) :=
        Set.mem_image_of_mem _ (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hs))
      rw [coordBlowupSubstMap_appTop_coord_self k m S s] at hmem
      exact Ideal.subset_span hmem
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, Scheme.IdealSheafData.comap_ofIdealTop, key,
    coordSubspaceIdeal_singleton]


end

section
variable {X X₁ : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} {p₁ : X₁ ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {V : X₁.Opens} {m : ℕ} {S : Finset (Fin m)} {s : Fin m} (c : EtaleChart p U m) (c₁ : EtaleChart p₁ V m) (g : V.toScheme ⟶ U.toScheme) (hg : c₁.map ≫ coordBlowupSubstMap k m S s = g ≫ c.map)
include hg

theorem comap_coordIdeal_of_coordBlowupSubstMap (T : Finset (Fin m)) :
    (c.coordIdeal T).comap g =
      ((coordSubspaceIdeal k m T).comap (coordBlowupSubstMap k m S s)).comap c₁.map := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, ← Scheme.IdealSheafData.comap_comp, ← hg,
    Scheme.IdealSheafData.comap_comp]

theorem comap_coordIdeal_singleton_of_mem (j : Fin m) (hj : j ∈ S) (hjs : j ≠ s) :
    (c.coordIdeal {j}).comap g = c₁.coordIdeal {j} * c₁.coordIdeal {s} := by
  rw [comap_coordIdeal_of_coordBlowupSubstMap c c₁ g hg {j},
    comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_of_mem k m S s j hj hjs,
    Scheme.IdealSheafData.comap_mul]
  rfl

theorem comap_coordIdeal_singleton_self :
    (c.coordIdeal {s}).comap g = c₁.coordIdeal {s} := by
  rw [comap_coordIdeal_of_coordBlowupSubstMap c c₁ g hg {s},
    comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_self k m S s]
  rfl

theorem comap_coordIdeal_singleton_of_notMem (j : Fin m) (hj : j ∉ S) :
    (c.coordIdeal {j}).comap g = c₁.coordIdeal {j} := by
  rw [comap_coordIdeal_of_coordBlowupSubstMap c c₁ g hg {j},
    comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_of_notMem k m S s j hj]
  rfl

theorem comap_coordIdeal_center (hs : s ∈ S) :
    (c.coordIdeal S).comap g = c₁.coordIdeal {s} := by
  rw [comap_coordIdeal_of_coordBlowupSubstMap c c₁ g hg S,
    comap_coordBlowupSubstMap_coordSubspaceIdeal_center k m S s hs]
  rfl


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
section

open CategoryTheory AlgebraicGeometry Opposite

section

variable {Y : Scheme.{u}}

section
variable {Y' : Scheme.{u}}

private theorem mul_ideal_apply_consolidated111 (F G : Y'.IdealSheafData)
    (U : Y'.affineOpens) : (F * G).ideal U = F.ideal U * G.ideal U := rfl

private theorem pow_ideal_apply_consolidated111 (F : Y'.IdealSheafData) (n : ℕ)
    (U : Y'.affineOpens) : (F ^ n).ideal U = F.ideal U ^ n := by
  induction n with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_succ, mul_ideal_apply_consolidated111, ih]


end

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.pow {F : Y.IdealSheafData} (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F) (n : ℕ) :
    FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor (F ^ n) := by
  unfold FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor at hF ⊢
  intro x
  obtain ⟨U, f, hxU, hf, hFU⟩ := hF x
  refine ⟨U, f ^ n, hxU, pow_mem hf n, ?_⟩
  rw [EmbeddedResolution.pow_ideal_apply_consolidated111, hFU, Ideal.span_singleton_pow]

section
variable {Y : Scheme.{u}}

private theorem le_of_forall_ideal_le_consolidated111 {I J : Y.IdealSheafData}
    (H : ∀ U : Y.affineOpens, I.ideal U ≤ J.ideal U) : I ≤ J := H

private theorem mul_ideal_le_mul_ideal_consolidated111 {F J J' : Y.IdealSheafData}
    (h : F * J ≤ F * J') (W : Y.affineOpens) :
    F.ideal W * J.ideal W ≤ F.ideal W * J'.ideal W := h W

private theorem exists_affineOpen_ideal_eq_span_singleton_consolidated111 {F : Y.IdealSheafData}
    (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F) (x : Y) :
    ∃ (W : Y.affineOpens) (t : Γ(Y, (W : Y.Opens))), x ∈ (W : Y.Opens) ∧
      t ∈ nonZeroDivisors Γ(Y, (W : Y.Opens)) ∧ F.ideal W = Ideal.span {t} := by
  unfold Blowup.IsLocallyGeneratedByNonZeroDivisor at hF
  exact hF x


end

private theorem exists_pow_mul_mem_of_algebraMap_mem_map_consolidated111 {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (r : R) [IsLocalization.Away r S] (I : Ideal R) (x : R)
    (hx : algebraMap R S x ∈ Ideal.map (algebraMap R S) I) : ∃ n : ℕ, r ^ n * x ∈ I := by
  rw [IsLocalization.mem_map_algebraMap_iff (M := Submonoid.powers r) (S := S)] at hx
  obtain ⟨w, hy⟩ := hx
  rw [← map_mul] at hy
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (M := Submonoid.powers r) (S := S)).mp hy
  obtain ⟨p, hp⟩ : ∃ p : ℕ, r ^ p = (c : R) := c.2
  obtain ⟨q, hq⟩ : ∃ q : ℕ, r ^ q = (w.2 : R) := w.2.2
  refine ⟨p + q, ?_⟩
  have h2 : r ^ (p + q) * x = (c : R) * (w.1 : R) := by
    rw [pow_add, hp, hq, ← hc]; ring
  rw [h2]
  exact I.mul_mem_left _ w.1.2

section
variable {Y : Scheme.{u}}

private theorem ideal_le_ideal_of_mul_le_mul_consolidated111 {F J J' : Y.IdealSheafData}
    (h : F * J ≤ F * J') (W : Y.affineOpens) (t : Γ(Y, (W : Y.Opens)))
    (hFW : F.ideal W = Ideal.span {t}) (ht : t ∈ nonZeroDivisors Γ(Y, (W : Y.Opens))) :
    J.ideal W ≤ J'.ideal W := by
  intro b hb
  have h1 : t * b ∈ F.ideal W * J.ideal W := by
    rw [hFW]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self t) hb
  have h2 : t * b ∈ F.ideal W * J'.ideal W := mul_ideal_le_mul_ideal_consolidated111 h W h1
  rw [hFW, Ideal.mem_span_singleton_mul] at h2
  obtain ⟨j, hj, hje⟩ := h2
  have h3 : (b - j) * t = 0 := by
    rw [sub_mul, mul_comm b t, mul_comm j t, hje, sub_self]
  have h4 : b = j := eq_of_sub_eq_zero ((mem_nonZeroDivisors_iff.mp ht).2 (b - j) h3)
  rw [h4]
  exact hj

private theorem span_eq_top_of_forall_exists_mem_basicOpen_consolidated111 {U : Y.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(Y, U))
    (h : ∀ x : Y, x ∈ U → ∃ f : s, x ∈ Y.basicOpen (f : Γ(Y, U))) :
    Ideal.span s = ⊤ := by
  rw [← IsAffineOpen.self_le_iSup_basicOpen_iff hU]
  intro x hx
  exact TopologicalSpace.Opens.mem_iSup.mpr (h x hx)


end

section
variable {F J J' : Y.IdealSheafData} (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F)
include hF

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.le_of_mul_le_mul (h : F * J ≤ F * J') : J ≤ J' := by
  refine EmbeddedResolution.le_of_forall_ideal_le_consolidated111 fun U => ?_
  intro b hb
  have hU : IsAffineOpen (U : Y.Opens) := U.2
  have hcover :
      Ideal.span {g : Γ(Y, (U : Y.Opens)) | ∃ n : ℕ, g ^ n * b ∈ J'.ideal U} = ⊤ := by
    refine EmbeddedResolution.span_eq_top_of_forall_exists_mem_basicOpen_consolidated111 hU _ ?_
    intro x hx
    obtain ⟨V, t, hxV, htz, hFt⟩ := EmbeddedResolution.exists_affineOpen_ideal_eq_span_singleton_consolidated111 hF x
    have hxUV : x ∈ (U : Y.Opens) ⊓ (V : Y.Opens) := ⟨hx, hxV⟩
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter hU V.2 x hxUV
    have hWfg : Y.affineBasicOpen f = Y.affineBasicOpen g := Subtype.ext hfg
    have hcan : J.ideal (Y.affineBasicOpen f) ≤ J'.ideal (Y.affineBasicOpen f) := by
      rw [hWfg]
      refine EmbeddedResolution.ideal_le_ideal_of_mul_le_mul_consolidated111 h (Y.affineBasicOpen g)
        ((Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom t) ?_ ?_
      · rw [← F.map_ideal_basicOpen V g, hFt, Ideal.map_span, Set.image_singleton]
        rfl
      · have := V.2.isLocalization_basicOpen g
        exact IsLocalization.nonZeroDivisors_le_comap (.powers g) Γ(Y, Y.basicOpen g) htz
    have hbW : (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom b
        ∈ J.ideal (Y.affineBasicOpen f) := by
      rw [← J.map_ideal_basicOpen U f]
      exact Ideal.mem_map_of_mem _ hb
    have hbW2 : (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom b
        ∈ Ideal.map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom (J'.ideal U) := by
      have hbW3 := hcan hbW
      rwa [← J'.map_ideal_basicOpen U f] at hbW3
    have := hU.isLocalization_basicOpen f
    obtain ⟨n, hn⟩ :=
      EmbeddedResolution.exists_pow_mul_mem_of_algebraMap_mem_map_consolidated111 (S := Γ(Y, Y.basicOpen f)) f (J'.ideal U) b hbW2
    exact ⟨⟨f, n, hn⟩, hxf⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (J'.ideal U) _ hcover b ?_
  intro r
  have hr : ∃ n : ℕ, (r : Γ(Y, (U : Y.Opens))) ^ n * b ∈ J'.ideal U := r.2
  obtain ⟨n, hn⟩ := hr
  exact ⟨n, by rw [smul_eq_mul]; exact hn⟩

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.eq_of_mul_eq_mul (h : F * J = F * J') : J = J' :=
  le_antisymm (hF.le_of_mul_le_mul (le_of_eq h)) (hF.le_of_mul_le_mul (le_of_eq h.symm))


end

private theorem exists_affineOpen_mem_subset_consolidated111 (Z : Scheme.{u}) (x : Z) (W : Z.Opens)
    (hx : x ∈ W) : ∃ V : Z.affineOpens, x ∈ (V : Z.Opens) ∧ (V : Z.Opens) ≤ W := by
  obtain ⟨V, hV, hxV, hVW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens hx
  exact ⟨⟨V, hV⟩, hxV, hVW⟩

section
variable {X' Y' : Scheme.{u}} (f : X' ⟶ Y')

private theorem coe_image_of_isOpenImmersion_consolidated111 [IsOpenImmersion f] (V : X'.Opens) :
    ((f ''ᵁ V : Y'.Opens) : Set Y') = f.base '' (V : Set X') := rfl

private theorem coe_preimage_opens_consolidated111 (V : Y'.Opens) :
    ((f ⁻¹ᵁ V : X'.Opens) : Set X') = f.base ⁻¹' (V : Set Y') := rfl


end

section
variable {Y' : Scheme.{u}} (U : Y'.Opens)

private theorem range_opensι_consolidated111 :
    Set.range U.ι.base = (U : Set Y') := U.range_ι

private theorem image_opensι_le_consolidated111 (V : U.toScheme.Opens) :
    (U.ι ''ᵁ V : Y'.Opens) ≤ U := by
  intro z hz
  have hz' : z ∈ U.ι.base '' (V : Set U.toScheme) := hz
  obtain ⟨w, -, rfl⟩ := hz'
  have hr : U.ι.base w ∈ Set.range U.ι.base := Set.mem_range_self w
  rw [range_opensι_consolidated111] at hr
  exact hr

private theorem image_preimage_opensι_consolidated111 (D : Y'.Opens)
    (hD : D ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ D) = D := by
  apply TopologicalSpace.Opens.ext
  rw [coe_image_of_isOpenImmersion_consolidated111, coe_preimage_opens_consolidated111, Set.image_preimage_eq_inter_range,
    range_opensι_consolidated111]
  exact Set.inter_eq_self_of_subset_left hD


end

private theorem basicOpen_appLE_consolidated111 {X' Y' : Scheme.{u}} (f : X' ⟶ Y') {U : Y'.Opens}
    {V : X'.Opens} (h : V ≤ f ⁻¹ᵁ U) (r : Γ(Y', U)) :
    X'.basicOpen ((f.appLE U V h).hom r) = V ⊓ f ⁻¹ᵁ (Y'.basicOpen r) := by
  have h1 : (f.appLE U V h).hom r
      = (X'.presheaf.map (homOfLE h).op).hom ((f.app U).hom r) := rfl
  rw [h1, Scheme.basicOpen_res, Scheme.preimage_basicOpen]

private noncomputable def sectionsOpensImageIso {Y' : Scheme.{u}} (U : Y'.Opens)
    (V : U.toScheme.Opens) : Γ(Y', U.ι ''ᵁ V) ≅ Γ(U.toScheme, V) := U.ι.appIso V

private theorem restrictAppIso_hom_consolidated111 {Y' : Scheme.{u}} (U : Y'.Opens) (V : U.toScheme.Opens) :
    (sectionsOpensImageIso U V).hom
      = U.ι.appLE (U.ι ''ᵁ V) V (U.ι.preimage_image_eq V).ge :=
  Scheme.Hom.appIso_hom' U.ι V

private theorem map_comp_appLE_consolidated111 {X' Y' : Scheme.{u}} (f : X' ⟶ Y') {U₁ U₂ : Y'.Opens}
    (e : U₁ ≤ U₂) {V : X'.Opens} (h : V ≤ f ⁻¹ᵁ U₁) (h' : V ≤ f ⁻¹ᵁ U₂) :
    Y'.presheaf.map (homOfLE e).op ≫ f.appLE U₁ V h = f.appLE U₂ V h' :=
  Scheme.Hom.map_appLE f h (homOfLE e).op

section
variable {F : Y.IdealSheafData} (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F) (U : Y.Opens)
include hF

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.comap_opensι : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor (F.comap U.ι) := by
  intro x
  obtain ⟨W, t, hyW, ht, hFW⟩ := hF (U.ι.base x)
  obtain ⟨V₀, hxV₀, hV₀⟩ :=
    EmbeddedResolution.exists_affineOpen_mem_subset_consolidated111 U.toScheme x (U.ι ⁻¹ᵁ (W : Y.Opens)) hyW
  have hD₀aff : IsAffineOpen (U.ι ''ᵁ (V₀ : U.toScheme.Opens)) :=
    V₀.2.image_of_isOpenImmersion U.ι
  have hyD₀ : U.ι.base x ∈ U.ι ''ᵁ (V₀ : U.toScheme.Opens) := ⟨x, hxV₀, rfl⟩
  obtain ⟨a, b, hab, hya⟩ :=
    exists_basicOpen_le_affine_inter W.2 hD₀aff (U.ι.base x) ⟨hyW, hyD₀⟩
  have hDD₀ : Y.basicOpen a ≤ U.ι ''ᵁ (V₀ : U.toScheme.Opens) := by
    rw [hab]
    exact Y.basicOpen_le b
  have hDU : Y.basicOpen a ≤ U := hDD₀.trans (EmbeddedResolution.image_opensι_le_consolidated111 U (V₀ : U.toScheme.Opens))
  have hDW : Y.basicOpen a ≤ (W : Y.Opens) := Y.basicOpen_le a
  have hpreV₀ : U.ι ⁻¹ᵁ (Y.basicOpen a) ≤ (V₀ : U.toScheme.Opens) := by
    intro z hz
    have h2 : z ∈ U.ι ⁻¹ᵁ (U.ι ''ᵁ (V₀ : U.toScheme.Opens)) := hDD₀ hz
    rwa [U.ι.preimage_image_eq] at h2
  have hV₁eq : U.toScheme.basicOpen
      ((U.ι.appLE (W : Y.Opens) (V₀ : U.toScheme.Opens) hV₀).hom a)
      = U.ι ⁻¹ᵁ (Y.basicOpen a) := by
    rw [_root_.FunctorialResolution.EmbeddedResolution.basicOpen_appLE_consolidated111]
    exact inf_eq_right.mpr hpreV₀
  have hV₁aff : IsAffineOpen (U.ι ⁻¹ᵁ (Y.basicOpen a)) := by
    rw [← hV₁eq]
    exact V₀.2.basicOpen _
  have himg : U.ι ''ᵁ (U.ι ⁻¹ᵁ (Y.basicOpen a)) = Y.basicOpen a :=
    EmbeddedResolution.image_preimage_opensι_consolidated111 U (Y.basicOpen a) hDU
  have himgW : (U.ι ''ᵁ (U.ι ⁻¹ᵁ (Y.basicOpen a))) ≤ (W : Y.Opens) := by
    rw [himg]
    exact hDW
  have hleW : (U.ι ⁻¹ᵁ (Y.basicOpen a)) ≤ U.ι ⁻¹ᵁ (W : Y.Opens) := fun z hz => hDW hz
  refine ⟨⟨U.ι ⁻¹ᵁ (Y.basicOpen a), hV₁aff⟩,
    (U.ι.appLE (W : Y.Opens) (U.ι ⁻¹ᵁ (Y.basicOpen a)) hleW).hom t, hya, ?_, ?_⟩
  · have := W.2.isLocalization_basicOpen a
    have ht' : (Y.presheaf.map (homOfLE hDW).op).hom t
        ∈ nonZeroDivisors Γ(Y, Y.basicOpen a) :=
      IsLocalization.nonZeroDivisors_le_comap (.powers a) Γ(Y, Y.basicOpen a) ht
    have hmor : Y.presheaf.map (homOfLE hDW).op ≫ Y.presheaf.map (eqToHom himg).op ≫
        (_root_.FunctorialResolution.EmbeddedResolution.sectionsOpensImageIso U (U.ι ⁻¹ᵁ (Y.basicOpen a))).hom
        = U.ι.appLE (W : Y.Opens) (U.ι ⁻¹ᵁ (Y.basicOpen a)) hleW := by
      rw [EmbeddedResolution.restrictAppIso_hom_consolidated111, ← Category.assoc, ← Functor.map_comp]
      have h3 : eqToHom himg ≫ homOfLE hDW = homOfLE himgW := Subsingleton.elim _ _
      have h3' : (homOfLE hDW).op ≫ (eqToHom himg).op = (homOfLE himgW).op := by
        rw [← op_comp, h3]
      rw [h3']
      exact EmbeddedResolution.map_comp_appLE_consolidated111 U.ι himgW _ hleW
    have hfin : (U.ι.appLE (W : Y.Opens) (U.ι ⁻¹ᵁ (Y.basicOpen a)) hleW).hom t
        = (_root_.FunctorialResolution.EmbeddedResolution.sectionsOpensImageIso U (U.ι ⁻¹ᵁ (Y.basicOpen a))).hom.hom
            ((Y.presheaf.map (eqToHom himg).op).hom
              ((Y.presheaf.map (homOfLE hDW).op).hom t)) := by
      rw [← hmor]
      rfl
    rw [hfin]
    exact FunctorialResolution.Blowup.map_mem_nonZeroDivisors_of_iso
      (Y.presheaf.mapIso (eqToIso himg).op ≪≫ _root_.FunctorialResolution.EmbeddedResolution.sectionsOpensImageIso U (U.ι ⁻¹ᵁ (Y.basicOpen a))) ht'
  · rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE F U.ι W
      ⟨U.ι ⁻¹ᵁ (Y.basicOpen a), hV₁aff⟩ hleW, hFW, Ideal.map_span, Set.image_singleton]

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.eq_of_mul_eq_mul_comap_opensι {J J' : U.toScheme.IdealSheafData}
    (h : F.comap U.ι * J = F.comap U.ι * J') : J = J' :=
  (hF.comap_opensι U).eq_of_mul_eq_mul h


end

private theorem mem_colon_span_consolidated111 {R : Type*} [CommRing R] (I : Ideal R) (s : Set R)
    (x : R) (h : ∀ g ∈ s, x * g ∈ I) : x ∈ I.colon (Submodule.span R s) := by
  refine Submodule.mem_colon.2 ?_
  intro p hp
  rw [smul_eq_mul]
  induction hp using Submodule.span_induction with
  | mem g hg => exact h g hg
  | zero => rw [mul_zero]; exact zero_mem I
  | add y z _ _ ihy ihz => rw [mul_add]; exact add_mem ihy ihz
  | smul c y _ ih =>
    rw [smul_eq_mul, ← mul_assoc, mul_comm x c, mul_assoc]
    exact I.mul_mem_left c ih

private theorem map_colon_eq_colon_map_away_consolidated111 {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S] (I J : Ideal R) (hJ : J.FG) :
    Ideal.map (algebraMap R S) (I.colon J) =
      (Ideal.map (algebraMap R S) I).colon (Ideal.map (algebraMap R S) J) := by
  refine le_antisymm ?_ ?_
  · have hsub : Ideal.map (algebraMap R S) (I.colon J) * Ideal.map (algebraMap R S) J ≤
        Ideal.map (algebraMap R S) I := by
      rw [← Ideal.map_mul]
      refine Ideal.map_mono (Ideal.mul_le.2 ?_)
      intro a ha b hb
      have ha' := Submodule.mem_colon.mp ha b hb
      rwa [smul_eq_mul] at ha'
    intro z hz
    refine Submodule.mem_colon.2 ?_
    intro p hp
    rw [smul_eq_mul]
    exact hsub (Ideal.mul_mem_mul hz hp)
  · intro b hb
    obtain ⟨s, hs⟩ := hJ
    obtain ⟨w, hab⟩ := IsLocalization.surj (M := Submonoid.powers r) b
    have key : ∀ g ∈ (s : Set R), ∃ n : ℕ, r ^ n * (w.1 * g) ∈ I := by
      intro g hg
      have hgJ : g ∈ J := by
        rw [← hs]; exact Submodule.subset_span hg
      have h1 := Submodule.mem_colon.mp hb (algebraMap R S g) (Ideal.mem_map_of_mem _ hgJ)
      rw [smul_eq_mul] at h1
      have h2 : algebraMap R S (w.1 * g) ∈ Ideal.map (algebraMap R S) I := by
        have heq : algebraMap R S (w.1 * g) =
            b * algebraMap R S g * algebraMap R S (w.2 : R) := by
          rw [map_mul, ← hab]; ring
        rw [heq]
        exact Ideal.mul_mem_right _ _ h1
      exact exists_pow_mul_mem_of_algebraMap_mem_map_consolidated111 r I (w.1 * g) h2
    choose! n hn using key
    have hNa : r ^ (s.sup n) * w.1 ∈ I.colon J := by
      rw [← hs]
      refine mem_colon_span_consolidated111 I (↑s) (r ^ (s.sup n) * w.1) ?_
      intro g hg
      have hle : n g ≤ s.sup n := Finset.le_sup (Finset.mem_coe.mp hg)
      have hg' := hn g hg
      have hpow : r ^ (s.sup n - n g) * r ^ (n g) = r ^ (s.sup n) := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      have hre : r ^ (s.sup n) * w.1 * g = r ^ (s.sup n - n g) * (r ^ (n g) * (w.1 * g)) := by
        rw [← hpow]; ring
      rw [hre]
      exact I.mul_mem_left _ hg'
    have hmem : r ^ (s.sup n) * (w.2 : R) ∈ Submonoid.powers r :=
      mul_mem (pow_mem (Submonoid.mem_powers r) _) w.2.2
    have hunit : IsUnit (algebraMap R S (r ^ (s.sup n) * (w.2 : R))) :=
      IsLocalization.map_units (M := Submonoid.powers r) S
        ⟨r ^ (s.sup n) * (w.2 : R), hmem⟩
    obtain ⟨v, hv⟩ := hunit.exists_right_inv
    have hb2 : b * algebraMap R S (r ^ (s.sup n) * (w.2 : R)) ∈
        Ideal.map (algebraMap R S) (I.colon J) := by
      have heq : b * algebraMap R S (r ^ (s.sup n) * (w.2 : R)) =
          algebraMap R S (r ^ (s.sup n) * w.1) := by
        rw [map_mul, map_mul, ← hab]; ring
      rw [heq]
      exact Ideal.mem_map_of_mem _ hNa
    have hbv := Ideal.mul_mem_right v (Ideal.map (algebraMap R S) (I.colon J)) hb2
    rw [mul_assoc, hv, mul_one] at hbv
    exact hbv

theorem idealSheafColon_ideal_map_basicOpen [IsLocallyNoetherian Y]
    (I' F : Y.IdealSheafData) (U : Y.affineOpens) (f : Γ(Y, U)) :
    Ideal.map (CommRingCat.Hom.hom (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op))
        ((I'.ideal U).colon (F.ideal U)) =
      (I'.ideal (Y.affineBasicOpen f)).colon (F.ideal (Y.affineBasicOpen f)) := by
  have := IsLocallyNoetherian.component_noetherian U
  have : IsLocalization.Away f Γ(Y, Y.basicOpen f) := U.2.isLocalization_basicOpen f
  have key := map_colon_eq_colon_map_away_consolidated111 (S := Γ(Y, Y.basicOpen f)) f (I'.ideal U) (F.ideal U)
    (IsNoetherian.noetherian (F.ideal U))
  rw [← I'.map_ideal_basicOpen U f, ← F.map_ideal_basicOpen U f]
  exact key

def idealSheafColon [IsLocallyNoetherian Y] (I' F : Y.IdealSheafData) :
    Y.IdealSheafData where
  ideal U := (I'.ideal U).colon (F.ideal U)
  map_ideal_basicOpen := idealSheafColon_ideal_map_basicOpen I' F

@[simp]
theorem idealSheafColon_ideal [IsLocallyNoetherian Y] (I' F : Y.IdealSheafData)
    (U : Y.affineOpens) :
    (idealSheafColon I' F).ideal U = (I'.ideal U).colon (F.ideal U) :=
  rfl

private theorem span_singleton_mul_colon_consolidated111 {R : Type*} [CommRing R] {P J : Ideal R}
    (hP : ∃ f : R, P = Ideal.span {f}) (hJ : J ≤ P) : P * J.colon P = J := by
  obtain ⟨f, rfl⟩ := hP
  refine le_antisymm ?_ ?_
  · rw [Ideal.mul_le]
    intro a ha b hb
    have hb' := Submodule.mem_colon.mp hb a ha
    rw [smul_eq_mul] at hb'
    rw [mul_comm a b]
    exact hb'
  · intro y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp (hJ hy)
    have hc : c ∈ J.colon (Ideal.span {f}) := by
      refine Submodule.mem_colon.2 ?_
      intro p hp
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      rw [smul_eq_mul]
      have hre : c * (d * f) = d * (c * f) := by ring
      rw [hre]
      exact J.mul_mem_left d hy
    have hmem := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self f) hc
    rwa [mul_comm f c] at hmem

section
variable {Y' : Scheme.{u}}

private theorem exists_ideal_eq_span_singleton_congr_consolidated111 (F : Y'.IdealSheafData)
    {W W' : Y'.affineOpens} (hW : W = W')
    (h : ∃ f : Γ(Y', W'), F.ideal W' = Ideal.span {f}) :
    ∃ f : Γ(Y', W), F.ideal W = Ideal.span {f} := by
  subst hW
  exact h

private theorem exists_basicOpen_ideal_eq_span_singleton_consolidated111 (F : Y'.IdealSheafData)
    (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F) (U : Y'.affineOpens) (y : Y')
    (hy : y ∈ (U : Y'.Opens)) :
    ∃ g : Γ(Y', U), y ∈ Y'.basicOpen g ∧
      ∃ f : Γ(Y', Y'.affineBasicOpen g), F.ideal (Y'.affineBasicOpen g) = Ideal.span {f} := by
  obtain ⟨V, fV, hyV, hfV, hFV⟩ := hF y
  obtain ⟨g, h, heq, hyg⟩ := exists_basicOpen_le_affine_inter U.2 V.2 y ⟨hy, hyV⟩
  refine ⟨g, hyg, ?_⟩
  have habo : Y'.affineBasicOpen g = Y'.affineBasicOpen h := Subtype.ext heq
  refine exists_ideal_eq_span_singleton_congr_consolidated111 F habo ?_
  have hmap := F.map_ideal_basicOpen V h
  rw [hFV, Ideal.map_span, Set.image_singleton] at hmap
  exact ⟨_, hmap.symm⟩

private theorem span_eq_top_of_cover_basicOpen_consolidated111 (U : Y'.affineOpens)
    (T : Set Γ(Y', U))
    (hcov : ∀ y : Y', y ∈ (U : Y'.Opens) → ∃ g ∈ T, y ∈ Y'.basicOpen g) :
    Ideal.span T = ⊤ := by
  refine span_eq_top_of_forall_exists_mem_basicOpen_consolidated111 U.2 T ?_
  intro y hy
  obtain ⟨g, hgT, hyg⟩ := hcov y hy
  exact ⟨⟨g, hgT⟩, hyg⟩

private theorem exists_pow_mul_mem_mul_colon_consolidated111 [IsLocallyNoetherian Y']
    (F I' : Y'.IdealSheafData) (hIle : ∀ U : Y'.affineOpens, I'.ideal U ≤ F.ideal U)
    (U : Y'.affineOpens) (x : Γ(Y', U)) (hx : x ∈ I'.ideal U) (g : Γ(Y', U))
    (f : Γ(Y', Y'.affineBasicOpen g))
    (hf : F.ideal (Y'.affineBasicOpen g) = Ideal.span {f}) :
    ∃ n : ℕ, g ^ n * x ∈ F.ideal U * (I'.ideal U).colon (F.ideal U) := by
  have : IsLocalization.Away g Γ(Y', Y'.basicOpen g) := U.2.isLocalization_basicOpen g
  have h1 : Ideal.map (CommRingCat.Hom.hom (Y'.presheaf.map (homOfLE (Y'.basicOpen_le g)).op))
      (F.ideal U * (I'.ideal U).colon (F.ideal U)) = I'.ideal (Y'.affineBasicOpen g) := by
    rw [Ideal.map_mul, F.map_ideal_basicOpen U g,
      idealSheafColon_ideal_map_basicOpen I' F U g]
    exact span_singleton_mul_colon_consolidated111 ⟨f, hf⟩ (hIle (Y'.affineBasicOpen g))
  have h2 : (CommRingCat.Hom.hom (Y'.presheaf.map (homOfLE (Y'.basicOpen_le g)).op)) x ∈
      Ideal.map (CommRingCat.Hom.hom (Y'.presheaf.map (homOfLE (Y'.basicOpen_le g)).op))
        (F.ideal U * (I'.ideal U).colon (F.ideal U)) := by
    rw [h1, ← I'.map_ideal_basicOpen U g]
    exact Ideal.mem_map_of_mem _ hx
  have h3 : algebraMap Γ(Y', U) Γ(Y', Y'.basicOpen g) x ∈
      Ideal.map (algebraMap Γ(Y', U) Γ(Y', Y'.basicOpen g))
        (F.ideal U * (I'.ideal U).colon (F.ideal U)) := h2
  exact exists_pow_mul_mem_of_algebraMap_mem_map_consolidated111 g _ x h3


end

section
variable [IsLocallyNoetherian Y] {F I' : Y.IdealSheafData} (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F) (hI : I' ≤ F)
include hF hI

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.mul_idealSheafColon :
    F * EmbeddedResolution.idealSheafColon I' F = I' := by
  have hIle : ∀ U : Y.affineOpens, I'.ideal U ≤ F.ideal U := fun U => hI U
  refine Scheme.IdealSheafData.ext (funext ?_)
  intro U
  rw [EmbeddedResolution.mul_ideal_apply_consolidated111, EmbeddedResolution.idealSheafColon_ideal]
  refine le_antisymm ?_ ?_
  · rw [Ideal.mul_le]
    intro a ha b hb
    have hb' := Submodule.mem_colon.mp hb a ha
    rw [smul_eq_mul] at hb'
    rw [mul_comm a b]
    exact hb'
  · intro x hx
    have hspan : Ideal.span {g : Γ(Y, U) | ∃ f : Γ(Y, Y.affineBasicOpen g),
        F.ideal (Y.affineBasicOpen g) = Ideal.span {f}} = ⊤ := by
      refine EmbeddedResolution.span_eq_top_of_cover_basicOpen_consolidated111 U _ ?_
      intro y hy
      obtain ⟨g, hyg, hfg⟩ := EmbeddedResolution.exists_basicOpen_ideal_eq_span_singleton_consolidated111 F hF U y hy
      exact ⟨g, hfg, hyg⟩
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hspan x ?_
    intro r
    have hr : ∃ f : Γ(Y, Y.affineBasicOpen (r : Γ(Y, U))),
        F.ideal (Y.affineBasicOpen (r : Γ(Y, U))) = Ideal.span {f} := r.2
    obtain ⟨f, hf⟩ := hr
    obtain ⟨n, hn⟩ := EmbeddedResolution.exists_pow_mul_mem_mul_colon_consolidated111 F I' hIle U x hx (r : Γ(Y, U)) f hf
    exact ⟨n, by rw [smul_eq_mul]; exact hn⟩

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.exists_mul_eq :
    ∃ J : Y.IdealSheafData, F * J = I' :=
  ⟨EmbeddedResolution.idealSheafColon I' F, hF.mul_idealSheafColon hI⟩

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.existsUnique_mul_eq :
    ∃! J : Y.IdealSheafData, F * J = I' := by
  refine ⟨EmbeddedResolution.idealSheafColon I' F, hF.mul_idealSheafColon hI, ?_⟩
  intro J hJ
  exact hF.eq_of_mul_eq_mul (hJ.trans (hF.mul_idealSheafColon hI).symm)


end

variable {X X₁ : Scheme.{u}}

theorem comap_le_exceptionalIdeal_pow (π : X₁ ⟶ X) {Z I : X.IdealSheafData} {n : ℕ}
    (hI : I ≤ Z ^ n) : I.comap π ≤ Blowup.exceptionalIdeal π Z ^ n := by
  rw [Blowup.exceptionalIdeal_eq_comap, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_pow]
  apply AlgebraicGeometry.Scheme.IdealSheafData.comap_mono
  exact hI

section
variable [IsLocallyNoetherian X₁] (π : X₁ ⟶ X) (Z I : X.IdealSheafData) (n : ℕ)

theorem existsUnique_pow_mul_eq_comap (hZ : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z))
    (hI : I ≤ Z ^ n) :
    ∃! J : X₁.IdealSheafData, Blowup.exceptionalIdeal π Z ^ n * J = I.comap π :=
  (hZ.pow n).existsUnique_mul_eq (comap_le_exceptionalIdeal_pow π hI)

theorem existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hI : I ≤ Z ^ n) :
    ∃! J : X₁.IdealSheafData, Blowup.exceptionalIdeal π Z ^ n * J = I.comap π := by
  have hZ : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := by
    rw [Blowup.exceptionalIdeal_eq_comap]
    exact hπ.1
  exact existsUnique_pow_mul_eq_comap π Z I n hZ hI


end

def controlledTransform [IsLocallyNoetherian X₁] (π : X₁ ⟶ X) (Z I : X.IdealSheafData)
    (n : ℕ) (_hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (_hI : I ≤ Z ^ n) : X₁.IdealSheafData :=
  idealSheafColon (I.comap π) (Blowup.exceptionalIdeal π Z ^ n)

section
variable [IsLocallyNoetherian X₁] (π : X₁ ⟶ X) (Z I : X.IdealSheafData) (n : ℕ) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hI : I ≤ Z ^ n)

theorem exceptionalIdeal_pow_mul_controlledTransform :
    Blowup.exceptionalIdeal π Z ^ n * controlledTransform π Z I n hπ hI = I.comap π := by
  have hZ : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := by
    rw [Blowup.exceptionalIdeal_eq_comap]
    exact hπ.1
  have hle : I.comap π ≤ Blowup.exceptionalIdeal π Z ^ n := comap_le_exceptionalIdeal_pow π hI
  exact (hZ.pow n).mul_idealSheafColon hle

theorem eq_controlledTransform_of_mul_eq_comap (J : X₁.IdealSheafData) (hJ : Blowup.exceptionalIdeal π Z ^ n * J = I.comap π) :
    J = controlledTransform π Z I n hπ hI :=
  (existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf π Z I n hπ hI).unique hJ
    (exceptionalIdeal_pow_mul_controlledTransform π Z I n hπ hI)


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
section
open CategoryTheory AlgebraicGeometry

section


def coordIdeal (R : Type u) [CommRing R] {σ : Type v} (S : Finset σ) : Ideal (MvPolynomial σ R) :=
  Ideal.span ((MvPolynomial.X : σ → MvPolynomial σ R) '' (S : Set σ))

section
variable (R : Type u) [CommRing R] {σ : Type v} (S : Finset σ)

theorem coordIdeal_eq_span :
    coordIdeal R S = Ideal.span ((MvPolynomial.X : σ → MvPolynomial σ R) '' (S : Set σ)) := rfl

theorem X_mem_coordIdeal {i : σ}
    (hi : i ∈ S) : (MvPolynomial.X i : MvPolynomial σ R) ∈ coordIdeal R S :=
  Ideal.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩


end

def coordIdealGen (R : Type u) [CommRing R] {σ : Type v} (S : Finset σ) (i : σ) (hi : i ∈ S) :
    ↥(coordIdeal R S) :=
  ⟨MvPolynomial.X i, X_mem_coordIdeal R S hi⟩

@[simp] theorem coe_coordIdealGen (R : Type u) [CommRing R] {σ : Type v} (S : Finset σ) (i : σ)
    (hi : i ∈ S) :
    ((coordIdealGen R S i hi : ↥(coordIdeal R S)) : MvPolynomial σ R) = MvPolynomial.X i := rfl

private theorem reesGenerator_mem_of_span_consolidated165 {A : Type u} [CommRing A] (s : Set A)
    (P : Ideal ↥(reesAlgebra (Ideal.span s)))
    (hP : ∀ y ∈ s, ∀ hy : y ∈ Ideal.span s, Blowup.reesGenerator (Ideal.span s) ⟨y, hy⟩ ∈ P)
    (a : ↥(Ideal.span s)) : Blowup.reesGenerator (Ideal.span s) a ∈ P := by
  obtain ⟨r, hr⟩ := a
  induction hr using Submodule.span_induction with
  | mem x hx => exact hP x hx _
  | zero =>
      have e : Blowup.reesGenerator (Ideal.span s) (0 : ↥(Ideal.span s)) = 0 := by
        apply Subtype.ext
        simp [Blowup.reesGenerator_coe]
      show Blowup.reesGenerator (Ideal.span s) (0 : ↥(Ideal.span s)) ∈ P
      rw [e]
      exact P.zero_mem
  | add x y hx hy ihx ihy =>
      have e : Blowup.reesGenerator (Ideal.span s) ((⟨x, hx⟩ : ↥(Ideal.span s)) + ⟨y, hy⟩)
          = Blowup.reesGenerator (Ideal.span s) ⟨x, hx⟩ + Blowup.reesGenerator (Ideal.span s) ⟨y, hy⟩ := by
        apply Subtype.ext
        simp [Blowup.reesGenerator_coe]
      show Blowup.reesGenerator (Ideal.span s) ((⟨x, hx⟩ : ↥(Ideal.span s)) + ⟨y, hy⟩) ∈ P
      rw [e]
      exact P.add_mem ihx ihy
  | smul c x hx ih =>
      have e : Blowup.reesGenerator (Ideal.span s) (c • (⟨x, hx⟩ : ↥(Ideal.span s)))
          = c • Blowup.reesGenerator (Ideal.span s) ⟨x, hx⟩ := by
        apply Subtype.ext
        simp [Blowup.reesGenerator_coe, Polynomial.smul_monomial, smul_eq_mul]
      show Blowup.reesGenerator (Ideal.span s) (c • (⟨x, hx⟩ : ↥(Ideal.span s))) ∈ P
      rw [e, Algebra.smul_def]
      exact Ideal.mul_mem_left P _ ih

private theorem reesGenerator_mem_homogeneousIdeal_of_span_consolidated165 {A : Type u} [CommRing A] (s : Set A)
    (P : HomogeneousIdeal (Blowup.reesGrading (Ideal.span s)))
    (hP : ∀ y ∈ s, ∀ hy : y ∈ Ideal.span s, Blowup.reesGenerator (Ideal.span s) ⟨y, hy⟩ ∈ P)
    (a : ↥(Ideal.span s)) : Blowup.reesGenerator (Ideal.span s) a ∈ P :=
  reesGenerator_mem_of_span_consolidated165 s P.toIdeal (fun y hy hy2 => hP y hy hy2) a

section
variable (R : Type u) [CommRing R] {σ : Type v}

theorem iSup_opensRange_affineBlowupChart_coordIdealGen (S : Finset σ) :
    (⨆ i : ↥S, Scheme.Hom.opensRange
        (Blowup.affineBlowupChart (coordIdeal R S) (coordIdealGen R S i.1 i.2)))
      = (⊤ : (Blowup.affineBlowup (coordIdeal R S)).Opens) := by
  refine le_antisymm le_top ?_
  rw [SetLike.le_def]
  intro x _
  have hxtop : x ∈ (⨆ a : ↥(coordIdeal R S),
      Proj.basicOpen (Blowup.reesGrading (coordIdeal R S)) (Blowup.reesGenerator (coordIdeal R S) a)) := by
    rw [Blowup.iSup_proj_basicOpen_reesGenerator_eq_top]
    trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hxtop
  by_contra hxn
  refine (Proj.mem_basicOpen ..).mp ha ?_
  refine reesGenerator_mem_homogeneousIdeal_of_span_consolidated165
    ((MvPolynomial.X : σ → MvPolynomial σ R) '' (S : Set σ)) _ ?_ a
  intro y hy hy2
  obtain ⟨i, hiS, rfl⟩ := hy
  by_contra hcon
  refine hxn (TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, Finset.mem_coe.mp hiS⟩, ?_⟩)
  rw [Blowup.opensRange_affineBlowupChart_eq_basicOpen]
  exact (Proj.mem_basicOpen ..).mpr hcon

theorem X_mem_nonZeroDivisors (i : σ) :
    (MvPolynomial.X i : MvPolynomial σ R) ∈ nonZeroDivisors (MvPolynomial σ R) := by
  have key : ∀ x : MvPolynomial σ R, x * MvPolynomial.X i = 0 → x = 0 := by
    intro x hx
    ext m
    have h := MvPolynomial.coeff_mul_X m i x
    rw [hx, MvPolynomial.coeff_zero] at h
    simp [← h]
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx => key x (by rw [mul_comm]; exact hx), key⟩


end

def coordBlowupSubst (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ] (S : Finset σ) (s : σ) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval fun i =>
    if i ∈ S ∧ i ≠ s then (MvPolynomial.X i : MvPolynomial σ R) * MvPolynomial.X s
    else MvPolynomial.X i

section
variable (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ] (S : Finset σ) (s : σ)

theorem coordBlowupSubst_X (i : σ) :
    coordBlowupSubst R S s (MvPolynomial.X i) =
      if i ∈ S ∧ i ≠ s then (MvPolynomial.X i : MvPolynomial σ R) * MvPolynomial.X s
      else MvPolynomial.X i :=
  MvPolynomial.aeval_X _ i

@[simp] theorem coordBlowupSubst_X_of_mem {i : σ} (hi : i ∈ S) (hne : i ≠ s) :
    coordBlowupSubst R S s (MvPolynomial.X i) =
      (MvPolynomial.X i : MvPolynomial σ R) * MvPolynomial.X s := by
  rw [coordBlowupSubst_X, if_pos ⟨hi, hne⟩]

@[simp] theorem coordBlowupSubst_X_self :
    coordBlowupSubst R S s (MvPolynomial.X s) = (MvPolynomial.X s : MvPolynomial σ R) := by
  rw [coordBlowupSubst_X, if_neg]
  rintro ⟨-, h⟩
  exact h rfl

@[simp] theorem coordBlowupSubst_X_of_not_mem_erase {i : σ} (h : ¬ (i ∈ S ∧ i ≠ s)) :
    coordBlowupSubst R S s (MvPolynomial.X i) = (MvPolynomial.X i : MvPolynomial σ R) := by
  rw [coordBlowupSubst_X, if_neg h]

theorem coordBlowupSubst_C (r : R) :
    coordBlowupSubst R S s (MvPolynomial.C r) = (MvPolynomial.C r : MvPolynomial σ R) := by
  rw [← MvPolynomial.algebraMap_eq]
  exact (coordBlowupSubst R S s).commutes r

theorem map_coordIdeal_coordBlowupSubst (hs : s ∈ S) :
    Ideal.map (coordBlowupSubst R S s).toRingHom (coordIdeal R S)
      = Ideal.span {(MvPolynomial.X s : MvPolynomial σ R)} := by
  apply le_antisymm
  · rw [coordIdeal_eq_span, Ideal.map_span, Ideal.span_le]
    rintro y ⟨x, ⟨i, hi, rfl⟩, rfl⟩
    show (coordBlowupSubst R S s).toRingHom (MvPolynomial.X i) ∈
      Ideal.span {(MvPolynomial.X s : MvPolynomial σ R)}
    by_cases h : i ∈ S ∧ i ≠ s
    · rw [show (coordBlowupSubst R S s).toRingHom (MvPolynomial.X i)
          = (MvPolynomial.X i : MvPolynomial σ R) * MvPolynomial.X s from
        coordBlowupSubst_X_of_mem R S s h.1 h.2]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · have hieq : i = s := by
        by_contra hne
        exact h ⟨Finset.mem_coe.mp hi, hne⟩
      rw [show (coordBlowupSubst R S s).toRingHom (MvPolynomial.X i)
          = (MvPolynomial.X i : MvPolynomial σ R) from coordBlowupSubst_X_of_not_mem_erase R S s h, hieq]
      exact Ideal.mem_span_singleton_self _
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have h1 : (MvPolynomial.X s : MvPolynomial σ R) ∈ coordIdeal R S := X_mem_coordIdeal R S hs
    have h2 := Ideal.mem_map_of_mem ((coordBlowupSubst R S s).toRingHom) h1
    rw [show (coordBlowupSubst R S s).toRingHom (MvPolynomial.X s)
        = (MvPolynomial.X s : MvPolynomial σ R) from coordBlowupSubst_X_self R S s] at h2
    exact h2


end

private theorem coe_reesDegreeZeroEquiv_consolidated165 {A : Type u} [CommRing A] (I : Ideal A) (r : A) :
    ((Blowup.reesDegreeZeroEquiv I r : ↥(Blowup.reesGrading I 0)) : ↥(reesAlgebra I))
      = algebraMap A ↥(reesAlgebra I) r := by
  apply Subtype.ext
  rw [Blowup.reesDegreeZeroEquiv_coe_coe]
  simp [Polynomial.C_eq_algebraMap]

private def coordIdealReesAlgebraLift_consolidated165 (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) :
    ↥(reesAlgebra (coordIdeal R S)) →+* MvPolynomial σ R :=
  Blowup.reesAlgebraLift (coordIdeal R S) (coordBlowupSubst R S s).toRingHom (MvPolynomial.X s)
    (map_coordIdeal_coordBlowupSubst R S s hs) (X_mem_nonZeroDivisors R s)

section
variable (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ] (S : Finset σ) (s : σ) (hs : s ∈ S)

private theorem reesAlgebraToMvPolynomial_algebraMap_consolidated165 (r : MvPolynomial σ R) :
    coordIdealReesAlgebraLift_consolidated165 R S s hs (algebraMap (MvPolynomial σ R) ↥(reesAlgebra (coordIdeal R S)) r)
      = coordBlowupSubst R S s r :=
  Blowup.reesAlgebraLift_algebraMap (coordIdeal R S) (coordBlowupSubst R S s).toRingHom (MvPolynomial.X s)
    (map_coordIdeal_coordBlowupSubst R S s hs) (X_mem_nonZeroDivisors R s) r

private theorem reesAlgebraToMvPolynomial_reesGenerator_consolidated165 :
    coordIdealReesAlgebraLift_consolidated165 R S s hs (Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs)) = 1 :=
  Blowup.reesAlgebraLift_reesGenerator (coordIdeal R S) (coordBlowupSubst R S s).toRingHom (MvPolynomial.X s)
    (map_coordIdeal_coordBlowupSubst R S s hs) (X_mem_nonZeroDivisors R s)
    (coordIdealGen R S s hs) (by rw [coe_coordIdealGen]; exact coordBlowupSubst_X_self R S s)

private theorem isUnit_reesAlgebraToMvPolynomial_powers_consolidated165 :
    ∀ y : ↥(Submonoid.powers (Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs))),
      IsUnit (coordIdealReesAlgebraLift_consolidated165 R S s hs (y : ↥(reesAlgebra (coordIdeal R S)))) := by
  rintro ⟨y, n, rfl⟩
  show IsUnit (coordIdealReesAlgebraLift_consolidated165 R S s hs
    ((Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs)) ^ n))
  rw [map_pow, reesAlgebraToMvPolynomial_reesGenerator_consolidated165, one_pow]
  exact isUnit_one


end

private def homogeneousAwayToLocalization_consolidated165 {A : Type u} [CommRing A] (I : Ideal A) (a : ↥I) :
    HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a) →+*
      Localization (Submonoid.powers (Blowup.reesGenerator I a)) :=
  algebraMap (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a))
    (Localization (Submonoid.powers (Blowup.reesGenerator I a)))

private theorem homogeneousLocalizationVal_apply_consolidated165 {A : Type u} [CommRing A] (I : Ideal A) (a : ↥I)
    (z : HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) :
    homogeneousAwayToLocalization_consolidated165 I a z = HomogeneousLocalization.val z :=
  HomogeneousLocalization.algebraMap_apply ..

private def coordBlowupChartToMvPolynomial_consolidated165 (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) :
    HomogeneousLocalization.Away (Blowup.reesGrading (coordIdeal R S))
        (Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs)) →+* MvPolynomial σ R :=
  (IsLocalization.lift (isUnit_reesAlgebraToMvPolynomial_powers_consolidated165 R S s hs)).comp
    (homogeneousAwayToLocalization_consolidated165 (coordIdeal R S) (coordIdealGen R S s hs))

section
variable (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ] (S : Finset σ) (s : σ) (hs : s ∈ S)

private theorem chartToMvPolynomial_apply_consolidated165 (z : HomogeneousLocalization.Away (Blowup.reesGrading (coordIdeal R S))
      (Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs))) :
    coordBlowupChartToMvPolynomial_consolidated165 R S s hs z =
      IsLocalization.lift (isUnit_reesAlgebraToMvPolynomial_powers_consolidated165 R S s hs) (HomogeneousLocalization.val z) := by
  show IsLocalization.lift (isUnit_reesAlgebraToMvPolynomial_powers_consolidated165 R S s hs)
      (homogeneousAwayToLocalization_consolidated165 (coordIdeal R S) (coordIdealGen R S s hs) z) = _
  rw [homogeneousLocalizationVal_apply_consolidated165]

private theorem chartToMvPolynomial_chartRingHom_consolidated165 (r : MvPolynomial σ R) :
    coordBlowupChartToMvPolynomial_consolidated165 R S s hs (Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) r)
      = coordBlowupSubst R S s r := by
  have hval : HomogeneousLocalization.val (Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) r)
      = Localization.mk
          ((Blowup.reesDegreeZeroEquiv (coordIdeal R S) r : ↥(reesAlgebra (coordIdeal R S)))) 1 := rfl
  rw [chartToMvPolynomial_apply_consolidated165, hval, Localization.mk_eq_mk', IsLocalization.mk'_one,
    IsLocalization.lift_eq, coe_reesDegreeZeroEquiv_consolidated165, reesAlgebraToMvPolynomial_algebraMap_consolidated165]


end

private def mvPolynomialToCoordBlowupChart_consolidated165 (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) :
    MvPolynomial σ R →+* HomogeneousLocalization.Away (Blowup.reesGrading (coordIdeal R S))
      (Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs)) :=
  MvPolynomial.eval₂Hom
    ((Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs)).comp
      (MvPolynomial.C : R →+* MvPolynomial σ R))
    (fun i => if h : i ∈ S ∧ i ≠ s then
        Blowup.chartFraction (coordIdeal R S) (coordIdealGen R S s hs) (coordIdealGen R S i h.1)
      else Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.X i))

section
variable (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ] (S : Finset σ) (s : σ) (hs : s ∈ S)

private theorem awayCoordGenEquivMvPolynomial_invFun_C_consolidated165 (r : R) :
    mvPolynomialToCoordBlowupChart_consolidated165 R S s hs (MvPolynomial.C r)
      = Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.C r) :=
  MvPolynomial.eval₂Hom_C _ _ r

private theorem awayCoordGenEquivMvPolynomial_invFun_X_consolidated165 (i : σ) :
    mvPolynomialToCoordBlowupChart_consolidated165 R S s hs (MvPolynomial.X i)
      = if h : i ∈ S ∧ i ≠ s then
          Blowup.chartFraction (coordIdeal R S) (coordIdealGen R S s hs) (coordIdealGen R S i h.1)
        else Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.X i) :=
  MvPolynomial.eval₂Hom_X' _ _ i

private theorem awayCoordGenEquivMvPolynomial_invFun_X_self_consolidated165 :
    mvPolynomialToCoordBlowupChart_consolidated165 R S s hs (MvPolynomial.X s)
      = Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.X s) := by
  rw [awayCoordGenEquivMvPolynomial_invFun_X_consolidated165, dif_neg]
  rintro ⟨-, h⟩
  exact h rfl

private theorem mvPolynomialToChart_coordBlowupSubst_consolidated165 (f : MvPolynomial σ R) :
    mvPolynomialToCoordBlowupChart_consolidated165 R S s hs (coordBlowupSubst R S s f)
      = Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) f := by
  have key : (mvPolynomialToCoordBlowupChart_consolidated165 R S s hs).comp ((coordBlowupSubst R S s).toRingHom)
      = Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro r
      show mvPolynomialToCoordBlowupChart_consolidated165 R S s hs (coordBlowupSubst R S s (MvPolynomial.C r)) = _
      rw [coordBlowupSubst_C, awayCoordGenEquivMvPolynomial_invFun_C_consolidated165]
    · intro i
      show mvPolynomialToCoordBlowupChart_consolidated165 R S s hs (coordBlowupSubst R S s (MvPolynomial.X i)) = _
      by_cases h : i ∈ S ∧ i ≠ s
      · rw [coordBlowupSubst_X_of_mem R S s h.1 h.2, map_mul, awayCoordGenEquivMvPolynomial_invFun_X_consolidated165, dif_pos h, awayCoordGenEquivMvPolynomial_invFun_X_self_consolidated165]
        have hb := Blowup.chartRingHom_coe_eq_chartFraction_mul (coordIdeal R S) (coordIdealGen R S s hs)
          (coordIdealGen R S i h.1)
        rw [coe_coordIdealGen, coe_coordIdealGen] at hb
        exact hb.symm
      · rw [coordBlowupSubst_X_of_not_mem_erase R S s h, awayCoordGenEquivMvPolynomial_invFun_X_consolidated165, dif_neg h]
  exact DFunLike.congr_fun key f

private theorem chartToMvPolynomial_mvPolynomialToChart_consolidated165 (f : MvPolynomial σ R) :
    coordBlowupChartToMvPolynomial_consolidated165 R S s hs (mvPolynomialToCoordBlowupChart_consolidated165 R S s hs f) = f := by
  have key : (coordBlowupChartToMvPolynomial_consolidated165 R S s hs).comp (mvPolynomialToCoordBlowupChart_consolidated165 R S s hs) = RingHom.id (MvPolynomial σ R) := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro r
      show coordBlowupChartToMvPolynomial_consolidated165 R S s hs (mvPolynomialToCoordBlowupChart_consolidated165 R S s hs (MvPolynomial.C r)) = MvPolynomial.C r
      rw [awayCoordGenEquivMvPolynomial_invFun_C_consolidated165, chartToMvPolynomial_chartRingHom_consolidated165, coordBlowupSubst_C]
    · intro i
      show coordBlowupChartToMvPolynomial_consolidated165 R S s hs (mvPolynomialToCoordBlowupChart_consolidated165 R S s hs (MvPolynomial.X i)) = MvPolynomial.X i
      by_cases h : i ∈ S ∧ i ≠ s
      · rw [awayCoordGenEquivMvPolynomial_invFun_X_consolidated165, dif_pos h]
        have hb := Blowup.chartRingHom_coe_eq_chartFraction_mul (coordIdeal R S) (coordIdealGen R S s hs)
          (coordIdealGen R S i h.1)
        rw [coe_coordIdealGen, coe_coordIdealGen] at hb
        have h2 := congrArg (coordBlowupChartToMvPolynomial_consolidated165 R S s hs) hb
        rw [chartToMvPolynomial_chartRingHom_consolidated165, map_mul, chartToMvPolynomial_chartRingHom_consolidated165,
          coordBlowupSubst_X_of_mem R S s h.1 h.2, coordBlowupSubst_X_self] at h2
        have hnzd := X_mem_nonZeroDivisors R s
        exact (mul_cancel_right_mem_nonZeroDivisors hnzd).mp h2.symm
      · rw [awayCoordGenEquivMvPolynomial_invFun_X_consolidated165, dif_neg h, chartToMvPolynomial_chartRingHom_consolidated165, coordBlowupSubst_X_of_not_mem_erase R S s h]
  exact DFunLike.congr_fun key f

private theorem mvPolynomialToChart_surjective_consolidated165 : Function.Surjective (mvPolynomialToCoordBlowupChart_consolidated165 R S s hs) := by
  intro z
  obtain ⟨n, r, hr⟩ := Blowup.exists_mul_pow_eq_chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) z
  have hLc : coordBlowupChartToMvPolynomial_consolidated165 R S s hs
      (Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs)
        ((coordIdealGen R S s hs : ↥(coordIdeal R S)) : MvPolynomial σ R))
      = (MvPolynomial.X s : MvPolynomial σ R) := by
    rw [chartToMvPolynomial_chartRingHom_consolidated165, coe_coordIdealGen, coordBlowupSubst_X_self]
  have hpL : coordBlowupChartToMvPolynomial_consolidated165 R S s hs
      (Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs)
        ((coordIdealGen R S s hs : ↥(coordIdeal R S)) : MvPolynomial σ R) ^ n)
      = coordBlowupChartToMvPolynomial_consolidated165 R S s hs
        (Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs)
          ((coordIdealGen R S s hs : ↥(coordIdeal R S)) : MvPolynomial σ R)) ^ n :=
    map_pow (coordBlowupChartToMvPolynomial_consolidated165 R S s hs)
      (Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs)
        ((coordIdealGen R S s hs : ↥(coordIdeal R S)) : MvPolynomial σ R)) n
  have h2 : coordBlowupChartToMvPolynomial_consolidated165 R S s hs z * (MvPolynomial.X s : MvPolynomial σ R) ^ n
      = coordBlowupSubst R S s r := by
    have hcg := congrArg (coordBlowupChartToMvPolynomial_consolidated165 R S s hs) hr
    rw [map_mul, hpL, hLc, chartToMvPolynomial_chartRingHom_consolidated165] at hcg
    exact hcg
  have hpF : mvPolynomialToCoordBlowupChart_consolidated165 R S s hs ((MvPolynomial.X s : MvPolynomial σ R) ^ n)
      = mvPolynomialToCoordBlowupChart_consolidated165 R S s hs (MvPolynomial.X s) ^ n :=
    map_pow (mvPolynomialToCoordBlowupChart_consolidated165 R S s hs) (MvPolynomial.X s) n
  have h3 : mvPolynomialToCoordBlowupChart_consolidated165 R S s hs (coordBlowupChartToMvPolynomial_consolidated165 R S s hs z) *
      Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.X s) ^ n
      = Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) r := by
    have hcg := congrArg (mvPolynomialToCoordBlowupChart_consolidated165 R S s hs) h2
    rw [map_mul, hpF, awayCoordGenEquivMvPolynomial_invFun_X_self_consolidated165, mvPolynomialToChart_coordBlowupSubst_consolidated165] at hcg
    exact hcg
  have hnzd0 : Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.X s) ∈
      nonZeroDivisors (HomogeneousLocalization.Away (Blowup.reesGrading (coordIdeal R S))
        (Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs))) :=
    Blowup.chartRingHom_mem_nonZeroDivisors (coordIdeal R S) (coordIdealGen R S s hs)
  have hnzd : Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.X s) ^ n ∈
      nonZeroDivisors (HomogeneousLocalization.Away (Blowup.reesGrading (coordIdeal R S))
        (Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs))) :=
    pow_mem hnzd0 n
  refine ⟨coordBlowupChartToMvPolynomial_consolidated165 R S s hs z, ?_⟩
  have h : mvPolynomialToCoordBlowupChart_consolidated165 R S s hs (coordBlowupChartToMvPolynomial_consolidated165 R S s hs z) *
      Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.X s) ^ n
      = z * Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.X s) ^ n := by
    rw [h3]
    exact hr.symm
  exact (mul_cancel_right_mem_nonZeroDivisors hnzd).mp h

private theorem exists_ringEquiv_away_mvPolynomial_consolidated165 :
    ∃ e : HomogeneousLocalization.Away (Blowup.reesGrading (coordIdeal R S))
        (Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs)) ≃+* MvPolynomial σ R,
      e.symm.toRingHom.comp (coordBlowupSubst R S s).toRingHom
        = Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) := by
  have hL : Function.LeftInverse (coordBlowupChartToMvPolynomial_consolidated165 R S s hs) (mvPolynomialToCoordBlowupChart_consolidated165 R S s hs) :=
    fun f => chartToMvPolynomial_mvPolynomialToChart_consolidated165 R S s hs f
  refine ⟨(RingEquiv.ofBijective (mvPolynomialToCoordBlowupChart_consolidated165 R S s hs)
      ⟨hL.injective, mvPolynomialToChart_surjective_consolidated165 R S s hs⟩).symm, ?_⟩
  rw [RingEquiv.symm_symm]
  refine RingHom.ext fun f => ?_
  exact mvPolynomialToChart_coordBlowupSubst_consolidated165 R S s hs f


end

def awayCoordGenEquivMvPolynomial (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ] (S : Finset σ) (s : σ)
    (hs : s ∈ S) :
    HomogeneousLocalization.Away (Blowup.reesGrading (coordIdeal R S))
        (Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs)) ≃+* MvPolynomial σ R :=
  (exists_ringEquiv_away_mvPolynomial_consolidated165 R S s hs).choose

theorem awayCoordGenEquivMvPolynomial_symm_comp_coordBlowupSubst (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) :
    (awayCoordGenEquivMvPolynomial R S s hs).symm.toRingHom.comp (coordBlowupSubst R S s).toRingHom
      = Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) :=
  (exists_ringEquiv_away_mvPolynomial_consolidated165 R S s hs).choose_spec

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits


private theorem map_mem_nonZeroDivisors_of_flat_consolidated208 {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.Flat) {s : R} (hs : s ∈ nonZeroDivisors R) :
    φ s ∈ nonZeroDivisors S := by
  let _ : Algebra R S := φ.toAlgebra
  have : Module.Flat R S := hφ
  have hmul : ∀ x : S, φ s * x = s • x := by
    intro x
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hs1 : ∀ x : R, s * x = 0 → x = 0 := (mem_nonZeroDivisors_iff.mp hs).1
  have hL : Function.Injective (LinearMap.mulLeft R s) := by
    intro a b hab
    have h1 : s * a = s * b := by
      simpa only [LinearMap.mulLeft_apply] using hab
    have h2 : s * (a - b) = 0 := by rw [mul_sub, h1, sub_self]
    exact sub_eq_zero.mp (hs1 _ h2)
  have hinj : Function.Injective ((LinearMap.mulLeft R s).rTensor S) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := S) _ hL
  have key : ∀ t : S, φ s * t = 0 → t = 0 := by
    intro t ht
    have hsmul : s • t = 0 := by rw [← hmul t]; exact ht
    have e1 : TensorProduct.tmul R s t = (0 : TensorProduct R R S) := by
      have h3 : TensorProduct.tmul R s t = TensorProduct.tmul R (1 : R) (s • t) := by
        rw [← TensorProduct.smul_tmul, smul_eq_mul, mul_one]
      rw [h3, hsmul, TensorProduct.tmul_zero]
    have e0 : ((LinearMap.mulLeft R s).rTensor S) (TensorProduct.tmul R (1 : R) t)
        = ((LinearMap.mulLeft R s).rTensor S) 0 := by
      rw [LinearMap.rTensor_tmul, map_zero, LinearMap.mulLeft_apply, mul_one]
      exact e1
    have h1 : TensorProduct.tmul R (1 : R) t = (0 : TensorProduct R R S) := hinj e0
    have h2 : (TensorProduct.lid R S) (TensorProduct.tmul R (1 : R) t)
        = (TensorProduct.lid R S) 0 := by rw [h1]
    rwa [TensorProduct.lid_tmul, one_smul, map_zero] at h2
  exact mem_nonZeroDivisors_iff.mpr
    ⟨key, fun t ht => key t (by rw [mul_comm]; exact ht)⟩

private theorem exists_affineOpen_mem_le_consolidated208 {Y : Scheme.{u}} (y : Y) (W : Y.Opens) (hy : y ∈ W) :
    ∃ V : Y.affineOpens, y ∈ (V : Y.Opens) ∧ (V : Y.Opens) ≤ W := by
  obtain ⟨V, hVmem, hyV, hVle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hy
  exact ⟨⟨V, hVmem⟩, hyV, hVle⟩

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.comap_of_flat {X Y : Scheme.{u}} {D : X.IdealSheafData}
    (hD : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor D) (f : Y ⟶ X) [Flat f] :
    FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor (D.comap f) := by
  unfold FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor at hD ⊢
  intro y
  obtain ⟨U, s, hxU, hs, hUs⟩ := hD (f.base y)
  obtain ⟨V, hyV, hVle⟩ :=
    EmbeddedResolution.exists_affineOpen_mem_le_consolidated208 y (f ⁻¹ᵁ (U : X.Opens))
      (show y ∈ f ⁻¹ᵁ (U : X.Opens) from hxU)
  have hU2 : IsAffineOpen (U : X.Opens) := U.2
  have hV2 : IsAffineOpen (V : Y.Opens) := V.2
  have hflat : (Scheme.Hom.appLE f (U : X.Opens) (V : Y.Opens) hVle).hom.Flat := by
    apply AlgebraicGeometry.Scheme.Hom.flat_appLE <;> assumption
  refine ⟨V, (Scheme.Hom.appLE f (U : X.Opens) (V : Y.Opens) hVle).hom s, hyV, ?_, ?_⟩
  · exact _root_.FunctorialResolution.EmbeddedResolution.map_mem_nonZeroDivisors_of_flat_consolidated208 _ hflat hs
  · rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE D f U V hVle, hUs, Ideal.map_span,
      Set.image_singleton]

theorem _root_.FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.pullback_snd_of_flat {X Y B : Scheme.{u}} {π : B ⟶ X}
    {J : X.IdealSheafData} (h : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf π J) (g : Y ⟶ X) [Flat g] :
    FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf (pullback.snd π g) (J.comap g) := by
  have e1 : (J.comap g).comap (pullback.snd π g)
      = (J.comap π).comap (pullback.fst π g) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      pullback.condition]
  refine ⟨?_, ?_⟩
  · rw [e1]
    exact h.1.comap_of_flat (pullback.fst π g)
  · intro W m hm
    have hm' : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor (J.comap (m ≫ g)) := by
      rw [Scheme.IdealSheafData.comap_comp]
      exact hm
    obtain ⟨b, hb, hbuniq⟩ := h.2 W (m ≫ g) hm'
    refine ⟨pullback.lift b m hb, ?_, ?_⟩
    · exact pullback.lift_snd b m hb
    · intro a ha
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst]
        refine hbuniq _ ?_
        show (a ≫ pullback.fst π g) ≫ π = m ≫ g
        rw [Category.assoc, pullback.condition, ← Category.assoc, ha]
      · rw [pullback.lift_snd, ha]

theorem _root_.FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.of_isPullback_of_flat {X Y B P : Scheme.{u}} {π : B ⟶ X}
    {J : X.IdealSheafData} (h : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf π J) (g : Y ⟶ X) [Flat g]
    {p : P ⟶ B} {q : P ⟶ Y} (hsq : IsPullback p q π g) :
    FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf q (J.comap g) := by
  have h3 : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf (pullback.snd π g) (J.comap g) := h.pullback_snd_of_flat g
  have h4 := h3.iso_hom_comp hsq.isoPullback
  rwa [hsq.isoPullback_hom_snd] at h4

theorem _root_.FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.exists_isPullback_of_flat {X Y B B' : Scheme.{u}} {π : B ⟶ X}
    {J : X.IdealSheafData} (h : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf π J) (g : Y ⟶ X) [Flat g]
    {π' : B' ⟶ Y} (h' : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf π' (J.comap g)) :
    ∃ q : B' ⟶ B, q ≫ π = π' ≫ g ∧ IsPullback q π' π g := by
  obtain ⟨e, he⟩ := h'.exists_iso (h.pullback_snd_of_flat g)
  have hc : (e.hom ≫ pullback.fst π g) ≫ π = π' ≫ g := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  exact ⟨e.hom ≫ pullback.fst π g, hc, IsPullback.of_iso_pullback ⟨hc⟩ e rfl he⟩

end
end FunctorialResolution.EmbeddedResolution
end
