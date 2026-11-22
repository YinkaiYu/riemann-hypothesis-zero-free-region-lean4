import Mathlib
import Core5.M07BlowupPullback

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicGeometry
universe u
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardFlatBaseChange
section

open CategoryTheory.Limits


section
variable {A B C D : Scheme.{u}} {a : A ⟶ B} {b : A ⟶ C} {c : B ⟶ D} {d : C ⟶ D} (sq : IsPullback a b c d)
include sq

private theorem flat_of_isPullback_consolidated257 (hd : Flat d) :
    Flat a := by
  have := hd
  have : Flat (pullback.snd d c) := inferInstance
  rw [← sq.flip.isoPullback_hom_snd]
  infer_instance

private theorem isClosedImmersion_of_isPullback_consolidated257 (hd : IsClosedImmersion d) : IsClosedImmersion a := by
  have := hd
  have : IsClosedImmersion (pullback.snd d c) := inferInstance
  rw [← sq.flip.isoPullback_hom_snd]
  infer_instance


end

theorem comp_projectionToBase_of_comp_blowupMorphism {S X : Scheme.{u}} (s : SequenceOfBlowups S) (t : SequenceOfBlowups X)
    (L : ℕ) (j : S ⟶ X) (σ : ∀ i : ℕ, i ≤ L → (s.schemeAt i ⟶ t.schemeAt i))
    (hzero : σ 0 (Nat.zero_le _) ≫ t.isoZero.hom = s.isoZero.hom ≫ j)
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      σ (i + 1) hi ≫ t.transitionMapSucc i = s.transitionMapSucc i ≫ σ i hi.le) :
    ∀ b : ℕ, ∀ hb : b ≤ L, σ b hb ≫ t.projectionToBase b = s.projectionToBase b ≫ j := by
  intro b
  induction b with
  | zero =>
    intro hb
    rw [SequenceOfBlowups.projectionToBase_zero, SequenceOfBlowups.projectionToBase_zero]
    exact hzero
  | succ n ih =>
    intro hb
    have hn : n < L := hb
    have h1 := hstep n hn
    rw [SequenceOfBlowups.projectionToBase_succ, SequenceOfBlowups.projectionToBase_succ, ← Category.assoc, h1,
      Category.assoc, ih hn.le, Category.assoc]

namespace IsPushforwardBlowupSeq

theorem of_flat_isPullback {S X S' X' : Scheme.{u}}
    (j : S ⟶ X) (j' : S' ⟶ X') (g : X' ⟶ X) (p : S' ⟶ S)
    [IsClosedImmersion j] [IsClosedImmersion j'] [Flat g]
    (hsq : IsPullback j' p g j)
    (s : SequenceOfBlowups S) (t : SequenceOfBlowups X) (s' : SequenceOfBlowups S') (t' : SequenceOfBlowups X')
    (hnoeth : ∀ i : ℕ, i ≤ t.length → IsLocallyNoetherian (t.schemeAt i))
    (hnoeth' : ∀ i : ℕ, i ≤ t'.length → IsLocallyNoetherian (t'.schemeAt i))
    (hpush : IsPushforwardBlowupSeq j s t)
    (hs' : IsStrictPullbackBlowupSeq p s' s)
    (ht' : IsStrictPullbackBlowupSeq g t' t) :
    IsPushforwardBlowupSeq j' s' t' := by
  obtain ⟨hlen1, σ, hσci, hσ0, hσstep, hσcen, hσker⟩ := hpush
  obtain ⟨hlen2, τ, hτ0, hτstep, hτcen⟩ := hs'
  obtain ⟨hlen3, ρ, hρ0, hρstep, hρcen⟩ := ht'
  have hA : ∀ i : ℕ, i ≤ s'.length → i ≤ s.length := fun i hi => by omega
  have hB : ∀ i : ℕ, i ≤ s'.length → i ≤ t'.length := fun i hi => by omega
  have Pt := isPullback_projectionToBase_of_isPullback_blowupMorphism g t' t t'.length ρ hρ0 hρstep
  have Ps := isPullback_projectionToBase_of_isPullback_blowupMorphism p s' s s'.length τ hτ0 hτstep
  have hσS := comp_projectionToBase_of_comp_blowupMorphism s t s.length j σ hσ0 hσstep
  have hflatρ : ∀ i : ℕ, ∀ hi : i ≤ t'.length, Flat (ρ i hi) := fun i hi =>
    flat_of_isPullback_consolidated257 (Pt i hi) inferInstance
  have hw : ∀ i : ℕ, ∀ hi : i ≤ s'.length,
      (τ i hi ≫ σ i (hA i hi)) ≫ t.projectionToBase i = (s'.projectionToBase i ≫ j') ≫ g := by
    intro i hi
    rw [Category.assoc, hσS i (hA i hi), ← Category.assoc, (Ps i hi).w, Category.assoc,
      ← hsq.w, Category.assoc]
  obtain ⟨σ', hσ'1, hσ'2⟩ :
      ∃ σ' : ∀ i : ℕ, i ≤ s'.length → (s'.schemeAt i ⟶ t'.schemeAt i),
        (∀ i : ℕ, ∀ hi : i ≤ s'.length,
          σ' i hi ≫ ρ i (hB i hi) = τ i hi ≫ σ i (hA i hi)) ∧
        (∀ i : ℕ, ∀ hi : i ≤ s'.length,
          σ' i hi ≫ t'.projectionToBase i = s'.projectionToBase i ≫ j') :=
    ⟨fun i hi => (Pt i (hB i hi)).lift (τ i hi ≫ σ i (hA i hi)) (s'.projectionToBase i ≫ j') (hw i hi),
      fun i hi => (Pt i (hB i hi)).lift_fst _ _ (hw i hi),
      fun i hi => (Pt i (hB i hi)).lift_snd _ _ (hw i hi)⟩
  have Psq : ∀ i : ℕ, ∀ hi : i ≤ s'.length,
      IsPullback (σ' i hi) (τ i hi) (ρ i (hB i hi)) (σ i (hA i hi)) := by
    intro i hi
    refine IsPullback.of_right ?_ (hσ'1 i hi) (Pt i (hB i hi)).flip
    rw [hσ'2 i hi, hσS i (hA i hi)]
    exact ((Ps i hi).flip).paste_horiz hsq
  have hci' : ∀ i : ℕ, ∀ hi : i ≤ s'.length, IsClosedImmersion (σ' i hi) := fun i hi =>
    isClosedImmersion_of_isPullback_consolidated257 (Psq i hi) (hσci i (hA i hi))
  have hzero' : σ' 0 (Nat.zero_le _) ≫ t'.isoZero.hom = s'.isoZero.hom ≫ j' := by
    have h := hσ'2 0 (Nat.zero_le _)
    rwa [SequenceOfBlowups.projectionToBase_zero, SequenceOfBlowups.projectionToBase_zero] at h
  have hstep' : ∀ i : ℕ, ∀ hi : i < s'.length,
      σ' (i + 1) hi ≫ t'.transitionMapSucc i = s'.transitionMapSucc i ≫ σ' i hi.le := by
    intro i hi
    have hit : i < t'.length := by omega
    have his : i < s.length := by omega
    refine (Pt i (hB i hi.le)).hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [← (hρstep i hit).w, hσ'1 i hi.le, ← Category.assoc, hσ'1 (i + 1) hi,
        Category.assoc, hσstep i his, ← Category.assoc, (hτstep i hi).w, Category.assoc]
    · simp only [Category.assoc]
      rw [← SequenceOfBlowups.projectionToBase_succ, hσ'2 (i + 1) hi, hσ'2 i hi.le,
        SequenceOfBlowups.projectionToBase_succ, Category.assoc]
  have hcen' : ∀ i : ℕ, ∀ hi : i < s'.length,
      t'.center i = imageIdealSheaf (σ' i hi.le) (s'.center i) := by
    intro i hi
    have hit : i < t'.length := by omega
    have his : i < s.length := by omega
    have := hσci i (hA i hi.le)
    have : QuasiCompact (σ i (hA i hi.le)) := inferInstance
    have := hflatρ i (hB i hi.le)
    rw [hρcen i hit, hτcen i hi, hσcen i his, ← map_eq_imageIdealSheaf, ← map_eq_imageIdealSheaf]
    exact comap_map_eq_map_comap_of_isPullback (Psq i hi.le).flip (s.center i)
  have hker' : ∀ i : ℕ, ∀ hi : i < s'.length,
      (σ' (i + 1) hi).ker =
        Blowup.strictTransform (t'.transitionMapSucc i) (t'.center i) (σ' i hi.le).ker := by
    intro i hi
    have hit : i < t'.length := by omega
    have his : i < s.length := by omega
    have hitt : i < t.length := by omega
    have := hσci i (hA i hi.le)
    have := hσci (i + 1) (hA (i + 1) hi)
    have := hci' i hi.le
    have := hci' (i + 1) hi
    have := hflatρ i (hB i hi.le)
    have := hflatρ (i + 1) (hB (i + 1) hi)
    have : IsLocallyNoetherian (t.schemeAt (i + 1)) := hnoeth (i + 1) (by omega)
    have : IsLocallyNoetherian (t'.schemeAt (i + 1)) := hnoeth' (i + 1) (by omega)
    rw [ker_eq_comap_ker_of_isPullback_of_flat (Psq (i + 1) hi).flip,
      ker_eq_comap_ker_of_isPullback_of_flat (Psq i hi.le).flip, hσker i his, hρcen i hit]
    exact comap_strictTransform_of_flat_of_isLocallyNoetherian (t.transitionMapSucc i)
      (ρ i (hB i hi.le)) (t'.transitionMapSucc i) (ρ (i + 1) (hB (i + 1) hi)) (hρstep i hit)
      (t.center i) (σ i (hA i hi.le)).ker (t.isBlowupAlongIdealSheaf_blowupMorphism i hitt)
  have hlen : s'.length = t'.length := by omega
  exact And.intro hlen (Exists.intro σ' ⟨hci', hzero', hstep', hcen', hker'⟩)

end IsPushforwardBlowupSeq

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupSeqComparison
section


section

private theorem range_iso_hom_comp_consolidated212 {X Y Z : Scheme.{u}} (e : X ≅ Y) (g : Y ⟶ Z) :
    Set.range (e.hom ≫ g).base = Set.range g.base := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨e.hom.base x, rfl⟩
  · rintro _ ⟨y, rfl⟩
    refine ⟨e.inv.base y, ?_⟩
    show g.base (e.hom.base (e.inv.base y)) = g.base y
    rw [Scheme.inv_hom_apply]

private theorem comap_hom_comap_inv_consolidated212 {X Y : Scheme.{u}} (e : X ≅ Y) (I : Y.IdealSheafData) :
    (I.comap e.hom).comap e.inv = I := by
  rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id]

section
variable {X : Scheme.{u}}

private theorem mem_support_of_le_consolidated212 {I J : X.IdealSheafData} (h : I ≤ J) (x : ↥X)
    (hx : x ∈ J.support) : x ∈ I.support :=
  Scheme.IdealSheafData.support_antitone h hx

private theorem exists_subschemeι_base_eq_consolidated212 (I : X.IdealSheafData) (x : ↥X)
    (hx : x ∈ I.support) : ∃ z, I.subschemeι.base z = x := by
  have hmem : x ∈ Set.range ⇑I.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι I]
    exact hx
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, hz⟩


end

private theorem exists_pullbackFst_base_eq_consolidated212 {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : ↥X)
    (hx : f.base x ∈ Set.range g.base) : ∃ z, (Limits.pullback.fst f g).base z = x := by
  have h := Scheme.Pullback.range_fst f g
  rw [Set.ext_iff] at h
  exact (h x).mpr hx

private theorem exists_preimage_of_isPullback_consolidated212 {X' X S : Scheme.{u}} {g : X' ⟶ X} {s : S ⟶ X}
    {Q : Scheme.{u}} {p : Q ⟶ S} {q : Q ⟶ X'} (h : IsPullback p q s g) (x : ↥S)
    (hx : s.base x ∈ Set.range g.base) : ∃ y : ↥Q, p.base y = x := by
  have h1 : Set.range p.base = Set.range (Limits.pullback.fst s g).base := by
    rw [← h.isoPullback_hom_fst]
    exact range_iso_hom_comp_consolidated212 h.isoPullback _
  obtain ⟨z, hz⟩ := exists_pullbackFst_base_eq_consolidated212 s g x hx
  have hmem : x ∈ Set.range p.base := by
    rw [h1]
    exact ⟨z, hz⟩
  exact hmem

def BlowupLiftEqOnControlledTransform : Prop :=
  ∀ (X Y S T : Scheme.{u}) (π : Y ⟶ X) (Z : X.IdealSheafData), Blowup.IsBlowupAlongIdealSheaf π Z →
    ∀ f g : S ⟶ X, Z.comap f = Z.comap g →
      ∀ ρ : T ⟶ S, Blowup.IsBlowupAlongIdealSheaf ρ (Z.comap f) →
        ∀ f' g' : T ⟶ Y, f' ≫ π = ρ ≫ f → g' ≫ π = ρ ≫ g →
          ∀ a : S.IdealSheafData, a.subschemeι ≫ f = a.subschemeι ≫ g →
            ∀ c : T.IdealSheafData,
              Blowup.exceptionalIdeal ρ (Z.comap f) * c = a.comap ρ →
              c.subschemeι ≫ f' = c.subschemeι ≫ g'

variable {V P : Scheme.{u}}

structure BlowupSeqLevelIso (C : SequenceOfBlowups V) (B₁ B₂ : SequenceOfBlowups P) (L : ℕ)
    (σ₁ : ∀ i : ℕ, i ≤ L → (C.schemeAt i ⟶ B₁.schemeAt i))
    (σ₂ : ∀ i : ℕ, i ≤ L → (C.schemeAt i ⟶ B₂.schemeAt i))
    (a : ∀ i : ℕ, (C.schemeAt i).IdealSheafData) (i : ℕ) where
  iso : B₁.schemeAt i ≅ B₂.schemeAt i
  compat : ∀ hi : i ≤ L,
    (a i).subschemeι ≫ σ₁ i hi = (a i).subschemeι ≫ σ₂ i hi ≫ iso.inv

structure BlowupSeqComparison (f g : V ⟶ P) (C : SequenceOfBlowups V) (B₁ B₂ : SequenceOfBlowups P) (L : ℕ)
    (σ₁ : ∀ i : ℕ, i ≤ L → (C.schemeAt i ⟶ B₁.schemeAt i))
    (σ₂ : ∀ i : ℕ, i ≤ L → (C.schemeAt i ⟶ B₂.schemeAt i))
    (a : ∀ i : ℕ, (C.schemeAt i).IdealSheafData) : Prop where
  zero_ideal :
    (a 0).subschemeι ≫ C.isoZero.hom ≫ f = (a 0).subschemeι ≫ C.isoZero.hom ≫ g
  isBlowup_B₁ : ∀ i : ℕ, i < L → Blowup.IsBlowupAlongIdealSheaf (B₁.transitionMapSucc i) (B₁.center i)
  isBlowup_B₂ : ∀ i : ℕ, i < L → Blowup.IsBlowupAlongIdealSheaf (B₂.transitionMapSucc i) (B₂.center i)
  isBlowup_C : ∀ i : ℕ, i < L → Blowup.IsBlowupAlongIdealSheaf (C.transitionMapSucc i) (C.center i)
  ideal_succ : ∀ i : ℕ, i < L →
    Blowup.exceptionalIdeal (C.transitionMapSucc i) (C.center i) * a (i + 1) = (a i).comap (C.transitionMapSucc i)
  ideal_le_center : ∀ i : ℕ, i < L → a i ≤ C.center i
  center_C₁ : ∀ i : ℕ, ∀ hi : i < L, C.center i = (B₁.center i).comap (σ₁ i hi.le)
  center_C₂ : ∀ i : ℕ, ∀ hi : i < L, C.center i = (B₂.center i).comap (σ₂ i hi.le)
  cover₁ : ∀ i : ℕ, i < L → ∀ x ∈ (B₁.center i).support,
    (B₁.projectionToBase i).base x ∈ Set.range f.base
  cover₂ : ∀ i : ℕ, i < L → ∀ x ∈ (B₂.center i).support,
    (B₂.projectionToBase i).base x ∈ Set.range g.base
  lifting : BlowupLiftEqOnControlledTransform.{u}
  determined₁ : ∀ i : ℕ, i < L → ∀ J : (B₁.schemeAt i).IdealSheafData,
    (B₁.center i).support ≤ J.support → J ≤ B₁.center i
  determined₂ : ∀ i : ℕ, i < L → ∀ J : (B₂.schemeAt i).IdealSheafData,
    (B₂.center i).support ≤ J.support → J ≤ B₂.center i
  pullback₁ : ∀ i : ℕ, ∀ hi : i < L,
    IsPullback (σ₁ (i + 1) hi) (C.transitionMapSucc i) (B₁.transitionMapSucc i) (σ₁ i hi.le)
  pullback₂ : ∀ i : ℕ, ∀ hi : i < L,
    IsPullback (σ₂ (i + 1) hi) (C.transitionMapSucc i) (B₂.transitionMapSucc i) (σ₂ i hi.le)
  zero₁ : σ₁ 0 (Nat.zero_le _) ≫ B₁.isoZero.hom = C.isoZero.hom ≫ f
  zero₂ : σ₂ 0 (Nat.zero_le _) ≫ B₂.isoZero.hom = C.isoZero.hom ≫ g

variable {f g : V ⟶ P} {C : SequenceOfBlowups V} {B₁ B₂ : SequenceOfBlowups P} {L : ℕ}
  {σ₁ : ∀ i : ℕ, i ≤ L → (C.schemeAt i ⟶ B₁.schemeAt i)}
  {σ₂ : ∀ i : ℕ, i ≤ L → (C.schemeAt i ⟶ B₂.schemeAt i)}
  {a : ∀ i : ℕ, (C.schemeAt i).IdealSheafData}

section
variable (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a)
include hd

theorem BlowupSeqComparison.exists_preimage_of_mem_center_support_left (i : ℕ) (hi : i < L) (x : ↥(B₁.schemeAt i)) (hx : x ∈ (B₁.center i).support) :
    ∃ y : ↥(C.schemeAt i), (σ₁ i hi.le).base y = x := by
  have hsq : IsPullback (σ₁ i hi.le) (C.projectionToBase i) (B₁.projectionToBase i) f :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism f C B₁ L σ₁ hd.zero₁ hd.pullback₁ i hi.le
  exact exists_preimage_of_isPullback_consolidated212 hsq x (hd.cover₁ i hi x hx)

theorem BlowupSeqComparison.exists_preimage_of_mem_center_support_right (i : ℕ) (hi : i < L) (x : ↥(B₂.schemeAt i)) (hx : x ∈ (B₂.center i).support) :
    ∃ y : ↥(C.schemeAt i), (σ₂ i hi.le).base y = x := by
  have hsq : IsPullback (σ₂ i hi.le) (C.projectionToBase i) (B₂.projectionToBase i) g :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism g C B₂ L σ₂ hd.zero₂ hd.pullback₂ i hi.le
  exact exists_preimage_of_isPullback_consolidated212 hsq x (hd.cover₂ i hi x hx)

theorem subschemeι_comp_zero_eq_comp_isoObjZero_inv :
    ∀ hi : (0 : ℕ) ≤ L,
      (a 0).subschemeι ≫ σ₁ 0 hi =
        (a 0).subschemeι ≫ σ₂ 0 hi ≫ (B₁.isoZero ≪≫ B₂.isoZero.symm).inv := by
  intro hi
  have h1 : σ₁ 0 hi ≫ B₁.isoZero.hom = C.isoZero.hom ≫ f := hd.zero₁
  have h2 : σ₂ 0 hi ≫ B₂.isoZero.hom = C.isoZero.hom ≫ g := hd.zero₂
  rw [← cancel_mono B₁.isoZero.hom]
  simp only [Category.assoc, Iso.trans_inv, Iso.symm_inv, Iso.inv_hom_id, Category.comp_id]
  rw [h1, h2]
  exact hd.zero_ideal


end

def blowupSeqLevelIsoZero (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a) :
    BlowupSeqLevelIso C B₁ B₂ L σ₁ σ₂ a 0 where
  iso := B₁.isoZero ≪≫ B₂.isoZero.symm
  compat := subschemeι_comp_zero_eq_comp_isoObjZero_inv hd

theorem blowupSeqLevelIsoZero_iso_hom_comp_isoObjZero (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a) :
    (blowupSeqLevelIsoZero hd).iso.hom ≫ B₂.isoZero.hom = B₁.isoZero.hom := by
  show (B₁.isoZero ≪≫ B₂.isoZero.symm).hom ≫ B₂.isoZero.hom = B₁.isoZero.hom
  simp

section
variable (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a) {i : ℕ} (hi : i < L) (st : BlowupSeqLevelIso C B₁ B₂ L σ₁ σ₂ a i)
include hd hi

theorem BlowupSeqLevelIso.center_comap_iso_hom_eq :
    (B₂.center i).comap st.iso.hom = B₁.center i := by
  have hkey : ∀ y : ↥(C.schemeAt i), y ∈ (C.center i).support →
      (σ₁ i hi.le).base y = st.iso.inv.base ((σ₂ i hi.le).base y) := by
    intro y hy
    have hy2 : y ∈ (a i).support := mem_support_of_le_consolidated212 (hd.ideal_le_center i hi) y hy
    obtain ⟨z, hz⟩ := exists_subschemeι_base_eq_consolidated212 (a i) y hy2
    have e1 : ((a i).subschemeι ≫ σ₁ i hi.le).base z
        = ((a i).subschemeι ≫ σ₂ i hi.le ≫ st.iso.inv).base z := by
      rw [st.compat hi.le]
    have e2 : (σ₁ i hi.le).base ((a i).subschemeι.base z)
        = st.iso.inv.base ((σ₂ i hi.le).base ((a i).subschemeι.base z)) := e1
    rw [hz] at e2
    exact e2
  have h1 : (B₁.center i).support ≤ ((B₂.center i).comap st.iso.hom).support := by
    intro x hx
    obtain ⟨y, hy⟩ := hd.exists_preimage_of_mem_center_support_left i hi x hx
    have hyc : y ∈ (C.center i).support := by
      rw [hd.center_C₁ i hi, Scheme.IdealSheafData.mem_support_comap, hy]
      exact hx
    have hy2 : (σ₂ i hi.le).base y ∈ (B₂.center i).support := by
      have := hyc
      rw [hd.center_C₂ i hi, Scheme.IdealSheafData.mem_support_comap] at this
      exact this
    rw [Scheme.IdealSheafData.mem_support_comap]
    have hx' : x = st.iso.inv.base ((σ₂ i hi.le).base y) := by
      rw [← hy]
      exact hkey y hyc
    rw [hx', Scheme.inv_hom_apply]
    exact hy2
  have h2 : (B₂.center i).support ≤ ((B₁.center i).comap st.iso.inv).support := by
    intro x hx
    obtain ⟨y, hy⟩ := hd.exists_preimage_of_mem_center_support_right i hi x hx
    have hyc : y ∈ (C.center i).support := by
      rw [hd.center_C₂ i hi, Scheme.IdealSheafData.mem_support_comap, hy]
      exact hx
    have hy1 : (σ₁ i hi.le).base y ∈ (B₁.center i).support := by
      have := hyc
      rw [hd.center_C₁ i hi, Scheme.IdealSheafData.mem_support_comap] at this
      exact this
    rw [Scheme.IdealSheafData.mem_support_comap, ← hy, ← hkey y hyc]
    exact hy1
  have hle1 : (B₂.center i).comap st.iso.hom ≤ B₁.center i :=
    hd.determined₁ i hi _ h1
  have hle2 : (B₁.center i).comap st.iso.inv ≤ B₂.center i :=
    hd.determined₂ i hi _ h2
  have hle3 : B₁.center i ≤ (B₂.center i).comap st.iso.hom := by
    have hmono : ((B₁.center i).comap st.iso.inv).comap st.iso.hom
        ≤ (B₂.center i).comap st.iso.hom :=
      Scheme.IdealSheafData.comap_mono st.iso.hom hle2
    rwa [← Scheme.IdealSheafData.comap_comp, st.iso.hom_inv_id,
      Scheme.IdealSheafData.comap_id] at hmono
  exact le_antisymm hle1 hle3

theorem BlowupSeqLevelIso.exists_iso_succ_comp_blowupMorphism :
    ∃ e : B₁.schemeAt (i + 1) ≅ B₂.schemeAt (i + 1),
      e.hom ≫ B₂.transitionMapSucc i ≫ st.iso.inv = B₁.transitionMapSucc i := by
  have h2 : Blowup.IsBlowupAlongIdealSheaf (B₂.transitionMapSucc i ≫ st.iso.symm.hom)
      ((B₂.center i).comap st.iso.symm.inv) :=
    (hd.isBlowup_B₂ i hi).comp_iso_hom st.iso.symm
  rw [Iso.symm_hom, Iso.symm_inv, BlowupSeqLevelIso.center_comap_iso_hom_eq hd hi st] at h2
  exact (hd.isBlowup_B₁ i hi).exists_iso h2


end

theorem BlowupSeqLevelIso.hom_comp_blowupMorphism_eq_comp_iso_hom {i : ℕ} (st : BlowupSeqLevelIso C B₁ B₂ L σ₁ σ₂ a i)
    (e : B₁.schemeAt (i + 1) ≅ B₂.schemeAt (i + 1))
    (he : e.hom ≫ B₂.transitionMapSucc i ≫ st.iso.inv = B₁.transitionMapSucc i) :
    e.hom ≫ B₂.transitionMapSucc i = B₁.transitionMapSucc i ≫ st.iso.hom := by
  rw [← he]
  simp

def BlowupSeqLevelIso.isoSucc (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a)
    {i : ℕ} (hi : i < L) (st : BlowupSeqLevelIso C B₁ B₂ L σ₁ σ₂ a i) :
    B₁.schemeAt (i + 1) ≅ B₂.schemeAt (i + 1) :=
  (BlowupSeqLevelIso.exists_iso_succ_comp_blowupMorphism hd hi st).choose

section
variable (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a) {i : ℕ} (hi : i < L) (st : BlowupSeqLevelIso C B₁ B₂ L σ₁ σ₂ a i)

theorem BlowupSeqLevelIso.isoSucc_hom_comp_blowupMorphism :
    (BlowupSeqLevelIso.isoSucc hd hi st).hom ≫ B₂.transitionMapSucc i ≫ st.iso.inv = B₁.transitionMapSucc i :=
  (BlowupSeqLevelIso.exists_iso_succ_comp_blowupMorphism hd hi st).choose_spec

theorem BlowupSeqLevelIso.subschemeι_comp_eq_comp_isoSucc_inv :
    ∀ hj : i + 1 ≤ L,
      (a (i + 1)).subschemeι ≫ σ₁ (i + 1) hj =
        (a (i + 1)).subschemeι ≫ σ₂ (i + 1) hj ≫ (BlowupSeqLevelIso.isoSucc hd hi st).inv := by
  intro hj
  have hcen1 : C.center i = (B₁.center i).comap (σ₁ i hi.le) := hd.center_C₁ i hi
  have hinv : (B₁.center i).comap st.iso.inv = B₂.center i := by
    rw [← BlowupSeqLevelIso.center_comap_iso_hom_eq hd hi st, comap_hom_comap_inv_consolidated212]
  have hcen2 : (B₁.center i).comap (σ₂ i hi.le ≫ st.iso.inv) = C.center i := by
    rw [Scheme.IdealSheafData.comap_comp, hinv, ← hd.center_C₂ i hi]
  have hZeq : (B₁.center i).comap (σ₁ i hi.le)
      = (B₁.center i).comap (σ₂ i hi.le ≫ st.iso.inv) := by
    rw [← hcen1, hcen2]
  have hρ : Blowup.IsBlowupAlongIdealSheaf (C.transitionMapSucc i) ((B₁.center i).comap (σ₁ i hi.le)) := by
    rw [← hcen1]
    exact hd.isBlowup_C i hi
  have hf' : σ₁ (i + 1) hj ≫ B₁.transitionMapSucc i = C.transitionMapSucc i ≫ σ₁ i hi.le :=
    (hd.pullback₁ i hi).w
  have hspec := BlowupSeqLevelIso.isoSucc_hom_comp_blowupMorphism hd hi st
  have hw2 : σ₂ (i + 1) hj ≫ B₂.transitionMapSucc i = C.transitionMapSucc i ≫ σ₂ i hi.le :=
    (hd.pullback₂ i hi).w
  have hg' : (σ₂ (i + 1) hj ≫ (BlowupSeqLevelIso.isoSucc hd hi st).inv) ≫ B₁.transitionMapSucc i
      = C.transitionMapSucc i ≫ σ₂ i hi.le ≫ st.iso.inv := by
    calc (σ₂ (i + 1) hj ≫ (BlowupSeqLevelIso.isoSucc hd hi st).inv) ≫ B₁.transitionMapSucc i
        = σ₂ (i + 1) hj ≫ (BlowupSeqLevelIso.isoSucc hd hi st).inv ≫ B₁.transitionMapSucc i := by
          rw [Category.assoc]
      _ = σ₂ (i + 1) hj ≫ B₂.transitionMapSucc i ≫ st.iso.inv := by
          rw [← hspec]
          simp
      _ = (σ₂ (i + 1) hj ≫ B₂.transitionMapSucc i) ≫ st.iso.inv := by rw [Category.assoc]
      _ = C.transitionMapSucc i ≫ σ₂ i hi.le ≫ st.iso.inv := by rw [hw2, Category.assoc]
  have hc : Blowup.exceptionalIdeal (C.transitionMapSucc i) ((B₁.center i).comap (σ₁ i hi.le)) * a (i + 1)
      = (a i).comap (C.transitionMapSucc i) := by
    rw [← hcen1]
    exact hd.ideal_succ i hi
  exact hd.lifting (B₁.schemeAt i) (B₁.schemeAt (i + 1)) (C.schemeAt i) (C.schemeAt (i + 1)) (B₁.transitionMapSucc i)
    (B₁.center i) (hd.isBlowup_B₁ i hi) (σ₁ i hi.le) (σ₂ i hi.le ≫ st.iso.inv) hZeq
    (C.transitionMapSucc i) hρ (σ₁ (i + 1) hj)
    (σ₂ (i + 1) hj ≫ (BlowupSeqLevelIso.isoSucc hd hi st).inv) hf' hg' (a i) (st.compat hi.le)
    (a (i + 1)) hc


end

def BlowupSeqLevelIso.succ (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a)
    {i : ℕ} (hi : i < L) (st : BlowupSeqLevelIso C B₁ B₂ L σ₁ σ₂ a i) :
    BlowupSeqLevelIso C B₁ B₂ L σ₁ σ₂ a (i + 1) where
  iso := BlowupSeqLevelIso.isoSucc hd hi st
  compat := BlowupSeqLevelIso.subschemeι_comp_eq_comp_isoSucc_inv hd hi st

private def blowupSeqLevelIsoOfLE_consolidated212 (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a) :
    ∀ i : ℕ, i ≤ L → BlowupSeqLevelIso C B₁ B₂ L σ₁ σ₂ a i
  | 0, _ => blowupSeqLevelIsoZero hd
  | (i + 1), h =>
      BlowupSeqLevelIso.succ hd (Nat.lt_of_succ_le h) (blowupSeqLevelIsoOfLE_consolidated212 hd i (Nat.le_of_succ_le h))

theorem SequenceOfBlowups.isomorphic_of_isStrictPullback_same_source (B B' : SequenceOfBlowups P)
    {φ ψ : V ⟶ P} {D : SequenceOfBlowups V}
    (hlift : BlowupLiftEqOnControlledTransform.{u})
    (h₁ : IsStrictPullbackBlowupSeq φ D B) (h₂ : IsStrictPullbackBlowupSeq ψ D B')
    (hcov₁ : ∀ i : ℕ, i < B.length → ∀ x ∈ (B.center i).support,
      (B.projectionToBase i).base x ∈ Set.range φ.base)
    (hcov₂ : ∀ i : ℕ, i < B'.length → ∀ x ∈ (B'.center i).support,
      (B'.projectionToBase i).base x ∈ Set.range ψ.base)
    (hdet₁ : ∀ i : ℕ, i < B.length → ∀ J : (B.schemeAt i).IdealSheafData,
      (B.center i).support ≤ J.support → J ≤ B.center i)
    (hdet₂ : ∀ i : ℕ, i < B'.length → ∀ J : (B'.schemeAt i).IdealSheafData,
      (B'.center i).support ≤ J.support → J ≤ B'.center i)
    (b : ∀ i : ℕ, (D.schemeAt i).IdealSheafData)
    (hzero : (b 0).subschemeι ≫ D.isoZero.hom ≫ φ = (b 0).subschemeι ≫ D.isoZero.hom ≫ ψ)
    (hsucc : ∀ i : ℕ, i < D.length →
      Blowup.exceptionalIdeal (D.transitionMapSucc i) (D.center i) * b (i + 1) = (b i).comap (D.transitionMapSucc i))
    (hle : ∀ i : ℕ, i < D.length → b i ≤ D.center i) :
    B.Isomorphic B' := by
  unfold IsStrictPullbackBlowupSeq at h₁ h₂
  obtain ⟨hlen1, s₁, hz1, hpb1, hc1⟩ := h₁
  obtain ⟨hlen2, s₂, hz2, hpb2, hc2⟩ := h₂
  have hd : BlowupSeqComparison φ ψ D B B' D.length s₁ s₂ b :=
    { zero_ideal := hzero
      isBlowup_B₁ := fun i hi => B.isBlowupAlongIdealSheaf_blowupMorphism i (by rw [← hlen1]; exact hi)
      isBlowup_B₂ := fun i hi => B'.isBlowupAlongIdealSheaf_blowupMorphism i (by rw [← hlen2]; exact hi)
      isBlowup_C := fun i hi => D.isBlowupAlongIdealSheaf_blowupMorphism i hi
      ideal_succ := hsucc
      ideal_le_center := hle
      center_C₁ := fun i hi => hc1 i hi
      center_C₂ := fun i hi => hc2 i hi
      cover₁ := fun i hi => hcov₁ i (by rw [← hlen1]; exact hi)
      cover₂ := fun i hi => hcov₂ i (by rw [← hlen2]; exact hi)
      lifting := hlift
      determined₁ := fun i hi => hdet₁ i (by rw [← hlen1]; exact hi)
      determined₂ := fun i hi => hdet₂ i (by rw [← hlen2]; exact hi)
      pullback₁ := hpb1
      pullback₂ := hpb2
      zero₁ := hz1
      zero₂ := hz2 }
  unfold SequenceOfBlowups.Isomorphic
  refine ⟨hlen1.symm.trans hlen2,
    fun i hi => (blowupSeqLevelIsoOfLE_consolidated212 hd i (le_of_le_of_eq hi hlen1.symm)).iso, ?_, ?_, ?_⟩
  · exact blowupSeqLevelIsoZero_iso_hom_comp_isoObjZero hd
  · intro i hi
    have hiD : i < D.length := by rw [hlen1]; exact hi
    exact BlowupSeqLevelIso.hom_comp_blowupMorphism_eq_comp_iso_hom (blowupSeqLevelIsoOfLE_consolidated212 hd i hiD.le)
      (BlowupSeqLevelIso.isoSucc hd hiD (blowupSeqLevelIsoOfLE_consolidated212 hd i hiD.le))
      (BlowupSeqLevelIso.isoSucc_hom_comp_blowupMorphism hd hiD (blowupSeqLevelIsoOfLE_consolidated212 hd i hiD.le))
  · intro i hi
    have hiD : i < D.length := by rw [hlen1]; exact hi
    exact BlowupSeqLevelIso.center_comap_iso_hom_eq hd hiD (blowupSeqLevelIsoOfLE_consolidated212 hd i hiD.le)


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupLiftCongruence
section

open TopologicalSpace

section

section
variable {X : Scheme.{u}}

private theorem mul_le_right_consolidated230 (I J : X.IdealSheafData) :
    I * J ≤ J := by
  rw [Scheme.IdealSheafData.le_def]
  intro V
  rw [Scheme.IdealSheafData.ideal_mul]
  exact Ideal.mul_le_inf.trans inf_le_right

private theorem eq_of_comp_ι_eq_consolidated230 (U : X.Opens) {W : Scheme.{u}}
    {a b : W ⟶ U.toScheme} (h : a ≫ U.ι = b ≫ U.ι) : a = b := by
  have : Mono U.ι := inferInstance
  exact (cancel_mono U.ι).mp h


end

private theorem hom_ext_of_comp_ι_eq_of_opens_cover_consolidated230 {X Y : Scheme.{u}} {ι : Type u} (W : ι → X.Opens)
    (hW : ∀ x : ↥X, ∃ i, x ∈ W i) (a b : X ⟶ Y)
    (h : ∀ i, (W i).ι ≫ a = (W i).ι ≫ b) : a = b := by
  refine (Scheme.Cover.mkOfCovers ι (fun i => (W i).toScheme) (fun i => (W i).ι) ?_ ?_).hom_ext
    a b ?_
  · intro x
    obtain ⟨i, hi⟩ := hW x
    have hx : x ∈ Set.range ⇑(W i).ι := by
      rw [Scheme.Opens.range_ι]
      exact hi
    obtain ⟨y, hy⟩ := hx
    exact ⟨i, y, hy⟩
  · intro i
    infer_instance
  · intro i
    exact h i

private theorem exists_isoSpec_of_isAffineOpen_consolidated230 {P : Scheme.{u}} {U : P.Opens}
    (hU : IsAffineOpen U) :
    ∃ (R : Type u) (_ : CommRing R), Nonempty (U.toScheme ≅ Spec (CommRingCat.of R)) :=
  ⟨↥Γ(P, U), inferInstance, ⟨hU.isoSpec⟩⟩

theorem comap_mul_of_isOpenImmersion {X U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f]
    (I J : X.IdealSheafData) :
    (I * J).comap f = I.comap f * J.comap f := by
  refine Scheme.IdealSheafData.ext (funext fun V => ?_)
  have hV : IsAffineOpen (f ''ᵁ (V : U.Opens)) := V.2.image_of_isOpenImmersion f
  have he : (V : U.Opens) ≤ f ⁻¹ᵁ (f ''ᵁ (V : U.Opens)) := by
    simp [Scheme.Hom.preimage_image_eq]
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I f ⟨_, hV⟩ V he,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE J f ⟨_, hV⟩ V he,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE (I * J) f ⟨_, hV⟩ V he]
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  rw [Ideal.map_mul]

theorem exists_specIdealSheaf_eq (R : Type u) [CommRing R]
    (I : (Spec (CommRingCat.of R)).IdealSheafData) :
    ∃ J : Ideal R, Blowup.specIdealSheaf J = I := by
  refine ⟨Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    (I.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩), ?_⟩
  have h := (Scheme.IdealSheafData.equivOfIsAffine
      (X := Spec (CommRingCat.of R))).symm_apply_apply I
  rw [Scheme.IdealSheafData.equivOfIsAffine_apply,
    Scheme.IdealSheafData.equivOfIsAffine_symm_apply] at h
  rw [Blowup.specIdealSheaf_eq_ofIdealTop, Ideal.map_map, ← CommRingCat.hom_comp,
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id, CommRingCat.hom_id, Ideal.map_id]
  exact h

theorem subschemeι_comap_comp_eq_of_subschemeι_comp_eq {X Y P : Scheme.{u}} (f : X ⟶ Y) (u v : Y ⟶ P)
    (𝔟 : Y.IdealSheafData) (hagree : 𝔟.subschemeι ≫ u = 𝔟.subschemeι ≫ v) :
    (𝔟.comap f).subschemeι ≫ f ≫ u = (𝔟.comap f).subschemeι ≫ f ≫ v := by
  obtain ⟨t, ht⟩ : ∃ t : (𝔟.comap f).subscheme ⟶ 𝔟.subscheme,
      (𝔟.comap f).subschemeι ≫ f = t ≫ 𝔟.subschemeι :=
    ⟨(𝔟.comapIso f).hom ≫ Limits.pullback.snd f 𝔟.subschemeι, by
      rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc,
        Scheme.IdealSheafData.comapIso_hom_fst]⟩
  calc (𝔟.comap f).subschemeι ≫ f ≫ u
      = t ≫ 𝔟.subschemeι ≫ u := by rw [← Category.assoc, ht, Category.assoc]
    _ = t ≫ 𝔟.subschemeι ≫ v := by rw [hagree]
    _ = (𝔟.comap f).subschemeι ≫ f ≫ v := by rw [← Category.assoc, ← ht, Category.assoc]

theorem subschemeι_comp_eq_of_mul_comap {V V₁ P : Scheme.{u}} (f : V₁ ⟶ V) (u v : V ⟶ P)
    (𝔟 : V.IdealSheafData) (hagree : 𝔟.subschemeι ≫ u = 𝔟.subschemeι ≫ v)
    (e 𝔟₁ : V₁.IdealSheafData) (hmul : e * 𝔟₁ = 𝔟.comap f) :
    𝔟₁.subschemeι ≫ f ≫ u = 𝔟₁.subschemeι ≫ f ≫ v := by
  have hle : 𝔟.comap f ≤ 𝔟₁ := by
    rw [← hmul]
    exact mul_le_right_consolidated230 e 𝔟₁
  obtain ⟨t, ht⟩ : ∃ t : 𝔟₁.subscheme ⟶ (𝔟.comap f).subscheme,
      t ≫ (𝔟.comap f).subschemeι = 𝔟₁.subschemeι :=
    ⟨Scheme.IdealSheafData.inclusion hle, Scheme.IdealSheafData.inclusion_subschemeι hle⟩
  have h3 := subschemeι_comap_comp_eq_of_subschemeι_comp_eq f u v 𝔟 hagree
  calc 𝔟₁.subschemeι ≫ f ≫ u
      = (t ≫ (𝔟.comap f).subschemeι) ≫ f ≫ u := by rw [ht]
    _ = t ≫ ((𝔟.comap f).subschemeι ≫ f ≫ u) := by rw [Category.assoc]
    _ = t ≫ ((𝔟.comap f).subschemeι ≫ f ≫ v) := by rw [h3]
    _ = (t ≫ (𝔟.comap f).subschemeι) ≫ f ≫ v := by rw [Category.assoc]
    _ = 𝔟₁.subschemeι ≫ f ≫ v := by rw [ht]

theorem subschemeι_comp_eq_of_blowup_lifts_spec {R : Type u} [CommRing R] {B W : Scheme.{u}}
    (p : B ⟶ Spec (CommRingCat.of R)) (J : (Spec (CommRingCat.of R)).IdealSheafData)
    (hp : Blowup.IsBlowupAlongIdealSheaf p J) (ρ ρ' : W ⟶ Spec (CommRingCat.of R)) (𝔞 𝔟₁ : W.IdealSheafData)
    (hagree : 𝔞.subschemeι ≫ ρ = 𝔞.subschemeι ≫ ρ')
    (hpull : J.comap ρ = J.comap ρ')
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (J.comap ρ))
    (hfac : J.comap ρ * 𝔟₁ = 𝔞)
    (h h' : W ⟶ B) (hh : h ≫ p = ρ) (hh' : h' ≫ p = ρ') :
    𝔟₁.subschemeι ≫ h = 𝔟₁.subschemeι ≫ h' := by
  obtain ⟨I, rfl⟩ := exists_specIdealSheaf_eq R J
  have hq : Blowup.IsBlowupAlongIdealSheaf (Blowup.AffineBlowup.toSpec I) (Blowup.specIdealSheaf I) := Blowup.isBlowupAlongIdealSheaf_affineBlowup_toSpec I
  obtain ⟨β, hβ⟩ := hq.exists_lift p hp.1
  obtain ⟨α, hα⟩ := hp.exists_lift (Blowup.AffineBlowup.toSpec I) hq.1
  have hβα : β ≫ α = 𝟙 B := by
    refine hp.hom_ext hp.1 ?_ ?_
    · rw [Category.assoc, hα, hβ]
    · rw [Category.id_comp]
  have key := subschemeι_comp_eq_of_affineBlowup_lifts I ρ ρ' 𝔞 𝔟₁ (h ≫ β) (h' ≫ β) hagree hpull hcart hfac
    (by rw [Category.assoc, hβ, hh]) (by rw [Category.assoc, hβ, hh'])
  have hfin := congrArg (fun m => m ≫ α) key
  simp only [Category.assoc, hβα, Category.comp_id] at hfin
  exact hfin

theorem subschemeι_comap_ι_comp_eq_of_blowup_lifts_affine {P P₁ V V₁ : Scheme.{u}} (π : P₁ ⟶ P)
    (Z : P.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (ψ ψ' : V ⟶ P)
    (hZ : Z.comap ψ = Z.comap ψ') (ρ : V₁ ⟶ V)
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor ((Z.comap ψ).comap ρ))
    (ψ₁ ψ'₁ : V₁ ⟶ P₁) (hψ₁ : ψ₁ ≫ π = ρ ≫ ψ) (hψ'₁ : ψ'₁ ≫ π = ρ ≫ ψ')
    (𝔟 : V.IdealSheafData) (hagree : 𝔟.subschemeι ≫ ψ = 𝔟.subschemeι ≫ ψ')
    (𝔟₁ : V₁.IdealSheafData) (hfac : (Z.comap ψ).comap ρ * 𝔟₁ = 𝔟.comap ρ)
    (U : P.Opens) (hU : IsAffineOpen U) (O : V₁.Opens)
    (hO : O ≤ (Opens.map (ρ ≫ ψ).base).obj U)
    (hO' : O ≤ (Opens.map (ρ ≫ ψ').base).obj U) :
    (𝔟₁.comap O.ι).subschemeι ≫ O.ι ≫ ψ₁ = (𝔟₁.comap O.ι).subschemeι ≫ O.ι ≫ ψ'₁ := by
  obtain ⟨R, hR, ⟨e⟩⟩ := exists_isoSpec_of_isAffineOpen_consolidated230 hU
  let _ : CommRing R := hR
  have hres : (ρ ≫ ψ).resLE U O hO ≫ U.ι = O.ι ≫ (ρ ≫ ψ) := by
    rw [Scheme.Hom.resLE_comp_ι]
  have hres' : (ρ ≫ ψ').resLE U O hO' ≫ U.ι = O.ι ≫ (ρ ≫ ψ') := by
    rw [Scheme.Hom.resLE_comp_ι]
  have hπS : Blowup.IsBlowupAlongIdealSheaf (Limits.pullback.snd π U.ι ≫ e.hom) ((Z.comap U.ι).comap e.inv) :=
    (hπ.pullback_snd_of_isOpenImmersion U.ι).comp_iso_hom e
  have hcalc : ∀ (χ : V ⟶ P) (hχ : O ≤ (Opens.map (ρ ≫ χ).base).obj U),
      ((Z.comap U.ι).comap e.inv).comap ((ρ ≫ χ).resLE U O hχ ≫ e.hom)
        = ((Z.comap χ).comap ρ).comap O.ι := by
    intro χ hχ
    simp only [← Scheme.IdealSheafData.comap_comp]
    congr 1
    simp [Scheme.Hom.resLE_comp_ι]
  have hcart_W : Blowup.IsLocallyGeneratedByNonZeroDivisor (((Z.comap U.ι).comap e.inv).comap
      ((ρ ≫ ψ).resLE U O hO ≫ e.hom)) := by
    rw [hcalc ψ hO]
    exact hcart.comap_of_isOpenImmersion O.ι
  have hpull_W : ((Z.comap U.ι).comap e.inv).comap ((ρ ≫ ψ).resLE U O hO ≫ e.hom)
      = ((Z.comap U.ι).comap e.inv).comap ((ρ ≫ ψ').resLE U O hO' ≫ e.hom) := by
    rw [hcalc ψ hO, hcalc ψ' hO', hZ]
  have hfac_W : ((Z.comap U.ι).comap e.inv).comap ((ρ ≫ ψ).resLE U O hO ≫ e.hom)
      * 𝔟₁.comap O.ι = (𝔟.comap ρ).comap O.ι := by
    rw [hcalc ψ hO, ← comap_mul_of_isOpenImmersion O.ι, hfac]
  have hagree_W : ((𝔟.comap ρ).comap O.ι).subschemeι ≫ ((ρ ≫ ψ).resLE U O hO ≫ e.hom)
      = ((𝔟.comap ρ).comap O.ι).subschemeι ≫ ((ρ ≫ ψ').resLE U O hO' ≫ e.hom) := by
    have step1 := subschemeι_comap_comp_eq_of_subschemeι_comp_eq ρ ψ ψ' 𝔟 hagree
    have step2 := subschemeι_comap_comp_eq_of_subschemeι_comp_eq O.ι (ρ ≫ ψ) (ρ ≫ ψ') (𝔟.comap ρ) step1
    have step3 : (((𝔟.comap ρ).comap O.ι).subschemeι ≫ (ρ ≫ ψ).resLE U O hO) ≫ U.ι
        = (((𝔟.comap ρ).comap O.ι).subschemeι ≫ (ρ ≫ ψ').resLE U O hO') ≫ U.ι := by
      rw [Category.assoc, Category.assoc, hres, hres']
      exact step2
    have step4 := eq_of_comp_ι_eq_consolidated230 U step3
    rw [← Category.assoc, ← Category.assoc, step4]
  have hcond : (O.ι ≫ ψ₁) ≫ π = (ρ ≫ ψ).resLE U O hO ≫ U.ι := by
    rw [hres, Category.assoc, hψ₁]
  have hcond' : (O.ι ≫ ψ'₁) ≫ π = (ρ ≫ ψ').resLE U O hO' ≫ U.ι := by
    rw [hres', Category.assoc, hψ'₁]
  have hh : Limits.pullback.lift (O.ι ≫ ψ₁) ((ρ ≫ ψ).resLE U O hO) hcond
      ≫ (Limits.pullback.snd π U.ι ≫ e.hom) = (ρ ≫ ψ).resLE U O hO ≫ e.hom := by
    rw [← Category.assoc, Limits.pullback.lift_snd]
  have hh' : Limits.pullback.lift (O.ι ≫ ψ'₁) ((ρ ≫ ψ').resLE U O hO') hcond'
      ≫ (Limits.pullback.snd π U.ι ≫ e.hom) = (ρ ≫ ψ').resLE U O hO' ≫ e.hom := by
    rw [← Category.assoc, Limits.pullback.lift_snd]
  have key := subschemeι_comp_eq_of_blowup_lifts_spec (R := R)
    (Limits.pullback.snd π U.ι ≫ e.hom) ((Z.comap U.ι).comap e.inv) hπS
    ((ρ ≫ ψ).resLE U O hO ≫ e.hom) ((ρ ≫ ψ').resLE U O hO' ≫ e.hom)
    ((𝔟.comap ρ).comap O.ι) (𝔟₁.comap O.ι) hagree_W hpull_W hcart_W hfac_W
    (Limits.pullback.lift (O.ι ≫ ψ₁) ((ρ ≫ ψ).resLE U O hO) hcond)
    (Limits.pullback.lift (O.ι ≫ ψ'₁) ((ρ ≫ ψ').resLE U O hO') hcond') hh hh'
  have hfin := congrArg (fun m => m ≫ Limits.pullback.fst π U.ι) key
  simpa only [Category.assoc, Limits.pullback.lift_fst] using hfin

private theorem exists_preimage_subscheme_to_subscheme_comap_consolidated230 {T : Scheme.{u}} (c : T.IdealSheafData)
    (O : T.Opens) :
    ∃ k : (c.subschemeι ⁻¹ᵁ O).toScheme ⟶ (c.comap O.ι).subscheme,
      k ≫ (c.comap O.ι).subschemeι ≫ O.ι = (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι := by
  obtain ⟨s, hs⟩ : ∃ s : Limits.pullback O.ι c.subschemeι ⟶ (c.comap O.ι).subscheme,
      s ≫ (c.comap O.ι).subschemeι = Limits.pullback.fst O.ι c.subschemeι :=
    ⟨(c.comapIso O.ι).inv, Scheme.IdealSheafData.comapIso_inv_subschemeι c O.ι⟩
  have hres : c.subschemeι.resLE O (c.subschemeι ⁻¹ᵁ O) le_rfl ≫ O.ι
      = (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι := Scheme.Hom.resLE_comp_ι _ _
  obtain ⟨k, hk⟩ : ∃ k : (c.subschemeι ⁻¹ᵁ O).toScheme ⟶ Limits.pullback O.ι c.subschemeι,
      k ≫ Limits.pullback.fst O.ι c.subschemeι
        = c.subschemeι.resLE O (c.subschemeι ⁻¹ᵁ O) le_rfl :=
    ⟨Limits.pullback.lift _ _ hres, Limits.pullback.lift_fst _ _ _⟩
  refine ⟨k ≫ s, ?_⟩
  calc (k ≫ s) ≫ (c.comap O.ι).subschemeι ≫ O.ι
      = k ≫ (s ≫ (c.comap O.ι).subschemeι) ≫ O.ι := by simp only [Category.assoc]
    _ = k ≫ Limits.pullback.fst O.ι c.subschemeι ≫ O.ι := by rw [hs]
    _ = (k ≫ Limits.pullback.fst O.ι c.subschemeι) ≫ O.ι := by rw [Category.assoc]
    _ = c.subschemeι.resLE O (c.subschemeι ⁻¹ᵁ O) le_rfl ≫ O.ι := by rw [hk]
    _ = (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι := hres

private theorem preimage_ι_subschemeι_comp_eq_of_comap_ι_consolidated230 {T Y : Scheme.{u}} (c : T.IdealSheafData) (O : T.Opens)
    (f' g' : T ⟶ Y)
    (hEqComap : (c.comap O.ι).subschemeι ≫ O.ι ≫ f' = (c.comap O.ι).subschemeι ≫ O.ι ≫ g') :
    (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι ≫ f'
      = (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι ≫ g' := by
  obtain ⟨k, hk⟩ := exists_preimage_subscheme_to_subscheme_comap_consolidated230 c O
  calc (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι ≫ f'
      = ((c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι) ≫ f' := by rw [Category.assoc]
    _ = (k ≫ (c.comap O.ι).subschemeι ≫ O.ι) ≫ f' := by rw [hk]
    _ = k ≫ ((c.comap O.ι).subschemeι ≫ O.ι ≫ f') := by
        rw [Category.assoc, Category.assoc]
    _ = k ≫ ((c.comap O.ι).subschemeι ≫ O.ι ≫ g') := by rw [hEqComap]
    _ = (k ≫ (c.comap O.ι).subschemeι ≫ O.ι) ≫ g' := by
        rw [Category.assoc, Category.assoc]
    _ = ((c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι) ≫ g' := by rw [hk]
    _ = (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι ≫ g' := by rw [Category.assoc]

theorem blowupLiftEqOnControlledTransform : BlowupLiftEqOnControlledTransform.{u} := by
  intro X Y S T π Z hπ f g hfg ρ hρ f' g' hf' hg' a hagree c hc
  have hEqOnSubscheme : c.subschemeι ≫ ρ ≫ f = c.subschemeι ≫ ρ ≫ g :=
    subschemeι_comp_eq_of_mul_comap ρ f g a hagree ((Z.comap f).comap ρ) c hc
  have main : ∀ x : ↥(c.subscheme), ∃ O : T.Opens, c.subschemeι.base x ∈ O ∧
      (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι ≫ f'
        = (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι ≫ g' := by
    intro x
    have hpt : (ρ ≫ f).base (c.subschemeι.base x)
        = (ρ ≫ g).base (c.subschemeι.base x) := by
      have h := congrArg (fun m : c.subscheme ⟶ X => m.base x) hEqOnSubscheme
      simpa using h
    obtain ⟨U, hxU, hU⟩ := X.exists_isAffineOpen_mem ((ρ ≫ f).base (c.subschemeι.base x))
    refine ⟨(Opens.map (ρ ≫ f).base).obj U ⊓ (Opens.map (ρ ≫ g).base).obj U, ⟨hxU, ?_⟩, ?_⟩
    · show (ρ ≫ g).base (c.subschemeι.base x) ∈ U
      rw [← hpt]
      exact hxU
    · refine preimage_ι_subschemeι_comp_eq_of_comap_ι_consolidated230 c _ f' g' ?_
      exact subschemeι_comap_ι_comp_eq_of_blowup_lifts_affine π Z hπ f g hfg ρ hρ.1 f' g' hf' hg' a hagree
        c hc U hU ((Opens.map (ρ ≫ f).base).obj U ⊓ (Opens.map (ρ ≫ g).base).obj U)
        inf_le_left inf_le_right
  choose Ox hOx hOeq using main
  refine hom_ext_of_comp_ι_eq_of_opens_cover_consolidated230 (fun x : ↥(c.subscheme) => c.subschemeι ⁻¹ᵁ (Ox x)) ?_ _ _ hOeq
  intro y
  exact ⟨y, hOx y⟩


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemoval
section



namespace SequenceOfBlowups

section
variable {X' X : Scheme.{u}} (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (hlen : t.length = s.length) (hcen : ∀ i : ℕ, i < s.length → (t.center i = ⊤ ↔ s.center i = ⊤))
include hlen hcen

private theorem nextNontrivialIndex_le_of_center_eq_top_iff_consolidated153 (a : ℕ) :
    t.nextNontrivialIndex a ≤ s.nextNontrivialIndex a := by
  refine t.nextNontrivialIndex_le (s.le_nextNontrivialIndex a) ?_
  rcases s.center_nextNontrivialIndex_ne_top_or_length_le a with hd | hd
  · by_cases hlt : s.nextNontrivialIndex a < s.length
    · exact Or.inl fun hc => hd ((hcen _ hlt).mp hc)
    · exact Or.inr (by omega)
  · exact Or.inr (by omega)

theorem nextNontrivialIndex_congr (a : ℕ) :
    t.nextNontrivialIndex a = s.nextNontrivialIndex a :=
  le_antisymm (nextNontrivialIndex_le_of_center_eq_top_iff_consolidated153 t s hlen hcen a)
    (nextNontrivialIndex_le_of_center_eq_top_iff_consolidated153 s t hlen.symm (fun i hi => (hcen i (by omega)).symm) a)

theorem nontrivialIndex_congr (j : ℕ) :
    t.nontrivialIndex j = s.nontrivialIndex j := by
  induction j with
  | zero =>
      rw [nontrivialIndex_zero, nontrivialIndex_zero]
      exact nextNontrivialIndex_congr t s hlen hcen 0
  | succ j ih =>
      rw [nontrivialIndex_succ, nontrivialIndex_succ, ih]
      exact nextNontrivialIndex_congr t s hlen hcen _

private theorem lengthWithoutIsoBlowups_le_of_center_eq_top_iff_consolidated153 :
    t.lengthWithoutIsoBlowups ≤ s.lengthWithoutIsoBlowups := by
  by_contra hc
  have hc' : s.lengthWithoutIsoBlowups < t.lengthWithoutIsoBlowups := not_le.mp hc
  have h1 : t.nontrivialIndex s.lengthWithoutIsoBlowups < t.length := t.nontrivialIndex_lt_length hc'
  have h2 : s.nontrivialIndex s.lengthWithoutIsoBlowups = s.length := s.nontrivialIndex_lengthWithoutIsoBlowups
  have h3 := nontrivialIndex_congr t s hlen hcen s.lengthWithoutIsoBlowups
  omega

theorem lengthWithoutIsoBlowups_congr :
    t.lengthWithoutIsoBlowups = s.lengthWithoutIsoBlowups :=
  le_antisymm (lengthWithoutIsoBlowups_le_of_center_eq_top_iff_consolidated153 t s hlen hcen)
    (lengthWithoutIsoBlowups_le_of_center_eq_top_iff_consolidated153 s t hlen.symm (fun i hi => (hcen i (by omega)).symm))


end

section
variable {X : Scheme.{u}} (s : SequenceOfBlowups X)

private theorem transitionMap_eq_eqToHom_consolidated153 {a b : ℕ} (h : a ≤ b)
    (h' : a = b) : s.transitionMap h = eqToHom (congrArg s.schemeAt h'.symm) := by
  subst h'
  rw [s.transitionMap_self h, eqToHom_refl]

private theorem eqToHom_comp_transitionMap_consolidated153 {a b a' b' : ℕ}
    (ha : a = a') (hb : b = b') (h : a ≤ b) (h' : a' ≤ b') :
    eqToHom (congrArg s.schemeAt hb) ≫ s.transitionMap h' = s.transitionMap h ≫ eqToHom (congrArg s.schemeAt ha) := by
  subst ha
  subst hb
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem eqToHom_comp_projectionToBase_consolidated153 {a b : ℕ} (h : a = b) :
    eqToHom (congrArg s.schemeAt h) ≫ s.projectionToBase b = s.projectionToBase a := by
  subst h
  rw [eqToHom_refl, Category.id_comp]

private theorem center_comap_eqToHom_consolidated153 {a b : ℕ} (h : a = b) :
    (s.center b).comap (eqToHom (congrArg s.schemeAt h)) = s.center a := by
  subst h
  simp


end

theorem withoutIsoBlowups_isomorphic_self {X : Scheme.{u}} (t : SequenceOfBlowups X)
    (h : ∀ i : ℕ, i < t.length → t.center i ≠ ⊤) : t.withoutIsoBlowups.Isomorphic t := by
  have hnext : ∀ a : ℕ, t.nextNontrivialIndex a = a := by
    intro a
    refine le_antisymm (t.nextNontrivialIndex_le le_rfl ?_) (t.le_nextNontrivialIndex a)
    by_cases ha : a < t.length
    · exact Or.inl (h a ha)
    · exact Or.inr (by omega)
  have hret : ∀ j : ℕ, t.nontrivialIndex j = j := by
    intro j
    induction j with
    | zero => rw [t.nontrivialIndex_zero, hnext]
    | succ j ih => rw [t.nontrivialIndex_succ, hnext, ih]
  have hplen : t.withoutIsoBlowups.length = t.length := by
    have h2 := t.nontrivialIndex_lengthWithoutIsoBlowups
    rw [hret] at h2
    exact h2
  have h1 : (eqToIso (congrArg t.schemeAt (hret 0))).hom ≫ t.isoZero.hom = t.withoutIsoBlowups.isoZero.hom := by
    rw [t.withoutIsoBlowups_isoObjZero, t.objNontrivialIndexZeroIso_hom, t.projectionToBase_def,
      t.transitionMap_eq_eqToHom_consolidated153 _ (hret 0).symm]
    rfl
  have h2 : ∀ i : ℕ, i < t.withoutIsoBlowups.length →
      (eqToIso (congrArg t.schemeAt (hret (i + 1)))).hom ≫ t.transitionMapSucc i
        = t.withoutIsoBlowups.transitionMapSucc i ≫ (eqToIso (congrArg t.schemeAt (hret i))).hom := by
    intro i _
    rw [t.withoutIsoBlowups_blowupMorphism, t.blowupMorphism_eq_transitionMap]
    exact t.eqToHom_comp_transitionMap_consolidated153 (hret i) (hret (i + 1)) _ _
  have h3 : ∀ i : ℕ, i < t.withoutIsoBlowups.length →
      (t.center i).comap (eqToIso (congrArg t.schemeAt (hret i))).hom = t.withoutIsoBlowups.center i := by
    intro i _
    exact t.center_comap_eqToHom_consolidated153 (hret i)
  unfold SequenceOfBlowups.Isomorphic
  exact ⟨hplen, fun i _ => eqToIso (congrArg t.schemeAt (hret i)), h1, h2, h3⟩

end SequenceOfBlowups

private theorem isPullback_eqToHom_right_consolidated153 {P Y X Z X' Z' : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (hX : X = X') (hZ : Z = Z') {f' : X' ⟶ Z'}
    (hf : eqToHom hX ≫ f' = f ≫ eqToHom hZ) :
    IsPullback (fst ≫ eqToHom hX) snd f' (g ≫ eqToHom hZ) := by
  subst hX
  subst hZ
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hf ⊢
  rw [hf]
  exact h

section
variable {X' X : Scheme.{u}}

private theorem center_eq_comap_comp_eqToHom_consolidated153 (t : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) {a b : ℕ} (hab : a = b) (f : t.schemeAt a ⟶ s.schemeAt a)
    (hf : t.center a = (s.center a).comap f) :
    t.center a = (s.center b).comap (f ≫ eqToHom (congrArg s.schemeAt hab)) := by
  subst hab
  simp only [eqToHom_refl, Category.comp_id]
  exact hf

theorem IsStrictPullbackBlowupSeq.withoutIsoBlowups {g : X' ⟶ X}
    [AlgebraicGeometry.Surjective g] {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) :
    IsStrictPullbackBlowupSeq g t.withoutIsoBlowups s.withoutIsoBlowups := by
  have hiff : ∀ i : ℕ, i < s.length → (t.center i = ⊤ ↔ s.center i = ⊤) :=
    fun i hi => h.center_eq_top_iff i hi
  have hlen : t.length = s.length := h.length_eq
  have hret : ∀ j : ℕ, t.nontrivialIndex j = s.nontrivialIndex j := SequenceOfBlowups.nontrivialIndex_congr t s hlen hiff
  have hplen : t.lengthWithoutIsoBlowups = s.lengthWithoutIsoBlowups := SequenceOfBlowups.lengthWithoutIsoBlowups_congr t s hlen hiff
  unfold IsStrictPullbackBlowupSeq at h ⊢
  obtain ⟨-, σ, hzero, hstep, hcen⟩ := h
  have hstruct := isPullback_projectionToBase_of_isPullback_blowupMorphism g t s t.length σ hzero hstep
  have hdown := isPullback_transitionMap_of_isPullback_blowupMorphism t s t.length σ hstep
  have h1 : (σ (t.nontrivialIndex 0) (t.nontrivialIndex_le_length (Nat.zero_le _)) ≫
        eqToHom (congrArg s.schemeAt (hret 0))) ≫ s.withoutIsoBlowups.isoZero.hom
      = t.withoutIsoBlowups.isoZero.hom ≫ g := by
    rw [s.withoutIsoBlowups_isoObjZero, t.withoutIsoBlowups_isoObjZero, s.objNontrivialIndexZeroIso_hom, t.objNontrivialIndexZeroIso_hom,
      Category.assoc, SequenceOfBlowups.eqToHom_comp_projectionToBase_consolidated153 s (hret 0)]
    exact (hstruct (t.nontrivialIndex 0) (t.nontrivialIndex_le_length (Nat.zero_le _))).w
  have h2 : ∀ j : ℕ, ∀ hj : j < t.withoutIsoBlowups.length,
      IsPullback
        (σ (t.nontrivialIndex (j + 1)) (t.nontrivialIndex_le_length hj) ≫
          eqToHom (congrArg s.schemeAt (hret (j + 1))))
        (t.withoutIsoBlowups.transitionMapSucc j) (s.withoutIsoBlowups.transitionMapSucc j)
        (σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length (le_of_lt hj)) ≫
          eqToHom (congrArg s.schemeAt (hret j))) := by
    intro j hj
    rw [t.withoutIsoBlowups_blowupMorphism, s.withoutIsoBlowups_blowupMorphism]
    exact isPullback_eqToHom_right_consolidated153
      (hdown (t.nontrivialIndex j) (t.nontrivialIndex (j + 1)) (t.nontrivialIndex_monotone (Nat.le_succ j))
        (t.nontrivialIndex_le_length hj))
      (congrArg s.schemeAt (hret (j + 1))) (congrArg s.schemeAt (hret j))
      (SequenceOfBlowups.eqToHom_comp_transitionMap_consolidated153 s (hret j) (hret (j + 1))
        (t.nontrivialIndex_monotone (Nat.le_succ j)) (s.nontrivialIndex_monotone (Nat.le_succ j)))
  have h3 : ∀ j : ℕ, ∀ hj : j < t.withoutIsoBlowups.length,
      t.withoutIsoBlowups.center j = (s.withoutIsoBlowups.center j).comap
        (σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length (le_of_lt hj)) ≫
          eqToHom (congrArg s.schemeAt (hret j))) := by
    intro j hj
    exact center_eq_comap_comp_eqToHom_consolidated153 t s (hret j)
      (σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length (le_of_lt hj)))
      (hcen (t.nontrivialIndex j) (t.nontrivialIndex_lt_length hj))
  exact ⟨hplen, fun j hj => σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length hj) ≫
    eqToHom (congrArg s.schemeAt (hret j)), h1, h2, h3⟩


end

section
variable {X : Scheme.{u}}

private theorem isStrictPullbackSequenceOfBlowups_id_of_isomorphic_consolidated153 {B B' : SequenceOfBlowups X}
    (h : B.Isomorphic B') : IsStrictPullbackBlowupSeq (𝟙 X) B B' := by
  unfold SequenceOfBlowups.Isomorphic at h
  unfold IsStrictPullbackBlowupSeq
  obtain ⟨hlen, e, hzero, hstep, hcen⟩ := h
  refine ⟨hlen, fun i hi => (e i hi).hom, ?_, ?_, ?_⟩
  · rw [Category.comp_id]
    exact hzero
  · intro i hi
    exact IsPullback.of_horiz_isIso ⟨hstep i hi⟩
  · intro i hi
    exact (hcen i hi).symm

theorem SequenceOfBlowups.Isomorphic.withoutIsoBlowups {t₁ t₂ : SequenceOfBlowups X}
    (h : t₁.Isomorphic t₂) : t₁.withoutIsoBlowups.Isomorphic t₂.withoutIsoBlowups :=
  ((isStrictPullbackSequenceOfBlowups_id_of_isomorphic_consolidated153 h).withoutIsoBlowups).isomorphic
    (isStrictPullbackSequenceOfBlowups_id_of_isomorphic_consolidated153 (SequenceOfBlowups.isomorphic_refl t₂.withoutIsoBlowups))


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
section



private theorem support_nonempty_iff_ne_top_consolidated154 {A : Scheme.{u}} (I : A.IdealSheafData) :
    (∃ x, x ∈ I.support) ↔ I ≠ ⊤ := by
  constructor
  · rintro ⟨x, hx⟩ rfl
    rw [Scheme.IdealSheafData.support_top] at hx
    exact hx
  · intro hne
    by_contra hc
    push Not at hc
    exact hne ((Scheme.IdealSheafData.support_eq_bot_iff I).mp
      (SetLike.ext fun x => iff_of_false (hc x) (fun hmem => hmem)))

private theorem comap_isoHom_eq_top_iff_consolidated154 {A B : Scheme.{u}} (e : A ≅ B) (J : B.IdealSheafData) :
    J.comap e.hom = ⊤ ↔ J = ⊤ := by
  constructor
  · intro hJ
    have h1 : (J.comap e.hom).comap e.inv = J := by
      rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id]
    rw [← h1, hJ]
    simp
  · rintro rfl
    simp

namespace SequenceOfBlowups

variable {X : Scheme.{u}}

section
variable (s : SequenceOfBlowups X)

theorem withoutIsoBlowups_projectionToBase (j : ℕ) :
    s.withoutIsoBlowups.projectionToBase j = s.projectionToBase (s.nontrivialIndex j) := by
  have h0 : s.withoutIsoBlowups.isoZero.hom = s.projectionToBase (s.nontrivialIndex 0) := s.objNontrivialIndexZeroIso_hom
  rw [projectionToBase_def, withoutIsoBlowups_transitionMap, h0]
  exact s.transitionMap_comp_projectionToBase (s.nontrivialIndex_monotone (Nat.zero_le j))

theorem exists_nontrivialIndex_eq_of_center_ne_top {i : ℕ} (hi : i < s.length)
    (h : s.center i ≠ ⊤) :
    ∃ j, j < s.lengthWithoutIsoBlowups ∧ s.nontrivialIndex j = i := by
  have hex : ∃ n, i < s.nontrivialIndex n :=
    ⟨s.lengthWithoutIsoBlowups, by rw [s.nontrivialIndex_lengthWithoutIsoBlowups]; exact hi⟩
  obtain ⟨n, hn1, hn2, hn3⟩ :
      ∃ n, i < s.nontrivialIndex n ∧ (∀ m, m < n → ¬ (i < s.nontrivialIndex m)) ∧ n ≤ s.lengthWithoutIsoBlowups :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm,
      Nat.find_le (by rw [s.nontrivialIndex_lengthWithoutIsoBlowups]; exact hi)⟩
  cases n with
  | zero => exact absurd (s.center_eq_top_of_lt_nontrivialIndex_zero hn1) h
  | succ m =>
      have hmi : s.nontrivialIndex m ≤ i := not_lt.mp (hn2 m (Nat.lt_succ_self m))
      refine ⟨m, by omega, ?_⟩
      rcases eq_or_lt_of_le hmi with heq | hlt
      · exact heq
      · exact absurd (s.center_eq_top_of_nontrivialIndex_lt hlt hn1) h


end

end SequenceOfBlowups

namespace IsStrictPullbackBlowupSeq

theorem isPullbackSequenceOfBlowups_withoutIsoBlowups {X' X : Scheme.{u}} {φ : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq φ t s) :
    IsPullbackBlowupSequence φ t.withoutIsoBlowups s := by
  obtain ⟨hlen, σ, hzero, hstep, hcen⟩ := h
  have hstructPB : ∀ (i : ℕ) (hi : i ≤ t.length),
      IsPullback (σ i hi) (t.projectionToBase i) (s.projectionToBase i) φ :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism φ t s t.length σ hzero hstep
  have hdownPB : ∀ (a b : ℕ) (hab : a ≤ b) (hb : b ≤ t.length),
      IsPullback (σ b hb) (t.transitionMap hab) (s.transitionMap hab) (σ a (hab.trans hb)) :=
    isPullback_transitionMap_of_isPullback_blowupMorphism t s t.length σ hstep
  obtain ⟨e, he1, he2⟩ :
      ∃ e : ∀ i : ℕ, i ≤ t.withoutIsoBlowups.length →
          (t.withoutIsoBlowups.schemeAt i ≅ Limits.pullback φ (s.projectionToBase (t.nontrivialIndex i))),
        (∀ (i : ℕ) (hi : i ≤ t.withoutIsoBlowups.length),
            (e i hi).hom ≫ Limits.pullback.fst φ (s.projectionToBase (t.nontrivialIndex i))
              = t.projectionToBase (t.nontrivialIndex i)) ∧
        (∀ (i : ℕ) (hi : i ≤ t.withoutIsoBlowups.length),
            (e i hi).hom ≫ Limits.pullback.snd φ (s.projectionToBase (t.nontrivialIndex i))
              = σ (t.nontrivialIndex i)
                  (t.nontrivialIndex_le_length (show i ≤ t.lengthWithoutIsoBlowups from hi))) := by
    refine ⟨fun i hi => ((hstructPB (t.nontrivialIndex i)
        (t.nontrivialIndex_le_length (show i ≤ t.lengthWithoutIsoBlowups from hi))).flip).isoPullback, ?_, ?_⟩
    · intro i hi
      exact ((hstructPB (t.nontrivialIndex i)
        (t.nontrivialIndex_le_length (show i ≤ t.lengthWithoutIsoBlowups from hi))).flip).isoPullback_hom_fst
    · intro i hi
      exact ((hstructPB (t.nontrivialIndex i)
        (t.nontrivialIndex_le_length (show i ≤ t.lengthWithoutIsoBlowups from hi))).flip).isoPullback_hom_snd
  refine ⟨t.nontrivialIndex, e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have h1 := t.nontrivialIndex_lt_length hi
    omega
  · intro i j _ hij
    exact t.nontrivialIndex_strictMono hij
  · exact t.nontrivialIndex_lengthWithoutIsoBlowups.trans hlen
  · intro i hi
    have hi' : i < t.length := by omega
    have hcomap : ((s.center i).comap (Limits.pullback.snd φ (s.projectionToBase i))).comap
        (((hstructPB i hi'.le).flip).isoPullback.hom) = t.center i := by
      rw [← Scheme.IdealSheafData.comap_comp,
        ((hstructPB i hi'.le).flip).isoPullback_hom_snd]
      exact (hcen i hi').symm
    rw [support_nonempty_iff_ne_top_consolidated154]
    constructor
    · intro hne
      refine t.exists_nontrivialIndex_eq_of_center_ne_top hi' ?_
      intro htop
      exact hne ((comap_isoHom_eq_top_iff_consolidated154 _ _).mp (hcomap.trans htop))
    · rintro ⟨j, hj, rfl⟩
      intro htop
      refine t.center_nontrivialIndex_ne_top hj ?_
      rw [← hcomap, htop]
      simp
  · intro i hi
    rw [he1 i hi, t.withoutIsoBlowups_projectionToBase]
  · intro i hi hr
    have hbi : t.nontrivialIndex (i + 1) ≤ t.length :=
      t.nontrivialIndex_le_length (show i + 1 ≤ t.lengthWithoutIsoBlowups from hi)
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Category.assoc, he1, s.pullbackTransitionMap_fst, he1, t.withoutIsoBlowups_blowupMorphism i]
      exact t.transitionMap_comp_projectionToBase (t.nontrivialIndex_monotone (Nat.le_succ i))
    · rw [Category.assoc, Category.assoc, he2, s.pullbackTransitionMap_snd, ← Category.assoc, he2,
        t.withoutIsoBlowups_blowupMorphism i]
      exact (hdownPB (t.nontrivialIndex i) (t.nontrivialIndex (i + 1))
        (t.nontrivialIndex_monotone (Nat.le_succ i)) hbi).w.symm
  · intro i hi
    rw [he2 i hi.le]
    exact hcen (t.nontrivialIndex i) (t.nontrivialIndex_lt_length hi)

end IsStrictPullbackBlowupSeq

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackComposition
section



private theorem mem_support_comap_consolidated152 {A B : Scheme.{u}} (f : A ⟶ B) (I : B.IdealSheafData)
    (x : ↥A) : x ∈ (I.comap f).support ↔ f.base x ∈ I.support := by
  rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
  exact Iff.rfl

private theorem support_comap_pullback_snd_nonempty_iff_consolidated152 {W V Y T : Scheme.{u}} (u : V ⟶ Y) (c : W ⟶ V)
    [AlgebraicGeometry.Surjective c] (g : T ⟶ Y) (I : T.IdealSheafData) :
    (∃ x, x ∈ (I.comap (Limits.pullback.snd (c ≫ u) g)).support) ↔
      (∃ x, x ∈ (I.comap (Limits.pullback.snd u g)).support) := by
  obtain ⟨q, hq1, hq2⟩ :
      ∃ q : Limits.pullback (c ≫ u) g ⟶ Limits.pullback u g,
        q ≫ Limits.pullback.fst u g = Limits.pullback.fst (c ≫ u) g ≫ c ∧
          q ≫ Limits.pullback.snd u g = Limits.pullback.snd (c ≫ u) g :=
    ⟨Limits.pullback.lift (Limits.pullback.fst (c ≫ u) g ≫ c)
        (Limits.pullback.snd (c ≫ u) g)
        (by rw [Category.assoc]; exact Limits.pullback.condition),
      Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩
  have hA : IsPullback (Limits.pullback.fst (c ≫ u) g) q c (Limits.pullback.fst u g) := by
    refine IsPullback.of_bot ?_ hq1.symm (IsPullback.of_hasPullback u g)
    rw [hq2]
    exact IsPullback.of_hasPullback (c ≫ u) g
  have hqs : AlgebraicGeometry.Surjective q := by
    rw [← hA.isoPullback_hom_snd]
    infer_instance
  have hbase : ∀ x : ↥(Limits.pullback (c ≫ u) g),
      (Limits.pullback.snd (c ≫ u) g).base x =
        (Limits.pullback.snd u g).base (q.base x) := by
    intro x
    rw [← hq2]
    simp
  constructor
  · rintro ⟨x, hx⟩
    rw [mem_support_comap_consolidated152] at hx
    refine ⟨q.base x, ?_⟩
    rw [mem_support_comap_consolidated152, ← hbase x]
    exact hx
  · rintro ⟨y, hy⟩
    rw [mem_support_comap_consolidated152] at hy
    obtain ⟨x, hx⟩ := hqs.surj y
    refine ⟨x, ?_⟩
    rw [mem_support_comap_consolidated152, hbase x, hx]
    exact hy

namespace IsPullbackBlowupSequence

theorem comp_isStrictPullbackSequenceOfBlowups {W V Y : Scheme.{u}} {u : V ⟶ Y} {c : W ⟶ V}
    [AlgebraicGeometry.Surjective c]
    {s : SequenceOfBlowups Y} {s' : SequenceOfBlowups V} {t : SequenceOfBlowups W}
    (h : IsPullbackBlowupSequence u s' s) (hc : IsStrictPullbackBlowupSeq c t s') :
    IsPullbackBlowupSequence (c ≫ u) t s := by
  unfold FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence at h ⊢
  unfold FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq at hc
  obtain ⟨r, e, hr1, hr2, hr3, hr4, hefst, hestep, hecenter⟩ := h
  obtain ⟨hlen, σ, hzero, hstep, hcenter⟩ := hc
  have hle : ∀ i : ℕ, i ≤ t.length → i ≤ s'.length := by
    intro i hi
    omega
  have hsq : ∀ (i : ℕ) (hi : i ≤ t.length),
      IsPullback (σ i hi) (t.projectionToBase i) (s'.projectionToBase i) c :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism c t s' t.length σ hzero hstep
  have hpaste : ∀ (i : ℕ) (hi : i ≤ t.length),
      IsPullback (t.projectionToBase i)
        (σ i hi ≫ (e i (hle i hi)).hom ≫ Limits.pullback.snd u (s.projectionToBase (r i)))
        (c ≫ u) (s.projectionToBase (r i)) := by
    intro i hi
    have hcomm : s'.projectionToBase i ≫ u =
        ((e i (hle i hi)).hom ≫ Limits.pullback.snd u (s.projectionToBase (r i))) ≫
          s.projectionToBase (r i) := by
      rw [← hefst i (hle i hi), Category.assoc, Category.assoc, Limits.pullback.condition]
    exact (hsq i hi).flip.paste_vert
      (IsPullback.of_iso_pullback ⟨hcomm⟩ (e i (hle i hi)) (hefst i (hle i hi)) rfl)
  have hFfst : ∀ (i : ℕ) (hi : i ≤ t.length),
      ((hpaste i hi).isoPullback).hom ≫
          Limits.pullback.fst (c ≫ u) (s.projectionToBase (r i)) = t.projectionToBase i :=
    fun i hi => (hpaste i hi).isoPullback_hom_fst
  have hFsnd : ∀ (i : ℕ) (hi : i ≤ t.length),
      ((hpaste i hi).isoPullback).hom ≫
          Limits.pullback.snd (c ≫ u) (s.projectionToBase (r i)) =
        σ i hi ≫ (e i (hle i hi)).hom ≫ Limits.pullback.snd u (s.projectionToBase (r i)) :=
    fun i hi => (hpaste i hi).isoPullback_hom_snd
  have hFsnd' : ∀ (i : ℕ) (hi : i ≤ t.length) {Z : Scheme.{u}} (k : s.schemeAt (r i) ⟶ Z),
      ((hpaste i hi).isoPullback).hom ≫
          Limits.pullback.snd (c ≫ u) (s.projectionToBase (r i)) ≫ k =
        σ i hi ≫ (e i (hle i hi)).hom ≫
          Limits.pullback.snd u (s.projectionToBase (r i)) ≫ k := by
    intro i hi Z k
    rw [← Category.assoc, hFsnd, Category.assoc, Category.assoc]
  have hc1 : ∀ i < t.length, r i < s.length := by
    intro i hi
    exact hr1 i (by omega)
  have hc2 : ∀ (i j : ℕ), j ≤ t.length → i < j → r i < r j := by
    intro i j hj hij
    exact hr2 i j (by omega) hij
  have hc3 : r t.length = s.length := by
    rw [hlen]
    exact hr3
  have hc4 : ∀ i < s.length,
      (∃ x, x ∈ ((s.center i).comap
        (Limits.pullback.snd (c ≫ u) (s.projectionToBase i))).support) ↔
        ∃ j < t.length, r j = i := by
    intro i hi
    refine (support_comap_pullback_snd_nonempty_iff_consolidated152 u c (s.projectionToBase i) (s.center i)).trans ?_
    refine (hr4 i hi).trans ?_
    constructor
    · rintro ⟨j, hj, hji⟩
      exact ⟨j, by omega, hji⟩
    · rintro ⟨j, hj, hji⟩
      exact ⟨j, by omega, hji⟩
  have hc6 : ∀ (i : ℕ) (hi : i < t.length) (hrr : r i ≤ r (i + 1)),
      t.transitionMapSucc i ≫ ((hpaste i (Nat.le_of_lt hi)).isoPullback).hom =
        ((hpaste (i + 1) hi).isoPullback).hom ≫ s.pullbackTransitionMap (c ≫ u) hrr := by
    intro i hi hrr
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc, SequenceOfBlowups.pullbackTransitionMap_fst, hFfst]
      rw [t.blowupMorphism_eq_transitionMap]
      exact t.transitionMap_comp_projectionToBase _
    · simp only [Category.assoc, SequenceOfBlowups.pullbackTransitionMap_snd, hFsnd, hFsnd']
      rw [← Category.assoc, ← (hstep i hi).w, Category.assoc,
        ← Category.assoc (s'.transitionMapSucc i), hestep i (by omega) hrr, Category.assoc,
        SequenceOfBlowups.pullbackTransitionMap_snd]
  have hc7 : ∀ (i : ℕ) (hi : i < t.length),
      t.center i = (s.center (r i)).comap
        (((hpaste i (Nat.le_of_lt hi)).isoPullback).hom ≫
          Limits.pullback.snd (c ≫ u) (s.projectionToBase (r i))) := by
    intro i hi
    rw [hcenter i hi, hecenter i (by omega), hFsnd,
      ← Scheme.IdealSheafData.comap_comp]
  exact ⟨r, fun i hi => (hpaste i hi).isoPullback, hc1, hc2, hc3, hc4, hFfst, hc6, hc7⟩

end IsPullbackBlowupSequence

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackUpToEmptyCenters
section

open CategoryTheory.Limits Opposite


def IsPullbackUpToEmptyCenters {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) : Prop :=
  ∃ (r : ℕ → ℕ) (e : ∀ i, i ≤ s'.length → (s'.schemeAt i ≅ pullback φ (s.projectionToBase (r i)))),
    (∀ i < s'.length, r i < s.length) ∧
    (∀ i j : ℕ, j ≤ s'.length → i < j → r i < r j) ∧
    r s'.length = s.length ∧
    (∀ i < s.length, (¬ ∃ j < s'.length, r j = i) →
      ¬ ∃ x, x ∈ ((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support) ∧
    (∀ (i : ℕ) (hi : i ≤ s'.length),
      (e i hi).hom ≫ pullback.fst φ (s.projectionToBase (r i)) = s'.projectionToBase i) ∧
    (∀ (i : ℕ) (hi : i < s'.length) (hr : r i ≤ r (i + 1)),
      s'.transitionMapSucc i ≫ (e i (Nat.le_of_lt hi)).hom =
        (e (i + 1) (Nat.succ_le_of_lt hi)).hom ≫ s.pullbackTransitionMap φ hr) ∧
    (∀ (i : ℕ) (hi : i < s'.length),
      s'.center i =
        (s.center (r i)).comap
          ((e i (Nat.le_of_lt hi)).hom ≫ pullback.snd φ (s.projectionToBase (r i))))

private theorem ne_top_iff_exists_mem_support_consolidated206 {X : Scheme.{u}} (I : X.IdealSheafData) :
    I ≠ ⊤ ↔ ∃ x, x ∈ I.support := by
  have hiff : I.support = ⊥ ↔ I = ⊤ := by simp
  constructor
  · intro hne
    by_contra hx
    refine hne (hiff.mp (SetLike.ext fun y => ⟨fun hy => ?_, fun hy => (hy : False).elim⟩))
    exact absurd (⟨y, hy⟩ : ∃ x, x ∈ I.support) hx
  · rintro ⟨x, hx⟩ hI
    rw [hiff.mpr hI] at hx
    exact hx

private theorem comap_iso_hom_ne_top_consolidated206 {X Y : Scheme.{u}} (E : X ≅ Y) (J : Y.IdealSheafData)
    (h : J ≠ ⊤) : J.comap E.hom ≠ ⊤ := by
  intro hc
  apply h
  have hJ : J = (J.comap E.hom).comap E.inv := by
    rw [← Scheme.IdealSheafData.comap_comp, E.inv_hom_id, Scheme.IdealSheafData.comap_id]
  rw [hJ, hc, Scheme.IdealSheafData.comap_top]

private theorem comp_eq_of_eq_of_comp_eq_consolidated206 {A B C : Scheme.{u}} (u : A ⟶ B) {f g : B ⟶ C} (hfg : f = g)
    {k : A ⟶ C} (hk : u ≫ g = k) : u ≫ f = k := by
  rw [hfg]
  exact hk

private theorem comp_comp_eq_of_comp_eq_consolidated206 {A B C D : Scheme.{u}} {u : A ⟶ B} {v : B ⟶ C} {w : A ⟶ C}
    (h : u ≫ v = w) (k : C ⟶ D) : u ≫ v ≫ k = w ≫ k := by
  rw [← Category.assoc, h]

section
variable {A B : Scheme.{u}}

private theorem comap_congr_morphism_consolidated206 {u v : A ⟶ B} (h : u = v) (I : B.IdealSheafData) :
    I.comap u = I.comap v := by
  rw [h]

private theorem comap_congr_idealSheaf_consolidated206 (u : A ⟶ B) {I J : B.IdealSheafData}
    (h : I = J) : I.comap u = J.comap u := by
  rw [h]


end

private noncomputable def pullbackCongrRightHom {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X)
    (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) : pullback φ f ⟶ pullback φ g :=
  pullback.lift (pullback.fst φ f) (pullback.snd φ f ≫ θ.hom)
    (by rw [Category.assoc, hθ]; exact pullback.condition)

section
variable {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X) (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f)

private theorem pullbackCongrRightHom_fst_consolidated206 :
    pullbackCongrRightHom φ f g θ hθ ≫ pullback.fst φ g = pullback.fst φ f :=
  pullback.lift_fst _ _ _

private theorem pullbackCongrRightHom_snd_consolidated206 :
    pullbackCongrRightHom φ f g θ hθ ≫ pullback.snd φ g = pullback.snd φ f ≫ θ.hom :=
  pullback.lift_snd _ _ _


end

private noncomputable def pullbackCongrRightIso {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X)
    (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) : pullback φ f ≅ pullback φ g where
  hom := pullbackCongrRightHom φ f g θ hθ
  inv := pullbackCongrRightHom φ g f θ.symm (by rw [← hθ, Iso.symm_hom, Iso.inv_hom_id_assoc])
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullbackCongrRightHom_fst_consolidated206, pullbackCongrRightHom_fst_consolidated206, Category.id_comp]
    · rw [Category.assoc, pullbackCongrRightHom_snd_consolidated206, ← Category.assoc, pullbackCongrRightHom_snd_consolidated206, Category.assoc, Iso.symm_hom,
        θ.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullbackCongrRightHom_fst_consolidated206, pullbackCongrRightHom_fst_consolidated206, Category.id_comp]
    · rw [Category.assoc, pullbackCongrRightHom_snd_consolidated206, ← Category.assoc, pullbackCongrRightHom_snd_consolidated206, Category.assoc, Iso.symm_hom,
        θ.inv_hom_id, Category.comp_id, Category.id_comp]

section
variable {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X) (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f)

private theorem pullbackCongrRightIso_hom_fst_consolidated206 :
    (pullbackCongrRightIso φ f g θ hθ).hom ≫ pullback.fst φ g = pullback.fst φ f :=
  pullbackCongrRightHom_fst_consolidated206 φ f g θ hθ

private theorem pullbackCongrRightIso_hom_snd_consolidated206 :
    (pullbackCongrRightIso φ f g θ hθ).hom ≫ pullback.snd φ g = pullback.snd φ f ≫ θ.hom :=
  pullbackCongrRightHom_snd_consolidated206 φ f g θ hθ


end

private theorem exists_pullbackIso_of_iso_consolidated206 {X X' A Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X)
    (u : A ≅ pullback φ f) (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) :
    ∃ v : A ≅ pullback φ g,
      v.hom ≫ pullback.fst φ g = u.hom ≫ pullback.fst φ f ∧
      v.hom ≫ pullback.snd φ g = u.hom ≫ pullback.snd φ f ≫ θ.hom := by
  refine ⟨u ≪≫ pullbackCongrRightIso φ f g θ hθ, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, pullbackCongrRightIso_hom_fst_consolidated206]
  · rw [Iso.trans_hom, Category.assoc, pullbackCongrRightIso_hom_snd_consolidated206]

private theorem comap_pullback_snd_ne_top_iff_of_iso_consolidated206 {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X)
    (g : Z' ⟶ X) (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) (I : Z.IdealSheafData)
    (J : Z'.IdealSheafData) (hIJ : J.comap θ.hom = I) :
    (I.comap (pullback.snd φ f) ≠ ⊤) ↔ (J.comap (pullback.snd φ g) ≠ ⊤) := by
  have hkey : (J.comap (pullback.snd φ g)).comap (pullbackCongrRightIso φ f g θ hθ).hom
      = I.comap (pullback.snd φ f) := by
    rw [← Scheme.IdealSheafData.comap_comp, pullbackCongrRightIso_hom_snd_consolidated206, Scheme.IdealSheafData.comap_comp, hIJ]
  constructor
  · intro h hc
    apply h
    rw [← hkey, hc, Scheme.IdealSheafData.comap_top]
  · intro h
    rw [← hkey]
    exact comap_iso_hom_ne_top_consolidated206 (pullbackCongrRightIso φ f g θ hθ) _ h

private theorem nontrivialIndex_comap_ne_top_iff_withoutIsoBlowups_consolidated206 {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X)
    (i : ℕ) :
    ((s.center (s.nontrivialIndex i)).comap (pullback.snd φ (s.projectionToBase (s.nontrivialIndex i))) ≠ ⊤) ↔
      ((s.withoutIsoBlowups.center i).comap (pullback.snd φ (s.withoutIsoBlowups.projectionToBase i)) ≠ ⊤) :=
  comap_pullback_snd_ne_top_iff_of_iso_consolidated206 φ (s.projectionToBase (s.nontrivialIndex i)) (s.withoutIsoBlowups.projectionToBase i) (Iso.refl _)
    ((Category.id_comp (s.withoutIsoBlowups.projectionToBase i)).trans (s.withoutIsoBlowups_projectionToBase_eq_nontrivialIndex i))
    (s.center (s.nontrivialIndex i)) (s.withoutIsoBlowups.center i) (Scheme.IdealSheafData.comap_id _)

section
variable {X : Scheme.{u}} (s : SequenceOfBlowups X)

private theorem eqToIso_hom_comp_projectionToBase_consolidated206 {a b : ℕ} (hab : a = b) :
    (eqToIso (congrArg s.schemeAt hab)).hom ≫ s.projectionToBase b = s.projectionToBase a := by
  subst hab
  simp

private theorem center_comap_eqToIso_hom_consolidated206 {a b : ℕ} (hab : a = b) :
    (s.center b).comap (eqToIso (congrArg s.schemeAt hab)).hom = s.center a := by
  subst hab
  simp

private theorem transitionMap_comp_eqToIso_consolidated206 {p q p' q' : ℕ}
    (hp : p = p') (hq : q = q') (hpq : p ≤ q) (hpq' : p' ≤ q') :
    s.transitionMap hpq ≫ (eqToIso (congrArg s.schemeAt hp)).hom
      = (eqToIso (congrArg s.schemeAt hq)).hom ≫ s.transitionMap hpq' := by
  subst hp
  subst hq
  simp


end

private theorem center_comap_pullback_snd_ne_top_congr_consolidated206 {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X)
    {a b : ℕ} (hab : a = b)
    (h : (s.center b).comap (pullback.snd φ (s.projectionToBase b)) ≠ ⊤) :
    (s.center a).comap (pullback.snd φ (s.projectionToBase a)) ≠ ⊤ := by
  subst hab
  exact h

section
variable {X X' : Scheme.{u}} (s : SequenceOfBlowups X) (φ : X' ⟶ X)

private theorem pullbackTransitionMap_self_consolidated206 {i : ℕ}
    (h : i ≤ i) : s.pullbackTransitionMap φ h = 𝟙 (pullback φ (s.projectionToBase i)) := by
  refine pullback.hom_ext ?_ ?_
  · rw [s.pullbackTransitionMap_fst, Category.id_comp]
  · rw [s.pullbackTransitionMap_snd, s.transitionMap_self, Category.comp_id, Category.id_comp]

private theorem pullbackTransitionMap_comp_consolidated206 {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    s.pullbackTransitionMap φ hbc ≫ s.pullbackTransitionMap φ hab = s.pullbackTransitionMap φ (hab.trans hbc) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, s.pullbackTransitionMap_fst, s.pullbackTransitionMap_fst, s.pullbackTransitionMap_fst]
  · rw [Category.assoc, s.pullbackTransitionMap_snd, ← Category.assoc, s.pullbackTransitionMap_snd, Category.assoc,
      s.transitionMap_trans, s.pullbackTransitionMap_snd]

private theorem pullbackTransitionMap_comp_assoc_consolidated206 {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) {W : Scheme.{u}}
    (k : pullback φ (s.projectionToBase a) ⟶ W) :
    s.pullbackTransitionMap φ hbc ≫ s.pullbackTransitionMap φ hab ≫ k
      = s.pullbackTransitionMap φ (hab.trans hbc) ≫ k := by
  rw [← Category.assoc, pullbackTransitionMap_comp_consolidated206]

private theorem pullbackTransitionMap_snd_assoc_consolidated206 {i i' : ℕ} (h : i ≤ i') {W : Scheme.{u}} (k : s.schemeAt i ⟶ W) :
    s.pullbackTransitionMap φ h ≫ pullback.snd φ (s.projectionToBase i) ≫ k
      = pullback.snd φ (s.projectionToBase i') ≫ s.transitionMap h ≫ k := by
  rw [← Category.assoc, s.pullbackTransitionMap_snd, Category.assoc]


end

namespace IsPullbackUpToEmptyCenters

theorem isPullbackSequenceOfBlowups_withoutIsoBlowups {X X' : Scheme.{u}} {φ : X' ⟶ X} {s' : SequenceOfBlowups X'}
    {s : SequenceOfBlowups X} (h : IsPullbackUpToEmptyCenters φ s' s) :
    IsPullbackBlowupSequence φ s'.withoutIsoBlowups s.withoutIsoBlowups := by
  obtain ⟨r, e, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hle : ∀ j : ℕ, j ≤ s'.lengthWithoutIsoBlowups → s'.nontrivialIndex j ≤ s'.length := fun j hj =>
    s'.nontrivialIndex_le_length hj
  have hrmono : ∀ i i' : ℕ, i ≤ i' → i' ≤ s'.length → r i ≤ r i' := by
    intro i i' hii hi'
    rcases eq_or_lt_of_le hii with rfl | hlt
    · exact le_rfl
    · exact le_of_lt (h2 i i' hi' hlt)
  have hdown : ∀ (i i' : ℕ) (hii' : i ≤ i') (hi' : i' ≤ s'.length) {W : Scheme.{u}}
      (k : pullback φ (s.projectionToBase (r i)) ⟶ W),
      s'.transitionMap hii' ≫ (e i (hii'.trans hi')).hom ≫ k
        = (e i' hi').hom ≫ s.pullbackTransitionMap φ (hrmono i i' hii' hi') ≫ k := by
    intro i i' hii'
    induction i', hii' using Nat.le_induction with
    | base =>
      intro hi W k
      rw [s'.transitionMap_self, Category.id_comp, pullbackTransitionMap_self_consolidated206, Category.id_comp]
    | succ m hm ih =>
      intro hi W k
      have hm' : m ≤ s'.length := le_trans (Nat.le_succ m) hi
      have hmlt : m < s'.length := lt_of_lt_of_le (Nat.lt_succ_self m) hi
      have hrstep : r m ≤ r (m + 1) := hrmono m (m + 1) (Nat.le_succ m) hi
      have hstep : s'.transitionMapSucc m ≫ (e m hm').hom
          = (e (m + 1) hi).hom ≫ s.pullbackTransitionMap φ hrstep := h6 m hmlt hrstep
      have hdec : s'.transitionMap (hm.trans (Nat.le_succ m)) = s'.transitionMapSucc m ≫ s'.transitionMap hm := by
        rw [s'.blowupMorphism_eq_transitionMap]
        exact (s'.transitionMap_trans hm (Nat.le_succ m)).symm
      rw [hdec, Category.assoc, ih hm' k, ← Category.assoc, hstep, Category.assoc,
        pullbackTransitionMap_comp_assoc_consolidated206]
  have key : ∀ j : ℕ, ∃ k : ℕ, j ≤ s'.lengthWithoutIsoBlowups → s.nontrivialIndex k = r (s'.nontrivialIndex j) := by
    intro j
    rcases lt_trichotomy j s'.lengthWithoutIsoBlowups with hj | hj | hj
    · have ha : s'.nontrivialIndex j < s'.length := s'.nontrivialIndex_lt_length hj
      have hc : s'.center (s'.nontrivialIndex j) ≠ ⊤ := s'.center_nontrivialIndex_ne_top hj
      have hc2 : s.center (r (s'.nontrivialIndex j)) ≠ ⊤ := by
        intro hcc
        apply hc
        rw [h7 (s'.nontrivialIndex j) ha, hcc, Scheme.IdealSheafData.comap_top]
      obtain ⟨k, _, hk2⟩ := s.exists_nontrivialIndex_eq_of_center_ne_top (h1 _ ha) hc2
      exact ⟨k, fun _ => hk2⟩
    · refine ⟨s.lengthWithoutIsoBlowups, fun _ => ?_⟩
      rw [s.nontrivialIndex_lengthWithoutIsoBlowups, hj, s'.nontrivialIndex_lengthWithoutIsoBlowups, h3]
    · exact ⟨0, fun hle' => absurd hle' (not_le.mpr hj)⟩
  choose μ hμ using key
  have hθ : ∀ (j : ℕ) (hj : j ≤ s'.lengthWithoutIsoBlowups),
      (eqToIso (congrArg s.schemeAt (hμ j hj).symm)).hom ≫ s.withoutIsoBlowups.projectionToBase (μ j)
        = s.projectionToBase (r (s'.nontrivialIndex j)) := by
    intro j hj
    exact comp_eq_of_eq_of_comp_eq_consolidated206 ((eqToIso (congrArg s.schemeAt (hμ j hj).symm)).hom)
      (s.withoutIsoBlowups_projectionToBase_eq_nontrivialIndex (μ j)) (eqToIso_hom_comp_projectionToBase_consolidated206 s (hμ j hj).symm)
  have hEx : ∀ (j : ℕ) (hj : j ≤ s'.lengthWithoutIsoBlowups),
      ∃ v : s'.withoutIsoBlowups.schemeAt j ≅ pullback φ (s.withoutIsoBlowups.projectionToBase (μ j)),
        v.hom ≫ pullback.fst φ (s.withoutIsoBlowups.projectionToBase (μ j))
            = (e (s'.nontrivialIndex j) (hle j hj)).hom ≫
                pullback.fst φ (s.projectionToBase (r (s'.nontrivialIndex j))) ∧
        v.hom ≫ pullback.snd φ (s.withoutIsoBlowups.projectionToBase (μ j))
            = (e (s'.nontrivialIndex j) (hle j hj)).hom ≫
                pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))) ≫
                  (eqToIso (congrArg s.schemeAt (hμ j hj).symm)).hom := by
    intro j hj
    exact exists_pullbackIso_of_iso_consolidated206 φ (s.projectionToBase (r (s'.nontrivialIndex j))) (s.withoutIsoBlowups.projectionToBase (μ j))
      (e (s'.nontrivialIndex j) (hle j hj)) (eqToIso (congrArg s.schemeAt (hμ j hj).symm)) (hθ j hj)
  choose E hEfst0 hEsnd0 using hEx
  have hEfst : ∀ (j : ℕ) (hj : j ≤ s'.lengthWithoutIsoBlowups),
      (E j hj).hom ≫ pullback.fst φ (s.withoutIsoBlowups.projectionToBase (μ j)) = s'.withoutIsoBlowups.projectionToBase j := by
    intro j hj
    exact ((hEfst0 j hj).trans (h5 (s'.nontrivialIndex j) (hle j hj))).trans
      (s'.withoutIsoBlowups_projectionToBase_eq_nontrivialIndex j).symm
  unfold IsPullbackBlowupSequence
  refine ⟨μ, E, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hh := hμ j (le_of_lt hj)
    have hlt : s.nontrivialIndex (μ j) < s.nontrivialIndex s.lengthWithoutIsoBlowups := by
      rw [hh, s.nontrivialIndex_lengthWithoutIsoBlowups]
      exact h1 (s'.nontrivialIndex j) (s'.nontrivialIndex_lt_length hj)
    exact s.nontrivialIndex_strictMono.lt_iff_lt.mp hlt
  · intro j k hk hjk
    have hj1 : j ≤ s'.lengthWithoutIsoBlowups := le_of_lt (lt_of_lt_of_le hjk hk)
    have hlt : s.nontrivialIndex (μ j) < s.nontrivialIndex (μ k) := by
      rw [hμ j hj1, hμ k hk]
      exact h2 (s'.nontrivialIndex j) (s'.nontrivialIndex k) (hle k hk) (s'.nontrivialIndex_strictMono hjk)
    exact s.nontrivialIndex_strictMono.lt_iff_lt.mp hlt
  · have hh : s.nontrivialIndex (μ s'.lengthWithoutIsoBlowups) = s.nontrivialIndex s.lengthWithoutIsoBlowups := by
      rw [hμ s'.lengthWithoutIsoBlowups le_rfl, s'.nontrivialIndex_lengthWithoutIsoBlowups, h3, s.nontrivialIndex_lengthWithoutIsoBlowups]
    exact s.nontrivialIndex_strictMono.injective hh
  · intro i hi
    have hi' : i < s.lengthWithoutIsoBlowups := hi
    have hiL : s.nontrivialIndex i < s.length := s.nontrivialIndex_lt_length hi'
    constructor
    · intro hx
      have hne : (s.center (s.nontrivialIndex i)).comap
          (pullback.snd φ (s.projectionToBase (s.nontrivialIndex i))) ≠ ⊤ :=
        (nontrivialIndex_comap_ne_top_iff_withoutIsoBlowups_consolidated206 φ s i).mpr ((ne_top_iff_exists_mem_support_consolidated206 _).mpr hx)
      obtain ⟨j0, hj0, hrj0⟩ : ∃ j < s'.length, r j = s.nontrivialIndex i := by
        by_contra hcon
        exact h4 (s.nontrivialIndex i) hiL hcon ((ne_top_iff_exists_mem_support_consolidated206 _).mp hne)
      have hK : (s.center (r j0)).comap (pullback.snd φ (s.projectionToBase (r j0))) ≠ ⊤ :=
        center_comap_pullback_snd_ne_top_congr_consolidated206 φ s hrj0 hne
      have hcen : s'.center j0 ≠ ⊤ := by
        rw [h7 j0 hj0, Scheme.IdealSheafData.comap_comp]
        exact comap_iso_hom_ne_top_consolidated206 (e j0 (le_of_lt hj0)) _ hK
      obtain ⟨k, hk1, hk2⟩ := s'.exists_nontrivialIndex_eq_of_center_ne_top hj0 hcen
      refine ⟨k, hk1, ?_⟩
      apply s.nontrivialIndex_strictMono.injective
      rw [hμ k (le_of_lt hk1), hk2]
      exact hrj0
    · rintro ⟨j, hj, rfl⟩
      refine (ne_top_iff_exists_mem_support_consolidated206 _).mp ((nontrivialIndex_comap_ne_top_iff_withoutIsoBlowups_consolidated206 φ s (μ j)).mp ?_)
      refine center_comap_pullback_snd_ne_top_congr_consolidated206 φ s (hμ j (le_of_lt hj)) ?_
      intro hcc
      refine s'.center_nontrivialIndex_ne_top hj ?_
      rw [h7 (s'.nontrivialIndex j) (s'.nontrivialIndex_lt_length hj), Scheme.IdealSheafData.comap_comp, hcc,
        Scheme.IdealSheafData.comap_top]
  · exact fun i hi => hEfst i hi
  · intro j hj hr
    have hj1 : j ≤ s'.lengthWithoutIsoBlowups := le_of_lt hj
    have hj2 : j + 1 ≤ s'.lengthWithoutIsoBlowups := hj
    have haj1 : s'.nontrivialIndex (j + 1) ≤ s'.length := hle (j + 1) hj2
    have hstep : s'.nontrivialIndex j ≤ s'.nontrivialIndex (j + 1) := le_of_lt (s'.nontrivialIndex_lt_succ j)
    have hrr : r (s'.nontrivialIndex j) ≤ r (s'.nontrivialIndex (j + 1)) :=
      hrmono (s'.nontrivialIndex j) (s'.nontrivialIndex (j + 1)) hstep haj1
    refine pullback.hom_ext ?_ ?_
    · have hL : (s'.withoutIsoBlowups.transitionMapSucc j ≫ (E j hj1).hom)
          ≫ pullback.fst φ (s.withoutIsoBlowups.projectionToBase (μ j)) = s'.withoutIsoBlowups.projectionToBase (j + 1) := by
        rw [Category.assoc, hEfst j hj1]
        exact (s'.withoutIsoBlowups.projectionToBase_succ j).symm
      have hR : ((E (j + 1) hj2).hom ≫ s.withoutIsoBlowups.pullbackTransitionMap φ hr)
          ≫ pullback.fst φ (s.withoutIsoBlowups.projectionToBase (μ j)) = s'.withoutIsoBlowups.projectionToBase (j + 1) := by
        rw [Category.assoc, SequenceOfBlowups.pullbackTransitionMap_fst, hEfst (j + 1) hj2]
      exact hL.trans hR.symm
    · have hL := (Category.assoc (s'.withoutIsoBlowups.transitionMapSucc j) (E j hj1).hom
            (pullback.snd φ (s.withoutIsoBlowups.projectionToBase (μ j)))).trans
          (((whisker_eq (s'.withoutIsoBlowups.transitionMapSucc j) (hEsnd0 j hj1)).trans
              (eq_whisker (s'.withoutIsoBlowups_blowupMorphism j) _)).trans
            ((hdown (s'.nontrivialIndex j) (s'.nontrivialIndex (j + 1)) hstep haj1 _).trans
              ((whisker_eq _ (pullbackTransitionMap_snd_assoc_consolidated206 s φ hrr _)).trans
                (whisker_eq _ (whisker_eq _
                  (transitionMap_comp_eqToIso_consolidated206 s (hμ j hj1).symm (hμ (j + 1) hj2).symm hrr
                    (s.nontrivialIndex_monotone hr)))))))
      have hR := (Category.assoc (E (j + 1) hj2).hom (s.withoutIsoBlowups.pullbackTransitionMap φ hr)
            (pullback.snd φ (s.withoutIsoBlowups.projectionToBase (μ j)))).trans
          ((whisker_eq (E (j + 1) hj2).hom
              (SequenceOfBlowups.pullbackTransitionMap_snd s.withoutIsoBlowups φ hr)).trans
            ((comp_comp_eq_of_comp_eq_consolidated206 (hEsnd0 (j + 1) hj2) (s.withoutIsoBlowups.transitionMap hr)).trans
              ((Category.assoc _ _ _).trans
                ((whisker_eq _ (Category.assoc _ _ _)).trans
                  (whisker_eq _ (whisker_eq _
                    (whisker_eq _ (s.withoutIsoBlowups_transitionMap hr))))))))
      exact hL.trans hR.symm
  · intro j hj
    have hj1 : j ≤ s'.lengthWithoutIsoBlowups := le_of_lt hj
    have haj : s'.nontrivialIndex j < s'.length := s'.nontrivialIndex_lt_length hj
    refine Eq.trans ?_ (comap_congr_morphism_consolidated206 (hEsnd0 j hj1) (s.center (s.nontrivialIndex (μ j)))).symm
    have hA := (center_comap_eqToIso_hom_consolidated206 s (hμ j hj1).symm).symm
    have hB := comap_congr_idealSheaf_consolidated206 (pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j)))) hA
    have hC := comap_congr_idealSheaf_consolidated206 (e (s'.nontrivialIndex j) (hle j hj1)).hom hB
    have hD : (s.center (r (s'.nontrivialIndex j))).comap
          ((e (s'.nontrivialIndex j) (hle j hj1)).hom ≫
            pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))))
        = ((s.center (r (s'.nontrivialIndex j))).comap
            (pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))))).comap
              (e (s'.nontrivialIndex j) (hle j hj1)).hom := by
      simp [Scheme.IdealSheafData.comap_comp]
    have hE2 : (s.center (s.nontrivialIndex (μ j))).comap
          ((e (s'.nontrivialIndex j) (hle j hj1)).hom ≫
            pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))) ≫
              (eqToIso (congrArg s.schemeAt (hμ j hj1).symm)).hom)
        = ((s.center (s.nontrivialIndex (μ j))).comap
            (pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))) ≫
              (eqToIso (congrArg s.schemeAt (hμ j hj1).symm)).hom)).comap
                (e (s'.nontrivialIndex j) (hle j hj1)).hom := by
      simp [Scheme.IdealSheafData.comap_comp]
    have hF2 : ((s.center (s.nontrivialIndex (μ j))).comap
          (pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))) ≫
            (eqToIso (congrArg s.schemeAt (hμ j hj1).symm)).hom)).comap
              (e (s'.nontrivialIndex j) (hle j hj1)).hom
        = (((s.center (s.nontrivialIndex (μ j))).comap
            (eqToIso (congrArg s.schemeAt (hμ j hj1).symm)).hom).comap
              (pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))))).comap
                (e (s'.nontrivialIndex j) (hle j hj1)).hom := by
      simp [Scheme.IdealSheafData.comap_comp]
    exact (((h7 (s'.nontrivialIndex j) haj).trans hD).trans hC).trans (hE2.trans hF2).symm

end IsPullbackUpToEmptyCenters

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceDescentDatum
section

open CategoryTheory.Limits

section

private theorem baseChange_projectionToBase_eq_fst_consolidated241 {X X' : Scheme.{u}} (s : SequenceOfBlowups X)
    (φ : X' ⟶ X) [Flat φ] (i : ℕ) :
    (s.baseChange φ).projectionToBase i = pullback.fst φ (s.projectionToBase i) := by
  induction i with
  | zero =>
    rw [SequenceOfBlowups.projectionToBase_zero, SequenceOfBlowups.baseChange_isoObjZero_hom]
  | succ n ih =>
    have hb : (s.baseChange φ).transitionMapSucc n ≫ (s.baseChange φ).projectionToBase n
        = (s.baseChange φ).projectionToBase (n + 1) := by
      rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
      exact SequenceOfBlowups.transitionMap_comp_projectionToBase _ _
    rw [← hb, ih, SequenceOfBlowups.baseChange_blowupMorphism]
    exact SequenceOfBlowups.pullbackTransitionMap_comp_fst s φ _

structure SequenceOfBlowupsDescentDatum {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W) where
  iso : ∀ i : ℕ, i ≤ t.length → (pullbackFstSchemeAt g t i ≅ pullbackSndSchemeAt g t i)
  comp_fst : ∀ (i : ℕ) (hi : i ≤ t.length),
    (iso i hi).hom ≫ pullback.fst (pullback.snd g g) (t.projectionToBase i)
      = pullback.fst (pullback.fst g g) (t.projectionToBase i)
  center_comap : ∀ (i : ℕ) (hi : i < t.length),
    ((t.center i).comap (pullback.snd (pullback.snd g g) (t.projectionToBase i))).comap
        (iso i hi.le).hom
      = (t.center i).comap (pullback.snd (pullback.fst g g) (t.projectionToBase i))
  comp_step : ∀ (i : ℕ) (hi : i < t.length),
    (iso (i + 1) (Nat.succ_le_of_lt hi)).hom ≫ t.pullbackTransitionMap (pullback.snd g g) (Nat.le_succ i)
      = t.pullbackTransitionMap (pullback.fst g g) (Nat.le_succ i) ≫ (iso i hi.le).hom

private structure DescendedSchemeData {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W)
    (D : SequenceOfBlowupsDescentDatum g t) (n : ℕ) where
  X : Scheme.{u}
  str : X ⟶ Y
  gam : t.schemeAt n ⟶ X
  hsq : n ≤ t.length → IsPullback gam (t.projectionToBase n) str g
  hgam : ∀ hn : n ≤ t.length,
    (D.iso n hn).hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n) ≫ gam
      = pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ gam

private structure DescendedBlowupOfSchemeData {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W)
    (D : SequenceOfBlowupsDescentDatum g t) (n : ℕ) (P : DescendedSchemeData g t D n) where
  next : DescendedSchemeData g t D (n + 1)
  down : next.X ⟶ P.X
  cen : P.X.IdealSheafData
  hblow : n < t.length → Blowup.IsBlowupAlongIdealSheaf down cen
  hpb : n < t.length → IsPullback next.gam (t.transitionMapSucc n) down P.gam
  hcen : n < t.length → t.center n = cen.comap P.gam

private def descendedSchemeDataZero_consolidated241 {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W)
    (D : SequenceOfBlowupsDescentDatum g t) : DescendedSchemeData g t D 0 where
  X := Y
  str := 𝟙 Y
  gam := t.projectionToBase 0 ≫ g
  hsq := fun _ => (IsPullback.of_horiz_isIso ⟨by simp⟩).flip
  hgam := fun h0 => by
    have c1 : pullback.fst (pullback.fst g g) (t.projectionToBase 0) ≫ pullback.fst g g
        = pullback.snd (pullback.fst g g) (t.projectionToBase 0) ≫ t.projectionToBase 0 := pullback.condition
    have c2 : pullback.fst (pullback.snd g g) (t.projectionToBase 0) ≫ pullback.snd g g
        = pullback.snd (pullback.snd g g) (t.projectionToBase 0) ≫ t.projectionToBase 0 := pullback.condition
    have c3 : pullback.fst g g ≫ g = pullback.snd g g ≫ g := pullback.condition
    have hf := D.comp_fst 0 h0
    calc (D.iso 0 h0).hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase 0) ≫
          (t.projectionToBase 0 ≫ g)
        = ((D.iso 0 h0).hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase 0) ≫
            t.projectionToBase 0) ≫ g := by
          simp only [Category.assoc]
      _ = (pullback.fst (pullback.fst g g) (t.projectionToBase 0) ≫ pullback.snd g g) ≫ g := by
          rw [← c2, ← Category.assoc, hf]
      _ = (pullback.fst (pullback.fst g g) (t.projectionToBase 0) ≫ pullback.fst g g) ≫ g := by
          rw [Category.assoc, Category.assoc, c3]
      _ = pullback.snd (pullback.fst g g) (t.projectionToBase 0) ≫ (t.projectionToBase 0 ≫ g) := by
          rw [c1, Category.assoc]

private def descendedBlowupAt_consolidated241 {W Y : Scheme.{u}} (g : W ⟶ Y) [Flat g]
    [QuasiCompact g] (t : SequenceOfBlowups W) (D : SequenceOfBlowupsDescentDatum g t)
    (n : ℕ) (P : DescendedSchemeData g t D n) : DescendedBlowupOfSchemeData g t D n P :=
  if hn : n < t.length then
    let S := descendedBlowupData g t hn P.str P.gam (P.hsq hn.le) (D.iso n hn.le)
      (D.iso (n + 1) (Nat.succ_le_of_lt hn)) (D.comp_step n hn) (D.center_comap n hn)
      (D.comp_fst n hn.le) (P.hgam hn.le)
    { next :=
        { X := S.total
          str := S.totalStruct
          gam := S.totalComparison
          hsq := fun _ => S.isPullback_base
          hgam := fun _ => S.hom_comparison }
      down := S.down
      cen := S.totalCenter
      hblow := fun _ => S.isBlowup_down
      hpb := fun _ => S.isPullback_sq
      hcen := fun _ => S.center_comap.symm }
  else
    { next :=
        { X := t.schemeAt (n + 1)
          str := t.projectionToBase (n + 1) ≫ g
          gam := 𝟙 (t.schemeAt (n + 1))
          hsq := fun hle => absurd (Nat.lt_of_succ_le hle) hn
          hgam := fun hle => absurd (Nat.lt_of_succ_le hle) hn }
      down := t.transitionMapSucc n ≫ P.gam
      cen := ⊤
      hblow := fun hlt => absurd hlt hn
      hpb := fun hlt => absurd hlt hn
      hcen := fun hlt => absurd hlt hn }

private def descendedSchemeDataAt_consolidated241 {W Y : Scheme.{u}} (g : W ⟶ Y) [Flat g]
    [QuasiCompact g] (t : SequenceOfBlowups W) (D : SequenceOfBlowupsDescentDatum g t)
    (n : ℕ) : DescendedSchemeData g t D n :=
  Nat.rec (motive := fun m => DescendedSchemeData g t D m) (descendedSchemeDataZero_consolidated241 g t D)
    (fun m P => (descendedBlowupAt_consolidated241 g t D m P).next) n

private def descendedSchemeAt_consolidated241 {W Y : Scheme.{u}} (g : W ⟶ Y) [Flat g]
    [QuasiCompact g] (t : SequenceOfBlowups W) (D : SequenceOfBlowupsDescentDatum g t)
    (n : ℕ) : Scheme.{u} :=
  (descendedSchemeDataAt_consolidated241 g t D n).X

private def descendedBlowupMorphism_consolidated241 {W Y : Scheme.{u}} (g : W ⟶ Y) [Flat g]
    [QuasiCompact g] (t : SequenceOfBlowups W) (D : SequenceOfBlowupsDescentDatum g t)
    (n : ℕ) : descendedSchemeAt_consolidated241 g t D (n + 1) ⟶ descendedSchemeAt_consolidated241 g t D n :=
  (descendedBlowupAt_consolidated241 g t D n (descendedSchemeDataAt_consolidated241 g t D n)).down

private def descendedTower_consolidated241 {W Y : Scheme.{u}} (g : W ⟶ Y) [Flat g]
    [QuasiCompact g] (t : SequenceOfBlowups W) (D : SequenceOfBlowupsDescentDatum g t) :
    ℕᵒᵖ ⥤ Scheme.{u} :=
  Functor.ofOpSequence (descendedBlowupMorphism_consolidated241 g t D)

private def descendedSequenceOfBlowups_consolidated241 {W Y : Scheme.{u}} (g : W ⟶ Y) [Flat g]
    [QuasiCompact g] (t : SequenceOfBlowups W) (D : SequenceOfBlowupsDescentDatum g t) :
    SequenceOfBlowups Y where
  length := t.length
  tower := descendedTower_consolidated241 g t D
  isoZero := Iso.refl Y
  center := fun i => (descendedBlowupAt_consolidated241 g t D i (descendedSchemeDataAt_consolidated241 g t D i)).cen
  isBlowup := fun i hi => by
    have hmap : (descendedTower_consolidated241 g t D).map (homOfLE (Nat.le_succ i)).op = descendedBlowupMorphism_consolidated241 g t D i :=
      Functor.ofOpSequence_map_homOfLE_succ (descendedBlowupMorphism_consolidated241 g t D) i
    rw [hmap]
    exact (descendedBlowupAt_consolidated241 g t D i (descendedSchemeDataAt_consolidated241 g t D i)).hblow hi

section
variable {W Y : Scheme.{u}} (g : W ⟶ Y) [Flat g] [QuasiCompact g] (t : SequenceOfBlowups W)

private theorem exists_isStrictPullbackSequenceOfBlowups_of_descentDatum_consolidated241 (D : SequenceOfBlowupsDescentDatum g t) : ∃ s : SequenceOfBlowups Y, IsStrictPullbackBlowupSeq g t s := by
  refine ⟨descendedSequenceOfBlowups_consolidated241 g t D, rfl, fun i _ => (descendedSchemeDataAt_consolidated241 g t D i).gam, ?_, ?_, ?_⟩
  · show (descendedSchemeDataAt_consolidated241 g t D 0).gam ≫ (descendedSequenceOfBlowups_consolidated241 g t D).isoZero.hom = t.isoZero.hom ≫ g
    have h0 : (descendedSchemeDataAt_consolidated241 g t D 0).gam = t.projectionToBase 0 ≫ g := rfl
    rw [h0, SequenceOfBlowups.projectionToBase_zero]
    exact Category.comp_id _
  · intro i hi
    have hmap : (descendedSequenceOfBlowups_consolidated241 g t D).transitionMapSucc i = descendedBlowupMorphism_consolidated241 g t D i := by
      rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_def]
      exact Functor.ofOpSequence_map_homOfLE_succ (descendedBlowupMorphism_consolidated241 g t D) i
    rw [hmap]
    exact (descendedBlowupAt_consolidated241 g t D i (descendedSchemeDataAt_consolidated241 g t D i)).hpb hi
  · intro i hi
    exact (descendedBlowupAt_consolidated241 g t D i (descendedSchemeDataAt_consolidated241 g t D i)).hcen hi

theorem exists_isStrictPullback_of_isomorphic_baseChange (h : (t.baseChange (pullback.fst g g)).Isomorphic (t.baseChange (pullback.snd g g))) :
    ∃ s : SequenceOfBlowups Y, IsStrictPullbackBlowupSeq g t s := by
  obtain ⟨-, e, hzero, hstep, hcen⟩ := h
  have hlp : (t.baseChange (pullback.fst g g)).length = t.length :=
    t.baseChange_length (pullback.fst g g)
  refine exists_isStrictPullbackSequenceOfBlowups_of_descentDatum_consolidated241 g t
    { iso := fun i hi => e i (by rw [hlp]; exact hi)
      comp_fst := ?_
      center_comap := ?_
      comp_step := ?_ }
  · intro i hi
    have key := SequenceOfBlowups.iso_hom_comp_projectionToBase (t.baseChange (pullback.fst g g))
      (t.baseChange (pullback.snd g g)) _ e hstep hzero i (by rw [hlp]; exact hi)
    rw [baseChange_projectionToBase_eq_fst_consolidated241, baseChange_projectionToBase_eq_fst_consolidated241] at key
    exact key
  · intro i hi
    have key := hcen i (by rw [hlp]; exact hi)
    rw [SequenceOfBlowups.baseChange_center, SequenceOfBlowups.baseChange_center] at key
    exact key
  · intro i hi
    have key := hstep i (by rw [hlp]; exact hi)
    rw [SequenceOfBlowups.baseChange_blowupMorphism, SequenceOfBlowups.baseChange_blowupMorphism] at key
    exact key


end

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.InducedRuleFieldExtension
section


section

private theorem notMem_support_comap_top_consolidated242 {A C : Scheme.{u}} (h : A ⟶ C) (x : ↥A) :
    x ∉ ((⊤ : C.IdealSheafData).comap h).support := by
  rw [Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.support_top]
  intro hx
  have hx' : x ∈ ((⊥ : TopologicalSpace.Closeds ↥A) : Set ↥A) := hx
  simp at hx'

theorem center_ne_top_of_isPullbackSequenceOfBlowups_id {X : Scheme.{u}} (s : SequenceOfBlowups X)
    (h : IsPullbackBlowupSequence (𝟙 X) s s) :
    ∀ i : ℕ, i < s.length → s.center i ≠ ⊤ := by
  obtain ⟨r, _e, _hlt, hmono, htop, hsupp, -⟩ := h
  have hgeid : ∀ i : ℕ, i ≤ s.length → i ≤ r i := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have h1 : r n < r (n + 1) := hmono n (n + 1) hn (Nat.lt_succ_self n)
      have h2 : n ≤ r n := ih (Nat.le_of_succ_le hn)
      omega
  have hleid : ∀ d i : ℕ, i + d = s.length → r i + d ≤ s.length := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have hii : i = s.length := by omega
      subst hii
      rw [htop]
      omega
    | succ m ih =>
      intro i hi
      have hi1 : (i + 1) + m = s.length := by omega
      have h2 := ih (i + 1) hi1
      have h3 : r i < r (i + 1) := hmono i (i + 1) (by omega) (Nat.lt_succ_self i)
      omega
  have hrid : ∀ i : ℕ, i ≤ s.length → r i = i := by
    intro i hi
    have h1 := hgeid i hi
    have h2 := hleid (s.length - i) i (by omega)
    omega
  intro i hi hc
  obtain ⟨x, hx⟩ := (hsupp i hi).mpr ⟨i, hi, hrid i hi.le⟩
  rw [hc] at hx
  exact notMem_support_comap_top_consolidated242 _ x hx

section
variable (B : AffineResolutionRule.{u})

theorem AffineResolutionRule.center_ne_top (hB : IsCompatibleWithOpenImmersions B)
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y] :
    ∀ i : ℕ, i < (B k Y p).length → (B k Y p).center i ≠ ⊤ :=
  center_ne_top_of_isPullbackSequenceOfBlowups_id (B k Y p) (hB k Y Y p p (𝟙 Y) (Category.id_comp p))

theorem inducedRuleCompatibleWithFieldExtension : InducedRuleCompatibleWithFieldExtension B := by
  intro hoi hfe F hF k _ _ X f _ _ _ K _ _ _ _
  obtain ⟨W, c, g, hWaff, hWred, hqlft, hqqc, hcet, hcsur, hYaff, hYred, hglft, hgqc, hget,
    hgsur, hgstruct, hgproj⟩ := exists_etale_surjective_affine_cover_baseChange X f K
  have := hWaff
  have := hWred
  have := hqlft
  have := hqqc
  have := hcet
  have := hcsur
  have := hYaff
  have := hYred
  have := hglft
  have := hgqc
  have := hget
  have := hgsur
  have h0 : IsStrictPullbackBlowupSeq (baseChangeProjection f K)
      ((F k X f).baseChange (baseChangeProjection f K)) (F k X f) :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  have hw : IsStrictPullbackBlowupSeq g
      (((F k X f).baseChange (baseChangeProjection f K)).baseChange g)
      ((F k X f).baseChange (baseChangeProjection f K)) :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  have hcomp := hw.comp h0
  rw [hgproj] at hcomp
  have htW : IsStrictPullbackBlowupSeq c (B k W (c ≫ f)) (F k X f) :=
    hF k X f W (c ≫ f) c rfl AlgebraicGeometry.Surjective.surj
  have htK : IsStrictPullbackBlowupSeq (baseChangeProjection (c ≫ f) K)
      (B K (baseChange (c ≫ f) K) (baseChangeToSpec (c ≫ f) K)) (B k W (c ≫ f)) :=
    hfe k W (c ≫ f) K
  have hEqw := hcomp.isomorphic (htK.comp htW)
  have hntop := AffineResolutionRule.center_ne_top B hoi K (baseChange (c ≫ f) K)
      (baseChangeToSpec (c ≫ f) K)
  have hEq := (SequenceOfBlowups.Isomorphic.withoutIsoBlowups hEqw).trans (SequenceOfBlowups.withoutIsoBlowups_isomorphic_self _ hntop)
  have h₂ : IsStrictPullbackBlowupSeq g (B K (baseChange (c ≫ f) K) (baseChangeToSpec (c ≫ f) K))
      (F K (baseChange f K) (baseChangeToSpec f K)) :=
    hF K (baseChange f K) (baseChangeToSpec f K) (baseChange (c ≫ f) K)
      (baseChangeToSpec (c ≫ f) K) g hgstruct AlgebraicGeometry.Surjective.surj
  have hdesc := IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic hw.withoutIsoBlowups h₂ hEq
  exact h0.isPullbackSequenceOfBlowups_withoutIsoBlowups.of_isomorphic hdesc


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GluedBlowupSequenceExistence
section

open CategoryTheory.Limits

section

private theorem exists_isStrictPullback_of_pullback_cover_consolidated263 {Y W V : Scheme.{u}} (g : W ⟶ Y) [Flat g]
    [QuasiCompact g] (r : V ⟶ pullback g g) [Flat r]
    [AlgebraicGeometry.Surjective r] (t : SequenceOfBlowups W) (u : SequenceOfBlowups V)
    (h1 : IsStrictPullbackBlowupSeq (r ≫ pullback.fst g g) u t)
    (h2 : IsStrictPullbackBlowupSeq (r ≫ pullback.snd g g) u t) :
    ∃ B : SequenceOfBlowups Y, IsStrictPullbackBlowupSeq g t B := by
  have hA : IsStrictPullbackBlowupSeq (pullback.fst g g) (t.baseChange (pullback.fst g g)) t :=
    isStrictPullbackSequenceOfBlowups_baseChange t (pullback.fst g g)
  have hC : IsStrictPullbackBlowupSeq (pullback.snd g g) (t.baseChange (pullback.snd g g)) t :=
    isStrictPullbackSequenceOfBlowups_baseChange t (pullback.snd g g)
  have hAr : IsStrictPullbackBlowupSeq r ((t.baseChange (pullback.fst g g)).baseChange r)
      (t.baseChange (pullback.fst g g)) :=
    isStrictPullbackSequenceOfBlowups_baseChange (t.baseChange (pullback.fst g g)) r
  have hCr : IsStrictPullbackBlowupSeq r ((t.baseChange (pullback.snd g g)).baseChange r)
      (t.baseChange (pullback.snd g g)) :=
    isStrictPullbackSequenceOfBlowups_baseChange (t.baseChange (pullback.snd g g)) r
  have e1 : u.Isomorphic ((t.baseChange (pullback.fst g g)).baseChange r) :=
    h1.isomorphic (hAr.comp hA)
  have e2 : u.Isomorphic ((t.baseChange (pullback.snd g g)).baseChange r) :=
    h2.isomorphic (hCr.comp hC)
  exact exists_isStrictPullback_of_isomorphic_baseChange g t
    (IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic hAr hCr (e1.symm.trans e2))

private theorem isStrictPullback_of_comp_flat_surjective_consolidated263 {X X' V : Scheme.{u}} (φ : X' ⟶ X)
    [Flat φ] (α : V ⟶ X') [Flat α]
    [AlgebraicGeometry.Surjective α] (s : SequenceOfBlowups X') (B : SequenceOfBlowups X) (u : SequenceOfBlowups V)
    (h1 : IsStrictPullbackBlowupSeq α u s) (h2 : IsStrictPullbackBlowupSeq (α ≫ φ) u B) :
    IsStrictPullbackBlowupSeq φ s B := by
  have hbc : IsStrictPullbackBlowupSeq φ (B.baseChange φ) B := isStrictPullbackSequenceOfBlowups_baseChange B φ
  have hbcα : IsStrictPullbackBlowupSeq α ((B.baseChange φ).baseChange α) (B.baseChange φ) :=
    isStrictPullbackSequenceOfBlowups_baseChange (B.baseChange φ) α
  have e : u.Isomorphic ((B.baseChange φ).baseChange α) := h2.isomorphic (hbcα.comp hbc)
  exact hbc.of_isomorphic_pullback (IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic h1 hbcα e).symm

theorem existsGluedBlowupSequence_of_center_ne_top (R : AffineResolutionRule.{u})
    (hR : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
      [QuasiCompact p] [IsReduced Y]
      [IsAffine Y] (i : ℕ),
      i < (R k Y p).length → (R k Y p).center i ≠ ⊤) :
    ExistsGluedBlowupSequence R := by
  intro hcover k hk hk0 Y p hpft hpqc hpred
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace ↥(Spec (CommRingCat.of k)) := inferInstance
  have : CompactSpace ↥Y := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨ι, hι, U, hUaff, hUtop⟩ := exists_finite_affine_cover Y
  have : IsAffine (sigmaOpens Y U) := isAffine_sigmaOpens Y U hUaff
  have : CompactSpace ↥(sigmaOpens Y U) := inferInstance
  have : AlgebraicGeometry.Surjective (sigmaOpensDesc Y U) :=
    surjective_sigmaOpensDesc Y U hUtop
  obtain ⟨V, sV, r, hVaff, hVred, hsft, hsqc, hret, hrsurj, hrq⟩ :=
    exists_affine_etale_cover_pullback_sigmaOpensDesc Y p U hUaff (sigmaOpens Y U)
      (sigmaOpensDesc Y U ≫ p) (sigmaOpensDesc Y U) rfl
  have : Etale
      (r ≫ pullback.fst (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) :=
    etale_comp_fst_pullback_sigmaOpensDesc Y U (sigmaOpens Y U) (sigmaOpensDesc Y U) V r
  have : Etale
      (r ≫ pullback.snd (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) :=
    etale_comp_snd_pullback_sigmaOpensDesc Y U (sigmaOpens Y U) (sigmaOpensDesc Y U) V r
  have : AlgebraicGeometry.Surjective
      (r ≫ pullback.fst (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) :=
    surjective_comp_fst_pullback_sigmaOpensDesc Y U hUtop (sigmaOpens Y U)
      (sigmaOpensDesc Y U) V r
  have : AlgebraicGeometry.Surjective
      (r ≫ pullback.snd (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) :=
    surjective_comp_snd_pullback_sigmaOpensDesc Y U (sigmaOpens Y U)
      (sigmaOpensDesc Y U) V r
  have hq1 : (r ≫ pullback.fst (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) ≫
      (sigmaOpensDesc Y U ≫ p) = sV := by
    rw [Category.assoc]
    exact hrq
  have hq2 : (r ≫ pullback.snd (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) ≫
      (sigmaOpensDesc Y U ≫ p) = sV := by
    have h := comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc Y U (sigmaOpens Y U)
      (sigmaOpensDesc Y U) V r
    have h3 := congrArg (fun m => m ≫ p) h
    simp only [Category.assoc] at h3
    rw [Category.assoc, ← h3]
    exact hrq
  have ht1 := hcover k (sigmaOpens Y U) V (sigmaOpensDesc Y U ≫ p) sV
    (r ≫ pullback.fst (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) hq1
    (fun y => AlgebraicGeometry.Surjective.surj y)
  have ht2 := hcover k (sigmaOpens Y U) V (sigmaOpensDesc Y U ≫ p) sV
    (r ≫ pullback.snd (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) hq2
    (fun y => AlgebraicGeometry.Surjective.surj y)
  obtain ⟨B, hB⟩ := exists_isStrictPullback_of_pullback_cover_consolidated263 (sigmaOpensDesc Y U) r
    (R k (sigmaOpens Y U) (sigmaOpensDesc Y U ≫ p)) (R k V sV) ht1 ht2
  refine ⟨B, hB.center_ne_top_of_forall_center_ne_top
    (fun i hi => hR k (sigmaOpens Y U) (sigmaOpensDesc Y U ≫ p) i hi), ?_⟩
  intro W' q' hq'ft hq'qc hW'red hW'aff φ hφet hφq hφsurj
  have : AlgebraicGeometry.Surjective φ := ⟨hφsurj⟩
  obtain ⟨V', sV', r', hV'aff, hV'red, hs'ft, hs'qc, hr'et, hr'surj, hr'q⟩ :=
    exists_affine_etale_cover_pullback_sigmaOpensDesc Y p U hUaff W' q' φ hφq
  have : Etale (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) :=
    etale_comp_fst_pullback_sigmaOpensDesc Y U W' φ V' r'
  have : Etale (r' ≫ pullback.snd φ (sigmaOpensDesc Y U)) :=
    etale_comp_snd_pullback_sigmaOpensDesc Y U W' φ V' r'
  have : AlgebraicGeometry.Surjective (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) :=
    surjective_comp_fst_pullback_sigmaOpensDesc Y U hUtop W' φ V' r'
  have : AlgebraicGeometry.Surjective (r' ≫ pullback.snd φ (sigmaOpensDesc Y U)) :=
    surjective_comp_snd_pullback_sigmaOpensDesc Y U W' φ V' r'
  have hα : (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) ≫ q' = sV' := by
    rw [Category.assoc]
    exact hr'q
  have hβ : (r' ≫ pullback.snd φ (sigmaOpensDesc Y U)) ≫ (sigmaOpensDesc Y U ≫ p) = sV' := by
    have h := comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc Y U W' φ V' r'
    have h3 := congrArg (fun m => m ≫ p) h
    simp only [Category.assoc] at h3
    rw [Category.assoc, ← h3, hφq]
    exact hr'q
  have hu1 := hcover k W' V' q' sV' (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) hα
    (fun y => AlgebraicGeometry.Surjective.surj y)
  have hu2 := hcover k (sigmaOpens Y U) V' (sigmaOpensDesc Y U ≫ p) sV'
    (r' ≫ pullback.snd φ (sigmaOpensDesc Y U)) hβ
    (fun y => AlgebraicGeometry.Surjective.surj y)
  have hαφ : (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) ≫ φ
      = (r' ≫ pullback.snd φ (sigmaOpensDesc Y U)) ≫ sigmaOpensDesc Y U := by
    simp only [Category.assoc]
    exact comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc Y U W' φ V' r'
  have hfin : IsStrictPullbackBlowupSeq ((r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) ≫ φ)
      (R k V' sV') B := by
    rw [hαφ]
    exact hu2.comp hB
  exact isStrictPullback_of_comp_flat_surjective_consolidated263 φ (r' ≫ pullback.fst φ (sigmaOpensDesc Y U))
    (R k W' q') B (R k V' sV') hu1 hfin


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineEmbeddingIntoAffineSpace
section



private noncomputable def extendAlgHomLastVarZero {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
    {n : ℕ} (f : MvPolynomial (Fin n) k →ₐ[k] A) :
    MvPolynomial (ULift.{u} (Fin (n + 1))) k →ₐ[k] A :=
  MvPolynomial.aeval fun i : ULift.{u} (Fin (n + 1)) =>
    Fin.lastCases (motive := fun _ => A) 0 (fun j => f (MvPolynomial.X j)) i.down

section
variable {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A] {n : ℕ} (f : MvPolynomial (Fin n) k →ₐ[k] A)

private theorem extension_X_last_eq_zero_consolidated118 :
    extendAlgHomLastVarZero f (MvPolynomial.X (ULift.up (Fin.last n))) = 0 := by
  simp [extendAlgHomLastVarZero]

private theorem extension_surjective_consolidated118 (hf : Function.Surjective f) :
    Function.Surjective (extendAlgHomLastVarZero f) := by
  intro a
  obtain ⟨q, rfl⟩ := hf a
  refine ⟨MvPolynomial.rename
    (fun j : Fin n => (ULift.up j.castSucc : ULift.{u} (Fin (n + 1)))) q, ?_⟩
  show MvPolynomial.aeval (fun i : ULift.{u} (Fin (n + 1)) =>
      Fin.lastCases (motive := fun _ => A) 0 (fun j => f (MvPolynomial.X j)) i.down)
      (MvPolynomial.rename (fun j : Fin n => (ULift.up j.castSucc : ULift.{u} (Fin (n + 1)))) q)
      = f q
  rw [MvPolynomial.aeval_rename]
  have h : ((fun i : ULift.{u} (Fin (n + 1)) =>
      Fin.lastCases (motive := fun _ => A) 0 (fun j => f (MvPolynomial.X j)) i.down) ∘
      fun j : Fin n => (ULift.up j.castSucc : ULift.{u} (Fin (n + 1))))
      = fun j : Fin n => f (MvPolynomial.X j) := by
    funext j
    simp
  rw [h]
  exact DFunLike.congr_fun (MvPolynomial.aeval_unique f).symm q


end

private noncomputable def toAffineSpaceOfAlgHom {k : Type u} [Field k] (Y : Scheme.{u}) [IsAffine Y]
    {m : Type u} [Algebra k ↥Γ(Y, ⊤)] (g : MvPolynomial m k →ₐ[k] ↥Γ(Y, ⊤)) :
    Y ⟶ affineSpaceIndexedBy k m :=
  Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
    (AffineSpace.SpecIso m (CommRingCat.of k)).inv

section
variable {k : Type u} [Field k] (Y : Scheme.{u}) [IsAffine Y]

private theorem isoSpec_hom_comp_spec_map_appTop_consolidated118 (p : Y ⟶ Spec (CommRingCat.of k)) :
    Y.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop) = p := by
  have h2 : Y.isoSpec.hom = Y.toSpecΓ := rfl
  rw [h2, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality p,
    ← SpecMap_ΓSpecIso_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.comp_id]

private theorem isClosedImmersion_embedding_and_comp_eq_consolidated118 {m : Type u} [Algebra k ↥Γ(Y, ⊤)] (p : Y ⟶ Spec (CommRingCat.of k))
    (halg : algebraMap k ↥Γ(Y, ⊤)
      = (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom))
    (g : MvPolynomial m k →ₐ[k] ↥Γ(Y, ⊤)) (hg : Function.Surjective g) :
    IsClosedImmersion (toAffineSpaceOfAlgHom Y g) ∧
      toAffineSpaceOfAlgHom Y g ≫ (affineSpaceIndexedBy k m ↘ Spec (CommRingCat.of k)) = p := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hg
  constructor
  · show IsClosedImmersion (Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      (AffineSpace.SpecIso m (CommRingCat.of k)).inv)
    infer_instance
  · show (Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      (AffineSpace.SpecIso m (CommRingCat.of k)).inv) ≫
      (affineSpaceIndexedBy k m ↘ Spec (CommRingCat.of k)) = p
    rw [Category.assoc, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
    have h2 : CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial m k) ≫
        CommRingCat.ofHom g.toRingHom
        = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop := by
      refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
      show g (MvPolynomial.C a) = _
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, halg]
    rw [h2]
    exact isoSpec_hom_comp_spec_map_appTop_consolidated118 Y p


end

private theorem isIrreducible_univ_affineSpaceIndexedBy_consolidated118 (k : Type u) [Field k] (m : Type u) :
    IsIrreducible (Set.univ : Set ↥(affineSpaceIndexedBy k m)) := by
  have h0 : IsIrreducible (Set.univ : Set ↥(Spec (CommRingCat.of (MvPolynomial m k)))) :=
    IrreducibleSpace.isIrreducible_univ (PrimeSpectrum (MvPolynomial m k))
  have h1 := h0.image (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k)).symm)
    (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k)).symm).continuous.continuousOn
  rwa [Set.image_univ,
    (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k)).symm).surjective.range_eq] at h1

private theorem eq_univ_of_mem_irreducibleComponents_of_isIrreducible_univ_consolidated118 {X : Type u} [TopologicalSpace X]
    (h : IsIrreducible (Set.univ : Set X)) {T : Set X} (hT : T ∈ irreducibleComponents X) :
    T = Set.univ :=
  Set.eq_univ_of_univ_subset (hT.2 h (Set.subset_univ T))

private theorem support_ker_ne_univ_of_map_X_eq_zero_consolidated118 {k : Type u} [Field k] (Y : Scheme.{u}) [IsAffine Y]
    {m : Type u} [Algebra k ↥Γ(Y, ⊤)] (g : MvPolynomial m k →ₐ[k] ↥Γ(Y, ⊤))
    (x₀ : m) (hx₀ : g (MvPolynomial.X x₀) = 0) [QuasiCompact (toAffineSpaceOfAlgHom Y g)] :
    ((toAffineSpaceOfAlgHom Y g).ker.support : Set ↥(affineSpaceIndexedBy k m)) ≠ Set.univ := by
  intro hcon
  have hcomp : toAffineSpaceOfAlgHom Y g ≫ (AffineSpace.SpecIso m (CommRingCat.of k)).hom
      = Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) := by
    show (Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      (AffineSpace.SpecIso m (CommRingCat.of k)).inv) ≫
      (AffineSpace.SpecIso m (CommRingCat.of k)).hom = _
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hmem0 : ∀ w : PrimeSpectrum ↥Γ(Y, ⊤),
      (MvPolynomial.X x₀ : MvPolynomial m k) ∈
        ((Spec.map (CommRingCat.ofHom g.toRingHom)).base w).asIdeal := by
    intro w
    show g (MvPolynomial.X x₀) ∈ w.asIdeal
    rw [hx₀]
    exact Ideal.zero_mem _
  obtain ⟨v, hv, hvcont, hvsurj⟩ :
      ∃ v : ↥(affineSpaceIndexedBy k m) → PrimeSpectrum (MvPolynomial m k),
        (∀ y : ↥Y, v ((toAffineSpaceOfAlgHom Y g).base y)
            = (Spec.map (CommRingCat.ofHom g.toRingHom)).base (Y.isoSpec.hom.base y)) ∧
          Continuous v ∧ Function.Surjective v := by
    refine ⟨fun x => (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k))) x, ?_, ?_, ?_⟩
    · intro y
      exact congrArg
        (fun φ : Y ⟶ Spec (CommRingCat.of (MvPolynomial m k)) => φ.base y) hcomp
    · exact (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k))).continuous
    · exact (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k))).surjective
  have hrange : ∀ y : ↥Y,
      (MvPolynomial.X x₀ : MvPolynomial m k) ∈ (v ((toAffineSpaceOfAlgHom Y g).base y)).asIdeal := by
    intro y
    rw [hv y]
    exact hmem0 _
  have hsub : Set.range (toAffineSpaceOfAlgHom Y g).base ⊆
      v ⁻¹' PrimeSpectrum.zeroLocus {(MvPolynomial.X x₀ : MvPolynomial m k)} := by
    rintro _ ⟨y, rfl⟩
    have : v ((toAffineSpaceOfAlgHom Y g).base y) ∈
        PrimeSpectrum.zeroLocus {(MvPolynomial.X x₀ : MvPolynomial m k)} := by
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      exact hrange y
    exact this
  have hsupp : ((toAffineSpaceOfAlgHom Y g).ker.support : Set ↥(affineSpaceIndexedBy k m))
      = closure (Set.range (toAffineSpaceOfAlgHom Y g).base) := Scheme.Hom.support_ker _
  have huniv : (Set.univ : Set ↥(affineSpaceIndexedBy k m)) ⊆
      v ⁻¹' PrimeSpectrum.zeroLocus {(MvPolynomial.X x₀ : MvPolynomial m k)} := by
    rw [← hcon, hsupp]
    exact closure_minimal hsub ((PrimeSpectrum.isClosed_zeroLocus _).preimage hvcont)
  obtain ⟨ξ, hξ⟩ := hvsurj ⟨⊥, Ideal.isPrime_bot⟩
  have hmem : ξ ∈ v ⁻¹' PrimeSpectrum.zeroLocus {(MvPolynomial.X x₀ : MvPolynomial m k)} :=
    huniv (Set.mem_univ ξ)
  rw [Set.mem_preimage, hξ, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hmem
  have h6 : (MvPolynomial.X x₀ : MvPolynomial m k) = 0 := Ideal.mem_bot.mp hmem
  have h7 : (1 : k) = 0 := by
    have h8 := congrArg (fun p => AddMonoidAlgebra.coeff p (Finsupp.single x₀ 1)) h6
    simp at h8
  exact one_ne_zero h7

theorem affineEmbedsIntoAffineSpace : AffineEmbedsIntoAffineSpace.{u} := by
  intro k _ Y _ p _
  have hft : RingHom.FiniteType (p.appTop).hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (f := p)).mp inferInstance
  have hiso : Function.Surjective ⇑((Scheme.ΓSpecIso (CommRingCat.of k)).inv) := by
    intro x
    exact ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom x, by simp⟩
  have hφ : RingHom.FiniteType
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom) := by
    rw [CommRingCat.hom_comp]
    exact hft.comp (RingHom.FiniteType.of_surjective _ hiso)
  let _ : Algebra k ↥Γ(Y, ⊤) :=
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom).toAlgebra
  have halg : algebraMap k ↥Γ(Y, ⊤)
      = (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom) := rfl
  have hfta : Algebra.FiniteType k ↥Γ(Y, ⊤) := hφ
  obtain ⟨n, f, hfsurj⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp hfta
  obtain ⟨hci, hover⟩ := isClosedImmersion_embedding_and_comp_eq_consolidated118 Y p halg (extendAlgHomLastVarZero f) (extension_surjective_consolidated118 f hfsurj)
  have := hci
  refine ⟨n + 1, toAffineSpaceOfAlgHom Y (extendAlgHomLastVarZero f), hci, ?_, hover⟩
  have hne := support_ker_ne_univ_of_map_X_eq_zero_consolidated118 Y (extendAlgHomLastVarZero f) (ULift.up (Fin.last n)) (extension_X_last_eq_zero_consolidated118 f)
  have hirr := isIrreducible_univ_affineSpaceIndexedBy_consolidated118 k (ULift.{u} (Fin (n + 1)))
  have key : ∀ T ∈ irreducibleComponents ↥(affineSpaceIndexedBy k (ULift.{u} (Fin (n + 1)))),
      ¬ T ⊆ ((toAffineSpaceOfAlgHom Y (extendAlgHomLastVarZero f)).ker.support :
        Set ↥(affineSpaceIndexedBy k (ULift.{u} (Fin (n + 1))))) := by
    intro T hT hsubT
    refine hne (Set.eq_univ_of_univ_subset ?_)
    rw [← eq_univ_of_mem_irreducibleComponents_of_isIrreducible_univ_consolidated118 hirr hT]
    exact hsubT
  exact key

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineSpaceSmooth
section



section
variable (k : Type u) [Field k] (n : ℕ)

private theorem algebra_smooth_mvPolynomial_consolidated117 :
    Algebra.Smooth k (MvPolynomial (ULift.{u} (Fin n)) k) :=
  ⟨inferInstance, inferInstance⟩

private theorem ringHom_smooth_algebraMap_mvPolynomial_consolidated117 :
    RingHom.Smooth (algebraMap k (MvPolynomial (ULift.{u} (Fin n)) k)) :=
  RingHom.smooth_algebraMap.mpr (algebra_smooth_mvPolynomial_consolidated117 k n)

private theorem specIso_inv_comp_affineSpaceIndexedByToSpec_consolidated117 :
    (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).inv ≫
        affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin n)) k)) :=
  AffineSpace.SpecIso_inv_over _

private theorem affineSpaceIndexedByToSpec_eq_consolidated117 :
    affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) =
      (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).hom ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin n)) k)) := by
  rw [← specIso_inv_comp_affineSpaceIndexedByToSpec_consolidated117 k n, Iso.hom_inv_id_assoc]


end

theorem affineSpaceIsSmooth : AffineSpaceIsSmooth.{u} := by
  intro k _ n
  have hC : Smooth
      (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin n)) k))) :=
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @Smooth)).mpr (ringHom_smooth_algebraMap_mvPolynomial_consolidated117 k n)
  rw [affineSpaceIndexedByToSpec_eq_consolidated117 k n]
  infer_instance

theorem nilIsStrictNormalCrossingsOnAffineSpace : NilIsStrictNormalCrossingsOnAffineSpace.{u} := by
  intro k _ n
  refine ⟨by simp, fun x => ⟨⊤, trivial, n,
    ⟨(⊤ : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens).ι, rfl, ?_⟩,
    fun _ => none, by simp, by simp, by simp⟩⟩
  infer_instance

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
section

open Opposite TopologicalSpace


variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ}

theorem smooth_of_iSup_eq_top {W Y : Scheme.{u}} (f : W ⟶ Y) {ι : Sort*} (U : ι → W.Opens)
    (hU : iSup U = ⊤) (h : ∀ i, Smooth ((U i).ι ≫ f)) : Smooth f := by
  have i3 : HasRingHomProperty (@Smooth.{u})
      (fun {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) => g.Smooth) := inferInstance
  have hloc : IsZariskiLocalAtSource (@Smooth.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ i3
  have hVtop : (⨆ i : PLift ι, U i.down) = ⊤ := by
    rw [← hU]
    exact le_antisymm (iSup_le fun i => le_iSup U i.down)
      (iSup_le fun i => le_iSup (fun j : PLift ι => U j.down) (PLift.up i))
  exact (IsZariskiLocalAtSource.iff_of_iSup_eq_top (fun i : PLift ι => U i.down) hVtop).mpr
    fun i => h i.down

theorem restrictIdeal_eq_restrict_coordIdeal_of_le {U V : X.Opens} (hVU : V ≤ U) (c : EtaleChart p U m)
    (Z : X.IdealSheafData) (S : Finset (Fin m)) (h : restrictIdeal Z U = c.coordIdeal S) :
    restrictIdeal Z V = (c.restrict hVU).coordIdeal S := by
  have h' : Z.comap U.ι = (coordSubspaceIdeal k m S).comap c.map := by
    rw [← restrictIdeal_eq_comap_ι, h, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.restrict_map,
    Scheme.IdealSheafData.comap_comp, ← h', ← Scheme.IdealSheafData.comap_comp,
    Scheme.homOfLE_ι]

theorem restrictIdeal_eq_top_of_le {Y : Scheme.{u}} (Z : Y.IdealSheafData) {U V : Y.Opens}
    (hVU : V ≤ U) (h : restrictIdeal Z U = ⊤) : restrictIdeal Z V = ⊤ := by
  rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal Z hVU, h, Scheme.IdealSheafData.comap_top]

section
variable (Z : X.IdealSheafData)

theorem smooth_ι_comp_subschemeι_comp_of_eq_coordIdeal {U : X.Opens}
    (hU : IsAffineOpen U) (c : EtaleChart p U m) (S : Finset (Fin m))
    (h : restrictIdeal Z U = c.coordIdeal S) :
    Smooth ((Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p)) := by
  have hsm : Smooth (affineSpaceFinToSpec k (m - S.card)) := affineSpaceIsSmooth ..
  have het : Etale (c.restrictToSubscheme hU Z S h).map :=
    (c.restrictToSubscheme hU Z S h).isEtale
  have hsm2 : Smooth (c.restrictToSubscheme hU Z S h).map := inferInstance
  have hc : (c.restrictToSubscheme hU Z S h).map ≫ affineSpaceFinToSpec k (m - S.card)
      = (Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p) :=
    (c.restrictToSubscheme hU Z S h).comp_struct
  rw [← hc]
  infer_instance

theorem smooth_subschemeι_comp_of_locally_eq_coordIdeal (h : ∀ x : X, x ∈ Z.support →
      ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n) (S : Finset (Fin n)),
        restrictIdeal Z U = c.coordIdeal S) :
    Smooth (Z.subschemeι ≫ p) := by
  classical
  have i3 : HasRingHomProperty (@Smooth.{u})
      (fun {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) => g.Smooth) := inferInstance
  have hloc : IsZariskiLocalAtSource (@Smooth.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ i3
  have key : ∀ y : ↥Z.subscheme, ∃ W : (Z.subscheme).Opens,
      y ∈ W ∧ Smooth (W.ι ≫ (Z.subschemeι ≫ p)) := by
    intro y
    have hy : Z.subschemeι.base y ∈ Z.support := by
      have hmem : Z.subschemeι.base y ∈ Set.range Z.subschemeι.base := Set.mem_range_self y
      simpa using hmem
    obtain ⟨U, hxU, n, c, S, hS⟩ := h _ hy
    obtain ⟨V, hV, hxV, hVU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU
    have hV' : IsAffineOpen V := hV
    refine ⟨Z.subschemeι ⁻¹ᵁ V, hxV, ?_⟩
    exact smooth_ι_comp_subschemeι_comp_of_eq_coordIdeal Z hV' (c.restrict hVU) S
      (restrictIdeal_eq_restrict_coordIdeal_of_le hVU c Z S hS)
  choose W hyW hWsm using key
  have hsup : (⨆ y, W y) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hyW y⟩
  exact (IsZariskiLocalAtSource.iff_of_iSup_eq_top W hsup).mpr hWsm

theorem smooth_subschemeι_comp_of_hasStrictNormalCrossingsWith (E : List X.IdealSheafData)
    (h : HasStrictNormalCrossingsWith p Z E) : Smooth (Z.subschemeι ≫ p) := by
  unfold HasStrictNormalCrossingsWith at h
  refine smooth_subschemeι_comp_of_locally_eq_coordIdeal Z ?_
  intro x hx
  obtain ⟨U, hxU, n, c, a, S, -, -, -, hS⟩ := h x hx
  exact ⟨U, hxU, n, c, S, hS⟩


end

private theorem algebraMap_mem_nonZeroDivisors_of_flat_consolidated159 {R A : Type u} [CommRing R]
    [CommRing A] [Algebra R A] [Module.Flat R A] {r : R} (hr : r ∈ nonZeroDivisors R) :
    algebraMap R A r ∈ nonZeroDivisors A := by
  have hreg : IsSMulRegular A r := Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  have key : ∀ x : A, algebraMap R A r * x = 0 → x = 0 := by
    intro x hx
    have hsm : r • x = r • (0 : A) := by
      rw [smul_zero, Algebra.smul_def]
      exact hx
    exact hreg hsm
  rw [mem_nonZeroDivisors_iff]
  exact ⟨key, fun x hx => key x (by rw [mul_comm]; exact hx)⟩

theorem coord_mem_nonZeroDivisors {U : X.Opens} (hU : IsAffineOpen U) (c : EtaleChart p U m)
    (j : Fin m) : c.coord j ∈ nonZeroDivisors ↑(X.presheaf.obj (op U)) := by
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
    algebraMap_mem_nonZeroDivisors_of_flat_consolidated159 hXnzd
  rw [halg] at key
  rwa [c.coordRingHom_X j] at key

section
variable {σ : Type u} {k : Type u} [Field k] {j s : σ} (hjs : j ≠ s)
include hjs

private theorem mem_span_X_of_X_mul_mem_consolidated159 (r : MvPolynomial σ k)
    (hr : MvPolynomial.X s * r ∈ Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)}) :
    r ∈ Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)} := by
  classical
  obtain ⟨ψ, hψC, hψXj, hψXi⟩ : ∃ ψ : MvPolynomial σ k →+* MvPolynomial σ k,
      (∀ a : k, ψ (MvPolynomial.C a) = MvPolynomial.C a) ∧
        ψ (MvPolynomial.X j) = 0 ∧
        ∀ i : σ, i ≠ j → ψ (MvPolynomial.X i) = MvPolynomial.X i := by
    refine ⟨MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* MvPolynomial σ k)
        (fun i : σ => if i = j then (0 : MvPolynomial σ k) else MvPolynomial.X i), ?_, ?_, ?_⟩
    · intro a
      simp
    · simp
    · intro i hi
      simp [hi]
  have hXjmem : (MvPolynomial.X j : MvPolynomial σ k)
      ∈ Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)} := Ideal.mem_span_singleton_self _
  have key : (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)})).comp ψ
      = Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)}) := by
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
  have hXs : (MvPolynomial.X s : MvPolynomial σ k) ≠ 0 := MvPolynomial.X_ne_zero _
  have hψr : ψ r = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hXs
    · exact h
  have h3 := DFunLike.congr_fun key r
  rw [RingHom.comp_apply, hψr, map_zero] at h3
  exact Ideal.Quotient.eq_zero_iff_mem.mp h3.symm

private theorem eq_of_mk_X_mul_eq_quotient_span_X_consolidated159 (a b : MvPolynomial σ k ⧸ Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)})
    (h : (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)}))
            (MvPolynomial.X s) * a
        = (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)}))
            (MvPolynomial.X s) * b) : a = b := by
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub] at h
  exact Ideal.Quotient.eq.mpr (mem_span_X_of_X_mul_mem_consolidated159 hjs (a' - b') h)


end

private theorem mem_map_of_mul_mem_of_etale_consolidated159 {P A : Type u} [CommRing P] [CommRing A]
    {f : P →+* A} (hf : f.Etale) (I : Ideal P) (w : P)
    (hw : ∀ a b : P ⧸ I,
      (Ideal.Quotient.mk I) w * a = (Ideal.Quotient.mk I) w * b → a = b)
    (x : A) (hx : f w * x ∈ Ideal.map f I) : x ∈ Ideal.map f I := by
  have hg : (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).Etale :=
    etale_quotientMap hf I
  let _ : Algebra (P ⧸ I) (A ⧸ Ideal.map f I) :=
    (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).toAlgebra
  have : Algebra.Etale (P ⧸ I) (A ⧸ Ideal.map f I) := hg
  have : Module.Flat (P ⧸ I) (A ⧸ Ideal.map f I) := inferInstance
  have hreg : IsSMulRegular (P ⧸ I) ((Ideal.Quotient.mk I) w) := by
    intro a b h
    exact hw a b (by simpa only [smul_eq_mul] using h)
  have hregB : IsSMulRegular (A ⧸ Ideal.map f I) ((Ideal.Quotient.mk I) w) := hreg.of_flat
  have hy : (Ideal.Quotient.mk I) w • (Ideal.Quotient.mk (Ideal.map f I)) x
      = (Ideal.Quotient.mk I) w • (0 : A ⧸ Ideal.map f I) := by
    rw [smul_zero]
    show (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map) ((Ideal.Quotient.mk I) w) *
        (Ideal.Quotient.mk (Ideal.map f I)) x = 0
    rw [Ideal.quotientMap_mk, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hregB hy)

theorem mem_span_coord_of_coord_mul_mem {U : X.Opens} (hU : IsAffineOpen U) (c : EtaleChart p U m)
    {j s : Fin m} (hjs : j ≠ s) (x : ↑(X.presheaf.obj (op U)))
    (hx : c.coord s * x ∈ Ideal.span {c.coord j}) : x ∈ Ideal.span {c.coord j} := by
  classical
  have hmapspan : Ideal.map c.coordRingHom
      (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k)})
      = Ideal.span {c.coord j} := by
    rw [Ideal.map_span, Set.image_singleton, c.coordRingHom_X]
  have hju : (ULift.up j : ULift.{u} (Fin m)) ≠ ULift.up s := by
    intro h
    exact hjs (congrArg ULift.down h)
  have hu : ∀ a b : MvPolynomial (ULift.{u} (Fin m)) k ⧸
        Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k)},
      (Ideal.Quotient.mk
          (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k)}))
          (MvPolynomial.X (ULift.up s)) * a
        = (Ideal.Quotient.mk
          (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k)}))
          (MvPolynomial.X (ULift.up s)) * b → a = b :=
    fun a b h => eq_of_mk_X_mul_eq_quotient_span_X_consolidated159 hju a b h
  have hx' : c.coordRingHom (MvPolynomial.X (ULift.up s)) * x
      ∈ Ideal.map c.coordRingHom
          (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k)}) := by
    rw [hmapspan, c.coordRingHom_X]
    exact hx
  have hfin := mem_map_of_mul_mem_of_etale_consolidated159 (c.coordRingHom_etale hU)
      (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k)})
      (MvPolynomial.X (ULift.up s)) hu x hx'
  rw [hmapspan] at hfin
  exact hfin

section
variable {σ : Type u} {k : Type u} [Field k] {j s : σ} (hjs : j ≠ s)
include hjs

private theorem X_pow_dvd_of_X_pow_dvd_X_mul_consolidated159 :
    ∀ (n : ℕ) (r : MvPolynomial σ k),
      (MvPolynomial.X j : MvPolynomial σ k) ^ n ∣ MvPolynomial.X s * r →
        (MvPolynomial.X j : MvPolynomial σ k) ^ n ∣ r := by
  intro n
  induction n with
  | zero =>
    intro r _
    rw [pow_zero]
    exact one_dvd r
  | succ n ih =>
    intro r hr
    have hXne : (MvPolynomial.X j : MvPolynomial σ k) ≠ 0 := MvPolynomial.X_ne_zero _
    have h1 : (MvPolynomial.X j : MvPolynomial σ k) ∣ MvPolynomial.X s * r :=
      dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero n)) hr
    have h2 : (MvPolynomial.X j : MvPolynomial σ k) ∣ r :=
      Ideal.mem_span_singleton.mp
        (mem_span_X_of_X_mul_mem_consolidated159 hjs r (Ideal.mem_span_singleton.mpr h1))
    obtain ⟨r', rfl⟩ := h2
    have h3 : (MvPolynomial.X j : MvPolynomial σ k) * MvPolynomial.X j ^ n ∣
        MvPolynomial.X j * (MvPolynomial.X s * r') := by
      have e1 : (MvPolynomial.X j : MvPolynomial σ k) * (MvPolynomial.X s * r')
          = MvPolynomial.X s * (MvPolynomial.X j * r') := by ring
      have e2 : (MvPolynomial.X j : MvPolynomial σ k) * MvPolynomial.X j ^ n
          = MvPolynomial.X j ^ (n + 1) := by ring
      rw [e1, e2]
      exact hr
    have h4 : (MvPolynomial.X j : MvPolynomial σ k) ^ n ∣ MvPolynomial.X s * r' :=
      (mul_dvd_mul_iff_left hXne).mp h3
    have h5 := ih r' h4
    have e3 : (MvPolynomial.X j : MvPolynomial σ k) ^ (n + 1)
        = MvPolynomial.X j * MvPolynomial.X j ^ n := by ring
    rw [e3]
    exact mul_dvd_mul_left _ h5

private theorem eq_of_mk_X_mul_eq_quotient_span_X_pow_consolidated159 (n : ℕ)
    (a b : MvPolynomial σ k ⧸ Ideal.span {(MvPolynomial.X j : MvPolynomial σ k) ^ n})
    (h : (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ k) ^ n}))
            (MvPolynomial.X s) * a
        = (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ k) ^ n}))
            (MvPolynomial.X s) * b) : a = b := by
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub] at h
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr
    (X_pow_dvd_of_X_pow_dvd_X_mul_consolidated159 hjs n (a' - b') (Ideal.mem_span_singleton.mp h)))


end

theorem mem_span_coord_pow_of_mul_mem {U : X.Opens} (hU : IsAffineOpen U) (c : EtaleChart p U m)
    {j s : Fin m} (hjs : j ≠ s) (n : ℕ) (x : ↑(X.presheaf.obj (op U)))
    (hx : c.coord s * x ∈ Ideal.span {c.coord j ^ n}) :
    x ∈ Ideal.span {c.coord j ^ n} := by
  classical
  have hmapspan : Ideal.map c.coordRingHom
      (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n})
      = Ideal.span {c.coord j ^ n} := by
    rw [Ideal.map_span, Set.image_singleton, map_pow, c.coordRingHom_X]
  have hju : (ULift.up j : ULift.{u} (Fin m)) ≠ ULift.up s := by
    intro h
    exact hjs (congrArg ULift.down h)
  have hu : ∀ a b : MvPolynomial (ULift.{u} (Fin m)) k ⧸
        Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n},
      (Ideal.Quotient.mk
          (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n}))
          (MvPolynomial.X (ULift.up s)) * a
        = (Ideal.Quotient.mk
          (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n}))
          (MvPolynomial.X (ULift.up s)) * b → a = b :=
    fun a b h => eq_of_mk_X_mul_eq_quotient_span_X_pow_consolidated159 hju n a b h
  have hx' : c.coordRingHom (MvPolynomial.X (ULift.up s)) * x
      ∈ Ideal.map c.coordRingHom
          (Ideal.span
            {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n}) := by
    rw [hmapspan, c.coordRingHom_X]
    exact hx
  have hfin := mem_map_of_mul_mem_of_etale_consolidated159 (c.coordRingHom_etale hU)
      (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n})
      (MvPolynomial.X (ULift.up s)) hu x hx'
  rw [hmapspan] at hfin
  exact hfin

section
variable {Y : Scheme.{u}} (V : Y.Opens) (hle : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V)

private theorem appLE_ι_top_eq_topIso_inv_consolidated159 :
    V.ι.appLE V ⊤ hle = V.topIso.inv := by
  simp
  rfl

private theorem bijective_appLE_ι_top_consolidated159 :
    Function.Bijective (CommRingCat.Hom.hom (V.ι.appLE V ⊤ hle)) := by
  rw [appLE_ι_top_eq_topIso_inv_consolidated159 V hle]
  exact V.topIso.commRingCatIsoToRingEquiv.symm.bijective


end

private theorem ideal_eq_top_of_restrictIdeal_eq_top_consolidated159 {Y : Scheme.{u}} (D : Y.IdealSheafData)
    {V : Y.Opens} (hV : IsAffineOpen V) (htop : restrictIdeal D V = ⊤) :
    D.ideal ⟨V, hV⟩ = ⊤ := by
  have : IsAffine V.toScheme := hV
  have hle : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := V.ι_preimage_self.ge
  have key := Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ hle
  rw [← restrictIdeal_eq_comap_ι, htop] at key
  have h0 : ((⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩) = ⊤ := by
    simp
  rw [h0] at key
  have key2 : Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ hle)) (D.ideal ⟨V, hV⟩) = ⊤ :=
    key.symm
  have hcomap : Ideal.comap (CommRingCat.Hom.hom (V.ι.appLE V ⊤ hle))
      (Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ hle)) (D.ideal ⟨V, hV⟩))
      = D.ideal ⟨V, hV⟩ := by
    apply Ideal.comap_map_of_bijective
    exact bijective_appLE_ι_top_consolidated159 V hle
  rw [← hcomap, key2, Ideal.comap_top]

theorem isLocallyGeneratedByNonZeroDivisor_of_locally_coordIdeal (D : X.IdealSheafData)
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j}) :
    Blowup.IsLocallyGeneratedByNonZeroDivisor D := by
  intro x
  obtain ⟨U, hxU, n, c, hc⟩ := h x
  obtain ⟨V, hV, hxV, hVU⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hxU
  obtain ⟨f, hf, hfspan⟩ :
      ∃ f : ↑(X.presheaf.obj (op V)), f ∈ nonZeroDivisors ↑(X.presheaf.obj (op V)) ∧
        D.ideal ⟨V, hV⟩ = Ideal.span {f} := by
    rcases hc with htop | ⟨j, hj⟩
    · refine ⟨1, one_mem _, ?_⟩
      rw [ideal_eq_top_of_restrictIdeal_eq_top_consolidated159 D hV (restrictIdeal_eq_top_of_le D hVU htop),
        Ideal.span_singleton_one]
    · refine ⟨(c.restrict hVU).coord j, coord_mem_nonZeroDivisors hV (c.restrict hVU) j, ?_⟩
      rw [(c.restrict hVU).ideal_eq_span_coord hV D {j}
        (restrictIdeal_eq_restrict_coordIdeal_of_le hVU c D {j} hj), Finset.coe_singleton,
        Set.image_singleton]
  exact ⟨⟨V, hV⟩, f, hxV, hf, hfspan⟩

private theorem notMem_support_of_mem_of_restrictIdeal_eq_top_consolidated159 {Y : Scheme.{u}}
    (I : Y.IdealSheafData) {U : Y.Opens} (h : restrictIdeal I U = ⊤) {x : Y} (hxU : x ∈ U) :
    x ∉ I.support := by
  intro hx
  have h1 : (⟨x, hxU⟩ : ↥U) ∈ (I.comap U.ι).support := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
    exact hx
  rw [← restrictIdeal_eq_comap_ι, h, AlgebraicGeometry.Scheme.IdealSheafData.support_top] at h1
  have h2 : (⟨x, hxU⟩ : ↥U) ∈ ((⊥ : TopologicalSpace.Closeds ↥U) : Set ↥U) := h1
  simp at h2

theorem isSmoothDivisor_of_locally_coordIdeal (D : X.IdealSheafData)
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j}) :
    IsSmoothDivisor p D := by
  rw [isSmoothDivisor_iff]
  refine ⟨isLocallyGeneratedByNonZeroDivisor_of_locally_coordIdeal D h, smooth_subschemeι_comp_of_locally_eq_coordIdeal D ?_⟩
  intro x hx
  obtain ⟨U, hxU, n, c, hc⟩ := h x
  rcases hc with hc | ⟨j, hj⟩
  · exact absurd hx (notMem_support_of_mem_of_restrictIdeal_eq_top_consolidated159 D hc hxU)
  · exact ⟨U, hxU, n, c, {j}, hj⟩

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartFieldBaseChange
section

open CategoryTheory.Limits TopologicalSpace Opposite

section

section

variable {k K : Type u} [Field k] [Field K] {φ : CommRingCat.of k ⟶ CommRingCat.of K}
  {X Y : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of K)}
  {f : Y ⟶ X}

theorem smooth_of_isPullback_field [Smooth p]
    (hsq : IsPullback q f (Spec.map φ) p) :
    Smooth q := by
  have hp : Smooth p := inferInstance
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Smooth)
    hsq.flip hp

def baseChangeCoords (g : Y ⟶ X) {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) :
    ULift.{u} (Fin m) → Γ(↑(g ⁻¹ᵁ U), ⊤) :=
  fun i => (g ⁻¹ᵁ U).topIso.inv.hom ((g.appLE U (g ⁻¹ᵁ U) le_rfl).hom (c.coord i.down))

theorem baseChangeCoords_apply (g : Y ⟶ X) {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (i : ULift.{u} (Fin m)) :
    baseChangeCoords g c i =
      (g ⁻¹ᵁ U).topIso.inv.hom ((g.appLE U (g ⁻¹ᵁ U) le_rfl).hom (c.coord i.down)) :=
  rfl

private theorem presheafMap_eq_id_consolidated183 {Z : Scheme.{u}} {A : (Z.Opens)ᵒᵖ} (g : A ⟶ A) :
    Z.presheaf.map g = 𝟙 _ := by
  obtain rfl : g = 𝟙 A := Subsingleton.elim g (𝟙 A)
  exact Z.presheaf.map_id A

private theorem appLE_top_eq_appTop_consolidated183 {Z W : Scheme.{u}} (g : Z ⟶ W)
    (e : (⊤ : Z.Opens) ≤ g ⁻¹ᵁ ⊤) : g.appLE ⊤ ⊤ e = g.appTop := by
  have h1 : Z.presheaf.map (homOfLE e).op = 𝟙 Γ(Z, ⊤) := presheafMap_eq_id_consolidated183 _
  calc g.appLE ⊤ ⊤ e = g.app ⊤ ≫ Z.presheaf.map (homOfLE e).op := rfl
    _ = g.appTop := by rw [h1]; exact Category.comp_id _

private theorem ι_appLE_eq_topIso_inv_consolidated183 {Z : Scheme.{u}} (A : Z.Opens)
    (e : (⊤ : A.toScheme.Opens) ≤ A.ι ⁻¹ᵁ A) : A.ι.appLE A ⊤ e = A.topIso.inv := by
  simp
  exact AlgebraicGeometry.Scheme.presheaf_map_eq_of_parallel _ _ _

private theorem appLE_comp_appLE_consolidated183 {X₁ X₂ X₃ : Scheme.{u}} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃)
    {A : X₃.Opens} {B : X₂.Opens} {C : X₁.Opens} (e₁ : B ≤ b ⁻¹ᵁ A) (e₂ : C ≤ a ⁻¹ᵁ B)
    (e₃ : C ≤ (a ≫ b) ⁻¹ᵁ A) :
    b.appLE A B e₁ ≫ a.appLE B C e₂ = (a ≫ b).appLE A C e₃ := by
  rw [Scheme.Hom.appLE_comp_appLE]

private theorem appTop_topIso_inv_of_comp_eq_consolidated183 {Z W : Scheme.{u}} (g : Z ⟶ W) {A : W.Opens}
    {B : Z.Opens} (e : B ≤ g ⁻¹ᵁ A) (r : B.toScheme ⟶ A.toScheme) (hr : r ≫ A.ι = B.ι ≫ g)
    (x : Γ(W, A)) :
    r.appTop.hom (A.topIso.inv.hom x) = B.topIso.inv.hom ((g.appLE A B e).hom x) := by
  have eA : (⊤ : A.toScheme.Opens) ≤ A.ι ⁻¹ᵁ A := by intro z _; exact z.2
  have eB : (⊤ : B.toScheme.Opens) ≤ B.ι ⁻¹ᵁ B := by intro z _; exact z.2
  have eTop : (⊤ : B.toScheme.Opens) ≤ r ⁻¹ᵁ (⊤ : A.toScheme.Opens) := by simp
  have e4 : (⊤ : B.toScheme.Opens) ≤ (B.ι ≫ g) ⁻¹ᵁ A := by intro z _; exact e z.2
  have e3 : (⊤ : B.toScheme.Opens) ≤ (r ≫ A.ι) ⁻¹ᵁ A := by rw [hr]; exact e4
  have hgen : ∀ m₁ m₂ : B.toScheme ⟶ W, m₁ = m₂ →
      ∀ (k₁ : (⊤ : B.toScheme.Opens) ≤ m₁ ⁻¹ᵁ A) (k₂ : (⊤ : B.toScheme.Opens) ≤ m₂ ⁻¹ᵁ A),
        m₁.appLE A ⊤ k₁ = m₂.appLE A ⊤ k₂ := by
    rintro m₁ m₂ rfl _ _
    rfl
  have key : A.topIso.inv ≫ r.appTop = g.appLE A B e ≫ B.topIso.inv := by
    rw [← ι_appLE_eq_topIso_inv_consolidated183 A eA, ← ι_appLE_eq_topIso_inv_consolidated183 B eB,
      ← appLE_top_eq_appTop_consolidated183 r eTop, appLE_comp_appLE_consolidated183 r A.ι eA eTop e3,
      appLE_comp_appLE_consolidated183 B.ι g e eB e4]
    exact hgen _ _ hr e3 e4
  have h2 := congrArg (fun ψ : Γ(W, A) ⟶ Γ(B.toScheme, ⊤) => ψ.hom x) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  exact h2

theorem etale_homOfVector_baseChangeCoords (hsq : IsPullback q f (Spec.map φ) p)
    {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) :
    Etale
      (AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c)) := by
  have hrι : (f ∣_ U) ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := morphismRestrict_ι f U
  have sq1 : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι f := isPullback_morphismRestrict f U
  have sqOuter : IsPullback ((f ⁻¹ᵁ U).ι ≫ q) (f ∣_ U) (Spec.map φ) (U.ι ≫ p) :=
    sq1.flip.paste_horiz hsq
  have hover : AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c)
      ≫ affineSpaceFinToSpec K m = (f ⁻¹ᵁ U).ι ≫ q := AffineSpace.homOfVector_over _ _
  have hmo : AffineSpace.map (ULift.{u} (Fin m)) (Spec.map φ) ≫ affineSpaceFinToSpec k m
      = affineSpaceFinToSpec K m ≫ Spec.map φ := by simp
  have tsq : IsPullback (affineSpaceFinToSpec K m)
      (AffineSpace.map (ULift.{u} (Fin m)) (Spec.map φ)) (Spec.map φ) (affineSpaceFinToSpec k m) :=
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin m)) (Spec.map φ)).flip
  have hL2 : (AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c)
        ≫ AffineSpace.map (ULift.{u} (Fin m)) (Spec.map φ)) ≫ affineSpaceFinToSpec k m
      = (f ⁻¹ᵁ U).ι ≫ q ≫ Spec.map φ := by
    rw [Category.assoc, hmo, ← Category.assoc, hover, Category.assoc]
  have hR2 : ((f ∣_ U) ≫ c.map) ≫ affineSpaceFinToSpec k m = (f ⁻¹ᵁ U).ι ≫ f ≫ p := by
    rw [Category.assoc, c.comp_struct, ← Category.assoc, hrι, Category.assoc]
  have ecomm : AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c)
      ≫ AffineSpace.map (ULift.{u} (Fin m)) (Spec.map φ) = (f ∣_ U) ≫ c.map := by
    refine AffineSpace.hom_ext ?_ ?_
    · refine hL2.trans ?_
      rw [hsq.w]
      exact hR2.symm
    · intro i
      have hmc : (AffineSpace.map (ULift.{u} (Fin m)) (Spec.map φ)).appTop.hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) i)
          = AffineSpace.coord (Spec (CommRingCat.of K)) i := by simp
      have hhv : (AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q)
            (baseChangeCoords f c)).appTop.hom
              (AffineSpace.coord (Spec (CommRingCat.of K)) i)
          = baseChangeCoords f c i :=
        AffineSpace.homOfVector_appTop_coord _ _ i
      have hc : c.map.appTop.hom (AffineSpace.coord (Spec (CommRingCat.of k)) i)
          = U.topIso.inv.hom (c.coord i.down) := by
        rw [EtaleChart.coord_def]
        exact (CommRingCat.inv_hom_apply ..).symm
      simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
        RingHom.comp_apply]
      rw [hmc, hhv, hc, baseChangeCoords_apply]
      exact (appTop_topIso_inv_of_comp_eq_consolidated183 (A := U) (B := f ⁻¹ᵁ U) f le_rfl (f ∣_ U) hrι
        (c.coord i.down)).symm
  have sqBig : IsPullback
      (AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c)
        ≫ affineSpaceFinToSpec K m) (f ∣_ U) (Spec.map φ) (c.map ≫ affineSpaceFinToSpec k m) := by
    rw [hover, c.comp_struct]
    exact sqOuter
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Etale) (sqBig.of_right ecomm tsq).flip c.isEtale

def EtaleChart.baseChange {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (hsq : IsPullback q f (Spec.map φ) p) : EtaleChart q (f ⁻¹ᵁ U) m :=
  EtaleChart.ofCoords q (f ⁻¹ᵁ U) (baseChangeCoords f c)
    (etale_homOfVector_baseChangeCoords hsq c)

section
variable {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (hsq : IsPullback q f (Spec.map φ) p)

theorem EtaleChart.baseChange_map :
    (c.baseChange hsq).map =
      AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c) :=
  EtaleChart.ofCoords_map q (f ⁻¹ᵁ U) (baseChangeCoords f c)
    (etale_homOfVector_baseChangeCoords hsq c)

@[simp] theorem EtaleChart.baseChange_coord (j : Fin m) :
    (c.baseChange hsq).coord j = (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom (c.coord j) := by
  have h1 := AffineSpace.homOfVector_appTop_coord ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c)
    (ULift.up j : ULift.{u} (Fin m))
  rw [EtaleChart.coord_def, EtaleChart.baseChange_map, h1,
    baseChangeCoords_apply f c (ULift.up j : ULift.{u} (Fin m))]
  exact CommRingCat.hom_inv_apply ..


end

private theorem appLE_of_le_eq_appLE_comp_presheaf_map_consolidated183 {Z W : Scheme.{u}} (g : Z ⟶ W) (A : W.Opens)
    (B C : Z.Opens) (e : B ≤ g ⁻¹ᵁ A) (hCB : C ≤ B) (hCA : C ≤ g ⁻¹ᵁ A) :
    g.appLE A C hCA = g.appLE A B e ≫ Z.presheaf.map (homOfLE hCB).op := by
  have hL : g.appLE A C hCA = g.app A ≫ Z.presheaf.map (homOfLE hCA).op := rfl
  have hR : g.appLE A B e = g.app A ≫ Z.presheaf.map (homOfLE e).op := rfl
  have hmap : Z.presheaf.map ((homOfLE e).op ≫ (homOfLE hCB).op)
      = Z.presheaf.map (homOfLE hCA).op :=
    AlgebraicGeometry.Scheme.presheaf_map_eq_of_parallel _ _ _
  rw [hL, hR, Category.assoc, ← Functor.map_comp, hmap]

theorem exists_etaleChart_of_isPullback (hsq : IsPullback q f (Spec.map φ) p)
    {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (y : ↥Y) (hy : f.base y ∈ U) :
    ∃ (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ U) (c' : EtaleChart q V m),
      IsAffineOpen V ∧ y ∈ V ∧
        ∀ j : Fin m, c'.coord j = (f.appLE U V hV).hom (c.coord j) := by
  have hymem : y ∈ (f ⁻¹ᵁ U : Y.Opens) := hy
  obtain ⟨V, hVaff, hyV, hVsub⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hymem
  have hV : V ≤ f ⁻¹ᵁ U := hVsub
  refine ⟨V, hV, (c.baseChange hsq).restrict hV, hVaff, hyV, fun j => ?_⟩
  have happ : f.appLE U V hV
      = f.appLE U (f ⁻¹ᵁ U) le_rfl ≫ Y.presheaf.map (homOfLE hV).op :=
    appLE_of_le_eq_appLE_comp_presheaf_map_consolidated183 f U (f ⁻¹ᵁ U) V le_rfl hV hV
  have h2 : (f.appLE U V hV).hom (c.coord j)
      = (Y.presheaf.map (homOfLE hV).op).hom
          ((f.appLE U (f ⁻¹ᵁ U) le_rfl).hom (c.coord j)) := by
    rw [happ]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [EtaleChart.coord_restrict (c.baseChange hsq) hV j,
    EtaleChart.baseChange_coord c hsq j]
  exact h2.symm

section
variable {Z : Scheme.{u}} {V : Z.Opens} (hV : IsAffineOpen V) (D : Z.IdealSheafData)

private theorem restrictIdeal_eq_top_of_ideal_eq_top_consolidated183 (hD : D.ideal ⟨V, hV⟩ = ⊤) :
    restrictIdeal D V = ⊤ := by
  have : IsAffine V.toScheme := hV
  have e1 : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by
    intro z _
    exact z.2
  apply AlgebraicGeometry.Scheme.IdealSheafData.ext_of_isAffine
  rw [restrictIdeal_eq_comap_ι,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ e1, hD, Ideal.map_top]
  simp

private theorem ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top_consolidated183 (hD : restrictIdeal D V = ⊤) :
    D.ideal ⟨V, hV⟩ = ⊤ := by
  have : IsAffine V.toScheme := hV
  have e1 : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by
    intro z _
    exact z.2
  have hD' : D.comap V.ι = ⊤ := by
    rw [← restrictIdeal_eq_comap_ι]
    exact hD
  have h1 : Ideal.map (V.ι.appLE V ⊤ e1).hom (D.ideal ⟨V, hV⟩) = ⊤ := by
    rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ e1, hD']
    simp
  rw [ι_appLE_eq_topIso_inv_consolidated183] at h1
  have hid : (V.topIso.hom.hom).comp (V.topIso.inv.hom) = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id]
  have h2 : Ideal.map V.topIso.hom.hom (Ideal.map V.topIso.inv.hom (D.ideal ⟨V, hV⟩))
      = D.ideal ⟨V, hV⟩ := by
    rw [Ideal.map_map, hid, Ideal.map_id]
  rw [h1, Ideal.map_top] at h2
  exact h2.symm


end

theorem inStrictNormalCrossingPositionAt_comap_of_isPullback (hsq : IsPullback q f (Spec.map φ) p)
    (E : List X.IdealSheafData) (y : ↥Y) (hy : InStrictNormalCrossingPositionAt p E (f.base y)) :
    InStrictNormalCrossingPositionAt q (E.map fun D => D.comap f) y := by
  obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := hy.exists_etaleChart
  obtain ⟨W, hW, hxW, hWU⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hxU
  obtain ⟨V, hVW, c', hVaff, hyV, hcoord⟩ :=
    exists_etaleChart_of_isPullback hsq (c.restrict hWU) y hxW
  refine inStrictNormalCrossingPositionAt_of_exists_etaleChart ⟨V, hyV, m, c', a, ?_, ?_, ?_⟩
  · intro i hi j hj t h1 h2
    simp only [List.length_map] at hi hj
    exact hinj i hi j hj t h1 h2
  · intro i hi hai
    have hiE : i < E.length := by simpa using hi
    have hgi : (E.map fun D => D.comap f)[i]'hi = (E[i]'hiE).comap f := by simp
    rw [hgi]
    have h1 : restrictIdeal (E[i]'hiE) W = ⊤ :=
      restrictIdeal_eq_top_of_le (E[i]'hiE) hWU (hnone i hiE hai)
    have h2 : (E[i]'hiE).ideal ⟨W, hW⟩ = ⊤ :=
      ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top_consolidated183 hW (E[i]'hiE) h1
    refine restrictIdeal_eq_top_of_ideal_eq_top_consolidated183 hVaff ((E[i]'hiE).comap f) ?_
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE (E[i]'hiE) f
      ⟨W, hW⟩ ⟨V, hVaff⟩ hVW, h2, Ideal.map_top]
  · intro i hi t hai
    have hiE : i < E.length := by simpa using hi
    have hgi : (E.map fun D => D.comap f)[i]'hi = (E[i]'hiE).comap f := by simp
    rw [hgi]
    have h1 : restrictIdeal (E[i]'hiE) W = (c.restrict hWU).coordIdeal {t} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hWU c (E[i]'hiE) {t} (hsome i hiE t hai)
    have h2 : (E[i]'hiE).ideal ⟨W, hW⟩
        = Ideal.span ((c.restrict hWU).coord '' ((({t} : Finset (Fin m))) : Set (Fin m))) :=
      EtaleChart.ideal_eq_span_coord (c.restrict hWU) hW (E[i]'hiE) {t} h1
    refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hVaff c' ((E[i]'hiE).comap f) {t} ?_
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_span_image (E[i]'hiE) f
      ⟨W, hW⟩ ⟨V, hVaff⟩ hVW _ h2]
    congr 1
    rw [Set.image_image]
    exact Set.image_congr fun j _ => (hcoord j).symm

section
variable [Smooth p] (hsq : IsPullback q f (Spec.map φ) p) (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
include hsq hE

theorem isSmoothDivisor_comap_of_isPullback_field (D : X.IdealSheafData) (hD : D ∈ E) :
    IsSmoothDivisor q (D.comap f) := by
  obtain ⟨i, hi, hEi⟩ := List.mem_iff_getElem.1 hD
  refine isSmoothDivisor_of_locally_coordIdeal (D.comap f) ?_
  intro y
  obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ :=
    (((inStrictNormalCrossingPosition_iff p E).1 hE).2 (f.base y)).exists_etaleChart
  obtain ⟨W, hWaff, hxW, hWU⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hxU
  obtain ⟨V, hVW, c', hVaff, hyV, hcoord⟩ :=
    exists_etaleChart_of_isPullback hsq (c.restrict hWU) y hxW
  have hcomap : (D.comap f).ideal ⟨V, hVaff⟩
      = Ideal.map (f.appLE W V hVW).hom (D.ideal ⟨W, hWaff⟩) :=
    AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE D f ⟨W, hWaff⟩
      ⟨V, hVaff⟩ hVW
  refine ⟨V, hyV, m, c', ?_⟩
  cases hai : a i with
  | none =>
      left
      have h1 := hnone i hi hai
      rw [hEi] at h1
      have h2 : restrictIdeal D W = ⊤ := restrictIdeal_eq_top_of_le D hWU h1
      have h3 : D.ideal ⟨W, hWaff⟩ = ⊤ := ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top_consolidated183 hWaff D h2
      rw [h3, Ideal.map_top] at hcomap
      exact restrictIdeal_eq_top_of_ideal_eq_top_consolidated183 hVaff (D.comap f) hcomap
  | some t =>
      right
      refine ⟨t, ?_⟩
      have h1 := hsome i hi t hai
      rw [hEi] at h1
      have h2 : restrictIdeal D W = (c.restrict hWU).coordIdeal {t} :=
        restrictIdeal_eq_restrict_coordIdeal_of_le hWU c D {t} h1
      have h3 : D.ideal ⟨W, hWaff⟩
          = Ideal.span ((c.restrict hWU).coord '' ((({t} : Finset (Fin m)) : Finset (Fin m)) :
              Set (Fin m))) :=
        EtaleChart.ideal_eq_span_coord (c.restrict hWU) hWaff D {t} h2
      refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hVaff c' (D.comap f) {t} ?_
      rw [hcomap, h3, Ideal.map_span, Set.image_image]
      exact congrArg Ideal.span (Set.image_congr fun j _ => (hcoord j).symm)

theorem inStrictNormalCrossingPosition_comap_of_isPullback :
    InStrictNormalCrossingPosition q (E.map fun D => D.comap f) := by
  rw [inStrictNormalCrossingPosition_iff]
  refine ⟨?_, ?_⟩
  · intro D hD
    rw [List.mem_map] at hD
    obtain ⟨D₀, hD₀, rfl⟩ := hD
    exact isSmoothDivisor_comap_of_isPullback_field hsq E hE D₀ hD₀
  · intro y
    exact inStrictNormalCrossingPositionAt_comap_of_isPullback hsq E y
      (((inStrictNormalCrossingPosition_iff p E).1 hE).2 (f.base y))


end

end

section

section
variable {k K : Type u} [Field k] [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))

theorem isPullback_pullback_specMap (φ : CommRingCat.of k ⟶ CommRingCat.of K) :
    IsPullback (pullback.snd p (Spec.map φ)) (pullback.fst p (Spec.map φ)) (Spec.map φ) p :=
  (IsPullback.of_hasPullback p (Spec.map φ)).flip

theorem smooth_pullbackSnd_specMap [Smooth p]
    (φ : CommRingCat.of k ⟶ CommRingCat.of K) :
    Smooth (pullback.snd p (Spec.map φ)) :=
  smooth_of_isPullback_field (isPullback_pullback_specMap p φ)

theorem exists_etaleChart_pullback_specMap (φ : CommRingCat.of k ⟶ CommRingCat.of K)
    {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (y : ↥(pullback p (Spec.map φ)))
    (hy : (pullback.fst p (Spec.map φ)).base y ∈ U) :
    ∃ (V : (pullback p (Spec.map φ)).Opens) (hV : V ≤ pullback.fst p (Spec.map φ) ⁻¹ᵁ U)
      (c' : EtaleChart (pullback.snd p (Spec.map φ)) V m),
      IsAffineOpen V ∧ y ∈ V ∧
        ∀ j : Fin m,
          c'.coord j = ((pullback.fst p (Spec.map φ)).appLE U V hV).hom (c.coord j) :=
  exists_etaleChart_of_isPullback (isPullback_pullback_specMap p φ) c y hy

theorem inStrictNormalCrossingPosition_comap_pullback_specMap [Smooth p]
    (φ : CommRingCat.of k ⟶ CommRingCat.of K)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) :
    InStrictNormalCrossingPosition (pullback.snd p (Spec.map φ))
      (E.map fun D => D.comap (pullback.fst p (Spec.map φ))) :=
  inStrictNormalCrossingPosition_comap_of_isPullback (isPullback_pullback_specMap p φ) E hE


end

end

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsChartNormalization
section

open Opposite TopologicalSpace

section

section
variable {n : ℕ} (P : Fin n → Prop) [DecidablePred P] {o : Option (Fin n)} {j : Fin n}

private theorem eq_some_and_not_of_bind_ite_eq_some_consolidated179 (h : o.bind (fun j0 => if P j0 then none else some j0) = some j) : o = some j ∧ ¬ P j := by
  cases o with
  | none => simp at h
  | some j0 =>
    by_cases hb : P j0
    · simp [hb] at h
    · simp [hb] at h
      subst h
      exact ⟨rfl, hb⟩

private theorem of_bind_ite_eq_none_consolidated179 (hg : o = some j)
    (h : o.bind (fun j0 => if P j0 then none else some j0) = none) : P j := by
  subst hg
  by_contra hb
  simp [hb] at h


end

section
variable {X : Scheme.{u}}

private theorem eq_top_of_forall_ideal_eq_top_consolidated179 (I : X.IdealSheafData)
    (h : ∀ W : X.affineOpens, I.ideal W = ⊤) : I = ⊤ := by
  have hfun : I.ideal = (⊤ : X.IdealSheafData).ideal := by
    funext W
    have htop : (⊤ : X.IdealSheafData).ideal W = ⊤ := rfl
    rw [h W, htop]
  exact Scheme.IdealSheafData.ext hfun

private theorem mem_support_iff_forall_notMem_basicOpen_consolidated179 (I : X.IdealSheafData)
    {x : ↥X} {U : X.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) :
    x ∈ I.support ↔ ∀ f ∈ I.ideal ⟨U, hU⟩, x ∉ X.basicOpen f := by
  have h0 : x ∈ I.support ↔
      x ∈ X.zeroLocus (↑(I.ideal ⟨U, hU⟩) : Set Γ(X, U)) :=
    Scheme.IdealSheafData.mem_support_iff_of_mem hx
  rw [h0, Scheme.mem_zeroLocus_iff]
  exact Iff.rfl

private theorem mem_basicOpen_iff_notMem_primeIdealOf_consolidated179 {U : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) (x : ↥U) :
    (x : ↥X) ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf x).asIdeal := by
  have h2 : (AlgebraicGeometry.IsAffineOpen.fromSpec hU).base
      (AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x) = (x : ↥X) :=
    AlgebraicGeometry.IsAffineOpen.fromSpec_primeIdealOf hU x
  have h1 : AlgebraicGeometry.IsAffineOpen.fromSpec hU ⁻¹ᵁ X.basicOpen f
      = PrimeSpectrum.basicOpen f :=
    AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_basicOpen hU f
  constructor
  · intro hx
    have hmem : AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x
        ∈ AlgebraicGeometry.IsAffineOpen.fromSpec hU ⁻¹ᵁ X.basicOpen f := by
      show (AlgebraicGeometry.IsAffineOpen.fromSpec hU).base
        (AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x) ∈ X.basicOpen f
      rw [h2]
      exact hx
    rw [h1] at hmem
    exact (PrimeSpectrum.mem_basicOpen f _).mp hmem
  · intro hx
    have hmem : AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x ∈ PrimeSpectrum.basicOpen f :=
      (PrimeSpectrum.mem_basicOpen f _).mpr hx
    rw [← h1] at hmem
    have h3 : (AlgebraicGeometry.IsAffineOpen.fromSpec hU).base
        (AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x) ∈ X.basicOpen f := hmem
    rw [h2] at h3
    exact h3


end

section
variable {X : Scheme.{u}} (I : X.IdealSheafData) {x : ↥X} {U : X.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) (g : Γ(X, U)) (hI : I.ideal ⟨U, hU⟩ = Ideal.span {g})
include hx hI

private theorem mem_support_of_ideal_eq_span_singleton_consolidated179 (hg : x ∉ X.basicOpen g) : x ∈ I.support := by
  rw [mem_support_iff_forall_notMem_basicOpen_consolidated179 I hU hx]
  intro f hf
  rw [hI, Ideal.mem_span_singleton] at hf
  obtain ⟨a, rfl⟩ := hf
  have hle : X.basicOpen (g * a) ≤ X.basicOpen g := by
    rw [Scheme.basicOpen_mul]
    exact inf_le_left
  exact fun hc => hg (hle hc)

private theorem mem_primeIdealOf_of_mem_support_of_ideal_eq_span_singleton_consolidated179 (hs : x ∈ I.support) :
    g ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h := (mem_support_iff_forall_notMem_basicOpen_consolidated179 I hU hx).mp hs g
    (by rw [hI]; exact Ideal.mem_span_singleton_self g)
  by_contra hc
  exact h ((mem_basicOpen_iff_notMem_primeIdealOf_consolidated179 hU g ⟨x, hx⟩).mpr hc)


end

private theorem subschemeι_base_mem_support_of_subscheme_consolidated179 {W : Scheme.{u}} (Z : W.IdealSheafData)
    (z : ↥Z.subscheme) : Z.subschemeι.base z ∈ Z.support := by
  have h : Z.subschemeι.base z ∈ Set.range Z.subschemeι.base := ⟨z, rfl⟩
  rwa [Scheme.IdealSheafData.range_subschemeι] at h

private theorem restrictIdeal_eq_top_of_le_basicOpen_consolidated179 {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (I : X.IdealSheafData) (f : Γ(X, U))
    (hI : I.ideal ⟨U, hU⟩ = Ideal.span {f}) {V : X.Opens} (hVb : V ≤ X.basicOpen f) :
    restrictIdeal I V = ⊤ := by
  have hbU : X.basicOpen f ≤ U := X.basicOpen_le f
  have hVU : V ≤ U := hVb.trans hbU
  rw [restrictIdeal_eq_comap_ι]
  refine eq_top_of_forall_ideal_eq_top_consolidated179 _ ?_
  intro Wa
  have e : (Wa : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ U := fun x _ => hVU x.2
  have e' : (Wa : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ X.basicOpen f := fun x _ => hVb x.2
  rw [Scheme.IdealSheafData.comap_ideal_eq_span_image I V.ι ⟨U, hU⟩ Wa e {f} hI,
    Set.image_singleton, Ideal.span_singleton_eq_top]
  have hfac : V.ι.appLE U (Wa : (V.toScheme).Opens) e
      = X.presheaf.map (homOfLE hbU).op ≫
        V.ι.appLE (X.basicOpen f) (Wa : (V.toScheme).Opens) e' := by
    rw [Scheme.Hom.map_appLE]
  have hcp : ((X.presheaf.map (homOfLE hbU).op ≫
        V.ι.appLE (X.basicOpen f) (Wa : (V.toScheme).Opens) e').hom) f
      = (V.ι.appLE (X.basicOpen f) (Wa : (V.toScheme).Opens) e').hom
          ((X.presheaf.map (homOfLE hbU).op).hom f) := rfl
  rw [hfac, hcp]
  exact IsUnit.map _ (X.toRingedSpace.isUnit_res_basicOpen f)

private def complOrderEmbInv_consolidated179 (m : ℕ) (S : Finset (Fin m)) (t : Fin m) : Option (Fin (m - S.card)) :=
  if h : t ∈ S then none else some (Classical.choose (exists_complOrderEmb_eq m S h))

section
variable (m : ℕ) (S : Finset (Fin m))

private theorem complInv_def_consolidated179 (t : Fin m) :
    complOrderEmbInv_consolidated179 m S t =
      if h : t ∈ S then none else some (Classical.choose (exists_complOrderEmb_eq m S h)) :=
  rfl

private theorem complInv_eq_some_iff_consolidated179 {t : Fin m}
    {j : Fin (m - S.card)} : complOrderEmbInv_consolidated179 m S t = some j ↔ complOrderEmb m S j = t := by
  constructor
  · intro h
    by_cases ht : t ∈ S
    · rw [complInv_def_consolidated179, dif_pos ht] at h
      simp at h
    · rw [complInv_def_consolidated179, dif_neg ht] at h
      have hj : Classical.choose (exists_complOrderEmb_eq m S ht) = j := Option.some.inj h
      have hspec := Classical.choose_spec (exists_complOrderEmb_eq m S ht)
      rw [hj] at hspec
      exact hspec
  · intro h
    have ht : t ∉ S := by
      rw [← h]
      exact complOrderEmb_notMem m S j
    rw [complInv_def_consolidated179, dif_neg ht]
    have hspec := Classical.choose_spec (exists_complOrderEmb_eq m S ht)
    have heq : Classical.choose (exists_complOrderEmb_eq m S ht) = j :=
      (complOrderEmb m S).injective (by rw [hspec, h])
    rw [heq]

private theorem eq_some_complOrderEmb_of_bind_complInv_eq_some_consolidated179 (o : Option (Fin m))
    (j : Fin (m - S.card)) (h : o.bind (complOrderEmbInv_consolidated179 m S) = some j) :
    o = some (complOrderEmb m S j) := by
  cases o with
  | none => simp at h
  | some t =>
    have h' : complOrderEmbInv_consolidated179 m S t = some j := h
    rw [(complInv_eq_some_iff_consolidated179 m S).mp h']

private theorem eq_none_of_bind_complInv_eq_none_consolidated179 (o : Option (Fin m))
    (hnot : ∀ t, o = some t → t ∉ S) (h : o.bind (complOrderEmbInv_consolidated179 m S) = none) : o = none := by
  cases o with
  | none => rfl
  | some t =>
    exfalso
    have h' : complOrderEmbInv_consolidated179 m S t = none := h
    rw [complInv_def_consolidated179, dif_neg (hnot t rfl)] at h'
    simp at h'


end

section

variable {Y Y' : Scheme.{u}} {k : Type u} [Field k] {p : Y ⟶ Spec (CommRingCat.of k)}
  {V : Y.Opens} {n : ℕ}

section
variable (c : EtaleChart p V n) (f : Y' ⟶ Y) [IsOpenImmersion f]

theorem morphismRestrict_comp_map_comp_affineSpaceFinToSpec :
    (morphismRestrict f V ≫ c.map) ≫ affineSpaceFinToSpec k n = (f ⁻¹ᵁ V).ι ≫ (f ≫ p) := by
  rw [Category.assoc, c.comp_struct, ← Category.assoc, morphismRestrict_ι, Category.assoc]

theorem etale_morphismRestrict_comp_map :
    Etale (morphismRestrict f V ≫ c.map) := by
  have h0 : IsOpenImmersion (morphismRestrict f V ≫ V.ι) := by
    rw [morphismRestrict_ι]
    infer_instance
  have h1 : IsOpenImmersion (morphismRestrict f V) :=
    IsOpenImmersion.of_comp (morphismRestrict f V) V.ι
  have h2 : Etale c.map := c.isEtale
  have h3 : Etale (morphismRestrict f V) := inferInstance
  infer_instance


end

def EtaleChart.pullbackOpenImmersion (c : EtaleChart p V n) (f : Y' ⟶ Y) [IsOpenImmersion f] :
    EtaleChart (f ≫ p) (f ⁻¹ᵁ V) n :=
  ⟨morphismRestrict f V ≫ c.map, morphismRestrict_comp_map_comp_affineSpaceFinToSpec c f,
    etale_morphismRestrict_comp_map c f⟩

section
variable (c : EtaleChart p V n) (f : Y' ⟶ Y) [IsOpenImmersion f]

theorem EtaleChart.pullbackOpenImmersion_map :
    (c.pullbackOpenImmersion f).map = morphismRestrict f V ≫ c.map :=
  rfl

private theorem restrictIdeal_comap_eq_coordIdeal_pullbackOpenImmersion_consolidated179 (D : Y.IdealSheafData) (S : Finset (Fin n))
    (h : restrictIdeal D V = c.coordIdeal S) :
    restrictIdeal (D.comap f) (f ⁻¹ᵁ V) = (c.pullbackOpenImmersion f).coordIdeal S := by
  have h1 : (c.pullbackOpenImmersion f).coordIdeal S
      = (c.coordIdeal S).comap (morphismRestrict f V) := by
    rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal,
      EtaleChart.pullbackOpenImmersion_map, Scheme.IdealSheafData.comap_comp]
  rw [h1, ← h, restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
    ← morphismRestrict_ι, Scheme.IdealSheafData.comap_comp]


end

end

theorem restrictIdeal_comap_preimage_eq_top {Y Y' : Scheme.{u}} (f : Y' ⟶ Y) (V : Y.Opens)
    (D : Y.IdealSheafData) (h : restrictIdeal D V = ⊤) :
    restrictIdeal (D.comap f) (f ⁻¹ᵁ V) = ⊤ := by
  have h1 : restrictIdeal (D.comap f) (f ⁻¹ᵁ V)
      = (restrictIdeal D V).comap (morphismRestrict f V) := by
    rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
      ← morphismRestrict_ι, Scheme.IdealSheafData.comap_comp]
  rw [h1, h, Scheme.IdealSheafData.comap_top]

theorem image_subset_of_image_inter_subset {α : Type*} {β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {A O : Set α} {g : α → β} {C : Set β} (hA : IsIrreducible A)
    (hO : IsOpen O) (hAO : (A ∩ O).Nonempty) (hg : Continuous g) (hC : IsClosed C)
    (h : g '' (A ∩ O) ⊆ C) : g '' A ⊆ C := by
  have hsub : A ⊆ closure (A ∩ O) := by
    intro x hx
    rw [mem_closure_iff]
    intro u hu hxu
    obtain ⟨z, hz⟩ := hA.2 u O hu hO ⟨x, hx, hxu⟩ hAO
    exact ⟨z, hz.2.1, hz.1, hz.2.2⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 : g x ∈ g '' closure (A ∩ O) := ⟨x, hsub hx, rfl⟩
  exact closure_minimal h hC (image_closure_subset_closure_image hg h1)

section

variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}

theorem exists_etaleChart_coord_mem_primeIdealOf (F : List X.IdealSheafData) (y : ↥X) (U : X.Opens)
    (hU : IsAffineOpen U) (hyU : y ∈ U) {n : ℕ} (c : EtaleChart p U n) (γ : ℕ → Option (Fin n))
    (hdesc : ∀ i, ∀ hi : i < F.length,
      (γ i = none → restrictIdeal (F[i]'hi) U = ⊤) ∧
        ∀ j, γ i = some j → restrictIdeal (F[i]'hi) U = c.coordIdeal {j})
    (hinj : ∀ i i', i < F.length → i' < F.length → ∀ j, γ i = some j → γ i' = some j → i = i') :
    ∃ (U' : X.Opens) (hU' : IsAffineOpen U') (hy' : y ∈ U') (n' : ℕ)
      (c' : EtaleChart p U' n') (γ' : ℕ → Option (Fin n')),
      (∀ i, ∀ hi : i < F.length,
        (γ' i = none → restrictIdeal (F[i]'hi) U' = ⊤) ∧
          ∀ j, γ' i = some j → restrictIdeal (F[i]'hi) U' = c'.coordIdeal {j}) ∧
      (∀ i i', i < F.length → i' < F.length → ∀ j, γ' i = some j → γ' i' = some j → i = i') ∧
      (∀ i, i < F.length → ∀ j, γ' i = some j →
        c'.coord j ∈ (hU'.primeIdealOf ⟨y, hy'⟩).asIdeal) := by
  classical
  set notInPrime : Finset (Fin n) :=
    Finset.univ.filter (fun j => c.coord j ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal) with hBadDef
  have hBad : ∀ j : Fin n, j ∈ notInPrime ↔ c.coord j ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
    intro j
    rw [hBadDef]
    simp
  set t : Γ(X, U) := ∏ j ∈ notInPrime, c.coord j with htdef
  have ht : t ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
    have hmem : ∀ j ∈ notInPrime, c.coord j ∈ Ideal.primeCompl (hU.primeIdealOf ⟨y, hyU⟩).asIdeal :=
      fun j hj => (hBad j).mp hj
    have hprod := Submonoid.prod_mem (Ideal.primeCompl (hU.primeIdealOf ⟨y, hyU⟩).asIdeal) hmem
    rw [← htdef] at hprod
    exact hprod
  have hUt : IsAffineOpen (X.basicOpen t) := hU.basicOpen t
  have hle : X.basicOpen t ≤ U := X.basicOpen_le t
  have hy' : y ∈ X.basicOpen t := (mem_basicOpen_iff_notMem_primeIdealOf_consolidated179 hU t ⟨y, hyU⟩).mpr ht
  have hbasic_le : ∀ j ∈ notInPrime, X.basicOpen t ≤ X.basicOpen (c.coord j) := by
    intro j hj
    have hsplit : t = c.coord j * ∏ i ∈ notInPrime.erase j, c.coord i := by
      rw [htdef]
      exact (Finset.mul_prod_erase notInPrime (fun i => c.coord i) hj).symm
    rw [hsplit, Scheme.basicOpen_mul]
    exact inf_le_left
  refine ⟨X.basicOpen t, hUt, hy', n, c.restrict hle,
    fun i => (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0), ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hA, hB⟩ := hdesc i hi
    constructor
    · intro hnone
      have hnone' : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = none := hnone
      by_cases hg : γ i = none
      · exact restrictIdeal_eq_top_of_le _ hle (hA hg)
      · obtain ⟨j0, hj0⟩ := Option.ne_none_iff_exists'.mp hg
        have hb : j0 ∈ notInPrime := of_bind_ite_eq_none_consolidated179 (fun j1 => j1 ∈ notInPrime) hj0 hnone'
        have hideal : (F[i]'hi).ideal ⟨U, hU⟩ = Ideal.span {c.coord j0} := by
          rw [c.ideal_eq_span_coord hU _ _ (hB j0 hj0), Finset.coe_singleton,
            Set.image_singleton]
        exact restrictIdeal_eq_top_of_le_basicOpen_consolidated179 hU _ (c.coord j0) hideal (hbasic_le j0 hb)
    · intro j hj
      have hj' : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j := hj
      obtain ⟨hg, hb⟩ := eq_some_and_not_of_bind_ite_eq_some_consolidated179 (fun j1 => j1 ∈ notInPrime) hj'
      exact restrictIdeal_eq_restrict_coordIdeal_of_le hle c _ _ (hB j hg)
  · intro i i' hi hi' j hj hj'
    have hja : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j := hj
    have hjb : (γ i').bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j := hj'
    exact hinj i i' hi hi' j (eq_some_and_not_of_bind_ite_eq_some_consolidated179 (fun j1 => j1 ∈ notInPrime) hja).1
      (eq_some_and_not_of_bind_ite_eq_some_consolidated179 (fun j1 => j1 ∈ notInPrime) hjb).1
  · intro i hi j hj
    obtain ⟨_, hB⟩ := hdesc i hi
    have hj' : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j := hj
    obtain ⟨hg, hb⟩ := eq_some_and_not_of_bind_ite_eq_some_consolidated179 (fun j1 => j1 ∈ notInPrime) hj'
    have hmemP : c.coord j ∈ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
      by_contra hcon
      exact hb ((hBad j).mpr hcon)
    have hidU : (F[i]'hi).ideal ⟨U, hU⟩ = Ideal.span {c.coord j} := by
      rw [c.ideal_eq_span_coord hU _ _ (hB j hg), Finset.coe_singleton, Set.image_singleton]
    have hynb : y ∉ X.basicOpen (c.coord j) := fun hc =>
      (mem_basicOpen_iff_notMem_primeIdealOf_consolidated179 hU (c.coord j) ⟨y, hyU⟩).mp hc hmemP
    have hysup : y ∈ (F[i]'hi).support :=
      mem_support_of_ideal_eq_span_singleton_consolidated179 _ hU hyU (c.coord j) hidU hynb
    have hidU' : (F[i]'hi).ideal ⟨X.basicOpen t, hUt⟩
        = Ideal.span {(c.restrict hle).coord j} := by
      rw [(c.restrict hle).ideal_eq_span_coord hUt _ _
        (restrictIdeal_eq_restrict_coordIdeal_of_le hle c _ _ (hB j hg)), Finset.coe_singleton,
        Set.image_singleton]
    exact mem_primeIdealOf_of_mem_support_of_ideal_eq_span_singleton_consolidated179 _ hUt hy' _ hidU' hysup

end

section

variable {W : Scheme.{u}} {k : Type u} [Field k]

section
variable (q : W ⟶ Spec (CommRingCat.of k))

theorem exists_etaleChart_on_open_of_hasStrictNormalCrossingsWith (E : List W.IdealSheafData) (Z : W.IdealSheafData) (hZ : HasStrictNormalCrossingsWith q Z E)
    (T : Z.subscheme.Opens)
    (hcomp : ∀ D ∈ E, ∀ C ∈ irreducibleComponents ↥T.toScheme,
      ¬ ((T.ι ≫ Z.subschemeι).base '' C ⊆ (D.support : Set ↥W)))
    (y : ↥T.toScheme) :
    ∃ (U : T.toScheme.Opens) (_ : IsAffineOpen U) (_ : y ∈ U) (n : ℕ)
      (c : EtaleChart (T.ι ≫ (Z.subschemeι ≫ q)) U n) (γ : ℕ → Option (Fin n)),
      (∀ i, ∀ hi : i < E.length,
        (γ i = none → restrictIdeal ((E[i]'hi).comap (T.ι ≫ Z.subschemeι)) U = ⊤) ∧
          ∀ j, γ i = some j →
            restrictIdeal ((E[i]'hi).comap (T.ι ≫ Z.subschemeι)) U = c.coordIdeal {j}) ∧
      (∀ i i', i < E.length → i' < E.length → ∀ j, γ i = some j → γ i' = some j → i = i') := by
  classical
  have hbase : ∀ z : ↥T.toScheme,
      (T.ι ≫ Z.subschemeι).base z = Z.subschemeι.base (T.ι.base z) := fun _ => rfl
  have hcont : Continuous fun z : ↥T.toScheme => (T.ι ≫ Z.subschemeι).base z :=
    (T.ι ≫ Z.subschemeι).base.hom.continuous
  have hw : Z.subschemeι.base (T.ι.base y) ∈ Z.support := subschemeι_base_mem_support_of_subscheme_consolidated179 Z _
  obtain ⟨U, hwU, m, c, a, S, hainj, hanone, hasome, hZU⟩ := hZ.exists_etaleChart hw
  obtain ⟨U₀, hU₀aff, hwU₀, hU₀le⟩ := exists_isAffineOpen_mem_and_subset hwU
  have hZU₀ : restrictIdeal Z U₀ = (c.restrict hU₀le).coordIdeal S :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hU₀le c Z S hZU
  have hE₀none : ∀ (i : ℕ) (hi : i < E.length), a i = none →
      restrictIdeal (E[i]'hi) U₀ = ⊤ := fun i hi h =>
    restrictIdeal_eq_top_of_le _ hU₀le (hanone i hi h)
  have hE₀some : ∀ (i : ℕ) (hi : i < E.length) (t : Fin m), a i = some t →
      restrictIdeal (E[i]'hi) U₀ = (c.restrict hU₀le).coordIdeal {t} := fun i hi t h =>
    restrictIdeal_eq_restrict_coordIdeal_of_le hU₀le c _ _ (hasome i hi t h)
  have hnotS : ∀ (i : ℕ) (hi : i < E.length) (t : Fin m), a i = some t → t ∉ S := by
    intro i hi t hat htS
    have hEle : (E[i]'hi).ideal ⟨U₀, hU₀aff⟩ ≤ Z.ideal ⟨U₀, hU₀aff⟩ := by
      rw [(c.restrict hU₀le).ideal_eq_span_coord hU₀aff _ _ (hE₀some i hi t hat),
        (c.restrict hU₀le).ideal_eq_span_coord hU₀aff _ _ hZU₀,
        Finset.coe_singleton, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
      exact Ideal.subset_span ⟨t, Finset.mem_coe.mpr htS, rfl⟩
    refine hcomp (E[i]'hi) (List.getElem_mem hi) (irreducibleComponent y)
      (irreducibleComponent_mem_irreducibleComponents y) ?_
    refine image_subset_of_image_inter_subset isIrreducible_irreducibleComponent
      (U₀.2.preimage hcont) ⟨y, mem_irreducibleComponent, ?_⟩ hcont
      (E[i]'hi).support.2 ?_
    · show (T.ι ≫ Z.subschemeι).base y ∈ (U₀ : Set ↥W)
      rw [hbase y]
      exact hwU₀
    · rintro _ ⟨z, ⟨-, hz⟩, rfl⟩
      have hzU₀ : (T.ι ≫ Z.subschemeι).base z ∈ U₀ := hz
      have hzZ : (T.ι ≫ Z.subschemeι).base z ∈ Z.support := by
        rw [hbase z]
        exact subschemeι_base_mem_support_of_subscheme_consolidated179 Z _
      exact (mem_support_iff_forall_notMem_basicOpen_consolidated179 _ hU₀aff hzU₀).mpr
        (fun f hf => (mem_support_iff_forall_notMem_basicOpen_consolidated179 Z hU₀aff hzU₀).mp hzZ f (hEle hf))
  have hyV : y ∈ T.ι ⁻¹ᵁ (Z.subschemeι ⁻¹ᵁ U₀) := hwU₀
  obtain ⟨U₁, hU₁aff, hyU₁, hU₁le⟩ := exists_isAffineOpen_mem_and_subset hyV
  set d := (c.restrict hU₀le).restrictToSubscheme hU₀aff Z S hZU₀ with hd
  set d' := d.pullbackOpenImmersion T.ι with hd'
  refine ⟨U₁, hU₁aff, hyU₁, m - S.card, d'.restrict hU₁le,
    fun i => (a i).bind (complOrderEmbInv_consolidated179 m S), ?_, ?_⟩
  · intro i hi
    constructor
    · intro hnone
      have hnone' : (a i).bind (complOrderEmbInv_consolidated179 m S) = none := hnone
      have ha : a i = none :=
        eq_none_of_bind_complInv_eq_none_consolidated179 m S (a i) (fun t ht => hnotS i hi t ht) hnone'
      have h1 := hE₀none i hi ha
      have h2 : restrictIdeal ((E[i]'hi).comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U₀) = ⊤ :=
        restrictIdeal_comap_subschemeι_eq_top Z U₀ _ h1
      have h3 : restrictIdeal (((E[i]'hi).comap Z.subschemeι).comap T.ι)
          (T.ι ⁻¹ᵁ (Z.subschemeι ⁻¹ᵁ U₀)) = ⊤ :=
        restrictIdeal_comap_preimage_eq_top T.ι _ _ h2
      have h4 := restrictIdeal_eq_top_of_le _ hU₁le h3
      rw [Scheme.IdealSheafData.comap_comp]
      exact h4
    · intro j hj
      have hj' : (a i).bind (complOrderEmbInv_consolidated179 m S) = some j := hj
      have ha : a i = some (complOrderEmb m S j) := eq_some_complOrderEmb_of_bind_complInv_eq_some_consolidated179 m S (a i) j hj'
      have h1 := hE₀some i hi _ ha
      have h2 : restrictIdeal ((E[i]'hi).comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U₀)
          = d.coordIdeal {j} :=
        (c.restrict hU₀le).restrictToSubscheme_coordIdeal_singleton hU₀aff Z S hZU₀ j _ h1
      have h3 : restrictIdeal (((E[i]'hi).comap Z.subschemeι).comap T.ι)
          (T.ι ⁻¹ᵁ (Z.subschemeι ⁻¹ᵁ U₀)) = d'.coordIdeal {j} :=
        restrictIdeal_comap_eq_coordIdeal_pullbackOpenImmersion_consolidated179 d T.ι _ _ h2
      have h4 := restrictIdeal_eq_restrict_coordIdeal_of_le hU₁le d' _ _ h3
      rw [Scheme.IdealSheafData.comap_comp]
      exact h4
  · intro i i' hi hi' j hj hj'
    have hja : (a i).bind (complOrderEmbInv_consolidated179 m S) = some j := hj
    have hjb : (a i').bind (complOrderEmbInv_consolidated179 m S) = some j := hj'
    exact hainj i hi i' hi' (complOrderEmb m S j) (eq_some_complOrderEmb_of_bind_complInv_eq_some_consolidated179 m S (a i) j hja)
      (eq_some_complOrderEmb_of_bind_complInv_eq_some_consolidated179 m S (a i') j hjb)

theorem exists_etaleChart_coord_mem_primeIdealOf_on_clopen [Smooth q]
    (E : List W.IdealSheafData) (_hE : InStrictNormalCrossingPosition q E) (Z : W.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith q Z E) (T : Z.subscheme.Opens)
    (_hTclosed : IsClosed (T : Set ↥Z.subscheme))
    (hcomp : ∀ D ∈ E, ∀ C ∈ irreducibleComponents ↥T.toScheme,
      ¬ ((T.ι ≫ Z.subschemeι).base '' C ⊆ (D.support : Set ↥W)))
    (y : ↥T.toScheme) :
    ∃ (U : T.toScheme.Opens) (hU : IsAffineOpen U) (hy : y ∈ U) (n : ℕ)
      (c : EtaleChart (T.ι ≫ (Z.subschemeι ≫ q)) U n) (γ : ℕ → Option (Fin n)),
      (∀ i, ∀ hi : i < E.length,
        (γ i = none → restrictIdeal ((E[i]'hi).comap (T.ι ≫ Z.subschemeι)) U = ⊤) ∧
          ∀ j, γ i = some j →
            restrictIdeal ((E[i]'hi).comap (T.ι ≫ Z.subschemeι)) U = c.coordIdeal {j}) ∧
      (∀ i i', i < E.length → i' < E.length → ∀ j, γ i = some j → γ i' = some j → i = i') ∧
      (∀ i, i < E.length → ∀ j, γ i = some j → c.coord j ∈ (hU.primeIdealOf ⟨y, hy⟩).asIdeal) := by
  classical
  obtain ⟨U, hU, hy, n, c, γ, hdesc, hinj⟩ :=
    exists_etaleChart_on_open_of_hasStrictNormalCrossingsWith q E Z hZ T hcomp y
  have hlen : (E.map fun D : W.IdealSheafData => D.comap (T.ι ≫ Z.subschemeι)).length
      = E.length := by
    simp
  have hdesc' : ∀ i, ∀ hi : i < (E.map fun D : W.IdealSheafData =>
        D.comap (T.ι ≫ Z.subschemeι)).length,
      (γ i = none → restrictIdeal ((E.map fun D : W.IdealSheafData =>
          D.comap (T.ι ≫ Z.subschemeι))[i]'hi) U = ⊤) ∧
        ∀ j, γ i = some j → restrictIdeal ((E.map fun D : W.IdealSheafData =>
          D.comap (T.ι ≫ Z.subschemeι))[i]'hi) U = c.coordIdeal {j} := by
    intro i hi
    have hi' : i < E.length := by rwa [hlen] at hi
    obtain ⟨hA, hB⟩ := hdesc i hi'
    simp only [List.getElem_map]
    exact ⟨hA, hB⟩
  have hinj' : ∀ i i', i < (E.map fun D : W.IdealSheafData =>
      D.comap (T.ι ≫ Z.subschemeι)).length →
      i' < (E.map fun D : W.IdealSheafData => D.comap (T.ι ≫ Z.subschemeι)).length →
      ∀ j, γ i = some j → γ i' = some j → i = i' := by
    intro i i' hi hi' j h1 h2
    rw [hlen] at hi hi'
    exact hinj i i' hi hi' j h1 h2
  obtain ⟨U', hU', hy', n', c', γ', h1, h2, h3⟩ :=
    exists_etaleChart_coord_mem_primeIdealOf
      (E.map fun D : W.IdealSheafData => D.comap (T.ι ≫ Z.subschemeι)) y U hU hy c γ
      hdesc' hinj'
  refine ⟨U', hU', hy', n', c', γ', ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i < (E.map fun D : W.IdealSheafData =>
        D.comap (T.ι ≫ Z.subschemeι)).length := by
      rw [hlen]; exact hi
    obtain ⟨hA, hB⟩ := h1 i hi'
    simp only [List.getElem_map] at hA hB
    exact ⟨hA, hB⟩
  · intro i i' hi hi' j hj hj'
    exact h2 i i' (by rw [hlen]; exact hi) (by rw [hlen]; exact hi') j hj hj'
  · intro i hi j hj
    exact h3 i (by rw [hlen]; exact hi) j hj


end

end

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsSmoothBaseChange
section

open TopologicalSpace Opposite


variable {k : Type u} [Field k] {X Y : Scheme.{u}}

section
variable {Z : Scheme.{u}} (V : Z.Opens)

private theorem topIso_hom_inv_apply_consolidated185 (x : Γ(Z, V)) :
    V.topIso.hom.hom (V.topIso.inv.hom x) = x :=
  V.topIso.commRingCatIsoToRingEquiv.right_inv x

private theorem ι_appLE_self_top_eq_topIso_inv_consolidated185 :
    V.ι.appLE V ⊤ (by simp) = V.topIso.inv := by
  simp
  apply Scheme.presheaf_map_eq_of_parallel


end

private theorem appLE_eq_map_comp_appLE_consolidated185 (f : Y ⟶ X) {U W : X.Opens} {V : Y.Opens} (hWU : W ≤ U)
    (e : V ≤ f ⁻¹ᵁ W) (hVU : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V hVU = X.presheaf.map (homOfLE hWU).op ≫ f.appLE W V e := by
  rw [Scheme.Hom.map_appLE]

private theorem etale_comp_ringEquiv_consolidated185 {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : B →+* C) (e : A ≃+* B) (hf : f.Etale) : (f.comp e.toRingHom).Etale :=
  RingHom.Etale.respectsIso.2 f e hf

private def uliftFinAddEquivSum_consolidated185 (m d : ℕ) :
    ULift.{u} (Fin (m + d)) ≃ ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d) :=
  Equiv.ulift.trans (finSumFinEquiv.symm.trans (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm))

private theorem sumEquiv_castAdd_eq_inl_consolidated185 (m d : ℕ) (j : Fin m) :
    uliftFinAddEquivSum_consolidated185 m d (ULift.up (Fin.castAdd d j)) = Sum.inl (ULift.up j) := by
  simp [uliftFinAddEquivSum_consolidated185]

section
variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

private theorem etale_of_formallyEtale_of_finitePresentation_consolidated185 (h1 : @Algebra.FormallyEtale A B _ _ f.toAlgebra)
    (h2 : @Algebra.FinitePresentation A B _ _ f.toAlgebra) : f.Etale :=
  @Algebra.Etale.mk A B _ _ f.toAlgebra h1 h2

private theorem ideal_eq_top_of_map_eq_top_of_leftInverse_consolidated185 (g : B →+* A) (hgf : ∀ x, g (f x) = x) (I : Ideal A) (hI : Ideal.map f I = ⊤) : I = ⊤ := by
  have h2 : Ideal.map g (Ideal.map f I) = I := by
    rw [Ideal.map_map]
    have hc : g.comp f = RingHom.id A := RingHom.ext hgf
    rw [hc, Ideal.map_id]
  rw [hI, Ideal.map_top] at h2
  exact h2.symm


end

section
variable {Z : Scheme.{u}} {V : Z.Opens} (hV : IsAffineOpen V) (D : Z.IdealSheafData)

private theorem restrictIdeal_eq_top_of_ideal_eq_top_consolidated185 (hD : D.ideal ⟨V, hV⟩ = ⊤) :
    restrictIdeal D V = ⊤ := by
  have : IsAffine V.toScheme := hV
  have e1 : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by simp
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [restrictIdeal_eq_comap_ι,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ e1,
    hD, Ideal.map_top]
  simp

private theorem ideal_affineOpen_eq_top_of_restrictIdeal_eq_top_consolidated185 (hD : restrictIdeal D V = ⊤) :
    D.ideal ⟨V, hV⟩ = ⊤ := by
  have : IsAffine V.toScheme := hV
  have e1 : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by simp
  have h1 : Ideal.map (V.ι.appLE V ⊤ e1).hom (D.ideal ⟨V, hV⟩) = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ e1, ← restrictIdeal_eq_comap_ι, hD]
    simp
  rw [ι_appLE_self_top_eq_topIso_inv_consolidated185] at h1
  exact ideal_eq_top_of_map_eq_top_of_leftInverse_consolidated185 _ V.topIso.hom.hom (topIso_hom_inv_apply_consolidated185 V) _ h1


end

section
variable (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (h : Y ⟶ X) [Smooth h]

private theorem finiteType_sectionsAlgebra_of_isAffineOpen_consolidated185 {V : Y.Opens} (hV : IsAffineOpen V) :
    @Algebra.FiniteType k Γ(Y, V) _ _ (sectionsAlgebra k (h ≫ p) V) :=
  @finiteType_sections k _ Y (h ≫ p) _ ⟨V, hV⟩ (sectionsAlgebra k (h ≫ p) V)
    (algebraMap_sectionsAlgebra k (h ≫ p) V)

private theorem exists_etale_mvPolynomialHom_castAdd_coord_consolidated185 {W : X.Opens} (hW : IsAffineOpen W) {m : ℕ} (cW : EtaleChart p W m)
    {V : Y.Opens} (hV : IsAffineOpen V) (e : V ≤ h ⁻¹ᵁ W) {d : ℕ}
    (g : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) W.toScheme) (hgE : Etale g)
    (hg : g ≫ (AffineSpace (ULift.{u} (Fin d)) W.toScheme ↘ W.toScheme) = h.resLE W V e) :
    ∃ ψ : MvPolynomial (ULift.{u} (Fin (m + d))) k →+* Γ(Y, V),
      ψ.Etale ∧ (∀ a : k, ψ (MvPolynomial.C a) = sectionsAlgebraMap k (h ≫ p) V a) ∧
        ∀ j : Fin m, ψ (MvPolynomial.X (ULift.up (Fin.castAdd d j)))
          = (h.appLE W V e).hom (cW.coord j) := by
  have := hgE
  let _ : Algebra k Γ(X, W) := sectionsAlgebra k p W
  let _ : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W) := cW.algebra
  have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W) := cW.isScalarTower
  have : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W) :=
    cW.algebra_formallyEtale hW
  let _ : Algebra (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
  have : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) :=
    chartAlgebra_formallyEtale hW hV g
  set χ : MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k →+* Γ(Y, V) :=
    (chartEvalHom hW g).comp
      (EtaleCoordinates.sumEval k (ULift.{u} (Fin m)) (ULift.{u} (Fin d)) Γ(X, W)).toRingHom
    with hχdef
  let _ : Algebra (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V) := χ.toAlgebra
  let _ := EtaleCoordinates.sumEvalAlgebra k (ULift.{u} (Fin m)) (ULift.{u} (Fin d)) Γ(X, W)
  have : IsScalarTower (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
      (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [EtaleCoordinates.algebraMap_eq_sumEval]
      rfl)
  have : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
      Γ(Y, V) :=
    EtaleCoordinates.formallyEtale_trans k (ULift.{u} (Fin m)) (ULift.{u} (Fin d)) Γ(X, W)
      Γ(Y, V)
  have hCval : ∀ a : k, χ (MvPolynomial.C a) = sectionsAlgebraMap k (h ≫ p) V a := by
    intro a
    have hc := (EtaleCoordinates.sumEval k (ULift.{u} (Fin m)) (ULift.{u} (Fin d))
      Γ(X, W)).commutes a
    rw [MvPolynomial.algebraMap_eq] at hc
    have h1 : EtaleCoordinates.sumEval k (ULift.{u} (Fin m)) (ULift.{u} (Fin d)) Γ(X, W)
        (MvPolynomial.C a) = MvPolynomial.C (sectionsAlgebraMap k p W a) := by
      rw [hc, MvPolynomial.algebraMap_apply, algebraMap_sectionsAlgebra]
    rw [hχdef]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [h1, chartEvalHom_C hW h e g hg, sectionsAlgebraMap_appLE_apply]
  have hXval : ∀ j : Fin m, χ (MvPolynomial.X (Sum.inl (ULift.up j)))
      = (h.appLE W V e).hom (cW.coord j) := by
    intro j
    have h1 : EtaleCoordinates.sumEval k (ULift.{u} (Fin m)) (ULift.{u} (Fin d)) Γ(X, W)
        (MvPolynomial.X (Sum.inl (ULift.up j)))
        = MvPolynomial.C (EtaleCoordinates.coord k (ULift.{u} (Fin m)) Γ(X, W)
            (ULift.up j)) := by
      rw [← EtaleCoordinates.algebraMap_eq_sumEval]
      exact EtaleCoordinates.algebraMap_X_inl k (ULift.{u} (Fin m)) (ULift.{u} (Fin d))
        Γ(X, W) (ULift.up j)
    rw [hχdef]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [h1, cW.etaleCoordinates_coord j, chartEvalHom_C hW h e g hg]
  let _ : Algebra k Γ(Y, V) := sectionsAlgebra k (h ≫ p) V
  have : Algebra.FiniteType k Γ(Y, V) := finiteType_sectionsAlgebra_of_isAffineOpen_consolidated185 p h hV
  have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V) :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      rw [algebraMap_sectionsAlgebra, MvPolynomial.algebraMap_eq]
      exact (hCval a).symm)
  have : Algebra.FiniteType (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k
      (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V)
  have : IsNoetherianRing (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) :=
    inferInstance
  have : Algebra.FinitePresentation (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
      Γ(Y, V) := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hχE : χ.Etale := etale_of_formallyEtale_of_finitePresentation_consolidated185 χ inferInstance inferInstance
  refine ⟨χ.comp (MvPolynomial.renameEquiv k (uliftFinAddEquivSum_consolidated185 m d)).toRingEquiv.toRingHom,
    etale_comp_ringEquiv_consolidated185 χ (MvPolynomial.renameEquiv k (uliftFinAddEquivSum_consolidated185 m d)).toRingEquiv hχE,
    ?_, ?_⟩
  · intro a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_ringEquiv, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C]
    exact hCval a
  · intro j
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_ringEquiv, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
    rw [sumEquiv_castAdd_eq_inl_consolidated185]
    exact hXval j

private theorem exists_etaleChart_comap_restrictIdeal_eq_coordIdeal_consolidated185 {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (y : Y) (hy : h.base y ∈ U) :
    ∃ (V : Y.Opens) (d : ℕ) (c' : EtaleChart (h ≫ p) V (m + d)) (hVU : V ≤ h ⁻¹ᵁ U),
      IsAffineOpen V ∧ y ∈ V ∧
      (∀ j : Fin m, c'.coord (Fin.castAdd d j) = (h.appLE U V hVU).hom (c.coord j)) ∧
      (∀ D : X.IdealSheafData, restrictIdeal D U = ⊤ → restrictIdeal (D.comap h) V = ⊤) ∧
      (∀ (D : X.IdealSheafData) (S : Finset (Fin m)), restrictIdeal D U = c.coordIdeal S →
        restrictIdeal (D.comap h) V = c'.coordIdeal (S.map (Fin.castAddEmb d))) := by
  obtain ⟨W, V, d, e, hW, hV, hyV, hWU, -, g, hgE, hgc⟩ :=
    SmoothEtaleChart.exists_isAffineOpen_etale_resLE_le h y U hy ⊤ (by trivial)
  obtain ⟨ψ, hψE, hψC, hψX⟩ := exists_etale_mvPolynomialHom_castAdd_coord_consolidated185 p h hW (c.restrict hWU) hV e g hgE hgc
  have hVU : V ≤ h ⁻¹ᵁ U := fun z hz => hWU (e hz)
  set v : ULift.{u} (Fin (m + d)) → Γ(V.toScheme, ⊤) :=
    fun i => V.topIso.inv.hom (ψ (MvPolynomial.X i)) with hvdef
  have hEt : Etale (AffineSpace.homOfVector (V.ι ≫ (h ≫ p)) v) :=
    etale_homOfVector_of_ringHom_etale (h ≫ p) hV ψ hψC hψE
      (y := fun i => ψ (MvPolynomial.X i)) (hX := fun _ => rfl)
  have hcoordEq : ∀ j : Fin m,
      (EtaleChart.ofCoords (h ≫ p) V v hEt).coord (Fin.castAdd d j)
        = ψ (MvPolynomial.X (ULift.up (Fin.castAdd d j))) := by
    intro j
    rw [EtaleChart.coord_def, EtaleChart.ofCoords_map,
      show (AffineSpace.homOfVector (V.ι ≫ (h ≫ p)) v).appTop.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up (Fin.castAdd d j)))
          = v (ULift.up (Fin.castAdd d j)) from
        AffineSpace.homOfVector_appTop_coord _ _ _]
    rw [hvdef]
    exact topIso_hom_inv_apply_consolidated185 V _
  refine ⟨V, d, EtaleChart.ofCoords (h ≫ p) V v hEt, hVU, hV, hyV, ?_, ?_, ?_⟩
  · intro j
    refine (hcoordEq j).trans ((hψX j).trans ?_)
    rw [EtaleChart.coord_restrict c hWU j]
    have h5 := congrArg (fun φ : Γ(X, U) ⟶ Γ(Y, V) => φ.hom (c.coord j))
      (appLE_eq_map_comp_appLE_consolidated185 h hWU e hVU)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h5
    exact h5.symm
  · intro D hD
    have h1 : restrictIdeal D W = ⊤ := restrictIdeal_eq_top_of_le D hWU hD
    have h2 : D.ideal ⟨W, hW⟩ = ⊤ := ideal_affineOpen_eq_top_of_restrictIdeal_eq_top_consolidated185 hW D h1
    have h3 : (D.comap h).ideal ⟨V, hV⟩ = ⊤ := by
      rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE D h ⟨W, hW⟩ ⟨V, hV⟩ e, h2, Ideal.map_top]
    exact restrictIdeal_eq_top_of_ideal_eq_top_consolidated185 hV (D.comap h) h3
  · intro D S hD
    have h1 : restrictIdeal D W = (c.restrict hWU).coordIdeal S :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hWU c D S hD
    have h2 : D.ideal ⟨W, hW⟩
        = Ideal.span ((c.restrict hWU).coord '' (S : Set (Fin m))) :=
      EtaleChart.ideal_eq_span_coord (c.restrict hWU) hW D S h1
    apply restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV
    rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE D h ⟨W, hW⟩ ⟨V, hV⟩ e, h2, Ideal.map_span]
    congr 1
    rw [Finset.coe_map, Set.image_image, Set.image_image]
    have hEq : ∀ i : Fin m, (h.appLE W V e).hom ((c.restrict hWU).coord i)
        = (EtaleChart.ofCoords (h ≫ p) V v hEt).coord (Fin.castAddEmb d i) := by
      intro i
      rw [Fin.castAddEmb_apply]
      exact ((hcoordEq i).trans (hψX i)).symm
    exact Set.image_congr (fun i _ => hEq i)

theorem exists_etaleChart_comap_coord_eq {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (y : Y)
    (hy : h.base y ∈ U) :
    ∃ (V : Y.Opens) (hVU : V ≤ h ⁻¹ᵁ U) (d : ℕ) (c' : EtaleChart (h ≫ p) V (m + d)),
      IsAffineOpen V ∧ y ∈ V ∧
        ∀ j : Fin m,
          c'.coord (Fin.castAdd d j) = (h.appLE U V hVU).hom (c.coord j) := by
  obtain ⟨V, d, c', hVU, hV, hyV, hcoord, -, -⟩ := exists_etaleChart_comap_restrictIdeal_eq_coordIdeal_consolidated185 p h c y hy
  exact ⟨V, hVU, d, c', hV, hyV, hcoord⟩

theorem isSmoothDivisor_comap_of_mem_inStrictNormalCrossingPosition (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (D : X.IdealSheafData) (hD : D ∈ E) :
    IsSmoothDivisor (h ≫ p) (D.comap h) := by
  obtain ⟨i, hi, hEi⟩ := List.mem_iff_getElem.1 hD
  refine isSmoothDivisor_of_locally_coordIdeal (D.comap h) ?_
  intro y
  obtain ⟨U, hxU, m, c, a, _, hnone, hsome⟩ := ((inStrictNormalCrossingPosition_iff p E).1 hE).2 (h.base y)
  obtain ⟨V, d, c', _, _, hyV, _, htop, hcid⟩ := exists_etaleChart_comap_restrictIdeal_eq_coordIdeal_consolidated185 p h c y hxU
  refine ⟨V, hyV, m + d, c', ?_⟩
  cases hai : a i with
  | none =>
      left
      have h1 := hnone i hi hai
      rw [hEi] at h1
      exact htop D h1
  | some t =>
      right
      refine ⟨Fin.castAdd d t, ?_⟩
      have h1 := hsome i hi t hai
      rw [hEi] at h1
      have h2 := hcid D {t} h1
      rw [Finset.map_singleton, Fin.castAddEmb_apply] at h2
      exact h2


end

private theorem strictNormalCrossings_chart_conditions_comap_consolidated185 (p : X ⟶ Spec (CommRingCat.of k)) (h : Y ⟶ X)
    (E : List X.IdealSheafData) {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (a : ℕ → Option (Fin m))
    (hinj : ∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j)
    (hnone : ∀ (i : ℕ) (hi : i < E.length), a i = none → restrictIdeal E[i] U = ⊤)
    (hsome : ∀ (i : ℕ) (hi : i < E.length) (t : Fin m), a i = some t →
      restrictIdeal E[i] U = c.coordIdeal {t})
    {V : Y.Opens} {d : ℕ} (c' : EtaleChart (h ≫ p) V (m + d))
    (htop : ∀ D : X.IdealSheafData, restrictIdeal D U = ⊤ → restrictIdeal (D.comap h) V = ⊤)
    (hcid : ∀ (D : X.IdealSheafData) (S : Finset (Fin m)), restrictIdeal D U = c.coordIdeal S →
      restrictIdeal (D.comap h) V = c'.coordIdeal (S.map (Fin.castAddEmb d))) :
    (∀ i < (E.map (fun D => D.comap h)).length, ∀ j < (E.map (fun D => D.comap h)).length,
        ∀ t : Fin (m + d), Option.map (Fin.castAdd d) (a i) = some t →
          Option.map (Fin.castAdd d) (a j) = some t → i = j) ∧
      (∀ (i : ℕ) (hi : i < (E.map (fun D => D.comap h)).length),
          Option.map (Fin.castAdd d) (a i) = none →
          restrictIdeal (E.map (fun D => D.comap h))[i] V = ⊤) ∧
      (∀ (i : ℕ) (hi : i < (E.map (fun D => D.comap h)).length) (t : Fin (m + d)),
          Option.map (Fin.castAdd d) (a i) = some t →
          restrictIdeal (E.map (fun D => D.comap h))[i] V = c'.coordIdeal {t}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj t h1 h2
    have hi' : i < E.length := by simpa using hi
    have hj' : j < E.length := by simpa using hj
    cases hai : a i with
    | none => rw [hai] at h1; simp at h1
    | some t₁ =>
      cases haj : a j with
      | none => rw [haj] at h2; simp at h2
      | some t₂ =>
        rw [hai] at h1
        rw [haj] at h2
        have e1 : Fin.castAdd d t₁ = t := Option.some.inj h1
        have e2 : Fin.castAdd d t₂ = t := Option.some.inj h2
        have ht : t₁ = t₂ := (Fin.castAddEmb d).injective (by
          rw [Fin.castAddEmb_apply, Fin.castAddEmb_apply, e1, e2])
        exact hinj i hi' j hj' t₁ hai (by rw [haj, ht])
  · intro i hi hni
    have hi' : i < E.length := by simpa using hi
    have hgi : (E.map (fun D => D.comap h))[i]'hi = (E[i]'hi').comap h := by simp
    rw [hgi]
    cases hai : a i with
    | none => exact htop _ (hnone i hi' hai)
    | some _ => rw [hai] at hni; simp at hni
  · intro i hi t h1
    have hi' : i < E.length := by simpa using hi
    have hgi : (E.map (fun D => D.comap h))[i]'hi = (E[i]'hi').comap h := by simp
    rw [hgi]
    cases hai : a i with
    | none => rw [hai] at h1; simp at h1
    | some t₁ =>
      rw [hai] at h1
      have e1 : Fin.castAdd d t₁ = t := Option.some.inj h1
      have h2 := hcid _ {t₁} (hsome i hi' t₁ hai)
      rw [Finset.map_singleton, Fin.castAddEmb_apply, e1] at h2
      exact h2

section
variable (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (h : Y ⟶ X) [Smooth h]

theorem inStrictNormalCrossingPosition_comap (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) :
    InStrictNormalCrossingPosition (h ≫ p) (E.map (fun D => D.comap h)) := by
  rw [inStrictNormalCrossingPosition_iff]
  refine ⟨?_, ?_⟩
  · intro D hD
    rw [List.mem_map] at hD
    obtain ⟨D₀, hD₀, rfl⟩ := hD
    exact isSmoothDivisor_comap_of_mem_inStrictNormalCrossingPosition p h E hE D₀ hD₀
  · intro y
    obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := ((inStrictNormalCrossingPosition_iff p E).1 hE).2 (h.base y)
    obtain ⟨V, d, c', _, _, hyV, _, htop, hcid⟩ := exists_etaleChart_comap_restrictIdeal_eq_coordIdeal_consolidated185 p h c y hxU
    have hL := strictNormalCrossings_chart_conditions_comap_consolidated185 p h E c a hinj hnone hsome c' htop hcid
    exact ⟨V, hyV, m + d, c', fun i => Option.map (Fin.castAdd d) (a i),
      hL.1, hL.2.1, hL.2.2⟩

theorem inStrictNormalCrossingPosition_comap_singleton (H : X.IdealSheafData) (hH : InStrictNormalCrossingPosition p [H]) :
    InStrictNormalCrossingPosition (h ≫ p) [H.comap h] := by
  have hcomp := inStrictNormalCrossingPosition_comap p h [H] hH
  rw [List.map_cons, List.map_nil] at hcomp
  exact hcomp


end

private theorem base_mem_support_of_mem_support_comap_consolidated185 (f : Y ⟶ X) (I : X.IdealSheafData) (y : Y)
    (hy : y ∈ (I.comap f).support) : f.base y ∈ I.support := by
  rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] at hy
  exact hy

theorem hasStrictNormalCrossingsWith_comap (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (h : Y ⟶ X) [Smooth h]
    (Z : X.IdealSheafData) (E : List X.IdealSheafData) (hZ : HasStrictNormalCrossingsWith p Z E) :
    HasStrictNormalCrossingsWith (h ≫ p) (Z.comap h) (E.map (fun D => D.comap h)) := by
  intro y hy
  have hxZ : h.base y ∈ Z.support := base_mem_support_of_mem_support_comap_consolidated185 h Z y hy
  obtain ⟨U, hxU, m, c, a, S, hinj, hnone, hsome, hZU⟩ := hZ (h.base y) hxZ
  obtain ⟨V, d, c', _, _, hyV, _, htop, hcid⟩ := exists_etaleChart_comap_restrictIdeal_eq_coordIdeal_consolidated185 p h c y hxU
  have hL := strictNormalCrossings_chart_conditions_comap_consolidated185 p h E c a hinj hnone hsome c' htop hcid
  exact ⟨V, hyV, m + d, c', fun i => Option.map (Fin.castAdd d) (a i), S.map (Fin.castAddEmb d),
    hL.1, hL.2.1, hL.2.2, hcid Z S hZU⟩

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsWithoutUnitIdeals
section


section

variable {X : Scheme.{u}} {k : Type u} [Field k]

noncomputable def filterNeTop (E : List X.IdealSheafData) : List X.IdealSheafData :=
  E.filter (fun D => @decide (D ≠ ⊤) (Classical.propDecidable _))

private theorem filterNeTop_nil_consolidated178 : filterNeTop ([] : List X.IdealSheafData) = [] := rfl

private theorem filterNeTop_cons_of_ne_top_consolidated178 (D : X.IdealSheafData) (T : List X.IdealSheafData)
    (h : D ≠ ⊤) : filterNeTop (D :: T) = D :: filterNeTop T := by
  simp [filterNeTop, h]

private theorem filterNeTop_cons_top_consolidated178 (T : List X.IdealSheafData) :
    filterNeTop ((⊤ : X.IdealSheafData) :: T) = filterNeTop T := by
  simp [filterNeTop]

section
variable {D : X.IdealSheafData} {E : List X.IdealSheafData}

private theorem mem_of_mem_filterNeTop_consolidated178 (h : D ∈ filterNeTop E) : D ∈ E := by
  simp only [filterNeTop, List.mem_filter] at h
  exact h.1

private theorem mem_filterNeTop_consolidated178 (hD : D ∈ E) (h : D ≠ ⊤) : D ∈ filterNeTop E := by
  simp only [filterNeTop, List.mem_filter]
  exact ⟨hD, by simpa using h⟩


end

private def unshiftIndex_consolidated178 (g₀ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => g₀ i

private def shiftIndex_consolidated178 (g₀ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => g₀ i + 1

private theorem exists_index_map_of_filterNeTop_eq_consolidated178 (n : ℕ) :
    ∀ (E E' : List X.IdealSheafData),
    E.length + E'.length ≤ n → filterNeTop E' = filterNeTop E →
    ∃ g : ℕ → ℕ,
      (∀ i, i < E'.length → E'[i]? ≠ some ⊤ → g i < E.length ∧ E[g i]? = E'[i]?) ∧
      (∀ i j, i < E'.length → j < E'.length → E'[i]? ≠ some ⊤ → E'[j]? ≠ some ⊤ →
        g i = g j → i = j) := by
  induction n with
  | zero =>
    intro E E' hlen _
    have h0 : E'.length = 0 := by omega
    exact ⟨id, fun i hi _ => absurd hi (by omega), fun i j hi _ _ _ _ => absurd hi (by omega)⟩
  | succ n ih =>
    intro E E' hlen hfilt
    cases E' with
    | nil =>
      exact ⟨id, fun i hi _ => absurd hi (by simp), fun i j hi _ _ _ _ => absurd hi (by simp)⟩
    | cons D T' =>
      by_cases hD : D = ⊤
      · subst hD
        rw [filterNeTop_cons_top_consolidated178] at hfilt
        have hlen' : E.length + T'.length ≤ n := by
          simp only [List.length_cons] at hlen
          omega
        obtain ⟨g₀, h1, h2⟩ := ih E T' hlen' hfilt
        refine ⟨unshiftIndex_consolidated178 g₀, ?_, ?_⟩
        · intro i hi hne
          cases i with
          | zero => simp at hne
          | succ i =>
            simp only [List.getElem?_cons_succ] at hne
            simp only [List.length_cons] at hi
            simp only [unshiftIndex_consolidated178, List.getElem?_cons_succ]
            exact h1 i (by omega) hne
        · intro i j hi hj hni hnj hgij
          cases i with
          | zero => simp at hni
          | succ i =>
            cases j with
            | zero => simp at hnj
            | succ j =>
              have e1 : unshiftIndex_consolidated178 g₀ (i + 1) = g₀ i := rfl
              have e2 : unshiftIndex_consolidated178 g₀ (j + 1) = g₀ j := rfl
              have hij : g₀ i = g₀ j := by omega
              simp only [List.getElem?_cons_succ] at hni hnj
              simp only [List.length_cons] at hi hj
              have := h2 i j (by omega) (by omega) hni hnj hij
              omega
      · rw [filterNeTop_cons_of_ne_top_consolidated178 D T' hD] at hfilt
        cases E with
        | nil =>
          rw [filterNeTop_nil_consolidated178] at hfilt
          exact absurd hfilt (List.cons_ne_nil _ _)
        | cons C T =>
          by_cases hC : C = ⊤
          · subst hC
            rw [filterNeTop_cons_top_consolidated178] at hfilt
            have hlen' : T.length + (D :: T').length ≤ n := by
              simp only [List.length_cons] at hlen ⊢
              omega
            have hfilt' : filterNeTop (D :: T') = filterNeTop T := by
              rw [filterNeTop_cons_of_ne_top_consolidated178 D T' hD]
              exact hfilt
            obtain ⟨g₀, h1, h2⟩ := ih T (D :: T') hlen' hfilt'
            refine ⟨fun i => g₀ i + 1, ?_, ?_⟩
            · intro i hi hne
              obtain ⟨ha, hb⟩ := h1 i hi hne
              refine ⟨by simp only [List.length_cons]; omega, ?_⟩
              simpa using hb
            · intro i j hi hj hni hnj hgij
              have hgij' : g₀ i + 1 = g₀ j + 1 := hgij
              exact h2 i j hi hj hni hnj (by omega)
          · rw [filterNeTop_cons_of_ne_top_consolidated178 C T hC] at hfilt
            simp only [List.cons.injEq] at hfilt
            obtain ⟨hcond, hTT⟩ := hfilt
            have hlen' : T.length + T'.length ≤ n := by
              simp only [List.length_cons] at hlen
              omega
            obtain ⟨g₀, h1, h2⟩ := ih T T' hlen' hTT
            refine ⟨shiftIndex_consolidated178 g₀, ?_, ?_⟩
            · intro i hi hne
              cases i with
              | zero =>
                simp only [shiftIndex_consolidated178]
                refine ⟨by simp, ?_⟩
                simp [hcond]
              | succ i =>
                simp only [List.getElem?_cons_succ] at hne
                simp only [List.length_cons] at hi
                obtain ⟨ha, hb⟩ := h1 i (by omega) hne
                simp only [shiftIndex_consolidated178, List.getElem?_cons_succ]
                exact ⟨by simp only [List.length_cons]; omega, hb⟩
            · intro i j hi hj hni hnj hgij
              cases i with
              | zero =>
                cases j with
                | zero => rfl
                | succ j =>
                  have e1 : shiftIndex_consolidated178 g₀ 0 = 0 := rfl
                  have e2 : shiftIndex_consolidated178 g₀ (j + 1) = g₀ j + 1 := rfl
                  omega
              | succ i =>
                cases j with
                | zero =>
                  have e1 : shiftIndex_consolidated178 g₀ 0 = 0 := rfl
                  have e2 : shiftIndex_consolidated178 g₀ (i + 1) = g₀ i + 1 := rfl
                  omega
                | succ j =>
                  have e1 : shiftIndex_consolidated178 g₀ (i + 1) = g₀ i + 1 := rfl
                  have e2 : shiftIndex_consolidated178 g₀ (j + 1) = g₀ j + 1 := rfl
                  have hij : g₀ i = g₀ j := by omega
                  simp only [List.getElem?_cons_succ] at hni hnj
                  simp only [List.length_cons] at hi hj
                  have := h2 i j (by omega) (by omega) hni hnj hij
                  omega

open Classical in
private def transportAssignment_consolidated178 {m : ℕ} (E' : List X.IdealSheafData) (a : ℕ → Option (Fin m))
    (g : ℕ → ℕ) : ℕ → Option (Fin m) :=
  fun i => if E'[i]? = some ⊤ then none else a (g i)

section
variable {m : ℕ} (E' : List X.IdealSheafData) (a : ℕ → Option (Fin m)) (g : ℕ → ℕ) (i : ℕ)

private theorem transportAssignment_of_eq_top_consolidated178 (h : E'[i]? = some ⊤) :
    transportAssignment_consolidated178 E' a g i = none := by
  simp [transportAssignment_consolidated178, h]

private theorem transportAssignment_of_ne_top_consolidated178 (h : E'[i]? ≠ some ⊤) :
    transportAssignment_consolidated178 E' a g i = a (g i) := by
  simp [transportAssignment_consolidated178, h]


end

private theorem transportAssignment_injective_and_coordIdeal_consolidated178 {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (E E' : List X.IdealSheafData) (a : ℕ → Option (Fin m)) (g : ℕ → ℕ)
    (hg1 : ∀ i, i < E'.length → E'[i]? ≠ some ⊤ → g i < E.length ∧ E[g i]? = E'[i]?)
    (hg2 : ∀ i j, i < E'.length → j < E'.length → E'[i]? ≠ some ⊤ → E'[j]? ≠ some ⊤ →
      g i = g j → i = j)
    (hinj : ∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j)
    (hnone : ∀ (i : ℕ) (hi : i < E.length), a i = none → restrictIdeal E[i] U = ⊤)
    (hsome : ∀ (i : ℕ) (hi : i < E.length) (t : Fin m), a i = some t →
      restrictIdeal E[i] U = c.coordIdeal {t}) :
    (∀ i < E'.length, ∀ j < E'.length, ∀ t : Fin m,
        transportAssignment_consolidated178 E' a g i = some t → transportAssignment_consolidated178 E' a g j = some t → i = j) ∧
      (∀ (i : ℕ) (hi : i < E'.length), transportAssignment_consolidated178 E' a g i = none →
        restrictIdeal E'[i] U = ⊤) ∧
      (∀ (i : ℕ) (hi : i < E'.length) (t : Fin m), transportAssignment_consolidated178 E' a g i = some t →
        restrictIdeal E'[i] U = c.coordIdeal {t}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj t hti htj
    have hni : E'[i]? ≠ some ⊤ := by
      intro hc
      rw [transportAssignment_of_eq_top_consolidated178 E' a g i hc] at hti
      simp at hti
    have hnj : E'[j]? ≠ some ⊤ := by
      intro hc
      rw [transportAssignment_of_eq_top_consolidated178 E' a g j hc] at htj
      simp at htj
    rw [transportAssignment_of_ne_top_consolidated178 E' a g i hni] at hti
    rw [transportAssignment_of_ne_top_consolidated178 E' a g j hnj] at htj
    obtain ⟨hgi, -⟩ := hg1 i hi hni
    obtain ⟨hgj, -⟩ := hg1 j hj hnj
    exact hg2 i j hi hj hni hnj (hinj (g i) hgi (g j) hgj t hti htj)
  · intro i hi hn
    by_cases hc : E'[i]? = some ⊤
    · have he : E'[i] = ⊤ := by
        rw [List.getElem?_eq_getElem hi] at hc
        exact Option.some_inj.mp hc
      rw [he]
      exact Scheme.IdealSheafData.comap_top U.ι
    · rw [transportAssignment_of_ne_top_consolidated178 E' a g i hc] at hn
      obtain ⟨hgi, hb⟩ := hg1 i hi hc
      have he : E[g i] = E'[i] := by
        rw [List.getElem?_eq_getElem hgi, List.getElem?_eq_getElem hi] at hb
        exact Option.some_inj.mp hb
      rw [← he]
      exact hnone (g i) hgi hn
  · intro i hi t hti
    have hc : E'[i]? ≠ some ⊤ := by
      intro hc
      rw [transportAssignment_of_eq_top_consolidated178 E' a g i hc] at hti
      simp at hti
    rw [transportAssignment_of_ne_top_consolidated178 E' a g i hc] at hti
    obtain ⟨hgi, hb⟩ := hg1 i hi hc
    have he : E[g i] = E'[i] := by
      rw [List.getElem?_eq_getElem hgi, List.getElem?_eq_getElem hi] at hb
      exact Option.some_inj.mp hb
    rw [← he]
    exact hsome (g i) hgi t hti

section
variable (p : X ⟶ Spec (CommRingCat.of k))

theorem isSmoothDivisor_top [Smooth p] :
    IsSmoothDivisor p (⊤ : X.IdealSheafData) := by
  refine isSmoothDivisor_of_locally_coordIdeal (p := p) ⊤ ?_
  intro x
  obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p x
  exact ⟨U, hxU, m, c, Or.inl (Scheme.IdealSheafData.comap_top U.ι)⟩

theorem inStrictNormalCrossingPositionAt_of_filterNeTop_eq (E E' : List X.IdealSheafData) (h : filterNeTop E = filterNeTop E') (x : X)
    (hE : InStrictNormalCrossingPositionAt p E x) : InStrictNormalCrossingPositionAt p E' x := by
  obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := hE.exists_etaleChart
  obtain ⟨g, hg1, hg2⟩ :=
    exists_index_map_of_filterNeTop_eq_consolidated178 (E.length + E'.length) E E' le_rfl h.symm
  obtain ⟨k1, k2, k3⟩ := transportAssignment_injective_and_coordIdeal_consolidated178 c E E' a g hg1 hg2 hinj hnone hsome
  exact inStrictNormalCrossingPositionAt_of_exists_etaleChart ⟨U, hxU, m, c, transportAssignment_consolidated178 E' a g, k1, k2, k3⟩

theorem inStrictNormalCrossingPosition_of_filterNeTop_eq [Smooth p] (E E' : List X.IdealSheafData)
    (h : filterNeTop E = filterNeTop E') (hE : InStrictNormalCrossingPosition p E) :
    InStrictNormalCrossingPosition p E' := by
  rw [inStrictNormalCrossingPosition_iff] at hE ⊢
  obtain ⟨hsm, hpos⟩ := hE
  refine ⟨?_, fun x => inStrictNormalCrossingPositionAt_of_filterNeTop_eq p E E' h x (hpos x)⟩
  intro D hD
  by_cases hDt : D = ⊤
  · rw [hDt]
    exact isSmoothDivisor_top p
  · have h1 : D ∈ filterNeTop E' := mem_filterNeTop_consolidated178 hD hDt
    rw [← h] at h1
    exact hsm D (mem_of_mem_filterNeTop_consolidated178 h1)

theorem hasStrictNormalCrossingsWith_of_filterNeTop_eq (Z : X.IdealSheafData) (E E' : List X.IdealSheafData)
    (h : filterNeTop E = filterNeTop E') (hE : HasStrictNormalCrossingsWith p Z E) :
    HasStrictNormalCrossingsWith p Z E' := by
  obtain ⟨g, hg1, hg2⟩ :=
    exists_index_map_of_filterNeTop_eq_consolidated178 (E.length + E'.length) E E' le_rfl h.symm
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hxU, m, c, a, S, hinj, hnone, hsome, hZ⟩ := hE.exists_etaleChart hx
  obtain ⟨k1, k2, k3⟩ := transportAssignment_injective_and_coordIdeal_consolidated178 c E E' a g hg1 hg2 hinj hnone hsome
  exact ⟨U, hxU, m, c, transportAssignment_consolidated178 E' a g, S, k1, k2, k3, hZ⟩


end

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinateCodimensionCriterion
section

open TopologicalSpace

section

def castAddImage (c d : ℕ) : Finset (Fin (c + d)) :=
  (Finset.univ : Finset (Fin c)).image (Fin.castAdd d)

section
variable (c d : ℕ)

theorem castAddImage_eq_image_castAdd :
    castAddImage c d = (Finset.univ : Finset (Fin c)).image (Fin.castAdd d) := rfl

theorem card_castAddImage : (castAddImage c d).card = c := by
  have hinj : Function.Injective (Fin.castAdd d : Fin c → Fin (c + d)) := by
    intro a b hab
    have hv : ((Fin.castAdd d a : Fin (c + d)) : ℕ) = ((Fin.castAdd d b : Fin (c + d)) : ℕ) :=
      congrArg (fun z : Fin (c + d) => (z : ℕ)) hab
    exact Fin.ext hv
  rw [castAddImage_eq_image_castAdd, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_fin]


end

section
variable {X' : Scheme.{u}} (U : X'.Opens) (V : U.toScheme.Opens)

private theorem mem_image_ι_of_mem_consolidated202 (y : X') (hy : y ∈ U) (h : (⟨y, hy⟩ : ↥U) ∈ V) :
    y ∈ U.ι ''ᵁ V :=
  ⟨⟨y, hy⟩, h, rfl⟩

private theorem range_ι_comp_ι_eq_image_consolidated202 :
    Set.range ((V.ι ≫ U.ι).base) = (↑(U.ι ''ᵁ V) : Set ↥X') := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, w.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩


end

private def etaleChartTop_consolidated202 (k : Type u) [Field k] (c : ℕ) :
    EtaleChart (affineSpaceFinToSpec k c) (⊤ : (affineSpaceFin k c).Opens) c where
  map := (⊤ : (affineSpaceFin k c).Opens).ι
  comp_struct := rfl
  isEtale := inferInstance

section
variable (k : Type u) [Field k] (c : ℕ)

private theorem etaleChartTop_map_consolidated202 :
    (etaleChartTop_consolidated202 k c).map = (⊤ : (affineSpaceFin k c).Opens).ι := rfl

private theorem restrictIdeal_top_coordSubspaceIdeal_univ_consolidated202 :
    restrictIdeal (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c)))
      (⊤ : (affineSpaceFin k c).Opens) = (etaleChartTop_consolidated202 k c).coordIdeal Finset.univ := by
  rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, etaleChartTop_map_consolidated202]


end

theorem exists_etaleChart_image_of_restrictIdeal_eq {X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (U : X'.Opens) (V : U.toScheme.Opens) (n : ℕ)
    (ch : EtaleChart (U.ι ≫ p) V n) (D : X'.IdealSheafData) (S : Finset (Fin n))
    (h : restrictIdeal (restrictIdeal D U) V = ch.coordIdeal S) :
    ∃ ch' : EtaleChart p (U.ι ''ᵁ V) n, restrictIdeal D (U.ι ''ᵁ V) = ch'.coordIdeal S := by
  have hr : Set.range ((U.ι ''ᵁ V).ι).base = Set.range ((V.ι ≫ U.ι).base) := by
    rw [Scheme.Opens.range_ι, ← range_ι_comp_ι_eq_image_consolidated202]
  let φ : (U.ι ''ᵁ V).toScheme ≅ V.toScheme :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq ((U.ι ''ᵁ V).ι) (V.ι ≫ U.ι) hr
  have hfac : φ.hom ≫ (V.ι ≫ U.ι) = (U.ι ''ᵁ V).ι :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hr
  have hcs : (φ.hom ≫ ch.map) ≫ affineSpaceFinToSpec k n = (U.ι ''ᵁ V).ι ≫ p := by
    calc (φ.hom ≫ ch.map) ≫ affineSpaceFinToSpec k n
        = φ.hom ≫ (ch.map ≫ affineSpaceFinToSpec k n) := Category.assoc _ _ _
      _ = φ.hom ≫ (V.ι ≫ (U.ι ≫ p)) := by rw [ch.comp_struct]
      _ = (φ.hom ≫ (V.ι ≫ U.ι)) ≫ p := by simp only [Category.assoc]
      _ = (U.ι ''ᵁ V).ι ≫ p := by rw [hfac]
  have : Etale ch.map := ch.isEtale
  have hkey : (D.comap U.ι).comap V.ι = (coordSubspaceIdeal k n S).comap ch.map := by
    rw [← restrictIdeal_eq_comap_ι, ← restrictIdeal_eq_comap_ι, h, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  refine ⟨⟨φ.hom ≫ ch.map, hcs, inferInstance⟩, ?_⟩
  rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  calc D.comap (U.ι ''ᵁ V).ι
      = ((D.comap U.ι).comap V.ι).comap φ.hom := by
        rw [← hfac, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    _ = ((coordSubspaceIdeal k n S).comap ch.map).comap φ.hom := by rw [hkey]
    _ = (coordSubspaceIdeal k n S).comap (φ.hom ≫ ch.map) := by
        rw [Scheme.IdealSheafData.comap_comp]

section
variable {X X' : Scheme.{u}} {k : Type u} [Field k] (p : X' ⟶ Spec (CommRingCat.of k))

theorem exists_etaleChart_of_restrictIdeal_ker_eq_comap
    (τ : X ⟶ X') (c : ℕ) (U : X'.Opens) (q : U.toScheme ⟶ affineSpaceFin k c)
    [Smooth q] (hq : q ≫ affineSpaceFinToSpec k c = U.ι ≫ p)
    (hker : restrictIdeal τ.ker U =
      (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))).comap q)
    (x : X) (hx : τ.base x ∈ U) :
    ∃ (V : U.toScheme.Opens) (_ : IsAffineOpen V) (_ : (⟨τ.base x, hx⟩ : ↥U) ∈ V) (d : ℕ)
      (ch : EtaleChart (U.ι ≫ p) V (c + d)),
      restrictIdeal (restrictIdeal τ.ker U) V = ch.coordIdeal (castAddImage c d) := by
  have : Smooth (affineSpaceFinToSpec k c) := affineSpaceIsSmooth ..
  obtain ⟨V, hVU, d, ch, hVaff, hyV, hcoord⟩ :=
    exists_etaleChart_comap_coord_eq (affineSpaceFinToSpec k c) q (etaleChartTop_consolidated202 k c)
      (⟨τ.base x, hx⟩ : ↥U) (by trivial)
  have hidtop : (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))).ideal
      ⟨⊤, isAffineOpen_top (affineSpaceFin k c)⟩
      = Ideal.span ((etaleChartTop_consolidated202 k c).coord ''
          ((Finset.univ : Finset (Fin c)) : Set (Fin c))) :=
    EtaleChart.ideal_eq_span_coord (etaleChartTop_consolidated202 k c) (isAffineOpen_top (affineSpaceFin k c))
      (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))) Finset.univ
      (restrictIdeal_top_coordSubspaceIdeal_univ_consolidated202 k c)
  have hspanV : (restrictIdeal τ.ker U).ideal ⟨V, hVaff⟩
      = Ideal.span (ch.coord ''
          ((castAddImage c d : Finset (Fin (c + d))) : Set (Fin (c + d)))) := by
    rw [hker,
      Scheme.IdealSheafData.comap_ideal_eq_map_appLE
        (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))) q
        ⟨⊤, isAffineOpen_top (affineSpaceFin k c)⟩ ⟨V, hVaff⟩ hVU,
      hidtop, Ideal.map_span]
    congr 1
    rw [Set.image_image, castAddImage_eq_image_castAdd, Finset.coe_image, Set.image_image]
    exact Set.image_congr (fun j _ => (hcoord j).symm)
  have hcs : ch.map ≫ affineSpaceFinToSpec k (c + d) = V.ι ≫ (U.ι ≫ p) := by
    rw [ch.comp_struct, hq]
  refine ⟨V, hVaff, hyV, d, ⟨ch.map, hcs, ch.isEtale⟩, ?_⟩
  exact restrictIdeal_eq_coordIdeal_of_ideal_eq_span hVaff _ _ (castAddImage c d) hspanV

theorem hasEtaleCoordCodim_of_locally_smooth_over_affineSpace [Smooth p] (τ : X ⟶ X') (c : ℕ)
    (h : ∀ x : X, ∃ (U : X'.Opens) (_ : τ.base x ∈ U) (q : U.toScheme ⟶ affineSpaceFin k c),
      Smooth q ∧ q ≫ affineSpaceFinToSpec k c = U.ι ≫ p ∧
        restrictIdeal τ.ker U =
          (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))).comap q) :
    HasEtaleCoordCodim p τ c := by
  intro x
  obtain ⟨U, hxU, q, hqsm, hqc, hker⟩ := h x
  have := hqsm
  obtain ⟨V, hVaff, hxV, d, ch, hch⟩ :=
    exists_etaleChart_of_restrictIdeal_ker_eq_comap p τ c U q hqc hker x hxU
  obtain ⟨ch', hch'⟩ :=
    exists_etaleChart_image_of_restrictIdeal_eq p U V (c + d) ch τ.ker (castAddImage c d) hch
  exact ⟨U.ι ''ᵁ V, mem_image_ι_of_mem_consolidated202 U V (τ.base x) hxU hxV, c + d, ch',
    castAddImage c d, card_castAddImage c d, hch'⟩


end


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsClopen
section

open Opposite TopologicalSpace

section

private theorem ideal_top_consolidated198 {X : Scheme.{u}} (U : X.affineOpens) :
    (⊤ : X.IdealSheafData).ideal U = ⊤ := by simp

private theorem ideal_comap_mul_consolidated198 {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.affineOpens)
    (V : X.affineOpens) (e : (V : X.Opens) ≤ g ⁻¹ᵁ (U : Y.Opens)) (I J : Y.IdealSheafData) :
    ((I * J).comap g).ideal V = (I.comap g).ideal V * (J.comap g).ideal V := by
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (I * J) g U V e,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE I g U V e,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE J g U V e,
    Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul]

section
variable {Y : Scheme.{u}} (V : Y.Opens)

private theorem top_le_ι_preimage_self_consolidated198 :
    (⊤ : V.toScheme.Opens) ≤ (Opens.map V.ι.base).obj V := by
  intro x _
  exact x.2

private theorem ι_appLE_top_eq_topIso_inv_consolidated198 :
    V.ι.appLE V ⊤ (top_le_ι_preimage_self_consolidated198 V) = V.topIso.inv := by
  simp
  rfl

private theorem ι_appLE_top_bijective_consolidated198 :
    Function.Injective (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self_consolidated198 V))) ∧
      Function.Surjective (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self_consolidated198 V))) := by
  rw [ι_appLE_top_eq_topIso_inv_consolidated198]
  exact V.topIso.commRingCatIsoToRingEquiv.symm.bijective


end

private theorem ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top_consolidated198 {Y : Scheme.{u}} (D : Y.IdealSheafData)
    {V : Y.Opens} (hV : IsAffineOpen V) (htop : restrictIdeal D V = ⊤) :
    D.ideal ⟨V, hV⟩ = ⊤ := by
  have : IsAffine V.toScheme := hV
  have key := Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_ι_preimage_self_consolidated198 V)
  rw [← restrictIdeal_eq_comap_ι, htop] at key
  have h0 : ((⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩) = ⊤ := by
    simp
  rw [h0] at key
  have key2 : Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self_consolidated198 V)))
      (D.ideal ⟨V, hV⟩) = ⊤ := key.symm
  have hbij := ι_appLE_top_bijective_consolidated198 V
  have hcomap : Ideal.comap (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self_consolidated198 V)))
      (Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self_consolidated198 V)))
        (D.ideal ⟨V, hV⟩)) = D.ideal ⟨V, hV⟩ := by
    apply Ideal.comap_map_of_bijective
    exact hbij
  rw [key2, Ideal.comap_top] at hcomap
  exact hcomap.symm

section
variable {X : Scheme.{u}}

private theorem etaleChartCoord_eq_coord_consolidated198 {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {V : X.Opens} {m : ℕ} (c : EtaleChart p V m) (j : Fin m) :
    @etaleChartCoord k _ m Γ(X, V) _ c.algebra j = c.coord j := by
  rw [etaleChartCoord_def, c.algebraMap_eq_coordRingHom, c.coordRingHom_X]

private theorem presheaf_map_mem_primeIdealOf_consolidated198 {V V' : X.Opens}
    (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V) (x : ↥X)
    (hxV : x ∈ V) (hxV' : x ∈ V') (s : Γ(X, V))
    (hs : s ∈ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal) :
    (X.presheaf.map (homOfLE hle).op).hom s ∈ (hV'.primeIdealOf ⟨x, hxV'⟩).asIdeal := by
  have hres : X.presheaf.map (homOfLE hle).op ≫ X.presheaf.germ V' x hxV'
      = X.presheaf.germ V x hxV := X.presheaf.germ_res (homOfLE hle) x hxV'
  have hgerm := congrArg
    (fun φ : Γ(X, V) ⟶ X.presheaf.stalk x => CommRingCat.Hom.hom φ s) hres
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hgerm
  have h1 : X.presheaf.germ V x hxV s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (germ_mem_maximalIdeal_iff hV x hxV s).mpr hs
  refine (germ_mem_maximalIdeal_iff hV' x hxV' _).mp ?_
  show (X.presheaf.germ V' x hxV').hom ((X.presheaf.map (homOfLE hle).op).hom s) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)
  rw [hgerm]
  exact h1


end

private theorem exists_finset_comap_prod_ideal_eq_span_prod_coord_consolidated198 {Y W : Scheme.{u}} {k : Type u}
    [Field k] {pY : Y ⟶ Spec (CommRingCat.of k)} (g : Y ⟶ W) (U : W.affineOpens) {V : Y.Opens}
    (hV : IsAffineOpen V) (e : V ≤ g ⁻¹ᵁ (U : W.Opens)) {n : ℕ} (c : EtaleChart pY V n) :
    ∀ (F : List W.IdealSheafData) (γ : ℕ → Option (Fin n)),
      (∀ i, ∀ h : i < F.length, γ i = none → restrictIdeal ((F[i]'h).comap g) V = ⊤) →
      (∀ i, ∀ h : i < F.length, ∀ j, γ i = some j →
        restrictIdeal ((F[i]'h).comap g) V = c.coordIdeal {j}) →
      (∀ i i', i < F.length → i' < F.length → ∀ j, γ i = some j → γ i' = some j → i = i') →
      ∃ J : Finset (Fin n),
        (∀ j ∈ J, ∃ i, ∃ _ : i < F.length, γ i = some j) ∧
        (F.prod.comap g).ideal ⟨V, hV⟩ = Ideal.span {∏ j ∈ J, c.coord j} := by
  intro F
  induction F with
  | nil =>
      intro γ _ _ _
      refine ⟨∅, by simp, ?_⟩
      have h1 : (([] : List W.IdealSheafData).prod).comap g = (⊤ : Y.IdealSheafData) := by
        rw [Blowup.idealSheafData_prod_nil]
        simp
      rw [h1, Finset.prod_empty, Ideal.span_singleton_one]
      exact ideal_top_consolidated198 _
  | cons D F ih =>
      intro γ hnone hsome hinj
      have hlen : ∀ i, i < F.length → i + 1 < (D :: F).length := by
        intro i hi
        simp only [List.length_cons]
        omega
      have hD0 : (0 : ℕ) < (D :: F).length := by
        simp only [List.length_cons]
        omega
      obtain ⟨J', hJ'mem, hJ'⟩ := ih (fun i => γ (i + 1))
        (fun i h hg => hnone (i + 1) (hlen i h) hg)
        (fun i h j hg => hsome (i + 1) (hlen i h) j hg)
        (fun i i' hi hi' j h1 h2 => by
          have h3 := hinj (i + 1) (i' + 1) (hlen i hi) (hlen i' hi') j h1 h2
          omega)
      have hprod : ((D :: F).prod.comap g).ideal ⟨V, hV⟩
          = (D.comap g).ideal ⟨V, hV⟩ * ((F.prod).comap g).ideal ⟨V, hV⟩ := by
        rw [Blowup.idealSheafData_prod_cons]
        exact ideal_comap_mul_consolidated198 g U ⟨V, hV⟩ e D F.prod
      cases hγ0 : γ 0 with
      | none =>
          have hD : (D.comap g).ideal ⟨V, hV⟩ = ⊤ :=
            ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top_consolidated198 _ hV (hnone 0 hD0 hγ0)
          refine ⟨J', ?_, ?_⟩
          · intro j hj
            obtain ⟨i, hi, hγi⟩ := hJ'mem j hj
            exact ⟨i + 1, hlen i hi, hγi⟩
          · rw [hprod, hD, hJ', Ideal.top_mul]
      | some j0 =>
          have hD : (D.comap g).ideal ⟨V, hV⟩ = Ideal.span {c.coord j0} := by
            have h2 := EtaleChart.ideal_eq_span_coord c hV (D.comap g) {j0}
              (hsome 0 hD0 j0 hγ0)
            rw [Finset.coe_singleton, Set.image_singleton] at h2
            exact h2
          have hj0 : j0 ∉ J' := by
            intro hj0mem
            obtain ⟨i, hi, hγi⟩ := hJ'mem j0 hj0mem
            have h3 := hinj 0 (i + 1) hD0 (hlen i hi) j0 hγ0 hγi
            omega
          refine ⟨insert j0 J', ?_, ?_⟩
          · intro j hj
            rcases Finset.mem_insert.mp hj with rfl | hj'
            · exact ⟨0, hD0, hγ0⟩
            · obtain ⟨i, hi, hγi⟩ := hJ'mem j hj'
              exact ⟨i + 1, hlen i hi, hγi⟩
          · rw [hprod, hD, hJ', Ideal.span_singleton_mul_span_singleton,
              Finset.prod_insert hj0]

theorem strictNormalCrossingsRestrictToClopen : StrictNormalCrossingsRestrictToClopen.{u} := by
  intro k _ W p _ E Z hE hZ T hTclosed hcomp y
  have hsmZ : Smooth (Z.subschemeι ≫ p) :=
    smooth_subschemeι_comp_of_hasStrictNormalCrossingsWith Z E hZ
  have hsmT : Smooth (T.ι ≫ (Z.subschemeι ≫ p)) := inferInstance
  obtain ⟨V, hV, hyV, n, c, γ, hγ, hinjγ, hmem⟩ :=
    exists_etaleChart_coord_mem_primeIdealOf_on_clopen p E hE Z hZ T hTclosed hcomp y
  obtain ⟨U, hyU, hU⟩ : ∃ U : W.Opens, (T.ι ≫ Z.subschemeι).base y ∈ U ∧ IsAffineOpen U := by
    obtain ⟨U, hUmem, hxU, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens W)
        (show (T.ι ≫ Z.subschemeι).base y ∈ (⊤ : W.Opens) from trivial)
    exact ⟨U, hxU, hUmem⟩
  have hyVU : y ∈ (V ⊓ (T.ι ≫ Z.subschemeι) ⁻¹ᵁ U : (T.toScheme).Opens) := ⟨hyV, hyU⟩
  obtain ⟨fs, hfle, hyf⟩ := hV.exists_basicOpen_le ⟨y, hyVU⟩ hyV
  obtain ⟨V', hV', hV'V, hV'U, hyV'⟩ :
      ∃ V' : (T.toScheme).Opens, IsAffineOpen V' ∧ V' ≤ V ∧
        V' ≤ (T.ι ≫ Z.subschemeι) ⁻¹ᵁ U ∧ y ∈ V' :=
    ⟨T.toScheme.basicOpen fs, hV.basicOpen fs, le_trans hfle inf_le_left,
      le_trans hfle inf_le_right, hyf⟩
  have hγ' : ∀ i, ∀ h : i < E.length,
      (γ i = none → restrictIdeal ((E[i]'h).comap (T.ι ≫ Z.subschemeι)) V' = ⊤) ∧
      (∀ j, γ i = some j →
        restrictIdeal ((E[i]'h).comap (T.ι ≫ Z.subschemeι)) V'
          = (c.restrict hV'V).coordIdeal {j}) := by
    intro i h
    refine ⟨fun hg => restrictIdeal_eq_top_of_le _ hV'V ((hγ i h).1 hg), fun j hg => ?_⟩
    exact restrictIdeal_eq_restrict_coordIdeal_of_le hV'V c _ {j} ((hγ i h).2 j hg)
  obtain ⟨J₀, hJ₀mem, hJ₀⟩ :=
    exists_finset_comap_prod_ideal_eq_span_prod_coord_consolidated198 (T.ι ≫ Z.subschemeι) ⟨U, hU⟩ hV' hV'U
      (c.restrict hV'V) E γ (fun i h => (hγ' i h).1) (fun i h => (hγ' i h).2) hinjγ
  have hJ₀prime : ∀ j ∈ J₀,
      (c.restrict hV'V).coord j ∈ (hV'.primeIdealOf ⟨y, hyV'⟩).asIdeal := by
    intro j hj
    obtain ⟨i, hi, hγi⟩ := hJ₀mem j hj
    rw [FunctorialResolution.EmbeddedResolution.EtaleChart.coord_restrict c hV'V j]
    exact presheaf_map_mem_primeIdealOf_consolidated198 hV hV' hV'V y hyV hyV' (c.coord j) (hmem i hi j hγi)
  have hntr : Nontrivial ↥(T.toScheme.presheaf.obj (op V')) := by
    rcases subsingleton_or_nontrivial ↥(T.toScheme.presheaf.obj (op V')) with hs | hs
    · exfalso
      refine (hV'.primeIdealOf ⟨y, hyV'⟩).isPrime.ne_top ?_
      rw [Ideal.eq_top_iff_one]
      have h10 : (1 : ↥(T.toScheme.presheaf.obj (op V'))) = 0 := @Subsingleton.elim _ hs 1 0
      rw [h10]
      exact Submodule.zero_mem _
    · exact hs
  have hcinj : Function.Injective (c.restrict hV'V).coord := by
    have h := @etaleChartCoord_injective k _ n ↥(T.toScheme.presheaf.obj (op V')) _
      (c.restrict hV'V).algebra ((c.restrict hV'V).algebra_etale hV') hntr
    intro a b hab
    refine h ?_
    simp only [etaleChartCoord_eq_coord_consolidated198]
    exact hab
  have hrad := @isRadical_span_singleton_prod_etaleChartCoord k _ n
    ↥(T.toScheme.presheaf.obj (op V')) _ (c.restrict hV'V).algebra
    ((c.restrict hV'V).algebra_etale hV') J₀
  simp only [etaleChartCoord_eq_coord_consolidated198] at hrad
  obtain ⟨N, f, hfcoord, hfreg⟩ :=
    exists_isRegularParameterSystem_with_coords_of_mem_prime hV' (c.restrict hV'V) y hyV'
      J₀ hJ₀prime
  choose ι hι using hfcoord
  have hinj2 : ∀ a ∈ J₀.attach, ∀ b ∈ J₀.attach,
      (fun j : { x // x ∈ J₀ } => ι j.1 j.2) a = (fun j : { x // x ∈ J₀ } => ι j.1 j.2) b →
        a = b := by
    intro a _ b _ hab
    have h1 : (c.restrict hV'V).coord a.1 = (c.restrict hV'V).coord b.1 := by
      rw [← hι a.1 a.2, ← hι b.1 b.2]
      exact congrArg f hab
    exact Subtype.ext (hcinj h1)
  have hprodJ : (∏ i ∈ J₀.attach.image (fun j : { x // x ∈ J₀ } => ι j.1 j.2), f i)
      = ∏ j ∈ J₀, (c.restrict hV'V).coord j := by
    rw [Finset.prod_image hinj2, ← Finset.prod_attach J₀ (fun j => (c.restrict hV'V).coord j)]
    exact Finset.prod_congr rfl fun j _ => hι j.1 j.2
  refine ⟨isRegularLocalRing_stalk_of_smooth (T.ι ≫ (Z.subschemeι ≫ p)) y,
    ⟨V', hV'⟩, hyV', N, f, J₀.attach.image (fun j : { x // x ∈ J₀ } => ι j.1 j.2), hfreg, ?_⟩
  rw [Scheme.IdealSheafData.radical_ideal, hJ₀, hrad.radical, hprodJ]


end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
section

open TopologicalSpace


section
variable {X : Scheme.{u}}

theorem support_subset_orderAtLeastLocus_of_le_pow (Z I : X.IdealSheafData) (m : ℕ)
    (h : I ≤ Z ^ m) : (Z.support : Set X) ⊆ orderAtLeastLocus I m := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff_stalkIdeal_le_maximalIdeal_pow]
  have h1 : stalkIdeal I x ≤ stalkIdeal (Z ^ m) x := stalkIdeal_mono h x
  rw [stalkIdeal_pow] at h1
  refine h1.trans (Ideal.pow_right_mono ?_ m)
  exact (mem_support_iff_stalkIdeal_le_maximalIdeal Z x).mp hx

private theorem mem_support_iff_ideal_le_primeIdealOf_of_isAffineOpen_consolidated177 (I : X.IdealSheafData) {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) :
    (x : X) ∈ I.support ↔ I.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf x).asIdeal := by
  have := hU.isLocalization_stalk x
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_eq_map_germ I (x : X) ⟨U, hU⟩ x.2]
  constructor
  · intro hle y hy
    have h2 : (X.presheaf.germ U (x : X) x.2).hom y ∈
        IsLocalRing.maximalIdeal ↑(X.presheaf.stalk (x : X)) := hle (Ideal.mem_map_of_mem _ hy)
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (X.presheaf.stalk (x : X)) (hU.primeIdealOf x).asIdeal y).mp h2
  · intro hle
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (X.presheaf.stalk (x : X)) (hU.primeIdealOf x).asIdeal y).mpr (hle hy)


end

section
variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

private theorem exists_point_primeIdealOf_eq_consolidated177 (q : PrimeSpectrum Γ(X, U)) : ∃ x : U, hU.primeIdealOf x = q := by
  have hmem : hU.fromSpec.base q ∈ U := by
    have h1 : hU.fromSpec.base q ∈ Set.range hU.fromSpec.base := ⟨q, rfl⟩
    rw [hU.range_fromSpec] at h1
    exact h1
  refine ⟨⟨hU.fromSpec.base q, hmem⟩, ?_⟩
  have hinj : Function.Injective hU.fromSpec.base := hU.fromSpec.isOpenEmbedding.injective
  apply hinj
  exact hU.fromSpec_primeIdealOf ⟨hU.fromSpec.base q, hmem⟩

private theorem notMem_primeIdealOf_of_mem_basicOpen_consolidated177 (g : Γ(X, U)) (x : U) (hxg : (x : X) ∈ X.basicOpen g) :
    g ∉ (hU.primeIdealOf x).asIdeal := by
  have := hU.isLocalization_stalk x
  have hunit : IsUnit ((X.presheaf.germ U (x : X) x.2).hom g) :=
    (X.mem_basicOpen g (x : X) x.2).mp hxg
  intro hmem
  have h2 := (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (X.presheaf.stalk (x : X)) (hU.primeIdealOf x).asIdeal g).mpr hmem
  exact (IsLocalRing.mem_maximalIdeal _).mp h2 hunit

private theorem ideal_le_of_support_subset_consolidated177 (Z J : X.IdealSheafData) (hrad : (Z.ideal ⟨U, hU⟩).IsRadical)
    (hsupp : ∀ x : X, x ∈ Z.support → x ∈ U → x ∈ J.support) :
    J.ideal ⟨U, hU⟩ ≤ Z.ideal ⟨U, hU⟩ := by
  have hrad' : (Z.ideal ⟨U, hU⟩).radical = Z.ideal ⟨U, hU⟩ := hrad.radical
  rw [← hrad', Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro q ⟨hq1, hq2⟩
  obtain ⟨x, hxq⟩ := exists_point_primeIdealOf_eq_consolidated177 hU ⟨q, hq2⟩
  have hxq' : (hU.primeIdealOf x).asIdeal = q := congrArg PrimeSpectrum.asIdeal hxq
  have hxZ : (x : X) ∈ Z.support := by
    refine (mem_support_iff_ideal_le_primeIdealOf_of_isAffineOpen_consolidated177 Z hU x).mpr ?_
    rw [hxq']
    exact hq1
  have hxJ := hsupp (x : X) hxZ x.2
  have hfin := (mem_support_iff_ideal_le_primeIdealOf_of_isAffineOpen_consolidated177 J hU x).mp hxJ
  rw [hxq'] at hfin
  exact hfin


end

section
variable {X : Scheme.{u}}

private theorem ideal_eq_top_of_disjoint_support_consolidated177 (Z : X.IdealSheafData)
    (W : X.affineOpens) (hW : ∀ y : X, y ∈ W.1 → y ∉ Z.support) : Z.ideal W = ⊤ := by
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have : P.IsPrime := hP.isPrime
  obtain ⟨x, hxq⟩ := exists_point_primeIdealOf_eq_consolidated177 W.2 ⟨P, hP.isPrime⟩
  have hxq' : (W.2.primeIdealOf x).asIdeal = P := congrArg PrimeSpectrum.asIdeal hxq
  refine hW (x : X) x.2 ?_
  refine (mem_support_iff_ideal_le_primeIdealOf_of_isAffineOpen_consolidated177 Z W.2 x).mpr ?_
  rw [hxq']
  exact hle

private theorem le_pow_of_forall_le_pow_basicOpen_consolidated177 (Z I : X.IdealSheafData) (m : ℕ)
    (hloc : ∀ (V : X.affineOpens) (x : X), x ∈ V.1 →
      ∃ g : Γ(X, V.1), x ∈ X.basicOpen g ∧
        I.ideal (X.affineBasicOpen g) ≤ Z.ideal (X.affineBasicOpen g) ^ m) :
    I ≤ Z ^ m := by
  have key : ∀ V : X.affineOpens, I.ideal V ≤ (Z ^ m).ideal V := by
    intro V
    rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
    intro a ha
    by_contra hcon
    have hcol : ((Z.ideal V) ^ m).colon (Ideal.span {a}) ≠ ⊤ := by
      intro htop
      have h1 : (1 : Γ(X, V.1)) ∈ ((Z.ideal V) ^ m).colon (Ideal.span {a}) := by
        rw [htop]; exact Submodule.mem_top
      have h2 := Submodule.mem_colon.mp h1 a (Ideal.mem_span_singleton_self a)
      rw [smul_eq_mul, one_mul] at h2
      exact hcon h2
    obtain ⟨P, hP, hPle⟩ := Ideal.exists_le_maximal _ hcol
    have : P.IsPrime := hP.isPrime
    obtain ⟨x, hxq⟩ := exists_point_primeIdealOf_eq_consolidated177 V.2 ⟨P, hP.isPrime⟩
    have hxq' : (V.2.primeIdealOf x).asIdeal = P := congrArg PrimeSpectrum.asIdeal hxq
    obtain ⟨g, hxg, hgle⟩ := hloc V (x : X) x.2
    have hgP : g ∉ P := by
      have hg := notMem_primeIdealOf_of_mem_basicOpen_consolidated177 V.2 g x hxg
      rw [hxq'] at hg
      exact hg
    let _ : Algebra Γ(X, V.1) Γ(X, X.basicOpen g) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
    have : IsLocalization.Away g Γ(X, X.basicOpen g) := V.2.isLocalization_basicOpen g
    have hI : Ideal.map (algebraMap Γ(X, V.1) Γ(X, X.basicOpen g)) (I.ideal V) =
        I.ideal (X.affineBasicOpen g) := I.map_ideal_basicOpen V g
    have hZ : Ideal.map (algebraMap Γ(X, V.1) Γ(X, X.basicOpen g)) (Z.ideal V) =
        Z.ideal (X.affineBasicOpen g) := Z.map_ideal_basicOpen V g
    have hmem : (algebraMap Γ(X, V.1) Γ(X, X.basicOpen g)) a ∈
        Ideal.map (algebraMap Γ(X, V.1) Γ(X, X.basicOpen g)) ((Z.ideal V) ^ m) := by
      rw [Ideal.map_pow, hZ]
      exact hgle (hI ▸ Ideal.mem_map_of_mem _ ha)
    rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g)] at hmem
    obtain ⟨⟨bb, sm⟩, heq⟩ := hmem
    rw [← map_mul] at heq
    obtain ⟨tm, hct⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers g)
      Γ(X, X.basicOpen g)).mp heq
    have hmemB : ((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) * a ∈ (Z.ideal V) ^ m := by
      have h3 : ((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) * a
          = (tm : Γ(X, V.1)) * (a * (sm : Γ(X, V.1))) := by ring
      rw [h3, hct]
      exact Ideal.mul_mem_left _ _ bb.2
    have hcolmem : ((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) ∈
        ((Z.ideal V) ^ m).colon (Ideal.span {a}) := by
      refine Submodule.mem_colon.mpr ?_
      intro q hq
      obtain ⟨cc, rfl⟩ := Ideal.mem_span_singleton'.mp hq
      have h4 : ((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) • (cc * a)
          = cc * (((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) * a) := by
        rw [smul_eq_mul]; ring
      rw [h4]
      exact Ideal.mul_mem_left _ _ hmemB
    obtain ⟨i, hi⟩ := tm.2
    obtain ⟨j, hj⟩ := sm.2
    have hts : (tm : Γ(X, V.1)) * (sm : Γ(X, V.1)) = g ^ (i + j) := by
      rw [← hi, ← hj, pow_add]
    have hmemP : g ^ (i + j) ∈ P := hts ▸ hPle hcolmem
    exact hgP (hP.isPrime.mem_of_pow_mem _ hmemP)
  exact key


end

private theorem isUnit_natCast_of_algebra_of_charZero_consolidated177 (k : Type*) [Field k] [CharZero k]
    (R : Type*) [CommRing R] [Algebra k R] {r : ℕ} (hr : 1 ≤ r) : IsUnit ((r : ℕ) : R) := by
  have h0 : ((r : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : ((r : ℕ) : R) = algebraMap k R ((r : ℕ) : k) := (map_natCast (algebraMap k R) r).symm
  rw [h1]
  exact IsUnit.map (algebraMap k R) (IsUnit.mk0 ((r : ℕ) : k) h0)

theorem isRadical_ideal_of_restrictIdeal_eq_coordIdeal {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (c : EtaleChart p U n) (Z : X.IdealSheafData) (S : Finset (Fin n))
    (h : restrictIdeal Z U = c.coordIdeal S) :
    (Z.ideal ⟨U, hU⟩).IsRadical := by
  classical
  have hmap : Ideal.map c.coordRingHom (mvPolynomialCoordIdeal k n S) = Z.ideal ⟨U, hU⟩ :=
    c.map_mvPolynomialCoordIdeal_eq_ideal hU Z S h
  have hg := etale_quotientMk_comp_renameCompl k n S c.coordRingHom (c.coordRingHom_etale hU)
    (Z.ideal ⟨U, hU⟩) hmap.symm
  let _ : Algebra (CoordPolynomialRing k (n - S.card)) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) :=
    RingHom.toAlgebra
      (((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)).comp c.coordRingHom).comp (renameCompl k n S).toRingHom)
  have : Algebra.Etale (CoordPolynomialRing k (n - S.card)) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) := hg
  have hred : IsReduced (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) := by
    refine isReduced_ofLocalizationMaximal _ ?_
    intro q hq
    have : q.IsPrime := hq.isPrime
    have := isRegularLocalRing_localization_atPrime_etale k (n - S.card)
      (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) q
    have : IsDomain (Localization.AtPrime q) := inferInstance
    exact ⟨fun x hx => hx.eq_zero⟩
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr hred

section
variable {X : Scheme.{u}} {k : Type u} [Field k] [CharZero k] (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]

theorem ideal_le_pow_of_restrictIdeal_eq_coordIdeal {U : X.Opens}
    (hU : IsAffineOpen U) {n : ℕ} (c : EtaleChart p U n) (Z : X.IdealSheafData)
    (S : Finset (Fin n)) (h : restrictIdeal Z U = c.coordIdeal S) (m : ℕ)
    (I : X.IdealSheafData)
    (hord : ∀ x : X, x ∈ Z.support → x ∈ U → x ∈ orderAtLeastLocus I m) :
    I.ideal ⟨U, hU⟩ ≤ Z.ideal ⟨U, hU⟩ ^ m := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    rw [pow_zero, Ideal.one_eq_top]
    exact le_top
  let algR : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let algP : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := c.algebra
  have htower : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := c.isScalarTower
  have hfet : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) :=
    c.algebra_formallyEtale hU
  let xs : {i : Fin n // i ∈ S} → Γ(X, U) := fun i => c.coord i.1
  let Ds : {i : Fin n // i ∈ S} → Derivation k Γ(X, U) Γ(X, U) :=
    fun i => EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, U) (ULift.up i.1)
  have hD : ∀ i j : {i : Fin n // i ∈ S}, Ds i (xs j) = if i = j then 1 else 0 := by
    intro i j
    show (EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, U) (ULift.up i.1))
        (c.coord j.1) = if i = j then 1 else 0
    rw [← c.etaleCoordinates_coord j.1, EtaleCoordinates.partialDeriv_coord]
    have hiff : (ULift.up.{u} i.1 = ULift.up.{u} j.1) ↔ i = j := by
      constructor
      · intro hh
        exact Subtype.ext (congrArg ULift.down hh)
      · intro hh
        rw [hh]
    by_cases hij : i = j
    · rw [if_pos (hiff.mpr hij), if_pos hij]
    · rw [if_neg (fun hh => hij (hiff.mp hh)), if_neg hij]
  have hrange : Set.range xs = c.coord '' (S : Set (Fin n)) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hspan : Ideal.span (Set.range xs) = Z.ideal ⟨U, hU⟩ := by
    rw [hrange, c.ideal_eq_span_coord hU Z S h]
  have hunit : ∀ r : ℕ, 1 ≤ r → IsUnit ((r : ℕ) : Γ(X, U)) := by
    intro r hr
    exact isUnit_natCast_of_algebra_of_charZero_consolidated177 k Γ(X, U) hr
  have hbase : derivIdealIterate k (m - 1) (I.ideal ⟨U, hU⟩) ≤ Z.ideal ⟨U, hU⟩ := by
    have h1 : (derivIdealSheafIterate k p (m - 1) I).ideal ⟨U, hU⟩ ≤ Z.ideal ⟨U, hU⟩ := by
      refine ideal_le_of_support_subset_consolidated177 hU Z (derivIdealSheafIterate k p (m - 1) I)
        (isRadical_ideal_of_restrictIdeal_eq_coordIdeal p hU c Z S h) ?_
      intro y hy hyU
      have h2 : ((derivIdealSheafIterate k p (m - 1) I).support : Set X) = orderAtLeastLocus I m :=
        support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm
      have h3 : y ∈ orderAtLeastLocus I m := hord y hy hyU
      rw [← h2] at h3
      exact h3
    calc derivIdealIterate k (m - 1) (I.ideal ⟨U, hU⟩)
        = (derivIdealSheafIterate k p (m - 1) I).ideal ⟨U, hU⟩ :=
          (derivIdealSheafIterate_ideal k p (m - 1) I ⟨U, hU⟩).symm
      _ ≤ Z.ideal ⟨U, hU⟩ := h1
  have key : ∀ j : ℕ, 1 ≤ j → j ≤ m →
      derivIdealIterate k (m - j) (I.ideal ⟨U, hU⟩) ≤ Z.ideal ⟨U, hU⟩ ^ j := by
    intro j
    induction j with
    | zero => intro hj; exact absurd hj (by omega)
    | succ j ih =>
      intro _ hjm
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        simpa using hbase
      · intro f hf
        have hmem1 : f ∈ derivIdealIterate k (m - j) (I.ideal ⟨U, hU⟩) :=
          derivIdealIterate_le_of_le k (show m - (j + 1) ≤ m - j by omega) _ hf
        have hfW : f ∈ Z.ideal ⟨U, hU⟩ ^ j := ih hj0 (by omega) hmem1
        have hdf : ∀ i : {i : Fin n // i ∈ S}, (Ds i) f ∈ Z.ideal ⟨U, hU⟩ ^ j := by
          intro i
          refine ih hj0 (by omega) ?_
          have h4 : (Ds i) f ∈ derivIdeal k (derivIdealIterate k (m - (j + 1)) (I.ideal ⟨U, hU⟩)) :=
            derivation_apply_mem_derivIdeal k _ (Ds i) hf
          rw [← derivIdealIterate_succ] at h4
          exact derivIdealIterate_le_of_le k (show m - (j + 1) + 1 ≤ m - j by omega) _ h4
        have hf' : f ∈ Ideal.span (Set.range xs) ^ j := by rw [hspan]; exact hfW
        have hdf' : ∀ i : {i : Fin n // i ∈ S}, (Ds i) f ∈ Ideal.span (Set.range xs) ^ j := by
          intro i
          rw [hspan]
          exact hdf i
        have hres := mem_pow_succ_of_deriv_mem_pow k xs Ds hD (hunit j hj0) hf' hdf'
        rw [hspan] at hres
        exact hres
  have hfin := key m hm le_rfl
  rw [Nat.sub_self, derivIdealIterate_zero] at hfin
  exact hfin

theorem le_pow_of_support_subset_orderAtLeastLocus_of_coordIdeal (Z I : X.IdealSheafData)
    (m : ℕ)
    (hchart : ∀ x : X, x ∈ Z.support →
      ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n) (S : Finset (Fin n)),
        restrictIdeal Z U = c.coordIdeal S)
    (hord : (Z.support : Set X) ⊆ orderAtLeastLocus I m) :
    I ≤ Z ^ m := by
  refine le_pow_of_forall_le_pow_basicOpen_consolidated177 Z I m ?_
  intro V x hx
  by_cases hxZ : x ∈ Z.support
  · obtain ⟨U, hxU, n, c, S, hS⟩ := hchart x hxZ
    obtain ⟨g, hgU, hxg⟩ := V.2.exists_basicOpen_le (⟨x, hxU⟩ : U) hx
    refine ⟨g, hxg, ?_⟩
    have hWaff : IsAffineOpen (X.basicOpen g) := V.2.basicOpen g
    have hchart' : restrictIdeal Z (X.basicOpen g) = (c.restrict hgU).coordIdeal S :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hgU c Z S hS
    exact ideal_le_pow_of_restrictIdeal_eq_coordIdeal p hWaff (c.restrict hgU) Z S hchart' m I
      (fun y hy _ => hord hy)
  · have hΩopen : IsOpen ((Z.support : Set X)ᶜ) := Z.support.2.isOpen_compl
    have hxΩ : x ∈ (⟨(Z.support : Set X)ᶜ, hΩopen⟩ : X.Opens) := hxZ
    obtain ⟨g, hgΩ, hxg⟩ :=
      V.2.exists_basicOpen_le (⟨x, hxΩ⟩ : (⟨(Z.support : Set X)ᶜ, hΩopen⟩ : X.Opens)) hx
    refine ⟨g, hxg, ?_⟩
    have htop : Z.ideal (X.affineBasicOpen g) = ⊤ := by
      refine ideal_eq_top_of_disjoint_support_consolidated177 Z (X.affineBasicOpen g) ?_
      intro y hy
      have hy' : y ∈ X.basicOpen g := hy
      exact hgΩ hy'
    rw [htop, ← Ideal.one_eq_top, one_pow, Ideal.one_eq_top]
    exact le_top

theorem le_pow_of_hasStrictNormalCrossingsWith (Z I : X.IdealSheafData)
    (E : List X.IdealSheafData) (hE : HasStrictNormalCrossingsWith p Z E) (m : ℕ)
    (hord : (Z.support : Set X) ⊆ orderAtLeastLocus I m) :
    I ≤ Z ^ m := by
  refine le_pow_of_support_subset_orderAtLeastLocus_of_coordIdeal p Z I m ?_ hord
  unfold HasStrictNormalCrossingsWith at hE
  intro x hx
  obtain ⟨U, hxU, n, c, _, S, _, _, _, hZ⟩ := hE x hx
  exact ⟨U, hxU, n, c, S, hZ⟩


end

end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafFieldBaseChange
section

open CategoryTheory.Limits TopologicalSpace

section

section
variable {X : Scheme.{u}}

private theorem span_eq_top_of_isAffineOpen_of_forall_mem_basicOpen_consolidated199 {U : X.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(X, U)) (hcov : ∀ x ∈ U, ∃ g ∈ s, x ∈ X.basicOpen g) :
    Ideal.span s = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmp : m.IsPrime := hm.isPrime
  have hx : hU.fromSpec.base (⟨m, hmp⟩ : PrimeSpectrum Γ(X, U)) ∈ U := by
    have hr : hU.fromSpec.base (⟨m, hmp⟩ : PrimeSpectrum Γ(X, U))
        ∈ Set.range hU.fromSpec.base := ⟨_, rfl⟩
    rw [hU.range_fromSpec] at hr
    exact hr
  obtain ⟨g, hgs, hg⟩ := hcov _ hx
  have hmem : (⟨m, hmp⟩ : PrimeSpectrum Γ(X, U)) ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := hg
  rw [hU.fromSpec_preimage_basicOpen] at hmem
  have hnot : g ∉ m := hmem
  exact hnot (hle (Ideal.subset_span hgs))

private theorem ideal_eq_of_le_consolidated199 (I J : X.IdealSheafData)
    (V W : X.affineOpens) (h : (W : X.Opens) ≤ (V : X.Opens)) (hIJ : I.ideal V = J.ideal V) :
    I.ideal W = J.ideal W := by
  have e : (W : X.Opens) ≤ (𝟙 X) ⁻¹ᵁ (V : X.Opens) := by simpa using h
  have h1 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE I (𝟙 X) V W e
  have h2 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE J (𝟙 X) V W e
  rw [Scheme.IdealSheafData.comap_id] at h1 h2
  rw [h1, h2, hIJ]

private theorem exists_pow_mul_mem_of_map_mem_consolidated199 (U : X.affineOpens)
    (g : Γ(X, U.1)) (Jid : Ideal Γ(X, U.1)) (s : Γ(X, U.1))
    (hs : (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom s ∈
        Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom Jid) :
    ∃ n : ℕ, g ^ n * s ∈ Jid := by
  let algUV : Algebra Γ(X, U.1) Γ(X, X.basicOpen g) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
  have hloc : IsLocalization.Away g Γ(X, X.basicOpen g) := U.2.isLocalization_basicOpen g
  have hmem : algebraMap Γ(X, U.1) Γ(X, X.basicOpen g) s ∈
      Ideal.map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen g)) Jid := hs
  obtain ⟨⟨⟨y, hy⟩, mm⟩, hEq⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (M := Submonoid.powers g)
      (S := Γ(X, X.basicOpen g))).mp hmem
  have hEq' : algebraMap Γ(X, U.1) Γ(X, X.basicOpen g) (s * (mm : Γ(X, U.1)))
      = algebraMap Γ(X, U.1) Γ(X, X.basicOpen g) y := by
    rw [map_mul]
    exact hEq
  obtain ⟨cc, hcc⟩ :=
    (IsLocalization.eq_iff_exists (Submonoid.powers g) Γ(X, X.basicOpen g)).mp hEq'
  obtain ⟨n₁, hn₁⟩ := (Submonoid.mem_powers_iff (cc : Γ(X, U.1)) g).mp cc.2
  obtain ⟨n₂, hn₂⟩ := (Submonoid.mem_powers_iff (mm : Γ(X, U.1)) g).mp mm.2
  refine ⟨n₁ + n₂, ?_⟩
  have hrw : g ^ (n₁ + n₂) * s = (cc : Γ(X, U.1)) * (s * (mm : Γ(X, U.1))) := by
    rw [pow_add, hn₁, hn₂]; ring
  rw [hrw, hcc]
  exact Ideal.mul_mem_left _ _ hy


end

section
variable {X : Scheme.{u}} (I J : X.IdealSheafData) (h : ∀ x : ↥X, ∃ V : X.affineOpens, x ∈ (V : X.Opens) ∧ I.ideal V = J.ideal V)
include h

private theorem ideal_le_of_locally_eq_consolidated199 (U : X.affineOpens) : I.ideal U ≤ J.ideal U := by
  intro s hs
  have hspan : Ideal.span {g : Γ(X, U.1) | ∃ n : ℕ, g ^ n * s ∈ J.ideal U} = ⊤ := by
    refine span_eq_top_of_isAffineOpen_of_forall_mem_basicOpen_consolidated199 U.2 _ ?_
    intro x hx
    obtain ⟨V, hxV, hIJ⟩ := h x
    obtain ⟨g, hgV, hxg⟩ := U.2.exists_basicOpen_le (⟨x, hxV⟩ : ↥(V : X.Opens)) hx
    have hIJW : I.ideal (X.affineBasicOpen g) = J.ideal (X.affineBasicOpen g) :=
      ideal_eq_of_le_consolidated199 I J V (X.affineBasicOpen g) hgV hIJ
    have hres : (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom s ∈
        Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (J.ideal U) := by
      rw [J.map_ideal_basicOpen U g, ← hIJW, ← I.map_ideal_basicOpen U g]
      exact Ideal.mem_map_of_mem _ hs
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_of_map_mem_consolidated199 U g (J.ideal U) s hres
    exact ⟨g, ⟨n, hn⟩, hxg⟩
  obtain ⟨K, hK⟩ : ∃ K : Ideal Γ(X, U.1), ∀ a : Γ(X, U.1), a ∈ K ↔ a * s ∈ J.ideal U := by
    refine ⟨Submodule.comap (LinearMap.toSpanSingleton Γ(X, U.1) Γ(X, U.1) s) (J.ideal U),
      fun a => ?_⟩
    simp [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, smul_eq_mul]
  have hsub : Ideal.span {g : Γ(X, U.1) | ∃ n : ℕ, g ^ n * s ∈ J.ideal U} ≤ K.radical := by
    refine Ideal.span_le.mpr ?_
    rintro g ⟨n, hn⟩
    exact Ideal.mem_radical_iff.mpr ⟨n, (hK _).mpr hn⟩
  have htop : K.radical = ⊤ := by
    rw [eq_top_iff, ← hspan]
    exact hsub
  have h1 : (1 : Γ(X, U.1)) ∈ K.radical := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp h1
  have hone : (1 : Γ(X, U.1)) ∈ K := by simpa using hn
  simpa using (hK 1).mp hone

private theorem idealSheafData_eq_of_locally_eq_consolidated199 : I = J := by
  have h1 : ∀ U : X.affineOpens, I.ideal U ≤ J.ideal U := fun U =>
    ideal_le_of_locally_eq_consolidated199 I J h U
  have h2 : ∀ U : X.affineOpens, J.ideal U ≤ I.ideal U := by
    refine fun U => ideal_le_of_locally_eq_consolidated199 J I (fun x => ?_) U
    obtain ⟨V, hV, hIJ⟩ := h x
    exact ⟨V, hV, hIJ.symm⟩
  exact le_antisymm h1 h2


end

private theorem sectionsAlgebraMap_comp_specMap_consolidated199 (k L : Type u) [Field k] [Field L]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of L))
    (φ : CommRingCat.of k ⟶ CommRingCat.of L) (W : Y.Opens) :
    sectionsAlgebraMap k (q ≫ Spec.map φ) W = (sectionsAlgebraMap L q W).comp φ.hom := by
  have h1 : (q ≫ Spec.map φ).appLE ⊤ W (le_preimage_top k (q ≫ Spec.map φ) W)
      = ((Spec.map φ).appTop ≫ q.appTop) ≫
          Y.presheaf.map (homOfLE (le_preimage_top L q W)).op := rfl
  have h2 : (Spec.map φ).appTop ≫ q.appLE ⊤ W (le_preimage_top L q W)
      = ((Spec.map φ).appTop ≫ q.appTop) ≫
          Y.presheaf.map (homOfLE (le_preimage_top L q W)).op :=
    (Category.assoc _ _ _).symm
  have happ : (q ≫ Spec.map φ).appLE ⊤ W (le_preimage_top k (q ≫ Spec.map φ) W)
      = (Spec.map φ).appTop ≫ q.appLE ⊤ W (le_preimage_top L q W) := h1.trans h2.symm
  have key : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (q ≫ Spec.map φ).appLE ⊤ W (le_preimage_top k (q ≫ Spec.map φ) W)
      = φ ≫ ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫
          q.appLE ⊤ W (le_preimage_top L q W)) := by
    rw [happ, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality φ, Category.assoc]
  ext a
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom key) a

private theorem exists_affineOpen_derivIdealSheaf_comap_eq_consolidated199 {k L : Type u} [Field k] [Field L]
    {X Y : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} [Smooth p]
    {q : Y ⟶ Spec (CommRingCat.of L)} [Smooth q] {f : Y ⟶ X}
    {φ : CommRingCat.of k ⟶ CommRingCat.of L} (hsq : IsPullback q f (Spec.map φ) p)
    (I : X.IdealSheafData) (y : ↥Y) :
    ∃ V : Y.affineOpens, y ∈ (V : Y.Opens) ∧
      (derivIdealSheaf L q (I.comap f)).ideal V
        = ((derivIdealSheaf k p I).comap f).ideal V := by
  obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p (f.base y)
  obtain ⟨V, hVU, c', hVaff, hyV, hcoord⟩ :=
    exists_etaleChart_of_isPullback hsq c y hxU
  refine ⟨⟨V, hVaff⟩, hyV, ?_⟩
  have hdec : DecidableEq (ULift.{u} (Fin m)) := Classical.decEq _
  let instkL : Algebra k L := φ.hom.toAlgebra
  let instA : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let instPA : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra
  let instB : Algebra L Γ(Y, V) := sectionsAlgebra L q V
  let instPB : Algebra (MvPolynomial (ULift.{u} (Fin m)) L) Γ(Y, V) := c'.algebra
  let instAlgebra : Algebra k Γ(Y, V) := ((sectionsAlgebraMap L q V).comp φ.hom).toAlgebra
  have tA : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.isScalarTower
  have tB : IsScalarTower L (MvPolynomial (ULift.{u} (Fin m)) L) Γ(Y, V) := c'.isScalarTower
  have feA : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) :=
    c.algebra_formallyEtale hU
  have feB : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) L) Γ(Y, V) :=
    c'.algebra_formallyEtale hVaff
  have tkL : IsScalarTower k L Γ(Y, V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcommutes : ∀ a : k, (f.appLE U V hVU).hom (algebraMap k Γ(X, U) a)
      = algebraMap k Γ(Y, V) a := by
    intro a
    show (f.appLE U V hVU).hom (sectionsAlgebraMap k p U a)
      = sectionsAlgebraMap L q V (φ.hom a)
    rw [sectionsAlgebraMap_appLE_apply k p f U V hVU a, ← hsq.w,
      sectionsAlgebraMap_comp_specMap_consolidated199 k L q φ V]
    rfl
  let ψ : Γ(X, U) →ₐ[k] Γ(Y, V) := AlgHom.mk (f.appLE U V hVU).hom hcommutes
  have hψ : ∀ i : ULift.{u} (Fin m),
      ψ (EtaleCoordinates.coord k (ULift.{u} (Fin m)) Γ(X, U) i)
        = EtaleCoordinates.coord L (ULift.{u} (Fin m)) Γ(Y, V) i := by
    rintro ⟨j⟩
    have h1 : EtaleCoordinates.coord k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j) = c.coord j :=
      c.etaleCoordinates_coord j
    have h2 : EtaleCoordinates.coord L (ULift.{u} (Fin m)) Γ(Y, V) (ULift.up j) = c'.coord j :=
      c'.etaleCoordinates_coord j
    rw [h1, h2]
    show (f.appLE U V hVU).hom (c.coord j) = c'.coord j
    exact (hcoord j).symm
  have key := DerivIdealBaseChange.map_derivIdeal k L (ULift.{u} (Fin m)) Γ(X, U) Γ(Y, V) ψ hψ
      (I.ideal ⟨U, hU⟩)
  have hcomapV : (I.comap f).ideal ⟨V, hVaff⟩
      = Ideal.map (f.appLE U V hVU).hom (I.ideal ⟨U, hU⟩) :=
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE I f ⟨U, hU⟩ ⟨V, hVaff⟩ hVU
  have hcomapD : ((derivIdealSheaf k p I).comap f).ideal ⟨V, hVaff⟩
      = Ideal.map (f.appLE U V hVU).hom ((derivIdealSheaf k p I).ideal ⟨U, hU⟩) :=
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE (derivIdealSheaf k p I) f ⟨U, hU⟩
      ⟨V, hVaff⟩ hVU
  rw [derivIdealSheaf_ideal, hcomapV, hcomapD, derivIdealSheaf_ideal]
  exact key.symm

section
variable {k L : Type u} [Field k] [Field L] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (φ : CommRingCat.of k ⟶ CommRingCat.of L)

theorem derivIdealSheaf_comap_fieldBaseChange (I : X.IdealSheafData) :
    derivIdealSheaf L (pullback.snd p (Spec.map φ))
        (I.comap (pullback.fst p (Spec.map φ))) =
      (derivIdealSheaf k p I).comap (pullback.fst p (Spec.map φ)) :=
  idealSheafData_eq_of_locally_eq_consolidated199 _ _ fun y =>
    exists_affineOpen_derivIdealSheaf_comap_eq_consolidated199 (isPullback_pullback_specMap p φ) I y

theorem derivIdealSheafIterate_comap_fieldBaseChange (r : ℕ) (I : X.IdealSheafData) :
    derivIdealSheafIterate L (pullback.snd p (Spec.map φ)) r
        (I.comap (pullback.fst p (Spec.map φ))) =
      (derivIdealSheafIterate k p r I).comap (pullback.fst p (Spec.map φ)) := by
  induction r with
  | zero => rfl
  | succ n ih =>
      rw [derivIdealSheafIterate_succ, derivIdealSheafIterate_succ, ih,
        derivIdealSheaf_comap_fieldBaseChange p φ (derivIdealSheafIterate k p n I)]

theorem maxContactIdeal_comap_fieldBaseChange (m : ℕ) (I : X.IdealSheafData) :
    maxContactIdeal L (pullback.snd p (Spec.map φ))
        (I.comap (pullback.fst p (Spec.map φ))) m =
      (maxContactIdeal k p I m).comap (pullback.fst p (Spec.map φ)) := by
  rw [maxContactIdeal_eq_derivIdealSheafIterate, maxContactIdeal_eq_derivIdealSheafIterate, derivIdealSheafIterate_comap_fieldBaseChange]


end

section
variable {k L : Type u} [Field k] [Field L] [CharZero k] [CharZero L] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (φ : CommRingCat.of k ⟶ CommRingCat.of L) (I : X.IdealSheafData)

theorem orderAtLeastLocus_comap_fieldBaseChange (m : ℕ) :
    orderAtLeastLocus (I.comap (pullback.fst p (Spec.map φ))) m =
      (pullback.fst p (Spec.map φ)).base ⁻¹' orderAtLeastLocus I m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [orderAtLeastLocus_zero, orderAtLeastLocus_zero, Set.preimage_univ]
  · rw [← support_derivIdealSheafIterate_eq_orderAtLeastLocus L (pullback.snd p (Spec.map φ))
        (I.comap (pullback.fst p (Spec.map φ))) hm,
      ← support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm,
      derivIdealSheafIterate_comap_fieldBaseChange p φ (m - 1) I]
    ext y
    simp

theorem orderAt_comap_fieldBaseChange (y : ↥(pullback p (Spec.map φ))) :
    orderAt (I.comap (pullback.fst p (Spec.map φ))) y =
      orderAt I ((pullback.fst p (Spec.map φ)).base y) := by
  refine ENat.eq_of_forall_natCast_le_iff ?_
  intro n
  have h := orderAtLeastLocus_comap_fieldBaseChange p φ I n
  have hy := Set.ext_iff.mp h y
  simpa [mem_orderAtLeastLocus_iff, Set.mem_preimage] using hy


end

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
section

open Opposite TopologicalSpace

section

private theorem span_eq_top_of_forall_mem_basicOpen_consolidated221 {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(X, U))
    (hcov : ∀ x : X, x ∈ U → ∃ t ∈ s, x ∈ X.basicOpen t) :
    Ideal.span s = ⊤ := by
  have hUeq : (⨆ f : s, X.basicOpen (f : Γ(X, U))) = U := by
    refine le_antisymm (iSup_le fun f => Scheme.basicOpen_le (X := X) (f : Γ(X, U)))
      (SetLike.le_def.mpr ?_)
    intro x hx
    obtain ⟨t, hts, hxt⟩ := hcov x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨t, hts⟩, hxt⟩
  exact (IsAffineOpen.iSup_basicOpen_eq_self_iff hU).mp hUeq

section
variable {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (M : Submonoid R) (hlocal : @IsLocalization R _ M S _ g.toAlgebra)
include hlocal

private theorem exists_mul_mem_of_map_mem_map_consolidated221 (b : Ideal R) (f : R) (hf : g f ∈ Ideal.map g b) :
    ∃ t ∈ M, t * f ∈ b := by
  let _ : Algebra R S := g.toAlgebra
  have : IsLocalization M S := hlocal
  have hf' : algebraMap R S f ∈ Ideal.map (algebraMap R S) b := hf
  obtain ⟨⟨y, m⟩, he⟩ := (IsLocalization.mem_map_algebraMap_iff (M := M) (S := S)).mp hf'
  rw [← map_mul] at he
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (M := M) (S := S)).mp he
  refine ⟨(c : R) * (m : R), M.mul_mem c.2 m.2, ?_⟩
  have h3 : (c : R) * (m : R) * f = (c : R) * (y : R) := by rw [← hc]; ring
  rw [h3]
  exact b.mul_mem_left _ y.2

private theorem isUnit_map_of_mem_of_isLocalization_consolidated221 (t : R) (ht : t ∈ M) : IsUnit (g t) := by
  let _ : Algebra R S := g.toAlgebra
  have : IsLocalization M S := hlocal
  have h1 : IsUnit (algebraMap R S t) := IsLocalization.map_units S (⟨t, ht⟩ : M)
  exact h1


end

private theorem mem_of_span_mul_mem_eq_top_consolidated221 {R : Type*} [CommRing R] (b : Ideal R)
    (f : R) (h : Ideal.span {t : R | t * f ∈ b} = ⊤) : f ∈ b := by
  have hC : ∀ g ∈ Ideal.span {t : R | t * f ∈ b}, g * f ∈ b := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => simp
    | add x y hx hy ihx ihy => simpa [add_mul] using b.add_mem ihx ihy
    | smul a x hx ih => simpa [smul_eq_mul, mul_assoc] using b.mul_mem_left a ih
  have h1 : (1 : R) ∈ Ideal.span {t : R | t * f ∈ b} := by
    rw [h]; exact Submodule.mem_top
  simpa using hC 1 h1

section
variable {X : Scheme.{u}}

theorem le_iff_forall_stalkIdeal_le (I J : X.IdealSheafData) :
    I ≤ J ↔ ∀ x : X, stalkIdeal I x ≤ stalkIdeal J x := by
  refine ⟨fun h x => stalkIdeal_mono h x, fun h => ?_⟩
  rw [Scheme.IdealSheafData.le_def]
  intro U f hf
  have hU : IsAffineOpen U.1 := U.2
  have hlocal : ∀ (x : X) (hx : x ∈ U.1),
      @IsLocalization ↥Γ(X, U.1) _
        (IsAffineOpen.primeIdealOf hU ⟨x, hx⟩).asIdeal.primeCompl
        ↥(X.presheaf.stalk x) _ ((X.presheaf.germ U.1 x hx).hom.toAlgebra) := by
    intro x hx
    exact IsAffineOpen.isLocalization_stalk hU ⟨x, hx⟩
  have hbasic : ∀ (x : X) (hx : x ∈ U.1) (t : Γ(X, U.1)),
      IsUnit ((X.presheaf.germ U.1 x hx).hom t) → x ∈ X.basicOpen t := by
    intro x hx t ht
    exact (Scheme.mem_basicOpen X t x hx).mpr ht
  have key : ∀ (x : X) (hx : x ∈ U.1),
      ∃ t : Γ(X, U.1), t * f ∈ J.ideal U ∧ x ∈ X.basicOpen t := by
    intro x hx
    have hmemI : (X.presheaf.germ U.1 x hx).hom f ∈ stalkIdeal I x := by
      rw [stalkIdeal_eq_map_germ I x U hx]
      exact Ideal.mem_map_of_mem _ hf
    have hmem : (X.presheaf.germ U.1 x hx).hom f ∈
        Ideal.map (X.presheaf.germ U.1 x hx).hom (J.ideal U) := by
      have hh := h x hmemI
      rwa [stalkIdeal_eq_map_germ J x U hx] at hh
    obtain ⟨t, htM, htf⟩ := exists_mul_mem_of_map_mem_map_consolidated221 (X.presheaf.germ U.1 x hx).hom
      (IsAffineOpen.primeIdealOf hU ⟨x, hx⟩).asIdeal.primeCompl (hlocal x hx) (J.ideal U) f hmem
    exact ⟨t, htf, hbasic x hx t (isUnit_map_of_mem_of_isLocalization_consolidated221
      (X.presheaf.germ U.1 x hx).hom _ (hlocal x hx) t htM)⟩
  have hspan : Ideal.span {t : Γ(X, U.1) | t * f ∈ J.ideal U} = ⊤ := by
    refine span_eq_top_of_forall_mem_basicOpen_consolidated221 hU {t : Γ(X, U.1) | t * f ∈ J.ideal U}
      (fun x hx => ?_)
    obtain ⟨t, htf, hxt⟩ := key x hx
    exact ⟨t, htf, hxt⟩
  exact mem_of_span_mul_mem_eq_top_consolidated221 (J.ideal U) f hspan

theorem notMem_support_of_mem_opens_of_restrictIdeal_eq_top (Z : X.IdealSheafData)
    (U : X.Opens) (h : restrictIdeal Z U = ⊤) (x : X) (hx : x ∈ U) : x ∉ Z.support := by
  intro hxZ
  obtain ⟨y, hy⟩ : x ∈ Set.range (⇑U.ι) := by
    rw [Scheme.Opens.range_ι]
    exact hx
  have h' : Z.comap U.ι = ⊤ := h
  have h2 := Scheme.IdealSheafData.support_comap Z U.ι
  have h3 : (⇑U.ι) y ∈ Z.support := by
    rw [hy]
    exact hxZ
  have h4 : y ∈ (Z.comap U.ι).support := by
    rw [h2]
    exact h3
  rw [h', Scheme.IdealSheafData.support_top] at h4
  exact h4

theorem isClosed_of_maximal_irreducible_subset_support (D : X.IdealSheafData)
    {C : Set X} (hC : IsIrreducible C) (hCsub : C ⊆ (D.support : Set X))
    (hCmax : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (D.support : Set X) → C' = C) :
    IsClosed C := by
  have hsupp : IsClosed ((D.support : Set X)) := D.support.2
  have hsub : closure C ⊆ (D.support : Set X) := closure_minimal hCsub hsupp
  have heq : closure C = C := hCmax (closure C) hC.closure subset_closure hsub
  rw [← heq]
  exact isClosed_closure


end

variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))

section
variable {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ} (c : EtaleChart p V n) (j : Fin n) (D : X.IdealSheafData) (hD : restrictIdeal D V = c.coordIdeal {j}) (y : X) (hy : y ∈ V)
include hV hD

theorem stalkIdeal_eq_span_germ_coord :
    stalkIdeal D y =
      Ideal.span ({(X.presheaf.germ V y hy).hom (c.coord j)} : Set (X.presheaf.stalk y)) := by
  have h1 : stalkIdeal D y = Ideal.map (X.presheaf.germ V y hy).hom (D.ideal ⟨V, hV⟩) :=
    stalkIdeal_eq_map_germ D y ⟨V, hV⟩ hy
  have h2 : D.ideal ⟨V, hV⟩ = Ideal.span (c.coord '' (({j} : Finset (Fin n)) : Set (Fin n))) :=
    EtaleChart.ideal_eq_span_coord c hV D {j} hD
  rw [h1, h2, Ideal.map_span]
  simp

theorem coord_mem_primeIdealOf_of_mem_support (hys : y ∈ D.support) :
    c.coord j ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := by
  by_contra hcon
  let _ : Algebra (Γ(X, V)) (X.presheaf.stalk y) :=
    (X.presheaf.germ V y hy).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk y)
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal := hV.isLocalization_stalk ⟨y, hy⟩
  have hunit : IsUnit ((X.presheaf.germ V y hy).hom (c.coord j)) :=
    IsLocalization.map_units (S := X.presheaf.stalk y)
      (M := (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl) ⟨c.coord j, hcon⟩
  refine (mem_support_iff_stalkIdeal_ne_top D y).mp hys ?_
  rw [stalkIdeal_eq_span_germ_coord p hV c j D hD y hy]
  exact Ideal.span_singleton_eq_top.mpr hunit


end

section
variable {Y : Scheme.{u}} {W : Y.Opens} (hW : IsAffineOpen W)

private theorem isUnit_germ_iff_notMem_primeIdealOf_consolidated221 (y : Y) (hy : y ∈ W) (f : Γ(Y, W)) :
    IsUnit ((Y.presheaf.germ W y hy).hom f) ↔ f ∉ (hW.primeIdealOf ⟨y, hy⟩).asIdeal := by
  let _ : Algebra (Γ(Y, W)) (Y.presheaf.stalk y) := (Y.presheaf.germ W y hy).hom.toAlgebra
  have : IsLocalization.AtPrime (Y.presheaf.stalk y) (hW.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hW.isLocalization_stalk ⟨y, hy⟩
  constructor
  · intro hu hmem
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (↥(Y.presheaf.stalk y))
      (hW.primeIdealOf ⟨y, hy⟩).asIdeal f).mp hu hmem
  · intro hmem
    exact IsLocalization.map_units (S := Y.presheaf.stalk y)
      (M := (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl) ⟨f, hmem⟩

private theorem primeIdealOf_le_of_specializes_consolidated221 (a b : Y) (ha : a ∈ W) (hb : b ∈ W) (h : a ⤳ b) :
    (hW.primeIdealOf ⟨a, ha⟩).asIdeal ≤ (hW.primeIdealOf ⟨b, hb⟩).asIdeal := by
  intro f hf
  by_contra hcon
  have hb' : b ∈ Y.basicOpen f :=
    (Scheme.mem_basicOpen Y f b hb).mpr ((isUnit_germ_iff_notMem_primeIdealOf_consolidated221 hW b hb f).mpr hcon)
  have ha' : a ∈ Y.basicOpen f := h.mem_open (Y.basicOpen f).isOpen hb'
  exact ((isUnit_germ_iff_notMem_primeIdealOf_consolidated221 hW a ha f).mp
    ((Scheme.mem_basicOpen Y f a ha).mp ha')) hf


end

private theorem isPrime_span_germ_coord_consolidated221 {Y : Scheme.{u}} {K : Type u} [Field K]
    {pr : Y ⟶ Spec (CommRingCat.of K)} {W : Y.Opens} (hW : IsAffineOpen W) {n : ℕ}
    (c : EtaleChart pr W n) (j : Fin n) (y : Y) (hy : y ∈ W)
    (hcoord : c.coord j ∈ (hW.primeIdealOf ⟨y, hy⟩).asIdeal) :
    (Ideal.span ({(Y.presheaf.germ W y hy).hom (c.coord j)} :
      Set (Y.presheaf.stalk y))).IsPrime := by
  let instPoly : Algebra (MvPolynomial (ULift.{u} (Fin n)) K) (Γ(Y, W)) := c.algebra
  have instEt : Algebra.Etale (MvPolynomial (ULift.{u} (Fin n)) K) (Γ(Y, W)) :=
    c.algebra_etale hW
  let instAlg : Algebra (Γ(Y, W)) (Y.presheaf.stalk y) :=
    (Y.presheaf.germ W y hy).hom.toAlgebra
  have instPrime : ((hW.primeIdealOf ⟨y, hy⟩).asIdeal).IsPrime :=
    (hW.primeIdealOf ⟨y, hy⟩).isPrime
  have instLoc : IsLocalization.AtPrime (Y.presheaf.stalk y)
      (hW.primeIdealOf ⟨y, hy⟩).asIdeal := hW.isLocalization_stalk ⟨y, hy⟩
  have hcoordeq : etaleChartCoord K n (Γ(Y, W)) j = c.coord j := by
    rw [etaleChartCoord_def]
    exact EtaleChart.coordRingHom_X c j
  have h := isPrime_span_singleton_algebraMap_etaleChartCoord K n (Γ(Y, W))
    ((hW.primeIdealOf ⟨y, hy⟩).asIdeal) (Y.presheaf.stalk y) j
    (by rw [hcoordeq]; exact hcoord)
  rw [hcoordeq] at h
  exact h

section
variable {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ} (c : EtaleChart p V n) (j : Fin n) (D : X.IdealSheafData) (hD : restrictIdeal D V = c.coordIdeal {j}) (x η : X)
include hD

theorem primeIdealOf_eq_comap_span_germ_coord (hx : x ∈ V) (hη : η ∈ V)
    (hspec : η ⤳ x) (hηs : η ∈ D.support)
    (hmin : ∀ P : Ideal Γ(X, V), P.IsPrime → c.coord j ∈ P →
      P ≤ (hV.primeIdealOf ⟨η, hη⟩).asIdeal → P = (hV.primeIdealOf ⟨η, hη⟩).asIdeal) :
    (hV.primeIdealOf ⟨η, hη⟩).asIdeal =
      Ideal.comap (X.presheaf.germ V x hx).hom
        (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
          Set (X.presheaf.stalk x))) := by
  have hcoordq : c.coord j ∈ (hV.primeIdealOf ⟨η, hη⟩).asIdeal :=
    coord_mem_primeIdealOf_of_mem_support p hV c j D hD η hη hηs
  have hqle : (hV.primeIdealOf ⟨η, hη⟩).asIdeal ≤ (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    primeIdealOf_le_of_specializes_consolidated221 hV η x hη hx hspec
  have hsp : (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
      Set (X.presheaf.stalk x))).IsPrime :=
    isPrime_span_germ_coord_consolidated221 hV c j x hx (hqle hcoordq)
  have hPprime : (Ideal.comap (X.presheaf.germ V x hx).hom
      (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
        Set (X.presheaf.stalk x)))).IsPrime := inferInstance
  have htP : c.coord j ∈ Ideal.comap (X.presheaf.germ V x hx).hom
      (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
        Set (X.presheaf.stalk x))) := by
    rw [Ideal.mem_comap]
    exact Ideal.mem_span_singleton_self _
  have hmapspan : Ideal.map (X.presheaf.germ V x hx).hom
      (Ideal.span ({c.coord j} : Set Γ(X, V)))
      = Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
        Set (X.presheaf.stalk x)) := by
    rw [Ideal.map_span, Set.image_singleton]
  have hloc : @IsLocalization ↥Γ(X, V) _ (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      ↥(X.presheaf.stalk x) _ ((X.presheaf.germ V x hx).hom.toAlgebra) :=
    hV.isLocalization_stalk ⟨x, hx⟩
  have hPle : Ideal.comap (X.presheaf.germ V x hx).hom
      (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
        Set (X.presheaf.stalk x)))
      ≤ (hV.primeIdealOf ⟨η, hη⟩).asIdeal := by
    intro a ha
    rw [Ideal.mem_comap, ← hmapspan] at ha
    obtain ⟨s, hs, hsa⟩ := exists_mul_mem_of_map_mem_map_consolidated221 (X.presheaf.germ V x hx).hom
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl hloc
      (Ideal.span ({c.coord j} : Set Γ(X, V))) a ha
    have hs' : s ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := hs
    have hsq : s ∉ (hV.primeIdealOf ⟨η, hη⟩).asIdeal := fun hcon => hs' (hqle hcon)
    have hle : Ideal.span ({c.coord j} : Set Γ(X, V)) ≤ (hV.primeIdealOf ⟨η, hη⟩).asIdeal :=
      (Ideal.span_singleton_le_iff_mem _).mpr hcoordq
    exact ((hV.primeIdealOf ⟨η, hη⟩).isPrime.mem_or_mem (hle hsa)).resolve_left hsq
  exact (hmin _ hPprime htP hPle).symm

theorem stalkIdeal_eq_maximalIdeal_of_minimal (_hx : x ∈ V) (hη : η ∈ V)
    (_hspec : η ⤳ x) (hηs : η ∈ D.support)
    (hmin : ∀ P : Ideal Γ(X, V), P.IsPrime → c.coord j ∈ P →
      P ≤ (hV.primeIdealOf ⟨η, hη⟩).asIdeal → P = (hV.primeIdealOf ⟨η, hη⟩).asIdeal) :
    stalkIdeal D η = IsLocalRing.maximalIdeal (X.presheaf.stalk η) := by
  let _ : Algebra (Γ(X, V)) (X.presheaf.stalk η) :=
    (X.presheaf.germ V η hη).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk η)
      (hV.primeIdealOf ⟨η, hη⟩).asIdeal := hV.isLocalization_stalk ⟨η, hη⟩
  have halg : (algebraMap (Γ(X, V)) (X.presheaf.stalk η)) = (X.presheaf.germ V η hη).hom := rfl
  have hsp : stalkIdeal D η =
      Ideal.span ({(X.presheaf.germ V η hη).hom (c.coord j)} : Set (X.presheaf.stalk η)) :=
    stalkIdeal_eq_span_germ_coord p hV c j D hD η hη
  have hpeq : (hV.primeIdealOf ⟨η, hη⟩).asIdeal =
      Ideal.comap (X.presheaf.germ V η hη).hom
        (Ideal.span ({(X.presheaf.germ V η hη).hom (c.coord j)} :
          Set (X.presheaf.stalk η))) :=
    primeIdealOf_eq_comap_span_germ_coord p hV c j D hD η η hη hη specializes_rfl hηs hmin
  have hne : stalkIdeal D η ≠ ⊤ := (mem_support_iff_stalkIdeal_ne_top D η).mp hηs
  have hsub : Ideal.comap (X.presheaf.germ V η hη).hom
      (IsLocalRing.maximalIdeal (X.presheaf.stalk η)) ≤
      (hV.primeIdealOf ⟨η, hη⟩).asIdeal := by
    intro a ha
    by_contra hcon
    have hunit : IsUnit ((X.presheaf.germ V η hη).hom a) :=
      IsLocalization.map_units (S := X.presheaf.stalk η)
        (M := (hV.primeIdealOf ⟨η, hη⟩).asIdeal.primeCompl) ⟨a, hcon⟩
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
    exact ha hunit
  have h1 : Ideal.map (algebraMap (Γ(X, V)) (X.presheaf.stalk η))
      (Ideal.comap (algebraMap (Γ(X, V)) (X.presheaf.stalk η))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk η)))
      = IsLocalRing.maximalIdeal (X.presheaf.stalk η) :=
    IsLocalization.map_under (M := (hV.primeIdealOf ⟨η, hη⟩).asIdeal.primeCompl)
      (S := X.presheaf.stalk η) _
  refine le_antisymm (IsLocalRing.le_maximalIdeal hne) ?_
  rw [hsp, ← h1, Ideal.map_le_iff_le_comap, halg]
  exact le_trans hsub (le_of_eq hpeq)


end

private theorem mem_span_pow_of_mul_mem_span_pow_consolidated221 {A : Type*} [CommRing A] (τ : A)
    (hprime : (Ideal.span ({τ} : Set A)).IsPrime) (hnzd : τ ∈ nonZeroDivisors A) (a : ℕ) :
    ∀ s f : A, s ∉ Ideal.span ({τ} : Set A) →
      s * f ∈ Ideal.span ({τ ^ a} : Set A) → f ∈ Ideal.span ({τ ^ a} : Set A) := by
  induction a with
  | zero =>
      intro s f _ _
      rw [pow_zero, Ideal.span_singleton_one]
      exact Submodule.mem_top
  | succ b ih =>
      intro s f hs hsf
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hsf
      have hsf1 : s * f ∈ Ideal.span ({τ} : Set A) := by
        refine Ideal.mem_span_singleton.mpr ⟨τ ^ b * d, ?_⟩
        rw [hd]
        ring
      have hf1 : f ∈ Ideal.span ({τ} : Set A) := (hprime.mem_or_mem hsf1).resolve_left hs
      obtain ⟨f', rfl⟩ := Ideal.mem_span_singleton.mp hf1
      have hcancel : (s * f' - τ ^ b * d) * τ = 0 := by
        have h2 : (s * f' - τ ^ b * d) * τ = s * (τ * f') - τ ^ (b + 1) * d := by ring
        rw [h2, hd, sub_self]
      have hsf' : s * f' = τ ^ b * d :=
        eq_of_sub_eq_zero ((mem_nonZeroDivisors_iff.mp hnzd).2 _ hcancel)
      have hf' : f' ∈ Ideal.span ({τ ^ b} : Set A) :=
        ih s f' hs (Ideal.mem_span_singleton.mpr ⟨d, hsf'⟩)
      obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp hf'
      refine Ideal.mem_span_singleton.mpr ⟨e, ?_⟩
      rw [he]
      ring

theorem stalkIdeal_le_pow_stalkIdeal_of_minimal {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c : EtaleChart p V n) (j : Fin n) (D : X.IdealSheafData)
    (hD : restrictIdeal D V = c.coordIdeal {j}) (x η : X) (hx : x ∈ V) (hη : η ∈ V)
    (hspec : η ⤳ x) (hηs : η ∈ D.support)
    (hmin : ∀ P : Ideal Γ(X, V), P.IsPrime → c.coord j ∈ P →
      P ≤ (hV.primeIdealOf ⟨η, hη⟩).asIdeal → P = (hV.primeIdealOf ⟨η, hη⟩).asIdeal)
    (I : X.IdealSheafData) (a : ℕ) (ha : (a : ℕ∞) ≤ orderAt I η) :
    stalkIdeal I x ≤ stalkIdeal D x ^ a := by
  let _ : Algebra (Γ(X, V)) (X.presheaf.stalk x) := (X.presheaf.germ V x hx).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hx⟩
  let _ : Algebra (Γ(X, V)) (X.presheaf.stalk η) := (X.presheaf.germ V η hη).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk η) (hV.primeIdealOf ⟨η, hη⟩).asIdeal :=
    hV.isLocalization_stalk ⟨η, hη⟩
  have halgη : (algebraMap (Γ(X, V)) (X.presheaf.stalk η)) = (X.presheaf.germ V η hη).hom := rfl
  have hqcomap : (hV.primeIdealOf ⟨η, hη⟩).asIdeal =
      Ideal.comap (X.presheaf.germ V x hx).hom
        (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x))) :=
    primeIdealOf_eq_comap_span_germ_coord p hV c j D hD x η hx hη hspec hηs hmin
  have hqle : ∀ z : Γ(X, V), (X.presheaf.germ V x hx).hom z ∈
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x)) →
      z ∈ (hV.primeIdealOf ⟨η, hη⟩).asIdeal := by
    intro z hz
    rw [hqcomap]
    exact hz
  have hnetop : (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
      Set (X.presheaf.stalk x))) ≠ ⊤ := by
    intro hcon
    have h1 : (hV.primeIdealOf ⟨η, hη⟩).asIdeal = ⊤ := by
      rw [hqcomap, hcon, Ideal.comap_top]
    exact (hV.primeIdealOf ⟨η, hη⟩).isPrime.ne_top h1
  have hqp : (hV.primeIdealOf ⟨η, hη⟩).asIdeal ≤ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
    intro r hr
    by_contra hcon
    have hunit : IsUnit ((X.presheaf.germ V x hx).hom r) :=
      IsLocalization.map_units (S := X.presheaf.stalk x)
        (M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) ⟨r, hcon⟩
    have hmemr : (X.presheaf.germ V x hx).hom r ∈
        Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x)) := by
      rw [hqcomap] at hr
      exact hr
    exact hnetop (Ideal.eq_top_of_isUnit_mem _ hmemr hunit)
  have hdisj : Disjoint ((hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl : Set (Γ(X, V)))
      ((hV.primeIdealOf ⟨η, hη⟩).asIdeal : Set (Γ(X, V))) := by
    rw [Set.disjoint_left]
    intro r hr hr'
    have hr1 : r ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := hr
    exact hr1 (hqp hr')
  have hqcomap' : (hV.primeIdealOf ⟨η, hη⟩).asIdeal =
      Ideal.comap (algebraMap (Γ(X, V)) (X.presheaf.stalk x))
        (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x))) :=
    hqcomap
  have hmapq : Ideal.map (algebraMap (Γ(X, V)) (X.presheaf.stalk x))
      (hV.primeIdealOf ⟨η, hη⟩).asIdeal =
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x)) := by
    rw [hqcomap']
    exact IsLocalization.map_under (M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
      (S := X.presheaf.stalk x) _
  have hprime : (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
      Set (X.presheaf.stalk x))).IsPrime := by
    rw [← hmapq]
    exact IsLocalization.isPrime_of_isPrime_disjoint
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x)
      (hV.primeIdealOf ⟨η, hη⟩).asIdeal (hV.primeIdealOf ⟨η, hη⟩).isPrime hdisj
  have hnzd : (X.presheaf.germ V x hx).hom (c.coord j) ∈
      nonZeroDivisors (X.presheaf.stalk x) :=
    IsLocalization.nonZeroDivisors_le_comap (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) (coord_mem_nonZeroDivisors hV c j)
  have hDx : stalkIdeal D x =
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x)) :=
    stalkIdeal_eq_span_germ_coord p hV c j D hD x hx
  have hDη : stalkIdeal D η =
      Ideal.span ({(X.presheaf.germ V η hη).hom (c.coord j)} : Set (X.presheaf.stalk η)) :=
    stalkIdeal_eq_span_germ_coord p hV c j D hD η hη
  have hmaxη : stalkIdeal D η = IsLocalRing.maximalIdeal (X.presheaf.stalk η) :=
    stalkIdeal_eq_maximalIdeal_of_minimal p hV c j D hD x η hx hη hspec hηs hmin
  have hIη : stalkIdeal I η ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a :=
    (le_orderAt_iff I η a).mp ha
  have hmapη : IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a =
      Ideal.map (algebraMap (Γ(X, V)) (X.presheaf.stalk η))
        (Ideal.span ({c.coord j ^ a} : Set (Γ(X, V)))) := by
    rw [← hmaxη, hDη, Ideal.span_singleton_pow, Ideal.map_span, halgη]
    simp [Set.image_singleton, map_pow]
  rw [hDx, Ideal.span_singleton_pow, stalkIdeal_eq_map_germ I x ⟨V, hV⟩ hx,
    Ideal.map_le_iff_le_comap]
  intro g hg
  rw [Ideal.mem_comap]
  have hgη : (X.presheaf.germ V η hη).hom g ∈ stalkIdeal I η :=
    germ_mem_stalkIdeal I η ⟨V, hV⟩ hη hg
  have hstep : (X.presheaf.germ V η hη).hom g ∈
      Ideal.map (algebraMap (Γ(X, V)) (X.presheaf.stalk η))
        (Ideal.span ({c.coord j ^ a} : Set (Γ(X, V)))) := by
    rw [← hmapη]
    exact hIη hgη
  obtain ⟨w, hw⟩ := (IsLocalization.mem_map_algebraMap_iff
    (M := (hV.primeIdealOf ⟨η, hη⟩).asIdeal.primeCompl) (S := X.presheaf.stalk η)).mp hstep
  have hw' : algebraMap (Γ(X, V)) (X.presheaf.stalk η) (g * (w.2 : Γ(X, V))) =
      algebraMap (Γ(X, V)) (X.presheaf.stalk η) ((w.1 : Γ(X, V))) := by
    rw [map_mul]
    exact hw
  obtain ⟨cc, hcc⟩ := (IsLocalization.eq_iff_exists
    (M := (hV.primeIdealOf ⟨η, hη⟩).asIdeal.primeCompl)
    (S := X.presheaf.stalk η)).mp hw'
  have humem : ((cc : Γ(X, V)) * (w.2 : Γ(X, V))) ∈
      (hV.primeIdealOf ⟨η, hη⟩).asIdeal.primeCompl := Submonoid.mul_mem _ cc.2 w.2.2
  have hug : ((cc : Γ(X, V)) * (w.2 : Γ(X, V))) * g ∈
      Ideal.span ({c.coord j ^ a} : Set (Γ(X, V))) := by
    have heq : ((cc : Γ(X, V)) * (w.2 : Γ(X, V))) * g = (cc : Γ(X, V)) * (w.1 : Γ(X, V)) := by
      rw [← hcc]
      ring
    rw [heq]
    exact Ideal.mul_mem_left _ _ w.1.2
  have hnotin : (X.presheaf.germ V x hx).hom ((cc : Γ(X, V)) * (w.2 : Γ(X, V))) ∉
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x)) := by
    intro hcon
    exact humem (hqle _ hcon)
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hug
  have hA : (X.presheaf.germ V x hx).hom ((cc : Γ(X, V)) * (w.2 : Γ(X, V))) *
      (X.presheaf.germ V x hx).hom g ∈
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j) ^ a} : Set (X.presheaf.stalk x)) := by
    refine Ideal.mem_span_singleton.mpr ⟨(X.presheaf.germ V x hx).hom d, ?_⟩
    rw [← map_mul, hd, map_mul, map_pow]
  exact mem_span_pow_of_mul_mem_span_pow_consolidated221 _ hprime hnzd a _ _ hnotin hA

section
variable {Y : Scheme.{u}} {V : Y.Opens} (hV : IsAffineOpen V)

private theorem specializes_of_primeIdealOf_le_consolidated221 (a b : Y) (ha : a ∈ V) (hb : b ∈ V)
    (h : (hV.primeIdealOf ⟨a, ha⟩).asIdeal ≤ (hV.primeIdealOf ⟨b, hb⟩).asIdeal) : a ⤳ b := by
  rw [specializes_iff_mem_closure, mem_closure_iff]
  intro W hWopen hbW
  have hbW' : b ∈ (⟨W, hWopen⟩ : Y.Opens) := hbW
  obtain ⟨f, hfW, hbf⟩ :=
    hV.exists_basicOpen_le (⟨b, hbW'⟩ : ↥(⟨W, hWopen⟩ : Y.Opens)) hb
  have hfb : f ∉ (hV.primeIdealOf ⟨b, hb⟩).asIdeal :=
    (isUnit_germ_iff_notMem_primeIdealOf_consolidated221 hV b hb f).mp ((Scheme.mem_basicOpen Y f b hb).mp hbf)
  have hfa : f ∉ (hV.primeIdealOf ⟨a, ha⟩).asIdeal := fun hcon => hfb (h hcon)
  have haf : a ∈ Y.basicOpen f :=
    (Scheme.mem_basicOpen Y f a ha).mpr ((isUnit_germ_iff_notMem_primeIdealOf_consolidated221 hV a ha f).mpr hfa)
  exact ⟨a, SetLike.le_def.mp hfW haf, rfl⟩

private theorem exists_mem_primeIdealOf_eq_of_isPrime_consolidated221 (P : Ideal Γ(Y, V)) (hP : P.IsPrime) :
    ∃ (ξ : Y) (hξ : ξ ∈ V), (hV.primeIdealOf ⟨ξ, hξ⟩).asIdeal = P := by
  have hsub : Set.range hV.fromSpec.base ⊆ (V : Set Y) := hV.range_fromSpec.subset
  have hmem : hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(Y, V)) ∈ V :=
    hsub (Set.mem_range_self _)
  refine ⟨hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(Y, V)), hmem, ?_⟩
  have h1 : hV.fromSpec.base (hV.primeIdealOf
      ⟨hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(Y, V)), hmem⟩) =
      hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(Y, V)) :=
    hV.fromSpec_primeIdealOf ⟨hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(Y, V)), hmem⟩
  exact congrArg PrimeSpectrum.asIdeal (hV.fromSpec.isOpenEmbedding.injective h1)


end

section
variable (D : X.IdealSheafData) (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n), restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j}) {C : Set X} (hC : IsIrreducible C) (hCsub : C ⊆ (D.support : Set X)) (hCmax : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (D.support : Set X) → C' = C)
include hloc hCsub hCmax

theorem exists_etaleChart_genericPoint_mem (x : X) (hx : x ∈ C) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (_ : x ∈ V) (hη : hC.genericPoint ∈ V) (n : ℕ)
      (c : EtaleChart p V n) (j : Fin n),
      restrictIdeal D V = c.coordIdeal {j} ∧ hC.genericPoint ⤳ x ∧
        hC.genericPoint ∈ D.support ∧
        ∀ P : Ideal Γ(X, V), P.IsPrime → c.coord j ∈ P →
          P ≤ (hV.primeIdealOf ⟨hC.genericPoint, hη⟩).asIdeal →
          P = (hV.primeIdealOf ⟨hC.genericPoint, hη⟩).asIdeal := by
  have hCclosed : IsClosed C := isClosed_of_maximal_irreducible_subset_support D hC hCsub hCmax
  have hgen0 : closure ({hC.genericPoint} : Set X) = closure C :=
    (QuasiSober.sober hC.closure isClosed_closure).choose_spec
  have hgen : closure ({hC.genericPoint} : Set X) = C := by
    rw [hgen0]
    exact hCclosed.closure_eq
  have hηC : hC.genericPoint ∈ C := by
    have h1 : hC.genericPoint ∈ closure ({hC.genericPoint} : Set X) := subset_closure rfl
    rwa [hgen] at h1
  have hspec : hC.genericPoint ⤳ x := by
    have h1 : x ∈ closure ({hC.genericPoint} : Set X) := by
      rw [hgen]
      exact hx
    exact specializes_iff_mem_closure.mpr h1
  obtain ⟨U, hxU, n, c, hcase⟩ := hloc x
  have hxsupp : x ∈ D.support := hCsub hx
  have hne : ¬ (restrictIdeal D U = ⊤) := fun htop =>
    notMem_support_of_mem_opens_of_restrictIdeal_eq_top D U htop x hxU hxsupp
  obtain ⟨j, hDU⟩ := hcase.resolve_left hne
  obtain ⟨W, hxW, hW⟩ := Scheme.exists_isAffineOpen_mem x
  obtain ⟨f, hfU, hxf⟩ := hW.exists_basicOpen_le (⟨x, hxU⟩ : ↥U) hxW
  have hVaff : IsAffineOpen (X.basicOpen f) := hW.basicOpen f
  have hVU : X.basicOpen f ≤ U := hfU
  have hxV : x ∈ X.basicOpen f := hxf
  have hηV : hC.genericPoint ∈ X.basicOpen f := hspec.mem_open (X.basicOpen f).isOpen hxV
  have hDV : restrictIdeal D (X.basicOpen f) = (c.restrict hVU).coordIdeal {j} :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU c D {j} hDU
  refine ⟨X.basicOpen f, hVaff, hxV, hηV, n, c.restrict hVU, j, hDV, hspec, hCsub hηC, ?_⟩
  intro P hP hcoord hPle
  obtain ⟨ξ, hξV, hξP⟩ := exists_mem_primeIdealOf_eq_of_isPrime_consolidated221 hVaff P hP
  have hξsupp : ξ ∈ D.support := by
    rw [mem_support_iff_stalkIdeal_ne_top,
      stalkIdeal_eq_span_germ_coord p hVaff (c.restrict hVU) j D hDV ξ hξV]
    intro htop
    have hu := Ideal.span_singleton_eq_top.mp htop
    have hnot :=
      (isUnit_germ_iff_notMem_primeIdealOf_consolidated221 hVaff ξ hξV ((c.restrict hVU).coord j)).mp hu
    rw [hξP] at hnot
    exact hnot hcoord
  have hξη : ξ ⤳ hC.genericPoint :=
    specializes_of_primeIdealOf_le_consolidated221 hVaff ξ hC.genericPoint hξV hηV
      (by rw [hξP]; exact hPle)
  have hclosξ : closure ({ξ} : Set X) ⊆ (D.support : Set X) :=
    closure_minimal (Set.singleton_subset_iff.mpr hξsupp) D.support.2
  have hCsubξ : C ⊆ closure ({ξ} : Set X) := by
    have h1 : closure ({hC.genericPoint} : Set X) ⊆ closure ({ξ} : Set X) :=
      closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hξη))
        isClosed_closure
    rwa [hgen] at h1
  have hEq : closure ({ξ} : Set X) = C :=
    hCmax _ isIrreducible_singleton.closure hCsubξ hclosξ
  have hξC : ξ ∈ C := by
    have h1 : ξ ∈ closure ({ξ} : Set X) := subset_closure rfl
    rwa [hEq] at h1
  have hηξ : hC.genericPoint ⤳ ξ := by
    have h1 : ξ ∈ closure ({hC.genericPoint} : Set X) := by
      rw [hgen]
      exact hξC
    exact specializes_iff_mem_closure.mpr h1
  have hle2 : (hVaff.primeIdealOf ⟨hC.genericPoint, hηV⟩).asIdeal ≤ P := by
    rw [← hξP]
    exact primeIdealOf_le_of_specializes_consolidated221 hVaff hC.genericPoint ξ hηV hξV hηξ
  exact le_antisymm hPle hle2

theorem stalkIdeal_le_pow_of_le_orderAt_genericPoint (I : X.IdealSheafData) (a : ℕ) (ha : (a : ℕ∞) ≤ orderAt I hC.genericPoint)
    (x : X) (hx : x ∈ C) :
    stalkIdeal I x ≤ stalkIdeal D x ^ a := by
  obtain ⟨V, hV, hxV, hηV, n, c, j, hD, hspec, hηs, hmin⟩ :=
    exists_etaleChart_genericPoint_mem p D hloc hC hCsub hCmax x hx
  exact stalkIdeal_le_pow_stalkIdeal_of_minimal p hV c j D hD x hC.genericPoint hxV hηV hspec
    hηs hmin I a ha

theorem stalkIdeal_genericPoint_eq_maximalIdeal :
    stalkIdeal D hC.genericPoint =
      IsLocalRing.maximalIdeal (X.presheaf.stalk hC.genericPoint) := by
  obtain ⟨x, hx⟩ := hC.1
  obtain ⟨V, hV, hxV, hηV, n, c, j, hD, hspec, hηs, hmin⟩ :=
    exists_etaleChart_genericPoint_mem p D hloc hC hCsub hCmax x hx
  exact stalkIdeal_eq_maximalIdeal_of_minimal p hV c j D hD x hC.genericPoint hxV hηV hspec
    hηs hmin

theorem not_stalkIdeal_le_pow_succ_genericPoint (I : X.IdealSheafData) (a : ℕ) (ha : orderAt I hC.genericPoint = (a : ℕ∞)) :
    ¬ stalkIdeal I hC.genericPoint ≤ stalkIdeal D hC.genericPoint ^ (a + 1) := by
  intro hcon
  rw [stalkIdeal_genericPoint_eq_maximalIdeal p D hloc hC hCsub hCmax] at hcon
  have h : ((a + 1 : ℕ) : ℕ∞) ≤ orderAt I hC.genericPoint :=
    (le_orderAt_iff I hC.genericPoint (a + 1)).mpr hcon
  rw [ha] at h
  have h2 : (a : ℕ∞) < ((a + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self a
  exact absurd h (not_le.mpr h2)


end

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsAddHypersurface
section

open Opposite TopologicalSpace

section

theorem det_update_eq_repr {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι K V) (j : ι) (v : V) :
    e.det (Function.update (⇑e) j v) = e.repr v j := by
  have key : ∀ b : ι → K, (Matrix.updateCol (1 : Matrix ι ι K) j b).det = b j := by
    intro b
    have h : (Matrix.cramer (1 : Matrix ι ι K)) b j
        = (Matrix.updateCol (1 : Matrix ι ι K) j b).det := by
      rw [Matrix.cramer_apply]
    rw [← h]
    simp [Matrix.cramer_one]
  have hm : e.toMatrix (Function.update (⇑e) j v)
      = Matrix.updateCol (1 : Matrix ι ι K) j (fun i => e.repr v i) := by
    ext i l
    rw [Module.Basis.toMatrix_apply, Matrix.updateCol_apply, Function.update_apply]
    by_cases hl : l = j
    · simp [hl]
    · rcases eq_or_ne i l with rfl | hil
      · simp [hl, Module.Basis.repr_self]
      · simp [hl, Module.Basis.repr_self, Matrix.one_apply_ne hil, Ne.symm hil]
  rw [Module.Basis.det_apply, hm]
  exact key _

theorem span_image_update_sum_eq {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (y : ι → R) (S : Finset ι) (a : ι → R) (j : ι) (hj : j ∈ S) (ha : IsUnit (a j)) :
    Ideal.span (Function.update y j (∑ i ∈ S, a i * y i) '' (S : Set ι)) =
      Ideal.span (y '' (S : Set ι)) := by
  have hzj : Function.update y j (∑ t ∈ S, a t * y t) j = ∑ t ∈ S, a t * y t := by
    simp
  have hzne : ∀ i : ι, i ≠ j →
      Function.update y j (∑ t ∈ S, a t * y t) i = y i := by
    intro i hi
    rw [Function.update_apply, if_neg hi]
  have hsplit : ∑ t ∈ S, a t * y t = a j * y j + ∑ t ∈ S.erase j, a t * y t :=
    (Finset.add_sum_erase S (fun t => a t * y t) hj).symm
  have key1 : ∀ i ∈ S, Function.update y j (∑ t ∈ S, a t * y t) i
      ∈ Ideal.span (y '' (S : Set ι)) := by
    intro i hi
    by_cases h : i = j
    · rw [h, hzj]
      exact Ideal.sum_mem _ fun t ht =>
        Ideal.mul_mem_left _ _
          (Ideal.subset_span (Set.mem_image_of_mem y (Finset.mem_coe.mpr ht)))
    · rw [hzne i h]
      exact Ideal.subset_span (Set.mem_image_of_mem y (Finset.mem_coe.mpr hi))
  have hmemj : a j * y j ∈
      Ideal.span (Function.update y j (∑ t ∈ S, a t * y t) '' (S : Set ι)) := by
    have h1 : a j * y j
        = Function.update y j (∑ t ∈ S, a t * y t) j - ∑ t ∈ S.erase j, a t * y t := by
      rw [hzj, hsplit]; ring
    rw [h1]
    refine Submodule.sub_mem _
      (Ideal.subset_span (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hj))) ?_
    refine Ideal.sum_mem _ fun t ht => Ideal.mul_mem_left _ _ ?_
    rw [← hzne t (Finset.ne_of_mem_erase ht)]
    exact Ideal.subset_span
      (Set.mem_image_of_mem _ (Finset.mem_coe.mpr (Finset.mem_of_mem_erase ht)))
  have key2 : ∀ i ∈ S, y i ∈
      Ideal.span (Function.update y j (∑ t ∈ S, a t * y t) '' (S : Set ι)) := by
    intro i hi
    by_cases h : i = j
    · obtain ⟨u, hu⟩ := ha
      have hyj : y j = (↑u⁻¹ : R) * (a j * y j) := by
        rw [← mul_assoc, ← hu, Units.inv_mul, one_mul]
      rw [h, hyj]
      exact Ideal.mul_mem_left _ _ hmemj
    · rw [← hzne i h]
      exact Ideal.subset_span (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hi))
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro _ ⟨i, hi, rfl⟩
    exact SetLike.mem_coe.mpr (key1 i (Finset.mem_coe.mp hi))
  · rintro _ ⟨i, hi, rfl⟩
    exact SetLike.mem_coe.mpr (key2 i (Finset.mem_coe.mp hi))

theorem exists_basis_isUnit_det_of_isLocalization {k : Type*} [Field k] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {S : Type*} [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
    {S' : Type*} [CommRing S'] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']
    (M : Submonoid S) [IsLocalization M S'] (v : ι → S)
    (h : IsUnit (algebraMap S S'
      ((EtaleCoordinates.basisKaehler k ι S).det
        fun i : ι => KaehlerDifferential.D k S (v i)))) :
    ∃ e : Module.Basis ι S' (KaehlerDifferential k S'),
      IsUnit (e.det fun i : ι =>
        KaehlerDifferential.D k S' (algebraMap S S' (v i))) := by
  let instPS' : Algebra (MvPolynomial ι k) S' :=
    ((algebraMap S S').comp (algebraMap (MvPolynomial ι k) S)).toAlgebra
  have instT1 : IsScalarTower (MvPolynomial ι k) S S' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have t2Space_cuspAdeles : IsScalarTower k (MvPolynomial ι k) S' :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply k S S' x,
        IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S x]
      rfl
  have instFEloc : Algebra.FormallyEtale S S' :=
    Algebra.FormallyEtale.of_isLocalization (M := M)
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial ι k) S' :=
    Algebra.FormallyEtale.comp (MvPolynomial ι k) S S'
  refine ⟨EtaleCoordinates.basisKaehler k ι S', ?_⟩
  rw [← EtaleCoordinates.algebraMap_det_basisKaehler k ι S S' v]
  exact h

section
variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)

theorem notMem_basicOpen_of_mem_primeIdealOf (f : Γ(X, U))
    (hf : f ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) : x ∉ X.basicOpen f := by
  intro hmem
  have h1 : hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) = x :=
    hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have h2 : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
    show hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f
    rw [h1]
    exact hmem
  rw [hU.fromSpec_preimage_basicOpen] at h2
  exact (PrimeSpectrum.mem_basicOpen f _).mp h2 hf

private theorem map_germ_primeIdealOf_eq_maximalIdeal_consolidated239 :
    Ideal.map (X.presheaf.germ U x hx).hom (hU.primeIdealOf ⟨x, hx⟩).asIdeal =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  let instAlgStalk : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hx).hom.toAlgebra
  have instLocStalk : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  have h : Ideal.map (algebraMap Γ(X, U) (X.presheaf.stalk x))
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal = IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal (hU.primeIdealOf ⟨x, hx⟩).asIdeal
      (X.presheaf.stalk x)
  exact h


end

theorem mem_support_of_ideal_le_primeIdealOf {X : Scheme.{u}} (D : X.IdealSheafData) {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (h : D.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) : x ∈ D.support := by
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_eq_map_germ D x ⟨U, hU⟩ hx]
  refine le_trans (Ideal.map_mono h) ?_
  exact le_of_eq (map_germ_primeIdealOf_eq_maximalIdeal_consolidated239 hU hx)

section
variable {X₁ : Scheme.{u}} (V : X₁.Opens)

private theorem appLE_top_eq_topIso_inv_consolidated239 (e : (⊤ : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ e = V.topIso.inv := by
  simp
  exact Scheme.presheaf_map_eq_of_parallel ..

private theorem eq_of_ideal_map_topIso_inv_eq_consolidated239 {J₁ J₂ : Ideal Γ(X₁, V)}
    (hJ : Ideal.map V.topIso.inv.hom J₁ = Ideal.map V.topIso.inv.hom J₂) : J₁ = J₂ := by
  have hid : (V.topIso.hom.hom).comp (V.topIso.inv.hom) = RingHom.id _ := by
    ext x
    exact V.topIso.inv_hom_id_apply x
  have key : ∀ J : Ideal Γ(X₁, V),
      Ideal.map V.topIso.hom.hom (Ideal.map V.topIso.inv.hom J) = J := by
    intro J
    rw [Ideal.map_map, hid, Ideal.map_id]
  rw [← key J₁, hJ, key J₂]


end

theorem ideal_eq_span_image_map_of_le {X : Scheme.{u}} (D : X.IdealSheafData) {U U' : X.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U' ≤ U) (s : Set Γ(X, U))
    (hs : D.ideal ⟨U, hU⟩ = Ideal.span s) :
    D.ideal ⟨U', hU'⟩ = Ideal.span ((X.presheaf.map (homOfLE h).op).hom '' s) := by
  have hU'aff : IsAffine U'.toScheme := hU'
  have htop : IsAffineOpen (⊤ : (U'.toScheme).Opens) := isAffineOpen_top U'.toScheme
  have e2 : (⊤ : (U'.toScheme).Opens) ≤ U'.ι ⁻¹ᵁ U' := by
    intro x _
    exact x.2
  have e1 : (⊤ : (U'.toScheme).Opens) ≤ U'.ι ⁻¹ᵁ U := by
    intro x _
    exact h x.2
  have key1 : (D.comap U'.ι).ideal ⟨⊤, htop⟩
      = Ideal.map (U'.ι.appLE U ⊤ e1).hom (D.ideal ⟨U, hU⟩) :=
    D.comap_ideal_eq_map_appLE U'.ι ⟨U, hU⟩ ⟨⊤, htop⟩ e1
  have key2 : (D.comap U'.ι).ideal ⟨⊤, htop⟩
      = Ideal.map (U'.ι.appLE U' ⊤ e2).hom (D.ideal ⟨U', hU'⟩) :=
    D.comap_ideal_eq_map_appLE U'.ι ⟨U', hU'⟩ ⟨⊤, htop⟩ e2
  have happ : U'.ι.appLE U ⊤ e1 = X.presheaf.map (homOfLE h).op ≫ U'.ι.appLE U' ⊤ e2 := by
    rw [Scheme.Hom.map_appLE]
  have hmain : D.ideal ⟨U', hU'⟩
      = Ideal.map (X.presheaf.map (homOfLE h).op).hom (D.ideal ⟨U, hU⟩) := by
    refine eq_of_ideal_map_topIso_inv_eq_consolidated239 U' ?_
    rw [← appLE_top_eq_topIso_inv_consolidated239 U' e2, ← key2, key1, happ, CommRingCat.hom_comp,
      ← Ideal.map_map]
  rw [hmain, hs, Ideal.map_span]

def IsCoordLabeling {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
    {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (lab : ℕ → Option (Fin m))
    (N : List X.IdealSheafData) : Prop :=
  ∀ i : ℕ, ∀ hi : i < N.length,
    (lab i = none → restrictIdeal (N[i]'hi) U = ⊤) ∧
    (∀ j : Fin m, lab i = some j → restrictIdeal (N[i]'hi) U = c.coordIdeal {j})

def LabelingInjective {m : ℕ} (lab : ℕ → Option (Fin m)) (n : ℕ) : Prop :=
  ∀ i i' : ℕ, i < n → i' < n → ∀ j : Fin m, lab i = some j → lab i' = some j → i = i'

theorem exists_etaleCharts_of_inStrictNormalCrossingPosition_cons {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (Z H : X.IdealSheafData) (N : List X.IdealSheafData)
    (hN : InStrictNormalCrossingPosition p (H :: N)) (hZ : HasStrictNormalCrossingsWith p Z N) (hHZ : H ≤ Z)
    (x : X) (hx : x ∈ Z.support) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m)
      (lab : ℕ → Option (Fin m)) (S : Finset (Fin m)) (m' : ℕ) (c' : EtaleChart p U m')
      (j0 : Fin m') (lab' : ℕ → Option (Fin m')),
      restrictIdeal Z U = c.coordIdeal S ∧
      restrictIdeal H U = c'.coordIdeal {j0} ∧
      IsCoordLabeling c lab N ∧
      LabelingInjective lab N.length ∧
      IsCoordLabeling c' (fun i => lab' (i + 1)) N ∧
      (∀ i : ℕ, i < N.length → lab' (i + 1) ≠ some j0) := by
  obtain ⟨U₁, hxU₁, m₁, c₁, a₁, S₁, hinj₁, hnone₁, hsome₁, hZU₁⟩ := hZ.exists_etaleChart hx
  have hptN := ((inStrictNormalCrossingPosition_iff p (H :: N)).mp hN).2 x
  obtain ⟨U₂, hxU₂, m₂, c₂, a₂, hinj₂, hnone₂, hsome₂⟩ := hptN.exists_etaleChart
  obtain ⟨V, hVaff, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (U := U₁ ⊓ U₂) ⟨hxU₁, hxU₂⟩
  have hVU₁ : V ≤ U₁ := le_trans hVW inf_le_left
  have hVU₂ : V ≤ U₂ := le_trans hVW inf_le_right
  have hlen0 : 0 < (H :: N).length := by simp
  have hHsupp : x ∈ H.support := Scheme.IdealSheafData.support_antitone hHZ hx
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin m₂, a₂ 0 = some j0 := by
    cases hcase : a₂ 0 with
    | none =>
        exfalso
        have h := hnone₂ 0 hlen0 hcase
        simp only [List.getElem_cons_zero] at h
        exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top H U₂ h x hxU₂ hHsupp
    | some j => exact ⟨j, rfl⟩
  refine ⟨V, hVaff, hxV, m₁, c₁.restrict hVU₁, a₁, S₁, m₂, c₂.restrict hVU₂, j0, a₂,
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU₁ c₁ Z S₁ hZU₁, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hsome₂ 0 hlen0 j0 hj0
    simp only [List.getElem_cons_zero] at h
    exact restrictIdeal_eq_restrict_coordIdeal_of_le hVU₂ c₂ H {j0} h
  · intro i hi
    refine ⟨fun hn => ?_, fun j hs => ?_⟩
    · exact restrictIdeal_eq_top_of_le (N[i]'hi) hVU₁ (hnone₁ i hi hn)
    · exact restrictIdeal_eq_restrict_coordIdeal_of_le hVU₁ c₁ (N[i]'hi) {j} (hsome₁ i hi j hs)
  · intro i i' hi hi' j h h'
    exact hinj₁ i hi i' hi' j h h'
  · intro i hi
    have hi' : i + 1 < (H :: N).length := by
      simp only [List.length_cons]
      omega
    refine ⟨fun hn => ?_, fun j hs => ?_⟩
    · have h := hnone₂ (i + 1) hi' hn
      simp only [List.getElem_cons_succ] at h
      exact restrictIdeal_eq_top_of_le (N[i]'hi) hVU₂ h
    · have h := hsome₂ (i + 1) hi' j hs
      simp only [List.getElem_cons_succ] at h
      exact restrictIdeal_eq_restrict_coordIdeal_of_le hVU₂ c₂ (N[i]'hi) {j} h
  · intro i hi hcon
    have hi' : i + 1 < (H :: N).length := by
      simp only [List.length_cons]
      omega
    have hzero := hinj₂ (i + 1) hi' 0 hlen0 j0 hcon hj0
    omega

private theorem exists_coeffs_of_mem_span_image_consolidated239 {R : Type*} [CommRing R] {ι : Type*}
    [DecidableEq ι] (y : ι → R) (S : Finset ι) (z : R)
    (hz : z ∈ Ideal.span (y '' (S : Set ι))) :
    ∃ a : ι → R, z = ∑ j ∈ S, a j * y j := by
  classical
  have hle : Ideal.span (y '' (S : Set ι)) ≤
      ({ carrier := {w : R | ∃ a : ι → R, w = ∑ j ∈ S, a j * y j}
         add_mem' := by
           rintro u v ⟨au, rfl⟩ ⟨av, rfl⟩
           refine ⟨fun i => au i + av i, ?_⟩
           rw [← Finset.sum_add_distrib]
           exact Finset.sum_congr rfl fun i _ => by ring
         zero_mem' := ⟨0, by simp⟩
         smul_mem' := by
           rintro r u ⟨au, rfl⟩
           refine ⟨fun i => r * au i, ?_⟩
           rw [smul_eq_mul, Finset.mul_sum]
           exact Finset.sum_congr rfl fun i _ => by ring } : Ideal R) := by
    rw [Ideal.span_le]
    rintro w ⟨j, hj, rfl⟩
    have hjS : j ∈ S := Finset.mem_coe.mp hj
    refine ⟨fun i => if i = j then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single_of_mem j hjS]
    · simp
    · intro i _ hij
      simp [hij]
  exact hle hz

section
variable {X : Scheme.{u}} {k : Type u} [Field k]

private theorem ideal_eq_span_coord_of_restrictIdeal_eq_consolidated239 {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} (hU : IsAffineOpen U) {m : ℕ}
    (c : EtaleChart p U m) (I : X.IdealSheafData) (j : Fin m)
    (h : restrictIdeal I U = c.coordIdeal {j}) :
    I.ideal ⟨U, hU⟩ = Ideal.span ({c.coord j} : Set Γ(X, U)) := by
  rw [c.ideal_eq_span_coord hU I {j} h, Finset.coe_singleton, Set.image_singleton]

theorem exists_coord_eq_sum_coeff_not_mem_of_le (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) {m : ℕ} (c : EtaleChart p U m)
    (lab : ℕ → Option (Fin m)) (S : Finset (Fin m)) {m' : ℕ} (c' : EtaleChart p U m')
    (j0 : Fin m') (lab' : ℕ → Option (Fin m')) (Z H : X.IdealSheafData)
    (N : List X.IdealSheafData)
    (hxZ : x ∈ Z.support)
    (hlab : IsCoordLabeling c lab N)
    (hZU : restrictIdeal Z U = c.coordIdeal S)
    (hHU : restrictIdeal H U = c'.coordIdeal {j0})
    (hlab' : IsCoordLabeling c' (fun i => lab' (i + 1)) N)
    (hj0 : ∀ i : ℕ, i < N.length → lab' (i + 1) ≠ some j0)
    (hHZ : H ≤ Z) :
    ∃ a : Fin m → Γ(X, U),
      c'.coord j0 = ∑ j ∈ S, a j * c.coord j ∧
      ∃ j ∈ S, a j ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∧
        ∀ i : ℕ, i < N.length → lab i ≠ some j := by
  classical
  let instAlgBase : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let instAlgPoly : Algebra (MvPolynomial (ULift.{u} (Fin m')) k) Γ(X, U) := c'.algebra
  have instTower : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m')) k) Γ(X, U) :=
    c'.isScalarTower
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m')) k) Γ(X, U) :=
    c'.algebra_formallyEtale hU
  obtain ⟨D, hD1, hD0⟩ : ∃ D : Derivation k Γ(X, U) Γ(X, U),
      D (c'.coord j0) = 1 ∧ ∀ t : Fin m', t ≠ j0 → D (c'.coord t) = 0 := by
    refine ⟨EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m')) Γ(X, U) (ULift.up j0), ?_, ?_⟩
    · rw [← c'.etaleCoordinates_coord j0]
      exact EtaleCoordinates.partialDeriv_coord_self k (ULift.{u} (Fin m')) Γ(X, U)
        (ULift.up j0)
    · intro t ht
      rw [← c'.etaleCoordinates_coord t]
      exact EtaleCoordinates.partialDeriv_coord_of_ne k (ULift.{u} (Fin m')) Γ(X, U)
        (ULift.up j0) (ULift.up t) (fun hcon => ht (congrArg ULift.down hcon).symm)
  have hZideal : Z.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m))) :=
    c.ideal_eq_span_coord hU Z S hZU
  have hZP : Z.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    ideal_le_primeIdealOf Z hU hx hxZ
  have hcP : ∀ j ∈ S, c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    intro j hj
    refine hZP ?_
    rw [hZideal]
    exact Ideal.subset_span ⟨j, Finset.mem_coe.mpr hj, rfl⟩
  have hHideal : H.ideal ⟨U, hU⟩ = Ideal.span ({c'.coord j0} : Set Γ(X, U)) :=
    ideal_eq_span_coord_of_restrictIdeal_eq_consolidated239 hU c' H j0 hHU
  obtain ⟨a, ha⟩ : ∃ a : Fin m → Γ(X, U), c'.coord j0 = ∑ j ∈ S, a j * c.coord j := by
    refine exists_coeffs_of_mem_span_image_consolidated239 c.coord S (c'.coord j0) ?_
    rw [← hZideal]
    refine hHZ ⟨U, hU⟩ ?_
    rw [hHideal]
    exact Ideal.subset_span rfl
  refine ⟨a, ha, ?_⟩
  by_cases hex : ∃ j ∈ S, a j ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∧
      ∀ i : ℕ, i < N.length → lab i ≠ some j
  · exact hex
  · exfalso
    have hlabelMem : ∀ j ∈ S, ∀ i : ℕ, i < N.length → lab i = some j →
        D (c.coord j) ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
      intro j hjS i hi hli
      obtain ⟨-, hsome⟩ := hlab i hi
      have hNideal : (N[i]'hi).ideal ⟨U, hU⟩ = Ideal.span ({c.coord j} : Set Γ(X, U)) :=
        ideal_eq_span_coord_of_restrictIdeal_eq_consolidated239 hU c (N[i]'hi) j (hsome j hli)
      have hNle : (N[i]'hi).ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
        rw [hNideal, Ideal.span_le, Set.singleton_subset_iff]
        exact hcP j hjS
      obtain ⟨hnone', hsome'⟩ := hlab' i hi
      cases hlv : lab' (i + 1) with
      | none =>
          exact absurd (mem_support_of_ideal_le_primeIdealOf (N[i]'hi) hU hx hNle)
            (notMem_support_of_mem_opens_of_restrictIdeal_eq_top (N[i]'hi) U (hnone' hlv) x hx)
      | some t =>
          have htj0 : t ≠ j0 := fun hcon =>
            hj0 i hi (hlv.trans (congrArg Option.some hcon))
          have hNideal' : (N[i]'hi).ideal ⟨U, hU⟩ = Ideal.span ({c'.coord t} : Set Γ(X, U)) :=
            ideal_eq_span_coord_of_restrictIdeal_eq_consolidated239 hU c' (N[i]'hi) t (hsome' t hlv)
          have hct : c'.coord t ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
            refine hNle ?_
            rw [hNideal']
            exact Ideal.subset_span rfl
          have hmem : c.coord j ∈ Ideal.span ({c'.coord t} : Set Γ(X, U)) := by
            rw [← hNideal', hNideal]
            exact Ideal.subset_span rfl
          obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp hmem
          have hDv : D (c.coord j) = c'.coord t * D v := by
            rw [← hv, Derivation.leibniz, hD0 t htj0, smul_zero, zero_add, smul_eq_mul]
          rw [hDv]
          exact Ideal.mul_mem_right _ _ hct
    have hone : (1 : Γ(X, U)) ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
      have hsum : (1 : Γ(X, U)) = ∑ j ∈ S, (a j * D (c.coord j) + c.coord j * D (a j)) := by
        calc (1 : Γ(X, U)) = D (c'.coord j0) := hD1.symm
          _ = D (∑ j ∈ S, a j * c.coord j) := by rw [ha]
          _ = ∑ j ∈ S, D (a j * c.coord j) := map_sum D (fun j => a j * c.coord j) S
          _ = ∑ j ∈ S, (a j * D (c.coord j) + c.coord j * D (a j)) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              simp only [Derivation.leibniz, smul_eq_mul]
      rw [hsum]
      refine Ideal.sum_mem _ fun j hj => add_mem ?_ ?_
      · by_cases hlj : ∃ i : ℕ, i < N.length ∧ lab i = some j
        · obtain ⟨i, hi, hli⟩ := hlj
          exact Ideal.mul_mem_left _ _ (hlabelMem j hj i hi hli)
        · have haj : a j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
            by_contra hajP
            exact hex ⟨j, hj, hajP, fun i hi hli => hlj ⟨i, hi, hli⟩⟩
          exact Ideal.mul_mem_right _ _ haj
      · exact Ideal.mul_mem_right _ _ (hcP j hj)
    exact (hU.primeIdealOf ⟨x, hx⟩).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

theorem basisKaehler_apply_eq_D_coord {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    [Algebra k Γ(X, U)] [Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U)]
    [IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U)]
    [Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U)]
    (_hk : algebraMap k Γ(X, U) = sectionsAlgebraMap k p U)
    (hc : algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) = c.coordRingHom)
    (j : Fin m) :
    EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j) =
      KaehlerDifferential.D k Γ(X, U) (c.coord j) := by
  rw [EtaleCoordinates.basisKaehler_apply, EtaleCoordinates.coord_def, hc,
    EtaleChart.coordRingHom_X]


end

section
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]

theorem ringHom_etale_of_formallyEtale {V : X.Opens}
    (hV : IsAffineOpen V) {m : ℕ}
    (f : MvPolynomial (ULift.{u} (Fin m)) k →+* Γ(X, V))
    (hC : ∀ a : k, f (MvPolynomial.C a) = sectionsAlgebraMap k p V a)
    (hf : @Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, V) _ _
      f.toAlgebra) :
    f.Etale := by
  let instP : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, V) := f.toAlgebra
  let instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  have hk : (algebraMap k Γ(X, V)) = sectionsAlgebraMap k p V :=
    algebraMap_sectionsAlgebra k p V
  have h1 : (algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, V)) = f := rfl
  have instTower : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, V) := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [hk, h1, MvPolynomial.algebraMap_eq, hC]
  have instFiniteType : Algebra.FiniteType k Γ(X, V) := finiteType_sections k p ⟨V, hV⟩ hk
  have hFTp : Algebra.FiniteType (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, V) := by
    obtain ⟨t, ht⟩ := instFiniteType.out
    refine ⟨⟨t, ?_⟩⟩
    rw [Algebra.eq_top_iff]
    intro x
    have hx : x ∈ Algebra.adjoin k (↑t : Set Γ(X, V)) := by
      rw [ht]
      exact Algebra.mem_top
    have hle : Algebra.adjoin k (↑t : Set Γ(X, V)) ≤
        Subalgebra.restrictScalars k
          (Algebra.adjoin (MvPolynomial (ULift.{u} (Fin m)) k) (↑t : Set Γ(X, V))) :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact hle hx
  have hFP : Algebra.FinitePresentation (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, V) := by
    rw [← Algebra.FinitePresentation.of_finiteType]
    exact hFTp
  have hEt : @Algebra.Etale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, V) _ _ instP :=
    ⟨hf, hFP⟩
  exact hEt

theorem exists_etaleChart_update_coord {U : X.Opens}
    (hU : IsAffineOpen U) {m : ℕ} (c : EtaleChart p U m) {x : X} (hx : x ∈ U)
    (S : Finset (Fin m)) (a : Fin m → Γ(X, U)) (j : Fin m) (hjS : j ∈ S)
    (hS : ∀ i ∈ S, c.coord i ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
    (haj : a j ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (hVU : V ≤ U) (_ : x ∈ V) (c' : EtaleChart p V m),
      (∀ i : Fin m, i ≠ j →
          c'.coord i = (X.presheaf.map (homOfLE hVU).op).hom (c.coord i)) ∧
      c'.coord j = (X.presheaf.map (homOfLE hVU).op).hom (∑ i ∈ S, a i * c.coord i) ∧
      IsUnit ((X.presheaf.map (homOfLE hVU).op).hom (a j)) := by
  classical
  let instAlgU : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let instPolyU : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra
  have instTowerU : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) :=
    c.isScalarTower
  have instFEU : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) :=
    c.algebra_formallyEtale hU
  obtain ⟨v, hvj, hvne⟩ : ∃ v : ULift.{u} (Fin m) → Γ(X, U),
      v (ULift.up j) = ∑ i ∈ S, a i * c.coord i ∧
        ∀ i : ULift.{u} (Fin m), i ≠ ULift.up j → v i = c.coord i.down := by
    refine ⟨Function.update (fun i : ULift.{u} (Fin m) => c.coord i.down) (ULift.up j)
      (∑ i ∈ S, a i * c.coord i), ?_, fun i hi => ?_⟩
    · rw [Function.update_apply, if_pos rfl]
    · rw [Function.update_apply, if_neg hi]
  have hBcoord : ∀ i : ULift.{u} (Fin m),
      EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m)) Γ(X, U) i =
        KaehlerDifferential.D k Γ(X, U) (c.coord i.down) := fun i =>
    basisKaehler_apply_eq_D_coord c (algebraMap_sectionsAlgebra k p U)
      (EtaleChart.algebraMap_eq_coordRingHom c) i.down
  have hfam : (fun i : ULift.{u} (Fin m) => KaehlerDifferential.D k Γ(X, U) (v i)) =
      Function.update (⇑(EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m)) Γ(X, U)))
        (ULift.up j) (KaehlerDifferential.D k Γ(X, U) (∑ i ∈ S, a i * c.coord i)) := by
    funext i
    by_cases hi : i = ULift.up j
    · rw [Function.update_apply, if_pos hi, hi, hvj]
    · rw [Function.update_apply, if_neg hi, hvne i hi, hBcoord i]
  have hdeteq : (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m)) Γ(X, U)).det
        (fun i : ULift.{u} (Fin m) => KaehlerDifferential.D k Γ(X, U) (v i)) =
      EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j)
        (∑ i ∈ S, a i * c.coord i) := by
    rw [hfam, det_update_eq_repr, EtaleCoordinates.partialDeriv_apply]
  have hDself : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j)
      (c.coord j) = 1 := by
    rw [← c.etaleCoordinates_coord j]
    exact EtaleCoordinates.partialDeriv_coord_self k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j)
  have hDne : ∀ i : Fin m, i ≠ j →
      EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j)
        (c.coord i) = 0 := by
    intro i hi
    rw [← c.etaleCoordinates_coord i]
    exact EtaleCoordinates.partialDeriv_coord_of_ne k (ULift.{u} (Fin m)) Γ(X, U)
      (ULift.up j) (ULift.up i) (fun h => hi (congrArg ULift.down h).symm)
  have hsumeq : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j)
        (∑ i ∈ S, a i * c.coord i) =
      a j + ∑ i ∈ S, c.coord i *
        EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j) (a i) := by
    have h3 : ∀ i ∈ S, i ≠ j →
        a i * EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j)
          (c.coord i) = 0 := by
      intro i _ hij
      rw [hDne i hij, mul_zero]
    have h1 : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j)
          (∑ i ∈ S, a i * c.coord i) =
        (∑ i ∈ S, a i * EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U)
          (ULift.up j) (c.coord i)) +
          ∑ i ∈ S, c.coord i * EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U)
            (ULift.up j) (a i) := by
      rw [map_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Derivation.leibniz, smul_eq_mul]
    rw [h1, Finset.sum_eq_single_of_mem j hjS h3, hDself, mul_one]
  have hdetP : (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m)) Γ(X, U)).det
      (fun i : ULift.{u} (Fin m) => KaehlerDifferential.D k Γ(X, U) (v i)) ∉
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    rw [hdeteq]
    intro hmem
    refine haj ?_
    have hrw : a j =
        EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U) (ULift.up j)
          (∑ i ∈ S, a i * c.coord i) -
          ∑ i ∈ S, c.coord i * EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) Γ(X, U)
            (ULift.up j) (a i) := by
      rw [hsumeq]; ring
    rw [hrw]
    exact Submodule.sub_mem _ hmem
      (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (hS i hi))
  obtain ⟨g, hgdef⟩ : ∃ g : Γ(X, U), g =
      (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m)) Γ(X, U)).det
        (fun i : ULift.{u} (Fin m) => KaehlerDifferential.D k Γ(X, U) (v i)) * a j := ⟨_, rfl⟩
  have hgP : g ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    rw [hgdef]
    intro hmem
    rcases (hU.primeIdealOf ⟨x, hx⟩).isPrime.mem_or_mem hmem with h | h
    · exact hdetP h
    · exact haj h
  have hVaff : IsAffineOpen (X.basicOpen g) := hU.basicOpen g
  have hVU : X.basicOpen g ≤ U := X.basicOpen_le g
  have hxV : x ∈ X.basicOpen g := mem_basicOpen_of_notMem_primeIdealOf hU hx g hgP
  let instAlgV : Algebra k Γ(X, X.basicOpen g) := sectionsAlgebra k p (X.basicOpen g)
  have instLocV : IsLocalization (Submonoid.powers g) Γ(X, X.basicOpen g) :=
    hU.isLocalization_basicOpen g
  have instTowerV : IsScalarTower k Γ(X, U) Γ(X, X.basicOpen g) :=
    isScalarTower_sections k p U g (algebraMap_sectionsAlgebra k p U)
      (algebraMap_sectionsAlgebra k p (X.basicOpen g)) rfl
  have hgunit : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen g) g) :=
    IsLocalization.map_units (M := Submonoid.powers g) Γ(X, X.basicOpen g)
      ⟨g, Submonoid.mem_powers g⟩
  have hmul : algebraMap Γ(X, U) Γ(X, X.basicOpen g) g =
      algebraMap Γ(X, U) Γ(X, X.basicOpen g)
        ((EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m)) Γ(X, U)).det
          (fun i : ULift.{u} (Fin m) => KaehlerDifferential.D k Γ(X, U) (v i))) *
        algebraMap Γ(X, U) Γ(X, X.basicOpen g) (a j) := by
    rw [← map_mul, ← hgdef]
  rw [hmul] at hgunit
  have hdetunit := isUnit_of_mul_isUnit_left hgunit
  have hajunit := isUnit_of_mul_isUnit_right hgunit
  obtain ⟨e, he⟩ := exists_basis_isUnit_det_of_isLocalization (Submonoid.powers g) v hdetunit
  obtain ⟨w, hw⟩ : ∃ w : ULift.{u} (Fin m) → Γ(X, X.basicOpen g),
      ∀ i : ULift.{u} (Fin m), w i = algebraMap Γ(X, U) Γ(X, X.basicOpen g) (v i) :=
    ⟨_, fun _ => rfl⟩
  have he' : IsUnit (e.det fun i : ULift.{u} (Fin m) =>
      KaehlerDifferential.D k Γ(X, X.basicOpen g) (w i)) := by
    have hfun : (fun i : ULift.{u} (Fin m) =>
        KaehlerDifferential.D k Γ(X, X.basicOpen g) (w i)) =
        fun i : ULift.{u} (Fin m) => KaehlerDifferential.D k Γ(X, X.basicOpen g)
          (algebraMap Γ(X, U) Γ(X, X.basicOpen g) (v i)) := by
      funext i
      rw [hw i]
    rw [hfun]
    exact he
  have instFSV : Algebra.FormallySmooth k Γ(X, X.basicOpen g) :=
    formallySmooth_sections k p (X.basicOpen g) hVaff
      (algebraMap_sectionsAlgebra k p (X.basicOpen g))
  have hformallyEtale := EtaleCoordinates.formallyEtale_aeval_of_isUnit_det e w he'
  have hC : ∀ b : k,
      ((MvPolynomial.aeval w :
          MvPolynomial (ULift.{u} (Fin m)) k →ₐ[k] Γ(X, X.basicOpen g)).toRingHom)
        (MvPolynomial.C b) = sectionsAlgebraMap k p (X.basicOpen g) b := by
    intro b
    have h1 : (MvPolynomial.aeval w :
        MvPolynomial (ULift.{u} (Fin m)) k →ₐ[k] Γ(X, X.basicOpen g)) (MvPolynomial.C b) =
        algebraMap k Γ(X, X.basicOpen g) b := MvPolynomial.aeval_C w b
    exact h1.trans (DFunLike.congr_fun (algebraMap_sectionsAlgebra k p (X.basicOpen g)) b)
  have hXv : ∀ i : ULift.{u} (Fin m),
      ((MvPolynomial.aeval w :
          MvPolynomial (ULift.{u} (Fin m)) k →ₐ[k] Γ(X, X.basicOpen g)).toRingHom)
        (MvPolynomial.X i) = w i := fun i => MvPolynomial.aeval_X w i
  have hetale : ((MvPolynomial.aeval w :
      MvPolynomial (ULift.{u} (Fin m)) k →ₐ[k] Γ(X, X.basicOpen g)).toRingHom).Etale :=
    ringHom_etale_of_formallyEtale p hVaff
      ((MvPolynomial.aeval w :
        MvPolynomial (ULift.{u} (Fin m)) k →ₐ[k] Γ(X, X.basicOpen g)).toRingHom) hC hformallyEtale
  obtain ⟨c', hc'⟩ := exists_etaleChart_coord_eq p hVaff w
    ((MvPolynomial.aeval w :
      MvPolynomial (ULift.{u} (Fin m)) k →ₐ[k] Γ(X, X.basicOpen g)).toRingHom)
    hC hXv hetale
  refine ⟨X.basicOpen g, hVaff, hVU, hxV, c', ?_, ?_, hajunit⟩
  · intro i hi
    exact ((hc' i).trans (hw (ULift.up i))).trans
      (congrArg (algebraMap Γ(X, U) Γ(X, X.basicOpen g))
        (hvne (ULift.up i) (fun h => hi (congrArg ULift.down h))))
  · exact ((hc' j).trans (hw (ULift.up j))).trans
      (congrArg (algebraMap Γ(X, U) Γ(X, X.basicOpen g)) hvj)

theorem hasStrictNormalCrossingsWith_cons_of_le (Z H : X.IdealSheafData)
    (N : List X.IdealSheafData) (hN : InStrictNormalCrossingPosition p (H :: N)) (hZ : HasStrictNormalCrossingsWith p Z N)
    (hHZ : H ≤ Z) : HasStrictNormalCrossingsWith p Z (H :: N) := by
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hU, hxU, m, c, lab, S, m', c', j0, lab', hZU, hHU, hlab, hlabinj, hlab', hj0⟩ :=
    exists_etaleCharts_of_inStrictNormalCrossingPosition_cons p Z H N hN hZ hHZ x hx
  obtain ⟨a, ha, j, hjS, hajP, hjlab⟩ :=
    exists_coord_eq_sum_coeff_not_mem_of_le p hU hxU c lab S c' j0 lab' Z H N hx hlab hZU hHU hlab' hj0 hHZ
  have hZideal : Z.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m))) :=
    c.ideal_eq_span_coord hU Z S hZU
  have hHideal : H.ideal ⟨U, hU⟩ = Ideal.span ({c'.coord j0} : Set Γ(X, U)) :=
    ideal_eq_span_coord_of_restrictIdeal_eq_consolidated239 hU c' H j0 hHU
  have hcP : ∀ i ∈ S, c.coord i ∈ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    intro i hi
    refine ideal_le_primeIdealOf Z hU hxU hx ?_
    rw [hZideal]
    exact Ideal.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩
  obtain ⟨V, hV, hVU, hxV, c2, hc2ne, hc2j, hc2unit⟩ :=
    exists_etaleChart_update_coord p hU c hxU S a j hjS hcP hajP
  have hcoordfun : c2.coord = Function.update
      (fun i : Fin m => (X.presheaf.map (homOfLE hVU).op).hom (c.coord i)) j
      (∑ i ∈ S, (X.presheaf.map (homOfLE hVU).op).hom (a i) *
        (X.presheaf.map (homOfLE hVU).op).hom (c.coord i)) := by
    funext i
    by_cases hij : i = j
    · rw [Function.update_apply, if_pos hij, hij, hc2j, map_sum]
      exact Finset.sum_congr rfl fun t _ => map_mul _ _ _
    · rw [Function.update_apply, if_neg hij]
      exact hc2ne i hij
  have hupd : Ideal.span (c2.coord '' (S : Set (Fin m)))
      = Ideal.span ((fun i : Fin m => (X.presheaf.map (homOfLE hVU).op).hom (c.coord i)) ''
        (S : Set (Fin m))) := by
    rw [hcoordfun]
    exact span_image_update_sum_eq
      (fun i : Fin m => (X.presheaf.map (homOfLE hVU).op).hom (c.coord i)) S
      (fun i : Fin m => (X.presheaf.map (homOfLE hVU).op).hom (a i)) j hjS hc2unit
  have hZVspan : Z.ideal ⟨V, hV⟩ = Ideal.span (c2.coord '' (S : Set (Fin m))) := by
    rw [hupd, ideal_eq_span_image_map_of_le Z hU hV hVU (c.coord '' (S : Set (Fin m))) hZideal,
      Set.image_image]
  have hZVcoord : restrictIdeal Z V = c2.coordIdeal S :=
    restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV c2 Z S hZVspan
  have hHVspan : H.ideal ⟨V, hV⟩
      = Ideal.span (c2.coord '' ((({j} : Finset (Fin m))) : Set (Fin m))) := by
    rw [Finset.coe_singleton, Set.image_singleton,
      ideal_eq_span_image_map_of_le H hU hV hVU ({c'.coord j0} : Set Γ(X, U)) hHideal,
      Set.image_singleton, ha, ← hc2j]
  have hHVcoord : restrictIdeal H V = c2.coordIdeal {j} :=
    restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV c2 H {j} hHVspan
  have hNVcoord : ∀ (i : ℕ) (hi : i < N.length) (t : Fin m), lab i = some t →
      restrictIdeal (N[i]'hi) V = c2.coordIdeal {t} := by
    intro i hi t hlt
    have htj : t ≠ j := by
      intro hcon
      exact hjlab i hi (by rw [hlt, hcon])
    have hUeq : restrictIdeal (N[i]'hi) U = c.coordIdeal {t} := (hlab i hi).2 t hlt
    have hideal : (N[i]'hi).ideal ⟨U, hU⟩ = Ideal.span ({c.coord t} : Set Γ(X, U)) :=
      ideal_eq_span_coord_of_restrictIdeal_eq_consolidated239 hU c (N[i]'hi) t hUeq
    have hspanV : (N[i]'hi).ideal ⟨V, hV⟩
        = Ideal.span (c2.coord '' ((({t} : Finset (Fin m))) : Set (Fin m))) := by
      rw [Finset.coe_singleton, Set.image_singleton, hc2ne t htj,
        ideal_eq_span_image_map_of_le (N[i]'hi) hU hV hVU ({c.coord t} : Set Γ(X, U)) hideal,
        Set.image_singleton]
    exact restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV c2 (N[i]'hi) {t} hspanV
  have hNVtop : ∀ (i : ℕ) (hi : i < N.length), lab i = none →
      restrictIdeal (N[i]'hi) V = ⊤ := by
    intro i hi hn
    exact restrictIdeal_eq_top_of_le (N[i]'hi) hVU ((hlab i hi).1 hn)
  obtain ⟨relab, hnl0, hnls⟩ :
      ∃ nl : ℕ → Option (Fin m), nl 0 = some j ∧ ∀ i : ℕ, nl (i + 1) = lab i :=
    ⟨fun i => if i = 0 then some j else lab (i - 1), by simp, fun i => by simp⟩
  refine ⟨V, hxV, m, c2, relab, S, ?_, ?_, ?_, hZVcoord⟩
  · intro i hi i' hi' t h1 h2
    rcases i with _ | i1
    · rcases i' with _ | i1'
      · rfl
      · exfalso
        rw [hnl0] at h1
        rw [hnls i1'] at h2
        have hb : i1' < N.length := by
          simp only [List.length_cons] at hi'
          omega
        exact hjlab i1' hb (h2.trans h1.symm)
    · rcases i' with _ | i1'
      · exfalso
        rw [hnl0] at h2
        rw [hnls i1] at h1
        have hb : i1 < N.length := by
          simp only [List.length_cons] at hi
          omega
        exact hjlab i1 hb (h1.trans h2.symm)
      · rw [hnls i1] at h1
        rw [hnls i1'] at h2
        have hb1 : i1 < N.length := by
          simp only [List.length_cons] at hi
          omega
        have hb2 : i1' < N.length := by
          simp only [List.length_cons] at hi'
          omega
        have hee := hlabinj i1 i1' hb1 hb2 t h1 h2
        omega
  · intro i hi hn
    rcases i with _ | i1
    · rw [hnl0] at hn
      exact absurd hn (Option.some_ne_none j)
    · rw [hnls i1] at hn
      have hb : i1 < N.length := by
        simp only [List.length_cons] at hi
        omega
      exact hNVtop i1 hb hn
  · intro i hi t hs
    rcases i with _ | i1
    · rw [hnl0] at hs
      have htj : t = j := (Option.some.inj hs).symm
      subst htj
      exact hHVcoord
    · rw [hnls i1] at hs
      have hb : i1 < N.length := by
        simp only [List.length_cons] at hi
        omega
      exact hNVcoord i1 hb t hs


end

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianChartChange
section

open Opposite TopologicalSpace

section

private theorem formallySmooth_of_etaleChart_consolidated262 {X₁ : Scheme.{u}} {k₁ : Type u} [Field k₁]
    {p₁ : X₁ ⟶ Spec (CommRingCat.of k₁)} {U₁ : X₁.Opens} {m₁ : ℕ}
    [Algebra k₁ Γ(X₁, U₁)]
    (hk : algebraMap k₁ Γ(X₁, U₁) = sectionsAlgebraMap k₁ p₁ U₁)
    (hU : IsAffineOpen U₁) (c : EtaleChart p₁ U₁ m₁) :
    Algebra.FormallySmooth k₁ Γ(X₁, U₁) := by
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin m₁)) k₁) Γ(X₁, U₁) := c.algebra
  have instT : IsScalarTower k₁ (MvPolynomial (ULift.{u} (Fin m₁)) k₁) Γ(X₁, U₁) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [hk, MvPolynomial.algebraMap_eq]
      exact (c.coordRingHom_C a).symm
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m₁)) k₁) Γ(X₁, U₁) :=
    c.algebra_formallyEtale hU
  exact Algebra.FormallySmooth.comp k₁ (MvPolynomial (ULift.{u} (Fin m₁)) k₁) Γ(X₁, U₁)

private theorem notMem_support_of_restrictIdeal_eq_top_of_mem_consolidated262 {Y : Scheme.{u}} (I : Y.IdealSheafData)
    {U : Y.Opens} (h : restrictIdeal I U = ⊤) {y : Y} (hyU : y ∈ U) : y ∉ I.support := by
  intro hy
  have h1 : (⟨y, hyU⟩ : ↥U) ∈ (I.comap U.ι).support := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
    exact hy
  rw [← restrictIdeal_eq_comap_ι, h, AlgebraicGeometry.Scheme.IdealSheafData.support_top] at h1
  have h2 : (⟨y, hyU⟩ : ↥U) ∈ ((⊥ : TopologicalSpace.Closeds ↥U) : Set ↥U) := h1
  simp at h2

private theorem exists_isUnit_mul_of_span_singleton_eq_consolidated262 {R : Type*} [CommRing R] {y z : R}
    (hy : y ∈ nonZeroDivisors R) (hsp : Ideal.span {z} = Ideal.span {y}) :
    ∃ u : R, IsUnit u ∧ z = u * y := by
  have hz : z ∈ Ideal.span {y} := by
    rw [← hsp]
    exact Ideal.mem_span_singleton_self z
  have hy' : y ∈ Ideal.span {z} := by
    rw [hsp]
    exact Ideal.mem_span_singleton_self y
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hz
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hy'
  have hsub : (b * u - 1) * y = 0 := by
    rw [sub_mul, one_mul, mul_assoc, hu, hb, sub_self]
  have hcancel : ∀ w : R, w * y = 0 → w = 0 := (mem_nonZeroDivisors_iff.mp hy).2
  have h1 : b * u - 1 = 0 := hcancel _ hsub
  have h2 : b * u = 1 := by
    rw [sub_eq_zero] at h1
    exact h1
  have h3 : u * b = 1 := by
    rw [mul_comm]
    exact h2
  exact ⟨u, ⟨⟨u, b, h3, h2⟩, rfl⟩, hu.symm⟩

private theorem repr_sum_smul_apply_consolidated262 {ι₀ : Type*} [Fintype ι₀]
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (b : Module.Basis ι₀ R M) (cc : ι₀ → R) (i : ι₀) :
    b.repr (∑ j : ι₀, cc j • b j) i = cc i := by
  rw [Module.Basis.repr_sum_self]

private theorem basisKaehler_repr_kaehlerMap_consolidated262 (k₀ : Type*) [CommRing k₀] (ι₀ : Type*) [Fintype ι₀]
    [DecidableEq ι₀] (S : Type*) [CommRing S] (S' : Type*) [CommRing S']
    [Algebra k₀ S] [Algebra k₀ S'] [Algebra (MvPolynomial ι₀ k₀) S]
    [Algebra (MvPolynomial ι₀ k₀) S'] [Algebra S S']
    [IsScalarTower k₀ (MvPolynomial ι₀ k₀) S] [IsScalarTower k₀ (MvPolynomial ι₀ k₀) S']
    [IsScalarTower k₀ S S'] [IsScalarTower (MvPolynomial ι₀ k₀) S S']
    [Algebra.FormallyEtale (MvPolynomial ι₀ k₀) S]
    [Algebra.FormallyEtale (MvPolynomial ι₀ k₀) S']
    (ω : KaehlerDifferential k₀ S) (i : ι₀) :
    (EtaleCoordinates.basisKaehler k₀ ι₀ S').repr (KaehlerDifferential.map k₀ k₀ S S' ω) i
      = algebraMap S S' ((EtaleCoordinates.basisKaehler k₀ ι₀ S).repr ω i) := by
  have hb : ∀ j : ι₀,
      KaehlerDifferential.map k₀ k₀ S S' (EtaleCoordinates.basisKaehler k₀ ι₀ S j)
        = EtaleCoordinates.basisKaehler k₀ ι₀ S' j := by
    intro j
    simp only [EtaleCoordinates.basisKaehler_apply, KaehlerDifferential.map_D,
      EtaleCoordinates.algebraMap_coord]
  have hω : ω = ∑ j : ι₀, (EtaleCoordinates.basisKaehler k₀ ι₀ S).repr ω j •
      EtaleCoordinates.basisKaehler k₀ ι₀ S j :=
    ((EtaleCoordinates.basisKaehler k₀ ι₀ S).sum_repr ω).symm
  have key : KaehlerDifferential.map k₀ k₀ S S' ω
      = ∑ j : ι₀, algebraMap S S' ((EtaleCoordinates.basisKaehler k₀ ι₀ S).repr ω j) •
        EtaleCoordinates.basisKaehler k₀ ι₀ S' j := by
    conv_lhs => rw [hω]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [map_smul, hb j]
    exact algebra_compatible_smul S' ((EtaleCoordinates.basisKaehler k₀ ι₀ S).repr ω j)
      (EtaleCoordinates.basisKaehler k₀ ι₀ S' j)
  rw [key]
  exact repr_sum_smul_apply_consolidated262 (EtaleCoordinates.basisKaehler k₀ ι₀ S')
    (fun j => algebraMap S S' ((EtaleCoordinates.basisKaehler k₀ ι₀ S).repr ω j)) i

variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  [Smooth p] {V : X.Opens} {n : ℕ}

section
variable (hV : IsAffineOpen V) (c : EtaleChart p V n)
include hV c

theorem exists_etaleChart_coord_eq_of_isUnit_jacobianDet (w : ULift.{u} (Fin n) → Γ(X, V)) :
    letI : Algebra k Γ(X, V) := sectionsAlgebra k p V
    letI : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
    haveI : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
    haveI : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
      c.algebra_formallyEtale hV
    IsUnit ((EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)).det
        fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(X, V) (w i)) →
      ∃ c' : EtaleChart p V n, ∀ j : Fin n, c'.coord j = w (ULift.up j) := by
  intro hdet0
  let instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  have instT : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  have hk : algebraMap k Γ(X, V) = sectionsAlgebraMap k p V := algebraMap_sectionsAlgebra k p V
  have instFS : Algebra.FormallySmooth k Γ(X, V) := formallySmooth_of_etaleChart_consolidated262 hk hV c
  have hdet : IsUnit ((EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)).det
      fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(X, V) (w i)) := hdet0
  obtain ⟨f, hfC, hfX, hfEtale⟩ :
      ∃ f : MvPolynomial (ULift.{u} (Fin n)) k →+* Γ(X, V),
        (∀ a : k, f (MvPolynomial.C a) = sectionsAlgebraMap k p V a) ∧
        (∀ i : ULift.{u} (Fin n), f (MvPolynomial.X i) = w i) ∧
        @Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) _ _
          f.toAlgebra := by
    refine ⟨(MvPolynomial.aeval (R := k) w).toRingHom, fun a => ?_, fun i => ?_, ?_⟩
    · show MvPolynomial.aeval w (MvPolynomial.C a) = sectionsAlgebraMap k p V a
      rw [MvPolynomial.aeval_C, hk]
    · show MvPolynomial.aeval w (MvPolynomial.X i) = w i
      rw [MvPolynomial.aeval_X]
    · exact EtaleCoordinates.formallyEtale_aeval_of_isUnit_det
        (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)) w hdet
  exact exists_etaleChart_coord_eq p hV w f hfC hfX
    (ringHom_etale_of_formallyEtale p hV f hfC hfEtale)

theorem exists_etaleChart_restrict_coord_eq_of_jacobianDet_notMem
    {x : X} (hx : x ∈ V)
    (w : ULift.{u} (Fin n) → Γ(X, V)) :
    letI : Algebra k Γ(X, V) := sectionsAlgebra k p V
    letI : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
    haveI : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
    haveI : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
      c.algebra_formallyEtale hV
    ((EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)).det
        fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(X, V) (w i)) ∉
        (hV.primeIdealOf ⟨x, hx⟩).asIdeal →
      ∃ (V' : X.Opens) (_ : IsAffineOpen V') (hV'V : V' ≤ V) (_ : x ∈ V')
        (c' : EtaleChart p V' n),
        ∀ j : Fin n,
          c'.coord j = (X.presheaf.map (homOfLE hV'V).op).hom (w (ULift.up j)) := by
  intro hg0
  let instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  have instT : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  obtain ⟨g, hgd⟩ : ∃ g : Γ(X, V),
      g = (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)).det
        fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(X, V) (w i) := ⟨_, rfl⟩
  have hg : g ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
    rw [hgd]
    exact hg0
  have hle : X.basicOpen g ≤ V := X.basicOpen_le g
  have hVg : IsAffineOpen (X.basicOpen g) := hV.basicOpen g
  have hxg : x ∈ X.basicOpen g := mem_basicOpen_of_notMem_primeIdealOf hV hx g hg
  let instk' : Algebra k Γ(X, X.basicOpen g) := sectionsAlgebra k p (X.basicOpen g)
  let instAlg : Algebra Γ(X, V) Γ(X, X.basicOpen g) :=
    (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  have halg : ∀ z : Γ(X, V),
      algebraMap Γ(X, V) Γ(X, X.basicOpen g) z =
        (X.presheaf.map (homOfLE hle).op).hom z := fun _ => rfl
  have instScalarTower : IsScalarTower k Γ(X, V) Γ(X, X.basicOpen g) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [halg]
      exact (FunctorialResolution.EmbeddedResolution.sectionsAlgebraMap_restrict_apply k p hle a).symm
  have instLoc : IsLocalization (Submonoid.powers g) Γ(X, X.basicOpen g) :=
    hV.isLocalization_basicOpen g
  have hunit : IsUnit (algebraMap Γ(X, V) Γ(X, X.basicOpen g)
      ((EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)).det
        fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(X, V) (w i))) := by
    rw [← hgd]
    exact IsLocalization.map_units (M := Submonoid.powers g) Γ(X, X.basicOpen g)
      ⟨g, Submonoid.mem_powers g⟩
  obtain ⟨e, he⟩ := exists_basis_isUnit_det_of_isLocalization (k := k)
    (S' := Γ(X, X.basicOpen g)) (Submonoid.powers g) w hunit
  have instFS : Algebra.FormallySmooth k Γ(X, X.basicOpen g) :=
    formallySmooth_of_etaleChart_consolidated262 (algebraMap_sectionsAlgebra k p (X.basicOpen g)) hVg
      (c.restrict hle)
  obtain ⟨f, hfC, hfX, hfEtale⟩ :
      ∃ f : MvPolynomial (ULift.{u} (Fin n)) k →+* Γ(X, X.basicOpen g),
        (∀ a : k, f (MvPolynomial.C a) = sectionsAlgebraMap k p (X.basicOpen g) a) ∧
        (∀ i : ULift.{u} (Fin n), f (MvPolynomial.X i) =
          algebraMap Γ(X, V) Γ(X, X.basicOpen g) (w i)) ∧
        @Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, X.basicOpen g) _ _
          f.toAlgebra := by
    refine ⟨(MvPolynomial.aeval (R := k)
      (fun i : ULift.{u} (Fin n) =>
        algebraMap Γ(X, V) Γ(X, X.basicOpen g) (w i))).toRingHom,
      fun a => ?_, fun i => ?_, ?_⟩
    · show MvPolynomial.aeval
        (fun i : ULift.{u} (Fin n) => algebraMap Γ(X, V) Γ(X, X.basicOpen g) (w i))
        (MvPolynomial.C a) = sectionsAlgebraMap k p (X.basicOpen g) a
      rw [MvPolynomial.aeval_C, algebraMap_sectionsAlgebra k p (X.basicOpen g)]
    · show MvPolynomial.aeval
        (fun i : ULift.{u} (Fin n) => algebraMap Γ(X, V) Γ(X, X.basicOpen g) (w i))
        (MvPolynomial.X i) = algebraMap Γ(X, V) Γ(X, X.basicOpen g) (w i)
      rw [MvPolynomial.aeval_X]
    · exact EtaleCoordinates.formallyEtale_aeval_of_isUnit_det e
        (fun i : ULift.{u} (Fin n) => algebraMap Γ(X, V) Γ(X, X.basicOpen g) (w i)) he
  obtain ⟨c', hc'⟩ := exists_etaleChart_coord_eq p hVg
    (fun i : ULift.{u} (Fin n) => algebraMap Γ(X, V) Γ(X, X.basicOpen g) (w i)) f hfC hfX
    (ringHom_etale_of_formallyEtale p hVg f hfC hfEtale)
  exact ⟨X.basicOpen g, hVg, hle, hxg, c', fun j => (hc' j).trans (halg _)⟩

theorem exists_etaleChart_coord_add_smul (j₁ j₂ : Fin n) (hj : j₁ ≠ j₂) (t : k) :
    ∃ c' : EtaleChart p V n,
      c'.coord j₂ = c.coord j₂ + sectionsAlgebraMap k p V t * c.coord j₁ ∧
        ∀ j : Fin n, j ≠ j₂ → c'.coord j = c.coord j := by
  let instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  have instT : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  have hk : algebraMap k Γ(X, V) = sectionsAlgebraMap k p V := algebraMap_sectionsAlgebra k p V
  have hcr : algebraMap (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) = c.coordRingHom :=
    c.algebraMap_eq_coordRingHom
  have hcoord : ∀ j : Fin n,
      EtaleCoordinates.coord k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) = c.coord j :=
    fun j => c.etaleCoordinates_coord j
  have h1 : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j₂)
      (c.coord j₂) = 1 := by
    rw [← hcoord j₂]
    exact EtaleCoordinates.partialDeriv_coord_self k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j₂)
  have h2 : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j₂)
      (c.coord j₁) = 0 := by
    rw [← hcoord j₁]
    refine EtaleCoordinates.partialDeriv_coord_of_ne k (ULift.{u} (Fin n)) Γ(X, V)
      (ULift.up j₂) (ULift.up j₁) ?_
    intro hcon
    exact hj (congrArg ULift.down hcon).symm
  have h3 : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j₂)
      (sectionsAlgebraMap k p V t) = 0 := by
    rw [← hk]
    simp
  have hpd : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j₂)
      (c.coord j₂ + sectionsAlgebraMap k p V t * c.coord j₁) = 1 := by
    simp [Derivation.leibniz, h1, h2, h3]
  obtain ⟨w, hwj, hwne, hwupd⟩ : ∃ w : ULift.{u} (Fin n) → Γ(X, V),
      w (ULift.up j₂) = c.coord j₂ + sectionsAlgebraMap k p V t * c.coord j₁ ∧
      (∀ j : Fin n, j ≠ j₂ → w (ULift.up j) = c.coord j) ∧
      (fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(X, V) (w i)) =
        Function.update (⇑(EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)))
          (ULift.up j₂)
          (KaehlerDifferential.D k Γ(X, V)
            (c.coord j₂ + sectionsAlgebraMap k p V t * c.coord j₁)) := by
    refine ⟨Function.update (fun i : ULift.{u} (Fin n) => c.coord i.down) (ULift.up j₂)
      (c.coord j₂ + sectionsAlgebraMap k p V t * c.coord j₁), ?_, fun j hjne => ?_, ?_⟩
    · rw [Function.update_apply]
      exact if_pos rfl
    · rw [Function.update_apply]
      exact if_neg (fun hcon : ULift.up j = ULift.up j₂ => hjne (congrArg ULift.down hcon))
    · funext i
      rw [Function.update_apply, Function.update_apply]
      by_cases hi : i = ULift.up j₂
      · rw [if_pos hi, if_pos hi]
      · rw [if_neg hi, if_neg hi]
        exact (basisKaehler_apply_eq_D_coord c hk hcr i.down).symm
  have hdet : IsUnit ((EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)).det
      fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(X, V) (w i)) := by
    rw [hwupd, det_update_eq_repr, ← EtaleCoordinates.partialDeriv_apply, hpd]
    exact isUnit_one
  obtain ⟨c', hc'⟩ := exists_etaleChart_coord_eq_of_isUnit_jacobianDet hV c w hdet
  refine ⟨c', ?_, fun j hjne => ?_⟩
  · rw [hc' j₂, hwj]
  · rw [hc' j, hwne j hjne]

theorem exists_etaleChart_update_coord_of_partialDeriv_notMem
    {x : X} (hx : x ∈ V) (j₁ : Fin n)
    (x' : Γ(X, V)) :
    letI : Algebra k Γ(X, V) := sectionsAlgebra k p V
    letI : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
    haveI : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
    haveI : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
      c.algebra_formallyEtale hV
    EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j₁) x' ∉
        (hV.primeIdealOf ⟨x, hx⟩).asIdeal →
      ∃ (V' : X.Opens) (_ : IsAffineOpen V') (hV'V : V' ≤ V) (_ : x ∈ V')
        (c' : EtaleChart p V' n),
        c'.coord j₁ = (X.presheaf.map (homOfLE hV'V).op).hom x' ∧
          ∀ j : Fin n, j ≠ j₁ →
            c'.coord j = (X.presheaf.map (homOfLE hV'V).op).hom (c.coord j) := by
  intro hpd0
  let instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  have instT : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  have hpd : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j₁) x' ∉
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal := hpd0
  have hk : algebraMap k Γ(X, V) = sectionsAlgebraMap k p V := algebraMap_sectionsAlgebra k p V
  have hcr : algebraMap (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) = c.coordRingHom :=
    c.algebraMap_eq_coordRingHom
  obtain ⟨w, hwj, hwne, hwupd⟩ : ∃ w : ULift.{u} (Fin n) → Γ(X, V),
      w (ULift.up j₁) = x' ∧
      (∀ j : Fin n, j ≠ j₁ → w (ULift.up j) = c.coord j) ∧
      (fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(X, V) (w i)) =
        Function.update (⇑(EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)))
          (ULift.up j₁) (KaehlerDifferential.D k Γ(X, V) x') := by
    refine ⟨Function.update (fun i : ULift.{u} (Fin n) => c.coord i.down) (ULift.up j₁) x',
      ?_, fun j hjne => ?_, ?_⟩
    · rw [Function.update_apply]
      exact if_pos rfl
    · rw [Function.update_apply]
      exact if_neg (fun hcon : ULift.up j = ULift.up j₁ => hjne (congrArg ULift.down hcon))
    · funext i
      rw [Function.update_apply, Function.update_apply]
      by_cases hi : i = ULift.up j₁
      · rw [if_pos hi, if_pos hi]
      · rw [if_neg hi, if_neg hi]
        exact (basisKaehler_apply_eq_D_coord c hk hcr i.down).symm
  have hdet : ((EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)).det
      fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(X, V) (w i)) ∉
        (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
    rw [hwupd, det_update_eq_repr, ← EtaleCoordinates.partialDeriv_apply]
    exact hpd
  obtain ⟨V', hV'aff, hle, hxV', c', hc'⟩ :=
    exists_etaleChart_restrict_coord_eq_of_jacobianDet_notMem hV c hx w hdet
  refine ⟨V', hV'aff, hle, hxV', c', ?_, fun j hjne => ?_⟩
  · rw [hc' j₁, hwj]
  · rw [hc' j, hwne j hjne]


end

def chartPartialDeriv (hV : IsAffineOpen V) (c : EtaleChart p V n) (j : Fin n)
    (f : Γ(X, V)) : Γ(X, V) :=
  letI _instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  letI _instc : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  haveI _instT : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
  haveI _instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) f

omit [Smooth p] in
private theorem derivation_sum_apply_consolidated262 {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (D : ι → Derivation R A A) (a : A) :
    (∑ i ∈ s, D i) a = ∑ i ∈ s, D i a := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      simp [ih]

omit [Smooth p] in
private theorem chartPartialDeriv_chainRule_consolidated262 {W : X.Opens} (hW : IsAffineOpen W) {n₁ n₂ : ℕ}
    (c₁ : EtaleChart p W n₁) (c₂ : EtaleChart p W n₂) (j : Fin n₂) (f : Γ(X, W)) :
    chartPartialDeriv hW c₂ j f =
      ∑ i : Fin n₁, chartPartialDeriv hW c₂ j (c₁.coord i) * chartPartialDeriv hW c₁ i f := by
  classical
  let instk : Algebra k Γ(X, W) := sectionsAlgebra k p W
  obtain ⟨D, hD⟩ : ∃ D : Derivation k Γ(X, W) Γ(X, W),
      ∀ z : Γ(X, W), D z = chartPartialDeriv hW c₂ j z := by
    let instc₂ : Algebra (MvPolynomial (ULift.{u} (Fin n₂)) k) Γ(X, W) := c₂.algebra
    have instT₂ : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n₂)) k) Γ(X, W) :=
      c₂.isScalarTower
    have instFE₂ : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n₂)) k) Γ(X, W) :=
      c₂.algebra_formallyEtale hW
    exact ⟨EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n₂)) Γ(X, W) (ULift.up j),
      fun _ => rfl⟩
  let instc₁ : Algebra (MvPolynomial (ULift.{u} (Fin n₁)) k) Γ(X, W) := c₁.algebra
  have instT₁ : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n₁)) k) Γ(X, W) :=
    c₁.isScalarTower
  have instFE₁ : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n₁)) k) Γ(X, W) :=
    c₁.algebra_formallyEtale hW
  have hcoord : ∀ i : ULift.{u} (Fin n₁),
      EtaleCoordinates.coord k (ULift.{u} (Fin n₁)) Γ(X, W) i = c₁.coord i.down := by
    rintro ⟨i⟩
    exact c₁.etaleCoordinates_coord i
  have hpd : ∀ i : ULift.{u} (Fin n₁),
      EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n₁)) Γ(X, W) i f =
        chartPartialDeriv hW c₁ i.down f := by
    rintro ⟨i⟩
    rfl
  have hsum := EtaleCoordinates.eq_sum_smul_partialDeriv k (ULift.{u} (Fin n₁)) Γ(X, W) D
  have happ : D f = ∑ i : ULift.{u} (Fin n₁),
      D (EtaleCoordinates.coord k (ULift.{u} (Fin n₁)) Γ(X, W) i) *
        EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n₁)) Γ(X, W) i f := by
    conv_lhs => rw [hsum]
    rw [derivation_sum_apply_consolidated262]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have hbij : Function.Bijective (fun i : ULift.{u} (Fin n₁) => i.down) := by
    constructor
    · rintro ⟨a⟩ ⟨b⟩ hab
      exact congrArg ULift.up hab
    · intro b
      exact ⟨ULift.up b, rfl⟩
  rw [← hD f, happ]
  refine Fintype.sum_bijective (fun i : ULift.{u} (Fin n₁) => i.down) hbij _ _ ?_
  intro i
  rw [hcoord i, hpd i, hD]

omit [Smooth p] in
private theorem chartPartialDeriv_coord_self_consolidated262 (hV : IsAffineOpen V) (c : EtaleChart p V n)
    (j : Fin n) : chartPartialDeriv hV c j (c.coord j) = 1 := by
  let instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  have instT : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  have hcoord : EtaleCoordinates.coord k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) = c.coord j :=
    c.etaleCoordinates_coord j
  show EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) (c.coord j) = 1
  rw [← hcoord]
  exact EtaleCoordinates.partialDeriv_coord_self k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j)

omit [Smooth p] in
private theorem chartPartialDeriv_coord_of_ne_consolidated262 (hV : IsAffineOpen V) (c : EtaleChart p V n)
    (j i : Fin n) (h : j ≠ i) : chartPartialDeriv hV c j (c.coord i) = 0 := by
  let instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  have instT : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  have hcoord : EtaleCoordinates.coord k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up i) = c.coord i :=
    c.etaleCoordinates_coord i
  show EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) (c.coord i) = 0
  rw [← hcoord]
  refine EtaleCoordinates.partialDeriv_coord_of_ne k (ULift.{u} (Fin n)) Γ(X, V)
    (ULift.up j) (ULift.up i) ?_
  intro hcon
  exact h (congrArg ULift.down hcon)

omit [Smooth p] in
private theorem chartPartialDeriv_coord_consolidated262 (hV : IsAffineOpen V) (c : EtaleChart p V n)
    (j i : Fin n) :
    chartPartialDeriv hV c j (c.coord i) = if i = j then (1 : Γ(X, V)) else 0 := by
  by_cases h : i = j
  · rw [if_pos h, ← h]
    exact chartPartialDeriv_coord_self_consolidated262 hV c i
  · rw [if_neg h]
    exact chartPartialDeriv_coord_of_ne_consolidated262 hV c j i (fun hc => h hc.symm)

omit [Smooth p] in
private theorem chartPartialDeriv_add_algebraMap_mul_consolidated262 (hV : IsAffineOpen V) (c : EtaleChart p V n)
    (j : Fin n) (a b : Γ(X, V)) (t : k) :
    chartPartialDeriv hV c j (a + sectionsAlgebraMap k p V t * b) =
      chartPartialDeriv hV c j a + sectionsAlgebraMap k p V t * chartPartialDeriv hV c j b := by
  let instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  have instT : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  have hk : algebraMap k Γ(X, V) = sectionsAlgebraMap k p V := algebraMap_sectionsAlgebra k p V
  have h3 : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j)
      (sectionsAlgebraMap k p V t) = 0 := by
    rw [← hk]
    simp
  show EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j)
      (a + sectionsAlgebraMap k p V t * b)
    = EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) a
      + sectionsAlgebraMap k p V t *
        EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) b
  simp [Derivation.leibniz, h3]

omit [Smooth p] in
private theorem chartPartialDeriv_mul_consolidated262 (hV : IsAffineOpen V) (c : EtaleChart p V n) (j : Fin n)
    (a b : Γ(X, V)) :
    chartPartialDeriv hV c j (a * b) =
      a * chartPartialDeriv hV c j b + b * chartPartialDeriv hV c j a := by
  let instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  have instT : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  show EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) (a * b)
    = a * EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) b
      + b * EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) a
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

omit [Smooth p] in
private theorem chartPartialDeriv_chainRule_of_same_rank_consolidated262 (hV : IsAffineOpen V)
    (c c' : EtaleChart p V n) (j : Fin n) (f : Γ(X, V)) :
    chartPartialDeriv hV c' j f =
      ∑ i : Fin n, chartPartialDeriv hV c' j (c.coord i) * chartPartialDeriv hV c i f :=
  chartPartialDeriv_chainRule_consolidated262 hV c c' j f

theorem exists_etaleChart_coord_add_smul_chartPartialDeriv (hV : IsAffineOpen V)
    (c : EtaleChart p V n) (j₁ j₂ : Fin n) (hj : j₁ ≠ j₂) (t : k) :
    ∃ c' : EtaleChart p V n,
      c'.coord j₂ = c.coord j₂ + sectionsAlgebraMap k p V t * c.coord j₁ ∧
      (∀ j : Fin n, j ≠ j₂ → c'.coord j = c.coord j) ∧
      (∀ f : Γ(X, V),
        chartPartialDeriv hV c' j₁ f =
          chartPartialDeriv hV c j₁ f -
            sectionsAlgebraMap k p V t * chartPartialDeriv hV c j₂ f) ∧
      (∀ (j : Fin n) (f : Γ(X, V)), j ≠ j₁ →
        chartPartialDeriv hV c' j f = chartPartialDeriv hV c j f) := by
  classical
  obtain ⟨c', h1, h2⟩ := exists_etaleChart_coord_add_smul hV c j₁ j₂ hj t
  have hc1 : c'.coord j₁ = c.coord j₁ := h2 j₁ hj
  have hB : ∀ j : Fin n, chartPartialDeriv hV c' j (c.coord j₂) =
      chartPartialDeriv hV c' j (c'.coord j₂) -
        sectionsAlgebraMap k p V t * chartPartialDeriv hV c' j (c.coord j₁) := by
    intro j
    have happ : chartPartialDeriv hV c' j (c'.coord j₂) =
        chartPartialDeriv hV c' j (c.coord j₂) +
          sectionsAlgebraMap k p V t * chartPartialDeriv hV c' j (c.coord j₁) := by
      rw [h1]
      exact chartPartialDeriv_add_algebraMap_mul_consolidated262 hV c' j (c.coord j₂) (c.coord j₁) t
    exact eq_sub_of_add_eq happ.symm
  have hgen : ∀ j i : Fin n, chartPartialDeriv hV c' j (c.coord i) =
      (if i = j then (1 : Γ(X, V)) else 0) -
        (if i = j₂ then (if j = j₁ then sectionsAlgebraMap k p V t else 0) else 0) := by
    intro j i
    by_cases hi : i = j₂
    · rw [hi, hB j, ← hc1, chartPartialDeriv_coord_consolidated262 hV c' j j₂, chartPartialDeriv_coord_consolidated262 hV c' j j₁]
      by_cases hjj : j = j₁
      · simp [hjj]
      · simp [hjj, Ne.symm hjj]
    · rw [← h2 i hi, chartPartialDeriv_coord_consolidated262 hV c' j i, if_neg hi, sub_zero]
  refine ⟨c', h1, h2, ?_, ?_⟩
  · intro f
    rw [chartPartialDeriv_chainRule_of_same_rank_consolidated262 hV c c' j₁ f]
    have hterm : ∀ i : Fin n,
        chartPartialDeriv hV c' j₁ (c.coord i) * chartPartialDeriv hV c i f =
          (if i = j₁ then chartPartialDeriv hV c j₁ f else 0) +
            (if i = j₂ then
              -(sectionsAlgebraMap k p V t * chartPartialDeriv hV c j₂ f) else 0) := by
      intro i
      rw [hgen j₁ i]
      by_cases hi1 : i = j₁
      · simp [hi1, hj]
      · by_cases hi2 : i = j₂
        · simp [hi2, Ne.symm hj]
        · simp [hi1, hi2]
    simp only [hterm]
    simp [Finset.sum_add_distrib, sub_eq_add_neg]
  · intro j f hjne
    rw [chartPartialDeriv_chainRule_of_same_rank_consolidated262 hV c c' j f]
    have hterm : ∀ i : Fin n,
        chartPartialDeriv hV c' j (c.coord i) * chartPartialDeriv hV c i f =
          (if i = j then chartPartialDeriv hV c j f else 0) := by
      intro i
      rw [hgen j i, if_neg hjne, ite_self, sub_zero]
      by_cases hi : i = j
      · simp [hi]
      · simp [hi]
    simp only [hterm]
    simp

omit [Smooth p] in
private theorem etaleChart_restrict_coordRingHom_consolidated262 (c : EtaleChart p V n) {W : X.Opens}
    (hWV : W ≤ V) :
    (c.restrict hWV).coordRingHom =
      ((X.presheaf.map (homOfLE hWV).op).hom).comp c.coordRingHom := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · rw [RingHom.comp_apply, EtaleChart.coordRingHom_C, EtaleChart.coordRingHom_C,
      FunctorialResolution.EmbeddedResolution.sectionsAlgebraMap_restrict_apply]
  · obtain ⟨i⟩ := i
    rw [RingHom.comp_apply, EtaleChart.coordRingHom_X, EtaleChart.coordRingHom_X]
    exact FunctorialResolution.EmbeddedResolution.EtaleChart.coord_restrict c hWV i

omit [Smooth p] in
private theorem map_chartPartialDeriv_restrict_consolidated262 (hV : IsAffineOpen V) (c : EtaleChart p V n)
    {W : X.Opens} (hW : IsAffineOpen W) (hWV : W ≤ V) (j : Fin n) (f : Γ(X, V)) :
    (X.presheaf.map (homOfLE hWV).op).hom (chartPartialDeriv hV c j f)
      = chartPartialDeriv hW (c.restrict hWV) j
          ((X.presheaf.map (homOfLE hWV).op).hom f) := by
  let instkV : Algebra k Γ(X, V) := sectionsAlgebra k p V
  let instkW : Algebra k Γ(X, W) := sectionsAlgebra k p W
  let instcV : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  let instcW : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, W) :=
    (c.restrict hWV).algebra
  let instVW : Algebra Γ(X, V) Γ(X, W) :=
    (X.presheaf.map (homOfLE hWV).op).hom.toAlgebra
  have instScalarTowerMvPolynomial : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.isScalarTower
  have instTW : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, W) :=
    (c.restrict hWV).isScalarTower
  have instFEV : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  have instFEW : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, W) :=
    (c.restrict hWV).algebra_formallyEtale hW
  have halg : ∀ z : Γ(X, V),
      algebraMap Γ(X, V) Γ(X, W) z = (X.presheaf.map (homOfLE hWV).op).hom z := fun _ => rfl
  have instTkVW : IsScalarTower k Γ(X, V) Γ(X, W) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [halg]
      exact (FunctorialResolution.EmbeddedResolution.sectionsAlgebraMap_restrict_apply k p hWV a).symm
  have instTPVW : IsScalarTower (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) Γ(X, W) :=
    IsScalarTower.of_algebraMap_eq fun z => by
      rw [halg]
      show (c.restrict hWV).coordRingHom z
        = (X.presheaf.map (homOfLE hWV).op).hom (c.coordRingHom z)
      rw [etaleChart_restrict_coordRingHom_consolidated262 c hWV]
      rfl
  have key : algebraMap Γ(X, V) Γ(X, W)
      ((EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)).repr
        (KaehlerDifferential.D k Γ(X, V) f) (ULift.up j))
      = (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, W)).repr
        (KaehlerDifferential.D k Γ(X, W) (algebraMap Γ(X, V) Γ(X, W) f)) (ULift.up j) := by
    rw [← KaehlerDifferential.map_D k k Γ(X, V) Γ(X, W)]
    exact (basisKaehler_repr_kaehlerMap_consolidated262 k (ULift.{u} (Fin n)) Γ(X, V) Γ(X, W)
      (KaehlerDifferential.D k Γ(X, V) f) (ULift.up j)).symm
  have hl : chartPartialDeriv hV c j f
      = (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)).repr
        (KaehlerDifferential.D k Γ(X, V) f) (ULift.up j) := rfl
  have hr : chartPartialDeriv hW (c.restrict hWV) j
      ((X.presheaf.map (homOfLE hWV).op).hom f)
      = (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, W)).repr
        (KaehlerDifferential.D k Γ(X, W) ((X.presheaf.map (homOfLE hWV).op).hom f))
        (ULift.up j) := rfl
  rw [hl, hr, ← halg]
  exact key

private theorem map_mem_primeIdealOf_of_mem_of_le_consolidated262 {V₁ W₁ : X.Opens} (hV₁ : IsAffineOpen V₁)
    (hW₁ : IsAffineOpen W₁) (hle : W₁ ≤ V₁) {y : X} (hyV : y ∈ V₁) (hyW : y ∈ W₁)
    (f : Γ(X, V₁)) (hf : f ∈ (hV₁.primeIdealOf ⟨y, hyV⟩).asIdeal) :
    (X.presheaf.map (homOfLE hle).op).hom f ∈ (hW₁.primeIdealOf ⟨y, hyW⟩).asIdeal := by
  by_contra hcon
  have h1 : y ∈ X.basicOpen ((X.presheaf.map (homOfLE hle).op).hom f) :=
    mem_basicOpen_of_notMem_primeIdealOf hW₁ hyW _ hcon
  have hgerm : (X.presheaf.germ W₁ y hyW).hom ((X.presheaf.map (homOfLE hle).op).hom f)
      = (X.presheaf.germ V₁ y hyV).hom f := by
    simp
  have h2 : y ∈ X.basicOpen f := by
    rw [X.mem_basicOpen f y hyV, ← hgerm]
    exact (X.mem_basicOpen _ y hyW).mp h1
  exact notMem_basicOpen_of_mem_primeIdealOf hV₁ hyV f hf h2

omit [Smooth p] in
theorem exists_unlabeled_index_partialDeriv_notMem_primeIdealOf
    (hV : IsAffineOpen V) (c : EtaleChart p V n) {x : X} (hx : x ∈ V)
    (N : List X.IdealSheafData) (γ : ℕ → Option (Fin n)) (H : X.IdealSheafData)
    (g : Γ(X, V)) (hγ : IsCoordLabeling c γ N) (_hinj : LabelingInjective γ N.length)
    (hsnc : InStrictNormalCrossingPositionAt p (H :: N) x) (hg : H.ideal ⟨V, hV⟩ = Ideal.span {g})
    (hxH : x ∈ H.support)
    (hxN : ∀ i : ℕ, ∀ hi : i < N.length, ∀ j : Fin n,
      γ i = some j → x ∈ (N[i]'hi).support) :
    letI : Algebra k Γ(X, V) := sectionsAlgebra k p V
    letI : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
    haveI : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
    haveI : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
      c.algebra_formallyEtale hV
    ∃ j : Fin n, (∀ i : ℕ, i < N.length → γ i ≠ some j) ∧
      EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) g ∉
        (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  classical
  show ∃ j : Fin n, (∀ i : ℕ, i < N.length → γ i ≠ some j) ∧
      chartPartialDeriv hV c j g ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  by_contra hcon
  have hall : ∀ j : Fin n, (∀ i : ℕ, i < N.length → γ i ≠ some j) →
      chartPartialDeriv hV c j g ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
    intro j hj
    by_contra hm
    exact hcon ⟨j, hj, hm⟩
  obtain ⟨U, hxU, m, c₂, alab, hainj, hanone, hasome⟩ := hsnc.exists_etaleChart
  have hlen0 : 0 < (H :: N).length := by
    rw [List.length_cons]
    omega
  have hHget : (H :: N)[0]'hlen0 = H := rfl
  obtain ⟨t, hat⟩ : ∃ t : Fin m, alab 0 = some t := by
    rcases hopt : alab 0 with _ | t
    · exfalso
      have htop : restrictIdeal ((H :: N)[0]'hlen0) U = ⊤ := hanone 0 hlen0 hopt
      rw [hHget] at htop
      exact (notMem_support_of_restrictIdeal_eq_top_of_mem_consolidated262 H htop hxU) hxH
    · exact ⟨t, rfl⟩
  have hHU : restrictIdeal H U = c₂.coordIdeal {t} := by
    have h1 := hasome 0 hlen0 t hat
    rwa [hHget] at h1
  have hxUV : x ∈ (U ⊓ V : X.Opens) := ⟨hxU, hx⟩
  obtain ⟨fW, hfWle, hxfW⟩ := hV.exists_basicOpen_le (⟨x, hxUV⟩ : (U ⊓ V : X.Opens)) hx
  obtain ⟨W, hWaff, hWV, hWU, hxW⟩ :
      ∃ W : X.Opens, IsAffineOpen W ∧ W ≤ V ∧ W ≤ U ∧ x ∈ W :=
    ⟨X.basicOpen fW, hV.basicOpen fW, X.basicOpen_le fW,
      le_trans hfWle inf_le_left, hxfW⟩
  have hHW : restrictIdeal H W = (c₂.restrict hWU).coordIdeal {t} :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hWU c₂ H {t} hHU
  have hHidW : H.ideal ⟨W, hWaff⟩ = Ideal.span {(c₂.restrict hWU).coord t} := by
    have h1 := (c₂.restrict hWU).ideal_eq_span_coord hWaff H {t} hHW
    rwa [Finset.coe_singleton, Set.image_singleton] at h1
  have hgW : H.ideal ⟨W, hWaff⟩
      = Ideal.span {(X.presheaf.map (homOfLE hWV).op).hom g} := by
    have h1 := ideal_eq_span_image_map_of_le H hV hWaff hWV {g} hg
    rwa [Set.image_singleton] at h1
  obtain ⟨u, hu, hgu⟩ := exists_isUnit_mul_of_span_singleton_eq_consolidated262
    (coord_mem_nonZeroDivisors hWaff (c₂.restrict hWU) t) (hgW.symm.trans hHidW)
  have hyq : (c₂.restrict hWU).coord t ∈ (hWaff.primeIdealOf ⟨x, hxW⟩).asIdeal := by
    refine ideal_le_primeIdealOf H hWaff hxW hxH ?_
    rw [hHidW]
    exact Ideal.mem_span_singleton_self _
  have hlabel : ∀ j : Fin n, (∃ i : ℕ, i < N.length ∧ γ i = some j) →
      chartPartialDeriv hWaff (c₂.restrict hWU) t ((c.restrict hWV).coord j) ∈
        (hWaff.primeIdealOf ⟨x, hxW⟩).asIdeal := by
    rintro j ⟨i, hi, hγi⟩
    have hNV : restrictIdeal (N[i]'hi) V = c.coordIdeal {j} := (hγ i hi).2 j hγi
    have hNW : restrictIdeal (N[i]'hi) W = (c.restrict hWV).coordIdeal {j} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hWV c (N[i]'hi) {j} hNV
    have hNidW : (N[i]'hi).ideal ⟨W, hWaff⟩
        = Ideal.span {(c.restrict hWV).coord j} := by
      have h1 := (c.restrict hWV).ideal_eq_span_coord hWaff (N[i]'hi) {j} hNW
      rwa [Finset.coe_singleton, Set.image_singleton] at h1
    have hilen : i + 1 < (H :: N).length := by
      rw [List.length_cons]
      omega
    have hNget : (H :: N)[i + 1]'hilen = N[i]'hi := rfl
    obtain ⟨s, has⟩ : ∃ s : Fin m, alab (i + 1) = some s := by
      rcases hopt : alab (i + 1) with _ | s
      · exfalso
        have htop := hanone (i + 1) hilen hopt
        rw [hNget] at htop
        exact (notMem_support_of_restrictIdeal_eq_top_of_mem_consolidated262 (N[i]'hi) htop hxU) (hxN i hi j hγi)
      · exact ⟨s, rfl⟩
    have hst : s ≠ t := by
      intro heq
      have h0 : (0 : ℕ) = i + 1 :=
        hainj 0 hlen0 (i + 1) hilen t hat (by rw [has, heq])
      omega
    have hNU : restrictIdeal (N[i]'hi) U = c₂.coordIdeal {s} := by
      have h1 := hasome (i + 1) hilen s has
      rwa [hNget] at h1
    have hNW2 : restrictIdeal (N[i]'hi) W = (c₂.restrict hWU).coordIdeal {s} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hWU c₂ (N[i]'hi) {s} hNU
    have hNidW2 : (N[i]'hi).ideal ⟨W, hWaff⟩
        = Ideal.span {(c₂.restrict hWU).coord s} := by
      have h1 := (c₂.restrict hWU).ideal_eq_span_coord hWaff (N[i]'hi) {s} hNW2
      rwa [Finset.coe_singleton, Set.image_singleton] at h1
    obtain ⟨v, _, hvj⟩ := exists_isUnit_mul_of_span_singleton_eq_consolidated262
      (coord_mem_nonZeroDivisors hWaff (c₂.restrict hWU) s) (hNidW.symm.trans hNidW2)
    have hsq : (c₂.restrict hWU).coord s ∈ (hWaff.primeIdealOf ⟨x, hxW⟩).asIdeal := by
      refine ideal_le_primeIdealOf (N[i]'hi) hWaff hxW (hxN i hi j hγi) ?_
      rw [hNidW2]
      exact Ideal.mem_span_singleton_self _
    rw [hvj, chartPartialDeriv_mul_consolidated262,
      chartPartialDeriv_coord_of_ne_consolidated262 hWaff (c₂.restrict hWU) t s (Ne.symm hst),
      mul_zero, zero_add]
    exact Ideal.mul_mem_right _ _ hsq
  have hdecomp := chartPartialDeriv_chainRule_consolidated262 hWaff (c.restrict hWV) (c₂.restrict hWU) t
    ((X.presheaf.map (homOfLE hWV).op).hom g)
  have hsum : chartPartialDeriv hWaff (c₂.restrict hWU) t
      ((X.presheaf.map (homOfLE hWV).op).hom g)
      ∈ (hWaff.primeIdealOf ⟨x, hxW⟩).asIdeal := by
    rw [hdecomp]
    refine Ideal.sum_mem _ fun i _ => ?_
    by_cases hlab : ∃ l : ℕ, l < N.length ∧ γ l = some i
    · exact Ideal.mul_mem_right _ _ (hlabel i hlab)
    · refine Ideal.mul_mem_left _ _ ?_
      have hunlab : ∀ l : ℕ, l < N.length → γ l ≠ some i := by
        intro l hl hcon2
        exact hlab ⟨l, hl, hcon2⟩
      have h1 := hall i hunlab
      have h2 := map_mem_primeIdealOf_of_mem_of_le_consolidated262 hV hWaff hWV hx hxW _ h1
      rw [map_chartPartialDeriv_restrict_consolidated262 hV c hWaff hWV i g] at h2
      exact h2
  have hgt : chartPartialDeriv hWaff (c₂.restrict hWU) t
      ((X.presheaf.map (homOfLE hWV).op).hom g)
      = u * 1 + (c₂.restrict hWU).coord t *
        chartPartialDeriv hWaff (c₂.restrict hWU) t u := by
    rw [hgu, chartPartialDeriv_mul_consolidated262, chartPartialDeriv_coord_self_consolidated262]
  rw [hgt] at hsum
  have huq : u ∈ (hWaff.primeIdealOf ⟨x, hxW⟩).asIdeal := by
    have h2 : (c₂.restrict hWU).coord t *
        chartPartialDeriv hWaff (c₂.restrict hWU) t u
        ∈ (hWaff.primeIdealOf ⟨x, hxW⟩).asIdeal := Ideal.mul_mem_right _ _ hyq
    have h3 := Ideal.sub_mem _ hsum h2
    rwa [add_sub_cancel_right, mul_one] at h3
  exact (hWaff.primeIdealOf ⟨x, hxW⟩).isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ huq hu)

end
end
end FunctorialResolution.EmbeddedResolution
end
