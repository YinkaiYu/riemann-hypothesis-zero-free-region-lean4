import Mathlib
import Core5.M05TransformCharts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicGeometry
universe u
noncomputable section
-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
section

open CategoryTheory.Limits Opposite TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

structure SmoothCenterBlowup {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) : Type (u + 1) where
  center : X.IdealSheafData
  center_smooth : Smooth (center.subschemeι ≫ p)
  center_snc : HasStrictNormalCrossingsWith p center E
  ideal_vanishes : VanishesAlong I center
  obj : Scheme.{u}
  map : obj ⟶ X
  isBlowup : Blowup.IsBlowupAlongIdealSheaf map center
  idealUp : obj.IdealSheafData
  transform_rule : Blowup.exceptionalIdeal map center * idealUp = I.comap map

namespace SmoothCenterBlowup

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {E : List X.IdealSheafData}

def structureMorphism (s : SmoothCenterBlowup p I E) : s.obj ⟶ Spec (CommRingCat.of k) := s.map ≫ p

def exceptionalIdeal (s : SmoothCenterBlowup p I E) : s.obj.IdealSheafData :=
  Blowup.exceptionalIdeal s.map s.center

theorem exceptionalIdeal_eq (s : SmoothCenterBlowup p I E) : s.exceptionalIdeal = s.center.comap s.map := rfl

def boundary (s : SmoothCenterBlowup p I E) : List s.obj.IdealSheafData :=
  E.map (Blowup.strictTransform s.map s.center) ++ [s.exceptionalIdeal]

theorem boundary_eq (s : SmoothCenterBlowup p I E) :
    s.boundary = E.map (Blowup.strictTransform s.map s.center) ++ [s.exceptionalIdeal] := rfl

end SmoothCenterBlowup

structure IdealBlowupSequence {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) extends SequenceOfBlowups X where
  ideal : ∀ i : ℕ, (toSequenceOfBlowups.schemeAt i).IdealSheafData
  boundary : ∀ i : ℕ, List (toSequenceOfBlowups.schemeAt i).IdealSheafData
  ideal_zero : ideal 0 = I.comap (toSequenceOfBlowups.projectionToBase 0)
  boundary_zero : boundary 0 = E.map (fun D => D.comap (toSequenceOfBlowups.projectionToBase 0))
  center_smooth : ∀ i, i < toSequenceOfBlowups.length →
    Smooth
      ((toSequenceOfBlowups.center i).subschemeι ≫ toSequenceOfBlowups.projectionToBase i ≫ p)
  center_snc : ∀ i, i < toSequenceOfBlowups.length →
    HasStrictNormalCrossingsWith (toSequenceOfBlowups.projectionToBase i ≫ p) (toSequenceOfBlowups.center i) (boundary i)
  ideal_vanishes : ∀ i, i < toSequenceOfBlowups.length →
    VanishesAlong (ideal i) (toSequenceOfBlowups.center i)
  ideal_succ : ∀ i, i < toSequenceOfBlowups.length →
    Blowup.exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i) * ideal (i + 1) =
      (ideal i).comap (toSequenceOfBlowups.transitionMapSucc i)
  boundary_succ : ∀ i, i < toSequenceOfBlowups.length →
    boundary (i + 1) =
      (boundary i).map (Blowup.strictTransform (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i)) ++
        [Blowup.exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i)]

namespace IdealBlowupSequence

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {E : List X.IdealSheafData}

def structureMorphism (s : IdealBlowupSequence p I E) (i : ℕ) :
    s.toSequenceOfBlowups.schemeAt i ⟶ Spec (CommRingCat.of k) :=
  s.toSequenceOfBlowups.projectionToBase i ≫ p

section
variable (s : IdealBlowupSequence p I E) (i : ℕ)

theorem structureMorphism_def :
    s.structureMorphism i = s.toSequenceOfBlowups.projectionToBase i ≫ p := rfl

theorem smooth_center_subschemeι (h : i < s.toSequenceOfBlowups.length) :
    Smooth ((s.toSequenceOfBlowups.center i).subschemeι ≫ s.structureMorphism i) :=
  s.center_smooth i h

theorem hasStrictNormalCrossingsWith_center (h : i < s.toSequenceOfBlowups.length) :
    HasStrictNormalCrossingsWith (s.structureMorphism i) (s.toSequenceOfBlowups.center i) (s.boundary i) :=
  s.center_snc i h


end

def exceptionalIdeal (s : IdealBlowupSequence p I E) (i : ℕ) : (s.toSequenceOfBlowups.schemeAt (i + 1)).IdealSheafData :=
  Blowup.exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i)

section
variable (s : IdealBlowupSequence p I E) (i : ℕ)

theorem exceptionalIdeal_eq :
    s.exceptionalIdeal i = (s.toSequenceOfBlowups.center i).comap (s.toSequenceOfBlowups.transitionMapSucc i) := rfl

theorem boundary_succ_eq_map_strictTransform_append (h : i < s.toSequenceOfBlowups.length) :
    s.boundary (i + 1) =
      (s.boundary i).map
          (Blowup.strictTransform (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i)) ++
        [s.exceptionalIdeal i] :=
  s.boundary_succ i h


end

def lastIdeal (s : IdealBlowupSequence p I E) :
    (s.toSequenceOfBlowups.schemeAt s.toSequenceOfBlowups.length).IdealSheafData :=
  s.ideal s.toSequenceOfBlowups.length

theorem lastIdeal_eq (s : IdealBlowupSequence p I E) :
    s.lastIdeal = s.ideal s.toSequenceOfBlowups.length := rfl

end IdealBlowupSequence

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
section

open CategoryTheory.Limits Opposite TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

def withBotSuccToNat : WithBot ℕ∞ → ℕ
  | ⊥ => 0
  | (n : ℕ∞) => n.toNat + 1

theorem withBotSuccToNat_bot : withBotSuccToNat ⊥ = 0 := rfl

theorem withBotSuccToNat_coe (n : ℕ∞) : withBotSuccToNat (n : WithBot ℕ∞) = n.toNat + 1 := rfl

def krullDimSucc (X : Scheme.{u}) : ℕ := withBotSuccToNat (topologicalKrullDim ↥X)

theorem krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim (X : Scheme.{u}) : krullDimSucc X = withBotSuccToNat (topologicalKrullDim ↥X) := rfl

theorem krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le (X Y : Scheme.{u})
    (h : topologicalKrullDim ↥X ≤ topologicalKrullDim ↥Y)
    (hY : topologicalKrullDim ↥Y < ⊤) :
    krullDimSucc X ≤ krullDimSucc Y := by
  rcases eq_or_ne (topologicalKrullDim ↥X) ⊥ with hX | hX
  · simp [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, hX, withBotSuccToNat_bot]
  · obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hX
    have hYne : topologicalKrullDim ↥Y ≠ ⊥ := by
      intro hb0
      rw [hb0, le_bot_iff] at h
      exact hX h
    obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.mp hYne
    have hab : a ≤ b := by
      rw [← ha, ← hb] at h
      exact_mod_cast h
    have hbtop : b ≠ ⊤ := by
      intro hbt
      rw [← hb, hbt] at hY
      exact lt_irrefl _ hY
    have hatop : a ≠ ⊤ := by
      intro hat
      rw [hat, top_le_iff] at hab
      exact hbtop hab
    have hle : a.toNat ≤ b.toNat := by
      lift a to ℕ using hatop
      lift b to ℕ using hbtop
      simpa using hab
    rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim X, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim Y, ← ha, ← hb, withBotSuccToNat_coe, withBotSuccToNat_coe]
    omega

structure MarkedIdealWithBoundary : Type (u + 1) where
  base : Type u
  [instField : Field base]
  scheme : Scheme.{u}
  structMap : scheme ⟶ Spec (CommRingCat.of base)
  ideal : scheme.IdealSheafData
  mult : ℕ
  boundary : List scheme.IdealSheafData

attribute [instance] MarkedIdealWithBoundary.instField

theorem MarkedIdealWithBoundary.mk_eq_mk {k : Type u} [instk : Field k] (X : Scheme.{u}) (m : ℕ)
    {p p' : X ⟶ Spec (CommRingCat.of k)} {I I' : X.IdealSheafData}
    {E E' : List X.IdealSheafData} (hp : p = p') (hI : I = I') (hE : E = E') :
    @MarkedIdealWithBoundary.mk k instk X p I m E = @MarkedIdealWithBoundary.mk k instk X p' I' m E' := by
  subst hp
  subst hI
  subst hE
  rfl

abbrev MarkedIdealWithBoundary.krullDimSucc (T : MarkedIdealWithBoundary.{u}) : ℕ := EmbeddedResolution.krullDimSucc T.scheme

structure MarkedIdealWithBoundary.IsAdmissible (T : MarkedIdealWithBoundary.{u}) : Prop where
  charZero : CharZero T.base
  locallyOfFiniteType : LocallyOfFiniteType T.structMap
  nonzeroOnComponents : NonzeroOnComponents T.ideal
  one_le_mult : 1 ≤ T.mult
  quasiCompact : QuasiCompact T.structMap
  smooth : Smooth T.structMap
  snc : InStrictNormalCrossingPosition T.structMap T.boundary

structure MarkedSequenceOfBlowups {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) extends SequenceOfBlowups X where
  ideal : ∀ i : ℕ, (toSequenceOfBlowups.schemeAt i).IdealSheafData
  boundary : ∀ i : ℕ, List (toSequenceOfBlowups.schemeAt i).IdealSheafData
  ideal_zero : ideal 0 = I.comap toSequenceOfBlowups.isoZero.hom
  boundary_zero : boundary 0 = E.map (fun D => D.comap toSequenceOfBlowups.isoZero.hom)
  center_smooth : ∀ i, i < toSequenceOfBlowups.length →
    Smooth
      ((toSequenceOfBlowups.center i).subschemeι ≫ toSequenceOfBlowups.projectionToBase i ≫ p)
  center_snc : ∀ i, i < toSequenceOfBlowups.length →
    HasStrictNormalCrossingsWith (toSequenceOfBlowups.projectionToBase i ≫ p) (toSequenceOfBlowups.center i) (boundary i)
  center_order : ∀ i, i < toSequenceOfBlowups.length →
    ((toSequenceOfBlowups.center i).support : Set ↥(toSequenceOfBlowups.schemeAt i)) ⊆ orderAtLeastLocus (ideal i) m
  ideal_succ : ∀ i, i < toSequenceOfBlowups.length →
    Blowup.exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i) ^ m * ideal (i + 1) =
      (ideal i).comap (toSequenceOfBlowups.transitionMapSucc i)
  boundary_succ : ∀ i, i < toSequenceOfBlowups.length →
    boundary (i + 1) =
      (boundary i).map (Blowup.strictTransform (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i)) ++
        [Blowup.exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i)]

namespace MarkedSequenceOfBlowups

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def projectionToSpec (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    s.toSequenceOfBlowups.schemeAt i ⟶ Spec (CommRingCat.of k) :=
  s.toSequenceOfBlowups.projectionToBase i ≫ p

theorem projectionToSpec_eq (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    s.projectionToSpec i = s.toSequenceOfBlowups.projectionToBase i ≫ p := rfl

def exceptionalDivisor (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (s.toSequenceOfBlowups.schemeAt (i + 1)).IdealSheafData :=
  Blowup.exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i)

theorem exceptionalDivisor_eq (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    s.exceptionalDivisor i = (s.toSequenceOfBlowups.center i).comap (s.toSequenceOfBlowups.transitionMapSucc i) := rfl

def lastIdeal (s : MarkedSequenceOfBlowups p I m E) :
    (s.toSequenceOfBlowups.schemeAt s.toSequenceOfBlowups.length).IdealSheafData :=
  s.ideal s.toSequenceOfBlowups.length

theorem lastIdeal_eq (s : MarkedSequenceOfBlowups p I m E) :
    s.lastIdeal = s.ideal s.toSequenceOfBlowups.length := rfl

def IsResolution (s : MarkedSequenceOfBlowups p I m E) : Prop :=
  orderAtLeastLocus s.lastIdeal m = ∅

theorem isResolution_iff (s : MarkedSequenceOfBlowups p I m E) :
    s.IsResolution ↔ orderAtLeastLocus s.lastIdeal m = ∅ := Iff.rfl

end MarkedSequenceOfBlowups

def emptySequenceOfBlowups (X : Scheme.{u}) : SequenceOfBlowups X where
  length := 0
  tower := (CategoryTheory.Functor.const ℕᵒᵖ).obj X
  isoZero := Iso.refl X
  center := fun _ => ⊥
  isBlowup := fun i hi => absurd hi (Nat.not_lt_zero i)

def emptyMarkedSequenceOfBlowups {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) : MarkedSequenceOfBlowups p I m E where
  toSequenceOfBlowups := emptySequenceOfBlowups X
  ideal := fun _ => I.comap (emptySequenceOfBlowups X).isoZero.hom
  boundary := fun _ => E.map (fun D => D.comap (emptySequenceOfBlowups X).isoZero.hom)
  ideal_zero := rfl
  boundary_zero := rfl
  center_smooth := fun i hi => absurd hi (Nat.not_lt_zero i)
  center_snc := fun i hi => absurd hi (Nat.not_lt_zero i)
  center_order := fun i hi => absurd hi (Nat.not_lt_zero i)
  ideal_succ := fun i hi => absurd hi (Nat.not_lt_zero i)
  boundary_succ := fun i hi => absurd hi (Nat.not_lt_zero i)

theorem emptyMarkedSequenceOfBlowups_length {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) :
    (emptyMarkedSequenceOfBlowups p I m E).toSequenceOfBlowups.length = 0 := rfl

abbrev MarkedIdealWithBoundary.SequenceOfBlowups (T : MarkedIdealWithBoundary.{u}) : Type (u + 1) :=
  MarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary

def PrincipalizationAssignment : Type (u + 1) := ∀ T : MarkedIdealWithBoundary.{u}, T.SequenceOfBlowups

theorem PrincipalizationAssignment.toSequenceOfBlowups_heq_of_eq (L : PrincipalizationAssignment.{u})
    {T T' : MarkedIdealWithBoundary.{u}} (h : T = T') :
    HEq (L T).toSequenceOfBlowups (L T').toSequenceOfBlowups := by
  subst h
  rfl

def trivialPrincipalizationAssignment : PrincipalizationAssignment.{u} :=
  fun (T : MarkedIdealWithBoundary.{u}) => emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary

structure OrderReductionData : Type (u + 1) where
  maxOrderRed : PrincipalizationAssignment.{u}
  orderRed : PrincipalizationAssignment.{u}

def trivialOrderReductionData : OrderReductionData.{u} where
  maxOrderRed := trivialPrincipalizationAssignment
  orderRed := trivialPrincipalizationAssignment

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def HasReducedCenters (s : MarkedSequenceOfBlowups p I m E) : Prop :=
  ∀ i, i < s.toSequenceOfBlowups.length → ∀ J : (s.toSequenceOfBlowups.schemeAt i).IdealSheafData,
    ((s.toSequenceOfBlowups.center i).support : Set ↥(s.toSequenceOfBlowups.schemeAt i)) ⊆
        (J.support : Set ↥(s.toSequenceOfBlowups.schemeAt i)) →
      J ≤ s.toSequenceOfBlowups.center i

section
variable (s : MarkedSequenceOfBlowups p I m E)

theorem markedSequenceOfBlowups_ideal_zero :
    s.ideal 0 = I.comap (s.toSequenceOfBlowups.projectionToBase 0) := by
  rw [s.ideal_zero, s.toSequenceOfBlowups.projectionToBase_zero]

theorem markedSequenceOfBlowups_boundary_zero :
    s.boundary 0 = E.map (fun D => D.comap (s.toSequenceOfBlowups.projectionToBase 0)) := by
  rw [s.boundary_zero, s.toSequenceOfBlowups.projectionToBase_zero]


end

section
variable (s : MarkedSequenceOfBlowups p I 1 E)

theorem markedSequenceOfBlowups_exceptionalIdeal_mul_ideal_succ (i : ℕ)
    (h : i < s.toSequenceOfBlowups.length) :
    Blowup.exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i) * s.ideal (i + 1) =
      (s.ideal i).comap (s.toSequenceOfBlowups.transitionMapSucc i) := by
  have hs := s.ideal_succ i h
  rwa [pow_one] at hs

theorem markedSequenceOfBlowups_ideal_vanishesAlong_center (hmax : HasReducedCenters s) (i : ℕ) (h : i < s.toSequenceOfBlowups.length) :
    VanishesAlong (s.ideal i) (s.toSequenceOfBlowups.center i) := by
  rw [vanishesAlong_iff_le]
  refine hmax i h (s.ideal i) ?_
  intro x hx
  have hx' := s.center_order i h hx
  rw [mem_orderAtLeastLocus_one_iff] at hx'
  exact hx'


end

def MarkedSequenceOfBlowups.toIdealBlowupSequence (s : MarkedSequenceOfBlowups p I 1 E) (hmax : HasReducedCenters s) :
    IdealBlowupSequence p I E where
  toSequenceOfBlowups := s.toSequenceOfBlowups
  ideal := s.ideal
  boundary := s.boundary
  ideal_zero := markedSequenceOfBlowups_ideal_zero s
  boundary_zero := markedSequenceOfBlowups_boundary_zero s
  center_smooth := s.center_smooth
  center_snc := s.center_snc
  ideal_vanishes := fun i h => markedSequenceOfBlowups_ideal_vanishesAlong_center s hmax i h
  ideal_succ := fun i h => markedSequenceOfBlowups_exceptionalIdeal_mul_ideal_succ s i h
  boundary_succ := s.boundary_succ

@[simp]
theorem MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups (s : MarkedSequenceOfBlowups p I 1 E)
    (hmax : HasReducedCenters s) :
    (s.toIdealBlowupSequence hmax).toSequenceOfBlowups = s.toSequenceOfBlowups := rfl

@[simp]
theorem MarkedSequenceOfBlowups.toMarkedSequence_lastIdeal (s : MarkedSequenceOfBlowups p I 1 E)
    (hmax : HasReducedCenters s) :
    (s.toIdealBlowupSequence hmax).lastIdeal = s.lastIdeal := rfl

end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
section

open Opposite

section
namespace FunctorialResolution.EmbeddedResolution

structure BlowupSequenceData (X : Scheme.{u}) : Type (u + 1) where
  length : ℕ
  obj : ℕ → Scheme.{u}
  map : ∀ i : ℕ, obj (i + 1) ⟶ obj i
  isoZero : obj 0 ≅ X
  center : ∀ i : ℕ, (obj i).IdealSheafData
  isBlowup : ∀ i, i < length → Blowup.IsBlowupAlongIdealSheaf (map i) (center i)

namespace BlowupSequenceData

variable {X : Scheme.{u}}

def projectionToBase (d : BlowupSequenceData X) : ∀ i : ℕ, d.obj i ⟶ X
  | 0 => d.isoZero.hom
  | (i + 1) => d.map i ≫ projectionToBase d i

@[simp]
theorem projectionToBase_zero (d : BlowupSequenceData X) : projectionToBase d 0 = d.isoZero.hom := rfl

@[simp]
theorem projectionToBase_succ (d : BlowupSequenceData X) (i : ℕ) :
    projectionToBase d (i + 1) = d.map i ≫ projectionToBase d i := rfl

private def homAdd_consolidated133 (d : BlowupSequenceData X) (i : ℕ) : ∀ k : ℕ, d.obj (i + k) ⟶ d.obj i
  | 0 => 𝟙 (d.obj i)
  | (k + 1) => d.map (i + k) ≫ homAdd_consolidated133 d i k

private def homOfLE_consolidated133 (d : BlowupSequenceData X) {i j : ℕ} (h : i ≤ j) : d.obj j ⟶ d.obj i :=
  eqToHom (congrArg d.obj (Nat.add_sub_cancel' h).symm) ≫ homAdd_consolidated133 d i (j - i)

section
variable (d : BlowupSequenceData X)

private theorem eqToHom_comp_iteratedBlowupMorphism_of_eq_zero_consolidated133 (i k : ℕ)
    (h : d.obj i = d.obj (i + k)) (hk : k = 0) :
    eqToHom h ≫ homAdd_consolidated133 d i k = 𝟙 (d.obj i) := by
  subst hk
  have h1 : homAdd_consolidated133 d i 0 = 𝟙 (d.obj i) := rfl
  have h2 : eqToHom h = 𝟙 (d.obj i) := rfl
  rw [h1, h2]
  exact Category.id_comp (𝟙 (d.obj i))

private theorem towerMorphism_refl_consolidated133 (i : ℕ) :
    homOfLE_consolidated133 d (le_refl i) = 𝟙 (d.obj i) :=
  eqToHom_comp_iteratedBlowupMorphism_of_eq_zero_consolidated133 d i (i - i)
    (congrArg d.obj (Nat.add_sub_cancel' (le_refl i)).symm) (Nat.sub_self i)

private theorem iteratedBlowupMorphism_zero_consolidated133 (i : ℕ) :
    homAdd_consolidated133 d i 0 = 𝟙 (d.obj i) := rfl

private theorem iteratedBlowupMorphism_succ_consolidated133 (i k : ℕ) :
    homAdd_consolidated133 d i (k + 1) = d.map (i + k) ≫ homAdd_consolidated133 d i k := rfl

private theorem blowupMorphism_comp_eqToHom_consolidated133 {n m : ℕ} (h : n = m) :
    d.map n ≫ eqToHom (congrArg d.obj h) =
      eqToHom (show d.obj (n + 1) = d.obj (m + 1) by rw [h]) ≫ d.map m := by
  subst h
  simp

private theorem iteratedBlowupMorphism_congr_length_consolidated133 (i : ℕ) {k k' : ℕ} (h : k = k') :
    homAdd_consolidated133 d i k =
      eqToHom (show d.obj (i + k) = d.obj (i + k') by rw [h]) ≫ homAdd_consolidated133 d i k' := by
  subst h
  simp

private theorem iteratedBlowupMorphism_congr_start_consolidated133 {i i' : ℕ} (h : i = i') (k : ℕ) :
    homAdd_consolidated133 d i k =
      eqToHom (show d.obj (i + k) = d.obj (i' + k) by rw [h]) ≫ homAdd_consolidated133 d i' k ≫
        eqToHom (show d.obj i' = d.obj i by rw [h]) := by
  subst h
  simp

private theorem iteratedBlowupMorphism_comp_iteratedBlowupMorphism_consolidated133 (i a b : ℕ) :
    homAdd_consolidated133 d (i + a) b ≫ homAdd_consolidated133 d i a =
      eqToHom (congrArg d.obj (Nat.add_assoc i a b)) ≫ homAdd_consolidated133 d i (a + b) := by
  induction b with
  | zero =>
      show homAdd_consolidated133 d (i + a) 0 ≫ homAdd_consolidated133 d i a
          = eqToHom (rfl : d.obj (i + a) = d.obj (i + a)) ≫ homAdd_consolidated133 d i a
      rw [iteratedBlowupMorphism_zero_consolidated133, eqToHom_refl, Category.id_comp]
      exact Category.id_comp _
  | succ b ih =>
      rw [iteratedBlowupMorphism_succ_consolidated133, Category.assoc, ih, ← Category.assoc,
        blowupMorphism_comp_eqToHom_consolidated133 d (Nat.add_assoc i a b), Category.assoc]
      rfl

private theorem towerMorphism_eq_iteratedBlowupMorphism_consolidated133 {i j : ℕ} (h : i ≤ j) (k : ℕ)
    (hk : j = i + k) :
    homOfLE_consolidated133 d h = eqToHom (congrArg d.obj hk) ≫ homAdd_consolidated133 d i k := by
  subst hk
  unfold homOfLE_consolidated133
  rw [iteratedBlowupMorphism_congr_length_consolidated133 d i (show i + k - i = k by omega)]
  simp

private theorem towerMorphism_comp_consolidated133 {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) :
    homOfLE_consolidated133 d hjl ≫ homOfLE_consolidated133 d hij = homOfLE_consolidated133 d (hij.trans hjl) := by
  rw [towerMorphism_eq_iteratedBlowupMorphism_consolidated133 d hjl (l - j) (by omega), towerMorphism_eq_iteratedBlowupMorphism_consolidated133 d hij (j - i) (by omega),
    towerMorphism_eq_iteratedBlowupMorphism_consolidated133 d (hij.trans hjl) ((j - i) + (l - j)) (by omega),
    iteratedBlowupMorphism_congr_start_consolidated133 d (show j = i + (j - i) by omega) (l - j)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [iteratedBlowupMorphism_comp_iteratedBlowupMorphism_consolidated133 d i (j - i) (l - j)]
  simp


end

def tower (d : BlowupSequenceData X) : ℕᵒᵖ ⥤ Scheme.{u} where
  obj n := d.obj n.unop
  map f := homOfLE_consolidated133 d (leOfHom f.unop)
  map_id n := towerMorphism_refl_consolidated133 d n.unop
  map_comp f g := (towerMorphism_comp_consolidated133 d (leOfHom g.unop) (leOfHom f.unop)).symm

@[simp]
theorem tower_obj (d : BlowupSequenceData X) (i : ℕ) : d.tower.obj (op i) = d.obj i := rfl

section
variable (d : BlowupSequenceData X) (i : ℕ)

private theorem iteratedBlowupMorphism_one_consolidated133 :
    homAdd_consolidated133 d i 1 = d.map i := by
  show d.map (i + 0) ≫ homAdd_consolidated133 d i 0 = d.map i
  exact Category.comp_id _

private theorem eqToHom_comp_iteratedBlowupMorphism_consolidated133 {k k' : ℕ} (h : k = k')
    (hobj : d.obj (i + k) = d.obj (i + k')) :
    eqToHom hobj ≫ homAdd_consolidated133 d i k' = homAdd_consolidated133 d i k := by
  subst h
  simp

private theorem towerMorphism_succ_consolidated133 (h : i ≤ i + 1) :
    homOfLE_consolidated133 d h = d.map i := by
  have h1 : i + 1 - i = 1 := by omega
  have h2 := eqToHom_comp_iteratedBlowupMorphism_consolidated133 d i h1
    (show d.obj (i + (i + 1 - i)) = d.obj (i + 1) by rw [h1])
  unfold homOfLE_consolidated133
  rw [← h2, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  exact iteratedBlowupMorphism_one_consolidated133 d i


end

@[simp]
theorem tower_map_succ (d : BlowupSequenceData X) (i : ℕ) :
    d.tower.map (CategoryTheory.homOfLE (Nat.le_succ i)).op = d.map i :=
  towerMorphism_succ_consolidated133 d i (Nat.le_succ i)

theorem isBlowupAlongIdealSheaf_tower_map (d : BlowupSequenceData X) (i : ℕ) (hi : i < d.length) :
    Blowup.IsBlowupAlongIdealSheaf (d.tower.map (CategoryTheory.homOfLE (Nat.le_succ i)).op) (d.center i) := by
  have h := d.isBlowup i hi
  rw [tower_map_succ]
  exact h

def toSequenceOfBlowups (d : BlowupSequenceData X) : SequenceOfBlowups X where
  length := d.length
  tower := d.tower
  isoZero := d.isoZero
  center := d.center
  isBlowup := fun i hi => isBlowupAlongIdealSheaf_tower_map d i hi

@[simp]
theorem toSequenceOfBlowups_length (d : BlowupSequenceData X) : d.toSequenceOfBlowups.length = d.length := rfl

@[simp]
theorem toSequenceOfBlowups_tower (d : BlowupSequenceData X) : d.toSequenceOfBlowups.tower = d.tower := rfl

theorem toSequenceOfBlowups_schemeAt (d : BlowupSequenceData X) (i : ℕ) : d.toSequenceOfBlowups.schemeAt i = d.obj i := rfl

@[simp]
theorem toSequenceOfBlowups_center (d : BlowupSequenceData X) (i : ℕ) : d.toSequenceOfBlowups.center i = d.center i := rfl

@[simp]
theorem toSequenceOfBlowups_isoObjZero (d : BlowupSequenceData X) : d.toSequenceOfBlowups.isoZero = d.isoZero := rfl

@[simp]
theorem toSequenceOfBlowups_blowupMorphism (d : BlowupSequenceData X) (i : ℕ) : d.toSequenceOfBlowups.transitionMapSucc i = d.map i :=
  tower_map_succ d i

@[simp]
theorem toSequenceOfBlowups_projectionToBase (d : BlowupSequenceData X) (i : ℕ) : d.toSequenceOfBlowups.projectionToBase i = projectionToBase d i := by
  induction i with
  | zero =>
      have h0 : d.toSequenceOfBlowups.transitionMap (Nat.zero_le 0) = 𝟙 (d.toSequenceOfBlowups.schemeAt 0) :=
        d.toSequenceOfBlowups.tower.map_id (op 0)
      have h1 : d.toSequenceOfBlowups.projectionToBase 0 = d.toSequenceOfBlowups.transitionMap (Nat.zero_le 0) ≫ d.toSequenceOfBlowups.isoZero.hom :=
        SequenceOfBlowups.projectionToBase_def d.toSequenceOfBlowups 0
      have h2 : d.toSequenceOfBlowups.projectionToBase 0 = d.toSequenceOfBlowups.isoZero.hom := by
        rw [h1, h0, Category.id_comp]
      exact h2
  | succ j ih =>
      have h2 : d.toSequenceOfBlowups.transitionMap (Nat.le_succ j) = d.map j :=
        (SequenceOfBlowups.transitionMap_def d.toSequenceOfBlowups (Nat.le_succ j)).trans (tower_map_succ d j)
      have h3 : d.toSequenceOfBlowups.transitionMap (Nat.le_succ j) ≫ d.toSequenceOfBlowups.projectionToBase j
          = d.toSequenceOfBlowups.projectionToBase (j + 1) :=
        SequenceOfBlowups.transitionMap_comp_projectionToBase d.toSequenceOfBlowups (Nat.le_succ j)
      have h5 : d.toSequenceOfBlowups.transitionMap (Nat.le_succ j) ≫ d.toSequenceOfBlowups.projectionToBase j
          = d.map j ≫ projectionToBase d j := by
        rw [h2, ih]
        exact rfl
      exact h3.symm.trans h5

def ofSequenceOfBlowups (s : SequenceOfBlowups X) : BlowupSequenceData X where
  length := s.length
  obj := s.schemeAt
  map := s.transitionMapSucc
  isoZero := s.isoZero
  center := s.center
  isBlowup := fun i hi => s.isBlowupAlongIdealSheaf_blowupMorphism i hi

@[simp]
theorem ofSequenceOfBlowups_length (s : SequenceOfBlowups X) : (ofSequenceOfBlowups s).length = s.length := rfl

@[simp]
theorem ofSequenceOfBlowups_schemeAt (s : SequenceOfBlowups X) (i : ℕ) : (ofSequenceOfBlowups s).obj i = s.schemeAt i := rfl

@[simp]
theorem ofSequenceOfBlowups_blowupMorphism (s : SequenceOfBlowups X) (i : ℕ) : (ofSequenceOfBlowups s).map i = s.transitionMapSucc i := rfl

@[simp]
theorem ofSequenceOfBlowups_center (s : SequenceOfBlowups X) (i : ℕ) : (ofSequenceOfBlowups s).center i = s.center i := rfl

@[simp]
theorem ofSequenceOfBlowups_isoObjZero (s : SequenceOfBlowups X) : (ofSequenceOfBlowups s).isoZero = s.isoZero := rfl

theorem ofSequenceOfBlowups_projectionToBase (s : SequenceOfBlowups X) (i : ℕ) : projectionToBase (ofSequenceOfBlowups s) i = s.projectionToBase i := by
  induction i with
  | zero =>
    have h1 : s.tower.map (CategoryTheory.homOfLE (le_refl (0 : ℕ))).op = 𝟙 (s.tower.obj (Opposite.op 0)) :=
      s.tower.map_id (Opposite.op 0)
    have h2 : s.projectionToBase 0 = s.isoZero.hom := by
      rw [SequenceOfBlowups.projectionToBase_def, SequenceOfBlowups.transitionMap_def, h1, Category.id_comp]
    exact h2.symm
  | succ i ih =>
    show (ofSequenceOfBlowups s).map i ≫ projectionToBase (ofSequenceOfBlowups s) i = s.projectionToBase (i + 1)
    rw [ih]
    show s.transitionMapSucc i ≫ s.projectionToBase i = s.projectionToBase (i + 1)
    rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_comp_projectionToBase]

end BlowupSequenceData

def emptyBlowupSequenceData (X : Scheme.{u}) : BlowupSequenceData X where
  length := 0
  obj := fun _ => X
  map := fun _ => 𝟙 X
  isoZero := Iso.refl X
  center := fun _ => ⊤
  isBlowup := fun i hi => absurd hi (Nat.not_lt_zero i)

@[simp]
theorem emptyBlowupSequenceData_length (X : Scheme.{u}) : (emptyBlowupSequenceData X).length = 0 := rfl

@[simp]
theorem emptyBlowupSequenceData_schemeAt (X : Scheme.{u}) (i : ℕ) : (emptyBlowupSequenceData X).obj i = X := rfl

@[simp]
theorem emptyBlowupSequenceData_blowupMorphism (X : Scheme.{u}) (i : ℕ) : (emptyBlowupSequenceData X).map i = 𝟙 X := rfl

@[simp]
theorem emptyBlowupSequenceData_center (X : Scheme.{u}) (i : ℕ) : (emptyBlowupSequenceData X).center i = ⊤ := rfl

@[simp]
theorem emptyBlowupSequenceData_isoObjZero (X : Scheme.{u}) :
    (emptyBlowupSequenceData X).isoZero = Iso.refl X := rfl

structure MarkedBlowupSequenceData {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) extends BlowupSequenceData X where
  proj : ∀ i : ℕ, toBlowupSequenceData.obj i ⟶ X
  proj_zero : proj 0 = toBlowupSequenceData.isoZero.hom
  proj_succ : ∀ i : ℕ, proj (i + 1) = toBlowupSequenceData.map i ≫ proj i
  ideal : ∀ i : ℕ, (toBlowupSequenceData.obj i).IdealSheafData
  boundary : ∀ i : ℕ, List (toBlowupSequenceData.obj i).IdealSheafData
  ideal_zero : ideal 0 = I.comap toBlowupSequenceData.isoZero.hom
  boundary_zero : boundary 0 = E.map (fun D => D.comap toBlowupSequenceData.isoZero.hom)
  center_order : ∀ i, i < toBlowupSequenceData.length →
    ((toBlowupSequenceData.center i).support : Set ↥(toBlowupSequenceData.obj i)) ⊆ orderAtLeastLocus (ideal i) m
  center_smooth : ∀ i, i < toBlowupSequenceData.length →
    Smooth ((toBlowupSequenceData.center i).subschemeι ≫ proj i ≫ p)
  center_snc : ∀ i, i < toBlowupSequenceData.length →
    HasStrictNormalCrossingsWith (proj i ≫ p) (toBlowupSequenceData.center i) (boundary i)
  ideal_succ : ∀ i, i < toBlowupSequenceData.length →
    Blowup.exceptionalIdeal (toBlowupSequenceData.map i) (toBlowupSequenceData.center i) ^ m * ideal (i + 1) =
      (ideal i).comap (toBlowupSequenceData.map i)
  boundary_succ : ∀ i, i < toBlowupSequenceData.length →
    boundary (i + 1) =
      (boundary i).map (Blowup.strictTransform (toBlowupSequenceData.map i) (toBlowupSequenceData.center i)) ++
        [Blowup.exceptionalIdeal (toBlowupSequenceData.map i) (toBlowupSequenceData.center i)]

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

section
variable (d : MarkedBlowupSequenceData p I m E) (i : ℕ)

theorem projectionToBase_eq :
    d.proj i = BlowupSequenceData.projectionToBase d.toBlowupSequenceData i := by
  induction i with
  | zero =>
      rw [BlowupSequenceData.projectionToBase_zero]
      exact d.proj_zero
  | succ i ih =>
      rw [d.proj_succ i, BlowupSequenceData.projectionToBase_succ, ih]

theorem projectionToBase_eq_toSequenceOfBlowups :
    d.proj i = d.toBlowupSequenceData.toSequenceOfBlowups.projectionToBase i :=
  (d.projectionToBase_eq i).trans (BlowupSequenceData.toSequenceOfBlowups_projectionToBase d.toBlowupSequenceData i).symm


end

section
variable (d : MarkedBlowupSequenceData p I m E) (i : ℕ) (hi : i < d.toBlowupSequenceData.length)
include hi

private theorem center_support_subset_orderAtLeastLocus_consolidated133 :
    ((d.toBlowupSequenceData.center i).support : Set ↥(d.toBlowupSequenceData.obj i)) ⊆
      orderAtLeastLocus (d.ideal i) m :=
  d.center_order i hi

private theorem smooth_center_comp_projection_consolidated133 :
    Smooth
      ((d.toBlowupSequenceData.center i).subschemeι ≫ d.toBlowupSequenceData.toSequenceOfBlowups.projectionToBase i ≫ p) := by
  have h := d.center_smooth i hi
  rw [projectionToBase_eq_toSequenceOfBlowups d i] at h
  exact h

private theorem hasStrictNormalCrossingsWith_center_boundary_consolidated133 :
    HasStrictNormalCrossingsWith (d.toBlowupSequenceData.toSequenceOfBlowups.projectionToBase i ≫ p) (d.toBlowupSequenceData.center i)
      (d.boundary i) := by
  have h := d.center_snc i hi
  rw [d.projectionToBase_eq_toSequenceOfBlowups i] at h
  exact h

private theorem exceptionalIdeal_pow_mul_ideal_succ_eq_comap_consolidated133 :
    Blowup.exceptionalIdeal (d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i)
          (show (d.toBlowupSequenceData.toSequenceOfBlowups.schemeAt i).IdealSheafData from d.toBlowupSequenceData.center i) ^ m *
        (show (d.toBlowupSequenceData.toSequenceOfBlowups.schemeAt (i + 1)).IdealSheafData from d.ideal (i + 1)) =
      (show (d.toBlowupSequenceData.toSequenceOfBlowups.schemeAt i).IdealSheafData from d.ideal i).comap
        (d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i) := by
  have key := d.ideal_succ i hi
  have h : d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i = d.toBlowupSequenceData.map i :=
    BlowupSequenceData.toSequenceOfBlowups_blowupMorphism d.toBlowupSequenceData i
  rw [h]
  exact key

private theorem boundary_succ_eq_map_strictTransform_append_consolidated133 :
    d.boundary (i + 1) =
      (d.boundary i).map
          (Blowup.strictTransform (d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i) (d.toBlowupSequenceData.center i)) ++
        [Blowup.exceptionalIdeal (d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i) (d.toBlowupSequenceData.center i)] := by
  have key := d.boundary_succ i hi
  have h : d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i = d.toBlowupSequenceData.map i :=
    BlowupSequenceData.toSequenceOfBlowups_blowupMorphism d.toBlowupSequenceData i
  rw [h]
  exact key


end

def toMarkedSequenceOfBlowups (d : MarkedBlowupSequenceData p I m E) : MarkedSequenceOfBlowups p I m E where
  toSequenceOfBlowups := d.toBlowupSequenceData.toSequenceOfBlowups
  ideal := d.ideal
  boundary := d.boundary
  ideal_zero := d.ideal_zero
  boundary_zero := d.boundary_zero
  center_smooth := fun i hi => smooth_center_comp_projection_consolidated133 d i hi
  center_snc := fun i hi => hasStrictNormalCrossingsWith_center_boundary_consolidated133 d i hi
  center_order := fun i hi => center_support_subset_orderAtLeastLocus_consolidated133 d i hi
  ideal_succ := fun i hi => exceptionalIdeal_pow_mul_ideal_succ_eq_comap_consolidated133 d i hi
  boundary_succ := fun i hi => boundary_succ_eq_map_strictTransform_append_consolidated133 d i hi

@[simp]
theorem toMarkedSequence_toSequenceOfBlowups (d : MarkedBlowupSequenceData p I m E) :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups = d.toBlowupSequenceData.toSequenceOfBlowups := rfl

@[simp]
theorem toMarkedSequence_length (d : MarkedBlowupSequenceData p I m E) :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length = d.toBlowupSequenceData.length := rfl

theorem toMarkedSequence_schemeAt (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.schemeAt i = d.toBlowupSequenceData.obj i := rfl

@[simp]
theorem toMarkedSequence_ideal (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.ideal i = d.ideal i := rfl

@[simp]
theorem toMarkedSequence_boundary (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.boundary i = d.boundary i := rfl

@[simp]
theorem toMarkedSequence_center (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.center i = d.toBlowupSequenceData.center i := rfl

section
variable (d : MarkedBlowupSequenceData p I m E) (i : ℕ)

theorem toMarkedSequence_blowupMorphism :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.transitionMapSucc i = d.toBlowupSequenceData.map i :=
  BlowupSequenceData.toSequenceOfBlowups_blowupMorphism d.toBlowupSequenceData i

theorem toMarkedSequence_projectionToBase :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase i = d.proj i :=
  (BlowupSequenceData.toSequenceOfBlowups_projectionToBase d.toBlowupSequenceData i).trans (d.projectionToBase_eq i).symm


end

@[simp]
theorem toMarkedSequence_projectionToSpec (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.projectionToSpec i = d.proj i ≫ p := by
  rw [MarkedSequenceOfBlowups.projectionToSpec_eq, toMarkedSequence_projectionToBase]
  rfl

@[simp]
theorem toMarkedSequence_lastIdeal (d : MarkedBlowupSequenceData p I m E) :
    d.toMarkedSequenceOfBlowups.lastIdeal = d.ideal d.toBlowupSequenceData.length := rfl

section
variable (s : MarkedSequenceOfBlowups p I m E)

private theorem toSequenceOfBlowups_projectionToBase_zero_consolidated133 :
    s.toSequenceOfBlowups.projectionToBase 0 = (BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups).isoZero.hom := by
  have h1 : s.toSequenceOfBlowups.tower.map (homOfLE (le_refl (0 : ℕ))).op
      = 𝟙 (s.toSequenceOfBlowups.tower.obj (Opposite.op 0)) :=
    s.toSequenceOfBlowups.tower.map_id (Opposite.op 0)
  show s.toSequenceOfBlowups.projectionToBase 0 = s.toSequenceOfBlowups.isoZero.hom
  rw [SequenceOfBlowups.projectionToBase_def, SequenceOfBlowups.transitionMap_def, h1, Category.id_comp]

private theorem toSequenceOfBlowups_projectionToBase_succ_consolidated133 (i : ℕ) :
    s.toSequenceOfBlowups.projectionToBase (i + 1) =
      (BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups).map i ≫ s.toSequenceOfBlowups.projectionToBase i := by
  show s.toSequenceOfBlowups.projectionToBase (i + 1)
      = s.toSequenceOfBlowups.transitionMapSucc i ≫ s.toSequenceOfBlowups.projectionToBase i
  rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_comp_projectionToBase]


end

def ofMarkedSequence (s : MarkedSequenceOfBlowups p I m E) : MarkedBlowupSequenceData p I m E where
  toBlowupSequenceData := BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups
  proj := fun i => s.toSequenceOfBlowups.projectionToBase i
  proj_zero := toSequenceOfBlowups_projectionToBase_zero_consolidated133 s
  proj_succ := fun i => toSequenceOfBlowups_projectionToBase_succ_consolidated133 s i
  ideal := s.ideal
  boundary := s.boundary
  ideal_zero := s.ideal_zero
  boundary_zero := s.boundary_zero
  center_order := fun i hi => s.center_order i hi
  center_smooth := fun i hi => s.center_smooth i hi
  center_snc := fun i hi => s.center_snc i hi
  ideal_succ := fun i hi => s.ideal_succ i hi
  boundary_succ := fun i hi => s.boundary_succ i hi

@[simp]
theorem blowupSequenceData_ofMarkedSequence (s : MarkedSequenceOfBlowups p I m E) :
    (ofMarkedSequence s).toBlowupSequenceData = BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups := rfl

@[simp]
theorem ofMarkedSequence_length (s : MarkedSequenceOfBlowups p I m E) :
    (ofMarkedSequence s).toBlowupSequenceData.length = s.toSequenceOfBlowups.length := rfl

@[simp]
theorem ofMarkedSequence_projectionToBase (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (ofMarkedSequence s).proj i = s.toSequenceOfBlowups.projectionToBase i := rfl

@[simp]
theorem ofMarkedSequence_blowupMorphism (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (ofMarkedSequence s).toBlowupSequenceData.map i = s.toSequenceOfBlowups.transitionMapSucc i := rfl

@[simp]
theorem ofMarkedSequence_ideal (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (ofMarkedSequence s).ideal i = s.ideal i := rfl

@[simp]
theorem ofMarkedSequence_boundary_apply (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (ofMarkedSequence s).boundary i = s.boundary i := rfl

@[simp]
theorem ofMarkedSequence_center (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (ofMarkedSequence s).toBlowupSequenceData.center i = s.toSequenceOfBlowups.center i := rfl

end MarkedBlowupSequenceData

def emptyMarkedBlowupSequenceData {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) : MarkedBlowupSequenceData p I m E where
  toBlowupSequenceData := emptyBlowupSequenceData X
  proj := fun _ => 𝟙 X
  proj_zero := rfl
  proj_succ := fun _ => (Category.id_comp _).symm
  ideal := fun _ => I
  boundary := fun _ => E
  ideal_zero := (Scheme.IdealSheafData.comap_id I).symm
  boundary_zero := by simp [Scheme.IdealSheafData.comap_id]
  center_order := fun i hi => absurd hi (Nat.not_lt_zero i)
  center_smooth := fun i hi => absurd hi (Nat.not_lt_zero i)
  center_snc := fun i hi => absurd hi (Nat.not_lt_zero i)
  ideal_succ := fun i hi => absurd hi (Nat.not_lt_zero i)
  boundary_succ := fun i hi => absurd hi (Nat.not_lt_zero i)

@[simp]
theorem emptyMarkedBlowupSequenceData_toBlowupSequenceData_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) :
    (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData = emptyBlowupSequenceData X := rfl

@[simp]
theorem emptyMarkedBlowupSequenceData_length {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) :
    (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length = 0 := rfl

@[simp]
theorem emptyMarkedBlowupSequenceData_schemeAt {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (i : ℕ) :
    (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.obj i = X := rfl

@[simp]
theorem emptyMarkedBlowupSequenceData_center {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (i : ℕ) :
    (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.center i = ⊤ := rfl

@[simp]
theorem emptyMarkedBlowupSequenceData_projectionToBase {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (i : ℕ) :
    (emptyMarkedBlowupSequenceData p I m E).proj i = 𝟙 X := rfl

@[simp]
theorem emptyMarkedBlowupSequenceData_ideal {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (i : ℕ) :
    (emptyMarkedBlowupSequenceData p I m E).ideal i = I := rfl

@[simp]
theorem emptyMarkedBlowupSequenceData_boundary {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (i : ℕ) :
    (emptyMarkedBlowupSequenceData p I m E).boundary i = E := rfl

@[simp]
theorem emptyMarkedBlowupSequenceData_toMarkedSequence_length {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) :
    (emptyMarkedBlowupSequenceData p I m E).toMarkedSequenceOfBlowups.toSequenceOfBlowups.length = 0 := rfl

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
section

open TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

def BlowupPreservesNoetherian : Prop :=
  ∀ (X X' : Scheme.{u}) [IsNoetherian X] (π : X' ⟶ X)
    (Z : X.IdealSheafData), Blowup.IsBlowupAlongIdealSheaf π Z → IsNoetherian X'

structure AmbientEmbedding {S : Scheme.{u}} (s : BlowupSequenceData S) (n : ℕ) : Type (u + 1) where
  ambient : Scheme.{u}
  emb : s.obj n ⟶ ambient
  emb_isClosedImmersion : IsClosedImmersion emb
  isNoetherian_ambient_of_le_length : n ≤ s.length → IsNoetherian ambient

private theorem isClosedImmersion_isoObjZero_hom_comp_consolidated211 {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] (s : BlowupSequenceData S) :
    IsClosedImmersion (s.isoZero.hom ≫ ι) := by
  have : IsClosedImmersion s.isoZero.hom := inferInstance
  infer_instance

private theorem isNoetherian_blowup_of_isNoetherian_consolidated211 (hno : BlowupPreservesNoetherian.{u})
    {A : Scheme.{u}} (hA : IsNoetherian A) (Z : A.IdealSheafData) :
    IsNoetherian (Blowup.blowup Z) := by
  have := hA
  exact hno A (Blowup.blowup Z) (Blowup.blowup.proj Z) Z (Blowup.blowup.isBlowupAlongIdealSheaf_proj Z)

section
variable {S' A : Scheme.{u}} (σ : S' ⟶ A)

private theorem comap_imageIdealSheaf_of_isClosedImmersion_consolidated211 [IsClosedImmersion σ] (J : S'.IdealSheafData) :
    (imageIdealSheaf σ J).comap σ = J := by
  have h : imageIdealSheaf σ J = J.map σ := rfl
  rw [h]
  exact Blowup.comap_map_of_isClosedImmersion σ J

private theorem preimage_support_subset_support_comap_consolidated211 (Z : A.IdealSheafData) :
    σ.base ⁻¹' (Z.support : Set ↥A) ⊆ ((Z.comap σ).support : Set ↥S') := by
  simp [Scheme.IdealSheafData.support_comap]


end

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
include hres

private theorem exists_closedImmersion_blowup_of_isBlowupAlongIdealSheaf_consolidated211 {S' A : Scheme.{u}} [IsLocallyNoetherian A] (σ : S' ⟶ A)
    [IsClosedImmersion σ] (J : S'.IdealSheafData) {S'' : Scheme.{u}}
    (f : S'' ⟶ S') (hf : Blowup.IsBlowupAlongIdealSheaf f J)
    (hc : ∀ T ∈ irreducibleComponents ↥S', ¬ T ⊆ (J.support : Set ↥S')) :
    ∃ τ : S'' ⟶ Blowup.blowup (imageIdealSheaf σ J),
      IsClosedImmersion τ ∧
      τ ≫ Blowup.blowup.proj (imageIdealSheaf σ J) = f ≫ σ ∧
      τ.ker = Blowup.strictTransform (Blowup.blowup.proj (imageIdealSheaf σ J)) (imageIdealSheaf σ J) σ.ker := by
  have hπ : Blowup.IsBlowupAlongIdealSheaf (Blowup.blowup.proj (imageIdealSheaf σ J)) (imageIdealSheaf σ J) :=
    Blowup.blowup.isBlowupAlongIdealSheaf_proj _
  have hcomap : (imageIdealSheaf σ J).comap σ = J := comap_imageIdealSheaf_of_isClosedImmersion_consolidated211 σ J
  have hsupp : ∀ T ∈ irreducibleComponents ↥S',
      ¬ (σ.base '' T) ⊆ ((imageIdealSheaf σ J).support : Set ↥A) := by
    intro T hT hsub
    refine hc T hT ?_
    have h2 := (Set.image_subset_iff.mp hsub).trans (preimage_support_subset_support_comap_consolidated211 σ (imageIdealSheaf σ J))
    rwa [hcomap] at h2
  obtain ⟨ψ, hψ1, hψ2⟩ := hres A (Blowup.blowup (imageIdealSheaf σ J)) S' σ
    (Blowup.blowup.proj (imageIdealSheaf σ J)) (imageIdealSheaf σ J) hπ hsupp
  rw [hcomap] at hψ2
  have hab : hψ2.lift f hf.1 ≫ ψ = f := hψ2.lift_comp f hf.1
  have hba : hf.lift ψ hψ2.1 ≫ f = ψ := hf.lift_comp ψ hψ2.1
  have hid1 : hψ2.lift f hf.1 ≫ hf.lift ψ hψ2.1 = 𝟙 S'' := by
    refine hf.hom_ext hf.1 ?_ (Category.id_comp f)
    rw [Category.assoc, hba, hab]
  have hid2 : hf.lift ψ hψ2.1 ≫ hψ2.lift f hf.1 = 𝟙 _ := by
    refine hψ2.hom_ext hψ2.1 ?_ (Category.id_comp ψ)
    rw [Category.assoc, hab, hba]
  have : IsIso (hψ2.lift f hf.1) := ⟨⟨hf.lift ψ hψ2.1, hid1, hid2⟩⟩
  refine ⟨hψ2.lift f hf.1 ≫
      (Blowup.strictTransform (Blowup.blowup.proj (imageIdealSheaf σ J)) (imageIdealSheaf σ J) σ.ker).subschemeι,
    inferInstance, ?_, ?_⟩
  · rw [Category.assoc, ← hψ1, ← Category.assoc, hab]
  · rw [Scheme.Hom.ker_comp_of_isIso]
    exact Scheme.IdealSheafData.ker_subschemeι _

private theorem exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length_consolidated211 (_hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (n : ℕ) (hn : n < s.length) (A : Scheme.{u}) (σ : s.obj n ⟶ A)
    (hσ : IsClosedImmersion σ) (hA : IsNoetherian A)
    (hc : ∀ T ∈ irreducibleComponents ↥(s.obj n),
        ¬ T ⊆ ((s.center n).support : Set ↥(s.obj n))) :
    ∃ τ : s.obj (n + 1) ⟶ Blowup.blowup (imageIdealSheaf σ (s.center n)),
      IsClosedImmersion τ ∧
      τ ≫ Blowup.blowup.proj (imageIdealSheaf σ (s.center n)) = s.map n ≫ σ ∧
      τ.ker = Blowup.strictTransform (Blowup.blowup.proj (imageIdealSheaf σ (s.center n)))
          (imageIdealSheaf σ (s.center n)) σ.ker := by
  have := hσ
  have := hA
  have : IsLocallyNoetherian A := inferInstance
  exact exists_closedImmersion_blowup_of_isBlowupAlongIdealSheaf_consolidated211 hres σ (s.center n) (s.map n) (s.isBlowup n hn) hc


end

private def embeddingIntoAmbientBlowup_consolidated211 (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (n : ℕ) (hn : n < s.length) (A : Scheme.{u}) (σ : s.obj n ⟶ A)
    (hσ : IsClosedImmersion σ) (hA : IsNoetherian A)
    (hc : ∀ T ∈ irreducibleComponents ↥(s.obj n),
        ¬ T ⊆ ((s.center n).support : Set ↥(s.obj n))) :
    s.obj (n + 1) ⟶ Blowup.blowup (imageIdealSheaf σ (s.center n)) :=
  (exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length_consolidated211 hres hno s n hn A σ hσ hA hc).choose

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S) (n : ℕ) (hn : n < s.length) (A : Scheme.{u}) (σ : s.obj n ⟶ A) (hσ : IsClosedImmersion σ) (hA : IsNoetherian A) (hc : ∀ T ∈ irreducibleComponents ↥(s.obj n), ¬ T ⊆ ((s.center n).support : Set ↥(s.obj n)))

private theorem isClosedImmersion_embeddingIntoBlowupImageIdealSheaf_consolidated211 :
    IsClosedImmersion (embeddingIntoAmbientBlowup_consolidated211 hres hno s n hn A σ hσ hA hc) :=
  (exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length_consolidated211 hres hno s n hn A σ hσ hA hc).choose_spec.1

private theorem embeddingIntoBlowupImageIdealSheaf_comp_proj_consolidated211 :
    embeddingIntoAmbientBlowup_consolidated211 hres hno s n hn A σ hσ hA hc ≫ Blowup.blowup.proj (imageIdealSheaf σ (s.center n)) =
      s.map n ≫ σ :=
  (exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length_consolidated211 hres hno s n hn A σ hσ hA hc).choose_spec.2.1

private theorem ker_embeddingIntoBlowupImageIdealSheaf_consolidated211 :
    (embeddingIntoAmbientBlowup_consolidated211 hres hno s n hn A σ hσ hA hc).ker =
      Blowup.strictTransform (Blowup.blowup.proj (imageIdealSheaf σ (s.center n)))
        (imageIdealSheaf σ (s.center n)) σ.ker :=
  (exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length_consolidated211 hres hno s n hn A σ hσ hA hc).choose_spec.2.2


end

private def ambientEmbeddingZero_consolidated211 {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] [IsNoetherian X]
    (s : BlowupSequenceData S) : AmbientEmbedding s 0 where
  ambient := X
  emb := s.isoZero.hom ≫ ι
  emb_isClosedImmersion := isClosedImmersion_isoObjZero_hom_comp_consolidated211 ι s
  isNoetherian_ambient_of_le_length := fun _ => inferInstance

private def ambientEmbeddingSucc_consolidated211 (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i)))
    (n : ℕ) (st : AmbientEmbedding s n) :
    Σ t : AmbientEmbedding s (n + 1), (t.ambient ⟶ st.ambient) :=
  if h : n < s.length then
    ⟨{ ambient := Blowup.blowup (imageIdealSheaf st.emb (s.center n))
       emb := embeddingIntoAmbientBlowup_consolidated211 hres hno s n h st.ambient st.emb st.emb_isClosedImmersion
         (st.isNoetherian_ambient_of_le_length (Nat.le_of_lt h)) (hcen n h)
       emb_isClosedImmersion := isClosedImmersion_embeddingIntoBlowupImageIdealSheaf_consolidated211 hres hno s n h st.ambient st.emb
         st.emb_isClosedImmersion (st.isNoetherian_ambient_of_le_length (Nat.le_of_lt h)) (hcen n h)
       isNoetherian_ambient_of_le_length := fun _ =>
         isNoetherian_blowup_of_isNoetherian_consolidated211 hno (st.isNoetherian_ambient_of_le_length (Nat.le_of_lt h))
           (imageIdealSheaf st.emb (s.center n)) },
     Blowup.blowup.proj (imageIdealSheaf st.emb (s.center n))⟩
  else
    ⟨{ ambient := s.obj (n + 1)
       emb := 𝟙 (s.obj (n + 1))
       emb_isClosedImmersion := inferInstance
       isNoetherian_ambient_of_le_length := fun hle => absurd (Nat.lt_of_succ_le hle) h },
     s.map n ≫ st.emb⟩

section
variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S) (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i), ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) (st : AmbientEmbedding s n)

private theorem isBlowupAlongIdealSheaf_succAmbientEmbeddingMorphism_consolidated211 (h : n < s.length) :
    Blowup.IsBlowupAlongIdealSheaf (ambientEmbeddingSucc_consolidated211 hres hno s hcen n st).2 (imageIdealSheaf st.emb (s.center n)) := by
  unfold ambientEmbeddingSucc_consolidated211
  rw [dif_pos h]
  exact Blowup.blowup.isBlowupAlongIdealSheaf_proj _

private theorem succAmbientEmbedding_comp_blowupMorphism_consolidated211 :
    (ambientEmbeddingSucc_consolidated211 hres hno s hcen n st).1.emb ≫ (ambientEmbeddingSucc_consolidated211 hres hno s hcen n st).2 =
      s.map n ≫ st.emb := by
  unfold ambientEmbeddingSucc_consolidated211
  by_cases h : n < s.length
  · rw [dif_pos h]
    exact embeddingIntoBlowupImageIdealSheaf_comp_proj_consolidated211 hres hno s n h st.ambient st.emb st.emb_isClosedImmersion
      (st.isNoetherian_ambient_of_le_length (Nat.le_of_lt h)) (hcen n h)
  · rw [dif_neg h]
    exact Category.id_comp _

private theorem ker_succAmbientEmbedding_eq_strictTransform_consolidated211 (h : n < s.length) :
    (ambientEmbeddingSucc_consolidated211 hres hno s hcen n st).1.emb.ker =
      Blowup.strictTransform (ambientEmbeddingSucc_consolidated211 hres hno s hcen n st).2
        (imageIdealSheaf st.emb (s.center n)) st.emb.ker := by
  unfold ambientEmbeddingSucc_consolidated211
  rw [dif_pos h]
  exact ker_embeddingIntoBlowupImageIdealSheaf_consolidated211 hres hno s n h st.ambient st.emb st.emb_isClosedImmersion
    (st.isNoetherian_ambient_of_le_length (Nat.le_of_lt h)) (hcen n h)


end

private def ambientEmbedding_consolidated211 {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] [IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) :
    ∀ n : ℕ, AmbientEmbedding s n := fun n =>
  Nat.rec (motive := fun n => AmbientEmbedding s n) (ambientEmbeddingZero_consolidated211 ι s)
    (fun m st => (ambientEmbeddingSucc_consolidated211 hres hno s hcen m st).1) n

private def ambientEmbeddingSuccMap_consolidated211 {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] [IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) :
    (ambientEmbedding_consolidated211 ι s hres hno hcen (n + 1)).ambient ⟶ (ambientEmbedding_consolidated211 ι s hres hno hcen n).ambient :=
  (ambientEmbeddingSucc_consolidated211 hres hno s hcen n (ambientEmbedding_consolidated211 ι s hres hno hcen n)).2

private theorem isBlowupAlongIdealSheaf_ambientBlowupMorphism_consolidated211 {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] [IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) (hn : n < s.length) :
    Blowup.IsBlowupAlongIdealSheaf (ambientEmbeddingSuccMap_consolidated211 ι s hres hno hcen n)
      (imageIdealSheaf (ambientEmbedding_consolidated211 ι s hres hno hcen n).emb (s.center n)) :=
  isBlowupAlongIdealSheaf_succAmbientEmbeddingMorphism_consolidated211 hres hno s hcen n (ambientEmbedding_consolidated211 ι s hres hno hcen n) hn

def ambientBlowupSequence {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] [IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) : BlowupSequenceData X where
  length := s.length
  obj := fun n => (ambientEmbedding_consolidated211 ι s hres hno hcen n).ambient
  map := fun n => ambientEmbeddingSuccMap_consolidated211 ι s hres hno hcen n
  isoZero := Iso.refl X
  center := fun n => imageIdealSheaf (ambientEmbedding_consolidated211 ι s hres hno hcen n).emb (s.center n)
  isBlowup := fun n hn => isBlowupAlongIdealSheaf_ambientBlowupMorphism_consolidated211 ι s hres hno hcen n hn

def embeddingIntoAmbientBlowupSequence {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] [IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) :
    s.obj n ⟶ (ambientBlowupSequence ι s hres hno hcen).obj n :=
  (ambientEmbedding_consolidated211 ι s hres hno hcen n).emb

@[simp]
theorem ambientBlowupSequence_length {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] [IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) :
    (ambientBlowupSequence ι s hres hno hcen).length = s.length := rfl

theorem ambientBlowupSequence_isoObjZero {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] [IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) :
    (ambientBlowupSequence ι s hres hno hcen).isoZero = Iso.refl X := rfl

@[simp]
theorem ambientBlowupSequence_center {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] [IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) :
    (ambientBlowupSequence ι s hres hno hcen).center n =
      imageIdealSheaf (embeddingIntoAmbientBlowupSequence ι s hres hno hcen n) (s.center n) := rfl

section
variable {S X : Scheme.{u}} (ι : S ⟶ X) [IsClosedImmersion ι] [IsNoetherian X] (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u}) (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i), ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i)))

theorem isNoetherian_ambientBlowupSequence_schemeAt (n : ℕ) (hn : n ≤ s.length) :
    IsNoetherian ((ambientBlowupSequence ι s hres hno hcen).obj n) :=
  (ambientEmbedding_consolidated211 ι s hres hno hcen n).isNoetherian_ambient_of_le_length hn

theorem isClosedImmersion_embeddingIntoAmbientBlowupSequence (n : ℕ) :
    IsClosedImmersion (embeddingIntoAmbientBlowupSequence ι s hres hno hcen n) :=
  (ambientEmbedding_consolidated211 ι s hres hno hcen n).emb_isClosedImmersion

theorem embeddingIntoAmbientBlowupSequence_zero :
    embeddingIntoAmbientBlowupSequence ι s hres hno hcen 0 = s.isoZero.hom ≫ ι := rfl

theorem embeddingIntoAmbientBlowupSequence_succ_comp_map (n : ℕ) :
    embeddingIntoAmbientBlowupSequence ι s hres hno hcen (n + 1) ≫ (ambientBlowupSequence ι s hres hno hcen).map n =
      s.map n ≫ embeddingIntoAmbientBlowupSequence ι s hres hno hcen n :=
  succAmbientEmbedding_comp_blowupMorphism_consolidated211 hres hno s hcen n (ambientEmbedding_consolidated211 ι s hres hno hcen n)

theorem ker_embeddingIntoAmbientBlowupSequence_succ (n : ℕ) (hn : n < s.length) :
    (embeddingIntoAmbientBlowupSequence ι s hres hno hcen (n + 1)).ker =
      Blowup.strictTransform ((ambientBlowupSequence ι s hres hno hcen).map n)
        ((ambientBlowupSequence ι s hres hno hcen).center n)
        (embeddingIntoAmbientBlowupSequence ι s hres hno hcen n).ker :=
  ker_succAmbientEmbedding_eq_strictTransform_consolidated211 hres hno s hcen n (ambientEmbedding_consolidated211 ι s hres hno hcen n) hn

theorem isPushforwardBlowupSeq_ambientBlowupSequence :
    IsPushforwardBlowupSeq ι s.toSequenceOfBlowups (ambientBlowupSequence ι s hres hno hcen).toSequenceOfBlowups := by
  refine ⟨rfl, ⟨fun i _ => embeddingIntoAmbientBlowupSequence ι s hres hno hcen i,
    fun i _ => isClosedImmersion_embeddingIntoAmbientBlowupSequence ι s hres hno hcen i, ?_, ?_, ?_, ?_⟩⟩
  · show (s.isoZero.hom ≫ ι) ≫ 𝟙 X = s.isoZero.hom ≫ ι
    exact Category.comp_id _
  · intro i hi
    show embeddingIntoAmbientBlowupSequence ι s hres hno hcen (i + 1) ≫
        (ambientBlowupSequence ι s hres hno hcen).toSequenceOfBlowups.transitionMapSucc i =
      s.toSequenceOfBlowups.transitionMapSucc i ≫ embeddingIntoAmbientBlowupSequence ι s hres hno hcen i
    rw [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.toSequenceOfBlowups_blowupMorphism]
    exact embeddingIntoAmbientBlowupSequence_succ_comp_map ι s hres hno hcen i
  · intro i _
    rfl
  · intro i hi
    show (embeddingIntoAmbientBlowupSequence ι s hres hno hcen (i + 1)).ker =
      Blowup.strictTransform ((ambientBlowupSequence ι s hres hno hcen).toSequenceOfBlowups.transitionMapSucc i)
        ((ambientBlowupSequence ι s hres hno hcen).toSequenceOfBlowups.center i)
        (embeddingIntoAmbientBlowupSequence ι s hres hno hcen i).ker
    rw [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism]
    exact ker_embeddingIntoAmbientBlowupSequence_succ ι s hres hno hcen i hi


end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
section


section
namespace FunctorialResolution.EmbeddedResolution

theorem _root_.FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.of_eq {A A' B B' : Scheme.{u}} {π : A ⟶ B} {J : B.IdealSheafData}
    (h : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf π J) (hA : A = A') (hB : B = B') :
    FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf (eqToHom hA.symm ≫ π ≫ eqToHom hB) (J.comap (eqToHom hB.symm)) := by
  subst hA
  subst hB
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id] using h

namespace BlowupSequenceData

variable {X : Scheme.{u}}

theorem projectionToBase_congr (d : BlowupSequenceData X) {n n' : ℕ} (h : n = n') :
    projectionToBase d n = eqToHom (congrArg d.obj h) ≫ projectionToBase d n' := by
  subst h
  rw [eqToHom_refl, Category.id_comp]

variable (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))

def appendSchemeAt (i : ℕ) : Scheme.{u} :=
  if i ≤ s.length then s.obj i else t.obj (i - s.length)

section
variable {i : ℕ}

theorem appendSchemeAt_of_le_length (h : i ≤ s.length) : appendSchemeAt s t i = s.obj i := if_pos h

theorem appendSchemeAt_of_length_lt (h : s.length < i) :
    appendSchemeAt s t i = t.obj (i - s.length) := if_neg (not_le.2 h)


end

theorem appendSchemeAt_zero : appendSchemeAt s t 0 = s.obj 0 := appendSchemeAt_of_le_length s t (Nat.zero_le _)

section
variable {i : ℕ}

theorem appendSchemeAt_succ_of_lt_length (h : i < s.length) :
    appendSchemeAt s t (i + 1) = s.obj (i + 1) :=
  appendSchemeAt_of_le_length s t (by omega)

theorem appendSchemeAt_of_eq_length (h : i = s.length) : appendSchemeAt s t i = s.obj s.length := by
  subst h
  exact appendSchemeAt_of_le_length s t le_rfl

theorem appendSchemeAt_succ_of_eq_length (h : i = s.length) :
    appendSchemeAt s t (i + 1) = t.obj 1 := by
  subst h
  have h2 : s.length + 1 - s.length = 1 := by omega
  rw [appendSchemeAt_of_length_lt s t (by omega), h2]

theorem appendSchemeAt_succ_of_length_lt (h : s.length < i) :
    appendSchemeAt s t (i + 1) = t.obj (i - s.length + 1) := by
  have h2 : i + 1 - s.length = i - s.length + 1 := by omega
  rw [appendSchemeAt_of_length_lt s t (by omega), h2]


end

def appendBlowupMorphism (i : ℕ) : appendSchemeAt s t (i + 1) ⟶ appendSchemeAt s t i :=
  if h : i < s.length then
    eqToHom (appendSchemeAt_succ_of_lt_length s t h) ≫ s.map i ≫ eqToHom (appendSchemeAt_of_le_length s t (le_of_lt h)).symm
  else if h2 : s.length < i then
    eqToHom (appendSchemeAt_succ_of_length_lt s t h2) ≫ t.map (i - s.length) ≫
      eqToHom (appendSchemeAt_of_length_lt s t h2).symm
  else
    eqToHom (appendSchemeAt_succ_of_eq_length s t (by omega)) ≫ t.map 0 ≫ t.isoZero.hom ≫
      eqToHom (appendSchemeAt_of_eq_length s t (by omega)).symm

def appendCenter (i : ℕ) : (appendSchemeAt s t i).IdealSheafData :=
  if h : i < s.length then (s.center i).comap (eqToHom (appendSchemeAt_of_le_length s t (le_of_lt h)))
  else if h2 : s.length < i then (t.center (i - s.length)).comap (eqToHom (appendSchemeAt_of_length_lt s t h2))
  else ((t.center 0).comap t.isoZero.inv).comap (eqToHom (appendSchemeAt_of_eq_length s t (by omega)))

theorem isBlowupAlongIdealSheaf_appendBlowupMorphism (i : ℕ) (hi : i < s.length + t.length) :
    Blowup.IsBlowupAlongIdealSheaf (appendBlowupMorphism s t i) (appendCenter s t i) := by
  rcases lt_trichotomy i s.length with h | h | h
  · have hmap : appendBlowupMorphism s t i =
        eqToHom (appendSchemeAt_succ_of_lt_length s t h) ≫ s.map i ≫
          eqToHom (appendSchemeAt_of_le_length s t (le_of_lt h)).symm := dif_pos h
    have hcen : appendCenter s t i =
        (s.center i).comap (eqToHom (appendSchemeAt_of_le_length s t (le_of_lt h))) := dif_pos h
    rw [hmap, hcen]
    exact Blowup.IsBlowupAlongIdealSheaf.of_eq (s.isBlowup i h) (appendSchemeAt_succ_of_lt_length s t h).symm
      (appendSchemeAt_of_le_length s t (le_of_lt h)).symm
  · subst h
    have ht : 0 < t.length := by omega
    have hmap : appendBlowupMorphism s t s.length =
        eqToHom (appendSchemeAt_succ_of_eq_length s t (rfl : s.length = s.length)) ≫ t.map 0 ≫
          t.isoZero.hom ≫
            eqToHom (appendSchemeAt_of_eq_length s t (rfl : s.length = s.length)).symm :=
      (dif_neg (lt_irrefl s.length)).trans (dif_neg (lt_irrefl s.length))
    have hcen : appendCenter s t s.length =
        ((t.center 0).comap t.isoZero.inv).comap
          (eqToHom (appendSchemeAt_of_eq_length s t (rfl : s.length = s.length))) :=
      (dif_neg (lt_irrefl s.length)).trans (dif_neg (lt_irrefl s.length))
    rw [hmap, hcen, ← Category.assoc (t.map 0) t.isoZero.hom]
    exact Blowup.IsBlowupAlongIdealSheaf.of_eq (Blowup.IsBlowupAlongIdealSheaf.comp_iso_hom (t.isBlowup 0 ht) t.isoZero)
      (appendSchemeAt_succ_of_eq_length s t (rfl : s.length = s.length)).symm
      (appendSchemeAt_of_eq_length s t (rfl : s.length = s.length)).symm
  · have hlt : i - s.length < t.length := by omega
    have hmap : appendBlowupMorphism s t i =
        eqToHom (appendSchemeAt_succ_of_length_lt s t h) ≫ t.map (i - s.length) ≫
          eqToHom (appendSchemeAt_of_length_lt s t h).symm :=
      (dif_neg (not_lt.2 (le_of_lt h))).trans (dif_pos h)
    have hcen : appendCenter s t i =
        (t.center (i - s.length)).comap (eqToHom (appendSchemeAt_of_length_lt s t h)) :=
      (dif_neg (not_lt.2 (le_of_lt h))).trans (dif_pos h)
    rw [hmap, hcen]
    exact Blowup.IsBlowupAlongIdealSheaf.of_eq (t.isBlowup (i - s.length) hlt)
      (appendSchemeAt_succ_of_length_lt s t h).symm (appendSchemeAt_of_length_lt s t h).symm

def append : BlowupSequenceData X where
  length := s.length + t.length
  obj := appendSchemeAt s t
  map := appendBlowupMorphism s t
  isoZero := eqToIso (appendSchemeAt_zero s t) ≪≫ s.isoZero
  center := appendCenter s t
  isBlowup := fun i hi => isBlowupAlongIdealSheaf_appendBlowupMorphism s t i hi

@[simp]
theorem append_length : (s.append t).length = s.length + t.length := rfl

section
variable {i : ℕ}

theorem append_schemeAt_of_le_length (h : i ≤ s.length) : (s.append t).obj i = s.obj i :=
  appendSchemeAt_of_le_length s t h

theorem append_schemeAt_of_length_lt (h : s.length < i) :
    (s.append t).obj i = t.obj (i - s.length) :=
  appendSchemeAt_of_length_lt s t h


end

theorem append_schemeAt_zero : (s.append t).obj 0 = s.obj 0 := appendSchemeAt_zero s t

section
variable {i : ℕ}

theorem append_schemeAt_succ_of_lt_length (h : i < s.length) :
    (s.append t).obj (i + 1) = s.obj (i + 1) :=
  appendSchemeAt_succ_of_lt_length s t h

theorem append_schemeAt_succ_of_length_lt (h : s.length < i) :
    (s.append t).obj (i + 1) = t.obj (i - s.length + 1) :=
  appendSchemeAt_succ_of_length_lt s t h


end

theorem append_schemeAt_length_succ : (s.append t).obj (s.length + 1) = t.obj 1 :=
  appendSchemeAt_succ_of_eq_length s t rfl

theorem append_schemeAt_length_add_length (h : 0 < t.length) :
    (s.append t).obj (s.length + t.length) = t.obj t.length := by
  have h2 : s.length + t.length - s.length = t.length := by omega
  show appendSchemeAt s t (s.length + t.length) = t.obj t.length
  rw [appendSchemeAt_of_length_lt s t (by omega), h2]

theorem append_isoObjZero_hom :
    (s.append t).isoZero.hom = eqToHom (append_schemeAt_zero s t) ≫ s.isoZero.hom := rfl

section
variable {i : ℕ}

theorem append_blowupMorphism_of_lt_length (h : i < s.length) :
    (s.append t).map i =
      eqToHom (append_schemeAt_succ_of_lt_length s t h) ≫ s.map i ≫
        eqToHom (append_schemeAt_of_le_length s t (le_of_lt h)).symm := by
  exact dif_pos h

theorem append_blowupMorphism_of_length_lt (h : s.length < i) :
    (s.append t).map i =
      eqToHom (append_schemeAt_succ_of_length_lt s t h) ≫ t.map (i - s.length) ≫
        eqToHom (append_schemeAt_of_length_lt s t h).symm := by
  exact (dif_neg (not_lt.2 (le_of_lt h))).trans (dif_pos h)


end

theorem append_blowupMorphism_length :
    (s.append t).map s.length =
      eqToHom (append_schemeAt_length_succ s t) ≫ t.map 0 ≫ t.isoZero.hom ≫
        eqToHom (append_schemeAt_of_le_length s t (le_refl s.length)).symm := by
  exact (dif_neg (lt_irrefl s.length)).trans (dif_neg (lt_irrefl s.length))

section
variable {i : ℕ}

theorem append_center_of_lt_length (h : i < s.length) :
    (s.append t).center i = (s.center i).comap (eqToHom (append_schemeAt_of_le_length s t (le_of_lt h))) := by
  exact dif_pos h

theorem append_center_of_length_lt (h : s.length < i) :
    (s.append t).center i =
      (t.center (i - s.length)).comap (eqToHom (append_schemeAt_of_length_lt s t h)) := by
  exact (dif_neg (not_lt.2 (le_of_lt h))).trans (dif_pos h)


end

theorem append_center_length :
    (s.append t).center s.length =
      ((t.center 0).comap t.isoZero.inv).comap
        (eqToHom (append_schemeAt_of_le_length s t (le_refl s.length))) := by
  exact (dif_neg (lt_irrefl s.length)).trans (dif_neg (lt_irrefl s.length))

theorem projectionToBase_append_of_le_length {i : ℕ} (h : i ≤ s.length) :
    projectionToBase (s.append t) i = eqToHom (append_schemeAt_of_le_length s t h) ≫ projectionToBase s i := by
  revert h
  induction i with
  | zero =>
    intro _
    rfl
  | succ n ih =>
    intro h
    have hn : n < s.length := h
    rw [projectionToBase_succ, ih (le_of_lt hn), append_blowupMorphism_of_lt_length s t hn, projectionToBase_succ]
    simp

private theorem blowupMorphism_eq_eqToHom_comp_of_eq_consolidated209 {Y : Scheme.{u}} (d : BlowupSequenceData Y) {n n' : ℕ} (h : n = n')
    (e1 : d.obj (n + 1) = d.obj (n' + 1)) (e2 : d.obj n' = d.obj n) :
    d.map n = eqToHom e1 ≫ d.map n' ≫ eqToHom e2 := by
  subst h
  simp

section
variable {Y : Scheme.{u}} (a : BlowupSequenceData Y) (b : BlowupSequenceData (a.obj a.length))

private theorem append_schemeAt_of_eq_length_add_succ_consolidated209 (i j : ℕ) (h : i = a.length + j + 1) :
    (a.append b).obj i = b.obj (j + 1) := by
  subst h
  have hgt : a.length < a.length + j + 1 := by omega
  have hsub : a.length + j + 1 - a.length = j + 1 := by omega
  rw [append_schemeAt_of_length_lt a b hgt, hsub]

private theorem append_blowupMorphism_of_eq_length_add_succ_consolidated209 (i j : ℕ) (h : i = a.length + j + 1)
    (e1 : (a.append b).obj (i + 1) = b.obj (j + 1 + 1))
    (e2 : b.obj (j + 1) = (a.append b).obj i) :
    (a.append b).map i = eqToHom e1 ≫ b.map (j + 1) ≫ eqToHom e2 := by
  subst h
  have hgt : a.length < a.length + j + 1 := by omega
  have hsub : a.length + j + 1 - a.length = j + 1 := by omega
  rw [append_blowupMorphism_of_length_lt a b hgt, blowupMorphism_eq_eqToHom_comp_of_eq_consolidated209 b hsub (by rw [hsub]) (by rw [hsub])]
  simp

private theorem projectionToBase_append_of_eq_length_add_succ_consolidated209 :
    ∀ (j i : ℕ), i = a.length + j + 1 → ∀ (e : (a.append b).obj i = b.obj (j + 1)),
      projectionToBase (a.append b) i = eqToHom e ≫ projectionToBase b (j + 1) ≫ projectionToBase a a.length := by
  intro j
  induction j with
  | zero =>
      intro i hi e
      have hi' : i = a.length + 1 := by omega
      subst hi'
      rw [projectionToBase_succ (a.append b) a.length, append_blowupMorphism_length a b,
        projectionToBase_append_of_le_length a b le_rfl, projectionToBase_succ b 0, projectionToBase_zero b]
      simp
  | succ n ih =>
      intro i hi e
      have hi' : i = a.length + n + 1 + 1 := by omega
      subst hi'
      rw [projectionToBase_succ (a.append b) (a.length + n + 1),
        append_blowupMorphism_of_eq_length_add_succ_consolidated209 a b (a.length + n + 1) n rfl
          (append_schemeAt_of_eq_length_add_succ_consolidated209 a b (a.length + n + 1 + 1) (n + 1) (by omega))
          (append_schemeAt_of_eq_length_add_succ_consolidated209 a b (a.length + n + 1) n rfl).symm,
        ih (a.length + n + 1) rfl (append_schemeAt_of_eq_length_add_succ_consolidated209 a b (a.length + n + 1) n rfl),
        projectionToBase_succ b (n + 1)]
      simp


end

theorem projectionToBase_append_of_length_lt {i : ℕ} (h : s.length < i) :
    projectionToBase (s.append t) i =
      eqToHom (append_schemeAt_of_length_lt s t h) ≫ projectionToBase t (i - s.length) ≫ projectionToBase s s.length := by
  obtain ⟨j, rfl⟩ : ∃ j, i = s.length + j + 1 := ⟨i - s.length - 1, by omega⟩
  have hsub : s.length + j + 1 - s.length = j + 1 := by omega
  rw [projectionToBase_congr t hsub,
    projectionToBase_append_of_eq_length_add_succ_consolidated209 s t j (s.length + j + 1) rfl
      (append_schemeAt_of_eq_length_add_succ_consolidated209 s t (s.length + j + 1) j rfl)]
  simp

end BlowupSequenceData

structure ComapIsoInvariance : Prop where
  coSupport_comap : ∀ {X Y : Scheme.{u}} (e : X ≅ Y) (J : Y.IdealSheafData) (n : ℕ),
    orderAtLeastLocus (J.comap e.hom) n = ⇑e.hom.base ⁻¹' orderAtLeastLocus J n
  hasSNCWith_comap : ∀ {k : Type u} [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) (Z : Y.IdealSheafData)
    (F : List Y.IdealSheafData), HasStrictNormalCrossingsWith q Z F →
      HasStrictNormalCrossingsWith (e.hom ≫ q) (Z.comap e.hom) (F.map (fun D => D.comap e.hom))
  smooth_comap : ∀ {k : Type u} [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) (Z : Y.IdealSheafData),
    Smooth (Z.subschemeι ≫ q) →
      Smooth ((Z.comap e.hom).subschemeι ≫ e.hom ≫ q)
  strictTransform_comap : ∀ {X X₁ Y : Scheme.{u}} (π : X₁ ⟶ X) (e : X ≅ Y)
    (Z D : Y.IdealSheafData),
    Blowup.strictTransform (π ≫ e.hom) Z D = Blowup.strictTransform π (Z.comap e.hom) (D.comap e.hom)

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

variable (s : MarkedBlowupSequenceData p I m E)
  (t : MarkedBlowupSequenceData (s.proj s.toBlowupSequenceData.length ≫ p) (s.ideal s.toBlowupSequenceData.length) m
    (s.boundary s.toBlowupSequenceData.length))

def appendToBlowupSequenceData : BlowupSequenceData X := s.toBlowupSequenceData.append t.toBlowupSequenceData

@[simp]
theorem appendToBlowupSequenceData_length :
    (s.appendToBlowupSequenceData t).length = s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := rfl

section
variable {i : ℕ}

theorem appendToBlowupSequenceData_schemeAt_of_le_length (h : i ≤ s.toBlowupSequenceData.length) :
    (s.appendToBlowupSequenceData t).obj i = s.toBlowupSequenceData.obj i :=
  BlowupSequenceData.append_schemeAt_of_le_length s.toBlowupSequenceData t.toBlowupSequenceData h

theorem appendToBlowupSequenceData_schemeAt_of_length_lt (h : s.toBlowupSequenceData.length < i) :
    (s.appendToBlowupSequenceData t).obj i = t.toBlowupSequenceData.obj (i - s.toBlowupSequenceData.length) :=
  BlowupSequenceData.append_schemeAt_of_length_lt s.toBlowupSequenceData t.toBlowupSequenceData h


end

theorem appendToBlowupSequenceData_schemeAt_zero : (s.appendToBlowupSequenceData t).obj 0 = s.toBlowupSequenceData.obj 0 :=
  BlowupSequenceData.append_schemeAt_zero s.toBlowupSequenceData t.toBlowupSequenceData

section
variable {i : ℕ}

theorem appendToBlowupSequenceData_schemeAt_succ_of_lt_length (h : i < s.toBlowupSequenceData.length) :
    (s.appendToBlowupSequenceData t).obj (i + 1) = s.toBlowupSequenceData.obj (i + 1) :=
  BlowupSequenceData.append_schemeAt_succ_of_lt_length s.toBlowupSequenceData t.toBlowupSequenceData h

theorem appendToBlowupSequenceData_schemeAt_succ_of_length_lt (h : s.toBlowupSequenceData.length < i) :
    (s.appendToBlowupSequenceData t).obj (i + 1) =
      t.toBlowupSequenceData.obj (i - s.toBlowupSequenceData.length + 1) :=
  BlowupSequenceData.append_schemeAt_succ_of_length_lt s.toBlowupSequenceData t.toBlowupSequenceData h


end

theorem appendToBlowupSequenceData_schemeAt_length_succ :
    (s.appendToBlowupSequenceData t).obj (s.toBlowupSequenceData.length + 1) = t.toBlowupSequenceData.obj 1 :=
  BlowupSequenceData.append_schemeAt_length_succ s.toBlowupSequenceData t.toBlowupSequenceData

theorem appendToBlowupSequenceData_schemeAt_length_add_length (h : 0 < t.toBlowupSequenceData.length) :
    (s.appendToBlowupSequenceData t).obj (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length) =
      t.toBlowupSequenceData.obj t.toBlowupSequenceData.length :=
  BlowupSequenceData.append_schemeAt_length_add_length s.toBlowupSequenceData t.toBlowupSequenceData h

theorem appendToBlowupSequenceData_isoObjZero_hom :
    (s.appendToBlowupSequenceData t).isoZero.hom =
      eqToHom (appendToBlowupSequenceData_schemeAt_zero s t) ≫ s.toBlowupSequenceData.isoZero.hom := rfl

section
variable {i : ℕ}

theorem appendToBlowupSequenceData_blowupMorphism_of_lt_length (h : i < s.toBlowupSequenceData.length) :
    (s.appendToBlowupSequenceData t).map i =
      eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_lt_length s t h) ≫ s.toBlowupSequenceData.map i ≫
        eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h)).symm :=
  BlowupSequenceData.append_blowupMorphism_of_lt_length s.toBlowupSequenceData t.toBlowupSequenceData h

theorem appendToBlowupSequenceData_blowupMorphism_of_length_lt (h : s.toBlowupSequenceData.length < i) :
    (s.appendToBlowupSequenceData t).map i =
      eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h) ≫
        t.toBlowupSequenceData.map (i - s.toBlowupSequenceData.length) ≫
        eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h).symm :=
  BlowupSequenceData.append_blowupMorphism_of_length_lt s.toBlowupSequenceData t.toBlowupSequenceData h


end

theorem appendToBlowupSequenceData_blowupMorphism_length :
    (s.appendToBlowupSequenceData t).map s.toBlowupSequenceData.length =
      eqToHom (appendToBlowupSequenceData_schemeAt_length_succ s t) ≫ t.toBlowupSequenceData.map 0 ≫
        t.toBlowupSequenceData.isoZero.hom ≫
        eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length)).symm :=
  BlowupSequenceData.append_blowupMorphism_length s.toBlowupSequenceData t.toBlowupSequenceData

section
variable {i : ℕ}

theorem appendToBlowupSequenceData_center_of_lt_length (h : i < s.toBlowupSequenceData.length) :
    (s.appendToBlowupSequenceData t).center i =
      (s.toBlowupSequenceData.center i).comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h))) :=
  BlowupSequenceData.append_center_of_lt_length s.toBlowupSequenceData t.toBlowupSequenceData h

theorem appendToBlowupSequenceData_center_of_length_lt (h : s.toBlowupSequenceData.length < i) :
    (s.appendToBlowupSequenceData t).center i =
      (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length)).comap
        (eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)) :=
  BlowupSequenceData.append_center_of_length_lt s.toBlowupSequenceData t.toBlowupSequenceData h


end

theorem appendToBlowupSequenceData_center_length :
    (s.appendToBlowupSequenceData t).center s.toBlowupSequenceData.length =
      ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv).comap
        (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))) :=
  BlowupSequenceData.append_center_length s.toBlowupSequenceData t.toBlowupSequenceData

def appendProjectionToBase (i : ℕ) : (s.appendToBlowupSequenceData t).obj i ⟶ X :=
  if h : i ≤ s.toBlowupSequenceData.length then
    eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t h) ≫ s.proj i
  else
    eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t (not_le.1 h)) ≫ t.proj (i - s.toBlowupSequenceData.length) ≫
      s.proj s.toBlowupSequenceData.length

section
variable {i : ℕ}

theorem appendProjectionToBase_of_le_length (h : i ≤ s.toBlowupSequenceData.length) :
    s.appendProjectionToBase t i = eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t h) ≫ s.proj i :=
  dif_pos h

theorem appendProjectionToBase_of_length_lt (h : s.toBlowupSequenceData.length < i) :
    s.appendProjectionToBase t i =
      eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h) ≫ t.proj (i - s.toBlowupSequenceData.length) ≫
        s.proj s.toBlowupSequenceData.length :=
  dif_neg (not_le.2 h)


end

def appendIdeal (i : ℕ) : ((s.appendToBlowupSequenceData t).obj i).IdealSheafData :=
  if h : i ≤ s.toBlowupSequenceData.length then
    (s.ideal i).comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t h))
  else
    (t.ideal (i - s.toBlowupSequenceData.length)).comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t (not_le.1 h)))

section
variable {i : ℕ}

theorem appendIdeal_of_le_length (h : i ≤ s.toBlowupSequenceData.length) :
    s.appendIdeal t i = (s.ideal i).comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t h)) :=
  dif_pos h

theorem appendIdeal_of_length_lt (h : s.toBlowupSequenceData.length < i) :
    s.appendIdeal t i =
      (t.ideal (i - s.toBlowupSequenceData.length)).comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)) :=
  dif_neg (not_le.2 h)


end

private theorem comap_eqToHom_congr_consolidated209 {A : Scheme.{u}} (F : ℕ → Scheme.{u})
    (G : ∀ n : ℕ, (F n).IdealSheafData) {i j : ℕ} (hij : i = j)
    (hi : A = F i) (hj : A = F j) :
    (G i).comap (eqToHom hi) = (G j).comap (eqToHom hj) := by
  subst hij
  rfl

theorem appendIdeal_length_succ :
    s.appendIdeal t (s.toBlowupSequenceData.length + 1) =
      (t.ideal 1).comap (eqToHom (appendToBlowupSequenceData_schemeAt_length_succ s t)) := by
  have hlt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + 1 := Nat.lt_succ_self _
  refine (appendIdeal_of_length_lt s t hlt).trans ?_
  exact comap_eqToHom_congr_consolidated209 (fun n => t.toBlowupSequenceData.obj n)
    (fun n => t.ideal n) (by omega) (appendToBlowupSequenceData_schemeAt_of_length_lt s t hlt)
    (appendToBlowupSequenceData_schemeAt_length_succ s t)

def appendBoundary (i : ℕ) : List ((s.appendToBlowupSequenceData t).obj i).IdealSheafData :=
  if h : i ≤ s.toBlowupSequenceData.length then
    (s.boundary i).map (fun D => D.comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t h)))
  else
    (t.boundary (i - s.toBlowupSequenceData.length)).map
      (fun D => D.comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t (not_le.1 h))))

section
variable {i : ℕ}

theorem appendBoundary_of_le_length (h : i ≤ s.toBlowupSequenceData.length) :
    s.appendBoundary t i =
      (s.boundary i).map (fun D => D.comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t h))) :=
  dif_pos h

theorem appendBoundary_of_length_lt (h : s.toBlowupSequenceData.length < i) :
    s.appendBoundary t i =
      (t.boundary (i - s.toBlowupSequenceData.length)).map
        (fun D => D.comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h))) :=
  dif_neg (not_le.2 h)


end

private theorem map_comap_eqToHom_congr_consolidated209 {A : Scheme.{u}}
    {F : ℕ → Scheme.{u}} (B : ∀ n : ℕ, List (F n).IdealSheafData) (i j : ℕ) (hij : i = j)
    (e : A = F i) (e' : A = F j) :
    (B i).map (fun D => D.comap (eqToHom e)) = (B j).map (fun D => D.comap (eqToHom e')) := by
  subst hij
  rfl

theorem appendBoundary_length_succ :
    s.appendBoundary t (s.toBlowupSequenceData.length + 1) =
      (t.boundary 1).map (fun D => D.comap (eqToHom (appendToBlowupSequenceData_schemeAt_length_succ s t))) := by
  have hlt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + 1 := Nat.lt_succ_self _
  refine (appendBoundary_of_length_lt s t hlt).trans ?_
  exact map_comap_eqToHom_congr_consolidated209
    (A := (s.appendToBlowupSequenceData t).obj (s.toBlowupSequenceData.length + 1))
    (F := fun n => t.toBlowupSequenceData.obj n) (fun n => t.boundary n)
    (s.toBlowupSequenceData.length + 1 - s.toBlowupSequenceData.length) 1 (by omega)
    (appendToBlowupSequenceData_schemeAt_of_length_lt s t hlt) (appendToBlowupSequenceData_schemeAt_length_succ s t)

theorem appendProjectionToBase_zero : s.appendProjectionToBase t 0 = (s.appendToBlowupSequenceData t).isoZero.hom := by
  rw [appendProjectionToBase_of_le_length s t (Nat.zero_le _), appendToBlowupSequenceData_isoObjZero_hom, s.proj_zero]

private theorem projectionToBase_congr_consolidated209 (d : MarkedBlowupSequenceData p I m E) {i j : ℕ} (h : i = j) :
    d.proj i = eqToHom (congrArg d.toBlowupSequenceData.obj h) ≫ d.proj j := by
  subst h
  simp

theorem appendProjectionToBase_succ (i : ℕ) :
    s.appendProjectionToBase t (i + 1) = (s.appendToBlowupSequenceData t).map i ≫ s.appendProjectionToBase t i := by
  rcases lt_trichotomy i s.toBlowupSequenceData.length with h | h | h
  · have h1 : i + 1 ≤ s.toBlowupSequenceData.length := by omega
    rw [appendProjectionToBase_of_le_length s t h1, appendToBlowupSequenceData_blowupMorphism_of_lt_length s t h, appendProjectionToBase_of_le_length s t (le_of_lt h),
      s.proj_succ i]
    simp
  · subst h
    have hlt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + 1 := by omega
    have hsub : s.toBlowupSequenceData.length + 1 - s.toBlowupSequenceData.length = 1 := by omega
    have hp1 : t.proj 1 = t.toBlowupSequenceData.map 0 ≫ t.proj 0 := t.proj_succ 0
    rw [appendProjectionToBase_of_length_lt s t hlt, appendToBlowupSequenceData_blowupMorphism_length s t,
      appendProjectionToBase_of_le_length s t (le_refl s.toBlowupSequenceData.length),
      projectionToBase_congr_consolidated209 t hsub, hp1, t.proj_zero]
    simp
  · have h1 : s.toBlowupSequenceData.length < i + 1 := by omega
    have hsub : i + 1 - s.toBlowupSequenceData.length = (i - s.toBlowupSequenceData.length) + 1 := by omega
    have hp1 : t.proj (i - s.toBlowupSequenceData.length + 1) =
        t.toBlowupSequenceData.map (i - s.toBlowupSequenceData.length) ≫ t.proj (i - s.toBlowupSequenceData.length) :=
      t.proj_succ _
    rw [appendProjectionToBase_of_length_lt s t h1, appendToBlowupSequenceData_blowupMorphism_of_length_lt s t h, appendProjectionToBase_of_length_lt s t h,
      projectionToBase_congr_consolidated209 t hsub, hp1]
    simp

theorem appendIdeal_zero : s.appendIdeal t 0 = I.comap (s.appendToBlowupSequenceData t).isoZero.hom := by
  rw [appendIdeal_of_le_length s t (Nat.zero_le _), s.ideal_zero, appendToBlowupSequenceData_isoObjZero_hom]
  exact (AlgebraicGeometry.Scheme.IdealSheafData.comap_comp ..).symm

private theorem map_comap_eqToHom_comp_consolidated209 {A B C : Scheme.{u}} (h : A = B) (g : B ⟶ C)
    (L : List C.IdealSheafData) :
    (L.map (fun D => D.comap g)).map (fun D => D.comap (eqToHom h)) =
      L.map (fun D => D.comap (eqToHom h ≫ g)) := by
  subst h
  simp [AlgebraicGeometry.Scheme.IdealSheafData.comap_id]

theorem appendBoundary_zero :
    s.appendBoundary t 0 = E.map (fun D => D.comap (s.appendToBlowupSequenceData t).isoZero.hom) := by
  rw [appendBoundary_of_le_length s t (Nat.zero_le _), appendToBlowupSequenceData_isoObjZero_hom, s.boundary_zero]
  exact map_comap_eqToHom_comp_consolidated209 (appendToBlowupSequenceData_schemeAt_of_le_length s t (Nat.zero_le _))
    s.toBlowupSequenceData.isoZero.hom E

section
variable (hinv : ComapIsoInvariance.{u}) (i : ℕ) (hi : i < (s.appendToBlowupSequenceData t).length)
include hinv hi

theorem center_support_subset_orderAtLeastLocus_appendIdeal :
    (((s.appendToBlowupSequenceData t).center i).support : Set ↥((s.appendToBlowupSequenceData t).obj i)) ⊆
      orderAtLeastLocus (s.appendIdeal t i) m := by
  have hi' : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := hi
  have hcomp : ∀ (V W T : Scheme.{u}) (f : V ⟶ W) (g : W ⟶ T) (J : T.IdealSheafData),
      J.comap (f ≫ g) = (J.comap g).comap f := by
    intro V W T f g J
    simp only [AlgebraicGeometry.Scheme.IdealSheafData.comap_comp]
  have key : ∀ (A B : Scheme.{u}) (hAB : A = B) (C K : B.IdealSheafData),
      ((C.support : Set ↥B) ⊆ orderAtLeastLocus K m) →
      (((C.comap (eqToHom hAB)).support : Set ↥A) ⊆ orderAtLeastLocus (K.comap (eqToHom hAB)) m) := by
    intro A B hAB C K h
    subst hAB
    simpa only [eqToHom_refl, AlgebraicGeometry.Scheme.IdealSheafData.comap_id] using h
  have keyIso : ∀ (A B : Scheme.{u}) (e : A ≅ B) (C : A.IdealSheafData) (K : B.IdealSheafData),
      ((C.support : Set ↥A) ⊆ orderAtLeastLocus (K.comap e.hom) m) →
      (((C.comap e.inv).support : Set ↥B) ⊆ orderAtLeastLocus K m) := by
    intro A B e C K h
    have hK : (K.comap e.hom).comap e.inv = K := by
      rw [← hcomp, e.inv_hom_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]
    have h2 : orderAtLeastLocus ((K.comap e.hom).comap e.inv) m
        = ⇑e.inv.base ⁻¹' orderAtLeastLocus (K.comap e.hom) m :=
      hinv.coSupport_comap e.symm (K.comap e.hom) m
    rw [hK] at h2
    have hsupp : ((C.comap e.inv).support : Set ↥B) = ⇑e.inv.base ⁻¹' (C.support : Set ↥A) := by
      simp [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
    rw [hsupp, h2]
    exact Set.preimage_mono h
  rcases lt_trichotomy i s.toBlowupSequenceData.length with h | h | h
  · rw [appendToBlowupSequenceData_center_of_lt_length s t h, appendIdeal_of_le_length s t (le_of_lt h)]
    exact key _ _ (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h)) (s.toBlowupSequenceData.center i) (s.ideal i)
      (s.center_order i h)
  · subst h
    have ht0 : 0 < t.toBlowupSequenceData.length := by omega
    have hb := t.center_order 0 ht0
    rw [t.ideal_zero] at hb
    have hbase := keyIso _ _ t.toBlowupSequenceData.isoZero (t.toBlowupSequenceData.center 0)
      (s.ideal s.toBlowupSequenceData.length) hb
    rw [appendToBlowupSequenceData_center_length s t,
      appendIdeal_of_le_length s t (le_refl s.toBlowupSequenceData.length)]
    exact key _ _ (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))
      ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv)
      (s.ideal s.toBlowupSequenceData.length) hbase
  · have hsub : i - s.toBlowupSequenceData.length < t.toBlowupSequenceData.length := by omega
    rw [appendToBlowupSequenceData_center_of_length_lt s t h, appendIdeal_of_length_lt s t h]
    exact key _ _ (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)
      (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length))
      (t.ideal (i - s.toBlowupSequenceData.length))
      (t.center_order (i - s.toBlowupSequenceData.length) hsub)

private theorem smooth_center_comp_appendProjectionToBase_consolidated209 :
    Smooth
      (((s.appendToBlowupSequenceData t).center i).subschemeι ≫ s.appendProjectionToBase t i ≫ p) := by
  have hi' : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := hi
  rcases lt_trichotomy i s.toBlowupSequenceData.length with h | h | h
  · rw [appendProjectionToBase_of_le_length s t (le_of_lt h), appendToBlowupSequenceData_center_of_lt_length s t h]
    have hA := hinv.smooth_comap (s.proj i ≫ p)
      (eqToIso (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h))) (s.toBlowupSequenceData.center i)
      (s.center_smooth i h)
    simpa only [eqToIso.hom, Category.assoc] using hA
  · subst h
    have ht0 : 0 < t.toBlowupSequenceData.length := by omega
    have hsm := t.center_smooth 0 ht0
    rw [t.proj_zero] at hsm
    have hT := hinv.smooth_comap
      (t.toBlowupSequenceData.isoZero.hom ≫ s.proj s.toBlowupSequenceData.length ≫ p)
      t.toBlowupSequenceData.isoZero.symm (t.toBlowupSequenceData.center 0) hsm
    simp only [Iso.symm_hom, Iso.inv_hom_id_assoc] at hT
    rw [appendProjectionToBase_of_le_length s t (le_refl s.toBlowupSequenceData.length), appendToBlowupSequenceData_center_length s t]
    have hB := hinv.smooth_comap (s.proj s.toBlowupSequenceData.length ≫ p)
      (eqToIso (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length)))
      ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv) hT
    simpa only [eqToIso.hom, Category.assoc] using hB
  · rw [appendProjectionToBase_of_length_lt s t h, appendToBlowupSequenceData_center_of_length_lt s t h]
    have hC := hinv.smooth_comap
      (t.proj (i - s.toBlowupSequenceData.length) ≫ s.proj s.toBlowupSequenceData.length ≫ p)
      (eqToIso (appendToBlowupSequenceData_schemeAt_of_length_lt s t h))
      (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length))
      (t.center_smooth (i - s.toBlowupSequenceData.length) (by omega))
    simpa only [eqToIso.hom, Category.assoc] using hC


end

section
variable {A B : Scheme.{u}} (e : A ≅ B)

private theorem comap_comap_hom_inv_consolidated209 (D : B.IdealSheafData) : (D.comap e.hom).comap e.inv = D := by
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, e.inv_hom_id,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id]

private theorem map_comap_hom_map_comap_inv_consolidated209 (F : List B.IdealSheafData) :
    ((F.map fun D => D.comap e.hom).map fun D => D.comap e.inv) = F := by
  induction F with
  | nil => rfl
  | cons D L ih => simp only [List.map_cons, ih, comap_comap_hom_inv_consolidated209]


end

section
variable {K : Type u} [Field K] {A B : Scheme.{u}}

private theorem hasStrictNormalCrossingsWith_comap_eqToHom_consolidated209 (h : A = B) (q : B ⟶ Spec (CommRingCat.of K)) (Z : B.IdealSheafData)
    (F : List B.IdealSheafData) (hZ : HasStrictNormalCrossingsWith q Z F) :
    HasStrictNormalCrossingsWith (eqToHom h ≫ q) (Z.comap (eqToHom h))
      (F.map fun D => D.comap (eqToHom h)) := by
  subst h
  simpa [AlgebraicGeometry.Scheme.IdealSheafData.comap_id] using hZ

private theorem hasStrictNormalCrossingsWith_comap_iso_inv_consolidated209 (hinv : ComapIsoInvariance.{u}) (e : A ≅ B) (q : B ⟶ Spec (CommRingCat.of K))
    (Z : A.IdealSheafData) (F : List B.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith (e.hom ≫ q) Z (F.map fun D => D.comap e.hom)) :
    HasStrictNormalCrossingsWith q (Z.comap e.inv) F := by
  have h2 := hinv.hasSNCWith_comap (e.hom ≫ q) e.symm Z (F.map fun D => D.comap e.hom) hZ
  rw [Iso.symm_hom, Iso.inv_hom_id_assoc, map_comap_hom_map_comap_inv_consolidated209 e F] at h2
  exact h2


end

private theorem hasStrictNormalCrossingsWith_appendBoundary_consolidated209 (hinv : ComapIsoInvariance.{u}) (i : ℕ)
    (hi : i < (s.appendToBlowupSequenceData t).length) :
    HasStrictNormalCrossingsWith (s.appendProjectionToBase t i ≫ p) ((s.appendToBlowupSequenceData t).center i)
      (s.appendBoundary t i) := by
  have hlen : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := hi
  rcases lt_trichotomy i s.toBlowupSequenceData.length with h | h | h
  · rw [appendProjectionToBase_of_le_length s t (le_of_lt h), appendToBlowupSequenceData_center_of_lt_length s t h,
      appendBoundary_of_le_length s t (le_of_lt h)]
    simp only [Category.assoc]
    exact hasStrictNormalCrossingsWith_comap_eqToHom_consolidated209 (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h)) (s.proj i ≫ p)
      (s.toBlowupSequenceData.center i) (s.boundary i) (s.center_snc i h)
  · subst h
    have ht : 0 < t.toBlowupSequenceData.length := by omega
    have H0 := t.center_snc 0 ht
    rw [t.proj_zero, t.boundary_zero] at H0
    have H1 := hasStrictNormalCrossingsWith_comap_iso_inv_consolidated209 hinv t.toBlowupSequenceData.isoZero
      (s.proj s.toBlowupSequenceData.length ≫ p) (t.toBlowupSequenceData.center 0)
      (s.boundary s.toBlowupSequenceData.length) H0
    rw [appendProjectionToBase_of_le_length s t (le_refl s.toBlowupSequenceData.length), appendToBlowupSequenceData_center_length s t,
      appendBoundary_of_le_length s t (le_refl s.toBlowupSequenceData.length)]
    simp only [Category.assoc]
    exact hasStrictNormalCrossingsWith_comap_eqToHom_consolidated209
      (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))
      (s.proj s.toBlowupSequenceData.length ≫ p)
      ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv)
      (s.boundary s.toBlowupSequenceData.length) H1
  · have hsub : i - s.toBlowupSequenceData.length < t.toBlowupSequenceData.length := by omega
    rw [appendProjectionToBase_of_length_lt s t h, appendToBlowupSequenceData_center_of_length_lt s t h, appendBoundary_of_length_lt s t h]
    simp only [Category.assoc]
    exact hasStrictNormalCrossingsWith_comap_eqToHom_consolidated209 (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)
      (t.proj (i - s.toBlowupSequenceData.length) ≫ s.proj s.toBlowupSequenceData.length ≫ p)
      (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length))
      (t.boundary (i - s.toBlowupSequenceData.length))
      (t.center_snc (i - s.toBlowupSequenceData.length) hsub)

private theorem comap_comap_inv_hom_consolidated209 {A B : Scheme.{u}} (e : A ≅ B) (D : A.IdealSheafData) :
    (D.comap e.inv).comap e.hom = D := by
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, e.hom_inv_id,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id]

private theorem exceptionalIdeal_pow_mul_comap_eqToHom_consolidated209 {A A' B B' : Scheme.{u}} (eA : A = A')
    (eB : B = B') (g : A' ⟶ B') (Z J : B'.IdealSheafData) (J' : A'.IdealSheafData) (n : ℕ)
    (h : Blowup.exceptionalIdeal g Z ^ n * J' = J.comap g) :
    Blowup.exceptionalIdeal (eqToHom eA ≫ g ≫ eqToHom eB.symm) (Z.comap (eqToHom eB)) ^ n *
        J'.comap (eqToHom eA) =
      (J.comap (eqToHom eB)).comap (eqToHom eA ≫ g ≫ eqToHom eB.symm) := by
  subst eA
  subst eB
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id]
  exact h

theorem exceptionalIdeal_pow_mul_appendIdeal_succ (_hinv : ComapIsoInvariance.{u}) (i : ℕ)
    (hi : i < (s.appendToBlowupSequenceData t).length) :
    Blowup.exceptionalIdeal ((s.appendToBlowupSequenceData t).map i) ((s.appendToBlowupSequenceData t).center i) ^ m *
        s.appendIdeal t (i + 1) =
      (s.appendIdeal t i).comap ((s.appendToBlowupSequenceData t).map i) := by
  have hi' : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := hi
  rcases lt_trichotomy i s.toBlowupSequenceData.length with h | h | h
  · have h1 : i + 1 ≤ s.toBlowupSequenceData.length := h
    rw [appendToBlowupSequenceData_blowupMorphism_of_lt_length s t h, appendToBlowupSequenceData_center_of_lt_length s t h, appendIdeal_of_le_length s t h1,
      appendIdeal_of_le_length s t (le_of_lt h)]
    exact exceptionalIdeal_pow_mul_comap_eqToHom_consolidated209 (appendToBlowupSequenceData_schemeAt_succ_of_lt_length s t h)
      (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h)) (s.toBlowupSequenceData.map i) (s.toBlowupSequenceData.center i)
      (s.ideal i) (s.ideal (i + 1)) m (s.ideal_succ i h)
  · subst h
    have ht0 : 0 < t.toBlowupSequenceData.length := by omega
    have hExceptional : Blowup.exceptionalIdeal (t.toBlowupSequenceData.map 0 ≫ t.toBlowupSequenceData.isoZero.hom)
        ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv) ^ m * t.ideal 1 =
        (s.ideal s.toBlowupSequenceData.length).comap
          (t.toBlowupSequenceData.map 0 ≫ t.toBlowupSequenceData.isoZero.hom) := by
      rw [Blowup.exceptionalIdeal_eq_comap,
        AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
        AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
        comap_comap_inv_hom_consolidated209 t.toBlowupSequenceData.isoZero (t.toBlowupSequenceData.center 0),
        ← t.ideal_zero]
      simpa only [Blowup.exceptionalIdeal_eq_comap, zero_add] using t.ideal_succ 0 ht0
    rw [appendToBlowupSequenceData_blowupMorphism_length s t, appendToBlowupSequenceData_center_length s t,
      appendIdeal_length_succ s t, appendIdeal_of_le_length s t (le_refl s.toBlowupSequenceData.length),
      ← Category.assoc (t.toBlowupSequenceData.map 0) t.toBlowupSequenceData.isoZero.hom]
    exact exceptionalIdeal_pow_mul_comap_eqToHom_consolidated209 (appendToBlowupSequenceData_schemeAt_length_succ s t)
      (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))
      (t.toBlowupSequenceData.map 0 ≫ t.toBlowupSequenceData.isoZero.hom)
      ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv)
      (s.ideal s.toBlowupSequenceData.length) (t.ideal 1) m hExceptional
  · have h1 : s.toBlowupSequenceData.length < i + 1 := by omega
    have hsub : i - s.toBlowupSequenceData.length < t.toBlowupSequenceData.length := by omega
    have hidx : s.appendIdeal t (i + 1) =
        (t.ideal (i - s.toBlowupSequenceData.length + 1)).comap
          (eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h)) := by
      rw [appendIdeal_of_length_lt s t h1]
      exact comap_eqToHom_congr_consolidated209 (fun n => t.toBlowupSequenceData.obj n)
        (fun n => t.ideal n) (by omega) (appendToBlowupSequenceData_schemeAt_of_length_lt s t h1)
        (appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h)
    rw [appendToBlowupSequenceData_blowupMorphism_of_length_lt s t h, appendToBlowupSequenceData_center_of_length_lt s t h, hidx, appendIdeal_of_length_lt s t h]
    exact exceptionalIdeal_pow_mul_comap_eqToHom_consolidated209 (appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h)
      (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)
      (t.toBlowupSequenceData.map (i - s.toBlowupSequenceData.length))
      (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length))
      (t.ideal (i - s.toBlowupSequenceData.length))
      (t.ideal (i - s.toBlowupSequenceData.length + 1)) m
      (t.ideal_succ (i - s.toBlowupSequenceData.length) hsub)

private theorem map_strictTransform_comap_eqToHom_consolidated209 {A A' B B' : Scheme.{u}}
    (hA : A = A') (hB : B = B') (f : A' ⟶ B') (Z : B'.IdealSheafData)
    (Lst : List B'.IdealSheafData) (Lst1 : List A'.IdealSheafData)
    (hL : Lst1 = Lst.map (Blowup.strictTransform f Z) ++ [Blowup.exceptionalIdeal f Z]) :
    Lst1.map (fun D => D.comap (eqToHom hA)) =
      (Lst.map (fun D => D.comap (eqToHom hB))).map
          (Blowup.strictTransform (eqToHom hA ≫ f ≫ eqToHom hB.symm) (Z.comap (eqToHom hB))) ++
        [Blowup.exceptionalIdeal (eqToHom hA ≫ f ≫ eqToHom hB.symm) (Z.comap (eqToHom hB))] := by
  subst hA
  subst hB
  subst hL
  simp [AlgebraicGeometry.Scheme.IdealSheafData.comap_id]

section
variable (hinv : ComapIsoInvariance.{u})
include hinv

private theorem map_strictTransform_comp_iso_hom_consolidated209 {A B C : Scheme.{u}}
    (f : A ⟶ B) (e : B ≅ C) (Z : B.IdealSheafData) (Lst : List C.IdealSheafData)
    (Lst1 : List A.IdealSheafData)
    (hL1 : Lst1 = (Lst.map (fun D => D.comap e.hom)).map (Blowup.strictTransform f Z) ++
      [Blowup.exceptionalIdeal f Z]) :
    Lst1 = Lst.map (Blowup.strictTransform (f ≫ e.hom) (Z.comap e.inv)) ++
      [Blowup.exceptionalIdeal (f ≫ e.hom) (Z.comap e.inv)] := by
  have hZ : (Z.comap e.inv).comap e.hom = Z := by
    rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, e.hom_inv_id,
      AlgebraicGeometry.Scheme.IdealSheafData.comap_id]
  have hfun : (Blowup.strictTransform f Z) ∘ (fun D : C.IdealSheafData => D.comap e.hom) =
      Blowup.strictTransform (f ≫ e.hom) (Z.comap e.inv) := by
    funext D
    show Blowup.strictTransform f Z (D.comap e.hom) =
      Blowup.strictTransform (f ≫ e.hom) (Z.comap e.inv) D
    rw [hinv.strictTransform_comap f e (Z.comap e.inv) D, hZ]
  have hexc : Blowup.exceptionalIdeal (f ≫ e.hom) (Z.comap e.inv) = Blowup.exceptionalIdeal f Z := by
    rw [Blowup.exceptionalIdeal_eq_comap, Blowup.exceptionalIdeal_eq_comap,
      AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hZ]
  rw [hL1, List.map_map, hfun, hexc]

private theorem appendBoundary_succ_consolidated209 (i : ℕ)
    (hi : i < (s.appendToBlowupSequenceData t).length) :
    s.appendBoundary t (i + 1) =
      (s.appendBoundary t i).map
          (Blowup.strictTransform ((s.appendToBlowupSequenceData t).map i) ((s.appendToBlowupSequenceData t).center i)) ++
        [Blowup.exceptionalIdeal ((s.appendToBlowupSequenceData t).map i) ((s.appendToBlowupSequenceData t).center i)] := by
  have hi' : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := hi
  rcases lt_trichotomy i s.toBlowupSequenceData.length with h | h | h
  · have h1 : i + 1 ≤ s.toBlowupSequenceData.length := by omega
    rw [appendBoundary_of_le_length s t h1, appendBoundary_of_le_length s t (le_of_lt h),
      appendToBlowupSequenceData_blowupMorphism_of_lt_length s t h, appendToBlowupSequenceData_center_of_lt_length s t h]
    exact map_strictTransform_comap_eqToHom_consolidated209 (appendToBlowupSequenceData_schemeAt_succ_of_lt_length s t h)
      (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h)) (s.toBlowupSequenceData.map i) (s.toBlowupSequenceData.center i)
      (s.boundary i) (s.boundary (i + 1)) (s.boundary_succ i h)
  · subst h
    have ht0 : 0 < t.toBlowupSequenceData.length := by omega
    have hbs : t.boundary 1 =
        (t.boundary 0).map
            (Blowup.strictTransform (t.toBlowupSequenceData.map 0) (t.toBlowupSequenceData.center 0)) ++
          [Blowup.exceptionalIdeal (t.toBlowupSequenceData.map 0) (t.toBlowupSequenceData.center 0)] :=
      t.boundary_succ 0 ht0
    have hL1 : t.boundary 1 =
        ((s.boundary s.toBlowupSequenceData.length).map
            (fun D => D.comap t.toBlowupSequenceData.isoZero.hom)).map
            (Blowup.strictTransform (t.toBlowupSequenceData.map 0) (t.toBlowupSequenceData.center 0)) ++
          [Blowup.exceptionalIdeal (t.toBlowupSequenceData.map 0) (t.toBlowupSequenceData.center 0)] := by
      rw [hbs, t.boundary_zero]
    have hb1 := map_strictTransform_comp_iso_hom_consolidated209 hinv (t.toBlowupSequenceData.map 0) t.toBlowupSequenceData.isoZero
      (t.toBlowupSequenceData.center 0) (s.boundary s.toBlowupSequenceData.length) (t.boundary 1) hL1
    rw [appendBoundary_length_succ s t,
      appendBoundary_of_le_length s t (le_refl s.toBlowupSequenceData.length),
      appendToBlowupSequenceData_blowupMorphism_length s t, appendToBlowupSequenceData_center_length s t,
      ← Category.assoc (t.toBlowupSequenceData.map 0) t.toBlowupSequenceData.isoZero.hom]
    exact map_strictTransform_comap_eqToHom_consolidated209 (appendToBlowupSequenceData_schemeAt_length_succ s t)
      (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))
      (t.toBlowupSequenceData.map 0 ≫ t.toBlowupSequenceData.isoZero.hom)
      ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv)
      (s.boundary s.toBlowupSequenceData.length) (t.boundary 1) hb1
  · have hlt : i - s.toBlowupSequenceData.length < t.toBlowupSequenceData.length := by omega
    have hsucc : s.toBlowupSequenceData.length < i + 1 := by omega
    have hidx : i + 1 - s.toBlowupSequenceData.length = i - s.toBlowupSequenceData.length + 1 := by omega
    rw [appendBoundary_of_length_lt s t hsucc, appendBoundary_of_length_lt s t h,
      appendToBlowupSequenceData_blowupMorphism_of_length_lt s t h, appendToBlowupSequenceData_center_of_length_lt s t h,
      map_comap_eqToHom_congr_consolidated209 (A := (s.appendToBlowupSequenceData t).obj (i + 1))
        (F := t.toBlowupSequenceData.obj) t.boundary
        (i + 1 - s.toBlowupSequenceData.length) (i - s.toBlowupSequenceData.length + 1) hidx
        (appendToBlowupSequenceData_schemeAt_of_length_lt s t hsucc) (appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h)]
    exact map_strictTransform_comap_eqToHom_consolidated209 (appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h)
      (appendToBlowupSequenceData_schemeAt_of_length_lt s t h) (t.toBlowupSequenceData.map (i - s.toBlowupSequenceData.length))
      (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length))
      (t.boundary (i - s.toBlowupSequenceData.length))
      (t.boundary (i - s.toBlowupSequenceData.length + 1))
      (t.boundary_succ (i - s.toBlowupSequenceData.length) hlt)


end

def append (hinv : ComapIsoInvariance.{u}) : MarkedBlowupSequenceData p I m E where
  toBlowupSequenceData := s.appendToBlowupSequenceData t
  proj := s.appendProjectionToBase t
  proj_zero := appendProjectionToBase_zero s t
  proj_succ := appendProjectionToBase_succ s t
  ideal := s.appendIdeal t
  boundary := s.appendBoundary t
  ideal_zero := appendIdeal_zero s t
  boundary_zero := appendBoundary_zero s t
  center_order := fun i hi => center_support_subset_orderAtLeastLocus_appendIdeal s t hinv i hi
  center_smooth := fun i hi => smooth_center_comp_appendProjectionToBase_consolidated209 s t hinv i hi
  center_snc := fun i hi => hasStrictNormalCrossingsWith_appendBoundary_consolidated209 s t hinv i hi
  ideal_succ := fun i hi => exceptionalIdeal_pow_mul_appendIdeal_succ s t hinv i hi
  boundary_succ := fun i hi => appendBoundary_succ_consolidated209 s t hinv i hi

@[simp]
theorem append_toBlowupSequenceData (hinv : ComapIsoInvariance.{u}) :
    (s.append t hinv).toBlowupSequenceData = s.appendToBlowupSequenceData t := rfl

@[simp]
theorem append_length (hinv : ComapIsoInvariance.{u}) :
    (s.append t hinv).toBlowupSequenceData.length =
      s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := rfl

section
variable (hinv : ComapIsoInvariance.{u}) (i : ℕ)

theorem append_projectionToBase :
    (s.append t hinv).proj i = s.appendProjectionToBase t i := rfl

theorem append_ideal :
    (s.append t hinv).ideal i = s.appendIdeal t i := rfl

theorem append_boundary :
    (s.append t hinv).boundary i = s.appendBoundary t i := rfl


end

section
variable (hinv : ComapIsoInvariance.{u}) {i : ℕ}

theorem append_schemeAt_of_le_length (h : i ≤ s.toBlowupSequenceData.length) :
    (s.append t hinv).toBlowupSequenceData.obj i = s.toBlowupSequenceData.obj i :=
  appendToBlowupSequenceData_schemeAt_of_le_length s t h

theorem append_schemeAt_of_length_lt (h : s.toBlowupSequenceData.length < i) :
    (s.append t hinv).toBlowupSequenceData.obj i =
      t.toBlowupSequenceData.obj (i - s.toBlowupSequenceData.length) :=
  appendToBlowupSequenceData_schemeAt_of_length_lt s t h


end

section
variable (hinv : ComapIsoInvariance.{u}) (h : 0 < t.toBlowupSequenceData.length)

theorem append_ideal_length_add_length :
    (s.append t hinv).ideal (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length) =
      (t.ideal t.toBlowupSequenceData.length).comap (eqToHom (appendToBlowupSequenceData_schemeAt_length_add_length s t h)) := by
  have hgt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := by omega
  have key : s.appendIdeal t (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length) =
      (t.ideal t.toBlowupSequenceData.length).comap (eqToHom (appendToBlowupSequenceData_schemeAt_length_add_length s t h)) := by
    rw [appendIdeal_of_length_lt s t hgt]
    exact comap_eqToHom_congr_consolidated209 (fun n => t.toBlowupSequenceData.obj n)
      (fun n => t.ideal n) (by omega) (appendToBlowupSequenceData_schemeAt_of_length_lt s t hgt)
      (appendToBlowupSequenceData_schemeAt_length_add_length s t h)
  exact key

theorem append_boundary_length_add_length :
    (s.append t hinv).boundary (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length) =
      (t.boundary t.toBlowupSequenceData.length).map
        (fun D => D.comap (eqToHom (appendToBlowupSequenceData_schemeAt_length_add_length s t h))) := by
  have hgt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := by omega
  show s.appendBoundary t (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length) =
      (t.boundary t.toBlowupSequenceData.length).map
        (fun D => D.comap (eqToHom (appendToBlowupSequenceData_schemeAt_length_add_length s t h)))
  refine (appendBoundary_of_length_lt s t hgt).trans ?_
  exact map_comap_eqToHom_congr_consolidated209
    (A := (s.appendToBlowupSequenceData t).obj (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length))
    (F := fun n => t.toBlowupSequenceData.obj n) (fun n => t.boundary n)
    (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length - s.toBlowupSequenceData.length)
    t.toBlowupSequenceData.length (by omega)
    (appendToBlowupSequenceData_schemeAt_of_length_lt s t hgt) (appendToBlowupSequenceData_schemeAt_length_add_length s t h)


end

end MarkedBlowupSequenceData

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SingleBlowup
section


section
namespace FunctorialResolution.EmbeddedResolution

open Classical in
noncomputable def residualByPow {Y : Scheme.{u}} (A F : Y.IdealSheafData) (m : ℕ) : Y.IdealSheafData :=
  if h : ∃ B : Y.IdealSheafData, F ^ m * B = A then h.choose else ⊤

theorem pow_mul_residualByPow {Y : Scheme.{u}} (A F : Y.IdealSheafData) (m : ℕ)
    (h : ∃ B : Y.IdealSheafData, F ^ m * B = A) : F ^ m * residualByPow A F m = A := by
  have hx : residualByPow A F m = h.choose := dif_pos h
  rw [hx]
  exact h.choose_spec

private theorem map_comap_id_list_idealSheafData_consolidated210 {X : Scheme.{u}} (E : List X.IdealSheafData) :
    E.map (fun D => D.comap (𝟙 X)) = E := by
  induction E with
  | nil => rfl
  | cons a t ih => simp [Scheme.IdealSheafData.comap_id]

@[simp]
theorem exceptionalIdeal_id {X : Scheme.{u}} (Z : X.IdealSheafData) :
    Blowup.exceptionalIdeal (𝟙 X) Z = Z := by
  rw [Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id]

private def singleBlowupScheme_consolidated210 {X : Scheme.{u}} (Z : X.IdealSheafData) : ℕ → Scheme.{u}
  | 0 => X
  | (_ + 1) => Blowup.blowup Z

private def singleBlowupMap_consolidated210 {X : Scheme.{u}} (Z : X.IdealSheafData) :
    ∀ i : ℕ, singleBlowupScheme_consolidated210 Z (i + 1) ⟶ singleBlowupScheme_consolidated210 Z i
  | 0 => Blowup.blowup.proj Z
  | (_ + 1) => 𝟙 (Blowup.blowup Z)

private def singleBlowupCenter_consolidated210 {X : Scheme.{u}} (Z : X.IdealSheafData) :
    ∀ i : ℕ, (singleBlowupScheme_consolidated210 Z i).IdealSheafData
  | 0 => Z
  | (_ + 1) => ⊤

private def singleBlowupProj_consolidated210 {X : Scheme.{u}} (Z : X.IdealSheafData) : ∀ i : ℕ, singleBlowupScheme_consolidated210 Z i ⟶ X
  | 0 => 𝟙 X
  | (_ + 1) => Blowup.blowup.proj Z

private def singleBlowupResidualIdeal_consolidated210 {X : Scheme.{u}} (I Z : X.IdealSheafData) (m : ℕ) :
    ∀ i : ℕ, (singleBlowupScheme_consolidated210 Z i).IdealSheafData
  | 0 => I.comap (𝟙 X)
  | (_ + 1) => residualByPow (I.comap (Blowup.blowup.proj Z)) (Z.comap (Blowup.blowup.proj Z)) m

private def singleBlowupBoundary_consolidated210 {X : Scheme.{u}} (Z : X.IdealSheafData) (E : List X.IdealSheafData) :
    ∀ i : ℕ, List (singleBlowupScheme_consolidated210 Z i).IdealSheafData
  | 0 => E.map (fun D => D.comap (𝟙 X))
  | (_ + 1) =>
      E.map (Blowup.strictTransform (Blowup.blowup.proj Z) Z) ++ [Blowup.exceptionalIdeal (Blowup.blowup.proj Z) Z]

private theorem isBlowupAlongIdealSheaf_singleBlowupMap_consolidated210 {X : Scheme.{u}} (Z : X.IdealSheafData) (i : ℕ) (hi : i < 1) :
    Blowup.IsBlowupAlongIdealSheaf (singleBlowupMap_consolidated210 Z i) (singleBlowupCenter_consolidated210 Z i) := by
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  show Blowup.IsBlowupAlongIdealSheaf (Blowup.blowup.proj Z) Z
  exact Blowup.blowup.isBlowupAlongIdealSheaf_proj Z

private def singleBlowupSequenceData_consolidated210 {X : Scheme.{u}} (Z : X.IdealSheafData) : BlowupSequenceData X where
  length := 1
  obj := singleBlowupScheme_consolidated210 Z
  map := singleBlowupMap_consolidated210 Z
  isoZero := Iso.refl X
  center := singleBlowupCenter_consolidated210 Z
  isBlowup := fun i hi => isBlowupAlongIdealSheaf_singleBlowupMap_consolidated210 Z i hi

section
variable {X : Scheme.{u}}

private theorem singleBlowupProj_succ_consolidated210 (Z : X.IdealSheafData) (i : ℕ) :
    singleBlowupProj_consolidated210 Z (i + 1) = singleBlowupMap_consolidated210 Z i ≫ singleBlowupProj_consolidated210 Z i := by
  cases i with
  | zero =>
      show Blowup.blowup.proj Z = Blowup.blowup.proj Z ≫ 𝟙 X
      exact (Category.comp_id _).symm
  | succ j =>
      show Blowup.blowup.proj Z = 𝟙 (Blowup.blowup Z) ≫ Blowup.blowup.proj Z
      exact (Category.id_comp _).symm

private theorem singleBlowupCenter_support_subset_orderAtLeastLocus_consolidated210 (I Z : X.IdealSheafData) (m : ℕ)
    (hord : (Z.support : Set ↥X) ⊆ orderAtLeastLocus I m) :
    ∀ i : ℕ, i < 1 →
      ((singleBlowupCenter_consolidated210 Z i).support : Set ↥(singleBlowupScheme_consolidated210 Z i)) ⊆ orderAtLeastLocus (singleBlowupResidualIdeal_consolidated210 I Z m i) m := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  show (Z.support : Set ↥X) ⊆ orderAtLeastLocus (I.comap (𝟙 X)) m
  rw [Scheme.IdealSheafData.comap_id]
  exact hord


end

section
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} (Z : X.IdealSheafData)

private theorem smooth_singleBlowupCenter_of_smooth_consolidated210 (hsm : Smooth (Z.subschemeι ≫ p)) :
    ∀ i : ℕ, i < 1 →
      Smooth ((singleBlowupCenter_consolidated210 Z i).subschemeι ≫ singleBlowupProj_consolidated210 Z i ≫ p) := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  show Smooth (Z.subschemeι ≫ 𝟙 X ≫ p)
  rw [Category.id_comp]
  exact hsm

private theorem hasStrictNormalCrossingsWith_singleBlowupCenter_consolidated210 (E : List X.IdealSheafData)
    (hsnc : HasStrictNormalCrossingsWith p Z E) :
    ∀ i : ℕ, i < 1 →
      HasStrictNormalCrossingsWith (singleBlowupProj_consolidated210 Z i ≫ p) (singleBlowupCenter_consolidated210 Z i) (singleBlowupBoundary_consolidated210 Z E i) := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  show HasStrictNormalCrossingsWith (𝟙 X ≫ p) Z (E.map (fun D => D.comap (𝟙 X)))
  rw [map_comap_id_list_idealSheafData_consolidated210 E, Category.id_comp]
  exact hsnc


end

section
variable {X : Scheme.{u}}

private theorem exceptionalIdeal_pow_mul_singleBlowupResidualIdeal_succ_consolidated210 (I Z : X.IdealSheafData) (m : ℕ)
    (hdiv : ∃ B : (Blowup.blowup Z).IdealSheafData,
      (Z.comap (Blowup.blowup.proj Z)) ^ m * B = I.comap (Blowup.blowup.proj Z)) :
    ∀ i : ℕ, i < 1 →
      Blowup.exceptionalIdeal (singleBlowupMap_consolidated210 Z i) (singleBlowupCenter_consolidated210 Z i) ^ m * singleBlowupResidualIdeal_consolidated210 I Z m (i + 1) =
        (singleBlowupResidualIdeal_consolidated210 I Z m i).comap (singleBlowupMap_consolidated210 Z i) := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  show Blowup.exceptionalIdeal (Blowup.blowup.proj Z) Z ^ m *
      residualByPow (I.comap (Blowup.blowup.proj Z)) (Z.comap (Blowup.blowup.proj Z)) m =
    (I.comap (𝟙 X)).comap (Blowup.blowup.proj Z)
  rw [Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id]
  exact pow_mul_residualByPow _ _ _ hdiv

private theorem singleBlowupBoundary_succ_consolidated210 (Z : X.IdealSheafData)
    (E : List X.IdealSheafData) :
    ∀ i : ℕ, i < 1 →
      singleBlowupBoundary_consolidated210 Z E (i + 1) =
        (singleBlowupBoundary_consolidated210 Z E i).map (Blowup.strictTransform (singleBlowupMap_consolidated210 Z i) (singleBlowupCenter_consolidated210 Z i)) ++
          [Blowup.exceptionalIdeal (singleBlowupMap_consolidated210 Z i) (singleBlowupCenter_consolidated210 Z i)] := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  show E.map (Blowup.strictTransform (Blowup.blowup.proj Z) Z) ++ [Blowup.exceptionalIdeal (Blowup.blowup.proj Z) Z] =
      (E.map (fun D => D.comap (𝟙 X))).map (Blowup.strictTransform (Blowup.blowup.proj Z) Z) ++
        [Blowup.exceptionalIdeal (Blowup.blowup.proj Z) Z]
  rw [map_comap_id_list_idealSheafData_consolidated210 E]


end

namespace MarkedBlowupSequenceData

def ofSingleBlowup {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (Z : X.IdealSheafData)
    (hsm : Smooth (Z.subschemeι ≫ p))
    (hsnc : HasStrictNormalCrossingsWith p Z E)
    (hord : (Z.support : Set ↥X) ⊆ orderAtLeastLocus I m)
    (hdiv : ∃ B : (Blowup.blowup Z).IdealSheafData,
      (Z.comap (Blowup.blowup.proj Z)) ^ m * B = I.comap (Blowup.blowup.proj Z)) :
    MarkedBlowupSequenceData p I m E where
  toBlowupSequenceData := singleBlowupSequenceData_consolidated210 Z
  proj := singleBlowupProj_consolidated210 Z
  proj_zero := rfl
  proj_succ := fun i => singleBlowupProj_succ_consolidated210 Z i
  ideal := singleBlowupResidualIdeal_consolidated210 I Z m
  boundary := singleBlowupBoundary_consolidated210 Z E
  ideal_zero := rfl
  boundary_zero := rfl
  center_order := singleBlowupCenter_support_subset_orderAtLeastLocus_consolidated210 I Z m hord
  center_smooth := smooth_singleBlowupCenter_of_smooth_consolidated210 Z hsm
  center_snc := hasStrictNormalCrossingsWith_singleBlowupCenter_consolidated210 Z E hsnc
  ideal_succ := exceptionalIdeal_pow_mul_singleBlowupResidualIdeal_succ_consolidated210 I Z m hdiv
  boundary_succ := singleBlowupBoundary_succ_consolidated210 Z E

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} {Z : X.IdealSheafData}
  (hsm : Smooth (Z.subschemeι ≫ p)) (hsnc : HasStrictNormalCrossingsWith p Z E)
  (hord : (Z.support : Set ↥X) ⊆ orderAtLeastLocus I m)
  (hdiv : ∃ B : (Blowup.blowup Z).IdealSheafData,
    (Z.comap (Blowup.blowup.proj Z)) ^ m * B = I.comap (Blowup.blowup.proj Z))

@[simp]
theorem ofSingleBlowup_length :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).toBlowupSequenceData.length = 1 := rfl

@[simp]
theorem ofSingleBlowup_schemeAt_succ (i : ℕ) :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).toBlowupSequenceData.obj (i + 1) = Blowup.blowup Z := rfl

theorem ofSingleBlowup_schemeAt_zero :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).toBlowupSequenceData.obj 0 = X := rfl

theorem ofSingleBlowup_projectionToBase_one :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).proj 1 = Blowup.blowup.proj Z := rfl

theorem ofSingleBlowup_center_zero :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).toBlowupSequenceData.center 0 = Z := rfl

theorem ofSingleBlowup_ideal_one :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).ideal 1 =
      residualByPow (I.comap (Blowup.blowup.proj Z)) (Z.comap (Blowup.blowup.proj Z)) m := rfl

theorem ofSingleBlowup_boundary_one :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).boundary 1 =
      E.map (Blowup.strictTransform (Blowup.blowup.proj Z) Z) ++ [Blowup.exceptionalIdeal (Blowup.blowup.proj Z) Z] := rfl

end MarkedBlowupSequenceData

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
section


section
namespace FunctorialResolution.EmbeddedResolution

noncomputable def BlowupSequenceData.controlledTransform {X : Scheme.{u}} (d : BlowupSequenceData X)
    (I : X.IdealSheafData) (m : ℕ) : ∀ i : ℕ, (d.obj i).IdealSheafData
  | 0 => I.comap d.isoZero.hom
  | (i + 1) =>
      residualByPow ((d.controlledTransform I m i).comap (d.map i))
        (Blowup.exceptionalIdeal (d.map i) (d.center i)) m

@[simp]
theorem BlowupSequenceData.controlledTransform_zero {X : Scheme.{u}} (d : BlowupSequenceData X)
    (I : X.IdealSheafData) (m : ℕ) :
    d.controlledTransform I m 0 = I.comap d.isoZero.hom := rfl

@[simp]
theorem BlowupSequenceData.controlledTransform_succ {X : Scheme.{u}} (d : BlowupSequenceData X)
    (I : X.IdealSheafData) (m : ℕ) (i : ℕ) :
    d.controlledTransform I m (i + 1) =
      residualByPow ((d.controlledTransform I m i).comap (d.map i))
        (Blowup.exceptionalIdeal (d.map i) (d.center i)) m := rfl

theorem BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ {X : Scheme.{u}} (d : BlowupSequenceData X)
    (I : X.IdealSheafData) (m : ℕ) (i : ℕ)
    (h : ∃ B : (d.obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * B =
        (d.controlledTransform I m i).comap (d.map i)) :
    Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * d.controlledTransform I m (i + 1) =
      (d.controlledTransform I m i).comap (d.map i) := by
  rw [d.controlledTransform_succ I m i]
  exact pow_mul_residualByPow _ _ m h

noncomputable def BlowupSequenceData.boundaryFrom {X : Scheme.{u}} (d : BlowupSequenceData X)
    (E : List X.IdealSheafData) : ∀ i : ℕ, List (d.obj i).IdealSheafData
  | 0 => E.map (fun D => D.comap d.isoZero.hom)
  | (i + 1) =>
      (d.boundaryFrom E i).map (Blowup.strictTransform (d.map i) (d.center i)) ++
        [Blowup.exceptionalIdeal (d.map i) (d.center i)]

@[simp]
theorem BlowupSequenceData.boundary_zero {X : Scheme.{u}} (d : BlowupSequenceData X)
    (E : List X.IdealSheafData) :
    d.boundaryFrom E 0 = E.map (fun D => D.comap d.isoZero.hom) := rfl

@[simp]
theorem BlowupSequenceData.boundary_succ {X : Scheme.{u}} (d : BlowupSequenceData X)
    (E : List X.IdealSheafData) (i : ℕ) :
    d.boundaryFrom E (i + 1) =
      (d.boundaryFrom E i).map (Blowup.strictTransform (d.map i) (d.center i)) ++
        [Blowup.exceptionalIdeal (d.map i) (d.center i)] := rfl

theorem BlowupSequenceData.boundary_length {X : Scheme.{u}} (d : BlowupSequenceData X)
    (E : List X.IdealSheafData) (i : ℕ) :
    (d.boundaryFrom E i).length = E.length + i := by
  induction i with
  | zero =>
      rw [d.boundary_zero E, List.length_map]
      omega
  | succ j ih =>
      rw [d.boundary_succ E j, List.length_append, List.length_map, ih,
        List.length_cons, List.length_nil]
      omega

structure BlowupSequenceData.IsMarked {k : Type u} [Field k] {X : Scheme.{u}} (d : BlowupSequenceData X)
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) : Prop where
  divisible : ∀ i < d.length, ∃ B : (d.obj (i + 1)).IdealSheafData,
    Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * B =
      (d.controlledTransform I m i).comap (d.map i)
  center_order : ∀ i < d.length,
    ((d.center i).support : Set ↥(d.obj i)) ⊆ orderAtLeastLocus (d.controlledTransform I m i) m
  center_smooth : ∀ i < d.length,
    Smooth ((d.center i).subschemeι ≫ d.projectionToBase i ≫ p)
  center_snc : ∀ i < d.length,
    HasStrictNormalCrossingsWith (d.projectionToBase i ≫ p) (d.center i) (d.boundaryFrom E i)

noncomputable def BlowupSequenceData.toMarkedBlowupSequenceData {k : Type u} [Field k] {X : Scheme.{u}}
    (d : BlowupSequenceData X) (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (h : d.IsMarked p I m E) : MarkedBlowupSequenceData p I m E where
  toBlowupSequenceData := d
  proj := d.projectionToBase
  proj_zero := d.projectionToBase_zero
  proj_succ := d.projectionToBase_succ
  ideal := d.controlledTransform I m
  boundary := d.boundaryFrom E
  ideal_zero := rfl
  boundary_zero := rfl
  center_order := h.center_order
  center_smooth := h.center_smooth
  center_snc := h.center_snc
  ideal_succ := fun i hi => d.pow_exceptionalIdeal_mul_controlledTransform_succ I m i (h.divisible i hi)
  boundary_succ := fun i _ => d.boundary_succ E i

section

variable {k : Type u} [Field k] {X : Scheme.{u}} (d : BlowupSequenceData X)
  (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
  (E : List X.IdealSheafData) (h : d.IsMarked p I m E)

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_toBlowupSequenceData :
    (d.toMarkedBlowupSequenceData p I m E h).toBlowupSequenceData = d := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_length :
    (d.toMarkedBlowupSequenceData p I m E h).length = d.length := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_center (i : ℕ) :
    (d.toMarkedBlowupSequenceData p I m E h).center i = d.center i := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_blowupMorphism (i : ℕ) :
    (d.toMarkedBlowupSequenceData p I m E h).map i = d.map i := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_projectionToBase (i : ℕ) :
    (d.toMarkedBlowupSequenceData p I m E h).proj i = d.projectionToBase i := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_ideal (i : ℕ) :
    (d.toMarkedBlowupSequenceData p I m E h).ideal i = d.controlledTransform I m i := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_boundary (i : ℕ) :
    (d.toMarkedBlowupSequenceData p I m E h).boundary i = d.boundaryFrom E i := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups :
    (d.toMarkedBlowupSequenceData p I m E h).toMarkedSequenceOfBlowups.toSequenceOfBlowups = d.toSequenceOfBlowups :=
  MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups _

end

section
variable {R : Type u} [CommRing R] {f : R} (hf : f ∈ nonZeroDivisors R) {I J : Ideal R} (h : Ideal.span ({f} : Set R) * I = Ideal.span ({f} : Set R) * J)
include hf h

private theorem le_of_span_singleton_mul_eq_mul_consolidated228 : I ≤ J := by
  intro a ha
  have h1 : f * a ∈ Ideal.span ({f} : Set R) * J := by
    rw [← h]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self f) ha
  obtain ⟨z, hz, hfz⟩ := Ideal.mem_span_singleton_mul.mp h1
  have hza : a = z := ((mul_cancel_left_mem_nonZeroDivisors hf).mp hfz).symm
  rw [hza]
  exact hz

private theorem eq_of_span_singleton_mul_eq_mul_consolidated228 : I = J :=
  le_antisymm (le_of_span_singleton_mul_eq_mul_consolidated228 hf h) (le_of_span_singleton_mul_eq_mul_consolidated228 hf h.symm)


end

section
variable {Y : Scheme.{u}}

private theorem stalkIdeal_eq_of_mul_eq_mul_consolidated228 {F A B : Y.IdealSheafData}
    (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F) (h : F * A = F * B) (x : ↥Y) :
    stalkIdeal A x = stalkIdeal B x := by
  obtain ⟨U, f, hxU, hf, hFU⟩ := hF x
  let _ : Algebra ↑(Y.presheaf.obj (Opposite.op (U : Y.Opens))) ↑(Y.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨x, hxU⟩ : ↥(U : Y.Opens))
  have : IsLocalization
      (IsAffineOpen.primeIdealOf U.2 (⟨x, hxU⟩ : ↥(U : Y.Opens))).asIdeal.primeCompl
      ↑(Y.presheaf.stalk x) :=
    IsAffineOpen.isLocalization_stalk U.2 (⟨x, hxU⟩ : ↥(U : Y.Opens))
  have hnzd : (CommRingCat.Hom.hom (Y.presheaf.germ (U : Y.Opens) x hxU)) f ∈
      nonZeroDivisors ↑(Y.presheaf.stalk x) :=
    IsLocalization.map_nonZeroDivisors_le
      (IsAffineOpen.primeIdealOf U.2 (⟨x, hxU⟩ : ↥(U : Y.Opens))).asIdeal.primeCompl
      ↑(Y.presheaf.stalk x) ⟨f, hf, rfl⟩
  have hstalk : stalkIdeal F x =
      Ideal.span ({(CommRingCat.Hom.hom (Y.presheaf.germ (U : Y.Opens) x hxU)) f} :
        Set ↑(Y.presheaf.stalk x)) := by
    rw [stalkIdeal_eq_map_germ F x U hxU, hFU, Ideal.map_span, Set.image_singleton]
  have hmul : stalkIdeal F x * stalkIdeal A x = stalkIdeal F x * stalkIdeal B x := by
    rw [← stalkIdeal_mul, ← stalkIdeal_mul, h]
  rw [hstalk] at hmul
  exact eq_of_span_singleton_mul_eq_mul_consolidated228 hnzd hmul

private theorem eq_of_stalkIdeal_eq_consolidated228 {A B : Y.IdealSheafData}
    (h : ∀ x : ↥Y, stalkIdeal A x = stalkIdeal B x) : A = B := by
  apply Scheme.IdealSheafData.ext
  funext V
  apply Ideal.eq_of_localization_maximal
  intro P hP
  have : P.IsPrime := hP.isPrime
  have hx : IsAffineOpen.fromSpec V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _) ∈ (V : Y.Opens) := by
    have hr : IsAffineOpen.fromSpec V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _) ∈
        Set.range (IsAffineOpen.fromSpec V.2) := Set.mem_range_self _
    rw [IsAffineOpen.range_fromSpec V.2] at hr
    exact hr
  let _ : Algebra ↑(Y.presheaf.obj (Opposite.op (V : Y.Opens)))
      ↑(Y.presheaf.stalk (IsAffineOpen.fromSpec V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _))) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf
      (⟨IsAffineOpen.fromSpec V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _), hx⟩ : ↥(V : Y.Opens))
  have : IsLocalization P.primeCompl
      ↑(Y.presheaf.stalk (IsAffineOpen.fromSpec V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _))) :=
    IsAffineOpen.isLocalization_stalk' V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _) hx
  have key := h (IsAffineOpen.fromSpec V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _))
  rw [stalkIdeal_eq_map_germ A _ V hx, stalkIdeal_eq_map_germ B _ V hx] at key
  exact IsLocalization.map_eq_map_of_map_eq_map P.primeCompl key


end

theorem isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal {X' X : Scheme.{u}} {f : X' ⟶ X}
    {Z : X.IdealSheafData} (h : Blowup.IsBlowupAlongIdealSheaf f Z) :
    Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal f Z) := by
  rw [Blowup.exceptionalIdeal_eq_comap]
  exact Blowup.IsBlowupAlongIdealSheaf.isLocallyGeneratedByNonZeroDivisor_comap h

theorem isLocallyGeneratedByNonZeroDivisor_pow {Y : Scheme.{u}} {F : Y.IdealSheafData}
    (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F) (m : ℕ) : Blowup.IsLocallyGeneratedByNonZeroDivisor (F ^ m) := by
  intro x
  obtain ⟨U, f, hxU, hf, hFU⟩ := hF x
  refine ⟨U, f ^ m, hxU, pow_mem hf m, ?_⟩
  rw [Scheme.IdealSheafData.ideal_pow]
  show F.ideal U ^ m = _
  rw [hFU, Ideal.span_singleton_pow]

section
variable {Y : Scheme.{u}} {F A B : Y.IdealSheafData} (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F)
include hF

theorem eq_of_isLocallyGeneratedByNonZeroDivisor_mul_eq_mul (h : F * A = F * B) : A = B :=
  eq_of_stalkIdeal_eq_consolidated228 (stalkIdeal_eq_of_mul_eq_mul_consolidated228 hF h)

theorem eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul (m : ℕ) (h : F ^ m * A = F ^ m * B) : A = B :=
  eq_of_isLocallyGeneratedByNonZeroDivisor_mul_eq_mul (isLocallyGeneratedByNonZeroDivisor_pow hF m) h


end

theorem BlowupSequenceData.eq_of_pow_exceptionalIdeal_mul_eq_mul {X : Scheme.{u}} (d : BlowupSequenceData X)
    {i : ℕ} (hi : i < d.length) (m : ℕ) (A B : (d.obj (i + 1)).IdealSheafData)
    (h : Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * A =
      Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * B) : A = B :=
  eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul
    (isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal (d.isBlowup i hi)) m h

namespace MarkedBlowupSequenceData

section
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (s : MarkedBlowupSequenceData p I m E)

theorem projectionToBase_eq_toBlowupSequenceData_projectionToBase (i : ℕ) :
    s.proj i = s.toBlowupSequenceData.projectionToBase i := by
  induction i with
  | zero => rw [s.proj_zero, s.toBlowupSequenceData.projectionToBase_zero]
  | succ j ih => rw [s.proj_succ j, s.toBlowupSequenceData.projectionToBase_succ j, ih]

theorem controlledTransform_and_boundary_eq_of_cancel (huniq : ∀ i < s.length, ∀ A B : (s.obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (s.map i) (s.center i) ^ m * A = (s.ideal i).comap (s.map i) →
      Blowup.exceptionalIdeal (s.map i) (s.center i) ^ m * B = (s.ideal i).comap (s.map i) →
      A = B)
    (i : ℕ) (hi : i ≤ s.length) :
    s.toBlowupSequenceData.controlledTransform I m i = s.ideal i ∧
      s.toBlowupSequenceData.boundaryFrom E i = s.boundary i := by
  revert hi
  induction i with
  | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · rw [BlowupSequenceData.controlledTransform_zero]
        exact s.ideal_zero.symm
      · rw [BlowupSequenceData.boundary_zero]
        exact s.boundary_zero.symm
  | succ j ih =>
      intro hi
      have hj : j < s.length := hi
      obtain ⟨ih1, ih2⟩ := ih (le_of_lt hj)
      refine ⟨?_, ?_⟩
      · rw [BlowupSequenceData.controlledTransform_succ, ih1]
        have hex : ∃ B : (s.obj (j + 1)).IdealSheafData,
            Blowup.exceptionalIdeal (s.map j) (s.center j) ^ m * B =
              (s.ideal j).comap (s.map j) :=
          ⟨s.ideal (j + 1), s.ideal_succ j hj⟩
        exact huniq j hj _ _ (pow_mul_residualByPow _ _ m hex) (s.ideal_succ j hj)
      · rw [BlowupSequenceData.boundary_succ, ih2]
        exact (s.boundary_succ j hj).symm

theorem controlledTransform_and_boundary_eq (i : ℕ) (hi : i ≤ s.length) :
    s.toBlowupSequenceData.controlledTransform I m i = s.ideal i ∧
      s.toBlowupSequenceData.boundaryFrom E i = s.boundary i :=
  s.controlledTransform_and_boundary_eq_of_cancel
    (fun _j hj A B hA hB =>
      s.toBlowupSequenceData.eq_of_pow_exceptionalIdeal_mul_eq_mul hj m A B (hA.trans hB.symm))
    i hi

theorem toBlowupSequenceData_controlledTransform_eq (i : ℕ) (hi : i ≤ s.length) :
    s.toBlowupSequenceData.controlledTransform I m i = s.ideal i :=
  (s.controlledTransform_and_boundary_eq i hi).1

theorem toBlowupSequenceData_boundary_eq_boundary_of_le (i : ℕ) (hi : i ≤ s.length) :
    s.toBlowupSequenceData.boundaryFrom E i = s.boundary i :=
  (s.controlledTransform_and_boundary_eq i hi).2

theorem isMarked_toBlowupSequenceData :
    s.toBlowupSequenceData.IsMarked p I m E := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    refine ⟨s.ideal (i + 1), ?_⟩
    rw [s.toBlowupSequenceData_controlledTransform_eq i (le_of_lt hi)]
    exact s.ideal_succ i hi
  · intro i hi
    rw [s.toBlowupSequenceData_controlledTransform_eq i (le_of_lt hi)]
    exact s.center_order i hi
  · intro i hi
    have h := s.center_smooth i hi
    rw [s.projectionToBase_eq_toBlowupSequenceData_projectionToBase i] at h
    exact h
  · intro i hi
    have h := s.center_snc i hi
    rw [s.projectionToBase_eq_toBlowupSequenceData_projectionToBase i] at h
    rw [s.toBlowupSequenceData_boundary_eq_boundary_of_le i (le_of_lt hi)]
    exact h


end

section
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length)
include hi

theorem ofMarkedSequence_controlledTransform :
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.controlledTransform I m i = s.ideal i :=
  (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData_controlledTransform_eq i hi

theorem ofMarkedSequence_boundary :
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.boundaryFrom E i = s.boundary i :=
  (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData_boundary_eq_boundary_of_le i hi


end

end MarkedBlowupSequenceData

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
section


namespace FunctorialResolution.EmbeddedResolution

variable {X : Scheme.{u}}

def OrderLE (I : X.IdealSheafData) (m : ℕ) : Prop :=
  ∀ x : X, orderAt I x ≤ (m : ℕ∞)

theorem orderLE_iff (I : X.IdealSheafData) (m : ℕ) :
    OrderLE I m ↔ ∀ x : X, orderAt I x ≤ (m : ℕ∞) := Iff.rfl

structure MaxOrderEq (I : X.IdealSheafData) (m : ℕ) : Prop where
  orderLE : OrderLE I m
  coSupport_nonempty : (orderAtLeastLocus I m).Nonempty

def lcmUpTo (m : ℕ) : ℕ := (List.range' 1 m).foldr Nat.lcm 1

theorem lcmUpTo_eq_foldr (m : ℕ) : lcmUpTo m = (List.range' 1 m).foldr Nat.lcm 1 := rfl

theorem lcmUpTo_one : lcmUpTo 1 = 1 := rfl

def tuningExponent (m : ℕ) : ℕ := if m ≤ 1 then 1 else (m - 1) * lcmUpTo m

section
variable {m : ℕ}

theorem tuningExponent_of_le_one (h : m ≤ 1) : tuningExponent m = 1 := by
  unfold tuningExponent
  exact if_pos h

theorem tuningExponent_of_two_le (h : 2 ≤ m) : tuningExponent m = (m - 1) * lcmUpTo m := by
  unfold tuningExponent
  exact if_neg (by omega)


end

theorem tuningExponent_one : tuningExponent 1 = 1 := tuningExponent_of_le_one le_rfl

noncomputable def tunedSheaf (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData)
    (m s : ℕ) : X.IdealSheafData :=
  ⨆ c : {c : ℕ → ℕ // s ≤ ∑ j ∈ Finset.range m, (m - j) * c j},
    ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ (c.1 j))).prod

theorem tunedSheaf_eq_iSup (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData)
    (m s : ℕ) :
    tunedSheaf k p I m s =
      ⨆ c : {c : ℕ → ℕ // s ≤ ∑ j ∈ Finset.range m, (m - j) * c j},
        ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ (c.1 j))).prod := rfl

noncomputable def balancedTunedSheaf (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData)
    (m : ℕ) : X.IdealSheafData :=
  tunedSheaf k p I m (tuningExponent m)

theorem balancedTunedSheaf_eq (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData)
    (m : ℕ) : balancedTunedSheaf k p I m = tunedSheaf k p I m (tuningExponent m) := rfl

def TunedSheafSuccLe : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s : ℕ, tunedSheaf k p I m (s + 1) ≤ tunedSheaf k p I m s

def TunedSheafMulLeAdd : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s t : ℕ, tunedSheaf k p I m s * tunedSheaf k p I m t ≤ tunedSheaf k p I m (s + t)

def DerivIdealSheafTunedSheafSucc : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s : ℕ, derivIdealSheaf k p (tunedSheaf k p I m (s + 1)) = tunedSheaf k p I m s

def MaxContactIdealTunedSheafEq : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s : ℕ, 1 ≤ s →
      derivIdealSheafIterate k p (s - 1) (tunedSheaf k p I m s) =
        derivIdealSheafIterate k p (m - 1) I

def IsMaxContactInvariantTunedSheaf : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s : ℕ, 1 ≤ s →
      derivIdealSheafIterate k p (s - 1) (tunedSheaf k p I m s) *
          derivIdealSheaf k p (tunedSheaf k p I m s) ≤ tunedSheaf k p I m s

def TunedSheafMulEqAdd : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ r t : ℕ, (m - 1) * lcmUpTo m ≤ t →
      tunedSheaf k p I m (r * lcmUpTo m) * tunedSheaf k p I m t =
        tunedSheaf k p I m (r * lcmUpTo m + t)

def TunedSheafPowEqMul : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ r : ℕ, m - 1 ≤ r → ∀ j : ℕ, 1 ≤ j →
      tunedSheaf k p I m (r * lcmUpTo m) ^ j = tunedSheaf k p I m (j * (r * lcmUpTo m))

def IsDerivBalancedTunedSheafMulLcm : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ r : ℕ, m - 1 ≤ r → ∀ i : ℕ, i < r * lcmUpTo m →
      derivIdealSheafIterate k p i (tunedSheaf k p I m (r * lcmUpTo m)) ^ (r * lcmUpTo m) ≤
        tunedSheaf k p I m (r * lcmUpTo m) ^ (r * lcmUpTo m - i)

def CoSupportTunedSheafEqAndOrderLE : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s : ℕ, 1 ≤ s →
      orderAtLeastLocus (tunedSheaf k p I m s) s = orderAtLeastLocus I m ∧ OrderLE (tunedSheaf k p I m s) s

theorem CoSupportTunedSheafEqAndOrderLE.orderLE (h : CoSupportTunedSheafEqAndOrderLE.{u}) (k : Type u) [Field k]
    [CharZero k] [IsNoetherianRing k] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p] (I : X.IdealSheafData) (m : ℕ)
    (hm : 1 ≤ m) (hmax : MaxOrderEq I m) (s : ℕ) (hs : 1 ≤ s) :
    OrderLE (tunedSheaf k p I m s) s :=
  (h k X p I m hm hmax s hs).2

def IsMarkedIffOfPowLeOfLeTunedSheaf : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s : ℕ, 1 ≤ s → ∀ J : X.IdealSheafData, I ^ s ≤ J → J ≤ tunedSheaf k p I m (m * s) →
      ∀ (E : List X.IdealSheafData) (d : BlowupSequenceData X),
        (d.IsMarked p I m E ↔ d.IsMarked p J (m * s) E) ∧
        (d.IsMarked p I m E → ∀ i : ℕ, i ≤ d.length →
          orderAtLeastLocus (d.controlledTransform J (m * s) i) (m * s) = orderAtLeastLocus (d.controlledTransform I m i) m)

def IsMarkedIffBalancedTunedSheaf : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ (E : List X.IdealSheafData) (d : BlowupSequenceData X),
      (d.IsMarked p I m E ↔ d.IsMarked p (balancedTunedSheaf k p I m) (tuningExponent m) E) ∧
      (d.IsMarked p I m E → ∀ i : ℕ, i ≤ d.length →
        orderAtLeastLocus (d.controlledTransform (balancedTunedSheaf k p I m) (tuningExponent m) i) (tuningExponent m) =
          orderAtLeastLocus (d.controlledTransform I m i) m) ∧
      (derivIdealSheafIterate k p (tuningExponent m - 1) (balancedTunedSheaf k p I m) *
          derivIdealSheaf k p (balancedTunedSheaf k p I m) ≤ balancedTunedSheaf k p I m) ∧
      (∀ i : ℕ, i < tuningExponent m →
        derivIdealSheafIterate k p i (balancedTunedSheaf k p I m) ^ tuningExponent m ≤
          balancedTunedSheaf k p I m ^ (tuningExponent m - i))

structure TunedSheafProperties : Prop where
  isMarked_tuned_iff : IsMarkedIffBalancedTunedSheaf.{u}
  tunedSheaf_succ_le : TunedSheafSuccLe.{u}
  tunedSheaf_mul_le : TunedSheafMulLeAdd.{u}
  derivIdealSheaf_tunedSheaf_succ : DerivIdealSheafTunedSheafSucc.{u}
  derivIdealSheafIter_pred_tunedSheaf : MaxContactIdealTunedSheafEq.{u}
  derivIdealSheafIter_mul_derivIdealSheaf_le_tunedSheaf : IsMaxContactInvariantTunedSheaf.{u}
  tunedSheaf_mul_eq : TunedSheafMulEqAdd.{u}
  tunedSheaf_pow : TunedSheafPowEqMul.{u}
  derivIdealSheafIter_tunedSheaf_pow_le : IsDerivBalancedTunedSheafMulLcm.{u}
  coSupport_tunedSheaf_eq_and_orderLE : CoSupportTunedSheafEqAndOrderLE.{u}
  isMarked_iff_of_pow_le_of_le_tunedSheaf : IsMarkedIffOfPowLeOfLeTunedSheaf.{u}

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafBasic
section


namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Scheme.{u}}

private theorem mul_le_mul_idealSheafData_consolidated272 {A B C D : X.IdealSheafData}
    (h1 : A ≤ B) (h2 : C ≤ D) : A * C ≤ B * D := by
  have h : ∀ U : X.affineOpens, (A * C).ideal U ≤ (B * D).ideal U := by
    intro U
    rw [Scheme.IdealSheafData.ideal_mul, Scheme.IdealSheafData.ideal_mul]
    exact Ideal.mul_mono (h1 U) (h2 U)
  exact h

private theorem idealSheafData_pow_antitone_of_le_consolidated272 (I : X.IdealSheafData) {a b : ℕ}
    (h : b ≤ a) : I ^ a ≤ I ^ b := by
  have hU : ∀ U : X.affineOpens, (I ^ a).ideal U ≤ (I ^ b).ideal U := by
    intro U
    rw [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_pow]
    exact Ideal.pow_le_pow_right h
  exact hU

private theorem listProd_map_le_listProd_map_consolidated272 (f g : ℕ → X.IdealSheafData) :
    ∀ L : List ℕ, (∀ j ∈ L, f j ≤ g j) → (L.map f).prod ≤ (L.map g).prod := by
  intro L
  induction L with
  | nil =>
      intro _
      exact le_rfl
  | cons a L ih =>
      intro h
      simp only [List.map_cons, List.prod_cons]
      exact mul_le_mul_idealSheafData_consolidated272 (h a (by simp)) (ih fun j hj => h j (by simp [hj]))

private theorem listProd_map_range_one_consolidated272 (f : ℕ → X.IdealSheafData) :
    ((List.range 1).map f).prod = f 0 := by
  have h : List.range 1 = [0] := rfl
  rw [h, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]


end

private def extendExponentsByZero_consolidated272 (m s : ℕ) (t : Fin m → Fin (s + 1)) (j : ℕ) : ℕ :=
  if h : j < m then (t ⟨j, h⟩ : ℕ) else 0

section
variable (m s : ℕ)

private theorem extendExponentsByZero_apply_of_lt_consolidated272 (t : Fin m → Fin (s + 1)) (j : ℕ) (hj : j < m) :
    extendExponentsByZero_consolidated272 m s t j = (t ⟨j, hj⟩ : ℕ) :=
  dif_pos hj

private theorem le_sum_mul_min_of_le_sum_consolidated272 (c : ℕ → ℕ)
    (hc : s ≤ ∑ j ∈ Finset.range m, (m - j) * c j) :
    s ≤ ∑ j ∈ Finset.range m, (m - j) * min (c j) s := by
  by_cases h : ∀ j ∈ Finset.range m, c j ≤ s
  · refine le_trans hc (le_of_eq (Finset.sum_congr rfl ?_))
    intro j hj
    rw [min_eq_left (h j hj)]
  · push Not at h
    obtain ⟨j, hj, hjs⟩ := h
    have hjm : j < m := Finset.mem_range.mp hj
    have h1 : 1 ≤ m - j := by omega
    have hterm : s ≤ (m - j) * min (c j) s := by
      have hmin : min (c j) s = s := min_eq_right (le_of_lt hjs)
      rw [hmin]
      calc s = 1 * s := (one_mul s).symm
        _ ≤ (m - j) * s := Nat.mul_le_mul h1 (le_refl s)
    refine le_trans hterm (Finset.single_le_sum
      (f := fun j : ℕ => (m - j) * min (c j) s) ?_ hj)
    intro i _
    exact Nat.zero_le _


end

section
variable (k : Type u) [Field k] [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData) (m s : ℕ)

theorem prod_pow_derivIdealSheafIterate_le_tunedSheaf (c : ℕ → ℕ)
    (hc : s ≤ ∑ j ∈ Finset.range m, (m - j) * c j) :
    ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ c j)).prod ≤
      tunedSheaf k p I m s := by
  rw [tunedSheaf_eq_iSup]
  exact le_iSup (fun c : {c : ℕ → ℕ // s ≤ ∑ j ∈ Finset.range m, (m - j) * c j} =>
    ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ (c.1 j))).prod) ⟨c, hc⟩

private theorem tunedSheaf_eq_iSup_fin_consolidated272 :
    tunedSheaf k p I m s =
      ⨆ t : {t : Fin m → Fin (s + 1) //
          s ≤ ∑ j ∈ Finset.range m, (m - j) * extendExponentsByZero_consolidated272 m s t j},
        ((List.range m).map
          (fun j => derivIdealSheafIterate k p j I ^ extendExponentsByZero_consolidated272 m s t.1 j)).prod := by
  rw [tunedSheaf_eq_iSup]
  refine le_antisymm (iSup_le ?_) (iSup_le ?_)
  · rintro ⟨c, hc⟩
    have hex : ∀ j : ℕ, j < m →
        extendExponentsByZero_consolidated272 m s (fun i : Fin m =>
            (⟨min (c i.1) s, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (s + 1))) j
          = min (c j) s := fun j hj => extendExponentsByZero_apply_of_lt_consolidated272 m s _ j hj
    have hconstr : s ≤ ∑ j ∈ Finset.range m, (m - j) *
        extendExponentsByZero_consolidated272 m s (fun i : Fin m =>
          (⟨min (c i.1) s, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (s + 1))) j := by
      refine le_trans (le_sum_mul_min_of_le_sum_consolidated272 m s c hc) (le_of_eq (Finset.sum_congr rfl ?_))
      intro j hj
      rw [hex j (Finset.mem_range.mp hj)]
    have hprod : ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ c j)).prod ≤
        ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^
          extendExponentsByZero_consolidated272 m s (fun i : Fin m =>
            (⟨min (c i.1) s, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (s + 1))) j)).prod := by
      refine listProd_map_le_listProd_map_consolidated272 _ _ (List.range m) fun j hj => ?_
      rw [hex j (List.mem_range.mp hj)]
      exact idealSheafData_pow_antitone_of_le_consolidated272 _ (min_le_left _ _)
    exact le_iSup_of_le ⟨_, hconstr⟩ hprod
  · rintro ⟨t, ht⟩
    exact le_iSup_of_le ⟨extendExponentsByZero_consolidated272 m s t, ht⟩ le_rfl


end

theorem idealSheafData_pow_le_self {X : Scheme.{u}} (I : X.IdealSheafData) {c : ℕ}
    (hc : 1 ≤ c) : I ^ c ≤ I := by
  have h : ∀ U : X.affineOpens, (I ^ c).ideal U ≤ I.ideal U := by
    intro U
    rw [Scheme.IdealSheafData.ideal_pow]
    exact Ideal.pow_le_self (by omega)
  exact h

section
variable (k : Type u) [Field k] [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData)

theorem tunedSheaf_one_one :
    tunedSheaf k p I 1 1 = I := by
  rw [tunedSheaf_eq_iSup]
  refine le_antisymm (iSup_le ?_) ?_
  · rintro ⟨c, hc⟩
    have hc1 : 1 ≤ c 0 := by simpa using hc
    have key : ((List.range 1).map (fun j => derivIdealSheafIterate k p j I ^ c j)).prod ≤ I := by
      rw [listProd_map_range_one_consolidated272]
      exact idealSheafData_pow_le_self I hc1
    exact key
  · have key : I ≤ ((List.range 1).map
        (fun j => derivIdealSheafIterate k p j I ^ ((fun _ : ℕ => 1) j))).prod := by
      rw [listProd_map_range_one_consolidated272]
      exact le_of_eq (pow_one I).symm
    exact le_trans key (le_iSup
      (fun c : {c : ℕ → ℕ // 1 ≤ ∑ j ∈ Finset.range 1, (1 - j) * c j} =>
        ((List.range 1).map (fun j => derivIdealSheafIterate k p j I ^ (c.1 j))).prod)
      ⟨fun _ => 1, by simp⟩)

theorem balancedTunedSheaf_one :
    balancedTunedSheaf k p I 1 = I := by
  rw [balancedTunedSheaf_eq, tuningExponent_one, tunedSheaf_one_one]


end

section
variable (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p] (I : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m)
include hm

theorem tunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty (s : ℕ) (h : orderAtLeastLocus I m = (∅ : Set X)) :
    tunedSheaf k p I m s = ⊤ := by
  classical
  have hm1 : m - 1 + 1 = m := by omega
  have htop : derivIdealSheafIterate k p (m - 1) I = ⊤ :=
    derivIdealSheafIterate_eq_top_of_orderAtLeastLocus_eq_empty k p I (m - 1) (by rw [hm1]; exact h)
  have hmem : m - 1 ∈ Finset.range m := Finset.mem_range.mpr (by omega)
  have hm2 : m - (m - 1) = 1 := by omega
  have heq : ∑ j ∈ Finset.range m, (m - j) * (if j = m - 1 then s else 0)
      = (m - (m - 1)) * (if m - 1 = m - 1 then s else 0) :=
    Finset.sum_eq_single (m - 1) (fun b _ hb => by rw [if_neg hb, mul_zero])
      (fun hb => absurd hmem hb)
  have h3 : (m - (m - 1)) * (if m - 1 = m - 1 then s else 0) = s := by simp [hm2]
  have hsum : s ≤ ∑ j ∈ Finset.range m, (m - j) * (if j = m - 1 then s else 0) :=
    (heq.trans h3).ge
  have hprod : ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^
      (if j = m - 1 then s else 0))).prod = ⊤ := by
    have h1 : ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^
        (if j = m - 1 then s else 0))).prod = 1 := by
      refine List.prod_eq_one ?_
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨j, -, rfl⟩ := hx
      by_cases hj : j = m - 1
      · subst hj
        rw [htop, ← Scheme.IdealSheafData.one_eq_top, one_pow]
      · rw [if_neg hj, pow_zero]
    rw [h1, Scheme.IdealSheafData.one_eq_top]
  rw [tunedSheaf_eq_iSup]
  exact top_le_iff.mp (le_trans (le_of_eq hprod.symm)
    (le_iSup (fun c : {c : ℕ → ℕ // s ≤ ∑ j ∈ Finset.range m, (m - j) * c j} =>
      ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ (c.1 j))).prod)
      ⟨fun j => if j = m - 1 then s else 0, hsum⟩))

theorem balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty (h : orderAtLeastLocus I m = (∅ : Set X)) :
    balancedTunedSheaf k p I m = ⊤ := by
  rw [balancedTunedSheaf_eq]
  exact tunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty k p I hm (tuningExponent m) h


end

section
variable (k : Type u) [Field k] [IsNoetherianRing k] {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p] (h : Y ⟶ X) [Smooth h] [LocallyOfFiniteType (h ≫ p)] (I : X.IdealSheafData)

theorem tunedSheaf_comap (m s : ℕ) :
    tunedSheaf k (h ≫ p) (I.comap h) m s = (tunedSheaf k p I m s).comap h := by
  rw [tunedSheaf_eq_iSup_fin_consolidated272 k (h ≫ p) (I.comap h) m s, tunedSheaf_eq_iSup_fin_consolidated272 k p I m s,
    Scheme.IdealSheafData.comap_iSup]
  refine iSup_congr fun t => ?_
  have hfun : (fun j : ℕ =>
        derivIdealSheafIterate k (h ≫ p) j (I.comap h) ^ extendExponentsByZero_consolidated272 m s t.1 j)
      = (fun J : X.IdealSheafData => J.comap h) ∘
        (fun j : ℕ => derivIdealSheafIterate k p j I ^ extendExponentsByZero_consolidated272 m s t.1 j) := by
    funext j
    show derivIdealSheafIterate k (h ≫ p) j (I.comap h) ^ extendExponentsByZero_consolidated272 m s t.1 j
        = (derivIdealSheafIterate k p j I ^ extendExponentsByZero_consolidated272 m s t.1 j).comap h
    rw [derivIdealSheafIterate_comap k p h j I, Scheme.IdealSheafData.comap_pow]
  rw [Scheme.IdealSheafData.comap_listProd, List.map_map]
  exact congrArg List.prod
    (congrArg (fun F : ℕ → Y.IdealSheafData => List.map F (List.range m)) hfun)

theorem balancedTunedSheaf_comap (m : ℕ) :
    balancedTunedSheaf k (h ≫ p) (I.comap h) m = (balancedTunedSheaf k p I m).comap h := by
  rw [balancedTunedSheaf_eq, balancedTunedSheaf_eq]
  exact tunedSheaf_comap k p h I m (tuningExponent m)


end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafMultiplicativity
section
universe v w


namespace FunctorialResolution.EmbeddedResolution

private theorem listProd_map_pow_mul_listProd_map_pow_consolidated271 {M : Type u} [CommMonoid M] (f : ℕ → M) (c d : ℕ → ℕ) :
    ∀ L : List ℕ, ((L.map fun j => f j ^ c j).prod * (L.map fun j => f j ^ d j).prod)
      = (L.map fun j => f j ^ (c j + d j)).prod := by
  intro L
  rw [← List.prod_map_mul]
  simp [pow_add]

section
variable {X : Scheme.{u}} {ι : Type v}

private theorem ideal_iSup_consolidated271 (f : ι → X.IdealSheafData)
    (U : X.affineOpens) : (⨆ i, f i).ideal U = ⨆ i, (f i).ideal U := by simp

private theorem iSup_mul_iSup_le_consolidated271 {κ : Type w}
    (f : ι → X.IdealSheafData) (g : κ → X.IdealSheafData) (h : X.IdealSheafData)
    (H : ∀ i j, f i * g j ≤ h) : (⨆ i, f i) * (⨆ j, g j) ≤ h := by
  refine Scheme.IdealSheafData.le_def.mpr fun U => ?_
  show (⨆ i, f i).ideal U * (⨆ j, g j).ideal U ≤ h.ideal U
  rw [ideal_iSup_consolidated271, ideal_iSup_consolidated271, Submodule.iSup_mul]
  refine iSup_le fun i => ?_
  rw [Submodule.mul_iSup]
  refine iSup_le fun j => ?_
  exact Scheme.IdealSheafData.le_def.mp (H i j) U


end

theorem tunedSheaf_succ_le : TunedSheafSuccLe.{u} := by
  intro k _ _ _ X p _ _ I m _ _ s
  rw [tunedSheaf_eq_iSup, tunedSheaf_eq_iSup]
  refine iSup_le fun c => ?_
  exact le_iSup_of_le ⟨c.1, le_trans (Nat.le_succ s) c.2⟩ le_rfl

theorem tunedSheaf_mul_le_add : TunedSheafMulLeAdd.{u} := by
  intro k _ _ _ X p _ _ I m _ _ s t
  rw [tunedSheaf_eq_iSup, tunedSheaf_eq_iSup, tunedSheaf_eq_iSup]
  refine iSup_mul_iSup_le_consolidated271 _ _ _ fun c d => ?_
  refine le_iSup_of_le ⟨fun j => c.1 j + d.1 j, ?_⟩ (le_of_eq ?_)
  · show s + t ≤ ∑ j ∈ Finset.range m, (m - j) * (c.1 j + d.1 j)
    have hsum : ∑ j ∈ Finset.range m, (m - j) * (c.1 j + d.1 j)
        = (∑ j ∈ Finset.range m, (m - j) * c.1 j) + ∑ j ∈ Finset.range m, (m - j) * d.1 j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => Nat.mul_add _ _ _
    have h1 := c.2
    have h2 := d.2
    omega
  · exact listProd_map_pow_mul_listProd_map_pow_consolidated271 (fun j => derivIdealSheafIterate k p j I) c.1 d.1 (List.range m)

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
section

open TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

private theorem exists_isIso_subschemeι_eq_comp_of_eq_ker_consolidated227 {A X : Scheme.{u}} (g : A ⟶ X)
    [IsClosedImmersion g] (I : X.IdealSheafData) (hI : I = g.ker) :
    ∃ φ : I.subscheme ⟶ A, IsIso φ ∧ I.subschemeι = φ ≫ g := by
  subst hI
  have : Mono g := inferInstance
  have : Mono (Scheme.Hom.ker g).subschemeι := inferInstance
  have h1 : Scheme.Hom.ker g ≤ Scheme.Hom.ker (Scheme.Hom.ker g).subschemeι :=
    le_of_eq (Scheme.IdealSheafData.ker_subschemeι _).symm
  have h2 : Scheme.Hom.ker (Scheme.Hom.ker g).subschemeι ≤ Scheme.Hom.ker g :=
    le_of_eq (Scheme.IdealSheafData.ker_subschemeι _)
  have hφ : IsClosedImmersion.lift g (Scheme.Hom.ker g).subschemeι h1 ≫ g
      = (Scheme.Hom.ker g).subschemeι := by simp
  have hψ : IsClosedImmersion.lift (Scheme.Hom.ker g).subschemeι g h2
      ≫ (Scheme.Hom.ker g).subschemeι = g := by simp
  refine ⟨IsClosedImmersion.lift g (Scheme.Hom.ker g).subschemeι h1,
    ⟨⟨IsClosedImmersion.lift (Scheme.Hom.ker g).subschemeι g h2, ?_, ?_⟩⟩, hφ.symm⟩
  · rw [← cancel_mono (Scheme.Hom.ker g).subschemeι, Category.assoc, hψ, hφ, Category.id_comp]
  · rw [← cancel_mono g, Category.assoc, hφ, hψ, Category.id_comp]

section
variable {X Y : Scheme.{u}} (e : X ≅ Y)

private theorem iso_inv_base_hom_base_apply_consolidated227 (x : X) :
    e.inv.base (e.hom.base x) = x := by
  simp

private theorem iso_hom_base_inv_base_apply_consolidated227 (y : Y) :
    e.hom.base (e.inv.base y) = y := by
  simp

private theorem isIso_resLE_iso_hom_consolidated227 (U : Y.Opens) :
    IsIso (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl) := by
  have h1 : U ≤ (Opens.map e.inv.base).obj ((Opens.map e.hom.base).obj U) := by
    intro y hy
    show e.hom.base (e.inv.base y) ∈ U
    rw [iso_hom_base_inv_base_apply_consolidated227 e y]
    exact hy
  refine ⟨e.inv.resLE ((Opens.map e.hom.base).obj U) U h1, ?_, ?_⟩
  · rw [← cancel_mono (Scheme.Opens.ι ((Opens.map e.hom.base).obj U)), Category.assoc,
      Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
      e.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [← cancel_mono (Scheme.Opens.ι U), Category.assoc,
      Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
      e.inv_hom_id, Category.comp_id, Category.id_comp]

theorem orderAtLeastLocus_comap_iso_hom_eq_preimage (J : Y.IdealSheafData) (n : ℕ) :
    orderAtLeastLocus (J.comap e.hom) n = ⇑e.hom.base ⁻¹' orderAtLeastLocus J n := by
  have hJ : (J.comap e.hom).comap e.inv = J := by
    rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id]
  ext x
  have h1 := orderAt_le_orderAt_comap e.hom J x
  have h2 := orderAt_le_orderAt_comap e.inv (J.comap e.hom) (e.hom.base x)
  rw [iso_inv_base_hom_base_apply_consolidated227 e x, hJ] at h2
  simp only [Set.mem_preimage, mem_orderAtLeastLocus_iff]
  exact ⟨fun hm => le_trans hm h2, fun hm => le_trans hm h1⟩


end

theorem strictTransform_comp_iso_hom {X X₁ Y : Scheme.{u}} (π : X₁ ⟶ X) (e : X ≅ Y)
    (Z D : Y.IdealSheafData) :
    Blowup.strictTransform (π ≫ e.hom) Z D = Blowup.strictTransform π (Z.comap e.hom) (D.comap e.hom) := by
  have hZ : Z.comap (π ≫ e.hom) = (Z.comap e.hom).comap π := by
    rw [Scheme.IdealSheafData.comap_comp]
  have hD : D.comap (π ≫ e.hom) = (D.comap e.hom).comap π := by
    rw [Scheme.IdealSheafData.comap_comp]
  rw [Blowup.strictTransform_eq_ker, Blowup.strictTransform_eq_ker, Blowup.strictTransformImmersion_eq,
    Blowup.strictTransformImmersion_eq, Blowup.strictTransformOpens_eq, Blowup.strictTransformOpens_eq, hZ, hD]

theorem smooth_comap_iso {k : Type u} [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) (Z : Y.IdealSheafData)
    (h : Smooth (Z.subschemeι ≫ q)) :
    Smooth ((Z.comap e.hom).subschemeι ≫ e.hom ≫ q) := by
  have hsq : Limits.pullback.fst e.hom Z.subschemeι =
      Limits.pullback.snd e.hom Z.subschemeι ≫ Z.subschemeι ≫ e.inv := by
    rw [← Category.assoc, ← Limits.pullback.condition, Category.assoc, e.hom_inv_id,
      Category.comp_id]
  have hsnd : IsIso (Limits.pullback.snd e.hom Z.subschemeι) := inferInstance
  have hci : IsClosedImmersion (Limits.pullback.fst e.hom Z.subschemeι) := by
    rw [hsq]; infer_instance
  obtain ⟨φ, hφ, hcomm⟩ :=
    exists_isIso_subschemeι_eq_comp_of_eq_ker_consolidated227 (Limits.pullback.fst e.hom Z.subschemeι)
      (Z.comap e.hom) rfl
  have := hφ
  have hc2 : (Z.comap e.hom).subschemeι ≫ e.hom =
      (φ ≫ Limits.pullback.snd e.hom Z.subschemeι) ≫ Z.subschemeι := by
    rw [hcomm, Category.assoc, Category.assoc, Limits.pullback.condition]
  rw [← Category.assoc, hc2, Category.assoc]
  have : IsIso (φ ≫ Limits.pullback.snd e.hom Z.subschemeι) := inferInstance
  have : Smooth (Z.subschemeι ≫ q) := h
  infer_instance

theorem restrictIdeal_comap {X Y : Scheme.{u}} (f : X ⟶ Y) (J : Y.IdealSheafData) (U : Y.Opens) :
    restrictIdeal (J.comap f) ((Opens.map f.base).obj U) =
      (restrictIdeal J U).comap (f.resLE U ((Opens.map f.base).obj U) le_rfl) := by
  rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, Scheme.Hom.resLE_comp_ι]

section
variable {k : Type u} [Field k] {X Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) {U : Y.Opens} {m : ℕ} (c : EtaleChart q U m)

private theorem ofIso_map_comp_affineSpaceFinToSpec_consolidated227 :
    (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl ≫ c.map) ≫ affineSpaceFinToSpec k m =
      Scheme.Opens.ι ((Opens.map e.hom.base).obj U) ≫ (e.hom ≫ q) := by
  rw [Category.assoc, c.comp_struct, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]

private theorem etale_resLE_comp_map_of_iso_consolidated227 :
    Etale
      (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl ≫ c.map) := by
  have : IsIso (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl) := isIso_resLE_iso_hom_consolidated227 e U
  have : Etale (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl) :=
    inferInstance
  have : Etale c.map := c.isEtale
  infer_instance


end

def EtaleChart.ofIso {k : Type u} [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) {U : Y.Opens} {m : ℕ}
    (c : EtaleChart q U m) : EtaleChart (e.hom ≫ q) ((Opens.map e.hom.base).obj U) m where
  map := e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl ≫ c.map
  comp_struct := ofIso_map_comp_affineSpaceFinToSpec_consolidated227 q e c
  isEtale := etale_resLE_comp_map_of_iso_consolidated227 q e c

section
variable {k : Type u} [Field k] {X Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y)

theorem EtaleChart.ofIso_coordIdeal {U : Y.Opens} {m : ℕ}
    (c : EtaleChart q U m) (S : Finset (Fin m)) :
    (EtaleChart.ofIso q e c).coordIdeal S =
      (c.coordIdeal S).comap (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl) := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  show (coordSubspaceIdeal k m S).comap
      (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl ≫ c.map) = _
  rw [Scheme.IdealSheafData.comap_comp]

theorem hasStrictNormalCrossingsWith_comap_iso (Z : Y.IdealSheafData)
    (F : List Y.IdealSheafData) (h : HasStrictNormalCrossingsWith q Z F) :
    HasStrictNormalCrossingsWith (e.hom ≫ q) (Z.comap e.hom) (F.map (fun D => D.comap e.hom)) := by
  unfold HasStrictNormalCrossingsWith at h ⊢
  intro x hx
  have hx1 : x ∈ orderAtLeastLocus (Z.comap e.hom) 1 := (mem_orderAtLeastLocus_one_iff _ _).2 hx
  rw [orderAtLeastLocus_comap_iso_hom_eq_preimage e Z 1] at hx1
  have hx' : e.hom.base x ∈ Z.support := (mem_orderAtLeastLocus_one_iff _ _).1 hx1
  obtain ⟨U, hU, m, c, a, S, h1, h2, h3, h4⟩ := h (e.hom.base x) hx'
  refine ⟨(Opens.map e.hom.base).obj U, hU, m, EtaleChart.ofIso q e c, a, S, ?_, ?_, ?_, ?_⟩
  · simpa using h1
  · intro i hi hai
    have hi' : i < F.length := by simpa using hi
    have hmap : (List.map (fun D => D.comap e.hom) F)[i] = (F[i]'hi').comap e.hom := by
      simp
    rw [hmap, restrictIdeal_comap, h2 i hi' hai]
    exact Scheme.IdealSheafData.comap_top _
  · intro i hi t hai
    have hi' : i < F.length := by simpa using hi
    have hmap : (List.map (fun D => D.comap e.hom) F)[i] = (F[i]'hi').comap e.hom := by
      simp
    rw [hmap, restrictIdeal_comap, h3 i hi' t hai, EtaleChart.ofIso_coordIdeal]
  · rw [restrictIdeal_comap, h4, EtaleChart.ofIso_coordIdeal]


end

theorem comapIsoInvariance : ComapIsoInvariance.{u} where
  coSupport_comap := fun e J n => orderAtLeastLocus_comap_iso_hom_eq_preimage e J n
  hasSNCWith_comap := fun q e Z F h => hasStrictNormalCrossingsWith_comap_iso q e Z F h
  smooth_comap := fun q e Z h => smooth_comap_iso q e Z h
  strictTransform_comap := fun π e Z D => strictTransform_comp_iso_hom π e Z D

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardUniqueness
section


section
namespace FunctorialResolution.EmbeddedResolution

structure SequenceOfBlowupsPushforward {S X : Scheme.{u}} (j : S ⟶ X) (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X) where
  lengthEq : BS.length = B.length
  σ : ∀ i : ℕ, i ≤ B.length → (BS.schemeAt i ⟶ B.schemeAt i)
  isClosedImmersion : ∀ (i : ℕ) (hi : i ≤ B.length), IsClosedImmersion (σ i hi)
  zero : σ 0 (Nat.zero_le B.length) ≫ B.isoZero.hom = BS.isoZero.hom ≫ j
  square : ∀ (i : ℕ) (hi : i < B.length),
    σ (i + 1) hi ≫ B.transitionMapSucc i = BS.transitionMapSucc i ≫ σ i hi.le
  center : ∀ (i : ℕ) (hi : i < B.length),
    B.center i = imageIdealSheaf (σ i hi.le) (BS.center i)

private theorem comap_imageIdealSheaf_of_isIso_consolidated94 {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (J : A.IdealSheafData) :
    (imageIdealSheaf f J).comap f = J := by
  rw [show imageIdealSheaf f J = J.map f from map_eq_imageIdealSheaf ..]
  exact Blowup.comap_map_of_isClosedImmersion f J

private theorem exists_iso_succ_comp_blowupMorphism_consolidated94 {X : Scheme.{u}} (B B' : SequenceOfBlowups X) (i : ℕ)
    (hi : i < B.length) (hi' : i < B'.length) (f : B.schemeAt i ≅ B'.schemeAt i)
    (hf : (B'.center i).comap f.hom = B.center i) :
    ∃ g : B.schemeAt (i + 1) ≅ B'.schemeAt (i + 1),
      g.hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ f.hom := by
  have hB := B.isBlowupAlongIdealSheaf_blowupMorphism i hi
  have hB' := B'.isBlowupAlongIdealSheaf_blowupMorphism i hi'
  have cB : Blowup.IsLocallyGeneratedByNonZeroDivisor ((B.center i).comap (B.transitionMapSucc i)) := hB.1
  have cB' : Blowup.IsLocallyGeneratedByNonZeroDivisor ((B'.center i).comap (B'.transitionMapSucc i)) := hB'.1
  have hinv : (B.center i).comap f.inv = B'.center i := by
    rw [← hf, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id,
      AlgebraicGeometry.Scheme.IdealSheafData.comap_id]
  have c1 : Blowup.IsLocallyGeneratedByNonZeroDivisor ((B'.center i).comap (B.transitionMapSucc i ≫ f.hom)) := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hf]
    exact cB
  have c2 : Blowup.IsLocallyGeneratedByNonZeroDivisor ((B.center i).comap (B'.transitionMapSucc i ≫ f.inv)) := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hinv]
    exact cB'
  obtain ⟨a, ha⟩ := (hB'.2 _ (B.transitionMapSucc i ≫ f.hom) c1).exists
  obtain ⟨b, hb⟩ := (hB.2 _ (B'.transitionMapSucc i ≫ f.inv) c2).exists
  have hab : a ≫ b = 𝟙 _ := by
    refine (hB.2 _ (B.transitionMapSucc i) cB).unique ?_ ?_
    · rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    · rw [Category.id_comp]
  have hba : b ≫ a = 𝟙 _ := by
    refine (hB'.2 _ (B'.transitionMapSucc i) cB').unique ?_ ?_
    · rw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
    · rw [Category.id_comp]
  exact ⟨⟨a, b, hab, hba⟩, ha⟩

private theorem comap_center_eq_of_sequenceOfBlowupsPushforward_consolidated94 {S X : Scheme.{u}} {j : S ⟶ X}
    {BS : SequenceOfBlowups S} {B B' : SequenceOfBlowups X}
    (d : SequenceOfBlowupsPushforward j BS B) (d' : SequenceOfBlowupsPushforward j BS B')
    (i : ℕ) (hi : i < B.length) (hi' : i < B'.length)
    (f : B.schemeAt i ≅ B'.schemeAt i) (hf : d.σ i hi.le ≫ f.hom = d'.σ i hi'.le) :
    (B'.center i).comap f.hom = B.center i := by
  rw [d'.center i hi', ← hf, imageIdealSheaf_comp, comap_imageIdealSheaf_of_isIso_consolidated94, d.center i hi]

namespace SequenceOfBlowupsPushforward

section
variable {S X : Scheme.{u}}

theorem nonempty_of_isPushforward (j : S ⟶ X) [IsClosedImmersion j]
    {BS : SequenceOfBlowups S} {B : SequenceOfBlowups X} (h : IsPushforwardBlowupSeq j BS B) :
    Nonempty (SequenceOfBlowupsPushforward j BS B) := by
  obtain ⟨hlen, σ, hci, h0, hstep, hcent, hker⟩ := h
  refine ⟨⟨hlen, fun i hi => σ i (by omega), fun i hi => hci i _, ?_, ?_, ?_⟩⟩
  · exact h0
  · intro i hi
    exact hstep i (by omega)
  · intro i hi
    exact hcent i (by omega)

theorem length_eq_length {j : S ⟶ X}
    {BS : SequenceOfBlowups S} {B B' : SequenceOfBlowups X}
    (d : SequenceOfBlowupsPushforward j BS B) (d' : SequenceOfBlowupsPushforward j BS B') :
    B.length = B'.length :=
  d.lengthEq ▸ d'.lengthEq

theorem isomorphic {j : S ⟶ X} [IsClosedImmersion j]
    {BS : SequenceOfBlowups S} {B B' : SequenceOfBlowups X}
    (d : SequenceOfBlowupsPushforward j BS B) (d' : SequenceOfBlowupsPushforward j BS B') :
    B.Isomorphic B' := by
  have hlength : B.length = B'.length := length_eq_length d d'
  have hSL : BS.length = B.length := d.lengthEq
  have key : ∀ n : ℕ, n ≤ B.length →
      ∃ e : ∀ i : ℕ, i ≤ n → (B.schemeAt i ≅ B'.schemeAt i),
        (∀ (i : ℕ) (hi : i ≤ n) (h1 : i ≤ B.length) (h2 : i ≤ B'.length),
            d.σ i h1 ≫ (e i hi).hom = d'.σ i h2) ∧
        ((e 0 (Nat.zero_le n)).hom ≫ B'.isoZero.hom = B.isoZero.hom) ∧
        (∀ (i : ℕ) (hi : i + 1 ≤ n),
            (e (i + 1) hi).hom ≫ B'.transitionMapSucc i
              = B.transitionMapSucc i ≫ (e i (Nat.le_of_succ_le hi)).hom) := by
    intro n
    induction n with
    | zero =>
        intro _
        refine ⟨fun i hi => eqToIso (congrArg B.schemeAt (Nat.le_zero.mp hi)) ≪≫
          (B.isoZero ≪≫ B'.isoZero.symm) ≪≫
          eqToIso (congrArg B'.schemeAt (Nat.le_zero.mp hi).symm), ?_, ?_, ?_⟩
        · intro i hi h1 h2
          obtain rfl : i = 0 := Nat.le_zero.mp hi
          have hz : d.σ 0 h1 ≫ B.isoZero.hom = d'.σ 0 h2 ≫ B'.isoZero.hom :=
            d.zero.trans d'.zero.symm
          have hgoal : d.σ 0 h1 ≫ B.isoZero.hom ≫ B'.isoZero.inv = d'.σ 0 h2 := by
            rw [← Category.assoc, hz, Category.assoc, Iso.hom_inv_id, Category.comp_id]
          simpa using hgoal
        · simp
        · intro i hi
          exact absurd hi (Nat.not_succ_le_zero i)
    | succ n ih =>
        intro hn1
        obtain ⟨e, hσ, h0, hsq⟩ := ih (by omega)
        have hnB : n < B.length := by omega
        have hnB' : n < B'.length := by omega
        have hnS : n < BS.length := by omega
        have hcen : (B'.center n).comap (e n le_rfl).hom = B.center n :=
          comap_center_eq_of_sequenceOfBlowupsPushforward_consolidated94 d d' n hnB hnB' (e n le_rfl)
            (hσ n le_rfl hnB.le hnB'.le)
        obtain ⟨g, hg⟩ := exists_iso_succ_comp_blowupMorphism_consolidated94 B B' n hnB hnB' (e n le_rfl) hcen
        refine ⟨fun i hi => if hin : i ≤ n then e i hin else
            eqToIso (congrArg B.schemeAt (by omega : i = n + 1)) ≪≫ g ≪≫
              eqToIso (congrArg B'.schemeAt (by omega : n + 1 = i)), ?_, ?_, ?_⟩
        · intro i hi h1 h2
          by_cases hin : i ≤ n
          · simp only [dif_pos hin]
            exact hσ i hin h1 h2
          · have hie : i = n + 1 := by omega
            subst hie
            simp only [dif_neg hin, Iso.trans_hom, eqToIso.hom, eqToHom_refl,
              Category.id_comp, Category.comp_id]
            have hBcen : (B'.center n).comap (d'.σ n hnB'.le) = BS.center n := by
              have := d'.isClosedImmersion n hnB'.le
              rw [d'.center n hnB', show imageIdealSheaf (d'.σ n hnB'.le) (BS.center n)
                  = (BS.center n).map (d'.σ n hnB'.le) from map_eq_imageIdealSheaf ..,
                Blowup.comap_map_of_isClosedImmersion]
            have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor
                ((B'.center n).comap (BS.transitionMapSucc n ≫ d'.σ n hnB'.le)) := by
              rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hBcen]
              exact (BS.isBlowupAlongIdealSheaf_blowupMorphism n hnS).1
            have hstep : (d.σ (n + 1) hnB ≫ g.hom) ≫ B'.transitionMapSucc n
                = BS.transitionMapSucc n ≫ d'.σ n hnB'.le := by
              rw [Category.assoc, hg, ← Category.assoc, d.square n hnB, Category.assoc,
                hσ n le_rfl hnB.le hnB'.le]
            exact ((B'.isBlowupAlongIdealSheaf_blowupMorphism n hnB').2 _
              (BS.transitionMapSucc n ≫ d'.σ n hnB'.le) hcart).unique hstep (d'.square n hnB')
        · have hzz : (0 : ℕ) ≤ n := Nat.zero_le n
          simp only [dif_pos hzz]
          exact h0
        · intro i hi
          by_cases hin : i + 1 ≤ n
          · have hin' : i ≤ n := Nat.le_of_succ_le hin
            simp only [dif_pos hin, dif_pos hin']
            exact hsq i hin
          · have hien : i = n := by omega
            have hile : i ≤ n := le_of_eq hien
            subst hien
            simp only [dif_neg hin, dif_pos hile, Iso.trans_hom, eqToIso.hom, eqToHom_refl,
              Category.id_comp, Category.comp_id]
            exact hg
  obtain ⟨e, hσ, h0, hsq⟩ := key B.length le_rfl
  refine ⟨hlength, e, h0, ?_, ?_⟩
  · intro i hi
    exact hsq i hi
  · intro i hi
    exact comap_center_eq_of_sequenceOfBlowupsPushforward_consolidated94 d d' i hi (by omega) (e i hi.le)
      (hσ i hi.le hi.le (by omega))


end

end SequenceOfBlowupsPushforward

theorem IsPushforwardBlowupSeq.isomorphic {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    {BS : SequenceOfBlowups S} {B B' : SequenceOfBlowups X}
    (h : IsPushforwardBlowupSeq j BS B) (h' : IsPushforwardBlowupSeq j BS B') :
    B.Isomorphic B' := by
  obtain ⟨d⟩ := SequenceOfBlowupsPushforward.nonempty_of_isPushforward j h
  obtain ⟨d'⟩ := SequenceOfBlowupsPushforward.nonempty_of_isPushforward j h'
  exact d.isomorphic d'

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.IsoBlowupRemoval
section


section
namespace FunctorialResolution.EmbeddedResolution

section
variable {S X : Scheme.{u}} (σ : S ⟶ X)

private theorem imageIdealSheaf_top_consolidated236 :
    imageIdealSheaf σ (⊤ : S.IdealSheafData) = ⊤ := by
  have hemp : IsEmpty ↥(⊤ : S.IdealSheafData).subscheme := inferInstance
  have hqc : QuasiCompact ((⊤ : S.IdealSheafData).subschemeι ≫ σ) := by
    constructor
    intro U _ _
    convert isCompact_empty
    exact Set.eq_empty_of_isEmpty _
  rw [imageIdealSheaf_eq_ker, ← Scheme.IdealSheafData.support_eq_bot_iff]
  have hs := Scheme.Hom.support_ker ((⊤ : S.IdealSheafData).subschemeι ≫ σ)
  rw [Set.range_eq_empty, closure_empty] at hs
  refine SetLike.coe_injective ?_
  rw [hs]
  simp

private theorem imageIdealSheaf_eq_top_iff_consolidated236 [IsClosedImmersion σ]
    (I : S.IdealSheafData) : imageIdealSheaf σ I = ⊤ ↔ I = ⊤ := by
  constructor
  · intro hI
    have h2 : (imageIdealSheaf σ I).comap σ = I := Blowup.comap_schemeImageIdeal σ I
    rw [hI] at h2
    rw [← h2]
    simp
  · rintro rfl
    exact imageIdealSheaf_top_consolidated236 σ


end

private theorem eqToHom_projectionToBase_consolidated236 {Sc : Scheme.{u}} (t : SequenceOfBlowups Sc) {a a' : ℕ} (ha : a = a') :
    eqToHom (congrArg t.schemeAt ha) ≫ t.projectionToBase a' = t.projectionToBase a := by
  subst ha
  simp

private theorem comp_eqToHom_comp_transitionMap_consolidated236 {Sc A C : Scheme.{u}} (t : SequenceOfBlowups Sc) {a b a' b' : ℕ}
    (ha : a = a') (hb : b = b') (hab : a ≤ b) (hab' : a' ≤ b')
    (g : C ⟶ t.schemeAt b) (f : A ⟶ t.schemeAt a) (u : C ⟶ A)
    (H : g ≫ t.transitionMap hab = u ≫ f) :
    (g ≫ eqToHom (congrArg t.schemeAt hb)) ≫ t.transitionMap hab'
      = u ≫ (f ≫ eqToHom (congrArg t.schemeAt ha)) := by
  subst ha
  subst hb
  simpa using H

section
variable {Sc A : Scheme.{u}} (t : SequenceOfBlowups Sc)

private theorem isClosedImmersion_comp_eqToHom_consolidated236 {a a' : ℕ}
    (ha : a = a') (f : A ⟶ t.schemeAt a) (hf : IsClosedImmersion f) :
    IsClosedImmersion (f ≫ eqToHom (congrArg t.schemeAt ha)) := by
  subst ha
  simpa using hf

private theorem center_eq_imageIdealSheaf_comp_eqToHom_consolidated236 (I : A.IdealSheafData) {a a' : ℕ} (ha : a = a') (f : A ⟶ t.schemeAt a)
    (hf : t.center a = imageIdealSheaf f I) :
    t.center a' = imageIdealSheaf (f ≫ eqToHom (congrArg t.schemeAt ha)) I := by
  subst ha
  simpa using hf


end

private theorem ker_comp_eqToHom_eq_strictTransform_consolidated236 {Sc A C : Scheme.{u}} (t : SequenceOfBlowups Sc)
    {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (hab : a ≤ b) (hab' : a' ≤ b')
    (g : C ⟶ t.schemeAt b) (f : A ⟶ t.schemeAt a)
    (H : g.ker = Blowup.strictTransform (t.transitionMap hab) (t.center a) f.ker) :
    (g ≫ eqToHom (congrArg t.schemeAt hb)).ker
      = Blowup.strictTransform (t.transitionMap hab') (t.center a') (f ≫ eqToHom (congrArg t.schemeAt ha)).ker := by
  subst ha
  subst hb
  simpa using H

theorem isPushforwardSequenceOfBlowups_withoutIsoBlowups {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (B : SequenceOfBlowups S) (t : SequenceOfBlowups X)
    (hN : ∀ i : ℕ, i ≤ t.length → IsLocallyNoetherian (t.schemeAt i))
    (h : IsPushforwardBlowupSeq j B t) :
    IsPushforwardBlowupSeq j B.withoutIsoBlowups t.withoutIsoBlowups := by
  obtain ⟨hlen, σ, hci, h0, hsq, hcen, hker⟩ := h
  have htriv : ∀ i : ℕ, i < B.length → (B.center i = ⊤ ↔ t.center i = ⊤) := by
    intro i hi
    have := hci i hi.le
    rw [hcen i hi]
    exact (imageIdealSheaf_eq_top_iff_consolidated236 (σ i hi.le) (B.center i)).symm
  have hretf : B.nontrivialIndex = t.nontrivialIndex :=
    SequenceOfBlowups.nontrivialIndex_congr_of_center_eq_top_iff B t hlen htriv
  have hplen : B.lengthWithoutIsoBlowups = t.lengthWithoutIsoBlowups :=
    SequenceOfBlowups.lengthWithoutIsoBlowups_congr_of_center_eq_top_iff B t hlen htriv
  have hret : ∀ i : ℕ, B.nontrivialIndex i = t.nontrivialIndex i := fun i => congrFun hretf i
  have hdown : ∀ (a b : ℕ) (hab : a ≤ b) (hb : b ≤ B.length),
      σ b hb ≫ t.transitionMap hab = B.transitionMap hab ≫ σ a (le_trans hab hb) := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base =>
        intro hb
        rw [t.transitionMap_self, B.transitionMap_self, Category.comp_id, Category.id_comp]
    | succ b hab ih =>
        intro hb
        have hbl : b < B.length := hb
        have e1 : t.transitionMapSucc b ≫ t.transitionMap hab = t.transitionMap (le_trans hab (Nat.le_succ b)) := by
          rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
          exact t.transitionMap_trans hab (Nat.le_succ b)
        have e2 : B.transitionMapSucc b ≫ B.transitionMap hab = B.transitionMap (le_trans hab (Nat.le_succ b)) := by
          rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
          exact B.transitionMap_trans hab (Nat.le_succ b)
        rw [← e1, ← Category.assoc, hsq b hbl, Category.assoc, ih hbl.le, ← Category.assoc, e2]
  have hstruct : ∀ (i : ℕ) (hi : i ≤ B.length),
      σ i hi ≫ t.projectionToBase i = B.projectionToBase i ≫ j := by
    intro i hi
    have hd := hdown 0 i (Nat.zero_le i) hi
    rw [SequenceOfBlowups.projectionToBase_def, SequenceOfBlowups.projectionToBase_def, ← Category.assoc (σ i hi), hd]
    simp only [Category.assoc, h0]
  have key : ∀ (a c : ℕ) (hac : a + 1 ≤ c), (∀ d : ℕ, a + 1 ≤ d → d < c → t.center d = ⊤) →
      ∀ (hc : c ≤ B.length) (ha : a < B.length),
      (σ c hc).ker
        = Blowup.strictTransform (t.transitionMap (Nat.le_of_succ_le hac)) (t.center a) (σ a ha.le).ker := by
    intro a c hac
    induction c, hac using Nat.le_induction with
    | base =>
        intro _ hc ha
        have hk := hker a ha
        rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap] at hk
        exact hk
    | succ c hac ih =>
        intro htop hc ha
        have hcl : c < B.length := hc
        have hc' : c ≤ B.length := le_of_lt hcl
        have htopc : ∀ d : ℕ, a + 1 ≤ d → d < c → t.center d = ⊤ :=
          fun d hd1 hd2 => htop d hd1 (Nat.lt_succ_of_lt hd2)
        have hctop : t.center c = ⊤ := htop c hac (Nat.lt_succ_self c)
        have : IsLocallyNoetherian (t.schemeAt c) := hN c (by omega)
        have : IsLocallyNoetherian (t.schemeAt (c + 1)) := hN (c + 1) (by omega)
        have ihc := ih htopc hc' ha
        have hk := hker c hcl
        rw [hctop, strictTransform_top_eq_comap (t.transitionMapSucc c) ((σ c hcl.le).ker), ihc] at hk
        have hiso : IsIso (t.transitionMapSucc c) := by
          have hB := t.isBlowupAlongIdealSheaf_blowupMorphism c (by omega)
          rw [hctop] at hB
          exact hB.isIso_of_top
        have hbl : Blowup.IsBlowupAlongIdealSheaf (t.transitionMap (Nat.le_of_succ_le hac)) (t.center a) := by
          have : IsIso (t.transitionMap hac) := t.isIso_transitionMap_of_center_eq_top hac (by omega) htopc
          have hB : Blowup.IsBlowupAlongIdealSheaf (t.transitionMapSucc a) (t.center a) := t.isBlowupAlongIdealSheaf_blowupMorphism a (by omega)
          have hcomp := hB.iso_hom_comp (asIso (t.transitionMap hac))
          have heq2 : (asIso (t.transitionMap hac)).hom ≫ t.transitionMapSucc a
              = t.transitionMap (Nat.le_of_succ_le hac) := by
            rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
            exact t.transitionMap_trans (Nat.le_succ a) hac
          rw [heq2] at hcomp
          exact hcomp
        have heq : t.transitionMapSucc c ≫ t.transitionMap (Nat.le_of_succ_le hac)
            = t.transitionMap (Nat.le_of_succ_le (le_trans hac (Nat.le_succ c))) := by
          rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
          exact t.transitionMap_trans (Nat.le_of_succ_le hac) (Nat.le_succ c)
        rw [hk, ← strictTransform_isIso_comp (t.transitionMapSucc c) (t.transitionMap (Nat.le_of_succ_le hac))
          (t.center a) ((σ a ha.le).ker) hbl, heq]
  have h1 : ∀ (i : ℕ) (hi : i ≤ B.lengthWithoutIsoBlowups),
      IsClosedImmersion (σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length hi) ≫
        eqToHom (congrArg t.schemeAt (hret i))) := by
    intro i hi
    exact isClosedImmersion_comp_eqToHom_consolidated236 t (hret i) _ (hci _ _)
  have h2 : (σ (B.nontrivialIndex 0) (B.nontrivialIndex_le_length (Nat.zero_le B.lengthWithoutIsoBlowups)) ≫
      eqToHom (congrArg t.schemeAt (hret 0))) ≫ t.withoutIsoBlowups.isoZero.hom
      = B.withoutIsoBlowups.isoZero.hom ≫ j := by
    simp only [SequenceOfBlowups.withoutIsoBlowups_isoObjZero, SequenceOfBlowups.objNontrivialIndexZeroIso_hom]
    rw [Category.assoc, eqToHom_projectionToBase_consolidated236 t (hret 0)]
    exact hstruct (B.nontrivialIndex 0) (B.nontrivialIndex_le_length (Nat.zero_le B.lengthWithoutIsoBlowups))
  have h3 : ∀ (i : ℕ) (hi : i < B.lengthWithoutIsoBlowups),
      (σ (B.nontrivialIndex (i + 1)) (B.nontrivialIndex_le_length hi) ≫
          eqToHom (congrArg t.schemeAt (hret (i + 1)))) ≫ t.withoutIsoBlowups.transitionMapSucc i
        = B.withoutIsoBlowups.transitionMapSucc i ≫
          (σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length (le_of_lt hi)) ≫
            eqToHom (congrArg t.schemeAt (hret i))) := by
    intro i hi
    simp only [SequenceOfBlowups.withoutIsoBlowups_blowupMorphism]
    exact comp_eqToHom_comp_transitionMap_consolidated236 t (hret i) (hret (i + 1))
      (B.nontrivialIndex_monotone (Nat.le_succ i) : B.nontrivialIndex i ≤ B.nontrivialIndex (i + 1))
      (t.nontrivialIndex_monotone (Nat.le_succ i) : t.nontrivialIndex i ≤ t.nontrivialIndex (i + 1)) _ _ _
      (hdown (B.nontrivialIndex i) (B.nontrivialIndex (i + 1))
        (B.nontrivialIndex_monotone (Nat.le_succ i) : B.nontrivialIndex i ≤ B.nontrivialIndex (i + 1))
        (B.nontrivialIndex_le_length hi))
  have h4 : ∀ (i : ℕ) (hi : i < B.lengthWithoutIsoBlowups),
      t.withoutIsoBlowups.center i = imageIdealSheaf (σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length (le_of_lt hi)) ≫
        eqToHom (congrArg t.schemeAt (hret i))) (B.withoutIsoBlowups.center i) := by
    intro i hi
    simp only [SequenceOfBlowups.withoutIsoBlowups_center]
    exact center_eq_imageIdealSheaf_comp_eqToHom_consolidated236 t (B.center (B.nontrivialIndex i)) (hret i) _
      (hcen (B.nontrivialIndex i) (B.nontrivialIndex_lt_length hi))
  have h5 : ∀ (i : ℕ) (hi : i < B.lengthWithoutIsoBlowups),
      (σ (B.nontrivialIndex (i + 1)) (B.nontrivialIndex_le_length hi) ≫
          eqToHom (congrArg t.schemeAt (hret (i + 1)))).ker
        = Blowup.strictTransform (t.withoutIsoBlowups.transitionMapSucc i) (t.withoutIsoBlowups.center i)
          (σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length (le_of_lt hi)) ≫
            eqToHom (congrArg t.schemeAt (hret i))).ker := by
    intro i hi
    have htopd : ∀ d : ℕ, B.nontrivialIndex i + 1 ≤ d → d < B.nontrivialIndex (i + 1) → t.center d = ⊤ := by
      intro d hd1 hd2
      have hdlt : d < B.length := lt_of_lt_of_le hd2 (B.nontrivialIndex_le_length hi)
      exact (htriv d hdlt).1 (B.center_eq_top_of_nontrivialIndex_lt (Nat.lt_of_succ_le hd1) hd2)
    simp only [SequenceOfBlowups.withoutIsoBlowups_blowupMorphism, SequenceOfBlowups.withoutIsoBlowups_center]
    exact ker_comp_eqToHom_eq_strictTransform_consolidated236 t (hret i) (hret (i + 1))
      (B.nontrivialIndex_monotone (Nat.le_succ i))
      (t.nontrivialIndex_monotone (Nat.le_succ i)) _ _
      (key (B.nontrivialIndex i) (B.nontrivialIndex (i + 1)) (B.succ_le_nontrivialIndex_succ i) htopd
        (B.nontrivialIndex_le_length hi) (B.nontrivialIndex_lt_length hi))
  exact ⟨hplen, fun i hi => σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length hi) ≫
    eqToHom (congrArg t.schemeAt (hret i)), h1, h2, h3, h4, h5⟩

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.StrictTransformClosedImmersion
section

open TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

section
variable {U V : Scheme.{u}} (j : U ⟶ V)

private theorem comap_eq_ker_of_mono_consolidated235 [Mono j]
    (I : V.IdealSheafData) (lam : I.subscheme ⟶ U) (hlam : lam ≫ j = I.subschemeι) :
    I.comap j = Scheme.Hom.ker lam := by
  have hc : I.comap j = Scheme.Hom.ker (Limits.pullback.fst j I.subschemeι) := rfl
  have hcomm : lam ≫ j = 𝟙 I.subscheme ≫ I.subschemeι := by rw [hlam, Category.id_comp]
  obtain ⟨e, hefst, hesnd⟩ : ∃ e : I.subscheme ⟶ Limits.pullback j I.subschemeι,
      e ≫ Limits.pullback.fst j I.subschemeι = lam ∧
        e ≫ Limits.pullback.snd j I.subschemeι = 𝟙 I.subscheme :=
    ⟨Limits.pullback.lift lam (𝟙 I.subscheme) hcomm, Limits.pullback.lift_fst _ _ _,
      Limits.pullback.lift_snd _ _ _⟩
  have hsndlam : Limits.pullback.snd j I.subschemeι ≫ lam
      = Limits.pullback.fst j I.subschemeι := by
    rw [← cancel_mono j, Category.assoc, hlam, ← Limits.pullback.condition]
  have : IsIso e := by
    refine ⟨Limits.pullback.snd j I.subschemeι, hesnd, ?_⟩
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hefst, hsndlam, Category.id_comp]
    · rw [Category.assoc, hesnd, Category.comp_id, Category.id_comp]
  rw [hc]
  exact (ker_eq_ker_of_isIso_comp lam (Limits.pullback.fst j I.subschemeι) e hefst).symm

theorem map_eq_ker_subschemeι_comp (K : U.IdealSheafData) :
    K.map j = Scheme.Hom.ker (K.subschemeι ≫ j) := by
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι]

theorem ker_subschemeι_comp_eq_of_ker_le [IsClosedImmersion j]
    (L : V.IdealSheafData) (hL : Scheme.Hom.ker j ≤ L) (K : U.IdealSheafData)
    (hK : K = L.comap j) :
    Scheme.Hom.ker (K.subschemeι ≫ j) = L := by
  have hle : Scheme.Hom.ker j ≤ Scheme.Hom.ker L.subschemeι := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact hL
  have hfac : IsClosedImmersion.lift j L.subschemeι hle ≫ j = L.subschemeι := by
    rw [IsClosedImmersion.lift_fac]
  have hcomap : L.comap j = Scheme.Hom.ker (IsClosedImmersion.lift j L.subschemeι hle) :=
    comap_eq_ker_of_mono_consolidated235 j L (IsClosedImmersion.lift j L.subschemeι hle) hfac
  rw [hK, hcomap, Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
    ← Scheme.Hom.ker_comp, hfac, Scheme.IdealSheafData.ker_subschemeι]


end

theorem strictTransform_eq_ker_complComapSupport {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    Blowup.strictTransform π Z D =
      Scheme.Hom.ker
        (((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι ≫
          Scheme.Opens.ι (complComapSupport π Z)) := by
  rw [Blowup.strictTransform_eq_ker, Blowup.strictTransformImmersion_eq, Blowup.strictTransformOpens_eq,
    ← complComapSupport_eq]
  exact ker_ι_preimage_comp_subschemeι_eq_ker_comap (D.comap π) (complComapSupport π Z)

section
variable {A A' A₁ A'₁ : Scheme.{u}} (j : A ⟶ A') [IsClosedImmersion j]

theorem preimage_complComapSupport_eq (Z : A.IdealSheafData) (π : A₁ ⟶ A) (π' : A'₁ ⟶ A') (j₁ : A₁ ⟶ A'₁)
    (hsq : j₁ ≫ π' = π ≫ j) :
    (Opens.map j₁.base).obj (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))) =
      complComapSupport π Z := by
  have key : ((Scheme.Hom.ker (Z.subschemeι ≫ j)).comap π').comap j₁ = Z.comap π := by
    rw [← Scheme.IdealSheafData.comap_comp, hsq, Scheme.IdealSheafData.comap_comp,
      ← map_eq_ker_subschemeι_comp, Blowup.comap_map_of_isClosedImmersion]
  have h2 : ((Z.comap π).support : Set A₁)
      = ⇑j₁.base ⁻¹'
        ((((Scheme.Hom.ker (Z.subschemeι ≫ j)).comap π').support : Set A'₁)) := by
    rw [← key, Scheme.IdealSheafData.support_comap
      ((Scheme.Hom.ker (Z.subschemeι ≫ j)).comap π') j₁]
    rfl
  apply TopologicalSpace.Opens.ext
  have h1 : (((Opens.map j₁.base).obj
        (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j)))) : Set A₁)
      = ⇑j₁.base ⁻¹' (((Scheme.Hom.ker (Z.subschemeι ≫ j)).comap π').support : Set A'₁)ᶜ := rfl
  rw [h1, coe_complComapSupport, h2, Set.preimage_compl]

private theorem map_ker_subschemeι_comp_restrict_consolidated235 (D : A.IdealSheafData) (π : A₁ ⟶ A) (π' : A'₁ ⟶ A') (j₁ : A₁ ⟶ A'₁) [IsClosedImmersion j₁]
    (hsq : j₁ ≫ π' = π ≫ j) (V' : A'₁.Opens) [IsClosedImmersion (j₁ ∣_ V')]
    (hkerr : Scheme.Hom.ker (j₁ ∣_ V') ≤
      ((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι) :
    (Scheme.Hom.ker (((D.comap π).comap (j₁ ⁻¹ᵁ V').ι).subschemeι ≫ (j₁ ⁻¹ᵁ V').ι)).map j₁
      = Scheme.Hom.ker
          ((((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι).subschemeι ≫ V'.ι) := by
  have hm : (j₁ ∣_ V') ≫ V'.ι ≫ π' = (j₁ ⁻¹ᵁ V').ι ≫ π ≫ j := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hsq]
  have hMcomap :
      ((((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι).comap (j₁ ∣_ V'))
        = (D.comap π).comap (j₁ ⁻¹ᵁ V').ι := by
    calc ((((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι).comap (j₁ ∣_ V'))
        = (Scheme.Hom.ker (D.subschemeι ≫ j)).comap ((j₁ ∣_ V') ≫ V'.ι ≫ π') := by
          rw [Scheme.IdealSheafData.comap_comp (Scheme.Hom.ker (D.subschemeι ≫ j))
              (j₁ ∣_ V') (V'.ι ≫ π'),
            Scheme.IdealSheafData.comap_comp (Scheme.Hom.ker (D.subschemeι ≫ j)) V'.ι π']
      _ = (Scheme.Hom.ker (D.subschemeι ≫ j)).comap ((j₁ ⁻¹ᵁ V').ι ≫ π ≫ j) := by rw [hm]
      _ = (D.comap π).comap (j₁ ⁻¹ᵁ V').ι := by
          rw [Scheme.IdealSheafData.comap_comp (Scheme.Hom.ker (D.subschemeι ≫ j))
              (j₁ ⁻¹ᵁ V').ι (π ≫ j),
            Scheme.IdealSheafData.comap_comp (Scheme.Hom.ker (D.subschemeι ≫ j)) π j,
            ← map_eq_ker_subschemeι_comp j D, Blowup.comap_map_of_isClosedImmersion j D]
  have hmor : ((((D.comap π).comap (j₁ ⁻¹ᵁ V').ι).subschemeι ≫ (j₁ ⁻¹ᵁ V').ι) ≫ j₁)
      = ((((D.comap π).comap (j₁ ⁻¹ᵁ V').ι).subschemeι ≫ (j₁ ∣_ V')) ≫ V'.ι) := by
    simp only [Category.assoc, morphismRestrict_ι]
  rw [← Scheme.Hom.ker_comp, hmor,
    Scheme.Hom.ker_comp (((D.comap π).comap (j₁ ⁻¹ᵁ V').ι).subschemeι ≫ (j₁ ∣_ V')) V'.ι,
    ker_subschemeι_comp_eq_of_ker_le (j₁ ∣_ V')
      (((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι) hkerr
      ((D.comap π).comap (j₁ ⁻¹ᵁ V').ι) hMcomap.symm,
    Scheme.Hom.ker_comp
      ((((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι).subschemeι) V'.ι,
    Scheme.IdealSheafData.ker_subschemeι]


end

section
variable {A A' A₁ A'₁ : Scheme.{u}} (j : A ⟶ A') [IsClosedImmersion j] (Z D : A.IdealSheafData) (π : A₁ ⟶ A) (π' : A'₁ ⟶ A') (j₁ : A₁ ⟶ A'₁) [IsClosedImmersion j₁] [IsNoetherian A₁] [IsNoetherian A'₁] (hsq : j₁ ≫ π' = π ≫ j)
include hsq

theorem image_strictTransform_eq_strictTransform_image (hker : Scheme.Hom.ker j₁ =
      Blowup.strictTransform π' (Scheme.Hom.ker (Z.subschemeι ≫ j)) (Scheme.Hom.ker j)) :
    Scheme.Hom.ker ((Blowup.strictTransform π Z D).subschemeι ≫ j₁) =
      Blowup.strictTransform π' (Scheme.Hom.ker (Z.subschemeι ≫ j))
        (Scheme.Hom.ker (D.subschemeι ≫ j)) := by
  have : IsClosedImmersion
      (j₁ ∣_ complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))) := inferInstance
  have hDle : Scheme.Hom.ker j ≤ Scheme.Hom.ker (D.subschemeι ≫ j) := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
      ← Scheme.IdealSheafData.map_bot j]
    exact Scheme.IdealSheafData.map_mono j bot_le
  have hUeq : j₁ ⁻¹ᵁ complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))
      = complComapSupport π Z := preimage_complComapSupport_eq j Z π π' j₁ hsq
  have hkerr : Scheme.Hom.ker (j₁ ∣_ complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j)))
      ≤ ((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap
          (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))).ι := by
    rw [← ker_comap_ι_eq_ker_morphismRestrict j₁
        (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))), hker,
      strictTransform_comap_complComapSupport_ι π' (Scheme.Hom.ker (Z.subschemeι ≫ j))
        (Scheme.Hom.ker j)]
    exact Scheme.IdealSheafData.comap_mono
      (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))).ι
      (Scheme.IdealSheafData.comap_mono π' hDle)
  have hTmap : Scheme.Hom.ker ((Blowup.strictTransform π Z D).subschemeι ≫ j₁)
      = (Blowup.strictTransform π Z D).map j₁ := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι]
  rw [hTmap, strictTransform_eq_ker_complComapSupport π Z D, ← hUeq,
    map_ker_subschemeι_comp_restrict_consolidated235 j D π π' j₁ hsq
      (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))) hkerr]
  exact (strictTransform_eq_ker_complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))
    (Scheme.Hom.ker (D.subschemeι ≫ j))).symm

theorem map_strictTransform_eq_strictTransform_map (hker : Scheme.Hom.ker j₁ = Blowup.strictTransform π' (Z.map j) (Scheme.Hom.ker j)) :
    (Blowup.strictTransform π Z D).map j₁ = Blowup.strictTransform π' (Z.map j) (D.map j) := by
  have hZ : Z.map j = Scheme.Hom.ker (Z.subschemeι ≫ j) := map_eq_ker_subschemeι_comp j Z
  have hD : D.map j = Scheme.Hom.ker (D.subschemeι ≫ j) := map_eq_ker_subschemeι_comp j D
  have hT : (Blowup.strictTransform π Z D).map j₁
      = Scheme.Hom.ker ((Blowup.strictTransform π Z D).subschemeι ≫ j₁) :=
    map_eq_ker_subschemeι_comp j₁ (Blowup.strictTransform π Z D)
  rw [hT, hD, hZ]
  exact image_strictTransform_eq_strictTransform_image j Z D π π' j₁ hsq (by rw [hker, hZ])


end

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyBoundedOrder
section

open TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

theorem isOpen_setOf_stalkIdeal_eq_bot {X : Scheme.{u}} [IsLocallyNoetherian X]
    (J : X.IdealSheafData) :
    IsOpen {x : ↥X | stalkIdeal J x = (⊥ : Ideal (X.presheaf.stalk x))} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hx' : stalkIdeal J x = (⊥ : Ideal (X.presheaf.stalk x)) := hx
  obtain ⟨U, hxU⟩ : ∃ U : X.affineOpens, x ∈ (U : X.Opens) := by
    have h1 : x ∈ (⨆ i : X.affineOpens, (i : X.Opens)) := by
      rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp h1
  have : IsNoetherianRing Γ(X, (U : X.Opens)) :=
    AlgebraicGeometry.IsLocallyNoetherian.component_noetherian U
  obtain ⟨s, hs⟩ : (J.ideal U).FG := IsNoetherian.noetherian (J.ideal U)
  have hzero : ∀ g ∈ s, (X.presheaf.germ (U : X.Opens) x hxU).hom g = 0 := by
    intro g hg
    have hgI : g ∈ J.ideal U := by
      rw [← hs]
      exact Submodule.subset_span (Finset.mem_coe.mpr hg)
    have hmem := germ_mem_stalkIdeal J x U hxU hgI
    rw [hx'] at hmem
    simpa using hmem
  have hWex : ∀ g : Γ(X, (U : X.Opens)), ∃ (W : X.Opens) (i : W ⟶ (U : X.Opens)),
      x ∈ W ∧ (g ∈ s → (X.presheaf.map i.op).hom g = 0) := by
    intro g
    by_cases hg : g ∈ s
    · obtain ⟨V, iV, hxV, hi⟩ :=
        X.toLocallyRingedSpace.toRingedSpace.exists_res_eq_zero_of_germ_eq_zero
          (U : X.Opens) g ⟨x, hxU⟩ (hzero g hg)
      exact ⟨V, iV, hxV, fun _ => hi⟩
    · exact ⟨(U : X.Opens), 𝟙 _, hxU, fun h => absurd h hg⟩
  choose W i hxW hres using hWex
  refine ⟨((U : X.Opens) : Set ↥X) ∩
      ⋂ g ∈ (s : Set Γ(X, (U : X.Opens))), ((W g : X.Opens) : Set ↥X), ?_, ?_, ?_⟩
  · rintro y ⟨hyU, hyW⟩
    have hyW' : ∀ g ∈ s, y ∈ W g := fun g hg =>
      Set.mem_iInter₂.mp hyW g (Finset.mem_coe.mpr hg)
    have hmain : ∀ g ∈ s, (X.presheaf.germ (U : X.Opens) y hyU).hom g = 0 := by
      intro g hg
      have h3 : (X.presheaf.germ (W g) y (hyW' g hg)).hom
          ((X.presheaf.map (i g).op).hom g) = 0 := by
        rw [hres g hg, map_zero]
      exact (X.presheaf.germ_res_apply (i g) y (hyW' g hg) g).symm.trans h3
    show stalkIdeal J y = ⊥
    rw [stalkIdeal_eq_map_germ J y U hyU, ← le_bot_iff, Ideal.map_le_iff_le_comap, ← hs,
      Submodule.span_le]
    intro g hg
    have hg0 := hmain g (Finset.mem_coe.mp hg)
    have hmem : (X.presheaf.germ (U : X.Opens) y hyU).hom g ∈
        (⊥ : Ideal (X.presheaf.stalk y)) := by
      rw [hg0]
      exact Submodule.zero_mem _
    simpa using hmem
  · exact (TopologicalSpace.Opens.isOpen (U : X.Opens)).inter
      (Set.Finite.isOpen_biInter s.finite_toSet
        (fun g _ => TopologicalSpace.Opens.isOpen (W g)))
  · exact ⟨hxU, Set.mem_iInter₂.mpr (fun g _ => hxW g)⟩

section
variable (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
include hT

private theorem isLocallyNoetherian_of_isAdmissible_consolidated135 :
    IsLocallyNoetherian T.scheme := by
  have := hT.locallyOfFiniteType
  have : IsNoetherianRing T.base := inferInstance
  constructor
  intro U
  exact @isNoetherianRing_sections T.base _ _ T.scheme T.structMap _ U
    (sectionsAlgebra T.base T.structMap U.1)
    (algebraMap_sectionsAlgebra T.base T.structMap U.1)

private theorem stalkIdeal_ne_bot_of_isAdmissible_of_nonzeroOnComponents_consolidated135 (J : T.scheme.IdealSheafData) (hJ : NonzeroOnComponents J) (x : ↥T.scheme) :
    stalkIdeal J x ≠ ⊥ := by
  have := isLocallyNoetherian_of_isAdmissible_consolidated135 T hT
  intro hbot
  obtain ⟨y, hyC, hyJ⟩ := Set.not_subset.mp
    (hJ (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x))
  have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hcl : IsClosed ((J.support : Set ↥T.scheme)) := J.support.2
  obtain ⟨z, hzC, hz1, hz2⟩ :=
    hirr.2 {w : ↥T.scheme | stalkIdeal J w = ⊥} ((J.support : Set ↥T.scheme)ᶜ)
      (isOpen_setOf_stalkIdeal_eq_bot J) hcl.isOpen_compl
      ⟨x, mem_irreducibleComponent, hbot⟩ ⟨y, hyC, hyJ⟩
  have hz1' : stalkIdeal J z = ⊥ := hz1
  have hztop : stalkIdeal J z = ⊤ := by
    by_contra hne
    exact hz2 ((mem_support_iff_stalkIdeal_ne_top J z).2 hne)
  have h1 : (1 : T.scheme.presheaf.stalk z) ∈ (⊥ : Ideal (T.scheme.presheaf.stalk z)) := by
    rw [← hz1', hztop]
    exact Submodule.mem_top
  rw [Ideal.mem_bot] at h1
  exact one_ne_zero h1

theorem exists_orderAt_le (J : T.scheme.IdealSheafData) (hJ : NonzeroOnComponents J) :
    ∃ B : ℕ, ∀ x : ↥T.scheme, orderAt J x ≤ (B : ℕ∞) := by
  have := hT.charZero
  have := hT.smooth
  have := hT.locallyOfFiniteType
  have := isLocallyNoetherian_of_isAdmissible_consolidated135 T hT
  have hfin : ∀ x : ↥T.scheme, orderAt J x ≠ ⊤ := fun x =>
    orderAt_ne_top_of_stalkIdeal_ne_bot J x
      (stalkIdeal_ne_bot_of_isAdmissible_of_nonzeroOnComponents_consolidated135 T hT J hJ x)
  have hclosed : ∀ m : ℕ, IsClosed (orderAtLeastLocus J m) := fun m =>
    isClosed_orderAtLeastLocus T.base T.structMap J m
  have hspec : IsCompact (Set.univ : Set ↥(Spec (CommRingCat.of T.base))) := by
    simp
  have hcpt : IsCompact (Set.univ : Set ↥T.scheme) := by
    have h := hT.quasiCompact.isCompact_preimage Set.univ isOpen_univ hspec
    simpa using h
  have hempty : (Set.univ : Set ↥T.scheme) ∩ (⋂ m : ℕ, orderAtLeastLocus J m) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨x, -, hx⟩
    have hx' := Set.mem_iInter.mp hx
    have h1 : ∀ m : ℕ, (m : ℕ∞) ≤ orderAt J x := fun m => (mem_orderAtLeastLocus_iff J m x).1 (hx' m)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, orderAt J x = (n : ℕ∞) :=
      ⟨(orderAt J x).toNat, (ENat.natCast_toNat (hfin x)).symm⟩
    have h3 : ((n + 1 : ℕ) : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := by
      rw [← hn]
      exact h1 (n + 1)
    have h4 : n + 1 ≤ n := by exact_mod_cast h3
    omega
  obtain ⟨u, hu⟩ := hcpt.elim_finite_subfamily_closed (fun m : ℕ => orderAtLeastLocus J m) hclosed (Set.disjoint_iff_inter_eq_empty.mpr hempty)
  have hMempty : ¬ ((Set.univ : Set ↥T.scheme) ∩ ⋂ i ∈ u, orderAtLeastLocus J i).Nonempty := by
    rw [Set.not_nonempty_iff_eq_empty]
    exact Set.disjoint_iff_inter_eq_empty.mp hu
  refine ⟨u.sup id, fun x => ?_⟩
  have hxnot : x ∉ orderAtLeastLocus J (u.sup id) := by
    intro hx
    refine hMempty ⟨x, Set.mem_univ x, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    exact orderAtLeastLocus_subset_of_le J (Finset.le_sup (f := id) hi) hx
  rw [mem_orderAtLeastLocus_iff] at hxnot
  exact le_of_lt (not_le.mp hxnot)


end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
section


section
namespace FunctorialResolution.EmbeddedResolution

section

variable {Y : Scheme.{u}}

def intersectionIdeal (L : List Y.IdealSheafData) (J : Finset (Fin L.length)) : Y.IdealSheafData :=
  ⨆ j ∈ J, L.get j

@[simp]
theorem intersectionIdeal_eq_iSup (L : List Y.IdealSheafData) (J : Finset (Fin L.length)) :
    intersectionIdeal L J = ⨆ j ∈ J, L.get j := rfl

def intersectionComponents (L : List Y.IdealSheafData) (J : Finset (Fin L.length)) : Set (Set ↥Y) :=
  {C | IsIrreducible C ∧ C ⊆ ((intersectionIdeal L J).support : Set ↥Y) ∧
    ∀ C' : Set ↥Y, IsIrreducible C' → C ⊆ C' → C' ⊆ ((intersectionIdeal L J).support : Set ↥Y) → C' = C}

open Classical in
def orderAlong (I : Y.IdealSheafData) (C : Set ↥Y) : ℕ∞ :=
  if h : IsIrreducible C then orderAt I h.genericPoint else 0

def IsCandidateComponent (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) (r : ℕ)
    (J : Finset (Fin L.length)) (C : Set ↥Y) : Prop :=
  J.card = r ∧ C ∈ intersectionComponents L J ∧ (m : ℕ∞) ≤ orderAlong I C

def minIndexCard (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) : ℕ :=
  sInf {r : ℕ | 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y), IsCandidateComponent I m L r J C}

def maxCandidateOrder (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) : ℕ∞ :=
  ⨆ (J : Finset (Fin L.length)) (C : Set ↥Y)
    (_ : IsCandidateComponent I m L (minIndexCard I m L) J C), orderAlong I C

def IsMaxOrderIndexSet (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) : Prop :=
  ∃ C : Set ↥Y, IsCandidateComponent I m L (minIndexCard I m L) J C ∧ orderAlong I C = maxCandidateOrder I m L

def binaryEncode {n : ℕ} (J : Finset (Fin n)) : ℕ :=
  ∑ j ∈ J, 2 ^ (n - 1 - (j : ℕ))

def maxBinaryCode (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) : ℕ :=
  sSup {c : ℕ | ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J ∧ binaryEncode J = c}

open Classical in
def lexMaxIndices (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) :
    Finset (Fin L.length) :=
  if h : ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J ∧ binaryEncode J = maxBinaryCode I m L then
    h.choose
  else ∅

def monomialCenterSet (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) : Set ↥Y :=
  ⋃₀ {C : Set ↥Y |
    IsCandidateComponent I m L (minIndexCard I m L) (lexMaxIndices I m L) C ∧ orderAlong I C = maxCandidateOrder I m L}

def openSublocusIdeal {V : Scheme.{u}} (ι : V ⟶ Y) (S : Set ↥V) (hS : IsOpen S) : Y.IdealSheafData :=
  AlgebraicGeometry.Scheme.Hom.ker
    (AlgebraicGeometry.Scheme.Opens.ι (X := V) ⟨S, hS⟩ ≫ ι)

open Classical in
def monomialCenter (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) : Y.IdealSheafData :=
  if h : minIndexCard I m L ≠ 0 ∧
      IsOpen (⇑(intersectionIdeal L (lexMaxIndices I m L)).subschemeι.base ⁻¹' monomialCenterSet I m L) then
    openSublocusIdeal (intersectionIdeal L (lexMaxIndices I m L)).subschemeι
      (⇑(intersectionIdeal L (lexMaxIndices I m L)).subschemeι.base ⁻¹' monomialCenterSet I m L) h.2
  else ⊤

end

namespace MarkedBlowupSequenceData

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def centerAtLast (d : MarkedBlowupSequenceData p I m E) : (d.obj d.length).IdealSheafData :=
  monomialCenter (d.ideal d.length) m (d.boundary d.length)

def IsAdmissibleCenter (d : MarkedBlowupSequenceData p I m E) : Prop :=
  centerAtLast d ≠ ⊤ ∧
  Smooth ((centerAtLast d).subschemeι ≫ d.proj d.length ≫ p) ∧
  HasStrictNormalCrossingsWith (d.proj d.length ≫ p) (centerAtLast d) (d.boundary d.length) ∧
  (((centerAtLast d).support : Set ↥(d.obj d.length)) ⊆ orderAtLeastLocus (d.ideal d.length) m) ∧
  (∃ B : (Blowup.blowup (centerAtLast d)).IdealSheafData,
    ((centerAtLast d).comap (Blowup.blowup.proj (centerAtLast d))) ^ m * B =
      (d.ideal d.length).comap (Blowup.blowup.proj (centerAtLast d)))

open Classical in
def blowupAtCenter (hinv : ComapIsoInvariance.{u}) (d : MarkedBlowupSequenceData p I m E) :
    MarkedBlowupSequenceData p I m E :=
  if h : IsAdmissibleCenter d then
    d.append
      (ofSingleBlowup (d.proj d.length ≫ p) (d.ideal d.length) m (d.boundary d.length)
        (centerAtLast d) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2) hinv
  else d

def monomialBlowupIterate (hinv : ComapIsoInvariance.{u}) (d : MarkedBlowupSequenceData p I m E) :
    ℕ → MarkedBlowupSequenceData p I m E
  | 0 => d
  | (n + 1) => blowupAtCenter hinv (monomialBlowupIterate hinv d n)

section
variable (hinv : ComapIsoInvariance.{u}) (d : MarkedBlowupSequenceData p I m E)

theorem monomialBlowupIterate_zero :
    monomialBlowupIterate hinv d 0 = d := rfl

theorem monomialBlowupIterate_succ (n : ℕ) :
    monomialBlowupIterate hinv d (n + 1) = blowupAtCenter hinv (monomialBlowupIterate hinv d n) := rfl


end

def IsStationaryAt (hinv : ComapIsoInvariance.{u}) (d : MarkedBlowupSequenceData p I m E) (n : ℕ) : Prop :=
  (monomialBlowupIterate hinv d (n + 1)).length = (monomialBlowupIterate hinv d n).length

end

end MarkedBlowupSequenceData

section

variable {k : Type u} [Field k] {X : Scheme.{u}}

def monomialBlowupSeq (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) : MarkedBlowupSequenceData p I m E :=
  MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E)
    (sInf {n : ℕ | MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) n})

end

def monomialPrincipalization (hinv : ComapIsoInvariance.{u}) : PrincipalizationAssignment.{u} :=
  fun T => (monomialBlowupSeq hinv T.structMap T.ideal T.mult T.boundary).toMarkedSequenceOfBlowups

theorem monomialPrincipalization_apply (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) :
    monomialPrincipalization hinv T =
      (monomialBlowupSeq hinv T.structMap T.ideal T.mult T.boundary).toMarkedSequenceOfBlowups := rfl

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IsomorphismTransport
section


section
namespace FunctorialResolution.EmbeddedResolution

section
variable {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]

private theorem comap_eq_ker_subschemeι_comp_inv_consolidated90 (I : B.IdealSheafData) :
    I.comap f = (I.subschemeι ≫ inv f).ker := by
  have : IsIso (Limits.pullback.snd f I.subschemeι) :=
    (IsPullback.of_hasPullback f I.subschemeι).flip.isIso_fst_of_isIso
  have hw : Limits.pullback.fst f I.subschemeι
      = Limits.pullback.snd f I.subschemeι ≫ I.subschemeι ≫ inv f := by
    rw [← Category.assoc, ← Limits.pullback.condition, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  unfold AlgebraicGeometry.Scheme.IdealSheafData.comap
  rw [hw, AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]

theorem imageIdealSheaf_eq_comap_inv (J : A.IdealSheafData) :
    imageIdealSheaf f J = J.comap (inv f) := by
  rw [imageIdealSheaf_eq_ker, comap_eq_ker_subschemeι_comp_inv_consolidated90 (inv f) J, IsIso.inv_inv]

theorem imageIdealSheaf_comap (I : B.IdealSheafData) :
    imageIdealSheaf f (I.comap f) = I := by
  rw [imageIdealSheaf_eq_comap_inv, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    IsIso.inv_hom_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]

theorem comap_imageIdealSheaf (J : A.IdealSheafData) :
    (imageIdealSheaf f J).comap f = J := by
  rw [imageIdealSheaf_eq_comap_inv, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    IsIso.hom_inv_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]


end

theorem ker_comp_eq_imageIdealSheaf_ker {W A B : Scheme.{u}} (g : W ⟶ A) (w : A ⟶ B) :
    (g ≫ w).ker = imageIdealSheaf w g.ker := by
  rw [imageIdealSheaf_eq_ker, AlgebraicGeometry.Scheme.Hom.ker_comp,
    AlgebraicGeometry.Scheme.Hom.ker_comp, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]

private theorem exists_iso_subscheme_comap_of_isIso_consolidated90 {A B : Scheme.{u}} (w : A ⟶ B) [IsIso w]
    (I : B.IdealSheafData) :
    ∃ θ : (I.comap w).subscheme ≅ I.subscheme,
      θ.hom ≫ I.subschemeι = (I.comap w).subschemeι ≫ w := by
  have e1 : ((I.comap w).subschemeι ≫ w).ker = I := by
    rw [ker_comp_eq_imageIdealSheaf_ker, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι,
      imageIdealSheaf_comap]
  have e2 : (I.subschemeι ≫ inv w).ker = I.comap w := by
    rw [ker_comp_eq_imageIdealSheaf_ker, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι,
      imageIdealSheaf_eq_comap_inv, IsIso.inv_inv]
  have h1 : I.subschemeι.ker ≤ ((I.comap w).subschemeι ≫ w).ker :=
    le_of_eq (by rw [e1, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι])
  have h2 : (I.comap w).subschemeι.ker ≤ (I.subschemeι ≫ inv w).ker :=
    le_of_eq (by rw [e2, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι])
  refine ⟨⟨IsClosedImmersion.lift I.subschemeι ((I.comap w).subschemeι ≫ w) h1,
    IsClosedImmersion.lift (I.comap w).subschemeι (I.subschemeι ≫ inv w) h2, ?_, ?_⟩, ?_⟩
  · rw [← cancel_mono (I.comap w).subschemeι, Category.assoc, IsClosedImmersion.lift_fac,
      ← Category.assoc, IsClosedImmersion.lift_fac, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id, Category.id_comp]
  · rw [← cancel_mono I.subschemeι, Category.assoc, IsClosedImmersion.lift_fac,
      ← Category.assoc, IsClosedImmersion.lift_fac, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, Category.id_comp]
  · exact IsClosedImmersion.lift_fac ..

theorem imageIdealSheaf_comp_comap_of_isIso {A B C : Scheme.{u}} (w : A ⟶ B) [IsIso w] (g : B ⟶ C)
    (I : B.IdealSheafData) :
    imageIdealSheaf (w ≫ g) (I.comap w) = imageIdealSheaf g I := by
  obtain ⟨θ, hθ⟩ := exists_iso_subscheme_comap_of_isIso_consolidated90 w I
  rw [imageIdealSheaf_eq_ker (w ≫ g) (I.comap w), imageIdealSheaf_eq_ker g I, ← Category.assoc, ← hθ,
    Category.assoc, AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]

private theorem compl_support_comap_consolidated90 {A B : Scheme.{u}} (v : A ⟶ B) (I : B.IdealSheafData) :
    (I.comap v).support.compl = (TopologicalSpace.Opens.map v.base).obj I.support.compl := by
  ext x
  simp [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]

private theorem opens_map_comp_consolidated90 {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (U : C.Opens) :
    (TopologicalSpace.Opens.map (f ≫ g).base).obj U
      = (TopologicalSpace.Opens.map f.base).obj ((TopologicalSpace.Opens.map g.base).obj U) := by
  ext x
  simp

private theorem opens_map_id_consolidated90 {B : Scheme.{u}} (W : B.Opens) :
    (TopologicalSpace.Opens.map (𝟙 B : B ⟶ B).base).obj W = W := by
  ext x
  exact Iff.rfl

private theorem exists_iso_opens_preimage_consolidated90 {A B : Scheme.{u}} (θ : A ≅ B) (V' : A.Opens) (V : B.Opens)
    (hVV' : V' = (TopologicalSpace.Opens.map θ.hom.base).obj V) :
    ∃ c : (↑V' : Scheme.{u}) ≅ (↑V : Scheme.{u}), c.hom ≫ V.ι = V'.ι ≫ θ.hom := by
  have hcomp : (TopologicalSpace.Opens.map θ.inv.base).obj V'
      = (TopologicalSpace.Opens.map (θ.inv ≫ θ.hom).base).obj V := by
    rw [hVV', opens_map_comp_consolidated90]
  have hle : V ≤ (TopologicalSpace.Opens.map θ.inv.base).obj V' :=
    le_of_eq (by rw [hcomp, Iso.inv_hom_id, opens_map_id_consolidated90])
  refine ⟨⟨Scheme.Hom.resLE θ.hom V V' (le_of_eq hVV'),
    Scheme.Hom.resLE θ.inv V' V hle, ?_, ?_⟩, ?_⟩
  · rw [← cancel_mono V'.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [← cancel_mono V.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  · exact Scheme.Hom.resLE_comp_ι ..

private theorem ker_eq_of_iso_comp_consolidated90 {P Q T : Scheme.{u}} (c : Q ≅ P) (h₁ : P ⟶ T) (h₂ : Q ⟶ T)
    (hc : c.hom ≫ h₁ = h₂) : h₁.ker = h₂.ker := by
  rw [← hc, AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]

theorem imageIdealSheaf_strictTransform_of_comm_sq {X X₁ Y Y₁ : Scheme.{u}}
    (φ : X₁ ⟶ X) (ψ : Y₁ ⟶ Y) (u : X ⟶ Y) (u₁ : X₁ ⟶ Y₁) [IsIso u] [IsIso u₁]
    (hsq : u₁ ≫ ψ = φ ≫ u) (Z D : X.IdealSheafData) :
    imageIdealSheaf u₁ (Blowup.strictTransform φ Z D)
      = Blowup.strictTransform ψ (imageIdealSheaf u Z) (imageIdealSheaf u D) := by
  have hψ : ψ = inv u₁ ≫ φ ≫ u := by
    rw [← hsq, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hmaps : ψ ≫ inv u = inv u₁ ≫ φ := by
    rw [hψ, Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hcm : ∀ I : X.IdealSheafData,
      (imageIdealSheaf u I).comap ψ = (I.comap φ).comap (inv u₁) := by
    intro I
    rw [imageIdealSheaf_eq_comap_inv,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hmaps]
  obtain ⟨θ, hθ⟩ := exists_iso_subscheme_comap_of_isIso_consolidated90 (inv u₁) (D.comap φ)
  have hVV' : (TopologicalSpace.Opens.map ((D.comap φ).comap (inv u₁)).subschemeι.base).obj
        ((Z.comap φ).comap (inv u₁)).support.compl
      = (TopologicalSpace.Opens.map θ.hom.base).obj
        ((TopologicalSpace.Opens.map (D.comap φ).subschemeι.base).obj
          (Z.comap φ).support.compl) := by
    rw [compl_support_comap_consolidated90, ← opens_map_comp_consolidated90, ← opens_map_comp_consolidated90, hθ]
  obtain ⟨c, hc⟩ := exists_iso_opens_preimage_consolidated90 θ _ _ hVV'
  rw [Blowup.strictTransform_eq_ker, Blowup.strictTransform_eq_ker, Blowup.strictTransformImmersion_eq,
    Blowup.strictTransformImmersion_eq, Blowup.strictTransformOpens_eq, Blowup.strictTransformOpens_eq,
    hcm Z, hcm D, ← ker_comp_eq_imageIdealSheaf_ker]
  refine ker_eq_of_iso_comp_consolidated90 c _ _ ?_
  simp only [Category.assoc]
  rw [← Category.assoc c.hom, hc, Category.assoc, reassoc_of% hθ]
  simp

namespace IsPushforwardBlowupSeq

theorem of_isomorphic {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    {BS : SequenceOfBlowups S} {B B' : SequenceOfBlowups X}
    (h : IsPushforwardBlowupSeq j BS B) (he : B.Isomorphic B') :
    IsPushforwardBlowupSeq j BS B' := by
  obtain ⟨hlen, σ, hci, h0, hstep, hcent, hker⟩ := h
  obtain ⟨hlen2, e, he0, hestep, hecent⟩ := he
  have hestep' : ∀ (i : ℕ) (hp : i + 1 ≤ B.length) (hq : i ≤ B.length),
      (e (i + 1) hp).hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ (e i hq).hom :=
    fun i hp _ => hestep i hp
  have hecent' : ∀ (i : ℕ) (hp : i < B.length) (hq : i ≤ B.length),
      (B'.center i).comap (e i hq).hom = B.center i := fun i hp _ => hecent i hp
  refine ⟨by omega, fun i hi => σ i hi ≫ (e i (by omega)).hom, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := hci i hi
    infer_instance
  · have hgoal : (σ 0 (Nat.zero_le _) ≫ (e 0 (Nat.zero_le _)).hom) ≫ B'.isoZero.hom
        = BS.isoZero.hom ≫ j := by
      rw [Category.assoc, he0, h0]
    exact hgoal
  · intro i hi
    have hiB : i < B.length := by omega
    have hgoal : (σ (i + 1) hi ≫ (e (i + 1) hiB).hom) ≫ B'.transitionMapSucc i
        = BS.transitionMapSucc i ≫ (σ i hi.le ≫ (e i hiB.le).hom) := by
      rw [Category.assoc, hestep' i hiB hiB.le, ← Category.assoc, hstep i hi, Category.assoc]
    exact hgoal
  · intro i hi
    have hiB : i < B.length := by omega
    have hgoal : imageIdealSheaf (σ i hi.le ≫ (e i hiB.le).hom) (BS.center i) = B'.center i := by
      rw [imageIdealSheaf_comp, ← hcent i hi, ← hecent' i hiB hiB.le,
        imageIdealSheaf_comap]
    exact hgoal.symm
  · intro i hi
    have hiB : i < B.length := by omega
    have hcen : imageIdealSheaf (e i hiB.le).hom (B.center i) = B'.center i := by
      rw [← hecent' i hiB hiB.le, imageIdealSheaf_comap]
    have hgoal : (σ (i + 1) hi ≫ (e (i + 1) hiB).hom).ker
        = Blowup.strictTransform (B'.transitionMapSucc i) (B'.center i)
            ((σ i hi.le ≫ (e i hiB.le).hom).ker) := by
      rw [ker_comp_eq_imageIdealSheaf_ker, hker i hi,
        imageIdealSheaf_strictTransform_of_comm_sq (B.transitionMapSucc i) (B'.transitionMapSucc i)
          (e i hiB.le).hom (e (i + 1) hiB).hom (hestep' i hiB hiB.le) (B.center i)
          ((σ i hi.le).ker),
        hcen, ker_comp_eq_imageIdealSheaf_ker]
    exact hgoal

theorem isIso_comp {S' S X : Scheme.{u}} (e : S' ⟶ S) [IsIso e]
    (j : S ⟶ X) [IsClosedImmersion j] (j' : S' ⟶ X) [IsClosedImmersion j']
    (hj : j' = e ≫ j)
    {BS' : SequenceOfBlowups S'} {BS : SequenceOfBlowups S} {B : SequenceOfBlowups X}
    (hpb : IsStrictPullbackBlowupSeq e BS' BS) (h : IsPushforwardBlowupSeq j BS B) :
    IsPushforwardBlowupSeq j' BS' B := by
  obtain ⟨hlen2, τ, hτ0, hτsq, hτcent⟩ := hpb
  obtain ⟨hlen, σ, hci, h0, hstep, hcent, hker⟩ := h
  have hτ0' : ∀ hp : (0 : ℕ) ≤ BS'.length,
      τ 0 hp ≫ BS.isoZero.hom = BS'.isoZero.hom ≫ e := fun _ => hτ0
  have hiso : ∀ (i : ℕ) (hi : i ≤ BS'.length), IsIso (τ i hi) := by
    intro i
    induction i with
    | zero =>
        intro hi
        have hzz : τ 0 hi = BS'.isoZero.hom ≫ e ≫ BS.isoZero.inv := by
          rw [← Category.assoc, ← hτ0' hi]
          simp
        rw [hzz]
        infer_instance
    | succ n ih =>
        intro hi
        have hn : n < BS'.length := by omega
        have := ih (by omega)
        exact (hτsq n hn).isIso_fst_of_isIso
  refine ⟨by omega, fun i hi => τ i hi ≫ σ i (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := hiso i hi
    have := hci i (by omega)
    infer_instance
  · have hgoal : (τ 0 (Nat.zero_le _) ≫ σ 0 (Nat.zero_le _)) ≫ B.isoZero.hom
        = BS'.isoZero.hom ≫ j' := by
      rw [hj, Category.assoc, h0, ← Category.assoc, hτ0, Category.assoc]
    exact hgoal
  · intro i hi
    have hiS : i < BS.length := by omega
    have hgoal : (τ (i + 1) hi ≫ σ (i + 1) hiS) ≫ B.transitionMapSucc i
        = BS'.transitionMapSucc i ≫ (τ i hi.le ≫ σ i hiS.le) := by
      rw [Category.assoc, hstep i hiS, ← Category.assoc, (hτsq i hi).w, Category.assoc]
    exact hgoal
  · intro i hi
    have hiS : i < BS.length := by omega
    have := hiso i hi.le
    have hgoal : imageIdealSheaf (τ i hi.le ≫ σ i hiS.le) (BS'.center i) = B.center i := by
      rw [hτcent i hi, hcent i hiS]
      exact imageIdealSheaf_comp_comap_of_isIso (τ i hi.le) (σ i hiS.le) (BS.center i)
    exact hgoal.symm
  · intro i hi
    have hiS : i < BS.length := by omega
    have := hiso (i + 1) hi
    have := hiso i hi.le
    have hgoal : (τ (i + 1) hi ≫ σ (i + 1) hiS).ker
        = Blowup.strictTransform (B.transitionMapSucc i) (B.center i) ((τ i hi.le ≫ σ i hiS.le).ker) := by
      rw [AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso,
        AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]
      exact hker i hiS
    exact hgoal

theorem of_length_eq_zero {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X)
    (hS : BS.length = 0) (hX : B.length = 0) :
    IsPushforwardBlowupSeq j BS B := by
  have key : ∀ i : ℕ, i ≤ BS.length → i = 0 := fun i hi => by omega
  refine ⟨by omega, fun i hi =>
      eqToHom (congrArg BS.schemeAt (key i hi)) ≫ BS.isoZero.hom ≫ j ≫ B.isoZero.inv ≫
        eqToHom (congrArg B.schemeAt (key i hi).symm), ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    infer_instance
  · simp
  · intro i hi
    exact absurd hi (by omega)
  · intro i hi
    exact absurd hi (by omega)
  · intro i hi
    exact absurd hi (by omega)

end IsPushforwardBlowupSeq

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.IsoBlowupPushforward
section

open Opposite

section
namespace FunctorialResolution.EmbeddedResolution

private theorem isIso_subschemeι_comap_bot_consolidated121 {X X' : Scheme.{u}} (π : X' ⟶ X) :
    IsIso ((⊥ : X.IdealSheafData).comap π).subschemeι := by
  rw [show (⊥ : X.IdealSheafData).comap π = ⊥ from by simp]
  infer_instance

theorem ker_preimage_ι_comp_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (U : Y.Opens) :
    ((f ⁻¹ᵁ U).ι ≫ f).ker = U.ι.ker := by
  have : IsIso (AlgebraicGeometry.morphismRestrict f U) := inferInstance
  rw [← (isPullback_morphismRestrict f U).w]
  exact Scheme.Hom.ker_comp_of_isIso ..

section
variable {X : Scheme.{u}}

theorem section_eq_zero_of_locally_zero (U : X.Opens)
    (s : X.presheaf.obj (op U))
    (h : ∀ x ∈ U, ∃ V : X.Opens, ∃ hV : V ≤ U, x ∈ V ∧
      X.presheaf.map (homOfLE hV).op s = 0) :
    s = 0 := by
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro x hx
  obtain ⟨V, hV, hxV, hs⟩ := h x hx
  have h1 : X.presheaf.germ V x hxV (X.presheaf.map (homOfLE hV).op s)
      = X.presheaf.germ U x hx s := X.presheaf.germ_res_apply (homOfLE hV) x hxV s
  rw [hs, map_zero] at h1
  show X.presheaf.germ U x hx s = X.presheaf.germ U x hx 0
  rw [map_zero]
  exact h1.symm

private theorem map_homOfLE_map_homOfLE_consolidated121 {V V' V'' : X.Opens} (h1 : V' ≤ V) (h2 : V'' ≤ V')
    (s : Γ(X, V)) :
    X.presheaf.map (homOfLE h2).op (X.presheaf.map (homOfLE h1).op s)
      = X.presheaf.map (homOfLE (h2.trans h1)).op s := by
  have hcomp : X.presheaf.map (homOfLE h1).op ≫ X.presheaf.map (homOfLE h2).op
      = X.presheaf.map (homOfLE (h2.trans h1)).op := by
    rw [← Functor.map_comp]
    rfl
  exact congrArg (fun φ : Γ(X, V) ⟶ Γ(X, V'') => (ConcreteCategory.hom φ) s) hcomp

private theorem map_eq_zero_of_app_ι_eq_zero_consolidated121 (W V V' : X.Opens) (s : Γ(X, V))
    (hs : (W.ι.app V).hom s = 0) (h1 : V' ≤ V) (h2 : ∀ y : ↥X, y ∈ V' → y ∈ W) :
    X.presheaf.map (homOfLE h1).op s = 0 := by
  have hT : W.ι ''ᵁ W.ι ⁻¹ᵁ V ≤ V := by
    rintro y ⟨z, hz, rfl⟩
    exact hz
  have hle : V' ≤ W.ι ''ᵁ W.ι ⁻¹ᵁ V := by
    intro y hy
    exact ⟨⟨y, h2 y hy⟩, h1 hy, rfl⟩
  have hzero : X.presheaf.map (homOfLE hT).op s = 0 := by
    rw [Scheme.Opens.ι_app] at hs
    exact hs
  rw [← map_homOfLE_map_homOfLE_consolidated121 hT hle s, hzero, map_zero]

private theorem algebraMap_basicOpen_consolidated121 {U : X.Opens} (f : Γ(X, U)) (t : Γ(X, U)) :
    algebraMap Γ(X, U) Γ(X, X.basicOpen f) t
      = X.presheaf.map (homOfLE (X.basicOpen_le f)).op t := rfl

private theorem notMem_support_of_mem_basicOpen_consolidated121 (I : X.IdealSheafData) (U : X.affineOpens)
    (f : Γ(X, U.1)) (hf : f ∈ I.ideal U) (y : ↥X) (hy : y ∈ X.basicOpen f) :
    y ∉ I.support := by
  intro hmem
  have h1 : y ∈ I.supportSet := hmem
  rw [Scheme.IdealSheafData.mem_supportSet_iff] at h1
  have h2 := h1 U
  rw [Scheme.mem_zeroLocus_iff] at h2
  exact h2 f hf hy

private theorem map_basicOpen_eq_zero_of_app_ι_eq_zero_consolidated121 (W V U₀ : X.Opens)
    (hU₀ : IsAffineOpen U₀)
    (s : Γ(X, V)) (hs : (W.ι.app V).hom s = 0)
    (f : Γ(X, U₀)) (hf : f ∈ nonZeroDivisors Γ(X, U₀))
    (hWf : ∀ y : ↥X, y ∈ X.basicOpen f → y ∈ W)
    (b : Γ(X, U₀)) (hbV : X.basicOpen b ≤ V) :
    X.presheaf.map (homOfLE hbV).op s = 0 := by
  have hAaff : IsAffineOpen (X.basicOpen b) := hU₀.basicOpen b
  have := hU₀.isLocalization_basicOpen b
  have hAU₀ : X.basicOpen b ≤ U₀ := X.basicOpen_le b
  have hgnzd : X.presheaf.map (homOfLE hAU₀).op f ∈ nonZeroDivisors Γ(X, X.basicOpen b) := by
    have hq : X.presheaf.map (homOfLE hAU₀).op f
        = algebraMap Γ(X, U₀) Γ(X, X.basicOpen b) f := rfl
    rw [hq]
    exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers b) Γ(X, X.basicOpen b) hf
  have hbg : X.basicOpen (X.presheaf.map (homOfLE hAU₀).op f)
      = X.basicOpen b ⊓ X.basicOpen f := by
    rw [Scheme.basicOpen_res]
  have hgV : X.basicOpen (X.presheaf.map (homOfLE hAU₀).op f) ≤ V :=
    (X.basicOpen_le _).trans hbV
  have hres : X.presheaf.map (homOfLE hgV).op s = 0 := by
    refine map_eq_zero_of_app_ι_eq_zero_consolidated121 W V _ s hs hgV ?_
    intro y hy
    rw [hbg] at hy
    exact hWf y hy.2
  have := hAaff.isLocalization_basicOpen (X.presheaf.map (homOfLE hAU₀).op f)
  have hres' : algebraMap Γ(X, X.basicOpen b)
      Γ(X, X.basicOpen (X.presheaf.map (homOfLE hAU₀).op f))
      (X.presheaf.map (homOfLE hbV).op s) = 0 := by
    rw [algebraMap_basicOpen_consolidated121, map_homOfLE_map_homOfLE_consolidated121]
    exact hres
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (X.presheaf.map (homOfLE hAU₀).op f))
    Γ(X, X.basicOpen (X.presheaf.map (homOfLE hAU₀).op f))
    (X.presheaf.map (homOfLE hbV).op s)).mp hres'
  obtain ⟨n, hn⟩ := m.2
  have hmem : (m : Γ(X, X.basicOpen b)) ∈ nonZeroDivisors Γ(X, X.basicOpen b) := by
    rw [← hn]
    exact pow_mem hgnzd n
  refine (mem_nonZeroDivisors_iff.mp hmem).1 (X.presheaf.map (homOfLE hbV).op s) ?_
  exact hm

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.ker_supportCompl_ι_eq_bot {I : X.IdealSheafData}
    (h : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor I) :
    (Scheme.Opens.ι (X := X) I.support.compl).ker = ⊥ := by
  refine le_antisymm (fun U => ?_) bot_le
  intro s hs
  have hs' : s ∈ RingHom.ker ((Scheme.Opens.ι (X := X) I.support.compl).app U.1).hom :=
    Scheme.IdealSheafData.ideal_ofIdeals_le _ U hs
  rw [show (⊥ : X.IdealSheafData).ideal U = ⊥ from by simp, Ideal.mem_bot]
  refine EmbeddedResolution.section_eq_zero_of_locally_zero U.1 s ?_
  intro x hx
  obtain ⟨U₀, f, hxU₀, hfnzd, hIf⟩ := h x
  obtain ⟨a, b, hab, hxa⟩ := exists_basicOpen_le_affine_inter U.2 U₀.2 x ⟨hx, hxU₀⟩
  have hbV : X.basicOpen b ≤ U.1 := hab ▸ X.basicOpen_le a
  refine ⟨X.basicOpen b, hbV, hab ▸ hxa, ?_⟩
  refine _root_.FunctorialResolution.EmbeddedResolution.map_basicOpen_eq_zero_of_app_ι_eq_zero_consolidated121 I.support.compl U.1 U₀.1 U₀.2 s
    (RingHom.mem_ker.mp hs') f hfnzd ?_ b hbV
  intro y hy
  show y ∉ I.support
  refine _root_.FunctorialResolution.EmbeddedResolution.notMem_support_of_mem_basicOpen_consolidated121 I U₀ f ?_ y hy
  rw [hIf]
  exact Ideal.mem_span_singleton_self f


end

theorem strictTransform_bot_of_isBlowupAlongIdealSheaf {X X' : Scheme.{u}} {π : X' ⟶ X}
    {I : X.IdealSheafData} (h : Blowup.IsBlowupAlongIdealSheaf π I) :
    Blowup.strictTransform π I (⊥ : X.IdealSheafData) = (⊥ : X'.IdealSheafData) := by
  have := isIso_subschemeι_comap_bot_consolidated121 π
  rw [Blowup.strictTransform_eq_ker, Blowup.strictTransformImmersion_eq, Blowup.strictTransformOpens_eq]
  exact (ker_preimage_ι_comp_of_isIso _ _).trans h.1.ker_supportCompl_ι_eq_bot

theorem IsPushforwardBlowupSeq.of_isStrictPullback_of_isIso {X' X : Scheme.{u}} (φ : X' ⟶ X)
    [IsIso φ] [IsClosedImmersion φ] {B' : SequenceOfBlowups X'} {B : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq φ B' B) : IsPushforwardBlowupSeq φ B' B := by
  obtain ⟨hlen, σ, hσ0, hsq, hc⟩ := h
  have hiso : ∀ (i : ℕ) (hi : i ≤ B'.length), IsIso (σ i hi) := by
    intro i
    induction i with
    | zero =>
        intro hi
        have hz : σ 0 hi = B'.isoZero.hom ≫ φ ≫ B.isoZero.inv := by
          rw [← Category.assoc, ← hσ0]
          simp
        rw [hz]
        infer_instance
    | succ n ih =>
        intro hi
        have hn : n < B'.length := hi
        have := ih hn.le
        exact (hsq n hn).isIso_fst_of_isIso
  refine ⟨hlen, σ, ?_, hσ0, fun i hi => (hsq i hi).w, ?_, ?_⟩
  · intro i hi
    have := hiso i hi
    infer_instance
  · intro i hi
    have := hiso i hi.le
    rw [hc i hi, imageIdealSheaf_comap]
  · intro i hi
    have hi' : i < B.length := hlen ▸ hi
    have := hiso i hi.le
    have := hiso (i + 1) hi
    rw [Scheme.Hom.ker_eq_bot_of_isIso, Scheme.Hom.ker_eq_bot_of_isIso,
      strictTransform_bot_of_isBlowupAlongIdealSheaf (B.isBlowupAlongIdealSheaf_blowupMorphism i hi')]

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardComposition
section


section
namespace FunctorialResolution.EmbeddedResolution

namespace IsPushforwardBlowupSeq

private theorem ker_comp_eq_ker_subschemeι_comp_consolidated259 {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Scheme.Hom.ker (f ≫ g) = Scheme.Hom.ker ((Scheme.Hom.ker f).subschemeι ≫ g) :=
  (ker_comp_eq_imageIdealSheaf_ker f g).trans (imageIdealSheaf_eq_ker g f.ker)

theorem comp {Y H X : Scheme.{u}} (σ : Y ⟶ H) [IsClosedImmersion σ]
    (ρ : H ⟶ X) [IsClosedImmersion ρ]
    {s : SequenceOfBlowups Y} {t : SequenceOfBlowups H} {u : SequenceOfBlowups X}
    (hNt : ∀ i : ℕ, i ≤ t.length → IsNoetherian (t.schemeAt i))
    (hNu : ∀ i : ℕ, i ≤ u.length → IsNoetherian (u.schemeAt i))
    (hst : IsPushforwardBlowupSeq σ s t) (htu : IsPushforwardBlowupSeq ρ t u) :
    IsPushforwardBlowupSeq (σ ≫ ρ) s u := by
  obtain ⟨hl1, a, haci, ha0, hasq, hac, hak⟩ := hst
  obtain ⟨hl2, b, hbci, hb0, hbsq, hbc, hbk⟩ := htu
  refine ⟨hl1.trans hl2, fun i hi => a i hi ≫ b i (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hit : i ≤ t.length := by omega
    have := haci i hi
    have := hbci i hit
    show IsClosedImmersion (a i hi ≫ b i hit)
    infer_instance
  · show (a 0 (Nat.zero_le _) ≫ b 0 (Nat.zero_le _)) ≫ u.isoZero.hom
      = s.isoZero.hom ≫ (σ ≫ ρ)
    rw [Category.assoc, hb0, ← Category.assoc, ha0, Category.assoc]
  · intro i hi
    have hit : i < t.length := by omega
    show (a (i + 1) hi ≫ b (i + 1) hit) ≫ u.transitionMapSucc i
      = s.transitionMapSucc i ≫ (a i hi.le ≫ b i hit.le)
    rw [Category.assoc, hbsq i hit, ← Category.assoc, hasq i hi, Category.assoc]
  · intro i hi
    have hit : i < t.length := by omega
    have := haci i hi.le
    have := hbci i hit.le
    show u.center i = imageIdealSheaf (a i hi.le ≫ b i hit.le) (s.center i)
    rw [hbc i hit, hac i hi, imageIdealSheaf_comp]
  · intro i hi
    have hit : i < t.length := by omega
    have hiu : i < u.length := by omega
    have := hbci i hit.le
    have := hbci (i + 1) hit
    have := haci i hi.le
    have := haci (i + 1) hi
    have := hNt (i + 1) hit
    have := hNu (i + 1) hiu
    have hker : Scheme.Hom.ker (b (i + 1) hit)
        = Blowup.strictTransform (u.transitionMapSucc i)
            (Scheme.Hom.ker ((t.center i).subschemeι ≫ b i hit.le))
            (Scheme.Hom.ker (b i hit.le)) := by
      rw [hbk i hit, hbc i hit, imageIdealSheaf_eq_ker]
    have key := image_strictTransform_eq_strictTransform_image (b i hit.le) (t.center i)
      (Scheme.Hom.ker (a i hi.le)) (t.transitionMapSucc i) (u.transitionMapSucc i) (b (i + 1) hit)
      (hbsq i hit) hker
    have hL : Scheme.Hom.ker (a (i + 1) hi ≫ b (i + 1) hit)
        = Scheme.Hom.ker ((Blowup.strictTransform (t.transitionMapSucc i) (t.center i)
            (Scheme.Hom.ker (a i hi.le))).subschemeι ≫ b (i + 1) hit) := by
      rw [ker_comp_eq_ker_subschemeι_comp_consolidated259, hak i hi]
    have hD : Scheme.Hom.ker (a i hi.le ≫ b i hit.le)
        = Scheme.Hom.ker ((Scheme.Hom.ker (a i hi.le)).subschemeι ≫ b i hit.le) :=
      ker_comp_eq_ker_subschemeι_comp_consolidated259 _ _
    have hC : u.center i = Scheme.Hom.ker ((t.center i).subschemeι ≫ b i hit.le) := by
      rw [hbc i hit, imageIdealSheaf_eq_ker]
    show Scheme.Hom.ker (a (i + 1) hi ≫ b (i + 1) hit)
      = Blowup.strictTransform (u.transitionMapSucc i) (u.center i)
          (Scheme.Hom.ker (a i hi.le ≫ b i hit.le))
    rw [hL, key, hC, hD]

theorem of_isomorphic_source {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    {s s' : SequenceOfBlowups S} {t : SequenceOfBlowups X}
    (hs : s.Isomorphic s') (h : IsPushforwardBlowupSeq j s t) :
    IsPushforwardBlowupSeq j s' t := by
  obtain ⟨hlen, e, h0, hsqe, hce⟩ := hs
  have hpb : IsStrictPullbackBlowupSeq (𝟙 S) s' s := by
    refine ⟨hlen.symm, fun i hi => (e i (by omega)).inv, ?_, ?_, ?_⟩
    · show (e 0 (Nat.zero_le _)).inv ≫ s.isoZero.hom = s'.isoZero.hom ≫ 𝟙 S
      rw [Category.comp_id, ← h0, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    · intro i hi
      have hi' : i < s.length := by omega
      have hsq : (e (i + 1) hi').inv ≫ s.transitionMapSucc i
          = s'.transitionMapSucc i ≫ (e i hi'.le).inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, hsqe i hi', Category.assoc,
          Iso.hom_inv_id, Category.comp_id]
      show IsPullback ((e (i + 1) hi').inv) (s'.transitionMapSucc i) (s.transitionMapSucc i)
        ((e i hi'.le).inv)
      exact IsPullback.of_horiz_isIso ⟨hsq⟩
    · intro i hi
      have hi' : i < s.length := by omega
      have h1 : imageIdealSheaf (e i hi'.le).hom ((s'.center i).comap (e i hi'.le).hom)
          = imageIdealSheaf (e i hi'.le).hom (s.center i) := by rw [hce i hi']
      rw [imageIdealSheaf_comap] at h1
      have h2 : inv (e i hi'.le).hom = (e i hi'.le).inv :=
        IsIso.inv_eq_of_hom_inv_id (Iso.hom_inv_id (e i hi'.le))
      show s'.center i = (s.center i).comap ((e i hi'.le).inv)
      rw [h1, imageIdealSheaf_eq_comap_inv, h2]
  exact IsPushforwardBlowupSeq.isIso_comp (𝟙 S) j j (Category.id_comp j).symm hpb h

end IsPushforwardBlowupSeq

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MarkedBlowupSequenceBoundary
section


section
namespace FunctorialResolution.EmbeddedResolution

section
variable {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)

private theorem support_comap_subset_preimage_consolidated250 (D : X.IdealSheafData) :
    ((D.comap π).support : Set ↥X₁) ⊆ ⇑π ⁻¹' (D.support : Set ↥X) := by
  simp

theorem support_strictTransform_subset_preimage (Z D : X.IdealSheafData) :
    ((Blowup.strictTransform π Z D).support : Set ↥X₁) ⊆ ⇑π ⁻¹' (D.support : Set ↥X) := by
  refine subset_trans ?_ (support_comap_subset_preimage_consolidated250 π D)
  intro x hx
  have h1 : stalkIdeal (Blowup.strictTransform π Z D) x ≠ ⊤ :=
    (mem_support_iff_stalkIdeal_ne_top (Blowup.strictTransform π Z D) x).mp hx
  have h2 : stalkIdeal (D.comap π) x ≤ stalkIdeal (Blowup.strictTransform π Z D) x :=
    stalkIdeal_mono (comap_le_strictTransform π Z D) x
  have h3 : stalkIdeal (D.comap π) x ≠ ⊤ := by
    intro htop
    rw [htop, top_le_iff] at h2
    exact h1 h2
  exact (mem_support_iff_stalkIdeal_ne_top (D.comap π) x).mpr h3


end

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}

@[simp]
theorem EtaleChart.map_restrict {U : X.Opens} {n : ℕ} (c : EtaleChart p U n)
    {V : X.Opens} (hVU : V ≤ U) :
    (c.restrict hVU).map = X.homOfLE hVU ≫ c.map :=
  c.restrict_map hVU

theorem EtaleChart.coordIdeal_restrict {U : X.Opens} {n : ℕ} (c : EtaleChart p U n)
    {V : X.Opens} (hVU : V ≤ U) (S : Finset (Fin n)) :
    (c.restrict hVU).coordIdeal S = (c.coordIdeal S).comap (X.homOfLE hVU) := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, c.restrict_map hVU]
  simp only [Scheme.IdealSheafData.comap_comp]

private theorem getElemOpt_append_length_add_consolidated250.{v} {α : Type v} (L₂ : List α) :
    ∀ (L₁ : List α) (i : ℕ), (L₁ ++ L₂)[L₁.length + i]? = L₂[i]? := by
  intro L₁
  induction L₁ with
  | nil => intro i; simp
  | cons b L ih =>
      intro i
      have hlen : (b :: L).length + i = (L.length + i) + 1 := by
        simp only [List.length_cons]; omega
      rw [List.cons_append, hlen, List.getElem?_cons_succ]
      exact ih i

private theorem getElem_append_length_add_consolidated250.{v} {α : Type v} (L₁ L₂ : List α) (i : ℕ)
    (hi : i < L₂.length) (hi' : L₁.length + i < (L₁ ++ L₂).length) :
    (L₁ ++ L₂)[L₁.length + i]'hi' = L₂[i]'hi := by
  have h1 := getElemOpt_append_length_add_consolidated250 L₂ L₁ i
  rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at h1
  exact Option.some.inj h1

section
variable {Z : X.IdealSheafData}

theorem HasStrictNormalCrossingsWith.of_append {L₁ L₂ : List X.IdealSheafData}
    (h : HasStrictNormalCrossingsWith p Z (L₁ ++ L₂)) : HasStrictNormalCrossingsWith p Z L₂ := by
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hxU, m, c, a, S, hinj, hnone, hsome, hZ⟩ := h.exists_etaleChart hx
  refine ⟨U, hxU, m, c, fun i => a (L₁.length + i), S, ?_, ?_, ?_, hZ⟩
  · intro i hi j hj t hti htj
    have hi' : L₁.length + i < (L₁ ++ L₂).length := by
      rw [List.length_append]; omega
    have hj' : L₁.length + j < (L₁ ++ L₂).length := by
      rw [List.length_append]; omega
    have heq := hinj _ hi' _ hj' t hti htj
    omega
  · intro i hi hni
    have hi' : L₁.length + i < (L₁ ++ L₂).length := by
      rw [List.length_append]; omega
    have h2 := hnone _ hi' hni
    rwa [getElem_append_length_add_consolidated250 L₁ L₂ i hi hi'] at h2
  · intro i hi t hti
    have hi' : L₁.length + i < (L₁ ++ L₂).length := by
      rw [List.length_append]; omega
    have h2 := hsome _ hi' t hti
    rwa [getElem_append_length_add_consolidated250 L₁ L₂ i hi hi'] at h2

private theorem hasStrictNormalCrossingsWith_cons_of_disjoint_support_consolidated250 {M : List X.IdealSheafData} (h : HasStrictNormalCrossingsWith p Z M) {D : X.IdealSheafData}
    (hD : (D.support : Set ↥X) ∩ (Z.support : Set ↥X) = ∅) :
    HasStrictNormalCrossingsWith p Z (D :: M) := by
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hxU, m, c, a, S, hinj, hnone, hsome, hZU⟩ := h.exists_etaleChart hx
  have hxD : x ∉ (D.support : Set ↥X) := by
    intro hxD
    have hmem : x ∈ (D.support : Set ↥X) ∩ (Z.support : Set ↥X) := ⟨hxD, hx⟩
    rw [hD] at hmem
    exact hmem
  obtain ⟨V, hVU, hxV, hVD⟩ :
      ∃ V : X.Opens, V ≤ U ∧ x ∈ V ∧ ∀ y : ↥X, y ∈ V → y ∉ D.support := by
    refine ⟨⟨(U : Set ↥X) ∩ ((D.support : Set ↥X))ᶜ,
        U.2.inter D.support.2.isOpen_compl⟩, ?_, ⟨hxU, hxD⟩, ?_⟩
    · intro y hy
      exact hy.1
    · intro y hy
      exact hy.2
  refine ⟨V, hxV, m, c.restrict hVU, fun i => if i = 0 then none else a (i - 1), S,
    ?_, ?_, ?_, ?_⟩
  · intro i hi j hj t hti htj
    cases i with
    | zero => simp at hti
    | succ i' =>
      cases j with
      | zero => simp at htj
      | succ j' =>
        have hi' : i' < M.length := by
          simp only [List.length_cons] at hi
          omega
        have hj' : j' < M.length := by
          simp only [List.length_cons] at hj
          omega
        have hti' : a i' = some t := by simpa using hti
        have htj' : a j' = some t := by simpa using htj
        have heq := hinj i' hi' j' hj' t hti' htj'
        omega
  · intro i hi hni
    cases i with
    | zero =>
      refine (restrictIdeal_eq_top_iff_forall_notMem_support _ V).mpr ?_
      intro y hy
      exact hVD y hy
    | succ i' =>
      have hi' : i' < M.length := by
        simp only [List.length_cons] at hi
        omega
      have ha : a i' = none := by simpa using hni
      have key : restrictIdeal (M[i']'hi') U = ⊤ := hnone i' hi' ha
      show restrictIdeal (M[i']'hi') V = ⊤
      rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal _ hVU, key]
      simp
  · intro i hi t hti
    cases i with
    | zero => simp at hti
    | succ i' =>
      have hi' : i' < M.length := by
        simp only [List.length_cons] at hi
        omega
      have ha : a i' = some t := by simpa using hti
      have key : restrictIdeal (M[i']'hi') U = c.coordIdeal {t} := hsome i' hi' t ha
      show restrictIdeal (M[i']'hi') V = (c.restrict hVU).coordIdeal {t}
      rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal _ hVU, key, EtaleChart.coordIdeal_restrict]
  · rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal _ hVU, hZU, EtaleChart.coordIdeal_restrict]

theorem HasStrictNormalCrossingsWith.append_of_support_disjoint {N : List X.IdealSheafData}
    (h : HasStrictNormalCrossingsWith p Z N) {L : List X.IdealSheafData}
    (hL : ∀ D ∈ L, (D.support : Set ↥X) ∩ (Z.support : Set ↥X) = ∅) :
    HasStrictNormalCrossingsWith p Z (L ++ N) := by
  revert hL
  induction L with
  | nil =>
      intro _
      exact h
  | cons D L ih =>
      intro hL
      exact hasStrictNormalCrossingsWith_cons_of_disjoint_support_consolidated250
        (ih fun E hE => hL E (List.mem_cons.mpr (Or.inr hE)))
        (hL D (List.mem_cons.mpr (Or.inl rfl)))


end

end

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

section
variable (u : MarkedBlowupSequenceData p I m E)

theorem boundary_length (t : ℕ) (ht : t ≤ u.length) :
    (u.boundary t).length = E.length + t := by
  revert ht
  induction t with
  | zero =>
      intro _
      simp [u.boundary_zero]
  | succ j ih =>
      intro ht
      have hj : j < u.length := ht
      rw [u.boundary_succ j hj, List.length_append, List.length_map, ih (le_of_lt hj)]
      simp only [List.length_cons, List.length_nil]
      omega

theorem index_lt_boundary_length {t : ℕ} (ht : t ≤ u.length)
    {i : ℕ} (hi : i < E.length) : i < (u.boundary t).length := by
  rw [u.boundary_length t ht]
  omega

theorem boundary_succ_drop {t : ℕ} (ht : t < u.length)
    (n : ℕ) (hn : n ≤ (u.boundary t).length) :
    (u.boundary (t + 1)).drop n =
      ((u.boundary t).drop n).map (Blowup.strictTransform (u.map t) (u.center t)) ++
        [Blowup.exceptionalIdeal (u.map t) (u.center t)] := by
  have hlen : n ≤ ((u.boundary t).map (Blowup.strictTransform (u.map t) (u.center t))).length := by
    rw [List.length_map]
    exact hn
  rw [u.boundary_succ t ht, List.drop_append_of_le_length hlen, ← List.map_drop]

theorem preimage_iUnion_support_boundary_subset (hN : ∀ i ≤ u.length, IsLocallyNoetherian (u.obj i)) {t : ℕ} (ht : t < u.length) :
    ⇑(u.map t) ⁻¹' (⋃ D ∈ u.boundary t, (D.support : Set ↥(u.obj t))) ⊆
      ⋃ D ∈ u.boundary (t + 1), (D.support : Set ↥(u.obj (t + 1))) := by
  have hlocNoeth : IsLocallyNoetherian (u.obj (t + 1)) := hN (t + 1) ht
  intro x hx
  obtain ⟨D, hD, hxD0⟩ := Set.mem_iUnion₂.mp (Set.mem_preimage.mp hx)
  have hxD : ⇑(u.map t) x ∈ ((D.support : Set ↥(u.obj t))) := hxD0
  by_cases hc : ⇑(u.map t) x ∈ ((u.center t).support : Set ↥(u.obj t))
  · have hmem : Blowup.exceptionalIdeal (u.map t) (u.center t) ∈ u.boundary (t + 1) := by
      rw [u.boundary_succ t ht, List.mem_append]
      exact Or.inr (List.mem_singleton_self _)
    have h2 : x ∈ ((Blowup.exceptionalIdeal (u.map t) (u.center t)).support : Set ↥(u.obj (t + 1))) := by
      rw [Blowup.exceptionalIdeal_eq_comap]
      have hEq : ((((u.center t).comap (u.map t)).support) : Set ↥(u.obj (t + 1)))
          = ⇑(u.map t) ⁻¹' ((u.center t).support : Set ↥(u.obj t)) := by
        simp
      rw [hEq]
      exact hc
    exact Set.mem_iUnion₂.mpr ⟨_, hmem, h2⟩
  · have hmem : Blowup.strictTransform (u.map t) (u.center t) D ∈ u.boundary (t + 1) := by
      rw [u.boundary_succ t ht, List.mem_append]
      refine Or.inl ?_
      rw [List.mem_map]
      exact ⟨D, hD, rfl⟩
    have h2 : x ∈ ((Blowup.strictTransform (u.map t) (u.center t) D).support : Set ↥(u.obj (t + 1))) := by
      rw [support_strictTransform_eq_closure_preimage (u.map t) (u.center t) D]
      exact subset_closure (Set.mem_preimage.mpr (Set.mem_sdiff_of_mem hxD hc))
    exact Set.mem_iUnion₂.mpr ⟨_, hmem, h2⟩


end

private theorem eq_of_exceptionalIdeal_pow_mul_eq_mul_consolidated250 {Y Y' : Scheme.{u}} {π : Y' ⟶ Y}
    {Z : Y.IdealSheafData} (h : Blowup.IsBlowupAlongIdealSheaf π Z) (n : ℕ) {A B : Y'.IdealSheafData}
    (e : Blowup.exceptionalIdeal π Z ^ n * A = Blowup.exceptionalIdeal π Z ^ n * B) : A = B := by
  rw [Blowup.exceptionalIdeal_eq_comap] at e
  exact eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul h.1 n e

section
variable (u : MarkedBlowupSequenceData p I m E)

private theorem projectionToBase_eq_projectionToBase_toBlowupSequenceData_consolidated250 (i : ℕ) :
    u.proj i = u.toBlowupSequenceData.projectionToBase i := by
  induction i with
  | zero => rw [u.proj_zero, BlowupSequenceData.projectionToBase_zero]
  | succ j ih => rw [u.proj_succ j, BlowupSequenceData.projectionToBase_succ, ih]

private theorem toBlowupSequenceData_boundary_eq_boundary_consolidated250 :
    ∀ i, i ≤ u.length → u.toBlowupSequenceData.boundaryFrom E i = u.boundary i := by
  intro i
  induction i with
  | zero =>
      intro _
      rw [BlowupSequenceData.boundary_zero, u.boundary_zero]
  | succ j ih =>
      intro hj
      have hjlt : j < u.length := hj
      rw [BlowupSequenceData.boundary_succ, ih (le_of_lt hjlt), u.boundary_succ j hjlt]

private theorem toBlowupSequenceData_controlledTransform_eq_ideal_consolidated250 :
    ∀ i, i ≤ u.length → u.toBlowupSequenceData.controlledTransform I m i = u.ideal i := by
  intro i
  induction i with
  | zero =>
      intro _
      rw [BlowupSequenceData.controlledTransform_zero, u.ideal_zero]
  | succ j ih =>
      intro hj
      have hjlt : j < u.length := hj
      have hIH : u.toBlowupSequenceData.controlledTransform I m j = u.ideal j := ih (le_of_lt hjlt)
      have hex : ∃ B : (u.obj (j + 1)).IdealSheafData,
          Blowup.exceptionalIdeal (u.map j) (u.center j) ^ m * B =
            (u.toBlowupSequenceData.controlledTransform I m j).comap (u.map j) := by
        refine ⟨u.ideal (j + 1), ?_⟩
        rw [hIH]
        exact u.ideal_succ j hjlt
      have key := u.toBlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ I m j hex
      refine eq_of_exceptionalIdeal_pow_mul_eq_mul_consolidated250 (u.isBlowup j hjlt) m ?_
      rw [key, hIH]
      exact (u.ideal_succ j hjlt).symm

theorem isMarked : u.toBlowupSequenceData.IsMarked p I m E := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    refine ⟨u.ideal (i + 1), ?_⟩
    rw [toBlowupSequenceData_controlledTransform_eq_ideal_consolidated250 u i (le_of_lt hi)]
    exact u.ideal_succ i hi
  · intro i hi
    rw [toBlowupSequenceData_controlledTransform_eq_ideal_consolidated250 u i (le_of_lt hi)]
    exact u.center_order i hi
  · intro i hi
    have h := u.center_smooth i hi
    rwa [projectionToBase_eq_projectionToBase_toBlowupSequenceData_consolidated250 u i] at h
  · intro i hi
    have h := u.center_snc i hi
    rwa [projectionToBase_eq_projectionToBase_toBlowupSequenceData_consolidated250 u i, ← toBlowupSequenceData_boundary_eq_boundary_consolidated250 u i (le_of_lt hi)] at h


end

private theorem getElemOpt_map_append_consolidated250.{v, w} {α : Type v} {β : Type w} (f : α → β) (T : List β) :
    ∀ (L : List α) (i : ℕ), i < L.length → (List.map f L ++ T)[i]? = Option.map f (L[i]?) := by
  intro L
  induction L with
  | nil =>
      intro i hi
      simp at hi
  | cons a L ih =>
      intro i hi
      cases i with
      | zero => simp
      | succ j =>
          have hj : j < L.length := by
            simp only [List.length_cons] at hi
            omega
          simp only [List.map_cons, List.cons_append, List.getElem?_cons_succ]
          exact ih j hj

private theorem getElem_map_append_consolidated250.{v, w} {α : Type v} {β : Type w} (f : α → β)
    (L : List α) (T : List β) (i : ℕ) (hi : i < L.length)
    (hi' : i < (List.map f L ++ T).length) :
    (List.map f L ++ T)[i]'hi' = f (L[i]'hi) := by
  have h := getElemOpt_map_append_consolidated250 f T L i hi
  rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at h
  simpa using h

theorem orderAtLeastLocus_disjoint_boundary_of_le (u : MarkedBlowupSequenceData p I m E)
    (hdesc : ∀ t < u.length,
      orderAtLeastLocus (u.ideal (t + 1)) m ⊆ ⇑(u.map t) ⁻¹' orderAtLeastLocus (u.ideal t) m)
    {i : ℕ} (hi : i < E.length) {r : ℕ} (hr : r ≤ u.length)
    (hsep : orderAtLeastLocus (u.ideal r) m ∩
        ((((u.boundary r)[i]'(u.index_lt_boundary_length hr hi)).support :
          Set ↥(u.obj r))) = ∅) :
    ∀ t, r ≤ t → ∀ ht : t ≤ u.length,
      orderAtLeastLocus (u.ideal t) m ∩
        ((((u.boundary t)[i]'(u.index_lt_boundary_length ht hi)).support :
          Set ↥(u.obj t))) = ∅ := by
  intro t hrt
  induction t, hrt using Nat.le_induction with
  | base =>
      intro ht
      exact hsep
  | succ t hrt ih =>
      intro ht
      have htlt : t < u.length := ht
      have ihy := ih (le_of_lt htlt)
      have hxl : i < (u.boundary t).length :=
        u.index_lt_boundary_length (le_of_lt htlt) hi
      have hlen2 : i < (List.map (Blowup.strictTransform (u.map t) (u.center t)) (u.boundary t)
          ++ [Blowup.exceptionalIdeal (u.map t) (u.center t)]).length := by
        rw [List.length_append, List.length_map]
        omega
      have hbeq : (u.boundary (t + 1))[i]'(u.index_lt_boundary_length ht hi)
          = Blowup.strictTransform (u.map t) (u.center t) ((u.boundary t)[i]'hxl) := by
        refine Eq.trans (List.getElem_of_eq (u.boundary_succ t htlt)
          (u.index_lt_boundary_length ht hi)) ?_
        exact getElem_map_append_consolidated250 (Blowup.strictTransform (u.map t) (u.center t))
          (u.boundary t) [Blowup.exceptionalIdeal (u.map t) (u.center t)] i hxl hlen2
      refine Set.eq_empty_of_subset_empty ?_
      rintro x ⟨hx1, hx2⟩
      rw [hbeq] at hx2
      have hx1' : ⇑(u.map t) x ∈ orderAtLeastLocus (u.ideal t) m :=
        Set.mem_preimage.mp (hdesc t htlt hx1)
      have hx2' : ⇑(u.map t) x ∈ ((((u.boundary t)[i]'hxl).support : Set ↥(u.obj t))) :=
        Set.mem_preimage.mp
          (support_strictTransform_subset_preimage (u.map t) (u.center t)
            ((u.boundary t)[i]'hxl) hx2)
      have hfalse : (⇑(u.map t) x) ∈ (∅ : Set ↥(u.obj t)) := by
        rw [← ihy]
        exact Set.mem_inter hx1' hx2'
      simp at hfalse

end MarkedBlowupSequenceData

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedSchemeWithCenter
section


section
namespace FunctorialResolution.EmbeddedResolution

structure MarkedSchemeWithCenter (k : Type u) [Field k] where
  ambient : Scheme.{u}
  ideal : ambient.IdealSheafData
  boundary : List ambient.IdealSheafData
  structMap : ambient ⟶ Spec (CommRingCat.of k)
  center : ambient.IdealSheafData

private theorem comap_inv_comap_hom_consolidated226 {X Y : Scheme.{u}} (e : X ≅ Y) (I : Y.IdealSheafData) :
    (I.comap e.hom).comap e.inv = I := by
  rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id]
  simp

namespace MarkedSchemeWithCenter

variable {k : Type u} [Field k]

def transport (D : MarkedSchemeWithCenter k) {A : Scheme.{u}} (e : A ≅ D.ambient) : MarkedSchemeWithCenter k where
  ambient := A
  ideal := D.ideal.comap e.hom
  boundary := D.boundary.map (fun J => J.comap e.hom)
  structMap := e.hom ≫ D.structMap
  center := D.center.comap e.hom

@[simp]
theorem transport_ideal (D : MarkedSchemeWithCenter k) {A : Scheme.{u}} (e : A ≅ D.ambient) :
    (D.transport e).ideal = D.ideal.comap e.hom := rfl

@[simp]
theorem transport_projectionToBase (D : MarkedSchemeWithCenter k) {A : Scheme.{u}} (e : A ≅ D.ambient) :
    (D.transport e).structMap = e.hom ≫ D.structMap := rfl

@[simp]
theorem transport_center (D : MarkedSchemeWithCenter k) {A : Scheme.{u}} (e : A ≅ D.ambient) :
    (D.transport e).center = D.center.comap e.hom := rfl

private theorem mk_congr_consolidated226 {K : Type u} [Field K] (A : Scheme.{u})
    (I I' : A.IdealSheafData) (B B' : List A.IdealSheafData)
    (f f' : A ⟶ Spec (CommRingCat.of K)) (C C' : A.IdealSheafData)
    (h1 : I = I') (h2 : B = B') (h3 : f = f') (h4 : C = C') :
    (MarkedSchemeWithCenter.mk A I B f C : MarkedSchemeWithCenter K) = MarkedSchemeWithCenter.mk A I' B' f' C' := by
  subst h1 h2 h3 h4
  rfl

theorem transport_refl (D : MarkedSchemeWithCenter k) : D.transport (Iso.refl D.ambient) = D := by
  obtain ⟨A, I, B, f, C⟩ := D
  have h1 : I.comap (𝟙 A) = I := by simp
  have h2 : B.map (fun J => J.comap (𝟙 A)) = B := by simp
  have h3 : 𝟙 A ≫ f = f := Category.id_comp f
  have h4 : C.comap (𝟙 A) = C := by simp
  exact mk_congr_consolidated226 _ _ _ _ _ _ _ _ _ h1 h2 h3 h4

end MarkedSchemeWithCenter

def IsInvariantUnderIso {k : Type u} [Field k] (P : MarkedSchemeWithCenter.{u} k → Prop) : Prop :=
  ∀ (D : MarkedSchemeWithCenter.{u} k) (A : Scheme.{u}) (e : A ≅ D.ambient), P D → P (D.transport e)

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def dataAt (s : MarkedBlowupSequenceData p I m E) (i : ℕ) : MarkedSchemeWithCenter.{u} k where
  ambient := s.toBlowupSequenceData.obj i
  ideal := s.ideal i
  boundary := s.boundary i
  structMap := s.proj i ≫ p
  center := s.toBlowupSequenceData.center i

@[simp]
theorem dataAt_ideal (s : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    (s.dataAt i).ideal = s.ideal i := rfl

@[simp]
theorem dataAt_boundary (s : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    (s.dataAt i).boundary = s.boundary i := rfl

@[simp]
theorem dataAt_structMap (s : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    (s.dataAt i).structMap = s.proj i ≫ p := rfl

@[simp]
theorem dataAt_center (s : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    (s.dataAt i).center = s.toBlowupSequenceData.center i := rfl

private theorem transport_dataAt_congr_consolidated226 {K : Type u} [Field K] {Y : Scheme.{u}}
    {q : Y ⟶ Spec (CommRingCat.of K)} {J : Y.IdealSheafData} {n : ℕ}
    {F : List Y.IdealSheafData} (d : MarkedBlowupSequenceData q J n F) {a b : ℕ} (hab : a = b)
    {Z : Scheme.{u}} (h1 : Z = d.toBlowupSequenceData.obj a) (h2 : Z = d.toBlowupSequenceData.obj b) :
    (d.dataAt a).transport (eqToIso h1) = (d.dataAt b).transport (eqToIso h2) := by
  subst hab
  rfl

variable (s : MarkedBlowupSequenceData p I m E)
  (t : MarkedBlowupSequenceData (s.proj s.toBlowupSequenceData.length ≫ p) (s.ideal s.toBlowupSequenceData.length) m
    (s.boundary s.toBlowupSequenceData.length))

section
variable (hinv : ComapIsoInvariance.{u})

theorem append_dataAt_of_lt_length {i : ℕ} (h : i < s.toBlowupSequenceData.length) :
    (s.append t hinv).dataAt i =
      (s.dataAt i).transport (eqToIso (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h))) := by
  have hle : i ≤ s.toBlowupSequenceData.length := le_of_lt h
  have h1 : s.appendIdeal t i =
      (s.ideal i).comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t hle)) :=
    appendIdeal_of_le_length s t hle
  have h2 : s.appendBoundary t i =
      (s.boundary i).map (fun J => J.comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t hle))) :=
    appendBoundary_of_le_length s t hle
  have h3 : s.appendProjectionToBase t i ≫ p =
      eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t hle) ≫ (s.proj i ≫ p) := by
    rw [appendProjectionToBase_of_le_length s t hle, Category.assoc]
  have h4 : (s.appendToBlowupSequenceData t).center i =
      (s.toBlowupSequenceData.center i).comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t hle)) :=
    appendToBlowupSequenceData_center_of_lt_length s t h
  exact MarkedSchemeWithCenter.mk_congr_consolidated226 _ _ _ _ _ _ _ _ _ h1 h2 h3 h4

theorem append_dataAt_length :
    (s.append t hinv).dataAt s.toBlowupSequenceData.length =
      ((t.dataAt 0).transport t.toBlowupSequenceData.isoZero.symm).transport
        (eqToIso (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))) := by
  have h1 : s.appendIdeal t s.toBlowupSequenceData.length =
      ((t.ideal 0).comap t.toBlowupSequenceData.isoZero.inv).comap
        (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))) := by
    rw [appendIdeal_of_le_length s t (le_refl s.toBlowupSequenceData.length), t.ideal_zero, comap_inv_comap_hom_consolidated226]
  have h2 : s.appendBoundary t s.toBlowupSequenceData.length =
      ((t.boundary 0).map (fun J => J.comap t.toBlowupSequenceData.isoZero.inv)).map
        (fun J => J.comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length)))) := by
    rw [appendBoundary_of_le_length s t (le_refl s.toBlowupSequenceData.length), t.boundary_zero]
    simp only [List.map_map, Function.comp_def, comap_inv_comap_hom_consolidated226]
  have h3 : s.appendProjectionToBase t s.toBlowupSequenceData.length ≫ p =
      eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length)) ≫
        (t.toBlowupSequenceData.isoZero.inv ≫
          (t.proj 0 ≫ (s.proj s.toBlowupSequenceData.length ≫ p))) := by
    rw [appendProjectionToBase_of_le_length s t (le_refl s.toBlowupSequenceData.length), t.proj_zero]
    simp
  have h4 : (s.appendToBlowupSequenceData t).center s.toBlowupSequenceData.length =
      ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv).comap
        (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))) :=
    appendToBlowupSequenceData_center_length s t
  exact MarkedSchemeWithCenter.mk_congr_consolidated226 _ _ _ _ _ _ _ _ _ h1 h2 h3 h4

theorem append_dataAt_of_length_lt {i : ℕ} (h : s.toBlowupSequenceData.length < i) :
    (s.append t hinv).dataAt i =
      (t.dataAt (i - s.toBlowupSequenceData.length)).transport
        (eqToIso (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)) := by
  have h1 : s.appendIdeal t i =
      (t.ideal (i - s.toBlowupSequenceData.length)).comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)) :=
    appendIdeal_of_length_lt s t h
  have h2 : s.appendBoundary t i =
      (t.boundary (i - s.toBlowupSequenceData.length)).map
        (fun J => J.comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h))) :=
    appendBoundary_of_length_lt s t h
  have h3 : s.appendProjectionToBase t i ≫ p =
      eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h) ≫
        (t.proj (i - s.toBlowupSequenceData.length) ≫ (s.proj s.toBlowupSequenceData.length ≫ p)) := by
    rw [appendProjectionToBase_of_length_lt s t h]
    simp only [Category.assoc]
  have h4 : (s.appendToBlowupSequenceData t).center i =
      (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length)).comap
        (eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)) :=
    appendToBlowupSequenceData_center_of_length_lt s t h
  exact MarkedSchemeWithCenter.mk_congr_consolidated226 _ _ _ _ _ _ _ _ _ h1 h2 h3 h4

theorem append_dataAt_last (h : 0 < t.toBlowupSequenceData.length) :
    (s.append t hinv).dataAt ((s.append t hinv).toBlowupSequenceData.length) =
      (t.dataAt t.toBlowupSequenceData.length).transport
        (eqToIso (appendToBlowupSequenceData_schemeAt_length_add_length s t h)) := by
  have hgt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := by omega
  have key : (s.append t hinv).dataAt (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length) =
      (t.dataAt t.toBlowupSequenceData.length).transport
        (eqToIso (appendToBlowupSequenceData_schemeAt_length_add_length s t h)) := by
    rw [append_dataAt_of_length_lt s t hinv hgt]
    exact transport_dataAt_congr_consolidated226 t (by omega) _ _
  exact key

theorem append_dataAt_of_forall (P : MarkedSchemeWithCenter.{u} k → Prop)
    (hP : IsInvariantUnderIso P)
    (hs : ∀ i < s.toBlowupSequenceData.length, P (s.dataAt i))
    (ht : ∀ i < t.toBlowupSequenceData.length, P (t.dataAt i))
    (i : ℕ) (hi : i < (s.append t hinv).toBlowupSequenceData.length) :
    P ((s.append t hinv).dataAt i) := by
  have hN : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := hi
  rcases lt_trichotomy i s.toBlowupSequenceData.length with hlt | heq | hgt
  · rw [append_dataAt_of_lt_length s t hinv hlt]
    exact hP (s.dataAt i) _ _ (hs i hlt)
  · subst heq
    rw [append_dataAt_length s t hinv]
    exact hP _ _ _ (hP (t.dataAt 0) _ _ (ht 0 (by omega)))
  · rw [append_dataAt_of_length_lt s t hinv hgt]
    exact hP (t.dataAt (i - s.toBlowupSequenceData.length)) _ _
      (ht (i - s.toBlowupSequenceData.length) (by omega))


end

end MarkedBlowupSequenceData

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
section


open scoped Classical

section
namespace FunctorialResolution.EmbeddedResolution

section

variable {X : Scheme.{u}}

def monomialSplitting (E : List X.IdealSheafData) (I : X.IdealSheafData) :
    X.IdealSheafData × X.IdealSheafData :=
  if h : ∃ q : X.IdealSheafData × X.IdealSheafData, IsMonomialSplitting E I q.1 q.2 then
    h.choose
  else (⊤, I)

def monomialPart (E : List X.IdealSheafData) (I : X.IdealSheafData) : X.IdealSheafData :=
  (monomialSplitting E I).1

def nonMonomialPart (E : List X.IdealSheafData) (I : X.IdealSheafData) : X.IdealSheafData :=
  (monomialSplitting E I).2

theorem isMonomialSplitting_monomialPart_nonMonomialPart (E : List X.IdealSheafData) (I : X.IdealSheafData)
    (h : ∃ q : X.IdealSheafData × X.IdealSheafData, IsMonomialSplitting E I q.1 q.2) :
    IsMonomialSplitting E I (monomialPart E I) (nonMonomialPart E I) := by
  unfold monomialPart nonMonomialPart monomialSplitting
  rw [dif_pos h]
  exact h.choose_spec

end

section

variable {X : Scheme.{u}}

def maxOrder (N : X.IdealSheafData) : ℕ :=
  sSup {n : ℕ | ∃ x : ↥X, (n : ℕ∞) ≤ orderAt N x}

def maxOrderOn (N : X.IdealSheafData) (S : Set ↥X) : ℕ :=
  sSup {n : ℕ | ∃ x ∈ S, (n : ℕ∞) ≤ orderAt N x}

end

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def markedDataOfSeq (s : MarkedBlowupSequenceData p I m E) (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (t : MarkedSequenceOfBlowups (s.proj s.length ≫ p) J μ (s.boundary s.length)) :
    Option (MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length)) :=
  if h : (BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m
      (s.boundary s.length) then
    some ((BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).toMarkedBlowupSequenceData (s.proj s.length ≫ p)
      (s.ideal s.length) m (s.boundary s.length) h)
  else
    none

def appendIfMarked (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (t : MarkedSequenceOfBlowups (s.proj s.length ≫ p) J μ (s.boundary s.length)) :
    MarkedBlowupSequenceData p I m E :=
  match markedDataOfSeq s J μ t with
  | some d => s.append d hinv
  | none => s

end

section

def tripleAtLength (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ) : MarkedIdealWithBoundary.{u} where
  base := T.base
  instField := T.instField
  scheme := s.obj s.length
  structMap := s.proj s.length ≫ T.structMap
  ideal := J
  mult := μ
  boundary := s.boundary s.length

def appendRecursivePrincipalization (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ) :
    MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
  if h : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc then
    appendIfMarked hinv s J μ (rc (tripleAtLength T s J μ) h)
  else s

def nonMonomialOrderReductionIter (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) :
    ℕ → MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary
  | 0 => emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary
  | n + 1 =>
    if T.mult ≤
          maxOrder (nonMonomialPart ((nonMonomialOrderReductionIter hinv T rc n).boundary
            (nonMonomialOrderReductionIter hinv T rc n).length)
            ((nonMonomialOrderReductionIter hinv T rc n).ideal (nonMonomialOrderReductionIter hinv T rc n).length)) ∧
        (orderAtLeastLocus
            (nonMonomialPart ((nonMonomialOrderReductionIter hinv T rc n).boundary
              (nonMonomialOrderReductionIter hinv T rc n).length)
              ((nonMonomialOrderReductionIter hinv T rc n).ideal (nonMonomialOrderReductionIter hinv T rc n).length))
            (maxOrder (nonMonomialPart ((nonMonomialOrderReductionIter hinv T rc n).boundary
              (nonMonomialOrderReductionIter hinv T rc n).length)
              ((nonMonomialOrderReductionIter hinv T rc n).ideal
                (nonMonomialOrderReductionIter hinv T rc n).length)))).Nonempty then
      appendRecursivePrincipalization hinv T rc (nonMonomialOrderReductionIter hinv T rc n)
        (nonMonomialPart ((nonMonomialOrderReductionIter hinv T rc n).boundary
          (nonMonomialOrderReductionIter hinv T rc n).length)
          ((nonMonomialOrderReductionIter hinv T rc n).ideal (nonMonomialOrderReductionIter hinv T rc n).length))
        (maxOrder (nonMonomialPart ((nonMonomialOrderReductionIter hinv T rc n).boundary
          (nonMonomialOrderReductionIter hinv T rc n).length)
          ((nonMonomialOrderReductionIter hinv T rc n).ideal (nonMonomialOrderReductionIter hinv T rc n).length)))
    else nonMonomialOrderReductionIter hinv T rc n

def nonMonomialOrderReduction (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) :
    MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
  nonMonomialOrderReductionIter hinv T rc (maxOrder (nonMonomialPart T.boundary T.ideal) + 1)

def companionIdealReductionIter (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s₀ : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    ℕ → MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary
  | 0 => s₀
  | n + 1 =>
    if 1 ≤
        maxOrderOn
          (nonMonomialPart ((companionIdealReductionIter hinv T rc s₀ n).boundary
            (companionIdealReductionIter hinv T rc s₀ n).length)
            ((companionIdealReductionIter hinv T rc s₀ n).ideal (companionIdealReductionIter hinv T rc s₀ n).length))
          (orderAtLeastLocus ((companionIdealReductionIter hinv T rc s₀ n).ideal
            (companionIdealReductionIter hinv T rc s₀ n).length) T.mult) then
      appendRecursivePrincipalization hinv T rc (companionIdealReductionIter hinv T rc s₀ n)
        (nonMonomialPart ((companionIdealReductionIter hinv T rc s₀ n).boundary
            (companionIdealReductionIter hinv T rc s₀ n).length)
            ((companionIdealReductionIter hinv T rc s₀ n).ideal (companionIdealReductionIter hinv T rc s₀ n).length) ^ T.mult ⊔
          (companionIdealReductionIter hinv T rc s₀ n).ideal (companionIdealReductionIter hinv T rc s₀ n).length ^
            maxOrderOn
              (nonMonomialPart ((companionIdealReductionIter hinv T rc s₀ n).boundary
                (companionIdealReductionIter hinv T rc s₀ n).length)
                ((companionIdealReductionIter hinv T rc s₀ n).ideal (companionIdealReductionIter hinv T rc s₀ n).length))
              (orderAtLeastLocus ((companionIdealReductionIter hinv T rc s₀ n).ideal
                (companionIdealReductionIter hinv T rc s₀ n).length) T.mult))
        (T.mult *
          maxOrderOn
            (nonMonomialPart ((companionIdealReductionIter hinv T rc s₀ n).boundary
              (companionIdealReductionIter hinv T rc s₀ n).length)
              ((companionIdealReductionIter hinv T rc s₀ n).ideal (companionIdealReductionIter hinv T rc s₀ n).length))
            (orderAtLeastLocus ((companionIdealReductionIter hinv T rc s₀ n).ideal
              (companionIdealReductionIter hinv T rc s₀ n).length) T.mult))
    else companionIdealReductionIter hinv T rc s₀ n

def companionIdealReduction (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) :
    MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
  companionIdealReductionIter hinv T rc (nonMonomialOrderReduction hinv T rc)
    (maxOrderOn
      (nonMonomialPart ((nonMonomialOrderReduction hinv T rc).boundary (nonMonomialOrderReduction hinv T rc).length)
        ((nonMonomialOrderReduction hinv T rc).ideal (nonMonomialOrderReduction hinv T rc).length))
      (orderAtLeastLocus ((nonMonomialOrderReduction hinv T rc).ideal (nonMonomialOrderReduction hinv T rc).length) T.mult) + 1)

def orderReductionData (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) :
    MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
  (companionIdealReduction hinv T rc).append
    (MarkedBlowupSequenceData.ofMarkedSequence
      (monomialPrincipalization hinv
        (tripleAtLength T (companionIdealReduction hinv T rc)
          ((companionIdealReduction hinv T rc).ideal (companionIdealReduction hinv T rc).length) T.mult)))
    hinv

def orderReductionSeq (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) : T.SequenceOfBlowups :=
  if orderAtLeastLocus T.ideal T.mult = ∅ then
    emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
  else
    (orderReductionData hinv T rc).toMarkedSequenceOfBlowups

end

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealGeometry
section

open TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

private theorem le_of_ideal_le_consolidated219 {X : Scheme.{u}} {I J : X.IdealSheafData}
    (h : ∀ V : X.affineOpens, I.ideal V ≤ J.ideal V) : I ≤ J := h

section
variable {A B : CommRingCat.{u}} (e : A ≅ B)

private theorem injective_hom_of_iso_consolidated219 :
    Function.Injective e.hom.hom :=
  e.commRingCatIsoToRingEquiv.injective

private theorem surjective_hom_of_iso_consolidated219 :
    Function.Surjective e.hom.hom :=
  e.commRingCatIsoToRingEquiv.surjective

private theorem ker_hom_of_iso_le_consolidated219 (I : Ideal A) :
    RingHom.ker e.hom.hom ≤ I := by
  intro x hx
  have hx0 : e.hom.hom x = e.hom.hom 0 := by
    simpa [RingHom.mem_ker] using hx
  have hz : x = 0 := injective_hom_of_iso_consolidated219 e hx0
  simp [hz]


end

private theorem isReduced_quotient_of_radical_eq_consolidated219 {R : Type u} [CommRing R] (I : Ideal R)
    (h : I.radical = I) : _root_.IsReduced (R ⧸ I) :=
  (Ideal.isRadical_iff_quotient_reduced I).mp (Ideal.radical_eq_iff.mp h)

private theorem isReduced_of_isLocalization_consolidated219 {R S : Type u} [CommRing R] [CommRing S]
    (alg : Algebra R S) (M : Submonoid R) (hloc : @IsLocalization R _ M S _ alg)
    (hred : _root_.IsReduced R) : _root_.IsReduced S :=
  @isReduced_localizationPreserves R _ M S _ alg hloc hred

private theorem radical_primeSpectrum_vanishingIdeal_eq_consolidated219 {R : Type u} [CommRing R]
    (t : Set (PrimeSpectrum R)) :
    (PrimeSpectrum.vanishingIdeal t).radical = PrimeSpectrum.vanishingIdeal t :=
  (PrimeSpectrum.isRadical_vanishingIdeal t).radical

section
variable {X : Scheme.{u}}

private theorem isReduced_subscheme_of_radical_eq_consolidated219 (J : X.IdealSheafData)
    (hJ : ∀ U : X.affineOpens, (J.ideal U).radical = J.ideal U) :
    IsReduced J.subscheme := by
  have hst : ∀ y : ↥(J.subscheme), _root_.IsReduced ↑((J.subscheme).presheaf.stalk y) := by
    intro y
    obtain ⟨U, hyU, hU⟩ :=
      AlgebraicGeometry.Scheme.exists_isAffineOpen_mem (J.subschemeι.base y)
    have hV : IsAffineOpen (J.subschemeι ⁻¹ᵁ U) := hU.preimage J.subschemeι
    have hy : y ∈ J.subschemeι ⁻¹ᵁ U := hyU
    have hredq : _root_.IsReduced (↑Γ(X, U) ⧸ J.ideal ⟨U, hU⟩) :=
      isReduced_quotient_of_radical_eq_consolidated219 _ (hJ ⟨U, hU⟩)
    have hsec : _root_.IsReduced ↑Γ(J.subscheme, J.subschemeι ⁻¹ᵁ U) := by
      refine ⟨fun z hz => ?_⟩
      obtain ⟨n, hn⟩ := hz
      apply injective_hom_of_iso_consolidated219 (J.subschemeObjIso ⟨U, hU⟩)
      rw [map_zero]
      refine hredq.eq_zero _ ⟨n, ?_⟩
      rw [← map_pow, hn, map_zero]
    show _root_.IsReduced
      ↑((J.subscheme).presheaf.stalk ((⟨y, hy⟩ : ↥(J.subschemeι ⁻¹ᵁ U)) : ↥(J.subscheme)))
    exact isReduced_of_isLocalization_consolidated219 _ (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
      (hV.isLocalization_stalk ⟨y, hy⟩) hsec
  have := hst
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _

private theorem isReduced_vanishingIdeal_subscheme_consolidated219 (Z : Closeds ↥X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  refine isReduced_subscheme_of_radical_eq_consolidated219 _ (fun U => ?_)
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  exact radical_primeSpectrum_vanishingIdeal_eq_consolidated219 _

private theorem support_vanishingIdeal_eq_self_consolidated219 (Z : Closeds ↥X) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z := rfl

private theorem radical_vanishingIdeal_eq_self_consolidated219 (Z : Closeds ↥X) :
    (Scheme.IdealSheafData.vanishingIdeal Z).radical
      = Scheme.IdealSheafData.vanishingIdeal Z := by
  rw [← Scheme.IdealSheafData.vanishingIdeal_support]
  exact Scheme.IdealSheafData.gc.u_l_u_eq_u Z

private theorem le_vanishingIdeal_of_subset_consolidated219 (I : X.IdealSheafData)
    (Z : Closeds ↥X) (h : (Z : Set ↥X) ⊆ (I.support : Set ↥X)) :
    I ≤ Scheme.IdealSheafData.vanishingIdeal Z := by
  have h' : Z ≤ I.support := h
  exact (Scheme.IdealSheafData.gc I Z).mp h'


end

private theorem radical_comap_eq_of_isOpenImmersion_consolidated219 {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (I : Y.IdealSheafData) (hI : I.radical = I) :
    (I.comap f).radical = I.comap f := by
  refine le_antisymm (le_of_ideal_le_consolidated219 ?_) (Scheme.IdealSheafData.le_radical _)
  intro V
  have hV : IsAffineOpen (f ''ᵁ (V : X.Opens)) := V.2.image_of_isOpenImmersion f
  have e : (V : X.Opens) ≤ f ⁻¹ᵁ (f ''ᵁ (V : X.Opens)) := fun x hx => ⟨x, hx, rfl⟩
  have hmap := Scheme.IdealSheafData.comap_ideal_eq_map_appLE I f
    ⟨f ''ᵁ (V : X.Opens), hV⟩ V e
  have hiso : f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e
      = (f.appIso (V : X.Opens)).hom := (Scheme.Hom.appIso_hom' f (V : X.Opens)).symm
  have hsurj : Function.Surjective
      (f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e).hom := by
    rw [hiso]; exact surjective_hom_of_iso_consolidated219 _
  have hker : RingHom.ker (f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e).hom
      ≤ I.ideal ⟨f ''ᵁ (V : X.Opens), hV⟩ := by
    rw [hiso]; exact ker_hom_of_iso_le_consolidated219 _ _
  have hIrad : (I.ideal ⟨f ''ᵁ (V : X.Opens), hV⟩).radical
      = I.ideal ⟨f ''ᵁ (V : X.Opens), hV⟩ := by
    rw [← Scheme.IdealSheafData.radical_ideal, hI]
  have hrw : ((I.comap f).ideal V).radical = (I.comap f).ideal V := by
    rw [hmap, ← Ideal.map_radical_of_surjective hsurj hker, hIrad]
  exact le_of_eq ((Scheme.IdealSheafData.radical_ideal (I.comap f) V).trans hrw)

private theorem radical_ker_eq_of_isReduced_consolidated219 {A B : Scheme.{u}} (g : A ⟶ B)
    [IsAffineHom g] [IsReduced A] :
    (Scheme.Hom.ker g).radical = Scheme.Hom.ker g := by
  refine le_antisymm (le_of_ideal_le_consolidated219 ?_) (Scheme.IdealSheafData.le_radical _)
  intro V
  have key : ∀ y : Γ(B, (V : B.Opens)), y ∈ (Scheme.Hom.ker g).ideal V ↔
      (Scheme.Hom.app g (V : B.Opens)).hom y = 0 := by
    intro y
    rw [← Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ideal_map_of_isAffineHom]
    simp [Scheme.IdealSheafData.ideal_bot, Ideal.mem_comap, Pi.bot_apply, Submodule.mem_bot]
  rw [Scheme.IdealSheafData.radical_ideal]
  intro y hy
  obtain ⟨n, hn⟩ := hy
  refine (key y).2 ?_
  have : _root_.IsReduced Γ(A, g ⁻¹ᵁ (V : B.Opens)) := inferInstance
  refine IsNilpotent.eq_zero ⟨n, ?_⟩
  rw [← map_pow]
  exact (key _).1 hn

section
variable {X : Scheme.{u}}

private theorem isIso_pullback_snd_of_le_consolidated219 (H J : X.IdealSheafData)
    (h : H ≤ J) : IsIso (Limits.pullback.snd H.subschemeι J.subschemeι) := by
  have hker : Scheme.Hom.ker H.subschemeι ≤ Scheme.Hom.ker J.subschemeι := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
    exact h
  have hβfac : AlgebraicGeometry.IsClosedImmersion.lift H.subschemeι J.subschemeι hker
      ≫ H.subschemeι = J.subschemeι :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ hker
  have hcond : AlgebraicGeometry.IsClosedImmersion.lift H.subschemeι J.subschemeι hker
      ≫ H.subschemeι = 𝟙 J.subscheme ≫ J.subschemeι := by
    rw [hβfac, Category.id_comp]
  refine ⟨Limits.pullback.lift _ _ hcond, ?_, Limits.pullback.lift_snd _ _ hcond⟩
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, Limits.pullback.lift_fst, Category.id_comp]
    have hmono : Mono H.subschemeι := inferInstance
    apply hmono.right_cancellation
    rw [Category.assoc, hβfac, Limits.pullback.condition]
  · rw [Category.assoc, Limits.pullback.lift_snd, Category.comp_id, Category.id_comp]

private theorem comap_vanishingIdeal_subschemeι_consolidated219 (H : X.IdealSheafData)
    (Z : Closeds ↥X) (hZH : (Z : Set ↥X) ⊆ (H.support : Set ↥X))
    (S : Closeds ↥(H.subscheme))
    (hS : (S : Set ↥(H.subscheme)) = H.subschemeι.base ⁻¹' (Z : Set ↥X)) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap H.subschemeι =
      Scheme.IdealSheafData.vanishingIdeal S := by
  have hred : IsReduced
      (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isReduced_vanishingIdeal_subscheme_consolidated219 Z
  have hHJ : H ≤ Scheme.IdealSheafData.vanishingIdeal Z :=
    le_vanishingIdeal_of_subset_consolidated219 H Z hZH
  have : IsIso (Limits.pullback.snd H.subschemeι
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) :=
    isIso_pullback_snd_of_le_consolidated219 H _ hHJ
  have : IsOpenImmersion (Limits.pullback.snd H.subschemeι
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) := inferInstance
  have : IsReduced (Limits.pullback H.subschemeι
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) :=
    AlgebraicGeometry.isReduced_of_isOpenImmersion (Limits.pullback.snd H.subschemeι
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)
  have hrad : ((Scheme.IdealSheafData.vanishingIdeal Z).comap H.subschemeι).radical
      = (Scheme.IdealSheafData.vanishingIdeal Z).comap H.subschemeι :=
    radical_ker_eq_of_isReduced_consolidated219 (Limits.pullback.fst H.subschemeι
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal Z).comap H.subschemeι).support = S := by
    apply SetLike.coe_injective
    rw [Scheme.IdealSheafData.support_comap]
    show ⇑H.subschemeι ⁻¹'
      ((Scheme.IdealSheafData.vanishingIdeal Z).support : Set ↥X) = (S : Set ↥(H.subscheme))
    rw [support_vanishingIdeal_eq_self_consolidated219, hS]
  calc (Scheme.IdealSheafData.vanishingIdeal Z).comap H.subschemeι
      = ((Scheme.IdealSheafData.vanishingIdeal Z).comap H.subschemeι).radical := hrad.symm
    _ = Scheme.IdealSheafData.vanishingIdeal
          (((Scheme.IdealSheafData.vanishingIdeal Z).comap H.subschemeι).support) :=
        Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = Scheme.IdealSheafData.vanishingIdeal S := by rw [hsupp]


end

section
variable {W : Scheme.{u}} (U : W.Opens) (T : Closeds ↥W)

private theorem support_comap_opens_vanishingIdeal_consolidated219 :
    ((((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι).support) : Set ↥(U.toScheme))
      = U.ι.base ⁻¹' (T : Set ↥W) := by
  rw [Scheme.IdealSheafData.support_comap]
  show ⇑U.ι ⁻¹' ((Scheme.IdealSheafData.vanishingIdeal T).support : Set ↥W)
    = ⇑U.ι ⁻¹' (T : Set ↥W)
  rw [support_vanishingIdeal_eq_self_consolidated219]

private theorem comap_opens_vanishingIdeal_eq_vanishingIdeal_support_consolidated219 :
    (Scheme.IdealSheafData.vanishingIdeal T).comap U.ι
      = Scheme.IdealSheafData.vanishingIdeal
          (((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι).support) := by
  rw [Scheme.IdealSheafData.vanishingIdeal_support]
  exact (radical_comap_eq_of_isOpenImmersion_consolidated219 U.ι _ (radical_vanishingIdeal_eq_self_consolidated219 T)).symm


end

section
variable {W : Scheme.{u}} (U : W.Opens) (H : (U.toScheme).IdealSheafData) (T : Closeds ↥W)

private theorem le_comap_vanishingIdeal_of_preimage_subset_consolidated219 (hTsubH : (U.ι.base ⁻¹' (T : Set ↥W)) ⊆ (H.support : Set ↥(U.toScheme))) :
    H ≤ (Scheme.IdealSheafData.vanishingIdeal T).comap U.ι := by
  rw [comap_opens_vanishingIdeal_eq_vanishingIdeal_support_consolidated219 U T]
  refine le_vanishingIdeal_of_subset_consolidated219 H _ ?_
  rw [support_comap_opens_vanishingIdeal_consolidated219]
  exact hTsubH

private theorem comap_subschemeι_comap_vanishingIdeal_consolidated219 (S : Closeds ↥(H.subscheme))
    (hS : (S : Set ↥(H.subscheme)) = (H.subschemeι ≫ U.ι).base ⁻¹' (T : Set ↥W))
    (hTsubH : (U.ι.base ⁻¹' (T : Set ↥W)) ⊆ (H.support : Set ↥(U.toScheme))) :
    ((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι).comap H.subschemeι =
      Scheme.IdealSheafData.vanishingIdeal S := by
  rw [comap_opens_vanishingIdeal_eq_vanishingIdeal_support_consolidated219 U T]
  refine comap_vanishingIdeal_subschemeι_consolidated219 H _ ?_ S ?_
  · rw [support_comap_opens_vanishingIdeal_consolidated219]
    exact hTsubH
  · rw [hS, support_comap_opens_vanishingIdeal_consolidated219, ← Set.preimage_comp]
    rfl


end

private theorem exists_isIso_pullback_lift_comap_subschemeι_consolidated219 {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData) :
    ∃ α : (I.comap f).subscheme ⟶ Limits.pullback f I.subschemeι,
      IsIso α ∧ α ≫ Limits.pullback.fst f I.subschemeι = (I.comap f).subschemeι :=
  ⟨(I.comapIso f).hom, inferInstance, Scheme.IdealSheafData.comapIso_hom_fst I f⟩

private theorem smooth_comap_subschemeι_comp_of_smooth_pullback_snd_consolidated219 {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (g : Y ⟶ S)
    (hsm : Smooth (I.subschemeι ≫ g))
    (hsnd : Smooth (Limits.pullback.snd f I.subschemeι)) :
    Smooth ((I.comap f).subschemeι ≫ f ≫ g) := by
  obtain ⟨α, hα, hαfac⟩ := exists_isIso_pullback_lift_comap_subschemeι_consolidated219 f I
  have key : (I.comap f).subschemeι ≫ f ≫ g
      = α ≫ (Limits.pullback.snd f I.subschemeι ≫ I.subschemeι ≫ g) := by
    calc (I.comap f).subschemeι ≫ f ≫ g
        = (α ≫ Limits.pullback.fst f I.subschemeι) ≫ f ≫ g := by rw [hαfac]
      _ = α ≫ ((Limits.pullback.fst f I.subschemeι ≫ f) ≫ g) := by simp
      _ = α ≫ ((Limits.pullback.snd f I.subschemeι ≫ I.subschemeι) ≫ g) := by
            rw [Limits.pullback.condition]
      _ = α ≫ (Limits.pullback.snd f I.subschemeι ≫ I.subschemeι ≫ g) := by simp
  rw [key]
  have := hα
  have := hsm
  have := hsnd
  infer_instance

private theorem exists_irreducibleComponent_mem_consolidated219 (α : Type u) [TopologicalSpace α] (x : α) :
    ∃ C ∈ irreducibleComponents α, x ∈ C :=
  ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x,
    mem_irreducibleComponent⟩

theorem comap_vanishingIdeal_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (T : Closeds ↥Y) (S : Closeds ↥X)
    (hS : (S : Set ↥X) = f.base ⁻¹' (T : Set ↥Y)) :
    (Scheme.IdealSheafData.vanishingIdeal T).comap f =
      Scheme.IdealSheafData.vanishingIdeal S := by
  have hrad := radical_comap_eq_of_isOpenImmersion_consolidated219 f
    (Scheme.IdealSheafData.vanishingIdeal T) (radical_vanishingIdeal_eq_self_consolidated219 T)
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal T).comap f).support = S := by
    apply SetLike.coe_injective
    rw [Scheme.IdealSheafData.support_comap]
    show ⇑f ⁻¹' ((Scheme.IdealSheafData.vanishingIdeal T).support : Set ↥Y) = (S : Set ↥X)
    rw [support_vanishingIdeal_eq_self_consolidated219, hS]
  calc (Scheme.IdealSheafData.vanishingIdeal T).comap f
      = ((Scheme.IdealSheafData.vanishingIdeal T).comap f).radical := hrad.symm
    _ = Scheme.IdealSheafData.vanishingIdeal
          (((Scheme.IdealSheafData.vanishingIdeal T).comap f).support) :=
        Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = Scheme.IdealSheafData.vanishingIdeal S := by rw [hsupp]

theorem agreeNearVanishingComapSubscheme : AgreeNearVanishingComapSubscheme.{u} := by
  intro W N U H T S x hS hTsubH hN
  simp only [vanishingIdealAssignment_apply] at hN ⊢
  obtain ⟨V, hxV, hVeq⟩ := (agreeNear_iff _ _ _).1 hN
  have hrange : Set.range ⇑(((H.subschemeι ≫ U.ι) ⁻¹ᵁ V).ι ≫ H.subschemeι ≫ U.ι)
      ⊆ Set.range ⇑V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro z ⟨y, rfl⟩
    have hy : ((H.subschemeι ≫ U.ι) ⁻¹ᵁ V).ι y
        ∈ (((H.subschemeι ≫ U.ι) ⁻¹ᵁ V : (H.subscheme).Opens) : Set ↥(H.subscheme)) := by
      rw [← Scheme.Opens.range_ι ((H.subschemeι ≫ U.ι) ⁻¹ᵁ V)]
      exact ⟨y, rfl⟩
    exact hy
  obtain ⟨g, hg⟩ : ∃ g : ((H.subschemeι ≫ U.ι) ⁻¹ᵁ V).toScheme ⟶ V.toScheme,
      g ≫ V.ι = ((H.subschemeι ≫ U.ι) ⁻¹ᵁ V).ι ≫ H.subschemeι ≫ U.ι :=
    ⟨AlgebraicGeometry.IsOpenImmersion.lift V.ι _ hrange,
      AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hrange⟩
  refine (agreeNear_iff _ _ _).2 ⟨(H.subschemeι ≫ U.ι) ⁻¹ᵁ V, hxV, ?_⟩
  have e : ∀ I : W.IdealSheafData,
      ((I.comap U.ι).comap H.subschemeι).comap ((H.subschemeι ≫ U.ι) ⁻¹ᵁ V).ι
        = (I.comap V.ι).comap g := by
    intro I
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, Category.assoc,
      ← hg, ← Scheme.IdealSheafData.comap_comp]
  rw [e N, hVeq, ← e, comap_subschemeι_comap_vanishingIdeal_consolidated219 U H T S hS hTsubH]

theorem smooth_subschemeι_comp_of_eq {X S : Scheme.{u}} (f : X ⟶ S) {K K' : X.IdealSheafData}
    (h : K = K') (hsm : Smooth (K'.subschemeι ≫ f)) :
    Smooth (K.subschemeι ≫ f) := by
  subst h
  exact hsm

theorem smooth_comap_subschemeι_of_isOpenImmersion {X Y S : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (I : Y.IdealSheafData) (g : Y ⟶ S)
    (hsm : Smooth (I.subschemeι ≫ g)) :
    Smooth ((I.comap f).subschemeι ≫ f ≫ g) := by
  have : Smooth (Limits.pullback.snd f I.subschemeι) := inferInstance
  exact smooth_comap_subschemeι_comp_of_smooth_pullback_snd_consolidated219 f I g hsm inferInstance

section
variable {k : Type u} [Field k]

theorem smooth_vanishingIdeal_comap_subschemeι {W : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens) (H : (U.toScheme).IdealSheafData)
    (_hH : FunctorialResolution.EmbeddedResolution.IsSmoothDivisor (U.ι ≫ p) H)
    (T : Closeds ↥W) (S : Closeds ↥(H.subscheme))
    (hS : (S : Set ↥(H.subscheme)) = (H.subschemeι ≫ U.ι).base ⁻¹' (T : Set ↥W))
    (hTsubH : (U.ι.base ⁻¹' (T : Set ↥W)) ⊆ (H.support : Set ↥(U.toScheme)))
    (hT : Smooth ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p)) :
    Smooth
      ((Scheme.IdealSheafData.vanishingIdeal S).subschemeι ≫ H.subschemeι ≫ U.ι ≫ p) := by
  have hcomap := comap_subschemeι_comap_vanishingIdeal_consolidated219 U H T S hS hTsubH
  refine smooth_subschemeι_comp_of_eq (H.subschemeι ≫ U.ι ≫ p) hcomap.symm ?_
  have hJ : Smooth
      (((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι).subschemeι ≫ U.ι ≫ p) :=
    smooth_comap_subschemeι_of_isOpenImmersion U.ι
      (Scheme.IdealSheafData.vanishingIdeal T) p hT
  have : IsIso (Limits.pullback.snd H.subschemeι
      ((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι).subschemeι) :=
    isIso_pullback_snd_of_le_consolidated219 H _ (le_comap_vanishingIdeal_of_preimage_subset_consolidated219 U H T hTsubH)
  have hsnd : Smooth (Limits.pullback.snd H.subschemeι
      ((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι).subschemeι) := inferInstance
  exact smooth_comap_subschemeι_comp_of_smooth_pullback_snd_consolidated219 H.subschemeι
    ((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι) (U.ι ≫ p) hJ hsnd

theorem orderAt_vanishingIdeal_eq_one [CharZero k] {W : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of k)) (hp : Smooth p) (T : Closeds ↥W)
    (_hirr : IsIrreducible (T : Set ↥W))
    (hsm : Smooth ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p))
    (hcomp : ∀ C ∈ irreducibleComponents ↥W, ¬ C ⊆ (T : Set ↥W))
    (x : ↥W) (hx : x ∈ (T : Set ↥W)) :
    FunctorialResolution.EmbeddedResolution.orderAt (Scheme.IdealSheafData.vanishingIdeal T) x = 1 := by
  have hp' : Smooth p := hp
  have hsm' : Smooth
      ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p) := hsm
  have hZs : (Scheme.IdealSheafData.vanishingIdeal T).support = T :=
    support_vanishingIdeal_eq_self_consolidated219 T
  have hxZ : x ∈ (Scheme.IdealSheafData.vanishingIdeal T).support := by
    rw [hZs]; exact hx
  obtain ⟨U, m, c, S, hxU, hU, hD⟩ :=
    FunctorialResolution.EmbeddedResolution.exists_chart_restrictIdeal_eq_coordIdeal p
      (Scheme.IdealSheafData.vanishingIdeal T) x hxZ
  rcases S.eq_empty_or_nonempty with hSe | ⟨j, hj⟩
  · exfalso
    have key : ∀ y : ↥(U.toScheme),
        FunctorialResolution.EmbeddedResolution.orderAt (Scheme.IdealSheafData.vanishingIdeal T) (U.ι.base y) = ⊤ := by
      intro y
      have h1 : FunctorialResolution.EmbeddedResolution.restrictIdeal (Scheme.IdealSheafData.vanishingIdeal T) U
          = c.coordIdeal (∅ : Finset (Fin m)) := by rw [hD, hSe]
      have h2 : (Scheme.IdealSheafData.vanishingIdeal T).comap U.ι
          = (⊥ : (FunctorialResolution.EmbeddedResolution.affineSpaceFin k m).IdealSheafData).comap c.map := by
        rw [← FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_comap_ι, h1, FunctorialResolution.EmbeddedResolution.EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal,
          FunctorialResolution.EmbeddedResolution.coordSubspaceIdeal_empty]
      have h3 : FunctorialResolution.EmbeddedResolution.stalkIdeal ((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι) y
          = FunctorialResolution.EmbeddedResolution.stalkIdeal (⊥ : (U.toScheme).IdealSheafData) y := by
        rw [h2, FunctorialResolution.EmbeddedResolution.stalkIdeal_comap, FunctorialResolution.EmbeddedResolution.stalkIdeal_bot, Ideal.map_bot,
          FunctorialResolution.EmbeddedResolution.stalkIdeal_bot]
      have h4 : FunctorialResolution.EmbeddedResolution.orderAt ((Scheme.IdealSheafData.vanishingIdeal T).comap U.ι) y = ⊤ := by
        rw [FunctorialResolution.EmbeddedResolution.orderAt_eq_of_stalkIdeal_eq h3, FunctorialResolution.EmbeddedResolution.orderAt_bot]
      exact (FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isOpenImmersion U.ι
        (Scheme.IdealSheafData.vanishingIdeal T) y).symm.trans h4
    have hUsubT : (U : Set ↥W) ⊆ (T : Set ↥W) := by
      intro z hz
      have hrange : Set.range U.ι.base = (U : Set ↥W) := by simp
      obtain ⟨y, rfl⟩ : z ∈ Set.range U.ι.base := by rw [hrange]; exact hz
      have h6 : (1 : ℕ∞) ≤ FunctorialResolution.EmbeddedResolution.orderAt (Scheme.IdealSheafData.vanishingIdeal T)
          (U.ι.base y) := by
        rw [key y]; exact le_top
      have h7 := (FunctorialResolution.EmbeddedResolution.one_le_orderAt_iff_mem_support _ _).1 h6
      rw [hZs] at h7
      exact h7
    obtain ⟨C, hC, hxC⟩ := exists_irreducibleComponent_mem_consolidated219 (↥W) x
    refine hcomp C hC ?_
    intro z hzC
    by_contra hzT
    obtain ⟨w, hwC, hwU, hwT⟩ := hC.1.2 (U : Set ↥W) ((T : Set ↥W)ᶜ) U.isOpen
      T.2.isOpen_compl ⟨x, hxC, hxU⟩ ⟨z, hzC, hzT⟩
    exact hwT (hUsubT hwU)
  · exact FunctorialResolution.EmbeddedResolution.orderAt_eq_one_of_restrictIdeal_eq_coordIdeal p hU c S j hj
      (Scheme.IdealSheafData.vanishingIdeal T) hD x hxU hxZ


end

end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealHypotheses
section

open TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

namespace OpenImmersionRestriction

theorem vanishingComapOpens : VanishingComapOpens.{u} := by
  intro W T U T' hT'
  simp only [vanishingIdealAssignment_apply]
  exact comap_vanishingIdeal_of_isOpenImmersion U.ι T T' hT'

theorem idealSheafGeometryHypotheses_vanishingIdealAssignment : IdealSheafGeometryHypotheses (vanishingIdealAssignment.{u}) :=
  idealSheafGeometryHypotheses_of_vanishingOrderOneOnSmoothDivisor vanishingOrderOneOnSmoothDivisor agreeNearVanishingComapSubscheme vanishingComapOpens

private theorem orderAt_vanishingIdealAssignment_eq_one_consolidated237 :
    ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)), Smooth p →
      ∀ T : Closeds ↥W, IsIrreducible (T : Set ↥W) →
      Smooth ((vanishingIdealAssignment W T).subschemeι ≫ p) →
      (∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ (T : Set ↥W)) →
      ∀ x ∈ (T : Set ↥W), FunctorialResolution.EmbeddedResolution.orderAt (vanishingIdealAssignment W T) x = 1 := by
  intro k _ _ W p hp T hirr hsm hcomp x hx
  rw [vanishingIdealAssignment_apply] at hsm ⊢
  exact orderAt_vanishingIdeal_eq_one p hp T hirr hsm hcomp x hx

private theorem smooth_opens_ι_comp_of_smooth_consolidated237 :
    ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens), Smooth p → Smooth (U.ι ≫ p) := by
  intro k _ _ W p U hp
  have : Smooth p := hp
  infer_instance

private theorem smooth_vanishingIdealAssignment_of_isSmoothDivisor_consolidated237 :
    ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens) (H : (U.toScheme).IdealSheafData),
      IsSmoothDivisor (U.ι ≫ p) H →
      ∀ (T : Closeds ↥W) (S : Closeds ↥(H.subscheme)),
        (S : Set ↥(H.subscheme)) = (H.subschemeι ≫ U.ι).base ⁻¹' (T : Set ↥W) →
        (U.ι.base ⁻¹' (T : Set ↥W)) ⊆ (H.support : Set ↥(U.toScheme)) →
        Smooth ((vanishingIdealAssignment W T).subschemeι ≫ p) →
        Smooth ((vanishingIdealAssignment H.subscheme S).subschemeι ≫ (H.subschemeι ≫ (U.ι ≫ p))) := by
  intro k _ _ W p U H hH T S hS hTsubH hT
  rw [vanishingIdealAssignment_apply] at hT ⊢
  exact smooth_vanishingIdeal_comap_subschemeι p U H hH T S hS hTsubH hT

private theorem smooth_vanishingIdealAssignment_restrict_opens_consolidated237 :
    ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens) (T : Closeds ↥W)
      (S : Closeds ↥(U.toScheme)),
      (S : Set ↥(U.toScheme)) = U.ι.base ⁻¹' (T : Set ↥W) →
      Smooth ((vanishingIdealAssignment W T).subschemeι ≫ p) →
      Smooth ((vanishingIdealAssignment U.toScheme S).subschemeι ≫ (U.ι ≫ p)) := by
  intro k _ _ W p U T S hS hT
  rw [vanishingIdealAssignment_apply] at hT ⊢
  exact smooth_subschemeι_comp_of_eq (U.ι ≫ p)
    (comap_vanishingIdeal_of_isOpenImmersion U.ι T S hS).symm
    (smooth_comap_subschemeι_of_isOpenImmersion U.ι
      (Scheme.IdealSheafData.vanishingIdeal T) p hT)

theorem smoothVanishingHypotheses_vanishingIdealAssignment : SmoothVanishingHypotheses (vanishingIdealAssignment.{u}) where
  orderAt_vanishing_eq_one := orderAt_vanishingIdealAssignment_eq_one_consolidated237
  smooth_opens_ι_comp := smooth_opens_ι_comp_of_smooth_consolidated237
  smooth_vanishing_hypersurface := smooth_vanishingIdealAssignment_of_isSmoothDivisor_consolidated237
  smooth_vanishing_opens := smooth_vanishingIdealAssignment_restrict_opens_consolidated237

theorem smoothOrderOneCentersIsolated_vanishingIdealAssignment_of_principalizationCertificate {k : Type u} [Field k] [CharZero k]
    {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z) :
    SmoothOrderOneCentersIsolated (vanishingIdealAssignment.{u}) W p I m Mem Z :=
  smoothOrderOneCentersIsolated_of_principalizationCertificate idealSheafGeometryHypotheses_vanishingIdealAssignment smoothVanishingHypotheses_vanishingIdealAssignment h

end OpenImmersionRestriction

theorem openImmersionStability (k : Type u) [Field k] : OpenImmersionStability.{u} k := by
  refine ⟨?_, ?_, ?_⟩
  · intro V W f hf J hJ
    have : IsOpenImmersion f := hf
    exact NonzeroOnComponents.comap_of_isOpenImmersion hJ f
  · intro V W f hf D
    have : IsOpenImmersion f := hf
    exact OpenImmersionRestriction.isOpenImmersion_subschemeMap f D (comapSubscheme f D) (comapSubscheme_comp f D)
  · intro V W f hf p D hD
    have : IsOpenImmersion f := hf
    exact OpenImmersionRestriction.isSmoothDivisor_comap f p D hD

theorem PrincipalizationCertificate.comap_of_isOpenImmersion {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z) {V : Scheme.{u}} (f : V ⟶ W)
    [IsOpenImmersion f] :
    PrincipalizationCertificate V (f ≫ p) (I.comap f) m (f.base ⁻¹' Mem) (Z.comap f) :=
  h.comap_of_openImmersionStability (openImmersionStability k) f

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.FieldExtensionEtaleCover
section

open CategoryTheory.Limits

namespace FunctorialResolution.EmbeddedResolution

section
variable {k : Type u} [Field k] {X W : Scheme.{u}}

private theorem pullbackCondition_baseChangeMap_consolidated82 (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
    (K : Type u) [Field K] [Algebra k K] :
    (baseChangeProjection (c ≫ f) K ≫ c) ≫ f = baseChangeToSpec (c ≫ f) K ≫ specMapAlgebraMap k K := by
  rw [Category.assoc]
  exact pullback.condition

def baseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
    (K : Type u) [Field K] [Algebra k K] :
    baseChange (c ≫ f) K ⟶ baseChange f K :=
  pullback.lift (baseChangeProjection (c ≫ f) K ≫ c) (baseChangeToSpec (c ≫ f) K)
    (pullbackCondition_baseChangeMap_consolidated82 f c K)

@[simp]
theorem baseChangeMap_comp_baseChangeProjection (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
    (K : Type u) [Field K] [Algebra k K] :
    baseChangeMap f c K ≫ baseChangeProjection f K = baseChangeProjection (c ≫ f) K ≫ c :=
  pullback.lift_fst _ _ _

@[simp]
theorem baseChangeMap_comp_baseChangeToSpec (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
    (K : Type u) [Field K] [Algebra k K] :
    baseChangeMap f c K ≫ baseChangeToSpec f K = baseChangeToSpec (c ≫ f) K :=
  pullback.lift_snd _ _ _

private theorem morphismProperty_of_isPullback_consolidated82 {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {A B C' D : Scheme.{u}} {h : A ⟶ B} {v : A ⟶ C'} {v' : B ⟶ D}
    {b : C' ⟶ D} (sq : IsPullback h v v' b) (hb : P b) : P h :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip hb

section
variable (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)

private theorem isPullback_baseChangeMap_consolidated82 (K : Type u) [Field K] [Algebra k K] :
    IsPullback (baseChangeMap f c K) (baseChangeProjection (c ≫ f) K) (baseChangeProjection f K) c := by
  have h1 : IsPullback (baseChangeToSpec (c ≫ f) K) (baseChangeProjection (c ≫ f) K)
      (specMapAlgebraMap k K) (c ≫ f) := (IsPullback.of_hasPullback (c ≫ f) (specMapAlgebraMap k K)).flip
  have h2 : IsPullback (baseChangeToSpec f K) (baseChangeProjection f K) (specMapAlgebraMap k K) f :=
    (IsPullback.of_hasPullback f (specMapAlgebraMap k K)).flip
  refine IsPullback.of_right ?_ (baseChangeMap_comp_baseChangeProjection f c K) h2
  rw [baseChangeMap_comp_baseChangeToSpec]
  exact h1

theorem etale_baseChangeMap [Etale c]
    (K : Type u) [Field K] [Algebra k K] : Etale (baseChangeMap f c K) :=
  morphismProperty_of_isPullback_consolidated82 (P := @Etale) (isPullback_baseChangeMap_consolidated82 f c K) ‹Etale c›


end

instance instEtaleBaseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [Etale c]
    (K : Type u) [Field K] [Algebra k K] : Etale (baseChangeMap f c K) :=
  etale_baseChangeMap f c K

theorem surjective_baseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [Surjective c]
    (K : Type u) [Field K] [Algebra k K] : Surjective (baseChangeMap f c K) :=
  morphismProperty_of_isPullback_consolidated82 (P := @Surjective) (isPullback_baseChangeMap_consolidated82 f c K) ‹Surjective c›

instance instSurjectiveBaseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [Surjective c]
    (K : Type u) [Field K] [Algebra k K] : Surjective (baseChangeMap f c K) :=
  surjective_baseChangeMap f c K

theorem isAffine_baseChange (p : W ⟶ Spec (CommRingCat.of k)) [IsAffine W]
    (K : Type u) [Field K] [Algebra k K] : IsAffine (baseChange p K) := by
  have : IsAffineHom (baseChangeProjection p K) :=
    morphismProperty_of_isPullback_consolidated82 (P := @IsAffineHom) (IsPullback.of_hasPullback p (specMapAlgebraMap k K))
      inferInstance
  exact isAffine_of_isAffineHom (f := baseChangeProjection p K)

theorem isAffine_baseChange_comp (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [IsAffine W]
    (K : Type u) [Field K] [Algebra k K] : IsAffine (baseChange (c ≫ f) K) :=
  isAffine_baseChange (c ≫ f) K

private theorem isReduced_of_isReduced_stalk_consolidated82 (Y : Scheme.{u})
    (h : ∀ y : ↥Y, _root_.IsReduced (Y.presheaf.stalk y)) : IsReduced Y := by
  have : ∀ y : ↥Y, _root_.IsReduced (Y.presheaf.stalk y) := h
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk Y

private theorem isReduced_stalk_of_isOpenImmersion_consolidated82 {A B : Scheme.{u}} (w : A ⟶ B)
    [IsOpenImmersion w] [IsReduced B] (a : ↥A) : _root_.IsReduced (A.presheaf.stalk a) :=
  isReduced_of_injective (CategoryTheory.inv (w.stalkMap a)).hom
    (ConcreteCategory.bijective_of_isIso (CategoryTheory.inv (w.stalkMap a))).1

private theorem isReduced_of_isReduced_stalk_of_cover_consolidated82 {Y : Scheme.{u}} {ι : Type u} {Z : ι → Scheme.{u}}
    (j : ∀ i, Z i ⟶ Y) (hj : ∀ i, IsOpenImmersion (j i))
    (hZ : ∀ (i : ι) (z : ↥(Z i)), _root_.IsReduced ((Z i).presheaf.stalk z))
    (hcov : ∀ y : ↥Y, ∃ (i : ι) (z : ↥(Z i)), (j i).base z = y) : IsReduced Y := by
  refine isReduced_of_isReduced_stalk_consolidated82 Y ?_
  intro y
  obtain ⟨i, z, rfl⟩ := hcov y
  have := hj i
  have := hZ i z
  exact isReduced_of_injective ((j i).stalkMap z).hom
    (ConcreteCategory.bijective_of_isIso ((j i).stalkMap z)).1

private theorem sigma_jointly_surjective_consolidated82 {ι : Type u} (Z : ι → Scheme.{u}) (x : ↥(∐ Z)) :
    ∃ (i : ι) (y : ↥(Z i)), (Sigma.ι Z i).base y = x := by
  obtain ⟨y, hy⟩ := (sigmaOpenCover Z).covers x
  exact ⟨_, y, hy⟩

private theorem exists_pullback_snd_base_eq_consolidated82 {A B C' : Scheme.{u}} (g1 : A ⟶ C') (g2 : B ⟶ C')
    (a : ↥A) (b : ↥B) (h : g1.base a = g2.base b) :
    ∃ z : ↥(pullback g1 g2), (pullback.snd g1 g2).base z = b := by
  obtain ⟨z, _, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := g1) (g := g2) a b h
  exact ⟨z, hz2⟩

theorem isReduced_baseChange_sigmaOpensDesc (f : X ⟶ Spec (CommRingCat.of k))
    (K : Type u) [Field K] [Algebra k K] [IsReduced (baseChange f K)]
    {ι : Type u} (U : ι → X.Opens) :
    IsReduced (baseChange (sigmaOpensDesc X U ≫ f) K) := by
  have hsq : ∀ i : ι, IsPullback
      (pullback.snd (Sigma.ι (fun i => (U i).toScheme) i)
          (baseChangeProjection (sigmaOpensDesc X U ≫ f) K) ≫
        baseChangeMap f (sigmaOpensDesc X U) K)
      (pullback.fst (Sigma.ι (fun i => (U i).toScheme) i)
        (baseChangeProjection (sigmaOpensDesc X U ≫ f) K))
      (baseChangeProjection f K) ((U i).ι) := by
    intro i
    have h := IsPullback.paste_horiz
      (IsPullback.of_hasPullback (Sigma.ι (fun i => (U i).toScheme) i)
        (baseChangeProjection (sigmaOpensDesc X U ≫ f) K)).flip
      (isPullback_baseChangeMap_consolidated82 f (sigmaOpensDesc X U) K)
    rwa [sigma_ι_sigmaOpensDesc X U i] at h
  refine isReduced_of_isReduced_stalk_of_cover_consolidated82
    (Z := fun i => pullback (Sigma.ι (fun i => (U i).toScheme) i)
      (baseChangeProjection (sigmaOpensDesc X U ≫ f) K))
    (fun i => pullback.snd (Sigma.ι (fun i => (U i).toScheme) i)
      (baseChangeProjection (sigmaOpensDesc X U ≫ f) K))
    (fun i => inferInstance) (fun i z => ?_) ?_
  · have : IsOpenImmersion (pullback.snd (Sigma.ι (fun i => (U i).toScheme) i)
        (baseChangeProjection (sigmaOpensDesc X U ≫ f) K) ≫
        baseChangeMap f (sigmaOpensDesc X U) K) :=
      morphismProperty_of_isPullback_consolidated82 (P := @IsOpenImmersion) (hsq i) inferInstance
    exact isReduced_stalk_of_isOpenImmersion_consolidated82
      (pullback.snd (Sigma.ι (fun i => (U i).toScheme) i)
        (baseChangeProjection (sigmaOpensDesc X U ≫ f) K) ≫
        baseChangeMap f (sigmaOpensDesc X U) K) z
  · intro p
    obtain ⟨i, y, hy⟩ := sigma_jointly_surjective_consolidated82 (fun i => (U i).toScheme)
      ((baseChangeProjection (sigmaOpensDesc X U ≫ f) K).base p)
    obtain ⟨z, hz⟩ := exists_pullback_snd_base_eq_consolidated82 (Sigma.ι (fun i => (U i).toScheme) i)
      (baseChangeProjection (sigmaOpensDesc X U ≫ f) K) y p hy
    exact ⟨i, z, hz⟩

theorem exists_etale_surjective_affine_cover_baseChange (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X]
    (K : Type u) [Field K] [Algebra k K] [IsReduced (baseChange f K)] :
    ∃ (W : Scheme.{u}) (c : W ⟶ X) (g : baseChange (c ≫ f) K ⟶ baseChange f K),
      IsAffine W ∧ IsReduced W ∧ LocallyOfFiniteType (c ≫ f) ∧ QuasiCompact (c ≫ f) ∧
        Etale c ∧ Surjective c ∧
        IsAffine (baseChange (c ≫ f) K) ∧ IsReduced (baseChange (c ≫ f) K) ∧
        LocallyOfFiniteType (baseChangeToSpec (c ≫ f) K) ∧
        QuasiCompact (baseChangeToSpec (c ≫ f) K) ∧
        Etale g ∧ Surjective g ∧
        g ≫ baseChangeToSpec f K = baseChangeToSpec (c ≫ f) K ∧
        g ≫ baseChangeProjection f K = baseChangeProjection (c ≫ f) K ≫ c := by
  have : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace (f := f)
  obtain ⟨ι, hι, U, hUaff, hUtop⟩ := exists_finite_affine_cover X
  have := hι
  have hWaff : IsAffine (sigmaOpens X U) := isAffine_sigmaOpens X U hUaff
  have hsurj : Surjective (sigmaOpensDesc X U) := surjective_sigmaOpensDesc X U hUtop
  have hqc : QuasiCompact (sigmaOpensDesc X U ≫ f) := inferInstance
  have hbcaff : IsAffine (baseChange (sigmaOpensDesc X U ≫ f) K) :=
    isAffine_baseChange_comp f (sigmaOpensDesc X U) K
  refine ⟨sigmaOpens X U, sigmaOpensDesc X U, baseChangeMap f (sigmaOpensDesc X U) K,
    hWaff, inferInstance, inferInstance, hqc, inferInstance, hsurj, hbcaff,
    isReduced_baseChange_sigmaOpensDesc f K U, ?_, ?_, inferInstance, inferInstance,
    baseChangeMap_comp_baseChangeToSpec f (sigmaOpensDesc X U) K,
    baseChangeMap_comp_baseChangeProjection f (sigmaOpensDesc X U) K⟩
  · exact morphismProperty_of_isPullback_consolidated82 (P := @LocallyOfFiniteType)
      (IsPullback.of_hasPullback (sigmaOpensDesc X U ≫ f) (specMapAlgebraMap k K)).flip inferInstance
  · exact morphismProperty_of_isPullback_consolidated82 (P := @QuasiCompact)
      (IsPullback.of_hasPullback (sigmaOpensDesc X U ≫ f) (specMapAlgebraMap k K)).flip inferInstance

end

end FunctorialResolution.EmbeddedResolution
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
section

open TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

def AffineEmbedsIntoAffineSpace : Prop :=
  ∀ (k : Type u) [Field k] (Y : Scheme.{u}) [IsAffine Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p],
    ∃ (n : ℕ) (e : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))),
      IsClosedImmersion e ∧ NonzeroOnComponents e.ker ∧
        e ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) = p

def NilIsStrictNormalCrossingsOnAffineSpace : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)))
      ([] : List (affineSpaceIndexedBy k (ULift.{u} (Fin n))).IdealSheafData)

def AffineSpaceIsSmooth : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    Smooth (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)))

def ClosedEmbeddingsRelatedByAutomorphism : Prop :=
  ∀ (k : Type u) [Field k] (Y : Scheme.{u}) [IsAffine Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (n m : ℕ)
    (e₁ : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n)))
    [IsClosedImmersion e₁]
    (e₂ : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m)))
    [IsClosedImmersion e₂],
    e₁ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) = p →
    e₂ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin m)) = p →
    ∃ Φ : affineSpaceIndexedBy k (ULift.{u} (Fin n ⊕ Fin m)) ≅
            affineSpaceIndexedBy k (ULift.{u} (Fin n ⊕ Fin m)),
      Φ.hom ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) =
          affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) ∧
        AffineSpace.homOfVector p (coordVectorInl n m e₁) ≫ Φ.hom =
          AffineSpace.homOfVector p (coordVectorInr n m e₂)

abbrev AffineResolutionRule : Type (u + 1) :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y], SequenceOfBlowups Y

def IsCompatibleWithOpenImmersions (R : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    [IsReduced Y] [IsAffine Y]
    [LocallyOfFiniteType pV] [QuasiCompact pV]
    [IsReduced V] [IsAffine V]
    (φ : V ⟶ Y) [IsOpenImmersion φ],
    φ ≫ pY = pV → IsPullbackBlowupSequence φ (R k V pV) (R k Y pY)

def IsCompatibleWithEtaleCovers (R : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y W : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pW : W ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    [IsReduced Y] [IsAffine Y]
    [LocallyOfFiniteType pW] [QuasiCompact pW]
    [IsReduced W] [IsAffine W]
    (φ : W ⟶ Y) [Etale φ],
    φ ≫ pY = pW → (∀ y : ↥Y, ∃ w : ↥W, φ.base w = y) →
    IsStrictPullbackBlowupSeq φ (R k W pW) (R k Y pY)

def IsCompatibleWithFieldBaseChange (R : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y] (K : Type u) [Field K] [CharZero K] [Algebra k K]
    [IsReduced (baseChange p K)]
    [IsAffine (baseChange p K)],
    IsStrictPullbackBlowupSeq (baseChangeProjection p K)
      (R K (baseChange p K) (baseChangeToSpec p K)) (R k Y p)

def IsInducedByAffineRule (R : AffineResolutionRule.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) (B : SequenceOfBlowups Y) : Prop :=
  ∀ (W : Scheme.{u}) (q : W ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType q] [QuasiCompact q]
    [IsReduced W] [IsAffine W]
    (φ : W ⟶ Y) [Etale φ],
    φ ≫ p = q → (∀ y : ↥Y, ∃ w : ↥W, φ.base w = y) → IsStrictPullbackBlowupSeq φ (R k W q) B

def ExistsGluedBlowupSequence (R : AffineResolutionRule.{u}) : Prop :=
  IsCompatibleWithEtaleCovers R →
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y],
    ∃ B : SequenceOfBlowups Y, (∀ i, i < B.length → B.center i ≠ ⊤) ∧ IsInducedByAffineRule R k Y p B

def InducedRuleCompatibleWithFieldExtension (R : AffineResolutionRule.{u}) : Prop :=
  IsCompatibleWithOpenImmersions R → IsCompatibleWithFieldBaseChange R →
  ∀ F : ResolutionRule.{u},
    (∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
      [QuasiCompact f] [IsReduced X],
      IsInducedByAffineRule R k X f (F k X f)) →
    IsCompatibleWithFieldExtension F

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceIsomorphism
section


section
namespace FunctorialResolution.EmbeddedResolution

private theorem iso_hom_comp_projectionToBase_consolidated93 {X' : Scheme.{u}} {s' s'' : SequenceOfBlowups X'}
    (ε : ∀ i : ℕ, i ≤ s'.length → (s'.schemeAt i ≅ s''.schemeAt i))
    (h0 : (ε 0 (Nat.zero_le _)).hom ≫ s''.isoZero.hom = s'.isoZero.hom)
    (hst : ∀ i : ℕ, ∀ hi : i < s'.length,
      (ε (i + 1) hi).hom ≫ s''.transitionMapSucc i = s'.transitionMapSucc i ≫ (ε i hi.le).hom) :
    ∀ i : ℕ, ∀ hi : i ≤ s'.length, (ε i hi).hom ≫ s''.projectionToBase i = s'.projectionToBase i := by
  intro i
  induction i with
  | zero =>
    intro hi
    rw [s''.projectionToBase_zero, s'.projectionToBase_zero]
    exact h0
  | succ n ih =>
    intro hi
    rw [s''.projectionToBase_succ n, s'.projectionToBase_succ n, ← Category.assoc,
      hst n hi, Category.assoc, ih (Nat.le_of_succ_le hi)]

private def pullbackProjectionToBaseIsoOfEq_consolidated93 {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X) {a b : ℕ}
    (h : a = b) :
    Limits.pullback φ (s.projectionToBase a) ≅ Limits.pullback φ (s.projectionToBase b) :=
  eqToIso (by rw [h])

section
variable {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X)

private theorem pullbackIsoOfEq_hom_fst_consolidated93 {a b : ℕ} (h : a = b) :
    (pullbackProjectionToBaseIsoOfEq_consolidated93 φ s h).hom ≫ Limits.pullback.fst φ (s.projectionToBase b)
      = Limits.pullback.fst φ (s.projectionToBase a) := by
  subst h
  simp [pullbackProjectionToBaseIsoOfEq_consolidated93]

private theorem pullbackIsoOfEq_hom_comp_pullbackTransitionMap_consolidated93 {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (hab : a ≤ b) (hab' : a' ≤ b') :
    (pullbackProjectionToBaseIsoOfEq_consolidated93 φ s hb).hom ≫ s.pullbackTransitionMap φ hab'
      = s.pullbackTransitionMap φ hab ≫ (pullbackProjectionToBaseIsoOfEq_consolidated93 φ s ha).hom := by
  subst ha
  subst hb
  have hpr : hab = hab' := rfl
  subst hpr
  simp [pullbackProjectionToBaseIsoOfEq_consolidated93]

private theorem comap_pullbackIsoOfEq_consolidated93 {a b : ℕ}
    (h : a = b) {W : Scheme.{u}} (g : W ⟶ Limits.pullback φ (s.projectionToBase a)) :
    (s.center b).comap (g ≫ (pullbackProjectionToBaseIsoOfEq_consolidated93 φ s h).hom ≫ Limits.pullback.snd φ (s.projectionToBase b))
      = (s.center a).comap (g ≫ Limits.pullback.snd φ (s.projectionToBase a)) := by
  subst h
  simp [pullbackProjectionToBaseIsoOfEq_consolidated93]


end

section
variable {n m L : ℕ} {r q : ℕ → ℕ} {P : ℕ → Prop}

private theorem strictMono_enumeration_le_consolidated93 (hr2 : ∀ i j : ℕ, j ≤ n → i < j → r i < r j)
    (hq1 : ∀ i, i < m → q i < L)
    (hq2 : ∀ i j : ℕ, j ≤ m → i < j → q i < q j)
    (hr4 : ∀ i, i < L → (P i ↔ ∃ j, j < n ∧ r j = i))
    (hq4 : ∀ i, i < L → (P i ↔ ∃ j, j < m ∧ q j = i)) :
    ∀ i, i < n → i < m → r i ≤ q i := by
  have main : ∀ k i : ℕ, i < k → i < n → i < m → r i ≤ q i := by
    intro k
    induction k with
    | zero => intro i hik; exact absurd hik (Nat.not_lt_zero i)
    | succ k ih =>
      intro i hik hin him
      by_contra hcon
      push Not at hcon
      have hqL : q i < L := hq1 i him
      obtain ⟨j, hjn, hj⟩ := (hr4 (q i) hqL).mp ((hq4 (q i) hqL).mpr ⟨i, him, rfl⟩)
      have hji : j < i := by
        by_contra hc
        push Not at hc
        rcases Nat.eq_or_lt_of_le hc with h' | h'
        · rw [← h'] at hj
          omega
        · have hlt := hr2 i j hjn.le h'
          omega
      have h1 : r j ≤ q j := ih j (by omega) (by omega) (by omega)
      have h2 : q j < q i := hq2 j i him.le hji
      omega
  intro i hin him
  exact main (i + 1) i (Nat.lt_succ_self i) hin him

private theorem strictMono_enumeration_unique_consolidated93 (hr1 : ∀ i, i < n → r i < L)
    (hr2 : ∀ i j : ℕ, j ≤ n → i < j → r i < r j)
    (hrn : r n = L)
    (hr4 : ∀ i, i < L → (P i ↔ ∃ j, j < n ∧ r j = i))
    (hq1 : ∀ i, i < m → q i < L)
    (hq2 : ∀ i j : ℕ, j ≤ m → i < j → q i < q j)
    (hqm : q m = L)
    (hq4 : ∀ i, i < L → (P i ↔ ∃ j, j < m ∧ q j = i)) :
    n = m ∧ ∀ i, i ≤ n → r i = q i := by
  have le1 := strictMono_enumeration_le_consolidated93 hr2 hq1 hq2 hr4 hq4
  have le2 := strictMono_enumeration_le_consolidated93 hq2 hr1 hr2 hq4 hr4
  have heq : ∀ i, i < n → i < m → r i = q i := fun i h1 h2 =>
    le_antisymm (le1 i h1 h2) (le2 i h2 h1)
  have hnm : n = m := by
    rcases lt_trichotomy n m with hlt | heqnm | hgt
    · exfalso
      have hqn : q n < L := hq1 n hlt
      obtain ⟨j, hjn, hj⟩ := (hr4 (q n) hqn).mp ((hq4 (q n) hqn).mpr ⟨n, hlt, rfl⟩)
      have ha : r j = q j := heq j hjn (hjn.trans hlt)
      have hb : q j < q n := hq2 j n hlt.le hjn
      omega
    · exact heqnm
    · exfalso
      have hrm : r m < L := hr1 m hgt
      obtain ⟨j, hjm, hj⟩ := (hq4 (r m) hrm).mp ((hr4 (r m) hrm).mpr ⟨m, hgt, rfl⟩)
      have ha : r j = q j := heq j (hjm.trans hgt) hjm
      have hb : r j < r m := hr2 j m hgt.le hjm
      omega
  refine ⟨hnm, ?_⟩
  intro i hi
  rcases Nat.eq_or_lt_of_le hi with h | h
  · rw [h, hrn, hnm, hqm]
  · exact heq i h (by omega)


end

namespace IsPullbackBlowupSequence

section
variable {X X' : Scheme.{u}} {φ : X' ⟶ X} {s : SequenceOfBlowups X} {s' s'' : SequenceOfBlowups X'} (h : IsPullbackBlowupSequence φ s' s)
include h

theorem of_isomorphic (e : s'.Isomorphic s'') : IsPullbackBlowupSequence φ s'' s := by
  obtain ⟨r, E, hr1, hr2, hr3, hr4, hfst, hstepE, hcen⟩ := h
  obtain ⟨hlen, ε, h0, hst, hc⟩ := e
  have hcl : ∀ i : ℕ, i ≤ s''.length → i ≤ s'.length := fun i hi => le_of_le_of_eq hi hlen.symm
  have hcl' : ∀ i : ℕ, i < s''.length → i < s'.length := fun i hi => lt_of_lt_of_eq hi hlen.symm
  have hproj := iso_hom_comp_projectionToBase_consolidated93 ε h0 hst
  refine ⟨r, fun i hi => (ε i (hcl i hi)).symm ≪≫ E i (hcl i hi),
    fun i hi => hr1 i (hcl' i hi), fun i j hj hij => hr2 i j (hcl j hj) hij,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hlen]; exact hr3
  · intro i hi
    rw [hr4 i hi, hlen]
  · intro i hi
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hfst i (hcl i hi)]
    rw [← hproj i (hcl i hi)]
    simp
  · intro i hi hr
    have h1 := hstepE i (hcl' i hi) hr
    have h2 := hst i (hcl' i hi)
    have key : s''.transitionMapSucc i ≫ (ε i (hcl i hi.le)).inv
        = (ε (i + 1) (hcl' i hi)).inv ≫ s'.transitionMapSucc i := by
      rw [← Iso.cancel_iso_hom_left (ε (i + 1) (hcl' i hi)), ← Category.assoc, h2]
      simp
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, key, Category.assoc, h1, Category.assoc]
  · intro i hi
    have h1 := hcen i (hcl' i hi)
    have h2 := hc i (hcl' i hi)
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [Scheme.IdealSheafData.comap_comp, ← h1, ← h2, ← Scheme.IdealSheafData.comap_comp,
      Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]

theorem isomorphic (h' : IsPullbackBlowupSequence φ s'' s) : s'.Isomorphic s'' := by
  obtain ⟨r, E, hr1, hr2, hr3, hr4, hfst, hstepE, hcen⟩ := h
  obtain ⟨q, G, hq1, hq2, hq3, hq4, gfst, gstep, gcen⟩ := h'
  obtain ⟨hnm, hall⟩ := strictMono_enumeration_unique_consolidated93 hr1 hr2 hr3 hr4 hq1 hq2 hq3 hq4
  refine ⟨hnm, fun i hi => E i hi ≪≫ pullbackProjectionToBaseIsoOfEq_consolidated93 φ s (hall i hi) ≪≫
    (G i (le_of_le_of_eq hi hnm)).symm, ?_, ?_, ?_⟩
  · have hG0 : (G 0 (le_of_le_of_eq (Nat.zero_le _) hnm)).inv ≫ s''.projectionToBase 0
        = Limits.pullback.fst φ (s.projectionToBase (q 0)) := by
      rw [← gfst 0 (le_of_le_of_eq (Nat.zero_le _) hnm)]
      simp
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← s''.projectionToBase_zero, hG0, pullbackIsoOfEq_hom_fst_consolidated93, hfst 0 (Nat.zero_le _),
      s'.projectionToBase_zero]
  · intro i hi
    have hr : r i ≤ r (i + 1) := (hr2 i (i + 1) hi (Nat.lt_succ_self i)).le
    have hq' : q i ≤ q (i + 1) :=
      (hq2 i (i + 1) (le_of_le_of_eq hi hnm) (Nat.lt_succ_self i)).le
    have h1 := hstepE i hi hr
    have h2 := gstep i (lt_of_lt_of_eq hi hnm) hq'
    have hGinv : (G (i + 1) (le_of_le_of_eq hi hnm)).inv ≫ s''.transitionMapSucc i
        = s.pullbackTransitionMap φ hq' ≫ (G i (le_of_le_of_eq (Nat.le_of_succ_le hi) hnm)).inv := by
      rw [← Iso.cancel_iso_hom_left (G (i + 1) (le_of_le_of_eq hi hnm)), ← Category.assoc,
        Iso.hom_inv_id, Category.id_comp, ← Category.assoc, ← h2]
      simp
    have htrans := pullbackIsoOfEq_hom_comp_pullbackTransitionMap_consolidated93 φ s (hall i (Nat.le_of_succ_le hi))
      (hall (i + 1) hi) hr hq'
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hGinv]
    rw [reassoc_of% h1, reassoc_of% htrans]
  · intro i hi
    have h1 := hcen i hi
    have h2 := gcen i (lt_of_lt_of_eq hi hnm)
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [h2, h1, ← Scheme.IdealSheafData.comap_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact comap_pullbackIsoOfEq_consolidated93 φ s (hall i (Nat.le_of_succ_le hi)) _


end

end IsPullbackBlowupSequence

end FunctorialResolution.EmbeddedResolution
end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceProduct
section

open TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

def homOfSumCoords {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u}) {X : Scheme.{u}}
    (f : X ⟶ AffineSpace n₁ S) (g : X ⟶ AffineSpace n₂ S) :
    X ⟶ AffineSpace n S :=
  AffineSpace.homOfVector (f ≫ AffineSpace n₁ S ↘ S)
    (fun i =>
      Sum.elim (fun a => f.appTop (AffineSpace.coord S a))
        (fun b => g.appTop (AffineSpace.coord S b)) (e.symm i))

@[simp]
theorem homOfSumCoords_appTop_coord_inl {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u})
    {X : Scheme.{u}} (f : X ⟶ AffineSpace n₁ S) (g : X ⟶ AffineSpace n₂ S) (a : n₁) :
    (homOfSumCoords e S f g).appTop (AffineSpace.coord S (e (Sum.inl a))) =
      f.appTop (AffineSpace.coord S a) := by
  simp [homOfSumCoords]

@[simp]
theorem homOfSumCoords_appTop_coord_inr {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u})
    {X : Scheme.{u}} (f : X ⟶ AffineSpace n₁ S) (g : X ⟶ AffineSpace n₂ S) (b : n₂) :
    (homOfSumCoords e S f g).appTop (AffineSpace.coord S (e (Sum.inr b))) =
      g.appTop (AffineSpace.coord S b) := by
  simp [homOfSumCoords]

section
variable {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u}) {X : Scheme.{u}} (f : X ⟶ AffineSpace n₁ S) (g : X ⟶ AffineSpace n₂ S)

private theorem homOfSumCoords_comp_reindex_inl_consolidated120 :
    homOfSumCoords e S f g ≫ AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)) = f := by
  refine AffineSpace.hom_ext ?_ (fun a => ?_)
  · simp [homOfSumCoords]
  · rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    simp

private theorem homOfSumCoords_comp_reindex_inr_consolidated120 (hfg : f ≫ (AffineSpace n₁ S ↘ S) = g ≫ (AffineSpace n₂ S ↘ S)) :
    homOfSumCoords e S f g ≫ AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b)) = g := by
  refine AffineSpace.hom_ext ?_ (fun b => ?_)
  · simpa [homOfSumCoords] using hfg
  · rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    simp


end

private theorem eq_homOfSumCoords_of_comp_reindex_consolidated120 {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u})
    {X : Scheme.{u}} (f : X ⟶ AffineSpace n₁ S) (g : X ⟶ AffineSpace n₂ S)
    (m : X ⟶ AffineSpace n S)
    (h₁ : m ≫ AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)) = f)
    (h₂ : m ≫ AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b)) = g) :
    m = homOfSumCoords e S f g := by
  refine AffineSpace.hom_ext ?_ (fun i => ?_)
  · have h : (m ≫ AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a))) ≫
        (AffineSpace n₁ S ↘ S) = f ≫ (AffineSpace n₁ S ↘ S) := by rw [h₁]
    simpa [homOfSumCoords] using h
  · obtain ⟨j, rfl⟩ : ∃ j, e j = i := ⟨e.symm i, e.apply_symm_apply i⟩
    obtain (a | b) := j
    · have h : (m ≫ AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a))).appTop
          (AffineSpace.coord S a) = f.appTop (AffineSpace.coord S a) := by rw [h₁]
      rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
      simpa using h
    · have h : (m ≫ AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b))).appTop
          (AffineSpace.coord S b) = g.appTop (AffineSpace.coord S b) := by rw [h₂]
      rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
      simpa using h

theorem isPullback_reindex_of_sumEquiv {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u}) :
    IsPullback
      (AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)))
      (AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b)))
      (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) := by
  have hcomm : CommSq
      (AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)))
      (AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b)))
      (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) := ⟨by simp⟩
  have hcond : Limits.pullback.fst (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) ≫
      (AffineSpace n₁ S ↘ S) =
      Limits.pullback.snd (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) ≫
      (AffineSpace n₂ S ↘ S) := Limits.pullback.condition
  have hA : homOfSumCoords e S
      (Limits.pullback.fst (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S))
      (Limits.pullback.snd (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S)) ≫
      AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)) =
      Limits.pullback.fst (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) :=
    homOfSumCoords_comp_reindex_inl_consolidated120 e S _ _
  have hB : homOfSumCoords e S
      (Limits.pullback.fst (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S))
      (Limits.pullback.snd (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S)) ≫
      AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b)) =
      Limits.pullback.snd (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) :=
    homOfSumCoords_comp_reindex_inr_consolidated120 e S _ _ hcond
  have hid : (𝟙 (AffineSpace n S)) = homOfSumCoords e S
      (AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)))
      (AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b))) :=
    eq_homOfSumCoords_of_comp_reindex_consolidated120 e S _ _ _ (Category.id_comp _) (Category.id_comp _)
  refine IsPullback.of_iso_pullback hcomm
    { hom := Limits.pullback.lift _ _ hcomm.w
      inv := homOfSumCoords e S
        (Limits.pullback.fst (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S))
        (Limits.pullback.snd (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S))
      hom_inv_id := ?_
      inv_hom_id := ?_ }
    (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)
  · rw [hid]
    refine eq_homOfSumCoords_of_comp_reindex_consolidated120 e S _ _ _ ?_ ?_
    · rw [Category.assoc, hA]
      exact Limits.pullback.lift_fst _ _ _
    · rw [Category.assoc, hB]
      exact Limits.pullback.lift_snd _ _ _
  · refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Limits.pullback.lift_fst, Category.id_comp]
      exact hA
    · rw [Category.assoc, Limits.pullback.lift_snd, Category.id_comp]
      exact hB

def sumUliftEquivUliftSum (n m : ℕ) :
    (ULift.{u} (Fin n) ⊕ ULift.{u} (Fin m)) ≃ ULift.{u} (Fin n ⊕ Fin m) where
  toFun := Sum.elim (fun a => ULift.up (Sum.inl a.down)) (fun b => ULift.up (Sum.inr b.down))
  invFun := fun i =>
    Sum.elim (fun a => Sum.inl (ULift.up a)) (fun b => Sum.inr (ULift.up b)) i.down
  left_inv := by rintro (⟨a⟩ | ⟨b⟩) <;> rfl
  right_inv := by rintro ⟨a | b⟩ <;> rfl

@[simp]
theorem sumUliftEquivUliftSum_inl (n m : ℕ) (a : Fin n) :
    sumUliftEquivUliftSum.{u} n m (Sum.inl (ULift.up a)) = ULift.up (Sum.inl a) := rfl

@[simp]
theorem sumUliftEquivUliftSum_inr (n m : ℕ) (b : Fin m) :
    sumUliftEquivUliftSum.{u} n m (Sum.inr (ULift.up b)) = ULift.up (Sum.inr b) := rfl

@[simp]
theorem sumUliftEquivUliftSum_symm_inl (n m : ℕ) (a : Fin n) :
    (sumUliftEquivUliftSum.{u} n m).symm (ULift.up (Sum.inl a)) = Sum.inl (ULift.up a) := rfl

@[simp]
theorem sumUliftEquivUliftSum_symm_inr (n m : ℕ) (b : Fin m) :
    (sumUliftEquivUliftSum.{u} n m).symm (ULift.up (Sum.inr b)) = Sum.inr (ULift.up b) := rfl

def projRight (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceIndexedBy k (ULift.{u} (Fin n ⊕ Fin m)) ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m)) :=
  AffineSpace.reindex (S := Spec (CommRingCat.of k))
    (fun j : ULift.{u} (Fin m) => (ULift.up (Sum.inr j.down) : ULift.{u} (Fin n ⊕ Fin m)))

def projLeft (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceIndexedBy k (ULift.{u} (Fin n ⊕ Fin m)) ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n)) :=
  AffineSpace.reindex (S := Spec (CommRingCat.of k))
    (fun j : ULift.{u} (Fin n) => (ULift.up (Sum.inl j.down) : ULift.{u} (Fin n ⊕ Fin m)))

@[simp]
theorem projRight_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (n m : ℕ) :
    projRight k n m ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin m)) =
      affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) := by
  simp [projRight]

@[simp]
theorem projRight_appTop_coord (k : Type u) [Field k] (n m : ℕ) (j : Fin m) :
    (projRight k n m).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) =
      AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up (Sum.inr j) : ULift.{u} (Fin n ⊕ Fin m)) := by
  simp [projRight]

@[simp]
theorem projLeft_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (n m : ℕ) :
    projLeft k n m ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) =
      affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) := by
  simp [projLeft]

@[simp]
theorem projLeft_appTop_coord (k : Type u) [Field k] (n m : ℕ) (j : Fin n) :
    (projLeft k n m).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) =
      AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up (Sum.inl j) : ULift.{u} (Fin n ⊕ Fin m)) := by
  simp [projLeft]

theorem isPullback_projLeft_projRight (k : Type u) [Field k] (n m : ℕ) :
    IsPullback (projLeft k n m) (projRight k n m)
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)))
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin m))) :=
  isPullback_reindex_of_sumEquiv (sumUliftEquivUliftSum.{u} n m) (Spec (CommRingCat.of k))

section
variable (hs : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] (n m : ℕ)
include hs

theorem smooth_projRight :
    Smooth (projRight k n m) :=
  MorphismProperty.of_isPullback (P := @Smooth)
    (isPullback_projLeft_projRight k n m) (hs k n)

theorem smooth_projLeft :
    Smooth (projLeft k n m) := by
  have hsm : Smooth (affineSpaceIndexedByToSpec k (ULift.{u} (Fin m))) := hs k m
  have hpb : IsPullback (projLeft k n m) (projRight k n m)
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)))
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin m))) :=
    isPullback_reindex_of_sumEquiv (sumUliftEquivUliftSum.{u} n m) (Spec (CommRingCat.of k))
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hsm


end

def prodMapOnPreimage (k : Type u) [Field k] (n m c : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens)
    (φ : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c))) :
    (projLeft k n m ⁻¹ᵁ U).toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c ⊕ Fin m)) :=
  AffineSpace.homOfVector
    ((projLeft k n m ⁻¹ᵁ U).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)))
    (fun i =>
      Sum.elim
        (fun a : Fin c =>
          (AlgebraicGeometry.morphismRestrict (projLeft k n m) U ≫ φ).appTop
            (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up a)))
        (fun b : Fin m =>
          ((projLeft k n m ⁻¹ᵁ U).ι).appTop
            (AffineSpace.coord (Spec (CommRingCat.of k))
              (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))))
        i.down)

section
variable (k : Type u) [Field k] (n m c : ℕ) (U : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens) (φ : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c)))

theorem prodMapOnPreimage_comp_affineSpaceIndexedByToSpec :
    prodMapOnPreimage k n m c U φ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c ⊕ Fin m)) =
      (projLeft k n m ⁻¹ᵁ U).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) := by
  simp [prodMapOnPreimage]

theorem prodMapOnPreimage_comp_projRight :
    prodMapOnPreimage k n m c U φ ≫ projRight k c m =
      (projLeft k n m ⁻¹ᵁ U).ι ≫ projRight k n m := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, projRight_comp_affineSpaceIndexedByToSpec, Category.assoc, projRight_comp_affineSpaceIndexedByToSpec, prodMapOnPreimage_comp_affineSpaceIndexedByToSpec]
  · rintro ⟨j⟩
    simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rw [projRight_appTop_coord, projRight_appTop_coord]
    simp [prodMapOnPreimage]

theorem morphismRestrict_projLeft_comp (hφ : φ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) =
      U.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n))) :
    AlgebraicGeometry.morphismRestrict (projLeft k n m) U ≫ φ =
      prodMapOnPreimage k n m c U φ ≫ projLeft k c m := by
  refine AffineSpace.hom_ext ?_ ?_
  · have h1 : (AlgebraicGeometry.morphismRestrict (projLeft k n m) U ≫ φ) ≫
        affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) =
        (projLeft k n m ⁻¹ᵁ U).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) := by
      rw [Category.assoc, hφ, morphismRestrict_ι_assoc, projLeft_comp_affineSpaceIndexedByToSpec]
    have h2 : (prodMapOnPreimage k n m c U φ ≫ projLeft k c m) ≫
        affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) =
        (projLeft k n m ⁻¹ᵁ U).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) := by
      rw [Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, prodMapOnPreimage_comp_affineSpaceIndexedByToSpec]
    exact h1.trans h2.symm
  · rintro ⟨j⟩
    have h : (prodMapOnPreimage k n m c U φ ≫ projLeft k c m).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) =
        (AlgebraicGeometry.morphismRestrict (projLeft k n m) U ≫ φ).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) := by
      rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply, projLeft_appTop_coord]
      simp [prodMapOnPreimage]
    exact h.symm

theorem isPullback_prodMapOnPreimage (hφ : φ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) =
      U.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n))) :
    IsPullback (prodMapOnPreimage k n m c U φ)
      (AlgebraicGeometry.morphismRestrict (projLeft k n m) U)
      (projLeft k c m) φ := by
  have hsq1 : IsPullback (AlgebraicGeometry.morphismRestrict (projLeft k n m) U)
      (projLeft k n m ⁻¹ᵁ U).ι U.ι (projLeft k n m) :=
    AlgebraicGeometry.isPullback_morphismRestrict (projLeft k n m) U
  have hstar := hsq1.paste_vert (isPullback_projLeft_projRight k n m)
  have hstar' : IsPullback (AlgebraicGeometry.morphismRestrict (projLeft k n m) U)
      (prodMapOnPreimage k n m c U φ ≫ projRight k c m)
      (φ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)))
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin m))) := by
    rw [prodMapOnPreimage_comp_projRight, hφ]
    exact hstar
  exact (hstar'.of_bot (morphismRestrict_projLeft_comp k n m c U φ hφ)
    (isPullback_projLeft_projRight k c m)).flip


end

theorem smooth_prodMapOnPreimage (_hs : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] (n m c : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens)
    (φ : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c)))
    [Smooth φ]
    (hφ : φ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) =
      U.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n))) :
    Smooth (prodMapOnPreimage k n m c U φ) := by
  have hsmooth : Smooth φ := ‹Smooth φ›
  exact MorphismProperty.of_isPullback (P := @Smooth)
    (isPullback_prodMapOnPreimage k n m c U φ hφ).flip hsmooth

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
section

open CategoryTheory.Limits

section
namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))

theorem locallyOfFiniteType_baseChangeToSpec [LocallyOfFiniteType p]
    (K : Type u) [Field K] [Algebra k K] :
    LocallyOfFiniteType (baseChangeToSpec p K) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback p (specMapAlgebraMap k K))
    (inferInstanceAs (LocallyOfFiniteType p))

theorem quasiCompact_baseChangeToSpec [QuasiCompact p]
    (K : Type u) [Field K] [Algebra k K] :
    QuasiCompact (baseChangeToSpec p K) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback p (specMapAlgebraMap k K))
    (inferInstanceAs (QuasiCompact p))

theorem smooth_baseChangeToSpec [Smooth p]
    (K : Type u) [Field K] [Algebra k K] :
    Smooth (baseChangeToSpec p K) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback p (specMapAlgebraMap k K))
    (inferInstanceAs (Smooth p))


end

structure EmbeddingDatum (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) where
  ambient : Scheme.{u}
  ambientStruct : ambient ⟶ Spec (CommRingCat.of k)
  emb : Y ⟶ ambient
  isAffine_ambient : IsAffine ambient
  smooth_ambientStruct : Smooth ambientStruct
  locallyOfFiniteType_ambientStruct : LocallyOfFiniteType ambientStruct
  quasiCompact_ambientStruct : QuasiCompact ambientStruct
  isClosedImmersion_emb : IsClosedImmersion emb
  nonzeroOnComponents_ker : NonzeroOnComponents emb.ker
  comp_eq : emb ≫ ambientStruct = p
  sncEmpty : InStrictNormalCrossingPosition ambientStruct ([] : List ambient.IdealSheafData)

namespace EmbeddingDatum

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
  {p : Y ⟶ Spec (CommRingCat.of k)}

instance instIsAffineAmbient (D : EmbeddingDatum k Y p) :
    IsAffine D.ambient := D.isAffine_ambient

instance instSmoothAmbientStruct (D : EmbeddingDatum k Y p) :
    Smooth D.ambientStruct := D.smooth_ambientStruct

instance instLocallyOfFiniteTypeAmbientStruct (D : EmbeddingDatum k Y p) :
    LocallyOfFiniteType D.ambientStruct :=
  D.locallyOfFiniteType_ambientStruct

instance instQuasiCompactAmbientStruct (D : EmbeddingDatum k Y p) :
    QuasiCompact D.ambientStruct := D.quasiCompact_ambientStruct

instance instIsClosedImmersionEmb (D : EmbeddingDatum k Y p) :
    IsClosedImmersion D.emb := D.isClosedImmersion_emb

end EmbeddingDatum

def embeddingDatumOfClosedImmersion {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (A : Scheme.{u}) [IsAffine A]
    (q : A ⟶ Spec (CommRingCat.of k)) [Smooth q]
    [LocallyOfFiniteType q] [QuasiCompact q]
    (e : Y ⟶ A) [IsClosedImmersion e]
    (hker : NonzeroOnComponents e.ker) (hcomp : e ≫ q = p)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A.IdealSheafData)) :
    EmbeddingDatum k Y p where
  ambient := A
  ambientStruct := q
  emb := e
  isAffine_ambient := inferInstance
  smooth_ambientStruct := inferInstance
  locallyOfFiniteType_ambientStruct := inferInstance
  quasiCompact_ambientStruct := inferInstance
  isClosedImmersion_emb := inferInstance
  nonzeroOnComponents_ker := hker
  comp_eq := hcomp
  sncEmpty := hsnc

namespace EmbeddingDatum

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
  {p : Y ⟶ Spec (CommRingCat.of k)}

private theorem pullbackCondition_baseChangeEmb_consolidated119 (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [Algebra k K] :
    (baseChangeProjection p K ≫ D.emb) ≫ D.ambientStruct =
      baseChangeToSpec p K ≫ specMapAlgebraMap k K := by
  rw [Category.assoc, D.comp_eq]
  exact pullback.condition

def baseChangeEmb (D : EmbeddingDatum k Y p) (K : Type u) [Field K] [Algebra k K] :
    baseChange p K ⟶ baseChange D.ambientStruct K :=
  pullback.lift (baseChangeProjection p K ≫ D.emb) (baseChangeToSpec p K)
    (pullbackCondition_baseChangeEmb_consolidated119 D K)

@[simp]
theorem baseChangeEmb_comp_baseChangeProjection (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [Algebra k K] :
    D.baseChangeEmb K ≫ baseChangeProjection D.ambientStruct K = baseChangeProjection p K ≫ D.emb :=
  pullback.lift_fst _ _ _

@[simp]
theorem baseChangeEmb_comp_baseChangeToSpec (D : EmbeddingDatum k Y p) (K : Type u)
    [Field K] [Algebra k K] :
    D.baseChangeEmb K ≫ baseChangeToSpec D.ambientStruct K = baseChangeToSpec p K :=
  pullback.lift_snd _ _ _

section
variable (D : EmbeddingDatum k Y p) (K : Type u) [Field K] [Algebra k K]

theorem isPullback_baseChangeEmb :
    IsPullback (D.baseChangeEmb K) (baseChangeProjection p K) (baseChangeProjection D.ambientStruct K)
      D.emb := by
  have hbig : IsPullback (D.baseChangeEmb K ≫ baseChangeToSpec D.ambientStruct K)
      (baseChangeProjection p K) (specMapAlgebraMap k K) (D.emb ≫ D.ambientStruct) := by
    rw [baseChangeEmb_comp_baseChangeToSpec D K, D.comp_eq]
    exact (IsPullback.of_hasPullback p (specMapAlgebraMap k K)).flip
  exact IsPullback.of_right hbig (baseChangeEmb_comp_baseChangeProjection D K)
    (IsPullback.of_hasPullback D.ambientStruct (specMapAlgebraMap k K)).flip

theorem isClosedImmersion_baseChangeEmb : IsClosedImmersion (D.baseChangeEmb K) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_baseChangeEmb D K).flip D.isClosedImmersion_emb


end

instance instIsClosedImmersionBaseChangeEmb (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [Algebra k K] : IsClosedImmersion (D.baseChangeEmb K) :=
  isClosedImmersion_baseChangeEmb D K

section
variable (D : EmbeddingDatum k Y p) (K : Type u) [Field K] [Algebra k K]

theorem isAffine_baseChange_ambientToSpec : IsAffine (baseChange D.ambientStruct K) :=
  isAffine_baseChange D.ambientStruct K

theorem smooth_baseChangeToSpec_ambientToSpec :
    Smooth (baseChangeToSpec D.ambientStruct K) :=
  smooth_baseChangeToSpec D.ambientStruct K

theorem locallyOfFiniteType_baseChangeToSpec_ambientToSpec :
    LocallyOfFiniteType (baseChangeToSpec D.ambientStruct K) :=
  locallyOfFiniteType_baseChangeToSpec D.ambientStruct K

theorem quasiCompact_baseChangeToSpec_ambientToSpec :
    QuasiCompact (baseChangeToSpec D.ambientStruct K) :=
  quasiCompact_baseChangeToSpec D.ambientStruct K


end

def baseChange (D : EmbeddingDatum k Y p) (K : Type u) [Field K] [CharZero K]
    [Algebra k K]
    (hker : NonzeroOnComponents (D.baseChangeEmb K).ker)
    (hsnc : InStrictNormalCrossingPosition (baseChangeToSpec D.ambientStruct K)
      ([] : List (EmbeddedResolution.baseChange D.ambientStruct K).IdealSheafData)) :
    EmbeddingDatum K (EmbeddedResolution.baseChange p K) (baseChangeToSpec p K) where
  ambient := EmbeddedResolution.baseChange D.ambientStruct K
  ambientStruct := baseChangeToSpec D.ambientStruct K
  emb := D.baseChangeEmb K
  isAffine_ambient := isAffine_baseChange_ambientToSpec D K
  smooth_ambientStruct := smooth_baseChangeToSpec_ambientToSpec D K
  locallyOfFiniteType_ambientStruct := locallyOfFiniteType_baseChangeToSpec_ambientToSpec D K
  quasiCompact_ambientStruct := quasiCompact_baseChangeToSpec_ambientToSpec D K
  isClosedImmersion_emb := isClosedImmersion_baseChangeEmb D K
  nonzeroOnComponents_ker := hker
  comp_eq := baseChangeEmb_comp_baseChangeToSpec D K
  sncEmpty := hsnc

end EmbeddingDatum

abbrev EmbeddedResolutionRule : Type (u + 1) :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y], EmbeddingDatum k Y p → SequenceOfBlowups Y

abbrev EmbeddingChoice : Type (u + 1) :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y], EmbeddingDatum k Y p

def EmbeddedResolutionRule.toAffineResolutionRule (R : EmbeddedResolutionRule.{u}) (S : EmbeddingChoice.{u}) :
    AffineResolutionRule.{u} :=
  fun k _ _ Y p _ _ _ _ => R k Y p (S k Y p)

@[simp]
theorem EmbeddedResolutionRule.toAffineResolutionRule_apply (R : EmbeddedResolutionRule.{u}) (S : EmbeddingChoice.{u})
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y] :
    R.toAffineResolutionRule S k Y p = R k Y p (S k Y p) := rfl

def EmbeddedResolutionRule.HasProperCenters (R : EmbeddedResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y] (D : EmbeddingDatum k Y p) (i : ℕ),
    i < (R k Y p D).length → (R k Y p D).center i ≠ ⊤

def EmbeddedResolutionRule.IsCompatibleWithSmoothAmbientMaps (R : EmbeddedResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y Y' : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) (p' : Y' ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [QuasiCompact p]
    [IsReduced Y] [IsAffine Y]
    [LocallyOfFiniteType p'] [QuasiCompact p']
    [IsReduced Y'] [IsAffine Y']
    (D : EmbeddingDatum k Y p) (D' : EmbeddingDatum k Y' p')
    (φ : D'.ambient ⟶ D.ambient) [Smooth φ] (ψ : Y' ⟶ Y),
    φ ≫ D.ambientStruct = D'.ambientStruct →
    IsPullback D'.emb ψ φ D.emb →
    IsPullbackBlowupSequence ψ (R k Y' p' D') (R k Y p D)

def EmbeddedResolutionRule.IsCompatibleWithFieldBaseChange (R : EmbeddedResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y] (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [CharZero K] [Algebra k K] [IsReduced (baseChange p K)]
    (hker : NonzeroOnComponents (D.baseChangeEmb K).ker)
    (hsnc : InStrictNormalCrossingPosition (baseChangeToSpec D.ambientStruct K)
      ([] : List (baseChange D.ambientStruct K).IdealSheafData)),
    haveI : IsAffine (baseChange p K) := isAffine_baseChange p K
    haveI : LocallyOfFiniteType (baseChangeToSpec p K) :=
      locallyOfFiniteType_baseChangeToSpec p K
    haveI : QuasiCompact (baseChangeToSpec p K) :=
      quasiCompact_baseChangeToSpec p K
    IsStrictPullbackBlowupSeq (baseChangeProjection p K)
      (R K (baseChange p K) (baseChangeToSpec p K) (D.baseChange K hker hsnc))
      (R k Y p D)

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ClosedEmbeddingIntoAffineSpace
section


section
namespace FunctorialResolution.EmbeddedResolution

structure ClosedEmbeddingIntoAffineSpace {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) where
  codimBound : ℕ
  dim : ℕ
  toAffine : G.ambient ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin dim))
  one_le_codimBound : 1 ≤ codimBound
  one_le_dim : 1 ≤ dim
  isClosedImmersion_toAffine : IsClosedImmersion toAffine
  toAffine_comp : toAffine ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin dim)) = G.ambientStruct
  locallyConstCodim :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u} (Fin dim))) toAffine codimBound

namespace ClosedEmbeddingIntoAffineSpace

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
  {p : Y ⟶ Spec (CommRingCat.of k)} {G : EmbeddingDatum k Y p}

instance instIsClosedImmersionToAffine (P : ClosedEmbeddingIntoAffineSpace G) :
    IsClosedImmersion P.toAffine :=
  P.isClosedImmersion_toAffine

end ClosedEmbeddingIntoAffineSpace

def EmbeddedResolutionRule.IsIndependentOfPresentedEmbedding (R : EmbeddedResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y] (D D' : EmbeddingDatum k Y p),
    ClosedEmbeddingIntoAffineSpace D → ClosedEmbeddingIntoAffineSpace D' →
    (R k Y p D).Isomorphic (R k Y p D')

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ExtendCoordinatesToAffineSpace
section

open TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

def specHomOfGlobalSections (A : Scheme.{u}) [IsAffine A] {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') : Spec B' ⟶ A :=
  Spec.map σ ≫ A.isoSpec.inv

@[simp]
theorem specHomOfGlobalSections_appTop (A : Scheme.{u}) [IsAffine A]
    {B' : CommRingCat.{u}} (σ : Γ(A, ⊤) ⟶ B') (s : Γ(A, ⊤)) :
    (specHomOfGlobalSections A σ).appTop s = (Scheme.ΓSpecIso B').inv (σ s) := by
  have hcomp : specHomOfGlobalSections A σ ≫ A.isoSpec.hom = Spec.map σ := by
    simp [specHomOfGlobalSections]
  have h : (Scheme.ΓSpecIso Γ(A, ⊤)).hom ≫ (specHomOfGlobalSections A σ).appTop
      = (Spec.map σ).appTop := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop, hcomp]
  have h3 : (specHomOfGlobalSections A σ).appTop = σ ≫ (Scheme.ΓSpecIso B').inv := by
    rw [← cancel_epi (Scheme.ΓSpecIso Γ(A, ⊤)).hom, Scheme.ΓSpecIso_inv_naturality,
      Iso.hom_inv_id_assoc]
    exact h
  rw [h3, CommRingCat.comp_apply]

def specToAffineSpaceExtendCoords (k : Type u) [Field k] (A : Scheme.{u}) [IsAffine A]
    (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B') :
    Spec B' ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n)) :=
  AffineSpace.homOfVector (specHomOfGlobalSections A σ ≫ pA)
    (fun i =>
      Sum.elim
        (fun a : Fin M =>
          (specHomOfGlobalSections A σ ≫ e).appTop
            (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up a)))
        (fun j : Fin n => (Scheme.ΓSpecIso B').inv (b j))
        i.down)

@[simp]
theorem specToAffineSpaceExtendCoords_comp_toSpec (k : Type u) [Field k] (A : Scheme.{u})
    [IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B') :
    specToAffineSpaceExtendCoords k A pA M e σ n b ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M ⊕ Fin n)) =
      specHomOfGlobalSections A σ ≫ pA := by
  simp [specToAffineSpaceExtendCoords]

@[simp]
theorem specToAffineSpaceExtendCoords_appTop_coord_inl (k : Type u) [Field k] (A : Scheme.{u})
    [IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B') (a : Fin M) :
    (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inl a) : ULift.{u} (Fin M ⊕ Fin n))) =
      (specHomOfGlobalSections A σ ≫ e).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up a)) := by
  simp [specToAffineSpaceExtendCoords]

@[simp]
theorem specToAffineSpaceExtendCoords_appTop_coord_inr (k : Type u) [Field k] (A : Scheme.{u})
    [IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B') (j : Fin n) :
    (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n))) =
      (Scheme.ΓSpecIso B').inv (b j) := by
  simp [specToAffineSpaceExtendCoords]

theorem specToAffineSpaceExtendCoords_comp_projLeft (k : Type u) [Field k] (A : Scheme.{u})
    [IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B')
    (he : e ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) = pA) :
    specToAffineSpaceExtendCoords k A pA M e σ n b ≫ projLeft k M n = specHomOfGlobalSections A σ ≫ e := by
  refine AffineSpace.hom_ext ?_ ?_
  · simp [he]
  · rintro ⟨a⟩
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, projLeft_appTop_coord,
      specToAffineSpaceExtendCoords_appTop_coord_inl]

section
variable (k : Type u) [Field k] (A : Scheme.{u}) [IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ) (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) [IsClosedImmersion e] {B' : CommRingCat.{u}} (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B') (he : e ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) = pA) (hgen : ∀ x : B', ∃ p : MvPolynomial (Fin n) Γ(A, ⊤), MvPolynomial.eval₂ σ.hom b p = x)
include he hgen

theorem specToAffineSpaceExtendCoords_appTop_surjective :
    Function.Surjective ⇑((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop) := by
  have hsurj : Function.Surjective ⇑(e.appTop) :=
    (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine e).2
  have hproj : specToAffineSpaceExtendCoords k A pA M e σ n b ≫ projLeft k M n
      = specHomOfGlobalSections A σ ≫ e := specToAffineSpaceExtendCoords_comp_projLeft k A pA M e σ n b he
  have hsec : ∀ s : Γ(A, ⊤), ∃ P, (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop P
      = (Scheme.ΓSpecIso B').inv (σ s) := by
    intro s
    obtain ⟨P, hPs⟩ := hsurj s
    refine ⟨(projLeft k M n).appTop P, ?_⟩
    have h2 := congrArg
      (fun g : Spec B' ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M)) => g.appTop P) hproj
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h2
    rw [h2, hPs, specHomOfGlobalSections_appTop]
  have key : ∀ p : MvPolynomial (Fin n) Γ(A, ⊤), ∃ P,
      (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop P
        = (Scheme.ΓSpecIso B').inv (MvPolynomial.eval₂ σ.hom b p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C s =>
        obtain ⟨P, hP⟩ := hsec s
        refine ⟨P, ?_⟩
        rw [MvPolynomial.eval₂_C]
        exact hP
    | add p q hp hq =>
        obtain ⟨P, hP⟩ := hp
        obtain ⟨Q, hQ⟩ := hq
        refine ⟨P + Q, ?_⟩
        rw [map_add, MvPolynomial.eval₂_add, map_add, hP, hQ]
    | mul_X p j hp =>
        obtain ⟨P, hP⟩ := hp
        refine ⟨P * AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n)), ?_⟩
        rw [map_mul, hP, specToAffineSpaceExtendCoords_appTop_coord_inr, MvPolynomial.eval₂_mul,
          MvPolynomial.eval₂_X, map_mul]
  intro y
  obtain ⟨p, hp⟩ := hgen ((Scheme.ΓSpecIso B').hom y)
  obtain ⟨P, hP⟩ := key p
  refine ⟨P, ?_⟩
  rw [hP, hp]
  simp

theorem isClosedImmersion_specToAffineSpaceExtendCoords :
    IsClosedImmersion (specToAffineSpaceExtendCoords k A pA M e σ n b) :=
  AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine _
    (specToAffineSpaceExtendCoords_appTop_surjective k A pA M e σ n b he hgen)


end

end FunctorialResolution.EmbeddedResolution

end
end

-- Source: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphChart
section

open TopologicalSpace

section
namespace FunctorialResolution.EmbeddedResolution

def graphMorphismToAffineSpace (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (D : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens) :
    D.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin q)) :=
  AffineSpace.homOfVector
    (D.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin n)))
    (fun i =>
      Sum.elim
        (fun a : Fin M =>
          (ConcreteCategory.hom (Scheme.Hom.appTop D.ι))
            (AffineSpace.coord (Spec (CommRingCat.of k))
              (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin n))))
        (fun j : Fin q => (ConcreteCategory.hom (Scheme.Hom.appTop D.ι)) (F j))
        i.down)

section
variable (k : Type u) [Field k] (M n q : ℕ) (F : Fin q → ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤))) (D : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens)

theorem graphMorphismToAffineSpace_comp_affineSpaceIndexedByToSpec :
    graphMorphismToAffineSpace k M n q F D ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin q)) =
      D.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin n)) := by
  simp [graphMorphismToAffineSpace]

theorem graphMorphismToAffineSpace_appTop_coord_inl (a : Fin M) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (graphMorphismToAffineSpace k M n q F D)))
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin q))) =
      (ConcreteCategory.hom (Scheme.Hom.appTop D.ι))
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin n))) := by
  simp [graphMorphismToAffineSpace]

theorem graphMorphismToAffineSpace_appTop_coord_inr (j : Fin q) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (graphMorphismToAffineSpace k M n q F D)))
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inr j) : ULift.{u, 0} (Fin M ⊕ Fin q))) =
      (ConcreteCategory.hom (Scheme.Hom.appTop D.ι)) (F j) := by
  simp [graphMorphismToAffineSpace]


end

def SmoothPullbackHasGraphChart : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X Y A : Scheme.{u})
    (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of k))
    (pA : A ⟶ Spec (CommRingCat.of k)) [IsAffine A] [Smooth pA]
    [LocallyOfFiniteType pA] [QuasiCompact pA]
    (i : X ⟶ A) [IsClosedImmersion i], i ≫ pA = pX →
    ∀ (M : ℕ) (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ],
      ρ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) = pA →
    ∀ (r : ℕ) (h : Y ⟶ X) [SmoothOfRelativeDimension r h], h ≫ pX = pY →
    ∀ y : Y,
      ∃ (V : Y.Opens) (_ : y ∈ V) (_ : IsAffineOpen V)
        (A' : Scheme.{u}) (pA' : A' ⟶ Spec (CommRingCat.of k)),
        IsAffine A' ∧ Smooth pA' ∧ LocallyOfFiniteType pA' ∧ QuasiCompact pA' ∧
        ∃ g : A' ⟶ A, Smooth g ∧ g ≫ pA = pA' ∧
          ∃ j : V.toScheme ⟶ A', IsClosedImmersion j ∧
            IsPullback j (V.ι ≫ h) g i ∧
            ∃ (n q : ℕ), n = q + r ∧
              ∃ σ : A' ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n)),
                IsClosedImmersion σ ∧
                σ ≫ projLeft k M n = g ≫ ρ ∧
                ∃ (F : Fin q →
                    ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj
                      (Opposite.op ⊤)))
                  (Δ : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj
                      (Opposite.op ⊤))),
                  RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop σ)) =
                      Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appTop (projLeft k M n)))
                        (RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop ρ))) ⊔
                      Ideal.span (Set.range F) ∧
                  σ ⁻¹ᵁ ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ) = ⊤ ∧
                  Smooth (graphMorphismToAffineSpace k M n q F
                    ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ))

end FunctorialResolution.EmbeddedResolution

end
end
end
