/-
# Diagonal positive spatial translations on the SAME union carrier

Translate each of the three spatial coordinates by one supplied natural s.
The target support guard is enlarged from b to b+2*s. This spare padding
makes recentering at r exactly the old recentering at r+s, in the same
finite box. A cofinal shift of the existing spatial limit therefore proves
preservation of its actual reflected pairing and squared distance.

This is a positive diagonal Nat action, not the full signed Z^3 translation
group, a change of lattice spacing, or a continuum symmetry theorem.
-/

import YMGap.Continuum.BF4SpatialUnionPairingData

namespace YMGap.Continuum.BF4SpatialUnionDiagonalTranslation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnion
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm (radius DistanceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (physicalTime unit zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe (translateSpan_comp)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits (jointPairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm (jointDistSq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

private theorem equiv_of_eq {a b : CReal} (h : a=b) : Equiv a b := by
  cases h
  exact Equiv.refl _

/-- A support-safe translation with exactly the padding needed by the old limit. -/
def translate {base : Nat} (s : Nat) (x : PhysicalSpan base) : PhysicalSpan (base+2*s) :=
  ⟨translateSpan s x.val, translateSpan_physical (by omega) x.val x.property⟩

theorem translate_radius {base : Nat} (s : Nat) (x : PhysicalSpan base) :
    radius (translate s x).val = radius x.val := radius_translate s x.val

theorem translate_time {base : Nat} (s n : Nat) (x : PhysicalSpan base) :
    translate s (physicalTime n x) = physicalTime n (translate s x) :=
  Subtype.ext (translateSpan_advance s n x.val)

theorem translate_unit (base s : Nat) : translate s (unit base) = unit (base+2*s) := rfl
theorem translate_zero (base s : Nat) : translate s (zero base) = zero (base+2*s) := rfl

/-- The exact spare-padding identity; no comparison estimate is needed. -/
theorem translated_paddedWidth (base s r : Nat) :
    paddedWidth (base+2*s) r = paddedWidth base (r+s) := by
  unfold paddedWidth
  omega

theorem recenter_translate_val {base : Nat} (s r : Nat) (x : PhysicalSpan base) :
    (recenter r (translate s x)).val = (recenter (r+s) x).val := by
  change translateSpan (r+1) (translateSpan s x.val) = translateSpan (r+s+1) x.val
  rw [translateSpan_comp, show s+(r+1)=r+s+1 by omega]

private theorem converges_add_shift {f : Nat → CReal} {l : CReal}
    (h : ConvergesTo f l) (s : Nat) : ConvergesTo (fun n => f (n+s)) l := by
  intro epsilon he
  obtain ⟨N, hN⟩ := h epsilon he
  exact ⟨N, fun n hn => hN (n+s) (by omega)⟩

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

private theorem jointPairing_congr_width {a b : Nat} (hab : a=b)
    (x y : PhysicalSpan a) (x' y' : PhysicalSpan b)
    (hx : x.val=x'.val) (hy : y.val=y'.val) :
    jointPairing hw0 hw1 a x y = jointPairing hw0 hw1 b x' y' := by
  cases hab
  have hxx : x=x' := Subtype.ext hx
  have hyy : y=y' := Subtype.ext hy
  rw [hxx, hyy]

private theorem jointDistSq_congr_width {a b : Nat} (hab : a=b)
    (x y : PhysicalSpan a) (x' y' : PhysicalSpan b)
    (hx : x.val=x'.val) (hy : y.val=y'.val) :
    jointDistSq hw0 hw1 a x y = jointDistSq hw0 hw1 b x' y' := by
  cases hab
  have hxx : x=x' := Subtype.ext hx
  have hyy : y=y' := Subtype.ext hy
  rw [hxx, hyy]

/-- The translated finite-width joint pairings are the literal cofinal old sequence. -/
theorem jointPairing_recenter_translate {base : Nat} (s r : Nat) (x y : PhysicalSpan base) :
    jointPairing hw0 hw1 (paddedWidth (base+2*s) r)
      (recenter r (translate s x)) (recenter r (translate s y)) =
    jointPairing hw0 hw1 (paddedWidth base (r+s))
      (recenter (r+s) x) (recenter (r+s) y) :=
  jointPairing_congr_width hw0 hw1 (translated_paddedWidth base s r)
    _ _ _ _ (recenter_translate_val s r x) (recenter_translate_val s r y)

/-- Actual limiting reflected pairing invariance, not a new pairing definition. -/
theorem spatialPairing_translate {base : Nat} (hb : 0<base) (s : Nat)
    (x y : PhysicalSpan base) :
    Equiv (spatialPairing hw0 hw1 (base+2*s) hsmall hd hs (by omega)
      (translate s x) (translate s y))
      (spatialPairing hw0 hw1 base hsmall hd hs hb x y) :=
  Equiv_of_limit_of_equal
    (fun r => equiv_of_eq (jointPairing_recenter_translate hw0 hw1 s r x y))
    (spatialPairing_converges hw0 hw1 (base+2*s) hsmall hd hs (by omega)
      (translate s x) (translate s y))
    (converges_add_shift (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x y) s)

theorem spatialDistSq_translate {base : Nat} (hb : 0<base) (s : Nat)
    (x y : PhysicalSpan base) :
    Equiv (spatialDistSq hw0 hw1 (base+2*s) hsmall hd hs (by omega)
      (translate s x) (translate s y))
      (spatialDistSq hw0 hw1 base hsmall hd hs hb x y) :=
  Equiv_of_limit_of_equal
    (fun r => equiv_of_eq (jointDistSq_congr_width hw0 hw1 (translated_paddedWidth base s r)
      _ _ _ _ (recenter_translate_val s r x) (recenter_translate_val s r y)))
    (distSq_converges_spatial hw0 hw1 (base+2*s) hsmall hd hs (by omega)
      (translate s x) (translate s y))
    (converges_add_shift (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb x y) s)

/-- Literal diagonal translation of the original words, with a computed new support guard. -/
def stageTranslate (s : Nat) (x : Stage) : Stage :=
  ⟨x.base+2*s, by have := x.positive; omega, translate s x.value⟩

private theorem stage_eq_of_values {x y : Stage} (hbase : x.base=y.base)
    (hvalue : x.value.val=y.value.val) : x=y := by
  cases x with
  | mk a ha xa =>
    cases y with
    | mk b hb yb =>
      dsimp at hbase hvalue
      cases hbase
      have hxy : xa=yb := Subtype.ext hvalue
      cases hxy
      rfl

theorem translateSpan_zero (xs : DistanceSpan) : translateSpan 0 xs = xs := by
  have hf : translateFactor 0 = id := by
    funext f
    obtain ⟨⟨⟨a, b, c, d⟩, plane⟩, j⟩ := f
    simp [translateFactor, BF4ExactSlabBulkEmbeddingGeometry.shiftFace,
      BF4ExactSlabBulkEmbeddingGeometry.shiftVertex]
  simp [translateSpan, translateSchedule, hf]

theorem stageTranslate_zero (x : Stage) : stageTranslate 0 x = x :=
  stage_eq_of_values (by simp [stageTranslate]) (translateSpan_zero x.value.val)

theorem stageTranslate_add (m n : Nat) (x : Stage) :
    stageTranslate (m+n) x = stageTranslate m (stageTranslate n x) := by
  apply stage_eq_of_values
  · simp only [stageTranslate]
    omega
  · change translateSpan (m+n) x.value.val = translateSpan m (translateSpan n x.value.val)
    rw [translateSpan_comp, Nat.add_comm m n]

theorem stageTranslate_time (s n : Nat) (x : Stage) :
    stageTranslate s (time n x) = time n (stageTranslate s x) := by
  simp only [stageTranslate, time, translate_time]

theorem stageTranslate_atBase (s : Nat) (x : Stage) {larger : Nat} (h : x.base≤larger) :
    atBase (stageTranslate s x) (Nat.add_le_add_right h (2*s)) = translate s (atBase x h) :=
  Subtype.ext rfl

/-- Pairing preservation at the computed common base of two unrelated presentations. -/
theorem pairing_translate (s : Nat) (x y : Stage) :
    Equiv (pairing hw0 hw1 hsmall hd hs (stageTranslate s x) (stageTranslate s y))
      (pairing hw0 hw1 hsmall hd hs x y) := by
  let base := max x.base y.base
  have hx : x.base≤base := Nat.le_max_left _ _
  have hy : y.base≤base := Nat.le_max_right _ _
  have hleft := pairing_at_base hw0 hw1 hsmall hd hs (stageTranslate s x) (stageTranslate s y)
    (base+2*s) (Nat.add_le_add_right hx (2*s)) (Nat.add_le_add_right hy (2*s))
  rw [stageTranslate_atBase s x hx, stageTranslate_atBase s y hy] at hleft
  exact hleft.trans ((spatialPairing_translate hw0 hw1 hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive hx) s (atBase x hx) (atBase y hy)).trans
      (pairing_at_base hw0 hw1 hsmall hd hs x y base hx hy).symm)

theorem distSq_translate (s : Nat) (x y : Stage) :
    Equiv (distSq hw0 hw1 hsmall hd hs (stageTranslate s x) (stageTranslate s y))
      (distSq hw0 hw1 hsmall hd hs x y) := by
  let base := max x.base y.base
  have hx : x.base≤base := Nat.le_max_left _ _
  have hy : y.base≤base := Nat.le_max_right _ _
  have hleft := distSq_at_base hw0 hw1 hsmall hd hs (stageTranslate s x) (stageTranslate s y)
    (base+2*s) (Nat.add_le_add_right hx (2*s)) (Nat.add_le_add_right hy (2*s))
  rw [stageTranslate_atBase s x hx, stageTranslate_atBase s y hy] at hleft
  exact hleft.trans ((spatialDistSq_translate hw0 hw1 hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive hx) s (atBase x hx) (atBase y hy)).trans
      (distSq_at_base hw0 hw1 hsmall hd hs x y base hx hy).symm)

/-- The existing generic completion map consumes this proved SAME-distance bound. -/
def translationNonexpansive (s : Nat) :
    (unionSeminorm hw0 hw1 hsmall hd hs).Nonexpansive where
  toFun := stageTranslate s
  contraction := fun x y => leEv_of_equiv (distSq_translate hw0 hw1 hsmall hd hs s x y)

def translationSemigroup : (unionSeminorm hw0 hw1 hsmall hd hs).NonexpansiveSemigroup where
  op := translationNonexpansive hw0 hw1 hsmall hd hs
  zero_law := by
    intro x
    change Equiv (distSq hw0 hw1 hsmall hd hs (stageTranslate 0 x) x) czero
    rw [stageTranslate_zero]
    exact distance_refl hw0 hw1 hsmall hd hs x
  add_law := by
    intro m n x
    change Equiv (distSq hw0 hw1 hsmall hd hs (stageTranslate (m+n) x)
      (stageTranslate m (stageTranslate n x))) czero
    rw [stageTranslate_add]
    exact distance_refl hw0 hw1 hsmall hd hs _

def completedTranslation (s : Nat) : UnionCompletion hw0 hw1 hsmall hd hs →
    UnionCompletion hw0 hw1 hsmall hd hs :=
  (translationNonexpansive hw0 hw1 hsmall hd hs s).completionMap

theorem translation_cauchy_modulus (s : Nat) (X : (unionSeminorm hw0 hw1 hsmall hd hs).Cauchy) :
    ((translationNonexpansive hw0 hw1 hsmall hd hs s).mapCauchy X).modulus = X.modulus := rfl

theorem completedTranslation_embedStage (s : Nat) (x : Stage) :
    completedTranslation hw0 hw1 hsmall hd hs s (embedStage hw0 hw1 hsmall hd hs x) =
      embedStage hw0 hw1 hsmall hd hs (stageTranslate s x) := rfl

theorem completedTranslation_zero (x : UnionCompletion hw0 hw1 hsmall hd hs) :
    completedTranslation hw0 hw1 hsmall hd hs 0 x = x :=
  (translationSemigroup hw0 hw1 hsmall hd hs).completionMap_zero x

theorem completedTranslation_add (m n : Nat) (x : UnionCompletion hw0 hw1 hsmall hd hs) :
    completedTranslation hw0 hw1 hsmall hd hs (m+n) x =
      completedTranslation hw0 hw1 hsmall hd hs m
        (completedTranslation hw0 hw1 hsmall hd hs n x) :=
  (translationSemigroup hw0 hw1 hsmall hd hs).completionMap_add m n x

theorem completedTranslation_time (s n : Nat) (x : UnionCompletion hw0 hw1 hsmall hd hs) :
    completedTranslation hw0 hw1 hsmall hd hs s (completedTime hw0 hw1 hsmall hd hs n x) =
      completedTime hw0 hw1 hsmall hd hs n (completedTranslation hw0 hw1 hsmall hd hs s x) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  refine ⟨CRealSeminormCompletion.SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun k => ?_)⟩
  change Equiv (distSq hw0 hw1 hsmall hd hs (stageTranslate s (time n (X.seq k)))
    (time n (stageTranslate s (X.seq k)))) czero
  rw [stageTranslate_time]
  exact distance_refl hw0 hw1 hsmall hd hs _

theorem stageTranslate_unit_null (s : Nat) :
    Equiv (distSq hw0 hw1 hsmall hd hs (stageTranslate s unitStage) unitStage) czero := by
  have h := distSq_at_base hw0 hw1 hsmall hd hs (stageTranslate s unitStage) unitStage
    (1+2*s) (Nat.le_refl _) (by change 1≤1+2*s; omega)
  change Equiv (distSq hw0 hw1 hsmall hd hs (stageTranslate s unitStage) unitStage)
    (spatialDistSq hw0 hw1 (1+2*s) hsmall hd hs (by omega)
      (unit (1+2*s)) (unit (1+2*s))) at h
  exact h.trans (spatialDistSq_refl hw0 hw1 (1+2*s) hsmall hd hs (by omega) _)

theorem completedTranslation_unit (s : Nat) :
    completedTranslation hw0 hw1 hsmall hd hs s (completedUnit hw0 hw1 hsmall hd hs) =
      completedUnit hw0 hw1 hsmall hd hs := by
  apply Quotient.sound
  exact ⟨CRealSeminormCompletion.SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun _ => stageTranslate_unit_null hw0 hw1 hsmall hd hs s)⟩

theorem completedInner_translate (s : Nat) (x y : UnionCompletion hw0 hw1 hsmall hd hs) :
    BF4SpatialUnionPairingData.completedInner hw0 hw1 hsmall hd hs
      (completedTranslation hw0 hw1 hsmall hd hs s x)
      (completedTranslation hw0 hw1 hsmall hd hs s y) =
    BF4SpatialUnionPairingData.completedInner hw0 hw1 hsmall hd hs x y := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  apply Quotient.sound
  exact Equiv_of_limit_of_equal
    (fun k => pairing_translate hw0 hw1 hsmall hd hs s (X.seq k) (Y.seq k))
    (CRealSeminormPairingCompletion.pairSequence_converges
      (BF4SpatialUnionPairingData.pairingData hw0 hw1 hsmall hd hs)
      ((translationNonexpansive hw0 hw1 hsmall hd hs s).mapCauchy X)
      ((translationNonexpansive hw0 hw1 hsmall hd hs s).mapCauchy Y))
    (CRealSeminormPairingCompletion.pairSequence_converges
      (BF4SpatialUnionPairingData.pairingData hw0 hw1 hsmall hd hs) X Y)

#print axioms translate
#print axioms translate_radius
#print axioms translate_time
#print axioms translate_unit
#print axioms translate_zero
#print axioms translated_paddedWidth
#print axioms recenter_translate_val
#print axioms jointPairing_recenter_translate
#print axioms spatialPairing_translate
#print axioms spatialDistSq_translate
#print axioms stageTranslate
#print axioms translateSpan_zero
#print axioms stageTranslate_zero
#print axioms stageTranslate_add
#print axioms stageTranslate_time
#print axioms stageTranslate_atBase
#print axioms pairing_translate
#print axioms distSq_translate
#print axioms translationNonexpansive
#print axioms translationSemigroup
#print axioms completedTranslation
#print axioms translation_cauchy_modulus
#print axioms completedTranslation_embedStage
#print axioms completedTranslation_zero
#print axioms completedTranslation_add
#print axioms completedTranslation_time
#print axioms stageTranslate_unit_null
#print axioms completedTranslation_unit
#print axioms completedInner_translate

end YMGap.Continuum.BF4SpatialUnionDiagonalTranslation
