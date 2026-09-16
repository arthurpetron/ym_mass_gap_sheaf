/-
# Actual physical time on the cutoff-removed reflected Cauchy carrier

The proved fixed-cutoff difference contraction passes through convergence
to the actual joint reflected squared distance. The SAME literal advance
of physical distance-from-plane presentations is therefore nonexpansive
for the new joint seminorm. The existing explicit-modulus completion
machinery descends this map and its semigroup laws, preserving every
supplied Cauchy modulus verbatim.

The original constant observable is a fixed completed vector distinct from
zero. No fixed-cutoff completion is identified with this new carrier, and
no nonconstant excitation, metric-completeness theorem, completed joint
inner product or Hamiltonian is constructed here. Nome, spatial width and
lattice spacing remain fixed; continuum-uniform estimates remain open.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
import YMGap.Continuum.FCNormBoundLimit

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit (pairing_unit_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
  (physicalTime physicalTime_zero physicalTime_add unit zero physicalTime_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
  (jointPairing pairing_converges_jointPairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift (pairing_time_sum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction
  (difference_contraction pairing_advance_contraction pairing_even_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width

/-- The actual physical advances add inside the cutoff-removed reflected
pairing, by the existing identity at every fixed heat stage. -/
theorem jointPairing_time_sum (r s : Nat) (x y : PhysicalSpan width) :
    Equiv (jointPairing hw0 hw1 width (physicalTime r x) (physicalTime s y))
      (jointPairing hw0 hw1 width x (physicalTime (r+s) y)) :=
  Equiv_of_limit_of_equal
    (fun stage => pairing_time_sum hw0 hw1 width r s x.val y.val
      x.property y.property stage)
    (pairing_converges_jointPairing hw0 hw1 width (physicalTime r x) (physicalTime s y))
    (pairing_converges_jointPairing hw0 hw1 width x (physicalTime (r+s) y))

/-- Every actual finite time advance balances between the two inputs. -/
theorem jointPairing_time_balance (n : Nat) (x y : PhysicalSpan width) :
    Equiv (jointPairing hw0 hw1 width (physicalTime n x) y)
      (jointPairing hw0 hw1 width x (physicalTime n y)) := by
  simpa only [physicalTime_zero, Nat.add_zero] using
    jointPairing_time_sum hw0 hw1 width n 0 x y

/-- Diagonal contraction survives the actual cutoff limit at each fixed
physical lag, without a positivity premise on the presentation. -/
theorem jointPairing_advance_contraction (n : Nat) (x : PhysicalSpan width) :
    leEv (jointPairing hw0 hw1 width (physicalTime n x) (physicalTime n x))
      (jointPairing hw0 hw1 width x x) :=
  leEv_of_convergesTo_le
    (pairing_converges_jointPairing hw0 hw1 width (physicalTime n x) (physicalTime n x))
    (pairing_converges_jointPairing hw0 hw1 width x x)
    (fun stage => pairing_advance_contraction hw0 hw1 width n x.val x.property stage)

/-- Site-reflected positivity remains an even-time statement. No one-step
positivity is inferred from symmetry or nonexpansiveness. -/
theorem jointPairing_even_nonnegative (n : Nat) (x : PhysicalSpan width) :
    leEv czero (jointPairing hw0 hw1 width x (physicalTime (2*n) x)) :=
  leEv_of_convergesTo_le (convergesTo_const czero)
    (pairing_converges_jointPairing hw0 hw1 width x (physicalTime (2*n) x))
    (fun stage => pairing_even_nonnegative hw0 hw1 width n x.val x.property stage)

/-- Nonexpansiveness is the limit of the actual original reflected-distance
inequalities, not an ordinary Haar-norm comparison or an assumed bound. -/
theorem jointPhysicalTime_contraction (n : Nat) (x y : PhysicalSpan width) :
    leEv (jointDistSq hw0 hw1 width (physicalTime n x) (physicalTime n y))
      (jointDistSq hw0 hw1 width x y) :=
  leEv_of_convergesTo_le
    (distSq_converges_joint hw0 hw1 width (physicalTime n x) (physicalTime n y))
    (distSq_converges_joint hw0 hw1 width x y)
    (fun stage => difference_contraction hw0 hw1 width n x.val y.val
      x.property y.property stage)

def jointTimeNonexpansive (n : Nat) : (D).Nonexpansive where
  toFun := physicalTime n
  contraction := jointPhysicalTime_contraction hw0 hw1 width n

def jointTimeSemigroup : (D).NonexpansiveSemigroup where
  op := jointTimeNonexpansive hw0 hw1 width
  zero_law := by
    intro x
    change Equiv (jointDistSq hw0 hw1 width (physicalTime 0 x) x) czero
    rw [physicalTime_zero]
    exact jointDistSq_refl hw0 hw1 width x
  add_law := by
    intro m n x
    change Equiv (jointDistSq hw0 hw1 width (physicalTime (m+n) x)
      (physicalTime m (physicalTime n x))) czero
    rw [physicalTime_add]
    exact jointDistSq_refl hw0 hw1 width _

/-- The existing explicit-modulus Cauchy quotient for the actual joint
seminorm; this is not any of the old stage-indexed completion carriers. -/
def JointCompletion : Type := (D).Completion

def jointEmbedSpan (x : PhysicalSpan width) : JointCompletion hw0 hw1 width :=
  (D).embedRep x

def jointCompletedTime (n : Nat) :
    JointCompletion hw0 hw1 width → JointCompletion hw0 hw1 width :=
  (jointTimeNonexpansive hw0 hw1 width n).completionMap

theorem jointCompletedTime_zero (x : JointCompletion hw0 hw1 width) :
    jointCompletedTime hw0 hw1 width 0 x = x :=
  (jointTimeSemigroup hw0 hw1 width).completionMap_zero x

theorem jointCompletedTime_add (m n : Nat) (x : JointCompletion hw0 hw1 width) :
    jointCompletedTime hw0 hw1 width (m+n) x =
      jointCompletedTime hw0 hw1 width m (jointCompletedTime hw0 hw1 width n x) :=
  (jointTimeSemigroup hw0 hw1 width).completionMap_add m n x

/-- On every original physical presentation, the descended map is precisely
the literal distance advance, with its face guard retained. -/
theorem jointCompletedTime_embedSpan (n : Nat) (x : PhysicalSpan width) :
    jointCompletedTime hw0 hw1 width n (jointEmbedSpan hw0 hw1 width x) =
      jointEmbedSpan hw0 hw1 width (physicalTime n x) := rfl

theorem jointTime_cauchy_seq (n : Nat) (X : (D).Cauchy) (k : Nat) :
    ((jointTimeNonexpansive hw0 hw1 width n).mapCauchy X).seq k =
      physicalTime n (X.seq k) := rfl

/-- No modulus is erased, replaced by a choice, or enlarged on descent. -/
theorem jointTime_cauchy_modulus (n : Nat) (X : (D).Cauchy) :
    ((jointTimeNonexpansive hw0 hw1 width n).mapCauchy X).modulus = X.modulus := rfl

def jointCompletedUnit : JointCompletion hw0 hw1 width :=
  jointEmbedSpan hw0 hw1 width (unit width)

theorem jointCompletedUnit_fixed (n : Nat) :
    jointCompletedTime hw0 hw1 width n (jointCompletedUnit hw0 hw1 width) =
      jointCompletedUnit hw0 hw1 width := by
  unfold jointCompletedUnit
  rw [jointCompletedTime_embedSpan, physicalTime_unit]

/-- The unit's distance from zero is the cutoff limit of its SAME normalized
original diagonal. The literal difference from the empty span reduces to unit. -/
theorem jointUnit_distance :
    Equiv (jointDistSq hw0 hw1 width (unit width) (zero width)) (ofQ' 1) :=
  Equiv_of_limit_of_equal
    (fun stage => pairing_unit_unit hw0 hw1 width stage)
    (distSq_converges_joint hw0 hw1 width (unit width) (zero width))
    (convergesTo_const (ofQ' 1))

/-- Equality of embedded constants in this joint completion forces their
joint reflected distance to vanish. The closeness witness keeps its modulus. -/
theorem jointEmbedSpan_eq_implies_null (x y : PhysicalSpan width)
    (h : jointEmbedSpan hw0 hw1 width x = jointEmbedSpan hw0 hw1 width y) :
    Equiv (jointDistSq hw0 hw1 width x y) czero := by
  obtain ⟨hc⟩ := Quotient.exact h
  have hu : leEv (jointDistSq hw0 hw1 width x y) czero := by
    intro epsilon he
    have hh := ExpNeg.half_mul_pos epsilon he
    have hb := hc.close (HalfPow.half*epsilon) hh
      (hc.modulus (HalfPow.half*epsilon)) (Nat.le_refl _)
    obtain ⟨N, hN⟩ := hb (HalfPow.half*epsilon) hh
    refine ⟨N, fun n hn => ?_⟩
    exact Q'.le_trans' _ _ _ (hN n hn)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (ExpNeg.two_halves epsilon)
        (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' epsilon)))))
  exact equiv_of_leEv_leEv hu (jointDistSq_nonnegative hw0 hw1 width x y)

/-- The fixed unit is nonzero. This does not assert a non-vacuum excitation
or a one-dimensional vacuum sector for the joint completion. -/
theorem jointCompletedUnit_ne_zero :
    jointCompletedUnit hw0 hw1 width ≠ jointEmbedSpan hw0 hw1 width (zero width) := by
  intro h
  have hnull := jointEmbedSpan_eq_implies_null hw0 hw1 width (unit width) (zero width) h
  have hbad := Equiv.trans (Equiv.symm (jointUnit_distance hw0 hw1 width)) hnull
  obtain ⟨N, hN⟩ := hbad HalfPow.half (by decide)
  have hle : (1 : Q') ≤ 0+HalfPow.half := (hN N (Nat.le_refl N)).1
  exact (by decide : ¬ ((1 : Q') ≤ 0+HalfPow.half)) hle

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointPairing_time_sum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointPairing_time_balance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointPairing_advance_contraction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointPairing_even_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointPhysicalTime_contraction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointTimeNonexpansive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointTimeSemigroup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.JointCompletion
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointEmbedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointCompletedTime
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointCompletedTime_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointCompletedTime_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointCompletedTime_embedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointTime_cauchy_seq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointTime_cauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointCompletedUnit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointCompletedUnit_fixed
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointUnit_distance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointEmbedSpan_eq_implies_null
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime.jointCompletedUnit_ne_zero
