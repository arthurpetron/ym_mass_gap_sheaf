/-
# One-step positivity on the SAME completed Wilson spatial union

The proved original odd-window positivity is applied to every finite signed
Wilson stage, then passed through the existing mixed-pairing limit of each
supplied Cauchy stream. Quotient induction gives positivity on every vector
of the current spatial-union completion, including streams with unbounded
spatial bases and time radii. No representative is selected by choice.

On the direct complexification, the real part is the sum of the two actual
real quadratic forms. Symmetry and time balance cancel the imaginary part.
The result concerns the original one-step time map, not merely its square.

The existing fixed-spacing, small-nome SU(2) guards are unchanged. No new
strict rate, spectral theorem, continuous-time generator, complex Hilbert
completeness, changing-spacing construction or continuum QFT is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimePositive
import YMGap.Continuum.BF4WilsonSpatialUnionComplexification

namespace YMGap.Continuum.BF4WilsonSpatialUnionTimePositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
open YMGap.Continuum.BF4WilsonSpatialUnionComplexification
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (intrinsicForm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimePositive
  (intrinsicForm_oneStep_nonnegative)
open YMGap.Continuum.BF4SpatialUnionBilinear (rc_add_zero rc_sub_self)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "P" => pairing hw0 hw1 hsmall hd hs
local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "PD" => pairingData hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "A" n => timeNonexpansive hw0 hw1 hsmall hd hs n
local notation "VC" => ComplexCarrier hw0 hw1 hsmall hd hs
local notation "I" => inner hw0 hw1 hsmall hd hs
local notation "CT" => complexTime hw0 hw1 hsmall hd hs

attribute [local irreducible] pairing intrinsicForm

/-- Each stage uses its own actual positive spatial base. -/
theorem pairing_oneStep_nonnegative (x : Stage) :
    leEv (ofQ' 0) (P x (time 1 x)) := by
  have h := pairing_at_base hw0 hw1 hsmall hd hs x (time 1 x)
    x.base (Nat.le_refl _) (Nat.le_refl _)
  simp only [atBase_time, atBase_self] at h
  exact leEv_trans
    (intrinsicForm_oneStep_nonnegative hw0 hw1 hsmall hd hs x.positive x.value)
    (leEv_of_equiv h.symm)

/-- The time and Cauchy-stream indices are distinct; no common finite support
bound is required of the supplied stream. -/
theorem representativeInner_oneStep_nonnegative (X : (D).Cauchy) :
    leEv (ofQ' 0)
      (representativeInner hw0 hw1 hsmall hd hs X ((A 1).mapCauchy X)) := by
  apply leEv_of_convergesTo_le (convergesTo_const (ofQ' 0))
    (CRealSeminormPairingCompletion.pairSequence_converges PD X ((A 1).mapCauchy X))
  intro k
  exact pairing_oneStep_nonnegative hw0 hw1 hsmall hd hs (X.seq k)

/-- Positive quadratic form for the actual ONE-step map on every vector of
the same spatial-union quotient. No strict gap is asserted by this theorem. -/
theorem completedInner_oneStep_nonnegative (x : V) :
    RCnonneg (B x (T 1 x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact representativeInner_oneStep_nonnegative hw0 hw1 hsmall hd hs X

/-- The full complex one-step quadratic is real and nonnegative. Both
components range over the entire original real completion. -/
theorem inner_oneStep_nonnegative (x : VC) :
    RCnonneg (I x (CT 1 x)).1 ∧ (I x (CT 1 x)).2 = RCzero := by
  constructor
  · have h := RCadd_le_add
      (completedInner_oneStep_nonnegative hw0 hw1 hsmall hd hs x.1)
      (completedInner_oneStep_nonnegative hw0 hw1 hsmall hd hs x.2)
    rw [rc_add_zero] at h
    exact h
  · change RCsub (B x.1 (T 1 x.2)) (B x.2 (T 1 x.1)) = RCzero
    rw [← completedInner_time_balance hw0 hw1 hsmall hd hs 1 x.2 x.1,
      completedInner_symm hw0 hw1 hsmall hd hs (T 1 x.2) x.1, rc_sub_self]

end YMGap.Continuum.BF4WilsonSpatialUnionTimePositive

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionTimePositive.pairing_oneStep_nonnegative
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionTimePositive.representativeInner_oneStep_nonnegative
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionTimePositive.completedInner_oneStep_nonnegative
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionTimePositive.inner_oneStep_nonnegative
