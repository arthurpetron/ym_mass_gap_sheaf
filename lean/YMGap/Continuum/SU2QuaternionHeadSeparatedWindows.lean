/-
# Exact chronological factorization of two separated observed windows

The left observed window is contracted first, the same weighted step crosses
the unobserved gap, and the right observed window is contracted last. The
result is coefficient-equivalent to contracting their single combined
half-open action. No final spatial weight is inserted or removed: it remains
outside either message for the existing final weighted pairing.

All factors are arbitrary signed rational polynomials. The pull-out is valid
because the right factor is explicitly lifted beyond the integrated heads;
it does not require support, positivity, normalization or stationarity.
Zero blocks, zero window lengths and a zero gap are included. Original
geometric placement and normalized scalar comparison are later consumers.
-/

import YMGap.Continuum.SU2QuaternionHeadWindowContraction

namespace YMGap.Continuum.SU2QuaternionHeadSeparatedWindows

set_option autoImplicit false

open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadChainMiddleInsertion (liftBoundary_add)
open YMGap.Continuum.SU2QuaternionHeadWindowContraction

private theorem step_congr (blocks : Nat) (kernel weight : RatPoly)
    {f g : RatPoly} (h : RatPolyCoeffEqv f g) :
    RatPolyCoeffEqv (step blocks kernel weight f) (step blocks kernel weight g) :=
  partialHaarHeads_congr blocks ((h.mul_left weight).mul_left kernel)

private theorem iterate_congr (blocks : Nat) (kernel weight : RatPoly)
    (count : Nat) {f g : RatPoly} (h : RatPolyCoeffEqv f g) :
    RatPolyCoeffEqv (iterateStep blocks kernel weight count f)
      (iterateStep blocks kernel weight count g) := by
  induction count generalizing f g with
  | zero => exact h
  | succ count ih => exact ih (step_congr blocks kernel weight h)

private theorem iterate_add (blocks : Nat) (kernel weight : RatPoly)
    (m n : Nat) (input : RatPoly) :
    iterateStep blocks kernel weight (m+n) input =
      iterateStep blocks kernel weight n (iterateStep blocks kernel weight m input) := by
  induction m generalizing input with
  | zero => simp only [Nat.zero_add, iterateStep]
  | succ m ih =>
      simpa only [Nat.succ_add, iterateStep] using ih (step blocks kernel weight input)

/-- A factor explicitly placed beyond one integrated slice pulls out of
the actual weighted step, retaining all of its remaining coordinates. -/
theorem step_mul_lift (blocks : Nat) (kernel weight input tail : RatPoly) :
    RatPolyCoeffEqv
      (step blocks kernel weight (polyMul input (liftBoundary blocks tail)))
      (polyMul (step blocks kernel weight input) tail) := by
  have hsource : RatPolyCoeffEqv
      (polyMul kernel (polyMul weight (polyMul input (liftBoundary blocks tail))))
      (polyMul (polyMul kernel (polyMul weight input)) (liftBoundary blocks tail)) :=
    (((RatPolyCoeffEqv.mul_assoc weight input (liftBoundary blocks tail)).symm).mul_left kernel).trans
      (RatPolyCoeffEqv.mul_assoc kernel (polyMul weight input) (liftBoundary blocks tail)).symm
  exact (partialHaarHeads_congr blocks hsource).trans
    (partialHaarHeads_mul_lift blocks (polyMul kernel (polyMul weight input)) tail)

/-- A right insertion is retained through exactly the heads preceding its
explicit chronological offset. No one-slice support of input is assumed. -/
theorem iterateStep_mul_lift (blocks : Nat) (kernel weight : RatPoly)
    (count : Nat) (input tail : RatPoly) :
    RatPolyCoeffEqv
      (iterateStep blocks kernel weight count
        (polyMul input (liftBoundary (count*blocks) tail)))
      (polyMul (iterateStep blocks kernel weight count input) tail) := by
  induction count generalizing input with
  | zero =>
      simpa only [Nat.zero_mul, iterateStep, liftBoundary] using
        RatPolyCoeffEqv.refl (polyMul input tail)
  | succ count ih =>
      have hoffset : (count+1)*blocks = blocks+count*blocks := by
        rw [Nat.succ_mul]
        omega
      change RatPolyCoeffEqv
        (iterateStep blocks kernel weight count
          (step blocks kernel weight (polyMul input (liftBoundary ((count+1)*blocks) tail))))
        (polyMul (iterateStep blocks kernel weight count (step blocks kernel weight input)) tail)
      rw [hoffset, liftBoundary_add]
      exact (iterate_congr blocks kernel weight count
        (step_mul_lift blocks kernel weight input (liftBoundary (count*blocks) tail))).trans
        (ih (step blocks kernel weight input))

/-- Coefficient-level middle-insertion contraction for the SAME iterate.
This retains the insertion polynomial itself, not merely its Haar pairing. -/
theorem iterateStep_middle (blocks : Nat) (kernel weight : RatPoly)
    (m n : Nat) (input probe : RatPoly) :
    RatPolyCoeffEqv
      (iterateStep blocks kernel weight (m+n)
        (polyMul input (liftBoundary (m*blocks) probe)))
      (iterateStep blocks kernel weight n
        (polyMul (iterateStep blocks kernel weight m input) probe)) := by
  rw [iterate_add]
  exact iterate_congr blocks kernel weight n
    (iterateStep_mul_lift blocks kernel weight m input probe)

/-- Exact factorization of two observed windows separated by g transitions.
The whole original half-open action is unchanged, with all overlapping
kernel/weight factors retained and the final spatial weight still external. -/
theorem windowMessage_separated (blocks : Nat) (kernel weight : RatPoly)
    (L g R : Nat) (input p q : RatPoly) :
    RatPolyCoeffEqv
      (windowMessage blocks kernel weight (L+g+R) input
        (polyMul p (liftBoundary ((L+g)*blocks) q)))
      (windowMessage blocks kernel weight R
        (iterateStep blocks kernel weight g (windowMessage blocks kernel weight L input p)) q) := by
  have hleft : RatPolyCoeffEqv
      (iterateStep blocks kernel weight (L+g) (polyMul input p))
      (iterateStep blocks kernel weight g (windowMessage blocks kernel weight L input p)) := by
    rw [iterate_add]
    exact iterate_congr blocks kernel weight g (windowMessage_iterate blocks kernel weight L input p).symm
  have hsource : RatPolyCoeffEqv
      (polyMul input (polyMul p (liftBoundary ((L+g)*blocks) q)))
      (polyMul (polyMul input p) (liftBoundary ((L+g)*blocks) q)) :=
    (RatPolyCoeffEqv.mul_assoc input p (liftBoundary ((L+g)*blocks) q)).symm
  exact (windowMessage_iterate blocks kernel weight (L+g+R) input
    (polyMul p (liftBoundary ((L+g)*blocks) q))).trans
    ((iterate_congr blocks kernel weight (L+g+R) hsource).trans
      ((iterateStep_middle blocks kernel weight (L+g) R (polyMul input p) q).trans
        ((iterate_congr blocks kernel weight R (hleft.mul_right q)).trans
          (windowMessage_iterate blocks kernel weight R
            (iterateStep blocks kernel weight g (windowMessage blocks kernel weight L input p)) q).symm)))

end YMGap.Continuum.SU2QuaternionHeadSeparatedWindows

#print axioms YMGap.Continuum.SU2QuaternionHeadSeparatedWindows.step_mul_lift
#print axioms YMGap.Continuum.SU2QuaternionHeadSeparatedWindows.iterateStep_mul_lift
#print axioms YMGap.Continuum.SU2QuaternionHeadSeparatedWindows.iterateStep_middle
#print axioms YMGap.Continuum.SU2QuaternionHeadSeparatedWindows.windowMessage_separated
