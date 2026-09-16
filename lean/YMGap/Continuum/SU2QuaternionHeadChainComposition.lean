/-
# Exact finite composition on two ordered quaternion slice carriers

The first `blocks` variables are integrated and the second `blocks`
variables are retained. The supplied kernel and one-slice weight remain
arbitrary signed rational polynomials. Explicit support bounds make each
step a polynomial on the SAME one-slice carrier.

The chain pairing counts the one-slice weight once at every slice,
including both endpoints. It is a finite coefficient/Fubini identity,
not a positivity, norm, stationary-vacuum, or spectral statement. The
identification with an original geometric action is a separate consumer.
-/

import YMGap.Continuum.SU2QuaternionHeadLinearHaar
import YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
import YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal

namespace YMGap.Continuum.SU2QuaternionHeadChainComposition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal

local infix:50 " ≈ " => Q'.eqv

/-- Integrating any number of ordered head blocks preserves coefficient
equality, with all surviving coordinates still polynomial variables. -/
theorem partialHaarHeads_congr (blocks : Nat) {left right : RatPoly}
    (h : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv (partialHaarHeads blocks left)
      (partialHaarHeads blocks right) := by
  induction blocks generalizing left right with
  | zero => exact h
  | succ blocks ih => exact ih (partialHaarHead_congr h)

/-- A polynomial placed after all integrated blocks can be pulled out
without a degree bound or an independence assumption on retained factors. -/
theorem partialHaarHeads_mul_lift : ∀ (blocks : Nat) (head tail : RatPoly),
    RatPolyCoeffEqv
      (partialHaarHeads blocks (polyMul head (liftBoundary blocks tail)))
      (polyMul (partialHaarHeads blocks head) tail)
  | 0, _, _ => RatPolyCoeffEqv.refl _
  | blocks+1, head, tail =>
      (partialHaarHeads_congr blocks
        (partialHaarHead_mul_lift head (liftBoundary blocks tail))).trans
        (partialHaarHeads_mul_lift blocks (partialHaarHead head) tail)

/-- Ordered-head Fubini with an arbitrary polynomial in the survivors. -/
theorem head_pairing (tailBlocks blocks : Nat) (head tail : RatPoly) :
    quaternionHaar (tailBlocks+blocks)
        (polyMul head (liftBoundary blocks tail)) ≈
      quaternionHaar tailBlocks
        (polyMul (partialHaarHeads blocks head) tail) :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_symm (quaternionHaar_partialHaarHeads tailBlocks blocks
      (polyMul head (liftBoundary blocks tail))))
    (haar_of_coeff (partialHaarHeads_mul_lift blocks head tail))

/-- One exact finite weighted step. `kernel` uses the lower then upper
slice; `weight` and `input` use the lower slice. The result uses the upper
slice, shifted back to the canonical first `blocks` coordinates. -/
def step (blocks : Nat) (kernel weight input : RatPoly) : RatPoly :=
  partialHaarHeads blocks (polyMul kernel (polyMul weight input))

private theorem support_mono {small large : Nat} {polynomial : RatPoly}
    (h : SupportedQuaternionBlocks small polynomial) (hle : small ≤ large) :
    SupportedQuaternionBlocks large polynomial := by
  intro term hterm
  exact Nat.le_trans (h term hterm) (Nat.mul_le_mul_left 4 hle)

/-- The same `blocks`-carrier is retained at every finite weighted step. -/
theorem step_supported {blocks : Nat} {kernel weight input : RatPoly}
    (hkernel : SupportedQuaternionBlocks (blocks+blocks) kernel)
    (hweight : SupportedQuaternionBlocks blocks weight)
    (hinput : SupportedQuaternionBlocks blocks input) :
    SupportedQuaternionBlocks blocks (step blocks kernel weight input) := by
  apply partialHaarHeads_supported blocks blocks
  exact supported_polyMul hkernel
    (supported_polyMul (support_mono hweight (by omega))
      (support_mono hinput (by omega)))

/-- Exact one-step pairing. The retained polynomial may use arbitrarily
many later slices; its variables are placed after the integrated slice. -/
theorem step_pairing (tailBlocks blocks : Nat)
    (kernel weight input tail : RatPoly) :
    quaternionHaar (tailBlocks+blocks)
        (polyMul (polyMul kernel (polyMul weight input))
          (liftBoundary blocks tail)) ≈
      quaternionHaar tailBlocks
        (polyMul (step blocks kernel weight input) tail) :=
  head_pairing tailBlocks blocks (polyMul kernel (polyMul weight input)) tail

private theorem input_product_reorder (kernel weight input tail : RatPoly) :
    RatPolyCoeffEqv
      (polyMul input (polyMul kernel (polyMul weight tail)))
      (polyMul (polyMul kernel (polyMul weight input)) tail) :=
  (RatPolyCoeffEqv.mul_left input
    (RatPolyCoeffEqv.mul_assoc kernel weight tail).symm).trans
    ((RatPolyCoeffEqv.mul_assoc input (polyMul kernel weight) tail).symm.trans
      (((RatPolyCoeffEqv.mul_comm input (polyMul kernel weight)).mul_right tail).trans
        ((RatPolyCoeffEqv.mul_assoc kernel weight input).mul_right tail)))

/-- The one-step identity in the product ordering of `chain` below. -/
theorem chain_step_pairing (tailBlocks blocks : Nat)
    (kernel weight input tail : RatPoly) :
    quaternionHaar (tailBlocks+blocks)
        (polyMul input (polyMul kernel
          (polyMul weight (liftBoundary blocks tail)))) ≈
      quaternionHaar tailBlocks
        (polyMul (step blocks kernel weight input) tail) :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff
      (input_product_reorder kernel weight input (liftBoundary blocks tail)))
    (step_pairing tailBlocks blocks kernel weight input tail)

/-- Iterate the concrete finite polynomial step; no quotient-space or
analytic operator construction is involved. -/
def iterateStep (blocks : Nat) (kernel weight : RatPoly) : Nat → RatPoly → RatPoly
  | 0, input => input
  | count+1, input =>
      iterateStep blocks kernel weight count (step blocks kernel weight input)

theorem iterateStep_supported {blocks : Nat} {kernel weight : RatPoly}
    (hkernel : SupportedQuaternionBlocks (blocks+blocks) kernel)
    (hweight : SupportedQuaternionBlocks blocks weight)
    (count : Nat) {input : RatPoly}
    (hinput : SupportedQuaternionBlocks blocks input) :
    SupportedQuaternionBlocks blocks (iterateStep blocks kernel weight count input) := by
  induction count generalizing input with
  | zero => exact hinput
  | succ count ih => exact ih (step_supported hkernel hweight hinput)

/-- A chain with `count` two-slice kernels and `count+1` one-slice
weights. The terminal insertion is on its final slice. Every recursive
lift shifts the entire remaining chain, preserving all overlapping factors. -/
def chain (blocks : Nat) (kernel weight : RatPoly) : Nat → RatPoly → RatPoly
  | 0, terminal => polyMul weight terminal
  | count+1, terminal =>
      polyMul kernel (polyMul weight
        (liftBoundary blocks (chain blocks kernel weight count terminal)))

theorem chain_supported {blocks : Nat} {kernel weight : RatPoly}
    (hkernel : SupportedQuaternionBlocks (blocks+blocks) kernel)
    (hweight : SupportedQuaternionBlocks blocks weight)
    (count : Nat) {terminal : RatPoly}
    (hterminal : SupportedQuaternionBlocks blocks terminal) :
    SupportedQuaternionBlocks ((count+1)*blocks)
      (chain blocks kernel weight count terminal) := by
  induction count with
  | zero =>
      simpa only [chain, Nat.zero_add, Nat.one_mul] using
        supported_polyMul hweight hterminal
  | succ count ih =>
      have hblocks : blocks ≤ (count+1)*blocks := by
        rw [Nat.succ_mul]
        omega
      have hproduct : SupportedQuaternionBlocks ((count+1)*blocks+blocks)
          (polyMul kernel (polyMul weight
            (liftBoundary blocks (chain blocks kernel weight count terminal)))) :=
        supported_polyMul (support_mono hkernel (by omega))
          (supported_polyMul (support_mono hweight (by omega))
            (lift_supported ih blocks))
      simpa only [chain, Nat.succ_mul] using hproduct

/-- Exact finite signed chain contraction. The endpoint weight on the
final slice remains explicit; no vacuum or normalization is supplied. -/
theorem chain_pairing (blocks : Nat) (kernel weight : RatPoly) :
    ∀ (count : Nat) (input terminal : RatPoly),
      quaternionHaar ((count+1)*blocks)
          (polyMul input (chain blocks kernel weight count terminal)) ≈
        quaternionHaar blocks
          (polyMul (iterateStep blocks kernel weight count input)
            (polyMul weight terminal))
  | 0, input, terminal => by
      simpa only [chain, iterateStep, Nat.zero_add, Nat.one_mul] using
        Q'.eqv_refl (quaternionHaar blocks (polyMul input (polyMul weight terminal)))
  | count+1, input, terminal => by
      have hstep := chain_step_pairing ((count+1)*blocks) blocks
        kernel weight input (chain blocks kernel weight count terminal)
      have htail := chain_pairing blocks kernel weight count
        (step blocks kernel weight input) terminal
      simpa only [chain, iterateStep, Nat.succ_mul] using
        Q'.eqv_trans _ _ _ hstep htail

end YMGap.Continuum.SU2QuaternionHeadChainComposition

#print axioms YMGap.Continuum.SU2QuaternionHeadChainComposition.partialHaarHeads_congr
#print axioms YMGap.Continuum.SU2QuaternionHeadChainComposition.partialHaarHeads_mul_lift
#print axioms YMGap.Continuum.SU2QuaternionHeadChainComposition.head_pairing
#print axioms YMGap.Continuum.SU2QuaternionHeadChainComposition.step
#print axioms YMGap.Continuum.SU2QuaternionHeadChainComposition.step_supported
#print axioms YMGap.Continuum.SU2QuaternionHeadChainComposition.step_pairing
#print axioms YMGap.Continuum.SU2QuaternionHeadChainComposition.chain_step_pairing
#print axioms YMGap.Continuum.SU2QuaternionHeadChainComposition.iterateStep
#print axioms YMGap.Continuum.SU2QuaternionHeadChainComposition.iterateStep_supported
#print axioms YMGap.Continuum.SU2QuaternionHeadChainComposition.chain
#print axioms YMGap.Continuum.SU2QuaternionHeadChainComposition.chain_supported
#print axioms YMGap.Continuum.SU2QuaternionHeadChainComposition.chain_pairing
