/-
# Exact contraction of a finite half-open observed window

The window action has one kernel and one lower-slice weight per transition,
but NO spatial weight on its retained final slice. Multiplication by the
lifted final weight recovers the existing full chain exactly. Integrating
the first L slices therefore produces a message to be paired with V*g,
without dividing by a variable polynomial or counting the final V twice.

The action, input and observed-window polynomial are arbitrary signed
rational polynomials. All three identities are coefficient/Haar identities
without positivity or support premises; the separate support theorems give
the genuine finite-window and retained-slice carriers. In particular the
unobserved message is the existing iterateStep, including zero transitions
and zero blocks. No normalization, stationarity or reflection is asserted.
-/

import YMGap.Continuum.SU2QuaternionHeadChainMiddleInsertion

namespace YMGap.Continuum.SU2QuaternionHeadWindowContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadFubini (partialHaarHead)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadChainMiddleInsertion (liftBoundary_add)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal

local infix:50 " ≈ " => Q'.eqv

/-- L transition factors, each carrying its lower-slice weight. The final
slice has no weight here; that factor remains in the final pairing. -/
def halfOpenAction (blocks : Nat) (kernel weight : RatPoly) : Nat → RatPoly
  | 0 => polyOne
  | count+1 => polyMul kernel (polyMul weight
      (liftBoundary blocks (halfOpenAction blocks kernel weight count)))

/-- Contract the first L slices of the observed window. The input lives
on the first slice and the probe may use the whole L+1-slice window. -/
def windowMessage (blocks : Nat) (kernel weight : RatPoly) (count : Nat)
    (input probe : RatPoly) : RatPoly :=
  partialHaarHeads (count*blocks)
    (polyMul (polyMul input probe) (halfOpenAction blocks kernel weight count))

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (hle : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 hle)

/-- The half-open action uses precisely the same L+1-slice carrier as
the full chain, even though the final one-slice weight is omitted. -/
theorem halfOpenAction_supported {blocks : Nat} {kernel weight : RatPoly}
    (hkernel : SupportedQuaternionBlocks (blocks+blocks) kernel)
    (hweight : SupportedQuaternionBlocks blocks weight) (count : Nat) :
    SupportedQuaternionBlocks ((count+1)*blocks)
      (halfOpenAction blocks kernel weight count) := by
  induction count with
  | zero =>
      simpa only [halfOpenAction, Nat.zero_add, Nat.one_mul] using supported_one blocks
  | succ count ih =>
      have hblocks : blocks ≤ (count+1)*blocks := by
        rw [Nat.succ_mul]
        omega
      have hproduct : SupportedQuaternionBlocks ((count+1)*blocks+blocks)
          (polyMul kernel (polyMul weight
            (liftBoundary blocks (halfOpenAction blocks kernel weight count)))) :=
        supported_polyMul (support_mono hkernel (by omega))
          (supported_polyMul (support_mono hweight (by omega)) (lift_supported ih blocks))
      simpa only [halfOpenAction, Nat.succ_mul] using hproduct

/-- A supported observed window contracts onto the SAME one-slice carrier. -/
theorem windowMessage_supported {blocks : Nat} {kernel weight input probe : RatPoly}
    (hkernel : SupportedQuaternionBlocks (blocks+blocks) kernel)
    (hweight : SupportedQuaternionBlocks blocks weight) (count : Nat)
    (hinput : SupportedQuaternionBlocks blocks input)
    (hprobe : SupportedQuaternionBlocks ((count+1)*blocks) probe) :
    SupportedQuaternionBlocks blocks (windowMessage blocks kernel weight count input probe) := by
  have hblocks : blocks ≤ (count+1)*blocks := by
    rw [Nat.succ_mul]
    omega
  have hsource := supported_polyMul
    (supported_polyMul (support_mono hinput hblocks) hprobe)
    (halfOpenAction_supported hkernel hweight count)
  have hsize : (count+1)*blocks = blocks+count*blocks := by
    rw [Nat.succ_mul]
    omega
  rw [hsize] at hsource
  exact partialHaarHeads_supported blocks (count*blocks) _ hsource

/-- Restoring the final V*g recovers the original full chain, with every
spatial weight exactly once. Equality is coefficient-sensitive. -/
theorem halfOpenAction_chain (blocks : Nat) (kernel weight : RatPoly) :
    ∀ (count : Nat) (terminal : RatPoly),
      RatPolyCoeffEqv
        (polyMul (halfOpenAction blocks kernel weight count)
          (liftBoundary (count*blocks) (polyMul weight terminal)))
        (chain blocks kernel weight count terminal)
  | 0, terminal => by
      simpa only [halfOpenAction, chain, Nat.zero_mul, liftBoundary] using
        RatPolyCoeffEqv.one_mul (polyMul weight terminal)
  | count+1, terminal => by
      have hoffset : (count+1)*blocks = blocks+count*blocks := by
        rw [Nat.succ_mul]
        omega
      rw [halfOpenAction, chain, hoffset, liftBoundary_add]
      have hreorder : RatPolyCoeffEqv
          (polyMul (polyMul kernel (polyMul weight
            (liftBoundary blocks (halfOpenAction blocks kernel weight count))))
            (liftBoundary blocks (liftBoundary (count*blocks) (polyMul weight terminal))))
          (polyMul kernel (polyMul weight
            (polyMul (liftBoundary blocks (halfOpenAction blocks kernel weight count))
              (liftBoundary blocks (liftBoundary (count*blocks) (polyMul weight terminal)))))) :=
        coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
          (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (by decide)
          (fun
            | 0 => kernel
            | 1 => weight
            | 2 => liftBoundary blocks (halfOpenAction blocks kernel weight count)
            | _ => liftBoundary blocks (liftBoundary (count*blocks) (polyMul weight terminal)))
      refine hreorder.trans ?_
      rw [← lift_product]
      exact RatPolyCoeffEqv.mul_left kernel (RatPolyCoeffEqv.mul_left weight
        (lift_coeff blocks (halfOpenAction_chain blocks kernel weight count terminal)))

/-- Exact all-window Fubini identity. The probe need not factor into
single-slice insertions, and the final V remains outside the message. -/
theorem windowMessage_pairing (blocks : Nat) (kernel weight : RatPoly)
    (count : Nat) (input probe terminal : RatPoly) :
    quaternionHaar ((count+1)*blocks)
        (polyMul (polyMul input probe) (chain blocks kernel weight count terminal)) ≈
      quaternionHaar blocks
        (polyMul (windowMessage blocks kernel weight count input probe) (polyMul weight terminal)) := by
  have hsource :=
    ((RatPolyCoeffEqv.refl (polyMul input probe)).mul
      (halfOpenAction_chain blocks kernel weight count terminal).symm).trans
      (RatPolyCoeffEqv.mul_assoc (polyMul input probe)
        (halfOpenAction blocks kernel weight count)
        (liftBoundary (count*blocks) (polyMul weight terminal))).symm
  have hsize : (count+1)*blocks = blocks+count*blocks := by
    rw [Nat.succ_mul]
    omega
  rw [hsize]
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hsource)
    (head_pairing blocks (count*blocks)
      (polyMul (polyMul input probe) (halfOpenAction blocks kernel weight count))
      (polyMul weight terminal))

private theorem partialHaarHeads_compose (first rest : Nat) (p : RatPoly) :
    partialHaarHeads (first+rest) p = partialHaarHeads rest (partialHaarHeads first p) := by
  induction first generalizing p with
  | zero => simp only [Nat.zero_add, partialHaarHeads]
  | succ first ih =>
      simpa only [Nat.succ_add, partialHaarHeads] using ih (partialHaarHead p)

private theorem halfOpenAction_contraction (blocks : Nat) (kernel weight : RatPoly) :
    ∀ (count : Nat) (input : RatPoly),
      RatPolyCoeffEqv
        (partialHaarHeads (count*blocks)
          (polyMul input (halfOpenAction blocks kernel weight count)))
        (iterateStep blocks kernel weight count input)
  | 0, input => by
      simpa only [Nat.zero_mul, partialHaarHeads, halfOpenAction, iterateStep] using
        RatPolyCoeffEqv.mul_one input
  | count+1, input => by
      have hsource : RatPolyCoeffEqv
          (polyMul input (halfOpenAction blocks kernel weight (count+1)))
          (polyMul (polyMul kernel (polyMul weight input))
            (liftBoundary blocks (halfOpenAction blocks kernel weight count))) :=
        coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
          (.mul (.mul (.var 1) (.mul (.var 2) (.var 0))) (.var 3)) (by decide)
          (fun
            | 0 => input
            | 1 => kernel
            | 2 => weight
            | _ => liftBoundary blocks (halfOpenAction blocks kernel weight count))
      have hhead := (partialHaarHeads_congr blocks hsource).trans
        (partialHaarHeads_mul_lift blocks (polyMul kernel (polyMul weight input))
          (halfOpenAction blocks kernel weight count))
      have hsize : (count+1)*blocks = blocks+count*blocks := by
        rw [Nat.succ_mul]
        omega
      rw [hsize, partialHaarHeads_compose]
      exact (partialHaarHeads_congr (count*blocks) hhead).trans
        (halfOpenAction_contraction blocks kernel weight count (step blocks kernel weight input))

/-- The whole observed window can be retained in the initial polynomial
of the existing algebraic iterate. The probe may use later slices; no
one-slice support premise is required for this finite coefficient identity. -/
theorem windowMessage_iterate (blocks : Nat) (kernel weight : RatPoly)
    (count : Nat) (input probe : RatPoly) :
    RatPolyCoeffEqv (windowMessage blocks kernel weight count input probe)
      (iterateStep blocks kernel weight count (polyMul input probe)) :=
  halfOpenAction_contraction blocks kernel weight count (polyMul input probe)

/-- The unobserved message is exactly the existing finite iterate. There
is no extra final V and no positivity or support assumption to cancel. -/
theorem windowMessage_one (blocks : Nat) (kernel weight : RatPoly)
    (count : Nat) (input : RatPoly) :
    RatPolyCoeffEqv (windowMessage blocks kernel weight count input polyOne)
      (iterateStep blocks kernel weight count input) :=
  (partialHaarHeads_congr (count*blocks)
    ((RatPolyCoeffEqv.mul_one input).mul_right (halfOpenAction blocks kernel weight count))).trans
    (halfOpenAction_contraction blocks kernel weight count input)

end YMGap.Continuum.SU2QuaternionHeadWindowContraction

#print axioms YMGap.Continuum.SU2QuaternionHeadWindowContraction.halfOpenAction
#print axioms YMGap.Continuum.SU2QuaternionHeadWindowContraction.windowMessage
#print axioms YMGap.Continuum.SU2QuaternionHeadWindowContraction.halfOpenAction_supported
#print axioms YMGap.Continuum.SU2QuaternionHeadWindowContraction.windowMessage_supported
#print axioms YMGap.Continuum.SU2QuaternionHeadWindowContraction.halfOpenAction_chain
#print axioms YMGap.Continuum.SU2QuaternionHeadWindowContraction.windowMessage_pairing
#print axioms YMGap.Continuum.SU2QuaternionHeadWindowContraction.windowMessage_iterate
#print axioms YMGap.Continuum.SU2QuaternionHeadWindowContraction.windowMessage_one
