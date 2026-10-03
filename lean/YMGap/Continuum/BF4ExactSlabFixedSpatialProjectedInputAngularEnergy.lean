/-
# SAME-reference input angular energy of the ORIGINAL projected derivative

The first source derivative and all incoming action/transfer data stay at
ORIGINAL K. Only the auxiliary reference kernel uses L. Lower-fringe
projection contracts its input angular energy under the SAME complete
reference kernel and arbitrary certified output weight, with coefficient one.
Both source-derivative terms and every action factor are retained.

This is a SECOND-derivative energy-to-energy estimate. It is not the Q^2
budget, an energy-to-surviving-norm bound, scaling uniformity or a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative
import YMGap.Continuum.SU2QuaternionHaarFamilyWeightedAngularContraction

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedInputAngularEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSourceDerivative
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionHaarFamilyWeightedAngularContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight kineticWeight

/-- Actual INPUT-gradient energy at the auxiliary reference cutoff. -/
def inputAngularReferenceEnergy (w : Q') (L width block : Nat) (p : RatPoly) : RatPoly :=
  partialHaarHeads (N width)
    (polyMul (kineticWeight w L width) (blockAngularSquare block p))

def projectedInputAngularEnergy (w : Q') (K L width block s i j : Nat)
    (a c : RatPoly) : RatPoly :=
  inputAngularReferenceEnergy w L width block
    (lastStepProjectedDerivative w K width s i j a c)

def sourceInputAngularEnergy (w : Q') (K L width block s i j : Nat)
    (a c : RatPoly) : RatPoly :=
  inputAngularReferenceEnergy w L width block
    (lastStepSourceDerivative w K width s i j a c)

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (hle : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 hle)

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  exact hp q hq

private theorem source_supported (w : Q') (K width s i j : Nat)
    (hs : s < N width) (hi : i < 4) (hj : j < 4) {a c : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) :
    SupportedQuaternionBlocks (N width+N width)
      (lastStepSourceDerivative w K width s i j a c) := by
  have hD {p : RatPoly} (hp : SupportedQuaternionBlocks (N width) p) :
      SupportedQuaternionBlocks (N width)
        (angularDerivative (4*s+i) (4*s+j) (polyMul (spatialWeight w K width) p)) :=
    angularDerivative_supported_at (by omega) (by omega)
      (supported_polyMul (spatialWeight_supported w K width) hp)
  exact supported_add
    (supported_polyMul (lift_supported (transferStep_supported w K width ha) (N width))
      (support_mono (hD hc) (by omega)))
    (support_neg (supported_polyMul (lift_supported (transferStep_supported w K width hc) (N width))
      (support_mono (hD ha) (by omega))))

/-- Exact output-weight pairing, retaining all lower kernel variables. -/
theorem inputAngularReferenceEnergy_pairing (w : Q') (L width block : Nat)
    (p W : RatPoly) :
    quaternionHaar (N width) (polyMul W (inputAngularReferenceEnergy w L width block p)) ≈
      quaternionHaar (N width+N width)
        (polyMul (polyMul (kineticWeight w L width) (liftBoundary (N width) W))
          (blockAngularSquare block p)) := by
  have hr : RatPolyCoeffEqv
      (polyMul (polyMul (kineticWeight w L width) (blockAngularSquare block p))
        (liftBoundary (N width) W))
      (polyMul (polyMul (kineticWeight w L width) (liftBoundary (N width) W))
        (blockAngularSquare block p)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => kineticWeight w L width | 1 => blockAngularSquare block p
           | _ => liftBoundary (N width) W)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (head_pairing (N width) (N width)
      (polyMul (kineticWeight w L width) (blockAngularSquare block p)) W))
      (haar_of_coeff hr))

/-- Genuine second-derivative contraction, retaining ORIGINAL K and every
action/transfer factor. Only the auxiliary positive reference kernel uses L. -/
theorem projected_inputAngularEnergy_weighted_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K L width : Nat)
    (hL : headCutoff w ≤ L) (block s i j : Nat)
    (hb : block < N width) (hs : s < N width) (hi : i < 4) (hj : j < 4)
    (a c W : RatPoly) (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) (P : Certificate (N width) W) :
    quaternionHaar (N width) (polyMul W (projectedInputAngularEnergy w K L width block s i j a c)) ≤
      quaternionHaar (N width) (polyMul W (sourceInputAngularEnergy w K L width block s i j a c)) := by
  let E := polyMul (kineticWeight w L width) (liftBoundary (N width) W)
  have PK : Certificate (N width+N width) (kineticWeight w L width) := by
    rw [kineticWeight_eq_indexedProduct]
    exact productHeatCertificate (N width) hw0 hw1 L hL (activeBlocks width) (activeBlocks_lt width)
  have PE : Certificate (N width+N width) E := PK.mul (lift_certificate (N width) P)
  have hE : ∀ b, b ∈ fringeBlocks width → QuaternionBlockIndependent b E := by
    intro b hmem
    have hp : QuaternionBlockIndependent b (kineticWeight w L width) := by
      rw [kineticWeight_eq_indexedProduct]
      exact productHeat_independent_lower (N width) w L (activeBlocks width)
        (activeBlocks_lt width) b (fringeBlocks_lt width b hmem)
        ((fringeBlocks_mem_iff width b).mp hmem).2
    exact quaternionBlockIndependent_polyMul hp
      (lift_lower_independent (N width) W b (fringeBlocks_lt width b hmem))
  have h := familyProject_weighted_blockAngularSquare_le (N width+N width)
    (fringeBlocks width) (fun b hmem => by have := fringeBlocks_lt width b hmem; omega)
    block (by omega) E (lastStepSourceDerivative w K width s i j a c) PE
    (source_supported w K width s i j hs hi hj ha hc) hE
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (inputAngularReferenceEnergy_pairing w L width block
    (lastStepProjectedDerivative w K width s i j a c) W))
    (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv (inputAngularReferenceEnergy_pairing w L width block
      (lastStepSourceDerivative w K width s i j a c) W)))

#print axioms inputAngularReferenceEnergy
#print axioms projectedInputAngularEnergy
#print axioms sourceInputAngularEnergy
#print axioms inputAngularReferenceEnergy_pairing
#print axioms projected_inputAngularEnergy_weighted_le

end YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedInputAngularEnergy
