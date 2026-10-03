/-
# Original selected-coordinate finite heat Stein identity

Expose one actual lower/upper kinetic pair on the complete carrier. The
computed head Green polynomial represents the selected coordinate defect,
while the ENTIRE source is differentiated and genuinely independent factors
are retained. No sign, source independence, or quantitative estimate follows.
-/

import YMGap.Continuum.SU2QuaternionRelativeHeatStein
import YMGap.Continuum.SU2QuaternionSelectedHarmonicHeatTransmission

namespace YMGap.Continuum.SU2QuaternionSelectedHeatStein

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionFourBlockSelection
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatStein
open YMGap.Continuum.SU2QuaternionHeadCasimirInverse
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

def coordinateDifference (a b : Nat) (w : Q') (i : Fin 4) : RatPoly :=
  polyAdd (polyVar (4*a+i.val)) (polySmul (-(qpow w 3)) (polyVar (4*b+i.val)))

/-- Computed gradients in the selected chart, with all source coordinates
and all retained polynomial factors carried through the same permutation. -/
def selectedGradientPair (tail : Nat) (hb : 0 < tail)
    (a b : Fin (tail+1)) (w : Q') (K : Nat) (i : Fin 4)
    (q r : RatPoly) : Q' :=
  let steps := pairSteps (by omega : 1 < tail+1) a b
  let tq := applyQuaternionBlockSwapChain steps q
  let tr := applyQuaternionBlockSwapChain steps r
  sixValue (fun j k => H (tail+1)
    (polyMul (polyMul (angularDerivative j k tq) tr)
      (angularDerivative j k (potential tail (coordinateDefect w K i)))))

private theorem chain_add {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (p q : RatPoly) :
    applyQuaternionBlockSwapChain steps (polyAdd p q) =
      polyAdd (applyQuaternionBlockSwapChain steps p)
        (applyQuaternionBlockSwapChain steps q) := by
  induction steps generalizing p q with
  | nil => rfl
  | cons s ss ih =>
      simp only [applyQuaternionBlockSwapChain, reindexQuaternionPolynomial_add, ih]

private theorem chain_smul {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (c : Q') (p : RatPoly) :
    applyQuaternionBlockSwapChain steps (polySmul c p) =
      polySmul c (applyQuaternionBlockSwapChain steps p) := by
  induction steps generalizing p with
  | nil => rfl
  | cons s ss ih =>
      simp only [applyQuaternionBlockSwapChain, reindexQuaternionPolynomial_smul, ih]

private theorem difference_supported {blocks : Nat} (a b : Fin blocks)
    (w : Q') (i : Fin 4) :
    SupportedQuaternionBlocks blocks (coordinateDifference a.val b.val w i) :=
  supported_add (coordinate_supported a.isLt i)
    (polySmul_supported (coordinate_supported b.isLt i) _)

/-- Exact ORIGINAL selected-coordinate identity. The source can depend on
the selected link and every spectator; only r is left undifferentiated. -/
theorem selected_coordinate_retained_source_gradient (tail : Nat) (hb : 0 < tail)
    (a b : Fin (tail+1)) (hab : a.val ≠ b.val)
    (w : Q') (K : Nat) (hK : 1 ≤ K) (i : Fin 4) (q r : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hr : SupportedQuaternionBlocks (tail+1) r)
    (hdr : HasQuaternionBlockDegree a.val 0 r) :
    H (tail+1) (polyMul (polyMul q r)
      (polyMul (heatAt a.val b.val w K) (coordinateDifference a.val b.val w i))) ≈
      selectedGradientPair tail hb a b w K i q r := by
  let steps := pairSteps (by omega : 1 < tail+1) a b
  let tq := applyQuaternionBlockSwapChain steps q
  let tr := applyQuaternionBlockSwapChain steps r
  let d := coordinateDifference a.val b.val w i
  have hq' := applyQuaternionBlockSwapChain_supported steps q hq
  have hr' := applyQuaternionBlockSwapChain_supported steps r hr
  have hd := difference_supported a b w i
  have hk := heat_supported a.isLt b.isLt w K
  have hfull := supported_polyMul (supported_polyMul hq hr) (supported_polyMul hk hd)
  have hinv := quaternionHaar_applyQuaternionBlockSwapChain steps _ hfull
  rw [chain_mul, chain_mul, chain_mul] at hinv
  have hdiff : PaddedPolynomialCoeffEqv (tail+1)
      (applyQuaternionBlockSwapChain steps d)
      (polyAdd (polyVar i.val) (polySmul (-(qpow w 3)) (polyVar (4+i.val)))) := by
    dsimp only [d, coordinateDifference]
    rw [chain_add, chain_smul]
    simpa only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] using
      ((PaddedPolynomialCoeffEqv.of_prefix
      (coordinate_exposed steps (by omega) (pair_zero (by omega) a b hab) i)).add
        ((PaddedPolynomialCoeffEqv.of_prefix
          (coordinate_exposed steps (by omega) (pair_one (by omega) a b) i)).smul (-(qpow w 3))))
  have hrec := ((PaddedPolynomialCoeffEqv.refl (tail+1) (polyMul tq tr)).mul
    ((heat_exposed (by omega) a b hab w K).mul hdiff)).haar
      (supported_polyMul (supported_polyMul hq' hr')
        (supported_polyMul (applyQuaternionBlockSwapChain_supported steps _ hk)
          (applyQuaternionBlockSwapChain_supported steps _ hd)))
      (supported_polyMul (supported_polyMul hq' hr') (coordinateDefect_supported hb w K i))
  have hrdeg : HasQuaternionBlockDegree 0 0 tr := by
    apply chain_degree steps (by omega)
    rw [pair_zero (by omega) a b hab]
    exact hdr
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hinv)
    (Q'.eqv_trans _ _ _ hrec
      (coordinateDefect_retained_source_gradient tail hb w K hK i tq tr hrdeg))

end YMGap.Continuum.SU2QuaternionSelectedHeatStein

#print axioms YMGap.Continuum.SU2QuaternionSelectedHeatStein.coordinateDifference
#print axioms YMGap.Continuum.SU2QuaternionSelectedHeatStein.selectedGradientPair
#print axioms YMGap.Continuum.SU2QuaternionSelectedHeatStein.selected_coordinate_retained_source_gradient
