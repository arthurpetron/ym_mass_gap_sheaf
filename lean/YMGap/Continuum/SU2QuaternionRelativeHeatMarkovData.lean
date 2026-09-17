/-
# Exact marginals and residual positivity of the original one-link heat kernel

The complete finite character packet on two quaternion blocks is supported,
has both normalized Haar marginals, and admits the existing positive
headFloor at every cutoff beyond the existing headCutoff. The marginals hold
for arbitrary supported polynomials, not only fundamental coordinates or
class functions. No spatial potential occurs in this kernel.

These are the concrete inputs to the centered ordinary-Haar kernel estimate.
No interacting transfer, OS norm, spatial tensorization or physical gap is
asserted here.
-/

import YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum
import YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate
import YMGap.Continuum.SU2QuaternionHaarKernelBound

namespace YMGap.Continuum.SU2QuaternionRelativeHeatMarkovData

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headFloor headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
  (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionRelativeHeatInsertion
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatVacuum
open YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

local infix:50 " ≈ " => Q'.eqv

/-- The actual two-link packet retains every spin through K. -/
theorem relativeHeat_supported (w : Q') (K : Nat) :
    SupportedQuaternionBlocks 2 (relativeHeat w K) :=
  heat_supported (blocks := 2) (a := 0) (b := 1) (by decide) (by decide) w K

private theorem sum_congr (f g : Nat → RatPoly) : ∀ xs : List Nat,
    (∀ i, i ∈ xs → f i = g i) → finitePolySum f xs = finitePolySum g xs
  | [], _ => rfl
  | i::xs, h => by
      simp only [finitePolySum, h i List.mem_cons_self,
        sum_congr f g xs (fun j hj => h j (List.mem_cons_of_mem i hj))]

/-- Literal ordinary heat prefix: no packet coefficient is replaced or dropped. -/
theorem relativeHeat_eq_prefix (w : Q') (K : Nat) :
    relativeHeat w K = heatPrefix w K relativeScalar := by
  unfold relativeHeat heatPrefix
  apply sum_congr
  intro spin hspin
  rw [coeffAt_heatKernelPacket (List.mem_range.mp hspin)]
  rfl

/-- Constructed residual-positive certificate at the original late-cutoff threshold. -/
def relativeHeat_floorCertificate {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K) :
    Certificate 2
      (polyAdd (relativeHeat w K) (polyNeg (cap (headFloor w)))) := by
  let word := PolyQuaternion.mul (PolyQuaternion.coordinateVariable 0)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 1))
  have hp : Supported 2 word :=
    (Supported.coordinate (blocks := 2) (block := 0) (by decide)).mul
      (Supported.coordinate (blocks := 2) (block := 1) (by decide)).conj
  have hu : HaarCarrierEqv 2 (polyQuaternionNorm word) polyOne :=
    haarNorm_mul (haarNorm_coordinate (blocks := 2) (block := 0) (by decide))
      (HaarCarrierEqv.trans
        (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _))
        (haarNorm_coordinate (blocks := 2) (block := 1) (by decide)))
  rw [relativeHeat_eq_prefix]
  exact QuaternionHaarAllNomeHeatCertificate.prefixFloorCertificate hw0 hw1 hp hu K hK

private theorem reversed_scalar : RatPolyCoeffEqv (scalarAt 1 0) relativeScalar := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

private theorem reversed_heat (w : Q') (K : Nat) :
    RatPolyCoeffEqv (heatAt 1 0 w K) (relativeHeat w K) := by
  unfold heatAt relativeHeat
  induction List.range (K+1) with
  | nil => exact .refl _
  | cons spin spins ih =>
      exact ((characterPolynomial_coeffEqv reversed_scalar spin).smul _).add ih

private theorem exponent_zero : ∀ (m : List Nat) (i : Nat),
    m.length ≤ i → exponentAt m i = 0
  | [], _, _ => rfl
  | _::_, 0, h => by simp at h
  | _::m, i+1, h => by
      simp only [exponentAt, List.getD_cons_succ]
      exact exponent_zero m i (by simp only [List.length_cons] at h; omega)

private theorem lower_independent {f : RatPoly}
    (hf : SupportedQuaternionBlocks 1 f) : HasQuaternionBlockDegree 1 0 f := by
  intro term hterm
  have hlength : term.1.length ≤ 4 := hf term hterm
  simp only [quaternionBlockDegree, Nat.mul_one,
    exponent_zero term.1 4 hlength,
    exponent_zero term.1 5 (by omega),
    exponent_zero term.1 6 (by omega),
    exponent_zero term.1 7 (by omega)]

/-- Integrating the upper endpoint leaves every original lower polynomial unchanged. -/
theorem relativeHeat_lower_marginal (w : Q') (K : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks 1 f) :
    quaternionHaar 2 (polyMul (relativeHeat w K) f) ≈ quaternionHaar 1 f := by
  have hf2 : SupportedQuaternionBlocks 2 f :=
    fun term hterm => Nat.le_trans (hf term hterm) (by decide)
  have hm := pair_vacuum 1 (by decide) ⟨1,by decide⟩ ⟨0,by decide⟩
    (by decide) w K f hf2 (lower_independent hf)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff ((reversed_heat w K).symm.mul_right f))
    (Q'.eqv_trans _ _ _ hm
      (quaternionHaar_extend_supported_endpoint (by decide : 1 ≤ 2) f hf))

/-- Integrating the lower endpoint leaves every original upper polynomial unchanged. -/
theorem relativeHeat_upper_marginal (w : Q') (K : Nat) (f : RatPoly)
    (_hf : SupportedQuaternionBlocks 1 f) :
    quaternionHaar 2 (polyMul (relativeHeat w K) (liftBoundary 1 f)) ≈
      quaternionHaar 1 f :=
  Q'.eqv_trans _ _ _
    (heat_vacuum 1 (by decide) w K (liftBoundary 1 f) (lifted_independent f))
    (haar_liftBoundary 1 1 f)

end YMGap.Continuum.SU2QuaternionRelativeHeatMarkovData

#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatMarkovData.relativeHeat_supported
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatMarkovData.relativeHeat_eq_prefix
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatMarkovData.relativeHeat_floorCertificate
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatMarkovData.relativeHeat_lower_marginal
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatMarkovData.relativeHeat_upper_marginal
