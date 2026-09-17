/-
# Division-free centered bound for the ORIGINAL spatially weighted transfer

Let m(f)=H[V*f], with V the complete original spatial heat product, and set
F=m(g)*f-m(f)*g. Signed linearity constructs H[V*F]=0 without a division,
an assumed centering field, or any independence of the spatial factors.
The actual transfer satisfies T F=m(g)*T f-m(f)*T g=K(V*F). The original
kinetic tensorization estimate therefore bounds the squared norm of this
same output by squaredHeatRate(w)*H[(V*F)^2].

Every V factor remains in the right-hand side, twice after squaring. This
is neither a comparison with H[V*F^2] nor a stationary/OS vacuum projection,
an interacting spectral gap, or a physical mass calibration. Nome and the
late-cutoff threshold are explicit; the kinetic coefficient has no width
dependence. The reference g need not be positive because no ratio is taken.
-/

import YMGap.Continuum.SU2QuaternionProductHeatTensorization
import YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredKineticBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticContraction
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeHeatContraction (squaredHeatRate)
open YMGap.Continuum.SU2QuaternionProductHeatTensorization
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_add haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

/-- Both coefficients are the ORIGINAL V-weighted masses of the two inputs. -/
def centeredInput (w : Q') (K width : Nat) (f g : RatPoly) : RatPoly :=
  polyAdd (polySmul (weightedMass w K width g) f)
    (polySmul (-(weightedMass w K width f)) g)

private theorem smul_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro term hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  exact hp source hsource

theorem centeredInput_supported (w : Q') (K width : Nat) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hg : SupportedQuaternionBlocks (N width) g) :
    SupportedQuaternionBlocks (N width) (centeredInput w K width f g) :=
  supported_add (smul_supported hf _) (smul_supported hg _)

private theorem scalar_centering (a b : Q') : b * a + (-a) * b ≈ 0 :=
  poly_identity_of_normal_eq
    (.add (.mul (.var 1) (.var 0)) (.mul (.neg (.var 0)) (.var 1)))
    (.const 0) (by decide) (fun | 0 => a | _ => b)

/-- The centering premise required by kinetic contraction is constructed
for V*F, not incorrectly asserted for the unweighted input f. -/
theorem centeredInput_weighted_mean_zero (w : Q') (K width : Nat) (f g : RatPoly) :
    quaternionHaar (N width)
      (polyMul (spatialWeight w K width) (centeredInput w K width f g)) ≈ 0 := by
  change weightedMass w K width (centeredInput w K width f g) ≈ 0
  exact Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (weightedMass_smul w K width (weightedMass w K width g) f)
        (weightedMass_smul w K width (-(weightedMass w K width f)) g))
      (scalar_centering (weightedMass w K width f) (weightedMass w K width g)))

/-- Literal signed linearity uses the two INPUT masses; it does not recenter
with new output masses or replace T1 by the constant polynomial. -/
theorem transferStep_centeredInput (w : Q') (K width : Nat) (f g : RatPoly) :
    RatPolyCoeffEqv (transferStep w K width (centeredInput w K width f g))
      (polyAdd (polySmul (weightedMass w K width g) (transferStep w K width f))
        (polySmul (-(weightedMass w K width f)) (transferStep w K width g))) :=
  (transferStep_add w K width _ _).trans
    ((transferStep_smul w K width (weightedMass w K width g) f).add
      (transferStep_smul w K width (-(weightedMass w K width f)) g))

/-- Actual original-action consumer of the width-independent kinetic rate.
The spatial multiplier remains completely present in the displayed norm. -/
theorem centered_transfer_square_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hg : SupportedQuaternionBlocks (N width) g) :
    quaternionHaar (N width) (polyMul
      (polyAdd (polySmul (weightedMass w K width g) (transferStep w K width f))
        (polySmul (-(weightedMass w K width f)) (transferStep w K width g)))
      (polyAdd (polySmul (weightedMass w K width g) (transferStep w K width f))
        (polySmul (-(weightedMass w K width f)) (transferStep w K width g)))) ≤
      squaredHeatRate w * quaternionHaar (N width) (polyMul
        (polyMul (spatialWeight w K width) (centeredInput w K width f g))
        (polyMul (spatialWeight w K width) (centeredInput w K width f g))) := by
  have h := kineticMap_centered_square_bound hw0 hw1 K width hK
    (supported_polyMul (spatialWeight_supported w K width)
      (centeredInput_supported w K width hf hg))
    (centeredInput_weighted_mean_zero w K width f g)
  have hp := transferStep_centeredInput w K width f g
  rw [← transferStep_kineticMap] at h
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff (hp.symm.mul hp.symm))) h

end YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredKineticBound

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredKineticBound.centeredInput
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredKineticBound.centeredInput_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredKineticBound.centeredInput_weighted_mean_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredKineticBound.transferStep_centeredInput
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredKineticBound.centered_transfer_square_bound
