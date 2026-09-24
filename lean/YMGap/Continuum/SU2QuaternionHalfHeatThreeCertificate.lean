/-
# A concrete positive cutoff-three relative heat kernel

At nome one half the three non-vacuum character terms have total sharp
absolute cap

  4/8 + 9/256 + 16/32768 = 1097/2048 < 1.

Thus the actual cutoff-three two-block heat polynomial has a constructive
positive certificate, and in fact retains the explicit floor 1/4.
-/

import YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
import YMGap.Continuum.QuaternionHaarSharpCharacterInterval

namespace YMGap.Continuum.SU2QuaternionHalfHeatThreeCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

local infix:50 " ≈ " => Q'.eqv

def half : Q' := Q'.mkPos 1 2 (by decide)

private def relativeSquare : SquareBound 2 (scalarAt 0 1) 1 :=
  SquareBound.scalar
    ((Supported.coordinate (by decide : 0 < 2)).mul
      (Supported.coordinate (by decide : 1 < 2)).conj)
    (haarNorm_mul (haarNorm_coordinate (by decide : 0 < 2))
      ((RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)).trans
        (haarNorm_coordinate (by decide : 1 < 2))))

private def c1 : Q' := Q'.mkPos 1 4 (by decide)
private def c2 : Q' := Q'.mkPos 3 256 (by decide)
private def c3 : Q' := Q'.mkPos 1 8192 (by decide)

theorem packetCoefficient_one :
    SU2CharacterVacuumHaar.coeffAt (heatKernelPacket 3 half) 1 ≈ c1 := by decide

theorem packetCoefficient_two :
    SU2CharacterVacuumHaar.coeffAt (heatKernelPacket 3 half) 2 ≈ c2 := by decide

theorem packetCoefficient_three :
    SU2CharacterVacuumHaar.coeffAt (heatKernelPacket 3 half) 3 ≈ c3 := by decide

/-- The sharp cap of all non-vacuum terms is exactly `1097/2048`. -/
theorem nonvacuum_cap_value :
    c1 * dimQ 1 + (c2 * dimQ 2 + c3 * dimQ 3) ≈
      Q'.mkPos 1097 2048 (by decide) := by decide

/-- The reserve remaining after also removing the displayed `1/4` floor. -/
theorem quarter_reserve_value :
    (Q'.mkPos 1 4 (by decide) + Q'.mkPos 439 2048 (by decide)) +
      Q'.mkPos 1097 2048 (by decide) ≈ 1 := by decide

private def characterLower (spin : Nat) :
    Certificate 2
      (polyAdd (cap (dimQ spin)) (characterPolynomial (scalarAt 0 1) spin)) :=
  (sharpCharacterInterval relativeSquare spin).lower

/-- A strict, fully explicit floor for the actual cutoff-three heat factor. -/
def heatAt_half_three_quarterFloor :
    Certificate 2
      (polyAdd (heatAt 0 1 half 3)
        (polyNeg (cap (Q'.mkPos 1 4 (by decide))))) := by
  let reserve := Q'.mkPos 439 2048 (by decide)
  let C : Certificate 2
      (polyAdd (cap reserve)
        (polyAdd
          (polySmul c1 (polyAdd (cap (dimQ 1))
            (characterPolynomial (scalarAt 0 1) 1)))
          (polyAdd
            (polySmul c2 (polyAdd (cap (dimQ 2))
              (characterPolynomial (scalarAt 0 1) 2)))
            (polySmul c3 (polyAdd (cap (dimQ 3))
              (characterPolynomial (scalarAt 0 1) 3)))))) :=
    .add (.constant 2 reserve (by decide))
      (.add
        (.smul c1 (by decide) (characterLower 1))
        (.add
          (.smul c2 (by decide) (characterLower 2))
          (.smul c3 (by decide) (characterLower 3))))
  exact .ofCoeff (RatPolyCoeffEqv.of_canon_termwise (by decide)) C

/-- Positivity of the concrete kernel itself, obtained without an eventual
cutoff hypothesis. -/
def heatAt_half_three_certificate : Certificate 2 (heatAt 0 1 half 3) :=
  let quarter : Q' := Q'.mkPos 1 4 (by decide)
  let C : Certificate 2
      (polyAdd
        (polyAdd (heatAt 0 1 half 3) (polyNeg (cap quarter)))
        (cap quarter)) :=
    .add heatAt_half_three_quarterFloor (.constant 2 quarter (by decide))
  .ofCoeff (RatPolyCoeffEqv.of_canon_termwise (by decide)) C

end YMGap.Continuum.SU2QuaternionHalfHeatThreeCertificate

#print axioms YMGap.Continuum.SU2QuaternionHalfHeatThreeCertificate.nonvacuum_cap_value
#print axioms YMGap.Continuum.SU2QuaternionHalfHeatThreeCertificate.heatAt_half_three_quarterFloor
#print axioms YMGap.Continuum.SU2QuaternionHalfHeatThreeCertificate.heatAt_half_three_certificate
