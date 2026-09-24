/-
# The actual path second moment is the literal Casimir square

The full character-product eigenaction, not a projector assumption, identifies
each computed path's Casimir.  Self-adjointness transfers that action to the
test polynomial.  Finite ragged-tree reassembly then identifies the second
moment with the Haar square of the SAME literal differential operator.
-/

import YMGap.Continuum.SU2QuaternionCyclicPathCasimir
import YMGap.Continuum.SU2QuaternionDiagonalRemainderMoment
import YMGap.Continuum.SU2QuaternionLiteralCasimirPairing

namespace YMGap.Continuum.SU2QuaternionCyclicCasimirSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicCasimirSweep
open YMGap.Continuum.SU2QuaternionCyclicCasimirBilinear
open YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
open YMGap.Continuum.SU2QuaternionCyclicPathReassembly
open YMGap.Continuum.SU2QuaternionCyclicPathCasimir
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionLiteralCasimirPairing
open YMGap.Continuum.SU2QuaternionDiagonalRemainderMoment
open YMGap.Continuum.SU2QuaternionExactRemainderForm
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem path_supported (tail : Nat) : ∀ (ds : List Nat) (p : RatPoly),
    SupportedQuaternionBlocks (tail+1) p →
    SupportedQuaternionBlocks (tail+1) (pathPiece tail p ds)
  | [], _, hp => hp
  | d::ds, p, _ => path_supported tail ds (nextPiece tail p d)
      (nextPiece_supported tail p d)

private theorem path_casimir_test (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (ds : List Nat)
    (hlen : ds.length = tail+1) (hpath : ValidPath tail p ds) :
    H (tail+1) (polyMul (activeCasimirPolynomial (List.range (tail+1)) p)
      (pathPiece tail p ds)) ≈
      totalCasimir ds * H (tail+1) (polyMul p (pathPiece tail p ds)) := by
  let piece := pathPiece tail p ds
  let Cp := activeCasimirPolynomial (List.range (tail+1)) p
  have hs : SupportedQuaternionBlocks (tail+1) piece := path_supported tail ds p hp
  have he := full_path_activeCasimir_carrier tail p hp ds hlen hpath
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm Cp piece))
    (Q'.eqv_trans _ _ _ (pairCasimir_eq_literal tail p piece hp hs).symm
      (Q'.eqv_trans _ _ _ (pairCasimir_symm tail p piece hp hs)
        (Q'.eqv_trans _ _ _ (pairCasimir_eq_literal tail piece p hs hp)
          (Q'.eqv_trans _ _ _ (he p)
            (quaternionHaar_polyMul_smul_right (tail+1) (totalCasimir ds) p piece)))))

/-- The positive full-path second moment is exactly the original Haar square
of the literal full Casimir, including all cross terms. -/
theorem full_squareMoment_eq_literal (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    leafSum tail (tail+1) p p (fun ds => totalCasimir ds * totalCasimir ds) ≈
      H (tail+1) (polyMul (activeCasimirPolynomial (List.range (tail+1)) p)
        (activeCasimirPolynomial (List.range (tail+1)) p)) := by
  let Cp := activeCasimirPolynomial (List.range (tail+1)) p
  have hCp : SupportedQuaternionBlocks (tail+1) Cp :=
    activeCasimirPolynomial_supported (List.range (tail+1))
      (fun i hi => List.mem_range.mp hi) hp
  have hsum : leafSum tail (tail+1) p Cp totalCasimir ≈
      leafSum tail (tail+1) p p (fun ds => totalCasimir ds * totalCasimir ds) := by
    apply leafSum_pairing_congr
    intro ds hlen hpath
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (totalCasimir ds) _ _
        (path_casimir_test tail p hp ds hlen hpath))
      (Q'.mul_assoc_eqv _ _ _).symm
  exact Q'.eqv_trans _ _ _ hsum.symm
    (pairCasimir_eq_literal tail p Cp hp hCp)

/-- The SAME second moment equals the square of the computed cyclic sweep. -/
theorem full_squareMoment_eq_sweep (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    leafSum tail (tail+1) p p (fun ds => totalCasimir ds * totalCasimir ds) ≈
      H (tail+1) (polyMul (casimirSweep tail (tail+1) p)
        (casimirSweep tail (tail+1) p)) :=
  Q'.eqv_trans _ _ _ (full_squareMoment_eq_literal tail p hp)
    (casimirSweep_square_eq_literal tail p hp).symm

/-- Quantitative remainder control in the actual computed differential norm.
This raw Haar norm is not the interacting centered variance. -/
theorem exactRemainderPair_diagonal_le_sweepSquare (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    exactRemainderPair tail w K p p ≤
      (((1 : Q')-w)*((1 : Q')-w))*
        H (tail+1) (polyMul (casimirSweep tail (tail+1) p)
          (casimirSweep tail (tail+1) p)) :=
  Q'.le_trans' _ _ _
    (exactRemainderPair_diagonal_le_squareMoment tail hw0 hw1 K hK p hp)
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (full_squareMoment_eq_sweep tail p hp)))

end YMGap.Continuum.SU2QuaternionCyclicCasimirSquare

#print axioms YMGap.Continuum.SU2QuaternionCyclicCasimirSquare.full_squareMoment_eq_literal
#print axioms YMGap.Continuum.SU2QuaternionCyclicCasimirSquare.full_squareMoment_eq_sweep
#print axioms YMGap.Continuum.SU2QuaternionCyclicCasimirSquare.exactRemainderPair_diagonal_le_sweepSquare
