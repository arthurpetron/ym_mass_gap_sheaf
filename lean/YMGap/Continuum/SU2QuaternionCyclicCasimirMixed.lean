/-
# The mixed full-path second Casimir moment

The computed cyclic path eigenvalue can be transferred to any supported test
polynomial.  Reassembling the paths gives the literal mixed Casimir pairing,
with no positivity or diagonal restriction on the two inputs.
-/

import YMGap.Continuum.SU2QuaternionCyclicCasimirSquare

namespace YMGap.Continuum.SU2QuaternionCyclicCasimirMixed

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicCasimirSweep
open YMGap.Continuum.SU2QuaternionCyclicCasimirBilinear
open YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
open YMGap.Continuum.SU2QuaternionCyclicPathReassembly
open YMGap.Continuum.SU2QuaternionCyclicPathCasimir
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionLiteralCasimirPairing
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem path_supported (tail : Nat) : ∀ (ds : List Nat) (p : RatPoly),
    SupportedQuaternionBlocks (tail+1) p →
    SupportedQuaternionBlocks (tail+1) (pathPiece tail p ds)
  | [], _, hp => hp
  | d::ds, p, _ => path_supported tail ds (nextPiece tail p d)
      (nextPiece_supported tail p d)

private theorem path_casimir_mixed_test (tail : Nat) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (ht : SupportedQuaternionBlocks (tail+1) test) (ds : List Nat)
    (hlen : ds.length = tail+1) (hpath : ValidPath tail p ds) :
    H (tail+1) (polyMul (activeCasimirPolynomial (List.range (tail+1)) test)
      (pathPiece tail p ds)) ≈
      totalCasimir ds * H (tail+1) (polyMul test (pathPiece tail p ds)) := by
  let piece := pathPiece tail p ds
  let Ct := activeCasimirPolynomial (List.range (tail+1)) test
  have hs : SupportedQuaternionBlocks (tail+1) piece := path_supported tail ds p hp
  have he := full_path_activeCasimir_carrier tail p hp ds hlen hpath
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm Ct piece))
    (Q'.eqv_trans _ _ _ (pairCasimir_eq_literal tail test piece ht hs).symm
      (Q'.eqv_trans _ _ _ (pairCasimir_symm tail test piece ht hs)
        (Q'.eqv_trans _ _ _ (pairCasimir_eq_literal tail piece test hs ht)
          (Q'.eqv_trans _ _ _ (he test)
            (quaternionHaar_polyMul_smul_right (tail+1) (totalCasimir ds) test piece)))))

/-- The full cyclic path second moment is the mixed Haar pairing of the SAME
literal full Casimir on both supported inputs. All cross terms are retained. -/
theorem full_mixedSecondMoment_eq_literal (tail : Nat) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (ht : SupportedQuaternionBlocks (tail+1) test) :
    leafSum tail (tail+1) p test
      (fun ds => totalCasimir ds * totalCasimir ds) ≈
      H (tail+1) (polyMul
        (activeCasimirPolynomial (List.range (tail+1)) p)
        (activeCasimirPolynomial (List.range (tail+1)) test)) := by
  let Ct := activeCasimirPolynomial (List.range (tail+1)) test
  let Cp := activeCasimirPolynomial (List.range (tail+1)) p
  have hCt : SupportedQuaternionBlocks (tail+1) Ct :=
    activeCasimirPolynomial_supported (List.range (tail+1))
      (fun i hi => List.mem_range.mp hi) ht
  have hsum : leafSum tail (tail+1) p Ct totalCasimir ≈
      leafSum tail (tail+1) p test
        (fun ds => totalCasimir ds * totalCasimir ds) := by
    apply leafSum_pairing_congr
    intro ds hlen hpath
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (totalCasimir ds) _ _
        (path_casimir_mixed_test tail p test hp ht ds hlen hpath))
      (Q'.mul_assoc_eqv _ _ _).symm
  exact Q'.eqv_trans _ _ _ hsum.symm
    (Q'.eqv_trans _ _ _ (pairCasimir_eq_literal tail p Ct hp hCt)
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm Ct Cp)))

end YMGap.Continuum.SU2QuaternionCyclicCasimirMixed

#print axioms YMGap.Continuum.SU2QuaternionCyclicCasimirMixed.full_mixedSecondMoment_eq_literal
