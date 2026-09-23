/-
# Conjugated head defect with a selected-block energy

The conjugated finite head estimate is stated first with the angular energy
of the recoded polynomial.  The padded-safe angular transport theorem rewrites
that right-hand side as the energy of the original block selected by the
involution.  This is still a finite SU(2) carrier statement; it does not
identify the conjugated update with an interacting selected-link kernel.
-/

import YMGap.Continuum.SU2QuaternionConjugatedHeadHeat
import YMGap.Continuum.SU2QuaternionAngularReindex

namespace YMGap.Continuum.SU2QuaternionConjugatedHeadHeatBlockEnergy

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.SU2QuaternionConjugatedHeadHeat
open YMGap.Continuum.SU2HeatCutoffCasimirBound

local infix:50 " ≈ " => Q'.eqv

theorem conjugatedHeadMap_defect_le_selected_block_energy
    (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K)
    (s : QuaternionBlockInvolution (tail + 1)) (polynomial : RatPoly)
    (hpolynomial : SupportedQuaternionBlocks (tail + 1) polynomial) :
    quaternionHaar (tail + 1) (polyMul polynomial polynomial) -
        quaternionHaar (tail + 1)
          (polyMul polynomial (conjugatedHeadMap s w K polynomial)) ≤
      ((1 : Q') - w) *
        quaternionHaar (tail + 1)
          (blockAngularSquare (s.map 0) polynomial) := by
  have hdef := conjugatedHeadMap_defect_le_angular tail hw0 hw1 K hK
    s polynomial hpolynomial
  have htransport := reindex_blockAngularSquare_haar
    (blocks := tail + 1) s (block := 0) (by omega) polynomial
  have hsourceSupport : SupportedQuaternionBlocks (tail + 1)
      (blockAngularSquare (s.map 0) polynomial) :=
    blockAngularSquare_supported (s.map_lt 0 (by omega)) hpolynomial
  have hsource := quaternionHaar_reindex s
    (blockAngularSquare (s.map 0) polynomial) hsourceSupport
  have hzero : blockAngularSquare 0
      (reindexQuaternionPolynomial s polynomial) =
      angularSquare (reindexQuaternionPolynomial s polynomial) := by
    rfl
  have henergy : quaternionHaar (tail + 1)
      (angularSquare (reindexQuaternionPolynomial s polynomial)) ≈
      quaternionHaar (tail + 1)
        (blockAngularSquare (s.map 0) polynomial) := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.eqv_of_eq (congrArg (quaternionHaar (tail + 1)) hzero)))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm htransport) hsource)
  exact Q'.le_trans' _ _ _ hdef
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left ((1 : Q') - w) _ _ henergy))

end YMGap.Continuum.SU2QuaternionConjugatedHeadHeatBlockEnergy

#print axioms YMGap.Continuum.SU2QuaternionConjugatedHeadHeatBlockEnergy.conjugatedHeadMap_defect_le_selected_block_energy
