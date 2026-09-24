/- Casimir eigenaction on actual full cyclic degree paths. -/

import YMGap.Continuum.SU2QuaternionCharacterProductCasimir
import YMGap.Continuum.SU2QuaternionCasimirHeadIntegration
import YMGap.Continuum.SU2QuaternionCyclicPathReassembly

namespace YMGap.Continuum.SU2QuaternionCyclicPathCasimir

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionCharacterProductPositive
open YMGap.Continuum.SU2QuaternionCharacterProductCasimir
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.SU2QuaternionCharacterCasimirLocality
open YMGap.Continuum.SU2QuaternionSelectedCharacterCasimir
open YMGap.Continuum.SU2QuaternionCasimirHeadIntegration
open YMGap.Continuum.SU2QuaternionCyclicCharacterPositive
open YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
open YMGap.Continuum.SU2QuaternionCyclicPathReassembly
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.QuaternionHaarAngularCarrier

/-- The literal finite Casimir sum preserves arbitrary-insertion carrier
equality. -/
theorem activeCasimirPolynomial_carrier {blocks : Nat} :
    ∀ (active : List Nat), (∀ i, i ∈ active → i < blocks) →
      ∀ {p q : RatPoly}, HaarCarrierEqv blocks p q →
      HaarCarrierEqv blocks (activeCasimirPolynomial active p)
        (activeCasimirPolynomial active q)
  | [], _, _, _, _ => HaarCarrierEqv.refl _ _
  | block::active, hactive, _p, _q, h =>
      HaarCarrierEqv.add
        (HaarCarrierEqv.neg
          (blockAngularLaplacian_carrier
            (hactive block List.mem_cons_self) h))
        (activeCasimirPolynomial_carrier active
          (fun i hi => hactive i (List.mem_cons_of_mem block hi)) h)

/-- If the right factor is independent of every selected block, the complete
literal Casimir differentiates only the left factor. -/
theorem activeCasimirPolynomial_mul_independent :
    ∀ (active : List Nat) (p q : RatPoly),
      (∀ block, block ∈ active → QuaternionBlockIndependent block q) →
      RatPolyCoeffEqv (activeCasimirPolynomial active (polyMul p q))
        (polyMul (activeCasimirPolynomial active p) q)
  | [], p, q, _ => (RatPolyCoeffEqv.mul_zero_left q).symm
  | block::active, p, q, hind => by
      change RatPolyCoeffEqv (polyAdd (polyNeg _) _)
        (polyMul (polyAdd (polyNeg _) _) q)
      have hblock := blockAngularLaplacian_mul_independent block p q
        (hind block List.mem_cons_self)
      have hneg : RatPolyCoeffEqv
          (polyNeg (blockAngularLaplacian block (polyMul p q)))
          (polyMul (polyNeg (blockAngularLaplacian block p)) q) :=
        (RatPolyCoeffEqv.neg hblock).trans
          ((QuaternionHaarAngularCarrier.neg_smul _).trans
            ((RatPolyCoeffEqv.polyMul_smul_left (-1)
              (blockAngularLaplacian block p) q).symm.trans
              ((QuaternionHaarAngularCarrier.neg_smul _).symm.mul_right q)))
      rw [polyMul_add_left_exact]
      exact hneg.add
        (activeCasimirPolynomial_mul_independent active p q
          (fun i hi => hind i (List.mem_cons_of_mem block hi)))

/-- Every valid full cyclic leaf is an eigenvector of the literal output
Casimir, with eigenvalue the sum of its selected representation Casimirs. -/
theorem full_path_activeCasimir_carrier (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (ds : List Nat)
    (hlen : ds.length = tail+1) (hpath : ValidPath tail p ds) :
    HaarCarrierEqv (tail+1)
      (activeCasimirPolynomial (List.range (tail+1)) (pathPiece tail p ds))
      (polySmul (totalCasimir ds) (pathPiece tail p ds)) := by
  let n := tail+1
  let kernel := characterProduct n (pathSlots 0 ds)
  have hbase : HaarCarrierEqv n
      (partialHaarHeads n (polyMul kernel p)) (pathPiece tail p ds) := by
    have hf := character_prefix_fold_carrier n ds p
    rw [hlen] at hf
    exact hf.trans (pathPiece_character_carrier tail ds p hp hpath)
  have hcomm := activeCasimirPolynomial_partialHaarHeads n
    (List.range n) (polyMul kernel p)
  have hkernel := characterProduct_full_upperCasimir n ds hlen
  have hpind : ∀ block,
      block ∈ (List.range n).map (fun i => n+i) →
      QuaternionBlockIndependent block p := by
    intro block hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact supported_upper_independent hp i
  have hpull := activeCasimirPolynomial_mul_independent
    ((List.range n).map fun i => n+i) kernel p hpind
  have hupper : HaarCarrierEqv (n+n)
      (activeCasimirPolynomial ((List.range n).map fun i => n+i)
        (polyMul kernel p))
      (polySmul (totalCasimir ds) (polyMul kernel p)) := by
    exact (RatPolyCoeffEqv.haarCarrier hpull).trans
      ((HaarCarrierEqv.mul_right p hkernel).trans
        (RatPolyCoeffEqv.haarCarrier
          (RatPolyCoeffEqv.polyMul_smul_left
            (totalCasimir ds) kernel p)))
  have hintegrated := partialHaarHeads_carrier (tailBlocks := n)
    (headBlocks := n) hupper
  have hscaled : HaarCarrierEqv n
      (partialHaarHeads n
        (polySmul (totalCasimir ds) (polyMul kernel p)))
      (polySmul (totalCasimir ds)
        (partialHaarHeads n (polyMul kernel p))) :=
    RatPolyCoeffEqv.haarCarrier
      (partialHaarHeads_smul n (totalCasimir ds) (polyMul kernel p))
  exact (activeCasimirPolynomial_carrier (List.range n)
      (fun i hi => List.mem_range.mp hi) hbase.symm).trans
    ((RatPolyCoeffEqv.haarCarrier hcomm).trans
      (hintegrated.trans (hscaled.trans
        (HaarCarrierEqv.smul (totalCasimir ds) hbase))))

end YMGap.Continuum.SU2QuaternionCyclicPathCasimir

#print axioms YMGap.Continuum.SU2QuaternionCyclicPathCasimir.activeCasimirPolynomial_carrier
#print axioms YMGap.Continuum.SU2QuaternionCyclicPathCasimir.activeCasimirPolynomial_mul_independent
#print axioms YMGap.Continuum.SU2QuaternionCyclicPathCasimir.full_path_activeCasimir_carrier
