/-
# Two relative Ward estimates on the same multi-affine source

The first estimate applies to each derivative at another block. The second
applies to the original source after an explicit head swap. Both keep the
same weight and squared source norm. Constants are explicit products of
the two original relative derivative costs; no uniform-coupling claim.
-/

import YMGap.Continuum.QuaternionHaarAffineRelativeEnergy
import YMGap.Continuum.QuaternionHaarMixedAngularDegreeBound
import YMGap.Continuum.QuaternionHaarDegreeBoundReindex
import YMGap.Continuum.QuaternionHaarMixedAngularTransport

namespace YMGap.Continuum.QuaternionHaarMixedRelativeEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionBlockDegreeBound
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarRelativePredictionEnergy
open YMGap.Continuum.QuaternionHaarAffineRelativeEnergy
open YMGap.Continuum.QuaternionHaarDegreeBoundReindex
open YMGap.Continuum.QuaternionHaarMixedAngularDegreeBound
open YMGap.Continuum.QuaternionHaarMixedAngularTransport
open YMGap.Continuum.QuaternionHaarBlockAngularCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteAngularSquare
  (reindex_blockAngularSquare_carrier)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The same relative bound at a selected block, transported back from its
explicit head frame. No change of probability law is made. -/
theorem block_energy_le_square {tail block : Nat} {W p : RatPoly} {C : Q'}
    (s : QuaternionBlockInvolution (tail+1)) (hb : block < tail+1)
    (hs : s.map 0 = block) (hC : (0 : Q') < C)
    (R : ∀ i j, i < 4 → j < 4 →
      RelativeBound (tail+1) i j (reindexQuaternionPolynomial s W) C)
    (hW : SupportedQuaternionBlocks (tail+1) W)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hdegree : DegreeLE block 1 p) :
    H (tail+1) (polyMul W (blockAngularSquare block p)) ≤
      energyPredictionFactor C * H (tail+1) (polyMul W (polyMul p p)) := by
  have hmain := angular_energy_le_square hC R (reindex_supported s p)
    (degreeLE_reindex s (Nat.zero_lt_succ tail) hs hdegree)
  have hcarrier := reindex_blockAngularSquare_carrier s (Nat.zero_lt_succ tail) p hp
  rw [hs] at hcarrier
  have he := quaternionHaar_reindex s (polyMul W (blockAngularSquare block p))
    (supported_polyMul hW (blockAngularSquare_supported hb hp))
  rw [reindexQuaternionPolynomial_mul] at he
  have hleft : H (tail+1) (polyMul W (blockAngularSquare block p)) ≈
      H (tail+1) (polyMul (reindexQuaternionPolynomial s W)
        (angularSquare (reindexQuaternionPolynomial s p))) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm he)
      (hcarrier (reindexQuaternionPolynomial s W))
  have hright := quaternionHaar_reindex s (polyMul W (polyMul p p))
    (supported_polyMul hW (supported_polyMul hp hp))
  rw [reindexQuaternionPolynomial_mul, reindexQuaternionPolynomial_mul] at hright
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hmain
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hright)))

/-- Apply the head estimate to all six derivatives in a distinct block.
The remaining energy is that of the original source, not a local summand. -/
theorem mixed_energy_le_block_energy {tail block : Nat} {W p : RatPoly} {C : Q'}
    (hb : block < tail+1) (hne : block ≠ 0) (hC : (0 : Q') < C)
    (R : ∀ i j, i < 4 → j < 4 → RelativeBound (tail+1) i j W C)
    (hp : SupportedQuaternionBlocks (tail+1) p) (hdegree : DegreeLE 0 1 p) :
    H (tail+1) (polyMul W (mixedSquare 0 block p)) ≤
      energyPredictionFactor C * H (tail+1) (polyMul W (blockAngularSquare block p)) := by
  let E := fun i j => H (tail+1) (polyMul W
    (blockAngularSquare 0 (blockAngularDerivative block i j p)))
  let A := fun i j => H (tail+1) (polyMul W
    (polyMul (blockAngularDerivative block i j p) (blockAngularDerivative block i j p)))
  have hd (i j : Nat) (hi : i < 4) (hj : j < 4) :
      E i j ≤ energyPredictionFactor C * A i j :=
    angular_energy_le_square hC R
      (blockAngularDerivative_supported hb hi hj hp)
      (blockAngularDerivative_headDegreeLE_of_ne hne i j hi hj hdegree)
  have hsum := sixValue_mono E (fun i j => energyPredictionFactor C * A i j) hd
  have hfactor := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (sixValue_mul_left (energyPredictionFactor C) A))
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (haar_six (tail+1) W
      (fun i j => polyMul (blockAngularDerivative block i j p)
        (blockAngularDerivative block i j p)))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_six (tail+1) W _))
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hfactor))

/-- The two-edge energy is bounded by the SAME whole-source square with
explicit product cost. Relative certificates are for the same weight in
its two frames, not independent one-link laws. -/
theorem mixed_energy_le_square {tail block : Nat} {W p : RatPoly} {C D : Q'}
    (s : QuaternionBlockInvolution (tail+1)) (hb : block < tail+1)
    (hs : s.map 0 = block) (hne : block ≠ 0)
    (hC : (0 : Q') < C) (hD : (0 : Q') < D)
    (R : ∀ i j, i < 4 → j < 4 → RelativeBound (tail+1) i j W C)
    (S : ∀ i j, i < 4 → j < 4 →
      RelativeBound (tail+1) i j (reindexQuaternionPolynomial s W) D)
    (hW : SupportedQuaternionBlocks (tail+1) W)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hhead : DegreeLE 0 1 p) (hblock : DegreeLE block 1 p) :
    H (tail+1) (polyMul W (mixedSquare 0 block p)) ≤
      (energyPredictionFactor C * energyPredictionFactor D) *
        H (tail+1) (polyMul W (polyMul p p)) := by
  have hfirst := mixed_energy_le_block_energy hb hne hC R hp hhead
  have hsecond := block_energy_le_square s hb hs hD S hW hp hblock
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hsecond
        (Q'.le_of_lt (energyPredictionFactor_positive C)))
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))))

#print axioms block_energy_le_square
#print axioms mixed_energy_le_block_energy
#print axioms mixed_energy_le_square

end YMGap.Continuum.QuaternionHaarMixedRelativeEnergy
