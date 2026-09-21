/-
# Actual selected-link plaquette second derivative certificates

The original ordered four-link Hamilton product carries explicit caps for
its value, first derivative and second derivative. Coordinate caps (1,2,4)
and Leibniz give (256,2048,16384), with the original identity start retained.
These are conservative constants, independent of extent, cutoff and nome.
No new analytic hypothesis or change of Haar carrier is used.
-/

import YMGap.Continuum.QuaternionHaarSecondAngularBounds
import YMGap.Continuum.BF4ExactSlabLinkStarGeometry
import YMGap.Continuum.QuaternionHaarHeatAngularDerivative
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics

namespace YMGap.Continuum.BF4ExactSlabPlaquetteSecondAngularInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarAngularProductBounds
open YMGap.Continuum.QuaternionHaarSecondAngularBounds
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

private theorem supported_reindex {B : Nat} (s : QuaternionBlockInvolution B) (p : PolyQuaternion) :
    Supported B (reindexPolyQuaternion s p) :=
  ⟨reindex_supported s p.scalar, reindex_supported s p.iPart,
    reindex_supported s p.jPart, reindex_supported s p.kPart⟩

private def reindexedOneBound {B i j : Nat} (hb : 0 < B) (hi : i < 4) (hj : j < 4)
    (s : QuaternionBlockInvolution B) :
    QuaternionSecondBound B i j (reindexPolyQuaternion s PolyQuaternion.one) 1 0 0 :=
  QuaternionSecondBound.ofPrefix hb hi hj (supported_reindex s _) (reindex_polyQuaternionOne_prefix s)
    (QuaternionSecondBound.one hb hi hj)

private def reindexedLinkBound {i j : Nat} (extent : Nat) (hb : 0 < blocks extent)
    (hi : i < 4) (hj : j < 4) (s : QuaternionBlockInvolution (blocks extent)) (link : Z4Link) :
    QuaternionSecondBound (blocks extent) i j (reindexPolyQuaternion s (correctedSlabLinkPolynomial extent link)) 1 2 4 := by
  by_cases hl : link ∈ boundaryCompleteSlabLinks extent
  · rw [correctedSlabLinkPolynomial_of_mem hl]
    have hk := List.idxOf_lt_length_of_mem hl
    exact QuaternionSecondBound.ofPrefix hb hi hj (supported_reindex s _)
      (reindex_coordinateVariable_prefix s (s.map_lt _ hk) (s.involutive _ hk))
      (QuaternionSecondBound.coordinate hb hi hj (s.map_lt _ hk))
  · rw [correctedSlabLinkPolynomial_of_not_mem hl]
    exact (reindexedOneBound hb hi hj s).weaken (Q'.le_refl' _) (by decide) (by decide)

private def reindexedOrientedBound {i j : Nat} (extent : Nat) (hb : 0 < blocks extent)
    (hi : i < 4) (hj : j < 4) (s : QuaternionBlockInvolution (blocks extent)) (entry : OrientedBF4Link) :
    QuaternionSecondBound (blocks extent) i j
      (reindexPolyQuaternion s (orientedCorrectedSlabLinkPolynomial extent entry)) 1 2 4 := by
  unfold orientedCorrectedSlabLinkPolynomial
  split
  · rw [reindexPolyQuaternion_conj]
    exact (reindexedLinkBound extent hb hi hj s entry.link).conj hb hi hj
  · exact reindexedLinkBound extent hb hi hj s entry.link

private def fourFactorSecondDerivative {B i j : Nat} (hb : 0 < B) (hi : i < 4) (hj : j < 4)
    {p q r t u : PolyQuaternion} (P : QuaternionSecondBound B i j p 1 0 0)
    (Q : QuaternionSecondBound B i j q 1 2 4) (R : QuaternionSecondBound B i j r 1 2 4)
    (T : QuaternionSecondBound B i j t 1 2 4) (U : QuaternionSecondBound B i j u 1 2 4) :
    AngularBound B i j (SU2QuaternionAngularDerivative.angularDerivative i j
      (PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul p q) r) t) u).scalar) 2048 16384 :=
  ((((P.mul hb hi hj Q).mul hb hi hj R).mul hb hi hj T).mul hb hi hj U).scalar.derivative.changeCaps (by decide) (by decide)

private def scalarIntervalOfReindexedEquality {B i j : Nat} {p q : PolyQuaternion} {c d : Q'}
    (s : QuaternionBlockInvolution B) (h : reindexPolyQuaternion s p = q)
    (Q : AngularBound B i j (SU2QuaternionAngularDerivative.angularDerivative i j q.scalar) c d) :
    AngularBound B i j (SU2QuaternionAngularDerivative.angularDerivative i j (reindexQuaternionPolynomial s p.scalar)) c d := by
  rw [← h] at Q
  exact Q

/-- Explicit first and second derivative intervals for the ORIGINAL four-link scalar,
after any supported block involution. No physical-face or incidence premise
is needed for this conservative bound; the identity fallback is covered. -/
def plaquetteSecondAngularInterval {i j : Nat} (extent : Nat) (hb : 0 < blocks extent)
    (hi : i < 4) (hj : j < 4) (s : QuaternionBlockInvolution (blocks extent)) (face : Z4Plaq) :
    AngularBound (blocks extent) i j
      (SU2QuaternionAngularDerivative.angularDerivative i j
        (reindexQuaternionPolynomial s (correctedSlabPlaquettePolynomial extent face).scalar)) 2048 16384 := by
  let a := (dirsOf face.2).1
  let b := (dirsOf face.2).2
  let e0 : OrientedBF4Link := ⟨(face.1, a), false⟩
  let e1 : OrientedBF4Link := ⟨(addE face.1 a, b), false⟩
  let e2 : OrientedBF4Link := ⟨(addE face.1 b, a), true⟩
  let e3 : OrientedBF4Link := ⟨(face.1, b), true⟩
  have hpin : reindexPolyQuaternion s (correctedSlabPlaquettePolynomial extent face) =
      PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul
        (reindexPolyQuaternion s PolyQuaternion.one)
        (reindexPolyQuaternion s (orientedCorrectedSlabLinkPolynomial extent e0)))
        (reindexPolyQuaternion s (orientedCorrectedSlabLinkPolynomial extent e1)))
        (reindexPolyQuaternion s (orientedCorrectedSlabLinkPolynomial extent e2)))
        (reindexPolyQuaternion s (orientedCorrectedSlabLinkPolynomial extent e3)) := by
    simp only [correctedSlabPlaquettePolynomial, orientedPlaquetteBoundary, List.foldl_cons,
      List.foldl_nil, reindexPolyQuaternion_mul, a, b, e0, e1, e2, e3]
  exact scalarIntervalOfReindexedEquality s hpin
    (fourFactorSecondDerivative hb hi hj (reindexedOneBound hb hi hj s)
      (reindexedOrientedBound extent hb hi hj s e0)
      (reindexedOrientedBound extent hb hi hj s e1)
      (reindexedOrientedBound extent hb hi hj s e2)
      (reindexedOrientedBound extent hb hi hj s e3))

/-- The SAME selected-link frame used by the original-action local Ward score. -/
def selectedPlaquetteSecondAngularInterval {i j : Nat} (hi : i < 4) (hj : j < 4)
    (extent : Nat) (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent) (face : Z4Plaq) :
    AngularBound (blocks extent) i j
      (SU2QuaternionAngularDerivative.angularDerivative i j
        (reindexQuaternionPolynomial (linkHeadSwap extent link hl)
          (correctedSlabPlaquettePolynomial extent face).scalar)) 2048 16384 :=
  plaquetteSecondAngularInterval extent
    (Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)) hi hj
    (linkHeadSwap extent link hl) face

end YMGap.Continuum.BF4ExactSlabPlaquetteSecondAngularInterval

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSecondAngularInterval.plaquetteSecondAngularInterval
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSecondAngularInterval.selectedPlaquetteSecondAngularInterval
