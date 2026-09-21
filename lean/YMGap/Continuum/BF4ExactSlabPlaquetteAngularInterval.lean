/-
# Actual selected-link plaquette derivative certificates

The literal four-link Hamilton product is differentiated by Leibniz's rule.
Each coordinate has value cap one and angular-derivative cap two. Keeping
the original identity start and all four component channels gives the
conservative numerical derivative cap 2048. It is independent of extent,
face, selected link, heat cutoff and nome, and is not asserted sharp.

Block reindexing is transported at original Haar-carrier equality, including
derivatives via tangential integration by parts. No pointwise bound or
deleted-action measure is used.
-/

import YMGap.Continuum.QuaternionHaarAngularProductBounds
import YMGap.Continuum.BF4ExactSlabLinkStarGeometry
import YMGap.Continuum.QuaternionHaarHeatAngularDerivative
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics

namespace YMGap.Continuum.BF4ExactSlabPlaquetteAngularInterval

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
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

private theorem supported_reindex {B : Nat} (s : QuaternionBlockInvolution B) (p : PolyQuaternion) :
    Supported B (reindexPolyQuaternion s p) :=
  ⟨reindex_supported s p.scalar, reindex_supported s p.iPart,
    reindex_supported s p.jPart, reindex_supported s p.kPart⟩

private def reindexedOneBound {B i j : Nat} (hb : 0 < B) (hi : i < 4) (hj : j < 4)
    (s : QuaternionBlockInvolution B) :
    QuaternionBound B i j (reindexPolyQuaternion s PolyQuaternion.one) 1 0 :=
  QuaternionBound.ofPrefix hb hi hj (supported_reindex s _) (reindex_polyQuaternionOne_prefix s)
    (QuaternionBound.one hb hi hj)

private def reindexedLinkBound {i j : Nat} (extent : Nat) (hb : 0 < blocks extent)
    (hi : i < 4) (hj : j < 4) (s : QuaternionBlockInvolution (blocks extent)) (link : Z4Link) :
    QuaternionBound (blocks extent) i j (reindexPolyQuaternion s (correctedSlabLinkPolynomial extent link)) 1 2 := by
  by_cases hl : link ∈ boundaryCompleteSlabLinks extent
  · rw [correctedSlabLinkPolynomial_of_mem hl]
    have hk := List.idxOf_lt_length_of_mem hl
    exact QuaternionBound.ofPrefix hb hi hj (supported_reindex s _)
      (reindex_coordinateVariable_prefix s (s.map_lt _ hk) (s.involutive _ hk))
      (QuaternionBound.coordinate hb hi hj (s.map_lt _ hk))
  · rw [correctedSlabLinkPolynomial_of_not_mem hl]
    exact (reindexedOneBound hb hi hj s).weaken (Q'.le_refl' _) (by decide)

private def reindexedOrientedBound {i j : Nat} (extent : Nat) (hb : 0 < blocks extent)
    (hi : i < 4) (hj : j < 4) (s : QuaternionBlockInvolution (blocks extent)) (entry : OrientedBF4Link) :
    QuaternionBound (blocks extent) i j
      (reindexPolyQuaternion s (orientedCorrectedSlabLinkPolynomial extent entry)) 1 2 := by
  unfold orientedCorrectedSlabLinkPolynomial
  split
  · rw [reindexPolyQuaternion_conj]
    exact (reindexedLinkBound extent hb hi hj s entry.link).conj hb hi hj
  · exact reindexedLinkBound extent hb hi hj s entry.link

private def fourFactorDerivative {B i j : Nat} (hb : 0 < B) (hi : i < 4) (hj : j < 4)
    {p q r t u : PolyQuaternion} (P : QuaternionBound B i j p 1 0)
    (Q : QuaternionBound B i j q 1 2) (R : QuaternionBound B i j r 1 2)
    (T : QuaternionBound B i j t 1 2) (U : QuaternionBound B i j u 1 2) :
    Interval B (SU2QuaternionAngularDerivative.angularDerivative i j
      (PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul p q) r) t) u).scalar) 2048 :=
  ((((P.mul hb hi hj Q).mul hb hi hj R).mul hb hi hj T).mul hb hi hj U).scalar.derivative.changeCap (by decide)

private def scalarIntervalOfReindexedEquality {B i j : Nat} {p q : PolyQuaternion} {c : Q'}
    (s : QuaternionBlockInvolution B) (h : reindexPolyQuaternion s p = q)
    (Q : Interval B (SU2QuaternionAngularDerivative.angularDerivative i j q.scalar) c) :
    Interval B (SU2QuaternionAngularDerivative.angularDerivative i j (reindexQuaternionPolynomial s p.scalar)) c := by
  rw [← h] at Q
  exact Q

/-- An explicit interval for the derivative of the ORIGINAL four-link scalar,
after any supported block involution. No physical-face or incidence premise
is needed for this conservative bound; the identity fallback is covered. -/
def plaquetteAngularInterval {i j : Nat} (extent : Nat) (hb : 0 < blocks extent)
    (hi : i < 4) (hj : j < 4) (s : QuaternionBlockInvolution (blocks extent)) (face : Z4Plaq) :
    Interval (blocks extent)
      (SU2QuaternionAngularDerivative.angularDerivative i j
        (reindexQuaternionPolynomial s (correctedSlabPlaquettePolynomial extent face).scalar)) 2048 := by
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
    (fourFactorDerivative hb hi hj (reindexedOneBound hb hi hj s)
      (reindexedOrientedBound extent hb hi hj s e0)
      (reindexedOrientedBound extent hb hi hj s e1)
      (reindexedOrientedBound extent hb hi hj s e2)
      (reindexedOrientedBound extent hb hi hj s e3))

/-- The SAME selected-link frame used by the original-action local Ward score. -/
def selectedPlaquetteAngularInterval {i j : Nat} (hi : i < 4) (hj : j < 4)
    (extent : Nat) (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent) (face : Z4Plaq) :
    Interval (blocks extent)
      (SU2QuaternionAngularDerivative.angularDerivative i j
        (reindexQuaternionPolynomial (linkHeadSwap extent link hl)
          (correctedSlabPlaquettePolynomial extent face).scalar)) 2048 :=
  plaquetteAngularInterval extent
    (Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)) hi hj
    (linkHeadSwap extent link hl) face

end YMGap.Continuum.BF4ExactSlabPlaquetteAngularInterval

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAngularInterval.plaquetteAngularInterval
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAngularInterval.selectedPlaquetteAngularInterval
