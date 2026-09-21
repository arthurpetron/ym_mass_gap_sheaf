/-
# Cutoff- and extent-independent derivative caps for actual slab heat factors

The original physical face supplies its unit scalar certificate; the proved
four-link derivative certificate supplies the former missing DX input.
Character-prefix reindexing is pinned in the original Haar carrier before
transporting its angular derivative. Thus the final interval bounds the
literal factor used in the selected-link Ward frame.

The cap is 4096 times the explicit quartic heat budget at the stated nome.
It is independent of cutoff and extent, not uniform as the nome tends to one.
No Ward response floor or energy/variance comparison is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteAngularInterval

namespace YMGap.Continuum.BF4ExactSlabHeatAngularInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteAngularInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate (heatTerm prefixInterval)
open YMGap.Continuum.QuaternionHaarHeatAngularDerivative
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private def squareReindex {blocks : Nat} {x : RatPoly} {c : Q'}
    (s : QuaternionBlockInvolution blocks) (X : SquareBound blocks x c) :
    SquareBound blocks (reindexQuaternionPolynomial s x) c where
  support := reindex_supported s x
  nonnegative := X.nonnegative
  certificate := by
    have hs : SupportedQuaternionBlocks blocks (gap c x) :=
      supported_add (polySmul_supported (supported_one blocks) c)
        (by
          intro t ht
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
          exact supported_polyMul X.support X.support u hu)
    have C := reindex_certificate s hs X.certificate
    simp only [gap, cap, reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_smul,
      reindexQuaternionPolynomial_neg, reindexQuaternionPolynomial_mul] at C
    have hone := carrierOfPrefix (reindex_supported s polyOne) (supported_one blocks)
      (reindex_polyOne_prefix s)
    exact .transport (HaarCarrierEqv.add (HaarCarrierEqv.symm (HaarCarrierEqv.smul c hone))
      (HaarCarrierEqv.refl blocks _)) C

private theorem reindexHeatList {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (w : Q') (x : RatPoly) : ∀ ids : List Nat,
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial s (finitePolySum (heatTerm w x) ids))
      (finitePolySum (heatTerm w (reindexQuaternionPolynomial s x)) ids)
  | [] => .nil
  | n :: ids => by
      change QuaternionPrefixPolynomialEqv blocks
        (reindexQuaternionPolynomial s (polyAdd (heatTerm w x n) (finitePolySum (heatTerm w x) ids))) _
      rw [reindexQuaternionPolynomial_add]
      apply QuaternionPrefixPolynomialEqv.append
      · unfold heatTerm
        rw [reindexQuaternionPolynomial_smul]
        exact QuaternionPrefixPolynomialEqv.smul (coeffW w n) (reindexQuaternionPolynomial_character_prefix s x n)
      · exact reindexHeatList s w x ids

/-- Reindex the original prefix, not just its scalar argument, and then
differentiate: the literal two routes are joined in original Haar order. -/
def reindexedHeatAngularInterval {blocks i j : Nat} {x : RatPoly} {d w : Q'}
    (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : QuaternionBlockInvolution blocks) (X : SquareBound blocks x 1)
    (DX : Interval blocks (angularDerivative i j (reindexQuaternionPolynomial s x)) d) (K : Nat) :
    Interval blocks (angularDerivative i j (reindexQuaternionPolynomial s (heatPrefix w K x)))
      (heatDerivativeCap w d) := by
  let XR := squareReindex s X
  have h := carrierOfPrefix (reindex_supported s (heatPrefix w K x))
    (prefixInterval hw0 hw1 XR K).support (reindexHeatList s w x (List.range (K+1)))
  exact intervalOfCarrier (angularDerivative_supported hb hi hj (reindex_supported s _))
    (angularDerivative_carrier hb hi hj h) (heatPrefixAngularInterval hb hi hj hw0 hw1 XR DX K)

/-- Explicit nome-dependent cap; 2*2048=4096 times the quartic prefix budget. -/
def faceAngularCap (w : Q') : Q' := heatDerivativeCap w 2048

/-- All missing scalar-derivative inputs are constructed for the actual
physical face and SAME selected-link frame. Every finite cutoff is allowed. -/
def selectedFaceHeatAngularInterval {i j : Nat} (hi : i < 4) (hj : j < 4)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent)
    (id : Nat) (hid : id ∈ slabPhysicalFaceEdges extent) :
    Interval (boundaryCompleteSlabLinks extent).length
      (angularDerivative i j (reindexQuaternionPolynomial (linkHeadSwap extent link hl)
        (faceHeatPolynomial w K extent id))) (faceAngularCap w) := by
  have hb := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  let X := SquareBound.scalar (supported_slabPlaquette extent (slabPlaquetteAt extent id))
    (haarNorm_slabPlaquette (slabPlaquetteAt_mem hid))
  let DX := selectedPlaquetteAngularInterval hi hj extent link hl (slabPlaquetteAt extent id)
  rw [faceHeatPolynomial_eq_sum]
  exact reindexedHeatAngularInterval hb hi hj hw0 hw1 (linkHeadSwap extent link hl) X DX K

/-- The squared derivative cost against any original positive background.
No disjointness, independence, partition replacement or late-cutoff guard. -/
theorem selectedFaceHeatAngularSquare_bound {i j : Nat} (hi : i < 4) (hj : j < 4)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent)
    (id : Nat) (hid : id ∈ slabPhysicalFaceEdges extent) {r : RatPoly}
    (R : Certificate (boundaryCompleteSlabLinks extent).length r) :
    let d := angularDerivative i j (reindexQuaternionPolynomial (linkHeadSwap extent link hl)
      (faceHeatPolynomial w K extent id))
    Q'.abs (quaternionHaar (boundaryCompleteSlabLinks extent).length (polyMul r (polyMul d d))) ≤
      (faceAngularCap w * faceAngularCap w) * quaternionHaar (boundaryCompleteSlabLinks extent).length r := by
  let D := selectedFaceHeatAngularInterval hi hj hw0 hw1 K extent link hl id hid
  exact (D.mul D).weighted_haar_bound R

end YMGap.Continuum.BF4ExactSlabHeatAngularInterval

#print axioms YMGap.Continuum.BF4ExactSlabHeatAngularInterval.reindexedHeatAngularInterval
#print axioms YMGap.Continuum.BF4ExactSlabHeatAngularInterval.faceAngularCap
#print axioms YMGap.Continuum.BF4ExactSlabHeatAngularInterval.selectedFaceHeatAngularInterval
#print axioms YMGap.Continuum.BF4ExactSlabHeatAngularInterval.selectedFaceHeatAngularSquare_bound
