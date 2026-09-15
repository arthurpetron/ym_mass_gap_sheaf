/-
# Fixed ORIGINAL crossing packets reconstruct the full action limit

First remove the bulk spin cutoff, retaining a fixed finite crossing heat
packet and all original shared links. The bulk-uniform crossing remainder
then proves that these limits converge to the pre-existing ORIGINAL full
reflected numerator limit. Both the crossing-packet threshold and the
CReal representative threshold are explicit Type-level functions.

This is a two-stage action-limit theorem at fixed finite volume and nome.
It does not yet identify each limiting packet with a sum of the retained
limiting channel squares, prove channel completeness in the completed
norm, control growing volume, or prove completed transfer range density.
Full-space zero-time continuity, physical scaling and Clay remain open.
-/

import YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail
import YMGap.Continuum.BoundedRationalCauchyProduct

namespace YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity
open YMGap.Continuum.BF4ExactSlabMixedInterfacePin
open YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

private theorem reorder (p L I : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul p L) I) (polyMul (polyMul p I) L) :=
  (RatPolyCoeffEqv.mul_assoc p L I).trans
    (((RatPolyCoeffEqv.mul_comm L I).mul_left p).trans (RatPolyCoeffEqv.mul_assoc p I L).symm)

/-- Exactly the original lower and upper face lists; crossing faces excluded. -/
def bulkFaceIds (half : Nat) : List Nat := centralLowerFaceIds half ++ centralUpperFaceIds half

def packetInsertion (v : Q') (N : Nat) {half : Nat} (e : PlaquetteExpression half) : RatPoly :=
  polyMul (polyMul (lower e) (upper e)) (interfaceHeatProduct v N half)

def packetSequence (b v : Q') (N : Nat) {half : Nat} (e : PlaquetteExpression half) (B : Nat) : Q' :=
  numerator b (boundaryCompleteSlabLinks (centralExtent half)).length (centralExtent half)
    (bulkFaceIds half) (packetInsertion v N e) B

/-- Only regrouping of ORIGINAL polynomial factors inside the SAME Haar integral. -/
theorem mixed_packet_pin (b v : Q') (B N : Nat) {half : Nat} (e : PlaquetteExpression half) :
    mixedQuadratic b v B N e ≈ packetSequence b v N e B :=
  Q'.eqv_trans _ _ _ (mixedQuadratic_eq_bulkHaar b v B N e)
    (haar_of_coeff_eqv _ ((reorder (polyMul (lower e) (upper e))
      (polyMul (lowerHeatProduct b B half) (upperHeatProduct b B half))
      (interfaceHeatProduct v N half)).trans
        ((polynomialProduct_append (faceHeatPolynomial b B (centralExtent half))
          (centralLowerFaceIds half) (centralUpperFaceIds half)).symm.mul_left _)))

def packetCauchy (b v : Q') (hb0 : (0 : Q') < b) (hb1 : b < (1 : Q'))
    (N : Nat) {half : Nat} (e : PlaquetteExpression half) : CReal.QCauchy (packetSequence b v N e) :=
  numeratorCauchy b hb0 hb1 _ _ _ _

def packetLimit (b v : Q') (hb0 : (0 : Q') < b) (hb1 : b < (1 : Q'))
    (N : Nat) {half : Nat} (e : PlaquetteExpression half) : CReal :=
  numeratorLimit b hb0 hb1 (boundaryCompleteSlabLinks (centralExtent half)).length (centralExtent half)
    (bulkFaceIds half) (packetInsertion v N e)

def packetLimitCauchy (b v : Q') (hb0 : (0 : Q') < b) (hb1 : b < (1 : Q'))
    (N : Nat) {half : Nat} (e : PlaquetteExpression half) :
    CReal.QCauchy (packetLimit b v hb0 hb1 N e).approx :=
  BoundedRationalCauchyProduct.representativeCauchy _ (packetCauchy b v hb0 hb1 N e)

theorem packet_converges (b v : Q') (hb0 : (0 : Q') < b) (hb1 : b < (1 : Q'))
    (N : Nat) {half : Nat} (e : PlaquetteExpression half) :
    CReal.ConvergesTo (fun B => CReal.ofQ' (packetSequence b v N e B)) (packetLimit b v hb0 hb1 N e) :=
  numerator_converges b hb0 hb1 _ _ _ _

theorem mixed_approx_close (b v : Q') (hb0 : (0 : Q') < b) (hb1 : b < (1 : Q'))
    (N : Nat) {half : Nat} (e : PlaquetteExpression half) (epsilon : Q') (he : (0 : Q') < epsilon)
    (B n : Nat) (hB : (packetCauchy b v hb0 hb1 N e).M epsilon ≤ B)
    (hn : (packetCauchy b v hb0 hb1 N e).M epsilon ≤ n) :
    mixedQuadratic b v B N e ≤ (packetLimit b v hb0 hb1 N e).approx n + epsilon ∧
    (packetLimit b v hb0 hb1 N e).approx n ≤ mixedQuadratic b v B N e + epsilon := by
  have h := numerator_approx_close b hb0 hb1 (boundaryCompleteSlabLinks (centralExtent half)).length
    (centralExtent half) (bulkFaceIds half) (packetInsertion v N e) epsilon he B n hB hn
  have hp := mixed_packet_pin b v B N e
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) h.1,
    Q'.le_trans' _ _ _ h.2 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv hp))⟩

theorem mixed_converges (b v : Q') (hb0 : (0 : Q') < b) (hb1 : b < (1 : Q'))
    (N : Nat) {half : Nat} (e : PlaquetteExpression half) :
    CReal.ConvergesTo (fun B => CReal.ofQ' (mixedQuadratic b v B N e)) (packetLimit b v hb0 hb1 N e) :=
  fun epsilon he => ⟨(packetCauchy b v hb0 hb1 N e).M epsilon, fun B hB =>
    ⟨(packetCauchy b v hb0 hb1 N e).M epsilon, fun n hn => mixed_approx_close b v hb0 hb1 N e epsilon he B n hB hn⟩⟩

private theorem quarter_chain (epsilon : Q') (he : (0 : Q') < epsilon)
    (u v x z : Q')
    (hu : u ≤ v + HalfPow.half * (HalfPow.half * epsilon))
    (hv : v ≤ x + HalfPow.half * (HalfPow.half * epsilon))
    (hx : x ≤ z + HalfPow.half * (HalfPow.half * epsilon)) : u ≤ z + epsilon := by
  let q : Q' := HalfPow.half * (HalfPow.half * epsilon)
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon he)
  have hsum : u ≤ ((z + q) + q) + q :=
    Q'.le_trans' _ _ _ hu (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hv)
      (Q'.add_le_add_right _ _ q (Q'.add_le_add_right _ _ q hx)))
  have hbudget : (((z + q) + q) + q) + q ≈ z + epsilon := by
    have hfour : ((q + q) + q) + q ≈ epsilon :=
      Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (q + q) q q)
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
          (ExpNeg.two_halves (HalfPow.half * epsilon)) (ExpNeg.two_halves (HalfPow.half * epsilon)))
          (ExpNeg.two_halves epsilon))
    exact Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv ((z + q) + q) q q)
      (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (z + q) q (q + q))
        (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv z q (q + (q + q)))
          (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
            (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv q q (q + q)))
              (Q'.eqv_symm (Q'.add_assoc_eqv (q + q) q q))) hfour))))
  exact Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ q (Q'.le_of_lt hq)) (Q'.le_of_eqv hbudget))

def reconstructionCutoff (w : Q') {half : Nat} (e : PlaquetteExpression half) (epsilon : Q') : Nat :=
  crossingCutoff w w e (HalfPow.half * (HalfPow.half * epsilon))

/-- The numerical representative threshold may depend on the retained packet N. -/
def reconstructionApproxCutoff (w : Q') {half : Nat} (e : PlaquetteExpression half)
    (N : Nat) (epsilon : Q') : Nat :=
  max (numeratorCutoff w (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
    (reflectedInsertion e) (HalfPow.half * (HalfPow.half * epsilon)))
    (numeratorCutoff w (centralExtent half) (bulkFaceIds half)
      (packetInsertion w N e) (HalfPow.half * (HalfPow.half * epsilon)))

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat} (e : PlaquetteExpression half)

local notation "originalLimit" => numeratorLimit w hw0 hw1
  (List.length (boundaryCompleteSlabLinks (centralExtent half))) (centralExtent half)
  (slabPhysicalFaceEdges (centralExtent half)) (reflectedInsertion e)

/-- Explicit two-stage estimate against the EXISTING full original limit. -/
theorem packetLimit_original_approx_close (epsilon : Q') (he : (0 : Q') < epsilon) (N n : Nat)
    (hN : reconstructionCutoff w e epsilon ≤ N)
    (hn : reconstructionApproxCutoff w e N epsilon ≤ n) :
    (packetLimit w w hw0 hw1 N e).approx n ≤ (originalLimit).approx n + epsilon ∧
    (originalLimit).approx n ≤ (packetLimit w w hw0 hw1 N e).approx n + epsilon := by
  let q : Q' := HalfPow.half * (HalfPow.half * epsilon)
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon he)
  have hna : numeratorCutoff w (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
      (reflectedInsertion e) q ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnb : (packetCauchy w w hw0 hw1 N e).M q ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  let B := max N n
  have hnB : n ≤ B := Nat.le_max_right _ _
  have ha := numerator_approx_close w hw0 hw1 (boundaryCompleteSlabLinks (centralExtent half)).length
    (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) (reflectedInsertion e)
    q hq B n (Nat.le_trans hna hnB) hna
  have hb := mixed_approx_close w w hw0 hw1 N e q hq B n (Nat.le_trans hnb hnB) hnb
  have ht := original_diagonal_close hw0 hw1 e q hq N B hN (Nat.le_max_left _ _)
  exact ⟨quarter_chain epsilon he _ _ _ _ hb.2 ht.2 ha.1,
    quarter_chain epsilon he _ _ _ _ ha.2 ht.1 hb.1⟩

theorem packetLimit_converges :
    CReal.ConvergesTo (fun N => packetLimit w w hw0 hw1 N e) originalLimit :=
  fun epsilon he => ⟨reconstructionCutoff w e epsilon, fun N hN =>
    ⟨reconstructionApproxCutoff w e N epsilon, fun n hn =>
      packetLimit_original_approx_close w hw0 hw1 e epsilon he N n hN hn⟩⟩

/-- Both limit-stage choices are data, not extracted from Prop-level convergence. -/
def reconstructionCertificate (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' N₀ : Nat, Σ' M : Nat → Nat, ∀ N n : Nat, N₀ ≤ N → M N ≤ n →
      ((packetLimit w w hw0 hw1 N e).approx n ≤ (originalLimit).approx n + epsilon ∧
       (originalLimit).approx n ≤ (packetLimit w w hw0 hw1 N e).approx n + epsilon) :=
  ⟨reconstructionCutoff w e epsilon, fun N => reconstructionApproxCutoff w e N epsilon,
    fun N n hN hn => packetLimit_original_approx_close w hw0 hw1 e epsilon he N n hN hn⟩

end YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit

#print axioms YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit.bulkFaceIds
#print axioms YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit.packetInsertion
#print axioms YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit.packetSequence
#print axioms YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit.mixed_packet_pin
#print axioms YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit.packetCauchy
#print axioms YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit.packetLimit
#print axioms YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit.packetLimitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit.packet_converges
#print axioms YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit.mixed_approx_close
#print axioms YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit.mixed_converges
#print axioms YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit.reconstructionCutoff
#print axioms YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit.reconstructionApproxCutoff
#print axioms YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit.packetLimit_original_approx_close
#print axioms YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit.packetLimit_converges
#print axioms YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit.reconstructionCertificate
