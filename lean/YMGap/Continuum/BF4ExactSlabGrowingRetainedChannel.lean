/-
# A selected ORIGINAL all-spin channel in every enlarged physical interface

The selected crossing face is translated by the actual bulk geometry.
Its original Gram branch is transported to that face's actual link
polynomial; every other crossing face uses its original unit leaf.
The resulting ACTUAL interface leaf has exactly the source heat weight,
independent of padding and every cutoff retaining the supplied spin.

The original lower action still occurs in its amplitude. The weighted
square is bounded by the full original numerator before and after bulk
cutoff removal, and by the SAME normalized form after multiplication by
the original reciprocal. Only the channel weight is volume-independent;
the amplitudes and reciprocal are not. This does not prove a polynomial
pullback identity between different slabs, thermodynamic coefficient
convergence/separation, transfer injectivity, or continuum/Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabGramChannelTransport
import YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
import YMGap.Continuum.BF4ExactSlabWholePacketNormBound

namespace YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabGramChannelTransport
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels
open YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity
open YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit
open YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.ReflectedSquareTreeRealizedLeaf
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

/-- A decidable scan retains one supplied face and vacuum-fills the others. -/
private def singletonProduct {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) {half id : Nat}
    (c : SpinChannel half id) (hK : c.spin ≤ K) :
    (ids : List Nat) → (physical : ∀ j, j ∈ ids → j ∈ centralFixedFaceIds half) → id ∈ ids →
    RealizedLeaf (LocalSquareExpansion.finiteProduct (faceHeatPolynomial w K half) ids
      (fun j hj => faceExpansion hw K (physical j hj))).tree (facePolynomial c) (faceWeight w c)
  | [], _, h => False.elim (List.not_mem_nil h)
  | j :: ids, physical, h => if hji : j = id then by
      subst j
      let tail := productUnit (faceHeatPolynomial w K half) ids
        (fun k hk => faceExpansion hw K (physical k (List.mem_cons_of_mem id hk)))
        (fun k hk => faceUnit hw K (physical k (List.mem_cons_of_mem id hk)))
      exact (((faceChannel hw K (physical id List.mem_cons_self) c hK).product (.ofUnit tail)).recode
        (RatPolyCoeffEqv.mul_one _)).reweight (Q'.mul_one_eqv _)
    else by
      have hi : id ∈ ids := (List.mem_cons.mp h).resolve_left (Ne.symm hji)
      exact (((RealizedLeaf.ofUnit (faceUnit hw K (physical j List.mem_cons_self))).product
        (singletonProduct hw K c hK ids (fun k hk => physical k (List.mem_cons_of_mem j hk)) hi)).recode
          (RatPolyCoeffEqv.one_mul _)).reweight (Q'.one_mul_eqv _)

def singletonChannel {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) {half id : Nat}
    (hi : id ∈ centralFixedFaceIds half) (c : SpinChannel half id) (hK : c.spin ≤ K) :
    RealizedLeaf (interfaceExpansion hw K half).tree (facePolynomial c) (faceWeight w c) :=
  singletonProduct hw K c hK _ (fun _ h => h) hi

private theorem shifted_fixed {half padding : Nat} {p : ClusterCount4DProgress.Z4Plaq}
    (hp : plaquetteHalfSide half p = .fixed) :
    plaquetteHalfSide (half+padding) (shiftFace padding padding p) = .fixed := by
  obtain ⟨⟨a,b,c,t⟩,plane⟩ := p
  cases plane <;>
    simp only [plaquetteHalfSide, spatialHalfSide, temporalHalfSide, shiftFace, shiftVertex] at hp ⊢ <;>
    split at hp <;> simp_all <;> omega

theorem bulkFaceId_fixed {half padding id : Nat} (hi : id ∈ centralFixedFaceIds half) :
    bulkFaceId half padding 0 id ∈ centralFixedFaceIds (half+padding) := by
  apply mem_centralFixedFaceIds.mpr
  refine ⟨bulkFaceId_physical (mem_centralFixedFaceIds.mp hi).1, ?_⟩
  rw [bulkFaceId_pin (mem_centralFixedFaceIds.mp hi).1, Nat.sub_zero]
  exact shifted_fixed (mem_centralFixedFaceIds.mp hi).2

/-- The same spin, representation column and tensor-row path at the actual new link. -/
def shiftedChannel {half id : Nat} (padding : Nat) (c : SpinChannel half id) :
    SpinChannel (half+padding) (bulkFaceId half padding 0 id) :=
  BF4ExactSlabGramChannelTransport.transport _ _ c

theorem shiftedChannel_spin {half id : Nat} (padding : Nat) (c : SpinChannel half id) :
    (shiftedChannel padding c).spin = c.spin := rfl

private theorem weighted_transport (q r : RationalQuaternionRatPoly.RatPolyQuaternion)
    (c : GramChannel q) (a : Nat → Q') :
    a (BF4ExactSlabGramChannelTransport.transport q r c).spin *
        (BF4ExactSlabGramChannelTransport.transport q r c).leaf.weight = a c.spin * c.leaf.weight := by
  change a c.spin * ((gramTransport q r c.spin).mapLeaf c.leaf).weight = _
  rw [SameWeights.mapLeaf_weight]

theorem shiftedChannel_weight (w : Q') {half id : Nat} (padding : Nat) (c : SpinChannel half id) :
    faceWeight w (shiftedChannel padding c) = faceWeight w c :=
  weighted_transport
    (asRepresentationQuaternion (correctedSlabLinkPolynomial (centralExtent half)
      (faceLinkA (slabPlaquetteAt (centralExtent half) id))))
    (asRepresentationQuaternion (correctedSlabLinkPolynomial (centralExtent (half+padding))
      (faceLinkA (slabPlaquetteAt (centralExtent (half+padding)) (bulkFaceId half padding 0 id))))) c
    (BondMovingStep.coeffW w)

/-- A literal original interface leaf at every larger volume and retained cutoff. -/
def growingChannel {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) {half id : Nat}
    (hi : id ∈ centralFixedFaceIds half) (padding : Nat) (c : SpinChannel half id) (hK : c.spin ≤ K) :
    RealizedLeaf (interfaceExpansion hw K (half+padding)).tree
      (facePolynomial (shiftedChannel padding c)) (faceWeight w c) :=
  (singletonChannel hw K (bulkFaceId_fixed hi) (shiftedChannel padding c) hK).reweight
    (Q'.eqv_of_eq (shiftedChannel_weight w padding c))

/-- No factor is paid for the number of added crossing faces. -/
theorem growingChannel_weight {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) {half id : Nat}
    (hi : id ∈ centralFixedFaceIds half) (padding : Nat) (c : SpinChannel half id) (hK : c.spin ≤ K) :
    Q'.eqv (growingChannel hw K hi padding c hK).leaf.weight (faceWeight w c) :=
  (growingChannel hw K hi padding c hK).weight_pin

theorem growingChannel_positive {w : Q'} (hw : (0 : Q') < w) (K : Nat) {half id : Nat}
    (hi : id ∈ centralFixedFaceIds half) (padding : Nat) (c : SpinChannel half id) (hK : c.spin ≤ K) :
    (0 : Q') < (growingChannel (Q'.le_of_lt hw) K hi padding c hK).leaf.weight :=
  (growingChannel (Q'.le_of_lt hw) K hi padding c hK).weight_positive (faceWeight_positive w hw c)

theorem growingChannel_finite_bound (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) {half id : Nat}
    (hi : id ∈ centralFixedFaceIds half) (padding : Nat) (c : SpinChannel half id) (hK : c.spin ≤ K)
    (e : PlaquetteExpression (half+padding)) :
    faceWeight w c * (lowerMoment w K (half+padding) (polyMul (lower e) (facePolynomial (shiftedChannel padding c))) *
      lowerMoment w K (half+padding) (polyMul (lower e) (facePolynomial (shiftedChannel padding c)))) ≤
      originalQuadratic w K e :=
  realized_bound w hw K (half+padding) (growingChannel hw K hi padding c hK) e

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half id : Nat}
    (hi : id ∈ centralFixedFaceIds half) (padding : Nat) (c : SpinChannel half id)
    (e : PlaquetteExpression (half+padding))

local notation "blocks" => List.length (boundaryCompleteSlabLinks (centralExtent (half+padding)))
local notation "originalLimit" => numeratorLimit w hw0 hw1 blocks (centralExtent (half+padding))
  (slabPhysicalFaceEdges (centralExtent (half+padding))) (reflectedInsertion e)
local notation "amplitude" => coefficientLimit w hw0 hw1 (half+padding)
  (polyMul (lower e) (facePolynomial (shiftedChannel padding c)))

include hi in
theorem growingChannel_bulk_bound :
    leEv (CReal.mul (ofQ' (faceWeight w c)) (CReal.mul amplitude amplitude)) originalLimit := by
  apply leEv_of_ofQ'_limit_le
    (energy_converges w hw0 hw1 (half+padding) (lower e)
      (.term (faceWeight w c) (facePolynomial (shiftedChannel padding c)))
      (Q'.le_of_lt (faceWeight_positive w hw0 c)))
    (numerator_converges w hw0 hw1 blocks (centralExtent (half+padding))
      (slabPhysicalFaceEdges (centralExtent (half+padding))) (reflectedInsertion e))
  intro epsilon he
  exact ⟨c.spin, fun K hK => Q'.le_trans' _ _ _
    (growingChannel_finite_bound w (Q'.le_of_lt hw0) K hi padding c hK e)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

include hi in
/-- The reciprocal remains explicit and volume-dependent; no uniform floor. -/
theorem growingChannel_normalized_bound :
    leEv (CReal.mul (actionReciprocal w hw0 hw1 (half+padding))
      (CReal.mul (ofQ' (faceWeight w c)) (CReal.mul amplitude amplitude))) (form w hw0 hw1 e e) :=
  leEv_trans (leEv_mul_nonneg_left (reciprocal_nonnegative w hw0 hw1 (half+padding))
    (growingChannel_bulk_bound w hw0 hw1 hi padding c e))
    (leEv_of_equiv ((CRealAlg.cmul_comm _ _).trans (expectation_reflection_eq_upper w e e hw0 hw1)))

end YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel

#print axioms YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel.singletonChannel
#print axioms YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel.bulkFaceId_fixed
#print axioms YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel.shiftedChannel
#print axioms YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel.shiftedChannel_spin
#print axioms YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel.shiftedChannel_weight
#print axioms YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel.growingChannel
#print axioms YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel.growingChannel_weight
#print axioms YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel.growingChannel_positive
#print axioms YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel.growingChannel_finite_bound
#print axioms YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel.growingChannel_bulk_bound
#print axioms YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel.growingChannel_normalized_bound
