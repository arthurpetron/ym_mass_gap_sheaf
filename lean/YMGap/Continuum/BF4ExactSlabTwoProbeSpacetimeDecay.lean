/-
# Separate literal spacetime probes with a translation-independent amplitude

Each observable retains its original base-box carrier. Its root is shifted
by its own temporal offset; no box containing the gap is used as a probe.
The normalized covariance coefficient is explicit in coupling, base size,
observable bounds and the distance between offsets, and independent of
outer padding and boundary margin. This is the original finite slab law
after representation-cutoff removal, not a replacement probability law.
-/

import YMGap.Continuum.BF4ExactSlabTwoProbeCovariance
import YMGap.Continuum.BF4ExactSlabOffsetSpacetimeExpression
import YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier

namespace YMGap.Continuum.BF4ExactSlabTwoProbeSpacetimeDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding
open YMGap.Continuum.BF4ExactSlabOffsetSpacetimeExpression
open YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier
open YMGap.Continuum.BF4ExactSlabSpacetimeExpression
open YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay (boxSize boxLinkCount)
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
open YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget
open YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay
open YMGap.Continuum.BF4ExactSlabTwoProbeCovariance
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.SepLatticeZ4Linf

/-- Literal root distance is unchanged by the common receding-boundary margin. -/
theorem shifted_root_distance (space time time' margin : Nat) :
    linfDist (shiftFace space (time+margin) originFace) (shiftFace space (time'+margin) originFace) =
      natDist time time' := by
  simp only [linfDist, cPlaq, vComp, shiftFace, shiftVertex, originFace, Nat.zero_add, natDist,
    Nat.sub_self, Nat.zero_add, Nat.add_sub_add_right, Nat.max_self, Nat.zero_max]

/-- All parameters controlling the amplitude and the decay exponent are visible. -/
def boxPairBudget (base : Nat) (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (c d : Q') (separation : Nat) : Q' :=
  ((c*d+c*d)*probePrefactor w hd (boxLinkCount base+boxLinkCount base))*
    tailBudget (2^(boxSize base+boxSize base)*625^(boxSize base+boxSize base)) 625
      (separation+1-(boxSize base+boxSize base)) (adjustedCoreRate w hd) hs

theorem shifted_budget_pin (base space time time' margin : Nat) (w : Q')
    (hd : heatRemainderBound w < 1) (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (c d : Q') :
    distanceBudget
      (shiftedBoxProbe (centralExtent base+1) space (time+margin) (Nat.zero_lt_succ _))
      (shiftedBoxProbe (centralExtent base+1) space (time'+margin) (Nat.zero_lt_succ _)) w hd hs c d =
      boxPairBudget base w hd hs c d (natDist time time') := by
  unfold distanceBudget twoProbeBudget minimumCoreSize countPrefactor totalProbeSize
  rw [shiftedBoxProbe_size, shiftedBoxProbe_size, shiftedBoxProbe_root, shiftedBoxProbe_root,
    shifted_root_distance, List.length_append, shiftedBoxLinks_length, shiftedBoxLinks_length]
  rfl

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

/-- The bound is uniform in both the common padding and the outer boundary margin. -/
theorem placed_covariance_bound
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (base padding time time' margin : Nat) (ht : time ≤ padding+padding) (ht' : time' ≤ padding+padding)
    (e f : SpacetimeExpression base) :
    leEv (CReal.abs (covariance w hw0 hw1 ((base+padding)+margin)
      (evaluate margin (embed ⟨base,padding,time,ht⟩ e))
      (evaluate margin (embed ⟨base,padding,time',ht'⟩ f))))
      (ofQ' (boxPairBudget base w hd hs (bound e+1) (bound f+1) (natDist time time'))) := by
  let P : Placement := ⟨base,padding,time,ht⟩
  let Q : Placement := ⟨base,padding,time',ht'⟩
  have Ip := Interval.ofSquare (squareBound margin (embed P e))
  have Iq := Interval.ofSquare (squareBound margin (embed Q f))
  rw [bound_embed] at Ip Iq
  have h := covariance_distance_bound w hw0 hw1 ((base+padding)+margin) hsmall hd hs _ _
    (bound e+1) (bound f+1) Ip Iq _ _
    (shiftedBoxProbe (centralExtent base+1) (padding+margin) (time+margin) (Nat.zero_lt_succ _))
    (shiftedBoxProbe (centralExtent base+1) (padding+margin) (time'+margin) (Nat.zero_lt_succ _))
    (evaluate_embed_local P margin e) (evaluate_embed_local Q margin f)
  rw [shifted_budget_pin] at h
  exact h

end YMGap.Continuum.BF4ExactSlabTwoProbeSpacetimeDecay

#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeSpacetimeDecay.shifted_root_distance
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeSpacetimeDecay.boxPairBudget
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeSpacetimeDecay.shifted_budget_pin
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeSpacetimeDecay.placed_covariance_bound
