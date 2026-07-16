/-
# Normalized one-sided stability of a canonical local occurrence

The connected-carrier tail is composed with the exact switching
cross-numerator.  Because its two background sums are precisely the large
and embedded-small partitions, division by the positive normalizing
partitions cancels without a volume-dependent loss.
-/

import YMGap.Continuum.Z4CanonicalConnectedCarrierTail
import YMGap.Continuum.Z4CanonicalPolymerSpecification
import YMGap.Continuum.Z4CanonicalRightRootConnectedCarrierTail

namespace YMGap.Continuum.Z4CanonicalOccurrenceStability

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.Z4CanonicalBoundarySwitchSummation
open YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation
open YMGap.Continuum.Z4CanonicalConnectedCarrierTail
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerLocalOccurrence
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4CanonicalRightRootConnectedCarrierTail
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

def occurrenceBoundaryEpsilon (distance : Nat) : Q' :=
  anchorEffectiveRatio ^ (distance + 2) * Q'.ofNat 2

theorem occurrenceBoundaryEpsilon_nonnegative (distance : Nat) :
    (0 : Q') ≤ occurrenceBoundaryEpsilon distance := by
  unfold occurrenceBoundaryEpsilon
  exact Q'.mul_nonneg _ _
    (Q'.pow_nonneg anchorEffectiveRatio
      anchorEffectiveRatio_nonnegative (distance + 2))
    (by decide)

/-! ## 1. Constructive rational normalization lemmas -/

theorem le_add_of_sub_le_local {a b c : Q'}
    (h : a + (-b) ≤ c) : a ≤ b + c := by
  have hadd : (a + (-b)) + b ≤ c + b :=
    Q'.add_le_add_right _ _ _ h
  have hleft : ((a + (-b)) + b).eqv a := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a ((-b) + b) 0
        (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (-b) b)
          (Q'.add_neg_self_eqv b))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' a)
  have hright : (c + b).eqv (b + c) := Q'.add_comm_eqv c b
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright))

/-- Cross multiplication for the repository's positive-denominator quotient. -/
theorem divPos_le_divPos_of_cross_local
    (p q p' q' : Q')
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : p * q' ≤ p' * q) :
    Q'.divPos p q hq ≤ Q'.divPos p' q' hq' := by
  refine Q'.divPos_le_of_le_mul p q hq ?_
  have hr : (0 : Q') ≤ Q'.recipPos q' hq' :=
    Q'.le_of_lt (Q'.recipPos_pos q' hq')
  have hstep :
      (p * q') * Q'.recipPos q' hq' ≤
        (p' * q) * Q'.recipPos q' hq' :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcross hr
  have hleft : ((p * q') * Q'.recipPos q' hq').eqv p := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv p q' (Q'.recipPos q' hq')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left p _ _
        (Q'.mul_recipPos_eqv q' hq')) ?_
    exact Q'.mul_one_eqv p
  have hright :
      ((p' * q) * Q'.recipPos q' hq').eqv
        (Q'.divPos p' q' hq' * q) := by
    unfold Q'.divPos
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv p' q (Q'.recipPos q' hq')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left p' _ _
        (Q'.mul_comm_eqv q (Q'.recipPos q' hq'))) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv p' (Q'.recipPos q' hq') q)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hright))

theorem divPos_add_scaled_eqv
    (p c q : Q') (hq : (0 : Q') < q) :
    Q'.divPos (p + c * q) q hq ≈
      Q'.divPos p q hq + c := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv p (c * q) (Q'.recipPos q hq)) ?_
  refine Q'.add_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv c q (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _
      (Q'.mul_recipPos_eqv q hq)) ?_
  exact Q'.mul_one_eqv c

private theorem sub_swap_eqv_neg_local (a b : Q') :
    b - a ≈ -(a - b) := by
  change (b + -a).eqv (-(a + -b))
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv b (-a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (-a) b (-(-b))
      (Q'.eqv_symm (Q'.neg_neg_eqv b))) ?_
  exact Q'.eqv_symm (Q'.neg_add_eqv a (-b))

/-! ## 2. Cross numerator and normalized occurrence bounds -/

theorem anchorOccurrenceCrossDifference_le_boundaryTail
    {small n inner distance start : Nat} {polymer : List Nat}
    (hsmall : small ≤ n)
    (hpolymer : polymer ∈ canonicalSurfacePolymers small)
    (hstart : start ∈ transportPolymer small n polymer)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    anchorEventNumerator n
          (targetOccurrenceEvent small n polymer) *
          anchorCanonicalPartition small -
        anchorEventNumerator small
          (sourceOccurrenceEvent polymer) *
          anchorCanonicalPartition n ≤
      occurrenceBoundaryEpsilon distance *
        (anchorCanonicalPartition small * anchorCanonicalPartition n) := by
  have hconnected := anchorOccurrenceCrossDifference_le_connected
    hsmall hpolymer
  have htail := connectedSourcePairSum_le_boundaryTail
    hsmall hstart hstartInner hbox
  have hbound := Q'.le_trans' _ _ _ hconnected htail
  have hreorder :
      ((anchorCanonicalPartition n * anchorCanonicalPartition small) *
          occurrenceBoundaryEpsilon distance).eqv
        (occurrenceBoundaryEpsilon distance *
          (anchorCanonicalPartition small * anchorCanonicalPartition n)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv
        (anchorCanonicalPartition n * anchorCanonicalPartition small)
        (occurrenceBoundaryEpsilon distance)) ?_
    exact Q'.mul_eqv_congr_left (occurrenceBoundaryEpsilon distance)
      (anchorCanonicalPartition n * anchorCanonicalPartition small)
      (anchorCanonicalPartition small * anchorCanonicalPartition n)
      (Q'.mul_comm_eqv _ _)
  exact Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hreorder)

theorem anchorOccurrenceProbability_sub_le_boundaryEpsilon
    {small n inner distance start : Nat} {polymer : List Nat}
    (hsmall : small ≤ n)
    (hpolymer : polymer ∈ canonicalSurfacePolymers small)
    (hstart : start ∈ transportPolymer small n polymer)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    anchorEventProbability n (targetOccurrenceEvent small n polymer) -
        anchorEventProbability small (sourceOccurrenceEvent polymer) ≤
      occurrenceBoundaryEpsilon distance := by
  let targetNumerator := anchorEventNumerator n
    (targetOccurrenceEvent small n polymer)
  let sourceNumerator := anchorEventNumerator small
    (sourceOccurrenceEvent polymer)
  let targetPartition := anchorCanonicalPartition n
  let sourcePartition := anchorCanonicalPartition small
  let epsilon := occurrenceBoundaryEpsilon distance
  have hcross :
      targetNumerator * sourcePartition -
          sourceNumerator * targetPartition ≤
        epsilon * (sourcePartition * targetPartition) := by
    exact anchorOccurrenceCrossDifference_le_boundaryTail
      hsmall hpolymer hstart hstartInner hbox
  have hadd :
      targetNumerator * sourcePartition ≤
        sourceNumerator * targetPartition +
          epsilon * (sourcePartition * targetPartition) :=
    le_add_of_sub_le_local hcross
  have hreorder :
      (sourceNumerator * targetPartition +
          epsilon * (sourcePartition * targetPartition)).eqv
        ((sourceNumerator + epsilon * sourcePartition) *
          targetPartition) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left
        (sourceNumerator * targetPartition)
        (epsilon * (sourcePartition * targetPartition))
        ((epsilon * sourcePartition) * targetPartition)
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv epsilon sourcePartition targetPartition))) ?_
    exact Q'.eqv_symm
      (Q'.add_mul_eqv sourceNumerator
        (epsilon * sourcePartition) targetPartition)
  have hratio := divPos_le_divPos_of_cross_local
    targetNumerator targetPartition
    (sourceNumerator + epsilon * sourcePartition) sourcePartition
    (anchorCanonicalPartition_pos n)
    (anchorCanonicalPartition_pos small)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hreorder))
  have hcollapse := divPos_add_scaled_eqv
    sourceNumerator epsilon sourcePartition
    (anchorCanonicalPartition_pos small)
  have hprob :
      anchorEventProbability n (targetOccurrenceEvent small n polymer) ≤
        anchorEventProbability small (sourceOccurrenceEvent polymer) +
          occurrenceBoundaryEpsilon distance := by
    unfold anchorEventProbability
    exact Q'.le_trans' _ _ _ hratio (Q'.le_of_eqv hcollapse)
  exact Q'.sub_le_of_le_add hprob

theorem anchorPolymerOccurrenceProbability_sub_le_boundaryEpsilon
    {small n inner distance start : Nat} {polymer : List Nat}
    (hsmall : small ≤ n)
    (hpolymer : polymer ∈ canonicalSurfacePolymers small)
    (hstart : start ∈ transportPolymer small n polymer)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    anchorPolymerOccurrenceProbability n
          (transportPolymer small n polymer) -
        anchorPolymerOccurrenceProbability small polymer ≤
      occurrenceBoundaryEpsilon distance := by
  simpa [anchorPolymerOccurrenceProbability, targetOccurrenceEvent,
    sourceOccurrenceEvent] using
    anchorOccurrenceProbability_sub_le_boundaryEpsilon
      hsmall hpolymer hstart hstartInner hbox

/-- A source face in the inner box supplies the transported target witness
required by the connected-carrier estimate. -/
theorem anchorPolymerOccurrenceProbability_sub_le_boundaryEpsilon_of_sourceFace
    {small n inner distance sourceFace : Nat} {polymer : List Nat}
    (hsmall : small ≤ n)
    (hpolymer : polymer ∈ canonicalSurfacePolymers small)
    (hsource : sourceFace ∈ polymer)
    (hsourceInner : boxPlaquetteAt small sourceFace ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    anchorPolymerOccurrenceProbability n
          (transportPolymer small n polymer) -
        anchorPolymerOccurrenceProbability small polymer ≤
      occurrenceBoundaryEpsilon distance := by
  obtain ⟨targetFace, htargetFace, hfaceEq⟩ :=
    transportPolymerMemberTarget hsmall
      (canonicalSurfacePolymer_mem_faceSupports hpolymer) hsource
  apply anchorPolymerOccurrenceProbability_sub_le_boundaryEpsilon
    hsmall hpolymer htargetFace
  · rw [← hfaceEq]
    exact hsourceInner
  · exact hbox

/-- Natural local-observable form: if the whole source polymer lies in the
inner box, its transported occurrence changes by at most the boundary tail. -/
theorem anchorPolymerOccurrenceProbability_sub_le_boundaryEpsilon_of_inside
    {small n inner distance : Nat} {polymer : List Nat}
    (hsmall : small ≤ n)
    (hpolymer : polymer ∈ canonicalSurfacePolymers small)
    (hinside : PolymerInsideBox inner small polymer)
    (hbox : inner + distance = small) :
    anchorPolymerOccurrenceProbability n
          (transportPolymer small n polymer) -
        anchorPolymerOccurrenceProbability small polymer ≤
      occurrenceBoundaryEpsilon distance := by
  obtain ⟨sourceFace, hsourceFace⟩ :=
    canonicalSurfacePolymers_allNonempty small polymer hpolymer
  apply anchorPolymerOccurrenceProbability_sub_le_boundaryEpsilon_of_sourceFace
    hsmall hpolymer hsourceFace
  · apply hinside (boxPlaquetteAt small sourceFace)
    exact List.mem_map.mpr ⟨sourceFace, hsourceFace, rfl⟩
  · exact hbox

/-! ## 3. Mirrored normalization and two-sided stability -/

theorem anchorReverseOccurrenceCrossDifference_le_boundaryTail
    {small n inner distance start : Nat} {polymer : List Nat}
    (hsmall : small ≤ n)
    (hpolymer : polymer ∈ canonicalSurfacePolymers small)
    (hstart : start ∈ transportPolymer small n polymer)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    anchorEventNumerator small (sourceOccurrenceEvent polymer) *
          anchorCanonicalPartition n -
        anchorEventNumerator n
          (targetOccurrenceEvent small n polymer) *
          anchorCanonicalPartition small ≤
      occurrenceBoundaryEpsilon distance *
        (anchorCanonicalPartition small * anchorCanonicalPartition n) := by
  have hconnected := anchorReverseOccurrenceCrossDifference_le_connected
    hsmall hpolymer
  have htail := connectedReverseSourcePairSum_le_boundaryTail
    hsmall hstart hstartInner hbox
  have hbound := Q'.le_trans' _ _ _ hconnected htail
  have hreorder :
      ((anchorCanonicalPartition n * anchorCanonicalPartition small) *
          occurrenceBoundaryEpsilon distance).eqv
        (occurrenceBoundaryEpsilon distance *
          (anchorCanonicalPartition small * anchorCanonicalPartition n)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv
        (anchorCanonicalPartition n * anchorCanonicalPartition small)
        (occurrenceBoundaryEpsilon distance)) ?_
    exact Q'.mul_eqv_congr_left (occurrenceBoundaryEpsilon distance)
      (anchorCanonicalPartition n * anchorCanonicalPartition small)
      (anchorCanonicalPartition small * anchorCanonicalPartition n)
      (Q'.mul_comm_eqv _ _)
  exact Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hreorder)

theorem anchorOccurrenceProbability_reverse_sub_le_boundaryEpsilon
    {small n inner distance start : Nat} {polymer : List Nat}
    (hsmall : small ≤ n)
    (hpolymer : polymer ∈ canonicalSurfacePolymers small)
    (hstart : start ∈ transportPolymer small n polymer)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    anchorEventProbability small (sourceOccurrenceEvent polymer) -
        anchorEventProbability n (targetOccurrenceEvent small n polymer) ≤
      occurrenceBoundaryEpsilon distance := by
  let sourceNumerator := anchorEventNumerator small
    (sourceOccurrenceEvent polymer)
  let targetNumerator := anchorEventNumerator n
    (targetOccurrenceEvent small n polymer)
  let sourcePartition := anchorCanonicalPartition small
  let targetPartition := anchorCanonicalPartition n
  let epsilon := occurrenceBoundaryEpsilon distance
  have hcross :
      sourceNumerator * targetPartition -
          targetNumerator * sourcePartition ≤
        epsilon * (sourcePartition * targetPartition) := by
    exact anchorReverseOccurrenceCrossDifference_le_boundaryTail
      hsmall hpolymer hstart hstartInner hbox
  have hadd :
      sourceNumerator * targetPartition ≤
        targetNumerator * sourcePartition +
          epsilon * (sourcePartition * targetPartition) :=
    le_add_of_sub_le_local hcross
  have hreorder :
      (targetNumerator * sourcePartition +
          epsilon * (sourcePartition * targetPartition)).eqv
        ((targetNumerator + epsilon * targetPartition) *
          sourcePartition) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left
        (targetNumerator * sourcePartition)
        (epsilon * (sourcePartition * targetPartition))
        ((epsilon * targetPartition) * sourcePartition) ?_) ?_
    · refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left epsilon _ _
          (Q'.mul_comm_eqv sourcePartition targetPartition)) ?_
      exact Q'.eqv_symm
        (Q'.mul_assoc_eqv epsilon targetPartition sourcePartition)
    · exact Q'.eqv_symm
        (Q'.add_mul_eqv targetNumerator
          (epsilon * targetPartition) sourcePartition)
  have hratio := divPos_le_divPos_of_cross_local
    sourceNumerator sourcePartition
    (targetNumerator + epsilon * targetPartition) targetPartition
    (anchorCanonicalPartition_pos small)
    (anchorCanonicalPartition_pos n)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hreorder))
  have hcollapse := divPos_add_scaled_eqv
    targetNumerator epsilon targetPartition
    (anchorCanonicalPartition_pos n)
  have hprob :
      anchorEventProbability small (sourceOccurrenceEvent polymer) ≤
        anchorEventProbability n (targetOccurrenceEvent small n polymer) +
          occurrenceBoundaryEpsilon distance := by
    unfold anchorEventProbability
    exact Q'.le_trans' _ _ _ hratio (Q'.le_of_eqv hcollapse)
  exact Q'.sub_le_of_le_add hprob

theorem anchorPolymerOccurrenceProbability_reverse_sub_le_boundaryEpsilon
    {small n inner distance start : Nat} {polymer : List Nat}
    (hsmall : small ≤ n)
    (hpolymer : polymer ∈ canonicalSurfacePolymers small)
    (hstart : start ∈ transportPolymer small n polymer)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    anchorPolymerOccurrenceProbability small polymer -
        anchorPolymerOccurrenceProbability n
          (transportPolymer small n polymer) ≤
      occurrenceBoundaryEpsilon distance := by
  simpa [anchorPolymerOccurrenceProbability, targetOccurrenceEvent,
    sourceOccurrenceEvent] using
    anchorOccurrenceProbability_reverse_sub_le_boundaryEpsilon
      hsmall hpolymer hstart hstartInner hbox

/-- Full finite-volume modulus for one transported canonical polymer. -/
theorem anchorPolymerOccurrenceProbability_abs_sub_le_boundaryEpsilon
    {small n inner distance start : Nat} {polymer : List Nat}
    (hsmall : small ≤ n)
    (hpolymer : polymer ∈ canonicalSurfacePolymers small)
    (hstart : start ∈ transportPolymer small n polymer)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    Q'.abs
        (anchorPolymerOccurrenceProbability n
            (transportPolymer small n polymer) -
          anchorPolymerOccurrenceProbability small polymer) ≤
      occurrenceBoundaryEpsilon distance := by
  apply Q'.abs_le
  · have hreverse :=
      anchorPolymerOccurrenceProbability_reverse_sub_le_boundaryEpsilon
        hsmall hpolymer hstart hstartInner hbox
    have hneg := Q'.neg_le_neg hreverse
    exact Q'.le_trans' _ _ _ hneg
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (sub_swap_eqv_neg_local
            (anchorPolymerOccurrenceProbability small polymer)
            (anchorPolymerOccurrenceProbability n
              (transportPolymer small n polymer)))))
  · exact anchorPolymerOccurrenceProbability_sub_le_boundaryEpsilon
      hsmall hpolymer hstart hstartInner hbox

theorem anchorPolymerOccurrenceProbability_abs_sub_le_boundaryEpsilon_of_sourceFace
    {small n inner distance sourceFace : Nat} {polymer : List Nat}
    (hsmall : small ≤ n)
    (hpolymer : polymer ∈ canonicalSurfacePolymers small)
    (hsource : sourceFace ∈ polymer)
    (hsourceInner : boxPlaquetteAt small sourceFace ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    Q'.abs
        (anchorPolymerOccurrenceProbability n
            (transportPolymer small n polymer) -
          anchorPolymerOccurrenceProbability small polymer) ≤
      occurrenceBoundaryEpsilon distance := by
  obtain ⟨targetFace, htargetFace, hfaceEq⟩ :=
    transportPolymerMemberTarget hsmall
      (canonicalSurfacePolymer_mem_faceSupports hpolymer) hsource
  apply anchorPolymerOccurrenceProbability_abs_sub_le_boundaryEpsilon
    hsmall hpolymer htargetFace
  · rw [← hfaceEq]
    exact hsourceInner
  · exact hbox

theorem anchorPolymerOccurrenceProbability_abs_sub_le_boundaryEpsilon_of_inside
    {small n inner distance : Nat} {polymer : List Nat}
    (hsmall : small ≤ n)
    (hpolymer : polymer ∈ canonicalSurfacePolymers small)
    (hinside : PolymerInsideBox inner small polymer)
    (hbox : inner + distance = small) :
    Q'.abs
        (anchorPolymerOccurrenceProbability n
            (transportPolymer small n polymer) -
          anchorPolymerOccurrenceProbability small polymer) ≤
      occurrenceBoundaryEpsilon distance := by
  obtain ⟨sourceFace, hsourceFace⟩ :=
    canonicalSurfacePolymers_allNonempty small polymer hpolymer
  apply
    anchorPolymerOccurrenceProbability_abs_sub_le_boundaryEpsilon_of_sourceFace
      hsmall hpolymer hsourceFace
  · apply hinside (boxPlaquetteAt small sourceFace)
    exact List.mem_map.mpr ⟨sourceFace, hsourceFace, rfl⟩
  · exact hbox

end YMGap.Continuum.Z4CanonicalOccurrenceStability

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalOccurrenceStability.divPos_le_divPos_of_cross_local
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceStability.anchorOccurrenceCrossDifference_le_boundaryTail
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceStability.anchorOccurrenceProbability_sub_le_boundaryEpsilon
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceStability.anchorPolymerOccurrenceProbability_sub_le_boundaryEpsilon
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceStability.anchorPolymerOccurrenceProbability_sub_le_boundaryEpsilon_of_sourceFace
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceStability.anchorPolymerOccurrenceProbability_sub_le_boundaryEpsilon_of_inside
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceStability.anchorReverseOccurrenceCrossDifference_le_boundaryTail
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceStability.anchorOccurrenceProbability_reverse_sub_le_boundaryEpsilon
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceStability.anchorPolymerOccurrenceProbability_abs_sub_le_boundaryEpsilon
#print axioms YMGap.Continuum.Z4CanonicalOccurrenceStability.anchorPolymerOccurrenceProbability_abs_sub_le_boundaryEpsilon_of_inside
