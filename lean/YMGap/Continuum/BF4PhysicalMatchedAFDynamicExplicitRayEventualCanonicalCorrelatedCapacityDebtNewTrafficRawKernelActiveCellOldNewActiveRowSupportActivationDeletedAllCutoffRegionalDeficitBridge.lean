/-
# Rejoin the all-cutoff adaptive observable to the canonical total deficit

The all-cutoff adaptive routing at transition `k` lives on cutoff `k+1`.
Consequently the observable-connected comparison of two consecutive adaptive
debts is naturally shifted by one cutoff.  This module inserts that coherent
adaptive stream between two consecutive canonical debts:

  canonical(k+1) -> adaptive(k+1) -> adaptive(k+2) -> canonical(k+2).

The two outer terms are exact route-mismatch deficits.  The middle term is the
exact adaptive data deficit on the projectively coherent route family stored
by the all-cutoff observable certificate.  A three-segment two-sided triangle
inequality bounds the existing canonical transported deficit at `k+1` by
those three terms.

Two antitone tail controls--one for route mismatch and one for adaptive data
drift--therefore construct the existing canonical transported tail, including
the single omitted cutoff through an explicit successor-tail reindexing.
Together with the unchanged three shell-face tails, this feeds the existing
one total-deficit compiler.  No parallel observable or replacement total tail
is introduced.

No adaptive route/data tail is inhabited here.  No completed gap, continuum
limit, or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler
import YMGap.Continuum.SummableRationalStepVariationAlgebra

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffRegionalDeficitBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra

local infix:50 " ≈ " => Q'.eqv

private theorem add_le_add_local
    {a b c d : Q'} (hab : a <= b) (hcd : c <= d) :
    a + c <= b + d :=
  Q'.le_trans' _ _ _
    (Q'.add_le_add_right a b c hab)
    (Q'.add_le_add_left b c d hcd)

private theorem reassoc_cancel_local (u middle residual : Q') :
    ((u + (-middle)) + (middle + residual)) ≈ u + residual := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv u (-middle) (middle + residual)) ?_
  refine Q'.add_eqv_congr_left u
    ((-middle) + (middle + residual)) residual ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-middle) middle residual)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((-middle) + middle) 0 residual
      (Q'.neg_add_self_eqv middle)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' residual)

private theorem abs_sub_triangle_local (a b c : Q') :
    Q'.abs (a + -b) <=
      Q'.abs (a + -c) + Q'.abs (c + -b) := by
  have hdecompose : a + -b ≈ (a + -c) + (c + -b) :=
    Q'.eqv_symm (reassoc_cancel_local a c (-b))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (Q'.abs_add_le' (a + -c) (c + -b))

private theorem reverse_three_sum_eqv (first middle last : Q') :
    last + (middle + first) ≈ first + (middle + last) := by
  refine Q'.eqv_trans _ ((last + middle) + first) _
    (Q'.eqv_symm (Q'.add_assoc_eqv last middle first)) ?_
  refine Q'.eqv_trans _ (first + (last + middle)) _
    (Q'.add_comm_eqv (last + middle) first) ?_
  exact Q'.add_eqv_congr_left first (last + middle) (middle + last)
    (Q'.add_comm_eqv last middle)

private theorem four_point_two_sided_triangle
    (canonicalCurrent adaptiveCurrent adaptiveNext canonicalNext : Q') :
    Q'.max'
        (Q'.abs (canonicalCurrent + -canonicalNext))
        (Q'.abs (canonicalNext + -canonicalCurrent)) <=
      Q'.max'
          (Q'.abs (adaptiveCurrent + -canonicalCurrent))
          (Q'.abs (canonicalCurrent + -adaptiveCurrent)) +
        (Q'.max'
            (Q'.abs (adaptiveCurrent + -adaptiveNext))
            (Q'.abs (adaptiveNext + -adaptiveCurrent)) +
          Q'.max'
            (Q'.abs (adaptiveNext + -canonicalNext))
            (Q'.abs (canonicalNext + -adaptiveNext))) := by
  apply (Q'.max'_le_iff' _ _ _).mpr
  constructor
  · have hfirst :=
      abs_sub_triangle_local canonicalCurrent canonicalNext adaptiveCurrent
    have hsecond :=
      abs_sub_triangle_local adaptiveCurrent canonicalNext adaptiveNext
    have htail :
        Q'.abs (adaptiveCurrent + -canonicalNext) <=
          Q'.max'
              (Q'.abs (adaptiveCurrent + -adaptiveNext))
              (Q'.abs (adaptiveNext + -adaptiveCurrent)) +
            Q'.max'
              (Q'.abs (adaptiveNext + -canonicalNext))
              (Q'.abs (canonicalNext + -adaptiveNext)) :=
      Q'.le_trans' _ _ _ hsecond
        (add_le_add_local
          (Q'.le_max'_left _ _) (Q'.le_max'_left _ _))
    exact Q'.le_trans' _ _ _ hfirst
      (add_le_add_local (Q'.le_max'_right _ _) htail)
  · have hfirst :=
      abs_sub_triangle_local canonicalNext canonicalCurrent adaptiveNext
    have hsecond :=
      abs_sub_triangle_local adaptiveNext canonicalCurrent adaptiveCurrent
    have htail :
        Q'.abs (adaptiveNext + -canonicalCurrent) <=
          Q'.max'
              (Q'.abs (adaptiveCurrent + -adaptiveNext))
              (Q'.abs (adaptiveNext + -adaptiveCurrent)) +
            Q'.max'
              (Q'.abs (adaptiveCurrent + -canonicalCurrent))
              (Q'.abs (canonicalCurrent + -adaptiveCurrent)) :=
      Q'.le_trans' _ _ _ hsecond
        (add_le_add_local
          (Q'.le_max'_right _ _) (Q'.le_max'_left _ _))
    have hreverse :
        Q'.abs (canonicalNext + -canonicalCurrent) <=
          Q'.max'
              (Q'.abs (adaptiveNext + -canonicalNext))
              (Q'.abs (canonicalNext + -adaptiveNext)) +
            (Q'.max'
                (Q'.abs (adaptiveCurrent + -adaptiveNext))
                (Q'.abs (adaptiveNext + -adaptiveCurrent)) +
              Q'.max'
                (Q'.abs (adaptiveCurrent + -canonicalCurrent))
                (Q'.abs (canonicalCurrent + -adaptiveCurrent))) :=
      Q'.le_trans' _ _ _ hfirst
        (add_le_add_local (Q'.le_max'_right _ _) htail)
    exact Q'.le_trans' _ _ _ hreverse
      (Q'.le_of_eqv
        (reverse_three_sum_eqv
          (Q'.max'
            (Q'.abs (adaptiveCurrent + -canonicalCurrent))
            (Q'.abs (canonicalCurrent + -adaptiveCurrent)))
          (Q'.max'
            (Q'.abs (adaptiveCurrent + -adaptiveNext))
            (Q'.abs (adaptiveNext + -adaptiveCurrent)))
          (Q'.max'
            (Q'.abs (adaptiveNext + -canonicalNext))
            (Q'.abs (canonicalNext + -adaptiveNext)))))

private theorem listQMaxZero_le_of_member_bound_local
    {State : Type} (value : State -> Q') (bound : Q') :
    forall states : List State,
      (0 : Q') <= bound ->
      (forall state, state ∈ states -> value state <= bound) ->
      listQMaxZero value states <= bound
  | [], hbound, _ => hbound
  | head :: tail, hbound, hall => by
      unfold listQMaxZero
      exact (Q'.max'_le_iff' _ _ _).mpr
        ⟨hall head List.mem_cons_self,
          listQMaxZero_le_of_member_bound_local value bound tail hbound
            (fun state hstate =>
              hall state (List.mem_cons_of_mem head hstate))⟩

/-! ## 1. The shifted adaptive debt stream -/

def matchedEventualAdaptiveDebtAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) (pair : Nat × Nat) : Q' :=
  matchedEventualRoutedCapacityDebtOnPairForRouting
    trajectory transitionStart physicalScale (cutoffOffset + 1)
    (certificate.fullRoutingAt cutoffOffset) pair

def matchedEventualAdaptiveCanonicalRouteMismatchDeficitOnPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) (pair : Nat × Nat) : Q' :=
  let adaptive := matchedEventualAdaptiveDebtAt certificate cutoffOffset pair
  let canonical := matchedEventualCanonicalRoutedCapacityDebtOnPair
    trajectory transitionStart physicalScale (cutoffOffset + 1) pair
  Q'.max' (Q'.abs (adaptive + -canonical))
    (Q'.abs (canonical + -adaptive))

def matchedEventualAdaptiveCoherentDataDeficitOnPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) (pair : Nat × Nat) : Q' :=
  let current := matchedEventualAdaptiveDebtAt certificate cutoffOffset pair
  let mappedPair := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale (cutoffOffset + 1) pair
  let following := matchedEventualAdaptiveDebtAt certificate (cutoffOffset + 1) mappedPair
  Q'.max' (Q'.abs (current + -following))
    (Q'.abs (following + -current))

def matchedEventualAdaptiveCanonicalRouteMismatchDeficitMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) : Q' :=
  listQMaxZero
    (matchedEventualAdaptiveCanonicalRouteMismatchDeficitOnPair certificate cutoffOffset)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1))

def matchedEventualAdaptiveCoherentDataDeficitMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) : Q' :=
  listQMaxZero
    (matchedEventualAdaptiveCoherentDataDeficitOnPair certificate cutoffOffset)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1))

theorem matchedEventualAdaptiveCanonicalRouteMismatchDeficitMaximum_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualAdaptiveCanonicalRouteMismatchDeficitMaximum
        certificate cutoffOffset := by
  unfold matchedEventualAdaptiveCanonicalRouteMismatchDeficitMaximum
  apply listQMaxZero_nonnegative
  intro pair
  unfold matchedEventualAdaptiveCanonicalRouteMismatchDeficitOnPair
  dsimp only
  exact Q'.le_trans' _ _ _ (Q'.abs_nonneg _) (Q'.le_max'_left _ _)

theorem matchedEventualAdaptiveCoherentDataDeficitMaximum_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    (0 : Q') <= matchedEventualAdaptiveCoherentDataDeficitMaximum
      certificate cutoffOffset := by
  unfold matchedEventualAdaptiveCoherentDataDeficitMaximum
  apply listQMaxZero_nonnegative
  intro pair
  unfold matchedEventualAdaptiveCoherentDataDeficitOnPair
  dsimp only
  exact Q'.le_trans' _ _ _ (Q'.abs_nonneg _) (Q'.le_max'_left _ _)

/-! ## 2. Three exact terms dominate the existing transported deficit -/

theorem matchedEventualCanonicalTransportedCapacityDebtDeficitOnPair_succ_le_adaptive_split
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) (pair : Nat × Nat) :
    matchedEventualCanonicalTransportedCapacityDebtDeficitOnPair
        trajectory transitionStart physicalScale (cutoffOffset + 1) pair <=
      matchedEventualAdaptiveCanonicalRouteMismatchDeficitOnPair
          certificate cutoffOffset pair +
        (matchedEventualAdaptiveCoherentDataDeficitOnPair
            certificate cutoffOffset pair +
          matchedEventualAdaptiveCanonicalRouteMismatchDeficitOnPair
            certificate (cutoffOffset + 1)
            (matchedEventualCanonicalCurrentPairToNext
              trajectory transitionStart physicalScale (cutoffOffset + 1) pair)) := by
  let canonicalCurrent := matchedEventualCanonicalRoutedCapacityDebtOnPair
    trajectory transitionStart physicalScale (cutoffOffset + 1) pair
  let adaptiveCurrent := matchedEventualAdaptiveDebtAt certificate cutoffOffset pair
  let mappedPair := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale (cutoffOffset + 1) pair
  let adaptiveNext := matchedEventualAdaptiveDebtAt certificate (cutoffOffset + 1) mappedPair
  let canonicalNext := matchedEventualCanonicalRoutedCapacityDebtOnPair
    trajectory transitionStart physicalScale ((cutoffOffset + 1) + 1) mappedPair
  unfold matchedEventualCanonicalTransportedCapacityDebtDeficitOnPair
    matchedEventualAdaptiveCanonicalRouteMismatchDeficitOnPair
    matchedEventualAdaptiveCoherentDataDeficitOnPair
  dsimp only
  exact four_point_two_sided_triangle
    canonicalCurrent adaptiveCurrent adaptiveNext canonicalNext

theorem matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_succ_le_adaptive_split
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale (cutoffOffset + 1) <=
      matchedEventualAdaptiveCanonicalRouteMismatchDeficitMaximum
          certificate cutoffOffset +
        (matchedEventualAdaptiveCoherentDataDeficitMaximum
            certificate cutoffOffset +
          matchedEventualAdaptiveCanonicalRouteMismatchDeficitMaximum
            certificate (cutoffOffset + 1)) := by
  have hexact :
      matchedEventualCanonicalTransportedCapacityDebtDeficitExactMaximum
          trajectory transitionStart physicalScale (cutoffOffset + 1) <=
        matchedEventualAdaptiveCanonicalRouteMismatchDeficitMaximum
            certificate cutoffOffset +
          (matchedEventualAdaptiveCoherentDataDeficitMaximum
              certificate cutoffOffset +
            matchedEventualAdaptiveCanonicalRouteMismatchDeficitMaximum
              certificate (cutoffOffset + 1)) := by
    unfold matchedEventualCanonicalTransportedCapacityDebtDeficitExactMaximum
    apply listQMaxZero_le_of_member_bound_local
    · exact Q'.zero_le_add _ _
        (matchedEventualAdaptiveCanonicalRouteMismatchDeficitMaximum_nonnegative
          certificate cutoffOffset)
        (Q'.zero_le_add _ _
          (matchedEventualAdaptiveCoherentDataDeficitMaximum_nonnegative
            certificate cutoffOffset)
          (matchedEventualAdaptiveCanonicalRouteMismatchDeficitMaximum_nonnegative
            certificate (cutoffOffset + 1)))
    · intro pair hpair
      have hmapped := matchedEventualCanonicalCurrentPairToNext_mem
        trajectory transitionStart physicalScale (cutoffOffset + 1) pair hpair
      exact Q'.le_trans' _ _ _
        (matchedEventualCanonicalTransportedCapacityDebtDeficitOnPair_succ_le_adaptive_split
          certificate cutoffOffset pair)
        (add_le_add_local
          (le_listQMaxZero_of_mem
            (matchedEventualAdaptiveCanonicalRouteMismatchDeficitOnPair
              certificate cutoffOffset)
            (matchedEventualCanonicalVacuumSectorPairs
              trajectory transitionStart physicalScale (cutoffOffset + 1)) hpair)
          (add_le_add_local
            (le_listQMaxZero_of_mem
              (matchedEventualAdaptiveCoherentDataDeficitOnPair
                certificate cutoffOffset)
              (matchedEventualCanonicalVacuumSectorPairs
                trajectory transitionStart physicalScale (cutoffOffset + 1)) hpair)
            (le_listQMaxZero_of_mem
              (matchedEventualAdaptiveCanonicalRouteMismatchDeficitOnPair
                certificate (cutoffOffset + 1))
              (matchedEventualCanonicalVacuumSectorPairs
                trajectory transitionStart physicalScale ((cutoffOffset + 1) + 1))
              hmapped)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_eqv_exact
        trajectory transitionStart physicalScale (cutoffOffset + 1)))
    hexact

/-! ## Axiom audit -/

#print axioms
  matchedEventualAdaptiveDebtAt
#print axioms matchedEventualAdaptiveCanonicalRouteMismatchDeficitMaximum
#print axioms matchedEventualAdaptiveCoherentDataDeficitMaximum
#print axioms
  matchedEventualCanonicalTransportedCapacityDebtDeficitOnPair_succ_le_adaptive_split
#print axioms
  matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_succ_le_adaptive_split

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffRegionalDeficitBridge
