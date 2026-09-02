/-
# The physical pushforward L1 remainder as an exact dual observable defect

For a finite physical kernel, assign each coarse target the rational sign of
its retained remainder.  Multiplying the remainder by this explicit sign is
exactly its absolute value.  Summing and using the pushforward decomposition
therefore proves

  remainderL1
    = blockedExpectation(sign remainder)
        - coarseExpectation(sign remainder).

The right-hand side is nonnegative, so the corresponding absolute observable
matching defect is also exactly `remainderL1`.  The final theorem specializes
this dual observable to the actual globally link-glued cutoff-one physical
kernel used by `observableMatchDefect`.

The sign observable depends on the candidate kernel.  Consequently this file
does not turn the existing fixed-observable finite argmin into a total-
variation argmin, and it proves no refining-scale smallness estimate.

Constructive contract: decidable rational order, finite sums, and exact
pushforward algebra only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.BF4ObservableMatchedOneStep

namespace YMGap.Continuum.CompactDualPhysicalRemainderL1DualObservable

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

private theorem add_then_sub_left_local (left residual : Q') :
    (left + residual) + (-left) ≈ residual := by
  refine Q'.eqv_trans _
    (left + (residual + (-left))) _
    (Q'.add_assoc_eqv left residual (-left)) ?_
  refine Q'.eqv_trans _
    (left + ((-left) + residual)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left left _ _
      (Q'.add_comm_eqv residual (-left))
  refine Q'.eqv_trans _
    ((left + (-left)) + residual) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.add_assoc_eqv left (-left) residual)
  refine Q'.eqv_trans _ (0 + residual) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ residual
      (Q'.add_neg_self_eqv left)
  exact Q'.eqv_of_eq (Q'.zero_add' residual)

/-! ## 1. Generic finite-kernel total-variation duality -/

/-- Explicit rational sign of one retained coarse-target remainder. -/
def remainderSign
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (target : EdgeLabelling) : Q' :=
  if (0 : Q') ≤ K.remainder target then 1 else -1

/-- Multiplication by the explicit sign produces the rational absolute value. -/
theorem remainder_mul_sign_eqv_abs
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (target : EdgeLabelling) :
    K.remainder target * remainderSign K target ≈
      Q'.abs (K.remainder target) := by
  unfold remainderSign Q'.abs
  by_cases hnonnegative : (0 : Q') ≤ K.remainder target
  · simp only [if_pos hnonnegative]
    exact Q'.mul_one_eqv (K.remainder target)
  · simp only [if_neg hnonnegative]
    refine Q'.eqv_trans _
      (-(K.remainder target * 1)) _ ?_ ?_
    · exact Q'.mul_neg_eqv (K.remainder target) 1
    · exact Q'.neg_eqv_congr _ _
        (Q'.mul_one_eqv (K.remainder target))

/-- Expectation of the candidate-dependent sign observable under the signed
remainder measure. -/
def signedRemainderExpectation
    {S : SlabScalePair} (K : S.FiniteSlabKernel) : Q' :=
  observableExpectation K.remainder S.coarse.physicalLabellings
    (remainderSign K)

/-- The signed-remainder expectation is exactly its finite `L1` norm. -/
theorem signedRemainderExpectation_eqv_remainderL1
    {S : SlabScalePair} (K : S.FiniteSlabKernel) :
    signedRemainderExpectation K ≈ K.remainderL1 := by
  unfold signedRemainderExpectation observableExpectation
    SlabScalePair.FiniteSlabKernel.remainderL1
  exact listQSum_congr_on _ _ S.coarse.physicalLabellings
    (fun target _ => remainder_mul_sign_eqv_abs K target)

theorem remainderL1_nonnegative
    {S : SlabScalePair} (K : S.FiniteSlabKernel) :
    (0 : Q') ≤ K.remainderL1 := by
  unfold SlabScalePair.FiniteSlabKernel.remainderL1
  apply listQSum_nonnegative_on
  intro target _
  exact Q'.abs_nonneg (K.remainder target)

/-- The blocked expectation of the sign observable decomposes into its coarse
expectation plus the signed-remainder expectation. -/
theorem blockedSignExpectation_eqv_coarse_add_signedRemainderExpectation
    {S : SlabScalePair} (K : S.FiniteSlabKernel) :
    observableExpectation K.blockedMass S.coarse.physicalLabellings
        (remainderSign K) ≈
      observableExpectation S.coarse.normalizedMass
          S.coarse.physicalLabellings (remainderSign K) +
        signedRemainderExpectation K := by
  unfold observableExpectation signedRemainderExpectation
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        (S.coarse.normalizedMass target + K.remainder target) *
          remainderSign K target)
      S.coarse.physicalLabellings) _ ?_ ?_
  · exact listQSum_congr_on _ _ S.coarse.physicalLabellings
      (fun target _ =>
        Q'.mul_eqv_congr_right _ _ (remainderSign K target)
          (K.pushforward_decomposition target))
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        S.coarse.normalizedMass target * remainderSign K target +
          K.remainder target * remainderSign K target)
      S.coarse.physicalLabellings) _ ?_ ?_
  · exact listQSum_congr_on _ _ S.coarse.physicalLabellings
      (fun target _ =>
        Q'.add_mul_eqv
          (S.coarse.normalizedMass target)
          (K.remainder target) (remainderSign K target))
  exact listQSum_add
    (fun target =>
      S.coarse.normalizedMass target * remainderSign K target)
    (fun target => K.remainder target * remainderSign K target)
    S.coarse.physicalLabellings

/-- The blocked-minus-coarse expectation of the sign observable is exactly
the signed-remainder expectation. -/
theorem blocked_sub_coarseSignExpectation_eqv_signedRemainderExpectation
    {S : SlabScalePair} (K : S.FiniteSlabKernel) :
    observableExpectation K.blockedMass S.coarse.physicalLabellings
          (remainderSign K) +
        -(observableExpectation S.coarse.normalizedMass
          S.coarse.physicalLabellings (remainderSign K)) ≈
      signedRemainderExpectation K := by
  let blocked := observableExpectation K.blockedMass
    S.coarse.physicalLabellings (remainderSign K)
  let coarse := observableExpectation S.coarse.normalizedMass
    S.coarse.physicalLabellings (remainderSign K)
  let residual := signedRemainderExpectation K
  refine Q'.eqv_trans _ ((coarse + residual) + (-coarse)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ (-coarse)
      (blockedSignExpectation_eqv_coarse_add_signedRemainderExpectation K)
  exact add_then_sub_left_local coarse residual

/-- Exact finite total-variation duality: the absolute observable defect of
the candidate-dependent sign is the full retained `L1` remainder. -/
theorem remainderSignObservableDefect_eqv_remainderL1
    {S : SlabScalePair} (K : S.FiniteSlabKernel) :
    Q'.abs
        (observableExpectation K.blockedMass S.coarse.physicalLabellings
            (remainderSign K) +
          -(observableExpectation S.coarse.normalizedMass
            S.coarse.physicalLabellings (remainderSign K))) ≈
      K.remainderL1 := by
  have hdifference :=
    blocked_sub_coarseSignExpectation_eqv_signedRemainderExpectation K
  have hL1 := signedRemainderExpectation_eqv_remainderL1 K
  refine Q'.eqv_trans _ (Q'.abs K.remainderL1) _ ?_ ?_
  · exact Q'.abs_eqv_congr (Q'.eqv_trans _ _ _ hdifference hL1)
  exact Q'.eqv_of_eq
    (ExpNeg.abs_of_nonneg (remainderL1_nonnegative K))

/-! ## 2. The actual cutoff-one observable-matching specialization -/

/-- Candidate-dependent sign observable for the actual globally link-glued
cutoff-one physical kernel. -/
def physicalRemainderSignObservable
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) :
    SlabLabelling → Q' :=
  let S := G.candidateScalePair g hg candidate hcandidate
  remainderSign (physicalKernel S rfl hcandidate)

/-- The existing physical observable-matching defect, evaluated at the
candidate's own sign observable, is exactly the actual pushforward `L1`
remainder at that candidate. -/
theorem physicalObservableMatchDefect_sign_eqv_remainderL1
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) :
    observableMatchDefect G g hg candidate hcandidate
        (physicalRemainderSignObservable
          G g hg candidate hcandidate) ≈
      (physicalKernel
        (G.candidateScalePair g hg candidate hcandidate)
        rfl hcandidate).remainderL1 := by
  simpa only [observableMatchDefect, blockedObservableExpectation,
      coarseObservableExpectation, physicalRemainderSignObservable] using
    (remainderSignObservableDefect_eqv_remainderL1
      (physicalKernel
        (G.candidateScalePair g hg candidate hcandidate)
        rfl hcandidate))

#print axioms remainderSign
#print axioms remainder_mul_sign_eqv_abs
#print axioms signedRemainderExpectation_eqv_remainderL1
#print axioms remainderL1_nonnegative
#print axioms blockedSignExpectation_eqv_coarse_add_signedRemainderExpectation
#print axioms blocked_sub_coarseSignExpectation_eqv_signedRemainderExpectation
#print axioms remainderSignObservableDefect_eqv_remainderL1
#print axioms physicalRemainderSignObservable
#print axioms physicalObservableMatchDefect_sign_eqv_remainderL1

end YMGap.Continuum.CompactDualPhysicalRemainderL1DualObservable
