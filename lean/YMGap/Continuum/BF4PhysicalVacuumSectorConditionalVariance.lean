/-
# Conditional variance behind the BF4 boundary transform

For a weighted Gram kernel

    K(x,y) = sum_b W(b) A(x,b) A(y,b),

its state-space Dirichlet energy is exactly the boundary average of the
pairwise variance carried by the channel weights `A(-,b)`.  In the physical
BF4 vacuum sector this gives the finite law of total variance

    D(f) - <f,Tf>
      = (1/2) sum_b W(b)
          sum_{x,y} A(x,b) A(y,b) (f(x)-f(y))^2.

When the channel total is positive, the inner expression divided by twice
the square of that total is the variance of `f` under the actual posterior
state law conditioned on the fixed-time boundary.  Zero-total channels need
no division and contribute exactly zero to the displayed formula.

Thus a strict transfer bound asks for a uniform fraction of stationary
variance to remain after revealing the time boundary.  This is a local
block-influence/conditional-variance problem; no canonical path is selected.

No uniform variance fraction is asserted here.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorBoundaryTransform

namespace YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVariance

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

/-- Cancellation-free rational-semantic polynomial normalization. -/
local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Generic weighted-Gram law of total variance -/

/-- Boundary average of the unnormalized posterior pairwise variances. -/
def weightedGramConditionalPairwiseVariance
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (channelWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (coefficient : State → Q') : Q' :=
  listQSum
    (fun channel =>
      channelWeight channel *
        finiteWeightedPairwiseVariance states
          (fun state => amplitude state channel)
          coefficient)
    channels

private def weightedGramConditionalPairTerm
    {State Channel : Type}
    (channelWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (coefficient : State → Q')
    (left right : State) (channel : Channel) : Q' :=
  channelWeight channel *
    ((amplitude left channel * amplitude right channel) *
      ((coefficient left + -coefficient right) *
        (coefficient left + -coefficient right)))

/-- **Finite law of total variance for a weighted Gram.**  The Dirichlet
energy of the Gram kernel is exactly the boundary average of within-channel
pairwise variance. -/
theorem finiteJointDirichletEnergy_weightedGram_eqv_conditionalPairwiseVariance
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (channelWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (coefficient : State → Q') :
    finiteJointDirichletEnergy states coefficient
        (weightedGram channels channelWeight amplitude) ≈
      weightedGramConditionalPairwiseVariance
        states channels channelWeight amplitude coefficient := by
  let term := weightedGramConditionalPairTerm
    channelWeight amplitude coefficient
  have hexpand :
      finiteJointDirichletEnergy states coefficient
          (weightedGram channels channelWeight amplitude) ≈
        listQSum
          (fun left =>
            listQSum
              (fun right => listQSum (term left right) channels)
              states)
          states := by
    unfold finiteJointDirichletEnergy
    apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    let differenceSquare :=
      (coefficient left + -coefficient right) *
        (coefficient left + -coefficient right)
    refine Q'.eqv_trans _
      (listQSum
        (fun channel =>
          (channelWeight channel *
            (amplitude left channel * amplitude right channel)) *
              differenceSquare)
        channels) _ ?_ ?_
    · unfold weightedGram
      exact Q'.eqv_symm
        (listQSum_mul_right
          (fun channel =>
            channelWeight channel *
              (amplitude left channel * amplitude right channel))
          differenceSquare channels)
    apply listQSum_congr
    intro channel
    unfold term weightedGramConditionalPairTerm differenceSquare
    q_ring
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun right => listQSum (term left right) channels)
          states)
      states) _ hexpand ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun channel => listQSum (fun right => term left right channel) states)
          channels)
      states) _ ?_ ?_
  · apply listQSum_congr
    intro left
    exact Q'.eqv_symm
      (listQSum_swap
        (fun right channel => term left right channel)
        states channels)
  refine Q'.eqv_trans _
    (listQSum
      (fun channel =>
        listQSum
          (fun left => listQSum (fun right => term left right channel) states)
          states)
      channels) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_swap
        (fun left channel =>
          listQSum (fun right => term left right channel) states)
        states channels)
  unfold weightedGramConditionalPairwiseVariance
  apply listQSum_congr
  intro channel
  let base := fun left right =>
    (amplitude left channel * amplitude right channel) *
      ((coefficient left + -coefficient right) *
        (coefficient left + -coefficient right))
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        channelWeight channel * listQSum (base left) states)
      states) _ ?_ ?_
  · apply listQSum_congr
    intro left
    unfold term weightedGramConditionalPairTerm base
    exact listQSum_mul_left
      (channelWeight channel)
      (fun right =>
        (amplitude left channel * amplitude right channel) *
          ((coefficient left + -coefficient right) *
            (coefficient left + -coefficient right)))
      states
  refine Q'.eqv_trans _
    (channelWeight channel *
      listQSum (fun left => listQSum (base left) states) states) _
    (listQSum_mul_left
      (channelWeight channel)
      (fun left => listQSum (base left) states)
      states) ?_
  unfold finiteWeightedPairwiseVariance finiteJointDirichletEnergy
    finiteStationaryProductJoint base
  exact Q'.eqv_refl _

/-! ## 2. The actual physical BF4 conditional variance -/

/-- Boundary average of within-posterior pairwise variance for the literal
physical BF4 vacuum-sector half-amplitudes. -/
def centralPhysicalFiniteVacuumSectorConditionalPairwiseVariance
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') : Q' :=
  weightedGramConditionalPairwiseVariance
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralBoundaryChannels cutoff half)
    (centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)
    coefficient

/-- The physical state-space edge energy is exactly the boundary-side
conditional pairwise variance. -/
theorem centralPhysicalFiniteVacuumSectorDirichlet_eqv_conditionalPairwiseVariance
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        coefficient
        (centralPhysicalFiniteKernel w hw cutoff half) ≈
      centralPhysicalFiniteVacuumSectorConditionalPairwiseVariance
        w hw cutoff half coefficient := by
  let states :=
    centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  let channels := centralBoundaryChannels cutoff half
  let gramWeight :=
    centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half
  let amplitude :=
    centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half
  refine Q'.eqv_trans _
    (finiteJointDirichletEnergy states coefficient
      (weightedGram channels gramWeight amplitude)) _ ?_ ?_
  · unfold finiteJointDirichletEnergy
    apply listQSum_congr_on
    intro left hleft
    apply listQSum_congr_on
    intro right hright
    exact Q'.mul_eqv_congr_right _ _ _
      (centralPhysicalFiniteKernel_eqv_vacuumSectorWeightedGram
        hleft hright)
  unfold centralPhysicalFiniteVacuumSectorConditionalPairwiseVariance
    states channels gramWeight amplitude
  exact
    finiteJointDirichletEnergy_weightedGram_eqv_conditionalPairwiseVariance
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      (centralBoundaryChannels cutoff half)
      (centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)
      coefficient

/-- **Physical law of total variance.**  The same-object transfer deficit is
exactly one half of the boundary average of posterior pairwise variance. -/
theorem centralPhysicalFiniteVacuumSector_deficit_eqv_half_conditionalPairwiseVariance
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw cutoff half coefficient +
        (-centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w hw cutoff half coefficient) ≈
      Q'.mkPos 1 2 (by decide) *
        centralPhysicalFiniteVacuumSectorConditionalPairwiseVariance
          w hw cutoff half coefficient := by
  refine Q'.eqv_trans _
    (Q'.mkPos 1 2 (by decide) *
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        coefficient
        (centralPhysicalFiniteKernel w hw cutoff half)) _ ?_ ?_
  · exact Q'.eqv_symm
      (half_mul_centralPhysicalFiniteVacuumSectorDirichlet_eqv_deficit
        w hw cutoff half coefficient)
  exact Q'.mul_eqv_congr_left _ _ _
    (centralPhysicalFiniteVacuumSectorDirichlet_eqv_conditionalPairwiseVariance
      w hw cutoff half coefficient)

end YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVariance

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVariance.finiteJointDirichletEnergy_weightedGram_eqv_conditionalPairwiseVariance
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVariance.centralPhysicalFiniteVacuumSectorDirichlet_eqv_conditionalPairwiseVariance
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVariance.centralPhysicalFiniteVacuumSector_deficit_eqv_half_conditionalPairwiseVariance
