/-
# Conditional stationary-product minorization gives the BF4 variance gap

For one positive-mass stationary component, the independent equilibrium joint
is the mass-normalized product

    pi(x) * pi(y) / mass(component).

This module proves the exact finite implication needed by the physical BF4
route.  If the genuine reflection-transfer joint pointwise dominates an
`epsilon` fraction of that component-conditioned product, then its Dirichlet
energy dominates `epsilon` times the centered stationary variance.  Equivalently,
the posterior conditional-variance fraction is at least `epsilon`, so the
same finite transfer form has strict rate `1 - epsilon`.

Crucially, the component mass cancels exactly after centering.  No lower bound
on that mass and no total-variation row estimate is used.  The analytic input
is therefore precisely a conditional transition / exact heat-weight ratio
lower bound.

No inhabitant of the minorization certificate is asserted here.  No cutoff-,
volume-, coupling-, beta-, or lattice-spacing-uniform estimate is claimed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
import YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVarianceGapBridge

namespace YMGap.Continuum.BF4PhysicalVacuumSectorConditionalMinorizationGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVariance
open YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVarianceGapBridge
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

/-- Cancellation-free rational-semantic polynomial normalization. -/
local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Generic normalized-product Dirichlet algebra -/

/-- Multiplying a finite joint by one scalar multiplies its entire directed
Dirichlet energy by the same scalar. -/
theorem finiteJointDirichletEnergy_scale_joint_eqv
    {State : Type} (states : List State) (coefficient : State → Q')
    (scale : Q') (joint : State → State → Q') :
    finiteJointDirichletEnergy states coefficient
        (fun left right => scale * joint left right) ≈
      scale * finiteJointDirichletEnergy states coefficient joint := by
  unfold finiteJointDirichletEnergy
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        scale * listQSum
          (fun right =>
            joint left right *
              ((coefficient left + -coefficient right) *
                (coefficient left + -coefficient right)))
          states)
      states) _ ?_ ?_
  · apply listQSum_congr
    intro left
    refine Q'.eqv_trans _
      (listQSum
        (fun right =>
          scale *
            (joint left right *
              ((coefficient left + -coefficient right) *
                (coefficient left + -coefficient right))))
        states) _ ?_ ?_
    · apply listQSum_congr
      intro right
      exact Q'.mul_assoc_eqv _ _ _
    · exact listQSum_mul_left scale _ states
  · exact listQSum_mul_left scale _ states

/-- Pointwise domination of finite joints is preserved after summing against
all squared coefficient differences. -/
theorem scale_mul_finiteJointDirichletEnergy_le_of_joint_le
    {State : Type} (states : List State) (coefficient : State → Q')
    (scale : Q') (lowerJoint upperJoint : State → State → Q')
    (hjoint : ∀ left, left ∈ states → ∀ right, right ∈ states →
      scale * lowerJoint left right ≤ upperJoint left right) :
    scale * finiteJointDirichletEnergy
        states coefficient lowerJoint ≤
      finiteJointDirichletEnergy states coefficient upperJoint := by
  have hsum :
      finiteJointDirichletEnergy states coefficient
          (fun left right => scale * lowerJoint left right) ≤
        finiteJointDirichletEnergy states coefficient upperJoint := by
    unfold finiteJointDirichletEnergy
    apply listQSum_mono
    intro left hleft
    apply listQSum_mono
    intro right hright
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (hjoint left hleft right hright)
      (SumOfSquares.q_mul_self_nonneg
        (coefficient left + -coefficient right))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (finiteJointDirichletEnergy_scale_joint_eqv
          states coefficient scale lowerJoint)))
    hsum

/-- On an exactly centered positive-mass component, the Dirichlet energy of
the mass-normalized stationary product is exactly twice the weighted square.
This is the cancellation that removes every component-mass floor. -/
theorem finiteCarrierMassNormalizedStationaryProductJoint_dirichlet_centered_eqv
    {State : Type} (states : List State) (mass : Q')
    (mass_pos : (0 : Q') < mass) (weight coefficient : State → Q')
    (hmass : finiteWeightedMass states weight ≈ mass)
    (hcenter : finiteListWeightedMean states weight coefficient ≈ 0) :
    finiteJointDirichletEnergy states coefficient
        (finiteCarrierMassNormalizedStationaryProductJoint
          mass mass_pos weight) ≈
      finiteWeightedSquare states weight coefficient +
        finiteWeightedSquare states weight coefficient := by
  let reciprocal := Q'.recipPos mass mass_pos
  let diagonal := finiteWeightedSquare states weight coefficient
  have hscale :
      finiteJointDirichletEnergy states coefficient
          (finiteCarrierMassNormalizedStationaryProductJoint
            mass mass_pos weight) ≈
        finiteWeightedPairwiseVariance states weight coefficient *
          reciprocal := by
    unfold finiteCarrierMassNormalizedStationaryProductJoint
      finiteWeightedPairwiseVariance reciprocal
    refine Q'.eqv_trans _
      (listQSum
        (fun left =>
          listQSum
            (fun right =>
              (finiteStationaryProductJoint weight left right *
                ((coefficient left + -coefficient right) *
                  (coefficient left + -coefficient right))) *
                Q'.recipPos mass mass_pos)
            states)
        states) _ ?_ ?_
    · unfold finiteJointDirichletEnergy
      apply listQSum_congr
      intro left
      apply listQSum_congr
      intro right
      q_ring
    · refine Q'.eqv_trans _
        (listQSum
          (fun left =>
            listQSum
              (fun right =>
                finiteStationaryProductJoint weight left right *
                  ((coefficient left + -coefficient right) *
                    (coefficient left + -coefficient right)))
              states * reciprocal)
          states) _ ?_ ?_
      · apply listQSum_congr
        intro left
        exact listQSum_mul_right _ reciprocal states
      · exact listQSum_mul_right _ reciprocal states
  have hpair :=
    finiteWeightedPairwiseVariance_centered_eqv_twice_mass_diagonal
      states weight coefficient hcenter
  have hpairMass :
      finiteWeightedPairwiseVariance states weight coefficient ≈
        mass * diagonal + mass * diagonal := by
    exact Q'.eqv_trans _ _ _ hpair
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ diagonal hmass)
        (Q'.mul_eqv_congr_right _ _ diagonal hmass))
  refine Q'.eqv_trans _
    (finiteWeightedPairwiseVariance states weight coefficient * reciprocal) _
    hscale ?_
  refine Q'.eqv_trans _
    ((mass * diagonal + mass * diagonal) * reciprocal) _
    (Q'.mul_eqv_congr_right _ _ reciprocal hpairMass) ?_
  refine Q'.eqv_trans _
    (((mass * reciprocal) * diagonal) +
      ((mass * reciprocal) * diagonal)) _ ?_ ?_
  · q_ring
  have hcancel : mass * reciprocal ≈ 1 := by
    exact Q'.mul_recipPos_eqv mass mass_pos
  exact Q'.add_eqv_congr'
    (Q'.eqv_trans _ (1 * diagonal) _
      (Q'.mul_eqv_congr_right _ _ diagonal hcancel)
      (Q'.one_mul_eqv diagonal))
    (Q'.eqv_trans _ (1 * diagonal) _
      (Q'.mul_eqv_congr_right _ _ diagonal hcancel)
      (Q'.one_mul_eqv diagonal))

/-! ## 2. The exact finite conditional-minorization certificate -/

/-- A pointwise Doeblin/minorization bound relative to the stationary law
conditioned on one positive-mass finite component. -/
structure FiniteCarrierConditionalMinorizationCertificate
    {State : Type} (states : List State) (mass epsilon : Q')
    (mass_pos : (0 : Q') < mass) (weight : State → Q')
    (kernel : State → State → Q') : Type 1 where
  epsilon_pos : (0 : Q') < epsilon
  epsilon_le_one : epsilon ≤ (1 : Q')
  minorization : ∀ left, left ∈ states → ∀ right, right ∈ states →
    epsilon *
        finiteCarrierMassNormalizedStationaryProductJoint
          mass mass_pos weight left right ≤
      kernel left right

namespace FiniteCarrierConditionalMinorizationCertificate

/-- Conditional minorization supplies the exact half-Dirichlet variance
margin.  Only centeredness and the equality between the named mass and the
finite weight sum enter the proof. -/
theorem varianceMargin
    {State : Type} {states : List State} {mass epsilon : Q'}
    {mass_pos : (0 : Q') < mass} {weight : State → Q'}
    {kernel : State → State → Q'}
    (certificate : FiniteCarrierConditionalMinorizationCertificate
      states mass epsilon mass_pos weight kernel)
    (coefficient : State → Q')
    (hmass : finiteWeightedMass states weight ≈ mass)
    (hcenter : finiteListWeightedMean states weight coefficient ≈ 0) :
    epsilon * finiteWeightedSquare states weight coefficient ≤
      Q'.mkPos 1 2 (by decide) *
        finiteJointDirichletEnergy states coefficient kernel := by
  let diagonal := finiteWeightedSquare states weight coefficient
  let reference := finiteCarrierMassNormalizedStationaryProductJoint
    mass mass_pos weight
  have hdomination :
      epsilon * finiteJointDirichletEnergy states coefficient reference ≤
        finiteJointDirichletEnergy states coefficient kernel :=
    scale_mul_finiteJointDirichletEnergy_le_of_joint_le
      states coefficient epsilon reference kernel certificate.minorization
  have href :
      finiteJointDirichletEnergy states coefficient reference ≈
        diagonal + diagonal :=
    finiteCarrierMassNormalizedStationaryProductJoint_dirichlet_centered_eqv
      states mass mass_pos weight coefficient hmass hcenter
  have htwice :
      epsilon * (diagonal + diagonal) ≤
        finiteJointDirichletEnergy states coefficient kernel :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left epsilon _ _ (Q'.eqv_symm href)))
      hdomination
  have hhalf := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.mkPos 1 2 (by decide)) htwice (by decide)
  have hcollapse :
      Q'.mkPos 1 2 (by decide) *
          (epsilon * (diagonal + diagonal)) ≈
        epsilon * diagonal := by
    refine Q'.eqv_trans _
      (Q'.mkPos 1 2 (by decide) *
        (epsilon * diagonal + epsilon * diagonal)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left (Q'.mkPos 1 2 (by decide)) _ _
        (Q'.mul_add_eqv epsilon diagonal diagonal)
    refine Q'.eqv_trans _
      (Q'.mkPos 1 2 (by decide) * (epsilon * diagonal) +
        Q'.mkPos 1 2 (by decide) * (epsilon * diagonal)) _ ?_ ?_
    · exact Q'.mul_add_eqv
        (Q'.mkPos 1 2 (by decide))
        (epsilon * diagonal) (epsilon * diagonal)
    · exact ExpNeg.two_halves (epsilon * diagonal)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hcollapse)) hhalf

end FiniteCarrierConditionalMinorizationCertificate

/-! ## 3. Literal physical BF4 specialization -/

/-- A finite physical BF4 vacuum sector whose genuine reflected joint
dominates a positive fraction of its component-conditioned stationary
product.  This is the exact finite heat-weight/conditional-transition input;
there is no hidden component-mass hypothesis. -/
structure CentralPhysicalFiniteConditionalMinorizationGapData
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) where
  fraction : Q'
  fraction_pos : (0 : Q') < fraction
  fraction_le_one : fraction ≤ (1 : Q')
  minorization : ∀ left,
    left ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
    ∀ right,
    right ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
      fraction *
          finiteCarrierMassNormalizedStationaryProductJoint
            (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
            (centralPhysicalFiniteVacuumSectorWeightSum_pos
              w hw cutoff half)
            (centralPhysicalFiniteWeight w hw cutoff half)
            left right ≤
        centralPhysicalFiniteKernel w hw cutoff half left right

namespace CentralPhysicalFiniteConditionalMinorizationGapData

/-- Forget only the BF4 names and expose the generic finite certificate. -/
def finiteCertificate
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (data : CentralPhysicalFiniteConditionalMinorizationGapData
      w hw cutoff half) :
    FiniteCarrierConditionalMinorizationCertificate
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
      data.fraction
      (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
      (centralPhysicalFiniteWeight w hw cutoff half)
      (centralPhysicalFiniteKernel w hw cutoff half) where
  epsilon_pos := data.fraction_pos
  epsilon_le_one := data.fraction_le_one
  minorization := data.minorization

/-- The pointwise conditional transition lower bound constructs the already
identified posterior-variance gap data with exactly the same fraction. -/
def toConditionalVarianceGapData
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (data : CentralPhysicalFiniteConditionalMinorizationGapData
      w hw cutoff half) :
    CentralPhysicalFiniteConditionalVarianceGapData w hw cutoff half where
  fraction := data.fraction
  fraction_pos := data.fraction_pos
  fraction_le_one := data.fraction_le_one
  conditionalVarianceMargin := by
    intro coefficient hcenter
    let states :=
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
    let weight := centralPhysicalFiniteWeight w hw cutoff half
    have hmass : finiteWeightedMass states weight ≈
        centralPhysicalFiniteVacuumSectorMass w hw cutoff half := by
      unfold centralPhysicalFiniteVacuumSectorMass states weight
      exact Q'.eqv_refl _
    have hgeneric := data.finiteCertificate.varianceMargin coefficient
      hmass
      hcenter
    have hdiagonal :
        finiteWeightedSquare states weight coefficient ≈
          centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            w hw cutoff half coefficient := by
      unfold finiteWeightedSquare
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic states weight
      apply listQSum_congr
      intro index
      exact Q'.mul_comm_eqv _ _
    have hdirichlet :=
      centralPhysicalFiniteVacuumSectorDirichlet_eqv_conditionalPairwiseVariance
        w hw cutoff half coefficient
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left data.fraction _ _
          (Q'.eqv_symm hdiagonal)))
      (Q'.le_trans' _ _ _ hgeneric
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left (Q'.mkPos 1 2 (by decide)) _ _
            hdirichlet)))

theorem toConditionalVarianceGapData_fraction
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (data : CentralPhysicalFiniteConditionalMinorizationGapData
      w hw cutoff half) :
    data.toConditionalVarianceGapData.fraction = data.fraction := rfl

/-- Consequently the literal finite BF4 transfer form has strict rate
`1 - fraction`, with no change of constants. -/
theorem formBound
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (data : CentralPhysicalFiniteConditionalMinorizationGapData
      w hw cutoff half)
    (coefficient : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean
      w hw cutoff half coefficient ≈ 0) :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw cutoff half coefficient ≤
      ((1 : Q') + (-data.fraction)) *
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw cutoff half coefficient := by
  exact data.toConditionalVarianceGapData.formBound coefficient hcenter

end CentralPhysicalFiniteConditionalMinorizationGapData

end YMGap.Continuum.BF4PhysicalVacuumSectorConditionalMinorizationGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionalMinorizationGap.finiteJointDirichletEnergy_scale_joint_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionalMinorizationGap.scale_mul_finiteJointDirichletEnergy_le_of_joint_le
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionalMinorizationGap.finiteCarrierMassNormalizedStationaryProductJoint_dirichlet_centered_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionalMinorizationGap.FiniteCarrierConditionalMinorizationCertificate.varianceMargin
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionalMinorizationGap.CentralPhysicalFiniteConditionalMinorizationGapData.toConditionalVarianceGapData
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionalMinorizationGap.CentralPhysicalFiniteConditionalMinorizationGapData.formBound
