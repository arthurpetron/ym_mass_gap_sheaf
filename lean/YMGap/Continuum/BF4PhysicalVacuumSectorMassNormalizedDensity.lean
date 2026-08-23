/-
# Conditional density on a positive-mass BF4 vacuum component

For a closed stationary component `S` with mass `m`, the conditioned law is

    pi_S(x) = pi(x) / m,
    J_S(x,y) = J(x,y) / m,
    k_S(x,y) = J_S(x,y) / (pi_S(x) pi_S(y)).

Equivalently, `J(x,y) = pi(x) pi_S(y) k_S(x,y)`.  This file constructs that
density using only positive rational division and proves the exact row identity

    sum_y |J(x,y) - pi(x)pi(y)/m|
      = pi(x) sum_y pi_S(y) |k_S(x,y)-1|.

Consequently the existing generic `1/32 + 1/64 + 1/64` core/tail lemma gives
the corrected component-conditioned row bound at rate `1/16`.  The physical
specialization is only to the graph-defined canonical vacuum sector.

No core/tail witness is asserted here.  No thermodynamic or continuum limit
is constructed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedFiniteChecker
import YMGap.Continuum.BF4PhysicalConditionalDensityContraction

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalConditionalDensityContraction
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSignedKernelL1
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RcQuadResidualClose
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.TsumDeriv.Q'

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Generic component-conditioned density -/

/-- Stationary probability weight after conditioning on a component of
positive mass. -/
def finiteCarrierMassNormalizedWeight
    {State : Type} (mass : Q') (mass_pos : (0 : Q') < mass)
    (weight : State → Q') (state : State) : Q' :=
  Q'.divPos (weight state) mass mass_pos

/-- The component-conditioned density of a joint relative to its conditioned
stationary product.  It is zero only where that reference entry is not
strictly positive. -/
def finiteCarrierMassNormalizedDensity
    {State : Type} (mass : Q') (mass_pos : (0 : Q') < mass)
    (weight : State → Q') (joint : State → State → Q')
    (source target : State) : Q' :=
  if href : (0 : Q') <
      finiteCarrierMassNormalizedStationaryProductJoint
        mass mass_pos weight source target then
    Q'.divPos (joint source target)
      (finiteCarrierMassNormalizedStationaryProductJoint
        mass mass_pos weight source target) href
  else 0

/-- Positive endpoint weights make the component-conditioned stationary
reference entry strictly positive. -/
theorem finiteCarrierMassNormalizedStationaryProductJoint_pos
    {State : Type} {mass : Q'} {mass_pos : (0 : Q') < mass}
    {weight : State → Q'} {source target : State}
    (hsource : (0 : Q') < weight source)
    (htarget : (0 : Q') < weight target) :
    (0 : Q') <
      finiteCarrierMassNormalizedStationaryProductJoint
        mass mass_pos weight source target := by
  unfold finiteCarrierMassNormalizedStationaryProductJoint
    finiteStationaryProductJoint
  exact Q'.mul_pos (Q'.mul_pos hsource htarget)
    (Q'.recipPos_pos mass mass_pos)

/-- On positive endpoint weights the density is the literal positive
division by the conditioned stationary reference. -/
theorem finiteCarrierMassNormalizedDensity_eq_divPos
    {State : Type} {mass : Q'} {mass_pos : (0 : Q') < mass}
    {weight : State → Q'} {joint : State → State → Q'}
    {source target : State}
    (hsource : (0 : Q') < weight source)
    (htarget : (0 : Q') < weight target) :
    finiteCarrierMassNormalizedDensity
        mass mass_pos weight joint source target =
      Q'.divPos (joint source target)
        (finiteCarrierMassNormalizedStationaryProductJoint
          mass mass_pos weight source target)
        (finiteCarrierMassNormalizedStationaryProductJoint_pos
          hsource htarget) := by
  unfold finiteCarrierMassNormalizedDensity
  rw [dif_pos
    (finiteCarrierMassNormalizedStationaryProductJoint_pos
      hsource htarget)]

/-- Multiplication by the conditioned stationary reference exactly recovers
the joint entry. -/
theorem finiteCarrierMassNormalizedStationaryProduct_mul_density_eqv_joint
    {State : Type} {mass : Q'} {mass_pos : (0 : Q') < mass}
    {weight : State → Q'} {joint : State → State → Q'}
    {source target : State}
    (hsource : (0 : Q') < weight source)
    (htarget : (0 : Q') < weight target) :
    finiteCarrierMassNormalizedStationaryProductJoint
          mass mass_pos weight source target *
        finiteCarrierMassNormalizedDensity
          mass mass_pos weight joint source target ≈
      joint source target := by
  rw [finiteCarrierMassNormalizedDensity_eq_divPos hsource htarget]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv
      (finiteCarrierMassNormalizedStationaryProductJoint
        mass mass_pos weight source target)
      (Q'.divPos (joint source target)
        (finiteCarrierMassNormalizedStationaryProductJoint
          mass mass_pos weight source target)
        (finiteCarrierMassNormalizedStationaryProductJoint_pos
          hsource htarget)))
    (Q'.divPos_mul_eqv _ _ _)

/-- Dividing every weight by its positive total mass produces an exact finite
probability weight. -/
theorem finiteCarrierMassNormalizedWeight_total_one
    {State : Type} (states : List State)
    (mass : Q') (mass_pos : (0 : Q') < mass)
    (weight : State → Q')
    (hmass : listQSum weight states ≈ mass) :
    listQSum
        (finiteCarrierMassNormalizedWeight mass mass_pos weight)
        states ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum weight states * Q'.recipPos mass mass_pos) _ ?_ ?_
  · unfold finiteCarrierMassNormalizedWeight Q'.divPos
    exact listQSum_mul_right weight (Q'.recipPos mass mass_pos) states
  · exact Q'.eqv_trans _
      (mass * Q'.recipPos mass mass_pos) _
      (Q'.mul_eqv_congr_right _ _ _ hmass)
      (Q'.mul_recipPos_eqv mass mass_pos)

/-- One centered joint entry is the source weight times the corresponding
conditioned weighted-density entry. -/
theorem finiteCarrierMassNormalized_centeredEntry_eqv
    {State : Type} {mass : Q'} {mass_pos : (0 : Q') < mass}
    {weight : State → Q'} {joint : State → State → Q'}
    {source target : State}
    (hsource : (0 : Q') < weight source)
    (htarget : (0 : Q') < weight target) :
    joint source target +
        (-finiteCarrierMassNormalizedStationaryProductJoint
          mass mass_pos weight source target) ≈
      weight source *
        finiteWeightedCenteredTransition
          (finiteCarrierMassNormalizedWeight mass mass_pos weight)
          (finiteCarrierMassNormalizedDensity
            mass mass_pos weight joint)
          source target := by
  let reference :=
    finiteCarrierMassNormalizedStationaryProductJoint
      mass mass_pos weight source target
  let density := finiteCarrierMassNormalizedDensity
    mass mass_pos weight joint source target
  have hrecover : reference * density ≈ joint source target :=
    finiteCarrierMassNormalizedStationaryProduct_mul_density_eqv_joint
      hsource htarget
  refine Q'.eqv_trans _
    (reference * density + (-reference)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hrecover)
  · unfold reference density
      finiteWeightedCenteredTransition finiteCenteredDensity
      finiteCarrierMassNormalizedWeight Q'.divPos
      finiteCarrierMassNormalizedStationaryProductJoint
      finiteStationaryProductJoint
    q_ring

/-- **Exact conditioned-density row identity.**  The corrected row distance
from component equilibrium is the source stationary weight times the
conditioned weighted `L1` density distance from one. -/
theorem finiteCarrierMassNormalizedRowDistance_eqv_densityCenteredRowMass
    {State : Type} {states : List State}
    {mass : Q'} {mass_pos : (0 : Q') < mass}
    {weight : State → Q'} {joint : State → State → Q'}
    {source : State}
    (hsource : (0 : Q') < weight source)
    (htarget : ∀ target, target ∈ states →
      (0 : Q') < weight target) :
    finiteJointDifferenceAbsRowMass states joint
        (finiteCarrierMassNormalizedStationaryProductJoint
          mass mass_pos weight) source ≈
      weight source *
        finiteWeightedCenteredRowMass states
          (finiteCarrierMassNormalizedWeight mass mass_pos weight)
          (finiteCarrierMassNormalizedDensity
            mass mass_pos weight joint)
          source := by
  have hsourceNonnegative : (0 : Q') ≤ weight source :=
    Q'.le_of_lt hsource
  unfold finiteJointDifferenceAbsRowMass
    finiteWeightedCenteredRowMass finiteL1Norm
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        weight source *
          Q'.abs
            (finiteWeightedCenteredTransition
              (finiteCarrierMassNormalizedWeight mass mass_pos weight)
              (finiteCarrierMassNormalizedDensity
                mass mass_pos weight joint)
              source target))
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro target htargetMem
    refine Q'.eqv_trans _
      (Q'.abs
        (weight source *
          finiteWeightedCenteredTransition
            (finiteCarrierMassNormalizedWeight mass mass_pos weight)
            (finiteCarrierMassNormalizedDensity
              mass mass_pos weight joint)
            source target)) _ ?_ ?_
    · exact Q'.abs_eqv_congr
        (finiteCarrierMassNormalized_centeredEntry_eqv
          hsource (htarget target htargetMem))
    refine Q'.eqv_trans _
      (Q'.abs (weight source) *
        Q'.abs
          (finiteWeightedCenteredTransition
            (finiteCarrierMassNormalizedWeight mass mass_pos weight)
            (finiteCarrierMassNormalizedDensity
              mass mass_pos weight joint)
            source target)) _ ?_ ?_
    · exact q_abs_mul_eqv _ _
    · exact Q'.mul_eqv_congr_right _ _ _
        (abs_of_nonneg hsourceNonnegative)
  · exact listQSum_mul_left (weight source)
        (fun target =>
          Q'.abs
            (finiteWeightedCenteredTransition
              (finiteCarrierMassNormalizedWeight mass mass_pos weight)
              (finiteCarrierMassNormalizedDensity
                mass mass_pos weight joint)
              source target))
        states

/-- A conditioned `1/32 + 1/64 + 1/64` core/tail window gives the corrected
row distance at rate `1/16`, without a component-mass loss. -/
theorem finiteCarrierMassNormalizedRowDistance_le_sixteenth_of_coreTail
    {State : Type} {states : List State}
    {mass : Q'} {mass_pos : (0 : Q') < mass}
    {weight : State → Q'} {joint : State → State → Q'}
    {source : State} {inCore : State → Bool}
    (hsource : (0 : Q') < weight source)
    (htarget : ∀ target, target ∈ states →
      (0 : Q') < weight target)
    (window :
      FiniteWeightedDensityCoreTailWindow states
        (finiteCarrierMassNormalizedWeight mass mass_pos weight)
        (finiteCarrierMassNormalizedDensity
          mass mass_pos weight joint)
        source inCore
        (Q'.mkPos 1 32 (by decide))
        (Q'.mkPos 1 64 (by decide))) :
    finiteJointDifferenceAbsRowMass states joint
        (finiteCarrierMassNormalizedStationaryProductJoint
          mass mass_pos weight) source ≤
      Q'.mkPos 1 16 (by decide) * weight source := by
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
    window.density_centered_row_sixteenth (Q'.le_of_lt hsource)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (finiteCarrierMassNormalizedRowDistance_eqv_densityCenteredRowMass
        hsource htarget)) ?_
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv
      (Q'.mul_comm_eqv
        (weight source) (Q'.mkPos 1 16 (by decide))))

/-! ## 2. Canonical BF4 vacuum-sector specialization -/

def centralPhysicalFiniteVacuumSectorMassNormalizedWeight
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half index : Nat) : Q' :=
  finiteCarrierMassNormalizedWeight
    (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
    (centralPhysicalFiniteWeight w hw cutoff half) index

def centralPhysicalFiniteVacuumSectorMassNormalizedDensity
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source target : Nat) : Q' :=
  finiteCarrierMassNormalizedDensity
    (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
    (centralPhysicalFiniteWeight w hw cutoff half)
    (centralPhysicalFiniteKernel w hw cutoff half)
    source target

/-- The conditioned stationary weight on the canonical component has total
mass exactly one. -/
theorem centralPhysicalFiniteVacuumSectorMassNormalizedWeight_total_one
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    listQSum
        (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) ≈ 1 := by
  let states := centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  let weight := centralPhysicalFiniteWeight w hw cutoff half
  let mass := centralPhysicalFiniteVacuumSectorMass w hw cutoff half
  let mass_pos :=
    centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half
  refine Q'.eqv_trans _
    (listQSum weight states * Q'.recipPos mass mass_pos) _ ?_ ?_
  · unfold centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      finiteCarrierMassNormalizedWeight Q'.divPos states weight mass mass_pos
    exact listQSum_mul_right _ _ _
  · unfold mass centralPhysicalFiniteVacuumSectorMass
      finiteWeightedMass states weight mass_pos
    exact Q'.mul_recipPos_eqv _ _

end YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity.finiteCarrierMassNormalizedStationaryProduct_mul_density_eqv_joint
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity.finiteCarrierMassNormalizedWeight_total_one
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity.finiteCarrierMassNormalized_centeredEntry_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity.finiteCarrierMassNormalizedRowDistance_eqv_densityCenteredRowMass
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity.finiteCarrierMassNormalizedRowDistance_le_sixteenth_of_coreTail
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity.centralPhysicalFiniteVacuumSectorMassNormalizedWeight_total_one
