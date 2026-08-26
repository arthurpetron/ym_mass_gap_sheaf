/-
# The BF4 vacuum-sector boundary transform

Reflection positivity factors the finite physical BF4 kernel through the
fixed-time boundary carrier.  This file keeps the resulting mathematics in
operator form.  For a coefficient vector `f`, define the boundary numerator

    C f (b) = sum_x f(x) A(x,b).

Then the physical same-object quadratic is exactly

    sum_b W(b) (C f (b))^2.

Moreover, subtracting the stationary component from every half-amplitude
changes `C f` by only

    -(sum_x f(x) pi(x)) B(b).

Thus on the vacuum complement the raw and centered boundary transforms are
identical.  Consequently a strict physical form bound is *equivalent* to one
weighted boundary-transform estimate.  After normalization by the positive
channel total, this is the finite conditional expectation
`E[f(X) | boundary]`; the remaining uniform analytic problem is therefore a
maximal-correlation/singular-value bound, not another carrier compiler.

No uniform bound is asserted here.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram

namespace YMGap.Continuum.BF4PhysicalVacuumSectorBoundaryTransform

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

private theorem one_num_local : (1 : Q').num = 1 := rfl

private theorem one_den_local : (1 : Q').den = 1 := rfl

/-- Cancellation-free rational-semantic polynomial normalization. -/
local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.ofInt, Q'.ofNat, Q'.neg,
               one_num_local, one_den_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try simp;
             try omega;
             try ac_rfl))

private theorem listQSum_neg_local
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      listQSum (fun item => -(value item)) items ≈
        -(listQSum value items)
  | [] => by
      change (0 : Q') ≈ -(0 : Q')
      decide
  | head :: tail => by
      change -(value head) +
          listQSum (fun item => -(value item)) tail ≈
        -(value head + listQSum value tail)
      refine Q'.eqv_trans _
        (-(value head) + -(listQSum value tail)) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_neg_local value tail)) ?_
      exact Q'.eqv_symm
        (Q'.neg_add_eqv (value head) (listQSum value tail))

/-! ## 1. Centering is rank one at the boundary-transform level -/

/-- Centering the half-amplitude changes its boundary transform by exactly
the state mean times the channel-total half-amplitude. -/
theorem channelLinear_centered_eqv_raw_sub_mean_mul_total
    {State Channel : Type}
    (states : List State)
    (amplitude : State → Channel → Q')
    (marginal coefficient : State → Q')
    (channel : Channel) :
    channelLinear states
        (finiteMarginalCenteredAmplitude states amplitude marginal)
        coefficient channel ≈
      channelLinear states amplitude coefficient channel +
        (-(listQSum
            (fun state => coefficient state * marginal state)
            states *
          finiteChannelTotalAmplitude states amplitude channel)) := by
  let total := finiteChannelTotalAmplitude states amplitude channel
  let raw := fun state => coefficient state * amplitude state channel
  let mean := fun state => coefficient state * marginal state
  have hpoint : ∀ state,
      coefficient state *
          finiteMarginalCenteredAmplitude
            states amplitude marginal state channel ≈
        raw state + (-(mean state * total)) := by
    intro state
    unfold finiteMarginalCenteredAmplitude raw mean total
    q_ring
  unfold channelLinear
  refine Q'.eqv_trans _
    (listQSum
      (fun state => raw state + (-(mean state * total))) states) _
    (listQSum_congr hpoint states) ?_
  refine Q'.eqv_trans _
    (listQSum raw states +
      listQSum (fun state => -(mean state * total)) states) _
    (listQSum_add raw (fun state => -(mean state * total)) states) ?_
  apply Q'.add_eqv_congr_left
  refine Q'.eqv_trans _
    (-(listQSum (fun state => mean state * total) states)) _
    (listQSum_neg_local (fun state => mean state * total) states) ?_
  exact Q'.neg_eqv_congr _ _
    (listQSum_mul_right mean total states)

/-- A mean-zero vector cannot see the rank-one centering correction. -/
theorem channelLinear_centered_eqv_raw_of_mean_zero
    {State Channel : Type}
    (states : List State)
    (amplitude : State → Channel → Q')
    (marginal coefficient : State → Q')
    (channel : Channel)
    (hmean :
      listQSum
          (fun state => coefficient state * marginal state)
          states ≈ 0) :
    channelLinear states
        (finiteMarginalCenteredAmplitude states amplitude marginal)
        coefficient channel ≈
      channelLinear states amplitude coefficient channel := by
  refine Q'.eqv_trans _
    (channelLinear states amplitude coefficient channel +
      (-(listQSum
          (fun state => coefficient state * marginal state)
          states *
        finiteChannelTotalAmplitude states amplitude channel))) _
    (channelLinear_centered_eqv_raw_sub_mean_mul_total
      states amplitude marginal coefficient channel) ?_
  refine Q'.eqv_trans _
    (channelLinear states amplitude coefficient channel +
      (-(0 * finiteChannelTotalAmplitude states amplitude channel))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ _ hmean))
  refine Q'.eqv_trans _
    (channelLinear states amplitude coefficient channel + (-0)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _
        (Q'.zero_mul_eqv
          (finiteChannelTotalAmplitude states amplitude channel)))
  refine Q'.eqv_trans _
    (channelLinear states amplitude coefficient channel + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _ (by decide)
  exact Q'.eqv_of_eq (Q'.add_zero' _)

/-! ## 2. The concrete physical transform and its energy -/

/-- The unnormalized conditional-expectation numerator on the literal BF4
fixed-time boundary carrier. -/
def centralPhysicalFiniteVacuumSectorBoundaryTransform
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') (boundary : EdgeLabelling) : Q' :=
  channelLinear
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)
    coefficient boundary

/-- The same transform formed from the component-centered physical
half-amplitudes. -/
def centralPhysicalFiniteVacuumSectorCenteredBoundaryTransform
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') (boundary : EdgeLabelling) : Q' :=
  channelLinear
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorCenteredGramAmplitude
      w hw cutoff half)
    coefficient boundary

/-- Squared weighted norm of the concrete boundary transform. -/
def centralPhysicalFiniteVacuumSectorBoundaryTransformEnergy
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') : Q' :=
  weightedGramSOS
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralBoundaryChannels cutoff half)
    (centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)
    coefficient

/-- The energy definition exposes the literal sum over the concrete boundary
carrier; there is no hidden matrix square root. -/
theorem centralPhysicalFiniteVacuumSectorBoundaryTransformEnergy_eq_explicit
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorBoundaryTransformEnergy
        w hw cutoff half coefficient =
      listQSum
        (fun boundary =>
          centralPhysicalFiniteVacuumSectorGramWeight
              w hw cutoff half boundary *
            (centralPhysicalFiniteVacuumSectorBoundaryTransform
                w hw cutoff half coefficient boundary *
              centralPhysicalFiniteVacuumSectorBoundaryTransform
                w hw cutoff half coefficient boundary))
        (centralBoundaryChannels cutoff half) := rfl

/-- The physical same-object quadratic is exactly the squared boundary
transform norm. -/
theorem centralPhysicalFiniteVacuumSectorMatrixQuadratic_eqv_boundaryTransformEnergy
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw cutoff half coefficient ≈
      centralPhysicalFiniteVacuumSectorBoundaryTransformEnergy
        w hw cutoff half coefficient := by
  refine Q'.eqv_trans _
    (weightedGramQuadratic
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      (centralBoundaryChannels cutoff half)
      (centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)
      coefficient) _
    (centralPhysicalFiniteVacuumSectorMatrixQuadratic_eqv_weightedGram
      w hw cutoff half coefficient) ?_
  exact weightedGramQuadratic_eq_sos
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralBoundaryChannels cutoff half)
    (centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)
    coefficient

/-- Raw centering against the sector weight implies centering against the
conditioned probability weight. -/
theorem centralPhysicalFiniteVacuumSector_normalizedMean_eqv_zero
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {coefficient : Nat → Q'}
    (hcenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
        w hw cutoff half coefficient ≈ 0) :
    listQSum
        (fun index =>
          coefficient index *
            centralPhysicalFiniteVacuumSectorMassNormalizedWeight
              w hw cutoff half index)
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) ≈
      0 := by
  let states :=
    centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  let reciprocal :=
    Q'.recipPos
      (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
  let rawMean := fun index =>
    coefficient index *
      centralPhysicalFiniteWeight w hw cutoff half index
  refine Q'.eqv_trans _
    (listQSum (fun index => rawMean index * reciprocal) states) _ ?_ ?_
  · apply listQSum_congr
    intro index
    unfold rawMean reciprocal
      centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      finiteCarrierMassNormalizedWeight Q'.divPos
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (coefficient index)
        (centralPhysicalFiniteWeight w hw cutoff half index)
        (Q'.recipPos
          (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorWeightSum_pos
            w hw cutoff half)))
  refine Q'.eqv_trans _
    (listQSum rawMean states * reciprocal) _
    (listQSum_mul_right rawMean reciprocal states) ?_
  refine Q'.eqv_trans _ (0 * reciprocal) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ reciprocal (by
      unfold rawMean states
      exact hcenter)
  exact Q'.zero_mul_eqv reciprocal

/-- On the physical vacuum complement, centering the half-amplitudes does
not change the boundary transform. -/
theorem centralPhysicalFiniteVacuumSector_centeredBoundaryTransform_eqv_raw
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {coefficient : Nat → Q'}
    (hcenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
        w hw cutoff half coefficient ≈ 0)
    (boundary : EdgeLabelling) :
    centralPhysicalFiniteVacuumSectorCenteredBoundaryTransform
        w hw cutoff half coefficient boundary ≈
      centralPhysicalFiniteVacuumSectorBoundaryTransform
        w hw cutoff half coefficient boundary := by
  unfold centralPhysicalFiniteVacuumSectorCenteredBoundaryTransform
    centralPhysicalFiniteVacuumSectorBoundaryTransform
    centralPhysicalFiniteVacuumSectorCenteredGramAmplitude
  exact channelLinear_centered_eqv_raw_of_mean_zero
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGramAmplitude w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight w hw cutoff half)
    coefficient boundary
    (centralPhysicalFiniteVacuumSector_normalizedMean_eqv_zero hcenter)

/-! ## 3. Exact analytic frontier -/

/-- Pointwise equivalence between the same-object form estimate and the
boundary-transform energy estimate.  The centering hypothesis records the
physical vacuum complement even though the algebraic Gram identity itself
holds for every coefficient vector. -/
theorem centralPhysicalFiniteVacuumSector_formBound_iff_boundaryTransformBound
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q')
    (_hcenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
        w hw cutoff half coefficient ≈ 0)
    (rate : Q') :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w hw cutoff half coefficient ≤
        rate * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw cutoff half coefficient ↔
      centralPhysicalFiniteVacuumSectorBoundaryTransformEnergy
          w hw cutoff half coefficient ≤
        rate * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw cutoff half coefficient := by
  constructor
  · intro hform
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (centralPhysicalFiniteVacuumSectorMatrixQuadratic_eqv_boundaryTransformEnergy
          w hw cutoff half coefficient))
      hform
  · intro hboundary
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (centralPhysicalFiniteVacuumSectorMatrixQuadratic_eqv_boundaryTransformEnergy
          w hw cutoff half coefficient))
      hboundary

/-- For a fixed physical cutoff, the complete mean-zero form inequality is
exactly the complete mean-zero boundary-transform inequality. -/
theorem centralPhysicalFiniteVacuumSector_allCenteredFormBounds_iff_boundaryTransformBounds
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (rate : Q') :
    (∀ coefficient : Nat → Q',
        centralPhysicalFiniteVacuumSectorWeightedMean
            w hw cutoff half coefficient ≈ 0 →
          centralPhysicalFiniteVacuumSectorMatrixQuadratic
              w hw cutoff half coefficient ≤
            rate * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
              w hw cutoff half coefficient) ↔
      (∀ coefficient : Nat → Q',
        centralPhysicalFiniteVacuumSectorWeightedMean
            w hw cutoff half coefficient ≈ 0 →
          centralPhysicalFiniteVacuumSectorBoundaryTransformEnergy
              w hw cutoff half coefficient ≤
            rate * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
              w hw cutoff half coefficient) := by
  constructor
  · intro hform coefficient hcenter
    exact
      (centralPhysicalFiniteVacuumSector_formBound_iff_boundaryTransformBound
        w hw cutoff half coefficient hcenter rate).mp
        (hform coefficient hcenter)
  · intro hboundary coefficient hcenter
    exact
      (centralPhysicalFiniteVacuumSector_formBound_iff_boundaryTransformBound
        w hw cutoff half coefficient hcenter rate).mpr
        (hboundary coefficient hcenter)

end YMGap.Continuum.BF4PhysicalVacuumSectorBoundaryTransform

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorBoundaryTransform.channelLinear_centered_eqv_raw_sub_mean_mul_total
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorBoundaryTransform.centralPhysicalFiniteVacuumSectorMatrixQuadratic_eqv_boundaryTransformEnergy
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorBoundaryTransform.centralPhysicalFiniteVacuumSector_centeredBoundaryTransform_eqv_raw
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorBoundaryTransform.centralPhysicalFiniteVacuumSector_formBound_iff_boundaryTransformBound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorBoundaryTransform.centralPhysicalFiniteVacuumSector_allCenteredFormBounds_iff_boundaryTransformBounds
