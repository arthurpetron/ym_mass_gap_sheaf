/-
# Outer-cutoff-uniform SU(2) dimension-weighted tensor tails

The existing dimension-weighted heat tail controls the one-label mass needed
by Clebsch--Gordan fusion.  This module tensors that estimate without paying
the cardinality of the later Peter--Weyl cutoff.

For retained doubled-spin cutoff `M` and later cutoff `K`, the omitted labels
are `M+1,...,K`.  Once `M+1` is beyond the explicit weighted-label cutoff,
their total dimension-weighted mass is at most

  2 * weightedChanCoeff q (M+1),

independently of `K`.  A constructive union recursion then gives a bound for
any fixed finite number of free label coordinates:

  E 0       = 0
  E (d + 1) = tail * ceiling^d + ceiling * E d.

This is the SU(2) analogue of the scalar tensor layer used by the U(1)
outer-cutoff proof.  It is intentionally prior to the interacting slab
Fubini step: the actual SU(2) spin-foam term also contains link intertwiner
multiplicities.  Those multiplicities require the repository's
spin-dependent local bound before this free-coordinate envelope can dominate
the physical new sector.

## Axiom gate

Finite `Nat`/`Q'` recursion only.  No `Classical.*`, `Real`, `native_decide`,
`sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.SU2DimensionWeightedHeatTail

namespace YMGap.Continuum.SU2OuterCutoffUniformTensorTail

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2DimensionWeightedHeatTail

local infix:50 " ≈ " => Q'.eqv

private theorem add_nonnegative {a b : Q'}
    (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) :
    (0 : Q') ≤ a + b := by
  have h := Q'.add_le_add ha hb
  rw [Q'.zero_add'] at h
  exact h

private theorem finSum_nonnegative_local
    (f : Nat → Q')
    (hf : ∀ index, (0 : Q') ≤ f index) :
    ∀ length, (0 : Q') ≤ finSum f length
  | 0 => Q'.le_refl' 0
  | length + 1 =>
      add_nonnegative
        (finSum_nonnegative_local f hf length)
        (hf length)

/-! ## 1. One-coordinate outer shell -/

/-- Dimension-weighted heat mass on the labels strictly above `M` and at
most `K`.  When `M ≤ K`, this is exactly the block `M+1,...,K`. -/
def su2WeightedOuterShellMass
    (q : Q') (M K : Nat) : Q' :=
  weightedDiscardedPartial q (M + 1) (K - M)

/-- All labels through `K`, with `K` interpreted as an inclusive cutoff. -/
def su2WeightedLabelPartial
    (q : Q') (K : Nat) : Q' :=
  finSum (weightedChanCoeff q) (K + 1)

/-- The cutoff-independent one-coordinate ceiling already supplied by the
dimension-weighted heat-tail layer. -/
def su2WeightedHeatCeiling (q : Q') : Q' :=
  weightedOnePlaquetteCeiling q
    (explicitWeightedLabelCutoff q)

/-- One-coordinate tail used by the tensor recursion. -/
def su2WeightedClosedTail (q : Q') (M : Nat) : Q' :=
  weightedChanCoeff q (M + 1) * Q'.ofNat 2

theorem su2WeightedOuterShellMass_nonnegative
    {q : Q'} (hq0 : (0 : Q') < q)
    (M K : Nat) :
    (0 : Q') ≤ su2WeightedOuterShellMass q M K := by
  unfold su2WeightedOuterShellMass weightedDiscardedPartial
  exact finSum_nonnegative_local _
    (fun offset =>
      weightedChanCoeff_nonneg
        (Q'.le_of_lt hq0) (M + 1 + offset))
    _

theorem su2WeightedLabelPartial_nonnegative
    {q : Q'} (hq0 : (0 : Q') < q)
    (K : Nat) :
    (0 : Q') ≤ su2WeightedLabelPartial q K := by
  unfold su2WeightedLabelPartial
  exact finSum_nonnegative_local _
    (weightedChanCoeff_nonneg (Q'.le_of_lt hq0))
    _

theorem su2WeightedHeatCeiling_nonnegative
    {q : Q'} (hq0 : (0 : Q') < q) :
    (0 : Q') ≤ su2WeightedHeatCeiling q := by
  unfold su2WeightedHeatCeiling weightedOnePlaquetteCeiling
  exact add_nonnegative
    (finSum_nonnegative_local _
      (weightedChanCoeff_nonneg (Q'.le_of_lt hq0))
      (explicitWeightedLabelCutoff q))
    (Q'.mul_nonneg _ _
      (weightedChanCoeff_nonneg
        (Q'.le_of_lt hq0)
        (explicitWeightedLabelCutoff q))
      (by decide))

theorem su2WeightedClosedTail_nonnegative
    {q : Q'} (hq0 : (0 : Q') < q)
    (M : Nat) :
    (0 : Q') ≤ su2WeightedClosedTail q M := by
  unfold su2WeightedClosedTail
  exact Q'.mul_nonneg _ _
    (weightedChanCoeff_nonneg
      (Q'.le_of_lt hq0) (M + 1))
    (by decide)

/-- The outer one-coordinate shell is independent of the later cutoff. -/
theorem su2WeightedOuterShellMass_le_closedTail
    {q : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q'))
    {M K : Nat}
    (hcut : explicitWeightedLabelCutoff q ≤ M + 1) :
    su2WeightedOuterShellMass q M K ≤
      su2WeightedClosedTail q M := by
  unfold su2WeightedOuterShellMass su2WeightedClosedTail
  exact weightedDiscardedPartial_le_twoLead
    (Q'.le_of_lt hq0)
    (Q'.le_trans' _ _ _
      (Q'.le_of_lt hq1) (Q'.le_refl' 1))
    (M + 1) (by omega)
    (weightedDiscardedRatio_le_half_of_cutoff
      hq0 hq1 hcut)
    (K - M)

/-- Every inclusive finite label partial obeys one ceiling independent of
the outer cutoff. -/
theorem su2WeightedLabelPartial_le_heatCeiling
    {q : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q'))
    (K : Nat) :
    su2WeightedLabelPartial q K ≤
      su2WeightedHeatCeiling q := by
  unfold su2WeightedLabelPartial su2WeightedHeatCeiling
  exact weightedAllLabelPartial_le_explicitCeiling
    hq0 hq1 (K + 1)

/-! ## 2. Free-coordinate tensor and outside-union recursions -/

/-- Free `dimension`-coordinate dimension-weighted heat mass. -/
def su2WeightedTensorMass
    (q : Q') (K : Nat) : Nat → Q'
  | 0 => 1
  | dimension + 1 =>
      su2WeightedLabelPartial q K *
        su2WeightedTensorMass q K dimension

/-- Union-bound mass for configurations with at least one coordinate above
the retained cutoff.  Multiple offending coordinates may be counted more
than once. -/
def su2WeightedTensorOutsideUnionMass
    (q : Q') (M K : Nat) : Nat → Q'
  | 0 => 0
  | dimension + 1 =>
      su2WeightedOuterShellMass q M K *
          su2WeightedTensorMass q K dimension +
        su2WeightedLabelPartial q K *
          su2WeightedTensorOutsideUnionMass
            q M K dimension

/-- Outer-cutoff-free SU(2) tensor-tail envelope. -/
def su2WeightedTensorTailEnvelope
    (q : Q') (M : Nat) : Nat → Q'
  | 0 => 0
  | dimension + 1 =>
      su2WeightedClosedTail q M *
          su2WeightedHeatCeiling q ^ dimension +
        su2WeightedHeatCeiling q *
          su2WeightedTensorTailEnvelope
            q M dimension

theorem su2WeightedTensorMass_nonnegative
    {q : Q'} (hq0 : (0 : Q') < q)
    (K : Nat) :
    ∀ dimension,
      (0 : Q') ≤
        su2WeightedTensorMass q K dimension
  | 0 => Q'.zero_le_one
  | dimension + 1 =>
      Q'.mul_nonneg _ _
        (su2WeightedLabelPartial_nonnegative hq0 K)
        (su2WeightedTensorMass_nonnegative
          hq0 K dimension)

theorem su2WeightedTensorOutsideUnionMass_nonnegative
    {q : Q'} (hq0 : (0 : Q') < q)
    (M K : Nat) :
    ∀ dimension,
      (0 : Q') ≤
        su2WeightedTensorOutsideUnionMass
          q M K dimension
  | 0 => Q'.le_refl' 0
  | dimension + 1 =>
      add_nonnegative
        (Q'.mul_nonneg _ _
          (su2WeightedOuterShellMass_nonnegative
            hq0 M K)
          (su2WeightedTensorMass_nonnegative
            hq0 K dimension))
        (Q'.mul_nonneg _ _
          (su2WeightedLabelPartial_nonnegative hq0 K)
          (su2WeightedTensorOutsideUnionMass_nonnegative
            hq0 M K dimension))

theorem su2WeightedTensorTailEnvelope_nonnegative
    {q : Q'} (hq0 : (0 : Q') < q)
    (M : Nat) :
    ∀ dimension,
      (0 : Q') ≤
        su2WeightedTensorTailEnvelope
          q M dimension
  | 0 => Q'.le_refl' 0
  | dimension + 1 =>
      add_nonnegative
        (Q'.mul_nonneg _ _
          (su2WeightedClosedTail_nonnegative hq0 M)
          (Q'.pow_nonneg _
            (su2WeightedHeatCeiling_nonnegative hq0)
            dimension))
        (Q'.mul_nonneg _ _
          (su2WeightedHeatCeiling_nonnegative hq0)
          (su2WeightedTensorTailEnvelope_nonnegative
            hq0 M dimension))

theorem su2WeightedTensorMass_le_ceilingPow
    {q : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q'))
    (K : Nat) :
    ∀ dimension,
      su2WeightedTensorMass q K dimension ≤
        su2WeightedHeatCeiling q ^ dimension
  | 0 => Q'.le_refl' 1
  | dimension + 1 => by
      have hpartial :=
        su2WeightedLabelPartial_le_heatCeiling
          hq0 hq1 K
      have htail :=
        su2WeightedTensorMass_le_ceilingPow
          hq0 hq1 K dimension
      have htail0 :=
        su2WeightedTensorMass_nonnegative
          hq0 K dimension
      have hceiling0 :=
        su2WeightedHeatCeiling_nonnegative hq0
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right
          _ _ _ hpartial htail0)
        (Q'.mul_le_mul_of_nonneg_left
          _ _ _ htail hceiling0)

/-- Main outer-cutoff-uniform SU(2) tensor estimate.  The right side depends
on `q`, `M`, and the fixed coordinate count, but not on `K`. -/
theorem su2WeightedTensorOutsideUnionMass_le_envelope
    {q : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q'))
    {M K : Nat}
    (hcut : explicitWeightedLabelCutoff q ≤ M + 1) :
    ∀ dimension,
      su2WeightedTensorOutsideUnionMass
          q M K dimension ≤
        su2WeightedTensorTailEnvelope
          q M dimension
  | 0 => Q'.le_refl' 0
  | dimension + 1 => by
      have houter :=
        su2WeightedOuterShellMass_le_closedTail
          hq0 hq1 (M := M) (K := K) hcut
      have htotal :=
        su2WeightedTensorMass_le_ceilingPow
          hq0 hq1 K dimension
      have hpartial :=
        su2WeightedLabelPartial_le_heatCeiling
          hq0 hq1 K
      have houtside :=
        su2WeightedTensorOutsideUnionMass_le_envelope
          hq0 hq1 (M := M) (K := K) hcut dimension
      have htotal0 :=
        su2WeightedTensorMass_nonnegative
          hq0 K dimension
      have htail0 :=
        su2WeightedClosedTail_nonnegative hq0 M
      have houtside0 :=
        su2WeightedTensorOutsideUnionMass_nonnegative
          hq0 M K dimension
      have hceiling0 :=
        su2WeightedHeatCeiling_nonnegative hq0
      have hleft1 :
          su2WeightedOuterShellMass q M K *
              su2WeightedTensorMass q K dimension ≤
            su2WeightedClosedTail q M *
              su2WeightedTensorMass q K dimension :=
        Q'.mul_le_mul_of_nonneg_right
          _ _ _ houter htotal0
      have hleft2 :
          su2WeightedClosedTail q M *
              su2WeightedTensorMass q K dimension ≤
            su2WeightedClosedTail q M *
              su2WeightedHeatCeiling q ^ dimension :=
        Q'.mul_le_mul_of_nonneg_left
          _ _ _ htotal htail0
      have hright1 :
          su2WeightedLabelPartial q K *
              su2WeightedTensorOutsideUnionMass
                q M K dimension ≤
            su2WeightedHeatCeiling q *
              su2WeightedTensorOutsideUnionMass
                q M K dimension :=
        Q'.mul_le_mul_of_nonneg_right
          _ _ _ hpartial houtside0
      have hright2 :
          su2WeightedHeatCeiling q *
              su2WeightedTensorOutsideUnionMass
                q M K dimension ≤
            su2WeightedHeatCeiling q *
              su2WeightedTensorTailEnvelope
                q M dimension :=
        Q'.mul_le_mul_of_nonneg_left
          _ _ _ houtside hceiling0
      exact Q'.add_le_add
        (Q'.le_trans' _ _ _ hleft1 hleft2)
        (Q'.le_trans' _ _ _ hright1 hright2)

/-! ## 3. Extracting the fixed-dimensional coefficient -/

/-- Fixed coefficient multiplying the one-coordinate closed tail. -/
def su2WeightedTensorTailCoefficient
    (q : Q') : Nat → Q'
  | 0 => 0
  | dimension + 1 =>
      su2WeightedHeatCeiling q ^ dimension +
        su2WeightedHeatCeiling q *
          su2WeightedTensorTailCoefficient q dimension

theorem su2WeightedTensorTailCoefficient_nonnegative
    {q : Q'} (hq0 : (0 : Q') < q) :
    ∀ dimension,
      (0 : Q') ≤
        su2WeightedTensorTailCoefficient q dimension
  | 0 => Q'.le_refl' 0
  | dimension + 1 =>
      add_nonnegative
        (Q'.pow_nonneg _
          (su2WeightedHeatCeiling_nonnegative hq0)
          dimension)
        (Q'.mul_nonneg _ _
          (su2WeightedHeatCeiling_nonnegative hq0)
          (su2WeightedTensorTailCoefficient_nonnegative
            hq0 dimension))

/-- The recursive envelope is exactly the one-coordinate closed tail times a
fixed coefficient.  This is the form needed by an explicit tolerance
rescaling in the eventual SU(2) score-tube modulus. -/
theorem su2WeightedTensorTailEnvelope_eqv_coefficient
    (q : Q') (M : Nat) :
    ∀ dimension,
      su2WeightedTensorTailEnvelope q M dimension ≈
        su2WeightedClosedTail q M *
          su2WeightedTensorTailCoefficient q dimension
  | 0 =>
      Q'.eqv_symm
        (Q'.mul_zero_eqv
          (su2WeightedClosedTail q M))
  | dimension + 1 => by
      have ih :=
        su2WeightedTensorTailEnvelope_eqv_coefficient
          q M dimension
      change
        su2WeightedClosedTail q M *
              su2WeightedHeatCeiling q ^ dimension +
            su2WeightedHeatCeiling q *
              su2WeightedTensorTailEnvelope q M dimension ≈
          su2WeightedClosedTail q M *
            (su2WeightedHeatCeiling q ^ dimension +
              su2WeightedHeatCeiling q *
                su2WeightedTensorTailCoefficient q dimension)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          (su2WeightedClosedTail q M *
            su2WeightedHeatCeiling q ^ dimension)
          _ _
          (Q'.mul_eqv_congr_left
            (su2WeightedHeatCeiling q) _ _ ih)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          (su2WeightedClosedTail q M *
            su2WeightedHeatCeiling q ^ dimension)
          _ _
          (Q'.eqv_trans _ _ _
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv
                (su2WeightedHeatCeiling q)
                (su2WeightedClosedTail q M)
                (su2WeightedTensorTailCoefficient q dimension)))
            (Q'.mul_eqv_congr_right
              (su2WeightedHeatCeiling q *
                su2WeightedClosedTail q M)
              (su2WeightedClosedTail q M *
                su2WeightedHeatCeiling q)
              (su2WeightedTensorTailCoefficient q dimension)
              (Q'.mul_comm_eqv
                (su2WeightedHeatCeiling q)
                (su2WeightedClosedTail q M))))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          (su2WeightedClosedTail q M *
            su2WeightedHeatCeiling q ^ dimension)
          _ _
          (Q'.mul_assoc_eqv
            (su2WeightedClosedTail q M)
            (su2WeightedHeatCeiling q)
            (su2WeightedTensorTailCoefficient q dimension))) ?_
      exact Q'.eqv_symm
        (Q'.mul_add_eqv
          (su2WeightedClosedTail q M)
          (su2WeightedHeatCeiling q ^ dimension)
          (su2WeightedHeatCeiling q *
            su2WeightedTensorTailCoefficient q dimension))

#print axioms su2WeightedOuterShellMass_le_closedTail
#print axioms su2WeightedLabelPartial_le_heatCeiling
#print axioms su2WeightedTensorMass_le_ceilingPow
#print axioms su2WeightedTensorOutsideUnionMass_le_envelope
#print axioms su2WeightedTensorTailEnvelope_eqv_coefficient

end YMGap.Continuum.SU2OuterCutoffUniformTensorTail
