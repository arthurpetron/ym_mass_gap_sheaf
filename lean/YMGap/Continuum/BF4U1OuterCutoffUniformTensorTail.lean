/-
# Outer-cutoff-uniform U(1) tensor tails

This module removes the cardinality of the outer Cartesian carrier from the
U(1) heat-tail estimate.  At a fixed rational heat coupling `0 < w < 1`, the
one-coordinate mass above charge `M` and below any outer charge cutoff
`K >= M` is bounded by `signedChargeClosedTail w M`, independently of `K`.

The bound is then tensorized with a constructive union recursion.  For a
finite face list only its fixed length enters; the outer label count does
not.  The exported envelope is deliberately recursive:

    E 0       = 0
    E (d + 1) = tail * ceiling^d + ceiling * E d.

This is the exact recurrence obtained by selecting an offending coordinate
and freely summing the remaining coordinates.  Identifying the recursive
tensor mass with the repository's function-valued
`boundedEdgeLabellings` sum, and then inserting the U(1) Haar constraints,
is left to a subsequent finite-Fubini module.
-/

import YMGap.Continuum.U1SignedChargeHeatTail

namespace YMGap.Continuum.BF4U1OuterCutoffUniformTensorTail

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.AbelianFusionCLT
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.U1SignedChargeHeatTail

local infix:50 " ≈ " => Q'.eqv

private theorem add_nonnegative {a b : Q'}
    (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) :
    (0 : Q') ≤ a + b := by
  have h := Q'.add_le_add ha hb
  rw [Q'.zero_add'] at h
  exact h

private theorem finSum_split_local (f : Nat → Q') (N : Nat) :
    ∀ L : Nat,
      finSum f (N + L) ≈
        finSum f N +
          finSum (fun offset => f (N + offset)) L
  | 0 => by
      rw [Nat.add_zero, finSum_zero, Q'.add_zero']
      exact Q'.eqv_refl _
  | L + 1 => by
      have ih := finSum_split_local f N L
      show
        finSum f (N + L) + f (N + L) ≈
          finSum f N +
            (finSum (fun offset => f (N + offset)) L +
              f (N + L))
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ ih)
        (Q'.add_assoc_eqv _ _ _)

private theorem finSum_nonnegative_local
    (f : Nat → Q')
    (hf : ∀ index, (0 : Q') ≤ f index) :
    ∀ length, (0 : Q') ≤ finSum f length
  | 0 => Q'.le_refl' 0
  | length + 1 =>
      add_nonnegative
        (finSum_nonnegative_local f hf length)
        (hf length)

/-! ## 1. A one-coordinate outer shell independent of the outer cutoff -/

/-- Signed-label mass with charge magnitude strictly above `M` and at most
the outer symmetric charge cutoff `K`.  When `M <= K`, these are exactly the
labels from `2*M+1` through `2*K`. -/
def signedChargeOuterShellMass
    (w : Q') (M K : Nat) : Q' :=
  finSum
    (fun offset =>
      signedChargeHeatWeight w (2 * M + 1 + offset))
    (2 * (K - M))

theorem signedChargeOuterShellMass_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (M K : Nat) :
    (0 : Q') ≤ signedChargeOuterShellMass w M K := by
  unfold signedChargeOuterShellMass
  exact finSum_nonnegative_local _
    (fun offset => by
      unfold signedChargeHeatWeight
      exact abelCoeff_nonneg
        (Q'.le_of_lt hw0) _)
    _

theorem symmetricLabelPartial_split_outer
    (w : Q') {M K : Nat} (hMK : M ≤ K) :
    symmetricLabelPartial w K ≈
      symmetricLabelPartial w M +
        signedChargeOuterShellMass w M K := by
  have hstage : M + (K - M) = K :=
    Nat.add_sub_of_le hMK
  have hlength :
      2 * K + 1 =
        (2 * M + 1) + 2 * (K - M) := by
    omega
  unfold symmetricLabelPartial
  rw [hlength]
  exact finSum_split_local
    (signedChargeHeatWeight w)
    (2 * M + 1) (2 * (K - M))

private theorem outer_eqv_partial_sub
    (w : Q') {M K : Nat} (hMK : M ≤ K) :
    signedChargeOuterShellMass w M K ≈
      symmetricLabelPartial w K +
        -symmetricLabelPartial w M := by
  let headMass := symmetricLabelPartial w M
  let fullMass := symmetricLabelPartial w K
  let outerMass := signedChargeOuterShellMass w M K
  have hsplit : fullMass ≈ headMass + outerMass :=
    symmetricLabelPartial_split_outer w hMK
  refine Q'.eqv_trans outerMass ((0 : Q') + outerMass) _
    (Q'.eqv_symm
      (Q'.eqv_of_eq
        (Q'.zero_add' outerMass))) ?_
  refine Q'.eqv_trans _ ((-headMass + headMass) + outerMass) _
    (Q'.add_eqv_congr_right
      0 (-headMass + headMass) outerMass
      (Q'.eqv_symm
        (Q'.neg_add_self_eqv headMass))) ?_
  refine Q'.eqv_trans _ (-headMass + (headMass + outerMass)) _
    (Q'.add_assoc_eqv (-headMass) headMass outerMass) ?_
  refine Q'.eqv_trans _ (-headMass + fullMass) _
    (Q'.add_eqv_congr_left
      (-headMass) (headMass + outerMass) fullMass
      (Q'.eqv_symm hsplit)) ?_
  exact Q'.add_comm_eqv (-headMass) fullMass

/-- The mass outside charge `M` is controlled uniformly in every later
outer cutoff `K`. -/
theorem signedChargeOuterShellMass_le_closedTail
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    {M K : Nat} (hMK : M ≤ K) :
    signedChargeOuterShellMass w M K ≤
      signedChargeClosedTail w M := by
  have hstage : M + (K - M) = K :=
    Nat.add_sub_of_le hMK
  have hupper :=
    symmetricLabelPartial_block_upper
      hw0 hw1 M (K - M)
  rw [hstage] at hupper
  have hsub :
      symmetricLabelPartial w K +
          -symmetricLabelPartial w M ≤
        signedChargeClosedTail w M :=
    Q'.sub_le_of_le_add hupper
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (outer_eqv_partial_sub w hMK))
    hsub

/-! ## 2. A uniform one-coordinate ceiling -/

/-- Fixed one-coordinate heat-mass ceiling, independent of the outer charge
cutoff. -/
def signedChargeHeatCeiling (w : Q') : Q' :=
  symmetricLabelPartial w 0 +
    signedChargeClosedTail w 0

theorem signedChargeHeatCeiling_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') ≤ signedChargeHeatCeiling w := by
  unfold signedChargeHeatCeiling
  exact add_nonnegative
    (by
      unfold symmetricLabelPartial
      exact finSum_nonnegative_local
        _
        (fun label =>
          abelCoeff_nonneg
            (Q'.le_of_lt hw0) _)
        1)
    (signedChargeClosedTail_nonnegative hw0 0)

theorem symmetricLabelPartial_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (K : Nat) :
    (0 : Q') ≤ symmetricLabelPartial w K := by
  unfold symmetricLabelPartial signedChargeHeatWeight
  exact finSum_nonnegative_local
    _
    (fun label =>
      abelCoeff_nonneg
        (Q'.le_of_lt hw0) _)
    (2 * K + 1)

theorem symmetricLabelPartial_le_heatCeiling
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (K : Nat) :
    symmetricLabelPartial w K ≤
      signedChargeHeatCeiling w := by
  simpa only [Nat.zero_add, signedChargeHeatCeiling] using
    (symmetricLabelPartial_block_upper
      hw0 hw1 0 K)

/-! ## 3. Recursive free-coordinate tensor and union masses -/

/-- The free `dimension`-coordinate heat mass at outer charge cutoff `K`. -/
def signedChargeTensorMass
    (w : Q') (K : Nat) : Nat → Q'
  | 0 => 1
  | dimension + 1 =>
      symmetricLabelPartial w K *
        signedChargeTensorMass w K dimension

/-- Union-bound mass: choose an offending coordinate, and freely sum the
remaining coordinates.  The recursion may count configurations with several
offending coordinates more than once, as a union bound should. -/
def signedChargeTensorOutsideUnionMass
    (w : Q') (M K : Nat) : Nat → Q'
  | 0 => 0
  | dimension + 1 =>
      signedChargeOuterShellMass w M K *
          signedChargeTensorMass w K dimension +
        symmetricLabelPartial w K *
          signedChargeTensorOutsideUnionMass
            w M K dimension

/-- Outer-cutoff-free recursive envelope. -/
def signedChargeTensorTailEnvelope
    (w : Q') (M : Nat) : Nat → Q'
  | 0 => 0
  | dimension + 1 =>
      signedChargeClosedTail w M *
          signedChargeHeatCeiling w ^ dimension +
        signedChargeHeatCeiling w *
          signedChargeTensorTailEnvelope
            w M dimension

theorem signedChargeTensorMass_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (K : Nat) :
    ∀ dimension,
      (0 : Q') ≤
        signedChargeTensorMass w K dimension
  | 0 => Q'.zero_le_one
  | dimension + 1 =>
      Q'.mul_nonneg _ _
        (symmetricLabelPartial_nonnegative hw0 K)
        (signedChargeTensorMass_nonnegative
          hw0 K dimension)

theorem signedChargeTensorOutsideUnionMass_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (M K : Nat) :
    ∀ dimension,
      (0 : Q') ≤
        signedChargeTensorOutsideUnionMass
          w M K dimension
  | 0 => Q'.le_refl' 0
  | dimension + 1 =>
      add_nonnegative
        (Q'.mul_nonneg _ _
          (signedChargeOuterShellMass_nonnegative
            hw0 M K)
          (signedChargeTensorMass_nonnegative
            hw0 K dimension))
        (Q'.mul_nonneg _ _
          (symmetricLabelPartial_nonnegative hw0 K)
          (signedChargeTensorOutsideUnionMass_nonnegative
            hw0 M K dimension))

theorem signedChargeTensorTailEnvelope_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (M : Nat) :
    ∀ dimension,
      (0 : Q') ≤
        signedChargeTensorTailEnvelope
          w M dimension
  | 0 => Q'.le_refl' 0
  | dimension + 1 =>
      add_nonnegative
        (Q'.mul_nonneg _ _
          (signedChargeClosedTail_nonnegative
            hw0 M)
          (Q'.pow_nonneg _
            (signedChargeHeatCeiling_nonnegative
              hw0) dimension))
        (Q'.mul_nonneg _ _
          (signedChargeHeatCeiling_nonnegative hw0)
          (signedChargeTensorTailEnvelope_nonnegative
            hw0 M dimension))

theorem signedChargeTensorMass_le_ceilingPow
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (K : Nat) :
    ∀ dimension,
      signedChargeTensorMass w K dimension ≤
        signedChargeHeatCeiling w ^ dimension
  | 0 => Q'.le_refl' 1
  | dimension + 1 => by
      have hpartial :=
        symmetricLabelPartial_le_heatCeiling
          hw0 hw1 K
      have htail :=
        signedChargeTensorMass_le_ceilingPow
          hw0 hw1 K dimension
      have htail0 :=
        signedChargeTensorMass_nonnegative
          hw0 K dimension
      have hceiling0 :=
        signedChargeHeatCeiling_nonnegative hw0
      have hfirst :
          symmetricLabelPartial w K *
              signedChargeTensorMass w K dimension ≤
            signedChargeHeatCeiling w *
              signedChargeTensorMass w K dimension :=
        Q'.mul_le_mul_of_nonneg_right
          _ _ _ hpartial htail0
      have hsecond :
          signedChargeHeatCeiling w *
              signedChargeTensorMass w K dimension ≤
            signedChargeHeatCeiling w *
              signedChargeHeatCeiling w ^ dimension :=
        Q'.mul_le_mul_of_nonneg_left
          _ _ _ htail hceiling0
      exact Q'.le_trans' _ _ _ hfirst hsecond

/-- Main outer-cutoff-uniform tensor/union estimate.  The right side depends
on the retained charge `M`, the fixed coupling, and the coordinate count,
but not on the outer cutoff `K`. -/
theorem signedChargeTensorOutsideUnionMass_le_envelope
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    {M K : Nat} (hMK : M ≤ K) :
    ∀ dimension,
      signedChargeTensorOutsideUnionMass
          w M K dimension ≤
        signedChargeTensorTailEnvelope
          w M dimension
  | 0 => Q'.le_refl' 0
  | dimension + 1 => by
      have houter :=
        signedChargeOuterShellMass_le_closedTail
          hw0 hw1 hMK
      have htotal :=
        signedChargeTensorMass_le_ceilingPow
          hw0 hw1 K dimension
      have hpartial :=
        symmetricLabelPartial_le_heatCeiling
          hw0 hw1 K
      have houtside :=
        signedChargeTensorOutsideUnionMass_le_envelope
          hw0 hw1 hMK dimension
      have htotal0 :=
        signedChargeTensorMass_nonnegative
          hw0 K dimension
      have htail0 :=
        signedChargeClosedTail_nonnegative hw0 M
      have houtside0 :=
        signedChargeTensorOutsideUnionMass_nonnegative
          hw0 M K dimension
      have hceiling0 :=
        signedChargeHeatCeiling_nonnegative hw0
      have hleft1 :
          signedChargeOuterShellMass w M K *
              signedChargeTensorMass w K dimension ≤
            signedChargeClosedTail w M *
              signedChargeTensorMass w K dimension :=
        Q'.mul_le_mul_of_nonneg_right
          _ _ _ houter htotal0
      have hleft2 :
          signedChargeClosedTail w M *
              signedChargeTensorMass w K dimension ≤
            signedChargeClosedTail w M *
              signedChargeHeatCeiling w ^ dimension :=
        Q'.mul_le_mul_of_nonneg_left
          _ _ _ htotal htail0
      have hright1 :
          symmetricLabelPartial w K *
              signedChargeTensorOutsideUnionMass
                w M K dimension ≤
            signedChargeHeatCeiling w *
              signedChargeTensorOutsideUnionMass
                w M K dimension :=
        Q'.mul_le_mul_of_nonneg_right
          _ _ _ hpartial houtside0
      have hright2 :
          signedChargeHeatCeiling w *
              signedChargeTensorOutsideUnionMass
                w M K dimension ≤
            signedChargeHeatCeiling w *
              signedChargeTensorTailEnvelope
                w M dimension :=
        Q'.mul_le_mul_of_nonneg_left
          _ _ _ houtside hceiling0
      exact Q'.add_le_add
        (Q'.le_trans' _ _ _ hleft1 hleft2)
        (Q'.le_trans' _ _ _ hright1 hright2)

/-- Finite-face-list form of the uniform estimate.  This is the scalar tensor
bound to be consumed by the later `boundedEdgeLabellings` Fubini bridge. -/
theorem finiteFaceListOuterUniformTensorBound
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (faces : List Nat)
    {M K : Nat} (hMK : M ≤ K) :
    signedChargeTensorOutsideUnionMass
        w M K faces.length ≤
      signedChargeTensorTailEnvelope
        w M faces.length :=
  signedChargeTensorOutsideUnionMass_le_envelope
    hw0 hw1 hMK faces.length

#print axioms symmetricLabelPartial_split_outer
#print axioms signedChargeOuterShellMass_le_closedTail
#print axioms symmetricLabelPartial_le_heatCeiling
#print axioms signedChargeTensorMass_le_ceilingPow
#print axioms signedChargeTensorOutsideUnionMass_le_envelope
#print axioms finiteFaceListOuterUniformTensorBound

end YMGap.Continuum.BF4U1OuterCutoffUniformTensorTail
