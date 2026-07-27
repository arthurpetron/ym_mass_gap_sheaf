/-
# Quantitative tails for the spacing-dependent SU(2) pointwise heat completion

`SU2PointwiseHeatSpacingCompletion` constructs the arbitrary-nome pointwise
heat series as a constructive real after the explicit label cutoff
`spacingLabelCutoff w`.  This module records the quantitative estimate carried
by that construction.

For every retained prefix index `M` and every finite block length `L`,

    |S(M+L) - S(M)|
      ≤ spacingTailHead(w) * spacingTailRatio(w)^M
          / (1 - spacingTailRatio(w)).

The project represents rational absolute-value estimates most robustly as the
two ordered inequalities

    S(M+L) - S(M) ≤ tail(M),
    S(M) - S(M+L) ≤ tail(M).

The same estimate is then lifted, without regularity assumptions, to the
semantic `CReal.leRat` / `ExpPos.geRat` corridor around every shifted prefix.

## Honest scope

This is a pointwise, fixed-rational-nome tail theorem.  The label cutoff is
spacing dependent.  No spacing-uniform continuum estimate, interacting BF4
identification, or Haar-integrated statement is asserted here.

## Constructivity

All bounds use the explicit geometric tail from
`HeatKernelConvGen`.  There is no `Classical.*`, `Real`, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
import YMGap.Constructive.CRealMul
import YMGap.Constructive.ExpPos

namespace YMGap.Continuum.SU2PointwiseHeatSpacingTailBound

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion

/-! ## 1. The explicit closed tail -/

/-- The closed geometric tail after `M` labels beyond the
spacing-dependent cutoff. -/
def spacingClosedTail (w : Q') (M : Nat) : Q' :=
  geoTailBase
    (spacingTailHead w)
    (spacingTailRatio w)
    M

/-- The closed tail is literally the advertised
`head * ratio^M / (1-ratio)` expression in the project's rational language. -/
theorem spacingClosedTail_formula (w : Q') (M : Nat) :
    spacingClosedTail w M =
      (spacingTailHead w * spacingTailRatio w ^ M) *
        HKConv.divPos 1 (1 + (-spacingTailRatio w)) := rfl

/-- Every closed tail is nonnegative. -/
theorem spacingClosedTail_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (M : Nat) :
    (0 : Q') ≤ spacingClosedTail w M := by
  exact geoTailBase_nonneg
    (spacingTailHead_nonnegative hw0)
    (Q'.le_of_lt (spacingTailRatio_pos hw0))
    M

/-! ## 2. Finite all-label block estimate -/

/-- Upper estimate for every finite block beyond shifted prefix `M`. -/
theorem spacingPointwiseHeatPartial_block_upper
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M L : Nat) :
    spacingPointwiseHeatPartial w x (M + L) ≤
      spacingPointwiseHeatPartial w x M +
        spacingClosedTail w M := by
  have htel :
      spacingPointwiseHeatPartial w x (M + L) ≤
        spacingPointwiseHeatPartial w x M +
          finSum
            (fun i =>
              geoIncrBase
                (spacingTailHead w)
                (spacingTailRatio w)
                (M + i))
            L :=
    telescope_up
      (spacingPointwiseHeatPartial w x)
      (geoIncrBase
        (spacingTailHead w)
        (spacingTailRatio w))
      (spacingPointwiseHeatPartial_hup
        hw0 hw1 hxLower hxUpper)
      M L
  have hsum :
      finSum
          (fun i =>
            geoIncrBase
              (spacingTailHead w)
              (spacingTailRatio w)
              (M + i))
          L ≤
        spacingClosedTail w M := by
    exact geoTailBase_series_le
      (spacingTailHead_nonnegative hw0)
      (spacingTailRatio_pos hw0)
      (spacingTailRatio_lt_one hw0 hw1)
      M L
  exact Q'.le_trans' _ _ _ htel
    (Q'.add_le_add_left
      (spacingPointwiseHeatPartial w x M)
      _ _ hsum)

/-- Lower estimate for every finite block beyond shifted prefix `M`. -/
theorem spacingPointwiseHeatPartial_block_lower
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M L : Nat) :
    spacingPointwiseHeatPartial w x M ≤
      spacingPointwiseHeatPartial w x (M + L) +
        spacingClosedTail w M := by
  have htel :
      spacingPointwiseHeatPartial w x M ≤
        spacingPointwiseHeatPartial w x (M + L) +
          finSum
            (fun i =>
              geoIncrBase
                (spacingTailHead w)
                (spacingTailRatio w)
                (M + i))
            L :=
    telescope_lo
      (spacingPointwiseHeatPartial w x)
      (geoIncrBase
        (spacingTailHead w)
        (spacingTailRatio w))
      (spacingPointwiseHeatPartial_hlo
        hw0 hw1 hxLower hxUpper)
      M L
  have hsum :
      finSum
          (fun i =>
            geoIncrBase
              (spacingTailHead w)
              (spacingTailRatio w)
              (M + i))
          L ≤
        spacingClosedTail w M := by
    exact geoTailBase_series_le
      (spacingTailHead_nonnegative hw0)
      (spacingTailRatio_pos hw0)
      (spacingTailRatio_lt_one hw0 hw1)
      M L
  exact Q'.le_trans' _ _ _ htel
    (Q'.add_le_add_left
      (spacingPointwiseHeatPartial w x (M + L))
      _ _ hsum)

/-- The finite estimate in the project's subtraction/order language:
both signed differences are bounded by the same explicit tail. -/
theorem spacingPointwiseHeatPartial_block_twoSided
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M L : Nat) :
    spacingPointwiseHeatPartial w x (M + L) +
          -spacingPointwiseHeatPartial w x M ≤
        spacingClosedTail w M ∧
      spacingPointwiseHeatPartial w x M +
          -spacingPointwiseHeatPartial w x (M + L) ≤
        spacingClosedTail w M := by
  exact
    ⟨Q'.sub_le_of_le_add
        (spacingPointwiseHeatPartial_block_upper
          hw0 hw1 hxLower hxUpper M L),
      Q'.sub_le_of_le_add
        (spacingPointwiseHeatPartial_block_lower
          hw0 hw1 hxLower hxUpper M L)⟩

/-- Type-level packaging of the quantitative finite-block corridor. -/
structure FiniteSpacingTailCorridor
    (w x : Q') (M L : Nat) : Type where
  forward :
    spacingPointwiseHeatPartial w x (M + L) +
          -spacingPointwiseHeatPartial w x M ≤
        spacingClosedTail w M
  backward :
    spacingPointwiseHeatPartial w x M +
          -spacingPointwiseHeatPartial w x (M + L) ≤
        spacingClosedTail w M

/-- Construct the finite-block corridor from the explicit all-label
geometric domination. -/
def finiteSpacingTailCorridor
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M L : Nat) :
    FiniteSpacingTailCorridor w x M L :=
  let h :=
    spacingPointwiseHeatPartial_block_twoSided
      hw0 hw1 hxLower hxUpper M L
  ⟨h.1, h.2⟩

/-! ## 3. Semantic constructive-real corridor -/

/-- The completed pointwise heat value lies below every shifted prefix plus
its explicit closed tail.  `leRat` is the regularity-free semantic order. -/
theorem pointwiseHeatCReal_le_prefix_add_tail
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M : Nat) :
    CReal.leRat
      (pointwiseHeatCReal
        hw0 hw1 hxLower hxUpper)
      (spacingPointwiseHeatPartial w x M +
        spacingClosedTail w M) := by
  apply CReal.leRat_of_eventually
  refine ⟨M, fun p hp => ?_⟩
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [pointwiseHeatCReal_approx]
  exact spacingPointwiseHeatPartial_block_upper
    hw0 hw1 hxLower hxUpper M L

/-- Every shifted prefix minus its closed tail lies below the completed
pointwise heat value.  `geRat` is the semantic lower-order predicate dual to
`CReal.leRat`. -/
theorem prefix_sub_tail_le_pointwiseHeatCReal
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M : Nat) :
    ExpPos.geRat
      (pointwiseHeatCReal
        hw0 hw1 hxLower hxUpper)
      (spacingPointwiseHeatPartial w x M +
        -spacingClosedTail w M) := by
  apply ExpPos.geRat_of_eventually
  refine ⟨M, fun p hp => ?_⟩
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [pointwiseHeatCReal_approx]
  have hlower :=
    spacingPointwiseHeatPartial_block_lower
      hw0 hw1 hxLower hxUpper M L
  have hcomm :
      spacingPointwiseHeatPartial w x M ≤
        spacingClosedTail w M +
          spacingPointwiseHeatPartial w x (M + L) :=
    Q'.le_trans' _ _ _ hlower
      (Q'.le_of_eqv
        (Q'.add_comm_eqv
          (spacingPointwiseHeatPartial w x (M + L))
          (spacingClosedTail w M)))
  exact Q'.sub_le_of_le_add hcomm

/-- Type-level semantic corridor around the `M`-th shifted prefix. -/
structure SemanticSpacingTailCorridor
    (value : CReal) (w x : Q') (M : Nat) : Type where
  lower :
    ExpPos.geRat value
      (spacingPointwiseHeatPartial w x M +
        -spacingClosedTail w M)
  upper :
    CReal.leRat value
      (spacingPointwiseHeatPartial w x M +
        spacingClosedTail w M)

/-- Every shifted prefix supplies an explicit semantic corridor for the same
completed pointwise heat value. -/
def semanticSpacingTailCorridor
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M : Nat) :
    SemanticSpacingTailCorridor
      (pointwiseHeatCReal
        hw0 hw1 hxLower hxUpper)
      w x M where
  lower :=
    prefix_sub_tail_le_pointwiseHeatCReal
      hw0 hw1 hxLower hxUpper M
  upper :=
    pointwiseHeatCReal_le_prefix_add_tail
      hw0 hw1 hxLower hxUpper M

/-! ## Axiom gates -/

#print axioms spacingClosedTail_nonnegative
#print axioms spacingPointwiseHeatPartial_block_upper
#print axioms spacingPointwiseHeatPartial_block_lower
#print axioms spacingPointwiseHeatPartial_block_twoSided
#print axioms finiteSpacingTailCorridor
#print axioms pointwiseHeatCReal_le_prefix_add_tail
#print axioms prefix_sub_tail_le_pointwiseHeatCReal
#print axioms semanticSpacingTailCorridor

end YMGap.Continuum.SU2PointwiseHeatSpacingTailBound
