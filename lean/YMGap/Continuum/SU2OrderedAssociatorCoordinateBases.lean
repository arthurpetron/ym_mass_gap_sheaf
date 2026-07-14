/-
# The constructive ordered all-label SU(2) associator

The cyclic right chart is converted to the fixed ordered right-associated
chart by the derived transvectant swap phase.  Multiplying the synthesis
data by the same involutive phase gives an actual coordinate basis, so the
ordered associator has constructive inverse round trips rather than only a
formal sign comparison.
-/

import YMGap.Continuum.SU2OrderedRightNormalizationBridge
import YMGap.Continuum.SU2GeneralHahnLeftCombFourCoordinateBases

namespace YMGap.Continuum.SU2OrderedAssociatorCoordinateBases

open YMGap.Constructive
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantSwapParity
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.SU2GeneralHahnAssociatorCoordinateBases
open YMGap.Continuum.SU2GeneralHahnLeftCombFourCoordinateBases
open YMGap.Continuum.SU2OrderedRightNormalizationBridge
open YMGap.Continuum.PentagonFromCoordinateBases

local infix:50 " ≈ " => Q'.eqv

/-- Rephase cyclic right-chart data into the fixed ordered convention. -/
def orderedRightPhaseData {m n p : Nat}
    (c : LeftNestedCGChannel n p m → Q') :
    LeftNestedCGChannel n p m → Q' :=
  fun q => swapPhase q.outer.k * c q

/-- Synthesis dual to the fixed ordered right-associated coordinates. -/
def orderedRightNestedReconstruct (m n p : Nat)
    (c : LeftNestedCGChannel n p m → Q') : TriForm :=
  rightNestedReconstruct m n p (orderedRightPhaseData c)

/-- Fixed ordered right coordinates respect the original physical box. -/
theorem orderedRightNestedCoordinates_congr (m n p : Nat)
    (x z : TriForm) (hxz : PhysicalBoxEqv m n p x z)
    (q : LeftNestedCGChannel n p m) :
    orderedRightNestedCoordinates m n p x q ≈
      orderedRightNestedCoordinates m n p z q := by
  have hleft := orderedRight_eq_phase_cyclic m n p x q
  have hmiddle := Q'.mul_eqv_congr_left (swapPhase q.outer.k) _ _
    (rightNestedCoordinates_congr m n p x z hxz q)
  have hright := orderedRight_eq_phase_cyclic m n p z q
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ hmiddle (Q'.eqv_symm hright))

private theorem phase_collapse (k : Nat) (x : Q') :
    swapPhase k * (swapPhase k * x) ≈ x := by
  exact Q'.eqv_trans _ ((swapPhase k * swapPhase k) * x) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ (1 * x) _
      (Q'.mul_eqv_congr_right _ _ _ (swapPhase_mul_self k))
      (Q'.one_mul_eqv x))

/-- Ordered-right synthesis followed by ordered-right analysis is the
identity on every dependent channel. -/
theorem orderedRightNestedCoordinates_reconstruct (m n p : Nat)
    (c : LeftNestedCGChannel n p m → Q')
    (q : LeftNestedCGChannel n p m) :
    orderedRightNestedCoordinates m n p
        (orderedRightNestedReconstruct m n p c) q ≈ c q := by
  have hbridge := orderedRight_eq_phase_cyclic m n p
    (orderedRightNestedReconstruct m n p c) q
  have hright := rightNestedCoordinates_reconstruct m n p
    (orderedRightPhaseData c) q
  have hmiddle := Q'.mul_eqv_congr_left (swapPhase q.outer.k) _ _ hright
  exact Q'.eqv_trans _ _ _ hbridge
    (Q'.eqv_trans _ _ _ hmiddle (phase_collapse q.outer.k (c q)))

/-- Ordered-right analysis followed by ordered-right synthesis recovers the
original physical coefficient box. -/
theorem orderedRightNestedReconstruct_coordinates (m n p : Nat)
    (x : TriForm) (i j l : Nat) (hi : i ≤ m) (hj : j ≤ n)
    (hl : l ≤ p) :
    orderedRightNestedReconstruct m n p
        (orderedRightNestedCoordinates m n p x) i j l ≈ x i j l := by
  let orderedData : LeftNestedCGChannel n p m → Q' :=
    orderedRightPhaseData (orderedRightNestedCoordinates m n p x)
  let cyclicData : LeftNestedCGChannel n p m → Q' :=
    rightNestedCoordinates m n p x
  have hdata : ∀ q, orderedData q ≈ cyclicData q := by
    intro q
    exact Q'.eqv_symm (cyclic_eq_phase_orderedRight m n p x q)
  have hcongr := leftNestedReconstruct_congr n p m
    orderedData cyclicData hdata j l i hj hl hi
  have hright := rightNestedReconstruct_coordinates m n p x
    i j l hi hj hl
  exact Q'.eqv_trans _ _ _
    (by simpa only [orderedRightNestedReconstruct, rightNestedReconstruct,
      orderedRightPhaseData, orderedData, cyclicData, unrotateTri] using hcongr)
    hright

/-- The left tree and the fixed ordered right tree as coordinate bases of
the same physical three-form box. -/
def orderedAssociatorCoordinateBases (m n p : Nat) :
    CoordinateBases AssocTree TriForm where
  Index := fun
    | .left => LeftNestedCGChannel m n p
    | .right => LeftNestedCGChannel n p m
  Rel := PhysicalBoxEqv m n p
  rel_refl := fun x i j l hi hj hl => Q'.eqv_refl _
  rel_symm := fun h i j l hi hj hl => Q'.eqv_symm (h i j l hi hj hl)
  rel_trans := fun h₁ h₂ i j l hi hj hl =>
    Q'.eqv_trans _ _ _ (h₁ i j l hi hj hl) (h₂ i j l hi hj hl)
  synth := fun
    | .left, c => leftNestedReconstruct m n p c
    | .right, c => orderedRightNestedReconstruct m n p c
  coords := fun
    | .left, x => leftNestedCoordinates m n p x
    | .right, x => orderedRightNestedCoordinates m n p x
  coords_congr := by
    intro T x z hxz q
    cases T with
    | left => exact leftNestedCoordinates_congr m n p x z hxz q
    | right => exact orderedRightNestedCoordinates_congr m n p x z hxz q
  synth_coords := by
    intro T x
    cases T with
    | left =>
        intro i j l hi hj hl
        exact leftNestedReconstruct_coordinates m n p x i j l hi hj hl
    | right =>
        intro i j l hi hj hl
        exact orderedRightNestedReconstruct_coordinates m n p x
          i j l hi hj hl
  coords_synth := by
    intro T c q
    cases T with
    | left => exact leftNestedCoordinates_reconstruct m n p c q
    | right => exact orderedRightNestedCoordinates_reconstruct m n p c q

/-- The fixed ordered all-label associator. -/
def orderedAllLabelAssociator (m n p : Nat)
    (c : LeftNestedCGChannel m n p → Q') :
    LeftNestedCGChannel n p m → Q' :=
  basisChange (orderedAssociatorCoordinateBases m n p) .left .right c

/-- The reverse fixed ordered all-label associator. -/
def orderedAllLabelAssociatorInv (m n p : Nat)
    (c : LeftNestedCGChannel n p m → Q') :
    LeftNestedCGChannel m n p → Q' :=
  basisChange (orderedAssociatorCoordinateBases m n p) .right .left c

/-- The ordered associator is the cyclic associator with the exact derived
outer-vertex phase on every output channel. -/
theorem orderedAllLabelAssociator_eq_phase_cyclic (m n p : Nat)
    (c : LeftNestedCGChannel m n p → Q')
    (q : LeftNestedCGChannel n p m) :
    orderedAllLabelAssociator m n p c q ≈
      swapPhase q.outer.k * allLabelAssociator m n p c q := by
  exact orderedRight_eq_phase_cyclic m n p
    (leftNestedReconstruct m n p c) q

/-- Ordered right-to-left recoupling is cyclic right-to-left recoupling after
the exact input-channel rephasing. -/
theorem orderedAllLabelAssociatorInv_eq_cyclic (m n p : Nat)
    (c : LeftNestedCGChannel n p m → Q')
    (q : LeftNestedCGChannel m n p) :
    orderedAllLabelAssociatorInv m n p c q ≈
      allLabelAssociatorInv m n p (orderedRightPhaseData c) q := by
  exact Q'.eqv_refl _

/-- Right then left ordered recoupling returns all left-tree coordinates. -/
theorem orderedAllLabelAssociator_left_roundtrip (m n p : Nat)
    (c : LeftNestedCGChannel m n p → Q') :
    ∀ q, orderedAllLabelAssociatorInv m n p
      (orderedAllLabelAssociator m n p c) q ≈ c q := by
  intro q
  exact Q'.eqv_trans _ _ _
    (basisChange_comp (orderedAssociatorCoordinateBases m n p)
      .left .right .left c q)
    (basisChange_refl (orderedAssociatorCoordinateBases m n p) .left c q)

/-- Left then right ordered recoupling returns all right-tree coordinates. -/
theorem orderedAllLabelAssociator_right_roundtrip (m n p : Nat)
    (c : LeftNestedCGChannel n p m → Q') :
    ∀ q, orderedAllLabelAssociator m n p
      (orderedAllLabelAssociatorInv m n p c) q ≈ c q := by
  intro q
  exact Q'.eqv_trans _ _ _
    (basisChange_comp (orderedAssociatorCoordinateBases m n p)
      .right .left .right c q)
    (basisChange_refl (orderedAssociatorCoordinateBases m n p) .right c q)

end YMGap.Continuum.SU2OrderedAssociatorCoordinateBases

#print axioms YMGap.Continuum.SU2OrderedAssociatorCoordinateBases.orderedRightNestedCoordinates_congr
#print axioms YMGap.Continuum.SU2OrderedAssociatorCoordinateBases.orderedRightNestedCoordinates_reconstruct
#print axioms YMGap.Continuum.SU2OrderedAssociatorCoordinateBases.orderedRightNestedReconstruct_coordinates
#print axioms YMGap.Continuum.SU2OrderedAssociatorCoordinateBases.orderedAssociatorCoordinateBases
#print axioms YMGap.Continuum.SU2OrderedAssociatorCoordinateBases.orderedAllLabelAssociator_eq_phase_cyclic
#print axioms YMGap.Continuum.SU2OrderedAssociatorCoordinateBases.orderedAllLabelAssociatorInv_eq_cyclic
#print axioms YMGap.Continuum.SU2OrderedAssociatorCoordinateBases.orderedAllLabelAssociator_left_roundtrip
#print axioms YMGap.Continuum.SU2OrderedAssociatorCoordinateBases.orderedAllLabelAssociator_right_roundtrip
