/-
# Constructive-real completion of the SU(2) pointwise heat series

`SU2AllLabelPointwiseHeatCorridor` proves the exact rational corridor

    1055/2272 ≤ pointwiseHeatPartial w x M ≤ 3489/2272

for every finite doubled-label partial, provided `0 ≤ w ≤ 1/2` and
`x ∈ [-1,1]`.  This module performs the missing all-label completion:

* the sharp post-label-two ratio `1/72` is weakened to `1/2`;
* the magnitude of every block beginning at tail index `M` is bounded by
  `(1/2)^M`;
* hence `ε.den` is an explicit, `Type`-level Cauchy modulus for the rational
  partials;
* the resulting `CReal` inherits the exact rational floor and ceiling in the
  semantic `geRat` / `leRat` orders (and in the legacy one-slack order).

Honest scope: this is the infinite-character completion of the pointwise
central SU(2) class kernel at a fixed rational nome and class coordinate.  It
does not identify the completed kernel with an interacting BF4 slab factor,
does not supply a spacing-uniform nome window along the physical BF4
trajectory, and does not interchange this limit with Haar integration or a
block-spin map.

## Axiom gate

Only exact `Q'` arithmetic, structural induction, finite sums, and the
constructive halving modulus are used.  There is no `Classical.*`, `Real`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Constructive.HalfPow
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.GroupedAllLabelHaarRefresh
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor

/-! ## 1. A halving majorant for every shifted tail -/

/-- The signed tail term with tail index `k` corresponding to doubled label
`2+k`. -/
def shiftedHeatTerm (w x : Q') (k : Nat) : Q' :=
  pointwiseHeatTerm w x (2 + k)

/-- Its positive squared-dimension majorant. -/
def shiftedHeatMajorant (w : Q') (k : Nat) : Q' :=
  pointwiseHeatMajorant w (2 + k)

/-- The magnitude block beginning at tail index `start`. -/
def shiftedHeatMajorantBlock (w : Q') (start length : Nat) : Q' :=
  finSum (fun j => shiftedHeatMajorant w (start + j)) length

theorem shiftedHeatMajorant_nonnegative
    {w : Q'} (hw0 : (0 : Q') ≤ w) (k : Nat) :
    (0 : Q') ≤ shiftedHeatMajorant w k := by
  exact tailTerm_nonneg hw0 2 (2 + k)

/-- The sharp `1/72` recurrence implies the simpler halving recurrence. -/
theorem shiftedHeatMajorant_succ_le_half
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (k : Nat) :
    shiftedHeatMajorant w (k + 1) ≤
      half * shiftedHeatMajorant w k := by
  have hsharp :
      shiftedHeatMajorant w (k + 1) ≤
        sharpTailRatio * shiftedHeatMajorant w k := by
    unfold shiftedHeatMajorant
    have hindex : 2 + (k + 1) = (2 + k) + 1 := by omega
    rw [hindex]
    exact pointwiseHeatMajorant_succ_le hw0 hw (2 + k) (by omega)
  have hratio : sharpTailRatio ≤ half := by decide
  have hscaled :
      sharpTailRatio * shiftedHeatMajorant w k ≤
        half * shiftedHeatMajorant w k :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hratio (shiftedHeatMajorant_nonnegative hw0 k)
  exact Q'.le_trans' _ _ _ hsharp hscaled

/-- The label-two head fits below `1/2`. -/
theorem shiftedHeatMajorant_zero_le_half
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) :
    shiftedHeatMajorant w 0 ≤ half := by
  exact Q'.le_trans' _ _ _
    (by
      simpa [shiftedHeatMajorant] using
        (labelTwo_majorant_le hw0 hw))
    (by decide)

/-- At tail index `k`, the majorant is at most
`(1/2) * (1/2)^k`. -/
theorem shiftedHeatMajorant_le_halfPow
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (k : Nat) :
    shiftedHeatMajorant w k ≤ half * half ^ k := by
  exact CharacterTail.geom_dom
    (shiftedHeatMajorant w) half half
    half_nonneg
    (shiftedHeatMajorant_zero_le_half hw0 hw)
    (shiftedHeatMajorant_succ_le_half hw0 hw)
    k

/-- Every finite magnitude block beginning at tail index `start` is bounded
by `(1/2)^start`. -/
theorem shiftedHeatMajorantBlock_le_halfPow
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (start length : Nat) :
    shiftedHeatMajorantBlock w start length ≤ half ^ start := by
  unfold shiftedHeatMajorantBlock
  apply CharacterTail.geom_series_le
    (fun j => shiftedHeatMajorant w (start + j))
    (half * half ^ start)
    half
    (half ^ start)
  · exact half_nonneg
  · exact Q'.pow_nonneg half half_nonneg start
  · simpa only [Nat.add_zero] using
      shiftedHeatMajorant_le_halfPow hw0 hw start
  · intro k
    have hindex : start + (k + 1) = (start + k) + 1 := by omega
    rw [hindex]
    exact shiftedHeatMajorant_succ_le_half hw0 hw (start + k)
  · exact Q'.le_of_eqv (two_halves (half ^ start))

/-! ## 2. Two-sided signed block bounds -/

private theorem shiftedHeatTerm_twoSided
    {w x : Q'} (hw0 : (0 : Q') ≤ w)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (k : Nat) :
    -shiftedHeatMajorant w k ≤ shiftedHeatTerm w x k ∧
      shiftedHeatTerm w x k ≤ shiftedHeatMajorant w k := by
  exact pointwiseHeatTerm_twoSided hw0 hxLower hxUpper (2 + k)

private theorem shiftedHeatTerm_add_majorant_nonnegative
    {w x : Q'} (hw0 : (0 : Q') ≤ w)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (k : Nat) :
    (0 : Q') ≤
      shiftedHeatTerm w x k + shiftedHeatMajorant w k := by
  have hlower :=
    (shiftedHeatTerm_twoSided hw0 hxLower hxUpper k).1
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (Q'.neg_add_self_eqv (shiftedHeatMajorant w k))) ?_
  exact Q'.add_le_add_right
    (-(shiftedHeatMajorant w k))
    (shiftedHeatTerm w x k)
    (shiftedHeatMajorant w k)
    hlower

/-- Adding one tail label changes the displayed partial by the corresponding
signed shifted term, up to rational setoid equality. -/
theorem pointwiseHeatPartial_succ_eqv
    (w x : Q') (n : Nat) :
    (pointwiseHeatPartial w x (n + 1)).eqv
      (pointwiseHeatPartial w x n + shiftedHeatTerm w x n) := by
  unfold pointwiseHeatPartial shiftedHeatTerm
  exact Q'.eqv_symm
    (Q'.add_assoc_eqv
      ((1 : Q') + pointwiseHeatTerm w x 1)
      (finSum (fun k => pointwiseHeatTerm w x (2 + k)) n)
      (pointwiseHeatTerm w x (2 + n)))

/-- Increasing the tail cutoff by `length` changes the finite partial by at
most the corresponding magnitude block, upper direction. -/
theorem pointwiseHeatPartial_block_upper
    {w x : Q'} (hw0 : (0 : Q') ≤ w)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (start : Nat) :
    ∀ length,
      pointwiseHeatPartial w x (start + length) ≤
        pointwiseHeatPartial w x start +
          shiftedHeatMajorantBlock w start length
  | 0 => by
      exact Q'.add_le_self_of_nonneg _ _ (Q'.le_refl' 0)
  | length + 1 => by
      have ih :=
        pointwiseHeatPartial_block_upper
          hw0 hxLower hxUpper start length
      rw [show start + (length + 1) = (start + length) + 1 by omega]
      change
        pointwiseHeatPartial w x ((start + length) + 1) ≤
          pointwiseHeatPartial w x start +
            (shiftedHeatMajorantBlock w start length +
              shiftedHeatMajorant w (start + length))
      exact Q'.le_trans' _ _ _
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (pointwiseHeatPartial_succ_eqv
              w x (start + length)))
          (Q'.add_le_add_left
            (pointwiseHeatPartial w x (start + length))
            (shiftedHeatTerm w x (start + length))
            (shiftedHeatMajorant w (start + length))
            (shiftedHeatTerm_twoSided
              hw0 hxLower hxUpper (start + length)).2))
        (Q'.le_trans' _ _ _
          (Q'.add_le_add_right
            (pointwiseHeatPartial w x (start + length))
            (pointwiseHeatPartial w x start +
              shiftedHeatMajorantBlock w start length)
            (shiftedHeatMajorant w (start + length))
            ih)
          (Q'.le_of_eqv
            (Q'.add_assoc_eqv
              (pointwiseHeatPartial w x start)
              (shiftedHeatMajorantBlock w start length)
              (shiftedHeatMajorant w (start + length)))))

/-- Increasing the tail cutoff by `length` changes the finite partial by at
most the corresponding magnitude block, reverse direction. -/
theorem pointwiseHeatPartial_block_lower
    {w x : Q'} (hw0 : (0 : Q') ≤ w)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (start : Nat) :
    ∀ length,
      pointwiseHeatPartial w x start ≤
        pointwiseHeatPartial w x (start + length) +
          shiftedHeatMajorantBlock w start length
  | 0 => by
      exact Q'.add_le_self_of_nonneg _ _ (Q'.le_refl' 0)
  | length + 1 => by
      have ih :=
        pointwiseHeatPartial_block_lower
          hw0 hxLower hxUpper start length
      rw [show start + (length + 1) = (start + length) + 1 by omega]
      change
        pointwiseHeatPartial w x start ≤
          pointwiseHeatPartial w x ((start + length) + 1) +
            (shiftedHeatMajorantBlock w start length +
              shiftedHeatMajorant w (start + length))
      refine Q'.le_trans' _ _ _ ih ?_
      have hraw :
          pointwiseHeatPartial w x (start + length) +
              shiftedHeatMajorantBlock w start length ≤
            (pointwiseHeatPartial w x (start + length) +
                shiftedHeatTerm w x (start + length)) +
              (shiftedHeatMajorantBlock w start length +
                shiftedHeatMajorant w (start + length)) :=
        Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg
          (pointwiseHeatPartial w x (start + length) +
            shiftedHeatMajorantBlock w start length)
          (shiftedHeatTerm w x (start + length) +
            shiftedHeatMajorant w (start + length))
          (shiftedHeatTerm_add_majorant_nonnegative
            hw0 hxLower hxUpper (start + length)))
        (Q'.le_of_eqv
          (Q'.add_swap_inner
            (pointwiseHeatPartial w x (start + length))
            (shiftedHeatMajorantBlock w start length)
            (shiftedHeatTerm w x (start + length))
            (shiftedHeatMajorant w (start + length))))
      exact Q'.le_trans' _ _ _ hraw
        (Q'.add_le_add_right _ _ _
          (Q'.ge_of_eqv
            (pointwiseHeatPartial_succ_eqv
              w x (start + length))))

/-! ## 3. Explicit Cauchy modulus and the completed all-label kernel -/

/-- The explicit cutoff modulus for the all-label pointwise heat series. -/
def pointwiseHeatModulus (ε : Q') : Nat := ε.den

/-- **Quantitative all-label Cauchy bound.**  Once both cutoffs are at least
`ε.den`, their pointwise heat partials differ by at most `ε` in both
directions.  The modulus is data, not extracted from a propositional
existence proof. -/
theorem pointwiseHeatPartial_cauchy
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (ε : Q') (hε : (0 : Q') < ε)
    (m n : Nat)
    (hm : pointwiseHeatModulus ε ≤ m)
    (hn : pointwiseHeatModulus ε ≤ n) :
    pointwiseHeatPartial w x m ≤
        pointwiseHeatPartial w x n + ε ∧
      pointwiseHeatPartial w x n ≤
        pointwiseHeatPartial w x m + ε := by
  have dir :
      ∀ k l : Nat,
        pointwiseHeatModulus ε ≤ k →
        k ≤ l →
        pointwiseHeatPartial w x l ≤
            pointwiseHeatPartial w x k + ε ∧
          pointwiseHeatPartial w x k ≤
            pointwiseHeatPartial w x l + ε := by
    intro k l hk hkl
    obtain ⟨length, rfl⟩ := Nat.exists_eq_add_of_le hkl
    have hpow : half ^ k ≤ ε := by
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hk
      rw [hoffset]
      exact Q'.le_trans' _ _ _
        (pow_half_antitone ε.den offset)
        (pow_half_le ε hε)
    have hblock :
        shiftedHeatMajorantBlock w k length ≤ ε :=
      Q'.le_trans' _ _ _
        (shiftedHeatMajorantBlock_le_halfPow hw0 hw k length)
        hpow
    exact
      ⟨Q'.le_trans' _ _ _
          (pointwiseHeatPartial_block_upper
            hw0 hxLower hxUpper k length)
          (Q'.add_le_add_left
            (pointwiseHeatPartial w x k)
            (shiftedHeatMajorantBlock w k length)
            ε hblock),
        Q'.le_trans' _ _ _
          (pointwiseHeatPartial_block_lower
            hw0 hxLower hxUpper k length)
          (Q'.add_le_add_left
            (pointwiseHeatPartial w x (k + length))
            (shiftedHeatMajorantBlock w k length)
            ε hblock)⟩
  rcases Nat.le_total m n with hmn | hnm
  · exact ⟨(dir m n hm hmn).2, (dir m n hm hmn).1⟩
  · exact ⟨(dir n m hn hnm).1, (dir n m hn hnm).2⟩

/-- **The completed all-label pointwise SU(2) central heat kernel.**
Its `n`-th rational approximation is the genuine character partial through
tail index `n`; its Cauchy modulus is `ε.den`. -/
def allLabelPointwiseHeat
    (w x : Q')
    (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    CReal where
  approx := pointwiseHeatPartial w x
  cauchy := by
    intro ε hε
    exact
      ⟨pointwiseHeatModulus ε,
        pointwiseHeatPartial_cauchy
          hw0 hw hxLower hxUpper ε hε⟩

@[simp] theorem allLabelPointwiseHeat_approx
    (w x : Q')
    (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (n : Nat) :
    (allLabelPointwiseHeat
      w x hw0 hw hxLower hxUpper).approx n =
        pointwiseHeatPartial w x n := rfl

/-! ## 4. The exact rational corridor survives completion -/

/-- The completed kernel lies above the exact finite-partial floor in the
semantic constructive-real order. -/
theorem allLabelPointwiseHeat_ge_floor
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    ExpPos.geRat
      (allLabelPointwiseHeat w x hw0 hw hxLower hxUpper)
      allLabelHaarFloor := by
  apply ExpPos.geRat_of_eventually
  exact
    ⟨0, fun n _ =>
      allLabelHaarFloor_le_pointwiseHeatPartial
        hw0 hw hxLower hxUpper n⟩

/-- The completed kernel lies below the exact finite-partial ceiling in the
semantic constructive-real order. -/
theorem allLabelPointwiseHeat_le_ceiling
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    CReal.leRat
      (allLabelPointwiseHeat w x hw0 hw hxLower hxUpper)
      allLabelHaarCeiling := by
  apply CReal.leRat_of_eventually
  exact
    ⟨0, fun n _ =>
      pointwiseHeatPartial_le_allLabelHaarCeiling
        hw0 hw hxLower hxUpper n⟩

/-- Legacy one-slack lower-order formulation of the same floor. -/
theorem ofQ'_floor_le_allLabelPointwiseHeat
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    CReal.ofQ' allLabelHaarFloor ≤
      allLabelPointwiseHeat w x hw0 hw hxLower hxUpper :=
  CReal.ofQ'_le_of_approx_ge
    (fun n =>
      allLabelHaarFloor_le_pointwiseHeatPartial
        hw0 hw hxLower hxUpper n)

/-- Legacy one-slack upper-order formulation of the same ceiling. -/
theorem allLabelPointwiseHeat_le_ofQ'_ceiling
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    allLabelPointwiseHeat w x hw0 hw hxLower hxUpper ≤
      CReal.ofQ' allLabelHaarCeiling :=
  CReal.le_ofQ'_of_approx_le
    (fun n =>
      pointwiseHeatPartial_le_allLabelHaarCeiling
        hw0 hw hxLower hxUpper n)

/-- The completed pointwise heat kernel has the same explicit positive
rational witness as every finite partial. -/
theorem allLabelPointwiseHeat_positive
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    CReal.IsPositive
      (allLabelPointwiseHeat w x hw0 hw hxLower hxUpper) :=
  ⟨allLabelHaarFloor,
    allLabelHaarFloor_pos,
    ofQ'_floor_le_allLabelPointwiseHeat
      hw0 hw hxLower hxUpper⟩

end YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion.shiftedHeatMajorant_succ_le_half
#print axioms YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion.shiftedHeatMajorantBlock_le_halfPow
#print axioms YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion.pointwiseHeatPartial_block_upper
#print axioms YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion.pointwiseHeatPartial_block_lower
#print axioms YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion.pointwiseHeatPartial_cauchy
#print axioms YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion.allLabelPointwiseHeat
#print axioms YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion.allLabelPointwiseHeat_ge_floor
#print axioms YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion.allLabelPointwiseHeat_le_ceiling
#print axioms YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion.ofQ'_floor_le_allLabelPointwiseHeat
#print axioms YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion.allLabelPointwiseHeat_le_ofQ'_ceiling
#print axioms YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion.allLabelPointwiseHeat_positive
