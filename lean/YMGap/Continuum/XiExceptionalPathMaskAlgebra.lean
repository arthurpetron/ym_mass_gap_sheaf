/-
# Exact path and residual mask algebra

This file supplies the multiplicative identities needed by the recoverable
branch router.  A path mask whose selected occurrences are exclusively
occupied splits the product of two occurrence-mask weights into the path
weight and the two residual weights.  On the right-safe region, the routed
background/external pair is exactly a component swap of the residual pair,
so its two family activities preserve the residual product.
-/

import YMGap.Continuum.XiExceptionalBranchRouter

namespace YMGap.Continuum.XiExceptionalPathMaskAlgebra

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalBranchRouter

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-! ## 1. Function-mask path partition -/

def residualMask (path mask : Nat → Bool) (i : Nat) : Bool :=
  (!path i) && mask i

private theorem factor_partition
    (a b p c d A B P C D : Q')
    (hhead : a * b ≈ p * (c * d))
    (htail : A * B ≈ P * (C * D)) :
    (a * A) * (b * B) ≈ (p * P) * ((c * C) * (d * D)) := by
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_trans _ _ _ (mul_eqv_congr_both hhead htail) ?_)
  · ring_qeqv
  · ring_qeqv

private theorem head_partition_off (a b : Q') :
    a * b ≈ 1 * (a * b) :=
  Q'.eqv_symm (Q'.one_mul_eqv (a * b))

private theorem head_partition_single_left (a : Q') :
    a * 1 ≈ a * (1 * 1) :=
  Q'.mul_eqv_congr_left a 1 (1 * 1)
    (Q'.eqv_symm (Q'.one_mul_eqv 1))

private theorem head_partition_single_right (a : Q') :
    1 * a ≈ a * (1 * 1) :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv 1 a)
    (head_partition_single_left a)

/-- Extracting an exclusively occupied path from two masks preserves every
activity factor exactly: path occurrences contribute once to `path`, while
all other selected occurrences remain on their original residual side. -/
theorem maskWeightFrom_path_partition
    (w : Q') (label : L.Plaquette → Rep)
    (path left right : Nat → Bool)
    (hexclusive : ∀ i, path i = true →
      differentBits (left i) (right i) = true) :
    ∀ (Gamma : List (Polymer L)) (offset : Nat),
      maskWeightFrom w Gamma label left offset *
          maskWeightFrom w Gamma label right offset ≈
        maskWeightFrom w Gamma label path offset *
          (maskWeightFrom w Gamma label (residualMask path left) offset *
            maskWeightFrom w Gamma label (residualMask path right) offset)
  | [], _ => by
      simp only [maskWeightFrom]
      ring_qeqv
  | X :: Gamma, offset => by
      have ih := maskWeightFrom_path_partition w label path left right
        hexclusive Gamma (offset + 1)
      simp only [maskWeightFrom]
      cases hp : path offset with
      | false =>
          cases hl : left offset <;> cases hr : right offset <;>
            simp only [hp, hl, hr, Bool.false_eq_true, Bool.not_false,
              Bool.true_and, residualMask, if_false, if_true] <;>
            exact factor_partition _ _ _ _ _ _ _ _ _ _
              (head_partition_off _ _) ih
      | true =>
          have he := hexclusive offset hp
          cases hl : left offset <;> cases hr : right offset <;>
            simp only [hp, hl, hr, differentBits, Bool.false_eq_true,
              Bool.not_true, Bool.false_and, residualMask, if_false,
              if_true] at he ⊢
          · cases he
          · exact factor_partition _ _ _ _ _ _ _ _ _ _
              (head_partition_single_right _) ih
          · exact factor_partition _ _ _ _ _ _ _ _ _ _
              (head_partition_single_left _) ih
          · cases he

theorem maskWeight_path_partition
    (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep)
    (path left right : Nat → Bool)
    (hexclusive : ∀ i, path i = true →
      differentBits (left i) (right i) = true) :
    maskWeight w Gamma label left * maskWeight w Gamma label right ≈
      maskWeight w Gamma label path *
        (maskWeight w Gamma label (residualMask path left) *
          maskWeight w Gamma label (residualMask path right)) :=
  maskWeightFrom_path_partition w label path left right hexclusive Gamma 0

/-! ## 2. Finite path and residual bit vectors -/

def pathOccurrenceBits (n : Nat) (vertices : List Nat) : OccBitVec n :=
  bitsFromMask n (fun i => decide (i ∈ vertices)) 0

def residualBits (path bits : OccBitVec n) : OccBitVec n :=
  bitsFromMask n (fun i => (!path.at i) && bits.at i) 0

theorem pathOccurrenceBits_at (n : Nat) (vertices : List Nat)
    (i : Nat) (hi : i < n) :
    (pathOccurrenceBits n vertices).at i = decide (i ∈ vertices) := by
  unfold pathOccurrenceBits
  simpa using bitsFromMask_at n (fun j => decide (j ∈ vertices)) 0 i hi

theorem residualBits_at (path bits : OccBitVec n)
    (i : Nat) (hi : i < n) :
    (residualBits path bits).at i = ((!path.at i) && bits.at i) := by
  unfold residualBits
  simpa using bitsFromMask_at n
    (fun j => (!path.at j) && bits.at j) 0 i hi

private theorem maskWeightFrom_congr_on
    (w : Q') (label : L.Plaquette → Rep) (mask1 mask2 : Nat → Bool) :
    ∀ (Gamma : List (Polymer L)) (offset : Nat),
      (∀ k, k < Gamma.length →
        mask1 (offset + k) = mask2 (offset + k)) →
      maskWeightFrom w Gamma label mask1 offset =
        maskWeightFrom w Gamma label mask2 offset
  | [], _, _ => by simp only [maskWeightFrom]
  | X :: Gamma, offset, hmask => by
      simp only [maskWeightFrom]
      rw [show mask1 offset = mask2 offset by simpa using hmask 0 (by simp)]
      apply congrArg
        (fun tail : Q' =>
          (if mask2 offset then activity w X label else 1) * tail)
      apply maskWeightFrom_congr_on w label mask1 mask2 Gamma (offset + 1)
      intro k hk
      rw [show offset + 1 + k = offset + (k + 1) by omega]
      exact hmask (k + 1) (by simp; omega)

theorem maskWeight_congr_on
    (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep) (mask1 mask2 : Nat → Bool)
    (hmask : ∀ i, i < Gamma.length → mask1 i = mask2 i) :
    maskWeight w Gamma label mask1 = maskWeight w Gamma label mask2 := by
  unfold maskWeight
  apply maskWeightFrom_congr_on w label mask1 mask2 Gamma 0
  intro k hk
  simpa using hmask k hk

private theorem bitMask_residualBits_on
    (path bits : OccBitVec n) (i : Nat) (hi : i < n) :
    bitMask (residualBits path bits) i =
      residualMask (bitMask path) (bitMask bits) i := by
  change (residualBits path bits).at i =
    residualMask (bitMask path) (bitMask bits) i
  rw [residualBits_at path bits i hi]
  rfl

/-! ## 3. The right-safe router is an exact residual swap -/

theorem routedBackground_eq_swapLeft_on
    (safe : Nat → Bool) (left right : OccBitVec n)
    (hrightSafe : ∀ i, i < n → right.at i = true → safe i = true)
    (i : Nat) (hi : i < n) :
    bitMask (routedBackground safe left) i =
      swapLeftMask (fun j => !safe j) (bitMask left) (bitMask right) i := by
  change (routedBackground safe left).at i =
    swapLeftMask (fun j => !safe j) (bitMask left) (bitMask right) i
  rw [routedBackground_at safe left i hi]
  unfold bitMask swapLeftMask
  cases hs : safe i with
  | true => simp [hs]
  | false =>
      have hr : right.at i = false := by
        cases hri : right.at i with
        | false => rfl
        | true =>
            have hsafe := hrightSafe i hi hri
            rw [hs] at hsafe
            cases hsafe
      simp [hs, hr]

theorem routedExternal_eq_swapRight_on
    (safe : Nat → Bool) (left right : OccBitVec n)
    (hrightSafe : ∀ i, i < n → right.at i = true → safe i = true)
    (i : Nat) (hi : i < n) :
    bitMask (routedExternal safe left right) i =
      swapRightMask (fun j => !safe j) (bitMask left) (bitMask right) i := by
  change (routedExternal safe left right).at i =
    swapRightMask (fun j => !safe j) (bitMask left) (bitMask right) i
  rw [routedExternal_at safe left right i hi]
  unfold bitMask swapRightMask
  cases hs : safe i with
  | true => simp [hs]
  | false =>
      have hr : right.at i = false := by
        cases hri : right.at i with
        | false => rfl
        | true =>
            have hsafe := hrightSafe i hi hri
            rw [hs] at hsafe
            cases hsafe
      simp [hs, hr]

/-- On the right-safe region, routing preserves the complete residual mask
product exactly. -/
theorem routedMaskWeight_preserved
    (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep) (safe : Nat → Bool)
    (left right : OccBitVec Gamma.length)
    (hrightSafe : ∀ i, i < Gamma.length →
      right.at i = true → safe i = true) :
    maskWeight w Gamma label (bitMask (routedBackground safe left)) *
        maskWeight w Gamma label
          (bitMask (routedExternal safe left right)) ≈
      maskWeight w Gamma label (bitMask left) *
        maskWeight w Gamma label (bitMask right) := by
  rw [maskWeight_congr_on w Gamma label
      (bitMask (routedBackground safe left))
      (swapLeftMask (fun j => !safe j) (bitMask left) (bitMask right))
      (routedBackground_eq_swapLeft_on safe left right hrightSafe),
    maskWeight_congr_on w Gamma label
      (bitMask (routedExternal safe left right))
      (swapRightMask (fun j => !safe j) (bitMask left) (bitMask right))
      (routedExternal_eq_swapRight_on safe left right hrightSafe)]
  exact maskWeight_swap_preserved w Gamma label
    (fun j => !safe j) (bitMask left) (bitMask right)

theorem routedFamilyActivity_preserved
    (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep) (safe : Nat → Bool)
    (left right : OccBitVec Gamma.length)
    (hrightSafe : ∀ i, i < Gamma.length →
      right.at i = true → safe i = true) :
    familyActivity w (selectByBits Gamma (routedBackground safe left)) label *
        familyActivity w
          (selectByBits Gamma (routedExternal safe left right)) label ≈
      familyActivity w (selectByBits Gamma left) label *
        familyActivity w (selectByBits Gamma right) label := by
  have hout := routedMaskWeight_preserved w Gamma label safe left right
    hrightSafe
  have hbg := maskWeight_eqv_familyActivity w Gamma label
    (bitMask (routedBackground safe left))
  have hext := maskWeight_eqv_familyActivity w Gamma label
    (bitMask (routedExternal safe left right))
  have hleft := maskWeight_eqv_familyActivity w Gamma label (bitMask left)
  have hright := maskWeight_eqv_familyActivity w Gamma label (bitMask right)
  rw [maskFamily_toMask_eq_selectByBits] at hbg hext hleft hright
  exact Q'.eqv_trans _ _ _
    (mul_eqv_congr_both (Q'.eqv_symm hbg) (Q'.eqv_symm hext))
    (Q'.eqv_trans _ _ _ hout (mul_eqv_congr_both hleft hright))

#print axioms maskWeight_path_partition
#print axioms pathOccurrenceBits_at
#print axioms residualBits_at
#print axioms maskWeight_congr_on
#print axioms routedMaskWeight_preserved
#print axioms routedFamilyActivity_preserved

end YMGap.Continuum.XiExceptionalPathMaskAlgebra
