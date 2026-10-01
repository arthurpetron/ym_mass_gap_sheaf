/-
# Finite dimension-squared Gaussian tail by representation blocks

This is a scalar finite-label estimate.  It does not compare an interacting
source energy with its centered variance or assert a physical nome schedule.
-/

import YMGap.Continuum.BondMovingScaledNorm
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.RefinedRetune
import YMGap.Continuum.SemicircleConvClosed
import YMGap.Continuum.FiveHolonomyPerronCutoff
import YMGap.Continuum.RingNormaliser
import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
import YMGap.Constructive.CRealMul

namespace YMGap.Continuum.SU2HeatDimensionBlockTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Constructive.CReal
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.RefinedRetune
open YMGap.Continuum.SemicircleConvClosed (finSum_const_eqv)
open YMGap.Continuum.FiveHolonomyPerronCutoff (geometricPartial_le_two)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion (qpow_eqv_pow)

local infix:50 " ≈ " => Q'.eqv

private theorem dimension_growth : ∀ r : Nat, (r + 1)^2 ≤ 4^r
  | 0 => by decide
  | r + 1 => by
      have h := dimension_growth r
      have hstep : (r + 2)^2 ≤ 4 * (r + 1)^2 := by
        calc
          (r + 2)^2 ≤ (2 * (r + 1))^2 := Nat.pow_le_pow_left (by omega) 2
          _ = 4 * (r + 1)^2 := by rw [Nat.mul_pow]
      calc
        (r + 1 + 1)^2 = (r + 2)^2 := by congr 1
        _ ≤ 4 * (r + 1)^2 := hstep
        _ ≤ 4 * 4^r := Nat.mul_le_mul_left 4 h
        _ = 4^(r+1) := by rw [Nat.pow_succ]; omega

private theorem ofNat_pow_eqv (a : Nat) : ∀ r : Nat,
    Q'.ofNat (a^r) ≈ qpow (Q'.ofNat a) r
  | 0 => Q'.eqv_refl _
  | r + 1 => by
      rw [Nat.pow_succ]
      exact Q'.eqv_trans _ _ _ (ofNat_mul_eqv (a^r) a)
        (Q'.mul_eqv_congr_right _ _ _ (ofNat_pow_eqv a r))

private theorem finSum_add_block (f : Nat → Q') (a : Nat) : ∀ t,
    finSum f (a + t) ≈ finSum f a + finSum (fun s => f (a + s)) t
  | 0 => Q'.eqv_symm (QPoly.q_add_zero_eqv _)
  | t + 1 => by
      rw [show a + (t + 1) = (a + t) + 1 by omega,
        finSum_succ, finSum_succ]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (finSum_add_block f a t))
        (Q'.add_assoc_eqv _ _ _)

private theorem finSum_block (f : Nat → Q') (L : Nat) : ∀ B,
    finSum f (B * L) ≈
      finSum (fun i => finSum (fun s => f (i * L + s)) L) B
  | 0 => by rw [Nat.zero_mul]; exact Q'.eqv_refl 0
  | B + 1 => by
      rw [Nat.succ_mul, finSum_succ]
      exact Q'.eqv_trans _ _ _ (finSum_add_block f (B * L) L)
        (Q'.add_eqv_congr_right _ _ _ (finSum_block f L B))

private theorem block_exponent (L r s : Nat) (hL : 1 ≤ L) (hr : 1 ≤ r) :
    r * (L * L) ≤ c4 (r * L + s) := by
  let k := r * L + s
  have hkL : L ≤ k := by
    have hmul := Nat.mul_le_mul_right L hr
    dsimp [k]
    omega
  have hkr : r * L ≤ k := by dsimp [k]; omega
  have hprod : (r * L) * L ≤ k * k := Nat.mul_le_mul hkr hkL
  have hkk : k * k ≤ k * (k + 2) := Nat.mul_le_mul_left k (by omega)
  unfold c4
  rw [← Nat.mul_assoc]
  exact Nat.le_trans hprod hkk

private theorem block_dimension (L r s : Nat) (hL : 1 ≤ L) (hs : s < L) :
    (r * L + s + 1)^2 ≤ 4^r * L^2 := by
  have hindex : r * L + s + 1 ≤ (r + 1) * L := by
    rw [Nat.add_mul]
    omega
  have hp := Nat.pow_le_pow_left hindex 2
  have hg := dimension_growth r
  calc
    (r * L + s + 1)^2 ≤ ((r + 1) * L)^2 := hp
    _ = (r + 1)^2 * L^2 := Nat.mul_pow _ _ _
    _ ≤ 4^r * L^2 := Nat.mul_le_mul_right _ hg

private theorem block_term_bound {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (L r s : Nat) (hL : 1 ≤ L)
    (hr : 1 ≤ r) (hs : s < L) :
    tailTerm w 2 (r * L + s) ≤
      Q'.ofNat (4^r * L^2) * qpow (qpow w (L*L)) r := by
  let q := qpow w (L*L)
  have hc := CReal.ofNat_le_ofNat (block_dimension L r s hL hs)
  have he : qpow w (c4 (r * L + s)) ≤ qpow q r := by
    have hpow := qpow_antitone hw0 hw1 (r * (L*L))
      (c4 (r*L+s)) (block_exponent L r s hL hr)
    have heq := qpow_qpow w (L*L) r
    rw [Nat.mul_comm (L*L) r] at heq
    exact Q'.le_trans' _ _ _ hpow (Q'.le_of_eqv (Q'.eqv_symm heq))
  unfold tailTerm
  exact Q'.mul_le_mul_of_nonneg hc he
    (zero_le_ofNat _)
    (qpow_nonneg w hw0 _)

private theorem block_term_rate (w : Q') (L r : Nat) :
    Q'.ofNat (4^r * L^2) * qpow (qpow w (L*L)) r ≈
      Q'.ofNat (L^2) * qpow (4 * qpow w (L*L)) r := by
  let q := qpow w (L*L)
  have h4 : Q'.ofNat (4^r) ≈ qpow (4 : Q') r := ofNat_pow_eqv 4 r
  have hprod : Q'.ofNat (4^r * L^2) ≈ qpow (4 : Q') r * Q'.ofNat (L^2) :=
    Q'.eqv_trans _ _ _ (ofNat_mul_eqv (4^r) (L^2))
      (Q'.mul_eqv_congr_right _ _ _ h4)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hprod)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_comm_eqv (qpow (4 : Q') r) (Q'.ofNat (L^2))))
      (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_symm (qpow_mul_base 4 q r)))))

private theorem finSum_le_const (f : Nat → Q') (C : Q') :
    ∀ L, (∀ s, s < L → f s ≤ C) →
      finSum f L ≤ finSum (fun _ => C) L
  | 0, _ => Q'.le_refl' 0
  | L+1, h => by
      have hp := finSum_le_const f C L (fun s hs => h s (by omega))
      rw [finSum_succ, finSum_succ]
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add_left (finSum f L) (f L) C (h L (by omega)))
        (Q'.add_le_add_right (finSum f L) (finSum (fun _ => C) L) C hp)

private theorem block_bound {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (L r : Nat) (hL : 1 ≤ L) (hr : 1 ≤ r) :
    finSum (fun s => tailTerm w 2 (r*L+s)) L ≤
      Q'.ofNat (L^3) * qpow (4 * qpow w (L*L)) r := by
  let C := Q'.ofNat (4^r * L^2) * qpow (qpow w (L*L)) r
  have hterm : ∀ s, s < L → tailTerm w 2 (r*L+s) ≤ C :=
    fun s hs => block_term_bound hw0 hw1 L r s hL hr hs
  have hs : finSum (fun s => tailTerm w 2 (r*L+s)) L ≤ finSum (fun _ => C) L :=
    finSum_le_const _ C L hterm
  have hconst := finSum_const_eqv C L
  have hL3 : Q'.ofNat L * Q'.ofNat (L^2) ≈ Q'.ofNat (L^3) := by
    have hn : L * L^2 = L^3 := by
      calc
        L * L^2 = L^2 * L := Nat.mul_comm _ _
        _ = L^3 := (Nat.pow_succ L 2).symm
    rw [← hn]
    exact Q'.eqv_symm (ofNat_mul_eqv L (L^2))
  have hrewrite : Q'.ofNat L * C ≈
      Q'.ofNat (L^3) * qpow (4 * qpow w (L*L)) r := by
    dsimp [C]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (block_term_rate w L r))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_eqv_congr_right _ _ _ hL3))
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hconst hrewrite))

private theorem shifted_geometric_le_two_rate (rate : Q')
    (hr0 : (0 : Q') ≤ rate)
    (hrHalf : rate ≤ HalfPow.half) (B : Nat) :
    finSum (fun i => rate ^ (i+1)) B ≤ rate * 2 := by
  have hgeom : finSum (fun i => rate^i) B ≤ 2 :=
    geometricPartial_le_two hr0 hrHalf B
  have hterms : finSum (fun i => rate^(i+1)) B ≈
      finSum (fun i => rate * rate^i) B :=
    RationalTail.finSum_eqv_congr _ _ (fun i => by
      rw [Q'.pow_succ]
      exact Q'.eqv_refl _) B
  have hpull : finSum (fun i => rate * rate^i) B ≈
      rate * finSum (fun i => rate^i) B :=
    Q'.eqv_symm (RationalTail.const_mul_finSum (fun i => rate^i) rate B)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hterms hpull))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hgeom hr0)

/-- A finite window of `M` doubled-spin labels, with both SU(2)
representation dimensions retained. -/
def dimensionTail (w : Q') (L M : Nat) : Q' :=
  finSum (fun s => tailTerm w 2 (L+s)) M

/-- Blockwise Gaussian tail.  This is purely a finite scalar estimate;
`q <= 1/8` is explicit data, not an asserted nome/scaling schedule. -/
theorem dimensionTail_le_eight_blocks {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (L : Nat) (hL : 1 ≤ L)
    (hq : qpow w (L*L) ≤ Q'.mkPos 1 8 (by decide))
    (M : Nat) :
    dimensionTail w L M ≤
      (8 : Q') * Q'.ofNat (L^3) * qpow w (L*L) := by
  let q := qpow w (L*L)
  let rate := 4*q
  let B := M+1
  let f := fun s => tailTerm w 2 (L+s)
  have hq0 : (0 : Q') ≤ q := qpow_nonneg w hw0 _
  have hr0 : (0 : Q') ≤ rate := Q'.mul_nonneg _ _ (by decide) hq0
  have hrHalf : rate ≤ HalfPow.half := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hq (by decide))
      (by decide)
  have hpad : M ≤ B*L := by
    have hm := Nat.mul_le_mul_left B hL
    have hm0 : M ≤ B*1 := by dsimp [B]; omega
    exact Nat.le_trans hm0 hm
  have hprefix : dimensionTail w L M ≤ finSum f (B*L) :=
    RationalTail.finSum_monotone_of_nonneg f
      (fun s => tailTerm_nonneg hw0 2 (L+s)) M (B*L) hpad
  have hblocks : finSum f (B*L) ≈
      finSum (fun i => finSum (fun s => f (i*L+s)) L) B :=
    finSum_block f L B
  have hblock : ∀ i, finSum (fun s => f (i*L+s)) L ≤
      Q'.ofNat (L^3) * rate^(i+1) := by
    intro i
    have h := block_bound hw0 hw1 L (i+1) hL (by omega)
    have heq : (fun s => f (i*L+s)) =
        (fun s => tailTerm w 2 ((i+1)*L+s)) := by
      funext s
      dsimp [f]
      have hn : L + (i*L+s) = (i+1)*L+s := by
        rw [Nat.succ_mul]
        omega
      exact congrArg (tailTerm w 2) hn
    rw [heq]
    exact Q'.le_trans' _ _ _ h
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.le_of_eqv (qpow_eqv_pow rate (i+1))) (zero_le_ofNat _))
  have hsum : finSum (fun i => finSum (fun s => f (i*L+s)) L) B ≤
      finSum (fun i => Q'.ofNat (L^3) * rate^(i+1)) B :=
    ExpNeg.finSum_le_finSum_of_termwise _ _ hblock B
  have hpull : finSum (fun i => Q'.ofNat (L^3) * rate^(i+1)) B ≈
      Q'.ofNat (L^3) * finSum (fun i => rate^(i+1)) B :=
    Q'.eqv_symm (RationalTail.const_mul_finSum _ _ _)
  have hgeo := shifted_geometric_le_two_rate rate hr0 hrHalf B
  have hlast : Q'.ofNat (L^3) * finSum (fun i => rate^(i+1)) B ≤
      Q'.ofNat (L^3) * (rate*2) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgeo (zero_le_ofNat _)
  have hnormal : Q'.ofNat (L^3) * (rate*2) ≈
      (8 : Q') * Q'.ofNat (L^3) * q := by
    change Q'.ofNat (L^3) * ((4*q)*2) ≈ (8:Q') * Q'.ofNat (L^3) * q
    exact poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.const 4) (.var 1)) (.const 2)))
      (.mul (.mul (.const 8) (.var 0)) (.var 1))
      (by decide) (fun | 0 => Q'.ofNat (L^3) | _ => q)
  exact Q'.le_trans' _ _ _ hprefix
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hblocks)
      (Q'.le_trans' _ _ _ hsum
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpull)
          (Q'.le_trans' _ _ _ hlast (Q'.le_of_eqv hnormal)))))

end YMGap.Continuum.SU2HeatDimensionBlockTail

#print axioms YMGap.Continuum.SU2HeatDimensionBlockTail.dimension_growth
#print axioms YMGap.Continuum.SU2HeatDimensionBlockTail.block_term_bound
#print axioms YMGap.Continuum.SU2HeatDimensionBlockTail.block_bound
#print axioms YMGap.Continuum.SU2HeatDimensionBlockTail.dimensionTail
#print axioms YMGap.Continuum.SU2HeatDimensionBlockTail.dimensionTail_le_eight_blocks
