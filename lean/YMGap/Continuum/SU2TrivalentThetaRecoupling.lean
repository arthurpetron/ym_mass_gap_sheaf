/-
# Exact rational SU(2) trivalent data, one F-move, and the theta graph

The first gauge graphs beyond bivalent cycles require trivalent intertwiner
data.  SU(2) is multiplicity-free: the trivalent invariant space has dimension
`fusionInd a b c`, hence either zero or one.

For four fundamental external labels the two admissible intermediate channels
are `0` and `2`.  In an orthonormal basis the F-move contains `sqrt 3`.  The
dimension-rescaled channel basis instead has Gram `diag(1,3)` and the exact
rational signed associator

                   [ -1/2   3/2 ]
             F  =  [  1/2   1/2 ].

This module proves constructively that `F^2 = I` and `F^T diag(1,3) F =
diag(1,3)`.  Its normalized squared kernel is exactly
`[[1/4,3/4],[3/4,1/4]]`; thus the fractional Racah normalization is derived
without an irrational scalar or a probability-only surrogate.

The first closed trivalent graph is the theta graph.  Its gauge quotient is
indexed by admissible triples `(a,b,c)`.  The unique vacuum is `(0,0,0)`.  We
construct the admissibility-plus-vacuum projector, prove it commutes with the
three-link diagonal transfer, prove link-elimination order independence, and
obtain the same uniform `(1/8)^2` squared-norm contraction on every finite
support.
-/

import YMGap.Continuum.SU2GlobalVacuumCycleQuotient
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2TrivalentThetaRecoupling

set_option maxHeartbeats 800000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PeterWeylRealWeight
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    (a * b) ≈ (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## Multiplicity-free trivalent intertwiner data -/

abbrev TrivalentLabel := Nat × (Nat × Nat)

def trivalentMultiplicity (j : TrivalentLabel) : Q' :=
  fusionInd j.1 j.2.1 j.2.2

theorem trivalentMultiplicity_zero_or_one (j : TrivalentLabel) :
    trivalentMultiplicity j = 0 ∨ trivalentMultiplicity j = 1 := by
  rcases j with ⟨a, b, c⟩
  unfold trivalentMultiplicity fusionInd
  by_cases h : fusionOK a b c
  · rw [if_pos h]; exact Or.inr rfl
  · rw [if_neg h]; exact Or.inl rfl

/-- The two fundamental strands have precisely the singlet and triplet
intermediate channels. -/
theorem fundamental_trivalent_channels :
    trivalentMultiplicity (1, 1, 0) = 1 ∧
    trivalentMultiplicity (1, 1, 1) = 0 ∧
    trivalentMultiplicity (1, 1, 2) = 1 := by decide

/-- A nontrivial theta label: three spin-one (twice-spin `2`) edges have a
unique trivalent intertwiner at each endpoint. -/
theorem theta_spin_one_admissible :
    trivalentMultiplicity (2, 2, 2) = 1 := by decide

/-! ## Exact dimension-rescaled fundamental F-move -/

abbrev RecoupleVec := Q' × Q'

def oneHalf : Q' := Q'.mkPos 1 2 (by decide)
def threeHalves : Q' := Q'.mkPos 3 2 (by decide)
def threeQuarters : Q' := Q'.mkPos 3 4 (by decide)

def recoupleGram (x y : RecoupleVec) : Q' :=
  x.1 * y.1 + Q'.ofNat 3 * (x.2 * y.2)

/-- Signed fundamental SU(2) associator in the dimension-rescaled rational
channel basis `(singlet, triplet)`.  The factored form makes the common `1/2`
normalization explicit. -/
def fundamentalFMoveAt (h : Q') (x : RecoupleVec) : RecoupleVec :=
  (h * ((-x.1) + Q'.ofNat 3 * x.2), h * (x.1 + x.2))

def fundamentalFMove (x : RecoupleVec) : RecoupleVec :=
  fundamentalFMoveAt oneHalf x

def RecoupleEq (x y : RecoupleVec) : Prop :=
  x.1 ≈ y.1 ∧ x.2 ≈ y.2

private def f0Expr (h x y : PolyExpr) : PolyExpr :=
  .mul h (.add (.neg x) (.mul (.const 3) y))

private def f1Expr (h x y : PolyExpr) : PolyExpr :=
  .mul h (.add x y)

private def ffFirstLHS : PolyExpr :=
  f0Expr (.var 0)
    (f0Expr (.var 0) (.var 1) (.var 2))
    (f1Expr (.var 0) (.var 1) (.var 2))

private def ffFirstRHS : PolyExpr :=
  .mul (.mul (.mul (.var 0) (.var 0)) (.const 4)) (.var 1)

private def ffSecondLHS : PolyExpr :=
  f1Expr (.var 0)
    (f0Expr (.var 0) (.var 1) (.var 2))
    (f1Expr (.var 0) (.var 1) (.var 2))

private def ffSecondRHS : PolyExpr :=
  .mul (.mul (.mul (.var 0) (.var 0)) (.const 4)) (.var 2)

private theorem ffFirst_normal :
    normalize ffFirstLHS = normalize ffFirstRHS := by decide

private theorem ffSecond_normal :
    normalize ffSecondLHS = normalize ffSecondRHS := by decide

private theorem fundamentalFMoveAt_twice_first (h : Q') (x : RecoupleVec) :
    (fundamentalFMoveAt h (fundamentalFMoveAt h x)).1 ≈
      ((h * h) * Q'.ofNat 4) * x.1 := by
  have H := poly_identity_of_normal_eq ffFirstLHS ffFirstRHS ffFirst_normal
    (fun i => if i = 0 then h else if i = 1 then x.1 else x.2)
  simpa [RingNormaliser.eval, ffFirstLHS, ffFirstRHS, f0Expr, f1Expr,
    fundamentalFMoveAt] using H

private theorem fundamentalFMoveAt_twice_second (h : Q') (x : RecoupleVec) :
    (fundamentalFMoveAt h (fundamentalFMoveAt h x)).2 ≈
      ((h * h) * Q'.ofNat 4) * x.2 := by
  have H := poly_identity_of_normal_eq ffSecondLHS ffSecondRHS ffSecond_normal
    (fun i => if i = 0 then h else if i = 1 then x.1 else x.2)
  simpa [RingNormaliser.eval, ffSecondLHS, ffSecondRHS, f0Expr, f1Expr,
    fundamentalFMoveAt] using H

private theorem oneHalf_square_four :
    (oneHalf * oneHalf) * Q'.ofNat 4 ≈ 1 := by decide

/-- Recoupling twice returns to the original parenthesization. -/
theorem fundamentalFMove_involutive (x : RecoupleVec) :
    RecoupleEq (fundamentalFMove (fundamentalFMove x)) x := by
  unfold RecoupleEq fundamentalFMove
  constructor
  · exact Q'.eqv_trans _ _ _ (fundamentalFMoveAt_twice_first oneHalf x)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ x.1 oneHalf_square_four)
        (Q'.one_mul_eqv x.1))
  · exact Q'.eqv_trans _ _ _ (fundamentalFMoveAt_twice_second oneHalf x)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ x.2 oneHalf_square_four)
        (Q'.one_mul_eqv x.2))

private def gramExpr (x0 x1 y0 y1 : PolyExpr) : PolyExpr :=
  .add (.mul x0 y0) (.mul (.const 3) (.mul x1 y1))

private def fGramLHS : PolyExpr :=
  gramExpr
    (f0Expr (.var 0) (.var 1) (.var 2))
    (f1Expr (.var 0) (.var 1) (.var 2))
    (f0Expr (.var 0) (.var 3) (.var 4))
    (f1Expr (.var 0) (.var 3) (.var 4))

private def fGramRHS : PolyExpr :=
  .mul (.mul (.mul (.var 0) (.var 0)) (.const 4))
    (gramExpr (.var 1) (.var 2) (.var 3) (.var 4))

private theorem fGram_normal : normalize fGramLHS = normalize fGramRHS := by decide

private theorem fundamentalFMoveAt_gram_scaled (h : Q') (x y : RecoupleVec) :
    recoupleGram (fundamentalFMoveAt h x) (fundamentalFMoveAt h y) ≈
      ((h * h) * Q'.ofNat 4) * recoupleGram x y := by
  have H := poly_identity_of_normal_eq fGramLHS fGramRHS fGram_normal
    (fun i => if i = 0 then h else if i = 1 then x.1 else
      if i = 2 then x.2 else if i = 3 then y.1 else y.2)
  simpa [RingNormaliser.eval, fGramLHS, fGramRHS, gramExpr, f0Expr, f1Expr,
    recoupleGram, fundamentalFMoveAt] using H

/-- Exact order independence of the closed four-leg block: the rational
F-move preserves the dimension-weighted Haar Gram. -/
theorem fundamentalFMove_gram_isometry (x y : RecoupleVec) :
    recoupleGram (fundamentalFMove x) (fundamentalFMove y) ≈
      recoupleGram x y := by
  unfold fundamentalFMove
  exact Q'.eqv_trans _ _ _ (fundamentalFMoveAt_gram_scaled oneHalf x y)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (recoupleGram x y) oneHalf_square_four)
      (Q'.one_mul_eqv _))

def singletChannel : RecoupleVec := (1, 0)
def tripletChannel : RecoupleVec := (0, 1)

theorem fundamentalFMove_basis_exact :
    RecoupleEq (fundamentalFMove singletChannel) ((-oneHalf), oneHalf) ∧
    RecoupleEq (fundamentalFMove tripletChannel) (threeHalves, oneHalf) := by
  unfold RecoupleEq fundamentalFMove singletChannel tripletChannel
  exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- The dimension-normalized squared F entries.  Unlike the signed rational
matrix, this is the orthonormal Racah probability kernel. -/
def fundamentalRacahProb (i j : Nat) : Q' :=
  match i, j with
  | 0, 0 => Q'.mkPos 1 4 (by decide)
  | 0, 1 => threeQuarters
  | 1, 0 => threeQuarters
  | 1, 1 => Q'.mkPos 1 4 (by decide)
  | _, _ => 0

theorem fundamentalRacahProb_exact :
    fundamentalRacahProb 0 0 ≈ Q'.mkPos 1 4 (by decide) ∧
    fundamentalRacahProb 0 1 ≈ threeQuarters ∧
    fundamentalRacahProb 1 0 ≈ threeQuarters ∧
    fundamentalRacahProb 1 1 ≈ Q'.mkPos 1 4 (by decide) := by decide

theorem fundamentalRacahProb_rows_normalized :
    fundamentalRacahProb 0 0 + fundamentalRacahProb 0 1 ≈ 1 ∧
    fundamentalRacahProb 1 0 + fundamentalRacahProb 1 1 ≈ 1 := by decide

theorem fundamentalRacahProb_columns_normalized :
    fundamentalRacahProb 0 0 + fundamentalRacahProb 1 0 ≈ 1 ∧
    fundamentalRacahProb 0 1 + fundamentalRacahProb 1 1 ≈ 1 := by decide

/-- Squaring the rational signed F coefficients with the source/target Gram
weights derives the fractional Racah kernel, including the `3/4` entries. -/
theorem fundamentalRacahProb_from_weighted_F :
    ((-oneHalf) * (-oneHalf)) ≈ fundamentalRacahProb 0 0 ∧
    (Q'.ofNat 3 * (oneHalf * oneHalf)) ≈ fundamentalRacahProb 1 0 ∧
    (threeHalves * threeHalves) ≈
      Q'.ofNat 3 * fundamentalRacahProb 0 1 ∧
    (Q'.ofNat 3 * (oneHalf * oneHalf)) ≈
      Q'.ofNat 3 * fundamentalRacahProb 1 1 := by decide

/-! ## The theta-graph gauge and vacuum quotient -/

abbrev ThetaPacket := TrivalentLabel → Q'

def thetaGlobalVacuumProject (f : ThetaPacket) : ThetaPacket
  | (0, 0, 0) => 0
  | j => f j

/-- First impose trivalent admissibility, then remove the unique all-zero
theta vacuum. -/
def thetaGaugeVacuumProject (f : ThetaPacket) (j : TrivalentLabel) : Q' :=
  trivalentMultiplicity j * thetaGlobalVacuumProject f j

theorem thetaGaugeVacuumProject_vacuum (f : ThetaPacket) :
    thetaGaugeVacuumProject f (0, 0, 0) ≈ 0 := by
  unfold thetaGaugeVacuumProject thetaGlobalVacuumProject
  exact Q'.mul_zero_eqv _

theorem thetaGaugeVacuumProject_inadmissible (f : ThetaPacket)
    (j : TrivalentLabel) (h : trivalentMultiplicity j = 0) :
    thetaGaugeVacuumProject f j ≈ 0 := by
  unfold thetaGaugeVacuumProject
  rw [h]
  exact Q'.zero_mul_eqv _

private theorem zeroOne_mul_idempotent (m x : Q')
    (h : m = 0 ∨ m = 1) : m * (m * x) ≈ m * x := by
  rcases h with h | h
  · rw [h]
    exact Q'.eqv_trans _ _ _ (Q'.zero_mul_eqv _)
      (Q'.eqv_symm (Q'.zero_mul_eqv _))
  · rw [h]
    exact Q'.mul_eqv_congr_left 1 _ _ (Q'.one_mul_eqv x)

theorem thetaGaugeVacuumProject_idempotent (f : ThetaPacket)
    (j : TrivalentLabel) :
    thetaGaugeVacuumProject (thetaGaugeVacuumProject f) j ≈
      thetaGaugeVacuumProject f j := by
  rcases j with ⟨a, b, c⟩
  cases a with
  | zero =>
      cases b with
      | zero =>
          cases c with
          | zero =>
              unfold thetaGaugeVacuumProject thetaGlobalVacuumProject
              exact Q'.eqv_refl _
          | succ c =>
              unfold thetaGaugeVacuumProject thetaGlobalVacuumProject
              exact zeroOne_mul_idempotent _ _
                (trivalentMultiplicity_zero_or_one (0, 0, c + 1))
      | succ b =>
          unfold thetaGaugeVacuumProject thetaGlobalVacuumProject
          exact zeroOne_mul_idempotent _ _
            (trivalentMultiplicity_zero_or_one (0, b + 1, c))
  | succ a =>
      unfold thetaGaugeVacuumProject thetaGlobalVacuumProject
      exact zeroOne_mul_idempotent _ _
        (trivalentMultiplicity_zero_or_one (a + 1, b, c))

def thetaEdgeLabel (j : TrivalentLabel) : Nat → Nat
  | 0 => j.1
  | 1 => j.2.1
  | 2 => j.2.2
  | _ => 0

def thetaEigenOrder (order : List Nat) (j : TrivalentLabel) : Q' :=
  eliminateLinks (fun e => eigA coupling (thetaEdgeLabel j e)) order

def thetaTransferOrder (order : List Nat) (f : ThetaPacket) : ThetaPacket :=
  fun j => thetaEigenOrder order j * f j

def thetaOrder : List Nat := [0, 1, 2]

theorem thetaEigen_order_independent (j : TrivalentLabel)
    {A B : List Nat} (h : A.Perm B) :
    thetaEigenOrder A j ≈ thetaEigenOrder B j :=
  eliminateLinks_perm (fun e => eigA coupling (thetaEdgeLabel j e)) h

theorem thetaTransfer_order_independent (f : ThetaPacket)
    (j : TrivalentLabel) {A B : List Nat} (h : A.Perm B) :
    thetaTransferOrder A f j ≈ thetaTransferOrder B f j :=
  Q'.mul_eqv_congr_right _ _ _ (thetaEigen_order_independent j h)

theorem thetaProject_transfer_commutes (order : List Nat) (f : ThetaPacket)
    (j : TrivalentLabel) :
    thetaTransferOrder order (thetaGaugeVacuumProject f) j ≈
      thetaGaugeVacuumProject (thetaTransferOrder order f) j := by
  unfold thetaTransferOrder thetaGaugeVacuumProject
  rcases j with ⟨a, b, c⟩
  cases a with
  | zero =>
      cases b with
      | zero =>
          cases c with
          | zero =>
              unfold thetaGlobalVacuumProject
              exact Q'.eqv_trans _ 0 _
                (Q'.eqv_trans _ _ _
                  (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _))
                  (Q'.mul_zero_eqv _))
                (Q'.eqv_symm (Q'.mul_zero_eqv _))
          | succ c =>
              unfold thetaGlobalVacuumProject
              ring_qeqv
      | succ b =>
          unfold thetaGlobalVacuumProject
          ring_qeqv
  | succ a =>
      unfold thetaGlobalVacuumProject
      ring_qeqv

/-! ## Uniform theta-graph contraction on finite supports -/

def thetaEigen (j : TrivalentLabel) : Q' :=
  eigA coupling j.1 *
    (eigA coupling j.2.1 * eigA coupling j.2.2)

def thetaTransfer (f : ThetaPacket) (j : TrivalentLabel) : Q' :=
  thetaEigen j * f j

theorem thetaOrder_matches_eigen (j : TrivalentLabel) :
    thetaEigenOrder thetaOrder j ≈ thetaEigen j := by
  unfold thetaEigenOrder thetaOrder thetaEdgeLabel eliminateLinks thetaEigen
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  exact Q'.mul_one_eqv _

private theorem twoEigen_nonneg (b c : Nat) :
    (0 : Q') ≤ eigA coupling b * eigA coupling c :=
  Q'.mul_nonneg _ _ (eigA_nonneg (by decide) b)
    (eigA_nonneg (by decide) c)

private theorem twoEigen_le_one (b c : Nat) :
    eigA coupling b * eigA coupling c ≤ (1 : Q') := by
  have hm := Q'.mul_le_mul_of_nonneg
    (eigA_le_one (w := coupling) (by decide) (by decide) b)
    (eigA_le_one (w := coupling) (by decide) (by decide) c)
    (by decide : (0 : Q') ≤ 1)
    (eigA_nonneg (w := coupling) (by decide) c)
  exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.one_mul_eqv 1))

private theorem thetaEigen_nonneg (j : TrivalentLabel) :
    (0 : Q') ≤ thetaEigen j :=
  Q'.mul_nonneg _ _ (eigA_nonneg (by decide) j.1)
    (twoEigen_nonneg j.2.1 j.2.2)

private theorem excitedEigen_le_eighth {s : Nat} (hs : 1 ≤ s) :
    eigA coupling s ≤ eighth :=
  Q'.le_trans' _ _ _
    (gapEdge_dominates (by decide) (by decide) hs)
    (Q'.le_of_eqv (by decide : eigA coupling 1 ≈ eighth))

private theorem thetaEigen_excited_le_eighth (j : TrivalentLabel)
    (h : j ≠ (0, 0, 0)) : thetaEigen j ≤ eighth := by
  rcases j with ⟨a, b, c⟩
  cases a with
  | succ a =>
      have hm := Q'.mul_le_mul_of_nonneg
        (excitedEigen_le_eighth (s := a + 1) (by omega))
        (twoEigen_le_one b c) (by decide : (0 : Q') ≤ eighth)
        (twoEigen_nonneg b c)
      exact Q'.le_trans' _ _ _ hm
        (Q'.le_of_eqv (Q'.mul_one_eqv eighth))
  | zero =>
      cases b with
      | succ b =>
          unfold thetaEigen
          rw [eigA_zero]
          have hm := Q'.mul_le_mul_of_nonneg
            (excitedEigen_le_eighth (s := b + 1) (by omega))
            (eigA_le_one (w := coupling) (by decide) (by decide) c)
            (by decide : (0 : Q') ≤ eighth)
            (eigA_nonneg (by decide) c)
          exact Q'.le_trans' _ _ _
            (Q'.le_trans' _ _ _
              (Q'.le_of_eqv (Q'.one_mul_eqv _)) hm)
            (Q'.le_of_eqv (Q'.mul_one_eqv eighth))
      | zero =>
          cases c with
          | zero => exact False.elim (h rfl)
          | succ c =>
              unfold thetaEigen
              exact Q'.le_trans' _ _ _
                (Q'.le_of_eqv
                  (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
                    (Q'.one_mul_eqv _)))
                (excitedEigen_le_eighth (s := c + 1) (by omega))

private theorem scaled_term_le (a b x : Q')
    (ha : (0 : Q') ≤ a) (hab : a ≤ b) (hb : (0 : Q') ≤ b) :
    (a * x) * (a * x) ≤ (b * b) * (x * x) := by
  have h1 := Q'.mul_le_mul_of_nonneg_right a b a hab ha
  have h2 := Q'.mul_le_mul_of_nonneg_left a b b hab hb
  have hs : a * a ≤ b * b := Q'.le_trans' _ _ _ h1 h2
  have hm := Q'.mul_le_mul_of_nonneg_right
    (a * a) (b * b) (x * x) hs
    (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg x)
  exact Q'.le_trans' _ ((a * a) * (x * x)) _
    (Q'.le_of_eqv (by ring_qeqv)) hm

private theorem theta_projected_term_uniform (f : ThetaPacket)
    (j : TrivalentLabel) :
    thetaTransfer (thetaGaugeVacuumProject f) j *
        thetaTransfer (thetaGaugeVacuumProject f) j ≤
      (eighth * eighth) *
        (thetaGaugeVacuumProject f j * thetaGaugeVacuumProject f j) := by
  by_cases h : j = (0, 0, 0)
  · rw [h]
    have hz := thetaGaugeVacuumProject_vacuum f
    have hl : thetaTransfer (thetaGaugeVacuumProject f) (0, 0, 0) *
        thetaTransfer (thetaGaugeVacuumProject f) (0, 0, 0) ≈ 0 := by
      unfold thetaTransfer
      exact Q'.eqv_trans _ _ _
        (q_mul_congr
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _))
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _)))
        (Q'.zero_mul_eqv 0)
    have hr : (eighth * eighth) *
        (thetaGaugeVacuumProject f (0, 0, 0) *
          thetaGaugeVacuumProject f (0, 0, 0)) ≈ 0 := by
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (q_mul_congr hz hz) (Q'.zero_mul_eqv 0)))
        (Q'.mul_zero_eqv _)
    exact Q'.le_trans' _ 0 _ (Q'.le_of_eqv hl)
      (Q'.le_of_eqv (Q'.eqv_symm hr))
  · exact scaled_term_le _ _ _ (thetaEigen_nonneg j)
      (thetaEigen_excited_le_eighth j h) (by decide)

def thetaNorm (f : ThetaPacket) : List TrivalentLabel → Q'
  | [] => 0
  | j :: support => f j * f j + thetaNorm f support

private theorem thetaNorm_termwise {f g : ThetaPacket}
    (h : ∀ j, f j * f j ≤ g j * g j) : ∀ support,
    thetaNorm f support ≤ thetaNorm g support
  | [] => Q'.le_refl' 0
  | j :: rest => Q'.add_le_add (h j) (thetaNorm_termwise h rest)

/-- **Theta-graph global gap.**  On every finite set of trivalent labels, the
admissibility-and-vacuum projected theta state contracts in squared norm by
`(1/8)^2`.  The bound is independent of support size. -/
theorem theta_global_vacuum_contraction (f : ThetaPacket)
    (support : List TrivalentLabel) :
    thetaNorm (thetaTransfer (thetaGaugeVacuumProject f)) support ≤
      (eighth * eighth) * thetaNorm (thetaGaugeVacuumProject f) support := by
  induction support with
  | nil =>
      unfold thetaNorm
      exact Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_zero_eqv _))
  | cons j rest ih =>
      unfold thetaNorm
      have hs := Q'.add_le_add (theta_projected_term_uniform f j) ih
      exact Q'.le_trans' _ _ _ hs
        (Q'.le_of_eqv (Q'.eqv_symm
          (Q'.mul_add_eqv (eighth * eighth)
            (thetaGaugeVacuumProject f j * thetaGaugeVacuumProject f j)
            (thetaNorm (thetaGaugeVacuumProject f) rest))))

private theorem thetaNorm_eqv_congr {f g : ThetaPacket}
    (h : ∀ j, f j ≈ g j) : ∀ support,
    thetaNorm f support ≈ thetaNorm g support
  | [] => Q'.eqv_refl 0
  | j :: rest => by
      unfold thetaNorm
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (q_mul_congr (h j) (h j)))
        (Q'.add_eqv_congr_left _ _ _ (thetaNorm_eqv_congr h rest))

/-- Reordering the three theta-link eliminations does not alter the projected
transferred norm. -/
theorem theta_transferred_norm_order_independent (f : ThetaPacket)
    (support : List TrivalentLabel) {A B : List Nat} (h : A.Perm B) :
    thetaNorm (thetaTransferOrder A (thetaGaugeVacuumProject f)) support ≈
      thetaNorm (thetaTransferOrder B (thetaGaugeVacuumProject f)) support :=
  thetaNorm_eqv_congr
    (fun j => thetaTransfer_order_independent (thetaGaugeVacuumProject f) j h)
    support

end YMGap.Continuum.SU2TrivalentThetaRecoupling

#print axioms YMGap.Continuum.SU2TrivalentThetaRecoupling.trivalentMultiplicity_zero_or_one
#print axioms YMGap.Continuum.SU2TrivalentThetaRecoupling.fundamentalFMove_involutive
#print axioms YMGap.Continuum.SU2TrivalentThetaRecoupling.fundamentalFMove_gram_isometry
#print axioms YMGap.Continuum.SU2TrivalentThetaRecoupling.fundamentalRacahProb_from_weighted_F
#print axioms YMGap.Continuum.SU2TrivalentThetaRecoupling.thetaGaugeVacuumProject_idempotent
#print axioms YMGap.Continuum.SU2TrivalentThetaRecoupling.thetaProject_transfer_commutes
#print axioms YMGap.Continuum.SU2TrivalentThetaRecoupling.theta_global_vacuum_contraction
#print axioms YMGap.Continuum.SU2TrivalentThetaRecoupling.theta_transferred_norm_order_independent
