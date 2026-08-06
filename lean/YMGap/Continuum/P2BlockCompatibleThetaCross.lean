/-
Track 11.7-fusion / R3g -- theta normal form for the physical block cross.

# Result

The cancellation-preserving mode-one residual is transported to the exact
finite integer/half-integer theta coordinates.  Writing

    I_k = w_k^2 D_k,    H_k = w_k A_k,

the cross inequality is equivalent after multiplication by a positive common
factor to

    (w_k H_k) I_(k+1)^2
      <= w_(k+1)^2 I_k H_(k+1)^2.

This is the canonical target for a Pascal, Abel, or modular comparison: no
rational quotient and no unnormalized Lipschitz constant remains.

# Constructivity

Exact finite theta identities, commutative-semiring normalization, and
positive-factor cancellation.  No `Classical`, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.HarmonicThetaRepresentation
import YMGap.Continuum.P2BlockCompatibleModeOneCross

namespace YMGap.Continuum.P2BlockCompatibleThetaCross

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.P2BlockCompatibleModeOneCross
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.mul_num_cast, Q'.mul_den_cast, Int.mul_one];
             ac_rfl))

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

private theorem qpow_two_eqv (x : Q') : qpow x 2 ≈ x * x := by
  show ((1 : Q') * x) * x ≈ x * x
  exact Q'.mul_eqv_congr_right _ _ x (Q'.one_mul_eqv x)

/-- Integer-theta norm on the block-compatible schedule. -/
def blockIntegerTheta (k : Nat) : Q' :=
  integerThetaSum (blockWeight k) (blockNcut k)

/-- Half-integer-theta numerator on the block-compatible schedule. -/
def blockHalfTheta (k : Nat) : Q' :=
  halfThetaSum (blockWeight k) (blockNcut k)

theorem blockModeOneDen_theta_eqv (k : Nat) :
    (blockWeight k * blockWeight k) * blockModeOneDen k ≈
      blockIntegerTheta k := by
  have h := coordNormSq_theta_eqv (blockWeight k) (blockNcut k)
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (blockModeOneDen k)
      (Q'.eqv_symm (qpow_two_eqv (blockWeight k))))
    h

theorem blockModeOneNum_theta_eqv (k : Nat) :
    blockWeight k * blockModeOneNum k ≈ blockHalfTheta k :=
  adjCorr_theta_eqv (blockWeight k) (blockNcut k)

/-- Exact finite-theta residual from the first scale not covered by the four
kernel-checked head cells. -/
structure BlockCompatibleP2ThetaCrossTail : Type where
  cross : forall k, 4 <= k ->
    (blockWeight k * blockHalfTheta k) *
        (blockIntegerTheta (k + 1) * blockIntegerTheta (k + 1)) <=
      (blockWeight (k + 1) * blockWeight (k + 1)) *
        (blockIntegerTheta k *
          (blockHalfTheta (k + 1) * blockHalfTheta (k + 1)))

/-- The theta residual compiles to the cancellation-preserving adjacent-
correlation/norm cross product. -/
def BlockCompatibleP2ThetaCrossTail.toModeOneCrossTail
    (T : BlockCompatibleP2ThetaCrossTail) :
    BlockCompatibleP2ModeOneCrossTail where
  cross := fun k hk => by
    let w0 := blockWeight k
    let w1 := blockWeight (k + 1)
    let A0 := blockModeOneNum k
    let D0 := blockModeOneDen k
    let A1 := blockModeOneNum (k + 1)
    let D1 := blockModeOneDen (k + 1)
    let H0 := blockHalfTheta k
    let I0 := blockIntegerTheta k
    let H1 := blockHalfTheta (k + 1)
    let I1 := blockIntegerTheta (k + 1)
    let S := (w0 * w0) * ((w1 * w1) * (w1 * w1))
    have hA0 : w0 * A0 ≈ H0 := blockModeOneNum_theta_eqv k
    have hD0 : (w0 * w0) * D0 ≈ I0 := blockModeOneDen_theta_eqv k
    have hA1 : w1 * A1 ≈ H1 := blockModeOneNum_theta_eqv (k + 1)
    have hD1 : (w1 * w1) * D1 ≈ I1 :=
      blockModeOneDen_theta_eqv (k + 1)
    have hleftRearrange :
        S * (A0 * (D1 * D1)) ≈
          (w0 * (w0 * A0)) *
            (((w1 * w1) * D1) * ((w1 * w1) * D1)) := by
      dsimp only [S]
      ring_qeqv
    have hleftTheta :
        (w0 * (w0 * A0)) *
            (((w1 * w1) * D1) * ((w1 * w1) * D1)) ≈
          (w0 * H0) * (I1 * I1) :=
      mul_eqv_both
        (Q'.mul_eqv_congr_left w0 _ _ hA0)
        (mul_eqv_both hD1 hD1)
    have hleft :
        S * (A0 * (D1 * D1)) ≈
          (w0 * H0) * (I1 * I1) :=
      Q'.eqv_trans _ _ _ hleftRearrange hleftTheta
    have hrightRearrange :
        S * (D0 * (A1 * A1)) ≈
          ((w0 * w0) * D0) *
            (((w1 * A1) * (w1 * A1)) * (w1 * w1)) := by
      dsimp only [S]
      ring_qeqv
    have hrightTheta :
        ((w0 * w0) * D0) *
            (((w1 * A1) * (w1 * A1)) * (w1 * w1)) ≈
          I0 * ((H1 * H1) * (w1 * w1)) :=
      mul_eqv_both hD0
        (mul_eqv_both (mul_eqv_both hA1 hA1) (Q'.eqv_refl _))
    have hrightFinal :
        I0 * ((H1 * H1) * (w1 * w1)) ≈
          (w1 * w1) * (I0 * (H1 * H1)) := by
      ring_qeqv
    have hright :
        S * (D0 * (A1 * A1)) ≈
          (w1 * w1) * (I0 * (H1 * H1)) :=
      Q'.eqv_trans _ _ _ hrightRearrange
        (Q'.eqv_trans _ _ _ hrightTheta hrightFinal)
    have htheta :
        (w0 * H0) * (I1 * I1) <=
          (w1 * w1) * (I0 * (H1 * H1)) := by
      simpa only [w0, w1, H0, I0, H1, I1] using T.cross k hk
    have hscaled :
        S * (A0 * (D1 * D1)) <= S * (D0 * (A1 * A1)) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
        (Q'.le_trans' _ _ _ htheta (Q'.ge_of_eqv hright))
    have hS : (0 : Q') < S := by
      dsimp only [S, w0, w1]
      exact Q'.mul_pos
        (Q'.mul_pos (blockWeight_pos k) (blockWeight_pos k))
        (Q'.mul_pos
          (Q'.mul_pos (blockWeight_pos (k + 1)) (blockWeight_pos (k + 1)))
          (Q'.mul_pos (blockWeight_pos (k + 1)) (blockWeight_pos (k + 1))))
    exact Q'.le_of_mul_le_mul_left hscaled hS

#print axioms blockModeOneDen_theta_eqv
#print axioms blockModeOneNum_theta_eqv
#print axioms BlockCompatibleP2ThetaCrossTail.toModeOneCrossTail

end YMGap.Continuum.P2BlockCompatibleThetaCross
