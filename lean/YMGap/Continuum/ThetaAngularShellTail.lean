/-
# Explicit geometric tail for derivative-weighted Gaussian shells

The actual shell majorant `16*T^3*w^(T^2)` has a half-ratio after an
explicit nome-dependent onset. This leaf only packages that scalar tail and
its rational/Nat modulus; it is not an angular identity, curvature ceiling,
or operator estimate.
-/

import YMGap.Continuum.ChebTFwdBoundClose
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.ThetaAngularShellTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.ChebTFwdBoundClose

local infix:50 " ≈ " => Q'.eqv

def sixteenth : Q' := Q'.mkPos 1 16 (by decide)

/-- The `T`-th derivative-weighted Gaussian shell. -/
def shellTerm (w : Q') (T : Nat) : Q' :=
  16 * Q'.ofNat (T*T*T) * w^(T*T)

/-- Explicit onset at which the Gaussian exponent forces the next shell
ratio below one half. -/
def shellOnset (w : Q') : Nat := max 1 (powBaseCutoff w sixteenth)

private def shellMajorant (n : Nat) : Nat := (n+1)*(n+1)*(n+1)

private theorem shellMajorant_ratio (n : Nat) :
    shellMajorant (n+1) ≤ 8 * shellMajorant n := by
  let m := n+1
  have hm : m+1 ≤ 2*m := by omega
  have hp := Nat.pow_le_pow_left hm 3
  have he : (2*m)^3 = 8*m^3 := by
    calc
      (2*m)^3 = (2*m)*(2*m)*(2*m) := by simp [Nat.pow_succ]
      _ = (2*2*2)*(m*m*m) := by ac_rfl
      _ = 8*(m*m*m) := by rw [show 2*2*2 = 8 by decide]
      _ = 8*m^3 := by simp [Nat.pow_succ]
  have hleft : shellMajorant (n+1) = (m+1)^3 := by
    dsimp [shellMajorant, m]
    simp [Nat.pow_succ]
  have hright : shellMajorant n = m^3 := by
    dsimp [shellMajorant, m]
    simp [Nat.pow_succ]
  calc
    shellMajorant (n+1) = (m+1)^3 := hleft
    _ ≤ (2*m)^3 := hp
    _ = 8*shellMajorant n := by rw [he, hright]

private theorem shellTerm_eq_fCoef {w : Q'} {T : Nat} (hT : 1 ≤ T) :
    shellTerm w T ≈ 16 * fCoef w shellMajorant (T-1) := by
  have hi : T-1+1 = T := by omega
  unfold shellTerm
  unfold fCoef shellMajorant
  rw [hi]
  exact poly_identity_of_normal_eq
    (.mul (.mul (.const 16) (.var 0)) (.var 1))
    (.mul (.const 16) (.mul (.var 1) (.var 0)))
    (by decide) (fun
      | 0 => Q'.ofNat (T*T*T)
      | _ => w^(T*T))

private theorem shellTerm_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (T : Nat) :
    (0 : Q') ≤ shellTerm w T := by
  unfold shellTerm
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide) (ofNat_nonneg (T*T*T)))
    (Q'.pow_nonneg w hw (T*T))

private theorem half_double_eqv (t : Q') : HalfPow.half * (t+t) ≈ t := by
  have hd : (HalfPow.half+HalfPow.half) ≈ (1 : Q') := by decide
  exact Q'.eqv_trans _ _ _ (Q'.mul_add_eqv HalfPow.half t t)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv HalfPow.half HalfPow.half t))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ t hd) (Q'.one_mul_eqv t)))

/-- One shell step contracts by one half once the onset has been crossed. -/
theorem shellTerm_succ_le_half {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (T : Nat) (hT : shellOnset w ≤ T) :
    shellTerm w (T+1) ≤ HalfPow.half * shellTerm w T := by
  have hT1 : 1 ≤ T := Nat.le_trans (Nat.le_max_left _ _) hT
  have hcut : powBaseCutoff w sixteenth ≤ T := Nat.le_trans (Nat.le_max_right _ _) hT
  have hsmall : w^(2*T+1) ≤ sixteenth := by
    exact Q'.le_trans' _ _ _
      (pow_base_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) (by omega))
      (pow_base_le_cutoff hw0 hw1
        (CReal.pos_of_num_pos (by decide)))
  have hcoeff : w^(2*(T-1)+3) * Q'.ofNat 8 ≤ HalfPow.half := by
    rw [show 2*(T-1)+3 = 2*T+1 by omega]
    have hmul := Q'.mul_le_mul_of_nonneg_right _ _ _ hsmall
      (by decide : (0 : Q') ≤ Q'.ofNat 8)
    have hpin : sixteenth * Q'.ofNat 8 ≈ HalfPow.half := by decide
    exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hpin)
  have hratioNat : ∀ n, shellMajorant (n+1) ≤ 8*shellMajorant n := shellMajorant_ratio
  have hstep := step_ratio hw0 shellMajorant 8 hratioNat (T-1)
  have hfnn : (0 : Q') ≤ fCoef w shellMajorant (T-1) :=
    fCoef_nonneg hw0 shellMajorant (T-1)
  have hcontract : fCoef w shellMajorant ((T-1)+1) ≤
      HalfPow.half * fCoef w shellMajorant (T-1) := by
    have hmul := Q'.mul_le_mul_of_nonneg_right _ _ _ hcoeff hfnn
    exact Q'.le_trans' _ _ _ hstep hmul
  have hsuccEq : shellTerm w (T+1) ≈ 16 * fCoef w shellMajorant ((T-1)+1) := by
    have hidx : (T+1)-1 = (T-1)+1 := by omega
    have h := shellTerm_eq_fCoef (w := w) (T := T+1) (by omega)
    simpa only [hidx] using h
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ 16 hcontract (by decide)
  have hfactor : 16 * (HalfPow.half * fCoef w shellMajorant (T-1)) ≈
      HalfPow.half * (16 * fCoef w shellMajorant (T-1)) :=
    poly_identity_of_normal_eq
      (.mul (.const 16) (.mul (.var 1) (.var 0)))
      (.mul (.var 1) (.mul (.const 16) (.var 0)))
      (by decide) (fun
        | 0 => fCoef w shellMajorant (T-1)
        | _ => HalfPow.half)
  have hcurrEq : shellTerm w T ≈ 16 * fCoef w shellMajorant (T-1) :=
    shellTerm_eq_fCoef hT1
  have hcurrScaled : HalfPow.half * (16 * fCoef w shellMajorant (T-1)) ≈
      HalfPow.half * shellTerm w T :=
    Q'.mul_eqv_congr_left HalfPow.half _ _ (Q'.eqv_symm hcurrEq)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsuccEq)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hfactor hcurrScaled)))

/-- Every finite tail starting after the explicit onset is bounded by twice
its first shell. -/
theorem shellTail_le_two {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (L d : Nat) (hL : shellOnset w ≤ L) :
    finSum (fun j => shellTerm w (L+j)) d ≤ 2*shellTerm w L := by
  have hdom : ∀ j, shellTerm w (L+(j+1)) ≤
      HalfPow.half * shellTerm w (L+j) := by
    intro j
    have hi : L+(j+1) = (L+j)+1 := by omega
    rw [hi]
    exact shellTerm_succ_le_half hw0 hw1 (L+j) (by omega)
  have hH : (0 : Q') ≤ shellTerm w L + shellTerm w L :=
    Q'.le_trans' _ _ _ (shellTerm_nonneg (Q'.le_of_lt hw0) L)
      (Q'.add_le_self_of_nonneg _ _ (shellTerm_nonneg (Q'.le_of_lt hw0) L))
  have hrec : shellTerm w L + HalfPow.half*(shellTerm w L+shellTerm w L) ≤
      shellTerm w L+shellTerm w L :=
    Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ (half_double_eqv (shellTerm w L)))
  have hgeom := CharacterTail.geom_series_le (fun j => shellTerm w (L+j))
    (shellTerm w L) HalfPow.half (shellTerm w L+shellTerm w L)
    (Q'.le_of_lt ThetaSeriesC1Close.half_pos) hH (Q'.le_refl' _)
    hdom hrec d
  have hdouble : shellTerm w L + shellTerm w L ≈ 2*shellTerm w L :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
      (by decide) (fun _ => shellTerm w L)
  exact Q'.le_trans' _ _ _ hgeom (Q'.le_of_eqv hdouble)

/-- A tolerance-to-shell ratio, retained as rational data. -/
def shellTolerance (w epsilon : Q') : Q' :=
  HKConv.divPos epsilon (2*shellTerm w (shellOnset w))

/-- Explicit later cutoff for the derivative-weighted shell tail. -/
def shellTailCutoff (w epsilon : Q') : Nat :=
  shellOnset w + powBaseCutoff HalfPow.half (shellTolerance w epsilon)

private theorem shellAtOnset_pos {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') < shellTerm w (shellOnset w) := by
  have hL : 1 ≤ shellOnset w := Nat.le_max_left _ _
  have hcube : 0 < shellOnset w * shellOnset w * shellOnset w :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  unfold shellTerm
  apply Q'.mul_pos
  · exact Q'.mul_pos (by decide) (CReal.pos_of_num_pos (by
      rw [Q'.ofNat_num_cast]
      exact_mod_cast hcube))
  · exact HKPos.pow_pos hw0 _

theorem shellTolerance_pos {w epsilon : Q'}
    (he : (0 : Q') < epsilon) : (0 : Q') < shellTolerance w epsilon :=
  HKConv.divPos_pos (CReal.num_pos_of_pos he)

private theorem shellTolerance_payment {w epsilon : Q'}
    (hw0 : (0 : Q') < w) :
    shellTolerance w epsilon * (2*shellTerm w (shellOnset w)) ≈ epsilon :=
  HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (by
    exact HKPos.q_mul_pos (by decide : (0 : Q') < 2) (shellAtOnset_pos hw0)))

/-- The explicit cutoff pays any requested epsilon for every finite later
tail. The bound is uniform in all angular data represented by the shell. -/
theorem shellTail_le_epsilon {w epsilon : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (he : (0 : Q') < epsilon)
    (N d : Nat) (hN : shellTailCutoff w epsilon ≤ N) :
    finSum (fun j => shellTerm w (N+j)) d ≤ epsilon := by
  have hOn : shellOnset w ≤ N := by
    unfold shellTailCutoff at hN
    omega
  have hk : powBaseCutoff HalfPow.half (shellTolerance w epsilon) ≤ N-shellOnset w := by
    unfold shellTailCutoff at hN
    omega
  have hgeom := CharacterTail.geom_dom (fun j => shellTerm w (shellOnset w+j))
    (shellTerm w (shellOnset w)) HalfPow.half
    (Q'.le_of_lt ThetaSeriesC1Close.half_pos)
    (Q'.le_refl' _) (fun j => by
      change shellTerm w (shellOnset w+(j+1)) ≤
        HalfPow.half * shellTerm w (shellOnset w+j)
      have hidx : shellOnset w+(j+1) = (shellOnset w+j)+1 := by omega
      rw [hidx]
      exact shellTerm_succ_le_half hw0 hw1 (shellOnset w+j) (by omega))
    (N-shellOnset w)
  have hshift : shellOnset w+(N-shellOnset w)=N := Nat.add_sub_of_le hOn
  have hfirst : shellTerm w N ≤ shellTerm w (shellOnset w)*
      HalfPow.half^(N-shellOnset w) := by
    simpa only [hshift] using hgeom
  have hpow : HalfPow.half^(N-shellOnset w) ≤ shellTolerance w epsilon :=
    Q'.le_trans' _ _ _
      (pow_base_antitone (Q'.le_of_lt ThetaSeriesC1Close.half_pos)
        (by decide : HalfPow.half ≤ (1 : Q')) hk)
      (pow_base_le_cutoff ThetaSeriesC1Close.half_pos
        (by decide : HalfPow.half < (1 : Q'))
        (shellTolerance_pos he))
  have htail := shellTail_le_two hw0 hw1 N d (by omega)
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _
    (2*shellTerm w (shellOnset w)) hpow
    (Q'.le_of_lt (HKPos.q_mul_pos (by decide) (shellAtOnset_pos hw0)))
  have htarget : (2*shellTerm w (shellOnset w))*shellTolerance w epsilon ≈ epsilon :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (shellTolerance_payment hw0)
  have hfirstBound : 2*shellTerm w N ≤
      (2*shellTerm w (shellOnset w))*HalfPow.half^(N-shellOnset w) := by
    have hm := Q'.mul_le_mul_of_nonneg_left _ _ 2 hfirst (by decide)
    exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.mul (.const 2) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.const 2) (.var 0)) (.var 1))
        (by decide) (fun
          | 0 => shellTerm w (shellOnset w)
          | _ => HalfPow.half^(N-shellOnset w))))
  exact Q'.le_trans' _ _ _ htail
    (Q'.le_trans' _ _ _ hfirstBound
      (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv htarget)))

end YMGap.Continuum.ThetaAngularShellTail

#print axioms YMGap.Continuum.ThetaAngularShellTail.shellTerm_succ_le_half
#print axioms YMGap.Continuum.ThetaAngularShellTail.shellTail_le_two
#print axioms YMGap.Continuum.ThetaAngularShellTail.shellTail_le_epsilon
#print axioms YMGap.Continuum.ThetaAngularShellTail.shellTolerance_pos
#print axioms YMGap.Continuum.ThetaAngularShellTail.shellTerm
#print axioms YMGap.Continuum.ThetaAngularShellTail.shellOnset
#print axioms YMGap.Continuum.ThetaAngularShellTail.shellTolerance
#print axioms YMGap.Continuum.ThetaAngularShellTail.shellTailCutoff
