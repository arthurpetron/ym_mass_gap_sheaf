/-
# Scalar dyadic schedule for the quartic selected-link budget

This nome and spin split are finite rational diagnostic parameters only.
They are not a physical lattice-spacing or Yang--Mills coupling trajectory.
-/

import YMGap.Continuum.SU2QuaternionHeatQuarticBound
import YMGap.Continuum.ReciprocalBernoulliUpper
import YMGap.Continuum.R1CornerAtoms
import YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy
import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
import YMGap.Continuum.RouteDHigherRepTail

namespace YMGap.Continuum.SU2HeatQuarticDyadicSchedule

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.HeatKernelRGStep (qpow_qpow)
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.R1CornerAtoms (oneSub_qpow_le)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy (half_power_normalizes)
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion (qpow_eqv_pow)
open YMGap.Continuum.RouteDHigherRepTail (qpow_base_mono)

local infix:50 " ≈ " => Q'.eqv

/-- Dyadic rational nome defect, with no physical-spacing interpretation. -/
def defect (m : Nat) : Q' := HalfPow.half ^ (3*m)

def nome (m : Nat) : Q' := (1 : Q') + -(defect m)

def split (m : Nat) : Nat := 2 ^ (2*m)

private theorem half_pow_num : ∀ k : Nat, (HalfPow.half^k).num = 1
  | 0 => rfl
  | k+1 => by
      change (HalfPow.half * HalfPow.half^k).num = 1
      rw [Q'.mul_num_cast, half_pow_num k]
      rfl

private theorem half_pow_den : ∀ k : Nat, (HalfPow.half^k).den = 2^k
  | 0 => rfl
  | k+1 => by
      change 2 * (HalfPow.half^k).den = 2^(k+1)
      rw [half_pow_den k, Nat.pow_succ]
      exact Nat.mul_comm 2 (2^k)

theorem defect_pos (m : Nat) : (0 : Q') < defect m := by
  unfold defect
  exact HKPos.pow_pos (by decide) _

theorem defect_le_half {m : Nat} (hm : 6 ≤ m) : defect m ≤ HalfPow.half := by
  have he : 3*m = 1 + (3*m-1) := by omega
  unfold defect
  rw [he]
  exact Q'.le_trans' _ _ _ (ExpNeg.pow_half_antitone 1 (3*m-1))
    (Q'.le_of_eqv (by decide : HalfPow.half^1 ≈ HalfPow.half))

theorem nome_pos {m : Nat} (hm : 6 ≤ m) : (0 : Q') < nome m :=
  HKPos.one_sub_pos (HKPos.q_lt_of_le_of_lt (defect_le_half hm) (by decide))

theorem nome_lt_one (m : Nat) : nome m < (1 : Q') :=
  BakryEmery.one_sub_lt_one (defect_pos m)

theorem split_ge_one (m : Nat) : 1 ≤ split m := by
  unfold split
  exact Nat.pow_pos (by decide : 0 < 2)

private theorem split_square (m : Nat) :
    split m * split m = 2^(3*m) * 2^m := by
  unfold split
  rw [← Nat.pow_add, ← Nat.pow_add]
  congr 1
  omega

private theorem block_defect (m : Nat) :
    defect m * Q'.ofNat (2^(3*m)) ≈ 1 := by
  unfold defect
  exact half_power_normalizes (3*m)

private theorem bern_block (m : Nat) :
    bernDen (defect m) (2^(3*m)) ≈ 2 := by
  unfold bernDen
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 _ _ (Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv _ _) (block_defect m))) (by decide)

private theorem half_guard_natural {m : Nat} (hm : 6 ≤ m) :
    2*(4*(split m+2)) ≤ 2^(3*m) := by
  let A := 2^m
  let S := split m
  have hA : 16 ≤ A := Nat.le_trans (by decide : 16 ≤ 2^6)
    (Nat.pow_le_pow_right (by decide) hm)
  have hS : 2 ≤ S := by
    dsimp only [S, split]
    exact Nat.le_trans (by decide : 2 ≤ 2^12)
      (Nat.pow_le_pow_right (by decide) (by omega : 12 ≤ 2*m))
  have hstep : 8*(S+2) ≤ 16*S := by omega
  have hmul : 16*S ≤ A*S := Nat.mul_le_mul_right S hA
  have hpow : A*S = 2^(3*m) := by
    dsimp only [A, S, split]
    rw [← Nat.pow_add]
    congr 1
    omega
  calc
    2*(4*(split m+2)) = 8*(S+2) := by dsimp only [S]; omega
    _ ≤ 16*S := hstep
    _ ≤ A*S := hmul
    _ = 2^(3*m) := hpow

private theorem defect_mul_guard_le_half {m : Nat} (hm : 6 ≤ m) :
    Q'.ofNat (4*(split m+2)) * defect m ≤ HalfPow.half := by
  show (Q'.ofNat (4*(split m+2)) * defect m).num * (HalfPow.half.den : Int) ≤
    HalfPow.half.num * ((Q'.ofNat (4*(split m+2)) * defect m).den : Int)
  unfold defect
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, half_pow_num, half_pow_den]
  dsimp only [HalfPow.half, Q'.mkPos_num, Q'.mkPos_den]
  push_cast
  have hnat :
      (4 * (split m + 1 + 1)) * 1 * (Q'.mkPos 1 2 (by decide)).den ≤
        1 * (1 * 2 ^ (3 * m)) := by
    simpa only [Q'.mkPos_den, Nat.mul_one, Nat.one_mul, Nat.add_assoc,
      Nat.reduceAdd, Nat.mul_comm] using half_guard_natural hm
  exact_mod_cast hnat

private theorem nome_defect_pin (m : Nat) :
    (1 : Q') + -(nome m) ≈ defect m := by
  unfold nome
  exact poly_identity_of_normal_eq
    (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
    (.var 0) (by decide) (fun _ => defect m)

/-- The selected middle spin remains in the half-strength corridor. -/
theorem half_guard {m : Nat} (hm : 6 ≤ m) :
    (1 : Q') ≤ 2*(nome m)^(4*(split m+2)) := by
  let k := 4*(split m+2)
  let x := qpow (nome m) k
  have hw0 := Q'.le_of_lt (nome_pos hm)
  have hw1 := Q'.le_of_lt (nome_lt_one m)
  have hlin : (1 : Q') + -x ≤ Q'.ofNat k * defect m :=
    Q'.le_trans' _ _ _ (oneSub_qpow_le hw0 hw1 k)
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (nome_defect_pin m)))
  have hraw : (1 : Q') + -x ≤ HalfPow.half :=
    Q'.le_trans' _ _ _ hlin (defect_mul_guard_le_half hm)
  have hadd := Q'.add_le_add_right _ _ (x + -HalfPow.half) hraw
  have hl : ((1 : Q') + -x) + (x + -HalfPow.half) ≈ HalfPow.half := by
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.add (.const 1) (.neg (.var 0)))
          (.add (.var 0) (.neg (.var 1))))
        (.add (.const 1) (.neg (.var 1)))
        (by decide) (fun | 0 => x | _ => HalfPow.half))
      (by decide : (1 : Q') + -HalfPow.half ≈ HalfPow.half)
  have hr : HalfPow.half + (x + -HalfPow.half) ≈ x := by
    exact poly_identity_of_normal_eq
      (.add (.var 1) (.add (.var 0) (.neg (.var 1)))) (.var 0)
      (by decide) (fun | 0 => x | _ => HalfPow.half)
  have hx : HalfPow.half ≤ x :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hl))
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hr))
  have htwice := Q'.mul_le_mul_of_nonneg_left _ _ 2 hx (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (1 : Q') ≈ 2*HalfPow.half))
    (Q'.le_trans' _ _ _ htwice
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left 2 _ _ (qpow_eqv_pow (nome m) k))))

private theorem qpow_nome_block_le_half {m : Nat} (hm : 6 ≤ m) :
    qpow (nome m) (2^(3*m)) ≤ HalfPow.half := by
  have hbern := oneSub_pow_mul_bernDen_le
    (Q'.le_of_lt (defect_pos m))
    (Q'.le_trans' _ _ _ (defect_le_half hm) (by decide)) (2^(3*m))
  change qpow (nome m) (2^(3*m)) * bernDen (defect m) (2^(3*m)) ≤ 1 at hbern
  have he : qpow (nome m) (2^(3*m)) * 2 ≤ 1 :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (bern_block m)))) hbern
  have hh : HalfPow.half * 2 ≈ (1 : Q') := by decide
  have hmultip : qpow (nome m) (2^(3*m)) * 2 ≤ HalfPow.half * 2 :=
    Q'.le_trans' _ _ _ he (Q'.ge_of_eqv hh)
  exact BakryEmery.le_of_mul_le_mul_right_pos (by decide) hmultip

/-- The quadratic split buys an exponentially small heat-prefix tail. -/
theorem tail_guard {m : Nat} (hm : 6 ≤ m) :
    qpow (nome m) (split m * split m) ≤ HalfPow.half^(2^m) := by
  rw [split_square]
  have hpow := qpow_base_mono
    (RGTransport.qpow_nonneg _ (Q'.le_of_lt (nome_pos hm)) (2^(3*m)))
    (qpow_nome_block_le_half hm) (2^m)
  have he := qpow_qpow (nome m) (2^(3*m)) (2^m)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm he))
    (Q'.le_trans' _ _ _ hpow
      (Q'.le_of_eqv (qpow_eqv_pow HalfPow.half (2^m))))

theorem tail_le_eighth {m : Nat} (hm : 6 ≤ m) :
    qpow (nome m) (split m * split m) ≤ Q'.mkPos 1 8 (by decide) := by
  have hm3 : 3 ≤ 2^m := Nat.le_trans (by decide : 3 ≤ 2^6)
    (Nat.pow_le_pow_right (by decide) hm)
  have he : 2^m = 3+(2^m-3) := by omega
  exact Q'.le_trans' _ _ _ (tail_guard hm)
    (Q'.le_trans' _ _ _ (by rw [he]; exact ExpNeg.pow_half_antitone 3 (2^m-3))
      (by decide))

#print axioms defect_pos
#print axioms defect_le_half
#print axioms nome_pos
#print axioms nome_lt_one
#print axioms split_ge_one
#print axioms half_guard
#print axioms tail_guard
#print axioms tail_le_eighth

end YMGap.Continuum.SU2HeatQuarticDyadicSchedule
