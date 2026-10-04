/-
# Explicit near-one sign of the exact Wilson square coefficient

The literal two-heat-image coefficient is positive near unit nome.  This is
finite rational power arithmetic only: the numeric window is not a physical
coupling trajectory, and the credit is not uniform in the square side.
-/

import YMGap.Continuum.BondMovingQuadratic
import YMGap.Continuum.HeatKernelPos
import YMGap.Continuum.R1CornerAtoms
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2HeatExactSquareCreditWindow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Negative of the exact signed square-moment coefficient. -/
def exactSquareCredit (w : Q') (L : Nat) : Q' :=
  2*RingNormaliser.qpow w (12*L)-1-RingNormaliser.qpow w (32*L)

private theorem qpow_rg (w : Q') : ∀ n : Nat,
    RingNormaliser.qpow w n = RGTransport.qpow w n
  | 0 => rfl
  | n+1 => congrArg (fun z : Q' => z*w) (qpow_rg w n)

private theorem add_nonneg (a b : Q') (ha : (0 : Q') ≤ a)
    (hb : (0 : Q') ≤ b) : (0 : Q') ≤ a+b :=
  Q'.le_trans' _ _ _ ha (Q'.add_le_self_of_nonneg a b hb)

/-- The elementary degree-three/eight comparison retains its quadratic
Taylor overshoot instead of treating the signed coefficient as positive. -/
private theorem base_credit_lower (x : Q') (hx0 : (0 : Q') ≤ x)
    (hx1 : x ≤ (1 : Q')) :
    let d := (1 : Q')-x
    2*d-64*(d*d) ≤
      2*RingNormaliser.qpow x 3-1-RingNormaliser.qpow x 8 := by
  dsimp only
  let d := (1 : Q')-x
  let a := RingNormaliser.qpow x 3
  let b := RingNormaliser.qpow x 8
  have h8 : 8*d-(1-b) ≤ 64*(d*d) := by
    dsimp only [d, b]
    rw [qpow_rg]
    have h := BondMovingQuadratic.secondOrder_qpow hx0 hx1 8
    have hright :
        (Q'.ofNat 8*Q'.ofNat 8)*(((1 : Q')-x)*((1 : Q')-x)) ≈
          64*(((1 : Q')-x)*((1 : Q')-x)) :=
      Q'.mul_eqv_congr_right _ _ _ (by decide)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright)
  have h3 : 1-a ≤ 3*d := by
    dsimp only [d, a]
    rw [qpow_rg]
    exact R1CornerAtoms.oneSub_qpow_le hx0 hx1 3
  have he8 : (0 : Q') ≤ 64*(d*d)-(8*d-(1-b)) := Q'.sub_nonneg_of_le h8
  have he3 : (0 : Q') ≤ 3*d-(1-a) := Q'.sub_nonneg_of_le h3
  have hsum : (0 : Q') ≤
      (64*(d*d)-(8*d-(1-b)))+2*(3*d-(1-a)) :=
    add_nonneg _ _ he8 (Q'.mul_nonneg _ _ (by decide) he3)
  have hpin :
      (64*(d*d)-(8*d-(1-b)))+2*(3*d-(1-a)) ≈
        (2*a-1-b)-(2*d-64*(d*d)) :=
    poly_identity_of_normal_eq
      (.add
        (.add (.mul (.const 64) (.mul (.var 0) (.var 0)))
          (.neg (.add (.mul (.const 8) (.var 0))
            (.neg (.add (.const 1) (.neg (.var 2)))))))
        (.mul (.const 2)
          (.add (.mul (.const 3) (.var 0))
            (.neg (.add (.const 1) (.neg (.var 1)))))))
      (.add
        (.add (.add (.mul (.const 2) (.var 1)) (.neg (.const 1)))
          (.neg (.var 2)))
        (.neg (.add (.mul (.const 2) (.var 0))
          (.neg (.mul (.const 64) (.mul (.var 0) (.var 0)))))))
      (by decide) (fun | 0 => d | 1 => a | _ => b)
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hpin))

private theorem deficit_scaled_window {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (L m : Nat)
    (hwindow : ((1 : Q')-w)*Q'.ofNat (m*(4*L)) ≤ 1) :
    Q'.ofNat m*((1 : Q')-RingNormaliser.qpow w (4*L)) ≤ 1 := by
  have hb : (1 : Q')-RingNormaliser.qpow w (4*L) ≤
      Q'.ofNat (4*L)*((1 : Q')-w) := by
    rw [qpow_rg]
    exact R1CornerAtoms.oneSub_qpow_le hw0 hw1 (4*L)
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat m) hb
    (HeatKernelRGStep.zero_le_ofNat m)
  have hcast : Q'.ofNat m*Q'.ofNat (4*L) ≈ Q'.ofNat (m*(4*L)) :=
    Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv m (4*L))
  have hpin : Q'.ofNat m*(Q'.ofNat (4*L)*((1 : Q')-w)) ≈
      ((1 : Q')-w)*Q'.ofNat (m*(4*L)) :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 2) (.mul (.var 0) (.var 1)))
        (by decide) (fun
          | 0 => Q'.ofNat m
          | 1 => Q'.ofNat (4*L)
          | _ => (1 : Q')-w))
      (Q'.mul_eqv_congr_left ((1 : Q')-w) _ _ hcast)
  exact Q'.le_trans' _ _ _ hm
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin) hwindow)

private theorem power_pin (w : Q') (L k : Nat) :
    RingNormaliser.qpow (RingNormaliser.qpow w (4*L)) k ≈
      RingNormaliser.qpow w ((4*L)*k) := by
  simp only [qpow_rg]
  exact HeatKernelRGStep.qpow_qpow w (4*L) k

private theorem credit_pin (w : Q') (L : Nat) :
    let x := RingNormaliser.qpow w (4*L)
    exactSquareCredit w L ≈
      2*RingNormaliser.qpow x 3-1-RingNormaliser.qpow x 8 := by
  dsimp only
  have h3 : RingNormaliser.qpow (RingNormaliser.qpow w (4*L)) 3 ≈
      RingNormaliser.qpow w (12*L) := by
    have h := power_pin w L 3
    rwa [show (4*L)*3 = 12*L by omega] at h
  have h8 : RingNormaliser.qpow (RingNormaliser.qpow w (4*L)) 8 ≈
      RingNormaliser.qpow w (32*L) := by
    have h := power_pin w L 8
    rwa [show (4*L)*8 = 32*L by omega] at h
  unfold exactSquareCredit
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left 2 _ _ (Q'.eqv_symm h3))
      (Q'.eqv_refl (-(1 : Q'))))
    (Q'.neg_eqv_congr _ _ (Q'.eqv_symm h8))

/-- A cleared near-unit nome window makes the exact signed coefficient
nonnegative. This window depends explicitly on the tile side. -/
theorem exactSquareCredit_nonnegative_window {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (L : Nat)
    (hwindow : ((1 : Q')-w)*Q'.ofNat (128*L) ≤ 1) :
    (0 : Q') ≤ exactSquareCredit w L := by
  let x := RingNormaliser.qpow w (4*L)
  let d := (1 : Q')-x
  have hx0 : (0 : Q') ≤ x := by
    dsimp only [x]
    rw [qpow_rg]
    exact RGTransport.qpow_nonneg w (Q'.le_of_lt hw0) _
  have hx1 : x ≤ (1 : Q') := by
    dsimp only [x]
    rw [qpow_rg]
    exact HeatKernelGap.qpow_le_one (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) _
  have hd0 : (0 : Q') ≤ d := Q'.sub_nonneg_of_le hx1
  have hd32 : 32*d ≤ (1 : Q') := by
    have h := deficit_scaled_window (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
      L 32 (by simpa only [show 32*(4*L) = 128*L by omega] using hwindow)
    exact h
  have hfactor : (0 : Q') ≤ (2*d)*(1-32*d) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hd0)
      (Q'.sub_nonneg_of_le hd32)
  have hshape : 2*d-64*(d*d) ≈ (2*d)*(1-32*d) :=
    poly_identity_of_normal_eq
      (.add (.mul (.const 2) (.var 0))
        (.neg (.mul (.const 64) (.mul (.var 0) (.var 0)))))
      (.mul (.mul (.const 2) (.var 0))
        (.add (.const 1) (.neg (.mul (.const 32) (.var 0)))))
      (by decide) (fun _ => d)
  have hlower := base_credit_lower x hx0 hx1
  have hpin := credit_pin w L
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ hfactor (Q'.le_of_eqv (Q'.eqv_symm hshape)))
    (Q'.le_trans' _ _ _ hlower (Q'.ge_of_eqv hpin))

/-- In a narrower explicit window the exact square coefficient pays at
least one full first heat deficit. The credit stays scale-dependent. -/
theorem exactSquareCredit_ge_deficit_window {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (L : Nat)
    (hwindow : ((1 : Q')-w)*Q'.ofNat (256*L) ≤ 1) :
    (1 : Q')-RingNormaliser.qpow w (4*L) ≤ exactSquareCredit w L := by
  let x := RingNormaliser.qpow w (4*L)
  let d := (1 : Q')-x
  have hx0 : (0 : Q') ≤ x := by
    dsimp only [x]
    rw [qpow_rg]
    exact RGTransport.qpow_nonneg w (Q'.le_of_lt hw0) _
  have hx1 : x ≤ (1 : Q') := by
    dsimp only [x]
    rw [qpow_rg]
    exact HeatKernelGap.qpow_le_one (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) _
  have hd0 : (0 : Q') ≤ d := Q'.sub_nonneg_of_le hx1
  have hd64 : 64*d ≤ (1 : Q') :=
    deficit_scaled_window (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
      L 64 (by simpa only [show 64*(4*L) = 256*L by omega] using hwindow)
  have hfactor : (0 : Q') ≤ d*(1-64*d) :=
    Q'.mul_nonneg _ _ hd0 (Q'.sub_nonneg_of_le hd64)
  have hshape : d+d*(1-64*d) ≈ 2*d-64*(d*d) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.mul (.var 0)
        (.add (.const 1) (.neg (.mul (.const 64) (.var 0))))))
      (.add (.mul (.const 2) (.var 0))
        (.neg (.mul (.const 64) (.mul (.var 0) (.var 0)))))
      (by decide) (fun _ => d)
  have hfirst : d ≤ 2*d-64*(d*d) := Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg d _ hfactor) (Q'.le_of_eqv hshape)
  have hlower := base_credit_lower x hx0 hx1
  have hpin := credit_pin w L
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hlower (Q'.ge_of_eqv hpin))

/-- A nonempty loop side makes the narrower-window credit strictly positive.
This does not supply a uniform floor as nome or loop side changes. -/
theorem exactSquareCredit_positive_window {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (L : Nat) (hL : 0 < L)
    (hwindow : ((1 : Q')-w)*Q'.ofNat (256*L) ≤ 1) :
    (0 : Q') < exactSquareCredit w L := by
  have hpower : RingNormaliser.qpow w (4*L) < (1 : Q') := by
    rw [qpow_rg]
    have hpos : 0 < 4*L := Nat.mul_pos (by decide) hL
    have hn : 4*L = (4*L-1)+1 := by omega
    rw [hn]
    exact HeatKernelGap.qpow_succ_lt_one (Q'.le_of_lt hw0) hw1 _
  exact Q'.pos_of_lt_of_le (HKPos.one_sub_pos hpower)
    (exactSquareCredit_ge_deficit_window hw0 hw1 L hwindow)

end YMGap.Continuum.SU2HeatExactSquareCreditWindow

#print axioms YMGap.Continuum.SU2HeatExactSquareCreditWindow.exactSquareCredit
#print axioms YMGap.Continuum.SU2HeatExactSquareCreditWindow.exactSquareCredit_nonnegative_window
#print axioms YMGap.Continuum.SU2HeatExactSquareCreditWindow.exactSquareCredit_ge_deficit_window
#print axioms YMGap.Continuum.SU2HeatExactSquareCreditWindow.exactSquareCredit_positive_window
