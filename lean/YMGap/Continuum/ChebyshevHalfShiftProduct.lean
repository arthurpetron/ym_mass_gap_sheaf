/-
# The actual finite half-shift Chebyshev product kernel

The radical-free coordinate C_n=U_n+sinCoord n satisfies
 (1-x)*C_n*C_m = T_|n-m| - T_(n+m+1).
This is exact rational polynomial algebra at every x, including both
index orders and zero indices. Difference rotation is derived from the
existing addition and Pythagorean identities, never assumed.

Consumer: the shifted/alternating theta convolution. No finite theta
addition identity, completed convolution, curvature, Haar certificate,
original-action estimate or physical scaling conclusion is asserted.
-/

import YMGap.Continuum.ChebyshevEvenSOS
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.ChebyshevHalfShiftProduct

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebyshevEvenSOS
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Natural-number distance, written without an unrelated geometry import. -/
def natDist (n m : Nat) : Nat := (n-m)+(m-n)

/-- The actual half-shift kernel coordinate, with sinCoord 0=0. -/
def halfShiftCoord (n : Nat) (x : Q') : Q' := U n x + sinCoord n x

private theorem add_congr {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a+c ≈ b+d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hab)
    (Q'.add_eqv_congr_left _ _ _ hcd)

/-- C_n=T_n+(x+1)*S_n, from the existing one-step sine rotation. -/
theorem halfShiftCoord_rotation (n : Nat) (x : Q') :
    halfShiftCoord n x ≈ T n x + (x+1)*sinCoord n x :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (sinCoord_succ_rotation n x))
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.mul (.var 1) (.var 2))) (.var 2))
      (.add (.var 0) (.mul (.add (.var 1) (.const 1)) (.var 2)))
      (by decide) (fun | 0 => T n x | 1 => x | _ => sinCoord n x))

private theorem difference_rotation_ordered (m d : Nat) (x : Q') :
    T d x ≈ T m x*T (m+d) x +
      (1 + -(x*x))*(sinCoord m x*sinCoord (m+d) x) := by
  have h := rotation_add m d x
  have hsub : T m x*T (m+d) x +
      (1 + -(x*x))*(sinCoord m x*sinCoord (m+d) x) ≈
      T m x*(T m x*T d x + -((1 + -(x*x))*(sinCoord m x*sinCoord d x))) +
      (1 + -(x*x))*(sinCoord m x*
        (sinCoord m x*T d x + T m x*sinCoord d x)) :=
    add_congr (Q'.mul_eqv_congr_left _ _ _ h.1)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ h.2))
  have hring :
      T m x*(T m x*T d x + -((1 + -(x*x))*(sinCoord m x*sinCoord d x))) +
      (1 + -(x*x))*(sinCoord m x*
        (sinCoord m x*T d x + T m x*sinCoord d x)) ≈
      (T m x*T m x + (1 + -(x*x))*(sinCoord m x*sinCoord m x))*T d x :=
    poly_identity_of_normal_eq
      (.add
        (.mul (.var 1) (.add (.mul (.var 1) (.var 3))
          (.neg (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))
            (.mul (.var 2) (.var 4))))))
        (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))
          (.mul (.var 2) (.add (.mul (.var 2) (.var 3)) (.mul (.var 1) (.var 4))))))
      (.mul (.add (.mul (.var 1) (.var 1))
        (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))
          (.mul (.var 2) (.var 2)))) (.var 3))
      (by decide)
      (fun | 0 => x | 1 => T m x | 2 => sinCoord m x
           | 3 => T d x | _ => sinCoord d x)
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hsub (Q'.eqv_trans _ _ _ hring
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (rotation_pythagorean m x))
      (Q'.one_mul_eqv (T d x)))))

/-- Difference rotation on both index orders, without division or a
separately supplied inverse-rotation premise. -/
theorem rotation_difference (n m : Nat) (x : Q') :
    T (natDist n m) x ≈ T n x*T m x +
      (1 + -(x*x))*(sinCoord n x*sinCoord m x) := by
  rcases Nat.le_total n m with hnm | hmn
  · have hd : natDist n m = m-n := by unfold natDist; omega
    rw [hd]
    have h := difference_rotation_ordered n (m-n) x
    rw [Nat.add_sub_of_le hnm] at h
    exact h
  · have hd : natDist n m = n-m := by unfold natDist; omega
    rw [hd]
    have h := difference_rotation_ordered m (n-m) x
    rw [Nat.add_sub_of_le hmn] at h
    exact Q'.eqv_trans _ _ _ h (add_congr (Q'.mul_comm_eqv _ _)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)))

private theorem forward_successor (n m : Nat) (x : Q') :
    T (n+m+1) x ≈
      x*(T n x*T m x + -((1 + -(x*x))*(sinCoord n x*sinCoord m x))) +
      -((1 + -(x*x))*(sinCoord n x*T m x + T n x*sinCoord m x)) :=
  Q'.eqv_trans _ _ _ (T_succ_rotation (n+m) x)
    (add_congr (Q'.mul_eqv_congr_left _ _ _ (rotation_add n m x).1)
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _ (rotation_add n m x).2)))

/-- The finite half-shift product kernel needed by the normalized odd
theta square. Valid for arbitrary rational x and all n,m, including zero. -/
theorem halfShift_product (n m : Nat) (x : Q') :
    (1 + -x)*halfShiftCoord n x*halfShiftCoord m x ≈
      T (natDist n m) x + -(T (n+m+1) x) := by
  have hleft : (1 + -x)*halfShiftCoord n x*halfShiftCoord m x ≈
      (1 + -x)*(T n x + (x+1)*sinCoord n x)*(T m x + (x+1)*sinCoord m x) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (halfShiftCoord_rotation n x)))
      (Q'.mul_eqv_congr_left _ _ _ (halfShiftCoord_rotation m x))
  have hright : T (natDist n m) x + -(T (n+m+1) x) ≈
      (T n x*T m x + (1 + -(x*x))*(sinCoord n x*sinCoord m x)) +
      -(x*(T n x*T m x + -((1 + -(x*x))*(sinCoord n x*sinCoord m x))) +
        -((1 + -(x*x))*(sinCoord n x*T m x + T n x*sinCoord m x))) :=
    add_congr (rotation_difference n m x) (Q'.neg_eqv_congr _ _ (forward_successor n m x))
  have hring :
      (1 + -x)*(T n x + (x+1)*sinCoord n x)*(T m x + (x+1)*sinCoord m x) ≈
      (T n x*T m x + (1 + -(x*x))*(sinCoord n x*sinCoord m x)) +
      -(x*(T n x*T m x + -((1 + -(x*x))*(sinCoord n x*sinCoord m x))) +
        -((1 + -(x*x))*(sinCoord n x*T m x + T n x*sinCoord m x))) :=
    poly_identity_of_normal_eq
      (.mul
        (.mul (.add (.const 1) (.neg (.var 0)))
          (.add (.var 1) (.mul (.add (.var 0) (.const 1)) (.var 3))))
        (.add (.var 2) (.mul (.add (.var 0) (.const 1)) (.var 4))))
      (.add
        (.add (.mul (.var 1) (.var 2))
          (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))
            (.mul (.var 3) (.var 4))))
        (.neg (.add
          (.mul (.var 0) (.add (.mul (.var 1) (.var 2))
            (.neg (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))
              (.mul (.var 3) (.var 4))))))
          (.neg (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))
            (.add (.mul (.var 3) (.var 2)) (.mul (.var 1) (.var 4))))))))
      (by decide)
      (fun | 0 => x | 1 => T n x | 2 => T m x | 3 => sinCoord n x | _ => sinCoord m x)
  exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_trans _ _ _ hring (Q'.eqv_symm hright))

end YMGap.Continuum.ChebyshevHalfShiftProduct

#print axioms YMGap.Continuum.ChebyshevHalfShiftProduct.natDist
#print axioms YMGap.Continuum.ChebyshevHalfShiftProduct.halfShiftCoord
#print axioms YMGap.Continuum.ChebyshevHalfShiftProduct.halfShiftCoord_rotation
#print axioms YMGap.Continuum.ChebyshevHalfShiftProduct.rotation_difference
#print axioms YMGap.Continuum.ChebyshevHalfShiftProduct.halfShift_product
