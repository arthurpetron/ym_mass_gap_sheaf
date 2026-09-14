/-
# An explicit all-order error for normalized falling products

For N=n+1 and 0<=k<=N, the product of (k-j)_+/N over j<r lies below
(k/N)^r and within C(r)/N of it, where C(0)=0 and C(r+1)=C(r)+r.
Every factor is rational, every truncating-natural boundary is included,
and the tolerance index is computed. This is numerical approximation
algebra; it does not assume a spectral measure or a Yang--Mills limit.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments

namespace YMGap.Continuum.BernsteinFallingProductError

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.SU2TransvectantFactorialRecurrence (tvFallingNat)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

def grid (n k : Nat) : Q' := Q'.invSucc n*Q'.ofNat k

theorem grid_nonnegative (n k : Nat) : (0 : Q')≤grid n k :=
  Q'.mul_nonneg _ _ (Q'.le_of_lt (Q'.invSucc_pos n)) (Q'.ofNat_nonneg k)

theorem grid_mono (n : Nat) {k j : Nat} (h : k≤j) : grid n k≤grid n j :=
  Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.ofNat_le_ofNat h) (Q'.le_of_lt (Q'.invSucc_pos n))

theorem grid_top (n : Nat) : Q'.eqv (grid n (n+1)) 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.ofNat_succ_mul_invSucc n)

theorem grid_le_one (n k : Nat) (hk : k≤n+1) : grid n k≤(1 : Q') :=
  Q'.le_trans' _ _ _ (grid_mono n hk) (Q'.le_of_eqv (grid_top n))

theorem grid_add (n k j : Nat) : Q'.eqv (grid n (k+j)) (grid n k+grid n j) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.ofNat_add_eqv k j)) (Q'.mul_add_eqv _ _ _)

theorem grid_loss (n k r : Nat) : grid n k≤grid n (k-r)+grid n r :=
  Q'.le_trans' _ _ _ (grid_mono n (show k≤(k-r)+r by omega)) (Q'.le_of_eqv (grid_add n _ _))

def coefficient : Nat → Nat
  | 0 => 0
  | r+1 => coefficient r+r

def error (n r : Nat) : Q' := grid n (coefficient r)

theorem error_nonnegative (n r : Nat) : (0 : Q')≤error n r := grid_nonnegative n _

theorem error_step (n r : Nat) : Q'.eqv (error n (r+1)) (error n r+grid n r) := grid_add n _ _

def product (n k : Nat) : Nat → Q'
  | 0 => 1
  | r+1 => grid n (k-r)*product n k r

theorem product_nonnegative (n k : Nat) : ∀ r, (0 : Q')≤product n k r
  | 0 => by change (0 : Q')≤1; decide
  | r+1 => Q'.mul_nonneg _ _ (grid_nonnegative n _) (product_nonnegative n k r)

theorem product_le_power (n k : Nat) : ∀ r, product n k r≤grid n k^r
  | 0 => Q'.le_refl' _
  | r+1 =>
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (grid_mono n (Nat.sub_le k r)) (product_nonnegative n k r))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (product_le_power n k r) (grid_nonnegative n k))

theorem product_le_one (n k r : Nat) (hk : k≤n+1) : product n k r≤(1 : Q') :=
  Q'.le_trans' _ _ _ (product_le_power n k r) (HKPos.pow_le_one (grid_nonnegative n k) (grid_le_one n k hk) r)

theorem product_step_error (u f a b e c : Q')
    (hu0 : (0 : Q')≤u) (hu1 : u≤1) (hb0 : (0 : Q')≤b) (hb1 : b≤1)
    (he : (0 : Q')≤e) (hc : (0 : Q')≤c) (ha : a≤b+e) (hu : u≤f+c) :
    u*a≤f*b+(e+c) := by
  have hstart := Q'.mul_le_mul_of_nonneg_left _ _ u ha hu0
  have hsplit := Q'.le_trans' _ _ _ hstart (Q'.le_of_eqv (Q'.mul_add_eqv u b e))
  have hub := Q'.mul_le_mul_of_nonneg_right _ _ b hu hb0
  have hue := Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ e hu1 he)
    (Q'.le_of_eqv (Q'.one_mul_eqv e))
  have hmid := Q'.le_trans' _ _ _ hsplit (Q'.add_le_add hub hue)
  have hcb := Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ c hb1 hc)
    (Q'.le_of_eqv (Q'.mul_one_eqv c))
  have hexpand : Q'.eqv ((f+c)*b+e) (f*b+(e+c*b)) :=
    poly_identity_of_normal_eq
      (.add (.mul (.add (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.add (.mul (.var 0) (.var 2)) (.add (.var 3) (.mul (.var 1) (.var 2)))) (by decide)
      (fun | 0 => f | 1 => c | 2 => b | _ => e)
  exact Q'.le_trans' _ _ _ hmid (Q'.le_trans' _ _ _ (Q'.le_of_eqv hexpand)
    (Q'.add_le_add_left (f*b) _ _ (Q'.add_le_add_left e _ _ hcb)))

theorem power_le_product_error (n k : Nat) (hk : k≤n+1) :
    ∀ r, grid n k^r≤product n k r+error n r
  | 0 => by
      have he : (0 : Q')≤error n 0 := error_nonnegative n 0
      exact Q'.add_le_self_of_nonneg 1 _ he
  | r+1 =>
      Q'.le_trans' _ _ _
        (product_step_error (grid n k) (grid n (k-r)) (grid n k^r) (product n k r)
          (error n r) (grid n r) (grid_nonnegative n k) (grid_le_one n k hk)
          (product_nonnegative n k r) (product_le_one n k r hk)
          (error_nonnegative n r) (grid_nonnegative n r) (power_le_product_error n k hk r)
          (grid_loss n k r))
        (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (error_step n r))))

theorem product_falling (n k : Nat) : ∀ r,
    Q'.eqv (product n k r) (Q'.invSucc n^r*Q'.ofNat (tvFallingNat k r))
  | 0 => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | r+1 => by
      have hi := Q'.mul_eqv_congr_left (grid n (k-r)) _ _ (product_falling n k r)
      have hring := poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 3) (.var 1))) (by decide)
        (fun | 0 => Q'.invSucc n | 1 => Q'.ofNat (k-r) | 2 => Q'.invSucc n^r | _ => Q'.ofNat (tvFallingNat k r))
      exact Q'.eqv_trans _ _ _ hi (Q'.eqv_trans _ _ _ hring
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (SU3CharFactor.ofNat_mul_eqv _ _))))

theorem top_power (n : Nat) : ∀ r : Nat, Q'.eqv (grid n (n+1)^r) 1
  | 0 => Q'.eqv_refl 1
  | r+1 => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (grid_top n))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 1 _ _ (top_power n r)) (Q'.one_mul_eqv 1))

theorem top_product_budget (n r : Nat) : (1 : Q')≤product n (n+1) r+error n r :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (top_power n r))) (power_le_product_error n (n+1) (Nat.le_refl _) r)

/-- A positive ceiling avoids division by zero at orders zero and one. -/
def errorCeiling (r : Nat) : Q' := Q'.ofNat (coefficient r+1)

theorem errorCeiling_positive (r : Nat) : (0 : Q')<errorCeiling r := Q'.ofNat_succ_pos _

def modulus (r : Nat) (epsilon : Q') : Nat :=
  (Q'.divPos epsilon (errorCeiling r) (errorCeiling_positive r)).den

theorem error_small (r : Nat) (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat)
    (hn : modulus r epsilon≤n) : error n r≤epsilon := by
  let d := Q'.divPos epsilon (errorCeiling r) (errorCeiling_positive r)
  have hd : (0 : Q')<d := Q'.divPos_pos _ _ _ he
  have hs : Q'.invSucc n≤d := Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn) (HalfPow.invSucc_den_le d hd)
  have hfirst := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.invSucc n)
    (Q'.ofNat_le_ofNat (Nat.le_succ (coefficient r))) (Q'.le_of_lt (Q'.invSucc_pos n))
  have hsecond := Q'.mul_le_mul_of_nonneg_right _ _ (errorCeiling r) hs
    (Q'.le_of_lt (errorCeiling_positive r))
  have hcancel : Q'.eqv (d*errorCeiling r) epsilon :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _))) (Q'.mul_one_eqv epsilon))
  exact Q'.le_trans' _ _ _ hfirst (Q'.le_trans' _ _ _ hsecond (Q'.le_of_eqv hcancel))

end YMGap.Continuum.BernsteinFallingProductError

#print axioms YMGap.Continuum.BernsteinFallingProductError.grid
#print axioms YMGap.Continuum.BernsteinFallingProductError.grid_nonnegative
#print axioms YMGap.Continuum.BernsteinFallingProductError.grid_mono
#print axioms YMGap.Continuum.BernsteinFallingProductError.grid_top
#print axioms YMGap.Continuum.BernsteinFallingProductError.grid_le_one
#print axioms YMGap.Continuum.BernsteinFallingProductError.grid_add
#print axioms YMGap.Continuum.BernsteinFallingProductError.grid_loss
#print axioms YMGap.Continuum.BernsteinFallingProductError.coefficient
#print axioms YMGap.Continuum.BernsteinFallingProductError.error
#print axioms YMGap.Continuum.BernsteinFallingProductError.error_nonnegative
#print axioms YMGap.Continuum.BernsteinFallingProductError.error_step
#print axioms YMGap.Continuum.BernsteinFallingProductError.product
#print axioms YMGap.Continuum.BernsteinFallingProductError.product_nonnegative
#print axioms YMGap.Continuum.BernsteinFallingProductError.product_le_power
#print axioms YMGap.Continuum.BernsteinFallingProductError.product_le_one
#print axioms YMGap.Continuum.BernsteinFallingProductError.product_step_error
#print axioms YMGap.Continuum.BernsteinFallingProductError.power_le_product_error
#print axioms YMGap.Continuum.BernsteinFallingProductError.product_falling
#print axioms YMGap.Continuum.BernsteinFallingProductError.top_power
#print axioms YMGap.Continuum.BernsteinFallingProductError.top_product_budget
#print axioms YMGap.Continuum.BernsteinFallingProductError.errorCeiling
#print axioms YMGap.Continuum.BernsteinFallingProductError.errorCeiling_positive
#print axioms YMGap.Continuum.BernsteinFallingProductError.modulus
#print axioms YMGap.Continuum.BernsteinFallingProductError.error_small
