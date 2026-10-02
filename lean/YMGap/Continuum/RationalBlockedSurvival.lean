/-
# A positive rational survival floor from any finite physical slope budget

For integers C>=1 and m>=4*C, rho=1-C/m has
  rho^(m-1) >= (1/4)^(2*C).
The floor is independent of m. Split the exponent into at most 2*C
blocks of length b=floor((m-1)/(2*C))+1; each block loses at most 3/4
by the existing constructive product floor. No real reciprocal,
exponential, spectral representation or small total budget is used.
This is a rational estimate, not an inhabited Yang--Mills scaling budget.
-/

import YMGap.Continuum.TotalMajorantClose
import YMGap.Continuum.ProductFloor
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.RationalBlockedSurvival

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

def quarter : Q' := Q'.mkPos 1 4 (by decide)

theorem quarter_positive : (0 : Q') < quarter := by decide

/-- The only division is by the supplied positive integer lag. -/
def blocked_rate (C m : Nat) : Q' := 1-Q'.ofNat C*Q'.invSucc (m-1)

private def loss (C m : Nat) : Q' := Q'.ofNat C*Q'.invSucc (m-1)

private theorem loss_nonnegative (C m : Nat) : (0 : Q') ≤ loss C m :=
  Q'.mul_nonneg _ _ (by
    rw [Q'.zero_le_iff_num_nonneg]
    exact Int.natCast_nonneg C) (Q'.invSucc_nonneg (m-1))

private theorem loss_le_one (C m : Nat) (hC : 1 ≤ C) (hm : 4*C ≤ m) :
    loss C m ≤ (1 : Q') := by
  have hm1 : 1 ≤ m := by omega
  have hCm : C ≤ m := by omega
  unfold loss
  change (Q'.ofNat C*Q'.invSucc (m-1)).num*(1 : Int) ≤
    (1 : Int)*((Q'.ofNat C*Q'.invSucc (m-1)).den : Int)
  rw [Q'.mul_num_cast, Q'.mul_den_cast, Q'.invSucc_num, Q'.invSucc_den]
  change (C : Int)*1*1 ≤ 1*(1*((m-1+1 : Nat) : Int))
  simp only [Int.mul_one, Int.one_mul, Nat.sub_add_cancel hm1]
  exact Int.ofNat_le.mpr hCm

theorem blocked_rate_nonnegative (C m : Nat) (hC : 1 ≤ C) (hm : 4*C ≤ m) :
    (0 : Q') ≤ blocked_rate C m :=
  Q'.sub_nonneg_of_le (loss_le_one C m hC hm)

theorem blocked_rate_le_one (C m : Nat) (_hC : 1 ≤ C) (_hm : 4*C ≤ m) :
    blocked_rate C m ≤ (1 : Q') := by
  have h := Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (loss_nonnegative C m))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by decide : (1 : Q') + -0 ≈ 1))

private theorem sum_constant (a : Q') : ∀ n : Nat,
    ProductFloor.lossSum (fun _ => a) n ≈ Q'.ofNat n*a
  | 0 => Q'.eqv_symm (Q'.zero_mul_eqv a)
  | n+1 => by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (sum_constant a n)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (poly_identity_of_normal_eq
      (.mul (.add (.var 0) (.const 1)) (.var 1))
      (.add (.mul (.var 0) (.var 1)) (.var 1)) (by decide)
      (fun | 0 => Q'.ofNat n | _ => a))) ?_
    exact Q'.mul_eqv_congr_right _ _ a (Q'.eqv_symm (Q'.ofNat_add_eqv n 1))

private theorem product_constant (a : Q') : ∀ n : Nat,
    ProductFloor.prodOneSub (fun _ => a) n ≈ (1-a)^n
  | 0 => Q'.eqv_refl _
  | n+1 => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (product_constant a n)) (Q'.mul_comm_eqv _ _)

private def block_length (C m : Nat) : Nat := (m-1)/(2*C)+1

private theorem block_covers (C m : Nat) (hC : 1 ≤ C) :
    m-1 ≤ block_length C m*(2*C) := by
  have hd : 0 < 2*C := by omega
  have hr := Nat.mod_lt (m-1) hd
  have he := Nat.mod_add_div (m-1) (2*C)
  unfold block_length
  rw [Nat.add_mul, Nat.one_mul]
  rw [Nat.mul_comm ((m-1)/(2*C)) (2*C)]
  omega

private theorem block_budget_nat (C m : Nat) (_hC : 1 ≤ C) (hm : 4*C ≤ m) :
    4*(block_length C m*C) ≤ 3*m := by
  have he := Nat.mod_add_div (m-1) (2*C)
  have hb : 2*C*block_length C m ≤ m-1+2*C := by
    unfold block_length
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hd := Nat.mul_le_mul_left 2 hb
  have hfour : 2*(2*C*block_length C m) = 4*(block_length C m*C) := by
    calc
      2*(2*C*block_length C m) = (2*2)*(C*block_length C m) := by
        simp only [Nat.mul_assoc]
      _ = 4*(block_length C m*C) := by rw [Nat.mul_comm C (block_length C m)]
  rw [hfour] at hd
  omega

private theorem block_budget (C m : Nat) (hC : 1 ≤ C) (hm : 4*C ≤ m) :
    Q'.ofNat (block_length C m)*loss C m ≤ Q'.mkPos 3 4 (by decide) := by
  have hm1 : 1 ≤ m := by omega
  have hb := block_budget_nat C m hC hm
  unfold loss
  change (Q'.ofNat (block_length C m)*(Q'.ofNat C*Q'.invSucc (m-1))).num*4 ≤
    3*((Q'.ofNat (block_length C m)*(Q'.ofNat C*Q'.invSucc (m-1))).den : Int)
  rw [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.invSucc_num, Q'.invSucc_den]
  change ((block_length C m : Int)*((C : Int)*1))*4 ≤
    3*(1*(1*((m-1+1 : Nat) : Int)))
  simp only [Int.mul_one, Int.one_mul, Nat.sub_add_cancel hm1]
  have hc : (4 : Int)*((block_length C m : Int)*(C : Int)) ≤ 3*(m : Int) := by
    exact_mod_cast hb
  rwa [Int.mul_comm 4] at hc

private theorem one_block_floor (C m : Nat) (hC : 1 ≤ C) (hm : 4*C ≤ m) :
    quarter ≤ (blocked_rate C m)^(block_length C m) := by
  have hsum := sum_constant (loss C m) (block_length C m)
  have hbudget := Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum) (block_budget C m hC hm)
  have hneg := Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hbudget)
  have hquarter : quarter ≤ 1-ProductFloor.lossSum (fun _ => loss C m) (block_length C m) :=
    Q'.le_trans' _ _ _ (by decide : quarter ≤ 1-Q'.mkPos 3 4 (by decide)) hneg
  exact Q'.le_trans' _ _ _ hquarter
    (Q'.le_trans' _ _ _ (ProductFloor.prod_floor_weierstrass (fun _ => loss C m)
      (fun _ => loss_nonnegative C m) (fun _ => loss_le_one C m hC hm) _)
      (Q'.le_of_eqv (product_constant (loss C m) (block_length C m))))

/-- Explicit positive lag-independent floor for ANY finite integer budget C.
The hypothesis m>=4*C is a computed eventual threshold, not smallness of C. -/
theorem blocked_rate_floor (C m : Nat) (hC : 1 ≤ C) (hm : 4*C ≤ m) :
    quarter^(2*C) ≤ (blocked_rate C m)^(m-1) := by
  have hblock := TotalMajorantClose.pow_le_pow_base (Q'.le_of_lt quarter_positive)
    (one_block_floor C m hC hm) (2*C)
  have hpin := TotalMajorantClose.pow_mul (blocked_rate C m) (block_length C m) (2*C)
  exact Q'.le_trans' _ _ _ hblock
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
      (HKConvGen.pow_base_antitone (blocked_rate_nonnegative C m hC hm)
        (blocked_rate_le_one C m hC hm) (block_covers C m hC)))

#print axioms quarter
#print axioms quarter_positive
#print axioms blocked_rate
#print axioms blocked_rate_nonnegative
#print axioms blocked_rate_le_one
#print axioms blocked_rate_floor

end YMGap.Continuum.RationalBlockedSurvival
