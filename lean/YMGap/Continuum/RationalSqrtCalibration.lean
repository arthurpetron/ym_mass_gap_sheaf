/-
# Explicit rational calibration below a positive squared margin

The Heron modulus selects an actual natural index. Dividing the input by
that positive iterate returns a rational whose square is within a factor
four of the input. No square-root witness is extracted from `Prop`.
-/

import YMGap.Constructive.Sqrt
import YMGap.Constructive.RegularCRealArith
import YMGap.Constructive.Soundness
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.RationalSqrtCalibration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private def threeHalves : Q' := Q'.mkPos 3 2 (by decide)

/-- The actual Type-level selected Heron stage. -/
def index (eta : Q') (hEta : (0 : Q') < eta) : Nat :=
  CReal.sqrtModulus eta eta hEta hEta threeHalves (by decide)

def approx (eta : Q') (hEta : (0 : Q') < eta) : Q' :=
  CReal.heronSeq eta (index eta hEta)

/-- The calibrated rational, with its constructive positive denominator. -/
def rho (eta : Q') (hEta : (0 : Q') < eta) : Q' :=
  Q'.divPos eta (approx eta hEta)
    (CReal.heronSeq_pos hEta (index eta hEta))

private theorem budget_four (eta : Q') :
    eta + (eta + eta) * threeHalves ≈ (4 : Q') * eta := by
  have hthree : threeHalves + threeHalves ≈ (3 : Q') := by decide
  have hfirst : eta + (eta + eta) * threeHalves ≈
      eta + eta * (threeHalves + threeHalves) := by
    exact poly_identity_of_normal_eq
      (.add (.var 0) (.mul (.add (.var 0) (.var 0)) (.var 1)))
      (.add (.var 0) (.mul (.var 0) (.add (.var 1) (.var 1))))
      (by decide) (fun | 0 => eta | _ => threeHalves)
  have hmiddle : eta + eta * (threeHalves + threeHalves) ≈
      eta + eta * (3 : Q') :=
    Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hthree)
  have hlast : eta + eta * (3 : Q') ≈ (4 : Q') * eta := by
    exact poly_identity_of_normal_eq
      (.add (.var 0) (.mul (.var 0) (.const 3)))
      (.mul (.const 4) (.var 0))
      (by decide) (fun _ => eta)
  exact Q'.eqv_trans _ _ _ hfirst (Q'.eqv_trans _ _ _ hmiddle hlast)

private theorem square_error (eta x : Q') :
    x * x ≈ eta + (x * x + -eta) := by
  exact poly_identity_of_normal_eq
    (.mul (.var 1) (.var 1))
    (.add (.var 0) (.add (.mul (.var 1) (.var 1)) (.neg (.var 0))))
    (by decide) (fun | 0 => eta | _ => x)

theorem approx_pos (eta : Q') (hEta : (0 : Q') < eta) :
    (0 : Q') < approx eta hEta :=
  CReal.heronSeq_pos hEta (index eta hEta)

theorem approx_sq_lower (eta : Q') (hEta : (0 : Q') < eta) :
    eta ≤ approx eta hEta * approx eta hEta :=
  CReal.heronSeq_sq_ge eta hEta (index eta hEta)

theorem approx_sq_upper (eta : Q') (hEta : (0 : Q') < eta) :
    approx eta hEta * approx eta hEta ≤ (4 : Q') * eta := by
  let x := approx eta hEta
  have herr : CReal.errAt eta (index eta hEta) ≤ (eta + eta) * threeHalves :=
    CReal.errAt_modulus_le eta eta hEta hEta threeHalves (by decide)
  change x * x + -eta ≤ (eta + eta) * threeHalves at herr
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (square_error eta x))
    (Q'.le_trans' _ _ _
      (Q'.add_le_add_left eta _ _ herr)
      (Q'.le_of_eqv (budget_four eta)))

theorem rho_pos (eta : Q') (hEta : (0 : Q') < eta) :
    (0 : Q') < rho eta hEta :=
  Q'.divPos_pos eta (approx eta hEta) (approx_pos eta hEta) hEta

private theorem ratio_square (eta : Q') (hEta : (0 : Q') < eta) :
    ((rho eta hEta * rho eta hEta) *
      (approx eta hEta * approx eta hEta)) ≈ eta * eta := by
  let r := rho eta hEta
  let x := approx eta hEta
  have hdiv : r * x ≈ eta :=
    Q'.divPos_mul_eqv eta x (approx_pos eta hEta)
  have hfirst : (r * r) * (x * x) ≈ (r * x) * (r * x) := by
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => r | _ => x)
  have hlast : (r * x) * (r * x) ≈ eta * eta :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hdiv)
      (Q'.mul_eqv_congr_left _ _ _ hdiv)
  exact Q'.eqv_trans _ _ _ hfirst hlast

theorem rho_sq_upper (eta : Q') (hEta : (0 : Q') < eta) :
    rho eta hEta * rho eta hEta ≤ eta := by
  let r := rho eta hEta
  let x := approx eta hEta
  have hrnn : (0 : Q') ≤ r * r :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt (rho_pos eta hEta))
      (Q'.le_of_lt (rho_pos eta hEta))
  have hs : (r * r) * eta ≤ eta * eta :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left eta (x * x) (r * r)
        (approx_sq_lower eta hEta) hrnn)
      (Q'.le_of_eqv (ratio_square eta hEta))
  have hcancel : eta * (r * r) ≤ eta * eta :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv eta (r * r))) hs
  exact HKConvGen.mul_le_mul_left_cancel hEta hcancel

theorem rho_sq_lower (eta : Q') (hEta : (0 : Q') < eta) :
    Q'.divPos eta 4 (by decide) ≤ rho eta hEta * rho eta hEta := by
  let r := rho eta hEta
  let x := approx eta hEta
  have hrnn : (0 : Q') ≤ r * r :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt (rho_pos eta hEta))
      (Q'.le_of_lt (rho_pos eta hEta))
  have hs : eta * eta ≤ (r * r) * ((4 : Q') * eta) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (ratio_square eta hEta))
      (Q'.mul_le_mul_of_nonneg_left (x * x) ((4 : Q') * eta) (r * r)
        (approx_sq_upper eta hEta) hrnn)
  have hrearrange : (r * r) * ((4 : Q') * eta) ≈ eta * ((r * r) * 4) := by
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.mul (.const 4) (.var 1)))
      (.mul (.var 1) (.mul (.mul (.var 0) (.var 0)) (.const 4)))
      (by decide) (fun | 0 => r | _ => eta)
  have hcancel : eta ≤ (r * r) * 4 :=
    HKConvGen.mul_le_mul_left_cancel hEta
      (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hrearrange))
  exact Q'.divPos_le_of_le_mul eta 4 (by decide) hcancel

theorem rho_lt_one (eta : Q') (hEta : (0 : Q') < eta)
    (hEta1 : eta < (1 : Q')) : rho eta hEta < (1 : Q') := by
  let r := rho eta hEta
  have hs : r * r < (1 : Q') :=
    Q'.lt_of_le_of_lt (rho_sq_upper eta hEta) hEta1
  have hcross : r.num * r.num < (r.den : Int) * (r.den : Int) := by
    have hh := hs
    change (r * r).num * (1 : Int) <
      (1 : Int) * ((r * r).den : Int) at hh
    simpa only [Int.mul_one, Int.one_mul, Q'.mul_den_cast] using hh
  have hn : (0 : Int) < r.num := Q'.num_pos_of_pos (rho_pos eta hEta)
  have hd : (0 : Int) < (r.den : Int) := by exact_mod_cast Q'.den_pos r
  have hnd : r.num < (r.den : Int) := by
    by_cases h : r.num < (r.den : Int)
    · exact h
    · have hge : (r.den : Int) ≤ r.num := by omega
      have h1 : (r.den : Int) * (r.den : Int) ≤ r.num * (r.den : Int) :=
        Int.mul_le_mul_of_nonneg_right hge (Int.le_of_lt hd)
      have h2 : r.num * (r.den : Int) ≤ r.num * r.num :=
        Int.mul_le_mul_of_nonneg_left hge (Int.le_of_lt hn)
      exact False.elim ((Int.not_le_of_gt hcross) (Int.le_trans h1 h2))
  show r.num * (1 : Int) < (1 : Int) * (r.den : Int)
  simpa only [Int.mul_one, Int.one_mul] using hnd

#print axioms index
#print axioms approx
#print axioms rho
#print axioms approx_pos
#print axioms approx_sq_lower
#print axioms approx_sq_upper
#print axioms rho_pos
#print axioms rho_sq_upper
#print axioms rho_sq_lower
#print axioms rho_lt_one

end YMGap.Continuum.RationalSqrtCalibration
