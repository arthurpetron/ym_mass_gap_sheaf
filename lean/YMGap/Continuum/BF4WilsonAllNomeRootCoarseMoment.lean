/-
# Coarse time-defect moments of the ACTUAL original root polynomial form

The root stride 2^depth is original time one. The polynomial 1-u^N therefore
has precisely the original coarse defect moments, without cancelling u or
postulating multiplicativity of a diagonal functional. Every depth, time
index and defect exponent is included; the boundary kernel is retained.
-/

import YMGap.Continuum.BF4WilsonAllNomeRootPolynomialForm

namespace YMGap.Continuum.BF4WilsonAllNomeRootCoarseMoment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyPositivePrimitive (polynomialPower complement)
open YMGap.Constructive.QPolyRootLogDifference (rootDefect rootPower)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RCPolynomialFunctional (formFrom formFrom_psub formFrom_singleton)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (meshAction mesh_add)
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy (full_mesh_time)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay (moment)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (mixedMoment mixedMoment_split)
open YMGap.Continuum.BF4WilsonAllNomeRootPolynomialForm

private theorem sub_first (a b : RC) : RCsub (RCadd a b) a = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1) (by decide)
      (fun | 0 => A.approx n | _ => B.approx n)))

private theorem coarse_defect_mul (depth : Nat) (p : Poly) :
    CoeffEqv (pmul (rootDefect (2^depth-1)) p)
      (psub p (pmul (polynomialPower complement (2^depth)) p)) := by
  have hpos : 0 < 2^depth := Nat.pow_pos (by decide)
  have hn : (2^depth-1)+1 = 2^depth := by omega
  unfold rootDefect rootPower
  rw [hn]
  exact (coeffEqv_padd_pmul_left [1]
    (pneg (polynomialPower complement (2^depth))) p).trans
    (CoeffEqv.padd (coeffEqv_pmul_one_left p)
      (coeffEqv_pscale_pmul (-1) (polynomialPower complement (2^depth)) p))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "Phi" => form hw0 hw1
local notation "M" => moment hw0 hw1
local notation "C" => mixedMoment hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- An arbitrary polynomial times u^a shifts the actual root-time index.
This is linear form algebra, not multiplication of scalar form values. -/
theorem form_power_complement_mul (depth : Nat) (x : V) (k l a : Nat) (p : Poly) :
    Phi depth x k (pmul (polynomialPower complement a) p) l =
      Phi depth x (k+a) p l := by
  induction a generalizing k with
  | zero =>
      rw [Nat.add_zero]
      exact form_coeffEqv hw0 hw1 depth x k l (coeffEqv_pmul_one_left p)
  | succ a ih =>
      change Phi depth x k (pmul (pmul complement (polynomialPower complement a)) p) l = _
      rw [form_coeffEqv hw0 hw1 depth x k l (coeffEqv_pmul_assoc _ _ _),
        form_complement, ih]
      congr 1
      omega

/-- EVERY full root stride equals the existing original completed time,
including depth zero, time zero and states in its boundary kernel. -/
theorem full_stride (depth k : Nat) (x : V) :
    meshAction hw0 hw1 depth (k*2^depth) x = T k x := by
  induction k with
  | zero =>
      rw [Nat.zero_mul]
      exact (completedTime_zero hw0 hw1 x).symm
  | succ k ih =>
      have hi : (k+1)*2^depth = 2^depth+k*2^depth := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      rw [hi, mesh_add, full_mesh_time, ih, ← completedTime_add, Nat.one_add]

private theorem form_one (depth : Nat) (x : V) (k l : Nat) :
    Phi depth x k [1] l = M depth x k l := by
  unfold form
  rw [formFrom_singleton, RCscale_one]

/-- The ORIGINAL coarse defect polynomial has the ORIGINAL mixed moments.
The induction keeps all coarse time indices, so no scalar multiplicativity
or operator inverse is needed at the successor step. -/
theorem form_coarseDefectPower (depth : Nat) (x : V) (k j : Nat) :
    Phi depth x (k*2^depth)
      (polynomialPower (rootDefect (2^depth-1)) j) 0 = C x k j := by
  induction j generalizing k with
  | zero =>
      rw [polynomialPower, form_one]
      change completedInner hw0 hw1 x (meshAction hw0 hw1 depth (k*2^depth) x) =
        completedInner hw0 hw1 x (T k x)
      rw [full_stride]
  | succ j ih =>
      change Phi depth x (k*2^depth)
        (pmul (rootDefect (2^depth-1))
          (polynomialPower (rootDefect (2^depth-1)) j)) 0 = _
      rw [form_coeffEqv hw0 hw1 depth x (k*2^depth) 0 (coarse_defect_mul depth _)]
      change formFrom (fun i => M depth x (k*2^depth) i) (psub _ _) 0 = _
      rw [formFrom_psub]
      change RCsub
        (Phi depth x (k*2^depth) (polynomialPower (rootDefect (2^depth-1)) j) 0)
        (Phi depth x (k*2^depth)
          (pmul (polynomialPower complement (2^depth))
            (polynomialPower (rootDefect (2^depth-1)) j)) 0) = _
      rw [form_power_complement_mul, ih]
      have hi : k*2^depth+2^depth = (k+1)*2^depth := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [hi, ih, mixedMoment_split, sub_first]

/-- Multiplication by the full root power is exactly ONE original time factor
in the coarse defect form, at every defect exponent. -/
theorem form_coarse_one_time (depth : Nat) (x : V) (j : Nat) :
    Phi depth x 0
      (pmul (polynomialPower complement (2^depth))
        (polynomialPower (rootDefect (2^depth-1)) j)) 0 = C x 1 j := by
  rw [form_power_complement_mul, Nat.zero_add]
  have h := form_coarseDefectPower hw0 hw1 depth x 1 j
  simpa only [Nat.one_mul] using h

#print axioms form_power_complement_mul
#print axioms full_stride
#print axioms form_coarseDefectPower
#print axioms form_coarse_one_time

end YMGap.Continuum.BF4WilsonAllNomeRootCoarseMoment
