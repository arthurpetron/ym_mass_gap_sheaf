/-
# Positive-coefficient defect polynomials on the ORIGINAL Wilson completion

For D=I-T and P with nonnegative rational coefficients, the actual mixed
moments give ||P(D)x||^2 <= P(1)^2 ||x||^2. This is a coefficient-mass
estimate, not a sup-norm functional calculus for arbitrary polynomials.

Its intended consumer is the monotone polynomial iteration
H_0=0, H_(n+1)=(D+H_n^2)/2: differences have nonnegative coefficients,
so their small scalar mass controls convergence on this SAME carrier.
No lower spectral floor, different transfer, or physical mass is assumed.
-/

import YMGap.Continuum.BF4WilsonAllNomeLogPartial
import YMGap.Constructive.CRealArtanhEulerPositiveCompanion

namespace YMGap.Continuum.BF4WilsonAllNomeDefectPolynomial

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.CRealArtanhEulerPositiveCompanion (CoeffNonnegative)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail
open YMGap.Continuum.BF4WilsonAllNomeDistance

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "DP" => defectPower hw0 hw1

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (X.approx n))))

private theorem rc_scale_zero (a : RC) : RCscale 0 a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (X.approx n)))

private theorem rc_scale_add (a b : Q') (x : RC) :
    RCadd (RCscale a x) (RCscale b x) = RCscale (a+b) x := by
  refine Quotient.inductionOn x ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_symm (Q'.add_mul_eqv a b (X.approx n))))

private theorem mass_cons (a : Q') (p : Poly) :
    Q'.eqv (eval (a::p) 1) (a+eval p 1) :=
  Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv _)

theorem mass_nonnegative (p : Poly) (hp : CoeffNonnegative p) :
    (0 : Q') ≤ eval p 1 := by
  induction p with
  | nil => exact Q'.le_refl' _
  | cons a p ih =>
      exact Q'.le_trans' _ _ _
        (Q'.zero_le_add _ _ (hp 0) (ih (fun n => hp (n+1))))
        (Q'.ge_of_eqv (mass_cons a p))

/-- All mixed defect powers are bounded by the ORIGINAL input norm. -/
theorem defect_pair_bound (x : V) (i j : Nat) :
    RCle (B (DP i x) (DP j x)) (B x x) := by
  rw [defectPower_symmetric, ← defectPower_add]
  have h (n : Nat) : RCle (mixedMoment hw0 hw1 x 0 n) (B x x) := by
    induction n with
    | zero => rw [mixedMoment_zero]; exact RCle_refl _
    | succ n ih =>
        exact RCle_trans (mixedMoment_defect_decreasing hw0 hw1 x 0 n) ih
  simpa only [mixedMoment, completedTime_zero] using h (i+j)

theorem defect_pair_nonnegative (x : V) (i j : Nat) :
    RCnonneg (B (DP i x) (DP j x)) := by
  rw [defectPower_symmetric, ← defectPower_add]
  simpa only [mixedMoment, completedTime_zero] using
    mixedMoment_nonnegative hw0 hw1 x 0 (i+j)

/-- Finite coefficient-list action, with an explicit starting defect power. -/
def actionFrom : Poly → Nat → V → V
  | [], _, _ => Z
  | a::p, i, x => A (S a (DP i x)) (actionFrom p (i+1) x)

def action (p : Poly) (x : V) : V := actionFrom hw0 hw1 p 0 x

theorem actionFrom_defect_pair_bound (p : Poly) (hp : CoeffNonnegative p)
    (x : V) (i j : Nat) :
    RCle (B (actionFrom hw0 hw1 p i x) (DP j x))
      (RCscale (eval p 1) (B x x)) := by
  induction p generalizing i with
  | nil =>
      change RCle (B Z (DP j x)) (RCscale 0 (B x x))
      rw [completedInner_zero_left, rc_scale_zero]
      exact RCle_refl _
  | cons a p ih =>
      change RCle (B (A (S a (DP i x)) (actionFrom hw0 hw1 p (i+1) x)) _) _
      rw [completedInner_add_left, completedInner_smul_left]
      have h := RCadd_le_add
        (RCscale_mono (hp 0) (defect_pair_bound hw0 hw1 x i j))
        (ih (fun n => hp (n+1)) (i+1))
      simp only [coeff] at h
      rw [rc_scale_add, ← RCSignedPairBudget.scale_congr (mass_cons a p)] at h
      exact h

theorem actionFrom_pair_bound (p q : Poly)
    (hp : CoeffNonnegative p) (hq : CoeffNonnegative q) (x : V) (i j : Nat) :
    RCle (B (actionFrom hw0 hw1 p i x) (actionFrom hw0 hw1 q j x))
      (RCscale (eval p 1 * eval q 1) (B x x)) := by
  induction q generalizing j with
  | nil =>
      change RCle (B _ Z) (RCscale (eval p 1 * 0) (B x x))
      rw [completedInner_zero_right,
        RCSignedPairBudget.scale_congr (Q'.mul_zero_eqv _), rc_scale_zero]
      exact RCle_refl _
  | cons a q ih =>
      change RCle (B _ (A (S a (DP j x)) (actionFrom hw0 hw1 q (j+1) x))) _
      rw [completedInner_add_right, completedInner_smul_right]
      have h := RCadd_le_add
        (RCscale_mono (hq 0) (actionFrom_defect_pair_bound hw0 hw1 p hp x i j))
        (ih (fun n => hq (n+1)) (j+1))
      simp only [coeff] at h
      rw [RCscale_RCscale, rc_scale_add] at h
      have he : Q'.eqv (a * eval p 1 + eval p 1 * eval q 1)
          (eval p 1 * eval (a::q) 1) :=
        Q'.eqv_trans _ _ _
          (RingNormaliser.poly_identity_of_normal_eq
            (.add (.mul (.var 0) (.var 1)) (.mul (.var 1) (.var 2)))
            (.mul (.var 1) (.add (.var 0) (.var 2))) (by decide)
            (fun | 0 => a | 1 => eval p 1 | _ => eval q 1))
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (mass_cons a q)))
      rwa [RCSignedPairBudget.scale_congr he] at h

/-- The squared coefficient mass is an actual same-carrier norm bound. -/
theorem action_norm_bound (p : Poly) (hp : CoeffNonnegative p) (x : V) :
    RCle (B (action hw0 hw1 p x) (action hw0 hw1 p x))
      (RCscale (eval p 1 * eval p 1) (B x x)) :=
  actionFrom_pair_bound hw0 hw1 p p hp hp x 0 0

private theorem add_interchange (a b c d : V) :
    A (A a b) (A c d) = A (A a c) (A b d) := by
  rw [completedAdd_assoc, ← completedAdd_assoc hw0 hw1 b c d,
    completedAdd_comm hw0 hw1 b c, completedAdd_assoc hw0 hw1 c b d,
    ← completedAdd_assoc]

theorem actionFrom_padd (p q : Poly) (i : Nat) (x : V) :
    actionFrom hw0 hw1 (padd p q) i x =
      A (actionFrom hw0 hw1 p i x) (actionFrom hw0 hw1 q i x) := by
  induction p generalizing q i with
  | nil => exact (completedZero_add hw0 hw1 _).symm
  | cons a p ih =>
      cases q with
      | nil => exact (completedAdd_zero hw0 hw1 _).symm
      | cons b q =>
          change A (S (a+b) (DP i x)) (actionFrom hw0 hw1 (padd p q) (i+1) x) = _
          rw [ih, ← completedAdd_smul, add_interchange]
          rfl

private theorem smul_zero (c : Q') : S c Z = Z := by
  calc
    S c Z = S c (S 0 Z) := congrArg (S c) (completedSmul_zero hw0 hw1 Z).symm
    _ = S (c*0) Z := completedSmul_mul hw0 hw1 c 0 Z
    _ = S 0 Z := completedSmul_congr hw0 hw1 (Q'.mul_zero_eqv c) Z
    _ = Z := completedSmul_zero hw0 hw1 Z

theorem actionFrom_pscale (c : Q') (p : Poly) (i : Nat) (x : V) :
    actionFrom hw0 hw1 (pscale c p) i x = S c (actionFrom hw0 hw1 p i x) := by
  induction p generalizing i with
  | nil => exact (smul_zero hw0 hw1 c).symm
  | cons a p ih =>
      change A (S (c*a) (DP i x)) (actionFrom hw0 hw1 (pscale c p) (i+1) x) = _
      rw [ih, ← completedSmul_mul, ← completedSmul_add]
      rfl

theorem action_psub (p q : Poly) (x : V) :
    action hw0 hw1 (psub p q) x =
      completedSub hw0 hw1 (action hw0 hw1 p x) (action hw0 hw1 q x) := by
  unfold action psub pneg completedSub completedNeg
  rw [actionFrom_padd, actionFrom_pscale]

/-- Positive coefficient differences suffice; no uniform functional calculus
for arbitrary signed polynomials is asserted. -/
theorem action_distance_bound (p q : Poly) (h : CoeffNonnegative (psub p q))
    (x : V) :
    RCle (completedDist hw0 hw1 (action hw0 hw1 p x) (action hw0 hw1 q x))
      (RCscale (eval (psub p q) 1 * eval (psub p q) 1) (B x x)) := by
  rw [completedDist, ← action_psub]
  exact action_norm_bound hw0 hw1 (psub p q) h x

#print axioms defect_pair_bound
#print axioms defect_pair_nonnegative
#print axioms action_norm_bound
#print axioms action_psub
#print axioms action_distance_bound

end YMGap.Continuum.BF4WilsonAllNomeDefectPolynomial
