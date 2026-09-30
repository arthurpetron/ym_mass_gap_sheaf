/-
# A depth-independent pairing modulus for the finite nested-root error

The exact finite square error remains on the original all-nome Wilson
completion.  Its coefficient mass is bounded by the original scalar root
residual, independently of nesting depth.  Supplied Cauchy representatives
provide the rational norm ceilings needed for an absolute pairing modulus.
This does not pass a square law through a limit or construct continuous time.
-/

import YMGap.Continuum.BF4WilsonAllNomeNestedRootSquareError
import YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeNestedRootErrorSmall

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity (pairing_small)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootSquareError
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
  (smallTolerance smallTolerance_pos)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "Class" => Quotient.mk (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
  (seminorm hw0 hw1 (width := width)))
local notation "Rq" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem cap_tail_small (cap epsilon : Q') (hc : (0 : Q') ≤ cap)
    (he : (0 : Q') < epsilon) (n : Nat)
    (hn : max cap.num.toNat epsilon.den ≤ n) :
    (Q'.invSucc n * Q'.invSucc n) * cap ≤ epsilon := by
  have hcap : cap * Q'.invSucc n ≤ 1 :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (ExpNeg.invSucc_le_of_le (Nat.le_trans (Nat.le_max_left _ _) hn)) hc)
      (ExpNeg.mul_invSucc_toNat_le_one cap hc)
  have heq : Q'.eqv ((Q'.invSucc n * Q'.invSucc n)*cap)
      ((cap * Q'.invSucc n)*Q'.invSucc n) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.var 1))
      (.mul (.mul (.var 1) (.var 0)) (.var 0)) (by decide)
      (fun | 0 => Q'.invSucc n | _ => cap)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hcap (Q'.invSucc_nonneg n))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
      (Q'.le_trans' _ _ _
        (ExpNeg.invSucc_le_of_le (Nat.le_trans (Nat.le_max_right _ _) hn))
        (HalfPow.invSucc_den_le epsilon he))))

/-- The cutoff is computed from both supplied norm ceilings and the requested
pairing precision, and has no nesting-depth parameter. -/
def errorPairingModulus (X Y : (D).Cauchy) (epsilon : Q') : Nat :=
  let capX := normCeiling PD X
  let delta := smallTolerance capX (normCeiling_nonnegative PD X) epsilon
  let j := max (normCeiling PD Y).num.toNat delta.den
  ComplementRootMass.tailModulus (Q'.invSucc j)

private theorem fourth_power_le_square {r v : Q'}
    (hr0 : (0 : Q') ≤ r) (hr1 : r ≤ 1)
    (hv0 : (0 : Q') ≤ v) (hrv : r ≤ v) :
    (r*r)*(r*r) ≤ v*v := by
  have hr2nonneg : (0 : Q') ≤ r*r := Q'.mul_nonneg _ _ hr0 hr0
  have hr2le1 : r*r ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg hr1 hr1 Q'.zero_le_one hr0)
      (Q'.le_of_eqv (Q'.one_mul_eqv 1))
  have hfour : (r*r)*(r*r) ≤ r*r :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hr2le1 hr2nonneg)
      (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have htwo : r*r ≤ v*v :=
    Q'.mul_le_mul_of_nonneg hrv hrv hv0 hr0
  exact Q'.le_trans' _ _ _ hfour htwo

/-- Squared norm of the error is absolutely small at the supplied original
representative, uniformly in the finite nested-root depth. -/
theorem nestedError_norm_small (k : Nat) (Y : (D).Cauchy)
    (delta : Q') (hdelta : (0 : Q') < delta) (n : Nat)
    (hn : ComplementRootMass.tailModulus
      (Q'.invSucc (max (normCeiling PD Y).num.toNat delta.den)) ≤ n) :
    RCle
      (B (BF4WilsonAllNomeDefectPolynomial.action hw0 hw1 (nestedError k n) (Class Y))
        (BF4WilsonAllNomeDefectPolynomial.action hw0 hw1 (nestedError k n) (Class Y)))
      (Rq delta) := by
  let cap := normCeiling PD Y
  let j := max cap.num.toNat delta.den
  let r := ComplementRootMass.residual n
  let v := Q'.invSucc j
  have hcap : (0 : Q') ≤ cap := normCeiling_nonnegative PD Y
  have hr0 : (0 : Q') ≤ r := ComplementRootMass.residual_nonnegative n
  have hr1 : r ≤ (1 : Q') := ComplementRootMass.residual_le_one n
  have hv0 : (0 : Q') ≤ v := Q'.invSucc_nonneg j
  have hrv : r ≤ v :=
    ComplementRootMass.residual_small (Q'.invSucc_pos j) hn
  have hcoef : (r*r)*(r*r) ≤ v*v :=
    fourth_power_le_square hr0 hr1 hv0 hrv
  have hnorm := nestedError_action_norm_bound hw0 hw1 k n (Class Y)
  have hnonneg : (0 : Q') ≤ (r*r)*(r*r) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hr0 hr0)
      (Q'.mul_nonneg _ _ hr0 hr0)
  have h := RCle_trans hnorm
    (RCscale_mono hnonneg (completedInner_diagonal_le_normCeiling PD Y))
  have hscale : RCscale ((r*r)*(r*r)) (Rq cap) = Rq (((r*r)*(r*r))*cap) :=
    Quotient.sound (CRealAlg.ofQ'_mul _ _).symm
  rw [hscale] at h
  exact RCle_trans h (leEv_le_ofQ'_of_approx_le (fun _ =>
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ cap hcoef hcap)
      (cap_tail_small cap delta hcap hdelta j (Nat.le_refl j))))

/-- The actual original pairing with the finite square-error vector is small
in both signs, with no dependence of the cutoff on nesting depth. -/
theorem nestedError_pairing_small (k : Nat) (X Y : (D).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : errorPairingModulus hw0 hw1 X Y epsilon ≤ n) :
    let e := BF4WilsonAllNomeDefectPolynomial.action hw0 hw1
      (nestedError k n) (Class Y)
    RCle (B (Class X) e) (Rq epsilon) ∧
      RCle (RCneg (B (Class X) e)) (Rq epsilon) := by
  dsimp only
  let capX := normCeiling PD X
  let delta := smallTolerance capX (normCeiling_nonnegative PD X) epsilon
  have hdelta : (0 : Q') < delta :=
    smallTolerance_pos capX (normCeiling_nonnegative PD X) he
  have hsmall := pairing_small hw0 hw1
    (BF4WilsonAllNomeDefectPolynomial.action hw0 hw1 (nestedError k n) (Class Y))
    (Class X) capX (normCeiling_nonnegative PD X) epsilon he
    (nestedError_norm_small hw0 hw1 k Y delta hdelta n hn)
    (completedInner_diagonal_le_normCeiling PD X)
  rw [completedInner_symm hw0 hw1
    (BF4WilsonAllNomeDefectPolynomial.action hw0 hw1 (nestedError k n) (Class Y))
    (Class X)] at hsmall
  exact hsmall

#print axioms errorPairingModulus
#print axioms nestedError_norm_small
#print axioms nestedError_pairing_small

end YMGap.Continuum.BF4WilsonAllNomeNestedRootErrorSmall
