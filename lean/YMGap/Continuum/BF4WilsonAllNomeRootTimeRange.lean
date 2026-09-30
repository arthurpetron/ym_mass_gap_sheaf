/-
# Explicit original time-range witnesses for every fixed-depth root image

The finite root polynomial splits into its scalar mass times the input
plus an actual T(1)-image. Its mass tends to zero with the existing
fixed-depth residual modulus. Combining this error with the original
root-row limit constructs a range witness, without a transfer inverse
or a new carrier. No convergence uniform in root depth is assumed.
-/

import YMGap.Continuum.BF4WilsonAllNomePolynomialTimeRange
import YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility
import YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure

namespace YMGap.Continuum.BF4WilsonAllNomeRootTimeRange

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.QPoly
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomePolynomialTimeRange
open YMGap.Continuum.BF4WilsonAllNomeNestedRootSquareError (rootPolynomial)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root finiteRoot)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility
  (rootRows rootRows_point limit_rootRows)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure
  (RangeLimit quarter quarter_positive four_quarters)
open YMGap.Continuum.ComplementRootNestedMass
  (residual residual_nonnegative residual_le_one residualModulus residual_small)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (linearTolerance linearTolerance_pos linearTolerance_budget)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "P" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "R" => root hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

theorem rootPolynomial_mass (k n : Nat) :
    Q'.eqv (eval (rootPolynomial k n) 1) (residual k n) :=
  Q'.eqv_trans _ _ _ (eval_psub _ _ _)
    (q_add_congr (by decide : Q'.eqv (eval ([1] : Poly) 1) 1) (Q'.eqv_refl _))

def rootPreimage (k n : Nat) (X : (D).Cauchy) : (D).Cauchy :=
  preimageRepresentative hw0 hw1 (rootPolynomial k n) X

theorem rootPreimage_error (k n : Nat) (X : (D).Cauchy) :
    dist (T 1 (Class (rootPreimage hw0 hw1 k n X)))
      (finiteRoot hw0 hw1 k n (Class X)) =
      RCscale (residual k n * residual k n) (B (Class X) (Class X)) := by
  unfold rootPreimage
  rw [preimageRepresentative_pin]
  change dist (T 1 (preimage hw0 hw1 (rootPolynomial k n) (Class X)))
    (BF4WilsonAllNomeDefectPolynomial.action hw0 hw1 (rootPolynomial k n) (Class X)) = _
  rw [polynomial_time_error]
  exact RCSignedPairBudget.scale_congr
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (rootPolynomial_mass k n))
      (Q'.mul_eqv_congr_left _ _ _ (rootPolynomial_mass k n))) _

def residualTolerance (X : (D).Cauchy) (e : Q') : Q' :=
  linearTolerance (normCeiling P X) (normCeiling_nonnegative P X) e

theorem rootPreimage_small (k : Nat) (X : (D).Cauchy) (e : Q') (he : (0 : Q') < e)
    (n : Nat) (hn : residualModulus k (residualTolerance hw0 hw1 X e) ≤ n) :
    RCle (dist (T 1 (Class (rootPreimage hw0 hw1 k n X)))
      (finiteRoot hw0 hw1 k n (Class X))) (rat e) := by
  rw [rootPreimage_error]
  let cap := normCeiling P X
  have hc : (0 : Q') ≤ cap := normCeiling_nonnegative P X
  let eta := residualTolerance hw0 hw1 X e
  have heTa : (0 : Q') < eta := linearTolerance_pos cap hc he
  have hr := residual_small k eta heTa n hn
  have hrr : residual k n * residual k n ≤ eta :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (residual_le_one k n) (residual_nonnegative k n))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) hr)
  have hb : (residual k n * residual k n) * cap ≤ e :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hrr hc)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv eta cap))
        (linearTolerance_budget cap hc he))
  exact RCle_trans
    (RCscale_mono (SumOfSquares.q_mul_self_nonneg (residual k n))
      (completedInner_diagonal_le_normCeiling P X))
    (leEv_le_ofQ'_of_approx_le (fun _ => hb))

/-- A concrete range witness for each fixed root depth, retaining both
the root approximation and scalar mass moduli in its all-tail cutoff. -/
def rootRange (k : Nat) (X : (D).Cauchy) : RangeLimit hw0 hw1 (R k (Class X)) where
  preimage := fun n => rootPreimage hw0 hw1 k n X
  modulus := fun e => max (limitRate hw0 hw1 (rootRows hw0 hw1 k X) (quarter e))
    (residualModulus k (residualTolerance hw0 hw1 X (quarter e)))
  bound := by
    intro e he n hn
    let delta := quarter e
    have hd : (0 : Q') < delta := quarter_positive he
    have hfirst := rootPreimage_small hw0 hw1 k X delta hd n
      (Nat.le_trans (Nat.le_max_right _ _) hn)
    have hsecond := limit_bound hw0 hw1 (rootRows hw0 hw1 k X) delta hd n
      (Nat.le_trans (Nat.le_max_left _ _) hn)
    rw [rootRows_point,limit_rootRows] at hsecond
    have h := RCle_trans (completedDist_triangle hw0 hw1 _
      (finiteRoot hw0 hw1 k n (Class X)) (R k (Class X)))
      (RCadd_le_add (RCadd_le_add hfirst hfirst) (RCadd_le_add hsecond hsecond))
    rwa [four_quarters] at h

#print axioms rootPolynomial_mass
#print axioms rootPreimage
#print axioms rootPreimage_error
#print axioms residualTolerance
#print axioms rootPreimage_small
#print axioms rootRange

end YMGap.Continuum.BF4WilsonAllNomeRootTimeRange
