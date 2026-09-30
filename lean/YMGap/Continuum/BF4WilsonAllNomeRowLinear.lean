/-
Linear represented rows on the SAME original all-nome Wilson completion.
Difference rows use the actual completed squared-distance estimate. Scalar
rows use the supplied rational Cauchy modulus and the original Wilson norm
ceiling; their limit is the already constructed completed-real scalar action.
-/

import YMGap.Continuum.BF4WilsonAllNomeGraphDistance
import YMGap.Continuum.BF4WilsonAllNomeCauchyRows
import YMGap.Continuum.BF4WilsonAllNomeRealScalarCauchy
import YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar

namespace YMGap.Continuum.BF4WilsonAllNomeRowLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm distSq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeGraphDistance (completedDist_sub_le)
open YMGap.Continuum.BF4WilsonAllNomeRealScalarCauchy (scalar_change_bound realScalarCauchy)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completedRealSmul completedRealSmul_mk)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy
  (coefficientTolerance coefficientTolerance_pos)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation
  (quarter quarter_pos)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normBase normCeiling normCeiling_nonnegative diagonal_le_normCeiling)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "P" => distanceData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem four_quarters (epsilon : Q') :
    Q'.eqv ((quarter epsilon+quarter epsilon)+
      (quarter epsilon+quarter epsilon)) epsilon :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (ExpNeg.two_halves (HalfPow.half*epsilon))
      (ExpNeg.two_halves (HalfPow.half*epsilon)))
    (ExpNeg.two_halves epsilon)

private theorem sub_close (x x' y y' : V) (epsilon : Q')
    (hx : RCle (dist x x') (rat (quarter epsilon)))
    (hy : RCle (dist y y') (rat (quarter epsilon))) :
    RCle (dist (completedSub hw0 hw1 x y) (completedSub hw0 hw1 x' y'))
      (rat epsilon) := by
  have h := RCle_trans (completedDist_sub_le hw0 hw1 x x' y y')
    (RCadd_le_add (RCadd_le_add hx hx) (RCadd_le_add hy hy))
  exact RCle_trans h
    (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv (four_quarters epsilon)))

def differenceRows (R S : RepresentedCauchy hw0 hw1 (width := width)) :
    RepresentedCauchy hw0 hw1 (width := width) where
  row := fun n => differenceCauchy hw0 hw1 (R.row n) (S.row n)
  modulus := fun epsilon => max (R.modulus (quarter epsilon)) (S.modulus (quarter epsilon))
  isCauchy := by
    intro epsilon he m n hm hn
    exact sub_close hw0 hw1 (Class (R.row m)) (Class (R.row n))
      (Class (S.row m)) (Class (S.row n)) epsilon
      (R.isCauchy _ (quarter_pos he) m n
        (Nat.le_trans (Nat.le_max_left _ _) hm)
        (Nat.le_trans (Nat.le_max_left _ _) hn))
      (S.isCauchy _ (quarter_pos he) m n
        (Nat.le_trans (Nat.le_max_right _ _) hm)
        (Nat.le_trans (Nat.le_max_right _ _) hn))

theorem differenceRows_pin (R S : RepresentedCauchy hw0 hw1 (width := width)) (n : Nat) :
    rowPoint hw0 hw1 (differenceRows hw0 hw1 R S) n =
      completedSub hw0 hw1 (rowPoint hw0 hw1 R n) (rowPoint hw0 hw1 S n) := rfl

def differenceLimitModulus (R S : RepresentedCauchy hw0 hw1 (width := width))
    (epsilon : Q') : Nat :=
  max (limitRate hw0 hw1 R (quarter epsilon))
    (limitRate hw0 hw1 S (quarter epsilon))

theorem differenceLimit_bound (R S : RepresentedCauchy hw0 hw1 (width := width))
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat)
    (hn : differenceLimitModulus hw0 hw1 R S epsilon≤n) :
    RCle (dist (rowPoint hw0 hw1 (differenceRows hw0 hw1 R S) n)
      (completedSub hw0 hw1 (limit hw0 hw1 R) (limit hw0 hw1 S)))
      (rat epsilon) := by
  rw [differenceRows_pin]
  exact sub_close hw0 hw1 _ _ _ _ epsilon
    (limit_bound hw0 hw1 R _ (quarter_pos he) n
      (Nat.le_trans (Nat.le_max_left _ _) hn))
    (limit_bound hw0 hw1 S _ (quarter_pos he) n
      (Nat.le_trans (Nat.le_max_right _ _) hn))

theorem rowLimit_difference (R S : RepresentedCauchy hw0 hw1 (width := width)) :
    limit hw0 hw1 (differenceRows hw0 hw1 R S) =
      completedSub hw0 hw1 (limit hw0 hw1 R) (limit hw0 hw1 S) :=
  limit_unique hw0 hw1 (differenceRows hw0 hw1 R S) _
    (differenceLimitModulus hw0 hw1 R S) (differenceLimit_bound hw0 hw1 R S)

/-- Same original vector, two rational coefficients. The dense scalar-change
estimate is passed through the already certified original representatives. -/
private theorem scalar_change_completed (X : (D).Cauchy) (a b epsilon : Q')
    (he : (0 : Q')<epsilon)
    (hab : a ≤ b + coefficientTolerance (normCeiling PD X)
        (normCeiling_nonnegative PD X) epsilon ∧
      b ≤ a + coefficientTolerance (normCeiling PD X)
        (normCeiling_nonnegative PD X) epsilon) :
    RCle (dist (completedSmul hw0 hw1 a (Class X))
      (completedSmul hw0 hw1 b (Class X))) (rat (quarter epsilon)) := by
  let A := (scalarContinuous hw0 hw1 a).mapCauchy X
  let B := (scalarContinuous hw0 hw1 b).mapCauchy X
  change RCle (dist (Class A) (Class B)) _
  rw [completedDist_mk]
  change leEv (representativeDist hw0 hw1 A B) (ofQ' (quarter epsilon))
  apply CRealSeminormCompletedApproximation.representativeDist_le_of_eventually P
    A B (quarter epsilon) (normBase PD X)
  intro j hj
  change leEv (distSq hw0 hw1
    (YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.smul a (X.seq j))
    (YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.smul b (X.seq j)))
    (ofQ' (quarter epsilon))
  exact scalar_change_bound hw0 hw1 a b (normCeiling PD X) epsilon
    (normCeiling_nonnegative PD X) he (X.seq j)
    (diagonal_le_normCeiling PD X j hj) hab

def scalarRowModulus (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (epsilon : Q') : Nat :=
  cs.M (coefficientTolerance (normCeiling PD X)
    (normCeiling_nonnegative PD X) epsilon)

private theorem quarter_le_self (epsilon : Q') (he : (0 : Q')<epsilon) :
    quarter epsilon ≤ epsilon := by
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (by decide : HalfPow.half ≤ (1 : Q'))
      (Q'.le_of_lt (ExpNeg.half_mul_pos epsilon he)))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _
          (by decide : HalfPow.half ≤ (1 : Q')) (Q'.le_of_lt he))
        (Q'.le_of_eqv (Q'.one_mul_eqv _))))

def scalarRows (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) :
    RepresentedCauchy hw0 hw1 (width := width) where
  row := fun n => (scalarContinuous hw0 hw1 (s.approx n)).mapCauchy X
  modulus := scalarRowModulus hw0 hw1 s cs X
  isCauchy := by
    intro epsilon he m n hm hn
    let cap := normCeiling PD X
    have hc : (0 : Q')≤cap := normCeiling_nonnegative PD X
    let delta := coefficientTolerance cap hc epsilon
    have hd : (0 : Q')<delta := coefficientTolerance_pos cap hc he
    have h := scalar_change_completed hw0 hw1 X (s.approx m) (s.approx n)
      epsilon he (cs.bound delta hd m n hm hn)
    exact RCle_trans h
      (leEv_le_ofQ'_of_approx_le (fun _ => quarter_le_self epsilon he))

theorem scalarRows_pin (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (n : Nat) :
    rowPoint hw0 hw1 (scalarRows hw0 hw1 s cs X) n =
      completedSmul hw0 hw1 (s.approx n) (Class X) := rfl

/-- A fixed scalar row is close to the previously constructed real-scalar
class. The rate is the supplied scalar modulus, not an extracted existence. -/
theorem scalarRows_limit_bound (s : CReal) (cs : QCauchy s.approx)
    (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat)
    (hn : scalarRowModulus hw0 hw1 s cs X epsilon≤n) :
    RCle (dist (rowPoint hw0 hw1 (scalarRows hw0 hw1 s cs X) n)
      (completedRealSmul hw0 hw1 s cs (Class X))) (rat epsilon) := by
  let cap := normCeiling PD X
  have hc : (0 : Q')≤cap := normCeiling_nonnegative PD X
  let delta := coefficientTolerance cap hc epsilon
  have hd : (0 : Q')<delta := coefficientTolerance_pos cap hc he
  let A := (scalarContinuous hw0 hw1 (s.approx n)).mapCauchy X
  let B := realScalarCauchy hw0 hw1 s cs X
  rw [scalarRows_pin,completedRealSmul_mk]
  change RCle (dist (Class A) (Class B)) _
  rw [completedDist_mk]
  change leEv (representativeDist hw0 hw1 A B) (ofQ' epsilon)
  have hsmall : leEv (representativeDist hw0 hw1 A B) (ofQ' (quarter epsilon)) := by
    apply CRealSeminormCompletedApproximation.representativeDist_le_of_eventually P
      A B (quarter epsilon) (max (normBase PD X) (cs.M delta))
    intro j hj
    change leEv (distSq hw0 hw1
      (YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.smul (s.approx n) (X.seq j))
      (YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.smul (s.approx j) (X.seq j)))
      (ofQ' (quarter epsilon))
    exact scalar_change_bound hw0 hw1 (s.approx n) (s.approx j) cap epsilon hc he
      (X.seq j) (diagonal_le_normCeiling PD X j (Nat.le_trans (Nat.le_max_left _ _) hj))
      (cs.bound delta hd n j hn (Nat.le_trans (Nat.le_max_right _ _) hj))
  exact leEv_trans hsmall
    (leEv_le_ofQ'_of_approx_le (fun _ => quarter_le_self epsilon he))

theorem scalarRows_limit (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) :
    limit hw0 hw1 (scalarRows hw0 hw1 s cs X) =
      completedRealSmul hw0 hw1 s cs (Class X) :=
  limit_unique hw0 hw1 (scalarRows hw0 hw1 s cs X) _
    (scalarRowModulus hw0 hw1 s cs X) (scalarRows_limit_bound hw0 hw1 s cs X)

#print axioms differenceRows
#print axioms differenceRows_pin
#print axioms differenceLimitModulus
#print axioms differenceLimit_bound
#print axioms rowLimit_difference
#print axioms scalarRowModulus
#print axioms scalarRows
#print axioms scalarRows_pin
#print axioms scalarRows_limit_bound
#print axioms scalarRows_limit

end YMGap.Continuum.BF4WilsonAllNomeRowLinear
