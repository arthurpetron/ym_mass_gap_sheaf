/-
Approximation of the ORIGINAL signed one-quaternion polynomial Haar by actual
finite joint-weighted rational sphere nodes. Affine monomial recoding preserves
Haar moments and raw evaluations, including noncanonical trailing-zero lists.
Grid error and actual sphere-repair cost have separate computed half-budgets.
No continuous Haar integral, independent marginal law or supplied modulus.
-/

import YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget
import YMGap.Continuum.QuaternionHaarTensorBernsteinRepairModulus

namespace YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.RepTheory.RationalQuaternion
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.QuaternionHaarTensorBernsteinCubature
open YMGap.Continuum.QuaternionHaarTensorBernsteinError
open YMGap.Continuum.QuaternionHaarBernsteinMonomialRecoding
open YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget
open YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
open YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialRepair
open YMGap.Continuum.QuaternionHaarTensorBernsteinRepairModulus

local infix:50 " ≈ " => Q'.eqv

def nodeMonomialSum (n : Nat)
    (nodes : Nat → Nat → Nat → Nat → Nat → Q') (m : List Nat) : Q' :=
  sum4 (fun a b c d => jointWeightRaw n a b c d * evalMono (nodes a b c d) m) (n+2)

/-- Literal weighted evaluations, not an exact quadrature assumption. -/
def nodeWeightedSum (n : Nat)
    (nodes : Nat → Nat → Nat → Nat → Nat → Q') (p : RatPoly) : Q' :=
  sum4 (fun a b c d => jointWeightRaw n a b c d * evalRatPoly (nodes a b c d) p) (n+2)

private theorem sum4_zero (count : Nat) :
    sum4 (fun _ _ _ _ => (0 : Q')) count ≈ 0 := by
  simp only [sum4, finSum_zero_seq]
  exact Q'.eqv_refl _

theorem nodeWeightedSum_nil (n : Nat)
    (nodes : Nat → Nat → Nat → Nat → Nat → Q') :
    nodeWeightedSum n nodes [] ≈ 0 :=
  Q'.eqv_trans _ _ _
    (sum4_congr _ _ (fun a b c d => Q'.mul_zero_eqv (jointWeightRaw n a b c d)) (n+2))
    (sum4_zero (n+2))

/-- Signed-term linearity on the SAME literal finite weights. -/
theorem nodeWeightedSum_cons (n : Nat)
    (nodes : Nat → Nat → Nat → Nat → Nat → Q') (t : RatTerm) (p : RatPoly) :
    nodeWeightedSum n nodes (t::p) ≈
      t.2 * nodeMonomialSum n nodes t.1 + nodeWeightedSum n nodes p := by
  have hpoint (a b c d : Nat) :
      jointWeightRaw n a b c d * evalRatPoly (nodes a b c d) (t::p) ≈
        t.2 * (jointWeightRaw n a b c d * evalMono (nodes a b c d) t.1) +
          jointWeightRaw n a b c d * evalRatPoly (nodes a b c d) p :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.var 3)))
      (.add (.mul (.var 1) (.mul (.var 0) (.var 2))) (.mul (.var 0) (.var 3)))
      (by decide) (fun
        | 0 => jointWeightRaw n a b c d
        | 1 => t.2
        | 2 => evalMono (nodes a b c d) t.1
        | _ => evalRatPoly (nodes a b c d) p)
  exact Q'.eqv_trans _ _ _ (sum4_congr _ _ hpoint (n+2))
    (Q'.eqv_trans _ _ _ (sum4_add _ _ (n+2))
      (Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_symm (sum4_const_mul t.2 _ (n+2)))))

def rawWeightedSum (n : Nat) (p : RatPoly) : Q' :=
  nodeWeightedSum n (rawEnvironment n) p

def repairedWeightedSum (n : Nat) (p : RatPoly) : Q' :=
  nodeWeightedSum n (repairedEnvironment n) p

def monomialGridCutoff (m : List Nat) (eta : Q') : Nat :=
  weightedRowCutoff
    (monomialFactor m ⟨0,by decide⟩) (monomialFactor m ⟨1,by decide⟩)
    (monomialFactor m ⟨2,by decide⟩) (monomialFactor m ⟨3,by decide⟩) eta

/-- The original finite term list computes its maximum row cutoff. -/
def polynomialGridCutoff : RatPoly → Q' → Nat
  | [], _ => 0
  | t::p, eta => Nat.max (monomialGridCutoff t.1 eta) (polynomialGridCutoff p eta)

theorem monomial_raw_grid_error (m : List Nat) (hm : m.length ≤ 4)
    (eta : Q') (he : (0 : Q') < eta) (n : Nat)
    (hn : monomialGridCutoff m eta ≤ n) :
    Q'.abs (quaternionHaarMono 1 m + -(nodeMonomialSum n (rawEnvironment n) m)) ≤
      monomialGridBudget m eta := by
  have hp := haar_separable_grid_error
    (monomialFactor m ⟨0,by decide⟩) (monomialFactor m ⟨1,by decide⟩)
    (monomialFactor m ⟨2,by decide⟩) (monomialFactor m ⟨3,by decide⟩)
    eta he n hn
  have hg : gridWeightedSum n
      (monomialFactor m ⟨0,by decide⟩) (monomialFactor m ⟨1,by decide⟩)
      (monomialFactor m ⟨2,by decide⟩) (monomialFactor m ⟨3,by decide⟩) ≈
      nodeMonomialSum n (rawEnvironment n) m :=
    sum4_congr _ _ (fun a b c d =>
      Q'.mul_eqv_congr_left _ _ _ (monomial_gridProduct m hm n a b c d)) (n+2)
  have hpin : quaternionHaar 1 (monomialSeparable m) +
      -(gridWeightedSum n
        (monomialFactor m ⟨0,by decide⟩) (monomialFactor m ⟨1,by decide⟩)
        (monomialFactor m ⟨2,by decide⟩) (monomialFactor m ⟨3,by decide⟩)) ≈
      quaternionHaarMono 1 m + -(nodeMonomialSum n (rawEnvironment n) m) :=
    Q'.add_eqv_congr' (monomialSeparable_haar m hm) (Q'.neg_eqv_congr _ _ hg)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (ExpNeg.abs_eqv_congr hpin)) hp

/-- Every ORIGINAL supported signed polynomial, including duplicate terms and
noncanonical exponent lists, has an actual finite grid error budget. -/
theorem haar_raw_grid_error : ∀ (p : RatPoly), SupportedQuaternionBlocks 1 p →
    ∀ (eta : Q'), (0 : Q') < eta → ∀ n,
    polynomialGridCutoff p eta ≤ n →
    Q'.abs (quaternionHaar 1 p + -(rawWeightedSum n p)) ≤ polynomialGridBudget p eta
  | [], _, eta, _, n, _ => by
      have hz : quaternionHaar 1 [] + -(rawWeightedSum n []) ≈ 0 :=
        Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left 0 _ _
            (Q'.neg_eqv_congr _ _ (nodeWeightedSum_nil n (rawEnvironment n))))
          (by decide)
      exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ (ExpNeg.abs_eqv_congr hz)
        (by decide : Q'.abs (0 : Q') ≈ 0))
  | t::p, hp, eta, he, n, hn => by
      have hm : t.1.length ≤ 4 := hp t List.mem_cons_self
      have hr : SupportedQuaternionBlocks 1 p := fun s hs => hp s (List.mem_cons_of_mem t hs)
      have hn0 : monomialGridCutoff t.1 eta ≤ n :=
        Nat.le_trans (Nat.le_max_left _ _) hn
      have hnr : polynomialGridCutoff p eta ≤ n :=
        Nat.le_trans (Nat.le_max_right _ _) hn
      let A := quaternionHaarMono 1 t.1
      let B := nodeMonomialSum n (rawEnvironment n) t.1
      let R := quaternionHaar 1 p
      let S := rawWeightedSum n p
      have hpin : quaternionHaar 1 (t::p) + -(rawWeightedSum n (t::p)) ≈
          t.2*(A+-B)+(R+-S) :=
        Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _
            (Q'.neg_eqv_congr _ _ (nodeWeightedSum_cons n (rawEnvironment n) t p)))
          (poly_identity_of_normal_eq
            (.add (.add (.mul (.var 0) (.var 1)) (.var 3))
              (.neg (.add (.mul (.var 0) (.var 2)) (.var 4))))
            (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
              (.add (.var 3) (.neg (.var 4))))
            (by decide) (fun | 0 => t.2 | 1 => A | 2 => B | 3 => R | _ => S))
      have hterm : Q'.abs (t.2*(A+-B)) ≤ Q'.abs t.2*monomialGridBudget t.1 eta :=
        Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
          (Q'.mul_le_mul_of_nonneg_left _ _ _
            (monomial_raw_grid_error t.1 hm eta he n hn0) (Q'.abs_nonneg _))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin))
        (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
          (Q'.add_le_add hterm (haar_raw_grid_error p hr eta he n hnr)))

private theorem weighted_point_upper (w x y : Q') (hw : (0 : Q') ≤ w) :
    w*x ≤ w*y + w*Q'.abs (x+-y) :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (ExpNeg.le_add_of_abs_sub_le (Q'.le_refl' (Q'.abs (x+-y)))) hw)
    (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _))

/-- No absolute-sum equality is assumed: actual positivity and finite order
bound the difference of the two SAME-weight sums by the literal repair cost. -/
theorem raw_repaired_difference_le_cost (n : Nat) (p : RatPoly) :
    Q'.abs (rawWeightedSum n p + -(repairedWeightedSum n p)) ≤ repairPolynomialCost n p := by
  let F := fun a b c d => jointWeightRaw n a b c d * evalRatPoly (rawEnvironment n a b c d) p
  let G := fun a b c d => jointWeightRaw n a b c d * evalRatPoly (repairedEnvironment n a b c d) p
  let E := fun a b c d => jointWeightRaw n a b c d * Q'.abs
    (evalRatPoly (rawEnvironment n a b c d) p + -(evalRatPoly (repairedEnvironment n a b c d) p))
  have hforward : ∀ a b c d, F a b c d ≤ G a b c d + E a b c d :=
    fun a b c d => weighted_point_upper _ _ _ (jointWeightRaw_nonnegative n a b c d)
  have hbackward : ∀ a b c d, G a b c d ≤ F a b c d + E a b c d := by
    intro a b c d
    have h := weighted_point_upper (jointWeightRaw n a b c d)
      (evalRatPoly (repairedEnvironment n a b c d) p)
      (evalRatPoly (rawEnvironment n a b c d) p) (jointWeightRaw_nonnegative n a b c d)
    exact Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (ExpNeg.abs_sub_comm _ _))))
  have hF : rawWeightedSum n p ≤ repairedWeightedSum n p + repairPolynomialCost n p :=
    Q'.le_trans' _ _ _
      (sum4_le_lt F (fun a b c d => G a b c d + E a b c d) (n+2)
        (fun a b c d _ _ _ _ => hforward a b c d))
      (Q'.le_of_eqv (sum4_add G E (n+2)))
  have hG : repairedWeightedSum n p ≤ rawWeightedSum n p + repairPolynomialCost n p :=
    Q'.le_trans' _ _ _
      (sum4_le_lt G (fun a b c d => F a b c d + E a b c d) (n+2)
        (fun a b c d _ _ _ _ => hbackward a b c d))
      (Q'.le_of_eqv (sum4_add F E (n+2)))
  exact CReal.abs_sub_le_of_bounds hF hG

/-- A computable cutoff joining TWO independently paid error components. -/
def approximationCutoff (p : RatPoly) (epsilon : Q') : Nat :=
  Nat.max (polynomialGridCutoff p (gridTolerance p epsilon)) (repairCutoff p epsilon)

/-- Approximate the ORIGINAL Haar by actual rational UNIT-quaternion nodes.
The complete tolerance is paid, rather than silently allocating it twice. -/
theorem haar_repaired_error (p : RatPoly) (hp : SupportedQuaternionBlocks 1 p)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : approximationCutoff p epsilon ≤ n) :
    Q'.abs (quaternionHaar 1 p + -(repairedWeightedSum n p)) ≤ epsilon := by
  have hnG : polynomialGridCutoff p (gridTolerance p epsilon) ≤ n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hnR : repairCutoff p epsilon ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hG : Q'.abs (quaternionHaar 1 p + -(rawWeightedSum n p)) ≤ Q'.invSucc 1*epsilon :=
    Q'.le_trans' _ _ _
      (haar_raw_grid_error p hp _ (gridTolerance_positive p epsilon he) n hnG)
      (polynomialGridBudget_half p epsilon he)
  have hR : Q'.abs (rawWeightedSum n p + -(repairedWeightedSum n p)) ≤ Q'.invSucc 1*epsilon :=
    Q'.le_trans' _ _ _ (raw_repaired_difference_le_cost n p)
      (repair_halfBudget p epsilon he n hnR)
  have hpin : quaternionHaar 1 p + -(repairedWeightedSum n p) ≈
      (quaternionHaar 1 p + -(rawWeightedSum n p)) +
        (rawWeightedSum n p + -(repairedWeightedSum n p)) :=
    poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 2)))
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
      (by decide) (fun | 0 => quaternionHaar 1 p | 1 => rawWeightedSum n p | _ => repairedWeightedSum n p)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.le_trans' _ _ _ (Q'.add_le_add hG hR)
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (poly_identity_of_normal_eq
            (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
            (.mul (.add (.var 0) (.var 0)) (.var 1))
            (by decide) (fun | 0 => Q'.invSucc 1 | _ => epsilon))
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _
              (by decide : Q'.invSucc 1 + Q'.invSucc 1 ≈ (1 : Q')))
            (Q'.one_mul_eqv epsilon))))))

private theorem same_weight_const_sum (n : Nat) (c : Q') :
    sum4 (fun a b d e => c * jointWeightRaw n a b d e) (n+2) ≈ c :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (sum4_const_mul c (jointWeightRaw n) (n+2)))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (jointMass_one n))
      (Q'.mul_one_eqv c))

/-- Actual positive unit-mass sphere nodes preserve a bound on the original
polynomial over rational unit quaternions. No supremum is chosen. -/
theorem repairedWeightedSum_abs_le (n : Nat) (p : RatPoly) (M : Q')
    (hM : ∀ q : UnitNorm, Q'.abs (evalRatPoly (environmentOf q.val) p) ≤ M) :
    Q'.abs (repairedWeightedSum n p) ≤ M := by
  let F := fun a b c d => jointWeightRaw n a b c d *
    evalRatPoly (repairedEnvironment n a b c d) p
  let U := fun a b c d => M * jointWeightRaw n a b c d
  let L := fun a b c d => (-M) * jointWeightRaw n a b c d
  have hupper (a b c d : Nat) : F a b c d ≤ U a b c d :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.le_trans' _ _ _ (Q'.le_abs_self _) (hM (repairedQuaternion n a b c d)))
        (jointWeightRaw_nonnegative n a b c d))
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
  have hlower (a b c d : Nat) : L a b c d ≤ F a b c d := by
    have hpoint : -M ≤ evalRatPoly (repairedEnvironment n a b c d) p :=
      Q'.le_trans' _ _ _ (Q'.neg_le_neg (hM (repairedQuaternion n a b c d)))
        (ExpNeg.neg_abs_le _)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hpoint (jointWeightRaw_nonnegative n a b c d))
  have hU : repairedWeightedSum n p ≤ M :=
    Q'.le_trans' _ _ _
      (sum4_le_lt F U (n+2) (fun a b c d _ _ _ _ => hupper a b c d))
      (Q'.le_of_eqv (same_weight_const_sum n M))
  have hL : -M ≤ repairedWeightedSum n p :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (same_weight_const_sum n (-M)))
      (sum4_le_lt L F (n+2) (fun a b c d _ _ _ _ => hlower a b c d))
  exact Q'.abs_le hL hU

/-- Sphere sup-bound contractivity of the ORIGINAL polynomial Haar.
The bound is tested on the actual rational unit-quaternion carrier. This is
not yet an integral on arbitrary continuous functions or a compact Haar measure. -/
theorem haar_abs_le_unit_bound (p : RatPoly) (hp : SupportedQuaternionBlocks 1 p)
    (M : Q')
    (hM : ∀ q : UnitNorm, Q'.abs (evalRatPoly (environmentOf q.val) p) ≤ M) :
    Q'.abs (quaternionHaar 1 p) ≤ M := by
  apply Q'.le_of_le_add_mul_invSucc _ _ 1
  intro k
  let epsilon := Q'.invSucc k
  let n := approximationCutoff p epsilon
  let A := quaternionHaar 1 p
  let S := repairedWeightedSum n p
  have herr : Q'.abs (A+-S) ≤ epsilon :=
    haar_repaired_error p hp epsilon (Q'.invSucc_pos k) n (Nat.le_refl _)
  have hnode : Q'.abs S ≤ M := repairedWeightedSum_abs_le n p M hM
  have hpin : A ≈ S+(A+-S) :=
    poly_identity_of_normal_eq (.var 0)
      (.add (.var 1) (.add (.var 0) (.neg (.var 1))))
      (by decide) (fun | 0 => A | _ => S)
  have hbound : Q'.abs A ≤ M+epsilon :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin))
      (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _) (Q'.add_le_add hnode herr))
  exact Q'.le_trans' _ _ _ hbound
    (Q'.ge_of_eqv (Q'.add_eqv_congr_left _ _ _
      (Q'.one_mul_eqv epsilon)))

/-- The ACTUAL positive unit-mass sphere nodes preserve any signed rational
pointwise lower bound. No positivity of the polynomial's coefficients is needed. -/
theorem repairedWeightedSum_lower (n : Nat) (p : RatPoly) (c : Q')
    (hlow : ∀ q : UnitNorm, c ≤ evalRatPoly (environmentOf q.val) p) :
    c ≤ repairedWeightedSum n p := by
  let F := fun a b d e => jointWeightRaw n a b d e *
    evalRatPoly (repairedEnvironment n a b d e) p
  let L := fun a b d e => c * jointWeightRaw n a b d e
  have hpoint (a b d e : Nat) : L a b d e ≤ F a b d e :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (hlow (repairedQuaternion n a b d e))
        (jointWeightRaw_nonnegative n a b d e))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (same_weight_const_sum n c))
    (sum4_le_lt L F (n+2) (fun a b d e _ _ _ _ => hpoint a b d e))

/-- ORIGINAL polynomial Haar preserves a pointwise lower bound on rational
UnitNorm. Actual cubature error vanishes; no continuous-Haar positivity is assumed. -/
theorem haar_lower_bound (p : RatPoly) (hp : SupportedQuaternionBlocks 1 p)
    (c : Q') (hlow : ∀ q : UnitNorm, c ≤ evalRatPoly (environmentOf q.val) p) :
    c ≤ quaternionHaar 1 p := by
  apply Q'.le_of_le_add_mul_invSucc _ _ 1
  intro k
  let e := Q'.invSucc k
  let n := approximationCutoff p e
  have herr := haar_repaired_error p hp e (Q'.invSucc_pos k) n (Nat.le_refl _)
  have hback : repairedWeightedSum n p ≤ quaternionHaar 1 p + e :=
    ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) herr)
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ (repairedWeightedSum_lower n p c hlow) hback)
    (Q'.ge_of_eqv (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv e)))

end YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid

#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid.nodeMonomialSum
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid.nodeWeightedSum
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid.nodeWeightedSum_nil
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid.nodeWeightedSum_cons
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid.rawWeightedSum
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid.repairedWeightedSum
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid.monomialGridCutoff
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid.polynomialGridCutoff
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid.monomial_raw_grid_error
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid.haar_raw_grid_error
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid.raw_repaired_difference_le_cost
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid.approximationCutoff
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid.haar_repaired_error
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid.repairedWeightedSum_abs_le
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid.haar_abs_le_unit_bound
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid.repairedWeightedSum_lower
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid.haar_lower_bound
