/-
A positive mixed-moment square for adjacent constructed root resolvents on the
SAME original Wilson completion.  No spectral measure or positive-operator
product assumption is used: the only positivity inputs are actual mixed
root/defect moments.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay
import YMGap.Continuum.BF4WilsonAllNomeRootResolvent

namespace YMGap.Continuum.BF4WilsonAllNomeResolventSquareComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics
open YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Q" => root hw0 hw1
local notation "D" => BF4WilsonAllNomeDyadicDefectDecay.defect hw0 hw1
local notation "DP" => BF4WilsonAllNomeDyadicDefectDecay.defectPower hw0 hw1
local notation "M" => meshAction hw0 hw1

/-- The nonnegative-coefficient part of the two denominator product:
`alpha² + alpha*D*(3+Q) + 2*D²*Q`. -/
def positiveNumerator (depth : Nat) (alpha : Q') (z : V) : V :=
  A (A (S (alpha*alpha) z)
      (S (3*alpha) (D depth z)))
    (A (S alpha (M depth 1 (DP depth 1 z)))
      (S 2 (M depth 1 (DP depth 2 z))))

/-- The denominator product, expressed as a sum of a positive mixed
polynomial and `2D²`. The literal inverse-denominator pin is separate. -/
def denominatorProduct (depth : Nat) (alpha : Q') (z : V) : V :=
  A (positiveNumerator hw0 hw1 depth alpha z) (S 2 (DP depth 2 z))

/-- Literal denominator product used by the adjacent dyadic inverses. -/
def literalProduct (depth : Nat) (alpha : Q') (z : V) : V :=
  completedSub hw0 hw1
    (S (1+alpha)
      (completedSub hw0 hw1 (S (2+alpha) z)
        (S 2 (Q (depth+1) z))))
    (Q depth
      (completedSub hw0 hw1 (S (2+alpha) z)
        (S 2 (Q (depth+1) z))))

private theorem qthree (depth : Nat) (z : V) :
    Q depth (Q (depth+1) z) = Q (depth+1) (Q depth z) := by
  calc
    Q depth (Q (depth+1) z) =
        Q (depth+1) (Q (depth+1) (Q (depth+1) z)) :=
      (root_square hw0 hw1 depth (Q (depth+1) z)).symm
    _ = Q (depth+1) (Q depth z) :=
      congrArg (Q (depth+1)) (root_square hw0 hw1 depth z)

/-- The expansion needs only the four consecutive root images of `z`.
The coefficient normalization is exact on the original quotient pairing. -/
theorem denominatorProduct_pin (depth : Nat) (alpha : Q') (z : V) :
    denominatorProduct hw0 hw1 (depth+1) alpha z =
      literalProduct hw0 hw1 depth alpha z := by
  apply completed_eq_of_pairings hw0 hw1
  intro y
  let q1 := Q (depth+1) z
  let q2 := Q depth z
  let q3 := Q (depth+1) q2
  have hd1 : B (D (depth+1) z) y = RCsub (B z y) (B q1 y) := by
    unfold BF4WilsonAllNomeDyadicDefectDecay.defect q1
    rw [completedInner_sub_left]
  have hd2 : B (DP (depth+1) 2 z) y =
      RCsub (RCsub (B z y) (B q1 y))
        (RCsub (B q1 y) (B q2 y)) := by
    change B (D (depth+1) (D (depth+1) z)) y = _
    unfold BF4WilsonAllNomeDyadicDefectDecay.defect
    rw [root_sub, root_square, completedInner_sub_left,
      completedInner_sub_left, completedInner_sub_left]
  have hqd1 : B (M (depth+1) 1 (DP (depth+1) 1 z)) y =
      RCsub (B q1 y) (B q2 y) := by
    change B (Q (depth+1) (D (depth+1) z)) y = _
    unfold BF4WilsonAllNomeDyadicDefectDecay.defect
    rw [root_sub, root_square, completedInner_sub_left]
  have hqd2 : B (M (depth+1) 1 (DP (depth+1) 2 z)) y =
      RCsub (RCsub (B q1 y) (B q2 y))
        (RCsub (B q2 y) (B q3 y)) := by
    change B (Q (depth+1) (D (depth+1) (D (depth+1) z))) y = _
    unfold BF4WilsonAllNomeDyadicDefectDecay.defect
    rw [root_sub, root_sub, root_sub, root_square]
    simp only [completedInner_sub_left]
    rfl
  have hliteral : B (literalProduct hw0 hw1 depth alpha z) y =
      RCsub
        (RCscale (1+alpha)
          (RCsub (RCscale (2+alpha) (B z y)) (RCscale 2 (B q1 y))))
        (RCsub (RCscale (2+alpha) (B q2 y)) (RCscale 2 (B q3 y))) := by
    unfold literalProduct
    rw [root_sub, root_smul, root_smul, qthree,
      completedInner_sub_left, completedInner_smul_left,
      completedInner_sub_left, completedInner_smul_left,
      completedInner_smul_left, completedInner_sub_left,
      completedInner_smul_left, completedInner_smul_left]
  unfold denominatorProduct positiveNumerator
  simp only [completedInner_add_left, completedInner_smul_left]
  rw [hd1, hd2, hqd1, hqd2, hliteral]
  refine Quotient.inductionOn₃ (B z y) (B q1 y) (B q2 y) ?_
  intro X Y Z'
  refine Quotient.inductionOn (B q3 y) ?_
  intro H
  let a : PolyExpr := .var 0
  let u : PolyExpr := .var 1
  let v : PolyExpr := .var 2
  let s : PolyExpr := .var 3
  let t : PolyExpr := .var 4
  let d1 : PolyExpr := .add u (.neg v)
  let qd1 : PolyExpr := .add v (.neg s)
  let d2 : PolyExpr := .add d1 (.neg qd1)
  let qd2 : PolyExpr := .add qd1 (.neg (.add s (.neg t)))
  let cn : PolyExpr := .add
    (.add (.mul (.mul a a) u) (.mul (.mul (.const 3) a) d1))
    (.add (.mul a qd1) (.mul (.const 2) qd2))
  let lhs : PolyExpr := .add cn (.mul (.const 2) d2)
  let rhs : PolyExpr := .add
    (.mul (.add (.const 1) a)
      (.add (.mul (.add (.const 2) a) u) (.neg (.mul (.const 2) v))))
    (.neg (.add (.mul (.add (.const 2) a) s) (.neg (.mul (.const 2) t))))
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq lhs rhs (by decide)
      (fun
        | 0 => alpha
        | 1 => X.approx n
        | 2 => Y.approx n
        | 3 => Z'.approx n
        | _ => H.approx n)))

private theorem mixed_pair (depth : Nat) (z : V) (k l m : Nat) :
    B (M depth k (DP depth l z)) (DP depth m z) =
      moment hw0 hw1 depth z k (l+m) := by
  unfold moment
  rw [mesh_symmetric, defectPower_symmetric, ← time_defectPower,
    ← defectPower_add]

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (X.approx n))))

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (X.approx n)))

private theorem rc_nonneg_add {a b : RC} (ha : RCnonneg a) (hb : RCnonneg b) :
    RCnonneg (RCadd a b) := by
  have h := RCadd_le_add ha hb
  simp only [rc_zero_add] at h
  exact h

private theorem rc_nonneg_scale {a : RC} (c : Q') (hc : (0 : Q') ≤ c)
    (ha : RCnonneg a) : RCnonneg (RCscale c a) := by
  have h := RCscale_mono hc ha
  rw [RCscale_RCzero] at h
  exact h

/-- Only four already-constructed nonnegative mixed moments are needed. -/
theorem positiveNumerator_cross_nonnegative (depth : Nat) (alpha : Q')
    (hα : (0 : Q') ≤ alpha) (z : V) :
    RCnonneg (B (positiveNumerator hw0 hw1 depth alpha z) (DP depth 2 z)) := by
  unfold positiveNumerator
  rw [completedInner_add_left, completedInner_add_left,
    completedInner_add_left, completedInner_smul_left,
    completedInner_smul_left, completedInner_smul_left,
    completedInner_smul_left]
  have h0 : RCnonneg (B z (DP depth 2 z)) :=
    moment_nonnegative hw0 hw1 depth z 0 2
  have h1 : RCnonneg (B (DP depth 1 z) (DP depth 2 z)) := by
    change RCnonneg (B (M depth 0 (DP depth 1 z)) (DP depth 2 z))
    rw [mixed_pair]
    exact moment_nonnegative hw0 hw1 depth z 0 3
  have h2 : RCnonneg (B (M depth 1 (DP depth 1 z)) (DP depth 2 z)) := by
    rw [mixed_pair]
    exact moment_nonnegative hw0 hw1 depth z 1 3
  have h3 : RCnonneg (B (M depth 1 (DP depth 2 z)) (DP depth 2 z)) := by
    rw [mixed_pair]
    exact moment_nonnegative hw0 hw1 depth z 1 4
  have h3α : (0 : Q') ≤ 3*alpha :=
    Q'.mul_nonneg 3 alpha (by decide) hα
  exact rc_nonneg_add
    (rc_nonneg_add (rc_nonneg_scale _ (Q'.mul_nonneg _ _ hα hα) h0)
      (rc_nonneg_scale _ h3α h1))
    (rc_nonneg_add (rc_nonneg_scale _ hα h2)
      (rc_nonneg_scale _ (by decide : (0 : Q') ≤ 2) h3))

private theorem rc_norm_square_expansion (u v t : RC) :
    RCadd (RCadd u (RCscale 4 v)) (RCscale 4 t) =
      RCadd (RCadd u (RCscale 2 v))
        (RCadd (RCscale 2 v) (RCscale 4 t)) := by
  refine Quotient.inductionOn₃ u v t ?_
  intro U V' T
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.mul (.const 4) (.var 1)))
        (.mul (.const 4) (.var 2)))
      (.add (.add (.var 0) (.mul (.const 2) (.var 1)))
        (.add (.mul (.const 2) (.var 1)) (.mul (.const 4) (.var 2))))
      (by decide)
      (fun | 0 => U.approx n | 1 => V'.approx n | _ => T.approx n)))

private theorem denominator_square_identity (depth : Nat) (alpha : Q') (z : V) :
    B (denominatorProduct hw0 hw1 depth alpha z)
      (denominatorProduct hw0 hw1 depth alpha z) =
    RCadd
      (RCadd (B (positiveNumerator hw0 hw1 depth alpha z)
        (positiveNumerator hw0 hw1 depth alpha z))
        (RCscale 4 (B (positiveNumerator hw0 hw1 depth alpha z)
          (DP depth 2 z))))
      (RCscale 4 (B (DP depth 2 z) (DP depth 2 z))) := by
  unfold denominatorProduct
  rw [completedInner_add_left, completedInner_add_right,
    completedInner_add_right, completedInner_smul_left,
    completedInner_smul_right, completedInner_smul_right,
    completedInner_smul_left, RCscale_RCscale,
    completedInner_symm hw0 hw1
      (DP depth 2 z) (positiveNumerator hw0 hw1 depth alpha z)]
  rw [RCSignedPairBudget.scale_congr (by decide : Q'.eqv (2*2) 4)]
  exact (rc_norm_square_expansion _ _ _).symm

/-- Sharp positive-square comparison for the two adjacent inverse
denominators. This retains the original boundary kernel. -/
theorem positive_square_comparison (depth : Nat) (alpha : Q')
    (hα : (0 : Q') ≤ alpha) (z : V) :
    RCle (RCscale 4 (B (DP depth 2 z) (DP depth 2 z)))
      (B (denominatorProduct hw0 hw1 depth alpha z)
        (denominatorProduct hw0 hw1 depth alpha z)) := by
  have hc := completedInner_nonnegative hw0 hw1
    (positiveNumerator hw0 hw1 depth alpha z)
  have hm := rc_nonneg_scale 4 (by decide : (0 : Q') ≤ 4)
    (positiveNumerator_cross_nonnegative hw0 hw1 depth alpha hα z)
  have h := RCadd_le_add (rc_nonneg_add hc hm)
    (RCle_refl (RCscale 4 (B (DP depth 2 z) (DP depth 2 z))))
  rw [rc_zero_add] at h
  rw [denominator_square_identity]
  exact h

#print axioms positiveNumerator
#print axioms denominatorProduct
#print axioms denominatorProduct_pin
#print axioms positiveNumerator_cross_nonnegative
#print axioms positive_square_comparison

end YMGap.Continuum.BF4WilsonAllNomeResolventSquareComparison
