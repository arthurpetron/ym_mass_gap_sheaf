/-
Finite normalized geometric sums of one constructed root on the SAME original
Wilson completion. This file supplies exact algebra and represented finite
outputs; convergence and inverse laws belong to subsequent modules.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicRepresentatives
import YMGap.Continuum.BF4WilsonAllNomeDistance
import YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4WilsonAllNomeRootResolventPartial

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
open YMGap.Continuum.RCSignedPairBudget (scale_congr)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics
open YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup
open YMGap.Continuum.BF4WilsonAllNomeDyadicRepresentatives
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (zero)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "D" => seminorm hw0 hw1 (width := width)
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "R" => root hw0 hw1
local notation "M" => meshAction hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

/-- The normalized finite Neumann sum `(1-r) Σ_{j<n} r^j R^j x`.
The parameter `r` is explicit; its interval guards are used in estimates. -/
def rootPartial (depth : Nat) (r : Q') : Nat → V → V
  | 0, _ => Z
  | n+1, x => A (S (1-r) x) (S r (R depth (rootPartial depth r n x)))

private theorem add_exchange (a b c d : V) :
    A (A a b) (A c d) = A (A a c) (A b d) := by
  calc
    A (A a b) (A c d) = A a (A b (A c d)) := completedAdd_assoc hw0 hw1 a b (A c d)
    _ = A a (A (A b c) d) :=
      congrArg (A a) (completedAdd_assoc hw0 hw1 b c d).symm
    _ = A a (A (A c b) d) :=
      congrArg (fun z => A a (A z d)) (completedAdd_comm hw0 hw1 b c)
    _ = A a (A c (A b d)) :=
      congrArg (A a) (completedAdd_assoc hw0 hw1 c b d)
    _ = A (A a c) (A b d) := (completedAdd_assoc hw0 hw1 a c (A b d)).symm

private theorem smul_zero_element (c : Q') : S c Z = Z := by
  calc
    S c Z = S c (S 0 Z) := congrArg (S c) (completedSmul_zero hw0 hw1 Z).symm
    _ = S (c*0) Z := completedSmul_mul hw0 hw1 c 0 Z
    _ = S 0 Z := completedSmul_congr hw0 hw1 (Q'.mul_zero_eqv c) Z
    _ = Z := completedSmul_zero hw0 hw1 Z

theorem partial_add (depth : Nat) (r : Q') (n : Nat) (x y : V) :
    rootPartial hw0 hw1 depth r n (A x y) =
      A (rootPartial hw0 hw1 depth r n x) (rootPartial hw0 hw1 depth r n y) := by
  induction n with
  | zero => exact (completedZero_add hw0 hw1 Z).symm
  | succ n ih =>
      change A (S (1-r) (A x y))
        (S r (R depth (rootPartial hw0 hw1 depth r n (A x y)))) = _
      rw [ih, completedSmul_add, root_add, completedSmul_add, add_exchange]
      rfl

theorem partial_smul (depth : Nat) (r c : Q') (n : Nat) (x : V) :
    rootPartial hw0 hw1 depth r n (S c x) = S c (rootPartial hw0 hw1 depth r n x) := by
  induction n with
  | zero => rw [rootPartial, rootPartial, smul_zero_element]
  | succ n ih =>
      change A (S (1-r) (S c x))
        (S r (R depth (rootPartial hw0 hw1 depth r n (S c x)))) =
        S c (A (S (1-r) x) (S r (R depth (rootPartial hw0 hw1 depth r n x))))
      rw [ih, root_smul, completedSmul_mul, completedSmul_mul,
        completedSmul_add]
      rw [completedSmul_mul, completedSmul_mul]
      rw [completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv (1-r) c) x,
        completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv r c)
          (R depth (rootPartial hw0 hw1 depth r n x))]

theorem partial_sub (depth : Nat) (r : Q') (n : Nat) (x y : V) :
    rootPartial hw0 hw1 depth r n (completedSub hw0 hw1 x y) =
      completedSub hw0 hw1 (rootPartial hw0 hw1 depth r n x)
        (rootPartial hw0 hw1 depth r n y) := by
  unfold completedSub completedNeg
  rw [partial_add, partial_smul]

theorem partial_root_commute (depth : Nat) (r : Q') (n : Nat) (x : V) :
    rootPartial hw0 hw1 depth r n (R depth x) =
      R depth (rootPartial hw0 hw1 depth r n x) := by
  induction n with
  | zero => rw [rootPartial, rootPartial, root_zero]
  | succ n ih =>
      change A (S (1-r) (R depth x))
        (S r (R depth (rootPartial hw0 hw1 depth r n (R depth x)))) =
        R depth (A (S (1-r) x)
          (S r (R depth (rootPartial hw0 hw1 depth r n x))))
      rw [ih, root_add, root_smul, root_smul]

theorem partial_mesh_commute (depth : Nat) (r : Q') (n steps : Nat) (x : V) :
    rootPartial hw0 hw1 depth r n (M depth steps x) =
      M depth steps (rootPartial hw0 hw1 depth r n x) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      change rootPartial hw0 hw1 depth r n (R depth (M depth steps x)) =
        R depth (M depth steps (rootPartial hw0 hw1 depth r n x))
      rw [partial_root_commute, ih]

/-- Exact finite tail, with no norm or spectral assumption. -/
theorem partial_split (depth : Nat) (r : Q') (n k : Nat) (x : V) :
    rootPartial hw0 hw1 depth r (n+k) x =
      A (rootPartial hw0 hw1 depth r n x)
        (S (r^n) (M depth n (rootPartial hw0 hw1 depth r k x))) := by
  induction n with
  | zero =>
      rw [Nat.zero_add, rootPartial, Q'.pow_zero, completedSmul_one]
      exact (completedZero_add hw0 hw1 _).symm
  | succ n ih =>
      rw [show n+1+k = (n+k)+1 by omega]
      change A (S (1-r) x)
        (S r (R depth (rootPartial hw0 hw1 depth r (n+k) x))) = _
      rw [ih, root_add, completedSmul_add, root_smul,
        completedSmul_mul, ← completedAdd_assoc]
      change A (rootPartial hw0 hw1 depth r (n+1) x)
        (S (r*(r^n)) (R depth (M depth n
          (rootPartial hw0 hw1 depth r k x)))) = _
      apply congrArg (A (rootPartial hw0 hw1 depth r (n+1) x))
      exact completedSmul_congr hw0 hw1
        (Q'.eqv_symm (Q'.eqv_of_eq (Q'.pow_succ r n)))
        (M depth (n+1) (rootPartial hw0 hw1 depth r k x))

private def deficitExpr : RingNormaliser.PolyExpr :=
  .add (.const 1) (.neg (.var 0))

private def squareExpr : RingNormaliser.PolyExpr :=
  .add
    (.add
      (.mul (.mul deficitExpr deficitExpr) (.var 1))
      (.mul (.mul deficitExpr (.var 0)) (.var 3)))
    (.add
      (.mul (.mul (.var 0) deficitExpr) (.var 3))
      (.mul (.mul (.var 0) (.var 0)) (.var 2)))

private def differenceExpr : RingNormaliser.PolyExpr :=
  .add (.add (.var 1) (.neg (.var 3)))
    (.neg (.add (.var 3) (.neg (.var 2))))

private theorem rc_convex_identity (r : Q') (a b c : RC) :
    RCadd
      (RCadd
        (RCadd (RCscale ((1-r)*(1-r)) a) (RCscale ((1-r)*r) c))
        (RCadd (RCscale (r*(1-r)) c) (RCscale (r*r) b)))
      (RCscale (r*(1-r)) (RCsub (RCsub a c) (RCsub c b))) =
      RCadd (RCscale (1-r) a) (RCscale r b) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro X Y Z'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add squareExpr (.mul (.mul (.var 0) deficitExpr) differenceExpr))
      (.add (.mul deficitExpr (.var 1)) (.mul (.var 0) (.var 2)))
      (by decide)
      (fun | 0 => r | 1 => X.approx n | 2 => Y.approx n | _ => Z'.approx n)))

private theorem convex_norm_identity (r : Q') (x y : V) :
    RCadd
      (BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1
        (A (S (1-r) x) (S r y)) (A (S (1-r) x) (S r y)))
      (RCscale (r*(1-r))
        (BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1
          (completedSub hw0 hw1 x y) (completedSub hw0 hw1 x y))) =
      RCadd (RCscale (1-r) (BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1 x x))
        (RCscale r (BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1 y y)) := by
  simp only [completedInner_add_left, completedInner_add_right,
    completedInner_smul_left, completedInner_smul_right,
    completedInner_sub_left, completedInner_sub_right]
  rw [RCscale_RCadd, RCscale_RCadd, RCscale_RCscale,
    RCscale_RCscale, RCscale_RCscale, RCscale_RCscale]
  rw [completedInner_symm hw0 hw1 y x]
  exact rc_convex_identity r _ _ _

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (X.approx n)))

private theorem convex_norm_le (r : Q') (hr0 : (0 : Q') ≤ r)
    (hr1 : r ≤ (1 : Q')) (x y : V) :
    RCle (BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1
      (A (S (1-r) x) (S r y)) (A (S (1-r) x) (S r y)))
      (RCadd (RCscale (1-r) (BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1 x x))
        (RCscale r (BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1 y y))) := by
  have hcoeff : (0 : Q') ≤ r*(1-r) :=
    Q'.mul_nonneg r (1-r) hr0 (Q'.sub_nonneg_of_le hr1)
  have h := RCscale_mono hcoeff
    (completedInner_nonnegative hw0 hw1 (completedSub hw0 hw1 x y))
  rw [RCscale_RCzero] at h
  have h' := RCadd_le_add
    (RCle_refl (BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1
      (A (S (1-r) x) (S r y)) (A (S (1-r) x) (S r y)))) h
  rw [rc_add_zero, convex_norm_identity] at h'
  exact h'

/-- The normalized geometric partial is a contraction, uniformly in its
length, on the original completed Wilson carrier. -/
theorem partial_norm_bound (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q'))
    (n : Nat) (x : V) :
    RCle (BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1
      (rootPartial hw0 hw1 depth r n x) (rootPartial hw0 hw1 depth r n x))
      (BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1 x x) := by
  induction n with
  | zero =>
      rw [rootPartial, completedInner_zero_left]
      exact completedInner_nonnegative hw0 hw1 x
  | succ n ih =>
      change RCle (BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1
        (A (S (1-r) x) (S r (R depth (rootPartial hw0 hw1 depth r n x))))
        (A (S (1-r) x) (S r (R depth (rootPartial hw0 hw1 depth r n x))))) _
      have hc := convex_norm_le hw0 hw1 r hr0 (Q'.le_of_lt hr1)
        x (R depth (rootPartial hw0 hw1 depth r n x))
      have ht := RCle_trans (root_norm_bound hw0 hw1 depth _) ih
      have ht' := RCscale_mono hr0 ht
      have h := RCle_trans hc
        (RCadd_le_add (RCle_refl _) ht')
      have hp : Q'.eqv ((1-r)+r) 1 := by
        exact RingNormaliser.poly_identity_of_normal_eq
          (.add (.add (.const 1) (.neg (.var 0))) (.var 0)) (.const 1)
          (by decide) (fun _ => r)
      have heq : RCadd
          (RCscale (1-r) (BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1 x x))
          (RCscale r (BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1 x x)) =
          BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1 x x := by
        rw [← completedInner_smul_right, ← completedInner_smul_right,
          ← completedInner_add_right, completedAdd_smul,
          completedSmul_congr hw0 hw1 hp, completedSmul_one]
      rw [heq] at h
      exact h

/-- Squared tail distance with the sharp geometric factor `r^(2n)`. -/
theorem partial_tail_bound (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q'))
    (n k : Nat) (x : V) :
    RCle (completedDist hw0 hw1
      (rootPartial hw0 hw1 depth r (n+k) x)
      (rootPartial hw0 hw1 depth r n x))
      (RCscale (r^n*r^n)
        (BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1 x x)) := by
  rw [partial_split]
  unfold completedDist
  rw [show completedSub hw0 hw1
      (A (rootPartial hw0 hw1 depth r n x)
        (S (r^n) (M depth n (rootPartial hw0 hw1 depth r k x))))
      (rootPartial hw0 hw1 depth r n x) =
      S (r^n) (M depth n (rootPartial hw0 hw1 depth r k x)) by
        unfold completedSub
        rw [completedAdd_comm hw0 hw1 (rootPartial hw0 hw1 depth r n x),
          completedAdd_assoc,
          completedAdd_comm hw0 hw1 (rootPartial hw0 hw1 depth r n x)
            (completedNeg hw0 hw1 (rootPartial hw0 hw1 depth r n x)),
          completedNeg_add, completedAdd_zero]]
  rw [completedInner_smul_left, completedInner_smul_right, RCscale_RCscale]
  exact RCle_trans
    (RCscale_mono (Q'.mul_nonneg _ _
      (Q'.pow_nonneg r hr0 n) (Q'.pow_nonneg r hr0 n))
      (mesh_norm_bound hw0 hw1 depth n _))
    (RCscale_mono (Q'.mul_nonneg _ _
      (Q'.pow_nonneg r hr0 n) (Q'.pow_nonneg r hr0 n))
      (partial_norm_bound hw0 hw1 depth r hr0 hr1 k x))

/-- The actual Cauchy representative of each finite partial sum. -/
def partialRepresentative (depth : Nat) (r : Q') : Nat → (D).Cauchy → (D).Cauchy
  | 0, _ => (D).constant (zero width)
  | n+1, X => (addition hw0 hw1).mapCauchy
      ((scalarContinuous hw0 hw1 (1-r)).mapCauchy X)
      ((scalarContinuous hw0 hw1 r).mapCauchy
        (rootRepresentative hw0 hw1 depth
          (partialRepresentative depth r n X)))

theorem partialRepresentative_pin (depth : Nat) (r : Q') (n : Nat)
    (X : (D).Cauchy) :
    Class (partialRepresentative hw0 hw1 depth r n X) =
      rootPartial hw0 hw1 depth r n (Class X) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change A (S (1-r) (Class X))
        (S r (Class (rootRepresentative hw0 hw1 depth
          (partialRepresentative hw0 hw1 depth r n X)))) = _
      rw [rootRepresentative_pin, ih]
      rfl

#print axioms rootPartial
#print axioms partial_add
#print axioms partial_smul
#print axioms partial_sub
#print axioms partial_root_commute
#print axioms partial_mesh_commute
#print axioms partial_split
#print axioms partial_norm_bound
#print axioms partial_tail_bound
#print axioms partialRepresentative
#print axioms partialRepresentative_pin

end YMGap.Continuum.BF4WilsonAllNomeRootResolventPartial
