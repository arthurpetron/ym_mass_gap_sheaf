/-
# Closing the per-factor chain: the two pure `CReal` ring identities

`RcAlgResidualClose.RcRingResidual q k θ` has exactly two Type-level fields —
`step0` and `regroup` — the honest residual left after all analytic and rational
content was discharged upstream.  Each is a **pure `CReal` ring identity** that,
by index-wise reduction (`SumOfSquares.Equiv_of_approx_eqv`), collapses to a
multivariate `Q'` ring identity, once ONE trig congruence citation is applied:

* `regroup` — leg 1 rewrites `cosFull(2θ+2h)` via the addition law
  `JacobiQuadResidualClose.cosFull_add_signed`; leg 2 is the pointwise `Q'`
  identity `regroup_pt`.
* `step0`   — leg 1 aligns `cosFull(2·(θ+h)) → cosFull(2θ+2h)` via
  `TrigSignedAddFull.cosFull_argeqv (Q'.mul_add_eqv …)`; leg 2 is the pointwise
  `Q'` identity `step0_pt`.

Both `Q'` identities are proved here from first principles, hand-chained from the
primitive `Q'.*_eqv` ring lemmas (there is no multivariate `Q'` ring tactic;
`QPoly.poly_eqv` is univariate Horner only).  Inhabiting `RcRingResidual` makes
the whole per-factor chain `RcAlgResidual → RcQuadResidual → jacobiFactorFDDeriv`
UNCONDITIONAL — the closure corollaries `rcAlgResidual` and `fdderiv` are derived
at the end.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.
-/

import YMGap.Continuum.RcAlgResidualClose
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.RcRingResidualClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.JacobiFactorFDDeriv (Fk dk)
open YMGap.Continuum.JTPInstance (amp)

local infix:50 " ≈ " => Q'.eqv

/-- Local `Trans` instance so `calc` chains over `Q'.eqv` type-check. -/
instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

/-! ## 1. Primitive `Q'` rearrangement atoms -/

/-- `(-a) + (-b) ≈ -(a+b)` (via `q_eqv_of_sub_zero` + primitive rearrangement). -/
theorem negAddRev (a b : Q') : ((-a) + (-b)) ≈ (-(a + b)) := by
  apply QPoly.q_eqv_of_sub_zero
  have hmid : (((-a) + (-b)) + (a + b)) ≈ (0 : Q') := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (-a) (-b) (a + b)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-a) ((-b) + (a + b)) (((-b) + a) + b)
        (Q'.eqv_symm (Q'.add_assoc_eqv (-b) a b))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-a) (((-b) + a) + b) ((a + (-b)) + b)
        (Q'.add_eqv_congr_right ((-b) + a) (a + (-b)) b (Q'.add_comm_eqv (-b) a))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-a) ((a + (-b)) + b) (a + ((-b) + b))
        (Q'.add_assoc_eqv a (-b) b)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-a) (a + ((-b) + b)) (a + 0)
        (Q'.add_eqv_congr_left a ((-b) + b) 0 (Q'.neg_add_self_eqv b))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-a) (a + 0) a (QPoly.q_add_zero_eqv a)) ?_
    exact Q'.neg_add_self_eqv a
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left ((-a) + (-b)) (-(-(a + b))) (a + b) (Q'.neg_neg_eqv (a + b)))
    hmid

/-- `-(a+b) ≈ (-a) + (-b)`. -/
theorem negAdd (a b : Q') : (-(a + b)) ≈ ((-a) + (-b)) := Q'.eqv_symm (negAddRev a b)

/-- `a + -a ≈ 0`. -/
theorem addNegSelf (a : Q') : (a + -a) ≈ (0 : Q') :=
  Q'.eqv_trans _ _ _ (Q'.add_comm_eqv a (-a)) (Q'.neg_add_self_eqv a)

/-- `o + (p + w) ≈ p + (o + w)` (pull the middle summand out front). -/
theorem reassocMid (o p w : Q') : (o + (p + w)) ≈ (p + (o + w)) := by
  calc o + (p + w)
      ≈ (o + p) + w := Q'.eqv_symm (Q'.add_assoc_eqv o p w)
    _ ≈ (p + o) + w := Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv o p)
    _ ≈ p + (o + w) := Q'.add_assoc_eqv p o w

/-- `s + (-Y + -s) ≈ -Y` (cancel `s` against `-s`). -/
theorem midCancel (s Y : Q') : (s + (-Y + -s)) ≈ (-Y) := by
  calc s + (-Y + -s)
      ≈ (s + -Y) + -s := Q'.eqv_symm (Q'.add_assoc_eqv s (-Y) (-s))
    _ ≈ (-Y + s) + -s := Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv s (-Y))
    _ ≈ -Y + (s + -s) := Q'.add_assoc_eqv (-Y) s (-s)
    _ ≈ -Y + 0 := Q'.add_eqv_congr_left _ _ _ (addNegSelf s)
    _ ≈ -Y := QPoly.q_add_zero_eqv (-Y)

/-- `(X + s) + -(Y + s) ≈ X + -Y` (cancel the common summand `s`). -/
theorem diffCommon (X Y s : Q') : ((X + s) + -(Y + s)) ≈ (X + -Y) := by
  calc (X + s) + -(Y + s)
      ≈ (X + s) + (-Y + -s) := Q'.add_eqv_congr_left _ _ _ (negAdd Y s)
    _ ≈ X + (s + (-Y + -s)) := Q'.add_assoc_eqv X s (-Y + -s)
    _ ≈ X + -Y := Q'.add_eqv_congr_left _ _ _ (midCancel s Y)

/-- `(o + (p + w)) + -(o + (q + w)) ≈ p + -q` (the constant/`w`-telescoping). -/
theorem bracketReduce (o p q w : Q') :
    ((o + (p + w)) + -(o + (q + w))) ≈ (p + -q) := by
  calc (o + (p + w)) + -(o + (q + w))
      ≈ (p + (o + w)) + -(o + (q + w)) :=
        Q'.add_eqv_congr_right _ _ _ (reassocMid o p w)
    _ ≈ (p + (o + w)) + -(q + (o + w)) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (reassocMid o q w))
    _ ≈ p + -q := diffCommon p q (o + w)

/-- `(X + Y) + Z ≈ (X + Z) + Y` (swap the two trailing summands). -/
theorem addSwapR (X Y Z : Q') : ((X + Y) + Z) ≈ ((X + Z) + Y) := by
  calc (X + Y) + Z
      ≈ X + (Y + Z) := Q'.add_assoc_eqv X Y Z
    _ ≈ X + (Z + Y) := Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv Y Z)
    _ ≈ (X + Z) + Y := Q'.eqv_symm (Q'.add_assoc_eqv X Z Y)

/-- `c · (-1) ≈ -c`. -/
theorem mulOneNeg (c : Q') : (c * -(1 : Q')) ≈ (-c) :=
  Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv c 1) (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv c))

/-- `(2 : Q')·x ≈ x + x`. -/
theorem twoMul (x : Q') : ((2 : Q') * x) ≈ (x + x) := by
  calc (2 : Q') * x
      ≈ ((1 : Q') + (1 : Q')) * x := Q'.mul_eqv_congr_right _ _ _ (by decide)
    _ ≈ (1 : Q') * x + (1 : Q') * x := RcAlgResidualClose.add_mul_eqv 1 1 x
    _ ≈ x + (1 : Q') * x := Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv x)
    _ ≈ x + x := Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv x)

/-- `-((-u)·h) ≈ u·h`. -/
theorem negNegMul (u h : Q') : (-((-u) * h)) ≈ (u * h) :=
  Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.neg_mul_eqv u h)) (Q'.neg_neg_eqv (u * h))

/-- `((A+A)·s)·h ≈ A·((2·h)·s)` (the `fourAmp = 2·(amp+amp)` factorization). -/
theorem thirdEq (A s hh : Q') :
    (((A + A) * s) * hh) ≈ (A * (((2 : Q') * hh) * s)) := by
  have left : (((A + A) * s) * hh) ≈ (A * (hh * s) + A * (hh * s)) := by
    calc ((A + A) * s) * hh
        ≈ (A + A) * (s * hh) := Q'.mul_assoc_eqv (A + A) s hh
      _ ≈ (A + A) * (hh * s) := Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv s hh)
      _ ≈ A * (hh * s) + A * (hh * s) := RcAlgResidualClose.add_mul_eqv A A (hh * s)
  have right : (A * (((2 : Q') * hh) * s)) ≈ (A * (hh * s) + A * (hh * s)) := by
    calc A * (((2 : Q') * hh) * s)
        ≈ A * ((2 : Q') * (hh * s)) :=
          Q'.mul_eqv_congr_left _ _ _ (Q'.mul_assoc_eqv (2 : Q') hh s)
      _ ≈ A * ((hh * s) + (hh * s)) := Q'.mul_eqv_congr_left _ _ _ (twoMul (hh * s))
      _ ≈ A * (hh * s) + A * (hh * s) := Q'.mul_add_eqv A (hh * s) (hh * s)
  exact Q'.eqv_trans _ _ _ left (Q'.eqv_symm right)

/-- `A·((p + -q) + r) ≈ (A·p + -(A·q)) + A·r`. -/
theorem rhsExpand (A p q r : Q') :
    (A * ((p + -q) + r)) ≈ ((A * p + -(A * q)) + A * r) := by
  calc A * ((p + -q) + r)
      ≈ A * (p + -q) + A * r := Q'.mul_add_eqv A (p + -q) r
    _ ≈ (A * p + A * (-q)) + A * r :=
        Q'.add_eqv_congr_right _ _ _ (Q'.mul_add_eqv A p (-q))
    _ ≈ (A * p + -(A * q)) + A * r :=
        Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv A q))

/-! ## 2. The two pointwise `Q'` ring identities (legs 2) -/

/-- **`regroup_pt`** — the pointwise identity behind the `regroup` field.  Both
sides equal `cc·CC − cc − ss·SS + 2h·ss`. -/
theorem regroup_pt (cc CC ss SS h : Q') :
    (((cc * CC + -(ss * SS)) + -cc) + (((2 : Q') * h) * ss))
      ≈ (cc * (CC + -(1 : Q')) + -(ss * (SS + -((2 : Q') * h)))) := by
  -- LHS ≈ normal form  NF := ((cc·CC + -cc) + -(ss·SS)) + ss·(2h)
  have lhs : (((cc * CC + -(ss * SS)) + -cc) + (((2 : Q') * h) * ss))
      ≈ (((cc * CC + -cc) + -(ss * SS)) + ss * ((2 : Q') * h)) := by
    calc ((cc * CC + -(ss * SS)) + -cc) + (((2 : Q') * h) * ss)
        ≈ ((cc * CC + -cc) + -(ss * SS)) + (((2 : Q') * h) * ss) :=
          Q'.add_eqv_congr_right _ _ _ (addSwapR (cc * CC) (-(ss * SS)) (-cc))
      _ ≈ ((cc * CC + -cc) + -(ss * SS)) + ss * ((2 : Q') * h) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.mul_comm_eqv ((2 : Q') * h) ss)
  -- RHS ≈ NF
  have dstep : (cc * (CC + -(1 : Q'))) ≈ ((cc * CC) + -cc) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv cc CC (-(1 : Q')))
      (Q'.add_eqv_congr_left _ _ _ (mulOneNeg cc))
  have einner : (ss * (SS + -((2 : Q') * h))) ≈ ((ss * SS) + -(ss * ((2 : Q') * h))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv ss SS (-((2 : Q') * h)))
      (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv ss ((2 : Q') * h)))
  have estep : (-(ss * (SS + -((2 : Q') * h)))) ≈ ((-(ss * SS)) + ss * ((2 : Q') * h)) :=
    Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ einner)
      (Q'.eqv_trans _ _ _ (negAdd (ss * SS) (-(ss * ((2 : Q') * h))))
        (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv (ss * ((2 : Q') * h)))))
  have rhs : (cc * (CC + -(1 : Q')) + -(ss * (SS + -((2 : Q') * h))))
      ≈ (((cc * CC + -cc) + -(ss * SS)) + ss * ((2 : Q') * h)) := by
    calc cc * (CC + -(1 : Q')) + -(ss * (SS + -((2 : Q') * h)))
        ≈ (cc * CC + -cc) + -(ss * (SS + -((2 : Q') * h))) :=
          Q'.add_eqv_congr_right _ _ _ dstep
      _ ≈ (cc * CC + -cc) + (-(ss * SS) + ss * ((2 : Q') * h)) :=
          Q'.add_eqv_congr_left _ _ _ estep
      _ ≈ ((cc * CC + -cc) + -(ss * SS)) + ss * ((2 : Q') * h) :=
          Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
  exact Q'.eqv_trans _ _ _ lhs (Q'.eqv_symm rhs)

/-- **`step0_pt`** — the pointwise identity behind the `step0` field.  The `1` and
`a²` constants cancel, `fourAmp = (a+a)+(a+a) = 2·(a+a)` factors the sine term. -/
theorem step0_pt (a c1 c0 s0 h : Q') :
    ((((1 : Q') + ((a + a) * c1 + a * a)) + -((1 : Q') + ((a + a) * c0 + a * a)))
        + -((-(((a + a) + (a + a)) * s0)) * h))
      ≈ ((a + a) * ((c1 + -c0) + (((2 : Q') * h) * s0))) := by
  calc (((1 : Q') + ((a + a) * c1 + a * a)) + -((1 : Q') + ((a + a) * c0 + a * a)))
          + -((-(((a + a) + (a + a)) * s0)) * h)
      ≈ (((1 : Q') + ((a + a) * c1 + a * a)) + -((1 : Q') + ((a + a) * c0 + a * a)))
          + ((((a + a) + (a + a)) * s0) * h) :=
        Q'.add_eqv_congr_left _ _ _ (negNegMul (((a + a) + (a + a)) * s0) h)
    _ ≈ ((a + a) * c1 + -((a + a) * c0)) + ((((a + a) + (a + a)) * s0) * h) :=
        Q'.add_eqv_congr_right _ _ _ (bracketReduce 1 ((a + a) * c1) ((a + a) * c0) (a * a))
    _ ≈ ((a + a) * c1 + -((a + a) * c0)) + ((a + a) * (((2 : Q') * h) * s0)) :=
        Q'.add_eqv_congr_left _ _ _ (thirdEq (a + a) s0 h)
    _ ≈ (a + a) * ((c1 + -c0) + (((2 : Q') * h) * s0)) :=
        Q'.eqv_symm (rhsExpand (a + a) c1 c0 (((2 : Q') * h) * s0))

/-! ## 3. Inhabiting `RcRingResidual` (legs 1 = trig citations, `.trans` leg 2) -/

/-- **The honest residual is inhabited.**  Each field is one trig congruence
citation pushed through the object's nested `add`/`mul` structure, composed by
`.trans` with the pure-`Q'` pointwise identity above. -/
def rcRingResidual (q : Q') (k : Nat) (θ : Q') :
    RcAlgResidualClose.RcRingResidual q k θ where
  step0 := fun h =>
    CReal.Equiv.trans
      (CReal.add_congr_left (CReal.add_congr_left (CReal.add_congr_right
        (CReal.add_congr_left (TrigSignedAdd.mul_congr_right
          (TrigSignedAddFull.cosFull_argeqv (Q'.mul_add_eqv 2 θ h)))))))
      (SumOfSquares.Equiv_of_approx_eqv (fun n =>
        step0_pt (amp q k)
          ((TrigAdd.cosFull ((2 : Q') * θ + (2 : Q') * h)).approx n)
          ((TrigAdd.cosFull ((2 : Q') * θ)).approx n)
          ((TrigAdd.sinFull ((2 : Q') * θ)).approx n) h))
  regroup := fun h =>
    CReal.Equiv.trans
      (CReal.add_congr_left (CReal.add_congr_left
        (JacobiQuadResidualClose.cosFull_add_signed ((2 : Q') * θ) ((2 : Q') * h))))
      (SumOfSquares.Equiv_of_approx_eqv (fun n =>
        regroup_pt
          ((TrigAdd.cosFull ((2 : Q') * θ)).approx n)
          ((TrigAdd.cosFull ((2 : Q') * h)).approx n)
          ((TrigAdd.sinFull ((2 : Q') * θ)).approx n)
          ((TrigAdd.sinFull ((2 : Q') * h)).approx n) h))

/-! ## 4. The per-factor chain, now UNCONDITIONAL -/

/-- `RcSDResidualClose.RcAlgResidual q k θ`, unconditionally. -/
def rcAlgResidual (q : Q') (k : Nat) (θ : Q') :
    RcSDResidualClose.RcAlgResidual q k θ :=
  RcAlgResidualClose.rcAlgResidual_of_ring k θ (rcRingResidual q k θ)

/-- `JacobiQuadResidualClose.RcQuadResidual q k θ`, unconditionally. -/
def rcQuadResidual (q : Q') (hq : (0 : Q') < q) (k : Nat) (θ : Q') :
    JacobiQuadResidualClose.RcQuadResidual q k θ :=
  RcAlgResidualClose.rcQuadResidual_of_ring hq k θ (rcRingResidual q k θ)

/-- The per-factor finite-difference derivative `FDDerivDataC (Fk q k) (dk q k θ) θ`,
unconditionally. -/
def fdderiv (q : Q') (hq : (0 : Q') < q) (k : Nat) (θ : Q') :=
  RcAlgResidualClose.fdderiv_of_ring hq k θ (rcRingResidual q k θ)

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms negAddRev
#print axioms negAdd
#print axioms twoMul
#print axioms thirdEq
#print axioms rhsExpand
#print axioms regroup_pt
#print axioms step0_pt
#print axioms rcRingResidual
#print axioms rcAlgResidual
#print axioms rcQuadResidual
#print axioms fdderiv

end YMGap.Continuum.RcRingResidualClose
