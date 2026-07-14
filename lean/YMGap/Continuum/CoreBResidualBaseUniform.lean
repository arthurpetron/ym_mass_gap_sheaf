/-
# Core-B base-row residual: uniform homogeneous-chain mechanism

For every offset `r`, the range-two window has only two monomials.  After
extracting the common monomial and the square difference, its residual splits
into finitely many homogeneous power chains.  Seven chains have a positive
coefficient and only four are adverse.  This file develops the uniform chain
bound used to pay all four adverse blocks at once; no offset is enumerated.
-/

import YMGap.Continuum.CoreBResidualOffsetTwo

namespace YMGap.Continuum.CoreBResidualBaseUniform

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.CoreBStructuralRecurrence
open YMGap.Continuum.CoreBResidualPotential

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.add_zero,
               Int.zero_add]; ac_rfl))

private theorem add_le_add' {a b c d : Q'} (h1 : a ≤ b) (h2 : c ≤ d) :
    a + c ≤ b + d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right a b c h1)
    (Q'.add_le_add_left b c d h2)

private theorem mul_eqv_congr' {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem coeff_mul_add_eqv (a b x : Q') :
    a * x + b * x ≈ (a + b) * x := by
  have hcomm : a * x + b * x ≈ x * a + x * b :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.mul_comm_eqv a x))
      (Q'.add_eqv_congr_left _ _ _ (Q'.mul_comm_eqv b x))
  exact Q'.eqv_trans _ _ _ hcomm
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv x a b))
      (Q'.mul_comm_eqv x (a + b)))

private theorem four_mul_sum_eqv (a b c d x : Q') :
    a * x + b * x + c * x + d * x ≈ (a + b + c + d) * x := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_right _ _ _ (coeff_mul_add_eqv a b x))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (coeff_mul_add_eqv (a + b) c x)) ?_
  exact coeff_mul_add_eqv (a + b + c) d x

private theorem mul_shuffle_eqv (a b x : Q') :
    (a * b) * x ≈ b * (a * x) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b x) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.mul_comm_eqv b x)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a x b)) ?_
  exact Q'.mul_comm_eqv (a * x) b

private theorem qpow_two_eqv (x : Q') : qpow x 2 ≈ x * x := by
  unfold qpow
  exact Q'.mul_eqv_congr_right _ _ x (Q'.one_mul_eqv x)

private theorem two_mul_eqv (x : Q') : (2 : Q') * x ≈ x + x := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ x (by decide : (2 : Q') ≈ 1 + 1)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 1 x) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv x))
    (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv x))

/-- The homogeneous divided-power chain
`x^(b+n-1)y^b + ... + x^b y^(b+n-1)`, defined recursively in its length. -/
def homChain (x y : Q') (base : Nat) : Nat → Q'
  | 0 => 0
  | n + 1 => qpow x (base + n) * qpow y base + y * homChain x y base n

theorem homChain_nonneg {x y : Q'} (hx0 : (0 : Q') ≤ x)
    (hy0 : (0 : Q') ≤ y) (base : Nat) : ∀ len,
    (0 : Q') ≤ homChain x y base len
  | 0 => Q'.le_refl' 0
  | n + 1 => Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (qpow_nonneg x hx0 _) (qpow_nonneg y hy0 _))
      (Q'.mul_nonneg _ _ hy0 (homChain_nonneg hx0 hy0 base n))

private def factorStepAssocL : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let A := RingNormaliser.PolyExpr.var 2
  let C := RingNormaliser.PolyExpr.var 3
  .mul (.add x (.neg y)) (.add A (.mul y C))

private def factorStepAssocR : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let A := RingNormaliser.PolyExpr.var 2
  let C := RingNormaliser.PolyExpr.var 3
  .add (.mul (.add x (.neg y)) A)
    (.mul y (.mul (.add x (.neg y)) C))

private theorem factorStepAssoc_normal :
    RingNormaliser.normalize factorStepAssocL =
      RingNormaliser.normalize factorStepAssocR := by
  decide

private theorem factor_step_assoc (x y A C : Q') :
    (x + -y) * (A + y * C) ≈
      (x + -y) * A + y * ((x + -y) * C) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _
    factorStepAssoc_normal (fun i => match i with
      | 0 => x | 1 => y | 2 => A | _ => C)
  simpa [factorStepAssocL, factorStepAssocR, RingNormaliser.eval] using hn

private def factorStepCancelL : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let A := RingNormaliser.PolyExpr.var 2
  let V := RingNormaliser.PolyExpr.var 3
  .add (.mul (.add x (.neg y)) A) (.mul y (.add A (.neg V)))

private def factorStepCancelR : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let A := RingNormaliser.PolyExpr.var 2
  let V := RingNormaliser.PolyExpr.var 3
  .add (.mul x A) (.neg (.mul y V))

private theorem factorStepCancel_normal :
    RingNormaliser.normalize factorStepCancelL =
      RingNormaliser.normalize factorStepCancelR := by
  decide

private theorem factor_step_cancel (x y A V : Q') :
    (x + -y) * A + y * (A + -V) ≈ x * A + -(y * V) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _
    factorStepCancel_normal (fun i => match i with
      | 0 => x | 1 => y | 2 => A | _ => V)
  simpa [factorStepCancelL, factorStepCancelR, RingNormaliser.eval] using hn

/-- Exact divided-difference identity for the homogeneous chain. -/
theorem homChain_factor (x y : Q') (base : Nat) : ∀ len,
    (x + -y) * homChain x y base len ≈
      qpow x (base + len) * qpow y base +
        -(qpow x base * qpow y (base + len))
  | 0 => by
      simp only [homChain, Nat.add_zero]
      exact Q'.eqv_trans _ _ _ (Q'.mul_zero_eqv (x + -y))
        (Q'.eqv_symm (Q'.add_neg_self_eqv
          (qpow x base * qpow y base)))
  | n + 1 => by
      let A := qpow x (base + n) * qpow y base
      let V := qpow x base * qpow y (base + n)
      have ih := homChain_factor x y base n
      have hstep : (x + -y) * (A + y * homChain x y base n) ≈
          x * A + -(y * V) := by
        refine Q'.eqv_trans _ _ _ (factor_step_assoc x y A _) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_left y _ _ ih)) ?_
        exact factor_step_cancel x y A V
      have hhigh : x * A ≈
          qpow x (base + (n + 1)) * qpow y base := by
        dsimp [A]
        rw [show base + (n + 1) = (base + n) + 1 by omega]
        change x * (qpow x (base + n) * qpow y base) ≈
          (qpow x (base + n) * x) * qpow y base
        exact Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv x (qpow x (base + n)) (qpow y base)))
          (Q'.mul_eqv_congr_right _ _ (qpow y base)
            (Q'.mul_comm_eqv x (qpow x (base + n))))
      have hlow : y * V ≈
          qpow x base * qpow y (base + (n + 1)) := by
        dsimp [V]
        rw [show base + (n + 1) = (base + n) + 1 by omega]
        change y * (qpow x base * qpow y (base + n)) ≈
          qpow x base * (qpow y (base + n) * y)
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv y (qpow x base) (qpow y (base + n)))) ?_
        refine Q'.eqv_trans _ _ _ (mul_shuffle_eqv y (qpow x base) _) ?_
        exact Q'.mul_eqv_congr_left (qpow x base) _ _
          (Q'.mul_comm_eqv y (qpow y (base + n)))
      show (x + -y) * (A + y * homChain x y base n) ≈ _
      exact Q'.eqv_trans _ _ _ hstep
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ _ hhigh)
          (Q'.add_eqv_congr_left _ _ _
            (Q'.neg_eqv_congr _ _ hlow)))

def crossPair (x y : Q') (p q : Nat) : Q' :=
  qpow x p * qpow y q + -(qpow x q * qpow y p)

theorem crossPair_factor (x y : Q') (base len : Nat) :
    crossPair x y (base + len) base ≈
      (x + -y) * homChain x y base len :=
  Q'.eqv_symm (homChain_factor x y base len)

private theorem crossPair_swap (x y : Q') (p q : Nat) :
    crossPair x y p q ≈ -crossPair x y q p := by
  unfold crossPair
  ring_qeqv

theorem crossPair_factor_neg (x y : Q') (base len : Nat) :
    crossPair x y base (base + len) ≈
      -((x + -y) * homChain x y base len) := by
  exact Q'.eqv_trans _ _ _ (crossPair_swap x y base (base + len))
    (Q'.neg_eqv_congr _ _ (crossPair_factor x y base len))

private def rawCross (x y X Y U V : Q') : Q' :=
  (x * X) * V + -((y * U) * Y)

private theorem rawCross_power (x y : Q') (a b : Nat) :
    rawCross x y (qpow x a) (qpow y a) (qpow x b) (qpow y b) ≈
      crossPair x y (a + 1) b := by
  unfold rawCross crossPair
  change (x * qpow x a) * qpow y b +
      -((y * qpow x b) * qpow y a) ≈
    (qpow x a * x) * qpow y b +
      -(qpow x b * (qpow y a * y))
  refine Q'.add_eqv_congr' ?_ (Q'.neg_eqv_congr _ _ ?_)
  · exact Q'.mul_eqv_congr_right _ _ (qpow y b)
      (Q'.mul_comm_eqv x (qpow x a))
  · refine Q'.eqv_trans _ _ _ (mul_shuffle_eqv y (qpow x b) (qpow y a)) ?_
    exact Q'.mul_eqv_congr_left (qpow x b) _ _
      (Q'.mul_comm_eqv y (qpow y a))

/-- Every nonempty-base homogeneous chain is bounded by `x` when
`0 ≤ y ≤ x` and `2x ≤ 1`.  The induction uses
`C_(n+1) = x^(b+n)y^b + y C_n`: both summands are at most `x²`. -/
theorem homChain_le_x {x y : Q'} (hx0 : (0 : Q') ≤ x)
    (hy0 : (0 : Q') ≤ y) (hyx : y ≤ x)
    (h2x : (2 : Q') * x ≤ (1 : Q')) {base : Nat} (hbase : 1 ≤ base) :
    ∀ len, homChain x y base len ≤ x
  | 0 => hx0
  | n + 1 => by
      have hxle2x := Q'.mul_le_mul_of_nonneg_right 1 2 x
        (by decide : (1 : Q') ≤ 2) hx0
      have hx1 : x ≤ (1 : Q') :=
        Q'.le_trans' _ _ _
          (Q'.le_trans' _ _ _
            (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv x))) hxle2x)
          h2x
      have hpowY : qpow y base ≤ qpow x base := qpow_mono hy0 hyx base
      have hpowX0 : (0 : Q') ≤ qpow x (base + n) := qpow_nonneg x hx0 _
      have hterm0 : qpow x (base + n) * qpow y base ≤
          qpow x (base + n) * qpow x base :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ hpowY hpowX0
      have hexp : 2 ≤ (base + n) + base := by omega
      have hterm1 : qpow x (base + n) * qpow x base ≤ qpow x 2 := by
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.eqv_symm (qpow_add x (base + n) base)))
          (qpow_antitone hx0 hx1 2 ((base + n) + base) hexp)
      have hterm : qpow x (base + n) * qpow y base ≤ x * x :=
        Q'.le_trans' _ _ _ hterm0
          (Q'.le_trans' _ _ _ hterm1 (Q'.le_of_eqv (qpow_two_eqv x)))
      have htail0 : y * homChain x y base n ≤ y * x :=
        Q'.mul_le_mul_of_nonneg_left _ _ _
          (homChain_le_x hx0 hy0 hyx h2x hbase n) hy0
      have htail : y * homChain x y base n ≤ x * x :=
        Q'.le_trans' _ _ _ htail0
          (Q'.mul_le_mul_of_nonneg_right _ _ x hyx hx0)
      have hadd : homChain x y base (n + 1) ≤ x * x + x * x := by
        exact add_le_add' hterm htail
      have hdouble : x * x + x * x ≈ ((2 : Q') * x) * x := by
        exact Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.add_mul_eqv x x x))
          (Q'.mul_eqv_congr_right _ _ x
            (Q'.eqv_symm (two_mul_eqv x)))
      have hscaled := Q'.mul_le_mul_of_nonneg_right ((2 : Q') * x) 1 x
        h2x hx0
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hdouble)
          (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (Q'.one_mul_eqv x))))

/-! ## Coefficients of the range-two window -/

def rq (r : Nat) : Q' := Q'.ofNat r

def a0 (r : Nat) : Q' := (4 : Q') * (rq r + 1) * (rq r + 3)
def a1 (r : Nat) : Q' := (2 : Q') * (rq r + 2) * (rq r + 3)
def a2 (r : Nat) : Q' := (2 : Q') * (rq r + 1) * (rq r + 4)
def a3 (r : Nat) : Q' := (rq r + 2) * (rq r + 4)

def m0 (r : Nat) : Q' := (4 : Q') * (rq r + 2) * (rq r + 2)
def m1 (r : Nat) : Q' := (4 : Q') * (rq r + 2) * (rq r + 3)
def m2 (r : Nat) : Q' := (rq r + 3) * (rq r + 3)

def positiveAnchor (r : Nat) : Q' := a0 r * m0 r

def adverseCoefficientMass (r : Nat) : Q' :=
  a0 r * m1 r + a0 r * m2 r + a1 r * m2 r + a2 r * m2 r

/-- The complete adverse portion of the divided residual for every `r ≥ 1`.
The final chain has length zero at `r = 1`, so the formula is uniform. -/
def adversePart (x y : Q') (r : Nat) : Q' :=
  (a0 r * m1 r) * homChain x y 1 r +
  (a0 r * m2 r) * homChain x y 1 (2 * r + 1) +
  (a1 r * m2 r) * homChain x y (r + 1) (r + 1) +
  (a2 r * m2 r) * homChain x y (r + 3) (r - 1)

/-- The six surviving positive chains after the highest pair is telescoped
against the preceding base-row residual. -/
def positiveTail (x y : Q') (r : Nat) : Q' :=
  (a1 r * m0 r) * homChain x y 0 (r + 1) +
  (a2 r * m0 r) * homChain x y 0 (r + 3) +
  (a2 r * m1 r) * homChain x y (r + 1) 2 +
  (a3 r * m0 r) * homChain x y 0 (2 * r + 3) +
  (a3 r * m1 r) * homChain x y (r + 1) (r + 2)

/-- Reduced divided residual: its constant anchor and positive tail, less the
four adverse chains. -/
def reducedPart (x y : Q') (r : Nat) : Q' :=
  positiveAnchor r + -adversePart x y r + positiveTail x y r

def aPoly (x : Q') (r : Nat) : Q' :=
  a0 r + a1 r * qpow x r + a2 r * qpow x (r + 2) +
    a3 r * qpow x (2 * r + 2)

def mPoly (x : Q') (r : Nat) : Q' :=
  m0 r + m1 r * qpow x (r + 1) + m2 r * qpow x (2 * r + 2)

def terminalPart (x y : Q') (r : Nat) : Q' :=
  (a3 r * m2 r) * homChain x y (2 * r + 2) 1

private def add12 (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 : Q') : Q' :=
  ((z0 + z1 + z2) + (z3 + z4 + z5)) + (z6 + z7 + z8) + (z9 + z10 + z11)

private theorem add12_eqv {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Q'}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Q'}
    (h0 : a0 ≈ b0) (h1 : a1 ≈ b1) (h2 : a2 ≈ b2)
    (h3 : a3 ≈ b3) (h4 : a4 ≈ b4) (h5 : a5 ≈ b5)
    (h6 : a6 ≈ b6) (h7 : a7 ≈ b7) (h8 : a8 ≈ b8)
    (h9 : a9 ≈ b9) (h10 : a10 ≈ b10) (h11 : a11 ≈ b11) :
    add12 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 ≈
      add12 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 := by
  unfold add12
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.add_eqv_congr' h0 h1) h2)
        (Q'.add_eqv_congr' (Q'.add_eqv_congr' h3 h4) h5))
      (Q'.add_eqv_congr' (Q'.add_eqv_congr' h6 h7) h8))
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' h9 h10) h11)

private def rawPairSum (x y : Q') (r : Nat) : Q' :=
  add12
    ((a0 r * m0 r) * rawCross x y (qpow x 0) (qpow y 0) (qpow x 0) (qpow y 0))
    ((a0 r * m1 r) * rawCross x y (qpow x 0) (qpow y 0)
      (qpow x (r + 1)) (qpow y (r + 1)))
    ((a0 r * m2 r) * rawCross x y (qpow x 0) (qpow y 0)
      (qpow x (2 * r + 2)) (qpow y (2 * r + 2)))
    ((a1 r * m0 r) * rawCross x y (qpow x r) (qpow y r) (qpow x 0) (qpow y 0))
    ((a1 r * m1 r) * rawCross x y (qpow x r) (qpow y r)
      (qpow x (r + 1)) (qpow y (r + 1)))
    ((a1 r * m2 r) * rawCross x y (qpow x r) (qpow y r)
      (qpow x (2 * r + 2)) (qpow y (2 * r + 2)))
    ((a2 r * m0 r) * rawCross x y (qpow x (r + 2)) (qpow y (r + 2))
      (qpow x 0) (qpow y 0))
    ((a2 r * m1 r) * rawCross x y (qpow x (r + 2)) (qpow y (r + 2))
      (qpow x (r + 1)) (qpow y (r + 1)))
    ((a2 r * m2 r) * rawCross x y (qpow x (r + 2)) (qpow y (r + 2))
      (qpow x (2 * r + 2)) (qpow y (2 * r + 2)))
    ((a3 r * m0 r) * rawCross x y (qpow x (2 * r + 2)) (qpow y (2 * r + 2))
      (qpow x 0) (qpow y 0))
    ((a3 r * m1 r) * rawCross x y (qpow x (2 * r + 2)) (qpow y (2 * r + 2))
      (qpow x (r + 1)) (qpow y (r + 1)))
    ((a3 r * m2 r) * rawCross x y (qpow x (2 * r + 2)) (qpow y (2 * r + 2))
      (qpow x (2 * r + 2)) (qpow y (2 * r + 2)))

private def aCoeff (r : Nat) : Nat → Q'
  | 0 => a0 r | 1 => a1 r | 2 => a2 r | _ => a3 r

private def aExp (r : Nat) : Nat → Nat
  | 0 => 0 | 1 => r | 2 => r + 2 | _ => 2 * r + 2

private def mCoeff (r : Nat) : Nat → Q'
  | 0 => m0 r | 1 => m1 r | _ => m2 r

private def mExp (r : Nat) : Nat → Nat
  | 0 => 0 | 1 => r + 1 | _ => 2 * r + 2

private def aComponent (x : Q') (r i : Nat) : Q' :=
  aCoeff r i * qpow x (aExp r i)

private def xaComponent (x : Q') (r i : Nat) : Q' :=
  x * aComponent x r i

private def mComponent (x : Q') (r i : Nat) : Q' :=
  mCoeff r i * qpow x (mExp r i)

private theorem aPoly_fsum (x : Q') (r : Nat) :
    fsum (aComponent x r) 4 ≈ aPoly x r := by
  unfold aComponent aCoeff aExp aPoly
  simp only [fsum_succ, fsum_zero]
  rw [Q'.zero_add']
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.mul_one_eqv (a0 r)) (Q'.eqv_refl _))
      (Q'.eqv_refl _))
    (Q'.eqv_refl _)

private theorem mPoly_fsum (x : Q') (r : Nat) :
    fsum (mComponent x r) 3 ≈ mPoly x r := by
  unfold mComponent mCoeff mExp mPoly
  simp only [fsum_succ, fsum_zero]
  rw [Q'.zero_add']
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (Q'.mul_one_eqv (m0 r)) (Q'.eqv_refl _))
    (Q'.eqv_refl _)

private theorem xaPoly_fsum (x : Q') (r : Nat) :
    fsum (xaComponent x r) 4 ≈ x * aPoly x r := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (fsum_const_mul x (aComponent x r) 4))
    (Q'.mul_eqv_congr_left x _ _ (aPoly_fsum x r))

private def componentMinorL : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let a := RingNormaliser.PolyExpr.var 2
  let m := RingNormaliser.PolyExpr.var 3
  let X := RingNormaliser.PolyExpr.var 4
  let Y := RingNormaliser.PolyExpr.var 5
  let U := RingNormaliser.PolyExpr.var 6
  let V := RingNormaliser.PolyExpr.var 7
  .add (.mul (.mul x (.mul a X)) (.mul m V))
    (.neg (.mul (.mul m U) (.mul y (.mul a Y))))

private def componentMinorR : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let a := RingNormaliser.PolyExpr.var 2
  let m := RingNormaliser.PolyExpr.var 3
  let X := RingNormaliser.PolyExpr.var 4
  let Y := RingNormaliser.PolyExpr.var 5
  let U := RingNormaliser.PolyExpr.var 6
  let V := RingNormaliser.PolyExpr.var 7
  .mul (.mul a m)
    (.add (.mul (.mul x X) V) (.neg (.mul (.mul y U) Y)))

private theorem componentMinor_normal :
    RingNormaliser.normalize componentMinorL =
      RingNormaliser.normalize componentMinorR := by
  decide

private theorem componentMinor_eq_raw (x y a m X Y U V : Q') :
    determinant (x * (a * X)) (y * (a * Y)) (m * U) (m * V) ≈
      (a * m) * rawCross x y X Y U V := by
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _
    componentMinor_normal (fun i => match i with
      | 0 => x | 1 => y | 2 => a | 3 => m | 4 => X | 5 => Y | 6 => U | _ => V)
  simpa [componentMinorL, componentMinorR, determinant, rawCross,
    RingNormaliser.eval] using hn

private def rawDoubleSum (x y : Q') (r : Nat) : Q' :=
  fsum (fun i => fsum (fun j =>
    (aCoeff r i * mCoeff r j) *
      rawCross x y (qpow x (aExp r i)) (qpow y (aExp r i))
        (qpow x (mExp r j)) (qpow y (mExp r j))) 3) 4

private theorem rawDoubleSum_eq_rawPairSum (x y : Q') (r : Nat) :
    rawDoubleSum x y r ≈ rawPairSum x y r := by
  unfold rawDoubleSum rawPairSum add12 aCoeff aExp mCoeff mExp
  simp only [fsum_succ, fsum_zero]
  repeat' rw [Q'.zero_add']
  exact Q'.eqv_refl _

private theorem polyDet_eq_rawPairSum (x y : Q') (r : Nat) :
    x * aPoly x r * mPoly y r + -(y * mPoly x r * aPoly y r) ≈
      rawPairSum x y r := by
  have hA := aPoly_fsum x r
  have hAh := aPoly_fsum y r
  have hM := mPoly_fsum x r
  have hMh := mPoly_fsum y r
  have hxA := xaPoly_fsum x r
  have hyA := xaPoly_fsum y r
  have hinput : determinant (x * aPoly x r) (y * aPoly y r)
      (mPoly x r) (mPoly y r) ≈
      determinant (fsum (xaComponent x r) 4) (fsum (xaComponent y r) 4)
        (fsum (mComponent x r) 3) (fsum (mComponent y r) 3) := by
    unfold determinant
    exact Q'.add_eqv_congr'
      (mul_eqv_congr' (Q'.eqv_symm hxA) (Q'.eqv_symm hMh))
      (Q'.neg_eqv_congr _ _
        (mul_eqv_congr' (Q'.eqv_symm hM) (Q'.eqv_symm hyA)))
  have hdet := determinant_fsum (xaComponent x r) (xaComponent y r)
    (mComponent x r) (mComponent y r) 4 3
  have hterms :
      fsum (fun i => fsum (fun j =>
        determinant (xaComponent x r i) (xaComponent y r i)
          (mComponent x r j) (mComponent y r j)) 3) 4 ≈
        rawDoubleSum x y r := by
    unfold rawDoubleSum
    apply fsum_eqv_congr
    intro i
    apply fsum_eqv_congr
    intro j
    unfold xaComponent aComponent mComponent
    exact componentMinor_eq_raw x y (aCoeff r i) (mCoeff r j)
      (qpow x (aExp r i)) (qpow y (aExp r i))
      (qpow x (mExp r j)) (qpow y (mExp r j))
  have hshape : x * aPoly x r * mPoly y r +
      -(y * mPoly x r * aPoly y r) ≈
      determinant (x * aPoly x r) (y * aPoly y r)
        (mPoly x r) (mPoly y r) := by
    unfold determinant
    exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _
        (mul_shuffle_eqv y (mPoly x r) (aPoly y r)))
  exact Q'.eqv_trans _ _ _ hshape
    (Q'.eqv_trans _ _ _ hinput
    (Q'.eqv_trans _ _ _ hdet
      (Q'.eqv_trans _ _ _ hterms (rawDoubleSum_eq_rawPairSum x y r))))

private theorem rawTerm_factor_pos (c x y : Q') (a b base len : Nat)
    (ha : a + 1 = base + len) (hb : b = base) :
    c * rawCross x y (qpow x a) (qpow y a) (qpow x b) (qpow y b) ≈
      c * ((x + -y) * homChain x y base len) := by
  refine Q'.mul_eqv_congr_left c _ _ ?_
  refine Q'.eqv_trans _ _ _ (rawCross_power x y a b) ?_
  rw [ha, hb]
  exact crossPair_factor x y base len

private theorem rawTerm_factor_neg (c x y : Q') (a b base len : Nat)
    (ha : a + 1 = base) (hb : b = base + len) :
    c * rawCross x y (qpow x a) (qpow y a) (qpow x b) (qpow y b) ≈
      c * (-((x + -y) * homChain x y base len)) := by
  refine Q'.mul_eqv_congr_left c _ _ ?_
  refine Q'.eqv_trans _ _ _ (rawCross_power x y a b) ?_
  rw [ha, hb]
  exact crossPair_factor_neg x y base len

private theorem rawTerm_zero (c x y : Q') (a b : Nat) (hab : a + 1 = b) :
    c * rawCross x y (qpow x a) (qpow y a) (qpow x b) (qpow y b) ≈ 0 := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _ (rawCross_power x y a b)) ?_
  rw [hab]
  unfold crossPair
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _
      (Q'.add_neg_self_eqv (qpow x b * qpow y b)))
    (Q'.mul_zero_eqv c)

private theorem homChain_zero_one (x y : Q') : homChain x y 0 1 ≈ 1 := by
  unfold homChain qpow
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (1 * 1) _ _ (Q'.mul_zero_eqv y))
    (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' (1 * 1)))
      (Q'.one_mul_eqv 1))

private def classifiedPairSum (x y : Q') (r : Nat) : Q' :=
  let d := x + -y
  add12
    ((a0 r * m0 r) * (d * homChain x y 0 1))
    ((a0 r * m1 r) * (-(d * homChain x y 1 r)))
    ((a0 r * m2 r) * (-(d * homChain x y 1 (2 * r + 1))))
    ((a1 r * m0 r) * (d * homChain x y 0 (r + 1)))
    0
    ((a1 r * m2 r) * (-(d * homChain x y (r + 1) (r + 1))))
    ((a2 r * m0 r) * (d * homChain x y 0 (r + 3)))
    ((a2 r * m1 r) * (d * homChain x y (r + 1) 2))
    ((a2 r * m2 r) * (-(d * homChain x y (r + 3) (r - 1))))
    ((a3 r * m0 r) * (d * homChain x y 0 (2 * r + 3)))
    ((a3 r * m1 r) * (d * homChain x y (r + 1) (r + 2)))
    ((a3 r * m2 r) * (d * homChain x y (2 * r + 2) 1))

private theorem rawPairSum_eq_classified {x y : Q'} {r : Nat} (hr : 1 ≤ r) :
    rawPairSum x y r ≈ classifiedPairSum x y r := by
  unfold rawPairSum classifiedPairSum
  apply add12_eqv
  · exact rawTerm_factor_pos _ x y 0 0 0 1 (by omega) rfl
  · exact rawTerm_factor_neg _ x y 0 (r + 1) 1 r (by omega) (by omega)
  · exact rawTerm_factor_neg _ x y 0 (2 * r + 2) 1 (2 * r + 1)
      (by omega) (by omega)
  · exact rawTerm_factor_pos _ x y r 0 0 (r + 1) (by omega) rfl
  · exact rawTerm_zero _ x y r (r + 1) (by omega)
  · exact rawTerm_factor_neg _ x y r (2 * r + 2) (r + 1) (r + 1)
      (by omega) (by omega)
  · exact rawTerm_factor_pos _ x y (r + 2) 0 0 (r + 3) (by omega) rfl
  · exact rawTerm_factor_pos _ x y (r + 2) (r + 1) (r + 1) 2
      (by omega) rfl
  · exact rawTerm_factor_neg _ x y (r + 2) (2 * r + 2) (r + 3) (r - 1)
      (by omega) (by omega)
  · exact rawTerm_factor_pos _ x y (2 * r + 2) 0 0 (2 * r + 3)
      (by omega) rfl
  · exact rawTerm_factor_pos _ x y (2 * r + 2) (r + 1) (r + 1) (r + 2)
      (by omega) rfl
  · exact rawTerm_factor_pos _ x y (2 * r + 2) (2 * r + 2) (2 * r + 2) 1
      (by omega) rfl

private theorem coeff_factor_pos (c d z : Q') :
    c * (d * z) ≈ d * (c * z) := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv c d z))
    (mul_shuffle_eqv c d z)

private theorem coeff_factor_neg (c d z : Q') :
    c * (-(d * z)) ≈ d * (-(c * z)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv c (d * z)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.neg_eqv_congr _ _ (coeff_factor_pos c d z)) ?_
  exact Q'.eqv_symm (Q'.mul_neg_eqv d (c * z))

private theorem left_factor_three (d a b c : Q') :
    d * a + d * b + d * c ≈ d * (a + b + c) := by
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv d a b)))
    (Q'.eqv_symm (Q'.mul_add_eqv d (a + b) c))

private theorem left_factor_four (d a b c e : Q') :
    d * a + d * b + d * c + d * e ≈ d * (a + b + c + e) := by
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (left_factor_three d a b c))
    (Q'.eqv_symm (Q'.mul_add_eqv d (a + b + c) e))

private theorem add12_left_factor (d z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 : Q') :
    add12 (d*z0) (d*z1) (d*z2) (d*z3) (d*z4) (d*z5)
      (d*z6) (d*z7) (d*z8) (d*z9) (d*z10) (d*z11) ≈
      d * add12 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 := by
  unfold add12
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (left_factor_three d z0 z1 z2)
          (left_factor_three d z3 z4 z5))
        (left_factor_three d z6 z7 z8))
      (left_factor_three d z9 z10 z11)) ?_
  exact left_factor_four d (z0 + z1 + z2) (z3 + z4 + z5)
    (z6 + z7 + z8) (z9 + z10 + z11)

private def classifiedInner (x y : Q') (r : Nat) : Q' :=
  add12
    ((a0 r * m0 r) * homChain x y 0 1)
    (-((a0 r * m1 r) * homChain x y 1 r))
    (-((a0 r * m2 r) * homChain x y 1 (2 * r + 1)))
    ((a1 r * m0 r) * homChain x y 0 (r + 1))
    0
    (-((a1 r * m2 r) * homChain x y (r + 1) (r + 1)))
    ((a2 r * m0 r) * homChain x y 0 (r + 3))
    ((a2 r * m1 r) * homChain x y (r + 1) 2)
    (-((a2 r * m2 r) * homChain x y (r + 3) (r - 1)))
    ((a3 r * m0 r) * homChain x y 0 (2 * r + 3))
    ((a3 r * m1 r) * homChain x y (r + 1) (r + 2))
    ((a3 r * m2 r) * homChain x y (2 * r + 2) 1)

private theorem classifiedPairSum_factor (x y : Q') (r : Nat) :
    classifiedPairSum x y r ≈ (x + -y) * classifiedInner x y r := by
  let d := x + -y
  unfold classifiedPairSum classifiedInner
  refine Q'.eqv_trans _ _ _ (add12_eqv
    (coeff_factor_pos (a0 r * m0 r) d _)
    (coeff_factor_neg (a0 r * m1 r) d _)
    (coeff_factor_neg (a0 r * m2 r) d _)
    (coeff_factor_pos (a1 r * m0 r) d _)
    (Q'.eqv_symm (Q'.mul_zero_eqv d))
    (coeff_factor_neg (a1 r * m2 r) d _)
    (coeff_factor_pos (a2 r * m0 r) d _)
    (coeff_factor_pos (a2 r * m1 r) d _)
    (coeff_factor_neg (a2 r * m2 r) d _)
    (coeff_factor_pos (a3 r * m0 r) d _)
    (coeff_factor_pos (a3 r * m1 r) d _)
    (coeff_factor_pos (a3 r * m2 r) d _)) ?_
  exact add12_left_factor d _ _ _ _ _ _ _ _ _ _ _ _

private def innerAssocL : RingNormaliser.PolyExpr :=
  let z := fun n => RingNormaliser.PolyExpr.var n
  .add (.add (.add
    (.add (.add (z 0) (.neg (z 1))) (.neg (z 2)))
    (.add (.add (z 5) (.const 0)) (.neg (z 3))))
    (.add (.add (z 6) (z 7)) (.neg (z 4))))
    (.add (.add (z 8) (z 9)) (z 10))

private def innerAssocR : RingNormaliser.PolyExpr :=
  let z := fun n => RingNormaliser.PolyExpr.var n
  .add
    (.add
      (.add (z 0)
        (.neg (.add (.add (.add (z 1) (z 2)) (z 3)) (z 4))))
      (.add (.add (.add (.add (z 5) (z 6)) (z 7)) (z 8)) (z 9)))
    (z 10)

private theorem innerAssoc_normal : RingNormaliser.normalize innerAssocL =
    RingNormaliser.normalize innerAssocR := by
  decide

private def reducedChainPart (x y : Q') (r : Nat) : Q' :=
  (positiveAnchor r * homChain x y 0 1) + -adversePart x y r + positiveTail x y r

private theorem classifiedInner_eq (x y : Q') (r : Nat) :
    classifiedInner x y r ≈ reducedChainPart x y r + terminalPart x y r := by
  let z : Nat → Q' := fun n => match n with
    | 0 => positiveAnchor r * homChain x y 0 1
    | 1 => (a0 r * m1 r) * homChain x y 1 r
    | 2 => (a0 r * m2 r) * homChain x y 1 (2 * r + 1)
    | 3 => (a1 r * m2 r) * homChain x y (r + 1) (r + 1)
    | 4 => (a2 r * m2 r) * homChain x y (r + 3) (r - 1)
    | 5 => (a1 r * m0 r) * homChain x y 0 (r + 1)
    | 6 => (a2 r * m0 r) * homChain x y 0 (r + 3)
    | 7 => (a2 r * m1 r) * homChain x y (r + 1) 2
    | 8 => (a3 r * m0 r) * homChain x y 0 (2 * r + 3)
    | 9 => (a3 r * m1 r) * homChain x y (r + 1) (r + 2)
    | _ => (a3 r * m2 r) * homChain x y (2 * r + 2) 1
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _ innerAssoc_normal z
  simpa [innerAssocL, innerAssocR, classifiedInner, reducedChainPart,
    positiveAnchor, adversePart, positiveTail, terminalPart, add12,
    RingNormaliser.eval, z] using hn

private theorem reducedChainPart_eq (x y : Q') (r : Nat) :
    reducedChainPart x y r ≈ reducedPart x y r := by
  unfold reducedChainPart reducedPart
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (positiveAnchor r) _ _ (homChain_zero_one x y))
        (Q'.mul_one_eqv (positiveAnchor r))))

/-- Exact algebraic base-row factorization after the terminal range-one pair
has been removed. -/
theorem polyResidual_factor {x y : Q'} {r : Nat} (hr : 1 ≤ r) :
    x * aPoly x r * mPoly y r + -(y * mPoly x r * aPoly y r) ≈
      (x + -y) * (reducedPart x y r + terminalPart x y r) := by
  exact Q'.eqv_trans _ _ _ (polyDet_eq_rawPairSum x y r)
    (Q'.eqv_trans _ _ _ (rawPairSum_eq_classified hr)
      (Q'.eqv_trans _ _ _ (classifiedPairSum_factor x y r)
        (Q'.mul_eqv_congr_left (x + -y) _ _
          (Q'.eqv_trans _ _ _ (classifiedInner_eq x y r)
            (Q'.add_eqv_congr_right _ _ _ (reducedChainPart_eq x y r))))))

theorem rq_nonneg (r : Nat) : (0 : Q') ≤ rq r := by
  unfold rq
  exact zero_le_ofNat r

theorem a0_nonneg (r : Nat) : (0 : Q') ≤ a0 r := by
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _ (rq_nonneg r) (by decide)))
    (Q'.zero_le_add _ _ (rq_nonneg r) (by decide))

theorem a1_nonneg (r : Nat) : (0 : Q') ≤ a1 r := by
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _ (rq_nonneg r) (by decide)))
    (Q'.zero_le_add _ _ (rq_nonneg r) (by decide))

theorem a2_nonneg (r : Nat) : (0 : Q') ≤ a2 r := by
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _ (rq_nonneg r) (by decide)))
    (Q'.zero_le_add _ _ (rq_nonneg r) (by decide))

theorem a3_nonneg (r : Nat) : (0 : Q') ≤ a3 r := by
  exact Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ (rq_nonneg r) (by decide))
    (Q'.zero_le_add _ _ (rq_nonneg r) (by decide))

theorem m0_nonneg (r : Nat) : (0 : Q') ≤ m0 r := by
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _ (rq_nonneg r) (by decide)))
    (Q'.zero_le_add _ _ (rq_nonneg r) (by decide))

theorem m1_nonneg (r : Nat) : (0 : Q') ≤ m1 r := by
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _ (rq_nonneg r) (by decide)))
    (Q'.zero_le_add _ _ (rq_nonneg r) (by decide))

theorem m2_nonneg (r : Nat) : (0 : Q') ≤ m2 r := by
  exact Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ (rq_nonneg r) (by decide))
    (Q'.zero_le_add _ _ (rq_nonneg r) (by decide))

theorem positiveAnchor_nonneg (r : Nat) : (0 : Q') ≤ positiveAnchor r :=
  Q'.mul_nonneg _ _ (a0_nonneg r) (m0_nonneg r)

private def coeffMassL : RingNormaliser.PolyExpr :=
  let z := RingNormaliser.PolyExpr.var 0
  let A0 := .mul (.mul (.const 4) (.add z (.const 1))) (.add z (.const 3))
  let M0 := .mul (.mul (.const 4) (.add z (.const 2))) (.add z (.const 2))
  .mul (.const 3) (.mul A0 M0)

private def coeffMassR : RingNormaliser.PolyExpr :=
  let z := RingNormaliser.PolyExpr.var 0
  let A0 := .mul (.mul (.const 4) (.add z (.const 1))) (.add z (.const 3))
  let A1 := .mul (.mul (.const 2) (.add z (.const 2))) (.add z (.const 3))
  let A2 := .mul (.mul (.const 2) (.add z (.const 1))) (.add z (.const 4))
  let M1 := .mul (.mul (.const 4) (.add z (.const 2))) (.add z (.const 3))
  let M2 := .mul (.add z (.const 3)) (.add z (.const 3))
  let adverse : RingNormaliser.PolyExpr :=
    .add (.add (.add (.mul A0 M1) (.mul A0 M2)) (.mul A1 M2)) (.mul A2 M2)
  let reserve : RingNormaliser.PolyExpr :=
    .mul (.mul (.mul (.const 4) z) (.add z (.const 3)))
      (.add (.add (.mul (.mul (.const 6) z) z) (.mul (.const 21) z))
        (.const 17))
  .add adverse reserve

private theorem coeffMass_normal : RingNormaliser.normalize coeffMassL =
    RingNormaliser.normalize coeffMassR := by
  decide

/-- Exact coefficient budget:
`3 P_r - N_r = 4r(r+3)(6r²+21r+17) ≥ 0`. -/
theorem adverseCoefficientMass_le (r : Nat) :
    adverseCoefficientMass r ≤ (3 : Q') * positiveAnchor r := by
  let reserve : Q' :=
    (4 : Q') * rq r * (rq r + 3) *
      ((6 : Q') * rq r * rq r + 21 * rq r + 17)
  have heq : (3 : Q') * positiveAnchor r ≈
      adverseCoefficientMass r + reserve := by
    have hn := RingNormaliser.poly_identity_of_normal_eq _ _ coeffMass_normal
      (fun _ => rq r)
    simpa [coeffMassL, coeffMassR, positiveAnchor, adverseCoefficientMass,
      a0, a1, a2, m0, m1, m2, reserve, RingNormaliser.eval] using hn
  have hz : (0 : Q') ≤ rq r := by
    unfold rq
    exact zero_le_ofNat r
  have hreserve : (0 : Q') ≤ reserve := by
    dsimp [reserve]
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (by decide) hz)
        (Q'.zero_le_add _ _ hz (by decide)))
      (Q'.zero_le_add _ _
        (Q'.zero_le_add _ _
          (Q'.mul_nonneg _ _
            (Q'.mul_nonneg _ _ (by decide) hz) hz)
          (Q'.mul_nonneg _ _ (by decide) hz))
        (by decide))
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (adverseCoefficientMass r) reserve hreserve)
    (Q'.le_of_eqv (Q'.eqv_symm heq))

/-- All four adverse chains are paid by the single constant anchor, uniformly
in `r`.  The analytic input is only `3x ≤ 1`; chain monotonicity itself needs
the weaker `2x ≤ 1`. -/
theorem adversePart_le_anchor {x y : Q'} (hx0 : (0 : Q') ≤ x)
    (hy0 : (0 : Q') ≤ y) (hyx : y ≤ x)
    (h2x : (2 : Q') * x ≤ (1 : Q'))
    (h3x : (3 : Q') * x ≤ (1 : Q')) (r : Nat) :
    adversePart x y r ≤ positiveAnchor r := by
  let c0 := a0 r * m1 r
  let c1 := a0 r * m2 r
  let c2 := a1 r * m2 r
  let c3 := a2 r * m2 r
  have hc0 : (0 : Q') ≤ c0 := Q'.mul_nonneg _ _ (a0_nonneg r) (m1_nonneg r)
  have hc1 : (0 : Q') ≤ c1 := Q'.mul_nonneg _ _ (a0_nonneg r) (m2_nonneg r)
  have hc2 : (0 : Q') ≤ c2 := Q'.mul_nonneg _ _ (a1_nonneg r) (m2_nonneg r)
  have hc3 : (0 : Q') ≤ c3 := Q'.mul_nonneg _ _ (a2_nonneg r) (m2_nonneg r)
  have h0 : c0 * homChain x y 1 r ≤ c0 * x :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (homChain_le_x hx0 hy0 hyx h2x (by omega) r) hc0
  have h1 : c1 * homChain x y 1 (2 * r + 1) ≤ c1 * x :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (homChain_le_x hx0 hy0 hyx h2x (by omega) (2 * r + 1)) hc1
  have h2 : c2 * homChain x y (r + 1) (r + 1) ≤ c2 * x :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (homChain_le_x hx0 hy0 hyx h2x (by omega) (r + 1)) hc2
  have h3 : c3 * homChain x y (r + 3) (r - 1) ≤ c3 * x :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (homChain_le_x hx0 hy0 hyx h2x (by omega) (r - 1)) hc3
  have hchains : adversePart x y r ≤ c0 * x + c1 * x + c2 * x + c3 * x := by
    dsimp [adversePart, c0, c1, c2, c3]
    exact add_le_add' (add_le_add' (add_le_add' h0 h1) h2) h3
  have hmass : c0 * x + c1 * x + c2 * x + c3 * x ≈
      adverseCoefficientMass r * x := by
    dsimp [c0, c1, c2, c3, adverseCoefficientMass]
    exact four_mul_sum_eqv _ _ _ _ x
  have hbudget : adverseCoefficientMass r * x ≤
      ((3 : Q') * positiveAnchor r) * x :=
    Q'.mul_le_mul_of_nonneg_right _ _ x (adverseCoefficientMass_le r) hx0
  have hshuffle : ((3 : Q') * positiveAnchor r) * x ≈
      positiveAnchor r * ((3 : Q') * x) :=
    mul_shuffle_eqv 3 (positiveAnchor r) x
  have hcap : positiveAnchor r * ((3 : Q') * x) ≤
      positiveAnchor r * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h3x (positiveAnchor_nonneg r)
  exact Q'.le_trans' _ _ _ hchains
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmass)
      (Q'.le_trans' _ _ _ hbudget
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hshuffle)
          (Q'.le_trans' _ _ _ hcap
            (Q'.le_of_eqv (Q'.mul_one_eqv (positiveAnchor r)))))))

theorem positiveTail_nonneg {x y : Q'} (hx0 : (0 : Q') ≤ x)
    (hy0 : (0 : Q') ≤ y) (r : Nat) :
    (0 : Q') ≤ positiveTail x y r := by
  have h0 := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (a1_nonneg r) (m0_nonneg r))
    (homChain_nonneg hx0 hy0 0 (r + 1))
  have h1 := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (a2_nonneg r) (m0_nonneg r))
    (homChain_nonneg hx0 hy0 0 (r + 3))
  have h2 := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (a2_nonneg r) (m1_nonneg r))
    (homChain_nonneg hx0 hy0 (r + 1) 2)
  have h3 := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (a3_nonneg r) (m0_nonneg r))
    (homChain_nonneg hx0 hy0 0 (2 * r + 3))
  have h4 := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (a3_nonneg r) (m1_nonneg r))
    (homChain_nonneg hx0 hy0 (r + 1) (r + 2))
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.zero_le_add _ _ h0 h1) h2) h3) h4

/-- The reduced divided residual is nonnegative for every offset. -/
theorem reducedPart_nonneg {x y : Q'} (hx0 : (0 : Q') ≤ x)
    (hy0 : (0 : Q') ≤ y) (hyx : y ≤ x)
    (h2x : (2 : Q') * x ≤ (1 : Q'))
    (h3x : (3 : Q') * x ≤ (1 : Q')) (r : Nat) :
    (0 : Q') ≤ reducedPart x y r := by
  exact Q'.zero_le_add _ _
    (Q'.sub_nonneg_of_le
      (adversePart_le_anchor hx0 hy0 hyx h2x h3x r))
    (positiveTail_nonneg hx0 hy0 r)

/-! ## Concrete base-row bridge -/

def lPoly (x : Q') (k : Nat) : Q' :=
  (2 : Q') * (rq k + 1) + (rq k + 2) * qpow x k

private theorem dimQ_eq_rq_add_one (k : Nat) : dimQ k ≈ rq k + 1 := by
  simpa [dimQ, rq] using Q'.ofNat_add_eqv k 1

private theorem dimQ_succ_eq_rq_add_two (k : Nat) : dimQ (k + 1) ≈ rq k + 2 := by
  exact Q'.eqv_trans _ _ _ (dimQ_eq_rq_add_one (k + 1))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ 1 (Q'.ofNat_add_eqv k 1))
      (Q'.add_assoc_eqv (rq k) 1 1))

private theorem qpow_square_iterate (w : Q') (k : Nat) :
    qpow (qpow w 2) k ≈ qpow w (2 * k) :=
  qpow_qpow w 2 k

private theorem window_head_term (w : Q') (k : Nat) :
    coeffW w 0 * coeffW w (k + 1) ≈
      qpow w (c4 k + 3) * ((rq k + 2) * qpow (qpow w 2) k) := by
  rw [coeffW_zero]
  refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv (coeffW w (k + 1))) ?_
  unfold coeffW
  have hdim := dimQ_succ_eq_rq_add_two k
  have hpow0 : qpow w (c4 (k + 1)) ≈
      qpow w (c4 k + 3) * qpow w (2 * k) := by
    rw [show c4 (k + 1) = (c4 k + 3) + 2 * k by
      unfold c4
      simp only [Nat.add_mul, Nat.mul_add]
      omega]
    exact qpow_add w (c4 k + 3) (2 * k)
  have hpow : qpow w (c4 (k + 1)) ≈
      qpow w (c4 k + 3) * qpow (qpow w 2) k :=
    Q'.eqv_trans _ _ _ hpow0
      (Q'.mul_eqv_congr_left (qpow w (c4 k + 3)) _ _
        (Q'.eqv_symm (qpow_square_iterate w k)))
  refine Q'.eqv_trans _ _ _ (mul_eqv_congr' hdim hpow) ?_
  exact Q'.eqv_trans _ _ _
    (coeff_factor_pos (rq k + 2) (qpow w (c4 k + 3))
      (qpow (qpow w 2) k))
    (Q'.eqv_refl _)

private theorem window_boundary_term (w : Q') (k : Nat) :
    coeffW w 1 * coeffW w k ≈
      qpow w (c4 k + 3) * ((2 : Q') * (rq k + 1)) := by
  unfold coeffW
  refine Q'.eqv_trans _ _ _
    (FusionResidualBound.mul_four_regroup (dimQ 1) (qpow w (c4 1))
      (dimQ k) (qpow w (c4 k))) ?_
  have hcoeff : dimQ 1 * dimQ k ≈ (2 : Q') * (rq k + 1) :=
    mul_eqv_congr' (by decide : dimQ 1 ≈ (2 : Q'))
      (dimQ_eq_rq_add_one k)
  have hpow : qpow w (c4 1) * qpow w (c4 k) ≈
      qpow w (c4 k + 3) := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (qpow_add w (c4 1) (c4 k)))
      (by
        rw [show c4 1 + c4 k = c4 k + 3 by unfold c4; omega]
        exact Q'.eqv_refl _)
  refine Q'.eqv_trans _ _ _ (mul_eqv_congr' hcoeff hpow) ?_
  exact Q'.mul_comm_eqv _ _

/-- The range-two window is a common monomial times a two-term polynomial in
`x=w²`, uniformly in its offset. -/
theorem modeWindow_one_formula (w : Q') (k : Nat) :
    modeWindow w 1 k ≈ qpow w (c4 k + 3) * lPoly (qpow w 2) k := by
  unfold modeWindow acN
  simp only [fsum_succ, fsum_zero, Nat.sub_zero]
  rw [show 1 + k = k + 1 by omega, show k + 1 - 1 = k by omega]
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (window_boundary_term w k)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq (Q'.zero_add' (coeffW w 0 * coeffW w (k + 1))))
        (window_head_term w k))) ?_
  unfold lPoly
  exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
    (Q'.eqv_symm (Q'.mul_add_eqv (qpow w (c4 k + 3))
      ((2 : Q') * (rq k + 1)) ((rq k + 2) * qpow (qpow w 2) k)))

private theorem rq_shift_add (r n c : Nat) :
    rq (r + n) + Q'.ofNat c ≈ rq r + Q'.ofNat (n + c) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (Q'.ofNat c) (Q'.ofNat_add_eqv r n)) ?_
  exact Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (rq r) (Q'.ofNat n) (Q'.ofNat c))
    (Q'.add_eqv_congr_left (rq r) _ _
      (Q'.eqv_symm (Q'.ofNat_add_eqv n c)))

private def aExpandL : RingNormaliser.PolyExpr :=
  let z := RingNormaliser.PolyExpr.var 0
  let X := RingNormaliser.PolyExpr.var 1
  let Y := RingNormaliser.PolyExpr.var 2
  .mul
    (.add (.mul (.const 2) (.add z (.const 1))) (.mul (.add z (.const 2)) X))
    (.add (.mul (.const 2) (.add z (.const 3))) (.mul (.add z (.const 4)) Y))

private def aExpandR : RingNormaliser.PolyExpr :=
  let z := RingNormaliser.PolyExpr.var 0
  let X := RingNormaliser.PolyExpr.var 1
  let Y := RingNormaliser.PolyExpr.var 2
  .add (.add (.add
    (.mul (.mul (.const 4) (.add z (.const 1))) (.add z (.const 3)))
    (.mul (.mul (.mul (.const 2) (.add z (.const 2))) (.add z (.const 3))) X))
    (.mul (.mul (.mul (.const 2) (.add z (.const 1))) (.add z (.const 4))) Y))
    (.mul (.mul (.add z (.const 2)) (.add z (.const 4))) (.mul X Y))

private theorem aExpand_normal : RingNormaliser.normalize aExpandL =
    RingNormaliser.normalize aExpandR := by
  decide

private def mExpandL : RingNormaliser.PolyExpr :=
  let z := RingNormaliser.PolyExpr.var 0
  let X := RingNormaliser.PolyExpr.var 1
  .mul
    (.add (.mul (.const 2) (.add z (.const 2))) (.mul (.add z (.const 3)) X))
    (.add (.mul (.const 2) (.add z (.const 2))) (.mul (.add z (.const 3)) X))

private def mExpandR : RingNormaliser.PolyExpr :=
  let z := RingNormaliser.PolyExpr.var 0
  let X := RingNormaliser.PolyExpr.var 1
  .add (.add
    (.mul (.mul (.const 4) (.add z (.const 2))) (.add z (.const 2)))
    (.mul (.mul (.mul (.const 4) (.add z (.const 2))) (.add z (.const 3))) X))
    (.mul (.mul (.add z (.const 3)) (.add z (.const 3))) (.mul X X))

private theorem mExpand_normal : RingNormaliser.normalize mExpandL =
    RingNormaliser.normalize mExpandR := by
  decide

theorem lPoly_offset_product (x : Q') (r : Nat) :
    lPoly x r * lPoly x (r + 2) ≈ aPoly x r := by
  let X := qpow x r
  let Y := qpow x (r + 2)
  have hL2 : lPoly x (r + 2) ≈
      (2 : Q') * (rq r + 3) + (rq r + 4) * Y := by
    unfold lPoly
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left 2 _ _
        (by simpa only using rq_shift_add r 2 1))
      (Q'.mul_eqv_congr_right _ _ Y
        (by simpa only using rq_shift_add r 2 2))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (lPoly x r) _ _ hL2) ?_
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _ aExpand_normal
    (fun i => match i with | 0 => rq r | 1 => X | _ => Y)
  have hexpand :
      lPoly x r * ((2 : Q') * (rq r + 3) + (rq r + 4) * Y) ≈
        a0 r + a1 r * X + a2 r * Y + a3 r * (X * Y) := by
    simpa [aExpandL, aExpandR, lPoly, a0, a1, a2, a3,
      RingNormaliser.eval, X, Y] using hn
  refine Q'.eqv_trans _ _ _ hexpand ?_
  unfold aPoly
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_left (a3 r) _ _
      (Q'.eqv_symm (by
        simpa only [show r + (r + 2) = 2 * r + 2 by omega] using
          qpow_add x r (r + 2))))

theorem lPoly_mid_square (x : Q') (r : Nat) :
    lPoly x (r + 1) * lPoly x (r + 1) ≈ mPoly x r := by
  let X := qpow x (r + 1)
  have hL1 : lPoly x (r + 1) ≈
      (2 : Q') * (rq r + 2) + (rq r + 3) * X := by
    unfold lPoly
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left 2 _ _
        (by simpa only using rq_shift_add r 1 1))
      (Q'.mul_eqv_congr_right _ _ X
        (by simpa only using rq_shift_add r 1 2))
  refine Q'.eqv_trans _ _ _ (mul_eqv_congr' hL1 hL1) ?_
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _ mExpand_normal
    (fun i => if i = 0 then rq r else X)
  have hexpand :
      ((2 : Q') * (rq r + 2) + (rq r + 3) * X) *
        ((2 : Q') * (rq r + 2) + (rq r + 3) * X) ≈
      m0 r + m1 r * X + m2 r * (X * X) := by
    simpa [mExpandL, mExpandR, m0, m1, m2, RingNormaliser.eval, X] using hn
  refine Q'.eqv_trans _ _ _ hexpand ?_
  unfold mPoly
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_left (m2 r) _ _
      (Q'.eqv_symm (by
        simpa only [show (r + 1) + (r + 1) = 2 * r + 2 by omega] using
          qpow_add x (r + 1) (r + 1))))

def commonExp (r : Nat) : Nat := 2 * c4 (r + 1) + 6

theorem offsetA_one_formula (w : Q') (r : Nat) :
    offsetA w 1 r ≈
      (qpow w (commonExp r) * qpow w 2) * aPoly (qpow w 2) r := by
  unfold offsetA
  refine Q'.eqv_trans _ _ _
    (mul_eqv_congr' (modeWindow_one_formula w r)
      (modeWindow_one_formula w (r + 2))) ?_
  refine Q'.eqv_trans _ _ _
    (FusionResidualBound.mul_four_regroup
      (qpow w (c4 r + 3)) (lPoly (qpow w 2) r)
      (qpow w (c4 (r + 2) + 3)) (lPoly (qpow w 2) (r + 2))) ?_
  have hp : qpow w (c4 r + 3) * qpow w (c4 (r + 2) + 3) ≈
      qpow w (commonExp r) * qpow w 2 := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (qpow_add w (c4 r + 3) (c4 (r + 2) + 3))) ?_
    rw [show (c4 r + 3) + (c4 (r + 2) + 3) = commonExp r + 2 by
      unfold commonExp
      have hc := MeanExpConvexProgress.casimir_secondDiff_eq_two r
      omega]
    exact qpow_add w (commonExp r) 2
  exact mul_eqv_congr' hp (lPoly_offset_product (qpow w 2) r)

theorem offsetM_one_formula (w : Q') (r : Nat) :
    offsetM w 1 r ≈ qpow w (commonExp r) * mPoly (qpow w 2) r := by
  unfold offsetM
  refine Q'.eqv_trans _ _ _
    (mul_eqv_congr' (modeWindow_one_formula w (r + 1))
      (modeWindow_one_formula w (r + 1))) ?_
  refine Q'.eqv_trans _ _ _
    (FusionResidualBound.mul_four_regroup
      (qpow w (c4 (r + 1) + 3)) (lPoly (qpow w 2) (r + 1))
      (qpow w (c4 (r + 1) + 3)) (lPoly (qpow w 2) (r + 1))) ?_
  have hp : qpow w (c4 (r + 1) + 3) * qpow w (c4 (r + 1) + 3) ≈
      qpow w (commonExp r) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (qpow_add w (c4 (r + 1) + 3) (c4 (r + 1) + 3))) ?_
    rw [show (c4 (r + 1) + 3) + (c4 (r + 1) + 3) = commonExp r by
      unfold commonExp; omega]
    exact Q'.eqv_refl _
  exact mul_eqv_congr' hp (lPoly_mid_square (qpow w 2) r)

private def detCommonL : RingNormaliser.PolyExpr :=
  let W := RingNormaliser.PolyExpr.var 0
  let H := RingNormaliser.PolyExpr.var 1
  let x := RingNormaliser.PolyExpr.var 2
  let y := RingNormaliser.PolyExpr.var 3
  let Ax := RingNormaliser.PolyExpr.var 4
  let Ay := RingNormaliser.PolyExpr.var 5
  let Mx := RingNormaliser.PolyExpr.var 6
  let My := RingNormaliser.PolyExpr.var 7
  .add (.mul (.mul (.mul W x) Ax) (.mul H My))
    (.neg (.mul (.mul W Mx) (.mul (.mul H y) Ay)))

private def detCommonR : RingNormaliser.PolyExpr :=
  let W := RingNormaliser.PolyExpr.var 0
  let H := RingNormaliser.PolyExpr.var 1
  let x := RingNormaliser.PolyExpr.var 2
  let y := RingNormaliser.PolyExpr.var 3
  let Ax := RingNormaliser.PolyExpr.var 4
  let Ay := RingNormaliser.PolyExpr.var 5
  let Mx := RingNormaliser.PolyExpr.var 6
  let My := RingNormaliser.PolyExpr.var 7
  .mul (.mul W H)
    (.add (.mul (.mul x Ax) My) (.neg (.mul (.mul y Mx) Ay)))

private theorem detCommon_normal : RingNormaliser.normalize detCommonL =
    RingNormaliser.normalize detCommonR := by
  decide

private theorem det_common (W H x y Ax Ay Mx My : Q') :
    (((W*x)*Ax)*(H*My)) + -((W*Mx)*((H*y)*Ay)) ≈
      (W*H) * (x*Ax*My + -(y*Mx*Ay)) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _ detCommon_normal
    (fun i => match i with
      | 0 => W | 1 => H | 2 => x | 3 => y | 4 => Ax | 5 => Ay | 6 => Mx | _ => My)
  simpa [detCommonL, detCommonR, RingNormaliser.eval] using hn

theorem offsetDelta_one_formula (w h : Q') (r : Nat) :
    offsetDelta w h 1 r ≈
      (qpow w (commonExp r) * qpow h (commonExp r)) *
        (qpow w 2 * aPoly (qpow w 2) r * mPoly (qpow h 2) r +
          -(qpow h 2 * mPoly (qpow w 2) r * aPoly (qpow h 2) r)) := by
  unfold offsetDelta determinant
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (mul_eqv_congr' (offsetA_one_formula w r) (offsetM_one_formula h r))
      (Q'.neg_eqv_congr _ _
        (mul_eqv_congr' (offsetM_one_formula w r) (offsetA_one_formula h r)))) ?_
  exact det_common (qpow w (commonExp r)) (qpow h (commonExp r))
    (qpow w 2) (qpow h 2) (aPoly (qpow w 2) r) (aPoly (qpow h 2) r)
    (mPoly (qpow w 2) r) (mPoly (qpow h 2) r)

private theorem dimQ_shift (r n : Nat) :
    dimQ (r + n) ≈ rq r + Q'.ofNat (n + 1) := by
  exact Q'.eqv_trans _ _ _ (dimQ_eq_rq_add_one (r + n))
    (by simpa only using rq_shift_add r n 1)

private theorem offsetA_zero_shape (w : Q') (r : Nat) :
    offsetA w 0 (r + 1) ≈
      (qpow w (commonExp r) * qpow (qpow w 2) (2 * r + 3)) * a3 r := by
  refine Q'.eqv_trans _ _ _ (offsetA_zero_monomial w (r + 1)) ?_
  have hc : dimQ (r + 1) * dimQ (r + 1 + 2) ≈ a3 r := by
    unfold a3
    exact mul_eqv_congr'
      (by simpa only using dimQ_shift r 1)
      (by simpa only [show r + 1 + 2 = r + 3 by omega] using dimQ_shift r 3)
  have hp : qpow w (c4 (r + 1) + c4 (r + 1 + 2)) ≈
      qpow w (commonExp r) * qpow (qpow w 2) (2 * r + 3) := by
    rw [show c4 (r + 1) + c4 (r + 1 + 2) =
        commonExp r + 2 * (2 * r + 3) by
      unfold commonExp c4
      simp only [Nat.add_mul, Nat.mul_add]
      omega]
    exact Q'.eqv_trans _ _ _ (qpow_add w (commonExp r) (2 * (2 * r + 3)))
      (Q'.mul_eqv_congr_left (qpow w (commonExp r)) _ _
        (Q'.eqv_symm (qpow_square_iterate w (2 * r + 3))))
  exact Q'.eqv_trans _ _ _ (mul_eqv_congr' hc hp) (Q'.mul_comm_eqv _ _)

private theorem offsetM_zero_shape (w : Q') (r : Nat) :
    offsetM w 0 (r + 1) ≈
      (qpow w (commonExp r) * qpow (qpow w 2) (2 * r + 2)) * m2 r := by
  refine Q'.eqv_trans _ _ _ (offsetM_zero_monomial w (r + 1)) ?_
  have hc : dimQ (r + 1 + 1) * dimQ (r + 1 + 1) ≈ m2 r := by
    unfold m2
    exact mul_eqv_congr'
      (by simpa only [show r + 1 + 1 = r + 2 by omega] using dimQ_shift r 2)
      (by simpa only [show r + 1 + 1 = r + 2 by omega] using dimQ_shift r 2)
  have hp : qpow w (2 * c4 (r + 1 + 1)) ≈
      qpow w (commonExp r) * qpow (qpow w 2) (2 * r + 2) := by
    rw [show 2 * c4 (r + 1 + 1) = commonExp r + 2 * (2 * r + 2) by
      unfold commonExp c4
      simp only [Nat.add_mul, Nat.mul_add]
      omega]
    exact Q'.eqv_trans _ _ _ (qpow_add w (commonExp r) (2 * (2 * r + 2)))
      (Q'.mul_eqv_congr_left (qpow w (commonExp r)) _ _
        (Q'.eqv_symm (qpow_square_iterate w (2 * r + 2))))
  exact Q'.eqv_trans _ _ _ (mul_eqv_congr' hc hp) (Q'.mul_comm_eqv _ _)

private def terminalDetL : RingNormaliser.PolyExpr :=
  let a := RingNormaliser.PolyExpr.var 0
  let m := RingNormaliser.PolyExpr.var 1
  let X1 := RingNormaliser.PolyExpr.var 2
  let X0 := RingNormaliser.PolyExpr.var 3
  let Y1 := RingNormaliser.PolyExpr.var 4
  let Y0 := RingNormaliser.PolyExpr.var 5
  .add (.mul (.mul X1 a) (.mul Y0 m))
    (.neg (.mul (.mul X0 m) (.mul Y1 a)))

private def terminalDetR : RingNormaliser.PolyExpr :=
  let a := RingNormaliser.PolyExpr.var 0
  let m := RingNormaliser.PolyExpr.var 1
  let X1 := RingNormaliser.PolyExpr.var 2
  let X0 := RingNormaliser.PolyExpr.var 3
  let Y1 := RingNormaliser.PolyExpr.var 4
  let Y0 := RingNormaliser.PolyExpr.var 5
  .mul (.mul a m) (.add (.mul X1 Y0) (.neg (.mul X0 Y1)))

private theorem terminalDet_normal : RingNormaliser.normalize terminalDetL =
    RingNormaliser.normalize terminalDetR := by
  decide

private theorem terminal_det (a m X1 X0 Y1 Y0 : Q') :
    (X1*a)*(Y0*m) + -((X0*m)*(Y1*a)) ≈
      (a*m)*(X1*Y0 + -(X0*Y1)) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _ terminalDet_normal
    (fun i => match i with
      | 0 => a | 1 => m | 2 => X1 | 3 => X0 | 4 => Y1 | _ => Y0)
  simpa [terminalDetL, terminalDetR, RingNormaliser.eval] using hn

private theorem terminal_inner_factor (x y : Q') (r : Nat) :
    (qpow x (2 * r + 3) * a3 r) * (qpow y (2 * r + 2) * m2 r) +
      -((qpow x (2 * r + 2) * m2 r) * (qpow y (2 * r + 3) * a3 r)) ≈
      (x + -y) * terminalPart x y r := by
  refine Q'.eqv_trans _ _ _
    (terminal_det (a3 r) (m2 r) (qpow x (2 * r + 3))
      (qpow x (2 * r + 2)) (qpow y (2 * r + 3)) (qpow y (2 * r + 2))) ?_
  have hcross : qpow x (2 * r + 3) * qpow y (2 * r + 2) +
      -(qpow x (2 * r + 2) * qpow y (2 * r + 3)) ≈
      (x + -y) * homChain x y (2 * r + 2) 1 := by
    simpa only [show 2 * r + 2 + 1 = 2 * r + 3 by omega] using
      crossPair_factor x y (2 * r + 2) 1
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (a3 r * m2 r) _ _ hcross) ?_
  unfold terminalPart
  exact coeff_factor_pos (a3 r * m2 r) (x + -y)
    (homChain x y (2 * r + 2) 1)

private def terminalCommonL : RingNormaliser.PolyExpr :=
  let W := RingNormaliser.PolyExpr.var 0
  let H := RingNormaliser.PolyExpr.var 1
  let a := RingNormaliser.PolyExpr.var 2
  let m := RingNormaliser.PolyExpr.var 3
  let X1 := RingNormaliser.PolyExpr.var 4
  let X0 := RingNormaliser.PolyExpr.var 5
  let Y1 := RingNormaliser.PolyExpr.var 6
  let Y0 := RingNormaliser.PolyExpr.var 7
  .add (.mul (.mul (.mul W X1) a) (.mul (.mul H Y0) m))
    (.neg (.mul (.mul (.mul W X0) m) (.mul (.mul H Y1) a)))

private def terminalCommonR : RingNormaliser.PolyExpr :=
  let W := RingNormaliser.PolyExpr.var 0
  let H := RingNormaliser.PolyExpr.var 1
  let a := RingNormaliser.PolyExpr.var 2
  let m := RingNormaliser.PolyExpr.var 3
  let X1 := RingNormaliser.PolyExpr.var 4
  let X0 := RingNormaliser.PolyExpr.var 5
  let Y1 := RingNormaliser.PolyExpr.var 6
  let Y0 := RingNormaliser.PolyExpr.var 7
  .mul (.mul W H)
    (.add (.mul (.mul X1 a) (.mul Y0 m))
      (.neg (.mul (.mul X0 m) (.mul Y1 a))))

private theorem terminalCommon_normal : RingNormaliser.normalize terminalCommonL =
    RingNormaliser.normalize terminalCommonR := by
  decide

private theorem terminal_common (W H a m X1 X0 Y1 Y0 : Q') :
    (((W*X1)*a)*((H*Y0)*m)) + -(((W*X0)*m)*((H*Y1)*a)) ≈
      (W*H) * ((X1*a)*(Y0*m) + -((X0*m)*(Y1*a))) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _ terminalCommon_normal
    (fun i => match i with
      | 0 => W | 1 => H | 2 => a | 3 => m | 4 => X1 | 5 => X0 | 6 => Y1 | _ => Y0)
  simpa [terminalCommonL, terminalCommonR, RingNormaliser.eval] using hn

theorem offsetDelta_zero_terminal_formula (w h : Q') (r : Nat) :
    offsetDelta w h 0 (r + 1) ≈
      (qpow w (commonExp r) * qpow h (commonExp r)) *
        ((qpow w 2 + -(qpow h 2)) * terminalPart (qpow w 2) (qpow h 2) r) := by
  unfold offsetDelta determinant
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (mul_eqv_congr' (offsetA_zero_shape w r) (offsetM_zero_shape h r))
      (Q'.neg_eqv_congr _ _
        (mul_eqv_congr' (offsetM_zero_shape w r) (offsetA_zero_shape h r)))) ?_
  let W := qpow w (commonExp r)
  let H := qpow h (commonExp r)
  let x := qpow w 2
  let y := qpow h 2
  refine Q'.eqv_trans _ _ _
    (terminal_common W H (a3 r) (m2 r)
      (qpow x (2 * r + 3)) (qpow x (2 * r + 2))
      (qpow y (2 * r + 3)) (qpow y (2 * r + 2))) ?_
  exact Q'.mul_eqv_congr_left (W * H) _ _ (terminal_inner_factor x y r)

private def cancelTerminalL : RingNormaliser.PolyExpr :=
  let C := RingNormaliser.PolyExpr.var 0
  let d := RingNormaliser.PolyExpr.var 1
  let R := RingNormaliser.PolyExpr.var 2
  let T := RingNormaliser.PolyExpr.var 3
  .add (.mul C (.mul d (.add R T))) (.neg (.mul C (.mul d T)))

private def cancelTerminalR : RingNormaliser.PolyExpr :=
  let C := RingNormaliser.PolyExpr.var 0
  let d := RingNormaliser.PolyExpr.var 1
  let R := RingNormaliser.PolyExpr.var 2
  .mul C (.mul d R)

private theorem cancelTerminal_normal : RingNormaliser.normalize cancelTerminalL =
    RingNormaliser.normalize cancelTerminalR := by
  decide

private theorem cancel_terminal (C d R T : Q') :
    C * (d * (R + T)) + -(C * (d * T)) ≈ C * (d * R) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _ cancelTerminal_normal
    (fun i => match i with | 0 => C | 1 => d | 2 => R | _ => T)
  simpa [cancelTerminalL, cancelTerminalR, RingNormaliser.eval] using hn

/-- Exact concrete factorization of every positive-offset base-row residual. -/
theorem boundaryResidualAt_zero_factor {w h : Q'} {r : Nat} (hr : 1 ≤ r) :
    boundaryResidualAt w h 0 r ≈
      (qpow w (commonExp r) * qpow h (commonExp r)) *
        ((qpow w 2 + -(qpow h 2)) * reducedPart (qpow w 2) (qpow h 2) r) := by
  refine Q'.eqv_trans _ _ _
    (boundaryResidualAt_eq_potential_difference w h 0 r) ?_
  simp only [Nat.zero_add]
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (offsetDelta_one_formula w h r)
      (Q'.neg_eqv_congr _ _ (offsetDelta_zero_terminal_formula w h r))) ?_
  let C := qpow w (commonExp r) * qpow h (commonExp r)
  let x := qpow w 2
  let y := qpow h 2
  have hpoly := polyResidual_factor (x := x) (y := y) hr
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left C _ _ hpoly)) ?_
  exact cancel_terminal C (x + -y) (reducedPart x y r) (terminalPart x y r)

private theorem square_cap_data {w h : Q'} (hh0 : (0 : Q') ≤ h)
    (hhw : h ≤ w) (hwcap : (4 : Q') * w ≤ (1 : Q')) :
    let x := qpow w 2
    let y := qpow h 2
    (0 : Q') ≤ x ∧ (0 : Q') ≤ y ∧ y ≤ x ∧
      (2 : Q') * x ≤ (1 : Q') ∧ (3 : Q') * x ≤ (1 : Q') := by
  let x := qpow w 2
  let y := qpow h 2
  have hw0 : (0 : Q') ≤ w := Q'.le_trans' _ _ _ hh0 hhw
  have hx0 : (0 : Q') ≤ x := qpow_nonneg w hw0 2
  have hy0 : (0 : Q') ≤ y := qpow_nonneg h hh0 2
  have hyx : y ≤ x := qpow_mono hh0 hhw 2
  have hw4 : w ≤ (4 : Q') * w :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv w)))
      (Q'.mul_le_mul_of_nonneg_right 1 4 w (by decide) hw0)
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hw4 hwcap
  have hxw : x ≤ w := by
    simpa only [show 1 + 1 = 2 by omega] using qpow_succ_le_self hw0 hw1 1
  have h3x3w : (3 : Q') * x ≤ (3 : Q') * w :=
    Q'.mul_le_mul_of_nonneg_left _ _ 3 hxw (by decide)
  have h3w4w : (3 : Q') * w ≤ (4 : Q') * w :=
    Q'.mul_le_mul_of_nonneg_right 3 4 w (by decide) hw0
  have h3x : (3 : Q') * x ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ h3x3w (Q'.le_trans' _ _ _ h3w4w hwcap)
  have h2x3x : (2 : Q') * x ≤ (3 : Q') * x :=
    Q'.mul_le_mul_of_nonneg_right 2 3 x (by decide) hx0
  exact ⟨hx0, hy0, hyx, Q'.le_trans' _ _ _ h2x3x h3x, h3x⟩

/-- **Uniform base-row theorem.** Every offset residual at `s=0` is
nonnegative on the physical simplex, with no finite offset enumeration. -/
theorem boundaryResidualAt_zero_nonneg {w h : Q'} (hh0 : (0 : Q') ≤ h)
    (hhw : h ≤ w) (hwcap : (4 : Q') * w ≤ (1 : Q')) (r : Nat) :
    (0 : Q') ≤ boundaryResidualAt w h 0 r := by
  cases r with
  | zero => exact CoreBResidualAbel.boundaryResidualAt_zero_zero_nonneg hh0 hhw
  | succ r =>
      let x := qpow w 2
      let y := qpow h 2
      obtain ⟨hx0, hy0, hyx, h2x, h3x⟩ := square_cap_data hh0 hhw hwcap
      have hred : (0 : Q') ≤ reducedPart x y (r + 1) :=
        reducedPart_nonneg hx0 hy0 hyx h2x h3x (r + 1)
      have hdiff : (0 : Q') ≤ x + -y := Q'.sub_nonneg_of_le hyx
      have hcommon : (0 : Q') ≤
          qpow w (commonExp (r + 1)) * qpow h (commonExp (r + 1)) :=
        Q'.mul_nonneg _ _
          (qpow_nonneg w (Q'.le_trans' _ _ _ hh0 hhw) _)
          (qpow_nonneg h hh0 _)
      have hfact := boundaryResidualAt_zero_factor (w := w) (h := h)
        (r := r + 1) (by omega)
      exact Q'.le_trans' _ _ _
        (Q'.mul_nonneg _ _ hcommon (Q'.mul_nonneg _ _ hdiff hred))
        (Q'.ge_of_eqv hfact)

/-! ## All-`s` propagation audit -/

/-- Exact physical scout used to test shifted residual propagation. -/
def hEighth : Q' := Q'.mkPos 1 8 (by decide)

theorem hEighth_physical :
    (0 : Q') ≤ hEighth ∧ hEighth ≤ wQuarter ∧
      (4 : Q') * wQuarter ≤ (1 : Q') := by
  decide

/-- The tempting diagonal monotonicity
`R_(s+1,r) ≥ R_(s,r+1)` does not propagate the base row: it already fails at
`(s,r)=(1,0)` inside the physical simplex. -/
theorem shifted_residual_monotonicity_counterexample :
    ¬ (boundaryResidualAt wQuarter hEighth 1 1 ≤
      boundaryResidualAt wQuarter hEighth 2 0) := by
  set_option maxRecDepth 100000 in
    decide

/-! ## Exact diagonal-cumulative audit -/

/-- The diagonal cumulative is exactly the endpoint potential gain.  This is
the subtraction form of `offsetDelta_diagonal_telescope`; it makes explicit
that a cumulative sign is an all-range determinant comparison, not a
consequence of the base row alone. -/
theorem cumulativeResidual_eq_potential_gain (w h : Q') (s r n : Nat) :
    cumulativeResidual w h s r n ≈
      offsetDelta w h (s + n) r + -(offsetDelta w h s (r + n)) := by
  let D := offsetDelta w h (s + n) r
  let P := offsetDelta w h s (r + n)
  let C := cumulativeResidual w h s r n
  have htel : D ≈ P + C := offsetDelta_diagonal_telescope w h s r n
  have hsub : D + -P ≈ (P + C) + -P :=
    Q'.add_eqv_congr_right _ _ (-P) htel
  have hcancel : (P + C) + -P ≈ C := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv P C (-P)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left P _ _ (Q'.add_comm_eqv C (-P))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv P (-P) C)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ C (Q'.add_neg_self_eqv P)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' C)
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hsub hcancel)

/-- The first genuinely shifted cumulative already contains a row-one term:
`C_(0,r,2) = R_(0,r+1) + R_(1,r)`.  Hence uniform control of every
`R_(0,*)` pays only one of its two summands. -/
theorem cumulativeResidual_zero_two (w h : Q') (r : Nat) :
    cumulativeResidual w h 0 r 2 ≈
      boundaryResidualAt w h 0 (r + 1) +
        boundaryResidualAt w h 1 r := by
  simp only [cumulativeResidual, Nat.zero_add, Nat.add_zero]
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.eqv_of_eq (Q'.zero_add' (boundaryResidualAt w h 0 (r + 1))))

#print axioms homChain_nonneg
#print axioms homChain_le_x
#print axioms adverseCoefficientMass_le
#print axioms adversePart_le_anchor
#print axioms reducedPart_nonneg
#print axioms polyResidual_factor
#print axioms boundaryResidualAt_zero_factor
#print axioms boundaryResidualAt_zero_nonneg
#print axioms shifted_residual_monotonicity_counterexample
#print axioms cumulativeResidual_eq_potential_gain
#print axioms cumulativeResidual_zero_two

end YMGap.Continuum.CoreBResidualBaseUniform
