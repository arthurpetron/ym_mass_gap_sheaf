/-
# The exact divided-difference (secant) identity `ddId` for the first-kind
# Chebyshev polynomial — closing the DD/Markov side of `CosNodeResidual`

`CosPiEnclosure.ddBound_of_ddId` (and downstream `cosNodeResidual_of_walls`)
reduce the whole quantitative `dd` field of `CosNodeBracket.CosNodeResidual` to
the SINGLE exact divided-difference identity

    ddId :  T_{k+2}(b) − T_{k+2}(a)  ≈  (b − a) · ddSecant k a b,

where `ddSecant k a b = U_{k+1}(b) + Σ_{j=0}^{k} 2·U_j(b)·T_{k+1−j}(a)`
(`CosPiEnclosure.ddSecant`).  This module PROVES that identity, unconditionally
over `Q'`, by the two-step telescoping induction off the first-kind recurrence
`Cheb.T_succ_succ` (`T_{n+2} = 2x·T_{n+1} − T_n`).

## The two recurrences that drive the induction

* **`Drec`** — the divided-difference (D-)recurrence, a PURE ALGEBRA identity
  from `T_succ_succ` on both endpoints:

      D_{n+2}  ≈  2b·D_{n+1} − D_n + (b−a)·(2·T_{n+1}(a)),   D_m := T_m(b) − T_m(a).

  Its all-atom core `Drec_abs` is an abelian-group/ring rearrangement (the sole
  cancellation is the `2b·T_{n+1}(a)` cross-term).

* **`Srec`** — the secant (S-)recurrence for the closed form:

      S_{k+2}  ≈  2b·S_{k+1} − S_k + 2·T_{k+3}(a),   S_m := ddSecant m a b.

  This is the convolution/telescoping reindexing of the closed `ddSecant`; it
  splits into the second-kind three-term recurrence on the leading `U_{m+1}(b)`
  term and the `2b`-reindex of the finite convolution `finSum`.

Matching the two recurrences (same shape, same two base values) closes `ddId`.

## What is PROVED here (axiom-clean)

  * `regroup6` — a reusable 6-atom additive cancellation lemma.
  * `Drec_abs` / `Drec` — the D-recurrence (abstract core + `Cheb.T` instance).
  * `ddId_zero` / `ddId_one` — the two base cases (`k = 0, 1`), direct `eqv`
    polynomial identities.
  * `Prec` / `Srec` — the secant recurrence `SrecP`, PROVED: the `2b`-reindex of
    the finite convolution `finSum` (`Prec`, via `const_mul_finSum` /
    `finSum_peel_left` / `finSum_add` / `htermCore`) plus the second-kind
    three-term recurrence on the leading `U`-term (`Srec_of_Prec`).
  * `ddId` — the divided-difference identity at ALL `k`, UNCONDITIONAL, by the
    two-step induction off `Drec` + `Srec`.
  * `cosNodeResidual_of` / `deMoivreNode_of` — the re-assembly plugging the
    proved `ddId` into `CosPiEnclosure.cosNodeResidual_of_walls`, so the general
    `M` off-diagonal OS2 Gram positivity rests ONLY on the three rational-`π`
    `U`-sign walls (`loSign`/`hiSign`/`tsign`); the DD/Markov side is CLOSED.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no
`sorry`/`sorryAx`, no `native_decide`, no custom axiom.  All identities are
propositional `Q'.eqv` equations (universally quantified equalities, never an
erased `Prop`-∃); the enclosure records remain `Type`-level data.
-/

import YMGap.Continuum.CosPiEnclosure
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.DDIdentity

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum
open YMGap.Continuum.Cheb
open YMGap.Continuum.CosPiEnclosure

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

/-! ## 1. A reusable 6-atom additive cancellation lemma -/

/-- **6-atom additive cancellation**: the sole cancellation `(−N) + N = 0`.
`(P + (−N)) + ((Qs + S) + (N + M)) ≈ (P + Qs) + (M + S)`.  Pure abelian-group
regrouping. -/
theorem regroup6 (P N Qs S M : Q') :
    (P + (-N)) + ((Qs + S) + (N + M)) ≈ (P + Qs) + (M + S) := by
  calc (P + (-N)) + ((Qs + S) + (N + M))
      ≈ (P + (-N)) + ((Qs + N) + (S + M)) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.add_swap_inner Qs S N M)
    _ ≈ ((P + (-N)) + (Qs + N)) + (S + M) :=
        Q'.eqv_symm (Q'.add_assoc_eqv (P + (-N)) (Qs + N) (S + M))
    _ ≈ ((P + Qs) + ((-N) + N)) + (S + M) :=
        Q'.add_eqv_congr_right _ _ _ (Q'.add_swap_inner P (-N) Qs N)
    _ ≈ ((P + Qs) + (0 : Q')) + (S + M) :=
        Q'.add_eqv_congr_right _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv N))
    _ ≈ (P + Qs) + (S + M) := by
        rw [Q'.add_zero']; exact Q'.eqv_refl _
    _ ≈ (P + Qs) + (M + S) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv S M)

/-! ## 2. The D-recurrence: abstract core and the `Cheb.T` instance -/

/-- **All-atom core of the divided-difference recurrence.**  With `p = T_{n+1}(b)`,
`q = T_n(b)`, `r = T_{n+1}(a)`, `s = T_n(a)`:

    (2b·p − q) − (2a·r − s)
      ≈  (2b·(p − r) − (q − s)) + (b − a)·(2·r).

The sole cancellation is the `2b·r` cross-term (via `regroup6`). -/
theorem Drec_abs (a b p q r s : Q') :
    (((2 : Q') * b) * p + (-q)) + (-(((2 : Q') * a) * r + (-s)))
      ≈ (((2 : Q') * b) * (p + (-r)) + (-(q + (-s))))
          + (b + (-a)) * ((2 : Q') * r) := by
  -- common canonical form C = (2b·p + −q) + ((−(2a·r)) + s)
  -- LHS ≈ C
  have hL : (((2 : Q') * b) * p + (-q)) + (-(((2 : Q') * a) * r + (-s)))
      ≈ (((2 : Q') * b) * p + (-q)) + ((-(((2 : Q') * a) * r)) + s) := by
    refine Q'.add_eqv_congr_left _ _ _ ?_
    calc (-(((2 : Q') * a) * r + (-s)))
        ≈ (-(((2 : Q') * a) * r)) + (-(-s)) := Q'.neg_add_eqv _ _
      _ ≈ (-(((2 : Q') * a) * r)) + s :=
          Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv s)
  -- RHS ≈ C
  have hR : (((2 : Q') * b) * (p + (-r)) + (-(q + (-s))))
            + (b + (-a)) * ((2 : Q') * r)
      ≈ (((2 : Q') * b) * p + (-q)) + ((-(((2 : Q') * a) * r)) + s) := by
    -- X1 := 2b·(p−r) ≈ 2b·p + −(2b·r)
    have hX1 : ((2 : Q') * b) * (p + (-r))
        ≈ ((2 : Q') * b) * p + (-(((2 : Q') * b) * r)) := by
      calc ((2 : Q') * b) * (p + (-r))
          ≈ ((2 : Q') * b) * p + ((2 : Q') * b) * (-r) := Q'.mul_add_eqv _ _ _
        _ ≈ ((2 : Q') * b) * p + (-(((2 : Q') * b) * r)) :=
            Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv _ _)
    -- X2 := −(q − s) ≈ −q + s
    have hX2 : (-(q + (-s))) ≈ (-q) + s :=
      Q'.eqv_trans _ _ _ (Q'.neg_add_eqv q (-s))
        (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv s))
    -- X3 := (b−a)·(2r) ≈ 2b·r + −(2a·r)
    have hbr : b * ((2 : Q') * r) ≈ ((2 : Q') * b) * r :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv b 2 r))
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv b 2))
    have har : (-a) * ((2 : Q') * r) ≈ (-(((2 : Q') * a) * r)) := by
      calc (-a) * ((2 : Q') * r)
          ≈ ((-a) * 2) * r := Q'.eqv_symm (Q'.mul_assoc_eqv (-a) 2 r)
        _ ≈ (2 * (-a)) * r := Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv (-a) 2)
        _ ≈ (-(2 * a)) * r := Q'.mul_eqv_congr_right _ _ _ (Q'.mul_neg_eqv 2 a)
        _ ≈ (-(((2 : Q') * a) * r)) := Q'.neg_mul_eqv (2 * a) r
    have hX3 : (b + (-a)) * ((2 : Q') * r)
        ≈ ((2 : Q') * b) * r + (-(((2 : Q') * a) * r)) := by
      calc (b + (-a)) * ((2 : Q') * r)
          ≈ b * ((2 : Q') * r) + (-a) * ((2 : Q') * r) := Q'.add_mul_eqv _ _ _
        _ ≈ ((2 : Q') * b) * r + (-(((2 : Q') * a) * r)) :=
            Cheb.add_eqv_congr _ _ _ _ hbr har
    -- assemble RHS ≈ ((P + −N) + (Qs + S)) + (N + M) ≈ (P + Qs) + (M + S) = C
    have hstep : (((2 : Q') * b) * (p + (-r)) + (-(q + (-s))))
                 + (b + (-a)) * ((2 : Q') * r)
        ≈ ((((2 : Q') * b) * p + (-(((2 : Q') * b) * r))) + ((-q) + s))
            + (((2 : Q') * b) * r + (-(((2 : Q') * a) * r))) :=
      Cheb.add_eqv_congr _ _ _ _ (Cheb.add_eqv_congr _ _ _ _ hX1 hX2) hX3
    refine Q'.eqv_trans _ _ _ hstep ?_
    -- reassociate then apply regroup6
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (((2 : Q') * b) * p + (-(((2 : Q') * b) * r)))
        ((-q) + s) (((2 : Q') * b) * r + (-(((2 : Q') * a) * r)))) ?_
    exact regroup6 (((2 : Q') * b) * p) (((2 : Q') * b) * r) (-q) s
      (-(((2 : Q') * a) * r))
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

/-- **The divided-difference recurrence for `Cheb.T`.**  From `Drec_abs` after
rewriting the two `T_{n+2}` via `T_succ_succ`. -/
theorem Drec (n : Nat) (a b : Q') :
    Cheb.T (n + 2) b + (-(Cheb.T (n + 2) a))
      ≈ ((2 : Q') * b) * (Cheb.T (n + 1) b + (-(Cheb.T (n + 1) a)))
          + (-(Cheb.T n b + (-(Cheb.T n a))))
          + (b + (-a)) * ((2 : Q') * Cheb.T (n + 1) a) := by
  rw [Cheb.T_succ_succ n b, Cheb.T_succ_succ n a]
  exact Drec_abs a b (Cheb.T (n + 1) b) (Cheb.T n b) (Cheb.T (n + 1) a) (Cheb.T n a)

/-! ## 3. The two base cases (`k = 0, 1`) -/

/-- **4-atom additive cancellation** `(A + K) + ((−K) + B) ≈ A + B`. -/
theorem regroup4 (A K B : Q') : (A + K) + ((-K) + B) ≈ A + B := by
  calc (A + K) + ((-K) + B)
      ≈ A + (K + ((-K) + B)) := Q'.add_assoc_eqv A K ((-K) + B)
    _ ≈ A + ((K + (-K)) + B) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv K (-K) B))
    _ ≈ A + ((0 : Q') + B) :=
        Q'.add_eqv_congr_left _ _ _
          (Q'.add_eqv_congr_right _ _ _ (ChebU.add_neg_self_eqv K))
    _ ≈ A + B := by rw [Q'.zero_add']; exact Q'.eqv_refl _

/-- **Quadratic secant expansion** `(x − y)·(2x + 2y) ≈ 2x·x − 2y·y`.  The `2·xy`
cross-terms cancel (via `regroup4`).  This is the `k = 0` closed form. -/
theorem expand2 (x y : Q') :
    (x + (-y)) * (((2 : Q') * x) + ((2 : Q') * y))
      ≈ ((2 : Q') * x) * x + (-(((2 : Q') * y) * y)) := by
  -- normalizations of the four products
  have hA : x * ((2 : Q') * x) ≈ ((2 : Q') * x) * x := Q'.mul_comm_eqv x (2 * x)
  have hK : x * ((2 : Q') * y) ≈ (2 : Q') * (x * y) := by
    calc x * ((2 : Q') * y)
        ≈ ((2 : Q') * y) * x := Q'.mul_comm_eqv x (2 * y)
      _ ≈ (2 : Q') * (y * x) := Q'.mul_assoc_eqv 2 y x
      _ ≈ (2 : Q') * (x * y) := Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv y x)
  have hnK : (-y) * ((2 : Q') * x) ≈ (-((2 : Q') * (x * y))) := by
    calc (-y) * ((2 : Q') * x)
        ≈ (-(y * ((2 : Q') * x))) := Q'.neg_mul_eqv y (2 * x)
      _ ≈ (-(((2 : Q') * x) * y)) :=
          Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv y (2 * x))
      _ ≈ (-((2 : Q') * (x * y))) :=
          Q'.neg_eqv_congr _ _ (Q'.mul_assoc_eqv 2 x y)
  have hB : (-y) * ((2 : Q') * y) ≈ (-(((2 : Q') * y) * y)) :=
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv y (2 * y))
      (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv y (2 * y)))
  calc (x + (-y)) * (((2 : Q') * x) + ((2 : Q') * y))
      ≈ x * (((2 : Q') * x) + ((2 : Q') * y))
          + (-y) * (((2 : Q') * x) + ((2 : Q') * y)) := Q'.add_mul_eqv _ _ _
    _ ≈ (x * ((2 : Q') * x) + x * ((2 : Q') * y))
          + ((-y) * ((2 : Q') * x) + (-y) * ((2 : Q') * y)) :=
        Cheb.add_eqv_congr _ _ _ _ (Q'.mul_add_eqv _ _ _) (Q'.mul_add_eqv _ _ _)
    _ ≈ (((2 : Q') * x) * x + (2 : Q') * (x * y))
          + ((-((2 : Q') * (x * y))) + (-(((2 : Q') * y) * y))) :=
        Cheb.add_eqv_congr _ _ _ _
          (Cheb.add_eqv_congr _ _ _ _ hA hK) (Cheb.add_eqv_congr _ _ _ _ hnK hB)
    _ ≈ ((2 : Q') * x) * x + (-(((2 : Q') * y) * y)) :=
        regroup4 (((2 : Q') * x) * x) ((2 : Q') * (x * y)) (-(((2 : Q') * y) * y))

/-- **Base case `k = 0`**: `T_2(b) − T_2(a) ≈ (b − a)·ddSecant 0 a b`. -/
theorem ddId_zero (a b : Q') :
    Cheb.T (0 + 2) b + (-(Cheb.T (0 + 2) a))
      ≈ (b + (-a)) * ddSecant 0 a b := by
  -- ddSecant 0 a b ≈ 2b + 2a
  have hdd : ddSecant 0 a b ≈ (2 : Q') * b + (2 : Q') * a := by
    show ((2 : Q') * b) + ((0 : Q') + (2 : Q') * ((1 : Q') * a))
        ≈ (2 : Q') * b + (2 : Q') * a
    rw [Q'.zero_add']
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv a))
  -- both sides ≈ Cval = (2b)b − (2a)a
  -- LHS ≈ Cval
  have hL : Cheb.T (0 + 2) b + (-(Cheb.T (0 + 2) a))
      ≈ ((2 : Q') * b) * b + (-(((2 : Q') * a) * a)) := by
    show (((2 : Q') * b) * b + (-(1 : Q'))) + (-((((2 : Q') * a) * a) + (-(1 : Q'))))
        ≈ ((2 : Q') * b) * b + (-(((2 : Q') * a) * a))
    calc (((2 : Q') * b) * b + (-(1 : Q'))) + (-((((2 : Q') * a) * a) + (-(1 : Q'))))
        ≈ (((2 : Q') * b) * b + (-(1 : Q')))
            + ((-(((2 : Q') * a) * a)) + (1 : Q')) :=
          Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_trans _ _ _ (Q'.neg_add_eqv _ _)
              (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv (1 : Q'))))
      _ ≈ (((2 : Q') * b) * b + (-(((2 : Q') * a) * a)))
            + ((-(1 : Q')) + (1 : Q')) :=
          Q'.add_swap_inner _ _ _ _
      _ ≈ (((2 : Q') * b) * b + (-(((2 : Q') * a) * a))) + (0 : Q') :=
          Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv (1 : Q'))
      _ ≈ ((2 : Q') * b) * b + (-(((2 : Q') * a) * a)) := by
          rw [Q'.add_zero']; exact Q'.eqv_refl _
  -- RHS ≈ Cval
  have hR : (b + (-a)) * ddSecant 0 a b
      ≈ ((2 : Q') * b) * b + (-(((2 : Q') * a) * a)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hdd) (expand2 b a)
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

/-! ## 4. The shifted secant `Sm` and its three-term recurrence -/

/-- `x·0 ≈ 0` over `Q'` (local; mirrors `CRealLog.mul_zero_eqv`). -/
theorem mulZero (x : Q') : x * (0 : Q') ≈ (0 : Q') := by
  show (x * (0 : Q')).num * ((0 : Q').den : Int)
      = ((0 : Q').num) * ((x * (0 : Q')).den : Int)
  show (x.num * (0 : Q').num) * ((0 : Q').den : Int)
      = ((0 : Q').num) * ((x * (0 : Q')).den : Int)
  show (x.num * (0 : Int)) * (1 : Int) = (0 : Int) * ((x * (0 : Q')).den : Int)
  rw [Int.mul_zero, Int.zero_mul, Int.zero_mul]

/-- **The shifted secant** `Sm n`: `Sm 0 = 0`, `Sm 1 = 1`, `Sm (m+2) = ddSecant m`.
This shifts `ddSecant` down by two indices so that the divided-difference identity
`T_n(b) − T_n(a) ≈ (b−a)·Sm n` acquires TRIVIAL base cases (`n = 0, 1`), pushing
all the content into the uniform three-term recurrence `SmRec`. -/
def Sm (a b : Q') : Nat → Q'
  | 0 => 0
  | 1 => 1
  | (m + 2) => ddSecant m a b

/-- `ddSecant 0 a b ≈ 2b + 2a`. -/
theorem ddSecant0_eqv (a b : Q') :
    ddSecant 0 a b ≈ (2 : Q') * b + (2 : Q') * a := by
  show ((2 : Q') * b) + ((0 : Q') + (2 : Q') * ((1 : Q') * a))
      ≈ (2 : Q') * b + (2 : Q') * a
  rw [Q'.zero_add']
  exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv a))

/-- **Base recurrence `n = 0`** (`Sm`-form): `ddSecant 0 ≈ 2b·1 − 0 + 2·T_1(a)`. -/
theorem Sbase0 (a b : Q') :
    ddSecant 0 a b
      ≈ (((2 : Q') * b) * (1 : Q') + (-(0 : Q'))) + (2 : Q') * Cheb.T 1 a := by
  have hneg0 : (-(0 : Q')) ≈ (0 : Q') := by decide
  -- RHS ≈ 2b + 2a
  have hR : (((2 : Q') * b) * (1 : Q') + (-(0 : Q'))) + (2 : Q') * Cheb.T 1 a
      ≈ (2 : Q') * b + (2 : Q') * a := by
    have hfst : ((2 : Q') * b) * (1 : Q') + (-(0 : Q')) ≈ (2 : Q') * b := by
      calc ((2 : Q') * b) * (1 : Q') + (-(0 : Q'))
          ≈ (2 : Q') * b + (-(0 : Q')) :=
            Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv _)
        _ ≈ (2 : Q') * b + (0 : Q') := Q'.add_eqv_congr_left _ _ _ hneg0
        _ ≈ (2 : Q') * b := by rw [Q'.add_zero']; exact Q'.eqv_refl _
    -- Cheb.T 1 a = a
    show (((2 : Q') * b) * (1 : Q') + (-(0 : Q'))) + (2 : Q') * a
        ≈ (2 : Q') * b + (2 : Q') * a
    exact Q'.add_eqv_congr_right _ _ _ hfst
  exact Q'.eqv_trans _ _ _ (ddSecant0_eqv a b) (Q'.eqv_symm hR)

/-- **Base recurrence `n = 1`** (`Sm`-form):
`ddSecant 1 ≈ 2b·ddSecant 0 − 1 + 2·T_2(a)`. -/
theorem Sbase1 (a b : Q') :
    ddSecant 1 a b
      ≈ (((2 : Q') * b) * (ddSecant 0 a b) + (-(1 : Q'))) + (2 : Q') * Cheb.T 2 a := by
  -- cross-term normalization  (2b)(2a) ≈ 2·((2b)·a)
  have hcross : ((2 : Q') * b) * ((2 : Q') * a) ≈ (2 : Q') * (((2 : Q') * b) * a) := by
    calc ((2 : Q') * b) * ((2 : Q') * a)
        ≈ (((2 : Q') * b) * (2 : Q')) * a :=
          Q'.eqv_symm (Q'.mul_assoc_eqv ((2 : Q') * b) 2 a)
      _ ≈ ((2 : Q') * ((2 : Q') * b)) * a :=
          Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv ((2 : Q') * b) 2)
      _ ≈ (2 : Q') * (((2 : Q') * b) * a) := Q'.mul_assoc_eqv 2 ((2 : Q') * b) a
  -- LHS reduction:  ddSecant 1 ≈ ((2b)(2b) − 1) + (2·T₂(a) + 2·((2b)a))
  have hB1 : ((0 : Q') + (2 : Q') * ((1 : Q') * (Cheb.T 2 a)))
      ≈ (2 : Q') * (Cheb.T 2 a) := by
    rw [Q'.zero_add']
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv (Cheb.T 2 a))
  have hLHS : ddSecant 1 a b
      ≈ (((2 : Q') * b) * ((2 : Q') * b) + (-(1 : Q')))
          + ((2 : Q') * (Cheb.T 2 a) + (2 : Q') * (((2 : Q') * b) * a)) := by
    show (((2 : Q') * b) * ((2 : Q') * b) + (-(1 : Q')))
          + (((0 : Q') + (2 : Q') * ((1 : Q') * (Cheb.T 2 a)))
              + (2 : Q') * (((2 : Q') * b) * a))
        ≈ (((2 : Q') * b) * ((2 : Q') * b) + (-(1 : Q')))
          + ((2 : Q') * (Cheb.T 2 a) + (2 : Q') * (((2 : Q') * b) * a))
    exact Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_right _ _ _ hB1)
  -- RHS reduction to the same canonical form
  have hRHS : (((2 : Q') * b) * (ddSecant 0 a b) + (-(1 : Q'))) + (2 : Q') * Cheb.T 2 a
      ≈ (((2 : Q') * b) * ((2 : Q') * b) + (-(1 : Q')))
          + ((2 : Q') * (Cheb.T 2 a) + (2 : Q') * (((2 : Q') * b) * a)) := by
    -- 2b·ddSecant0 ≈ (2b)(2b) + (2b)(2a) ≈ (2b)(2b) + 2·((2b)a)
    have hmul : ((2 : Q') * b) * (ddSecant 0 a b)
        ≈ ((2 : Q') * b) * ((2 : Q') * b) + (2 : Q') * (((2 : Q') * b) * a) := by
      calc ((2 : Q') * b) * (ddSecant 0 a b)
          ≈ ((2 : Q') * b) * ((2 : Q') * b + (2 : Q') * a) :=
            Q'.mul_eqv_congr_left _ _ _ (ddSecant0_eqv a b)
        _ ≈ ((2 : Q') * b) * ((2 : Q') * b) + ((2 : Q') * b) * ((2 : Q') * a) :=
            Q'.mul_add_eqv _ _ _
        _ ≈ ((2 : Q') * b) * ((2 : Q') * b) + (2 : Q') * (((2 : Q') * b) * a) :=
            Q'.add_eqv_congr_left _ _ _ hcross
    -- abbreviations X, Y, Z
    -- RHS = ((X + Y) + (−1)) + Z  ≈  (X + (−1)) + (Z + Y)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_right _ _ _ hmul)) ?_
    -- now RHS-shape = ((X + Y) + −1) + Z, target = (X + −1) + (Z + Y)
    calc (((( 2 : Q') * b) * ((2 : Q') * b) + (2 : Q') * (((2 : Q') * b) * a))
              + (-(1 : Q'))) + (2 : Q') * Cheb.T 2 a
        ≈ ((((2 : Q') * b) * ((2 : Q') * b) + (-(1 : Q')))
              + (2 : Q') * (((2 : Q') * b) * a)) + (2 : Q') * Cheb.T 2 a := by
            refine Q'.add_eqv_congr_right _ _ _ ?_
            calc (((2 : Q') * b) * ((2 : Q') * b) + (2 : Q') * (((2 : Q') * b) * a))
                    + (-(1 : Q'))
                ≈ ((2 : Q') * b) * ((2 : Q') * b)
                    + ((2 : Q') * (((2 : Q') * b) * a) + (-(1 : Q'))) :=
                  Q'.add_assoc_eqv _ _ _
              _ ≈ ((2 : Q') * b) * ((2 : Q') * b)
                    + ((-(1 : Q')) + (2 : Q') * (((2 : Q') * b) * a)) :=
                  Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)
              _ ≈ (((2 : Q') * b) * ((2 : Q') * b) + (-(1 : Q')))
                    + (2 : Q') * (((2 : Q') * b) * a) :=
                  Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
      _ ≈ (((2 : Q') * b) * ((2 : Q') * b) + (-(1 : Q')))
            + ((2 : Q') * Cheb.T 2 a + (2 : Q') * (((2 : Q') * b) * a)) := by
          refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) ?_
          exact Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)
  exact Q'.eqv_trans _ _ _ hLHS (Q'.eqv_symm hRHS)

/-! ## 5. The secant recurrence residual and the `Sm`-recurrence -/

/-- **The secant recurrence** (the convolution/telescoping residual): for all
`m`, the closed `ddSecant` satisfies the same three-term recurrence as the
divided difference does.  This is the SOLE remaining sub-identity feeding `ddId`
— the `2b`-reindex of the finite convolution `finSum` plus the second-kind
recurrence on the leading `U`-term. -/
def SrecP (a b : Q') : Prop := ∀ m,
  ddSecant (m + 2) a b
    ≈ (((2 : Q') * b) * (ddSecant (m + 1) a b) + (-(ddSecant m a b)))
        + (2 : Q') * Cheb.T (m + 3) a

/-- **The pure finite-convolution residual** `PrecP` — the SHARPEST remaining
sub-identity.  It states the same three-term recurrence for the `finSum`
convolution part alone (`P m := Σ_{j≤m} 2·U_j(b)·T_{m+1−j}(a)`):

    P (m+2)  ≈  2b·P (m+1) − P m + 2·T_{m+3}(a).

This is the `2b`-reindex of the finite convolution — the sole content that is not
elementary recurrence bookkeeping.  It is a genuine identity (verified `m = 0,1,2`
upstream); everything else feeding `ddId` is proved here. -/
def PrecP (a b : Q') : Prop := ∀ m,
  RationalTail.finSum (gseq (m + 2) a b) (m + 3)
    ≈ (((2 : Q') * b) * (RationalTail.finSum (gseq (m + 1) a b) (m + 2))
         + (-(RationalTail.finSum (gseq m a b) (m + 1))))
       + (2 : Q') * Cheb.T (m + 3) a

/-- **`SrecP` from the pure convolution `PrecP`.**  Splits the secant recurrence
into the second-kind recurrence `U_{m+3} = 2b·U_{m+2} − U_{m+1}`
(`Cheb.U_succ_succ`) on the leading term and the convolution residual `PrecP` on
the `finSum` part, then regroups.  This closes the `U`-side of `SrecP`, reducing
it to `PrecP`. -/
theorem Srec_of_Prec (a b : Q') (hPrec : PrecP a b) : SrecP a b := by
  intro m
  show Cheb.U (m + 3) b + RationalTail.finSum (gseq (m + 2) a b) (m + 3)
      ≈ (((2 : Q') * b) * (Cheb.U (m + 2) b + RationalTail.finSum (gseq (m + 1) a b) (m + 2))
           + (-(Cheb.U (m + 1) b + RationalTail.finSum (gseq m a b) (m + 1))))
         + (2 : Q') * Cheb.T (m + 3) a
  rw [Cheb.U_succ_succ (m + 1) b]
  -- LHS = ((2b·U(m+2) − U(m+1)) + P2) ;  push P2 through PrecP
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (hPrec m)) ?_
  -- regroup the five atoms A=2b·U(m+2), B=−U(m+1), C=2b·P1, Dd=−P0, E=2·T
  calc (((2 : Q') * b) * (Cheb.U (m + 2) b) + (-(Cheb.U (m + 1) b)))
          + ((((2 : Q') * b) * (RationalTail.finSum (gseq (m + 1) a b) (m + 2))
               + (-(RationalTail.finSum (gseq m a b) (m + 1)))) + (2 : Q') * Cheb.T (m + 3) a)
      ≈ ((((2 : Q') * b) * (Cheb.U (m + 2) b) + (-(Cheb.U (m + 1) b)))
           + (((2 : Q') * b) * (RationalTail.finSum (gseq (m + 1) a b) (m + 2))
               + (-(RationalTail.finSum (gseq m a b) (m + 1))))) + (2 : Q') * Cheb.T (m + 3) a :=
        Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
    _ ≈ ((((2 : Q') * b) * (Cheb.U (m + 2) b)
             + ((2 : Q') * b) * (RationalTail.finSum (gseq (m + 1) a b) (m + 2)))
           + ((-(Cheb.U (m + 1) b)) + (-(RationalTail.finSum (gseq m a b) (m + 1)))))
           + (2 : Q') * Cheb.T (m + 3) a :=
        Q'.add_eqv_congr_right _ _ _ (Q'.add_swap_inner _ _ _ _)
    _ ≈ (((2 : Q') * b) * (Cheb.U (m + 2) b + RationalTail.finSum (gseq (m + 1) a b) (m + 2))
           + (-(Cheb.U (m + 1) b + RationalTail.finSum (gseq m a b) (m + 1))))
           + (2 : Q') * Cheb.T (m + 3) a :=
        Q'.add_eqv_congr_right _ _ _
          (Cheb.add_eqv_congr _ _ _ _
            (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))
            (Q'.eqv_symm (Q'.neg_add_eqv _ _)))

/-- **The `Sm`-recurrence** at every index: `Sm (n+2) ≈ 2b·Sm(n+1) − Sm n +
2·T_{n+1}(a)`, from the two base cases and the secant recurrence. -/
theorem SmRec (a b : Q') (hSrec : SrecP a b) : ∀ n,
    Sm a b (n + 2)
      ≈ (((2 : Q') * b) * (Sm a b (n + 1)) + (-(Sm a b n)))
          + (2 : Q') * Cheb.T (n + 1) a
  | 0 => Sbase0 a b
  | 1 => Sbase1 a b
  | (m + 2) => hSrec m

/-! ### Closing `PrecP`: the `2b`-reindex of the finite convolution -/

/-- All-atom core of the convolution term shift.  With `c = 2b`, `p = U_{j+1}(b)`,
`v = U_j(b)`, `t = T_{m+1−j}(a)` and `U_{j+2} = c·p − v` (`Cheb.U_succ_succ`):

    c·(2·(p·t))  ≈  2·((c·p − v)·t) + 2·(v·t).

The `2·(v·t)` cross-terms cancel; the `2·((c·p)·t)` survives. -/
theorem htermCore (c p t v : Q') :
    c * ((2 : Q') * (p * t))
      ≈ (2 : Q') * (((c * p + (-v)) * t)) + (2 : Q') * (v * t) := by
  -- LHS ≈ 2·((c·p)·t)
  have hL : c * ((2 : Q') * (p * t)) ≈ (2 : Q') * ((c * p) * t) := by
    calc c * ((2 : Q') * (p * t))
        ≈ (c * (2 : Q')) * (p * t) := Q'.eqv_symm (Q'.mul_assoc_eqv c 2 (p * t))
      _ ≈ ((2 : Q') * c) * (p * t) := Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv c 2)
      _ ≈ (2 : Q') * (c * (p * t)) := Q'.mul_assoc_eqv 2 c (p * t)
      _ ≈ (2 : Q') * ((c * p) * t) :=
          Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv c p t))
  -- RHS ≈ 2·((c·p)·t)
  have hR : (2 : Q') * (((c * p + (-v)) * t)) + (2 : Q') * (v * t)
      ≈ (2 : Q') * ((c * p) * t) := by
    have hd : (c * p + (-v)) * t ≈ (c * p) * t + (-(v * t)) :=
      Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _ (Q'.neg_mul_eqv v t))
    calc (2 : Q') * (((c * p + (-v)) * t)) + (2 : Q') * (v * t)
        ≈ (2 : Q') * ((c * p) * t + (-(v * t))) + (2 : Q') * (v * t) :=
          Q'.add_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left _ _ _ hd)
      _ ≈ ((2 : Q') * ((c * p) * t) + (2 : Q') * (-(v * t))) + (2 : Q') * (v * t) :=
          Q'.add_eqv_congr_right _ _ _ (Q'.mul_add_eqv _ _ _)
      _ ≈ ((2 : Q') * ((c * p) * t) + (-((2 : Q') * (v * t)))) + (2 : Q') * (v * t) :=
          Q'.add_eqv_congr_right _ _ _
            (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv (2 : Q') (v * t)))
      _ ≈ (2 : Q') * ((c * p) * t)
            + ((-((2 : Q') * (v * t))) + (2 : Q') * (v * t)) :=
          Q'.add_assoc_eqv _ _ _
      _ ≈ (2 : Q') * ((c * p) * t) + (0 : Q') :=
          Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv ((2 : Q') * (v * t)))
      _ ≈ (2 : Q') * ((c * p) * t) := by rw [Q'.add_zero']; exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

/-- **The pure convolution recurrence `PrecP` — PROVED.**  The `2b`-reindex of the
finite convolution `finSum`, via `const_mul_finSum`, `finSum_peel_left`,
`finSum_add`, and the second-kind recurrence `htermCore`.  This discharges the
last residual of `ddId`. -/
theorem Prec (a b : Q') : PrecP a b := by
  intro m
  -- per-index term shift  c·gseq(m+1)(j+1) ≈ gseq(m+2)(j+2) + gseq m j
  have hterm : ∀ j, ((2 : Q') * b) * (gseq (m + 1) a b (j + 1))
      ≈ gseq (m + 2) a b (j + 2) + gseq m a b j := by
    intro j
    have e1 : (m + 1) + 1 - (j + 1) = m + 1 - j := by omega
    have e2 : (m + 2) + 1 - (j + 2) = m + 1 - j := by omega
    show ((2 : Q') * b)
          * ((2 : Q') * (Cheb.U (j + 1) b * Cheb.T ((m + 1) + 1 - (j + 1)) a))
        ≈ (2 : Q') * (Cheb.U (j + 2) b * Cheb.T ((m + 2) + 1 - (j + 2)) a)
            + (2 : Q') * (Cheb.U j b * Cheb.T (m + 1 - j) a)
    rw [e1, e2, Cheb.U_succ_succ j b]
    exact htermCore ((2 : Q') * b) (Cheb.U (j + 1) b) (Cheb.T (m + 1 - j) a)
      (Cheb.U j b)
  -- (I)  P2 ≈ gseq(m+2)0 + (g1 + FA)
  have hP2 : RationalTail.finSum (gseq (m + 2) a b) (m + 3)
      ≈ gseq (m + 2) a b 0
        + (gseq (m + 2) a b 1
            + RationalTail.finSum (fun j => gseq (m + 2) a b (j + 2)) (m + 1)) := by
    refine Q'.eqv_trans _ _ _
      (RationalTail.finSum_peel_left (gseq (m + 2) a b) (m + 2)) ?_
    refine Q'.add_eqv_congr_left _ _ _ ?_
    exact RationalTail.finSum_peel_left (fun j => gseq (m + 2) a b (j + 1)) (m + 1)
  -- (II) c·P1 ≈ g1 + (FA + P0)
  have hCP1 : ((2 : Q') * b) * (RationalTail.finSum (gseq (m + 1) a b) (m + 2))
      ≈ gseq (m + 2) a b 1
        + (RationalTail.finSum (fun j => gseq (m + 2) a b (j + 2)) (m + 1)
            + RationalTail.finSum (gseq m a b) (m + 1)) := by
    -- pull the scalar in, peel, rewrite termwise, split
    refine Q'.eqv_trans _ _ _
      (RationalTail.const_mul_finSum (gseq (m + 1) a b) ((2 : Q') * b) (m + 2)) ?_
    refine Q'.eqv_trans _ _ _
      (RationalTail.finSum_peel_left
        (fun j => ((2 : Q') * b) * (gseq (m + 1) a b j)) (m + 1)) ?_
    -- head term  c·gseq(m+1)0 ≈ g1
    have hhead : ((2 : Q') * b) * (gseq (m + 1) a b 0) ≈ gseq (m + 2) a b 1 := by
      show ((2 : Q') * b) * ((2 : Q') * (Cheb.U 0 b * Cheb.T ((m + 1) + 1 - 0) a))
          ≈ (2 : Q') * (Cheb.U 1 b * Cheb.T ((m + 2) + 1 - 1) a)
      have ee : (m + 1) + 1 - 0 = (m + 2) + 1 - 1 := by omega
      rw [ee]
      -- 2b·(2·(1·t)) ≈ 2·((2b)·t)
      calc ((2 : Q') * b) * ((2 : Q') * ((1 : Q') * Cheb.T ((m + 2) + 1 - 1) a))
          ≈ ((2 : Q') * b) * ((2 : Q') * (Cheb.T ((m + 2) + 1 - 1) a)) :=
            Q'.mul_eqv_congr_left _ _ _
              (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv _))
        _ ≈ (((2 : Q') * b) * (2 : Q')) * (Cheb.T ((m + 2) + 1 - 1) a) :=
            Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
        _ ≈ ((2 : Q') * ((2 : Q') * b)) * (Cheb.T ((m + 2) + 1 - 1) a) :=
            Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)
        _ ≈ (2 : Q') * (((2 : Q') * b) * (Cheb.T ((m + 2) + 1 - 1) a)) :=
            Q'.mul_assoc_eqv _ _ _
    -- tail  Σ (c·gseq(m+1)(j+1)) ≈ FA + P0
    have htail : RationalTail.finSum
          (fun j => ((2 : Q') * b) * (gseq (m + 1) a b (j + 1))) (m + 1)
        ≈ RationalTail.finSum (fun j => gseq (m + 2) a b (j + 2)) (m + 1)
            + RationalTail.finSum (gseq m a b) (m + 1) := by
      refine Q'.eqv_trans _ _ _
        (RationalTail.finSum_eqv_congr_lt
          (fun j => ((2 : Q') * b) * (gseq (m + 1) a b (j + 1)))
          (fun j => gseq (m + 2) a b (j + 2) + gseq m a b j)
          (m + 1) (fun i _ => hterm i)) ?_
      exact RationalTail.finSum_add
        (fun j => gseq (m + 2) a b (j + 2)) (gseq m a b) (m + 1)
    exact Cheb.add_eqv_congr _ _ _ _ hhead htail
  -- gseq(m+2)0 ≈ 2·T(m+3)a
  have hg0 : gseq (m + 2) a b 0 ≈ (2 : Q') * Cheb.T (m + 3) a := by
    show (2 : Q') * (Cheb.U 0 b * Cheb.T ((m + 2) + 1 - 0) a)
        ≈ (2 : Q') * Cheb.T (m + 3) a
    have ee : (m + 2) + 1 - 0 = m + 3 := by omega
    rw [ee]
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv _)
  -- assemble:  both sides ≈ W = (g1 + FA) + 2·T(m+3)a
  have hLW : RationalTail.finSum (gseq (m + 2) a b) (m + 3)
      ≈ (gseq (m + 2) a b 1
          + RationalTail.finSum (fun j => gseq (m + 2) a b (j + 2)) (m + 1))
        + (2 : Q') * Cheb.T (m + 3) a := by
    refine Q'.eqv_trans _ _ _ hP2 ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hg0) ?_
    exact Q'.add_comm_eqv _ _
  have hRW : (((2 : Q') * b) * (RationalTail.finSum (gseq (m + 1) a b) (m + 2))
        + (-(RationalTail.finSum (gseq m a b) (m + 1))))
        + (2 : Q') * Cheb.T (m + 3) a
      ≈ (gseq (m + 2) a b 1
          + RationalTail.finSum (fun j => gseq (m + 2) a b (j + 2)) (m + 1))
        + (2 : Q') * Cheb.T (m + 3) a := by
    refine Q'.add_eqv_congr_right _ _ _ ?_
    -- c·P1 + −P0 ≈ g1 + FA
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hCP1) ?_
    calc (gseq (m + 2) a b 1
            + (RationalTail.finSum (fun j => gseq (m + 2) a b (j + 2)) (m + 1)
                + RationalTail.finSum (gseq m a b) (m + 1)))
          + (-(RationalTail.finSum (gseq m a b) (m + 1)))
        ≈ gseq (m + 2) a b 1
            + ((RationalTail.finSum (fun j => gseq (m + 2) a b (j + 2)) (m + 1)
                + RationalTail.finSum (gseq m a b) (m + 1))
              + (-(RationalTail.finSum (gseq m a b) (m + 1)))) :=
          Q'.add_assoc_eqv _ _ _
      _ ≈ gseq (m + 2) a b 1
            + (RationalTail.finSum (fun j => gseq (m + 2) a b (j + 2)) (m + 1)
              + (RationalTail.finSum (gseq m a b) (m + 1)
                  + (-(RationalTail.finSum (gseq m a b) (m + 1))))) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.add_assoc_eqv _ _ _)
      _ ≈ gseq (m + 2) a b 1
            + (RationalTail.finSum (fun j => gseq (m + 2) a b (j + 2)) (m + 1)
              + (0 : Q')) :=
          Q'.add_eqv_congr_left _ _ _
            (Q'.add_eqv_congr_left _ _ _
              (ChebU.add_neg_self_eqv (RationalTail.finSum (gseq m a b) (m + 1))))
      _ ≈ gseq (m + 2) a b 1
            + RationalTail.finSum (fun j => gseq (m + 2) a b (j + 2)) (m + 1) := by
          rw [Q'.add_zero']; exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hLW (Q'.eqv_symm hRW)

/-- **The secant recurrence, PROVED** (unconditional), from `Prec` via
`Srec_of_Prec`. -/
theorem Srec (a b : Q') : SrecP a b := Srec_of_Prec a b (Prec a b)

/-! ## 6. The step-matching identity and the two-step induction -/

/-- **Step-matching**: pushes the scalar `w = b − a` through the recurrence
shape.  `w·((2b·S₁ − S₀) + 2·Ta) ≈ (2b·(w·S₁) − w·S₀) + w·(2·Ta)`. -/
theorem stepMatch (w S1 S0 Ta b : Q') :
    w * ((((2 : Q') * b) * S1 + (-S0)) + ((2 : Q') * Ta))
      ≈ (((2 : Q') * b) * (w * S1) + (-(w * S0))) + w * ((2 : Q') * Ta) := by
  have hWS1 : w * (((2 : Q') * b) * S1) ≈ ((2 : Q') * b) * (w * S1) := by
    calc w * (((2 : Q') * b) * S1)
        ≈ (w * ((2 : Q') * b)) * S1 := Q'.eqv_symm (Q'.mul_assoc_eqv w (2 * b) S1)
      _ ≈ (((2 : Q') * b) * w) * S1 :=
          Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv w (2 * b))
      _ ≈ ((2 : Q') * b) * (w * S1) := Q'.mul_assoc_eqv (2 * b) w S1
  have hWS0 : w * (-S0) ≈ (-(w * S0)) := Q'.mul_neg_eqv w S0
  calc w * ((((2 : Q') * b) * S1 + (-S0)) + ((2 : Q') * Ta))
      ≈ w * (((2 : Q') * b) * S1 + (-S0)) + w * ((2 : Q') * Ta) :=
        Q'.mul_add_eqv _ _ _
    _ ≈ (w * (((2 : Q') * b) * S1) + w * (-S0)) + w * ((2 : Q') * Ta) :=
        Q'.add_eqv_congr_right _ _ _ (Q'.mul_add_eqv _ _ _)
    _ ≈ (((2 : Q') * b) * (w * S1) + (-(w * S0))) + w * ((2 : Q') * Ta) :=
        Q'.add_eqv_congr_right _ _ _ (Cheb.add_eqv_congr _ _ _ _ hWS1 hWS0)

/-- **The two-step induction step**: from the identity at `n` and `n+1`, and the
`Sm`-recurrence, conclude the identity at `n+2`.  Combines `Drec` with
`stepMatch`. -/
theorem Qstep (a b : Q')
    (hsm : ∀ n, Sm a b (n + 2)
      ≈ (((2 : Q') * b) * (Sm a b (n + 1)) + (-(Sm a b n)))
          + (2 : Q') * Cheb.T (n + 1) a)
    (n : Nat)
    (hn : Cheb.T n b + (-(Cheb.T n a)) ≈ (b + (-a)) * Sm a b n)
    (hn1 : Cheb.T (n + 1) b + (-(Cheb.T (n + 1) a)) ≈ (b + (-a)) * Sm a b (n + 1)) :
    Cheb.T (n + 2) b + (-(Cheb.T (n + 2) a)) ≈ (b + (-a)) * Sm a b (n + 2) := by
  have hD := Drec n a b
  -- substitute the two IHs into the Drec RHS
  have hsub :
      (((2 : Q') * b) * (Cheb.T (n + 1) b + (-(Cheb.T (n + 1) a)))
          + (-(Cheb.T n b + (-(Cheb.T n a)))))
        + (b + (-a)) * ((2 : Q') * Cheb.T (n + 1) a)
      ≈ (((2 : Q') * b) * ((b + (-a)) * Sm a b (n + 1))
          + (-((b + (-a)) * Sm a b n)))
        + (b + (-a)) * ((2 : Q') * Cheb.T (n + 1) a) :=
    Q'.add_eqv_congr_right _ _ _
      (Cheb.add_eqv_congr _ _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hn1) (Q'.neg_eqv_congr _ _ hn))
  -- the RHS via the Sm-recurrence + stepMatch
  have hRHS : (b + (-a)) * Sm a b (n + 2)
      ≈ (((2 : Q') * b) * ((b + (-a)) * Sm a b (n + 1))
          + (-((b + (-a)) * Sm a b n)))
        + (b + (-a)) * ((2 : Q') * Cheb.T (n + 1) a) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (hsm n))
      (stepMatch (b + (-a)) (Sm a b (n + 1)) (Sm a b n) (Cheb.T (n + 1) a) b)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ hD hsub) (Q'.eqv_symm hRHS)

/-- Trivial base `n = 0`: `T_0(b) − T_0(a) ≈ (b − a)·Sm 0`  (`0 ≈ (b−a)·0`). -/
theorem Qbase0 (a b : Q') :
    Cheb.T 0 b + (-(Cheb.T 0 a)) ≈ (b + (-a)) * Sm a b 0 := by
  show (1 : Q') + (-(1 : Q')) ≈ (b + (-a)) * (0 : Q')
  exact Q'.eqv_trans _ _ _ (ChebU.add_neg_self_eqv (1 : Q'))
    (Q'.eqv_symm (mulZero (b + (-a))))

/-- Trivial base `n = 1`: `T_1(b) − T_1(a) ≈ (b − a)·Sm 1`  (`(b−a) ≈ (b−a)·1`). -/
theorem Qbase1 (a b : Q') :
    Cheb.T 1 b + (-(Cheb.T 1 a)) ≈ (b + (-a)) * Sm a b 1 := by
  show (b + (-a)) ≈ (b + (-a)) * (1 : Q')
  exact Q'.eqv_symm (Q'.mul_one_eqv (b + (-a)))

/-- **Two-step induction packager**: the divided-difference identity holds at `n`
and `n+1` simultaneously, for every `n`. -/
theorem ddId_pair (a b : Q')
    (hsm : ∀ n, Sm a b (n + 2)
      ≈ (((2 : Q') * b) * (Sm a b (n + 1)) + (-(Sm a b n)))
          + (2 : Q') * Cheb.T (n + 1) a) : ∀ n,
    (Cheb.T n b + (-(Cheb.T n a)) ≈ (b + (-a)) * Sm a b n)
    ∧ (Cheb.T (n + 1) b + (-(Cheb.T (n + 1) a)) ≈ (b + (-a)) * Sm a b (n + 1))
  | 0 => ⟨Qbase0 a b, Qbase1 a b⟩
  | (n + 1) =>
      let ih := ddId_pair a b hsm n
      ⟨ih.2, Qstep a b hsm n ih.1 ih.2⟩

/-! ## 7. The divided-difference identity `ddId` (unconditional) -/

/-- **The exact divided-difference identity** — PROVED unconditionally over `Q'`:

    T_{k+2}(b) − T_{k+2}(a)  ≈  (b − a) · ddSecant k a b.

The two-step telescoping induction (bases `Qbase0`/`Qbase1`, step `Qstep`) driven
by the D-recurrence `Drec` and the fully proved secant recurrence `Srec`.
(`Sm a b (k+2)` is definitionally `ddSecant k a b`.) -/
theorem ddId (a b : Q') (k : Nat) :
    Cheb.T (k + 2) b + (-(Cheb.T (k + 2) a)) ≈ (b + (-a)) * ddSecant k a b :=
  (ddId_pair a b (SmRec a b (Srec a b)) (k + 2)).1

/-! ## 8. Re-assembly of `CosNodeResidual` / `DeMoivreNode` from the walls -/

/-- **Assembly** — a full `CosNodeBracket.CosNodeResidual k` from the (now fully
proved) DD/Markov side plus the three genuine rational-`π` sign walls, discharging
the `ddId` argument of `CosPiEnclosure.cosNodeResidual_of_walls`.  The DD side is
UNCONDITIONAL; only the sign walls remain hypotheses. -/
def cosNodeResidual_of (k : Nat) (lo hi : Q')
    (hlo1 : (-(1 : Q')) ≤ lo) (hhi1 : hi ≤ (1 : Q')) (hle : lo ≤ hi)
    (loSign : ChebRoot.Ueval (k + 1) lo ≤ (0 : Q'))
    (hiSign : (0 : Q') ≤ ChebRoot.Ueval (k + 1) hi)
    (tsign : Cheb.T (k + 2) hi + Q'.ofNat ((k + 2) ^ 2) * (hi + -lo) ≤ (0 : Q')) :
    CosNodeBracket.CosNodeResidual k :=
  CosPiEnclosure.cosNodeResidual_of_walls k lo hi hlo1 hhi1 hle
    (fun a b _ _ _ => ddId a b k) loSign hiSign tsign

/-- **De Moivre node** from the three sign walls alone (the DD/Markov side is now
fully proved); general-`M` off-diagonal OS2 Gram positivity downstream. -/
def deMoivreNode_of (k : Nat) (lo hi : Q')
    (hlo1 : (-(1 : Q')) ≤ lo) (hhi1 : hi ≤ (1 : Q')) (hle : lo ≤ hi)
    (loSign : ChebRoot.Ueval (k + 1) lo ≤ (0 : Q'))
    (hiSign : (0 : Q') ≤ ChebRoot.Ueval (k + 1) hi)
    (tsign : Cheb.T (k + 2) hi + Q'.ofNat ((k + 2) ^ 2) * (hi + -lo) ≤ (0 : Q')) :
    ChebRotationPair.DeMoivreNode (k + 1) :=
  CosNodeBracket.deMoivreNode_of_residual k
    (cosNodeResidual_of k lo hi hlo1 hhi1 hle loSign hiSign tsign)

end YMGap.Continuum.DDIdentity

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.DDIdentity.regroup6
#print axioms YMGap.Continuum.DDIdentity.Drec_abs
#print axioms YMGap.Continuum.DDIdentity.Drec
#print axioms YMGap.Continuum.DDIdentity.regroup4
#print axioms YMGap.Continuum.DDIdentity.expand2
#print axioms YMGap.Continuum.DDIdentity.ddId_zero
#print axioms YMGap.Continuum.DDIdentity.Sbase0
#print axioms YMGap.Continuum.DDIdentity.Sbase1
#print axioms YMGap.Continuum.DDIdentity.stepMatch
#print axioms YMGap.Continuum.DDIdentity.Qstep
#print axioms YMGap.Continuum.DDIdentity.htermCore
#print axioms YMGap.Continuum.DDIdentity.Srec_of_Prec
#print axioms YMGap.Continuum.DDIdentity.Prec
#print axioms YMGap.Continuum.DDIdentity.Srec
#print axioms YMGap.Continuum.DDIdentity.ddId
#print axioms YMGap.Continuum.DDIdentity.cosNodeResidual_of
#print axioms YMGap.Continuum.DDIdentity.deMoivreNode_of
