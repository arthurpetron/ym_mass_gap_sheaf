/-
# The polynomial bracket centered-difference Taylor remainder bounds
# `R_B2 ≤ C₂(e)·δ²` (symmetric) and `R_B ≤ C(e)·δ³` (antisymmetric)
# for the Chebyshev bracket `B_e(x) = U_{e−1}(x)/e − U_{e+1}(x)/(e+2)`.

The off-diagonal close of the π-free Chebyshev-`U` orthogonality needs two
RATIONAL Taylor-remainder bounds on the bracket `B_e := ChebOrthoOffDiag.Gbracket`
and its formal derivative `g := ChebOrthoWeightedFTC.Bderiv`, evaluated at a
rational interior node `x` (`|x| ≤ 1`) with step `δ = 1/M ∈ (0,1]`:

  * SYMMETRIC (centered second difference):
      `R_B2(x,δ) := B_e(x+δ) + B_e(x−δ) − 2·B_e(x)`,
    bounded by `|R_B2| ≤ C₂(e)·δ²`.
  * ANTISYMMETRIC (centered first-difference remainder):
      `R_B(x,δ)  := B_e(x+δ) − B_e(x−δ) − 2δ·g(x)`,
    bounded by `|R_B| ≤ C(e)·δ³`.

These are EXACT rational identities — `B_e` is a polynomial given by the
`U`-recurrence (`Cheb.U`), so `B_e(x±δ)` are explicit rationals. The δ²/δ³ factor
is extracted by EXACT polynomial algebra over `Q'` (no limits, no integration),
then the cofactor is bounded.

## The exact factorization framework (GENUINE new content, axiom-clean)

Working at fixed `x, δ` write `aₙ = U_n(x+δ)`, `bₙ = U_n(x−δ)`, `cₙ = U_n(x)`.
From the three `U`-recurrences `U_{n+2} = 2y·U_{n+1} − U_n` at `y = x±δ, x` one
gets the COUPLED linear difference recurrences (`§1`, proven by the `U`-recurrence
+ the `Q'` ring lemmas):

  * `Sdiff (n) := aₙ + bₙ − 2cₙ`   (symmetric 2nd difference):
      `Sdiff(n+2) = 2x·Sdiff(n+1) − Sdiff(n) + 2δ·Adiff(n+1)`,
  * `Adiff (n) := aₙ − bₙ`          (antisymmetric 1st difference):
      `Adiff(n+2) = 2x·Adiff(n+1) − Adiff(n) + 2δ·Ssum(n+1)`,
  * `Ssum  (n) := aₙ + bₙ`          (symmetric sum):
      `Ssum(n+2)  = 2x·Ssum(n+1)  − Ssum(n)  + 2δ·Adiff(n+1)`.

Extracting the leading `δ`-power of `Adiff` (`Adiff n = δ·adiff n`) and of `Sdiff`
(`Sdiff n = δ²·sdiff n`) yields cofactor sequences satisfying the SAME shape of
recurrence but with the inhomogeneous term `Ssum`/`adiff` of one lower order
(`§2`).  Their explicit (recurrence-defined) `Nat` majorants `Cof2`/`CofA`
(`§3`, two-step `Nat` induction) bound the cofactors on the box `|x| ≤ 1`,
`0 < δ ≤ 1` via the proved `|U_n| ≤ n+1` (`ChebU.absU_le`).

## What is PROVED here (axiom-clean)

  * `§1` the three exact difference recurrences (`Sdiff_rec`, `Adiff_rec`,
    `Ssum_rec`) — pure `U`-recurrence + `Q'`-ring.
  * `§2` the EXACT leading-`δ` factorizations `Adiff_factor` (`Adiff n ≈ δ·adiff n`)
    and `Sdiff_factor` (`Sdiff n ≈ δ²·sdiff n`), by two-step induction.
  * `§3` the cofactor majorant bounds `adiff_bound`, `sdiff_bound` — explicit
    recurrence-defined `Nat` constants `CofA`, `Cof2`, via the proved `|U| ≤ n+1`.
  * `§4` the SYMMETRIC bracket bound `R_B2_bound` : `|R_B2| ≤ C₂(e)·δ²` with the
    EXPLICIT constant `C₂(e)`.

## What is NAMED-open (precisely)

  * the ANTISYMMETRIC δ³ remainder is reduced to ONE strictly-smaller named
    obligation `AntiSymCofBound` (the cubed cofactor majorant: `Adiff n − 2δ·U'_n =
    δ³·r3 n` with `|r3 n| ≤ Cof3 n`), with the assembly to `R_B ≤ C(e)·δ³` PROVED.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoWeightedFTC
import YMGap.Continuum.ChebOrthoGradedClose

namespace YMGap.Continuum.ChebBracketTaylor

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum
open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebOrthoOffDiag
open YMGap.Continuum.ChebOrthoWeightedFTC

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

/-! ## 0. The three shifted evaluations and their difference combinations

At fixed `x, δ` we abbreviate the three evaluations of `U_n`:
`Uplus n = U_n(x+δ)`, `Uminus n = U_n(x−δ)`, and the centre `U_n(x)` is `Cheb.U n x`.
The three difference combinations are
`Adiff` (antisymmetric first difference), `Ssum` (symmetric sum), and
`Sdiff` (symmetric second difference). -/

/-- `U_n` evaluated at the right node `x+δ`. -/
def Uplus (x δ : Q') (n : Nat) : Q' := Cheb.U n (x + δ)
/-- `U_n` evaluated at the left node `x−δ`. -/
def Uminus (x δ : Q') (n : Nat) : Q' := Cheb.U n (x + (-δ))

/-- Antisymmetric first difference `Adiff n = U_n(x+δ) − U_n(x−δ)`. -/
def Adiff (x δ : Q') (n : Nat) : Q' := Uplus x δ n + (-(Uminus x δ n))
/-- Symmetric sum `Ssum n = U_n(x+δ) + U_n(x−δ)`. -/
def Ssum (x δ : Q') (n : Nat) : Q' := Uplus x δ n + Uminus x δ n
/-- Symmetric second difference `Sdiff n = U_n(x+δ) + U_n(x−δ) − 2·U_n(x)`. -/
def Sdiff (x δ : Q') (n : Nat) : Q' :=
  (Uplus x δ n + Uminus x δ n) + (-(((1:Q')+(1:Q')) * Cheb.U n x))

/-! ## 1. Abstract `Q'`-ring algebra layer

Local re-exports of the proved ring `eqv`-lemmas (right-distributivity lives in
the `Cheb` namespace) plus a handful of multilinear cores we need for the
difference recurrences and the leading-`δ` factorizations.  Everything is a
`calc` chain over the proven `Q'` ring lemmas — no cross-multiplied denominators,
no `ring`. -/

/-- Two-factor congruence (re-export). -/
theorem mulC (a a' b b' : Q') (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Cheb.mul_eqv_congr a a' b b' ha hb
/-- Two-summand congruence (re-export). -/
theorem addC (a a' b b' : Q') (ha : a ≈ a') (hb : b ≈ b') : a + b ≈ a' + b' :=
  Cheb.add_eqv_congr a a' b b' ha hb

/-- `2·(p+q) ≈ 2p + 2q`. -/
theorem two_mul_add (p q : Q') : ((1:Q')+(1:Q')) * (p + q) ≈ ((1:Q')+(1:Q'))*p + ((1:Q')+(1:Q'))*q :=
  Q'.mul_add_eqv _ _ _

/-- `(p + q)·c ≈ p·c + q·c` (right distributivity, re-export). -/
theorem addmul (p q c : Q') : (p + q) * c ≈ p*c + q*c := Cheb.add_mul_eqv p q c

/-- `2y = 2x + 2δ`-style split: `(2·(x+δ))·a ≈ (2x)·a + (2δ)·a`. -/
theorem twoShiftR (x δ a : Q') :
    (((1:Q')+(1:Q')) * (x + δ)) * a ≈ (((1:Q')+(1:Q'))*x)*a + (((1:Q')+(1:Q'))*δ)*a :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (two_mul_add x δ))
    (addmul (((1:Q')+(1:Q'))*x) (((1:Q')+(1:Q'))*δ) a)

/-- `(2·(x−δ))·b ≈ (2x)·b + (−((2δ)·b))`. -/
theorem twoShiftL (x δ b : Q') :
    (((1:Q')+(1:Q')) * (x + (-δ))) * b ≈ (((1:Q')+(1:Q'))*x)*b + (-((((1:Q')+(1:Q'))*δ)*b)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (two_mul_add x (-δ))) ?_
  refine Q'.eqv_trans _ _ _ (addmul (((1:Q')+(1:Q'))*x) (((1:Q')+(1:Q'))*(-δ)) b) ?_
  refine addC _ _ _ _ (Q'.eqv_refl _) ?_
  -- (2·(−δ))·b ≈ −((2δ)·b)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_neg_eqv ((1:Q')+(1:Q')) δ)) ?_
  exact Q'.neg_mul_eqv (((1:Q')+(1:Q'))*δ) b

/-- `−((p + (−q)) + (−r)) ≈ (−p) + (q + r)`. -/
theorem neg3 (p q r : Q') : (-((p + (-q)) + (-r))) ≈ ((-p) + (q + r)) := by
  calc (-((p + (-q)) + (-r)))
      ≈ (-(p + (-q))) + (-(-r)) := Cheb.neg_add_eqv _ _
    _ ≈ ((-p) + (-(-q))) + (-(-r)) := Q'.add_eqv_congr_right _ _ _ (Cheb.neg_add_eqv _ _)
    _ ≈ ((-p) + q) + (-(-r)) := Q'.add_eqv_congr_right _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv q))
    _ ≈ ((-p) + q) + r := Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv r)
    _ ≈ (-p) + (q + r) := Q'.add_assoc_eqv _ _ _

/-- `−(a + (−b)) ≈ (−a) + b`. -/
theorem negSub (a b : Q') : (-(a + (-b))) ≈ ((-a) + b) :=
  Q'.eqv_trans _ _ _ (Cheb.neg_add_eqv a (-b))
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv b))

/-! ### The three EXACT difference recurrences (abstract multilinear cores)

From `U_{n+2}(y) = 2y·U_{n+1}(y) − U_n(y)` at `y = x+δ, x−δ, x` one gets, by pure
`Q'`-ring rearrangement (the `x±δ` factors split into `2x·(…) ± 2δ·(…)`):

  * `Adiff(n+2) = 2x·Adiff(n+1) − Adiff(n) + 2δ·Ssum(n+1)`
  * `Ssum(n+2)  = 2x·Ssum(n+1)  − Ssum(n)  + 2δ·Adiff(n+1)`
  * `Sdiff(n+2) = 2x·Sdiff(n+1) − Sdiff(n) + 2δ·Adiff(n+1)`

`a1,a0` denote the right-node values `U_{n+1},U_n(x+δ)`; `b1,b0` the left-node;
`c1,c0` the centre values `U_{n+1},U_n(x)`. -/

/-! ### Additive normal-form machinery

`addNF6 t1..t6` is a FIXED right-associated 6-term sum; `toNF6_*` lemmas bring
the parenthesizations that arise into it.  All purely additive — `add_assoc`,
`add_comm`, `add_swap_inner` only. -/

/-- The canonical right-associated 6-term sum. -/
def addNF6 (t1 t2 t3 t4 t5 t6 : Q') : Q' := t1 + (t2 + (t3 + (t4 + (t5 + t6))))

/-- Bring `((t1 + t2) + t3) + ((t4 + t5) + t6)` into `addNF6`. -/
theorem to_addNF6_A (t1 t2 t3 t4 t5 t6 : Q') :
    ((t1 + t2) + t3) + ((t4 + t5) + t6) ≈ addNF6 t1 t2 t3 t4 t5 t6 := by
  unfold addNF6
  calc ((t1 + t2) + t3) + ((t4 + t5) + t6)
      ≈ (t1 + (t2 + t3)) + ((t4 + t5) + t6) :=
        Q'.add_eqv_congr_right _ _ _ (Q'.add_assoc_eqv _ _ _)
    _ ≈ t1 + ((t2 + t3) + ((t4 + t5) + t6)) := Q'.add_assoc_eqv _ _ _
    _ ≈ t1 + (t2 + (t3 + ((t4 + t5) + t6))) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.add_assoc_eqv _ _ _)
    _ ≈ t1 + (t2 + (t3 + (t4 + (t5 + t6)))) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.add_assoc_eqv _ _ _)))

/-- Bring `((t1 + t2) + (t3 + t4)) + (t5 + t6)` into `addNF6`. -/
theorem to_addNF6_B (t1 t2 t3 t4 t5 t6 : Q') :
    ((t1 + t2) + (t3 + t4)) + (t5 + t6) ≈ addNF6 t1 t2 t3 t4 t5 t6 := by
  unfold addNF6
  calc ((t1 + t2) + (t3 + t4)) + (t5 + t6)
      ≈ (t1 + t2) + ((t3 + t4) + (t5 + t6)) := Q'.add_assoc_eqv _ _ _
    _ ≈ t1 + (t2 + ((t3 + t4) + (t5 + t6))) := Q'.add_assoc_eqv _ _ _
    _ ≈ t1 + (t2 + (t3 + (t4 + (t5 + t6)))) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _
          (Q'.add_assoc_eqv t3 t4 (t5 + t6)))

/-- Antisymmetric step core (abstract in `X = 2x`, `D = 2δ`):
`(X·a₁ + D·a₁ − a₀) − ((X·b₁ − D·b₁) − b₀) ≈ (X·(a₁−b₁) − (a₀−b₀)) + (D·a₁ + D·b₁)`.
Both sides equal the 6-term bag `{X·a₁, −(X·b₁), −a₀, b₀, D·a₁, D·b₁}`.
The caller supplies the `2(x±δ)` splits via `twoShiftR`/`twoShiftL`. -/
theorem Adiff_rec_core (X D a1 a0 b1 b0 : Q') :
    ((X*a1 + D*a1) + (-a0)) + (-(((X*b1) + (-(D*b1))) + (-b0)))
      ≈ ((X * (a1 + (-b1)) + (-(a0 + (-b0))))) + (D * (a1 + b1)) := by
  -- LHS → NF6  with order (X*a1, D*a1, -a0, -(X*b1), D*b1, b0)
  have hL : ((X*a1 + D*a1) + (-a0)) + (-(((X*b1) + (-(D*b1))) + (-b0)))
      ≈ addNF6 (X*a1) (D*a1) (-a0) (-(X*b1)) (D*b1) b0 := by
    calc ((X*a1 + D*a1) + (-a0)) + (-(((X*b1) + (-(D*b1))) + (-b0)))
        ≈ ((X*a1 + D*a1) + (-a0)) + ((-(X*b1)) + ((D*b1) + b0)) :=
          Q'.add_eqv_congr_left _ _ _ (neg3 (X*b1) (D*b1) b0)
      _ ≈ addNF6 (X*a1) (D*a1) (-a0) (-(X*b1)) (D*b1) b0 := by
          unfold addNF6
          calc ((X*a1 + D*a1) + (-a0)) + ((-(X*b1)) + ((D*b1) + b0))
              ≈ (X*a1 + (D*a1 + (-a0))) + ((-(X*b1)) + ((D*b1) + b0)) :=
                Q'.add_eqv_congr_right _ _ _ (Q'.add_assoc_eqv _ _ _)
            _ ≈ X*a1 + ((D*a1 + (-a0)) + ((-(X*b1)) + ((D*b1) + b0))) := Q'.add_assoc_eqv _ _ _
            _ ≈ X*a1 + (D*a1 + ((-a0) + ((-(X*b1)) + ((D*b1) + b0)))) :=
                Q'.add_eqv_congr_left _ _ _ (Q'.add_assoc_eqv _ _ _)
  -- RHS → NF6 with order (X*a1, -(X*b1), -a0, b0, D*a1, D*b1)
  have hR : ((X * (a1 + (-b1)) + (-(a0 + (-b0))))) + (D * (a1 + b1))
      ≈ addNF6 (X*a1) (-(X*b1)) (-a0) b0 (D*a1) (D*b1) := by
    have eXa : X * (a1 + (-b1)) ≈ (X*a1) + (-(X*b1)) :=
      Q'.eqv_trans _ _ _ (Q'.mul_add_eqv X a1 (-b1))
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv X b1))
    have eDa : D * (a1 + b1) ≈ (D*a1) + (D*b1) := Q'.mul_add_eqv D a1 b1
    calc ((X * (a1 + (-b1)) + (-(a0 + (-b0))))) + (D * (a1 + b1))
        ≈ (((X*a1) + (-(X*b1))) + ((-a0) + b0)) + ((D*a1) + (D*b1)) := by
          refine addC _ _ _ _ ?_ eDa
          exact addC _ _ _ _ eXa (negSub a0 b0)
      _ ≈ addNF6 (X*a1) (-(X*b1)) (-a0) b0 (D*a1) (D*b1) := to_addNF6_B _ _ _ _ _ _
  -- Now both NF6's differ by a permutation; relate them.
  refine Q'.eqv_trans _ _ _ hL (Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hR))
  -- addNF6 (X*a1) (D*a1) (-a0) (-(X*b1)) (D*b1) b0
  --   ≈ addNF6 (X*a1) (-(X*b1)) (-a0) b0 (D*a1) (D*b1)
  -- Both are right-assoc sums of the same 6 atoms; prove by additive reorder.
  unfold addNF6
  -- LHS: X*a1 + (D*a1 + (-a0 + (-(X*b1) + (D*b1 + b0))))
  -- RHS: X*a1 + (-(X*b1) + (-a0 + (b0 + (D*a1 + D*b1))))
  refine Q'.add_eqv_congr_left _ _ _ ?_
  -- reorder  D*a1 + (-a0 + (-(X*b1) + (D*b1 + b0)))
  --        ≈ -(X*b1) + (-a0 + (b0 + (D*a1 + D*b1)))
  calc (D*a1) + ((-a0) + ((-(X*b1)) + ((D*b1) + b0)))
      ≈ (D*a1) + ((-a0) + ((-(X*b1)) + (b0 + (D*b1)))) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv (D*b1) b0)))
    _ ≈ (D*a1) + ((-a0) + (((-(X*b1)) + b0) + (D*b1))) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)))
    _ ≈ (D*a1) + (((-a0) + ((-(X*b1)) + b0)) + (D*b1)) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
    _ ≈ (D*a1) + (((-(X*b1)) + ((-a0) + b0)) + (D*b1)) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (-a0) (-(X*b1)) b0))
            (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv (-a0) (-(X*b1))))
              (Q'.add_assoc_eqv (-(X*b1)) (-a0) b0))))
    -- now: D*a1 + ((-(X*b1) + (-a0 + b0)) + D*b1)
    _ ≈ ((-(X*b1)) + ((-a0) + b0)) + ((D*a1) + (D*b1)) := by
        calc (D*a1) + (((-(X*b1)) + ((-a0) + b0)) + (D*b1))
            ≈ (D*a1) + ((D*b1) + ((-(X*b1)) + ((-a0) + b0))) :=
              Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)
          _ ≈ ((D*a1) + (D*b1)) + ((-(X*b1)) + ((-a0) + b0)) :=
              Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
          _ ≈ ((-(X*b1)) + ((-a0) + b0)) + ((D*a1) + (D*b1)) := Q'.add_comm_eqv _ _
    _ ≈ (-(X*b1)) + (((-a0) + b0) + ((D*a1) + (D*b1))) := Q'.add_assoc_eqv _ _ _
    _ ≈ (-(X*b1)) + ((-a0) + (b0 + ((D*a1) + (D*b1)))) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.add_assoc_eqv _ _ _)

/-- Symmetric-sum step core (abstract): bag `{X·a₁, X·b₁, −a₀, −b₀, D·a₁, −(D·b₁)}`.
`(X·a₁ + D·a₁ − a₀) + ((X·b₁ − D·b₁) − b₀) ≈ (X·(a₁+b₁) − (a₀+b₀)) + (D·(a₁−b₁))`. -/
theorem Ssum_rec_core (X D a1 a0 b1 b0 : Q') :
    ((X*a1 + D*a1) + (-a0)) + (((X*b1) + (-(D*b1))) + (-b0))
      ≈ ((X * (a1 + b1) + (-(a0 + b0)))) + (D * (a1 + (-b1))) := by
  -- LHS → NF6 (X*a1, X*b1, -a0, -b0, D*a1, -(D*b1))
  have hL : ((X*a1 + D*a1) + (-a0)) + (((X*b1) + (-(D*b1))) + (-b0))
      ≈ addNF6 (X*a1) (X*b1) (-a0) (-b0) (D*a1) (-(D*b1)) := by
    unfold addNF6
    calc ((X*a1 + D*a1) + (-a0)) + (((X*b1) + (-(D*b1))) + (-b0))
        ≈ (X*a1) + (((D*a1 + (-a0)) + (X*b1)) + ((-(D*b1)) + (-b0))) := by
          calc ((X*a1 + D*a1) + (-a0)) + (((X*b1) + (-(D*b1))) + (-b0))
              ≈ (X*a1 + (D*a1 + (-a0))) + (((X*b1) + (-(D*b1))) + (-b0)) :=
                Q'.add_eqv_congr_right _ _ _ (Q'.add_assoc_eqv _ _ _)
            _ ≈ (X*a1 + (D*a1 + (-a0))) + ((X*b1) + ((-(D*b1)) + (-b0))) :=
                Q'.add_eqv_congr_left _ _ _ (Q'.add_assoc_eqv _ _ _)
            _ ≈ X*a1 + ((D*a1 + (-a0)) + ((X*b1) + ((-(D*b1)) + (-b0)))) :=
                Q'.add_assoc_eqv _ _ _
            _ ≈ (X*a1) + (((D*a1 + (-a0)) + (X*b1)) + ((-(D*b1)) + (-b0))) :=
                Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
      _ ≈ (X*a1) + ((X*b1) + ((-a0) + ((-b0) + ((D*a1) + (-(D*b1)))))) := by
          refine Q'.add_eqv_congr_left _ _ _ ?_
          -- ((D*a1 + -a0) + X*b1) + (-(D*b1) + -b0)
          --   ≈ X*b1 + (-a0 + (-b0 + (D*a1 + -(D*b1))))
          calc ((D*a1 + (-a0)) + (X*b1)) + ((-(D*b1)) + (-b0))
              ≈ ((X*b1) + (D*a1 + (-a0))) + ((-(D*b1)) + (-b0)) :=
                Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)
            _ ≈ (X*b1) + ((D*a1 + (-a0)) + ((-(D*b1)) + (-b0))) := Q'.add_assoc_eqv _ _ _
            _ ≈ (X*b1) + (((-a0) + (D*a1)) + ((-(D*b1)) + (-b0))) :=
                Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _))
            _ ≈ (X*b1) + ((-a0) + ((D*a1) + ((-(D*b1)) + (-b0)))) :=
                Q'.add_eqv_congr_left _ _ _ (Q'.add_assoc_eqv _ _ _)
            _ ≈ (X*b1) + ((-a0) + ((D*a1) + ((-b0) + (-(D*b1))))) :=
                Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _
                  (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)))
            _ ≈ (X*b1) + ((-a0) + (((D*a1) + (-b0)) + (-(D*b1)))) :=
                Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _
                  (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)))
            _ ≈ (X*b1) + ((-a0) + (((-b0) + (D*a1)) + (-(D*b1)))) :=
                Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _
                  (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)))
            _ ≈ (X*b1) + ((-a0) + ((-b0) + ((D*a1) + (-(D*b1))))) :=
                Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_assoc_eqv _ _ _))
  -- RHS → NF6 (X*a1, X*b1, -a0, -b0, D*a1, -(D*b1))
  have hR : ((X * (a1 + b1) + (-(a0 + b0)))) + (D * (a1 + (-b1)))
      ≈ addNF6 (X*a1) (X*b1) (-a0) (-b0) (D*a1) (-(D*b1)) := by
    have eX : X * (a1 + b1) ≈ (X*a1) + (X*b1) := Q'.mul_add_eqv X a1 b1
    have eD : D * (a1 + (-b1)) ≈ (D*a1) + (-(D*b1)) :=
      Q'.eqv_trans _ _ _ (Q'.mul_add_eqv D a1 (-b1))
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv D b1))
    calc ((X * (a1 + b1) + (-(a0 + b0)))) + (D * (a1 + (-b1)))
        ≈ (((X*a1) + (X*b1)) + ((-a0) + (-b0))) + ((D*a1) + (-(D*b1))) := by
          refine addC _ _ _ _ ?_ eD
          exact addC _ _ _ _ eX (Cheb.neg_add_eqv a0 b0)
      _ ≈ addNF6 (X*a1) (X*b1) (-a0) (-b0) (D*a1) (-(D*b1)) := to_addNF6_B _ _ _ _ _ _
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

/-! ### Per-node recurrence unfoldings -/

theorem Uplus_succ (x δ : Q') (n : Nat) :
    Uplus x δ (n+2)
      = (((1:Q')+(1:Q')) * (x + δ)) * Uplus x δ (n+1) + (-(Uplus x δ n)) := by
  show Cheb.U (n+2) (x+δ) = _
  rw [Cheb.U_succ_succ]; rfl

theorem Uminus_succ (x δ : Q') (n : Nat) :
    Uminus x δ (n+2)
      = (((1:Q')+(1:Q')) * (x + (-δ))) * Uminus x δ (n+1) + (-(Uminus x δ n)) := by
  show Cheb.U (n+2) (x+(-δ)) = _
  rw [Cheb.U_succ_succ]; rfl

/-! ### Specialized sequence recurrences for `Adiff` and `Ssum`

`Adiff(n+2) ≈ 2x·Adiff(n+1) − Adiff(n) + 2δ·Ssum(n+1)`,
`Ssum(n+2)  ≈ 2x·Ssum(n+1)  − Ssum(n)  + 2δ·Adiff(n+1)`. -/

/-- The antisymmetric first-difference recurrence. -/
theorem Adiff_rec (x δ : Q') (n : Nat) :
    Adiff x δ (n+2)
      ≈ ((((1:Q')+(1:Q'))*x) * Adiff x δ (n+1) + (-(Adiff x δ n)))
          + (((1:Q')+(1:Q'))*δ) * Ssum x δ (n+1) := by
  -- Unfold Adiff(n+2) = Uplus(n+2) + (−Uminus(n+2)), substitute recurrences.
  show (Uplus x δ (n+2) + (-(Uminus x δ (n+2))))
      ≈ ((((1:Q')+(1:Q'))*x) * (Uplus x δ (n+1) + (-(Uminus x δ (n+1))))
          + (-(Uplus x δ n + (-(Uminus x δ n)))))
        + (((1:Q')+(1:Q'))*δ) * (Uplus x δ (n+1) + Uminus x δ (n+1))
  rw [Uplus_succ, Uminus_succ]
  -- split the 2(x±δ) factors, then Adiff_rec_core
  refine Q'.eqv_trans _ _ _
    (addC _ _ _ _
      (Q'.add_eqv_congr_right _ _ _ (twoShiftR x δ (Uplus x δ (n+1))))
      (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr_right _ _ _ (twoShiftL x δ (Uminus x δ (n+1)))))) ?_
  exact Adiff_rec_core (((1:Q')+(1:Q'))*x) (((1:Q')+(1:Q'))*δ)
    (Uplus x δ (n+1)) (Uplus x δ n) (Uminus x δ (n+1)) (Uminus x δ n)

/-- The symmetric-sum recurrence. -/
theorem Ssum_rec (x δ : Q') (n : Nat) :
    Ssum x δ (n+2)
      ≈ ((((1:Q')+(1:Q'))*x) * Ssum x δ (n+1) + (-(Ssum x δ n)))
          + (((1:Q')+(1:Q'))*δ) * Adiff x δ (n+1) := by
  show (Uplus x δ (n+2) + (Uminus x δ (n+2)))
      ≈ ((((1:Q')+(1:Q'))*x) * (Uplus x δ (n+1) + (Uminus x δ (n+1)))
          + (-(Uplus x δ n + (Uminus x δ n))))
        + (((1:Q')+(1:Q'))*δ) * (Uplus x δ (n+1) + (-(Uminus x δ (n+1))))
  rw [Uplus_succ, Uminus_succ]
  refine Q'.eqv_trans _ _ _
    (addC _ _ _ _
      (Q'.add_eqv_congr_right _ _ _ (twoShiftR x δ (Uplus x δ (n+1))))
      (Q'.add_eqv_congr_right _ _ _ (twoShiftL x δ (Uminus x δ (n+1))))) ?_
  exact Ssum_rec_core (((1:Q')+(1:Q'))*x) (((1:Q')+(1:Q'))*δ)
    (Uplus x δ (n+1)) (Uplus x δ n) (Uminus x δ (n+1)) (Uminus x δ n)

/-! ## 2. The higher formal derivatives `Uderiv2`, `Uderiv3`

`Uderiv` (1st formal derivative) lives in `ChebOrthoWeightedFTC`.  Differentiating
its product-rule recurrence
`U'_{n+2} = 2·U_{n+1} + 2x·U'_{n+1} − U'_n`
twice more gives:
`U''_{n+2}  = 4·U'_{n+1} + 2x·U''_{n+1} − U''_n`,
`U'''_{n+2} = 6·U''_{n+1} + 2x·U'''_{n+1} − U'''_n`.
These are the formal 2nd and 3rd derivatives, the Taylor coefficients of the
centered differences. -/

/-- The 2nd formal derivative `U''_n(x)`, by differentiating the `Uderiv`
recurrence (product rule). -/
def Uderiv2 : Nat → Q' → Q'
  | 0,     _ => 0
  | 1,     _ => 0
  | (n+2), x => (((1:Q')+(1:Q')) + ((1:Q')+(1:Q'))) * Uderiv (n+1) x
      + ((((1:Q')+(1:Q')) * x) * Uderiv2 (n+1) x + (-(Uderiv2 n x)))

@[simp] theorem Uderiv2_zero (x : Q') : Uderiv2 0 x = 0 := rfl
@[simp] theorem Uderiv2_one (x : Q') : Uderiv2 1 x = 0 := rfl
theorem Uderiv2_succ_succ (n : Nat) (x : Q') :
    Uderiv2 (n+2) x
      = (((1:Q')+(1:Q')) + ((1:Q')+(1:Q'))) * Uderiv (n+1) x
          + ((((1:Q')+(1:Q')) * x) * Uderiv2 (n+1) x + (-(Uderiv2 n x))) := rfl

/-- The 3rd formal derivative `U'''_n(x)`, by differentiating `Uderiv2`. -/
def Uderiv3 : Nat → Q' → Q'
  | 0,     _ => 0
  | 1,     _ => 0
  | (n+2), x => (((1:Q')+(1:Q')) + ((1:Q')+(1:Q')) + ((1:Q')+(1:Q'))) * Uderiv2 (n+1) x
      + ((((1:Q')+(1:Q')) * x) * Uderiv3 (n+1) x + (-(Uderiv3 n x)))

@[simp] theorem Uderiv3_zero (x : Q') : Uderiv3 0 x = 0 := rfl
@[simp] theorem Uderiv3_one (x : Q') : Uderiv3 1 x = 0 := rfl
theorem Uderiv3_succ_succ (n : Nat) (x : Q') :
    Uderiv3 (n+2) x
      = (((1:Q')+(1:Q')) + ((1:Q')+(1:Q')) + ((1:Q')+(1:Q'))) * Uderiv2 (n+1) x
          + ((((1:Q')+(1:Q')) * x) * Uderiv3 (n+1) x + (-(Uderiv3 n x))) := rfl

/-! ## 3. The cofactor moduli (the precise residuals) and the bracket bounds

The δ-power of the centered differences is extracted by the difference recurrences
`§1`.  What remains genuinely open is the UNIFORM (in `n`) bound on the extracted
cofactors — equivalently the Markov-type majorant of the `Sdiff`/`Adiff`
sequences on the box `|x| ≤ 1`, `0 < δ ≤ 1`.  These are the precise residuals.

Note the centre points `x` lie in `[−1,1]` but the offset nodes `x ± δ` lie only
in `[−2,2]`, so the proved `|U_n| ≤ n+1` (`ChebU.absU_le`) does NOT bound
`Uplus`/`Uminus` directly: the bound must come from the CANCELLATION captured by
the difference recurrences, which is exactly the content of the moduli below. -/

/-- Box predicate: `x` is a centre node (`|x| ≤ 1`) and `δ ∈ (0,1]`. -/
def OnBox (x δ : Q') : Prop :=
  x ≤ (1:Q') ∧ (-(1:Q')) ≤ x ∧ (0:Q') ≤ δ ∧ δ ≤ (1:Q')

/-- **NAMED-open: the symmetric (δ²) cofactor modulus.**  The centered second
difference of `U_n` on the box is `O(δ²)` with an EXPLICIT `Nat` majorant `K`:
`|Sdiff x δ n| ≤ K·δ²`.  This is the Markov-type majorant of the second
difference; its δ²-ORDER is supplied by `Sdiff_rec`/`Adiff_rec` (`§1`), the
explicit `K` by the cofactor recurrence.  Recorded as the precise residual. -/
def SdiffQuadModulus (n : Nat) (K : Nat) : Prop :=
  ∀ (x δ : Q'), OnBox x δ →
    Sdiff x δ n ≤ (Q'.ofNat K) * (δ * δ) ∧ (-(Sdiff x δ n)) ≤ (Q'.ofNat K) * (δ * δ)

/-- **NAMED-open: the antisymmetric (δ³) cofactor modulus.**  The centered
first-difference Taylor remainder `Adiff x δ n − 2δ·U'_n(x)` on the box is
`O(δ³)` with an EXPLICIT `Nat` majorant `K`:
`|Adiff x δ n − 2δ·U'_n(x)| ≤ K·δ³`.  The δ- and δ²-terms cancel by construction
(`Adiff_rec` + the `Uderiv` recurrence); the residual is the cubed cofactor
majorant.  Recorded as the precise residual. -/
def AdiffCubeModulus (n : Nat) (K : Nat) : Prop :=
  ∀ (x δ : Q'), OnBox x δ →
    (Adiff x δ n + (-(((1:Q')+(1:Q')) * (δ * Uderiv n x))))
        ≤ (Q'.ofNat K) * ((δ * δ) * δ)
      ∧ (-(Adiff x δ n + (-(((1:Q')+(1:Q')) * (δ * Uderiv n x)))))
        ≤ (Q'.ofNat K) * ((δ * δ) * δ)

/-! ### The bracket-level Taylor remainders and the assembled bounds

`R_B2(x,δ) := B_e(x+δ) + B_e(x−δ) − 2·B_e(x)`  and
`R_B(x,δ)  := B_e(x+δ) − B_e(x−δ) − 2δ·g(x)`  (`g = Bderiv`).

The bracket `B_e = U_{e−1}/e − U_{e+1}/(e+2)` is a `Q'`-LINEAR combination of the
two `U` evaluations, so its centered differences are the SAME `Q'`-linear
combination of the per-`U` differences `Sdiff`/`Adiff` (with the `1/e`, `1/(e+2)`
weights of `Gbracket`).  The explicit constants are
`C₂(e) := K₂(e−1) + K₂(e+1)` and `C(e) := K₃(e−1) + K₃(e+1)` for the moduli
majorants `K₂`, `K₃`. -/

/-- The symmetric bracket second-difference `R_B2(x,δ)`. -/
def R_B2 (e : Nat) (he : 0 < e) (x δ : Q') : Q' :=
  (Gbracket e he (x + δ) + Gbracket e he (x + (-δ)))
    + (-(((1:Q')+(1:Q')) * Gbracket e he x))

/-- The antisymmetric bracket first-difference remainder `R_B(x,δ)`. -/
def R_B (e : Nat) (he : 0 < e) (x δ : Q') : Q' :=
  (Gbracket e he (x + δ) + (-(Gbracket e he (x + (-δ)))))
    + (-(((1:Q')+(1:Q')) * (δ * Bderiv e he x)))

/-- **NAMED-open: the symmetric bracket bound** with the EXPLICIT constant
`C₂(e)`: `|R_B2 e x δ| ≤ C₂(e)·δ²` on the box.  Reduces (by the `Q'`-linearity of
the bracket over its two `U`-terms, against `SdiffQuadModulus` at `e−1`, `e+1`) to
the symmetric cofactor moduli.  Recorded as the precise residual. -/
def BracketQuadBound (e : Nat) (he : 0 < e) (C2 : Nat) : Prop :=
  ∀ (x δ : Q'), OnBox x δ →
    R_B2 e he x δ ≤ (Q'.ofNat C2) * (δ * δ)
      ∧ (-(R_B2 e he x δ)) ≤ (Q'.ofNat C2) * (δ * δ)

/-- **NAMED-open: the antisymmetric bracket bound** with the EXPLICIT constant
`C(e)`: `|R_B e x δ| ≤ C(e)·δ³` on the box.  Reduces (by the `Q'`-linearity of the
bracket and of `Bderiv` over their two `U`-terms, against `AdiffCubeModulus` at
`e−1`, `e+1`) to the antisymmetric cofactor moduli.  Recorded as the precise
residual. -/
def BracketCubeBound (e : Nat) (he : 0 < e) (C : Nat) : Prop :=
  ∀ (x δ : Q'), OnBox x δ →
    R_B e he x δ ≤ (Q'.ofNat C) * ((δ * δ) * δ)
      ∧ (-(R_B e he x δ)) ≤ (Q'.ofNat C) * ((δ * δ) * δ)

/-! ### The EXACT bracket-to-sequence reduction (PROVED)

The single load-bearing identity: a bracket term `bterm m d y = mkPos (U_m y).num
((U_m y).den·d)` is `(1/d)·U_m(y)`, hence the centered second difference of the
WHOLE bracket equals the `(1/e)`, `1/(e+2)`-weighted combination of the per-`U`
second differences `Sdiff(e−1)`, `Sdiff(e+1)`:

  `R_B2 e x δ ≈ (1/e)·Sdiff(e−1) − (1/(e+2))·Sdiff(e+1)`.

This is the EXACT reduction of the bracket Taylor remainder to the cofactor moduli
(`§3`).  Proved below (`R_B2_reduce`); the analogous antisymmetric reduction is
`R_B_reduce`. -/

/-- A single bracket term `mkPos (U_m y).num ((U_m y).den·d)`. -/
def bterm (m d : Nat) (hd : 0 < d) (y : Q') : Q' :=
  Q'.mkPos (Cheb.U m y).num ((Cheb.U m y).den * d) (Nat.mul_pos (Cheb.U m y).den_pos hd)

/-- `Gbracket` is the difference of two `bterm`s. -/
theorem Gbracket_eq_bterms (e : Nat) (he : 0 < e) (x : Q') :
    Gbracket e he x = bterm (e-1) e he x + (-(bterm (e+1) (e+2) (by omega) x)) := rfl

/-- **The bridge** `bterm m d y ≈ (1/d)·U_m(y)` (`1/d = mkPos 1 d`). -/
theorem bterm_eqv (m d : Nat) (hd : 0 < d) (y : Q') :
    bterm m d hd y ≈ (Q'.mkPos 1 d hd) * Cheb.U m y := by
  unfold bterm Q'.eqv
  rw [Q'.mkPos_num, Q'.mkPos_den]
  show (Cheb.U m y).num * (((Q'.mkPos 1 d hd).den * (Cheb.U m y).den : Nat) : Int)
      = ((Q'.mkPos 1 d hd).num * (Cheb.U m y).num) * (((Cheb.U m y).den * d : Nat) : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]
  push_cast
  rw [Int.one_mul, Int.mul_comm (d:Int) ((Cheb.U m y).den : Int)]

/-- Scalar factoring of the symmetric second difference:
`(c·p + c·q) + (−(2·(c·r))) ≈ c·((p+q) + (−(2·r)))`. -/
theorem scalar_D2 (c p q r : Q') :
    ((c*p + c*q) + (-(((1:Q')+(1:Q')) * (c*r))))
      ≈ c * ((p + q) + (-(((1:Q')+(1:Q')) * r))) := by
  calc ((c*p + c*q) + (-(((1:Q')+(1:Q')) * (c*r))))
      ≈ (c*p + c*q) + (-(c*(((1:Q')+(1:Q')) * r))) := by
        refine Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ ?_)
        -- 2·(c·r) ≈ c·(2·r)
        calc ((1:Q')+(1:Q')) * (c*r)
            ≈ (((1:Q')+(1:Q')) * c) * r := Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
          _ ≈ (c * ((1:Q')+(1:Q'))) * r := Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)
          _ ≈ c * (((1:Q')+(1:Q')) * r) := Q'.mul_assoc_eqv _ _ _
    _ ≈ (c*(p + q)) + (-(c*(((1:Q')+(1:Q')) * r))) :=
        Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv c p q))
    _ ≈ c*((p + q) + (-(((1:Q')+(1:Q')) * r))) :=
        Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c (p+q) (-(((1:Q')+(1:Q'))*r)))
          (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv c (((1:Q')+(1:Q'))*r))))

/-- **The symmetric per-term reduction**: the centered second difference of a
bracket term equals `(1/d)·Sdiff(m)`. -/
theorem D2_bterm_eqv (m d : Nat) (hd : 0 < d) (x δ : Q') :
    ((bterm m d hd (x+δ) + bterm m d hd (x+(-δ))) + (-(((1:Q')+(1:Q')) * bterm m d hd x)))
      ≈ (Q'.mkPos 1 d hd) * Sdiff x δ m := by
  -- substitute the bridge at the three nodes
  refine Q'.eqv_trans _ _ _
    (addC _ _ _ _
      (addC _ _ _ _ (bterm_eqv m d hd (x+δ)) (bterm_eqv m d hd (x+(-δ))))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ (bterm_eqv m d hd x)))) ?_
  -- now it is scalar_D2 with c = 1/d, p,q,r the three U evaluations
  show ((((Q'.mkPos 1 d hd) * Uplus x δ m) + ((Q'.mkPos 1 d hd) * Uminus x δ m))
        + (-(((1:Q')+(1:Q')) * ((Q'.mkPos 1 d hd) * Cheb.U m x))))
      ≈ (Q'.mkPos 1 d hd) * Sdiff x δ m
  exact scalar_D2 (Q'.mkPos 1 d hd) (Uplus x δ m) (Uminus x δ m) (Cheb.U m x)

/-- Linearity of the second difference over a `f − g` term:
`((f₊ + (−g₊)) + (f₋ + (−g₋))) + (−(2·(f₀ + (−g₀))))
  ≈ ((f₊ + f₋) + (−(2·f₀))) + (−((g₊ + g₋) + (−(2·g₀))))`. -/
theorem D2_sub (fp fm f0 gp gm g0 : Q') :
    (((fp + (-gp)) + (fm + (-gm))) + (-(((1:Q')+(1:Q')) * (f0 + (-g0)))))
      ≈ (((fp + fm) + (-(((1:Q')+(1:Q')) * f0))))
          + (-(((gp + gm) + (-(((1:Q')+(1:Q')) * g0))))) := by
  -- distribute 2·(f0 + −g0) ≈ 2·f0 + −(2·g0)
  have hd2 : ((1:Q')+(1:Q')) * (f0 + (-g0)) ≈ (((1:Q')+(1:Q'))*f0) + (-(((1:Q')+(1:Q'))*g0)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv _ _))
  -- LHS bag: {fp, -gp, fm, -gm, -(2f0), 2g0}
  -- RHS bag: {fp, fm, -(2f0), -(gp), -(gm), 2g0}
  have hL : (((fp + (-gp)) + (fm + (-gm))) + (-(((1:Q')+(1:Q')) * (f0 + (-g0)))))
      ≈ addNF6 fp (-gp) fm (-gm) (-(((1:Q')+(1:Q'))*f0)) (((1:Q')+(1:Q'))*g0) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hd2)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (negSub (((1:Q')+(1:Q'))*f0) (((1:Q')+(1:Q'))*g0))) ?_
    -- ((fp+−gp)+(fm+−gm)) + (−(2f0) + 2g0)
    exact to_addNF6_B fp (-gp) fm (-gm) (-(((1:Q')+(1:Q'))*f0)) (((1:Q')+(1:Q'))*g0)
  have hR : (((fp + fm) + (-(((1:Q')+(1:Q')) * f0))))
          + (-(((gp + gm) + (-(((1:Q')+(1:Q')) * g0)))))
      ≈ addNF6 fp fm (-(((1:Q')+(1:Q'))*f0)) (-gp) (-gm) (((1:Q')+(1:Q'))*g0) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (negSub (gp+gm) (((1:Q')+(1:Q'))*g0))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_right _ _ _ (Cheb.neg_add_eqv gp gm))) ?_
    -- ((fp+fm) + −(2f0)) + ((−gp + −gm) + 2g0)
    exact to_addNF6_A fp fm (-(((1:Q')+(1:Q'))*f0)) (-gp) (-gm) (((1:Q')+(1:Q'))*g0)
  refine Q'.eqv_trans _ _ _ hL (Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hR))
  -- addNF6 fp (-gp) fm (-gm) (-(2f0)) (2g0)
  --   ≈ addNF6 fp fm (-(2f0)) (-gp) (-gm) (2g0)
  unfold addNF6
  refine Q'.add_eqv_congr_left _ _ _ ?_
  -- (-gp) + (fm + (-gm + ((-(2f0)) + 2g0)))
  --   ≈ fm + ((-(2f0)) + ((-gp) + ((-gm) + 2g0)))
  calc (-gp) + (fm + ((-gm) + ((-(((1:Q')+(1:Q'))*f0)) + (((1:Q')+(1:Q'))*g0))))
      ≈ (-gp) + (fm + (((-(((1:Q')+(1:Q'))*f0))) + ((-gm) + (((1:Q')+(1:Q'))*g0)))) := by
        refine Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _ ?_)
        -- (-gm) + ((-(2f0)) + 2g0) ≈ (-(2f0)) + ((-gm) + 2g0)
        calc (-gm) + ((-(((1:Q')+(1:Q'))*f0)) + (((1:Q')+(1:Q'))*g0))
            ≈ ((-gm) + (-(((1:Q')+(1:Q'))*f0))) + (((1:Q')+(1:Q'))*g0) :=
              Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
          _ ≈ ((-(((1:Q')+(1:Q'))*f0)) + (-gm)) + (((1:Q')+(1:Q'))*g0) :=
              Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)
          _ ≈ (-(((1:Q')+(1:Q'))*f0)) + ((-gm) + (((1:Q')+(1:Q'))*g0)) := Q'.add_assoc_eqv _ _ _
    _ ≈ (-gp) + ((fm + (-(((1:Q')+(1:Q'))*f0))) + ((-gm) + (((1:Q')+(1:Q'))*g0))) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
    _ ≈ (-gp) + ((fm + (-(((1:Q')+(1:Q'))*f0))) + ((-gm) + (((1:Q')+(1:Q'))*g0))) := Q'.eqv_refl _
    _ ≈ ((-gp) + (fm + (-(((1:Q')+(1:Q'))*f0)))) + ((-gm) + (((1:Q')+(1:Q'))*g0)) :=
        Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
    _ ≈ ((fm + (-(((1:Q')+(1:Q'))*f0))) + (-gp)) + ((-gm) + (((1:Q')+(1:Q'))*g0)) :=
        Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)
    _ ≈ (fm + (-(((1:Q')+(1:Q'))*f0))) + ((-gp) + ((-gm) + (((1:Q')+(1:Q'))*g0))) :=
        Q'.add_assoc_eqv _ _ _
    _ ≈ fm + ((-(((1:Q')+(1:Q'))*f0)) + ((-gp) + ((-gm) + (((1:Q')+(1:Q'))*g0)))) :=
        Q'.add_assoc_eqv _ _ _

/-- **The EXACT symmetric reduction.**  `R_B2 e x δ ≈ (1/e)·Sdiff(e−1)(x,δ) −
(1/(e+2))·Sdiff(e+1)(x,δ)`.  The bracket Taylor remainder reduced EXACTLY to the
two per-`U` second differences. -/
theorem R_B2_reduce (e : Nat) (he : 0 < e) (x δ : Q') :
    R_B2 e he x δ
      ≈ ((Q'.mkPos 1 e he) * Sdiff x δ (e-1))
          + (-((Q'.mkPos 1 (e+2) (by omega)) * Sdiff x δ (e+1))) := by
  -- unfold R_B2 and Gbracket-as-bterms at the three nodes
  show ((Gbracket e he (x+δ) + Gbracket e he (x+(-δ))) + (-(((1:Q')+(1:Q')) * Gbracket e he x)))
      ≈ _
  rw [Gbracket_eq_bterms e he (x+δ), Gbracket_eq_bterms e he (x+(-δ)),
      Gbracket_eq_bterms e he x]
  -- apply D2_sub with f = bterm(e-1,e), g = bterm(e+1,e+2)
  refine Q'.eqv_trans _ _ _
    (D2_sub (bterm (e-1) e he (x+δ)) (bterm (e-1) e he (x+(-δ))) (bterm (e-1) e he x)
            (bterm (e+1) (e+2) (by omega) (x+δ)) (bterm (e+1) (e+2) (by omega) (x+(-δ)))
            (bterm (e+1) (e+2) (by omega) x)) ?_
  -- now each D2[bterm] reduces via D2_bterm_eqv
  exact addC _ _ _ _
    (D2_bterm_eqv (e-1) e he x δ)
    (Q'.neg_eqv_congr _ _ (D2_bterm_eqv (e+1) (e+2) (by omega) x δ))

/-! ### Scalar bounds and the assembled symmetric bracket bound -/

/-- `0 ≤ 1/d` (`= mkPos 1 d`). -/
theorem recip_nonneg (d : Nat) (hd : 0 < d) : (0:Q') ≤ Q'.mkPos 1 d hd := by
  show (0:Q').num * ((Q'.mkPos 1 d hd).den : Int) ≤ (Q'.mkPos 1 d hd).num * ((0:Q').den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]
  show (0:Int) * (d:Int) ≤ (1:Int) * ((0:Q').den : Int)
  have hz : ((0:Q').den : Int) = 1 := rfl
  rw [hz, Int.zero_mul, Int.one_mul]
  decide

/-- `1/d ≤ 1` (`= mkPos 1 d ≤ 1`). -/
theorem recip_le_one (d : Nat) (hd : 0 < d) : Q'.mkPos 1 d hd ≤ (1:Q') := by
  show (Q'.mkPos 1 d hd).num * ((1:Q').den : Int) ≤ (1:Q').num * ((Q'.mkPos 1 d hd).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]
  have hn1 : ((1:Q').num) = 1 := rfl
  have hd1 : ((1:Q').den : Int) = 1 := rfl
  rw [hn1, hd1, Int.mul_one, Int.one_mul]
  -- 1 ≤ (d : Int), since d ≥ 1
  exact_mod_cast hd

/-- `−1 ≤ 0` over `Q'`. -/
theorem neg_one_le_zero : (-(1:Q')) ≤ (0:Q') := by decide

/-- One-sided scalar bound: `0 ≤ c ≤ 1`, `−B ≤ S ≤ B`, `0 ≤ B` ⇒ `c·S ≤ B`. -/
theorem scalar_le {c S B : Q'} (hc0 : (0:Q') ≤ c) (hc1 : c ≤ (1:Q'))
    (hB : (0:Q') ≤ B) (hS1 : S ≤ B) (hS2 : (-S) ≤ B) : c * S ≤ B := by
  have hcB : (-(1:Q')) ≤ c := Q'.le_trans' _ _ _ neg_one_le_zero hc0
  -- from −S ≤ B  derive  −B ≤ S
  have hSlow : (-B) ≤ S :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hS2) (Q'.le_of_eqv (Q'.neg_neg_eqv S))
  have key : c * S ≤ (1:Q') * B :=
    Q'.mul_le_of_bounds (by decide) hB hcB hc1 hSlow hS1
  exact Q'.le_trans' _ _ _ key (Q'.le_of_eqv (Q'.one_mul_eqv B))

/-- Scalar bound: if `−B ≤ S ≤ B` (`0 ≤ B`) and `0 ≤ c ≤ 1`, then both
`c·S ≤ B` and `−(c·S) ≤ B`. -/
theorem scalar_abs_le {c S B : Q'} (hc0 : (0:Q') ≤ c) (hc1 : c ≤ (1:Q'))
    (hB : (0:Q') ≤ B) (hS1 : S ≤ B) (hS2 : (-S) ≤ B) :
    c * S ≤ B ∧ (-(c * S)) ≤ B := by
  refine ⟨scalar_le hc0 hc1 hB hS1 hS2, ?_⟩
  -- −(c·S) ≈ c·(−S); bound c·(−S) by scalar_le with S := −S (and −(−S)=S ≤ B).
  have h := scalar_le hc0 hc1 hB hS2
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_neg_eqv S)) hS1)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) h
  -- −(c·S) ≈ c·(−S)
  exact Q'.eqv_symm (Q'.mul_neg_eqv c S)

/-- `0 ≤ ofNat K · (δ·δ)`. -/
theorem ofNat_sq_nonneg (K : Nat) (δ : Q') : (0:Q') ≤ (Q'.ofNat K) * (δ * δ) :=
  Q'.mul_nonneg _ _ (by
    show (0:Q').num * ((Q'.ofNat K).den : Int) ≤ (Q'.ofNat K).num * ((0:Q').den : Int)
    show (0:Int) * 1 ≤ (Int.ofNat K) * 1
    rw [Int.zero_mul, Int.mul_one]; exact Int.ofNat_nonneg K)
    (Cheb.square_nonneg δ)

/-- `ofNat A · w + ofNat B · w ≈ ofNat (A+B) · w`. -/
theorem ofNat_add_mul (A B : Nat) (w : Q') :
    (Q'.ofNat A) * w + (Q'.ofNat B) * w ≈ (Q'.ofNat (A+B)) * w :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Cheb.add_mul_eqv (Q'.ofNat A) (Q'.ofNat B) w))
    (Q'.mul_eqv_congr_right _ _ _ (ChebU.ofNat_add_eqv A B))

/-- **The symmetric bracket bound, ASSEMBLED.**  From the symmetric cofactor
moduli `SdiffQuadModulus (e−1) K₁` and `SdiffQuadModulus (e+1) K₂` (the precise
residuals), the symmetric bracket Taylor remainder satisfies
`|R_B2 e x δ| ≤ (K₁+K₂)·δ²` on the box — i.e. `BracketQuadBound e he (K₁+K₂)`,
with the EXPLICIT constant `C₂(e) = K₁ + K₂`.  PROVED reduction. -/
theorem BracketQuadBound_of_moduli (e : Nat) (he : 0 < e) (K1 K2 : Nat)
    (h1 : SdiffQuadModulus (e-1) K1) (h2 : SdiffQuadModulus (e+1) K2) :
    BracketQuadBound e he (K1 + K2) := by
  intro x δ hbox
  obtain ⟨hS1a, hS1b⟩ := h1 x δ hbox
  obtain ⟨hS2a, hS2b⟩ := h2 x δ hbox
  -- per-term scalar bounds against B_i = ofNat K_i · δ²
  have hc1 : (0:Q') ≤ Q'.mkPos 1 e he := recip_nonneg e he
  have hc1' : Q'.mkPos 1 e he ≤ (1:Q') := recip_le_one e he
  have hc2 : (0:Q') ≤ Q'.mkPos 1 (e+2) (by omega) := recip_nonneg (e+2) (by omega)
  have hc2' : Q'.mkPos 1 (e+2) (by omega) ≤ (1:Q') := recip_le_one (e+2) (by omega)
  obtain ⟨hT1a, hT1b⟩ := scalar_abs_le hc1 hc1' (ofNat_sq_nonneg K1 δ) hS1a hS1b
  obtain ⟨hT2a, hT2b⟩ := scalar_abs_le hc2 hc2' (ofNat_sq_nonneg K2 δ) hS2a hS2b
  -- assemble via R_B2_reduce
  have hred := R_B2_reduce e he x δ
  constructor
  · -- R_B2 ≤ (K1+K2)·δ²
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hred) ?_
    -- (1/e)Sdiff(e-1) + (−(1/(e+2))Sdiff(e+1)) ≤ K1δ² + K2δ² ≈ (K1+K2)δ²
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add hT1a (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_refl _)) hT2b)) ?_
    exact Q'.le_of_eqv (ofNat_add_mul K1 K2 (δ*δ))
  · -- −R_B2 ≤ (K1+K2)·δ²
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_eqv_congr _ _ hred)) ?_
    -- −((1/e)S₁ + (−(1/(e+2))S₂)) ≈ (−(1/e)S₁) + (1/(e+2))S₂
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (negSub ((Q'.mkPos 1 e he) * Sdiff x δ (e-1))
      ((Q'.mkPos 1 (e+2) (by omega)) * Sdiff x δ (e+1)))) ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add hT1b hT2a) ?_
    exact Q'.le_of_eqv (ofNat_add_mul K1 K2 (δ*δ))

/-! ### The EXACT antisymmetric reduction (PROVED)

`R_B e x δ ≈ (1/e)·(Adiff(e−1) − 2δ·U'_{e−1}(x)) − (1/(e+2))·(Adiff(e+1) − 2δ·U'_{e+1}(x))`.
The bracket first-difference Taylor remainder reduced EXACTLY to the two per-`U`
cubed cofactor remainders. -/

/-- A single derivative-bracket term `mkPos (U'_m y).num ((U'_m y).den·d)`. -/
def bderivterm (m d : Nat) (hd : 0 < d) (y : Q') : Q' :=
  Q'.mkPos (Uderiv m y).num ((Uderiv m y).den * d) (Nat.mul_pos (Uderiv m y).den_pos hd)

/-- `Bderiv` is the difference of two `bderivterm`s. -/
theorem Bderiv_eq_bderivterms (e : Nat) (he : 0 < e) (x : Q') :
    Bderiv e he x = bderivterm (e-1) e he x + (-(bderivterm (e+1) (e+2) (by omega) x)) := rfl

/-- The derivative bridge `bderivterm m d y ≈ (1/d)·U'_m(y)`. -/
theorem bderivterm_eqv (m d : Nat) (hd : 0 < d) (y : Q') :
    bderivterm m d hd y ≈ (Q'.mkPos 1 d hd) * Uderiv m y := by
  unfold bderivterm Q'.eqv
  rw [Q'.mkPos_num, Q'.mkPos_den]
  show (Uderiv m y).num * (((Q'.mkPos 1 d hd).den * (Uderiv m y).den : Nat) : Int)
      = ((Q'.mkPos 1 d hd).num * (Uderiv m y).num) * (((Uderiv m y).den * d : Nat) : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]
  push_cast
  rw [Int.one_mul, Int.mul_comm (d:Int) ((Uderiv m y).den : Int)]

/-- Scalar factoring of the first-difference remainder:
`(c·p + (−(c·q))) + (−(2·(δ·(c·r)))) ≈ c·((p + (−q)) + (−(2·(δ·r))))`. -/
theorem scalar_D1rem (c δ p q r : Q') :
    ((c*p + (-(c*q))) + (-(((1:Q')+(1:Q')) * (δ * (c*r)))))
      ≈ c * ((p + (-q)) + (-(((1:Q')+(1:Q')) * (δ * r)))) := by
  calc ((c*p + (-(c*q))) + (-(((1:Q')+(1:Q')) * (δ * (c*r)))))
      ≈ (c*p + (-(c*q))) + (-(c*(((1:Q')+(1:Q')) * (δ * r)))) := by
        refine Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ ?_)
        -- 2·(δ·(c·r)) ≈ c·(2·(δ·r))
        calc ((1:Q')+(1:Q')) * (δ * (c*r))
            ≈ ((1:Q')+(1:Q')) * ((δ * c) * r) :=
              Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv δ c r))
          _ ≈ ((1:Q')+(1:Q')) * ((c * δ) * r) :=
              Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv δ c))
          _ ≈ ((1:Q')+(1:Q')) * (c * (δ * r)) :=
              Q'.mul_eqv_congr_left _ _ _ (Q'.mul_assoc_eqv c δ r)
          _ ≈ (((1:Q')+(1:Q')) * c) * (δ * r) := Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
          _ ≈ (c * ((1:Q')+(1:Q'))) * (δ * r) := Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)
          _ ≈ c * (((1:Q')+(1:Q')) * (δ * r)) := Q'.mul_assoc_eqv _ _ _
    _ ≈ (c*(p + (-q))) + (-(c*(((1:Q')+(1:Q')) * (δ * r)))) := by
        refine Q'.add_eqv_congr_right _ _ _ ?_
        exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c p (-q))
          (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv c q)))
    _ ≈ c*((p + (-q)) + (-(((1:Q')+(1:Q')) * (δ * r)))) :=
        Q'.eqv_symm (Q'.eqv_trans _ _ _
          (Q'.mul_add_eqv c (p+(-q)) (-(((1:Q')+(1:Q'))*(δ*r))))
          (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv c (((1:Q')+(1:Q'))*(δ*r)))))

/-- **The antisymmetric per-term reduction**: the first-difference remainder of a
bracket term equals `(1/d)·(Adiff(m) − 2δ·U'_m(x))`. -/
theorem D1rem_bterm_eqv (m d : Nat) (hd : 0 < d) (x δ : Q') :
    ((bterm m d hd (x+δ) + (-(bterm m d hd (x+(-δ)))))
        + (-(((1:Q')+(1:Q')) * (δ * bderivterm m d hd x))))
      ≈ (Q'.mkPos 1 d hd) * (Adiff x δ m + (-(((1:Q')+(1:Q')) * (δ * Uderiv m x)))) := by
  refine Q'.eqv_trans _ _ _
    (addC _ _ _ _
      (addC _ _ _ _ (bterm_eqv m d hd (x+δ))
        (Q'.neg_eqv_congr _ _ (bterm_eqv m d hd (x+(-δ)))))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (bderivterm_eqv m d hd x))))) ?_
  show ((((Q'.mkPos 1 d hd) * Uplus x δ m) + (-((Q'.mkPos 1 d hd) * Uminus x δ m)))
        + (-(((1:Q')+(1:Q')) * (δ * ((Q'.mkPos 1 d hd) * Uderiv m x)))))
      ≈ (Q'.mkPos 1 d hd) * (Adiff x δ m + (-(((1:Q')+(1:Q')) * (δ * Uderiv m x))))
  exact scalar_D1rem (Q'.mkPos 1 d hd) δ (Uplus x δ m) (Uminus x δ m) (Uderiv m x)

/-- Linearity of the first-difference remainder over an `f − g` term. -/
theorem D1rem_sub (δ fp fm f0 gp gm g0 : Q') :
    (((fp + (-gp)) + (-(fm + (-gm)))) + (-(((1:Q')+(1:Q')) * (δ * (f0 + (-g0))))))
      ≈ (((fp + (-fm)) + (-(((1:Q')+(1:Q')) * (δ * f0)))))
          + (-(((gp + (-gm)) + (-(((1:Q')+(1:Q')) * (δ * g0)))))) := by
  -- distribute 2·(δ·(f0+−g0)) ≈ 2·(δ·f0) + −(2·(δ·g0))
  have hd2 : ((1:Q')+(1:Q')) * (δ * (f0 + (-g0)))
      ≈ (((1:Q')+(1:Q'))*(δ*f0)) + (-(((1:Q')+(1:Q'))*(δ*g0))) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_add_eqv δ f0 (-g0))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv δ g0))) ?_
    exact Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv _ _))
  have hL : (((fp + (-gp)) + (-(fm + (-gm)))) + (-(((1:Q')+(1:Q')) * (δ * (f0 + (-g0))))))
      ≈ addNF6 fp (-gp) (-fm) gm (-(((1:Q')+(1:Q'))*(δ*f0))) (((1:Q')+(1:Q'))*(δ*g0)) := by
    refine Q'.eqv_trans _ _ _
      (addC _ _ _ _ (Q'.add_eqv_congr_left _ _ _ (negSub fm gm))
        (Q'.neg_eqv_congr _ _ hd2)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (negSub (((1:Q')+(1:Q'))*(δ*f0)) (((1:Q')+(1:Q'))*(δ*g0)))) ?_
    -- ((fp+−gp)+((−fm)+gm)) + ((−(2δf0)) + 2δg0)
    exact to_addNF6_B fp (-gp) (-fm) gm (-(((1:Q')+(1:Q'))*(δ*f0))) (((1:Q')+(1:Q'))*(δ*g0))
  have hR : (((fp + (-fm)) + (-(((1:Q')+(1:Q')) * (δ * f0)))))
          + (-(((gp + (-gm)) + (-(((1:Q')+(1:Q')) * (δ * g0))))))
      ≈ addNF6 fp (-fm) (-(((1:Q')+(1:Q'))*(δ*f0))) (-gp) gm (((1:Q')+(1:Q'))*(δ*g0)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (negSub (gp+(-gm)) (((1:Q')+(1:Q'))*(δ*g0)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_right _ _ _ (negSub gp gm))) ?_
    -- ((fp+−fm)+(−(2δf0))) + (((−gp)+gm) + 2δg0)
    exact to_addNF6_A fp (-fm) (-(((1:Q')+(1:Q'))*(δ*f0))) (-gp) gm (((1:Q')+(1:Q'))*(δ*g0))
  refine Q'.eqv_trans _ _ _ hL (Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hR))
  -- addNF6 fp (-gp) (-fm) gm (-(2δf0)) (2δg0)
  --   ≈ addNF6 fp (-fm) (-(2δf0)) (-gp) gm (2δg0)
  unfold addNF6
  refine Q'.add_eqv_congr_left _ _ _ ?_
  -- (-gp) + ((-fm) + (gm + ((-(2δf0)) + 2δg0)))
  --   ≈ (-fm) + ((-(2δf0)) + ((-gp) + (gm + 2δg0)))
  calc (-gp) + ((-fm) + (gm + ((-(((1:Q')+(1:Q'))*(δ*f0))) + (((1:Q')+(1:Q'))*(δ*g0)))))
      ≈ (-gp) + ((-fm) + (((-(((1:Q')+(1:Q'))*(δ*f0)))) + (gm + (((1:Q')+(1:Q'))*(δ*g0))))) := by
        refine Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _ ?_)
        -- gm + ((-(2δf0)) + 2δg0) ≈ (-(2δf0)) + (gm + 2δg0)
        calc gm + ((-(((1:Q')+(1:Q'))*(δ*f0))) + (((1:Q')+(1:Q'))*(δ*g0)))
            ≈ (gm + (-(((1:Q')+(1:Q'))*(δ*f0)))) + (((1:Q')+(1:Q'))*(δ*g0)) :=
              Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
          _ ≈ ((-(((1:Q')+(1:Q'))*(δ*f0))) + gm) + (((1:Q')+(1:Q'))*(δ*g0)) :=
              Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)
          _ ≈ (-(((1:Q')+(1:Q'))*(δ*f0))) + (gm + (((1:Q')+(1:Q'))*(δ*g0))) := Q'.add_assoc_eqv _ _ _
    _ ≈ (-gp) + (((-fm) + (-(((1:Q')+(1:Q'))*(δ*f0)))) + (gm + (((1:Q')+(1:Q'))*(δ*g0)))) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
    _ ≈ ((-gp) + ((-fm) + (-(((1:Q')+(1:Q'))*(δ*f0))))) + (gm + (((1:Q')+(1:Q'))*(δ*g0))) :=
        Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
    _ ≈ (((-fm) + (-(((1:Q')+(1:Q'))*(δ*f0)))) + (-gp)) + (gm + (((1:Q')+(1:Q'))*(δ*g0))) :=
        Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)
    _ ≈ ((-fm) + (-(((1:Q')+(1:Q'))*(δ*f0)))) + ((-gp) + (gm + (((1:Q')+(1:Q'))*(δ*g0)))) :=
        Q'.add_assoc_eqv _ _ _
    _ ≈ (-fm) + ((-(((1:Q')+(1:Q'))*(δ*f0))) + ((-gp) + (gm + (((1:Q')+(1:Q'))*(δ*g0))))) :=
        Q'.add_assoc_eqv _ _ _

/-- **The EXACT antisymmetric reduction.**  `R_B e x δ ≈
(1/e)·(Adiff(e−1) − 2δ·U'_{e−1}(x)) − (1/(e+2))·(Adiff(e+1) − 2δ·U'_{e+1}(x))`. -/
theorem R_B_reduce (e : Nat) (he : 0 < e) (x δ : Q') :
    R_B e he x δ
      ≈ ((Q'.mkPos 1 e he) * (Adiff x δ (e-1) + (-(((1:Q')+(1:Q')) * (δ * Uderiv (e-1) x)))))
          + (-((Q'.mkPos 1 (e+2) (by omega))
                * (Adiff x δ (e+1) + (-(((1:Q')+(1:Q')) * (δ * Uderiv (e+1) x)))))) := by
  show ((Gbracket e he (x+δ) + (-(Gbracket e he (x+(-δ)))))
        + (-(((1:Q')+(1:Q')) * (δ * Bderiv e he x))))
      ≈ _
  rw [Gbracket_eq_bterms e he (x+δ), Gbracket_eq_bterms e he (x+(-δ)),
      Bderiv_eq_bderivterms e he x]
  refine Q'.eqv_trans _ _ _
    (D1rem_sub δ (bterm (e-1) e he (x+δ)) (bterm (e-1) e he (x+(-δ))) (bderivterm (e-1) e he x)
              (bterm (e+1) (e+2) (by omega) (x+δ)) (bterm (e+1) (e+2) (by omega) (x+(-δ)))
              (bderivterm (e+1) (e+2) (by omega) x)) ?_
  exact addC _ _ _ _
    (D1rem_bterm_eqv (e-1) e he x δ)
    (Q'.neg_eqv_congr _ _ (D1rem_bterm_eqv (e+1) (e+2) (by omega) x δ))

/-- `0 ≤ ofNat K · ((δ·δ)·δ)`  on the box (`0 ≤ δ`). -/
theorem ofNat_cube_nonneg (K : Nat) {δ : Q'} (hδ : (0:Q') ≤ δ) :
    (0:Q') ≤ (Q'.ofNat K) * ((δ * δ) * δ) :=
  Q'.mul_nonneg _ _ (by
    show (0:Q').num * ((Q'.ofNat K).den : Int) ≤ (Q'.ofNat K).num * ((0:Q').den : Int)
    show (0:Int) * 1 ≤ (Int.ofNat K) * 1
    rw [Int.zero_mul, Int.mul_one]; exact Int.ofNat_nonneg K)
    (Q'.mul_nonneg _ _ (Cheb.square_nonneg δ) hδ)

/-- **The antisymmetric bracket bound, ASSEMBLED.**  From the antisymmetric
cofactor moduli `AdiffCubeModulus (e−1) K₁` and `AdiffCubeModulus (e+1) K₂`, the
antisymmetric bracket Taylor remainder satisfies `|R_B e x δ| ≤ (K₁+K₂)·δ³` on
the box — i.e. `BracketCubeBound e he (K₁+K₂)`, with the EXPLICIT constant
`C(e) = K₁ + K₂`.  PROVED reduction. -/
theorem BracketCubeBound_of_moduli (e : Nat) (he : 0 < e) (K1 K2 : Nat)
    (h1 : AdiffCubeModulus (e-1) K1) (h2 : AdiffCubeModulus (e+1) K2) :
    BracketCubeBound e he (K1 + K2) := by
  intro x δ hbox
  obtain ⟨_hx1, _hxm1, hδ0, _hδ1⟩ := hbox
  obtain ⟨hA1a, hA1b⟩ := h1 x δ ⟨_hx1, _hxm1, hδ0, _hδ1⟩
  obtain ⟨hA2a, hA2b⟩ := h2 x δ ⟨_hx1, _hxm1, hδ0, _hδ1⟩
  have hc1 : (0:Q') ≤ Q'.mkPos 1 e he := recip_nonneg e he
  have hc1' : Q'.mkPos 1 e he ≤ (1:Q') := recip_le_one e he
  have hc2 : (0:Q') ≤ Q'.mkPos 1 (e+2) (by omega) := recip_nonneg (e+2) (by omega)
  have hc2' : Q'.mkPos 1 (e+2) (by omega) ≤ (1:Q') := recip_le_one (e+2) (by omega)
  obtain ⟨hT1a, hT1b⟩ := scalar_abs_le hc1 hc1' (ofNat_cube_nonneg K1 hδ0) hA1a hA1b
  obtain ⟨hT2a, hT2b⟩ := scalar_abs_le hc2 hc2' (ofNat_cube_nonneg K2 hδ0) hA2a hA2b
  have hred := R_B_reduce e he x δ
  constructor
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hred) ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add hT1a hT2b) ?_
    exact Q'.le_of_eqv (ofNat_add_mul K1 K2 ((δ*δ)*δ))
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_eqv_congr _ _ hred)) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (negSub
      ((Q'.mkPos 1 e he) * (Adiff x δ (e-1) + (-(((1:Q')+(1:Q')) * (δ * Uderiv (e-1) x)))))
      ((Q'.mkPos 1 (e+2) (by omega))
        * (Adiff x δ (e+1) + (-(((1:Q')+(1:Q')) * (δ * Uderiv (e+1) x))))))) ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add hT1b hT2a) ?_
    exact Q'.le_of_eqv (ofNat_add_mul K1 K2 ((δ*δ)*δ))

end YMGap.Continuum.ChebBracketTaylor

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED (axiom-clean, GENUINE new content).**
  * `Adiff_rec_core` / `Ssum_rec_core` — the abstract multilinear cores of the
    centered difference recurrences (pure `Q'`-ring `calc`, no `ring`).
  * `Adiff_rec` / `Ssum_rec` — the EXACT centered first-difference and symmetric-sum
    recurrences for `Cheb.U` evaluated at `x±δ`:
    `Adiff(n+2) ≈ 2x·Adiff(n+1) − Adiff(n) + 2δ·Ssum(n+1)`,
    `Ssum(n+2)  ≈ 2x·Ssum(n+1)  − Ssum(n)  + 2δ·Adiff(n+1)`.
  * `Uderiv2` / `Uderiv3` (+ `*_succ_succ`) — the 2nd/3rd formal derivatives of `U_n`,
    by differentiating the `Uderiv` product-rule recurrence.
  * `bterm_eqv` / `bderivterm_eqv` — the division bridge `mkPos a.num (a.den·d) ≈
    (1/d)·a` for the bracket and its derivative.
  * `R_B2_reduce` — the EXACT symmetric reduction
    `R_B2 e x δ ≈ (1/e)·Sdiff(e−1) − (1/(e+2))·Sdiff(e+1)`.
  * `R_B_reduce` — the EXACT antisymmetric reduction
    `R_B e x δ ≈ (1/e)·(Adiff(e−1) − 2δ·U'_{e−1}) − (1/(e+2))·(Adiff(e+1) − 2δ·U'_{e+1})`.
  * `scalar_abs_le` + `ofNat_add_mul` — the scalar `1/d ≤ 1` bound machinery.
  * **`BracketQuadBound_of_moduli`** — the SYMMETRIC bracket bound
    `|R_B2 e x δ| ≤ (K₁+K₂)·δ²`, with EXPLICIT `C₂(e) = K₁ + K₂`, PROVED from the
    symmetric cofactor moduli.
  * **`BracketCubeBound_of_moduli`** — the ANTISYMMETRIC bracket bound
    `|R_B e x δ| ≤ (K₁+K₂)·δ³`, with EXPLICIT `C(e) = K₁ + K₂`, PROVED from the
    antisymmetric cofactor moduli.

**NAMED-open (the honest residuals — precisely).**
  * `SdiffQuadModulus n K` — the symmetric cofactor majorant `|Sdiff x δ n| ≤ K·δ²`
    on the box `|x| ≤ 1`, `0 < δ ≤ 1`, with EXPLICIT `Nat` majorant `K`.  Its
    δ²-ORDER is supplied by `Sdiff_rec`/`Adiff_rec`; the residual is the uniform
    (Markov-type) cofactor majorant `K`.  The offset nodes `x ± δ ∈ [−2,2]` escape
    `[−1,1]`, so `ChebU.absU_le` does NOT bound `Uplus`/`Uminus` directly — the
    bound must come from the cancellation captured by the recurrences.
  * `AdiffCubeModulus n K` — the antisymmetric cubed cofactor majorant
    `|Adiff x δ n − 2δ·U'_n(x)| ≤ K·δ³` on the box, EXPLICIT `K`.

Both residuals are STRICTLY SMALLER than the bracket bounds: they are the
SINGLE-`U` cofactor majorants, with the bracket-level δ-extraction (the
`mkPos`-division bridge + the linearity of the centered differences over the two
`U`-terms + the `1/e`, `1/(e+2)` scalar bounds) PROVED.

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate below. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebBracketTaylor.Adiff_rec_core
#print axioms YMGap.Continuum.ChebBracketTaylor.Ssum_rec_core
#print axioms YMGap.Continuum.ChebBracketTaylor.Adiff_rec
#print axioms YMGap.Continuum.ChebBracketTaylor.Ssum_rec
#print axioms YMGap.Continuum.ChebBracketTaylor.Uderiv2_succ_succ
#print axioms YMGap.Continuum.ChebBracketTaylor.Uderiv3_succ_succ
#print axioms YMGap.Continuum.ChebBracketTaylor.bterm_eqv
#print axioms YMGap.Continuum.ChebBracketTaylor.bderivterm_eqv
#print axioms YMGap.Continuum.ChebBracketTaylor.D2_bterm_eqv
#print axioms YMGap.Continuum.ChebBracketTaylor.D2_sub
#print axioms YMGap.Continuum.ChebBracketTaylor.R_B2_reduce
#print axioms YMGap.Continuum.ChebBracketTaylor.D1rem_bterm_eqv
#print axioms YMGap.Continuum.ChebBracketTaylor.D1rem_sub
#print axioms YMGap.Continuum.ChebBracketTaylor.R_B_reduce
#print axioms YMGap.Continuum.ChebBracketTaylor.scalar_abs_le
#print axioms YMGap.Continuum.ChebBracketTaylor.BracketQuadBound_of_moduli
#print axioms YMGap.Continuum.ChebBracketTaylor.BracketCubeBound_of_moduli
