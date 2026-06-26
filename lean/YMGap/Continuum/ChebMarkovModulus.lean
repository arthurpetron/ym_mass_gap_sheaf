/-
# The two Markov-modulus obligations for the Chebyshev bracket Taylor bounds
# (`SdiffQuadModulus` and `AdiffCubeModulus`, unconditionally, for every `n`)

`ChebBracketTaylor.lean` reduces the polynomial bracket centered-difference
Taylor remainders to two NAMED cofactor moduli, each with an EXPLICIT `Nat`
majorant:

  * `SdiffQuadModulus n K`  :  `|Sdiff x δ n| ≤ K·δ²`  on the box,
  * `AdiffCubeModulus n K`  :  `|Adiff x δ n − 2δ·U'_n(x)| ≤ K·δ³`  on the box,

where `Sdiff x δ n = U_n(x+δ)+U_n(x−δ)−2U_n(x)`,
`Adiff x δ n = U_n(x+δ)−U_n(x−δ)`, on the box `|x| ≤ 1`, `0 ≤ δ ≤ 1`.

This module PROVES both, for every `n`, with explicit `Nat` majorants `KS n`,
`KA n`, by a SIMULTANEOUS two-step strong induction over FOUR coupled `Nat`
majorant sequences `S, A, KS, KA`.

## The four majorant sequences (`§1`)

Bundled as `M : Nat → Nat⁴` with the two-step recurrence

  * bases   `S 0=2, S 1=4`;  `A 0=0, A 1=4`;  `KS 0=0, KS 1=0`;  `KA 0=0, KA 1=0`;
  * steps   `S(n+2)  = 2·S(n+1)  + 2·A(n+1)  + S(n)`,
            `A(n+2)  = 2·A(n+1)  + 2·S(n+1)  + A(n)`,
            `KS(n+2) = 2·KS(n+1) + 2·A(n+1)  + KS(n)`,
            `KA(n+2) = 2·KA(n+1) + 2·KS(n+1) + KA(n)`.

## The four simultaneous bounds (`§3`)

For fixed `x, δ` on the box, with `Ssum x δ n = U_n(x+δ)+U_n(x−δ)` and the
remainder `Arem x δ n := Adiff x δ n − 2δ·U'_n(x)`:

  1. `|Ssum x δ n|  ≤ ofNat(S n)`            (plain `O(1)`),
  2. `|Adiff x δ n| ≤ ofNat(A n)·δ`          (`O(δ)`),
  3. `|Sdiff x δ n| ≤ ofNat(KS n)·δ²`        (the `SdiffQuadModulus` content),
  4. `|Arem x δ n|  ≤ ofNat(KA n)·δ³`        (the `AdiffCubeModulus` content).

The δ-powers MATCH EXACTLY by construction; the inductive step uses the EXACT
centered-difference recurrences `Ssum_rec`, `Adiff_rec` (proved in
`ChebBracketTaylor`) plus the derived `Sdiff_rec`, `Arem_rec`, and the
`Q'` product/order bounds (`mul_le_of_bounds`, etc.).

## What is PROVED here (axiom-clean)

  * `sdiffQuadModulus_holds (n) : SdiffQuadModulus n (KS n)` — UNCONDITIONAL.
  * `adiffCubeModulus_holds (n) : AdiffCubeModulus n (KA n)` — UNCONDITIONAL.
  * `bracketQuadBound_holds`, `bracketCubeBound_holds` — the assembled bracket
    bounds, UNCONDITIONAL, composing the moduli with the proved
    `BracketQuadBound_of_moduli` / `BracketCubeBound_of_moduli`.

# Axiom gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` or `[propext, Quot.sound]`.
No `Classical.*`, no `sorry`/`sorryAx`, no `native_decide`.
-/

import YMGap.Continuum.ChebBracketTaylor

namespace YMGap.Continuum.ChebMarkovModulus

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum
open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebOrthoWeightedFTC
open YMGap.Continuum.ChebBracketTaylor

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

/-! ## 1. The four `Nat` majorant sequences -/

/-- The bundled four majorants `(S, A, KS, KA)` by a two-step `Nat` recurrence. -/
def M : Nat → Nat × Nat × Nat × Nat
  | 0     => (2, 0, 0, 0)
  | 1     => (4, 4, 0, 0)
  | (n+2) =>
      let p1 := M (n+1)
      let p0 := M n
      let S1 := p1.1;  let A1 := p1.2.1;  let KS1 := p1.2.2.1;  let KA1 := p1.2.2.2
      let S0 := p0.1;  let A0 := p0.2.1;  let KS0 := p0.2.2.1;  let KA0 := p0.2.2.2
      ( 2*S1  + 2*A1  + S0,
        2*A1  + 2*S1  + A0,
        2*KS1 + 2*A1  + KS0,
        2*KA1 + 2*KS1 + KA0 )

/-- The symmetric-sum majorant. -/
def Smaj (n : Nat) : Nat := (M n).1
/-- The first-difference (cofactor) majorant. -/
def Amaj (n : Nat) : Nat := (M n).2.1
/-- The symmetric second-difference (δ²) majorant. -/
def KS (n : Nat) : Nat := (M n).2.2.1
/-- The antisymmetric remainder (δ³) majorant. -/
def KA (n : Nat) : Nat := (M n).2.2.2

@[simp] theorem Smaj_zero : Smaj 0 = 2 := rfl
@[simp] theorem Smaj_one  : Smaj 1 = 4 := rfl
@[simp] theorem Amaj_zero : Amaj 0 = 0 := rfl
@[simp] theorem Amaj_one  : Amaj 1 = 4 := rfl
@[simp] theorem KS_zero : KS 0 = 0 := rfl
@[simp] theorem KS_one  : KS 1 = 0 := rfl
@[simp] theorem KA_zero : KA 0 = 0 := rfl
@[simp] theorem KA_one  : KA 1 = 0 := rfl

theorem Smaj_succ (n : Nat) :
    Smaj (n+2) = 2 * Smaj (n+1) + 2 * Amaj (n+1) + Smaj n := rfl
theorem Amaj_succ (n : Nat) :
    Amaj (n+2) = 2 * Amaj (n+1) + 2 * Smaj (n+1) + Amaj n := rfl
theorem KS_succ (n : Nat) :
    KS (n+2) = 2 * KS (n+1) + 2 * Amaj (n+1) + KS n := rfl
theorem KA_succ (n : Nat) :
    KA (n+2) = 2 * KA (n+1) + 2 * KS (n+1) + KA n := rfl

/-! ## 2. The two derived difference recurrences `Sdiff_rec`, `Arem_rec`

`Ssum_rec` and `Adiff_rec` are already proved in `ChebBracketTaylor`.  Here we
derive the centered-second-difference recurrence and the antisymmetric-remainder
recurrence, in the SAME shape
`V(n+2) ≈ 2x·V(n+1) + (−V(n)) + 2δ·W(n+1)`. -/

/-- `Sdiff x δ n = Ssum x δ n + (−(2·U_n(x)))` (definitional). -/
theorem Sdiff_eq (x δ : Q') (n : Nat) :
    Sdiff x δ n = Ssum x δ n + (-(((1:Q')+(1:Q')) * Cheb.U n x)) := rfl

/-- The antisymmetric remainder `Arem x δ n = Adiff x δ n − 2δ·U'_n(x)`. -/
def Arem (x δ : Q') (n : Nat) : Q' :=
  Adiff x δ n + (-(((1:Q')+(1:Q')) * (δ * Uderiv n x)))

/-- `2·U_{n+2}(x) ≈ 2x·(2·U_{n+1}(x)) + (−(2·U_n(x)))` — the `U`-recurrence at the
centre, scaled by `2`. -/
theorem twoU_rec (x : Q') (n : Nat) :
    ((1:Q')+(1:Q')) * Cheb.U (n+2) x
      ≈ (((1:Q')+(1:Q'))*x) * (((1:Q')+(1:Q')) * Cheb.U (n+1) x)
          + (-(((1:Q')+(1:Q')) * Cheb.U n x)) := by
  rw [Cheb.U_succ_succ n x]
  -- 2·((2x)·U(n+1) + (-U(n))) ≈ (2x)·(2·U(n+1)) + (-(2·U(n)))
  calc ((1:Q')+(1:Q')) * (((2:Q')*x) * Cheb.U (n+1) x + (-(Cheb.U n x)))
      ≈ ((1:Q')+(1:Q')) * (((2:Q')*x) * Cheb.U (n+1) x) + ((1:Q')+(1:Q')) * (-(Cheb.U n x)) :=
        Q'.mul_add_eqv _ _ _
    _ ≈ (((1:Q')+(1:Q'))*x) * (((1:Q')+(1:Q')) * Cheb.U (n+1) x)
          + ((1:Q')+(1:Q')) * (-(Cheb.U n x)) := by
        refine Q'.add_eqv_congr_right _ _ _ ?_
        -- 2·((2x)·c1) ≈ (2x)·(2·c1)   (2x = (1+1)*x defeq)
        calc ((1:Q')+(1:Q')) * ((((1:Q')+(1:Q'))*x) * Cheb.U (n+1) x)
            ≈ (((1:Q')+(1:Q')) * (((1:Q')+(1:Q'))*x)) * Cheb.U (n+1) x :=
              Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
          _ ≈ ((((1:Q')+(1:Q'))*x) * ((1:Q')+(1:Q'))) * Cheb.U (n+1) x :=
              Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)
          _ ≈ (((1:Q')+(1:Q'))*x) * (((1:Q')+(1:Q')) * Cheb.U (n+1) x) :=
              Q'.mul_assoc_eqv _ _ _
    _ ≈ (((1:Q')+(1:Q'))*x) * (((1:Q')+(1:Q')) * Cheb.U (n+1) x)
          + (-(((1:Q')+(1:Q')) * Cheb.U n x)) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv _ _)

/-- Abstract core of the `Sdiff` / `Arem` recurrence (5 atoms `X·s1, −s0, D·a1,
−(X·P), Q0`).  `((X·s1 + (−s0)) + D·a1) + (−(X·P + (−Q0)))
  ≈ (X·(s1 + (−P)) + (−(s0 + (−Q0)))) + D·a1`. -/
theorem diffRec_core (X D s1 s0 a1 P Q0 : Q') :
    (((X*s1 + (-s0)) + D*a1) + (-((X*P) + (-Q0))))
      ≈ ((X * (s1 + (-P)) + (-(s0 + (-Q0)))) + D*a1) := by
  -- LHS normal form: X·s1 + (−s0 + (D·a1 + ((−(X·P)) + Q0)))
  have hL : (((X*s1 + (-s0)) + D*a1) + (-((X*P) + (-Q0))))
      ≈ X*s1 + ((-s0) + ((D*a1) + ((-(X*P)) + Q0))) := by
    calc (((X*s1 + (-s0)) + D*a1) + (-((X*P) + (-Q0))))
        ≈ (((X*s1 + (-s0)) + D*a1) + ((-(X*P)) + Q0)) :=
          Q'.add_eqv_congr_left _ _ _ (negSub (X*P) Q0)
      _ ≈ ((X*s1 + (-s0)) + (D*a1 + ((-(X*P)) + Q0))) :=
          Q'.add_assoc_eqv _ _ _
      _ ≈ (X*s1 + ((-s0) + (D*a1 + ((-(X*P)) + Q0)))) :=
          Q'.add_assoc_eqv _ _ _
  -- RHS normal form: same
  have hR : ((X * (s1 + (-P)) + (-(s0 + (-Q0)))) + D*a1)
      ≈ X*s1 + ((-s0) + ((D*a1) + ((-(X*P)) + Q0))) := by
    have eX : X * (s1 + (-P)) ≈ (X*s1) + (-(X*P)) :=
      Q'.eqv_trans _ _ _ (Q'.mul_add_eqv X s1 (-P))
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv X P))
    calc ((X * (s1 + (-P)) + (-(s0 + (-Q0)))) + D*a1)
        ≈ (((X*s1) + (-(X*P)) + ((-s0) + Q0)) + D*a1) := by
          refine Q'.add_eqv_congr_right _ _ _ ?_
          exact addC _ _ _ _ eX (negSub s0 Q0)
      _ ≈ ((X*s1) + ((-(X*P)) + ((-s0) + Q0)) + D*a1) :=
          Q'.add_eqv_congr_right _ _ _ (Q'.add_assoc_eqv _ _ _)
      _ ≈ (X*s1) + (((-(X*P)) + ((-s0) + Q0)) + D*a1) :=
          Q'.add_assoc_eqv _ _ _
      _ ≈ (X*s1) + ((-(X*P)) + (((-s0) + Q0) + D*a1)) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.add_assoc_eqv _ _ _)
      _ ≈ (X*s1) + ((-(X*P)) + ((-s0) + (Q0 + D*a1))) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_assoc_eqv _ _ _))
      _ ≈ (X*s1) + ((-s0) + ((-(X*P)) + (Q0 + D*a1))) := by
          -- swap (−(X·P)) and (−s0):  a + (b + R) ≈ b + (a + R)
          refine Q'.add_eqv_congr_left _ _ _ ?_
          calc (-(X*P)) + ((-s0) + (Q0 + D*a1))
              ≈ ((-(X*P)) + (-s0)) + (Q0 + D*a1) := Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
            _ ≈ ((-s0) + (-(X*P))) + (Q0 + D*a1) := Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)
            _ ≈ (-s0) + ((-(X*P)) + (Q0 + D*a1)) := Q'.add_assoc_eqv _ _ _
      _ ≈ (X*s1) + ((-s0) + ((-(X*P)) + (D*a1 + Q0))) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _
            (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv Q0 (D*a1))))
      _ ≈ (X*s1) + ((-s0) + ((D*a1) + ((-(X*P)) + Q0))) := by
          refine Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _ ?_)
          -- (−(X·P)) + (D·a1 + Q0) ≈ D·a1 + ((−(X·P)) + Q0)
          calc (-(X*P)) + ((D*a1) + Q0)
              ≈ ((-(X*P)) + (D*a1)) + Q0 := Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
            _ ≈ ((D*a1) + (-(X*P))) + Q0 := Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)
            _ ≈ (D*a1) + ((-(X*P)) + Q0) := Q'.add_assoc_eqv _ _ _
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

/-- Generalized abstract core (6 atoms) for the `Arem` recurrence, where BOTH the
homogeneous sequence and the inhomogeneous driver are differences.
`((X·s1 + (−s0)) + D·sa1) + (−((X·P + (−Q0)) + D·pa1))
  ≈ (X·(s1 + (−P)) + (−(s0 + (−Q0)))) + D·(sa1 + (−pa1))`. -/
theorem diffRec_core2 (X D s1 s0 sa1 P Q0 pa1 : Q') :
    (((X*s1 + (-s0)) + D*sa1) + (-((X*P + (-Q0)) + D*pa1)))
      ≈ ((X * (s1 + (-P)) + (-(s0 + (-Q0)))) + D * (sa1 + (-pa1))) := by
  -- LHS → addNF6 (X·s1, −s0, D·sa1, −(X·P), Q0, −(D·pa1))
  have hL : (((X*s1 + (-s0)) + D*sa1) + (-((X*P + (-Q0)) + D*pa1)))
      ≈ addNF6 (X*s1) (-s0) (D*sa1) (-(X*P)) Q0 (-(D*pa1)) := by
    unfold addNF6
    calc (((X*s1 + (-s0)) + D*sa1) + (-((X*P + (-Q0)) + D*pa1)))
        ≈ (((X*s1 + (-s0)) + D*sa1) + ((-(X*P + (-Q0))) + (-(D*pa1)))) :=
          Q'.add_eqv_congr_left _ _ _ (Cheb.neg_add_eqv (X*P + (-Q0)) (D*pa1))
      _ ≈ (((X*s1 + (-s0)) + D*sa1) + (((-(X*P)) + Q0) + (-(D*pa1)))) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_right _ _ _ (negSub (X*P) Q0))
      _ ≈ ((X*s1 + (-s0)) + (D*sa1 + (((-(X*P)) + Q0) + (-(D*pa1))))) :=
          Q'.add_assoc_eqv _ _ _
      _ ≈ (X*s1 + ((-s0) + (D*sa1 + (((-(X*P)) + Q0) + (-(D*pa1)))))) :=
          Q'.add_assoc_eqv _ _ _
      _ ≈ X*s1 + ((-s0) + (D*sa1 + ((-(X*P)) + (Q0 + (-(D*pa1)))))) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _
            (Q'.add_eqv_congr_left _ _ _ (Q'.add_assoc_eqv _ _ _)))
  -- RHS → addNF6 (X·s1, −(X·P), −s0, Q0, D·sa1, −(D·pa1))
  have hR : ((X * (s1 + (-P)) + (-(s0 + (-Q0)))) + D * (sa1 + (-pa1)))
      ≈ addNF6 (X*s1) (-(X*P)) (-s0) Q0 (D*sa1) (-(D*pa1)) := by
    have eX : X * (s1 + (-P)) ≈ (X*s1) + (-(X*P)) :=
      Q'.eqv_trans _ _ _ (Q'.mul_add_eqv X s1 (-P))
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv X P))
    have eD : D * (sa1 + (-pa1)) ≈ (D*sa1) + (-(D*pa1)) :=
      Q'.eqv_trans _ _ _ (Q'.mul_add_eqv D sa1 (-pa1))
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv D pa1))
    calc ((X * (s1 + (-P)) + (-(s0 + (-Q0)))) + D * (sa1 + (-pa1)))
        ≈ (((X*s1) + (-(X*P)) + ((-s0) + Q0)) + ((D*sa1) + (-(D*pa1)))) := by
          refine addC _ _ _ _ ?_ eD
          exact addC _ _ _ _ eX (negSub s0 Q0)
      _ ≈ addNF6 (X*s1) (-(X*P)) (-s0) Q0 (D*sa1) (-(D*pa1)) := to_addNF6_B _ _ _ _ _ _
  refine Q'.eqv_trans _ _ _ hL (Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hR))
  -- addNF6 (X·s1) (−s0) (D·sa1) (−(X·P)) Q0 (−(D·pa1))
  --   ≈ addNF6 (X·s1) (−(X·P)) (−s0) Q0 (D·sa1) (−(D·pa1))
  unfold addNF6
  refine Q'.add_eqv_congr_left _ _ _ ?_
  -- (−s0) + (D·sa1 + ((−(X·P)) + (Q0 + (−(D·pa1)))))
  --   ≈ (−(X·P)) + ((−s0) + (Q0 + (D·sa1 + (−(D·pa1)))))
  calc (-s0) + ((D*sa1) + ((-(X*P)) + (Q0 + (-(D*pa1)))))
      ≈ (-s0) + ((D*sa1) + ((-(X*P)) + ((-(D*pa1)) + Q0))) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv Q0 (-(D*pa1)))))
    _ ≈ (-s0) + ((D*sa1) + (((-(X*P)) + (-(D*pa1))) + Q0)) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)))
    _ ≈ (-s0) + (((D*sa1) + ((-(X*P)) + (-(D*pa1)))) + Q0) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
    _ ≈ (-s0) + ((((-(X*P)) + (-(D*pa1))) + (D*sa1)) + Q0) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _))
    _ ≈ (-s0) + (((-(X*P)) + ((-(D*pa1)) + (D*sa1))) + Q0) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.add_assoc_eqv _ _ _))
    _ ≈ (-s0) + (((-(X*P)) + ((D*sa1) + (-(D*pa1)))) + Q0) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_right _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)))
    -- now: (−s0) + (((−(X·P)) + (D·sa1 + (−(D·pa1)))) + Q0)
    _ ≈ ((-(X*P)) + ((-s0) + (Q0 + ((D*sa1) + (-(D*pa1)))))) := by
        calc (-s0) + (((-(X*P)) + ((D*sa1) + (-(D*pa1)))) + Q0)
            ≈ (-s0) + ((-(X*P)) + (((D*sa1) + (-(D*pa1))) + Q0)) :=
              Q'.add_eqv_congr_left _ _ _ (Q'.add_assoc_eqv _ _ _)
          _ ≈ (-s0) + ((-(X*P)) + (Q0 + ((D*sa1) + (-(D*pa1))))) :=
              Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _))
          _ ≈ ((-s0) + (-(X*P))) + (Q0 + ((D*sa1) + (-(D*pa1)))) :=
              Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
          _ ≈ ((-(X*P)) + (-s0)) + (Q0 + ((D*sa1) + (-(D*pa1)))) :=
              Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)
          _ ≈ (-(X*P)) + ((-s0) + (Q0 + ((D*sa1) + (-(D*pa1))))) :=
              Q'.add_assoc_eqv _ _ _
    _ ≈ (-(X*P)) + ((-s0) + (Q0 + ((D*sa1) + (-(D*pa1))))) := Q'.eqv_refl _

/-- The driver `W n = 2·(δ·U'_n(x))` satisfies
`W(n+2) ≈ 2x·W(n+1) + (−W(n)) + 2δ·(2·U_{n+1}(x))`. -/
theorem W_rec (x δ : Q') (n : Nat) :
    ((1:Q')+(1:Q')) * (δ * Uderiv (n+2) x)
      ≈ ((((1:Q')+(1:Q'))*x) * (((1:Q')+(1:Q')) * (δ * Uderiv (n+1) x))
            + (-(((1:Q')+(1:Q')) * (δ * Uderiv n x))))
          + (((1:Q')+(1:Q'))*δ) * (((1:Q')+(1:Q')) * Cheb.U (n+1) x) := by
  rw [Uderiv_succ_succ n x]
  -- abbreviations as in the derivation, with c = (1+1)
  -- LHS = c*(δ*( (2)·U(n+1) + ((2x)·U'(n+1) + (-U'(n))) ))
  -- atom equalities
  have hT1 : ((1:Q')+(1:Q')) * (δ * (((1:Q')+(1:Q')) * Cheb.U (n+1) x))
      ≈ (((1:Q')+(1:Q'))*δ) * (((1:Q')+(1:Q')) * Cheb.U (n+1) x) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  have hT2 : ((1:Q')+(1:Q')) * (δ * ((((1:Q')+(1:Q'))*x) * Uderiv (n+1) x))
      ≈ (((1:Q')+(1:Q'))*x) * (((1:Q')+(1:Q')) * (δ * Uderiv (n+1) x)) := by
    -- both ≈ c·(cx)·(δ·d1); reassociate / commute
    calc ((1:Q')+(1:Q')) * (δ * ((((1:Q')+(1:Q'))*x) * Uderiv (n+1) x))
        ≈ ((1:Q')+(1:Q')) * ((δ * (((1:Q')+(1:Q'))*x)) * Uderiv (n+1) x) :=
          Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      _ ≈ ((1:Q')+(1:Q')) * (((((1:Q')+(1:Q'))*x) * δ) * Uderiv (n+1) x) :=
          Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
      _ ≈ ((1:Q')+(1:Q')) * ((((1:Q')+(1:Q'))*x) * (δ * Uderiv (n+1) x)) :=
          Q'.mul_eqv_congr_left _ _ _ (Q'.mul_assoc_eqv _ _ _)
      _ ≈ (((1:Q')+(1:Q')) * (((1:Q')+(1:Q'))*x)) * (δ * Uderiv (n+1) x) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
      _ ≈ ((((1:Q')+(1:Q'))*x) * ((1:Q')+(1:Q'))) * (δ * Uderiv (n+1) x) :=
          Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)
      _ ≈ (((1:Q')+(1:Q'))*x) * (((1:Q')+(1:Q')) * (δ * Uderiv (n+1) x)) :=
          Q'.mul_assoc_eqv _ _ _
  have hT3 : ((1:Q')+(1:Q')) * (δ * (-(Uderiv n x)))
      ≈ (-(((1:Q')+(1:Q')) * (δ * Uderiv n x))) := by
    calc ((1:Q')+(1:Q')) * (δ * (-(Uderiv n x)))
        ≈ ((1:Q')+(1:Q')) * (-(δ * Uderiv n x)) :=
          Q'.mul_eqv_congr_left _ _ _ (Q'.mul_neg_eqv _ _)
      _ ≈ (-(((1:Q')+(1:Q')) * (δ * Uderiv n x))) := Q'.mul_neg_eqv _ _
  -- distribute LHS into T1 + (T2 + T3)
  have hdist : ((1:Q')+(1:Q')) * (δ * (((1:Q')+(1:Q')) * Cheb.U (n+1) x
        + ((((1:Q')+(1:Q'))*x) * Uderiv (n+1) x + (-(Uderiv n x)))))
      ≈ (((1:Q')+(1:Q')) * (δ * (((1:Q')+(1:Q')) * Cheb.U (n+1) x)))
          + ((((1:Q')+(1:Q')) * (δ * ((((1:Q')+(1:Q'))*x) * Uderiv (n+1) x)))
              + (((1:Q')+(1:Q')) * (δ * (-(Uderiv n x))))) := by
    -- δ*(A + (B + C)) ≈ δ*A + (δ*B + δ*C), then c*(...) distributes
    have hδ : δ * (((1:Q')+(1:Q')) * Cheb.U (n+1) x
          + ((((1:Q')+(1:Q'))*x) * Uderiv (n+1) x + (-(Uderiv n x))))
        ≈ (δ * (((1:Q')+(1:Q')) * Cheb.U (n+1) x))
            + ((δ * ((((1:Q')+(1:Q'))*x) * Uderiv (n+1) x)) + (δ * (-(Uderiv n x)))) :=
      Q'.eqv_trans _ _ _ (Q'.mul_add_eqv δ _ _)
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_add_eqv δ _ _))
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hδ) ?_
    -- c*(δA + (δB + δC)) ≈ c*(δA) + (c*(δB) + c*(δC))
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_add_eqv _ _ _)
  refine Q'.eqv_trans _ _ _ hdist ?_
  -- T1 + (T2 + T3) ≈ ((cx·W(n+1) + (-W(n))) + (cδ)·(c·e1))
  -- substitute atom equalities, then reorder a+(b+c) ≈ (b+c)+a
  refine Q'.eqv_trans _ _ _
    (addC _ _ _ _ hT1 (addC _ _ _ _ hT2 hT3)) ?_
  -- now: T1' + (T2' + T3')  with
  --   T1' = (cδ)·(c·e1), T2' = (cx)·W(n+1), T3' = (-W(n))
  -- target: ((cx)·W(n+1) + (-W(n))) + (cδ)·(c·e1) = (T2' + T3') + T1'
  exact Q'.add_comm_eqv _ _

/-- **The antisymmetric-remainder recurrence**
`Arem(n+2) ≈ 2x·Arem(n+1) + (−Arem(n)) + 2δ·Sdiff(n+1)`. -/
theorem Arem_rec (x δ : Q') (n : Nat) :
    Arem x δ (n+2)
      ≈ ((((1:Q')+(1:Q'))*x) * Arem x δ (n+1) + (-(Arem x δ n)))
          + (((1:Q')+(1:Q'))*δ) * Sdiff x δ (n+1) := by
  -- Arem(n+2) = Adiff(n+2) + (−W(n+2))
  show (Adiff x δ (n+2) + (-(((1:Q')+(1:Q')) * (δ * Uderiv (n+2) x))))
      ≈ ((((1:Q')+(1:Q'))*x) * (Adiff x δ (n+1) + (-(((1:Q')+(1:Q')) * (δ * Uderiv (n+1) x))))
            + (-(Adiff x δ n + (-(((1:Q')+(1:Q')) * (δ * Uderiv n x))))))
          + (((1:Q')+(1:Q'))*δ) * Sdiff x δ (n+1)
  refine Q'.eqv_trans _ _ _
    (addC _ _ _ _ (Adiff_rec x δ n) (Q'.neg_eqv_congr _ _ (W_rec x δ n))) ?_
  -- now diffRec_core2 with X=2x, D=2δ, s1=Adiff(n+1), s0=Adiff(n),
  -- sa1=Ssum(n+1), P=W(n+1), Q0=W(n), pa1=2·U(n+1)x, and Sdiff(n+1)=sa1+(-pa1)
  exact diffRec_core2 (((1:Q')+(1:Q'))*x) (((1:Q')+(1:Q'))*δ)
    (Adiff x δ (n+1)) (Adiff x δ n) (Ssum x δ (n+1))
    (((1:Q')+(1:Q')) * (δ * Uderiv (n+1) x)) (((1:Q')+(1:Q')) * (δ * Uderiv n x))
    (((1:Q')+(1:Q')) * Cheb.U (n+1) x)

/-- **The symmetric second-difference recurrence**
`Sdiff(n+2) ≈ 2x·Sdiff(n+1) + (−Sdiff(n)) + 2δ·Adiff(n+1)`. -/
theorem Sdiff_rec (x δ : Q') (n : Nat) :
    Sdiff x δ (n+2)
      ≈ ((((1:Q')+(1:Q'))*x) * Sdiff x δ (n+1) + (-(Sdiff x δ n)))
          + (((1:Q')+(1:Q'))*δ) * Adiff x δ (n+1) := by
  -- Sdiff(n+2) = Ssum(n+2) + (−(2·U(n+2)x))
  show (Ssum x δ (n+2) + (-(((1:Q')+(1:Q')) * Cheb.U (n+2) x)))
      ≈ ((((1:Q')+(1:Q'))*x) * (Ssum x δ (n+1) + (-(((1:Q')+(1:Q')) * Cheb.U (n+1) x)))
            + (-(Ssum x δ n + (-(((1:Q')+(1:Q')) * Cheb.U n x)))))
          + (((1:Q')+(1:Q'))*δ) * Adiff x δ (n+1)
  refine Q'.eqv_trans _ _ _
    (addC _ _ _ _ (Ssum_rec x δ n) (Q'.neg_eqv_congr _ _ (twoU_rec x n))) ?_
  -- now exactly diffRec_core
  exact diffRec_core (((1:Q')+(1:Q'))*x) (((1:Q')+(1:Q'))*δ)
    (Ssum x δ (n+1)) (Ssum x δ n) (Adiff x δ (n+1))
    (((1:Q')+(1:Q')) * Cheb.U (n+1) x) (((1:Q')+(1:Q')) * Cheb.U n x)

/-- Tighten a symmetric bound `−R ≤ v ≤ R` to `−B ≤ v ≤ B` when `R ≤ B`. -/
theorem tighten {v R B : Q'} (hl : (-R) ≤ v) (hu : v ≤ R) (hRB : R ≤ B) :
    (-B) ≤ v ∧ v ≤ B :=
  ⟨Q'.le_trans' _ (-R) _ (Q'.neg_le_neg hRB) hl, Q'.le_trans' _ R _ hu hRB⟩

/-! ## 2b. `ofNat` arithmetic helpers for the majorant reconciliation -/

/-- `(1+1)·ofNat k ≈ ofNat (2·k)`. -/
theorem two_mul_ofNat (k : Nat) : ((1:Q')+(1:Q')) * Q'.ofNat k ≈ Q'.ofNat (2*k) := by
  -- (1+1)·ofNat k ≈ ofNat k + ofNat k ≈ ofNat (k+k) = ofNat (2k)
  refine Q'.eqv_trans _ _ _ (Cheb.add_mul_eqv 1 1 (Q'.ofNat k)) ?_
  refine Q'.eqv_trans _ _ _
    (addC _ _ _ _ (Q'.one_mul_eqv _) (Q'.one_mul_eqv _)) ?_
  refine Q'.eqv_trans _ _ _ (ChebU.ofNat_add_eqv k k) ?_
  have hk : k + k = 2 * k := by omega
  rw [hk]; exact Q'.eqv_refl _

/-- `(1+1)·(ofNat k · w) ≈ ofNat (2·k) · w`. -/
theorem two_mul_ofNat_mul (k : Nat) (w : Q') :
    ((1:Q')+(1:Q')) * (Q'.ofNat k * w) ≈ Q'.ofNat (2*k) * w :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.mul_eqv_congr_right _ _ _ (two_mul_ofNat k))

/-- `ofNat k · w ≈ ofNat k · w'` from `w ≈ w'`. -/
theorem ofNat_mul_congr (k : Nat) {w w' : Q'} (h : w ≈ w') :
    Q'.ofNat k * w ≈ Q'.ofNat k * w' :=
  Q'.mul_eqv_congr_left _ _ _ h

/-- **Generic reconciliation** of the `step_bound` constant `R` with the majorant
times a δ-power `P`.  Given `Bv1 ≈ ofNat b1·P`, `Bv0 ≈ ofNat b0·P`, and the inhom
identity `(1+1)·δ·Bw1 ≈ ofNat (2·w)·P`,
`((1+1)·Bv1 + Bv0) + ((1+1)·δ)·Bw1 ≈ ofNat (2·b1 + 2·w + b0)·P`. -/
theorem R_recon {δ P Bv1 Bv0 Bw1 : Q'} (b1 b0 w : Nat)
    (hBv1 : Bv1 ≈ Q'.ofNat b1 * P) (hBv0 : Bv0 ≈ Q'.ofNat b0 * P)
    (hInhom : ((1:Q')+(1:Q'))*δ * Bw1 ≈ Q'.ofNat (2*w) * P) :
    (((1:Q')+(1:Q'))*Bv1 + Bv0) + (((1:Q')+(1:Q'))*δ)*Bw1
      ≈ Q'.ofNat (2*b1 + 2*w + b0) * P := by
  -- rewrite the three pieces
  have h1 : ((1:Q')+(1:Q'))*Bv1 ≈ Q'.ofNat (2*b1) * P :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hBv1) (two_mul_ofNat_mul b1 P)
  -- assemble:  (ofNat(2b1)·P + ofNat b0·P) + ofNat(2w)·P
  refine Q'.eqv_trans _ _ _ (addC _ _ _ _ (addC _ _ _ _ h1 hBv0) hInhom) ?_
  -- (ofNat(2b1)·P + ofNat b0·P) + ofNat(2w)·P ≈ ofNat(2b1+2w+b0)·P
  refine Q'.eqv_trans _ _ _
    (addC _ _ _ _ (ofNat_add_mul (2*b1) b0 P) (Q'.eqv_refl (Q'.ofNat (2*w) * P))) ?_
  refine Q'.eqv_trans _ _ _ (ofNat_add_mul (2*b1 + b0) (2*w) P) ?_
  have he : (2*b1 + b0) + 2*w = 2*b1 + 2*w + b0 := by omega
  rw [he]; exact Q'.eqv_refl _

/-- Inhom identity (B2): `(1+1)·δ·ofNat k ≈ ofNat (2k)·δ`. -/
theorem inhom_A (k : Nat) (δ : Q') :
    ((1:Q')+(1:Q'))*δ * Q'.ofNat k ≈ Q'.ofNat (2*k) * δ := by
  calc ((1:Q')+(1:Q'))*δ * Q'.ofNat k
      ≈ ((1:Q')+(1:Q')) * (δ * Q'.ofNat k) := Q'.mul_assoc_eqv _ _ _
    _ ≈ ((1:Q')+(1:Q')) * (Q'.ofNat k * δ) :=
        Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)
    _ ≈ Q'.ofNat (2*k) * δ := two_mul_ofNat_mul k δ

/-- Inhom identity (B3): `(1+1)·δ·(ofNat k·δ) ≈ ofNat (2k)·(δ·δ)`. -/
theorem inhom_S (k : Nat) (δ : Q') :
    ((1:Q')+(1:Q'))*δ * (Q'.ofNat k * δ) ≈ Q'.ofNat (2*k) * (δ*δ) := by
  calc ((1:Q')+(1:Q'))*δ * (Q'.ofNat k * δ)
      ≈ ((1:Q')+(1:Q')) * (δ * (Q'.ofNat k * δ)) := Q'.mul_assoc_eqv _ _ _
    _ ≈ ((1:Q')+(1:Q')) * ((δ * Q'.ofNat k) * δ) :=
        Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    _ ≈ ((1:Q')+(1:Q')) * ((Q'.ofNat k * δ) * δ) :=
        Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
    _ ≈ ((1:Q')+(1:Q')) * (Q'.ofNat k * (δ * δ)) :=
        Q'.mul_eqv_congr_left _ _ _ (Q'.mul_assoc_eqv _ _ _)
    _ ≈ Q'.ofNat (2*k) * (δ*δ) := two_mul_ofNat_mul k (δ*δ)

/-- Inhom identity (B4): `(1+1)·δ·(ofNat k·(δ·δ)) ≈ ofNat (2k)·((δ·δ)·δ)`. -/
theorem inhom_KS (k : Nat) (δ : Q') :
    ((1:Q')+(1:Q'))*δ * (Q'.ofNat k * (δ*δ)) ≈ Q'.ofNat (2*k) * ((δ*δ)*δ) := by
  calc ((1:Q')+(1:Q'))*δ * (Q'.ofNat k * (δ*δ))
      ≈ ((1:Q')+(1:Q')) * (δ * (Q'.ofNat k * (δ*δ))) := Q'.mul_assoc_eqv _ _ _
    _ ≈ ((1:Q')+(1:Q')) * ((δ * Q'.ofNat k) * (δ*δ)) :=
        Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    _ ≈ ((1:Q')+(1:Q')) * ((Q'.ofNat k * δ) * (δ*δ)) :=
        Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
    _ ≈ ((1:Q')+(1:Q')) * (Q'.ofNat k * (δ * (δ*δ))) :=
        Q'.mul_eqv_congr_left _ _ _ (Q'.mul_assoc_eqv _ _ _)
    _ ≈ ((1:Q')+(1:Q')) * (Q'.ofNat k * ((δ*δ)*δ)) :=
        Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv δ (δ*δ)))
    _ ≈ Q'.ofNat (2*k) * ((δ*δ)*δ) := two_mul_ofNat_mul k ((δ*δ)*δ)

/-- `0 ≤ ofNat k`. -/
theorem ofNat_nonneg (k : Nat) : (0:Q') ≤ Q'.ofNat k := by
  show (0:Q').num * ((Q'.ofNat k).den : Int) ≤ (Q'.ofNat k).num * ((0:Q').den : Int)
  show (0:Int) * 1 ≤ (Int.ofNat k) * 1
  rw [Int.zero_mul, Int.mul_one]; exact Int.ofNat_nonneg k

/-- `δ·δ ≤ 1` on the box (`0 ≤ δ ≤ 1`). -/
theorem sq_le_one {δ : Q'} (hδ0 : (0:Q') ≤ δ) (hδ1 : δ ≤ (1:Q')) : δ*δ ≤ (1:Q') := by
  -- δ·δ ≤ δ·1 = δ ≤ 1
  refine Q'.le_trans' _ (δ * (1:Q')) _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hδ1 hδ0) ?_
  exact Q'.le_trans' _ δ _ (Q'.le_of_eqv (Q'.mul_one_eqv δ)) hδ1

/-- `ofNat k · (δ·δ) ≤ ofNat k` on the box. -/
theorem ofNat_sq_le {δ : Q'} (k : Nat) (hδ0 : (0:Q') ≤ δ) (hδ1 : δ ≤ (1:Q')) :
    Q'.ofNat k * (δ*δ) ≤ Q'.ofNat k := by
  refine Q'.le_trans' _ (Q'.ofNat k * (1:Q')) _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (sq_le_one hδ0 hδ1) (ofNat_nonneg k)) ?_
  exact Q'.le_of_eqv (Q'.mul_one_eqv _)

/-! ## 3. The generic two-sided step bound

A single lemma bounds `v2 = (2x·v1 + (−v0)) + 2δ·w1` from two-sided bounds on
`v0, v1, w1`, given `|x| ≤ 1`, `0 ≤ δ`. -/

/-- `0 ≤ (1:Q')+(1:Q')`. -/
theorem two_nonneg : (0:Q') ≤ (1:Q')+(1:Q') := by decide

/-- `(1+1)·x` is bounded by `±(1+1)` when `−1 ≤ x ≤ 1`. -/
theorem twoX_bounds (x : Q') (hx1 : x ≤ (1:Q')) (hxm1 : (-(1:Q')) ≤ x) :
    (-((1:Q')+(1:Q'))) ≤ ((1:Q')+(1:Q'))*x ∧ ((1:Q')+(1:Q'))*x ≤ ((1:Q')+(1:Q')) := by
  constructor
  · -- −(1+1) ≈ (1+1)·(−1) ≤ (1+1)·x
    refine Q'.le_trans' _ (((1:Q')+(1:Q'))*(-(1:Q'))) _ ?_
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hxm1 two_nonneg)
    -- −(1+1) ≈ (1+1)·(−1)
    exact Q'.ge_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv _ _)
      (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv _)))
  · -- (1+1)·x ≤ (1+1)·1 ≈ (1+1)
    refine Q'.le_trans' _ (((1:Q')+(1:Q'))*(1:Q')) _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hx1 two_nonneg) ?_
    exact Q'.le_of_eqv (Q'.mul_one_eqv _)

/-- `0 ≤ (1+1)·δ` from `0 ≤ δ`. -/
theorem twoδ_nonneg {δ : Q'} (hδ : (0:Q') ≤ δ) : (0:Q') ≤ ((1:Q')+(1:Q'))*δ :=
  Q'.mul_nonneg _ _ two_nonneg hδ

/-- Two-sided product bound `−(B·d) ≤ u·v ≤ B·d` from `|u| ≤ B`, `|v| ≤ d`,
`0 ≤ B`, `0 ≤ d`. -/
theorem mul_abs_bound {u v B d : Q'} (hB : (0:Q') ≤ B) (hd : (0:Q') ≤ d)
    (hu1 : (-B) ≤ u) (hu2 : u ≤ B) (hv1 : (-d) ≤ v) (hv2 : v ≤ d) :
    (-(B*d)) ≤ u*v ∧ u*v ≤ B*d := by
  refine ⟨?_, Q'.mul_le_of_bounds hB hd hu1 hu2 hv1 hv2⟩
  -- −(B·d) ≤ u·v.  Bound (−u)·v ≤ B·d (|−u| ≤ B), then negate.
  have hnu1 : (-B) ≤ (-u) := Q'.neg_le_neg hu2
  have hnu2 : (-u) ≤ B :=
    Q'.le_trans' _ (-(-B)) _ (Q'.neg_le_neg hu1) (Q'.le_of_eqv (Q'.neg_neg_eqv B))
  have h := Q'.mul_le_of_bounds hB hd hnu1 hnu2 hv1 hv2  -- (−u)·v ≤ B·d
  -- (−u)·v ≈ −(u·v)
  have hneg : (-(u*v)) ≤ B*d :=
    Q'.le_trans' _ ((-u)*v) _ (Q'.ge_of_eqv (Q'.neg_mul_eqv u v)) h
  -- −(B·d) ≤ −(−(u·v)) ≈ u·v
  refine Q'.le_trans' _ (-(-(u*v))) _ (Q'.neg_le_neg hneg) (Q'.le_of_eqv (Q'.neg_neg_eqv (u*v)))

/-- `−c ≤ c` when `0 ≤ c`. -/
theorem neg_self_le_of_nonneg {c : Q'} (hc : (0:Q') ≤ c) : (-c) ≤ c := by
  have h0 : (-c) ≤ (-(0:Q')) := Q'.neg_le_neg hc
  have e : (-(0:Q')) = (0:Q') := rfl
  rw [e] at h0
  exact Q'.le_trans' _ (0:Q') _ h0 hc

/-- **The generic two-sided step bound.**  If
`v2 ≈ (2x·v1 + (−v0)) + 2δ·w1` and `−Bv0 ≤ v0 ≤ Bv0`, `−Bv1 ≤ v1 ≤ Bv1`,
`−Bw1 ≤ w1 ≤ Bw1` (all bounds `≥ 0`), `−1 ≤ x ≤ 1`, `0 ≤ δ`, then
`−R ≤ v2 ≤ R`  with  `R = ((1+1)·Bv1 + Bv0) + ((1+1)·δ)·Bw1`. -/
theorem step_bound {x δ v2 v1 v0 w1 Bv1 Bv0 Bw1 : Q'}
    (hrec : v2 ≈ ((((1:Q')+(1:Q'))*x) * v1 + (-v0)) + (((1:Q')+(1:Q'))*δ) * w1)
    (hx1 : x ≤ (1:Q')) (hxm1 : (-(1:Q')) ≤ x) (hδ : (0:Q') ≤ δ)
    (hBv1 : (0:Q') ≤ Bv1) (hBv0 : (0:Q') ≤ Bv0) (hBw1 : (0:Q') ≤ Bw1)
    (hv1a : (-Bv1) ≤ v1) (hv1b : v1 ≤ Bv1)
    (hv0a : (-Bv0) ≤ v0) (hv0b : v0 ≤ Bv0)
    (hw1a : (-Bw1) ≤ w1) (hw1b : w1 ≤ Bw1) :
    (-((((1:Q')+(1:Q'))*Bv1 + Bv0) + (((1:Q')+(1:Q'))*δ)*Bw1)) ≤ v2
      ∧ v2 ≤ (((1:Q')+(1:Q'))*Bv1 + Bv0) + (((1:Q')+(1:Q'))*δ)*Bw1 := by
  obtain ⟨hXl, hXu⟩ := twoX_bounds x hx1 hxm1
  -- bound on 2x·v1:  −((1+1)·Bv1) ≤ 2x·v1 ≤ (1+1)·Bv1
  obtain ⟨hP1l, hP1u⟩ := mul_abs_bound two_nonneg hBv1 hXl hXu hv1a hv1b
  -- bound on −v0:  −Bv0 ≤ −v0 ≤ Bv0
  have hN0u : (-v0) ≤ Bv0 :=
    Q'.le_trans' _ (-(-Bv0)) _ (Q'.neg_le_neg hv0a) (Q'.le_of_eqv (Q'.neg_neg_eqv Bv0))
  have hN0l : (-Bv0) ≤ (-v0) := Q'.neg_le_neg hv0b
  -- bound on 2δ·w1:  −((2δ)·Bw1) ≤ 2δ·w1 ≤ (2δ)·Bw1
  have h2δ : (0:Q') ≤ ((1:Q')+(1:Q'))*δ := twoδ_nonneg hδ
  obtain ⟨hW1l, hW1u⟩ :=
    mul_abs_bound h2δ hBw1
      (neg_self_le_of_nonneg h2δ) (Q'.le_refl' (((1:Q')+(1:Q'))*δ)) hw1a hw1b
  -- assemble:  v2 ≈ (2x·v1 + (−v0)) + 2δ·w1
  -- upper
  have hupper : v2 ≤ (((1:Q')+(1:Q'))*Bv1 + Bv0) + (((1:Q')+(1:Q'))*δ)*Bw1 := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hrec) ?_
    exact Q'.add_le_add (Q'.add_le_add hP1u hN0u) hW1u
  -- lower:  −R ≤ v2.  Use −R ≤ (2x·v1 + (−v0)) + 2δ·w1 ≈ v2.
  have hlower : (-((((1:Q')+(1:Q'))*Bv1 + Bv0) + (((1:Q')+(1:Q'))*δ)*Bw1)) ≤ v2 := by
    refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hrec)
    -- −((A + Bv0) + W) ≈ ((−A) + (−Bv0)) + (−W) ≤ (2x·v1 + (−v0)) + 2δ·w1
    refine Q'.le_trans' _ ((((-(((1:Q')+(1:Q'))*Bv1)) + (-Bv0)) + (-((((1:Q')+(1:Q'))*δ)*Bw1)))) _
      (Q'.le_of_eqv ?_) ?_
    · -- −((A + Bv0) + W) ≈ ((−A) + (−Bv0)) + (−W)
      refine Q'.eqv_trans _ _ _ (Cheb.neg_add_eqv _ _) ?_
      exact Q'.add_eqv_congr_right _ _ _ (Cheb.neg_add_eqv _ _)
    · exact Q'.add_le_add (Q'.add_le_add hP1l hN0l) hW1l
  exact ⟨hlower, hupper⟩

/-- `ofNat 0 ≈ 0`. -/
theorem ofNat_zero_eqv : Q'.ofNat 0 ≈ (0:Q') := Q'.eqv_refl _

/-- `ofNat 0 · w ≈ 0`. -/
theorem ofNat_zero_mul (w : Q') : Q'.ofNat 0 * w ≈ (0:Q') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ofNat_zero_eqv) (Q'.zero_mul_eqv w)

/-- B1 reconciliation (the δ⁰ case, using δ² ≤ 1):
`((1+1)·ofNat b1 + ofNat b0) + ((1+1)·δ)·(ofNat w · δ) ≤ ofNat (2·b1 + 2·w + b0)`. -/
theorem R_const_le (b1 b0 w : Nat) {δ : Q'} (hδ0 : (0:Q') ≤ δ) (hδ1 : δ ≤ (1:Q')) :
    (((1:Q')+(1:Q'))*Q'.ofNat b1 + Q'.ofNat b0) + (((1:Q')+(1:Q'))*δ)*(Q'.ofNat w * δ)
      ≤ Q'.ofNat (2*b1 + 2*w + b0) := by
  -- bound the inhom:  ((1+1)δ)·(ofNat w·δ) ≈ ofNat(2w)·(δ·δ) ≤ ofNat(2w)
  have hWeq : (((1:Q')+(1:Q'))*δ)*(Q'.ofNat w * δ) ≈ Q'.ofNat (2*w) * (δ*δ) := inhom_S w δ
  have hWle : (((1:Q')+(1:Q'))*δ)*(Q'.ofNat w * δ) ≤ Q'.ofNat (2*w) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hWeq) (ofNat_sq_le (2*w) hδ0 hδ1)
  -- bound (1+1)·ofNat b1 ≈ ofNat(2b1)
  have hb1 : ((1:Q')+(1:Q'))*Q'.ofNat b1 ≈ Q'.ofNat (2*b1) := two_mul_ofNat b1
  -- assemble:  ≤ ofNat(2b1) + ofNat b0 + ofNat(2w) ≈ ofNat(2b1 + b0 + 2w)
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add (Q'.add_le_add (Q'.le_of_eqv hb1) (Q'.le_refl' (Q'.ofNat b0))) hWle) ?_
  -- (ofNat 2b1 + ofNat b0) + ofNat 2w ≈ ofNat (2b1 + b0 + 2w) = ofNat (2b1+2w+b0)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (ChebU.ofNat_add_eqv (2*b1) b0 |> fun h =>
    Q'.eqv_trans _ _ _ (addC _ _ _ _ h (Q'.eqv_refl (Q'.ofNat (2*w))))
      (ChebU.ofNat_add_eqv (2*b1 + b0) (2*w)))) ?_
  have he : (2*b1 + b0) + 2*w = 2*b1 + 2*w + b0 := by omega
  rw [he]; exact Q'.le_refl' _

/-! ## 4. The bundled four-way bound predicate and its two-step induction -/

/-- The four simultaneous two-sided bounds at index `n`, for fixed `x, δ`. -/
def QB (x δ : Q') (n : Nat) : Prop :=
  ((-(Q'.ofNat (Smaj n))) ≤ Ssum x δ n ∧ Ssum x δ n ≤ Q'.ofNat (Smaj n))
  ∧ ((-(Q'.ofNat (Amaj n) * δ)) ≤ Adiff x δ n ∧ Adiff x δ n ≤ Q'.ofNat (Amaj n) * δ)
  ∧ ((-(Q'.ofNat (KS n) * (δ*δ))) ≤ Sdiff x δ n ∧ Sdiff x δ n ≤ Q'.ofNat (KS n) * (δ*δ))
  ∧ ((-(Q'.ofNat (KA n) * ((δ*δ)*δ))) ≤ Arem x δ n
      ∧ Arem x δ n ≤ Q'.ofNat (KA n) * ((δ*δ)*δ))

/-! ### Base cases -/

/-- `−B ≤ v ≤ B` from `v ≈ B` and `0 ≤ B`. -/
theorem bound_of_eqv_nonneg {v B : Q'} (h : v ≈ B) (hB : (0:Q') ≤ B) :
    (-B) ≤ v ∧ v ≤ B := by
  refine ⟨?_, Q'.le_of_eqv h⟩
  exact Q'.le_trans' _ B _ (neg_self_le_of_nonneg hB) (Q'.ge_of_eqv h)

/-- `0 ≤ ofNat k · δ` on the box. -/
theorem ofNat_lin_nonneg (k : Nat) {δ : Q'} (hδ : (0:Q') ≤ δ) : (0:Q') ≤ Q'.ofNat k * δ :=
  Q'.mul_nonneg _ _ (ofNat_nonneg k) hδ

/-- `((1+1)+(1+1)) ≈ ofNat 4`. -/
theorem four_eqv : ((1:Q')+(1:Q'))+((1:Q')+(1:Q')) ≈ Q'.ofNat 4 := by
  refine Q'.eqv_trans _ _ _ (addC _ _ _ _ ChebU.one_add_one_eqv_two ChebU.one_add_one_eqv_two) ?_
  refine Q'.eqv_trans _ _ _ (ChebU.ofNat_add_eqv 2 2) ?_
  exact Q'.eqv_refl _

/-- `Ssum x δ 1 ≈ (1+1)·x + (1+1)·x`. -/
theorem Ssum_one_eqv (x δ : Q') :
    Ssum x δ 1 ≈ (((1:Q')+(1:Q'))*x) + (((1:Q')+(1:Q'))*x) := by
  show ((2:Q')*(x+δ) + (2:Q')*(x+(-δ))) ≈ (((1:Q')+(1:Q'))*x) + (((1:Q')+(1:Q'))*x)
  -- 2(x+δ) ≈ 2x + 2δ ;  2(x−δ) ≈ 2x + (−(2δ))
  have hL : (2:Q')*(x+δ) ≈ (((1:Q')+(1:Q'))*x) + (((1:Q')+(1:Q'))*δ) := Q'.mul_add_eqv _ _ _
  have hR : (2:Q')*(x+(-δ)) ≈ (((1:Q')+(1:Q'))*x) + (-(((1:Q')+(1:Q'))*δ)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv _ _))
  refine Q'.eqv_trans _ _ _ (addC _ _ _ _ hL hR) ?_
  -- (2x + 2δ) + (2x + (−2δ)) ≈ 2x + 2x
  calc ((((1:Q')+(1:Q'))*x) + (((1:Q')+(1:Q'))*δ)) + ((((1:Q')+(1:Q'))*x) + (-(((1:Q')+(1:Q'))*δ)))
      ≈ ((((1:Q')+(1:Q'))*x) + (((1:Q')+(1:Q'))*x)) + ((((1:Q')+(1:Q'))*δ) + (-(((1:Q')+(1:Q'))*δ))) :=
        add_swap_inner _ _ _ _
    _ ≈ ((((1:Q')+(1:Q'))*x) + (((1:Q')+(1:Q'))*x)) + (0:Q') :=
        Q'.add_eqv_congr_left _ _ _ (ChebU.add_neg_self_eqv _)
    _ ≈ (((1:Q')+(1:Q'))*x) + (((1:Q')+(1:Q'))*x) := by rw [Q'.add_zero']; exact Q'.eqv_refl _

/-- `Adiff x δ 1 ≈ (1+1)·δ + (1+1)·δ`. -/
theorem Adiff_one_eqv (x δ : Q') :
    Adiff x δ 1 ≈ (((1:Q')+(1:Q'))*δ) + (((1:Q')+(1:Q'))*δ) := by
  show ((2:Q')*(x+δ) + (-((2:Q')*(x+(-δ))))) ≈ (((1:Q')+(1:Q'))*δ) + (((1:Q')+(1:Q'))*δ)
  have hL : (2:Q')*(x+δ) ≈ (((1:Q')+(1:Q'))*x) + (((1:Q')+(1:Q'))*δ) := Q'.mul_add_eqv _ _ _
  have hR : (-((2:Q')*(x+(-δ)))) ≈ (-(((1:Q')+(1:Q'))*x)) + (((1:Q')+(1:Q'))*δ) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_add_eqv (2:Q') x (-δ))) ?_
    refine Q'.eqv_trans _ _ _ (Cheb.neg_add_eqv _ _) ?_
    refine Q'.add_eqv_congr_left _ _ _ ?_
    -- −((1+1)·(−δ)) ≈ (1+1)·δ
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv _ _)) ?_
    exact Q'.neg_neg_eqv _
  refine Q'.eqv_trans _ _ _ (addC _ _ _ _ hL hR) ?_
  -- (2x + 2δ) + ((−2x) + 2δ) ≈ 2δ + 2δ
  calc ((((1:Q')+(1:Q'))*x) + (((1:Q')+(1:Q'))*δ)) + ((-(((1:Q')+(1:Q'))*x)) + (((1:Q')+(1:Q'))*δ))
      ≈ ((((1:Q')+(1:Q'))*x) + (-(((1:Q')+(1:Q'))*x))) + ((((1:Q')+(1:Q'))*δ) + (((1:Q')+(1:Q'))*δ)) :=
        add_swap_inner _ _ _ _
    _ ≈ (0:Q') + ((((1:Q')+(1:Q'))*δ) + (((1:Q')+(1:Q'))*δ)) :=
        Q'.add_eqv_congr_right _ _ _ (ChebU.add_neg_self_eqv _)
    _ ≈ (((1:Q')+(1:Q'))*δ) + (((1:Q')+(1:Q'))*δ) := by rw [Q'.zero_add']; exact Q'.eqv_refl _

/-- `Sdiff x δ 1 ≈ 0`. -/
theorem Sdiff_one_eqv (x δ : Q') : Sdiff x δ 1 ≈ (0:Q') := by
  show (Ssum x δ 1 + (-(((1:Q')+(1:Q')) * Cheb.U 1 x))) ≈ (0:Q')
  rw [Cheb.U_one]
  have h2U : ((1:Q')+(1:Q')) * ((2:Q')*x) ≈ (((1:Q')+(1:Q'))*x) + (((1:Q')+(1:Q'))*x) :=
    Cheb.two_mul_eqv ((2:Q')*x)
  refine Q'.eqv_trans _ _ _
    (addC _ _ _ _ (Ssum_one_eqv x δ) (Q'.neg_eqv_congr _ _ h2U)) ?_
  exact ChebU.add_neg_self_eqv _

/-- `Arem x δ 1 ≈ 0`. -/
theorem Arem_one_eqv (x δ : Q') : Arem x δ 1 ≈ (0:Q') := by
  show (Adiff x δ 1 + (-(((1:Q')+(1:Q')) * (δ * Uderiv 1 x)))) ≈ (0:Q')
  rw [Uderiv_one]
  have hδ2 : δ * (2:Q') ≈ ((1:Q')+(1:Q'))*δ := Q'.mul_comm_eqv δ (2:Q')
  have h2U : ((1:Q')+(1:Q')) * (δ * (2:Q'))
      ≈ (((1:Q')+(1:Q'))*δ) + (((1:Q')+(1:Q'))*δ) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hδ2) (Cheb.two_mul_eqv (((1:Q')+(1:Q'))*δ))
  refine Q'.eqv_trans _ _ _
    (addC _ _ _ _ (Adiff_one_eqv x δ) (Q'.neg_eqv_congr _ _ h2U)) ?_
  exact ChebU.add_neg_self_eqv _

/-- `Ssum x δ 0 ≈ ofNat 2`. -/
theorem Ssum_zero_eqv (x δ : Q') : Ssum x δ 0 ≈ Q'.ofNat 2 := by
  show (Cheb.U 0 (x+δ) + Cheb.U 0 (x+(-δ))) ≈ Q'.ofNat 2
  rw [Cheb.U_zero, Cheb.U_zero]
  -- 1 + 1 ≈ ofNat 2
  exact ChebU.one_add_one_eqv_two

/-- `Adiff x δ 0 ≈ 0`. -/
theorem Adiff_zero_eqv (x δ : Q') : Adiff x δ 0 ≈ (0:Q') := by
  show (Cheb.U 0 (x+δ) + (-(Cheb.U 0 (x+(-δ))))) ≈ (0:Q')
  rw [Cheb.U_zero]
  exact ChebU.add_neg_self_eqv (1:Q')

/-- `Sdiff x δ 0 ≈ 0`. -/
theorem Sdiff_zero_eqv (x δ : Q') : Sdiff x δ 0 ≈ (0:Q') := by
  show ((Cheb.U 0 (x+δ) + Cheb.U 0 (x+(-δ))) + (-(((1:Q')+(1:Q')) * Cheb.U 0 x))) ≈ (0:Q')
  rw [Cheb.U_zero, Cheb.U_zero, Cheb.U_zero]
  -- (1 + 1) + (−((1+1)·1)) ≈ 0
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv _))) ?_
  exact ChebU.add_neg_self_eqv ((1:Q')+(1:Q'))

/-- `Arem x δ 0 ≈ 0`. -/
theorem Arem_zero_eqv (x δ : Q') : Arem x δ 0 ≈ (0:Q') := by
  show (Adiff x δ 0 + (-(((1:Q')+(1:Q')) * (δ * Uderiv 0 x)))) ≈ (0:Q')
  rw [Uderiv_zero]
  -- 2·(δ·0) ≈ 0
  have hz : ((1:Q')+(1:Q')) * (δ * (0:Q')) ≈ (0:Q') :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv δ)) (Q'.mul_zero_eqv _)
  refine Q'.eqv_trans _ _ _
    (addC _ _ _ _ (Adiff_zero_eqv x δ) (Q'.neg_eqv_congr _ _ hz)) ?_
  -- 0 + (−0) ≈ 0
  exact ChebU.add_neg_self_eqv (0:Q')

/-! ### The two base predicates -/

/-- `QB x δ 0` on the box. -/
theorem QB_zero (x δ : Q') (hbox : OnBox x δ) : QB x δ 0 := by
  obtain ⟨_hx1, _hxm1, hδ0, _hδ1⟩ := hbox
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Ssum 0 ≈ ofNat 2
    exact bound_of_eqv_nonneg (Ssum_zero_eqv x δ) (ofNat_nonneg 2)
  · -- Adiff 0 ≈ 0 ≈ ofNat 0 · δ
    exact bound_of_eqv_nonneg
      (Q'.eqv_trans _ _ _ (Adiff_zero_eqv x δ) (Q'.eqv_symm (ofNat_zero_mul δ)))
      (ofNat_lin_nonneg 0 hδ0)
  · -- Sdiff 0 ≈ 0 ≈ ofNat 0 · (δ·δ)
    exact bound_of_eqv_nonneg
      (Q'.eqv_trans _ _ _ (Sdiff_zero_eqv x δ) (Q'.eqv_symm (ofNat_zero_mul (δ*δ))))
      (ofNat_sq_nonneg 0 δ)
  · -- Arem 0 ≈ 0 ≈ ofNat 0 · ((δ·δ)·δ)
    exact bound_of_eqv_nonneg
      (Q'.eqv_trans _ _ _ (Arem_zero_eqv x δ) (Q'.eqv_symm (ofNat_zero_mul ((δ*δ)*δ))))
      (ofNat_cube_nonneg 0 hδ0)

/-- `QB x δ 1` on the box. -/
theorem QB_one (x δ : Q') (hbox : OnBox x δ) : QB x δ 1 := by
  obtain ⟨hx1, hxm1, hδ0, _hδ1⟩ := hbox
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Ssum 1 ≈ (1+1)x + (1+1)x, bounded by ofNat 4
    -- −ofNat 4 ≤ Ssum 1 ≤ ofNat 4
    obtain ⟨hXl, hXu⟩ := twoX_bounds x hx1 hxm1
    have hsum : (-(((1:Q')+(1:Q'))+((1:Q')+(1:Q')))) ≤ Ssum x δ 1
        ∧ Ssum x δ 1 ≤ (((1:Q')+(1:Q'))+((1:Q')+(1:Q'))) := by
      refine tighten ?_ ?_ (Q'.le_refl' _)
      · -- −(2+2) ≤ Ssum 1
        refine Q'.le_trans' _ ((-((1:Q')+(1:Q'))) + (-((1:Q')+(1:Q')))) _ ?_ ?_
        · exact Q'.le_of_eqv (Cheb.neg_add_eqv _ _)
        · refine Q'.le_trans' _ _ _ (Q'.add_le_add hXl hXl) (Q'.ge_of_eqv (Ssum_one_eqv x δ))
      · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Ssum_one_eqv x δ)) (Q'.add_le_add hXu hXu)
    -- now rewrite (2+2) ≈ ofNat 4 in the bound  (Smaj 1 = 4)
    obtain ⟨hl, hu⟩ := hsum
    refine ⟨?_, ?_⟩
    · exact Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.ge_of_eqv four_eqv)) hl
    · exact Q'.le_trans' _ _ _ hu (Q'.le_of_eqv four_eqv)
  · -- Adiff 1 ≈ (1+1)δ + (1+1)δ ; Amaj 1 = 4 ; bound ofNat 4 · δ
    -- (1+1)δ + (1+1)δ ≈ ((1+1)+(1+1))·δ ≈ ofNat 4 · δ
    have hAeq : Adiff x δ 1 ≈ Q'.ofNat 4 * δ := by
      refine Q'.eqv_trans _ _ _ (Adiff_one_eqv x δ) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Cheb.add_mul_eqv _ _ δ)) ?_
      exact Q'.mul_eqv_congr_right _ _ _ four_eqv
    exact bound_of_eqv_nonneg hAeq (ofNat_lin_nonneg 4 hδ0)
  · -- Sdiff 1 ≈ 0 ; KS 1 = 0
    exact bound_of_eqv_nonneg
      (Q'.eqv_trans _ _ _ (Sdiff_one_eqv x δ) (Q'.eqv_symm (ofNat_zero_mul (δ*δ))))
      (ofNat_sq_nonneg 0 δ)
  · -- Arem 1 ≈ 0 ; KA 1 = 0
    exact bound_of_eqv_nonneg
      (Q'.eqv_trans _ _ _ (Arem_one_eqv x δ) (Q'.eqv_symm (ofNat_zero_mul ((δ*δ)*δ))))
      (ofNat_cube_nonneg 0 hδ0)

/-! ### The inductive step -/

/-- **The two-step inductive step** `QB n → QB (n+1) → QB (n+2)` on the box. -/
theorem QB_step (x δ : Q') (hbox : OnBox x δ) (n : Nat)
    (hn : QB x δ n) (hn1 : QB x δ (n+1)) : QB x δ (n+2) := by
  obtain ⟨hx1, hxm1, hδ0, hδ1⟩ := hbox
  obtain ⟨⟨hSs0l, hSs0u⟩, ⟨hAd0l, hAd0u⟩, ⟨hSd0l, hSd0u⟩, ⟨hAr0l, hAr0u⟩⟩ := hn
  obtain ⟨⟨hSs1l, hSs1u⟩, ⟨hAd1l, hAd1u⟩, ⟨hSd1l, hSd1u⟩, ⟨hAr1l, hAr1u⟩⟩ := hn1
  -- nonneg facts
  have hofS1 : (0:Q') ≤ Q'.ofNat (Smaj (n+1)) := ofNat_nonneg _
  have hofS0 : (0:Q') ≤ Q'.ofNat (Smaj n) := ofNat_nonneg _
  have hofA1 : (0:Q') ≤ Q'.ofNat (Amaj (n+1)) * δ := ofNat_lin_nonneg _ hδ0
  have hofA0 : (0:Q') ≤ Q'.ofNat (Amaj n) * δ := ofNat_lin_nonneg _ hδ0
  have hofKS1 : (0:Q') ≤ Q'.ofNat (KS (n+1)) * (δ*δ) := ofNat_sq_nonneg _ δ
  have hofKS0 : (0:Q') ≤ Q'.ofNat (KS n) * (δ*δ) := ofNat_sq_nonneg _ δ
  have hofKA1 : (0:Q') ≤ Q'.ofNat (KA (n+1)) * ((δ*δ)*δ) := ofNat_cube_nonneg _ hδ0
  have hofKA0 : (0:Q') ≤ Q'.ofNat (KA n) * ((δ*δ)*δ) := ofNat_cube_nonneg _ hδ0
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- B1: Ssum
    obtain ⟨hl, hu⟩ := step_bound (Ssum_rec x δ n) hx1 hxm1 hδ0
      hofS1 hofS0 hofA1 hSs1l hSs1u hSs0l hSs0u hAd1l hAd1u
    rw [Smaj_succ]
    exact tighten hl hu (R_const_le (Smaj (n+1)) (Smaj n) (Amaj (n+1)) hδ0 hδ1)
  · -- B2: Adiff,  w1 = Ssum(n+1),  Bw1 = ofNat(Smaj(n+1)),  P = δ
    obtain ⟨hl, hu⟩ := step_bound (Adiff_rec x δ n) hx1 hxm1 hδ0
      hofA1 hofA0 hofS1 hAd1l hAd1u hAd0l hAd0u hSs1l hSs1u
    rw [Amaj_succ]
    refine tighten hl hu (Q'.le_of_eqv ?_)
    exact R_recon (Amaj (n+1)) (Amaj n) (Smaj (n+1))
      (Q'.eqv_refl _) (Q'.eqv_refl _) (inhom_A (Smaj (n+1)) δ)
  · -- B3: Sdiff,  w1 = Adiff(n+1),  Bw1 = ofNat(Amaj(n+1))·δ,  P = δ·δ
    obtain ⟨hl, hu⟩ := step_bound (Sdiff_rec x δ n) hx1 hxm1 hδ0
      hofKS1 hofKS0 hofA1 hSd1l hSd1u hSd0l hSd0u hAd1l hAd1u
    rw [KS_succ]
    refine tighten hl hu (Q'.le_of_eqv ?_)
    exact R_recon (KS (n+1)) (KS n) (Amaj (n+1))
      (Q'.eqv_refl _) (Q'.eqv_refl _) (inhom_S (Amaj (n+1)) δ)
  · -- B4: Arem,  w1 = Sdiff(n+1),  Bw1 = ofNat(KS(n+1))·(δ·δ),  P = (δ·δ)·δ
    obtain ⟨hl, hu⟩ := step_bound (Arem_rec x δ n) hx1 hxm1 hδ0
      hofKA1 hofKA0 hofKS1 hAr1l hAr1u hAr0l hAr0u hSd1l hSd1u
    rw [KA_succ]
    refine tighten hl hu (Q'.le_of_eqv ?_)
    exact R_recon (KA (n+1)) (KA n) (KS (n+1))
      (Q'.eqv_refl _) (Q'.eqv_refl _) (inhom_KS (KS (n+1)) δ)

/-- `QB x δ n` for all `n` on the box (two-step induction). -/
theorem QB_all (x δ : Q') (hbox : OnBox x δ) : ∀ n, QB x δ n ∧ QB x δ (n+1) := by
  intro n
  induction n with
  | zero => exact ⟨QB_zero x δ hbox, QB_one x δ hbox⟩
  | succ k ih =>
      obtain ⟨hk, hk1⟩ := ih
      exact ⟨hk1, QB_step x δ hbox k hk hk1⟩

/-! ## 5. The two Markov-modulus obligations, discharged unconditionally -/

/-- `−(−a) ≤ b` rewritten: from `−a ≤ v` get `−v ≤ a`. -/
theorem neg_flip {a v : Q'} (h : (-a) ≤ v) : (-v) ≤ a :=
  Q'.le_trans' _ (-(-a)) _ (Q'.neg_le_neg h) (Q'.le_of_eqv (Q'.neg_neg_eqv a))

/-- **The symmetric (δ²) cofactor modulus, for every `n`**:
`SdiffQuadModulus n (KS n)`, UNCONDITIONAL. -/
theorem sdiffQuadModulus_holds (n : Nat) : SdiffQuadModulus n (KS n) := by
  intro x δ hbox
  obtain ⟨_, _, ⟨hl, hu⟩, _⟩ := (QB_all x δ hbox n).1
  exact ⟨hu, neg_flip hl⟩

/-- **The antisymmetric (δ³) cofactor modulus, for every `n`**:
`AdiffCubeModulus n (KA n)`, UNCONDITIONAL. -/
theorem adiffCubeModulus_holds (n : Nat) : AdiffCubeModulus n (KA n) := by
  intro x δ hbox
  obtain ⟨_, _, _, ⟨hl, hu⟩⟩ := (QB_all x δ hbox n).1
  -- Arem x δ n = Adiff + (−(2·(δ·U'_n)))  (definitional)
  exact ⟨hu, neg_flip hl⟩

/-! ## 6. The assembled bracket Taylor bounds, UNCONDITIONAL

Composing the moduli with the proved reductions `BracketQuadBound_of_moduli` and
`BracketCubeBound_of_moduli`. -/

/-- **The symmetric bracket bound, UNCONDITIONAL.**
`BracketQuadBound e he (KS (e−1) + KS (e+1))`. -/
theorem bracketQuadBound_holds (e : Nat) (he : 0 < e) :
    BracketQuadBound e he (KS (e-1) + KS (e+1)) :=
  BracketQuadBound_of_moduli e he (KS (e-1)) (KS (e+1))
    (sdiffQuadModulus_holds (e-1)) (sdiffQuadModulus_holds (e+1))

/-- **The antisymmetric bracket bound, UNCONDITIONAL.**
`BracketCubeBound e he (KA (e−1) + KA (e+1))`. -/
theorem bracketCubeBound_holds (e : Nat) (he : 0 < e) :
    BracketCubeBound e he (KA (e-1) + KA (e+1)) :=
  BracketCubeBound_of_moduli e he (KA (e-1)) (KA (e+1))
    (adiffCubeModulus_holds (e-1)) (adiffCubeModulus_holds (e+1))

end YMGap.Continuum.ChebMarkovModulus

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebMarkovModulus.Sdiff_rec
#print axioms YMGap.Continuum.ChebMarkovModulus.Arem_rec
#print axioms YMGap.Continuum.ChebMarkovModulus.step_bound
#print axioms YMGap.Continuum.ChebMarkovModulus.QB_zero
#print axioms YMGap.Continuum.ChebMarkovModulus.QB_one
#print axioms YMGap.Continuum.ChebMarkovModulus.QB_step
#print axioms YMGap.Continuum.ChebMarkovModulus.QB_all
#print axioms YMGap.Continuum.ChebMarkovModulus.sdiffQuadModulus_holds
#print axioms YMGap.Continuum.ChebMarkovModulus.adiffCubeModulus_holds
#print axioms YMGap.Continuum.ChebMarkovModulus.bracketQuadBound_holds
#print axioms YMGap.Continuum.ChebMarkovModulus.bracketCubeBound_holds
