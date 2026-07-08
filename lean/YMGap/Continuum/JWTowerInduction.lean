/-
**Track A2-Wenzl (tower) — the general Jones–Wenzl tower one genuine rung past
the elementary ½-recoupling: the ∀-n Wenzl coefficient/trace laws + the concrete
faithful `TL₃` algebra and the genuine `p₃` projector.**

`TemperleyLiebRecoupling.lean` built the RATIONAL Temperley–Lieb substrate and
CLOSED the elementary `n = 2` ½-recoupling (a complete orthogonal pair of rational
Jones–Wenzl idempotents `jw2`, `p0`, trace-faithful to the SU(2) channel
dimensions).  It named the general tower coherence `JWTowerCoherence` as the
UNINHABITED residual (the diagrammatic induction over the growing non-crossing
matching basis `TL n`).  This module advances the tower on two honest fronts:

  1. **The ∀-n Wenzl / Chebyshev laws (genuine `∀ n`, not a decide list).**  The
     Jones–Wenzl coefficient recursion `c_{n+1}·Δ_{n+1} = Δ_n` and the loop-value
     recurrence `Δ_{n+2}+Δ_n = δ·Δ_{n+1}` are proved for EVERY `n` (the
     `wenzl_coeff_rec_low` decide-list at `n = 0,1,2` becoming a real universal
     statement).  This is the ∀-spins arithmetic backbone of the whole tower.

  2. **The genuine `n = 3` rung: the concrete faithful `TL₃` algebra + the real
     Jones–Wenzl projector `p₃`.**  `TL₃` is the 5-dimensional
     non-crossing-matching algebra `{1, e₁, e₂, u = e₁e₂, v = e₂e₁}` with the
     genuine loop value `δ = 2`; we verify the DEFINING Temperley–Lieb relations
     (`e₁² = δe₁`, `e₁e₂e₁ = e₁`, associativity spot-checks), build `p₃` by the
     ACTUAL Wenzl recursion `p₃ = p₂ − (Δ₁/Δ₂)·p₂ e₂ p₂ = p₂ − (2/3)·p₂ e₂ p₂`,
     and PROVE its three DEFINING projector properties: idempotence `p₃² = p₃`,
     the absorbing/killing property `p₃ e₁ = p₃ e₂ = 0`, and the Markov trace
     `tr(p₃) = Δ₃ = 4`.  This is a REAL second rung of the Jones–Wenzl tower
     (previously only `n = 2` existed), radical-free.

# Honest scope (AGENTS.md Rule 6)

PROVED here (genuine, rational, axiom-clean):
  * the ∀-n Wenzl coefficient law and the ∀-n loop-value recurrence — the tower's
    universal arithmetic (real `∀`, by direct computation, NOT a finite decide);
  * the concrete faithful `TL₃` algebra (defining relations verified) and the
    genuine `p₃` Jones–Wenzl projector with ALL THREE defining properties
    (idempotence + double killing + trace `= Δ₃`).

NAMED-open (NOT faked, NO inhabitant — the genuine residual is UNCHANGED):
  * the ∀-spins projector idempotence `p_n² = p_n` for ALL `n` is the induction on
    the Wenzl recursion over the growing `TL n` basis (`JWTowerCoherence`).  Here
    the base rungs `n = 2` (`TemperleyLiebRecoupling`) and `n = 3` (this module)
    are DISCHARGED as concrete faithful computations, and the ∀-n arithmetic
    (coefficient/trace laws) is PROVED; the residual is precisely the diagrammatic
    `n ↦ n+1` step at the algebra level (a growing Catalan-dimensional basis).

HONEST verdict on the literal A2 target: the field
`PartitionBeyondTree.SixJRecoupling.biedenharn_elliott` is PROVABLY UNINHABITED
(`SixJRecouplingProgress.sixjRecoupling_uninhabited`, a `D = 0` truncation bug),
and its corrected rational shadow `RacahProb` is ALREADY INHABITED
(`RacahInhabit.racahRP`).  The genuine remaining A2 content
(`PentagonRelation.PentagonNumericCore` + the nonlinear pentagon) is
IRRATIONAL-cored (the signed `{6j}` is irrational), so the JW/TL rational route
delivers exactly the tower's rational backbone (the coefficient/trace laws and the
concrete rungs), not an all-spins closure.  The Clay YM mass gap stays OPEN.

# Constructive contract (AGENTS.md Rules 1/6/8)

Mathlib-free; `Q'`/`Nat`/`Int` core only.  No `Classical.*`, no `Real`, no `√`,
no `native_decide` (only `decide` on decidable `Q'`/`Nat` facts and direct `Int`
arithmetic).  No `sorry`/`admit`/new `axiom`.  All witnesses are `Type`-level
data; the ∀-spins projector induction stays a NAMED obligation, never faked.
`#print axioms` gated (permitted: `propext`/`Quot.sound`).
-/

import YMGap.Continuum.TemperleyLiebRecoupling

namespace YMGap.Continuum.JWTowerInduction

open YMGap.Constructive
open YMGap.Continuum.TemperleyLiebRecoupling

/-! ## 1. The ∀-n Wenzl / Chebyshev laws (genuine universal, not a decide list). -/

/-- **The Jones–Wenzl coefficient recursion, for ALL `n`** (upgrading the
`wenzl_coeff_rec_low` decide-list at `n = 0,1,2` to a genuine universal).  The
coefficient `c_{n+1} = Δ_n/Δ_{n+1} = (n+1)/(n+2)` times the loop value
`Δ_{n+1} = n+2` recovers `Δ_n = n+1`:

    c_{n+1} · Δ_{n+1}  ≃  Δ_n     for every `n`.

This is the ∀-spins arithmetic backbone of the Wenzl recursion — the tower's
trace-normalisation identity at every rung.  Proved by direct `Int` computation
(the cross-multiplied `eqv` reduces to `(n+1)(n+2)·1 = (n+1)(n+2)`), NOT a finite
`decide`. -/
theorem wenzl_coeff_rec_all (n : Nat) :
    (wenzlCoeff (n + 1) * Q'.ofNat (dimN (n + 1))).eqv (Q'.ofNat (dimN n)) := by
  -- `eqv p q` is `p.num * (q.den:Int) = q.num * (p.den:Int)` on `Int`.
  -- Product numerator `= (n+1)*(n+2)`, product denominator `= n+2`; RHS `= (n+1)/1`.
  have hden : (wenzlCoeff (n + 1) * Q'.ofNat (dimN (n + 1))).den = n + 1 + 1 := by
    show (n + 1 + 1) * (0 + 1) - 1 + 1 = n + 1 + 1
    omega
  unfold Q'.eqv
  have hnum : (wenzlCoeff (n + 1) * Q'.ofNat (dimN (n + 1))).num
      = Int.ofNat (n + 1) * Int.ofNat (n + 1 + 1) := rfl
  rw [hnum, hden]
  show (Int.ofNat (n + 1) * Int.ofNat (n + 1 + 1)) * (1 : Int)
      = Int.ofNat (n + 1) * Int.ofNat (n + 1 + 1)
  rw [Int.mul_one]

/-- **The loop-value / Chebyshev recurrence over `Q'`, for ALL `n`.**  The `Q'`
image of the Jones–Wenzl loop values satisfies the defining second-order
recurrence `Δ_{n+2} + Δ_n ≃ δ·Δ_{n+1}` at `δ = 2` (the `Nat` identity
`chebyshev_rec` lifted to the rational trace level, where the Markov traces
live).  Genuine `∀ n`. -/
theorem wenzl_trace_recurrence (n : Nat) :
    (Q'.ofNat (dimN (n + 2)) + Q'.ofNat (dimN n)).eqv
      (delta * Q'.ofNat (dimN (n + 1))) := by
  -- `dimN k = k+1`, `delta = 2`; both sides are integers with denominator 1.
  -- State the goal with the `Nat.cast` coercion `↑` (defeq to the `Q'.num`
  -- `Int.ofNat` values) so that `omega` can see through the casts.
  show (((n + 2 + 1 : Nat) : Int) * (1 : Int) + ((n + 1 : Nat) : Int) * (1 : Int)) * (1 : Int)
      = ((2 : Int) * ((n + 1 + 1 : Nat) : Int)) * (1 : Int)
  rw [Int.mul_one, Int.mul_one, Int.mul_one, Int.mul_one]
  -- `(n+3) + (n+1) = 2*(n+2)`; `omega` handles the `↑` casts and `2·(n+2)`.
  omega

/-! ## 2. The concrete faithful `TL₃` algebra (5 non-crossing matchings, δ = 2).

Basis `{1, e₁, e₂, u = e₁e₂, v = e₂e₁}` (Catalan(3) = 5).  An element is the tuple
`c₁·1 + cₑ₁·e₁ + cₑ₂·e₂ + c_u·u + c_v·v`.  Multiplication is the `Q'`-bilinear
extension of the diagram concatenation table generated by the defining relations
`e_i² = δ·e_i`, `e₁e₂e₁ = e₁`, `e₂e₁e₂ = e₂` (loop value `δ = 2`). -/

/-- A `TL₃` element `c₁·1 + cₑ₁·e₁ + cₑ₂·e₂ + c_u·u + c_v·v`. -/
structure TL3 where
  c1  : Q'
  ce1 : Q'
  ce2 : Q'
  cu  : Q'
  cv  : Q'

/-- The zero element. -/
def tl3zero : TL3 := ⟨0, 0, 0, 0, 0⟩
/-- The identity diagram `1`. -/
def tl3id : TL3 := ⟨1, 0, 0, 0, 0⟩
/-- The generator `e₁`. -/
def tl3e1 : TL3 := ⟨0, 1, 0, 0, 0⟩
/-- The generator `e₂`. -/
def tl3e2 : TL3 := ⟨0, 0, 1, 0, 0⟩
/-- The diagram `u = e₁e₂`. -/
def tl3u : TL3 := ⟨0, 0, 0, 1, 0⟩
/-- The diagram `v = e₂e₁`. -/
def tl3v : TL3 := ⟨0, 0, 0, 0, 1⟩

/-- **Diagram concatenation on `TL₃`** — the `Q'`-bilinear extension of the basis
product table (`δ = 2`):

    1·x = x·1 = x,  e₁² = δe₁,  e₂² = δe₂,  e₁e₂ = u,  e₂e₁ = v,
    e₁u = δu, e₁v = e₁, e₂u = e₂, e₂v = δv, u e₁ = e₁, u e₂ = δu,
    u u = u, u v = δe₁, v e₁ = δv, v e₂ = e₂, v u = δe₂, v v = v.

Each output coordinate collects every basis pair landing on that basis element. -/
def tl3mul (x y : TL3) : TL3 :=
  let a0 := x.c1; let a1 := x.ce1; let a2 := x.ce2; let a3 := x.cu; let a4 := x.cv
  let b0 := y.c1; let b1 := y.ce1; let b2 := y.ce2; let b3 := y.cu; let b4 := y.cv
  { c1  := a0 * b0
    ce1 := a0 * b1 + a1 * b0 + delta * (a1 * b1) + a1 * b4 + a3 * b1 + delta * (a3 * b4)
    ce2 := a0 * b2 + a2 * b0 + delta * (a2 * b2) + a2 * b3 + a4 * b2 + delta * (a4 * b3)
    cu  := a0 * b3 + a3 * b0 + a1 * b2 + delta * (a1 * b3) + delta * (a3 * b2) + a3 * b3
    cv  := a0 * b4 + a4 * b0 + a2 * b1 + delta * (a2 * b4) + delta * (a4 * b1) + a4 * b4 }

/-- Scalar multiple `s·x`. -/
def tl3smul (s : Q') (x : TL3) : TL3 :=
  ⟨s * x.c1, s * x.ce1, s * x.ce2, s * x.cu, s * x.cv⟩

/-- Difference `x − y`. -/
def tl3sub (x y : TL3) : TL3 :=
  ⟨x.c1 - y.c1, x.ce1 - y.ce1, x.ce2 - y.ce2, x.cu - y.cu, x.cv - y.cv⟩

/-- Componentwise semantic equality (decidable). -/
def tl3eqv (x y : TL3) : Prop :=
  x.c1.eqv y.c1 ∧ x.ce1.eqv y.ce1 ∧ x.ce2.eqv y.ce2 ∧ x.cu.eqv y.cu ∧ x.cv.eqv y.cv

instance (x y : TL3) : Decidable (tl3eqv x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-! ### The defining Temperley–Lieb relations of `TL₃` hold (faithfulness). -/

/-- `e₁² = δ·e₁` and `e₂² = δ·e₂` (the loop relation, `δ = 2`). -/
theorem tl3_loop :
    tl3eqv (tl3mul tl3e1 tl3e1) (tl3smul delta tl3e1) ∧
    tl3eqv (tl3mul tl3e2 tl3e2) (tl3smul delta tl3e2) := by
  refine ⟨by decide, by decide⟩

/-- `e₁e₂ = u`, `e₂e₁ = v` (the composite generators). -/
theorem tl3_compose :
    tl3eqv (tl3mul tl3e1 tl3e2) tl3u ∧ tl3eqv (tl3mul tl3e2 tl3e1) tl3v := by
  refine ⟨by decide, by decide⟩

/-- **The braid/isotopy relations `e₁e₂e₁ = e₁` and `e₂e₁e₂ = e₂`** — the defining
`TL₃` relations that separate it from the free two-generator algebra.  Verified
in the concrete table. -/
theorem tl3_braid :
    tl3eqv (tl3mul (tl3mul tl3e1 tl3e2) tl3e1) tl3e1 ∧
    tl3eqv (tl3mul (tl3mul tl3e2 tl3e1) tl3e2) tl3e2 := by
  refine ⟨by decide, by decide⟩

/-- **Associativity spot-checks** on the generators (the concatenation is a
genuine associative product): `(e₁e₂)e₁ = e₁(e₂e₁)` and `(e₁e₂)(e₁e₂) = e₁e₂`. -/
theorem tl3_assoc_spot :
    tl3eqv (tl3mul (tl3mul tl3e1 tl3e2) tl3e1) (tl3mul tl3e1 (tl3mul tl3e2 tl3e1)) ∧
    tl3eqv (tl3mul (tl3mul tl3e1 tl3e2) (tl3mul tl3e1 tl3e2)) (tl3mul tl3e1 tl3e2) := by
  refine ⟨by decide, by decide⟩

/-! ## 3. The genuine Jones–Wenzl projector `p₃` by the Wenzl recursion. -/

/-- The Jones–Wenzl projector `p₂ = 1 − (1/δ)e₁ = 1 − (1/2)e₁` embedded in `TL₃`
(acting on the first two strands, strand 3 idle). -/
def p2in3 : TL3 := ⟨1, Q'.mkPos (-1) 2 (by decide), 0, 0, 0⟩

/-- The Wenzl recursion coefficient `Δ₁/Δ₂ = 2/3` (`= wenzlCoeff 2`). -/
def c2 : Q' := Q'.mkPos 2 3 (by decide)

/-- **The Jones–Wenzl projector `p₃`** built by the ACTUAL Wenzl recursion
`p₃ = p₂ − (Δ₁/Δ₂)·p₂ e₂ p₂ = p₂ − (2/3)·p₂ e₂ p₂`.  A genuine element of the
concrete `TL₃` algebra. -/
def p3 : TL3 :=
  tl3sub p2in3 (tl3smul c2 (tl3mul (tl3mul p2in3 tl3e2) p2in3))

/-- **The explicit closed form** `p₃ = 1 − (2/3)e₁ − (2/3)e₂ + (1/3)u + (1/3)v`
(a rational combination, radical-free) — the value the Wenzl recursion produces. -/
theorem p3_value :
    tl3eqv p3
      ⟨1, Q'.mkPos (-2) 3 (by decide), Q'.mkPos (-2) 3 (by decide),
        Q'.mkPos 1 3 (by decide), Q'.mkPos 1 3 (by decide)⟩ := by
  decide

/-- **`p₃` is idempotent** (`p₃² = p₃`) — the defining Jones–Wenzl property at the
`n = 3` rung, from the ACTUAL Wenzl recursion, exact over `Q'`, no radical. -/
theorem p3_idem : tl3eqv (tl3mul p3 p3) p3 := by decide

/-- **`p₃` kills `e₁`** (`p₃ e₁ = 0`) — the absorbing property `p_n e_i = 0`
(`i < n`) at `i = 1`. -/
theorem p3_kills_e1 : tl3eqv (tl3mul p3 tl3e1) tl3zero := by decide

/-- **`p₃` kills `e₂`** (`p₃ e₂ = 0`) — the absorbing property at `i = 2`.
Together with `p3_kills_e1`, `p₃` annihilates EVERY Temperley–Lieb generator of
`TL₃` (the full defining absorbing property of the top Jones–Wenzl idempotent). -/
theorem p3_kills_e2 : tl3eqv (tl3mul p3 tl3e2) tl3zero := by decide

/-! ### The Markov trace of `p₃` recovers the physical channel dimension. -/

/-- The Markov trace on `TL₃` (close all three strands): `tr(1) = δ³ = 8`,
`tr(e_i) = δ² = 4`, `tr(u) = tr(v) = δ = 2` (loop counts `3,2,2,1,1`). -/
def mtr3 (x : TL3) : Q' :=
  x.c1 * (delta * (delta * delta)) + x.ce1 * (delta * delta) + x.ce2 * (delta * delta)
    + x.cu * delta + x.cv * delta

/-- **`tr(p₃) = Δ₃ = 4 = dim χ₃`** (the spin-3/2 channel dimension) — the
Jones–Wenzl projector at the `n = 3` rung is trace-faithful to the SU(2) channel
dimension, exactly as `Δ_n = n+1` predicts. -/
theorem mtr3_p3 : (mtr3 p3).eqv (Q'.ofNat (dimN 3)) := by decide

/-- The Markov trace of `p₂` inside `TL₃` is `δ·Δ₂ = 2·3 = 6` (the idle third
strand contributes one extra loop `δ`), confirming `mtr3` is the genuine
three-strand trace, distinct from the two-strand `mtr`. -/
theorem mtr3_p2 : (mtr3 p2in3).eqv (Q'.ofNat 6) := by decide

/-! ## 4. Non-vacuity: `p₃` is a genuinely NEW rung (not `p₂` in disguise). -/

/-- **`p₃ ≠ p₂`** at the `TL₃` level: `p₃` has a nonzero `e₂` coordinate
(`−2/3`) whereas `p₂` (embedded) has `e₂`-coordinate `0`.  So the `n = 3` rung is
genuinely distinct — the Wenzl recursion produced new data, not a relabelling. -/
theorem p3_ne_p2 : ¬ tl3eqv p3 p2in3 := by decide

/-- **The trace jump `tr(p₃) = 4 ≠ 6 = tr(p₂)`** in `TL₃`: the top idempotent
strictly refines the channel, dropping the trace from `δ·Δ₂` to `Δ₃`.  Non-vacuous
evidence that `p₃` carries the genuine `n = 3` Jones–Wenzl content. -/
theorem mtr3_jump : ¬ (mtr3 p3).eqv (mtr3 p2in3) := by decide

/-! ## 5. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED here (genuine, rational, axiom-clean — `Q'`/`Nat`/`Int`, NO radicals):

  * `wenzl_coeff_rec_all` — the Jones–Wenzl coefficient recursion
    `c_{n+1}·Δ_{n+1} ≃ Δ_n` for ALL `n` (real universal, not a decide list);
  * `wenzl_trace_recurrence` — the loop-value/Chebyshev recurrence over `Q'` for
    ALL `n` (`Δ_{n+2}+Δ_n ≃ δ·Δ_{n+1}`), the Markov-trace backbone;
  * `tl3_loop`, `tl3_compose`, `tl3_braid`, `tl3_assoc_spot` — the concrete
    faithful `TL₃` algebra (defining Temperley–Lieb relations + associativity);
  * `p3_value`, `p3_idem`, `p3_kills_e1`, `p3_kills_e2`, `mtr3_p3` — the genuine
    `n = 3` Jones–Wenzl projector with ALL THREE defining properties (idempotence,
    double killing, trace `= Δ₃`), a REAL second rung of the tower;
  * `p3_ne_p2`, `mtr3_jump` — non-vacuity (the rung is genuinely new).

NAMED-open (NOT faked, NO inhabitant — the residual is UNCHANGED):

  * `TemperleyLiebRecoupling.JWTowerCoherence` — the ∀-spins projector idempotence
    `p_n² = p_n` as the induction on the Wenzl recursion over the growing
    Catalan-dimensional `TL n` basis.  The base rungs `n = 2` and `n = 3` are now
    DISCHARGED as concrete faithful computations and the ∀-n arithmetic is PROVED;
    the residual is precisely the diagrammatic `n ↦ n+1` algebra step.

This is a genuine advance on the Jones–Wenzl tower (the ∀-n arithmetic + a real
new `n = 3` rung), radical-free.  The literal A2 field
`SixJRecoupling.biedenharn_elliott` is a PROVED-uninhabited bug and its genuine
content is irrational-cored; this module does NOT close the ∀-spins recoupling,
NOT a continuum limit, and NOT a 4D Yang–Mills mass gap.  The Clay problem stays
OPEN. -/

end YMGap.Continuum.JWTowerInduction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.JWTowerInduction.wenzl_coeff_rec_all
#print axioms YMGap.Continuum.JWTowerInduction.wenzl_trace_recurrence
#print axioms YMGap.Continuum.JWTowerInduction.tl3_braid
#print axioms YMGap.Continuum.JWTowerInduction.tl3_assoc_spot
#print axioms YMGap.Continuum.JWTowerInduction.p3_value
#print axioms YMGap.Continuum.JWTowerInduction.p3_idem
#print axioms YMGap.Continuum.JWTowerInduction.p3_kills_e1
#print axioms YMGap.Continuum.JWTowerInduction.p3_kills_e2
#print axioms YMGap.Continuum.JWTowerInduction.mtr3_p3
#print axioms YMGap.Continuum.JWTowerInduction.p3_ne_p2
#print axioms YMGap.Continuum.JWTowerInduction.mtr3_jump
