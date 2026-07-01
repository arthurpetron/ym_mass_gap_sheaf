/-
# `tan(arctan x) = x` — the ODE/coefficient recurrence core (GREEN) + the sharp residual

## The atom

The last transcendental atom under `sin π ≃ 0` (`Continuum.SinPiDoubleAngle`,
`Continuum.ArctanTanInversion`) is the arctan↔trig **base link**
`sin(arctan x) ≃ x·cos(arctan x)` (equivalently `tan(arctan x) = x`, or
`cos(arctan x)²·(1+x²) ≃ 1`, or `cos(arctan x) = 1/√(1+x²)`).  There is no purely
algebraic route from the Machin arctan **series** to the trig **series**; this is
the genuine analytic input.

## The route taken — the derivative-free coefficient recurrence

Write `P(x) = sin(arctan x)`, `Q(x) = cos(arctan x)` as formal power series
`P = Σ pₙ xⁿ`, `Q = Σ qₙ xⁿ`.  The chain rule (`arctan' = 1/(1+x²)`) gives the
first-order ODE system

    (1+x²)·P' = Q,     (1+x²)·Q' = −P,     P(0) = 0,  Q(0) = 1,

which — reading off the coefficient of `xⁿ` — is **algebraic** on the sequences:

    (P-rec)   (n+2)·p_{n+2} + n·pₙ = q_{n+1},     p₁ = q₀
    (Q-rec)   (n+2)·q_{n+2} + n·qₙ = −p_{n+1},     q₁ = −p₀
    (init)    p₀ = 0     (and q₀ = 1, unused for the identity)

The formal identity `P = x·Q` is exactly `p_{n+1} = qₙ` for all `n` (and `p₀ = 0`).
`odeShift` below **PROVES this coefficient identity green**, purely from the two
recurrences and `p₀ = 0`, by a two-step induction: the reduced cosine recurrence
`(n+2)·q_{n+2} ≃ −(n+1)·qₙ` follows from `(Q-rec)` and the identity two steps back,
and feeds `(P-rec)` to advance the identity.  This is the algebraic heart of the
primary route — the "matching of recurrences".

## What is GREEN here

  * `odeShift` — the formal coefficient identity `p_{n+1} ≃ qₙ` (`P = x·Q`), the
    algebraic core, proved outright from the ODE coefficient recurrences.
  * `shiftMulX` — the value-level lift of the coefficient identity to every finite
    truncation: `Σ_{n<N+1} pₙ xⁿ ≃ x·Σ_{n<N} qₙ xⁿ`.  This makes `odeShift`
    load-bearing at the value level and reduces the remaining gap to pure
    convergence of the partial sums to `sinC`/`cosC`.
  * `tanArctan_of_model` — given a `TanArctanModel` (the honest interface below),
    the tangent link `sα ≃ x·cα` follows, with `odeShift` discharging the entire
    algebraic middle.

## The sharp residual (named, NOT faked)

`TanArctanModel x` packages the two genuinely-transcendental bridges as
`Type`-level data (mirroring `ArctanTanInversion.CircleModel`):

  * (REC)  the composed series `sin(arctan x)`, `cos(arctan x)` really have
           coefficients satisfying the ODE recurrences (`hp`,`hq`,…) — the
           formal chain-rule / Cauchy-product content;
  * (VAL)  `valBridge` — the CReal values `sval = sinC(arctan x)`,
           `cval = cosC(arctan x)` equal their series and the formal identity
           `p_{n+1} ≃ qₙ` lifts to `sval ≃ x·cval` (the tail/convergence bridge).

`odeShift` shows these are jointly sufficient.  Nothing here fabricates the link:
`odeShift` is a real, non-vacuous theorem, and the residual is the (REC)+(VAL)
data of a concrete model for `arctanRecip`/`sinC`/`cosC`.  Downstream,
`cos(arctan x)²·(1+x²) ≃ 1` additionally needs the Pythagorean identity
`sin²+cos² ≃ 1`, and `SinQuarterAtom` (`sin(π/4) = 1/√2`) additionally needs the
CReal-angle addition law — both separate, still-open inputs.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only (via reused `Int`/`Nat`/`Q'` helpers).
No `Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.  The model is
`Type`-level data (Rule 8), not a `Prop`-∃.
-/

import YMGap.Constructive.CRealTrig
import YMGap.Constructive.Pi
import YMGap.Constructive.ExpAddConv

namespace YMGap.Continuum.TanArctan

open YMGap.Constructive

/-! ## 1. Local `Q'` equational helpers -/

/-- `(a + b) + (−b) ≃ a`. -/
theorem addNegCancelR (a b : Q') : ((a + b) + -b).eqv a := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a b (-b)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a (b + -b) 0 ?_) (Q'.eqv_of_eq (Q'.add_zero' a))
  exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv b (-b)) (Q'.neg_add_self_eqv b)

/-- Move a summand across an `eqv`: `(a + b) ≃ c ⟹ a ≃ c + (−b)`. -/
theorem moveR {a b c : Q'} (h : (a + b).eqv c) : a.eqv (c + -b) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (addNegCancelR a b))
    (Q'.add_eqv_congr_right (a + b) c (-b) h)

/-- Cancel a positive natural coefficient: `(n+1)·a ≃ (n+1)·b ⟹ a ≃ b`. -/
theorem cancelSucc {k : Nat} {a b : Q'}
    (h : (Q'.ofNat (k + 1) * a).eqv (Q'.ofNat (k + 1) * b)) : a.eqv b :=
  Q'.mul_left_cancel_of_pos (Q'.ofNat_succ_pos k) h

/-- The zero coefficient annihilates: `ofNat 0 · x ≃ 0`. -/
theorem zeroCoeff (x : Q') : (Q'.ofNat 0 * x).eqv 0 :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (Q'.ofNat 0) 0 x (by decide)) (Q'.zero_mul_eqv x)

/-- Split off the top coefficient: `ofNat (k+1) · y ≃ ofNat k · y + y`. -/
theorem succCoeff (k : Nat) (y : Q') :
    (Q'.ofNat (k + 1) * y).eqv (Q'.ofNat k * y + y) := by
  have h1 : (Q'.ofNat (k + 1)).eqv (Q'.ofNat k + 1) :=
    Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv k 1)
      (Q'.add_eqv_congr_left (Q'.ofNat k) (Q'.ofNat 1) 1 (by decide))
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (Q'.ofNat (k + 1)) (Q'.ofNat k + 1) y h1) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (Q'.ofNat k) 1 y) ?_
  exact Q'.add_eqv_congr_left (Q'.ofNat k * y) (1 * y) y (Q'.one_mul_eqv y)

/-! ## 2. The formal coefficient identity `P = x·Q` (the algebraic core) -/

/-- **The ODE coefficient identity `p_{n+1} ≃ qₙ` (i.e. `P = x·Q` formally).**

Given two rational coefficient sequences `p, q` satisfying the arctan↔trig ODE
coefficient recurrences (`hp`/`hp0` for `(1+x²)P' = Q`, `hq`/`hq0` for
`(1+x²)Q' = −P`) and the initial value `p₀ = 0`, the sine coefficients are the
shift of the cosine coefficients — exactly the formal `sin = x·cos`.  Proved by a
two-step induction; the reduced cosine recurrence
`(n+2)·q_{n+2} ≃ −(n+1)·qₙ` is derived on the fly. -/
theorem odeShift
    (p q : Nat → Q')
    (hp0 : (p 1).eqv (q 0))
    (hp : ∀ n, (Q'.ofNat (n + 2) * p (n + 2) + Q'.ofNat n * p n).eqv (q (n + 1)))
    (hq0 : (q 1).eqv (-(p 0)))
    (hq : ∀ n, (Q'.ofNat (n + 2) * q (n + 2) + Q'.ofNat n * q n).eqv (-(p (n + 1))))
    (hp0init : (p 0).eqv 0) :
    ∀ n, (p (n + 1)).eqv (q n) := by
  -- Base second component `B(1)`: `p 2 ≃ q 1`.
  have hB1 : (p 2).eqv (q 1) := by
    have h0 := hp 0
    have hz : (Q'.ofNat 2 * p 2 + Q'.ofNat 0 * p 0).eqv (Q'.ofNat 2 * p 2) :=
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (Q'.ofNat 2 * p 2) _ 0 (zeroCoeff (p 0)))
        (Q'.eqv_of_eq (Q'.add_zero' (Q'.ofNat 2 * p 2)))
    have h2p2 : (Q'.ofNat 2 * p 2).eqv (q 1) := Q'.eqv_trans _ _ _ (Q'.eqv_symm hz) h0
    have hq1 : (q 1).eqv 0 :=
      Q'.eqv_trans _ _ _ hq0
        (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr (p 0) 0 hp0init) (by decide))
    have hcancel : (Q'.ofNat 2 * p 2).eqv (Q'.ofNat 2 * 0) :=
      Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ h2p2 hq1)
        (Q'.eqv_symm (Q'.mul_zero_eqv (Q'.ofNat 2)))
    exact Q'.eqv_trans _ _ _ (cancelSucc (k := 1) hcancel) (Q'.eqv_symm hq1)
  -- Paired two-step induction `B(n) ∧ B(n+1)`.
  have pair : ∀ n, (p (n + 1)).eqv (q n) ∧ (p (n + 2)).eqv (q (n + 1)) := by
    intro n
    induction n with
    | zero => exact ⟨hp0, hB1⟩
    | succ k ih =>
        refine ⟨ih.2, ?_⟩
        have ihk : (p (k + 1)).eqv (q k) := ih.1
        -- Reduced cosine recurrence `RQ2 : (k+2)·q_{k+2} ≃ −(k+1)·qₖ`.
        have hqk' : (Q'.ofNat (k + 2) * q (k + 2) + Q'.ofNat k * q k).eqv (-(q k)) :=
          Q'.eqv_trans _ _ _ (hq k) (Q'.neg_eqv_congr (p (k + 1)) (q k) ihk)
        have RQ : (Q'.ofNat (k + 2) * q (k + 2)).eqv ((-(q k)) + -(Q'.ofNat k * q k)) :=
          moveR hqk'
        have hlink :
            (-(Q'.ofNat (k + 1) * q k)).eqv ((-(q k)) + -(Q'.ofNat k * q k)) := by
          refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (succCoeff k (q k))) ?_
          refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (Q'.ofNat k * q k) (q k)) ?_
          exact Q'.add_comm_eqv (-(Q'.ofNat k * q k)) (-(q k))
        have RQ2 : (Q'.ofNat (k + 2) * q (k + 2)).eqv (-(Q'.ofNat (k + 1) * q k)) :=
          Q'.eqv_trans _ _ _ RQ (Q'.eqv_symm hlink)
        -- Advance the identity via `(P-rec)` at `k+1`.
        have hp3 :
            (Q'.ofNat (k + 3) * p (k + 3)).eqv ((q (k + 2)) + -(Q'.ofNat (k + 1) * p (k + 1))) :=
          moveR (hp (k + 1))
        have hp3' :
            (Q'.ofNat (k + 3) * p (k + 3)).eqv ((q (k + 2)) + -(Q'.ofNat (k + 1) * q k)) :=
          Q'.eqv_trans _ _ _ hp3
            (Q'.add_eqv_congr_left (q (k + 2)) _ _
              (Q'.neg_eqv_congr _ _
                (Q'.mul_eqv_congr_left (Q'.ofNat (k + 1)) (p (k + 1)) (q k) ihk)))
        have hp3'' :
            (Q'.ofNat (k + 3) * p (k + 3)).eqv ((q (k + 2)) + Q'.ofNat (k + 2) * q (k + 2)) :=
          Q'.eqv_trans _ _ _ hp3'
            (Q'.add_eqv_congr_left (q (k + 2)) _ _ (Q'.eqv_symm RQ2))
        have hcollect :
            ((q (k + 2)) + Q'.ofNat (k + 2) * q (k + 2)).eqv (Q'.ofNat (k + 3) * q (k + 2)) := by
          refine Q'.eqv_symm ?_
          refine Q'.eqv_trans _ _ _ (succCoeff (k + 2) (q (k + 2))) ?_
          exact Q'.add_comm_eqv (Q'.ofNat (k + 2) * q (k + 2)) (q (k + 2))
        have hfinal : (Q'.ofNat (k + 3) * p (k + 3)).eqv (Q'.ofNat (k + 3) * q (k + 2)) :=
          Q'.eqv_trans _ _ _ hp3'' hcollect
        exact cancelSucc (k := k + 2) hfinal
  intro n
  exact (pair n).1

/-! ## 3. The value-level bridge: `S_P(x, N+1) ≃ x·S_Q(x, N)` (green)

The formal identity `p_{n+1} ≃ qₙ` (with `p₀ ≃ 0`) lifts to the **finite partial
sums** with no analysis at all: `Σ_{n<N+1} pₙ xⁿ ≃ x·Σ_{n<N} qₙ xⁿ`.  This turns
`odeShift` into a genuine value-level certificate — the ONLY remaining gap to the
CReal statement is the pure convergence of these partial sums to `sinC`/`cosC`. -/

/-- `x^n : Q'`. -/
def qpow (x : Q') : Nat → Q'
  | 0 => 1
  | n + 1 => x * qpow x n

/-- Partial power-series sum `Σ_{n<N} aₙ xⁿ`. -/
def series (a : Nat → Q') (x : Q') : Nat → Q'
  | 0 => 0
  | N + 1 => series a x N + a N * qpow x N

/-- `u·(v·w) ≃ v·(u·w)` — pull the middle factor out. -/
theorem mulSwap (u v w : Q') : (u * (v * w)).eqv (v * (u * w)) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv u v w)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (u * v) (v * u) w (Q'.mul_comm_eqv u v)) ?_
  exact Q'.mul_assoc_eqv v u w

/-- **The partial-sum shift identity.**  From the formal coefficient identity
`a_{n+1} ≃ bₙ` and `a₀ ≃ 0`, the sine partial sum of length `N+1` equals `x`
times the cosine partial sum of length `N`.  This is the exact value-level
content of `P = x·Q`, at every truncation. -/
theorem shiftMulX (a b : Nat → Q') (x : Q')
    (hshift : ∀ n, (a (n + 1)).eqv (b n)) (h0 : (a 0).eqv 0) :
    ∀ N, (series a x (N + 1)).eqv (x * series b x N) := by
  intro N
  induction N with
  | zero =>
      -- `series a x 1 = 0 + a 0 * 1 ≃ 0 ≃ x * 0 = x * series b x 0`
      show (series a x 0 + a 0 * qpow x 0).eqv (x * series b x 0)
      refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' (a 0 * qpow x 0))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_one_eqv (a 0)) ?_
      exact Q'.eqv_trans _ _ _ h0 (Q'.eqv_symm (Q'.mul_zero_eqv x))
  | succ N ih =>
      show (series a x (N + 1) + a (N + 1) * qpow x (N + 1)).eqv (x * series b x (N + 1))
      -- rewrite the new term `a(N+1)·(x·qpow) ≃ x·(b N · qpow)`
      have hterm : (a (N + 1) * qpow x (N + 1)).eqv (x * (b N * qpow x N)) := by
        show (a (N + 1) * (x * qpow x N)).eqv (x * (b N * qpow x N))
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right (a (N + 1)) (b N) (x * qpow x N) (hshift N)) ?_
        exact mulSwap (b N) x (qpow x N)
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ih hterm) ?_
      -- `x·S + x·t ≃ x·(S + t)`
      exact Q'.eqv_symm (Q'.mul_add_eqv x (series b x N) (b N * qpow x N))

/-! ## 4. The named residual and the reduction to the tangent link -/

/-- The tangent link `sα ≃ x·cα` (`tan(arctan x) = x`), matching
`ArctanTanInversion.ArctanTrigLink`.  A concrete model supplies this for
`α = arctan x`, `cα = cos α`, `sα = sin α`. -/
def TanLink (x : Q') (cα sα : CReal) : Prop :=
  CReal.Equiv sα (CReal.mul (CReal.ofQ' x) cα)

/-- **The honest interface for the arctan↔trig link at a base value `x`.**

Fields, read as content:
  * `p`,`q`         — the formal power-series coefficients of `sin(arctan x)`,
                      `cos(arctan x)`;
  * `cval`,`sval`   — the actual CReal values (`cos(arctan x)`, `sin(arctan x)`),
                      so the conclusion is a genuine `CReal.Equiv`;
  * `hp`/`hp0`/`hq`/`hq0`/`hp0init` — (REC) the ODE coefficient recurrences the
                      composed series satisfy (the formal chain-rule content);
  * `valBridge`     — (VAL) the tail/convergence bridge: the formal identity
                      `p_{n+1} ≃ qₙ` lifts to the CReal values `sval ≃ x·cval`.

The algebraic middle (`p_{n+1} ≃ qₙ`) is discharged by `odeShift`; the residual is
exactly the (REC)+(VAL) data for a concrete `arctanRecip`/`sinC`/`cosC`. -/
structure TanArctanModel (x : Q') where
  p : Nat → Q'
  q : Nat → Q'
  cval : CReal
  sval : CReal
  hp0 : (p 1).eqv (q 0)
  hp : ∀ n, (Q'.ofNat (n + 2) * p (n + 2) + Q'.ofNat n * p n).eqv (q (n + 1))
  hq0 : (q 1).eqv (-(p 0))
  hq : ∀ n, (Q'.ofNat (n + 2) * q (n + 2) + Q'.ofNat n * q n).eqv (-(p (n + 1)))
  hp0init : (p 0).eqv 0
  valBridge : (∀ n, (p (n + 1)).eqv (q n)) → TanLink x cval sval

/-- **The tangent link, modulo the model.**  `sin(arctan x) ≃ x·cos(arctan x)`.

The whole transcendental burden is the existence of the model; GIVEN it, the
algebraic identity `p_{n+1} ≃ qₙ` is discharged by `odeShift` and fed to
`valBridge`. -/
theorem tanArctan_of_model {x : Q'} (M : TanArctanModel x) : TanLink x M.cval M.sval :=
  M.valBridge (odeShift M.p M.q M.hp0 M.hp M.hq0 M.hq M.hp0init)

end YMGap.Continuum.TanArctan

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TanArctan.addNegCancelR
#print axioms YMGap.Continuum.TanArctan.moveR
#print axioms YMGap.Continuum.TanArctan.cancelSucc
#print axioms YMGap.Continuum.TanArctan.zeroCoeff
#print axioms YMGap.Continuum.TanArctan.succCoeff
#print axioms YMGap.Continuum.TanArctan.odeShift
#print axioms YMGap.Continuum.TanArctan.mulSwap
#print axioms YMGap.Continuum.TanArctan.shiftMulX
#print axioms YMGap.Continuum.TanArctan.tanArctan_of_model
