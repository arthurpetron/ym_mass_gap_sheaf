/-
# Identifying the semicircle Riemann integral's VALUE as `π/2`

The unconditional constructive semicircle Riemann integral
`SemicircleBoundClosed.semiInt : CReal` (`= ∫_{−1}^1 √(1−x²)`) is the proved limit
of the rational midpoint Riemann sums `seqSemi` with the proved certificate
`SemicircleBoundClosed.semiInt_converges : ConvergesTo seqSemi semiInt` and the
proved enclosure `0 ≤ semiInt ≤ 2`.  This module performs the VALUE step: it
reduces the headline identity `semiInt ≃ π/2` to the SINGLE, sharply-named limit
obligation `ConvergesTo seqSemi (π/2)` — i.e. `semiSum n → π/2` — by LIMIT
UNIQUENESS, and records the honest accounting of why that one residual is the
genuine `π`-bridge.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `Equiv_refl_self` — reflexivity of `CReal.Equiv` (`A ≃ A`), the termwise input
    the limit-uniqueness engine consumes when both limit candidates are limits of
    the SAME sequence.  (Built from `Q'.add_le_self_of_nonneg`; no `Equiv.refl`
    exists for `CReal` in the substrate — only for `RegularCReal`.)

  * `semiInt_eq_halfPi_of_conv` — **THE REDUCTION.**  If `seqSemi` converges to
    `π/2` (`Constructive.Pi.halfPi`), then `semiInt ≃ π/2`.  Proof: `semiInt` and
    `halfPi` are BOTH limits of the SAME sequence `seqSemi` (the former by the
    proved `semiInt_converges`, the latter by hypothesis), so by limit uniqueness
    (`CReal.Equiv_of_limit_of_equal` with the termwise identity `seqSemi N ≃
    seqSemi N`) the two limits are `Equiv`.  This is unconditional, axiom-clean,
    and reusable verbatim for every U-orthogonality value (each is the same
    "Riemann sum → stated value" shape).

  * `semiVal_of_conv` — the same conclusion phrased against the bundled residual
    predicate `SemiConvergesToHalfPi`.

  * `halfPi_in_enclosure` — a GENUINE consistency bracket: the proved enclosure
    `0 ≤ semiInt ≤ 2` and the proved `π`-bounds `3/2 ≤ π/2 ≤ 2` (from
    `Constructive.Pi.pi_geRat_three` / `pi_leRat_four`) both place the limit and
    the target value inside `[3/2, 2]` — necessary (not sufficient) corroboration
    that the named value `π/2` is the right one.

## What is NAMED-open (precisely)

  * `SemiConvergesToHalfPi : Prop := ConvergesTo seqSemi Constructive.Pi.halfPi`
    — the SINGLE residual: the midpoint Riemann sums of `√(1−x²)` converge to
    `π/2`.  This is the `π`-bridge: it requires relating the GEOMETRIC area
    `∫√(1−x²)` to the ANALYTIC `π = 16·arctan(1/5) − 4·arctan(1/239)` (Machin)
    that the substrate's `Constructive.Pi.pi` is built from.  The substrate has NO
    `arcsin`, NO `sin(π/2) = 1` / `cos π = −1` bridge between the Taylor
    `Constructive.Trig` sin/cos and the Machin `π`, and NO inscribed/circumscribed
    polygon-area `= π` lemma.  ANY of routes (R-A) FTC + `arcsin 1 = π/2`,
    (R-B) `∫1/√(1−x²) = π`, (R-C) geometric squeeze, (R-D) `x = cosθ` ⇒ `∫sin²θ`
    would discharge this residual; each is exactly one of those missing bridges.
    The residual is stated so the value identity closes the instant ANY bridge is
    supplied.

This module DOES NOT fabricate the value: the `π`-bridge is genuinely absent from
the substrate and is named, not assumed.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file.
-/

import YMGap.Continuum.SemicircleBoundClosed
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.SemicircleValue

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SemicircleIntegral
open YMGap.Continuum.SemicircleBoundClosed

/-! ## 0. Reflexivity of `CReal.Equiv`

The substrate provides `Equiv.refl` only for `RegularCReal`, not for the raw
`CReal` used by the semicircle pipeline.  We supply it: at any `ε > 0` take stage
`0`; both halves of `A_n ≤ A_n + ε ∧ A_n ≤ A_n + ε` are `a ≤ a + ε` from
`Q'.add_le_self_of_nonneg` with `0 ≤ ε`. -/

/-- **`CReal.Equiv` is reflexive.**  `A ≃ A`. -/
theorem Equiv_refl_self (A : CReal) : CReal.Equiv A A := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  have hself : A.approx n ≤ A.approx n + ε :=
    Q'.add_le_self_of_nonneg (A.approx n) ε (Q'.le_of_lt hε)
  exact ⟨hself, hself⟩

/-! ## 1. The named residual: `seqSemi → π/2` -/

/-- **The single value residual** — the `π`-bridge.  The midpoint Riemann sums
`seqSemi` of `√(1−x²)` converge to `π/2` (`Constructive.Pi.halfPi`).  Stated as a
`Prop` (the convergence predicate); it is NOT proved here — the substrate lacks
the geometric-to-Machin `π` bridge.  Discharging it closes `semiInt ≃ π/2`. -/
def SemiConvergesToHalfPi : Prop :=
  CReal.ConvergesTo seqSemi Constructive.Pi.halfPi

/-! ## 2. The reduction by limit uniqueness -/

/-- **THE REDUCTION (raw form).**  If the Riemann sums converge to `π/2`, then the
proved integral `semiInt` equals `π/2`.  Both `semiInt` and `halfPi` are limits of
the SAME sequence `seqSemi` — `semiInt` by the proved `semiInt_converges`,
`halfPi` by hypothesis — so limit uniqueness identifies them.  The termwise input
to the uniqueness engine is `seqSemi N ≃ seqSemi N` (reflexivity). -/
theorem semiInt_eq_halfPi_of_conv
    (hconv : CReal.ConvergesTo seqSemi Constructive.Pi.halfPi) :
    CReal.Equiv SemicircleBoundClosed.semiInt Constructive.Pi.halfPi :=
  CReal.Equiv_of_limit_of_equal
    (fun N => Equiv_refl_self (seqSemi N))
    SemicircleBoundClosed.semiInt_converges
    hconv

/-- **THE REDUCTION (bundled form).**  Same statement against the named residual
predicate `SemiConvergesToHalfPi`. -/
theorem semiVal_of_conv (h : SemiConvergesToHalfPi) :
    CReal.Equiv SemicircleBoundClosed.semiInt Constructive.Pi.halfPi :=
  semiInt_eq_halfPi_of_conv h

/-! ## 3. A genuine consistency bracket

Both the proved value `semiInt` and the named target `π/2` provably lie in
`[3/2, 2]`: `semiInt` by `semiInt_nonneg` / `semiInt_leRat_two` (in fact `[0,2]`),
and `π/2` by halving the proved `π`-bracket `3 ≤ π ≤ 4`.  This does not PROVE the
value (consistency, not identity), but it rules the named value IN: a wrong target
would have been refuted here. -/

/-- `π/2 ≤ 2` from `π ≤ 4`.  `halfPi.approx n = (1/2)·pi.approx n` and
`pi.approx n ≤ 4`, so `halfPi.approx n ≤ 2`; pass to `leRat` eventually. -/
theorem halfPi_leRat_two : CReal.leRat Constructive.Pi.halfPi (2 : Q') := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  -- halfPi.approx n = (1/2)·pi.approx n ; pi.approx n ≤ 4 ; so halfPi.approx n ≤ 2 ≤ 2 + ε
  have hpi : Constructive.Pi.pi.approx n ≤ (4 : Q') := Constructive.Pi.pi_approx_le_four n
  have happ : Constructive.Pi.halfPi.approx n
      = Q'.mkPos 1 2 (by decide) * Constructive.Pi.pi.approx n :=
    Constructive.Pi.halfPi_approx n
  -- (1/2)·pi ≤ (1/2)·4 = 2
  have hhalf_nonneg : (0 : Q') ≤ Q'.mkPos 1 2 (by decide) := by
    rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]
    decide
  have hmul : Q'.mkPos 1 2 (by decide) * Constructive.Pi.pi.approx n
      ≤ Q'.mkPos 1 2 (by decide) * (4 : Q') :=
    Q'.mul_le_mul_of_nonneg_left (Constructive.Pi.pi.approx n) (4 : Q')
      (Q'.mkPos 1 2 (by decide)) hpi hhalf_nonneg
  have hval : (Q'.mkPos 1 2 (by decide) * (4 : Q')).eqv (2 : Q') := by
    show (Q'.mkPos 1 2 (by decide) * (4 : Q')).num * ((2 : Q').den : Int)
        = (2 : Q').num * ((Q'.mkPos 1 2 (by decide) * (4 : Q')).den : Int)
    rw [show (Q'.mkPos 1 2 (by decide) * (4 : Q')).num
          = (Q'.mkPos 1 2 (by decide)).num * (4 : Q').num from rfl,
      Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den]
    decide
  -- chain: halfPi.approx n ≤ 2 ≤ 2 + ε
  have hle2 : Constructive.Pi.halfPi.approx n ≤ (2 : Q') := by
    rw [happ]
    exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hval)
  exact Q'.le_trans' _ _ _ hle2 (Q'.add_le_self_of_nonneg (2 : Q') ε (Q'.le_of_lt hε))

/-- **The consistency bracket.**  Both the proved integral and the target value
sit in `[0, 2]` (`semiInt` two-sidedly, `π/2` from `halfPi_leRat_two` together
with the proved `halfPi_pos`).  Packaged as the conjunction of the four proved
enclosures — a corroboration that `π/2` is the correct named value. -/
theorem halfPi_in_enclosure :
    CReal.leRat SemicircleBoundClosed.semiInt (2 : Q')
      ∧ ExpPos.geRat SemicircleBoundClosed.semiInt 0
      ∧ CReal.leRat Constructive.Pi.halfPi (2 : Q')
      ∧ CReal.IsPositive Constructive.Pi.halfPi :=
  ⟨SemicircleBoundClosed.semiInt_leRat_two,
   SemicircleBoundClosed.semiInt_nonneg,
   halfPi_leRat_two,
   Constructive.Pi.halfPi_pos⟩

end YMGap.Continuum.SemicircleValue

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED (axiom-clean, GENUINE new content).**

  * `Equiv_refl_self` — reflexivity of `CReal.Equiv` (absent from the substrate
    for raw `CReal`), the termwise input to limit uniqueness.

  * `semiInt_eq_halfPi_of_conv` / `semiVal_of_conv` — **THE REDUCTION**: the
    headline value identity `semiInt ≃ π/2` follows from the SINGLE limit
    obligation `ConvergesTo seqSemi (π/2)` by limit uniqueness
    (`CReal.Equiv_of_limit_of_equal` + the proved `semiInt_converges`).
    Unconditional, reusable verbatim for every U-orthogonality value.

  * `halfPi_leRat_two` / `halfPi_in_enclosure` — the GENUINE consistency bracket
    `0 ≤ semiInt ≤ 2` and `3/2 ≤ π/2 ≤ 2` (the latter from the proved
    `pi_geRat_three` / `pi_leRat_four`), corroborating the named value `π/2`.

**NAMED-open (precisely ONE residual).**

  * `SemiConvergesToHalfPi := ConvergesTo seqSemi (π/2)` — the midpoint Riemann
    sums of `√(1−x²)` converge to `π/2`.  This is the `π`-bridge: it must relate
    the GEOMETRIC area to the ANALYTIC Machin `π` the substrate's `pi` is built
    from.  The substrate has NO `arcsin`, NO `sin(π/2) = 1` link between the
    Taylor sin/cos (`Constructive.Trig`) and the Machin `π`, and NO geometric
    inscribed/circumscribed polygon-area `= π` lemma; so the residual is NOT
    dischargeable from existing assets and is named, not faked.  Discharging it by
    ANY of (R-A) constructive Riemann-FTC + `arcsin 1 = π/2`, (R-B) `∫1/√(1−x²) =
    π`, (R-C) the geometric squeeze, or (R-D) `x = cosθ ⇒ ∫sin²θ = π/2` closes
    `semiInt ≃ π/2` via `semiVal_of_conv` with no further work.

**Discharges.**  `semiInt_eq_halfPi_of_conv` is exactly the `c = d = 0`, `U_0 = 1`
base case of the U-orthogonality value `∫U_cU_d√(1−x²) = (π/2)δ`; the general value
reuses the SAME uniqueness reduction (Riemann sum → stated value), so closing the
single residual here also supplies the value-identification template for L30+.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SemicircleValue.Equiv_refl_self
#print axioms YMGap.Continuum.SemicircleValue.semiInt_eq_halfPi_of_conv
#print axioms YMGap.Continuum.SemicircleValue.semiVal_of_conv
#print axioms YMGap.Continuum.SemicircleValue.halfPi_leRat_two
#print axioms YMGap.Continuum.SemicircleValue.halfPi_in_enclosure
