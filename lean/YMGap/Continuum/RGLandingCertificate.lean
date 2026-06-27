/-
Track B / R2 — **the RG-landing target sharpened to a DIMENSIONLESS RATIONAL
certificate**, with the continuum scale carried as the single named-open datum.

# What this module is — and what it is emphatically NOT (read first)

This file does NOT prove the 4D Yang–Mills continuum mass gap, and it does NOT
inhabit the open landing wall.  It SHARPENS the shape of the open RG-landing
target.

The earlier continuum-closure scaffold isolated the analytic frontier into a bare
positive per-scale gap floor `prodFloor > 0` (the uniform floor produced by the
`DefectGapRecursion` product induction).  Per the external-strategy review, the
genuinely Clay-relevant landing target is not a bare positive floor in lattice
units — it is a strictly-positive lower bound on the DIMENSIONLESS, RG-invariant
ratio `m / Λ_YM` (the continuum gap over the dynamically-generated scale).  This
module recasts the target in exactly that dimensionless rational form.

The certificate is stated DIVISION-FREE (there is no total `CReal` division in
this project; ratios are carried by cross-multiplication, matching `SqrtBridge`
and `DimensionlessRatio`):

      q · Λ_YM  ≤  m        i.e.   q  ≤  m / Λ_YM,   q a positive RATIONAL.

# The genuine content vs the named-open wall

GENUINE (proved here, reusing real machinery):

  * The RATIONAL certificate `q` is NOT a free decoration.  It is taken to be the
    per-scale gap-floor `D.prodFloor` of an arbitrary `DefectGapRecursion D` —
    the genuine product-floor output of the summability / per-step recursion
    machinery (`continuum_floor_of_defectRecursion`).  Its positivity is
    `D.prodFloor_pos`.  Thus the certificate's rational content is tied to the
    proved per-scale recursion, not invented.

  * The REDUCTION `rgLanding_of_input` is real proof: it assembles the full
    dimensionless certificate from the single named continuum-scale datum,
    supplying `q := D.prodFloor` from the recursion.  It shows the landing
    certificate FOLLOWS from the continuum-scale normalization input.

NAMED-OPEN (the wall, carried as `Type`-level data, never faked):

  * `RGLandingInput D` packages the continuum-scale normalization: the continuum
    gap `m` (`massScale`), the dynamically-generated scale `Λ_YM` (`lambdaYM`,
    strictly positive), and the division-free dimensionless bound
    `ofQ' D.prodFloor · Λ_YM ≤ m`.  This is EXACTLY the asymptotically-free
    RG-landing wall: relating the continuum limit of the per-scale floor to the
    physical scale `Λ_YM`.  NO inhabitant of `RGLandingInput` is constructed —
    it is uninhabited by design.

So this module contributes the proved reduction and the rational `q` from the
real recursion; the ONE open input remains the continuum-scale normalization,
now sharpened to the dimensionless rational shape `q ≤ m/Λ_YM`.

# Honesty contract (AGENTS.md Rules 1, 6, 8)

  * `RGLandingCertificate`, `RGLandingInput` are `Type`-level `structure`s with
    real content (positivity proofs + a genuine cross-multiplied `CReal`
    inequality).  No `Prop := True`, no vacuous/free-data field.
  * NO inhabitant of `RGLandingInput` or `RGLandingCertificate` is constructed
    unconditionally.  The only constructor is the CONDITIONAL reduction
    `rgLanding_of_input`, which CONSUMES an `RGLandingInput`.
  * Every load-bearing declaration is gated with `#print axioms`; permitted
    output is `propext` / `Quot.sound` only.  No `Classical.*`, no
    `native_decide`, no `sorry`.
-/

import YMGap.Continuum.ContinuumClosureProgram
import YMGap.Continuum.DimensionlessRatio
import YMGap.Constructive.Reals

namespace YMGap.Continuum.RGLandingCertificate

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ContinuumClosureProgram

/-! ## 1. The named-open continuum-scale normalization input (the wall)

`RGLandingInput D` is parameterized over an arbitrary per-scale defect-controlled
gap recursion `D : DefectGapRecursion`.  It carries the two continuum-scale
`CReal`s — the continuum gap `m` and the dynamically-generated scale `Λ_YM` — and
the division-free dimensionless bound `ofQ' D.prodFloor · Λ_YM ≤ m`, i.e.
`D.prodFloor ≤ m / Λ_YM`.

This is the genuinely-OPEN analytic obligation: it relates the per-scale rational
floor `D.prodFloor` (a lattice-units quantity from the recursion) to the physical
continuum ratio `m / Λ_YM`.  NO inhabitant is provided — it IS the
asymptotically-free RG-landing wall (the continuum-scale normalization). -/

/-- **The named-open continuum-scale normalization input (the RG-landing wall).**

`Type`-level data (Rule 8).  Given a `DefectGapRecursion D`, an inhabitant would
supply the continuum gap `massScale = m`, the dynamically-generated scale
`lambdaYM = Λ_YM > 0`, and the division-free dimensionless bound
`ofQ' D.prodFloor · Λ_YM ≤ m`.  NO inhabitant is constructed: this is the open
continuum-scale normalization. -/
structure RGLandingInput (D : DefectGapRecursion) : Type where
  /-- The continuum gap `m`, as a `CReal`. -/
  massScale : CReal
  /-- The dynamically-generated scale `Λ_YM`, as a `CReal`. -/
  lambdaYM : CReal
  /-- `Λ_YM` is strictly positive (a genuine physical scale). -/
  lambdaYM_pos : CReal.IsPositive lambdaYM
  /-- **THE OPEN CONTENT — the division-free dimensionless bound.**  The per-scale
  rational floor `D.prodFloor` is a lower bound for the dimensionless ratio
  `m / Λ_YM`, encoded division-free as `ofQ' D.prodFloor · Λ_YM ≤ m`.  This is the
  continuum-scale normalization — the asymptotically-free RG-landing wall. -/
  ratio_bound :
    CReal.mul (CReal.ofQ' D.prodFloor) lambdaYM ≤ massScale

/-! ## 2. The dimensionless rational landing certificate

`RGLandingCertificate` is the SHAPE of the sharpened landing target: a positive
RATIONAL `q` with the division-free dimensionless bound `ofQ' q · Λ_YM ≤ m`,
i.e. `q ≤ m / Λ_YM`.  The certificate stands alone (it does not mention any
particular recursion); the reduction below shows how to build it. -/

/-- **The dimensionless rational RG-landing certificate.**

`Type`-level data.  It asserts a positive RATIONAL lower bound `q` on the
dimensionless ratio `m / Λ_YM`, stated division-free as `ofQ' q · Λ_YM ≤ m`.
This is the Clay-relevant landing shape: a pure-number rational floor on the
RG-invariant ratio. -/
structure RGLandingCertificate : Type where
  /-- The continuum gap `m`, as a `CReal`. -/
  massScale : CReal
  /-- The dynamically-generated scale `Λ_YM`, as a `CReal`. -/
  lambdaYM : CReal
  /-- `Λ_YM` is strictly positive. -/
  lambdaYM_pos : CReal.IsPositive lambdaYM
  /-- The extracted RATIONAL certificate `q` (the dimensionless floor). -/
  q : Q'
  /-- The rational certificate is strictly positive. -/
  q_pos : (0 : Q') < q
  /-- **The division-free dimensionless bound:** `ofQ' q · Λ_YM ≤ m`, i.e.
  `q ≤ m / Λ_YM`. -/
  ratio_bound :
    CReal.mul (CReal.ofQ' q) lambdaYM ≤ massScale

/-! ## 3. The reduction — the genuine content

From the named continuum-scale input `RGLandingInput D`, assemble the
`RGLandingCertificate` with the rational `q := D.prodFloor` supplied by the real
per-scale recursion (positivity from `D.prodFloor_pos`).  This is the genuine
reduction: the landing certificate FOLLOWS from the continuum-scale normalization
datum, with its rational content tied to the proved product floor.

NOTE: this is the ONLY way to obtain an `RGLandingCertificate` here, and it
CONSUMES an `RGLandingInput`; no unconditional inhabitant exists. -/

/-- **THE REDUCTION (the headline conditional).**  From a `DefectGapRecursion D`
and the named continuum-scale input `RGLandingInput D`, build the dimensionless
rational landing certificate with `q := D.prodFloor` (the genuine product-floor
output of the recursion) and `q_pos := D.prodFloor_pos`.  The `ratio_bound` is
carried verbatim from the input — it is the open continuum-scale normalization.
This PROVES that the sharpened landing certificate follows from the single open
datum. -/
def rgLanding_of_input (D : DefectGapRecursion) (h : RGLandingInput D) :
    RGLandingCertificate where
  massScale := h.massScale
  lambdaYM := h.lambdaYM
  lambdaYM_pos := h.lambdaYM_pos
  q := D.prodFloor
  q_pos := D.prodFloor_pos
  ratio_bound := h.ratio_bound

/-! ## 4. Non-vacuity guard

The certificate's rational `q` is LITERALLY `D.prodFloor` (the real machinery),
and it is strictly positive.  We expose this as a lemma so the genuineness is
machine-checked, not merely asserted. -/

/-- **Non-vacuity guard.**  The certificate's extracted rational `q` is exactly
the recursion's product floor `D.prodFloor`, and it is strictly positive.  This
confirms the rational content is supplied by real machinery, not a free
rational. -/
theorem rgLandingCertificate_q_pos (D : DefectGapRecursion) (h : RGLandingInput D) :
    (0 : Q') < (rgLanding_of_input D h).q :=
  D.prodFloor_pos

/-- **Sanity: `q` is literally `D.prodFloor`.**  The extracted rational of the
built certificate is definitionally the recursion's product floor. -/
theorem rgLandingCertificate_q_eq_prodFloor
    (D : DefectGapRecursion) (h : RGLandingInput D) :
    (rgLanding_of_input D h).q = D.prodFloor := rfl

end YMGap.Continuum.RGLandingCertificate

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RGLandingCertificate.rgLanding_of_input
#print axioms YMGap.Continuum.RGLandingCertificate.rgLandingCertificate_q_pos
#print axioms YMGap.Continuum.RGLandingCertificate.rgLandingCertificate_q_eq_prodFloor
