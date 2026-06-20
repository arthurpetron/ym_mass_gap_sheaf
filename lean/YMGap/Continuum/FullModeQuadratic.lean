/-
Track B / R2 — the **full-mode** (all spins `s`) renormalized quadratic defect of
the SU(2) bond-moving step: the per-coefficient transverse residual is QUADRATIC in
the weak-coupling margin `1 − w` for EVERY mode `s`, with the `s`-dependence carried
by an EXPLICIT nonnegative-coefficient polynomial in the Casimir exponent `C₄(s)`.

# Why this module exists — extending the dominant-mode crack to all modes

One Migdal–Kadanoff block step is `bond-moving ∘ decimation`.  The bond-moving half
raises the single-plaquette SU(2) class function to the power `p = b^{d−1}`
pointwise and re-expands in characters (the Clebsch–Gordan fusion convolution
`fusionPow`).  On the dominant first-excited mode `s = 1` the renormalized
transverse defect is proved QUADRATIC in the margin `1 − w` (the linear/marginal
coupling drift is absorbed by the `s = 1` retuning, leaving an `O((1−w)²)`
residual).  That dominant-mode result is the seed; THIS module extends the
quadratic control to the FULL spin tower.

Two genuinely-proved pieces here:

  1. **The generalized second-order remainder, per mode.**  For the diagonal
     heat-kernel coefficient `coeff_w(s) = dimQ s · w^{C₄(s)}`, the matched-linear
     model `dimQ s · C₄(s)·(1 − w)` overshoots the true deviation
     `dimQ s · (1 − w^{C₄(s)})` by at most a QUADRATIC amount, with the
     `s`-dependence an EXPLICIT polynomial in `C₄(s)`:

         δ_s(w)  :=  dimQ s · ( C₄(s)·(1 − w) − (1 − w^{C₄(s)}) )
                  ≤  dimQ s · C₄(s)² · (1 − w)².

     This is `secondOrder_qpow` (the reusable `w^n` Taylor-with-remainder engine)
     instantiated at the per-mode exponent `n = C₄(s)` and scaled by the dimension
     `dimQ s`.  It generalizes the `s = 1`-only dominant-mode bound to every `s`.

  2. **The coefficientwise quadratic envelope via POSITIVE DOMINATION.**  The
     per-mode defect sequence `s ↦ δ_s(w)` is dominated coefficientwise
     (`≤_c`, `FusionPositivity`) by the EXPLICIT nonnegative-coefficient envelope

         H_w(s)  :=  dimQ s · C₄(s)² · (1 − w)²  =  (1 − w)² · ( dimQ s · C₄(s)² ),

     i.e. `δ_·(w) ≤_c H_w`.  Because the SU(2) Clebsch–Gordan structure constants
     are nonnegative, the `p`-fold bond-moving map `fusionPow` is MONOTONE
     (`bondMove_envelope`), so the domination is PRESERVED under bond-moving:

         fusionPow N (δ_·(w)) p  ≤_c  fusionPow N H_w p.

     The positivity-preservation of fusion replaces analytic cancellation: the
     quadratic envelope, valid for ALL modes, survives the convolution.

The EXPLICIT polynomial envelope factor is `P_p(y) = y²` carried per mode as
`dimQ s · C₄(s)²` (degree-2 in `C₄(s)`, nonnegative coefficients), times the
universal quadratic margin factor `(1 − w)²`.

# Scope and honesty (AGENTS.md Rule 6) — what is PROVED vs. what remains

PROVED (genuine `Q'`/`Nat` arithmetic, axiom-clean):

  * `modeDefect` / `modeDefect_nonneg` / **`modeDefect_quadratic`** — the per-mode
    renormalized transverse defect and its EXPLICIT quadratic-times-Casimir bound
    `δ_s ≤ dimQ s · C₄(s)² · (1 − w)²`, for EVERY mode `s` (not just `s = 1`).
    This is the generalized second-order remainder (piece 1).
  * `quadEnvelope` / `quadEnvelope_nonneg` — the EXPLICIT nonnegative-coefficient
    envelope sequence `H_w(s) = (1 − w)²·(dimQ s · C₄(s)²)`.
  * **`modeDefect_le_envelope`** (`δ_·(w) ≤_c H_w`) — the coefficientwise
    domination of the per-mode defect by the envelope, for ALL modes.
  * **`bondMoved_defect_le_envelope`** — the POSITIVE-DOMINATION lift: the
    bond-moving map preserves the envelope domination,
    `fusionPow N (δ_·(w)) p ≤_c fusionPow N H_w p`.  This is the crack: the
    all-mode quadratic envelope survives the fusion convolution.
  * `envelope_factor_quadratic` — the envelope is `(1 − w)²` times an explicit
    `w`-independent nonnegative-coefficient Casimir polynomial `dimQ s · C₄(s)²`,
    making the quadratic-in-margin structure manifest per mode.

HONEST SCOPE — what is NOT closed here:

  * The defect `δ_s` is the per-FACTOR (single-plaquette) renormalized transverse
    residual against the `s = 1`-matched linear/marginal model.  The retuning
    matches the `s = 1` direction only; higher modes are NOT separately re-matched.
    The genuine content proved is that the per-mode residual against the matched
    model is QUADRATIC for every `s` with explicit Casimir-polynomial growth.
  * The EXACT normalized ratio `B_p(K_τ)_s / K_{R_p(τ)}(s) − 1` of the FULL fusion
    convolution is NOT computed in closed form here; what is delivered is the
    coefficientwise quadratic envelope and its domination-preservation under
    bond-moving (the positivity route), which bounds the bond-moved defect
    coefficientwise by the bond-moved envelope.  Converting that coefficientwise
    envelope into a single scaled-NORM `O(τ²)` bound requires the moment
    `∑ μ_τ·(1+y)^q·P_p(y) ≤ M_p` (the scaled-norm tail/moment infrastructure of a
    sibling module); that moment is NOT assembled here.
  * Per-step only; the summability `∑_k δ(w_k,p) < ∞` along the AF trajectory is a
    sibling obligation, NOT inhabited here.

The decisive advance over the dominant-mode module: the quadratic remainder is now
proved for EVERY mode `s` with explicit Casimir-polynomial `s`-dependence, AND the
all-mode envelope is shown to survive the bond-moving fusion convolution by positive
domination — the analytic-cancellation-free route to the full-mode defect.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, reusing the second-order Taylor engine and the fusion
monotonicity (positive-domination) tool.  Every load-bearing declaration is gated
with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.BondMovingQuadratic
import YMGap.Continuum.FusionPositivity

namespace YMGap.Continuum.FullModeQuadratic

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.FusionPositivity

/-! ## 1. The generalized second-order remainder — per mode `s`

The dominant-mode module proves `secondOrder_qpow` (the `w^n` Taylor-with-remainder
engine) and instantiates it at `n = C₄(1) = 3`.  Here we instantiate it at the
GENERAL per-mode exponent `n = C₄(s)` and scale by the dimension `dimQ s`, giving the
per-mode renormalized transverse defect and its quadratic-times-Casimir bound for
EVERY `s`. -/

/-- **The per-mode renormalized transverse defect** `δ_s(w)`: the overshoot of the
matched linear (marginal-flow) model `dimQ s · C₄(s)·(1 − w)` over the true
first-mode deviation `dimQ s · (1 − w^{C₄(s)})`, at mode `s`:

    δ_s(w)  =  dimQ s · ( C₄(s)·(1 − w)  −  (1 − w^{C₄(s)}) ).

Nonnegative on `[0,1]` (the linear model over-estimates), and `0` at `w = 1` and at
`s = 0` (`C₄(0) = 0`).  At `s = 1` this is the per-factor (`p = 1`) form of the
dominant-mode `bondMovingDeltaRen`. -/
def modeDefect (w : Q') (s : Nat) : Q' :=
  dimQ s * ((Q'.ofNat (c4 s) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 s)))

/-- The per-mode defect is nonnegative on `[0,1]` (the linear marginal-flow model
over-estimates: `1 − w^{C₄(s)} ≤ C₄(s)·(1 − w)`). -/
theorem modeDefect_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (s : Nat) : (0 : Q') ≤ modeDefect w s := by
  refine Q'.mul_nonneg _ _ (dimQ_nonneg s) ?_
  have hlin : (1 : Q') - qpow w (c4 s) ≤ Q'.ofNat (c4 s) * ((1 : Q') - w) :=
    oneSub_qpow_le hw0 hw1 (c4 s)
  exact Q'.sub_nonneg_of_le hlin

/-- **THE GENERALIZED SECOND-ORDER REMAINDER — per mode.**  On `[0,1]`, for EVERY
mode `s`,

    modeDefect w s  ≤  dimQ s · ( C₄(s)² · ((1 − w)·(1 − w)) ),

i.e. the per-mode renormalized transverse residual is QUADRATIC in the margin
`1 − w`, with the `s`-dependence the EXPLICIT Casimir polynomial `C₄(s)²` (degree 2,
nonnegative coefficients).  PROOF: the inner bracket is the second-order overshoot
`secondOrder_qpow` at exponent `n = C₄(s)`; scale by `dimQ s ≥ 0`.  Generalizes the
dominant-mode `bondMovingDeltaRen_quadratic` (the `s = 1`, `p = 1` instance) to all
`s`. -/
theorem modeDefect_quadratic {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (s : Nat) :
    modeDefect w s
      ≤ dimQ s * ((Q'.ofNat (c4 s) * Q'.ofNat (c4 s)) * (((1 : Q') - w) * ((1 : Q') - w))) := by
  -- inner bracket: the second-order overshoot at n = C₄(s)
  have hquad :
      (Q'.ofNat (c4 s) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 s))
        ≤ (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)) * (((1 : Q') - w) * ((1 : Q') - w)) :=
    secondOrder_qpow hw0 hw1 (c4 s)
  -- scale by dimQ s ≥ 0 on the left
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hquad (dimQ_nonneg s)

/-! ## 2. The explicit nonnegative-coefficient quadratic envelope

The per-mode bound `modeDefect w s ≤ dimQ s · C₄(s)² · (1 − w)²` says the defect is
dominated, coefficientwise over `s`, by the explicit sequence

    H_w(s)  :=  (1 − w)² · ( dimQ s · C₄(s)² ),

which factors as the universal QUADRATIC margin `(1 − w)²` times the `w`-independent
NONNEGATIVE-COEFFICIENT Casimir polynomial `dimQ s · C₄(s)²`.  This is the envelope
the positive-domination tool transports through the bond-moving map. -/

/-- **The explicit quadratic envelope** sequence
`H_w(s) = (1 − w)²·(dimQ s · C₄(s)²)` — the universal quadratic margin `(1 − w)²`
times the `w`-independent nonnegative-coefficient Casimir polynomial `dimQ s·C₄(s)²`. -/
def quadEnvelope (w : Q') (s : Nat) : Q' :=
  (((1 : Q') - w) * ((1 : Q') - w)) * (dimQ s * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)))

/-- The envelope is nonnegative on `[0,1]` (a product of a square and a nonnegative
Casimir polynomial). -/
theorem quadEnvelope_nonneg {w : Q'} (hw1 : w ≤ (1 : Q')) (s : Nat) :
    (0 : Q') ≤ quadEnvelope w s := by
  have hnn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  refine Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hnn hnn) ?_
  exact Q'.mul_nonneg _ _ (dimQ_nonneg s)
    (Q'.mul_nonneg _ _ (zero_le_ofNat (c4 s)) (zero_le_ofNat (c4 s)))

/-- **The envelope is `(1 − w)²` times a `w`-independent Casimir polynomial.**  The
quadratic-in-margin structure made manifest: `H_w(s) = (1 − w)²·(dimQ s · C₄(s)²)`,
holding the explicit nonnegative-coefficient factor `dimQ s · C₄(s)²` (degree 2 in
`C₄(s)`) apart from the universal quadratic margin `(1 − w)²`.  (Definitional; stated
for downstream legibility of the `P_p(y) = y²`/Casimir structure.) -/
theorem envelope_factor_quadratic (w : Q') (s : Nat) :
    quadEnvelope w s
      = (((1 : Q') - w) * ((1 : Q') - w)) * (dimQ s * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))) :=
  rfl

/-- **THE COEFFICIENTWISE QUADRATIC ENVELOPE — all modes.**  The per-mode defect
sequence is dominated coefficientwise by the explicit quadratic envelope:

    modeDefect w  ≤_c  quadEnvelope w        (i.e. `∀ s, modeDefect w s ≤ H_w(s)`).

PROOF: the per-mode bound `modeDefect_quadratic` gives
`δ_s ≤ dimQ s · (C₄(s)²·(1−w)²)`; reassociate/commute the RHS into
`(1−w)²·(dimQ s·C₄(s)²) = H_w(s)`. -/
theorem modeDefect_le_envelope {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    modeDefect w ≤_c quadEnvelope w := by
  intro s
  refine Q'.le_trans' _ _ _ (modeDefect_quadratic hw0 hw1 s) ?_
  -- dimQ s · (C₄² · u²)  ≃  u² · (dimQ s · C₄²)   where u = 1−w, C₄² = ofNat(c4 s)²
  refine Q'.le_of_eqv ?_
  -- d·(C·u) ≃ u·(d·C)  with d = dimQ s, C = C₄², u = (1−w)²
  -- d·(C·u) ≃ (d·C)·u  [assoc symm] ≃ u·(d·C)  [comm]
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (dimQ s) (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))
      (((1 : Q') - w) * ((1 : Q') - w)))) ?_
  exact Q'.mul_comm_eqv (dimQ s * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)))
    (((1 : Q') - w) * ((1 : Q') - w))

/-! ## 3. THE CRACK — the all-mode envelope survives bond-moving (positive domination)

The coefficientwise domination `modeDefect w ≤_c quadEnvelope w` is preserved by the
`p`-fold bond-moving fusion map, because the SU(2) Clebsch–Gordan structure
constants are nonnegative (`FusionPositivity.bondMove_envelope`).  This replaces
analytic cancellation: the all-mode quadratic envelope is transported through the
fusion convolution. -/

/-- **THE POSITIVE-DOMINATION LIFT — the all-mode envelope survives bond-moving.**
The `p`-fold bond-moving map preserves the coefficientwise quadratic-envelope
domination:

    fusionPow N (modeDefect w) p  ≤_c  fusionPow N (quadEnvelope w) p,

i.e. the bond-moved per-mode defect is dominated, coefficientwise for ALL modes, by
the bond-moved quadratic envelope.  PROOF: `bondMove_envelope` applied to
`modeDefect w ≤_c quadEnvelope w` (`modeDefect_le_envelope`), with the
nonnegativity side-conditions `modeDefect w ≥ 0` (`modeDefect_nonneg`) and
`quadEnvelope w ≥ 0` (`quadEnvelope_nonneg`).  This is the analytic-cancellation-free
route: positivity of fusion carries the all-mode quadratic envelope through the
convolution. -/
theorem bondMoved_defect_le_envelope {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N p : Nat) :
    fusionPow N (modeDefect w) p ≤_c fusionPow N (quadEnvelope w) p :=
  bondMove_envelope N p
    (fun s => modeDefect_nonneg hw0 hw1 s)
    (fun s => quadEnvelope_nonneg hw1 s)
    (modeDefect_le_envelope hw0 hw1)

/-! ## 4. Consistency with the dominant-mode crack

The per-mode defect at `s = 1` is exactly the per-factor (`p = 1`) form of the
dominant-mode `bondMovingDeltaRen`: `modeDefect w 1 = bondMovingDeltaRen N 1 w` (the
`bondMovingDeltaRen` carries the bond-moving multiplicity `p` as an outer factor, so
at `p = 1` they coincide).  This anchors the generalization. -/

/-- **Consistency at the dominant mode.**  `modeDefect w 1` equals the per-factor
(`p = 1`) dominant-mode renormalized defect `bondMovingDeltaRen N 1 w`: both are
`dimQ 1 · ( C₄(1)·(1 − w) − (1 − w^{C₄(1)}) )` (the `bondMovingDeltaRen`'s outer
`ofNat p` factor is `ofNat 1`).  PROOF: unfold both; the `1·x` is removed by the
`Q'` unit law. -/
theorem modeDefect_one_eq_bondMovingDeltaRen (N : Nat) (w : Q') :
    (modeDefect w 1).eqv (bondMovingDeltaRen N 1 w) := by
  -- modeDefect w 1 = dimQ 1 · B ;  bondMovingDeltaRen N 1 w = ofNat 1 · (dimQ 1 · B)
  show (dimQ 1 * ((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1)))).eqv
      (Q'.ofNat 1 * (dimQ 1 * ((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1)))))
  exact Q'.eqv_symm (Q'.one_mul_eqv _)

/-! ## 5. Doc-section — PROVED vs. remaining (CRITICAL honesty)

  * GENERALIZED SECOND-ORDER REMAINDER, ALL MODES (proved).  `modeDefect_quadratic`:
    on `[0,1]`, for EVERY `s`, the per-mode renormalized transverse defect is
    `≤ dimQ s · C₄(s)² · (1 − w)²` — QUADRATIC in the margin with explicit Casimir
    polynomial `s`-dependence.  This generalizes the `s = 1`-only dominant-mode
    quadratic bound (its `p = 1` instance is `modeDefect_one_eq_bondMovingDeltaRen`).

  * EXPLICIT NONNEG-COEFF ENVELOPE (proved).  `quadEnvelope w s =
    (1 − w)²·(dimQ s · C₄(s)²)` (`envelope_factor_quadratic`), and
    `modeDefect_le_envelope`: `modeDefect w ≤_c quadEnvelope w` for ALL modes.

  * POSITIVE-DOMINATION LIFT (proved — THE CRACK).  `bondMoved_defect_le_envelope`:
    the bond-moving map preserves the all-mode envelope domination,
    `fusionPow N (modeDefect w) p ≤_c fusionPow N (quadEnvelope w) p`.  The
    nonnegativity of the SU(2) fusion structure constants carries the all-mode
    quadratic envelope through the convolution — no analytic cancellation needed.

HONEST VERDICT and SCOPE.  The full-mode (all `s`) quadratic remainder is GENUINELY
PROVED at the per-coefficient level with explicit Casimir-polynomial growth, and the
envelope is shown to SURVIVE the bond-moving fusion convolution by positive
domination.  NOT closed here: (i) the retuning matches the `s = 1` direction only —
`modeDefect` is the residual against that single matched model, not a per-mode
re-match; (ii) the EXACT normalized full-convolution ratio
`B_p(K_τ)_s / K_{R_p(τ)}(s) − 1` is not computed in closed form — what is delivered
is the coefficientwise envelope and its bond-moving-preservation; (iii) collapsing
the coefficientwise envelope to a single scaled-NORM `O(τ²)` bound needs the moment
`∑ μ_τ·(1 + y)^q·P_p(y) ≤ M_p` of the scaled-norm sibling, NOT assembled here;
(iv) per step only — the AF-trajectory summability is a sibling obligation.  The
explicit envelope polynomial is `P(y) = y²` carried per mode as `dimQ s · C₄(s)²`. -/

end YMGap.Continuum.FullModeQuadratic

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FullModeQuadratic.modeDefect_nonneg
#print axioms YMGap.Continuum.FullModeQuadratic.modeDefect_quadratic
#print axioms YMGap.Continuum.FullModeQuadratic.quadEnvelope_nonneg
#print axioms YMGap.Continuum.FullModeQuadratic.envelope_factor_quadratic
#print axioms YMGap.Continuum.FullModeQuadratic.modeDefect_le_envelope
#print axioms YMGap.Continuum.FullModeQuadratic.bondMoved_defect_le_envelope
#print axioms YMGap.Continuum.FullModeQuadratic.modeDefect_one_eq_bondMovingDeltaRen
