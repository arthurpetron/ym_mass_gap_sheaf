/-
Track A / R2 — the BAND-SPLIT reduction of the `symMinor` Gershgorin domination
(`AutoconvGershgorin.SymMinorGershgorin`) to two honest named residuals, together with the
genuine PROVED diagonal-band content.

# What this module adds (read first — load-bearing honesty)

`AutoconvGershgorin` closed the Andréief half-sum expansion of the central-autoconvolution
defect into the symmetrized off-diagonal minor quadratic form and reduced the whole reserve to
the SINGLE aggregate domination

    SymMinorGershgorin.gershgorin :
        2·δ·(acN(s+1,s)·acN(s+1,s+2))  ≤  Σ_{i,j<s+1} c_i c_j symMinor(s−i,s−j),   δ = 31/225.

`LocalCLTSteepestDescent` located the indefinite content of that form at spread `|i−j| ≥ 2`
(diagonal `(3/4)` reserve `≥ 0`, adjacent band `≥ 0`, `|i−j| ≥ 2` leak bounded by the negative
envelope).  This module BAND-SPLITS the domination along the plan

    Σ_{i,j} c_i c_j symMinor(s−i,s−j)  =  D + B + L
      ≥ D + 0 + L                          (adjacent band `B ≥ 0`)
      ≥ (3/2)·S − L_env                    (diagonal reserve on `D`; envelope on `L`)
      ≥ (3/2 − 1/15)·S = (43/30)·S         (leak geometric decay `L_env ≤ (1/15)·S`)

with `S := Σ_i c_i²·c_{s−i+1}²` the anchor diagonal mass, and reduces the wall to two honest
Type-level residuals plus PROVED scalar arithmetic.

DELIVERABLE 1 (the DIAGONAL BAND — PROVED, axiom-clean, all `s`).
  * `symMinor_diag_reserve` — the pointwise `(3/2)` reserve `qq32·c_{a+1}² ≤ symMinor(a,a)`
    (twice Round J's `(3/4)` diagonal minor reserve, off `coeffW_superLogConcave`).
  * `diag_term_lower` — the `(i,i)` summand bound `qq32·R_i ≤ c_i²·symMinor(s−i,s−i)`,
    `R_i := c_i²·c_{s−i+1}²` (scale the reserve by `c_i² ≥ 0`).
  * `anchorSum`, `anchorSum_nonneg` — the anchor diagonal mass `S = Σ_i R_i` and `S ≥ 0`.
  * `anchorDiag_lower` — the AGGREGATE diagonal band `qq32·S ≤ Σ_i c_i²·symMinor(s−i,s−i)`
    (`fsum_mono_lt` over `diag_term_lower` + `fsum_const_mul`).  This is exactly the plan's
    `D ≥ (3/2)·S`.

DELIVERABLE 2 (the two-residual REDUCTION of the Gershgorin wall — REDUCTION, not closure).
  * `symQuadForm` — the `symMinor` quadratic form (the exact RHS of `SymMinorGershgorin`).
  * `QuadSlackLower w` — the COMBINATORIAL-CORE residual: `(43/30)·S ≤ symQuadForm(s)`,
    the net `(3/2 − 1/15)` slack after dropping the adjacent band and dominating the
    `|i−j| ≥ 2` leak by `(1/15)·S` (the `leak_geo_decay` sub-lemma of the plan).  NAMED-OPEN.
  * `AnchorDominatesProd w` — the TRUNCATION-EDGE BRIDGE residual: `2·(acN(s+1,s)·acN(s+1,s+2))
    ≤ S`, twice the off-diagonal product bounded by the anchor diagonal mass.  NAMED-OPEN.
  * `gershgorinOfResiduals` — a Gershgorin witness FROM the two residuals, via the PROVED
    scalar chain `2·(δ·P) ≃ δ·(2·P) ≤ δ·S ≤ (43/30)·S ≤ symQuadForm`, using `δ ≤ 43/30`.
  * `acN_defect_reserve_of_residuals` — end-to-end: the two residuals yield the range-`(s+1)`
    autoconvolution defect reserve (through `AutoconvGershgorin.acN_defect_reserve_of_gershgorin`).

# HONESTY — what is NOT closed

Neither `QuadSlackLower` nor `AnchorDominatesProd` is inhabited here.  `QuadSlackLower` still
carries the full `fsum` band split AND the `|i−j| ≥ 2` geometric leak decay (`leak_geo_decay`,
the one genuinely new computation of the plan — the row-shifted-anchor exponent bookkeeping via
`coeffW_superLogConcave_four`, tail-closed by `geoShiftTail_le`).  `AnchorDominatesProd` is the
per-level `H0auto(N,·)` ↦ uniform `acN(s+1,·)` truncation-edge bridge, a separate non-small
obligation.  What this module PROVES is the diagonal band in full and the reduction of the
single Gershgorin wall to these two honest residuals plus the scalar threshold arithmetic
`δ = 31/225 ≤ 43/30`.  This is a structural sharpening of one box-level log-concavity sub-fact;
it is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW`/`symMinor`/`coeffW_superLogConcave`/`acN` lemmas,
the `fsum_mono_lt`/`fsum_const_mul`/`fsum_nonneg` finite-sum algebra, and `decide` on closed
concrete-rational facts.  Every load-bearing declaration is gated with `#print axioms`; permitted
output is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.  All
witnesses are `Type`-level data.
-/

import YMGap.Continuum.AutoconvGershgorin

namespace YMGap.Continuum.SymMinorGershgorinProof

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.FusionCoreStepRoundJ
open YMGap.Continuum.LocalCLTSteepestDescent
open YMGap.Continuum.AutoconvGershgorin

/-! ## 0. The pinned band-split constants -/

/-- The doubled diagonal Casimir reserve constant `3/2 = 2·(3/4)`. -/
abbrev qq32 : Q' := Q'.mkPos 3 2 (by decide)
/-- The net band-split slack `43/30 = 3/2 − 1/15`. -/
abbrev qq4330 : Q' := Q'.mkPos 43 30 (by decide)
/-- The reserve constant `δ = 31/225`. -/
abbrev qδ : Q' := Q'.mkPos 31 225 (by decide)
/-- The half-sum factor `2`. -/
abbrev two : Q' := Q'.ofNat 2

/-! ## 1. The diagonal band (PROVED) -/

/-- **`symMinor_diag_reserve` — the pointwise `(3/2)` diagonal reserve** (all `a`).
`symMinor(a,a) = 2c_{a+1}² − 2c_a c_{a+2}`, and `coeffW_superLogConcave` gives
`c_a c_{a+2} ≤ (1/4)c_{a+1}²`, so `symMinor(a,a) ≥ 2c_{a+1}² − (1/2)c_{a+1}² = (3/2)c_{a+1}²`.
This is twice Round J's `(3/4)` diagonal minor reserve. -/
theorem symMinor_diag_reserve {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (a : Nat) :
    qq32 * (coeffW w (a + 1) * coeffW w (a + 1)) ≤ symMinor w a a := by
  unfold symMinor
  -- `X := c_{a+1}²`, `Z := c_a c_{a+2}`, with `Z ≤ (1/4)X`.
  have hZ : coeffW w a * coeffW w (a + 2)
      ≤ quarter * (coeffW w (a + 1) * coeffW w (a + 1)) :=
    coeffW_superLogConcave hw0 hw12 a
  have hZ2 :
      (coeffW w a * coeffW w (a + 2) + coeffW w a * coeffW w (a + 2))
        ≤ (quarter * (coeffW w (a + 1) * coeffW w (a + 1))
            + quarter * (coeffW w (a + 1) * coeffW w (a + 1))) :=
    Q'.add_le_add hZ hZ
  have hstep :
      qq32 * (coeffW w (a + 1) * coeffW w (a + 1))
          + (coeffW w a * coeffW w (a + 2) + coeffW w a * coeffW w (a + 2))
        ≤ qq32 * (coeffW w (a + 1) * coeffW w (a + 1))
            + (quarter * (coeffW w (a + 1) * coeffW w (a + 1))
                + quarter * (coeffW w (a + 1) * coeffW w (a + 1))) :=
    Q'.add_le_add (Q'.le_refl' _) hZ2
  -- `(3/2)X + ((1/4)X + (1/4)X) ≃ X + X`.
  have e :
      (qq32 * (coeffW w (a + 1) * coeffW w (a + 1))
          + (quarter * (coeffW w (a + 1) * coeffW w (a + 1))
              + quarter * (coeffW w (a + 1) * coeffW w (a + 1)))).eqv
        (coeffW w (a + 1) * coeffW w (a + 1) + coeffW w (a + 1) * coeffW w (a + 1)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (qq32 * (coeffW w (a + 1) * coeffW w (a + 1)))
        (quarter * (coeffW w (a + 1) * coeffW w (a + 1))
          + quarter * (coeffW w (a + 1) * coeffW w (a + 1)))
        ((quarter + quarter) * (coeffW w (a + 1) * coeffW w (a + 1)))
        (Q'.eqv_symm
          (Q'.add_mul_eqv quarter quarter (coeffW w (a + 1) * coeffW w (a + 1))))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.add_mul_eqv qq32 (quarter + quarter)
          (coeffW w (a + 1) * coeffW w (a + 1)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (qq32 + (quarter + quarter)) (1 + 1)
        (coeffW w (a + 1) * coeffW w (a + 1)) (by decide)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv 1 1 (coeffW w (a + 1) * coeffW w (a + 1))) ?_
    exact Q'.add_eqv_congr'
      (Q'.one_mul_eqv _) (Q'.one_mul_eqv _)
  have hle :
      qq32 * (coeffW w (a + 1) * coeffW w (a + 1))
          + (coeffW w a * coeffW w (a + 2) + coeffW w a * coeffW w (a + 2))
        ≤ coeffW w (a + 1) * coeffW w (a + 1) + coeffW w (a + 1) * coeffW w (a + 1) :=
    Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv e)
  exact le_add_neg_of_add_le hle

/-- **`anchorR`** — the `(i,i)` anchor `R_i := c_i²·c_{s−i+1}²` (the diagonal of the
autoconvolution square). -/
def anchorR (w : Q') (s i : Nat) : Q' :=
  (coeffW w i * coeffW w i) * (coeffW w (s - i + 1) * coeffW w (s - i + 1))

/-- Each anchor is nonnegative (a product of squares). -/
theorem anchorR_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (s i : Nat) :
    (0 : Q') ≤ anchorR w s i :=
  Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (coeffW_nonneg hw0 i) (coeffW_nonneg hw0 i))
    (Q'.mul_nonneg _ _ (coeffW_nonneg hw0 (s - i + 1)) (coeffW_nonneg hw0 (s - i + 1)))

/-- **`diag_term_lower` — the `(i,i)` summand reserve.**  For `i ≤ s`,
`qq32·R_i ≤ c_i²·symMinor(s−i,s−i)`: scale `symMinor_diag_reserve` (at mode `a = s−i`) by the
nonnegative anchor weight `c_i² ≥ 0`. -/
theorem diag_term_lower {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (s i : Nat)
    (_hi : i ≤ s) :
    qq32 * anchorR w s i
      ≤ (coeffW w i * coeffW w i) * symMinor w (s - i) (s - i) := by
  have hcc : (0 : Q') ≤ coeffW w i * coeffW w i :=
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0 i) (coeffW_nonneg hw0 i)
  have hd : qq32 * (coeffW w (s - i + 1) * coeffW w (s - i + 1))
      ≤ symMinor w (s - i) (s - i) := symMinor_diag_reserve hw0 hw12 (s - i)
  have hmul :
      (coeffW w i * coeffW w i)
          * (qq32 * (coeffW w (s - i + 1) * coeffW w (s - i + 1)))
        ≤ (coeffW w i * coeffW w i) * symMinor w (s - i) (s - i) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hd hcc
  -- `c_i²·(qq32·X) ≃ qq32·(c_i²·X) = qq32·R_i`.
  have e :
      ((coeffW w i * coeffW w i)
          * (qq32 * (coeffW w (s - i + 1) * coeffW w (s - i + 1)))).eqv
        (qq32 * anchorR w s i) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (coeffW w i * coeffW w i) qq32
          (coeffW w (s - i + 1) * coeffW w (s - i + 1)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right ((coeffW w i * coeffW w i) * qq32)
        (qq32 * (coeffW w i * coeffW w i))
        (coeffW w (s - i + 1) * coeffW w (s - i + 1))
        (Q'.mul_comm_eqv (coeffW w i * coeffW w i) qq32)) ?_
    exact Q'.mul_assoc_eqv qq32 (coeffW w i * coeffW w i)
      (coeffW w (s - i + 1) * coeffW w (s - i + 1))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv e) hmul

/-- **`anchorSum`** — the anchor diagonal mass `S := Σ_{i<s+1} R_i` (the diagonal of the
range-`(s+1)` autoconvolution square). -/
def anchorSum (w : Q') (s : Nat) : Q' := fsum (anchorR w s) (s + 1)

/-- `S ≥ 0`. -/
theorem anchorSum_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (s : Nat) :
    (0 : Q') ≤ anchorSum w s :=
  fsum_nonneg (fun i => anchorR_nonneg hw0 s i) (s + 1)

/-- **`anchorDiag_lower` — the AGGREGATE diagonal band `D ≥ (3/2)·S`.**  Summing the pointwise
`diag_term_lower` over `i < s+1` and pulling the constant out:
`qq32·S ≤ Σ_i c_i²·symMinor(s−i,s−i)`. -/
theorem anchorDiag_lower {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (s : Nat) :
    qq32 * anchorSum w s
      ≤ fsum (fun i => (coeffW w i * coeffW w i) * symMinor w (s - i) (s - i)) (s + 1) := by
  have e : (qq32 * anchorSum w s).eqv
      (fsum (fun i => qq32 * anchorR w s i) (s + 1)) :=
    fsum_const_mul qq32 (anchorR w s) (s + 1)
  have hmono :
      fsum (fun i => qq32 * anchorR w s i) (s + 1)
        ≤ fsum (fun i => (coeffW w i * coeffW w i) * symMinor w (s - i) (s - i)) (s + 1) :=
    fsum_mono_lt (s + 1)
      (fun i hi => diag_term_lower hw0 hw12 s i (by omega))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e) hmono

/-! ## 2. The two-residual reduction of the Gershgorin wall -/

/-- **`symQuadForm`** — the `symMinor` quadratic form on the range-`(s+1)` block; the exact RHS
of `AutoconvGershgorin.SymMinorGershgorin.gershgorin`. -/
def symQuadForm (w : Q') (s : Nat) : Q' :=
  fsum (fun i => fsum (fun j =>
    coeffW w i * coeffW w j * symMinor w (s - i) (s - j)) (s + 1)) (s + 1)

/-- **`QuadSlackLower w`** — the COMBINATORIAL-CORE residual (the plan's band split + leak
decay).  After dropping the adjacent band (`symMinor_adj_nonneg : B ≥ 0`) and dominating the
`|i−j| ≥ 2` leak by `(1/15)·S` (`leak_geo_decay`, `L_env ≤ (1/15)·S`), the quadratic form
retains the net `(3/2 − 1/15) = 43/30` diagonal slack:

    (43/30)·S  ≤  symQuadForm(s),   S = Σ_i c_i²·c_{s−i+1}².

NAMED-OPEN (never `sorry`). -/
structure QuadSlackLower (w : Q') : Type where
  /-- The `(43/30)` net band-split slack (uniform in `s`). -/
  slack : ∀ s, qq4330 * anchorSum w s ≤ symQuadForm w s

/-- **`AnchorDominatesProd w`** — the TRUNCATION-EDGE BRIDGE residual.  Twice the off-diagonal
autoconvolution product is bounded by the anchor diagonal mass:

    2·(acN(s+1,s)·acN(s+1,s+2))  ≤  S,   S = Σ_i c_i²·c_{s−i+1}².

NAMED-OPEN (never `sorry`). -/
structure AnchorDominatesProd (w : Q') : Type where
  /-- Twice the off-diagonal product is bounded by the anchor mass (uniform in `s`). -/
  dom : ∀ s,
    two * (acN w (s + 1) s * acN w (s + 1) (s + 2)) ≤ anchorSum w s

/-- **`gershgorinOfResiduals` — THE REDUCTION.**  The two residuals yield a Gershgorin witness,
via the PROVED scalar chain

    2·(δ·P)  ≃  δ·(2·P)  ≤  δ·S  ≤  (43/30)·S  ≤  symQuadForm(s),

using `2·P ≤ S` (bridge), `δ ≤ 43/30` (`decide`), and `(43/30)·S ≤ symQuadForm` (slack).
(`0 ≤ w` is threaded only for the anchor-mass nonnegativity `S ≥ 0`.) -/
def gershgorinOfResiduals {w : Q'} (hw0 : (0 : Q') ≤ w)
    (qsl : QuadSlackLower w) (adp : AnchorDominatesProd w) :
    SymMinorGershgorin w where
  gershgorin := fun s => by
    -- `P := acN(s+1,s)·acN(s+1,s+2)`, `S := anchorSum`.
    -- `2·(δ·P) ≃ δ·(2·P)`.
    have eEq :
        (two * (qδ * (acN w (s + 1) s * acN w (s + 1) (s + 2)))).eqv
          (qδ * (two * (acN w (s + 1) s * acN w (s + 1) (s + 2)))) := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv two qδ (acN w (s + 1) s * acN w (s + 1) (s + 2)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (two * qδ) (qδ * two)
          (acN w (s + 1) s * acN w (s + 1) (s + 2)) (Q'.mul_comm_eqv two qδ)) ?_
      exact Q'.mul_assoc_eqv qδ two (acN w (s + 1) s * acN w (s + 1) (s + 2))
    have h1 :
        qδ * (two * (acN w (s + 1) s * acN w (s + 1) (s + 2)))
          ≤ qδ * anchorSum w s :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ (adp.dom s) (by decide)
    have h2 : qδ * anchorSum w s ≤ qq4330 * anchorSum w s :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide) (anchorSum_nonneg hw0 s)
    have h3 : qq4330 * anchorSum w s ≤ symQuadForm w s := qsl.slack s
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eEq)
      (Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 h3))

/-- **`acN_defect_reserve_of_residuals` — end-to-end.**  The two residuals (plus `0 ≤ w`) yield
the range-`(s+1)` autoconvolution defect reserve, through
`AutoconvGershgorin.acN_defect_reserve_of_gershgorin`. -/
theorem acN_defect_reserve_of_residuals {w : Q'} (hw0 : (0 : Q') ≤ w)
    (qsl : QuadSlackLower w) (adp : AnchorDominatesProd w) (s : Nat) :
    Q'.mkPos 31 225 (by decide) * (acN w (s + 1) s * acN w (s + 1) (s + 2))
      ≤ acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1)
        + -(acN w (s + 1) s * acN w (s + 1) (s + 2)) :=
  acN_defect_reserve_of_gershgorin (gershgorinOfResiduals hw0 qsl adp) s

/-! ## 3. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `symMinor_diag_reserve` — the pointwise `(3/2)` diagonal reserve `qq32·c_{a+1}² ≤
    symMinor(a,a)` (twice Round J's `(3/4)` reserve, off `coeffW_superLogConcave`).
  * `anchorR`, `anchorR_nonneg`, `diag_term_lower` — the `(i,i)` summand reserve `qq32·R_i ≤
    c_i²·symMinor(s−i,s−i)`.
  * `anchorSum`, `anchorSum_nonneg`, `anchorDiag_lower` — the AGGREGATE diagonal band
    `qq32·S ≤ Σ_i c_i²·symMinor(s−i,s−i)` (the plan's `D ≥ (3/2)·S`).
  * `gershgorinOfResiduals` — a Gershgorin witness FROM the two residuals via the scalar chain
    `2·(δ·P) ≃ δ·(2·P) ≤ δ·S ≤ (43/30)·S ≤ symQuadForm`, using `δ = 31/225 ≤ 43/30`.
  * `acN_defect_reserve_of_residuals` — end-to-end to the range-`(s+1)` defect reserve.

NAMED OPEN (Type-level structure, never `sorry`):
  * `QuadSlackLower w` — the combinatorial-core `(43/30)·S ≤ symQuadForm(s)`: the full `fsum`
    band split + the `|i−j| ≥ 2` geometric leak decay `L_env ≤ (1/15)·S` (`leak_geo_decay`).
  * `AnchorDominatesProd w` — the truncation-edge bridge `2·(acN(s+1,s)·acN(s+1,s+2)) ≤ S`.

HONEST VERDICT.  This module PROVES the diagonal band of the `symMinor` Gershgorin form in full
(pointwise and aggregate) and REDUCES the single Gershgorin wall
(`AutoconvGershgorin.SymMinorGershgorin`) to two honest residuals — the combinatorial-core leak
decay and the truncation-edge bridge — connected by PROVED scalar threshold arithmetic
(`δ ≤ 43/30`).  It does NOT inhabit either residual.  This is a structural sharpening of one
box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.SymMinorGershgorinProof

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SymMinorGershgorinProof.symMinor_diag_reserve
#print axioms YMGap.Continuum.SymMinorGershgorinProof.anchorR_nonneg
#print axioms YMGap.Continuum.SymMinorGershgorinProof.diag_term_lower
#print axioms YMGap.Continuum.SymMinorGershgorinProof.anchorSum_nonneg
#print axioms YMGap.Continuum.SymMinorGershgorinProof.anchorDiag_lower
#print axioms YMGap.Continuum.SymMinorGershgorinProof.gershgorinOfResiduals
#print axioms YMGap.Continuum.SymMinorGershgorinProof.acN_defect_reserve_of_residuals
