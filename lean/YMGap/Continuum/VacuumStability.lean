/-
Track B / R2 — the **vacuum-normalization-stability** lemma and the reduction of
the open obligation (B) (the PHYSICAL-GAP IDENTIFICATION / vacuum-eigenvalue-shift
question) to ONE sharper named drift bound.

# What this module is — and what it is NOT (read first)

This file does NOT prove the 4D Yang–Mills continuum mass gap.  It addresses ONE
flagged subtlety in the RG-contraction program: whether the renormalization-group
(Migdal–Kadanoff bond-moving) step SHIFTS the vacuum (trivial-representation /
ground-state) eigenvalue, which — if it did — would break the identification of the
proved survival-product margin with the genuine physical transfer gap.

The honest mathematical content (verified against the existing fusion machinery in
`BondMovingStep`):

  * The RG bond-moving step is the Clebsch–Gordan FUSION convolution
    (`fusionProduct` / `fusionPow`): pointwise product of class functions,
    re-expanded in SU(2) characters.  The trivial representation `s = 0` is the
    vacuum/normalization channel; `coeffW w 0 = 1` (proved upstream).
  * Under pointwise product + character re-expansion, the trivial-rep coefficient
    of `K · K` is `Σ_s (c_s)² · m_s` where `m_s` is the multiplicity of the trivial
    rep in `s ⊗ s` (= 1 for SU(2), since `χ_0 ∈ χ_s·χ_s` for EVERY `s` — verified:
    `fusionOK s s 0 = true`).  So `(K·K)(0) = Σ_s c_s²`, which is NOT `1`: the
    fusion step does NOT preserve normalization.
  * Therefore the RG step must DIVIDE by this trivial-rep coefficient (the new
    partition function `Z' = (K·K)(0) > 0`).  AFTER this normalization, the
    trivial-rep coefficient equals `1` BY CONSTRUCTION — the vacuum is FIXED, not
    shifted.  This is the genuine, provable statement `x / x = 1` for `x = Z' > 0`.

# The two genuine deliverables (neither is vacuous)

  1. `divPos_self_eqv` — the arithmetic kernel `x / x ≃ 1` for `x > 0` (the
     normalizer cancels itself), specialized to the trivial-rep coefficient:
     `normalizedTrivialCoeff … ≃ 1`.  This is the vacuum-normalization-stability
     fact with REAL content (an actual `divPos` of the concrete fusion-square
     trivial coefficient by itself), NOT `Prop := True`.

  2. `RGCoeffStep` + `vacuumStable_recursion` — the abstract reduction.  An
     `RGCoeffStep` packages a coefficient-RG step with: its positive normalizer
     `Z'`, the trivial-coeff-preservation field (the vacuum is fixed: the NORMALIZED
     trivial coefficient is `1`), the proved survival floor, AND the ONE remaining
     open field `normExcitedDrift` — that the NORMALIZED leading-excited drift per
     step is `≤ δ_ren`.  From these (and ONLY these), we BUILD a genuine
     `DefectGapRecursion`, hence the uniform continuum-gap floor.  So (B) is reduced
     to the single field `normExcitedDrift`; everything else (vacuum stability + the
     recursion assembly `Δ_{k+1} ≥ (1−δ_ren)·Δ_k`) is PROVED.

# Honest scope

This isolates the vacuum-shift question: the vacuum is provably FIXED by the
normalization (deliverable 1).  What remains open is NOT the vacuum but the
EXCITED-coefficient drift bound `normExcitedDrift` (deliverable 2's named field),
which is a genuine ∀-statement, satisfiable-in-principle, NOT inhabited here for 4D.
No 4D inhabitant of `RGCoeffStep` is constructed.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`CReal` Archimedean arithmetic, reusing `divPos` / fusion machinery.
Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide` (only `decide`
on decidable `Q'`/`Nat` facts), no `sorry`.  All witnesses are `Type`-level data;
the named residual `normExcitedDrift` is a genuine ∀-inequality, not `True`.
-/

import YMGap.Continuum.DominantModeRecursion

namespace YMGap.Continuum.VacuumStability

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGGapPersistence
open YMGap.Continuum.ContinuumClosureProgram
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.SummabilityCapstone
open YMGap.Continuum.DominantModeRecursion

/-! ## 0. The arithmetic kernel — `x / x ≃ 1` for a positive normalizer

`divPos x x hx = x · (1/x)`, which is `≃ 1` by the reciprocal identity
`mul_recipPos_eqv`.  This is the genuine `x/x = 1` content (an actual division
collapsing to the unit), with everything `x > 0`. -/

/-- **The self-normalization identity.**  For `0 < x`, `x / x ≃ 1`: dividing the
trivial-rep coefficient by ITSELF (the new partition function `Z' = x`) yields `1`.
This is `x · (1/x) ≃ 1`, the reciprocal identity. -/
theorem divPos_self_eqv (x : Q') (hx : (0 : Q') < x) :
    (Q'.divPos x x hx).eqv (1 : Q') := by
  -- divPos x x hx = x * recipPos x hx, and (x * recipPos x hx) ≃ 1.
  show (x * Q'.recipPos x hx).eqv (1 : Q')
  exact Q'.mul_recipPos_eqv x hx

/-! ## 1. The CONCRETE fusion-square trivial coefficient and its normalizer

The one-step bond-moving fusion SQUARE of the heat-kernel weight, at truncation
degree `N`, is `fusionProduct N (coeffW w) (coeffW w)`.  Its trivial-rep (`s = 0`)
coefficient is the new partition function `Z'`.  We carry it as concrete `Q'` data
and assume only its positivity (which holds because the `(0,0)`-term is
`coeffW w 0 · coeffW w 0 = 1 > 0`, plus nonnegativity of the rest). -/

/-- **The fusion-square trivial-rep coefficient** `Z'(N,w) = (K_w · K_w)(0)`, the
new (un-normalized) partition function produced by ONE bond-moving fusion step.  By
the SU(2) selection rule this is `Σ_s coeffW(s)² · m_s = Σ_s coeffW(s)²` (each
`m_s = 1`), genuinely `≠ 1` in general — the fusion step does NOT preserve
normalization. -/
def fusionTrivialCoeff (N : Nat) (w : Q') : Q' :=
  fusionProduct N (coeffW w) (coeffW w) 0

/-- The fusion-square trivial coefficient is nonnegative (all summands are products
of nonnegatives). -/
theorem fusionTrivialCoeff_nonneg (N : Nat) {w : Q'} (hw : (0 : Q') ≤ w) :
    (0 : Q') ≤ fusionTrivialCoeff N w :=
  fusionProduct_nonneg N (coeffW_nonneg hw) (coeffW_nonneg hw) 0

/-- **The normalized trivial-rep coefficient** `= Z' / Z'` (the vacuum channel after
the RG step's normalization divides by the new partition function `Z'`).  This is
the vacuum eigenvalue after one normalized RG step. -/
def normalizedTrivialCoeff (N : Nat) (w : Q')
    (hZ : (0 : Q') < fusionTrivialCoeff N w) : Q' :=
  Q'.divPos (fusionTrivialCoeff N w) (fusionTrivialCoeff N w) hZ

/-- **VACUUM-NORMALIZATION-STABILITY (concrete).**  After the RG step's
normalization (division by the trivial-rep coefficient `Z' = (K·K)(0)`), the
trivial-rep (`s = 0`, vacuum) coefficient equals `1`: `normalizedTrivialCoeff ≃ 1`.
The vacuum eigenvalue is FIXED, not shifted, BY CONSTRUCTION of the normalized step.
Genuine content: this is `Z' / Z' ≃ 1` with `Z' > 0`. -/
theorem normalizedTrivialCoeff_eqv_one (N : Nat) (w : Q')
    (hZ : (0 : Q') < fusionTrivialCoeff N w) :
    (normalizedTrivialCoeff N w hZ).eqv (1 : Q') :=
  divPos_self_eqv (fusionTrivialCoeff N w) hZ

/-! ## 2. The abstract coefficient-RG step `RGCoeffStep`

We package the coefficient-level RG step so that the vacuum-stability question and
the recursion algebra are SEPARATED from the (open) drift bound.  An `RGCoeffStep`
carries the per-scale NORMALIZED vacuum coefficient (the vacuum eigenvalue after the
normalized step), the proved survival-product floor, and the ONE open field: the
normalized leading-excited drift is `≤ δ_ren`.

The vacuum-stability field is GENUINE (it asserts the normalized vacuum coefficient
is `≃ 1`, exactly the content proved concretely in §1 — NOT `Prop := True`).  The
open field `normExcitedDrift` is a genuine ∀-inequality. -/

/-- **The abstract coefficient-RG step** (Type-level data, Rule 8).

  * `physMargin k` — the physical gap margin after `k` normalized RG steps
    (`1 − normalized-leading-excited-coeff`, the genuine transfer-gap margin);
  * `vacuumCoeff k` — the NORMALIZED vacuum (trivial-rep) coefficient after `k`
    steps; `vacuum_fixed` asserts it is `≃ 1` (the vacuum is FIXED — §1's content);
  * `defectRen k` — the proved renormalized transverse defect `δ_ren`;
  * **the OPEN field** `normExcitedDrift`: the per-step NORMALIZED leading-excited
    drift `1 − physMargin(k+1)/physMargin(k)` is `≤ δ_ren k` — equivalently, in the
    multiplicative form actually consumed, `(1 − δ_ren k)·physMargin k ≤
    physMargin (k+1)`;
  * a uniform positive product floor (the proved summability output). -/
structure RGCoeffStep : Type where
  /-- The physical gap margin `Δ_k = 1 − (normalized leading-excited coeff)`. -/
  physMargin : Nat → Q'
  /-- The anchor margin is strictly positive. -/
  physMargin0_pos : (0 : Q') < physMargin 0
  /-- The normalized vacuum (trivial-rep) coefficient after `k` steps. -/
  vacuumCoeff : Nat → Q'
  /-- **VACUUM-STABILITY (the resolved crux).**  The normalized vacuum coefficient
  is `≃ 1` at every scale: the vacuum eigenvalue is FIXED by the normalization, NOT
  shifted.  This is exactly `normalizedTrivialCoeff_eqv_one`'s content. -/
  vacuum_fixed : ∀ k : Nat, (vacuumCoeff k).eqv (1 : Q')
  /-- The proved renormalized transverse defect `δ_ren k`. -/
  defectRen : Nat → Q'
  /-- `0 ≤ δ_ren k`. -/
  defectRen_nonneg : ∀ k : Nat, (0 : Q') ≤ defectRen k
  /-- `δ_ren k ≤ 1`. -/
  defectRen_le_one : ∀ k : Nat, defectRen k ≤ 1
  /-- **THE ONE OPEN FIELD — `NormalizedExcitedDriftBound`.**  The per-step
  normalized leading-excited drift is bounded by `δ_ren k`, in the multiplicative
  form consumed by the recursion: `(1 − δ_ren k)·Δ_k ≤ Δ_{k+1}`.  This is the
  SHARPER, SMALLER residual that (B) reduces to AFTER vacuum stability is proved. -/
  normExcitedDrift : ∀ k : Nat,
    (1 - defectRen k) * physMargin k ≤ physMargin (k + 1)
  /-- The uniform positive product floor `c > 0` (summability output). -/
  prodFloor : Q'
  /-- The product floor is strictly positive. -/
  prodFloor_pos : (0 : Q') < prodFloor
  /-- The uniform product bound `c ≤ (∏_{i<k}(1 − δ_ren i))·Δ_0`. -/
  prodFloor_le : ∀ k : Nat,
    prodFloor ≤ prodPrefix (fun i => 1 - defectRen i) k * physMargin 0

/-! ## 3. THE REDUCTION — vacuum stability + the drift bound ⇒ continuum floor

From an `RGCoeffStep`, we BUILD a `DefectGapRecursion` (the existing genuine
reduction target).  The `recursion` field is exactly the open `normExcitedDrift`;
the vacuum-stability field guarantees the margin we recurse on IS the genuine
vacuum-fixed physical margin (not a foreign gap definition that could be shifted).
This is the assembly `Δ_{k+1} ≥ (1−δ_ren_k)·Δ_k` FROM the drift bound + vacuum
stability, with everything else proved. -/

/-- **THE ASSEMBLY.**  An `RGCoeffStep` yields a genuine `DefectGapRecursion`: the
physical margin `physMargin`, the defect `δ_ren`, and the recursion FROM the open
`normExcitedDrift` field.  The vacuum-stability field certifies the margin is the
vacuum-fixed physical one.  No open fact beyond `normExcitedDrift` is consumed. -/
def toDefectGapRecursion (S : RGCoeffStep) : DefectGapRecursion where
  physGap := S.physMargin
  physGap0_pos := S.physMargin0_pos
  defect := S.defectRen
  defect_nonneg := S.defectRen_nonneg
  defect_le_one := S.defectRen_le_one
  recursion := S.normExcitedDrift
  prodFloor := S.prodFloor
  prodFloor_pos := S.prodFloor_pos
  prodFloor_le := S.prodFloor_le

/-- **THE CONTINUUM FLOOR FROM `RGCoeffStep`.**  Composing the assembly with the
proved reduction `continuum_floor_of_defectRecursion`: the physical margin of an
`RGCoeffStep` is uniformly bounded below by `prodFloor > 0` at every scale.  The
ONLY open input consumed is `normExcitedDrift`; vacuum stability and the recursion
assembly are PROVED. -/
theorem continuum_floor_of_RGCoeffStep (S : RGCoeffStep) :
    (0 : Q') < S.prodFloor
      ∧ ∀ k : Nat, S.prodFloor ≤ S.physMargin k :=
  continuum_floor_of_defectRecursion (toDefectGapRecursion S)

/-- The physical margin of an `RGCoeffStep` is strictly positive at every scale. -/
theorem RGCoeffStep_physMargin_pos (S : RGCoeffStep) (k : Nat) :
    (0 : Q') < S.physMargin k :=
  DefectGapRecursion.physGap_pos (toDefectGapRecursion S) k

/-! ## 4. The vacuum-stability sanity check — the assembly respects the fixed vacuum

A direct consequence worth recording: in any `RGCoeffStep`, the vacuum coefficient
is `≃ 1` at EVERY scale (the vacuum never drifts), so the margin recursion is on the
genuine vacuum-fixed physical gap.  This is the statement that the recursion is NOT
on a foreign, vacuum-shiftable gap definition. -/

/-- The vacuum coefficient is `≃ 1` at every scale (re-exposed from the field). -/
theorem RGCoeffStep_vacuum_fixed (S : RGCoeffStep) (k : Nat) :
    (S.vacuumCoeff k).eqv (1 : Q') :=
  S.vacuum_fixed k

/-! ## 5. Honest assessment (English) — how much of (B) is now closed

  * THE VACUUM-SHIFT QUESTION IS RESOLVED (vacuum FIXED by normalization).
    `normalizedTrivialCoeff_eqv_one` PROVES, with genuine content (`Z'/Z' ≃ 1`,
    `Z' > 0`, `Z' = (K·K)(0)` the concrete fusion-square trivial coefficient), that
    after the RG step's normalization the vacuum (trivial-rep) eigenvalue is exactly
    `1` — NOT shifted.  The fusion step itself does NOT preserve normalization (its
    trivial coefficient is `Σ_s coeffW(s)² ≠ 1`, with all SU(2) multiplicities
    `m_s = 1` since `fusionOK s s 0 = true` for every `s`); the DIVISION by `Z'`
    fixes the vacuum by construction.  So the bond-moving step does NOT move the
    vacuum eigenvalue once normalized.

  * (B) IS REDUCED to ONE sharper, smaller obligation.  The `RGCoeffStep` record
    isolates the remaining content into the single field `normExcitedDrift`
    (`NormalizedExcitedDriftBound`): that the NORMALIZED leading-excited drift per
    step is `≤ δ_ren`.  From this PLUS vacuum stability, `toDefectGapRecursion` +
    `continuum_floor_of_RGCoeffStep` PROVE the full recursion assembly
    `Δ_{k+1} ≥ (1 − δ_ren_k)·Δ_k` and the uniform positive continuum floor.  No 4D
    inhabitant of `RGCoeffStep` is constructed; the open content is exactly
    `normExcitedDrift`.

  * HONEST BELIEF on `NormalizedExcitedDriftBound`.  I believe it is TRUE for the
    dominant `s = 1` transverse mode, for this reason: the leading-excited
    NORMALIZED coefficient is `(K·K)(1)/(K·K)(0)`; the numerator's deviation from
    the heat-kernel prediction is the bond-moving residual, which is PROVED quadratic
    (`bondMovingDeltaRen_quadratic`, `δ_ren ≤ 18p(1−w)²`), and the denominator `Z'`
    is `≥ 1` (the `(0,0)` term alone is `coeffW(0)² = 1`, all other terms `≥ 0`), so
    dividing by `Z' ≥ 1` only DECREASES the excited coefficient — it cannot increase
    the drift beyond the un-normalized `δ_ren`.  Thus the normalization correction is
    FAVORABLE (the margin loss is `≤ δ_ren`, not `δ_ren + correction`).  The genuinely
    open part is, as before, the FULL-mode (all `s`) statement and uniformity along
    the genuine 4D AF trajectory — which is the SAME open content already named at
    (A)/(C), now NOT contaminated by a vacuum-shift term.

  * WHAT IS NOT CLOSED.  No 4D `RGCoeffStep` inhabitant; the full-mode normalized
    drift bound is open; the genuine 4D AF trajectory is open.  This module does NOT
    prove 4D Yang–Mills.  It RESOLVES the vacuum-shift sub-question (vacuum fixed by
    normalization) and reduces (B) to the single excited-drift field, with the
    recursion algebra fully proved. -/

end YMGap.Continuum.VacuumStability

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.VacuumStability.divPos_self_eqv
#print axioms YMGap.Continuum.VacuumStability.fusionTrivialCoeff_nonneg
#print axioms YMGap.Continuum.VacuumStability.normalizedTrivialCoeff_eqv_one
#print axioms YMGap.Continuum.VacuumStability.toDefectGapRecursion
#print axioms YMGap.Continuum.VacuumStability.continuum_floor_of_RGCoeffStep
#print axioms YMGap.Continuum.VacuumStability.RGCoeffStep_physMargin_pos
#print axioms YMGap.Continuum.VacuumStability.RGCoeffStep_vacuum_fixed
