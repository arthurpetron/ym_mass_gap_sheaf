/-
Track B / R2 — THE CONVERGED CLAY CORE, made concrete: the non-perturbative
CONDENSATE / renormalon scale `ε_k = exp(−c/(β₀ g_k²))` as a GEOMETRIC additive
erosion, its SUMMABILITY and ANCHOR-DOMINANCE (both PROVED, upper bounds), and the
honest verdict on whether it is CONSTRUCTED or whether the condensate GENERATION /
POSITIVITY is the genuine 4D-Yang–Mills residual.

# Where everything converges (`CAPSTONE §5`, `borel §0`, `transmutation §4`)

Both the block-spin route and the interacting-measure/Borel route converge on ONE
object: the additive erosion `ε_k` of `TrueMarginRecursionPhysical`.  The Borel
scaffold (`BorelRenormalonScaffold`) identified it: the confining-theory renormalon
ambiguity is `~ exp(−c/(β₀ g²))` = the condensate / mass-gap scale, and it coincides
EXACTLY with `ε_k`.  This module makes that identification concrete and audits it.

# The condensate is GEOMETRIC (task point 1)

Asymptotic freedom (PROVED shape, `AFRateModulus.rate_upper`) gives
`g_k² ≍ 1 − w_k ≍ A/(k+B)`.  Hence

    ε_k  =  exp(−c/(β₀ g_k²))  =  exp(−c(k+B)/(β₀A))  =  K · r^k ,
        r = exp(−c/(β₀A)) ∈ (0,1),   K = exp(−cB/(β₀A)),

a GEOMETRIC sequence (`condensateCReal`, the genuine irrational CReal via `expNeg`;
`condensate_creal_nonneg` / `condensate_creal_le_one` — it is a bona-fide CReal in
`[0,1]`).  For the SU(2) `β₀ = 22/3`, `A=1`, deep-UV anchor `B=12` (`w_0=11/12`),
`c=4`: `r_real = 0.5796`, `K_real = 0.001437` (mpmath dps 50, `condensate_numerics.py`).

# SUMMABILITY + ANCHOR-DOMINANCE — the PROVED (upper-bound) direction

A rational geometric MAJORANT `condTerm_k = K'·r'^k` with `K'=1/100 ≥ K_real`,
`r'=3/5 ≥ r_real` dominates the condensate at every `k` (numerically verified; the
domination itself is the OPEN renormalon identification, see below).  For the rational
majorant BOTH obligations are PROVED, axiom-clean, Lean-core:

  * `cond_tailSum_le` — `∑_{j<N} K'·r'^j ≤ K'/(1−r') = 1/40 =: Bε` (∀N), the geometric
    closed form (reusing the PROVED `RationalTail.geometric_tail_closure`).  This is
    the geometric analog of the eigenvalue-shift telescope — the condensate is
    GEOMETRICALLY SUMMABLE, `Σ ε_k < ∞`.
  * `cond_anchorDom` — `Bε = 1/40 < 3/10 ≤ m_phys` (kernel `decide`), the
    anchor-dominance `Σ ε_k < m_phys` with slack `≈ 0.275`.
  * `condensate_floor` — the CONDITIONAL producer: given the real additive step with a
    geometric-majorized erosion and the anchor `Bε < margin 0`, the PROVED
    `additiveErosion_uniform_floor` yields the UNIFORM STRICTLY-POSITIVE continuum
    floor `margin 0 − Bε` (∀k).  Open binders on the real margin/erosion/step: NOT an
    inhabitant of any guarded bundle.

# THE CRUX — is `ε_k` CONSTRUCTED, or is the CONDENSATE POSITIVITY the residual?

MAXIMALLY ADVERSARIAL verdict.  Summability and anchor-dominance are UPPER bounds on
the erosion (`ε_k` SMALL ⟹ gap survives) — the EASY direction, PROVED above.  They do
NOT close the mass gap.  The two genuinely open inputs — the hypotheses `hmajorant` and
`hanchor` of `condensate_floor` — are the residual:

  1. **THE RENORMALON IDENTIFICATION** (`hmajorant : εReal k ≤ condTerm k`).  That the
     REAL 4D block-spin erosion IS (bounded by) the condensate `exp(−c/β₀g²)`.  The
     Borel scaffold PROVED this is NOT the perturbative Borel sum
     (`connected_reorg_no_resummation`, `IRRenormalonPositiveAxis` UNINHABITED); it is
     the non-perturbative renormalon — a PHYSICS EXPECTATION, not a construction.

  2. **THE CONDENSATE POSITIVITY / GENERATION** (`hanchor : Bε < margin 0`, i.e.
     `margin 0 = m_phys > 0`).  This is the mass gap itself: that the non-perturbative
     RG GENERATES a NONZERO condensate scale `Λ = a·exp(−1/(2β₀g²))`, so the physical
     margin at the UV anchor is a genuine `m_phys > 0`.  `DimensionlessMarginTransmutation`
     proved this for the IDEAL self-similar flow — but there `m_phys = 1 − e^{−1/e}` is
     DIALED by the seed `e^{−1}` (the zero-defect idealization).  The REAL 4D flow's
     generation of a nonzero condensate is the open R2.

  **The exp-positivity red herring.**  `exp(−x) > 0` is TRIVIALLY true for the function
  `exp` (`condensate_creal_nonneg`: the condensate CReal is `≥ 0`, free).  So the mass
  gap is NOT "is `exp(−c/β₀g²) ≠ 0`" — that is free.  It is "does the REAL theory's
  non-perturbative scale EQUAL a nonzero `Λ`" (input 2) and "is the real erosion the
  condensate" (input 1).  Both are the genuine 4D content, UNINHABITED.

# Guard / STOP (mandatory — this is the mass gap)

`condensate_floor` is a CONDITIONAL producer (open binders on `margin`, `εReal`,
`hmajorant`, `hstep`, `hanchor`).  It does NOT construct `TrueMarginRecursionPhysical`,
`TrueMarginRecursionSummable`, `SingleStepDefectBound`, `UniformSpacingFloor`,
`Tier0Scorecard`, `ClayTarget`, `ClayTargetPinned`, or `FrontierDAG`.  No guarded
bundle is inhabited; no STOP condition is tripped.  The `CondensateGeneration`-class
inputs are, per the `CAPSTONE §4` systematic caveat, bounds on free fields (hence
vacuously fakeable by a constant `εReal ≡ 0` / dialed `margin`) — they are honestly
OPEN because we REFUSE the fake, not because the types are uninhabitable.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` + the `expNeg` CReal (nonneg only, trivial).  Every load-bearing
declaration gated with `#print axioms`; permitted output `propext` / `Quot.sound`.  No
`Classical.*`, no `native_decide` (only `decide` on closed decidable `Q'` facts), no
`sorry`.
-/
import YMGap.Continuum.AdditiveErosionAdequacy
import YMGap.Continuum.AnchorDominanceEigenvalueShift
import YMGap.Constructive.GeometricTail
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.CondensateGeometric

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.AnchorDominance
open YMGap.Constructive.RationalTail

/-! ## 1. The condensate as a genuine geometric CReal (task point 1) -/

/-- The AF rate `c/(β₀A)` for the SU(2) one-loop `β₀ = 22/3`, `A = 1`, action `c = 4`:
`c/(β₀A) = 4/(22/3) = 6/11` (rational).  The geometric ratio of the condensate is
`r = exp(−6/11) = 0.5796` (`condensate_numerics.py`, mpmath dps 50). -/
def condRateExp : Q' := Q'.mkPos 6 11 (by decide)

/-- The deep-UV anchor offset `B = 12` (the AF trajectory cutoff `w_0 = 11/12`). -/
def condOffset : Nat := 12

/-- **The condensate exponent** `c(k+B)/(β₀A) = (6/11)·(k+12) ≥ 0`. -/
def condExponent (k : Nat) : Q' := condRateExp * Q'.ofNat (k + condOffset)

/-- The condensate exponent is nonnegative (product of nonnegatives). -/
theorem condExponent_nonneg (k : Nat) : (0 : Q') ≤ condExponent k :=
  Q'.mul_nonneg _ _ (by decide) (ExpNeg.ofNat_nonneg' (k + condOffset))

/-- **THE NON-PERTURBATIVE CONDENSATE `ε_k = exp(−c(k+B)/(β₀A))` as a genuine CReal**
(via `CRealExp`).  This is the renormalon / mass-gap scale of `BorelRenormalonScaffold`,
geometric in `k` (ratio `exp(−6/11)`), built as an honest irrational constructive real. -/
def condensateCReal (k : Nat) : CReal := ExpNeg.expNeg (condExponent k) (condExponent_nonneg k)

/-- **The condensate CReal is `≥ 0`** — trivially (`expNeg_geRat_zero`: `exp` is
nonnegative).  This is the exp-positivity RED HERRING: constructing `exp(−c/β₀g²) > 0`
as a CReal is FREE, so the mass gap does NOT reduce to it. -/
theorem condensate_creal_nonneg (k : Nat) :
    ExpPos.geRat (condensateCReal k) 0 :=
  expNeg_geRat_zero (condExponent k) (condExponent_nonneg k)

/-- **The condensate CReal is `≤ 1`** (`expNeg_le_one`): a bona-fide CReal in `[0,1]`. -/
theorem condensate_creal_le_one (k : Nat) :
    CReal.leRat (condensateCReal k) 1 :=
  CReal.expNeg_le_one (condExponent k) (condExponent_nonneg k)

/-! ## 2. The rational geometric MAJORANT `condTerm_k = K'·r'^k` -/

/-- Rational geometric ratio `r' = 3/5 ≥ r_real = exp(−6/11) = 0.5796`. -/
def condRate : Q' := Q'.mkPos 3 5 (by decide)

/-- Rational geometric head `K' = 1/100 ≥ K_real = exp(−72/11) = 0.001437`. -/
def condHead : Q' := Q'.mkPos 1 100 (by decide)

/-- The geometric closed-form budget `Bε = K'/(1−r') = (1/100)/(2/5) = 1/40`. -/
def condSum : Q' := Q'.mkPos 1 40 (by decide)

/-- **The rational geometric erosion majorant** `condTerm_k = K'·r'^k` — the
`Q'`-valued summable stand-in the additive-erosion recursion consumes.  It dominates the
genuine condensate `condensateCReal k` at every `k` (numerically verified; the
domination is the OPEN renormalon identification). -/
def condTerm (k : Nat) : Q' := condHead * condRate ^ k

/-- `condTerm_k ≥ 0`. -/
theorem condTerm_nonneg (k : Nat) : (0 : Q') ≤ condTerm k :=
  Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg condRate (by decide) k)

/-- **The geometric one-step recurrence** `K' + r'·Bε ≤ Bε`
(`1/100 + (3/5)(1/40) = 1/40`, kernel `decide`) — the hypothesis of
`geometric_tail_closure`, certifying `Bε` is the closed geometric sum. -/
theorem cond_recurrence : condHead + condRate * condSum ≤ condSum := by decide

/-! ## 3. SUMMABILITY — the geometric closed form (PROVED, task points 1/2) -/

/-- Bridge: the tail sum from `0` equals the finite partial sum (identical recursion,
`0 + M = M`).  Lets the `additiveErosion` engine's `tailSum` consume
`geometric_tail_closure`'s `finSum`. -/
theorem tailSum_condTerm_eq_finSum :
    ∀ N, tailSum condTerm 0 N = finSum condTerm N
  | 0 => rfl
  | M + 1 => by
    show tailSum condTerm 0 M + condTerm (0 + M) = finSum condTerm M + condTerm M
    rw [tailSum_condTerm_eq_finSum M, Nat.zero_add]

/-- **THE GEOMETRIC SUMMABILITY BUDGET.**  `∑_{j<N} K'·r'^j ≤ Bε = 1/40` for every
window `N` — the condensate erosion is GEOMETRICALLY SUMMABLE.  Reuses the PROVED
`RationalTail.geometric_tail_closure` (the closed-form `K'/(1−r')` from the one-step
recurrence `cond_recurrence`).  The geometric analog of the eigenvalue-shift telescope
`eigShift_tailSum_le`. -/
theorem cond_tailSum_le (N : Nat) : tailSum condTerm 0 N ≤ condSum := by
  rw [tailSum_condTerm_eq_finSum N]
  exact geometric_tail_closure condHead condRate condSum (by decide) (by decide)
    cond_recurrence N

/-! ## 4. ANCHOR-DOMINANCE — `Σ ε_k < m_phys` (PROVED, task point 2) -/

/-- **THE ANCHOR-DOMINANCE INEQUALITY (kernel `decide`, zero-axiom).**
`Bε = 1/40 < 3/10 ≤ m_phys`.  The accumulated geometric condensate erosion is strictly
dominated by the transmuted margin lower bound `mPhysLB = 3/10`
(`m_phys = 1 − e^{−1/e} = 0.30780`), with comfortable slack `≈ 0.275`.  Compare the
telescoping eigenvalue-shift budget `1 − w_0³ = 0.22975` — the geometric condensate
budget is far smaller (deep-UV-anchored geometric decay). -/
theorem cond_anchorDom : condSum < mPhysLB := by decide

/-! ## 5. THE CONDITIONAL FLOOR PRODUCER (guard-safe) — task point 4 -/

/-- **GEOMETRIC CONDENSATE ⟹ POSITIVE CONTINUUM FLOOR (conditional producer).**

Given the real dimensionless margin `margin_k` with nonnegative anchor, a real additive
erosion `εReal_k ≥ 0` that is MAJORIZED by the geometric condensate
(`hmajorant : εReal k ≤ condTerm k = K'·r'^k`), obeying the purely-additive step
`margin (k+1) ≥ margin k − εReal_k`, and the **anchor-dominance** `Bε < margin 0`, the
PROVED `additiveErosion_uniform_floor` yields the UNIFORM STRICTLY-POSITIVE continuum
floor

    ∀ k,  margin 0 − Bε  ≤  margin k    and    0 < margin 0 − Bε ,     Bε = 1/40.

OPEN BINDERS on `margin`, `εReal`, `hmajorant`, `hstep`, `hanchor` — a CONDITIONAL
producer, NOT an inhabitant of any guarded/frontier bundle.  The TWO open inputs are the
genuine 4D residual:
  * `hmajorant` = **the renormalon identification** (real erosion = the condensate);
  * `hanchor`   = **the condensate positivity / generation** (`margin 0 = m_phys > 0`). -/
theorem condensate_floor
    (margin εReal : Nat → Q')
    (_hεnn : ∀ k, (0 : Q') ≤ εReal k)
    (hmajorant : ∀ k, εReal k ≤ condTerm k)
    (hm0 : (0 : Q') ≤ margin 0)
    (hstep : ∀ k, margin k - εReal k ≤ margin (k + 1))
    (hanchor : condSum < margin 0) :
    ∀ k, (margin 0 - condSum ≤ margin k) ∧ (0 : Q') < margin 0 - condSum := by
  -- (1) majorize the real step by the condensate step: margin k − condTerm k ≤ margin (k+1).
  have hstepCond : ∀ k, margin k - condTerm k ≤ margin (k + 1) := by
    intro k
    have hneg : -(condTerm k) ≤ -(εReal k) := qNegLeNeg (hmajorant k)
    have hle : margin k + -(condTerm k) ≤ margin k + -(εReal k) :=
      Q'.add_le_add_left (margin k) _ _ hneg
    exact Q'.le_trans' _ _ _ hle (hstep k)
  -- (2) put the step into the engine's (1−δ)·margin shape with δ ≡ 0.
  have e0 : (((1 : Q') - 0) * margin 0).eqv (margin 0) := by
    rw [Q'.sub_zero']; exact Q'.one_mul_eqv (margin 0)
  have hstep' : ∀ k,
      ((1 : Q') - (fun _ => (0 : Q')) k) * margin k - condTerm k ≤ margin (k + 1) := by
    intro k
    have ek : (((1 : Q') - 0) * margin k).eqv (margin k) := by
      rw [Q'.sub_zero']; exact Q'.one_mul_eqv (margin k)
    have e2 : (((1 : Q') - 0) * margin k + -(condTerm k)).eqv
        (margin k + -(condTerm k)) :=
      Q'.add_eqv_congr_right _ _ (-(condTerm k)) ek
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e2) (hstepCond k)
  -- (3) anchor-dominance in the engine's shape.
  have hanchor' : condSum < ((1 : Q') - 0) * margin 0 := qLtLe hanchor (Q'.ge_of_eqv e0)
  -- (4) apply the PROVED adequacy engine with δ ≡ 0, Bδ = 0, ε = condTerm, Bε = condSum.
  have H := additiveErosion_uniform_floor margin (fun _ => (0 : Q')) condTerm
    (0 : Q') condSum hstep'
    (fun _ => Q'.le_refl' 0) (fun _ => qZeroLeOne)
    condTerm_nonneg hm0
    (fun k => zero_tailSum_le k) cond_tailSum_le hanchor'
  -- (5) convert (1−0)·margin 0 back to margin 0 in the conclusion.
  have hconv : (((1 : Q') - 0) * margin 0 + -condSum).eqv (margin 0 + -condSum) :=
    Q'.add_eqv_congr_right _ _ (-condSum) e0
  intro k
  obtain ⟨hle, hpos⟩ := H k
  exact ⟨Q'.le_trans' _ _ _ (Q'.ge_of_eqv hconv) hle,
         qLtLe hpos (Q'.le_of_eqv hconv)⟩

/-- **The floor is strictly positive at the transmuted anchor** (kernel `decide`): the
anchor floor `mPhysLB − Bε = 3/10 − 1/40 = 11/40 > 0`.  Combined with `condensate_floor`
and `margin 0 ≥ mPhysLB`, the continuum margin stays `> 0` at every scale — GIVEN the two
open inputs. -/
theorem cond_floor_pos_at_anchor : (0 : Q') < mPhysLB - condSum := by decide

/-- **Anchor-dominance from the transmutation anchor.**  If the dimensionless margin at
the deep-UV anchor satisfies `margin 0 ≥ mPhysLB = 3/10` (the transmuted `m_phys`,
`DimensionlessMarginTransmutation`), then `condensate_floor`'s anchor hypothesis holds. -/
theorem cond_anchor_from_mphys_lb (margin : Nat → Q') (hm0lb : mPhysLB ≤ margin 0) :
    condSum < margin 0 := qLtLe cond_anchorDom hm0lb

/-! ## 6. Honest verdict (AGENTS.md Rule 6 / Rule 9) -/

/-- **PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]` or fewer):**
  * `condensateCReal` / `condensate_creal_nonneg` / `condensate_creal_le_one` — the
    non-perturbative condensate `ε_k = exp(−c(k+B)/β₀A)` as a genuine CReal in `[0,1]`
    (geometric, ratio `exp(−6/11)`), its positivity TRIVIAL (the red herring).
  * `cond_tailSum_le` — the condensate erosion is GEOMETRICALLY SUMMABLE
    `∑ ε_k ≤ Bε = 1/40` (reusing PROVED `geometric_tail_closure`).
  * `cond_anchorDom` — ANCHOR-DOMINANCE `Bε = 1/40 < 3/10 ≤ m_phys` (kernel `decide`).
  * `condensate_floor` — the two proved bounds ⟹ uniform positive continuum floor
    `margin 0 − Bε > 0` (via the PROVED adequacy engine), conditional on the two open
    inputs; open binders, guard-safe.

**VERDICT — the converged Clay core is NOT constructed; the condensate GENERATION is the
residual.**  The condensate `ε_k = exp(−c/β₀g²)` is GEOMETRIC, its erosion is
GEOMETRICALLY SUMMABLE (`cond_tailSum_le`), and it is ANCHOR-DOMINATED
(`cond_anchorDom`) — but these are UPPER bounds on the erosion (the EASY direction:
`ε_k` small ⟹ gap survives), and they do NOT close the mass gap.  What the mass gap
needs, and what stays OPEN (both the hypotheses of `condensate_floor`, both UNINHABITED):

  1. **The renormalon identification** — that the REAL 4D block-spin erosion IS the
     condensate `exp(−c/β₀g²)` (`hmajorant`).  `BorelRenormalonScaffold` PROVED this is
     NOT the perturbative Borel sum; it is the non-perturbative renormalon, a PHYSICS
     EXPECTATION.

  2. **The condensate positivity / generation** — that the non-perturbative RG GENERATES
     a NONZERO condensate `Λ = a·exp(−1/2β₀g²)`, so `margin 0 = m_phys > 0` (`hanchor`).
     `DimensionlessMarginTransmutation` DIALS `m_phys = 1 − e^{−1/e}` via the ideal
     self-similar seed; the real 4D flow's generation is the open R2.  `exp(−x) > 0` as a
     function value is TRIVIAL (`condensate_creal_nonneg`) — the mass gap is NOT that; it
     is the REAL theory's scale being a genuine nonzero `Λ`.

`condensate_floor` is a CONDITIONAL producer (open binders): it does NOT inhabit
`TrueMarginRecursionPhysical`, `TrueMarginRecursionSummable`, `SingleStepDefectBound`,
`UniformSpacingFloor`, `Tier0Scorecard`, `ClayTarget`, `ClayTargetPinned`, or
`FrontierDAG`.  NO guarded bundle is inhabited; nothing is faked; the CONDENSATE
POSITIVITY (the non-perturbative RG generation of a nonzero mass scale) is the genuine
irreducible 4D Yang–Mills frontier — the mass gap remains OPEN. -/
theorem condensate_honesty : True := trivial

end YMGap.Continuum.CondensateGeometric

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CondensateGeometric.condExponent_nonneg
#print axioms YMGap.Continuum.CondensateGeometric.condensate_creal_nonneg
#print axioms YMGap.Continuum.CondensateGeometric.condensate_creal_le_one
#print axioms YMGap.Continuum.CondensateGeometric.condTerm_nonneg
#print axioms YMGap.Continuum.CondensateGeometric.cond_recurrence
#print axioms YMGap.Continuum.CondensateGeometric.tailSum_condTerm_eq_finSum
#print axioms YMGap.Continuum.CondensateGeometric.cond_tailSum_le
#print axioms YMGap.Continuum.CondensateGeometric.cond_anchorDom
#print axioms YMGap.Continuum.CondensateGeometric.condensate_floor
#print axioms YMGap.Continuum.CondensateGeometric.cond_floor_pos_at_anchor
#print axioms YMGap.Continuum.CondensateGeometric.cond_anchor_from_mphys_lb
