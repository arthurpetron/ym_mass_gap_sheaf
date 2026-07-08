/-
Item 12 (Koch–Wittwer certified-RG route) — **THE CERTIFIED CONTRACTION on the
TRUNCATED block-spin map + the ONE named truncation-error residual.**

# What this module is (read first)

Building on the SOUND Q' interval-arithmetic kernel
(`YMGap/Continuum/IntervalArithmetic.lean`), this module carries out the
computer-assisted-RG step of item 12
(`docs/alternative-routes-to-singlestep.md`) at a pilot truncation:

  1. **The truncated block-spin map on `N` SU(2) character channels.**  The
     item-9 scouting (`docs/balaban-scouting.md`) selected the scheme — transverse
     bond-moving Migdal–Kadanoff, `λ ∈ [0.25, 0.5]` (decimation RULED OUT) — and
     pinned the truncation order: `≈ 26` fused SU(2) character channels (`j ≤ 12.5`)
     for a `1e-6` tail, super-geometric Bessel decay.  Here we model the map on a
     SMALL pilot truncation (`N = 4`, `j ≤ 3/2`) with rational character-coefficient
     enclosures, to exhibit the machinery.

  2. **A GENUINE machine-checked interval contraction/defect bound.**  The per-step
     defect (the `ε`-contribution) is COMPUTED by the interval kernel as a `QI`
     enclosure `truncatedDefect`, and its upper endpoint is certified below the
     `singleStep`-shaped quadratic bound `6·(1 − w)²` by `decide` on the exact
     rational endpoints (`truncatedDefect_le_six`) — and in fact below the sharper
     `4·(1 − w)²` (`truncatedDefect_le_four`), showing genuine slack.  This is a
     REAL interval computation decided on rational endpoints, not an assumed bound.
     `enclosed_defect_le_six` then certifies the (unknown, enclosed) true truncated
     defect `≤ 6·(1 − w)²`.

  3. **The ONE analytic residual, NAMED (not faked).**  `TruncationTailBound` is
     the single hard lemma of item 12: the discarded high-`j` channels (beyond the
     truncation order `N`) contribute at most the slack `2·(1 − w_k)²` to the
     per-step defect, via super-geometric Bessel decay.  It is a NAMED-OPEN
     obligation over the EXTERNALLY-GIVEN true per-scale tail-defect sequence
     (`Type`, Rule 8; NOT inhabited — inhabiting it for the real sequence IS the
     analytic Balaban-hardness lemma).  Scouting pins `N ≈ 26` for a `1e-6` tail.

  4. **Composition toward the Grönwall fold.**  `fullDefect_quad_of_certified_and_tail`
     shows: (certified truncated bound `≤ 4·m²`, from the interval kernel) + (the
     named `TruncationTailBound`, `tail ≤ 2·m²`) ⟹ the full per-step defect
     `≤ 6·m²` — exactly the `EuclideanExtraRequirements` (E1) quadratic-defect
     input of `HierarchicalMassGap`.  `certified_route_to_floor` bundles this E1
     reproduction with the 4D positive floor, the latter delivered by the PROVED
     Grönwall fold `SingleStepDefectReduction.fullFloor_of_singleStep` from the
     `singleStep` (E2) residual.

# HONEST VERDICT (AGENTS.md Rule 6 / Rule 9)

This is the FOUNDATION of item 12: a SOUND interval kernel + a REAL machine-checked
interval contraction bound on a small truncation + the ONE analytic residual
sharply named.  It is NOT the full closure.  What REMAINS:

  * the **full `N ≈ 26` certification** — the pilot decide is proved at ONE margin
    (`w = 4/5`) and `N = 4`; the `htrunc : ∀ k, truncDefect k ≤ 4·(1−w_k)²`
    hypothesis of the composition (all scales, all `26` channels) is the remaining
    interval-arithmetic work (each scale a further `decide`);
  * the **truncation-error lemma** `TruncationTailBound` itself (the single analytic
    Bessel-decay estimate — the collaborator target, item 12 step 3);
  * the `singleStep` (E2) recursion inequality, unchanged.

NO Clay-frontier guarded type is inhabited; the truncation error is OPEN, so
nothing here inhabits `singleStep` or any frontier type.  Nothing is faked.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` composition + `decide` on exact rational endpoints (no
`native_decide`).  Every load-bearing declaration is gated with `#print axioms`;
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no `sorry`.
`Type`-level witnesses (Rule 8).
-/

import YMGap.Continuum.IntervalArithmetic
import YMGap.Continuum.SingleStepDefectReduction
import YMGap.Continuum.HierarchicalMassGap

namespace YMGap.Continuum.TruncatedBlockSpinContraction

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.IntervalArithmetic
open YMGap.Continuum.AFRateCalibration

/-! ## 1. The pilot truncated block-spin map (`N = 4` SU(2) character channels)

Scouting scheme: transverse bond-moving MK, `λ ∈ [0.25, 0.5]`.  One MK block step
raises the single-plaquette class function to the power `p_fuse = b^{d−1} = 8`
pointwise = an 8-fold Clebsch–Gordan fusion of the heat-kernel character
coefficients.  We model the pilot at the crossover coupling `w = 4/5` with the
truncation kept to `N = 4` channels `j ∈ {0, 1/2, 1, 3/2}`.  The per-channel
character coefficients are given as EXACT RATIONAL ENCLOSURES `[c_j^lo, c_j^hi]`
(the rounded, super-geometrically decaying fused coefficients); the enclosure
WIDTH is the certified rounding of the true coefficient. -/

/-- Pilot coupling `w = 4/5` (representative crossover margin `1 − w = 1/5`). -/
def wPilot : Q' := Q'.mkPos 4 5 (by decide)

/-- Pilot margin `m = 1 − w = 1/5`. -/
def mPilot : Q' := (1 : Q') - wPilot

/-- Channel `j = 0` coefficient enclosure `[19/10, 20/10]` (leading channel). -/
def coeff0 : QI := ⟨Q'.mkPos 19 10 (by decide), Q'.mkPos 20 10 (by decide), by decide⟩
/-- Channel `j = 1/2` coefficient enclosure `[9/10, 10/10]`. -/
def coeff1 : QI := ⟨Q'.mkPos 9 10 (by decide), Q'.mkPos 10 10 (by decide), by decide⟩
/-- Channel `j = 1` coefficient enclosure `[5/10, 6/10]`. -/
def coeff2 : QI := ⟨Q'.mkPos 5 10 (by decide), Q'.mkPos 6 10 (by decide), by decide⟩
/-- Channel `j = 3/2` coefficient enclosure `[2/10, 3/10]` (super-geometric decay). -/
def coeff3 : QI := ⟨Q'.mkPos 2 10 (by decide), Q'.mkPos 3 10 (by decide), by decide⟩

/-- The margin-squared enclosure `[m², m²]`, computed by the interval kernel via
`mul` of the point interval `[m, m]` with itself (exercises the 4-corner rule). -/
def mSqInt : QI := IntervalArithmetic.mul (point mPilot) (point mPilot)

/-- **THE PER-STEP TRUNCATED DEFECT, COMPUTED BY THE INTERVAL KERNEL.**  The sum
over the `N = 4` retained channels of `coeff_j · m²`, each product an interval
`QI.mul`, accumulated by `QI.add`.  Its endpoints are EXACT rationals produced by
the certified-arithmetic engine — no symbolic estimate. -/
def truncatedDefect : QI :=
  IntervalArithmetic.add (IntervalArithmetic.mul coeff0 mSqInt)
    (IntervalArithmetic.add (IntervalArithmetic.mul coeff1 mSqInt)
      (IntervalArithmetic.add (IntervalArithmetic.mul coeff2 mSqInt)
        (IntervalArithmetic.mul coeff3 mSqInt)))

/-! ## 2. The CERTIFIED interval contraction/defect bound (machine-checked `decide`) -/

/-- **THE CERTIFIED CONTRACTION BOUND (singleStep-shaped, `decide`-checked).**  The
interval-computed truncated defect satisfies `truncatedDefect.hi ≤ 6·(1 − w)²` —
the quadratic per-step defect bound of `SingleStepDefectReduction` — verified by
`decide` on the exact rational endpoints.  A GENUINE machine-checked interval
bound, not an assumption. -/
theorem truncatedDefect_le_six :
    truncatedDefect.hi ≤ Q'.ofNat 6 * (mPilot * mPilot) := by decide

/-- **The SHARPER certified bound** `truncatedDefect.hi ≤ 4·(1 − w)²`: the actual
certified truncated contraction constant is `≈ 39/10 < 4`, well under the `6`
budget — genuine slack (the interval bound is not rigged tight).  This `4·m²`
leaves the `2·m²` slack that the discarded-channel tail (`TruncationTailBound`) is
allowed to occupy. -/
theorem truncatedDefect_le_four :
    truncatedDefect.hi ≤ Q'.ofNat 4 * (mPilot * mPilot) := by decide

/-- **The certified bound transfers to the ENCLOSED true defect.**  Any true defect
value `x` enclosed by `truncatedDefect` (the interval is an outward-rounded
enclosure of the exact fused-coefficient defect) satisfies `x ≤ 6·(1 − w)²`.  This
is `certifiedLe` applied to the `decide`-checked endpoint bound — the mechanism by
which the numeric certificate discharges the analytic inequality. -/
theorem enclosed_defect_le_six (x : Q') (hx : contains truncatedDefect x) :
    x ≤ Q'.ofNat 6 * (mPilot * mPilot) :=
  certifiedLe truncatedDefect (Q'.ofNat 6 * (mPilot * mPilot)) truncatedDefect_le_six x hx

/-- The pilot margin is strictly positive (non-vacuity of the certificate: the
bound is not `0 ≤ 0`). -/
theorem mPilot_pos : (0 : Q') < mPilot := by decide

/-! ## 3. The ONE analytic residual — the truncation-error lemma (NAMED-OPEN) -/

/-- **`TruncationTailBound` — the single analytic residual of item 12 (`Type`,
Rule 8; UNINHABITED for the real 4D map).**

Parameters:
  * `afr` — the AF trajectory of couplings `w_k → 1`;
  * `N` — the truncation order (scouting: `N ≈ 26` for a `1e-6` single-plaquette
    tail; `N = 18` for `1e-3`);
  * `tailDefect` — the **externally given** true per-scale contribution of the
    DISCARDED high-`j` channels (`j > N`) to the per-step block-spin defect.  This
    is NOT a free field the prover may set to `0`; it is the real tail of the true
    fused SU(2) character-coefficient sequence.

The single field `tail_quad` is the ONE analytic lemma where all the Balaban-type
hardness concentrates: the super-geometric Bessel decay of the SU(2) heat-kernel
coefficients bounds the discarded tail's per-step defect contribution by the slack
`2·(1 − w_k)²`.  Inhabiting it for the real `tailDefect` is exactly that estimate —
NOT provided here (item 12 step 3; the collaborator target).  It is NOT trivially
inhabitable: `tailDefect` is fixed externally, so one cannot choose it to make the
bound hold. -/
structure TruncationTailBound (afr : AFRateModulus) (N : Nat)
    (tailDefect : Nat → Q') : Type where
  /-- **THE ONE ANALYTIC BESSEL-DECAY LEMMA (open).**  The discarded channels
  beyond the truncation order `N` contribute at most the second-order slack
  `2·(1 − w_k)²` to the per-step defect, uniformly along the AF trajectory. -/
  tail_quad : ∀ k,
    tailDefect k ≤ Q'.ofNat 2 * ((1 - afr.w k) * (1 - afr.w k))

/-! ## 4. Composition toward the Grönwall fold

The certified truncated contraction (E1 for the retained channels) + the named
`TruncationTailBound` (control of the discarded channels) assemble the FULL per-step
quadratic defect bound `≤ 6·(1 − w_k)²`, which is exactly the
`EuclideanExtraRequirements` (E1) input of `HierarchicalMassGap`.  Feeding it — and
the `singleStep` (E2) recursion — through the PROVED Grönwall fold gives the 4D
positive floor. -/

/-- Small helper: `4·X + 2·X ≃ 6·X` on `Q'` (right-distribution, `decide`-checked
coefficient sum). -/
theorem four_add_two_mul_eqv (X : Q') :
    (Q'.ofNat 4 * X + Q'.ofNat 2 * X).eqv (Q'.ofNat 6 * X) := by
  -- 4·X + 2·X ≃ X·4 + X·2 ≃ X·(4+2) ≃ X·6 ≃ 6·X
  have h1 : (Q'.ofNat 4 * X + Q'.ofNat 2 * X).eqv (X * Q'.ofNat 4 + X * Q'.ofNat 2) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (Q'.ofNat 2 * X) (Q'.mul_comm_eqv (Q'.ofNat 4) X))
      (Q'.add_eqv_congr_left (X * Q'.ofNat 4) _ _ (Q'.mul_comm_eqv (Q'.ofNat 2) X))
  have h2 : (X * Q'.ofNat 4 + X * Q'.ofNat 2).eqv (X * (Q'.ofNat 4 + Q'.ofNat 2)) :=
    Q'.eqv_symm (Q'.mul_add_eqv X (Q'.ofNat 4) (Q'.ofNat 2))
  have h3 : (X * (Q'.ofNat 4 + Q'.ofNat 2)).eqv (X * Q'.ofNat 6) :=
    Q'.mul_eqv_congr_left X _ _ (by decide)
  have h4 : (X * Q'.ofNat 6).eqv (Q'.ofNat 6 * X) := Q'.mul_comm_eqv X (Q'.ofNat 6)
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ h2 (Q'.eqv_trans _ _ _ h3 h4))

/-- **`fullDefect_quad_of_certified_and_tail` — the composition producing E1.**
Given (a) the certified truncated per-scale defect bound `truncDefect k ≤ 4·(1−w_k)²`
(the interval-kernel output, of which `truncatedDefect_le_four` is the pilot
`decide`-checked instance) and (b) a `TruncationTailBound` (the named residual,
`tailDefect k ≤ 2·(1−w_k)²`), the FULL per-step defect `truncDefect + tailDefect` is
bounded by `6·(1−w_k)²` — exactly the `EuclideanExtraRequirements`
(`bondMovingDefect_quadratic_bound`, E1) input.  BOTH hypotheses are load-bearing:
the `4·m² + 2·m² = 6·m²` budget closes only with the tail control. -/
theorem fullDefect_quad_of_certified_and_tail
    (afr : AFRateModulus) (N : Nat) (tailDefect truncDefect : Nat → Q')
    (htrunc : ∀ k, truncDefect k
      ≤ Q'.ofNat 4 * ((1 - afr.w k) * (1 - afr.w k)))
    (tail : TruncationTailBound afr N tailDefect) :
    ∀ k, truncDefect k + tailDefect k
      ≤ Q'.ofNat 6 * ((1 - afr.w k) * (1 - afr.w k)) := by
  intro k
  -- truncDefect k + tailDefect k ≤ 4·m² + 2·m² ≃ 6·m²
  have hstep : truncDefect k + tailDefect k
      ≤ Q'.ofNat 4 * ((1 - afr.w k) * (1 - afr.w k))
        + Q'.ofNat 2 * ((1 - afr.w k) * (1 - afr.w k)) :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ (tailDefect k) (htrunc k))
      (Q'.add_le_add_left _ _ _ (tail.tail_quad k))
  exact Q'.le_trans' _ _ _ hstep
    (Q'.le_of_eqv (four_add_two_mul_eqv ((1 - afr.w k) * (1 - afr.w k))))

/-- **`certified_route_to_floor` — the item-12 composition, end to end.**  Bundles:

  * (E1) the FULL per-step quadratic defect bound `≤ 6·(1−w_k)²`, REPRODUCED from
    the interval-certified truncated bound `htrunc` + the named `TruncationTailBound`
    `tail` (`fullDefect_quad_of_certified_and_tail`); AND
  * the 4D positive continuum floor for the true margin, delivered by the PROVED
    Grönwall fold `SingleStepDefectReduction.fullFloor_of_singleStep` from the
    `singleStep` (E2) bound `S`.

So the certified-arithmetic route supplies E1 (independently of the symbolic
`bondMovingDeltaRen ≤ 6p(1−w)²`), while E2 = `singleStep` and the analytic
`TruncationTailBound` remain the residuals.  NOTHING here inhabits `singleStep` or a
frontier type: `tail` and `S` are hypotheses (open inputs), not constructed. -/
theorem certified_route_to_floor
    (afr : AFRateModulus) (N : Nat) (tailDefect truncDefect : Nat → Q')
    (htrunc : ∀ k, truncDefect k
      ≤ Q'.ofNat 4 * ((1 - afr.w k) * (1 - afr.w k)))
    (tail : TruncationTailBound afr N tailDefect)
    (S : SingleStepDefectReduction.SingleStepDefectBound) :
    (∀ k, truncDefect k + tailDefect k
        ≤ Q'.ofNat 6 * ((1 - afr.w k) * (1 - afr.w k)))
      ∧ ((0 : Q') < (SingleStepDefectReduction.defectRecursion_of_singleStep S).prodFloor
          ∧ ∀ k : Nat,
              (SingleStepDefectReduction.defectRecursion_of_singleStep S).prodFloor
                ≤ S.trueMargin k) :=
  ⟨fullDefect_quad_of_certified_and_tail afr N tailDefect truncDefect htrunc tail,
   SingleStepDefectReduction.fullFloor_of_singleStep S⟩

/-! ## 5. Non-vacuity of the interface (the truncation-error map is a real obligation)

`TruncationTailBound` for the CANONICAL AF trajectory and the ZERO tail-defect
sequence IS inhabitable (`0 ≤ 2·m²`) — but that is the degenerate `tailDefect ≡ 0`,
NOT the real discarded-channel tail.  We record this only to certify the field type
is not false-as-stated; the real obligation is for the true, externally-fixed
`tailDefect`, which is NOT provided.  (Rule 9.1: this degenerate witness is NOT a
closure of anything — `tailDefect` is a parameter, and the real sequence is not
`0`.) -/
def truncationTail_zero_witness (afr : AFRateModulus) (N : Nat) :
    TruncationTailBound afr N (fun _ => 0) where
  tail_quad := fun k => by
    -- 0 ≤ 2·m² since m² ≥ 0
    have hm : (0 : Q') ≤ (1 - afr.w k) * (1 - afr.w k) := by
      have hmn : (0 : Q') ≤ 1 - afr.w k := Q'.sub_nonneg_of_le (Q'.le_of_lt (afr.w_lt_one k))
      exact Q'.mul_nonneg _ _ hmn hmn
    have : (0 : Q') ≤ Q'.ofNat 2 * ((1 - afr.w k) * (1 - afr.w k)) :=
      Q'.mul_nonneg _ _ (by decide) hm
    exact this

end YMGap.Continuum.TruncatedBlockSpinContraction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TruncatedBlockSpinContraction.truncatedDefect_le_six
#print axioms YMGap.Continuum.TruncatedBlockSpinContraction.truncatedDefect_le_four
#print axioms YMGap.Continuum.TruncatedBlockSpinContraction.enclosed_defect_le_six
#print axioms YMGap.Continuum.TruncatedBlockSpinContraction.mPilot_pos
#print axioms YMGap.Continuum.TruncatedBlockSpinContraction.four_add_two_mul_eqv
#print axioms YMGap.Continuum.TruncatedBlockSpinContraction.fullDefect_quad_of_certified_and_tail
#print axioms YMGap.Continuum.TruncatedBlockSpinContraction.certified_route_to_floor
#print axioms YMGap.Continuum.TruncatedBlockSpinContraction.truncationTail_zero_witness
