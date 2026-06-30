/-
Track B / R2 — **From the conserved CReal margin BUDGET to an emergent physical-gap
FLOOR; the conserved-margin half SUPPLIED, the spacing-uniform a→0 physics ISOLATED.**

# Why this module exists (read first)

`CodynamicCRealFlow` closed the codynamic conserved-margin budget along a genuine
constructive-real self-similar flow: for any `SelfSimilarTower b` with a strictly
positive UV exponent seed `PosEv (T.w 0)`, the rescaled margin

    budgetC N = (1 − sep N) · ∏_{j=1}^{N} geomSumC (sep j) (b+1)

is strictly positive (`marginBudget_posC_tower`) and CONSERVED `≃ 1 − sep 0`
(`marginInvariantC`).  `CodynamicHierarchical` named the PHYSICAL-gap obligation as
the (uninhabited, rational-valued) `DimensionalTransmutation.rate_matched` — the
margin, rescaled by the decimation product and matched against the lattice spacing,
must stay above a strictly-positive `physFloor` at every scale.

This module connects the two.  Dividing the conserved budget by a strictly-positive
SPACING SCHEDULE `a_N` produces the per-scale CReal floor

    physFloorC N = budgetC N · (1 / a_N),

and `physFloorC_pos_tower` proves it is `PosEv` at EVERY scale, UNCONDITIONALLY, from
`marginBudget_posC_tower` plus the positive spacing schedule.  This is the
constructive-real, irrational-exponent inhabitant of the emergent floor that the
rational `polyFlow` could not provide.

# Honest scope — what is SUPPLIED and what remains OPEN

The conserved-margin half is genuinely SUPPLIED by the self-similar flow:
`physFloorC N ≃ (1 − sep 0)·(1/a_N)` (`physFloorC_conserved`), the conserved base
margin rescaled.  But `physFloorC` is the conserved BUDGET rescaled, NOT the physical
mass gap: the budget carries the accumulated geometric factor
`∏ geomSumC = (b+1)^N · ∏ ρ_dec`, so `budgetC N / a_N` is dominated by that growth and
is automatically bounded below for a vanishing geometric spacing — it does NOT see the
genuine continuum content.

The GENUINE physical gap is `physGapC N = (1 − sep N) · (1 / a_N)` (margin over
spacing, no budget rescaling).  Its per-scale positivity is again SUPPLIED by the flow
(`physGapC_pos_tower`, via the propagated per-scale exponent positivity
`posEv_w_tower`).  What is NOT supplied — and is the genuine a→0 dimensional-
transmutation physics — is a SPACING-UNIFORM positive floor: a single rational
`floor > 0` with `ofQ' floor ≤ physGapC N` for EVERY scale `N` simultaneously.  This is
the convergence of `∏ ρ_dec` against the vanishing spacing; it is left as the named
Type-level open field `UniformPhysGapFloor` of `CRealContinuumGapResidual`, the exact
CReal analogue of the uninhabited `DimensionalTransmutation.rate_matched`.  No
uniform/continuum floor is fabricated.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over the `CodynamicCRealFlow` backbone; every carrier is `Type`-level
data (no `Prop`-∃ witnesses).  Each load-bearing declaration is gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).  No `Classical.*`, no
`native_decide`, no `sorry`.
-/

import YMGap.Continuum.CodynamicCRealFlow
import YMGap.Continuum.CodynamicHierarchical

namespace YMGap.Continuum.CodynamicPhysFloor

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.TuranPositivity
open YMGap.Continuum.CodynamicCRealFlow

/-! ## 1. The strictly-positive spacing schedule and its reciprocal -/

/-- **A strictly-positive lattice-spacing schedule** `a_N > 0`.  This is the SINGLE
named spacing-schedule input the reduction consumes; it carries the per-scale lattice
spacing along the flow.  (`SelfSimilarTower` supplies the dimensionless margin; the
spacing supplies the dimensionful denominator.) -/
structure SpacingSchedule : Type where
  /-- The per-scale lattice spacing. -/
  a : Nat → Q'
  /-- The spacing is strictly positive at every scale. -/
  a_pos : ∀ N, (0 : Q') < a N

/-- The reciprocal spacing `1 / a_N` as a `CReal` (a positive rational constant). -/
def recipSpacingC (A : SpacingSchedule) (N : Nat) : CReal :=
  CReal.ofQ' (Q'.divPos 1 (A.a N) (A.a_pos N))

/-- The reciprocal spacing is strictly positive (`PosEv`): `1 / a_N > 0`. -/
theorem recipSpacingC_pos (A : SpacingSchedule) (N : Nat) :
    PosEv (recipSpacingC A N) := by
  refine posEv_of_eventually (ε := Q'.divPos 1 (A.a N) (A.a_pos N))
    (Q'.divPos_pos 1 (A.a N) (A.a_pos N) (by decide)) ⟨0, fun n _ => ?_⟩
  show Q'.divPos 1 (A.a N) (A.a_pos N)
      ≤ (CReal.ofQ' (Q'.divPos 1 (A.a N) (A.a_pos N))).approx n
  exact Q'.le_refl' _

/-- **The constant unit spacing schedule** `a_N = 1` (a placeholder fixed spacing;
NOT a continuum approach — a genuine a→0 schedule has `a_N → 0`). -/
def unitSpacing : SpacingSchedule where
  a := fun _ => 1
  a_pos := fun _ => by decide

/-! ## 2. The emergent physical-gap floor from the conserved BUDGET

`physFloorC` divides the conserved codynamic budget by the spacing.  Its per-scale
positivity is UNCONDITIONAL from `marginBudget_posC_tower`. -/

/-- The conserved codynamic budget `(1 − sep N) · ∏ geomSumC` at scale `N` (the
`CodynamicCRealFlow` invariant, repackaged for division). -/
def budgetC (b : Nat) (s : Nat → CReal) (N : Nat) : CReal :=
  CReal.mul (CReal.sub CReal.cone (s N))
    (cprodTail (fun j => geomSumC (s j) (b + 1)) N)

/-- **THE EMERGENT PHYSICAL-GAP FLOOR (conserved budget / spacing).**
`physFloorC N = budgetC N · (1 / a_N)` — the conserved codynamic budget rescaled by
the spacing schedule. -/
def physFloorC (b : Nat) (s : Nat → CReal) (A : SpacingSchedule) (N : Nat) : CReal :=
  CReal.mul (budgetC b s N) (recipSpacingC A N)

/-- **THE EMERGENT FLOOR IS STRICTLY POSITIVE AT EVERY SCALE (UNCONDITIONAL).**  For
any `SelfSimilarTower b` with positive UV exponent seed `PosEv (T.w 0)`, and any
strictly-positive spacing schedule, the emergent floor `physFloorC N` is `PosEv` at
every scale.  Proof: `marginBudget_posC_tower` (the conserved budget is positive) times
`recipSpacingC_pos` (the spacing reciprocal is positive).  This is the conserved-margin
half SUPPLIED by the genuine constructive-real self-similar flow. -/
theorem physFloorC_pos_tower {b : Nat} (T : SelfSimilarTower b)
    (hx : PosEv (T.w 0)) (A : SpacingSchedule) (N : Nat) :
    PosEv (physFloorC b (sep T) A N) :=
  posEv_mul (marginBudget_posC_tower T hx N) (recipSpacingC_pos A N)

/-- **THE EMERGENT FLOOR IS THE CONSERVED BASE MARGIN, RESCALED.**  Under the CReal
flow law, `physFloorC N ≃ (1 − sep 0)·(1 / a_N)`: the per-scale floor is the FIXED UV
margin `1 − sep 0` divided by the spacing — the conserved-margin invariant made
explicit at the floor level.  (The genuine physical mass gap is `physGapC`, §3; this
budget-floor is the conserved-margin half.) -/
theorem physFloorC_conserved {b : Nat} {s : Nat → CReal} (hss : selfSimilarC b s)
    (A : SpacingSchedule) (N : Nat) :
    CReal.Equiv (physFloorC b s A N)
      (CReal.mul (CReal.sub CReal.cone (s 0)) (recipSpacingC A N)) :=
  CReal.mul_congr_left (marginInvariantC hss N)

/-! ## 3. The GENUINE physical gap `margin / spacing` and per-scale positivity

`physGapC N = (1 − sep N)·(1 / a_N)` is the genuine physical mass gap (margin over
spacing, no budget rescaling).  Its per-scale positivity needs the per-scale margin
positivity `1 − sep N > 0`, which we obtain from the propagated exponent positivity
`PosEv (T.w N)` (the tower descent `(b+1)·w(k+1) ≃ w k` carries strict positivity from
the UV seed to every scale). -/

/-- **`PosEv` cancels a positive rational scale.**  If `c·x > 0` (`PosEv (ofQ' c · x)`)
with `c > 0`, then `x > 0`: from an eventual bound `ε' ≤ c·x.approx n` divide by `c`
(`divPos_le_of_le_mul`) to get `ε'/c ≤ x.approx n`. -/
theorem posEv_scale_cancel {c : Q'} (hc : (0 : Q') < c) {x : CReal}
    (h : PosEv (CReal.mul (CReal.ofQ' c) x)) : PosEv x := by
  obtain ⟨ε', hε', N, hN⟩ := eventually_ge_of_posEv h
  refine posEv_of_eventually (ε := Q'.divPos ε' c hc)
    (Q'.divPos_pos ε' c hc hε') ⟨N, fun n hn => ?_⟩
  have hcx : ε' ≤ c * x.approx n := hN n hn
  have hxc : ε' ≤ x.approx n * c :=
    Q'.le_trans' _ _ _ hcx (Q'.le_of_eqv (Q'.mul_comm_eqv c (x.approx n)))
  exact Q'.divPos_le_of_le_mul ε' c hc hxc

/-- **The UV exponent positivity propagates one step toward the IR.**  From
`PosEv (T.w k)` and the tower descent `(b+1)·w(k+1) ≃ w k` (`scaleN_approx` + `T.div`),
`PosEv (T.w (k+1))`.  The `(b+1)`-fold sum carries strict positivity down, and
`posEv_scale_cancel`-style division by `b+1` recovers the per-scale exponent. -/
theorem posEv_w_succ {b : Nat} (T : SelfSimilarTower b) {k : Nat}
    (h : PosEv (T.w k)) : PosEv (T.w (k + 1)) := by
  obtain ⟨ε', hε', N, hN⟩ := eventually_ge_of_posEv h
  have hcpos : (0 : Q') < Q'.ofNat (b + 1) := Q'.ofNat_succ_pos b
  refine posEv_of_eventually (ε := Q'.divPos ε' (Q'.ofNat (b + 1)) hcpos)
    (Q'.divPos_pos ε' (Q'.ofNat (b + 1)) hcpos hε') ⟨N, fun n hn => ?_⟩
  have hwk : ε' ≤ (T.w k).approx n := hN n hn
  have hrel : ((T.w k).approx n).eqv (Q'.ofNat (b + 1) * (T.w (k + 1)).approx n) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (T.div k n)) (scaleN_approx (b + 1) (T.w (k + 1)) n)
  have hle : ε' ≤ Q'.ofNat (b + 1) * (T.w (k + 1)).approx n :=
    Q'.le_trans' _ _ _ hwk (Q'.le_of_eqv hrel)
  have hle' : ε' ≤ (T.w (k + 1)).approx n * Q'.ofNat (b + 1) :=
    Q'.le_trans' _ _ _ hle
      (Q'.le_of_eqv (Q'.mul_comm_eqv (Q'.ofNat (b + 1)) ((T.w (k + 1)).approx n)))
  exact Q'.divPos_le_of_le_mul ε' (Q'.ofNat (b + 1)) hcpos hle'

/-- **The UV exponent positivity holds at EVERY scale.**  From `PosEv (T.w 0)`,
`PosEv (T.w N)` for all `N` (iterate `posEv_w_succ`). -/
theorem posEv_w_tower {b : Nat} (T : SelfSimilarTower b) (h0 : PosEv (T.w 0)) :
    ∀ N, PosEv (T.w N)
  | 0 => h0
  | N + 1 => posEv_w_succ T (posEv_w_tower T h0 N)

/-- **The per-scale margin is strictly positive at every scale.**  From the propagated
exponent positivity `PosEv (T.w N)`, the margin `1 − sep N = 1 − e^{−w N}` is `PosEv`
(`expNegCD_lt_one`). -/
theorem margin_pos_tower {b : Nat} (T : SelfSimilarTower b) (h0 : PosEv (T.w 0))
    (N : Nat) : PosEv (CReal.sub CReal.cone (sep T N)) :=
  expNegCD_lt_one (T.dw N) (posEv_w_tower T h0 N)

/-- **THE GENUINE PHYSICAL GAP** `physGapC N = (1 − sep N)·(1 / a_N)` — the per-scale
margin over the spacing (no budget rescaling).  This is the dimensionful mass-gap
surrogate whose spacing-UNIFORM positivity (§4) is the genuine a→0 content. -/
def physGapC (_b : Nat) (s : Nat → CReal) (A : SpacingSchedule) (N : Nat) : CReal :=
  CReal.mul (CReal.sub CReal.cone (s N)) (recipSpacingC A N)

/-- **THE PHYSICAL GAP IS STRICTLY POSITIVE AT EVERY SCALE (UNCONDITIONAL).**  For any
`SelfSimilarTower b` with positive UV exponent seed and any positive spacing schedule,
`physGapC N` is `PosEv` at every scale: per-scale margin positivity (`margin_pos_tower`)
times reciprocal-spacing positivity.  The flow SUPPLIES per-scale positivity of the
genuine physical gap; the OPEN content is the spacing-UNIFORM floor (§4). -/
theorem physGapC_pos_tower {b : Nat} (T : SelfSimilarTower b)
    (hx : PosEv (T.w 0)) (A : SpacingSchedule) (N : Nat) :
    PosEv (physGapC b (sep T) A N) :=
  posEv_mul (margin_pos_tower T hx N) (recipSpacingC_pos A N)

/-! ## 4. The continuum-gap residual: conserved-margin half SUPPLIED, spacing-
uniformity ISOLATED

The genuine continuum mass gap needs a SINGLE positive floor below `physGapC N` for
ALL scales `N` at once — the dimensional-transmutation rate match (the convergence of
`∏ ρ_dec` against the vanishing spacing).  We isolate exactly this as the named
Type-level open field `UniformPhysGapFloor`, the CReal analogue of the uninhabited
`CodynamicHierarchical.DimensionalTransmutation.rate_matched`. -/

/-- **THE SPACING-UNIFORM PHYSICAL-GAP FLOOR (the NAMED OPEN a→0 content).**  A single
strictly-positive rational `floor` lying below `physGapC N` at EVERY scale `N`
simultaneously.  This is the genuine asymptotic-freedom / dimensional-transmutation
content: it asserts the margin shrinks at exactly the spacing rate so a fixed positive
gap survives the continuum limit.  It is left UNINHABITED for a genuine vanishing
(a→0) spacing schedule — the per-scale positivity (`physGapC_pos_tower`) is supplied by
the flow, the UNIFORMITY over the a→0 schedule is not. -/
structure UniformPhysGapFloor {b : Nat} (T : SelfSimilarTower b)
    (A : SpacingSchedule) : Type where
  /-- The uniform positive floor. -/
  floor : Q'
  /-- The floor is strictly positive. -/
  floor_pos : (0 : Q') < floor
  /-- The floor lies below the physical gap at every scale simultaneously. -/
  bound : ∀ N, CReal.leEv (CReal.ofQ' floor) (physGapC b (sep T) A N)

/-- **THE CReal CONTINUUM-GAP RESIDUAL (the honest reduction carrier).**

Carries the genuine self-similar flow, its positive UV exponent seed, the spacing
schedule, and the SINGLE named open field `uniform`.  Mirrors
`CodynamicHierarchical.PhysicalContinuumGapResidual`, but with the conserved-margin
half PROVED (not assumed): given any inhabitant, `physGapC` is positive at every scale
UNCONDITIONALLY (`residual_physGap_pos` — uses only `T`/`uvSeed`, not `uniform`), and
the continuum floor is exactly the open `uniform` field.  UNINHABITED for a genuine
a→0 spacing schedule (the `uniform` field is the open dimensional-transmutation
content). -/
structure CRealContinuumGapResidual (b : Nat) : Type where
  /-- The self-similar CReal flow (the irrational-exponent tower). -/
  T : SelfSimilarTower b
  /-- The strictly-positive UV exponent seed `PosEv (T.w 0)`. -/
  uvSeed : PosEv (T.w 0)
  /-- The strictly-positive spacing schedule. -/
  spacing : SpacingSchedule
  /-- **OPEN ANALYTIC CORE (a→0).**  The spacing-uniform physical-gap floor — the
  dimensional-transmutation rate match.  Supplied here as Type-level data; uninhabited
  for a genuine vanishing spacing schedule. -/
  uniform : UniformPhysGapFloor T spacing

/-- **The conserved-margin half is SUPPLIED — per-scale positivity is unconditional.**
For any residual, the genuine physical gap `physGapC N` is `PosEv` at every scale,
using ONLY the flow `T` and its UV seed `uvSeed` (NOT the open `uniform` field).  This
is exactly the half the self-similar flow delivers. -/
theorem CRealContinuumGapResidual.physGap_pos {b : Nat}
    (R : CRealContinuumGapResidual b) (N : Nat) :
    PosEv (physGapC b (sep R.T) R.spacing N) :=
  physGapC_pos_tower R.T R.uvSeed R.spacing N

/-- **The continuum gap floor extracted from the (open) uniform field.**  Given a
residual, the spacing-uniform continuum floor is a strictly-positive rational below
the physical gap at every scale — the data of a positive continuum mass gap.  The
positivity and the bound come from the open `uniform` field; this lemma is the
reduction's payoff GIVEN that named input. -/
def CRealContinuumGapResidual.continuumFloor {b : Nat}
    (R : CRealContinuumGapResidual b) : Q' :=
  R.uniform.floor

theorem CRealContinuumGapResidual.continuumFloor_pos {b : Nat}
    (R : CRealContinuumGapResidual b) : (0 : Q') < R.continuumFloor :=
  R.uniform.floor_pos

theorem CRealContinuumGapResidual.continuumFloor_bound {b : Nat}
    (R : CRealContinuumGapResidual b) (N : Nat) :
    CReal.leEv (CReal.ofQ' R.continuumFloor) (physGapC b (sep R.T) R.spacing N) :=
  R.uniform.bound N

/-! ## 5. Capstone: the genuine irrational `e^{−1}` self-similar flow yields a
strictly-positive emergent physical-gap floor at EVERY scale -/

/-- **CAPSTONE — the emergent budget-floor is strictly positive at every scale along
the irrational `e^{−1}` flow (UNCONDITIONAL).**  For the genuinely-irrational
`e^{−1}`-seeded self-similar flow `concreteTowerE 1` (where the rational `polyFlow`
provably fails the flow law) and ANY positive spacing schedule, the emergent floor
`physFloorC N = budgetC N · (1 / a_N)` is `PosEv` at every scale — with no open
hypothesis.  The UV seed positivity `e^{−1} > 0` is `posEv_expNeg_one`. -/
theorem physFloorC_pos_concreteE (A : SpacingSchedule) (N : Nat) :
    PosEv (physFloorC 1 (sep (concreteTowerE 1)) A N) :=
  physFloorC_pos_tower (concreteTowerE 1) posEv_expNeg_one A N

/-- **CAPSTONE — the GENUINE physical gap is strictly positive at every scale along the
irrational `e^{−1}` flow (UNCONDITIONAL).**  For `concreteTowerE 1` and any positive
spacing schedule, the genuine physical gap `physGapC N = (1 − sep N)·(1 / a_N)` is
`PosEv` at every scale.  Per-scale margin positivity is `margin_pos_tower` fed by the
propagated exponent positivity from `posEv_expNeg_one`.  (The spacing-UNIFORM floor over
a vanishing a→0 schedule remains the named open `UniformPhysGapFloor`.) -/
theorem physGapC_pos_concreteE (A : SpacingSchedule) (N : Nat) :
    PosEv (physGapC 1 (sep (concreteTowerE 1)) A N) :=
  physGapC_pos_tower (concreteTowerE 1) posEv_expNeg_one A N

/-- **CAPSTONE — the emergent floor is the conserved base margin rescaled, along the
`e^{−1}` flow.**  `physFloorC N ≃ (1 − sep 0)·(1 / a_N)` for the `concreteTowerE 1`
flow: the per-scale floor is the FIXED irrational UV margin `1 − e^{−(e^{−1})}` divided
by the spacing — the conserved-margin invariant at the floor level, on a flow with
genuinely irrational separators. -/
theorem physFloorC_conserved_concreteE (A : SpacingSchedule) (N : Nat) :
    CReal.Equiv (physFloorC 1 (sep (concreteTowerE 1)) A N)
      (CReal.mul (CReal.sub CReal.cone (sep (concreteTowerE 1) 0)) (recipSpacingC A N)) :=
  physFloorC_conserved (fun k => selfSimilarCReal (concreteTowerE 1) k) A N

end YMGap.Continuum.CodynamicPhysFloor

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CodynamicPhysFloor.recipSpacingC_pos
#print axioms YMGap.Continuum.CodynamicPhysFloor.physFloorC_pos_tower
#print axioms YMGap.Continuum.CodynamicPhysFloor.physFloorC_conserved
#print axioms YMGap.Continuum.CodynamicPhysFloor.posEv_scale_cancel
#print axioms YMGap.Continuum.CodynamicPhysFloor.posEv_w_succ
#print axioms YMGap.Continuum.CodynamicPhysFloor.posEv_w_tower
#print axioms YMGap.Continuum.CodynamicPhysFloor.margin_pos_tower
#print axioms YMGap.Continuum.CodynamicPhysFloor.physGapC_pos_tower
#print axioms YMGap.Continuum.CodynamicPhysFloor.CRealContinuumGapResidual.physGap_pos
#print axioms YMGap.Continuum.CodynamicPhysFloor.CRealContinuumGapResidual.continuumFloor_pos
#print axioms YMGap.Continuum.CodynamicPhysFloor.CRealContinuumGapResidual.continuumFloor_bound
#print axioms YMGap.Continuum.CodynamicPhysFloor.physFloorC_pos_concreteE
#print axioms YMGap.Continuum.CodynamicPhysFloor.physGapC_pos_concreteE
#print axioms YMGap.Continuum.CodynamicPhysFloor.physFloorC_conserved_concreteE
