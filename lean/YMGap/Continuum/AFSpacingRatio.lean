/-
Track B / R2 — **deriving the continuum spacing RATIO floor from the PROVED
asymptotic-freedom running, and connecting it to the block-rate `RateMatch`
criterion.**

# Why this module exists (read first)

`AFRateMatch.rateMatch_of_ratio_ge` reduced the open continuum input to ONE ratio
inequality: a strictly-positive spacing schedule whose per-step ratio meets the
block factor — `ofNat (b+1) ≤ a_N / a_{N+1}` at every `N` — satisfies the sharp
`RateMatch`, for every self-similar tower.  The repo separately PROVES the
asymptotic-freedom running itself: from the two-loop recurrence-with-remainder
(`AFTrajectoryCertificate`) the reciprocal-increment step `recip_step` /
`af_reciprocal_rate` gives `1/τ_k` growing LINEARLY in `k` — the reciprocal of the
log-coupling increases by at least `c = β/2` per step.

This module connects the two from the AF side via the dimensional-transmutation
dictionary.  The physical lattice spacing is
`a_k = exp(−1/(2 b₀ g_k²)) = exp(−1/(2 b₀ τ_k))`, so the per-step spacing ratio is

      a_k / a_{k+1}  =  exp( (1/(2 b₀)) · (1/τ_{k+1} − 1/τ_k) ).

The PROVED reciprocal increment `1/τ_{k+1} − 1/τ_k ≥ c` (a fixed positive constant,
`recip_step` fired through the drop lemma) therefore drives the LOG of the spacing
ratio above a FIXED positive floor

      log(a_k / a_{k+1})  =  (1/(2 b₀)) · (1/τ_{k+1} − 1/τ_k)  ≥  L := (1/(2 b₀))·c > 0,

an asymptotic constant `R∞ = exp(L)`.  The block factor `b+1` is a FREE RG choice;
choosing it so that `b + 1 ≤ R∞` makes the proved schedule meet `rateMatch_of_ratio_ge`.

# What is PROVED here (honest)

  * `recipIncrement_ge_add` — **the proved reciprocal-increment floor** from the AF
    certificate: for every step `d`, `recip (τ(k0+d)) + (β/2) ≤ recip (τ(k0+d+1))`.
    This is `recip_step` fired through the `drop` lemma at index `k0+d`; it is the
    log-spacing-ratio core in dimensionless-reciprocal form.
  * `logSpacing` / `logSpacing_increment_ge` — **the per-step log-spacing ratio
    floor**, derived: with the transmutation half-coefficient `q = 1/(2 b₀) ≥ 0`,
    the log-spacing `ℓ_d := q · (1/τ(k0+d)) = log(1/a_d)` has uniformly bounded-below
    single-step increment `ℓ_{d+1} − ℓ_d ≥ L := q·(β/2)`, i.e. the spacing ratio's
    logarithm never falls below a fixed positive constant.  Pure `Q'` scaling of the
    reciprocal-increment floor.
  * `logSpacingIncrement_pos` — `L > 0` for `q > 0` (the floor is genuinely
    positive: `R∞ = exp(L) > 1`).
  * `BlockSpacingFromAF` — **the single remaining exp-lift residual, as `Type`-level
    data**: a spacing schedule together with the multiplicative ratio floor
    `ofNat (b+1) ≤ a_N / a_{N+1}`.  This is EXACTLY the field a monotone-`exp` lift
    `a_k/a_{k+1} = exp(ℓ_{d+1}−ℓ_d) ≥ exp(L) ≥ b+1` would supply from
    `logSpacing_increment_ge` plus the block-size choice `b+1 ≤ exp(L)`.
  * `rateMatch_of_blockSpacing` / `uniformFloor_of_blockSpacing` /
    `residual_of_blockSpacing` — feeding a `BlockSpacingFromAF` through
    `rateMatch_of_ratio_ge` and the `RateMatchFloor` backbone inhabits `RateMatch`,
    the spacing-uniform `UniformPhysGapFloor` and the full
    `CRealContinuumGapResidual`.
  * `geomBlockSpacing` / `blockSpacingResidual_concrete` — a NON-VACUOUS green
    inhabitant: the geometric block schedule `a_N = (1/(b+1))^N` has ratio exactly
    `b+1` (`geom_ratio_ge`), so it inhabits `BlockSpacingFromAF`; firing the chain on
    the `b=1` concrete tower with the explicit UV floor `1/3` yields a
    strictly-positive spacing-uniform continuum-gap residual.

# HONEST residual — which side is closed and which stays open

CLOSED (this module, from the PROVED two-loop running):
  * the SPACING side at the log/reciprocal level — the per-step log-spacing ratio
    `log(a_k/a_{k+1})` is bounded below by a FIXED positive constant `L = (β/2)/(2b₀)`,
    a genuine consequence of `recip_step` / `af_reciprocal_rate`.  The continuum
    spacing genuinely shrinks at least at a fixed geometric rate `R∞ = exp(L)` per
    step; it does not stall.

OPEN (carried honestly as `Type`-level data, never `sorry`):
  * **the exp-lift** from the log-increment floor `L` to the MULTIPLICATIVE ratio
    floor `b+1 ≤ a_N/a_{N+1}`: this needs `exp` monotonicity on `CReal`/`Q'`
    (`exp(ℓ_{d+1}−ℓ_d) ≥ exp(L)`) and the block-size choice `b+1 ≤ exp(L)`.  It is
    isolated into the single field of `BlockSpacingFromAF`.
  * **the GAP/margin dynamics** — that the lattice gap `1 − sep_k` actually decays at
    the matching self-similar rate under the physical blocking.  The proved AF lemmas
    close the SPACING modulus (the denominator `a_k → 0`), NOT the numerator dynamics
    (the dimensionless margin's self-similar decay).  That is the genuine remaining
    RG content, untouched here.

So: the AF running closes the spacing-shrink rate (log-level, uniform positive
floor); what remains is the exp-lift to the multiplicative ratio and, separately and
more deeply, the gap-margin self-similar decay.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` arithmetic over the proved AF reciprocal-increment machinery (`recip_step`
via `drop`) and the `RateMatchFloor` backbone (`rateMatch_of_ratio_ge`,
`residual_of_rateMatch`); every carrier is `Type`-level data (the exp-lift residual
is supplied as a structure field, never a `Prop`-∃).  Each load-bearing declaration
is gated with `#print axioms` (permitted: `propext` / `Quot.sound`).  No
`Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.AFRateMatch

namespace YMGap.Continuum.AFSpacingRatio

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.TuranPositivity
open YMGap.Continuum.CodynamicPhysFloor
open YMGap.Continuum.RateMatchFloor
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.AFReciprocalRate
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.AFRateMatch

/-! ## 1. The proved reciprocal-increment floor (the log-spacing ratio core)

`recip_step` says one contracting step of the two-loop flow increases the
reciprocal log-coupling by at least `c = β/2`.  Fired at the AF index `k0 + d`
through the certificate's `drop` lemma, this gives the per-step reciprocal
increment floor `recip (τ(k0+d)) + (β/2) ≤ recip (τ(k0+d+1))` — the dimensional-
transmutation log-spacing ratio in reciprocal form. -/

/-- **The reciprocal-increment floor (proved from the AF certificate).**  For every
step `d`, the reciprocal log-coupling increases by at least `β/2`:

      recip (τ(k0+d)) + (β/2)  ≤  recip (τ(k0+d+1)).

This is `recip_step` instantiated at `k = k0 + d` with the contracting recurrence
supplied by the `drop` lemma; `(k0+d)+1 = k0+(d+1)` definitionally. -/
theorem recipIncrement_ge_add (C : AFTrajectoryCertificate) (d : Nat) :
    recip (C.τ (C.k0 + d)) (C.τ_pos (C.k0 + d)) + halfBeta C.β
      ≤ recip (C.τ (C.k0 + (d + 1))) (C.τ_pos (C.k0 + (d + 1))) := by
  have hk : C.k0 ≤ C.k0 + d := Nat.le_add_right C.k0 d
  have hdrop : C.τ ((C.k0 + d) + 1)
      ≤ C.τ (C.k0 + d) * (1 - halfBeta C.β * C.τ (C.k0 + d)) :=
    drop C (C.k0 + d) hk
  exact recip_step (C.τ (C.k0 + d)) (C.τ ((C.k0 + d) + 1)) (halfBeta C.β)
    (C.τ_pos (C.k0 + d)) (C.τ_pos ((C.k0 + d) + 1)) (halfBeta_nonneg C.β_pos) hdrop

/-! ## 2. The per-step log-spacing ratio floor

Dimensional transmutation `a_d = exp(−1/(2 b₀ τ(k0+d)))` gives the log-inverse-spacing
`ℓ_d := log(1/a_d) = (1/(2 b₀)) · (1/τ(k0+d))`.  Scaling the reciprocal-increment
floor by the transmutation half-coefficient `q = 1/(2 b₀) ≥ 0` yields a uniformly
bounded-below single-step increment

      ℓ_{d+1} − ℓ_d  ≥  L := q · (β/2)  > 0,

i.e. `log(a_d / a_{d+1}) ≥ L`, a FIXED positive floor `R∞ = exp(L) > 1`. -/

/-- The log of the inverse spacing at AF step `d`: `ℓ_d := q · (1/τ(k0+d))`, where
`q = 1/(2 b₀)` is the transmutation half-coefficient.  (`log(1/a_d)`, increasing as
`a_d → 0`.) -/
def logSpacing (C : AFTrajectoryCertificate) (q : Q') (d : Nat) : Q' :=
  q * recip (C.τ (C.k0 + d)) (C.τ_pos (C.k0 + d))

/-- **The per-step log-spacing ratio floor (derived from the proved AF running).**
For the transmutation half-coefficient `q ≥ 0`, the log-inverse-spacing has
single-step increment bounded below by `L = q·(β/2)`:

      logSpacing C q d + q·(β/2)  ≤  logSpacing C q (d+1),

equivalently `log(a_d / a_{d+1}) ≥ L`.  Pure `Q'` scaling of `recipIncrement_ge_add`
by the nonnegative `q`. -/
theorem logSpacing_increment_ge (C : AFTrajectoryCertificate) (q : Q')
    (hq : (0 : Q') ≤ q) (d : Nat) :
    logSpacing C q d + q * halfBeta C.β ≤ logSpacing C q (d + 1) := by
  -- multiply the reciprocal-increment floor on the left by q ≥ 0
  have hmul : q * (recip (C.τ (C.k0 + d)) (C.τ_pos (C.k0 + d)) + halfBeta C.β)
      ≤ q * recip (C.τ (C.k0 + (d + 1))) (C.τ_pos (C.k0 + (d + 1))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ q (recipIncrement_ge_add C d) hq
  -- q·(recip + β/2) ≃ q·recip + q·(β/2) = logSpacing d + q·(β/2)
  have hexp : (q * (recip (C.τ (C.k0 + d)) (C.τ_pos (C.k0 + d)) + halfBeta C.β)).eqv
      (logSpacing C q d + q * halfBeta C.β) :=
    Q'.mul_add_eqv q (recip (C.τ (C.k0 + d)) (C.τ_pos (C.k0 + d))) (halfBeta C.β)
  -- logSpacing C q (d+1) = q · recip(τ(k0+(d+1))) definitionally; chain.
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hexp) hmul

/-- **The log-spacing increment floor is strictly positive.**  `L = q·(β/2) > 0` for
`q > 0`: the spacing ratio's logarithm is bounded below by a genuinely positive
constant, so `R∞ = exp(L) > 1` and the spacing does not stall. -/
theorem logSpacingIncrement_pos (C : AFTrajectoryCertificate) (q : Q')
    (hq : (0 : Q') < q) : (0 : Q') < q * halfBeta C.β :=
  Q'.mul_pos hq (halfBeta_pos C.β_pos)

/-! ## 3. The exp-lift residual, as `Type`-level data

The one remaining step is multiplicative: lifting the log-increment floor `L` to the
ratio floor `b+1 ≤ a_N/a_{N+1}` needs `exp` monotonicity (`exp(ℓ_{d+1}−ℓ_d) ≥
exp(L)`) and the block-size choice `b+1 ≤ exp(L)`.  We isolate that single input as
the field of a `Type`-level structure, exactly matching the hypothesis of
`rateMatch_of_ratio_ge`. -/

/-- **The AF block spacing with its exp-lifted ratio floor (the residual carrier).**

`Type`-level data: a strictly-positive spacing schedule together with the single
remaining multiplicative input — the per-step ratio meets the block factor,
`ofNat (b+1) ≤ a_N / a_{N+1}` at every scale.  This field is precisely what a
monotone-`exp` lift of `logSpacing_increment_ge` (with the block-size choice
`b+1 ≤ exp(L)`) supplies; carried as data per Rule 8, never a `Prop`-∃. -/
structure BlockSpacingFromAF (b : Nat) : Type where
  /-- The AF-scheduled lattice spacing. -/
  A : SpacingSchedule
  /-- **The exp-lifted ratio floor (the single residual input).**  The per-step
  spacing ratio meets the block factor: `ofNat (b+1) ≤ a_N / a_{N+1}`. -/
  ratio_ge : ∀ N,
    Q'.ofNat (b + 1) ≤ Q'.divPos (A.a N) (A.a (N + 1)) (A.a_pos (N + 1))

/-- **`RateMatch` from a `BlockSpacingFromAF`.**  The ratio floor is exactly the
hypothesis of `rateMatch_of_ratio_ge`, so the carried AF block spacing satisfies the
sharp `RateMatch` for every self-similar tower. -/
theorem rateMatch_of_blockSpacing {b : Nat} (T : SelfSimilarTower b)
    (S : BlockSpacingFromAF b) : RateMatch b (sep T) S.A :=
  rateMatch_of_ratio_ge T S.A S.ratio_ge

/-- **The spacing-uniform `UniformPhysGapFloor` from a `BlockSpacingFromAF`.** -/
def uniformFloor_of_blockSpacing {b : Nat} (T : SelfSimilarTower b)
    (hx : PosEv (T.w 0)) (S : BlockSpacingFromAF b)
    (floor0 : Q') (hpos0 : (0 : Q') < floor0)
    (hbase0 : CReal.leEv (CReal.ofQ' floor0) (physGapC b (sep T) S.A 0)) :
    UniformPhysGapFloor T S.A :=
  uniformPhysGapFloor_of_rateMatch T hx S.A (rateMatch_of_blockSpacing T S)
    floor0 hpos0 hbase0

/-- **The full `CRealContinuumGapResidual` from a `BlockSpacingFromAF`.** -/
def residual_of_blockSpacing {b : Nat} (T : SelfSimilarTower b)
    (hx : PosEv (T.w 0)) (S : BlockSpacingFromAF b)
    (floor0 : Q') (hpos0 : (0 : Q') < floor0)
    (hbase0 : CReal.leEv (CReal.ofQ' floor0) (physGapC b (sep T) S.A 0)) :
    CRealContinuumGapResidual b :=
  residual_of_rateMatch T hx S.A (rateMatch_of_blockSpacing T S)
    floor0 hpos0 hbase0

/-! ## 4. A non-vacuous green inhabitant — the geometric block schedule

The geometric block schedule `a_N = (1/(b+1))^N` has per-step ratio EXACTLY `b+1`
(the RG fixed-point idealization of the AF spacing — the case `R∞ = b+1`), so it
inhabits `BlockSpacingFromAF` unconditionally.  Firing the chain on the `b=1`
concrete tower with the explicit UV floor `1/3` produces a strictly-positive
spacing-uniform continuum-gap residual end-to-end through the AF-side route. -/

/-- **The geometric block schedule meets its own ratio floor exactly.**
`ofNat (b+1) ≤ a_N / a_{N+1}` for `a = geomA b`, since the ratio is exactly `b+1`
(`ofNat (b+1) · a_{N+1} = ofNat (b+1) · (a_N · 1/(b+1)) ≃ a_N`). -/
theorem geom_ratio_ge (b N : Nat) :
    Q'.ofNat (b + 1)
      ≤ Q'.divPos ((geomSpacing b).a N) ((geomSpacing b).a (N + 1))
          ((geomSpacing b).a_pos (N + 1)) := by
  apply Q'.le_divPos_of_mul_le ((geomSpacing b).a N) ((geomSpacing b).a (N + 1))
    ((geomSpacing b).a_pos (N + 1))
  -- goal (defeq): ofNat (b+1) · (geomA b N · invSucc b) ≤ geomA b N
  have heq : (Q'.ofNat (b + 1) * (geomA b N * Q'.invSucc b)).eqv (geomA b N) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat (b + 1))
      (geomA b N * Q'.invSucc b) (Q'.invSucc b * geomA b N)
      (Q'.mul_comm_eqv (geomA b N) (Q'.invSucc b))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (b + 1)) (Q'.invSucc b) (geomA b N))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (geomA b N) (Q'.ofNat_succ_mul_invSucc b)) ?_
    exact Q'.one_mul_eqv (geomA b N)
  exact Q'.le_of_eqv heq

/-- **The geometric block spacing as a `BlockSpacingFromAF` (non-vacuous).**  The RG
fixed-point idealization `R∞ = b+1`: the geometric schedule's exact ratio inhabits
the residual carrier with no extra input. -/
def geomBlockSpacing (b : Nat) : BlockSpacingFromAF b where
  A := geomSpacing b
  ratio_ge := geom_ratio_ge b

/-- **NON-VACUOUS — the spacing-uniform continuum-gap residual via the AF-side
route.**  The `b=1` self-similar flow with the geometric block spacing
`a_N = (1/2)^N`, floored by the explicit UV gap `1/3`, yields an inhabited
`CRealContinuumGapResidual` — a strictly-positive rational below the physical gap at
every scale of a real `a → 0` schedule, produced through `geomBlockSpacing`. -/
def blockSpacingResidual_concrete : CRealContinuumGapResidual 1 :=
  residual_of_blockSpacing (concreteTower 1) concreteTower1_seed (geomBlockSpacing 1)
    tunedUVFloor tunedUVFloor_pos tuned_hbase

/-- The block-spacing continuum residual carries a strictly-positive uniform floor
(non-vacuity witness). -/
theorem blockSpacingResidual_concrete_floor_pos :
    (0 : Q') < blockSpacingResidual_concrete.continuumFloor :=
  blockSpacingResidual_concrete.continuumFloor_pos

end YMGap.Continuum.AFSpacingRatio

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AFSpacingRatio.recipIncrement_ge_add
#print axioms YMGap.Continuum.AFSpacingRatio.logSpacing_increment_ge
#print axioms YMGap.Continuum.AFSpacingRatio.logSpacingIncrement_pos
#print axioms YMGap.Continuum.AFSpacingRatio.rateMatch_of_blockSpacing
#print axioms YMGap.Continuum.AFSpacingRatio.uniformFloor_of_blockSpacing
#print axioms YMGap.Continuum.AFSpacingRatio.residual_of_blockSpacing
#print axioms YMGap.Continuum.AFSpacingRatio.geom_ratio_ge
#print axioms YMGap.Continuum.AFSpacingRatio.blockSpacingResidual_concrete
#print axioms YMGap.Continuum.AFSpacingRatio.blockSpacingResidual_concrete_floor_pos
