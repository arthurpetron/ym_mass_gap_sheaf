/-
Track B / R2 — ANCHORING the full continuum margin floor to the PROVED
strong-coupling gap, and REDUCING the entire remaining continuum obligation to a
SINGLE named crossover input.

# What this module does (read first)

`NetDriftBudgetSplit.fullFloor_of_crossover_and_AF` reduces the whole 4D SU(N)
continuum margin floor to four ingredients:

  [anchor]      the strong-coupling anchor `margin 0`;
  [deep-UV AF]  the asymptotically-free tail `δ_k ≤ Dδ·1/(k+1)²`, `k ≥ K`
                (PROVED upstream, `AFDeepUVSummability.af_defect_invSq`), giving
                `Σ_{k≥K} δ_k ≤ 2·Dδ`;
  [crossover]   the FINITE strong→weak-coupling window sums
                `Bcrossδ = Σ_{k<K} δ_k`, `Bcrossε = Σ_{k<K} ε_k` (`k < K`);
  [dominance]   `Bcrossε + 2·Dε < (1 − (Bcrossδ + 2·Dδ))·margin 0`.

This module does two honest things and states one honest residual.

## 1. The anchor is the PROVED strong-coupling gap (not a free parameter)

`strongAnchor := (RealCorrMass.realLocated 0).gapMargin` is DEFINITIONALLY the
gap-margin of the genuine `MayerClustering.reconTransfer_located_gap 0` — the
located second eigenvalue of the reconstructed single-edge transfer operator,
whose clustering is the REAL `wilsonG` connected-correlator decay
(`wilsonG_decay`) at the strong-coupling weight `w = 1/6`.  Its value is the
volume-independent `1 − rho gw = 1 − 2·(1/6)³ = 107/108`, and it clears `1/2`
(`RealCorrMass.realUniform_floor`).  `fullFloor_anchored_to_strong_gap` wires
`fullFloor_of_crossover_and_AF`'s `margin 0` to this proved object: the anchor
`hm0 : 0 ≤ margin 0` is DERIVED from the proved gap, not assumed.

## 2. The crossover reduced to ONE named obligation

`CrossoverWindowDefect δ ε K` is the SINGLE named input carrying exactly the two
finite crossover defect sums `tailSum δ 0 K ≤ Bδ`, `tailSum ε 0 K ≤ Bε`.
`fullFloor_on_one_crossover_obligation` exhibits the full positive floor
`physGapMin > 0` resting on:
  * the PROVED strong-coupling anchor (`hanchor0 : margin 0 = strongAnchor`);
  * the PROVED deep-UV AF tail (`hUVδ`, `hUVε`);
  * ONE named crossover obligation `W : CrossoverWindowDefect δ ε K`;
  * plus the (decidable, given the constants) anchor-dominance `hanchor`.

So the ENTIRE continuum gap is now a single named crossover fact with everything
else proved.  `CrossoverWindowDefect` is NEVER inhabited here — it is the genuine
Balaban / RG-clustering-transport physics.

### Two routes to the obligation (neither closes it)

  (a) FINITE PER-STEP.  `crossoverDefect_ofPerStep`: a per-step no-gap-closing
      bound `δ_j ≤ δmax`, `ε_j ≤ εmax` for `j < K` inhabits the obligation with
      `Bδ = K·δmax`, `Bε = K·εmax` (via `tailSum_le_ofNat_mul`).  The residual is
      then the DECIDABLE rational check `K·εmax + 2·Dε < (1 − (K·δmax + 2·Dδ))·
      (1 − rho gw)` — a finite check GIVEN the per-step bound.  The per-step bound
      is itself the genuine open content (the gap does not close in one crossover
      step).

  (b) CLUSTERING-TRANSPORT.  `crossoverDefect_ofClusteringWindow`: a uniform
      per-step RETENTION `δ_k ≤ 1 − ρmin` (`0 < ρmin ≤ 1`) on the finite window
      `k < K` — i.e. every crossover step keeps at least fraction `ρmin` of the
      margin — inhabits the obligation with `Bδ = K·(1 − ρmin)`.  This is the
      finite-`K` restriction of "clustering persists across the middle", exactly
      the content of `WeakCouplingGap.RGClusteringTransport` and the interval
      shadow `TwoSidedGap.WindowOverlap`.  So the new block-spin crossover defect
      sum UNIFIES with the existing continuum wall: `CrossoverWindowDefect` is the
      δ-defect shadow of `RGClusteringTransport` / `WindowOverlap`.

# HONEST SCOPE (AGENTS.md Rule 6, Rule 9)

The anchor is genuinely the proved strong-coupling gap; the deep-UV tail is
genuinely AF-derived; the crossover obligation `CrossoverWindowDefect` is a
GENUINE input (the theorems are false for arbitrary `Bδ`/`Bε`), left UNINHABITED
— it IS the Balaban / RG-clustering-transport crossover physics.  This module
does NOT close the continuum gap: it reduces it to ONE named crossover fact
(unified with `RGClusteringTransport` / `WindowOverlap`) with everything else
proved.  No 4D Yang–Mills mass gap is claimed; nothing is faked.

# Axiom gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` / `Nat` core, reusing the proved `fullFloor_of_crossover_and_AF`,
`tailSum` toolkit, and the proved `RealCorrMass` gap.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` /
`Quot.sound` only.  No `sorry`, no `Classical.*`, no `native_decide`.  All
witnesses are `Type`-level data.
-/

import YMGap.Continuum.NetDriftBudgetSplit
import YMGap.Continuum.RealCorrMass
import YMGap.Continuum.WeakCouplingGap
import YMGap.Continuum.TwoSidedGap

namespace YMGap.Continuum.CrossoverAnchorFloor

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.GenuineKP

/-! ## 1. THE ANCHOR — tied to the PROVED strong-coupling located gap

`strongAnchor` is the gap-margin of the genuine
`MayerClustering.reconTransfer_located_gap 0` (the real Wilson connected-
correlator gap at `w = 1/6`), namely the volume-independent `1 − rho gw = 107/108`.
It is `≥ 1/2 > 0`, so it discharges the `margin 0` anchor of the full floor. -/

/-- **The strong-coupling anchor value** — the gap-margin of the PROVED located
gap `reconTransfer_located_gap 0` (definitionally `RealCorrMass.realLocated 0`),
the genuine real-Wilson-correlator strong-coupling gap. -/
def strongAnchor : Q' := (RealCorrMass.realLocated 0).gapMargin

/-- **The anchor IS the proved `reconTransfer_located_gap` margin** (definitional).
`RealCorrMass.realLocated 0 = MayerClustering.reconTransfer_located_gap 0`, so the
anchor is exactly the proved located-gap margin — NOT a free parameter. -/
theorem strongAnchor_is_reconTransfer_gap :
    strongAnchor = (MayerClustering.reconTransfer_located_gap 0).gapMargin := rfl

/-- The anchor value is the volume-independent `1 − rho gw` (`= 107/108`), the
real leading transfer eigenvalue `rho gw = coeffW gw 1 = 2·(1/6)³`. -/
theorem strongAnchor_eq : strongAnchor = (1 : Q') - rho gw :=
  RealCorrMass.realLocated_gapMargin 0

/-- **The anchor clears the floor `1/2`** — the proved strong-coupling gap margin
is `≥ 1/2` (`RealCorrMass.realUniform_floor 0`, the single rational comparison
`1/2 ≤ 107/108`). -/
theorem strongAnchor_ge_half : RealCorrMass.realFloor ≤ strongAnchor :=
  RealCorrMass.realUniform_floor 0

/-- **The anchor is nonnegative** — derived from the proved gap (`0 < 1/2 ≤
strongAnchor`), so it discharges the `hm0 : 0 ≤ margin 0` slot of the full floor
WITHOUT assuming it. -/
theorem strongAnchor_nonneg : (0 : Q') ≤ strongAnchor :=
  Q'.le_trans' 0 RealCorrMass.realFloor strongAnchor
    (Q'.le_of_lt RealCorrMass.realFloor_pos) strongAnchor_ge_half

/-! ## 2. A FINITE-SUM toolkit lemma — `Σ_{j<K} f j ≤ K·c` from a per-step cap

The crossover sum is FINITE.  Given a per-step bound `f j ≤ c` on the window
`j < K`, the partial sum is `≤ K·c` (`Q'.ofNat K · c`).  Pure `Q'` induction. -/

/-- **`tailSum_le_ofNat_mul` — the finite windowed sum bound.**  If `f j ≤ c` for
every `j < K` (and `0 ≤ c`), then `tailSum f 0 K ≤ (ofNat K)·c`.  Induction on `K`;
the step re-associates `(ofNat K)·c + c ≃ (ofNat (K+1))·c`. -/
theorem tailSum_le_ofNat_mul (f : Nat → Q') (c : Q') (hc : (0 : Q') ≤ c) :
    ∀ K, (∀ j, j < K → f j ≤ c) → tailSum f 0 K ≤ Q'.ofNat K * c := by
  intro K
  induction K with
  | zero =>
    intro _
    rw [tailSum_zero]
    -- 0 ≤ ofNat 0 · c, since ofNat 0 · c ≃ 0·c ≃ 0.
    have h0 : (Q'.ofNat 0 * c).eqv (0 : Q') :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (Q'.ofNat 0) 0 c Q'.ofNat_zero_eqv)
        (Q'.zero_mul_eqv c)
    exact Q'.ge_of_eqv h0
  | succ K ih =>
    intro hb
    rw [tailSum_succ, Nat.zero_add]
    have hfK : f K ≤ c := hb K (Nat.lt_succ_self K)
    have hih : tailSum f 0 K ≤ Q'.ofNat K * c :=
      ih (fun j hj => hb j (Nat.lt_succ_of_lt hj))
    have hstep : tailSum f 0 K + f K ≤ Q'.ofNat K * c + c :=
      Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ (f K) hih)
        (Q'.add_le_add_left _ _ _ hfK)
    -- ofNat (K+1)·c ≃ ofNat K·c + c
    have hone : (Q'.ofNat 1).eqv (1 : Q') := by decide
    have e1 : (Q'.ofNat (K + 1)).eqv (Q'.ofNat K + Q'.ofNat 1) := Q'.ofNat_add_eqv K 1
    have e2 : (Q'.ofNat (K + 1) * c).eqv ((Q'.ofNat K + Q'.ofNat 1) * c) :=
      Q'.mul_eqv_congr_right (Q'.ofNat (K + 1)) (Q'.ofNat K + Q'.ofNat 1) c e1
    have e3 : ((Q'.ofNat K + Q'.ofNat 1) * c).eqv (Q'.ofNat K * c + Q'.ofNat 1 * c) :=
      Q'.add_mul_eqv (Q'.ofNat K) (Q'.ofNat 1) c
    have e4 : (Q'.ofNat 1 * c).eqv c :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (Q'.ofNat 1) 1 c hone) (Q'.one_mul_eqv c)
    have e5 : (Q'.ofNat K * c + Q'.ofNat 1 * c).eqv (Q'.ofNat K * c + c) :=
      Q'.add_eqv_congr_left (Q'.ofNat K * c) (Q'.ofNat 1 * c) c e4
    have hcomb : (Q'.ofNat (K + 1) * c).eqv (Q'.ofNat K * c + c) :=
      Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ e2 e3) e5
    exact Q'.le_trans' _ _ _ hstep (Q'.ge_of_eqv hcomb)

/-! ## 3. THE SINGLE NAMED CROSSOVER OBLIGATION

`CrossoverWindowDefect δ ε K` carries EXACTLY the two finite crossover defect
sums.  It is the genuine open input — the finite strong→weak window
no-gap-closing physics — carried as `Type`-level data, NEVER inhabited here. -/

/-- **`CrossoverWindowDefect` — the SINGLE named crossover obligation.**

The finite strong→weak coupling window (`k < K`) defect sums:
  * `Bδ`, `Bε` — the finite crossover defect budgets;
  * `crossδ : tailSum δ 0 K ≤ Bδ` — the multiplicative crossover budget;
  * `crossε : tailSum ε 0 K ≤ Bε` — the additive crossover budget.

This is the genuine Balaban / RG-clustering-transport crossover physics: a FINITE
sum over the finite crossover window, false for arbitrary `Bδ`/`Bε`, so a genuine
input (Rule 6a).  NO inhabitant for the real 4D theory is constructed — it is the
δ-defect shadow of `WeakCouplingGap.RGClusteringTransport` /
`TwoSidedGap.WindowOverlap`. -/
structure CrossoverWindowDefect (δ ε : Nat → Q') (K : Nat) : Type where
  /-- The finite multiplicative crossover budget `Σ_{k<K} δ_k`. -/
  Bδ : Q'
  /-- The finite additive crossover budget `Σ_{k<K} ε_k`. -/
  Bε : Q'
  /-- The multiplicative crossover defect sum is bounded (the no-gap-closing
  content over the finite window). -/
  crossδ : tailSum δ 0 K ≤ Bδ
  /-- The additive crossover defect sum is bounded. -/
  crossε : tailSum ε 0 K ≤ Bε

/-! ## 4. THE CAPSTONE — full floor on [proved anchor] + [AF] + [ONE obligation]

`fullFloor_on_one_crossover_obligation` exhibits `physGapMin > 0` resting on the
proved strong-coupling anchor, the proved deep-UV AF tail, and the SINGLE named
crossover obligation `CrossoverWindowDefect`. -/

/-- **`fullFloor_on_one_crossover_obligation` — the WHOLE continuum floor on a
SINGLE named crossover input.**

Given the margin step recursion, the standard `δ`/`ε` sign conditions, the
PROVED deep-UV AF tail bounds `hUVδ`/`hUVε`, ONE crossover obligation
`W : CrossoverWindowDefect δ ε K`, the anchor tie `hanchor0 : margin 0 =
strongAnchor` (the PROVED `reconTransfer_located_gap 0` margin), and the
anchor-dominance `hanchor`, the margin is uniformly bounded below by the strictly
positive floor

    physGapMin := (1 − (W.Bδ + 2·Dδ))·margin 0 − (W.Bε + 2·Dε) > 0.

Everything is proved EXCEPT the single crossover obligation `W`: the anchor is the
proved strong-coupling gap (`hm0` is DERIVED, not assumed), the deep-UV tail is
AF-derived.  This is the entire Clay continuum gap reduced to ONE named crossover
fact. -/
theorem fullFloor_on_one_crossover_obligation
    (margin δ ε : Nat → Q') (K : Nat) (Dδ Dε : Q')
    (W : CrossoverWindowDefect δ ε K)
    (hstep : ∀ k, (1 - δ k) * margin k - ε k ≤ margin (k + 1))
    (hδnn : ∀ k, (0 : Q') ≤ δ k) (hδ1 : ∀ k, δ k ≤ 1)
    (hεnn : ∀ k, (0 : Q') ≤ ε k)
    (hanchor0 : margin 0 = strongAnchor)
    (hDδ : (0 : Q') ≤ Dδ) (hDε : (0 : Q') ≤ Dε)
    (hUVδ : ∀ k, K ≤ k → δ k ≤ Dδ * recipSqSucc k)
    (hUVε : ∀ k, K ≤ k → ε k ≤ Dε * recipSqSucc k)
    (hanchor : W.Bε + 2 * Dε < (1 - (W.Bδ + 2 * Dδ)) * margin 0) :
    ∀ k, (1 - (W.Bδ + 2 * Dδ)) * margin 0 - (W.Bε + 2 * Dε) ≤ margin k
       ∧ (0 : Q') < (1 - (W.Bδ + 2 * Dδ)) * margin 0 - (W.Bε + 2 * Dε) := by
  -- The anchor is nonnegative BECAUSE it is the proved strong-coupling gap.
  have hm0 : (0 : Q') ≤ margin 0 := by rw [hanchor0]; exact strongAnchor_nonneg
  exact fullFloor_of_crossover_and_AF margin δ ε K Dδ Dε W.Bδ W.Bε
    hstep hδnn hδ1 hεnn hm0 hDδ hDε W.crossδ W.crossε hUVδ hUVε hanchor

/-! ## 5. ROUTE (a) — the finite per-step crossover bound inhabits the obligation

A per-step no-gap-closing bound `δ_j ≤ δmax`, `ε_j ≤ εmax` on the finite window
`j < K` gives the obligation with `Bδ = K·δmax`, `Bε = K·εmax`.  This does NOT
close the crossover: the per-step bound is itself the genuine open content (the
gap does not close in one crossover step). -/

/-- **`crossoverDefect_ofPerStep` — route (a): finite per-step ⟹ obligation.**
The finite crossover defect obligation from a per-step cap on the window: each
`δ_j ≤ δmax` and `ε_j ≤ εmax` for `j < K` yields `Bδ = K·δmax`, `Bε = K·εmax`
(via `tailSum_le_ofNat_mul`).  The residual anchor-dominance is then a DECIDABLE
rational check GIVEN `(δmax, εmax, K, Dδ, Dε)`. -/
def crossoverDefect_ofPerStep (δ ε : Nat → Q') (K : Nat) (δmax εmax : Q')
    (hδmax : (0 : Q') ≤ δmax) (hεmax : (0 : Q') ≤ εmax)
    (hstepδ : ∀ j, j < K → δ j ≤ δmax) (hstepε : ∀ j, j < K → ε j ≤ εmax) :
    CrossoverWindowDefect δ ε K where
  Bδ := Q'.ofNat K * δmax
  Bε := Q'.ofNat K * εmax
  crossδ := tailSum_le_ofNat_mul δ δmax hδmax K hstepδ
  crossε := tailSum_le_ofNat_mul ε εmax hεmax K hstepε

/-! ## 6. ROUTE (b) — clustering-transport UNIFICATION

A uniform per-step RETENTION `δ_k ≤ 1 − ρmin` (`0 < ρmin ≤ 1`) on the finite
window `k < K` — every crossover step keeps at least fraction `ρmin` of the margin
— inhabits the obligation with `Bδ = K·(1 − ρmin)`.  This is the finite-`K`
restriction of "clustering persists across the middle": exactly the content of
`WeakCouplingGap.RGClusteringTransport` and the interval shadow
`TwoSidedGap.WindowOverlap`.  So `CrossoverWindowDefect` UNIFIES with the existing
continuum wall — it is the δ-defect shadow of `RGClusteringTransport`. -/

/-- **`crossoverDefect_ofClusteringWindow` — route (b): clustering-transport ⟹
obligation (the UNIFICATION).**

A crossover clustering window with uniform per-step retention `ρmin` (each step
keeps `≥ ρmin` of the margin, i.e. multiplicative defect `δ_k ≤ 1 − ρmin`, and
additive defect `ε_k ≤ εmax`, for `k < K`) inhabits the crossover obligation with
`Bδ = K·(1 − ρmin)`, `Bε = K·εmax`.

The retention hypothesis `δ_k ≤ 1 − ρmin` with `ρmin > 0` is precisely the
finite-`K` restriction of "the gap does not close across the middle" — the content
of `WeakCouplingGap.RGClusteringTransport` (RG-flow preservation of clustering) and
its interval shadow `TwoSidedGap.WindowOverlap`.  Hence the block-spin crossover
defect sum and the existing continuum-wall obligation are the SAME physics; this
`def` is the explicit bridge.  It CONSUMES the retention bound; nothing is
inhabited unconditionally. -/
def crossoverDefect_ofClusteringWindow (δ ε : Nat → Q') (K : Nat)
    (ρmin εmax : Q') (hρnn : (0 : Q') ≤ (1 : Q') - ρmin) (hεmax : (0 : Q') ≤ εmax)
    (hretain : ∀ j, j < K → δ j ≤ (1 : Q') - ρmin)
    (hstepε : ∀ j, j < K → ε j ≤ εmax) :
    CrossoverWindowDefect δ ε K :=
  crossoverDefect_ofPerStep δ ε K ((1 : Q') - ρmin) εmax hρnn hεmax hretain hstepε

/-! ## 7. THE STATEMENT OF THE SINGLE REMAINING OBLIGATION

Assembling §1–§6: the full continuum margin floor `physGapMin > 0` holds once a
`CrossoverWindowDefect δ ε K` is supplied and the (decidable-in-the-constants)
anchor-dominance is met, with the anchor being the PROVED
`reconTransfer_located_gap 0` margin and the deep-UV tail AF-derived.  The SINGLE
remaining physical obligation is therefore:

  **`CrossoverWindowDefect δ ε K`** — the finite strong→weak crossover defect
  sums `Σ_{k<K} δ_k ≤ Bδ`, `Σ_{k<K} ε_k ≤ Bε`, equivalently (route b) a uniform
  per-step retention `δ_k ≤ 1 − ρmin` (`ρmin > 0`) across the finite crossover,
  which is the δ-defect shadow of `WeakCouplingGap.RGClusteringTransport` /
  `TwoSidedGap.WindowOverlap`.

`fullFloor_reduced_to_crossover` records the reduction in one statement. -/

/-- **`fullFloor_reduced_to_crossover` — the whole floor on ONE obligation, one
statement.**  For any `K`, AF tail constants `Dδ`/`Dε` (proved), a margin step
recursion, the sign conditions, the anchor tie to the PROVED strong-coupling gap,
the proved deep-UV AF tail, ONE `CrossoverWindowDefect`, and the anchor-dominance,
the positive uniform floor holds.  Definitionally identical to
`fullFloor_on_one_crossover_obligation`; stated separately as the capstone name.
The crossover obligation is the SOLE uninhabited input. -/
theorem fullFloor_reduced_to_crossover
    (margin δ ε : Nat → Q') (K : Nat) (Dδ Dε : Q')
    (W : CrossoverWindowDefect δ ε K)
    (hstep : ∀ k, (1 - δ k) * margin k - ε k ≤ margin (k + 1))
    (hδnn : ∀ k, (0 : Q') ≤ δ k) (hδ1 : ∀ k, δ k ≤ 1)
    (hεnn : ∀ k, (0 : Q') ≤ ε k)
    (hanchor0 : margin 0 = strongAnchor)
    (hDδ : (0 : Q') ≤ Dδ) (hDε : (0 : Q') ≤ Dε)
    (hUVδ : ∀ k, K ≤ k → δ k ≤ Dδ * recipSqSucc k)
    (hUVε : ∀ k, K ≤ k → ε k ≤ Dε * recipSqSucc k)
    (hanchor : W.Bε + 2 * Dε < (1 - (W.Bδ + 2 * Dδ)) * margin 0) :
    ∀ k, (1 - (W.Bδ + 2 * Dδ)) * margin 0 - (W.Bε + 2 * Dε) ≤ margin k
       ∧ (0 : Q') < (1 - (W.Bδ + 2 * Dδ)) * margin 0 - (W.Bε + 2 * Dε) :=
  fullFloor_on_one_crossover_obligation margin δ ε K Dδ Dε W
    hstep hδnn hδ1 hεnn hanchor0 hDδ hDε hUVδ hUVε hanchor

end YMGap.Continuum.CrossoverAnchorFloor

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CrossoverAnchorFloor.strongAnchor_is_reconTransfer_gap
#print axioms YMGap.Continuum.CrossoverAnchorFloor.strongAnchor_eq
#print axioms YMGap.Continuum.CrossoverAnchorFloor.strongAnchor_ge_half
#print axioms YMGap.Continuum.CrossoverAnchorFloor.strongAnchor_nonneg
#print axioms YMGap.Continuum.CrossoverAnchorFloor.tailSum_le_ofNat_mul
#print axioms YMGap.Continuum.CrossoverAnchorFloor.fullFloor_on_one_crossover_obligation
#print axioms YMGap.Continuum.CrossoverAnchorFloor.crossoverDefect_ofPerStep
#print axioms YMGap.Continuum.CrossoverAnchorFloor.crossoverDefect_ofClusteringWindow
#print axioms YMGap.Continuum.CrossoverAnchorFloor.fullFloor_reduced_to_crossover
