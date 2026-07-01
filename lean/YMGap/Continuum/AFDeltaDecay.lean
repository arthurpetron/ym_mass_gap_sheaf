/-
Track B / R2 — **Relaxing the exact `δ=0` self-similar descent to a SUMMABLE-`δ`
input: the asymptotic (bond-moving-defect) exponent descent.**

# What this module does (read first)

`PhysicalRGSelfSimilar`'s single sharp input is the EXACT descent field of
`SelfSimilarTower b` (`Constructive/SelfSimilarFlow.lean`):

    div : scaleN (b+1) (w_{k+1}) ≃ w_k     pointwise   (δ = 0 exactly),

which forces the exact separator law `sep_k ≃ (sep_{k+1})^(b+1)`.  Only the
hierarchical / diamond lattice inhabits `δ=0`; ℝ⁴ cannot (MK is approximate).

This module relaxes `div` to a SUMMABLE rational defect and reconnects three
already-green machines:

  * **`SummableDescentTower b`** (§1) — the approximate descent
    `w_k ≃ (b+1)·w_{k+1} + δ_k` with a per-step rational defect `δ_k ∈ [0,½]`
    whose partial sums are uniformly bounded (`∑ δ ≤ R`).  `SelfSimilarTower`
    embeds as the `δ≡0, R=0` special case (`ofSelfSimilar`).

  * **(T1) `descent_selfSimilarC_defect_step`** (§3) — the ASYMPTOTIC separator
    law `sep_k ≃ (sep_{k+1})^(b+1)·e^{−δ_k}`.  Pure plumbing: the exact peel
    `descent_selfSimilarC_step` carrying the extra `e^{−δ_k}` factor instead of
    cancelling it, via `expNegCD_add` + `expNegCD_powerLaw`.

  * **(T2) `defect_product_floor`** (§4) — the accumulated STRICTLY-POSITIVE
    product floor `c = e^{−2R} > 0` with `c ≤ ∏_{k<n}(1−δ_k)` at every prefix,
    the `ExpProductFloor.sum_loss_to_productFloor_exp` output rewrapped with the
    tower's own `δ`.  Its rational distillate `defect_product_floor_rat`
    (bridged by `le_of_geRat_leRat`) gives a positive rational floor.

  * **The payoff** (§5) — `AsymptoticDescentInput b` packages the tower's
    `rho := 1−δ` and product floor into `RGGapPersistence.RGBlockPersistence`,
    so `blockPersistence_uniform_floor` yields the uniform physical-gap floor
    WITHOUT exact `δ=0`.  The SOLE genuinely-open field is the per-block margin
    recursion `(1−δ_k)·physGap_k ≤ physGap_{k+1}` — the `hlocalize`/`hbound`
    spectral-localization residual, never a new summability obligation.

# Honest scope

T1, T2 and the `RGBlockPersistence` packaging are genuine axiom-clean plumbing
connecting three green machines; `SelfSimilarTower` embeds as `δ≡0` so nothing
regresses.  The per-block margin recursion (`AsymptoticDescentInput.recursion`)
remains the single named open residual — exactly the `s=1`-scope spectral
localization; it is NOT fabricated.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over `SelfSimilarFlow` / `ExpProductFloor` / `RGGapPersistence`;
every carrier is `Type`-level data.  Each load-bearing declaration is gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).  No `Classical.*`, no
`native_decide`, no `sorry`, no custom `axiom`.
-/

import YMGap.Constructive.SelfSimilarFlow
import YMGap.Continuum.ExpProductFloor
import YMGap.Continuum.AFRateCalibration

namespace YMGap.Continuum.AFDeltaDecay

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ProductFloor

/-! ## 1. The summable-defect descent tower -/

/-- **A summable-defect exponent descent tower** (block factor `b`).  The EXACT
`δ=0` descent of `SelfSimilarTower` is relaxed to an APPROXIMATE descent
`w_k ≃ (b+1)·w_{k+1} + δ_k` with a per-step rational majorant `δ_k ∈ [0,½]`
whose partial sums are uniformly bounded (`∑ δ ≤ R`).  `SelfSimilarTower b` is
the `δ≡0, R=0` special case (`ofSelfSimilar`). -/
structure SummableDescentTower (b : Nat) : Type where
  /-- The exponent at scale `k`. -/
  w : Nat → CReal
  /-- Its modulus data. -/
  dw : ∀ k, ExpNegCData (w k)
  /-- The `(b+1)`-fold sub-unit bound at level `k+1` (as for `SelfSimilarTower`). -/
  bnd : ∀ k j, (scaleN (b + 1) (w (k + 1))).approx j ≤ 1
  /-- The per-step rational defect majorant `δ_k` (`= renDefect` in the AF case). -/
  δ : Nat → Q'
  /-- The defect is nonnegative. -/
  δ_nonneg : ∀ k, (0 : Q') ≤ δ k
  /-- The defect is `≤ ½` (the tail condition the product floor consumes). -/
  δ_le_half : ∀ k, δ k ≤ HalfPow.half
  /-- The sub-unit bound on the APPROXIMATE exponent `(b+1)·w_{k+1} + δ_k`. -/
  sumbnd : ∀ k j, (scaleN (b + 1) (w (k + 1))).approx j + δ k ≤ 1
  /-- **APPROXIMATE descent** (pointwise): `w_k ≃ (b+1)·w_{k+1} + δ_k`.
  `δ≡0` recovers `SelfSimilarTower.div`. -/
  descent : ∀ k j,
    ((w k).approx j).eqv ((scaleN (b + 1) (w (k + 1))).approx j + δ k)
  /-- The uniform loss-sum bound `R`. -/
  R : Q'
  /-- **SUMMABILITY** (loss form): every partial defect sum is `≤ R`. -/
  summable : ∀ n, lossSum δ n ≤ R

/-- The separator flow `sep_k = e^{−w_k}` of a summable-descent tower. -/
def sepD {b : Nat} (T : SummableDescentTower b) (k : Nat) : CReal :=
  expNegCD (T.w k) (T.dw k)

/-- `δ_k ≤ 1` (from `δ_k ≤ ½ ≤ 1`). -/
theorem δ_le_one {b : Nat} (T : SummableDescentTower b) (k : Nat) : T.δ k ≤ 1 :=
  Q'.le_trans' _ _ _ (T.δ_le_half k) (by decide : HalfPow.half ≤ (1 : Q'))

/-- `0 ≤ 1 − δ_k` (the per-block multiplier `ρ_k = 1 − δ_k ≥ 0`). -/
theorem oneSub_nonneg {b : Nat} (T : SummableDescentTower b) (k : Nat) :
    (0 : Q') ≤ 1 - T.δ k := by
  show (0 : Q') ≤ 1 + (-(T.δ k))
  have hstep := Q'.add_le_add_right (T.δ k) 1 (-(T.δ k)) (δ_le_one T k)
  refine Q'.le_trans' _ _ _ ?_ hstep
  exact Q'.ge_of_eqv (Q'.add_neg_self_eqv (T.δ k))

/-- `1 − δ_k ≤ 1` (from `0 ≤ δ_k`). -/
theorem oneSub_le_one {b : Nat} (T : SummableDescentTower b) (k : Nat) :
    (1 : Q') - T.δ k ≤ 1 := by
  have hnn : (0 : Q') ≤ T.δ k := T.δ_nonneg k
  have hnegle : (-(T.δ k)) ≤ (0 : Q') := by
    have h : (0 : Q') + (-(T.δ k)) ≤ T.δ k + (-(T.δ k)) :=
      Q'.add_le_add_right 0 (T.δ k) (-(T.δ k)) hnn
    refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.add_neg_self_eqv (T.δ k))))
    exact Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (-(T.δ k))))
  show (1 : Q') + (-(T.δ k)) ≤ 1
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ 0 hnegle) ?_
  exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1))

/-! ## 2. The `δ≡0` embedding of `SelfSimilarTower` -/

/-- **`SelfSimilarTower b` embeds as the `δ≡0, R=0` summable-descent tower.**
The exact descent `T.div` supplies the approximate descent with zero defect, and
the loss-sum of the zero defect is `≤ 0`.  Nothing in the exact theory regresses:
`SelfSimilarTower` is precisely the `δ≡0` special case of `SummableDescentTower`. -/
def ofSelfSimilar {b : Nat} (T : SelfSimilarTower b) : SummableDescentTower b where
  w := T.w
  dw := T.dw
  bnd := T.bnd
  δ := fun _ => 0
  δ_nonneg := fun _ => Q'.le_refl' 0
  δ_le_half := fun _ => HalfPow.half_nonneg
  sumbnd := fun k j =>
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (QPoly.q_add_zero_eqv _)) (T.bnd k j)
  descent := fun k j =>
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (T.div k j))
      (Q'.eqv_symm (QPoly.q_add_zero_eqv _))
  R := 0
  summable := by
    intro n
    induction n with
    | zero => exact Q'.le_refl' 0
    | succ m ih =>
        show lossSum (fun _ => (0 : Q')) m + 0 ≤ 0
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (QPoly.q_add_zero_eqv _)) ih

/-- A non-vacuous inhabitant: the irrational `e^{−1}`-seeded hierarchical tower,
embedded as the `δ≡0` summable-descent tower. -/
def summableDescent_concreteE : SummableDescentTower 1 :=
  ofSelfSimilar (concreteTowerE 1)

/-! ## 3. (T1) The asymptotic (summable-defect) separator law -/

/-- The `e^{−δ_k}` defect factor of the asymptotic separator law. -/
def expDefect {b : Nat} (T : SummableDescentTower b) (k : Nat) : CReal :=
  expNegCD (CReal.ofQ' (T.δ k)) (ofQ'Data (T.δ k) (T.δ_nonneg k) (δ_le_one T k))

/-- **(T1) THE ASYMPTOTIC SEPARATOR LAW.**  For a `SummableDescentTower b`,

    sep_k ≃ (sep_{k+1})^(b+1) · e^{−δ_k}.

Proof (mirroring `descent_selfSimilarC_step`, keeping the `e^{−δ_k}` factor):
`sep_k = e^{−w_k} ≃ e^{−((b+1)w_{k+1}+δ_k)}` by the descent through
`expNegCD_pointwise_congr`; `= e^{−(b+1)w_{k+1}}·e^{−δ_k}` by `expNegCD_add`;
`= (sep_{k+1})^{b+1}·e^{−δ_k}` by `expNegCD_powerLaw`.  With `δ≡0` this collapses
to the exact law (`e^{−0} = 1`), so it strictly extends the `δ=0` case. -/
theorem descent_selfSimilarC_defect_step {b : Nat} (T : SummableDescentTower b) (k : Nat) :
    CReal.Equiv (sepD T k)
      (CReal.mul (cpow (sepD T (k + 1)) (b + 1)) (expDefect T k)) := by
  -- assembled modulus data.
  let dScale : ExpNegCData (scaleN (b + 1) (T.w (k + 1))) :=
    scaleData (T.w (k + 1)) (T.dw (k + 1)) (b + 1) (T.bnd k)
  let dδ : ExpNegCData (CReal.ofQ' (T.δ k)) :=
    ofQ'Data (T.δ k) (T.δ_nonneg k) (δ_le_one T k)
  let dSum : ExpNegCData (CReal.add (scaleN (b + 1) (T.w (k + 1))) (CReal.ofQ' (T.δ k))) :=
    addData (scaleN (b + 1) (T.w (k + 1))) (CReal.ofQ' (T.δ k)) dScale dδ
      (fun j => T.sumbnd k j)
  -- (a) sep_k ≃ e^{−((b+1)w_{k+1}+δ_k)}  (pointwise descent).
  have ha : CReal.Equiv (sepD T k)
      (expNegCD (CReal.add (scaleN (b + 1) (T.w (k + 1))) (CReal.ofQ' (T.δ k))) dSum) :=
    expNegCD_pointwise_congr (T.w k)
      (CReal.add (scaleN (b + 1) (T.w (k + 1))) (CReal.ofQ' (T.δ k)))
      (T.dw k) dSum (fun j => T.descent k j)
  -- (b) e^{−(A+B)} ≃ e^{−A}·e^{−B}  (add law, symmetrised).
  have hb : CReal.Equiv
      (expNegCD (CReal.add (scaleN (b + 1) (T.w (k + 1))) (CReal.ofQ' (T.δ k))) dSum)
      (CReal.mul (expNegCD (scaleN (b + 1) (T.w (k + 1))) dScale) (expDefect T k)) :=
    (expNegCD_add (scaleN (b + 1) (T.w (k + 1))) (CReal.ofQ' (T.δ k)) dScale dδ dSum).symm
  -- (c) e^{−(b+1)w_{k+1}} ≃ (sep_{k+1})^(b+1)  (power law, symmetrised).
  have hc : CReal.Equiv
      (expNegCD (scaleN (b + 1) (T.w (k + 1))) dScale)
      (cpow (sepD T (k + 1)) (b + 1)) :=
    (expNegCD_powerLaw (T.w (k + 1)) (T.dw (k + 1)) (b + 1) (T.bnd k)).symm
  -- (d) multiply (c) by the fixed e^{−δ_k} factor.
  have hd : CReal.Equiv
      (CReal.mul (expNegCD (scaleN (b + 1) (T.w (k + 1))) dScale) (expDefect T k))
      (CReal.mul (cpow (sepD T (k + 1)) (b + 1)) (expDefect T k)) :=
    mul_congr_left hc
  exact CReal.Equiv.trans ha (CReal.Equiv.trans hb hd)

/-! ## 4. (T2) The accumulated positive product floor -/

/-- `1 − (1 − δ_k) ≃ δ_k` lifts through the loss sum:
`∑_{k<n}(1 − (1 − δ_k)) ≃ ∑_{k<n} δ_k`. -/
theorem lossSum_oneSubOneSub_eqv {b : Nat} (T : SummableDescentTower b) :
    ∀ n, (lossSum (fun k => 1 - (1 - T.δ k)) n).eqv (lossSum T.δ n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
    show (lossSum (fun k => 1 - (1 - T.δ k)) n + (1 - (1 - T.δ n))).eqv
        (lossSum T.δ n + T.δ n)
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (1 - (1 - T.δ n)) (lossSum_oneSubOneSub_eqv T n))
      (Q'.add_eqv_congr_left _ _ _ (AFRateCalibration.one_sub_one_sub_eqv (T.δ n)))

/-- **(T2) THE ACCUMULATED POSITIVE PRODUCT FLOOR.**  For a `SummableDescentTower`,
the running product of the per-block multipliers `ρ_k = 1 − δ_k` has a strictly-
positive constructive-real floor `c = e^{−2R} > 0` (with a positive rational lower
bound `ε`) at every prefix `n`, in the exact `RGGapPersistence.prodPrefix` shape.

This is `ExpProductFloor.sum_loss_to_productFloor_exp` fed the tower's own defect:
`0 ≤ δ_k ≤ ½`, `1 − ρ_k = δ_k ≤ ½`, and `∑(1 − ρ_k) ≃ ∑ δ_k ≤ R` (`summable`). -/
def defect_product_floor {b : Nat} (T : SummableDescentTower b) :
    Σ' (c : CReal) (ε : Q'),
      (0 : Q') < ε ∧ ExpPos.geRat c ε
      ∧ ∀ n, CReal.leRat c (RGGapPersistence.prodPrefix (fun k => 1 - T.δ k) n) :=
  ExpProductFloor.sum_loss_to_productFloor_exp (fun k => 1 - T.δ k)
    (fun k => oneSub_nonneg T k)
    (fun k => oneSub_le_one T k)
    (fun k => Q'.le_trans' _ _ _
      (Q'.le_of_eqv (AFRateCalibration.one_sub_one_sub_eqv (T.δ k))) (T.δ_le_half k))
    T.R
    (fun n => Q'.le_trans' _ _ _
      (Q'.le_of_eqv (lossSum_oneSubOneSub_eqv T n)) (T.summable n))

/-! ### The rational-floor bridge -/

/-- **`geRat ∘ leRat ⇒ rational `≤`.**  If a constructive real `c` has a positive
rational lower bound `lo` (`geRat c lo`) and a rational upper bound `hi`
(`leRat c hi`), then `lo ≤ hi` as rationals.  From `lo ≤ c.approx n + 1/(N+1)`
and `c.approx n ≤ hi + 1/(N+1)` at a common index, `lo ≤ hi + 2·(1/(N+1))` for
every `N`; the Archimedean `Q'.le_of_le_add_residual` closes it. -/
theorem le_of_geRat_leRat {c : CReal} {lo hi : Q'}
    (hg : ExpPos.geRat c lo) (hl : CReal.leRat c hi) : lo ≤ hi := by
  refine Q'.le_of_le_add_residual lo hi 2 (fun N => Q'.invSucc N + Q'.invSucc N)
    (fun N => Q'.ge_of_eqv (ExpNeg.two_mul_eqv (Q'.invSucc N))) ?_
  intro N
  have hpos : (0 : Q') < Q'.invSucc N := Q'.invSucc_pos N
  obtain ⟨N1, hN1⟩ := hg (Q'.invSucc N) hpos
  obtain ⟨N2, hN2⟩ := hl (Q'.invSucc N) hpos
  have hge : lo ≤ c.approx (max N1 N2) + Q'.invSucc N :=
    hN1 (max N1 N2) (Nat.le_max_left _ _)
  have hle : c.approx (max N1 N2) ≤ hi + Q'.invSucc N :=
    hN2 (max N1 N2) (Nat.le_max_right _ _)
  refine Q'.le_trans' _ _ _ hge ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ (Q'.invSucc N) hle) ?_
  exact Q'.le_of_eqv (Q'.add_assoc_eqv hi (Q'.invSucc N) (Q'.invSucc N))

/-- **(T2, rational).**  The distilled positive RATIONAL product floor: a
strictly-positive `ε` with `ε ≤ ∏_{k<n}(1 − δ_k)` at every prefix `n`, extracted
from `defect_product_floor` via the `geRat/leRat` bridge.  This is the shape the
`Q'`-valued per-block persistence floor consumes. -/
def defect_product_floor_rat {b : Nat} (T : SummableDescentTower b) :
    Σ' (ε : Q'), (0 : Q') < ε
      ∧ ∀ n, ε ≤ RGGapPersistence.prodPrefix (fun k => 1 - T.δ k) n :=
  ⟨(defect_product_floor T).2.1,
   (defect_product_floor T).2.2.1,
   fun n => le_of_geRat_leRat (defect_product_floor T).2.2.2.1
     ((defect_product_floor T).2.2.2.2 n)⟩

/-- The distilled rational floor `ε` of a summable-descent tower. -/
def towerFloor {b : Nat} (T : SummableDescentTower b) : Q' :=
  (defect_product_floor_rat T).1

theorem towerFloor_pos {b : Nat} (T : SummableDescentTower b) :
    (0 : Q') < towerFloor T :=
  (defect_product_floor_rat T).2.1

theorem towerFloor_le {b : Nat} (T : SummableDescentTower b) (n : Nat) :
    towerFloor T ≤ RGGapPersistence.prodPrefix (fun k => 1 - T.δ k) n :=
  (defect_product_floor_rat T).2.2 n

/-! ## 5. The payoff — packaging into `RGBlockPersistence`, `recursion` isolated -/

open YMGap.Continuum.RegularContinuumPipeline

/-- **THE ASYMPTOTIC-DESCENT INPUT.**  A summable-descent tower together with the
physical spacing schedule, the fixed-spacing cluster bounds, a UV anchor, and the
SINGLE genuinely-open field `recursion` — the per-block margin recursion
`(1−δ_k)·physGap_k ≤ physGap_{k+1}`.  Its `rho := 1−δ` and product floor come
from the tower (T2), so `recursion` is the sole named residual: exactly the
`s=1`-scope spectral-localization (`hlocalize`/`hbound`) statement that the
exponent-level defect controls the true physical margin.  UNINHABITED on ℝ⁴. -/
structure AsymptoticDescentInput (b : Nat) : Type where
  /-- The summable-defect exponent descent tower (supplies `rho = 1−δ`, floor). -/
  T : SummableDescentTower b
  /-- The lattice spacings `a_j > 0`. -/
  spacing : Nat → Q'
  /-- Each spacing is strictly positive. -/
  spacing_pos : ∀ j, (0 : Q') < spacing j
  /-- The fixed-spacing infinite-volume cluster bounds. -/
  atSpacing : Nat → RegUniformClusterBound
  /-- A uniform physical ceiling. -/
  ceilConst : Q'
  /-- The physical gap is bounded above by the ceiling. -/
  physCeil : ∀ j,
    Q'.divPos ((atSpacing j).floorRate) (spacing j) (spacing_pos j) ≤ ceilConst
  /-- The UV anchor floor `g0 > 0`. -/
  anchor : Q'
  /-- The anchor is strictly positive. -/
  anchor_pos : (0 : Q') < anchor
  /-- **The anchor bound:** `g0 ≤ physGap_0`. -/
  anchor_le : anchor ≤
    Q'.divPos ((atSpacing 0).floorRate) (spacing 0) (spacing_pos 0)
  /-- **THE SOLE OPEN FIELD — the per-block margin recursion.**
  `(1−δ_k)·physGap_k ≤ physGap_{k+1}`: the exponent-level defect `δ_k` bounds the
  loss in the physical margin over spacing.  This is the `s=1`-scope spectral
  localization residual (`hlocalize`/`hbound`); UNINHABITED on ℝ⁴. -/
  recursion : ∀ k,
    (1 - T.δ k) * Q'.divPos ((atSpacing k).floorRate) (spacing k) (spacing_pos k)
      ≤ Q'.divPos ((atSpacing (k + 1)).floorRate) (spacing (k + 1)) (spacing_pos (k + 1))

/-- **THE PACKAGING.**  From an `AsymptoticDescentInput` build a
`RGGapPersistence.RGBlockPersistence` with `rho := 1−δ` and product floor
`prodFloor := towerFloor·anchor` (both from the tower, T2); the open `recursion`
is supplied verbatim.  This inhabits the per-block persistence shape WITHOUT the
exact `δ=0` descent. -/
def AsymptoticDescentInput.toBlockPersistence {b : Nat}
    (I : AsymptoticDescentInput b) : RGGapPersistence.RGBlockPersistence where
  spacing := I.spacing
  spacing_pos := I.spacing_pos
  atSpacing := I.atSpacing
  ceilConst := I.ceilConst
  physCeil := I.physCeil
  rho := fun k => 1 - I.T.δ k
  rho_nonneg := fun k => oneSub_nonneg I.T k
  anchor := I.anchor
  anchor_pos := I.anchor_pos
  anchor_le := I.anchor_le
  recursion := I.recursion
  prodFloor := towerFloor I.T * I.anchor
  prodFloor_pos := Q'.mul_pos (towerFloor_pos I.T) I.anchor_pos
  prodFloor_le := fun k =>
    Q'.mul_le_mul_of_nonneg_right (towerFloor I.T)
      (RGGapPersistence.prodPrefix (fun j => 1 - I.T.δ j) k) I.anchor
      (towerFloor_le I.T k) (Q'.le_of_lt I.anchor_pos)

/-- **THE UNIFORM PHYSICAL-GAP FLOOR (from a summable-`δ` input).**  The packaged
per-block data yields, via `blockPersistence_uniform_floor`, a single positive
floor below the physical gap `physGap_k = m_lat(a_k)/a_k` at EVERY scale `k` —
the spacing-uniform continuum floor, obtained WITHOUT exact `δ=0`. -/
theorem AsymptoticDescentInput.uniform_floor {b : Nat}
    (I : AsymptoticDescentInput b) (k : Nat) :
    I.toBlockPersistence.prodFloor ≤
      Q'.divPos ((I.atSpacing k).floorRate) (I.spacing k) (I.spacing_pos k) :=
  RGGapPersistence.blockPersistence_uniform_floor I.toBlockPersistence k

/-- The distilled uniform-form open inequality (per-block ⇒ uniform). -/
def AsymptoticDescentInput.toUniform {b : Nat}
    (I : AsymptoticDescentInput b) : RGGapPersistence.RGGapPersistence :=
  I.toBlockPersistence.toUniform

/-- **The continuum physical-gap floor is strictly positive.**  Composing the
packaging with the persistence reduction: a summable-`δ` input yields a strictly-
positive continuum physical-gap floor surviving `a → 0` (given the sole open
`recursion` field). -/
theorem AsymptoticDescentInput.continuum_floor_pos {b : Nat}
    (I : AsymptoticDescentInput b) :
    (0 : Q') < (RGGapPersistence.toScalingBand I.toUniform).physGapMin :=
  RGGapPersistence.physGapMin_pos_of_blockPersistence I.toBlockPersistence

end YMGap.Continuum.AFDeltaDecay

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AFDeltaDecay.sepD
#print axioms YMGap.Continuum.AFDeltaDecay.δ_le_one
#print axioms YMGap.Continuum.AFDeltaDecay.oneSub_nonneg
#print axioms YMGap.Continuum.AFDeltaDecay.oneSub_le_one
#print axioms YMGap.Continuum.AFDeltaDecay.ofSelfSimilar
#print axioms YMGap.Continuum.AFDeltaDecay.summableDescent_concreteE
#print axioms YMGap.Continuum.AFDeltaDecay.descent_selfSimilarC_defect_step
#print axioms YMGap.Continuum.AFDeltaDecay.lossSum_oneSubOneSub_eqv
#print axioms YMGap.Continuum.AFDeltaDecay.defect_product_floor
#print axioms YMGap.Continuum.AFDeltaDecay.le_of_geRat_leRat
#print axioms YMGap.Continuum.AFDeltaDecay.defect_product_floor_rat
#print axioms YMGap.Continuum.AFDeltaDecay.towerFloor_pos
#print axioms YMGap.Continuum.AFDeltaDecay.towerFloor_le
#print axioms YMGap.Continuum.AFDeltaDecay.AsymptoticDescentInput.toBlockPersistence
#print axioms YMGap.Continuum.AFDeltaDecay.AsymptoticDescentInput.uniform_floor
#print axioms YMGap.Continuum.AFDeltaDecay.AsymptoticDescentInput.toUniform
#print axioms YMGap.Continuum.AFDeltaDecay.AsymptoticDescentInput.continuum_floor_pos
