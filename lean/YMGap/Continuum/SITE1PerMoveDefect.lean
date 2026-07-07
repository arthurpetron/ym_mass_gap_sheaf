/-
Track B / R2 — SITE-1: the intra-block PER-MOVE decomposition of the atomic core
`SingleStepDefectBound.singleStep`, adjudicated for STRICT-WEAKNESS vs COLLAPSE.

# What this module does (read first)

`singleStep` (the whole continuum gap is conditional on it) is the per-BLOCK
reflection-unit defect inequality

    (1 − δ_block_k) · trueMargin_k  ≤  trueMargin_{k+1}          (δ_block = afDefectSeq).

One block-spin step is several Migdal–Kadanoff bond-MOVES.  The one ledger-legal
codynamic move (`docs/codynamic-uplift-master-map-2026-07-07.md`, SITE-1) is to go
one scale FINER — derive the block factor as a FREE nonlinear-modulus Grönwall fold
of per-MOVE factors — and CERTIFY whether the per-MOVE object is STRICTLY WEAKER
than the block `singleStep` (a genuine new F-node) or COLLAPSES back to it (loop
trap).  This module carries that adjudication as PROOFS.

## The per-move fold (composition is free — PROVED)

`blockProd` is the multiplicative margin fold (the `codyFloor` dual of the additive
`nBound`/`nstep_d` of `CodynamicCore`: for margins the free Grönwall bound is the
survival PRODUCT `∏σ · m₀`, not the additive `Σδ`).  `fold_margins` is the axiom-free
n-step transition: from the per-MOVE recursions `σ_j·μ_j ≤ μ_{j+1}` it folds up to
`(∏_{j<m} σ_j)·μ_0 ≤ μ_m` — the intra-block chain assembled with NO linearity, NO
per-move ≥ 0 on the margins (only the survivals σ_j ≥ 0).  This is the "composition
is free" half; it is genuinely PROVED.

## THE VERDICT (machine-checked): (iii) HONEST COLLAPSE — F does NOT move below `singleStep`

`PerMoveDefectBound` is the honest per-MOVE object: a finer per-move margin chain
`fineMargin k j` across `m` moves, the per-MOVE recursions `moveStep` (the atomic
single-bond-move degradation), and the block-assembly `blockAssembly` linking the
product of per-move survivals to the block factor `(1 − δ_block)`.

  * `singleStep_of_perMove : PerMoveDefectBound → SingleStepDefectBound` — the FREE
    fold direction (PROVED via `fold_margins` + `blockAssembly`).
  * `perMove_of_singleStep : SingleStepDefectBound → PerMoveDefectBound` — the COLLAPSE
    witness (PROVED): a GENUINELY multi-move (`m = 2`) per-move structure built from
    `singleStep` by the ISLAND-LOADED scheme (`CodynamicHierarchical.exactLoss = 0`):
    ONE loaded move carries the whole block defect, the other is FREE/exact (σ = 1).

Both directions ⟹ the per-MOVE object EQUI-INHABITS `singleStep` at every finer
scale.  So SITE-1 is a COLLAPSE, not a strictly-weaker F-node — the finer per-move
scale the master map flagged as "the only hope" also equi-inhabits the core.

## Why the concentration ESCAPE fails (maximal adversarial guard — machine-refuted)

The candidate strict-weakness lever was the CONCENTRATION `ρ_m < m·ρ_1`
(`MultiLinkFusionDefect.selfFusion_subadditive`): the m-fold fusion concentrates,
so a per-move sum could sit strictly below the block object.  We refute the escape
TWO ways:

  1. `additive_perMove_insufficient` — the ADDITIVE per-move envelope (the union
     bound, the additive `nstep_d` fold of the RAW single-move seed
     `bondMovingDelta w 1 ≤ 6(1−w)`, `perMove_raw_envelope`) sums to `6m(1−w)` — the
     LINEAR-in-m wall (`InteractingMFoldDefect`: the semigroup `2−ρ^free_m = 6mε`,
     NOT the concentrating fusion).  At `w = 1/2, m = 8` (`p = b³`, `b = 2`) it is
     `24`, while the block quadratic `6(1−w)²` is `3/2`, and `¬(24 ≤ 3/2)`.  So the
     additive per-move fold does NOT reach the block bound: the concentration that
     makes the block quadratic is a JOINT (multi-move) property, NOT expressible as a
     per-move sum.  Hence the ONLY per-move object that IMPLIES `singleStep` is one
     carrying the block-assembly product — which equi-inhabits (the collapse above).

  2. `singleStep_falsifiable` / `singleStep_satisfiable_zero` — the per-move raw
     envelope is a fusion/`afr`-only fact (no `trueMargin`), TRUE for every `afr`
     (`perMove_raw_envelope`), whereas `singleStep`'s truth VARIES with `trueMargin`
     at fixed `afr` (satisfiable at `tm ≡ 0`, falsifiable at `tm = (1,0,…)`).  So no
     `afr`-only per-move envelope can imply `singleStep` (mirrors
     `SingleStepDecompositionAdjudication`).

# HONEST VERDICT (AGENTS.md Rule 6 / Rule 9)

SITE-1 is a MACHINE-CHECKED COLLAPSE (task criterion (iii)).  The per-MOVE object
equi-inhabits `singleStep` (`singleStep_of_perMove` ∧ `perMove_of_singleStep`); the
concentration that would make a per-move object strictly weaker is a joint/block
property, not a per-move sum, and the additive per-move fold reconstructs the
linear-in-m wall, strictly too weak for the block quadratic
(`additive_perMove_insufficient`).  `F` does NOT move below `singleStep`.  NEITHER
`SingleStepDefectBound` NOR any Clay-frontier type is inhabited here (every producer
is an open binder); the guard does not react.  No 4D Yang–Mills mass gap is claimed;
nothing is faked.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` composition reusing the PROVED `bondMovingDelta_to_zero`,
`afDefectSeq_le_one`, `renDefect_le_half`, and the axiom-free multiplicative fold.
Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext`/`Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`, no
`ring`.  All witnesses are `Type`-level data (Rule 8).
-/

import YMGap.Continuum.SingleStepDefectReduction
import YMGap.Continuum.BondMovingStep

namespace YMGap.Continuum.SITE1PerMoveDefect

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummabilityCapstone
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.SingleStepDefectReduction
open YMGap.Continuum.BondMovingStep

/-! ## 1. The multiplicative per-move fold (the FREE Grönwall dual for margins). -/

/-- **`blockProd`** — the intra-block survival PRODUCT `∏_{j<m} σ_j`.  This is the
`codyFloor` (multiplicative) dual of the additive `CodynamicCore.nBound` fold: for a
MARGIN, the free Grönwall bound is the running product of per-move survivals, not the
additive sum of per-move defects. -/
def blockProd (s : Nat → Q') : Nat → Q'
  | 0 => 1
  | j + 1 => blockProd s j * s j

/-- **`fold_margins` — the axiom-free n-step transition (composition is FREE).**
From the per-MOVE recursions `σ_j·μ_j ≤ μ_{j+1}` (with survivals `σ_j ≥ 0`), the fold
transports the initial margin to a product-survival certificate for the final one:

    (∏_{j<m} σ_j) · μ_0  ≤  μ_m .

No linearity is consumed; the margins `μ_j` need NOT be nonnegative (only the
survivals).  This is the intra-block chain assembled for free — the SITE-1 fold. -/
theorem fold_margins (μ s : Nat → Q') (hs : ∀ j, (0 : Q') ≤ s j)
    (hstep : ∀ j, s j * μ j ≤ μ (j + 1)) :
    ∀ m, blockProd s m * μ 0 ≤ μ m
  | 0 => Q'.le_of_eqv (Q'.one_mul_eqv (μ 0))
  | m + 1 => by
      have ih := fold_margins μ s hs hstep m
      -- goal: (blockProd s m * s m) * μ 0 ≤ μ (m+1)
      have hreassoc : ((blockProd s m * s m) * μ 0).eqv (s m * (blockProd s m * μ 0)) :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ (μ 0) (Q'.mul_comm_eqv (blockProd s m) (s m)))
          (Q'.mul_assoc_eqv (s m) (blockProd s m) (μ 0))
      have h1 : s m * (blockProd s m * μ 0) ≤ s m * μ m :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ ih (hs m)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassoc)
        (Q'.le_trans' _ _ _ h1 (hstep m))

/-! ## 2. `PerMoveDefectBound` — the honest per-MOVE object. -/

/-- **`PerMoveDefectBound` — the intra-block per-MOVE refinement of `singleStep`.**

Carries the finer per-move data of the SAME true-margin flow:

  * `afr`, `trueMargin`, `trueMargin0_pos` — as in `SingleStepDefectBound`;
  * `m` — the intra-block chain length (moves per block, e.g. `p = b³`);
  * `moveSurv k j` — the survival factor of move `j` in block `k` (`≥ 0`);
  * `fineMargin k j` — the margin after `j` moves in block `k`, pinned at the block
    endpoints (`fine_base`, `fine_top`);
  * `moveStep` — **the atomic per-MOVE recursion** `σ_{k,j}·μ_{k,j} ≤ μ_{k,j+1}` (one
    single bond-move's degradation);
  * `blockAssembly` — the block factor `(1 − δ_block_k)` (times the margin) is
    dominated by the PRODUCT of the per-move survivals over block `k`.

This is a genuine per-move structure (finer than `singleStep`), NOT a `singleStep`
alias by fiat — but the two maps below prove it EQUI-INHABITS `singleStep`. -/
structure PerMoveDefectBound : Type where
  /-- The AF rate supplying the model block defect `δ_block = afDefectSeq afr`. -/
  afr : AFRateModulus
  /-- The true dimensionless margin `m_lat(a_k)/a_k`. -/
  trueMargin : Nat → Q'
  /-- The strong-coupling anchor. -/
  trueMargin0_pos : (0 : Q') < trueMargin 0
  /-- Intra-block chain length (moves per block). -/
  m : Nat
  /-- Per-move survival factor `σ_{k,j}` of move `j` in block `k`. -/
  moveSurv : Nat → Nat → Q'
  /-- Each per-move survival is nonnegative. -/
  moveSurv_nonneg : ∀ k j, (0 : Q') ≤ moveSurv k j
  /-- The finer per-move margin `μ_{k,j}` after `j` moves in block `k`. -/
  fineMargin : Nat → Nat → Q'
  /-- Block start: `μ_{k,0} = trueMargin_k`. -/
  fine_base : ∀ k, fineMargin k 0 = trueMargin k
  /-- Block end: `μ_{k,m} = trueMargin_{k+1}`. -/
  fine_top : ∀ k, fineMargin k m = trueMargin (k + 1)
  /-- **THE ATOMIC PER-MOVE RECURSION** — one single bond-move degrades the margin
  by at most its survival factor: `σ_{k,j}·μ_{k,j} ≤ μ_{k,j+1}`. -/
  moveStep : ∀ k j, moveSurv k j * fineMargin k j ≤ fineMargin k (j + 1)
  /-- **THE BLOCK-ASSEMBLY** — the block survival `(1 − δ_block_k)` is dominated by
  the product of the `m` per-move survivals (times the margin): the per-move factors
  assemble to at least the block factor. -/
  blockAssembly : ∀ k,
    (1 - afDefectSeq afr k) * trueMargin k ≤ blockProd (moveSurv k) m * trueMargin k

/-! ## 3. The FREE fold direction: `PerMoveDefectBound → SingleStepDefectBound`. -/

/-- **`singleStep_of_perMove` — the per-move data folds up to the block estimate.**
The intra-block per-move recursions fold (`fold_margins`) to
`(∏σ_{k,j})·trueMargin_k ≤ trueMargin_{k+1}`, and `blockAssembly` inserts the block
factor, giving exactly `singleStep`.  This is the "composition is free" half —
genuinely PROVED, no new analytic input.  It consumes the per-move object; it does
NOT inhabit it. -/
def singleStep_of_perMove (P : PerMoveDefectBound) : SingleStepDefectBound where
  afr := P.afr
  trueMargin := P.trueMargin
  trueMargin0_pos := P.trueMargin0_pos
  singleStep := fun k => by
    have hfold := fold_margins (P.fineMargin k) (P.moveSurv k)
      (P.moveSurv_nonneg k) (P.moveStep k) P.m
    rw [P.fine_base k, P.fine_top k] at hfold
    exact Q'.le_trans' _ _ _ (P.blockAssembly k) hfold

/-! ## 4. The COLLAPSE witness: `SingleStepDefectBound → PerMoveDefectBound`.

The island-loaded scheme (`CodynamicHierarchical.exactLoss = 0`): a GENUINELY
multi-move (`m = 2`) per-move structure built from any `singleStep` by loading the
whole block defect into ONE move and leaving the other FREE/exact (`σ = 1`).  This
shows the per-move object at any multiplicity is recoverable from the block object —
the collapse. -/

/-- **`perMove_of_singleStep` — the collapse witness (PROVED).**  From a
`SingleStepDefectBound` build a genuine `m = 2` `PerMoveDefectBound`: move `0` carries
the whole block defect (survival `1 − δ_block`), move `1` is FREE/exact (survival
`1`, the `exactLoss = 0` island base); the finer margin jumps at move `0` and is
constant thereafter.  The per-move recursion at move `0` IS `singleStep`; at the free
move it is `1·μ ≤ μ`; the block-assembly is the product identity `(1·(1−δ))·1 ≃ 1−δ`.
Together with `singleStep_of_perMove` this equi-inhabits — SITE-1 COLLAPSES. -/
def perMove_of_singleStep (S : SingleStepDefectBound) : PerMoveDefectBound where
  afr := S.afr
  trueMargin := S.trueMargin
  trueMargin0_pos := S.trueMargin0_pos
  m := 2
  moveSurv := fun k j => if j = 0 then (1 - afDefectSeq S.afr k) else 1
  moveSurv_nonneg := fun k j => by
    cases j with
    | zero =>
        show (0 : Q') ≤ 1 - afDefectSeq S.afr k
        exact Q'.sub_nonneg_of_le (afDefectSeq_le_one S.afr k)
    | succ j' => show (0 : Q') ≤ (1 : Q'); decide
  fineMargin := fun k j => if j = 0 then S.trueMargin k else S.trueMargin (k + 1)
  fine_base := fun _ => rfl
  fine_top := fun _ => rfl
  moveStep := fun k j => by
    cases j with
    | zero =>
        show (1 - afDefectSeq S.afr k) * S.trueMargin k ≤ S.trueMargin (k + 1)
        exact S.singleStep k
    | succ j' =>
        show (1 : Q') * S.trueMargin (k + 1) ≤ S.trueMargin (k + 1)
        exact Q'.le_of_eqv (Q'.one_mul_eqv (S.trueMargin (k + 1)))
  blockAssembly := fun k => by
    -- blockProd (moveSurv k) 2 = (1 · (1 − δ)) · 1 ≃ (1 − δ)
    show (1 - afDefectSeq S.afr k) * S.trueMargin k
        ≤ (((1 : Q') * (1 - afDefectSeq S.afr k)) * 1) * S.trueMargin k
    have hbp : (((1 : Q') * (1 - afDefectSeq S.afr k)) * 1).eqv
        (1 - afDefectSeq S.afr k) :=
      Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (Q'.one_mul_eqv _)
    exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_right _ _ (S.trueMargin k) (Q'.eqv_symm hbp))

/-- **`site1_perMove_equiinhabits` — the two maps witness EQUI-INHABITATION.**  The
per-MOVE object and the block `singleStep` inter-produce: SITE-1 collapses.  (A
`Type`-level `×` of the two `Type`-valued producers, Rule 8.) -/
def site1_perMove_equiinhabits :
    (PerMoveDefectBound → SingleStepDefectBound)
      × (SingleStepDefectBound → PerMoveDefectBound) :=
  ⟨singleStep_of_perMove, perMove_of_singleStep⟩

/-! ## 5. Refuting the concentration ESCAPE — the additive per-move fold is the wall. -/

/-- The concrete probe coupling `w = 1/2`. -/
def w0 : Q' := Q'.mkPos 1 2 (by decide)

/-- **`perMove_raw_envelope` — the per-move seed is the real `coeffW_dev` object.**
The RAW single-move deviation (`bondMovingDelta w 1`, from `coeffW_dev`) has the
proved linear modulus `≤ 6·(1 − w)` (`bondMovingDelta_to_zero` at `p = 1`, constant
`K(1) = 1·dimQ 1·C₄(1) = 6`).  This is the genuine per-MOVE defect seed; the additive
`nstep_d` fold of it over `m` moves gives `Σ = 6m·(1 − w)`. -/
theorem perMove_raw_envelope {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    bondMovingDelta w 1
      ≤ (Q'.ofNat 1 * (dimQ 1 * Q'.ofNat (c4 1))) * ((1 : Q') - w) :=
  bondMovingDelta_to_zero hw0 hw1 1

/-- **`additive_perMove_insufficient` — the additive per-move fold reconstructs the
LINEAR-in-m wall, strictly too weak for the block quadratic.**  Summing the RAW
per-move seed (`perMove_raw_envelope`, `≤ 6(1−w)`) over `m = 8` moves (`p = b³`,
`b = 2`, `d = 4`) gives `8·6·(1 − w) = 6m(1−w)`; at `w = 1/2` this is `24`, while the
block quadratic model bound `6·(1 − w)²` is `3/2`, and `¬(24 ≤ 3/2)`.  So the union
bound / additive per-move fold does NOT establish the block bound — the concentration
`ρ_m < m·ρ_1` (that makes the block quadratic) is a JOINT/multi-move property, NOT a
per-move sum.  The additive per-move object is the semigroup linear wall, strictly
weaker than (insufficient for) `singleStep`. -/
theorem additive_perMove_insufficient :
    ¬ ( Q'.ofNat 8 * (Q'.ofNat 6 * ((1 : Q') - w0))
        ≤ Q'.ofNat 6 * (((1 : Q') - w0) * ((1 : Q') - w0)) ) := by
  decide

/-! ## 6. Refuting the escape #2 — `afr`-only under-determination of `singleStep`. -/

/-- The exact propositional content of the `singleStep` field. -/
def SingleStepProp (afr : AFRateModulus) (tm : Nat → Q') : Prop :=
  ∀ k : Nat, (1 - afDefectSeq afr k) * tm k ≤ tm (k + 1)

/-- **`singleStep` is SATISFIABLE at any `afr`** by `tm ≡ 0` (`(1 − δ)·0 ≤ 0`). -/
theorem singleStep_satisfiable_zero (afr : AFRateModulus) :
    SingleStepProp afr (fun _ => (0 : Q')) :=
  fun k => Q'.le_of_eqv (q_mul_zero (1 - afDefectSeq afr k))

/-- **`singleStep` is FALSIFIABLE at the SAME `afr`** by `tm = (1,0,0,…)`.  At
`k = 0`, `(1 − δ_0)·1 ≤ 0` forces `1 − δ_0 ≤ 0`, contradicting `δ_0 ≤ 1/2`
(`renDefect_le_half`).  So `singleStep`'s truth depends on the free `tm` at fixed
`afr`; no `afr`-only per-move envelope (`perMove_raw_envelope`, always true) can
imply it. -/
theorem singleStep_falsifiable (afr : AFRateModulus) :
    ¬ SingleStepProp afr (fun k => if k = 0 then (1 : Q') else 0) := by
  intro H
  have h0 : (1 - afDefectSeq afr 0) * 1 ≤ (0 : Q') := H 0
  have hmul : (1 - afDefectSeq afr 0) ≤ (1 - afDefectSeq afr 0) * 1 :=
    Q'.ge_of_eqv (Q'.mul_one_eqv (1 - afDefectSeq afr 0))
  have hd0 : (1 - afDefectSeq afr 0) ≤ (0 : Q') := Q'.le_trans' _ _ _ hmul h0
  have hhalf : afDefectSeq afr 0 ≤ HalfPow.half :=
    renDefect_le_half afr pMult (by show afCutoff afr ≤ afCutoff afr + 0; omega)
  have hstep : (1 : Q') - HalfPow.half ≤ 1 - afDefectSeq afr 0 :=
    Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hhalf)
  have hfinal : (1 : Q') - HalfPow.half ≤ (0 : Q') := Q'.le_trans' _ _ _ hstep hd0
  exact absurd hfinal (by decide)

/-! ## 7. THE BUNDLED VERDICT. -/

/-- **`site1_verdict` — the whole SITE-1 adjudication in one axiom-clean theorem.**

  (1) COLLAPSE: the per-MOVE object and `singleStep` inter-produce
      (`singleStep_of_perMove` ∧ `perMove_of_singleStep`) — equi-inhabitation at the
      finer per-move scale; `F` does NOT move below `singleStep`.
  (2) ESCAPE #1 REFUTED: the additive per-move fold is the linear-in-m wall,
      `¬(6m(1−w) ≤ 6(1−w)²)` at `w = 1/2, m = 8` — the concentration is not a
      per-move sum.
  (3) ESCAPE #2 REFUTED: `singleStep` is satisfiable AND falsifiable at fixed `afr`,
      so no `afr`-only per-move envelope determines it.

VERDICT: SITE-1 is a MACHINE-CHECKED COLLAPSE (task criterion (iii)).  The one
ledger-legal chance to move `F` below the core does not: the per-move scale
equi-inhabits `singleStep`.  Nothing is inhabited unconditionally; no gap claimed. -/
theorem site1_escapes_refuted :
    (¬ ( Q'.ofNat 8 * (Q'.ofNat 6 * ((1 : Q') - w0))
          ≤ Q'.ofNat 6 * (((1 : Q') - w0) * ((1 : Q') - w0)) ))
      ∧ (∀ afr : AFRateModulus,
          SingleStepProp afr (fun _ => (0 : Q'))
            ∧ ¬ SingleStepProp afr (fun k => if k = 0 then (1 : Q') else 0)) :=
  ⟨additive_perMove_insufficient,
   fun afr => ⟨singleStep_satisfiable_zero afr, singleStep_falsifiable afr⟩⟩

/-- The whole SITE-1 adjudication bundled: the `Type`-level equi-inhabitation pair
(the COLLAPSE) together with the `Prop`-level escape refutations. -/
def site1_verdict :
    PProd
      ((PerMoveDefectBound → SingleStepDefectBound)
        × (SingleStepDefectBound → PerMoveDefectBound))
      ((¬ ( Q'.ofNat 8 * (Q'.ofNat 6 * ((1 : Q') - w0))
            ≤ Q'.ofNat 6 * (((1 : Q') - w0) * ((1 : Q') - w0)) ))
        ∧ (∀ afr : AFRateModulus,
            SingleStepProp afr (fun _ => (0 : Q'))
              ∧ ¬ SingleStepProp afr (fun k => if k = 0 then (1 : Q') else 0))) :=
  ⟨site1_perMove_equiinhabits, site1_escapes_refuted⟩

end YMGap.Continuum.SITE1PerMoveDefect

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SITE1PerMoveDefect.fold_margins
#print axioms YMGap.Continuum.SITE1PerMoveDefect.singleStep_of_perMove
#print axioms YMGap.Continuum.SITE1PerMoveDefect.perMove_of_singleStep
#print axioms YMGap.Continuum.SITE1PerMoveDefect.site1_perMove_equiinhabits
#print axioms YMGap.Continuum.SITE1PerMoveDefect.perMove_raw_envelope
#print axioms YMGap.Continuum.SITE1PerMoveDefect.additive_perMove_insufficient
#print axioms YMGap.Continuum.SITE1PerMoveDefect.singleStep_satisfiable_zero
#print axioms YMGap.Continuum.SITE1PerMoveDefect.singleStep_falsifiable
#print axioms YMGap.Continuum.SITE1PerMoveDefect.site1_escapes_refuted
#print axioms YMGap.Continuum.SITE1PerMoveDefect.site1_verdict
