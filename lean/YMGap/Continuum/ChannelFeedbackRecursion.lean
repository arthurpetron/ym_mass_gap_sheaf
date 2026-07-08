/-
Track B / R2 — RE-BASING the single-step defect reduction onto the LOOSE model
`6(1 − w)²`, for which the MAGNITUDE piece is SATISFIABLE, cleanly isolating the
true-margin RECURSION (channel feedback) as the sole residual.

# What this module does (read first)

`SingleStepDefectReduction.SingleStepDefectBound` compares the real per-step RG
defect against the TIGHT model `afDefectSeq afr k = renDefect afr 1 (afCutoff afr + k)`
(= `δ_free`).  `RealDefectConstruction.honest_realDefect_exceeds_tight` shows the
honest interacting defect `realδ = δ_free + Cdef` (with `Cdef ≥ 0`) OVERSHOOTS
`δ_free`, so the TIGHT structure's magnitude field is UNSATISFIABLE for the genuine
defect.

This module re-bases onto the LOOSE model `modelExpr w = 6(1 − w)²`, which carries the
cubic slack `2(1 − w)³` to absorb `Cdef`.  We prove:

  * `model_le_two_renDefect` / `renDefect_le_model` — the two-sided comparison of the
    loose model `6(1 − w)²` with the renormalized transverse defect `δ_free`
    (`2(1 − w)²(2 + w)`), both from the exact factorization `renDefect_factor`.
  * `renDefect_le_quarter` — the loose-tail per-step `1/4` cutoff (mirrors
    `renDefect_le_half` at `1/4`), hence `model_le_half` on the loose tail.
  * `looseFloorData` / `looseFloorEps_le_prod` — the STRICTLY POSITIVE product floor
    `∏(1 − 6(1 − w_k)²) > 0` on the loose tail (summable `O(1/k²)`), mirroring
    `SummabilityCapstone.renormalized_gap_of_AFRate`.
  * `SingleStepDefectBoundLoose` — the re-based residual structure (UNINHABITED; its
    `recursion` field stays open), with builder `defectRecursion_of_looseBound` into
    `DefectGapRecursion` and hence the whole continuum floor `fullFloor_of_looseBound`.
  * `looseMagnitude_satisfiable` — the KEY CONTRAST: the loose magnitude field IS
    inhabited concretely by the interacting `m = 1` construction
    `realDefectRen w (cdef1 w)` (unlike the tight model).
  * `MarginRecursion` on the SURROGATE regime CONSTRUCTED (`looseRecursion_on_surrogate`);
    the precise `s ≥ 2 → s = 1` object PINNED as `SurrogateDomination` with the genuine
    reduction `looseRecursion_of_surrogateDomination`; and the adversarial
    `perScale_not_recursion_reexport` (the per-scale bound does NOT imply the recursion).

# HONEST VERDICT (AGENTS.md Rule 6 / Rule 9)

The magnitude piece is now SATISFIABLE on the loose model (proved), so the ONLY open
content of the re-based single-step reduction is the true-margin RECURSION (the
`recursion` field of `SingleStepDefectBoundLoose`, or equivalently a
`SurrogateDomination`).  NO `SingleStepDefectBoundLoose` is inhabited (its `recursion`
field is left open); NO guarded Clay-frontier type is inhabited; the 4D Yang–Mills mass
gap remains OPEN.  Nothing is faked.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`/`CReal` composition reusing PROVED `renDefect_factor`,
`dfree_add_slack_eqv_model`, `renDefect_invSq`, `renDefect_summable`,
`sum_loss_to_productFloor_exp`, `fullFloor_of_defectRecursion`.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext`/`Quot.sound`
only.  No `Classical.*`, no `native_decide`, no `sorry`, no `ring`.  All witnesses are
`Type`-level data (Rule 8).
-/

import YMGap.Continuum.RealDefectConstruction
import YMGap.Continuum.SingleStepDefectReduction
import YMGap.Continuum.LargeFieldSuppression

namespace YMGap.Continuum.ChannelFeedbackRecursion

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.RenDefectQuadFactor
open YMGap.Continuum.SubdominanceWindow
open YMGap.Continuum.ConnectedSlackBound
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.ProductFloor
open YMGap.Continuum.RGGapPersistence
open YMGap.Continuum.SummabilityCapstone
open YMGap.Continuum.ExpProductFloor
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.ContinuumClosureProgram
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.SingleStepDefectReduction

/-! ## 0. Elementary `Q'` nonnegativity facts on the loose model. -/

/-- `0 ≤ modelExpr w = 6·(1 − w)²` unconditionally (`(1 − w)² ≥ 0`). -/
theorem modelExpr_nonneg (w : Q') : (0 : Q') ≤ modelExpr w := by
  show (0 : Q') ≤ Q'.ofNat 6 * oneSubWSq w
  exact Q'.mul_nonneg _ _ (by decide)
    (SumOfSquares.q_mul_self_nonneg ((1 : Q') - w))

/-- `0 ≤ slackExpr w = 2·(1 − w)²·(1 − w)` for `w ≤ 1`. -/
theorem slackExpr_nonneg {w : Q'} (hw1 : w ≤ (1 : Q')) : (0 : Q') ≤ slackExpr w := by
  show (0 : Q') ≤ Q'.ofNat 2 * (oneSubWSq w * ((1 : Q') - w))
  refine Q'.mul_nonneg _ _ (by decide) ?_
  refine Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg ((1 : Q') - w)) ?_
  show (0 : Q') ≤ (1 : Q') + (-w)
  have h : w + (-w) ≤ (1 : Q') + (-w) := Q'.add_le_add_right w 1 (-w) hw1
  refine Q'.le_trans' _ _ _ ?_ h
  exact Q'.ge_of_eqv (Q'.add_neg_self_eqv w)

/-- `1 − w ≤ 2 + w` for `0 ≤ w`. -/
theorem one_sub_le_two_add {w : Q'} (hw0 : (0 : Q') ≤ w) :
    (1 : Q') - w ≤ Q'.ofNat 2 + w := by
  have hnegw : (-w) ≤ (0 : Q') := by
    have h : (0 : Q') + (-w) ≤ w + (-w) := Q'.add_le_add_right 0 w (-w) hw0
    refine Q'.le_trans' _ _ _ ?_
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.add_neg_self_eqv w)))
    exact Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (-w)))
  have h1 : (1 : Q') - w ≤ 1 := by
    show (1 : Q') + (-w) ≤ 1
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 (-w) 0 hnegw) ?_
    exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1))
  have h2 : (1 : Q') ≤ Q'.ofNat 2 + w := by
    have h2a : (Q'.ofNat 2 : Q') + 0 ≤ Q'.ofNat 2 + w :=
      Q'.add_le_add_left (Q'.ofNat 2) 0 w hw0
    have h2b : (1 : Q') ≤ Q'.ofNat 2 + 0 := by
      refine Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ Q'.ofNat 2) ?_
      exact Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.add_zero' (Q'.ofNat 2)))
    exact Q'.le_trans' _ _ _ h2b h2a
  exact Q'.le_trans' _ _ _ h1 h2

/-! ## 1. The two-sided comparison of `modelExpr` and the renormalized defect.

`renDefect afr 1 k = bondMovingDeltaRen 1 1 (w_k) ≃ dfreeExpr w = 2(1 − w)²(2 + w)`
(`RealDefectConstruction.bondMovingDeltaRen_one_eqv_dfree`).  The loose model
`modelExpr w = 6(1 − w)²` satisfies both `modelExpr ≤ 2·renDefect` (the majorant used
for summability) and `renDefect ≤ modelExpr` (the per-step bound feeding the recursion
reduction). -/

/-- **`model_le_two_renDefect` — `6(1 − w)² ≤ 2·δ_free`.**  `modelExpr = δ_free + slack`
(`dfree_add_slack_eqv_model`) and `slack ≤ δ_free` (since `1 − w ≤ 2 + w`), so
`modelExpr ≤ δ_free + δ_free ≃ 2·renDefect`.  The `O(1/k²)`-summable majorant. -/
theorem model_le_two_renDefect (afr : AFRateModulus) (k : Nat) :
    modelExpr (afr.w k) ≤ Q'.ofNat 2 * renDefect afr 1 k := by
  have hw0 : (0 : Q') ≤ afr.w k := afr.w_nonneg k
  have hslack_le : slackExpr (afr.w k) ≤ dfreeExpr (afr.w k) := by
    show Q'.ofNat 2 * (oneSubWSq (afr.w k) * ((1 : Q') - afr.w k))
        ≤ Q'.ofNat 2 * (oneSubWSq (afr.w k) * (Q'.ofNat 2 + afr.w k))
    refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ (by decide)
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ (one_sub_le_two_add hw0)
      (SumOfSquares.q_mul_self_nonneg ((1 : Q') - afr.w k))
  have hmodel_le : modelExpr (afr.w k) ≤ dfreeExpr (afr.w k) + dfreeExpr (afr.w k) := by
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (dfree_add_slack_eqv_model (afr.w k))) ?_
    exact Q'.add_le_add_left (dfreeExpr (afr.w k)) _ _ hslack_le
  have he : (renDefect afr 1 k).eqv (dfreeExpr (afr.w k)) :=
    RealDefectConstruction.bondMovingDeltaRen_one_eqv_dfree (afr.w k)
  have htwo : (dfreeExpr (afr.w k) + dfreeExpr (afr.w k)).eqv
      (Q'.ofNat 2 * renDefect afr 1 k) := by
    refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (ExpNeg.two_mul_eqv (renDefect afr 1 k)))
    exact Q'.add_eqv_congr' (Q'.eqv_symm he) (Q'.eqv_symm he)
  exact Q'.le_trans' _ _ _ hmodel_le (Q'.le_of_eqv htwo)

/-- **`renDefect_le_model` — `δ_free ≤ 6(1 − w)²`.**  `δ_free = realDefectRen w 0`
(`Cdef = 0`), so `dfree_le_realDefect` + `realDefectRen_le_model` (`0 ≤ slackExpr`)
give the per-step bound `renDefect afr 1 j ≤ modelExpr (w_j)` at every index `j`. -/
theorem renDefect_le_model (afr : AFRateModulus) (j : Nat) :
    renDefect afr 1 j ≤ modelExpr (afr.w j) := by
  have hw1 : afr.w j ≤ (1 : Q') := Q'.le_of_lt (afr.w_lt_one j)
  have he : (renDefect afr 1 j).eqv (dfreeExpr (afr.w j)) :=
    RealDefectConstruction.bondMovingDeltaRen_one_eqv_dfree (afr.w j)
  have hmid : dfreeExpr (afr.w j) ≤ RealDefectConstruction.realDefectRen (afr.w j) 0 :=
    RealDefectConstruction.dfree_le_realDefect (Q'.le_refl' 0)
  have hend : RealDefectConstruction.realDefectRen (afr.w j) 0 ≤ modelExpr (afr.w j) :=
    RealDefectConstruction.realDefectRen_le_model (slackExpr_nonneg hw1)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) (Q'.le_trans' _ _ _ hmid hend)

/-! ## 2. The loose per-step `1/4` cutoff and the `1/2` model bound on the tail. -/

/-- The loose head-cutoff `looseCutoff afr = 4·Aconst.num.toNat`: for `k ≥ looseCutoff`,
`renDefect afr 1 k ≤ 1/4` (twice as strict as `defectCutoff`'s `1/2`, giving the loose
model `≤ 1/2` via the factor-2 majorant). -/
def looseCutoff (afr : AFRateModulus) : Nat := 4 * (Aconst afr 1).num.toNat

/-- **`renDefect_le_quarter`** — for `k ≥ looseCutoff afr`, `renDefect afr 1 k ≤ 1/4`.
Mirrors `renDefect_le_half` with the cross-product `A.num·4 ≤ A.den·(k+2)` from
`k ≥ 4·A.num.toNat`. -/
theorem renDefect_le_quarter (afr : AFRateModulus) {k : Nat}
    (hk : looseCutoff afr ≤ k) :
    renDefect afr 1 k ≤ Q'.mkPos 1 4 (by decide) := by
  have hAnn : (0 : Q') ≤ Aconst afr 1 := Aconst_nonneg afr 1
  have hAnum : 0 ≤ (Aconst afr 1).num := (Q'.zero_le_iff_num_nonneg _).mp hAnn
  have h1 : renDefect afr 1 k ≤ Aconst afr 1 * invSqTerm 2 (by decide) k :=
    renDefect_invSq afr 1 k
  have hk2 : 0 < k + 2 := by omega
  have hk2sq : 0 < (k + 2) * (k + 2) := Nat.mul_pos hk2 hk2
  have hanti : unit ((k + 2) * (k + 2)) hk2sq ≤ unit (k + 2) hk2 := by
    refine unit_antitone hk2 hk2sq ?_
    calc k + 2 = (k + 2) * 1 := by omega
      _ ≤ (k + 2) * (k + 2) := Nat.mul_le_mul_left (k + 2) (by omega)
  have h2 : Aconst afr 1 * invSqTerm 2 (by decide) k
      ≤ Aconst afr 1 * unit (k + 2) hk2 := by
    show Aconst afr 1 * unit ((k + 2) * (k + 2)) _ ≤ Aconst afr 1 * unit (k + 2) hk2
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hanti hAnn
  have h3 : Aconst afr 1 * unit (k + 2) hk2 ≤ Q'.mkPos 1 4 (by decide) := by
    show (Aconst afr 1 * unit (k + 2) hk2).num * ((Q'.mkPos 1 4 (by decide)).den : Int)
        ≤ (Q'.mkPos 1 4 (by decide)).num * ((Aconst afr 1 * unit (k + 2) hk2).den : Int)
    have hhn : (Q'.mkPos 1 4 (by decide)).num = 1 := rfl
    have hhd : ((Q'.mkPos 1 4 (by decide)).den : Int) = 4 := rfl
    rw [hhn, hhd, Int.one_mul]
    have hLn : (Aconst afr 1 * unit (k + 2) hk2).num = (Aconst afr 1).num := by
      show (Aconst afr 1).num * (unit (k + 2) hk2).num = (Aconst afr 1).num
      rw [unit_num, Int.mul_one]
    have hLd : ((Aconst afr 1 * unit (k + 2) hk2).den : Int)
        = ((Aconst afr 1).den : Int) * ((k + 2 : Nat) : Int) := by
      rw [Q'.mul_den_cast, unit_den]
    rw [hLn, hLd]
    have htoNat : ((Aconst afr 1).num.toNat : Int) = (Aconst afr 1).num :=
      Int.toNat_of_nonneg hAnum
    have hkge : 4 * (Aconst afr 1).num.toNat ≤ k := hk
    have hden1 : (1 : Int) ≤ ((Aconst afr 1).den : Int) := by
      have := (Aconst afr 1).den_pos; exact_mod_cast this
    have hstepA : (Aconst afr 1).num * 4 ≤ ((k + 2 : Nat) : Int) := by
      have hc : (4 * (Aconst afr 1).num.toNat : Nat) ≤ k + 2 := by omega
      have hc' : ((4 * (Aconst afr 1).num.toNat : Nat) : Int) ≤ ((k + 2 : Nat) : Int) := by
        exact_mod_cast hc
      have heq : ((4 * (Aconst afr 1).num.toNat : Nat) : Int) = (Aconst afr 1).num * 4 := by
        push_cast [htoNat]; omega
      rw [heq] at hc'; exact hc'
    have hkpos : (0 : Int) ≤ ((k + 2 : Nat) : Int) := by exact_mod_cast Nat.zero_le _
    have hstepB : ((k + 2 : Nat) : Int)
        ≤ ((Aconst afr 1).den : Int) * ((k + 2 : Nat) : Int) := by
      have := Int.mul_le_mul_of_nonneg_right hden1 hkpos
      rwa [Int.one_mul] at this
    exact Int.le_trans hstepA hstepB
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 h3)

/-- **`model_le_half`** — for `k ≥ looseCutoff afr`, `modelExpr (w_k) ≤ 1/2`.  From
`modelExpr ≤ 2·renDefect ≤ 2·(1/4) = 1/2`. -/
theorem model_le_half (afr : AFRateModulus) {k : Nat} (hk : looseCutoff afr ≤ k) :
    modelExpr (afr.w k) ≤ HalfPow.half := by
  have h1 : modelExpr (afr.w k) ≤ Q'.ofNat 2 * renDefect afr 1 k :=
    model_le_two_renDefect afr k
  have h2 : renDefect afr 1 k ≤ Q'.mkPos 1 4 (by decide) := renDefect_le_quarter afr hk
  have h3 : Q'.ofNat 2 * renDefect afr 1 k ≤ Q'.ofNat 2 * Q'.mkPos 1 4 (by decide) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h2 (by decide)
  have h4 : Q'.ofNat 2 * Q'.mkPos 1 4 (by decide) ≤ HalfPow.half := by decide
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h3 h4)

/-! ## 3. Loose summability and the strictly-positive loose product floor. -/

/-- `lossSum (2·g) n ≃ 2·lossSum g n` (linearity of the finite sum). -/
theorem lossSum_two_mul (g : Nat → Q') :
    ∀ n, (lossSum (fun j => Q'.ofNat 2 * g j) n).eqv (Q'.ofNat 2 * lossSum g n)
  | 0 => Q'.eqv_symm (q_mul_zero (Q'.ofNat 2))
  | n + 1 => by
    show (lossSum (fun j => Q'.ofNat 2 * g j) n + Q'.ofNat 2 * g n).eqv
        (Q'.ofNat 2 * (lossSum g n + g n))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (Q'.ofNat 2 * g n) (lossSum_two_mul g n)) ?_
    exact Q'.eqv_symm (Q'.mul_add_eqv (Q'.ofNat 2) (lossSum g n) (g n))

/-- **`loose_lossSum_le`** — the loose model is `O(1/k²)`-summable on the tail:
`Σ_{j<n} 6(1 − w_{looseCutoff+j})² ≤ 2·Aconst·pot 2 looseCutoff`. -/
theorem loose_lossSum_le (afr : AFRateModulus) (n : Nat) :
    lossSum (fun j => modelExpr (afr.w (looseCutoff afr + j))) n
      ≤ Q'.ofNat 2 * (Aconst afr 1 * pot 2 (by decide) (looseCutoff afr)) := by
  have hterm : lossSum (fun j => modelExpr (afr.w (looseCutoff afr + j))) n
      ≤ lossSum (fun j => Q'.ofNat 2 * renDefect afr 1 (looseCutoff afr + j)) n :=
    LargeFieldSuppression.lossSum_le_termwise
      (fun k => model_le_two_renDefect afr (looseCutoff afr + k)) n
  have heqv : (lossSum (fun j => Q'.ofNat 2 * renDefect afr 1 (looseCutoff afr + j)) n).eqv
      (Q'.ofNat 2 * lossSum (fun j => renDefect afr 1 (looseCutoff afr + j)) n) :=
    lossSum_two_mul (fun j => renDefect afr 1 (looseCutoff afr + j)) n
  have hshift : lossSum (fun j => renDefect afr 1 (looseCutoff afr + j)) n
      = tailSum (renDefect afr 1) (looseCutoff afr) n :=
    lossSum_shift_eq afr 1 (looseCutoff afr) n
  have hsum : tailSum (renDefect afr 1) (looseCutoff afr) n
      ≤ Aconst afr 1 * pot 2 (by decide) (looseCutoff afr) :=
    renDefect_summable afr 1 (looseCutoff afr) n
  refine Q'.le_trans' _ _ _ hterm ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv) ?_
  rw [hshift]
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hsum (by decide)

/-- `lossSum (1 − (1 − modelExpr)) n ≃ lossSum modelExpr n` (termwise `1 − (1 − x) ≃ x`). -/
theorem lossSum_oneSub_model_eqv (afr : AFRateModulus) :
    ∀ n, (lossSum (fun j => 1 - ((1 : Q') - modelExpr (afr.w (looseCutoff afr + j)))) n).eqv
      (lossSum (fun j => modelExpr (afr.w (looseCutoff afr + j))) n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
    show (lossSum (fun j => 1 - ((1 : Q') - modelExpr (afr.w (looseCutoff afr + j)))) n
            + (1 - ((1 : Q') - modelExpr (afr.w (looseCutoff afr + n))))).eqv
        (lossSum (fun j => modelExpr (afr.w (looseCutoff afr + j))) n
            + modelExpr (afr.w (looseCutoff afr + n)))
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (1 - ((1 : Q') - modelExpr (afr.w (looseCutoff afr + n))))
        (lossSum_oneSub_model_eqv afr n))
      (Q'.add_eqv_congr_left _ _ _
        (one_sub_one_sub_eqv (modelExpr (afr.w (looseCutoff afr + n)))))

/-- The loose per-tail survival product `∏_{j<k}(1 − 6(1 − w_{looseCutoff+j})²)`. -/
def looseSurvival (afr : AFRateModulus) (k : Nat) : Q' :=
  prodPrefix (fun j => 1 - modelExpr (afr.w (looseCutoff afr + j))) k

/-- **`looseFloorData`** — the STRICTLY POSITIVE exponential product floor on the loose
tail survival product, mirroring `renormalized_gap_of_AFRate` (loose model `≤ 1/2` on
the tail, `O(1/k²)`-summable). -/
noncomputable def looseFloorData (afr : AFRateModulus) :
    Σ' (c : CReal) (ε : Q'),
      (0 : Q') < ε ∧ ExpPos.geRat c ε
      ∧ ∀ n, CReal.leRat c
          (prodPrefix (fun j => 1 - modelExpr (afr.w (looseCutoff afr + j))) n) := by
  have hρ0 : ∀ j, (0 : Q') ≤ (1 : Q') - modelExpr (afr.w (looseCutoff afr + j)) := by
    intro j
    show (0 : Q') ≤ (1 : Q') + (-(modelExpr (afr.w (looseCutoff afr + j))))
    have hmle : modelExpr (afr.w (looseCutoff afr + j)) ≤ HalfPow.half :=
      model_le_half afr (Nat.le_add_right (looseCutoff afr) j)
    have hmle1 : modelExpr (afr.w (looseCutoff afr + j)) ≤ 1 :=
      Q'.le_trans' _ _ _ hmle (by decide)
    have h := Q'.add_le_add_right (modelExpr (afr.w (looseCutoff afr + j))) 1
      (-(modelExpr (afr.w (looseCutoff afr + j)))) hmle1
    refine Q'.le_trans' _ _ _ ?_ h
    exact Q'.ge_of_eqv (Q'.add_neg_self_eqv (modelExpr (afr.w (looseCutoff afr + j))))
  have hρ1 : ∀ j, (1 : Q') - modelExpr (afr.w (looseCutoff afr + j)) ≤ 1 := by
    intro j
    have hnn : (0 : Q') ≤ modelExpr (afr.w (looseCutoff afr + j)) := modelExpr_nonneg _
    have hnegle : (-(modelExpr (afr.w (looseCutoff afr + j)))) ≤ (0 : Q') := by
      have h : (0 : Q') + (-(modelExpr (afr.w (looseCutoff afr + j))))
          ≤ modelExpr (afr.w (looseCutoff afr + j))
              + (-(modelExpr (afr.w (looseCutoff afr + j)))) :=
        Q'.add_le_add_right 0 (modelExpr (afr.w (looseCutoff afr + j)))
          (-(modelExpr (afr.w (looseCutoff afr + j)))) hnn
      refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.add_neg_self_eqv (modelExpr (afr.w (looseCutoff afr + j))))))
      exact Q'.ge_of_eqv (Q'.eqv_of_eq
        (Q'.zero_add' (-(modelExpr (afr.w (looseCutoff afr + j))))))
    show (1 : Q') + (-(modelExpr (afr.w (looseCutoff afr + j)))) ≤ 1
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ 0 hnegle) ?_
    exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1))
  have hρhalf : ∀ j, (1 - ((1 : Q') - modelExpr (afr.w (looseCutoff afr + j))))
      ≤ HalfPow.half := by
    intro j
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv
      (one_sub_one_sub_eqv (modelExpr (afr.w (looseCutoff afr + j))))) ?_
    exact model_le_half afr (Nat.le_add_right (looseCutoff afr) j)
  have hR : ∀ n, lossSum
      (fun k => 1 - ((1 : Q') - modelExpr (afr.w (looseCutoff afr + k)))) n
        ≤ Q'.ofNat 2 * (Aconst afr 1 * pot 2 (by decide) (looseCutoff afr)) := by
    intro n
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (lossSum_oneSub_model_eqv afr n)) ?_
    exact loose_lossSum_le afr n
  exact sum_loss_to_productFloor_exp
    (fun j => 1 - modelExpr (afr.w (looseCutoff afr + j))) hρ0 hρ1 hρhalf
    (Q'.ofNat 2 * (Aconst afr 1 * pot 2 (by decide) (looseCutoff afr))) hR

/-- The positive rational floor witness `ε > 0` of the loose product floor. -/
noncomputable def looseFloorEps (afr : AFRateModulus) : Q' := (looseFloorData afr).2.1

/-- `0 < looseFloorEps afr`. -/
theorem looseFloorEps_pos (afr : AFRateModulus) : (0 : Q') < looseFloorEps afr :=
  (looseFloorData afr).2.2.1

/-- **`looseFloorEps_le_prod`** — the `Q'`-level loose product floor:
`looseFloorEps afr ≤ ∏_{j<k}(1 − 6(1 − w_{looseCutoff+j})²)` for every `k`.  Bridges the
capstone's `geRat`/`leRat` via `le_of_geRat_leRat` (mirrors
`afFloorEps_le_afPhysGapSeq`). -/
theorem looseFloorEps_le_prod (afr : AFRateModulus) (k : Nat) :
    looseFloorEps afr
      ≤ prodPrefix (fun j => 1 - modelExpr (afr.w (looseCutoff afr + j))) k := by
  have hge : ExpPos.geRat (looseFloorData afr).1 (looseFloorEps afr) :=
    (looseFloorData afr).2.2.2.1
  have hle : CReal.leRat (looseFloorData afr).1
      (prodPrefix (fun j => 1 - modelExpr (afr.w (looseCutoff afr + j))) k) :=
    (looseFloorData afr).2.2.2.2 k
  exact DominantModeRecursion.le_of_geRat_leRat hge hle

/-! ## 4. The re-based residual structure (UNINHABITED) and its builder. -/

/-- **`SingleStepDefectBoundLoose` — the LOOSE-model re-based single-step residual
(`Type`, Rule 8; UNINHABITED).**  Carries the true margin, its positive anchor, the
loose MAGNITUDE bound `realδ_k ≤ 6(1 − w_{looseCutoff+k})²` (SATISFIABLE — see
`looseMagnitude_satisfiable`), and the SOLE OPEN residual: the true-margin `recursion`
`(1 − realδ_k)·tm_k ≤ tm_{k+1}` (channel feedback).  No full inhabitant is constructed
here; the `recursion` field stays open. -/
structure SingleStepDefectBoundLoose : Type where
  /-- The AF rate supplying the loose model weights `w_{looseCutoff+k}`. -/
  afr : AFRateModulus
  /-- The genuine interacting per-step real defect. -/
  realδ : Nat → Q'
  /-- The genuine dimensionless physical margin. -/
  trueMargin : Nat → Q'
  /-- The true margin is nonnegative at every scale. -/
  trueMargin_nonneg : ∀ k, (0 : Q') ≤ trueMargin k
  /-- The strong-coupling anchor: the scale-0 true margin is strictly positive. -/
  trueMargin0_pos : (0 : Q') < trueMargin 0
  /-- **THE LOOSE MAGNITUDE BOUND (SATISFIABLE).**  The real defect is bounded by the
  loose model `6(1 − w)²` (which carries the cubic slack to absorb `Cdef`). -/
  magnitude : ∀ k, realδ k ≤ modelExpr (afr.w (looseCutoff afr + k))
  /-- **THE SOLE OPEN RESIDUAL — the true-margin recursion (channel feedback).** -/
  recursion : ∀ k, (1 - realδ k) * trueMargin k ≤ trueMargin (k + 1)

/-- **`defectRecursion_of_looseBound` — the builder.**  A `SingleStepDefectBoundLoose`
inhabits a full `DefectGapRecursion` whose `physGap` IS the true margin, `defect` is the
loose model (nonneg / `≤ 1` proved), `recursion` follows from `magnitude` + the open
`recursion` field, and `prodFloor = looseFloorEps · trueMargin 0 > 0` from the loose
product floor. -/
noncomputable def defectRecursion_of_looseBound (S : SingleStepDefectBoundLoose) :
    DefectGapRecursion where
  physGap := S.trueMargin
  physGap0_pos := S.trueMargin0_pos
  defect := fun k => modelExpr (S.afr.w (looseCutoff S.afr + k))
  defect_nonneg := fun _ => modelExpr_nonneg _
  defect_le_one := fun k =>
    Q'.le_trans' _ _ _
      (model_le_half S.afr (Nat.le_add_right (looseCutoff S.afr) k)) (by decide)
  recursion := by
    intro k
    show (1 - modelExpr (S.afr.w (looseCutoff S.afr + k))) * S.trueMargin k
        ≤ S.trueMargin (k + 1)
    have hmag : S.realδ k ≤ modelExpr (S.afr.w (looseCutoff S.afr + k)) := S.magnitude k
    have hone : (1 - modelExpr (S.afr.w (looseCutoff S.afr + k))) ≤ (1 - S.realδ k) := by
      show (1 : Q') + (-(modelExpr (S.afr.w (looseCutoff S.afr + k))))
          ≤ (1 : Q') + (-(S.realδ k))
      exact Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hmag)
    have hstep : (1 - modelExpr (S.afr.w (looseCutoff S.afr + k))) * S.trueMargin k
        ≤ (1 - S.realδ k) * S.trueMargin k :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hone (S.trueMargin_nonneg k)
    exact Q'.le_trans' _ _ _ hstep (S.recursion k)
  prodFloor := looseFloorEps S.afr * S.trueMargin 0
  prodFloor_pos := Q'.mul_pos (looseFloorEps_pos S.afr) S.trueMargin0_pos
  prodFloor_le := by
    intro k
    show looseFloorEps S.afr * S.trueMargin 0
        ≤ prodPrefix (fun i => 1 - modelExpr (S.afr.w (looseCutoff S.afr + i))) k
            * S.trueMargin 0
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (looseFloorEps_le_prod S.afr k) (Q'.le_of_lt S.trueMargin0_pos)

/-- **`fullFloor_of_looseBound`** — the whole positive continuum floor for the true
margin from a `SingleStepDefectBoundLoose`: `0 < prodFloor` and `prodFloor ≤ trueMargin k`
at every scale.  Rests only on the single open `recursion` field. -/
theorem fullFloor_of_looseBound (S : SingleStepDefectBoundLoose) :
    (0 : Q') < (defectRecursion_of_looseBound S).prodFloor
      ∧ ∀ k, (defectRecursion_of_looseBound S).prodFloor ≤ S.trueMargin k :=
  CrossoverDefectUnification.fullFloor_of_defectRecursion
    (defectRecursion_of_looseBound S)

/-! ## 5. MAGNITUDE SATISFIABLE — the key contrast with the tight model. -/

/-- **`looseMagnitude_satisfiable` — the loose magnitude field IS inhabited.**  The
interacting `m = 1` construction `realDefectRen w (cdef1 w)` (from
`RealDefectConstruction`) satisfies the loose model bound `≤ 6(1 − w)²` at every scale
(`realDefect_m1_closed`, uniform in `w ≤ 1`).  Unlike the TIGHT model — which
`RealDefectConstruction.honest_realDefect_exceeds_tight` shows is unsatisfiable once
`Cdef > 0` — the loose magnitude piece is concretely realized. -/
def looseMagnitude_satisfiable (afr : AFRateModulus) :
    Σ' realδ : Nat → Q', ∀ k, realδ k ≤ modelExpr (afr.w (looseCutoff afr + k)) :=
  ⟨fun k => RealDefectConstruction.realDefectRen (afr.w (looseCutoff afr + k))
      (cdef1 (afr.w (looseCutoff afr + k))),
   fun k => RealDefectConstruction.realDefect_m1_closed
      (Q'.le_of_lt (afr.w_lt_one (looseCutoff afr + k)))⟩

/-! ## 6. THE RECURSION — construct on the surrogate regime + pin the s≥2→s=1 object. -/

/-- **`MarginRecursion realδ tm`** — the true-margin recursion `(1 − realδ_k)·tm_k ≤
tm_{k+1}` (the channel-feedback content). -/
def MarginRecursion (realδ tm : Nat → Q') : Prop :=
  ∀ k : Nat, (1 - realδ k) * tm k ≤ tm (k + 1)

/-- **`looseRecursion_on_surrogate` — the loose recursion CONSTRUCTED on the survival
product.**  Taking `tm := looseSurvival afr` (the RG-transported loose survival product),
the loose recursion holds as an EQUALITY: `prodPrefix` succ is
`looseSurvival_k · (1 − modelExpr_k)`, so `(1 − modelExpr_k)·looseSurvival_k ≤
looseSurvival_{k+1}` by `mul_comm`. -/
theorem looseRecursion_on_surrogate (afr : AFRateModulus) :
    MarginRecursion (fun k => modelExpr (afr.w (looseCutoff afr + k)))
      (looseSurvival afr) := by
  intro k
  show (1 - modelExpr (afr.w (looseCutoff afr + k))) * looseSurvival afr k
      ≤ looseSurvival afr (k + 1)
  exact Q'.le_of_eqv
    (Q'.mul_comm_eqv (1 - modelExpr (afr.w (looseCutoff afr + k))) (looseSurvival afr k))

/-- **`SurrogateDomination afr tm`** — the precise `s ≥ 2 → s = 1` object: the true
margin `tm` is dominated per step by the RG transfer survival factor `(1 − δ_free_k)`
at the SAME physical index `looseCutoff + k`. -/
def SurrogateDomination (afr : AFRateModulus) (tm : Nat → Q') : Prop :=
  ∀ k : Nat, (1 - renDefect afr 1 (looseCutoff afr + k)) * tm k ≤ tm (k + 1)

/-- **`looseRecursion_of_surrogateDomination` — the GENUINE REDUCTION.**  Since
`renDefect ≤ modelExpr` (`renDefect_le_model`), `1 − modelExpr_k ≤ 1 − renDefect_k`, so a
`SurrogateDomination` (dominance by the transfer factor `1 − δ_free`) yields the loose
`MarginRecursion` for any nonnegative `tm`.  The channel-feedback residual is thus
exactly a `SurrogateDomination`. -/
theorem looseRecursion_of_surrogateDomination (afr : AFRateModulus) (tm : Nat → Q')
    (hnn : ∀ k, (0 : Q') ≤ tm k) (H : SurrogateDomination afr tm) :
    MarginRecursion (fun k => modelExpr (afr.w (looseCutoff afr + k))) tm := by
  intro k
  show (1 - modelExpr (afr.w (looseCutoff afr + k))) * tm k ≤ tm (k + 1)
  have hrm : renDefect afr 1 (looseCutoff afr + k)
      ≤ modelExpr (afr.w (looseCutoff afr + k)) :=
    renDefect_le_model afr (looseCutoff afr + k)
  have hone : (1 - modelExpr (afr.w (looseCutoff afr + k)))
      ≤ (1 - renDefect afr 1 (looseCutoff afr + k)) := by
    show (1 : Q') + (-(modelExpr (afr.w (looseCutoff afr + k))))
        ≤ (1 : Q') + (-(renDefect afr 1 (looseCutoff afr + k)))
    exact Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hrm)
  have hstep : (1 - modelExpr (afr.w (looseCutoff afr + k))) * tm k
      ≤ (1 - renDefect afr 1 (looseCutoff afr + k)) * tm k :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hone (hnn k)
  exact Q'.le_trans' _ _ _ hstep (H k)

/-- **`perScale_not_recursion_reexport` — the per-scale magnitude bound does NOT imply
the recursion.**  Re-export of `RealDefectConstruction.perScale_not_recursion`: there is
data with the loose per-scale bound `∀k, realδ_k ≤ 6(1 − w_k)²` HOLDING yet the
`MarginRecursion` FAILING.  Channel feedback carries strictly more content than any
per-scale defect bound. -/
theorem perScale_not_recursion_reexport :
    ∃ (w realδ tm : Nat → Q'),
      (∀ k, realδ k ≤ modelExpr (w k)) ∧ ¬ MarginRecursion realδ tm := by
  obtain ⟨w, realδ, tm, hpb, hnr⟩ := RealDefectConstruction.perScale_not_recursion
  exact ⟨w, realδ, tm, hpb, hnr⟩

/-! ## 7. The `Type`-level verdict bundle — inhabits NO frontier type. -/

/-- **`ChannelFeedbackVerdict`** — the machine-checked state of the loose-model re-basing:
the loose magnitude field is SATISFIABLE (data), the loose recursion is CONSTRUCTED on
the survival regime, the reduction `SurrogateDomination → recursion` is PROVED, and the
per-scale-does-not-imply-recursion refutation holds.  Inhabits NO guarded Clay-frontier
type; produces NO `SingleStepDefectBoundLoose`. -/
structure ChannelFeedbackVerdict : Type where
  /-- The loose magnitude field is inhabited by the interacting `m = 1` construction. -/
  magnitude_sat : ∀ afr : AFRateModulus,
    Σ' realδ : Nat → Q', ∀ k, realδ k ≤ modelExpr (afr.w (looseCutoff afr + k))
  /-- The loose recursion is CONSTRUCTED on the RG survival regime. -/
  surrogate_recursion : ∀ afr : AFRateModulus,
    MarginRecursion (fun k => modelExpr (afr.w (looseCutoff afr + k))) (looseSurvival afr)
  /-- The genuine reduction: transfer-factor dominance ⟹ the loose recursion. -/
  reduction : ∀ (afr : AFRateModulus) (tm : Nat → Q'),
    (∀ k, (0 : Q') ≤ tm k) → SurrogateDomination afr tm →
      MarginRecursion (fun k => modelExpr (afr.w (looseCutoff afr + k))) tm
  /-- The per-scale bound does NOT supply the recursion (channel feedback binds). -/
  feedback_refutation : ∃ (w realδ tm : Nat → Q'),
    (∀ k, realδ k ≤ modelExpr (w k)) ∧ ¬ MarginRecursion realδ tm

/-- **`channelFeedback_verdict` — non-vacuous inhabitant; every field a PROVED
result.**  No frontier bundle inhabited; no `SingleStepDefectBoundLoose` produced (its
`recursion` field stays open). -/
def channelFeedback_verdict : ChannelFeedbackVerdict where
  magnitude_sat := looseMagnitude_satisfiable
  surrogate_recursion := looseRecursion_on_surrogate
  reduction := looseRecursion_of_surrogateDomination
  feedback_refutation := perScale_not_recursion_reexport

end YMGap.Continuum.ChannelFeedbackRecursion

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChannelFeedbackRecursion.modelExpr_nonneg
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.slackExpr_nonneg
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.one_sub_le_two_add
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.model_le_two_renDefect
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.renDefect_le_model
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.renDefect_le_quarter
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.model_le_half
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.lossSum_two_mul
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.loose_lossSum_le
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.lossSum_oneSub_model_eqv
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.looseFloorData
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.looseFloorEps_pos
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.looseFloorEps_le_prod
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.defectRecursion_of_looseBound
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.fullFloor_of_looseBound
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.looseMagnitude_satisfiable
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.looseRecursion_on_surrogate
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.looseRecursion_of_surrogateDomination
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.perScale_not_recursion_reexport
#print axioms YMGap.Continuum.ChannelFeedbackRecursion.channelFeedback_verdict
