/-
# Wilson-carrier dynamic vacuum-sector family, decay, and B04-shaped band (X1 PLUMBING)

Companion to `audits/SCOPE-WILSON-CARRIER-GAP-RETARGET-2026-10-06.md` (§X1). ADDITIVE.
No cube-side file is touched.

THIS IS PLUMBING ONLY. It makes NO progress on:
* X2, the lower margin `m·2^-j ≤ 1 − r_j`;
* the nontriviality input (H-var, H-ray, and the lag-k step ratio of 9d58a5df).
Both stay OPEN.

Contents:
* `WilsonDynamicFamily`. A Wilson mirror of the cube `DynamicVacuumSectorCompletedFamily`
  (`BF4PhysicalDynamicVacuumSectorCompletedFamily.lean:53`): nome, spacing, and a per-scale
  rate.
  * Its contraction slot is the ALL-VECTOR squared-norm contraction
    `WilsonVacuumSqContraction` on the all-nome literal-width Wilson completion of width
    `width j`.
  * The cube slot `…StrictContractionData` is replaced field-for-field: `rate`,
    `rate_nonnegative`, `rate_lt_one`, `contraction`.
* `latticeMargin`, `physicalGap`, `latticeMargin_pos`: as on the cube.
* `WilsonDynamicFamily.completedAutocorrelation_sq_decay`. The cube's shape
  (`…CylinderCompletedGap.lean:245`), re-proved on Wilson:
  `B(y,Tⁿy)·B(y,Tⁿy) ≤ ((r·r)ⁿ·B(y,y))·B(y,y)` for every `y` in the vacuum complement.
  Proof: `iterated_of_vacuumSq` (the generic-rate analogue of
  `completed_iterated_norm_gap`), then Cauchy–Schwarz.
* `exprWilsonFamily tr r …`. The family on the Expr trajectory `tr`, with the same schedule,
  the same widths, and spacing `2^-j`. `exprMixRateFamily tr` is the UNCONDITIONAL instance
  with `r_j = mixRate(w_j, width_j)`.
* `WilsonLowerMargin F m` (X2, OPEN), `WilsonUpperMargin F M`, and
  `WilsonPhysicalRateBand F := ∃ m M, lower ∧ upper`. The last is the B04 band as a Prop.
* `wilsonUpper_of_stepRatio`. The UPPER half on `exprWilsonFamily tr r`, from the
  step-ratio input alone via the cf08f0df compatibility. It does not use X2.
* `wilsonGapBranch_of_stepRatio_lowerMargin` and `…_mixRate`: the capstone.
  * Open analytic hypotheses:
    * H-var `Hv`, H-ray `Hr`, and the step ratio (`H`, `hc`, `hrho'0`, `hrho'1`). These form
      the nontriviality bundle of 9d58a5df.
    * X2 `WilsonLowerMargin (exprMixRateFamily tr) m`.
  * All other hypotheses are arithmetic parameter choices: `ha hC hcC hj0 hj0' hdelta0
    hdelta hcd hk`.
  * Conclusions: A03 (`ExprShiftedAnchorPackage`), the Wilson B04 band, decay at every scale
    and every vacuum-complement vector, and the necessary consistency `m ≤ 2^(2C+3)`.

HONEST SCOPE.
* DEAD END (2026-10-06 PT): at `mixRate` on any trajectory with `j + j ≤ width_j`, e.g.
  `trAF`, X2 is FALSE for every `m`. See `not_wilsonLowerMargin_mixRate_of_width` in
  `BF4WilsonAllNomeWilsonMixRateDeadEnd`. So `wilsonGapBranch_mixRate` is vacuous there. The
  generic capstone with some other rate family is the live route.
* On the GAP side, X2 is the single open analytic input. The upper half and the
  contraction are discharged.
* The capstone still carries the nontriviality bundle (H-var, H-ray, step ratio). That bundle
  is needed for A03 and for the upper half, so it is NOT gap-side, and it stays OPEN.
* The rate `mixRate = 1 − kineticFloor/kineticCap` is a Doeblin ratio. X2 at this rate is not
  expected to hold. A sharper Wilson rate producer may be needed: any `exprWilsonFamily tr r`
  works with the generic capstone.
* X3 TODO (J02-level, NOT done):
  * a Wilson `ObservablePin` that maps gauge-invariant local observables into this
    `VacuumComplement`;
  * re-pointing the OS/GNS handoffs: the selected Wilson GNS datum is uninhabited and is not
    identified with this `Completion`;
  * the AF/physical-time calibration of `2^-j`.

Constructive, no external library; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction

namespace YMGap.Continuum.BF4WilsonAllNomeWilsonDynamicFamily

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4DyadicWilsonSquare (side spacing spacing_positive)
open YMGap.Continuum.PhysicalSeparatorLogRate (PhysicalSpacing)
open YMGap.Continuum.PhysicalSeparatorLinearTail (SpacingToZero)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion completedInner completedInner_symm completedInner_nonnegative
   completedInner_cauchySchwarz unitState)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedTime_zero VacuumComplement)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixRate mixRate_nonnegative mixRate_lt_one)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory
  (dyadicPhysicalSpacing dyadicSpacingToZero)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory
open YMGap.Continuum.BF4WilsonAllNomeExprShiftedAnchorPackage (ExprShiftedAnchorPackage)
open YMGap.Continuum.BF4WilsonAllNomeExprStepRatioWindowSurvival (ExprStepRatio)
open YMGap.Continuum.BF4WilsonAllNomeExprWindowGapCompatibility (ExprPathOrbitContraction)
open YMGap.Continuum.BF4WilsonAllNomeExprStepRatioAnyC
  (expr_normalized_anchor_of_hvar_hray_stepRatio_anyC expr_stepRatio_forces_rate_anyC)
open YMGap.Continuum.BF4WilsonAllNomeExprTwoSidedBand
  (ExprCenteredContractionLower lower_side_form upper_spacing_form small_scale_upper)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction
  (WilsonVacuumSqContraction wilsonVacuumSqContraction_mixRate orbitContraction_of_vacuumSq)

/-! ## 0. Helpers -/

private theorem wf_ofNat_le {a b : Nat} (h : a ≤ b) : Q'.ofNat a ≤ Q'.ofNat b := by
  change (a : Int)*1 ≤ (b : Int)*1
  simp only [Int.mul_one]
  omega

private theorem wf_ofNat_pos (n : Nat) (hn : 0 < n) : (0 : Q') < Q'.ofNat n := by
  change (0 : Int)*1 < (n : Int)*1
  simp only [Int.mul_one]
  omega

private theorem wf_RCmul_mono_right {left right factor : RC}
    (hle : RCle left right) (hfactor : RCnonneg factor) :
    RCle (RCmul left factor) (RCmul right factor) := by
  rw [RCmul_comm left factor, RCmul_comm right factor]
  revert hfactor hle
  refine Quotient.inductionOn₃ factor left right ?_
  intro F L R hLR hF
  exact CReal.leEv_mul_nonneg_left hF hLR

/-! ## 1. Generic-rate iteration and squared autocorrelation decay on one Wilson carrier -/

section Carrier

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- Generic-rate analogue of `completed_iterated_norm_gap`:
`B(Tⁿx,Tⁿx) ≤ (r·r)ⁿ·B(x,x)` for `x ⊥ U`. -/
theorem iterated_of_vacuumSq (r : Q') (hr : (0 : Q') ≤ r)
    (H : WilsonVacuumSqContraction hw0 hw1 width r) (n : Nat) (x : V)
    (hx : B (unitState hw0 hw1 width) x = RCzero) :
    RCle (B (T n x) (T n x)) (RCscale ((r*r)^n) (B x x)) := by
  induction n with
  | zero =>
      rw [completedTime_zero, Q'.pow_zero, RCscale_one]
      exact RCle_refl _
  | succ k ih =>
      have hstep := orbitContraction_of_vacuumSq hw0 hw1 width r H x hx k
      refine RCle_trans hstep ?_
      have hscaled := RCscale_mono (Q'.mul_nonneg r r hr hr) ih
      refine RCle_trans hscaled ?_
      rw [RCscale_RCscale, Q'.pow_succ]
      exact RCle_refl _

/-- **Squared autocorrelation decay**, in the cube's shape (`…CylinderCompletedGap:245`),
on the Wilson vacuum complement. -/
theorem autocorrelation_sq_decay_of_vacuumSq (r : Q') (hr : (0 : Q') ≤ r)
    (H : WilsonVacuumSqContraction hw0 hw1 width r) (n : Nat)
    (y : VacuumComplement hw0 hw1 (width := width)) :
    RCle (RCmul (B y.val (T n y.val)) (B y.val (T n y.val)))
      (RCmul (RCscale ((r*r)^n) (B y.val y.val)) (B y.val y.val)) := by
  have hcs := completedInner_cauchySchwarz hw0 hw1 (T n y.val) y.val
  rw [completedInner_symm hw0 hw1 (T n y.val) y.val] at hcs
  have hnorm := iterated_of_vacuumSq hw0 hw1 width r hr H n y.val y.property
  exact RCle_trans hcs (wf_RCmul_mono_right hnorm (completedInner_nonnegative hw0 hw1 y.val))

end Carrier

/-! ## 2. The Wilson dynamic family (mirror of `DynamicVacuumSectorCompletedFamily`) -/

/-- Scale-indexed Wilson completed transfers with an ALL-VECTOR squared-norm contraction
at rate `rate j < 1` on the width-`width j` all-nome completion. -/
structure WilsonDynamicFamily : Type where
  nome : Nat → Q'
  nome_pos : ∀ j, (0 : Q') < nome j
  nome_lt_one : ∀ j, nome j < (1 : Q')
  width : Nat → Nat
  transferSpacing : PhysicalSpacing
  transferSpacingToZero : SpacingToZero transferSpacing
  rate : Nat → Q'
  rate_nonnegative : ∀ j, (0 : Q') ≤ rate j
  rate_lt_one : ∀ j, rate j < (1 : Q')
  contraction : ∀ j, WilsonVacuumSqContraction (nome_pos j) (nome_lt_one j) (width j) (rate j)

namespace WilsonDynamicFamily

variable (F : WilsonDynamicFamily)

/-- Dimensionless lattice margin `1 − rate_j`. -/
def latticeMargin (j : Nat) : Q' := (1 : Q') - F.rate j

/-- Rational physical gap `(1 − rate_j)/a_j`. -/
def physicalGap (j : Nat) : Q' :=
  Q'.divPos (F.latticeMargin j) (F.transferSpacing.spacing j) (F.transferSpacing.spacing_pos j)

theorem latticeMargin_pos (j : Nat) : (0 : Q') < F.latticeMargin j :=
  one_sub_pos_of_lt_one (F.rate_lt_one j)

/-- **Squared autocorrelation decay** at every scale and every vacuum-complement vector. -/
theorem completedAutocorrelation_sq_decay (j n : Nat)
    (y : VacuumComplement (F.nome_pos j) (F.nome_lt_one j) (width := F.width j)) :
    RCle
      (RCmul (completedInner (F.nome_pos j) (F.nome_lt_one j) y.val
          (completedTime (F.nome_pos j) (F.nome_lt_one j) n y.val))
        (completedInner (F.nome_pos j) (F.nome_lt_one j) y.val
          (completedTime (F.nome_pos j) (F.nome_lt_one j) n y.val)))
      (RCmul (RCscale ((F.rate j * F.rate j)^n)
          (completedInner (F.nome_pos j) (F.nome_lt_one j) y.val y.val))
        (completedInner (F.nome_pos j) (F.nome_lt_one j) y.val y.val)) :=
  autocorrelation_sq_decay_of_vacuumSq (F.nome_pos j) (F.nome_lt_one j) (F.width j) (F.rate j)
    (F.rate_nonnegative j) (F.contraction j) n y

end WilsonDynamicFamily

/-! ## 3. The Wilson B04 band as a Prop, split into halves -/

/-- **X2 (OPEN): the lower margin**, `0 < m` and `m·a_j ≤ 1 − rate_j`. The mass-gap content. -/
def WilsonLowerMargin (F : WilsonDynamicFamily) (m : Q') : Prop :=
  (0 : Q') < m ∧ ∀ j, m * F.transferSpacing.spacing j ≤ F.latticeMargin j

/-- Upper margin `1 − rate_j ≤ M·a_j`, `0 < M`. -/
def WilsonUpperMargin (F : WilsonDynamicFamily) (M : Q') : Prop :=
  (0 : Q') < M ∧ ∀ j, F.latticeMargin j ≤ M * F.transferSpacing.spacing j

/-- **Wilson B04 band** (Prop): field-for-field `DynamicVacuumSectorPhysicalRateBand`
with existentially quantified floor/ceiling. -/
def WilsonPhysicalRateBand (F : WilsonDynamicFamily) : Prop :=
  ∃ m M : Q', WilsonLowerMargin F m ∧ WilsonUpperMargin F M

/-! ## 4. The family on the Expr trajectory; the unconditional `mixRate` instance -/

/-- Wilson family on the SAME schedule and widths as `tr`, spacing `2^-j`. -/
def exprWilsonFamily (tr : ExprAnchorTrajectory) (r : Nat → Q')
    (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j < (1 : Q'))
    (Hc : ∀ j, WilsonVacuumSqContraction (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (tr.width j) (r j)) : WilsonDynamicFamily where
  nome := tr.schedule.nome
  nome_pos := tr.schedule.nome_pos
  nome_lt_one := tr.schedule.nome_lt_one
  width := tr.width
  transferSpacing := dyadicPhysicalSpacing
  transferSpacingToZero := dyadicSpacingToZero
  rate := r
  rate_nonnegative := hr0
  rate_lt_one := hr1
  contraction := Hc

/-- **Unconditional instance**: `rate_j = mixRate(w_j, width_j)`. -/
def exprMixRateFamily (tr : ExprAnchorTrajectory) : WilsonDynamicFamily :=
  exprWilsonFamily tr
    (fun j => mixRate (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j))
    (fun _ => mixRate_nonnegative _ _ _) (fun _ => mixRate_lt_one _ _ _)
    (fun _ => wilsonVacuumSqContraction_mixRate _ _ _)

/-- The family's contraction gives the anchor orbit contraction (all-vector ⇒ orbit). -/
theorem exprOrbit_of_family (tr : ExprAnchorTrajectory) (r : Nat → Q')
    (Hc : ∀ j, WilsonVacuumSqContraction (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (tr.width j) (r j)) : ExprPathOrbitContraction tr r := fun j =>
  orbitContraction_of_vacuumSq (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
    (r j) (Hc j) (tr.state j)
    (exprSmoothedState (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
      (tr.expr j) (tr.radius j)).property

/-- X2 on the family is exactly the remaining field of `ExprCenteredContractionLower`. -/
theorem exprLower_of_lowerMargin (tr : ExprAnchorTrajectory) (r : Nat → Q')
    (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j < (1 : Q'))
    (Hc : ∀ j, WilsonVacuumSqContraction (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (tr.width j) (r j)) (m : Q')
    (hX2 : WilsonLowerMargin (exprWilsonFamily tr r hr0 hr1 Hc) m) :
    ExprCenteredContractionLower tr r m where
  contraction := exprOrbit_of_family tr r Hc
  rate_nonneg := hr0
  rate_le_one := fun j => Q'.le_of_lt (hr1 j)
  floor_pos := hX2.1
  lowerRate := hX2.2

/-! ## 5. Upper half from the step-ratio input (no X2) -/

/-- **Upper half**, ceiling `2^(2C+3) + 2^(j0+2)`, from the step-ratio input via the
compatibility theorem `expr_stepRatio_forces_rate_anyC`. Does NOT use X2. -/
theorem wilsonUpper_of_stepRatio (tr : ExprAnchorTrajectory) (r : Nat → Q')
    (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j < (1 : Q'))
    (Hc : ∀ j, WilsonVacuumSqContraction (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (tr.width j) (r j))
    (c : Q') (C j0 : Nat) (hC : 1 ≤ C) (hcC : c ≤ Q'.ofNat C) (hj0 : 2*C ≤ side j0)
    (v rho : Nat → Q') (Hv : ExprHVar tr v) (Hr : ExprHRay tr rho)
    (rho' : Nat → Q') (k : Nat → Nat)
    (hrho'0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho' j) (hrho'1 : ∀ j, j0 ≤ j → rho' j ≤ 1)
    (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho' j) ≤ c)
    (H : ExprStepRatio tr rho' k) :
    WilsonUpperMargin (exprWilsonFamily tr r hr0 hr1 Hc) (Q'.ofNat (2^(2*C+3) + 2^(j0+2))) :=
  ⟨wf_ofNat_pos _ (Nat.lt_of_lt_of_le (Nat.two_pow_pos _) (Nat.le_add_right _ _)), fun j => by
    show (1 : Q') - r j ≤ Q'.ofNat (2^(2*C+3) + 2^(j0+2)) * spacing j
    rcases Nat.lt_or_ge j (j0+2) with h | h
    · exact Q'.le_trans' _ _ _ (small_scale_upper (r j) (hr0 j) j (j0+2) (by omega))
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (wf_ofNat_le (Nat.le_add_left _ _))
          (Q'.le_of_lt (spacing_positive j)))
    · exact Q'.le_trans' _ _ _
        (upper_spacing_form _ _ j
          (expr_stepRatio_forces_rate_anyC tr rho' k c C j0 r (exprNondegFloor tr v rho) hC hcC
            hj0 hrho'0 hrho'1 hk hc H (exprNondegFloor_pos tr v rho Hv Hr)
            (exprShiftedNondegenerate_of_hvar_hray tr v rho Hv Hr) (exprOrbit_of_family tr r Hc)
            hr0 (fun j => Q'.le_of_lt (hr1 j)) j (by omega) (by omega)))
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (wf_ofNat_le (Nat.le_add_right _ _))
          (Q'.le_of_lt (spacing_positive j)))⟩

/-! ## 6. Capstone -/

/-- **Capstone (generic rate).**
Open analytic hypotheses:
* nontriviality: `Hv`, `Hr`, and the step ratio `H` with `hc`, `hrho'0`, `hrho'1`;
* the gap side: X2 `hX2`.
Every other hypothesis is an arithmetic parameter choice.
Conclusions: A03, the Wilson B04 band, decay at every scale and every vacuum-complement
vector, and the necessary consistency `m ≤ 2^(2C+3)`. -/
theorem wilsonGapBranch_of_stepRatio_lowerMargin (tr : ExprAnchorTrajectory) (r : Nat → Q')
    (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j < (1 : Q'))
    (Hc : ∀ j, WilsonVacuumSqContraction (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (tr.width j) (r j))
    (c delta : Q') (C j0 a : Nat) (ha : 1 ≤ a) (hC : 1 ≤ C) (hcC : c ≤ Q'.ofNat C)
    (hj0 : 2*C ≤ side j0) (hj0' : j0 ≤ 2*C+4)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : Q'.ofNat (2^(2*C+3)) ≤ Q'.ofNat (side a) * delta) (v rho : Nat → Q')
    (Hv : ExprHVar tr v) (Hr : ExprHRay tr rho) (rho' : Nat → Q') (k : Nat → Nat)
    (hrho'0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho' j) (hrho'1 : ∀ j, j0 ≤ j → rho' j ≤ 1)
    (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho' j) ≤ c)
    (H : ExprStepRatio tr rho' k) (m : Q')
    (hX2 : WilsonLowerMargin (exprWilsonFamily tr r hr0 hr1 Hc) m) :
    ExprShiftedAnchorPackage tr delta hdelta a (exprNondegFloor tr v rho)
        (exprNondegFloor_pos tr v rho Hv Hr) ∧
      WilsonPhysicalRateBand (exprWilsonFamily tr r hr0 hr1 Hc) ∧
      (∀ j n (y : VacuumComplement (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
          (width := tr.width j)),
        RCle
          (RCmul (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) y.val
              (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) n y.val))
            (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) y.val
              (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) n y.val)))
          (RCmul (RCscale ((r j * r j)^n)
              (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) y.val y.val))
            (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) y.val y.val))) ∧
      m ≤ Q'.ofNat (2^(2*C+3)) :=
  have hup := wilsonUpper_of_stepRatio tr r hr0 hr1 Hc c C j0 hC hcC hj0 v rho Hv Hr rho' k
    hrho'0 hrho'1 hk hc H
  ⟨expr_normalized_anchor_of_hvar_hray_stepRatio_anyC tr c delta C j0 a ha hC hcC hj0 hj0'
      hdelta0 hdelta hcd v rho Hv Hr rho' k hrho'0 hrho'1 hk hc H,
    ⟨m, _, hX2, hup⟩,
    fun j n y => (exprWilsonFamily tr r hr0 hr1 Hc).completedAutocorrelation_sq_decay j n y,
    Q'.le_trans' _ _ _ (lower_side_form m _ (j0+2) (hX2.2 (j0+2)))
      (expr_stepRatio_forces_rate_anyC tr rho' k c C j0 r (exprNondegFloor tr v rho) hC hcC hj0
        hrho'0 hrho'1 hk hc H (exprNondegFloor_pos tr v rho Hv Hr)
        (exprShiftedNondegenerate_of_hvar_hray tr v rho Hv Hr) (exprOrbit_of_family tr r Hc)
        hr0 (fun j => Q'.le_of_lt (hr1 j)) (j0+2) (by omega) (by omega))⟩

/-- **Capstone (`mixRate` instance).** As above, with the unconditional family
`exprMixRateFamily tr`, so the contraction is discharged. On the gap side, the ONLY open
input is X2 `WilsonLowerMargin (exprMixRateFamily tr) m`, i.e. `m·2^-j ≤ mixFraction_j`.
At this Doeblin rate, X2 is not expected to hold. -/
theorem wilsonGapBranch_mixRate (tr : ExprAnchorTrajectory)
    (c delta : Q') (C j0 a : Nat) (ha : 1 ≤ a) (hC : 1 ≤ C) (hcC : c ≤ Q'.ofNat C)
    (hj0 : 2*C ≤ side j0) (hj0' : j0 ≤ 2*C+4)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : Q'.ofNat (2^(2*C+3)) ≤ Q'.ofNat (side a) * delta) (v rho : Nat → Q')
    (Hv : ExprHVar tr v) (Hr : ExprHRay tr rho) (rho' : Nat → Q') (k : Nat → Nat)
    (hrho'0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho' j) (hrho'1 : ∀ j, j0 ≤ j → rho' j ≤ 1)
    (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho' j) ≤ c)
    (H : ExprStepRatio tr rho' k) (m : Q')
    (hX2 : WilsonLowerMargin (exprMixRateFamily tr) m) :
    ExprShiftedAnchorPackage tr delta hdelta a (exprNondegFloor tr v rho)
        (exprNondegFloor_pos tr v rho Hv Hr) ∧
      WilsonPhysicalRateBand (exprMixRateFamily tr) ∧
      (∀ j n (y : VacuumComplement (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
          (width := tr.width j)),
        RCle
          (RCmul (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) y.val
              (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) n y.val))
            (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) y.val
              (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) n y.val)))
          (RCmul (RCscale (((exprMixRateFamily tr).rate j * (exprMixRateFamily tr).rate j)^n)
              (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) y.val y.val))
            (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) y.val y.val))) ∧
      m ≤ Q'.ofNat (2^(2*C+3)) :=
  wilsonGapBranch_of_stepRatio_lowerMargin tr _ _ _ _ c delta C j0 a ha hC hcC hj0 hj0'
    hdelta0 hdelta hcd v rho Hv Hr rho' k hrho'0 hrho'1 hk hc H m hX2

#print axioms iterated_of_vacuumSq
#print axioms autocorrelation_sq_decay_of_vacuumSq
#print axioms WilsonDynamicFamily
#print axioms WilsonDynamicFamily.latticeMargin_pos
#print axioms WilsonDynamicFamily.completedAutocorrelation_sq_decay
#print axioms WilsonLowerMargin
#print axioms WilsonPhysicalRateBand
#print axioms exprWilsonFamily
#print axioms exprMixRateFamily
#print axioms exprOrbit_of_family
#print axioms exprLower_of_lowerMargin
#print axioms wilsonUpper_of_stepRatio
#print axioms wilsonGapBranch_of_stepRatio_lowerMargin
#print axioms wilsonGapBranch_mixRate

end YMGap.Continuum.BF4WilsonAllNomeWilsonDynamicFamily
