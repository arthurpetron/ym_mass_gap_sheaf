/-
# Two-sided band: step ratio + lower contraction ⇒ A03 + a B04-shaped band (PACKAGING ONLY)

Companion to `audits/AUDIT-STEP-RATIO-WINDOW-SURVIVAL-2026-10-06.md` §15. ADDITIVE.

THIS IS REFORMULATION/PACKAGING ONLY. It makes NO progress on either input:
* the nontriviality input, a bounded intermediate-lag step ratio;
* the gap-branch input, a centered contraction with a lower margin.
Both stay OPEN.

B04 shape. B04l consumes `DynamicVacuumSectorPhysicalRateBand family`
(`BF4PhysicalDynamicVacuumSectorCompletedFamily`). Its fields are `floor, ceiling > 0`, with
`floor·spacing_j ≤ 1 − rate_j ≤ ceiling·spacing_j`, where:
* `rate_j` is the rate of a `CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData`.
  That is an ALL-VECTOR squared-norm contraction of the completed vacuum-complement
  transfer on the SU(2) extent-one CUBE carrier.
* Along the trajectory, `trajectoryDynamicFamily` uses `spacing_j = 2^-j`. The open Prop
  `PathPhysicalContractionBand` is equivalent to this band.

On the Expr layer (all-nome WILSON carrier), the analogous objects are:
* `ExprCenteredContractionLower tr r m` (OPEN, gap branch).
  * `ExprPathOrbitContraction tr r`: an ORBIT contraction on the centered anchor `Y_j`,
    `B(Ty,Ty) ≤ r_j² B(y,y)` for `y = T^k Y_j`.
  * `0 ≤ r_j ≤ 1`, and the lower margin `m·spacing_j ≤ 1 − r_j`, i.e. `m ≤ side_j(1−r_j)`.
* `ExprPhysicalRateBand r`: field-for-field B04l's band, with `rate_j := r_j` and the same
  spacing `2^-j`.

Results:
* `expr_twoSidedBand_package`. The step-ratio hypotheses of
  `expr_normalized_anchor_of_hvar_hray_stepRatio_anyC` (`side_j(1−ρ'_j) ≤ c ≤ C` at a lag
  `k_j ≤ side_j/2`, e.g. `k_j = side_j/2`) plus `ExprCenteredContractionLower tr r m` give:
  * A03 (`ExprShiftedAnchorPackage`);
  * the UPPER half for free, from the window/gap compatibility theorem
    (`expr_stepRatio_forces_rate_anyC`): `side_j(1−r_j) ≤ 2^(2C+3)` for `j ≥ max(2, j0)`;
  * CONSISTENCY, which is necessary: `m ≤ 2^(2C+3)`;
  * the band `exprTwoSidedBand` with floor `m` and ceiling `2^(2C+3) + 2^(j0+2)`, for ALL
    `j`. Scales below `j0+2` are covered by `1 − r_j ≤ 1 ≤ 2^(j0+2)·spacing_j`.
* `b04Band_of_exprBand`: Type-level handoff into B04l's EXACT input
  `DynamicVacuumSectorPhysicalRateBand (trajectoryDynamicFamily tr.schedule gap)`.
  It needs any cube gap family `gap` whose rates equal `r_j`.

HONEST GAP to B04, two missing ingredients:
1. A cube-carrier strict contraction `gap j` at every `w_j` (the open
   `PathCubeContraction`; the existing producer covers only `w ≤ 1/2`).
2. A cube↔Wilson bridge making `(gap j).rate` the rate of the SAME transfer that contracts
   the Wilson anchor orbit. Bare rational equality `hmatch` is bookkeeping, not a bridge.
   See `audits/SCOPE-CUBE-WILSON-CARRIER-BRIDGE-2026-10-06.md`.

Also, the Expr input is an orbit contraction, which is weaker than B04's all-vector
contraction. The all-vector Wilson analogue is `WilsonVacuumRayleighRate`
(`BF4WilsonAllNomeH1FixedScale`, Rayleigh form). Rayleigh ⇒ orbit contraction is
paper-level only (see the window-gap audit remark).

Constructive, no external library; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeExprStepRatioAnyC
import YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory

namespace YMGap.Continuum.BF4WilsonAllNomeExprTwoSidedBand

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side spacing spacing_positive unit_side)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory
open YMGap.Continuum.BF4WilsonAllNomeExprShiftedAnchorPackage (ExprShiftedAnchorPackage)
open YMGap.Continuum.BF4WilsonAllNomeExprStepRatioWindowSurvival (ExprStepRatio)
open YMGap.Continuum.BF4WilsonAllNomeExprWindowGapCompatibility (ExprPathOrbitContraction)
open YMGap.Continuum.BF4WilsonAllNomeExprStepRatioAnyC
  (expr_normalized_anchor_of_hvar_hray_stepRatio_anyC expr_stepRatio_forces_rate_anyC)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (trajectoryDynamicFamily)
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
  (CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData)
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
  (DynamicVacuumSectorPhysicalRateBand)

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Helpers -/

private theorem tb_ofNat_le {a b : Nat} (h : a ≤ b) : Q'.ofNat a ≤ Q'.ofNat b := by
  change (a : Int)*1 ≤ (b : Int)*1
  simp only [Int.mul_one]
  omega

private theorem tb_ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  change (0 : Int)*1 ≤ (n : Int)*1
  simp only [Int.mul_one]
  omega

private theorem tb_ofNat_pos (n : Nat) (hn : 0 < n) : (0 : Q') < Q'.ofNat n := by
  change (0 : Int)*1 < (n : Int)*1
  simp only [Int.mul_one]
  omega

private theorem tb_one_sub_le_one {x : Q'} (h0 : (0 : Q') ≤ x) : (1 : Q') - x ≤ 1 :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_add_zero_eqv ((1 : Q') - x)))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left ((1 : Q') - x) 0 x h0)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0) (by decide)
        (fun | 0 => (1 : Q') | _ => x))))

/-- `side_j · spacing_j ≈ 1`. -/
private theorem tb_side_spacing (j : Nat) : Q'.ofNat (side j) * spacing j ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (unit_side j)

/-! ## 1. Scalar forms: spacing ⇔ side -/

/-- Lower margin, spacing form ⇒ side form: `m·spacing_j ≤ x` ⇒ `m ≤ side_j·x`. -/
theorem lower_side_form (m x : Q') (j : Nat) (h : m * spacing j ≤ x) :
    m ≤ Q'.ofNat (side j) * x :=
  Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => Q'.ofNat (side j) | 1 => m | _ => spacing j))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (tb_side_spacing j)) (Q'.mul_one_eqv m))))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ h (tb_ofNat_nonneg _))

/-- Upper bound, side form ⇒ spacing form: `side_j·x ≤ c` ⇒ `x ≤ c·spacing_j`. -/
theorem upper_spacing_form (c x : Q') (j : Nat) (h : Q'.ofNat (side j) * x ≤ c) :
    x ≤ c * spacing j :=
  Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => Q'.ofNat (side j) | 1 => x | _ => spacing j))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (tb_side_spacing j)) (Q'.mul_one_eqv x))))
    (Q'.mul_le_mul_of_nonneg_right _ _ _ h (Q'.le_of_lt (spacing_positive j)))

/-- Small scales: `0 ≤ r`, `j ≤ N` ⇒ `1 − r ≤ 2^N·spacing_j`. -/
theorem small_scale_upper (r : Q') (hr0 : (0 : Q') ≤ r) (j N : Nat) (hjN : j ≤ N) :
    (1 : Q') - r ≤ Q'.ofNat (2^N) * spacing j :=
  Q'.le_trans' _ _ _ (tb_one_sub_le_one hr0)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (tb_side_spacing j))
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (tb_ofNat_le (Nat.pow_le_pow_right (by decide) hjN)) (Q'.le_of_lt (spacing_positive j))))

/-! ## 2. The gap-branch input and the B04-shaped band on the Expr layer -/

/-- **Gap-branch input (OPEN), Expr layer.** Orbit contraction of the centered anchor
`Y_j` at rate `r_j ∈ [0,1]`, with the lower margin `m·spacing_j ≤ 1 − r_j`
(`⇔ m ≤ side_j(1−r_j)`; `m·a_j ≤ 1 − r_j` in the fixed-physical-box picture). -/
structure ExprCenteredContractionLower (tr : ExprAnchorTrajectory) (r : Nat → Q') (m : Q') :
    Prop where
  contraction : ExprPathOrbitContraction tr r
  rate_nonneg : ∀ j, (0 : Q') ≤ r j
  rate_le_one : ∀ j, r j ≤ 1
  floor_pos : (0 : Q') < m
  lowerRate : ∀ j, m * spacing j ≤ (1 : Q') - r j

/-- **B04-shaped band**, field-for-field `DynamicVacuumSectorPhysicalRateBand` with
`latticeMargin_j := 1 − r_j` and `spacing_j = 2^-j`. -/
structure ExprPhysicalRateBand (r : Nat → Q') : Type where
  floor : Q'
  floor_pos : (0 : Q') < floor
  ceiling : Q'
  ceiling_pos : (0 : Q') < ceiling
  lowerRate : ∀ j, floor * spacing j ≤ (1 : Q') - r j
  upperRate : ∀ j, (1 : Q') - r j ≤ ceiling * spacing j

/-- Upper half from compatibility (side form), for `j ≥ max(2, j0)`. -/
theorem expr_upper_of_stepRatio (tr : ExprAnchorTrajectory) (c : Q') (C j0 : Nat) (hC : 1 ≤ C)
    (hcC : c ≤ Q'.ofNat C) (hj0 : 2*C ≤ side j0) (v rho : Nat → Q')
    (Hv : ExprHVar tr v) (Hr : ExprHRay tr rho) (rho' : Nat → Q') (k : Nat → Nat)
    (hrho'0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho' j) (hrho'1 : ∀ j, j0 ≤ j → rho' j ≤ 1)
    (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho' j) ≤ c)
    (H : ExprStepRatio tr rho' k) (r : Nat → Q') (m : Q') (G : ExprCenteredContractionLower tr r m)
    (j : Nat) (hj : 2 ≤ j) (hjj0 : j0 ≤ j) :
    Q'.ofNat (side j) * ((1 : Q') - r j) ≤ Q'.ofNat (2^(2*C+3)) :=
  expr_stepRatio_forces_rate_anyC tr rho' k c C j0 r (exprNondegFloor tr v rho) hC hcC hj0
    hrho'0 hrho'1 hk hc H (exprNondegFloor_pos tr v rho Hv Hr)
    (exprShiftedNondegenerate_of_hvar_hray tr v rho Hv Hr) G.contraction G.rate_nonneg
    G.rate_le_one j hj hjj0

/-- **The two-sided band** (data): floor `m`, ceiling `2^(2C+3) + 2^(j0+2)`, all scales. -/
def exprTwoSidedBand (tr : ExprAnchorTrajectory) (c : Q') (C j0 : Nat) (hC : 1 ≤ C)
    (hcC : c ≤ Q'.ofNat C) (hj0 : 2*C ≤ side j0) (v rho : Nat → Q')
    (Hv : ExprHVar tr v) (Hr : ExprHRay tr rho) (rho' : Nat → Q') (k : Nat → Nat)
    (hrho'0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho' j) (hrho'1 : ∀ j, j0 ≤ j → rho' j ≤ 1)
    (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho' j) ≤ c)
    (H : ExprStepRatio tr rho' k) (r : Nat → Q') (m : Q') (G : ExprCenteredContractionLower tr r m) :
    ExprPhysicalRateBand r where
  floor := m
  floor_pos := G.floor_pos
  ceiling := Q'.ofNat (2^(2*C+3) + 2^(j0+2))
  ceiling_pos := tb_ofNat_pos _ (Nat.lt_of_lt_of_le (Nat.two_pow_pos _) (Nat.le_add_right _ _))
  lowerRate := G.lowerRate
  upperRate := fun j => by
    rcases Nat.lt_or_ge j (j0+2) with h | h
    · exact Q'.le_trans' _ _ _ (small_scale_upper (r j) (G.rate_nonneg j) j (j0+2) (by omega))
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (tb_ofNat_le (Nat.le_add_left _ _))
          (Q'.le_of_lt (spacing_positive j)))
    · exact Q'.le_trans' _ _ _
        (upper_spacing_form _ _ j (expr_upper_of_stepRatio tr c C j0 hC hcC hj0 v rho Hv Hr rho' k
          hrho'0 hrho'1 hk hc H r m G j (by omega) (by omega)))
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (tb_ofNat_le (Nat.le_add_right _ _))
          (Q'.le_of_lt (spacing_positive j)))

/-- **Two-sided band package (PACKAGING ONLY).** Step ratio (`c ≤ C`, lag `k_j ≤ side_j/2`)
+ H-var + H-ray + the gap-branch input `ExprCenteredContractionLower tr r m` give:
A03; the upper half `side_j(1−r_j) ≤ 2^(2C+3)` (`j ≥ max(2,j0)`); the NECESSARY consistency
`m ≤ 2^(2C+3)`; and the all-scale band `exprTwoSidedBand` with floor `m`. -/
theorem expr_twoSidedBand_package (tr : ExprAnchorTrajectory)
    (c delta : Q') (C j0 a : Nat) (ha : 1 ≤ a) (hC : 1 ≤ C) (hcC : c ≤ Q'.ofNat C)
    (hj0 : 2*C ≤ side j0) (hj0' : j0 ≤ 2*C+4)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : Q'.ofNat (2^(2*C+3)) ≤ Q'.ofNat (side a) * delta) (v rho : Nat → Q')
    (Hv : ExprHVar tr v) (Hr : ExprHRay tr rho) (rho' : Nat → Q') (k : Nat → Nat)
    (hrho'0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho' j) (hrho'1 : ∀ j, j0 ≤ j → rho' j ≤ 1)
    (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho' j) ≤ c)
    (H : ExprStepRatio tr rho' k) (r : Nat → Q') (m : Q')
    (G : ExprCenteredContractionLower tr r m) :
    ExprShiftedAnchorPackage tr delta hdelta a (exprNondegFloor tr v rho)
        (exprNondegFloor_pos tr v rho Hv Hr) ∧
      (∀ j, 2 ≤ j → j0 ≤ j →
        m ≤ Q'.ofNat (side j) * ((1 : Q') - r j) ∧
        Q'.ofNat (side j) * ((1 : Q') - r j) ≤ Q'.ofNat (2^(2*C+3))) ∧
      m ≤ Q'.ofNat (2^(2*C+3)) ∧
      (exprTwoSidedBand tr c C j0 hC hcC hj0 v rho Hv Hr rho' k hrho'0 hrho'1 hk hc H r m G).floor
        = m :=
  have hup := fun j (hj : 2 ≤ j) (hjj0 : j0 ≤ j) =>
    expr_upper_of_stepRatio tr c C j0 hC hcC hj0 v rho Hv Hr rho' k hrho'0 hrho'1 hk hc H r m G
      j hj hjj0
  ⟨expr_normalized_anchor_of_hvar_hray_stepRatio_anyC tr c delta C j0 a ha hC hcC hj0 hj0'
      hdelta0 hdelta hcd v rho Hv Hr rho' k hrho'0 hrho'1 hk hc H,
    fun j hj hjj0 => ⟨lower_side_form m _ j (G.lowerRate j), hup j hj hjj0⟩,
    Q'.le_trans' _ _ _ (lower_side_form m _ (j0+2) (G.lowerRate (j0+2)))
      (hup (j0+2) (by omega) (by omega)),
    rfl⟩

/-! ## 3. Handoff into B04l's exact input shape (bookkeeping) -/

/-- **Type-level handoff.** Given ANY cube-carrier gap family `gap` (B04l data, the open
`PathCubeContraction`) whose rates equal `r_j`, an `ExprPhysicalRateBand r` IS B04l's
input `DynamicVacuumSectorPhysicalRateBand (trajectoryDynamicFamily tr.schedule gap)`.
The rational equality `hmatch` is NOT a carrier bridge: making `(gap j).rate` the rate of
the same transfer that contracts the Wilson anchor is the open cube↔Wilson node. -/
def b04Band_of_exprBand (tr : ExprAnchorTrajectory)
    (gap : ∀ j, CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) 0)
    (r : Nat → Q') (hmatch : ∀ j, (gap j).rate = r j) (band : ExprPhysicalRateBand r) :
    DynamicVacuumSectorPhysicalRateBand (trajectoryDynamicFamily tr.schedule gap) where
  floor := band.floor
  floor_pos := band.floor_pos
  ceiling := band.ceiling
  ceiling_pos := band.ceiling_pos
  lowerRate := fun j => by
    show band.floor * spacing j ≤ (1 : Q') - (gap j).rate
    rw [hmatch j]
    exact band.lowerRate j
  upperRate := fun j => by
    show (1 : Q') - (gap j).rate ≤ band.ceiling * spacing j
    rw [hmatch j]
    exact band.upperRate j

#print axioms lower_side_form
#print axioms upper_spacing_form
#print axioms small_scale_upper
#print axioms ExprCenteredContractionLower
#print axioms ExprPhysicalRateBand
#print axioms expr_upper_of_stepRatio
#print axioms exprTwoSidedBand
#print axioms expr_twoSidedBand_package
#print axioms b04Band_of_exprBand

end YMGap.Continuum.BF4WilsonAllNomeExprTwoSidedBand
