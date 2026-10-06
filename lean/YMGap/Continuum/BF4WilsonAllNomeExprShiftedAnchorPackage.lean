/-
# The A03 shifted normalized-anchor package for an arbitrary expression anchor

Companion to `audits/AUDIT-EXPR-ANCHOR-TRAJECTORY-2026-10-06.md` §2. ADDITIVE. This file
copies the `smoothedAnchorData` / `shiftedPathAnchor` / `ShiftedAnchorPackage` layer
(`BF4WilsonAllNomeGenericNormalizedAnchor` §3, `BF4WilsonAllNomeShiftedH1Anchor` §4),
with the plaquette family `familyState` replaced by an arbitrary slab expression `ψ`
and the carrier width `trajWidth j` replaced by `tr.width j`.

Proved:
* `exprAnchorData`: `NormalizedAnchorData` for `Y_M(ψ)` at any block `s ≥ 1`. It
  carries the concrete Cauchy representative of `R_M(2s)` built from the centered
  time moments of `ψ`.
* `expr_normalized_anchor_shifted`: the shifted H1 plus `fl_j ≤ R_j(side_j)` give the
  full package. The package is unit norm, block floors `κ^i`, real-time survival
  `κ^(i+1)` and the geometric increment modulus, with `κ = (1-δ)^(2^a)` and
  `c0 ≤ 2^a δ`.
* `expr_normalized_anchor_of_windowSurvival`: the same, from window survival.
* **`expr_normalized_anchor_of_windowSurvival_hvar_hray`**: the package with floor
  `fl_j = ρ_j^(2M_j+side_j) v_j`, CONDITIONAL on three OPEN inputs: window survival,
  H-var and H-ray. It also needs the scalar side conditions `0 < θ ≤ 1`,
  `2(1-θ) ≤ θ c0`, `1 ≤ c0`, `0 ≤ δ < 1`, `c0 ≤ 2^a δ` and `1 ≤ a`.

Constructive, no external library; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory

namespace YMGap.Continuum.BF4WilsonAllNomeExprShiftedAnchorPackage

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4DyadicWilsonSquare (side side_positive spacing unit_side)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion completedInner completedInner_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedTime_add timeNonexpansive VacuumComplement)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment centeredTimeMomentCauchy)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector (centeredStream centeredExcitation)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime (orbitSum responseSum)
open YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState (timeKernel)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory
  (side_split block_survival_of_oneStep_energy)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (bondCompletedInner bondCompletedDistance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealTime (action)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (PositiveTimeValue realValue)
open YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedMacroRatio (macroGeometricRadius)
open YMGap.Continuum.BF4WilsonAllNomeGenericNormalizedAnchor
  (NormalizedAnchorData kernelCSum kernelCSumCauchy responseSum_mk repOrbit repOrbit_class
   pathKappa_pos)
open YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor
  (OneStepEpsBound shift_norm_pin shift_response_pin)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory.ExprAnchorTrajectory

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)
local infix:50 " ≈ " => Q'.eqv

/-! ## Local helpers (copies of standard private lemmas) -/

private theorem ep_scale_rational (c q : Q') : RCscale c (Rq q) = Rq (c*q) := by
  rw [RCscale_mk]
  exact Quotient.sound (CRealAlg.ofQ'_mul c q).symm

private theorem ep_ofNat_pos (L : Nat) (hL : 0 < L) : (0 : Q') < Q'.ofNat L := by
  change (0 : Int)*1 < (L : Int)*1
  simp only [Int.mul_one]
  omega

private theorem ep_ofNat_mul (a b : Nat) :
    Q'.ofNat (a*b) ≈ Q'.ofNat a * Q'.ofNat b := by
  have hd1 : ((Q'.ofNat a * Q'.ofNat b).den : Int) = 1 := rfl
  have hd2 : ((Q'.ofNat (a*b)).den : Int) = 1 := rfl
  show ((a*b : Nat) : Int) * ((Q'.ofNat a * Q'.ofNat b).den : Int)
    = (((a : Nat) : Int) * ((b : Nat) : Int)) * ((Q'.ofNat (a*b)).den : Int)
  rw [hd1, hd2]
  push_cast
  omega

private theorem ep_pow_one (q : Q') : q^1 ≈ q := by
  change q * 1 ≈ q
  exact Q'.mul_one_eqv q

private theorem ep_scale_cancel {k : Q'} (hk : (0 : Q') < k) {a b : RC}
    (h : RCle (RCscale k a) (RCscale k b)) : RCle a b := by
  have h' := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos k hk)) h
  rw [RCscale_RCscale, RCscale_RCscale] at h'
  have e : Q'.recipPos k hk * k ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv k hk)
  rw [RCSignedPairBudget.scale_congr e, RCSignedPairBudget.scale_congr e,
    RCscale_one, RCscale_one] at h'
  exact h'

private theorem ep_traj_halves (j : Nat) (hj : 1 ≤ j) : side j/2+side j/2 = side j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i+1 := ⟨j-1, by omega⟩
  simp only [side, Nat.pow_succ]
  omega

private theorem ep_traj_hsp (j : Nat) : Q'.ofNat (side j)*spacing j ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (unit_side j)

/-! ## 1. Anchor data for the smoothing of an arbitrary expression -/

section Expr

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (ψ : IntrinsicExpression width)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "D" => seminorm hw0 hw1 (width := width)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid (seminorm hw0 hw1 (width := width)))

/-- Explicit representative of the centered vector of `ψ`. -/
def exprStream : (D).Cauchy := centeredStream hw0 hw1 ψ

theorem exprStream_class :
    Class (exprStream hw0 hw1 width ψ) = (centeredExcitation hw0 hw1 ψ).val := rfl

/-- Range witness for `T(s) Y_M(ψ)`, `s ≥ 1`. -/
def exprSector (M s : Nat) : BF4WilsonAllNomeTimeSector.State hw0 hw1 (width := width) :=
  BF4WilsonAllNomeTimeSector.fromTime hw0 hw1
    ((timeNonexpansive hw0 hw1 (width := width) (s-1)).mapCauchy
      (repOrbit hw0 hw1 width (exprStream hw0 hw1 width ψ) (timeKernel M)))

theorem exprSector_pin (M s : Nat) (hs : 0 < s) :
    (exprSector hw0 hw1 width ψ M s).val = T s (exprSmoothedVector hw0 hw1 width ψ M) := by
  change T 1 (T (s-1) (Class (repOrbit hw0 hw1 width (exprStream hw0 hw1 width ψ)
    (timeKernel M)))) = _
  rw [repOrbit_class, ← completedTime_add, show 1+(s-1) = s by omega]
  rfl

/-- Concrete real representative of `R_M(n)` built from the centered moments of `ψ`. -/
def exprNorm (M n : Nat) : CReal :=
  kernelCSum (timeKernel M) (fun m => kernelCSum (timeKernel M)
    (fun k => centeredTimeMoment hw0 hw1 (m+k+n) ψ ψ))

def exprNormCauchy (M n : Nat) : QCauchy (exprNorm hw0 hw1 width ψ M n).approx :=
  kernelCSumCauchy (timeKernel M) _ (fun m => kernelCSumCauchy (timeKernel M) _
    (fun k => centeredTimeMomentCauchy hw0 hw1 (m+k+n) ψ ψ))

theorem exprNorm_pin (M n : Nat) :
    exprResponse hw0 hw1 width ψ M n = Quotient.mk crealSetoid (exprNorm hw0 hw1 width ψ M n) := by
  rw [exprResponse_pin]
  unfold exprNorm
  rw [← responseSum_mk]
  apply congrArg (responseSum (timeKernel M))
  funext m
  exact responseSum_mk (timeKernel M) _

/-- Normalized-anchor data of `Y_M(ψ)` at block `s`, with a supplied positive rational. -/
def exprAnchorData (M s : Nat) (hs : 0 < s) (fl : Q') (hfl : (0 : Q') < fl) :
    NormalizedAnchorData hw0 hw1 width where
  base := exprSmoothedState hw0 hw1 width ψ M
  block := s
  norm := exprNorm hw0 hw1 width ψ M (2*s)
  normCauchy := exprNormCauchy hw0 hw1 width ψ M (2*s)
  norm_pin := exprNorm_pin hw0 hw1 width ψ M (2*s)
  floor := fl
  floor_pos := hfl
  sector := exprSector hw0 hw1 width ψ M s
  sector_pin := exprSector_pin hw0 hw1 width ψ M s hs

end Expr

/-! ## 2. The shifted path anchor along an expression trajectory -/

/-- Anchor data of `Y_j` at block `side_j`, floor `κ·fl_j`, `κ = (1-δ)^(2^a)`. -/
def exprShiftedPathAnchor (tr : ExprAnchorTrajectory) (delta : Q') (hdelta : delta < (1 : Q'))
    (a : Nat) (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j) (j : Nat) :
    NormalizedAnchorData (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j) :=
  exprAnchorData (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
    (tr.expr j) (tr.radius j) (side j) (side_positive j)
    (((1 : Q') - delta)^(side a) * fl j)
    (Q'.mul_pos (pathKappa_pos delta hdelta a) (hfl j))

/-- Shifted H1 + nondegeneracy give the macro ratio `κ R_j(side_j) ≤ R_j(2 side_j)`. -/
theorem expr_shifted_macroRatio (tr : ExprAnchorTrajectory) (c0 delta : Q') (a : Nat)
    (ha : 1 ≤ a) (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta) (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (H1s : ExprShiftedEpsBound tr c0) (Hnd : ExprShiftedNondegenerate tr fl)
    (j : Nat) (haj : a ≤ j) :
    (exprShiftedPathAnchor tr delta hdelta a fl hfl j).MacroRatio
      (((1 : Q') - delta)^(side a)) := by
  have hw0 := tr.schedule.nome_pos j
  have hw1 := tr.schedule.nome_lt_one j
  have hs := side_split a j haj
  have hL : 0 < side (j-a) := side_positive (j-a)
  have hh := ep_traj_halves j (by omega)
  have hxx := shift_norm_pin hw0 hw1 (tr.width j) (tr.state j) (side j / 2)
  rw [show 2*(side j/2) = side j by omega] at hxx
  have hnormx : RCle (Rq (fl j)) (completedInner hw0 hw1
      (completedTime hw0 hw1 (side j / 2) (tr.state j))
      (completedTime hw0 hw1 (side j / 2) (tr.state j))) := by
    rw [hxx]
    exact Hnd j
  have hkpos := ep_ofNat_pos (side a) (side_positive a)
  have hN := completedInner_nonnegative hw0 hw1 (completedTime hw0 hw1 (side j / 2) (tr.state j))
  have hside : Q'.ofNat (side j) ≈ Q'.ofNat (side a) * Q'.ofNat (side (j-a)) := by
    rw [side_split a j haj]
    exact Q'.eqv_trans _ _ _ (ep_ofNat_mul _ _) (Q'.mul_comm_eqv _ _)
  have h1s := H1s j
  unfold OneStepEpsBound at h1s
  have hE : RCle (RCscale (Q'.ofNat (side (j-a)))
      (RCsub (completedInner hw0 hw1 (completedTime hw0 hw1 (side j / 2) (tr.state j))
          (completedTime hw0 hw1 (side j / 2) (tr.state j)))
        (completedInner hw0 hw1 (completedTime hw0 hw1 (side j / 2) (tr.state j))
          (completedTime hw0 hw1 1 (completedTime hw0 hw1 (side j / 2) (tr.state j))))))
      (RCscale delta (completedInner hw0 hw1 (completedTime hw0 hw1 (side j / 2) (tr.state j))
          (completedTime hw0 hw1 (side j / 2) (tr.state j)))) := by
    apply ep_scale_cancel hkpos
    rw [RCscale_RCscale, RCscale_RCscale, ← RCSignedPairBudget.scale_congr hside]
    exact RCle_trans h1s (RCscale_scalar_mono hc0 hN)
  have hchain := block_survival_of_oneStep_energy hw0 hw1 (tr.width j)
    (completedTime hw0 hw1 (side j / 2) (tr.state j))
    (side j) (side (j-a)) (side a) hs hL delta (fl j) hdelta0 hdelta (hfl j) hnormx hE 1
  rw [Nat.mul_one, RCSignedPairBudget.scale_congr (ep_pow_one _), hxx,
    shift_response_pin hw0 hw1 (tr.width j) (tr.state j) (side j / 2) (side j),
    show side j + 2*(side j/2) = 2 * side j by omega] at hchain
  exact hchain

/-- The anchor floor `κ·fl_j` is a TRUE floor of `R_j(2 side_j)`. -/
theorem expr_shifted_anchor_floor (tr : ExprAnchorTrajectory) (c0 delta : Q') (a : Nat)
    (ha : 1 ≤ a) (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta) (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (H1s : ExprShiftedEpsBound tr c0) (Hnd : ExprShiftedNondegenerate tr fl)
    (j : Nat) (haj : a ≤ j) :
    leEv (ofQ' (exprShiftedPathAnchor tr delta hdelta a fl hfl j).floor)
      (exprShiftedPathAnchor tr delta hdelta a fl hfl j).norm := by
  have hw0 := tr.schedule.nome_pos j
  have hw1 := tr.schedule.nome_lt_one j
  have hratio := expr_shifted_macroRatio tr c0 delta a ha hdelta0 hdelta hc0 fl hfl H1s Hnd j haj
  have hk0 : (0 : Q') ≤ ((1 : Q') - delta)^(side a) := Q'.le_of_lt (pathKappa_pos delta hdelta a)
  have hnd := RCscale_mono hk0 (Hnd j)
  rw [ep_scale_rational] at hnd
  change RCle (RCscale (((1 : Q') - delta)^(side a)) (tr.response j (side j)))
    (completedInner hw0 hw1 (tr.state j) (completedTime hw0 hw1 (2 * side j) (tr.state j)))
    at hratio
  have h := RCle_trans hnd hratio
  have hpin := exprNorm_pin hw0 hw1 (tr.width j) (tr.expr j) (tr.radius j) (2 * side j)
  unfold exprResponse at hpin
  change RCle _ (completedInner hw0 hw1
    (exprSmoothedVector hw0 hw1 (tr.width j) (tr.expr j) (tr.radius j))
    (completedTime hw0 hw1 (2 * side j)
      (exprSmoothedVector hw0 hw1 (tr.width j) (tr.expr j) (tr.radius j)))) at h
  rw [hpin] at h
  exact h

/-- The A03 normalized-anchor package for the shifted expression anchor. -/
def ExprShiftedAnchorPackage (tr : ExprAnchorTrajectory) (delta : Q')
    (hdelta : delta < (1 : Q')) (a : Nat) (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j) : Prop :=
  ∀ j : Nat, a ≤ j →
    completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
        (exprShiftedPathAnchor tr delta hdelta a fl hfl j).normalized.val
        (exprShiftedPathAnchor tr delta hdelta a fl hfl j).normalized.val = Rq 1 ∧
    (∀ i : Nat, RCle (Rq ((((1 : Q') - delta)^(side a))^i))
      (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
        (exprShiftedPathAnchor tr delta hdelta a fl hfl j).normalized.val
        (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (i * side j)
          (exprShiftedPathAnchor tr delta hdelta a fl hfl j).normalized.val))) ∧
    (∀ (i : Nat) (time : PositiveTimeValue),
      RCle (RCscale (spacing j) (realValue time)) (Rq (Q'.ofNat i)) →
      RCle (Rq ((((1 : Q') - delta)^(side a))^(i+1)))
        (bondCompletedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
          (exprShiftedPathAnchor tr delta hdelta a fl hfl j).bondExcitation
          (action (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) time
            (exprShiftedPathAnchor tr delta hdelta a fl hfl j).bondExcitation))) ∧
    (∀ (epsilon : Q'), (0 : Q') < epsilon → ∀ time : PositiveTimeValue,
      RCle (RCscale (spacing j) (realValue time))
        (Rq (macroGeometricRadius (((1 : Q') - delta)^(side a)) epsilon)) →
      RCle (bondCompletedDistance (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
        (action (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) time
          (exprShiftedPathAnchor tr delta hdelta a fl hfl j).bondExcitation)
        (exprShiftedPathAnchor tr delta hdelta a fl hfl j).bondExcitation) (Rq epsilon))

/-- **Shifted A03 theorem for an expression anchor.** -/
theorem expr_normalized_anchor_shifted (tr : ExprAnchorTrajectory) (c0 delta : Q') (a : Nat)
    (ha : 1 ≤ a) (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta) (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (H1s : ExprShiftedEpsBound tr c0) (Hnd : ExprShiftedNondegenerate tr fl) :
    ExprShiftedAnchorPackage tr delta hdelta a fl hfl := by
  intro j haj
  have hkappa := pathKappa_pos delta hdelta a
  have hfloor := expr_shifted_anchor_floor tr c0 delta a ha hdelta0 hdelta hc0 fl hfl H1s Hnd j haj
  have hratio := expr_shifted_macroRatio tr c0 delta a ha hdelta0 hdelta hc0 fl hfl H1s Hnd j haj
  refine ⟨NormalizedAnchorData.normalized_norm (exprShiftedPathAnchor tr delta hdelta a fl hfl j)
      hfloor,
    fun i => NormalizedAnchorData.block_floor (exprShiftedPathAnchor tr delta hdelta a fl hfl j) _
      hkappa hfloor hratio i,
    fun i time ht => NormalizedAnchorData.real_floor
      (exprShiftedPathAnchor tr delta hdelta a fl hfl j) _ hkappa
      (side_positive j) hfloor hratio (spacing j) (ep_traj_hsp j) i time ht,
    fun epsilon he time ht => NormalizedAnchorData.real_increment
      (exprShiftedPathAnchor tr delta hdelta a fl hfl j) _ hkappa (side_positive j)
      (ep_traj_halves j (by omega)) hfloor hratio (spacing j) (ep_traj_hsp j) epsilon he time ht⟩

/-- Same package from backward-window survival (OPEN) and any qualitative floor. -/
theorem expr_normalized_anchor_of_windowSurvival (tr : ExprAnchorTrajectory)
    (c0 theta delta : Q') (a : Nat) (ha : 1 ≤ a)
    (h0 : (0 : Q') < theta) (h1 : theta ≤ 1)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) (hc1 : (1 : Q') ≤ c0)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : c0 ≤ Q'.ofNat (side a) * delta) (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (Hw : ExprShiftedWindowSurvival tr theta) (Hnd : ExprShiftedNondegenerate tr fl) :
    ExprShiftedAnchorPackage tr delta hdelta a fl hfl :=
  expr_normalized_anchor_shifted tr c0 delta a ha hdelta0 hdelta hcd fl hfl
    (exprShiftedEpsBound_of_windowSurvival tr c0 theta h0 h1 hc0 hc1 Hw) Hnd

/-- **The general A03 package, conditional on window survival + H-var + H-ray**
(all three OPEN), with floor `fl_j = ρ_j^(2M_j+side_j) v_j`. -/
theorem expr_normalized_anchor_of_windowSurvival_hvar_hray (tr : ExprAnchorTrajectory)
    (c0 theta delta : Q') (a : Nat) (ha : 1 ≤ a)
    (h0 : (0 : Q') < theta) (h1 : theta ≤ 1)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) (hc1 : (1 : Q') ≤ c0)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : c0 ≤ Q'.ofNat (side a) * delta) (v rho : Nat → Q')
    (Hv : ExprHVar tr v) (Hr : ExprHRay tr rho) (Hw : ExprShiftedWindowSurvival tr theta) :
    ExprShiftedAnchorPackage tr delta hdelta a (exprNondegFloor tr v rho)
      (exprNondegFloor_pos tr v rho Hv Hr) :=
  expr_normalized_anchor_of_windowSurvival tr c0 theta delta a ha h0 h1 hc0 hc1 hdelta0 hdelta
    hcd (exprNondegFloor tr v rho) (exprNondegFloor_pos tr v rho Hv Hr) Hw
    (exprShiftedNondegenerate_of_hvar_hray tr v rho Hv Hr)

#print axioms exprSector_pin
#print axioms exprNorm_pin
#print axioms exprAnchorData
#print axioms exprShiftedPathAnchor
#print axioms expr_shifted_macroRatio
#print axioms expr_shifted_anchor_floor
#print axioms ExprShiftedAnchorPackage
#print axioms expr_normalized_anchor_shifted
#print axioms expr_normalized_anchor_of_windowSurvival
#print axioms expr_normalized_anchor_of_windowSurvival_hvar_hray

end YMGap.Continuum.BF4WilsonAllNomeExprShiftedAnchorPackage
