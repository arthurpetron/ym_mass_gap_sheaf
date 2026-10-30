/-
# Scale-parameterized 4D heat-kernel torus family, matched-coupling transfer bridge, and inter-scale Schur / signed-remainder descent spine

**Labels (corrected per YM Bot audit, 2026-10-29): U(1)-true bookkeeping; NOT gap evidence.**
`InterScaleAnchoredDescentPackage` is `PathShortedGramLossBound` split at `j0` (equivalent in
content to the r44 interface via `θ = 1 - r`, `D = 0`); `InterScaleSchurRemainderStep` is NOT
connected to `tr.response`; `ir_anchor` is ASSUMED (the pilot-nome `1/4` rate at `w = 1/1024` is
an upper contraction rate, not a lower retention bound on `w_j`); `ZHKAt_pos` needs `hz`.
Companion to `r45`, `r46`, `r47`, and Milestone 447. ADDITIVE.
-/

import YMGap.RG.SchurComplementShortedDefect
import YMGap.Continuum.SU2HeatKernelTorusTransferBridge
import YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingSignedTelescope
import YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

namespace YMGap.Continuum.ScaleParameterizedTorusDescentSpine

set_option autoImplicit false

open YMGap.Constructive YMGap.Constructive.CReal
open YMGap.Continuum.RGTransport (dimQ c4 qpow)
open YMGap.Continuum.ClusterCount4DProgress (Z4Link Z4Plaq Z4Plane)
open YMGap.Continuum.Z4TorusGeometry (torusLinks torusPlaquettes)
open YMGap.Continuum.SU2HaarL1Activity (w0)
open YMGap.Continuum.SU2PolymerIdentity (incL gas)
open YMGap.Continuum.SU2ObsInsertion (ZObs ZObs_nil ZObs_eq_Xi zObs)
open YMGap.Continuum.SignedPolymerKP (Xi Xi_nil Xi_cons cpt)
open YMGap.Continuum.SU2ClusterBridge (lk_torus pA pB)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.Z4HalfTimeReflectionPartition (slabParametricKPhysicalPartition)
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
  (slabParametricKPhysicalPartition_pos slabParametricKPhysicalPartition_one_le)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime VacuumComplement)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay (timeRate)
open YMGap.Continuum.BF4WilsonStrongCouplingUniformRate (existingPilotNome)
open YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate (existingNome_allNome_strongCoupling)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule DyadicSmoothedTrajectory)
open YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor (ShiftedAnchorPackage NomeScheduleAFCalibrated)
open YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate
  (PathFacesPadded paddedNondegFloor paddedNondegFloor_pos)
open YMGap.Continuum.BF4WilsonAllNomeScaleDependentContractionInterface (ScaleDependentShiftedH1Conjecture)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afA afKappa afC afHalf afPaddedZeroMomentumTrajectory)
open YMGap.Continuum.BF4StrongCouplingClusteringBridge (even_correlator_decay)
open YMGap.Continuum.SU2HeatKernelTorusClusteringBridge (ZHK ZObsHK covHK EhatHK ZHK_pos)
open YMGap.Continuum.SU2HeatKernelTorusTransferBridge
  (backwardLag twoHandlePairing TorusSliceTraceIdentity backward_handle_le_forward_handle
   two_handle_pairing_le_forward)
open YMGap.RG.SchurComplementShortedDefect
  (VariationalLocalizationStep retentionFactor retentionProduct
   multiplicative_retention_of_nonneg_defect PathShortedGramLossBound
   shortedGramLoss_inhabits_conjecture shortedGramLoss_closes_padded_shifted_anchor
   afPadded_closed_by_shortedGramLoss)
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph (EdgeLabelling)
open YMGap.Continuum.CompactDualAllCutoffPhysicalPushforward (allCutoffPhysicalKernel)
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable (remainderObservableExpectation)
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingIteration
  (AllCutoffOriginalActionStep AllCutoffOriginalActionTrajectory)
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingIteration.AllCutoffOriginalActionTrajectory
  (Matched blockedExpectation coarseWilsonExpectation)
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingSignedTelescope
  (physicalKernelObservablePullback signedRemainderTelescope
   blockedExpectation_sub_coarseWilson_eqv_signedRemainderTelescope)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)
local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Link 1 — Parametric 4D Torus Family `𝒯_j = (2M_j, w_j, S_j)` for all `w_j ∈ (0, 1)` -/

/-- Heat-kernel 4D torus partition function `ZObs w S_trunc` on `(Z / 2M Z)⁴` at arbitrary nome `w`. -/
abbrev ZHKAt (w : Q') (M S_trunc : Nat) : Q' :=
  ZObs w S_trunc (torusLinks (2 * M)) (2 * M) (torusPlaquettes (2 * M)) []
/-- Heat-kernel 4D torus observable-inserted integral `ZObs w S_trunc` at arbitrary nome `w`. -/
abbrev ZObsHKAt (w : Q') (M S_trunc : Nat) (S : List Z4Plaq) : Q' :=
  ZObs w S_trunc (torusLinks (2 * M)) (2 * M) (torusPlaquettes (2 * M)) S
/-- Normalized χ₁ plaquette covariance on the 4D heat-kernel torus at arbitrary nome `w : Q'`. -/
abbrev covHKAt (w : Q') (M S_trunc b c d : Nat) (plane : Z4Plane) (n : Nat) : Q' :=
  let Z := ZHKAt w M S_trunc
  let Zp := ZObsHKAt w M S_trunc [pA (M := M) b c d plane] + -Z
  let Zq := ZObsHKAt w M S_trunc [pB (M := M) b c d plane n] + -Z
  let Zpq := ZObsHKAt w M S_trunc [pA (M := M) b c d plane, pB (M := M) b c d plane n] +
    -ZObsHKAt w M S_trunc [pA (M := M) b c d plane] +
    -ZObsHKAt w M S_trunc [pB (M := M) b c d plane n] + Z
  Zpq * Q'.recip Z + -((Zp * Q'.recip Z) * (Zq * Q'.recip Z))
/-- Even-lag normalized χ₁ covariance `EhatHKAt w M S_trunc b c d plane m = covHKAt ... (2m)`. -/
abbrev EhatHKAt (w : Q') (M S_trunc b c d : Nat) (plane : Z4Plane) (m : Nat) : Q' :=
  covHKAt w M S_trunc b c d plane (2 * m)

theorem ZHKAt_w0 (M S_trunc : Nat) : ZHKAt w0 M S_trunc = ZHK (M := M) S_trunc := rfl
theorem ZObsHKAt_w0 (M S_trunc : Nat) (S : List Z4Plaq) :
    ZObsHKAt w0 M S_trunc S = ZObsHK (M := M) S_trunc S := rfl
theorem covHKAt_w0 (M S_trunc b c d : Nat) (plane : Z4Plane) (n : Nat) :
    covHKAt w0 M S_trunc b c d plane n = covHK (M := M) S_trunc b c d plane n := rfl
theorem EhatHKAt_w0 (M S_trunc b c d : Nat) (plane : Z4Plane) (m : Nat) :
    EhatHKAt w0 M S_trunc b c d plane m = EhatHK (M := M) S_trunc b c d plane m := rfl

/-! ### Positivity of `coeffW` and of the 4D torus partition function for all `w > 0` -/

theorem dimQ_pos (s : Nat) : (0 : Q') < dimQ s := by
  change (0 : Int) * 1 < ((s + 1 : Nat) : Int) * 1
  rw [Int.zero_mul, Int.mul_one]; exact Int.ofNat_lt.mpr (Nat.succ_pos s)
theorem qpow_pos {w : Q'} (hw : (0 : Q') < w) : ∀ n : Nat, (0 : Q') < qpow w n
  | 0 => by show (0 : Q') < (1 : Q'); decide
  | n + 1 => Q'.mul_pos (qpow_pos hw n) hw
/-- **Strict positivity of every heat-kernel character coefficient for all `w > 0` (PROVED).** -/
theorem coeffW_pos {w : Q'} (hw : (0 : Q') < w) (s : Nat) :
    (0 : Q') < YMGap.Continuum.BondMovingStep.coeffW w s :=
  Q'.mul_pos (dimQ_pos s) (qpow_pos hw (c4 s))
private theorem torusIntegrand_zero (w : Q') (links : List Z4Link) (N : Nat) :
    ∀ P : List Z4Plaq, YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.torusIntegrand w 0 links N P =
      YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.polyOne
  | [] => rfl
  | p :: ps => by
      show YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.polyMul
        (YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.plaqWeight w links N p 0)
        (YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.torusIntegrand w 0 links N ps) = _
      rw [torusIntegrand_zero w links N ps]; rfl
theorem ZHKAt_zero_eqv_one (w : Q') (M : Nat) : (ZHKAt w M 0).eqv 1 := by
  unfold ZHKAt; rw [ZObs_nil]
  unfold YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.polyPartition; rw [torusIntegrand_zero]
  exact YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.quaternionHaar_polyOne (torusLinks (2 * M)).length
theorem ZHKAt_zero_pos (w : Q') (M : Nat) : (0 : Q') < ZHKAt w M 0 :=
  YMGap.Continuum.SU2PolymerActivityBound.pos_of_pos_le (by decide : (0 : Q') < 1)
    (Q'.ge_of_eqv (ZHKAt_zero_eqv_one w M))

/-- Character-orthogonality / spin-configuration expansion of the 4D torus partition function. -/
abbrev ZSpinHKAt (w : Q') (M S_trunc : Nat) : Q' :=
  slabParametricKPhysicalPartition w S_trunc (2 * M)
theorem ZSpinHKAt_one_le {w : Q'} (hw : (0 : Q') < w) (M S_trunc : Nat) :
    (1 : Q') ≤ ZSpinHKAt w M S_trunc :=
  slabParametricKPhysicalPartition_one_le (Q'.le_of_lt hw) S_trunc (2 * M)
theorem ZSpinHKAt_pos {w : Q'} (hw : (0 : Q') < w) (M S_trunc : Nat) :
    (0 : Q') < ZSpinHKAt w M S_trunc :=
  slabParametricKPhysicalPartition_pos (Q'.le_of_lt hw) S_trunc (2 * M)

private theorem Xi_one_le_of_nonneg_aux {α : Type} (z : α → Q') (inc : α → α → Bool) :
    ∀ (k : Nat) (l : List α), l.length ≤ k → (∀ a ∈ l, (0 : Q') ≤ z a) → (1 : Q') ≤ Xi z inc l
  | 0, l, hl, _ => by
      have hnil : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
      subst hnil; rw [Xi_nil]; exact Q'.le_refl' 1
  | _ + 1, [], _, _ => by rw [Xi_nil]; exact Q'.le_refl' 1
  | k + 1, a :: l, hl, hz => by
      have hlen : l.length ≤ k := Nat.le_of_succ_le_succ hl; rw [Xi_cons]
      have h1 : (1 : Q') ≤ Xi z inc l :=
        Xi_one_le_of_nonneg_aux z inc k l hlen (fun b hb => hz b (List.mem_cons_of_mem a hb))
      have hfilt : (1 : Q') ≤ Xi z inc (l.filter (cpt inc a)) :=
        Xi_one_le_of_nonneg_aux z inc k (l.filter (cpt inc a))
          (Nat.le_trans (List.length_filter_le _ _) hlen)
          (fun b hb => hz b (List.mem_cons_of_mem a (List.mem_filter.mp hb).1))
      have hprod : (0 : Q') ≤ z a * Xi z inc (l.filter (cpt inc a)) :=
        Q'.mul_nonneg _ _ (hz a (List.mem_cons_self ..))
          (Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1) hfilt)
      exact Q'.le_trans' _ _ _ h1
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_add_zero_eqv (Xi z inc l)))
          (Q'.add_le_add_left (Xi z inc l) 0 _ hprod))
theorem Xi_one_le_of_nonneg {α : Type} (z : α → Q') (inc : α → α → Bool)
    (l : List α) (hz : ∀ a ∈ l, (0 : Q') ≤ z a) : (1 : Q') ≤ Xi z inc l :=
  Xi_one_le_of_nonneg_aux z inc l.length l (Nat.le_refl _) hz
/-- **Positivity of `ZHKAt w M S_trunc` for arbitrary `w > 0` (PROVED).** -/
theorem ZHKAt_pos {w : Q'} (_hw : (0 : Q') < w) {M : Nat} (hM : 1 ≤ M) (S_trunc : Nat)
    (hz : ∀ γ ∈ gas (2 * M) (torusPlaquettes (2 * M)),
      (0 : Q') ≤ zObs w S_trunc (torusLinks (2 * M)) (2 * M) [] γ) :
    (0 : Q') < ZHKAt w M S_trunc :=
  YMGap.Continuum.SU2PolymerActivityBound.pos_of_pos_le
    (YMGap.Continuum.SU2PolymerActivityBound.pos_of_pos_le (by decide : (0 : Q') < 1)
      (Xi_one_le_of_nonneg _ _ _ hz))
    (Q'.ge_of_eqv (ZObs_eq_Xi w S_trunc (torusLinks (2 * M)) (2 * M)
      (torusPlaquettes (2 * M)) [] (lk_torus hM)))
theorem ZHKAt_w0_pos {M : Nat} (hM : 1 ≤ M) (S_trunc : Nat) : (0 : Q') < ZHKAt w0 M S_trunc :=
  ZHK_pos hM S_trunc

/-! ### Matched-coupling two-handle transfer bridge `TorusSliceTraceIdentityAt w` -/

/-- **Matched-coupling two-handle torus-to-semigroup trace inequality at arbitrary `w ∈ (0, 1)`.** -/
def TorusSliceTraceIdentityAt (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width M S_trunc b c d : Nat) (plane : Z4Plane)
    (y : VacuumComplement hw0 hw1 (width := width)) (cfwd cbwd : Q') : Prop :=
  ∀ m : Nat, 2 * m + 1 ≤ M →
    RCle (Rq (EhatHKAt w M S_trunc b c d plane m))
      (twoHandlePairing hw0 hw1 width cfwd cbwd M m y.val)
/-- **Matched-coupling single-correlator semigroup bridge at arbitrary `w ∈ (0, 1)`.** -/
def HeatKernelTorusSemigroupBridgeAt (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width M S_trunc b c d : Nat) (plane : Z4Plane)
    (y : VacuumComplement hw0 hw1 (width := width)) (C : Q') : Prop :=
  ∀ m : Nat, 2 * m + 1 ≤ M →
    RCle (Rq (EhatHKAt w M S_trunc b c d plane m))
      (RCscale C (completedInner hw0 hw1 y.val (completedTime hw0 hw1 (2 * m) y.val)))
theorem torusSliceTraceIdentityAt_w0 (hw0 : (0 : Q') < w0) (hw1 : w0 < (1 : Q'))
    (width M S_trunc b c d : Nat) (plane : Z4Plane)
    (y : VacuumComplement hw0 hw1 (width := width)) (cfwd cbwd : Q') :
    TorusSliceTraceIdentityAt w0 hw0 hw1 width M S_trunc b c d plane y cfwd cbwd =
      TorusSliceTraceIdentity hw0 hw1 width (M := M) S_trunc b c d plane y cfwd cbwd := rfl
/-- **Two-handle dominance along any `NomeSchedule` (`0 < w_j < 1`, PROVED).** -/
theorem schedule_backward_handle_le_forward_handle (ns : NomeSchedule) (j width M m : Nat)
    (hm : 2 * m ≤ M) (y : Completion (ns.nome_pos j) (ns.nome_lt_one j) width) :
    RCle (completedInner (ns.nome_pos j) (ns.nome_lt_one j) y
        (completedTime (ns.nome_pos j) (ns.nome_lt_one j) (backwardLag M m) y))
      (completedInner (ns.nome_pos j) (ns.nome_lt_one j) y
        (completedTime (ns.nome_pos j) (ns.nome_lt_one j) (2 * m) y)) :=
  backward_handle_le_forward_handle (ns.nome_pos j) (ns.nome_lt_one j) width hm y
/-- **Matched-coupling reduction from `TorusSliceTraceIdentityAt w` to
`HeatKernelTorusSemigroupBridgeAt w` (PROVED).** -/
theorem torusSliceTraceIdentityAt_implies_bridgeAt (w : Q')
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width M S_trunc b c d : Nat) (plane : Z4Plane)
    (y : VacuumComplement hw0 hw1 (width := width)) (cfwd cbwd : Q') (hcbwd : (0 : Q') ≤ cbwd)
    (htrace : TorusSliceTraceIdentityAt w hw0 hw1 width M S_trunc b c d plane y cfwd cbwd) :
    HeatKernelTorusSemigroupBridgeAt w hw0 hw1 width M S_trunc b c d plane y (cfwd + cbwd) :=
  fun m hm => RCle_trans (htrace m hm)
    (two_handle_pairing_le_forward hw0 hw1 width hcbwd (Nat.le_of_succ_le hm) y.val)
/-- **Matched-coupling exponential clustering on the 4D torus from `TorusSliceTraceIdentityAt w`.** -/
theorem ehatHKAt_decay_of_torusSliceTraceIdentityAt (w : Q')
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width M S_trunc b c d : Nat) (plane : Z4Plane)
    (y : VacuumComplement hw0 hw1 (width := width)) (cfwd cbwd : Q')
    (hcfwd : (0 : Q') ≤ cfwd) (hcbwd : (0 : Q') ≤ cbwd) (r : Q') (hr0 : (0 : Q') ≤ r)
    (hvac : WilsonVacuumSqContraction hw0 hw1 width r)
    (htrace : TorusSliceTraceIdentityAt w hw0 hw1 width M S_trunc b c d plane y cfwd cbwd)
    (m : Nat) (hm : 2 * m + 1 ≤ M) :
    RCle (Rq (EhatHKAt w M S_trunc b c d plane m))
      (RCscale ((cfwd + cbwd) * (r * r) ^ m) (completedInner hw0 hw1 y.val y.val)) := by
  have h1 := RCscale_mono (Q'.zero_le_add cfwd cbwd hcfwd hcbwd)
    (even_correlator_decay hw0 hw1 width r (Q'.mul_nonneg r r hr0 hr0) hvac m y)
  rw [RCscale_RCscale] at h1
  exact RCle_trans (torusSliceTraceIdentityAt_implies_bridgeAt w hw0 hw1 width M S_trunc
    b c d plane y cfwd cbwd hcbwd htrace m hm) h1

/-! ## 2. Link 2 — Inter-Scale `2M_j → M_j` (`j+1 → j`) Schur Pullback & Signed Remainder Descent -/

/-- Dyadic torus half-side `M_j = 2^(j-1)` at scale `j` (`2 * M_j = side j` for `j ≥ 1`). -/
def torusHalfSide (j : Nat) : Nat := 2 ^ (j - 1)
theorem torusHalfSide_pos (j : Nat) : 1 ≤ torusHalfSide j := Nat.pow_pos (by decide : 0 < 2)
theorem two_mul_torusHalfSide (j : Nat) (hj : 1 ≤ j) : 2 * torusHalfSide j = side j := by
  cases j with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hj)
  | succ i => show 2 * 2 ^ i = 2 ^ i * 2; exact Nat.mul_comm 2 (2 ^ i)
theorem torusHalfSide_succ (j : Nat) (hj : 1 ≤ j) :
    torusHalfSide (j + 1) = 2 * torusHalfSide j := by
  cases j with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hj)
  | succ i => show 2 ^ (i + 1) = 2 * 2 ^ i; exact Nat.mul_comm (2 ^ i) 2
theorem torusHalfSide_shift (j0 K : Nat) (hj0 : 1 ≤ j0) :
    torusHalfSide (j0 + K) = 2 ^ K * torusHalfSide j0 := by
  cases j0 with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hj0)
  | succ i =>
      have hsub : i + 1 + K - 1 = i + K := by rw [Nat.add_right_comm i 1 K]; rfl
      show 2 ^ (i + 1 + K - 1) = 2 ^ K * 2 ^ i; rw [hsub, Nat.add_comm i K, Nat.pow_add]
theorem torusHalfSide_of_le {j0 J : Nat} (hj0 : 1 ≤ j0) (hJ : j0 ≤ J) :
    torusHalfSide J = 2 ^ (J - j0) * torusHalfSide j0 := by
  have h := torusHalfSide_shift j0 (J - j0) hj0; rw [Nat.add_sub_of_le hJ] at h; exact h

/-- **Inter-scale `j+1 → j` (`2M_j → M_j`) Schur pullback + signed-remainder step.** -/
structure InterScaleSchurRemainderStep (Branch Readout : Type) where
  scale : Nat
  blockingStep : AllCutoffOriginalActionStep
  localization : VariationalLocalizationStep Branch Readout
  thetaBar : Q'
  thetaBar_nonneg : (0 : Q') ≤ thetaBar
  thetaBar_le_one : thetaBar ≤ (1 : Q')
def InterScaleSchurRemainderStep.pullbackObservable {Branch Readout : Type}
    (step : InterScaleSchurRemainderStep Branch Readout) (observable : EdgeLabelling → Q') :
    EdgeLabelling → Q' :=
  physicalKernelObservablePullback step.blockingStep observable
def InterScaleSchurRemainderStep.couplingRemainder {Branch Readout : Type}
    (step : InterScaleSchurRemainderStep Branch Readout) (observable : EdgeLabelling → Q') : Q' :=
  remainderObservableExpectation
    (allCutoffPhysicalKernel step.blockingStep.pair step.blockingStep.fineCutoff) observable
/-- **Combined inter-scale Schur defect nonnegativity and signed-remainder telescope bridge.** -/
theorem interScale_schur_and_signedRemainder_bridge {Branch Readout : Type}
    (step : InterScaleSchurRemainderStep Branch Readout) (b : Readout)
    (trajectory : AllCutoffOriginalActionTrajectory) (hmatched : Matched trajectory)
    (observable : EdgeLabelling → Q') :
    (0 : Q') ≤ step.localization.defect b ∧
    step.localization.assembledChild b ≤ step.localization.parentEff b ∧
    (blockedExpectation trajectory observable +
        -(coarseWilsonExpectation trajectory observable)).eqv
      (signedRemainderTelescope trajectory observable) :=
  ⟨step.localization.gluingDefect_nonneg b, step.localization.drop_gluingDefect_lower_bound b,
   blockedExpectation_sub_coarseWilson_eqv_signedRemainderTelescope trajectory hmatched observable⟩
/-- **Inter-scale retention descent from UV scale `J = j0 + K` down to IR anchor scale `j0`.** -/
theorem interScale_retention_descent_to_irAnchor
    (thetaBar defect E : Nat → Q') (j0 K : Nat) (hj0 : 1 ≤ j0)
    (htheta1 : ∀ n, thetaBar n ≤ (1 : Q')) (hdef : ∀ n, (0 : Q') ≤ defect n)
    (hstep : ∀ k, retentionFactor thetaBar (j0 + k) * E k + defect (j0 + k) ≤ E (k + 1)) :
    torusHalfSide (j0 + K) = 2 ^ K * torusHalfSide j0 ∧
    retentionProduct thetaBar j0 K * E 0 ≤ E K ∧
    (∃ (hw0 : (0 : Q') < existingPilotNome) (hw1 : existingPilotNome < (1 : Q')),
      (0 : Q') < timeRate ∧ timeRate < (1 : Q') ∧
      ∀ width : Nat, WilsonVacuumSqContraction hw0 hw1 width timeRate) :=
  ⟨torusHalfSide_shift j0 K hj0,
   multiplicative_retention_of_nonneg_defect thetaBar defect E htheta1 hdef j0 hstep K,
   existingNome_allNome_strongCoupling⟩

/-- **Scale-anchored inter-scale Schur descent package (`[1, j0]` IR anchor + `(j0, ∞)` UV
doubling descent).** -/
structure InterScaleAnchoredDescentPackage (tr : DyadicSmoothedTrajectory) (j0 : Nat)
    (thetaBar : Nat → Q') (defect : Nat → RC) (c0 : Q') : Prop where
  j0_pos : 1 ≤ j0
  ir_anchor : ∀ j : Nat, 1 ≤ j → j ≤ j0 →
    (0 : Q') ≤ thetaBar j ∧ RCnonneg (defect j) ∧
    RCle (RCadd (RCscale (retentionFactor thetaBar j) (tr.response j (side j))) (defect j))
      (tr.response j (side j + 1)) ∧ Q'.ofNat (side j) * thetaBar j ≤ c0
  uv_interScale_step : ∀ j : Nat, j0 < j →
    torusHalfSide j = 2 ^ (j - j0) * torusHalfSide j0 ∧
    (0 : Q') ≤ thetaBar j ∧ RCnonneg (defect j) ∧
    RCle (RCadd (RCscale (retentionFactor thetaBar j) (tr.response j (side j))) (defect j))
      (tr.response j (side j + 1)) ∧ Q'.ofNat (side j) * thetaBar j ≤ c0
theorem interScaleAnchoredDescent_implies_shortedGramLoss (tr : DyadicSmoothedTrajectory)
    (j0 : Nat) (thetaBar : Nat → Q') (defect : Nat → RC) (c0 : Q')
    (H : InterScaleAnchoredDescentPackage tr j0 thetaBar defect c0) :
    PathShortedGramLossBound tr thetaBar defect c0 := by
  intro j hj; by_cases hle : j ≤ j0
  · exact H.ir_anchor j hj hle
  · exact (H.uv_interScale_step j (Nat.gt_of_not_le hle)).2
/-- Repackaging: the ASSUMED split package yields `ScaleDependentShiftedH1Conjecture`
(name kept for stability; this is NOT an unconditional discharge). -/
theorem interScale_descent_discharges_conjecture (tr : DyadicSmoothedTrajectory)
    (j0 : Nat) (thetaBar : Nat → Q') (defect : Nat → RC) (c0 : Q') (hc0 : (1 : Q') ≤ c0)
    (H : InterScaleAnchoredDescentPackage tr j0 thetaBar defect c0) :
    ScaleDependentShiftedH1Conjecture tr c0 :=
  shortedGramLoss_inhabits_conjecture tr thetaBar defect c0 hc0
    (interScaleAnchoredDescent_implies_shortedGramLoss tr j0 thetaBar defect c0 H)
/-- Repackaging into `ShiftedAnchorPackage` from the ASSUMED split package (conditional). -/
theorem interScale_descent_closes_shifted_anchor
    (tr : DyadicSmoothedTrajectory) (j0 : Nat) (thetaBar : Nat → Q') (defect : Nat → RC)
    (c0 delta : Q') (a : Nat) (ha : 1 ≤ a) (hc0 : (1 : Q') ≤ c0)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : c0 ≤ Q'.ofNat (side a) * delta) (hpad : PathFacesPadded tr)
    (H : InterScaleAnchoredDescentPackage tr j0 thetaBar defect c0) :
    ShiftedAnchorPackage tr delta hdelta a (paddedNondegFloor tr) (paddedNondegFloor_pos tr) :=
  shortedGramLoss_closes_padded_shifted_anchor tr thetaBar defect c0 delta a ha hc0
    hdelta0 hdelta hcd hpad
    (interScaleAnchoredDescent_implies_shortedGramLoss tr j0 thetaBar defect c0 H)
/-- **Concrete closure on `afPaddedZeroMomentumTrajectory` from `InterScaleAnchoredDescentPackage`.** -/
theorem afPadded_closed_by_interScale_descent
    (j0 : Nat) (thetaBar : Nat → Q') (defect : Nat → RC)
    (H : InterScaleAnchoredDescentPackage afPaddedZeroMomentumTrajectory j0 thetaBar defect
      (Q'.ofNat 2)) :
    NomeScheduleAFCalibrated afPaddedZeroMomentumTrajectory.schedule afA afKappa afC ∧
      ShiftedAnchorPackage afPaddedZeroMomentumTrajectory afHalf (by decide) 2
        (paddedNondegFloor afPaddedZeroMomentumTrajectory)
        (paddedNondegFloor_pos afPaddedZeroMomentumTrajectory) :=
  afPadded_closed_by_shortedGramLoss thetaBar defect
    (interScaleAnchoredDescent_implies_shortedGramLoss afPaddedZeroMomentumTrajectory
      j0 thetaBar defect (Q'.ofNat 2) H)

end YMGap.Continuum.ScaleParameterizedTorusDescentSpine
