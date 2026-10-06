/-
# Explicit dyadic smoothed-coherent trajectory and the two-hypothesis A03 compiler

Trajectory data (P6 groundwork), all on the EXISTING all-nome completed Wilson
carrier:

* `side j = 2^j` (the existing `BF4DyadicWilsonSquare.side`);
* smoothing radius `M_j = m * side j` for an explicit positive factor `m`;
* width `trajWidth j = side j * side j + 1`, so `side j < width_j` and
  `width_j / side_j > side_j`;
* an ABSTRACT nome schedule `w_j` (`NomeSchedule`): positive, below one,
  nondecreasing, with an explicit modulus for `w_j -> 1`. No
  asymptotic-freedom formula is hardcoded; its physical justification is the
  OPEN named Prop `NomeScheduleAFJustified`, which nothing here consumes;
* an abstract family schedule (distinct spatial faces at width `width_j`,
  positive coefficient mass); the smoothed coherent state `Y_j` of P3.

Conditional compiler `path_macro_conclusion`: from exactly two path-uniform
OPEN hypotheses,

  H1  `PathEpsBound tr c0`: `SmoothedCoherentEpsBound (M_j, side_j, c0)` for all j,
  H2  `PathFamilyRadiusSurvival tr theta`: `FamilyRadiusSurvival (M_j, theta)`
      for all j,

plus purely scalar side conditions on the chosen constants, every scale
`j >= a` gets the SAME macro ratio `kappa = (1-delta)^(2^a)` (the line-132
`hratio` shape for `Y_j`) and the scale-uniform physical-time floor
`kappa^i * theta * B(x_j,x_j) <= R_j(i * side j)` (time `i` in units where
`spacing * side = 1`). The macro ratio uses H1 only; H2 is used only for the
floor relative to the unsmoothed family.

The existing dyadic-unit A03 consumer
(`BF4WilsonAllNomeDyadicNormalizedMacroRatio.normalizedAnchorResponse_block_floor`)
is hard-wired to `dyadicUnitExcitation`, not `Y_j`; feeding it needs the
precisely named extra Prop `PathUnitRatioBridge`. The B04l changing-nome
interface lives on the physical cutoff cube carrier; `trajectoryDynamicFamily`
instantiates its nome/spacing slots with this trajectory, but its contraction
slot is only produced by `completedSectorContraction` for `w <= 1/2`, and
`nomeSchedule_eventually_not_le_half` shows every schedule here eventually
leaves that range.

Even-compiler generalization: `macro_ratio_of_twoStep_block_general` replaces
the fixed `half` of `macro_ratio_of_block_energy` by `(1-delta)^k` for any
`L t <= delta < 1`, so the constant approaches `e^(-c)`.
-/

import YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen
import YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedMacroRatio
import YMGap.Continuum.BF4WilsonAllNomeWindowBudgetRateScreen
import YMGap.Continuum.AFRateCalibration
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity (varianceFloor)
open YMGap.Continuum.BF4DyadicWilsonSquare
  (side side_positive spacing spacing_positive spacingModulus spacing_small)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion completedInner completedInner_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance (familyExcitation)
open YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState
  (smoothedCoherentVector smoothedResponse smoothedEnergy SmoothedMacroRatio
   SmoothedCoherentEpsBound smoothedNormFloor smoothedNormFloor_positive
   smoothedCoherent_norm_floor smoothedCoherent_orthogonal)
open YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen
  (response_odd_jensen FamilyRadiusSurvival SmoothedCoherentNonDegradingFloor
   smoothedCoherent_norm_ge_family_response smoothed_macroRatio_of_epsBound_odd
   smoothedFloor_of_familyRadiusSurvival)
open YMGap.Continuum.BF4WilsonAllNomeEvenResponseJensen (response_even_jensen)
open YMGap.Continuum.BF4WilsonAllNomeCompletedLogConvexity (macro_ratio_of_survival_floor)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)
local infix:50 " ≈ " => Q'.eqv

/-! ## Scalar helpers (local copies of the standard private lemmas) -/

private theorem tr_ofNat_pos (L : Nat) (hL : 0 < L) : (0 : Q') < Q'.ofNat L := by
  change (0 : Int)*1 < (L : Int)*1
  simp only [Int.mul_one]
  omega

private theorem tr_one_le_ofNat (L : Nat) (hL : 0 < L) : (1 : Q') ≤ Q'.ofNat L := by
  change (1 : Int)*1 ≤ (L : Int)*1
  simp only [Int.mul_one]
  omega

private theorem tr_ofNat_mul (a b : Nat) :
    Q'.ofNat (a*b) ≈ Q'.ofNat a * Q'.ofNat b := by
  have hd1 : ((Q'.ofNat a * Q'.ofNat b).den : Int) = 1 := rfl
  have hd2 : ((Q'.ofNat (a*b)).den : Int) = 1 := rfl
  show ((a*b : Nat) : Int) * ((Q'.ofNat a * Q'.ofNat b).den : Int)
    = (((a : Nat) : Int) * ((b : Nat) : Int)) * ((Q'.ofNat (a*b)).den : Int)
  rw [hd1, hd2]
  push_cast
  omega

private theorem tr_qpow_eqv_pow (y : Q') : ∀ n, (RGTransport.qpow y n).eqv (y^n)
  | 0 => Q'.eqv_refl _
  | n+1 => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ y (tr_qpow_eqv_pow y n))
      (Q'.mul_comm_eqv _ _)

private theorem tr_scale_rational (c q : Q') : RCscale c (Rq q) = Rq (c*q) := by
  rw [RCscale_mk]
  exact Quotient.sound (CRealAlg.ofQ'_mul c q).symm

private theorem tr_response_lower (r : Q') (norm response : RC)
    (h : RCle (RCsub norm response) (RCscale r norm)) :
    RCle (RCscale (1-r) norm) response := by
  revert h
  refine Quotient.inductionOn₂ norm response ?_
  intro N F h epsilon he
  obtain ⟨index, hN⟩ := h epsilon he
  refine ⟨index, fun k hk => ?_⟩
  have hneg := Q'.add_le_add_left (N.approx k) _ _ (Q'.neg_le_neg_add (hN k hk))
  change (1-r)*N.approx k ≤ F.approx k + epsilon
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))
      (.add (.var 1) (.neg (.mul (.var 0) (.var 1)))) (by decide)
      (fun | 0 => r | _ => N.approx k)))
    (Q'.le_trans' _ _ _ hneg (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.add (.var 0) (.add (.neg (.add (.var 0) (.neg (.var 1)))) (.var 2)))
        (.add (.var 1) (.var 2)) (by decide)
        (fun | 0 => N.approx k | 1 => F.approx k | _ => epsilon))))

private theorem tr_scale_cancel {k : Q'} (hk : (0 : Q') < k) {a b : RC}
    (h : RCle (RCscale k a) (RCscale k b)) : RCle a b := by
  have h' := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos k hk)) h
  rw [RCscale_RCscale, RCscale_RCscale] at h'
  have e : Q'.recipPos k hk * k ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv k hk)
  rw [RCSignedPairBudget.scale_congr e, RCSignedPairBudget.scale_congr e,
    RCscale_one, RCscale_one] at h'
  exact h'

private theorem tr_one_sub_le {a delta : Q'} (h : a ≤ delta) :
    (1 : Q') - delta ≤ (1 : Q') - a :=
  Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg h)

/-! ## Shared Bernoulli block bound and the relative-energy-to-floor step -/

/-- `(1-delta)^k <= (1-t)^(L*k)` whenever `0 <= t < 1` and `L t <= delta < 1`. -/
theorem block_bernoulli_pow (t delta : Q') (L k : Nat) (ht0 : (0 : Q') ≤ t)
    (ht1 : t < (1 : Q')) (hdelta : delta < (1 : Q')) (hLt : Q'.ofNat L * t ≤ delta) :
    ((1 : Q') - delta)^k ≤ ((1 : Q') - t)^(L*k) := by
  have hbern := BondMovingRetuneFix.bernoulli_oneSub t ht0 (Q'.le_of_lt ht1) L
  have hblock : (1 : Q') - delta ≤ ((1 : Q') - t)^L :=
    Q'.le_trans' _ _ _ (tr_one_sub_le hLt)
      (Q'.le_trans' _ _ _ hbern (Q'.le_of_eqv (tr_qpow_eqv_pow _ L)))
  have hd0 : (0 : Q') ≤ (1 : Q') - delta := Q'.le_of_lt (HKPos.one_sub_pos hdelta)
  exact Q'.le_trans' _ _ _ (CRealLog.pow_le_pow_base _ _ hd0 hblock k)
    (Q'.le_of_eqv (FiveHolonomyPerronCutoff.pow_mul_eqv _ L k))

/-- A relative energy `L (N - F) <= delta N` (`L > 0`, `0 <= delta < 1`)
yields a floor `(1-t) N <= F` with `0 <= t < 1` and `L t <= delta`. -/
theorem floor_of_block_energy (norm resp : RC) (L : Nat) (hL : 0 < L) (delta : Q')
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hE : RCle (RCscale (Q'.ofNat L) (RCsub norm resp)) (RCscale delta norm)) :
    ∃ t : Q', (0 : Q') ≤ t ∧ t < (1 : Q') ∧ Q'.ofNat L * t ≤ delta ∧
      RCle (RCscale ((1 : Q') - t) norm) resp := by
  have hLpos := tr_ofNat_pos L hL
  let r : Q' := Q'.recipPos (Q'.ofNat L) hLpos
  have hr0 : (0 : Q') ≤ r := Q'.le_of_lt (Q'.recipPos_pos _ _)
  have hLr : Q'.ofNat L * r ≈ 1 := Q'.mul_recipPos_eqv _ _
  have hr1 : r ≤ 1 :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv r))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ r (tr_one_le_ofNat L hL) hr0)
        (Q'.le_of_eqv hLr))
  have ht0 : (0 : Q') ≤ delta * r := Q'.mul_nonneg _ _ hdelta0 hr0
  have htd : delta * r ≤ delta :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ delta hr1 hdelta0)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.one_mul_eqv delta)))
  have ht1 : delta * r < (1 : Q') := HKPos.q_lt_of_le_of_lt htd hdelta
  have hLt : Q'.ofNat L * (delta * r) ≤ delta := by
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _ ?_
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ delta hLr) (Q'.one_mul_eqv delta)))
    exact poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => Q'.ofNat L | 1 => delta | _ => r)
  have hEr := RCscale_mono hr0 hE
  rw [RCscale_RCscale, RCscale_RCscale] at hEr
  have hrL : r * Q'.ofNat L ≈ 1 := Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) hLr
  rw [RCSignedPairBudget.scale_congr hrL, RCscale_one,
    RCSignedPairBudget.scale_congr (Q'.mul_comm_eqv r delta)] at hEr
  exact ⟨delta * r, ht0, ht1, hLt, tr_response_lower (delta * r) _ _ hEr⟩

/-! ## Generalized even compiler and the odd block survival chain -/

section Completed

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- Even compiler with a FREE Bernoulli constant: `u = L*k`, `L t <= delta < 1`,
two-step floor `(1-t) R(0) <= R(2)` give `(1-delta)^k R(2u) <= R(4u)`.
`delta = 1/2` recovers `macro_ratio_of_block_energy` (`1 - 1/2 = 1/2`). -/
theorem macro_ratio_of_twoStep_block_general (x : V) (u L k : Nat) (hu : u = L*k)
    (t delta q : Q') (ht0 : (0 : Q') ≤ t) (ht1 : t < (1 : Q')) (hdelta : delta < (1 : Q'))
    (hq : (0 : Q') < q) (hLt : Q'.ofNat L * t ≤ delta)
    (hnorm : RCle (Rq q) (B x x))
    (h2 : RCle (RCscale ((1 : Q') - t) (B x x)) (B x (T 2 x))) :
    RCle (RCscale (((1 : Q') - delta)^k) (B x (T (2*u) x))) (B x (T (4*u) x)) := by
  have hrho : (0 : Q') < (1 : Q') - t := HKPos.one_sub_pos ht1
  have hpow : ((1 : Q') - delta)^k ≤ ((1 : Q') - t)^u := by
    rw [hu]
    exact block_bernoulli_pow t delta L k ht0 ht1 hdelta hLt
  have hj := response_even_jensen hw0 hw1 width x ((1 : Q') - t) q hrho hq hnorm h2 u
  have hfloor : RCle (RCscale (((1 : Q') - delta)^k) (B x x)) (B x (T (2*u) x)) :=
    RCle_trans (RCscale_scalar_mono hpow (completedInner_nonnegative hw0 hw1 x)) hj
  exact macro_ratio_of_survival_floor hw0 hw1 width x u _ q hq hnorm hfloor

/-- Energy form of the generalized even compiler:
`L (R(0) - R(2)) <= delta R(0)` gives `(1-delta)^k R(2u) <= R(4u)`. -/
theorem macro_ratio_of_twoStep_block_energy_general (x : V) (u L k : Nat) (hu : u = L*k)
    (hL : 0 < L) (delta q : Q') (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hq : (0 : Q') < q) (hnorm : RCle (Rq q) (B x x))
    (hE : RCle (RCscale (Q'.ofNat L) (RCsub (B x x) (B x (T 2 x))))
      (RCscale delta (B x x))) :
    RCle (RCscale (((1 : Q') - delta)^k) (B x (T (2*u) x))) (B x (T (4*u) x)) := by
  obtain ⟨t, ht0, ht1, hLt, h2⟩ := floor_of_block_energy _ _ L hL delta hdelta0 hdelta hE
  exact macro_ratio_of_twoStep_block_general hw0 hw1 width x u L k hu t delta q
    ht0 ht1 hdelta hq hLt hnorm h2

/-- Odd block survival chain: `L (R(0)-R(1)) <= delta R(0)`, `s = L*k` give
`((1-delta)^k)^i R(0) <= R(s*i)` for EVERY block count `i`. -/
theorem block_survival_of_oneStep_energy (x : V) (s L k : Nat) (hs : s = L*k)
    (hL : 0 < L) (delta q : Q') (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hq : (0 : Q') < q) (hnorm : RCle (Rq q) (B x x))
    (hE : RCle (RCscale (Q'.ofNat L) (RCsub (B x x) (B x (T 1 x))))
      (RCscale delta (B x x))) :
    ∀ i : Nat, RCle (RCscale ((((1 : Q') - delta)^k)^i) (B x x)) (B x (T (s*i) x)) := by
  obtain ⟨t, ht0, ht1, hLt, h1⟩ := floor_of_block_energy _ _ L hL delta hdelta0 hdelta hE
  intro i
  have hrho : (0 : Q') < (1 : Q') - t := HKPos.one_sub_pos ht1
  have hpow0 : ((1 : Q') - delta)^k ≤ ((1 : Q') - t)^s := by
    rw [hs]
    exact block_bernoulli_pow t delta L k ht0 ht1 hdelta hLt
  have hk0 : (0 : Q') ≤ ((1 : Q') - delta)^k :=
    CRealLog.pow_nonneg _ (Q'.le_of_lt (HKPos.one_sub_pos hdelta)) k
  have hpow : (((1 : Q') - delta)^k)^i ≤ ((1 : Q') - t)^(s*i) :=
    Q'.le_trans' _ _ _ (CRealLog.pow_le_pow_base _ _ hk0 hpow0 i)
      (Q'.le_of_eqv (FiveHolonomyPerronCutoff.pow_mul_eqv _ s i))
  exact RCle_trans (RCscale_scalar_mono hpow (completedInner_nonnegative hw0 hw1 x))
    (response_odd_jensen hw0 hw1 width x ((1 : Q') - t) q hrho hq hnorm h1 (s*i))

end Completed

/-! ## Trajectory data -/

/-- Abstract nome schedule: positive, below one, nondecreasing, and `w_j -> 1`
with an explicit modulus. No asymptotic-freedom formula is hardcoded. -/
structure NomeSchedule : Type where
  nome : Nat → Q'
  nome_pos : ∀ j, (0 : Q') < nome j
  nome_lt_one : ∀ j, nome j < (1 : Q')
  nome_mono : ∀ j, nome j ≤ nome (j+1)
  limitModulus : Q' → Nat
  nome_limit : ∀ epsilon : Q', (0 : Q') < epsilon →
    ∀ j, limitModulus epsilon ≤ j → (1 : Q') - epsilon ≤ nome j

private theorem tr_one_sub_lt_one (r : Q') (hr : (0 : Q') < r) : (1 : Q') - r < (1 : Q') := by
  have hn := Q'.num_pos_of_pos hr
  change (1 + -r).num * ((1 : Q').den : Int) < (1 : Q').num * ((1 + -r).den : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.neg_den]
  change (1 * (r.den : Int) + -r.num * 1) * 1 < 1 * (1 * (r.den : Int))
  simp only [Int.one_mul, Int.mul_one]
  omega

/-- Non-vacuity witness for the INTERFACE only, NOT a physical schedule:
`w_j = 1 - 2^-(j+1)`. -/
def dyadicNomeSchedule : NomeSchedule where
  nome := fun j => (1 : Q') - HalfPow.half^(1+j)
  nome_pos := fun j => HKPos.one_sub_pos
    (HKPos.q_lt_of_le_of_lt (ExpNeg.pow_half_antitone 1 j) (by decide))
  nome_lt_one := fun j => tr_one_sub_lt_one _ (HKPos.pow_pos (by decide) _)
  nome_mono := fun j => tr_one_sub_le (ExpNeg.pow_half_antitone (1+j) 1)
  limitModulus := spacingModulus
  nome_limit := fun epsilon he j hj => tr_one_sub_le
    (Q'.le_trans' _ _ _
      (show HalfPow.half^(1+j) ≤ HalfPow.half^j by
        rw [Nat.add_comm]
        exact ExpNeg.pow_half_antitone j 1)
      (spacing_small epsilon he j hj))

/-- OPEN physical justification (NOT proved; NOT consumed by any theorem here):
the schedule is a two-sided asymptotic-freedom trajectory in the sense of the
existing named interface `AFRateCalibration.AFRateModulus`, indexed by the
dyadic scale `j`. -/
def NomeScheduleAFJustified (ns : NomeSchedule) : Prop :=
  ∃ m : AFRateCalibration.AFRateModulus, ∀ j, (m.w j).eqv (ns.nome j)

/-- Smoothing radius `M_j = m * side j`. -/
def trajRadius (m j : Nat) : Nat := m * side j

/-- Width `side j ^ 2 + 1`: strictly larger than `side j`, ratio `> side j`. -/
def trajWidth (j : Nat) : Nat := side j * side j + 1

theorem trajWidth_gt_side (j : Nat) : side j < trajWidth j := by
  have hpos := side_positive j
  have h : side j * 1 ≤ side j * side j := Nat.mul_le_mul (Nat.le_refl _) hpos
  unfold trajWidth
  omega

theorem trajWidth_ratio (j : Nat) : side j * side j < trajWidth j :=
  Nat.lt_succ_self _

/-- Dyadic split `side j = side (j-a) * side a` for `a <= j`. -/
theorem side_split (a j : Nat) (h : a ≤ j) : side j = side (j-a) * side a := by
  unfold side
  rw [← Nat.pow_add]
  congr 1
  omega

/-- The explicit dyadic smoothed-coherent trajectory (data). -/
structure DyadicSmoothedTrajectory : Type where
  schedule : NomeSchedule
  radiusFactor : Nat
  radiusFactor_pos : 0 < radiusFactor
  faces : Nat → List Z4Plaq
  coeff : Nat → Z4Plaq → Q'
  faces_spatial : ∀ j p, p ∈ faces j → p ∈ spatialFaces (trajWidth j)
  faces_nodup : ∀ j, (faces j).Nodup
  coeff_mass_pos : ∀ j,
    (0 : Q') < listQSum (fun face => coeff j face * coeff j face) (faces j)

namespace DyadicSmoothedTrajectory

variable (tr : DyadicSmoothedTrajectory)

/-- `M_j`. -/
def radius (j : Nat) : Nat := trajRadius tr.radiusFactor j

/-- Unsmoothed family vector `x_j` at scale `j`. -/
def familyVector (j : Nat) :
    Completion (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j) :=
  Subtype.val (familyExcitation (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (trajWidth j) (tr.faces j) (tr.coeff j) (tr.faces_spatial j))

/-- Smoothed coherent state `Y_j = Y_{M_j}` at scale `j`. -/
def state (j : Nat) :
    Completion (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j) :=
  smoothedCoherentVector (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (trajWidth j) (tr.faces j) (tr.coeff j) (tr.faces_spatial j) (tr.radius j)

/-- `R_j(n) = B(Y_j, T(n) Y_j)`. -/
def response (j n : Nat) : RC :=
  smoothedResponse (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (trajWidth j) (tr.faces j) (tr.coeff j) (tr.faces_spatial j) (tr.radius j) n

/-- `B(x_j, x_j)`. -/
def familyNorm (j : Nat) : RC :=
  completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (tr.familyVector j) (tr.familyVector j)

/-- The macro ratio `kappa R_j(side j) <= R_j(2 side j)` at scale `j`. -/
def MacroRatioAt (j : Nat) (kappa : Q') : Prop :=
  SmoothedMacroRatio (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (trajWidth j) (tr.faces j) (tr.coeff j) (tr.faces_spatial j) (tr.radius j) j kappa

end DyadicSmoothedTrajectory

open DyadicSmoothedTrajectory

/-! ## The two path-uniform OPEN hypotheses -/

/-- H1 (OPEN): `SmoothedCoherentEpsBound (M_j, side_j, c0)` for every scale. -/
def PathEpsBound (tr : DyadicSmoothedTrajectory) (c0 : Q') : Prop :=
  ∀ j, SmoothedCoherentEpsBound (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (trajWidth j) (tr.faces j) (tr.coeff j) (tr.faces_spatial j) (tr.radius j) j c0

/-- H2 (OPEN): `FamilyRadiusSurvival (M_j, theta)` with ONE theta for every scale. -/
def PathFamilyRadiusSurvival (tr : DyadicSmoothedTrajectory) (theta : Q') : Prop :=
  ∀ j, FamilyRadiusSurvival (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (trajWidth j) (tr.faces j) (tr.coeff j) (tr.faces_spatial j) (tr.radius j) theta

/-- H2' (OPEN, alternative): absolute `SmoothedCoherentNonDegradingFloor (M_j, v)`
with ONE v for every scale. NOT invariant under rescaling the coefficients. -/
def PathNonDegradingFloor (tr : DyadicSmoothedTrajectory) (v : Q') : Prop :=
  ∀ j, SmoothedCoherentNonDegradingFloor (tr.schedule.nome_pos j)
    (tr.schedule.nome_lt_one j) (trajWidth j) (tr.faces j) (tr.coeff j)
    (tr.faces_spatial j) (tr.radius j) v

/-- Scalar side condition linking H2 to H2' (OPEN only through `varianceFloor (w_j)`). -/
def PathVarianceMassFloor (tr : DyadicSmoothedTrajectory) (theta v : Q') : Prop :=
  ∀ j, v ≤ theta * (varianceFloor (tr.schedule.nome j) (tr.schedule.nome_pos j) *
    listQSum (fun face => tr.coeff j face * tr.coeff j face) (tr.faces j))

/-! ## Per-scale compilers -/

/-- H1 at scale `j` in the block-energy form `L * E_j <= delta * R_j(0)`. -/
theorem blockEnergy_of_pathEps (tr : DyadicSmoothedTrajectory) (c0 delta : Q') (a j : Nat)
    (haj : a ≤ j) (hc0 : c0 ≤ Q'.ofNat (side a) * delta) (H1 : PathEpsBound tr c0) :
    RCle (RCscale (Q'.ofNat (side (j-a)))
        (smoothedEnergy (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
          (trajWidth j) (tr.faces j) (tr.coeff j) (tr.faces_spatial j) (tr.radius j)))
      (RCscale delta (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
        (tr.state j) (tr.state j))) := by
  have hkpos := tr_ofNat_pos (side a) (side_positive a)
  have hN := completedInner_nonnegative (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (tr.state j)
  have hside : Q'.ofNat (side j) ≈ Q'.ofNat (side a) * Q'.ofNat (side (j-a)) := by
    rw [side_split a j haj]
    exact Q'.eqv_trans _ _ _ (tr_ofNat_mul _ _) (Q'.mul_comm_eqv _ _)
  apply tr_scale_cancel hkpos
  rw [RCscale_RCscale, RCscale_RCscale, ← RCSignedPairBudget.scale_congr hside]
  exact RCle_trans (H1 j) (RCscale_scalar_mono hc0 hN)

/-! ## The two-hypothesis conditional theorem -/

/-- H1 alone gives the SAME macro ratio `(1-delta)^(2^a)` at every scale `j >= a`. -/
theorem path_macroRatio (tr : DyadicSmoothedTrajectory) (c0 delta : Q') (a : Nat)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta) (H1 : PathEpsBound tr c0) :
    ∀ j : Nat, a ≤ j → tr.MacroRatioAt j (((1 : Q') - delta)^(side a)) := fun j haj =>
  smoothed_macroRatio_of_epsBound_odd (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (trajWidth j) (tr.faces j) (tr.coeff j)
    (tr.faces_spatial j) (tr.faces_nodup j) (tr.coeff_mass_pos j) (tr.radius j) j
    (side (j-a)) (side a) (side_split a j haj) (side_positive a) c0 delta hdelta0 hdelta hc0
    (H1 j)

/-- **P6 conditional compiler.** Along the explicit dyadic trajectory, H1
(`PathEpsBound tr c0`) and H2 (`PathFamilyRadiusSurvival tr theta`) give, at
every scale `j >= a`, (i) the SAME macro ratio `kappa = (1-delta)^(2^a)` (the
line-132 `hratio` shape for `Y_j`), and (ii) the scale-uniform physical-time
floor `kappa^i * theta * B(x_j,x_j) <= R_j(side j * i)` for every `i`.
Side conditions are scalar only: `0 <= delta < 1` and `c0 <= 2^a * delta`
(no sign condition on theta is needed). (i) uses H1 only. -/
theorem path_macro_conclusion (tr : DyadicSmoothedTrajectory) (c0 theta delta : Q') (a : Nat)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta)
    (H1 : PathEpsBound tr c0) (H2 : PathFamilyRadiusSurvival tr theta) :
    ∀ j : Nat, a ≤ j →
      tr.MacroRatioAt j (((1 : Q') - delta)^(side a)) ∧
      ∀ i : Nat, RCle (RCscale ((((1 : Q') - delta)^(side a))^i * theta) (tr.familyNorm j))
        (tr.response j (side j * i)) := by
  intro j haj
  have hw0 := tr.schedule.nome_pos j
  have hw1 := tr.schedule.nome_lt_one j
  have hs := side_split a j haj
  refine ⟨smoothed_macroRatio_of_epsBound_odd hw0 hw1 (trajWidth j) (tr.faces j) (tr.coeff j)
      (tr.faces_spatial j) (tr.faces_nodup j) (tr.coeff_mass_pos j) (tr.radius j) j
      (side (j-a)) (side a) hs (side_positive a) c0 delta hdelta0 hdelta hc0 (H1 j), ?_⟩
  intro i
  have hL : 0 < side (j-a) := side_positive (j-a)
  have hE := blockEnergy_of_pathEps tr c0 delta a j haj hc0 H1
  have hchain := block_survival_of_oneStep_energy hw0 hw1 (trajWidth j) (tr.state j)
    (side j) (side (j-a)) (side a) hs hL delta _ hdelta0 hdelta
    (smoothedNormFloor_positive hw0 hw1 (tr.faces j) (tr.coeff j) (tr.coeff_mass_pos j)
      (tr.radius j))
    (smoothedCoherent_norm_floor hw0 hw1 (trajWidth j) (tr.faces j) (tr.coeff j)
      (tr.faces_spatial j) (tr.faces_nodup j) (tr.radius j))
    hE i
  have hfloor : RCle (RCscale theta (tr.familyNorm j))
      (completedInner hw0 hw1 (tr.state j) (tr.state j)) :=
    RCle_trans (H2 j) (smoothedCoherent_norm_ge_family_response hw0 hw1 (trajWidth j)
      (tr.faces j) (tr.coeff j) (tr.faces_spatial j) (tr.radius j))
  have hk0 : (0 : Q') ≤ (((1 : Q') - delta)^(side a))^i :=
    CRealLog.pow_nonneg _ (CRealLog.pow_nonneg _ (Q'.le_of_lt (HKPos.one_sub_pos hdelta)) _) i
  have hscaled := RCscale_mono hk0 hfloor
  rw [RCscale_RCscale] at hscaled
  exact RCle_trans hscaled hchain

/-- Variant with the absolute floor H2' (rescaling-sensitive; see the audit). -/
theorem path_macro_conclusion_absolute (tr : DyadicSmoothedTrajectory) (c0 v delta : Q')
    (a : Nat) (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta)
    (H1 : PathEpsBound tr c0) (H2 : PathNonDegradingFloor tr v) :
    ∀ j : Nat, a ≤ j →
      tr.MacroRatioAt j (((1 : Q') - delta)^(side a)) ∧
      ∀ i : Nat, RCle (Rq ((((1 : Q') - delta)^(side a))^i * v)) (tr.response j (side j * i)) := by
  intro j haj
  have hw0 := tr.schedule.nome_pos j
  have hw1 := tr.schedule.nome_lt_one j
  have hs := side_split a j haj
  refine ⟨smoothed_macroRatio_of_epsBound_odd hw0 hw1 (trajWidth j) (tr.faces j) (tr.coeff j)
      (tr.faces_spatial j) (tr.faces_nodup j) (tr.coeff_mass_pos j) (tr.radius j) j
      (side (j-a)) (side a) hs (side_positive a) c0 delta hdelta0 hdelta hc0 (H1 j), ?_⟩
  intro i
  have hL : 0 < side (j-a) := side_positive (j-a)
  have hE := blockEnergy_of_pathEps tr c0 delta a j haj hc0 H1
  have hchain := block_survival_of_oneStep_energy hw0 hw1 (trajWidth j) (tr.state j)
    (side j) (side (j-a)) (side a) hs hL delta _ hdelta0 hdelta
    (smoothedNormFloor_positive hw0 hw1 (tr.faces j) (tr.coeff j) (tr.coeff_mass_pos j)
      (tr.radius j))
    (smoothedCoherent_norm_floor hw0 hw1 (trajWidth j) (tr.faces j) (tr.coeff j)
      (tr.faces_spatial j) (tr.faces_nodup j) (tr.radius j))
    hE i
  have hk0 : (0 : Q') ≤ (((1 : Q') - delta)^(side a))^i :=
    CRealLog.pow_nonneg _ (CRealLog.pow_nonneg _ (Q'.le_of_lt (HKPos.one_sub_pos hdelta)) _) i
  have hscaled := RCscale_mono hk0 (H2 j)
  rw [tr_scale_rational] at hscaled
  exact RCle_trans hscaled hchain

/-- H2 plus the scalar `PathVarianceMassFloor` gives H2'. -/
theorem pathNonDegradingFloor_of_familyRadiusSurvival (tr : DyadicSmoothedTrajectory)
    (theta v : Q') (htheta : (0 : Q') ≤ theta)
    (H2 : PathFamilyRadiusSurvival tr theta) (hv : PathVarianceMassFloor tr theta v) :
    PathNonDegradingFloor tr v := by
  intro j
  have h := smoothedFloor_of_familyRadiusSurvival (tr.schedule.nome_pos j)
    (tr.schedule.nome_lt_one j) (trajWidth j) (tr.faces j) (tr.coeff j)
    (tr.faces_spatial j) (tr.faces_nodup j) (tr.radius j) theta htheta (H2 j)
  have hle : RCle (Rq v) (Rq (theta * (varianceFloor (tr.schedule.nome j)
      (tr.schedule.nome_pos j) *
      listQSum (fun face => tr.coeff j face * tr.coeff j face) (tr.faces j)))) :=
    CReal.leEv_of_le (CReal.ofQ'_le_ofQ' (hv j))
  exact RCle_trans hle h

/-! ## Necessary screen hidden in H1 -/

/-- Any macro ratio at scale `j >= 1` is capped by the SAME carrier's fixed-nome
rate at `(w_j, width_j)`: `kappa R_j(side j) <= twoStepRate^(side(j-1)) R_j(side j)`. -/
theorem path_rate_screen (tr : DyadicSmoothedTrajectory) (kappa : Q') (j : Nat) (hj : 1 ≤ j)
    (hratio : tr.MacroRatioAt j kappa) :
    RCle (RCscale kappa (tr.response j (2 * side (j-1))))
      (RCscale ((BF4ExactSlabFixedSpatialDenseCenteredGap.twoStepRate
          (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j))^(side (j-1)))
        (tr.response j (2 * side (j-1)))) := by
  have e1 : side j = 2 * side (j-1) := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i+1 := ⟨j-1, by omega⟩
    simp only [side, Nat.add_sub_cancel, Nat.pow_succ]
    omega
  have h : RCle (RCscale kappa (tr.response j (2 * side (j-1))))
      (tr.response j (4 * side (j-1))) := by
    have h0 := hratio
    unfold DyadicSmoothedTrajectory.MacroRatioAt SmoothedMacroRatio at h0
    rw [e1, show 2 * (2 * side (j-1)) = 4 * side (j-1) by omega] at h0
    exact h0
  exact BF4WilsonAllNomeWindowBudgetRateScreen.macro_ratio_rate_screen
    (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j) (tr.state j)
    (smoothedCoherent_orthogonal (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (trajWidth j) (tr.faces j) (tr.coeff j) (tr.faces_spatial j) (tr.radius j))
    (side (j-1)) kappa h

/-! ## Existing dyadic-unit A03 consumer: needs a named bridge -/

/-- EXTRA OPEN Prop required by the dyadic-unit A03 consumer: the smoothed macro
ratio at scale `j` transfers to the line-132 `hratio` of `dyadicUnitExcitation`
on the SAME `(w_j, width_j)`. Nothing here proves it. -/
def PathUnitRatioBridge (tr : DyadicSmoothedTrajectory) (kappa kappa' : Q') : Prop :=
  ∀ j, tr.MacroRatioAt j kappa →
    leEv (mul (ofQ' kappa')
        (BF4WilsonAllNomeDyadicUnitExcitation.dyadicUnitResponse (tr.schedule.nome_pos j)
          (tr.schedule.nome_lt_one j) j (trajWidth j) (trajWidth_gt_side j) (side j)))
      (BF4WilsonAllNomeDyadicUnitExcitation.dyadicUnitResponse (tr.schedule.nome_pos j)
        (tr.schedule.nome_lt_one j) j (trajWidth j) (trajWidth_gt_side j) (2 * side j))

/-- H1 plus the named bridge feed the existing normalized-anchor block floor at
every scale `j >= a`. -/
theorem path_unit_anchor_floor (tr : DyadicSmoothedTrajectory) (c0 delta kappa' : Q') (a : Nat)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta) (hkappa' : (0 : Q') < kappa')
    (H1 : PathEpsBound tr c0)
    (Hb : PathUnitRatioBridge tr (((1 : Q') - delta)^(side a)) kappa') :
    ∀ j : Nat, a ≤ j → ∀ i : Nat,
      leEv (ofQ' (kappa'^i))
        (BF4WilsonAllNomeDyadicNormalizedBondAnchor.normalizedAnchorResponse
          (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) j (trajWidth j)
          (trajWidth_gt_side j) (i * side j)) := by
  intro j haj i
  have hratio := path_macroRatio tr c0 delta a hdelta0 hdelta hc0 H1 j haj
  exact BF4WilsonAllNomeDyadicNormalizedMacroRatio.normalizedAnchorResponse_block_floor
    (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) j (trajWidth j)
    (trajWidth_gt_side j) kappa' hkappa' (Hb j hratio) i

/-! ## B04l changing-nome interface on the physical cube carrier -/

/-- The assigned dyadic spacing `2^-j` as a physical spacing. -/
def dyadicPhysicalSpacing : PhysicalSeparatorLogRate.PhysicalSpacing where
  spacing := spacing
  spacing_pos := spacing_positive

def dyadicSpacingToZero : PhysicalSeparatorLinearTail.SpacingToZero dyadicPhysicalSpacing where
  modulus := spacingModulus
  spacing_le := spacing_small

/-- B04l's dynamic-family interface with THIS trajectory's nome and spacing; its
per-scale cube contraction is an explicit input (no producer for `w > 1/2`). -/
def trajectoryDynamicFamily (ns : NomeSchedule)
    (gap : ∀ j, BF4PhysicalCutoffVacuumSectorCylinderCompletedGap.CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (ns.nome_pos j) (ns.nome_lt_one j) 0) :
    BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorCompletedFamily 0 where
  nome := ns.nome
  nome_pos := ns.nome_pos
  nome_lt_one := ns.nome_lt_one
  transferSpacing := dyadicPhysicalSpacing
  transferSpacingToZero := dyadicSpacingToZero
  completedGap := gap

/-- EXTRA OPEN Prop required to feed B04l along this trajectory: a strict cube
contraction at EVERY scale nome `w_j` (the existing producer covers only
`w <= 1/2`). Nothing here proves it. -/
def PathCubeContraction (ns : NomeSchedule) : Prop :=
  Nonempty (∀ j, BF4PhysicalCutoffVacuumSectorCylinderCompletedGap.CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
    (ns.nome_pos j) (ns.nome_lt_one j) 0)

/-- Every nome schedule eventually leaves `w <= 1/2`, the only range where the
existing producer `completedSectorContraction` supplies B04l's contraction. -/
theorem nomeSchedule_eventually_not_le_half (ns : NomeSchedule) :
    ∀ j, ns.limitModulus (HalfPow.half * HalfPow.half) ≤ j →
      ¬ (ns.nome j ≤ HalfPow.half) := by
  intro j hj hle
  have hlim := ns.nome_limit (HalfPow.half * HalfPow.half) (by decide) j hj
  have h := Q'.le_trans' _ _ _ hlim hle
  exact absurd h (by decide)

#print axioms block_bernoulli_pow
#print axioms floor_of_block_energy
#print axioms macro_ratio_of_twoStep_block_general
#print axioms macro_ratio_of_twoStep_block_energy_general
#print axioms block_survival_of_oneStep_energy
#print axioms NomeSchedule
#print axioms dyadicNomeSchedule
#print axioms NomeScheduleAFJustified
#print axioms trajWidth_gt_side
#print axioms side_split
#print axioms DyadicSmoothedTrajectory
#print axioms PathEpsBound
#print axioms PathFamilyRadiusSurvival
#print axioms PathNonDegradingFloor
#print axioms PathVarianceMassFloor
#print axioms blockEnergy_of_pathEps
#print axioms path_macroRatio
#print axioms path_macro_conclusion
#print axioms path_macro_conclusion_absolute
#print axioms pathNonDegradingFloor_of_familyRadiusSurvival
#print axioms path_rate_screen
#print axioms PathUnitRatioBridge
#print axioms path_unit_anchor_floor
#print axioms trajectoryDynamicFamily
#print axioms PathCubeContraction
#print axioms nomeSchedule_eventually_not_le_half

end YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory
