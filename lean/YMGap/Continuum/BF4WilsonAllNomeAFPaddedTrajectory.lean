/-
# An AF-calibrated padded trajectory for the shifted A03 anchor

Companion to `audits/AUDIT-AF-PADDED-TRAJECTORY-2026-10-06.md`.

1. `dyadicNomeSchedule` (`1 - w_j = 2^-(j+1)`) is NOT AF-calibrated:
   `dyadic_not_AFCalibrated : ¬ NomeScheduleAFCalibrated dyadicNomeSchedule A κ C`
   for EVERY `A κ C` (explicit witness scale, rational Archimedean bounds).
2. `afNomeSchedule`: `1 - w_j = A/(j + κ·⌊log2(j+1)⌋ + 4)` with `A = 1942/1000`
   (standard coupling normalization, see below), `κ = 51/121`, all rational;
   nome_pos/lt_one/mono and an explicit limit modulus `4·den ε` are proved, and
   `afNomeSchedule_AFCalibrated : NomeScheduleAFCalibrated afNomeSchedule A κ 4`.
3. `afPaddedZeroMomentumTrajectory`: the padded zero-momentum faces of
   `paddedZeroMomentumTrajectory` on this schedule; padding, nondegeneracy, and
   the A03 package conditional ONLY on `PathShiftedWindowSurvival`.

The schedule enters the Lean conclusions only through the carrier nome `w_j`;
no theorem consumes the calibration. It matters for the plausibility of window
survival, not for any proof here. `NomeSchedulePhysicalBox` is NOT addressed:
the repo has no concrete lattice-spacing function `a(w)`.

**Coupling conventions (reconciled 2026-10-06).** On this carrier the weight
is per Casimir unit, `w = e^{-t/4}` with heat-kernel time `t = -4 log w`.
The repo LABELS `t` as `g²` (`g² = t`, `NonpertActivityHeatKernel.lean`); that
is NOT the standard coupling. The STANDARD (Wilson-normalized, continuum action
`(1/4g²)∫F^aF^a`, SU(2) `β = 4/g²`) coupling is `g² = 2t = -8 log w`, from matching
the heat kernel `~exp(-θ²/t)` to `exp(β cos θ) ~ exp(-βθ²/2)`. The two-loop
coefficients `b0 = 11/(24π²)`, `b1 = 17/(96π⁴)` refer to the STANDARD `g²`, so the
calibrated constant is `A = 1/(16 b0 ln 2) = 24π²/(176 ln 2) = 1.94166…`
(not `1/(8 b0 ln 2) = 3.883`, which treats the label `t` as the standard `g²`;
the `A ≈ 3.883` remark in the docstring of `NomeScheduleAFCalibrated` is
superseded by this). `κ = b1/(2 b0²) = 51/121` is convention-independent.
Honest caveats: two-loop SHAPE only; `⌊log2⌋` surrogate; the offset `C = 4` is a
choice (it absorbs the Λ-parameter ratio and higher orders and fixes the box
size in units of Λ⁻¹); no concrete `a(w)`; the calibration is cosmetic for the
Lean conclusions.

No `sorry`, no axioms.
-/

import YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate

namespace YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory
open YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor
  (lg2 NomeScheduleAFCalibrated PathShiftedNondegenerate ShiftedAnchorPackage)
open YMGap.Continuum.BF4WilsonAllNomeShiftedWindowSurvival (PathShiftedWindowSurvival)
open YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate
  (PathFacesPadded paddedNondegFloor paddedNondegFloor_pos pathShiftedNondegenerate_of_padded
   path_normalized_anchor_of_windowSurvival_padded paddedZeroMomentumTrajectory)

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The dyadic schedule is not AF-calibrated -/

private theorem half_pow_num : ∀ n : Nat, (HalfPow.half^n).num = 1
  | 0 => rfl
  | n+1 => by
      show HalfPow.half.num * (HalfPow.half^n).num = 1
      rw [half_pow_num n]; rfl

private theorem half_pow_den : ∀ n : Nat, ((HalfPow.half^n).den : Int) = (2^n : Nat)
  | 0 => rfl
  | n+1 => by
      show ((HalfPow.half * HalfPow.half^n).den : Int) = (2^(n+1) : Nat)
      rw [Q'.mul_den_cast, half_pow_den n, Nat.pow_succ]
      have : (HalfPow.half.den : Int) = 2 := rfl
      rw [this]; omega

private theorem log2_succ_le (j : Nat) : Nat.log2 (j+1) ≤ j := by
  have h := (Nat.log2_lt (n := j+1) (k := j+1) (by omega)).mpr Nat.lt_two_pow_self
  omega

private theorem le_ofNat_natAbs (q : Q') : q ≤ Q'.ofNat q.num.natAbs := by
  show q.num * ((Q'.ofNat q.num.natAbs).den : Int) ≤ (q.num.natAbs : Int) * (q.den : Int)
  rw [Q'.ofNat_den_cast]
  have h1 := Int.le_natAbs (a := q.num)
  have h2 : q.num.natAbs ≤ q.num.natAbs * q.den := Nat.le_mul_of_pos_right _ (Q'.den_pos q)
  have h3 : ((q.num.natAbs * q.den : Nat) : Int) = (q.num.natAbs : Int) * (q.den : Int) :=
    Int.natCast_mul _ _
  omega

private theorem nat_choice (D K Cn : Nat) (hD : 1 ≤ D) :
    D * (2 * (D * (2 + 2*K + Cn)) + K * (2 * (D * (2 + 2*K + Cn))) + Cn) <
      2^(1 + 2 * (D * (2 + 2*K + Cn))) := by
  generalize hP : D * (2 + 2*K + Cn) = P
  have hP1 : 1 ≤ P := by
    rw [← hP]; exact Nat.le_trans hD (Nat.le_mul_of_pos_right _ (by omega))
  have hc : Cn ≤ Cn * P := Nat.le_mul_of_pos_right _ hP1
  have h1 : 2 * P + K * (2 * P) + Cn ≤ (2 + 2*K + Cn) * P := by
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm K 2 P]
    omega
  have h2 : D * (2 * P + K * (2 * P) + Cn) ≤ P * P := by
    have e : D * ((2 + 2*K + Cn) * P) = P * P := by rw [← Nat.mul_assoc, hP]
    exact Nat.le_trans (Nat.mul_le_mul_left D h1) (Nat.le_of_eq e)
  have h3 : P * P < 2^P * 2^P :=
    Nat.mul_lt_mul_of_lt_of_le Nat.lt_two_pow_self (Nat.le_of_lt Nat.lt_two_pow_self)
      (Nat.two_pow_pos _)
  have h4 : 2^P * 2^P < 2^(1 + 2*P) := by
    rw [← Nat.pow_add, show 1 + 2*P = (P + P) + 1 by omega, Nat.pow_succ]
    have := Nat.two_pow_pos (P+P)
    omega
  omega

/-- Core of the dyadic failure: for `j = 2·den(A)·(2 + 2|κ.num| + |C.num|)`,
`(j + κ lg2 j + C)·2^-(j+1) < A`. -/
theorem dyadic_af_core (A kappa C : Q')
    (h : (0 : Q') < A ∧ ∀ j : Nat,
      (Q'.ofNat j + kappa * lg2 j + -C) * ((1 : Q') - ((1 : Q') - HalfPow.half^(1+j))) ≤ A ∧
      A ≤ (Q'.ofNat j + kappa * lg2 j + C) * ((1 : Q') - ((1 : Q') - HalfPow.half^(1+j)))) :
    False := by
  obtain ⟨hA, hall⟩ := h
  let K := kappa.num.natAbs
  let Cn := C.num.natAbs
  let D := A.den
  let j := 2 * (D * (2 + 2*K + Cn))
  have hup := (hall j).2
  have hh0 : (0 : Q') ≤ HalfPow.half^(1+j) := by
    show (0 : Int) * _ ≤ (HalfPow.half^(1+j)).num * 1
    rw [half_pow_num]; omega
  have heq : (1 : Q') - ((1 : Q') - HalfPow.half^(1+j)) ≈ HalfPow.half^(1+j) :=
    poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0))))) (.var 0) (by decide)
      (fun _ => HalfPow.half^(1+j))
  -- X ≤ ofNat N
  have hL : Nat.log2 (j+1) ≤ j := log2_succ_le j
  have hk : kappa * lg2 j ≤ Q'.ofNat K * lg2 j :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (le_ofNat_natAbs kappa)
      (by show (0 : Int) * 1 ≤ (Nat.log2 (j+1) : Int) * 1; omega)
  have hk2 : Q'.ofNat K * lg2 j ≤ Q'.ofNat (K * j) := by
    show ((K : Int) * (Nat.log2 (j+1) : Int)) * ((Q'.ofNat (K*j)).den : Int) ≤
      ((K * j : Nat) : Int) * ((Q'.ofNat K * lg2 j).den : Int)
    have eL : ((lg2 j).den : Int) = 1 := Q'.ofNat_den_cast _
    rw [Q'.mul_den_cast, Q'.ofNat_den_cast, Q'.ofNat_den_cast, eL]
    have := Nat.mul_le_mul_left K hL
    have e : ((K * j : Nat) : Int) = (K : Int) * (j : Int) := Int.natCast_mul _ _
    have e2 : ((K * Nat.log2 (j+1) : Nat) : Int) = (K : Int) * (Nat.log2 (j+1) : Int) :=
      Int.natCast_mul _ _
    omega
  have hX : Q'.ofNat j + kappa * lg2 j + C ≤ Q'.ofNat (j + K*j + Cn) := by
    have s1 : Q'.ofNat j + kappa * lg2 j + C ≤ Q'.ofNat j + Q'.ofNat (K*j) + C :=
      Q'.add_le_add_right _ _ _ (Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _ hk hk2))
    have s2 : Q'.ofNat j + Q'.ofNat (K*j) + C ≤ Q'.ofNat j + Q'.ofNat (K*j) + Q'.ofNat Cn :=
      Q'.add_le_add_left _ _ _ (le_ofNat_natAbs C)
    have s3 : Q'.ofNat j + Q'.ofNat (K*j) + Q'.ofNat Cn ≤ Q'.ofNat (j + K*j + Cn) := by
      show (((j : Int) * ((Q'.ofNat (K*j)).den : Int) + ((K*j : Nat) : Int) * ((Q'.ofNat j).den : Int))
          * ((Q'.ofNat Cn).den : Int) + (Cn : Int) * ((Q'.ofNat j + Q'.ofNat (K*j)).den : Int))
          * ((Q'.ofNat (j + K*j + Cn)).den : Int) ≤
        ((j + K*j + Cn : Nat) : Int) * ((Q'.ofNat j + Q'.ofNat (K*j) + Q'.ofNat Cn).den : Int)
      simp only [Q'.add_den_cast, Q'.ofNat_den_cast]
      have e : ((K * j : Nat) : Int) = (K : Int) * (j : Int) := Int.natCast_mul _ _
      omega
    exact Q'.le_trans' _ _ _ s1 (Q'.le_trans' _ _ _ s2 s3)
  have hfin : A ≤ Q'.ofNat (j + K*j + Cn) * HalfPow.half^(1+j) :=
    Q'.le_trans' _ _ _ hup (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ heq))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hX hh0))
  have hAn := Q'.num_pos_of_pos hA
  have hint : A.num * ((Q'.ofNat (j + K*j + Cn) * HalfPow.half^(1+j)).den : Int) ≤
      (Q'.ofNat (j + K*j + Cn) * HalfPow.half^(1+j)).num * (A.den : Int) := hfin
  rw [Q'.mul_den_cast, Q'.ofNat_den_cast, half_pow_den, Q'.mul_num_cast, half_pow_num,
    Int.one_mul, Int.mul_one] at hint
  have hc := nat_choice D K Cn (Q'.den_pos A)
  have hpow : (1 : Int) * ((2^(1+j) : Nat) : Int) ≤ A.num * ((2^(1+j) : Nat) : Int) :=
    Int.mul_le_mul_of_nonneg_right (by omega) (Int.natCast_nonneg _)
  have hc' : (j + K*j + Cn) * A.den < 2^(1+j) := by
    rw [Nat.mul_comm]; exact hc
  have hc'' : (((j + K*j + Cn) * A.den : Nat) : Int) < ((2^(1+j) : Nat) : Int) :=
    Int.ofNat_lt.mpr hc'
  rw [Int.natCast_mul] at hc''
  rw [Int.one_mul] at hpow
  have hofn : (Q'.ofNat (j + K*j + Cn)).num = ((j + K*j + Cn : Nat) : Int) := rfl
  rw [hofn] at hint
  omega

theorem dyadic_not_AFCalibrated (A kappa C : Q') :
    ¬ NomeScheduleAFCalibrated dyadicNomeSchedule A kappa C :=
  fun h => dyadic_af_core A kappa C h

/-! ## 2. A concrete AF-calibrated rational schedule -/

/-- `121·D_j` for `D_j = j + (51/121) log2(j+1) + 4`. -/
def afE (j : Nat) : Nat := 121 * j + 51 * Nat.log2 (j+1) + 484
theorem afE_pos (j : Nat) : 0 < 1000 * afE j := by unfold afE; omega
/-- `A = 1942/1000 ≈ 1/(16 b0 ln 2) = 24π²/(176 ln 2) = 1.941659…` (two-loop SU(2),
STANDARD coupling `g² = -8 log w = 2t`; carrier heat-kernel time `t = -4 log w`).
Precision: `1.942 - 1.9416585 = 3.4·10⁻⁴` (relative `1.8·10⁻⁴`). -/
def afA : Q' := Q'.mkPos 1942 1000 (by decide)
/-- `κ = b1/(2 b0²) = 51/121` (SU(2), exact). -/
def afKappa : Q' := Q'.mkPos 51 121 (by decide)
/-- Offset `C = 4 > A`, so `w_0 = 1 - A/4 = 0.5145 ∈ (0,1)` (a choice; see header). -/
def afC : Q' := 4
/-- `1 - w_j = A/D_j = 234982/(1000·121·D_j)` (`234982 = 1942·121`). -/
def afGap (j : Nat) : Q' := Q'.mkPos 234982 (1000 * afE j) (afE_pos j)

theorem afGap_den (j : Nat) : (afGap j).den = 1000 * afE j := by
  unfold afGap; rw [Q'.mkPos_den]

theorem afGap_pos (j : Nat) : (0 : Q') < afGap j := by
  show (0 : Int) * ((afGap j).den : Int) < 234982 * 1
  rw [Int.zero_mul]; decide

theorem afGap_lt_one (j : Nat) : afGap j < (1 : Q') := by
  show (234982 : Int) * 1 < 1 * ((afGap j).den : Int)
  rw [afGap_den]; unfold afE; omega

private theorem log2_succ_mono (j : Nat) : Nat.log2 (j+1) ≤ Nat.log2 (j+1+1) := by
  rw [Nat.le_log2 (by omega)]
  exact Nat.le_trans (Nat.log2_self_le (by omega)) (by omega)

theorem afGap_anti (j : Nat) : afGap (j+1) ≤ afGap j := by
  show (234982 : Int) * ((afGap j).den : Int) ≤ 234982 * ((afGap (j+1)).den : Int)
  rw [afGap_den, afGap_den]; unfold afE
  have := log2_succ_mono j
  omega

/-- Exact calibration: `D_j · (1 - w_j) ≈ A`. -/
theorem afDen_gap (j : Nat) :
    (Q'.ofNat j + afKappa * lg2 j + afC) * afGap j ≈ afA := by
  show ((Q'.ofNat j + afKappa * lg2 j + afC) * afGap j).num * (afA.den : Int) =
    afA.num * (((Q'.ofNat j + afKappa * lg2 j + afC) * afGap j).den : Int)
  rw [Q'.mul_den_cast, Q'.add_den_cast, Q'.add_den_cast, Q'.mul_den_cast, afGap_den]
  simp only [Q'.mul_num_cast, Q'.add_num_cast]
  rw [Q'.mul_den_cast, Q'.add_den_cast, Q'.mul_den_cast]
  have e1 : ((Q'.ofNat j).den : Int) = 1 := Q'.ofNat_den_cast j
  have e2 : ((lg2 j).den : Int) = 1 := Q'.ofNat_den_cast _
  have e3 : (afKappa.den : Int) = 121 := rfl
  have e4 : (afC.den : Int) = 1 := rfl
  have e5 : (afA.den : Int) = 1000 := rfl
  have n1 : (Q'.ofNat j).num = (j : Int) := rfl
  have n2 : (lg2 j).num = (Nat.log2 (j+1) : Int) := rfl
  have n3 : afKappa.num = 51 := rfl
  have n4 : afC.num = 4 := rfl
  have n5 : (afGap j).num = 234982 := rfl
  have n6 : afA.num = 1942 := rfl
  rw [e1, e2, e3, e4, e5, n1, n2, n3, n4, n5, n6]
  unfold afE
  omega

theorem afGap_le_of_modulus (eps : Q') (he : (0 : Q') < eps) (j : Nat) (hj : 4 * eps.den ≤ j) :
    afGap j ≤ eps := by
  have hn := Q'.num_pos_of_pos he
  show (234982 : Int) * (eps.den : Int) ≤ eps.num * ((afGap j).den : Int)
  rw [afGap_den]
  have h1 : ((1000 * afE j : Nat) : Int) ≤ eps.num * ((1000 * afE j : Nat) : Int) :=
    by have := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ eps.num by omega)
         (show (0 : Int) ≤ ((1000 * afE j : Nat) : Int) by omega)
       rwa [Int.one_mul] at this
  have h2 : (234982 : Int) * (eps.den : Int) ≤ 1000 * (afE j : Int) := by
    unfold afE; omega
  omega

private theorem af_one_sub_lt_one (r : Q') (hr : (0 : Q') < r) : (1 : Q') - r < (1 : Q') := by
  have hn := Q'.num_pos_of_pos hr
  change (1 + -r).num * ((1 : Q').den : Int) < (1 : Q').num * ((1 + -r).den : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.neg_den]
  change (1 * (r.den : Int) + -r.num * 1) * 1 < 1 * (1 * (r.den : Int))
  simp only [Int.one_mul, Int.mul_one]
  omega

private theorem af_one_sub_le {a b : Q'} (h : a ≤ b) : (1 : Q') - b ≤ (1 : Q') - a :=
  Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg h)

/-- The AF-calibrated schedule `w_j = 1 - A/(j + κ⌊log2(j+1)⌋ + 4)`. -/
def afNomeSchedule : NomeSchedule where
  nome := fun j => (1 : Q') - afGap j
  nome_pos := fun j => HKPos.one_sub_pos (afGap_lt_one j)
  nome_lt_one := fun j => af_one_sub_lt_one _ (afGap_pos j)
  nome_mono := fun j => af_one_sub_le (afGap_anti j)
  limitModulus := fun eps => 4 * eps.den
  nome_limit := fun eps he j hj => af_one_sub_le (afGap_le_of_modulus eps he j hj)

private theorem af_one_sub_one_sub (g : Q') : (1 : Q') - ((1 : Q') - g) ≈ g :=
  poly_identity_of_normal_eq
    (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0))))) (.var 0) (by decide)
    (fun _ => g)

/-- **AF calibration holds** with `A = 1942/1000` (standard `g² = -8 log w`), `κ = 51/121`, `C = 4`. -/
theorem afNomeSchedule_AFCalibrated : NomeScheduleAFCalibrated afNomeSchedule afA afKappa afC := by
  refine ⟨by decide, fun j => ⟨?_, ?_⟩⟩
  · have hg : (0 : Q') ≤ afGap j := Q'.le_of_lt (afGap_pos j)
    have hX : Q'.ofNat j + afKappa * lg2 j + -afC ≤ Q'.ofNat j + afKappa * lg2 j + afC :=
      Q'.add_le_add_left _ _ _ (by decide)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (af_one_sub_one_sub (afGap j))))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hX hg)
        (Q'.le_of_eqv (afDen_gap j)))
  · exact Q'.ge_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (af_one_sub_one_sub (afGap j))) (afDen_gap j))

/-! ## 3. The AF-calibrated padded trajectory -/

/-- Same faces/coefficients/radius as `paddedZeroMomentumTrajectory`
(all faces of `spatialFaces (side_j²)`, unit coefficients, `M_j = side_j`),
on the AF-calibrated schedule. -/
def afPaddedZeroMomentumTrajectory : DyadicSmoothedTrajectory :=
  { paddedZeroMomentumTrajectory with schedule := afNomeSchedule }

theorem afPaddedZeroMomentum_schedule :
    afPaddedZeroMomentumTrajectory.schedule = afNomeSchedule := rfl

theorem afPaddedZeroMomentum_AFCalibrated :
    NomeScheduleAFCalibrated afPaddedZeroMomentumTrajectory.schedule afA afKappa afC :=
  afNomeSchedule_AFCalibrated

theorem afPaddedZeroMomentum_padded : PathFacesPadded afPaddedZeroMomentumTrajectory :=
  fun _ _ hp => hp

theorem afPaddedZeroMomentum_nondegenerate :
    PathShiftedNondegenerate afPaddedZeroMomentumTrajectory
      (paddedNondegFloor afPaddedZeroMomentumTrajectory) :=
  pathShiftedNondegenerate_of_padded _ afPaddedZeroMomentum_padded

/-- **A03 package on the AF-calibrated padded trajectory, conditional ONLY on
`PathShiftedWindowSurvival`** (plus scalar choices). -/
theorem af_path_normalized_anchor_of_windowSurvival
    (c0 theta delta : Q') (a : Nat) (ha : 1 ≤ a)
    (h0 : (0 : Q') < theta) (h1 : theta ≤ 1)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) (hc1 : (1 : Q') ≤ c0)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : c0 ≤ Q'.ofNat (side a) * delta)
    (Hw : PathShiftedWindowSurvival afPaddedZeroMomentumTrajectory theta) :
    ShiftedAnchorPackage afPaddedZeroMomentumTrajectory delta hdelta a
      (paddedNondegFloor afPaddedZeroMomentumTrajectory)
      (paddedNondegFloor_pos afPaddedZeroMomentumTrajectory) :=
  path_normalized_anchor_of_windowSurvival_padded _ c0 theta delta a ha h0 h1 hc0 hc1
    hdelta0 hdelta hcd afPaddedZeroMomentum_padded Hw

/-- `θ = 1/2`. -/
def afHalf : Q' := Q'.mkPos 1 2 (by decide)

/-- Concrete scalars: window survival with `θ = 1/2` gives the package with
`c0 = 2`, `a = 2`, `δ = 1/2`, i.e. `κ = (1/2)^4`. -/
theorem af_path_normalized_anchor_of_halfSurvival
    (Hw : PathShiftedWindowSurvival afPaddedZeroMomentumTrajectory afHalf) :
    ShiftedAnchorPackage afPaddedZeroMomentumTrajectory afHalf (by decide) 2
      (paddedNondegFloor afPaddedZeroMomentumTrajectory)
      (paddedNondegFloor_pos afPaddedZeroMomentumTrajectory) :=
  af_path_normalized_anchor_of_windowSurvival 2 afHalf afHalf 2 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) Hw

end YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory

#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.dyadic_af_core
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.dyadic_not_AFCalibrated
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afE
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afA
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afKappa
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afC
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afGap
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afGap_den
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afGap_pos
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afGap_lt_one
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afGap_anti
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afDen_gap
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afGap_le_of_modulus
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afNomeSchedule
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afNomeSchedule_AFCalibrated
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afPaddedZeroMomentumTrajectory
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afPaddedZeroMomentum_schedule
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afPaddedZeroMomentum_AFCalibrated
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afPaddedZeroMomentum_padded
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afPaddedZeroMomentum_nondegenerate
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.af_path_normalized_anchor_of_windowSurvival
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.afHalf
#print axioms YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory.af_path_normalized_anchor_of_halfSurvival
