/-
# Shifted H1: the UV-suppressed anchor `T^(side_j/2) Y_j` and the A03 package

Companion to `audits/MATH-NOTE-H1-FIXED-SCALE-2026-10-05.md` §2.2 and
`audits/AUDIT-SHIFTED-H1-ANCHOR-2026-10-05.md`.

The unshifted H1 (`PathEpsBound`) asks for `side·E ≤ c0·R_Y(0)` with
`E = R_Y(0) - R_Y(1)`. It is heuristically FALSE for local plaquette families,
because the box kernel leaves UV weight `~(M+1)^(-2)` at lag 0.
The SHIFTED H1 asks the same of `x_j = T^(h_j) Y_j` with `h_j = side_j/2`.
Since `T` is symmetric and positive here, `B(T^h Y, T^n T^h Y) = R_Y(n+2h)`,
so the shifted eps involves only `R_Y(side_j)` and `R_Y(side_j+1)`:

  `PathShiftedEpsBound tr c0 :  side_j (R_j(side_j) - R_j(side_j+1)) ≤ c0 R_j(side_j)`
  (`pathShiftedEpsBound_iff_response`, for `j ≥ 1`).

Proved here:
* the shifted Fejér telescope `(M+1)·E(T^h Y_M) ≤ B(x0, T^(2h) x0)`
  (`shifted_energy_le_familyResponse`) and its exact identity
  (`shifted_energy_telescope`);
* shifted relative floor ⟹ shifted H1, and the path form from
  `PathShiftedFamilySurvival` (`pathShiftedEpsBound_of_shiftedFamilySurvival`);
* **`path_normalized_anchor_shifted`**: the full A03 normalized-anchor package
  (unit norm, block floors `κ^i`, real-time survival `κ^(i+1)`, increments) for
  the SAME normalized state `α·T^(side_j) Y_j`, from `PathShiftedEpsBound` plus
  the QUALITATIVE `PathShiftedNondegenerate tr fl`, i.e. `fl_j ≤ R_j(side_j)` with
  ANY positive `fl_j`, which may depend arbitrarily on `j`. The anchor is fed
  through `NormalizedAnchorData` (`smoothedAnchorData`, block `side_j`);
* the shifted gap screen (`path_shiftedEps_forces_rate`).

Nondegeneracy cannot be dropped. If `Y_j ∈ ker T^(side_j/2)`, the shifted H1
holds trivially (`0 ≤ 0`) while no unit-norm anchor exists. It is a fixed-scale
positivity, not a uniform estimate. All uniform analytic content sits in
`PathShiftedEpsBound`.

AF schedule Props (OPEN physics input, nothing proved about them beyond
definitions): `NomeScheduleAFCalibrated`, `NomeSchedulePhysicalBox`. Proved:
the interface witness `dyadicNomeSchedule` has `(1-w_j)·side_j = 1/2`
(`dyadicNomeSchedule_margin_side`).

No `sorry`, no axioms.
-/

import YMGap.Continuum.BF4WilsonAllNomeH1FixedScale

namespace YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4DyadicWilsonSquare (side side_positive spacing unit_side)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion completedInner completedInner_nonnegative completedInner_symm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedTime_zero completedTime_add VacuumComplement)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
  (orbitSum responseSum orbitSum_inner_left orbitSum_time)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (mixedMoment_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance (familyExcitation)
open YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState
  (smoothingWeight smoothingWeight_nonneg smoothingWeight_normalizes boxKernel timeKernel
   kernelMass timeKernel_mass boxSum_nonneg smoothedCoherentVector smoothedCoherentState
   smoothedResponse smoothedResponse_orbit_expand)
open YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen (response_le_of_le boxSum_ge_const)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory.DyadicSmoothedTrajectory
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (bondCompletedInner bondCompletedDistance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealTime (action)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (PositiveTimeValue realValue)
open YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedMacroRatio (macroGeometricRadius)
open YMGap.Continuum.BF4WilsonAllNomeGenericNormalizedAnchor
  (NormalizedAnchorData smoothedAnchorData smoothedNorm_pin pathKappa_pos)
open YMGap.Continuum.BF4WilsonAllNomeH1FixedScale
  (boxSum_shift_telescope boxSum_le_const WilsonVacuumRayleighRate
   oneStep_energy_ge_of_rayleighRate)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)
local infix:50 " ≈ " => Q'.eqv

/-! ## Local helpers (copies of standard private lemmas) -/

private theorem sh_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
      (Q'.eqv_of_eq (Q'.zero_add' (A.approx n)))))

private theorem sh_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem sh_sub_add_cancel (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
      (by decide) (fun | 0 => A.approx n | _ => B'.approx n)))

private theorem sh_sub_le_self {a b : RC} (hb : RCnonneg b) : RCle (RCsub a b) a := by
  have h := RCadd_le_add (RCle_refl (RCsub a b)) hb
  rwa [sh_add_zero, sh_sub_add_cancel] at h

private theorem sh_sub_nonnegative_of_le {a b : RC} (h : RCle b a) :
    RCnonneg (RCsub a b) := by
  have h' := RCadd_le_add h (RCle_refl (RCneg b))
  change RCle (RCsub b b) (RCsub a b) at h'
  rwa [sh_sub_self] at h'

private theorem sh_scale_rational (c q : Q') : RCscale c (Rq q) = Rq (c*q) := by
  rw [RCscale_mk]
  exact Quotient.sound (CRealAlg.ofQ'_mul c q).symm

private theorem sh_scale_sub (a b : Q') (x : RC) :
    RCscale (a + -b) x = RCsub (RCscale a x) (RCscale b x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => a | 1 => b | _ => X.approx n)))

private theorem sh_ofNat_pos (L : Nat) (hL : 0 < L) : (0 : Q') < Q'.ofNat L := by
  change (0 : Int)*1 < (L : Int)*1
  simp only [Int.mul_one]
  omega

private theorem sh_ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  change (0 : Int)*1 ≤ (n : Int)*1
  simp only [Int.mul_one]
  omega

private theorem sh_ofNat_le_succ (n : Nat) : Q'.ofNat n ≤ Q'.ofNat (n+1) := by
  change (n : Int)*1 ≤ ((n+1 : Nat) : Int)*1
  simp only [Int.mul_one]
  omega

private theorem sh_ofNat_mul (a b : Nat) :
    Q'.ofNat (a*b) ≈ Q'.ofNat a * Q'.ofNat b := by
  have hd1 : ((Q'.ofNat a * Q'.ofNat b).den : Int) = 1 := rfl
  have hd2 : ((Q'.ofNat (a*b)).den : Int) = 1 := rfl
  show ((a*b : Nat) : Int) * ((Q'.ofNat a * Q'.ofNat b).den : Int)
    = (((a : Nat) : Int) * ((b : Nat) : Int)) * ((Q'.ofNat (a*b)).den : Int)
  rw [hd1, hd2]
  push_cast
  omega

private theorem sh_pow_one (q : Q') : q^1 ≈ q := by
  change q * 1 ≈ q
  exact Q'.mul_one_eqv q

private theorem sh_scale_cancel {k : Q'} (hk : (0 : Q') < k) {a b : RC}
    (h : RCle (RCscale k a) (RCscale k b)) : RCle a b := by
  have h' := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos k hk)) h
  rw [RCscale_RCscale, RCscale_RCscale] at h'
  have e : Q'.recipPos k hk * k ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv k hk)
  rw [RCSignedPairBudget.scale_congr e, RCSignedPairBudget.scale_congr e,
    RCscale_one, RCscale_one] at h'
  exact h'

private theorem sh_le_total (a b : Q') : a ≤ b ∨ b ≤ a := by
  rcases Int.le_total (a.num * (b.den : Int)) (b.num * (a.den : Int)) with h | h
  · exact Or.inl h
  · exact Or.inr h

private theorem sh_rational_nonpos {x : Q'} (h : RCle (Rq x) RCzero) : x ≤ (0 : Q') := by
  refine Q'.le_of_forall_pos_add (fun epsilon he => ?_)
  obtain ⟨index, hN⟩ := h epsilon he
  exact hN index (Nat.le_refl index)

private theorem sh_nonpos_of_mul_nonpos {x q : Q'} (hq : (0 : Q') < q)
    (h : x*q ≤ (0 : Q')) : x ≤ (0 : Q') := by
  have hr := Q'.le_of_lt (Q'.recipPos_pos q hq)
  have h1 := Q'.mul_le_mul_of_nonneg_right _ _ (Q'.recipPos q hq) h hr
  have hx : x*q*Q'.recipPos q hq ≈ x :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 0) (.mul (.var 1) (.var 2))) (by decide)
        (fun | 0 => x | 1 => q | _ => Q'.recipPos q hq))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left x _ _ (Q'.mul_recipPos_eqv q hq))
        (poly_identity_of_normal_eq (.mul (.var 0) (.const 1)) (.var 0) (by decide)
          (fun _ => x)))
  have h0 : (0 : Q')*Q'.recipPos q hq ≈ 0 := Q'.zero_mul_eqv _
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hx) (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv h0))

private theorem sh_coeff_le_of_scale_le {a b q : Q'} (hq : (0 : Q') < q) {N : RC}
    (hN : RCle (Rq q) N) (h : RCle (RCscale a N) (RCscale b N)) : a ≤ b := by
  rcases sh_le_total a b with hab | hba
  · exact hab
  · have hd : (0 : Q') ≤ a + -b := by
      have h' := Q'.add_le_add_right _ _ (-b) hba
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv b)) h'
    have hlow := RCscale_mono hd hN
    rw [sh_scale_rational, sh_scale_sub] at hlow
    have hup := RCadd_le_add h (RCle_refl (RCneg (RCscale b N)))
    change RCle (RCsub (RCscale a N) (RCscale b N)) (RCsub (RCscale b N) (RCscale b N)) at hup
    rw [sh_sub_self] at hup
    have hx := sh_nonpos_of_mul_nonpos hq (sh_rational_nonpos (RCle_trans hlow hup))
    have h2 := Q'.add_le_add_right _ _ b hx
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv
      (poly_identity_of_normal_eq (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
        (by decide) (fun | 0 => a | _ => b)))
      (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' b))))

private theorem sh_traj_halves (j : Nat) (hj : 1 ≤ j) : side j/2+side j/2 = side j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i+1 := ⟨j-1, by omega⟩
  simp only [side, Nat.pow_succ]
  omega

private theorem sh_traj_hsp (j : Nat) : Q'.ofNat (side j)*spacing j ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (unit_side j)

/-! ## 1. Generic one-step eps bound and the lag-shift pins -/

section Generic

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- The one-step relative energy bound `L (B(x,x) - B(x,Tx)) ≤ c0 B(x,x)` for an
arbitrary carrier vector (the H1 shape, state-agnostic). -/
def OneStepEpsBound (x : V) (L : Nat) (c0 : Q') : Prop :=
  RCle (RCscale (Q'.ofNat L) (RCsub (B x x) (B x (T 1 x)))) (RCscale c0 (B x x))

/-- Lag shift: `B(T^h x, T^h x) = B(x, T^(2h) x)`. -/
theorem shift_norm_pin (x : V) (h : Nat) : B (T h x) (T h x) = B x (T (2*h) x) := by
  rw [BF4WilsonAllNomeCompletedTime.completedInner_time_sum hw0 hw1 h h,
    show h+h = 2*h by omega]

/-- Lag shift: `B(T^h x, T^n T^h x) = B(x, T^(n+2h) x)`. -/
theorem shift_response_pin (x : V) (h n : Nat) :
    B (T h x) (T n (T h x)) = B x (T (n+2*h) x) := by
  rw [← completedTime_add hw0 hw1 n h,
    BF4WilsonAllNomeCompletedTime.completedInner_time_sum hw0 hw1 h (n+h),
    show h+(n+h) = n+2*h by omega]

end Generic

/-! ## 2. The shifted Fejér telescope on the actual carrier -/

section State

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
  (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "x0" => Subtype.val (familyExcitation hw0 hw1 width qs c hqs)
local notation "Y" M:arg => smoothedCoherentVector hw0 hw1 width qs c hqs M

/-- Overlaps of the family with the smoothed orbit are box sums of family
responses: `B(T^a x0, T^b Y_M) = Σ_k r B(x0, T^(k+a+b) x0)`. -/
theorem overlap_expand (M a b : Nat) :
    B (T a x0) (T b (Y M)) =
      responseSum (timeKernel M) (fun k => B x0 (T (k+(a+b)) x0)) := by
  rw [BF4WilsonAllNomeCompletedTime.completedInner_time_sum hw0 hw1 a b x0 (Y M),
    completedInner_symm hw0 hw1,
    show T (a+b) (Y M) = orbitSum hw0 hw1 (T (a+b) x0) (timeKernel M) from
      orbitSum_time hw0 hw1 x0 (timeKernel M) (a+b),
    orbitSum_inner_left hw0 hw1 (T (a+b) x0) x0 (timeKernel M)]
  apply congrArg (responseSum (timeKernel M))
  funext k
  rw [← completedTime_add hw0 hw1 k (a+b) x0,
    BF4WilsonAllNomeCompletedTime.completedInner_time_balance hw0 hw1 (k+(a+b)) x0 x0]

/-- **Exact shifted Fejér telescope.** For `x = T^h Y_M`,
`B(x,x) - B(x,Tx) = (M+1)^(-1) (B(x0, T^(2h) Y_M) - B(T^(M+1) x0, T^(2h) Y_M))`. -/
theorem shifted_energy_telescope (M h : Nat) :
    RCsub (B (T h (Y M)) (T h (Y M))) (B (T h (Y M)) (T 1 (T h (Y M)))) =
      RCscale (smoothingWeight M)
        (RCsub (B x0 (T (2*h) (Y M))) (B (T (M+1) x0) (T (2*h) (Y M)))) := by
  rw [shift_norm_pin hw0 hw1 width (Y M) h, shift_response_pin hw0 hw1 width (Y M) h 1]
  have h1 : B (Y M) (T (2*h) (Y M)) =
      responseSum (timeKernel M) (fun n => B (T n x0) (T (2*h) (Y M))) :=
    orbitSum_inner_left hw0 hw1 x0 (T (2*h) (Y M)) (timeKernel M)
  have h2 : B (Y M) (T (1+2*h) (Y M)) =
      responseSum (timeKernel M) (fun n => B (T (n+1) x0) (T (2*h) (Y M))) := by
    refine (orbitSum_inner_left hw0 hw1 x0 (T (1+2*h) (Y M)) (timeKernel M)).trans ?_
    apply congrArg (responseSum (timeKernel M))
    funext n
    rw [BF4WilsonAllNomeCompletedTime.completedInner_time_sum hw0 hw1 n (1+2*h) x0 (Y M),
      BF4WilsonAllNomeCompletedTime.completedInner_time_sum hw0 hw1 (n+1) (2*h) x0 (Y M),
      show n+(1+2*h) = n+1+2*h by omega]
  have ht := boxSum_shift_telescope (smoothingWeight M)
    (fun n => B (T n x0) (T (2*h) (Y M))) M
  rw [completedTime_zero hw0 hw1] at ht
  rw [h1, h2]
  exact ht

/-- The lag-`(M+1)` shifted overlap is nonnegative. -/
theorem shifted_tail_overlap_nonnegative (M h : Nat) :
    RCnonneg (B (T (M+1) x0) (T (2*h) (Y M))) := by
  rw [overlap_expand hw0 hw1 width qs c hqs M (M+1) (2*h)]
  refine boxSum_nonneg (smoothingWeight_nonneg M) (fun k => B x0 (T (k+(M+1+2*h)) x0))
    (fun k => ?_) M
  change RCnonneg (B x0 (T (k+(M+1+2*h)) x0))
  have hm := mixedMoment_nonnegative hw0 hw1 x0 (k+(M+1+2*h)) 0
  exact hm

/-- The shifted head overlap is at most the family response at lag `2h`. -/
theorem shifted_head_overlap_le (M h : Nat) :
    RCle (B x0 (T (2*h) (Y M))) (B x0 (T (2*h) x0)) := by
  have e := overlap_expand hw0 hw1 width qs c hqs M 0 (2*h)
  rw [completedTime_zero hw0 hw1] at e
  rw [e]
  have hb := boxSum_le_const (smoothingWeight_nonneg M)
    (fun k => B x0 (T (k+(0+2*h)) x0)) (B x0 (T (2*h) x0)) M
    (fun k _ => by
      change RCle (B x0 (T (k+(0+2*h)) x0)) (B x0 (T (2*h) x0))
      exact response_le_of_le hw0 hw1 width x0 (by omega : 2*h ≤ k+(0+2*h)))
  have hm := timeKernel_mass M
  change RCle (responseSum (timeKernel M) (fun k => B x0 (T (k+(0+2*h)) x0)))
    (RCscale (kernelMass (timeKernel M)) (B x0 (T (2*h) x0))) at hb
  rw [RCSignedPairBudget.scale_congr hm, RCscale_one] at hb
  exact hb

/-- **Shifted telescope bound.** `(M+1)·E(T^h Y_M) ≤ B(x0, T^(2h) x0)`. -/
theorem shifted_energy_le_familyResponse (M h : Nat) :
    RCle (RCscale (Q'.ofNat (M+1))
        (RCsub (B (T h (Y M)) (T h (Y M))) (B (T h (Y M)) (T 1 (T h (Y M))))))
      (B x0 (T (2*h) x0)) := by
  have hr := smoothingWeight_nonneg M
  rw [shifted_energy_telescope hw0 hw1 width qs c hqs M h]
  have hE := RCscale_mono hr (RCle_trans
    (sh_sub_le_self (shifted_tail_overlap_nonnegative hw0 hw1 width qs c hqs M h))
    (shifted_head_overlap_le hw0 hw1 width qs c hqs M h))
  have h' := RCscale_mono (sh_ofNat_nonneg (M+1)) hE
  have hB : RCscale (Q'.ofNat (M+1)) (RCscale (smoothingWeight M) (B x0 (T (2*h) x0))) =
      B x0 (T (2*h) x0) := by
    rw [RCscale_RCscale, RCSignedPairBudget.scale_congr (smoothingWeight_normalizes M),
      RCscale_one]
  rw [hB] at h'
  exact h'

/-- The shifted norm dominates the family response at lag `2M+2h`. -/
theorem shifted_norm_ge_family_response (M h : Nat) :
    RCle (B x0 (T (2*M+2*h) x0)) (B (T h (Y M)) (T h (Y M))) := by
  have hr := smoothingWeight_nonneg M
  rw [shift_norm_pin hw0 hw1 width (Y M) h]
  change RCle _ (smoothedResponse hw0 hw1 width qs c hqs M (2*h))
  rw [smoothedResponse_orbit_expand hw0 hw1 width qs c hqs M (2*h)]
  have hinner : ∀ m, m ≤ M →
      RCle (RCscale (kernelMass (timeKernel M)) (B x0 (T (2*M+2*h) x0)))
        (responseSum (timeKernel M) (fun k => B x0 (T (m+k+2*h) x0))) := fun m hm =>
    boxSum_ge_const hr (fun k => B x0 (T (m+k+2*h) x0)) _ M
      (fun k hk => response_le_of_le hw0 hw1 width x0 (by omega : m+k+2*h ≤ 2*M+2*h))
  have houter := boxSum_ge_const hr _ _ M hinner
  change RCle (RCscale (kernelMass (timeKernel M))
      (RCscale (kernelMass (timeKernel M)) (B x0 (T (2*M+2*h) x0)))) _ at houter
  have hm := timeKernel_mass M
  have hmm : kernelMass (timeKernel M) * kernelMass (timeKernel M) ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hm)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hm) (Q'.one_mul_eqv 1))
  rw [RCscale_RCscale, RCSignedPairBudget.scale_congr hmm, RCscale_one] at houter
  exact houter

/-- Shifted relative floor ⟹ shifted eps bound at a fixed scale. -/
theorem shiftedEpsBound_of_relativeFloor (M h L : Nat) (c0 theta : Q')
    (hc0 : (0 : Q') ≤ c0) (htheta : (0 : Q') ≤ theta)
    (hL : Q'.ofNat L ≤ c0 * theta * Q'.ofNat (M+1))
    (hfloor : RCle (RCscale theta (B x0 (T (2*h) x0))) (B (T h (Y M)) (T h (Y M)))) :
    OneStepEpsBound hw0 hw1 width (T h (Y M)) L c0 := by
  unfold OneStepEpsBound
  have hresp : RCle (B (T h (Y M)) (T 1 (T h (Y M)))) (B (T h (Y M)) (T h (Y M))) := by
    have hr := response_le_of_le hw0 hw1 width (T h (Y M)) (Nat.zero_le 1)
    rwa [completedTime_zero hw0 hw1] at hr
  have hE := sh_sub_nonnegative_of_le hresp
  have h1 := RCscale_scalar_mono hL hE
  have h2 := RCscale_mono (Q'.mul_nonneg _ _ hc0 htheta)
    (shifted_energy_le_familyResponse hw0 hw1 width qs c hqs M h)
  rw [RCscale_RCscale] at h2
  have h3 := RCscale_mono hc0 hfloor
  rw [RCscale_RCscale] at h3
  exact RCle_trans h1 (RCle_trans h2 h3)

end State

/-! ## 3. The shifted path Props -/

/-- **Shifted H1 (OPEN).** At every scale, the time-shifted anchor
`T^(side_j/2) Y_j` satisfies `side_j·E ≤ c0·B`. -/
def PathShiftedEpsBound (tr : DyadicSmoothedTrajectory) (c0 : Q') : Prop :=
  ∀ j, OneStepEpsBound (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j)
    (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (side j / 2)
      (tr.state j)) (side j) c0

/-- **Qualitative nondegeneracy (OPEN, fixed-scale).** `fl_j ≤ R_j(side_j)`; the
positive floors `fl_j` may depend arbitrarily on `j`. -/
def PathShiftedNondegenerate (tr : DyadicSmoothedTrajectory) (fl : Nat → Q') : Prop :=
  ∀ j, RCle (Rq (fl j)) (tr.response j (side j))

/-- Shifted family survival (OPEN): `θ R_x(2h_j) ≤ R_x(2M_j + 2h_j)`, `h_j = side_j/2`. -/
def PathShiftedFamilySurvival (tr : DyadicSmoothedTrajectory) (theta : Q') : Prop :=
  ∀ j, RCle (RCscale theta (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (tr.familyVector j)
      (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (2*(side j/2))
        (tr.familyVector j))))
    (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.familyVector j)
      (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
        (2*tr.radius j + 2*(side j/2)) (tr.familyVector j)))

/-- Response form of the shifted H1 at `j ≥ 1`:
`side_j (R_j(side_j) - R_j(side_j+1)) ≤ c0 R_j(side_j)`. -/
theorem pathShiftedEpsBound_iff_response (tr : DyadicSmoothedTrajectory) (c0 : Q')
    (j : Nat) (hj : 1 ≤ j) :
    OneStepEpsBound (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j)
      (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (side j / 2)
        (tr.state j)) (side j) c0 ↔
    RCle (RCscale (Q'.ofNat (side j)) (RCsub (tr.response j (side j))
        (tr.response j (side j + 1))))
      (RCscale c0 (tr.response j (side j))) := by
  have hh := sh_traj_halves j hj
  unfold OneStepEpsBound
  rw [shift_norm_pin (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j)
      (tr.state j) (side j / 2),
    shift_response_pin (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j)
      (tr.state j) (side j / 2) 1,
    show 2*(side j/2) = side j by omega, show 1 + side j = side j + 1 by omega]
  exact Iff.rfl

/-- Shifted family survival with `1 ≤ c0 θ m` gives the shifted H1. -/
theorem pathShiftedEpsBound_of_shiftedFamilySurvival (tr : DyadicSmoothedTrajectory)
    (c0 theta : Q') (hc0 : (0 : Q') ≤ c0) (htheta : (0 : Q') ≤ theta)
    (hrate : (1 : Q') ≤ c0 * theta * Q'.ofNat tr.radiusFactor)
    (H2s : PathShiftedFamilySurvival tr theta) : PathShiftedEpsBound tr c0 := by
  intro j
  have hw0 := tr.schedule.nome_pos j
  have hw1 := tr.schedule.nome_lt_one j
  have hfloor := RCle_trans (H2s j) (shifted_norm_ge_family_response hw0 hw1
    (trajWidth j) (tr.faces j) (tr.coeff j) (tr.faces_spatial j) (tr.radius j) (side j / 2))
  refine shiftedEpsBound_of_relativeFloor hw0 hw1 (trajWidth j) (tr.faces j) (tr.coeff j)
    (tr.faces_spatial j) (tr.radius j) (side j / 2) (side j) c0 theta hc0 htheta ?_ hfloor
  have hk : (0 : Q') ≤ c0 * theta := Q'.mul_nonneg _ _ hc0 htheta
  have hs := sh_ofNat_nonneg (side j)
  have hA : Q'.ofNat (side j) ≤ c0 * theta * Q'.ofNat tr.radiusFactor * Q'.ofNat (side j) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hrate hs)
  have hB : c0 * theta * Q'.ofNat tr.radiusFactor * Q'.ofNat (side j) ≈
      c0 * theta * Q'.ofNat (tr.radiusFactor * side j) :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 0) (.mul (.var 1) (.var 2))) (by decide)
        (fun | 0 => c0 * theta | 1 => Q'.ofNat tr.radiusFactor | _ => Q'.ofNat (side j)))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (sh_ofNat_mul _ _)))
  have hC : c0 * theta * Q'.ofNat (tr.radiusFactor * side j) ≤
      c0 * theta * Q'.ofNat (tr.radiusFactor * side j + 1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (sh_ofNat_le_succ _) hk
  exact Q'.le_trans' _ _ _ hA (Q'.le_trans' _ _ _ (Q'.le_of_eqv hB) hC)

/-! ## 4. Feeding `NormalizedAnchorData`: the shifted path anchor -/

/-- Anchor data of `Y_j` at block `side_j` (normalized state `α T^(side_j) Y_j`),
with floor `κ·fl_j`, `κ = (1-δ)^(2^a)`. -/
def shiftedPathAnchor (tr : DyadicSmoothedTrajectory) (delta : Q') (hdelta : delta < (1 : Q'))
    (a : Nat) (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j) (j : Nat) :
    NormalizedAnchorData (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j) :=
  smoothedAnchorData (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j)
    (tr.faces j) (tr.coeff j) (tr.faces_spatial j) (tr.radius j) (side j) (side_positive j)
    (((1 : Q') - delta)^(side a) * fl j)
    (Q'.mul_pos (pathKappa_pos delta hdelta a) (hfl j))

/-- Shifted H1 + nondegeneracy give the macro ratio `κ R_j(side_j) ≤ R_j(2 side_j)`. -/
theorem path_shifted_macroRatio (tr : DyadicSmoothedTrajectory) (c0 delta : Q') (a : Nat)
    (ha : 1 ≤ a) (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta) (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (H1s : PathShiftedEpsBound tr c0) (Hnd : PathShiftedNondegenerate tr fl)
    (j : Nat) (haj : a ≤ j) :
    (shiftedPathAnchor tr delta hdelta a fl hfl j).MacroRatio (((1 : Q') - delta)^(side a)) := by
  have hw0 := tr.schedule.nome_pos j
  have hw1 := tr.schedule.nome_lt_one j
  have hs := side_split a j haj
  have hL : 0 < side (j-a) := side_positive (j-a)
  have hh := sh_traj_halves j (by omega)
  have hxx := shift_norm_pin hw0 hw1 (trajWidth j) (tr.state j) (side j / 2)
  rw [show 2*(side j/2) = side j by omega] at hxx
  have hnormx : RCle (Rq (fl j)) (completedInner hw0 hw1
      (completedTime hw0 hw1 (side j / 2) (tr.state j))
      (completedTime hw0 hw1 (side j / 2) (tr.state j))) := by
    rw [hxx]
    exact Hnd j
  have hkpos := sh_ofNat_pos (side a) (side_positive a)
  have hN := completedInner_nonnegative hw0 hw1 (completedTime hw0 hw1 (side j / 2) (tr.state j))
  have hside : Q'.ofNat (side j) ≈ Q'.ofNat (side a) * Q'.ofNat (side (j-a)) := by
    rw [side_split a j haj]
    exact Q'.eqv_trans _ _ _ (sh_ofNat_mul _ _) (Q'.mul_comm_eqv _ _)
  have h1s := H1s j
  unfold OneStepEpsBound at h1s
  have hE : RCle (RCscale (Q'.ofNat (side (j-a)))
      (RCsub (completedInner hw0 hw1 (completedTime hw0 hw1 (side j / 2) (tr.state j))
          (completedTime hw0 hw1 (side j / 2) (tr.state j)))
        (completedInner hw0 hw1 (completedTime hw0 hw1 (side j / 2) (tr.state j))
          (completedTime hw0 hw1 1 (completedTime hw0 hw1 (side j / 2) (tr.state j))))))
      (RCscale delta (completedInner hw0 hw1 (completedTime hw0 hw1 (side j / 2) (tr.state j))
          (completedTime hw0 hw1 (side j / 2) (tr.state j)))) := by
    apply sh_scale_cancel hkpos
    rw [RCscale_RCscale, RCscale_RCscale, ← RCSignedPairBudget.scale_congr hside]
    exact RCle_trans h1s (RCscale_scalar_mono hc0 hN)
  have hchain := block_survival_of_oneStep_energy hw0 hw1 (trajWidth j)
    (completedTime hw0 hw1 (side j / 2) (tr.state j))
    (side j) (side (j-a)) (side a) hs hL delta (fl j) hdelta0 hdelta (hfl j) hnormx hE 1
  rw [Nat.mul_one, RCSignedPairBudget.scale_congr (sh_pow_one _), hxx,
    shift_response_pin hw0 hw1 (trajWidth j) (tr.state j) (side j / 2) (side j),
    show side j + 2*(side j/2) = 2 * side j by omega] at hchain
  exact hchain

/-- The anchor floor `κ·fl_j` is a TRUE floor of `R_j(2 side_j)`. -/
theorem path_shifted_anchor_floor (tr : DyadicSmoothedTrajectory) (c0 delta : Q') (a : Nat)
    (ha : 1 ≤ a) (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta) (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (H1s : PathShiftedEpsBound tr c0) (Hnd : PathShiftedNondegenerate tr fl)
    (j : Nat) (haj : a ≤ j) :
    leEv (ofQ' (shiftedPathAnchor tr delta hdelta a fl hfl j).floor)
      (shiftedPathAnchor tr delta hdelta a fl hfl j).norm := by
  have hw0 := tr.schedule.nome_pos j
  have hw1 := tr.schedule.nome_lt_one j
  have hratio := path_shifted_macroRatio tr c0 delta a ha hdelta0 hdelta hc0 fl hfl H1s Hnd j haj
  have hk0 : (0 : Q') ≤ ((1 : Q') - delta)^(side a) := Q'.le_of_lt (pathKappa_pos delta hdelta a)
  have hnd := RCscale_mono hk0 (Hnd j)
  rw [sh_scale_rational] at hnd
  change RCle (RCscale (((1 : Q') - delta)^(side a)) (tr.response j (side j)))
    (completedInner hw0 hw1 (tr.state j) (completedTime hw0 hw1 (2 * side j) (tr.state j)))
    at hratio
  have h := RCle_trans hnd hratio
  have hpin := smoothedNorm_pin hw0 hw1 (trajWidth j) (tr.faces j) (tr.coeff j)
    (tr.faces_spatial j) (tr.radius j) (2 * side j)
  unfold smoothedResponse at hpin
  change RCle _ (completedInner hw0 hw1
    (smoothedCoherentVector hw0 hw1 (trajWidth j) (tr.faces j) (tr.coeff j)
      (tr.faces_spatial j) (tr.radius j))
    (completedTime hw0 hw1 (2 * side j) (smoothedCoherentVector hw0 hw1 (trajWidth j)
      (tr.faces j) (tr.coeff j) (tr.faces_spatial j) (tr.radius j)))) at h
  rw [hpin] at h
  exact h

/-- The A03 normalized-anchor package for the shifted path anchor. -/
def ShiftedAnchorPackage (tr : DyadicSmoothedTrajectory) (delta : Q') (hdelta : delta < (1 : Q'))
    (a : Nat) (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j) : Prop :=
  ∀ j : Nat, a ≤ j →
    completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
        (shiftedPathAnchor tr delta hdelta a fl hfl j).normalized.val
        (shiftedPathAnchor tr delta hdelta a fl hfl j).normalized.val = Rq 1 ∧
    (∀ i : Nat, RCle (Rq ((((1 : Q') - delta)^(side a))^i))
      (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
        (shiftedPathAnchor tr delta hdelta a fl hfl j).normalized.val
        (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (i * side j)
          (shiftedPathAnchor tr delta hdelta a fl hfl j).normalized.val))) ∧
    (∀ (i : Nat) (time : PositiveTimeValue),
      RCle (RCscale (spacing j) (realValue time)) (Rq (Q'.ofNat i)) →
      RCle (Rq ((((1 : Q') - delta)^(side a))^(i+1)))
        (bondCompletedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
          (shiftedPathAnchor tr delta hdelta a fl hfl j).bondExcitation
          (action (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) time
            (shiftedPathAnchor tr delta hdelta a fl hfl j).bondExcitation))) ∧
    (∀ (epsilon : Q'), (0 : Q') < epsilon → ∀ time : PositiveTimeValue,
      RCle (RCscale (spacing j) (realValue time))
        (Rq (macroGeometricRadius (((1 : Q') - delta)^(side a)) epsilon)) →
      RCle (bondCompletedDistance (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
        (action (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) time
          (shiftedPathAnchor tr delta hdelta a fl hfl j).bondExcitation)
        (shiftedPathAnchor tr delta hdelta a fl hfl j).bondExcitation) (Rq epsilon))

/-- **Shifted A03 path theorem.** From the shifted H1 and qualitative
nondegeneracy, at every scale `j ≥ a ≥ 1` the normalized anchor
`α_j T^(side_j) Y_j` has unit norm, block floors `κ^i` at lag `i·side_j`,
real-time survival `κ^(i+1)` at represented times of geometric size `≤ i`, and the
geometric real-time increment modulus; `κ = (1-δ)^(2^a)`, `c0 ≤ 2^a δ`. -/
theorem path_normalized_anchor_shifted (tr : DyadicSmoothedTrajectory) (c0 delta : Q') (a : Nat)
    (ha : 1 ≤ a) (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta) (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (H1s : PathShiftedEpsBound tr c0) (Hnd : PathShiftedNondegenerate tr fl) :
    ShiftedAnchorPackage tr delta hdelta a fl hfl := by
  intro j haj
  have hkappa := pathKappa_pos delta hdelta a
  have hfloor := path_shifted_anchor_floor tr c0 delta a ha hdelta0 hdelta hc0 fl hfl H1s Hnd j haj
  have hratio := path_shifted_macroRatio tr c0 delta a ha hdelta0 hdelta hc0 fl hfl H1s Hnd j haj
  refine ⟨NormalizedAnchorData.normalized_norm (shiftedPathAnchor tr delta hdelta a fl hfl j)
      hfloor,
    fun i => NormalizedAnchorData.block_floor (shiftedPathAnchor tr delta hdelta a fl hfl j) _
      hkappa hfloor hratio i,
    fun i time ht => NormalizedAnchorData.real_floor
      (shiftedPathAnchor tr delta hdelta a fl hfl j) _ hkappa
      (side_positive j) hfloor hratio (spacing j) (sh_traj_hsp j) i time ht,
    fun epsilon he time ht => NormalizedAnchorData.real_increment
      (shiftedPathAnchor tr delta hdelta a fl hfl j) _ hkappa (side_positive j)
      (sh_traj_halves j (by omega)) hfloor hratio (spacing j) (sh_traj_hsp j) epsilon he time ht⟩

/-- Same package from shifted family survival (OPEN) instead of the shifted H1. -/
theorem path_normalized_anchor_shifted_of_survival (tr : DyadicSmoothedTrajectory)
    (c0 theta delta : Q') (a : Nat) (ha : 1 ≤ a)
    (hc0pos : (0 : Q') ≤ c0) (htheta : (0 : Q') ≤ theta)
    (hrate : (1 : Q') ≤ c0 * theta * Q'.ofNat tr.radiusFactor)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta) (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (H2s : PathShiftedFamilySurvival tr theta) (Hnd : PathShiftedNondegenerate tr fl) :
    ShiftedAnchorPackage tr delta hdelta a fl hfl :=
  path_normalized_anchor_shifted tr c0 delta a ha hdelta0 hdelta hc0 fl hfl
    (pathShiftedEpsBound_of_shiftedFamilySurvival tr c0 theta hc0pos htheta hrate H2s) Hnd

/-! ## 5. The shifted gap screen -/

/-- Shifted H1 still caps every certified one-step rate on the same carrier:
`side_j (1 - r_j) ≤ c0` at every `j ≥ 1` (given nondegeneracy). -/
theorem path_shiftedEps_forces_rate (tr : DyadicSmoothedTrajectory) (c0 : Q') (r : Nat → Q')
    (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (H1s : PathShiftedEpsBound tr c0) (Hnd : PathShiftedNondegenerate tr fl)
    (Hr : ∀ j, WilsonVacuumRayleighRate (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (trajWidth j) (r j))
    (j : Nat) (hj : 1 ≤ j) : Q'.ofNat (side j) * (1 - r j) ≤ c0 := by
  have hw0 := tr.schedule.nome_pos j
  have hw1 := tr.schedule.nome_lt_one j
  have hh := sh_traj_halves j hj
  let y : VacuumComplement hw0 hw1 (width := trajWidth j) :=
    ⟨completedTime hw0 hw1 (side j / 2) (tr.state j),
      BF4WilsonAllNomeCompletedTime.completedTime_preserves_vacuumComplement hw0 hw1
        (side j / 2) (tr.state j)
        (smoothedCoherentState hw0 hw1 (trajWidth j) (tr.faces j) (tr.coeff j)
          (tr.faces_spatial j) (tr.radius j)).property⟩
  have hlow := oneStep_energy_ge_of_rayleighRate hw0 hw1 (trajWidth j) (r j) (Hr j) y
  have h' := RCscale_mono (sh_ofNat_nonneg (side j)) hlow
  rw [RCscale_RCscale] at h'
  have h1s := H1s j
  unfold OneStepEpsBound at h1s
  have hrc := RCle_trans h' h1s
  have hxx := shift_norm_pin hw0 hw1 (trajWidth j) (tr.state j) (side j / 2)
  rw [show 2*(side j/2) = side j by omega] at hxx
  have hnormx : RCle (Rq (fl j)) (completedInner hw0 hw1
      (completedTime hw0 hw1 (side j / 2) (tr.state j))
      (completedTime hw0 hw1 (side j / 2) (tr.state j))) := by
    rw [hxx]
    exact Hnd j
  exact sh_coeff_le_of_scale_le (hfl j) hnormx hrc

/-! ## 6. AF-calibrated schedule Props (OPEN physics input) -/

/-- Integer log₂ surrogate `⌊log₂(j+1)⌋` (within 1 of `log₂(j+1)`). -/
def lg2 (j : Nat) : Q' := Q'.ofNat (Nat.log2 (j+1))

/-- **AF calibration of the nome schedule (OPEN, NOT proved, NOT consumed).**
Two-loop AF predicts that `side_j` lattice steps have bounded physical length iff
`|A/(1-w_j) - j - κ·log₂ j| ≤ C` for all `j`, with the PINNED constants
`A = 1/(16 b0 ln 2)` and `κ = b1/(2 b0²)` (SU(2): `A ≈ 1.942`, `κ = 51/121`), where
`b0, b1` refer to the STANDARD coupling `g² = 2t = -8 log w`; the carrier
heat-kernel time is `t = -4 log w` (repo label `g² = t`, under which one would get
3.883). See `docs/CONVENTIONS-COUPLING.md` and the audit. Here it is stated
multiplied out, for arbitrary `A, κ, C`. -/
def NomeScheduleAFCalibrated (ns : NomeSchedule) (A kappa C : Q') : Prop :=
  (0 : Q') < A ∧ ∀ j : Nat,
    (Q'.ofNat j + kappa * lg2 j + -C) * ((1 : Q') - ns.nome j) ≤ A ∧
    A ≤ (Q'.ofNat j + kappa * lg2 j + C) * ((1 : Q') - ns.nome j)

/-- **Physical-box form (OPEN).** For a supplied scale-setting function `a`
(lattice spacing in physical units at nome `w`), `L_j = side_j·a(w_j)` stays in
`[Llo, Lhi]`. The shifted H1 needs (heuristically) only the upper bound; a fixed
physical gap measured in units of `side_j` steps also needs the lower bound. -/
def NomeSchedulePhysicalBox (ns : NomeSchedule) (a : Q' → Q') (Llo Lhi : Q') : Prop :=
  (0 : Q') < Llo ∧ ∀ j : Nat,
    Llo ≤ Q'.ofNat (side j) * a (ns.nome j) ∧ Q'.ofNat (side j) * a (ns.nome j) ≤ Lhi

/-- The interface witness `dyadicNomeSchedule` has `(1-w_j)·side_j = 1/2` at
every scale: bounded, whereas AF calibration forces `(1-w_j)·side_j ≍ A·2^j/j`. -/
theorem dyadicNomeSchedule_margin_side (j : Nat) :
    ((1 : Q') - dyadicNomeSchedule.nome j) * Q'.ofNat (side j) ≈ HalfPow.half := by
  change ((1 : Q') - ((1 : Q') - HalfPow.half^(1+j))) * Q'.ofNat (side j) ≈ HalfPow.half
  rw [Nat.add_comm 1 j]
  change ((1 : Q') - ((1 : Q') - HalfPow.half * HalfPow.half^j)) * Q'.ofNat (side j)
    ≈ HalfPow.half
  have hu := unit_side j
  change HalfPow.half^j * Q'.ofNat (side j) ≈ 1 at hu
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.add (.const 1) (.neg (.add (.const 1) (.neg (.mul (.var 0) (.var 1))))))
        (.var 2))
      (.mul (.var 0) (.mul (.var 1) (.var 2))) (by decide)
      (fun | 0 => HalfPow.half | 1 => HalfPow.half^j | _ => Q'.ofNat (side j)))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hu) (Q'.mul_one_eqv _))

#print axioms OneStepEpsBound
#print axioms shift_norm_pin
#print axioms shift_response_pin
#print axioms overlap_expand
#print axioms shifted_energy_telescope
#print axioms shifted_tail_overlap_nonnegative
#print axioms shifted_head_overlap_le
#print axioms shifted_energy_le_familyResponse
#print axioms shifted_norm_ge_family_response
#print axioms shiftedEpsBound_of_relativeFloor
#print axioms PathShiftedEpsBound
#print axioms PathShiftedNondegenerate
#print axioms PathShiftedFamilySurvival
#print axioms pathShiftedEpsBound_iff_response
#print axioms pathShiftedEpsBound_of_shiftedFamilySurvival
#print axioms shiftedPathAnchor
#print axioms path_shifted_macroRatio
#print axioms path_shifted_anchor_floor
#print axioms ShiftedAnchorPackage
#print axioms path_normalized_anchor_shifted
#print axioms path_normalized_anchor_shifted_of_survival
#print axioms path_shiftedEps_forces_rate
#print axioms lg2
#print axioms NomeScheduleAFCalibrated
#print axioms NomeSchedulePhysicalBox
#print axioms dyadicNomeSchedule_margin_side

end YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor
