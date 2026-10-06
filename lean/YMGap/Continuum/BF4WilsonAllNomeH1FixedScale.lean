/-
# H1 at a fixed scale: exact smoothed-energy identity, H2 ⟹ H1, and the gap screen

Paper companion: `audits/MATH-NOTE-H1-FIXED-SCALE-2026-10-05.md`.

This file proves, on the SAME all-nome completed Wilson carrier and for the SAME
box-smoothed coherent family state `Y_M = (M+1)^(-1) Σ_{k≤M} T^k x0` used by the
dyadic trajectory, three carrier-level facts about the one-step energy
`E_M = B(Y_M,Y_M) - B(Y_M, T Y_M)` that enters H1 (`SmoothedCoherentEpsBound`).

1. **Exact Fejér telescope.** `E_M = (M+1)^(-1) (B(x0,Y_M) - B(T^(M+1) x0, Y_M))`
   (`smoothedEnergy_telescope`); hence `(M+1) E_M ≤ B(x0,x0)`
   (`smoothedEnergy_le_familyNorm`).  This is the polynomial identity
   `(1-λ) p(λ) = (1-λ^(M+1))/(M+1)` for the box kernel `p`, done at response level.
2. **H2 ⟹ H1.** A relative floor `θ B(x0,x0) ≤ B(Y_M,Y_M)` with
   `side ≤ c0 θ (M+1)` gives H1 (`smoothedEpsBound_of_relativeFloor`).  Along the
   trajectory, `PathFamilyRadiusSurvival tr θ` with `1 ≤ c0 θ m` gives
   `PathEpsBound tr c0` (`pathEpsBound_of_familyRadiusSurvival`), so the whole A03
   normalized-anchor conclusion follows from H2 alone
   (`path_normalized_anchor_of_familyRadiusSurvival`).  H2 itself stays OPEN.
3. **Gap screen.** For ANY one-step Rayleigh rate `r` on the vacuum complement of
   the same carrier (`WilsonVacuumRayleighRate`, an OPEN Prop for `r < 1`; it holds
   trivially at `r = 1`), the energy satisfies `E ≥ (1-r) B(y,y)`
   (`oneStep_energy_ge_of_rayleighRate`), so H1 forces
   `side_j (1 - r_j) ≤ c0` at every scale (`path_epsBound_forces_rate`).
   H1 is therefore an UPPER bound on the certified gap per lattice step: it is
   incompatible with any fixed rate `r < 1` as `side → ∞`.

Also: at each FIXED scale H1 holds unconditionally with the scale-dependent
constant `c0 = side` (`smoothedEpsBound_trivial`): H1 is never vacuous at one
scale; its content is uniformity of `c0`.

Nothing here proves H1 or H2 uniformly.  No `sorry`, no axioms.
-/

import YMGap.Continuum.BF4WilsonAllNomeGenericNormalizedAnchor

namespace YMGap.Continuum.BF4WilsonAllNomeH1FixedScale

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4DyadicWilsonSquare (side side_positive spacing)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion completedInner completedInner_nonnegative completedInner_symm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedTime_zero VacuumComplement)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime (orbitSum responseSum orbitSum_inner_left)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (mixedMoment_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance (familyExcitation)
open YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState
  (smoothingWeight smoothingWeight_nonneg smoothingWeight_normalizes boxKernel timeKernel
   kernelMass timeKernel_mass boxSum_nonneg smoothedCoherentVector smoothedCoherentState
   smoothedResponse_nonnegative smoothedEnergy smoothedEnergy_nonnegative
   SmoothedCoherentEpsBound smoothedNormFloor smoothedNormFloor_positive
   smoothedCoherent_norm_floor)
open YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen
  (response_le_of_le smoothedCoherent_norm_ge_family_response)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory.DyadicSmoothedTrajectory
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (bondCompletedInner bondCompletedDistance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealTime (action)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (PositiveTimeValue realValue)
open YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedMacroRatio (macroGeometricRadius)
open YMGap.Continuum.BF4WilsonAllNomeGenericNormalizedAnchor (pathAnchor path_normalized_anchor)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)
local infix:50 " ≈ " => Q'.eqv

/-! ## Scalar and `RC` helpers (local copies plus three pointwise identities) -/

private theorem h1_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem h1_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
      (Q'.eqv_of_eq (Q'.zero_add' (A.approx n)))))

private theorem h1_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem h1_scale_coeff_add (a b : Q') (x : RC) :
    RCscale (a + b) x = RCadd (RCscale a x) (RCscale b x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_mul_eqv a b (X.approx n)))

private theorem h1_scale_rational (c q : Q') : RCscale c (Rq q) = Rq (c*q) := by
  rw [RCscale_mk]
  exact Quotient.sound (CRealAlg.ofQ'_mul c q).symm

/-- `(r a + A) - (r d + B) = (A - B) + r (a - d)`. -/
private theorem h1_pair_sub (r : Q') (a d A B' : RC) :
    RCsub (RCadd (RCscale r a) A) (RCadd (RCscale r d) B') =
      RCadd (RCsub A B') (RCscale r (RCsub a d)) := by
  refine Quotient.inductionOn₂ a d ?_
  intro a' d'
  refine Quotient.inductionOn₂ A B' ?_
  intro A' B''
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 1)) (.var 3))
        (.neg (.add (.mul (.var 0) (.var 2)) (.var 4))))
      (.add (.add (.var 3) (.neg (.var 4)))
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))))
      (by decide)
      (fun | 0 => r | 1 => a'.approx n | 2 => d'.approx n | 3 => A'.approx n
           | _ => B''.approx n)))

/-- `r (c - a) + r (a - d) = r (c - d)`. -/
private theorem h1_scale_sub_add (r : Q') (c a d : RC) :
    RCadd (RCscale r (RCsub c a)) (RCscale r (RCsub a d)) = RCscale r (RCsub c d) := by
  refine Quotient.inductionOn₃ c a d ?_
  intro C A D
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.mul (.var 0) (.add (.var 2) (.neg (.var 3)))))
      (.mul (.var 0) (.add (.var 1) (.neg (.var 3))))
      (by decide)
      (fun | 0 => r | 1 => C.approx n | 2 => A.approx n | _ => D.approx n)))

/-- `a - (a - b) = b`. -/
private theorem h1_sub_sub_self (a b : RC) : RCsub a (RCsub a b) = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 0) (.neg (.var 1))))) (.var 1)
      (by decide) (fun | 0 => A.approx n | _ => B'.approx n)))

/-- `(a - b) + b = a`. -/
private theorem h1_sub_add_cancel (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
      (by decide) (fun | 0 => A.approx n | _ => B'.approx n)))

/-- `RCscale (a + -b) x = RCscale a x - RCscale b x`. -/
private theorem h1_scale_sub (a b : Q') (x : RC) :
    RCscale (a + -b) x = RCsub (RCscale a x) (RCscale b x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => a | 1 => b | _ => X.approx n)))

private theorem h1_sub_le_self {a b : RC} (hb : RCnonneg b) : RCle (RCsub a b) a := by
  have h := RCadd_le_add (RCle_refl (RCsub a b)) hb
  rwa [h1_add_zero, h1_sub_add_cancel] at h

private theorem h1_response_lower (r : Q') (norm response : RC)
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

private theorem h1_le_total (a b : Q') : a ≤ b ∨ b ≤ a := by
  rcases Int.le_total (a.num * (b.den : Int)) (b.num * (a.den : Int)) with h | h
  · exact Or.inl h
  · exact Or.inr h

private theorem h1_rational_nonpos {x : Q'} (h : RCle (Rq x) RCzero) : x ≤ (0 : Q') := by
  refine Q'.le_of_forall_pos_add (fun epsilon he => ?_)
  obtain ⟨index, hN⟩ := h epsilon he
  exact hN index (Nat.le_refl index)

private theorem h1_nonpos_of_mul_nonpos {x q : Q'} (hq : (0 : Q') < q)
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

/-- Rational cancellation against a positively floored `RC` value. -/
private theorem h1_coeff_le_of_scale_le {a b q : Q'} (hq : (0 : Q') < q) {N : RC}
    (hN : RCle (Rq q) N) (h : RCle (RCscale a N) (RCscale b N)) : a ≤ b := by
  rcases h1_le_total a b with hab | hba
  · exact hab
  · have hd : (0 : Q') ≤ a + -b := by
      have h' := Q'.add_le_add_right _ _ (-b) hba
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv b)) h'
    have hlow := RCscale_mono hd hN
    rw [h1_scale_rational, h1_scale_sub] at hlow
    have hup := RCadd_le_add h (RCle_refl (RCneg (RCscale b N)))
    change RCle (RCsub (RCscale a N) (RCscale b N)) (RCsub (RCscale b N) (RCscale b N)) at hup
    rw [h1_sub_self] at hup
    have hx := h1_nonpos_of_mul_nonpos hq (h1_rational_nonpos (RCle_trans hlow hup))
    have h2 := Q'.add_le_add_right _ _ b hx
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv
      (poly_identity_of_normal_eq (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
        (by decide) (fun | 0 => a | _ => b)))
      (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' b))))

private theorem h1_ofNat_mul (a b : Nat) :
    Q'.ofNat (a*b) ≈ Q'.ofNat a * Q'.ofNat b := by
  have hd1 : ((Q'.ofNat a * Q'.ofNat b).den : Int) = 1 := rfl
  have hd2 : ((Q'.ofNat (a*b)).den : Int) = 1 := rfl
  show ((a*b : Nat) : Int) * ((Q'.ofNat a * Q'.ofNat b).den : Int)
    = (((a : Nat) : Int) * ((b : Nat) : Int)) * ((Q'.ofNat (a*b)).den : Int)
  rw [hd1, hd2]
  push_cast
  omega

private theorem h1_ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  change (0 : Int)*1 ≤ (n : Int)*1
  simp only [Int.mul_one]
  omega

private theorem h1_ofNat_le_succ (n : Nat) : Q'.ofNat n ≤ Q'.ofNat (n+1) := by
  change (n : Int)*1 ≤ ((n+1 : Nat) : Int)*1
  simp only [Int.mul_one]
  omega

/-! ## 1. The box-kernel shift telescope (pure response algebra) -/

/-- **Shift telescope.** For the box kernel of weight `r` and radius `M`,
`Σ_{k≤M} r f(k) - Σ_{k≤M} r f(k+1) = r (f 0 - f (M+1))`. -/
theorem boxSum_shift_telescope (r : Q') (f : Nat → RC) :
    ∀ M : Nat, RCsub (responseSum (boxKernel r M) f)
        (responseSum (boxKernel r M) (fun n => f (n+1))) =
      RCscale r (RCsub (f 0) (f (M+1)))
  | 0 => by
      change RCsub (RCadd (RCscale r (f 0)) RCzero) (RCadd (RCscale r (f (0+1))) RCzero) = _
      rw [h1_pair_sub, h1_sub_self, h1_zero_add]
  | m+1 => by
      change RCsub (RCadd (RCscale r (f (m+1))) (responseSum (boxKernel r m) f))
        (RCadd (RCscale r (f (m+1+1)))
          (responseSum (boxKernel r m) (fun n => f (n+1)))) = _
      rw [h1_pair_sub, boxSum_shift_telescope r f m, h1_scale_sub_add]

/-- A box sum of terms bounded by `a` is bounded by `kernelMass * a`. -/
theorem boxSum_le_const {r : Q'} (hr : (0 : Q') ≤ r) (f : Nat → RC) (a : RC) :
    ∀ M : Nat, (∀ n, n ≤ M → RCle (f n) a) →
      RCle (responseSum (boxKernel r M) f) (RCscale (kernelMass (boxKernel r M)) a)
  | 0, h => by
      change RCle (RCadd (RCscale r (f 0)) RCzero) (RCscale (r + 0) a)
      rw [h1_add_zero, RCSignedPairBudget.scale_congr
        (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv r 0) (Q'.eqv_of_eq (Q'.zero_add' r))) a]
      exact RCscale_mono hr (h 0 (Nat.le_refl 0))
  | m+1, h => by
      change RCle (RCadd (RCscale r (f (m+1))) (responseSum (boxKernel r m) f))
        (RCscale (r + kernelMass (boxKernel r m)) a)
      rw [h1_scale_coeff_add]
      exact RCadd_le_add (RCscale_mono hr (h (m+1) (Nat.le_refl _)))
        (boxSum_le_const hr f a m (fun n hn => h n (by omega)))

/-! ## 2. The exact smoothed-energy identity on the actual carrier -/

section State

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
  (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "x0" => Subtype.val (familyExcitation hw0 hw1 width qs c hqs)
local notation "Y" M:arg => smoothedCoherentVector hw0 hw1 width qs c hqs M

/-- **Exact Fejér telescope.**
`E_M = (M+1)^(-1) * (B(x0, Y_M) - B(T^(M+1) x0, Y_M))`. -/
theorem smoothedEnergy_telescope (M : Nat) :
    smoothedEnergy hw0 hw1 width qs c hqs M =
      RCscale (smoothingWeight M) (RCsub (B x0 (Y M)) (B (T (M+1) x0) (Y M))) := by
  have h1 : B (Y M) (Y M) = responseSum (timeKernel M) (fun n => B (T n x0) (Y M)) :=
    orbitSum_inner_left hw0 hw1 x0 (Y M) (timeKernel M)
  have h2 : B (Y M) (T 1 (Y M)) =
      responseSum (timeKernel M) (fun n => B (T (n+1) x0) (Y M)) := by
    have h := orbitSum_inner_left hw0 hw1 x0 (T 1 (Y M)) (timeKernel M)
    refine h.trans ?_
    apply congrArg (responseSum (timeKernel M))
    funext n
    rw [BF4WilsonAllNomeCompletedTime.completedInner_time_sum hw0 hw1 n 1 x0 (Y M),
      ← BF4WilsonAllNomeCompletedTime.completedInner_time_balance hw0 hw1 (n+1) x0 (Y M)]
  have ht := boxSum_shift_telescope (smoothingWeight M) (fun n => B (T n x0) (Y M)) M
  rw [completedTime_zero hw0 hw1] at ht
  unfold smoothedEnergy
  rw [h1, h2]
  exact ht

/-- The lag-`(M+1)` overlap is nonnegative. -/
theorem smoothed_tail_overlap_nonnegative (M : Nat) :
    RCnonneg (B (T (M+1) x0) (Y M)) := by
  rw [completedInner_symm hw0 hw1]
  have h := orbitSum_inner_left hw0 hw1 x0 (T (M+1) x0) (timeKernel M)
  change RCnonneg (B (orbitSum hw0 hw1 x0 (timeKernel M)) (T (M+1) x0))
  rw [h]
  refine boxSum_nonneg (smoothingWeight_nonneg M) _ (fun n => ?_) M
  change RCnonneg (B (T n x0) (T (M+1) x0))
  rw [BF4WilsonAllNomeCompletedTime.completedInner_time_sum hw0 hw1 n (M+1) x0 x0]
  exact mixedMoment_nonnegative hw0 hw1 x0 (n+(M+1)) 0

/-- The single-average overlap is at most the family norm. -/
theorem smoothed_head_overlap_le_norm (M : Nat) :
    RCle (B x0 (Y M)) (B x0 x0) := by
  rw [completedInner_symm hw0 hw1]
  have h := orbitSum_inner_left hw0 hw1 x0 x0 (timeKernel M)
  change RCle (B (orbitSum hw0 hw1 x0 (timeKernel M)) x0) (B x0 x0)
  rw [h]
  have hb := boxSum_le_const (smoothingWeight_nonneg M) (fun n => B (T n x0) x0) (B x0 x0) M
    (fun n _ => by
      change RCle (B (T n x0) x0) (B x0 x0)
      rw [BF4WilsonAllNomeCompletedTime.completedInner_time_balance hw0 hw1 n x0 x0]
      have hr := response_le_of_le hw0 hw1 width x0 (Nat.zero_le n)
      rwa [completedTime_zero hw0 hw1] at hr)
  have hm := timeKernel_mass M
  change RCle (responseSum (timeKernel M) (fun n => B (T n x0) x0))
    (RCscale (kernelMass (timeKernel M)) (B x0 x0)) at hb
  rw [RCSignedPairBudget.scale_congr hm, RCscale_one] at hb
  exact hb

/-- **Unconditional energy bound.** `(M+1) * E_M ≤ B(x0, x0)`. -/
theorem smoothedEnergy_le_familyNorm (M : Nat) :
    RCle (RCscale (Q'.ofNat (M+1)) (smoothedEnergy hw0 hw1 width qs c hqs M)) (B x0 x0) := by
  have hr := smoothingWeight_nonneg M
  have hE : RCle (smoothedEnergy hw0 hw1 width qs c hqs M)
      (RCscale (smoothingWeight M) (B x0 x0)) := by
    rw [smoothedEnergy_telescope]
    exact RCscale_mono hr (RCle_trans
      (h1_sub_le_self (smoothed_tail_overlap_nonnegative hw0 hw1 width qs c hqs M))
      (smoothed_head_overlap_le_norm hw0 hw1 width qs c hqs M))
  have h := RCscale_mono (h1_ofNat_nonneg (M+1)) hE
  rw [RCscale_RCscale, RCSignedPairBudget.scale_congr (smoothingWeight_normalizes M),
    RCscale_one] at h
  exact h

/-- **Fixed-scale non-vacuity.** H1 holds at every single scale with the
scale-DEPENDENT constant `c0 = side scale`. The content of H1 is uniformity. -/
theorem smoothedEpsBound_trivial (M scale : Nat) :
    SmoothedCoherentEpsBound hw0 hw1 width qs c hqs M scale (Q'.ofNat (side scale)) :=
  RCscale_mono (h1_ofNat_nonneg _)
    (h1_sub_le_self (smoothedResponse_nonnegative hw0 hw1 width qs c hqs M 1))

/-- **Relative floor ⟹ H1 at a fixed scale.** If `θ B(x0,x0) ≤ B(Y_M,Y_M)` and
`side ≤ c0 θ (M+1)` (with `c0, θ ≥ 0`), then `SmoothedCoherentEpsBound M scale c0`. -/
theorem smoothedEpsBound_of_relativeFloor (M scale : Nat) (c0 theta : Q')
    (hc0 : (0 : Q') ≤ c0) (htheta : (0 : Q') ≤ theta)
    (hside : Q'.ofNat (side scale) ≤ c0 * theta * Q'.ofNat (M+1))
    (hfloor : RCle (RCscale theta (B x0 x0)) (B (Y M) (Y M))) :
    SmoothedCoherentEpsBound hw0 hw1 width qs c hqs M scale c0 := by
  unfold SmoothedCoherentEpsBound
  have hE := smoothedEnergy_nonnegative hw0 hw1 width qs c hqs M
  have h1 := RCscale_scalar_mono hside hE
  have h2 := RCscale_mono (Q'.mul_nonneg _ _ hc0 htheta)
    (smoothedEnergy_le_familyNorm hw0 hw1 width qs c hqs M)
  rw [RCscale_RCscale] at h2
  have h3 := RCscale_mono hc0 hfloor
  rw [RCscale_RCscale] at h3
  exact RCle_trans h1 (RCle_trans h2 h3)

end State

/-! ## 3. Along the dyadic trajectory: H2 ⟹ H1 -/

/-- **H2 ⟹ H1 along the trajectory.** `PathFamilyRadiusSurvival tr θ` with
`1 ≤ c0 θ m` (`m = tr.radiusFactor`) gives `PathEpsBound tr c0`. -/
theorem pathEpsBound_of_familyRadiusSurvival (tr : DyadicSmoothedTrajectory)
    (c0 theta : Q') (hc0 : (0 : Q') ≤ c0) (htheta : (0 : Q') ≤ theta)
    (hrate : (1 : Q') ≤ c0 * theta * Q'.ofNat tr.radiusFactor)
    (H2 : PathFamilyRadiusSurvival tr theta) : PathEpsBound tr c0 := by
  intro j
  have hw0 := tr.schedule.nome_pos j
  have hw1 := tr.schedule.nome_lt_one j
  have hfloor := RCle_trans (H2 j) (smoothedCoherent_norm_ge_family_response hw0 hw1
    (trajWidth j) (tr.faces j) (tr.coeff j) (tr.faces_spatial j) (tr.radius j))
  refine smoothedEpsBound_of_relativeFloor hw0 hw1 (trajWidth j) (tr.faces j) (tr.coeff j)
    (tr.faces_spatial j) (tr.radius j) j c0 theta hc0 htheta ?_ hfloor
  have hk : (0 : Q') ≤ c0 * theta := Q'.mul_nonneg _ _ hc0 htheta
  have hs := h1_ofNat_nonneg (side j)
  -- side ≤ (c0 θ m) side ≈ (c0 θ) (m side) ≤ (c0 θ) (m side + 1)
  have hA : Q'.ofNat (side j) ≤ c0 * theta * Q'.ofNat tr.radiusFactor * Q'.ofNat (side j) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hrate hs)
  have hB : c0 * theta * Q'.ofNat tr.radiusFactor * Q'.ofNat (side j) ≈
      c0 * theta * Q'.ofNat (tr.radiusFactor * side j) :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 0) (.mul (.var 1) (.var 2))) (by decide)
        (fun | 0 => c0 * theta | 1 => Q'.ofNat tr.radiusFactor | _ => Q'.ofNat (side j)))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (h1_ofNat_mul _ _)))
  have hC : c0 * theta * Q'.ofNat (tr.radiusFactor * side j) ≤
      c0 * theta * Q'.ofNat (tr.radiusFactor * side j + 1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (h1_ofNat_le_succ _) hk
  exact Q'.le_trans' _ _ _ hA (Q'.le_trans' _ _ _ (Q'.le_of_eqv hB) hC)

/-- **The A03 normalized-anchor package from H2 alone** (H1 is now derived).
Same conclusion as `path_normalized_anchor`, with H1 replaced by
`PathFamilyRadiusSurvival tr θ` and the scalar condition `1 ≤ c0 θ m`. -/
theorem path_normalized_anchor_of_familyRadiusSurvival (tr : DyadicSmoothedTrajectory)
    (c0 theta delta : Q') (a : Nat) (hc0pos : (0 : Q') ≤ c0) (htheta : (0 : Q') ≤ theta)
    (hrate : (1 : Q') ≤ c0 * theta * Q'.ofNat tr.radiusFactor)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta) (H2 : PathFamilyRadiusSurvival tr theta) :
    ∀ j : Nat, a ≤ j →
      completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
          (pathAnchor tr delta hdelta a j).normalized.val
          (pathAnchor tr delta hdelta a j).normalized.val = Rq 1 ∧
      (∀ i : Nat, RCle (Rq ((((1 : Q') - delta)^(side a))^i))
        (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
          (pathAnchor tr delta hdelta a j).normalized.val
          (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (i * side j)
            (pathAnchor tr delta hdelta a j).normalized.val))) ∧
      (∀ (i : Nat) (time : PositiveTimeValue),
        RCle (RCscale (spacing j) (realValue time)) (Rq (Q'.ofNat i)) →
        RCle (Rq ((((1 : Q') - delta)^(side a))^(i+1)))
          (bondCompletedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
            (pathAnchor tr delta hdelta a j).bondExcitation
            (action (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) time
              (pathAnchor tr delta hdelta a j).bondExcitation))) ∧
      (1 ≤ j → ∀ (epsilon : Q'), (0 : Q') < epsilon → ∀ time : PositiveTimeValue,
        RCle (RCscale (spacing j) (realValue time))
          (Rq (macroGeometricRadius (((1 : Q') - delta)^(side a)) epsilon)) →
        RCle (bondCompletedDistance (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
          (action (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) time
            (pathAnchor tr delta hdelta a j).bondExcitation)
          (pathAnchor tr delta hdelta a j).bondExcitation) (Rq epsilon)) :=
  path_normalized_anchor tr c0 delta a hdelta0 hdelta hc0
    (pathEpsBound_of_familyRadiusSurvival tr c0 theta hc0pos htheta hrate H2)

/-! ## 4. The gap screen: H1 caps every certified one-step rate -/

section Rate

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- OPEN for `r < 1` (NOT proved here): a one-step Rayleigh rate `r` for the
transfer step on the vacuum complement of THIS carrier,
`B(y, T y) ≤ r B(y, y)`. It is the carrier-level form of a lattice gap
`1 - r ≈ m_lat`. -/
def WilsonVacuumRayleighRate (r : Q') : Prop :=
  ∀ y : VacuumComplement hw0 hw1 (width := width),
    RCle (B y.val (T 1 y.val)) (RCscale r (B y.val y.val))

/-- Non-vacuity: the rate `r = 1` always holds (contractivity). -/
theorem wilsonVacuumRayleighRate_one : WilsonVacuumRayleighRate hw0 hw1 width 1 := by
  intro y
  rw [RCscale_one]
  have h := response_le_of_le hw0 hw1 width y.val (Nat.zero_le 1)
  rwa [completedTime_zero hw0 hw1] at h

/-- A Rayleigh rate is a LOWER bound on every one-step energy:
`(1 - r) B(y,y) ≤ B(y,y) - B(y, T y)`. -/
theorem oneStep_energy_ge_of_rayleighRate (r : Q')
    (H : WilsonVacuumRayleighRate hw0 hw1 width r)
    (y : VacuumComplement hw0 hw1 (width := width)) :
    RCle (RCscale (1-r) (B y.val y.val)) (RCsub (B y.val y.val) (B y.val (T 1 y.val))) :=
  h1_response_lower r _ _ (by rw [h1_sub_sub_self]; exact H y)

variable (qs : List Z4Plaq) (c : Z4Plaq → Q')
  (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width)

local notation "Y" M:arg => smoothedCoherentVector hw0 hw1 width qs c hqs M

/-- **H1 caps the certified rate (RC form).** -/
theorem epsBound_forces_rate_rc (M scale : Nat) (c0 r : Q')
    (H : WilsonVacuumRayleighRate hw0 hw1 width r)
    (heps : SmoothedCoherentEpsBound hw0 hw1 width qs c hqs M scale c0) :
    RCle (RCscale (Q'.ofNat (side scale) * (1-r)) (B (Y M) (Y M)))
      (RCscale c0 (B (Y M) (Y M))) := by
  have h : RCle (RCscale (1-r) (B (Y M) (Y M))) (smoothedEnergy hw0 hw1 width qs c hqs M) :=
    oneStep_energy_ge_of_rayleighRate hw0 hw1 width r H
      (smoothedCoherentState hw0 hw1 width qs c hqs M)
  have h' := RCscale_mono (h1_ofNat_nonneg (side scale)) h
  rw [RCscale_RCscale] at h'
  exact RCle_trans h' heps

/-- **H1 caps the certified rate (rational form).** With distinct faces and a
nonzero coefficient vector, `side * (1 - r) ≤ c0`. -/
theorem epsBound_forces_rate (hn : qs.Nodup)
    (hc : (0 : Q') < listQSum (fun face => c face*c face) qs)
    (M scale : Nat) (c0 r : Q')
    (H : WilsonVacuumRayleighRate hw0 hw1 width r)
    (heps : SmoothedCoherentEpsBound hw0 hw1 width qs c hqs M scale c0) :
    Q'.ofNat (side scale) * (1-r) ≤ c0 :=
  h1_coeff_le_of_scale_le (smoothedNormFloor_positive hw0 hw1 qs c hc M)
    (smoothedCoherent_norm_floor hw0 hw1 width qs c hqs hn M)
    (epsBound_forces_rate_rc hw0 hw1 width qs c hqs M scale c0 r H heps)

end Rate

/-- **Path gap screen.** H1 along the trajectory and ANY rates `r_j` certified on
the same carriers force `side_j (1 - r_j) ≤ c0` at every scale: the certified
one-step gap must close at least like `c0 / side_j`. In particular a fixed rate
`r < 1` along the path contradicts H1 once `side_j (1 - r) > c0`. -/
theorem path_epsBound_forces_rate (tr : DyadicSmoothedTrajectory) (c0 : Q') (r : Nat → Q')
    (H1 : PathEpsBound tr c0)
    (Hr : ∀ j, WilsonVacuumRayleighRate (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (trajWidth j) (r j)) :
    ∀ j, Q'.ofNat (side j) * (1 - r j) ≤ c0 := fun j =>
  epsBound_forces_rate (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j)
    (tr.faces j) (tr.coeff j) (tr.faces_spatial j) (tr.faces_nodup j) (tr.coeff_mass_pos j)
    (tr.radius j) j c0 (r j) (Hr j) (H1 j)

#print axioms boxSum_shift_telescope
#print axioms boxSum_le_const
#print axioms smoothedEnergy_telescope
#print axioms smoothed_tail_overlap_nonnegative
#print axioms smoothed_head_overlap_le_norm
#print axioms smoothedEnergy_le_familyNorm
#print axioms smoothedEpsBound_trivial
#print axioms smoothedEpsBound_of_relativeFloor
#print axioms pathEpsBound_of_familyRadiusSurvival
#print axioms path_normalized_anchor_of_familyRadiusSurvival
#print axioms WilsonVacuumRayleighRate
#print axioms wilsonVacuumRayleighRate_one
#print axioms oneStep_energy_ge_of_rayleighRate
#print axioms epsBound_forces_rate_rc
#print axioms epsBound_forces_rate
#print axioms path_epsBound_forces_rate

end YMGap.Continuum.BF4WilsonAllNomeH1FixedScale
