/-
# Time-smoothed coherent family state on the all-nome completed Wilson carrier

The EXISTING coherent signed spatial family `familyExcitation` (the original
completed-state pin of the literal family `familySpan width qs c`, whose
opposite-incidence angular geometry is the subject of
`BF4ExactSlabFixedSpatialFamilyCoherentEnergy`) is averaged in time with the
normalized box kernel of explicit smoothing radius `M`:

    Y_M = (1/(M+1)) * sum_{m=0}^{M} T(m) x,      x = familyExcitation.

The construction reuses `orbitSum` on the SAME completed carrier; no new
carrier, family or time operator is built. The radius `M` is a free natural
parameter, so a later schedule may let it grow with `side scale`.

Proved here: membership in the actual vacuum complement, the radius-zero pin
back to the unsmoothed family, the expansion of every response into the
original centered family moments, kernel positivity and unit mass,
nonnegativity and monotonicity of all responses, an unconditional norm floor
`(M+1)^(-2) * varianceFloor * sum c^2` (which DETERIORATES with M), the
same-carrier relative-energy survival compiler (the all-nome mirror of
`BF4ExactSlabFixedSpatialJointEnergySurvival.response_floor_of_relative_energy`,
which lives on the joint exact-slab carrier), and the macro-ratio adapters
for `response_shifted_block_geometric_lower`, the generic consumer behind
`BF4WilsonAllNomeDyadicNormalizedMacroRatio.normalizedAnchorResponse_block_floor`,
and for the P1 survival-floor compiler
`BF4WilsonAllNomeCompletedLogConvexity.macro_ratio_of_survival_floor`, whose
rational norm-floor input is discharged here by the unconditional floor.

OPEN, stated but NOT proved: `SmoothedCoherentEpsBound`, the relative one-step
energy bound eps <= c0/side for this state. Nothing here produces it; no
uniform survival, scaling trajectory, physical mass or continuum claim is made.
-/

import YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance
import YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyKineticUpper
import YMGap.Continuum.BF4WilsonAllNomeBilinearTime
import YMGap.Continuum.BF4WilsonAllNomeBlockResponseLower
import YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail
import YMGap.Continuum.BF4DyadicWilsonSquare
import YMGap.Continuum.RCSignedPairBudget
import YMGap.Continuum.BF4WilsonAllNomeCompletedLogConvexity

namespace YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces spatialFaces_nodup)
open YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity (varianceFloor varianceFloor_positive)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin (familyState)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion completedInner completedInner_nonnegative unitState)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedTime_zero completedTime_add VacuumComplement)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedAdd completedSmul completedZero)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedAdd_zero completedSmul_congr completedSmul_one)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
  (orbitSum responseSum orbitSum_pairing orbitSum_time orbitSum_orthogonal)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (mixedMoment_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail (mixedMoment_time_decreasing)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance
  (familyExcitation familyExcitation_norm_floor familyExcitation_correlator_pin)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyKineticUpper (time_loss_linear_bound)
open YMGap.Continuum.BF4WilsonAllNomeBlockResponseLower
  (response_shifted_block_geometric_lower)
open YMGap.Continuum.BF4WilsonAllNomeCompletedLogConvexity (macro_ratio_of_survival_floor)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)
local infix:50 " ≈ " => Q'.eqv

/-! ## Scalar helpers (local copies of the standard private lemmas) -/

private theorem sc_ofNat_succ_pos (M : Nat) : (0 : Q') < Q'.ofNat (M+1) := by
  change (0 : Int)*1 < ((M+1 : Nat) : Int)*1
  simp only [Int.mul_one]
  omega

private theorem sc_two_mul_ofNat (n : Nat) : Q'.ofNat (2*n) ≈ 2*Q'.ofNat n := by
  have h : 2*n = n+n := by omega
  rw [h]
  exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n n)
    (poly_identity_of_normal_eq (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
      (by decide) (fun _ => Q'.ofNat n))

private theorem sc_scale_rational (c q : Q') : RCscale c (Rq q) = Rq (c*q) := by
  rw [RCscale_mk]
  exact Quotient.sound (CRealAlg.ofQ'_mul c q).symm

private theorem sc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem sc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
      (Q'.eqv_of_eq (Q'.zero_add' (A.approx n)))))

private theorem sc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem sc_sub_nonnegative_of_le {a b : RC} (h : RCle b a) :
    RCnonneg (RCsub a b) := by
  have h' := RCadd_le_add h (RCle_refl (RCneg b))
  change RCle (RCsub b b) (RCsub a b) at h'
  rwa [sc_sub_self] at h'

private theorem sc_nonneg_add {a b : RC} (ha : RCnonneg a) (hb : RCnonneg b) :
    RCnonneg (RCadd a b) := by
  have h := RCadd_le_add ha hb
  rwa [sc_zero_add] at h

private theorem sc_scale_nonneg {r : Q'} (hr : (0 : Q') ≤ r) {a : RC}
    (ha : RCnonneg a) : RCnonneg (RCscale r a) := by
  have h := RCscale_mono hr ha
  rwa [RCscale_RCzero] at h

private theorem sc_response_lower (r : Q') (norm response : RC)
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

private theorem sc_remaining_fraction {r theta : Q'} (h : r+theta ≤ (1 : Q')) :
    theta ≤ 1-r := by
  have h' := Q'.add_le_add_right _ _ (-r) h
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun | 0 => r | _ => theta))) h'

/-! ## The smoothing kernel: explicit radius, positive weights, unit mass -/

/-- Box-kernel weight `1/(M+1)` for smoothing radius `M`. Computable data. -/
def smoothingWeight (M : Nat) : Q' :=
  Q'.recipPos (Q'.ofNat (M+1)) (sc_ofNat_succ_pos M)

theorem smoothingWeight_pos (M : Nat) : (0 : Q') < smoothingWeight M :=
  Q'.recipPos_pos _ _

theorem smoothingWeight_nonneg (M : Nat) : (0 : Q') ≤ smoothingWeight M :=
  Q'.le_of_lt (smoothingWeight_pos M)

theorem smoothingWeight_normalizes (M : Nat) :
    Q'.ofNat (M+1) * smoothingWeight M ≈ 1 :=
  Q'.mul_recipPos_eqv _ _

/-- The weighted lag list `[(r,M), (r,M-1), ..., (r,0)]`. -/
def boxKernel (r : Q') : Nat → List (Q' × Nat)
  | 0 => [(r,0)]
  | m+1 => (r,m+1) :: boxKernel r m

/-- Normalized box kernel of smoothing radius `M` (lags `0..M`). -/
def timeKernel (M : Nat) : List (Q' × Nat) := boxKernel (smoothingWeight M) M

/-- Total weight of a lag list. -/
def kernelMass : List (Q' × Nat) → Q'
  | [] => 0
  | a :: cs => a.1 + kernelMass cs

theorem boxKernel_weight (r : Q') :
    ∀ (M : Nat) (a : Q' × Nat), a ∈ boxKernel r M → a.1 = r
  | 0, a, h => by
      simp only [boxKernel, List.mem_singleton] at h
      rw [h]
  | m+1, a, h => by
      simp only [boxKernel, List.mem_cons] at h
      rcases h with h | h
      · rw [h]
      · exact boxKernel_weight r m a h

/-- Every smoothing weight is strictly positive. -/
theorem timeKernel_weight_pos (M : Nat) (a : Q' × Nat) (h : a ∈ timeKernel M) :
    (0 : Q') < a.1 := by
  rw [boxKernel_weight (smoothingWeight M) M a h]
  exact smoothingWeight_pos M

theorem boxKernel_mass (r : Q') :
    ∀ M : Nat, kernelMass (boxKernel r M) ≈ Q'.ofNat (M+1) * r
  | 0 => by
      change r + 0 ≈ Q'.ofNat (0+1) * r
      exact Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq (.add (.var 0) (.const 0))
          (.mul (.const 1) (.var 0)) (by decide) (fun _ => r))
        (Q'.mul_eqv_congr_right (1 : Q') (Q'.ofNat (0+1)) r (by decide))
  | m+1 => by
      change r + kernelMass (boxKernel r m) ≈ Q'.ofNat (m+1+1) * r
      have h1 : Q'.ofNat (m+1+1) ≈ Q'.ofNat (m+1) + 1 :=
        Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv (m+1) 1)
          (Q'.add_eqv_congr_left _ _ _ (by decide))
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (boxKernel_mass r m))
        (Q'.eqv_trans _ _ _
          (poly_identity_of_normal_eq (.add (.var 0) (.mul (.var 1) (.var 0)))
            (.mul (.add (.var 1) (.const 1)) (.var 0)) (by decide)
            (fun | 0 => r | _ => Q'.ofNat (m+1)))
          (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm h1)))

/-- Normalisation: the smoothing kernel has unit total mass. -/
theorem timeKernel_mass (M : Nat) : kernelMass (timeKernel M) ≈ 1 :=
  Q'.eqv_trans _ _ _ (boxKernel_mass _ M) (smoothingWeight_normalizes M)

/-- Positive box sums of nonnegative responses are nonnegative. -/
theorem boxSum_nonneg {r : Q'} (hr : (0 : Q') ≤ r) (f : Nat → RC)
    (hf : ∀ n, RCnonneg (f n)) : ∀ M : Nat, RCnonneg (responseSum (boxKernel r M) f)
  | 0 => by
      change RCnonneg (RCadd (RCscale r (f 0)) RCzero)
      rw [sc_add_zero]
      exact sc_scale_nonneg hr (hf 0)
  | m+1 => by
      change RCnonneg (RCadd (RCscale r (f (m+1))) (responseSum (boxKernel r m) f))
      exact sc_nonneg_add (sc_scale_nonneg hr (hf (m+1))) (boxSum_nonneg hr f hf m)

/-- A positive box sum dominates its lag-zero term. -/
theorem boxSum_ge_origin {r : Q'} (hr : (0 : Q') ≤ r) (f : Nat → RC)
    (hf : ∀ n, RCnonneg (f n)) :
    ∀ M : Nat, RCle (RCscale r (f 0)) (responseSum (boxKernel r M) f)
  | 0 => by
      change RCle (RCscale r (f 0)) (RCadd (RCscale r (f 0)) RCzero)
      rw [sc_add_zero]
      exact RCle_refl _
  | m+1 => by
      change RCle (RCscale r (f 0))
        (RCadd (RCscale r (f (m+1))) (responseSum (boxKernel r m) f))
      have h := RCadd_le_add (sc_scale_nonneg hr (hf (m+1))) (boxSum_ge_origin hr f hf m)
      rwa [sc_zero_add] at h

/-- Unconditional norm-floor constant `(M+1)^(-2) * varianceFloor * sum c^2`.
It deteriorates like `(M+1)^(-2)`; it is not a uniform floor. -/
def smoothedNormFloor {w : Q'} (hw0 : (0 : Q') < w) (qs : List Z4Plaq)
    (c : Z4Plaq → Q') (M : Nat) : Q' :=
  smoothingWeight M * smoothingWeight M *
    (varianceFloor w hw0 * listQSum (fun face => c face*c face) qs)

theorem smoothedNormFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hc : (0 : Q') < listQSum (fun face => c face*c face) qs) (M : Nat) :
    (0 : Q') < smoothedNormFloor hw0 qs c M :=
  Q'.mul_pos (Q'.mul_pos (smoothingWeight_pos M) (smoothingWeight_pos M))
    (Q'.mul_pos (varianceFloor_positive hw0 hw1) hc)

/-! ## The smoothed coherent state -/

section State

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
  (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "x0" => Subtype.val (familyExcitation hw0 hw1 width qs c hqs)

/-- Time smoothing of radius `M` applied to the EXISTING coherent family vector
on the SAME completed carrier. -/
def smoothedCoherentVector (M : Nat) : Completion hw0 hw1 width :=
  orbitSum hw0 hw1 (familyExcitation hw0 hw1 width qs c hqs).val (timeKernel M)

local notation "Y" M:arg => smoothedCoherentVector hw0 hw1 width qs c hqs M

/-- Well-definedness as a state of the actual vacuum complement. -/
def smoothedCoherentState (M : Nat) : VacuumComplement hw0 hw1 (width := width) :=
  ⟨Y M, orbitSum_orthogonal hw0 hw1 x0
    (familyExcitation hw0 hw1 width qs c hqs).property (timeKernel M)⟩

/-- Response `R_M(n) = B(Y_M, T(n) Y_M)`. -/
def smoothedResponse (M n : Nat) : RC := B (Y M) (T n (Y M))

/-- One-step energy `E_M = R_M(0) - R_M(1)`. -/
def smoothedEnergy (M : Nat) : RC := RCsub (B (Y M) (Y M)) (B (Y M) (T 1 (Y M)))

theorem smoothedCoherentState_val (M : Nat) :
    (smoothedCoherentState hw0 hw1 width qs c hqs M).val = Y M := rfl

theorem smoothedCoherent_orthogonal (M : Nat) : B U (Y M) = RCzero :=
  (smoothedCoherentState hw0 hw1 width qs c hqs M).property

/-- Radius zero recovers the unsmoothed coherent family exactly. -/
theorem smoothedCoherentVector_radius_zero : Y 0 = x0 := by
  have hw : smoothingWeight 0 ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (by decide : (1 : Q') ≈ Q'.ofNat (0+1)))
        (smoothingWeight_normalizes 0))
  show completedAdd hw0 hw1 (completedSmul hw0 hw1 (smoothingWeight 0) (T 0 x0))
      (completedZero hw0 hw1 width) = x0
  rw [completedAdd_zero hw0 hw1, completedSmul_congr hw0 hw1 hw, completedSmul_one hw0 hw1,
    completedTime_zero hw0 hw1]

/-- Time commutes with the smoothing. -/
theorem smoothedCoherentVector_time (M n : Nat) :
    T n (Y M) = orbitSum hw0 hw1 (T n x0) (timeKernel M) :=
  orbitSum_time hw0 hw1 x0 (timeKernel M) n

/-- Every smoothed response is the explicit double kernel sum of the
unsmoothed family responses; all signed cross terms remain. -/
theorem smoothedResponse_orbit_expand (M n : Nat) :
    smoothedResponse hw0 hw1 width qs c hqs M n =
      responseSum (timeKernel M) (fun m => responseSum (timeKernel M)
        (fun k => B x0 (T (m+k+n) x0))) := by
  unfold smoothedResponse
  rw [smoothedCoherentVector_time]
  unfold smoothedCoherentVector
  rw [orbitSum_pairing]
  apply congrArg (responseSum (timeKernel M))
  funext m
  apply congrArg (responseSum (timeKernel M))
  funext k
  rw [completedTime_add hw0 hw1 (m+k) n x0]

/-- Pin to the ORIGINAL centered family time moments of the literal family. -/
theorem smoothedResponse_pin (M n : Nat) :
    smoothedResponse hw0 hw1 width qs c hqs M n =
      responseSum (timeKernel M) (fun m => responseSum (timeKernel M)
        (fun k => Quotient.mk crealSetoid (centeredTimeMoment hw0 hw1 (m+k+n)
          (familyState width qs c hqs) (familyState width qs c hqs)))) := by
  rw [smoothedResponse_orbit_expand]
  apply congrArg (responseSum (timeKernel M))
  funext m
  apply congrArg (responseSum (timeKernel M))
  funext k
  exact familyExcitation_correlator_pin hw0 hw1 width qs c hqs (m+k+n)

theorem smoothedResponse_zero (M : Nat) :
    smoothedResponse hw0 hw1 width qs c hqs M 0 = B (Y M) (Y M) := by
  unfold smoothedResponse
  rw [completedTime_zero hw0 hw1]

/-- Nonnegativity of every response of the smoothed state. -/
theorem smoothedResponse_nonnegative (M n : Nat) :
    RCnonneg (smoothedResponse hw0 hw1 width qs c hqs M n) :=
  mixedMoment_nonnegative hw0 hw1 (Y M) n 0

theorem smoothedNorm_nonnegative (M : Nat) : RCnonneg (B (Y M) (Y M)) :=
  completedInner_nonnegative hw0 hw1 (Y M)

/-- Responses decrease in integer time. -/
theorem smoothedResponse_antitone (M n : Nat) :
    RCle (smoothedResponse hw0 hw1 width qs c hqs M (n+1))
      (smoothedResponse hw0 hw1 width qs c hqs M n) :=
  mixedMoment_time_decreasing hw0 hw1 (Y M) n 0

theorem smoothedResponse_le_norm (M : Nat) :
    ∀ n : Nat, RCle (smoothedResponse hw0 hw1 width qs c hqs M n) (B (Y M) (Y M))
  | 0 => by
      rw [smoothedResponse_zero]
      exact RCle_refl _
  | n+1 => RCle_trans (smoothedResponse_antitone hw0 hw1 width qs c hqs M n)
      (smoothedResponse_le_norm M n)

theorem smoothedEnergy_nonnegative (M : Nat) :
    RCnonneg (smoothedEnergy hw0 hw1 width qs c hqs M) :=
  sc_sub_nonnegative_of_le (smoothedResponse_le_norm hw0 hw1 width qs c hqs M 1)

/-- The smoothed norm dominates `(M+1)^(-2)` times the unsmoothed norm. -/
theorem smoothedCoherent_norm_ge_family (M : Nat) :
    RCle (RCscale (smoothingWeight M * smoothingWeight M) (B x0 x0)) (B (Y M) (Y M)) := by
  have hr := smoothingWeight_nonneg M
  have hpos : ∀ k, RCnonneg (B x0 (T k x0)) := fun k =>
    mixedMoment_nonnegative hw0 hw1 x0 k 0
  rw [← smoothedResponse_zero hw0 hw1 width qs c hqs M,
    smoothedResponse_orbit_expand hw0 hw1 width qs c hqs M 0]
  have hinner : ∀ m, RCnonneg (responseSum (timeKernel M)
      (fun k => B x0 (T (m+k+0) x0))) := fun m =>
    boxSum_nonneg hr (fun k => B x0 (T (m+k+0) x0)) (fun k => hpos (m+k+0)) M
  have houter := boxSum_ge_origin hr
    (fun m => responseSum (timeKernel M) (fun k => B x0 (T (m+k+0) x0))) hinner M
  have hfirst : RCle (RCscale (smoothingWeight M) (B x0 x0))
      (responseSum (timeKernel M) (fun k => B x0 (T (0+k+0) x0))) := by
    have h := boxSum_ge_origin hr (fun k => B x0 (T (0+k+0) x0))
      (fun k => hpos (0+k+0)) M
    have h0 : B x0 (T (0+0+0) x0) = B x0 x0 := by
      show B x0 (T 0 x0) = B x0 x0
      rw [completedTime_zero hw0 hw1]
    rw [← h0]
    exact h
  have h2 := RCscale_mono hr hfirst
  rw [RCscale_RCscale] at h2
  exact RCle_trans h2 houter

/-- Unconditional norm floor of the smoothed coherent state (distinct faces). -/
theorem smoothedCoherent_norm_floor (hn : qs.Nodup) (M : Nat) :
    RCle (Rq (smoothedNormFloor hw0 qs c M)) (B (Y M) (Y M)) := by
  have hf := familyExcitation_norm_floor hw0 hw1 width qs c hqs hn
  have hs := RCscale_mono
    (Q'.mul_nonneg _ _ (smoothingWeight_nonneg M) (smoothingWeight_nonneg M)) hf
  rw [sc_scale_rational] at hs
  exact RCle_trans hs (smoothedCoherent_norm_ge_family hw0 hw1 width qs c hqs M)

/-! ## Relative-energy survival (all-nome mirror of JointEnergySurvival:97/112) -/

/-- A relative one-step energy bound retains a fraction of the SAME norm. -/
theorem smoothed_response_ge_fraction_of_relative_energy (M n : Nat) (delta theta : Q')
    (hbudget : Q'.ofNat n*delta+theta ≤ (1 : Q'))
    (henergy : RCle (smoothedEnergy hw0 hw1 width qs c hqs M)
      (RCscale delta (B (Y M) (Y M)))) :
    RCle (RCscale theta (B (Y M) (Y M))) (smoothedResponse hw0 hw1 width qs c hqs M n) := by
  have hn := RCle_trans (time_loss_linear_bound hw0 hw1 (Y M) n)
    (RCscale_mono (Q'.ofNat_nonneg n) henergy)
  rw [RCscale_RCscale] at hn
  exact RCle_trans
    (RCscale_scalar_mono (sc_remaining_fraction hbudget)
      (completedInner_nonnegative hw0 hw1 (Y M)))
    (sc_response_lower (Q'.ofNat n*delta) (B (Y M) (Y M))
      (smoothedResponse hw0 hw1 width qs c hqs M n) hn)

/-- Same statement shape as `response_floor_of_relative_energy`, on this state. -/
theorem smoothed_response_floor_of_relative_energy (M n : Nat) (delta theta v : Q')
    (htheta : (0 : Q') ≤ theta)
    (hbudget : Q'.ofNat n*delta+theta ≤ (1 : Q'))
    (hfloor : RCle (Rq v) (B (Y M) (Y M)))
    (henergy : RCle (smoothedEnergy hw0 hw1 width qs c hqs M)
      (RCscale delta (B (Y M) (Y M)))) :
    RCle (Rq (theta*v)) (smoothedResponse hw0 hw1 width qs c hqs M n) := by
  have hv := RCscale_mono htheta hfloor
  rw [sc_scale_rational] at hv
  exact RCle_trans hv
    (smoothed_response_ge_fraction_of_relative_energy hw0 hw1 width qs c hqs
      M n delta theta hbudget henergy)

/-- The unconditional norm floor plugged in: only the relative energy remains. -/
theorem smoothed_response_floor_of_relative_energy_family (hn : qs.Nodup)
    (M n : Nat) (delta theta : Q') (htheta : (0 : Q') ≤ theta)
    (hbudget : Q'.ofNat n*delta+theta ≤ (1 : Q'))
    (henergy : RCle (smoothedEnergy hw0 hw1 width qs c hqs M)
      (RCscale delta (B (Y M) (Y M)))) :
    RCle (Rq (theta * smoothedNormFloor hw0 qs c M))
      (smoothedResponse hw0 hw1 width qs c hqs M n) :=
  smoothed_response_floor_of_relative_energy hw0 hw1 width qs c hqs M n delta theta _
    htheta hbudget (smoothedCoherent_norm_floor hw0 hw1 width qs c hqs hn M) henergy

/-! ## Macro-ratio adapters (shape of DyadicNormalizedMacroRatio:132) -/

/-- The macroscopic ratio `kappa*R(s) <= R(2s)`, `s = side scale`, for THIS
state. This is the hypothesis shape consumed at
`BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132`, here for `Y_M`. -/
def SmoothedMacroRatio (M scale : Nat) (kappa : Q') : Prop :=
  RCle (RCscale kappa (smoothedResponse hw0 hw1 width qs c hqs M (side scale)))
    (smoothedResponse hw0 hw1 width qs c hqs M (2*side scale))

/-- A macro ratio propagates geometrically to every later block. -/
theorem smoothed_macro_block_floor (M scale : Nat) (kappa : Q')
    (hkappa : (0 : Q') ≤ kappa)
    (hratio : SmoothedMacroRatio hw0 hw1 width qs c hqs M scale kappa) (j : Nat) :
    RCle (RCscale (kappa^j) (smoothedResponse hw0 hw1 width qs c hqs M (side scale)))
      (smoothedResponse hw0 hw1 width qs c hqs M (side scale + j*side scale)) := by
  have hfirst : RCle (RCscale kappa (B (Y M) (T (side scale) (Y M))))
      (B (Y M) (T (side scale + side scale) (Y M))) := by
    rw [show side scale + side scale = 2*side scale by omega]
    exact hratio
  exact response_shifted_block_geometric_lower hw0 hw1 (Y M) kappa hkappa
    (side scale) (side scale) hfirst j

/-- Survival floor at `s` plus a macro ratio gives explicit block floors. -/
theorem smoothed_macro_block_response_floor (M scale : Nat) (kappa v : Q')
    (hkappa : (0 : Q') ≤ kappa)
    (hratio : SmoothedMacroRatio hw0 hw1 width qs c hqs M scale kappa)
    (hsurv : RCle (Rq v) (smoothedResponse hw0 hw1 width qs c hqs M (side scale)))
    (j : Nat) :
    RCle (Rq (kappa^j * v))
      (smoothedResponse hw0 hw1 width qs c hqs M (side scale + j*side scale)) := by
  have h := RCscale_mono (Q'.pow_nonneg kappa hkappa j) hsurv
  rw [sc_scale_rational] at h
  exact RCle_trans h (smoothed_macro_block_floor hw0 hw1 width qs c hqs M scale kappa
    hkappa hratio j)

/-- Linear-loss route: a relative energy paying lag `2s` gives the macro ratio
directly (no log-convexity or Jensen step; those are P1/P2). -/
theorem smoothed_macroRatio_of_relative_energy (M scale : Nat) (delta kappa : Q')
    (hkappa : (0 : Q') ≤ kappa)
    (hbudget : Q'.ofNat (2*side scale)*delta + kappa ≤ (1 : Q'))
    (henergy : RCle (smoothedEnergy hw0 hw1 width qs c hqs M)
      (RCscale delta (B (Y M) (Y M)))) :
    SmoothedMacroRatio hw0 hw1 width qs c hqs M scale kappa :=
  RCle_trans (RCscale_mono hkappa (smoothedResponse_le_norm hw0 hw1 width qs c hqs M
      (side scale)))
    (smoothed_response_ge_fraction_of_relative_energy hw0 hw1 width qs c hqs
      M (2*side scale) delta kappa hbudget henergy)

/-! ## The remaining OPEN hypothesis -/

/-- OPEN (not proved anywhere): relative one-step energy of the smoothed
coherent state at most `c0/side`, written without division:

    side(scale) * (R_M(0) - R_M(1)) <= c0 * R_M(0).

Producing this along a justified schedule (side = 2^scale, nome per asymptotic
freedom, width >> side, radius `M` growing with side) is the P5 research step.
It is an explicit hypothesis for consumers to supply; nothing here asserts it. -/
def SmoothedCoherentEpsBound (M scale : Nat) (c0 : Q') : Prop :=
  RCle (RCscale (Q'.ofNat (side scale)) (smoothedEnergy hw0 hw1 width qs c hqs M))
    (RCscale c0 (B (Y M) (Y M)))

/-- Conditional consumer: the open bound gives survival at lag `side`. -/
theorem smoothed_survival_of_epsBound (M scale : Nat) (c0 theta : Q')
    (heps : SmoothedCoherentEpsBound hw0 hw1 width qs c hqs M scale c0)
    (hbudget : c0 + theta ≤ (1 : Q')) :
    RCle (RCscale theta (B (Y M) (Y M)))
      (smoothedResponse hw0 hw1 width qs c hqs M (side scale)) := by
  have hn := RCle_trans (time_loss_linear_bound hw0 hw1 (Y M) (side scale)) heps
  exact RCle_trans
    (RCscale_scalar_mono (sc_remaining_fraction hbudget)
      (completedInner_nonnegative hw0 hw1 (Y M)))
    (sc_response_lower c0 (B (Y M) (Y M))
      (smoothedResponse hw0 hw1 width qs c hqs M (side scale)) hn)

theorem smoothed_survival_floor_of_epsBound (hn : qs.Nodup) (M scale : Nat)
    (c0 theta : Q') (htheta : (0 : Q') ≤ theta)
    (heps : SmoothedCoherentEpsBound hw0 hw1 width qs c hqs M scale c0)
    (hbudget : c0 + theta ≤ (1 : Q')) :
    RCle (Rq (theta * smoothedNormFloor hw0 qs c M))
      (smoothedResponse hw0 hw1 width qs c hqs M (side scale)) := by
  have hv := RCscale_mono htheta (smoothedCoherent_norm_floor hw0 hw1 width qs c hqs hn M)
  rw [sc_scale_rational] at hv
  exact RCle_trans hv
    (smoothed_survival_of_epsBound hw0 hw1 width qs c hqs M scale c0 theta heps hbudget)

/-- Conditional consumer: the open bound with `2*c0 + kappa <= 1` gives the
macro ratio for this state (linear loss only; sharper Jensen form is P2). -/
theorem smoothed_macroRatio_of_epsBound (M scale : Nat) (c0 kappa : Q')
    (hkappa : (0 : Q') ≤ kappa)
    (heps : SmoothedCoherentEpsBound hw0 hw1 width qs c hqs M scale c0)
    (hbudget : 2*c0 + kappa ≤ (1 : Q')) :
    SmoothedMacroRatio hw0 hw1 width qs c hqs M scale kappa := by
  have hlin := time_loss_linear_bound hw0 hw1 (Y M) (2*side scale)
  rw [RCSignedPairBudget.scale_congr (sc_two_mul_ofNat (side scale)),
    ← RCscale_RCscale] at hlin
  have h2 := RCle_trans hlin (RCscale_mono (by decide : (0 : Q') ≤ 2) heps)
  rw [RCscale_RCscale] at h2
  exact RCle_trans
    (RCscale_mono hkappa (smoothedResponse_le_norm hw0 hw1 width qs c hqs M (side scale)))
    (RCle_trans
      (RCscale_scalar_mono (sc_remaining_fraction hbudget)
        (completedInner_nonnegative hw0 hw1 (Y M)))
      (sc_response_lower (2*c0) (B (Y M) (Y M))
        (smoothedResponse hw0 hw1 width qs c hqs M (2*side scale)) h2))

/-! ## Through the landed P1 survival-floor compiler (log-convexity) -/

/-- The unconditional positive norm floor discharges the `hq/hnorm` inputs of
`BF4WilsonAllNomeCompletedLogConvexity.macro_ratio_of_survival_floor` for this
state: a survival floor at lag `side = 2u` gives the macro ratio. -/
theorem smoothed_macroRatio_of_survival_floor (hn : qs.Nodup)
    (hc : (0 : Q') < listQSum (fun face => c face*c face) qs)
    (M scale u : Nat) (hs : side scale = 2*u) (kappa : Q')
    (hfloor : RCle (RCscale kappa (B (Y M) (Y M)))
      (smoothedResponse hw0 hw1 width qs c hqs M (side scale))) :
    SmoothedMacroRatio hw0 hw1 width qs c hqs M scale kappa := by
  have h := macro_ratio_of_survival_floor hw0 hw1 width (Y M) u kappa
    (smoothedNormFloor hw0 qs c M) (smoothedNormFloor_positive hw0 hw1 qs c hc M)
    (smoothedCoherent_norm_floor hw0 hw1 width qs c hqs hn M)
    (by rw [← hs]; exact hfloor)
  unfold SmoothedMacroRatio smoothedResponse
  rw [hs, show 2*(2*u) = 4*u by omega]
  exact h

/-- The OPEN bound with `c0 + kappa <= 1` gives the macro ratio for this state
through linear loss plus P1 log-convexity (kappa = 1 - c0 rather than 1 - 2c0). -/
theorem smoothed_macroRatio_of_epsBound_logConvex (hn : qs.Nodup)
    (hc : (0 : Q') < listQSum (fun face => c face*c face) qs)
    (M scale u : Nat) (hs : side scale = 2*u) (c0 kappa : Q')
    (heps : SmoothedCoherentEpsBound hw0 hw1 width qs c hqs M scale c0)
    (hbudget : c0 + kappa ≤ (1 : Q')) :
    SmoothedMacroRatio hw0 hw1 width qs c hqs M scale kappa :=
  smoothed_macroRatio_of_survival_floor hw0 hw1 width qs c hqs hn hc M scale u hs kappa
    (smoothed_survival_of_epsBound hw0 hw1 width qs c hqs M scale c0 kappa heps hbudget)

end State

/-! ## Zero-momentum instance: every spatial face, unit coefficient -/

section ZeroMomentum

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

/-- The zero-momentum translate sum over ALL spatial faces, smoothed. -/
def zeroMomentumSmoothedState (M : Nat) : VacuumComplement hw0 hw1 (width := width) :=
  smoothedCoherentState hw0 hw1 width (spatialFaces width) (fun _ => 1) (fun _ hp => hp) M

theorem zeroMomentumSmoothed_norm_floor (M : Nat) :
    RCle (Rq (smoothedNormFloor hw0 (spatialFaces width) (fun _ => 1) M))
      (completedInner hw0 hw1 (zeroMomentumSmoothedState hw0 hw1 width M).val
        (zeroMomentumSmoothedState hw0 hw1 width M).val) :=
  smoothedCoherent_norm_floor hw0 hw1 width (spatialFaces width) (fun _ => 1)
    (fun _ hp => hp) (spatialFaces_nodup width) M

end ZeroMomentum

end YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState

#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothingWeight
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.timeKernel
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.timeKernel_weight_pos
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.timeKernel_mass
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.boxSum_nonneg
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.boxSum_ge_origin
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothedCoherentVector
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothedCoherentState
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothedCoherent_orthogonal
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothedCoherentVector_radius_zero
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothedCoherentVector_time
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothedResponse_orbit_expand
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothedResponse_pin
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothedResponse_nonnegative
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothedResponse_antitone
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothedResponse_le_norm
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothedEnergy_nonnegative
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothedCoherent_norm_ge_family
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothedCoherent_norm_floor
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothedNormFloor_positive
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothed_response_ge_fraction_of_relative_energy
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothed_response_floor_of_relative_energy
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothed_response_floor_of_relative_energy_family
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.SmoothedMacroRatio
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothed_macro_block_floor
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothed_macro_block_response_floor
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothed_macroRatio_of_relative_energy
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.SmoothedCoherentEpsBound
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothed_survival_of_epsBound
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothed_survival_floor_of_epsBound
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothed_macroRatio_of_epsBound
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothed_macroRatio_of_survival_floor
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.smoothed_macroRatio_of_epsBound_logConvex
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.zeroMomentumSmoothedState
#print axioms YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState.zeroMomentumSmoothed_norm_floor
