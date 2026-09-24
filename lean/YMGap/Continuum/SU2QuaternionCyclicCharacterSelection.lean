/-
# One-channel character step for the cyclic heat expansion

This is the actual fresh-output conditional polynomial obtained by inserting
one dimension-normalized character channel and integrating the old head.  The
support statement is coefficient-level and keeps every spectator variable.

The nome-one cutoff recurrences below expose this channel as the exact
difference of two consecutive actual cyclic heat steps.  They are the
coefficient-level seam used to select a computed harmonic branch by finite
prefix subtraction; no commuting family of Fischer projections is assumed.
-/

import YMGap.Continuum.SU2QuaternionCharacterProductPositive
import YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
import YMGap.Continuum.RenormalizedContinuumZ1

namespace YMGap.Continuum.SU2QuaternionCyclicCharacterSelection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
open YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionCharacterProductPositive
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatCyclicFold
open YMGap.Continuum.RenormalizedContinuumZ1
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.RGTransport (qpow)

local infix:50 " ≈ " => Q'.eqv

/-- Insert one normalized character between the old head and a fresh last
block, then integrate and delete the old head. -/
def characterCycleStep (n degree : Nat) (p : RatPoly) : RatPoly :=
  partialHaarHead (polyMul (normalizedCharacterAt 0 n degree) p)

/-- The actual one-character cyclic step stays on the original `n`-block
window. -/
theorem characterCycleStep_supported (n degree : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (characterCycleStep n degree p) := by
  unfold characterCycleStep
  apply partialHaarHead_supported (blocks := n)
  exact supported_polyMul
    (normalizedCharacterAt_supported (by omega : 0 < n+1) (by omega : n < n+1))
    (fun term ht => Nat.le_trans (hp term ht) (Nat.mul_le_mul_left 4 (by omega)))

private theorem finitePolySum_append {A : Type} (f : A → RatPoly) :
    ∀ xs ys : List A,
      finitePolySum f (xs ++ ys) = polyAdd (finitePolySum f xs) (finitePolySum f ys)
  | [], _ => rfl
  | _ :: xs, ys => by
      simp only [List.cons_append, finitePolySum, finitePolySum_append f xs ys,
        polyAdd, List.append_assoc]

private theorem finitePolySum_congr {A : Type} (f g : A → RatPoly) :
    ∀ xs : List A, (∀ a, a ∈ xs → RatPolyCoeffEqv (f a) (g a)) →
      RatPolyCoeffEqv (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => RatPolyCoeffEqv.refl _
  | a::xs, h => (h a List.mem_cons_self).add
      (finitePolySum_congr f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem heatAt_one_channels (left right K : Nat) :
    RatPolyCoeffEqv (heatAt left right 1 K)
      (finitePolySum (normalizedCharacterAt left right) (List.range (K+1))) := by
  apply finitePolySum_congr
  intro d hd
  rw [coeffAt_heatKernelPacket (List.mem_range.mp hd)]
  exact RatPolyCoeffEqv.smul_coefficient (coeffW_at_one_eqv d) _

/-- At nome one, increasing the cutoff by one appends exactly one normalized
character channel.  This is the coefficient-level input for finite-prefix
subtraction. -/
theorem heatAt_one_succ (left right degree : Nat) :
    RatPolyCoeffEqv (heatAt left right 1 (degree+1))
      (polyAdd (heatAt left right 1 degree)
        (normalizedCharacterAt left right (degree+1))) := by
  apply (heatAt_one_channels left right (degree+1)).trans
  rw [List.range_succ, finitePolySum_append]
  simpa only [finitePolySum, polyAdd, polyZero, List.append_nil] using
    (heatAt_one_channels left right degree).symm.add
      (RatPolyCoeffEqv.refl (normalizedCharacterAt left right (degree+1)))

/-- The cutoff-zero nome-one packet is the normalized trivial character. -/
theorem heatAt_one_zero (left right : Nat) :
    RatPolyCoeffEqv (heatAt left right 1 0)
      (normalizedCharacterAt left right 0) := by
  simpa only [Nat.zero_add, List.range_succ, List.range_zero, List.nil_append,
    finitePolySum, polyAdd, List.append_nil] using heatAt_one_channels left right 0

/-- Polynomial recurrence for the actual conditional steps at nome one. -/
theorem cycleStep_one_succ (n degree : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (cycleStep n 1 (degree+1) p)
      (polyAdd (cycleStep n 1 degree p) (characterCycleStep n (degree+1) p)) := by
  unfold cycleStep characterCycleStep
  have h := partialHaarHead_congr ((heatAt_one_succ 0 n degree).mul_right p)
  rw [polyMul_add_left_exact, partialHaarHead_add] at h
  exact h

/-- The first nome-one conditional step is exactly the trivial-character
cycle step. -/
theorem cycleStep_one_zero (n : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (cycleStep n 1 0 p) (characterCycleStep n 0 p) := by
  unfold cycleStep characterCycleStep
  exact partialHaarHead_congr ((heatAt_one_zero 0 n).mul_right p)

private theorem sum_congr_local (f g : Nat → Q') : ∀ xs : List Nat,
    (∀ r, r ∈ xs → f r ≈ g r) → qListSum (xs.map f) ≈ qListSum (xs.map g)
  | [], _ => Q'.eqv_refl _
  | r :: rs, h => Q'.add_eqv_congr' (h r List.mem_cons_self)
      (sum_congr_local f g rs (fun s hs => h s (List.mem_cons_of_mem r hs)))

private theorem sum_add_local (f g : Nat → Q') : ∀ xs : List Nat,
    qListSum (xs.map fun d => f d + g d) ≈ qListSum (xs.map f) + qListSum (xs.map g)
  | [] => Q'.eqv_refl _
  | d::ds => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_add_local f g ds))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
        (by decide) (fun | 0 => f d | 1 => g d | 2 => qListSum (ds.map f) | _ => qListSum (ds.map g)))

private theorem sum_pick_absent (d : Nat) (v : Q') : ∀ xs : List Nat, d ∉ xs →
    qListSum (xs.map fun r => if r=d then v else 0) ≈ 0
  | [], _ => Q'.eqv_refl _
  | r::rs, h => by
      have hrd : r ≠ d := fun he => h (he ▸ List.mem_cons_self)
      simp only [List.map_cons, qListSum, if_neg hrd]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_pick_absent d v rs
          (fun hr => h (List.mem_cons_of_mem r hr)))) (Q'.eqv_of_eq (Q'.zero_add' _))

private theorem sum_pick (d : Nat) (v : Q') : ∀ xs : List Nat, xs.Nodup → d ∈ xs →
    qListSum (xs.map fun r => if r=d then v else 0) ≈ v
  | [], _, h => by contradiction
  | r::rs, hn, hd => by
      by_cases he : r=d
      · subst r
        simp only [List.map_cons, qListSum]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_pick_absent d v rs (List.nodup_cons.mp hn).1))
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · simp only [List.map_cons, qListSum, if_neg he]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_pick d v rs
            (List.nodup_cons.mp hn).2 ((List.mem_cons.mp hd).resolve_left (Ne.symm he))))
          (Q'.eqv_of_eq (Q'.zero_add' _))

private theorem attenuation_one_of_le {r K : Nat} (h : r ≤ K) :
    attenuation 1 K r ≈ 1 := by
  unfold attenuation
  rw [if_pos h]
  exact qpow_one_eqv_one _

private theorem attenuation_one_of_not_le {r K : Nat} (h : ¬ r ≤ K) :
    attenuation 1 K r ≈ 0 := by
  unfold attenuation
  rw [if_neg h]
  exact Q'.eqv_refl _

private theorem endpoint_weight (K r : Nat) (b : Q') :
    attenuation 1 K r * b ≈ if r ≤ K then b else 0 := by
  by_cases h : r ≤ K
  · rw [if_pos h]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (attenuation_one_of_le h)) (Q'.one_mul_eqv _)
  · rw [if_neg h]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (attenuation_one_of_not_le h)) (Q'.zero_mul_eqv _)

private theorem endpoint_step (b : Nat → Q') (k : Nat) (xs : List Nat)
    (hn : xs.Nodup) (hd : k+1 ∈ xs) :
    qListSum (xs.map fun r => attenuation 1 (k+1) r * b r) ≈
      qListSum (xs.map fun r => attenuation 1 k r * b r) + b (k+1) := by
  have hpoint (r : Nat) : attenuation 1 (k+1) r * b r ≈
      attenuation 1 k r * b r + (if r=k+1 then b (k+1) else 0) := by
    apply Q'.eqv_trans _ _ _ (endpoint_weight (k+1) r (b r))
    apply Q'.eqv_trans _ _ _ ?_ (Q'.add_eqv_congr' (endpoint_weight k r (b r)).symm (Q'.eqv_refl _))
    by_cases he : r=k+1
    · subst r
      simp only [Nat.le_refl, if_true, if_neg (show ¬ k+1 ≤ k by omega)]
      exact (Q'.eqv_of_eq (Q'.zero_add' _)).symm
    · by_cases hle : r ≤ k
      · simp only [if_neg he, if_pos hle, if_pos (show r ≤ k+1 by omega)]
        exact (Q'.eqv_of_eq (Q'.add_zero' _)).symm
      · simp only [if_neg he, if_neg hle, if_neg (show ¬ r ≤ k+1 by omega)]
        exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ (sum_congr_local _ _ xs (fun r _ => hpoint r))
    (Q'.eqv_trans _ _ _ (sum_add_local _ _ xs)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_pick (k+1) (b (k+1)) xs hn hd)))

private theorem endpoint_zero (b : Nat → Q') (xs : List Nat)
    (hn : xs.Nodup) (hd : 0 ∈ xs) :
    qListSum (xs.map fun r => attenuation 1 0 r * b r) ≈ b 0 := by
  apply Q'.eqv_trans _ _ _ (sum_congr_local _ _ xs (fun r _ => ?_)) (sum_pick 0 (b 0) xs hn hd)
  apply Q'.eqv_trans _ _ _ (endpoint_weight 0 r (b r))
  by_cases he : r=0
  · subst r; simp only [Nat.le_refl, if_true]; exact Q'.eqv_refl _
  · simp only [if_neg he, if_neg (show ¬ r ≤ 0 by omega)]; exact Q'.eqv_refl _

private theorem pairing_sum (n : Nat) (test : RatPoly) (f : Nat → RatPoly)
    (c : Nat → Q') : ∀ xs : List Nat,
    quaternionHaar n (polyMul test (polySum (xs.map fun d => polySmul (c d) (f d)))) ≈
      qListSum (xs.map fun d => c d * quaternionHaar n (polyMul test (f d)))
  | [] => haar_of_coeff (RatPolyCoeffEqv.mul_zero_right _)
  | d::ds => Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
        (Q'.add_eqv_congr' (quaternionHaar_polyMul_smul_right n (c d) test (f d))
          (pairing_sum n test f c ds)))

/-- A single normalized character selects the actual computed degree branch.
Finite nome-one prefix subtraction derives the selection from the ORIGINAL
heat action; it assumes no commuting Fischer-projector family. -/
theorem characterCycleStep_branch_carrier (tail d : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (hd : d ∈ branchDegrees tail p) :
    HaarCarrierEqv (tail+1) (characterCycleStep (tail+1) d p) (nextPiece tail p d) := by
  intro test
  let b := fun r => quaternionHaar (tail+1) (polyMul test (nextPiece tail p r))
  have hn : (branchDegrees tail p).Nodup := CayleyParentInj.range_nodup _
  have hsum (K : Nat) : quaternionHaar (tail+1) (polyMul test (cycleStep (tail+1) 1 K p)) ≈
      qListSum ((branchDegrees tail p).map fun r => attenuation 1 K r * b r) :=
    Q'.eqv_trans _ _ _ (cycleStep_grouped tail 1 K p hp test)
      (pairing_sum (tail+1) test (nextPiece tail p) (attenuation 1 K) _)
  cases d with
  | zero =>
      exact Q'.eqv_trans _ _ _ (haar_of_coeff ((cycleStep_one_zero (tail+1) p).symm.mul_left test))
        (Q'.eqv_trans _ _ _ (hsum 0) (endpoint_zero b _ hn hd))
  | succ k =>
      have hrec := Q'.eqv_trans _ _ _
        (haar_of_coeff ((cycleStep_one_succ (tail+1) k p).mul_left test))
        (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _))
          (quaternionHaar_append (tail+1) _ _))
      have htwo := Q'.eqv_trans _ _ _ (hsum (k+1))
        (Q'.eqv_trans _ _ _ (endpoint_step b k _ hn hd)
          (Q'.add_eqv_congr' (hsum k).symm (Q'.eqv_refl _)))
      have hc := Q'.add_eqv_congr' (Q'.eqv_refl
        (-quaternionHaar (tail+1) (polyMul test (cycleStep (tail+1) 1 k p))))
        (Q'.eqv_trans _ _ _ hrec.symm htwo)
      have cancel (a z : Q') : -a + (a+z) ≈ z :=
        poly_identity_of_normal_eq (.add (.neg (.var 0)) (.add (.var 0) (.var 1)))
          (.var 1) (by decide) (fun | 0 => a | _ => z)
      exact Q'.eqv_trans _ _ _ (cancel _ _).symm (Q'.eqv_trans _ _ _ hc (cancel _ _))

end YMGap.Continuum.SU2QuaternionCyclicCharacterSelection

#print axioms YMGap.Continuum.SU2QuaternionCyclicCharacterSelection.characterCycleStep
#print axioms YMGap.Continuum.SU2QuaternionCyclicCharacterSelection.characterCycleStep_supported
#print axioms YMGap.Continuum.SU2QuaternionCyclicCharacterSelection.heatAt_one_succ
#print axioms YMGap.Continuum.SU2QuaternionCyclicCharacterSelection.heatAt_one_zero
#print axioms YMGap.Continuum.SU2QuaternionCyclicCharacterSelection.cycleStep_one_succ
#print axioms YMGap.Continuum.SU2QuaternionCyclicCharacterSelection.cycleStep_one_zero
#print axioms YMGap.Continuum.SU2QuaternionCyclicCharacterSelection.characterCycleStep_branch_carrier
