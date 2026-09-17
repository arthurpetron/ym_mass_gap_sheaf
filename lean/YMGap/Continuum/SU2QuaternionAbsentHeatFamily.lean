/-
# A whole family of absent-coordinate tests for the original product heat

Each test is conditionally centered in the complete endpoint weight a at
a coordinate absent from the kinetic list. Their signed sum annihilates
every Haar pairing with the same product map. Its mixed jump pairing is
exactly twice its original marginal pairing, with no list-length factor.

Annihilation is asserted under Haar testing, not as raw coefficient equality
of the output. Different summands may use different absent coordinates, and
their cross terms are retained. No positivity or heat-cutoff guard is needed
for these identities; this is not an active-coordinate spectral estimate.
-/

import YMGap.Continuum.SU2QuaternionProductHeatMarginals
import YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy

namespace YMGap.Continuum.SU2QuaternionAbsentHeatFamily

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap kernelMap_smul)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary liftHead)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_add)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (edgeWeight)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy
  (jump marginalPair erased_jump_pairing)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

private theorem map_zero (n : Nat) (w : Q') (K : Nat) (ids : List Nat) :
    RatPolyCoeffEqv (productMap n w K ids polyZero) polyZero :=
  (productMap_congr n w K ids (RatPolyCoeffEqv.zero_smul polyOne).symm).trans
    ((kernelMap_smul n (productHeat n w K ids) 0 polyOne).trans
      (RatPolyCoeffEqv.zero_smul _))

private theorem map_pair_add (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (a p q r : RatPoly) :
    quaternionHaar n (polyMul p (productMap n w K ids (polyMul a (polyAdd q r)))) ≈
      quaternionHaar n (polyMul p (productMap n w K ids (polyMul a q))) +
      quaternionHaar n (polyMul p (productMap n w K ids (polyMul a r))) :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff (((productMap_congr n w K ids (RatPolyCoeffEqv.mul_add_right a q r)).trans
      (productMap_add n w K ids (polyMul a q) (polyMul a r))).mul_left p))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right p _ _))
      (quaternionHaar_append n _ _))

/-- Every Haar test annihilates the entire signed family at once.
No common centering coordinate or raw output-zero claim is required. -/
theorem absent_sum_pair_zero (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) (a : RatPoly) (qs : Nat → RatPoly)
    (js : List Nat) (hi : ∀ i, i ∈ js → i < n)
    (hnot : ∀ i, i ∈ js → i ∉ ids)
    (hc : ∀ i, i ∈ js → RatPolyCoeffEqv (project i (polyMul a (qs i))) polyZero)
    (p : RatPoly) :
    quaternionHaar n (polyMul p (productMap n w K ids (polyMul a (polySum (js.map qs))))) ≈ 0 := by
  revert hi hnot hc
  induction js with
  | nil =>
      intro _ _ _
      exact haar_of_coeff
        ((((productMap_congr n w K ids (RatPolyCoeffEqv.mul_zero_right a)).trans
          (map_zero n w K ids)).mul_left p).trans (RatPolyCoeffEqv.mul_zero_right p))
  | cons i js ih =>
      intro hi hnot hc
      have ht := ih
        (fun j hj => hi j (List.mem_cons_of_mem i hj))
        (fun j hj => hnot j (List.mem_cons_of_mem i hj))
        (fun j hj => hc j (List.mem_cons_of_mem i hj))
      exact Q'.eqv_trans _ _ _ (map_pair_add n w K ids a p (qs i) (polySum (js.map qs)))
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (productMap_absent_pair_zero n w K i ids (hi i List.mem_cons_self)
              (hnot i List.mem_cons_self) hids (polyMul a (qs i)) p (hc i List.mem_cons_self)) ht)
          (Q'.eqv_of_eq (Q'.add_zero' 0)))

private theorem lift_zero : ∀ n : Nat, liftBoundary n polyZero = polyZero
  | 0 => rfl
  | n+1 => by
      change liftHead (liftBoundary n polyZero) = polyZero
      rw [lift_zero n]
      rfl

private theorem jump_zero (n : Nat) : jump n polyZero = polyZero := by
  unfold jump
  rw [lift_zero]
  rfl

private theorem jump_add (n : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (jump n (polyAdd p q)) (polyAdd (jump n p) (jump n q)) := by
  unfold jump
  rw [lift_add]
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
    (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3))))
    (by decide) (fun | 0 => p | 1 => q | 2 => liftBoundary n p | _ => liftBoundary n q)

private theorem weighted_add_right (n : Nat) (e p q r : RatPoly) :
    weightedPair n e p (polyAdd q r) ≈ weightedPair n e p q + weightedPair n e p r :=
  Q'.eqv_trans _ _ _ (weighted_symm n e p _)
    (Q'.eqv_trans _ _ _ (weighted_add_left n e q r p)
      (Q'.add_eqv_congr' (weighted_symm n e q p) (weighted_symm n e r p)))

private theorem jump_pair_add (n : Nat) (e f q r : RatPoly) :
    weightedPair (n+n) e (jump n f) (jump n (polyAdd q r)) ≈
      weightedPair (n+n) e (jump n f) (jump n q) +
      weightedPair (n+n) e (jump n f) (jump n r) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (((jump_add n q r).mul_left (jump n f)).mul_right e))
    (weighted_add_right (n+n) e (jump n f) (jump n q) (jump n r))

private theorem marginal_add (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (a f q r : RatPoly) :
    marginalPair n w K ids a f (polyAdd q r) ≈
      marginalPair n w K ids a f q + marginalPair n w K ids a f r :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff ((RatPolyCoeffEqv.mul_add_right f q r).mul_left
      (polyMul a (productMap n w K ids a))))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _))
      (quaternionHaar_append n _ _))

private theorem marginal_zero (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (a f : RatPoly) :
    marginalPair n w K ids a f polyZero ≈ 0 :=
  haar_of_coeff (((RatPolyCoeffEqv.mul_zero_right f).mul_left
    (polyMul a (productMap n w K ids a))).trans (RatPolyCoeffEqv.mul_zero_right _))

/-- All absent-coordinate pieces form one exact coefficient-two jump test;
their ordinary marginal cross pairings are kept, not bounded separately. -/
theorem absent_sum_jump_pairing (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) (a : RatPoly) (qs : Nat → RatPoly)
    (js : List Nat) (hi : ∀ i, i ∈ js → i < n)
    (hnot : ∀ i, i ∈ js → i ∉ ids)
    (hc : ∀ i, i ∈ js → RatPolyCoeffEqv (project i (polyMul a (qs i))) polyZero)
    (f : RatPoly) (ha : SupportedQuaternionBlocks n a)
    (hf : SupportedQuaternionBlocks n f)
    (hqs : ∀ i, i ∈ js → SupportedQuaternionBlocks n (qs i)) :
    weightedPair (n+n) (edgeWeight n w K ids a)
      (jump n f) (jump n (polySum (js.map qs))) ≈
      (2 : Q')*marginalPair n w K ids a f (polySum (js.map qs)) := by
  revert hi hnot hc hqs
  induction js with
  | nil =>
      intro _ _ _ _
      change weightedPair (n+n) (edgeWeight n w K ids a) (jump n f) (jump n polyZero) ≈ _
      rw [jump_zero]
      have hz : weightedPair (n+n) (edgeWeight n w K ids a) (jump n f) polyZero ≈ 0 :=
        haar_of_coeff (((RatPolyCoeffEqv.mul_zero_right (jump n f)).mul_right _).trans
          (RatPolyCoeffEqv.mul_zero_left _))
      exact Q'.eqv_trans _ _ _ hz
        (Q'.eqv_symm (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left 2 _ _ (marginal_zero n w K ids a f)) (Q'.mul_zero_eqv 2)))
  | cons i js ih =>
      intro hi hnot hc hqs
      have ht := ih
        (fun j hj => hi j (List.mem_cons_of_mem i hj))
        (fun j hj => hnot j (List.mem_cons_of_mem i hj))
        (fun j hj => hc j (List.mem_cons_of_mem i hj))
        (fun j hj => hqs j (List.mem_cons_of_mem i hj))
      exact Q'.eqv_trans _ _ _
        (jump_pair_add n (edgeWeight n w K ids a) f (qs i) (polySum (js.map qs)))
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (erased_jump_pairing n w K i ids (hi i List.mem_cons_self)
              (hnot i List.mem_cons_self) hids ha hf (hqs i List.mem_cons_self)
              (hc i List.mem_cons_self)) ht)
          (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv 2 _ _))
            (Q'.mul_eqv_congr_left 2 _ _
              (Q'.eqv_symm (marginal_add n w K ids a f (qs i) (polySum (js.map qs)))))))

#print axioms absent_sum_pair_zero
#print axioms absent_sum_jump_pairing

end YMGap.Continuum.SU2QuaternionAbsentHeatFamily
