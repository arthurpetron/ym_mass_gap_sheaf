/-
# Full relative heat kernels preserve the vacuum under retained insertions

Every positive spin has zero conditional Haar mean. The original packet's
spin-zero coefficient is exactly one, so every cutoff K, including zero,
preserves any head-independent insertion on the same carrier. This is the
normalization identity needed to retain the connected subtraction.
-/

import YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry

namespace YMGap.Continuum.SU2QuaternionRelativeHeatVacuum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionTailEvaluation
open YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar

local infix:50 " ≈ " => Q'.eqv

theorem positive_spin_partial_zero (spin : Nat) (hs : 0 < spin) :
    RatPolyCoeffEqv (partialHaarHead (relativeSolid spin)) polyZero := by
  have hz := exposedSolid_partialHaar_zero false true false false spin polyOne (by exact hs)
  have hp := (evaluate_mul 8 auxiliaryUnits _ _).trans
    ((solid_specialization spin).mul (evaluate_one 8 auxiliaryUnits))
  have ht := (partialHaarHead_congr hp).symm.trans (partialHaarHead_evaluate_zero 4 auxiliaryUnits hz)
  exact (partialHaarHead_congr (RatPolyCoeffEqv.mul_one (relativeSolid spin))).symm.trans ht

/-- Every retained variable is shared with the original insertion. -/
theorem character_vacuum (tailBlocks : Nat) (hb : 0 < tailBlocks) (spin : Nat)
    (r : RatPoly) (hr : HeadQuaternionIndependent r) :
    quaternionHaar (tailBlocks+1) (polyMul (relativeCharacter spin) r) ≈
      (if spin = 0 then quaternionHaar (tailBlocks+1) r else 0) := by
  cases spin with
  | zero => exact haar_of_coeff (RatPolyCoeffEqv.one_mul r)
  | succ s =>
    have hc := haar_of_carrier ((solid_character_pin (tailBlocks+1) (by omega) (s+1)).symm.mul_right r)
    exact Q'.eqv_trans _ _ _ hc (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_headIndependent tailBlocks (relativeSolid (s+1)) r hr)
      (haar_of_coeff ((positive_spin_partial_zero (s+1) (by omega)).mul_right _)))

private theorem sum_insert (blocks : Nat) (f : Nat → RatPoly) (p : RatPoly) : ∀ xs : List Nat,
    quaternionHaar blocks (polyMul (finitePolySum f xs) p) ≈
      listQSum (fun s => quaternionHaar blocks (polyMul (f s) p)) xs
  | [] => Q'.eqv_refl _
  | s::xs => by
    change quaternionHaar blocks (polyMul (polyAdd (f s) (finitePolySum f xs)) p) ≈ _
    rw [polyMul_add_left_exact]
    exact Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_insert blocks f p xs))

private theorem sum_congr (f g : Nat → Q') : ∀ xs : List Nat,
    (∀ s, s ∈ xs → f s ≈ g s) → listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl _
  | s::xs, h => Q'.add_eqv_congr' (h s List.mem_cons_self)
      (sum_congr f g xs (fun t ht => h t (List.mem_cons_of_mem s ht)))

private theorem sum_append (f : Nat → Q') : ∀ xs ys : List Nat,
    listQSum f (xs++ys) ≈ listQSum f xs + listQSum f ys
  | [], _ => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | _::xs, ys => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (sum_append f xs ys)) (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem sum_vacuum (value : Q') : ∀ k,
    listQSum (fun s => if s = 0 then value else 0) (List.range (k+1)) ≈ value
  | 0 => Q'.eqv_of_eq (Q'.add_zero' value)
  | k+1 => by
    rw [List.range_succ]
    refine Q'.eqv_trans _ _ _ (sum_append _ _ _) ?_
    have hz : listQSum (fun s => if s = 0 then value else 0) [k+1] ≈ 0 := by
      simp only [listQSum, if_neg (show k+1 ≠ 0 by omega), Q'.add_zero']
      exact Q'.eqv_refl _
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (sum_vacuum value k) hz)
      (Q'.eqv_of_eq (Q'.add_zero' _))

/-- Full packet normalization at every cutoff, with no sign/nome restriction. -/
theorem heat_vacuum (tailBlocks : Nat) (hb : 0 < tailBlocks) (w : Q') (K : Nat)
    (r : RatPoly) (hr : HeadQuaternionIndependent r) :
    quaternionHaar (tailBlocks+1) (polyMul (relativeHeat w K) r) ≈ quaternionHaar (tailBlocks+1) r := by
  refine Q'.eqv_trans _ _ _ (sum_insert (tailBlocks+1) _ r (List.range (K+1))) ?_
  refine Q'.eqv_trans _ _ _ ?_ (sum_vacuum (quaternionHaar (tailBlocks+1) r) K)
  apply sum_congr
  intro s hmem
  rw [coeffAt_heatKernelPacket (List.mem_range.mp hmem)]
  refine Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _) ?_)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (character_vacuum tailBlocks hb s r hr)) ?_
  cases s with
  | zero => exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_of_eq (coeffW_zero w))) (Q'.one_mul_eqv _)
  | succ s => exact Q'.mul_zero_eqv _

end YMGap.Continuum.SU2QuaternionRelativeHeatVacuum

#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatVacuum.positive_spin_partial_zero
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatVacuum.character_vacuum
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatVacuum.heat_vacuum
