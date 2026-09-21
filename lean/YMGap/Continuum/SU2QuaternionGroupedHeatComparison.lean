/-
# Original heat pairing and explicit grouped Casimir budget

The original heat packet acts on the computed equal-degree GROUPS, not
on a presumed orthogonal list of Fischer summands. The scalar attenuation
defect controls the sum of their nonnegative squared norms under an explicit
cutoff guard, even when the input degree exceeds the heat cutoff.

The last estimate is a grouped norm budget. Identifying it with the original
product operator's full kinetic energy, then retaining the signed endpoint
correction, remains a separate obligation. No such identification is assumed.
-/

import YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm
import YMGap.Continuum.SU2HeatCutoffCasimirBound
import YMGap.Continuum.QuaternionHaarHarmonicAngularEnergy

namespace YMGap.Continuum.SU2QuaternionGroupedHeatComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionFischerDecomposition
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents
open YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionHarmonicHeatInsertion
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarHarmonicAngularEnergy

local infix:50 " ≈ " => Q'.eqv

private theorem grouped_heat_sum (tail : Nat) (hb : 0 < tail) (w : Q') (K : Nat)
    (r : RatPoly) (hr : HeadQuaternionIndependent r) (ms : List (Mode (tail+1))) :
    ∀ ids : List Nat,
    quaternionHaar (tail+1)
      (polyMul (polyMul (relativeHeat w K) (polySum (ids.map fun d => grouped d ms))) r) ≈
      qListSum (ids.map fun d => attenuation w K d *
        quaternionHaar (tail+1) (polyMul (retainedImage (grouped d ms)) r))
  | [] => haar_of_coeff (((RatPolyCoeffEqv.mul_zero_right _).mul_right r).trans
      (RatPolyCoeffEqv.mul_zero_left r))
  | d::ds => by
      have ht := harmonic_transmission_same_carrier tail hb w K d (grouped d ms) r
        (grouped_degree d ms) (grouped_harmonic d ms) hr
      have ha : quaternionHaar (tail+1)
          (polyMul (polyMul (relativeHeat w K) (grouped d ms)) r) ≈
          attenuation w K d * quaternionHaar (tail+1)
            (polyMul (retainedImage (grouped d ms)) r) := by
        unfold attenuation
        by_cases hd : d ≤ K
        · rw [if_pos hd] at ht ⊢
          exact ht
        · rw [if_neg hd] at ht ⊢
          exact Q'.eqv_trans _ _ _ ht (Q'.eqv_symm (Q'.zero_mul_eqv _))
      have hsplit := ((RatPolyCoeffEqv.mul_add_right (relativeHeat w K)
        (grouped d ms) (polySum (ds.map fun k => grouped k ms))).mul_right r)
      rw [polyMul_add_left_exact] at hsplit
      exact Q'.eqv_trans _ _ _ (haar_of_coeff hsplit)
        (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
          (Q'.add_eqv_congr' ha (grouped_heat_sum tail hb w K r hr ms ds)))

/-- Actual original-packet pairing for any supported signed input, grouped
by harmonic degree. The retained insertion is not dropped or replaced. -/
theorem polynomial_grouped_heat_pairing (tail : Nat) (hb : 0 < tail)
    (w : Q') (K : Nat) (p r : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (hr : HeadQuaternionIndependent r) :
    quaternionHaar (tail+1) (polyMul (polyMul (relativeHeat w K) p) r) ≈
      qListSum ((headDegrees (sumHarmonics (modes (tail+1) (by omega) p))).map fun d =>
        attenuation w K d * quaternionHaar (tail+1)
          (polyMul (retainedImage (grouped d (modes (tail+1) (by omega) p))) r)) := by
  let ms := modes (tail+1) (by omega) p
  have hc := (polynomial_harmonic_carrier (by omega : 0 < tail+1) p hp).trans
    (RatPolyCoeffEqv.haarCarrier (headComponent_reassembly (sumHarmonics ms)).symm)
  exact Q'.eqv_trans _ _ _
    (haar_of_carrier (HaarCarrierEqv.mul_right r (hc.mul_left (relativeHeat w K))))
    (grouped_heat_sum tail hb w K r hr ms _)

/-- All cross terms within one harmonic degree remain inside this norm. -/
def groupedNorm {blocks : Nat} (ms : List (Mode blocks)) (d : Nat) : Q' :=
  quaternionHaar blocks (polyMul (grouped d ms) (grouped d ms))

/-- The omitted-mode estimate does not require `degree(input) ≤ K`.
It controls a grouped norm sum, not yet the interacting transfer energy. -/
theorem grouped_defect_le_casimir {blocks : Nat} {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat)
    (hguard : (1 : Q') ≤ ((1 : Q') - w) * Q'.ofNat ((K+1)*(K+3)))
    (ms : List (Mode blocks)) : ∀ ids : List Nat,
    qListSum (ids.map fun d => ((1 : Q') - attenuation w K d) * groupedNorm ms d) ≤
      ((1 : Q') - w) *
        qListSum (ids.map fun d => Q'.ofNat (d*(d+2)) * groupedNorm ms d)
  | [] => Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_zero_eqv _))
  | d::ds => by
      have hmode := Q'.mul_le_mul_of_nonneg_right _ _ _
        (one_sub_attenuation_le hw0 hw1 K d hguard) (grouped_norm_nonnegative d ms)
      have hmode' := Q'.le_trans' _ _ _ hmode (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
      have hsum := Q'.add_le_add hmode' (grouped_defect_le_casimir hw0 hw1 K hguard ms ds)
      exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv (Q'.mul_add_eqv _ _ _))

/-- The Casimir cost is the actual angular square of each COMPLETE group. -/
theorem grouped_casimir_energy (tail : Nat) (ms : List (Mode (tail+1))) (d : Nat) :
    Q'.ofNat (d*(d+2)) * groupedNorm ms d ≈
      quaternionHaar (tail+1) (angularSquare (grouped d ms)) := by
  have hscalar : Q'.ofNat (d*(d+2)) ≈ Q'.ofNat d * (Q'.ofNat d+2) :=
    Q'.eqv_trans _ _ _ (HeatKernelRGStep.ofNat_mul_eqv d (d+2))
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv d 2)
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (by decide))))
  have he := retained_harmonic_energy tail d polyOne (grouped d ms)
    (hasQuaternionBlockDegree_one 0) (grouped_degree d ms) (grouped_harmonic d ms)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hscalar)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.one_mul _))))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm he) (haar_of_coeff (RatPolyCoeffEqv.one_mul _))))

private theorem grouped_casimir_sum (tail : Nat) (ms : List (Mode (tail+1))) :
    ∀ ids : List Nat,
    qListSum (ids.map fun d => Q'.ofNat (d*(d+2)) * groupedNorm ms d) ≈
      qListSum (ids.map fun d => quaternionHaar (tail+1) (angularSquare (grouped d ms)))
  | [] => Q'.eqv_refl _
  | d::ds => Q'.add_eqv_congr' (grouped_casimir_energy tail ms d)
      (grouped_casimir_sum tail ms ds)

/-- A quantitative angular-energy budget for the computed groups, valid
above AND below cutoff. This is not a product-transfer energy identity. -/
theorem grouped_defect_le_angular (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat)
    (hguard : (1 : Q') ≤ ((1 : Q') - w) * Q'.ofNat ((K+1)*(K+3)))
    (ms : List (Mode (tail+1))) (ids : List Nat) :
    qListSum (ids.map fun d => ((1 : Q') - attenuation w K d) * groupedNorm ms d) ≤
      ((1 : Q') - w) * qListSum (ids.map fun d =>
        quaternionHaar (tail+1) (angularSquare (grouped d ms))) :=
  Q'.le_trans' _ _ _ (grouped_defect_le_casimir hw0 hw1 K hguard ms ids)
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (grouped_casimir_sum tail ms ids)))

/-- The scalar guard is constructed, not an analytic hypothesis, for every
cutoff above the explicit rational-nome witness. -/
theorem grouped_defect_le_angular_of_cutoff (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (ms : List (Mode (tail+1))) (ids : List Nat) :
    qListSum (ids.map fun d => ((1 : Q') - attenuation w K d) * groupedNorm ms d) ≤
      ((1 : Q') - w) * qListSum (ids.map fun d =>
        quaternionHaar (tail+1) (angularSquare (grouped d ms))) :=
  grouped_defect_le_angular tail hw0 (Q'.le_of_lt hw1) K (cutoff_guard_of_le hw1 hK) ms ids

end YMGap.Continuum.SU2QuaternionGroupedHeatComparison

#print axioms YMGap.Continuum.SU2QuaternionGroupedHeatComparison.polynomial_grouped_heat_pairing
#print axioms YMGap.Continuum.SU2QuaternionGroupedHeatComparison.grouped_defect_le_casimir
#print axioms YMGap.Continuum.SU2QuaternionGroupedHeatComparison.grouped_casimir_energy
#print axioms YMGap.Continuum.SU2QuaternionGroupedHeatComparison.grouped_defect_le_angular
#print axioms YMGap.Continuum.SU2QuaternionGroupedHeatComparison.grouped_defect_le_angular_of_cutoff
