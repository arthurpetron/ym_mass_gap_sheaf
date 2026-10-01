/-
# Output-side smoothing of the original one-head heat

The head map preserves spectator coordinates.  The six-plane angular energy
of its actual output is a sum of complete, signed, equal-degree groups.  The
finite scalar attenuation inequality pays this output energy from the input
heat pairing, without a cutoff-largeness guard.

The RHS is an uncentered one-head Haar pairing. Full weighted product heat,
the original terminal action and the SAME interacting-variance join are not
asserted. No continuum survival, physical mass or full QFT claim is made.
-/

import YMGap.Continuum.SU2QuaternionGroupedAngularEnergy
import YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
import YMGap.Continuum.SU2HeatSquaredCasimirSmoothing

namespace YMGap.Continuum.SU2QuaternionHeadHeatSmoothing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadDegreeDifferential
open YMGap.Continuum.SU2QuaternionFischerDecomposition
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents
open YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm
open YMGap.Continuum.SU2QuaternionGroupedHeatComparison
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
open YMGap.Continuum.SU2QuaternionGroupedAngularEnergy
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.SU2HeatSquaredCasimirSmoothing
open YMGap.Continuum.QuaternionHaarHarmonicAngularEnergy
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem pairing_sum (n : Nat) (test : RatPoly)
    (f : Nat → RatPoly) (c : Nat → Q') : ∀ ids : List Nat,
    quaternionHaar n (polyMul test (polySum (ids.map fun a => polySmul (c a) (f a)))) ≈
      qListSum (ids.map fun a => c a * quaternionHaar n (polyMul (f a) test))
  | [] => haar_of_coeff (RatPolyCoeffEqv.mul_zero_right test)
  | a::ids => Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right n (c a) test (f a))
            (Q'.mul_eqv_congr_left _ _ _
              (haar_of_coeff (RatPolyCoeffEqv.mul_comm test (f a)))))
          (pairing_sum n test f c ids)))

/-- Exact Haar-carrier expansion of the literal head map.  Unlike
`productMap [0]`, it does not refresh the spectator coordinates. -/
theorem headMap_grouped (tail : Nat) (w : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv (tail+1) (headMap w K p)
      (polySum ((headDegrees (sumHarmonics (modes (tail+1) (by omega) p))).map fun d =>
        polySmul (attenuation w K d)
          (grouped d (modes (tail+1) (by omega) p)))) := by
  intro test
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_comm test _))
    (Q'.eqv_trans _ _ _ (headMap_pairing tail w K p test)
      (Q'.eqv_trans _ _ _ (polynomial_pair tail w K p test hp)
        (pairing_sum (tail+1) test
          (fun d => grouped d (modes (tail+1) (by omega) p))
          (attenuation w K) _).symm))

private theorem scaled_group_square (tail d : Nat) (ms : List (Mode (tail+1)))
    (a : Q') :
    quaternionHaar (tail+1)
        (polyMul (polySmul a (grouped d ms)) (polySmul a (grouped d ms))) ≈
      (a*a) * groupedNorm ms d := by
  have hc : RatPolyCoeffEqv
      (polyMul (polySmul a (grouped d ms)) (polySmul a (grouped d ms)))
      (polySmul a (polySmul a
        (polyMul (grouped d ms) (grouped d ms)))) :=
    (RatPolyCoeffEqv.polyMul_smul_left a _ _).trans
      ((RatPolyCoeffEqv.polyMul_smul_right a _ _).smul a)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hc)
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (tail+1) a _)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (quaternionHaar_polySmul (tail+1) a _))
        (Q'.eqv_symm (Q'.mul_assoc_eqv a a (groupedNorm ms d)))))

private theorem scaled_group_energy (tail d : Nat) (ms : List (Mode (tail+1)))
    (a : Q') :
    quaternionHaar (tail+1) (angularSquare (polySmul a (grouped d ms))) ≈
      (Q'.ofNat (d*(d+2)) * (a*a)) * groupedNorm ms d := by
  have he := retained_harmonic_energy tail d polyOne (polySmul a (grouped d ms))
    (hasQuaternionBlockDegree_one 0) ((grouped_degree d ms).smul a)
    ((headLaplacian_smul _ _).trans
      (((grouped_harmonic d ms).smul a).trans (RatPolyCoeffEqv.smul_zero a)))
  have hbase : quaternionHaar (tail+1) (angularSquare (polySmul a (grouped d ms))) ≈
      (Q'.ofNat d * (Q'.ofNat d+2)) *
        quaternionHaar (tail+1)
          (polyMul (polySmul a (grouped d ms)) (polySmul a (grouped d ms))) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.one_mul _)))
      (Q'.eqv_trans _ _ _ he
        (Q'.mul_eqv_congr_left _ _ _
          (haar_of_coeff (RatPolyCoeffEqv.one_mul _))))
  have hscalar : Q'.ofNat (d*(d+2)) ≈ Q'.ofNat d * (Q'.ofNat d+2) :=
    Q'.eqv_trans _ _ _ (HeatKernelRGStep.ofNat_mul_eqv d (d+2))
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv d 2)
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (by decide))))
  exact Q'.eqv_trans _ _ _ hbase
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (scaled_group_square tail d ms a))
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm
          (Q'.mul_eqv_congr_right _ _ _ hscalar)))))

private theorem sum_energy (tail : Nat) (ms : List (Mode (tail+1)))
    (c : Nat → Q') : ∀ ids : List Nat,
    qListSum (ids.map fun d => quaternionHaar (tail+1)
      (angularSquare (polySmul (c d) (grouped d ms)))) ≈
    qListSum (ids.map fun d =>
      (Q'.ofNat (d*(d+2)) * (c d*c d)) * groupedNorm ms d)
  | [] => Q'.eqv_refl _
  | d::ds => Q'.add_eqv_congr' (scaled_group_energy tail d ms (c d))
      (sum_energy tail ms c ds)

/-- Exact angular energy of the original one-head output, including all
within-degree signed cross terms before taking squares. -/
theorem headMap_angular_grouped (tail : Nat) (w : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    quaternionHaar (tail+1) (angularSquare (headMap w K p)) ≈
      qListSum ((headDegrees (sumHarmonics (modes (tail+1) (by omega) p))).map fun d =>
        (Q'.ofNat (d*(d+2)) *
          (attenuation w K d * attenuation w K d)) *
          groupedNorm (modes (tail+1) (by omega) p) d) := by
  let ms := modes (tail+1) (by omega) p
  let f := fun d => polySmul (attenuation w K d) (grouped d ms)
  let ids := headDegrees (sumHarmonics ms)
  have hf : ∀ d, HasQuaternionBlockDegree 0 d (f d) :=
    fun d => (grouped_degree d ms).smul _
  have hh : ∀ d, RatPolyCoeffEqv (headLaplacian (f d)) polyZero :=
    fun d => (headLaplacian_smul _ _).trans
      (((grouped_harmonic d ms).smul _).trans (RatPolyCoeffEqv.smul_zero _))
  exact Q'.eqv_trans _ _ _
    (carrier_harmonic_sum_angular_energy tail _ f hf hh ids
      (YMGap.Continuum.CayleyParentInj.range_nodup _)
      (headMap_grouped tail w K p hp))
    (sum_energy tail ms (attenuation w K) ids)

private theorem sum_scale (c : Q') (f : Nat → Q') : ∀ ids : List Nat,
    c * qListSum (ids.map f) ≈ qListSum (ids.map fun d => c * f d)
  | [] => Q'.mul_zero_eqv c
  | _d::ds => Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_scale c f ds))

private theorem sum_le (f g : Nat → Q') : ∀ ids : List Nat,
    (∀ d, d ∈ ids → f d ≤ g d) →
    qListSum (ids.map f) ≤ qListSum (ids.map g)
  | [], _ => Q'.le_refl' _
  | d::ds, h => Q'.add_le_add (h d List.mem_cons_self)
      (sum_le f g ds (fun k hk => h k (List.mem_cons_of_mem d hk)))

/-- One-head output angular smoothing for arbitrary supported signed input.
The cutoff is the literal `K`, with no largeness condition. -/
theorem headMap_angular_smoothing (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    ((1 : Q') - w) *
        quaternionHaar (tail+1) (angularSquare (headMap w K p)) ≤
      quaternionHaar (tail+1) (polyMul p (headMap w K p)) := by
  let ms := modes (tail+1) (by omega) p
  let ids := headDegrees (sumHarmonics ms)
  let a := fun d => attenuation w K d
  let n := fun d => groupedNorm ms d
  have hmode (d : Nat) :
      ((1 : Q') - w) * ((Q'.ofNat (d*(d+2)) * (a d*a d)) * n d) ≤
        a d * n d := by
    have hs := attenuation_squared_casimir_smoothing hw0 hw1 K d
    have hm := Q'.mul_le_mul_of_nonneg_right _ _ _ hs
      (grouped_norm_nonnegative d ms)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))))) hm
  have hsum : qListSum (ids.map fun d =>
      ((1 : Q') - w) * ((Q'.ofNat (d*(d+2)) * (a d*a d)) * n d)) ≤
      qListSum (ids.map fun d => a d*n d) :=
    sum_le _ _ ids (fun d _ => hmode d)
  have hleft := Q'.mul_eqv_congr_left ((1 : Q')-w) _ _
    (headMap_angular_grouped tail w K p hp)
  have hdiag : quaternionHaar (tail+1) (polyMul p (headMap w K p)) ≈
      qListSum (ids.map fun d => a d*n d) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm p (headMap w K p)))
      (Q'.eqv_trans _ _ _ (headMap_pairing tail w K p p)
        (polynomial_diagonal tail w K p hp))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (sum_scale _ _ ids))
      (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (Q'.eqv_symm hdiag))))

end YMGap.Continuum.SU2QuaternionHeadHeatSmoothing

#print axioms YMGap.Continuum.SU2QuaternionHeadHeatSmoothing.headMap_grouped
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatSmoothing.headMap_angular_grouped
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatSmoothing.headMap_angular_smoothing
