/-
# Actual one-link heat pairing with shared spectator variables

On (x,y,z), copy(p) is p(x,z) and liftHead(q) is q(y,z). The kernel is
the ORIGINAL finite relative heat packet. Its quadratic form is diagonal
on the computed complete harmonic-degree groups of p, with all spectators
shared rather than refreshed. This is one local kinetic factor, not the
full product operator, weighted transfer, OS gap or continuum limit.
-/

import YMGap.Continuum.SU2QuaternionSpareHeadCopy
import YMGap.Continuum.SU2QuaternionGroupedAngularEnergy
import YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction

namespace YMGap.Continuum.SU2QuaternionHeadHeatDiagonal

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionFischerRadial
open YMGap.Continuum.SU2QuaternionFischerDecomposition
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents
open YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm
open YMGap.Continuum.SU2QuaternionGroupedHeatComparison
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionRelativeHarmonicReproduction
open YMGap.Continuum.SU2QuaternionSpareHeadCopy
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.SU2QuaternionGroupedAngularEnergy
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction

local infix:50 " ≈ " => Q'.eqv

/-- The original two-link packet with every spectator coordinate shared. -/
def heatPair (tail : Nat) (w : Q') (K : Nat) (p q : RatPoly) : Q' :=
  quaternionHaar (tail+2)
    (polyMul (polyMul (relativeHeat w K) (copy p)) (liftHead q))

theorem harmonic_pair (tail : Nat) (w : Q') (K d : Nat) (p q : RatPoly)
    (hs : SupportedQuaternionBlocks (tail+1) p) (hpad : HeadPadded p)
    (hd : HasQuaternionBlockDegree 0 d p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) :
    heatPair tail w K p q ≈ attenuation w K d *
      quaternionHaar (tail+1) (polyMul p q) := by
  have h := heat_harmonic_reproduction (tail+1) (by omega) w K d (copy p)
    (copy_degree hd) (copy_harmonic hpad hh) q
  have hc := haar_of_carrier (HaarCarrierEqv.mul_right q
    (substitute_copy_carrier (by omega : 0 < tail+1) hs))
  unfold attenuation
  by_cases hK : d ≤ K
  · rw [if_pos hK] at h ⊢
    exact Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_left _ _ _ hc)
  · rw [if_neg hK] at h ⊢
    exact Q'.eqv_trans _ _ _ h (Q'.eqv_symm (Q'.zero_mul_eqv _))

private theorem pair_add (tail : Nat) (w : Q') (K : Nat) (p q r : RatPoly) :
    heatPair tail w K (polyAdd p q) r ≈
      heatPair tail w K p r + heatPair tail w K q r := by
  unfold heatPair
  rw [copy_add]
  have he := (RatPolyCoeffEqv.mul_add_right (relativeHeat w K) (copy p) (copy q)).mul_right (liftHead r)
  rw [polyMul_add_left_exact] at he
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he) (quaternionHaar_append _ _ _)

private theorem sum_padded {blocks : Nat} : ∀ ms : List (Mode blocks), HeadPadded (sumHarmonics ms)
  | [] => by intro t ht; contradiction
  | m::ms => (m.padded.smul m.coefficient).add (sum_padded ms)

private theorem group_pair_sum (tail : Nat) (w : Q') (K : Nat)
    (ms : List (Mode (tail+1))) (r : RatPoly) : ∀ ids : List Nat,
    heatPair tail w K (polySum (ids.map fun d => grouped d ms)) r ≈
      qListSum (ids.map fun d => attenuation w K d *
        quaternionHaar (tail+1) (polyMul (grouped d ms) r))
  | [] => haar_of_coeff (((RatPolyCoeffEqv.mul_zero_right _).mul_right _).trans
      (RatPolyCoeffEqv.mul_zero_left _))
  | d::ds => Q'.eqv_trans _ _ _ (pair_add tail w K _ _ r)
      (Q'.add_eqv_congr'
        (harmonic_pair tail w K d _ r (grouped_supported d ms)
          (headComponent_min_length (sum_padded ms)) (grouped_degree d ms) (grouped_harmonic d ms))
        (group_pair_sum tail w K ms r ds))

/-- Arbitrary original signed input, with computed (not assumed) harmonics. -/
theorem polynomial_pair (tail : Nat) (w : Q') (K : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    heatPair tail w K p q ≈
      qListSum ((headDegrees (sumHarmonics (modes (tail+1) (by omega) p))).map fun d =>
        attenuation w K d * quaternionHaar (tail+1)
          (polyMul (grouped d (modes (tail+1) (by omega) p)) q)) := by
  let ms := modes (tail+1) (by omega) p
  have hc := copy_carrier (by omega : 0 < tail+1) hp (sumHarmonics_supported ms)
    (polynomial_harmonic_carrier (by omega) p hp)
  have he := copy_congr (headComponent_reassembly (sumHarmonics ms)).symm
  exact Q'.eqv_trans _ _ _
    (haar_of_carrier (HaarCarrierEqv.mul_right (liftHead q) (hc.mul_left (relativeHeat w K))))
    (Q'.eqv_trans _ _ _ (haar_of_coeff ((he.mul_left (relativeHeat w K)).mul_right (liftHead q)))
      (group_pair_sum tail w K ms q _))

private theorem cross_sum (f : Nat → RatPoly)
    (hf : ∀ d, HasQuaternionBlockDegree 0 d (f d))
    (hh : ∀ d, RatPolyCoeffEqv (headLaplacian (f d)) polyZero)
    (n : Nat) : ∀ ids : List Nat, n ∉ ids →
    RatPolyCoeffEqv (partialHaarHead (polyMul (f n) (polySum (ids.map f)))) polyZero
  | [], _ => partialHaarHead_congr (RatPolyCoeffEqv.mul_zero_right _)
  | d::ds, hn => by
      have he := partialHaarHead_congr
        (RatPolyCoeffEqv.mul_add_right (f n) (f d) (polySum (ds.map f)))
      rw [partialHaarHead_add] at he
      exact he.trans ((harmonic_cross_degree (hf n) (hh n) (hf d) (hh d)
        (fun h => hn (h ▸ List.mem_cons_self))).add
          (cross_sum f hf hh n ds (fun h => hn (List.mem_cons_of_mem d h))))

private theorem projection_sum (f : Nat → RatPoly)
    (hf : ∀ d, HasQuaternionBlockDegree 0 d (f d))
    (hh : ∀ d, RatPolyCoeffEqv (headLaplacian (f d)) polyZero)
    (n : Nat) : ∀ ids : List Nat, ids.Nodup → n ∈ ids →
    RatPolyCoeffEqv (partialHaarHead (polyMul (f n) (polySum (ids.map f))))
      (partialHaarHead (polyMul (f n) (f n)))
  | [], _, hn => by contradiction
  | d::ds, hi, hn => by
      have he := partialHaarHead_congr
        (RatPolyCoeffEqv.mul_add_right (f n) (f d) (polySum (ds.map f)))
      rw [partialHaarHead_add] at he
      by_cases hnd : n=d
      · subst d
        exact he.trans (((RatPolyCoeffEqv.refl _).add
          (cross_sum f hf hh n ds (List.nodup_cons.mp hi).1)).trans (RatPolyCoeffEqv.add_zero _))
      · have hn' : n ∈ ds := (List.mem_cons.mp hn).resolve_left hnd
        exact he.trans (((harmonic_cross_degree (hf n) (hh n) (hf d) (hh d) hnd).add
          (projection_sum f hf hh n ds (List.nodup_cons.mp hi).2 hn')).trans
            (RatPolyCoeffEqv.zero_add _))

private theorem sum_congr (f g : Nat → Q') : ∀ ids : List Nat,
    (∀ d, d ∈ ids → f d ≈ g d) → qListSum (ids.map f) ≈ qListSum (ids.map g)
  | [], _ => Q'.eqv_refl _
  | d::ds, h => Q'.add_eqv_congr' (h d List.mem_cons_self)
      (sum_congr f g ds (fun k hk => h k (List.mem_cons_of_mem d hk)))

/-- The quadratic form of the actual original one-link kernel is the
attenuated sum of the complete grouped norms of the same input. -/
theorem polynomial_diagonal (tail : Nat) (w : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    heatPair tail w K p p ≈
      qListSum ((headDegrees (sumHarmonics (modes (tail+1) (by omega) p))).map fun d =>
        attenuation w K d * groupedNorm (modes (tail+1) (by omega) p) d) := by
  let ms := modes (tail+1) (by omega) p
  have hc := (polynomial_harmonic_carrier (by omega : 0 < tail+1) p hp).trans
    (RatPolyCoeffEqv.haarCarrier (headComponent_reassembly (sumHarmonics ms)).symm)
  apply Q'.eqv_trans _ _ _ (polynomial_pair tail w K p p hp)
  apply sum_congr
  intro d hd
  apply Q'.mul_eqv_congr_left
  apply Q'.eqv_trans _ _ _ (hc (grouped d ms))
  apply Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_partialHaarHead tail _))
  apply Q'.eqv_trans _ _ _ (haar_of_coeff (projection_sum (fun n => grouped n ms)
    (fun n => grouped_degree n ms) (fun n => grouped_harmonic n ms) d _
    (CayleyParentInj.range_nodup _) hd))
  exact quaternionHaar_partialHaarHead tail _

private theorem sum_defect (a N : Nat → Q') : ∀ ids : List Nat,
    qListSum (ids.map N) - qListSum (ids.map fun d => a d * N d) ≈
      qListSum (ids.map fun d => ((1 : Q')-a d)*N d)
  | [] => by change ((0 : Q')-0) ≈ 0; decide
  | d::ds => by
      have hr : (N d + qListSum (ds.map N)) -
          (a d*N d + qListSum (ds.map fun k => a k*N k)) ≈
          ((1 : Q')-a d)*N d +
            (qListSum (ds.map N) - qListSum (ds.map fun k => a k*N k)) :=
        poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 1)) (.neg (.add (.mul (.var 2) (.var 0)) (.var 3))))
          (.add (.mul (.add (.const 1) (.neg (.var 2))) (.var 0))
            (.add (.var 1) (.neg (.var 3))))
          (by decide) (fun
            | 0 => N d | 1 => qListSum (ds.map N) | 2 => a d
            | _ => qListSum (ds.map fun k => a k*N k))
      exact Q'.eqv_trans _ _ _ hr (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_defect a N ds))

/-- Exact defect of the ACTUAL local kernel on the same arbitrary input. -/
theorem polynomial_defect (tail : Nat) (w : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    quaternionHaar (tail+1) (polyMul p p) - heatPair tail w K p p ≈
      qListSum ((headDegrees (sumHarmonics (modes (tail+1) (by omega) p))).map fun d =>
        ((1 : Q')-attenuation w K d) * groupedNorm (modes (tail+1) (by omega) p) d) :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (polynomial_norm p hp)
      (Q'.neg_eqv_congr _ _ (polynomial_diagonal tail w K p hp)))
    (sum_defect (attenuation w K) (groupedNorm (modes (tail+1) (by omega) p)) _)

private theorem sum_nonnegative (f : Nat → Q') (hf : ∀ d, (0 : Q') ≤ f d) :
    ∀ ids : List Nat, (0 : Q') ≤ qListSum (ids.map f)
  | [] => Q'.le_refl' 0
  | d::ds => Q'.zero_le_add _ _ (hf d) (sum_nonnegative f hf ds)

/-- Positivity of the actual local quadratic form needs no large-cutoff
or pointwise heat-positivity premise. Its retained spectral weights are nonnegative. -/
theorem polynomial_pair_nonnegative (tail : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K : Nat) (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    (0 : Q') ≤ heatPair tail w K p p :=
  Q'.le_trans' _ _ _
    (sum_nonnegative _ (fun d => Q'.mul_nonneg _ _ (attenuation_nonnegative hw0 K d)
      (grouped_norm_nonnegative d (modes (tail+1) (by omega) p))) _)
    (Q'.ge_of_eqv (polynomial_diagonal tail w K p hp))

/-- The local quadratic form is at most the original norm at every cutoff. -/
theorem polynomial_defect_nonnegative (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    (0 : Q') ≤ quaternionHaar (tail+1) (polyMul p p) - heatPair tail w K p p :=
  Q'.le_trans' _ _ _
    (sum_nonnegative _ (fun d => Q'.mul_nonneg _ _
      (Q'.sub_nonneg_of_le (attenuation_le_one hw0 hw1 K d))
      (grouped_norm_nonnegative d (modes (tail+1) (by omega) p))) _)
    (Q'.ge_of_eqv (polynomial_defect tail w K p hp))

/-- A proved finite-time kinetic estimate, with a constructed sufficient
cutoff and the angular energy of the ORIGINAL signed polynomial. It concerns
one actual link update with shared spectators, not the full weighted transfer. -/
theorem polynomial_defect_le_angular (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    quaternionHaar (tail+1) (polyMul p p) - heatPair tail w K p p ≤
      ((1 : Q')-w) * quaternionHaar (tail+1) (angularSquare p) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (polynomial_defect tail w K p hp))
    (Q'.le_trans' _ _ _
      (grouped_defect_le_angular_of_cutoff tail hw0 hw1 K hK (modes (tail+1) (by omega) p) _)
      (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _ (polynomial_angular_energy tail p hp))))

/-- The actual conditional update: integrate x against the original packet
and return a polynomial in (y,z). Unselected coordinates z are unchanged. -/
def headMap (w : Q') (K : Nat) (p : RatPoly) : RatPoly :=
  conditionalHeat w K (copy p)

theorem headMap_supported (tail : Nat) (w : Q') (K : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    SupportedQuaternionBlocks (tail+1) (headMap w K p) :=
  conditionalHeat_supported (by omega) w K (copy_supported (by omega) hp)

/-- The existing normalized kernel marginal preserves the original mean. -/
theorem headMap_mean (tail : Nat) (w : Q') (K : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    quaternionHaar (tail+1) (headMap w K p) ≈ quaternionHaar (tail+1) p :=
  Q'.eqv_trans _ _ _
    (conditionalHeat_mean (by omega) w K (copy_supported (by omega) hp) (copy_spare_independent p))
    (haar_copy tail p)

/-- Its pairing is pinned to the original two-link Haar integral. -/
theorem headMap_pairing (tail : Nat) (w : Q') (K : Nat) (p q : RatPoly) :
    quaternionHaar (tail+1) (polyMul (headMap w K p) q) ≈ heatPair tail w K p q :=
  Q'.eqv_symm (SU2QuaternionHeadChainComposition.head_pairing (tail+1) 1
    (polyMul (relativeHeat w K) (copy p)) q)

/-- The quantitative estimate is about the computed local operator, not a
diagonal surrogate. Product composition and endpoint weights are not asserted. -/
theorem headMap_defect_le_angular (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    quaternionHaar (tail+1) (polyMul p p) -
        quaternionHaar (tail+1) (polyMul p (headMap w K p)) ≤
      ((1 : Q')-w) * quaternionHaar (tail+1) (angularSquare p) := by
  have he := Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm p (headMap w K p)))
    (headMap_pairing tail w K p p)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ he)))
    (polynomial_defect_le_angular tail hw0 hw1 K hK p hp)

end YMGap.Continuum.SU2QuaternionHeadHeatDiagonal

#print axioms YMGap.Continuum.SU2QuaternionHeadHeatDiagonal.harmonic_pair
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatDiagonal.polynomial_pair
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatDiagonal.polynomial_diagonal
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatDiagonal.polynomial_defect
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatDiagonal.polynomial_pair_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatDiagonal.polynomial_defect_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatDiagonal.polynomial_defect_le_angular
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatDiagonal.headMap_pairing
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatDiagonal.headMap_defect_le_angular
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatDiagonal.headMap_supported
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatDiagonal.headMap_mean
