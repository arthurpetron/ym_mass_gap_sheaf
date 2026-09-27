/-
# Cost-one deletion of reflection-fixed faces in the ORIGINAL action

Setting a crossing nome to zero deletes precisely that original heat factor:
the vacuum coefficient is one and every positive-spin coefficient vanishes.
Coefficientwise Gram comparison therefore orders nested subsets of the fixed
crossing faces, with the full reflected lower/upper bulk retained. The result
is pinned to the actual selected-face polynomial product and its Haar integral,
not a decoupled partition model. It holds at every finite cutoff and w >= 0.
For 0 < w < 1 the comparisons pass to the EXISTING fixed-volume CReal
heat-cutoff limits, with their already constructed explicit Cauchy moduli.

The observable version is an UNNORMALIZED reflected quadratic inequality.
Arbitrary collars need not consist of fixed faces or have reflection-paired
backgrounds. This does not remove the response collar cost in general, imply
monotonicity of normalized correlations, or prove spatial/scaling decay.
-/

import YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles
import YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder
import YMGap.Continuum.FusedAmplitudeDerivation
import YMGap.Continuum.RCCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabReflectionFixedDeletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentObservableReflection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabLocalBulkSelection (profileHeat profileHeat_supported)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity (reflectedInsertion)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator numeratorLimit numerator_converges)
open YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison (factorProduct)
open YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

theorem coeffW_zero_nome (s : Nat) : coeffW 0 (s+1) ≈ 0 := by
  have hn : 0 < c4 (s+1) := Nat.mul_pos (by omega) (by omega)
  have hp : qpow 0 (c4 (s+1)) ≈ 0 := by
    rw [← Nat.sub_add_cancel hn]
    exact Q'.mul_zero_eqv _
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hp) (Q'.mul_zero_eqv _)

/-- Nome zero, not cutoff zero: deletion works at EVERY representation cutoff. -/
theorem faceHeat_zero_nome (K extent id : Nat) :
    RatPolyCoeffEqv (faceHeatPolynomial 0 K extent id) polyOne := by
  have ht : ∀ n, RatPolyCoeffEqv (faceHeatTail 0 extent id 1 n) polyZero := by
    intro n
    unfold faceHeatTail
    have hz : ∀ ids : List Nat, RatPolyCoeffEqv
        (finitePolySum (fun i => faceHeatTerm 0 extent id (1+i)) ids) polyZero := by
      intro ids
      induction ids with
      | nil => exact RatPolyCoeffEqv.refl _
      | cons i ids ih =>
        have hi : RatPolyCoeffEqv (faceHeatTerm 0 extent id (1+i)) polyZero := by
          unfold faceHeatTerm
          rw [Nat.add_comm 1 i]
          exact (RatPolyCoeffEqv.smul_coefficient (coeffW_zero_nome i) _).trans
            (RatPolyCoeffEqv.zero_smul _)
        exact (hi.add ih).trans (RatPolyCoeffEqv.zero_add _)
    exact hz _
  exact (BF4ExactSlabSmallNomeFaceRemainder.faceHeat_eq_one_add 0 extent id K).trans
    (((RatPolyCoeffEqv.refl _).add (ht K)).trans (RatPolyCoeffEqv.add_zero _))

private theorem factors_one : ∀ ids : List Nat, factorProduct (fun _ => 1) ids ≈ 1
  | [] => Q'.eqv_refl _
  | _::ids => Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (factors_one ids)

/-- All original bulk factors stay fixed; only crossing nomes increase. -/
theorem fullQuadratic_mono (bulk : Nat → Q') (bulkCutoff : Nat → Nat)
    (a b : Nat → Q') (ha : ∀ id, (0 : Q') ≤ a id) (hb : ∀ id, (0 : Q') ≤ b id)
    (crossingCutoff : Nat → Nat) {half : Nat} (e : PlaquetteExpression half)
    (hab : ∀ id, id ∈ centralFixedFaceIds half → a id ≤ b id) :
    fullQuadratic bulk bulkCutoff a crossingCutoff e ≤
      fullQuadratic bulk bulkCutoff b crossingCutoff e := by
  have h := fullQuadratic_comparison bulk bulkCutoff a b (fun _ => 1) ha hb
    (fun _ => Q'.zero_le_one) crossingCutoff e (fun id hi s _ =>
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
        (FusedAmplitudeDerivation.coeffW_mono_w (ha id) (hab id hi) s))
  have hp := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (factors_one (centralFixedFaceIds half)))
    (Q'.one_mul_eqv (fullQuadratic bulk bulkCutoff a crossingCutoff e))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hp) h

def maskedNome (w : Q') (keep : Nat → Bool) (id : Nat) : Q' := if keep id then w else 0

private theorem masked_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (keep : Nat → Bool) (id : Nat) :
    (0 : Q') ≤ maskedNome w keep id := by
  unfold maskedNome
  split
  · exact hw
  · exact Q'.le_refl' _

private theorem masked_product (w : Q') (K extent : Nat) (keep : Nat → Bool) : ∀ ids : List Nat,
    RatPolyCoeffEqv (profileHeat (maskedNome w keep) (fun _ => K) extent ids)
      (polynomialProduct (faceHeatPolynomial w K extent) (ids.filter keep))
  | [] => RatPolyCoeffEqv.refl _
  | id::ids => by
    cases hi : keep id with
    | false =>
      simp only [profileHeat, polynomialProduct, List.foldr, maskedNome,
        List.filter_cons, hi, Bool.false_eq_true, if_false]
      exact ((faceHeat_zero_nome K extent id).mul (masked_product w K extent keep ids)).trans
        (RatPolyCoeffEqv.one_mul _)
    | true =>
      simp only [profileHeat, polynomialProduct, List.foldr, maskedNome, hi, if_true,
        List.filter_cons_of_pos hi]
      exact (RatPolyCoeffEqv.refl _).mul (masked_product w K extent keep ids)

/-- Actual original face IDs: neither half-bulk is deleted. -/
def keptFaceIds (half : Nat) (keep : Nat → Bool) : List Nat :=
  centralLowerFaceIds half ++ ((centralFixedFaceIds half).filter keep ++ centralUpperFaceIds half)

theorem masked_original_product (w : Q') (K half : Nat) (keep : Nat → Bool) :
    RatPolyCoeffEqv (fullHeat (fun _ => w) (fun _ => K) (maskedNome w keep) (fun _ => K) half)
      (polynomialProduct (faceHeatPolynomial w K (centralExtent half)) (keptFaceIds half keep)) := by
  have h := fullHeat_split (fun _ => w) (fun _ => K) (maskedNome w keep) (fun _ => K) half
  have hm := (masked_product w K (centralExtent half) keep (centralFixedFaceIds half)).mul_right
    (upperHeat (fun _ => w) (fun _ => K) half)
  have hp := (polynomialProduct_append (faceHeatPolynomial w K (centralExtent half))
    (centralLowerFaceIds half) ((centralFixedFaceIds half).filter keep ++ centralUpperFaceIds half)).trans
      ((polynomialProduct_append (faceHeatPolynomial w K (centralExtent half))
        ((centralFixedFaceIds half).filter keep) (centralUpperFaceIds half)).mul_left _)
  exact (h.trans (hm.mul_left _)).trans hp.symm

theorem masked_original_quadratic (w : Q') (K : Nat) {half : Nat}
    (keep : Nat → Bool) (e : PlaquetteExpression half) :
    fullQuadratic (fun _ => w) (fun _ => K) (maskedNome w keep) (fun _ => K) e ≈
      numerator w (blocks half) (centralExtent half) (keptFaceIds half keep) (reflectedInsertion e) K :=
  haar_of_coeff_eqv _ ((masked_original_product w K half keep).mul_left _)

/-- Nested fixed-face deletion, for the SAME original unnormalized quadratic. -/
theorem original_quadratic_nested {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) {half : Nat}
    (keep more : Nat → Bool) (hsub : ∀ id, id ∈ centralFixedFaceIds half → keep id = true → more id = true)
    (e : PlaquetteExpression half) :
    numerator w (blocks half) (centralExtent half) (keptFaceIds half keep) (reflectedInsertion e) K ≤
      numerator w (blocks half) (centralExtent half) (keptFaceIds half more) (reflectedInsertion e) K := by
  have h := fullQuadratic_mono (fun _ => w) (fun _ => K) (maskedNome w keep) (maskedNome w more)
    (masked_nonnegative hw keep) (masked_nonnegative hw more) (fun _ => K) e (by
      intro id hi
      cases hk : keep id with
      | false => simpa only [maskedNome, hk, Bool.false_eq_true, if_false] using masked_nonnegative hw more id
      | true => simp only [maskedNome, hk, hsub id hi hk, if_true]; exact Q'.le_refl' _)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (masked_original_quadratic w K keep e))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (masked_original_quadratic w K more e)))

/-- Cost is exactly one, independent of w, K and the number of deleted fixed faces. -/
theorem original_quadratic_deletion {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) {half : Nat}
    (keep : Nat → Bool) (e : PlaquetteExpression half) :
    numerator w (blocks half) (centralExtent half) (keptFaceIds half keep) (reflectedInsertion e) K ≤
      numerator w (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
        (reflectedInsertion e) K := by
  have h := fullQuadratic_mono (fun _ => w) (fun _ => K) (maskedNome w keep) (fun _ => w)
    (masked_nonnegative hw keep) (fun _ => hw) (fun _ => K) e (by
      intro id _
      unfold maskedNome
      split
      · exact Q'.le_refl' _
      · exact hw)
  rw [fullQuadratic_diagonal] at h
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (masked_original_quadratic w K keep e)) h

private theorem unit_numerator (w : Q') (K half : Nat) (ids : List Nat) :
    numerator w (blocks half) (centralExtent half) ids (reflectedInsertion (.unit : PlaquetteExpression half)) K ≈
      heatProductHaar w (blocks half) (centralExtent half) ids K := by
  let P := polynomialProduct (faceHeatPolynomial w K (centralExtent half)) ids
  have hs : SupportedQuaternionBlocks (blocks half) P := profileHeat_supported (fun _ => w) (fun _ => K) _ ids
  have hu := (PaddedPolynomialCoeffEqv.mul (lower_reflection (.unit : PlaquetteExpression half))
    (PaddedPolynomialCoeffEqv.refl (blocks half) polyOne)).mul (PaddedPolynomialCoeffEqv.refl _ P)
  have hh := hu.haar
    (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) (supported_one _)) hs)
    (supported_polyMul (supported_polyMul (supported_one _) (supported_one _)) hs)
  exact Q'.eqv_trans _ _ _ hh (haar_of_coeff_eqv _
    (((RatPolyCoeffEqv.one_mul polyOne).mul_right P).trans (RatPolyCoeffEqv.one_mul P)))

theorem original_partition_nested {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (keep more : Nat → Bool) (hsub : ∀ id, id ∈ centralFixedFaceIds half → keep id = true → more id = true) :
    heatProductHaar w (blocks half) (centralExtent half) (keptFaceIds half keep) K ≤
      heatProductHaar w (blocks half) (centralExtent half) (keptFaceIds half more) K :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (unit_numerator w K half _))
    (Q'.le_trans' _ _ _ (original_quadratic_nested hw K keep more hsub .unit)
      (Q'.le_of_eqv (unit_numerator w K half _)))

theorem original_partition_deletion {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) (keep : Nat → Bool) :
    heatProductHaar w (blocks half) (centralExtent half) (keptFaceIds half keep) K ≤ fullActionValue w K half :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (unit_numerator w K half _))
    (Q'.le_trans' _ _ _ (original_quadratic_deletion hw K keep .unit)
      (Q'.le_of_eqv (unit_numerator w K half _)))

/-- This removes the heat cutoff at FIXED volume, not physical lattice spacing. -/
theorem original_quadratic_limit_nested (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat} (keep more : Nat → Bool)
    (hsub : ∀ id, id ∈ centralFixedFaceIds half → keep id = true → more id = true)
    (e : PlaquetteExpression half) :
    CReal.leEv
      (numeratorLimit w hw0 hw1 (blocks half) (centralExtent half) (keptFaceIds half keep) (reflectedInsertion e))
      (numeratorLimit w hw0 hw1 (blocks half) (centralExtent half) (keptFaceIds half more) (reflectedInsertion e)) := by
  apply CReal.leEv_of_ofQ'_limit_le (numerator_converges w hw0 hw1 _ _ _ _)
    (numerator_converges w hw0 hw1 _ _ _ _)
  intro epsilon he
  exact ⟨0, fun K _ => Q'.le_trans' _ _ _ (original_quadratic_nested (Q'.le_of_lt hw0) K keep more hsub e)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

theorem original_quadratic_limit_deletion (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat} (keep : Nat → Bool) (e : PlaquetteExpression half) :
    CReal.leEv
      (numeratorLimit w hw0 hw1 (blocks half) (centralExtent half) (keptFaceIds half keep) (reflectedInsertion e))
      (numeratorLimit w hw0 hw1 (blocks half) (centralExtent half)
        (slabPhysicalFaceEdges (centralExtent half)) (reflectedInsertion e)) := by
  apply CReal.leEv_of_ofQ'_limit_le (numerator_converges w hw0 hw1 _ _ _ _)
    (numerator_converges w hw0 hw1 _ _ _ _)
  intro epsilon he
  exact ⟨0, fun K _ => Q'.le_trans' _ _ _ (original_quadratic_deletion (Q'.le_of_lt hw0) K keep e)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

theorem original_partition_limit_nested (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (keep more : Nat → Bool)
    (hsub : ∀ id, id ∈ centralFixedFaceIds half → keep id = true → more id = true) :
    CReal.leEv
      (heatProductHaarLimit w hw0 hw1 (blocks half) (centralExtent half) (keptFaceIds half keep))
      (heatProductHaarLimit w hw0 hw1 (blocks half) (centralExtent half) (keptFaceIds half more)) := by
  apply CReal.leEv_of_ofQ'_limit_le (heatProductHaar_converges w hw0 hw1 _ _ _)
    (heatProductHaar_converges w hw0 hw1 _ _ _)
  intro epsilon he
  exact ⟨0, fun K _ => Q'.le_trans' _ _ _ (original_partition_nested (Q'.le_of_lt hw0) K half keep more hsub)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

theorem original_partition_limit_deletion (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (keep : Nat → Bool) :
    CReal.leEv (heatProductHaarLimit w hw0 hw1 (blocks half) (centralExtent half) (keptFaceIds half keep))
      (fullActionLimit w hw0 hw1 half) := by
  apply CReal.leEv_of_ofQ'_limit_le (heatProductHaar_converges w hw0 hw1 _ _ _)
    (heatProductHaar_converges w hw0 hw1 _ _ _)
  intro epsilon he
  exact ⟨0, fun K _ => Q'.le_trans' _ _ _ (original_partition_deletion (Q'.le_of_lt hw0) K half keep)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

end YMGap.Continuum.BF4ExactSlabReflectionFixedDeletion

#print axioms YMGap.Continuum.BF4ExactSlabReflectionFixedDeletion.coeffW_zero_nome
#print axioms YMGap.Continuum.BF4ExactSlabReflectionFixedDeletion.faceHeat_zero_nome
#print axioms YMGap.Continuum.BF4ExactSlabReflectionFixedDeletion.fullQuadratic_mono
#print axioms YMGap.Continuum.BF4ExactSlabReflectionFixedDeletion.maskedNome
#print axioms YMGap.Continuum.BF4ExactSlabReflectionFixedDeletion.keptFaceIds
#print axioms YMGap.Continuum.BF4ExactSlabReflectionFixedDeletion.masked_original_product
#print axioms YMGap.Continuum.BF4ExactSlabReflectionFixedDeletion.masked_original_quadratic
#print axioms YMGap.Continuum.BF4ExactSlabReflectionFixedDeletion.original_quadratic_nested
#print axioms YMGap.Continuum.BF4ExactSlabReflectionFixedDeletion.original_quadratic_deletion
#print axioms YMGap.Continuum.BF4ExactSlabReflectionFixedDeletion.original_partition_nested
#print axioms YMGap.Continuum.BF4ExactSlabReflectionFixedDeletion.original_partition_deletion
#print axioms YMGap.Continuum.BF4ExactSlabReflectionFixedDeletion.original_quadratic_limit_nested
#print axioms YMGap.Continuum.BF4ExactSlabReflectionFixedDeletion.original_quadratic_limit_deletion
#print axioms YMGap.Continuum.BF4ExactSlabReflectionFixedDeletion.original_partition_limit_nested
#print axioms YMGap.Continuum.BF4ExactSlabReflectionFixedDeletion.original_partition_limit_deletion
