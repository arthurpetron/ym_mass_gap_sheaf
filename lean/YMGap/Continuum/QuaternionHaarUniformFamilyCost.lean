/-
# Uniform finite-family cost under one original normalized Haar weight

Each supported member has the same diagonal ceiling under a square-certified
weight. Constructive weighted Cauchy--Schwarz and rational Young give the
same ceiling for every mixed entry, including zero ceilings. Expanding the
literal signed family as an ordered Gram sum then charges the square of the
coefficient L1 sum. Repeated indices and the empty list need no exception.

This is an absolute weighted cost, not a variance-relative estimate.
-/

import YMGap.Continuum.QuaternionHaarSparseFamilyCost
import YMGap.Continuum.QuaternionHaarBiadditive
import YMGap.Continuum.FiniteWeightedGramSOS
import YMGap.Continuum.GNSHilbertSpace
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.QuaternionHaarUniformFamilyCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence
open YMGap.Continuum.QuaternionHaarNormalizedMomentLinear
open YMGap.Continuum.QuaternionHaarCenteredResponse
open YMGap.Continuum.QuaternionHaarSparseFamilyCost
open YMGap.Continuum.RationalFiniteSparseGram (weighted_young)

local infix:50 " ≈ " => Q'.eqv

private theorem sum_two (a : Q') : a+a ≈ 2*a :=
  poly_identity_of_normal_eq
    (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
    (by decide) (fun _ => a)

private theorem abs_square (a : Q') : Q'.abs a*Q'.abs a ≈ a*a := by
  unfold Q'.abs
  split
  · exact Q'.eqv_refl _
  · exact poly_identity_of_normal_eq
      (.mul (.neg (.var 0)) (.neg (.var 0))) (.mul (.var 0) (.var 0))
      (by decide) (fun _ => a)

/-- Absolute mixed entry under the SAME normalized, square-certified weight.
The ceiling may be zero; no square root or strict ceiling is required. -/
theorem normalized_pair_abs_le {blocks : Nat} {W p q : RatPoly} {C : Q'}
    (H : Certificate blocks W) (hW : (0 : Q') < quaternionHaar blocks W)
    (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q)
    (hpc : normalizedMoment blocks W (polyMul p p) hW ≤ C)
    (hqc : normalizedMoment blocks W (polyMul q q) hW ≤ C) :
    Q'.abs (normalizedMoment blocks W (polyMul p q) hW) ≤ C := by
  let x := normalizedMoment blocks W (polyMul p q) hW
  let a := normalizedMoment blocks W (polyMul p p) hW
  let b := normalizedMoment blocks W (polyMul q q) hW
  have ha : (0 : Q') ≤ a := normalized_square_nonnegative H hW hp
  have hb : (0 : Q') ≤ b := normalized_square_nonnegative H hW hq
  have hcs : x*x ≤ a*b := normalized_cauchySchwarz H hW hp hq
  have hsquare : (Q'.abs x)*(Q'.abs x) ≤ ((1 : Q')*1)*(a*b) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_square x))
      (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv
        (Q'.eqv_symm (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right ((1 : Q')*1) 1 (a*b)
            (Q'.one_mul_eqv (1 : Q')))
          (Q'.one_mul_eqv (a*b))))))
  have hyoung : 2*Q'.abs x ≤ (1 : Q')*(a+b) :=
    weighted_young Q'.zero_le_one ha hb hsquare
  have hceiling : (1 : Q')*(a+b) ≤ 2*C :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv (a+b)))
      (Q'.le_trans' _ _ _ (Q'.add_le_add hpc hqc)
        (Q'.le_of_eqv (sum_two C)))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ hyoung hceiling) (by decide)

private theorem normalized_scaled_pair {blocks : Nat} {W p q : RatPoly}
    (hW : (0 : Q') < quaternionHaar blocks W) (a b : Q') :
    normalizedMoment blocks W (polyMul (polySmul a p) (polySmul b q)) hW ≈
      (a*b)*normalizedMoment blocks W (polyMul p q) hW := by
  have hcoeff : RatPolyCoeffEqv
      (polyMul (polySmul a p) (polySmul b q))
      (polySmul (a*b) (polyMul p q)) :=
    (RatPolyCoeffEqv.polyMul_smul_left a p (polySmul b q)).trans
      (((RatPolyCoeffEqv.polyMul_smul_right b p q).smul a).trans
        (RatPolyCoeffEqv.smul_assoc a b (polyMul p q)))
  exact Q'.eqv_trans _ _ _
    (normalizedMoment_congr hW hW (RatPolyCoeffEqv.refl W) hcoeff)
    (normalizedMoment_smul hW)

/-- All signed positional cross terms are retained, including repeated
members. The only assumption on each member is its supported diagonal cost
under the SAME positive normalized Haar weight. -/
theorem normalized_family_l1_cost {Index : Type} {blocks : Nat} {W : RatPoly}
    (H : Certificate blocks W) (hW : (0 : Q') < quaternionHaar blocks W)
    (f : Index → RatPoly) (c : Index → Q') (xs : List Index) (C : Q')
    (hf : ∀ i, i ∈ xs → SupportedQuaternionBlocks blocks (f i))
    (hcost : ∀ i, i ∈ xs →
      normalizedMoment blocks W (polyMul (f i) (f i)) hW ≤ C) :
    normalizedMoment blocks W
      (polyMul (finitePolySum (fun i => polySmul (c i) (f i)) xs)
        (finitePolySum (fun i => polySmul (c i) (f i)) xs)) hW ≤
      C*(listQSum (fun i => Q'.abs (c i)) xs *
        listQSum (fun i => Q'.abs (c i)) xs) := by
  let g := fun i j => normalizedMoment blocks W (polyMul (f i) (f j)) hW
  let F := fun i => polySmul (c i) (f i)
  have hentry : ∀ i, i ∈ xs → ∀ j, j ∈ xs →
      normalizedMoment blocks W (polyMul (F i) (F j)) hW ≤
        C*(Q'.abs (c i)*Q'.abs (c j)) := by
    intro i hi j hj
    have hpair : Q'.abs (g i j) ≤ C :=
      normalized_pair_abs_le H hW (hf i hi) (hf j hj)
        (hcost i hi) (hcost j hj)
    have hscaled := normalized_scaled_pair (p := f i) (q := f j)
      hW (c i) (c j)
    have habs := YMGap.Continuum.QuaternionHaarBiadditive.abs_product_bound
      (YMGap.Constructive.ExpNeg.abs_mul_le (c i) (c j)) hpair
    exact Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hscaled))
        (Q'.le_trans' _ _ _ habs (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))))
  have hsum :
      listQSum (fun i => listQSum (fun j =>
        normalizedMoment blocks W (polyMul (F i) (F j)) hW) xs) xs ≤
      listQSum (fun i => listQSum (fun j =>
        C*(Q'.abs (c i)*Q'.abs (c j))) xs) xs :=
    YMGap.Continuum.Z4FiniteCylinderQuadraticStability.listQSum_mono
      _ _ xs (fun i hi =>
        YMGap.Continuum.Z4FiniteCylinderQuadraticStability.listQSum_mono
          _ _ xs (fun j hj => hentry i hi j hj))
  have hcollapse :
      listQSum (fun i => listQSum (fun j =>
        C*(Q'.abs (c i)*Q'.abs (c j))) xs) xs ≈
      C*(listQSum (fun i => Q'.abs (c i)) xs *
        listQSum (fun j => Q'.abs (c j)) xs) :=
    Q'.eqv_trans _ _ _
      (listQSum_congr (fun i =>
        YMGap.Continuum.FiniteDeterministicKernelPushforward.listQSum_mul_left
          C (fun j => Q'.abs (c i)*Q'.abs (c j)) xs) xs)
      (Q'.eqv_trans _ _ _
        (YMGap.Continuum.FiniteDeterministicKernelPushforward.listQSum_mul_left
          C (fun i => listQSum (fun j =>
            Q'.abs (c i)*Q'.abs (c j)) xs) xs)
        (Q'.mul_eqv_congr_left C _ _
          (YMGap.Continuum.FiniteWeightedGramSOS.listQSum_product
            (fun i => Q'.abs (c i)) (fun j => Q'.abs (c j)) xs xs)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (normalized_sum_square hW F xs))
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hcollapse))

#print axioms normalized_pair_abs_le
#print axioms normalized_scaled_pair
#print axioms normalized_family_l1_cost

end YMGap.Continuum.QuaternionHaarUniformFamilyCost
