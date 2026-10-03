/-
# Centered contraction from an actual certified one-factor floor

Subtract the supplied certified constant `1-eta` from ONE original factor,
retain all remaining original factors, and apply weighted Cauchy--Schwarz.
Both exact product marginals give residual mass eta. The existing exact
projection/fluctuation Pythagoras then tensorizes this rate without a
link-count penalty. Empty selections average all lower coordinates.

The input is a Type-valued polynomial positivity certificate, NOT an assumed
norm estimate. Spatial potentials, original terminal normalization, and
interacting response comparisons are not supplied by this Haar theorem.
-/

import YMGap.Continuum.SU2QuaternionProductHeatTensorization

namespace YMGap.Continuum.SU2QuaternionProductHeatCertifiedFloorContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
  (productHeatCertificate removed_pair_zero)
open YMGap.Continuum.SU2QuaternionProductHeatTensorization (productMap_square_split)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem haar_neg (n : Nat) : ∀ p : RatPoly,
    H n (polyNeg p) ≈ -(H n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono n t.1))
        (haar_neg n rest)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem residual_pair (n : Nat) (U V p q : RatPoly) (delta : Q') :
    weightedPair n (polyMul (polyAdd U (polyNeg (cap delta))) V) p q ≈
      weightedPair n (polyMul U V) p q + -(delta * weightedPair n V p q) := by
  let s := polyMul p q
  have hc : H n (polyMul (cap delta) (polyMul s V)) ≈
      delta * H n (polyMul s V) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left delta _))
      (quaternionHaar_polySmul _ _ _)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.add (.var 1) (.neg (.var 3))) (.var 2)))
    (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.neg (.mul (.var 3) (.mul (.var 0) (.var 2)))))
    (by decide) (fun
      | 0 => s
      | 1 => U
      | 2 => V
      | _ => cap delta)))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (haar_neg _ _) (Q'.neg_eqv_congr _ _ hc))))

private theorem factor_margin (eta a : Q') :
    a + -((1-eta)*a) ≈ eta*a :=
  poly_identity_of_normal_eq
    (.add (.var 1) (.neg (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))))
    (.mul (.var 0) (.var 1)) (by decide) (fun
      | 0 => eta
      | _ => a)

private theorem lower_diagonal (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hn : ids.Nodup) (hi : ∀ i, i ∈ ids → i < n) {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) :
    weightedPair (n+n) (productHeat n w K ids) f f ≈ H n (polyMul f f) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (productHeat_lower_marginal n w K ids hn hi _ (supported_polyMul hf hf))

private theorem upper_diagonal (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hn : ids.Nodup) (hi : ∀ i, i ∈ ids → i < n) {g : RatPoly}
    (hg : SupportedQuaternionBlocks n g) :
    weightedPair (n+n) (productHeat n w K ids) (liftBoundary n g) (liftBoundary n g) ≈
      H n (polyMul g g) := by
  change H (n+n)
    (polyMul (polyMul (liftBoundary n g) (liftBoundary n g)) (productHeat n w K ids)) ≈ _
  rw [← lift_product]
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (productHeat_upper_marginal n w K ids hn hi _ (supported_polyMul hg hg))

/-- One certified residual factor gives eta squared in the full original
product pairing; all other factors remain in the positivity witness. -/
theorem productMap_conditional_pair_bound (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (eta : Q') (_heta0 : (0 : Q') ≤ eta) (_heta1 : eta ≤ 1)
    (i : Nat) (ids : List Nat) (hn : ids.Nodup) (hi : i < n) (hnot : i ∉ ids)
    (hids : ∀ j, j ∈ ids → j < n)
    (P : Certificate (n+n)
      (polyAdd (heatAt i (n+i) w K) (polyNeg (cap (1-eta)))))
    {f g : RatPoly} (hf : SupportedQuaternionBlocks n f)
    (hg : SupportedQuaternionBlocks n g)
    (hc : RatPolyCoeffEqv (project i f) polyZero) :
    H n (polyMul (productMap n w K (i::ids) f) g) *
        H n (polyMul (productMap n w K (i::ids) f) g) ≤
      (eta*eta) * (H n (polyMul f f) * H n (polyMul g g)) := by
  let U := heatAt i (n+i) w K
  let V := productHeat n w K ids
  let W := polyMul U V
  let R := polyMul (polyAdd U (polyNeg (cap (1-eta)))) V
  let G := liftBoundary n g
  have hnall : (i::ids).Nodup := List.nodup_cons.mpr ⟨hnot, hn⟩
  have hiall : ∀ j, j ∈ i::ids → j < n := by
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hi
    · exact hids j hj
  have hp : weightedPair (n+n) W f G ≈
      H n (polyMul (productMap n w K (i::ids) f) g) :=
    kernelMap_pairing n W f g
  have hpR : weightedPair (n+n) R f G ≈
      H n (polyMul (productMap n w K (i::ids) f) g) :=
    Q'.eqv_trans _ _ _ (residual_pair _ U V f G _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hp
        (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (removed_pair_zero n w K i ids hi hnot hids f g hc))
          (Q'.mul_zero_eqv _))))
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : -(0 : Q') ≈ 0))
          (Q'.eqv_of_eq (Q'.add_zero' _))))
  have hlR : weightedPair (n+n) R f f ≈ eta * H n (polyMul f f) :=
    Q'.eqv_trans _ _ _ (residual_pair _ U V f f _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (lower_diagonal n w K (i::ids) hnall hiall hf)
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _
          (lower_diagonal n w K ids hn hids hf)))) (factor_margin _ _))
  have hrR : weightedPair (n+n) R G G ≈ eta * H n (polyMul g g) :=
    Q'.eqv_trans _ _ _ (residual_pair _ U V G G _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (upper_diagonal n w K (i::ids) hnall hiall hg)
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _
          (upper_diagonal n w K ids hn hids hg)))) (factor_margin _ _))
  have hR : Certificate (n+n) R :=
    P.mul (productHeatCertificate n hw0 hw1 K hK ids hids)
  have hf2 : SupportedQuaternionBlocks (n+n) f :=
    fun t ht => Nat.le_trans (hf t ht) (Nat.mul_le_mul_left 4 (by omega))
  have hcs := weighted_cauchySchwarz (n+n) R f G hR hf2 (lift_supported hg n)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qmul hpR hpR))
    (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (qmul hlR hrR)
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2))) (by decide)
        (fun
          | 0 => eta
          | 1 => H n (polyMul f f)
          | _ => H n (polyMul g g))))))

/-- The conditional norm bound uses its actual output as the test, including
the constructive zero-norm branch. -/
theorem productMap_conditional_square_bound (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (eta : Q') (heta0 : (0 : Q') ≤ eta) (heta1 : eta ≤ 1)
    (i : Nat) (ids : List Nat) (hn : ids.Nodup) (hi : i < n) (hnot : i ∉ ids)
    (hids : ∀ j, j ∈ ids → j < n)
    (P : Certificate (n+n)
      (polyAdd (heatAt i (n+i) w K) (polyNeg (cap (1-eta)))))
    {f : RatPoly} (hf : SupportedQuaternionBlocks n f)
    (hc : RatPolyCoeffEqv (project i f) polyZero) :
    H n (polyMul (productMap n w K (i::ids) f) (productMap n w K (i::ids) f)) ≤
      (eta*eta) * H n (polyMul f f) := by
  have hiall : ∀ j, j ∈ i::ids → j < n := by
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hi
    · exact hids j hj
  let A := H n (polyMul (productMap n w K (i::ids) f) (productMap n w K (i::ids) f))
  let F := H n (polyMul f f)
  have h := productMap_conditional_pair_bound n hw0 hw1 K hK eta heta0 heta1
    i ids hn hi hnot hids P hf (productMap_supported n w K (i::ids) hiall hf) hc
  change A*A ≤ (eta*eta)*(F*A) at h
  change A ≤ (eta*eta)*F
  by_cases hpos : (0 : Q') < A
  · exact Q'.le_of_mul_le_mul_left
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
          (Q'.mul_comm_eqv _ _)))) hpos
  · have hz : A ≤ (0 : Q') := by
      change ¬ ((0 : Int) * (A.den : Int) < A.num * 1) at hpos
      have hn0 : A.num ≤ 0 := by
        simpa only [Int.zero_mul, Int.mul_one] using Int.not_lt.mp hpos
      change A.num * 1 ≤ (0 : Int) * (A.den : Int)
      simpa only [Int.zero_mul, Int.mul_one] using hn0
    exact Q'.le_trans' _ _ _ hz (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ heta0 heta0) (Certificate.haar_nonnegative (.square f hf)))

/-- The actual product map contracts every Haar-centered supported input by
eta squared, independently of the number of distinct selected links.
Each selected original factor carries its OWN supplied floor certificate. -/
theorem productMap_centered_square_bound (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) (eta : Q') (heta0 : (0 : Q') ≤ eta) (heta1 : eta ≤ 1) :
    ∀ (ids : List Nat), ids.Nodup → (∀ i, i ∈ ids → i < n) →
      (∀ i, i ∈ ids → Certificate (n+n)
        (polyAdd (heatAt i (n+i) w K) (polyNeg (cap (1-eta))))) →
      ∀ {f : RatPoly}, SupportedQuaternionBlocks n f → H n f ≈ 0 →
      H n (polyMul (productMap n w K ids f) (productMap n w K ids f)) ≤
        (eta*eta) * H n (polyMul f f)
  | [], _, _, _, f, hf, hc => by
      have hz : RatPolyCoeffEqv (productMap n w K [] f) polyZero :=
        (productMap_nil n w K f hf).trans
          ((RatPolyCoeffEqv.smul_coefficient hc polyOne).trans (RatPolyCoeffEqv.zero_smul polyOne))
      have hs : H n (polyMul (productMap n w K [] f) (productMap n w K [] f)) ≈ 0 :=
        haar_of_coeff (hz.mul hz)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hs)
        (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ heta0 heta0)
          (Certificate.haar_nonnegative (.square f hf)))
  | i::ids, hn, hids, hfloor, f, hf, hc => by
      have hnd := List.nodup_cons.mp hn
      have hi := hids i List.mem_cons_self
      have ht (j : Nat) (hj : j ∈ ids) : j < n := hids j (List.mem_cons_of_mem i hj)
      have hp := productMap_centered_square_bound n hw0 hw1 K hK eta heta0 heta1 ids hnd.2 ht
        (fun j hj => hfloor j (List.mem_cons_of_mem i hj))
        (project_supported i hf) (Q'.eqv_trans _ _ _ (project_mean n i hi f) hc)
      have hq := productMap_conditional_square_bound n hw0 hw1 K hK eta heta0 heta1
        i ids hnd.2 hi hnd.1 ht (hfloor i List.mem_cons_self)
        (fluctuation_supported i hf) (project_fluctuation_zero i f)
      have hsum := Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hp)
        (Q'.add_le_add_left _ _ _ hq)
      have hbudget : (eta*eta) * H n (polyMul (project i f) (project i f)) +
          (eta*eta) * H n (polyMul (fluctuation i f) (fluctuation i f)) ≈
          (eta*eta) * H n (polyMul f f) :=
        Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (square_decomposition n i hi f)))
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (productMap_square_split n w K i ids hi hnd.1 ht hf))
        (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hbudget))

#print axioms productMap_conditional_pair_bound
#print axioms productMap_conditional_square_bound
#print axioms productMap_centered_square_bound

end YMGap.Continuum.SU2QuaternionProductHeatCertifiedFloorContraction
