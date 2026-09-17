/-
# Conditional contraction with the ENTIRE original product kernel retained

Subtract the certified constant floor from one selected heat factor, then
multiply by every remaining heat factor. Both exact product marginals make
the residual diagonal pairings equal to (1-headFloor) times the original
Haar square norms. Conditional centering kills the removed cross pairing.
Weighted Cauchy--Schwarz gives the one-link squared rate without a product
floor or a volume penalty. This is an ordinary Haar estimate; spatial action
factors and the interacting OS vacuum are not removed by this argument.
-/

import YMGap.Continuum.SU2QuaternionProductHeatMarginals
import YMGap.Continuum.SU2QuaternionRelativeHeatContraction

namespace YMGap.Continuum.SU2QuaternionProductHeatContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatContraction
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

local infix:50 " ≈ " => Q'.eqv

private theorem sum_congr (f g : Nat → RatPoly) : ∀ xs : List Nat,
    (∀ i, i ∈ xs → f i = g i) → finitePolySum f xs = finitePolySum g xs
  | [], _ => rfl
  | i::xs, h => by
      simp only [finitePolySum, h i List.mem_cons_self,
        sum_congr f g xs (fun j hj => h j (List.mem_cons_of_mem i hj))]

private theorem heatAt_eq_prefix (a b : Nat) (w : Q') (K : Nat) :
    heatAt a b w K = heatPrefix w K (scalarAt a b) := by
  unfold heatAt heatPrefix
  apply sum_congr
  intro spin hspin
  rw [coeffAt_heatKernelPacket (List.mem_range.mp hspin)]

/-- The original heat factor's floor on an arbitrary full ambient carrier. -/
def heatAt_floorCertificate {blocks a b : Nat} (ha : a < blocks) (hb : b < blocks)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) :
    Certificate blocks (polyAdd (heatAt a b w K) (polyNeg (cap (headFloor w)))) := by
  let word := PolyQuaternion.mul (PolyQuaternion.coordinateVariable a)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable b))
  have hp : Supported blocks word := (Supported.coordinate ha).mul (Supported.coordinate hb).conj
  have hu : HaarCarrierEqv blocks (polyQuaternionNorm word) polyOne :=
    haarNorm_mul (haarNorm_coordinate ha)
      (HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _))
        (haarNorm_coordinate hb))
  rw [heatAt_eq_prefix]
  exact QuaternionHaarAllNomeHeatCertificate.prefixFloorCertificate hw0 hw1 hp hu K hK

/-- Every other heat factor stays in the constructed positivity witness. -/
def productHeatCertificate (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K) :
    (ids : List Nat) → (∀ i, i ∈ ids → i < n) → Certificate (n+n) (productHeat n w K ids)
  | [], _ => .one _
  | i::ids, hi => by
      have hin := hi i List.mem_cons_self
      have hc : Certificate (n+n) (heatAt i (n+i) w K) :=
        .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
          (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (by decide)
          (fun | 0 => heatAt i (n+i) w K | _ => cap (headFloor w)))
          ((heatAt_floorCertificate (by omega) (by omega) hw0 hw1 K hK).add
            (.constant _ (headFloor w) (Q'.le_of_lt (headFloor_positive hw0 hw1))))
      exact hc.mul (productHeatCertificate n hw0 hw1 K hK ids
        (fun j hj => hi j (List.mem_cons_of_mem i hj)))

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem haar_neg (n : Nat) : ∀ p : RatPoly,
    quaternionHaar n (polyNeg p) ≈ -(quaternionHaar n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono n t.1))
        (haar_neg n rest)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem residual_pair (n : Nat) (U V p q : RatPoly) (delta : Q') :
    weightedPair n (polyMul (polyAdd U (polyNeg (cap delta))) V) p q ≈
      weightedPair n (polyMul U V) p q + -(delta * weightedPair n V p q) := by
  let s := polyMul p q
  have hc : quaternionHaar n (polyMul (cap delta) (polyMul s V)) ≈
      delta * quaternionHaar n (polyMul s V) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left delta _)) (quaternionHaar_polySmul _ _ _)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.add (.var 1) (.neg (.var 3))) (.var 2)))
    (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.neg (.mul (.var 3) (.mul (.var 0) (.var 2)))))
    (by decide) (fun | 0 => s | 1 => U | 2 => V | _ => cap delta)))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (haar_neg _ _) (Q'.neg_eqv_congr _ _ hc))))

private theorem factor_margin (d a : Q') : a + -(d*a) ≈ (1 + -d)*a :=
  poly_identity_of_normal_eq (.add (.var 1) (.neg (.mul (.var 0) (.var 1))))
    (.mul (.add (.const 1) (.neg (.var 0))) (.var 1)) (by decide)
    (fun | 0 => d | _ => a)

private theorem lower_diagonal (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hn : ids.Nodup) (hi : ∀ i, i ∈ ids → i < n) {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) :
    weightedPair (n+n) (productHeat n w K ids) f f ≈ quaternionHaar n (polyMul f f) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (productHeat_lower_marginal n w K ids hn hi _ (supported_polyMul hf hf))

private theorem upper_diagonal (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hn : ids.Nodup) (hi : ∀ i, i ∈ ids → i < n) {g : RatPoly}
    (hg : SupportedQuaternionBlocks n g) :
    weightedPair (n+n) (productHeat n w K ids) (liftBoundary n g) (liftBoundary n g) ≈
      quaternionHaar n (polyMul g g) := by
  change quaternionHaar (n+n)
    (polyMul (polyMul (liftBoundary n g) (liftBoundary n g)) (productHeat n w K ids)) ≈ _
  rw [← lift_product]
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (productHeat_upper_marginal n w K ids hn hi _ (supported_polyMul hg hg))

/-- Conditional centering kills the removed factor, with ALL other heat
factors and the actual output test still present. -/
theorem removed_pair_zero (n : Nat) (w : Q') (K i : Nat) (ids : List Nat)
    (hi : i < n) (hnot : i ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    (f g : RatPoly) (hc : RatPolyCoeffEqv (project i f) polyZero) :
    weightedPair (n+n) (productHeat n w K ids) f (liftBoundary n g) ≈ 0 := by
  let V := productHeat n w K ids
  let G := liftBoundary n g
  have hind : QuaternionBlockIndependent i (polyMul V G) :=
    quaternionBlockIndependent_polyMul
      (productHeat_independent_lower n w K ids hids i hi hnot)
      (lift_lower_independent n g i hi)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.mul (.var 2) (.var 1)) (.var 0)) (by decide)
    (fun | 0 => f | 1 => G | _ => V)))
    (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_eq_after_integratingBlock (n+n) i (by omega) _ f hind)
      (haar_of_coeff ((hc.mul_left _).trans (RatPolyCoeffEqv.mul_zero_right _))))

/-- The one-link strict rate for a conditionally centered input to the SAME
full product map. No product of floors or assumed contraction is used. -/
theorem productMap_conditional_pair_bound (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (i : Nat) (ids : List Nat) (hn : ids.Nodup) (hi : i < n) (hnot : i ∉ ids)
    (hids : ∀ j, j ∈ ids → j < n) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks n f) (hg : SupportedQuaternionBlocks n g)
    (hc : RatPolyCoeffEqv (project i f) polyZero) :
    quaternionHaar n (polyMul (productMap n w K (i::ids) f) g) *
        quaternionHaar n (polyMul (productMap n w K (i::ids) f) g) ≤
      squaredHeatRate w * (quaternionHaar n (polyMul f f) * quaternionHaar n (polyMul g g)) := by
  let U := heatAt i (n+i) w K
  let V := productHeat n w K ids
  let W := polyMul U V
  let R := polyMul (polyAdd U (polyNeg (cap (headFloor w)))) V
  let G := liftBoundary n g
  have hnall : (i::ids).Nodup := List.nodup_cons.mpr ⟨hnot, hn⟩
  have hiall : ∀ j, j ∈ i::ids → j < n := by
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hi
    · exact hids j hj
  have hp : weightedPair (n+n) W f G ≈
      quaternionHaar n (polyMul (productMap n w K (i::ids) f) g) :=
    kernelMap_pairing n W f g
  have hpR : weightedPair (n+n) R f G ≈
      quaternionHaar n (polyMul (productMap n w K (i::ids) f) g) :=
    Q'.eqv_trans _ _ _ (residual_pair _ U V f G _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hp
        (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (removed_pair_zero n w K i ids hi hnot hids f g hc))
          (Q'.mul_zero_eqv _))))
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : -(0 : Q') ≈ 0))
          (Q'.eqv_of_eq (Q'.add_zero' _))))
  have hlR : weightedPair (n+n) R f f ≈ heatRate w * quaternionHaar n (polyMul f f) :=
    Q'.eqv_trans _ _ _ (residual_pair _ U V f f _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (lower_diagonal n w K (i::ids) hnall hiall hf)
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _
          (lower_diagonal n w K ids hn hids hf)))) (factor_margin _ _))
  have hrR : weightedPair (n+n) R G G ≈ heatRate w * quaternionHaar n (polyMul g g) :=
    Q'.eqv_trans _ _ _ (residual_pair _ U V G G _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (upper_diagonal n w K (i::ids) hnall hiall hg)
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _
          (upper_diagonal n w K ids hn hids hg)))) (factor_margin _ _))
  have hR : Certificate (n+n) R :=
    (heatAt_floorCertificate (by omega) (by omega) hw0 hw1 K hK).mul
      (productHeatCertificate n hw0 hw1 K hK ids hids)
  have hf2 : SupportedQuaternionBlocks (n+n) f :=
    fun t ht => Nat.le_trans (hf t ht) (Nat.mul_le_mul_left 4 (by omega))
  have hcs := weighted_cauchySchwarz (n+n) R f G hR hf2 (lift_supported hg n)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qmul hpR hpR))
    (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (qmul hlR hrR)
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2))) (by decide)
        (fun | 0 => heatRate w | 1 => quaternionHaar n (polyMul f f)
             | _ => quaternionHaar n (polyMul g g))))))

/-- Same-output Cauchy--Schwarz, with the zero-norm case handled constructively. -/
theorem productMap_conditional_square_bound (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (i : Nat) (ids : List Nat) (hn : ids.Nodup) (hi : i < n) (hnot : i ∉ ids)
    (hids : ∀ j, j ∈ ids → j < n) {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f)
    (hc : RatPolyCoeffEqv (project i f) polyZero) :
    quaternionHaar n (polyMul (productMap n w K (i::ids) f) (productMap n w K (i::ids) f)) ≤
      squaredHeatRate w * quaternionHaar n (polyMul f f) := by
  have hiall : ∀ j, j ∈ i::ids → j < n := by
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hi
    · exact hids j hj
  let A := quaternionHaar n (polyMul (productMap n w K (i::ids) f) (productMap n w K (i::ids) f))
  let F := quaternionHaar n (polyMul f f)
  have h := productMap_conditional_pair_bound n hw0 hw1 K hK i ids hn hi hnot hids hf
    (productMap_supported n w K (i::ids) hiall hf) hc
  change A*A ≤ squaredHeatRate w*(F*A) at h
  change A ≤ squaredHeatRate w*F
  by_cases hpos : (0 : Q') < A
  · exact Q'.le_of_mul_le_mul_left
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) (Q'.mul_comm_eqv _ _)))) hpos
  · have hz : A ≤ (0 : Q') := by
      change ¬ ((0 : Int) * (A.den : Int) < A.num * 1) at hpos
      have hn0 : A.num ≤ 0 := by simpa only [Int.zero_mul, Int.mul_one] using Int.not_lt.mp hpos
      change A.num * 1 ≤ (0 : Int) * (A.den : Int)
      simpa only [Int.zero_mul, Int.mul_one] using hn0
    exact Q'.le_trans' _ _ _ hz (Q'.mul_nonneg _ _
      (squaredHeatRate_nonnegative hw0 hw1) (Certificate.haar_nonnegative (.square f hf)))

end YMGap.Continuum.SU2QuaternionProductHeatContraction

#print axioms YMGap.Continuum.SU2QuaternionProductHeatContraction.heatAt_floorCertificate
#print axioms YMGap.Continuum.SU2QuaternionProductHeatContraction.productHeatCertificate
#print axioms YMGap.Continuum.SU2QuaternionProductHeatContraction.removed_pair_zero
#print axioms YMGap.Continuum.SU2QuaternionProductHeatContraction.productMap_conditional_pair_bound
#print axioms YMGap.Continuum.SU2QuaternionProductHeatContraction.productMap_conditional_square_bound
