/-
# One-sided family flow and cost on the original odd marginal

Lift every signed test to the upper endpoint, retaining the same active
heat factors, fringe unit factors, and complete endpoint weight V*T^n1.
The family flow, signed cost, and full-product square are exactly their
original one-slice marginals. No conditional-centering premise is needed
and no factor two from a jump is present.

The factor-floor certificates are reused from the original family by a
constructive finite selection. These pins supply the next positive joint
cost calculation; they do not bound its signed remainder or assert a gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
import YMGap.Continuum.QuaternionHaarFamilySquare

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialOneSidedFamily

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks kineticWeight_eq_indexedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDualDirichlet (erasedPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual (crossPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalPair marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (family endpointWeight familyFloorCertificates)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals
  (marginalFlow marginalDiagonal marginalCross marginalCost)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_product lift_supported)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (step)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
  (productHeat productMap productMap_pairing)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump)
open YMGap.Continuum.SU2QuaternionWeightedProductTwoLinkDual (marginalPair_perm)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarFiniteFamilyDual
open YMGap.Continuum.QuaternionHaarFamilyErasure
open YMGap.Continuum.QuaternionHaarFamilySquare
  (qListSum_congr haar_weighted_add haar_weighted_sum_indexed)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] spatialWeight baseLinks kineticWeight activeBlocks

/-- Exactly the original coordinate factors, with one-sided upper tests. -/
def oneSidedFamily (w : Q') (K width : Nat) (tests : Nat → RatPoly) :
    List (RatPoly × RatPoly) :=
  (labels width).map (fun i => (coordinateFactor w K width i, liftBoundary (N width) (tests i)))

theorem oneSidedFamily_product_pin (w : Q') (K width : Nat) (tests : Nat → RatPoly) :
    RatPolyCoeffEqv (product (oneSidedFamily w K width tests)) (kineticWeight w K width) := by
  unfold oneSidedFamily
  rw [product_indexed]
  have h := product_pin w K width (labels width)
  rw [remainingHeat_labels] at h
  rw [kineticWeight_eq_indexedProduct]
  exact h

private theorem upper_pair (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (a f r : RatPoly) :
    quaternionHaar (n+n)
      (polyMul (polyMul a (liftBoundary n a))
        (polyMul (productHeat n w K ids) (polyMul (liftBoundary n f) (liftBoundary n r)))) ≈
      SU2QuaternionWeightedProductDualEnergy.marginalPair n w K ids a f r := by
  have hp : RatPolyCoeffEqv
      (polyMul (polyMul a (liftBoundary n a))
        (polyMul (productHeat n w K ids) (polyMul (liftBoundary n f) (liftBoundary n r))))
      (polyMul (productHeat n w K ids) (polyMul a (liftBoundary n (polyMul a (polyMul f r))))) := by
    simp only [lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.mul (.var 3) (.var 4))))
      (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))
      (by decide) (fun
        | 0 => productHeat n w K ids | 1 => a
        | 2 => liftBoundary n a | 3 => liftBoundary n f | _ => liftBoundary n r)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hp)
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (productMap_pairing n w K ids a (polyMul a (polyMul f r))))
      (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.mul (.var 2) (.var 3))) (.var 1))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (by decide) (fun | 0 => a | 1 => productMap n w K ids a | 2 => f | _ => r))))

private theorem upper_term (w : Q') (K width n : Nat) (rest : List Nat) (f r : RatPoly) :
    quaternionHaar (N width+N width)
      (polyMul (endpointWeight w K width n)
        (polyMul (polynomialProduct (coordinateFactor w K width) rest)
          (polyMul (liftBoundary (N width) f) (liftBoundary (N width) r)))) ≈
      SU2QuaternionWeightedProductDualEnergy.marginalPair (N width) w K
        (remainingHeat width rest)
        (polyMul (spatialWeight w K width) (terminalMessage w K width n)) f r :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff (((product_pin w K width rest).mul_right _).mul_left _))
    (upper_pair (N width) w K (remainingHeat width rest) _ f r)

private theorem single_term (w : Q') (K width n i : Nat) (rest : List Nat)
    (hm : (i,rest) ∈ singleCuts (labels width)) (f r : RatPoly) :
    quaternionHaar (N width+N width)
      (polyMul (endpointWeight w K width n)
        (polyMul (polynomialProduct (coordinateFactor w K width) rest)
          (polyMul (liftBoundary (N width) f) (liftBoundary (N width) r)))) ≈
      erasedPair w K width n i f r :=
  Q'.eqv_trans _ _ _ (upper_term w K width n rest f r)
    (marginalPair_perm (N width) w K (single_remaining_perm hm) _ f r)

private theorem pair_term (w : Q') (K width n i j : Nat) (rest : List Nat)
    (hm : (i,j,rest) ∈ pairCuts (labels width)) (f r : RatPoly) :
    quaternionHaar (N width+N width)
      (polyMul (endpointWeight w K width n)
        (polyMul (polynomialProduct (coordinateFactor w K width) rest)
          (polyMul (liftBoundary (N width) f) (liftBoundary (N width) r)))) ≈
      crossPair w K width n i j f r :=
  Q'.eqv_trans _ _ _ (upper_term w K width n rest f r)
    (marginalPair_perm (N width) w K (pair_remaining_perm hm) _ f r)

set_option maxHeartbeats 800000 in
/-- Exact one-erasure marginal flow, without a centering hypothesis or the
factor two belonging to two-ended jumps. -/
theorem oneSidedFamily_flow_pin (w : Q') (K width n : Nat) (tests : Nat → RatPoly) (f : RatPoly) :
    quaternionHaar (N width+N width)
      (polyMul (endpointWeight w K width n)
        (polyMul (flow (oneSidedFamily w K width tests)) (liftBoundary (N width) f))) ≈
      marginalFlow w K width n tests f := by
  let mu := endpointWeight w K width n
  let z := liftBoundary (N width) f
  let factors := coordinateFactor w K width
  let xs := fun i => liftBoundary (N width) (tests i)
  have hp := flow_expansion factors xs (labels width)
  have he : quaternionHaar (N width+N width)
      (polyMul mu (polyMul (flow (oneSidedFamily w K width tests)) z)) ≈
      quaternionHaar (N width+N width) (polyMul (polyMul mu z) (singleSum factors xs (labels width))) :=
    haar_of_coeff ((hp.mul_right z).mul_left mu |>.trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
        (fun | 0 => mu | 1 => singleSum factors xs (labels width) | _ => z)))
  exact Q'.eqv_trans _ _ _ he
    (Q'.eqv_trans _ _ _
      (haar_weighted_sum_indexed (N width+N width) (polyMul mu z)
        (fun c : Nat × List Nat => polyMul (polynomialProduct factors c.2) (xs c.1))
        (singleCuts (labels width)))
      (qListSum_congr (singleCuts (labels width)) _ _ (fun c hc =>
        Q'.eqv_trans _ _ _
          (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
            (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
            (.mul (.var 0) (.mul (.var 2) (.mul (.var 1) (.var 3))))
            (by decide) (fun
              | 0 => mu | 1 => z
              | 2 => polynomialProduct factors c.2 | _ => xs c.1)))
          (single_term w K width n c.1 c.2 hc f (tests c.1)))))

private theorem diagonal_pin (w : Q') (K width n : Nat) (tests : Nat → RatPoly) :
    quaternionHaar (N width+N width) (polyMul (endpointWeight w K width n)
      (singleSum (coordinateFactor w K width)
        (fun i => polyMul (liftBoundary (N width) (tests i)) (liftBoundary (N width) (tests i)))
        (labels width))) ≈ marginalDiagonal w K width n tests :=
  Q'.eqv_trans _ _ _
    (haar_weighted_sum_indexed (N width+N width) (endpointWeight w K width n) _ _)
    (qListSum_congr (singleCuts (labels width)) _ _ (fun c hc =>
      single_term w K width n c.1 c.2 hc (tests c.1) (tests c.1)))

private theorem cross_pin (w : Q') (K width n : Nat) (tests : Nat → RatPoly) :
    quaternionHaar (N width+N width) (polyMul (endpointWeight w K width n)
      (pairSum (coordinateFactor w K width) (fun i => liftBoundary (N width) (tests i))
        (labels width))) ≈ marginalCross w K width n tests :=
  Q'.eqv_trans _ _ _
    (haar_weighted_sum_indexed (N width+N width) (endpointWeight w K width n) _ _)
    (qListSum_congr (pairCuts (labels width)) _ _ (fun c hc =>
      pair_term w K width n c.1 c.2.1 c.2.2 hc (tests c.1) (tests c.2.1)))

private theorem haar_cap (blocks : Nat) (mu p : RatPoly) (c : Q') :
    quaternionHaar blocks (polyMul mu (polyMul (cap c) p)) ≈
      c*quaternionHaar blocks (polyMul mu p) :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => mu | 1 => cap c | _ => p)).trans (cap_mul_left c _)))
    (quaternionHaar_polySmul _ _ _)

/-- Exact signed marginal cost; every positional pair remains signed and
occurs once. The coefficient 2h is intrinsic to the cost, not a jump factor. -/
theorem oneSidedFamily_cost_pin (w : Q') (K width n : Nat) (tests : Nat → RatPoly) :
    quaternionHaar (N width+N width)
      (polyMul (endpointWeight w K width n) (cost (headFloor w) (oneSidedFamily w K width tests))) ≈
      marginalCost w K width n tests := by
  let mu := endpointWeight w K width n
  let d := singleSum (coordinateFactor w K width)
    (fun i => polyMul (liftBoundary (N width) (tests i)) (liftBoundary (N width) (tests i))) (labels width)
  let c := pairSum (coordinateFactor w K width) (fun i => liftBoundary (N width) (tests i)) (labels width)
  have hp := cost_expansion (headFloor w) (coordinateFactor w K width)
    (fun i => liftBoundary (N width) (tests i)) (labels width)
  have hc := cross_pin w K width n tests
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (hp.mul_left mu))
    (Q'.eqv_trans _ _ _ (haar_weighted_add (N width+N width) mu d _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (diagonal_pin w K width n tests)
          (Q'.eqv_trans _ _ _ (haar_cap (N width+N width) mu (polyAdd c c) (headFloor w))
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.eqv_trans _ _ _ (haar_weighted_add (N width+N width) mu c c)
                (Q'.add_eqv_congr' hc hc)))))
        (poly_identity_of_normal_eq
          (.add (.var 0) (.mul (.var 1) (.add (.var 2) (.var 2))))
          (.add (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 2)))
          (by decide) (fun
            | 0 => marginalDiagonal w K width n tests
            | 1 => headFloor w | _ => marginalCross w K width n tests))))

private theorem terminal_product (w : Q') (K width n : Nat) :
    productMap (N width) w K (activeBlocks width)
      (polyMul (spatialWeight w K width) (terminalMessage w K width n)) =
      terminalMessage w K width (n+1) := by
  rw [← terminalMessage_next]
  unfold transferStep step productMap kernelMap
  rw [kineticWeight_eq_indexedProduct]
  rfl

/-- The full-family square is the SAME original odd-marginal norm, with
both original terminal factors and no division by a partition. -/
theorem oneSidedFamily_square_pin (w : Q') (K width n : Nat) (tests : Nat → RatPoly) (f : RatPoly) :
    quaternionHaar (N width+N width)
      (polyMul (endpointWeight w K width n)
        (polyMul (product (oneSidedFamily w K width tests))
          (polyMul (liftBoundary (N width) f) (liftBoundary (N width) f)))) ≈
      marginalPair w K width n f f := by
  unfold oneSidedFamily
  rw [product_indexed]
  have h := upper_term w K width n (labels width) f f
  rw [remainingHeat_labels] at h
  unfold SU2QuaternionWeightedProductDualEnergy.marginalPair at h
  rw [terminal_product] at h
  exact h

private def mappedFloors {blocks : Nat} {h : Q'} (f : Nat → RatPoly × RatPoly) :
    (ids : List Nat) →
    (∀ i, i ∈ ids → Certificate blocks (polyAdd (f i).1 (polyNeg (cap h)))) →
    ∀ p, p ∈ ids.map f → Certificate blocks (polyAdd p.1 (polyNeg (cap h)))
  | [], _, _, hp => False.elim (List.not_mem_nil hp)
  | i::ids, C, p, hp =>
      if he : p = f i then he ▸ C i List.mem_cons_self
      else mappedFloors f ids (fun j hj => C j (List.mem_cons_of_mem i hj)) p
        ((List.mem_cons.mp hp).resolve_left he)

/-- Reuse the actual heat/unit floor certificates. The finite selection
returns certificate data without eliminating a membership existential. -/
def oneSidedFamily_floorCertificates {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (tests : Nat → RatPoly) :
    ∀ p, p ∈ oneSidedFamily w K width tests →
      Certificate (N width+N width) (polyAdd p.1 (polyNeg (cap (headFloor w)))) := by
  apply mappedFloors _ (labels width)
  intro i hi
  apply familyFloorCertificates hw0 hw1 K width hK tests
    (coordinateFactor w K width i, jump (N width) (tests i))
  rw [family_eq_indexed]
  exact List.mem_map.mpr ⟨i,hi,rfl⟩

theorem oneSidedFamily_tests_supported (w : Q') (K width : Nat) (tests : Nat → RatPoly)
    (ht : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (tests i)) :
    ∀ p, p ∈ oneSidedFamily w K width tests → SupportedQuaternionBlocks (N width+N width) p.2 := by
  intro p hp
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  exact lift_supported (ht i (labels_lt width i hi)) (N width)

#print axioms oneSidedFamily
#print axioms oneSidedFamily_product_pin
#print axioms oneSidedFamily_flow_pin
#print axioms oneSidedFamily_cost_pin
#print axioms oneSidedFamily_square_pin
#print axioms oneSidedFamily_floorCertificates
#print axioms oneSidedFamily_tests_supported

end YMGap.Continuum.BF4ExactSlabFixedSpatialOneSidedFamily
