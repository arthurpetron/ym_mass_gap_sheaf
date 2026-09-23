/-
# Full cube boundary summation at every positive subunit nome

The relative heat-tail ceiling replaces the old small-nome constant two
at each of the twelve active boundary faces. The resulting explicit factor
depends on w, but neither the representation cutoff nor the source labels.
All estimates use the original boundary enumeration, joint kernel and marginal.
No coupling-uniform estimate, original-YM identification or gap is asserted.
-/

import YMGap.Continuum.BF4PhysicalSubunitHeatRelativeTail
import YMGap.Continuum.BF4PhysicalCubeGaussianReturn

namespace YMGap.Continuum.BF4PhysicalCubeSubunitBoundarySumBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalSubunitHeatRelativeTail
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCubeBalancedDescent
open YMGap.Continuum.BF4PhysicalCubeBoundarySumBound
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity
open YMGap.Continuum.BF4PhysicalCubeKernelFactorization
open YMGap.Continuum.BF4PhysicalCubeGaussianReturn
open YMGap.Continuum.BF4PhysicalCutoffKernelSupportPersistence
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeContainment
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusedChannelOne
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.mul_num_cast, Q'.mul_den_cast];
             try ac_rfl))

-- Keep the explicit nome ceiling opaque to these purely algebraic steps.
private theorem diagonal_reorder (c a b : Q') :
    (a * a) * (c * b) ≈ c * ((a * a) * b) := by q_ring

private theorem balanced_reorder (c a b d : Q') :
    b * (c * ((a * a) * d)) ≈ (c * a) * ((a * b) * d) := by q_ring

private theorem product_nonneg (f : Nat → Q') (h : ∀ i, (0 : Q') ≤ f i) :
    ∀ ids, (0 : Q') ≤ eliminateLinks f ids
  | [] => Q'.zero_le_one
  | i :: ids => Q'.mul_nonneg _ _ (h i) (product_nonneg f h ids)

private theorem product_le (f g : Nat → Q') (h0 : ∀ i, (0 : Q') ≤ f i)
    (h : ∀ i, f i ≤ g i) : ∀ ids, eliminateLinks f ids ≤ eliminateLinks g ids
  | [] => Q'.le_refl' 1
  | i :: ids => Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (h i) (product_nonneg f h0 ids))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (product_le f g h0 h ids)
        (Q'.le_trans' _ _ _ (h0 i) (h i)))

private theorem product_mul (f g : Nat → Q') : ∀ ids,
    eliminateLinks (fun i => f i * g i) ids ≈ eliminateLinks f ids * eliminateLinks g ids
  | [] => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | i :: ids => by
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (product_mul f g ids)) ?_
      simp only [eliminateLinks]
      q_ring

private theorem sum_le {A : Type} (f g : A → Q') : ∀ xs,
    (∀ x, x ∈ xs → f x ≤ g x) → listQSum f xs ≤ listQSum g xs
  | [], _ => Q'.le_refl' 0
  | x :: xs, h => Q'.add_le_add (h x List.mem_cons_self)
      (sum_le f g xs (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem masked_product (c : Q') (test : Nat → Bool) : ∀ ids,
    eliminateLinks (fun i => if test i then c else 1) ids ≈
      qpow c (ids.filter test).length
  | [] => Q'.eqv_refl 1
  | i :: ids => by
      cases hi : test i with
      | false =>
          simp only [eliminateLinks, hi, Bool.false_eq_true, ↓reduceIte,
            List.filter_cons]
          exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
            (masked_product c test ids)
      | true =>
          simp only [eliminateLinks, hi, ↓reduceIte, List.filter_cons,
            List.length_cons, qpow]
          exact Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left c _ _ (masked_product c test ids))
            (Q'.mul_comm_eqv _ _)

/-- The complete twelve-face loss, computed from the literal heat nome. -/
def subunitBoundaryFactor (w : Q') : Q' := qpow (relativeHeatTailCeiling w) 12

theorem subunitBoundaryFactor_nonnegative {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') ≤ subunitBoundaryFactor w :=
  qpow_nonneg _ (Q'.le_of_lt (relativeHeatTailCeiling_pos hw0)) 12

/-- The original one-coordinate boundary tail with its all-subunit ceiling. -/
theorem boundaryTailFactor_sum_le_subunit {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (state : EdgeLabelling) (face : Nat) :
    fsum (boundaryTailFactor w state face) (K + 1) ≤
      (if face ∈ cubeDifferenceBoundaryIds then relativeHeatTailCeiling w else 1) *
        coeffW w (cubeDifferenceBoundary state face) := by
  by_cases hf : face ∈ cubeDifferenceBoundaryIds
  · unfold boundaryTailFactor
    simp only [if_pos hf]
    exact coeffW_tail_le_relativeCeiling hw0 hw1 _ _
  · unfold boundaryTailFactor
    simp only [if_neg hf, cubeDifferenceBoundary_zero_off state hf, coeffW_zero]
    have hc := fsum_collapse (g := fun s => if s = 0 then (1 : Q') else 0)
      (fun s hs => by simp only [if_neg hs]; exact Q'.eqv_refl 0)
      (K + 1) (Nat.zero_lt_succ K)
    exact Q'.le_of_eqv (Q'.eqv_trans _ 1 _ hc (Q'.eqv_symm (Q'.one_mul_eqv 1)))

/-- Full original boundary sum: all sources, targets and cutoffs; only the
explicit nome-dependent factor changes from the restricted estimate. -/
theorem cubeBoundaryOverlap_le_subunit_difference {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (left right : EdgeLabelling) :
    cubeBoundaryOverlap w K left right ≤
      subunitBoundaryFactor w * boundaryHeat w (cubeDifferenceBoundary left) := by
  have hsum := sum_le _ _ (centralBoundaryChannels K 0)
    (fun boundary hb => boundary_integrand_le_product (Q'.le_of_lt hw0) K left right boundary hb)
  have hF := bounded_product_sum (boundaryTailFactor w left) K (centralFixedFaceIds 0) (by decide +kernel)
  have hprod := product_le (fun face => fsum (boundaryTailFactor w left face) (K + 1))
    (fun face => (if face ∈ cubeDifferenceBoundaryIds then relativeHeatTailCeiling w else 1) *
      coeffW w (cubeDifferenceBoundary left face))
    (fun face => fsum_nonneg (fun spin => boundaryTailFactor_nonneg (Q'.le_of_lt hw0) left face spin) _)
    (boundaryTailFactor_sum_le_subunit hw0 hw1 K left) (centralFixedFaceIds 0)
  have hsplit := product_mul
    (fun face => if face ∈ cubeDifferenceBoundaryIds then relativeHeatTailCeiling w else 1)
    (fun face => coeffW w (cubeDifferenceBoundary left face)) (centralFixedFaceIds 0)
  have hcount : eliminateLinks
      (fun face => if face ∈ cubeDifferenceBoundaryIds then relativeHeatTailCeiling w else 1)
      (centralFixedFaceIds 0) ≈ subunitBoundaryFactor w := by
    have h := masked_product (relativeHeatTailCeiling w)
      (fun face => decide (face ∈ cubeDifferenceBoundaryIds)) (centralFixedFaceIds 0)
    have hc : ((centralFixedFaceIds 0).filter
      (fun face => decide (face ∈ cubeDifferenceBoundaryIds))).length = 12 := by decide +kernel
    simpa only [decide_eq_true_eq, hc, subunitBoundaryFactor] using h
  exact Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ (Q'.le_of_eqv hF)
    (Q'.le_trans' _ _ _ hprod (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hsplit
      (Q'.mul_eqv_congr_right _ _ _ hcount)))))

/-- The actual full raw diagonal, with no discarded boundary factors. -/
theorem cubePhysicalKernel_diagonal_le_subunit {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0) :
    centralPhysicalReflectedKernel w K 0 state state ≤
      subunitBoundaryFactor w * ((halfHeat w state * halfHeat w state) *
        boundaryHeat w (cubeDifferenceBoundary state)) := by
  have hn : (0 : Q') ≤ halfHeat w state :=
    product_nonneg _ (fun _ => coeffW_nonneg (Q'.le_of_lt hw0) _) _
  have hf := cubePhysicalKernel_eq_heat_overlap w K state state
    (cubeSupported_bounded K state hb hz) (cubeSupported_bounded K state hb hz) hz hz
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hf) (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (cubeBoundaryOverlap_le_subunit_difference hw0 hw1 K state state)
      (Q'.mul_nonneg _ _ hn hn)) (Q'.le_of_eqv (diagonal_reorder _ _ _)))

/-- Balanced descent pays the full diagonal using an actual off-diagonal
entry of the same kernel, now at every positive subunit nome. -/
theorem cube_diagonal_balanced_comparison_subunit {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : 2 ≤ K) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hp : CubeSupportedCommonParity state) :
    halfHeat w (balancedState state) * centralPhysicalReflectedKernel w K 0 state state ≤
      (subunitBoundaryFactor w * halfHeat w state) *
        centralPhysicalReflectedKernel w K 0 state (balancedState state) := by
  have hn : (0 : Q') ≤ halfHeat w (balancedState state) :=
    product_nonneg _ (fun _ => coeffW_nonneg (Q'.le_of_lt hw0) _) _
  have hd := Q'.mul_le_mul_of_nonneg_left _ _ _
    (cubePhysicalKernel_diagonal_le_subunit hw0 hw1 K state hb hp.1) hn
  refine Q'.le_trans' _ _ _ hd (Q'.le_trans' _
    ((subunitBoundaryFactor w * halfHeat w state) * balancedPhysicalWeight w state) _ ?_ ?_)
  · exact Q'.le_of_eqv (balanced_reorder _ _ _ _)
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (balancedPhysicalWeight_le_kernel (Q'.le_of_lt hw0) K hK state hb hp)
      (Q'.mul_nonneg _ _ (subunitBoundaryFactor_nonnegative hw0)
        (product_nonneg _ (fun _ => coeffW_nonneg (Q'.le_of_lt hw0) _) _))

private theorem member_le_sum {A : Type} (value : A → Q') (hn : ∀ x, (0 : Q') ≤ value x) :
    ∀ (xs : List A) {x : A}, x ∈ xs → value x ≤ listQSum value xs
  | [], _, h => by cases h
  | y :: ys, x, h => by
      rcases List.mem_cons.mp h with he | ht
      · subst x
        exact Q'.add_le_self_of_nonneg _ _ (listQSum_nonnegative_on _ _ (fun z _ => hn z))
      · have hh := Q'.add_le_add_right (0 : Q') (value y) (listQSum value ys) (hn y)
        rw [Q'.zero_add'] at hh
        exact Q'.le_trans' _ _ _ (member_le_sum value hn ys ht) hh

/-- Same positive-carrier row, with the entire boundary loss explicit. -/
theorem cube_diagonal_rawRow_comparison_subunit {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : 2 ≤ K) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hp : CubeSupportedCommonParity state) :
    halfHeat w (balancedState state) * centralPhysicalReflectedKernel w K 0 state state ≤
      (subunitBoundaryFactor w * halfHeat w state) *
        centralPhysicalPositiveRawRowMass w (Q'.le_of_lt hw0) K 0 state := by
  have hm := cubeSupported_mem_positiveHalfStates hw0 K (by omega) (balancedState state)
    (fun face _ => balancedState_bounded state K hK hb face) (balancedState_off state)
  have hr := member_le_sum (centralPhysicalReflectedKernel w K 0 state)
    (fun target => centralPhysicalReflectedKernel_nonnegative (Q'.le_of_lt hw0) K 0 state target)
    (centralPositiveHalfStates w (Q'.le_of_lt hw0) K 0) hm
  exact Q'.le_trans' _ _ _ (cube_diagonal_balanced_comparison_subunit hw0 hw1 K hK state hb hp)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hr
      (Q'.mul_nonneg _ _ (subunitBoundaryFactor_nonnegative hw0)
        (product_nonneg _ (fun _ => coeffW_nonneg (Q'.le_of_lt hw0) _) _)))

/-- The common partition cancels on the literal conditional operator. -/
theorem cube_selfReturn_scaled_le_subunit {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : 2 ≤ K) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hp : CubeSupportedCommonParity state) :
    halfHeat w (balancedState state) *
      centralPhysicalConditionalKernel w (Q'.le_of_lt hw0) K 0 state state ≤
      subunitBoundaryFactor w * halfHeat w state := by
  have hs := cubeSupported_mem_positiveHalfStates hw0 K (by omega) state hb hp.1
  rw [centralPhysicalConditionalKernel_eq_divPos (mem_centralPositiveHalfStates_iff.mp hs).2]
  have he := centralNormalizedPhysicalReturn_eqv_rawRatio hs state
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ he)) ?_
  refine Q'.le_trans' _
    (Q'.divPos (halfHeat w (balancedState state) * centralPhysicalReflectedKernel w K 0 state state)
      (centralPhysicalPositiveRawRowMass w (Q'.le_of_lt hw0) K 0 state)
      (centralPhysicalPositiveRawRowMass_pos hs)) _ ?_ ?_
  · exact Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
  · exact Q'.divPos_le_of_le_mul _ _ _
      (cube_diagonal_rawRow_comparison_subunit hw0 hw1 K hK state hb hp)

/-- Explicit all-subunit Gaussian envelope; the prefactor is allowed to
deteriorate as w approaches one. -/
def subunitReturnEnvelope (w : Q') (M : Nat) : Q' :=
  (subunitBoundaryFactor w * Q'.ofNat ((M + 1) ^ 6)) * qpow w (gaussianExponent M)

/-- Actual high-label conditional self-return for every 0<w<1. A
coupling-dependent summable radial tail is still needed for a full gap. -/
theorem cube_selfReturn_le_subunit_gaussian {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : 2 ≤ K) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hp : CubeSupportedCommonParity state) (hM : 1400 ≤ radius state) :
    centralPhysicalConditionalKernel w (Q'.le_of_lt hw0) K 0 state state ≤
      subunitReturnEnvelope w (radius state) := by
  have hh := balanced_heat_ratio (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) state hp.1 hM
  have hs := cube_selfReturn_scaled_le_subunit hw0 hw1 K hK state hb hp
  have ht : (0 : Q') < halfHeat w (balancedState state) := by
    have he := halfHeat_eq_dimension_casimir w (balancedState state) (balancedState_off state)
    have hd : (0 : Q') < Q'.ofNat (cubeDimension (balancedState state)) :=
      Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
        (CReal.ofNat_le_ofNat (dimensionProduct_positive _))
    exact Q'.pos_of_lt_of_le (Q'.mul_pos hd
      (YMGap.Continuum.BondMovingScaledNorm.qpow_pos hw0 _)) (Q'.ge_of_eqv he)
  apply Q'.le_of_mul_le_mul_left (c := halfHeat w (balancedState state)) (hc := ht)
  refine Q'.le_trans' _ _ _ hs (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hh (subunitBoundaryFactor_nonnegative hw0)) ?_)
  apply Q'.le_of_eqv
  unfold subunitReturnEnvelope
  q_ring

/-- Sector membership supplies support, parity and boundedness. This is the
all-subunit input for the existing high-label trace route, on its original
conditional kernel rather than a surrogate coefficient sequence. -/
theorem vacuumSector_selfReturn_le_subunit_gaussian {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) {state : EdgeLabelling}
    (hs : state ∈ BF4PhysicalFiniteVacuumSector.centralPhysicalFiniteVacuumSectorStates
      w (Q'.le_of_lt hw0) K 0)
    (hM : 1400 ≤ radius state) :
    centralPhysicalConditionalKernel w (Q'.le_of_lt hw0) K 0 state state ≤
      subunitReturnEnvelope w (radius state) := by
  have hb := vacuumSector_cubeBounded w (Q'.le_of_lt hw0) K hs
  have hp := vacuumSector_cubeSupportedCommonParity w (Q'.le_of_lt hw0) K hs
  have hK : 2 ≤ K := Nat.le_trans (by omega : 2 ≤ radius state) (radius_le state K hb)
  exact cube_selfReturn_le_subunit_gaussian hw0 hw1 K hK state hb hp hM

end YMGap.Continuum.BF4PhysicalCubeSubunitBoundarySumBound

#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitBoundarySumBound.subunitBoundaryFactor
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitBoundarySumBound.subunitBoundaryFactor_nonnegative
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitBoundarySumBound.boundaryTailFactor_sum_le_subunit
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitBoundarySumBound.cubeBoundaryOverlap_le_subunit_difference
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitBoundarySumBound.cubePhysicalKernel_diagonal_le_subunit
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitBoundarySumBound.cube_diagonal_balanced_comparison_subunit
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitBoundarySumBound.cube_diagonal_rawRow_comparison_subunit
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitBoundarySumBound.cube_selfReturn_scaled_le_subunit
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitBoundarySumBound.subunitReturnEnvelope
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitBoundarySumBound.cube_selfReturn_le_subunit_gaussian
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitBoundarySumBound.vacuumSector_selfReturn_le_subunit_gaussian
