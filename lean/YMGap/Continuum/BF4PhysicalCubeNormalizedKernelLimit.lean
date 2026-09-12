/-
# The all-spin raw cube kernel and the actual normalized cutoff limit

Every normalized cube entry has the SAME scalar normalization in the cutoff
limit. The scalar is constructed from the actual vacuum-pair cylinder limit
divided by its positive stable raw entry. Its rational approximations equal
the reciprocal of the original finite partition, at every cutoff.

Thus the all-spin raw kernel and the cutoff-removed physical pair-cylinder
kernel are exactly proportional, not merely entrywise close. All moduli are
retained as Type-level InnerRegularity data. At w=1/400 the scalar has the
cutoff-uniform lower bound 64/65, inherited from the actual partition ceiling.

This identifies kernel normalization, not row-conditional time evolution.
It does not identify the marginal completion with the raw cube completion,
construct geometric time, isolate a vacuum, or prove a strict gap.
-/

import YMGap.Continuum.BF4PhysicalCubeGNSData
import YMGap.Continuum.BF4PhysicalCutoffProbFunctional
import YMGap.Continuum.BF4PhysicalAnchorPartitionCeiling
import YMGap.Constructive.CRealInnerRegularity

namespace YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeKernelSaturation
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalCutoffProbFunctional
open YMGap.Continuum.BF4PhysicalAnchorPartitionCeiling
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.RationalKernelSpan
open YMGap.Continuum.FiniteDeterministicKernelPushforward

local infix:50 " ≈ " => Q'.eqv

/-- The original pair-cylinder expectation, with the spin cutoff removed. -/
def normalizedKernelLimit {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (left right : CubeSectorState) : CReal :=
  slabNomeCutoffObservableLimit hw0 hw1 1
    (centralPairCylinderObservable 0 left.val right.val)

def normalizedKernelRegularity {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (left right : CubeSectorState) : CReal.InnerRegularity (normalizedKernelLimit hw0 hw1 left right) where
  rate := slabNomeBoundedObservableModulus w 1
  regular := fun _ hepsilon _ _ hp hq =>
    slabNomeCutoffBoundedObservableExpectation_twoSided_of_modulus hw0 hw1 1
      (centralPairCylinderObservable 0 left.val right.val) hepsilon hp hq

private theorem root_kernel_pos {w : Q'} (hw : (0 : Q') ≤ w) :
    (0 : Q') < kernel w rootState rootState :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (one_le_centralPhysicalReflectedKernel_vacuum hw _ 0)

/-- One scalar shared by EVERY pair, constructed without a limiting inverse. -/
def inversePartitionLimit {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : CReal :=
  CReal.mul (CReal.ofQ' (Q'.recipPos (kernel w rootState rootState) (root_kernel_pos (Q'.le_of_lt hw0))))
    (normalizedKernelLimit hw0 hw1 rootState rootState)

def inversePartitionRegularity {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    CReal.InnerRegularity (inversePartitionLimit hw0 hw1) :=
  (normalizedKernelRegularity hw0 hw1 rootState rootState).scaleLeft
    (Q'.recipPos (kernel w rootState rootState) (root_kernel_pos (Q'.le_of_lt hw0)))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

private theorem cancel_root (c Z : Q') (hc : (0 : Q') < c) (hZ : (0 : Q') < Z) :
    Q'.recipPos c hc * Q'.divPos c Z hZ ≈ Q'.recipPos Z hZ := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv c hc))) ?_
  exact Q'.one_mul_eqv _

/-- Every approximation is the reciprocal of the SAME original partition. -/
theorem inversePartitionLimit_approx {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) :
    (inversePartitionLimit hw0 hw1).approx K ≈
      Q'.recipPos (slabParametricKPhysicalPartition w K 1)
        (slabParametricKPhysicalPartition_pos (Q'.le_of_lt hw0) K 1) := by
  have hv := centralNormalizedPhysicalReflectedKernel_eq_expectation
    (hw := Q'.le_of_lt hw0) (zeroEdgeLabelling_mem_centralHalfStates K 0)
    (zeroEdgeLabelling_mem_centralHalfStates K 0)
  have hs := cubeStableRawKernel_eventual w zeroEdgeLabelling zeroEdgeLabelling
    (fun _ _ => rfl) (fun _ _ => rfl) K (show 0 ≤ K from Nat.zero_le K)
  change Q'.recipPos (kernel w rootState rootState) (root_kernel_pos (Q'.le_of_lt hw0)) * _ ≈ _
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hv)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hs)) ?_
  exact cancel_root _ _ _ _

private theorem state_mem_at_saturation (left right : CubeSectorState) (K : Nat)
    (hK : cubeKernelSaturationCutoff left.val right.val ≤ K) :
    left.val ∈ centralHalfStates K 0 := by
  apply cubeSupported_mem_halfStates K left.val _ left.property.1
  apply cubeSupported_bounded _ left.val _ left.property.1
  intro face hf
  have hb := cubeSpinSum_bounds left.val face hf
  unfold cubeKernelSaturationCutoff at hK
  omega

/-- Exact equality after the computed pair admission/saturation cutoff. -/
theorem normalizedKernelLimit_approx_scaled {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (left right : CubeSectorState) (K : Nat)
    (hK : cubeKernelSaturationCutoff left.val right.val ≤ K) :
    (normalizedKernelLimit hw0 hw1 left right).approx K ≈
      (inversePartitionLimit hw0 hw1).approx K * kernel w left right := by
  have hswap : cubeKernelSaturationCutoff right.val left.val ≤ K := by
    simpa only [cubeKernelSaturationCutoff, Nat.add_comm] using hK
  have he := centralNormalizedPhysicalReflectedKernel_eq_expectation
    (hw := Q'.le_of_lt hw0) (state_mem_at_saturation left right K hK)
    (state_mem_at_saturation right left K hswap)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm he) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
    (cubeStableRawKernel_eventual w left.val right.val left.property.1 right.property.1 K hK)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (inversePartitionLimit_approx hw0 hw1 K))

/-- One common normalization relates the full all-spin physical kernels. -/
theorem normalizedKernelLimit_eq_scaled {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (left right : CubeSectorState) :
    CReal.Equiv (normalizedKernelLimit hw0 hw1 left right)
      (CReal.mul (inversePartitionLimit hw0 hw1) (CReal.ofQ' (kernel w left right))) := by
  intro epsilon hepsilon
  refine ⟨cubeKernelSaturationCutoff left.val right.val, fun K hK => ?_⟩
  have he := normalizedKernelLimit_approx_scaled hw0 hw1 left right K hK
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hepsilon)),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hepsilon))⟩

/-- A positive normalization floor at the SAME fixed anchor, not uniform in w. -/
theorem inversePartitionLimit_anchor_floor (K : Nat) :
    Q'.mkPos 64 65 (by decide) ≤
      (inversePartitionLimit (w := anchorCoupling) (by decide) (by decide)).approx K := by
  have hZ := slabParametricKPhysicalPartition_pos (w := anchorCoupling) (by decide) K 1
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.mkPos 64 65 (by decide))
    (anchorSlabPartition_one_le_ceiling K) (by decide)
  have hfloor := Q'.le_divPos_of_mul_le 1 _ hZ
    (Q'.le_trans' _ _ _ hscaled (by decide :
      Q'.mkPos 64 65 (by decide) * Q'.mkPos 65 64 (by decide) ≤ (1 : Q')))
  exact Q'.le_trans' _ _ _ hfloor (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (Q'.eqv_symm
      (inversePartitionLimit_approx (w := anchorCoupling) (by decide) (by decide) K))))

theorem inversePartitionLimit_upper {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) :
    (inversePartitionLimit hw0 hw1).approx K ≤ (1 : Q') := by
  have hp := slabParametricKPhysicalPartition_pos (Q'.le_of_lt hw0) K 1
  have hZ := slabParametricKPhysicalPartition_one_le (Q'.le_of_lt hw0) K 1
  have hb := Q'.divPos_le_of_le_mul 1 _ hp
    (Q'.le_trans' _ _ _ hZ (Q'.ge_of_eqv (Q'.one_mul_eqv _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (inversePartitionLimit_approx hw0 hw1 K)
      (Q'.eqv_symm (Q'.one_mul_eqv _)))) hb

private theorem mul_exchange (a b c : Q') : a * (b * c) ≈ b * (a * c) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

private theorem form_kernel_scale {State : Type} (k : State → State → Q')
    (c : Q') (left right : Span State) :
    form (fun l r => c * k l r) left right ≈ c * form k left right := by
  unfold form sectionPairing
  refine Q'.eqv_trans _ _ _ (listQSum_congr (fun r => ?_) right) (listQSum_mul_left c _ right)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ ?_) (mul_exchange r.2 c _)
  exact Q'.eqv_trans _ _ _ (listQSum_congr (fun l => mul_exchange l.2 c _) left)
    (listQSum_mul_left c _ left)

private theorem form_kernel_congr_on {State : Type} (k j : State → State → Q')
    (left right : Span State)
    (h : ∀ l, l ∈ left → ∀ r, r ∈ right → k l.1 r.1 ≈ j l.1 r.1) :
    form k left right ≈ form j left right := by
  unfold form sectionPairing
  apply listQSum_congr_on
  intro r hr
  apply Q'.mul_eqv_congr_left
  apply listQSum_congr_on
  intro l hl
  exact Q'.mul_eqv_congr_left _ _ _ (h l hl r hr)

/-- Original normalized OS form on finite signed lists, retaining repetitions. -/
def finiteNormalizedForm (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) (left right : CubeSpan) : Q' :=
  form (fun l r : CubeSectorState =>
    centralNormalizedPhysicalReflectedKernel w hw K 0 l.val r.val) left right

/-- The same raw signed form with its constructed physical normalization. -/
def normalizedFormLimit {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (left right : CubeSpan) : CReal :=
  CReal.mul (CReal.ofQ' (form (kernel w) left right)) (inversePartitionLimit hw0 hw1)

def normalizedFormRegularity {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (left right : CubeSpan) : CReal.InnerRegularity (normalizedFormLimit hw0 hw1 left right) :=
  (inversePartitionRegularity hw0 hw1).scaleLeftSigned (form (kernel w) left right)

/-- The whole signed form, not merely its entries, is exactly the finite
physical normalized form after one computed common cutoff. -/
theorem normalizedFormLimit_approx_finite {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (left right : CubeSpan) (K : Nat) (hK : 2 * (termSpinBound left + termSpinBound right) ≤ K) :
    finiteNormalizedForm w (Q'.le_of_lt hw0) K left right ≈
      (normalizedFormLimit hw0 hw1 left right).approx K := by
  refine Q'.eqv_trans _ _ _ (form_kernel_congr_on _
    (fun l r => (inversePartitionLimit hw0 hw1).approx K * kernel w l r) left right ?_) ?_
  · intro l hl r hr
    have hcut : cubeKernelSaturationCutoff l.1.val r.1.val ≤ K := by
      have hlb := termSpinBound_member left hl
      have hrb := termSpinBound_member right hr
      unfold cubeKernelSaturationCutoff
      omega
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (cubeStableRawKernel_eventual w l.1.val r.1.val l.1.property.1 r.1.property.1 K hcut))
      (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (inversePartitionLimit_approx hw0 hw1 K))))
  · exact Q'.eqv_trans _ _ _ (form_kernel_scale _ _ left right) (Q'.mul_comm_eqv _ _)

/-- Uniform comparison of the two reflected norms at fixed anchor/extent.
This is NOT a comparison with the marginal norm, and NOT a strict gap. -/
theorem normalizedFormLimit_anchor_norm_bounds (terms : CubeSpan) (K : Nat) :
    Q'.mkPos 64 65 (by decide) * form (kernel anchorCoupling) terms terms ≤
        (normalizedFormLimit (w := anchorCoupling) (by decide) (by decide) terms terms).approx K ∧
      (normalizedFormLimit (w := anchorCoupling) (by decide) (by decide) terms terms).approx K ≤
        form (kernel anchorCoupling) terms terms := by
  have hnonneg := form_nonnegative (w := anchorCoupling) (by decide) terms
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (inversePartitionLimit_anchor_floor K) hnonneg)
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
  · exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
      (inversePartitionLimit_upper (w := anchorCoupling) (by decide) (by decide) K) hnonneg)
      (Q'.le_of_eqv (Q'.mul_one_eqv _))

end YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit

#print axioms YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit.normalizedKernelLimit
#print axioms YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit.normalizedKernelRegularity
#print axioms YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit.inversePartitionLimit
#print axioms YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit.inversePartitionRegularity
#print axioms YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit.inversePartitionLimit_approx
#print axioms YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit.normalizedKernelLimit_approx_scaled
#print axioms YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit.normalizedKernelLimit_eq_scaled
#print axioms YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit.inversePartitionLimit_anchor_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit.inversePartitionLimit_upper
#print axioms YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit.normalizedFormLimit
#print axioms YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit.normalizedFormRegularity
#print axioms YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit.normalizedFormLimit_approx_finite
#print axioms YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit.normalizedFormLimit_anchor_norm_bounds
