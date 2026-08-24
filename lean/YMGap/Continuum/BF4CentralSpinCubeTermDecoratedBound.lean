/-
# Termwise decorated-activity bound for the BF4 central spin cube

The source-free fusion estimate and the exact decorated-face factorization
combine into a bound on the literal production spin-foam summand.  Every
boundary/target term is at most the six-face source activity times a product
of exponent-thirteen activities over the non-source physical faces.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4CentralSpinCubeResidualDecoratedFaceBound

namespace YMGap.Continuum.BF4CentralSpinCubeTermDecoratedBound

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CentralLowerCubeRowDomination
open YMGap.Continuum.BF4CentralSpinCubeResidualDecoratedFaceBound
open YMGap.Continuum.BF4CentralSpinCubeResidualFaceBound
open YMGap.Continuum.BF4CentralSpinCubeResidualLinkBound
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem slabCoefficient_nonnegative
    {w : Q'} (hw : (0 : Q') <= w) (K spin : Nat) :
    (0 : Q') <= coeffAt (heatKernelPacket K w) spin := by
  by_cases hspin : spin < K + 1
  · rw [coeffAt_heatKernelPacket hspin]
    exact coeffW_nonneg hw spin
  · have hlarge : K < spin := by omega
    rw [coeffAt_of_gt (heatKernelPacket K w) hlarge]
    exact Q'.le_refl' 0

private theorem eliminateLinks_nonnegative
    (value : Nat -> Q') (hvalue : forall id, (0 : Q') <= value id) :
    forall ids : List Nat, (0 : Q') <= eliminateLinks value ids
  | [] => Q'.zero_le_one
  | id :: rest =>
      Q'.mul_nonneg _ _ (hvalue id)
        (eliminateLinks_nonnegative value hvalue rest)

private theorem slabPhysicalFaceFactor_nonnegative
    {w : Q'} (hw : (0 : Q') <= w)
    (K extent : Nat) (physical : EdgeLabelling) :
    (0 : Q') <= slabParametricKPhysicalFaceFactor
      w K extent physical := by
  unfold slabParametricKPhysicalFaceFactor
  exact eliminateLinks_nonnegative _
    (fun id => slabCoefficient_nonnegative hw K (physical id)) _

private theorem qOfNat_mono {left right : Nat} (hle : left <= right) :
    Q'.ofNat left <= Q'.ofNat right := by
  show Int.ofNat left * (1 : Int) <= Int.ofNat right * (1 : Int)
  rw [Int.mul_one, Int.mul_one]
  exact Int.ofNat_le.mpr hle

/-! ## Literal production-term domination -/

/-- Every physical boundary/target summand for an admitted spin-cube source
is bounded by its exact six-face source activity times the source-free
decorated non-source face product. -/
theorem centralSpinCubePhysicalTerm_le_activity_mul_decorated
    {w : Q'} (hw : (0 : Q') <= w)
    {K spin : Nat} (hspin : spin <= K)
    (boundary target : EdgeLabelling)
    (hboundary : boundary ∈ centralBoundaryChannels K 0)
    (htarget : target ∈ centralHalfStates K 0) :
    slabParametricKPhysicalTerm w K 1
        (centralSpinCubeSourcePhysical spin boundary target) <=
      (coeffW w spin) ^ 6 *
        centralSpinCubeResidualDecoratedFaceProduct
          w boundary target := by
  let newPhysical :=
    centralSpinCubeSourcePhysical spin boundary target
  let newFace :=
    slabParametricKPhysicalFaceFactor w K 1 newPhysical
  let newLinks :=
    slabExplicitLinkMultiplicityProduct K 1 newPhysical
  let residualLinks :=
    centralSpinCubeResidualMultiplicityProduct boundary target
  let faceTwelfth :=
    centralSpinCubeResidualFaceTwelfthProduct boundary target
  have hlinkResidual : newLinks <= residualLinks := by
    unfold newLinks newPhysical residualLinks
    exact centralSpinCube_linkProduct_le_residual
      hspin boundary target hboundary htarget
  have hresidualFace : residualLinks <= faceTwelfth := by
    unfold residualLinks faceTwelfth
    exact centralSpinCubeResidualMultiplicityProduct_le_faceTwelfth
      boundary target
  have hlinks : newLinks <= faceTwelfth :=
    Nat.le_trans hlinkResidual hresidualFace
  have hqLinks : Q'.ofNat newLinks <= Q'.ofNat faceTwelfth :=
    qOfNat_mono hlinks
  have hnewFace0 : (0 : Q') <= newFace := by
    unfold newFace newPhysical
    exact slabPhysicalFaceFactor_nonnegative hw K 1 _
  have htermLe : newFace * Q'.ofNat newLinks <=
      newFace * Q'.ofNat faceTwelfth :=
    Q'.mul_le_mul_of_nonneg_left _ _ newFace hqLinks hnewFace0
  have hface :
      newFace ≈ (coeffW w spin) ^ 6 *
        slabParametricKPhysicalFaceFactor w K 1
          (centralVacuumSourcePhysical boundary target) := by
    unfold newFace newPhysical
    exact centralSpinCubePhysicalFaceFactor_eqv_activity_mul_vacuum
      w hspin boundary target
  have hdecorated :
      slabParametricKPhysicalFaceFactor w K 1
          (centralVacuumSourcePhysical boundary target) *
        Q'.ofNat faceTwelfth ≈
      centralSpinCubeResidualDecoratedFaceProduct
        w boundary target := by
    unfold faceTwelfth
    exact centralVacuumFaceFactor_mul_twelfth_eqv_decorated
      w boundary target hboundary htarget
  have hmajorant :
      newFace * Q'.ofNat faceTwelfth ≈
        (coeffW w spin) ^ 6 *
          centralSpinCubeResidualDecoratedFaceProduct
            w boundary target := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hface) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv
        ((coeffW w spin) ^ 6)
        (slabParametricKPhysicalFaceFactor w K 1
          (centralVacuumSourcePhysical boundary target))
        (Q'.ofNat faceTwelfth)) ?_
    exact Q'.mul_eqv_congr_left ((coeffW w spin) ^ 6) _ _
      hdecorated
  unfold slabParametricKPhysicalTerm
  change newFace * Q'.ofNat newLinks <= _
  exact Q'.le_trans' _ _ _ htermLe (Q'.le_of_eqv hmajorant)

end YMGap.Continuum.BF4CentralSpinCubeTermDecoratedBound

/-! ## Dependency gate -/

#print axioms YMGap.Continuum.BF4CentralSpinCubeTermDecoratedBound.centralSpinCubePhysicalTerm_le_activity_mul_decorated
