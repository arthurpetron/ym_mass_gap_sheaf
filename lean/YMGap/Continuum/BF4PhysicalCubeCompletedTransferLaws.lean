/-
# Full-space laws of the actual physical cube completion transfer

At the fixed anchor w=1/400 and extent one, mixed dense pairings are pinned
to the existing physical sector action. Cancelling its actual positive
normalization gives dense symmetry and positivity; joint pairing continuity
passes both to the already constructed endomorphism on the ENTIRE raw
completion. Its exact difference bound also passes without constant loss.
The inverse normalization comparison transports these laws to the entire
reflected completion. Dense testing proves intertwining with the entire
existing marginal sector, and hence its same-object conditional moments.
No stationary sector vacuum, geometric-time or strict-gap assertion is made.
-/

import YMGap.Continuum.BF4PhysicalCubeCompletedTransfer
import YMGap.Continuum.GNSDenseCompletionLaws

namespace YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSDenseCompletionLaws
open YMGap.Continuum.RCBilinearDifference
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeCompletion
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeSectorComparison
open YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage
open YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing
open YMGap.Continuum.BF4PhysicalCubeDenseTransfer
open YMGap.Continuum.BF4PhysicalCubeCompletedTransfer
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local notation "D" => cubeGNSData anchorCoupling (by decide)
local notation "Raw" => CubeCompletion anchorCoupling (by decide)
local notation "M" => centralPhysicalVacuumSectorCylinderSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "lambda" => Quotient.mk CReal.crealSetoid anchorNormalization.value
local notation "j" => embedSpan anchorCoupling (by decide)

/-- Rational scalar structure for the SAME physical finite-span GNS datum. -/
def cubeScalarData : YMGap.Continuum.HamiltonianScalar.SmulGNSData where
  toGNSData := D
  smul_sub := by
    intro s a b test
    let k := YMGap.Continuum.BF4PhysicalCubeGNSData.kernel anchorCoupling
    let f := fun v : CubeSpan => RationalKernelSpan.sectionPairing k v test
    have hp (u v : CubeSpan) : Q'.eqv (f ((D).sub u v)) (f u + (-1 : Q') * f v) :=
      Q'.eqv_trans _ _ _ (RationalKernelSpan.pairing_append k u _ test)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (RationalKernelSpan.pairing_scale k (-1) v test))
    have hs (v : CubeSpan) : Q'.eqv (f ((D).smul s v)) (s * f v) :=
      RationalKernelSpan.pairing_scale k s v test
    exact Q'.eqv_trans _ _ _ (hs ((D).sub a b)) (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (hp a b)) (Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv _ _ _) (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_trans _ _ _
            (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) (Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) (Q'.mul_assoc_eqv _ _ _))))
          (Q'.eqv_symm (Q'.eqv_trans _ _ _ (hp ((D).smul s a) ((D).smul s b))
            (Q'.add_eqv_congr' (hs a) (Q'.mul_eqv_congr_left _ _ _ (hs b))))))))

private theorem normalization_zero : CReal.RCmul CReal.RCzero lambda = CReal.RCzero :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.zero_mul_eqv (anchorNormalization.value.approx n)))

private theorem normalization_cancel (a b : CReal.RC)
    (h : CReal.RCle (CReal.RCmul a lambda) (CReal.RCmul b lambda)) : CReal.RCle a b := by
  revert h
  refine Quotient.inductionOn₂ a b ?_
  intro A B h
  exact cancel_positive_factor anchorNormalization.floor anchorNormalization.floor_pos
    anchorNormalization.lower h

private theorem normalization_mono (a b : CReal.RC) (h : CReal.RCle a b) :
    CReal.RCle (CReal.RCmul a lambda) (CReal.RCmul b lambda) := by
  revert h
  refine Quotient.inductionOn₂ a b ?_
  intro A B h epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  refine ⟨N, fun n hn => ?_⟩
  have hnneg := Q'.le_trans' _ _ _ (Q'.le_of_lt anchorNormalization.floor_pos)
    (anchorNormalization.lower n)
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ _ (hN n hn) hnneg
  have hbudget := Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ epsilon
    (anchorNormalization.upper n) (Q'.le_of_lt hepsilon)) (Q'.le_of_eqv (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ hmul (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_mul_eqv _ _ _))
    (Q'.add_le_add_left _ _ _ hbudget))

private theorem normalization_injective (a b : CReal.RC)
    (h : CReal.RCmul a lambda = CReal.RCmul b lambda) : a = b := by
  apply CReal.RCle_antisymm
  · apply normalization_cancel
    rw [h]
    exact CReal.RCle_refl _
  · apply normalization_cancel
    rw [h]
    exact CReal.RCle_refl _

theorem cubeReflectedInner_symm (x y : CubeReflectedCompletion) :
    cubeReflectedInner x y = cubeReflectedInner y x := by
  change CReal.RCmul ((D).cinnerCompl (reflectedToRaw x) (reflectedToRaw y)) lambda =
    CReal.RCmul ((D).cinnerCompl (reflectedToRaw y) (reflectedToRaw x)) lambda
  rw [(D).cinnerCompl_comm]

/-- The dense mixed pairing uses the SAME sector map, input and output. -/
theorem rawAction_mixed_pairing (left right : CubeSpan) :
    CReal.RCmul ((D).cinnerCompl (rawAction left) (j right)) lambda =
      cubeReflectedInner (mappedTransfer ((M).embedRep (spanPresentation left)))
        (sectorToReflected ((M).embedRep (spanPresentation right))) := by
  refine Eq.trans (cubeReflectedInner_comparison (rawAction left) (j right)).symm ?_
  rw [rawAction_reflected, rawToReflected_embed, spanPresentation_reflected]

theorem rawAction_selfAdjoint (left right : CubeSpan) :
    (D).cinnerCompl (rawAction left) (j right) = (D).cinnerCompl (j left) (rawAction right) := by
  apply normalization_injective
  rw [rawAction_mixed_pairing, (D).cinnerCompl_comm (j left) (rawAction right), rawAction_mixed_pairing]
  exact Eq.trans (mappedTransfer_selfAdjoint ((M).embedRep (spanPresentation left))
    ((M).embedRep (spanPresentation right))) (cubeReflectedInner_symm _ _)

theorem rawAction_positive (terms : CubeSpan) :
    CReal.RCnonneg ((D).cinnerCompl (rawAction terms) (j terms)) := by
  apply normalization_cancel
  rw [normalization_zero, rawAction_mixed_pairing]
  exact mappedTransfer_positive ((M).embedRep (spanPresentation terms))

theorem cubeRawTransfer_nonexpansive (x y : Raw) :
    CReal.RCle
      ((D).cinnerCompl ((D).cSub (cubeRawTransfer x) (cubeRawTransfer y))
        ((D).cSub (cubeRawTransfer x) (cubeRawTransfer y)))
      ((D).cinnerCompl ((D).cSub x y) ((D).cSub x y)) :=
  completionMap_nonexpansive denseTransferData x y

theorem cubeRawTransfer_selfAdjoint (x y : Raw) :
    (D).cinnerCompl (cubeRawTransfer x) y = (D).cinnerCompl x (cubeRawTransfer y) :=
  completionMap_selfAdjoint denseTransferData rawAction_selfAdjoint x y

theorem cubeRawTransfer_positive (x : Raw) :
    CReal.RCnonneg ((D).cinnerCompl (cubeRawTransfer x) x) :=
  completionMap_positive denseTransferData rawAction_positive x

/-- Symmetry and nondegeneracy give actual vector additivity. -/
theorem cubeRawTransfer_add (x y : Raw) :
    cubeRawTransfer ((D).cAdd x y) = (D).cAdd (cubeRawTransfer x) (cubeRawTransfer y) := by
  apply eq_of_pairings_equal
  intro z
  rw [cubeRawTransfer_selfAdjoint, (D).cinnerCompl_cAdd_left,
    (D).cinnerCompl_cAdd_left, cubeRawTransfer_selfAdjoint, cubeRawTransfer_selfAdjoint]

theorem cubeRawTransfer_zero : cubeRawTransfer (j []) = j [] := by
  apply eq_of_pairings_equal
  intro z
  rw [cubeRawTransfer_selfAdjoint]
  exact Eq.trans ((D).cinnerCompl_embedZero_left (cubeRawTransfer z))
    ((D).cinnerCompl_embedZero_left z).symm

theorem cubeRawTransfer_smul (s : Q') (x : Raw) :
    cubeRawTransfer (cubeScalarData.cSmul s x) = cubeScalarData.cSmul s (cubeRawTransfer x) := by
  apply eq_of_pairings_equal
  intro z
  rw [cubeRawTransfer_selfAdjoint]
  exact Eq.trans (cubeScalarData.cinnerCompl_cSmul_left s x (cubeRawTransfer z))
    (Eq.trans (congrArg (CReal.RCscale s) (cubeRawTransfer_selfAdjoint x z).symm)
      (cubeScalarData.cinnerCompl_cSmul_left s (cubeRawTransfer x) z).symm)

private theorem raw_sub_zero (x : Raw) : (D).cSub x (j []) = x := by
  apply eq_of_pairings_equal
  intro z
  rw [(D).cinnerCompl_cSub_left]
  have hz : (D).cinnerCompl (j []) z = CReal.RCzero := (D).cinnerCompl_embedZero_left z
  rw [hz]
  refine Quotient.inductionOn ((D).cinnerCompl x z) ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n))))

theorem cubeRawTransfer_contraction (x : Raw) :
    CReal.RCle ((D).cinnerCompl (cubeRawTransfer x) (cubeRawTransfer x)) ((D).cinnerCompl x x) := by
  have h := cubeRawTransfer_nonexpansive x (j [])
  rw [cubeRawTransfer_zero, raw_sub_zero, raw_sub_zero] at h
  exact h

/-- Reflected addition transported through the already proved inverse maps. -/
def cubeReflectedAdd (x y : CubeReflectedCompletion) : CubeReflectedCompletion :=
  rawToReflected ((D).cAdd (reflectedToRaw x) (reflectedToRaw y))

def cubeReflectedSub (x y : CubeReflectedCompletion) : CubeReflectedCompletion :=
  rawToReflected ((D).cSub (reflectedToRaw x) (reflectedToRaw y))

def cubeReflectedSmul (s : Q') (x : CubeReflectedCompletion) : CubeReflectedCompletion :=
  rawToReflected (cubeScalarData.cSmul s (reflectedToRaw x))

theorem cubeReflectedSmul_embed (s : Q') (terms : CubeSpan) :
    cubeReflectedSmul s (cubeReflectedEmbed terms) = cubeReflectedEmbed ((D).smul s terms) := by
  unfold cubeReflectedSmul
  rw [reflectedToRaw_embed]
  exact Eq.trans (congrArg rawToReflected (cubeScalarData.cSmul_embed s terms)) (rawToReflected_embed _)

theorem cubeReflectedAdd_embed (left right : CubeSpan) :
    cubeReflectedAdd (cubeReflectedEmbed left) (cubeReflectedEmbed right) =
      cubeReflectedEmbed ((D).add left right) := by
  unfold cubeReflectedAdd
  rw [reflectedToRaw_embed, reflectedToRaw_embed]
  exact Eq.trans (congrArg rawToReflected ((D).cAdd_embed left right)) (rawToReflected_embed _)

theorem cubeReflectedSub_embed (left right : CubeSpan) :
    cubeReflectedSub (cubeReflectedEmbed left) (cubeReflectedEmbed right) =
      cubeReflectedEmbed ((D).sub left right) := by
  unfold cubeReflectedSub
  rw [reflectedToRaw_embed, reflectedToRaw_embed]
  exact Eq.trans (congrArg rawToReflected ((D).cSub_embed left right)) (rawToReflected_embed _)

theorem cubeTransfer_nonexpansive (x y : CubeReflectedCompletion) :
    CReal.RCle
      (cubeReflectedInner (cubeReflectedSub (cubeTransfer x) (cubeTransfer y))
        (cubeReflectedSub (cubeTransfer x) (cubeTransfer y)))
      (cubeReflectedInner (cubeReflectedSub x y) (cubeReflectedSub x y)) := by
  unfold cubeReflectedSub
  rw [cubeRawTransfer_reflectedComparison, cubeRawTransfer_reflectedComparison,
    cubeReflectedInner_comparison, cubeReflectedInner_comparison]
  exact normalization_mono _ _ (cubeRawTransfer_nonexpansive (reflectedToRaw x) (reflectedToRaw y))

theorem cubeTransfer_selfAdjoint (x y : CubeReflectedCompletion) :
    cubeReflectedInner (cubeTransfer x) y = cubeReflectedInner x (cubeTransfer y) := by
  change CReal.RCmul ((D).cinnerCompl (reflectedToRaw (cubeTransfer x)) (reflectedToRaw y)) lambda =
    CReal.RCmul ((D).cinnerCompl (reflectedToRaw x) (reflectedToRaw (cubeTransfer y))) lambda
  rw [cubeRawTransfer_reflectedComparison, cubeRawTransfer_reflectedComparison, cubeRawTransfer_selfAdjoint]

theorem cubeTransfer_positive (x : CubeReflectedCompletion) :
    CReal.RCnonneg (cubeReflectedInner (cubeTransfer x) x) := by
  change CReal.RCle CReal.RCzero
    (CReal.RCmul ((D).cinnerCompl (reflectedToRaw (cubeTransfer x)) (reflectedToRaw x)) lambda)
  rw [cubeRawTransfer_reflectedComparison, ← normalization_zero]
  exact normalization_mono _ _ (cubeRawTransfer_positive (reflectedToRaw x))

theorem cubeTransfer_contraction (x : CubeReflectedCompletion) :
    CReal.RCle (cubeReflectedInner (cubeTransfer x) (cubeTransfer x)) (cubeReflectedInner x x) := by
  change CReal.RCle
    (CReal.RCmul ((D).cinnerCompl (reflectedToRaw (cubeTransfer x)) (reflectedToRaw (cubeTransfer x))) lambda)
    (CReal.RCmul ((D).cinnerCompl (reflectedToRaw x) (reflectedToRaw x)) lambda)
  rw [cubeRawTransfer_reflectedComparison]
  exact normalization_mono _ _ (cubeRawTransfer_contraction (reflectedToRaw x))

theorem cubeTransfer_add (x y : CubeReflectedCompletion) :
    cubeTransfer (cubeReflectedAdd x y) = cubeReflectedAdd (cubeTransfer x) (cubeTransfer y) := by
  unfold cubeReflectedAdd
  rw [cubeTransfer_rawComparison, cubeRawTransfer_add,
    cubeRawTransfer_reflectedComparison, cubeRawTransfer_reflectedComparison]

theorem cubeTransfer_zero : cubeTransfer (cubeReflectedEmbed []) = cubeReflectedEmbed [] := by
  unfold cubeTransfer
  rw [reflectedToRaw_embed, cubeRawTransfer_zero, rawToReflected_embed]

theorem cubeTransfer_smul (s : Q') (x : CubeReflectedCompletion) :
    cubeTransfer (cubeReflectedSmul s x) = cubeReflectedSmul s (cubeTransfer x) := by
  unfold cubeReflectedSmul
  rw [cubeTransfer_rawComparison, cubeRawTransfer_smul, cubeRawTransfer_reflectedComparison]

/-- Dense physical cube tests separate EVERY reflected completion vector. -/
theorem cubeReflected_ext_dense (x y : CubeReflectedCompletion)
    (h : ∀ terms, cubeReflectedInner x (cubeReflectedEmbed terms) =
      cubeReflectedInner y (cubeReflectedEmbed terms)) : x = y := by
  have hr : reflectedToRaw x = reflectedToRaw y := by
    apply eq_of_dense_pairings
    intro terms
    apply normalization_injective
    have hx := cubeReflectedInner_comparison (reflectedToRaw x) (j terms)
    have hy := cubeReflectedInner_comparison (reflectedToRaw y) (j terms)
    rw [reflected_raw_inverse, rawToReflected_embed] at hx hy
    exact Eq.trans hx.symm (Eq.trans (h terms) hy)
  exact Eq.trans (reflected_raw_inverse x).symm
    (Eq.trans (congrArg rawToReflected hr) (reflected_raw_inverse y))

/-- The full-space endomorphism intertwines the ENTIRE existing marginal
sector action, not just its finite presentations. -/
theorem cubeTransfer_sector (x : (M).Completion) :
    cubeTransfer (sectorToReflected x) = mappedTransfer x := by
  apply cubeReflected_ext_dense
  intro terms
  rw [cubeTransfer_selfAdjoint, cubeTransfer_embed, ← spanPresentation_reflected terms]
  exact (mappedTransfer_selfAdjoint x ((M).embedRep (spanPresentation terms))).symm

/-- Powers of the same constructed endomorphism on the entire carrier. -/
def cubeTransferPower : Nat → CubeReflectedCompletion → CubeReflectedCompletion
  | 0, x => x
  | n + 1, x => cubeTransfer (cubeTransferPower n x)

theorem cubeTransferPower_sector (n : Nat) (x : (M).Completion) :
    cubeTransferPower n (sectorToReflected x) =
      sectorToReflected (centralPhysicalVacuumSectorCylinderCompletedTransferPower
        (w := anchorCoupling) (by decide) (by decide) 0 n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cubeTransferPower, ih, cubeTransfer_sector]
    rfl

/-- Same-object physical moments for every completed sector input, including
the exact extra insertion contributed by the reflected inner form. Iteration
is conditional dynamics here, not yet geometric Euclidean time. -/
theorem cubeTransferPower_sector_moments (n : Nat) (x y : (M).Completion) :
    cubeReflectedInner (sectorToReflected x) (cubeTransferPower n (sectorToReflected y)) =
      centralPhysicalCutoffCompletedInner (w := anchorCoupling) (by decide) (by decide) 0
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal x)
        (centralPhysicalConcreteAdaptiveCompletedMarkovPower
          (w := anchorCoupling) (by decide) (by decide) 0 (n + 1)
          (centralPhysicalVacuumSectorCylinderCompletionToGlobal y)) := by
  rw [cubeTransferPower_sector]
  exact sectorToReflected_moments n x y

end YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws

#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeReflectedInner_symm
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeScalarData
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeRawTransfer_smul
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeReflectedSmul
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeReflectedSmul_embed
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeTransfer_smul
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeReflected_ext_dense
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeTransfer_sector
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeTransferPower
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeTransferPower_sector
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeTransferPower_sector_moments
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.rawAction_mixed_pairing
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.rawAction_selfAdjoint
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.rawAction_positive
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeRawTransfer_nonexpansive
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeRawTransfer_selfAdjoint
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeRawTransfer_positive
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeRawTransfer_add
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeRawTransfer_zero
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeRawTransfer_contraction
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeReflectedAdd
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeReflectedSub
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeReflectedAdd_embed
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeReflectedSub_embed
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeTransfer_nonexpansive
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeTransfer_selfAdjoint
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeTransfer_positive
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeTransfer_contraction
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeTransfer_add
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws.cubeTransfer_zero
