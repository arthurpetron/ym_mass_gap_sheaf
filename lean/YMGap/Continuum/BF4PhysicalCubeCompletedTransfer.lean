/-
# Constructed transfer maps on the entire raw and reflected cube completions

The dense output representatives are those of the ACTUAL physical conditional
action, and their nonexpansive difference bound is proved, not assumed.
The explicit double-Cauchy extension therefore constructs an endomorphism
on every raw completion vector. The already proved inverse normalization
comparison transports it to every reflected completion vector.

Dense agreement and both raw/reflected conjugation laws are proved here.
Extending the operator laws to all completed vectors and intertwining with
the entire existing marginal sector remain subsequent obligations. This is
not a stationary sector vacuum, a geometric-time identification, a uniform
strict gap or a continuum theory.
-/

import YMGap.Continuum.BF4PhysicalCubeDenseTransfer
import YMGap.Continuum.GNSDenseCompletionExtension

namespace YMGap.Continuum.BF4PhysicalCubeCompletedTransfer

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSDenseCompletionExtension
open YMGap.Continuum.ScaledGNSCompletion
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeCompletion
open YMGap.Continuum.BF4PhysicalCubeCompletedReflectedRealization
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage
open YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing
open YMGap.Continuum.BF4PhysicalCubeDenseTransfer
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local notation "D" => cubeGNSData anchorCoupling (by decide)
local notation "M" => centralPhysicalVacuumSectorCylinderSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0

/-- Both fields are inhabited by the same physical SU(2) construction. -/
def denseTransferData : DenseMap D where
  toRep := rawActionRep
  nonexpansive := rawAction_contraction

def cubeRawTransfer : CubeCompletion anchorCoupling (by decide) → CubeCompletion anchorCoupling (by decide) :=
  denseTransferData.completionMap

theorem cubeRawTransfer_mk (X : CauchyGNS D) :
    cubeRawTransfer (Quotient.mk (cauchySetoid D) X) =
      Quotient.mk (cauchySetoid D) (denseTransferData.mapRep X) := rfl

theorem cubeRawTransfer_embed (terms : CubeSpan) :
    cubeRawTransfer (embedSpan anchorCoupling (by decide) terms) = rawAction terms :=
  denseTransferData.completionMap_embed terms

/-- An endomorphism of the ENTIRE reflected completion, via the constructed
inverse raw comparison, not a map defined only on marginal-sector images. -/
def cubeTransfer (x : CubeReflectedCompletion) : CubeReflectedCompletion :=
  rawToReflected (cubeRawTransfer (reflectedToRaw x))

/-- Explicit output Cauchy data, including the computed double diagonal. -/
def cubeTransferRep (X : cubeReflectedSeminorm.Cauchy) : cubeReflectedSeminorm.Cauchy :=
  toScaledCauchy D anchorNormalization
    (denseTransferData.mapRep (toRawCauchy D anchorNormalization X))

theorem cubeTransfer_mk (X : cubeReflectedSeminorm.Cauchy) :
    cubeTransfer (Quotient.mk cubeReflectedSeminorm.completionSetoid X) =
      Quotient.mk cubeReflectedSeminorm.completionSetoid (cubeTransferRep X) := rfl

/-- The output representative uses the universal diagonal rate. Its actual
sample indices still depend on the input and dense-output Cauchy moduli. -/
theorem cubeTransferRep_modulus (X : cubeReflectedSeminorm.Cauchy) (epsilon : Q') :
    (cubeTransferRep X).modulus epsilon = gMod epsilon := rfl

theorem cubeTransfer_rawComparison (x : CubeCompletion anchorCoupling (by decide)) :
    cubeTransfer (rawToReflected x) = rawToReflected (cubeRawTransfer x) := by
  unfold cubeTransfer
  rw [raw_reflected_inverse]

theorem cubeRawTransfer_reflectedComparison (x : CubeReflectedCompletion) :
    reflectedToRaw (cubeTransfer x) = cubeRawTransfer (reflectedToRaw x) := by
  unfold cubeTransfer
  rw [raw_reflected_inverse]

/-- Exact agreement with the ACTUAL sector conditional action at every
finite signed input. This is stronger than matching a chosen model kernel. -/
theorem cubeTransfer_embed (terms : CubeSpan) :
    cubeTransfer (cubeReflectedEmbed terms) =
      mappedTransfer ((M).embedRep (spanPresentation terms)) := by
  unfold cubeTransfer
  rw [reflectedToRaw_embed, cubeRawTransfer_embed, rawAction_reflected]

/-- The new completed map's dense output pairings are the original physical
two-insertion pairings, with the same normalization and the same P. -/
theorem cubeTransfer_dense_pairing (left right : CubeSpan) :
    cubeReflectedInner (cubeTransfer (cubeReflectedEmbed left))
      (cubeTransfer (cubeReflectedEmbed right)) =
      completedReflectedForm (w := anchorCoupling) (by decide) (by decide) 0
        (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer
          (w := anchorCoupling) (by decide) (by decide) 0
          (cubeToCompleted (w := anchorCoupling) (by decide) (by decide) left))
        (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer
          (w := anchorCoupling) (by decide) (by decide) 0
          (cubeToCompleted (w := anchorCoupling) (by decide) (by decide) right)) := by
  unfold cubeTransfer
  rw [reflectedToRaw_embed, reflectedToRaw_embed, cubeRawTransfer_embed, cubeRawTransfer_embed]
  exact Eq.trans (cubeReflectedInner_comparison (rawAction left) (rawAction right))
    (rawAction_pairing left right)

end YMGap.Continuum.BF4PhysicalCubeCompletedTransfer

#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransfer.denseTransferData
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransfer.cubeRawTransfer
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransfer.cubeRawTransfer_mk
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransfer.cubeRawTransfer_embed
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransfer.cubeTransfer
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransfer.cubeTransferRep
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransfer.cubeTransfer_mk
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransfer.cubeTransferRep_modulus
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransfer.cubeTransfer_rawComparison
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransfer.cubeRawTransfer_reflectedComparison
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransfer.cubeTransfer_embed
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedTransfer.cubeTransfer_dense_pairing
