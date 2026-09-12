/-
# Complete the literal physical cube-cylinder image in its reflected norm

At the fixed anchor w=1/400 and extent one, the actual normalization has the
explicit floor 64/65. It supplies a CReal squared seminorm on the finite signed
cube spans, exactly the actual completed E form on their literal observable
image. We construct its null/Cauchy quotient, two inverse maps to the existing
raw cube completion, and the full completed pairing as the limit of the SAME
dense physical reflected pairings. All Cauchy and comparison rates are data.

This is completion of the presented root-sector image, not a claim that the
entire marginal carrier is that sector or is E-complete. No transfer on this
completion or stationary vacuum is constructed here: the nonzero root
cylinder is not the constant vacuum. Intertwining the actual conditional P,
geometric time, uniform strict gap and continuum remain open. Completeness
retains the existing raw completion's representative-family scope; no choice
of representatives from arbitrary quotient-valued sequences is asserted.
-/

import YMGap.Continuum.BF4PhysicalCubeCompletedReflectedRealization
import YMGap.Continuum.BF4PhysicalCubeCompletion
import YMGap.Continuum.ScaledGNSCompletion

namespace YMGap.Continuum.BF4PhysicalCubeReflectedCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.RationalKernelSpan
open YMGap.Continuum.ScaledGNSCompletion
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeCompletion
open YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit
open YMGap.Continuum.BF4PhysicalCubeObservableRealization
open YMGap.Continuum.BF4PhysicalCubeCompletedReflectedRealization
open YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv
local notation "D" => cubeGNSData anchorCoupling (by decide)

/-- The actual partition normalization, with its already constructed modulus. -/
def anchorNormalization : Normalization where
  value := inversePartitionLimit (w := anchorCoupling) (by decide) (by decide)
  regularity := inversePartitionRegularity (w := anchorCoupling) (by decide) (by decide)
  floor := Q'.mkPos 64 65 (by decide)
  floor_pos := by decide
  lower := inversePartitionLimit_anchor_floor
  upper := inversePartitionLimit_upper (w := anchorCoupling) (by decide) (by decide)

def cubeReflectedSeminorm := scaledSeminorm D anchorNormalization

abbrev CubeReflectedCompletion := cubeReflectedSeminorm.Completion

def cubeReflectedEmbed (terms : CubeSpan) : CubeReflectedCompletion :=
  cubeReflectedSeminorm.embedRep terms

def rawToReflected : CubeCompletion anchorCoupling (by decide) → CubeReflectedCompletion :=
  toScaledCompletion D anchorNormalization

def reflectedToRaw : CubeReflectedCompletion → CubeCompletion anchorCoupling (by decide) :=
  toRawCompletion D anchorNormalization

theorem raw_reflected_inverse (x : CubeCompletion anchorCoupling (by decide)) :
    reflectedToRaw (rawToReflected x) = x := raw_scaled_inverse D anchorNormalization x

theorem reflected_raw_inverse (x : CubeReflectedCompletion) :
    rawToReflected (reflectedToRaw x) = x := scaled_raw_inverse D anchorNormalization x

theorem rawToReflected_embed (terms : CubeSpan) :
    rawToReflected (embedSpan anchorCoupling (by decide) terms) = cubeReflectedEmbed terms :=
  toScaledCompletion_embed D anchorNormalization terms

theorem reflectedToRaw_embed (terms : CubeSpan) :
    reflectedToRaw (cubeReflectedEmbed terms) = embedSpan anchorCoupling (by decide) terms :=
  toRawCompletion_embed D anchorNormalization terms

theorem forward_modulus (X : CauchyGNS D) :
    (toScaledCauchy D anchorNormalization X).modulus = X.modulus := rfl

theorem inverse_modulus (X : cubeReflectedSeminorm.Cauchy) (epsilon : Q') :
    (toRawCauchy D anchorNormalization X).modulus epsilon =
      X.modulus (Q'.mkPos 64 65 (by decide) * epsilon) := rfl

private theorem observable_value (terms : CubeSpan) (state : EdgeLabelling) :
    (cubeObservable terms).value state = listQSum (fun t => t.2 *
      (centralPhysicalStateCylinderUnitObservable 0 t.1.val).value state) terms := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    simp only [cubeObservable, CentralPhysicalLinearObservable.value, listQSum, ih]

private theorem observable_append (left right : CubeSpan) (state : EdgeLabelling) :
    (cubeObservable (left ++ right)).value state ≈
      (cubeObservable left).value state + (cubeObservable right).value state := by
  rw [observable_value, observable_value, observable_value]
  exact listQSum_append _ left right

private theorem observable_scale (scalar : Q') (terms : CubeSpan) (state : EdgeLabelling) :
    (cubeObservable (scale scalar terms)).value state ≈ scalar * (cubeObservable terms).value state := by
  rw [observable_value, observable_value]
  unfold scale
  rw [listQSum_map]
  exact Q'.eqv_trans _ _ _ (listQSum_congr (fun _ => Q'.mul_assoc_eqv _ _ _) terms)
    (listQSum_mul_left scalar _ terms)

/-- The coefficient difference is literally the pointwise observable difference. -/
theorem cubeObservable_sub_value (left right : CubeSpan) (state : EdgeLabelling) :
    (cubeObservable ((D).sub left right)).value state ≈
      (cubeObservable left).value state + (-(cubeObservable right).value state) :=
  Q'.eqv_trans _ _ _ (observable_append left (scale (-1) right) state)
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (observable_scale (-1) right state)
        (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _)))))

/-- This quotient's distance is exactly the physical E norm of the realized
observable difference, not a freely chosen equivalent metric. -/
theorem cubeReflectedSeminorm_physical_distance (left right : CubeSpan) :
    Quotient.mk CReal.crealSetoid (cubeReflectedSeminorm.distSq left right) =
      completedReflectedForm (w := anchorCoupling) (by decide) (by decide) 0
        (cubeToCompleted (w := anchorCoupling) (by decide) (by decide) ((D).sub left right))
        (cubeToCompleted (w := anchorCoupling) (by decide) (by decide) ((D).sub left right)) :=
  (cubeToCompleted_reflected_pairing (w := anchorCoupling) (by decide) (by decide) _ _).symm

def cubeReflectedInner : CubeReflectedCompletion → CubeReflectedCompletion → CReal.RC :=
  scaledCompletedInner D anchorNormalization

/-- The completed form extends the actual physical reflected pairing. -/
theorem cubeReflectedInner_embed (left right : CubeSpan) :
    cubeReflectedInner (cubeReflectedEmbed left) (cubeReflectedEmbed right) =
      completedReflectedForm (w := anchorCoupling) (by decide) (by decide) 0
        (cubeToCompleted (w := anchorCoupling) (by decide) (by decide) left)
        (cubeToCompleted (w := anchorCoupling) (by decide) (by decide) right) :=
  Eq.trans (scaledCompletedInner_embed D anchorNormalization left right)
    (cubeToCompleted_reflected_pairing (w := anchorCoupling) (by decide) (by decide) left right).symm

theorem cubeReflectedInner_comparison (x y : CubeCompletion anchorCoupling (by decide)) :
    cubeReflectedInner (rawToReflected x) (rawToReflected y) =
      CReal.RCmul (completedInner anchorCoupling (by decide) x y)
        (Quotient.mk CReal.crealSetoid anchorNormalization.value) :=
  scaledCompletedInner_comparison D anchorNormalization x y

def cubeReflectedPairingLimit (X Y : cubeReflectedSeminorm.Cauchy) : CReal :=
  scaledPairingRep D anchorNormalization X Y

theorem cubeReflectedInner_mk (X Y : cubeReflectedSeminorm.Cauchy) :
    cubeReflectedInner (Quotient.mk cubeReflectedSeminorm.completionSetoid X)
      (Quotient.mk cubeReflectedSeminorm.completionSetoid Y) =
      Quotient.mk CReal.crealSetoid (cubeReflectedPairingLimit X Y) := rfl

/-- The full pairing is the limit of the same normalized physical dense forms. -/
theorem cubeReflectedPairingLimit_converges (X Y : cubeReflectedSeminorm.Cauchy) :
    CReal.ConvergesTo (fun n => normalizedFormLimit (w := anchorCoupling)
      (by decide) (by decide) (X.seq n) (Y.seq n)) (cubeReflectedPairingLimit X Y) :=
  scaledPairingRep_converges D anchorNormalization X Y

/-- Nontriviality survives normalization and completion; this is not a
transfer-fixed or isolated vacuum assertion. -/
theorem reflectedRoot_ne_zero : cubeReflectedEmbed rootVector ≠ cubeReflectedEmbed [] := by
  intro h
  have hr := congrArg reflectedToRaw h
  rw [reflectedToRaw_embed, reflectedToRaw_embed] at hr
  exact completedRoot_ne_zero anchorCoupling (by decide) hr

end YMGap.Continuum.BF4PhysicalCubeReflectedCompletion

#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.anchorNormalization
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.cubeReflectedSeminorm
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.cubeReflectedEmbed
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.rawToReflected
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.reflectedToRaw
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.raw_reflected_inverse
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.reflected_raw_inverse
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.rawToReflected_embed
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.reflectedToRaw_embed
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.forward_modulus
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.inverse_modulus
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.cubeObservable_sub_value
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.cubeReflectedSeminorm_physical_distance
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.cubeReflectedInner
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.cubeReflectedInner_embed
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.cubeReflectedInner_comparison
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.cubeReflectedPairingLimit
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.cubeReflectedInner_mk
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.cubeReflectedPairingLimit_converges
#print axioms YMGap.Continuum.BF4PhysicalCubeReflectedCompletion.reflectedRoot_ne_zero
