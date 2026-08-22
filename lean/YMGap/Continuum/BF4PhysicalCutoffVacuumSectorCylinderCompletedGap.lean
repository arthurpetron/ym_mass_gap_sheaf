/-
# The cofinal rate contracts the completed BF4 root sector

The completed canonical root sector, its invariant transfer, powers, and
same-object autocorrelation are now concrete.  The pointwise-adaptive global
gap compiler now accepts any cofinal rational strict rate without the old
same-index completion modulus.

This file joins those two constructions.  A
`FixedNomeCofinalCenteredStrictGap` at rate `q` pulls back to squared-norm
contraction by `q*q` on the actual completed sector vacuum complement.
Induction gives geometric decay for every sector power, and completed
Cauchy--Schwarz gives decay of the squared same-object autocorrelation.

Thus the complete fixed-nome, finite-half-volume operator conclusion now has
one rate input: a common cofinal finite strict-gap certificate.  No inhabitant
of that certificate, thermodynamic limit, continuum QFT, or Clay mass-gap
theorem is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCofinalStrictGap
import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveContraction
import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovCorrelationDecay
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerLaws
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovCorrelationDecay
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCofinalGap
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCofinalStrictGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTailInhabited
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift

/-! ## 1. Strict contraction on the actual sector vacuum complement -/

/-- Reusable strict squared-norm contraction data for the completed canonical
root sector. -/
structure CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type where
  rate : Q'
  rate_nonnegative : (0 : Q') <= rate
  rate_lt_one : rate < (1 : Q')
  contraction : forall
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      hw0 hw1 half),
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
          hw0 hw1 half vector).1
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
          hw0 hw1 half vector).1)
      (CReal.RCscale (rate * rate)
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          vector.1 vector.1))

/-- A cofinal finite strict rate contracts the actual completed sector
transfer at the same norm rate. -/
def centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap
      w (Q'.le_of_lt hw0) half q) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half where
  rate := q
  rate_nonnegative := certificate.rate_nonnegative
  rate_lt_one := certificate.rate_lt_one
  contraction := by
    intro vector
    let globalGap :=
      centralPhysicalConcreteAdaptiveCompletedMarkovCofinalStrictContractionDataAtRate
        hw0 hw1 half certificate
    have hglobal := globalGap.contraction
      (centralPhysicalVacuumSectorCylinderCompletedVacuumComplementToGlobal
        vector)
    unfold centralPhysicalVacuumSectorCylinderCompletedInner
    change CReal.RCle
      (centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          (centralPhysicalVacuumSectorCylinderCompletedTransfer
            hw0 hw1 half vector.1))
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          (centralPhysicalVacuumSectorCylinderCompletedTransfer
            hw0 hw1 half vector.1)))
      _
    have hintertwines :=
      (centralPhysicalVacuumSectorCylinderTransferLiftData
        hw0 hw1 half).intertwines vector.1
    unfold centralPhysicalVacuumSectorCylinderCompletedTransfer
    rw [hintertwines]
    exact hglobal

/-! ## 2. Every sector power decays geometrically -/

@[simp] theorem
    centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      hw0 hw1 half) :
    centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
      hw0 hw1 half 0 vector = vector := by
  apply Subtype.ext
  rfl

theorem centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower_succ
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half n : Nat)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      hw0 hw1 half) :
    centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
        hw0 hw1 half (n + 1) vector =
      centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
        hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
          hw0 hw1 half n vector) := by
  apply Subtype.ext
  rfl

/-- Any strict sector contraction iterates with the geometric squared-norm
rate `(q*q)^n`. -/
theorem centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower_norm_decay
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (gap : CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half)
    (n : Nat)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      hw0 hw1 half) :
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
          hw0 hw1 half n vector).1
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
          hw0 hw1 half n vector).1)
      (CReal.RCscale ((gap.rate * gap.rate) ^ n)
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          vector.1 vector.1)) := by
  induction n with
  | zero =>
      rw [centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower_zero,
        Q'.pow_zero, CReal.RCscale_one]
      exact CReal.RCle_refl _
  | succ k ih =>
      rw [centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower_succ]
      have hstep := gap.contraction
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
          hw0 hw1 half k vector)
      refine CReal.RCle_trans hstep ?_
      have hrateSqNonnegative : (0 : Q') <= gap.rate * gap.rate :=
        Q'.mul_nonneg gap.rate gap.rate
          gap.rate_nonnegative gap.rate_nonnegative
      have hscaled := CReal.RCscale_mono hrateSqNonnegative ih
      refine CReal.RCle_trans hscaled ?_
      rw [CReal.RCscale_RCscale]
      exact CReal.RCle_refl _

/-- Concrete geometric decay from the one remaining cofinal common-rate
certificate. -/
theorem centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower_cofinal_norm_decay
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap
      w (Q'.le_of_lt hw0) half q)
    (n : Nat)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      hw0 hw1 half) :
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
          hw0 hw1 half n vector).1
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
          hw0 hw1 half n vector).1)
      (CReal.RCscale ((q * q) ^ n)
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          vector.1 vector.1)) := by
  exact
    centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower_norm_decay
      (centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtRate
        hw0 hw1 half certificate) n vector

/-! ## 3. Same-object completed autocorrelation decay -/

/-- Cauchy--Schwarz pulls back from the global physical completion to the
completed root sector. -/
theorem centralPhysicalVacuumSectorCylinderCompletedInner_cauchy_schwarz
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (left right :
      CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalVacuumSectorCylinderCompletedInner
          hw0 hw1 half left right)
        (centralPhysicalVacuumSectorCylinderCompletedInner
          hw0 hw1 half left right))
      (CReal.RCmul
        (centralPhysicalVacuumSectorCylinderCompletedInner
          hw0 hw1 half left left)
        (centralPhysicalVacuumSectorCylinderCompletedInner
          hw0 hw1 half right right)) := by
  unfold centralPhysicalVacuumSectorCylinderCompletedInner
  exact centralPhysicalCutoffCompletedInner_cauchy_schwarz
    hw0 hw1 half
    (centralPhysicalVacuumSectorCylinderCompletionToGlobal left)
    (centralPhysicalVacuumSectorCylinderCompletionToGlobal right)

private theorem RCmul_mono_nonnegative_left
    {factor left right : CReal.RC}
    (hfactor : CReal.RCnonneg factor)
    (hle : CReal.RCle left right) :
    CReal.RCle
      (CReal.RCmul factor left)
      (CReal.RCmul factor right) := by
  revert hfactor hle
  refine Quotient.inductionOn₃ factor left right ?_
  intro F L R hF hLR
  exact CReal.leEv_mul_nonneg_left hF hLR

private theorem RCmul_mono_nonnegative_right
    {left right factor : CReal.RC}
    (hle : CReal.RCle left right)
    (hfactor : CReal.RCnonneg factor) :
    CReal.RCle
      (CReal.RCmul left factor)
      (CReal.RCmul right factor) := by
  rw [CReal.RCmul_comm left factor, CReal.RCmul_comm right factor]
  exact RCmul_mono_nonnegative_left hfactor hle

/-- Geometric decay of the squared same-object completed sector
autocorrelation. -/
theorem centralPhysicalVacuumSectorCylinderCompletedAutocorrelation_sq_decay
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (gap : CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half)
    (n : Nat)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      hw0 hw1 half) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
          hw0 hw1 half n vector.1)
        (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
          hw0 hw1 half n vector.1))
      (CReal.RCmul
        (CReal.RCscale ((gap.rate * gap.rate) ^ n)
          (centralPhysicalVacuumSectorCylinderCompletedInner
            hw0 hw1 half vector.1 vector.1))
        (centralPhysicalVacuumSectorCylinderCompletedInner
          hw0 hw1 half vector.1 vector.1)) := by
  have hcs :=
    centralPhysicalVacuumSectorCylinderCompletedInner_cauchy_schwarz
      hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
        hw0 hw1 half n vector).1 vector.1
  have hnorm :=
    centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower_norm_decay
      gap n vector
  have hvectorNonnegative :=
    centralPhysicalCutoffCompletedInner_self_nonneg hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCompletionToGlobal vector.1)
  have hscaled := RCmul_mono_nonnegative_right hnorm hvectorNonnegative
  exact CReal.RCle_trans hcs hscaled

/-- The cofinal common-rate certificate gives the same geometric
autocorrelation conclusion with its explicit rate `q`. -/
theorem centralPhysicalVacuumSectorCylinderCompletedAutocorrelation_cofinal_sq_decay
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap
      w (Q'.le_of_lt hw0) half q)
    (n : Nat)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      hw0 hw1 half) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
          hw0 hw1 half n vector.1)
        (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
          hw0 hw1 half n vector.1))
      (CReal.RCmul
        (CReal.RCscale ((q * q) ^ n)
          (centralPhysicalVacuumSectorCylinderCompletedInner
            hw0 hw1 half vector.1 vector.1))
        (centralPhysicalVacuumSectorCylinderCompletedInner
          hw0 hw1 half vector.1 vector.1)) := by
  exact centralPhysicalVacuumSectorCylinderCompletedAutocorrelation_sq_decay
    (centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtRate
      hw0 hw1 half certificate) n vector

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap.CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap.centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtRate
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap.centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower_norm_decay
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap.centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower_cofinal_norm_decay
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap.centralPhysicalVacuumSectorCylinderCompletedInner_cauchy_schwarz
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap.centralPhysicalVacuumSectorCylinderCompletedAutocorrelation_sq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap.centralPhysicalVacuumSectorCylinderCompletedAutocorrelation_cofinal_sq_decay
