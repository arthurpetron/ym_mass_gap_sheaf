/-
# The completed physical BF4 Markov action on the vacuum complement

The cutoff-limit Markov transfer already exists conditionally on its exact
diagonal-Cauchy and representative-close modulus, is rational-linear, and
fixes the normalized completed vacuum.  To restrict that transfer to the
completed vacuum complement, the remaining logical requirement is preservation
of the completed pairing with the vacuum.

This file isolates that minimum requirement as explicit `Type`-level data.  It
also records the stronger, physically natural self-adjointness certificate and
proves that self-adjointness implies vacuum-pairing invariance because the
transfer fixes the vacuum.  The invariant transfer is then restricted to the
actual completed vacuum-complement subtype and bundled as a rational-linear
endomorphism.

Neither pairing invariance nor self-adjointness is inhabited here.  Deriving
one of them from finite-cutoff detailed balance together with cross-cutoff
control is the next analytic frontier.  No strict contraction or spectral gap
is asserted.

## Axiom gate

Only the proved completed inner form, vacuum identity, quotient transfer, and
rational-linearity laws are used.  There is no classical choice,
noncomputable declaration, custom axiom, or unproved placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovLaws

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovVacuumComplement

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovLaws
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement

/-! ## 1. The exact remaining pairing certificate -/

/-- The minimum completed-form compatibility needed for the actual transfer to
preserve the completed vacuum complement.  This is explicit analytic data,
not an assumed theorem or a vacuous proposition. -/
structure CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half) : Type where
  pairing : forall
    (vector : CentralPhysicalCutoffLinearCompletion hw0 hw1 half),
    centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalCutoffCompletedMarkovTransfer M vector)
        (centralPhysicalCutoffCompletedVacuum hw0 hw1 half) =
      centralPhysicalCutoffCompletedInner hw0 hw1 half vector
        (centralPhysicalCutoffCompletedVacuum hw0 hw1 half)

/-- A stronger physical certificate: the actual completed transfer is
self-adjoint for the actual completed physical inner form. -/
structure CentralPhysicalCutoffCompletedMarkovSelfAdjointData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half) : Type where
  selfAdjoint : forall
    (left right : CentralPhysicalCutoffLinearCompletion hw0 hw1 half),
    centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalCutoffCompletedMarkovTransfer M left) right =
      centralPhysicalCutoffCompletedInner hw0 hw1 half left
        (centralPhysicalCutoffCompletedMarkovTransfer M right)

/-- Self-adjointness contracts to the minimum vacuum-pairing certificate
because the completed transfer already fixes the normalized vacuum. -/
def CentralPhysicalCutoffCompletedMarkovSelfAdjointData.toVacuumPairingInvariant
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    {M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half}
    (selfAdjointData :
      CentralPhysicalCutoffCompletedMarkovSelfAdjointData
        hw0 hw1 half M) :
    CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
      hw0 hw1 half M where
  pairing vector := by
    calc
      centralPhysicalCutoffCompletedInner hw0 hw1 half
          (centralPhysicalCutoffCompletedMarkovTransfer M vector)
          (centralPhysicalCutoffCompletedVacuum hw0 hw1 half) =
        centralPhysicalCutoffCompletedInner hw0 hw1 half vector
          (centralPhysicalCutoffCompletedMarkovTransfer M
            (centralPhysicalCutoffCompletedVacuum hw0 hw1 half)) :=
          selfAdjointData.selfAdjoint vector
            (centralPhysicalCutoffCompletedVacuum hw0 hw1 half)
      _ = centralPhysicalCutoffCompletedInner hw0 hw1 half vector
          (centralPhysicalCutoffCompletedVacuum hw0 hw1 half) := by
            rw [centralPhysicalCutoffCompletedMarkovTransfer_vacuum]

/-! ## 2. Restriction to the actual completed vacuum complement -/

/-- Vacuum-pairing invariance is exactly sufficient to preserve completed
vacuum orthogonality. -/
theorem centralPhysicalCutoffCompletedMarkovTransfer_preserves_orthogonal
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    {M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half}
    (pairingInvariant :
      CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
        hw0 hw1 half M)
    {vector : CentralPhysicalCutoffLinearCompletion hw0 hw1 half}
    (hvector : CentralPhysicalCutoffCompletedVacuumOrthogonal
      hw0 hw1 half vector) :
    CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
      (centralPhysicalCutoffCompletedMarkovTransfer M vector) := by
  unfold CentralPhysicalCutoffCompletedVacuumOrthogonal at hvector ⊢
  rw [pairingInvariant.pairing, hvector]

/-- The actual completed transfer restricted to the actual completed vacuum
complement. -/
def centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (pairingInvariant :
      CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
        hw0 hw1 half M) :
    CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half ->
      CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half :=
  fun vector =>
    ⟨centralPhysicalCutoffCompletedMarkovTransfer M vector.1,
      centralPhysicalCutoffCompletedMarkovTransfer_preserves_orthogonal
        pairingInvariant vector.2⟩

/-! ## 3. Rational-linearity of the restricted transfer -/

theorem centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer_zero
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (pairingInvariant :
      CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
        hw0 hw1 half M) :
    centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer
        M pairingInvariant
        (centralPhysicalCutoffCompletedVacuumComplementZero hw0 hw1 half) =
      centralPhysicalCutoffCompletedVacuumComplementZero hw0 hw1 half := by
  apply Subtype.ext
  exact centralPhysicalCutoffCompletedMarkovTransfer_zero M

theorem centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer_add
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (pairingInvariant :
      CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
        hw0 hw1 half M)
    (left right :
      CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half) :
    centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer
        M pairingInvariant
        (centralPhysicalCutoffCompletedVacuumComplementAdd
          hw0 hw1 half left right) =
      centralPhysicalCutoffCompletedVacuumComplementAdd hw0 hw1 half
        (centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer
          M pairingInvariant left)
        (centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer
          M pairingInvariant right) := by
  apply Subtype.ext
  exact centralPhysicalCutoffCompletedMarkovTransfer_add M left.1 right.1

theorem centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer_smul
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (pairingInvariant :
      CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
        hw0 hw1 half M)
    (scalar : Q')
    (vector : CentralPhysicalCutoffCompletedVacuumComplement
      hw0 hw1 half) :
    centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer
        M pairingInvariant
        (centralPhysicalCutoffCompletedVacuumComplementSmul
          hw0 hw1 half scalar vector) =
      centralPhysicalCutoffCompletedVacuumComplementSmul hw0 hw1 half scalar
        (centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer
          M pairingInvariant vector) := by
  apply Subtype.ext
  exact centralPhysicalCutoffCompletedMarkovTransfer_smul M scalar vector.1

/-- The restricted transfer as a rational-linear endomorphism of the concrete
completed vacuum-complement module. -/
def centralPhysicalCutoffCompletedVacuumComplementMarkovQLinearEndomorphism
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (pairingInvariant :
      CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
        hw0 hw1 half M) :
    CompletedQLinearEndomorphismData
      (centralPhysicalCutoffCompletedVacuumComplementQModule
        hw0 hw1 half) where
  toFun := centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer
    M pairingInvariant
  map_zero :=
    centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer_zero
      M pairingInvariant
  map_add :=
    centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer_add
      M pairingInvariant
  map_smul :=
    centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer_smul
      M pairingInvariant

/-! ## Axiom audit -/

#print axioms CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
#print axioms CentralPhysicalCutoffCompletedMarkovSelfAdjointData
#print axioms CentralPhysicalCutoffCompletedMarkovSelfAdjointData.toVacuumPairingInvariant
#print axioms centralPhysicalCutoffCompletedMarkovTransfer_preserves_orthogonal
#print axioms centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer
#print axioms centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer_zero
#print axioms centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer_add
#print axioms centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer_smul
#print axioms centralPhysicalCutoffCompletedVacuumComplementMarkovQLinearEndomorphism

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovVacuumComplement
