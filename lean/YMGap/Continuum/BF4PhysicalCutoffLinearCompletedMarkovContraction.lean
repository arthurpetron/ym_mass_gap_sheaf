/-
# Strict contraction of the cutoff-limit physical BF4 transfer

The preceding modules construct, from explicit completion and vacuum-pairing
data, the actual rational-linear cutoff-limit transfer on the actual completed
vacuum complement.  This file isolates the next analytic statement at that
same-object level: a single nonnegative rational rate strictly below one whose
square bounds the completed squared norm of the restricted transfer.

The certificate is `Type`-valued and carries its rate as recoverable data.
Once supplied, its estimate iterates constructively to geometric squared-norm
decay for every transfer power.  No spectral theorem, division by a possibly
zero norm, or unbounded Hamiltonian is used.

No strict-contraction certificate is inhabited here.  In particular, the
separate finite/matched-cutoff `1/16` results are not silently identified with
this cutoff-removed operator.

## Axiom gate

Only completed vacuum-complement preservation, completed-real order, rational
scaling, and induction on natural powers are used.  There is no classical
choice, noncomputable declaration, custom axiom, or unproved placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovVacuumPairing
import YMGap.Continuum.BoundedTransferCalculus

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovContraction

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement

/-! ## 1. The exact same-object strict-contraction certificate -/

/-- A recoverable strict squared-norm contraction rate for the actual
cutoff-limit transfer on the actual completed vacuum complement. -/
structure CentralPhysicalCutoffCompletedMarkovStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (pairingInvariant :
      CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
        hw0 hw1 half M) : Type where
  rate : Q'
  rate_nonnegative : (0 : Q') <= rate
  rate_lt_one : rate < (1 : Q')
  contraction : forall
    (vector : CentralPhysicalCutoffCompletedVacuumComplement
      hw0 hw1 half),
    CReal.RCle
      (centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer
          M pairingInvariant vector).1
        (centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer
          M pairingInvariant vector).1)
      (CReal.RCscale (rate * rate)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          vector.1 vector.1))

/-! ## 2. Concrete powers on the completed vacuum complement -/

/-- Natural powers of the actual restricted cutoff-limit transfer. -/
def centralPhysicalCutoffCompletedVacuumComplementMarkovPower
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (pairingInvariant :
      CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
        hw0 hw1 half M) :
    Nat ->
      CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half ->
      CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half
  | 0, vector => vector
  | n + 1, vector =>
      centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer
        M pairingInvariant
        (centralPhysicalCutoffCompletedVacuumComplementMarkovPower
          M pairingInvariant n vector)

theorem centralPhysicalCutoffCompletedVacuumComplementMarkovPower_zero
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (pairingInvariant :
      CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
        hw0 hw1 half M)
    (vector : CentralPhysicalCutoffCompletedVacuumComplement
      hw0 hw1 half) :
    centralPhysicalCutoffCompletedVacuumComplementMarkovPower
      M pairingInvariant 0 vector = vector :=
  rfl

theorem centralPhysicalCutoffCompletedVacuumComplementMarkovPower_succ
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (pairingInvariant :
      CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
        hw0 hw1 half M)
    (n : Nat)
    (vector : CentralPhysicalCutoffCompletedVacuumComplement
      hw0 hw1 half) :
    centralPhysicalCutoffCompletedVacuumComplementMarkovPower
        M pairingInvariant (n + 1) vector =
      centralPhysicalCutoffCompletedVacuumComplementMarkovTransfer
        M pairingInvariant
        (centralPhysicalCutoffCompletedVacuumComplementMarkovPower
          M pairingInvariant n vector) :=
  rfl

/-! ## 3. Geometric squared-norm decay -/

/-- The same-object strict contraction iterates geometrically on every
completed vacuum-orthogonal vector. -/
theorem centralPhysicalCutoffCompletedVacuumComplementMarkovPower_norm_decay
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    {M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half}
    {pairingInvariant :
      CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
        hw0 hw1 half M}
    (gap : CentralPhysicalCutoffCompletedMarkovStrictContractionData
      hw0 hw1 half M pairingInvariant)
    (n : Nat)
    (vector : CentralPhysicalCutoffCompletedVacuumComplement
      hw0 hw1 half) :
    CReal.RCle
      (centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalCutoffCompletedVacuumComplementMarkovPower
          M pairingInvariant n vector).1
        (centralPhysicalCutoffCompletedVacuumComplementMarkovPower
          M pairingInvariant n vector).1)
      (CReal.RCscale ((gap.rate * gap.rate) ^ n)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          vector.1 vector.1)) := by
  induction n with
  | zero =>
      rw [centralPhysicalCutoffCompletedVacuumComplementMarkovPower_zero,
        Q'.pow_zero, CReal.RCscale_one]
      exact CReal.RCle_refl _
  | succ k ih =>
      rw [centralPhysicalCutoffCompletedVacuumComplementMarkovPower_succ]
      have hstep := gap.contraction
        (centralPhysicalCutoffCompletedVacuumComplementMarkovPower
          M pairingInvariant k vector)
      refine CReal.RCle_trans hstep ?_
      have hrateSqNonnegative : (0 : Q') <= gap.rate * gap.rate :=
        Q'.mul_nonneg gap.rate gap.rate
          gap.rate_nonnegative gap.rate_nonnegative
      have hscaled := CReal.RCscale_mono hrateSqNonnegative ih
      refine CReal.RCle_trans hscaled ?_
      rw [CReal.RCscale_RCscale]
      exact CReal.RCle_refl _

/-! ## Axiom audit -/

#print axioms CentralPhysicalCutoffCompletedMarkovStrictContractionData
#print axioms centralPhysicalCutoffCompletedVacuumComplementMarkovPower
#print axioms centralPhysicalCutoffCompletedVacuumComplementMarkovPower_norm_decay

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovContraction
