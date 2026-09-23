/-
# Explicit modulus for the original connected spatial diagonal

The centered-form module already proves convergence of the unmodified
three-regulator connected diagonal to the spatial centered moment.  This
module exposes the missing Type-level `QCauchy` witness instead of relying on
that proposition alone.  The three raw moment streams are built from the
same chart, action, and partition; scalar arithmetic then supplies the
connected modulus.  The resulting CReal is pinned back to the existing
spatial centered moment by the already-proved diagonal convergence.

This is a regulator-limit certificate for one fixed physical lag and one
fixed spatial presentation.  It is not a common Hilbert-carrier theorem,
uniform mass calibration, continuum QFT construction, or Clay conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedDiagonalCauchy

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm (radius)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (physicalTime unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter
  (paddedWidth recenter recenter_time)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialVariance (recenter_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialLimit
  (recenteredScalar spatialCauchy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm
  (spatialCenteredMoment originalConnected_diagonal_converges)
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator
  (connectedScalar)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
  (scalarAddCauchy scalarNegCauchy scalarMulCauchy)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (base H : Nat) (x y : PhysicalSpan base)
  (hx : radius x.val ≤ H)
  (hsmall : heatRatio w ≤ HalfPow.half)
  (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  (hb : 0 < base)

/-! The physical lag is an explicit parameter and is not the receding
boundary/time-buffer index. -/

def originalConnectedDiagonal (n : Nat) (hy : radius (physicalTime n y).val ≤ H)
    (r : Nat) : Q' :=
  connectedScalar hw0 hw1 (paddedWidth base r) r H
    (recenter r x) (physicalTime n (recenter r y)) r

private def rawSpatialReal (r : Nat → Q') (c : QCauchy r) : CReal where
  approx := r
  cauchy := fun epsilon he => ⟨c.M epsilon, c.bound epsilon he⟩

private def diagonalRawA (n : Nat) (hy : radius (physicalTime n y).val ≤ H) : CReal :=
  rawSpatialReal
    (fun r => recenteredScalar hw0 hw1 base H x (physicalTime n y) r r r)
    (spatialCauchy hw0 hw1 base H x (physicalTime n y) hx hy
      hsmall hd hs hb)

private def diagonalRawC : CReal :=
  rawSpatialReal
    (fun r => recenteredScalar hw0 hw1 base H x (unit base) r r r)
    (spatialCauchy hw0 hw1 base H x (unit base) hx (Nat.zero_le H)
      hsmall hd hs hb)

private def diagonalRawE (n : Nat) (hy : radius (physicalTime n y).val ≤ H) : CReal :=
  rawSpatialReal
    (fun r => recenteredScalar hw0 hw1 base H (unit base) (physicalTime n y) r r r)
    (spatialCauchy hw0 hw1 base H (unit base) (physicalTime n y)
      (Nat.zero_le H) hy hsmall hd hs hb)

private def diagonalRawACauchy (n : Nat) (hy : radius (physicalTime n y).val ≤ H) :
    QCauchy (diagonalRawA hw0 hw1 base H x y hx hsmall hd hs hb n hy).approx :=
  spatialCauchy hw0 hw1 base H x (physicalTime n y) hx hy hsmall hd hs hb

private def diagonalRawCCauchy : QCauchy (diagonalRawC hw0 hw1 base H x
    hx hsmall hd hs hb).approx :=
  spatialCauchy hw0 hw1 base H x (unit base) hx (Nat.zero_le H) hsmall hd hs hb

private def diagonalRawECauchy (n : Nat) (hy : radius (physicalTime n y).val ≤ H) :
    QCauchy (diagonalRawE hw0 hw1 base H y hsmall hd hs hb n hy).approx :=
  spatialCauchy hw0 hw1 base H (unit base) (physicalTime n y) (Nat.zero_le H) hy
    hsmall hd hs hb

/-- The CReal assembled from the three same-chart raw spatial moments. -/
def originalConnectedDiagonalLimit (n : Nat)
    (hy : radius (physicalTime n y).val ≤ H) : CReal :=
  CReal.sub
    (diagonalRawA hw0 hw1 base H x y hx hsmall hd hs hb n hy)
    (CReal.mul
      (diagonalRawC hw0 hw1 base H x hx hsmall hd hs hb)
      (diagonalRawE hw0 hw1 base H y hsmall hd hs hb n hy))

/-- Explicit `QCauchy` data for the assembled connected diagonal.  No
convergence proposition is eliminated to obtain this modulus. -/
def originalConnectedDiagonalCauchy (n : Nat)
    (hy : radius (physicalTime n y).val ≤ H) :
    QCauchy (originalConnectedDiagonalLimit hw0 hw1 base H x y hx
      hsmall hd hs hb n hy).approx := by
  exact scalarAddCauchy
    (diagonalRawA hw0 hw1 base H x y hx hsmall hd hs hb n hy)
    (CReal.neg
      (CReal.mul
        (diagonalRawC hw0 hw1 base H x hx hsmall hd hs hb)
        (diagonalRawE hw0 hw1 base H y hsmall hd hs hb n hy)))
    (diagonalRawACauchy hw0 hw1 base H x y hx hsmall hd hs hb n hy)
    (scalarNegCauchy
      (CReal.mul
        (diagonalRawC hw0 hw1 base H x hx hsmall hd hs hb)
        (diagonalRawE hw0 hw1 base H y hsmall hd hs hb n hy))
      (scalarMulCauchy
        (diagonalRawC hw0 hw1 base H x hx hsmall hd hs hb)
        (diagonalRawE hw0 hw1 base H y hsmall hd hs hb n hy)
        (diagonalRawCCauchy hw0 hw1 base H x hx hsmall hd hs hb)
        (diagonalRawECauchy hw0 hw1 base H y hsmall hd hs hb n hy)))

theorem originalConnectedDiagonal_limit_converges (n : Nat)
    (hy : radius (physicalTime n y).val ≤ H) :
    ConvergesTo
      (fun r => ofQ' (originalConnectedDiagonal hw0 hw1 base H x y n hy r))
      (originalConnectedDiagonalLimit hw0 hw1 base H x y hx
        hsmall hd hs hb n hy) := by
  have h := CReal.convergesTo_self
    (originalConnectedDiagonalLimit hw0 hw1 base H x y hx hsmall hd hs hb n hy)
  apply TrigAddCReal.convergesTo_congr_seq _ h
  intro r
  apply SumOfSquares.Equiv_of_approx_eqv
  intro k
  simp only [originalConnectedDiagonalLimit, originalConnectedDiagonal,
    diagonalRawA, diagonalRawC, diagonalRawE, rawSpatialReal,
    connectedScalar, recenteredScalar, recenter_time, recenter_unit]
  exact Q'.eqv_refl _

/-- The explicit modulus-bearing diagonal has the same limit as the existing
spatial centered moment. -/
theorem originalConnectedDiagonal_limit_pin (n : Nat)
    (hy : radius (physicalTime n y).val ≤ H) :
    Equiv
      (originalConnectedDiagonalLimit hw0 hw1 base H x y hx
        hsmall hd hs hb n hy)
      (spatialCenteredMoment hw0 hw1 base hsmall hd hs hb n x y) := by
  apply Equiv_of_limit_of_equal
      (fun r => by
      simp only [originalConnectedDiagonal, connectedScalar, recenteredScalar,
        recenter_time, recenter_unit]
      exact Equiv.refl _)
    (originalConnectedDiagonal_limit_converges hw0 hw1 base H x y hx
      hsmall hd hs hb n hy)
    (originalConnected_diagonal_converges hw0 hw1 base hsmall hd hs hb n H x y
      hx hy)

end YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedDiagonalCauchy

#print axioms
  YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedDiagonalCauchy.originalConnectedDiagonalCauchy
#print axioms
  YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedDiagonalCauchy.originalConnectedDiagonal_limit_converges
#print axioms
  YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedDiagonalCauchy.originalConnectedDiagonal_limit_pin
