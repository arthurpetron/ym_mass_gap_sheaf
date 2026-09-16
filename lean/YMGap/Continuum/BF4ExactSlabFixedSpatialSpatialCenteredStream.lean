/-
# Explicit centered streams for the actual spatial limiting completion

Subtract the rational approximations of the spatial mean from the original
physical presentation. The coefficient-square identity and the existing
clipped scalar tolerance give a computed squared-distance Cauchy modulus.
No real scalar action, representative choice or square root is required.

The vector lives in SpatialCompletion for the SAME limiting form and
physical time map. These data do not assert metric completeness or a new
continuum state. All analytic small-nome guards remain explicit.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenterAlgebra
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredStream

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenterAlgebra (centerApprox)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream
  (centerTolerance centerTolerance_positive coefficient_square_bound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenterAlgebra
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (base : Nat)
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0 < base)

local notation "D" => spatialSeminorm hw0 hw1 base hsmall hd hs hb

/-- The actual spatial mean, not the mean in any finite-width carrier. -/
def mean (x : PhysicalSpan base) : CReal :=
  spatialPairing hw0 hw1 base hsmall hd hs hb x (unit base)

def meanCauchy (x : PhysicalSpan base) :
    QCauchy (mean hw0 hw1 base hsmall hd hs hb x).approx :=
  spatialPairingCauchy hw0 hw1 base hsmall hd hs hb x (unit base)

/-- Retain the displayed scalar modulus as computational data. -/
def centeredRate (x : PhysicalSpan base) (epsilon : Q') : Nat :=
  (meanCauchy hw0 hw1 base hsmall hd hs hb x).M (centerTolerance epsilon)

def centeredStream (x : PhysicalSpan base) : (D).Cauchy where
  seq n := centerApprox x ((mean hw0 hw1 base hsmall hd hs hb x).approx n)
  modulus := centeredRate hw0 hw1 base hsmall hd hs hb x
  isCauchy := by
    intro epsilon he m n hm hn
    have h := (meanCauchy hw0 hw1 base hsmall hd hs hb x).bound
      (centerTolerance epsilon) (centerTolerance_positive he) m n hm hn
    exact leEv_trans (leEv_of_equiv (centerApprox_distance hw0 hw1 base hsmall hd hs hb x _ _))
      (leEv_of_le (ofQ'_le_ofQ' (coefficient_square_bound he h)))

/-- A vector in the existing spatial Cauchy quotient, with explicit representative. -/
def centeredVector (x : PhysicalSpan base) : SpatialCompletion hw0 hw1 base hsmall hd hs hb :=
  Quotient.mk (D).completionSetoid (centeredStream hw0 hw1 base hsmall hd hs hb x)

theorem centeredStream_seq (x : PhysicalSpan base) (n : Nat) :
    (centeredStream hw0 hw1 base hsmall hd hs hb x).seq n =
      centerApprox x ((mean hw0 hw1 base hsmall hd hs hb x).approx n) := rfl

theorem centeredStream_modulus (x : PhysicalSpan base) :
    (centeredStream hw0 hw1 base hsmall hd hs hb x).modulus =
      centeredRate hw0 hw1 base hsmall hd hs hb x := rfl

theorem mean_approximations_converge (x : PhysicalSpan base) :
    ConvergesTo (fun n => ofQ' ((mean hw0 hw1 base hsmall hd hs hb x).approx n))
      (mean hw0 hw1 base hsmall hd hs hb x) := by
  intro epsilon he
  let c := meanCauchy hw0 hw1 base hsmall hd hs hb x
  exact ⟨c.M epsilon, fun n hn => ⟨c.M epsilon, fun k hk => c.bound epsilon he n k hn hk⟩⟩

#print axioms mean
#print axioms meanCauchy
#print axioms centeredRate
#print axioms centeredStream
#print axioms centeredVector
#print axioms centeredStream_seq
#print axioms centeredStream_modulus
#print axioms mean_approximations_converge

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredStream
