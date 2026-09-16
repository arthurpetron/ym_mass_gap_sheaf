/-
# The reusable completion is the already proved actual spatial pairing

Every generic dense-pairing input is supplied by an existing theorem for
the actual spatial limiting form. Both scalar constructions converge along
the SAME sequence of pairings of the supplied Cauchy representatives.
Uniqueness therefore identifies their real quotients even though their
computed inner approximation moduli can differ. The carrier is literally
the existing SpatialCompletion, with no representative selection or change
to the spatial limiting form, distance or physical observable algebra.
-/

import YMGap.Continuum.CRealSeminormPairingCompletion
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialGenericPairingPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime (SpatialCompletion)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (base : Nat)
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0 < base)

local notation "D" => spatialSeminorm hw0 hw1 base hsmall hd hs hb

/-- No new analytic premise: all four fields are checked spatial theorems. -/
def pairingData : CRealSeminormPairingCompletion.PairingData D where
  pairing := spatialPairing hw0 hw1 base hsmall hd hs hb
  pairingCauchy := spatialPairingCauchy hw0 hw1 base hsmall hd hs hb
  diagonal_anchor_bound :=
    BF4ExactSlabFixedSpatialSpatialPairingBounds.diagonal_anchor_bound hw0 hw1 base hsmall hd hs hb
  pairing_close :=
    BF4ExactSlabFixedSpatialSpatialPairingContinuity.pairing_close hw0 hw1 base hsmall hd hs hb

theorem representativeInner_pin (X Y : (D).Cauchy) :
    Equiv
      (CRealSeminormPairingCompletion.representativeInner
        (pairingData hw0 hw1 base hsmall hd hs hb) X Y)
      (BF4ExactSlabFixedSpatialSpatialPairingLimit.representativeInner
        hw0 hw1 base hsmall hd hs hb X Y) :=
  CRealSeminormPairingCompletion.representativeInner_unique
    (pairingData hw0 hw1 base hsmall hd hs hb) X Y _
    (BF4ExactSlabFixedSpatialSpatialPairingLimit.pairSequence_converges
      hw0 hw1 base hsmall hd hs hb X Y)

/-- Equality on the SAME existing quotient, not an unidentified isomorphism. -/
theorem completedInner_pin (x y : SpatialCompletion hw0 hw1 base hsmall hd hs hb) :
    CRealSeminormPairingCompletion.completedInner
        (pairingData hw0 hw1 base hsmall hd hs hb) x y =
      BF4ExactSlabFixedSpatialSpatialCompletedInner.completedInner
        hw0 hw1 base hsmall hd hs hb x y := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeInner_pin hw0 hw1 base hsmall hd hs hb X Y)

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialGenericPairingPin

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialGenericPairingPin.pairingData
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialGenericPairingPin.representativeInner_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialGenericPairingPin.completedInner_pin
