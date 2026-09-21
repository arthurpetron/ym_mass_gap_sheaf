/-
# Constructed value/derivative certificates for quaternion products

These are finite polynomial interval witnesses, not analytic hypotheses.
Leibniz's rule keeps the original shared-variable products. Four coordinate
products per Hamilton component give a deliberately conservative cap.
The consumer is the actual four-link plaquette after a block permutation.
-/

import YMGap.Continuum.QuaternionHaarAngularCarrier
import YMGap.Continuum.QuaternionHaarCoordinateAngularInterval

namespace YMGap.Continuum.QuaternionHaarAngularProductBounds

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarCoordinateAngularInterval

/-- Two explicit interval certificates for the SAME polynomial and its derivative. -/
structure AngularBound (blocks i j : Nat) (p : RatPoly) (a b : Q') : Type where
  value : Interval blocks p a
  derivative : Interval blocks (angularDerivative i j p) b

variable {blocks i j : Nat}

namespace AngularBound

def add {p q : RatPoly} {a b c d : Q'} (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (P : AngularBound blocks i j p a b)
    (Q : AngularBound blocks i j q c d) : AngularBound blocks i j (polyAdd p q) (a+c) (b+d) where
  value := P.value.add Q.value
  derivative := Interval.ofCoeff
    (angularDerivative_supported hb hi hj (P.value.add Q.value).support)
    (angularDerivative_add i j p q) (P.derivative.add Q.derivative)

def neg {p : RatPoly} {a b : Q'} (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (P : AngularBound blocks i j p a b) : AngularBound blocks i j (polyNeg p) a b where
  value := intervalNeg P.value
  derivative := Interval.ofCoeff
    (angularDerivative_supported hb hi hj (intervalNeg P.value).support)
    (angularDerivative_neg i j p) (intervalNeg P.derivative)

def mul {p q : RatPoly} {a b c d : Q'} (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (P : AngularBound blocks i j p a b) (Q : AngularBound blocks i j q c d) :
    AngularBound blocks i j (polyMul p q) (a*c) (b*c+a*d) where
  value := P.value.mul Q.value
  derivative := Interval.ofCoeff
    (angularDerivative_supported hb hi hj (P.value.mul Q.value).support)
    (angularDerivative_mul i j p q)
    ((P.derivative.mul Q.value).add (P.value.mul Q.derivative))

def ofCarrier {p q : RatPoly} {a b : Q'} (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (hp : SupportedQuaternionBlocks blocks p) (h : HaarCarrierEqv blocks p q)
    (Q : AngularBound blocks i j q a b) : AngularBound blocks i j p a b where
  value := intervalOfCarrier hp h Q.value
  derivative := intervalOfCarrier (angularDerivative_supported hb hi hj hp)
    (angularDerivative_carrier hb hi hj h) Q.derivative

def changeCaps {p : RatPoly} {a b c d : Q'} (ha : Q'.eqv a c) (hb : Q'.eqv b d)
    (P : AngularBound blocks i j p a b) : AngularBound blocks i j p c d :=
  ⟨P.value.changeCap ha, P.derivative.changeCap hb⟩

def weaken {p : RatPoly} {a b c d : Q'} (P : AngularBound blocks i j p a b)
    (ha : a ≤ c) (hb : b ≤ d) : AngularBound blocks i j p c d :=
  ⟨P.value.weaken ha, P.derivative.weaken hb⟩

def zero : AngularBound blocks i j polyZero 0 0 := ⟨Interval.zero blocks, Interval.zero blocks⟩

def one (hb : 0 < blocks) (hi : i < 4) (hj : j < 4) :
    AngularBound blocks i j polyOne 1 0 :=
  ⟨Interval.one blocks, Interval.ofCoeff
    (angularDerivative_supported hb hi hj (supported_one blocks))
    (angularDerivative_independent_zero hi hj polyOne (hasQuaternionBlockDegree_one 0)) (Interval.zero blocks)⟩

def coordinate {coordinate : Nat} (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (hc : coordinate < 4*blocks) : AngularBound blocks i j (polyVar coordinate) 1 2 :=
  ⟨coordinateInterval hc, coordinateAngularInterval hb hi hj hc⟩

end AngularBound

/-- Componentwise certificates; all components retain the SAME quaternion word. -/
structure QuaternionBound (blocks i j : Nat) (p : PolyQuaternion) (a b : Q') : Type where
  scalar : AngularBound blocks i j p.scalar a b
  iPart : AngularBound blocks i j p.iPart a b
  jPart : AngularBound blocks i j p.jPart a b
  kPart : AngularBound blocks i j p.kPart a b

def fourCap (a : Q') : Q' := a+(a+(a+a))

namespace QuaternionBound

def one (hb : 0 < blocks) (hi : i < 4) (hj : j < 4) :
    QuaternionBound blocks i j PolyQuaternion.one 1 0 :=
  ⟨AngularBound.one hb hi hj,
    AngularBound.zero.weaken Q'.zero_le_one (Q'.le_refl' _),
    AngularBound.zero.weaken Q'.zero_le_one (Q'.le_refl' _),
    AngularBound.zero.weaken Q'.zero_le_one (Q'.le_refl' _)⟩

def coordinate {block : Nat} (hb : 0 < blocks) (hi : i < 4) (hj : j < 4) (hk : block < blocks) :
    QuaternionBound blocks i j (PolyQuaternion.coordinateVariable block) 1 2 :=
  ⟨AngularBound.coordinate hb hi hj (by omega), AngularBound.coordinate hb hi hj (by omega),
    AngularBound.coordinate hb hi hj (by omega), AngularBound.coordinate hb hi hj (by omega)⟩

def conj {p : PolyQuaternion} {a b : Q'} (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (P : QuaternionBound blocks i j p a b) : QuaternionBound blocks i j (PolyQuaternion.conj p) a b :=
  ⟨P.scalar, P.iPart.neg hb hi hj, P.jPart.neg hb hi hj, P.kPart.neg hb hi hj⟩

def mul {p q : PolyQuaternion} {a b c d : Q'} (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (P : QuaternionBound blocks i j p a b) (Q : QuaternionBound blocks i j q c d) :
    QuaternionBound blocks i j (PolyQuaternion.mul p q) (fourCap (a*c)) (fourCap (b*c+a*d)) :=
  ⟨(P.scalar.mul hb hi hj Q.scalar).add hb hi hj
      (((P.iPart.mul hb hi hj Q.iPart).add hb hi hj
        ((P.jPart.mul hb hi hj Q.jPart).add hb hi hj (P.kPart.mul hb hi hj Q.kPart))).neg hb hi hj),
    (P.scalar.mul hb hi hj Q.iPart).add hb hi hj ((P.iPart.mul hb hi hj Q.scalar).add hb hi hj
      ((P.jPart.mul hb hi hj Q.kPart).add hb hi hj ((P.kPart.mul hb hi hj Q.jPart).neg hb hi hj))),
    (P.scalar.mul hb hi hj Q.jPart).add hb hi hj ((P.jPart.mul hb hi hj Q.scalar).add hb hi hj
      ((P.kPart.mul hb hi hj Q.iPart).add hb hi hj ((P.iPart.mul hb hi hj Q.kPart).neg hb hi hj))),
    (P.scalar.mul hb hi hj Q.kPart).add hb hi hj ((P.kPart.mul hb hi hj Q.scalar).add hb hi hj
      ((P.iPart.mul hb hi hj Q.jPart).add hb hi hj ((P.jPart.mul hb hi hj Q.iPart).neg hb hi hj)))⟩

def ofPrefix {p q : PolyQuaternion} {a b : Q'} (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (hp : Supported blocks p) (h : QuaternionPrefixPolyQuaternionEqv blocks p q)
    (Q : QuaternionBound blocks i j q a b) : QuaternionBound blocks i j p a b :=
  ⟨AngularBound.ofCarrier hb hi hj hp.scalar (carrierOfPrefix hp.scalar Q.scalar.value.support h.scalar) Q.scalar,
    AngularBound.ofCarrier hb hi hj hp.iPart (carrierOfPrefix hp.iPart Q.iPart.value.support h.iPart) Q.iPart,
    AngularBound.ofCarrier hb hi hj hp.jPart (carrierOfPrefix hp.jPart Q.jPart.value.support h.jPart) Q.jPart,
    AngularBound.ofCarrier hb hi hj hp.kPart (carrierOfPrefix hp.kPart Q.kPart.value.support h.kPart) Q.kPart⟩

def weaken {p : PolyQuaternion} {a b c d : Q'} (P : QuaternionBound blocks i j p a b)
    (ha : a ≤ c) (hb : b ≤ d) : QuaternionBound blocks i j p c d :=
  ⟨P.scalar.weaken ha hb, P.iPart.weaken ha hb, P.jPart.weaken ha hb, P.kPart.weaken ha hb⟩

end QuaternionBound
end YMGap.Continuum.QuaternionHaarAngularProductBounds

#print axioms YMGap.Continuum.QuaternionHaarAngularProductBounds.AngularBound.add
#print axioms YMGap.Continuum.QuaternionHaarAngularProductBounds.AngularBound.neg
#print axioms YMGap.Continuum.QuaternionHaarAngularProductBounds.AngularBound.mul
#print axioms YMGap.Continuum.QuaternionHaarAngularProductBounds.AngularBound.ofCarrier
#print axioms YMGap.Continuum.QuaternionHaarAngularProductBounds.AngularBound.changeCaps
#print axioms YMGap.Continuum.QuaternionHaarAngularProductBounds.AngularBound.weaken
#print axioms YMGap.Continuum.QuaternionHaarAngularProductBounds.AngularBound.zero
#print axioms YMGap.Continuum.QuaternionHaarAngularProductBounds.AngularBound.one
#print axioms YMGap.Continuum.QuaternionHaarAngularProductBounds.AngularBound.coordinate
#print axioms YMGap.Continuum.QuaternionHaarAngularProductBounds.fourCap
#print axioms YMGap.Continuum.QuaternionHaarAngularProductBounds.QuaternionBound.one
#print axioms YMGap.Continuum.QuaternionHaarAngularProductBounds.QuaternionBound.coordinate
#print axioms YMGap.Continuum.QuaternionHaarAngularProductBounds.QuaternionBound.conj
#print axioms YMGap.Continuum.QuaternionHaarAngularProductBounds.QuaternionBound.mul
#print axioms YMGap.Continuum.QuaternionHaarAngularProductBounds.QuaternionBound.ofPrefix
#print axioms YMGap.Continuum.QuaternionHaarAngularProductBounds.QuaternionBound.weaken
