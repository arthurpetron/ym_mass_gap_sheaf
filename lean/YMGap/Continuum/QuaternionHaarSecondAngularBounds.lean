/-
# Constructed second angular-derivative intervals

The derivative itself has a value/derivative certificate, so Leibniz's
rule yields second-derivative bounds without any analytic assumption.
Coordinate bases are proved using the actual padded Haar-carrier identity.
The quaternion constructors retain all four shared-variable channels.
-/

import YMGap.Continuum.QuaternionHaarAngularProductBounds
import YMGap.Continuum.QuaternionHaarSignedInterval

namespace YMGap.Continuum.QuaternionHaarSecondAngularBounds

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSignedInterval
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarCoordinateAngularInterval
open YMGap.Continuum.QuaternionHaarAngularProductBounds

/-- Signed coefficients remain in the polynomial; only the interval cap uses abs. -/
def angularSmul {blocks i j : Nat} {p : RatPoly} {a b : Q'}
    (hb : 0 < blocks) (hi : i < 4) (hj : j < 4) (c : Q')
    (P : AngularBound blocks i j p a b) :
    AngularBound blocks i j (polySmul c p) (Q'.abs c*a) (Q'.abs c*b) where
  value := QuaternionHaarSignedInterval.Interval.smul_abs c P.value
  derivative := Interval.ofCoeff
    (angularDerivative_supported hb hi hj (QuaternionHaarSignedInterval.Interval.smul_abs c P.value).support)
    (angularDerivative_smul i j c p) (QuaternionHaarSignedInterval.Interval.smul_abs c P.derivative)

/-- Three actual intervals, with the last two organized for direct Leibniz use. -/
structure SecondBound (blocks i j : Nat) (p : RatPoly) (a b c : Q') : Type where
  value : Interval blocks p a
  derivative : AngularBound blocks i j (angularDerivative i j p) b c

variable {blocks i j : Nat}

namespace SecondBound

def first {p : RatPoly} {a b c : Q'} (P : SecondBound blocks i j p a b c) :
    AngularBound blocks i j p a b := ⟨P.value, P.derivative.value⟩

def add {p q : RatPoly} {a b c d e f : Q'} (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (P : SecondBound blocks i j p a b c) (Q : SecondBound blocks i j q d e f) :
    SecondBound blocks i j (polyAdd p q) (a+d) (b+e) (c+f) where
  value := P.value.add Q.value
  derivative := AngularBound.ofCarrier hb hi hj
    (angularDerivative_supported hb hi hj (P.value.add Q.value).support)
    (RatPolyCoeffEqv.haarCarrier (angularDerivative_add i j p q))
    (P.derivative.add hb hi hj Q.derivative)

def neg {p : RatPoly} {a b c : Q'} (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (P : SecondBound blocks i j p a b c) : SecondBound blocks i j (polyNeg p) a b c where
  value := intervalNeg P.value
  derivative := AngularBound.ofCarrier hb hi hj
    (angularDerivative_supported hb hi hj (intervalNeg P.value).support)
    (RatPolyCoeffEqv.haarCarrier (angularDerivative_neg i j p))
    (P.derivative.neg hb hi hj)

/-- Both mixed Leibniz terms are retained, including shared variables. -/
def mul {p q : RatPoly} {a b c d e f : Q'} (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (P : SecondBound blocks i j p a b c) (Q : SecondBound blocks i j q d e f) :
    SecondBound blocks i j (polyMul p q) (a*d) (b*d+a*e) ((c*d+b*e)+(b*e+a*f)) where
  value := P.value.mul Q.value
  derivative := AngularBound.ofCarrier hb hi hj
    (angularDerivative_supported hb hi hj (P.value.mul Q.value).support)
    (RatPolyCoeffEqv.haarCarrier (angularDerivative_mul i j p q))
    ((P.derivative.mul hb hi hj Q.first).add hb hi hj (P.first.mul hb hi hj Q.derivative))

def ofCarrier {p q : RatPoly} {a b c : Q'} (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (hp : SupportedQuaternionBlocks blocks p) (h : HaarCarrierEqv blocks p q)
    (Q : SecondBound blocks i j q a b c) : SecondBound blocks i j p a b c where
  value := intervalOfCarrier hp h Q.value
  derivative := AngularBound.ofCarrier hb hi hj (angularDerivative_supported hb hi hj hp)
    (angularDerivative_carrier hb hi hj h) Q.derivative

def weaken {p : RatPoly} {a b c d e f : Q'} (P : SecondBound blocks i j p a b c)
    (ha : a ≤ d) (hb : b ≤ e) (hc : c ≤ f) : SecondBound blocks i j p d e f :=
  ⟨P.value.weaken ha, P.derivative.weaken hb hc⟩

def zero : SecondBound blocks i j polyZero 0 0 0 :=
  ⟨Interval.zero blocks, AngularBound.zero⟩

def one (hb : 0 < blocks) (hi : i < 4) (hj : j < 4) :
    SecondBound blocks i j polyOne 1 0 0 :=
  ⟨Interval.one blocks, AngularBound.ofCarrier hb hi hj
    (angularDerivative_supported hb hi hj (supported_one blocks))
    (RatPolyCoeffEqv.haarCarrier (angularDerivative_independent_zero hi hj polyOne (hasQuaternionBlockDegree_one 0)))
    AngularBound.zero⟩

private def coordinateFactor (factor derivative coordinate : Nat)
    (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (hf : factor < 4) (hd : derivative < 4) (hc : coordinate < 4*blocks) :
    AngularBound blocks i j (polyMul (polyVar factor) (ratDerivative derivative (polyVar coordinate))) 1 2 := by
  have hfactor : factor < 4*blocks := by omega
  have hs : SupportedQuaternionBlocks blocks
      (polyMul (polyVar factor) (ratDerivative derivative (polyVar coordinate))) :=
    supported_polyMul (coordinateInterval hfactor).support
    (ratDerivative_supported (coordinateInterval hc).support)
  by_cases heq : derivative = coordinate
  · subst coordinate
    exact AngularBound.ofCarrier hb hi hj hs
      (derivativeFactor_self_carrier blocks factor derivative hb hf hd)
      (AngularBound.coordinate hb hi hj hfactor)
  · exact AngularBound.ofCarrier hb hi hj hs
      (RatPolyCoeffEqv.haarCarrier (((ratDerivative_polyVar_ne derivative coordinate heq).mul_left _).trans
        (RatPolyCoeffEqv.mul_zero_right _)))
      (AngularBound.zero.weaken (by decide) (by decide))

/-- Every original supported coordinate has caps (1,2,4), including coordinates
outside the differentiated head. No unproved second derivative premise. -/
def coordinate {coordinate : Nat} (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (hc : coordinate < 4*blocks) : SecondBound blocks i j (polyVar coordinate) 1 2 4 := by
  let L := coordinateFactor i j coordinate hb hi hj hi hj hc
  let R := coordinateFactor j i coordinate hb hi hj hj hi hc
  let right := polyMul (polyVar j) (ratDerivative i (polyVar coordinate))
  have N : AngularBound blocks i j (polySmul (-1) right) 1 2 :=
    AngularBound.ofCarrier hb hi hj (polySmul_supported R.value.support (-1))
      (RatPolyCoeffEqv.haarCarrier (neg_smul right).symm) (R.neg hb hi hj)
  exact ⟨coordinateInterval hc, (L.add hb hi hj N).changeCaps (by decide) (by decide)⟩

end SecondBound

structure QuaternionSecondBound (blocks i j : Nat) (p : PolyQuaternion) (a b c : Q') : Type where
  scalar : SecondBound blocks i j p.scalar a b c
  iPart : SecondBound blocks i j p.iPart a b c
  jPart : SecondBound blocks i j p.jPart a b c
  kPart : SecondBound blocks i j p.kPart a b c

namespace QuaternionSecondBound

def one (hb : 0 < blocks) (hi : i < 4) (hj : j < 4) :
    QuaternionSecondBound blocks i j PolyQuaternion.one 1 0 0 :=
  ⟨SecondBound.one hb hi hj, SecondBound.zero.weaken (by decide) (by decide) (by decide),
    SecondBound.zero.weaken (by decide) (by decide) (by decide),
    SecondBound.zero.weaken (by decide) (by decide) (by decide)⟩

def coordinate {block : Nat} (hb : 0 < blocks) (hi : i < 4) (hj : j < 4) (hk : block < blocks) :
    QuaternionSecondBound blocks i j (PolyQuaternion.coordinateVariable block) 1 2 4 :=
  ⟨SecondBound.coordinate hb hi hj (by omega), SecondBound.coordinate hb hi hj (by omega),
    SecondBound.coordinate hb hi hj (by omega), SecondBound.coordinate hb hi hj (by omega)⟩

def conj {p : PolyQuaternion} {a b c : Q'} (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (P : QuaternionSecondBound blocks i j p a b c) :
    QuaternionSecondBound blocks i j (PolyQuaternion.conj p) a b c :=
  ⟨P.scalar, P.iPart.neg hb hi hj, P.jPart.neg hb hi hj, P.kPart.neg hb hi hj⟩

def mul {p q : PolyQuaternion} {a b c d e f : Q'} (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (P : QuaternionSecondBound blocks i j p a b c) (Q : QuaternionSecondBound blocks i j q d e f) :
    QuaternionSecondBound blocks i j (PolyQuaternion.mul p q)
      (fourCap (a*d)) (fourCap (b*d+a*e)) (fourCap ((c*d+b*e)+(b*e+a*f))) :=
  ⟨(P.scalar.mul hb hi hj Q.scalar).add hb hi hj
      (((P.iPart.mul hb hi hj Q.iPart).add hb hi hj
        ((P.jPart.mul hb hi hj Q.jPart).add hb hi hj (P.kPart.mul hb hi hj Q.kPart))).neg hb hi hj),
    (P.scalar.mul hb hi hj Q.iPart).add hb hi hj ((P.iPart.mul hb hi hj Q.scalar).add hb hi hj
      ((P.jPart.mul hb hi hj Q.kPart).add hb hi hj ((P.kPart.mul hb hi hj Q.jPart).neg hb hi hj))),
    (P.scalar.mul hb hi hj Q.jPart).add hb hi hj ((P.jPart.mul hb hi hj Q.scalar).add hb hi hj
      ((P.kPart.mul hb hi hj Q.iPart).add hb hi hj ((P.iPart.mul hb hi hj Q.kPart).neg hb hi hj))),
    (P.scalar.mul hb hi hj Q.kPart).add hb hi hj ((P.kPart.mul hb hi hj Q.scalar).add hb hi hj
      ((P.iPart.mul hb hi hj Q.jPart).add hb hi hj ((P.jPart.mul hb hi hj Q.iPart).neg hb hi hj)))⟩

def ofPrefix {p q : PolyQuaternion} {a b c : Q'} (hb : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (hp : Supported blocks p) (h : QuaternionPrefixPolyQuaternionEqv blocks p q)
    (Q : QuaternionSecondBound blocks i j q a b c) : QuaternionSecondBound blocks i j p a b c :=
  ⟨SecondBound.ofCarrier hb hi hj hp.scalar (carrierOfPrefix hp.scalar Q.scalar.value.support h.scalar) Q.scalar,
    SecondBound.ofCarrier hb hi hj hp.iPart (carrierOfPrefix hp.iPart Q.iPart.value.support h.iPart) Q.iPart,
    SecondBound.ofCarrier hb hi hj hp.jPart (carrierOfPrefix hp.jPart Q.jPart.value.support h.jPart) Q.jPart,
    SecondBound.ofCarrier hb hi hj hp.kPart (carrierOfPrefix hp.kPart Q.kPart.value.support h.kPart) Q.kPart⟩

def weaken {p : PolyQuaternion} {a b c d e f : Q'} (P : QuaternionSecondBound blocks i j p a b c)
    (ha : a ≤ d) (hb : b ≤ e) (hc : c ≤ f) : QuaternionSecondBound blocks i j p d e f :=
  ⟨P.scalar.weaken ha hb hc, P.iPart.weaken ha hb hc, P.jPart.weaken ha hb hc, P.kPart.weaken ha hb hc⟩

end QuaternionSecondBound
end YMGap.Continuum.QuaternionHaarSecondAngularBounds

#print axioms YMGap.Continuum.QuaternionHaarSecondAngularBounds.angularSmul
#print axioms YMGap.Continuum.QuaternionHaarSecondAngularBounds.SecondBound.first
#print axioms YMGap.Continuum.QuaternionHaarSecondAngularBounds.SecondBound.add
#print axioms YMGap.Continuum.QuaternionHaarSecondAngularBounds.SecondBound.neg
#print axioms YMGap.Continuum.QuaternionHaarSecondAngularBounds.SecondBound.mul
#print axioms YMGap.Continuum.QuaternionHaarSecondAngularBounds.SecondBound.ofCarrier
#print axioms YMGap.Continuum.QuaternionHaarSecondAngularBounds.SecondBound.weaken
#print axioms YMGap.Continuum.QuaternionHaarSecondAngularBounds.SecondBound.zero
#print axioms YMGap.Continuum.QuaternionHaarSecondAngularBounds.SecondBound.one
#print axioms YMGap.Continuum.QuaternionHaarSecondAngularBounds.SecondBound.coordinate
#print axioms YMGap.Continuum.QuaternionHaarSecondAngularBounds.QuaternionSecondBound.one
#print axioms YMGap.Continuum.QuaternionHaarSecondAngularBounds.QuaternionSecondBound.coordinate
#print axioms YMGap.Continuum.QuaternionHaarSecondAngularBounds.QuaternionSecondBound.conj
#print axioms YMGap.Continuum.QuaternionHaarSecondAngularBounds.QuaternionSecondBound.mul
#print axioms YMGap.Continuum.QuaternionHaarSecondAngularBounds.QuaternionSecondBound.ofPrefix
#print axioms YMGap.Continuum.QuaternionHaarSecondAngularBounds.QuaternionSecondBound.weaken
