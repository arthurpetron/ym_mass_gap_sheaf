/-
# Two-plane angular intervals for an original four-link plaquette

The original corrected-slab plaquette is a four-factor quaternion word.
The already constructed two-plane coordinate jets give an absolute mixed
angular interval for any two supported quaternion-block planes, including
equal blocks or overlapping planes. Identity fallback links are retained.
No action, nome, stage, or conditional measure enters this construction.
-/

import YMGap.Continuum.SU2QuaternionRelativeHeatSecondAngularBound
import YMGap.Continuum.BF4ExactSlabPlaquetteSecondAngularInterval

namespace YMGap.Continuum.BF4ExactSlabPlaquetteMixedAngularInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarAngularProductBounds (fourCap)
open YMGap.Continuum.SU2QuaternionRelativeHeatSecondAngularBound
  (MixedJet coordinateJet)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

private theorem zeroAngular (i j : Nat) :
    RatPolyCoeffEqv (angularDerivative i j polyZero) polyZero := by
  change RatPolyCoeffEqv polyZero polyZero
  exact RatPolyCoeffEqv.refl _

private def zeroJet {B oi oj ii ij : Nat} :
    MixedJet B oi oj ii ij polyZero 0 0 0 0 := by
  exact ⟨Interval.zero B,
    by simpa only [show angularDerivative ii ij polyZero = polyZero from rfl] using
      (Interval.zero B),
    by simpa only [show angularDerivative oi oj polyZero = polyZero from rfl] using
      (Interval.zero B),
    by simpa only [show angularDerivative ii ij polyZero = polyZero from rfl,
      show angularDerivative oi oj polyZero = polyZero from rfl] using
      (Interval.zero B)⟩

private def oneJet {B ob ib oi oj ii ij : Nat}
    (hob : ob < B) (hib : ib < B)
    (hoi : oi < 4) (hoj : oj < 4) (hii : ii < 4) (hij : ij < 4) :
    MixedJet B (4*ob+oi) (4*ob+oj) (4*ib+ii) (4*ib+ij)
      polyOne 1 0 0 0 := by
  have hxi : 4*ob+oi < 4*B := by omega
  have hxj : 4*ob+oj < 4*B := by omega
  have hyi : 4*ib+ii < 4*B := by omega
  have hyj : 4*ib+ij < 4*B := by omega
  have hzero := Interval.zero B
  have hinner := angularDerivative_one (4*ib+ii) (4*ib+ij)
  have houter := angularDerivative_one (4*ob+oi) (4*ob+oj)
  have hmixed : RatPolyCoeffEqv
      (angularDerivative (4*ob+oi) (4*ob+oj)
        (angularDerivative (4*ib+ii) (4*ib+ij) polyOne)) polyZero :=
    (angularDerivative_congr _ _ hinner).trans
      (zeroAngular (4*ob+oi) (4*ob+oj))
  exact ⟨Interval.one B,
    Interval.ofCoeff (angularDerivative_supported_at hyi hyj (supported_one B))
      hinner hzero,
    Interval.ofCoeff (angularDerivative_supported_at hxi hxj (supported_one B))
      houter hzero,
    Interval.ofCoeff
      (angularDerivative_supported_at hxi hxj
        (angularDerivative_supported_at hyi hyj (supported_one B)))
      hmixed hzero⟩

private def jetWeaken {B oi oj ii ij : Nat} {p : RatPoly}
    {a b c d e f g h : Q'}
    (P : MixedJet B oi oj ii ij p a b c d)
    (ha : a ≤ e) (hb : b ≤ f) (hc : c ≤ g) (hd : d ≤ h) :
    MixedJet B oi oj ii ij p e f g h :=
  ⟨P.value.weaken ha, P.inner.weaken hb,
    P.outer.weaken hc, P.mixed.weaken hd⟩

private def jetChangeCaps {B oi oj ii ij : Nat} {p : RatPoly}
    {a b c d e f g h : Q'}
    (P : MixedJet B oi oj ii ij p a b c d)
    (ha : Q'.eqv a e) (hb : Q'.eqv b f)
    (hc : Q'.eqv c g) (hd : Q'.eqv d h) :
    MixedJet B oi oj ii ij p e f g h :=
  ⟨P.value.changeCap ha, P.inner.changeCap hb,
    P.outer.changeCap hc, P.mixed.changeCap hd⟩

/-- Four componentwise two-plane jets for one quaternion polynomial. -/
private structure QuaternionMixedJet (B oi oj ii ij : Nat)
    (p : PolyQuaternion) (a b c d : Q') : Type where
  scalar : MixedJet B oi oj ii ij p.scalar a b c d
  iPart : MixedJet B oi oj ii ij p.iPart a b c d
  jPart : MixedJet B oi oj ii ij p.jPart a b c d
  kPart : MixedJet B oi oj ii ij p.kPart a b c d

private def QuaternionMixedJet.one {B ob ib oi oj ii ij : Nat}
    (hob : ob < B) (hib : ib < B)
    (hoi : oi < 4) (hoj : oj < 4) (hii : ii < 4) (hij : ij < 4) :
    QuaternionMixedJet B (4*ob+oi) (4*ob+oj) (4*ib+ii) (4*ib+ij)
      PolyQuaternion.one 1 0 0 0 :=
  ⟨oneJet hob hib hoi hoj hii hij,
    jetWeaken zeroJet (by decide) (by decide) (by decide) (by decide),
    jetWeaken zeroJet (by decide) (by decide) (by decide) (by decide),
    jetWeaken zeroJet (by decide) (by decide) (by decide) (by decide)⟩

private def QuaternionMixedJet.coordinate {B ob ib oi oj ii ij block : Nat}
    (hob : ob < B) (hib : ib < B)
    (hoi : oi < 4) (hoj : oj < 4) (hii : ii < 4) (hij : ij < 4)
    (hblock : block < B) :
    QuaternionMixedJet B (4*ob+oi) (4*ob+oj) (4*ib+ii) (4*ib+ij)
      (PolyQuaternion.coordinateVariable block) 1 2 2 4 :=
  ⟨coordinateJet hob hib hoi hoj hii hij (by omega),
    coordinateJet hob hib hoi hoj hii hij (by omega),
    coordinateJet hob hib hoi hoj hii hij (by omega),
    coordinateJet hob hib hoi hoj hii hij (by omega)⟩

private def QuaternionMixedJet.conj {B oi oj ii ij : Nat}
    {p : PolyQuaternion} {a b c d : Q'}
    (hoi : oi < 4*B) (hoj : oj < 4*B)
    (hii : ii < 4*B) (hij : ij < 4*B)
    (P : QuaternionMixedJet B oi oj ii ij p a b c d) :
    QuaternionMixedJet B oi oj ii ij (PolyQuaternion.conj p) a b c d :=
  ⟨P.scalar, P.iPart.neg hoi hoj hii hij,
    P.jPart.neg hoi hoj hii hij, P.kPart.neg hoi hoj hii hij⟩

private def QuaternionMixedJet.weaken {B oi oj ii ij : Nat}
    {p : PolyQuaternion} {a b c d e f g h : Q'}
    (P : QuaternionMixedJet B oi oj ii ij p a b c d)
    (ha : a ≤ e) (hb : b ≤ f) (hc : c ≤ g) (hd : d ≤ h) :
    QuaternionMixedJet B oi oj ii ij p e f g h :=
  ⟨jetWeaken P.scalar ha hb hc hd,
    jetWeaken P.iPart ha hb hc hd,
    jetWeaken P.jPart ha hb hc hd,
    jetWeaken P.kPart ha hb hc hd⟩

/-- Quaternion multiplication propagates all four signed channels and all
four ordered Leibniz terms of the mixed derivative. -/
private def QuaternionMixedJet.mul {B oi oj ii ij : Nat}
    {p q : PolyQuaternion} {a b c d e f g h : Q'}
    (hoi : oi < 4*B) (hoj : oj < 4*B)
    (hii : ii < 4*B) (hij : ij < 4*B)
    (P : QuaternionMixedJet B oi oj ii ij p a b c d)
    (Q : QuaternionMixedJet B oi oj ii ij q e f g h) :
    QuaternionMixedJet B oi oj ii ij (PolyQuaternion.mul p q)
      (fourCap (a*e)) (fourCap (b*e+a*f))
      (fourCap (c*e+a*g))
      (fourCap ((d*e+b*g)+(c*f+a*h))) :=
  ⟨(P.scalar.mul hoi hoj hii hij Q.scalar).add hoi hoj hii hij
      (((P.iPart.mul hoi hoj hii hij Q.iPart).add hoi hoj hii hij
        ((P.jPart.mul hoi hoj hii hij Q.jPart).add hoi hoj hii hij
          (P.kPart.mul hoi hoj hii hij Q.kPart))).neg hoi hoj hii hij),
    (P.scalar.mul hoi hoj hii hij Q.iPart).add hoi hoj hii hij
      ((P.iPart.mul hoi hoj hii hij Q.scalar).add hoi hoj hii hij
        ((P.jPart.mul hoi hoj hii hij Q.kPart).add hoi hoj hii hij
          ((P.kPart.mul hoi hoj hii hij Q.jPart).neg hoi hoj hii hij))),
    (P.scalar.mul hoi hoj hii hij Q.jPart).add hoi hoj hii hij
      ((P.jPart.mul hoi hoj hii hij Q.scalar).add hoi hoj hii hij
        ((P.kPart.mul hoi hoj hii hij Q.iPart).add hoi hoj hii hij
          ((P.iPart.mul hoi hoj hii hij Q.kPart).neg hoi hoj hii hij))),
    (P.scalar.mul hoi hoj hii hij Q.kPart).add hoi hoj hii hij
      ((P.kPart.mul hoi hoj hii hij Q.scalar).add hoi hoj hii hij
        ((P.iPart.mul hoi hoj hii hij Q.jPart).add hoi hoj hii hij
          ((P.jPart.mul hoi hoj hii hij Q.iPart).neg hoi hoj hii hij)))⟩

private def correctedLinkJet {extent ob ib oi oj ii ij : Nat}
    (hob : ob < blocks extent) (hib : ib < blocks extent)
    (hoi : oi < 4) (hoj : oj < 4) (hii : ii < 4) (hij : ij < 4)
    (link : Z4Link) :
    QuaternionMixedJet (blocks extent)
      (4*ob+oi) (4*ob+oj) (4*ib+ii) (4*ib+ij)
      (correctedSlabLinkPolynomial extent link) 1 2 2 4 := by
  by_cases hl : link ∈ boundaryCompleteSlabLinks extent
  · rw [correctedSlabLinkPolynomial_of_mem hl]
    exact QuaternionMixedJet.coordinate hob hib hoi hoj hii hij
      (List.idxOf_lt_length_of_mem hl)
  · rw [correctedSlabLinkPolynomial_of_not_mem hl]
    exact (QuaternionMixedJet.one hob hib hoi hoj hii hij).weaken
      (Q'.le_refl' _) (by decide) (by decide) (by decide)

private def orientedLinkJet {extent ob ib oi oj ii ij : Nat}
    (hob : ob < blocks extent) (hib : ib < blocks extent)
    (hoi : oi < 4) (hoj : oj < 4) (hii : ii < 4) (hij : ij < 4)
    (entry : OrientedBF4Link) :
    QuaternionMixedJet (blocks extent)
      (4*ob+oi) (4*ob+oj) (4*ib+ii) (4*ib+ij)
      (orientedCorrectedSlabLinkPolynomial extent entry) 1 2 2 4 := by
  unfold orientedCorrectedSlabLinkPolynomial
  split
  · exact (correctedLinkJet hob hib hoi hoj hii hij entry.link).conj
      (by omega) (by omega) (by omega) (by omega)
  · exact correctedLinkJet hob hib hoi hoj hii hij entry.link

/-- The ORIGINAL four-link scalar has dimension-independent value, first,
and mixed angular caps in any two possibly overlapping block planes. -/
def plaquetteMixedAngularJet {ob ib oi oj ii ij : Nat}
    (extent : Nat) (hob : ob < blocks extent) (hib : ib < blocks extent)
    (hoi : oi < 4) (hoj : oj < 4) (hii : ii < 4) (hij : ij < 4)
    (face : Z4Plaq) :
    MixedJet (blocks extent) (4*ob+oi) (4*ob+oj) (4*ib+ii) (4*ib+ij)
      (correctedSlabPlaquettePolynomial extent face).scalar
      256 2048 2048 16384 := by
  let a := (dirsOf face.2).1
  let b := (dirsOf face.2).2
  let e0 : OrientedBF4Link := ⟨(face.1, a), false⟩
  let e1 : OrientedBF4Link := ⟨(addE face.1 a, b), false⟩
  let e2 : OrientedBF4Link := ⟨(addE face.1 b, a), true⟩
  let e3 : OrientedBF4Link := ⟨(face.1, b), true⟩
  have hword : correctedSlabPlaquettePolynomial extent face =
      PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul
        PolyQuaternion.one
        (orientedCorrectedSlabLinkPolynomial extent e0))
        (orientedCorrectedSlabLinkPolynomial extent e1))
        (orientedCorrectedSlabLinkPolynomial extent e2))
        (orientedCorrectedSlabLinkPolynomial extent e3) := by
    simp only [correctedSlabPlaquettePolynomial, orientedPlaquetteBoundary,
      List.foldl_cons, List.foldl_nil, a, b, e0, e1, e2, e3]
  rw [hword]
  have hxi : 4*ob+oi < 4*blocks extent := by omega
  have hxj : 4*ob+oj < 4*blocks extent := by omega
  have hyi : 4*ib+ii < 4*blocks extent := by omega
  have hyj : 4*ib+ij < 4*blocks extent := by omega
  let O := QuaternionMixedJet.one hob hib hoi hoj hii hij
  let A := orientedLinkJet hob hib hoi hoj hii hij e0
  let B := orientedLinkJet hob hib hoi hoj hii hij e1
  let C := orientedLinkJet hob hib hoi hoj hii hij e2
  let D := orientedLinkJet hob hib hoi hoj hii hij e3
  have H := ((((O.mul hxi hxj hyi hyj A).mul hxi hxj hyi hyj B).mul
    hxi hxj hyi hyj C).mul hxi hxj hyi hyj D)
  exact jetChangeCaps H.scalar (by decide) (by decide) (by decide) (by decide)

/-- The mixed component alone, suitable for direct finite-interval consumers. -/
def plaquetteMixedAngularInterval {ob ib oi oj ii ij : Nat}
    (extent : Nat) (hob : ob < blocks extent) (hib : ib < blocks extent)
    (hoi : oi < 4) (hoj : oj < 4) (hii : ii < 4) (hij : ij < 4)
    (face : Z4Plaq) :
    Interval (blocks extent)
      (angularDerivative (4*ob+oi) (4*ob+oj)
        (angularDerivative (4*ib+ii) (4*ib+ij)
          (correctedSlabPlaquettePolynomial extent face).scalar)) 16384 :=
  (plaquetteMixedAngularJet extent hob hib hoi hoj hii hij face).mixed

#print axioms plaquetteMixedAngularJet
#print axioms plaquetteMixedAngularInterval

end YMGap.Continuum.BF4ExactSlabPlaquetteMixedAngularInterval
