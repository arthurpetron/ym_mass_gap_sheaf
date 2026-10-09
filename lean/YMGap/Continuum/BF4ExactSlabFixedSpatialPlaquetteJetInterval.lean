/-
# Literal fixed-spatial plaquette scalar jets on the original Haar carrier

The four factors are the original ordered face links, with orientation
`false, false, true, true`. The bounds are certificate intervals under every
Haar insertion, not pointwise estimates or a curvature/scaling conclusion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
import YMGap.Continuum.SU2QuaternionRelativeHeatSecondAngularBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteJetInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionOrientedWordSelection (word)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.SU2QuaternionRelativeHeatSecondAngularBound

local notation:max "N" width:arg => List.length (baseLinks width)

private def fourCap (a : Q') : Q' := a + (a + (a + a))

/-- Four explicit polynomial jets, with no analytic hypothesis field. -/
private structure QuaternionMixedJet (blocks oi oj ii ij : Nat) (p : PolyQuaternion)
    (a b c d : Q') : Type where
  scalar : MixedJet blocks oi oj ii ij p.scalar a b c d
  iPart : MixedJet blocks oi oj ii ij p.iPart a b c d
  jPart : MixedJet blocks oi oj ii ij p.jPart a b c d
  kPart : MixedJet blocks oi oj ii ij p.kPart a b c d

private def QuaternionMixedJet.coordinate
    {blocks ob ib oi oj ii ij block : Nat}
    (hob : ob < blocks) (hib : ib < blocks) (hblock : block < blocks)
    (hoi : oi < 4) (hoj : oj < 4) (hii : ii < 4) (hij : ij < 4) :
    QuaternionMixedJet blocks (4*ob+oi) (4*ob+oj) (4*ib+ii) (4*ib+ij)
      (PolyQuaternion.coordinateVariable block) 1 2 2 4 :=
  ⟨coordinateJet hob hib hoi hoj hii hij (by omega),
   coordinateJet hob hib hoi hoj hii hij (by omega),
   coordinateJet hob hib hoi hoj hii hij (by omega),
   coordinateJet hob hib hoi hoj hii hij (by omega)⟩

private def QuaternionMixedJet.conj
    {blocks oi oj ii ij : Nat} {p : PolyQuaternion} {a b c d : Q'}
    (hoi : oi < 4*blocks) (hoj : oj < 4*blocks)
    (hii : ii < 4*blocks) (hij : ij < 4*blocks)
    (P : QuaternionMixedJet blocks oi oj ii ij p a b c d) :
    QuaternionMixedJet blocks oi oj ii ij (PolyQuaternion.conj p) a b c d :=
  ⟨P.scalar, P.iPart.neg hoi hoj hii hij, P.jPart.neg hoi hoj hii hij,
   P.kPart.neg hoi hoj hii hij⟩

private def QuaternionMixedJet.mul
    {blocks oi oj ii ij : Nat} {p q : PolyQuaternion}
    {a b c d e f g h : Q'}
    (hoi : oi < 4*blocks) (hoj : oj < 4*blocks)
    (hii : ii < 4*blocks) (hij : ij < 4*blocks)
    (P : QuaternionMixedJet blocks oi oj ii ij p a b c d)
    (Q : QuaternionMixedJet blocks oi oj ii ij q e f g h) :
    QuaternionMixedJet blocks oi oj ii ij (PolyQuaternion.mul p q)
      (fourCap (a*e)) (fourCap (b*e+a*f)) (fourCap (c*e+a*g))
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

private def QuaternionMixedJet.changeCaps
    {blocks oi oj ii ij : Nat} {p : PolyQuaternion}
    {a b c d e f g h : Q'}
    (P : QuaternionMixedJet blocks oi oj ii ij p a b c d)
    (ha : Q'.eqv a e) (hb : Q'.eqv b f)
    (hc : Q'.eqv c g) (hd : Q'.eqv d h) :
    QuaternionMixedJet blocks oi oj ii ij p e f g h :=
  ⟨⟨P.scalar.value.changeCap ha, P.scalar.inner.changeCap hb,
     P.scalar.outer.changeCap hc, P.scalar.mixed.changeCap hd⟩,
   ⟨P.iPart.value.changeCap ha, P.iPart.inner.changeCap hb,
     P.iPart.outer.changeCap hc, P.iPart.mixed.changeCap hd⟩,
   ⟨P.jPart.value.changeCap ha, P.jPart.inner.changeCap hb,
     P.jPart.outer.changeCap hc, P.jPart.mixed.changeCap hd⟩,
   ⟨P.kPart.value.changeCap ha, P.kPart.inner.changeCap hb,
     P.kPart.outer.changeCap hc, P.kPart.mixed.changeCap hd⟩⟩

private def fourWordJet
    {blocks ob ib oi oj ii ij a b c d : Nat}
    (hob : ob < blocks) (hib : ib < blocks)
    (ha : a < blocks) (hb : b < blocks) (hc : c < blocks) (hd : d < blocks)
    (hoi : oi < 4) (hoj : oj < 4) (hii : ii < 4) (hij : ij < 4) :
    QuaternionMixedJet blocks (4*ob+oi) (4*ob+oj) (4*ib+ii) (4*ib+ij)
      (word a b c d false false true true) 64 512 512 4096 := by
  have hOI : 4*ob+oi < 4*blocks := by omega
  have hOJ : 4*ob+oj < 4*blocks := by omega
  have hII : 4*ib+ii < 4*blocks := by omega
  have hIJ : 4*ib+ij < 4*blocks := by omega
  let A := QuaternionMixedJet.coordinate hob hib ha hoi hoj hii hij
  let B := QuaternionMixedJet.coordinate hob hib hb hoi hoj hii hij
  let C := (QuaternionMixedJet.coordinate hob hib hc hoi hoj hii hij).conj hOI hOJ hII hIJ
  let D := (QuaternionMixedJet.coordinate hob hib hd hoi hoj hii hij).conj hOI hOJ hII hIJ
  have J := (((A.mul hOI hOJ hII hIJ B).mul hOI hOJ hII hIJ C).mul hOI hOJ hII hIJ D)
  change QuaternionMixedJet blocks (4*ob+oi) (4*ob+oj) (4*ib+ii) (4*ib+ij)
    (PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul
      (PolyQuaternion.coordinateVariable a) (PolyQuaternion.coordinateVariable b))
      (PolyQuaternion.conj (PolyQuaternion.coordinateVariable c)))
      (PolyQuaternion.conj (PolyQuaternion.coordinateVariable d))) 64 512 512 4096
  exact J.changeCaps (by decide) (by decide) (by decide) (by decide)

private def originalWordJet
    {width blocks ob ib oi oj ii ij : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) (hroom : N width ≤ blocks)
    (hob : ob < blocks) (hib : ib < blocks)
    (hoi : oi < 4) (hoj : oj < 4) (hii : ii < 4) (hij : ij < 4) :
    QuaternionMixedJet blocks (4*ob+oi) (4*ob+oj) (4*ib+ii) (4*ib+ij)
      (word
        ((baseLinks width).idxOf (face.1, (dirsOf face.2).1))
        ((baseLinks width).idxOf (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2))
        ((baseLinks width).idxOf (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1))
        ((baseLinks width).idxOf (face.1, (dirsOf face.2).2))
        false false true true) 64 512 512 4096 :=
  fourWordJet hob hib
    (Nat.lt_of_lt_of_le (List.idxOf_lt_length_of_mem
      (face_link_mem_base hf (by simp [edgesOf]))) hroom)
    (Nat.lt_of_lt_of_le (List.idxOf_lt_length_of_mem
      (face_link_mem_base hf (by simp [edgesOf]))) hroom)
    (Nat.lt_of_lt_of_le (List.idxOf_lt_length_of_mem
      (face_link_mem_base hf (by simp [edgesOf]))) hroom)
    (Nat.lt_of_lt_of_le (List.idxOf_lt_length_of_mem
      (face_link_mem_base hf (by simp [edgesOf]))) hroom)
    hoi hoj hii hij

/-- Original scalar face, before any heat-prefix operation, under arbitrary
Haar insertion on any carrier containing the literal source links. -/
def originalValueInterval
    {width blocks ob ib oi oj ii ij : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) (hroom : N width ≤ blocks)
    (hob : ob < blocks) (hib : ib < blocks)
    (hoi : oi < 4) (hoj : oj < 4) (hii : ii < 4) (hij : ij < 4) :
    Interval blocks (plaquette width face).scalar 64 :=
  Interval.ofCoeff (plaquette_supported width blocks hroom face).scalar
    (plaquette_fourWord hf).scalar
    (originalWordJet hf hroom hob hib hoi hoj hii hij).scalar.value

/-- First raw angular jet of the literal original face, cap 512. The selected
plane may overlap either of the four face links. -/
def originalFirstInterval
    {width blocks ob ib oi oj ii ij : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) (hroom : N width ≤ blocks)
    (hob : ob < blocks) (hib : ib < blocks)
    (hoi : oi < 4) (hoj : oj < 4) (hii : ii < 4) (hij : ij < 4) :
    Interval blocks (angularDerivative (4*ob+oi) (4*ob+oj)
      (plaquette width face).scalar) 512 := by
  have hOI : 4*ob+oi < 4*blocks := by omega
  have hOJ : 4*ob+oj < 4*blocks := by omega
  exact Interval.ofCoeff
    (angularDerivative_supported_at hOI hOJ
      (plaquette_supported width blocks hroom face).scalar)
    (angularDerivative_congr _ _ (plaquette_fourWord hf).scalar)
    (originalWordJet hf hroom hob hib hoi hoj hii hij).scalar.outer

/-- Ordered mixed raw angular jet of the same literal original face, cap
4096. Outer and inner planes may coincide or overlap. -/
def originalMixedInterval
    {width blocks ob ib oi oj ii ij : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) (hroom : N width ≤ blocks)
    (hob : ob < blocks) (hib : ib < blocks)
    (hoi : oi < 4) (hoj : oj < 4) (hii : ii < 4) (hij : ij < 4) :
    Interval blocks (angularDerivative (4*ob+oi) (4*ob+oj)
      (angularDerivative (4*ib+ii) (4*ib+ij)
        (plaquette width face).scalar)) 4096 := by
  have hOI : 4*ob+oi < 4*blocks := by omega
  have hOJ : 4*ob+oj < 4*blocks := by omega
  have hII : 4*ib+ii < 4*blocks := by omega
  have hIJ : 4*ib+ij < 4*blocks := by omega
  exact Interval.ofCoeff
    (angularDerivative_supported_at hOI hOJ
      (angularDerivative_supported_at hII hIJ
        (plaquette_supported width blocks hroom face).scalar))
    (angularDerivative_congr _ _
      (angularDerivative_congr _ _ (plaquette_fourWord hf).scalar))
    (originalWordJet hf hroom hob hib hoi hoj hii hij).scalar.mixed

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteJetInterval

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteJetInterval.originalValueInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteJetInterval.originalFirstInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteJetInterval.originalMixedInterval
