/-
# Polynomial denominator clearing for every ORIGINAL signed plaquette sector

The four constructive northern inverse charts have four different positive
denominators `1+r_i`.  Their product is a common denominator.  Multiplying
each imaginary-coordinate triple by the other three factors writes every
inverse chart with one common reciprocal scale.  The `D^8` compiler can then
remove that reciprocal completely.

The resulting identity is polynomial inside each fixed central-sign sector.
The computed sector predicate itself is still not a `RatPoly` probe, so this
leaf does not yet integrate the identity under the ORIGINAL expectation or
extract interacting center coefficients.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyExtraction
import YMGap.Continuum.BF4ExactSlabPlaquetteCayleyCommonDenominator
import YMGap.Constructive.ExpAddConv

namespace YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyPolynomialClear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCommutatorDefect (plaquetteWord)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion
open YMGap.Continuum.BF4ExactSlabPlaquetteCayleyCommonDenominator
open YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyExtraction
open YMGap.Continuum.BF4ExactSlabPlaquetteDeficit
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem ac {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a + c ≈ b + d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h)
    (Q'.add_eqv_congr_left _ _ _ k)

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem nc {a b : Q'} (h : a ≈ b) : -a ≈ -b :=
  Q'.neg_eqv_congr _ _ h

/-- Semantic equality of rational chart triples. -/
def TripleEquivalent (a b : Triple) : Prop :=
  a.x ≈ b.x ∧ a.y ≈ b.y ∧ a.z ≈ b.z

/-- The positive inverse-chart denominator of a northern unit. -/
def chartDenominator (x : UnitNorm) : Q' := 1 + x.val.r

/-- The unscaled imaginary-coordinate numerator triple. -/
def chartNumerator (x : UnitNorm) : Triple :=
  ⟨x.val.i, x.val.j, x.val.k⟩

def commonChartDenominator (a b c d : UnitNorm) : Q' :=
  ((chartDenominator a * chartDenominator b) * chartDenominator c) *
    chartDenominator d

def firstComplement (_a b c d : UnitNorm) : Q' :=
  (chartDenominator b * chartDenominator c) * chartDenominator d

def secondComplement (a _b c d : UnitNorm) : Q' :=
  (chartDenominator a * chartDenominator c) * chartDenominator d

def thirdComplement (a b _c d : UnitNorm) : Q' :=
  (chartDenominator a * chartDenominator b) * chartDenominator d

def fourthComplement (a b c _d : UnitNorm) : Q' :=
  (chartDenominator a * chartDenominator b) * chartDenominator c

/-- Four polynomial numerator triples sharing the one product denominator. -/
def firstClearedTriple (a b c d : UnitNorm) : Triple :=
  scale3 (firstComplement a b c d) (chartNumerator a)

def secondClearedTriple (a b c d : UnitNorm) : Triple :=
  scale3 (secondComplement a b c d) (chartNumerator b)

def thirdClearedTriple (a b c d : UnitNorm) : Triple :=
  scale3 (thirdComplement a b c d) (chartNumerator c)

def fourthClearedTriple (a b c d : UnitNorm) : Triple :=
  scale3 (fourthComplement a b c d) (chartNumerator d)

theorem chartDenominator_positive (x : UnitNorm) (hx : (0 : Q') ≤ x.val.r) :
    (0 : Q') < chartDenominator x :=
  Q'.pos_add_nonneg (by decide) hx

theorem commonChartDenominator_positive (a b c d : UnitNorm)
    (ha : (0 : Q') ≤ a.val.r) (hb : (0 : Q') ≤ b.val.r)
    (hc : (0 : Q') ≤ c.val.r) (hd : (0 : Q') ≤ d.val.r) :
    (0 : Q') < commonChartDenominator a b c d :=
  Q'.mul_pos
    (Q'.mul_pos
      (Q'.mul_pos (chartDenominator_positive a ha) (chartDenominator_positive b hb))
      (chartDenominator_positive c hc))
    (chartDenominator_positive d hd)

private theorem reciprocal_complement {D denominator complement e inverse : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hDsplit : D ≈ denominator * complement)
    (hDe : D * e ≈ 1) (hdi : denominator * inverse ≈ 1) :
    e * complement ≈ inverse := by
  have hleft : denominator * (e * complement) ≈ 1 := by
    have hreorder : denominator * (e * complement) ≈
        (denominator * complement) * e :=
      poly_identity_of_normal_eq
        (.var 0 * (.var 1 * .var 2)) ((.var 0 * .var 2) * .var 1)
        (by decide) (fun | 0 => denominator | 1 => e | _ => complement)
    exact Q'.eqv_trans _ _ _ hreorder
      (Q'.eqv_trans _ _ _
        (mc (Q'.eqv_symm hDsplit) (Q'.eqv_refl e)) hDe)
  exact Q'.mul_left_cancel_of_pos hdenominator
    (Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hdi))

private theorem common_split_first (a b c d : UnitNorm) :
    commonChartDenominator a b c d ≈
      chartDenominator a * firstComplement a b c d := by
  unfold commonChartDenominator firstComplement
  exact poly_identity_of_normal_eq
    (((.var 0 * .var 1) * .var 2) * .var 3)
    (.var 0 * ((.var 1 * .var 2) * .var 3))
    (by decide) (fun
      | 0 => chartDenominator a
      | 1 => chartDenominator b
      | 2 => chartDenominator c
      | _ => chartDenominator d)

private theorem common_split_second (a b c d : UnitNorm) :
    commonChartDenominator a b c d ≈
      chartDenominator b * secondComplement a b c d := by
  unfold commonChartDenominator secondComplement
  exact poly_identity_of_normal_eq
    (((.var 0 * .var 1) * .var 2) * .var 3)
    (.var 1 * ((.var 0 * .var 2) * .var 3))
    (by decide) (fun
      | 0 => chartDenominator a
      | 1 => chartDenominator b
      | 2 => chartDenominator c
      | _ => chartDenominator d)

private theorem common_split_third (a b c d : UnitNorm) :
    commonChartDenominator a b c d ≈
      chartDenominator c * thirdComplement a b c d := by
  unfold commonChartDenominator thirdComplement
  exact poly_identity_of_normal_eq
    (((.var 0 * .var 1) * .var 2) * .var 3)
    (.var 2 * ((.var 0 * .var 1) * .var 3))
    (by decide) (fun
      | 0 => chartDenominator a
      | 1 => chartDenominator b
      | 2 => chartDenominator c
      | _ => chartDenominator d)

private theorem common_split_fourth (a b c d : UnitNorm) :
    commonChartDenominator a b c d ≈
      chartDenominator d * fourthComplement a b c d := by
  unfold commonChartDenominator fourthComplement
  exact poly_identity_of_normal_eq
    (((.var 0 * .var 1) * .var 2) * .var 3)
    (.var 3 * ((.var 0 * .var 1) * .var 2))
    (by decide) (fun
      | 0 => chartDenominator a
      | 1 => chartDenominator b
      | 2 => chartDenominator c
      | _ => chartDenominator d)

/-- Exact stereographic coordinates respect semantic equality of all three
chart coordinates. -/
theorem stereographic_congr {a b : Triple} (h : TripleEquivalent a b) :
    (stereographic a).Equivalent (stereographic b) := by
  have hnorm : norm3 a ≈ norm3 b := by
    unfold norm3
    exact ac (ac (mc h.1 h.1) (mc h.2.1 h.2.1))
      (mc h.2.2 h.2.2)
  have hden : denominator a ≈ denominator b :=
    ac (Q'.eqv_refl 1) hnorm
  have hrecip :
      Q'.recipPos (denominator a) (denominator_positive a) ≈
        Q'.recipPos (denominator b) (denominator_positive b) :=
    Q'.recipPos_eqv_congr _ _ _ _ hden
  have hrawScalar : 1 + -norm3 a ≈ 1 + -norm3 b :=
    ac (Q'.eqv_refl 1) (nc hnorm)
  change
    (Q'.recipPos (denominator a) (denominator_positive a) *
          (1 + -norm3 a) ≈
        Q'.recipPos (denominator b) (denominator_positive b) *
          (1 + -norm3 b)) ∧
      (Q'.recipPos (denominator a) (denominator_positive a) * (2 * a.x) ≈
        Q'.recipPos (denominator b) (denominator_positive b) * (2 * b.x)) ∧
      (Q'.recipPos (denominator a) (denominator_positive a) * (2 * a.y) ≈
        Q'.recipPos (denominator b) (denominator_positive b) * (2 * b.y)) ∧
      (Q'.recipPos (denominator a) (denominator_positive a) * (2 * a.z) ≈
        Q'.recipPos (denominator b) (denominator_positive b) * (2 * b.z))
  exact ⟨mc hrecip hrawScalar,
    mc hrecip (mc (Q'.eqv_refl 2) h.1),
    mc hrecip (mc (Q'.eqv_refl 2) h.2.1),
    mc hrecip (mc (Q'.eqv_refl 2) h.2.2)⟩

private theorem scale_component (e complement inverse value : Q')
    (h : e * complement ≈ inverse) :
    e * (complement * value) ≈ inverse * value :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv e complement value))
    (mc h (Q'.eqv_refl value))

private theorem first_common_scale (a b c d : UnitNorm)
    (ha : (0 : Q') ≤ a.val.r) (hb : (0 : Q') ≤ b.val.r)
    (hc : (0 : Q') ≤ c.val.r) (hd : (0 : Q') ≤ d.val.r) :
    let D := commonChartDenominator a b c d
    let hD := commonChartDenominator_positive a b c d ha hb hc hd
    TripleEquivalent
      (scale3 (Q'.recipPos D hD) (firstClearedTriple a b c d))
      (inverseChart a ha) := by
  dsimp only
  let D := commonChartDenominator a b c d
  let hD := commonChartDenominator_positive a b c d ha hb hc hd
  let e := Q'.recipPos D hD
  let denominatorA := chartDenominator a
  let inverseA := Q'.recipPos denominatorA (chartDenominator_positive a ha)
  have hscale : e * firstComplement a b c d ≈ inverseA :=
    reciprocal_complement (chartDenominator_positive a ha)
      (common_split_first a b c d) (Q'.mul_recipPos_eqv D hD)
      (Q'.mul_recipPos_eqv denominatorA (chartDenominator_positive a ha))
  change
    (e * (firstComplement a b c d * a.val.i) ≈ inverseA * a.val.i) ∧
      (e * (firstComplement a b c d * a.val.j) ≈ inverseA * a.val.j) ∧
      (e * (firstComplement a b c d * a.val.k) ≈ inverseA * a.val.k)
  exact ⟨scale_component _ _ _ _ hscale,
    scale_component _ _ _ _ hscale, scale_component _ _ _ _ hscale⟩

private theorem second_common_scale (a b c d : UnitNorm)
    (ha : (0 : Q') ≤ a.val.r) (hb : (0 : Q') ≤ b.val.r)
    (hc : (0 : Q') ≤ c.val.r) (hd : (0 : Q') ≤ d.val.r) :
    let D := commonChartDenominator a b c d
    let hD := commonChartDenominator_positive a b c d ha hb hc hd
    TripleEquivalent
      (scale3 (Q'.recipPos D hD) (secondClearedTriple a b c d))
      (inverseChart b hb) := by
  dsimp only
  let D := commonChartDenominator a b c d
  let hD := commonChartDenominator_positive a b c d ha hb hc hd
  let e := Q'.recipPos D hD
  let denominatorB := chartDenominator b
  let inverseB := Q'.recipPos denominatorB (chartDenominator_positive b hb)
  have hscale : e * secondComplement a b c d ≈ inverseB :=
    reciprocal_complement (chartDenominator_positive b hb)
      (common_split_second a b c d) (Q'.mul_recipPos_eqv D hD)
      (Q'.mul_recipPos_eqv denominatorB (chartDenominator_positive b hb))
  change
    (e * (secondComplement a b c d * b.val.i) ≈ inverseB * b.val.i) ∧
      (e * (secondComplement a b c d * b.val.j) ≈ inverseB * b.val.j) ∧
      (e * (secondComplement a b c d * b.val.k) ≈ inverseB * b.val.k)
  exact ⟨scale_component _ _ _ _ hscale,
    scale_component _ _ _ _ hscale, scale_component _ _ _ _ hscale⟩

private theorem third_common_scale (a b c d : UnitNorm)
    (ha : (0 : Q') ≤ a.val.r) (hb : (0 : Q') ≤ b.val.r)
    (hc : (0 : Q') ≤ c.val.r) (hd : (0 : Q') ≤ d.val.r) :
    let D := commonChartDenominator a b c d
    let hD := commonChartDenominator_positive a b c d ha hb hc hd
    TripleEquivalent
      (scale3 (Q'.recipPos D hD) (thirdClearedTriple a b c d))
      (inverseChart c hc) := by
  dsimp only
  let D := commonChartDenominator a b c d
  let hD := commonChartDenominator_positive a b c d ha hb hc hd
  let e := Q'.recipPos D hD
  let denominatorC := chartDenominator c
  let inverseC := Q'.recipPos denominatorC (chartDenominator_positive c hc)
  have hscale : e * thirdComplement a b c d ≈ inverseC :=
    reciprocal_complement (chartDenominator_positive c hc)
      (common_split_third a b c d) (Q'.mul_recipPos_eqv D hD)
      (Q'.mul_recipPos_eqv denominatorC (chartDenominator_positive c hc))
  change
    (e * (thirdComplement a b c d * c.val.i) ≈ inverseC * c.val.i) ∧
      (e * (thirdComplement a b c d * c.val.j) ≈ inverseC * c.val.j) ∧
      (e * (thirdComplement a b c d * c.val.k) ≈ inverseC * c.val.k)
  exact ⟨scale_component _ _ _ _ hscale,
    scale_component _ _ _ _ hscale, scale_component _ _ _ _ hscale⟩

private theorem fourth_common_scale (a b c d : UnitNorm)
    (ha : (0 : Q') ≤ a.val.r) (hb : (0 : Q') ≤ b.val.r)
    (hc : (0 : Q') ≤ c.val.r) (hd : (0 : Q') ≤ d.val.r) :
    let D := commonChartDenominator a b c d
    let hD := commonChartDenominator_positive a b c d ha hb hc hd
    TripleEquivalent
      (scale3 (Q'.recipPos D hD) (fourthClearedTriple a b c d))
      (inverseChart d hd) := by
  dsimp only
  let D := commonChartDenominator a b c d
  let hD := commonChartDenominator_positive a b c d ha hb hc hd
  let e := Q'.recipPos D hD
  let denominatorD := chartDenominator d
  let inverseD := Q'.recipPos denominatorD (chartDenominator_positive d hd)
  have hscale : e * fourthComplement a b c d ≈ inverseD :=
    reciprocal_complement (chartDenominator_positive d hd)
      (common_split_fourth a b c d) (Q'.mul_recipPos_eqv D hD)
      (Q'.mul_recipPos_eqv denominatorD (chartDenominator_positive d hd))
  change
    (e * (fourthComplement a b c d * d.val.i) ≈ inverseD * d.val.i) ∧
      (e * (fourthComplement a b c d * d.val.j) ≈ inverseD * d.val.j) ∧
      (e * (fourthComplement a b c d * d.val.k) ≈ inverseD * d.val.k)
  exact ⟨scale_component _ _ _ _ hscale,
    scale_component _ _ _ _ hscale, scale_component _ _ _ _ hscale⟩

private theorem common_chart_pin_first (a b c d : UnitNorm)
    (ha : (0 : Q') ≤ a.val.r) (hb : (0 : Q') ≤ b.val.r)
    (hc : (0 : Q') ≤ c.val.r) (hd : (0 : Q') ≤ d.val.r) :
    let D := commonChartDenominator a b c d
    let hD := commonChartDenominator_positive a b c d ha hb hc hd
    a.Equivalent
      (stereographic (scale3 (Q'.recipPos D hD) (firstClearedTriple a b c d))) := by
  dsimp only
  exact UnitNorm.semanticSetoid.iseqv.trans
    (UnitNorm.semanticSetoid.iseqv.symm (stereographic_inverse a ha))
    (UnitNorm.semanticSetoid.iseqv.symm
      (stereographic_congr (first_common_scale a b c d ha hb hc hd)))

private theorem common_chart_pin_second (a b c d : UnitNorm)
    (ha : (0 : Q') ≤ a.val.r) (hb : (0 : Q') ≤ b.val.r)
    (hc : (0 : Q') ≤ c.val.r) (hd : (0 : Q') ≤ d.val.r) :
    let D := commonChartDenominator a b c d
    let hD := commonChartDenominator_positive a b c d ha hb hc hd
    b.Equivalent
      (stereographic (scale3 (Q'.recipPos D hD) (secondClearedTriple a b c d))) := by
  dsimp only
  exact UnitNorm.semanticSetoid.iseqv.trans
    (UnitNorm.semanticSetoid.iseqv.symm (stereographic_inverse b hb))
    (UnitNorm.semanticSetoid.iseqv.symm
      (stereographic_congr (second_common_scale a b c d ha hb hc hd)))

private theorem common_chart_pin_third (a b c d : UnitNorm)
    (ha : (0 : Q') ≤ a.val.r) (hb : (0 : Q') ≤ b.val.r)
    (hc : (0 : Q') ≤ c.val.r) (hd : (0 : Q') ≤ d.val.r) :
    let D := commonChartDenominator a b c d
    let hD := commonChartDenominator_positive a b c d ha hb hc hd
    c.Equivalent
      (stereographic (scale3 (Q'.recipPos D hD) (thirdClearedTriple a b c d))) := by
  dsimp only
  exact UnitNorm.semanticSetoid.iseqv.trans
    (UnitNorm.semanticSetoid.iseqv.symm (stereographic_inverse c hc))
    (UnitNorm.semanticSetoid.iseqv.symm
      (stereographic_congr (third_common_scale a b c d ha hb hc hd)))

private theorem common_chart_pin_fourth (a b c d : UnitNorm)
    (ha : (0 : Q') ≤ a.val.r) (hb : (0 : Q') ≤ b.val.r)
    (hc : (0 : Q') ≤ c.val.r) (hd : (0 : Q') ≤ d.val.r) :
    let D := commonChartDenominator a b c d
    let hD := commonChartDenominator_positive a b c d ha hb hc hd
    d.Equivalent
      (stereographic (scale3 (Q'.recipPos D hD) (fourthClearedTriple a b c d))) := by
  dsimp only
  exact UnitNorm.semanticSetoid.iseqv.trans
    (UnitNorm.semanticSetoid.iseqv.symm (stereographic_inverse d hd))
    (UnitNorm.semanticSetoid.iseqv.symm
      (stereographic_congr (fourth_common_scale a b c d ha hb hc hd)))

/-- Every ORIGINAL corrected-slab plaquette has an exact reciprocal-free
polynomial Cayley identity after its computed central sign sector is fixed. -/
theorem original_plaquette_signed_cayley_polynomial_cleared
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    let u0 := linkValue extent qs (face.1, (dirsOf face.2).1)
    let u1 := linkValue extent qs
      (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)
    let u2 := linkValue extent qs
      (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)
    let u3 := linkValue extent qs (face.1, (dirsOf face.2).2)
    let s0 := chartSign u0
    let s1 := chartSign u1
    let s2 := chartSign u2
    let s3 := chartSign u3
    let n0 := signed s0 u0
    let n1 := signed s1 u1
    let n2 := signed s2 u2
    let n3 := signed s3 u3
    let D := commonChartDenominator n0 n1 n2 n3
    let a := firstClearedTriple n0 n1 n2 n3
    let b := secondClearedTriple n0 n1 n2 n3
    let c := thirdClearedTriple n0 n1 n2 n3
    let d := fourthClearedTriple n0 n1 n2 n3
    let sector := plaquetteSign s0 s1 s2 s3
    clearedCayleyDenominator D a b (neg3 c) (neg3 d) *
        (2 + -(2 * signedScalar sector
          (evalRatPoly (environment qs)
            (correctedSlabPlaquettePolynomial extent face).scalar))) ≈
      clearedCayleyDeficit D a b (neg3 c) (neg3 d) := by
  dsimp only
  let u0 := linkValue extent qs (face.1, (dirsOf face.2).1)
  let u1 := linkValue extent qs
    (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)
  let u2 := linkValue extent qs
    (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)
  let u3 := linkValue extent qs (face.1, (dirsOf face.2).2)
  let s0 := chartSign u0
  let s1 := chartSign u1
  let s2 := chartSign u2
  let s3 := chartSign u3
  let n0 := signed s0 u0
  let n1 := signed s1 u1
  let n2 := signed s2 u2
  let n3 := signed s3 u3
  let h0 := chartSign_nonnegative u0
  let h1 := chartSign_nonnegative u1
  let h2 := chartSign_nonnegative u2
  let h3 := chartSign_nonnegative u3
  let D := commonChartDenominator n0 n1 n2 n3
  let hD := commonChartDenominator_positive n0 n1 n2 n3 h0 h1 h2 h3
  let e := Q'.recipPos D hD
  let a := firstClearedTriple n0 n1 n2 n3
  let b := secondClearedTriple n0 n1 n2 n3
  let c := thirdClearedTriple n0 n1 n2 n3
  let d := fourthClearedTriple n0 n1 n2 n3
  let sector := plaquetteSign s0 s1 s2 s3
  have hchart :
      (plaquetteWord n0 n1 n2 n3).Equivalent
        (plaquetteWord (stereographic (scale3 e a))
          (stereographic (scale3 e b))
          (stereographic (scale3 e c))
          (stereographic (scale3 e d))) :=
    UnitNorm.mul_congr
      (UnitNorm.mul_congr
        (UnitNorm.mul_congr
          (common_chart_pin_first n0 n1 n2 n3 h0 h1 h2 h3)
          (common_chart_pin_second n0 n1 n2 n3 h0 h1 h2 h3))
        (UnitNorm.inv_congr
          (common_chart_pin_third n0 n1 n2 n3 h0 h1 h2 h3)))
      (UnitNorm.inv_congr
        (common_chart_pin_fourth n0 n1 n2 n3 h0 h1 h2 h3))
  have hsector :
      (plaquetteWord n0 n1 n2 n3).Equivalent
        (signed sector (plaquetteWord u0 u1 u2 u3)) :=
    plaquetteWord_signed s0 s1 s2 s3 u0 u1 u2 u3
  have hchartSector :
      (plaquetteWord (stereographic (scale3 e a))
        (stereographic (scale3 e b))
        (stereographic (scale3 e c))
        (stereographic (scale3 e d))).val.r ≈
      signedScalar sector (plaquetteWord u0 u1 u2 u3).val.r :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hchart.1)
      (Q'.eqv_trans _ _ _ hsector.1
        (signed_scalar sector (plaquetteWord u0 u1 u2 u3)))
  have horiginal :
      evalRatPoly (environment qs)
          (correctedSlabPlaquettePolynomial extent face).scalar ≈
        (plaquetteWord u0 u1 u2 u3).val.r := by
    simpa only [u0, u1, u2, u3, plaquetteValue] using
      (plaquette_scalar_pin extent qs face)
  have hscalar :
      (plaquetteWord (stereographic (scale3 e a))
        (stereographic (scale3 e b))
        (stereographic (scale3 e c))
        (stereographic (scale3 e d))).val.r ≈
      signedScalar sector
        (evalRatPoly (environment qs)
          (correctedSlabPlaquettePolynomial extent face).scalar) :=
    Q'.eqv_trans _ _ _ hchartSector
      (signedScalar_congr sector (Q'.eqv_symm horiginal))
  exact Q'.eqv_trans _ _ _
    (mc (Q'.eqv_refl _)
      (ac (Q'.eqv_refl 2)
        (nc (mc (Q'.eqv_refl 2) (Q'.eqv_symm hscalar)))))
    (plaquetteWord_cayley_reciprocal_denominator_cleared D hD a b c d)

/-- Fixed-sector interface for integration: once the four computed chart
signs are supplied as explicit Boolean equalities, every quantity in the
cleared identity is polynomial in the corresponding signed link coordinates.
The four equalities are precisely the still-unintegrated sector indicators. -/
theorem original_plaquette_fixed_sign_sector_cayley_polynomial_cleared
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq)
    (s0 s1 s2 s3 : Bool)
    (hs0 : chartSign
      (linkValue extent qs (face.1, (dirsOf face.2).1)) = s0)
    (hs1 : chartSign
      (linkValue extent qs
        (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)) = s1)
    (hs2 : chartSign
      (linkValue extent qs
        (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)) = s2)
    (hs3 : chartSign
      (linkValue extent qs (face.1, (dirsOf face.2).2)) = s3) :
    let u0 := linkValue extent qs (face.1, (dirsOf face.2).1)
    let u1 := linkValue extent qs
      (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)
    let u2 := linkValue extent qs
      (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)
    let u3 := linkValue extent qs (face.1, (dirsOf face.2).2)
    let n0 := signed s0 u0
    let n1 := signed s1 u1
    let n2 := signed s2 u2
    let n3 := signed s3 u3
    let D := commonChartDenominator n0 n1 n2 n3
    let a := firstClearedTriple n0 n1 n2 n3
    let b := secondClearedTriple n0 n1 n2 n3
    let c := thirdClearedTriple n0 n1 n2 n3
    let d := fourthClearedTriple n0 n1 n2 n3
    let sector := plaquetteSign s0 s1 s2 s3
    clearedCayleyDenominator D a b (neg3 c) (neg3 d) *
        (2 + -(2 * signedScalar sector
          (evalRatPoly (environment qs)
            (correctedSlabPlaquettePolynomial extent face).scalar))) ≈
      clearedCayleyDeficit D a b (neg3 c) (neg3 d) := by
  subst s0
  subst s1
  subst s2
  subst s3
  exact original_plaquette_signed_cayley_polynomial_cleared extent qs face

end YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyPolynomialClear

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyPolynomialClear.stereographic_congr
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyPolynomialClear.chartDenominator_positive
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyPolynomialClear.commonChartDenominator_positive
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyPolynomialClear.original_plaquette_signed_cayley_polynomial_cleared
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyPolynomialClear.original_plaquette_fixed_sign_sector_cayley_polynomial_cleared
