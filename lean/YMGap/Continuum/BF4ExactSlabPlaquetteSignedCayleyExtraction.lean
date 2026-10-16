/-
# Global signed-chart extraction for the ORIGINAL plaquette scalar

Every rational unit quaternion has a constructive northern representative:
apply its computed chart sign and then use `inverseChart`.  This leaf tracks
the four resulting central signs through the actual ordered plaquette word.
The exact Cayley identity therefore holds on every finite configuration, with
one explicit Boolean parity acting on the original plaquette scalar.

This is still a pointwise finite identity.  It supplies no chart pushforward,
Jacobian, integration theorem, coefficient estimate, volume-uniform bound,
continuum Hamiltonian, or mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteNorthernCayleyExtraction
import YMGap.RepTheory.RationalQuaternionSignQuotient

namespace YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyExtraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCommutatorDefect (plaquetteWord)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion
open YMGap.Continuum.BF4ExactSlabPlaquetteNorthernCayleyExtraction
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

private theorem unit_trans {a b c : UnitNorm}
    (h : a.Equivalent b) (k : b.Equivalent c) : a.Equivalent c :=
  UnitNorm.semanticSetoid.iseqv.trans h k

/-- The scalar sign selected by a Boolean. -/
def signFactor (south : Bool) : UnitNorm :=
  if south then unitNegativeOne else unitOne

/-- The same sign action on one rational scalar. -/
def signedScalar (south : Bool) (value : Q') : Q' :=
  if south then -value else value

/-- Ordered parity of the four link signs.  Inverted links retain the same
central sign because `(-u)⁻¹ = -u⁻¹`. -/
def plaquetteSign (a b c d : Bool) : Bool :=
  Bool.xor (Bool.xor (Bool.xor a b) c) d

private theorem negativeOne_mul_equivalent_signedTrue (x : UnitNorm) :
    (UnitNorm.mul unitNegativeOne x).Equivalent (signed true x) := by
  let rho : Nat → Q' := fun
    | 0 => x.val.r
    | 1 => x.val.i
    | 2 => x.val.j
    | _ => x.val.k
  change
    ((((-1 : Q') * x.val.r + -(0 * x.val.i)) +
        (-(0 * x.val.j) + -(0 * x.val.k))) ≈ -x.val.r) ∧
      ((((-1 : Q') * x.val.i + 0 * x.val.r) +
        (0 * x.val.k + -(0 * x.val.j))) ≈ -x.val.i) ∧
      ((((-1 : Q') * x.val.j + -(0 * x.val.k)) +
        (0 * x.val.r + 0 * x.val.i)) ≈ -x.val.j) ∧
      (((-1 : Q') * x.val.k + 0 * x.val.j) +
        (-(0 * x.val.i) + 0 * x.val.r) ≈ -x.val.k)
  exact
    ⟨poly_identity_of_normal_eq
        (((-1) * .var 0 + -(0 * .var 1)) +
          (-(0 * .var 2) + -(0 * .var 3)))
        (-(.var 0 : PE)) (by decide) rho,
      poly_identity_of_normal_eq
        (((-1) * .var 1 + 0 * .var 0) +
          (0 * .var 3 + -(0 * .var 2)))
        (-(.var 1 : PE)) (by decide) rho,
      poly_identity_of_normal_eq
        (((-1) * .var 2 + -(0 * .var 3)) +
          (0 * .var 0 + 0 * .var 1))
        (-(.var 2 : PE)) (by decide) rho,
      poly_identity_of_normal_eq
        (((-1) * .var 3 + 0 * .var 2) +
          (-(0 * .var 1) + 0 * .var 0))
        (-(.var 3 : PE)) (by decide) rho⟩

/-- Multiplication by the selected actual central unit is exactly the existing
`signed` operation up to the rational semantic equality. -/
theorem signFactor_mul_equivalent_signed (south : Bool) (x : UnitNorm) :
    (UnitNorm.mul (signFactor south) x).Equivalent (signed south x) := by
  cases south
  · exact UnitNorm.one_mul x
  · exact negativeOne_mul_equivalent_signedTrue x

/-- The selected sign is central on the full rational unit-quaternion carrier. -/
theorem signFactor_central (south : Bool) (x : UnitNorm) :
    (UnitNorm.mul (signFactor south) x).Equivalent
      (UnitNorm.mul x (signFactor south)) := by
  cases south
  · exact UnitNorm.semanticSetoid.iseqv.trans (UnitNorm.one_mul x)
      (UnitNorm.semanticSetoid.iseqv.symm (UnitNorm.mul_one x))
  · simpa only [signFactor, if_true,
      RationalQuaternion.UnitNorm.includeSign] using
      (RationalQuaternion.UnitNorm.includeSign_central QuaternionSign.negative x)

/-- Multiplying two selected signs computes Boolean xor. -/
theorem signFactor_mul (south west : Bool) :
    (UnitNorm.mul (signFactor south) (signFactor west)).Equivalent
      (signFactor (Bool.xor south west)) := by
  cases south <;> cases west <;>
    change RationalQuaternion.Equivalent _ _ <;>
    unfold signFactor UnitNorm.mul unitOne unitNegativeOne RationalQuaternion.one
      RationalQuaternion.scalar RationalQuaternion.neg RationalQuaternion.mul
      RationalQuaternion.Equivalent <;>
    decide

/-- The signed representatives multiply with exactly the xor sign. -/
theorem signed_mul (south west : Bool) (x y : UnitNorm) :
    (UnitNorm.mul (signed south x) (signed west y)).Equivalent
      (signed (Bool.xor south west) (UnitNorm.mul x y)) := by
  let zSouth := signFactor south
  let zWest := signFactor west
  have h0 :
      (UnitNorm.mul (signed south x) (signed west y)).Equivalent
        (UnitNorm.mul (UnitNorm.mul zSouth x) (UnitNorm.mul zWest y)) :=
    UnitNorm.mul_congr
      (UnitNorm.semanticSetoid.iseqv.symm
        (signFactor_mul_equivalent_signed south x))
      (UnitNorm.semanticSetoid.iseqv.symm
        (signFactor_mul_equivalent_signed west y))
  have h1 :
      (UnitNorm.mul (UnitNorm.mul zSouth x) (UnitNorm.mul zWest y)).Equivalent
        (UnitNorm.mul zSouth (UnitNorm.mul x (UnitNorm.mul zWest y))) :=
    UnitNorm.mul_assoc zSouth x (UnitNorm.mul zWest y)
  have h2 :
      (UnitNorm.mul zSouth (UnitNorm.mul x (UnitNorm.mul zWest y))).Equivalent
        (UnitNorm.mul zSouth (UnitNorm.mul (UnitNorm.mul x zWest) y)) :=
    UnitNorm.mul_congr (UnitNorm.semanticSetoid.iseqv.refl _)
      (UnitNorm.semanticSetoid.iseqv.symm (UnitNorm.mul_assoc x zWest y))
  have h3 :
      (UnitNorm.mul zSouth (UnitNorm.mul (UnitNorm.mul x zWest) y)).Equivalent
        (UnitNorm.mul zSouth (UnitNorm.mul (UnitNorm.mul zWest x) y)) :=
    UnitNorm.mul_congr (UnitNorm.semanticSetoid.iseqv.refl _)
      (UnitNorm.mul_congr
        (UnitNorm.semanticSetoid.iseqv.symm (signFactor_central west x))
        (UnitNorm.semanticSetoid.iseqv.refl _))
  have h4 :
      (UnitNorm.mul zSouth (UnitNorm.mul (UnitNorm.mul zWest x) y)).Equivalent
        (UnitNorm.mul zSouth (UnitNorm.mul zWest (UnitNorm.mul x y))) :=
    UnitNorm.mul_congr (UnitNorm.semanticSetoid.iseqv.refl _)
      (UnitNorm.mul_assoc zWest x y)
  have h5 :
      (UnitNorm.mul zSouth (UnitNorm.mul zWest (UnitNorm.mul x y))).Equivalent
        (UnitNorm.mul (UnitNorm.mul zSouth zWest) (UnitNorm.mul x y)) :=
    UnitNorm.semanticSetoid.iseqv.symm
      (UnitNorm.mul_assoc zSouth zWest (UnitNorm.mul x y))
  have h6 :
      (UnitNorm.mul (UnitNorm.mul zSouth zWest) (UnitNorm.mul x y)).Equivalent
        (UnitNorm.mul (signFactor (Bool.xor south west)) (UnitNorm.mul x y)) :=
    UnitNorm.mul_congr (signFactor_mul south west)
      (UnitNorm.semanticSetoid.iseqv.refl _)
  have h7 :
      (UnitNorm.mul (signFactor (Bool.xor south west)) (UnitNorm.mul x y)).Equivalent
        (signed (Bool.xor south west) (UnitNorm.mul x y)) :=
    signFactor_mul_equivalent_signed _ _
  exact unit_trans h0 (unit_trans h1 (unit_trans h2
    (unit_trans h3 (unit_trans h4 (unit_trans h5 (unit_trans h6 h7))))))

/-- Conjugation, hence unit inversion, preserves the selected central sign. -/
theorem conj_signed (south : Bool) (x : UnitNorm) :
    (UnitNorm.conj (signed south x)).Equivalent
      (signed south (UnitNorm.conj x)) := by
  cases south
  · exact UnitNorm.semanticSetoid.iseqv.refl _
  · change (RationalQuaternion.conj (RationalQuaternion.neg x.val)).Equivalent
      (RationalQuaternion.neg (RationalQuaternion.conj x.val))
    unfold RationalQuaternion.Equivalent RationalQuaternion.conj RationalQuaternion.neg
    exact ⟨Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _⟩

/-- The ordered plaquette word carries precisely the xor of its four central
link signs. -/
theorem plaquetteWord_signed (sa sb sc sd : Bool) (a b c d : UnitNorm) :
    (plaquetteWord (signed sa a) (signed sb b) (signed sc c) (signed sd d)).Equivalent
      (signed (plaquetteSign sa sb sc sd) (plaquetteWord a b c d)) := by
  have hab :
      (UnitNorm.mul (signed sa a) (signed sb b)).Equivalent
        (signed (Bool.xor sa sb) (UnitNorm.mul a b)) :=
    signed_mul sa sb a b
  have hc :
      (UnitNorm.conj (signed sc c)).Equivalent
        (signed sc (UnitNorm.conj c)) :=
    conj_signed sc c
  have hd :
      (UnitNorm.conj (signed sd d)).Equivalent
        (signed sd (UnitNorm.conj d)) :=
    conj_signed sd d
  have habc :
      (UnitNorm.mul
        (UnitNorm.mul (signed sa a) (signed sb b))
        (UnitNorm.conj (signed sc c))).Equivalent
      (signed (Bool.xor (Bool.xor sa sb) sc)
        (UnitNorm.mul (UnitNorm.mul a b) (UnitNorm.conj c))) :=
    UnitNorm.semanticSetoid.iseqv.trans (UnitNorm.mul_congr hab hc)
      (signed_mul (Bool.xor sa sb) sc (UnitNorm.mul a b) (UnitNorm.conj c))
  exact UnitNorm.semanticSetoid.iseqv.trans (UnitNorm.mul_congr habc hd)
    (signed_mul (Bool.xor (Bool.xor sa sb) sc) sd
      (UnitNorm.mul (UnitNorm.mul a b) (UnitNorm.conj c)) (UnitNorm.conj d))

/-- Applying the computed chart sign twice returns the original unit
quaternion semantically. -/
theorem signed_chartSign_involutive (x : UnitNorm) :
    (signed (chartSign x) (signed (chartSign x) x)).Equivalent x := by
  unfold chartSign
  by_cases h : (0 : Q') ≤ x.val.r
  · simp only [h, not_true_eq_false, decide_false, signed, Bool.false_eq_true, if_false]
    exact UnitNorm.semanticSetoid.iseqv.refl _
  · simp only [h, not_false_eq_true, decide_true, signed, if_true]
    change (RationalQuaternion.neg (RationalQuaternion.neg x.val)).Equivalent x.val
    unfold RationalQuaternion.Equivalent RationalQuaternion.neg
    exact ⟨Q'.neg_neg_eqv _, Q'.neg_neg_eqv _, Q'.neg_neg_eqv _, Q'.neg_neg_eqv _⟩

/-- The computed northern representative of every rational unit quaternion
has a constructive exact Cayley pin. -/
theorem signed_chart_pin (x : UnitNorm) :
    let north := signed (chartSign x) x
    north.Equivalent
      (stereographic (scale3 1
        (inverseChart north (chartSign_nonnegative x)))) := by
  dsimp only
  exact UnitNorm.semanticSetoid.iseqv.trans
    (UnitNorm.semanticSetoid.iseqv.symm
      (stereographic_inverse (signed (chartSign x) x)
        (chartSign_nonnegative x)))
    (UnitNorm.semanticSetoid.iseqv.symm
      (stereographic_scale3_one
        (inverseChart (signed (chartSign x) x) (chartSign_nonnegative x))))

theorem signedScalar_congr (south : Bool) {x y : Q'} (h : x ≈ y) :
    signedScalar south x ≈ signedScalar south y := by
  cases south
  · exact h
  · exact nc h

theorem signed_scalar (south : Bool) (x : UnitNorm) :
    (signed south x).val.r ≈ signedScalar south x.val.r := by
  cases south <;> exact Q'.eqv_refl _

/-- Every actual corrected-slab plaquette admits an exact Cayley extraction.
The only extra datum is the explicitly computed xor of the four central chart
signs, acting on the ORIGINAL polynomial scalar. -/
theorem original_plaquette_signed_cayley_cleared
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
    let a := inverseChart n0 (chartSign_nonnegative u0)
    let b := inverseChart n1 (chartSign_nonnegative u1)
    let c := inverseChart n2 (chartSign_nonnegative u2)
    let d := inverseChart n3 (chartSign_nonnegative u3)
    let sector := plaquetteSign s0 s1 s2 s3
    cayleyDenominator 1 a b (neg3 c) (neg3 d) *
        (2 + -(2 * signedScalar sector
          (evalRatPoly (environment qs)
            (correctedSlabPlaquettePolynomial extent face).scalar))) ≈
      cayleyDeficit 1 a b (neg3 c) (neg3 d) := by
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
  let a := inverseChart n0 (chartSign_nonnegative u0)
  let b := inverseChart n1 (chartSign_nonnegative u1)
  let c := inverseChart n2 (chartSign_nonnegative u2)
  let d := inverseChart n3 (chartSign_nonnegative u3)
  let sector := plaquetteSign s0 s1 s2 s3
  have hchart :
      (plaquetteWord n0 n1 n2 n3).Equivalent
        (plaquetteWord (stereographic (scale3 1 a))
          (stereographic (scale3 1 b))
          (stereographic (scale3 1 c))
          (stereographic (scale3 1 d))) :=
    UnitNorm.mul_congr
      (UnitNorm.mul_congr
        (UnitNorm.mul_congr (signed_chart_pin u0) (signed_chart_pin u1))
        (UnitNorm.inv_congr (signed_chart_pin u2)))
      (UnitNorm.inv_congr (signed_chart_pin u3))
  have hsector :
      (plaquetteWord n0 n1 n2 n3).Equivalent
        (signed sector (plaquetteWord u0 u1 u2 u3)) :=
    plaquetteWord_signed s0 s1 s2 s3 u0 u1 u2 u3
  have hchartSector :
      (plaquetteWord (stereographic (scale3 1 a))
        (stereographic (scale3 1 b))
        (stereographic (scale3 1 c))
        (stereographic (scale3 1 d))).val.r ≈
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
      (plaquetteWord (stereographic (scale3 1 a))
        (stereographic (scale3 1 b))
        (stereographic (scale3 1 c))
        (stereographic (scale3 1 d))).val.r ≈
      signedScalar sector
        (evalRatPoly (environment qs)
          (correctedSlabPlaquettePolynomial extent face).scalar) :=
    Q'.eqv_trans _ _ _ hchartSector
      (signedScalar_congr sector (Q'.eqv_symm horiginal))
  exact Q'.eqv_trans _ _ _
    (mc (Q'.eqv_refl _)
      (ac (Q'.eqv_refl 2)
        (nc (mc (Q'.eqv_refl 2) (Q'.eqv_symm hscalar)))))
    (plaquetteWord_cayley_cleared 1 a b c d)

end YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyExtraction

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyExtraction.signFactor_mul_equivalent_signed
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyExtraction.signed_mul
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyExtraction.plaquetteWord_signed
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyExtraction.signed_chart_pin
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyExtraction.original_plaquette_signed_cayley_cleared
