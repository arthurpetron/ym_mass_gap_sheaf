/-
# Literal corrected-slab plaquette deficit

Every original slab link is assigned the supplied rational unit quaternion
at its ORIGINAL boundary-complete link index, or the original identity
fallback. Reversal is unit-quaternion inversion. Pointwise polynomial
evaluation is pinned to the four-factor Hamilton word, including the
initial identity in the original fold. The resulting scalar deficit is at
most four times the sum of the four actual link scalar deficits.

The assignment is shared: repeated links use the same value. No physical
membership, distinctness, commutation, independence, or Haar-only identity
is assumed. This supplies the literal-word input for a local-Casimir
small-region estimate, not a region-mass, partition, entropy, H1, or gap bound.
-/

import YMGap.Continuum.BF4ExactSlabOriginalHeatHaarOrder
import YMGap.RepTheory.RationalQuaternionFourFactorDeficit

namespace YMGap.Continuum.BF4ExactSlabPlaquetteDeficit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionNormRepair (coordinate)
open YMGap.RepTheory.RationalQuaternionFourFactorDeficit (four_factor_deficit)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq PolyExpr)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS (evalRatPoly_var)
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment environment_coordinate)

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩

private theorem ac {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a+c ≈ b+d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h) (Q'.add_eqv_congr_left _ _ _ k)

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem nc {a b : Q'} (h : a ≈ b) : -a ≈ -b := Q'.neg_eqv_congr _ _ h

/-- The existing polynomial evaluator's coordinate record of an actual unit. -/
def unitValue (u : UnitNorm) : QuaternionValue := ⟨u.val.r,u.val.i,u.val.j,u.val.k⟩

/-- Original shared link assignment, with precisely the original fallback. -/
def linkValue (extent : Nat) (qs : Nat → UnitNorm) (link : Z4Link) : UnitNorm :=
  if link ∈ boundaryCompleteSlabLinks extent then
    qs ((boundaryCompleteSlabLinks extent).idxOf link)
  else unitOne

/-- Orientation changes the assigned unit by its actual group inverse. -/
def orientedLinkValue (extent : Nat) (qs : Nat → UnitNorm)
    (entry : OrientedBF4Link) : UnitNorm :=
  if entry.reverse then UnitNorm.inv (linkValue extent qs entry.link)
  else linkValue extent qs entry.link

/-- The exact left-associated four-factor word, in original plaquette order. -/
def plaquetteValue (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) : UnitNorm :=
  let a := (dirsOf face.2).1
  let b := (dirsOf face.2).2
  UnitNorm.mul
    (UnitNorm.mul
      (UnitNorm.mul (linkValue extent qs (face.1,a))
        (linkValue extent qs (addE face.1 a,b)))
      (UnitNorm.inv (linkValue extent qs (addE face.1 b,a))))
    (UnitNorm.inv (linkValue extent qs (face.1,b)))

private theorem value_trans {a b c : QuaternionValue}
    (h : QuaternionValue.Eqv a b) (k : QuaternionValue.Eqv b c) :
    QuaternionValue.Eqv a c :=
  ⟨Q'.eqv_trans _ _ _ h.scalar k.scalar, Q'.eqv_trans _ _ _ h.iPart k.iPart,
   Q'.eqv_trans _ _ _ h.jPart k.jPart, Q'.eqv_trans _ _ _ h.kPart k.kPart⟩

private theorem unitValue_congr {a b : UnitNorm} (h : a.Equivalent b) :
    QuaternionValue.Eqv (unitValue a) (unitValue b) :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩

private theorem value_mul_congr {a b c d : QuaternionValue}
    (h : QuaternionValue.Eqv a b) (k : QuaternionValue.Eqv c d) :
    QuaternionValue.Eqv (QuaternionValue.mul a c) (QuaternionValue.mul b d) :=
  ⟨ac (mc h.scalar k.scalar) (nc (ac (mc h.iPart k.iPart)
      (ac (mc h.jPart k.jPart) (mc h.kPart k.kPart)))),
   ac (mc h.scalar k.iPart) (ac (mc h.iPart k.scalar)
      (ac (mc h.jPart k.kPart) (nc (mc h.kPart k.jPart)))),
   ac (mc h.scalar k.jPart) (ac (mc h.jPart k.scalar)
      (ac (mc h.kPart k.iPart) (nc (mc h.iPart k.kPart)))),
   ac (mc h.scalar k.kPart) (ac (mc h.kPart k.scalar)
      (ac (mc h.iPart k.jPart) (nc (mc h.jPart k.iPart))))⟩

private theorem unitValue_mul (a b : UnitNorm) :
    QuaternionValue.Eqv (QuaternionValue.mul (unitValue a) (unitValue b))
      (unitValue (UnitNorm.mul a b)) := by
  constructor
  · exact poly_identity_of_normal_eq
      (.var 0 + -(.var 1+(.var 2+.var 3)))
      ((.var 0 + -(.var 1))+(-(.var 2)+ -(.var 3))) (by decide)
      (fun | 0 => a.val.r*b.val.r | 1 => a.val.i*b.val.i | 2 => a.val.j*b.val.j | _ => a.val.k*b.val.k)
  · exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
  · exact poly_identity_of_normal_eq
      (.var 0+(.var 1+(.var 2 + -(.var 3))))
      ((.var 0 + -(.var 3))+(.var 1+.var 2)) (by decide)
      (fun | 0 => a.val.r*b.val.j | 1 => a.val.j*b.val.r | 2 => a.val.k*b.val.i | _ => a.val.i*b.val.k)
  · exact poly_identity_of_normal_eq
      (.var 0+(.var 1+(.var 2 + -(.var 3))))
      ((.var 0+.var 2)+(-(.var 3)+.var 1)) (by decide)
      (fun | 0 => a.val.r*b.val.k | 1 => a.val.k*b.val.r | 2 => a.val.i*b.val.j | _ => a.val.j*b.val.i)

private theorem mul_pin {rho : Nat → Q'} {p q : PolyQuaternion} {a b : UnitNorm}
    (hp : QuaternionValue.Eqv (evalPolyQuaternion rho p) (unitValue a))
    (hq : QuaternionValue.Eqv (evalPolyQuaternion rho q) (unitValue b)) :
    QuaternionValue.Eqv (evalPolyQuaternion rho (PolyQuaternion.mul p q))
      (unitValue (UnitNorm.mul a b)) :=
  value_trans (evalPolyQuaternion_mul rho p q)
    (value_trans (value_mul_congr hp hq) (unitValue_mul a b))

private theorem conj_pin {rho : Nat → Q'} {p : PolyQuaternion} {a : UnitNorm}
    (hp : QuaternionValue.Eqv (evalPolyQuaternion rho p) (unitValue a)) :
    QuaternionValue.Eqv (evalPolyQuaternion rho (PolyQuaternion.conj p))
      (unitValue (UnitNorm.inv a)) :=
  value_trans (evalPolyQuaternion_conj rho p)
    ⟨hp.scalar,nc hp.iPart,nc hp.jPart,nc hp.kPart⟩

private theorem coordinate_pin (qs : Nat → UnitNorm) (block : Nat) :
    QuaternionValue.Eqv
      (evalPolyQuaternion (environment qs) (PolyQuaternion.coordinateVariable block))
      (unitValue (qs block)) := by
  have hc (a : Fin 4) : evalRatPoly (environment qs) (polyVar (4*block+a.val)) ≈
      coordinate (qs block).val a :=
    Q'.eqv_trans _ _ _ (evalRatPoly_var _ _) (Q'.eqv_of_eq (environment_coordinate qs block a))
  constructor
  · simpa only [evalPolyQuaternion,PolyQuaternion.coordinateVariable,unitValue,coordinate,Nat.add_zero]
      using hc ⟨0,by decide⟩
  · simpa only [evalPolyQuaternion,PolyQuaternion.coordinateVariable,unitValue,coordinate]
      using hc ⟨1,by decide⟩
  · simpa only [evalPolyQuaternion,PolyQuaternion.coordinateVariable,unitValue,coordinate]
      using hc ⟨2,by decide⟩
  · simpa only [evalPolyQuaternion,PolyQuaternion.coordinateVariable,unitValue,coordinate]
      using hc ⟨3,by decide⟩

/-- Literal coordinatewise evaluation, including out-of-carrier identity. -/
theorem link_eval (extent : Nat) (qs : Nat → UnitNorm) (link : Z4Link) :
    QuaternionValue.Eqv
      (evalPolyQuaternion (environment qs) (correctedSlabLinkPolynomial extent link))
      (unitValue (linkValue extent qs link)) := by
  cases (inferInstance : Decidable (link ∈ boundaryCompleteSlabLinks extent)) with
  | isTrue h =>
      rw [correctedSlabLinkPolynomial_of_mem h,linkValue,if_pos h]
      exact coordinate_pin qs _
  | isFalse h =>
      rw [correctedSlabLinkPolynomial_of_not_mem h,linkValue,if_neg h]
      exact evalPolyQuaternion_one _

/-- Original reversal is precisely inversion of the SAME assigned unit. -/
theorem oriented_link_eval (extent : Nat) (qs : Nat → UnitNorm) (entry : OrientedBF4Link) :
    QuaternionValue.Eqv
      (evalPolyQuaternion (environment qs) (orientedCorrectedSlabLinkPolynomial extent entry))
      (unitValue (orientedLinkValue extent qs entry)) := by
  unfold orientedCorrectedSlabLinkPolynomial orientedLinkValue
  cases entry.reverse
  · exact link_eval extent qs entry.link
  · exact conj_pin (link_eval extent qs entry.link)

private theorem four_pin {rho : Nat → Q'} {p q r s : PolyQuaternion} {a b c d : UnitNorm}
    (hp : QuaternionValue.Eqv (evalPolyQuaternion rho p) (unitValue a))
    (hq : QuaternionValue.Eqv (evalPolyQuaternion rho q) (unitValue b))
    (hr : QuaternionValue.Eqv (evalPolyQuaternion rho r) (unitValue c))
    (hs : QuaternionValue.Eqv (evalPolyQuaternion rho s) (unitValue d)) :
    QuaternionValue.Eqv
      (evalPolyQuaternion rho
        (PolyQuaternion.mul (PolyQuaternion.mul
          (PolyQuaternion.mul (PolyQuaternion.mul PolyQuaternion.one p) q) r) s))
      (unitValue (UnitNorm.mul (UnitNorm.mul (UnitNorm.mul a b) c) d)) := by
  have hone : QuaternionValue.Eqv (evalPolyQuaternion rho PolyQuaternion.one)
      (unitValue unitOne) := evalPolyQuaternion_one rho
  have hp' := value_trans (mul_pin hone hp) (unitValue_congr (UnitNorm.one_mul a))
  exact mul_pin (mul_pin (mul_pin hp' hq) hr) hs

private theorem four_scalar_pin {rho : Nat → Q'} {p q r s : PolyQuaternion}
    {a b c d : UnitNorm}
    (hp : QuaternionValue.Eqv (evalPolyQuaternion rho p) (unitValue a))
    (hq : QuaternionValue.Eqv (evalPolyQuaternion rho q) (unitValue b))
    (hr : QuaternionValue.Eqv (evalPolyQuaternion rho r) (unitValue c))
    (hs : QuaternionValue.Eqv (evalPolyQuaternion rho s) (unitValue d)) :
    evalRatPoly rho
        (PolyQuaternion.mul (PolyQuaternion.mul
          (PolyQuaternion.mul (PolyQuaternion.mul PolyQuaternion.one p) q) r) s).scalar ≈
      (UnitNorm.mul (UnitNorm.mul (UnitNorm.mul a b) c) d).val.r :=
  (four_pin hp hq hr hs).scalar

/-- Scalar of the original ordered polynomial fold, with no Haar quotient. -/
theorem plaquette_scalar_pin (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    evalRatPoly (environment qs) (correctedSlabPlaquettePolynomial extent face).scalar ≈
      (plaquetteValue extent qs face).val.r := by
  let e0 : OrientedBF4Link := ⟨(face.1,(dirsOf face.2).1),false⟩
  let e1 : OrientedBF4Link := ⟨(addE face.1 (dirsOf face.2).1,(dirsOf face.2).2),false⟩
  let e2 : OrientedBF4Link := ⟨(addE face.1 (dirsOf face.2).2,(dirsOf face.2).1),true⟩
  let e3 : OrientedBF4Link := ⟨(face.1,(dirsOf face.2).2),true⟩
  have hpoly : correctedSlabPlaquettePolynomial extent face =
      PolyQuaternion.mul
        (PolyQuaternion.mul
          (PolyQuaternion.mul
            (PolyQuaternion.mul PolyQuaternion.one (orientedCorrectedSlabLinkPolynomial extent e0))
            (orientedCorrectedSlabLinkPolynomial extent e1))
          (orientedCorrectedSlabLinkPolynomial extent e2))
        (orientedCorrectedSlabLinkPolynomial extent e3) := rfl
  have hunit : plaquetteValue extent qs face =
      UnitNorm.mul
        (UnitNorm.mul
          (UnitNorm.mul (orientedLinkValue extent qs e0) (orientedLinkValue extent qs e1))
          (orientedLinkValue extent qs e2))
        (orientedLinkValue extent qs e3) := rfl
  have h := four_scalar_pin
    (oriented_link_eval extent qs e0) (oriented_link_eval extent qs e1)
    (oriented_link_eval extent qs e2) (oriented_link_eval extent qs e3)
  rw [hpoly,hunit]
  exact h

private theorem deficit_congr {a b : Q'} (h : a ≈ b) : 1 + -a ≈ 1 + -b :=
  Q'.add_eqv_congr_left 1 _ _ (nc h)

/-- The literal plaquette deficit is controlled by its FOUR actual link
deficits. Reversed factors have the same scalar as their unreversed links.
Shared/repeated variables and every original identity fallback are retained. -/
theorem plaquette_deficit (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    let rho := environment qs
    let a := (dirsOf face.2).1
    let b := (dirsOf face.2).2
    1 + -evalRatPoly rho (correctedSlabPlaquettePolynomial extent face).scalar ≤
      4*(((1 + -evalRatPoly rho (correctedSlabLinkPolynomial extent (face.1,a)).scalar)+
           (1 + -evalRatPoly rho (correctedSlabLinkPolynomial extent (addE face.1 a,b)).scalar))+
         ((1 + -evalRatPoly rho (correctedSlabLinkPolynomial extent (addE face.1 b,a)).scalar)+
           (1 + -evalRatPoly rho (correctedSlabLinkPolynomial extent (face.1,b)).scalar))) := by
  have hword := four_factor_deficit
    (linkValue extent qs (face.1,(dirsOf face.2).1))
    (linkValue extent qs (addE face.1 (dirsOf face.2).1,(dirsOf face.2).2))
    (UnitNorm.inv (linkValue extent qs (addE face.1 (dirsOf face.2).2,(dirsOf face.2).1)))
    (UnitNorm.inv (linkValue extent qs (face.1,(dirsOf face.2).2)))
  have hp := deficit_congr (plaquette_scalar_pin extent qs face)
  have hl (link : Z4Link) :
      1 + -(linkValue extent qs link).val.r ≈
        1 + -evalRatPoly (environment qs) (correctedSlabLinkPolynomial extent link).scalar :=
    deficit_congr (Q'.eqv_symm (link_eval extent qs link).scalar)
  have hsum := ac
    (ac (hl (face.1,(dirsOf face.2).1)) (hl (addE face.1 (dirsOf face.2).1,(dirsOf face.2).2)))
    (ac (hl (addE face.1 (dirsOf face.2).2,(dirsOf face.2).1)) (hl (face.1,(dirsOf face.2).2)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
    (Q'.le_trans' _ _ _ hword (Q'.le_of_eqv (Q'.mul_eqv_congr_left 4 _ _ hsum)))

#print axioms unitValue
#print axioms linkValue
#print axioms orientedLinkValue
#print axioms plaquetteValue
#print axioms link_eval
#print axioms oriented_link_eval
#print axioms plaquette_scalar_pin
#print axioms plaquette_deficit

end YMGap.Continuum.BF4ExactSlabPlaquetteDeficit
