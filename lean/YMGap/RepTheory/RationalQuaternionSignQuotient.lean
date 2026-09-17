/-
# The full rational unit-quaternion carrier modulo its two scalar signs

Construct the actual finite central subgroup {+1,-1} of ALL rational unit
quaternions, not just the eight-element basis-unit fixture. Decidable
coordinatewise rational equality supplies a finite-search locator. The
existing central-quotient construction then provides an exact kernel,
explicit representative lifts, and a constructive representation-descent
consumer. Quotient equivalence is characterized by its two sign cases.

This is an algebraic setoid presentation on rational unit-quaternion points.
It is NOT a compact SO(3) realization, a proof that every rational rotation
has a rational unit-quaternion lift, a topology, a Haar functional, or any
per-group Yang--Mills action, limiting theory, or analytic gap.
-/

import YMGap.RepTheory.RationalQuaternionUnitNormGroup
import YMGap.RepTheory.QuaternionSign
import YMGap.RepTheory.LocatedCentralQuotient

universe u

namespace YMGap.RepTheory.RationalQuaternion.UnitNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

-- A genuine scalar quaternion commutes with every raw quaternion. The
-- reflected identities concern only five rational coordinates, not a
-- finite enumeration of the ambient unit-quaternion carrier.
private theorem scalar_central (c : Q') (x : RationalQuaternion) :
    (RationalQuaternion.mul (scalar c) x).Equivalent
      (RationalQuaternion.mul x (scalar c)) := by
  let e : Nat → Q' := fun | 0 => c | 1 => x.r | 2 => x.i | 3 => x.j | _ => x.k
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.const 0) (.var 2))))
        (.add (.neg (.mul (.const 0) (.var 3))) (.neg (.mul (.const 0) (.var 4)))))
      (.add (.add (.mul (.var 1) (.var 0)) (.neg (.mul (.var 2) (.const 0))))
        (.add (.neg (.mul (.var 3) (.const 0))) (.neg (.mul (.var 4) (.const 0)))))
      (by decide) e
  · exact poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 2)) (.mul (.const 0) (.var 1)))
        (.add (.mul (.const 0) (.var 4)) (.neg (.mul (.const 0) (.var 3)))))
      (.add (.add (.mul (.var 1) (.const 0)) (.mul (.var 2) (.var 0)))
        (.add (.mul (.var 3) (.const 0)) (.neg (.mul (.var 4) (.const 0)))))
      (by decide) e
  · exact poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.const 0) (.var 4))))
        (.add (.mul (.const 0) (.var 1)) (.mul (.const 0) (.var 2))))
      (.add (.add (.mul (.var 1) (.const 0)) (.neg (.mul (.var 2) (.const 0))))
        (.add (.mul (.var 3) (.var 0)) (.mul (.var 4) (.const 0))))
      (by decide) e
  · exact poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 4)) (.mul (.const 0) (.var 3)))
        (.add (.neg (.mul (.const 0) (.var 2))) (.mul (.const 0) (.var 1))))
      (.add (.add (.mul (.var 1) (.const 0)) (.mul (.var 2) (.const 0)))
        (.add (.neg (.mul (.var 3) (.const 0))) (.mul (.var 4) (.var 0))))
      (by decide) e

/-- Include the two actual scalar units in the full rational carrier. -/
def includeSign : QuaternionSign → UnitNorm
  | .positive => unitOne
  | .negative => unitNegativeOne

/-- The scalar-sign inclusion is a homomorphism of the actual groups. -/
def signInclusion : ConstructiveGroup.Hom QuaternionSign.group group where
  toFun := includeSign
  map_equivalent := by
    intro x y h
    change x = y at h
    cases h
    exact group.equivalent_refl _
  map_one := group.equivalent_refl _
  map_mul := by
    intro x y
    cases x <;> cases y <;>
      change RationalQuaternion.Equivalent _ _ <;> unfold RationalQuaternion.Equivalent <;> decide

/-- Included scalar signs commute with EVERY rational unit quaternion. -/
theorem includeSign_central (z : QuaternionSign) (x : UnitNorm) :
    (mul (includeSign z) x).Equivalent (mul x (includeSign z)) := by
  cases z with
  | positive => exact group.equivalent_trans (one_mul x) (group.equivalent_symm (mul_one x))
  | negative =>
      have hs : unitNegativeOne.val.Equivalent (scalar (-1)) := by unfold RationalQuaternion.Equivalent; decide
      exact RationalQuaternion.semanticSetoid.iseqv.trans
        (RationalQuaternion.mul_congr hs (RationalQuaternion.semanticSetoid.iseqv.refl x.val))
        (RationalQuaternion.semanticSetoid.iseqv.trans (scalar_central (-1) x.val)
          (RationalQuaternion.mul_congr (RationalQuaternion.semanticSetoid.iseqv.refl x.val)
            (RationalQuaternion.semanticSetoid.iseqv.symm hs)))

/-- Semantic injectivity of the actual two scalar units. -/
theorem includeSign_injective {z t : QuaternionSign}
    (h : (includeSign z).Equivalent (includeSign t)) : z = t := by
  cases z with
  | positive =>
      cases t with
      | positive => rfl
      | negative => exact False.elim ((by decide : ¬ ((1 : Q') ≈ -1)) h.1)
  | negative =>
      cases t with
      | positive => exact False.elim ((by decide : ¬ ((-1 : Q') ≈ 1)) h.1)
      | negative => rfl

/-- The explicit finite central sign subgroup on the entire rational carrier. -/
def signCentralSubgroup : FiniteCentralSubgroup group where
  group := QuaternionSign.group
  finite := QuaternionSign.finite
  inclusion := signInclusion
  injective := includeSign_injective
  central := includeSign_central

/-- Finite search computes an actual sign witness or refutes both cases. -/
def signLocator : signCentralSubgroup.Locator :=
  FiniteCentralSubgroup.Locator.ofDecidableEquivalent signCentralSubgroup
    decidableEquivalent

/-- Algebraic located quotient by the two scalar signs. -/
def signLocatedQuotientGroup : ConstructiveGroup :=
  signCentralSubgroup.locatedCentralQuotientGroup signLocator

/-- Exact quotient: identity lifts and computable sign-kernel witnesses. -/
def signLocatedQuotientPresentation :
    CentralQuotientPresentation group signLocatedQuotientGroup :=
  signCentralSubgroup.locatedCentralQuotientPresentation signLocator

/-- No extra representatives are identified: precisely the two sign cosets.
The second branch is literal right multiplication by the negative unit. -/
theorem signCoset_iff (x y : UnitNorm) :
    signLocatedQuotientGroup.Equivalent x y ↔
      x.Equivalent y ∨ x.Equivalent (mul y unitNegativeOne) := by
  constructor
  · intro h
    obtain ⟨⟨z, hz⟩⟩ := h
    cases z with
    | positive => exact Or.inl (group.equivalent_trans hz (mul_one y))
    | negative => exact Or.inr hz
  · intro h
    cases h with
    | inl hxy => exact signCentralSubgroup.centralCosetEquivalent_of_equivalent hxy
    | inr hxy => exact ⟨⟨QuaternionSign.negative, hxy⟩⟩

/-- An explicit imaginary unit, used to exclude a collapsed quotient. -/
def signQuotientWitness : UnitNorm :=
  ⟨basisI, by unfold IsUnitNorm; decide⟩

/-- The constructed quotient is nontrivial on actual quaternion points. -/
theorem signQuotientWitness_ne_one :
    ¬ signLocatedQuotientGroup.Equivalent signQuotientWitness unitOne := by
  intro h
  rcases (signCoset_iff signQuotientWitness unitOne).mp h with hp | hn
  · exact (by decide : ¬ ((1 : Q') ≈ 0)) hp.2.1
  · have hz : signQuotientWitness.Equivalent unitNegativeOne :=
      group.equivalent_trans hn (one_mul unitNegativeOne)
    exact (by decide : ¬ ((1 : Q') ≈ -0)) hz.2.1

/-- Concrete consumer of the existing representation-descent construction.
For this actual quotient only the negative-unit test remains; identity
preservation supplies the positive-unit case automatically. -/
def descendSignRepresentation {target : ConstructiveGroup.{u}}
    (rho : ConstructiveGroup.Hom group target)
    (hnegative : target.Equivalent (rho.toFun unitNegativeOne) target.one) :
    ConstructiveGroup.Hom signLocatedQuotientGroup target :=
  signLocatedQuotientPresentation.descendRepresentation rho (by
    intro z
    cases z with
    | positive => exact rho.map_one
    | negative => exact hnegative)

/-- Descent uses the same representatives and recovers the original map. -/
theorem descendSignRepresentation_pin {target : ConstructiveGroup.{u}}
    (rho : ConstructiveGroup.Hom group target)
    (hnegative : target.Equivalent (rho.toFun unitNegativeOne) target.one)
    (x : UnitNorm) :
    target.Equivalent
      ((descendSignRepresentation rho hnegative).toFun
        (signLocatedQuotientPresentation.quotient_hom.toFun x))
      (rho.toFun x) :=
  target.equivalent_refl _

end YMGap.RepTheory.RationalQuaternion.UnitNorm

#print axioms YMGap.RepTheory.RationalQuaternion.UnitNorm.includeSign
#print axioms YMGap.RepTheory.RationalQuaternion.UnitNorm.signInclusion
#print axioms YMGap.RepTheory.RationalQuaternion.UnitNorm.includeSign_central
#print axioms YMGap.RepTheory.RationalQuaternion.UnitNorm.includeSign_injective
#print axioms YMGap.RepTheory.RationalQuaternion.UnitNorm.signCentralSubgroup
#print axioms YMGap.RepTheory.RationalQuaternion.UnitNorm.signLocator
#print axioms YMGap.RepTheory.RationalQuaternion.UnitNorm.signLocatedQuotientGroup
#print axioms YMGap.RepTheory.RationalQuaternion.UnitNorm.signLocatedQuotientPresentation
#print axioms YMGap.RepTheory.RationalQuaternion.UnitNorm.signCoset_iff
#print axioms YMGap.RepTheory.RationalQuaternion.UnitNorm.signQuotientWitness
#print axioms YMGap.RepTheory.RationalQuaternion.UnitNorm.signQuotientWitness_ne_one
#print axioms YMGap.RepTheory.RationalQuaternion.UnitNorm.descendSignRepresentation
#print axioms YMGap.RepTheory.RationalQuaternion.UnitNorm.descendSignRepresentation_pin
