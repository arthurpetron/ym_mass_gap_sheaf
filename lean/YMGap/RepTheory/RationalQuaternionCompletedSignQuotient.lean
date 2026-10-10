/-
# The central sign quotient of the actual completed quaternion group

The ambient carrier is the already constructed Cauchy-quotient `Point`.  Its
two central signs are the actual embedded rational units.  The quotient below
has the same raw Point carrier and the central-coset setoid; no decidable
equality or total coset locator on completed points is assumed.

The kernel selector samples a supplied Cauchy row at a fixed rational
tolerance.  A kernel proof is eliminated only into propositions that certify
which of the two separated signs the sample identifies.  The resulting
Type-valued sign witness descends because it is unique.  This is an algebraic
finite-central-quotient presentation, not compact SO(3), a topological
quotient, Haar integration, or a representation-theoretic completeness claim.
-/

import YMGap.RepTheory.RationalQuaternionCauchyGroup
import YMGap.RepTheory.RationalQuaternionSignQuotient
import YMGap.RepTheory.LocatedCentralQuotient

namespace YMGap.RepTheory.RationalQuaternionCompletedSignQuotient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionCauchyGroup
open YMGap.RepTheory.RationalQuaternion.UnitNorm
open SquaredSeminorm

local infix:50 " ≈ " => Q'.eqv

/-- The literal embedded scalar sign on the original completed carrier. -/
def includeSign (z : QuaternionSign) : Point :=
  embed (UnitNorm.includeSign z)

def signInclusion : ConstructiveGroup.Hom QuaternionSign.group completedGroup where
  toFun := includeSign
  map_equivalent := by
    intro z t h
    change z = t at h
    cases h
    exact completedGroup.equivalent_refl _
  map_one := rfl
  map_mul := by
    intro z t
    exact completedGroup.equivalent_trans
      (rationalEmbedding.map_equivalent (UnitNorm.signInclusion.map_mul z t))
      (rationalEmbedding.map_mul (UnitNorm.includeSign z) (UnitNorm.includeSign t))

theorem includeSign_injective {z t : QuaternionSign}
    (h : completedGroup.Equivalent (includeSign z) (includeSign t)) :
    QuaternionSign.group.Equivalent z t := by
  have hr : (UnitNorm.includeSign z).Equivalent (UnitNorm.includeSign t) :=
    rationalEmbedding_semantic_injective h
  change z = t
  exact UnitNorm.includeSign_injective hr

private theorem pointwise_eq {X Y : CauchyPoint}
    (h : ∀ n, (X.seq n).Equivalent (Y.seq n)) :
    Quotient.mk chordSeminorm.completionSetoid X =
      Quotient.mk chordSeminorm.completionSetoid Y :=
  Quotient.sound ⟨NonexpansiveSemigroup.closeOfPointwiseNull
    (D := chordSeminorm) (fun n => (null_iff_semantic _ _).mpr (h n))⟩

theorem includeSign_central (z : QuaternionSign) (x : Point) :
    completedGroup.Equivalent (completedMul (includeSign z) x)
      (completedMul x (includeSign z)) := by
  refine Quotient.inductionOn x (fun X => ?_)
  change completedMul (includeSign z)
      (Quotient.mk chordSeminorm.completionSetoid X) =
    completedMul (Quotient.mk chordSeminorm.completionSetoid X)
      (includeSign z)
  exact pointwise_eq (fun n => UnitNorm.includeSign_central z (X.seq n))

/-- The finite subgroup is inside the SAME completed Point group. -/
def signCentralSubgroup : FiniteCentralSubgroup completedGroup where
  group := QuaternionSign.group
  finite := QuaternionSign.finite
  inclusion := signInclusion
  injective := includeSign_injective
  central := includeSign_central

/-- Coset equality of actual completed points, without a total locator. -/
def signQuotientGroup : ConstructiveGroup where
  Carrier := Point
  setoid := signCentralSubgroup.centralCosetSetoid
  one := completedOne
  mul := completedMul
  inv := completedInv
  mul_congr := by
    intro a b c d hab hcd
    apply hab.elim
    intro wab
    apply hcd.elim
    intro wcd
    exact ⟨signCentralSubgroup.centralCosetWitness_mul wab wcd⟩
  inv_congr := by
    intro x y hxy
    apply hxy.elim
    intro witness
    exact ⟨signCentralSubgroup.centralCosetWitness_inv witness⟩
  mul_assoc := fun a b c =>
    signCentralSubgroup.centralCosetEquivalent_of_equivalent
      (completedGroup.mul_assoc a b c)
  one_mul := fun a =>
    signCentralSubgroup.centralCosetEquivalent_of_equivalent
      (completedGroup.one_mul a)
  mul_one := fun a =>
    signCentralSubgroup.centralCosetEquivalent_of_equivalent
      (completedGroup.mul_one a)
  inv_mul := fun a =>
    signCentralSubgroup.centralCosetEquivalent_of_equivalent
      (completedGroup.inv_mul a)
  mul_inv := fun a =>
    signCentralSubgroup.centralCosetEquivalent_of_equivalent
      (completedGroup.mul_inv a)

/-- The quotient homomorphism is identity on representatives. -/
def signQuotientHom : ConstructiveGroup.Hom completedGroup signQuotientGroup where
  toFun := fun x => x
  map_equivalent := by
    intro x y hxy
    exact signCentralSubgroup.centralCosetEquivalent_of_equivalent hxy
  map_one := signCentralSubgroup.centralCosetEquivalent_of_equivalent
    (completedGroup.equivalent_refl completedOne)
  map_mul := fun x y => signCentralSubgroup.centralCosetEquivalent_of_equivalent
    (completedGroup.equivalent_refl (completedMul x y))

private def sixteenth : Q' := Q'.mkPos 1 16 (by decide)
private def quarter : Q' := Q'.mkPos 1 4 (by decide)
private theorem sixteenth_pos : (0 : Q') < sixteenth := by decide

/-- A rational query of the supplied row, with no selected Point representative. -/
def rowProbe (X : CauchyPoint) : UnitNorm := rowApproximation X sixteenth

private theorem constant_le_reflect {a b : Q'}
    (h : CReal.leEv (CReal.ofQ' a) (CReal.ofQ' b)) : a ≤ b := by
  apply Q'.le_of_le_add_mul_invSucc a b 1
  intro N
  obtain ⟨M, hM⟩ := h (Q'.invSucc N) (Q'.invSucc_pos N)
  have ht : a ≤ b + Q'.invSucc N := hM M (Nat.le_refl M)
  have he : b + Q'.ofNat 1 * Q'.invSucc N ≈ b + Q'.invSucc N := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (show Q'.ofNat 1 ≈ (1 : Q') by decide))
          (Q'.one_mul_eqv _)))
      (Q'.eqv_refl _)
  exact Q'.le_trans' _ _ _ ht (Q'.ge_of_eqv he)

private theorem rowProbe_close_of_eq (X : CauchyPoint) (s : UnitNorm)
    (h : (Quotient.mk chordSeminorm.completionSetoid X : Point) = embed s) :
    chord (rowProbe X) s ≤ quarter := by
  have hh : chordSeminorm.CompletionRel X (chordSeminorm.constant s) :=
    Quotient.exact h
  rcases hh with ⟨hc⟩
  let n := max (X.modulus sixteenth) (hc.modulus sixteenth)
  have hrow : chord (rowProbe X) (X.seq n) ≤ sixteenth :=
    rowApproximation_bound X sixteenth sixteenth_pos n (Nat.le_max_left _ _)
  have hclose : chord (X.seq n) s ≤ sixteenth := by
    have hn : hc.modulus sixteenth ≤ n := Nat.le_max_right _ _
    exact constant_le_reflect (hc.close sixteenth sixteenth_pos n hn)
  have hsum : (chord (rowProbe X) (X.seq n) +
      chord (rowProbe X) (X.seq n)) +
      (chord (X.seq n) s + chord (X.seq n) s) ≤
      (sixteenth + sixteenth) + (sixteenth + sixteenth) :=
    Q'.add_le_add (Q'.add_le_add hrow hrow)
      (Q'.add_le_add hclose hclose)
  exact Q'.le_trans' _ _ _ (chord_triangle _ (X.seq n) _)
    (Q'.le_trans' _ _ _ hsum (by decide))

/-- The one fixed probe cannot be within squared chord 1/4 of both signs. -/
private theorem probe_signs_disjoint (X : CauchyPoint)
    (hp : chord (rowProbe X) unitOne ≤ quarter)
    (hn : chord (rowProbe X) unitNegativeOne ≤ quarter) : False := by
  have hp' : chord unitOne (rowProbe X) ≤ quarter :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (chord_symm _ _)) hp
  have hb : chord unitOne unitNegativeOne ≤ (1 : Q') := by
    have hsum : (chord unitOne (rowProbe X) + chord unitOne (rowProbe X)) +
        (chord (rowProbe X) unitNegativeOne +
          chord (rowProbe X) unitNegativeOne) ≤
        (quarter + quarter) + (quarter + quarter) :=
      Q'.add_le_add (Q'.add_le_add hp' hp') (Q'.add_le_add hn hn)
    exact Q'.le_trans' _ _ _ (chord_triangle _ (rowProbe X) _)
      (Q'.le_trans' _ _ _ hsum (by decide))
  exact (by decide : ¬ chord unitOne unitNegativeOne ≤ (1 : Q')) hb

private theorem kernel_sign_cases (x : Point)
    (h : signCentralSubgroup.CentralCosetEquivalent x completedOne) :
    x = includeSign .positive ∨ x = includeSign .negative := by
  apply h.elim
  intro witness
  rcases witness with ⟨z, hz⟩
  have hsign : x = includeSign z :=
    hz.trans (completedOne_mul (includeSign z))
  cases z with
  | positive => exact Or.inl hsign
  | negative => exact Or.inr hsign

private instance witness_subsingleton (x : Point) :
    Subsingleton (signCentralSubgroup.WitnessFor x) where
  allEq := by
    intro a b
    rcases a with ⟨z, hz⟩
    rcases b with ⟨t, ht⟩
    have hzt : QuaternionSign.group.Equivalent z t :=
      signCentralSubgroup.injective (hz.symm.trans ht)
    change z = t at hzt
    cases hzt
    rfl

/-- The computed sign is justified using the truncated kernel proof only in
propositional subgoals; the returned sign comes from the rational row probe. -/
private def rawKernelWitness (X : CauchyPoint)
    (h : signCentralSubgroup.CentralCosetEquivalent
      (Quotient.mk chordSeminorm.completionSetoid X : Point) completedOne) :
    signCentralSubgroup.WitnessFor
      (Quotient.mk chordSeminorm.completionSetoid X : Point) := by
  let x : Point := Quotient.mk chordSeminorm.completionSetoid X
  if hp : chord (rowProbe X) unitOne ≤ quarter then
    have hx : x = includeSign .positive := by
      rcases kernel_sign_cases x h with hpos | hneg
      · exact hpos
      · exact False.elim (probe_signs_disjoint X hp
          (rowProbe_close_of_eq X unitNegativeOne hneg))
    exact ⟨QuaternionSign.positive, hx⟩
  else
    have hx : x = includeSign .negative := by
      rcases kernel_sign_cases x h with hpos | hneg
      · exact False.elim (hp (rowProbe_close_of_eq X unitOne hpos))
      · exact hneg
    exact ⟨QuaternionSign.negative, hx⟩

/-- A kernel proof gives a Type-valued, uniquely determined actual sign.
Dependent quotient recursion is valid because two distinct sign witnesses
cannot inhabit the same fiber. -/
def kernelSignWitness (x : Point)
    (h : signCentralSubgroup.CentralCosetEquivalent x completedOne) :
    signCentralSubgroup.WitnessFor x :=
  (Quotient.recOnSubsingleton
    (motive := fun y : Point =>
      signCentralSubgroup.CentralCosetEquivalent y completedOne →
        signCentralSubgroup.WitnessFor y)
    x (fun X => rawKernelWitness X)) h

/-- Exact algebraic quotient of the SAME completed quaternion group by its
two embedded scalar signs.  It is not a topological or compact-group claim. -/
def signQuotientPresentation :
    CentralQuotientPresentation completedGroup signQuotientGroup where
  gamma := signCentralSubgroup
  quotient_hom := signQuotientHom
  surjective_lift := fun g => ⟨g, signQuotientGroup.equivalent_refl g⟩
  kernel_to_gamma := fun x h => kernelSignWitness x h
  gamma_to_kernel := fun x witness =>
    signCentralSubgroup.centralCosetEquivalent_one_of_witness (x := x) witness

/-- The exact kernel has precisely the positive and negative completed signs. -/
theorem signKernel_iff (x : Point) :
    signQuotientGroup.Equivalent (signQuotientHom.toFun x) signQuotientGroup.one ↔
      x = includeSign .positive ∨ x = includeSign .negative := by
  constructor
  · exact kernel_sign_cases x
  · intro h
    cases h with
    | inl hp =>
        exact signCentralSubgroup.centralCosetEquivalent_one_of_witness
          (x := x) ⟨QuaternionSign.positive, hp⟩
    | inr hn =>
        exact signCentralSubgroup.centralCosetEquivalent_one_of_witness
          (x := x) ⟨QuaternionSign.negative, hn⟩

#print axioms includeSign
#print axioms signInclusion
#print axioms includeSign_injective
#print axioms includeSign_central
#print axioms signCentralSubgroup
#print axioms signQuotientGroup
#print axioms signQuotientHom
#print axioms rowProbe
#print axioms kernelSignWitness
#print axioms signQuotientPresentation
#print axioms signKernel_iff

end YMGap.RepTheory.RationalQuaternionCompletedSignQuotient
