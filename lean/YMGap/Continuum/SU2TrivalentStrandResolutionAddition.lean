/-
# Additivity of canonical SU(2) trivalent strand resolution

For two admissible triples, componentwise addition of the external labels
adds the three canonical strand-bundle multiplicities exactly.  This is the
local algebraic hinge behind a reversible component switch: selected and
unselected accepted subnetworks can be recombined without changing the union
of their face-to-face strand connections.

The proof does not manipulate half-difference formulas.  It adds the two
explicit strand resolutions and invokes uniqueness of the resolution at the
summed triple.  This exposes the structural reason for additivity and avoids
parity/division bookkeeping.

No global graph-invariance, switch decoder, posterior capacity, or mass-gap
claim is made here.

Constructive contract: natural-number data and equality only; no `Classical`,
choice, `native_decide`, `sorry`, new axiom, or noncomputable declaration.
-/

import YMGap.Continuum.SU2FusionSupportAddition
import YMGap.Continuum.SU2TrivalentStrandPeeling

namespace YMGap.Continuum.SU2TrivalentStrandResolutionAddition

set_option autoImplicit false

open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2FusionSupportAddition
open YMGap.Continuum.SU2TrivalentStrandPeeling

/-! ## 1. Add two explicit resolutions -/

/-- Componentwise addition of the three bundle counts resolves the
componentwise sum of the two admissible triples. -/
def addTrivalentStrandResolutions
    {a b c a' b' c' : Nat}
    (left : TrivalentStrandResolution a b c)
    (right : TrivalentStrandResolution a' b' c') :
    TrivalentStrandResolution (a + a') (b + b') (c + c') where
  ab := left.ab + right.ab
  bc := left.bc + right.bc
  ca := left.ca + right.ca
  a_balance := by
    have hleft := left.a_balance
    have hright := right.a_balance
    omega
  b_balance := by
    have hleft := left.b_balance
    have hright := right.b_balance
    omega
  c_balance := by
    have hleft := left.c_balance
    have hright := right.c_balance
    omega

@[simp] theorem TrivalentStrandResolution.add_ab
    {a b c a' b' c' : Nat}
    (left : TrivalentStrandResolution a b c)
    (right : TrivalentStrandResolution a' b' c') :
    (addTrivalentStrandResolutions left right).ab =
      left.ab + right.ab := rfl

@[simp] theorem TrivalentStrandResolution.add_bc
    {a b c a' b' c' : Nat}
    (left : TrivalentStrandResolution a b c)
    (right : TrivalentStrandResolution a' b' c') :
    (addTrivalentStrandResolutions left right).bc =
      left.bc + right.bc := rfl

@[simp] theorem TrivalentStrandResolution.add_ca
    {a b c a' b' c' : Nat}
    (left : TrivalentStrandResolution a b c)
    (right : TrivalentStrandResolution a' b' c') :
    (addTrivalentStrandResolutions left right).ca =
      left.ca + right.ca := rfl

/-! ## 2. The canonical resolver is a monoid map on admissible support -/

/-- The canonical resolution at the summed labels is literally the sum of
the two canonical resolutions. -/
theorem canonicalTrivalentStrandResolution_add
    {a b c a' b' c' : Nat}
    (hleft : fusionOK a b c = true)
    (hright : fusionOK a' b' c' = true) :
    canonicalTrivalentStrandResolution
        (a + a') (b + b') (c + c')
        (fusionOK_add hleft hright) =
      addTrivalentStrandResolutions
        (canonicalTrivalentStrandResolution a b c hleft)
        (canonicalTrivalentStrandResolution a' b' c' hright) :=
  TrivalentStrandResolution.unique _ _

/-- Exact additivity of the canonical `a-b` strand bundle. -/
theorem canonicalAB_add_of_fusionOK
    {a b c a' b' c' : Nat}
    (hleft : fusionOK a b c = true)
    (hright : fusionOK a' b' c' = true) :
    canonicalAB (a + a') (b + b') (c + c') =
      canonicalAB a b c + canonicalAB a' b' c' := by
  have hresolution := canonicalTrivalentStrandResolution_add hleft hright
  exact congrArg TrivalentStrandResolution.ab hresolution

/-- Exact additivity of the canonical `b-c` strand bundle. -/
theorem canonicalBC_add_of_fusionOK
    {a b c a' b' c' : Nat}
    (hleft : fusionOK a b c = true)
    (hright : fusionOK a' b' c' = true) :
    canonicalBC (a + a') (b + b') (c + c') =
      canonicalBC a b c + canonicalBC a' b' c' := by
  have hresolution := canonicalTrivalentStrandResolution_add hleft hright
  exact congrArg TrivalentStrandResolution.bc hresolution

/-- Exact additivity of the canonical `c-a` strand bundle. -/
theorem canonicalCA_add_of_fusionOK
    {a b c a' b' c' : Nat}
    (hleft : fusionOK a b c = true)
    (hright : fusionOK a' b' c' = true) :
    canonicalCA (a + a') (b + b') (c + c') =
      canonicalCA a b c + canonicalCA a' b' c' := by
  have hresolution := canonicalTrivalentStrandResolution_add hleft hright
  exact congrArg TrivalentStrandResolution.ca hresolution

/-! ## 3. Local strand adjacency is union-preserving -/

/-- Whether the canonical resolution contains at least one strand in the
displayed leg-pair bundle.  This is precisely the face-to-face adjacency
information retained after strand slots are forgotten. -/
def canonicalTrivalentStrandBundleSupportB
    (a b c : Nat) (hadmissible : fusionOK a b c = true)
    (pair : TrivalentStrandPair) : Bool :=
  decide (0 <
    (canonicalTrivalentStrandResolution a b c hadmissible).pairCount pair)

private theorem nat_add_positiveB (left right : Nat) :
    decide (0 < left + right) =
      (decide (0 < left) || decide (0 < right)) := by
  cases left <;> cases right <;> rfl

/-- Componentwise addition takes the union of local face-to-face strand
adjacencies.  Multiplicities add, so a summed bundle is nonempty exactly when
one of its two summand bundles is nonempty. -/
theorem canonicalTrivalentStrandBundleSupportB_add
    {a b c a' b' c' : Nat}
    (hleft : fusionOK a b c = true)
    (hright : fusionOK a' b' c' = true)
    (pair : TrivalentStrandPair) :
    canonicalTrivalentStrandBundleSupportB
        (a + a') (b + b') (c + c')
        (fusionOK_add hleft hright) pair =
      (canonicalTrivalentStrandBundleSupportB a b c hleft pair ||
        canonicalTrivalentStrandBundleSupportB a' b' c' hright pair) := by
  unfold canonicalTrivalentStrandBundleSupportB
  rw [canonicalTrivalentStrandResolution_add hleft hright]
  cases pair <;>
    exact nat_add_positiveB _ _

end YMGap.Continuum.SU2TrivalentStrandResolutionAddition

#print axioms YMGap.Continuum.SU2TrivalentStrandResolutionAddition.addTrivalentStrandResolutions
#print axioms YMGap.Continuum.SU2TrivalentStrandResolutionAddition.canonicalTrivalentStrandResolution_add
#print axioms YMGap.Continuum.SU2TrivalentStrandResolutionAddition.canonicalAB_add_of_fusionOK
#print axioms YMGap.Continuum.SU2TrivalentStrandResolutionAddition.canonicalBC_add_of_fusionOK
#print axioms YMGap.Continuum.SU2TrivalentStrandResolutionAddition.canonicalCA_add_of_fusionOK
#print axioms YMGap.Continuum.SU2TrivalentStrandResolutionAddition.canonicalTrivalentStrandBundleSupportB_add
