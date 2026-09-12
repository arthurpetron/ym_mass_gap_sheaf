/-
# One carrier for original boundary observables with different cutoffs

Each coefficient function carries an explicit finite label cutoff and a
proof that it vanishes beyond that cutoff. Addition uses the maximum of
the two supplied witnesses. Equality is pointwise rational equivalence,
independent of which cutoff witness was supplied.

Every original finite-cutoff coefficient function has a specified image,
using the already-proved Boolean zero extension. This is an observable
carrier, not an assumed physical-time realization or a frontier package.
-/

import YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit

namespace YMGap.Continuum.BF4ExactSlabFiniteBoundaryObservable

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding

local infix:50 " ≈ " => Q'.eqv

theorem labelWithin_mono {small large : Nat} (h : small ≤ large)
    (state : EdgeLabelling) (ht : labelWithinB small (centralLowerFaceIds 0) state = true) :
    labelWithinB large (centralLowerFaceIds 0) state = true :=
  (labelWithinB_true_iff _ _ _).mpr (fun id hid =>
    Nat.lt_of_lt_of_le ((labelWithinB_true_iff _ _ _).mp ht id hid) (Nat.succ_le_succ h))

theorem outside_of_le {small large : Nat} (h : small ≤ large)
    (state : EdgeLabelling) (ht : labelWithinB large (centralLowerFaceIds 0) state = false) :
    labelWithinB small (centralLowerFaceIds 0) state = false := by
  cases hs : labelWithinB small (centralLowerFaceIds 0) state with
  | false => rfl
  | true =>
    have he := labelWithin_mono h state hs
    rw [ht] at he
    exact Bool.noConfusion he

/-- The cutoff is data, not a witness extracted from a propositional existence. -/
structure BoundaryObservable where
  cutoff : Nat
  coefficient : EdgeLabelling → Q'
  outside : ∀ state, labelWithinB cutoff (centralLowerFaceIds 0) state = false → coefficient state ≈ 0

namespace BoundaryObservable

def CoefficientEqv (a b : BoundaryObservable) : Prop := ∀ state, a.coefficient state ≈ b.coefficient state

def zero : BoundaryObservable where
  cutoff := 0
  coefficient := fun _ => 0
  outside := fun _ _ => Q'.eqv_refl _

def add (a b : BoundaryObservable) : BoundaryObservable where
  cutoff := max a.cutoff b.cutoff
  coefficient := fun state => a.coefficient state + b.coefficient state
  outside := fun state h => Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (a.outside state (outside_of_le (Nat.le_max_left _ _) state h))
      (b.outside state (outside_of_le (Nat.le_max_right _ _) state h)))
    (Q'.eqv_of_eq (Q'.zero_add' _))

def neg (a : BoundaryObservable) : BoundaryObservable where
  cutoff := a.cutoff
  coefficient := fun state => -a.coefficient state
  outside := fun state h => Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (a.outside state h))
    (by decide : (-(0 : Q')) ≈ 0)

def smul (s : Q') (a : BoundaryObservable) : BoundaryObservable where
  cutoff := a.cutoff
  coefficient := fun state => s * a.coefficient state
  outside := fun state h => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (a.outside state h))
    (Q'.mul_zero_eqv _)

/-- Every old finite observable has an explicit image in the common carrier. -/
def ofCoefficients (cutoff : Nat) (c : EdgeLabelling → Q') : BoundaryObservable where
  cutoff := cutoff
  coefficient := boundaryExtension cutoff 0 c
  outside := fun _ h => Q'.eqv_of_eq (boundaryExtension_outside cutoff 0 c h)

theorem ofCoefficients_on_anchor (cutoff : Nat) (c : EdgeLabelling → Q')
    {state : EdgeLabelling} (hs : state ∈ centralHalfStates cutoff 0) :
    (ofCoefficients cutoff c).coefficient state = c state :=
  boundaryExtension_on_anchor cutoff 0 c hs

/-- A larger anchor does not change this coefficient function even up to
the rational representation's harmless zero terms. -/
theorem extension_eqv (a : BoundaryObservable) (anchor : Nat) (ha : a.cutoff ≤ anchor)
    (state : EdgeLabelling) :
    boundaryExtension anchor 0 a.coefficient state ≈ a.coefficient state := by
  cases ht : labelWithinB anchor (centralLowerFaceIds 0) state with
  | false =>
    rw [boundaryExtension_outside anchor 0 a.coefficient ht]
    exact Q'.eqv_symm (a.outside state (outside_of_le ha state ht))
  | true =>
    simp only [boundaryExtension, ht, ↓reduceIte]
    exact Q'.eqv_refl _

end BoundaryObservable
end YMGap.Continuum.BF4ExactSlabFiniteBoundaryObservable

#print axioms YMGap.Continuum.BF4ExactSlabFiniteBoundaryObservable.labelWithin_mono
#print axioms YMGap.Continuum.BF4ExactSlabFiniteBoundaryObservable.outside_of_le
#print axioms YMGap.Continuum.BF4ExactSlabFiniteBoundaryObservable.BoundaryObservable.zero
#print axioms YMGap.Continuum.BF4ExactSlabFiniteBoundaryObservable.BoundaryObservable.add
#print axioms YMGap.Continuum.BF4ExactSlabFiniteBoundaryObservable.BoundaryObservable.neg
#print axioms YMGap.Continuum.BF4ExactSlabFiniteBoundaryObservable.BoundaryObservable.smul
#print axioms YMGap.Continuum.BF4ExactSlabFiniteBoundaryObservable.BoundaryObservable.ofCoefficients
#print axioms YMGap.Continuum.BF4ExactSlabFiniteBoundaryObservable.BoundaryObservable.ofCoefficients_on_anchor
#print axioms YMGap.Continuum.BF4ExactSlabFiniteBoundaryObservable.BoundaryObservable.extension_eqv
