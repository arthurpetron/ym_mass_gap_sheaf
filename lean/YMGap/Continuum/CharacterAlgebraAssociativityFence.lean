/-
# Lowest-channel character-carrier fence

`RGTransport.charAlg` stores only a spin label and defines multiplication by
the lowest Clebsch--Gordan channel `|a-b|`.  That operation is useful as a
single-channel carrier surrogate, but it is not the SU(2) representation-ring
product: the latter is a sum of all admissible fusion channels.  In fact the
stored binary operation is not associative.  This file banks the smallest
closed counterexample so downstream arguments cannot silently treat
`charAlg` (or its pointwise multi-edge lift) as an associative observable
algebra.
-/

import YMGap.Continuum.RGTransport

namespace YMGap.Continuum.CharacterAlgebraAssociativityFence

open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.RGTransport

private def spin (n : Nat) : charAlg.carrier := n

/-- The exact counterexample `(1⋆1)⋆2 = 2`, while `1⋆(1⋆2) = 0`. -/
theorem charAlg_lowest_channel_counterexample :
    charAlg.mul (charAlg.mul (spin 1) (spin 1)) (spin 2) = spin 2 ∧
      charAlg.mul (spin 1) (charAlg.mul (spin 1) (spin 2)) = spin 0 := by
  exact ⟨rfl, rfl⟩

/-- Consequently the lowest-channel projection used by `charAlg.mul` is not
associative and must not be identified with the SU(2) character algebra
product. -/
theorem charAlg_mul_not_associative :
    ¬ (∀ a b c : Nat,
      charAlg.mul (charAlg.mul a b) c =
        charAlg.mul a (charAlg.mul b c)) := by
  intro h
  have h112 := h 1 1 2
  change (2 : Nat) = 0 at h112
  exact (by decide : (2 : Nat) ≠ 0) h112

#print axioms charAlg_lowest_channel_counterexample
#print axioms charAlg_mul_not_associative

end YMGap.Continuum.CharacterAlgebraAssociativityFence
