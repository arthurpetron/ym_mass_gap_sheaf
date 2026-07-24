/-
# Summable distortion inherited from a pointwise majorant

RG-I9 needs more than a uniform `L1` bound: it needs a summable error stream
with a constructive tail modulus.  This module proves the exact transfer
principle used by the compact-dual remainder route.

If a nonnegative physical error stream is pointwise dominated by a stream
already carrying `SummableDistortion`, then it inherits:

* the same rational cap on every finite partial sum;
* the same computable tail modulus;
* the same finite-tail estimates; and
* pointwise vanishing after that modulus.

Thus the remaining analytic work is only the majorization inequality and the
construction of a summable majorant (for the proposed route, an
`s^64`-graded majorant).  No smallness is inferred from a bounded error.

## Axiom gate

Constructive exact-rational and finite-sum algebra only.  No `Classical.*`,
`sorry`, `native_decide`, custom axiom, quotient, or noncomputable
declaration is used.
-/

import YMGap.RG.StableDynamics

namespace YMGap.RG.DominatedSummableDistortion

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RG.StableDynamics

private theorem finSum_mono
    (lower upper : QSeq)
    (hterm : ∀ n, lower n ≤ upper n) :
    ∀ length, finSum lower length ≤ finSum upper length
  | 0 => Q'.le_refl' 0
  | length + 1 => by
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ _
          (finSum_mono lower upper hterm length))
        (Q'.add_le_add_left _ _ _
          (hterm length))

/-- Pointwise domination transfers a complete constructive summability
certificate without changing its cap or modulus. -/
def ofPointwiseDomination
    (term majorant : QSeq)
    (termNonnegative : ∀ n, (0 : Q') ≤ term n)
    (term_le : ∀ n, term n ≤ majorant n)
    (majorantBudget : SummableDistortion majorant) :
    SummableDistortion term where
  cap := majorantBudget.cap
  capNonnegative := majorantBudget.capNonnegative
  termNonnegative := termNonnegative
  partialSumBound := by
    intro length
    exact Q'.le_trans' _ _ _
      (finSum_mono term majorant term_le length)
      (majorantBudget.partialSumBound length)
  modulus := majorantBudget.modulus
  tailBound := by
    intro epsilon hepsilon start hstart length
    have htailTerms :
        ∀ offset,
          term (start + offset) ≤ majorant (start + offset) :=
      fun offset => term_le (start + offset)
    exact Q'.le_trans' _ _ _
      (finSum_mono
        (fun offset => term (start + offset))
        (fun offset => majorant (start + offset))
        htailTerms length)
      (majorantBudget.tailBound
        epsilon hepsilon start hstart length)

/-- A summable nonnegative stream vanishes pointwise with its own constructive
tail modulus. -/
theorem term_le_after_modulus
    {term : QSeq}
    (budget : SummableDistortion term)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (n : Nat) (hn : budget.modulus epsilon ≤ n) :
    term n ≤ epsilon := by
  have htail :=
    budget.tailBound epsilon hepsilon n hn 1
  change (0 : Q') + term n ≤ epsilon at htail
  rwa [Q'.zero_add'] at htail

/-- The dominated stream uses exactly the majorant's modulus. -/
theorem dominated_modulus_eq
    (term majorant : QSeq)
    (termNonnegative : ∀ n, (0 : Q') ≤ term n)
    (term_le : ∀ n, term n ≤ majorant n)
    (majorantBudget : SummableDistortion majorant)
    (epsilon : Q') :
    (ofPointwiseDomination term majorant termNonnegative
      term_le majorantBudget).modulus epsilon =
        majorantBudget.modulus epsilon :=
  rfl

#print axioms ofPointwiseDomination
#print axioms term_le_after_modulus
#print axioms dominated_modulus_eq

end YMGap.RG.DominatedSummableDistortion
