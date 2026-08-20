/-
# Checked finite local support implications

This module packages a small reusable computer-science proof principle.  If
two natural-valued functions depend only on a finite duplicate-free scope,
then exhaustively checking every bounded labelling on that scope proves the
corresponding support implication for every ambient labelling bounded there.

The checker is executable.  Its soundness theorem reconstructs the restricted
labelling and is proved in Lean; an external program may propose checks, but
cannot enlarge the trusted base.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteScopedFactorTableCertificate

namespace YMGap.Continuum.FiniteLocalSupportImplicationCertificate

open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-- Exhaustively check that positive support of `antecedent` implies positive
support of `consequent` on every `0,...,K` labelling of `scope`. -/
def boundedLocalSupportImplicationCheck
    (K : Nat) (scope : List Nat)
    (antecedent consequent : EdgeLabelling → Nat) : Bool :=
  (boundedEdgeLabellings K scope).all fun labelling =>
    decide (antecedent labelling = 0 ∨ 0 < consequent labelling)

/-- Soundness of the executable local support-implication checker. -/
theorem localSupportImplication_of_check
    (K : Nat) (scope : List Nat)
    (antecedent consequent : EdgeLabelling → Nat)
    (hnodup : scope.Nodup)
    (hantecedentLocal : ∀ first second,
      (∀ id, id ∈ scope → first id = second id) →
        antecedent first = antecedent second)
    (hconsequentLocal : ∀ first second,
      (∀ id, id ∈ scope → first id = second id) →
        consequent first = consequent second)
    (hcheck : boundedLocalSupportImplicationCheck K scope
      antecedent consequent = true)
    (labelling : EdgeLabelling)
    (hbounded : ∀ id, id ∈ scope → labelling id < K + 1)
    (hpositive : 0 < antecedent labelling) :
    0 < consequent labelling := by
  let restricted := restrictEdgeLabelling scope labelling
  have hrestricted : restricted ∈ boundedEdgeLabellings K scope :=
    restrictEdgeLabelling_mem_bounded K labelling scope hbounded
  have hchecked : antecedent restricted = 0 ∨
      0 < consequent restricted := by
    exact of_decide_eq_true
      (List.all_eq_true.mp hcheck restricted hrestricted)
  have hagree : ∀ id, id ∈ scope → restricted id = labelling id :=
    restrictEdgeLabelling_agrees labelling scope hnodup
  have hantecedentEq : antecedent restricted = antecedent labelling :=
    hantecedentLocal restricted labelling hagree
  have hconsequentEq : consequent restricted = consequent labelling :=
    hconsequentLocal restricted labelling hagree
  rcases hchecked with hzero | hconsequent
  · rw [hantecedentEq] at hzero
    omega
  · rwa [hconsequentEq] at hconsequent

end YMGap.Continuum.FiniteLocalSupportImplicationCertificate

#print axioms
  YMGap.Continuum.FiniteLocalSupportImplicationCertificate.localSupportImplication_of_check
