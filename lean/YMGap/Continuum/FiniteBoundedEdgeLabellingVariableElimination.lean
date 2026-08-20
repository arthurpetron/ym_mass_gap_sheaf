/-
# Bounded edge labellings as finite words

The BF4 finite-cutoff carrier is enumerated by `boundedEdgeLabellings`, while
the generic variable-elimination checker is stated over fixed-length words.
This file gives an exact constructive bridge between those two presentations.

The bridge is an equality of lists, not only an extensional equality of finite
sets.  It therefore preserves enumeration order and multiplicity.  Exact sums
and zero-seeded maxima over BF4 edge labellings can consequently be certified
by the generic elimination and branch-and-bound traces without trusting an
external decoder or a cardinality argument.

This remains a finite-cutoff computation theorem.  It makes no claim about
cutoff-uniformity, infinite volume, a continuum measure, or a mass gap.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteVariableEliminationCertificate
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

namespace YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteVariableEliminationCertificate
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## Boolean masks for filtered finite carriers -/

/-- Extend a value on a Boolean-filtered carrier by zero to the full list. -/
def finiteMaskedValue {Item : Type}
    (test : Item → Bool) (value : Item → Q') (item : Item) : Q' :=
  if test item then value item else 0

/-- Summing a zero extension over the full list is exactly the same, up to
the rational setoid, as summing the original value over the filtered list. -/
theorem listQSum_finiteMaskedValue_eqv_filter
    {Item : Type} (test : Item → Bool) (value : Item → Q') :
    ∀ items : List Item,
      listQSum (finiteMaskedValue test value) items ≈
        listQSum value (items.filter test)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      cases htest : test head with
      | false =>
          simp only [finiteMaskedValue, htest, Bool.false_eq_true,
            ↓reduceIte, List.filter_cons, listQSum]
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr'
              (Q'.eqv_refl 0)
              (listQSum_finiteMaskedValue_eqv_filter test value tail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [finiteMaskedValue, htest, ↓reduceIte,
            List.filter_cons, listQSum]
          exact Q'.add_eqv_congr'
            (Q'.eqv_refl (value head))
            (listQSum_finiteMaskedValue_eqv_filter test value tail)

/-- Decode a word by assigning its entries to the listed edges in order.
The mismatch branches are irrelevant on `allSeqs ... edges.length`, but make
the decoder total and executable. -/
def wordToEdgeLabelling : List Nat → List Nat → EdgeLabelling
  | [], _ => zeroEdgeLabelling
  | _ :: _, [] => zeroEdgeLabelling
  | edge :: rest, spin :: spins =>
      setEdgeLabel (wordToEdgeLabelling rest spins) edge spin

/-- The recursive BF4 bounded-labelling enumeration is exactly the image of
the generic fixed-length word enumeration under the executable decoder. -/
theorem boundedEdgeLabellings_eq_map_allSeqs (K : Nat) : ∀ edges : List Nat,
    boundedEdgeLabellings K edges =
      (allSeqs (K + 1) edges.length).map
        (wordToEdgeLabelling edges)
  | [] => rfl
  | edge :: rest => by
      simp only [boundedEdgeLabellings, List.length_cons, allSeqs,
        boundedEdgeLabellings_eq_map_allSeqs K rest,
        List.map_flatMap, List.map_map]
      apply congrArg
        (fun family : Nat → List EdgeLabelling =>
          (List.range (K + 1)).flatMap family)
      funext spin
      apply List.map_congr_left
      intro word _hword
      rfl

/-- Exact sums over bounded edge labellings are fixed-length word sums. -/
theorem listQSum_boundedEdgeLabellings_eqv_finiteAssignmentSum
    (K : Nat) (edges : List Nat) (value : EdgeLabelling → Q') :
    listQSum value (boundedEdgeLabellings K edges) ≈
      finiteAssignmentSum (K + 1) edges.length
        (fun word => value (wordToEdgeLabelling edges word)) := by
  rw [boundedEdgeLabellings_eq_map_allSeqs]
  unfold finiteAssignmentSum
  exact Q'.eqv_of_eq
    (listQSum_map value (wordToEdgeLabelling edges)
      (allSeqs (K + 1) edges.length))

/-- A checked exact variable-elimination trace for decoded words certifies the
corresponding full BF4 bounded-edge-labelling sum. -/
theorem listQSum_boundedEdgeLabellings_eqv_certificateBottom
    {K : Nat} {edges : List Nat} {value : EdgeLabelling → Q'}
    (certificate : ExactVariableEliminationCertificate
      (K + 1) edges.length
      (fun word => value (wordToEdgeLabelling edges word))) :
    listQSum value (boundedEdgeLabellings K edges) ≈
      certificate.table 0 [] := by
  exact Q'.eqv_trans _ _ _
    (listQSum_boundedEdgeLabellings_eqv_finiteAssignmentSum K edges value)
    certificate.assignmentSum_eqv_bottom

private theorem finiteListMaxZero_map
    {A B : Type} (value : B → Q') (decode : A → B) : ∀ words : List A,
    finiteListMaxZero value (words.map decode) =
      finiteListMaxZero (fun word => value (decode word)) words
  | [] => rfl
  | _ :: words => by
      simp only [List.map, finiteListMaxZero]
      rw [finiteListMaxZero_map value decode words]

/-- Zero-seeded maxima over bounded edge labellings are the corresponding
fixed-length word maxima. -/
theorem finiteListMaxZero_boundedEdgeLabellings_eq_finiteAssignmentMaxZero
    (K : Nat) (edges : List Nat) (value : EdgeLabelling → Q') :
    finiteListMaxZero value (boundedEdgeLabellings K edges) =
      finiteAssignmentMaxZero (K + 1) edges.length
        (fun word => value (wordToEdgeLabelling edges word)) := by
  rw [boundedEdgeLabellings_eq_map_allSeqs]
  unfold finiteAssignmentMaxZero
  exact finiteListMaxZero_map value (wordToEdgeLabelling edges)
    (allSeqs (K + 1) edges.length)

/-- A checked branch-and-bound trace for decoded words bounds the full
zero-seeded maximum over BF4 bounded edge labellings. -/
theorem finiteListMaxZero_boundedEdgeLabellings_le_certificateBottom
    {K : Nat} {edges : List Nat} {value : EdgeLabelling → Q'}
    (certificate : VariableEliminationUpperBoundCertificate
      (K + 1) edges.length
      (fun word => value (wordToEdgeLabelling edges word))) :
    finiteListMaxZero value (boundedEdgeLabellings K edges) ≤
      certificate.table 0 [] := by
  rw [finiteListMaxZero_boundedEdgeLabellings_eq_finiteAssignmentMaxZero]
  exact certificate.assignmentMax_le_bottom

end YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination.listQSum_finiteMaskedValue_eqv_filter
#print axioms
  YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination.boundedEdgeLabellings_eq_map_allSeqs
#print axioms
  YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination.listQSum_boundedEdgeLabellings_eqv_certificateBottom
#print axioms
  YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination.finiteListMaxZero_boundedEdgeLabellings_le_certificateBottom
