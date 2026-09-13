/-
# Separating-cut cancellation in the ORIGINAL connected numerator

Finite inclusion-exclusion is applied to the existing original connected
numerator as a function of its actual action-face list. If a selected set
admits a separating cut between the probes, every subselection inherits
that cut and has zero connected numerator. Its inclusion-exclusion
coefficient therefore vanishes. The exact sum can be filtered by the
computed separator search even though the FULL action need not split.

This supplies finite connected-support cancellation, not a bound on these
new coefficients, normalized summability, a path-length estimate or decay.
-/

import YMGap.Continuum.FiniteSelectionMobius
import YMGap.Continuum.BF4ExactSlabSelectionSeparation
import YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation

namespace YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

theorem connectedNumerator_perm (w : Q') (K extent : Nat) {xs ys : List Nat}
    (h : xs.Perm ys) (p q : RatPoly) :
    connectedNumerator w K extent xs p q ≈ connectedNumerator w K extent ys p q := by
  have he := polynomialProduct_perm (faceHeatPolynomial w K extent) h
  have hn (r : RatPoly) :
      numerator w (boundaryCompleteSlabLinks extent).length extent xs r K ≈
      numerator w (boundaryCompleteSlabLinks extent).length extent ys r K :=
    haar_of_coeff ((RatPolyCoeffEqv.refl r).mul he)
  exact Q'.add_eqv_congr' (qmul (hn (polyMul p q)) (haar_of_coeff he))
    (Q'.neg_eqv_congr _ _ (qmul (hn p) (hn q)))

def connectedCoefficient (w : Q') (K extent : Nat) (p q : RatPoly) (ids : List Nat) : Q' :=
  coefficient (fun ys => connectedNumerator w K extent ys p q) ids

def connectedSelections (extent : Nat) (left right : List Z4Link) (ids : List Nat) : List (List Nat) :=
  (selections ids).filter (keep extent left right)

theorem connectedNumerator_expansion (w : Q') (K extent : Nat) (p q : RatPoly) (ids : List Nat) :
    connectedNumerator w K extent ids p q ≈
      listQSum (connectedCoefficient w K extent p q) (selections ids) :=
  Q'.eqv_symm (reconstruct _ _)

section Local

variable (w : Q') (K extent : Nat) (p q : RatPoly) (left right : List Z4Link)
  (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
  (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
  (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)

include hp hq hl hr

theorem numerator_zero_of_separator (ids : List Nat) (S : Separator extent left right ids) :
    connectedNumerator w K extent ids p q ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (connectedNumerator_perm w K extent (cut_partition ids S.cut) p q))
    (connectedNumerator_zero w K extent (cutLeft ids S.cut) (cutRight ids S.cut) left right S.disjoint p q hp hq hl hr)

/-- The FULL slab can interact: only THIS selected set must have a separator. -/
theorem coefficient_zero_of_separator (ids : List Nat) (S : Separator extent left right ids) :
    connectedCoefficient w K extent p q ids ≈ 0 :=
  coefficient_zero_on _ _ (fun ys hy => numerator_zero_of_separator w K extent p q left right hp hq hl hr ys
    (S.restrict (fun id hid => selected_mem hy id hid)))

theorem coefficient_zero_of_discard (ids : List Nat) (hk : keep extent left right ids = false) :
    connectedCoefficient w K extent p q ids ≈ 0 := by
  cases he : findSeparator extent left right ids with
  | none => simp only [keep, he, Option.isNone] at hk; cases hk
  | some S => exact coefficient_zero_of_separator w K extent p q left right hp hq hl hr ids S

/-- Exact filtering by a computed support test, not a connectedness hypothesis. -/
theorem connectedNumerator_filtered (ids : List Nat) :
    connectedNumerator w K extent ids p q ≈
      listQSum (connectedCoefficient w K extent p q) (connectedSelections extent left right ids) :=
  reconstruct_filtered _ _ _ (fun ys _ hk => coefficient_zero_of_discard w K extent p q left right hp hq hl hr ys hk)

end Local

theorem retained_no_separating_cut {extent : Nat} {left right : List Z4Link} {ids selected : List Nat}
    (hs : selected ∈ connectedSelections extent left right ids) (cut : List Nat) (hc : cut ∈ selections selected) :
    ¬LinksDisjoint (left ++ faceLinks extent (cutLeft selected cut))
      (right ++ faceLinks extent (cutRight selected cut)) :=
  keep_no_cut (List.mem_filter.mp hs).2 cut hc

end YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion

#print axioms YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion.connectedNumerator_perm
#print axioms YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion.connectedCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion.connectedSelections
#print axioms YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion.connectedNumerator_expansion
#print axioms YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion.numerator_zero_of_separator
#print axioms YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion.coefficient_zero_of_separator
#print axioms YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion.coefficient_zero_of_discard
#print axioms YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion.connectedNumerator_filtered
#print axioms YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion.retained_no_separating_cut
