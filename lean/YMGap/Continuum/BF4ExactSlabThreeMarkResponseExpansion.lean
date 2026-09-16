/-
# Three-mark cancellation in the ORIGINAL signed face response

Finite inclusion-exclusion is applied to the actual cleared covariance
response. A coefficient vanishes if a literal link cut separates either
probe from the other probe and inserted face, or separates the inserted
face from both probes. Each separator restricts to every subselection.
The original response therefore equals the computed three-test filtered
sum at every rational nome and finite cutoff, without positivity.

The last theorem transports a SUPPLIED bound on this same signed sum to
the existing original cutoff-limit covariance. No coefficient bound or
spatial decay is proved here. Detached spectator components may still
contribute partition factors to raw coefficients: the filter does NOT
assert that every retained face belongs to one connected component.
-/

import YMGap.Continuum.BF4ExactSlabResponseProbeSeparation
import YMGap.Continuum.BF4ExactSlabResponseInsertionSeparation
import YMGap.Continuum.FiniteSelectionMobius

namespace YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabResponseProbeSeparation
open YMGap.Continuum.BF4ExactSlabResponseInsertionSeparation
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-- Actual finite differences of the SAME signed original response. -/
def responseCoefficient (w : Q') (K extent id : Nat) (p q : RatPoly) (ids : List Nat) : Q' :=
  coefficient (fun ys => response w K extent ys id p q) ids

/-- Keep only selections for which none of the three mark cuts is found. -/
def responseKeep (extent id : Nat) (left right : List Z4Link) (ids : List Nat) : Bool :=
  let face := edgesOf (slabPlaquetteAt extent id)
  keep extent left (right++face) ids &&
    (keep extent right (left++face) ids && keep extent (left++right) face ids)

def responseSelections (extent id : Nat) (left right : List Z4Link) (ids : List Nat) : List (List Nat) :=
  (selections ids).filter (responseKeep extent id left right)

section Local

variable (w : Q') (K extent : Nat) (p q : RatPoly) (left right : List Z4Link)
  (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
  (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
  (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)

include hp hq hl hr

private theorem coefficient_zero_left (ids : List Nat) (id : Nat)
    (S : Separator extent left (right++edgesOf (slabPlaquetteAt extent id)) ids) :
    responseCoefficient w K extent id p q ids ≈ 0 :=
  coefficient_zero_on _ _ (fun ys hy =>
    response_zero_of_left_separator w K extent p q left right hp hq hl hr ys id
      (S.restrict (fun j hj => selected_mem hy j hj)))

private theorem coefficient_zero_right (ids : List Nat) (id : Nat)
    (S : Separator extent right (left++edgesOf (slabPlaquetteAt extent id)) ids) :
    responseCoefficient w K extent id p q ids ≈ 0 :=
  coefficient_zero_on _ _ (fun ys hy =>
    response_zero_of_right_separator w K extent p q left right hp hq hl hr ys id
      (S.restrict (fun j hj => selected_mem hy j hj)))

private theorem coefficient_zero_insertion (ids : List Nat) (id : Nat)
    (S : Separator extent (left++right) (edgesOf (slabPlaquetteAt extent id)) ids) :
    responseCoefficient w K extent id p q ids ≈ 0 :=
  coefficient_zero_on _ _ (fun ys hy =>
    response_zero_of_insertion_separator w K extent p q left right hp hq hl hr ys id
      (S.restrict (fun j hj => selected_mem hy j hj)))

/-- An actual separator, inherited by all subselections, kills the
coefficient BEFORE any absolute-value estimate or division. -/
theorem responseCoefficient_zero_of_discard (ids : List Nat) (id : Nat)
    (hk : responseKeep extent id left right ids = false) :
    responseCoefficient w K extent id p q ids ≈ 0 := by
  cases hleft : findSeparator extent left (right++edgesOf (slabPlaquetteAt extent id)) ids with
  | some S => exact coefficient_zero_left w K extent p q left right hp hq hl hr ids id S
  | none =>
    cases hright : findSeparator extent right (left++edgesOf (slabPlaquetteAt extent id)) ids with
    | some S => exact coefficient_zero_right w K extent p q left right hp hq hl hr ids id S
    | none =>
      cases hins : findSeparator extent (left++right) (edgesOf (slabPlaquetteAt extent id)) ids with
      | some S => exact coefficient_zero_insertion w K extent p q left right hp hq hl hr ids id S
      | none => simp only [responseKeep, keep, hleft, hright, hins, Option.isNone,
          Bool.true_and] at hk; cases hk

/-- Exact finite response reconstruction with all three mark cuts removed.
The full original action need not split, and its covariance need not vanish. -/
theorem response_filtered (ids : List Nat) (id : Nat) :
    response w K extent ids id p q ≈
      listQSum (responseCoefficient w K extent id p q) (responseSelections extent id left right ids) :=
  reconstruct_filtered _ _ _ (fun ys _ hk =>
    responseCoefficient_zero_of_discard w K extent p q left right hp hq hl hr ys id hk)

end Local

/-- Operational geometry of every retained selection: all three searched
mark bipartitions have no separating cut. Spectator components are allowed. -/
theorem retained_three_no_cuts {extent id : Nat} {left right : List Z4Link} {ids selected : List Nat}
    (hs : selected ∈ responseSelections extent id left right ids)
    (cut : List Nat) (hc : cut ∈ selections selected) :
    (¬LinksDisjoint (left++faceLinks extent (cutLeft selected cut))
      ((right++edgesOf (slabPlaquetteAt extent id))++faceLinks extent (cutRight selected cut))) ∧
    (¬LinksDisjoint (right++faceLinks extent (cutLeft selected cut))
      ((left++edgesOf (slabPlaquetteAt extent id))++faceLinks extent (cutRight selected cut))) ∧
    (¬LinksDisjoint ((left++right)++faceLinks extent (cutLeft selected cut))
      (edgesOf (slabPlaquetteAt extent id)++faceLinks extent (cutRight selected cut))) := by
  have hk := (List.mem_filter.mp hs).2
  have ht := (Bool.and_eq_true _ _).mp hk
  have hu := (Bool.and_eq_true _ _).mp ht.2
  exact ⟨keep_no_cut ht.1 cut hc, keep_no_cut hu.1 cut hc, keep_no_cut hu.2 cut hc⟩

/-- A supplied bound on the FILTERED SIGNED SUM, with the actual two
partition squares, feeds the existing original covariance limit. This
does not supply the spatially decaying bound or discard spectator factors. -/
theorem covariance_response_bound_of_filtered (w : Q')
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent : Nat)
    (ids : List Nat) (hi : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)
    (id : Nat) (hid : id ∈ slabPhysicalFaceEdges extent)
    (p q : RatPoly) (left right : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (b : Q') (K0 : Nat)
    (h : ∀ K, K0 ≤ K → Q'.abs (listQSum (responseCoefficient w K extent id p q)
      (responseSelections extent id left right ids)) ≤ b*responseDenominator w K extent ids id) :
    CReal.leEv (CReal.abs (CReal.sub
      (covariance w hw0 hw1 extent (ids++[id])
        (fun j hj => by
          rcases List.mem_append.mp hj with hj | hj
          · exact hi j hj
          · have he := List.mem_singleton.mp hj
            subst j
            exact hid) p q)
      (covariance w hw0 hw1 extent ids hi p q))) (CReal.ofQ' b) :=
  covariance_response_bound_eventually w hw0 hw1 extent ids hi id hid p q b K0
    (fun K hK => Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr (response_filtered w K extent p q left right hp hq hl hr ids id)))
      (h K hK))

/-- A disconnected spectator insertion leaves the actual cutoff-removed
covariance unchanged, even if the probes remain correlated with each other.
This is finite-volume original-action invariance, not spatial decay. -/
theorem covariance_invariant_of_insertion_separator (w : Q')
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent : Nat)
    (ids : List Nat) (hi : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)
    (id : Nat) (hid : id ∈ slabPhysicalFaceEdges extent)
    (p q : RatPoly) (left right : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (S : Separator extent (left++right) (edgesOf (slabPlaquetteAt extent id)) ids) :
    CReal.Equiv
      (covariance w hw0 hw1 extent (ids++[id])
        (fun j hj => by
          rcases List.mem_append.mp hj with hj | hj
          · exact hi j hj
          · have he := List.mem_singleton.mp hj
            subst j
            exact hid) p q)
      (covariance w hw0 hw1 extent ids hi p q) := by
  have hzero := covariance_response_bound_eventually w hw0 hw1 extent ids hi id hid p q 0 0
    (fun K _ => Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr
        (response_zero_of_insertion_separator w K extent p q left right hp hq hl hr ids id S)))
      (Q'.ge_of_eqv (QPoly.q_zero_mul _)))
  exact CReal.Equiv_of_abs_sub_le_all_pos
    (fun epsilon he => CReal.leRat_mono hzero (Q'.le_of_lt he))

end YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion

#print axioms YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion.responseCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion.responseKeep
#print axioms YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion.responseSelections
#print axioms YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion.responseCoefficient_zero_of_discard
#print axioms YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion.response_filtered
#print axioms YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion.retained_three_no_cuts
#print axioms YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion.covariance_response_bound_of_filtered
#print axioms YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion.covariance_invariant_of_insertion_separator
