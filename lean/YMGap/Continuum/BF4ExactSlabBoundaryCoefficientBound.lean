/-
# A cutoff-independent finite majorant for the ORIGINAL boundary numerator

The selected exterior remainder contributes delta(w)^|S| and the actual
interior connected Mobius coefficient contributes kappa(w)^|T|. Summing
these bounds over the existing separating-cut filtered expansion yields
an explicit rational majorant with NO cutoff parameter.

The finite majorant still depends on volume, probe support/cap and nome.
Retained selections may include additional disconnected spectator pieces.
Neither geometric distance decay nor cancellation against the two original
partition factors is proved here; normalized summability remains open.
-/

import YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound
import YMGap.Continuum.BF4ExactSlabBoundaryConnectingSelections

namespace YMGap.Continuum.BF4ExactSlabBoundaryCoefficientBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
open YMGap.Continuum.BF4ExactSlabBoundaryConnectingSelections
open YMGap.Continuum.BF4ExactSlabRemainderExpansion
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

theorem sum_abs_bound_on {A : Type} (f g : A → Q') : ∀ xs : List A,
    (∀ x, x ∈ xs → Q'.abs (f x) ≤ g x) → Q'.abs (listQSum f xs) ≤ listQSum g xs
  | [], _ => by change Q'.abs (0 : Q') ≤ 0; decide
  | x :: xs, h => Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.add_le_add (h x List.mem_cons_self) (sum_abs_bound_on f g xs (fun y hy => h y (List.mem_cons_of_mem x hy))))

def summandCap (w c : Q') (exterior interior : List Nat) : Q' :=
  (c*(heatRemainderBound w)^exterior.length+c*(heatRemainderBound w)^exterior.length)*
    (pairedHeatRate w)^interior.length

def responseMajorant (w : Q') (half padding : Nat) (c : Q') (links : List Z4Link) (exterior : List Nat) : Q' :=
  listQSum (summandCap w c exterior)
    (connectedSelections (centralExtent (half+padding)) links
      (faceLinks (centralExtent (half+padding)) exterior) (interiorIds half padding))

def boundaryMajorant (w : Q') (half padding : Nat) (c : Q') (links : List Z4Link) : Q' :=
  listQSum (responseMajorant w half padding c links) (selections (exteriorIds half padding))

section SmallNome

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hsmall : heatRatio w ≤ HalfPow.half)
include hw0 hw1 hsmall

theorem boundarySummand_bound (K extent : Nat) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks extent).length p c) (exterior interior : List Nat)
    (he : ∀ id, id ∈ exterior → id ∈ slabPhysicalFaceEdges extent)
    (hi : ∀ id, id ∈ interior → id ∈ slabPhysicalFaceEdges extent) :
    Q'.abs (connectedCoefficient w K extent p (remainderProduct w K extent exterior) interior) ≤
      summandCap w c exterior interior :=
  connectedCoefficient_bound hw0 hw1 hsmall K extent p (remainderProduct w K extent exterior)
    c ((heatRemainderBound w)^exterior.length) P (productInterval hw0 hw1 hsmall K extent exterior he) interior hi

theorem connectingResponse_bound (K half padding : Nat) (p : RatPoly) (c : Q') (links : List Z4Link)
    (P : Interval (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p c)
    (exterior : List Nat) (he : exterior ∈ selections (exteriorIds half padding)) :
    Q'.abs (connectingResponse w K half padding p links exterior) ≤ responseMajorant w half padding c links exterior := by
  apply sum_abs_bound_on
  intro interior hi
  apply boundarySummand_bound hw0 hw1 hsmall K (centralExtent (half+padding)) p c P exterior interior
  · intro id hid
    exact (List.mem_filter.mp (selected_mem he id hid)).1
  · intro id hid
    exact (List.mem_filter.mp (selected_mem (List.mem_filter.mp hi).1 id hid)).1

/-- The existing original boundary determinant, with a computed finite bound
independent of K. Volume and nome dependence remain explicit in the majorant. -/
theorem boundaryNumerator_bound (K half padding : Nat) (p : RatPoly) (c : Q') (links : List Z4Link)
    (P : Interval (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p c)
    (hl : LinkLocal (centralExtent (half+padding)) links p) :
    Q'.abs (boundaryNumerator w half padding p K) ≤ boundaryMajorant w half padding c links :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr
    (boundaryNumerator_connecting_expansion w K half padding p links P.support hl)))
    (sum_abs_bound_on _ _ _ (fun exterior he => connectingResponse_bound hw0 hw1 hsmall K half padding p c links P exterior he))

end SmallNome
end YMGap.Continuum.BF4ExactSlabBoundaryCoefficientBound

#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCoefficientBound.sum_abs_bound_on
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCoefficientBound.summandCap
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCoefficientBound.responseMajorant
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCoefficientBound.boundaryMajorant
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCoefficientBound.boundarySummand_bound
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCoefficientBound.connectingResponse_bound
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCoefficientBound.boundaryNumerator_bound
