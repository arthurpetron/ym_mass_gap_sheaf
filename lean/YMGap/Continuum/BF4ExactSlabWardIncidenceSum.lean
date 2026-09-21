/-
# Four-link incidence budget for physical plaquette gradients

A duplicate-free family of witnessed physical links can meet any one
physical plaquette at most four times.  Finite Fubini therefore charges the
sum of all incident nonnegative face weights at most four times the global
physical-face sum.  The specialization to coefficient squares retains every
signed coefficient before squaring.

The companion local estimate is the six-face finite Cauchy--Schwarz bound for
the absolute coefficients incident to one link.  These are finite lattice and
exact rational estimates only; no action, response, or analytic lower bound is
asserted.
-/

import YMGap.Continuum.BF4ExactSlabWardFamilyCost
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
import YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
import YMGap.Continuum.FiniteWeightedCartesianInjection
import YMGap.Continuum.RationalFiniteSparseGram
import YMGap.Continuum.Z4SpinDependentIncidenceProductBound
import YMGap.Continuum.Z4UnitCubeIncidenceParity
import YMGap.Continuum.GNSHilbertSpace

namespace YMGap.Continuum.BF4ExactSlabWardIncidenceSum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabWardFamilyCost
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4SpinDependentIncidenceProductBound
open YMGap.Continuum.Z4UnitCubeIncidenceParity

local infix:50 " ≈ " => Q'.eqv

/-- The members of a written physical-link family incident to one physical
face identifier. -/
def faceRow (extent id : Nat) (xs : List (PhysicalLink extent)) :
    List (PhysicalLink extent) :=
  xs.filter (fun link =>
    decide (link.val ∈ edgesOf (slabPlaquetteAt extent id)))

/-- A duplicate-free physical-link family meets a fixed face at most four
times.  Physicality of the face identifier is not needed for this raw
four-edge count. -/
theorem faceRow_length_le_four (extent id : Nat)
    (xs : List (PhysicalLink extent)) (hxs : xs.Nodup) :
    (faceRow extent id xs).length ≤ 4 := by
  let row := faceRow extent id xs
  have hrowNodup : row.Nodup := List.filter_sublist.nodup hxs
  have hmappedNodup : (row.map (fun link => link.val)).Nodup :=
    nodup_map_of_injOn (fun link : PhysicalLink extent => link.val) row hrowNodup
      (fun a _ b _ heq => Subtype.ext heq)
  have hmappedSubset : ∀ link, link ∈ row.map (fun item => item.val) →
      link ∈ edgesOf (slabPlaquetteAt extent id) := by
    intro link hlink
    obtain ⟨item, hitem, rfl⟩ := List.mem_map.mp hlink
    exact of_decide_eq_true (List.mem_filter.mp hitem).2
  have hlength := nodup_subset_length_le
    (row.map (fun link => link.val))
    (edgesOf (slabPlaquetteAt extent id)) hmappedNodup hmappedSubset
  rw [List.length_map, edgesOf_length] at hlength
  exact hlength

private theorem listQSum_le_termwise {A : Type} (left right : A → Q') :
    ∀ xs : List A, (∀ x, x ∈ xs → left x ≤ right x) →
      listQSum left xs ≤ listQSum right xs
  | [], _ => Q'.le_refl' 0
  | x :: xs, h =>
      Q'.add_le_add (h x List.mem_cons_self)
        (listQSum_le_termwise left right xs
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem faceRow_weight_le_four (extent id : Nat)
    (xs : List (PhysicalLink extent)) (hxs : xs.Nodup)
    (weight : Q') (hweight : (0 : Q') ≤ weight) :
    listQSum (fun _ : PhysicalLink extent => weight) (faceRow extent id xs) ≤
      Q'.ofNat 4 * weight := by
  let row := faceRow extent id xs
  have hrowNodup : row.Nodup := List.filter_sublist.nodup hxs
  have hbound := listQSum_le_of_injective_nodup row
    (edgesOf (slabPlaquetteAt extent id))
    (fun _ : PhysicalLink extent => weight) (fun _ : Z4Link => weight)
    (fun link => link.val) hrowNodup (edgesOf_nodup _)
    (fun link hlink => of_decide_eq_true (List.mem_filter.mp hlink).2)
    (fun a _ b _ heq => Subtype.ext heq)
    (fun _ _ => Q'.le_refl' weight) (fun _ _ => hweight)
  exact Q'.le_trans' _ _ _ hbound
    (Q'.le_of_eqv
      (Q'.eqv_trans _ (weight * Q'.ofNat 4) _
        (RationalFiniteSparseGram.listQSum_const weight _)
        (Q'.mul_comm_eqv weight (Q'.ofNat 4))))

private theorem inner_incident_eq_mask (extent : Nat)
    (weight : Nat → Q') (link : PhysicalLink extent) :
    listQSum weight (incidentIds extent link.val) ≈
      listQSum
        (finiteMaskedValue
          (fun id => decide (link.val ∈ edgesOf (slabPlaquetteAt extent id)))
          weight)
        (slabPhysicalFaceEdges extent) := by
  unfold incidentIds
  exact Q'.eqv_symm
    (listQSum_finiteMaskedValue_eqv_filter
      (fun id => decide (link.val ∈ edgesOf (slabPlaquetteAt extent id)))
      weight (slabPhysicalFaceEdges extent))

private theorem outer_face_eq_row (extent id : Nat)
    (weight : Nat → Q') (xs : List (PhysicalLink extent)) :
    listQSum
        (fun link => finiteMaskedValue
          (fun face => decide (link.val ∈ edgesOf (slabPlaquetteAt extent face)))
          weight id)
        xs ≈
      listQSum (fun _ : PhysicalLink extent => weight id)
        (faceRow extent id xs) := by
  change listQSum
      (finiteMaskedValue
        (fun link : PhysicalLink extent =>
          decide (link.val ∈ edgesOf (slabPlaquetteAt extent id)))
        (fun _ => weight id)) xs ≈ _
  exact listQSum_finiteMaskedValue_eqv_filter _ _ xs

/-- Generic four-incidence estimate: every nonnegative physical-face weight
is charged once for each selected endpoint link on that face, hence at most
four times globally. -/
theorem incidence_sum_le_four (extent : Nat)
    (xs : List (PhysicalLink extent)) (hxs : xs.Nodup)
    (weight : Nat → Q')
    (hweight : ∀ id, id ∈ slabPhysicalFaceEdges extent →
      (0 : Q') ≤ weight id) :
    listQSum
        (fun link => listQSum weight (incidentIds extent link.val)) xs ≤
      Q'.ofNat 4 * listQSum weight (slabPhysicalFaceEdges extent) := by
  let masked : PhysicalLink extent → Nat → Q' := fun link id =>
    finiteMaskedValue
      (fun face => decide (link.val ∈ edgesOf (slabPlaquetteAt extent face)))
      weight id
  have hrows : listQSum
      (fun id => listQSum (fun link => masked link id) xs)
      (slabPhysicalFaceEdges extent) ≤
      listQSum (fun id => Q'.ofNat 4 * weight id)
        (slabPhysicalFaceEdges extent) := by
    apply listQSum_le_termwise
    intro id hid
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (outer_face_eq_row extent id weight xs))
      (faceRow_weight_le_four extent id xs hxs (weight id) (hweight id hid))
  have hleft : listQSum
      (fun link => listQSum weight (incidentIds extent link.val)) xs ≈
      listQSum (fun id => listQSum (fun link => masked link id) xs)
        (slabPhysicalFaceEdges extent) := by
    exact Q'.eqv_trans _ _ _
      (listQSum_congr_on _ _ xs
        (fun link _ => inner_incident_eq_mask extent weight link))
      (Q'.eqv_symm (listQSum_swap masked xs (slabPhysicalFaceEdges extent)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hrows
      (Q'.le_of_eqv
        (listQSum_mul_left (Q'.ofNat 4) weight
          (slabPhysicalFaceEdges extent))))

/-- The incidence estimate specialized to the squared coefficients of the
whole signed plaquette observable. -/
theorem coefficient_square_incidence_le_four (extent : Nat)
    (c : Nat → Q') (xs : List (PhysicalLink extent)) (hxs : xs.Nodup) :
    listQSum
        (fun link => listQSum (fun id => c id * c id)
          (incidentIds extent link.val)) xs ≤
      Q'.ofNat 4 * listQSum (fun id => c id * c id)
        (slabPhysicalFaceEdges extent) :=
  incidence_sum_le_four extent xs hxs (fun id => c id * c id)
    (fun id _ => SumOfSquares.q_mul_self_nonneg (c id))

private theorem listQSum_map_local {A B : Type} (f : B → Q') (g : A → B) :
  ∀ xs : List A,
      listQSum f (xs.map g) = listQSum (fun x => f (g x)) xs
  | [] => rfl
  | x :: xs =>
      congrArg (fun tail => f (g x) + tail) (listQSum_map_local f g xs)

/-- The local absolute coefficient sum costs at most the six incident faces.
This is the precise l1-to-l2 estimate needed before the global four-incidence
count. -/
theorem incident_abs_sum_square_le_six (extent : Nat) (link : Z4Link)
    (c : Nat → Q') :
    listQSum (fun id => Q'.abs (c id)) (incidentIds extent link) *
        listQSum (fun id => Q'.abs (c id)) (incidentIds extent link) ≤
      Q'.ofNat 6 *
        listQSum (fun id => c id * c id) (incidentIds extent link) := by
  let values := (incidentIds extent link).map (fun id => Q'.abs (c id))
  have hcs :=
    BF4PhysicalFiniteVacuumSectorPathLengthEnergy.listQSum_square_le_length_mul_squareSum
      values
  have hcs' :
      listQSum (fun id => Q'.abs (c id)) (incidentIds extent link) *
          listQSum (fun id => Q'.abs (c id)) (incidentIds extent link) ≤
        Q'.ofNat (incidentIds extent link).length *
          listQSum (fun id => Q'.abs (c id) * Q'.abs (c id))
            (incidentIds extent link) := by
    simpa only [values, List.length_map, listQSum_map_local] using hcs
  have hsquares : listQSum (fun id => Q'.abs (c id) * Q'.abs (c id))
      (incidentIds extent link) ≈
      listQSum (fun id => c id * c id) (incidentIds extent link) :=
    listQSum_congr (fun id => Q'.abs_mul_self_eqv (c id)) _
  have hsum0 : (0 : Q') ≤
      listQSum (fun id => c id * c id) (incidentIds extent link) :=
    listQSum_nonnegative_on _ _
      (fun id _ => SumOfSquares.q_mul_self_nonneg (c id))
  have hlength : Q'.ofNat (incidentIds extent link).length ≤ Q'.ofNat 6 :=
    CReal.ofNat_le_ofNat (incidentIds_length_le_six extent link)
  exact Q'.le_trans' _ _ _ hcs'
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left (Q'.ofNat (incidentIds extent link).length) _ _
          hsquares))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hlength hsum0))

end YMGap.Continuum.BF4ExactSlabWardIncidenceSum

#print axioms YMGap.Continuum.BF4ExactSlabWardIncidenceSum.faceRow_length_le_four
#print axioms YMGap.Continuum.BF4ExactSlabWardIncidenceSum.incidence_sum_le_four
#print axioms YMGap.Continuum.BF4ExactSlabWardIncidenceSum.coefficient_square_incidence_le_four
#print axioms YMGap.Continuum.BF4ExactSlabWardIncidenceSum.incident_abs_sum_square_le_six
