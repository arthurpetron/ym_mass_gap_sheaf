/-
# Volume-local normalization of the ORIGINAL resummed response

The detached spectator action is retained, not replaced by a whole-volume
partition floor. Restoring its removed collar costs headFloor(w) once per
face at each old endpoint and once per collar face plus the inserted face
at each new endpoint. The resulting fourth-power comparison has a positive
computable cost depending only on the nome and the collar size.

The existing four-dimensional incidence bound replaces that size by
6*(roots.length+4*anchor.length). The nome-dependent cutoff and floor remain
explicit. No spatial decay, summable coefficient bound, coupling-uniform
floor, OS contraction, or continuum conclusion is asserted.
-/

import YMGap.Continuum.BF4ExactSlabResponseSpectatorFactorization
import YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
import YMGap.Continuum.BF4ExactSlabCollarDegreeBound
import YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound

namespace YMGap.Continuum.BF4ExactSlabResponseCollarNormalization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabCollarDegreeBound
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabResponseSpectatorFactorization
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

/-- Two old and two inserted endpoint factors; the extra face is counted. -/
def collarFloor (w : Q') (count : Nat) : Q' :=
  let h := headFloor w
  (h^count*h^count)*(h^(count+1)*h^(count+1))

theorem collarFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (count : Nat) : (0 : Q') < collarFloor w count :=
  Q'.mul_pos
    (Q'.mul_pos (HKPos.pow_pos (headFloor_positive hw0 hw1) count)
      (HKPos.pow_pos (headFloor_positive hw0 hw1) count))
    (Q'.mul_pos (HKPos.pow_pos (headFloor_positive hw0 hw1) (count+1))
      (HKPos.pow_pos (headFloor_positive hw0 hw1) (count+1)))

/-- Executable reciprocal cost, with no ambient volume argument. -/
def collarCost (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (count : Nat) : Q' :=
  Q'.recipPos (collarFloor w count) (collarFloor_positive hw0 hw1 count)

theorem collarCost_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (count : Nat) : (0 : Q') < collarCost w hw0 hw1 count := Q'.recipPos_pos _ _

theorem collarCost_cancellation {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (count : Nat) : collarCost w hw0 hw1 count * collarFloor w count ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)

private theorem mul_mono {a b c d : Q'} (ha : (0 : Q') ≤ a) (hc : (0 : Q') ≤ c)
    (hab : a ≤ b) (hcd : c ≤ d) : a*c ≤ b*d :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hab hc)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hcd (Q'.le_trans' _ _ _ ha hab))

private theorem square_mono {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) : a*a ≤ b*b :=
  mul_mono ha ha hab hab

/-- Increasing the explicit face budget weakens its positive floor. -/
theorem collarFloor_antitone {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {c N : Nat} (hc : c ≤ N) : collarFloor w N ≤ collarFloor w c := by
  have h0 := Q'.le_of_lt (headFloor_positive hw0 hw1)
  have h1 : headFloor w ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (headFloor_le_oneThirtySecond hw0 hw1) (by decide)
  have hc0 := Q'.pow_nonneg (headFloor w) h0 N
  have hc1 := Q'.pow_nonneg (headFloor w) h0 (N+1)
  exact mul_mono (Q'.mul_nonneg _ _ hc0 hc0) (Q'.mul_nonneg _ _ hc1 hc1)
    (square_mono hc0 (HKConvGen.pow_base_antitone h0 h1 hc))
    (square_mono hc1 (HKConvGen.pow_base_antitone h0 h1 (Nat.add_le_add_right hc 1)))

private theorem relative_floor_perm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (removed background full : List Nat)
    (hr : ∀ id, id ∈ removed → id ∈ slabPhysicalFaceEdges extent)
    (hb : ∀ id, id ∈ background → id ∈ slabPhysicalFaceEdges extent)
    (hperm : (removed++background).Perm full) :
    (headFloor w)^removed.length * heatProductHaar w (blocks extent) extent background K ≤
      heatProductHaar w (blocks extent) extent full K := by
  have h := headProduct_weighted_floor hw0 hw1 K extent hK
    (headProduct_certificate hw0 hw1 K extent hK background hb) removed hr
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (haar_of_coeff
    ((RatPolyCoeffEqv.mul_comm _ _).trans
      ((polynomialProduct_append (faceHeatPolynomial w K extent) removed background).symm.trans
        (polynomialProduct_perm (faceHeatPolynomial w K extent) hperm)))))

/-- Both original endpoint partitions dominate the SAME detached action.
Neither probe locality nor a guessed connected-component structure is needed. -/
theorem detached_fourth_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (roots : List Z4Link)
    (anchor ambient : List Nat)
    (ha : ∀ j, j ∈ ambient → j ∈ slabPhysicalFaceEdges extent)
    (id : Nat) (hid : id ∈ slabPhysicalFaceEdges extent) :
    collarFloor w (collarIds extent roots anchor ambient).length *
      partitionFourth w K extent (detachedIds extent roots anchor ambient) ≤
      responseDenominator w K extent ambient id := by
  let C := collarIds extent roots anchor ambient
  let D := detachedIds extent roots anchor ambient
  let f := (headFloor w)^C.length
  let g := (headFloor w)^(C.length+1)
  let z := heatProductHaar w (blocks extent) extent D K
  have hC : ∀ j, j ∈ C → j ∈ slabPhysicalFaceEdges extent :=
    fun j hj => ha j (collar_mem hj)
  have hD : ∀ j, j ∈ D → j ∈ slabPhysicalFaceEdges extent :=
    fun j hj => ha j (detached_mem hj)
  have hCi : ∀ j, j ∈ C++[id] → j ∈ slabPhysicalFaceEdges extent := by
    intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact hC j hj
    · have he := List.mem_singleton.mp hj
      subst j
      exact hid
  have hshuffle : ((C++[id])++D).Perm ((C++D)++[id]) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := [id]) (l₂ := D)).append_left C
  have ho := relative_floor_perm hw0 hw1 K extent hK C D ambient hC hD
    (region_partition extent roots anchor ambient)
  have hn : g*z ≤ heatProductHaar w (blocks extent) extent (ambient++[id]) K := by
    simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero] using
      (relative_floor_perm hw0 hw1 K extent hK (C++[id]) D (ambient++[id]) hCi hD
        (hshuffle.trans ((region_partition extent roots anchor ambient).append_right [id])))
  have hz : (0 : Q') ≤ z :=
    (headProduct_certificate hw0 hw1 K extent hK D hD).haar_nonnegative
  have hf : (0 : Q') ≤ f := Q'.pow_nonneg _ (Q'.le_of_lt (headFloor_positive hw0 hw1)) _
  have hg : (0 : Q') ≤ g := Q'.pow_nonneg _ (Q'.le_of_lt (headFloor_positive hw0 hw1)) _
  have hfz := Q'.mul_nonneg _ _ hf hz
  have hgz := Q'.mul_nonneg _ _ hg hz
  have hs := mul_mono (Q'.mul_nonneg _ _ hgz hgz) (Q'.mul_nonneg _ _ hfz hfz)
    (square_mono hgz hn) (square_mono hfz ho)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hs
  exact poly_identity_of_normal_eq
    (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (.mul (.mul (.var 2) (.var 2)) (.mul (.var 2) (.var 2))))
    (.mul (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 2))))
    (by decide) (fun | 0 => f | 1 => g | _ => z)

/-- A count supplied by literal four-dimensional link/face incidence. -/
def collarCount (roots : List Z4Link) (anchor : List Nat) : Nat :=
  6*(roots.length+4*anchor.length)

/-- The floor now depends only on the marked roots and anchor size, not volume. -/
theorem detached_fourth_floor_bounded_count {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (roots : List Z4Link)
    (anchor ambient : List Nat) (hn : ambient.Nodup)
    (ha : ∀ j, j ∈ ambient → j ∈ slabPhysicalFaceEdges extent)
    (id : Nat) (hid : id ∈ slabPhysicalFaceEdges extent) :
    collarFloor w (collarCount roots anchor) *
      partitionFourth w K extent (detachedIds extent roots anchor ambient) ≤
      responseDenominator w K extent ambient id :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
    (collarFloor_antitone hw0 hw1 (collarIds_length_le extent roots anchor ambient hn ha))
    (Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg _) (SumOfSquares.q_mul_self_nonneg _)))
    (detached_fourth_floor hw0 hw1 K extent hK roots anchor ambient ha id hid)

/-- The actual detached fourth power costs only the explicit local reciprocal. -/
theorem detached_fourth_bound_bounded_count {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (roots : List Z4Link)
    (anchor ambient : List Nat) (hn : ambient.Nodup)
    (ha : ∀ j, j ∈ ambient → j ∈ slabPhysicalFaceEdges extent)
    (id : Nat) (hid : id ∈ slabPhysicalFaceEdges extent) :
    partitionFourth w K extent (detachedIds extent roots anchor ambient) ≤
      collarCost w hw0 hw1 (collarCount roots anchor) * responseDenominator w K extent ambient id := by
  have h := Q'.mul_le_mul_of_nonneg_left _ _ _
    (detached_fourth_floor_bounded_count hw0 hw1 K extent hK roots anchor ambient hn ha id hid)
    (Q'.le_of_lt (collarCost_positive hw0 hw1 (collarCount roots anchor)))
  have he := Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (collarCost_cancellation hw0 hw1 (collarCount roots anchor)))
      (Q'.one_mul_eqv (partitionFourth w K extent (detachedIds extent roots anchor ambient))))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) h

end YMGap.Continuum.BF4ExactSlabResponseCollarNormalization

#print axioms YMGap.Continuum.BF4ExactSlabResponseCollarNormalization.collarFloor
#print axioms YMGap.Continuum.BF4ExactSlabResponseCollarNormalization.collarFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabResponseCollarNormalization.collarCost
#print axioms YMGap.Continuum.BF4ExactSlabResponseCollarNormalization.collarCost_positive
#print axioms YMGap.Continuum.BF4ExactSlabResponseCollarNormalization.collarCost_cancellation
#print axioms YMGap.Continuum.BF4ExactSlabResponseCollarNormalization.collarFloor_antitone
#print axioms YMGap.Continuum.BF4ExactSlabResponseCollarNormalization.detached_fourth_floor
#print axioms YMGap.Continuum.BF4ExactSlabResponseCollarNormalization.collarCount
#print axioms YMGap.Continuum.BF4ExactSlabResponseCollarNormalization.detached_fourth_floor_bounded_count
#print axioms YMGap.Continuum.BF4ExactSlabResponseCollarNormalization.detached_fourth_bound_bounded_count
