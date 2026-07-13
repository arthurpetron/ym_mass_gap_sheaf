/-
# Finite node-list bridge for rational atan Darboux sums

This module turns the function-indexed uniform and Mobius-induced quadratures
into the ordered cut-list partitions consumed by the constructive common-
refinement theorem.  No rational representative is normalized or quotiented.
-/

import YMGap.Continuum.SemicircleAtanPartitionInsertion

namespace YMGap.Continuum.SemicircleAtanFiniteMeshBridge

open YMGap.Constructive
open YMGap.Continuum.SemicircleAtanInducedPartition
open YMGap.Continuum.SemicircleAtanInducedGap
open YMGap.Continuum.SemicircleAtanTransformedSqueeze
open YMGap.Continuum.SemicircleAtanPartitionInsertion
open YMGap.Continuum.SemicircleAtanMachinMesh
open YMGap.Continuum.SemicircleAtanMachinPath
open YMGap.Continuum.SemicircleAtanMobiusKernel

/-- The next `count` interior nodes after index `j`. -/
def meshCuts (node : Nat → Q') (j : Nat) : Nat → List Q'
  | 0 => []
  | count + 1 => node (j + 1) :: meshCuts node (j + 1) count

/-- Final node index after the cut list above.  This recursive presentation
keeps the endpoint definitionally aligned with the tail partition. -/
def meshEndIndex (j : Nat) : Nat → Nat
  | 0 => j + 1
  | count + 1 => meshEndIndex (j + 1) count

theorem meshEndIndex_eq (j count : Nat) :
    meshEndIndex j count = j + count + 1 := by
  induction count generalizing j with
  | zero => rfl
  | succ count ih =>
      rw [meshEndIndex, ih]
      omega

/-- Forward left sum on `cells` adjacent node intervals. -/
def meshLeftSum (node : Nat → Q') (j : Nat) : Nat → Q'
  | 0 => 0
  | cells + 1 =>
      partitionLeftRect (node j) (node (j + 1)) +
        meshLeftSum node (j + 1) cells

/-- Forward right sum on `cells` adjacent node intervals. -/
def meshRightSum (node : Nat → Q') (j : Nat) : Nat → Q'
  | 0 => 0
  | cells + 1 =>
      partitionRightRect (node j) (node (j + 1)) +
        meshRightSum node (j + 1) cells

theorem partitionLeftSum_meshCuts (node : Nat → Q') :
    ∀ count j,
      partitionLeftSum
        (cutCells (node j) (meshCuts node j count)
          (node (meshEndIndex j count))) =
        meshLeftSum node j (count + 1)
  | 0, _j => rfl
  | count + 1, j => by
      change partitionLeftRect (node j) (node (j + 1)) +
          partitionLeftSum
            (cutCells (node (j + 1)) (meshCuts node (j + 1) count)
              (node (meshEndIndex (j + 1) count))) =
        partitionLeftRect (node j) (node (j + 1)) +
          meshLeftSum node (j + 1) (count + 1)
      rw [partitionLeftSum_meshCuts node count (j + 1)]

theorem partitionRightSum_meshCuts (node : Nat → Q') :
    ∀ count j,
      partitionRightSum
        (cutCells (node j) (meshCuts node j count)
          (node (meshEndIndex j count))) =
        meshRightSum node j (count + 1)
  | 0, _j => rfl
  | count + 1, j => by
      change partitionRightRect (node j) (node (j + 1)) +
          partitionRightSum
            (cutCells (node (j + 1)) (meshCuts node (j + 1) count)
              (node (meshEndIndex (j + 1) count))) =
        partitionRightRect (node j) (node (j + 1)) +
          meshRightSum node (j + 1) (count + 1)
      rw [partitionRightSum_meshCuts node count (j + 1)]

theorem meshLeftSum_eqv_finSum (node : Nat → Q') :
    ∀ cells j,
      (meshLeftSum node j cells).eqv
        (RationalTail.finSum
          (fun i => partitionLeftRect (node (j + i))
            (node (j + i + 1))) cells)
  | 0, _j => Q'.eqv_refl 0
  | cells + 1, j => by
      let g : RationalTail.QSeq := fun i =>
        partitionLeftRect (node (j + i)) (node (j + i + 1))
      have htail : (meshLeftSum node (j + 1) cells).eqv
          (RationalTail.finSum (fun i => g (i + 1)) cells) := by
        simpa only [g, Nat.add_zero, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using meshLeftSum_eqv_finSum node cells (j + 1)
      have hhead : (partitionLeftRect (node j) (node (j + 1)) +
          meshLeftSum node (j + 1) cells).eqv
          (g 0 + RationalTail.finSum (fun i => g (i + 1)) cells) := by
        simpa only [g, Nat.add_zero] using
          Q'.add_eqv_congr_left
            (partitionLeftRect (node j) (node (j + 1))) _ _ htail
      exact Q'.eqv_trans _ _ _ hhead
        (Q'.eqv_symm (RationalTail.finSum_peel_left g cells))

theorem meshRightSum_eqv_finSum (node : Nat → Q') :
    ∀ cells j,
      (meshRightSum node j cells).eqv
        (RationalTail.finSum
          (fun i => partitionRightRect (node (j + i))
            (node (j + i + 1))) cells)
  | 0, _j => Q'.eqv_refl 0
  | cells + 1, j => by
      let g : RationalTail.QSeq := fun i =>
        partitionRightRect (node (j + i)) (node (j + i + 1))
      have htail : (meshRightSum node (j + 1) cells).eqv
          (RationalTail.finSum (fun i => g (i + 1)) cells) := by
        simpa only [g, Nat.add_zero, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using meshRightSum_eqv_finSum node cells (j + 1)
      have hhead : (partitionRightRect (node j) (node (j + 1)) +
          meshRightSum node (j + 1) cells).eqv
          (g 0 + RationalTail.finSum (fun i => g (i + 1)) cells) := by
        simpa only [g, Nat.add_zero] using
          Q'.add_eqv_congr_left
            (partitionRightRect (node j) (node (j + 1))) _ _ htail
      exact Q'.eqv_trans _ _ _ hhead
        (Q'.eqv_symm (RationalTail.finSum_peel_left g cells))

/-- A globally nonnegative monotone node family produces an ordered cut-list
partition at every finite length. -/
theorem meshCuts_ordered (node : Nat → Q')
    (hnonneg : ∀ j, (0 : Q') ≤ node j)
    (hmono : ∀ j, node j ≤ node (j + 1)) :
    ∀ count j,
      OrderedCuts (node j) (node (meshEndIndex j count))
        (meshCuts node j count)
  | 0, j => ⟨hnonneg j, hmono j⟩
  | count + 1, j =>
      ⟨hnonneg j, hmono j, meshCuts_ordered node hnonneg hmono count (j + 1)⟩

/-- Saturation by `min j n` makes the induced Mobius nodes monotone even
beyond the last physical grid node. -/
theorem inducedNode_mono_all
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) (j : Nat) :
    inducedNode R S A B n hS hB hn hbranch j ≤
      inducedNode R S A B n hS hB hn hbranch (j + 1) := by
  by_cases hj : j < n
  · exact inducedNode_mono_step R S A B n j hS hB hn hbranch hj
  · have hnj : n ≤ j := Nat.le_of_not_gt hj
    have hnjs : n ≤ j + 1 := Nat.le_trans hnj (Nat.le_succ j)
    unfold inducedNode
    simp only [Nat.min_eq_right hnj, Nat.min_eq_right hnjs]
    exact Q'.le_refl' _

def inducedMeshCuts
    (R S A B N : Nat) (hS : 0 < S) (hB : 0 < B)
    (hbranch : R*A < S*B) : List Q' :=
  meshCuts
    (inducedNode R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch) 0 N

theorem inducedMeshCuts_ordered
    (R S A B N : Nat) (hS : 0 < S) (hB : 0 < B)
    (hbranch : R*A < S*B) :
    OrderedCuts
      (inducedNode R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch 0)
      (inducedNode R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch (N + 1))
      (inducedMeshCuts R S A B N hS hB hbranch) := by
  let node := inducedNode R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch
  have h := meshCuts_ordered node
    (inducedNode_nonnegative R S A B (N + 1) hS hB
      (Nat.succ_pos N) hbranch)
    (inducedNode_mono_all R S A B (N + 1) hS hB
      (Nat.succ_pos N) hbranch) N 0
  simpa only [inducedMeshCuts, node, meshEndIndex_eq, Nat.zero_add] using h

/-- The existing induced left quadrature is exactly the left Darboux sum of
its explicit ordered node-list partition. -/
theorem inducedLeftGridSum_eqv_partition
    (R S A B N : Nat) (hS : 0 < S) (hB : 0 < B)
    (hbranch : R*A < S*B) :
    (inducedLeftGridSum R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch).eqv
      (partitionLeftSum
        (cutCells
          (inducedNode R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch 0)
          (inducedMeshCuts R S A B N hS hB hbranch)
          (inducedNode R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch
            (N + 1)))) := by
  let node := inducedNode R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch
  have hpart := meshLeftSum_eqv_finSum node (N + 1) 0
  have hcells := partitionLeftSum_meshCuts node N 0
  have hpartition :
      (partitionLeftSum
        (cutCells (node 0) (meshCuts node 0 N) (node (N + 1)))).eqv
      (RationalTail.finSum
        (fun j => inducedWidth R S A B (N + 1) hS hB
          (Nat.succ_pos N) hbranch j * kernelValue (node j)) (N + 1)) := by
    have hend : meshEndIndex 0 N = N + 1 := by
      simpa only [Nat.zero_add] using meshEndIndex_eq 0 N
    rw [hend] at hcells
    rw [hcells]
    simpa only [node, partitionLeftRect, inducedWidth, Nat.zero_add,
      Nat.add_zero, Nat.add_assoc] using hpart
  exact Q'.eqv_trans _ _ _
    (inducedLeftGridSum_factor R S A B (N + 1) hS hB
      (Nat.succ_pos N) hbranch)
    hpartition.symm

/-- Right-sum companion of `inducedLeftGridSum_eqv_partition`. -/
theorem inducedRightGridSum_eqv_partition
    (R S A B N : Nat) (hS : 0 < S) (hB : 0 < B)
    (hbranch : R*A < S*B) :
    (inducedRightGridSum R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch).eqv
      (partitionRightSum
        (cutCells
          (inducedNode R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch 0)
          (inducedMeshCuts R S A B N hS hB hbranch)
          (inducedNode R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch
            (N + 1)))) := by
  let node := inducedNode R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch
  have hpart := meshRightSum_eqv_finSum node (N + 1) 0
  have hcells := partitionRightSum_meshCuts node N 0
  have hpartition :
      (partitionRightSum
        (cutCells (node 0) (meshCuts node 0 N) (node (N + 1)))).eqv
      (RationalTail.finSum
        (fun j => inducedWidth R S A B (N + 1) hS hB
          (Nat.succ_pos N) hbranch j * kernelValue (node (j + 1))) (N + 1)) := by
    have hend : meshEndIndex 0 N = N + 1 := by
      simpa only [Nat.zero_add] using meshEndIndex_eq 0 N
    rw [hend] at hcells
    rw [hcells]
    simpa only [node, partitionRightRect, inducedWidth, Nat.zero_add,
      Nat.add_zero, Nat.add_assoc] using hpart
  exact Q'.eqv_trans _ _ _
    (inducedRightGridSum_factor R S A B (N + 1) hS hB
      (Nat.succ_pos N) hbranch)
    hpartition.symm

/-! ## Uniform endpoint meshes in the same partition representation -/

def uniformMeshCuts (A B N : Nat) (hB : 0 < B) : List Q' :=
  meshCuts (gridNode A B (N + 1) · hB (Nat.succ_pos N)) 0 N

theorem uniformMeshCuts_ordered (A B N : Nat) (hB : 0 < B) :
    OrderedCuts
      (gridNode A B (N + 1) 0 hB (Nat.succ_pos N))
      (gridNode A B (N + 1) (N + 1) hB (Nat.succ_pos N))
      (uniformMeshCuts A B N hB) := by
  let node := fun j => gridNode A B (N + 1) j hB (Nat.succ_pos N)
  have h := meshCuts_ordered node
    (fun j => gridNode_nonneg A B (N + 1) j hB (Nat.succ_pos N))
    (fun j => gridNode_mono A B (N + 1) j (j + 1) hB
      (Nat.succ_pos N) (Nat.le_succ j)) N 0
  simpa only [uniformMeshCuts, node, meshEndIndex_eq, Nat.zero_add] using h

private theorem partitionLeftRect_eqv_sourceLeftRect (x y : Q') :
    (partitionLeftRect x y).eqv (sourceLeftRect x y) := by
  unfold partitionLeftRect kernelValue sourceLeftRect Q'.divPos
  refine Q'.eqv_trans _ ((y + -x) * (2 * Q'.recipPos (kernelDen x)
    (kernelDen_pos x))) _ (Q'.eqv_refl _) ?_
  refine Q'.eqv_symm (Q'.eqv_trans _
    (((y + -x) * 2) * Q'.recipPos (kernelDen x) (kernelDen_pos x)) _ ?_ ?_)
  · exact Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv 2 (y + -x))
  · exact Q'.mul_assoc_eqv (y + -x) 2 _

private theorem partitionRightRect_eqv_sourceRightRect (x y : Q') :
    (partitionRightRect x y).eqv (sourceRightRect x y) := by
  unfold partitionRightRect kernelValue sourceRightRect Q'.divPos
  refine Q'.eqv_trans _ ((y + -x) * (2 * Q'.recipPos (kernelDen y)
    (kernelDen_pos y))) _ (Q'.eqv_refl _) ?_
  refine Q'.eqv_symm (Q'.eqv_trans _
    (((y + -x) * 2) * Q'.recipPos (kernelDen y) (kernelDen_pos y)) _ ?_ ?_)
  · exact Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv 2 (y + -x))
  · exact Q'.mul_assoc_eqv (y + -x) 2 _

/-- Uniform endpoint left sums are the left sums of their explicit ordered
cut-list partitions. -/
theorem scaledLeftSum_eqv_partition (A B N : Nat) (hB : 0 < B) :
    (SemicircleAtanRationalEndpoint.scaledLeftSum A B (N + 1) hB
      (Nat.succ_pos N)).eqv
      (partitionLeftSum
        (cutCells
          (gridNode A B (N + 1) 0 hB (Nat.succ_pos N))
          (uniformMeshCuts A B N hB)
          (gridNode A B (N + 1) (N + 1) hB (Nat.succ_pos N)))) := by
  let node := fun j => gridNode A B (N + 1) j hB (Nat.succ_pos N)
  have hpart := meshLeftSum_eqv_finSum node (N + 1) 0
  have hcells := partitionLeftSum_meshCuts node N 0
  have hend : meshEndIndex 0 N = N + 1 := by
    simpa only [Nat.zero_add] using meshEndIndex_eq 0 N
  rw [hend] at hcells
  have hpartition :
      (partitionLeftSum
        (cutCells (node 0) (meshCuts node 0 N) (node (N + 1)))).eqv
      (sourceLeftGridSum A B (N + 1) hB (Nat.succ_pos N)) := by
    rw [hcells]
    refine Q'.eqv_trans _ _ _ hpart ?_
    unfold sourceLeftGridSum
    apply RationalTail.finSum_eqv_congr_lt
    intro j hj
    unfold sourceLeftGridCell
    simp only [if_pos hj, node, Nat.zero_add]
    exact partitionLeftRect_eqv_sourceLeftRect _ _
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (sourceLeftGridSum_eqv_scaledLeftSum A B (N + 1) hB
        (Nat.succ_pos N)))
    hpartition.symm

/-- Uniform endpoint right-sum companion. -/
theorem scaledRightSum_eqv_partition (A B N : Nat) (hB : 0 < B) :
    (SemicircleAtanRationalEndpoint.scaledRightSum A B (N + 1) hB
      (Nat.succ_pos N)).eqv
      (partitionRightSum
        (cutCells
          (gridNode A B (N + 1) 0 hB (Nat.succ_pos N))
          (uniformMeshCuts A B N hB)
          (gridNode A B (N + 1) (N + 1) hB (Nat.succ_pos N)))) := by
  let node := fun j => gridNode A B (N + 1) j hB (Nat.succ_pos N)
  have hpart := meshRightSum_eqv_finSum node (N + 1) 0
  have hcells := partitionRightSum_meshCuts node N 0
  have hend : meshEndIndex 0 N = N + 1 := by
    simpa only [Nat.zero_add] using meshEndIndex_eq 0 N
  rw [hend] at hcells
  have hpartition :
      (partitionRightSum
        (cutCells (node 0) (meshCuts node 0 N) (node (N + 1)))).eqv
      (sourceRightGridSum A B (N + 1) hB (Nat.succ_pos N)) := by
    rw [hcells]
    refine Q'.eqv_trans _ _ _ hpart ?_
    unfold sourceRightGridSum
    apply RationalTail.finSum_eqv_congr_lt
    intro j hj
    unfold sourceRightGridCell
    simp only [if_pos hj, node, Nat.zero_add]
    exact partitionRightRect_eqv_sourceRightRect _ _
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (sourceRightGridSum_eqv_scaledRightSum A B (N + 1) hB
        (Nat.succ_pos N)))
    hpartition.symm

/-! ## Semantic endpoint identifications for joined meshes -/

private theorem divPos_eqv_divPos_of_cross {p q p' q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : (p*q').eqv (p'*q)) :
    (Q'.divPos p q hq).eqv (Q'.divPos p' q' hq') := by
  let c := Q'.divPos p' q' hq'
  have hright : ((c*q)*q').eqv (p'*q) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c q q') ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left c _ _ (Q'.mul_comm_eqv q q')) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv c q' q)) ?_
    exact Q'.mul_eqv_congr_right _ _ q (Q'.divPos_mul_eqv p' q' hq')
  have hmul : (p*q').eqv ((c*q)*q') :=
    Q'.eqv_trans _ _ _ hcross (Q'.eqv_symm hright)
  have hcancel : p.eqv (c*q) := by
    apply Q'.mul_left_cancel_of_pos hq'
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q' p) ?_
    refine Q'.eqv_trans _ _ _ hmul ?_
    exact Q'.mul_comm_eqv (c*q) q'
  apply Q'.mul_left_cancel_of_pos hq
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q (Q'.divPos p q hq)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv p q hq) ?_
  refine Q'.eqv_trans _ _ _ hcancel ?_
  exact Q'.mul_comm_eqv c q

theorem divPos_eqv_congr {p p' q q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hp : p.eqv p') (hden : q.eqv q') :
    (Q'.divPos p q hq).eqv (Q'.divPos p' q' hq') := by
  apply divPos_eqv_divPos_of_cross hq hq'
  exact Q'.eqv_trans _ (p' * q') _
    (Q'.mul_eqv_congr_right _ _ _ hp)
    (Q'.mul_eqv_congr_left p' _ _ hden.symm)

theorem mobius_eqv_tanAdd {r x t : Q'}
    (hx : x.eqv t)
    (hdenX : (0 : Q') < mobiusDen r x)
    (hdenT : (0 : Q') < (1 : Q') + -(r*t)) :
    (mobius r x hdenX).eqv (tanAdd r t hdenT) := by
  unfold mobius tanAdd
  apply divPos_eqv_congr
  · exact Q'.add_eqv_congr_left r _ _ hx
  · unfold mobiusDen
    exact Q'.add_eqv_congr_left 1 _ _
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left r _ _ hx))

/-- The last induced node is the exact rational tangent-addition endpoint,
independently of the mesh resolution. -/
theorem inducedNode_endpoint_eqv_tanAdd
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) :
    (inducedNode R S A B n hS hB hn hbranch n).eqv
      (tanAdd (rat R S hS) (rat A B hB)
        (endpointReserve_pos R S A B hS hB hbranch)) := by
  unfold inducedNode
  simp only [Nat.min_self]
  apply mobius_eqv_tanAdd (gridNode_endpoint_eqv A B n hB hn)

private theorem mul_zero_eqv (q : Q') : (q * (0 : Q')).eqv 0 := by
  show (q.num * (0 : Int)) * ((0 : Q').den : Int) =
    (0 : Int) * ((q * (0 : Q')).den : Int)
  simp only [Int.mul_zero, Int.zero_mul]

private theorem neg_zero_eqv : ((-(0 : Q')) : Q').eqv 0 := by decide

private theorem tanAdd_zero_eqv (r : Q')
    (hden : (0 : Q') < (1 : Q') + -(r*(0 : Q'))) :
    (tanAdd r 0 hden).eqv r := by
  have hp : (r + (0 : Q')).eqv r := by
    rw [Q'.add_zero']
    exact Q'.eqv_refl r
  have hq : ((1 : Q') + -(r*(0 : Q'))).eqv 1 := by
    refine Q'.eqv_trans _ ((1 : Q') + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr_left 1 _ _
        (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (mul_zero_eqv r))
          neg_zero_eqv)
    · rw [Q'.add_zero']
      exact Q'.eqv_refl 1
  have hdiv : (tanAdd r 0 hden).eqv
      (Q'.divPos r 1 (by decide)) := by
    unfold tanAdd
    exact divPos_eqv_congr hden (by decide) hp hq
  exact Q'.eqv_trans _ _ _ hdiv
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_one_eqv (Q'.divPos r 1 (by decide))))
      (Q'.divPos_mul_eqv r 1 (by decide)))

theorem gridNode_zero_eqv
    (A B n : Nat) (hB : 0 < B) (hn : 0 < n) :
    (gridNode A B n 0 hB hn).eqv 0 := by
  show (gridNode A B n 0 hB hn).num * ((0 : Q').den : Int) =
    (0 : Int) * ((gridNode A B n 0 hB hn).den : Int)
  unfold gridNode
  rw [Q'.mkPos_num, Nat.mul_zero]
  push_cast
  simp only [Int.zero_mul]

/-- The first induced node is the left endpoint `r`. -/
theorem inducedNode_zero_eqv_rat
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) :
    (inducedNode R S A B n hS hB hn hbranch 0).eqv (rat R S hS) := by
  have hx0 := gridNode_zero_eqv A B n hB hn
  have hzeroDen : (0 : Q') <
      (1 : Q') + -(rat R S hS * (0 : Q')) := by
    have hz := endpointReserve_pos R S 0 1 hS (by decide)
      (by simpa only [Nat.mul_zero, Nat.zero_mul, Nat.mul_one] using hS)
    simpa only [endpointReserve, rat] using hz
  have hmob : (inducedNode R S A B n hS hB hn hbranch 0).eqv
      (tanAdd (rat R S hS) 0 hzeroDen) := by
    unfold inducedNode
    simp only [Nat.min_eq_left (Nat.zero_le n)]
    apply mobius_eqv_tanAdd hx0
  exact Q'.eqv_trans _ _ _ hmob (tanAdd_zero_eqv _ hzeroDen)

/-! ## Joined endpoint-plus-induced partitions -/

def joinedMeshCuts
    (R S A B M N : Nat) (hS : 0 < S) (hB : 0 < B)
    (hbranch : R*A < S*B) : List Q' :=
  uniformMeshCuts R S M hS ++
    inducedNode R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch 0 ::
      inducedMeshCuts R S A B N hS hB hbranch

theorem joinedMeshCuts_ordered
    (R S A B M N : Nat) (hS : 0 < S) (hB : 0 < B)
    (hbranch : R*A < S*B) :
    OrderedCuts
      (gridNode R S (M + 1) 0 hS (Nat.succ_pos M))
      (inducedNode R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch (N + 1))
      (joinedMeshCuts R S A B M N hS hB hbranch) := by
  have hfirst := uniformMeshCuts_ordered R S M hS
  have hsecond := inducedMeshCuts_ordered R S A B N hS hB hbranch
  have hjoin :
      (gridNode R S (M + 1) (M + 1) hS (Nat.succ_pos M)).eqv
        (inducedNode R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch 0) :=
    Q'.eqv_trans _ (rat R S hS) _
      (gridNode_endpoint_eqv R S (M + 1) hS (Nat.succ_pos M))
      (inducedNode_zero_eqv_rat R S A B (N + 1) hS hB
        (Nat.succ_pos N) hbranch).symm
  exact OrderedCuts.append_join _ hfirst hsecond hjoin

theorem joinedLeftSum_eqv
    (R S A B M N : Nat) (hS : 0 < S) (hB : 0 < B)
    (hbranch : R*A < S*B) :
    (partitionLeftSum
      (cutCells
        (gridNode R S (M + 1) 0 hS (Nat.succ_pos M))
        (joinedMeshCuts R S A B M N hS hB hbranch)
        (inducedNode R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch
          (N + 1)))).eqv
      (SemicircleAtanRationalEndpoint.scaledLeftSum R S (M + 1) hS
          (Nat.succ_pos M) +
        inducedLeftGridSum R S A B (N + 1) hS hB
          (Nat.succ_pos N) hbranch) := by
  let x := gridNode R S (M + 1) 0 hS (Nat.succ_pos M)
  let rGrid := gridNode R S (M + 1) (M + 1) hS (Nat.succ_pos M)
  let rInd := inducedNode R S A B (N + 1) hS hB
    (Nat.succ_pos N) hbranch 0
  let y := inducedNode R S A B (N + 1) hS hB
    (Nat.succ_pos N) hbranch (N + 1)
  have hjoin : rGrid.eqv rInd :=
    Q'.eqv_trans _ (rat R S hS) _
      (gridNode_endpoint_eqv R S (M + 1) hS (Nat.succ_pos M))
      (inducedNode_zero_eqv_rat R S A B (N + 1) hS hB
        (Nat.succ_pos N) hbranch).symm
  have huniformEqv :
      PartitionEqv
        (cutCells x (uniformMeshCuts R S M hS) rGrid)
        (cutCells x (uniformMeshCuts R S M hS) rInd) :=
    cutCells_eqv_congr (Q'.eqv_refl x) hjoin
      (CutListEqv.refl (uniformMeshCuts R S M hS))
  have hsplit := partitionLeftSum_join_eqv x rInd y
    (uniformMeshCuts R S M hS) (inducedMeshCuts R S A B N hS hB hbranch)
  refine Q'.eqv_trans _ _ _ hsplit ?_
  apply Q'.add_eqv_congr'
  · exact Q'.eqv_trans _ _ _ huniformEqv.leftSum.symm
      (Q'.eqv_symm (scaledLeftSum_eqv_partition R S M hS))
  · exact Q'.eqv_symm
      (inducedLeftGridSum_eqv_partition R S A B N hS hB hbranch)

theorem joinedRightSum_eqv
    (R S A B M N : Nat) (hS : 0 < S) (hB : 0 < B)
    (hbranch : R*A < S*B) :
    (partitionRightSum
      (cutCells
        (gridNode R S (M + 1) 0 hS (Nat.succ_pos M))
        (joinedMeshCuts R S A B M N hS hB hbranch)
        (inducedNode R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch
          (N + 1)))).eqv
      (SemicircleAtanRationalEndpoint.scaledRightSum R S (M + 1) hS
          (Nat.succ_pos M) +
        inducedRightGridSum R S A B (N + 1) hS hB
          (Nat.succ_pos N) hbranch) := by
  let x := gridNode R S (M + 1) 0 hS (Nat.succ_pos M)
  let rGrid := gridNode R S (M + 1) (M + 1) hS (Nat.succ_pos M)
  let rInd := inducedNode R S A B (N + 1) hS hB
    (Nat.succ_pos N) hbranch 0
  let y := inducedNode R S A B (N + 1) hS hB
    (Nat.succ_pos N) hbranch (N + 1)
  have hjoin : rGrid.eqv rInd :=
    Q'.eqv_trans _ (rat R S hS) _
      (gridNode_endpoint_eqv R S (M + 1) hS (Nat.succ_pos M))
      (inducedNode_zero_eqv_rat R S A B (N + 1) hS hB
        (Nat.succ_pos N) hbranch).symm
  have huniformEqv :
      PartitionEqv
        (cutCells x (uniformMeshCuts R S M hS) rGrid)
        (cutCells x (uniformMeshCuts R S M hS) rInd) :=
    cutCells_eqv_congr (Q'.eqv_refl x) hjoin
      (CutListEqv.refl (uniformMeshCuts R S M hS))
  have hsplit := partitionRightSum_join_eqv x rInd y
    (uniformMeshCuts R S M hS) (inducedMeshCuts R S A B N hS hB hbranch)
  refine Q'.eqv_trans _ _ _ hsplit ?_
  apply Q'.add_eqv_congr'
  · exact Q'.eqv_trans _ _ _ huniformEqv.rightSum.symm
      (Q'.eqv_symm (scaledRightSum_eqv_partition R S M hS))
  · exact Q'.eqv_symm
      (inducedRightGridSum_eqv_partition R S A B N hS hB hbranch)

/-- Finite lower cross-bracket: the joined right sum is below every direct
left endpoint sum at the tangent-addition target. -/
theorem joinedRight_le_targetLeft
    (R S A B T U M N K : Nat)
    (hS : 0 < S) (hB : 0 < B) (hU : 0 < U)
    (hbranch : R*A < S*B)
    (htarget : (tanAdd (rat R S hS) (rat A B hB)
      (endpointReserve_pos R S A B hS hB hbranch)).eqv (rat T U hU)) :
    SemicircleAtanRationalEndpoint.scaledRightSum R S (M + 1) hS
        (Nat.succ_pos M) +
      inducedRightGridSum R S A B (N + 1) hS hB
        (Nat.succ_pos N) hbranch ≤
      SemicircleAtanRationalEndpoint.scaledLeftSum T U (K + 1) hU
        (Nat.succ_pos K) := by
  have hj := joinedMeshCuts_ordered R S A B M N hS hB hbranch
  have ht := uniformMeshCuts_ordered T U K hU
  have hx :
      (gridNode R S (M + 1) 0 hS (Nat.succ_pos M)).eqv
        (gridNode T U (K + 1) 0 hU (Nat.succ_pos K)) :=
    Q'.eqv_trans _ 0 _
      (gridNode_zero_eqv R S (M + 1) hS (Nat.succ_pos M))
      (gridNode_zero_eqv T U (K + 1) hU (Nat.succ_pos K)).symm
  have hy :
      (inducedNode R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch
        (N + 1)).eqv
      (gridNode T U (K + 1) (K + 1) hU (Nat.succ_pos K)) :=
    Q'.eqv_trans _
      (tanAdd (rat R S hS) (rat A B hB)
        (endpointReserve_pos R S A B hS hB hbranch)) _
      (inducedNode_endpoint_eqv_tanAdd R S A B (N + 1) hS hB
        (Nat.succ_pos N) hbranch)
      (Q'.eqv_trans _ (rat T U hU) _ htarget
        (gridNode_endpoint_eqv T U (K + 1) hU (Nat.succ_pos K)).symm)
  have hbracket := ordered_partitions_common_bracket_of_endpoints hj ht hx hy
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (joinedRightSum_eqv R S A B M N hS hB hbranch))
    (Q'.le_trans' _ _ _ hbracket
      (Q'.le_of_eqv
        (Q'.eqv_symm (scaledLeftSum_eqv_partition T U K hU))))

/-- Finite upper cross-bracket, dual to `joinedRight_le_targetLeft`. -/
theorem targetRight_le_joinedLeft
    (R S A B T U M N K : Nat)
    (hS : 0 < S) (hB : 0 < B) (hU : 0 < U)
    (hbranch : R*A < S*B)
    (htarget : (tanAdd (rat R S hS) (rat A B hB)
      (endpointReserve_pos R S A B hS hB hbranch)).eqv (rat T U hU)) :
    SemicircleAtanRationalEndpoint.scaledRightSum T U (K + 1) hU
        (Nat.succ_pos K) ≤
      SemicircleAtanRationalEndpoint.scaledLeftSum R S (M + 1) hS
          (Nat.succ_pos M) +
        inducedLeftGridSum R S A B (N + 1) hS hB
          (Nat.succ_pos N) hbranch := by
  have hj := joinedMeshCuts_ordered R S A B M N hS hB hbranch
  have ht := uniformMeshCuts_ordered T U K hU
  have hx :
      (gridNode T U (K + 1) 0 hU (Nat.succ_pos K)).eqv
        (gridNode R S (M + 1) 0 hS (Nat.succ_pos M)) :=
    Q'.eqv_trans _ 0 _
      (gridNode_zero_eqv T U (K + 1) hU (Nat.succ_pos K))
      (gridNode_zero_eqv R S (M + 1) hS (Nat.succ_pos M)).symm
  have hy :
      (gridNode T U (K + 1) (K + 1) hU (Nat.succ_pos K)).eqv
      (inducedNode R S A B (N + 1) hS hB (Nat.succ_pos N) hbranch
        (N + 1)) :=
    (Q'.eqv_trans _
      (tanAdd (rat R S hS) (rat A B hB)
        (endpointReserve_pos R S A B hS hB hbranch)) _
      (inducedNode_endpoint_eqv_tanAdd R S A B (N + 1) hS hB
        (Nat.succ_pos N) hbranch)
      (Q'.eqv_trans _ (rat T U hU) _ htarget
        (gridNode_endpoint_eqv T U (K + 1) hU (Nat.succ_pos K)).symm)).symm
  have hbracket := ordered_partitions_common_bracket_of_endpoints ht hj hx hy
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (scaledRightSum_eqv_partition T U K hU))
    (Q'.le_trans' _ _ _ hbracket
      (Q'.le_of_eqv
        (joinedLeftSum_eqv R S A B M N hS hB hbranch)))

end YMGap.Continuum.SemicircleAtanFiniteMeshBridge

#print axioms YMGap.Continuum.SemicircleAtanFiniteMeshBridge.meshCuts_ordered
#print axioms YMGap.Continuum.SemicircleAtanFiniteMeshBridge.inducedNode_mono_all
#print axioms YMGap.Continuum.SemicircleAtanFiniteMeshBridge.inducedMeshCuts_ordered
#print axioms YMGap.Continuum.SemicircleAtanFiniteMeshBridge.inducedLeftGridSum_eqv_partition
#print axioms YMGap.Continuum.SemicircleAtanFiniteMeshBridge.inducedRightGridSum_eqv_partition
#print axioms YMGap.Continuum.SemicircleAtanFiniteMeshBridge.uniformMeshCuts_ordered
#print axioms YMGap.Continuum.SemicircleAtanFiniteMeshBridge.scaledLeftSum_eqv_partition
#print axioms YMGap.Continuum.SemicircleAtanFiniteMeshBridge.scaledRightSum_eqv_partition
#print axioms YMGap.Continuum.SemicircleAtanFiniteMeshBridge.divPos_eqv_congr
#print axioms YMGap.Continuum.SemicircleAtanFiniteMeshBridge.inducedNode_endpoint_eqv_tanAdd
#print axioms YMGap.Continuum.SemicircleAtanFiniteMeshBridge.inducedNode_zero_eqv_rat
#print axioms YMGap.Continuum.SemicircleAtanFiniteMeshBridge.joinedMeshCuts_ordered
#print axioms YMGap.Continuum.SemicircleAtanFiniteMeshBridge.joinedLeftSum_eqv
#print axioms YMGap.Continuum.SemicircleAtanFiniteMeshBridge.joinedRightSum_eqv
#print axioms YMGap.Continuum.SemicircleAtanFiniteMeshBridge.joinedRight_le_targetLeft
#print axioms YMGap.Continuum.SemicircleAtanFiniteMeshBridge.targetRight_le_joinedLeft
