/-
# Exact uniform endpoint gap for the quadrant semicircle

This successor imports the frozen polygon/uniform cross-comparison module.
It derives the width of the uniform Darboux bracket by a finite telescoping
identity, without modifying either banked predecessor.
-/

import YMGap.Continuum.SemicirclePolygonMidpointValue

namespace YMGap.Continuum.SemicircleUniformEndpointGap

open YMGap.Constructive
open YMGap.Continuum.SemicircleAtanPartitionInsertion
open YMGap.Continuum.SemicircleAtanFiniteMeshBridge
open YMGap.Continuum.SemicircleAtanInducedPartition
open YMGap.Continuum.SemicirclePolygonMidpointBridge
open YMGap.Continuum.SemicirclePolygonMidpointValue
open YMGap.Continuum.SemicircleRationalPolygon

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem two_num_cast : (2 : Q').num = 2 := rfl
private theorem two_den_cast : ((2 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
               zero_num_cast, zero_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm];
             omega))

def unitNode (M j : Nat) : Q' :=
  gridNode 1 1 (M+1) j (by decide) (Nat.succ_pos M)

def unitWidth (M : Nat) : Q' :=
  gridMesh 1 1 (M+1) (by decide) (Nat.succ_pos M)

private def meshLeftSum (f : Q' → CReal) (node : Nat → Q') (j : Nat) :
    Nat → CReal
  | 0 => CReal.czero
  | cells + 1 => CReal.add
      (cPartitionRect f (node j) (node (j+1)) (node j))
      (meshLeftSum f node (j+1) cells)

private def meshRightSum (f : Q' → CReal) (node : Nat → Q') (j : Nat) :
    Nat → CReal
  | 0 => CReal.czero
  | cells + 1 => CReal.add
      (cPartitionRect f (node j) (node (j+1)) (node (j+1)))
      (meshRightSum f node (j+1) cells)

private theorem partitionLeftSum_meshCuts (f : Q' → CReal) (node : Nat → Q') :
    ∀ count j,
      cPartitionLeftSum f
        (cutCells (node j) (meshCuts node j count)
          (node (meshEndIndex j count))) =
        meshLeftSum f node j (count+1)
  | 0, _j => rfl
  | count + 1, j => by
      change CReal.add
          (cPartitionRect f (node j) (node (j+1)) (node j))
          (cPartitionLeftSum f
            (cutCells (node (j+1)) (meshCuts node (j+1) count)
              (node (meshEndIndex (j+1) count)))) =
        CReal.add
          (cPartitionRect f (node j) (node (j+1)) (node j))
          (meshLeftSum f node (j+1) (count+1))
      rw [partitionLeftSum_meshCuts f node count (j+1)]

private theorem partitionRightSum_meshCuts (f : Q' → CReal) (node : Nat → Q') :
    ∀ count j,
      cPartitionRightSum f
        (cutCells (node j) (meshCuts node j count)
          (node (meshEndIndex j count))) =
        meshRightSum f node j (count+1)
  | 0, _j => rfl
  | count + 1, j => by
      change CReal.add
          (cPartitionRect f (node j) (node (j+1)) (node (j+1)))
          (cPartitionRightSum f
            (cutCells (node (j+1)) (meshCuts node (j+1) count)
              (node (meshEndIndex (j+1) count)))) =
        CReal.add
          (cPartitionRect f (node j) (node (j+1)) (node (j+1)))
          (meshRightSum f node (j+1) (count+1))
      rw [partitionRightSum_meshCuts f node count (j+1)]

private theorem cadd_equiv_congr {A A' B B' : CReal}
    (hA : CReal.Equiv A A') (hB : CReal.Equiv B B') :
    CReal.Equiv (CReal.add A B) (CReal.add A' B') :=
  CReal.Equiv.trans (CReal.add_congr_left hA) (CReal.add_congr_right hB)

private theorem cmul_equiv_congr {A A' B B' : CReal}
    (hA : CReal.Equiv A A') (hB : CReal.Equiv B B') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A' B') := by
  have hr : CReal.Equiv (CReal.mul A' B) (CReal.mul A' B') :=
    (CRealAlg.cmul_comm A' B).trans
      ((CReal.mul_congr_left hB).trans (CRealAlg.cmul_comm B' A'))
  exact (CReal.mul_congr_left hA).trans hr

private theorem partitionEqv_left (f : Q' → CReal)
    (hf : ∀ {a b : Q'}, a.eqv b → CReal.Equiv (f a) (f b))
    {cells cells' : List PartitionCell} (h : PartitionEqv cells cells') :
    CReal.Equiv (cPartitionLeftSum f cells) (cPartitionLeftSum f cells') := by
  induction h with
  | nil => exact CReal.Equiv.refl _
  | cons hx hy hrest ih =>
      rename_i x y x' y' cs cs'
      have hw : (y + -x).eqv (y' + -x') :=
        Q'.add_eqv_congr' hy (Q'.neg_eqv_congr _ _ hx)
      have hrect : CReal.Equiv
          (cPartitionRect f x y x) (cPartitionRect f x' y' x') := by
        unfold cPartitionRect
        exact cmul_equiv_congr (TrigAdd.equiv_ofQ'_of_eqv hw) (hf hx)
      exact cadd_equiv_congr hrect ih

private theorem partitionEqv_right (f : Q' → CReal)
    (hf : ∀ {a b : Q'}, a.eqv b → CReal.Equiv (f a) (f b))
    {cells cells' : List PartitionCell} (h : PartitionEqv cells cells') :
    CReal.Equiv (cPartitionRightSum f cells) (cPartitionRightSum f cells') := by
  induction h with
  | nil => exact CReal.Equiv.refl _
  | cons hx hy hrest ih =>
      rename_i x y x' y' cs cs'
      have hw : (y + -x).eqv (y' + -x') :=
        Q'.add_eqv_congr' hy (Q'.neg_eqv_congr _ _ hx)
      have hrect : CReal.Equiv
          (cPartitionRect f x y y) (cPartitionRect f x' y' y') := by
        unfold cPartitionRect
        exact cmul_equiv_congr (TrigAdd.equiv_ofQ'_of_eqv hw) (hf hy)
      exact cadd_equiv_congr hrect ih

private theorem czero_equiv_zero_add_mul_cancel (W A : CReal) :
    CReal.Equiv CReal.czero
      (CReal.add CReal.czero (CReal.mul W (CReal.add A (CReal.neg A)))) :=
  TrigAdd.equiv_of_approx_eqv (fun k => by
    change (0 : Q').eqv (0 + W.approx k * (A.approx k + -A.approx k))
    ring_qeqv)

set_option maxHeartbeats 1000000 in
private theorem endpoint_shuffle (W A B R E : CReal) :
    CReal.Equiv
      (CReal.add (CReal.mul W A)
        (CReal.add R (CReal.mul W (CReal.add B (CReal.neg E)))))
      (CReal.add (CReal.add (CReal.mul W B) R)
        (CReal.mul W (CReal.add A (CReal.neg E)))) :=
  TrigAdd.equiv_of_approx_eqv (fun k => by
    change (W.approx k * A.approx k +
        (R.approx k + W.approx k * (B.approx k + -E.approx k))).eqv
      ((W.approx k * B.approx k + R.approx k) +
        W.approx k * (A.approx k + -E.approx k))
    ring_qeqv)

private theorem mesh_endpoint_gap
    (f : Q' → CReal) (node : Nat → Q') (w : Q')
    (hstep : ∀ i, (node (i+1) + -node i).eqv w) : ∀ cells j,
    CReal.Equiv (meshLeftSum f node j cells)
      (CReal.add (meshRightSum f node j cells)
        (CReal.mul (CReal.ofQ' w)
          (CReal.add (f (node j)) (CReal.neg (f (node (j+cells)))))))
  | 0, j => by
      change CReal.Equiv CReal.czero
        (CReal.add CReal.czero
          (CReal.mul (CReal.ofQ' w)
            (CReal.add (f (node j)) (CReal.neg (f (node (j+0)))))))
      simpa only [Nat.add_zero] using
        czero_equiv_zero_add_mul_cancel (CReal.ofQ' w) (f (node j))
  | cells + 1, j => by
      change CReal.Equiv
        (CReal.add
          (cPartitionRect f (node j) (node (j+1)) (node j))
          (meshLeftSum f node (j+1) cells))
        (CReal.add
          (CReal.add
            (cPartitionRect f (node j) (node (j+1)) (node (j+1)))
            (meshRightSum f node (j+1) cells))
          (CReal.mul (CReal.ofQ' w)
            (CReal.add (f (node j))
              (CReal.neg (f (node (j+(cells+1))))))))
      have hend : j + (cells+1) = (j+1)+cells := by omega
      rw [hend]
      have hleft : CReal.Equiv
          (cPartitionRect f (node j) (node (j+1)) (node j))
          (CReal.mul (CReal.ofQ' w) (f (node j))) := by
        unfold cPartitionRect
        exact CReal.mul_congr_left (TrigAdd.equiv_ofQ'_of_eqv (hstep j))
      have hright : CReal.Equiv
          (cPartitionRect f (node j) (node (j+1)) (node (j+1)))
          (CReal.mul (CReal.ofQ' w) (f (node (j+1)))) := by
        unfold cPartitionRect
        exact CReal.mul_congr_left (TrigAdd.equiv_ofQ'_of_eqv (hstep j))
      have htail := mesh_endpoint_gap f node w hstep cells (j+1)
      have hsubst := cadd_equiv_congr hleft htail
      have halg := endpoint_shuffle
        (CReal.ofQ' w) (f (node j)) (f (node (j+1)))
        (meshRightSum f node (j+1) cells)
        (f (node ((j+1)+cells)))
      have hrestore : CReal.Equiv
          (CReal.add
            (CReal.add
              (CReal.mul (CReal.ofQ' w) (f (node (j+1))))
              (meshRightSum f node (j+1) cells))
            (CReal.mul (CReal.ofQ' w)
              (CReal.add (f (node j))
                (CReal.neg (f (node ((j+1)+cells)))))))
          (CReal.add
            (CReal.add
              (cPartitionRect f (node j) (node (j+1)) (node (j+1)))
              (meshRightSum f node (j+1) cells))
            (CReal.mul (CReal.ofQ' w)
              (CReal.add (f (node j))
                (CReal.neg (f (node ((j+1)+cells))))))) :=
        cadd_equiv_congr
          (cadd_equiv_congr (CReal.Equiv.symm hright) (CReal.Equiv.refl _))
          (CReal.Equiv.refl _)
      exact hsubst.trans (halg.trans hrestore)

private theorem unitNode_zero_eqv (M : Nat) : (unitNode M 0).eqv 0 := by
  unfold unitNode
  exact gridNode_zero_eqv 1 1 (M+1) (by decide) (Nat.succ_pos M)

private theorem unitNode_end_eqv (M : Nat) : (unitNode M (M+1)).eqv 1 := by
  unfold unitNode
  refine Q'.eqv_trans _ (rat 1 1 (by decide)) _
    (gridNode_endpoint_eqv 1 1 (M+1) (by decide) (Nat.succ_pos M)) ?_
  unfold rat
  decide

private theorem unitNode_step_eqv (M i : Nat) :
    (unitNode M (i+1) + -unitNode M i).eqv (unitWidth M) := by
  unfold unitNode unitWidth
  exact gridNode_step_eqv 1 1 (M+1) i (by decide) (Nat.succ_pos M)

private theorem unitLeft_equiv_mesh (M : Nat) :
    CReal.Equiv (unitLeftSeq M)
      (meshLeftSum doubledQuadrantSemi (unitNode M) 0 (M+1)) := by
  have hcells : PartitionEqv
      (cutCells 0 (unitMeshCuts M) 1)
      (cutCells (unitNode M 0) (unitMeshCuts M) (unitNode M (M+1))) :=
    cutCells_eqv_congr (Q'.eqv_symm (unitNode_zero_eqv M))
      (Q'.eqv_symm (unitNode_end_eqv M))
      (CutListEqv.refl (unitMeshCuts M))
  have he := partitionEqv_left doubledQuadrantSemi
    doubledQuadrantSemi_eqv_congr hcells
  have hend : meshEndIndex 0 M = M+1 := by
    simpa only [Nat.zero_add] using meshEndIndex_eq 0 M
  have hm : cPartitionLeftSum doubledQuadrantSemi
      (cutCells (unitNode M 0) (unitMeshCuts M) (unitNode M (M+1))) =
      meshLeftSum doubledQuadrantSemi (unitNode M) 0 (M+1) := by
    simpa only [unitMeshCuts, uniformMeshCuts, unitNode, hend] using
      partitionLeftSum_meshCuts doubledQuadrantSemi (unitNode M) M 0
  rw [hm] at he
  exact he

private theorem unitRight_equiv_mesh (M : Nat) :
    CReal.Equiv (unitRightSeq M)
      (meshRightSum doubledQuadrantSemi (unitNode M) 0 (M+1)) := by
  have hcells : PartitionEqv
      (cutCells 0 (unitMeshCuts M) 1)
      (cutCells (unitNode M 0) (unitMeshCuts M) (unitNode M (M+1))) :=
    cutCells_eqv_congr (Q'.eqv_symm (unitNode_zero_eqv M))
      (Q'.eqv_symm (unitNode_end_eqv M))
      (CutListEqv.refl (unitMeshCuts M))
  have he := partitionEqv_right doubledQuadrantSemi
    doubledQuadrantSemi_eqv_congr hcells
  have hend : meshEndIndex 0 M = M+1 := by
    simpa only [Nat.zero_add] using meshEndIndex_eq 0 M
  have hm : cPartitionRightSum doubledQuadrantSemi
      (cutCells (unitNode M 0) (unitMeshCuts M) (unitNode M (M+1))) =
      meshRightSum doubledQuadrantSemi (unitNode M) 0 (M+1) := by
    simpa only [unitMeshCuts, uniformMeshCuts, unitNode, hend] using
      partitionRightSum_meshCuts doubledQuadrantSemi (unitNode M) M 0
  rw [hm] at he
  exact he

private theorem cx_one_one_eqv_zero :
    (cx 1 1 (by decide)).eqv 0 := by
  unfold cx cden
  show (Q'.mkPos _ _ _).num * ((0 : Q').den : Int) =
    (0 : Q').num * ((Q'.mkPos _ _ _).den : Int)
  rw [Q'.mkPos_num, zero_den_cast, zero_num_cast, Int.mul_one, Int.zero_mul]
  omega

theorem doubledQuadrantSemi_zero_equiv_two :
    CReal.Equiv (doubledQuadrantSemi 0) (CReal.ofQ' 2) := by
  have hnode := doubledQuadrantSemi_eqv_congr
    (Q'.eqv_symm cx_one_one_eqv_zero)
  have hcircle := doubledQuadrantSemi_cx_equiv_twoCy 1 1 (by decide) (by decide)
  have hcy : (cy 1 1 (by decide) + cy 1 1 (by decide)).eqv 2 := by
    refine Q'.eqv_trans _ (1+1) _
      (Q'.add_eqv_congr' (cy_diag_eqv_one 1 (by decide))
        (cy_diag_eqv_one 1 (by decide))) ?_
    decide
  exact hnode.trans (hcircle.trans (TrigAdd.equiv_ofQ'_of_eqv hcy))

theorem doubledQuadrantSemi_one_equiv_zero :
    CReal.Equiv (doubledQuadrantSemi 1) CReal.czero := by
  have hnot : ¬ ((0 : Q') ≤ (1 : Q') ∧ (1 : Q') < (1 : Q')) := by
    intro h
    exact (Int.lt_irrefl 1) h.2
  simp only [doubledQuadrantSemi, quadrantSemi, dif_neg hnot]
  exact TrigAdd.equiv_of_approx_eqv (fun _ => Q'.eqv_of_eq (Q'.add_zero' 0))

def unitGapQ (M : Nat) : Q' :=
  Q'.mkPos 2 (M+1) (Nat.succ_pos M)

private theorem unitWidth_mul_two_eqv_gap (M : Nat) :
    (unitWidth M * (2 : Q')).eqv (unitGapQ M) := by
  show (unitWidth M * (2 : Q')).num * ((unitGapQ M).den : Int) =
    (unitGapQ M).num * ((unitWidth M * (2 : Q')).den : Int)
  unfold unitWidth gridMesh rat unitGapQ
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    two_num_cast, two_den_cast, Int.mul_one]
  push_cast
  omega

private theorem unit_boundary_equiv_gap (M : Nat) :
    CReal.Equiv
      (CReal.mul (CReal.ofQ' (unitWidth M))
        (CReal.add (doubledQuadrantSemi (unitNode M 0))
          (CReal.neg (doubledQuadrantSemi (unitNode M (M+1))))))
      (CReal.ofQ' (unitGapQ M)) := by
  have hzeroNode : CReal.Equiv
      (doubledQuadrantSemi (unitNode M 0)) (CReal.ofQ' 2) :=
    (doubledQuadrantSemi_eqv_congr (unitNode_zero_eqv M)).trans
      doubledQuadrantSemi_zero_equiv_two
  have honeNode : CReal.Equiv
      (doubledQuadrantSemi (unitNode M (M+1))) CReal.czero :=
    (doubledQuadrantSemi_eqv_congr (unitNode_end_eqv M)).trans
      doubledQuadrantSemi_one_equiv_zero
  have hinner₁ := cadd_equiv_congr hzeroNode (CReal.neg_congr honeNode)
  have hinner₂ : CReal.Equiv
      (CReal.add (CReal.ofQ' 2) (CReal.neg CReal.czero))
      (CReal.ofQ' 2) :=
    TrigAdd.equiv_of_approx_eqv (fun _ => by
      change ((2 : Q') + -(0 : Q')).eqv (2 : Q')
      ring_qeqv)
  have hmul : CReal.Equiv
      (CReal.mul (CReal.ofQ' (unitWidth M))
        (CReal.add (doubledQuadrantSemi (unitNode M 0))
          (CReal.neg (doubledQuadrantSemi (unitNode M (M+1))))))
      (CReal.mul (CReal.ofQ' (unitWidth M)) (CReal.ofQ' 2)) :=
    cmul_equiv_congr (CReal.Equiv.refl (CReal.ofQ' (unitWidth M)))
      (hinner₁.trans hinner₂)
  exact hmul.trans
    ((CReal.Equiv.symm (CRealAlg.ofQ'_mul (unitWidth M) 2)).trans
      (TrigAdd.equiv_ofQ'_of_eqv (unitWidth_mul_two_eqv_gap M)))

/-- The uniform left and right endpoint sums differ by exactly `2/(M+1)`.
This is a finite telescoping identity, not a measured or asymptotic bound. -/
theorem unit_endpoint_gap_equiv (M : Nat) :
    CReal.Equiv (unitLeftSeq M)
      (CReal.add (unitRightSeq M) (CReal.ofQ' (unitGapQ M))) := by
  have hgap := mesh_endpoint_gap doubledQuadrantSemi (unitNode M)
    (unitWidth M) (unitNode_step_eqv M) (M+1) 0
  have hleft := unitLeft_equiv_mesh M
  have hright := unitRight_equiv_mesh M
  have hend : 0 + (M+1) = M+1 := by omega
  rw [hend] at hgap
  exact hleft.trans (hgap.trans
    (cadd_equiv_congr (CReal.Equiv.symm hright)
      (unit_boundary_equiv_gap M)))

end YMGap.Continuum.SemicircleUniformEndpointGap

#print axioms YMGap.Continuum.SemicircleUniformEndpointGap.doubledQuadrantSemi_zero_equiv_two
#print axioms YMGap.Continuum.SemicircleUniformEndpointGap.doubledQuadrantSemi_one_equiv_zero
#print axioms YMGap.Continuum.SemicircleUniformEndpointGap.unit_endpoint_gap_equiv
