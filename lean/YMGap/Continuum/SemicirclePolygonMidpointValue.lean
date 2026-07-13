/-
# Polygon endpoint sums and the value of the semicircle midpoint integral

This successor leaves `SemicirclePolygonMidpointBridge` frozen at its checked
common-refinement theorem.  It identifies the polygon endpoint partitions with
the rational lower/upper polygon sums, passes the independently refined
uniform endpoint sums to the unconditional midpoint integral, and squeezes its
value to `pi/2`.
-/

import YMGap.Continuum.SemicirclePolygonMidpointBridge

namespace YMGap.Continuum.SemicirclePolygonMidpointValue

open YMGap.Constructive
open YMGap.Continuum.SemicircleRationalPolygon
open YMGap.Continuum.SemicircleIntegral
open YMGap.Continuum.SemicircleBoundClosed
open YMGap.Continuum.SemicircleAtanPartitionInsertion
open YMGap.Continuum.SemicircleAtanFiniteMeshBridge
open YMGap.Continuum.SemicirclePolygonMidpointBridge

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl

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

private theorem cx_nonneg_of_le (n j : Nat) (hn : 0 < n) (hj : j ≤ n) :
    (0 : Q') ≤ cx n j hn := by
  rw [Q'.zero_le_iff_num_nonneg]
  unfold cx
  rw [Q'.mkPos_num]
  have hsqN : j * j ≤ n * n := Nat.mul_le_mul hj hj
  have hsqI : (j:Int) * (j:Int) ≤ (n:Int) * (n:Int) := by
    exact_mod_cast hsqN
  omega

private theorem cx_lt_one_of_pos (n j : Nat) (hn : 0 < n) (hj : 0 < j) :
    cx n j hn < (1 : Q') := by
  show (cx n j hn).num * (((1 : Q').den : Int)) <
    (1 : Q').num * ((cx n j hn).den : Int)
  unfold cx cden
  rw [Q'.mkPos_num, Q'.mkPos_den]
  change ((n:Int)*(n:Int) - (j:Int)*(j:Int)) * 1 <
    1 * (((n*n + j*j : Nat) : Int))
  push_cast
  have hjI : (0 : Int) < (j:Int) := by exact_mod_cast hj
  have hsq : (0 : Int) < (j:Int)*(j:Int) := Int.mul_pos hjI hjI
  simp only [Int.mul_one, Int.one_mul]
  omega

private theorem cy_pos_of_pos (n j : Nat) (hn : 0 < n) (hj : 0 < j) :
    (0 : Q') < cy n j hn := by
  show (0 : Int) * ((cy n j hn).den : Int) <
    (cy n j hn).num * (1 : Int)
  unfold cy
  rw [Q'.mkPos_num, Int.zero_mul, Int.mul_one]
  have hnI : (0:Int) < (n:Int) := by exact_mod_cast hn
  have hjI : (0:Int) < (j:Int) := by exact_mod_cast hj
  exact Int.mul_pos (Int.mul_pos (by decide) hnI) hjI

private theorem cx_zero_eqv_one (n : Nat) (hn : 0 < n) :
    (cx n 0 hn).eqv 1 := by
  unfold cx cden
  show (Q'.mkPos _ _ _).num * (((1 : Q').den : Int)) =
    (1 : Q').num * (((Q'.mkPos _ _ _).den : Int))
  rw [Q'.mkPos_num, Q'.mkPos_den]
  change ((n:Int)*(n:Int) - 0*0) * 1 =
    1 * (((n*n + 0*0 : Nat) : Int))
  push_cast
  simp only [Int.zero_mul, Int.mul_zero, Int.sub_zero, Int.mul_one,
    Int.one_mul]
  omega

private theorem quadrantRad_pos_local {x : Q'} (hx0 : (0 : Q') ≤ x)
    (hx1 : x < (1 : Q')) : (0 : Q') < quadrantRad x := by
  have hxx1 : x * x < (1 : Q') := by
    have hmul : x * x ≤ x * 1 :=
      Q'.mul_le_mul_of_nonneg_left x 1 x (Q'.le_of_lt hx1) hx0
    have hxx : x * x ≤ x :=
      Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.mul_one_eqv x))
    exact Q'.lt_of_le_of_lt hxx hx1
  exact HKPos.one_sub_pos hxx1

private theorem quadrantRad_le_one_local (x : Q') : quadrantRad x ≤ (1 : Q') := by
  have hs : (0 : Q') ≤ x * x := SumOfSquares.q_mul_self_nonneg x
  have hn : -(x * x) ≤ (0 : Q') := Q'.nonpos_neg_of_nonneg hs
  unfold quadrantRad
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 (-(x*x)) 0 hn) ?_
  exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1))

private theorem quadrantRad_sq_le_local {x : Q'} (hx0 : (0 : Q') ≤ x)
    (hx1 : x < (1 : Q')) : quadrantRad x * quadrantRad x ≤ quadrantRad x := by
  have ha0 : (0 : Q') ≤ quadrantRad x := Q'.le_of_lt (quadrantRad_pos_local hx0 hx1)
  have hmul : quadrantRad x * quadrantRad x ≤ quadrantRad x * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (quadrantRad_le_one_local x) ha0
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_of_eqv (Q'.mul_one_eqv (quadrantRad x)))

private theorem quadrantRad_cx_eqv_cy_sq (n j : Nat) (hn : 0 < n) :
    (quadrantRad (cx n j hn)).eqv (cy n j hn * cy n j hn) := by
  unfold quadrantRad
  refine Q'.eqv_trans _
    ((cx n j hn * cx n j hn + cy n j hn * cy n j hn) +
      -(cx n j hn * cx n j hn)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_symm (circle_point n j hn))
  · ring_qeqv

private theorem sqrtFrom_equiv_of_exact_square
    (a L y : Q') (ha : (0 : Q') < a) (hL : (0 : Q') < L)
    (hLa : L * L ≤ a) (hy : (0 : Q') < y)
    (hsq : a.eqv (y * y)) :
    CReal.Equiv (CReal.sqrtFrom a L ha hL hLa) (CReal.ofQ' y) := by
  have hu := CReal.sqrtFrom_leRat_of_sq a L ha hL hLa y hy
    (Q'.le_of_eqv hsq)
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hu epsilon hepsilon
  refine ⟨N, fun k hk => ?_⟩
  constructor
  · exact hN k hk
  · exact Q'.le_trans' _ _ _
      (CReal.heronSeq_lb a y ha hy (Q'.ge_of_eqv hsq) k)
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))

/-- At every polygon node, the constructed quadrant square root is the exact
rational circle ordinate, as a constructive-real equality. -/
theorem quadrantSemi_cx_equiv_cy
    (n j : Nat) (hn : 0 < n) (hj : j ≤ n) :
    CReal.Equiv (quadrantSemi (cx n j hn)) (CReal.ofQ' (cy n j hn)) := by
  cases j with
  | zero =>
      have hnot : ¬ ((0 : Q') ≤ cx n 0 hn ∧ cx n 0 hn < (1 : Q')) := by
        intro h
        have hle : (1 : Q') ≤ cx n 0 hn :=
          Q'.ge_of_eqv (cx_zero_eqv_one n hn)
        have hbad : (1 : Q') < (1 : Q') := Q'.lt_of_le_of_lt hle h.2
        exact (Int.lt_irrefl 1) hbad
      simp only [quadrantSemi, dif_neg hnot]
      exact TrigAdd.equiv_ofQ'_of_eqv
        (Q'.eqv_symm (SemicirclePolygonMidpointBridge.cy_zero_eqv n hn))
  | succ j =>
      have hjpos : 0 < j+1 := Nat.succ_pos j
      have hp : (0 : Q') ≤ cx n (j+1) hn ∧
          cx n (j+1) hn < (1 : Q') :=
        ⟨cx_nonneg_of_le n (j+1) hn hj,
          cx_lt_one_of_pos n (j+1) hn hjpos⟩
      simp only [quadrantSemi, dif_pos hp]
      exact sqrtFrom_equiv_of_exact_square
        (quadrantRad (cx n (j+1) hn)) (quadrantRad (cx n (j+1) hn))
        (cy n (j+1) hn)
        (quadrantRad_pos_local hp.1 hp.2)
        (quadrantRad_pos_local hp.1 hp.2)
        (quadrantRad_sq_le_local hp.1 hp.2)
        (cy_pos_of_pos n (j+1) hn hjpos)
        (quadrantRad_cx_eqv_cy_sq n (j+1) hn)

theorem doubledQuadrantSemi_cx_equiv_twoCy
    (n j : Nat) (hn : 0 < n) (hj : j ≤ n) :
    CReal.Equiv (doubledQuadrantSemi (cx n j hn))
      (CReal.ofQ' (cy n j hn + cy n j hn)) := by
  unfold doubledQuadrantSemi
  have h := quadrantSemi_cx_equiv_cy n j hn hj
  intro epsilon hepsilon
  let q : Q' := HalfPow.half * epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨N, hN⟩ := h q hq
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨h1, h2⟩ := hN k hk
  rw [CReal.ofQ'_approx] at h1 h2
  constructor
  · refine Q'.le_trans' _ _ _ (Q'.add_le_add h1 h1) (Q'.le_of_eqv ?_)
    refine Q'.eqv_trans _ ((cy n j hn + cy n j hn) + (q + q)) _ ?_ ?_
    · ring_qeqv
    · exact Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves epsilon)
  · change (cy n j hn + cy n j hn) ≤
      ((quadrantSemi (cx n j hn)).approx k +
        (quadrantSemi (cx n j hn)).approx k) + epsilon
    refine Q'.le_trans' _ _ _ (Q'.add_le_add h2 h2) (Q'.le_of_eqv ?_)
    refine Q'.eqv_trans _
      (((quadrantSemi (cx n j hn)).approx k +
        (quadrantSemi (cx n j hn)).approx k) + (q + q)) _ ?_ ?_
    · ring_qeqv
    · exact Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves epsilon)

/-! ## Finite mesh endpoint-sum identification -/

private def cMeshLeftSum (f : Q' → CReal) (node : Nat → Q') (j : Nat) :
    Nat → CReal
  | 0 => CReal.czero
  | cells + 1 => CReal.add
      (cPartitionRect f (node j) (node (j+1)) (node j))
      (cMeshLeftSum f node (j+1) cells)

private def cMeshRightSum (f : Q' → CReal) (node : Nat → Q') (j : Nat) :
    Nat → CReal
  | 0 => CReal.czero
  | cells + 1 => CReal.add
      (cPartitionRect f (node j) (node (j+1)) (node (j+1)))
      (cMeshRightSum f node (j+1) cells)

private theorem cPartitionLeftSum_meshCuts (f : Q' → CReal) (node : Nat → Q') :
    ∀ count j,
      cPartitionLeftSum f
        (cutCells (node j) (meshCuts node j count)
          (node (meshEndIndex j count))) =
        cMeshLeftSum f node j (count+1)
  | 0, _j => rfl
  | count + 1, j => by
      change CReal.add
          (cPartitionRect f (node j) (node (j+1)) (node j))
          (cPartitionLeftSum f
            (cutCells (node (j+1)) (meshCuts node (j+1) count)
              (node (meshEndIndex (j+1) count)))) =
        CReal.add
          (cPartitionRect f (node j) (node (j+1)) (node j))
          (cMeshLeftSum f node (j+1) (count+1))
      rw [cPartitionLeftSum_meshCuts f node count (j+1)]

private theorem cPartitionRightSum_meshCuts (f : Q' → CReal) (node : Nat → Q') :
    ∀ count j,
      cPartitionRightSum f
        (cutCells (node j) (meshCuts node j count)
          (node (meshEndIndex j count))) =
        cMeshRightSum f node j (count+1)
  | 0, _j => rfl
  | count + 1, j => by
      change CReal.add
          (cPartitionRect f (node j) (node (j+1)) (node (j+1)))
          (cPartitionRightSum f
            (cutCells (node (j+1)) (meshCuts node (j+1) count)
              (node (meshEndIndex (j+1) count)))) =
        CReal.add
          (cPartitionRect f (node j) (node (j+1)) (node (j+1)))
          (cMeshRightSum f node (j+1) (count+1))
      rw [cPartitionRightSum_meshCuts f node count (j+1)]

private def qMeshSum (g : Nat → Q') (j : Nat) : Nat → Q'
  | 0 => 0
  | cells + 1 => g j + qMeshSum g (j+1) cells

private theorem qMeshSum_eqv_finSum (g : Nat → Q') : ∀ cells j,
    (qMeshSum g j cells).eqv
      (RationalTail.finSum (fun i => g (j+i)) cells)
  | 0, _j => Q'.eqv_refl 0
  | cells + 1, j => by
      have htail : (qMeshSum g (j+1) cells).eqv
          (RationalTail.finSum (fun i => g (j+i+1)) cells) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          qMeshSum_eqv_finSum g cells (j+1)
      refine Q'.eqv_trans _
        (g j + RationalTail.finSum (fun i => g (j+i+1)) cells) _
        (Q'.add_eqv_congr_left (g j) _ _ htail) ?_
      simpa only [Nat.add_zero, Nat.add_assoc] using
        Q'.eqv_symm
          (RationalTail.finSum_peel_left (fun i => g (j+i)) cells)

private theorem cadd_equiv_congr {A A' B B' : CReal}
    (hA : CReal.Equiv A A') (hB : CReal.Equiv B B') :
    CReal.Equiv (CReal.add A B) (CReal.add A' B') :=
  CReal.Equiv.trans (CReal.add_congr_left hA) (CReal.add_congr_right hB)

private theorem cMeshRightSum_equiv_qMesh
    (f : Q' → CReal) (node : Nat → Q') (g : Nat → Q') (bound : Nat)
    (hcell : ∀ i, i < bound → CReal.Equiv
      (cPartitionRect f (node i) (node (i+1)) (node (i+1)))
      (CReal.ofQ' (g i))) : ∀ cells j,
    j + cells ≤ bound →
    CReal.Equiv (cMeshRightSum f node j cells)
      (CReal.ofQ' (qMeshSum g j cells))
  | 0, _j, _ => TrigAdd.equiv_of_approx_eqv (fun _ => Q'.eqv_refl 0)
  | cells + 1, j, hbound => by
      have hj : j < bound := by omega
      have htail : (j+1) + cells ≤ bound := by omega
      have hs := cadd_equiv_congr (hcell j hj)
        (cMeshRightSum_equiv_qMesh f node g bound hcell cells (j+1) htail)
      have hc : CReal.Equiv
          (CReal.add (CReal.ofQ' (g j))
            (CReal.ofQ' (qMeshSum g (j+1) cells)))
          (CReal.ofQ' (g j + qMeshSum g (j+1) cells)) :=
        TrigAdd.equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
      exact CReal.Equiv.trans hs hc

private theorem cMeshLeftSum_equiv_qMesh
    (f : Q' → CReal) (node : Nat → Q') (g : Nat → Q') (bound : Nat)
    (hcell : ∀ i, i < bound → CReal.Equiv
      (cPartitionRect f (node i) (node (i+1)) (node i))
      (CReal.ofQ' (g i))) : ∀ cells j,
    j + cells ≤ bound →
    CReal.Equiv (cMeshLeftSum f node j cells)
      (CReal.ofQ' (qMeshSum g j cells))
  | 0, _j, _ => TrigAdd.equiv_of_approx_eqv (fun _ => Q'.eqv_refl 0)
  | cells + 1, j, hbound => by
      have hj : j < bound := by omega
      have htail : (j+1) + cells ≤ bound := by omega
      have hs := cadd_equiv_congr (hcell j hj)
        (cMeshLeftSum_equiv_qMesh f node g bound hcell cells (j+1) htail)
      have hc : CReal.Equiv
          (CReal.add (CReal.ofQ' (g j))
            (CReal.ofQ' (qMeshSum g (j+1) cells)))
          (CReal.ofQ' (g j + qMeshSum g (j+1) cells)) :=
        TrigAdd.equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
      exact CReal.Equiv.trans hs hc

private theorem finSum_reverse (g : RationalTail.QSeq) : ∀ n,
    (RationalTail.finSum g n).eqv
      (RationalTail.finSum (fun k => g (n-1-k)) n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
      have hpeel := RationalTail.finSum_peel_left (fun k => g (n-k)) n
      have hrefl : (fun k => g (n+1-1-k)) = (fun k => g (n-k)) := by
        funext k
        congr 1 <;> omega
      have htail : (fun k => g (n-(k+1))) = (fun k => g (n-1-k)) := by
        funext k
        congr 1 <;> omega
      have hih : (RationalTail.finSum (fun k => g (n-1-k)) n).eqv
          (RationalTail.finSum g n) := Q'.eqv_symm (finSum_reverse g n)
      rw [hrefl]
      show (RationalTail.finSum g n + g n).eqv
        (RationalTail.finSum (fun k => g (n-k)) (n+1))
      refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (g n) _ _ (Q'.eqv_symm hih)) ?_
      rw [← htail]
      exact Q'.eqv_symm hpeel

private theorem cmul_equiv_congr {A A' B B' : CReal}
    (hA : CReal.Equiv A A') (hB : CReal.Equiv B B') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A' B') := by
  have hr : CReal.Equiv (CReal.mul A' B) (CReal.mul A' B') :=
    (CRealAlg.cmul_comm A' B).trans
      ((CReal.mul_congr_left hB).trans (CRealAlg.cmul_comm B' A'))
  exact (CReal.mul_congr_left hA).trans hr

private theorem cPartitionRect_equiv_of
    (f : Q' → CReal) (x y s w v : Q')
    (hw : (y + -x).eqv w) (hv : CReal.Equiv (f s) (CReal.ofQ' v)) :
    CReal.Equiv (cPartitionRect f x y s) (CReal.ofQ' (w*v)) := by
  unfold cPartitionRect
  have hm := cmul_equiv_congr (TrigAdd.equiv_ofQ'_of_eqv hw) hv
  exact hm.trans (CReal.Equiv.symm (CRealAlg.ofQ'_mul w v))

private theorem cPartitionEqv_right_local (f : Q' → CReal)
    (hf : ∀ {a b : Q'}, a.eqv b → CReal.Equiv (f a) (f b))
    {cells cells' : List PartitionCell} (h : PartitionEqv cells cells') :
    CReal.Equiv (cPartitionRightSum f cells) (cPartitionRightSum f cells') := by
  induction h with
  | nil => exact CReal.Equiv.refl _
  | cons hx hy hrest ih =>
      rename_i x y x' y' cs cs'
      have hrect : CReal.Equiv
          (cPartitionRect f x y y) (cPartitionRect f x' y' y') := by
        unfold cPartitionRect
        have hw : (y + -x).eqv (y' + -x') :=
          Q'.add_eqv_congr' hy (Q'.neg_eqv_congr _ _ hx)
        exact cmul_equiv_congr (TrigAdd.equiv_ofQ'_of_eqv hw) (hf hy)
      exact cadd_equiv_congr hrect ih

private theorem cPartitionEqv_left_local (f : Q' → CReal)
    (hf : ∀ {a b : Q'}, a.eqv b → CReal.Equiv (f a) (f b))
    {cells cells' : List PartitionCell} (h : PartitionEqv cells cells') :
    CReal.Equiv (cPartitionLeftSum f cells) (cPartitionLeftSum f cells') := by
  induction h with
  | nil => exact CReal.Equiv.refl _
  | cons hx hy hrest ih =>
      rename_i x y x' y' cs cs'
      have hrect : CReal.Equiv
          (cPartitionRect f x y x) (cPartitionRect f x' y' x') := by
        unfold cPartitionRect
        have hw : (y + -x).eqv (y' + -x') :=
          Q'.add_eqv_congr' hy (Q'.neg_eqv_congr _ _ hx)
        exact cmul_equiv_congr (TrigAdd.equiv_ofQ'_of_eqv hw) (hf hx)
      exact cadd_equiv_congr hrect ih

def polygonLowerForward (N i : Nat) : Q' :=
  polygonLowerCell (N+1) (N-i) (Nat.succ_pos N)

def polygonUpperForward (N i : Nat) : Q' :=
  polygonUpperCell (N+1) (N-i) (Nat.succ_pos N)

private theorem polygon_right_cell_equiv (N i : Nat) (hi : i < N+1) :
    CReal.Equiv
      (cPartitionRect doubledQuadrantSemi
        (polygonXNode N i) (polygonXNode N (i+1)) (polygonXNode N (i+1)))
      (CReal.ofQ' (polygonLowerForward N i)) := by
  have hiN : i ≤ N := by omega
  have hmini : min i (N+1) = i := Nat.min_eq_left (by omega)
  have hmini1 : min (i+1) (N+1) = i+1 := Nat.min_eq_left (by omega)
  have hidx0 : N+1-i = (N-i)+1 := by omega
  have hidx1 : N+1-(i+1) = N-i := by omega
  simp only [polygonXNode, hmini, hmini1, hidx0, hidx1]
  unfold polygonLowerForward polygonLowerCell
  exact cPartitionRect_equiv_of doubledQuadrantSemi _ _ _ _ _
    (Q'.eqv_refl _)
    (doubledQuadrantSemi_cx_equiv_twoCy (N+1) (N-i)
      (Nat.succ_pos N) (by omega))

private theorem polygon_left_cell_equiv (N i : Nat) (hi : i < N+1) :
    CReal.Equiv
      (cPartitionRect doubledQuadrantSemi
        (polygonXNode N i) (polygonXNode N (i+1)) (polygonXNode N i))
      (CReal.ofQ' (polygonUpperForward N i)) := by
  have hmini : min i (N+1) = i := Nat.min_eq_left (by omega)
  have hmini1 : min (i+1) (N+1) = i+1 := Nat.min_eq_left (by omega)
  have hidx0 : N+1-i = (N-i)+1 := by omega
  have hidx1 : N+1-(i+1) = N-i := by omega
  simp only [polygonXNode, hmini, hmini1, hidx0, hidx1]
  unfold polygonUpperForward polygonUpperCell
  exact cPartitionRect_equiv_of doubledQuadrantSemi _ _ _ _ _
    (Q'.eqv_refl _)
    (doubledQuadrantSemi_cx_equiv_twoCy (N+1) ((N-i)+1)
      (Nat.succ_pos N) (by omega))

private theorem polygon_node_zero_eqv (N : Nat) : (polygonXNode N 0).eqv 0 := by
  unfold polygonXNode
  simp only [Nat.min_eq_left (Nat.zero_le (N+1)), Nat.sub_zero]
  unfold cx
  show (Q'.mkPos _ _ _).num * ((0 : Q').den : Int) =
    (0 : Q').num * ((Q'.mkPos _ _ _).den : Int)
  rw [Q'.mkPos_num, zero_den_cast, zero_num_cast, Int.mul_one, Int.zero_mul]
  omega

private theorem polygon_node_one_eqv (N : Nat) :
    (polygonXNode N (N+1)).eqv 1 := by
  unfold polygonXNode
  simp only [Nat.min_self, Nat.sub_self]
  exact cx_zero_eqv_one (N+1) (Nat.succ_pos N)

private theorem polygonLowerForward_sum_eqv (N : Nat) :
    (RationalTail.finSum (polygonLowerForward N) (N+1)).eqv
      (polygonLowerQ (N+1) (Nat.succ_pos N)) := by
  have hr := finSum_reverse
    (fun j => polygonLowerCell (N+1) j (Nat.succ_pos N)) (N+1)
  exact Q'.eqv_symm (by
    simpa only [polygonLowerForward] using hr)

private theorem polygonUpperForward_sum_eqv (N : Nat) :
    (RationalTail.finSum (polygonUpperForward N) (N+1)).eqv
      (polygonUpperQ (N+1) (Nat.succ_pos N)) := by
  have hr := finSum_reverse
    (fun j => polygonUpperCell (N+1) j (Nat.succ_pos N)) (N+1)
  exact Q'.eqv_symm (by
    simpa only [polygonUpperForward] using hr)

/-- The polygon right endpoint partition is exactly the rational lower sum. -/
theorem polygon_partition_right_equiv_lowerSeq (N : Nat) :
    CReal.Equiv
      (cPartitionRightSum doubledQuadrantSemi
        (cutCells 0 (polygonMeshCuts N) 1))
      (polygonLowerSeq N) := by
  let node := polygonXNode N
  have hcells : PartitionEqv
      (cutCells 0 (polygonMeshCuts N) 1)
      (cutCells (node 0) (polygonMeshCuts N) (node (N+1))) :=
    cutCells_eqv_congr (Q'.eqv_symm (polygon_node_zero_eqv N))
      (Q'.eqv_symm (polygon_node_one_eqv N))
      (CutListEqv.refl (polygonMeshCuts N))
  have he := cPartitionEqv_right_local doubledQuadrantSemi
    doubledQuadrantSemi_eqv_congr hcells
  have hend : meshEndIndex 0 N = N+1 := by
    simpa only [Nat.zero_add] using meshEndIndex_eq 0 N
  have hmesh : cPartitionRightSum doubledQuadrantSemi
      (cutCells (node 0) (polygonMeshCuts N) (node (N+1))) =
      cMeshRightSum doubledQuadrantSemi node 0 (N+1) := by
    simpa only [polygonMeshCuts, node, hend] using
      cPartitionRightSum_meshCuts doubledQuadrantSemi node N 0
  rw [hmesh] at he
  have hq := cMeshRightSum_equiv_qMesh doubledQuadrantSemi node
    (polygonLowerForward N) (N+1)
    (fun i hi => by
      change CReal.Equiv
        (cPartitionRect doubledQuadrantSemi
          (polygonXNode N i) (polygonXNode N (i+1)) (polygonXNode N (i+1)))
        (CReal.ofQ' (polygonLowerForward N i))
      exact polygon_right_cell_equiv N i hi)
    (N+1) 0 (by omega)
  have hfin : (qMeshSum (polygonLowerForward N) 0 (N+1)).eqv
      (polygonLowerQ (N+1) (Nat.succ_pos N)) :=
    Q'.eqv_trans _ _ _
      (qMeshSum_eqv_finSum (polygonLowerForward N) (N+1) 0)
      (by simpa only [Nat.zero_add] using polygonLowerForward_sum_eqv N)
  exact he.trans (hq.trans (TrigAdd.equiv_ofQ'_of_eqv hfin))

/-- The polygon left endpoint partition is exactly the rational upper sum. -/
theorem polygon_partition_left_equiv_upperSeq (N : Nat) :
    CReal.Equiv
      (cPartitionLeftSum doubledQuadrantSemi
        (cutCells 0 (polygonMeshCuts N) 1))
      (polygonUpperSeq N) := by
  let node := polygonXNode N
  have hcells : PartitionEqv
      (cutCells 0 (polygonMeshCuts N) 1)
      (cutCells (node 0) (polygonMeshCuts N) (node (N+1))) :=
    cutCells_eqv_congr (Q'.eqv_symm (polygon_node_zero_eqv N))
      (Q'.eqv_symm (polygon_node_one_eqv N))
      (CutListEqv.refl (polygonMeshCuts N))
  have he := cPartitionEqv_left_local doubledQuadrantSemi
    doubledQuadrantSemi_eqv_congr hcells
  have hend : meshEndIndex 0 N = N+1 := by
    simpa only [Nat.zero_add] using meshEndIndex_eq 0 N
  have hmesh : cPartitionLeftSum doubledQuadrantSemi
      (cutCells (node 0) (polygonMeshCuts N) (node (N+1))) =
      cMeshLeftSum doubledQuadrantSemi node 0 (N+1) := by
    simpa only [polygonMeshCuts, node, hend] using
      cPartitionLeftSum_meshCuts doubledQuadrantSemi node N 0
  rw [hmesh] at he
  have hq := cMeshLeftSum_equiv_qMesh doubledQuadrantSemi node
    (polygonUpperForward N) (N+1)
    (fun i hi => by
      change CReal.Equiv
        (cPartitionRect doubledQuadrantSemi
          (polygonXNode N i) (polygonXNode N (i+1)) (polygonXNode N i))
        (CReal.ofQ' (polygonUpperForward N i))
      exact polygon_left_cell_equiv N i hi)
    (N+1) 0 (by omega)
  have hfin : (qMeshSum (polygonUpperForward N) 0 (N+1)).eqv
      (polygonUpperQ (N+1) (Nat.succ_pos N)) :=
    Q'.eqv_trans _ _ _
      (qMeshSum_eqv_finSum (polygonUpperForward N) (N+1) 0)
      (by simpa only [Nat.zero_add] using polygonUpperForward_sum_eqv N)
  exact he.trans (hq.trans (TrigAdd.equiv_ofQ'_of_eqv hfin))

/-! ## Independently refined uniform endpoint sums -/

def unitRightSeq (M : Nat) : CReal :=
  cPartitionRightSum doubledQuadrantSemi
    (cutCells 0 (unitMeshCuts M) 1)

def unitLeftSeq (M : Nat) : CReal :=
  cPartitionLeftSum doubledQuadrantSemi
    (cutCells 0 (unitMeshCuts M) 1)

private theorem equiv_limitLe_left {A A' B : CReal}
    (hAA' : CReal.Equiv A A') (h : LimitLe A' B) : LimitLe A B := by
  apply CReal.leRat_of_equiv (CReal.add_congr_left hAA')
  exact h

private theorem equiv_limitLe_right {A B B' : CReal}
    (hBB' : CReal.Equiv B B') (h : LimitLe A B) : LimitLe A B' := by
  apply CReal.leRat_of_equiv
    (CReal.Equiv.symm (CReal.add_congr_right (CReal.neg_congr hBB')))
  exact h

/-- Every rational polygon lower sum is below every independently refined
uniform left endpoint sum. -/
theorem polygonLower_le_unitLeft (N M : Nat) :
    LimitLe (polygonLowerSeq N) (unitLeftSeq M) := by
  have h := (polygon_uniform_partition_cross_brackets N M).1
  exact equiv_limitLe_left
    (CReal.Equiv.symm (polygon_partition_right_equiv_lowerSeq N)) h

/-- Every independently refined uniform right endpoint sum is below every
rational polygon upper sum. -/
theorem unitRight_le_polygonUpper (N M : Nat) :
    LimitLe (unitRightSeq M) (polygonUpperSeq N) := by
  have h := (polygon_uniform_partition_cross_brackets N M).2
  exact equiv_limitLe_right (polygon_partition_left_equiv_upperSeq N) h

end YMGap.Continuum.SemicirclePolygonMidpointValue

#print axioms YMGap.Continuum.SemicirclePolygonMidpointValue.quadrantSemi_cx_equiv_cy
#print axioms YMGap.Continuum.SemicirclePolygonMidpointValue.doubledQuadrantSemi_cx_equiv_twoCy
#print axioms YMGap.Continuum.SemicirclePolygonMidpointValue.polygon_partition_right_equiv_lowerSeq
#print axioms YMGap.Continuum.SemicirclePolygonMidpointValue.polygon_partition_left_equiv_upperSeq
#print axioms YMGap.Continuum.SemicirclePolygonMidpointValue.polygonLower_le_unitLeft
#print axioms YMGap.Continuum.SemicirclePolygonMidpointValue.unitRight_le_polygonUpper
