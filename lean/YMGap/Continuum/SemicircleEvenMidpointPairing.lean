/-
# Symmetric pairing of even semicircle midpoint sums

For resolution `2(M+1)`, the full midpoint rule has no central node.  Its
negative and positive nodes pair exactly, and each pair is one midpoint
rectangle for the doubled quadrant semicircle on the `M+1` cell unit mesh.
-/

import YMGap.Continuum.SemicircleUniformEndpointConvergence

namespace YMGap.Continuum.SemicircleEvenMidpointPairing

open YMGap.Constructive
open YMGap.Continuum.SemicircleIntegral
open YMGap.Continuum.SemicircleBoundClosed
open YMGap.Continuum.SemicircleAtanPartitionInsertion
open YMGap.Continuum.SemicircleAtanFiniteMeshBridge
open YMGap.Continuum.SemicircleAtanInducedPartition
open YMGap.Continuum.SemicirclePolygonMidpointBridge
open YMGap.Continuum.SemicirclePolygonMidpointValue
open YMGap.Continuum.SemicircleUniformEndpointGap
open YMGap.Continuum.SemicircleUniformEndpointConvergence

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm];
             omega))

def halfCount (M : Nat) : Nat := M+1
def evenResolution (M : Nat) : Nat := 2 * halfCount M
def positiveIndex (M i : Nat) : Nat := halfCount M + i
def reflectedIndex (M i : Nat) : Nat := halfCount M - 1 - i

def quadrantMidNode (M i : Nat) : Q' :=
  Q'.mkPos ((2*i+1 : Nat) : Int) (2 * halfCount M)
    (Nat.mul_pos (by decide) (Nat.succ_pos M))

private theorem le_add_of_sub_le_q {a b q : Q'}
    (h : a + -b ≤ q) : a ≤ b + q := by
  have h' := Q'.add_le_add_right (a + -b) q b h
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_)
    (Q'.le_trans' _ _ _ h' (Q'.le_of_eqv (Q'.add_comm_eqv q b)))
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a (-b+b) 0 (Q'.neg_add_self_eqv b)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' a)

private theorem limitLe_antisymm_equiv {A B : CReal}
    (hAB : LimitLe A B) (hBA : LimitLe B A) : CReal.Equiv A B := by
  intro epsilon hepsilon
  obtain ⟨Nab, hNab⟩ := hAB epsilon hepsilon
  obtain ⟨Nba, hNba⟩ := hBA epsilon hepsilon
  refine ⟨max Nab Nba, fun n hn => ?_⟩
  have hnab : Nab ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnba : Nba ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have habSub : A.approx n + -(B.approx n) ≤ epsilon :=
    Q'.le_trans' _ _ _ (hNab n hnab)
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' epsilon)))
  have hbaSub : B.approx n + -(A.approx n) ≤ epsilon :=
    Q'.le_trans' _ _ _ (hNba n hnba)
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' epsilon)))
  exact ⟨le_add_of_sub_le_q habSub, le_add_of_sub_le_q hbaSub⟩

private theorem sqrtFrom_limitLe_of_le
    (u Lu : Q') (hu : (0 : Q') < u) (hLu : (0 : Q') < Lu)
    (hLua : Lu * Lu ≤ u)
    (v Lv : Q') (hv : (0 : Q') < v) (hLv : (0 : Q') < Lv)
    (hLva : Lv * Lv ≤ v) (huv : u ≤ v) :
    LimitLe (CReal.sqrtFrom u Lu hu hLu hLua)
      (CReal.sqrtFrom v Lv hv hLv hLva) := by
  intro epsilon hepsilon
  let c : Q' := HalfPow.half * epsilon
  have hc : (0 : Q') < c := ExpNeg.half_mul_pos epsilon hepsilon
  have hcc : (0 : Q') ≤ c*c := SumOfSquares.q_mul_self_nonneg c
  have huvc : u ≤ v + c*c :=
    Q'.le_trans' _ _ _ huv (Q'.add_le_self_of_nonneg v (c*c) hcc)
  have hs := CReal.sqrtFrom_sub_leRat
    u Lu hu hLu hLua v Lv hv hLv hLva c hc huvc
  obtain ⟨N, hN⟩ := hs c hc
  refine ⟨N, fun n hn => ?_⟩
  have htwo : (c+c).eqv epsilon := ExpNeg.two_halves epsilon
  exact Q'.le_trans' _ _ _ (hN n hn) (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ htwo
      (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' epsilon)))))

private theorem sqrtFrom_equiv_of_rad_eqv
    (u Lu : Q') (hu : (0 : Q') < u) (hLu : (0 : Q') < Lu)
    (hLua : Lu * Lu ≤ u)
    (v Lv : Q') (hv : (0 : Q') < v) (hLv : (0 : Q') < Lv)
    (hLva : Lv * Lv ≤ v) (huv : u.eqv v) :
    CReal.Equiv (CReal.sqrtFrom u Lu hu hLu hLua)
      (CReal.sqrtFrom v Lv hv hLv hLva) :=
  limitLe_antisymm_equiv
    (sqrtFrom_limitLe_of_le u Lu hu hLu hLua v Lv hv hLv hLva
      (Q'.le_of_eqv huv))
    (sqrtFrom_limitLe_of_le v Lv hv hLv hLva u Lu hu hLu hLua
      (Q'.ge_of_eqv huv))

private theorem quadrantMidNode_nonneg (M i : Nat) :
    (0 : Q') ≤ quadrantMidNode M i := by
  rw [Q'.zero_le_iff_num_nonneg]
  unfold quadrantMidNode
  rw [Q'.mkPos_num]
  exact Int.natCast_nonneg _

private theorem quadrantMidNode_lt_one (M i : Nat) (hi : i < halfCount M) :
    quadrantMidNode M i < (1 : Q') := by
  unfold halfCount at hi
  show (quadrantMidNode M i).num * ((1 : Q').den : Int) <
    (1 : Q').num * ((quadrantMidNode M i).den : Int)
  unfold quadrantMidNode halfCount
  rw [Q'.mkPos_num, Q'.mkPos_den]
  have h1d : ((1 : Q').den : Int) = 1 := by decide
  have h1n : (1 : Q').num = 1 := by decide
  rw [h1d, h1n, Int.mul_one, Int.one_mul]
  push_cast
  omega

private theorem quadrantRad_pos_local {x : Q'} (hx0 : (0 : Q') ≤ x)
    (hx1 : x < (1 : Q')) : (0 : Q') < quadrantRad x := by
  have hxx1 : x*x < (1 : Q') := by
    have hmul : x*x ≤ x*1 :=
      Q'.mul_le_mul_of_nonneg_left x 1 x (Q'.le_of_lt hx1) hx0
    have hxx : x*x ≤ x :=
      Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.mul_one_eqv x))
    exact Q'.lt_of_le_of_lt hxx hx1
  exact HKPos.one_sub_pos hxx1

private theorem quadrantRad_le_one_local (x : Q') : quadrantRad x ≤ (1 : Q') := by
  have hs : (0 : Q') ≤ x*x := SumOfSquares.q_mul_self_nonneg x
  have hn : -(x*x) ≤ (0 : Q') := Q'.nonpos_neg_of_nonneg hs
  unfold quadrantRad
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 (-(x*x)) 0 hn) ?_
  exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1))

private theorem quadrantRad_sq_le_local {x : Q'} (hx0 : (0 : Q') ≤ x)
    (hx1 : x < (1 : Q')) : quadrantRad x * quadrantRad x ≤ quadrantRad x := by
  have ha0 : (0 : Q') ≤ quadrantRad x :=
    Q'.le_of_lt (quadrantRad_pos_local hx0 hx1)
  have hm : quadrantRad x * quadrantRad x ≤ quadrantRad x * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (quadrantRad_le_one_local x) ha0
  exact Q'.le_trans' _ _ _ hm
    (Q'.le_of_eqv (Q'.mul_one_eqv (quadrantRad x)))

private theorem positiveIndex_lt (M i : Nat) (hi : i < halfCount M) :
    positiveIndex M i < evenResolution M := by
  unfold positiveIndex evenResolution halfCount at *
  omega

private theorem reflectedIndex_lt (M i : Nat) (hi : i < halfCount M) :
    reflectedIndex M i < evenResolution M := by
  unfold reflectedIndex evenResolution halfCount
  omega

private theorem positive_coord_eq (M i : Nat) :
    2 * (positiveIndex M i : Int) + 1 - (evenResolution M : Int) =
      ((2*i+1 : Nat) : Int) := by
  unfold positiveIndex evenResolution halfCount
  push_cast
  omega

private theorem reflected_coord_eq (M i : Nat) (hi : i < halfCount M) :
    2 * (reflectedIndex M i : Int) + 1 - (evenResolution M : Int) =
      -((2*i+1 : Nat) : Int) := by
  have hiM : i ≤ M := by
    unfold halfCount at hi
    omega
  unfold reflectedIndex evenResolution halfCount
  push_cast [Int.natCast_sub hiM]
  omega

private theorem mkPos_rad_eqv (A : Int) (D : Nat) (hD : 0 < D) :
    (Q'.mkPos ((D:Int)*(D:Int) - A*A) (D*D) (Nat.mul_pos hD hD)).eqv
      (quadrantRad (Q'.mkPos A D hD)) := by
  unfold quadrantRad
  show (Q'.mkPos ((D:Int)*(D:Int) - A*A) (D*D) _).num *
      ((1 + -(Q'.mkPos A D hD * Q'.mkPos A D hD)).den : Int) =
    (1 + -(Q'.mkPos A D hD * Q'.mkPos A D hD)).num *
      ((Q'.mkPos ((D:Int)*(D:Int) - A*A) (D*D) _).den : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
    Q'.mkPos_den, one_num_cast, one_den_cast, Int.one_mul]
  push_cast
  simp only [Int.mul_one, Int.sub_eq_add_neg]

private theorem positive_radicand_eqv_quadrant (M i : Nat)
    (hi : i < halfCount M) :
    (oneMinusSqNode (evenResolution M) (positiveIndex M i)
      (Nat.mul_pos (by decide) (Nat.succ_pos M)) (positiveIndex_lt M i hi)).eqv
      (quadrantRad (quadrantMidNode M i)) := by
  have hraw :
      (oneMinusSqNode (evenResolution M) (positiveIndex M i)
        (Nat.mul_pos (by decide) (Nat.succ_pos M)) (positiveIndex_lt M i hi)).eqv
      (Q'.mkPos
        ((evenResolution M : Int)*(evenResolution M : Int) -
          ((2*i+1 : Nat) : Int)*((2*i+1 : Nat) : Int))
        (evenResolution M * evenResolution M)
        (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos M))
          (Nat.mul_pos (by decide) (Nat.succ_pos M)))) := by
    unfold oneMinusSqNode omsNum omsDen
    rw [positive_coord_eq]
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hraw
    (by
      unfold quadrantMidNode
      exact mkPos_rad_eqv ((2*i+1 : Nat) : Int) (evenResolution M)
        (Nat.mul_pos (by decide) (Nat.succ_pos M)))

private theorem reflected_radicand_eqv_positive (M i : Nat)
    (hi : i < halfCount M) :
    (oneMinusSqNode (evenResolution M) (reflectedIndex M i)
      (Nat.mul_pos (by decide) (Nat.succ_pos M)) (reflectedIndex_lt M i hi)).eqv
    (oneMinusSqNode (evenResolution M) (positiveIndex M i)
      (Nat.mul_pos (by decide) (Nat.succ_pos M)) (positiveIndex_lt M i hi)) := by
  unfold oneMinusSqNode omsNum omsDen
  rw [reflected_coord_eq M i hi, positive_coord_eq M i]
  unfold evenResolution halfCount
  simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
  exact Q'.eqv_refl _

theorem positive_nodeWeight_equiv_quadrant (M i : Nat)
    (hi : i < halfCount M) :
    CReal.Equiv
      (nodeWeight (evenResolution M)
        (Nat.mul_pos (by decide) (Nat.succ_pos M)) (positiveIndex M i))
      (quadrantSemi (quadrantMidNode M i)) := by
  have hk := positiveIndex_lt M i hi
  have hx0 := quadrantMidNode_nonneg M i
  have hx1 := quadrantMidNode_lt_one M i hi
  have hp : (0 : Q') ≤ quadrantMidNode M i ∧
      quadrantMidNode M i < (1 : Q') := ⟨hx0, hx1⟩
  rw [nodeWeight, dif_pos hk, quadrantSemi, dif_pos hp]
  exact sqrtFrom_equiv_of_rad_eqv
    (oneMinusSqNode (evenResolution M) (positiveIndex M i)
      (Nat.mul_pos (by decide) (Nat.succ_pos M)) hk)
    (nodeLB (evenResolution M) (Nat.mul_pos (by decide) (Nat.succ_pos M)))
    (oneMinusSqNode_pos _ hk) (nodeLB_pos _ ) (nodeLB_sq_le _ hk)
    (quadrantRad (quadrantMidNode M i)) (quadrantRad (quadrantMidNode M i))
    (quadrantRad_pos_local hx0 hx1) (quadrantRad_pos_local hx0 hx1)
    (quadrantRad_sq_le_local hx0 hx1)
    (positive_radicand_eqv_quadrant M i hi)

theorem reflected_nodeWeight_equiv_positive (M i : Nat)
    (hi : i < halfCount M) :
    CReal.Equiv
      (nodeWeight (evenResolution M)
        (Nat.mul_pos (by decide) (Nat.succ_pos M)) (reflectedIndex M i))
      (nodeWeight (evenResolution M)
        (Nat.mul_pos (by decide) (Nat.succ_pos M)) (positiveIndex M i)) := by
  have hr := reflectedIndex_lt M i hi
  have hp := positiveIndex_lt M i hi
  simp only [nodeWeight, dif_pos hr, dif_pos hp]
  exact sqrtFrom_equiv_of_rad_eqv
    (oneMinusSqNode (evenResolution M) (reflectedIndex M i)
      (Nat.mul_pos (by decide) (Nat.succ_pos M)) hr)
    (nodeLB (evenResolution M) (Nat.mul_pos (by decide) (Nat.succ_pos M)))
    (oneMinusSqNode_pos _ hr) (nodeLB_pos _) (nodeLB_sq_le _ hr)
    (oneMinusSqNode (evenResolution M) (positiveIndex M i)
      (Nat.mul_pos (by decide) (Nat.succ_pos M)) hp)
    (nodeLB (evenResolution M) (Nat.mul_pos (by decide) (Nat.succ_pos M)))
    (oneMinusSqNode_pos _ hp) (nodeLB_pos _) (nodeLB_sq_le _ hp)
    (reflected_radicand_eqv_positive M i hi)

/-! ## Finite symmetric reindexing -/

private theorem cadd_equiv_congr {A A' B B' : CReal}
    (hA : CReal.Equiv A A') (hB : CReal.Equiv B B') :
    CReal.Equiv (CReal.add A B) (CReal.add A' B') :=
  (CReal.add_congr_left hA).trans (CReal.add_congr_right hB)

private theorem cmul_equiv_congr {A A' B B' : CReal}
    (hA : CReal.Equiv A A') (hB : CReal.Equiv B B') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A' B') := by
  have hr : CReal.Equiv (CReal.mul A' B) (CReal.mul A' B') :=
    (CRealAlg.cmul_comm A' B).trans
      ((CReal.mul_congr_left hB).trans (CRealAlg.cmul_comm B' A'))
  exact (CReal.mul_congr_left hA).trans hr

private theorem csum_congr_lt {A B : Nat → CReal} : ∀ n,
    (∀ i, i < n → CReal.Equiv (A i) (B i)) →
    CReal.Equiv (CReal.csum A n) (CReal.csum B n)
  | 0, _ => CReal.Equiv.refl _
  | n+1, h => by
      exact cadd_equiv_congr
        (csum_congr_lt n (fun i hi => h i (by omega)))
        (h n (Nat.lt_succ_self n))

private theorem csum_split (A : Nat → CReal) (m : Nat) : ∀ n,
    CReal.Equiv (CReal.csum A (m+n))
      (CReal.add (CReal.csum A m) (CReal.csum (fun i => A (m+i)) n))
  | 0 => TrigAdd.equiv_of_approx_eqv (fun k => by
      change ((CReal.csum A m).approx k).eqv
        ((CReal.csum A m).approx k + 0)
      exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _)))
  | n+1 => by
      change CReal.Equiv
        (CReal.add (CReal.csum A (m+n)) (A (m+n)))
        (CReal.add (CReal.csum A m)
          (CReal.add (CReal.csum (fun i => A (m+i)) n) (A (m+n))))
      have hs := cadd_equiv_congr (csum_split A m n)
        (CReal.Equiv.refl (A (m+n)))
      exact hs.trans (TrigAdd.equiv_of_approx_eqv (fun k => by
        change (((CReal.csum A m).approx k +
            (CReal.csum (fun i => A (m+i)) n).approx k) +
              (A (m+n)).approx k).eqv
          ((CReal.csum A m).approx k +
            ((CReal.csum (fun i => A (m+i)) n).approx k +
              (A (m+n)).approx k))
        exact Q'.add_assoc_eqv _ _ _))

private theorem finSum_peel_left (g : RationalTail.QSeq) : ∀ n,
    (RationalTail.finSum g (n+1)).eqv
      (g 0 + RationalTail.finSum (fun k => g (k+1)) n)
  | 0 => by
      show ((0 : Q') + g 0).eqv (g 0 + (0 : Q'))
      rw [Q'.zero_add', Q'.add_zero']
      exact Q'.eqv_refl _
  | n+1 => by
      have ih := finSum_peel_left g n
      show (RationalTail.finSum g (n+1) + g (n+1)).eqv
        (g 0 + RationalTail.finSum (fun k => g (k+1)) (n+1))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ ih) ?_
      exact Q'.add_assoc_eqv _ _ _

private theorem finSum_reverse (g : RationalTail.QSeq) : ∀ n,
    (RationalTail.finSum g n).eqv
      (RationalTail.finSum (fun k => g (n-1-k)) n)
  | 0 => Q'.eqv_refl 0
  | n+1 => by
      have hpeel := finSum_peel_left (fun k => g (n-k)) n
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

private theorem csum_reverse (A : Nat → CReal) (n : Nat) :
    CReal.Equiv (CReal.csum A n)
      (CReal.csum (fun i => A (n-1-i)) n) := by
  exact TrigAdd.equiv_of_approx_eqv (fun k => by
    rw [CReal.csum_approx A n k,
      CReal.csum_approx (fun i => A (n-1-i)) n k]
    exact finSum_reverse (fun i => (A i).approx k) n)

def evenTerm (M k : Nat) : CReal :=
  CReal.mul
    (CReal.ofQ' (lebW (evenResolution M)
      (Nat.mul_pos (by decide) (Nat.succ_pos M))))
    (nodeWeight (evenResolution M)
      (Nat.mul_pos (by decide) (Nat.succ_pos M)) k)

def quadrantMidTerm (M i : Nat) : CReal :=
  cPartitionRect doubledQuadrantSemi
    (unitNode M i) (unitNode M (i+1)) (quadrantMidNode M i)

def quadrantMidSeq (M : Nat) : CReal :=
  CReal.csum (quadrantMidTerm M) (halfCount M)

def evenMidSeq (M : Nat) : CReal := seqSemi (2*M+1)

private theorem evenMidSeq_equiv_csum (M : Nat) :
    CReal.Equiv (evenMidSeq M)
      (CReal.csum (evenTerm M) (evenResolution M)) := by
  have hres : 2*M+1+1 = evenResolution M := by
    unfold evenResolution halfCount
    omega
  unfold evenMidSeq seqSemi
  cases hres
  unfold semiSum evenTerm
  exact CReal.Equiv.refl _

private theorem lebW_even_eqv_unitWidth (M : Nat) :
    (lebW (evenResolution M) (Nat.mul_pos (by decide) (Nat.succ_pos M))).eqv
      (unitWidth M) := by
  show (lebW (evenResolution M) _).num * ((unitWidth M).den : Int) =
    (unitWidth M).num * ((lebW (evenResolution M) _).den : Int)
  unfold lebW evenResolution halfCount unitWidth gridMesh rat
  simp only [Q'.mkPos_num, Q'.mkPos_den]
  push_cast
  omega

private theorem paired_algebra (W Q : CReal) :
    CReal.Equiv (CReal.add (CReal.mul W Q) (CReal.mul W Q))
      (CReal.mul W (CReal.add Q Q)) :=
  TrigAdd.equiv_of_approx_eqv (fun k => by
    change (W.approx k * Q.approx k + W.approx k * Q.approx k).eqv
      (W.approx k * (Q.approx k + Q.approx k))
    exact Q'.eqv_symm (Q'.mul_add_eqv _ _ _))

theorem pairedTerm_equiv_quadrantMidTerm (M i : Nat)
    (hi : i < halfCount M) :
    CReal.Equiv
      (CReal.add (evenTerm M (reflectedIndex M i))
        (evenTerm M (positiveIndex M i)))
      (quadrantMidTerm M i) := by
  let W := CReal.ofQ' (unitWidth M)
  let Q := quadrantSemi (quadrantMidNode M i)
  have hw : CReal.Equiv
      (CReal.ofQ' (lebW (evenResolution M)
        (Nat.mul_pos (by decide) (Nat.succ_pos M)))) W :=
    TrigAdd.equiv_ofQ'_of_eqv (lebW_even_eqv_unitWidth M)
  have hp := positive_nodeWeight_equiv_quadrant M i hi
  have hr := (reflected_nodeWeight_equiv_positive M i hi).trans hp
  have hneg : CReal.Equiv (evenTerm M (reflectedIndex M i))
      (CReal.mul W Q) := by
    unfold evenTerm
    exact cmul_equiv_congr hw hr
  have hpos : CReal.Equiv (evenTerm M (positiveIndex M i))
      (CReal.mul W Q) := by
    unfold evenTerm
    exact cmul_equiv_congr hw hp
  have hpair := (cadd_equiv_congr hneg hpos).trans (paired_algebra W Q)
  have hwidth : (unitNode M (i+1) + -unitNode M i).eqv (unitWidth M) := by
    unfold unitNode unitWidth
    exact gridNode_step_eqv 1 1 (M+1) i (by decide) (Nat.succ_pos M)
  have hrect : CReal.Equiv (quadrantMidTerm M i)
      (CReal.mul W (CReal.add Q Q)) := by
    unfold quadrantMidTerm cPartitionRect doubledQuadrantSemi W Q
    exact CReal.mul_congr_left (TrigAdd.equiv_ofQ'_of_eqv hwidth)
  exact hpair.trans (CReal.Equiv.symm hrect)

/-- The even full-interval midpoint rule is exactly the positive-quadrant
midpoint rule for the doubled semicircle. -/
theorem evenMidSeq_equiv_quadrantMidSeq (M : Nat) :
    CReal.Equiv (evenMidSeq M) (quadrantMidSeq M) := by
  let m := halfCount M
  let A := evenTerm M
  have heven : evenResolution M = m+m := by
    unfold evenResolution m
    omega
  have hsplit : CReal.Equiv (CReal.csum A (evenResolution M))
      (CReal.add (CReal.csum A m)
        (CReal.csum (fun i => A (m+i)) m)) := by
    rw [heven]
    exact csum_split A m m
  have hrev := csum_reverse A m
  have hfirst : CReal.Equiv
      (CReal.add (CReal.csum A m) (CReal.csum (fun i => A (m+i)) m))
      (CReal.add (CReal.csum (fun i => A (m-1-i)) m)
        (CReal.csum (fun i => A (m+i)) m)) :=
    CReal.add_congr_left hrev
  have hadd := CReal.Equiv.symm
    (CRealAlg.csum_add (fun i => A (m-1-i)) (fun i => A (m+i)) m)
  have hterms : CReal.Equiv
      (CReal.csum
        (fun i => CReal.add (A (m-1-i)) (A (m+i))) m)
      (CReal.csum (quadrantMidTerm M) m) := by
    apply csum_congr_lt m
    intro i hi
    change CReal.Equiv
      (CReal.add (evenTerm M (reflectedIndex M i))
        (evenTerm M (positiveIndex M i)))
      (quadrantMidTerm M i)
    exact pairedTerm_equiv_quadrantMidTerm M i hi
  exact (evenMidSeq_equiv_csum M).trans
    (hsplit.trans (hfirst.trans (hadd.trans hterms)))

/-! ## Midpoint Darboux bracket on the same unit cells -/

def unitRightTerm (M i : Nat) : CReal :=
  cPartitionRect doubledQuadrantSemi
    (unitNode M i) (unitNode M (i+1)) (unitNode M (i+1))

def unitLeftTerm (M i : Nat) : CReal :=
  cPartitionRect doubledQuadrantSemi
    (unitNode M i) (unitNode M (i+1)) (unitNode M i)

private def meshRightSum (f : Q' → CReal) (node : Nat → Q') (j : Nat) :
    Nat → CReal
  | 0 => CReal.czero
  | cells+1 => CReal.add
      (cPartitionRect f (node j) (node (j+1)) (node (j+1)))
      (meshRightSum f node (j+1) cells)

private def meshLeftSum (f : Q' → CReal) (node : Nat → Q') (j : Nat) :
    Nat → CReal
  | 0 => CReal.czero
  | cells+1 => CReal.add
      (cPartitionRect f (node j) (node (j+1)) (node j))
      (meshLeftSum f node (j+1) cells)

private theorem partitionRightSum_meshCuts (f : Q' → CReal) (node : Nat → Q') :
    ∀ count j,
      cPartitionRightSum f
        (cutCells (node j) (meshCuts node j count)
          (node (meshEndIndex j count))) =
        meshRightSum f node j (count+1)
  | 0, _ => rfl
  | count+1, j => by
      change CReal.add
          (cPartitionRect f (node j) (node (j+1)) (node (j+1)))
          (cPartitionRightSum f
            (cutCells (node (j+1)) (meshCuts node (j+1) count)
              (node (meshEndIndex (j+1) count)))) =
        CReal.add
          (cPartitionRect f (node j) (node (j+1)) (node (j+1)))
          (meshRightSum f node (j+1) (count+1))
      rw [partitionRightSum_meshCuts f node count (j+1)]

private theorem partitionLeftSum_meshCuts (f : Q' → CReal) (node : Nat → Q') :
    ∀ count j,
      cPartitionLeftSum f
        (cutCells (node j) (meshCuts node j count)
          (node (meshEndIndex j count))) =
        meshLeftSum f node j (count+1)
  | 0, _ => rfl
  | count+1, j => by
      change CReal.add
          (cPartitionRect f (node j) (node (j+1)) (node j))
          (cPartitionLeftSum f
            (cutCells (node (j+1)) (meshCuts node (j+1) count)
              (node (meshEndIndex (j+1) count)))) =
        CReal.add
          (cPartitionRect f (node j) (node (j+1)) (node j))
          (meshLeftSum f node (j+1) (count+1))
      rw [partitionLeftSum_meshCuts f node count (j+1)]

private theorem csum_peel_left (A : Nat → CReal) (n : Nat) :
    CReal.Equiv (CReal.csum A (n+1))
      (CReal.add (A 0) (CReal.csum (fun i => A (i+1)) n)) := by
  exact TrigAdd.equiv_of_approx_eqv (fun k => by
    rw [CReal.csum_approx A (n+1) k]
    rw [CReal.add_approx, CReal.csum_approx]
    change (RationalTail.finSum (fun i => (A i).approx k) (n+1)).eqv
      ((A 0).approx k +
        RationalTail.finSum (fun i => (A (i+1)).approx k) n)
    exact finSum_peel_left (fun i => (A i).approx k) n)

private theorem meshRight_equiv_csum (f : Q' → CReal) (node : Nat → Q') :
    ∀ cells j,
    CReal.Equiv (meshRightSum f node j cells)
      (CReal.csum
        (fun i => cPartitionRect f (node (j+i)) (node (j+i+1))
          (node (j+i+1))) cells)
  | 0, _ => CReal.Equiv.refl _
  | cells+1, j => by
      change CReal.Equiv
        (CReal.add
          (cPartitionRect f (node j) (node (j+1)) (node (j+1)))
          (meshRightSum f node (j+1) cells))
        (CReal.csum
          (fun i => cPartitionRect f (node (j+i)) (node (j+i+1))
            (node (j+i+1))) (cells+1))
      have htail := meshRight_equiv_csum f node cells (j+1)
      have hsub : CReal.Equiv
          (CReal.add
            (cPartitionRect f (node j) (node (j+1)) (node (j+1)))
            (meshRightSum f node (j+1) cells))
          (CReal.add
            (cPartitionRect f (node j) (node (j+1)) (node (j+1)))
            (CReal.csum
              (fun i => cPartitionRect f (node (j+1+i))
                (node (j+1+i+1)) (node (j+1+i+1))) cells)) :=
        cadd_equiv_congr (CReal.Equiv.refl _) htail
      have hpeel := csum_peel_left
        (fun i => cPartitionRect f (node (j+i)) (node (j+i+1))
          (node (j+i+1))) cells
      exact hsub.trans (CReal.Equiv.symm (by
        simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hpeel))

private theorem meshLeft_equiv_csum (f : Q' → CReal) (node : Nat → Q') :
    ∀ cells j,
    CReal.Equiv (meshLeftSum f node j cells)
      (CReal.csum
        (fun i => cPartitionRect f (node (j+i)) (node (j+i+1))
          (node (j+i))) cells)
  | 0, _ => CReal.Equiv.refl _
  | cells+1, j => by
      change CReal.Equiv
        (CReal.add
          (cPartitionRect f (node j) (node (j+1)) (node j))
          (meshLeftSum f node (j+1) cells))
        (CReal.csum
          (fun i => cPartitionRect f (node (j+i)) (node (j+i+1))
            (node (j+i))) (cells+1))
      have htail := meshLeft_equiv_csum f node cells (j+1)
      have hsub : CReal.Equiv
          (CReal.add
            (cPartitionRect f (node j) (node (j+1)) (node j))
            (meshLeftSum f node (j+1) cells))
          (CReal.add
            (cPartitionRect f (node j) (node (j+1)) (node j))
            (CReal.csum
              (fun i => cPartitionRect f (node (j+1+i))
                (node (j+1+i+1)) (node (j+1+i))) cells)) :=
        cadd_equiv_congr (CReal.Equiv.refl _) htail
      have hpeel := csum_peel_left
        (fun i => cPartitionRect f (node (j+i)) (node (j+i+1))
          (node (j+i))) cells
      exact hsub.trans (CReal.Equiv.symm (by
        simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hpeel))

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

private theorem unitNode_zero_eqv (M : Nat) : (unitNode M 0).eqv 0 := by
  unfold unitNode
  exact gridNode_zero_eqv 1 1 (M+1) (by decide) (Nat.succ_pos M)

private theorem unitNode_end_eqv (M : Nat) : (unitNode M (M+1)).eqv 1 := by
  unfold unitNode
  refine Q'.eqv_trans _ (rat 1 1 (by decide)) _
    (gridNode_endpoint_eqv 1 1 (M+1) (by decide) (Nat.succ_pos M)) ?_
  unfold rat
  decide

private theorem unitRightSeq_equiv_csum (M : Nat) :
    CReal.Equiv (unitRightSeq M)
      (CReal.csum (unitRightTerm M) (halfCount M)) := by
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
  have hs := meshRight_equiv_csum doubledQuadrantSemi (unitNode M) (M+1) 0
  simpa only [unitRightSeq, unitRightTerm, halfCount, Nat.zero_add,
    Nat.add_assoc] using he.trans hs

private theorem unitLeftSeq_equiv_csum (M : Nat) :
    CReal.Equiv (unitLeftSeq M)
      (CReal.csum (unitLeftTerm M) (halfCount M)) := by
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
  have hs := meshLeft_equiv_csum doubledQuadrantSemi (unitNode M) (M+1) 0
  simpa only [unitLeftSeq, unitLeftTerm, halfCount, Nat.zero_add,
    Nat.add_assoc] using he.trans hs

private theorem limitLe_refl (A : CReal) : LimitLe A A := by
  apply CReal.leRat_of_eventually
  refine ⟨0, fun k _ => ?_⟩
  exact Q'.le_of_eqv (Q'.add_neg_self_eqv (A.approx k))

private theorem limitLe_add {A B C D : CReal}
    (hAB : LimitLe A B) (hCD : LimitLe C D) :
    LimitLe (CReal.add A C) (CReal.add B D) := by
  have hsum := CReal.leRat_add hAB hCD
  have hzero : (0+0 : Q') ≤ 0 := Q'.le_of_eqv (by decide)
  have hsum0 := CReal.leRat_mono hsum hzero
  apply CReal.leRat_congr (b := CReal.add
    (CReal.add A (CReal.neg B)) (CReal.add C (CReal.neg D)))
  · intro k
    change ((A.approx k + C.approx k) + -(B.approx k + D.approx k)).eqv
      ((A.approx k + -(B.approx k)) + (C.approx k + -(D.approx k)))
    ring_qeqv
  · exact hsum0

private theorem limitLe_scale {A B : CReal} (c : Q')
    (hc : (0 : Q') ≤ c) (hAB : LimitLe A B) :
    LimitLe (CReal.mul (CReal.ofQ' c) A)
      (CReal.mul (CReal.ofQ' c) B) := by
  have hs := CReal.leRat_smul_nonneg hc hAB
  have hzero : c*(0 : Q') ≤ 0 := Q'.le_of_eqv (Q'.mul_zero_eqv c)
  have hs0 := CReal.leRat_mono hs hzero
  apply CReal.leRat_congr (b :=
    CReal.mul (CReal.ofQ' c) (CReal.add A (CReal.neg B)))
  · intro k
    change (c*A.approx k + -(c*B.approx k)).eqv
      (c*(A.approx k + -(B.approx k)))
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (c*A.approx k) _ _
        (Q'.eqv_symm (Q'.mul_neg_eqv c (B.approx k))))
      (Q'.eqv_symm (Q'.mul_add_eqv c (A.approx k) (-(B.approx k))))
  · exact hs0

private theorem equiv_limitLe_left {A A' B : CReal}
    (hAA' : CReal.Equiv A A') (h : LimitLe A' B) : LimitLe A B := by
  apply CReal.leRat_of_equiv (CReal.add_congr_left hAA')
  exact h

private theorem equiv_limitLe_right {A B B' : CReal}
    (hBB' : CReal.Equiv B B') (h : LimitLe A B) : LimitLe A B' := by
  apply CReal.leRat_of_equiv
    (CReal.Equiv.symm (CReal.add_congr_right (CReal.neg_congr hBB')))
  exact h

private theorem limitLe_csum {A B : Nat → CReal} : ∀ n,
    (∀ i, i < n → LimitLe (A i) (B i)) →
    LimitLe (CReal.csum A n) (CReal.csum B n)
  | 0, _ => limitLe_refl _
  | n+1, h =>
      limitLe_add
        (limitLe_csum n (fun i hi => h i (by omega)))
        (h n (Nat.lt_succ_self n))

private theorem unitNode_le_quadrantMidNode (M i : Nat) :
    unitNode M i ≤ quadrantMidNode M i := by
  show (unitNode M i).num * ((quadrantMidNode M i).den : Int) ≤
    (quadrantMidNode M i).num * ((unitNode M i).den : Int)
  unfold unitNode gridNode quadrantMidNode halfCount
  simp only [Q'.mkPos_num, Q'.mkPos_den]
  push_cast
  simp only [Int.one_mul, Int.mul_one, Int.mul_add, Int.add_mul,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hm : (0 : Int) ≤ (M:Int)+1 := by omega
  omega

private theorem quadrantMidNode_le_unitNode_succ (M i : Nat) :
    quadrantMidNode M i ≤ unitNode M (i+1) := by
  show (quadrantMidNode M i).num * ((unitNode M (i+1)).den : Int) ≤
    (unitNode M (i+1)).num * ((quadrantMidNode M i).den : Int)
  unfold unitNode gridNode quadrantMidNode halfCount
  simp only [Q'.mkPos_num, Q'.mkPos_den]
  push_cast
  simp only [Int.one_mul, Int.mul_one, Int.mul_add, Int.add_mul,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hm : (0 : Int) ≤ (M:Int)+1 := by omega
  omega

private theorem unitNode_nonneg (M i : Nat) : (0 : Q') ≤ unitNode M i := by
  unfold unitNode
  exact gridNode_nonneg 1 1 (M+1) i (by decide) (Nat.succ_pos M)

private theorem unitNode_mono_succ (M i : Nat) :
    unitNode M i ≤ unitNode M (i+1) := by
  unfold unitNode
  exact gridNode_mono 1 1 (M+1) i (i+1) (by decide)
    (Nat.succ_pos M) (Nat.le_succ i)

private theorem unitRightTerm_le_midTerm (M i : Nat) :
    LimitLe (unitRightTerm M i) (quadrantMidTerm M i) := by
  have hfun := doubledQuadrantSemi_antitone
    (quadrantMidNode_nonneg M i) (quadrantMidNode_le_unitNode_succ M i)
  have hw : (0 : Q') ≤ unitNode M (i+1) + -unitNode M i :=
    Q'.sub_nonneg_of_le (unitNode_mono_succ M i)
  unfold unitRightTerm quadrantMidTerm cPartitionRect
  exact limitLe_scale _ hw hfun

private theorem midTerm_le_unitLeftTerm (M i : Nat) :
    LimitLe (quadrantMidTerm M i) (unitLeftTerm M i) := by
  have hfun := doubledQuadrantSemi_antitone
    (unitNode_nonneg M i) (unitNode_le_quadrantMidNode M i)
  have hw : (0 : Q') ≤ unitNode M (i+1) + -unitNode M i :=
    Q'.sub_nonneg_of_le (unitNode_mono_succ M i)
  unfold quadrantMidTerm unitLeftTerm cPartitionRect
  exact limitLe_scale _ hw hfun

private theorem unitRightCsum_le_mid (M : Nat) :
    LimitLe (CReal.csum (unitRightTerm M) (halfCount M))
      (quadrantMidSeq M) := by
  unfold quadrantMidSeq
  exact limitLe_csum (halfCount M)
    (fun i _ => unitRightTerm_le_midTerm M i)

private theorem mid_le_unitLeftCsum (M : Nat) :
    LimitLe (quadrantMidSeq M)
      (CReal.csum (unitLeftTerm M) (halfCount M)) := by
  unfold quadrantMidSeq
  exact limitLe_csum (halfCount M)
    (fun i _ => midTerm_le_unitLeftTerm M i)

/-- The honest same-mesh bracket: the even midpoint subsequence lies between
the uniform right and left endpoint sums.  The polygon index is not involved. -/
theorem evenMidSeq_limitBracket (M : Nat) :
    LimitBracket (unitRightSeq M) (evenMidSeq M) (unitLeftSeq M) := by
  constructor
  · have h := unitRightCsum_le_mid M
    have h₁ := equiv_limitLe_left (unitRightSeq_equiv_csum M) h
    exact equiv_limitLe_right
      (CReal.Equiv.symm (evenMidSeq_equiv_quadrantMidSeq M)) h₁
  · have h := mid_le_unitLeftCsum M
    have h₁ := equiv_limitLe_left (evenMidSeq_equiv_quadrantMidSeq M) h
    exact equiv_limitLe_right
      (CReal.Equiv.symm (unitLeftSeq_equiv_csum M)) h₁

end YMGap.Continuum.SemicircleEvenMidpointPairing

#print axioms YMGap.Continuum.SemicircleEvenMidpointPairing.positive_nodeWeight_equiv_quadrant
#print axioms YMGap.Continuum.SemicircleEvenMidpointPairing.reflected_nodeWeight_equiv_positive
#print axioms YMGap.Continuum.SemicircleEvenMidpointPairing.pairedTerm_equiv_quadrantMidTerm
#print axioms YMGap.Continuum.SemicircleEvenMidpointPairing.evenMidSeq_equiv_quadrantMidSeq
#print axioms YMGap.Continuum.SemicircleEvenMidpointPairing.evenMidSeq_limitBracket
