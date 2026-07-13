/-
# Induced rational partitions for the atan Möbius substitution
-/

import YMGap.Continuum.SemicircleAtanMobiusKernel

namespace YMGap.Continuum.SemicircleAtanInducedPartition

open YMGap.Constructive
open YMGap.Continuum.SemicircleAtanMobiusKernel

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem one_num : (1 : Q').num = 1 := rfl
private theorem one_den : (((1 : Q').den : Int)) = 1 := rfl

private theorem divPos_le_divPos_of_cross (p q p' q' : Q')
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : p * q' ≤ p' * q) :
    Q'.divPos p q hq ≤ Q'.divPos p' q' hq' := by
  refine Q'.divPos_le_of_le_mul p q hq ?_
  have hr : (0 : Q') ≤ Q'.recipPos q' hq' :=
    Q'.le_of_lt (Q'.recipPos_pos q' hq')
  have hstep : (p*q') * Q'.recipPos q' hq' ≤
      (p'*q) * Q'.recipPos q' hq' :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcross hr
  have hL : ((p*q') * Q'.recipPos q' hq').eqv p := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv p q' (Q'.recipPos q' hq')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left p _ _ (Q'.mul_recipPos_eqv q' hq')) ?_
    exact Q'.mul_one_eqv p
  have hR : ((p'*q) * Q'.recipPos q' hq').eqv
      (Q'.divPos p' q' hq' * q) := by
    show ((p'*q) * Q'.recipPos q' hq').eqv
      ((p' * Q'.recipPos q' hq') * q)
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv p' q (Q'.recipPos q' hq')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left p' _ _
        (Q'.mul_comm_eqv q (Q'.recipPos q' hq'))) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv p' (Q'.recipPos q' hq') q)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
    (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hR))

def rat (A B : Nat) (hB : 0 < B) : Q' :=
  Q'.mkPos (A : Int) B hB

def gridNode (A B n j : Nat) (hB : 0 < B) (hn : 0 < n) : Q' :=
  Q'.mkPos ((A*j : Nat) : Int) (B*n) (Nat.mul_pos hB hn)

def gridMesh (A B n : Nat) (hB : 0 < B) (hn : 0 < n) : Q' :=
  rat A (B*n) (Nat.mul_pos hB hn)

theorem gridNode_nonneg (A B n j : Nat) (hB : 0 < B) (hn : 0 < n) :
    (0 : Q') ≤ gridNode A B n j hB hn := by
  rw [Q'.zero_le_iff_num_nonneg]
  unfold gridNode
  rw [Q'.mkPos_num]
  exact Int.natCast_nonneg _

theorem gridNode_mono (A B n j k : Nat) (hB : 0 < B) (hn : 0 < n)
    (hjk : j ≤ k) :
    gridNode A B n j hB hn ≤ gridNode A B n k hB hn := by
  show (gridNode A B n j hB hn).num *
      ((gridNode A B n k hB hn).den : Int) ≤
    (gridNode A B n k hB hn).num *
      ((gridNode A B n j hB hn).den : Int)
  unfold gridNode
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  have hnat : A*j * (B*n) ≤ A*k * (B*n) :=
    Nat.mul_le_mul_right (B*n) (Nat.mul_le_mul_left A hjk)
  exact_mod_cast hnat

theorem gridNode_endpoint_eqv (A B n : Nat) (hB : 0 < B) (hn : 0 < n) :
    (gridNode A B n n hB hn).eqv (rat A B hB) := by
  show (gridNode A B n n hB hn).num * ((rat A B hB).den : Int) =
    (rat A B hB).num * ((gridNode A B n n hB hn).den : Int)
  unfold gridNode rat
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  push_cast
  ac_rfl

theorem gridNode_step_eqv (A B n j : Nat) (hB : 0 < B) (hn : 0 < n) :
    (gridNode A B n (j+1) hB hn + -gridNode A B n j hB hn).eqv
      (gridMesh A B n hB hn) := by
  show (gridNode A B n (j+1) hB hn + -gridNode A B n j hB hn).num *
      ((gridMesh A B n hB hn).den : Int) =
    (gridMesh A B n hB hn).num *
      ((gridNode A B n (j+1) hB hn + -gridNode A B n j hB hn).den : Int)
  unfold gridNode gridMesh rat
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.neg_den, neg_num_cast,
    Q'.mkPos_num, Q'.mkPos_den]
  push_cast
  simp only [Int.mul_add, Int.add_mul, Int.mul_one, Int.neg_mul,
    Int.mul_assoc]
  omega

theorem branch_grid_nat
    (R S A B n j : Nat) (hn : 0 < n) (hj : j ≤ n)
    (hbranch : R*A < S*B) :
    R*A*j < S*B*n := by
  have h1 : R*A*j ≤ R*A*n := Nat.mul_le_mul_left (R*A) hj
  have h2 : R*A*n < S*B*n := by
    exact Nat.mul_lt_mul_of_pos_right hbranch hn
  exact Nat.lt_of_le_of_lt h1 h2

theorem mobiusDen_grid_pos
    (R S A B n j : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hj : j ≤ n) (hbranch : R*A < S*B) :
    (0 : Q') < mobiusDen (rat R S hS) (gridNode A B n j hB hn) := by
  show (0 : Int) *
      ((mobiusDen (rat R S hS) (gridNode A B n j hB hn)).den : Int) <
    (mobiusDen (rat R S hS) (gridNode A B n j hB hn)).num * (1 : Int)
  unfold mobiusDen rat gridNode
  simp only [Q'.add_num_cast, Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.neg_den, neg_num_cast, one_num, one_den,
    Q'.mkPos_num, Q'.mkPos_den]
  simp only [Int.zero_mul, Int.mul_one, Int.one_mul]
  have hnat := branch_grid_nat R S A B n j hn hj hbranch
  have hi : ((R*(A*j) : Nat) : Int) < ((S*(B*n) : Nat) : Int) := by
    exact_mod_cast (by simpa only [Nat.mul_assoc] using hnat)
  omega

private def crossMonoL : RingNormaliser.PolyExpr :=
  .add
    (.mul (.add (.var 0) (.var 1))
      (.add (.const 1) (.neg (.mul (.var 0) (.var 2)))))
    (.mul (.add (.const 1) (.mul (.var 0) (.var 0)))
      (.add (.var 2) (.neg (.var 1))))

private def crossMonoR : RingNormaliser.PolyExpr :=
  .mul (.add (.var 0) (.var 2))
    (.add (.const 1) (.neg (.mul (.var 0) (.var 1))))

private theorem crossMono_normal :
    RingNormaliser.normalize crossMonoL =
      RingNormaliser.normalize crossMonoR := by decide

private theorem mobius_cross_plus_gap (r x y : Q') :
    (((r+x) * mobiusDen r y) +
      (((1 : Q') + r*r) * (y + -x))).eqv
        ((r+y) * mobiusDen r x) := by
  unfold mobiusDen
  have h := RingNormaliser.poly_identity_of_normal_eq
    crossMonoL crossMonoR crossMono_normal
    (fun
      | 0 => r
      | 1 => x
      | _ => y)
  simpa [crossMonoL, crossMonoR, RingNormaliser.eval] using h

theorem mobiusDen_antitone {r x y : Q'} (hr0 : (0 : Q') ≤ r) (hxy : x ≤ y) :
    mobiusDen r y ≤ mobiusDen r x := by
  unfold mobiusDen
  have hm : r*x ≤ r*y := Q'.mul_le_mul_of_nonneg_left _ _ _ hxy hr0
  exact Q'.add_le_add_left _ _ _ (Q'.neg_le_neg hm)

theorem mobius_grid_mono
    (R S A B n j k : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hj : j ≤ n) (hk : k ≤ n) (hjk : j ≤ k)
    (hbranch : R*A < S*B) :
    mobius (rat R S hS) (gridNode A B n j hB hn)
        (mobiusDen_grid_pos R S A B n j hS hB hn hj hbranch) ≤
      mobius (rat R S hS) (gridNode A B n k hB hn)
        (mobiusDen_grid_pos R S A B n k hS hB hn hk hbranch) := by
  let r := rat R S hS
  let x := gridNode A B n j hB hn
  let y := gridNode A B n k hB hn
  let dx := mobiusDen_grid_pos R S A B n j hS hB hn hj hbranch
  let dy := mobiusDen_grid_pos R S A B n k hS hB hn hk hbranch
  have hxy : x ≤ y := gridNode_mono A B n j k hB hn hjk
  have hr0 : (0 : Q') ≤ r := by
    rw [Q'.zero_le_iff_num_nonneg]
    unfold r rat
    rw [Q'.mkPos_num]
    exact Int.natCast_nonneg _
  have hrr0 : (0 : Q') ≤ r*r := Q'.mul_nonneg _ _ hr0 hr0
  have hc0 : (0 : Q') ≤ (1 : Q') + r*r :=
    Q'.zero_le_add _ _ Q'.zero_le_one hrr0
  have hgap0 : (0 : Q') ≤ ((1 : Q') + r*r) * (y + -x) :=
    Q'.mul_nonneg _ _ hc0 (Q'.sub_nonneg_of_le hxy)
  have hfront : (r+x) * mobiusDen r y ≤
      (r+x) * mobiusDen r y + (((1 : Q') + r*r) * (y + -x)) :=
    Q'.add_le_self_of_nonneg _ _ hgap0
  have hcross : (r+x) * mobiusDen r y ≤ (r+y) * mobiusDen r x :=
    Q'.le_trans' _ _ _ hfront (Q'.le_of_eqv (mobius_cross_plus_gap r x y))
  exact divPos_le_divPos_of_cross
    (r+x) (mobiusDen r x) (r+y) (mobiusDen r y) dx dy hcross

def gridReserve (R S A B n : Nat)
    (hS : 0 < S) (hB : 0 < B) (hn : 0 < n) : Q' :=
  mobiusDen (rat R S hS) (gridNode A B n n hB hn)

theorem gridReserve_pos
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) :
    (0 : Q') < gridReserve R S A B n hS hB hn := by
  exact mobiusDen_grid_pos R S A B n n hS hB hn (Nat.le_refl n) hbranch

theorem gridReserve_le_den
    (R S A B n j : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hj : j ≤ n) :
    gridReserve R S A B n hS hB hn ≤
      mobiusDen (rat R S hS) (gridNode A B n j hB hn) := by
  unfold gridReserve
  have hr0 : (0 : Q') ≤ rat R S hS := by
    rw [Q'.zero_le_iff_num_nonneg]
    unfold rat
    rw [Q'.mkPos_num]
    exact Int.natCast_nonneg _
  exact mobiusDen_antitone hr0 (gridNode_mono A B n j n hB hn hj)

private theorem eqv_divPos_of_mul {a num den : Q'} (hden : (0 : Q') < den)
    (h : (a*den).eqv num) :
    a.eqv (Q'.divPos num den hden) := by
  apply Q'.mul_left_cancel_of_pos hden
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv den a) ?_
  refine Q'.eqv_trans _ _ _ h ?_
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv den (Q'.divPos num den hden)) ?_
  exact Q'.divPos_mul_eqv num den hden

def inducedMeshBound
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) : Q' :=
  let r := rat R S hS
  let mesh := gridMesh A B n hB hn
  let reserve := gridReserve R S A B n hS hB hn
  Q'.divPos (((1 : Q') + r*r) * mesh) (reserve*reserve)
    (Q'.mul_pos (gridReserve_pos R S A B n hS hB hn hbranch)
      (gridReserve_pos R S A B n hS hB hn hbranch))

/-- Every cell of the induced Möbius partition has width bounded uniformly by
`(1+r²)·mesh/reserve²`. -/
theorem induced_cell_width_le
    (R S A B n j : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hj : j < n) (hbranch : R*A < S*B) :
    mobius (rat R S hS) (gridNode A B n (j+1) hB hn)
        (mobiusDen_grid_pos R S A B n (j+1) hS hB hn
          (Nat.succ_le_iff.mpr hj) hbranch) +
      -mobius (rat R S hS) (gridNode A B n j hB hn)
        (mobiusDen_grid_pos R S A B n j hS hB hn
          (Nat.le_of_lt hj) hbranch) ≤
      inducedMeshBound R S A B n hS hB hn hbranch := by
  let r := rat R S hS
  let x := gridNode A B n j hB hn
  let y := gridNode A B n (j+1) hB hn
  let hx := mobiusDen_grid_pos R S A B n j hS hB hn (Nat.le_of_lt hj) hbranch
  let hy := mobiusDen_grid_pos R S A B n (j+1) hS hB hn
    (Nat.succ_le_iff.mpr hj) hbranch
  let reserve := gridReserve R S A B n hS hB hn
  let hreserve := gridReserve_pos R S A B n hS hB hn hbranch
  let mesh := gridMesh A B n hB hn
  let C := (1 : Q') + r*r
  let du := mobius r y hy + -mobius r x hx
  have hdiff := mobius_diff_cleared r x y hx hy
  have hstep : (y + -x).eqv mesh := gridNode_step_eqv A B n j hB hn
  have hnum : (C * (y + -x)).eqv (C*mesh) :=
    Q'.mul_eqv_congr_left C _ _ hstep
  have hmul : (du * (mobiusDen r x * mobiusDen r y)).eqv (C*mesh) :=
    Q'.eqv_trans _ _ _ hdiff hnum
  have hdenxy : (0 : Q') < mobiusDen r x * mobiusDen r y := Q'.mul_pos hx hy
  have heq : du.eqv (Q'.divPos (C*mesh)
      (mobiusDen r x * mobiusDen r y) hdenxy) :=
    eqv_divPos_of_mul hdenxy hmul
  have hr0 : (0 : Q') ≤ r := by
    rw [Q'.zero_le_iff_num_nonneg]
    unfold r rat
    rw [Q'.mkPos_num]
    exact Int.natCast_nonneg _
  have hC0 : (0 : Q') ≤ C := by
    exact Q'.zero_le_add _ _ Q'.zero_le_one (Q'.mul_nonneg _ _ hr0 hr0)
  have hmesh0 : (0 : Q') ≤ mesh := by
    unfold mesh gridMesh rat
    rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]
    exact Int.natCast_nonneg _
  have hN0 : (0 : Q') ≤ C*mesh := Q'.mul_nonneg _ _ hC0 hmesh0
  have hRx := gridReserve_le_den R S A B n j hS hB hn (Nat.le_of_lt hj)
  have hRy := gridReserve_le_den R S A B n (j+1) hS hB hn
    (Nat.succ_le_iff.mpr hj)
  have hR0 : (0 : Q') ≤ reserve := Q'.le_of_lt hreserve
  have hDx0 : (0 : Q') ≤ mobiusDen r x := Q'.le_of_lt hx
  have hdenle : reserve*reserve ≤ mobiusDen r x * mobiusDen r y := by
    have h1 := Q'.mul_le_mul_of_nonneg_right reserve (mobiusDen r x)
      reserve hRx hR0
    have h2 := Q'.mul_le_mul_of_nonneg_left reserve (mobiusDen r y)
      (mobiusDen r x) hRy hDx0
    exact Q'.le_trans' _ _ _ h1 h2
  have hcross : (C*mesh) * (reserve*reserve) ≤
      (C*mesh) * (mobiusDen r x * mobiusDen r y) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdenle hN0
  have hq := divPos_le_divPos_of_cross
    (C*mesh) (mobiusDen r x * mobiusDen r y)
    (C*mesh) (reserve*reserve) hdenxy (Q'.mul_pos hreserve hreserve) hcross
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) hq

end YMGap.Continuum.SemicircleAtanInducedPartition

#print axioms YMGap.Continuum.SemicircleAtanInducedPartition.gridNode_mono
#print axioms YMGap.Continuum.SemicircleAtanInducedPartition.mobiusDen_grid_pos
#print axioms YMGap.Continuum.SemicircleAtanInducedPartition.mobius_grid_mono
#print axioms YMGap.Continuum.SemicircleAtanInducedPartition.gridNode_step_eqv
#print axioms YMGap.Continuum.SemicircleAtanInducedPartition.gridReserve_le_den
#print axioms YMGap.Continuum.SemicircleAtanInducedPartition.induced_cell_width_le
