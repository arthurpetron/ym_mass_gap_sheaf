/-
# Finite Darboux squeeze for the atan Möbius substitution
-/

import YMGap.Continuum.SemicircleAtanInducedPartition

namespace YMGap.Continuum.SemicircleAtanTransformedSqueeze

open YMGap.Constructive
open YMGap.Continuum.SemicircleAtanMobiusKernel
open YMGap.Continuum.SemicircleAtanInducedPartition

def kernelDen (x : Q') : Q' := (1 : Q') + x*x

theorem kernelDen_pos (x : Q') : (0 : Q') < kernelDen x := by
  unfold kernelDen
  exact Q'.pos_add_nonneg (by decide) (SumOfSquares.q_mul_self_nonneg x)

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
  have hdiv : (Q'.divPos p q hq).eqv c := by
    apply Q'.mul_left_cancel_of_pos hq
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q (Q'.divPos p q hq)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv p q hq) ?_
    refine Q'.eqv_trans _ _ _ hcancel ?_
    exact Q'.mul_comm_eqv c q
  exact hdiv

private theorem divPos_le_divPos_of_cross (p q p' q' : Q')
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : p*q' ≤ p'*q) :
    Q'.divPos p q hq ≤ Q'.divPos p' q' hq' := by
  refine Q'.divPos_le_of_le_mul p q hq ?_
  have hr : (0 : Q') ≤ Q'.recipPos q' hq' :=
    Q'.le_of_lt (Q'.recipPos_pos q' hq')
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ _ hcross hr
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
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hR))

private theorem eqv_divPos_of_mul {a num den : Q'} (hden : (0 : Q') < den)
    (h : (a*den).eqv num) :
    a.eqv (Q'.divPos num den hden) := by
  apply Q'.mul_left_cancel_of_pos hden
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv den a) ?_
  refine Q'.eqv_trans _ _ _ h ?_
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv den (Q'.divPos num den hden)) ?_
  exact Q'.divPos_mul_eqv num den hden

private theorem mul_swap_last (a b c : Q') :
    (a*(b*c)).eqv ((a*c)*b) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (a*b) c) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv c a b)) ?_
  exact Q'.mul_eqv_congr_right _ _ b (Q'.mul_comm_eqv c a)

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem one_num : (1 : Q').num = 1 := rfl
private theorem one_den : (((1 : Q').den : Int)) = 1 := rfl
private theorem two_num : (2 : Q').num = 2 := rfl
private theorem two_den : (((2 : Q').den : Int)) = 1 := rfl

private theorem scaledCell_mul_kernelDen_eqv_mesh
    (A B n j : Nat) (hB : 0 < B) (hn : 0 < n) :
    (SemicircleAtanRationalEndpoint.scaledCell A B n j hB hn *
        kernelDen (gridNode A B n j hB hn)).eqv
      (2 * gridMesh A B n hB hn) := by
  show (SemicircleAtanRationalEndpoint.scaledCell A B n j hB hn *
      kernelDen (gridNode A B n j hB hn)).num *
      ((2 * gridMesh A B n hB hn).den : Int) =
    (2 * gridMesh A B n hB hn).num *
      ((SemicircleAtanRationalEndpoint.scaledCell A B n j hB hn *
        kernelDen (gridNode A B n j hB hn)).den : Int)
  unfold SemicircleAtanRationalEndpoint.scaledCell
    SemicircleAtanRationalEndpoint.scaledDen kernelDen gridNode gridMesh rat
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    one_num, one_den, two_num, two_den]
  push_cast
  simp only [Int.mul_one, Int.mul_add, Int.add_mul,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

def sourceLeftRect (x y : Q') : Q' :=
  Q'.divPos (2*(y + -x)) (kernelDen x) (kernelDen_pos x)

def sourceRightRect (x y : Q') : Q' :=
  Q'.divPos (2*(y + -x)) (kernelDen y) (kernelDen_pos y)

def transformedLeftRect (r x y : Q')
    (hx : (0 : Q') < mobiusDen r x) (hy : (0 : Q') < mobiusDen r y) : Q' :=
  Q'.divPos (2*(mobius r y hy + -mobius r x hx))
    (kernelDen (mobius r x hx)) (kernelDen_pos _)

def transformedRightRect (r x y : Q')
    (hx : (0 : Q') < mobiusDen r x) (hy : (0 : Q') < mobiusDen r y) : Q' :=
  Q'.divPos (2*(mobius r y hy + -mobius r x hx))
    (kernelDen (mobius r y hy)) (kernelDen_pos _)

def leftProxy' (r x y : Q')
    (hy : (0 : Q') < mobiusDen r y) : Q' :=
  Q'.divPos ((2*(y + -x))*mobiusDen r x)
    (kernelDen x * mobiusDen r y)
    (Q'.mul_pos (kernelDen_pos x) hy)

def rightProxy (r x y : Q')
    (hx : (0 : Q') < mobiusDen r x) : Q' :=
  Q'.divPos ((2*(y + -x))*mobiusDen r y)
    (kernelDen y * mobiusDen r x)
    (Q'.mul_pos (kernelDen_pos y) hx)

theorem transformedLeft_eqv_proxy (r x y : Q')
    (hx : (0 : Q') < mobiusDen r x) (hy : (0 : Q') < mobiusDen r y) :
    (transformedLeftRect r x y hx hy).eqv (leftProxy' r x y hy) := by
  apply divPos_eqv_divPos_of_cross
  exact mobius_left_rectangle_cleared r x y hx hy

theorem transformedRight_eqv_proxy (r x y : Q')
    (hx : (0 : Q') < mobiusDen r x) (hy : (0 : Q') < mobiusDen r y) :
    (transformedRightRect r x y hx hy).eqv (rightProxy r x y hx) := by
  apply divPos_eqv_divPos_of_cross
  exact mobius_right_rectangle_cleared r x y hx hy

theorem sourceLeft_le_transformedLeft (r x y : Q')
    (hr0 : (0 : Q') ≤ r) (hxy : x ≤ y)
    (hx : (0 : Q') < mobiusDen r x) (hy : (0 : Q') < mobiusDen r y) :
    sourceLeftRect x y ≤ transformedLeftRect r x y hx hy := by
  have hDyDx := mobiusDen_antitone hr0 hxy
  have hdx0 : (0 : Q') ≤ y + -x := Q'.sub_nonneg_of_le hxy
  have hN0 : (0 : Q') ≤ 2*(y + -x) :=
    Q'.mul_nonneg _ _ (by decide) hdx0
  have hND : (2*(y + -x))*mobiusDen r y ≤
      (2*(y + -x))*mobiusDen r x :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hDyDx hN0
  have hK0 : (0 : Q') ≤ kernelDen x := Q'.le_of_lt (kernelDen_pos x)
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ _ hND hK0
  have hcross : (2*(y + -x)) * (kernelDen x * mobiusDen r y) ≤
      ((2*(y + -x))*mobiusDen r x) * kernelDen x := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (mul_swap_last (2*(y + -x)) (kernelDen x) (mobiusDen r y))) hs
  have hp := divPos_le_divPos_of_cross
    (2*(y + -x)) (kernelDen x)
    ((2*(y + -x))*mobiusDen r x) (kernelDen x * mobiusDen r y)
    (kernelDen_pos x) (Q'.mul_pos (kernelDen_pos x) hy) hcross
  exact Q'.le_trans' _ _ _ hp
    (Q'.le_of_eqv (Q'.eqv_symm (transformedLeft_eqv_proxy r x y hx hy)))

theorem transformedRight_le_sourceRight (r x y : Q')
    (hr0 : (0 : Q') ≤ r) (hxy : x ≤ y)
    (hx : (0 : Q') < mobiusDen r x) (hy : (0 : Q') < mobiusDen r y) :
    transformedRightRect r x y hx hy ≤ sourceRightRect x y := by
  have hDyDx := mobiusDen_antitone hr0 hxy
  have hdx0 : (0 : Q') ≤ y + -x := Q'.sub_nonneg_of_le hxy
  have hN0 : (0 : Q') ≤ 2*(y + -x) :=
    Q'.mul_nonneg _ _ (by decide) hdx0
  have hND : (2*(y + -x))*mobiusDen r y ≤
      (2*(y + -x))*mobiusDen r x :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hDyDx hN0
  have hK0 : (0 : Q') ≤ kernelDen y := Q'.le_of_lt (kernelDen_pos y)
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ _ hND hK0
  have hcross : ((2*(y + -x))*mobiusDen r y) * kernelDen y ≤
      (2*(y + -x)) * (kernelDen y * mobiusDen r x) := by
    exact Q'.le_trans' _ _ _ hs
      (Q'.le_of_eqv (Q'.eqv_symm
        (mul_swap_last (2*(y + -x)) (kernelDen y) (mobiusDen r x))))
  have hp := divPos_le_divPos_of_cross
    ((2*(y + -x))*mobiusDen r y) (kernelDen y * mobiusDen r x)
    (2*(y + -x)) (kernelDen y)
    (Q'.mul_pos (kernelDen_pos y) hx) (kernelDen_pos y) hcross
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (transformedRight_eqv_proxy r x y hx hy)) hp

private theorem rat_nonneg (A B : Nat) (hB : 0 < B) :
    (0 : Q') ≤ rat A B hB := by
  rw [Q'.zero_le_iff_num_nonneg]
  unfold rat
  rw [Q'.mkPos_num]
  exact Int.natCast_nonneg _

def sourceLeftGridCell
    (A B n j : Nat) (hB : 0 < B) (hn : 0 < n) : Q' :=
  if j < n then
    sourceLeftRect (gridNode A B n j hB hn) (gridNode A B n (j+1) hB hn)
  else 0

def sourceRightGridCell
    (A B n j : Nat) (hB : 0 < B) (hn : 0 < n) : Q' :=
  if j < n then
    sourceRightRect (gridNode A B n j hB hn) (gridNode A B n (j+1) hB hn)
  else 0

def inducedLeftGridCell
    (R S A B n j : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) : Q' :=
  if hj : j < n then
    transformedLeftRect (rat R S hS)
      (gridNode A B n j hB hn) (gridNode A B n (j+1) hB hn)
      (mobiusDen_grid_pos R S A B n j hS hB hn (Nat.le_of_lt hj) hbranch)
      (mobiusDen_grid_pos R S A B n (j+1) hS hB hn
        (Nat.succ_le_iff.mpr hj) hbranch)
  else 0

def inducedRightGridCell
    (R S A B n j : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) : Q' :=
  if hj : j < n then
    transformedRightRect (rat R S hS)
      (gridNode A B n j hB hn) (gridNode A B n (j+1) hB hn)
      (mobiusDen_grid_pos R S A B n j hS hB hn (Nat.le_of_lt hj) hbranch)
      (mobiusDen_grid_pos R S A B n (j+1) hS hB hn
        (Nat.succ_le_iff.mpr hj) hbranch)
  else 0

def sourceLeftGridSum (A B n : Nat) (hB : 0 < B) (hn : 0 < n) : Q' :=
  RationalTail.finSum (fun j => sourceLeftGridCell A B n j hB hn) n

def sourceRightGridSum (A B n : Nat) (hB : 0 < B) (hn : 0 < n) : Q' :=
  RationalTail.finSum (fun j => sourceRightGridCell A B n j hB hn) n

def inducedLeftGridSum
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) : Q' :=
  RationalTail.finSum
    (fun j => inducedLeftGridCell R S A B n j hS hB hn hbranch) n

def inducedRightGridSum
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) : Q' :=
  RationalTail.finSum
    (fun j => inducedRightGridCell R S A B n j hS hB hn hbranch) n

theorem sourceLeftGridCell_eqv_scaledCell
    (A B n j : Nat) (hB : 0 < B) (hn : 0 < n) (hj : j < n) :
    (sourceLeftGridCell A B n j hB hn).eqv
      (SemicircleAtanRationalEndpoint.scaledCell A B n j hB hn) := by
  unfold sourceLeftGridCell sourceLeftRect
  simp only [if_pos hj]
  let x := gridNode A B n j hB hn
  let y := gridNode A B n (j+1) hB hn
  let c := SemicircleAtanRationalEndpoint.scaledCell A B n j hB hn
  have hc : (c * kernelDen x).eqv (2 * gridMesh A B n hB hn) :=
    scaledCell_mul_kernelDen_eqv_mesh A B n j hB hn
  have hs : (2*(y + -x)).eqv (2 * gridMesh A B n hB hn) :=
    Q'.mul_eqv_congr_left 2 _ _ (gridNode_step_eqv A B n j hB hn)
  exact Q'.eqv_symm
    (eqv_divPos_of_mul (kernelDen_pos x)
      (Q'.eqv_trans _ _ _ hc (Q'.eqv_symm hs)))

theorem sourceRightGridCell_eqv_scaledRightCell
    (A B n j : Nat) (hB : 0 < B) (hn : 0 < n) (hj : j < n) :
    (sourceRightGridCell A B n j hB hn).eqv
      (SemicircleAtanRationalEndpoint.scaledRightCell A B n j hB hn) := by
  unfold sourceRightGridCell sourceRightRect
  simp only [if_pos hj]
  let x := gridNode A B n j hB hn
  let y := gridNode A B n (j+1) hB hn
  let c := SemicircleAtanRationalEndpoint.scaledCell A B n (j+1) hB hn
  have hc : (c * kernelDen y).eqv (2 * gridMesh A B n hB hn) :=
    scaledCell_mul_kernelDen_eqv_mesh A B n (j+1) hB hn
  have hs : (2*(y + -x)).eqv (2 * gridMesh A B n hB hn) :=
    Q'.mul_eqv_congr_left 2 _ _ (gridNode_step_eqv A B n j hB hn)
  exact Q'.eqv_symm
    (eqv_divPos_of_mul (kernelDen_pos y)
      (Q'.eqv_trans _ _ _ hc (Q'.eqv_symm hs)))

theorem sourceLeftGridSum_eqv_scaledLeftSum
    (A B n : Nat) (hB : 0 < B) (hn : 0 < n) :
    (sourceLeftGridSum A B n hB hn).eqv
      (SemicircleAtanRationalEndpoint.scaledLeftSum A B n hB hn) := by
  unfold sourceLeftGridSum SemicircleAtanRationalEndpoint.scaledLeftSum
  exact RationalTail.finSum_eqv_congr_lt _ _ n
    (fun j hj => sourceLeftGridCell_eqv_scaledCell A B n j hB hn hj)

theorem sourceRightGridSum_eqv_scaledRightSum
    (A B n : Nat) (hB : 0 < B) (hn : 0 < n) :
    (sourceRightGridSum A B n hB hn).eqv
      (SemicircleAtanRationalEndpoint.scaledRightSum A B n hB hn) := by
  unfold sourceRightGridSum SemicircleAtanRationalEndpoint.scaledRightSum
  exact RationalTail.finSum_eqv_congr_lt _ _ n
    (fun j hj => sourceRightGridCell_eqv_scaledRightCell A B n j hB hn hj)

theorem sourceLeftGridSum_le_inducedLeftGridSum
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) :
    sourceLeftGridSum A B n hB hn ≤
      inducedLeftGridSum R S A B n hS hB hn hbranch := by
  unfold sourceLeftGridSum inducedLeftGridSum
  apply ExpNeg.finSum_le_finSum_of_termwise
  intro j
  by_cases hj : j < n
  · unfold sourceLeftGridCell inducedLeftGridCell
    simp only [if_pos hj, dif_pos hj]
    exact sourceLeft_le_transformedLeft _ _ _ (rat_nonneg R S hS)
      (gridNode_mono A B n j (j+1) hB hn (Nat.le_succ j)) _ _
  · unfold sourceLeftGridCell inducedLeftGridCell
    simp only [if_neg hj, dif_neg hj]
    exact Q'.le_refl' 0

theorem inducedRightGridSum_le_sourceRightGridSum
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) :
    inducedRightGridSum R S A B n hS hB hn hbranch ≤
      sourceRightGridSum A B n hB hn := by
  unfold inducedRightGridSum sourceRightGridSum
  apply ExpNeg.finSum_le_finSum_of_termwise
  intro j
  by_cases hj : j < n
  · unfold inducedRightGridCell sourceRightGridCell
    simp only [if_pos hj, dif_pos hj]
    exact transformedRight_le_sourceRight _ _ _ (rat_nonneg R S hS)
      (gridNode_mono A B n j (j+1) hB hn (Nat.le_succ j)) _ _
  · unfold inducedRightGridCell sourceRightGridCell
    simp only [if_neg hj, dif_neg hj]
    exact Q'.le_refl' 0

end YMGap.Continuum.SemicircleAtanTransformedSqueeze

#print axioms YMGap.Continuum.SemicircleAtanTransformedSqueeze.transformedLeft_eqv_proxy
#print axioms YMGap.Continuum.SemicircleAtanTransformedSqueeze.transformedRight_eqv_proxy
#print axioms YMGap.Continuum.SemicircleAtanTransformedSqueeze.sourceLeft_le_transformedLeft
#print axioms YMGap.Continuum.SemicircleAtanTransformedSqueeze.transformedRight_le_sourceRight
#print axioms YMGap.Continuum.SemicircleAtanTransformedSqueeze.sourceLeftGridSum_le_inducedLeftGridSum
#print axioms YMGap.Continuum.SemicircleAtanTransformedSqueeze.inducedRightGridSum_le_sourceRightGridSum
#print axioms YMGap.Continuum.SemicircleAtanTransformedSqueeze.sourceLeftGridSum_eqv_scaledLeftSum
#print axioms YMGap.Continuum.SemicircleAtanTransformedSqueeze.sourceRightGridSum_eqv_scaledRightSum
