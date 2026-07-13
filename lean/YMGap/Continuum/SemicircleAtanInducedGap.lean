/-
# Concrete induced-partition gap for rational atan addition

This specializes the finite Abel engine to the actual Mobius image of the
uniform rational endpoint grid.  It proves that the induced left sum is at
most the induced right sum plus the uniform transformed mesh times the first
kernel value.  The remaining limit step only needs the mesh to tend to zero.
-/

import YMGap.Continuum.SemicircleAtanTransformedGap

namespace YMGap.Continuum.SemicircleAtanInducedGap

open YMGap.Constructive
open YMGap.Continuum.SemicircleAtanMobiusKernel
open YMGap.Continuum.SemicircleAtanInducedPartition
open YMGap.Continuum.SemicircleAtanTransformedSqueeze
open YMGap.Continuum.SemicircleAtanTransformedGap

def inducedNode
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) (j : Nat) : Q' :=
  mobius (rat R S hS)
    (gridNode A B n (min j n) hB hn)
    (mobiusDen_grid_pos R S A B n (min j n) hS hB hn
      (Nat.min_le_right j n) hbranch)

def inducedWidth
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) (j : Nat) : Q' :=
  inducedNode R S A B n hS hB hn hbranch (j+1) +
    -inducedNode R S A B n hS hB hn hbranch j

def kernelValue (x : Q') : Q' :=
  Q'.divPos 2 (kernelDen x) (kernelDen_pos x)

private theorem rat_nonnegative (A B : Nat) (hB : 0 < B) :
    (0 : Q') ≤ rat A B hB := by
  rw [Q'.zero_le_iff_num_nonneg]
  unfold rat
  rw [Q'.mkPos_num]
  exact Int.natCast_nonneg _

private theorem zero_mul_le_of_nonneg {a b : Q'} (hb : (0 : Q') ≤ b) :
    (0 : Q') * a ≤ b := by
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.zero_mul_eqv a)) hb

theorem inducedNode_nonnegative
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) (j : Nat) :
    (0 : Q') ≤ inducedNode R S A B n hS hB hn hbranch j := by
  unfold inducedNode mobius
  apply Q'.le_divPos_of_mul_le
  exact zero_mul_le_of_nonneg
    (Q'.zero_le_add _ _ (rat_nonnegative R S hS)
      (gridNode_nonneg A B n (min j n) hB hn))

theorem inducedNode_mono_step
    (R S A B n j : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) (hj : j < n) :
    inducedNode R S A B n hS hB hn hbranch j ≤
      inducedNode R S A B n hS hB hn hbranch (j+1) := by
  simpa [inducedNode, Nat.min_eq_left (Nat.le_of_lt hj),
    Nat.min_eq_left (Nat.succ_le_iff.mpr hj)] using
    (mobius_grid_mono R S A B n j (j+1) hS hB hn
      (Nat.le_of_lt hj) (Nat.succ_le_iff.mpr hj) (Nat.le_succ j) hbranch)

theorem inducedWidth_le_mesh
    (R S A B n j : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) (hj : j < n) :
    inducedWidth R S A B n hS hB hn hbranch j ≤
      inducedMeshBound R S A B n hS hB hn hbranch := by
  simpa [inducedWidth, inducedNode, Nat.min_eq_left (Nat.le_of_lt hj),
    Nat.min_eq_left (Nat.succ_le_iff.mpr hj)] using
    (induced_cell_width_le R S A B n j hS hB hn hj hbranch)

theorem inducedMeshBound_nonnegative
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) :
    (0 : Q') ≤ inducedMeshBound R S A B n hS hB hn hbranch := by
  unfold inducedMeshBound
  apply Q'.le_divPos_of_mul_le
  have hr0 := rat_nonnegative R S hS
  have hC0 : (0 : Q') ≤ (1 : Q') + rat R S hS * rat R S hS :=
    Q'.zero_le_add _ _ Q'.zero_le_one (Q'.mul_nonneg _ _ hr0 hr0)
  have hm0 : (0 : Q') ≤ gridMesh A B n hB hn := by
    unfold gridMesh rat
    rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]
    exact Int.natCast_nonneg _
  exact zero_mul_le_of_nonneg (Q'.mul_nonneg _ _ hC0 hm0)

theorem kernelValue_positive (x : Q') : (0 : Q') < kernelValue x := by
  unfold kernelValue
  exact Q'.divPos_pos 2 (kernelDen x) (kernelDen_pos x) (by decide)

theorem kernelValue_le_two (x : Q') : kernelValue x ≤ (2 : Q') := by
  have hden : (1 : Q') ≤ kernelDen x := by
    unfold kernelDen
    exact Q'.add_le_self_of_nonneg _ _ (SumOfSquares.q_mul_self_nonneg x)
  unfold kernelValue
  apply Q'.divPos_le_of_le_mul
  have hm := Q'.mul_le_mul_of_nonneg_left (1 : Q') (kernelDen x) 2 hden
    (by decide : (0 : Q') ≤ 2)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv 2)) hm

theorem kernelValue_antitone {x y : Q'}
    (hx0 : (0 : Q') ≤ x) (hxy : x ≤ y) :
    kernelValue y ≤ kernelValue x := by
  have hy0 : (0 : Q') ≤ y := Q'.le_trans' _ _ _ hx0 hxy
  have hxx : x*x ≤ x*y :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hxy hx0
  have hxyy : x*y ≤ y*y :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hxy hy0
  have hden : kernelDen x ≤ kernelDen y := by
    unfold kernelDen
    exact Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _ hxx hxyy)
  unfold kernelValue
  apply Q'.divPos_le_of_le_mul
  have hq0 : (0 : Q') ≤ Q'.divPos 2 (kernelDen x) (kernelDen_pos x) :=
    Q'.le_of_lt (Q'.divPos_pos 2 _ (kernelDen_pos x) (by decide))
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ _ hden hq0
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.divPos_mul_eqv 2 (kernelDen x) (kernelDen_pos x))) hm

private theorem transformedLeft_factor (r x y : Q')
    (hx : (0 : Q') < mobiusDen r x) (hy : (0 : Q') < mobiusDen r y) :
    (transformedLeftRect r x y hx hy).eqv
      ((mobius r y hy + -mobius r x hx) * kernelValue (mobius r x hx)) := by
  unfold transformedLeftRect kernelValue Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv 2 (mobius r y hy + -mobius r x hx))) ?_
  exact Q'.mul_assoc_eqv (mobius r y hy + -mobius r x hx) 2 _

private theorem transformedRight_factor (r x y : Q')
    (hx : (0 : Q') < mobiusDen r x) (hy : (0 : Q') < mobiusDen r y) :
    (transformedRightRect r x y hx hy).eqv
      ((mobius r y hy + -mobius r x hx) * kernelValue (mobius r y hy)) := by
  unfold transformedRightRect kernelValue Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv 2 (mobius r y hy + -mobius r x hx))) ?_
  exact Q'.mul_assoc_eqv (mobius r y hy + -mobius r x hx) 2 _

theorem inducedLeftGridSum_factor
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) :
    (inducedLeftGridSum R S A B n hS hB hn hbranch).eqv
      (RationalTail.finSum
        (fun j => inducedWidth R S A B n hS hB hn hbranch j *
          kernelValue (inducedNode R S A B n hS hB hn hbranch j)) n) := by
  unfold inducedLeftGridSum
  apply RationalTail.finSum_eqv_congr_lt
  intro j hj
  unfold inducedLeftGridCell
  simp only [dif_pos hj]
  simpa [inducedWidth, inducedNode, Nat.min_eq_left (Nat.le_of_lt hj),
    Nat.min_eq_left (Nat.succ_le_iff.mpr hj)] using
    (transformedLeft_factor (rat R S hS)
      (gridNode A B n j hB hn) (gridNode A B n (j+1) hB hn)
      (mobiusDen_grid_pos R S A B n j hS hB hn (Nat.le_of_lt hj) hbranch)
      (mobiusDen_grid_pos R S A B n (j+1) hS hB hn
        (Nat.succ_le_iff.mpr hj) hbranch))

theorem inducedRightGridSum_factor
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) :
    (inducedRightGridSum R S A B n hS hB hn hbranch).eqv
      (RationalTail.finSum
        (fun j => inducedWidth R S A B n hS hB hn hbranch j *
          kernelValue (inducedNode R S A B n hS hB hn hbranch (j+1))) n) := by
  unfold inducedRightGridSum
  apply RationalTail.finSum_eqv_congr_lt
  intro j hj
  unfold inducedRightGridCell
  simp only [dif_pos hj]
  simpa [inducedWidth, inducedNode, Nat.min_eq_left (Nat.le_of_lt hj),
    Nat.min_eq_left (Nat.succ_le_iff.mpr hj)] using
    (transformedRight_factor (rat R S hS)
      (gridNode A B n j hB hn) (gridNode A B n (j+1) hB hn)
      (mobiusDen_grid_pos R S A B n j hS hB hn (Nat.le_of_lt hj) hbranch)
      (mobiusDen_grid_pos R S A B n (j+1) hS hB hn
        (Nat.succ_le_iff.mpr hj) hbranch))

/-- Concrete induced-partition Darboux gap. -/
theorem inducedLeft_le_right_add_mesh_first
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) :
    inducedLeftGridSum R S A B n hS hB hn hbranch ≤
      inducedRightGridSum R S A B n hS hB hn hbranch +
        inducedMeshBound R S A B n hS hB hn hbranch *
          kernelValue (inducedNode R S A B n hS hB hn hbranch 0) := by
  let w := inducedWidth R S A B n hS hB hn hbranch
  let f := fun j => kernelValue (inducedNode R S A B n hS hB hn hbranch j)
  let h := inducedMeshBound R S A B n hS hB hn hbranch
  have hg := weighted_antitone_gap w f h n
    (inducedMeshBound_nonnegative R S A B n hS hB hn hbranch)
    (fun j hj => inducedWidth_le_mesh R S A B n j hS hB hn hbranch hj)
    (fun j hj => kernelValue_antitone
      (inducedNode_nonnegative R S A B n hS hB hn hbranch j)
      (inducedNode_mono_step R S A B n j hS hB hn hbranch hj))
    (Q'.le_of_lt (kernelValue_positive _))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (inducedLeftGridSum_factor R S A B n hS hB hn hbranch))
    (Q'.le_trans' _ _ _ hg
      (Q'.le_of_eqv
        (Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_symm
            (inducedRightGridSum_factor R S A B n hS hB hn hbranch)))))

/-- Uniform quantitative gap in the form consumed by the convergence step. -/
theorem inducedLeft_le_right_add_two_mesh
    (R S A B n : Nat) (hS : 0 < S) (hB : 0 < B) (hn : 0 < n)
    (hbranch : R*A < S*B) :
    inducedLeftGridSum R S A B n hS hB hn hbranch ≤
      inducedRightGridSum R S A B n hS hB hn hbranch +
        inducedMeshBound R S A B n hS hB hn hbranch * 2 := by
  have hbase := inducedLeft_le_right_add_mesh_first
    R S A B n hS hB hn hbranch
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _
    (inducedMeshBound R S A B n hS hB hn hbranch)
    (kernelValue_le_two (inducedNode R S A B n hS hB hn hbranch 0))
    (inducedMeshBound_nonnegative R S A B n hS hB hn hbranch)
  exact Q'.le_trans' _ _ _ hbase (Q'.add_le_add_left _ _ _ hmul)

end YMGap.Continuum.SemicircleAtanInducedGap

#print axioms YMGap.Continuum.SemicircleAtanInducedGap.inducedNode_nonnegative
#print axioms YMGap.Continuum.SemicircleAtanInducedGap.inducedWidth_le_mesh
#print axioms YMGap.Continuum.SemicircleAtanInducedGap.kernelValue_antitone
#print axioms YMGap.Continuum.SemicircleAtanInducedGap.kernelValue_le_two
#print axioms YMGap.Continuum.SemicircleAtanInducedGap.inducedLeftGridSum_factor
#print axioms YMGap.Continuum.SemicircleAtanInducedGap.inducedRightGridSum_factor
#print axioms YMGap.Continuum.SemicircleAtanInducedGap.inducedLeft_le_right_add_mesh_first
#print axioms YMGap.Continuum.SemicircleAtanInducedGap.inducedLeft_le_right_add_two_mesh
