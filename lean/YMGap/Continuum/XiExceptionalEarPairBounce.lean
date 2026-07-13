/-
# Pair-bounce square encoding for open ears

An exceptional disagreement path has odd edge length, hence its interior
vertices occur in adjacent pairs.  `PairedPath` records that parity invariant.
The bounce walk traverses every interior pair forward, backward, and forward;
therefore each interior activity occurs exactly twice while the endpoints
occur once.  Two alternative ears are then dominated by the sum of their
bounce weights via `A*B <= A^2+B^2`.
-/

import YMGap.Continuum.XiExceptionalEarHamiltonianFence

namespace YMGap.Continuum.XiExceptionalEarPairBounce

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalPathExtraction

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-- An odd-length path, exposed as adjacent two-edge chunks followed by one
last edge. -/
inductive PairedPath {alpha : Type} (edge : alpha → alpha → Bool) :
    alpha → alpha → Type
  | last {x y : alpha} : edge x y = true → PairedPath edge x y
  | pair {x y z t : alpha} : edge x y = true → edge y z = true →
      PairedPath edge z t → PairedPath edge x t

namespace PairedPath

variable {alpha : Type} {edge : alpha → alpha → Bool}

def toWalk : {x y : alpha} → PairedPath edge x y → CWalk edge x y
  | _, _, .last h => .cons h (.single _)
  | _, _, .pair hxy hyz rest => .cons hxy (.cons hyz rest.toWalk)

/-- Repeat each adjacent interior pair without changing the endpoints. -/
def bounceWalk (hsymm : ∀ x y, edge x y = true → edge y x = true) :
    {x y : alpha} → PairedPath edge x y → CWalk edge x y
  | _, _, .last h => .cons h (.single _)
  | _, _, .pair hxy hyz rest =>
      .cons hxy (.cons hyz (.cons (hsymm _ _ hyz)
        (.cons hyz (bounceWalk hsymm rest))))

def pairCount : {x y : alpha} → PairedPath edge x y → Nat
  | _, _, .last _ => 0
  | _, _, .pair _ _ rest => pairCount rest + 1

theorem toWalk_length : ∀ {x y : alpha} (path : PairedPath edge x y),
    path.toWalk.vertices.length = 2 + 2 * path.pairCount
  | _, _, .last _ => rfl
  | _, _, .pair _ _ rest => by
      simp only [toWalk, CWalk.vertices, pairCount, List.length_cons]
      rw [toWalk_length rest]
      omega

theorem bounceWalk_length
    (hsymm : ∀ x y, edge x y = true → edge y x = true) :
    ∀ {x y : alpha} (path : PairedPath edge x y),
      (path.bounceWalk hsymm).vertices.length = 2 + 4 * path.pairCount
  | _, _, .last _ => rfl
  | _, _, .pair _ _ rest => by
      simp only [bounceWalk, CWalk.vertices, pairCount, List.length_cons]
      rw [bounceWalk_length hsymm rest]
      omega

variable {L : Lattice} [DecidableEq L.Plaquette]

def interiorActivity (w : Q') (label : L.Plaquette → Rep) :
    {X Y : Polymer L} →
      PairedPath (fun A B : Polymer L => !(compatibleB A B)) X Y → Q'
  | _, _, .last _ => 1
  | _, _, @PairedPath.pair _ _ X A B Y _ _ rest =>
      activity w A label * activity w B label *
        interiorActivity w label rest

theorem interiorActivity_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (label : L.Plaquette → Rep) :
    ∀ {X Y : Polymer L}
      (path : PairedPath (fun A B : Polymer L => !(compatibleB A B)) X Y),
      (0 : Q') ≤ path.interiorActivity w label
  | _, _, .last _ => Q'.zero_le_one
  | _, _, @PairedPath.pair _ _ X A B Y _ _ rest =>
      Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (activity_nonneg hw A label)
          (activity_nonneg hw B label))
        (interiorActivity_nonnegative hw label rest)

private theorem incompat_symm (X Y : Polymer L)
    (h : (!(compatibleB X Y)) = true) : (!(compatibleB Y X)) = true := by
  rw [compatibleB_symm Y X]
  exact h

/-- Exact square identity for the pair-bounced ear. -/
theorem bounceWalk_activity_eqv :
    ∀ {X Y : Polymer L}
      (path : PairedPath (fun A B : Polymer L => !(compatibleB A B)) X Y)
      (w : Q') (label : L.Plaquette → Rep),
      (path.bounceWalk incompat_symm).activityWeight w label ≈
        activity w X label *
          (path.interiorActivity w label * path.interiorActivity w label *
            activity w Y label)
  | _, _, .last _, w, label => by
      simp only [bounceWalk, CWalk.activityWeight, interiorActivity]
      ring_qeqv
  | _, _, @PairedPath.pair _ _ X A B Y hXA hAB rest, w, label => by
      simp only [bounceWalk, CWalk.activityWeight, interiorActivity]
      refine Q'.eqv_trans _
        (activity w X label * (activity w A label *
          (activity w B label * (activity w A label *
            (activity w B label *
              (rest.interiorActivity w label *
                rest.interiorActivity w label * activity w Y label)))))) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left (activity w X label) _ _
          (Q'.mul_eqv_congr_left (activity w A label) _ _
              (Q'.mul_eqv_congr_left (activity w B label) _ _
                (Q'.mul_eqv_congr_left (activity w A label) _ _
                  (bounceWalk_activity_eqv rest w label))))
      · ring_qeqv

/-- Two paired open ears with common endpoints have the exact two-code
square domination, before occurrence-code packaging. -/
theorem paired_two_arm_weight_bound {w : Q'} (hw : (0 : Q') ≤ w)
    {X Y : Polymer L}
    (left right :
      PairedPath (fun A B : Polymer L => !(compatibleB A B)) X Y)
    (label : L.Plaquette → Rep) :
    (activity w X label * activity w Y label) *
        (left.interiorActivity w label *
          right.interiorActivity w label) ≤
      (left.bounceWalk incompat_symm).activityWeight w label +
        (right.bounceWalk incompat_symm).activityWeight w label := by
  let C := activity w X label * activity w Y label
  let A := left.interiorActivity w label
  let B := right.interiorActivity w label
  have hA : (0 : Q') ≤ A := interiorActivity_nonnegative hw label left
  have hB : (0 : Q') ≤ B := interiorActivity_nonnegative hw label right
  have hC : (0 : Q') ≤ C := Q'.mul_nonneg _ _
    (activity_nonneg hw X label) (activity_nonneg hw Y label)
  have hab :=
    XiExceptionalMixedEarAbsorption.prod_le_square_sum hA hB
  have hscaled : C * (A * B) ≤ C * (A * A + B * B) :=
    Q'.mul_le_mul_of_nonneg_left (A * B) (A * A + B * B) C hab hC
  have htargets :
      (left.bounceWalk incompat_symm).activityWeight w label +
          (right.bounceWalk incompat_symm).activityWeight w label ≈
        C * (A * A + B * B) := by
    refine Q'.eqv_trans _
      (activity w X label *
          (left.interiorActivity w label * left.interiorActivity w label *
            activity w Y label) +
        activity w X label *
          (right.interiorActivity w label * right.interiorActivity w label *
            activity w Y label)) _ ?_ ?_
    · exact add_eqv_congr_both _ _ _ _
        (bounceWalk_activity_eqv left w label)
        (bounceWalk_activity_eqv right w label)
    · unfold C A B
      ring_qeqv
  exact Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv htargets)

#print axioms toWalk_length
#print axioms bounceWalk_length
#print axioms bounceWalk_activity_eqv
#print axioms interiorActivity_nonnegative
#print axioms paired_two_arm_weight_bound

end PairedPath

end YMGap.Continuum.XiExceptionalEarPairBounce
