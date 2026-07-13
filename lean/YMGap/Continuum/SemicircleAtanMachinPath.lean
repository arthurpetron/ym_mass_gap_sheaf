/-
# The branch-safe rational Machin path for the semicircle atan integral

This successor to `SemicircleAtanDarboux` supplies the exact finite algebra
behind the value bridge.  Instead of passing through the slope `120/119 > 1`,
it orders the Machin increments as

    (atan(1/5) - atan(1/239)) + atan(1/5) + atan(1/5) + atan(1/5),

whose successive tangent slopes are

    117/598, 1183/2873, 4394/6591, 1.

Every intermediate slope is in `(0,1)`, every tangent-addition denominator is
strictly positive, and every displayed fraction is checked exactly by the
kernel.  The generic cleared Möbius/Jacobian identity

    (1 + T²)(1-rt)² = (1+r²)(1+t²),   T=(r+t)/(1-rt),

is proved over arbitrary `Q'`; this is the pointwise algebra required by a
constructive rational change-of-variables proof.  No angle-addition or value
identity is assumed here.

All declarations are axiom-gated at EOF and depend only on `propext` (and
`Quot.sound` through imported integer arithmetic).  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, or measured constant occurs.
-/

import YMGap.Continuum.SemicircleAtanDarboux

namespace YMGap.Continuum.SemicircleAtanMachinPath

open YMGap.Constructive

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem one_num : (1 : Q').num = 1 := rfl
private theorem one_den : (((1 : Q').den : Int)) = 1 := rfl

local macro "ring_qeqv_test" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, one_num, one_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one, Int.mul_assoc, Int.mul_comm,
               Int.mul_left_comm] <;>
             omega))

theorem mobius_pythagorean (r t : Q') :
    (((1 : Q') + -(r*t))*((1 : Q') + -(r*t)) + (r+t)*(r+t)).eqv
      (((1 : Q')+r*r)*((1 : Q')+t*t)) := by
  ring_qeqv_test

def fifth : Q' := Q'.mkPos 1 5 (by decide)
def twoThirtyNinth : Q' := Q'.mkPos 1 239 (by decide)

/-- `tan(arctan(1/5) - arctan(1/239))`. -/
def slopeOne : Q' := Q'.mkPos 117 598 (by decide)

/-- Add one further `arctan(1/5)`. -/
def slopeTwo : Q' := Q'.mkPos 1183 2873 (by decide)

/-- Add a second further `arctan(1/5)`. -/
def slopeThree : Q' := Q'.mkPos 4394 6591 (by decide)

/-- The final slope after a third further `arctan(1/5)`. -/
def slopeFour : Q' := 1

theorem fifth_pos : (0 : Q') < fifth := by decide
theorem twoThirtyNinth_pos : (0 : Q') < twoThirtyNinth := by decide
theorem slopeOne_pos : (0 : Q') < slopeOne := by decide
theorem slopeTwo_pos : (0 : Q') < slopeTwo := by decide
theorem slopeThree_pos : (0 : Q') < slopeThree := by decide

theorem slopeOne_lt_one : slopeOne < (1 : Q') := by decide
theorem slopeTwo_lt_one : slopeTwo < (1 : Q') := by decide
theorem slopeThree_lt_one : slopeThree < (1 : Q') := by decide

/-- First branch-safe tangent identity:
`atan(1/239) + atan(117/598) = atan(1/5)`. -/
theorem first_path_cleared :
    (fifth * ((1 : Q') + -(twoThirtyNinth * slopeOne))).eqv
      (twoThirtyNinth + slopeOne) := by decide

/-- The first positive denominator in the path. -/
theorem first_path_den_pos :
    (0 : Q') < (1 : Q') + -(twoThirtyNinth * slopeOne) := by decide

/-- Second branch-safe tangent identity. -/
theorem second_path_cleared :
    (slopeTwo * ((1 : Q') + -(slopeOne * fifth))).eqv
      (slopeOne + fifth) := by decide

theorem second_path_den_pos :
    (0 : Q') < (1 : Q') + -(slopeOne * fifth) := by decide

/-- Third branch-safe tangent identity. -/
theorem third_path_cleared :
    (slopeThree * ((1 : Q') + -(slopeTwo * fifth))).eqv
      (slopeTwo + fifth) := by decide

theorem third_path_den_pos :
    (0 : Q') < (1 : Q') + -(slopeTwo * fifth) := by decide

/-- Final branch-safe tangent identity; the resulting slope is exactly one. -/
theorem fourth_path_cleared :
    (slopeFour * ((1 : Q') + -(slopeThree * fifth))).eqv
      (slopeThree + fifth) := by decide

theorem fourth_path_den_pos :
    (0 : Q') < (1 : Q') + -(slopeThree * fifth) := by decide

/-- Rational tangent addition, defined only with a witnessed positive branch
denominator. -/
def tanAdd (r t : Q') (hden : (0 : Q') < (1 : Q') + -(r*t)) : Q' :=
  Q'.divPos (r+t) ((1 : Q') + -(r*t)) hden

theorem tanAdd_mul_den (r t : Q')
    (hden : (0 : Q') < (1 : Q') + -(r*t)) :
    (tanAdd r t hden * ((1 : Q') + -(r*t))).eqv (r+t) :=
  Q'.divPos_mul_eqv _ _ hden

/-- The Möbius Jacobian identity in the exact cleared form consumed by a
rational change-of-variables argument:

`(1 + T²)(1-rt)² = (1+r²)(1+t²)`, where `T=(r+t)/(1-rt)`. -/
theorem tanAdd_kernel_cleared (r t : Q')
    (hden : (0 : Q') < (1 : Q') + -(r*t)) :
    (((1 : Q') + tanAdd r t hden * tanAdd r t hden) *
        (((1 : Q') + -(r*t))*((1 : Q') + -(r*t)))).eqv
      (((1 : Q') + r*r)*((1 : Q') + t*t)) := by
  let D : Q' := (1 : Q') + -(r*t)
  let T : Q' := tanAdd r t hden
  let N : Q' := r+t
  have hTD : (T*D).eqv N := tanAdd_mul_den r t hden
  have hsquare : ((T*D)*(T*D)).eqv (N*N) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (T*D) N (T*D) hTD)
      (Q'.mul_eqv_congr_left N (T*D) N hTD)
  have hexpand : (((1 : Q') + T*T)*(D*D)).eqv
      (D*D+(T*D)*(T*D)) := by
    ring_qeqv_test
  refine Q'.eqv_trans _ _ _ hexpand ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (D*D) _ _ hsquare) ?_
  exact mobius_pythagorean r t

theorem tanAdd_twoThirtyNinth_slopeOne_eqv_fifth :
    (tanAdd twoThirtyNinth slopeOne first_path_den_pos).eqv fifth := by decide

theorem tanAdd_slopeOne_fifth_eqv_slopeTwo :
    (tanAdd slopeOne fifth second_path_den_pos).eqv slopeTwo := by decide

theorem tanAdd_slopeTwo_fifth_eqv_slopeThree :
    (tanAdd slopeTwo fifth third_path_den_pos).eqv slopeThree := by decide

theorem tanAdd_slopeThree_fifth_eqv_one :
    (tanAdd slopeThree fifth fourth_path_den_pos).eqv (1 : Q') := by decide

/-- The complete exact branch certificate, in the order needed by the Machin
change-of-variables proof. -/
theorem machin_path_certificate :
    (0 : Q') < slopeOne ∧ slopeOne < (1 : Q') ∧
    (0 : Q') < slopeTwo ∧ slopeTwo < (1 : Q') ∧
    (0 : Q') < slopeThree ∧ slopeThree < (1 : Q') ∧
    (tanAdd twoThirtyNinth slopeOne first_path_den_pos).eqv fifth ∧
    (tanAdd slopeOne fifth second_path_den_pos).eqv slopeTwo ∧
    (tanAdd slopeTwo fifth third_path_den_pos).eqv slopeThree ∧
    (tanAdd slopeThree fifth fourth_path_den_pos).eqv (1 : Q') :=
  ⟨slopeOne_pos, slopeOne_lt_one,
   slopeTwo_pos, slopeTwo_lt_one,
   slopeThree_pos, slopeThree_lt_one,
   tanAdd_twoThirtyNinth_slopeOne_eqv_fifth,
   tanAdd_slopeOne_fifth_eqv_slopeTwo,
   tanAdd_slopeTwo_fifth_eqv_slopeThree,
   tanAdd_slopeThree_fifth_eqv_one⟩

end YMGap.Continuum.SemicircleAtanMachinPath

#print axioms YMGap.Continuum.SemicircleAtanMachinPath.mobius_pythagorean
#print axioms YMGap.Continuum.SemicircleAtanMachinPath.first_path_cleared
#print axioms YMGap.Continuum.SemicircleAtanMachinPath.second_path_cleared
#print axioms YMGap.Continuum.SemicircleAtanMachinPath.third_path_cleared
#print axioms YMGap.Continuum.SemicircleAtanMachinPath.fourth_path_cleared
#print axioms YMGap.Continuum.SemicircleAtanMachinPath.tanAdd_mul_den
#print axioms YMGap.Continuum.SemicircleAtanMachinPath.tanAdd_kernel_cleared
#print axioms YMGap.Continuum.SemicircleAtanMachinPath.machin_path_certificate
