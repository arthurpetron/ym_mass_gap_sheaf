/-
Six-coordinate projective boundary payment.

The four-coordinate consumer in `BernsteinMonomialReconstruction` is the
right interface when every coefficient from deficit four onward is
nonnegative.  The seven-unit theta gap has exactly two further exceptional
coordinates, at deficits three and four.  This successor supplies the
corresponding six-coordinate split without changing the frozen generic
module.
-/

import YMGap.Continuum.BernsteinMonomialReconstruction

namespace YMGap.Continuum.BernsteinProjectiveBoundarySix

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BernsteinMonomialReconstruction

local infix:50 " ≈ " => Q'.eqv

/-- The first six projective coordinates, in deficit order. -/
def projectiveBoundarySix (D : Nat) (c : Nat → Int) (t : Q') : Q' :=
  finSum (fun r => Q'.ofInt (c (D - r)) * t ^ (D - r)) 6

/-- The projective bulk beginning at deficit six. -/
def projectiveBulkAfterSix (D : Nat) (c : Nat → Int) (t : Q') : Q' :=
  finSum (fun s => Q'.ofInt (c (D - (6 + s))) * t ^ (D - (6 + s)))
    (D + 1 - 6)

/-- Exact six-coordinate/bulk split of a projective deficit polynomial. -/
theorem projectiveDeficitEval_split_six (D : Nat) (c : Nat → Int)
    (t : Q') (hD : 5 ≤ D) :
    projectiveDeficitEval D c t ≈
      projectiveBoundarySix D c t + projectiveBulkAfterSix D c t := by
  unfold projectiveDeficitEval projectiveBoundarySix projectiveBulkAfterSix
  have hlen : D + 1 = 6 + (D + 1 - 6) := by omega
  let f : QSeq := fun r => Q'.ofInt (c (D - r)) * t ^ (D - r)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_of_eq (congrArg (finSum f) hlen))
    (YMGap.Constructive.finSum_split f 6 (D + 1 - 6))

private theorem ofInt_nonnegative {z : Int} (hz : 0 ≤ z) :
    (0 : Q') ≤ Q'.ofInt z := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact hz

private theorem finSum_nonnegative (f : QSeq) : ∀ N,
    (∀ i, i < N → (0 : Q') ≤ f i) → (0 : Q') ≤ finSum f N
  | 0, _ => Q'.le_refl' 0
  | N + 1, h => by
      show (0 : Q') ≤ finSum f N + f N
      exact Q'.zero_le_add _ _
        (finSum_nonnegative f N (fun i hi => h i (by omega)))
        (h N (by omega))

/-- A nonnegative weighted sum of the first six coordinates, together with
coefficientwise nonnegativity from deficit six onward, makes the whole
projective row nonnegative. -/
theorem projectiveDeficitEval_nonnegative_of_boundary_six_bulk
    (D : Nat) (c : Nat → Int) (t : Q')
    (hD : 5 ≤ D) (ht : (0 : Q') ≤ t)
    (hboundary : (0 : Q') ≤ projectiveBoundarySix D c t)
    (hbulk : ∀ r, 6 ≤ r → r ≤ D → (0 : Int) ≤ c (D - r)) :
    (0 : Q') ≤ projectiveDeficitEval D c t := by
  have hbulkSum : (0 : Q') ≤ projectiveBulkAfterSix D c t := by
    unfold projectiveBulkAfterSix
    apply finSum_nonnegative
    intro s hs
    have hr6 : 6 ≤ 6 + s := by omega
    have hrD : 6 + s ≤ D := by omega
    exact Q'.mul_nonneg _ _
      (ofInt_nonnegative (hbulk (6 + s) hr6 hrD))
      (Q'.pow_nonneg t ht (D - (6 + s)))
  exact Q'.le_trans' _ _ _
    (Q'.zero_le_add _ _ hboundary hbulkSum)
    (Q'.ge_of_eqv (projectiveDeficitEval_split_six D c t hD))

#print axioms projectiveBoundarySix
#print axioms projectiveBulkAfterSix
#print axioms projectiveDeficitEval_split_six
#print axioms projectiveDeficitEval_nonnegative_of_boundary_six_bulk

end YMGap.Continuum.BernsteinProjectiveBoundarySix
