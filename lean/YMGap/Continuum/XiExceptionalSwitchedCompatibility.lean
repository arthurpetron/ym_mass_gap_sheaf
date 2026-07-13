/-
# Same-side compatibility after the occurrence switch

The reached-component switch preserves internal compatibility occurrence by
occurrence.  If two switched-left (respectively switched-right) bits are set,
their polymers cannot conflict.  In the mixed-cut case, a conflict would be
an alternating disagreement edge crossing the reached component boundary,
contradicting component closure.

This is the missing structural input for branch-sensitive routing: once the
carrier path is decoded, a path-incompatible residual occurrence cannot be
occupied on both switched sides.
-/

import YMGap.Continuum.XiExceptionalUnsafeRightCapacityFence

namespace YMGap.Continuum.XiExceptionalSwitchedCompatibility

open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery

private theorem false_of_true_eq_false {b : Bool}
    (hb : b = true) (hf : b = false) : False := by
  rw [hb] at hf
  cases hf

theorem switchedLeft_sameSide_guard
    (N : Nat) (inc : Nat → Nat → Bool)
    (left right bad : Nat → Bool)
    (hleft : ∀ i j, left i = true → left j = true →
      symConflict inc i j = false)
    (hright : ∀ i j, right i = true → right j = true →
      symConflict inc i j = false)
    (i j : Nat) (hi : i < N) (hj : j < N)
    (hsi : switchedLeft N inc left right bad i = true)
    (hsj : switchedLeft N inc left right bad j = true) :
    symConflict inc i j = false := by
  unfold switchedLeft swapLeftMask at hsi hsj
  cases hci : forwardComponent N inc left right bad i with
  | false =>
      cases hcj : forwardComponent N inc left right bad j with
      | false =>
          exact hleft i j (by simpa [hci] using hsi)
            (by simpa [hcj] using hsj)
      | true =>
          have hli : left i = true := by simpa [hci] using hsi
          have hrj : right j = true := by simpa [hcj] using hsj
          cases hconf : symConflict inc i j with
          | false => rfl
          | true =>
              have hlj : left j = false := by
                cases h : left j with
                | false => rfl
                | true =>
                    exact False.elim (false_of_true_eq_false hconf
                      (hleft i j hli h))
              have hri : right i = false := by
                cases h : right i with
                | false => rfl
                | true =>
                    exact False.elim (false_of_true_eq_false hconf
                      (hright i j h hrj))
              have hedge : disagreementEdge N inc left right i j = true := by
                unfold disagreementEdge disagreementBits leftOnly rightOnly
                simp [decide_eq_true hi, decide_eq_true hj, hli, hri, hlj,
                  hrj, hconf]
              have hcut := component_cut_closed N inc left right bad hedge
              rw [hci, hcj] at hcut
              cases hcut
  | true =>
      cases hcj : forwardComponent N inc left right bad j with
      | true =>
          exact hright i j (by simpa [hci] using hsi)
            (by simpa [hcj] using hsj)
      | false =>
          have hri : right i = true := by simpa [hci] using hsi
          have hlj : left j = true := by simpa [hcj] using hsj
          cases hconf : symConflict inc i j with
          | false => rfl
          | true =>
              have hli : left i = false := by
                cases h : left i with
                | false => rfl
                | true =>
                    exact False.elim (false_of_true_eq_false hconf
                      (hleft i j h hlj))
              have hrj : right j = false := by
                cases h : right j with
                | false => rfl
                | true =>
                    exact False.elim (false_of_true_eq_false hconf
                      (hright i j hri h))
              have hedge : disagreementEdge N inc left right i j = true := by
                unfold disagreementEdge disagreementBits leftOnly rightOnly
                simp [decide_eq_true hi, decide_eq_true hj, hli, hri, hlj,
                  hrj, hconf]
              have hcut := component_cut_closed N inc left right bad hedge
              rw [hci, hcj] at hcut
              cases hcut

theorem switchedRight_sameSide_guard
    (N : Nat) (inc : Nat → Nat → Bool)
    (left right bad : Nat → Bool)
    (hleft : ∀ i j, left i = true → left j = true →
      symConflict inc i j = false)
    (hright : ∀ i j, right i = true → right j = true →
      symConflict inc i j = false)
    (i j : Nat) (hi : i < N) (hj : j < N)
    (hsi : switchedRight N inc left right bad i = true)
    (hsj : switchedRight N inc left right bad j = true) :
    symConflict inc i j = false := by
  unfold switchedRight swapRightMask at hsi hsj
  cases hci : forwardComponent N inc left right bad i with
  | false =>
      cases hcj : forwardComponent N inc left right bad j with
      | false =>
          exact hright i j (by simpa [hci] using hsi)
            (by simpa [hcj] using hsj)
      | true =>
          have hri : right i = true := by simpa [hci] using hsi
          have hlj : left j = true := by simpa [hcj] using hsj
          cases hconf : symConflict inc i j with
          | false => rfl
          | true =>
              have hli : left i = false := by
                cases h : left i with
                | false => rfl
                | true =>
                    exact False.elim (false_of_true_eq_false hconf
                      (hleft i j h hlj))
              have hrj : right j = false := by
                cases h : right j with
                | false => rfl
                | true =>
                    exact False.elim (false_of_true_eq_false hconf
                      (hright i j hri h))
              have hedge : disagreementEdge N inc left right i j = true := by
                unfold disagreementEdge disagreementBits leftOnly rightOnly
                simp [decide_eq_true hi, decide_eq_true hj, hli, hri, hlj,
                  hrj, hconf]
              have hcut := component_cut_closed N inc left right bad hedge
              rw [hci, hcj] at hcut
              cases hcut
  | true =>
      cases hcj : forwardComponent N inc left right bad j with
      | true =>
          exact hleft i j (by simpa [hci] using hsi)
            (by simpa [hcj] using hsj)
      | false =>
          have hli : left i = true := by simpa [hci] using hsi
          have hrj : right j = true := by simpa [hcj] using hsj
          cases hconf : symConflict inc i j with
          | false => rfl
          | true =>
              have hri : right i = false := by
                cases h : right i with
                | false => rfl
                | true =>
                    exact False.elim (false_of_true_eq_false hconf
                      (hright i j h hrj))
              have hlj : left j = false := by
                cases h : left j with
                | false => rfl
                | true =>
                    exact False.elim (false_of_true_eq_false hconf
                      (hleft i j hli h))
              have hedge : disagreementEdge N inc left right i j = true := by
                unfold disagreementEdge disagreementBits leftOnly rightOnly
                simp [decide_eq_true hi, decide_eq_true hj, hli, hri, hlj,
                  hrj, hconf]
              have hcut := component_cut_closed N inc left right bad hedge
              rw [hci, hcj] at hcut
              cases hcut

#print axioms switchedLeft_sameSide_guard
#print axioms switchedRight_sameSide_guard

end YMGap.Continuum.XiExceptionalSwitchedCompatibility
