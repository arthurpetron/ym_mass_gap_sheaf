/-
# Represented-sector witnesses along the coupled Chebyshev recurrence

If the input has a supplied dense-sector representative, zero belongs to the
sector, and the operator preserves represented-sector witnesses, then both
components of every actual coupled-energy state have such witnesses. This is
an algebraic closure result on the existing completion; it assumes neither
self-adjointness nor contraction.
-/

import YMGap.Continuum.GNSRepresentedSector
import YMGap.Continuum.GNSChebyshevEnergy

namespace YMGap.Continuum.GNSRepresentedSectorRecurrence

set_option autoImplicit false

open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSRepresentedSector
open YMGap.Continuum.GNSChebyshevEnergy

/-- The literal two-component state is represented in the same dense sector
at every order, provided the input witness and operator-preservation witnesses
are supplied. -/
def state_representatives
    (D : GNSData) (P : D.V → Prop)
    (hzero : P D.zero)
    (hadd : ∀ p q, P p → P q → P (D.add p q))
    (hneg : ∀ p, P p → P (D.neg p))
    (X : GNSCompletionSpace D → GNSCompletionSpace D)
    (hX : ∀ x, Representative D P x → Representative D P (X x))
    {x : GNSCompletionSpace D} (hx : Representative D P x) (n : Nat) :
    Representative D P (state X x n).1 ×
      Representative D P (state X x n).2 := by
  induction n with
  | zero =>
      exact ⟨hx, Representative.ofDense D.zero hzero⟩
  | succ n ih =>
      change Representative D P
          (step X (state X x n).1 (state X x n).2).1 ×
        Representative D P
          (step X (state X x n).1 (state X x n).2).2
      let hXu := hX _ ih.2
      let hv := ih.1.add hadd hXu
      exact ⟨(hX _ hv).sub hadd hneg ih.2, hv⟩

#print axioms state_representatives

end YMGap.Continuum.GNSRepresentedSectorRecurrence
