/-
# Probability algebra for the constructive BF4 U(1) cutoff limit

The finite canonical U(1) slab law has exact rational interval,
event-monotonicity, and complement identities at every outer charge cutoff.
This module transports those pointwise identities to the Bishop-style
constructive real built in `BF4U1OuterCutoffCRealLimit`.

At fixed `0 < w < 1` and fixed finite slab half-width:

* every Boolean-event limit lies between zero and one in the transitive
  constructive-real order `CReal.leEv`;
* Boolean-event inclusion is monotone for the limiting probability; and
* an event limit plus its Boolean-complement limit is `CReal.Equiv` to one.

These are fixed-nome, fixed-geometry, finite-volume U(1) probability laws.
No spacing, infinite-volume, changing-carrier, or nonabelian limit is claimed.
-/

import YMGap.Continuum.BF4U1OuterCutoffCRealLimit
import YMGap.Continuum.BF4U1OuterCutoffEventProbabilityAlgebra
import YMGap.Constructive.CRealComplete
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.BF4U1OuterCutoffCRealProbabilityAlgebra

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4U1OuterCutoffCRealLimit
open YMGap.Continuum.BF4U1OuterCutoffEventProbabilityAlgebra
open YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
open YMGap.Continuum.BF4U1SameCarrierPushforward

/-! ## 1. The limiting probability lies in the unit interval -/

/-- The fixed-event outer-cutoff limit is nonnegative in the transitive
constructive-real order. -/
theorem canonicalU1SlabEventProbabilityLimit_nonnegative
    (w : Q') (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (half : Nat) (event : ChargeLabelling → Bool) :
    CReal.leEv CReal.czero
      (canonicalU1SlabEventProbabilityLimit
        w hw0 hw1 half event) := by
  apply CReal.leEv_ofQ'_of_approx_ge
  intro K
  exact canonicalU1SlabEventProbability_nonnegative
    w (Q'.le_of_lt hw0) half K event

/-- The fixed-event outer-cutoff limit is at most one in the transitive
constructive-real order. -/
theorem canonicalU1SlabEventProbabilityLimit_le_one
    (w : Q') (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (half : Nat) (event : ChargeLabelling → Bool) :
    CReal.leEv
      (canonicalU1SlabEventProbabilityLimit
        w hw0 hw1 half event)
      CReal.cone := by
  apply CReal.leEv_le_ofQ'_of_approx_le
  intro K
  exact canonicalU1SlabEventProbability_le_one
    w (Q'.le_of_lt hw0) half K event

/-- Unit-interval package for the limiting event probability. -/
theorem canonicalU1SlabEventProbabilityLimit_mem_unitInterval
    (w : Q') (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (half : Nat) (event : ChargeLabelling → Bool) :
    CReal.leEv CReal.czero
        (canonicalU1SlabEventProbabilityLimit
          w hw0 hw1 half event) ∧
      CReal.leEv
        (canonicalU1SlabEventProbabilityLimit
          w hw0 hw1 half event)
        CReal.cone :=
  ⟨canonicalU1SlabEventProbabilityLimit_nonnegative
      w hw0 hw1 half event,
    canonicalU1SlabEventProbabilityLimit_le_one
      w hw0 hw1 half event⟩

/-! ## 2. Event inclusion remains monotone in the limit -/

/-- Boolean-event inclusion is monotone for the constructive-real limiting
probability.  The proof is pointwise at every exact rational cutoff and hence
requires no order-limit interchange principle. -/
theorem canonicalU1SlabEventProbabilityLimit_mono
    (w : Q') (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (half : Nat)
    (first second : ChargeLabelling → Bool)
    (himp :
      ∀ state, first state = true → second state = true) :
    CReal.leEv
      (canonicalU1SlabEventProbabilityLimit
        w hw0 hw1 half first)
      (canonicalU1SlabEventProbabilityLimit
        w hw0 hw1 half second) := by
  intro ε hε
  refine ⟨0, fun K _ => ?_⟩
  exact Q'.le_trans' _ _ _
    (canonicalU1SlabEventProbability_mono
      w (Q'.le_of_lt hw0) half K
      first second himp)
    (Q'.add_le_self_of_nonneg
      (canonicalU1SlabEventProbability
        w (Q'.le_of_lt hw0) half K second)
      ε (Q'.le_of_lt hε))

/-! ## 3. Exact complement normalization in the limit -/

/-- A limiting event probability plus the limiting probability of its
Boolean complement is constructively equivalent to one.  The rational
identity holds at every approximation index. -/
theorem canonicalU1SlabEventProbabilityLimit_add_complement_equiv_one
    (w : Q') (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (half : Nat) (event : ChargeLabelling → Bool) :
    CReal.Equiv
      (CReal.add
        (canonicalU1SlabEventProbabilityLimit
          w hw0 hw1 half event)
        (canonicalU1SlabEventProbabilityLimit
          w hw0 hw1 half
            (fun state => !(event state))))
      CReal.cone := by
  apply Equiv_of_approx_eqv
  intro K
  exact
    canonicalU1SlabEventProbability_add_complement_eqv_one
      w (Q'.le_of_lt hw0) half K event

#print axioms canonicalU1SlabEventProbabilityLimit_nonnegative
#print axioms canonicalU1SlabEventProbabilityLimit_le_one
#print axioms canonicalU1SlabEventProbabilityLimit_mem_unitInterval
#print axioms canonicalU1SlabEventProbabilityLimit_mono
#print axioms canonicalU1SlabEventProbabilityLimit_add_complement_equiv_one

end YMGap.Continuum.BF4U1OuterCutoffCRealProbabilityAlgebra
