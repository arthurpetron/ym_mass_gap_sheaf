/-
# Constructive head-affine polynomial split

A literal polynomial whose terms have head-block degree at most one splits
into its homogeneous degree-zero and degree-one term lists. This is an exact
coefficient equivalence, not a quotient choice or an action comparison.
-/

import YMGap.Continuum.SU2QuaternionBlockDegreeBound
import YMGap.Continuum.SU2QuaternionSolidZonalCharacter

namespace YMGap.Continuum.QuaternionHaarHeadAffineSplit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionBlockDegreeBound

/-- Terms with no head-quaternion coordinate dependence. -/
def constantPart (p : RatPoly) : RatPoly :=
  p.filter (fun t => decide (quaternionBlockDegree t.1 0 = 0))

/-- Terms with exactly one head-quaternion coordinate. -/
def linearPart (p : RatPoly) : RatPoly :=
  p.filter (fun t => decide (quaternionBlockDegree t.1 0 = 1))

theorem constantPart_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (constantPart p) := by
  intro t ht
  exact hp t (List.mem_filter.mp ht).1

theorem linearPart_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (linearPart p) := by
  intro t ht
  exact hp t (List.mem_filter.mp ht).1

theorem constantPart_degree (p : RatPoly) :
    HasQuaternionBlockDegree 0 0 (constantPart p) := by
  intro t ht
  exact of_decide_eq_true (List.mem_filter.mp ht).2

theorem linearPart_degree (p : RatPoly) :
    HasQuaternionBlockDegree 0 1 (linearPart p) := by
  intro t ht
  exact of_decide_eq_true (List.mem_filter.mp ht).2

private theorem split_const_first : ∀ p : RatPoly,
    DegreeLE 0 1 p →
    RatPolyCoeffEqv p (polyAdd (constantPart p) (linearPart p))
  | [], _ => RatPolyCoeffEqv.refl _
  | t :: rest, hdegree => by
      have hrest : DegreeLE 0 1 rest :=
        fun s hs => hdegree s (List.mem_cons_of_mem t hs)
      have ih := split_const_first rest hrest
      have hterm : quaternionBlockDegree t.1 0 = 0 ∨
          quaternionBlockDegree t.1 0 = 1 := by
        have ht := hdegree t List.mem_cons_self
        omega
      rcases hterm with h0 | h1
      · have hnot1 : ¬ quaternionBlockDegree t.1 0 = 1 := by omega
        have h := (RatPolyCoeffEqv.refl [t]).add ih
        simpa [constantPart, linearPart, h0, hnot1, polyAdd] using h
      · have hnot0 : ¬ quaternionBlockDegree t.1 0 = 0 := by omega
        have h := (RatPolyCoeffEqv.refl [t]).add ih
        have hswap :=
          (RatPolyCoeffEqv.add_assoc [t] (constantPart rest) (linearPart rest)).symm.trans
            (((RatPolyCoeffEqv.add_comm [t] (constantPart rest)).add
              (RatPolyCoeffEqv.refl (linearPart rest))).trans
              (RatPolyCoeffEqv.add_assoc (constantPart rest) [t] (linearPart rest)))
        simpa [constantPart, linearPart, hnot0, h1, polyAdd] using h.trans hswap

/-- Every term of a head-affine polynomial is present exactly once in the
homogeneous split. No zero-coefficient terms are silently discarded. -/
theorem headAffine_split (p : RatPoly) (hdegree : DegreeLE 0 1 p) :
    RatPolyCoeffEqv p (polyAdd (linearPart p) (constantPart p)) :=
  (split_const_first p hdegree).trans
    (RatPolyCoeffEqv.add_comm (constantPart p) (linearPart p))

end YMGap.Continuum.QuaternionHaarHeadAffineSplit

#print axioms YMGap.Continuum.QuaternionHaarHeadAffineSplit.constantPart
#print axioms YMGap.Continuum.QuaternionHaarHeadAffineSplit.linearPart
#print axioms YMGap.Continuum.QuaternionHaarHeadAffineSplit.constantPart_supported
#print axioms YMGap.Continuum.QuaternionHaarHeadAffineSplit.linearPart_supported
#print axioms YMGap.Continuum.QuaternionHaarHeadAffineSplit.constantPart_degree
#print axioms YMGap.Continuum.QuaternionHaarHeadAffineSplit.linearPart_degree
#print axioms YMGap.Continuum.QuaternionHaarHeadAffineSplit.headAffine_split
