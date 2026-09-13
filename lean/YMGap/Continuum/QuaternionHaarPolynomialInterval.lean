/-
# Constructed two-sided polynomial intervals on the ORIGINAL Haar carrier

Both endpoints are existing sum-of-squares certificates, under arbitrary
Haar insertions. Positive sums and scales retain their actual variables.
The square-bound compiler supplies the initial intervals; finite sums and
explicit cap enlargement permit a cutoff-independent heat-remainder bound.
No positivity or locality estimate is assumed as an analytic axiom.
-/

import YMGap.Continuum.QuaternionHaarPolynomialSquareBound
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.QuaternionHaarPolynomialInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound

structure Interval (blocks : Nat) (p : RatPoly) (c : Q') : Type where
  support : SupportedQuaternionBlocks blocks p
  nonnegative : (0 : Q') ≤ c
  upper : Certificate blocks (polyAdd (cap c) (polyNeg p))
  lower : Certificate blocks (polyAdd (cap c) p)

private def env4 (a b p q : RatPoly) : Nat → RatPoly
  | 0 => a | 1 => b | 2 => p | 3 => q | _ => polyZero
private def minus (a b : PolyExpr) : PolyExpr := .add a (.neg b)

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') : SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, he⟩ := List.mem_map.mp ht
  rw [← he]
  exact hp s hs

namespace Interval

def ofCoeff {blocks : Nat} {p q : RatPoly} {c : Q'} (hp : SupportedQuaternionBlocks blocks p)
    (h : RatPolyCoeffEqv p q) (Q : Interval blocks q c) : Interval blocks p c where
  support := hp
  nonnegative := Q.nonnegative
  upper := .ofCoeff ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg h)) Q.upper
  lower := .ofCoeff ((RatPolyCoeffEqv.refl _).add h) Q.lower

def changeCap {blocks : Nat} {p : RatPoly} {c d : Q'} (h : Q'.eqv c d) (P : Interval blocks p c) : Interval blocks p d where
  support := P.support
  nonnegative := Q'.le_trans' _ _ _ P.nonnegative (Q'.le_of_eqv h)
  upper := .ofCoeff ((RatPolyCoeffEqv.smul_coefficient (Q'.eqv_symm h) polyOne).add (RatPolyCoeffEqv.refl _)) P.upper
  lower := .ofCoeff ((RatPolyCoeffEqv.smul_coefficient (Q'.eqv_symm h) polyOne).add (RatPolyCoeffEqv.refl _)) P.lower

def zero (blocks : Nat) : Interval blocks polyZero 0 where
  support := fun _ ht => False.elim (List.not_mem_nil ht)
  nonnegative := Q'.le_refl' _
  upper := .ofCoeff (RatPolyCoeffEqv.add_zero _) (.constant blocks 0 (Q'.le_refl' _))
  lower := .ofCoeff (RatPolyCoeffEqv.add_zero _) (.constant blocks 0 (Q'.le_refl' _))

def ofSquare {blocks : Nat} {p : RatPoly} {c : Q'} (P : SquareBound blocks p c) : Interval blocks p (c+1) where
  support := P.support
  nonnegative := Q'.zero_le_add _ _ P.nonnegative Q'.zero_le_one
  upper := P.linear
  lower := .ofCoeff ((RatPolyCoeffEqv.refl _).add
    (coeffEvalExpr_eqv_of_normalize_eq (.neg (.neg (.var 0))) (.var 0) (by decide) (fun _ => p)).symm) P.neg.linear

def add {blocks : Nat} {p q : RatPoly} {a b : Q'} (P : Interval blocks p a) (Q : Interval blocks q b) :
    Interval blocks (polyAdd p q) (a+b) where
  support := supported_add P.support Q.support
  nonnegative := Q'.zero_le_add _ _ P.nonnegative Q.nonnegative
  upper := .ofCoeff (((cap_add a b).symm.add (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq (minus (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
      (.add (minus (.var 0) (.var 2)) (minus (.var 1) (.var 3))) (by decide) (env4 (cap a) (cap b) p q)))
    (.add P.upper Q.upper)
  lower := .ofCoeff (((cap_add a b).symm.add (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
      (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3))) (by decide) (env4 (cap a) (cap b) p q)))
    (.add P.lower Q.lower)

def raise {blocks : Nat} {p : RatPoly} {c : Q'} (P : Interval blocks p c) (d : Q') (hd : (0 : Q') ≤ d) :
    Interval blocks p (c+d) where
  support := P.support
  nonnegative := Q'.zero_le_add _ _ P.nonnegative hd
  upper := .ofCoeff (((cap_add c d).symm.add (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq (minus (.add (.var 0) (.var 1)) (.var 2))
      (.add (minus (.var 0) (.var 2)) (.var 1)) (by decide) (env4 (cap c) (cap d) p polyZero)))
    (.add P.upper (.constant blocks d hd))
  lower := .ofCoeff (((cap_add c d).symm.add (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq (.add (.add (.var 0) (.var 1)) (.var 2))
      (.add (.add (.var 0) (.var 2)) (.var 1)) (by decide) (env4 (cap c) (cap d) p polyZero)))
    (.add P.lower (.constant blocks d hd))

def weaken {blocks : Nat} {p : RatPoly} {c d : Q'} (P : Interval blocks p c) (h : c ≤ d) : Interval blocks p d :=
  changeCap (poly_identity_of_normal_eq (.add (.var 0) (minus (.var 1) (.var 0))) (.var 1) (by decide)
    (fun i => if i = 0 then c else d)) (P.raise (d + -c) (Q'.sub_nonneg_of_le h))

private def capMul {blocks : Nat} {p : RatPoly} {c : Q'} (a : Q') (ha : (0 : Q') ≤ a) (P : Interval blocks p c) :
    Interval blocks (polyMul (cap a) p) (a*c) where
  support := supported_polyMul (support_smul (supported_one blocks) a) P.support
  nonnegative := Q'.mul_nonneg _ _ ha P.nonnegative
  upper := .ofCoeff (((cap_mul a c).symm.add (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq (minus (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
      (.mul (.var 0) (minus (.var 1) (.var 2))) (by decide) (env4 (cap a) (cap c) p polyZero)))
    ((Certificate.constant blocks a ha).mul P.upper)
  lower := .ofCoeff (((cap_mul a c).symm.add (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
      (.mul (.var 0) (.add (.var 1) (.var 2))) (by decide) (env4 (cap a) (cap c) p polyZero)))
    ((Certificate.constant blocks a ha).mul P.lower)

def smul {blocks : Nat} {p : RatPoly} {c : Q'} (a : Q') (ha : (0 : Q') ≤ a) (P : Interval blocks p c) :
    Interval blocks (polySmul a p) (a*c) :=
  ofCoeff (support_smul P.support a) (cap_mul_left a p).symm (capMul a ha P)

private theorem sum_append {A : Type} (f : A → RatPoly) : ∀ xs ys : List A,
    finitePolySum f (xs++ys) = polyAdd (finitePolySum f xs) (finitePolySum f ys)
  | [], _ => rfl
  | a :: xs, ys => by
      change polyAdd (f a) (finitePolySum f (xs++ys)) = _
      rw [sum_append f xs ys]
      exact (List.append_assoc _ _ _).symm

def finiteRange {blocks : Nat} (f : Nat → RatPoly) (c : Nat → Q')
    (h : ∀ n, Interval blocks (f n) (c n)) : ∀ count,
    Interval blocks (finitePolySum f (List.range count)) (finSum c count)
  | 0 => zero blocks
  | count+1 => by
      rw [List.range_succ, sum_append]
      simpa only [finitePolySum, polyAdd, polyZero, List.append_nil] using (finiteRange f c h count).add (h count)

end Interval
end YMGap.Continuum.QuaternionHaarPolynomialInterval

#print axioms YMGap.Continuum.QuaternionHaarPolynomialInterval.Interval
#print axioms YMGap.Continuum.QuaternionHaarPolynomialInterval.Interval.ofCoeff
#print axioms YMGap.Continuum.QuaternionHaarPolynomialInterval.Interval.changeCap
#print axioms YMGap.Continuum.QuaternionHaarPolynomialInterval.Interval.zero
#print axioms YMGap.Continuum.QuaternionHaarPolynomialInterval.Interval.ofSquare
#print axioms YMGap.Continuum.QuaternionHaarPolynomialInterval.Interval.add
#print axioms YMGap.Continuum.QuaternionHaarPolynomialInterval.Interval.raise
#print axioms YMGap.Continuum.QuaternionHaarPolynomialInterval.Interval.weaken
#print axioms YMGap.Continuum.QuaternionHaarPolynomialInterval.Interval.smul
#print axioms YMGap.Continuum.QuaternionHaarPolynomialInterval.Interval.finiteRange
