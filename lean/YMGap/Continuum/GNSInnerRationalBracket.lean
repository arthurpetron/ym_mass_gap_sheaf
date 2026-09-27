/-
# Computable rational brackets for a completed GNS pairing

Given actual Cauchy representatives, the existing rational inner-product
Cauchy modulus determines an approximation index in Type.  The resulting
finite rational interval encloses the same completed inner product.  No
estimate on that inner product is introduced here.
-/

import YMGap.Continuum.GNSHilbertSpace
import YMGap.Constructive.CRealInnerRegularity
import YMGap.Constructive.CRealComplete
import YMGap.Constructive.CRealMulMono

namespace YMGap.Continuum.GNSInnerRationalBracket

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient

/-- The representative-level completed inner product has an explicit
Type-level approximation-index modulus. -/
def innerRegularity (D : GNSData) (X Y : CauchyGNS D) :
    CReal.InnerRegularity (D.cinnerRep X Y) where
  rate epsilon := epsilon.den
  regular := by
    intro epsilon hepsilon p q hp hq
    change (D.cInnerSeq X Y) (CReal.QMhat (D.cInnerSeq X Y)
      (D.cInnerQCauchy X Y) p) ≤
        (D.cInnerSeq X Y) (CReal.QMhat (D.cInnerSeq X Y)
          (D.cInnerQCauchy X Y) q) + epsilon ∧
      (D.cInnerSeq X Y) (CReal.QMhat (D.cInnerSeq X Y)
        (D.cInnerQCauchy X Y) q) ≤
        (D.cInnerSeq X Y) (CReal.QMhat (D.cInnerSeq X Y)
          (D.cInnerQCauchy X Y) p) + epsilon
    rcases Nat.le_total p q with hpq | hqp
    · exact CReal.QMhat_directed _ _ epsilon hepsilon p q hpq hp
    · exact (CReal.QMhat_directed _ _ epsilon hepsilon q p hqp hq).symm

/-- The rational value read at the supplied Type-level cutoff. -/
def bracketValue (R : CReal) (reg : CReal.InnerRegularity R)
    (epsilon : Q') : Q' := R.approx (reg.rate epsilon)

private theorem add_sub_cancel (a b : Q') : ((a + b) + -b).eqv a := by
  exact Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a b (-b))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a (b + -b) 0 (Q'.add_neg_self_eqv b))
      (Q'.eqv_of_eq (Q'.add_zero' a)))

/-- Every later approximation lies above the computed value minus epsilon,
up to the arbitrary positive slack intrinsic to eventual order. -/
theorem bracket_lower (R : CReal) (reg : CReal.InnerRegularity R)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    CReal.leEv (CReal.ofQ' (bracketValue R reg epsilon + -epsilon)) R := by
  intro delta hdelta
  refine ⟨reg.rate epsilon, fun n hn => ?_⟩
  have hv := (reg.regular epsilon hepsilon (reg.rate epsilon) n
    (Nat.le_refl _) hn).1
  have hs := Q'.add_le_add_right _ _ (-epsilon) hv
  have hc : (R.approx n + epsilon) + -epsilon ≤ R.approx n :=
    Q'.le_of_eqv (add_sub_cancel (R.approx n) epsilon)
  have hbase : bracketValue R reg epsilon + -epsilon ≤ R.approx n :=
    Q'.le_trans' _ _ _ hs hc
  exact Q'.le_trans' _ _ _ hbase
    (Q'.add_le_self_of_nonneg (R.approx n) delta (Q'.le_of_lt hdelta))

/-- Every later approximation lies below the computed value plus epsilon,
again with only the arbitrary eventual-order slack. -/
theorem bracket_upper (R : CReal) (reg : CReal.InnerRegularity R)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    CReal.leEv R (CReal.ofQ' (bracketValue R reg epsilon + epsilon)) := by
  intro delta hdelta
  refine ⟨reg.rate epsilon, fun n hn => ?_⟩
  have hv := (reg.regular epsilon hepsilon (reg.rate epsilon) n
    (Nat.le_refl _) hn).2
  exact Q'.le_trans' _ _ _ hv
    (Q'.add_le_self_of_nonneg _ delta (Q'.le_of_lt hdelta))

/-- The finite evaluator instantiated on the actual completed pairing of
the supplied GNS representatives. -/
def innerValue (D : GNSData) (X Y : CauchyGNS D) (epsilon : Q') : Q' :=
  bracketValue (D.cinnerRep X Y) (innerRegularity D X Y) epsilon

theorem inner_bracket (D : GNSData) (X Y : CauchyGNS D)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    CReal.leEv (CReal.ofQ' (innerValue D X Y epsilon + -epsilon))
      (D.cinnerRep X Y) ∧
    CReal.leEv (D.cinnerRep X Y)
      (CReal.ofQ' (innerValue D X Y epsilon + epsilon)) :=
  ⟨bracket_lower _ _ epsilon hepsilon, bracket_upper _ _ epsilon hepsilon⟩

#print axioms innerRegularity
#print axioms bracketValue
#print axioms bracket_lower
#print axioms bracket_upper
#print axioms innerValue
#print axioms inner_bracket

end YMGap.Continuum.GNSInnerRationalBracket
