/-
# Fourteenth-order subordinate partition for the global Cayley charts

The denominator-cleared global vector jet carries the selected four-link
chart base to the fourteenth power.  The linear north/south partition is
therefore replaced by a positive degree-27 Bernstein partition whose selected
piece is divisible by the required fourteenth power.  Taking four products
gives sixteen certificate-positive chart weights which still sum exactly to
one, and each is coefficientwise its original chart weight to power fourteen
times a certificate-positive quotient.

This is the exponent-matching partition needed by a later signed chartwise
vector-jet reassembly.  It does not yet construct those signed numerators,
bound a remainder, remove a cutoff, or prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPartition
import YMGap.Continuum.BinomialTheorem
import YMGap.Continuum.QuaternionHaarBernsteinRowCertificate

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPowerPartition

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BinomialTheorem
open YMGap.Continuum.BernsteinVariance
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
  (finitePolySum)
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPartition
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarBernsteinRowCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QPolyHaarPositiveSubstitution
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- Number of selected-base factors required by the cleared vector jet. -/
def subordinateOrder : Nat := 14

/-- Odd degree of the symmetric positive subordinate partition. -/
def subordinateDegree : Nat := 27

/-- Degree left after extracting the selected fourteenth power. -/
def subordinateQuotientDegree : Nat := 13

def subordinateQuotientTerm
    (selected opposite : RatPoly) (index : Nat) : RatPoly :=
  polyMul
    (polySmul
      (Q'.ofNat (YMGap.RG.binom subordinateDegree
        (index + subordinateOrder))) polyOne)
    (polyMul
      (coeffPolyPow selected index)
      (coeffPolyPow opposite (subordinateQuotientDegree - index)))

/-- Positive quotient remaining after extracting the selected base to power
fourteen from its degree-27 subordinate chart weight. -/
def subordinateQuotient
    (selected opposite : RatPoly) : RatPoly :=
  finitePolySum
    (subordinateQuotientTerm selected opposite)
    (List.range subordinateOrder)

/-- One positive chart weight subordinate to the selected base. -/
def subordinateBase
    (selected opposite : RatPoly) : RatPoly :=
  polyMul
    (coeffPolyPow selected subordinateOrder)
    (subordinateQuotient selected opposite)

private def eFiniteSum
    (term : Nat → PolyExpr) : List Nat → PolyExpr
  | [] => .const 0
  | head :: tail => .add (term head) (eFiniteSum term tail)

private def eSubordinateQuotientTerm
    (selected opposite : PolyExpr) (index : Nat) : PolyExpr :=
  .mul
    (.const (Int.ofNat (YMGap.RG.binom subordinateDegree
      (index + subordinateOrder))))
    (.mul
      (.pow selected index)
      (.pow opposite (subordinateQuotientDegree - index)))

private def eSubordinateQuotient
    (selected opposite : PolyExpr) : PolyExpr :=
  eFiniteSum
    (eSubordinateQuotientTerm selected opposite)
    (List.range subordinateOrder)

private def eSubordinateBase
    (selected opposite : PolyExpr) : PolyExpr :=
  .mul (.pow selected subordinateOrder)
    (eSubordinateQuotient selected opposite)

private def eBernsteinTerm
    (selected opposite : PolyExpr) (index : Nat) : PolyExpr :=
  .mul
    (.const (Int.ofNat (YMGap.RG.binom subordinateDegree index)))
    (.mul
      (.pow selected index)
      (.pow opposite (subordinateDegree - index)))

private def ePolySum (term : Nat → PolyExpr) : Nat → PolyExpr
  | 0 => .const 0
  | count + 1 => .add (ePolySum term count) (term count)

private theorem subordinatePair_row_normal :
    normalize
      (.add
        (eSubordinateBase (.var 0) (.var 1))
        (eSubordinateBase (.var 1) (.var 0))) =
      normalize
        (ePolySum (eBernsteinTerm (.var 0) (.var 1))
          (subordinateDegree + 1)) := by
  decide

private theorem pair_cancel_normal :
    normalize
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) =
      normalize (.var 1) := by
  decide

private theorem oneMinus_coeff_eqv_of_pair
    {selected opposite : RatPoly}
    (hpair : RatPolyCoeffEqv (polyAdd selected opposite) polyOne) :
    RatPolyCoeffEqv
      (polyAdd polyOne (polyNeg selected)) opposite := by
  have hcancel := coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
    (.var 1) pair_cancel_normal
    (fun index => if index = 0 then selected else opposite)
  have hcancel' : RatPolyCoeffEqv
      (polyAdd (polyAdd selected opposite) (polyNeg selected))
      opposite := by
    simpa [coeffEvalExpr] using hcancel
  exact (hpair.symm.add (RatPolyCoeffEqv.refl (polyNeg selected))).trans
    hcancel'

private abbrev anchorPpow :=
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.ppow

private abbrev anchorPvar :=
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.pvar

private def ratPolySum (term : Nat → RatPoly) : Nat → RatPoly
  | 0 => polyZero
  | count + 1 => polyAdd (ratPolySum term count) (term count)

private theorem ratPolySum_congr
    (left right : Nat → RatPoly)
    (h : ∀ index, RatPolyCoeffEqv (left index) (right index)) :
    ∀ count,
      RatPolyCoeffEqv (ratPolySum left count) (ratPolySum right count)
  | 0 => RatPolyCoeffEqv.refl polyZero
  | count + 1 => (ratPolySum_congr left right h count).add (h count)

private def bernsteinTerm
    (selected opposite : RatPoly) (index : Nat) : RatPoly :=
  polyMul
    (polySmul
      (Q'.ofNat (YMGap.RG.binom subordinateDegree index)) polyOne)
    (polyMul
      (coeffPolyPow selected index)
      (coeffPolyPow opposite (subordinateDegree - index)))

private def bernsteinPartition (selected : RatPoly) : RatPoly :=
  subst selected
    (bernsteinRowPoly subordinateDegree
      (fun index => Q'.ofNat (YMGap.RG.binom subordinateDegree index)))

private theorem subst_pvar_coeff_eqv (selected : RatPoly) :
    RatPolyCoeffEqv (subst selected anchorPvar) selected := by
  unfold anchorPvar YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.pvar
  exact (subst_zero_cons selected [1]).trans
    (((subst_singleton selected 1).mul_left selected).trans
      ((RatPolyCoeffEqv.polyMul_smul_right 1 selected polyOne).trans
        ((RatPolyCoeffEqv.one_smul (polyMul selected polyOne)).trans
          (RatPolyCoeffEqv.mul_one selected))))

private theorem subst_ppow_coeff_eqv
    (selected : RatPoly) (base : Poly) :
    ∀ power,
      RatPolyCoeffEqv
        (subst selected (anchorPpow base power))
        (coeffPolyPow (subst selected base) power)
  | 0 => (subst_singleton selected 1).trans
      (RatPolyCoeffEqv.one_smul polyOne)
  | power + 1 =>
      (subst_pmul selected base (anchorPpow base power)).trans
        (((RatPolyCoeffEqv.refl (subst selected base)).mul
          (subst_ppow_coeff_eqv selected base power)).trans
            (RatPolyCoeffEqv.mul_comm
              (subst selected base)
              (coeffPolyPow (subst selected base) power)))

private theorem subst_oneMinusVar_coeff_eqv (selected : RatPoly) :
    RatPolyCoeffEqv
      (subst selected oneMinusVar)
      (polyAdd polyOne (polyNeg selected)) := by
  change RatPolyCoeffEqv
    (polyAdd (polySmul 1 polyOne)
      (polyMul selected (subst selected [-1]))) _
  have hnegative : RatPolyCoeffEqv
      (polyMul selected (subst selected [-1]))
      (polyNeg selected) := by
    have hscale : RatPolyCoeffEqv
        (polySmul (-1) selected) (polyNeg selected) := by
      have hnormal := coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => selected)
      have hshape : RatPolyCoeffEqv
          (polyMul (polySmul (-1) polyOne) selected)
          (polySmul (-1) selected) :=
        (RatPolyCoeffEqv.polyMul_smul_left (-1) polyOne selected).trans
          ((RatPolyCoeffEqv.one_mul selected).smul (-1))
      exact hshape.symm.trans hnormal
    exact (((subst_singleton selected (-1)).mul_left selected).trans
      ((RatPolyCoeffEqv.polyMul_smul_right (-1) selected polyOne).trans
        ((RatPolyCoeffEqv.mul_one selected).smul (-1)))).trans hscale
  exact ((RatPolyCoeffEqv.one_smul polyOne).add hnegative)

private theorem subst_bernsteinTerm_coeff_eqv
    (selected : RatPoly) (index : Nat) :
    RatPolyCoeffEqv
      (subst selected
        (pscale
          (Q'.ofNat (YMGap.RG.binom subordinateDegree index))
          (bernsteinBasisPoly subordinateDegree index)))
      (bernsteinTerm selected (subst selected oneMinusVar) index) := by
  have hvariable :=
    (subst_ppow_coeff_eqv selected anchorPvar index).trans
      (coeffPolyPow_congr (subst_pvar_coeff_eqv selected) index)
  have hopposite := subst_ppow_coeff_eqv selected oneMinusVar
    (subordinateDegree - index)
  have hproduct := (subst_pmul selected
      (anchorPpow anchorPvar index)
      (anchorPpow oneMinusVar (subordinateDegree - index))).trans
        (hvariable.mul hopposite)
  have hscale := RatPolyCoeffEqv.polyMul_smul_left
    (Q'.ofNat (YMGap.RG.binom subordinateDegree index)) polyOne
    (polyMul
      (coeffPolyPow selected index)
      (coeffPolyPow (subst selected oneMinusVar)
        (subordinateDegree - index)))
  exact (subst_pscale selected _ _).trans
    ((hproduct.smul
      (Q'.ofNat (YMGap.RG.binom subordinateDegree index))).trans
        (((RatPolyCoeffEqv.one_mul _).smul
          (Q'.ofNat (YMGap.RG.binom subordinateDegree index))).symm.trans
            hscale.symm))

private theorem subst_polyFinSum_coeff_eqv
    (selected : RatPoly) (term : Nat → Poly) :
    ∀ count,
      RatPolyCoeffEqv
        (subst selected
          (QuaternionHaarBernsteinRowCertificate.polyFinSum term count))
        (ratPolySum (fun index => subst selected (term index)) count)
  | 0 => RatPolyCoeffEqv.refl polyZero
  | count + 1 => (subst_padd selected _ _).trans
      ((subst_polyFinSum_coeff_eqv selected term count).add
        (RatPolyCoeffEqv.refl _))

private theorem bernsteinPartition_coeff_sum (selected : RatPoly) :
    RatPolyCoeffEqv
      (bernsteinPartition selected)
      (ratPolySum
        (bernsteinTerm selected (subst selected oneMinusVar))
        (subordinateDegree + 1)) := by
  unfold bernsteinPartition bernsteinRowPoly
  exact (subst_polyFinSum_coeff_eqv selected _
    (subordinateDegree + 1)).trans
      (ratPolySum_congr _ _
        (subst_bernsteinTerm_coeff_eqv selected)
        (subordinateDegree + 1))

private theorem bernsteinPartition_coeff_one (selected : RatPoly) :
    RatPolyCoeffEqv (bernsteinPartition selected) polyOne := by
  have hpoly : YMGap.Continuum.SU2ClassPolynomialAlgebra.PolyEqv
      (bernsteinRowPoly subordinateDegree
        (fun index => Q'.ofNat
          (YMGap.RG.binom subordinateDegree index))) [1] := by
    intro x
    exact Q'.eqv_trans _ _ _
      (bernsteinRowPoly_eval subordinateDegree
        (fun index => Q'.ofNat
          (YMGap.RG.binom subordinateDegree index)) x)
      (Q'.eqv_trans _ _ _
        (partition_of_unity subordinateDegree x)
        (by
          change (1 : Q') ≈ 1 + x * 0
          exact Q'.eqv_symm (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_left 1 _ _ (Q'.mul_zero_eqv x))
            (QPoly.q_add_zero_eqv 1))))
  unfold bernsteinPartition
  exact (subst_polyEqv selected hpoly).trans
    ((subst_singleton selected 1).trans
      (RatPolyCoeffEqv.one_smul polyOne))

private theorem eFiniteSum_coeff_congr
    (environment : Nat → RatPoly)
    (expression : Nat → PolyExpr) (polynomial : Nat → RatPoly)
    (h : ∀ index,
      RatPolyCoeffEqv
        (coeffEvalExpr environment (expression index))
        (polynomial index)) :
    ∀ items,
      RatPolyCoeffEqv
        (coeffEvalExpr environment (eFiniteSum expression items))
        (finitePolySum polynomial items)
  | [] => by
      simpa [eFiniteSum, finitePolySum, coeffEvalExpr] using
        (RatPolyCoeffEqv.zero_smul polyOne)
  | index :: items =>
      (h index).add
        (eFiniteSum_coeff_congr environment expression polynomial h items)

private theorem eSubordinateQuotient_coeff_congr
    (environment : Nat → RatPoly)
    (selectedExpression oppositeExpression : PolyExpr)
    (selected opposite : RatPoly)
    (hselected : RatPolyCoeffEqv
      (coeffEvalExpr environment selectedExpression) selected)
    (hopposite : RatPolyCoeffEqv
      (coeffEvalExpr environment oppositeExpression) opposite) :
    RatPolyCoeffEqv
      (coeffEvalExpr environment
        (eSubordinateQuotient selectedExpression oppositeExpression))
      (subordinateQuotient selected opposite) := by
  unfold eSubordinateQuotient subordinateQuotient
  apply eFiniteSum_coeff_congr
  intro index
  exact (RatPolyCoeffEqv.refl _).mul
    ((coeffPolyPow_congr hselected index).mul
      (coeffPolyPow_congr hopposite
        (subordinateQuotientDegree - index)))

private theorem eSubordinateBase_coeff_congr
    (environment : Nat → RatPoly)
    (selectedExpression oppositeExpression : PolyExpr)
    (selected opposite : RatPoly)
    (hselected : RatPolyCoeffEqv
      (coeffEvalExpr environment selectedExpression) selected)
    (hopposite : RatPolyCoeffEqv
      (coeffEvalExpr environment oppositeExpression) opposite) :
    RatPolyCoeffEqv
      (coeffEvalExpr environment
        (eSubordinateBase selectedExpression oppositeExpression))
      (subordinateBase selected opposite) :=
  (coeffPolyPow_congr hselected subordinateOrder).mul
    (eSubordinateQuotient_coeff_congr environment
      selectedExpression oppositeExpression selected opposite
      hselected hopposite)

private theorem ePolySum_coeff_congr
    (environment : Nat → RatPoly)
    (expression : Nat → PolyExpr) (polynomial : Nat → RatPoly)
    (h : ∀ index,
      RatPolyCoeffEqv
        (coeffEvalExpr environment (expression index))
        (polynomial index)) :
    ∀ count,
      RatPolyCoeffEqv
        (coeffEvalExpr environment (ePolySum expression count))
        (ratPolySum polynomial count)
  | 0 => by
      simpa [ePolySum, ratPolySum, coeffEvalExpr] using
        (RatPolyCoeffEqv.zero_smul polyOne)
  | count + 1 =>
      (ePolySum_coeff_congr environment expression polynomial h count).add
        (h count)

private theorem eBernsteinTerm_coeff_congr
    (environment : Nat → RatPoly)
    (selectedExpression oppositeExpression : PolyExpr)
    (selected opposite : RatPoly)
    (hselected : RatPolyCoeffEqv
      (coeffEvalExpr environment selectedExpression) selected)
    (hopposite : RatPolyCoeffEqv
      (coeffEvalExpr environment oppositeExpression) opposite)
    (index : Nat) :
    RatPolyCoeffEqv
      (coeffEvalExpr environment
        (eBernsteinTerm selectedExpression oppositeExpression index))
      (bernsteinTerm selected opposite index) :=
  (RatPolyCoeffEqv.refl _).mul
    ((coeffPolyPow_congr hselected index).mul
      (coeffPolyPow_congr hopposite (subordinateDegree - index)))

private theorem subordinatePair_coeff_row
    (selected opposite : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd
        (subordinateBase selected opposite)
        (subordinateBase opposite selected))
      (ratPolySum (bernsteinTerm selected opposite)
        (subordinateDegree + 1)) := by
  let environment : Nat → RatPoly
    | 0 => selected
    | _ => opposite
  have h := coeffEvalExpr_eqv_of_normalize_eq
    (.add
      (eSubordinateBase (.var 0) (.var 1))
      (eSubordinateBase (.var 1) (.var 0)))
    (ePolySum (eBernsteinTerm (.var 0) (.var 1))
      (subordinateDegree + 1))
    subordinatePair_row_normal
    environment
  have hselected : RatPolyCoeffEqv
      (coeffEvalExpr environment (.var 0)) selected :=
    RatPolyCoeffEqv.refl selected
  have hopposite : RatPolyCoeffEqv
      (coeffEvalExpr environment (.var 1)) opposite :=
    RatPolyCoeffEqv.refl opposite
  have hleft :=
    (eSubordinateBase_coeff_congr environment (.var 0) (.var 1)
      selected opposite hselected hopposite).add
    (eSubordinateBase_coeff_congr environment (.var 1) (.var 0)
      opposite selected hopposite hselected)
  have hright := ePolySum_coeff_congr environment
    (eBernsteinTerm (.var 0) (.var 1))
    (bernsteinTerm selected opposite)
    (eBernsteinTerm_coeff_congr environment (.var 0) (.var 1)
      selected opposite hselected hopposite)
    (subordinateDegree + 1)
  exact hleft.symm.trans (h.trans hright)

/-- Complementary bases which sum to one give a positive degree-27
partition, with each side divisible by its selected base to power fourteen. -/
theorem subordinateBase_pair_coeff_one
    {selected opposite : RatPoly}
    (hpair : RatPolyCoeffEqv (polyAdd selected opposite) polyOne) :
    RatPolyCoeffEqv
      (polyAdd
        (subordinateBase selected opposite)
        (subordinateBase opposite selected))
      polyOne := by
  have hopposite : RatPolyCoeffEqv opposite
      (subst selected oneMinusVar) :=
    (oneMinus_coeff_eqv_of_pair hpair).symm.trans
      (subst_oneMinusVar_coeff_eqv selected).symm
  exact (subordinatePair_coeff_row selected opposite).trans
    ((ratPolySum_congr _ _
      (fun index =>
        (RatPolyCoeffEqv.refl _).mul
          ((RatPolyCoeffEqv.refl
            (coeffPolyPow selected index)).mul
              (coeffPolyPow_congr hopposite
                (subordinateDegree - index))))
      (subordinateDegree + 1)).trans
        ((bernsteinPartition_coeff_sum selected).symm.trans
          (bernsteinPartition_coeff_one selected)))

private def certificatePower {blocks : Nat} {polynomial : RatPoly}
    (P : Certificate blocks polynomial) :
    ∀ exponent, Certificate blocks (coeffPolyPow polynomial exponent)
  | 0 => Certificate.one blocks
  | exponent + 1 => (certificatePower P exponent).mul P

private def finiteCertificateSum {Index : Type} {blocks : Nat}
    (polynomial : Index → RatPoly)
    (certificate : ∀ index, Certificate blocks (polynomial index)) :
    ∀ items : List Index,
      Certificate blocks (finitePolySum polynomial items)
  | [] => Certificate.ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm
      (Certificate.constant blocks 0 (Q'.le_refl' _))
  | index :: items =>
      (certificate index).add
        (finiteCertificateSum polynomial certificate items)

private def subordinateQuotientTerm_certificate {blocks : Nat}
    {selected opposite : RatPoly}
    (P : Certificate blocks selected)
    (Q : Certificate blocks opposite)
    (index : Nat) :
    Certificate blocks (subordinateQuotientTerm selected opposite index) :=
  (Certificate.constant blocks
    (Q'.ofNat (YMGap.RG.binom subordinateDegree
      (index + subordinateOrder)))
    (YMGap.RG.ofNat_nonneg _)).mul
      ((certificatePower P index).mul
        (certificatePower Q (subordinateQuotientDegree - index)))

/-- The extracted quotient is certificate-positive on the same carrier. -/
def subordinateQuotient_certificate {blocks : Nat}
    {selected opposite : RatPoly}
    (P : Certificate blocks selected)
    (Q : Certificate blocks opposite) :
    Certificate blocks (subordinateQuotient selected opposite) :=
  finiteCertificateSum
    (subordinateQuotientTerm selected opposite)
    (subordinateQuotientTerm_certificate P Q)
    (List.range subordinateOrder)

/-- The full subordinate base is certificate-positive on the same carrier. -/
def subordinateBase_certificate {blocks : Nat}
    {selected opposite : RatPoly}
    (P : Certificate blocks selected)
    (Q : Certificate blocks opposite) :
    Certificate blocks (subordinateBase selected opposite) :=
  (certificatePower P subordinateOrder).mul
    (subordinateQuotient_certificate P Q)

def oppositeChart : Bool → Bool
  | false => true
  | true => false

/-- Degree-27 subordinate weight for one sign choice on one link. -/
def cayleySubordinateBasePolynomial
    (south : Bool) (q : PolyQuaternion) : RatPoly :=
  subordinateBase
    (cayleyChartBasePolynomial south q)
    (cayleyChartBasePolynomial (oppositeChart south) q)

/-- The positive quotient after extracting the selected link base to power
fourteen. -/
def cayleySubordinateQuotientPolynomial
    (south : Bool) (q : PolyQuaternion) : RatPoly :=
  subordinateQuotient
    (cayleyChartBasePolynomial south q)
    (cayleyChartBasePolynomial (oppositeChart south) q)

/-- The two high-order subordinate link weights still sum exactly to one. -/
theorem cayleySubordinateBasePolynomial_pair_coeff_one
    (q : PolyQuaternion) :
    RatPolyCoeffEqv
      (polyAdd
        (cayleySubordinateBasePolynomial false q)
        (cayleySubordinateBasePolynomial true q))
      polyOne := by
  simpa [cayleySubordinateBasePolynomial, oppositeChart] using
    (subordinateBase_pair_coeff_one
      (cayleyChartBasePolynomial_pair_coeff_one q))

def cayleySubordinateBasePolynomial_certificate {blocks : Nat}
    (south : Bool) {q : PolyQuaternion}
    (hq : Supported blocks q)
    (hnorm : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne) :
    Certificate blocks (cayleySubordinateBasePolynomial south q) :=
  subordinateBase_certificate
    (cayleyChartBasePolynomial_certificate south hq hnorm)
    (cayleyChartBasePolynomial_certificate (oppositeChart south) hq hnorm)

def cayleySubordinateQuotientPolynomial_certificate {blocks : Nat}
    (south : Bool) {q : PolyQuaternion}
    (hq : Supported blocks q)
    (hnorm : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne) :
    Certificate blocks (cayleySubordinateQuotientPolynomial south q) :=
  subordinateQuotient_certificate
    (cayleyChartBasePolynomial_certificate south hq hnorm)
    (cayleyChartBasePolynomial_certificate (oppositeChart south) hq hnorm)

/-- Four-link product of the exponent-matched subordinate bases. -/
def globalCayleySubordinateChartWeightPolynomial
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  polyMul
    (polyMul
      (cayleySubordinateBasePolynomial chart.south0
        (faceCayleyQuaternion0 extent face))
      (cayleySubordinateBasePolynomial chart.south1
        (faceCayleyQuaternion1 extent face)))
    (polyMul
      (cayleySubordinateBasePolynomial chart.south2
        (faceCayleyQuaternion2 extent face))
      (cayleySubordinateBasePolynomial chart.south3
        (faceCayleyQuaternion3 extent face)))

/-- Product of the four certificate-positive extracted quotients. -/
def globalCayleySubordinateChartQuotientPolynomial
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  polyMul
    (polyMul
      (cayleySubordinateQuotientPolynomial chart.south0
        (faceCayleyQuaternion0 extent face))
      (cayleySubordinateQuotientPolynomial chart.south1
        (faceCayleyQuaternion1 extent face)))
    (polyMul
      (cayleySubordinateQuotientPolynomial chart.south2
        (faceCayleyQuaternion2 extent face))
      (cayleySubordinateQuotientPolynomial chart.south3
        (faceCayleyQuaternion3 extent face)))

/-- Every exponent-matched four-link chart weight is certificate-positive on
the unchanged complete ORIGINAL slab Haar carrier. -/
def globalCayleySubordinateChartWeight_certificate
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (globalCayleySubordinateChartWeightPolynomial extent face chart) := by
  let C0 := cayleySubordinateBasePolynomial_certificate chart.south0
    (supported_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry0 face))
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry0 face))
  let C1 := cayleySubordinateBasePolynomial_certificate chart.south1
    (supported_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry1 face))
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry1 face))
  let C2 := cayleySubordinateBasePolynomial_certificate chart.south2
    (supported_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry2 face))
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry2 face))
  let C3 := cayleySubordinateBasePolynomial_certificate chart.south3
    (supported_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry3 face))
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry3 face))
  exact (C0.mul C1).mul (C2.mul C3)

/-- Every extracted four-link quotient is separately certificate-positive. -/
def globalCayleySubordinateChartQuotient_certificate
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (globalCayleySubordinateChartQuotientPolynomial extent face chart) := by
  let C0 := cayleySubordinateQuotientPolynomial_certificate chart.south0
    (supported_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry0 face))
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry0 face))
  let C1 := cayleySubordinateQuotientPolynomial_certificate chart.south1
    (supported_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry1 face))
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry1 face))
  let C2 := cayleySubordinateQuotientPolynomial_certificate chart.south2
    (supported_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry2 face))
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry2 face))
  let C3 := cayleySubordinateQuotientPolynomial_certificate chart.south3
    (supported_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry3 face))
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry3 face))
  exact (C0.mul C1).mul (C2.mul C3)

/-- Sum of all sixteen exponent-matched subordinate chart weights. -/
def globalCayleySubordinateChartPartitionPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  finitePolySum
    (globalCayleySubordinateChartWeightPolynomial extent face)
    fourCayleyChartTable

private def subordinateChartBaseExpr
    (slot : Nat) (south : Bool) : PolyExpr :=
  .var (2 * slot + if south then 1 else 0)

private def subordinateChartWeightExpr
    (chart : FourCayleyChart) : PolyExpr :=
  .mul
    (.mul
      (subordinateChartBaseExpr 0 chart.south0)
      (subordinateChartBaseExpr 1 chart.south1))
    (.mul
      (subordinateChartBaseExpr 2 chart.south2)
      (subordinateChartBaseExpr 3 chart.south3))

private def subordinateChartSumExpr : PolyExpr :=
  fourCayleyChartTable.foldr
    (fun chart total => .add (subordinateChartWeightExpr chart) total)
    (.var 8)

private def subordinateChartPairProductExpr : PolyExpr :=
  .add
    (.mul
      (.mul (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
      (.mul (.add (.var 4) (.var 5)) (.add (.var 6) (.var 7))))
    (.var 8)

private theorem subordinateChartSum_normalized :
    normalize subordinateChartSumExpr =
      normalize subordinateChartPairProductExpr := by
  decide

private def subordinateChartEnvironment
    (extent : Nat) (face : Z4Plaq) : Nat → RatPoly
  | 0 => cayleySubordinateBasePolynomial false
      (faceCayleyQuaternion0 extent face)
  | 1 => cayleySubordinateBasePolynomial true
      (faceCayleyQuaternion0 extent face)
  | 2 => cayleySubordinateBasePolynomial false
      (faceCayleyQuaternion1 extent face)
  | 3 => cayleySubordinateBasePolynomial true
      (faceCayleyQuaternion1 extent face)
  | 4 => cayleySubordinateBasePolynomial false
      (faceCayleyQuaternion2 extent face)
  | 5 => cayleySubordinateBasePolynomial true
      (faceCayleyQuaternion2 extent face)
  | 6 => cayleySubordinateBasePolynomial false
      (faceCayleyQuaternion3 extent face)
  | 7 => cayleySubordinateBasePolynomial true
      (faceCayleyQuaternion3 extent face)
  | _ => polyZero

private def globalCayleySubordinateChartPairProductPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  polyMul
    (polyMul
      (polyAdd
        (cayleySubordinateBasePolynomial false
          (faceCayleyQuaternion0 extent face))
        (cayleySubordinateBasePolynomial true
          (faceCayleyQuaternion0 extent face)))
      (polyAdd
        (cayleySubordinateBasePolynomial false
          (faceCayleyQuaternion1 extent face))
        (cayleySubordinateBasePolynomial true
          (faceCayleyQuaternion1 extent face))))
    (polyMul
      (polyAdd
        (cayleySubordinateBasePolynomial false
          (faceCayleyQuaternion2 extent face))
        (cayleySubordinateBasePolynomial true
          (faceCayleyQuaternion2 extent face)))
      (polyAdd
        (cayleySubordinateBasePolynomial false
          (faceCayleyQuaternion3 extent face))
        (cayleySubordinateBasePolynomial true
          (faceCayleyQuaternion3 extent face))))

private theorem globalCayleySubordinateChartPartition_coeff_pairProduct
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (globalCayleySubordinateChartPartitionPolynomial extent face)
      (globalCayleySubordinateChartPairProductPolynomial extent face) := by
  have h := coeffEvalExpr_eqv_of_normalize_eq
    subordinateChartSumExpr subordinateChartPairProductExpr
    subordinateChartSum_normalized
    (subordinateChartEnvironment extent face)
  have hshape : RatPolyCoeffEqv
      (globalCayleySubordinateChartPartitionPolynomial extent face)
      (polyAdd
        (globalCayleySubordinateChartPairProductPolynomial extent face)
        polyZero) := by
    simpa [globalCayleySubordinateChartPartitionPolynomial,
      globalCayleySubordinateChartPairProductPolynomial,
      finitePolySum, subordinateChartSumExpr,
      subordinateChartPairProductExpr, subordinateChartWeightExpr,
      subordinateChartBaseExpr, fourCayleyChartTable,
      subordinateChartEnvironment,
      globalCayleySubordinateChartWeightPolynomial] using h
  exact hshape.trans
    (RatPolyCoeffEqv.add_zero
      (globalCayleySubordinateChartPairProductPolynomial extent face))

/-- The sixteen exponent-matched positive chart weights form an exact
coefficientwise partition of one. -/
theorem globalCayleySubordinateChartPartition_coeff_one
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (globalCayleySubordinateChartPartitionPolynomial extent face)
      polyOne := by
  have h0 := cayleySubordinateBasePolynomial_pair_coeff_one
    (faceCayleyQuaternion0 extent face)
  have h1 := cayleySubordinateBasePolynomial_pair_coeff_one
    (faceCayleyQuaternion1 extent face)
  have h2 := cayleySubordinateBasePolynomial_pair_coeff_one
    (faceCayleyQuaternion2 extent face)
  have h3 := cayleySubordinateBasePolynomial_pair_coeff_one
    (faceCayleyQuaternion3 extent face)
  have h01 := (h0.mul h1).trans (RatPolyCoeffEqv.one_mul polyOne)
  have h23 := (h2.mul h3).trans (RatPolyCoeffEqv.one_mul polyOne)
  exact
    (globalCayleySubordinateChartPartition_coeff_pairProduct extent face).trans
      ((h01.mul h23).trans (RatPolyCoeffEqv.one_mul polyOne))

/-- The complete high-order partition is itself certificate-positive. -/
def globalCayleySubordinateChartPartition_certificate
    (extent : Nat) (face : Z4Plaq) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (globalCayleySubordinateChartPartitionPolynomial extent face) :=
  finiteCertificateSum
    (globalCayleySubordinateChartWeightPolynomial extent face)
    (globalCayleySubordinateChartWeight_certificate extent face)
    fourCayleyChartTable

/-- Under the unchanged normalized ORIGINAL action the exponent-matched
sixteen-chart partition has expectation exactly one. -/
theorem globalCayleySubordinateChartPartition_expectation_one
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (halfTime : Nat) (face : Z4Plaq) :
    CReal.Equiv
      (expectation w hw0 hw1 halfTime
        (globalCayleySubordinateChartPartitionPolynomial
          (centralExtent halfTime) face))
      CReal.cone :=
  (expectation_congr w hw0 hw1 halfTime
    (globalCayleySubordinateChartPartition_coeff_one
      (centralExtent halfTime) face)).trans
    (expectation_one w hw0 hw1 halfTime)

private def eSubordinateFourSource : PolyExpr :=
  .mul
    (.mul
      (.mul (.pow (.var 0) subordinateOrder) (.var 4))
      (.mul (.pow (.var 1) subordinateOrder) (.var 5)))
    (.mul
      (.mul (.pow (.var 2) subordinateOrder) (.var 6))
      (.mul (.pow (.var 3) subordinateOrder) (.var 7)))

private def eSubordinateFourTarget : PolyExpr :=
  .mul
    (.pow
      (.mul (.mul (.var 0) (.var 1))
        (.mul (.var 2) (.var 3)))
      subordinateOrder)
    (.mul (.mul (.var 4) (.var 5))
      (.mul (.var 6) (.var 7)))

private theorem subordinateFourFactor_normalized :
    normalize eSubordinateFourSource =
      normalize eSubordinateFourTarget := by
  decide

private def subordinateFactorEnvironment
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    Nat → RatPoly
  | 0 => cayleyChartBasePolynomial chart.south0
      (faceCayleyQuaternion0 extent face)
  | 1 => cayleyChartBasePolynomial chart.south1
      (faceCayleyQuaternion1 extent face)
  | 2 => cayleyChartBasePolynomial chart.south2
      (faceCayleyQuaternion2 extent face)
  | 3 => cayleyChartBasePolynomial chart.south3
      (faceCayleyQuaternion3 extent face)
  | 4 => cayleySubordinateQuotientPolynomial chart.south0
      (faceCayleyQuaternion0 extent face)
  | 5 => cayleySubordinateQuotientPolynomial chart.south1
      (faceCayleyQuaternion1 extent face)
  | 6 => cayleySubordinateQuotientPolynomial chart.south2
      (faceCayleyQuaternion2 extent face)
  | _ => cayleySubordinateQuotientPolynomial chart.south3
      (faceCayleyQuaternion3 extent face)

/-- Each subordinate four-link chart weight is exactly the original linear
chart weight to power fourteen times a certificate-positive quotient. -/
theorem globalCayleySubordinateChartWeight_coeff_power14_quotient
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    RatPolyCoeffEqv
      (globalCayleySubordinateChartWeightPolynomial extent face chart)
      (polyMul
        (coeffPolyPow
          (globalCayleyChartWeightPolynomial extent face chart)
          subordinateOrder)
        (globalCayleySubordinateChartQuotientPolynomial
          extent face chart)) := by
  have h := coeffEvalExpr_eqv_of_normalize_eq
    eSubordinateFourSource eSubordinateFourTarget
    subordinateFourFactor_normalized
    (subordinateFactorEnvironment extent face chart)
  simpa [eSubordinateFourSource, eSubordinateFourTarget,
    subordinateFactorEnvironment,
    globalCayleySubordinateChartWeightPolynomial,
    globalCayleySubordinateChartQuotientPolynomial,
    globalCayleyChartWeightPolynomial,
    cayleySubordinateBasePolynomial, subordinateBase] using h

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPowerPartition

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPowerPartition.subordinateBase_pair_coeff_one
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPowerPartition.subordinateQuotient_certificate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPowerPartition.subordinateBase_certificate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPowerPartition.cayleySubordinateBasePolynomial_pair_coeff_one
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPowerPartition.globalCayleySubordinateChartWeight_certificate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPowerPartition.globalCayleySubordinateChartQuotient_certificate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPowerPartition.globalCayleySubordinateChartPartition_coeff_one
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPowerPartition.globalCayleySubordinateChartPartition_certificate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPowerPartition.globalCayleySubordinateChartPartition_expectation_one
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPowerPartition.globalCayleySubordinateChartWeight_coeff_power14_quotient
