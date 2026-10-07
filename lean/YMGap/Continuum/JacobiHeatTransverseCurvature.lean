/-
# Global transverse curvature of the actual positive Jacobi heat polynomial

The actual formal derivative of the positive Jacobi derivative polynomial is
used throughout.  The full-interval affine certificate propagates through both
the product and its derivative, with additive cost sum 2*w^(2*k+1).  Its
geometric ceiling is 2*w/(1-w*w); no reciprocal heat floor occurs.

This is a denominator-cleared transverse scalar certificate for the finite
weighted Jacobi heat, including truncations zero and one.  It does not pin an
intrinsic angular frame, remove the Jacobi weights, prove radial curvature,
or supply a conditional normalization or scaling bound.
-/

import YMGap.Continuum.JacobiHeatRelativeAngularBound
import YMGap.Constructive.QPolyFormalDerivative

namespace YMGap.Continuum.JacobiHeatTransverseCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QPolyHaarPositiveSubstitution
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra
open YMGap.Continuum.JTPFullProductDerivativeNormalization
open YMGap.Continuum.JacobiShiftedPositiveCoefficients

local infix:50 " ≈ " => Q'.eqv

def transverseRate (w : Q') (k : Nat) : Q' := HKPos.two (HKPos.geoAmp w k)
def transversePrefixCost (w : Q') (N : Nat) : Q' := finSum (transverseRate w) N
def transverseCap (w : Q') : Q' := HKConvGen.geoTailBase (HKPos.two w) (w*w) 0

private def gap (c : Q') (x p dp : RatPoly) : RatPoly :=
  polyAdd (polyMul (cap c) p) (polyNeg (polyMul x dp))

private theorem cap_neg (c : Q') : RatPolyCoeffEqv (polyNeg (cap c)) (cap (-c)) := by
  intro weight
  change (-(c*1))*weight []+0 ≈ ((-c)*1)*weight []+0
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv c 1))) (Q'.eqv_refl 0)

private theorem cap_pow (c : Q') : ∀ n,
    RatPolyCoeffEqv (coeffPolyPow (cap c) n) (cap (qpow c n))
  | 0 => (RatPolyCoeffEqv.one_smul polyOne).symm
  | n+1 => ((cap_pow c n).mul (RatPolyCoeffEqv.refl _)).trans (cap_mul _ _)

private theorem cap_expr (rho : Nat → Q') : ∀ E : PolyExpr,
    RatPolyCoeffEqv (coeffEvalExpr (fun i => cap (rho i)) E) (cap (eval rho E))
  | .const _ => RatPolyCoeffEqv.refl _
  | .var _ => RatPolyCoeffEqv.refl _
  | .add E F => ((cap_expr rho E).add (cap_expr rho F)).trans (cap_add _ _)
  | .mul E F => ((cap_expr rho E).mul (cap_expr rho F)).trans (cap_mul _ _)
  | .neg E => (RatPolyCoeffEqv.neg (cap_expr rho E)).trans (cap_neg _)
  | .pow E n => (coeffPolyPow_congr (cap_expr rho E) n).trans (cap_pow _ n)

/-- Direct bridge from padded formal-derivative coefficients to substitution. -/
private theorem subst_formalCoeffEqv (z : RatPoly) : ∀ p q : Poly,
    QPolyFormalDerivative.CoeffEqv p q → RatPolyCoeffEqv (subst z p) (subst z q)
  | [], [], _ => RatPolyCoeffEqv.refl _
  | [], b::bs, h => by
      have hz : RatPolyCoeffEqv polyZero
          (polyAdd (cap 0) (polyMul z polyZero)) :=
        (((RatPolyCoeffEqv.zero_smul polyOne).add (RatPolyCoeffEqv.mul_zero_right z)).trans
          (RatPolyCoeffEqv.zero_add polyZero)).symm
      exact hz.trans ((RatPolyCoeffEqv.smul_coefficient (h 0) polyOne).add
        ((subst_formalCoeffEqv z [] bs (fun i => h (i+1))).mul_left z))
  | a::as, [], h => by
      have hz : RatPolyCoeffEqv (polyAdd (cap 0) (polyMul z polyZero)) polyZero :=
        ((RatPolyCoeffEqv.zero_smul polyOne).add (RatPolyCoeffEqv.mul_zero_right z)).trans
          (RatPolyCoeffEqv.zero_add polyZero)
      exact ((RatPolyCoeffEqv.smul_coefficient (h 0) polyOne).add
        ((subst_formalCoeffEqv z as [] (fun i => h (i+1))).mul_left z)).trans hz
  | a::as, b::bs, h =>
      (RatPolyCoeffEqv.smul_coefficient (h 0) polyOne).add
        ((subst_formalCoeffEqv z as bs (fun i => h (i+1))).mul_left z)

private theorem subst_deriv_mul (z : RatPoly) (p q : Poly) :
    RatPolyCoeffEqv (subst z (pderiv (pmul p q)))
      (polyAdd (polyMul (subst z (pderiv p)) (subst z q))
        (polyMul (subst z p) (subst z (pderiv q)))) :=
  (subst_formalCoeffEqv z _ _ (pderiv_pmul p q)).trans
    ((subst_padd z _ _).trans ((subst_pmul z _ _).add (subst_pmul z _ _)))

private theorem subst_deriv_add (z : RatPoly) (p q : Poly) :
    RatPolyCoeffEqv (subst z (pderiv (padd p q)))
      (polyAdd (subst z (pderiv p)) (subst z (pderiv q))) :=
  (subst_formalCoeffEqv z _ _ (pderiv_padd p q)).trans (subst_padd z _ _)

private theorem subst_deriv_scale (z : RatPoly) (a : Q') (p : Poly) :
    RatPolyCoeffEqv (subst z (pderiv (pscale a p))) (polySmul a (subst z (pderiv p))) :=
  (subst_formalCoeffEqv z _ _ (pderiv_pscale a p)).trans (subst_pscale z a _)

private theorem factor_derivative_pin (z : RatPoly) (w : Q') (k : Nat) :
    RatPolyCoeffEqv (subst z (pderiv (factor w k))) (cap (gFacDx w k)) := by
  change RatPolyCoeffEqv (subst z [1*gFacDx w k]) _
  exact (subst_singleton z _).trans
    (RatPolyCoeffEqv.smul_coefficient (Q'.one_mul_eqv _) polyOne)

/-- The existing Jacobi Leibniz polynomial is the actual formal derivative. -/
theorem product_formal_derivative_pin (z : RatPoly) (w : Q') : ∀ N,
    RatPolyCoeffEqv (subst z (pderiv (product w N))) (subst z (derivative w N))
  | 0 => RatPolyCoeffEqv.refl _
  | N+1 => by
      have h := (subst_deriv_mul z (product w N) (factor w N)).trans
        (((product_formal_derivative_pin z w N).mul_right _).add
          ((factor_derivative_pin z w N).mul_left _))
      have hscale := (RatPolyCoeffEqv.refl
        (polyMul (subst z (derivative w N)) (subst z (factor w N)))).add
        ((RatPolyCoeffEqv.mul_comm (subst z (product w N)) (cap (gFacDx w N))).trans
          (cap_mul_left (gFacDx w N) (subst z (product w N))))
      have hsum := (subst_padd z (pmul (derivative w N) (factor w N))
        (pscale (gFacDx w N) (product w N))).trans
        ((subst_pmul z (derivative w N) (factor w N)).add
          (subst_pscale z (gFacDx w N) (product w N)))
      exact (h.trans hscale).trans hsum.symm

private def gap_mul {blocks : Nat} (x p dp q dq : RatPoly) (c d : Q')
    (P : Certificate blocks p) (Q : Certificate blocks q)
    (G : Certificate blocks (gap c x p dp)) (H : Certificate blocks (gap d x q dq)) :
    Certificate blocks (gap (c+d) x (polyMul p q)
      (polyAdd (polyMul dp q) (polyMul p dq))) :=
  .ofCoeff ((((cap_add c d).symm.mul_right _).add (.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.add (.var 0) (.var 1)) (.mul (.var 3) (.var 5)))
        (.neg (.mul (.var 2) (.add (.mul (.var 4) (.var 5)) (.mul (.var 3) (.var 6))))))
      (.add (.mul (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 2) (.var 4)))) (.var 5))
        (.mul (.var 3) (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 2) (.var 6))))))
      (by decide) (fun | 0 => cap c | 1 => cap d | 2 => x | 3 => p | 4 => dp | 5 => q | _ => dq)))
    ((G.mul Q).add (P.mul H))

private def gap_add {blocks : Nat} (x p dp q dq : RatPoly) (c : Q')
    (P : Certificate blocks (gap c x p dp)) (Q : Certificate blocks (gap c x q dq)) :
    Certificate blocks (gap c x (polyAdd p q) (polyAdd dp dq)) :=
  .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.add (.var 2) (.var 3))) (.neg (.mul (.var 1) (.add (.var 4) (.var 5)))))
    (.add (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 4))))
      (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 5)))))
    (by decide) (fun | 0 => cap c | 1 => x | 2 => p | 3 => q | 4 => dp | _ => dq)) (P.add Q)

private def gap_raise {blocks : Nat} (x p dp : RatPoly) (c d : Q') (hd : (0 : Q') ≤ d)
    (P : Certificate blocks p) (G : Certificate blocks (gap c x p dp)) :
    Certificate blocks (gap (c+d) x p dp) :=
  .ofCoeff ((((cap_add c d).symm.mul_right p).add (.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.add (.var 0) (.var 1)) (.var 3)) (.neg (.mul (.var 2) (.var 4))))
      (.add (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 2) (.var 4)))) (.mul (.var 1) (.var 3)))
      (by decide) (fun | 0 => cap c | 1 => cap d | 2 => x | 3 => p | _ => dp)))
    (G.add ((Certificate.constant blocks d hd).mul P))

private def gap_scale {blocks : Nat} (x p dp : RatPoly) (c a : Q') (ha : (0 : Q') ≤ a)
    (G : Certificate blocks (gap c x p dp)) :
    Certificate blocks (gap c x (polySmul a p) (polySmul a dp)) := by
  have h := coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.mul (.var 1) (.var 3))) (.neg (.mul (.var 2) (.mul (.var 1) (.var 4)))))
    (.mul (.var 1) (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 2) (.var 4)))))
    (by decide) (fun | 0 => cap c | 1 => cap a | 2 => x | 3 => p | _ => dp)
  exact .ofCoeff
    (((((cap_mul_left a p).symm).mul_left (cap c)).add
      (RatPolyCoeffEqv.neg ((cap_mul_left a dp).symm.mul_left x))).trans h)
    ((Certificate.constant blocks a ha).mul G)

private def baseExpr : PolyExpr :=
  .mul (.var 1) (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.neg (.var 0))))
private def slopeExpr : PolyExpr := .mul (.var 1) (.add (.var 0) (.var 0))
private def rateExpr : PolyExpr := .add (.var 0) (.var 0)
private def plusExpr : PolyExpr :=
  .mul (.mul (.var 1) (.var 0)) (.add (.mul (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
private def minusExpr : PolyExpr :=
  .mul (.mul (.var 1) (.var 0))
    (.add (.mul (.add (.var 0) (.neg (.const 1))) (.add (.var 0) (.neg (.const 1)))) (.const 1))

/-- Full-interval factor bound, retaining its actual Euler prefactor. -/
def factor_transverse_certificate {blocks : Nat} {x : RatPoly} {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (X : Interval blocks x 1) (k : Nat) :
    Certificate blocks (gap (transverseRate w k) x
      (subst (polyAdd polyOne x) (factor w k))
      (subst (polyAdd polyOne x) (pderiv (factor w k)))) := by
  let c := HKPos.geoAmp w k
  let e := 1 + -(ThetaConv.uAmp w k)
  let rho : Nat → Q' := fun | 0 => c | _ => e
  let env : Nat → RatPoly := fun | 0 => cap c | 1 => cap e | _ => x
  have hc : (0 : Q') ≤ c := Q'.le_of_lt (HKPos.pow_succ_pos_lt_one hw0 hw1 (2*k)).1
  have he : (0 : Q') ≤ e := Q'.le_of_lt (HKPos.one_sub_pos (ThetaConv.uAmp_pos_lt_one hw0 hw1 k).2)
  have ha : (0 : Q') ≤ eval rho plusExpr :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ he hc)
      (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hc hc) (Q'.zero_le_add _ _ hc hc))
  have hb : (0 : Q') ≤ eval rho minusExpr :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ he hc)
      (Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg _) Q'.zero_le_one)
  have hbase : RatPolyCoeffEqv (cap (base w k)) (coeffEvalExpr env baseExpr) :=
    (cap_expr rho baseExpr).symm
  have hslope : RatPolyCoeffEqv (cap (gFacDx w k)) (coeffEvalExpr env slopeExpr) :=
    (cap_expr rho slopeExpr).symm
  have hrate : RatPolyCoeffEqv (cap (transverseRate w k)) (coeffEvalExpr env rateExpr) :=
    (cap_expr rho rateExpr).symm
  have hone : RatPolyCoeffEqv polyOne (cap 1) := (RatPolyCoeffEqv.one_smul polyOne).symm
  have hf := ((RatPolyCoeffEqv.refl (cap (base w k))).add
    ((subst_singleton (polyAdd polyOne x) (gFacDx w k)).mul_left (polyAdd polyOne x))).trans
      (hbase.add ((hone.add (.refl x)).mul hslope))
  have hd := (factor_derivative_pin (polyAdd polyOne x) w k).trans hslope
  let lhs : PolyExpr := .add
    (.mul rateExpr (.add baseExpr (.mul (.add (.const 1) (.var 2)) slopeExpr)))
    (.neg (.mul (.var 2) slopeExpr))
  let rhs : PolyExpr := .add (.mul plusExpr (.add (.const 1) (.var 2)))
    (.mul minusExpr (.add (.const 1) (.neg (.var 2))))
  have hleft := (hrate.mul hf).add (RatPolyCoeffEqv.neg ((RatPolyCoeffEqv.refl x).mul hd))
  have hright : RatPolyCoeffEqv (coeffEvalExpr env rhs)
      (polyAdd (polyMul (cap (eval rho plusExpr)) (polyAdd (cap 1) x))
        (polyMul (cap (eval rho minusExpr)) (polyAdd (cap 1) (polyNeg x)))) :=
    ((cap_expr rho plusExpr).mul_right _).add ((cap_expr rho minusExpr).mul_right _)
  exact .ofCoeff (hleft.trans
    ((coeffEvalExpr_eqv_of_normalize_eq lhs rhs (by decide) env).trans hright))
    (((Certificate.constant blocks _ ha).mul X.lower).add
      ((Certificate.constant blocks _ hb).mul X.upper))

private def positiveSubst {blocks : Nat} {x : RatPoly} (X : Interval blocks x 1)
    (p : Poly) (hp : nonnegCoeffs p) : Certificate blocks (subst (polyAdd polyOne x) p) :=
  certificate (.ofCoeff ((RatPolyCoeffEqv.one_smul polyOne).symm.add (.refl x)) X.lower) p hp

/-- Simultaneous bounds for the actual product and actual Jacobi derivative;
both differentiated entries below are formal derivatives, not free jets. -/
def productDerivative_transverse_certificates {blocks : Nat} {x : RatPoly} {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (X : Interval blocks x 1) :
    (N : Nat) →
      Certificate blocks (gap (transversePrefixCost w N) x
        (subst (polyAdd polyOne x) (product w N))
        (subst (polyAdd polyOne x) (pderiv (product w N)))) ×
      Certificate blocks (gap (transversePrefixCost w N) x
        (subst (polyAdd polyOne x) (derivative w N))
        (subst (polyAdd polyOne x) (pderiv (derivative w N))))
  | 0 => by
      constructor
      · exact .ofCoeff
          (((((cap_mul_left 0 _).trans (RatPolyCoeffEqv.zero_smul _)).add
            (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_zero_right x))).trans (RatPolyCoeffEqv.zero_add _)).trans
            (RatPolyCoeffEqv.zero_smul polyOne).symm)
          (.constant blocks 0 (Q'.le_refl' 0))
      · exact .ofCoeff
          ((((RatPolyCoeffEqv.mul_zero_right _).add (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_zero_right x))).trans
            (RatPolyCoeffEqv.zero_add _)).trans (RatPolyCoeffEqv.zero_smul polyOne).symm)
          (.constant blocks 0 (Q'.le_refl' 0))
  | N+1 => by
      let z := polyAdd polyOne x
      let P := positiveSubst X (product w N) (product_nonnegative hw0 hw1 N)
      let H := positiveSubst X (derivative w N) (derivative_nonnegative hw0 hw1 N)
      let F := positiveSubst X (factor w N) (factor_nonnegative hw0 hw1 N)
      let old := productDerivative_transverse_certificates hw0 hw1 X N
      let FG := factor_transverse_certificate hw0 hw1 X N
      let PG := gap_mul x _ _ _ _ (transversePrefixCost w N) (transverseRate w N) P F old.1 FG
      let HG := gap_mul x _ _ _ _ (transversePrefixCost w N) (transverseRate w N) H F old.2 FG
      have hr : (0 : Q') ≤ transverseRate w N :=
        Q'.zero_le_add _ _ (Q'.pow_nonneg w (Q'.le_of_lt hw0) _) (Q'.pow_nonneg w (Q'.le_of_lt hw0) _)
      let raised := gap_raise x _ _ (transversePrefixCost w N) (transverseRate w N) hr P old.1
      let scaled := gap_scale x _ _ (transversePrefixCost w (N+1)) (gFacDx w N)
        (Q'.le_of_lt (slope_pos hw0 hw1 N)) raised
      constructor
      · exact .ofCoeff (((RatPolyCoeffEqv.refl _).mul (subst_pmul z _ _)).add
          (RatPolyCoeffEqv.neg ((subst_deriv_mul z _ _).mul_left x))) PG
      · have hp := (subst_padd z (pmul (derivative w N) (factor w N))
          (pscale (gFacDx w N) (product w N))).trans
          ((subst_pmul z (derivative w N) (factor w N)).add
            (subst_pscale z (gFacDx w N) (product w N)))
        have hd := (subst_deriv_add z (pmul (derivative w N) (factor w N))
          (pscale (gFacDx w N) (product w N))).trans
          ((subst_deriv_mul z (derivative w N) (factor w N)).add
            (subst_deriv_scale z (gFacDx w N) (product w N)))
        exact .ofCoeff (((RatPolyCoeffEqv.refl _).mul hp).add (RatPolyCoeffEqv.neg (hd.mul_left x)))
          (gap_add x _ _ _ _ (transversePrefixCost w (N+1)) HG scaled)

private theorem nome_square_lt_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : w*w < (1 : Q') :=
  HKPos.q_lt_of_le_of_lt (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right w 1 w (Q'.le_of_lt hw1) (Q'.le_of_lt hw0))
      (Q'.le_of_eqv (Q'.one_mul_eqv w))) hw1

/-- Exact cleared pin of the geometric cost to 2*w/(1-w*w). -/
theorem transverseCap_denominator_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    transverseCap w * (1 + -(w*w)) ≈ w+w := by
  have hD := HKPos.one_sub_pos (nome_square_lt_one hw0 hw1)
  have hC : transverseCap w ≈ (w+w)*HKConv.divPos 1 (1 + -(w*w)) :=
    Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv _)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hC)
    (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hD))) (Q'.mul_one_eqv _)))

/-- The transverse coefficient costs at most one inverse nome defect. -/
theorem transverseCap_nome_defect_le_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (1 + -w) * transverseCap w ≤ (1 : Q') := by
  have hp : (0 : Q') < 1+w := Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.add_le_self_of_nonneg 1 w (Q'.le_of_lt hw0))
  apply HKConvGen.mul_le_mul_left_cancel hp
  have hfactor : (1+w)*((1 + -w)*transverseCap w) ≈
      transverseCap w*(1 + -(w*w)) :=
    poly_identity_of_normal_eq
      (.mul (.add (.const 1) (.var 0)) (.mul (.add (.const 1) (.neg (.var 0))) (.var 1)))
      (.mul (.var 1) (.add (.const 1) (.neg (.mul (.var 0) (.var 0)))))
      (by decide) (fun | 0 => w | _ => transverseCap w)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hfactor (transverseCap_denominator_pin hw0 hw1)))
    (Q'.le_trans' _ _ _ (Q'.add_le_add (Q'.le_of_lt hw1) (Q'.le_refl' w))
      (Q'.ge_of_eqv (Q'.mul_one_eqv (1+w))))

/-- Every finite additive cost lies below the explicit geometric ceiling. -/
theorem transversePrefixCost_le_cap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (N : Nat) :
    transversePrefixCost w N ≤ transverseCap w := by
  have hqq0 := HKPos.q_mul_pos hw0 hw0
  have hqq1 := nome_square_lt_one hw0 hw1
  have hpin : transversePrefixCost w N ≈
      finSum (fun i => HKConvGen.geoIncrBase (HKPos.two w) (w*w) (0+i)) N :=
    by simpa only [Nat.zero_add, HKConvGen.geoIncrBase, transversePrefixCost, transverseRate] using
      (finSum_eqv_congr _ _ (fun i => HKConv.two_geoAmp_eqv w i) N)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
    (HKConvGen.geoTailBase_series_le
      (Q'.zero_le_add _ _ (Q'.le_of_lt hw0) (Q'.le_of_lt hw0)) hqq0 hqq1 0 N)

/-- GLOBAL transverse curvature for the literal normalized Jacobi heat and
its actual formal derivative. No heat-floor reciprocal or cutoff guard. -/
def heat_transverse_curvature_certificate {blocks : Nat} {x : RatPoly} {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (X : Interval blocks x 1) (N : Nat) :
    let h := subst (polyAdd polyOne x) (heat w N)
    let hx := subst (polyAdd polyOne x) (pderiv (heat w N))
    Certificate blocks (polyAdd (polyMul (cap (transverseCap w)) (polyMul h h))
      (polyNeg (polyMul x (polyMul h hx)))) := by
  let z := polyAdd polyOne x
  let a := SU2PointwiseHeatPositiveCompletion.inverseNome w * HalfPow.half
  let H := positiveSubst X (heat w N) (heat_nonnegative hw0 hw1 N)
  let G := gap_scale x _ _ (transversePrefixCost w N) a
    (Q'.mul_nonneg _ _ (SU2PointwiseHeatPositiveCompletion.inverseNome_nonnegative w)
      HalfPow.half_nonneg) (productDerivative_transverse_certificates hw0 hw1 X N).2
  have hpin := ((RatPolyCoeffEqv.refl (cap (transversePrefixCost w N))).mul
    (subst_pscale z a (derivative w N))).add
    (RatPolyCoeffEqv.neg ((subst_deriv_scale z a (derivative w N)).mul_left x))
  let GG : Certificate blocks (gap (transversePrefixCost w N) x
      (subst z (heat w N)) (subst z (pderiv (heat w N)))) := .ofCoeff hpin G
  let d := transverseCap w + -(transversePrefixCost w N)
  let raised := gap_raise x _ _ (transversePrefixCost w N) d
    (Q'.sub_nonneg_of_le (transversePrefixCost_le_cap hw0 hw1 N)) H GG
  have hc : transversePrefixCost w N+d ≈ transverseCap w :=
    poly_identity_of_normal_eq (.add (.var 0) (.add (.var 1) (.neg (.var 0)))) (.var 1)
      (by decide) (fun | 0 => transversePrefixCost w N | _ => transverseCap w)
  let finalGap : Certificate blocks (gap (transverseCap w) x
      (subst z (heat w N)) (subst z (pderiv (heat w N)))) :=
    .ofCoeff (((RatPolyCoeffEqv.smul_coefficient (Q'.eqv_symm hc) polyOne).mul_right _).add (.refl _)) raised
  exact .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.mul (.var 2) (.var 2))) (.neg (.mul (.var 1) (.mul (.var 2) (.var 3)))))
    (.mul (.var 2) (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 3)))))
    (by decide) (fun
      | 0 => cap (transverseCap w)
      | 1 => x
      | 2 => subst z (heat w N)
      | _ => subst z (pderiv (heat w N)))) (H.mul finalGap)

#print axioms product_formal_derivative_pin
#print axioms factor_transverse_certificate
#print axioms productDerivative_transverse_certificates
#print axioms transversePrefixCost_le_cap
#print axioms transverseCap_denominator_pin
#print axioms transverseCap_nome_defect_le_one
#print axioms heat_transverse_curvature_certificate

end YMGap.Continuum.JacobiHeatTransverseCurvature
