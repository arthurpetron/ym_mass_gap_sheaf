/-
# Finite geometric cancellation on the original shared-variable Haar carrier

For H=1+R, construct G_n=sum_{j<n}(-R)^j and E_n=(-R)^n.
The exact coefficient identity H*G_n+E_n=1 requires no limiting inverse.
If R has a certified interval cap at most 1/2, G_n has cap 2 and E_n
has cap 2^(-n). Both polynomials preserve R's block locality.

The signed corrected-moment error is bounded by c*2^(-n) times the
SAME positive background mass. The background is never replaced by a
coefficient norm or divided by a volume-dependent floor. All estimates
consume actual sum-of-squares interval certificates, not positivity axioms.
-/

import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct
import YMGap.Continuum.SU2QuaternionBlockLocality
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local infix:50 " ≈ " => Q'.eqv

private theorem support_neg {blocks : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

def negInterval {blocks : Nat} {p : RatPoly} {c : Q'} (P : Interval blocks p c) : Interval blocks (polyNeg p) c where
  support := support_neg P.support
  nonnegative := P.nonnegative
  upper := .ofCoeff ((RatPolyCoeffEqv.refl _).add
    (coeffEvalExpr_eqv_of_normalize_eq (.neg (.neg (.var 0))) (.var 0) (by decide) (fun _ => p))) P.lower
  lower := P.upper

def corrector (R : RatPoly) : Nat → RatPoly
  | 0 => polyZero
  | n+1 => polyAdd polyOne (polyMul (polyNeg R) (corrector R n))

def residual (R : RatPoly) : Nat → RatPoly
  | 0 => polyOne
  | n+1 => polyMul (polyNeg R) (residual R n)

private theorem recurrence (R G E : RatPoly) : RatPolyCoeffEqv
    (polyAdd (polyMul (polyAdd polyOne R) (polyAdd polyOne (polyMul (polyNeg R) G))) (polyMul (polyNeg R) E))
    (polyAdd polyOne (polyMul R (polyAdd polyOne (polyNeg (polyAdd (polyMul (polyAdd polyOne R) G) E))))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.add (.const 1) (.var 0)) (.add (.const 1) (.mul (.neg (.var 0)) (.var 1))))
      (.mul (.neg (.var 0)) (.var 2)))
    (.add (.const 1) (.mul (.var 0) (.add (.const 1) (.neg (.add (.mul (.add (.const 1) (.var 0)) (.var 1)) (.var 2))))))
    (by decide) (fun | 0 => R | 1 => G | _ => E)

theorem cancellation (R : RatPoly) : ∀ n,
    RatPolyCoeffEqv (polyAdd (polyMul (polyAdd polyOne R) (corrector R n)) (residual R n)) polyOne
  | 0 => ((RatPolyCoeffEqv.mul_zero_right _).add (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.zero_add _)
  | n+1 => by
      have h := ((RatPolyCoeffEqv.refl polyOne).add (RatPolyCoeffEqv.neg (cancellation R n))).mul_left R
      exact (recurrence R (corrector R n) (residual R n)).trans
        (((RatPolyCoeffEqv.refl polyOne).add h).trans
          (coeffEvalExpr_eqv_of_normalize_eq
            (.add (.const 1) (.mul (.var 0) (.add (.const 1) (.neg (.const 1)))))
            (.const 1) (by decide) (fun _ => R)))

theorem corrector_local {blocks : Nat} {allowed : Nat → Prop} {R : RatPoly} (h : BlockLocal blocks allowed R) :
    ∀ n, BlockLocal blocks allowed (corrector R n)
  | 0 => BlockLocal.zero _ _
  | n+1 => (BlockLocal.one _ _).add (h.neg.mul (corrector_local h n))

theorem residual_local {blocks : Nat} {allowed : Nat → Prop} {R : RatPoly} (h : BlockLocal blocks allowed R) :
    ∀ n, BlockLocal blocks allowed (residual R n)
  | 0 => BlockLocal.one _ _
  | n+1 => h.neg.mul (residual_local h n)

def residualInterval {blocks : Nat} {R : RatPoly} {r : Q'} (P : Interval blocks R r) :
    (n : Nat) → Interval blocks (residual R n) (r^n)
  | 0 => Interval.one _
  | n+1 => (negInterval P).mul (residualInterval P n)

/-- A bounded correction of any order; no inverse limit is needed. -/
def correctorInterval {blocks : Nat} {R : RatPoly} {r : Q'} (P : Interval blocks R r) (hr : r ≤ HalfPow.half) :
    (n : Nat) → Interval blocks (corrector R n) 2
  | 0 => (Interval.zero _).weaken (by decide)
  | n+1 => ((Interval.one _).add ((negInterval (P.weaken hr)).mul (correctorInterval P hr n))).changeCap
      (by decide : (1 : Q') + HalfPow.half*2 ≈ 2)

def defect (H R : RatPoly) (n : Nat) : RatPoly :=
  polyAdd (polyMul H (corrector R n)) (polyNeg polyOne)

theorem defect_pin {H R : RatPoly} (hH : RatPolyCoeffEqv H (polyAdd polyOne R)) (n : Nat) :
    RatPolyCoeffEqv (defect H R n) (polyNeg (residual R n)) := by
  have h := ((hH.mul_right (corrector R n)).add (RatPolyCoeffEqv.refl _)).trans (cancellation R n)
  have hr : RatPolyCoeffEqv (defect H R n)
      (polyAdd (polyAdd (polyMul H (corrector R n)) (residual R n)) (polyNeg (polyAdd polyOne (residual R n)))) :=
    coeffEvalExpr_eqv_of_normalize_eq (.add (.var 0) (.neg (.const 1)))
      (.add (.add (.var 0) (.var 1)) (.neg (.add (.const 1) (.var 1)))) (by decide)
      (fun | 0 => polyMul H (corrector R n) | _ => residual R n)
  exact hr.trans ((h.add (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq (.add (.const 1) (.neg (.add (.const 1) (.var 0)))) (.neg (.var 0))
      (by decide) (fun _ => residual R n)))

def defectInterval {blocks : Nat} {H R : RatPoly} {r : Q'} (hH : RatPolyCoeffEqv H (polyAdd polyOne R))
    (hHs : SupportedQuaternionBlocks blocks H) (P : Interval blocks R r) (hr : r ≤ HalfPow.half) (n : Nat) :
    Interval blocks (defect H R n) (HalfPow.half^n) :=
  .ofCoeff (supported_add (supported_polyMul hHs (correctorInterval P hr n).support) (support_neg (supported_one _)))
    (defect_pin hH n) (negInterval (residualInterval (P.weaken hr) n))

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly, quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t :: rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1)) (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

/-- Exact signed difference, before any absolute value or background estimate. -/
theorem moment_difference (blocks : Nat) (B p H R : RatPoly) (n : Nat) :
    quaternionHaar blocks (polyMul B (polyMul p (polyMul H (corrector R n)))) +
      -(quaternionHaar blocks (polyMul B p)) ≈ quaternionHaar blocks (polyMul B (polyMul p (defect H R n))) := by
  have hp : RatPolyCoeffEqv (polyMul B (polyMul p (defect H R n)))
      (polyAdd (polyMul B (polyMul p (polyMul H (corrector R n)))) (polyNeg (polyMul B p))) :=
    coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.mul (.var 1) (.add (.var 2) (.neg (.const 1)))))
      (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.neg (.mul (.var 0) (.var 1)))) (by decide)
      (fun | 0 => B | 1 => p | _ => polyMul H (corrector R n))
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (haar_of_coeff hp)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) (Q'.add_eqv_congr_left _ _ _ (haar_neg _ _))))

theorem relative_error {blocks : Nat} {B p H R : RatPoly} {c r : Q'} (Bpos : Certificate blocks B)
    (P : Interval blocks p c) (hH : RatPolyCoeffEqv H (polyAdd polyOne R)) (hHs : SupportedQuaternionBlocks blocks H)
    (Rcap : Interval blocks R r) (hr : r ≤ HalfPow.half) (n : Nat) :
    Q'.abs (quaternionHaar blocks (polyMul B (polyMul p (polyMul H (corrector R n)))) +
      -(quaternionHaar blocks (polyMul B p))) ≤ (c*HalfPow.half^n)*quaternionHaar blocks B :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (moment_difference blocks B p H R n)))
    ((P.mul (defectInterval hH hHs Rcap hr n)).weighted_haar_bound Bpos)

/-- Correcting a test does not cause a degree-dependent square-norm loss. -/
theorem corrected_square_bound {blocks : Nat} {B p R : RatPoly} {r : Q'} (Bpos : Certificate blocks B)
    (hp : SupportedQuaternionBlocks blocks p) (P : Interval blocks R r) (hr : r ≤ HalfPow.half) (n : Nat) :
    quaternionHaar blocks (polyMul B (polyMul (polyMul p (corrector R n)) (polyMul p (corrector R n)))) ≤
      4 * quaternionHaar blocks (polyMul B (polyMul p p)) := by
  let G := corrector R n
  have hG := correctorInterval P hr n
  have hsq := ((hG.mul hG).changeCap (by decide : (2 : Q')*2 ≈ 4)).weighted_haar_bound
    (Bpos.mul (.square p hp))
  have hpoly : RatPolyCoeffEqv (polyMul B (polyMul (polyMul p G) (polyMul p G)))
      (polyMul (polyMul B (polyMul p p)) (polyMul G G)) :=
    coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (by decide)
      (fun | 0 => B | 1 => p | _ => G)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff hpoly)) (Q'.le_trans' _ _ _ (Q'.le_abs_self _) hsq)

private theorem cap_succ_pos {c : Q'} (hc : (0 : Q') ≤ c) : (0 : Q') < c+1 :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 c hc) (Q'.le_of_eqv (Q'.add_comm_eqv 1 c)))

/-- No background mass, carrier size or heat cutoff enters this choice. -/
def correctionOrder (c : Q') (hc : (0 : Q') ≤ c) (epsilon : Q') : Nat :=
  (Q'.divPos epsilon (c+1) (cap_succ_pos hc)).den

theorem correctionOrder_budget (c : Q') (hc : (0 : Q') ≤ c) (epsilon : Q') (he : (0 : Q') < epsilon) :
    c * HalfPow.half^(correctionOrder c hc epsilon) ≤ epsilon := by
  let delta := Q'.divPos epsilon (c+1) (cap_succ_pos hc)
  have hd : (0 : Q') < delta := Q'.divPos_pos _ _ _ he
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (HalfPow.pow_half_le delta hd) hc)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.add_le_self_of_nonneg c 1 Q'.zero_le_one) (Q'.le_of_lt hd))
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.divPos_mul_eqv _ _ _))))

/-- Requested relative accuracy, without dividing by the background partition. -/
theorem relative_error_atOrder {blocks : Nat} {B p H R : RatPoly} {c r : Q'} (Bpos : Certificate blocks B)
    (P : Interval blocks p c) (hH : RatPolyCoeffEqv H (polyAdd polyOne R)) (hHs : SupportedQuaternionBlocks blocks H)
    (Rcap : Interval blocks R r) (hr : r ≤ HalfPow.half) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Q'.abs (quaternionHaar blocks (polyMul B (polyMul p (polyMul H (corrector R (correctionOrder c P.nonnegative epsilon))))) +
      -(quaternionHaar blocks (polyMul B p))) ≤ epsilon*quaternionHaar blocks B :=
  Q'.le_trans' _ _ _ (relative_error Bpos P hH hHs Rcap hr _)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (correctionOrder_budget c P.nonnegative epsilon he) Bpos.haar_nonnegative)

end YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse

#print axioms YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse.negInterval
#print axioms YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse.corrector
#print axioms YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse.residual
#print axioms YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse.cancellation
#print axioms YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse.corrector_local
#print axioms YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse.residual_local
#print axioms YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse.residualInterval
#print axioms YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse.correctorInterval
#print axioms YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse.defect
#print axioms YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse.defect_pin
#print axioms YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse.defectInterval
#print axioms YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse.moment_difference
#print axioms YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse.relative_error
#print axioms YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse.corrected_square_bound
#print axioms YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse.correctionOrder
#print axioms YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse.correctionOrder_budget
#print axioms YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse.relative_error_atOrder
