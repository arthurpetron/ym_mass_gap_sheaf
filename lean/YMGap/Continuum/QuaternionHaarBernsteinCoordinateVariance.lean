/-
The one-coordinate Bernstein variance on the ACTUAL one-block polynomial
Haar carrier.  This is a coefficient identity, before tensor averaging.
No continuous Haar or pointwise-to-Haar positivity principle is used.
-/

import YMGap.Continuum.QuaternionHaarTensorBernsteinNormDefect
import YMGap.Continuum.BernsteinVarianceClose

namespace YMGap.Continuum.QuaternionHaarBernsteinCoordinateVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QPolyHaarPositiveSubstitution
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.QuaternionHaarBernsteinRowCertificate
open YMGap.Continuum.BernsteinRationalPositiveRow
open YMGap.Continuum.QuaternionHaarTensorBernsteinCubature
open YMGap.Continuum.QuaternionHaarTensorBernsteinNormDefect
open YMGap.Continuum.QuaternionHaarUnitIntervalCoordinate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.BernsteinVariance
open YMGap.Continuum.BernsteinVarianceClose

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a*b ≈ a'*b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- Literal finite polynomial sum, with no quotienting of the summands. -/
def polySum (f : Nat → RatPoly) : Nat → RatPoly
  | 0 => polyZero
  | m+1 => polyAdd (polySum f m) (f m)

theorem polySum_congr (f g : Nat → RatPoly)
    (h : ∀ k, RatPolyCoeffEqv (f k) (g k)) :
    ∀ count, RatPolyCoeffEqv (polySum f count) (polySum g count)
  | 0 => RatPolyCoeffEqv.refl polyZero
  | count+1 => (polySum_congr f g h count).add (h count)

theorem polySum_add (f g : Nat → RatPoly) : ∀ count,
    RatPolyCoeffEqv (polySum (fun k => polyAdd (f k) (g k)) count)
      (polyAdd (polySum f count) (polySum g count))
  | 0 => (RatPolyCoeffEqv.zero_add polyZero).symm
  | count+1 => by
      change RatPolyCoeffEqv
        (polyAdd (polySum (fun k => polyAdd (f k) (g k)) count)
          (polyAdd (f count) (g count)))
        (polyAdd (polyAdd (polySum f count) (f count))
          (polyAdd (polySum g count) (g count)))
      exact ((polySum_add f g count).add (RatPolyCoeffEqv.refl _)).trans
        (RatPolyCoeffEqv.four_add_swap _ _ _ _)

theorem polySum_mul_left (factor : RatPoly) (f : Nat → RatPoly) :
    ∀ count, RatPolyCoeffEqv
      (polyMul factor (polySum f count))
      (polySum (fun k => polyMul factor (f k)) count)
  | 0 => RatPolyCoeffEqv.mul_zero_right factor
  | count+1 => by
      change RatPolyCoeffEqv
        (polyMul factor (polyAdd (polySum f count) (f count)))
        (polyAdd (polySum (fun k => polyMul factor (f k)) count)
          (polyMul factor (f count)))
      exact (RatPolyCoeffEqv.mul_add_right factor _ _).trans
        ((polySum_mul_left factor f count).add (RatPolyCoeffEqv.refl _))

theorem polySum_mul_right (f : Nat → RatPoly) (factor : RatPoly) :
    ∀ count, RatPolyCoeffEqv
      (polyMul (polySum f count) factor)
      (polySum (fun k => polyMul (f k) factor) count)
  | 0 => RatPolyCoeffEqv.mul_zero_left factor
  | count+1 => by
      change RatPolyCoeffEqv
        (polyMul (polyAdd (polySum f count) (f count)) factor)
        (polyAdd (polySum (fun k => polyMul (f k) factor) count)
          (polyMul (f count) factor))
      rw [polyMul_add_left_exact]
      exact (polySum_mul_right f factor count).add (RatPolyCoeffEqv.refl _)

theorem polySum_haar (f : Nat → RatPoly) : ∀ count,
    quaternionHaar 1 (polySum f count) ≈
      finSum (fun k => quaternionHaar 1 (f k)) count
  | 0 => Q'.eqv_refl 0
  | count+1 => by
      change quaternionHaar 1 (polyAdd (polySum f count) (f count)) ≈
        finSum (fun k => quaternionHaar 1 (f k)) count +
          quaternionHaar 1 (f count)
      exact Q'.eqv_trans _ _ _ (quaternionHaar_append 1 _ _)
        (Q'.add_eqv_congr_right _ _ _ (polySum_haar f count))

theorem subst_polyFinSum (y : RatPoly) (f : Nat → Poly) :
    ∀ count, RatPolyCoeffEqv
      (subst y (QuaternionHaarBernsteinRowCertificate.polyFinSum f count))
      (polySum (fun k => subst y (f k)) count)
  | 0 => RatPolyCoeffEqv.refl polyZero
  | count+1 => (subst_padd y _ _).trans
      ((subst_polyFinSum y f count).add (RatPolyCoeffEqv.refl _))

/-- The actual one-coordinate row partitions unity as a literal finite sum. -/
theorem coordinatePartition_sum (n : Nat) (i : Fin 4) :
    RatPolyCoeffEqv
      (polySum (fun k => coordinateBasis n i k) (n+2)) polyOne := by
  have hsum : RatPolyCoeffEqv (coordinatePartition n i)
      (polySum (fun k => coordinateBasis n i k) (n+2)) := by
    unfold coordinatePartition bernsteinRowPoly coordinateBasis
    exact subst_polyFinSum (shiftedCoordinate i)
      (fun k => pscale (Q'.ofNat (YMGap.RG.binom (degree n) k))
        (bernsteinBasisPoly (degree n) k)) (n+2)
  exact hsum.symm.trans (coordinatePartition_one n i)

private def affineVar : Poly := [-1, 2]
private def scalarDifference (n k : Nat) : Poly := psub [rawCoordinate n k] affineVar
private def scalarTerm (n k : Nat) : Poly :=
  pmul (pscale (Q'.ofNat (YMGap.RG.binom (degree n) k))
    (bernsteinBasisPoly (degree n) k))
    (pmul (scalarDifference n k) (scalarDifference n k))
private def scalarVariance (n : Nat) : Poly :=
  QuaternionHaarBernsteinRowCertificate.polyFinSum (scalarTerm n) (n+2)
private def scalarTarget (n : Nat) : Poly :=
  pscale (Q'.invSucc n) (psub [1] (pmul affineVar affineVar))

private theorem eval_scalarDifference (n k : Nat) (x : Q') :
    eval (scalarDifference n k) x ≈
      rawCoordinate n k + -(2*x + -1) := by
  have ha : eval affineVar x ≈ 2*x + -1 := by
    change Q'.eqv (-1 + x*(2+x*0)) (2*x + -1)
    exact poly_identity_of_normal_eq
      (.add (.const (-1)) (.mul (.var 0) (.add (.const 2) (.mul (.var 0) (.const 0)))))
      (.add (.mul (.const 2) (.var 0)) (.const (-1)))
      (by decide) (fun _ => x)
  exact Q'.eqv_trans _ _ _ (eval_psub [rawCoordinate n k] affineVar x)
    (Q'.add_eqv_congr'
      (by change Q'.eqv (rawCoordinate n k + x*0) (rawCoordinate n k)
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv x))
            (QPoly.q_add_zero_eqv _))
      (Q'.neg_eqv_congr _ _ ha))

private theorem eval_scalarTarget (n : Nat) (x : Q') :
    eval (scalarTarget n) x ≈
      Q'.invSucc n * (1 + -((2*x + -1)*(2*x + -1))) := by
  have ha : eval affineVar x ≈ 2*x + -1 := by
    change Q'.eqv (-1 + x*(2+x*0)) (2*x + -1)
    exact poly_identity_of_normal_eq
      (.add (.const (-1)) (.mul (.var 0) (.add (.const 2) (.mul (.var 0) (.const 0)))))
      (.add (.mul (.const 2) (.var 0)) (.const (-1)))
      (by decide) (fun _ => x)
  exact Q'.eqv_trans _ _ _ (eval_pscale _ _ _)
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (eval_psub [1] (pmul affineVar affineVar) x)
        (Q'.add_eqv_congr'
          (by change Q'.eqv (1 + x*0) 1
              exact Q'.eqv_trans _ _ _
                (Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv x))
                (QPoly.q_add_zero_eqv 1))
          (Q'.neg_eqv_congr _ _
            (Q'.eqv_trans _ _ _ (eval_pmul affineVar affineVar x)
              (mul_congr ha ha))))))

private theorem eval_scalarTerm (n k : Nat) (x : Q') :
    eval (scalarTerm n k) x ≈
      (Q'.ofNat (YMGap.RG.binom (degree n) k) *
        bernsteinBasis (degree n) x k) *
        ((rawCoordinate n k + -(2*x + -1)) *
          (rawCoordinate n k + -(2*x + -1))) := by
  have hv := YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.eval_ppow_pvar x k
  have hm : eval (YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.ppow
      oneMinusVar (degree n-k)) x ≈ (1-x)^(degree n-k) :=
    Q'.eqv_trans _ _ _
      (YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.eval_ppow
        oneMinusVar x (degree n-k))
      (YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.pow_eqv_congr
        (by
          change Q'.eqv (1+x*(-1+x*0)) (1-x)
          exact poly_identity_of_normal_eq
            (.add (.const 1) (.mul (.var 0)
              (.add (.const (-1)) (.mul (.var 0) (.const 0)))))
            (.add (.const 1) (.neg (.var 0)))
            (by decide) (fun _ => x)) (degree n-k))
  have hb : eval (bernsteinBasisPoly (degree n) k) x ≈
      bernsteinBasis (degree n) x k :=
    Q'.eqv_trans _ _ _
      (eval_pmul _ _ x)
      (mul_congr hv hm)
  have hweight := Q'.eqv_trans _ _ _
    (eval_pscale (Q'.ofNat (YMGap.RG.binom (degree n) k))
      (bernsteinBasisPoly (degree n) k) x)
    (Q'.mul_eqv_congr_left _ _ _ hb)
  have hd := eval_scalarDifference n k x
  exact Q'.eqv_trans _ _ _ (eval_pmul _ _ x)
    (mul_congr hweight
      (Q'.eqv_trans _ _ _ (eval_pmul _ _ x) (mul_congr hd hd)))

private theorem eval_scalarVariance (n : Nat) (x : Q') :
    eval (scalarVariance n) x ≈
      finSum (fun k => eval (scalarTerm n k) x) (n+2) := by
  have hsum : ∀ count, eval
      (QuaternionHaarBernsteinRowCertificate.polyFinSum (scalarTerm n) count) x ≈
      finSum (fun k => eval (scalarTerm n k) x) count := by
    intro count
    induction count with
    | zero => exact Q'.eqv_refl _
    | succ count ih =>
        change Q'.eqv (eval (padd _ _) x) _
        exact Q'.eqv_trans _ _ _ (eval_padd _ _ x)
          (Q'.add_eqv_congr' ih (Q'.eqv_refl _))
  exact hsum (n+2)

private theorem raw_difference_scaled (n k : Nat) (x : Q') :
    rawCoordinate n k + -(2*x + -1) ≈
      (2*Q'.invSucc n) *
        (Q'.ofNat k + -(Q'.ofNat (n+1)*x)) := by
  let a := Q'.invSucc n
  let N := Q'.ofNat (n+1)
  let u := Q'.ofNat k
  have hN : a*N ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv a N)
      (Q'.ofNat_succ_mul_invSucc n)
  have hring : (2*(a*u)+-1)+-(2*x+-1) ≈
      (2*a)*(u+-(N*x))+(2*(a*N+-1))*x :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.const 2) (.mul (.var 0) (.var 2))) (.const (-1)))
        (.neg (.add (.mul (.const 2) (.var 3)) (.const (-1)))))
      (.add (.mul (.mul (.const 2) (.var 0))
        (.add (.var 2) (.neg (.mul (.var 1) (.var 3)))))
        (.mul (.mul (.const 2)
          (.add (.mul (.var 0) (.var 1)) (.const (-1)))) (.var 3)))
      (by decide) (fun | 0 => a | 1 => N | 2 => u | _ => x)
  have hz : a*N+-1 ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hN (Q'.eqv_refl (-1)))
      (Q'.add_neg_self_eqv 1)
  have hcorrection : (2*(a*N+-1))*x ≈ 0 :=
    Q'.eqv_trans _ _ _
      (mul_congr
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 2 _ _ hz)
          (Q'.mul_zero_eqv 2)) (Q'.eqv_refl x))
      (Q'.zero_mul_eqv x)
  have hlast : (2*a)*(u+-(N*x))+(2*(a*N+-1))*x ≈
      (2*a)*(u+-(N*x)) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ hcorrection)
      (QPoly.q_add_zero_eqv _)
  have hactual : rawCoordinate n k + -(2*x+-1) ≈
      (2*(a*u)+-1)+-(2*x+-1) := by
    unfold rawCoordinate BernsteinFallingProductError.grid
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hactual (Q'.eqv_trans _ _ _ hring hlast)

private theorem scalar_term_scaled (n k : Nat) (x : Q') :
    (Q'.ofNat (YMGap.RG.binom (degree n) k) *
      bernsteinBasis (degree n) x k) *
      ((rawCoordinate n k + -(2*x+-1)) *
        (rawCoordinate n k + -(2*x+-1))) ≈
    ((2*Q'.invSucc n)*(2*Q'.invSucc n)) *
      (((Q'.ofNat k - Q'.ofNat (n+1)*x) *
        (Q'.ofNat k - Q'.ofNat (n+1)*x)) *
          bmono (n+1) x (1-x) k) := by
  let a := Q'.invSucc n
  let t := Q'.ofNat k - Q'.ofNat (n+1)*x
  let b := bmono (n+1) x (1-x) k
  have hd := raw_difference_scaled n k x
  have hfirst :
      (Q'.ofNat (YMGap.RG.binom (degree n) k) *
        bernsteinBasis (degree n) x k) *
        ((rawCoordinate n k + -(2*x+-1)) *
          (rawCoordinate n k + -(2*x+-1))) ≈
        b * (((2*a)*t)*((2*a)*t)) := by
    unfold degree bernsteinBasis
    exact mul_congr (Q'.eqv_refl _) (mul_congr hd hd)
  have hring : b * (((2*a)*t)*((2*a)*t)) ≈
      ((2*a)*(2*a))*((t*t)*b) :=
    poly_identity_of_normal_eq
      (.mul (.var 0)
        (.mul (.mul (.mul (.const 2) (.var 1)) (.var 2))
          (.mul (.mul (.const 2) (.var 1)) (.var 2))))
      (.mul (.mul (.mul (.const 2) (.var 1)) (.mul (.const 2) (.var 1)))
        (.mul (.mul (.var 2) (.var 2)) (.var 0)))
      (by decide) (fun | 0 => b | 1 => a | _ => t)
  exact Q'.eqv_trans _ _ _ hfirst hring

private theorem scalar_factor_identity (n : Nat) (x : Q') :
    ((2*Q'.invSucc n)*(2*Q'.invSucc n)) *
      (Q'.ofNat (n+1)*(x*(1-x))) ≈
      Q'.invSucc n * (1 + -((2*x+-1)*(2*x+-1))) := by
  let a := Q'.invSucc n
  let N := Q'.ofNat (n+1)
  have hN : a*N ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv a N)
      (Q'.ofNat_succ_mul_invSucc n)
  have hring : ((2*a)*(2*a))*(N*(x*(1-x))) ≈
      a * ((a*N) * (4*x*(1-x))) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.mul (.const 2) (.var 0))
        (.mul (.const 2) (.var 0)))
        (.mul (.var 1) (.mul (.var 2)
          (.add (.const 1) (.neg (.var 2))))))
      (.mul (.var 0) (.mul (.mul (.var 0) (.var 1))
        (.mul (.mul (.const 4) (.var 2))
          (.add (.const 1) (.neg (.var 2))))))
      (by decide) (fun | 0 => a | 1 => N | _ => x)
  have hmiddle : a*((a*N)*(4*x*(1-x))) ≈ a*(4*x*(1-x)) :=
    mul_congr (Q'.eqv_refl a)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hN)
        (Q'.one_mul_eqv _))
  have hlast : a*(4*x*(1-x)) ≈
      a*(1 + -((2*x+-1)*(2*x+-1))) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.const 4) (.var 1))
        (.add (.const 1) (.neg (.var 1)))))
      (.mul (.var 0) (.add (.const 1)
        (.neg (.mul (.add (.mul (.const 2) (.var 1)) (.const (-1)))
          (.add (.mul (.const 2) (.var 1)) (.const (-1)))))))
      (by decide) (fun | 0 => a | _ => x)
  exact Q'.eqv_trans _ _ _ hring (Q'.eqv_trans _ _ _ hmiddle hlast)

private theorem scalarVariance_eq (n : Nat) : PolyEqv (scalarVariance n) (scalarTarget n) := by
  intro x
  have hterms := finSum_eqv_congr
    (fun k => eval (scalarTerm n k) x)
    (fun k => ((2*Q'.invSucc n)*(2*Q'.invSucc n)) *
      ((Q'.ofNat k - Q'.ofNat (n+1)*x) *
        (Q'.ofNat k - Q'.ofNat (n+1)*x) *
          bmono (n+1) x (1-x) k))
    (fun k => Q'.eqv_trans _ _ _ (eval_scalarTerm n k x)
      (scalar_term_scaled n k x)) (n+2)
  have hsum := Q'.eqv_trans _ _ _ (eval_scalarVariance n x) hterms
  have hfactor := Q'.eqv_symm (const_mul_finSum
    (fun k => (Q'.ofNat k - Q'.ofNat (n+1)*x) *
      (Q'.ofNat k - Q'.ofNat (n+1)*x) *
        bmono (n+1) x (1-x) k)
    ((2*Q'.invSucc n)*(2*Q'.invSucc n)) (n+2))
  have hvariance := BernsteinVarianceClose.bernsteinVariance (n+1) x
  exact Q'.eqv_trans _ _ _ hsum
    (Q'.eqv_trans _ _ _ hfactor
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hvariance)
        (Q'.eqv_trans _ _ _ (scalar_factor_identity n x)
          (Q'.eqv_symm (eval_scalarTarget n x)))))

/-- One exact coordinate contribution at a raw Bernstein node. -/
def varianceTerm (n : Nat) (i : Fin 4) (k : Nat) : RatPoly :=
  let d := polyAdd (cap (rawCoordinate n k)) (polyNeg (polyVar i.val))
  polyMul (coordinateBasis n i k) (polyMul d d)

/-- Literal sum of the original one-block coefficient products. -/
def coordinateVariance (n : Nat) (i : Fin 4) : RatPoly :=
  polySum (varianceTerm n i) (n+2)

private theorem smul_neg (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (-1) p) (polyNeg p) :=
  (cap_mul_left (-1) p).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => p))

private theorem subst_scalarDifference (n k : Nat) (i : Fin 4) :
    RatPolyCoeffEqv
      (subst (shiftedCoordinate i) (scalarDifference n k))
      (polyAdd (cap (rawCoordinate n k)) (polyNeg (polyVar i.val))) := by
  let y := shiftedCoordinate i
  let X := polyVar i.val
  have hvar : RatPolyCoeffEqv (subst y affineVar) X := by
    change RatPolyCoeffEqv (subst (unitArgument X) [-1,2]) X
    exact unitArgument_inverse X
  unfold scalarDifference psub pneg
  exact (subst_padd y [rawCoordinate n k] (pscale (-1) affineVar)).trans
    ((subst_singleton y (rawCoordinate n k)).add
      ((subst_pscale y (-1) affineVar).trans
        ((hvar.smul (-1)).trans (smul_neg X))))

private theorem subst_scalarTerm (n k : Nat) (i : Fin 4) :
    RatPolyCoeffEqv (subst (shiftedCoordinate i) (scalarTerm n k))
      (varianceTerm n i k) := by
  let y := shiftedCoordinate i
  let d := polyAdd (cap (rawCoordinate n k)) (polyNeg (polyVar i.val))
  have hd := subst_scalarDifference n k i
  unfold scalarTerm varianceTerm coordinateBasis
  exact (subst_pmul y _ _).trans
    ((RatPolyCoeffEqv.refl _).mul
      ((subst_pmul y _ _).trans (hd.mul hd)))

private theorem subst_scalarTarget (n : Nat) (i : Fin 4) :
    RatPolyCoeffEqv (subst (shiftedCoordinate i) (scalarTarget n))
      (polySmul (Q'.invSucc n)
        (polyAdd polyOne
          (polyNeg (polyMul (polyVar i.val) (polyVar i.val))))) := by
  let y := shiftedCoordinate i
  let X := polyVar i.val
  have hvar : RatPolyCoeffEqv (subst y affineVar) X := by
    change RatPolyCoeffEqv (subst (unitArgument X) [-1,2]) X
    exact unitArgument_inverse X
  have hone : RatPolyCoeffEqv (subst y [1]) polyOne :=
    (subst_singleton y 1).trans (RatPolyCoeffEqv.one_smul polyOne)
  have hsq : RatPolyCoeffEqv (subst y (pmul affineVar affineVar))
      (polyMul X X) :=
    (subst_pmul y affineVar affineVar).trans (hvar.mul hvar)
  have hinside : RatPolyCoeffEqv
      (subst y (psub [1] (pmul affineVar affineVar)))
      (polyAdd polyOne (polyNeg (polyMul X X))) := by
    unfold psub pneg
    exact (subst_padd y [1] (pscale (-1) (pmul affineVar affineVar))).trans
      (hone.add
        ((subst_pscale y (-1) _).trans
          ((hsq.smul (-1)).trans
            (smul_neg (polyMul X X)))))
  unfold scalarTarget
  exact (subst_pscale y (Q'.invSucc n) _).trans
    (hinside.smul (Q'.invSucc n))

/-- Actual one-coordinate Bernstein variance, with `N=n+1` and no interval
or positivity hypothesis. All four coordinates remain on the SAME carrier. -/
theorem coordinateVariance_eq (n : Nat) (i : Fin 4) :
    RatPolyCoeffEqv (coordinateVariance n i)
      (polySmul (Q'.invSucc n)
        (polyAdd polyOne
          (polyNeg (polyMul (polyVar i.val) (polyVar i.val))))) := by
  have hsum : RatPolyCoeffEqv (subst (shiftedCoordinate i) (scalarVariance n))
      (coordinateVariance n i) := by
    unfold scalarVariance coordinateVariance
    exact (subst_polyFinSum (shiftedCoordinate i) (scalarTerm n) (n+2)).trans
      (polySum_congr _ _ (fun k => subst_scalarTerm n k i) (n+2))
  exact hsum.symm.trans
    ((subst_polyEqv (shiftedCoordinate i) (scalarVariance_eq n)).trans
      (subst_scalarTarget n i))

end YMGap.Continuum.QuaternionHaarBernsteinCoordinateVariance

#print axioms YMGap.Continuum.QuaternionHaarBernsteinCoordinateVariance.polySum
#print axioms YMGap.Continuum.QuaternionHaarBernsteinCoordinateVariance.polySum_congr
#print axioms YMGap.Continuum.QuaternionHaarBernsteinCoordinateVariance.polySum_add
#print axioms YMGap.Continuum.QuaternionHaarBernsteinCoordinateVariance.polySum_mul_left
#print axioms YMGap.Continuum.QuaternionHaarBernsteinCoordinateVariance.polySum_mul_right
#print axioms YMGap.Continuum.QuaternionHaarBernsteinCoordinateVariance.polySum_haar
#print axioms YMGap.Continuum.QuaternionHaarBernsteinCoordinateVariance.subst_polyFinSum
#print axioms YMGap.Continuum.QuaternionHaarBernsteinCoordinateVariance.coordinatePartition_sum
#print axioms YMGap.Continuum.QuaternionHaarBernsteinCoordinateVariance.varianceTerm
#print axioms YMGap.Continuum.QuaternionHaarBernsteinCoordinateVariance.coordinateVariance
#print axioms YMGap.Continuum.QuaternionHaarBernsteinCoordinateVariance.coordinateVariance_eq
