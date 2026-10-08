/-
# A produced radial Haar certificate for the actual finite Jacobi heat

The SAME finite heat's produced scalar radial bound, raised by delta>0,
has the explicit strict margin delta*floor(w)^2 at every nonempty prefix.
The existing constructive Bernstein-row compiler transports that actual
polynomial to any original certified unit-square coordinate. The heat
floor affects the row construction only; delta remains in the curvature
cost. No margin, reconstruction identity or Haar inequality is supplied.
The sharper global SAME-product cost also returns its actual certificate,
retaining the signed finite-tail payment and the same strict-margin compiler.

These are the original shifted Jacobi heat jets, NOT an identification
with a finite unweighted character prefix. Angular curvature, conditional
integration, OS and physical/scaling conclusions are separate consumers.
-/

import YMGap.Continuum.JacobiHeatRadialProducedBound
import YMGap.Continuum.QuaternionHaarBernsteinRowCertificate
import YMGap.Continuum.QuaternionHaarUnitIntervalCoordinate
import YMGap.Continuum.QPolyAffineJetTranslation

namespace YMGap.Continuum.JacobiHeatRadialHaarCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative (pderiv)
open YMGap.Continuum
open YMGap.Continuum.JacobiShiftedPositiveCoefficients (heat heat_nonnegative floor_le_heat_constant)
open YMGap.Continuum.JacobiHeatRadialMomentJets (heatRadialExpression)
open YMGap.Continuum.JacobiHeatRadialProducedBound
  (radialCap heat_radial_nonnegative nearFlatRadialCap heat_radial_nonnegative_nearFlat)
open YMGap.Continuum.JacobiProductRadialSignedTail (eighth)
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra (compose eval_compose)
open YMGap.Continuum.QPolyHaarPositiveSubstitution (subst)
open YMGap.Continuum.QPolyAffineJetTranslation (translate eval_translate)
open YMGap.Continuum.QuaternionHaarSquareCertificate (Certificate)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (SquareBound)
open YMGap.Continuum.QuaternionHaarUnitIntervalCoordinate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (RatPoly)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) :
    a*c ≈ b*d := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
      (Q'.mul_eqv_congr_left _ _ _ g)

private theorem eval_arg_congr {x y : Q'} (h : x ≈ y) : ∀ p : Poly,
    eval p x ≈ eval p y
  | [] => Q'.eqv_refl 0
  | c::p => Q'.add_eqv_congr' (Q'.eqv_refl c) (mul_congr h (eval_arg_congr h p))

private theorem eval_nonnegative : ∀ (p : Poly), nonnegCoeffs p →
    ∀ (z : Q'), (0 : Q') ≤ z → (0 : Q') ≤ eval p z
  | [], _, _, _ => Q'.le_refl' 0
  | c::p, hp, z, hz => by
    have h : decide ((0 : Q') ≤ c) = true ∧ nonnegCoeffsB p = true := by
      simpa only [nonnegCoeffs, nonnegCoeffsB, Bool.and_eq_true] using hp
    exact Q'.zero_le_add _ _ (of_decide_eq_true h.1)
      (Q'.mul_nonneg _ _ hz (eval_nonnegative p h.2 z hz))

private theorem eval_zero_le (p : Poly) (hp : nonnegCoeffs p)
    (z : Q') (hz : (0 : Q') ≤ z) : eval p 0 ≤ eval p z := by
  cases p with
  | nil => exact Q'.le_refl' 0
  | cons c p =>
    have h : decide ((0 : Q') ≤ c) = true ∧ nonnegCoeffsB p = true := by
      simpa only [nonnegCoeffs, nonnegCoeffsB, Bool.and_eq_true] using hp
    have he : eval (c::p) 0 ≈ c := Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left c _ _ (Q'.zero_mul_eqv _)) (q_add_zero_eqv c)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.add_le_self_of_nonneg c _ (Q'.mul_nonneg _ _ hz (eval_nonnegative p h.2 z hz)))

/-- Uniform actual Jacobi heat floor for every nonempty prefix. It is not
a claim about the empty heat polynomial or finite unweighted prefixes. -/
theorem radialHeat_floor {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hx0 : (-1 : Q') ≤ x)
    (N : Nat) (hN1 : 1 ≤ N) :
    SU2PointwiseHeatStrictFloor.floor w ≤ eval (heat w N) (1+x) := by
  have hz : (0 : Q') ≤ 1+x := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.add_neg_self_eqv 1)) (Q'.add_le_add_left 1 (-1) x hx0)
  exact Q'.le_trans' _ _ _ (floor_le_heat_constant hw0 hw1 N hN1)
    (eval_zero_le (heat w N) (heat_nonnegative hw0 hw1 N) (1+x) hz)

/-- Literal radial class polynomial, with all three original shifted jets.
The translates of first/second jets are pinned to derivatives of the
translated heat by QPolyAffineJetTranslation's coefficient identities. -/
def radialPolynomial (w : Q') (N : Nat) (C : Q') : Poly :=
  let h := translate 1 (heat w N)
  let hx := translate 1 (pderiv (heat w N))
  let hxx := translate 1 (pderiv (pderiv (heat w N)))
  padd (pscale C (pmul h h))
    (padd (pmul [1,0,-1] (psub (pmul h hxx) (pmul hx hx)))
      (pneg (pmul [0,1] (pmul h hx))))

private theorem eval_radial_coordinate (x : Q') :
    eval [1,0,-1] x ≈ JacobiHeatRadialMixtureCancellation.radialA x :=
  poly_identity_of_normal_eq
    (.add (.const 1) (.mul (.var 0)
      (.add (.const 0) (.mul (.var 0) (.add (.const (-1)) (.mul (.var 0) (.const 0)))))))
    (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))
    (by decide) (fun _ => x)

private theorem eval_variable (x : Q') : eval [0,1] x ≈ x :=
  poly_identity_of_normal_eq
    (.add (.const 0) (.mul (.var 0) (.add (.const 1) (.mul (.var 0) (.const 0)))))
    (.var 0) (by decide) (fun _ => x)

/-- Actual polynomial evaluation, for every rational argument, including
both endpoints. No supplied jet or polynomial-reconstruction pin. -/
theorem radialPolynomial_eval (w x C : Q') (N : Nat) :
    eval (radialPolynomial w N C) x ≈ heatRadialExpression w x C N := by
  have h := eval_translate 1 (heat w N) x
  have hx := eval_translate 1 (pderiv (heat w N)) x
  have hxx := eval_translate 1 (pderiv (pderiv (heat w N))) x
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
  exact Q'.eqv_trans _ _ _ (eval_padd _ _ x)
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (eval_pscale _ _ x)
        (Q'.mul_eqv_congr_left C _ _ (Q'.eqv_trans _ _ _ (eval_pmul _ _ x) (mul_congr h h))))
      (Q'.eqv_trans _ _ _ (eval_padd _ _ x)
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (eval_pmul _ _ x)
            (mul_congr (eval_radial_coordinate x)
              (Q'.eqv_trans _ _ _ (eval_psub _ _ x)
                (Q'.add_eqv_congr'
                  (Q'.eqv_trans _ _ _ (eval_pmul _ _ x) (mul_congr h hxx))
                  (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _ (eval_pmul _ _ x) (mul_congr hx hx)))))))
          (Q'.eqv_trans _ _ _ (eval_pneg _ x)
            (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _ (eval_pmul _ _ x)
              (mul_congr (eval_variable x)
                (Q'.eqv_trans _ _ _ (eval_pmul _ _ x) (mul_congr h hx)))))))))

private theorem raise_cost (w x C delta : Q') (N : Nat) :
    heatRadialExpression w x (C+delta) N ≈
      heatRadialExpression w x C N + delta*(eval (heat w N) (1+x)*eval (heat w N) (1+x)) := by
  let h := eval (heat w N) (1+x)
  let hx := eval (pderiv (heat w N)) (1+x)
  let hxx := eval (pderiv (pderiv (heat w N))) (1+x)
  exact poly_identity_of_normal_eq
    (.add (.add (.mul (.add (.var 0) (.var 1)) (.mul (.var 2) (.var 2))) (.var 3)) (.var 4))
    (.add (.add (.add (.mul (.var 0) (.mul (.var 2) (.var 2))) (.var 3)) (.var 4))
      (.mul (.var 1) (.mul (.var 2) (.var 2))))
    (by decide) (fun
      | 0 => C
      | 1 => delta
      | 2 => h
      | 3 => JacobiHeatRadialMixtureCancellation.radialA x*(h*hxx + -(hx*hx))
      | _ => -(x*(h*hx)))

/-- Produced strict margin. The original heat floor appears only in this
Bernstein margin, never as an inverse multiplier in the curvature cost. -/
theorem radialPolynomial_strict_margin {w x delta : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (N : Nat) (hN1 : 1 ≤ N) (hsmall : HKPos.geoAmp w N ≤ eighth)
    (hdelta : (0 : Q') < delta) :
    delta*(SU2PointwiseHeatStrictFloor.floor w*SU2PointwiseHeatStrictFloor.floor w) ≤
      eval (radialPolynomial w N (radialCap w N+delta)) x := by
  have hf := SU2PointwiseHeatStrictFloor.floor_pos hw0 hw1
  have hfloor := radialHeat_floor hw0 hw1 hx0 N hN1
  have hsq := HKConv.mul_le_mul' (Q'.le_of_lt hf)
    (Q'.le_trans' _ _ _ (Q'.le_of_lt hf) hfloor) hfloor hfloor
  have hbase := heat_radial_nonnegative hw0 hw1 hx0 hx1 N hsmall
  have hpaid := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ delta hsq (Q'.le_of_lt hdelta))
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hbase)
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  exact Q'.le_trans' _ _ _ hpaid
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (raise_cost w x (radialCap w N) delta N))
      (Q'.ge_of_eqv (radialPolynomial_eval w x (radialCap w N+delta) N)))

private theorem eval_inverse_coordinate (y : Q') : eval [-1,2] y ≈ -1+2*y :=
  poly_identity_of_normal_eq
    (.add (.const (-1)) (.mul (.var 0) (.add (.const 2) (.mul (.var 0) (.const 0)))))
    (.add (.const (-1)) (.mul (.const 2) (.var 0)))
    (by decide) (fun _ => y)

/-- Type-valued certificate on the ACTUAL original unit-square coordinate.
All scalar margins and Bernstein reconstruction witnesses are constructed.
Nonempty prefixes are required because the empty Jacobi heat is zero. -/
def radialCertificate {blocks : Nat} {X : RatPoly} {w delta : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (P : SquareBound blocks X 1)
    (N : Nat) (hN1 : 1 ≤ N) (hsmall : HKPos.geoAmp w N ≤ eighth)
    (hdelta : (0 : Q') < delta) :
    Certificate blocks (subst X (radialPolynomial w N (radialCap w N+delta))) := by
  let f := SU2PointwiseHeatStrictFloor.floor w
  let eta := delta*(f*f)
  have heta : (0 : Q') < eta :=
    Q'.mul_pos hdelta (Q'.mul_pos (SU2PointwiseHeatStrictFloor.floor_pos hw0 hw1)
      (SU2PointwiseHeatStrictFloor.floor_pos hw0 hw1))
  let p := radialPolynomial w N (radialCap w N+delta)
  have margin : ∀ y : Q', (0 : Q') ≤ y → y ≤ (1 : Q') →
      eta ≤ eval (compose [-1,2] p) y := by
    intro y hy0 hy1
    have hlo : (-1 : Q') ≤ -1+2*y :=
      Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) hy0)
    have hhi : -1+2*y ≤ (1 : Q') := Q'.le_trans' _ _ _
      (Q'.add_le_add_left (-1) _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ 2 hy1 (by decide : (0 : Q') ≤ 2)))
      (Q'.le_of_eqv (by decide : (-1 : Q')+2*1 ≈ 1))
    have he := Q'.eqv_trans _ _ _ (eval_compose [-1,2] y p)
      (eval_arg_congr (eval_inverse_coordinate y) p)
    exact Q'.le_trans' _ _ _
      (radialPolynomial_strict_margin hw0 hw1 hlo hhi N hN1 hsmall hdelta)
      (Q'.ge_of_eqv he)
  let C := QuaternionHaarBernsteinRowCertificate.strictPolynomialCertificate
    (unitArgument X) (compose [-1,2] p) eta heta margin
    (unitArgument_certificate P) (oneMinusUnitArgument_certificate P)
  exact Certificate.ofCoeff (unitArgument_unshift X p).symm C

/-- Produced global strict margin at the sharper SAME-product cost, with
the actual omitted-tail payment retained. No scalar ceiling is supplied. -/
theorem radialPolynomial_nearFlat_strict_margin {w x delta : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (N : Nat) (hN1 : 1 ≤ N) (hsmall : HKPos.geoAmp w N ≤ eighth)
    (hdelta : (0 : Q') < delta) :
    delta*(SU2PointwiseHeatStrictFloor.floor w*SU2PointwiseHeatStrictFloor.floor w) ≤
      eval (radialPolynomial w N (nearFlatRadialCap w N+delta)) x := by
  have hf := SU2PointwiseHeatStrictFloor.floor_pos hw0 hw1
  have hfloor := radialHeat_floor hw0 hw1 hx0 N hN1
  have hsq := HKConv.mul_le_mul' (Q'.le_of_lt hf)
    (Q'.le_trans' _ _ _ (Q'.le_of_lt hf) hfloor) hfloor hfloor
  have hbase := heat_radial_nonnegative_nearFlat hw0 hw1 hx0 hx1 N hsmall
  have hpaid := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ delta hsq (Q'.le_of_lt hdelta))
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hbase)
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  exact Q'.le_trans' _ _ _ hpaid
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (raise_cost w x (nearFlatRadialCap w N) delta N))
      (Q'.ge_of_eqv (radialPolynomial_eval w x (nearFlatRadialCap w N+delta) N)))

/-- Actual Type-valued Haar certificate for the sharper global radial cost.
The literal heat jets, strict margin and Bernstein rows are produced. This
does not identify the heat with an original finite character cutoff or pay
an original interacting marginal against its surviving variance. -/
def nearFlatRadialCertificate {blocks : Nat} {X : RatPoly} {w delta : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (P : SquareBound blocks X 1)
    (N : Nat) (hN1 : 1 ≤ N) (hsmall : HKPos.geoAmp w N ≤ eighth)
    (hdelta : (0 : Q') < delta) :
    Certificate blocks (subst X (radialPolynomial w N (nearFlatRadialCap w N+delta))) := by
  let f := SU2PointwiseHeatStrictFloor.floor w
  let eta := delta*(f*f)
  have heta : (0 : Q') < eta :=
    Q'.mul_pos hdelta (Q'.mul_pos (SU2PointwiseHeatStrictFloor.floor_pos hw0 hw1)
      (SU2PointwiseHeatStrictFloor.floor_pos hw0 hw1))
  let p := radialPolynomial w N (nearFlatRadialCap w N+delta)
  have margin : ∀ y : Q', (0 : Q') ≤ y → y ≤ (1 : Q') →
      eta ≤ eval (compose [-1,2] p) y := by
    intro y hy0 hy1
    have hlo : (-1 : Q') ≤ -1+2*y :=
      Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) hy0)
    have hhi : -1+2*y ≤ (1 : Q') := Q'.le_trans' _ _ _
      (Q'.add_le_add_left (-1) _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ 2 hy1 (by decide : (0 : Q') ≤ 2)))
      (Q'.le_of_eqv (by decide : (-1 : Q')+2*1 ≈ 1))
    have he := Q'.eqv_trans _ _ _ (eval_compose [-1,2] y p)
      (eval_arg_congr (eval_inverse_coordinate y) p)
    exact Q'.le_trans' _ _ _
      (radialPolynomial_nearFlat_strict_margin hw0 hw1 hlo hhi N hN1 hsmall hdelta)
      (Q'.ge_of_eqv he)
  let C := QuaternionHaarBernsteinRowCertificate.strictPolynomialCertificate
    (unitArgument X) (compose [-1,2] p) eta heta margin
    (unitArgument_certificate P) (oneMinusUnitArgument_certificate P)
  exact Certificate.ofCoeff (unitArgument_unshift X p).symm C

end YMGap.Continuum.JacobiHeatRadialHaarCertificate

#print axioms YMGap.Continuum.JacobiHeatRadialHaarCertificate.radialHeat_floor
#print axioms YMGap.Continuum.JacobiHeatRadialHaarCertificate.radialPolynomial
#print axioms YMGap.Continuum.JacobiHeatRadialHaarCertificate.radialPolynomial_eval
#print axioms YMGap.Continuum.JacobiHeatRadialHaarCertificate.radialPolynomial_strict_margin
#print axioms YMGap.Continuum.JacobiHeatRadialHaarCertificate.radialCertificate
#print axioms YMGap.Continuum.JacobiHeatRadialHaarCertificate.radialPolynomial_nearFlat_strict_margin
#print axioms YMGap.Continuum.JacobiHeatRadialHaarCertificate.nearFlatRadialCertificate
