/-
# Radial Young inequality about an arbitrary mean

This is a polynomial sum-of-squares identity under the original Haar
insertion.  In particular the radial polynomial need only have a constructive
positive certificate; it is not replaced by an independent or stationary
source.  The favorable radial square is retained in the principal inequality.
-/

import YMGap.Continuum.QuaternionHaarWordDifference
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.QuaternionHaarRadialMeanYoung

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap SquareBound)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_add cap_mul cap_mul_left)
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_add)
open YMGap.Continuum.QuaternionHaarWordDifference (weighted_order weighted_scale)

local infix:50 " ≈ " => Q'.eqv

private theorem support_neg {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
  exact hp v hv

private def env (c t : Q') (f r : RatPoly) : Nat → RatPoly
  | 0 => cap c | 1 => cap t | 2 => f | _ => r

private def eb : PolyExpr := .add (.var 0) (.neg (.var 2))
private def esq (e : PolyExpr) : PolyExpr := .mul e e
private def ed : PolyExpr :=
  .add (.mul (.var 1) eb) (.neg (.mul (.var 0) (.var 3)))
private def erbsq : PolyExpr := .mul (.mul (.var 1) (.var 3)) (esq eb)
private def eupper : PolyExpr :=
  .add
    (.add (.mul (esq (.var 1)) (esq eb))
      (.mul (.add (.var 1) (esq (.var 0))) (esq (.var 3))))
    (.mul (.mul (.var 1) (.add (.const 4) (.neg (esq (.var 0))))) (.var 3))
private def elower : PolyExpr :=
  .mul (.var 1)
    (.add (.mul (.var 3) (.add (.const 4) (.neg (esq (.var 2)))))
      (esq (.var 3)))

/-- The centering displacement, retaining the literal observable. -/
def displacement (c : Q') (f : RatPoly) : RatPoly :=
  polyAdd (cap c) (polyNeg f)

/-- The square in the cleared Young identity. -/
def youngSquareRoot (c t : Q') (f r : RatPoly) : RatPoly :=
  polyAdd (polyMul (cap t) (displacement c f))
    (polyNeg (polyMul (cap c) r))

/-- `t²(c-f)² + (t+c²)r² + t(4-c²)r`, as a literal polynomial. -/
def youngUpper (c t : Q') (f r : RatPoly) : RatPoly :=
  coeffEvalExpr (env c t f r) eupper

/-- `t[r(4-f²)+r²]`, the radial Wilson upper expression. -/
def youngLower (c t : Q') (f r : RatPoly) : RatPoly :=
  coeffEvalExpr (env c t f r) elower

/-- The nonnegative correction `t r(c-f)²`. -/
def radialSquare (c t : Q') (f r : RatPoly) : RatPoly :=
  polyMul (polyMul (cap t) r)
    (polyMul (displacement c f) (displacement c f))

theorem displacement_supported {n : Nat} {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) (c : Q') :
    SupportedQuaternionBlocks n (displacement c f) :=
  supported_add (SquareBound.constant n c).support (support_neg hf)

theorem youngSquareRoot_supported {n : Nat} {f r : RatPoly}
    (hf : SupportedQuaternionBlocks n f) (hr : SupportedQuaternionBlocks n r)
    (c t : Q') : SupportedQuaternionBlocks n (youngSquareRoot c t f r) :=
  supported_add
    (supported_polyMul (SquareBound.constant n t).support (displacement_supported hf c))
    (support_neg (supported_polyMul (SquareBound.constant n c).support hr))

/-- Exact cleared polynomial identity.  No bound on the center is used. -/
theorem young_identity (c t : Q') (f r : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (youngUpper c t f r) (polyNeg (youngLower c t f r)))
      (polyAdd (polyMul (youngSquareRoot c t f r) (youngSquareRoot c t f r))
        (radialSquare c t f r)) := by
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add eupper (.neg elower))
    (.add (esq ed) erbsq) (by decide) (env c t f r)

/-- The radial Young gap is a constructed sum of squares.  The only
positivity inputs are `t ≥ 0` and the certificate for the actual `r`. -/
def youngGapCertificate {n : Nat} {f r : RatPoly}
    (hf : SupportedQuaternionBlocks n f) (hr : SupportedQuaternionBlocks n r)
    (R : Certificate n r) (c t : Q') (ht : (0 : Q') ≤ t) :
    Certificate n (polyAdd (youngUpper c t f r) (polyNeg (youngLower c t f r))) :=
  .ofCoeff (young_identity c t f r)
    ((Certificate.square (youngSquareRoot c t f r) (youngSquareRoot_supported hf hr c t)).add
      (((Certificate.constant n t ht).mul R).mul
        (Certificate.square (displacement c f) (displacement_supported hf c))))

/-- The stronger retained-square identity is itself a square certificate. -/
theorem young_retained_identity (c t : Q') (f r : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (youngUpper c t f r)
        (polyNeg (polyAdd (youngLower c t f r) (radialSquare c t f r))))
      (polyMul (youngSquareRoot c t f r) (youngSquareRoot c t f r)) := by
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add eupper (.neg (.add elower erbsq)))
    (esq ed) (by decide) (env c t f r)

def youngRetainedCertificate {n : Nat} {f r : RatPoly}
    (hf : SupportedQuaternionBlocks n f) (hr : SupportedQuaternionBlocks n r)
    (c t : Q') :
    Certificate n (polyAdd (youngUpper c t f r)
      (polyNeg (polyAdd (youngLower c t f r) (radialSquare c t f r)))) :=
  .ofCoeff (young_retained_identity c t f r)
    (Certificate.square (youngSquareRoot c t f r) (youngSquareRoot_supported hf hr c t))

/-- Weighted Haar Young inequality, with the favorable `t r(c-f)²` term
still on the left.  No factorization of `W`, nor independence of `f,r`, is
used. -/
theorem weighted_young_retained {n : Nat} {W f r : RatPoly}
    (Wcert : Certificate n W)
    (hf : SupportedQuaternionBlocks n f) (hr : SupportedQuaternionBlocks n r)
    (c t : Q') :
    quaternionHaar n (polyMul W (polyAdd (youngLower c t f r) (radialSquare c t f r))) ≤
      quaternionHaar n (polyMul W (youngUpper c t f r)) :=
  weighted_order Wcert (youngRetainedCertificate hf hr c t)

/-- Dropping the nonnegative radial square gives the familiar cleared
Young inequality, without changing the supplied positive weight. -/
theorem weighted_young {n : Nat} {W f r : RatPoly}
    (Wcert : Certificate n W)
    (hf : SupportedQuaternionBlocks n f) (hr : SupportedQuaternionBlocks n r)
    (R : Certificate n r) (c t : Q') (ht : (0 : Q') ≤ t) :
    quaternionHaar n (polyMul W (youngLower c t f r)) ≤
      quaternionHaar n (polyMul W (youngUpper c t f r)) :=
  weighted_order Wcert (youngGapCertificate hf hr R c t ht)

private theorem cap_neg (c : Q') : RatPolyCoeffEqv (polyNeg (cap c)) (cap (-c)) := by
  intro weight
  change (-(c*1))*weight []+0 ≈ ((-c)*1)*weight []+0
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv c 1))) (Q'.eqv_refl _)

private theorem cap_four : RatPolyCoeffEqv
    (polySmul (Q'.ofInt 4) polyOne) (cap 4) :=
  RatPolyCoeffEqv.smul_coefficient (by decide) polyOne

private theorem cap_t_plus_csq (c t : Q') :
    RatPolyCoeffEqv (polyAdd (cap t) (polyMul (cap c) (cap c))) (cap (t+c*c)) :=
  ((RatPolyCoeffEqv.refl _).add (cap_mul c c)).trans (cap_add t (c*c))

private theorem cap_four_minus_csq (c : Q') :
    RatPolyCoeffEqv (polyAdd (polySmul (Q'.ofInt 4) polyOne)
      (polyNeg (polyMul (cap c) (cap c)))) (cap ((4 : Q') + -(c*c))) :=
  ((cap_four.add (RatPolyCoeffEqv.neg (cap_mul c c))).trans
    ((RatPolyCoeffEqv.refl _).add (cap_neg (c*c)))).trans
    (cap_add 4 (-(c*c)))

private theorem weighted_cap (n : Nat) (W p : RatPoly) (a : Q') :
    quaternionHaar n (polyMul W (polyMul (cap a) p)) ≈
      a*quaternionHaar n (polyMul W p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((cap_mul_left a p).mul_left W))
    (weighted_scale n W p a)

private theorem weighted_upper_moment (n : Nat) (W f r : RatPoly) (c t : Q') :
    quaternionHaar n (polyMul W (youngUpper c t f r)) ≈
      (t*t)*quaternionHaar n (polyMul W
        (polyMul (displacement c f) (displacement c f))) +
      (t+c*c)*quaternionHaar n (polyMul W (polyMul r r)) +
      (t*((4 : Q') + -(c*c)))*quaternionHaar n (polyMul W r) := by
  let b2 := polyMul (displacement c f) (displacement c f)
  let r2 := polyMul r r
  have hA : quaternionHaar n (polyMul W (polyMul (polyMul (cap t) (cap t)) b2)) ≈
      (t*t)*quaternionHaar n (polyMul W b2) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (((cap_mul t t).mul (RatPolyCoeffEqv.refl b2)).mul_left W))
      (weighted_cap n W b2 (t*t))
  have hB : quaternionHaar n (polyMul W
      (polyMul (polyAdd (cap t) (polyMul (cap c) (cap c))) r2)) ≈
      (t+c*c)*quaternionHaar n (polyMul W r2) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (((cap_t_plus_csq c t).mul
      (RatPolyCoeffEqv.refl r2)).mul_left W)) (weighted_cap n W r2 (t+c*c))
  have hC : quaternionHaar n (polyMul W
      (polyMul (polyMul (cap t)
        (polyAdd (polySmul (Q'.ofInt 4) polyOne)
          (polyNeg (polyMul (cap c) (cap c))))) r)) ≈
      (t*((4 : Q') + -(c*c)))*quaternionHaar n (polyMul W r) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (((((RatPolyCoeffEqv.refl (cap t)).mul
      (cap_four_minus_csq c)).trans (cap_mul t ((4 : Q') + -(c*c)))).mul
      (RatPolyCoeffEqv.refl r)).mul_left W))
      (weighted_cap n W r (t*((4 : Q') + -(c*c))))
  change quaternionHaar n (polyMul W (polyAdd
      (polyAdd (polyMul (polyMul (cap t) (cap t)) b2)
        (polyMul (polyAdd (cap t) (polyMul (cap c) (cap c))) r2))
      (polyMul (polyMul (cap t)
        (polyAdd (polySmul (Q'.ofInt 4) polyOne)
          (polyNeg (polyMul (cap c) (cap c))))) r))) ≈ _
  exact Q'.eqv_trans _ _ _ (haar_weighted_add n W _ _)
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (haar_weighted_add n W _ _)
        (Q'.add_eqv_congr' hA hB)) hC)

private theorem weighted_lower_moment (n : Nat) (W f r : RatPoly) (c t : Q') :
    quaternionHaar n (polyMul W (youngLower c t f r)) ≈
      t*(quaternionHaar n (polyMul W
        (polyMul r (polyAdd (polySmul (Q'.ofInt 4) polyOne)
          (polyNeg (polyMul f f))))) +
        quaternionHaar n (polyMul W (polyMul r r))) := by
  change quaternionHaar n (polyMul W (polyMul (cap t)
    (polyAdd (polyMul r (polyAdd (polySmul (Q'.ofInt 4) polyOne)
      (polyNeg (polyMul f f)))) (polyMul r r)))) ≈ _
  exact Q'.eqv_trans _ _ _ (weighted_cap n W _ t)
    (Q'.mul_eqv_congr_left _ _ _ (haar_weighted_add n W _ _))

private theorem weighted_radial_square_moment (n : Nat) (W f r : RatPoly) (c t : Q') :
    quaternionHaar n (polyMul W (radialSquare c t f r)) ≈
      t*quaternionHaar n (polyMul W
        (polyMul r (polyMul (displacement c f) (displacement c f)))) := by
  change quaternionHaar n (polyMul W (polyMul (polyMul (cap t) r)
    (polyMul (displacement c f) (displacement c f)))) ≈ _
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
    (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
    (by decide) (fun | 0 => W | 1 => cap t | 2 => r
                     | _ => polyMul (displacement c f) (displacement c f))))
    (weighted_cap n W _ t)

/-- Explicit rational-moment form of the retained Young estimate.  Every
moment uses the same supplied weight `W`, including the mixed radial moment. -/
theorem weighted_young_moments_retained {n : Nat} {W f r : RatPoly}
    (Wcert : Certificate n W)
    (hf : SupportedQuaternionBlocks n f) (hr : SupportedQuaternionBlocks n r)
    (c t : Q') :
    t*(quaternionHaar n (polyMul W
        (polyMul r (polyAdd (polySmul (Q'.ofInt 4) polyOne)
          (polyNeg (polyMul f f))))) +
      quaternionHaar n (polyMul W (polyMul r r))) +
      t*quaternionHaar n (polyMul W
        (polyMul r (polyMul (displacement c f) (displacement c f)))) ≤
      (t*t)*quaternionHaar n (polyMul W
        (polyMul (displacement c f) (displacement c f))) +
      (t+c*c)*quaternionHaar n (polyMul W (polyMul r r)) +
      (t*((4 : Q') + -(c*c)))*quaternionHaar n (polyMul W r) := by
  have h := weighted_young_retained Wcert hf hr c t
  have hl : quaternionHaar n (polyMul W
      (polyAdd (youngLower c t f r) (radialSquare c t f r))) ≈
      t*(quaternionHaar n (polyMul W
        (polyMul r (polyAdd (polySmul (Q'.ofInt 4) polyOne)
          (polyNeg (polyMul f f))))) +
        quaternionHaar n (polyMul W (polyMul r r))) +
        t*quaternionHaar n (polyMul W
          (polyMul r (polyMul (displacement c f) (displacement c f)))) :=
    Q'.eqv_trans _ _ _ (haar_weighted_add n W _ _)
      (Q'.add_eqv_congr' (weighted_lower_moment n W f r c t)
        (weighted_radial_square_moment n W f r c t))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl) (Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (weighted_upper_moment n W f r c t)))

/-- Dropping the favorable term needs the explicit nonnegative radial
certificate and `t ≥ 0`; it is not inferred from a changed weight. -/
theorem weighted_young_moments {n : Nat} {W f r : RatPoly}
    (Wcert : Certificate n W)
    (hf : SupportedQuaternionBlocks n f) (hr : SupportedQuaternionBlocks n r)
    (R : Certificate n r) (c t : Q') (ht : (0 : Q') ≤ t) :
    t*(quaternionHaar n (polyMul W
        (polyMul r (polyAdd (polySmul (Q'.ofInt 4) polyOne)
          (polyNeg (polyMul f f))))) +
      quaternionHaar n (polyMul W (polyMul r r))) ≤
      (t*t)*quaternionHaar n (polyMul W
        (polyMul (displacement c f) (displacement c f))) +
      (t+c*c)*quaternionHaar n (polyMul W (polyMul r r)) +
      (t*((4 : Q') + -(c*c)))*quaternionHaar n (polyMul W r) := by
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (weighted_lower_moment n W f r c t))
    (Q'.le_trans' _ _ _ (weighted_young Wcert hf hr R c t ht)
      (Q'.le_of_eqv (weighted_upper_moment n W f r c t)))

end YMGap.Continuum.QuaternionHaarRadialMeanYoung

#print axioms YMGap.Continuum.QuaternionHaarRadialMeanYoung.young_identity
#print axioms YMGap.Continuum.QuaternionHaarRadialMeanYoung.youngGapCertificate
#print axioms YMGap.Continuum.QuaternionHaarRadialMeanYoung.young_retained_identity
#print axioms YMGap.Continuum.QuaternionHaarRadialMeanYoung.youngRetainedCertificate
#print axioms YMGap.Continuum.QuaternionHaarRadialMeanYoung.weighted_young_retained
#print axioms YMGap.Continuum.QuaternionHaarRadialMeanYoung.weighted_young
#print axioms YMGap.Continuum.QuaternionHaarRadialMeanYoung.weighted_young_moments_retained
#print axioms YMGap.Continuum.QuaternionHaarRadialMeanYoung.weighted_young_moments
