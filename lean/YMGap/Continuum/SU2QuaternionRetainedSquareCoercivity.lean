/-
# Complete the ORIGINAL gradient and retained slack together

Finite Haar IBP and the actual Casimir-twelve carrier pin produce a
division-free square identity for a*G-t*B. Both the square and the angular
Gram determinant remain explicit. The source can be signed and Q can be
zero. This is not an interacting-variance comparison or a scaling estimate.
-/

import YMGap.Continuum.SU2QuaternionSecondOrderRetainedSquare
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

namespace YMGap.Continuum.SU2QuaternionRetainedSquareCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionSecondOrderCancellation
open YMGap.Continuum.SU2QuaternionSecondOrderRetainedSquare
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem qmul {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a b c hab)
    (Q'.mul_eqv_congr_left b c d hcd)

private theorem support_smul {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (c : Q') :
    SupportedQuaternionBlocks n (polySmul c p) := by
  intro z hz
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
  exact hp r hr

private theorem haar_neg (n : Nat) (p : RatPoly) : H n (polyNeg p) ≈ -(H n p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (neg_smul p))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-1) p)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
        (.neg (.var 0)) (by decide) (fun _ => H n p)))

private theorem haar_two_square (n : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q)
    (a d : Q') :
    let s := polyAdd (polySmul a p) (polySmul d q)
    H n (polyMul s s) ≈ a*a*H n (polyMul p p) +
      2*a*d*H n (polyMul p q) + d*d*H n (polyMul q q) := by
  dsimp only
  let D := weightedGNSData n polyOne (Certificate.one n)
  have h := D.diag_expand a d ⟨p, hp⟩ ⟨q, hq⟩
  have hb (r s : RatPoly) : weightedPair n polyOne r s ≈ H n (polyMul r s) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_one _)
  have ht := Q'.eqv_trans _ _ _ h (Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (qmul (Q'.eqv_refl a) (qmul (Q'.eqv_refl a) (hb p p)))
      (qmul (Q'.eqv_refl a) (qmul (Q'.eqv_refl d) (hb p q))))
    (Q'.add_eqv_congr' (qmul (Q'.eqv_refl d) (qmul (Q'.eqv_refl a) (hb p q)))
      (qmul (Q'.eqv_refl d) (qmul (Q'.eqv_refl d) (hb q q)))))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hb _ _)) (Q'.eqv_trans _ _ _ ht
    (poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.mul (.var 0) (.var 2)))
        (.mul (.var 0) (.mul (.var 1) (.var 3))))
        (.add (.mul (.var 1) (.mul (.var 0) (.var 3)))
          (.mul (.var 1) (.mul (.var 1) (.var 4)))))
      (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
        (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 3)))
        (.mul (.mul (.var 1) (.var 1)) (.var 4))) (by decide)
      (fun
        | 0 => a
        | 1 => d
        | 2 => H n (polyMul p p)
        | 3 => H n (polyMul p q)
        | _ => H n (polyMul q q))))

/-- The literal existing commutator/Gram slack, with explicit active indices. -/
def retainedSlackValue (n : Nat) (active : List Nat) (b f : RatPoly) : Q' :=
  let comm := commutatorPolynomial active b f
  let v := polyMul b f
  H n (polyAdd
    (polyAdd (polyMul comm comm)
      (polySmul 2 (polyMul (activeGamma active b b) (activeGamma active f f))))
    (polySmul (-48) (polyMul v v)))

/-- The remaining complete square, not an absolute source-derivative bound. -/
def coercivitySquare (active : List Nat) (b f : RatPoly) (a t : Q') : RatPoly :=
  polyAdd (polySmul (a-24*t) (polyMul b f))
    (polySmul (6*t) (activeGamma active b f))

/-- The angular Gram determinant on the SAME source/observable coordinates. -/
def coercivityGram (active : List Nat) (b f : RatPoly) : RatPoly :=
  polyAdd (polyMul (activeGamma active b b) (activeGamma active f f))
    (polyNeg (polyMul (activeGamma active b f) (activeGamma active b f)))

/-- Two product rules in the actual finite Haar IBP; no mixed moment assumed. -/
theorem casimir12_mixed_ibp (n : Nat) (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) (b f : RatPoly)
    (hCf : HaarCarrierEqv n (activeCasimirPolynomial active f) (polySmul 12 f)) :
    H n (polyMul (polyMul b b) (activeGamma active f f)) +
      2*H n (polyMul (polyMul b f) (activeGamma active b f)) ≈
      12*H n (polyMul (polyMul b f) (polyMul b f)) := by
  let test := polyMul (polyMul b b) f
  let x := activeGamma active b f
  let g := activeGamma active f f
  have hs := activeGamma_symm active f b
  have hsquare := (activeGamma_mul_right active f b b).trans
    ((hs.mul_right b).add (hs.mul_left b))
  have hprod := (activeGamma_symm active test f).trans
    ((activeGamma_mul_right active f (polyMul b b) f).trans
      ((hsquare.mul_right f).add (RatPolyCoeffEqv.refl _)))
  have hr : RatPolyCoeffEqv
      (polyAdd (polyMul (polyAdd (polyMul x b) (polyMul b x)) f)
        (polyMul (polyMul b b) g))
      (polyAdd (polyMul (polyMul b b) g) (polySmul 2 (polyMul (polyMul b f) x))) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.add (.mul (.var 2) (.var 0)) (.mul (.var 0) (.var 2))) (.var 1))
        (.mul (.mul (.var 0) (.var 0)) (.var 3)))
      (.add (.mul (.mul (.var 0) (.var 0)) (.var 3))
        (.mul (.const 2) (.mul (.mul (.var 0) (.var 1)) (.var 2))))
      (by decide) (fun | 0 => b | 1 => f | 2 => x | _ => g)).trans
        ((RatPolyCoeffEqv.refl _).add (cap_mul_left 2 _))
  have hright := Q'.eqv_trans _ _ _ (haar_of_coeff (hprod.trans hr))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (quaternionHaar_polySmul n 2 _)))
  have hnorm : RatPolyCoeffEqv (polyMul test f)
      (polyMul (polyMul b f) (polyMul b f)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => b | _ => f)
  have hleft := Q'.eqv_trans _ _ _ (hCf test)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right 12 test f))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n 12 _)
        (Q'.mul_eqv_congr_left 12 _ _ (haar_of_coeff hnorm))))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hright)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (casimir_pair_gamma n active hactive test f)) hleft)

private theorem slack_expansion (n : Nat) (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) (b f : RatPoly)
    (hb : SupportedQuaternionBlocks n b) (hf : SupportedQuaternionBlocks n f)
    (hCf : HaarCarrierEqv n (activeCasimirPolynomial active f) (polySmul 12 f)) :
    retainedSlackValue n active b f ≈
      96*H n (polyMul (polyMul b f) (polyMul b f)) -
      48*H n (polyMul (polyMul b f) (activeGamma active b f)) +
      4*H n (polyMul (activeGamma active b f) (activeGamma active b f)) +
      2*H n (polyMul (activeGamma active b b) (activeGamma active f f)) := by
  let v := polyMul b f
  let x := activeGamma active b f
  let s := polyAdd (polySmul 12 v) (polySmul (-2) x)
  have hcomm : HaarCarrierEqv n (commutatorPolynomial active b f) s :=
    (HaarCarrierEqv.add (HaarCarrierEqv.mul_left b hCf) (HaarCarrierEqv.refl n _)).trans
      (RatPolyCoeffEqv.haarCarrier
        ((RatPolyCoeffEqv.polyMul_smul_right 12 b f).add (RatPolyCoeffEqv.refl _)))
  have hc := haar_of_carrier (HaarCarrierEqv.mul hcomm hcomm)
  have he := haar_two_square n v x (supported_polyMul hb hf)
    (activeGamma_supported active hactive hb hf) 12 (-2)
  have ht : retainedSlackValue n active b f ≈
      ((12*12*H n (polyMul v v)+2*12*(-2)*H n (polyMul v x)+
        (-2)*(-2)*H n (polyMul x x))+
        2*H n (polyMul (activeGamma active b b) (activeGamma active f f)))+
        (-48)*H n (polyMul v v) :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
        (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ hc he) (quaternionHaar_polySmul n 2 _)))
      (quaternionHaar_polySmul n (-48) _))
  exact Q'.eqv_trans _ _ _ ht (poly_identity_of_normal_eq
    (.add (.add (.add (.add (.mul (.mul (.const 12) (.const 12)) (.var 0))
      (.mul (.mul (.mul (.const 2) (.const 12)) (.const (-2))) (.var 1)))
      (.mul (.mul (.const (-2)) (.const (-2))) (.var 2)))
      (.mul (.const 2) (.var 3))) (.mul (.const (-48)) (.var 0)))
    (.add (.add (.add (.mul (.const 96) (.var 0))
      (.neg (.mul (.const 48) (.var 1)))) (.mul (.const 4) (.var 2)))
      (.mul (.const 2) (.var 3))) (by decide)
    (fun
      | 0 => H n (polyMul v v)
      | 1 => H n (polyMul v x)
      | 2 => H n (polyMul x x)
      | _ => H n (polyMul (activeGamma active b b) (activeGamma active f f))))

private theorem scalar_square_identity (a t Q J X Y : Q') :
    (a*a+24*a*t)*Q-6*t*(a*(12*Q-2*J)-t*(96*Q-48*J+4*X+2*Y)) ≈
      ((a-24*t)*(a-24*t)*Q+2*(a-24*t)*(6*t)*J+(6*t)*(6*t)*X)+12*t*t*(Y-X) := by
  let A : PolyExpr := .var 0
  let T : PolyExpr := .var 1
  let Qe : PolyExpr := .var 2
  let Je : PolyExpr := .var 3
  let Xe : PolyExpr := .var 4
  let Ye : PolyExpr := .var 5
  let G : PolyExpr := .add (.mul (.const 12) Qe) (.neg (.mul (.const 2) Je))
  let B : PolyExpr := .add (.add (.add (.mul (.const 96) Qe)
    (.neg (.mul (.const 48) Je))) (.mul (.const 4) Xe)) (.mul (.const 2) Ye)
  let S : PolyExpr := .add A (.neg (.mul (.const 24) T))
  let R : PolyExpr := .mul (.const 6) T
  exact poly_identity_of_normal_eq
    (.add (.mul (.add (.mul A A) (.mul (.mul (.const 24) A) T)) Qe)
      (.neg (.mul (.mul (.const 6) T) (.add (.mul A G) (.neg (.mul T B))))))
    (.add (.add (.add (.mul (.mul S S) Qe) (.mul (.mul (.mul (.const 2) S) R) Je))
      (.mul (.mul R R) Xe)) (.mul (.mul (.mul (.const 12) T) T) (.add Ye (.neg Xe))))
    (by decide) (fun | 0 => a | 1 => t | 2 => Q | 3 => J | 4 => X | _ => Y)

/-- Exact cleared square identity for EVERY rational a,t, including t=0/Q=0. -/
theorem retained_coercivity_identity (n : Nat) (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) (b f : RatPoly)
    (hb : SupportedQuaternionBlocks n b) (hf : SupportedQuaternionBlocks n f)
    (hCf : HaarCarrierEqv n (activeCasimirPolynomial active f) (polySmul 12 f))
    (a t : Q') :
    (a*a+24*a*t)*H n (polyMul (polyMul b f) (polyMul b f)) -
      6*t*(a*H n (polyMul (polyMul b b) (activeGamma active f f))-
        t*retainedSlackValue n active b f) ≈
      H n (polyMul (coercivitySquare active b f a t) (coercivitySquare active b f a t))+
        12*t*t*H n (coercivityGram active b f) := by
  let Q := H n (polyMul (polyMul b f) (polyMul b f))
  let J := H n (polyMul (polyMul b f) (activeGamma active b f))
  let X := H n (polyMul (activeGamma active b f) (activeGamma active b f))
  let Y := H n (polyMul (activeGamma active b b) (activeGamma active f f))
  let G := H n (polyMul (polyMul b b) (activeGamma active f f))
  have hibp := casimir12_mixed_ibp n active hactive b f hCf
  have hg : G ≈ 12*Q-2*J := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.var 0)
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (by decide)
      (fun | 0 => G | _ => 2*J))
    (Q'.add_eqv_congr' hibp (Q'.eqv_refl _))
  have he := haar_two_square n (polyMul b f) (activeGamma active b f)
    (supported_polyMul hb hf) (activeGamma_supported active hactive hb hf) (a-24*t) (6*t)
  have hd : H n (coercivityGram active b f) ≈ Y-X :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _) (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (haar_neg n _))
  have ht := Q'.add_eqv_congr' (Q'.eqv_refl ((a*a+24*a*t)*Q))
    (Q'.neg_eqv_congr _ _ (qmul (Q'.eqv_refl (6*t))
      (Q'.add_eqv_congr' (qmul (Q'.eqv_refl a) hg)
        (Q'.neg_eqv_congr _ _ (qmul (Q'.eqv_refl t) (slack_expansion n active hactive b f hb hf hCf))))))
  exact Q'.eqv_trans _ _ _ ht (Q'.eqv_trans _ _ _ (scalar_square_identity a t Q J X Y)
    (Q'.add_eqv_congr' (Q'.eqv_symm he) (qmul (Q'.eqv_refl (12*t*t)) (Q'.eqv_symm hd))))

/-- The complete square has a produced support proof and nonnegative Haar. -/
theorem coercivitySquare_haar_nonnegative (n : Nat) (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) (b f : RatPoly)
    (hb : SupportedQuaternionBlocks n b) (hf : SupportedQuaternionBlocks n f) (a t : Q') :
    (0 : Q') ≤ H n (polyMul (coercivitySquare active b f a t) (coercivitySquare active b f a t)) :=
  quaternionHaar_square_nonnegative n _
    (supported_add (support_smul (supported_polyMul hb hf) (a-24*t))
      (support_smul (activeGamma_supported active hactive hb hf) (6*t)))

/-- The determinant is certified on the SAME angular coordinates. -/
theorem coercivityGram_nonnegative (n : Nat) (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) (b f : RatPoly)
    (hb : SupportedQuaternionBlocks n b) (hf : SupportedQuaternionBlocks n f) :
    (0 : Q') ≤ H n (coercivityGram active b f) :=
  (angularGramCertificate active hactive hb hf).haar_nonnegative

/-- Upper energy direction, cleared of EVERY source/observable inverse. -/
theorem retained_square_coercivity (n : Nat) (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) (b f : RatPoly)
    (hb : SupportedQuaternionBlocks n b) (hf : SupportedQuaternionBlocks n f)
    (hCf : HaarCarrierEqv n (activeCasimirPolynomial active f) (polySmul 12 f)) (a t : Q') :
    6*t*(a*H n (polyMul (polyMul b b) (activeGamma active f f))-
      t*retainedSlackValue n active b f) ≤
      (a*a+24*a*t)*H n (polyMul (polyMul b f) (polyMul b f)) := by
  let L := 6*t*(a*H n (polyMul (polyMul b b) (activeGamma active f f))-
    t*retainedSlackValue n active b f)
  let R := (a*a+24*a*t)*H n (polyMul (polyMul b f) (polyMul b f))
  have hc : (0 : Q') ≤ 12*t*t := Q'.le_trans' _ _ _
    (Q'.mul_nonneg 12 (t*t) (by decide) (SumOfSquares.q_mul_self_nonneg t))
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv 12 t t)))
  have hz : (0 : Q') ≤ R-L := Q'.le_trans' _ _ _
    (Q'.zero_le_add _ _ (coercivitySquare_haar_nonnegative n active hactive b f hb hf a t)
      (Q'.mul_nonneg _ _ hc (coercivityGram_nonnegative n active hactive b f hb hf)))
    (Q'.ge_of_eqv (retained_coercivity_identity n active hactive b f hb hf hCf a t))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.var 0) (.add (.var 0) (.const 0)) (by decide) (fun _ => L)))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left L 0 (R-L) hz)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.var 0) (.add (.var 1) (.neg (.var 0)))) (.var 1) (by decide)
        (fun | 0 => L | _ => R))))

#print axioms retainedSlackValue
#print axioms coercivitySquare
#print axioms coercivityGram
#print axioms casimir12_mixed_ibp
#print axioms retained_coercivity_identity
#print axioms coercivitySquare_haar_nonnegative
#print axioms coercivityGram_nonnegative
#print axioms retained_square_coercivity

end YMGap.Continuum.SU2QuaternionRetainedSquareCoercivity
