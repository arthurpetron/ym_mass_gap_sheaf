/-
# Complementary omitted form on the ORIGINAL finite polynomial carrier

The existing omitted diagonal cap constructs the positive form
`D = omittedRate * Haar - pairOmitted`. Its Cauchy inequality and a supplied
polynomial square certificate give a homogeneous, one-sided source bound.
The source may be signed or projected; no comparison through a projection,
source positivity, inverse normalizer, or continuous Haar is used. This is
only the omitted part of the original signed debt, not a survival estimate.
-/

import YMGap.Continuum.SU2QuaternionCyclicOmittedOperator
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.SU2QuaternionCyclicComplementaryOmitted

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder
open YMGap.Continuum.SU2QuaternionCyclicOmittedNorm
open YMGap.Continuum.SU2QuaternionCyclicOmittedOperator
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.GNSQuotient

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

def complementaryOmitted (tail : Nat) (w : Q') (K : Nat) (p test : RatPoly) : Q' :=
  omittedRate w K * H (tail+1) (polyMul test p) - pairOmitted tail w K p test

private theorem sub_add (a b c d : Q') :
    (a+b)-(c+d) ≈ (a-c)+(b-d) :=
  poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
    (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3))))
    (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)

private theorem sub_smul (r a b : Q') : r*a-r*b ≈ r*(a-b) :=
  poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
    (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
    (by decide) (fun | 0 => r | 1 => a | _ => b)

private theorem sub_restore (a b : Q') : (a-b)+b ≈ a :=
  poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
    (by decide) (fun | 0 => a | _ => b)

theorem complementaryOmitted_diagonal_nonnegative (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    (0 : Q') ≤ complementaryOmitted tail w K p p :=
  Q'.sub_nonneg_of_le (pairOmitted_diagonal_le_haar tail hw0 hw1 K p hp)

theorem complementaryOmitted_diagonal_le_haar (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    complementaryOmitted tail w K p p ≤ omittedRate w K * H (tail+1) (polyMul p p) :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (pairOmitted_diagonal_nonnegative tail hw0 K p hp))
    (Q'.le_of_eqv (sub_restore _ _))

private theorem test_congr (tail : Nat) (w : Q') (K : Nat) (p : RatPoly)
    {a b : RatPoly} (h : RatPolyCoeffEqv a b) :
    complementaryOmitted tail w K p a ≈ complementaryOmitted tail w K p b :=
  Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left (omittedRate w K) _ _ (haar_of_coeff (h.mul_right p)))
    (Q'.neg_eqv_congr _ _ (pairOmitted_test_congr tail w K p h))

private theorem test_add (tail : Nat) (w : Q') (K : Nat) (p a b : RatPoly) :
    complementaryOmitted tail w K p (polyAdd a b) ≈
      complementaryOmitted tail w K p a + complementaryOmitted tail w K p b := by
  have hh : H (tail+1) (polyMul (polyAdd a b) p) ≈
      H (tail+1) (polyMul a p)+H (tail+1) (polyMul b p) := by
    rw [polyMul_add_left_exact]
    exact quaternionHaar_append _ _ _
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (omittedRate w K) _ _ hh) (Q'.mul_add_eqv _ _ _))
      (Q'.neg_eqv_congr _ _ (pairOmitted_test_add tail w K p a b)))
    (sub_add _ _ _ _)

private theorem test_smul (tail : Nat) (w : Q') (K : Nat) (c : Q') (p a : RatPoly) :
    complementaryOmitted tail w K p (polySmul c a) ≈ c*complementaryOmitted tail w K p a := by
  have hh := Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c a p))
    (quaternionHaar_polySmul (tail+1) c (polyMul a p))
  have hc : omittedRate w K*(c*H (tail+1) (polyMul a p)) ≈
      c*(omittedRate w K*H (tail+1) (polyMul a p)) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => omittedRate w K | 1 => c | _ => H (tail+1) (polyMul a p))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (omittedRate w K) _ _ hh) hc)
      (Q'.neg_eqv_congr _ _ (pairOmitted_test_smul tail w K c p a)))
    (sub_smul _ _ _)

private theorem complementary_symm (tail : Nat) (w : Q') (K : Nat) (p a : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (ha : SupportedQuaternionBlocks (tail+1) a) :
    complementaryOmitted tail w K p a ≈ complementaryOmitted tail w K a p :=
  Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left (omittedRate w K) _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm a p)))
    (Q'.neg_eqv_congr _ _ (pairOmitted_symm tail w K p a hp ha))

/-- A constructed finite form: the old supported-polynomial carrier is retained. -/
def complementaryGNSData (tail : Nat) (w : Q') (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ 1) (K : Nat) : GNSData :=
  { omittedGNSData tail w hw0 K with
    B := fun p q => complementaryOmitted tail w K q.val p.val
    B_congr_left := fun q h => test_congr tail w K q.val h
    B_add_left := fun p q r => test_add tail w K r.val p.val q.val
    B_smul_left := fun c p q => test_smul tail w K c q.val p.val
    B_symm := fun p q => complementary_symm tail w K q.val p.val q.property p.property
    self_nonneg := fun p => complementaryOmitted_diagonal_nonnegative tail hw0 hw1 K p.val p.property }

theorem complementaryOmitted_cauchySchwarz (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (K : Nat) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (ht : SupportedQuaternionBlocks (tail+1) test) :
    complementaryOmitted tail w K p test*complementaryOmitted tail w K p test ≤
      complementaryOmitted tail w K p p*complementaryOmitted tail w K test test :=
  Q'.le_trans' _ _ _
    ((complementaryGNSData tail w hw0 hw1 K).cauchy_schwarz ⟨test,ht⟩ ⟨p,hp⟩)
    (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))

theorem complementaryOmitted_square_le_haar (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (K : Nat) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (ht : SupportedQuaternionBlocks (tail+1) test) :
    complementaryOmitted tail w K p test*complementaryOmitted tail w K p test ≤
      (omittedRate w K*omittedRate w K)*
        (H (tail+1) (polyMul p p)*H (tail+1) (polyMul test test)) := by
  have htt := complementaryOmitted_diagonal_nonnegative tail hw0 hw1 K test ht
  have hpp := complementaryOmitted_diagonal_nonnegative tail hw0 hw1 K p hp
  have hup := complementaryOmitted_diagonal_le_haar tail hw0 K p hp
  have hut := complementaryOmitted_diagonal_le_haar tail hw0 K test ht
  have hprod := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hup htt)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hut (Q'.le_trans' _ _ _ hpp hup))
  exact Q'.le_trans' _ _ _ (complementaryOmitted_cauchySchwarz tail hw0 hw1 K p test hp ht)
    (Q'.le_trans' _ _ _ hprod (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2))) (by decide)
        (fun
          | 0 => omittedRate w K
          | 1 => H (tail+1) (polyMul p p)
          | _ => H (tail+1) (polyMul test test)))))

private theorem square_order {x y : Q'} (hy : (0 : Q') ≤ y) (h : x*x ≤ y*y) : x ≤ y := by
  show x.num*(y.den : Int) ≤ y.num*(x.den : Int)
  apply Int.not_lt.mp
  intro hlt
  have hn : (0 : Int) ≤ y.num*(x.den : Int) :=
    Int.mul_nonneg ((Q'.zero_le_iff_num_nonneg y).mp hy) (Int.natCast_nonneg _)
  have hs := Int.mul_self_lt_mul_self hn hlt
  change (x.num*x.num)*((y*y).den : Int) ≤ (y.num*y.num)*((x*x).den : Int) at h
  rw [Q'.mul_den_cast, Q'.mul_den_cast] at h
  have pull (a b : Int) : (a*a)*(b*b) = (a*b)*(a*b) := by
    simp only [Int.mul_left_comm, Int.mul_comm]
  rw [pull, pull] at h
  exact (Int.not_le.mpr hs) h

private theorem multiplier_fourth_le {blocks : Nat} {q f : RatPoly} {M : Q'}
    (hq : SupportedQuaternionBlocks blocks q) (P : SquareBound blocks f M) :
    H blocks (polyMul (polyMul q (polyMul f f)) (polyMul q (polyMul f f))) ≤
      (M*M)*H blocks (polyMul q q) := by
  let a := polyMul f f
  let E := polyMul (polyMul q q) (gap (M*M) a)
  have hn : (0 : Q') ≤ H blocks E :=
    ((Certificate.square q hq).mul (P.mul P).certificate).haar_nonnegative
  have hid : RatPolyCoeffEqv
      (polyAdd (polyMul (polyMul q a) (polyMul q a)) E)
      (polyMul (cap (M*M)) (polyMul q q)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.var 0) (.var 0)) (.add (.var 2) (.neg (.mul (.var 1) (.var 1))))))
      (.mul (.var 2) (.mul (.var 0) (.var 0))) (by decide)
      (fun | 0 => q | 1 => a | _ => cap (M*M))
  have he := Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _).symm
    (Q'.eqv_trans _ _ _ (haar_of_coeff (hid.trans (cap_mul_left _ _)))
      (quaternionHaar_polySmul blocks (M*M) (polyMul q q)))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn) (Q'.le_of_eqv he)

/-- Matching ORIGINAL Haar terms cancel before bounding either omitted pairing. -/
theorem sourceOmitted_complementary (tail : Nat) (w : Q') (K : Nat) (q f : RatPoly) :
    -(sourceOmitted tail w K q f) ≈
      complementaryOmitted tail w K q (polyMul q (polyMul f f)) -
        complementaryOmitted tail w K (polyMul q f) (polyMul q f) := by
  have hh : H (tail+1) (polyMul (polyMul q (polyMul f f)) q) ≈
      H (tail+1) (polyMul (polyMul q f) (polyMul q f)) :=
    haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 0))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => q | _ => f))
  have hc : -(sourceOmitted tail w K q f) ≈
      (omittedRate w K*H (tail+1) (polyMul (polyMul q f) (polyMul q f)) -
        pairOmitted tail w K q (polyMul q (polyMul f f))) -
      complementaryOmitted tail w K (polyMul q f) (polyMul q f) :=
    poly_identity_of_normal_eq (.neg (.add (.var 1) (.neg (.var 2))))
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 0) (.neg (.var 2)))))
      (by decide) (fun
        | 0 => omittedRate w K*H (tail+1) (polyMul (polyMul q f) (polyMul q f))
        | 1 => pairOmitted tail w K q (polyMul q (polyMul f f))
        | _ => pairOmitted tail w K (polyMul q f) (polyMul q f))
  exact Q'.eqv_trans _ _ _ hc (Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left (omittedRate w K) _ _ hh.symm) (Q'.eqv_refl _))
    (Q'.eqv_refl _))

/-- Homogeneous one-sided omitted debt cap. Zero caps and signed sources are allowed. -/
theorem neg_sourceOmitted_le_squareBound (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (K : Nat) (q f : RatPoly) {M : Q'}
    (hq : SupportedQuaternionBlocks (tail+1) q) (P : SquareBound (tail+1) f M) :
    -(sourceOmitted tail w K q f) ≤ M*omittedRate w K*H (tail+1) (polyMul q q) := by
  let a := polyMul q (polyMul f f)
  let d := complementaryOmitted tail w K q a
  let U := H (tail+1) (polyMul q q)
  let r := omittedRate w K
  have ha : SupportedQuaternionBlocks (tail+1) a := supported_polyMul hq (supported_polyMul P.support P.support)
  have hU : (0 : Q') ≤ U := (Certificate.square q hq).haar_nonnegative
  have hr : (0 : Q') ≤ r := RGTransport.qpow_nonneg w hw0 _
  have hs := complementaryOmitted_square_le_haar tail hw0 hw1 K q a hq ha
  have hcap := Q'.mul_le_mul_of_nonneg_left _ _ (r*r)
    (Q'.mul_le_mul_of_nonneg_left _ _ U (multiplier_fourth_le hq P) hU)
    (Q'.mul_nonneg _ _ hr hr)
  have he : (r*r)*(U*((M*M)*U)) ≈ (M*r*U)*(M*r*U) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 1))))
      (.mul (.mul (.mul (.var 2) (.var 0)) (.var 1)) (.mul (.mul (.var 2) (.var 0)) (.var 1)))
      (by decide) (fun | 0 => r | 1 => U | _ => M)
  have hd : d ≤ M*r*U := square_order
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ P.nonnegative hr) hU)
    (Q'.le_trans' _ _ _ hs (Q'.le_trans' _ _ _ hcap (Q'.le_of_eqv he)))
  have hdiag := complementaryOmitted_diagonal_nonnegative tail hw0 hw1 K (polyMul q f)
    (supported_polyMul hq P.support)
  have hdrop : d-complementaryOmitted tail w K (polyMul q f) (polyMul q f) ≤ d :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hdiag) (Q'.le_of_eqv (sub_restore _ _))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (sourceOmitted_complementary tail w K q f))
    (Q'.le_trans' _ _ _ hdrop hd)

end YMGap.Continuum.SU2QuaternionCyclicComplementaryOmitted

#print axioms YMGap.Continuum.SU2QuaternionCyclicComplementaryOmitted.complementaryOmitted
#print axioms YMGap.Continuum.SU2QuaternionCyclicComplementaryOmitted.complementaryOmitted_diagonal_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionCyclicComplementaryOmitted.complementaryOmitted_diagonal_le_haar
#print axioms YMGap.Continuum.SU2QuaternionCyclicComplementaryOmitted.complementaryGNSData
#print axioms YMGap.Continuum.SU2QuaternionCyclicComplementaryOmitted.complementaryOmitted_cauchySchwarz
#print axioms YMGap.Continuum.SU2QuaternionCyclicComplementaryOmitted.complementaryOmitted_square_le_haar
#print axioms YMGap.Continuum.SU2QuaternionCyclicComplementaryOmitted.sourceOmitted_complementary
#print axioms YMGap.Continuum.SU2QuaternionCyclicComplementaryOmitted.neg_sourceOmitted_le_squareBound
