/-
# Signed angular directions in the original product-heat kinetic form

Finite rational linear combinations of block-angular vector fields remain
skew for the actual product-map pairing.  Consequently their full second
directional response is the negative of the corresponding kinetic square.
No family-size estimate, diagonal truncation, or gap assertion is made.
-/

import YMGap.Continuum.SU2QuaternionProductHeatAngularForm

namespace YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionProductHeatAngularForm
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- One signed angular generator on an explicitly in-range quaternion block. -/
structure AngularTerm (n : Nat) where
  block : Fin n
  first : Fin 4
  second : Fin 4
  coefficient : Q'

def applyAngularTerm {n : Nat} (term : AngularTerm n) (p : RatPoly) : RatPoly :=
  polySmul term.coefficient
    (angularDerivative (4 * term.block.val + term.first.val)
      (4 * term.block.val + term.second.val) p)

/-- A concrete finite signed angular direction. -/
def signedAngularDirection {n : Nat} (terms : List (AngularTerm n))
    (p : RatPoly) : RatPoly := match terms with
  | [] => polyZero
  | term :: rest =>
      polyAdd (applyAngularTerm term p) (signedAngularDirection rest p)

theorem signedAngularDirection_supported {n : Nat} (terms : List (AngularTerm n))
    {p : RatPoly} (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (signedAngularDirection terms p) := by
  induction terms with
  | nil =>
      intro term hterm
      exact False.elim (List.not_mem_nil hterm)
  | cons term terms ih =>
      simp only [signedAngularDirection]
      exact supported_add
        (polySmul_supported
          (angularDerivative_supported_at (by omega) (by omega) hp)
          term.coefficient)
        ih

private theorem kineticPair_add_right (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (f g r : RatPoly) (hf : SupportedQuaternionBlocks n f)
    (hg : SupportedQuaternionBlocks n g) (hr : SupportedQuaternionBlocks n r) :
    kineticPair n w K ids f (polyAdd g r) ≈
      kineticPair n w K ids f g + kineticPair n w K ids f r := by
  exact Q'.eqv_trans _ _ _
    (kineticPair_symm n w K ids hids f (polyAdd g r) hf (supported_add hg hr))
    (Q'.eqv_trans _ _ _ (kineticPair_add_left n w K ids g r f)
      (Q'.add_eqv_congr'
        (kineticPair_symm n w K ids hids g f hg hf)
        (kineticPair_symm n w K ids hids r f hr hf)))

private theorem kineticPair_smul_right (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (c : Q') (f g : RatPoly) (hf : SupportedQuaternionBlocks n f)
    (hg : SupportedQuaternionBlocks n g) :
    kineticPair n w K ids f (polySmul c g) ≈
      c * kineticPair n w K ids f g := by
  exact Q'.eqv_trans _ _ _
    (kineticPair_symm n w K ids hids f (polySmul c g) hf
      (polySmul_supported hg c))
    (Q'.eqv_trans _ _ _ (kineticPair_smul_left n w K ids c g f)
      (Q'.mul_eqv_congr_left c _ _
        (kineticPair_symm n w K ids hids g f hg hf)))

/-- Every finite signed angular direction is skew for the unchanged original
product-map kinetic pairing. -/
theorem kineticPair_signedAngular_sum_zero
    (n : Nat) (terms : List (AngularTerm n)) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (f g : RatPoly) (hf : SupportedQuaternionBlocks n f)
    (hg : SupportedQuaternionBlocks n g) :
    kineticPair n w K ids (signedAngularDirection terms f) g +
      kineticPair n w K ids f (signedAngularDirection terms g) ≈ 0 := by
  induction terms with
  | nil =>
      simp only [signedAngularDirection]
      have hzleft (r : RatPoly) : kineticPair n w K ids polyZero r ≈ 0 :=
        Q'.eqv_trans _ _ _
          (haar_of_coeff (RatPolyCoeffEqv.mul_zero_left _)) (Q'.eqv_refl 0)
      have hzright : kineticPair n w K ids f polyZero ≈ 0 :=
        Q'.eqv_trans _ _ _
          (kineticPair_symm n w K ids hids f polyZero hf
            (fun _ h => False.elim (List.not_mem_nil h))) (hzleft f)
      exact Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr' (hzleft g) hzright) (QPoly.q_zero_add_eqv 0)
  | cons term terms ih =>
      simp only [signedAngularDirection]
      have hdg : SupportedQuaternionBlocks n
          (angularDerivative (4*term.block.val+term.first.val)
            (4*term.block.val+term.second.val) g) :=
        angularDerivative_supported_at (by omega) (by omega) hg
      have hterm := kineticPair_angular_sum_zero n term.block.val
        term.first.val term.second.val term.block.isLt term.first.isLt
        term.second.isLt w K ids hids f g hf hg
      have hscaled :
          kineticPair n w K ids (applyAngularTerm term f) g +
            kineticPair n w K ids f (applyAngularTerm term g) ≈ 0 :=
        Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (kineticPair_smul_left n w K ids term.coefficient _ _)
            (kineticPair_smul_right n w K ids hids term.coefficient f _ hf hdg))
          (Q'.eqv_trans _ (term.coefficient *
              (kineticPair n w K ids
                  (angularDerivative (4 * term.block.val + term.first.val)
                    (4 * term.block.val + term.second.val) f) g +
                kineticPair n w K ids f
                  (angularDerivative (4 * term.block.val + term.first.val)
                    (4 * term.block.val + term.second.val) g))) _
            (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))
            (Q'.eqv_trans _ (term.coefficient * 0) _
              (Q'.mul_eqv_congr_left _ _ _ hterm) (Q'.mul_zero_eqv _)))
      have hleft := kineticPair_add_left n w K ids
        (applyAngularTerm term f) (signedAngularDirection terms f) g
      have hright := kineticPair_add_right n w K ids hids f
        (applyAngularTerm term g) (signedAngularDirection terms g) hf
        (polySmul_supported hdg term.coefficient)
        (signedAngularDirection_supported terms hg)
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hleft hright) ?_
      refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
          (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
          (by decide)
          (fun k => match k with
            | 0 => kineticPair n w K ids (applyAngularTerm term f) g
            | 1 => kineticPair n w K ids (signedAngularDirection terms f) g
            | 2 => kineticPair n w K ids f (applyAngularTerm term g)
            | _ => kineticPair n w K ids f (signedAngularDirection terms g))) ?_
      exact Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr' hscaled ih) (QPoly.q_zero_add_eqv 0)

/-- The whole directional Hessian equals minus the full kinetic square, so
all mixed angular directions are retained. -/
theorem kineticPair_signedAngular_second_eq_neg_square
    (n : Nat) (terms : List (AngularTerm n)) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (a : RatPoly) (ha : SupportedQuaternionBlocks n a) :
    kineticPair n w K ids a
        (signedAngularDirection terms (signedAngularDirection terms a)) ≈
      -(kineticPair n w K ids (signedAngularDirection terms a)
        (signedAngularDirection terms a)) := by
  have hDa := signedAngularDirection_supported terms ha
  have hz := kineticPair_signedAngular_sum_zero n terms w K ids hids
    a (signedAngularDirection terms a) ha hDa
  apply QPoly.q_eqv_of_sub_zero
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
    (.add (.var 0) (.neg (.neg (.var 1)))) (.add (.var 1) (.var 0))
    (by decide)
    (fun k => if k = 0 then
      kineticPair n w K ids a
        (signedAngularDirection terms (signedAngularDirection terms a))
      else kineticPair n w K ids (signedAngularDirection terms a)
        (signedAngularDirection terms a))) hz

/-- At nonnegative heat parameter, the full signed angular second response is
nonpositive because it is the negative of the same-form kinetic square. -/
theorem kineticPair_signedAngular_second_nonpositive
    (n : Nat) (terms : List (AngularTerm n)) (w : Q') (hw : (0 : Q') ≤ w)
    (K : Nat) (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (a : RatPoly) (ha : SupportedQuaternionBlocks n a) :
    kineticPair n w K ids a
      (signedAngularDirection terms (signedAngularDirection terms a)) ≤ 0 := by
  have hDa := signedAngularDirection_supported terms ha
  have he := kineticPair_signedAngular_second_eq_neg_square
    n terms w K ids hids a ha
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.nonpos_neg_of_nonneg
      (kineticPair_nonnegative n w hw K ids hids _ hDa))

end YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse

#print axioms YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse.kineticPair_signedAngular_sum_zero
#print axioms YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse.signedAngularDirection_supported
#print axioms YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse.kineticPair_signedAngular_second_eq_neg_square
#print axioms YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse.kineticPair_signedAngular_second_nonpositive
