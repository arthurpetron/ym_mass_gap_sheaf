/-
# Changed-factor comparison for finite quaternion Haar products

All positivity below is carried by square certificates on the original
polynomial Haar carrier. The telescoping identity permits overlapping
coordinates; unchanged factors are charged no scalar loss. This file does
not assert a comparison for a Wilson measure or a replica swap by itself.
-/

import YMGap.Constructive.Geometric
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound
import YMGap.Continuum.SU2QuaternionFactorizedHaarContraction

namespace YMGap.Continuum.QuaternionHaarChangedProductComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound

private theorem cancel_coeff (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd p (polyNeg p)) (cap 0) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide)
    (fun _ => p)

/-- A zero difference has a constructive certificate, including after
replacement by an equal polynomial under every supported Haar insertion. -/
def unchanged_gap {n : Nat} {p q : RatPoly}
    (h : HaarCarrierEqv n p q) :
    Certificate n (polyAdd q (polyNeg p)) := by
  have hcarrier : HaarCarrierEqv n (polyAdd q (polyNeg p)) (cap 0) :=
    (HaarCarrierEqv.add h.symm (HaarCarrierEqv.refl n (polyNeg p))).trans
      (RatPolyCoeffEqv.haarCarrier (cancel_coeff p))
  exact .transport hcarrier (.constant n 0 (by decide))

/-- Exact two-factor telescoping, proved in the rational polynomial ring. -/
private theorem two_factor_difference_coeff (upper upperTail lower lowerTail : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyMul upper upperTail)
        (polyNeg (polyMul lower lowerTail)))
      (polyAdd
        (polyMul (polyAdd upper (polyNeg lower)) upperTail)
        (polyMul lower (polyAdd upperTail (polyNeg lowerTail)))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3))))
    (.add (.mul (.add (.var 0) (.neg (.var 2))) (.var 1))
      (.mul (.var 2) (.add (.var 1) (.neg (.var 3)))))
    (by decide)
    (fun | 0 => upper | 1 => upperTail | 2 => lower | _ => lowerTail)

/-- Difference of two products, with the nonnegative factors retained in
each telescoping term. No independence or disjoint-support premise occurs. -/
def two_factor_gap {n : Nat} {lower upper lowerTail upperTail : RatPoly}
    (gap : Certificate n (polyAdd upper (polyNeg lower)))
    (upperTailCert : Certificate n upperTail)
    (lowerCert : Certificate n lower)
    (tailGap : Certificate n (polyAdd upperTail (polyNeg lowerTail))) :
    Certificate n
      (polyAdd (polyMul upper upperTail)
        (polyNeg (polyMul lower lowerTail))) :=
  .ofCoeff (two_factor_difference_coeff upper upperTail lower lowerTail)
    ((gap.mul upperTailCert).add (lowerCert.mul tailGap))

/-- An explicitly supplied certificate for every factor compiles into one
for the entire finite product. -/
def product_certificate {n : Nat} {Index : Type} (ids : List Index)
    (factor : Index → RatPoly)
    (cert : ∀ i : Index, Certificate n (factor i)) :
    Certificate n (factorProduct (ids.map factor)) :=
  match ids with
  | [] => .one n
  | i :: rest => (cert i).mul (product_certificate rest factor cert)

/-- A factorwise changed-product comparison compiles into a product
comparison on the same original Haar carrier. -/
def product_gap_certificate {n : Nat} {Index : Type} (ids : List Index)
    (lower upper : Index → RatPoly)
    (lowerCert : ∀ i : Index, Certificate n (lower i))
    (upperCert : ∀ i : Index, Certificate n (upper i))
    (gap : ∀ i : Index, Certificate n (polyAdd (upper i) (polyNeg (lower i)))) :
    Certificate n
      (polyAdd (factorProduct (ids.map upper))
        (polyNeg (factorProduct (ids.map lower)))) :=
  match ids with
  | [] => .ofCoeff (cancel_coeff polyOne) (.constant n 0 (by decide))
  | i :: rest =>
      two_factor_gap (gap i)
        (product_certificate rest upper upperCert) (lowerCert i)
        (product_gap_certificate rest lower upper lowerCert upperCert gap)

def changedCount {Index : Type} (mask : Index → Bool) : List Index → Nat
  | [] => 0
  | i :: rest => if mask i then changedCount mask rest + 1 else changedCount mask rest

theorem changedCount_eq_filter_length {Index : Type} (mask : Index → Bool)
    (ids : List Index) : changedCount mask ids = (ids.filter mask).length := by
  induction ids with
  | nil => rfl
  | cons i rest ih =>
      cases h : mask i <;> simp [changedCount, h, ih]

private def maskedFactor {Index : Type} (c : Q') (mask : Index → Bool)
    (factor : Index → RatPoly) (i : Index) : RatPoly :=
  if mask i then polySmul c (factor i) else factor i

/-- Multiplying a scalar only on changed factors is coefficientwise the
same as one scalar power outside the unmodified product. -/
theorem masked_product_coeff {Index : Type} (c : Q') (mask : Index → Bool)
    (factor : Index → RatPoly) (ids : List Index) :
    RatPolyCoeffEqv
      (factorProduct (ids.map (maskedFactor c mask factor)))
      (polySmul (c ^ changedCount mask ids) (factorProduct (ids.map factor))) := by
  induction ids with
  | nil =>
      change RatPolyCoeffEqv polyOne (polySmul (c ^ 0) polyOne)
      rw [Q'.pow_zero]
      exact (RatPolyCoeffEqv.one_smul polyOne).symm
  | cons i rest ih =>
      cases h : mask i with
      | false =>
          have hchain :=
            (RatPolyCoeffEqv.mul (RatPolyCoeffEqv.refl (factor i)) ih).trans
              (RatPolyCoeffEqv.polyMul_smul_right _ _ _)
          simpa only [List.map_cons, factorProduct, maskedFactor,
            changedCount, h, ↓reduceIte] using hchain
      | true =>
          have hchain : RatPolyCoeffEqv
              (polyMul (polySmul c (factor i))
                (factorProduct (rest.map (maskedFactor c mask factor))))
              (polySmul (c * c ^ changedCount mask rest)
                (polyMul (factor i) (factorProduct (rest.map factor)))) :=
            (RatPolyCoeffEqv.mul (RatPolyCoeffEqv.refl _) ih).trans
              ((RatPolyCoeffEqv.polyMul_smul_left _ _ _).trans
                (((RatPolyCoeffEqv.polyMul_smul_right _ _ _).smul c).trans
                  (RatPolyCoeffEqv.smul_assoc _ _ _)))
          simpa only [List.map_cons, factorProduct, maskedFactor,
            changedCount, h, ↓reduceIte, Q'.pow_succ] using hchain

/-- The scalar-on-a-factor notation used by local action bounds is
coefficientwise the same as polynomial scalar multiplication. -/
def cap_gap_to_smul {n : Nat} {p q : RatPoly} (lowerScale upperScale : Q')
    (gap : Certificate n
      (polyAdd (polyMul (cap upperScale) q)
        (polyNeg (polyMul (cap lowerScale) p)))) :
    Certificate n
      (polyAdd (polySmul upperScale q)
        (polyNeg (polySmul lowerScale p))) :=
  .ofCoeff
    (RatPolyCoeffEqv.add
      (cap_mul_left upperScale q).symm
      (RatPolyCoeffEqv.neg (cap_mul_left lowerScale p).symm)) gap

/-- The mask incurs precisely one factor of `upperScale` and `lowerScale`
per changed index. Unchanged factors require only carrier equality, and
are charged no scalar loss. The output remains a constructive certificate
under every supported Haar insertion. -/
def masked_product_gap_certificate {n : Nat} {Index : Type}
    (ids : List Index) (mask : Index → Bool) (p q : Index → RatPoly)
    (lowerScale upperScale : Q')
    (hLower : (0 : Q') ≤ lowerScale) (hUpper : (0 : Q') ≤ upperScale)
    (P : ∀ i : Index, Certificate n (p i))
    (Q : ∀ i : Index, Certificate n (q i))
    (changed : ∀ i : Index, mask i = true →
      Certificate n
        (polyAdd (polySmul upperScale (q i))
          (polyNeg (polySmul lowerScale (p i)))))
    (unchanged : ∀ i : Index, mask i = false → HaarCarrierEqv n (p i) (q i)) :
    Certificate n
      (polyAdd
        (polySmul (upperScale ^ changedCount mask ids)
          (factorProduct (ids.map q)))
        (polyNeg (polySmul (lowerScale ^ changedCount mask ids)
          (factorProduct (ids.map p))))) := by
  let lower : Index → RatPoly := maskedFactor lowerScale mask p
  let upper : Index → RatPoly := maskedFactor upperScale mask q
  have hP (i : Index) : Certificate n (lower i) := by
    cases h : mask i with
    | false => simpa [lower, maskedFactor, h] using P i
    | true => simpa [lower, maskedFactor, h] using
        (Certificate.smul lowerScale hLower (P i))
  have hQ (i : Index) : Certificate n (upper i) := by
    cases h : mask i with
    | false => simpa [upper, maskedFactor, h] using Q i
    | true => simpa [upper, maskedFactor, h] using
        (Certificate.smul upperScale hUpper (Q i))
  have hGap (i : Index) : Certificate n (polyAdd (upper i) (polyNeg (lower i))) := by
    cases h : mask i with
    | false => simpa [upper, lower, maskedFactor, h] using
        (unchanged_gap (unchanged i h))
    | true => simpa [upper, lower, maskedFactor, h] using changed i h
  have hProduct := product_gap_certificate ids lower upper hP hQ hGap
  have hUpperCoeff := masked_product_coeff upperScale mask q ids
  have hLowerCoeff := masked_product_coeff lowerScale mask p ids
  exact .ofCoeff
    (RatPolyCoeffEqv.add hUpperCoeff.symm (RatPolyCoeffEqv.neg hLowerCoeff.symm))
    hProduct

/-- Form of the masked comparison accepting the local certificates exactly
as `cap upperScale * q - cap lowerScale * p`. -/
def masked_product_gap_certificate_cap {n : Nat} {Index : Type}
    (ids : List Index) (mask : Index → Bool) (p q : Index → RatPoly)
    (lowerScale upperScale : Q')
    (hLower : (0 : Q') ≤ lowerScale) (hUpper : (0 : Q') ≤ upperScale)
    (P : ∀ i : Index, Certificate n (p i))
    (Q : ∀ i : Index, Certificate n (q i))
    (changed : ∀ i : Index, mask i = true →
      Certificate n
        (polyAdd (polyMul (cap upperScale) (q i))
          (polyNeg (polyMul (cap lowerScale) (p i)))))
    (unchanged : ∀ i : Index, mask i = false → HaarCarrierEqv n (p i) (q i)) :
    Certificate n
      (polyAdd
        (polySmul (upperScale ^ changedCount mask ids)
          (factorProduct (ids.map q)))
        (polyNeg (polySmul (lowerScale ^ changedCount mask ids)
          (factorProduct (ids.map p))))) :=
  masked_product_gap_certificate ids mask p q lowerScale upperScale
    hLower hUpper P Q
    (fun i hi => cap_gap_to_smul lowerScale upperScale (changed i hi)) unchanged

#print axioms unchanged_gap
#print axioms two_factor_gap
#print axioms product_certificate
#print axioms product_gap_certificate
#print axioms changedCount
#print axioms changedCount_eq_filter_length
#print axioms masked_product_coeff
#print axioms cap_gap_to_smul
#print axioms masked_product_gap_certificate
#print axioms masked_product_gap_certificate_cap

end YMGap.Continuum.QuaternionHaarChangedProductComparison
