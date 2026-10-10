/-
Actual product admissibility for the represented original-Haar domain. The
pointwise CReal product, its Type-level inner rate, sound bound and continuity
radius are all produced from the two existing dense presentations. Independently
sampled products agree with the SAME pointwise RC product on EVERY Point, so
multiplication descends through both represented-map arguments. No integral
multiplicativity is claimed; Haar is linear, not multiplicative. This does not
construct quantitative function-domain completion, full Haar/J04 or a physical
Yang--Mills mass gap.
-/

import YMGap.Constructive.CRealInnerMultiplication
import YMGap.Constructive.CRealMulLe
import YMGap.Continuum.QuaternionRepresentedHaar
import YMGap.Continuum.QuaternionRepresentedPolynomialHaar

namespace YMGap.Continuum.QuaternionRepresentedHaarMultiplication

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.QuaternionRepresentedHaar
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.QuaternionDenseCRealPointExtension
open YMGap.Continuum.QuaternionRepresentedPolynomialHaar
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCauchyGroup

local infix:50 " ≈ " => Q'.eqv

private theorem geRat_abs (x : CReal) : ExpPos.geRat (CReal.abs x) 0 :=
  ExpPos.geRat_of_eventually
    ⟨0, fun n _ => Q'.abs_nonneg (x.approx n)⟩

/-- Signed rational product telescope with only the two factor caps that are
actually used: the first factor of the left product and the second factor of
the right product. Nonnegativity of the caps follows from those inequalities. -/
theorem product_difference (a b c d A B delta : Q')
    (hA : Q'.abs a ≤ A) (hB : Q'.abs d ≤ B)
    (hfirst : Q'.abs (a + -c) ≤ delta)
    (hsecond : Q'.abs (b + -d) ≤ delta) :
    Q'.abs (a*b + -(c*d)) ≤ (A+B)*delta := by
  have hAnn : (0 : Q') ≤ A :=
    Q'.le_trans' _ _ _ (Q'.abs_nonneg a) hA
  have hpin : a*b + -(c*d) ≈ a*(b + -d)+(a + -c)*d :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3))))
      (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 3))))
        (.mul (.add (.var 0) (.neg (.var 2))) (.var 3)))
      (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)
  have hleft : Q'.abs a*Q'.abs (b + -d) ≤ A*delta :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hA (Q'.abs_nonneg _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hsecond hAnn)
  have hright : Q'.abs (a + -c)*Q'.abs d ≤ delta*B :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hfirst (Q'.abs_nonneg _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hB
        (Q'.le_trans' _ _ _ (Q'.abs_nonneg _) hfirst))
  have hfactor : A*delta+delta*B ≈ (A+B)*delta :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 2)) (.mul (.var 2) (.var 1)))
      (.mul (.add (.var 0) (.var 1)) (.var 2))
      (by decide) (fun | 0 => A | 1 => B | _ => delta)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.le_trans' _ _ _
        (Q'.add_le_add (ExpNeg.abs_mul_le _ _) (ExpNeg.abs_mul_le _ _))
        (Q'.le_trans' _ _ _ (Q'.add_le_add hleft hright)
          (Q'.le_of_eqv hfactor))))

/-- Sound product bound from the two sound absolute bounds. The pointwise
rational absolute-product inequality is retained, rather than postulating a
global early-row bound. -/
theorem product_abs_bound {u v : CReal} {A B : Q'}
    (hu : leRat (CReal.abs u) A) (hv : leRat (CReal.abs v) B)
    (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B) :
    leRat (CReal.abs (CReal.mul u v)) (A*B) := by
  have hmul := CReal.leRat_mul hu hv (geRat_abs u) (geRat_abs v) hA hB
  intro epsilon hepsilon
  obtain ⟨K, hK⟩ := hmul epsilon hepsilon
  refine ⟨K, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le (u.approx n) (v.approx n))
    (hK n hn)

/-- The actual four-input product difference, with signed inputs and separate
sound absolute caps on the first and fourth factors. -/
theorem product_distance {a b c d : CReal} {A B delta : Q'}
    (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (hdelta : (0 : Q') ≤ delta)
    (ha : leRat (CReal.abs a) A)
    (hd : leRat (CReal.abs d) B)
    (hfirst : leRat (CReal.abs (CReal.add a (CReal.neg c))) delta)
    (hsecond : leRat (CReal.abs (CReal.add b (CReal.neg d))) delta) :
    leRat (CReal.abs (CReal.add (CReal.mul a b)
      (CReal.neg (CReal.mul c d)))) ((A+B)*delta) := by
  have hleft := CReal.leRat_mul ha hsecond (geRat_abs a)
    (geRat_abs (CReal.add b (CReal.neg d))) hA hdelta
  have hright := CReal.leRat_mul hfirst hd
    (geRat_abs (CReal.add a (CReal.neg c))) (geRat_abs d) hdelta hB
  have hsum := CReal.leRat_add hleft hright
  intro epsilon hepsilon
  obtain ⟨K, hK⟩ := hsum epsilon hepsilon
  refine ⟨K, fun n hn => ?_⟩
  let ap := a.approx n
  let bp := b.approx n
  let cp := c.approx n
  let dp := d.approx n
  have hpin : ap*bp + -(cp*dp) ≈
      ap*(bp + -dp) + (ap + -cp)*dp :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1))
        (.neg (.mul (.var 2) (.var 3))))
      (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 3))))
        (.mul (.add (.var 0) (.neg (.var 2))) (.var 3)))
      (by decide) (fun | 0 => ap | 1 => bp | 2 => cp | _ => dp)
  have hpoint : Q'.abs (ap*bp + -(cp*dp)) ≤
      Q'.abs ap * Q'.abs (bp + -dp) +
        Q'.abs (ap + -cp) * Q'.abs dp :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin))
      (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
        (Q'.add_le_add (ExpNeg.abs_mul_le _ _) (ExpNeg.abs_mul_le _ _)))
  have hfactor : A*delta + delta*B ≈ (A+B)*delta :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 2)) (.mul (.var 2) (.var 1)))
      (.mul (.add (.var 0) (.var 1)) (.var 2))
      (by decide) (fun | 0 => A | 1 => B | _ => delta)
  exact Q'.le_trans' _ _ _ hpoint
    (Q'.le_trans' _ _ _ (hK n hn)
      (Q'.add_le_add_right _ _ epsilon (Q'.le_of_eqv hfactor)))

/-- Same literal dense input, not an independently supplied product map. -/
def productInput (D E : DenseData) (q : UnitNorm) : CReal :=
  CReal.mul (D.values q) (E.values q)

/-- The generic computed inner multiplication is applied at each actual
dense quaternion. -/
def productInner (D E : DenseData) :
    ∀ q, InnerRegularity (productInput D E q) :=
  fun q => InnerRegularity.mul (D.inner q) (E.inner q)

/-- The sound output cap uses absolute input caps, including negative or
noncanonical presentations. -/
def productBound (D E : DenseData) : Q' :=
  Q'.abs D.bound * Q'.abs E.bound

/-- Computed common input tolerance; no inverse of a potentially zero bound. -/
def productTolerance (D E : DenseData) (epsilon : Q') : Q' :=
  InnerRegularity.scaleTolerance (Q'.abs D.bound + Q'.abs E.bound) epsilon

/-- The minimum of the two produced radii at the common tolerance. -/
def productRadius (D E : DenseData) (epsilon : Q') : Q' :=
  Q'.min' (D.radius (productTolerance D E epsilon))
    (E.radius (productTolerance D E epsilon))

theorem productRadius_positive (D E : DenseData) (epsilon : Q')
    (he : (0 : Q') < epsilon) :
    (0 : Q') < productRadius D E epsilon :=
  CReal.min_pos
    (D.radius_positive _
      (InnerRegularity.scaleTolerance_pos _ epsilon he))
    (E.radius_positive _
      (InnerRegularity.scaleTolerance_pos _ epsilon he))

theorem product_bound (D E : DenseData) (q : UnitNorm) :
    leRat (CReal.abs (productInput D E q)) (productBound D E) :=
  product_abs_bound
    (CReal.leRat_mono (D.bounded q) (Q'.le_abs_self D.bound))
    (CReal.leRat_mono (E.bounded q) (Q'.le_abs_self E.bound))
    (Q'.abs_nonneg D.bound) (Q'.abs_nonneg E.bound)

/-- Continuity of the actual dense product from the same two source moduli.
The radius is squared-chord in the source and neither radius is assumed
monotone. -/
theorem product_modulus (D E : DenseData) (epsilon : Q')
    (he : (0 : Q') < epsilon) (q x : UnitNorm)
    (hd : distSq q.val x.val ≤ productRadius D E epsilon) :
    leRat (CReal.abs (CReal.add (productInput D E q)
      (CReal.neg (productInput D E x)))) epsilon := by
  let A := Q'.abs D.bound
  let B := Q'.abs E.bound
  let delta := productTolerance D E epsilon
  have hdelta : (0 : Q') < delta :=
    InnerRegularity.scaleTolerance_pos (A+B) epsilon he
  have hD : distSq q.val x.val ≤ D.radius delta :=
    Q'.le_trans' _ _ _ hd Q'.min_le_left
  have hE : distSq q.val x.val ≤ E.radius delta :=
    Q'.le_trans' _ _ _ hd Q'.min_le_right
  have hstep := product_distance
    (Q'.abs_nonneg D.bound) (Q'.abs_nonneg E.bound)
    (Q'.le_of_lt hdelta)
    (CReal.leRat_mono (D.bounded q) (Q'.le_abs_self D.bound))
    (CReal.leRat_mono (E.bounded x) (Q'.le_abs_self E.bound))
    (D.continuity delta hdelta q x hD)
    (E.continuity delta hdelta q x hE)
  exact CReal.leRat_mono hstep
    (InnerRegularity.mul_scaleTolerance_le (A+B) epsilon
      (Q'.zero_le_add A B (Q'.abs_nonneg D.bound)
        (Q'.abs_nonneg E.bound)) he)

/-- Produced product presentation in the SAME represented-map domain. -/
def productData (D E : DenseData) : DenseData where
  values := productInput D E
  inner := productInner D E
  bound := productBound D E
  radius := productRadius D E
  radius_positive := productRadius_positive D E
  bounded := product_bound D E
  continuity := product_modulus D E

private theorem abs_sub_triangle (a b c : Q') :
    Q'.abs (a + -c) ≤ Q'.abs (a + -b) + Q'.abs (b + -c) := by
  have hpin : a + -c ≈ (a + -b) + (b + -c) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.var 2)))
      (.add (.add (.var 0) (.neg (.var 1)))
        (.add (.var 1) (.neg (.var 2))))
      (by decide) (fun | 0 => a | 1 => b | _ => c)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin))
    (ExpNeg.abs_add_le _ _)

/-- Independent samples compare at ONE later inner index. The sound-bound
cutoff occurs only inside this rational proof, never in the produced rates.
Early input approximations need not satisfy the sound caps. -/
theorem sample_product_error (u v : CReal)
    (Ru : InnerRegularity u) (Rv : InnerRegularity v) (M N tau : Q')
    (hM : leRat (CReal.abs u) M) (hN : leRat (CReal.abs v) N)
    (ht : (0 : Q') < tau) (ht1 : tau ≤ 1) :
    Q'.abs (sample (CReal.mul u v) (InnerRegularity.mul Ru Rv) tau +
      -(sample u Ru tau * sample v Rv tau)) ≤
        (Q'.abs M + Q'.abs N + 3)*tau := by
  obtain ⟨K, hK⟩ := (leRat_mono hM (Q'.le_abs_self M)) tau ht
  let j := max ((InnerRegularity.mul Ru Rv).rate tau)
    (max (Ru.rate tau) (max (Rv.rate tau) K))
  have hprod := sample_error_bound (CReal.mul u v) (InnerRegularity.mul Ru Rv)
    tau ht j (Nat.le_max_left _ _)
  have hu := sample_error_bound u Ru tau ht j
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
  have hv := sample_error_bound v Rv tau ht j
    (Nat.le_trans
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      (Nat.le_max_right _ _))
  have hub : Q'.abs (u.approx j) ≤ Q'.abs M + tau :=
    hK j (Nat.le_trans
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      (Nat.le_max_right _ _))
  have hvb : Q'.abs (sample v Rv tau) ≤ Q'.abs N + tau :=
    sample_abs_le v Rv (Q'.abs N) tau
      (leRat_mono hN (Q'.le_abs_self N)) ht
  have hup : Q'.abs (u.approx j + -(sample u Ru tau)) ≤ tau :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) hu
  have hvp : Q'.abs (v.approx j + -(sample v Rv tau)) ≤ tau :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) hv
  have hpair := product_difference (u.approx j) (v.approx j)
    (sample u Ru tau) (sample v Rv tau)
    (Q'.abs M + tau) (Q'.abs N + tau) tau hub hvb hup hvp
  have hsum : Q'.abs (sample (CReal.mul u v) (InnerRegularity.mul Ru Rv) tau +
      -(sample u Ru tau * sample v Rv tau)) ≤
        tau + ((Q'.abs M + tau) + (Q'.abs N + tau))*tau :=
    Q'.le_trans' _ _ _ (abs_sub_triangle _ (u.approx j*v.approx j) _)
      (Q'.add_le_add hprod hpair)
  have hpin : tau + ((Q'.abs M + tau) + (Q'.abs N + tau))*tau ≈
      ((Q'.abs M + Q'.abs N) + (1+(tau+tau)))*tau :=
    poly_identity_of_normal_eq
      (.add (.var 2) (.mul
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 2))) (.var 2)))
      (.mul (.add (.add (.var 0) (.var 1))
        (.add (.const 1) (.add (.var 2) (.var 2)))) (.var 2))
      (by decide) (fun | 0 => Q'.abs M | 1 => Q'.abs N | _ => tau)
  have hthree : (1 : Q') + (tau+tau) ≤ 3 :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_left 1 _ _ (Q'.add_le_add ht1 ht1))
      (Q'.le_of_eqv (by decide : (1 : Q')+(1+1) ≈ 3))
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
      (Q'.mul_le_mul_of_nonneg_right _ _ tau
        (Q'.add_le_add_left _ _ _ hthree) (Q'.le_of_lt ht)))

/-- Recoverable cutoff for the full product-sampling error. -/
def productRowEqualityRate (D E : DenseData) (epsilon : Q') : Nat :=
  (InnerRegularity.scaleTolerance (Q'.abs D.bound + Q'.abs E.bound + 3)
    epsilon).den

private theorem product_tail_budget (D E : DenseData) (epsilon : Q')
    (he : (0 : Q') < epsilon) (n : Nat)
    (hn : productRowEqualityRate D E epsilon ≤ n) :
    (Q'.abs D.bound + Q'.abs E.bound + 3)*Q'.invSucc n ≤ epsilon := by
  let A := Q'.abs D.bound + Q'.abs E.bound + 3
  let theta := InnerRegularity.scaleTolerance A epsilon
  have hA : (0 : Q') ≤ A :=
    Q'.zero_le_add _ 3
      (Q'.zero_le_add _ _ (Q'.abs_nonneg _) (Q'.abs_nonneg _)) (by decide)
  have ht : (0 : Q') < theta := InnerRegularity.scaleTolerance_pos A epsilon he
  have hs : Q'.invSucc n ≤ theta :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn)
      (HalfPow.invSucc_den_le theta ht)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ A hs hA)
    (InnerRegularity.mul_scaleTolerance_le A epsilon hA he)

/-- Equality of actual output rows, retaining an explicit outer cutoff that
depends only on the supplied global bounds, not hidden inner choices. -/
theorem rowImage_product (D E : DenseData) (X : CauchyPoint) :
    Equiv
      (rowImage (productData D E).values (productData D E).inner
        (productData D E).radius (productData D E).radius_positive
        (productData D E).continuity X)
      (CReal.mul
        (rowImage D.values D.inner D.radius D.radius_positive D.continuity X)
        (rowImage E.values E.inner E.radius E.radius_positive E.continuity X)) := by
  intro epsilon he
  refine ⟨productRowEqualityRate D E epsilon, fun n hn => ?_⟩
  have ht1 : Q'.invSucc n ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le (Nat.zero_le n))
      (Q'.le_of_eqv (by decide : Q'.invSucc 0 ≈ 1))
  have hb := sample_product_error (D.values (X.seq n)) (E.values (X.seq n))
    (D.inner (X.seq n)) (E.inner (X.seq n)) D.bound E.bound (Q'.invSucc n)
    (D.bounded (X.seq n)) (E.bounded (X.seq n)) (Q'.invSucc_pos n) ht1
  have hs := Q'.le_trans' _ _ _ hb (product_tail_budget D E epsilon he n hn)
  exact ⟨ExpNeg.le_add_of_abs_sub_le hs,
    ExpNeg.le_add_of_abs_sub_le
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) hs)⟩

/-- Produced multiplication is the SAME RC multiplication at EVERY completed
Point, not just on dense embeddings or a chosen representative row. -/
theorem product_map (D E : DenseData) (x : Point) :
    (productData D E).map x = RCmul (D.map x) (E.map x) := by
  refine Quotient.inductionOn x (fun X => ?_)
  change pointExtension (productData D E).values (productData D E).inner
      (productData D E).radius (productData D E).radius_positive
      (productData D E).continuity (Quotient.mk _ X) =
    RCmul (pointExtension D.values D.inner D.radius D.radius_positive
      D.continuity (Quotient.mk _ X))
      (pointExtension E.values E.inner E.radius E.radius_positive
      E.continuity (Quotient.mk _ X))
  rw [pointExtension_mk, pointExtension_mk, pointExtension_mk, RCmul_mk]
  exact Quotient.sound (rowImage_product D E X)

/-- Both factors descend through equality of ACTUAL completed maps. -/
def mul : Represented → Represented → Represented :=
  Quotient.lift₂ (s₁ := dataSetoid) (s₂ := dataSetoid)
    (fun D E => classOf (productData D E))
    (fun D E D' E' hD hE => Quotient.sound (by
      intro x
      rw [product_map, product_map, hD x, hE x]))

theorem evaluate_mul (f g : Represented) (x : Point) :
    evaluate (mul f g) x = RCmul (evaluate f x) (evaluate g x) := by
  refine Quotient.inductionOn₂ f g ?_
  intro D E
  exact product_map D E x

/-- General domain multiplication agrees with the ORIGINAL polynomial product,
independently of its different admissibility presentation. -/
theorem mul_polynomial (p q :
    YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.RatPoly) :
    mul (polynomial p) (polynomial q) =
      polynomial (YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.polyMul p q) := by
  apply QuaternionRepresentedHaar.ext
  intro x
  rw [evaluate_mul, evaluate_polynomial_mul]

/-- A SAME-object nonzero second moment under general represented multiplication.
This is compact-group Haar variance, not interacting/continuum survival. -/
theorem integral_coordinate_square :
    integral (mul coordinateObservable coordinateObservable) =
      YMGap.Continuum.SU2QuaternionPointPolynomialHaarTranslation.rational
        (HalfPow.half*HalfPow.half) := by
  rw [coordinateObservable, mul_polynomial]
  exact coordinate_second_moment

#print axioms product_difference
#print axioms product_abs_bound
#print axioms product_distance
#print axioms productInput
#print axioms productInner
#print axioms productBound
#print axioms productTolerance
#print axioms productRadius
#print axioms productRadius_positive
#print axioms product_bound
#print axioms product_modulus
#print axioms productData
#print axioms sample_product_error
#print axioms productRowEqualityRate
#print axioms rowImage_product
#print axioms product_map
#print axioms mul
#print axioms evaluate_mul
#print axioms mul_polynomial
#print axioms integral_coordinate_square

end YMGap.Continuum.QuaternionRepresentedHaarMultiplication
