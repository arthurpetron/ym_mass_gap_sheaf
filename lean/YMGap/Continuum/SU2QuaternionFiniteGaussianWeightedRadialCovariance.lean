/-
# Rationally weighted finite Gaussian radial sixth covariance

This leaf extends the exact finite rational-row Gaussian radial identities to
coefficients multiplying the row squares themselves.  For

  S_B = sum_i u_i * (b_i dot X)^2,
  S_D = sum_j v_j * (d_j dot X)^2,

it proves

  Cov(S_B^2,S_D)
    = 8 * sum_i,k,j u_i*u_k*v_j
          * Gram(b_i,b_k)*Gram(b_i,d_j)*Gram(b_k,d_j)
      + 4 * (sum_i u_i*Gram(b_i,b_i))
          * (sum_i,j u_i*v_j*Gram(b_i,d_j)^2).

All sums are literal finite `Q'` sums.  No square roots, positivity premise,
matrix inverse, original interacting law, continuum limit, Hamiltonian gap,
or Clay-facing conclusion is introduced.  The immediate consumer is the
cleared numerator of the explicit positive-denominator open-cube Heron ratio.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianWeightedRadialCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP
open YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianSixthMoment
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS

local infix:50 " ≈ " => Q'.eqv

private theorem qListSum_map_eq_listQSum_local {A : Type}
    (value : A → Q') : ∀ items : List A,
    qListSum (items.map value) = listQSum value items
  | [] => rfl
  | _ :: items => by
      simp only [List.map, qListSum, listQSum]
      rw [qListSum_map_eq_listQSum_local value items]

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem gaussian_zero (N : Nat) : finiteProductGaussian N polyZero ≈ 0 := by
  rw [finiteProductGaussian_probe]
  exact Q'.eqv_refl _

private theorem gaussian_add (N : Nat) (p q : RatPoly) :
    finiteProductGaussian N (polyAdd p q) ≈
      finiteProductGaussian N p + finiteProductGaussian N q := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe, finiteProductGaussian_probe]
  exact ratWeightedSum_add (finiteGaussianMono N) p q

private theorem gaussian_smul (N : Nat) (c : Q') (p : RatPoly) :
    finiteProductGaussian N (polySmul c p) ≈
      c * finiteProductGaussian N p := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe]
  exact ratWeightedSum_smul (finiteGaussianMono N) c p

private theorem covariance_congr (N : Nat) {p p' q q' : RatPoly}
    (hp : RatPolyCoeffEqv p p') (hq : RatPolyCoeffEqv q q') :
    finiteGaussianCovariance N p q ≈ finiteGaussianCovariance N p' q' := by
  unfold finiteGaussianCovariance
  exact Q'.add_eqv_congr'
    (finiteProductGaussian_coeffEqv N (hp.mul hq))
    (Q'.neg_eqv_congr _ _ (mul_congr
      (finiteProductGaussian_coeffEqv N hp)
      (finiteProductGaussian_coeffEqv N hq)))

private theorem covariance_smul (N : Nat) (leftWeight rightWeight : Q')
    (p q : RatPoly) :
    finiteGaussianCovariance N
        (polySmul leftWeight p) (polySmul rightWeight q) ≈
      (leftWeight * rightWeight) * finiteGaussianCovariance N p q := by
  have hproduct :
      finiteProductGaussian N
          (polyMul (polySmul leftWeight p) (polySmul rightWeight q)) ≈
        (leftWeight * rightWeight) *
          finiteProductGaussian N (polyMul p q) := by
    exact Q'.eqv_trans _ _ _
      (finiteProductGaussian_coeffEqv N
        ((RatPolyCoeffEqv.polyMul_smul_left
            leftWeight p (polySmul rightWeight q)).trans
          (((RatPolyCoeffEqv.polyMul_smul_right rightWeight p q).smul
              leftWeight).trans
            (RatPolyCoeffEqv.smul_assoc
              leftWeight rightWeight (polyMul p q)))))
      (gaussian_smul N (leftWeight * rightWeight) (polyMul p q))
  unfold finiteGaussianCovariance
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hproduct
      (Q'.neg_eqv_congr _ _ (mul_congr
        (gaussian_smul N leftWeight p)
        (gaussian_smul N rightWeight q))))
    (poly_identity_of_normal_eq
      (.add
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.neg
          (.mul (.mul (.var 0) (.var 3))
            (.mul (.var 1) (.var 4)))))
      (.mul (.mul (.var 0) (.var 1))
        (.add (.var 2) (.neg (.mul (.var 3) (.var 4)))))
      (by decide) (fun
        | 0 => leftWeight
        | 1 => rightWeight
        | 2 => finiteProductGaussian N (polyMul p q)
        | 3 => finiteProductGaussian N p
        | _ => finiteProductGaussian N q))

private theorem covariance_add_left (N : Nat) (p q r : RatPoly) :
    finiteGaussianCovariance N (polyAdd p q) r ≈
      finiteGaussianCovariance N p r + finiteGaussianCovariance N q r := by
  unfold finiteGaussianCovariance
  rw [polyMul_add_left_exact]
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (gaussian_add N (polyMul p r) (polyMul q r))
      (Q'.neg_eqv_congr _ _ (mul_congr (gaussian_add N p q) (Q'.eqv_refl _))))
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1))
        (.neg (.mul (.add (.var 2) (.var 3)) (.var 4))))
      (.add
        (.add (.var 0) (.neg (.mul (.var 2) (.var 4))))
        (.add (.var 1) (.neg (.mul (.var 3) (.var 4)))))
      (by decide) (fun
        | 0 => finiteProductGaussian N (polyMul p r)
        | 1 => finiteProductGaussian N (polyMul q r)
        | 2 => finiteProductGaussian N p
        | 3 => finiteProductGaussian N q
        | _ => finiteProductGaussian N r))

private theorem covariance_add_right (N : Nat) (p q r : RatPoly) :
    finiteGaussianCovariance N p (polyAdd q r) ≈
      finiteGaussianCovariance N p q + finiteGaussianCovariance N p r := by
  unfold finiteGaussianCovariance
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _
        (finiteProductGaussian_coeffEqv N (RatPolyCoeffEqv.mul_add_right p q r))
        (gaussian_add N (polyMul p q) (polyMul p r)))
      (Q'.neg_eqv_congr _ _ (mul_congr (Q'.eqv_refl _) (gaussian_add N q r))))
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1))
        (.neg (.mul (.var 2) (.add (.var 3) (.var 4)))))
      (.add
        (.add (.var 0) (.neg (.mul (.var 2) (.var 3))))
        (.add (.var 1) (.neg (.mul (.var 2) (.var 4)))))
      (by decide) (fun
        | 0 => finiteProductGaussian N (polyMul p q)
        | 1 => finiteProductGaussian N (polyMul p r)
        | 2 => finiteProductGaussian N p
        | 3 => finiteProductGaussian N q
        | _ => finiteProductGaussian N r))

private theorem covariance_zero_left (N : Nat) (q : RatPoly) :
    finiteGaussianCovariance N polyZero q ≈ 0 := by
  unfold finiteGaussianCovariance
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (gaussian_zero N)
      (Q'.neg_eqv_congr _ _ (mul_congr (gaussian_zero N) (Q'.eqv_refl _))))
    (poly_identity_of_normal_eq
      (.add (.const 0) (.neg (.mul (.const 0) (.var 0))))
      (.const 0) (by decide) (fun _ => finiteProductGaussian N q))

private theorem covariance_zero_right (N : Nat) (p : RatPoly) :
    finiteGaussianCovariance N p polyZero ≈ 0 := by
  unfold finiteGaussianCovariance
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _
        (finiteProductGaussian_coeffEqv N (RatPolyCoeffEqv.mul_zero_right p))
        (gaussian_zero N))
      (Q'.neg_eqv_congr _ _ (mul_congr (Q'.eqv_refl _) (gaussian_zero N))))
    (poly_identity_of_normal_eq
      (.add (.const 0) (.neg (.mul (.var 0) (.const 0))))
      (.const 0) (by decide) (fun _ => finiteProductGaussian N p))

private theorem covariance_polySum_left (N : Nat) (q : RatPoly) : ∀ ps : List RatPoly,
    finiteGaussianCovariance N (polySum ps) q ≈
      qListSum (ps.map fun p => finiteGaussianCovariance N p q)
  | [] => covariance_zero_left N q
  | p :: ps => Q'.eqv_trans _ _ _ (covariance_add_left N p (polySum ps) q)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (covariance_polySum_left N q ps))

private theorem covariance_polySum_right (N : Nat) (p : RatPoly) : ∀ qs : List RatPoly,
    finiteGaussianCovariance N p (polySum qs) ≈
      qListSum (qs.map fun q => finiteGaussianCovariance N p q)
  | [] => covariance_zero_right N p
  | q :: qs => Q'.eqv_trans _ _ _ (covariance_add_right N p q (polySum qs))
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (covariance_polySum_right N p qs))

private theorem qListSum_congr {A : Type} (f g : A → Q') : ∀ ids : List A,
    (∀ i, i ∈ ids → f i ≈ g i) →
    qListSum (ids.map f) ≈ qListSum (ids.map g)
  | [], _ => Q'.eqv_refl _
  | i :: ids, h => Q'.add_eqv_congr' (h i List.mem_cons_self)
      (qListSum_congr f g ids (fun k hk => h k (List.mem_cons_of_mem i hk)))

private theorem weighted_radial_covariance_expansion
    (N rowCount directionCount : Nat)
    (rowWeights directionWeights : Nat → Q')
    (b d : Nat → Nat → Q') :
    finiteGaussianCovariance N
      (polyMul
        (finiteGaussianWeightedRadialSquare N rowCount rowWeights b)
        (finiteGaussianWeightedRadialSquare N rowCount rowWeights b))
      (finiteGaussianWeightedRadialSquare
        N directionCount directionWeights d) ≈
      qListSum ((List.range rowCount).map fun i =>
        qListSum ((List.range rowCount).map fun k =>
          qListSum ((List.range directionCount).map fun j =>
            finiteGaussianCovariance N
              (polyMul
                (polySmul (rowWeights i) (finiteGaussianRowSquare N (b i)))
                (polySmul (rowWeights k) (finiteGaussianRowSquare N (b k))))
              (polySmul (directionWeights j)
                (finiteGaussianRowSquare N (d j)))))) := by
  let bs := (List.range rowCount).map fun i =>
    polySmul (rowWeights i) (finiteGaussianRowSquare N (b i))
  let ds := (List.range directionCount).map fun j =>
    polySmul (directionWeights j) (finiteGaussianRowSquare N (d j))
  have houter :
      finiteGaussianCovariance N (polyMul (polySum bs) (polySum bs)) (polySum ds) ≈
        qListSum (bs.map fun p =>
          finiteGaussianCovariance N (polyMul p (polySum bs)) (polySum ds)) :=
    Q'.eqv_trans _ _ _
      (covariance_congr N (RatPolyCoeffEqv.polySum_mul_right bs (polySum bs))
        (RatPolyCoeffEqv.refl _))
      (by
        simpa only [List.map_map] using
          (covariance_polySum_left N (polySum ds)
            (bs.map fun p => polyMul p (polySum bs))))
  have hmiddle :
      qListSum (bs.map fun p =>
          finiteGaussianCovariance N (polyMul p (polySum bs)) (polySum ds)) ≈
        qListSum (bs.map fun p => qListSum (bs.map fun q =>
          finiteGaussianCovariance N (polyMul p q) (polySum ds))) :=
    qListSum_congr _ _ bs (fun p _ =>
      Q'.eqv_trans _ _ _
        (covariance_congr N (RatPolyCoeffEqv.mul_polySum_right p bs)
          (RatPolyCoeffEqv.refl _))
        (by
          simpa only [List.map_map] using
            (covariance_polySum_left N (polySum ds) (bs.map fun q => polyMul p q))))
  have hinner :
      qListSum (bs.map fun p => qListSum (bs.map fun q =>
          finiteGaussianCovariance N (polyMul p q) (polySum ds))) ≈
        qListSum (bs.map fun p => qListSum (bs.map fun q => qListSum (ds.map fun r =>
          finiteGaussianCovariance N (polyMul p q) r))) :=
    qListSum_congr _ _ bs (fun p _ => qListSum_congr _ _ bs (fun q _ =>
      covariance_polySum_right N (polyMul p q) ds))
  have htotal := Q'.eqv_trans _ _ _ houter (Q'.eqv_trans _ _ _ hmiddle hinner)
  simpa only [finiteGaussianWeightedRadialSquare, bs, ds, List.map_map] using htotal

/-- Covariance of two weighted row squares multiplied on the left and one
weighted row square on the right. -/
theorem finiteGaussianCovariance_weighted_three_square
    (N : Nat) (leftWeight middleWeight rightWeight : Q')
    (b d e : Nat → Q') :
    finiteGaussianCovariance N
      (polyMul
        (polySmul leftWeight (finiteGaussianRowSquare N b))
        (polySmul middleWeight (finiteGaussianRowSquare N d)))
      (polySmul rightWeight (finiteGaussianRowSquare N e)) ≈
      ((leftWeight * middleWeight) * rightWeight) *
        (2 * (finiteRowNorm2 N b *
              (finiteRowGram N d e * finiteRowGram N d e) +
            finiteRowNorm2 N d *
              (finiteRowGram N b e * finiteRowGram N b e)) +
          8 * finiteRowGram N b d * finiteRowGram N b e * finiteRowGram N d e) := by
  let p := finiteGaussianRowSquare N b
  let q := finiteGaussianRowSquare N d
  let r := finiteGaussianRowSquare N e
  have hleft :
      RatPolyCoeffEqv
        (polyMul (polySmul leftWeight p) (polySmul middleWeight q))
        (polySmul (leftWeight * middleWeight) (polyMul p q)) :=
    (RatPolyCoeffEqv.polyMul_smul_left
        leftWeight p (polySmul middleWeight q)).trans
      (((RatPolyCoeffEqv.polyMul_smul_right middleWeight p q).smul
          leftWeight).trans
        (RatPolyCoeffEqv.smul_assoc leftWeight middleWeight (polyMul p q)))
  exact Q'.eqv_trans _ _ _
    (covariance_congr N hleft (RatPolyCoeffEqv.refl _))
    (Q'.eqv_trans _ _ _
      (covariance_smul N (leftWeight * middleWeight) rightWeight (polyMul p q) r)
      (Q'.mul_eqv_congr_left _ _ _
        (finiteGaussianCovariance_three_square N b d e)))

/-- Literal weighted triple-sum expansion of the finite radial sixth
covariance. -/
theorem finiteGaussianWeightedRadialCovariance_summands
    (N rowCount directionCount : Nat)
    (rowWeights directionWeights : Nat → Q')
    (b d : Nat → Nat → Q') :
    finiteGaussianCovariance N
      (polyMul
        (finiteGaussianWeightedRadialSquare N rowCount rowWeights b)
        (finiteGaussianWeightedRadialSquare N rowCount rowWeights b))
      (finiteGaussianWeightedRadialSquare
        N directionCount directionWeights d) ≈
      qListSum ((List.range rowCount).map fun i =>
        qListSum ((List.range rowCount).map fun k =>
          qListSum ((List.range directionCount).map fun j =>
            (((rowWeights i * rowWeights k) * directionWeights j) *
              (2 * (finiteRowNorm2 N (b i) *
                    (finiteRowGram N (b k) (d j) * finiteRowGram N (b k) (d j)) +
                  finiteRowNorm2 N (b k) *
                    (finiteRowGram N (b i) (d j) * finiteRowGram N (b i) (d j))) +
                8 * finiteRowGram N (b i) (b k) *
                  finiteRowGram N (b i) (d j) *
                  finiteRowGram N (b k) (d j)))))) := by
  exact Q'.eqv_trans _ _ _
    (weighted_radial_covariance_expansion
      N rowCount directionCount rowWeights directionWeights b d)
    (qListSum_congr _ _ (List.range rowCount) (fun i _ =>
      qListSum_congr _ _ (List.range rowCount) (fun k _ =>
        qListSum_congr _ _ (List.range directionCount) (fun j _ =>
          finiteGaussianCovariance_weighted_three_square N
            (rowWeights i) (rowWeights k) (directionWeights j)
            (b i) (b k) (d j)))))

private def qSum {A : Type} (ids : List A) (f : A → Q') : Q' :=
  qListSum (ids.map f)

private def qSum2 {A B : Type} (as : List A) (bs : List B)
    (f : A → B → Q') : Q' :=
  qSum as fun a => qSum bs (f a)

private def qSum3 {A B C : Type} (as : List A) (bs : List B) (cs : List C)
    (f : A → B → C → Q') : Q' :=
  qSum as fun a => qSum2 bs cs (f a)

private theorem qSum_congr {A : Type} (ids : List A) (f g : A → Q')
    (h : ∀ i, i ∈ ids → f i ≈ g i) : qSum ids f ≈ qSum ids g :=
  qListSum_congr f g ids h

private theorem qSum_add {A : Type} (ids : List A) (f g : A → Q') :
    qSum ids (fun i => f i + g i) ≈ qSum ids f + qSum ids g := by
  induction ids with
  | nil => exact Q'.eqv_symm (QPoly.q_zero_add_eqv 0)
  | cons i ids ih =>
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ ih)
        (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
          (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
          (by decide) (fun
            | 0 => f i
            | 1 => g i
            | 2 => qSum ids f
            | _ => qSum ids g))

private theorem qSum_scale (c : Q') {A : Type} (ids : List A) (f : A → Q') :
    qSum ids (fun i => c * f i) ≈ c * qSum ids f := by
  induction ids with
  | nil => exact Q'.eqv_symm (Q'.mul_zero_eqv c)
  | cons i ids ih =>
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) ih)
        (Q'.eqv_symm (Q'.mul_add_eqv c (f i) (qSum ids f)))

private theorem qSum_scale_right {A : Type} (ids : List A) (f : A → Q') (c : Q') :
    qSum ids (fun i => f i * c) ≈ qSum ids f * c := by
  induction ids with
  | nil => exact Q'.eqv_symm (Q'.zero_mul_eqv c)
  | cons i ids ih =>
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) ih)
        (Q'.eqv_symm (Q'.add_mul_eqv (f i) (qSum ids f) c))

private theorem qSum2_congr {A B : Type} (as : List A) (bs : List B)
    (f g : A → B → Q') (h : ∀ a, a ∈ as → ∀ b, b ∈ bs → f a b ≈ g a b) :
    qSum2 as bs f ≈ qSum2 as bs g :=
  qSum_congr as _ _ (fun a ha => qSum_congr bs _ _ (h a ha))

private theorem qSum2_add {A B : Type} (as : List A) (bs : List B)
    (f g : A → B → Q') :
    qSum2 as bs (fun a b => f a b + g a b) ≈
      qSum2 as bs f + qSum2 as bs g :=
  Q'.eqv_trans _ _ _
    (qSum_congr as _ _ (fun a _ => qSum_add bs (f a) (g a)))
    (qSum_add as (fun a => qSum bs (f a)) (fun a => qSum bs (g a)))

private theorem qSum2_scale (c : Q') {A B : Type} (as : List A) (bs : List B)
    (f : A → B → Q') :
    qSum2 as bs (fun a b => c * f a b) ≈ c * qSum2 as bs f :=
  Q'.eqv_trans _ _ _
    (qSum_congr as _ _ (fun a _ => qSum_scale c bs (f a)))
    (qSum_scale c as (fun a => qSum bs (f a)))

private theorem qSum3_congr {A B C : Type} (as : List A) (bs : List B) (cs : List C)
    (f g : A → B → C → Q')
    (h : ∀ a, a ∈ as → ∀ b, b ∈ bs → ∀ c, c ∈ cs → f a b c ≈ g a b c) :
    qSum3 as bs cs f ≈ qSum3 as bs cs g :=
  qSum_congr as _ _ (fun a ha => qSum2_congr bs cs _ _ (h a ha))

private theorem qSum3_add {A B C : Type} (as : List A) (bs : List B) (cs : List C)
    (f g : A → B → C → Q') :
    qSum3 as bs cs (fun a b c => f a b c + g a b c) ≈
      qSum3 as bs cs f + qSum3 as bs cs g :=
  Q'.eqv_trans _ _ _
    (qSum_congr as _ _ (fun a _ => qSum2_add bs cs (f a) (g a)))
    (qSum_add as (fun a => qSum2 bs cs (f a)) (fun a => qSum2 bs cs (g a)))

private theorem qSum3_scale (c : Q') {A B C : Type}
    (as : List A) (bs : List B) (cs : List C) (f : A → B → C → Q') :
    qSum3 as bs cs (fun a b d => c * f a b d) ≈ c * qSum3 as bs cs f :=
  Q'.eqv_trans _ _ _
    (qSum_congr as _ _ (fun a _ => qSum2_scale c bs cs (f a)))
    (qSum_scale c as (fun a => qSum2 bs cs (f a)))

private theorem qSum3_linear_three {A B C : Type}
    (as : List A) (bs : List B) (cs : List C)
    (a b c : Q') (f g h : A → B → C → Q') :
    qSum3 as bs cs (fun i j k => (a * f i j k + b * g i j k) + c * h i j k) ≈
      (a * qSum3 as bs cs f + b * qSum3 as bs cs g) + c * qSum3 as bs cs h :=
  Q'.eqv_trans _ _ _
    (qSum3_add as bs cs
      (fun i j k => a * f i j k + b * g i j k)
      (fun i j k => c * h i j k))
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _
        (qSum3_add as bs cs (fun i j k => a * f i j k) (fun i j k => b * g i j k))
        (Q'.add_eqv_congr' (qSum3_scale a as bs cs f) (qSum3_scale b as bs cs g)))
      (qSum3_scale c as bs cs h))

private theorem qSum2_separable {A B : Type} (as : List A) (bs : List B)
    (f : A → Q') (g : B → Q') :
    qSum2 as bs (fun a b => f a * g b) ≈ qSum as f * qSum bs g :=
  Q'.eqv_trans _ _ _
    (qSum_congr as _ _ (fun a _ => qSum_scale (f a) bs g))
    (qSum_scale_right as f (qSum bs g))

private theorem weighted_radial_sum_scalar {A B : Type}
    (rows : List A) (directions : List B)
    (rowWeight : A → Q') (directionWeight : B → Q')
    (norm : A → Q') (sigma : A → A → Q') (cross : A → B → Q') :
    qSum3 rows rows directions (fun i k j =>
      (((rowWeight i * rowWeight k) * directionWeight j) *
        (2 * (norm i * (cross k j * cross k j) +
              norm k * (cross i j * cross i j)) +
          8 * sigma i k * cross i j * cross k j))) ≈
      8 * qSum3 rows rows directions (fun i k j =>
        (((rowWeight i * rowWeight k) * directionWeight j) *
          (sigma i k * cross i j * cross k j))) +
        4 * qSum rows (fun i => rowWeight i * norm i) *
          qSum2 rows directions (fun i j =>
            ((rowWeight i * directionWeight j) * (cross i j * cross i j))) := by
  let first := fun i : A => fun k : A => fun j : B =>
    (rowWeight i * norm i) *
      ((rowWeight k * directionWeight j) * (cross k j * cross k j))
  let second := fun i : A => fun k : A => fun j : B =>
    (rowWeight k * norm k) *
      ((rowWeight i * directionWeight j) * (cross i j * cross i j))
  let mixed := fun i : A => fun k : A => fun j : B =>
    ((rowWeight i * rowWeight k) * directionWeight j) *
      (sigma i k * cross i j * cross k j)
  let gramSquare := qSum2 rows directions (fun i j =>
    (rowWeight i * directionWeight j) * (cross i j * cross i j))
  have hpoint : qSum3 rows rows directions (fun i k j =>
      (((rowWeight i * rowWeight k) * directionWeight j) *
        (2 * (norm i * (cross k j * cross k j) +
              norm k * (cross i j * cross i j)) +
          8 * sigma i k * cross i j * cross k j))) ≈
      qSum3 rows rows directions (fun i k j =>
        (2 * first i k j + 2 * second i k j) + 8 * mixed i k j) :=
    qSum3_congr rows rows directions _ _ (fun i _ k _ j _ => by
      simp only [first, second, mixed]
      exact poly_identity_of_normal_eq
        (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.add
            (.mul (.const 2)
              (.add
                (.mul (.var 3) (.mul (.var 4) (.var 4)))
                (.mul (.var 5) (.mul (.var 6) (.var 6)))))
            (.mul (.mul (.mul (.const 8) (.var 7)) (.var 6)) (.var 4))))
        (.add
          (.add
            (.mul (.const 2)
              (.mul (.mul (.var 0) (.var 3))
                (.mul (.mul (.var 1) (.var 2)) (.mul (.var 4) (.var 4)))))
            (.mul (.const 2)
              (.mul (.mul (.var 1) (.var 5))
                (.mul (.mul (.var 0) (.var 2)) (.mul (.var 6) (.var 6))))))
          (.mul (.const 8)
            (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2))
              (.mul (.mul (.var 7) (.var 6)) (.var 4)))))
        (by decide) (fun
          | 0 => rowWeight i
          | 1 => rowWeight k
          | 2 => directionWeight j
          | 3 => norm i
          | 4 => cross k j
          | 5 => norm k
          | 6 => cross i j
          | _ => sigma i k))
  have hlinear := qSum3_linear_three rows rows directions 2 2 8 first second mixed
  have hfirst : qSum3 rows rows directions first ≈
      qSum rows (fun i => rowWeight i * norm i) * gramSquare := by
    exact Q'.eqv_trans _ _ _
      (qSum_congr rows _ _ (fun i _ => qSum2_scale (rowWeight i * norm i)
        rows directions (fun k j =>
          (rowWeight k * directionWeight j) * (cross k j * cross k j))))
      (qSum_scale_right rows (fun i => rowWeight i * norm i) gramSquare)
  have hsecond : qSum3 rows rows directions second ≈
      qSum rows (fun i => rowWeight i * norm i) * gramSquare := by
    have hrow : ∀ i, qSum2 rows directions (second i) ≈
        qSum rows (fun k => rowWeight k * norm k) *
          qSum directions (fun j =>
            (rowWeight i * directionWeight j) * (cross i j * cross i j)) := fun i =>
      qSum2_separable rows directions
        (fun k => rowWeight k * norm k)
        (fun j => (rowWeight i * directionWeight j) * (cross i j * cross i j))
    exact Q'.eqv_trans _ _ _
      (qSum_congr rows _ _ (fun i _ => hrow i))
      (qSum_scale (qSum rows (fun k => rowWeight k * norm k)) rows
        (fun i => qSum directions (fun j =>
          (rowWeight i * directionWeight j) * (cross i j * cross i j))))
  exact Q'.eqv_trans _ _ _ hpoint
    (Q'.eqv_trans _ _ _ hlinear
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left _ _ _ hfirst)
            (Q'.mul_eqv_congr_left _ _ _ hsecond))
          (Q'.eqv_refl _))
        (poly_identity_of_normal_eq
          (.add
            (.add
              (.mul (.const 2) (.mul (.var 0) (.var 1)))
              (.mul (.const 2) (.mul (.var 0) (.var 1))))
            (.mul (.const 8) (.var 2)))
          (.add (.mul (.const 8) (.var 2))
            (.mul (.mul (.const 4) (.var 0)) (.var 1)))
          (by decide) (fun
            | 0 => qSum rows (fun i => rowWeight i * norm i)
            | 1 => gramSquare
            | _ => qSum3 rows rows directions mixed))))

/-- Rationally weighted `Tr(Sigma)`, kept as a literal finite row sum. -/
def finiteWeightedRowGramTrace (N rowCount : Nat)
    (rowWeights : Nat → Q') (b : Nat → Nat → Q') : Q' :=
  qListSum ((List.range rowCount).map fun i =>
    rowWeights i * finiteRowNorm2 N (b i))

/-- Rationally weighted `Tr(Sigma*K*K^*)`, kept as a literal triple Gram
contraction. -/
def finiteWeightedGramSandwichTrace (N rowCount directionCount : Nat)
    (rowWeights directionWeights : Nat → Q')
    (b d : Nat → Nat → Q') : Q' :=
  qListSum ((List.range rowCount).map fun i =>
    qListSum ((List.range rowCount).map fun k =>
      qListSum ((List.range directionCount).map fun j =>
        (((rowWeights i * rowWeights k) * directionWeights j) *
          (finiteRowGram N (b i) (b k) * finiteRowGram N (b i) (d j) *
            finiteRowGram N (b k) (d j))))))

private theorem unitWeightedGram_eq_finiteRowGram
    (N : Nat) (b : Nat → Nat → Q') (left right : Nat) :
    weightedGram (List.range N) (fun _ => (1 : Q'))
        (fun row coordinate => b row coordinate) left right ≈
      finiteRowGram N (b left) (b right) := by
  unfold weightedGram finiteRowGram
  rw [qListSum_map_eq_listQSum_local]
  exact listQSum_congr
    (fun coordinate => Q'.one_mul_eqv (b left coordinate * b right coordinate))
    (List.range N)

/-- The weighted Gram-sandwich trace is exactly a direction-weighted sum of
finite Gram quadratic forms.  Source weights occur as quadratic-form
coefficients, so only the direction weights need a sign premise. -/
theorem finiteWeightedGramSandwichTrace_eq_weightedGramQuadratic
    (N rowCount directionCount : Nat)
    (rowWeights directionWeights : Nat → Q')
    (b d : Nat → Nat → Q') :
    finiteWeightedGramSandwichTrace N rowCount directionCount
        rowWeights directionWeights b d ≈
      listQSum
        (fun j => directionWeights j *
          weightedGramQuadratic
            (List.range rowCount) (List.range N)
            (fun _ => (1 : Q'))
            (fun row coordinate => b row coordinate)
            (fun i => rowWeights i * finiteRowGram N (b i) (d j)))
        (List.range directionCount) := by
  let term := fun i : Nat => fun k : Nat => fun j : Nat =>
    (((rowWeights i * rowWeights k) * directionWeights j) *
      (finiteRowGram N (b i) (b k) * finiteRowGram N (b i) (d j) *
        finiteRowGram N (b k) (d j)))
  unfold finiteWeightedGramSandwichTrace
  simp only [qListSum_map_eq_listQSum_local]
  change
    listQSum
        (fun i => listQSum
          (fun k => listQSum (fun j => term i k j) (List.range directionCount))
          (List.range rowCount))
        (List.range rowCount) ≈ _
  have hswapInner :
      listQSum
          (fun i => listQSum
            (fun k => listQSum (fun j => term i k j) (List.range directionCount))
            (List.range rowCount))
          (List.range rowCount) ≈
        listQSum
          (fun i => listQSum
            (fun j => listQSum (fun k => term i k j) (List.range rowCount))
            (List.range directionCount))
          (List.range rowCount) :=
    listQSum_congr
      (fun i => Q'.eqv_symm
        (listQSum_swap (fun k j => term i k j)
          (List.range rowCount) (List.range directionCount)))
      (List.range rowCount)
  have hswapOuter :
      listQSum
          (fun i => listQSum
            (fun j => listQSum (fun k => term i k j) (List.range rowCount))
            (List.range directionCount))
          (List.range rowCount) ≈
        listQSum
          (fun j => listQSum
            (fun i => listQSum (fun k => term i k j) (List.range rowCount))
            (List.range rowCount))
          (List.range directionCount) :=
    Q'.eqv_symm
      (listQSum_swap
        (fun i j => listQSum (fun k => term i k j) (List.range rowCount))
        (List.range rowCount) (List.range directionCount))
  have hdirection : ∀ j,
      listQSum
          (fun i => listQSum (fun k => term i k j) (List.range rowCount))
          (List.range rowCount) ≈
        directionWeights j *
          weightedGramQuadratic
            (List.range rowCount) (List.range N)
            (fun _ => (1 : Q'))
            (fun row coordinate => b row coordinate)
            (fun i => rowWeights i * finiteRowGram N (b i) (d j)) := by
    intro j
    let quadraticTerm := fun i : Nat => fun k : Nat =>
      ((rowWeights i * finiteRowGram N (b i) (d j)) *
          (rowWeights k * finiteRowGram N (b k) (d j))) *
        weightedGram (List.range N) (fun _ => (1 : Q'))
          (fun row coordinate => b row coordinate) i k
    have hterm : ∀ i k, term i k j ≈
        directionWeights j * quadraticTerm i k := by
      intro i k
      have hrearrange : term i k j ≈
          directionWeights j *
            (((rowWeights i * finiteRowGram N (b i) (d j)) *
                (rowWeights k * finiteRowGram N (b k) (d j))) *
              finiteRowGram N (b i) (b k)) := by
        simp only [term]
        exact poly_identity_of_normal_eq
          (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2))
            (.mul (.mul (.var 3) (.var 4)) (.var 5)))
          (.mul (.var 2)
            (.mul
              (.mul (.mul (.var 0) (.var 4))
                (.mul (.var 1) (.var 5)))
              (.var 3)))
          (by decide) (fun
            | 0 => rowWeights i
            | 1 => rowWeights k
            | 2 => directionWeights j
            | 3 => finiteRowGram N (b i) (b k)
            | 4 => finiteRowGram N (b i) (d j)
            | _ => finiteRowGram N (b k) (d j))
      exact Q'.eqv_trans _ _ _ hrearrange
        (Q'.mul_eqv_congr_left (directionWeights j) _ _
          (Q'.mul_eqv_congr_left
            ((rowWeights i * finiteRowGram N (b i) (d j)) *
              (rowWeights k * finiteRowGram N (b k) (d j)))
            (finiteRowGram N (b i) (b k))
            (weightedGram (List.range N) (fun _ => (1 : Q'))
              (fun row coordinate => b row coordinate) i k)
            (Q'.eqv_symm (unitWeightedGram_eq_finiteRowGram N b i k))))
    unfold weightedGramQuadratic
    exact Q'.eqv_trans _ _ _
      (listQSum_congr
        (fun i => listQSum_congr (fun k => hterm i k) (List.range rowCount))
        (List.range rowCount))
      (Q'.eqv_trans _ _ _
        (listQSum_congr
          (fun i => listQSum_mul_left (directionWeights j)
            (quadraticTerm i) (List.range rowCount))
          (List.range rowCount))
        (listQSum_mul_left (directionWeights j)
          (fun i => listQSum (quadraticTerm i) (List.range rowCount))
          (List.range rowCount)))
  exact Q'.eqv_trans _ _ _ hswapInner
    (Q'.eqv_trans _ _ _ hswapOuter
      (listQSum_congr hdirection (List.range directionCount)))

/-- Constructive nonnegativity of the weighted Gram-sandwich trace. -/
theorem finiteWeightedGramSandwichTrace_nonnegative
    (N rowCount directionCount : Nat)
    (rowWeights directionWeights : Nat → Q')
    (b d : Nat → Nat → Q')
    (hdirection : ∀ j, j ∈ List.range directionCount →
      (0 : Q') ≤ directionWeights j) :
    (0 : Q') ≤ finiteWeightedGramSandwichTrace N rowCount directionCount
      rowWeights directionWeights b d := by
  have heq := finiteWeightedGramSandwichTrace_eq_weightedGramQuadratic
    N rowCount directionCount rowWeights directionWeights b d
  have hsum : (0 : Q') ≤
      listQSum
        (fun j => directionWeights j *
          weightedGramQuadratic
            (List.range rowCount) (List.range N)
            (fun _ => (1 : Q'))
            (fun row coordinate => b row coordinate)
            (fun i => rowWeights i * finiteRowGram N (b i) (d j)))
        (List.range directionCount) := by
    apply listQSum_nonnegative_on
    intro j hj
    exact Q'.mul_nonneg _ _ (hdirection j hj)
      (weightedGramQuadratic_nonnegative
        (List.range rowCount) (List.range N)
        (fun _ => (1 : Q'))
        (fun row coordinate => b row coordinate)
        (fun i => rowWeights i * finiteRowGram N (b i) (d j))
        (fun _ _ => Q'.zero_le_one))
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (Q'.eqv_symm heq))

private theorem finiteRowNorm2_nonnegative (N : Nat) (row : Nat → Q') :
    (0 : Q') ≤ finiteRowNorm2 N row := by
  unfold finiteRowNorm2
  rw [qListSum_map_eq_listQSum_local]
  apply listQSum_nonnegative_on
  intro coordinate _
  exact q_mul_self_nonneg (row coordinate)

private theorem q_nonpos_of_not_pos {value : Q'}
    (hnot : ¬ (0 : Q') < value) : value ≤ 0 := by
  show value.num * (1 : Int) ≤ (0 : Int) * (value.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  exact Int.not_lt.mp (fun hnum => hnot (CReal.pos_of_num_pos hnum))

private theorem exists_mem_pos_of_listQSum_pos {A : Type} (value : A → Q') :
    ∀ items : List A,
      (0 : Q') < listQSum value items →
        Exists fun item => item ∈ items ∧ (0 : Q') < value item
  | [], hsum => by
      have hnum := Q'.num_pos_of_pos hsum
      simp only [listQSum] at hnum
      exact False.elim (Int.lt_irrefl 0 hnum)
  | head :: tail, hsum => by
      by_cases hhead : (0 : Q') < value head
      · exact Exists.intro head ⟨List.mem_cons_self, hhead⟩
      · have hheadLe : value head ≤ 0 := q_nonpos_of_not_pos hhead
        have hsumLe :
            value head + listQSum value tail ≤ listQSum value tail := by
          have hadd := Q'.add_le_add_right
            (value head) 0 (listQSum value tail) hheadLe
          simpa only [Q'.zero_add'] using hadd
        have htail : (0 : Q') < listQSum value tail := by
          change (0 : Q') < value head + listQSum value tail at hsum
          exact Q'.pos_of_lt_of_le hsum hsumLe
        rcases exists_mem_pos_of_listQSum_pos value tail htail with
          ⟨item, hitem, hitemPos⟩
        exact Exists.intro item
          ⟨List.mem_cons_of_mem head hitem, hitemPos⟩

private theorem listQSum_member_le_nonnegative {A : Type} (value : A → Q') :
    ∀ (items : List A) {witness : A},
      (∀ item, item ∈ items → (0 : Q') ≤ value item) →
      witness ∈ items →
      value witness ≤ listQSum value items
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, witness, hnonnegative, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst witness
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun item hitem =>
              hnonnegative item (List.mem_cons_of_mem head hitem)))
      · have htailLe := listQSum_member_le_nonnegative
          value tail
          (fun item hitem =>
            hnonnegative item (List.mem_cons_of_mem head hitem))
          htail
        have hsumLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail)
            (hnonnegative head List.mem_cons_self)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ htailLe hsumLe

private theorem listQSum_pos_of_mem_nonnegative {A : Type} (value : A → Q')
    (items : List A) {witness : A}
    (hnonnegative : ∀ item, item ∈ items → (0 : Q') ≤ value item)
    (hmem : witness ∈ items) (hwitness : (0 : Q') < value witness) :
    (0 : Q') < listQSum value items :=
  Q'.pos_of_lt_of_le hwitness
    (listQSum_member_le_nonnegative value items hnonnegative hmem)

/-- A strictly positive computed cross Gram constructively forces the left
row to have strictly positive computed squared norm. -/
theorem finiteRowNorm2_pos_of_finiteRowGram_pos
    (N : Nat) (left right : Nat → Q')
    (hgram : (0 : Q') < finiteRowGram N left right) :
    (0 : Q') < finiteRowNorm2 N left := by
  have hsum : (0 : Q') <
      listQSum (fun coordinate => left coordinate * right coordinate)
        (List.range N) := by
    unfold finiteRowGram at hgram
    rw [qListSum_map_eq_listQSum_local] at hgram
    exact hgram
  rcases exists_mem_pos_of_listQSum_pos
      (fun coordinate => left coordinate * right coordinate)
      (List.range N) hsum with
    ⟨coordinate, hcoordinate, hproduct⟩
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < (left coordinate).num * (right coordinate).num at hproductNum
  have hleftNumNonzero : (left coordinate).num ≠ 0 := by
    intro hzero
    rw [hzero, Int.zero_mul] at hproductNum
    exact Int.lt_irrefl 0 hproductNum
  have hsquare : (0 : Q') < left coordinate * left coordinate := by
    apply CReal.pos_of_num_pos
    by_cases hnegative : (left coordinate).num < 0
    · exact Int.mul_pos_of_neg_of_neg hnegative hnegative
    · have hnonnegative : (0 : Int) ≤ (left coordinate).num :=
        Int.not_lt.mp hnegative
      have hpositive : (0 : Int) < (left coordinate).num := by omega
      exact Int.mul_pos hpositive hpositive
  unfold finiteRowNorm2
  rw [qListSum_map_eq_listQSum_local]
  exact listQSum_pos_of_mem_nonnegative
    (fun coordinate => left coordinate * left coordinate)
    (List.range N)
    (fun coordinate _ => q_mul_self_nonneg (left coordinate))
    hcoordinate hsquare

/-- Nonnegativity of the weighted row Gram trace for nonnegative row
weights. -/
theorem finiteWeightedRowGramTrace_nonnegative
    (N rowCount : Nat) (rowWeights : Nat → Q') (b : Nat → Nat → Q')
    (hrow : ∀ i, i ∈ List.range rowCount → (0 : Q') ≤ rowWeights i) :
    (0 : Q') ≤ finiteWeightedRowGramTrace N rowCount rowWeights b := by
  unfold finiteWeightedRowGramTrace
  rw [qListSum_map_eq_listQSum_local]
  apply listQSum_nonnegative_on
  intro i hi
  exact Q'.mul_nonneg _ _ (hrow i hi) (finiteRowNorm2_nonnegative N (b i))

/-- Any selected nonnegative weighted row term is retained by the complete
weighted row Gram trace. -/
theorem finiteWeightedRowGramTrace_member_le
    (N rowCount : Nat) (rowWeights : Nat → Q') (b : Nat → Nat → Q')
    (rowIndex : Nat) (hindex : rowIndex ∈ List.range rowCount)
    (hrow : ∀ i, i ∈ List.range rowCount → (0 : Q') ≤ rowWeights i) :
    rowWeights rowIndex * finiteRowNorm2 N (b rowIndex) ≤
      finiteWeightedRowGramTrace N rowCount rowWeights b := by
  unfold finiteWeightedRowGramTrace
  rw [qListSum_map_eq_listQSum_local]
  exact listQSum_member_le_nonnegative
    (fun i => rowWeights i * finiteRowNorm2 N (b i))
    (List.range rowCount)
    (fun i hi => Q'.mul_nonneg _ _ (hrow i hi)
      (finiteRowNorm2_nonnegative N (b i)))
    hindex

/-- Exact rationally weighted finite radial contraction:
`Cov(S_B^2,S_D)=8*Tr(Sigma*K*K^*)+4*Tr(Sigma)*Tr(K*K^*)`. -/
theorem finiteGaussianWeightedRadialCovariance_trace
    (N rowCount directionCount : Nat)
    (rowWeights directionWeights : Nat → Q')
    (b d : Nat → Nat → Q') :
    finiteGaussianCovariance N
      (polyMul
        (finiteGaussianWeightedRadialSquare N rowCount rowWeights b)
        (finiteGaussianWeightedRadialSquare N rowCount rowWeights b))
      (finiteGaussianWeightedRadialSquare
        N directionCount directionWeights d) ≈
      8 * finiteWeightedGramSandwichTrace N rowCount directionCount
          rowWeights directionWeights b d +
        4 * finiteWeightedRowGramTrace N rowCount rowWeights b *
          finiteWeightedCrossGramSquareTrace N rowCount directionCount
            rowWeights directionWeights b d := by
  exact Q'.eqv_trans _ _ _
    (finiteGaussianWeightedRadialCovariance_summands
      N rowCount directionCount rowWeights directionWeights b d)
    (weighted_radial_sum_scalar
      (List.range rowCount) (List.range directionCount)
      rowWeights directionWeights
      (fun i => finiteRowNorm2 N (b i))
      (fun i k => finiteRowGram N (b i) (b k))
      (fun i j => finiteRowGram N (b i) (d j)))

end YMGap.Continuum.SU2QuaternionFiniteGaussianWeightedRadialCovariance

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianWeightedRadialCovariance.finiteGaussianCovariance_weighted_three_square
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianWeightedRadialCovariance.finiteGaussianWeightedRadialCovariance_summands
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianWeightedRadialCovariance.finiteGaussianWeightedRadialCovariance_trace
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianWeightedRadialCovariance.finiteWeightedGramSandwichTrace_eq_weightedGramQuadratic
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianWeightedRadialCovariance.finiteWeightedGramSandwichTrace_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianWeightedRadialCovariance.finiteWeightedRowGramTrace_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianWeightedRadialCovariance.finiteRowNorm2_pos_of_finiteRowGram_pos
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianWeightedRadialCovariance.finiteWeightedRowGramTrace_member_le
