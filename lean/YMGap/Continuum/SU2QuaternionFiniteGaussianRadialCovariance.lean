/-
# Finite rational-row radial quartic covariance

This leaf sums the checked row-square and three-square covariances over literal
finite row families. For S_B=sum_i (b_i dot X)^2 and
S_D=sum_j (d_j dot X)^2 it proves

  Cov(S_B,S_D) = 2*Tr(K*K^*),

  Cov(S_B^2,S_D)
    = 8*Tr(Sigma*K*K^*) + 4*Tr(Sigma)*Tr(K*K^*),

where every displayed trace is defined below as an explicit finite rational
sum of the computed row Grams. There is no matrix, Gaussian pullback, moment,
independence, nondegeneracy or change-of-basis premise. Empty families, zero
rows and every finite evaluator dimension are included.

For the actual rational source coefficients it also proves the weighted
quadratic identity

  Cov(sum_i u_i*(b_i dot X)^2, sum_j v_j*(d_j dot X)^2)
    = 2*sum_ij u_i*v_j*Gram(b_i,d_j)^2.

The coefficients multiply row squares directly, so no irrational square-root
rescaling of rows is introduced.

The consumer is the retained trace-source quartic in the adaptive-score audit.
Actual transverse-mode rows, CReal approximation moduli, the compact-Haar
comparison and the ORIGINAL interacting estimate remain separate obligations.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianSixthMoment

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP
open YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianSixthMoment

local infix:50 " ≈ " => Q'.eqv

/-- Literal square of one finite rational Gaussian row. -/
def finiteGaussianRowSquare (N : Nat) (row : Nat → Q') : RatPoly :=
  polyMul (finiteLinearRow N row) (finiteLinearRow N row)

/-- Literal radial square, with exactly `count` rows and no tail convention. -/
def finiteGaussianRadialSquare (N count : Nat) (rows : Nat → Nat → Q') : RatPoly :=
  polySum ((List.range count).map fun i => finiteGaussianRowSquare N (rows i))

/-- Literal rationally weighted radial square. The source coefficient
multiplies the row square itself; it is not absorbed into the row. -/
def finiteGaussianWeightedRadialSquare (N count : Nat)
    (weights : Nat → Q') (rows : Nat → Nat → Q') : RatPoly :=
  polySum ((List.range count).map fun i =>
    polySmul (weights i) (finiteGaussianRowSquare N (rows i)))

/-- Actual covariance under the existing finite product-Gaussian evaluator. -/
def finiteGaussianCovariance (N : Nat) (p q : RatPoly) : Q' :=
  finiteProductGaussian N (polyMul p q) -
    finiteProductGaussian N p * finiteProductGaussian N q

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a*b ≈ a'*b' :=
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

/-- Covariance of two literal squared rational Gaussian rows. -/
theorem finiteGaussianCovariance_row_square (N : Nat) (b d : Nat → Q') :
    finiteGaussianCovariance N
      (finiteGaussianRowSquare N b) (finiteGaussianRowSquare N d) ≈
      2 * (finiteRowGram N b d * finiteRowGram N b d) := by
  have hb :
      finiteProductGaussian N
          (polyMul (finiteLinearRow N b) (finiteLinearRow N b)) ≈
        finiteRowNorm2 N b := by
    exact Q'.eqv_trans _ _ _
      (finiteProductGaussian_row_pair N b b) (Q'.eqv_refl _)
  have hd :
      finiteProductGaussian N
          (polyMul (finiteLinearRow N d) (finiteLinearRow N d)) ≈
        finiteRowNorm2 N d := by
    exact Q'.eqv_trans _ _ _
      (finiteProductGaussian_row_pair N d d) (Q'.eqv_refl _)
  unfold finiteGaussianCovariance finiteGaussianRowSquare
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (finiteProductGaussian_row_square_pair N b d)
      (Q'.neg_eqv_congr _ _ (mul_congr hb hd)))
    (poly_identity_of_normal_eq
      (.add
        (.add (.mul (.var 0) (.var 1))
          (.mul (.const 2) (.mul (.var 2) (.var 2))))
        (.neg (.mul (.var 0) (.var 1))))
      (.mul (.const 2) (.mul (.var 2) (.var 2)))
      (by decide) (fun
        | 0 => finiteRowNorm2 N b
        | 1 => finiteRowNorm2 N d
        | _ => finiteRowGram N b d))

/-- Covariance of two rationally weighted squared Gaussian rows. -/
theorem finiteGaussianCovariance_weighted_row_square
    (N : Nat) (leftWeight rightWeight : Q') (b d : Nat → Q') :
    finiteGaussianCovariance N
        (polySmul leftWeight (finiteGaussianRowSquare N b))
        (polySmul rightWeight (finiteGaussianRowSquare N d)) ≈
      2 * ((leftWeight * rightWeight) *
        (finiteRowGram N b d * finiteRowGram N b d)) := by
  exact Q'.eqv_trans _ _ _
    (covariance_smul N leftWeight rightWeight
      (finiteGaussianRowSquare N b) (finiteGaussianRowSquare N d))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (finiteGaussianCovariance_row_square N b d))
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1))
          (.mul (.const 2) (.mul (.var 2) (.var 2))))
        (.mul (.const 2)
          (.mul (.mul (.var 0) (.var 1))
            (.mul (.var 2) (.var 2))))
        (by decide) (fun
          | 0 => leftWeight
          | 1 => rightWeight
          | _ => finiteRowGram N b d)))

private theorem radial_pair_covariance_expansion
    (N rowCount directionCount : Nat) (b d : Nat → Nat → Q') :
    finiteGaussianCovariance N
        (finiteGaussianRadialSquare N rowCount b)
        (finiteGaussianRadialSquare N directionCount d) ≈
      qListSum ((List.range rowCount).map fun i =>
        qListSum ((List.range directionCount).map fun j =>
          finiteGaussianCovariance N
            (finiteGaussianRowSquare N (b i))
            (finiteGaussianRowSquare N (d j)))) := by
  let bs := (List.range rowCount).map fun i => finiteGaussianRowSquare N (b i)
  let ds := (List.range directionCount).map fun j => finiteGaussianRowSquare N (d j)
  have houter := covariance_polySum_left N (polySum ds) bs
  have hinner :
      qListSum (bs.map fun p => finiteGaussianCovariance N p (polySum ds)) ≈
        qListSum (bs.map fun p =>
          qListSum (ds.map fun q => finiteGaussianCovariance N p q)) :=
    qListSum_congr _ _ bs (fun p _ => covariance_polySum_right N p ds)
  simpa only [finiteGaussianRadialSquare, bs, ds, List.map_map] using
    (Q'.eqv_trans _ _ _ houter hinner)

private theorem weighted_radial_pair_covariance_expansion
    (N rowCount directionCount : Nat)
    (rowWeights directionWeights : Nat → Q')
    (b d : Nat → Nat → Q') :
    finiteGaussianCovariance N
        (finiteGaussianWeightedRadialSquare N rowCount rowWeights b)
        (finiteGaussianWeightedRadialSquare
          N directionCount directionWeights d) ≈
      qListSum ((List.range rowCount).map fun i =>
        qListSum ((List.range directionCount).map fun j =>
          finiteGaussianCovariance N
            (polySmul (rowWeights i) (finiteGaussianRowSquare N (b i)))
            (polySmul (directionWeights j)
              (finiteGaussianRowSquare N (d j))))) := by
  let bs := (List.range rowCount).map fun i =>
    polySmul (rowWeights i) (finiteGaussianRowSquare N (b i))
  let ds := (List.range directionCount).map fun j =>
    polySmul (directionWeights j) (finiteGaussianRowSquare N (d j))
  have houter := covariance_polySum_left N (polySum ds) bs
  have hinner :
      qListSum (bs.map fun p => finiteGaussianCovariance N p (polySum ds)) ≈
        qListSum (bs.map fun p =>
          qListSum (ds.map fun q => finiteGaussianCovariance N p q)) :=
    qListSum_congr _ _ bs (fun p _ => covariance_polySum_right N p ds)
  simpa only [finiteGaussianWeightedRadialSquare, bs, ds, List.map_map] using
    (Q'.eqv_trans _ _ _ houter hinner)

private theorem radial_covariance_expansion (N rowCount directionCount : Nat)
    (b d : Nat → Nat → Q') :
    finiteGaussianCovariance N
      (polyMul (finiteGaussianRadialSquare N rowCount b)
        (finiteGaussianRadialSquare N rowCount b))
      (finiteGaussianRadialSquare N directionCount d) ≈
      qListSum ((List.range rowCount).map fun i =>
        qListSum ((List.range rowCount).map fun k =>
          qListSum ((List.range directionCount).map fun j =>
            finiteGaussianCovariance N
              (polyMul (finiteGaussianRowSquare N (b i))
                (finiteGaussianRowSquare N (b k)))
              (finiteGaussianRowSquare N (d j))))) := by
  let bs := (List.range rowCount).map fun i => finiteGaussianRowSquare N (b i)
  let ds := (List.range directionCount).map fun j => finiteGaussianRowSquare N (d j)
  have houter : finiteGaussianCovariance N (polyMul (polySum bs) (polySum bs)) (polySum ds) ≈
      qListSum (bs.map fun p => finiteGaussianCovariance N (polyMul p (polySum bs)) (polySum ds)) :=
    Q'.eqv_trans _ _ _
      (covariance_congr N (RatPolyCoeffEqv.polySum_mul_right bs (polySum bs))
        (RatPolyCoeffEqv.refl _))
      (by
        simpa only [List.map_map] using
          (covariance_polySum_left N (polySum ds)
            (bs.map fun p => polyMul p (polySum bs))))
  have hmiddle : qListSum (bs.map fun p => finiteGaussianCovariance N (polyMul p (polySum bs)) (polySum ds)) ≈
      qListSum (bs.map fun p => qListSum (bs.map fun q =>
        finiteGaussianCovariance N (polyMul p q) (polySum ds))) :=
    qListSum_congr _ _ bs (fun p _ =>
      Q'.eqv_trans _ _ _
        (covariance_congr N (RatPolyCoeffEqv.mul_polySum_right p bs)
          (RatPolyCoeffEqv.refl _))
        (by
          simpa only [List.map_map] using
            (covariance_polySum_left N (polySum ds) (bs.map fun q => polyMul p q))))
  have hinner : qListSum (bs.map fun p => qListSum (bs.map fun q =>
      finiteGaussianCovariance N (polyMul p q) (polySum ds))) ≈
      qListSum (bs.map fun p => qListSum (bs.map fun q => qListSum (ds.map fun r =>
        finiteGaussianCovariance N (polyMul p q) r))) :=
    qListSum_congr _ _ bs (fun p _ => qListSum_congr _ _ bs (fun q _ =>
      covariance_polySum_right N (polyMul p q) ds))
  have htotal := Q'.eqv_trans _ _ _ houter (Q'.eqv_trans _ _ _ hmiddle hinner)
  simpa only [finiteGaussianRadialSquare, bs, ds, List.map_map] using htotal

/-- The checked sixth-order covariance formula, written through the literal
row-square and covariance definitions used by the radial finite sum. -/
theorem finiteGaussianCovariance_three_square (N : Nat) (b d e : Nat → Q') :
    finiteGaussianCovariance N
      (polyMul (finiteGaussianRowSquare N b) (finiteGaussianRowSquare N d))
      (finiteGaussianRowSquare N e) ≈
      2 * (finiteRowNorm2 N b * (finiteRowGram N d e * finiteRowGram N d e) +
        finiteRowNorm2 N d * (finiteRowGram N b e * finiteRowGram N b e)) +
      8 * finiteRowGram N b d * finiteRowGram N b e * finiteRowGram N d e := by
  unfold finiteGaussianCovariance finiteGaussianRowSquare
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (finiteProductGaussian_coeffEqv N
        (RatPolyCoeffEqv.mul_assoc
          (polyMul (finiteLinearRow N b) (finiteLinearRow N b))
          (polyMul (finiteLinearRow N d) (finiteLinearRow N d))
          (polyMul (finiteLinearRow N e) (finiteLinearRow N e))))
      (Q'.eqv_refl _))
    (finiteProductGaussian_three_square_covariance N b d e)

/-- Finite radial summation of every checked three-square covariance summand.
This is already the full covariance of the literal radial quartic and radial
quadratic; the next theorem contracts this sum to the trace expression. -/
theorem finiteGaussianRadialCovariance_summands (N rowCount directionCount : Nat)
    (b d : Nat → Nat → Q') :
    finiteGaussianCovariance N
      (polyMul (finiteGaussianRadialSquare N rowCount b)
        (finiteGaussianRadialSquare N rowCount b))
      (finiteGaussianRadialSquare N directionCount d) ≈
      qListSum (List.map (fun i =>
        qListSum (List.map (fun k =>
          qListSum (List.map (fun j =>
            2 * (finiteRowNorm2 N (b i) *
                (finiteRowGram N (b k) (d j) * finiteRowGram N (b k) (d j)) +
              finiteRowNorm2 N (b k) *
                (finiteRowGram N (b i) (d j) * finiteRowGram N (b i) (d j))) +
            8 * finiteRowGram N (b i) (b k) * finiteRowGram N (b i) (d j) *
              finiteRowGram N (b k) (d j)) (List.range directionCount)))
          (List.range rowCount))) (List.range rowCount)) := by
  exact Q'.eqv_trans _ _ _ (radial_covariance_expansion N rowCount directionCount b d)
    (qListSum_congr _ _ (List.range rowCount) (fun i _ =>
      qListSum_congr _ _ (List.range rowCount) (fun k _ =>
        qListSum_congr _ _ (List.range directionCount) (fun j _ =>
          finiteGaussianCovariance_three_square N (b i) (b k) (d j)))))

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

private theorem radial_sum_scalar {A B : Type} (rows : List A) (directions : List B)
    (norm : A → Q') (sigma : A → A → Q') (cross : A → B → Q') :
    qSum3 rows rows directions (fun i k j =>
      2 * (norm i * (cross k j * cross k j) + norm k * (cross i j * cross i j)) +
        8 * sigma i k * cross i j * cross k j) ≈
      8 * qSum3 rows rows directions (fun i k j => sigma i k * cross i j * cross k j) +
        4 * qSum rows norm * qSum2 rows directions (fun i j => cross i j * cross i j) := by
  let first := fun i : A => fun k : A => fun j : B => norm i * (cross k j * cross k j)
  let second := fun i : A => fun k : A => fun j : B => norm k * (cross i j * cross i j)
  let mixed := fun i : A => fun k : A => fun j : B => sigma i k * cross i j * cross k j
  let gramSquare := qSum2 rows directions (fun i j => cross i j * cross i j)
  have hpoint : qSum3 rows rows directions (fun i k j =>
      2 * (norm i * (cross k j * cross k j) + norm k * (cross i j * cross i j)) +
        8 * sigma i k * cross i j * cross k j) ≈
      qSum3 rows rows directions (fun i k j =>
        (2 * first i k j + 2 * second i k j) + 8 * mixed i k j) :=
    qSum3_congr rows rows directions _ _ (fun i _ k _ j _ => by
      simp only [first, second, mixed]
      exact poly_identity_of_normal_eq
        (.add (.mul (.const 2) (.add (.var 0) (.var 1)))
          (.mul (.mul (.mul (.const 8) (.var 2)) (.var 3)) (.var 4)))
        (.add (.add (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 1)))
          (.mul (.const 8) (.mul (.mul (.var 2) (.var 3)) (.var 4))))
        (by decide) (fun
          | 0 => norm i * (cross k j * cross k j)
          | 1 => norm k * (cross i j * cross i j)
          | 2 => sigma i k
          | 3 => cross i j
          | _ => cross k j))
  have hlinear := qSum3_linear_three rows rows directions 2 2 8 first second mixed
  have hfirst : qSum3 rows rows directions first ≈ qSum rows norm * gramSquare := by
    exact Q'.eqv_trans _ _ _
      (qSum_congr rows _ _ (fun i _ => qSum2_scale (norm i) rows directions
        (fun k j => cross k j * cross k j)))
      (qSum_scale_right rows norm gramSquare)
  have hsecond : qSum3 rows rows directions second ≈ qSum rows norm * gramSquare := by
    have hrow : ∀ i, qSum2 rows directions (second i) ≈
        qSum rows norm * qSum directions (fun j => cross i j * cross i j) := fun i =>
      qSum2_separable rows directions norm (fun j => cross i j * cross i j)
    exact Q'.eqv_trans _ _ _
      (qSum_congr rows _ _ (fun i _ => hrow i))
      (qSum_scale (qSum rows norm) rows
        (fun i => qSum directions (fun j => cross i j * cross i j)))
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
          (.add (.mul (.const 8) (.var 2)) (.mul (.mul (.const 4) (.var 0)) (.var 1)))
          (by decide) (fun
            | 0 => qSum rows norm
            | 1 => gramSquare
            | _ => qSum3 rows rows directions mixed))))

/-- `Tr(Sigma)`, defined as the literal sum of computed row norms. -/
def finiteRowGramTrace (N rowCount : Nat) (b : Nat → Nat → Q') : Q' :=
  qListSum ((List.range rowCount).map fun i => finiteRowNorm2 N (b i))

/-- `Tr(K*K^*)`, defined as the literal sum of squared computed cross Grams. -/
def finiteCrossGramSquareTrace (N rowCount directionCount : Nat)
    (b d : Nat → Nat → Q') : Q' :=
  qListSum ((List.range rowCount).map fun i =>
    qListSum ((List.range directionCount).map fun j =>
      finiteRowGram N (b i) (d j) * finiteRowGram N (b i) (d j)))

/-- Rationally weighted `Tr(K*K^*)`, kept as a literal double sum so source
weights never require square roots. -/
def finiteWeightedCrossGramSquareTrace (N rowCount directionCount : Nat)
    (rowWeights directionWeights : Nat → Q')
    (b d : Nat → Nat → Q') : Q' :=
  qListSum ((List.range rowCount).map fun i =>
    qListSum ((List.range directionCount).map fun j =>
      (rowWeights i * directionWeights j) *
        (finiteRowGram N (b i) (d j) * finiteRowGram N (b i) (d j))))

/-- Exact finite rational-row quadratic radial contraction:
`Cov(S_B,S_D)=2*Tr(K*K^*)`. -/
theorem finiteGaussianRadialPairCovariance_trace
    (N rowCount directionCount : Nat) (b d : Nat → Nat → Q') :
    finiteGaussianCovariance N
        (finiteGaussianRadialSquare N rowCount b)
        (finiteGaussianRadialSquare N directionCount d) ≈
      2 * finiteCrossGramSquareTrace N rowCount directionCount b d := by
  refine Q'.eqv_trans _ _ _
    (radial_pair_covariance_expansion N rowCount directionCount b d) ?_
  refine Q'.eqv_trans _ _ _
    (qListSum_congr _ _ (List.range rowCount) (fun i _ =>
      qListSum_congr _ _ (List.range directionCount) (fun j _ =>
        finiteGaussianCovariance_row_square N (b i) (d j)))) ?_
  unfold finiteCrossGramSquareTrace
  change qSum2 (List.range rowCount) (List.range directionCount)
      (fun i j => 2 *
        (finiteRowGram N (b i) (d j) * finiteRowGram N (b i) (d j))) ≈
    2 * qSum2 (List.range rowCount) (List.range directionCount)
      (fun i j => finiteRowGram N (b i) (d j) * finiteRowGram N (b i) (d j))
  exact qSum2_scale 2 (List.range rowCount) (List.range directionCount)
    (fun i j => finiteRowGram N (b i) (d j) * finiteRowGram N (b i) (d j))

/-- Exact finite rational-row weighted quadratic contraction:
`Cov(sum_i u_i*(b_i dot X)^2, sum_j v_j*(d_j dot X)^2)
  = 2*sum_ij u_i*v_j*Gram(b_i,d_j)^2`. -/
theorem finiteGaussianWeightedRadialPairCovariance_trace
    (N rowCount directionCount : Nat)
    (rowWeights directionWeights : Nat → Q')
    (b d : Nat → Nat → Q') :
    finiteGaussianCovariance N
        (finiteGaussianWeightedRadialSquare N rowCount rowWeights b)
        (finiteGaussianWeightedRadialSquare
          N directionCount directionWeights d) ≈
      2 * finiteWeightedCrossGramSquareTrace N rowCount directionCount
        rowWeights directionWeights b d := by
  refine Q'.eqv_trans _ _ _
    (weighted_radial_pair_covariance_expansion
      N rowCount directionCount rowWeights directionWeights b d) ?_
  refine Q'.eqv_trans _ _ _
    (qListSum_congr _ _ (List.range rowCount) (fun i _ =>
      qListSum_congr _ _ (List.range directionCount) (fun j _ =>
        finiteGaussianCovariance_weighted_row_square N
          (rowWeights i) (directionWeights j) (b i) (d j)))) ?_
  unfold finiteWeightedCrossGramSquareTrace
  change qSum2 (List.range rowCount) (List.range directionCount)
      (fun i j => 2 * ((rowWeights i * directionWeights j) *
        (finiteRowGram N (b i) (d j) * finiteRowGram N (b i) (d j)))) ≈
    2 * qSum2 (List.range rowCount) (List.range directionCount)
      (fun i j => (rowWeights i * directionWeights j) *
        (finiteRowGram N (b i) (d j) * finiteRowGram N (b i) (d j)))
  exact qSum2_scale 2 (List.range rowCount) (List.range directionCount)
    (fun i j => (rowWeights i * directionWeights j) *
      (finiteRowGram N (b i) (d j) * finiteRowGram N (b i) (d j)))

/-- `Tr(Sigma*K*K^*)`, defined as the literal three-index Gram contraction. -/
def finiteGramSandwichTrace (N rowCount directionCount : Nat)
    (b d : Nat → Nat → Q') : Q' :=
  qListSum ((List.range rowCount).map fun i =>
    qListSum ((List.range rowCount).map fun k =>
      qListSum ((List.range directionCount).map fun j =>
        finiteRowGram N (b i) (b k) * finiteRowGram N (b i) (d j) *
          finiteRowGram N (b k) (d j))))

/-- Exact finite rational-row radial contraction:
`Cov(S_B^2,S_D)=8*Tr(Sigma*K*K^*)+4*Tr(Sigma)*Tr(K*K^*)`. -/
theorem finiteGaussianRadialCovariance_trace (N rowCount directionCount : Nat)
    (b d : Nat → Nat → Q') :
    finiteGaussianCovariance N
      (polyMul (finiteGaussianRadialSquare N rowCount b)
        (finiteGaussianRadialSquare N rowCount b))
      (finiteGaussianRadialSquare N directionCount d) ≈
      8 * finiteGramSandwichTrace N rowCount directionCount b d +
        4 * finiteRowGramTrace N rowCount b *
          finiteCrossGramSquareTrace N rowCount directionCount b d := by
  exact Q'.eqv_trans _ _ _
    (finiteGaussianRadialCovariance_summands N rowCount directionCount b d)
    (radial_sum_scalar (List.range rowCount) (List.range directionCount)
      (fun i => finiteRowNorm2 N (b i))
      (fun i k => finiteRowGram N (b i) (b k))
      (fun i j => finiteRowGram N (b i) (d j)))

end YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance.finiteGaussianCovariance_three_square
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance.finiteGaussianCovariance_row_square
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance.finiteGaussianRadialPairCovariance_trace
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance.finiteGaussianCovariance_weighted_row_square
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance.finiteGaussianWeightedRadialPairCovariance_trace
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance.finiteGaussianRadialCovariance_summands
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance.finiteGaussianRadialCovariance_trace
