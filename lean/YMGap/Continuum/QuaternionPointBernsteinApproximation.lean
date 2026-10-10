/-
Actual pointwise Bernstein approximation by polynomials on rational unit
quaternions. The weights evaluate the original joint basis at the input;
they are NOT its Haar averages. Total rational sphere repair is paid by an
explicit 102/(n+1) squared-distance estimate, including zero raw nodes.

The function below is rational-valued on the actual dense UnitNorm carrier.
Its bound and continuity radius are explicit inputs describing that function,
not a supplied polynomial approximation. No continuous Haar or completed
Point-function extension is asserted by this finite approximation theorem.
-/

import YMGap.Continuum.QuaternionPointBernsteinConcentration
import YMGap.Continuum.RationalQuaternionCubeRepairDistance
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.QuaternionPointBernsteinApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionNormRepair
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.QPolyHaarPositiveSubstitution
open YMGap.Continuum.QuaternionHaarTensorBernsteinCubature
open YMGap.Continuum.QuaternionHaarTensorBernsteinNormDefect
open YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
open YMGap.Continuum.QuaternionHaarBernsteinCoordinateVariance
open YMGap.Continuum.QuaternionPointBernsteinConcentration
open YMGap.Continuum.RationalQuaternionCubeRepairDistance

local infix:50 " ≈ " => Q'.eqv

/-- Literal squared distance from actual repaired nodes to the input point. -/
def pointRepairedDistance (x : UnitNorm) (n : Nat) : Q' :=
  sum4 (fun a b c d => pointWeight x n a b c d *
    distSq (repairedQuaternion n a b c d).val x.val) (n+2)

/-- A uniform finite bound for the POINTWISE kernel, not the Haar weights. -/
theorem pointRepairedDistance_le (x : UnitNorm) (n : Nat) :
    pointRepairedDistance x n ≤ 102 * Q'.invSucc n := by
  have hsum : pointRepairedDistance x n ≤ 34 * pointRawDistance x n := by
    refine Q'.le_trans' _ _ _
      (sum4_le_lt _ (fun a b c d => 34 * (pointWeight x n a b c d *
        distSq (rawQuaternion n a b c d) x.val)) (n+2) ?_)
      (Q'.ge_of_eqv (sum4_const_mul 34 _ (n+2)))
    intro a b c d ha hb hc hd
    have hcube : ∀ i : Fin 4, coordinate (rawQuaternion n a b c d) i *
        coordinate (rawQuaternion n a b c d) i ≤ (1 : Q') := by
      intro i
      have h := rawNode_square_le_one n a b c d (by omega) (by omega)
        (by omega) (by omega) i
      simpa only [rawQuaternion_coordinate] using h
    have hr := repair_distance_le (rawQuaternion n a b c d) hcube x
    have hm := Q'.mul_le_mul_of_nonneg_left _ _ (pointWeight x n a b c d)
      hr (pointWeight_nonnegative x n a b c d)
    exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.const 34) (.var 1)))
        (.mul (.const 34) (.mul (.var 0) (.var 1)))
        (by decide) (fun
          | 0 => pointWeight x n a b c d
          | _ => distSq (rawQuaternion n a b c d) x.val)))
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (pointRawDistance_eq x n))
      (poly_identity_of_normal_eq
        (.mul (.const 34) (.mul (.const 3) (.var 0)))
        (.mul (.const 102) (.var 0)) (by decide)
        (fun _ => Q'.invSucc n))))

private def polynomialSum4 (f : Nat → Nat → Nat → Nat → RatPoly)
    (count : Nat) : RatPoly :=
  polySum (fun a => polySum (fun b => polySum (fun c =>
    polySum (fun d => f a b c d) count) count) count) count

/-- Actual signed rational coefficients sampled at actual rational unit nodes. -/
def approximationPolynomial (f : UnitNorm → Q') (n : Nat) : RatPoly :=
  polynomialSum4 (fun a b c d => polySmul (f (repairedQuaternion n a b c d))
    (jointBasisRaw n a b c d)) (n+2)

private theorem supported_scale {p : RatPoly} (hp : SupportedQuaternionBlocks 1 p)
    (c : Q') : SupportedQuaternionBlocks 1 (polySmul c p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem supported_subst {x : RatPoly} (hx : SupportedQuaternionBlocks 1 x) :
    ∀ p : Poly, SupportedQuaternionBlocks 1 (subst x p)
  | [] => by intro t ht; exact False.elim (List.not_mem_nil ht)
  | c::p => supported_add (supported_scale (supported_one 1) c)
      (supported_polyMul hx (supported_subst hx p))

private theorem basis_supported (n : Nat) (i : Fin 4) (k : Nat) :
    SupportedQuaternionBlocks 1 (coordinateBasis n i k) :=
  supported_subst
    (supported_subst (coordinateSquareBound 1 i.val (by omega)).support _) _

private theorem joint_supported (n a b c d : Nat) :
    SupportedQuaternionBlocks 1 (jointBasisRaw n a b c d) :=
  supported_polyMul (basis_supported n ⟨0,by decide⟩ a)
    (supported_polyMul (basis_supported n ⟨1,by decide⟩ b)
      (supported_polyMul (basis_supported n ⟨2,by decide⟩ c)
        (basis_supported n ⟨3,by decide⟩ d)))

private theorem polySum_supported (f : Nat → RatPoly)
    (hf : ∀ k, SupportedQuaternionBlocks 1 (f k)) :
    ∀ count, SupportedQuaternionBlocks 1 (polySum f count)
  | 0 => by intro t ht; exact False.elim (List.not_mem_nil ht)
  | count+1 => supported_add (polySum_supported f hf count) (hf count)

theorem approximationPolynomial_supported (f : UnitNorm → Q') (n : Nat) :
    SupportedQuaternionBlocks 1 (approximationPolynomial f n) :=
  polySum_supported _ (fun a => polySum_supported _ (fun b =>
    polySum_supported _ (fun c => polySum_supported _ (fun d =>
      supported_scale (joint_supported n a b c d) _) _) _) _) _

private theorem eval_polySum (rho : Nat → Q') (f : Nat → RatPoly) :
    ∀ count, evalRatPoly rho (polySum f count) ≈
      finSum (fun k => evalRatPoly rho (f k)) count
  | 0 => Q'.eqv_refl 0
  | count+1 => Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
      (Q'.add_eqv_congr_right _ _ _ (eval_polySum rho f count))

/-- Its value is the literal pointwise kernel average, with no Haar applied. -/
def approximateValue (f : UnitNorm → Q') (x : UnitNorm) (n : Nat) : Q' :=
  sum4 (fun a b c d => pointWeight x n a b c d *
    f (repairedQuaternion n a b c d)) (n+2)

theorem eval_approximationPolynomial (f : UnitNorm → Q') (x : UnitNorm) (n : Nat) :
    evalRatPoly (environmentOf x.val) (approximationPolynomial f n) ≈
      approximateValue f x n := by
  let rho := environmentOf x.val
  have he : evalRatPoly rho (approximationPolynomial f n) ≈
      sum4 (fun a b c d => evalRatPoly rho
        (polySmul (f (repairedQuaternion n a b c d)) (jointBasisRaw n a b c d)))
        (n+2) := by
    exact Q'.eqv_trans _ _ _ (eval_polySum rho _ (n+2))
      (finSum_eqv_congr _ _ (fun a => Q'.eqv_trans _ _ _
        (eval_polySum rho _ (n+2))
        (finSum_eqv_congr _ _ (fun b => Q'.eqv_trans _ _ _
          (eval_polySum rho _ (n+2))
          (finSum_eqv_congr _ _ (fun c => eval_polySum rho _ (n+2)) (n+2)))
          (n+2))) (n+2))
  exact Q'.eqv_trans _ _ _ he (sum4_congr _ _ (fun a b c d =>
    Q'.eqv_trans _ _ _ (evalRatPoly_smul rho _ _)
      (Q'.mul_comm_eqv _ _)) (n+2))

private theorem constant_average (x : UnitNorm) (n : Nat) (c : Q') :
    sum4 (fun a b e d => c * pointWeight x n a b e d) (n+2) ≈ c :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (sum4_const_mul c _ (n+2)))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (pointMass_one x n))
      (Q'.mul_one_eqv c))

private theorem centered_average (f : UnitNorm → Q') (x : UnitNorm) (n : Nat) :
    sum4 (fun a b c d => pointWeight x n a b c d *
      (f (repairedQuaternion n a b c d) + -(f x))) (n+2) ≈
      approximateValue f x n + -(f x) := by
  refine Q'.eqv_trans _ _ _ (sum4_congr _ _ (fun a b c d =>
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.mul (.neg (.var 2)) (.var 0)))
      (by decide) (fun
        | 0 => pointWeight x n a b c d
        | 1 => f (repairedQuaternion n a b c d)
        | _ => f x)) (n+2)) ?_
  exact Q'.eqv_trans _ _ _ (sum4_add _ _ (n+2))
    (Q'.add_eqv_congr_left _ _ _ (constant_average x n (-(f x))))

private theorem abs_finiteSum (f : Nat → Q') :
    ∀ count, Q'.abs (finSum f count) ≤ finSum (fun k => Q'.abs (f k)) count
  | 0 => Q'.le_refl' 0
  | count+1 => Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.add_le_add_right _ _ _ (abs_finiteSum f count))

private theorem finiteSum_le (f g : Nat → Q') (h : ∀ k, f k ≤ g k) :
    ∀ count, finSum f count ≤ finSum g count
  | 0 => Q'.le_refl' 0
  | count+1 => Q'.add_le_add (finiteSum_le f g h count) (h count)

private theorem abs_sum4 (f : Nat → Nat → Nat → Nat → Q') (count : Nat) :
    Q'.abs (sum4 f count) ≤ sum4 (fun a b c d => Q'.abs (f a b c d)) count := by
  refine Q'.le_trans' _ _ _ (abs_finiteSum _ count) ?_
  apply finiteSum_le
  intro a
  refine Q'.le_trans' _ _ _ (abs_finiteSum _ count) ?_
  apply finiteSum_le
  intro b
  refine Q'.le_trans' _ _ _ (abs_finiteSum _ count) ?_
  apply finiteSum_le
  intro c
  exact abs_finiteSum _ count

private theorem function_difference_bound (f : UnitNorm → Q') (M : Q')
    (hM : ∀ x, Q'.abs (f x) ≤ M) (q x : UnitNorm) :
    Q'.abs (f q + -(f x)) ≤ 2*M :=
  Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
    (Q'.le_trans' _ _ _
      (Q'.add_le_add (hM q)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' (f x))) (hM x)))
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
        (by decide) (fun _ => M))))

private theorem function_majorant (f : UnitNorm → Q') (M delta eta : Q')
    (hd : (0 : Q') < delta) (he : (0 : Q') ≤ eta)
    (hM : ∀ x, Q'.abs (f x) ≤ M)
    (hmod : ∀ q x, distSq q.val x.val ≤ delta → Q'.abs (f q + -(f x)) ≤ eta)
    (q x : UnitNorm) :
    Q'.abs (f q + -(f x)) ≤
      eta + (2*M * Q'.recipPos delta hd) * distSq q.val x.val := by
  let D := distSq q.val x.val
  have hM0 : (0 : Q') ≤ M := Q'.le_trans' _ _ _ (Q'.abs_nonneg (f x)) (hM x)
  have hcoef : (0 : Q') ≤ 2*M * Q'.recipPos delta hd :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hM0)
      (Q'.le_of_lt (Q'.recipPos_pos delta hd))
  by_cases hnear : D ≤ delta
  · exact Q'.le_trans' _ _ _ (hmod q x hnear)
      (Q'.add_le_self_of_nonneg _ _
        (Q'.mul_nonneg _ _ hcoef (distance_nonnegative q.val x.val)))
  · have hfar : delta ≤ D := by
      change delta.num * (D.den : Int) ≤ D.num * (delta.den : Int)
      have hnot : ¬ D.num * (delta.den : Int) ≤ delta.num * (D.den : Int) := hnear
      exact Int.le_of_lt (Int.not_le.mp hnot)
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hfar hcoef
    have hpin : (2*M * Q'.recipPos delta hd) * delta ≈ 2*M :=
      Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv delta hd)))
          (Q'.mul_one_eqv _))
    have hbound := Q'.le_trans' _ _ _ (function_difference_bound f M hM q x)
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpin) hscaled)
    exact Q'.le_trans' _ _ _ hbound
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ eta he)
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

/-- A genuine approximation estimate from a function bound and its local
continuity radius, using only actual POINTWISE repaired-node samples. -/
theorem approximation_error (f : UnitNorm → Q') (M delta eta : Q')
    (hd : (0 : Q') < delta) (he : (0 : Q') ≤ eta)
    (hM : ∀ x, Q'.abs (f x) ≤ M)
    (hmod : ∀ q x, distSq q.val x.val ≤ delta → Q'.abs (f q + -(f x)) ≤ eta)
    (x : UnitNorm) (n : Nat) :
    Q'.abs (evalRatPoly (environmentOf x.val) (approximationPolynomial f n) + -(f x)) ≤
      eta + (2*M * Q'.recipPos delta hd) * (102*Q'.invSucc n) := by
  let C := 2*M * Q'.recipPos delta hd
  let F := fun a b c d => pointWeight x n a b c d *
    (f (repairedQuaternion n a b c d) + -(f x))
  let U := fun a b c d => pointWeight x n a b c d *
    (eta + C * distSq (repairedQuaternion n a b c d).val x.val)
  have hpoint (a b c d : Nat) : Q'.abs (F a b c d) ≤ U a b c d := by
    have hweight : Q'.abs (pointWeight x n a b c d) = pointWeight x n a b c d :=
      ExpNeg.abs_of_nonneg (pointWeight_nonnegative x n a b c d)
    exact Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
      (by
        rw [hweight]
        exact Q'.mul_le_mul_of_nonneg_left _ _ _
          (function_majorant f M delta eta hd he hM hmod _ x)
          (pointWeight_nonnegative x n a b c d))
  have hU : sum4 U (n+2) ≈ eta + C*pointRepairedDistance x n := by
    refine Q'.eqv_trans _ _ _ (sum4_congr _ _ (fun a b c d =>
      poly_identity_of_normal_eq
        (.mul (.var 0) (.add (.var 1) (.mul (.var 2) (.var 3))))
        (.add (.mul (.var 1) (.var 0))
          (.mul (.var 2) (.mul (.var 0) (.var 3))))
        (by decide) (fun
          | 0 => pointWeight x n a b c d
          | 1 => eta
          | 2 => C
          | _ => distSq (repairedQuaternion n a b c d).val x.val))
      (n+2)) ?_
    exact Q'.eqv_trans _ _ _ (sum4_add _ _ (n+2))
      (Q'.add_eqv_congr' (constant_average x n eta)
        (Q'.eqv_symm (sum4_const_mul C _ (n+2))))
  have hsum := Q'.le_trans' _ _ _ (abs_sum4 F (n+2))
    (Q'.le_trans' _ _ _
      (sum4_le_lt _ U (n+2) (fun a b c d _ _ _ _ => hpoint a b c d))
      (Q'.le_of_eqv hU))
  have hM0 : (0 : Q') ≤ M := Q'.le_trans' _ _ _ (Q'.abs_nonneg (f x)) (hM x)
  have hC : (0 : Q') ≤ C := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide) hM0) (Q'.le_of_lt (Q'.recipPos_pos delta hd))
  have hfinal := Q'.le_trans' _ _ _ hsum
    (Q'.add_le_add_left eta _ _ (Q'.mul_le_mul_of_nonneg_left _ _ C
      (pointRepairedDistance_le x n) hC))
  have hpin : evalRatPoly (environmentOf x.val) (approximationPolynomial f n) + -(f x) ≈
      sum4 F (n+2) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (eval_approximationPolynomial f x n))
      (Q'.eqv_symm (centered_average f x n))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin)) hfinal

/-- A positive ceiling computed from the supplied function bound, even at M=0. -/
def boundCeiling (M : Q') : Q' := 1 + Q'.abs M

theorem boundCeiling_positive (M : Q') : (0 : Q') < boundCeiling M :=
  Q'.pos_add_nonneg (by decide) (Q'.abs_nonneg M)

/-- Sufficient inverse-degree tolerance, with a separate continuity half-budget. -/
def degreeTolerance (M delta epsilon : Q') : Q' :=
  Q'.divPos ((HalfPow.half*epsilon)*delta) (204*boundCeiling M)
    (Q'.mul_pos (by decide) (boundCeiling_positive M))

theorem degreeTolerance_positive (M delta epsilon : Q')
    (hd : (0 : Q') < delta) (he : (0 : Q') < epsilon) :
    (0 : Q') < degreeTolerance M delta epsilon :=
  Q'.divPos_pos _ _ _ (Q'.mul_pos (Q'.mul_pos (by decide) he) hd)

private theorem degreeTolerance_pin (M delta epsilon : Q') :
    degreeTolerance M delta epsilon * (204*boundCeiling M) ≈
      (HalfPow.half*epsilon)*delta :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
        (Q'.mul_recipPos_eqv _ _))) (Q'.mul_one_eqv _))

/-- A computed Nat stage, not an existential or a supplied approximation. -/
def approximationCutoff (M delta epsilon : Q') : Nat :=
  (degreeTolerance M delta epsilon).den

private theorem tail_halfBudget (M delta epsilon : Q')
    (hM0 : (0 : Q') ≤ M) (hd : (0 : Q') < delta) (he : (0 : Q') < epsilon)
    (n : Nat) (hn : approximationCutoff M delta epsilon ≤ n) :
    (2*M * Q'.recipPos delta hd)*(102*Q'.invSucc n) ≤ HalfPow.half*epsilon := by
  let B := boundCeiling M
  let T := degreeTolerance M delta epsilon
  let R := Q'.recipPos delta hd
  have hrate : Q'.invSucc n ≤ T := Q'.le_trans' _ _ _
    (ExpNeg.invSucc_le_of_le hn)
    (HalfPow.invSucc_den_le T (degreeTolerance_positive M delta epsilon hd he))
  have hR : (0 : Q') ≤ R := Q'.le_of_lt (Q'.recipPos_pos delta hd)
  have hC : (0 : Q') ≤ 2*M*R :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hM0) hR
  have hstep := Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ 102 hrate (by decide)) hC
  have hM : M ≤ B := Q'.le_trans' _ _ _ (Q'.le_abs_self M)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg (Q'.abs M) 1 (by decide))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  have hMB := Q'.mul_le_mul_of_nonneg_right _ _ R
    (Q'.mul_le_mul_of_nonneg_left _ _ 2 hM (by decide)) hR
  have hT : (0 : Q') ≤ 102*T := Q'.mul_nonneg _ _ (by decide)
    (Q'.le_of_lt (degreeTolerance_positive M delta epsilon hd he))
  have hcap := Q'.mul_le_mul_of_nonneg_right _ _ (102*T) hMB hT
  have hring : (2*B*R)*(102*T) ≈ (T*(204*B))*R :=
    poly_identity_of_normal_eq
      (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1))
        (.mul (.const 102) (.var 2)))
      (.mul (.mul (.var 2) (.mul (.const 204) (.var 0))) (.var 1))
      (by decide) (fun | 0 => B | 1 => R | _ => T)
  have hpin : (T*(204*B))*R ≈ HalfPow.half*epsilon :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ R (degreeTolerance_pin M delta epsilon))
      (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_recipPos_eqv delta hd)) (Q'.mul_one_eqv _)))
  exact Q'.le_trans' _ _ _ hstep
    (Q'.le_trans' _ _ _ hcap (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hring hpin)))

/-- Uniform approximation of every bounded rational-valued function on the
actual dense quaternion carrier, from its explicit squared-distance modulus.
The polynomial and its degree cutoff are computed from samples and radius;
this does not assume approximation or integrate the function beforehand. -/
theorem uniform_approximation (f : UnitNorm → Q') (M : Q')
    (radius : Q' → Q')
    (radius_positive : ∀ e, (0 : Q') < e → (0 : Q') < radius e)
    (hM : ∀ x, Q'.abs (f x) ≤ M)
    (hmod : ∀ e, (0 : Q') < e → ∀ q x,
      distSq q.val x.val ≤ radius e → Q'.abs (f q + -(f x)) ≤ e)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : approximationCutoff M (radius (HalfPow.half*epsilon)) epsilon ≤ n)
    (x : UnitNorm) :
    Q'.abs (evalRatPoly (environmentOf x.val) (approximationPolynomial f n) + -(f x))
      ≤ epsilon := by
  let eta := HalfPow.half*epsilon
  let delta := radius eta
  have heta : (0 : Q') < eta := Q'.mul_pos (by decide) he
  have hdelta : (0 : Q') < delta := radius_positive eta heta
  have hM0 : (0 : Q') ≤ M := Q'.le_trans' _ _ _ (Q'.abs_nonneg (f x)) (hM x)
  have hbound := approximation_error f M delta eta hdelta
    (Q'.le_of_lt heta) hM (hmod eta heta) x n
  have hhalf := tail_halfBudget M delta epsilon hM0 hdelta he n hn
  have hsum := Q'.add_le_add_left eta _ _ hhalf
  have hpin : eta+HalfPow.half*epsilon ≈ epsilon :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_mul_eqv HalfPow.half HalfPow.half epsilon))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ epsilon
        (by decide : HalfPow.half+HalfPow.half ≈ (1 : Q')))
        (Q'.one_mul_eqv epsilon))
  exact Q'.le_trans' _ _ _ hbound
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hpin))

/-- The single-radius consumer retains a fixed noise floor in `eta`.
It does not require a modulus at every smaller tolerance. -/
theorem approximation_error_at_cutoff (f : UnitNorm → Q') (M delta eta : Q')
    (hd : (0 : Q') < delta) (heta : (0 : Q') ≤ eta)
    (hM : ∀ x, Q'.abs (f x) ≤ M)
    (hmod : ∀ q x, distSq q.val x.val ≤ delta → Q'.abs (f q + -(f x)) ≤ eta)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : approximationCutoff M delta epsilon ≤ n) (x : UnitNorm) :
    Q'.abs (evalRatPoly (environmentOf x.val) (approximationPolynomial f n) + -(f x))
      ≤ eta + HalfPow.half*epsilon := by
  have hM0 : (0 : Q') ≤ M := Q'.le_trans' _ _ _ (Q'.abs_nonneg (f x)) (hM x)
  exact Q'.le_trans' _ _ _ (approximation_error f M delta eta hd heta hM hmod x n)
    (Q'.add_le_add_left eta _ _ (tail_halfBudget M delta epsilon hM0 hd he n hn))

end YMGap.Continuum.QuaternionPointBernsteinApproximation

#print axioms YMGap.Continuum.QuaternionPointBernsteinApproximation.pointRepairedDistance
#print axioms YMGap.Continuum.QuaternionPointBernsteinApproximation.pointRepairedDistance_le
#print axioms YMGap.Continuum.QuaternionPointBernsteinApproximation.approximationPolynomial
#print axioms YMGap.Continuum.QuaternionPointBernsteinApproximation.approximationPolynomial_supported
#print axioms YMGap.Continuum.QuaternionPointBernsteinApproximation.approximateValue
#print axioms YMGap.Continuum.QuaternionPointBernsteinApproximation.eval_approximationPolynomial
#print axioms YMGap.Continuum.QuaternionPointBernsteinApproximation.approximation_error
#print axioms YMGap.Continuum.QuaternionPointBernsteinApproximation.boundCeiling
#print axioms YMGap.Continuum.QuaternionPointBernsteinApproximation.boundCeiling_positive
#print axioms YMGap.Continuum.QuaternionPointBernsteinApproximation.degreeTolerance
#print axioms YMGap.Continuum.QuaternionPointBernsteinApproximation.degreeTolerance_positive
#print axioms YMGap.Continuum.QuaternionPointBernsteinApproximation.approximationCutoff
#print axioms YMGap.Continuum.QuaternionPointBernsteinApproximation.uniform_approximation
#print axioms YMGap.Continuum.QuaternionPointBernsteinApproximation.approximation_error_at_cutoff
