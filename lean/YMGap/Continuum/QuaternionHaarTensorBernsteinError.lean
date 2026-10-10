/-
Exact finite coefficient-error budget for the SAME-Haar tensor Bernstein
weights.  The grid values here are rational polynomial evaluations, not an
assumed continuous Haar integral or an exact raw-grid quadrature rule.
-/

import YMGap.Continuum.QuaternionHaarTensorBernsteinCubature
import YMGap.Constructive.QPolyWeightedL1

namespace YMGap.Continuum.QuaternionHaarTensorBernsteinError

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyWeightedL1
open YMGap.Constructive.RationalTail
open YMGap.Constructive.CReal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.QPolyHaarPositiveSubstitution
open YMGap.Continuum.BernsteinFallingProductError
open YMGap.Continuum.BernsteinRationalPositiveRow
open YMGap.Continuum.QuaternionHaarTensorBernsteinCubature
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- The explicit per-row coefficient error. -/
def rowError (eta : Q') : Q' := HalfPow.half * eta

/-- A computable bound for both the elevated coefficient and grid value. -/
def rowBound (p : Poly) (eta : Q') : Q' := weightedL1 1 p + rowError eta

theorem rowError_nonnegative (eta : Q') (he : (0 : Q') < eta) :
    (0 : Q') ≤ rowError eta :=
  Q'.le_of_lt (Q'.mul_pos (by decide : (0 : Q') < HalfPow.half) he)

theorem rowBound_nonnegative (p : Poly) (eta : Q')
    (he : (0 : Q') < eta) : (0 : Q') ≤ rowBound p eta :=
  Q'.zero_le_add _ _
    (weightedL1_nonnegative 1 (by decide) p)
    (rowError_nonnegative eta he)

private theorem grid_abs_le_one (n k : Nat) (hk : k≤n+1) :
    Q'.abs (grid n k) ≤ 1 :=
  Q'.abs_le
    (Q'.le_trans' _ _ _ (by decide : (-(1 : Q')) ≤ 0)
      (grid_nonnegative n k))
    (grid_le_one n k hk)

theorem gridEval_abs_le_rowBound (p : Poly) (eta : Q')
    (he : (0 : Q') < eta) (n k : Nat) (hk : k≤n+1) :
    Q'.abs (eval p (grid n k)) ≤ rowBound p eta :=
  Q'.le_trans' _ _ _
    (abs_eval_le_weightedL1 (by decide : (0 : Q') ≤ 1)
      (grid_abs_le_one n k hk) p)
    (Q'.add_le_self_of_nonneg _ _ (rowError_nonnegative eta he))

theorem normalizedRow_abs_le_rowBound (p : Poly) (eta : Q')
    (he : (0 : Q') < eta) (n k : Nat)
    (hn : rowCutoff p eta ≤ n) (hk : k≤n+1) :
    Q'.abs (normalizedRow p n k) ≤ rowBound p eta := by
  let a := normalizedRow p n k
  let b := eval p (grid n k)
  have hsplit : a ≈ (a + -b) + b :=
    poly_identity_of_normal_eq (.var 0)
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1))
      (by decide) (fun | 0 => a | _ => b)
  have hdiff : Q'.abs (a + -b) ≤ rowError eta :=
    normalizedRow_error p eta he n k hn hk
  have heval : Q'.abs b ≤ weightedL1 1 p :=
    abs_eval_le_weightedL1 (by decide : (0 : Q') ≤ 1)
      (grid_abs_le_one n k hk) p
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hsplit))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.le_trans' _ _ _ (Q'.add_le_add hdiff heval)
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _))))

private theorem abs_product_bound {u v U V : Q'}
    (hu : Q'.abs u ≤ U) (hv : Q'.abs v ≤ V) :
    Q'.abs (u*v) ≤ U*V :=
  Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le u v)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hu (Q'.abs_nonneg v))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hv
        (Q'.le_trans' _ _ _ (Q'.abs_nonneg u) hu)))

private theorem abs_mul_difference {a b c d A D E F : Q'}
    (hA : (0 : Q') ≤ A) (hD : (0 : Q') ≤ D)
    (ha : Q'.abs a ≤ A) (hd : Q'.abs d ≤ D)
    (hb : Q'.abs (b + -d) ≤ E) (hc : Q'.abs (a + -c) ≤ F) :
    Q'.abs (a*b + -(c*d)) ≤ A*E + D*F := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ExpNeg.abs_eqv_congr (CReal.mul_sub_decomp a b c d))) ?_
  refine Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _) ?_
  apply Q'.add_le_add
  · refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _) ?_
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ ha (Q'.abs_nonneg _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hb hA)
  · refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _) ?_
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hd (Q'.abs_nonneg _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hc hD)

private theorem pair_error {a0 a1 b0 b1 B0 B1 e : Q'}
    (hB0 : (0 : Q') ≤ B0) (hB1 : (0 : Q') ≤ B1)
    (ha0 : Q'.abs a0 ≤ B0) (hb1 : Q'.abs b1 ≤ B1)
    (he0 : Q'.abs (a0 + -b0) ≤ e)
    (he1 : Q'.abs (a1 + -b1) ≤ e) :
    Q'.abs (a0*a1 + -(b0*b1)) ≤ B0*e+B1*e :=
  abs_mul_difference hB0 hB1 ha0 hb1 he1 he0

def gridProduct (n : Nat) (p0 p1 p2 p3 : Poly)
    (k0 k1 k2 k3 : Nat) : Q' :=
  eval p0 (grid n k0) * (eval p1 (grid n k1) *
    (eval p2 (grid n k2) * eval p3 (grid n k3)))

/-- Explicit four-factor telescope budget: each summand replaces one factor. -/
def productErrorBudget (p0 p1 p2 p3 : Poly) (eta : Q') : Q' :=
  let e := rowError eta
  let B0 := rowBound p0 eta
  let B1 := rowBound p1 eta
  let B2 := rowBound p2 eta
  let B3 := rowBound p3 eta
  e * (B1*B2*B3 + B0*B2*B3 + B0*B1*B3 + B0*B1*B2)

theorem normalizedCoefficientProduct_error (p0 p1 p2 p3 : Poly)
    (eta : Q') (he : (0 : Q') < eta) (n k0 k1 k2 k3 : Nat)
    (hn : weightedRowCutoff p0 p1 p2 p3 eta ≤ n)
    (hk0 : k0≤n+1) (hk1 : k1≤n+1)
    (hk2 : k2≤n+1) (hk3 : k3≤n+1) :
    Q'.abs (normalizedCoefficientProduct n p0 p1 p2 p3 k0 k1 k2 k3 +
      -(gridProduct n p0 p1 p2 p3 k0 k1 k2 k3)) ≤
      productErrorBudget p0 p1 p2 p3 eta := by
  let a0 := normalizedRow p0 n k0
  let a1 := normalizedRow p1 n k1
  let a2 := normalizedRow p2 n k2
  let a3 := normalizedRow p3 n k3
  let b0 := eval p0 (grid n k0)
  let b1 := eval p1 (grid n k1)
  let b2 := eval p2 (grid n k2)
  let b3 := eval p3 (grid n k3)
  let B0 := rowBound p0 eta
  let B1 := rowBound p1 eta
  let B2 := rowBound p2 eta
  let B3 := rowBound p3 eta
  let e := rowError eta
  have h0 : rowCutoff p0 eta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have h1 : rowCutoff p1 eta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have h2 : rowCutoff p2 eta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have h3 : rowCutoff p3 eta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  have hB0 : (0 : Q') ≤ B0 := rowBound_nonnegative p0 eta he
  have hB1 : (0 : Q') ≤ B1 := rowBound_nonnegative p1 eta he
  have hB2 : (0 : Q') ≤ B2 := rowBound_nonnegative p2 eta he
  have hB3 : (0 : Q') ≤ B3 := rowBound_nonnegative p3 eta he
  have ha0 : Q'.abs a0 ≤ B0 := normalizedRow_abs_le_rowBound p0 eta he n k0 h0 hk0
  have ha2 : Q'.abs a2 ≤ B2 := normalizedRow_abs_le_rowBound p2 eta he n k2 h2 hk2
  have hb1 : Q'.abs b1 ≤ B1 := gridEval_abs_le_rowBound p1 eta he n k1 hk1
  have hb3 : Q'.abs b3 ≤ B3 := gridEval_abs_le_rowBound p3 eta he n k3 hk3
  have hd0 : Q'.abs (a0 + -b0) ≤ e := normalizedRow_error p0 eta he n k0 h0 hk0
  have hd1 : Q'.abs (a1 + -b1) ≤ e := normalizedRow_error p1 eta he n k1 h1 hk1
  have hd2 : Q'.abs (a2 + -b2) ≤ e := normalizedRow_error p2 eta he n k2 h2 hk2
  have hd3 : Q'.abs (a3 + -b3) ≤ e := normalizedRow_error p3 eta he n k3 h3 hk3
  have hp01 : Q'.abs (a0*a1 + -(b0*b1)) ≤ B0*e+B1*e :=
    pair_error hB0 hB1 ha0 hb1 hd0 hd1
  have hp23 : Q'.abs (a2*a3 + -(b2*b3)) ≤ B2*e+B3*e :=
    pair_error hB2 hB3 ha2 hb3 hd2 hd3
  have ha01 : Q'.abs (a0*a1) ≤ B0*B1 := by
    have ha1 := normalizedRow_abs_le_rowBound p1 eta he n k1 h1 hk1
    exact abs_product_bound ha0 ha1
  have hb23 : Q'.abs (b2*b3) ≤ B2*B3 := by
    have hb2 := gridEval_abs_le_rowBound p2 eta he n k2 hk2
    exact abs_product_bound hb2 hb3
  have hbig : Q'.abs ((a0*a1)*(a2*a3) + -((b0*b1)*(b2*b3))) ≤
      (B0*B1)*(B2*e+B3*e) + (B2*B3)*(B0*e+B1*e) :=
    abs_mul_difference
      (Q'.mul_nonneg _ _ hB0 hB1) (Q'.mul_nonneg _ _ hB2 hB3)
      ha01 hb23 hp23 hp01
  have hreassoc :
      normalizedCoefficientProduct n p0 p1 p2 p3 k0 k1 k2 k3 +
        -(gridProduct n p0 p1 p2 p3 k0 k1 k2 k3) ≈
        (a0*a1)*(a2*a3) + -((b0*b1)*(b2*b3)) := by
    exact poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
        (.neg (.mul (.var 4) (.mul (.var 5) (.mul (.var 6) (.var 7))))))
      (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.neg (.mul (.mul (.var 4) (.var 5)) (.mul (.var 6) (.var 7)))))
      (by decide) (fun
        | 0 => a0
        | 1 => a1
        | 2 => a2
        | 3 => a3
        | 4 => b0
        | 5 => b1
        | 6 => b2
        | _ => b3)
  have hbudget :
      (B0*B1)*(B2*e+B3*e) + (B2*B3)*(B0*e+B1*e) ≈
        productErrorBudget p0 p1 p2 p3 eta := by
    exact poly_identity_of_normal_eq
      (.add (.mul (.mul (.var 0) (.var 1))
          (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 4))))
        (.mul (.mul (.var 2) (.var 3))
          (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 4)))))
      (.mul (.var 4)
        (.add (.add (.add (.mul (.mul (.var 1) (.var 2)) (.var 3))
          (.mul (.mul (.var 0) (.var 2)) (.var 3)))
          (.mul (.mul (.var 0) (.var 1)) (.var 3)))
          (.mul (.mul (.var 0) (.var 1)) (.var 2))))
      (by decide) (fun | 0 => B0 | 1 => B1 | 2 => B2 | 3 => B3 | _ => e)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hreassoc))
    (Q'.le_trans' _ _ _ hbig (Q'.le_of_eqv hbudget))

/-! ## Consequence for the actual finite joint Haar weights -/

private def sum4 (f : Nat → Nat → Nat → Nat → Q') (count : Nat) : Q' :=
  finSum (fun k0 => finSum (fun k1 => finSum (fun k2 =>
    finSum (fun k3 => f k0 k1 k2 k3) count) count) count) count

private theorem finSum_le_lt (f g : Nat → Q') :
    ∀ count, (∀ k, k<count → f k ≤ g k) →
      finSum f count ≤ finSum g count
  | 0, _ => Q'.le_refl' 0
  | count+1, h =>
      Q'.add_le_add
        (finSum_le_lt f g count (fun k hk => h k (by omega)))
        (h count (by omega))

private theorem sum4_le_lt (f g : Nat → Nat → Nat → Nat → Q')
    (count : Nat)
    (h : ∀ k0 k1 k2 k3, k0<count → k1<count → k2<count → k3<count →
      f k0 k1 k2 k3 ≤ g k0 k1 k2 k3) :
    sum4 f count ≤ sum4 g count := by
  unfold sum4
  apply finSum_le_lt
  intro k0 hk0
  apply finSum_le_lt
  intro k1 hk1
  apply finSum_le_lt
  intro k2 hk2
  apply finSum_le_lt
  intro k3 hk3
  exact h k0 k1 k2 k3 hk0 hk1 hk2 hk3

private theorem sum4_add (f g : Nat → Nat → Nat → Nat → Q')
    (count : Nat) :
    sum4 (fun k0 k1 k2 k3 => f k0 k1 k2 k3 + g k0 k1 k2 k3)
      count ≈ sum4 f count + sum4 g count := by
  unfold sum4
  exact Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ _ (fun k0 =>
      Q'.eqv_trans _ _ _
        (finSum_eqv_congr _ _ (fun k1 =>
          Q'.eqv_trans _ _ _
            (finSum_eqv_congr _ _ (fun k2 => finSum_add _ _ count) count)
            (finSum_add _ _ count)) count)
        (finSum_add _ _ count)) count)
    (finSum_add _ _ count)

private theorem sum4_const_mul (c : Q')
    (f : Nat → Nat → Nat → Nat → Q') (count : Nat) :
    c * sum4 f count ≈
      sum4 (fun k0 k1 k2 k3 => c * f k0 k1 k2 k3) count := by
  unfold sum4
  exact Q'.eqv_trans _ _ _ (const_mul_finSum _ c count)
    (finSum_eqv_congr _ _ (fun k0 =>
      Q'.eqv_trans _ _ _ (const_mul_finSum _ c count)
        (finSum_eqv_congr _ _ (fun k1 =>
          Q'.eqv_trans _ _ _ (const_mul_finSum _ c count)
            (finSum_eqv_congr _ _ (fun k2 =>
              const_mul_finSum _ c count) count)) count)) count)

private theorem weighted_sum4_difference
    (w f g : Nat → Nat → Nat → Nat → Q')
    (count : Nat) (E : Q')
    (hw : ∀ k0 k1 k2 k3, k0<count → k1<count → k2<count → k3<count →
      (0 : Q') ≤ w k0 k1 k2 k3)
    (hmass : sum4 w count ≈ 1)
    (herr : ∀ k0 k1 k2 k3, k0<count → k1<count → k2<count → k3<count →
      Q'.abs (f k0 k1 k2 k3 + -g k0 k1 k2 k3) ≤ E) :
    Q'.abs
      (sum4 (fun k0 k1 k2 k3 => w k0 k1 k2 k3 * f k0 k1 k2 k3) count +
        -(sum4 (fun k0 k1 k2 k3 => w k0 k1 k2 k3 * g k0 k1 k2 k3) count))
      ≤ E := by
  let F := fun k0 k1 k2 k3 => w k0 k1 k2 k3 * f k0 k1 k2 k3
  let G := fun k0 k1 k2 k3 => w k0 k1 k2 k3 * g k0 k1 k2 k3
  let W := fun k0 k1 k2 k3 => E * w k0 k1 k2 k3
  have hforward (k0 k1 k2 k3 : Nat)
      (h0 : k0<count) (h1 : k1<count) (h2 : k2<count) (h3 : k3<count) :
      F k0 k1 k2 k3 ≤ G k0 k1 k2 k3 + W k0 k1 k2 k3 := by
    let weight := w k0 k1 k2 k3
    let x := f k0 k1 k2 k3
    let y := g k0 k1 k2 k3
    have hxy : x ≤ y+E := ExpNeg.le_add_of_abs_sub_le
      (herr k0 k1 k2 k3 h0 h1 h2 h3)
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hxy (hw k0 k1 k2 k3 h0 h1 h2 h3))
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv weight y E)
        (Q'.add_eqv_congr_left (weight*y) _ _ (Q'.mul_comm_eqv weight E))))
  have hbackward (k0 k1 k2 k3 : Nat)
      (h0 : k0<count) (h1 : k1<count) (h2 : k2<count) (h3 : k3<count) :
      G k0 k1 k2 k3 ≤ F k0 k1 k2 k3 + W k0 k1 k2 k3 := by
    let weight := w k0 k1 k2 k3
    let x := f k0 k1 k2 k3
    let y := g k0 k1 k2 k3
    have hyx : y ≤ x+E := ExpNeg.le_add_of_abs_sub_le
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (ExpNeg.abs_sub_comm y x))
        (herr k0 k1 k2 k3 h0 h1 h2 h3))
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hyx (hw k0 k1 k2 k3 h0 h1 h2 h3))
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv weight x E)
        (Q'.add_eqv_congr_left (weight*x) _ _ (Q'.mul_comm_eqv weight E))))
  have hsumW : sum4 W count ≈ E :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (sum4_const_mul E w count))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left E _ _ hmass) (Q'.mul_one_eqv E))
  have hupper : sum4 F count ≤ sum4 G count + E :=
    Q'.le_trans' _ _ _
      (sum4_le_lt F (fun k0 k1 k2 k3 =>
        G k0 k1 k2 k3 + W k0 k1 k2 k3) count hforward)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (sum4_add G W count)
        (Q'.add_eqv_congr_left (sum4 G count) _ _ hsumW)))
  have hlower : sum4 G count ≤ sum4 F count + E :=
    Q'.le_trans' _ _ _
      (sum4_le_lt G (fun k0 k1 k2 k3 =>
        F k0 k1 k2 k3 + W k0 k1 k2 k3) count hbackward)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (sum4_add F W count)
        (Q'.add_eqv_congr_left (sum4 F count) _ _ hsumW)))
  exact CReal.abs_sub_le_of_bounds hupper hlower

/-- The literal same-weight grid evaluation sum, with no independent
coordinate marginals and no continuous integration. -/
def gridWeightedSum (n : Nat) (p0 p1 p2 p3 : Poly) : Q' :=
  sum4 (fun k0 k1 k2 k3 =>
    jointWeightRaw n k0 k1 k2 k3 *
      gridProduct n p0 p1 p2 p3 k0 k1 k2 k3) (n+2)

theorem weightedRowSum_grid_error (p0 p1 p2 p3 : Poly)
    (eta : Q') (he : (0 : Q') < eta) (n : Nat)
    (hn : weightedRowCutoff p0 p1 p2 p3 eta ≤ n) :
    Q'.abs (weightedRowSum n p0 p1 p2 p3 +
      -(gridWeightedSum n p0 p1 p2 p3)) ≤
      productErrorBudget p0 p1 p2 p3 eta := by
  exact weighted_sum4_difference
    (jointWeightRaw n)
    (normalizedCoefficientProduct n p0 p1 p2 p3)
    (gridProduct n p0 p1 p2 p3)
    (n+2) (productErrorBudget p0 p1 p2 p3 eta)
    (fun k0 k1 k2 k3 _ _ _ _ =>
      jointWeightRaw_nonnegative n k0 k1 k2 k3)
    (jointMass_one n)
    (fun k0 k1 k2 k3 h0 h1 h2 h3 =>
      normalizedCoefficientProduct_error p0 p1 p2 p3 eta he n
        k0 k1 k2 k3 hn (by omega) (by omega) (by omega) (by omega))

theorem haar_separable_grid_error (p0 p1 p2 p3 : Poly)
    (eta : Q') (he : (0 : Q') < eta) (n : Nat)
    (hn : weightedRowCutoff p0 p1 p2 p3 eta ≤ n) :
    Q'.abs
      (quaternionHaar 1
        (polyMul (subst (shiftedCoordinate ⟨0, by decide⟩) p0)
          (polyMul (subst (shiftedCoordinate ⟨1, by decide⟩) p1)
            (polyMul (subst (shiftedCoordinate ⟨2, by decide⟩) p2)
              (subst (shiftedCoordinate ⟨3, by decide⟩) p3)))) +
        -(gridWeightedSum n p0 p1 p2 p3)) ≤
      productErrorBudget p0 p1 p2 p3 eta :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ExpNeg.abs_eqv_congr
      (Q'.add_eqv_congr_right _ _ _
        (haar_separable_eq_weightedRow p0 p1 p2 p3 eta n hn))))
    (weightedRowSum_grid_error p0 p1 p2 p3 eta he n hn)

end YMGap.Continuum.QuaternionHaarTensorBernsteinError

#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinError.rowError
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinError.rowBound
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinError.rowError_nonnegative
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinError.rowBound_nonnegative
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinError.gridEval_abs_le_rowBound
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinError.normalizedRow_abs_le_rowBound
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinError.gridProduct
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinError.productErrorBudget
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinError.normalizedCoefficientProduct_error
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinError.gridWeightedSum
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinError.weightedRowSum_grid_error
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinError.haar_separable_grid_error
