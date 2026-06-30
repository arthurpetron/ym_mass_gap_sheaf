import YMGap.Continuum.SelfFusionLogConcave
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.FusionChannelIneq

open YMGap.Constructive
open YMGap.Continuum

/-! Local algebra helpers. -/

theorem prodsq (a b : Q') : ((a * b) * (a * b)).eqv ((a * a) * (b * b)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (a * b)) ?_
  have inner : (b * (a * b)).eqv (a * (b * b)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv b a b)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (b * a) (a * b) b (Q'.mul_comm_eqv b a)) ?_
    exact Q'.mul_assoc_eqv a b b
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ inner) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a a (b * b))

/-! ## polyI2 : the `s = 2` channel inequality. -/

theorem polyI2 (x y : Q') (hx0 : (0 : Q') ≤ x) (hy0 : (0 : Q') ≤ y)
    (hyx : y ≤ x * x) (hx1 : x * x ≤ (1 : Q')) :
    ((y + y) + (x * x + y * y)) * (y * y)
      ≤ (x * y + x * y) * (x * y + x * y) := by
  have hxxnn : (0 : Q') ≤ x * x := Q'.mul_nonneg _ _ hx0 hx0
  have hyynn : (0 : Q') ≤ y * y := Q'.mul_nonneg _ _ hy0 hy0
  -- y*y ≤ x*x
  have hyyxx : y * y ≤ x * x := by
    have a1 : y * y ≤ (x * x) * y := Q'.mul_le_mul_of_nonneg_right y (x * x) y hyx hy0
    have a2 : (x * x) * y ≤ (x * x) * (x * x) :=
      Q'.mul_le_mul_of_nonneg_left y (x * x) (x * x) hyx hxxnn
    have a3 : (x * x) * (x * x) ≤ (x * x) * 1 :=
      Q'.mul_le_mul_of_nonneg_left (x * x) 1 (x * x) hx1 hxxnn
    exact Q'.le_trans' _ _ _ a1 (Q'.le_trans' _ _ _ a2
      (Q'.le_trans' _ _ _ a3 (Q'.le_of_eqv (Q'.mul_one_eqv (x * x)))))
  -- B2 ≤ D
  have hB2D : (y + y) + (x * x + y * y) ≤ (x * x + x * x) + (x * x + x * x) :=
    Q'.add_le_add (Q'.add_le_add hyx hyx) (Q'.add_le_add (Q'.le_refl' (x * x)) hyyxx)
  have hstep : ((y + y) + (x * x + y * y)) * (y * y)
      ≤ ((x * x + x * x) + (x * x + x * x)) * (y * y) :=
    Q'.mul_le_mul_of_nonneg_right _ _ (y * y) hB2D hyynn
  -- expansions to the common 4-term form
  have hDexp : (((x * x + x * x) + (x * x + x * x)) * (y * y)).eqv
      ((((x * x) * (y * y)) + ((x * x) * (y * y)))
        + (((x * x) * (y * y)) + ((x * x) * (y * y)))) :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (x * x + x * x) (x * x + x * x) (y * y))
      (Q'.add_eqv_congr' (Q'.add_mul_eqv (x * x) (x * x) (y * y))
        (Q'.add_mul_eqv (x * x) (x * x) (y * y)))
  have hhalf : ((x * y) * (x * y + x * y)).eqv
      (((x * x) * (y * y)) + ((x * x) * (y * y))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (x * y) (x * y) (x * y))
      (Q'.add_eqv_congr' (prodsq x y) (prodsq x y))
  have hRexp : ((x * y + x * y) * (x * y + x * y)).eqv
      ((((x * x) * (y * y)) + ((x * x) * (y * y)))
        + (((x * x) * (y * y)) + ((x * x) * (y * y)))) :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (x * y) (x * y) (x * y + x * y))
      (Q'.add_eqv_congr' hhalf hhalf)
  exact Q'.le_trans' _ _ _ hstep
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hDexp) (Q'.ge_of_eqv hRexp))

/-! ## polyI1 : unconditional SOS-routed channel inequality. -/

theorem polyI1 (x y : Q') (hx0 : (0 : Q') ≤ x) (hy0 : (0 : Q') ≤ y) :
    ((x + x) + (x * y + x * y)) * (x * y + x * y)
      ≤ ((y + y) + (x * x + y * y)) * ((y + y) + (x * x + y * y)) := by
  have hcancel : ∀ A B T : Q',
      ((((A + T) + (T + B)) + (((-T) + (-T)) + ((-T) + (-T)))).eqv
        (((A + (-T)) + ((-T) + B)))) := by
    intro A B T
    have hzero : (((T + T) + ((-T) + (-T))).eqv (0 : Q')) := by
      refine Q'.eqv_trans _ _ _ (QPoly.q_interchange T T (-T) (-T)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.add_neg_self_eqv T) (Q'.add_neg_self_eqv T)) ?_
      exact QPoly.q_add_zero_eqv (0 : Q')
    have hTTNN : (((T + T) + (((-T) + (-T)) + ((-T) + (-T)))).eqv ((-T) + (-T))) := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv (T + T) ((-T) + (-T)) ((-T) + (-T)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right ((T + T) + ((-T) + (-T))) 0 ((-T) + (-T)) hzero) ?_
      exact QPoly.q_zero_add_eqv ((-T) + (-T))
    have hleft : (((A + T) + (T + B)).eqv (A + (B + (T + T)))) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv A T (T + B)) ?_
      refine Q'.add_eqv_congr_left A (T + (T + B)) (B + (T + T)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv T T B)) ?_
      exact Q'.add_comm_eqv (T + T) B
    have hLHSc :
        (((((A + T) + (T + B)) + (((-T) + (-T)) + ((-T) + (-T))))).eqv
          (A + (B + ((-T) + (-T))))) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right ((A + T) + (T + B)) (A + (B + (T + T)))
          (((-T) + (-T)) + ((-T) + (-T))) hleft) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv A (B + (T + T)) (((-T) + (-T)) + ((-T) + (-T)))) ?_
      refine Q'.add_eqv_congr_left A _ _ ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv B (T + T) (((-T) + (-T)) + ((-T) + (-T)))) ?_
      exact Q'.add_eqv_congr_left B _ _ hTTNN
    have hRHSc :
        ((((A + (-T)) + ((-T) + B))).eqv (A + (B + ((-T) + (-T))))) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv A (-T) ((-T) + B)) ?_
      refine Q'.add_eqv_congr_left A ((-T) + ((-T) + B)) (B + ((-T) + (-T))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (-T) (-T) B)) ?_
      exact Q'.add_comm_eqv ((-T) + (-T)) B
    exact Q'.eqv_trans _ _ _ hLHSc (Q'.eqv_symm hRHSc)
  -- hLHS : LHS ≃ FX2Y + FX2Y2
  have hxxy : ((x * (x * y)).eqv ((x * x) * y)) := Q'.eqv_symm (Q'.mul_assoc_eqv x x y)
  have hxhalf : ((x * (x * y + x * y)).eqv ((x * x) * y + (x * x) * y)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv x (x * y) (x * y))
      (Q'.add_eqv_congr' hxxy hxxy)
  have hL1half :
      (((x + x) * (x * y + x * y)).eqv
        (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))) :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv x x (x * y + x * y))
      (Q'.add_eqv_congr' hxhalf hxhalf)
  have hxyhalf :
      (((x * y) * (x * y + x * y)).eqv ((x * x) * (y * y) + (x * x) * (y * y))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (x * y) (x * y) (x * y))
      (Q'.add_eqv_congr' (prodsq x y) (prodsq x y))
  have hL2half :
      (((x * y + x * y) * (x * y + x * y)).eqv
        (((x * x) * (y * y) + (x * x) * (y * y)) + ((x * x) * (y * y) + (x * x) * (y * y)))) :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (x * y) (x * y) (x * y + x * y))
      (Q'.add_eqv_congr' hxyhalf hxyhalf)
  have hLHS :
      ((((x + x) + (x * y + x * y)) * (x * y + x * y)).eqv
        ((((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
          + (((x * x) * (y * y) + (x * x) * (y * y)) + ((x * x) * (y * y) + (x * x) * (y * y))))) :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (x + x) (x * y + x * y) (x * y + x * y))
      (Q'.add_eqv_congr' hL1half hL2half)
  -- hRHS : RHS ≃ FX2Y + (Q2 + (FYY + FY3))
  have hP2 :
      (((y + y) * (y + y)).eqv ((y * y + y * y) + (y * y + y * y))) :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv y y (y + y))
      (Q'.add_eqv_congr' (Q'.mul_add_eqv y y y) (Q'.mul_add_eqv y y y))
  have hhalf_pq :
      ((y * (x * x + y * y)).eqv ((x * x) * y + (y * y) * y)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv y (x * x) (y * y))
      (Q'.add_eqv_congr' (Q'.mul_comm_eqv y (x * x)) (Q'.mul_comm_eqv y (y * y)))
  have hPQraw :
      (((y + y) * (x * x + y * y)).eqv
        (((x * x) * y + (y * y) * y) + ((x * x) * y + (y * y) * y))) :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv y y (x * x + y * y))
      (Q'.add_eqv_congr' hhalf_pq hhalf_pq)
  have hPQ :
      (((y + y) * (x * x + y * y)).eqv
        (((x * x) * y + (x * x) * y) + ((y * y) * y + (y * y) * y))) :=
    Q'.eqv_trans _ _ _ hPQraw
      (QPoly.q_interchange ((x * x) * y) ((y * y) * y) ((x * x) * y) ((y * y) * y))
  have hQP :
      (((x * x + y * y) * (y + y)).eqv
        (((x * x) * y + (x * x) * y) + ((y * y) * y + (y * y) * y))) :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (x * x) (y * y) (y + y))
      (Q'.add_eqv_congr' (Q'.mul_add_eqv (x * x) y y) (Q'.mul_add_eqv (y * y) y y))
  have hsq :
      ((((y + y) + (x * x + y * y)) * ((y + y) + (x * x + y * y))).eqv
        (((y + y) * (y + y) + (y + y) * (x * x + y * y))
          + ((x * x + y * y) * (y + y) + (x * x + y * y) * (x * x + y * y)))) :=
    Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (y + y) (x * x + y * y) ((y + y) + (x * x + y * y)))
      (Q'.add_eqv_congr'
        (Q'.mul_add_eqv (y + y) (y + y) (x * x + y * y))
        (Q'.mul_add_eqv (x * x + y * y) (y + y) (x * x + y * y)))
  have hexp :
      ((((y + y) + (x * x + y * y)) * ((y + y) + (x * x + y * y))).eqv
        (((((y * y + y * y) + (y * y + y * y)))
            + (((x * x) * y + (x * x) * y) + ((y * y) * y + (y * y) * y)))
          + ((((x * x) * y + (x * x) * y) + ((y * y) * y + (y * y) * y))
            + (x * x + y * y) * (x * x + y * y)))) :=
    Q'.eqv_trans _ _ _ hsq
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' hP2 hPQ)
        (Q'.add_eqv_congr' hQP (Q'.eqv_refl ((x * x + y * y) * (x * x + y * y)))))
  have hregroup :
      (((((y * y + y * y) + (y * y + y * y))
            + (((x * x) * y + (x * x) * y) + ((y * y) * y + (y * y) * y)))
          + ((((x * x) * y + (x * x) * y) + ((y * y) * y + (y * y) * y))
            + (x * x + y * y) * (x * x + y * y))).eqv
        ((((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
          + ((x * x + y * y) * (x * x + y * y)
            + (((y * y + y * y) + (y * y + y * y))
              + (((y * y) * y + (y * y) * y) + ((y * y) * y + (y * y) * y)))))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv ((y * y + y * y) + (y * y + y * y))
        (((x * x) * y + (x * x) * y) + ((y * y) * y + (y * y) * y))
        ((((x * x) * y + (x * x) * y) + ((y * y) * y + (y * y) * y))
          + (x * x + y * y) * (x * x + y * y))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left ((y * y + y * y) + (y * y + y * y)) _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv
          (((x * x) * y + (x * x) * y) + ((y * y) * y + (y * y) * y))
          (((x * x) * y + (x * x) * y) + ((y * y) * y + (y * y) * y))
          ((x * x + y * y) * (x * x + y * y))))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left ((y * y + y * y) + (y * y + y * y)) _ _
        (Q'.add_eqv_congr_right
          ((((x * x) * y + (x * x) * y) + ((y * y) * y + (y * y) * y))
            + (((x * x) * y + (x * x) * y) + ((y * y) * y + (y * y) * y)))
          ((((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
            + (((y * y) * y + (y * y) * y) + ((y * y) * y + (y * y) * y)))
          ((x * x + y * y) * (x * x + y * y))
          (QPoly.q_interchange ((x * x) * y + (x * x) * y) ((y * y) * y + (y * y) * y)
            ((x * x) * y + (x * x) * y) ((y * y) * y + (y * y) * y)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left ((y * y + y * y) + (y * y + y * y)) _ _
        (Q'.add_assoc_eqv
          (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
          (((y * y) * y + (y * y) * y) + ((y * y) * y + (y * y) * y))
          ((x * x + y * y) * (x * x + y * y)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv ((y * y + y * y) + (y * y + y * y))
        (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
        ((((y * y) * y + (y * y) * y) + ((y * y) * y + (y * y) * y))
          + (x * x + y * y) * (x * x + y * y)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right
        (((y * y + y * y) + (y * y + y * y))
          + (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y)))
        ((((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
          + ((y * y + y * y) + (y * y + y * y)))
        ((((y * y) * y + (y * y) * y) + ((y * y) * y + (y * y) * y))
          + (x * x + y * y) * (x * x + y * y))
        (Q'.add_comm_eqv ((y * y + y * y) + (y * y + y * y))
          (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv
        (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
        ((y * y + y * y) + (y * y + y * y))
        ((((y * y) * y + (y * y) * y) + ((y * y) * y + (y * y) * y))
          + (x * x + y * y) * (x * x + y * y))) ?_
    refine Q'.add_eqv_congr_left
      (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y)) _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv ((y * y + y * y) + (y * y + y * y))
        (((y * y) * y + (y * y) * y) + ((y * y) * y + (y * y) * y))
        ((x * x + y * y) * (x * x + y * y)))) ?_
    exact Q'.add_comm_eqv
      (((y * y + y * y) + (y * y + y * y))
        + (((y * y) * y + (y * y) * y) + ((y * y) * y + (y * y) * y)))
      ((x * x + y * y) * (x * x + y * y))
  have hRHS :
      ((((y + y) + (x * x + y * y)) * ((y + y) + (x * x + y * y))).eqv
        ((((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
          + ((x * x + y * y) * (x * x + y * y)
            + (((y * y + y * y) + (y * y + y * y))
              + (((y * y) * y + (y * y) * y) + ((y * y) * y + (y * y) * y)))))) :=
    Q'.eqv_trans _ _ _ hexp hregroup
  -- hSOS : FX2Y2 ≤ Q2
  have hQ2second :
      (((y * y) * (x * x + y * y)).eqv ((x * x) * (y * y) + (y * y) * (y * y))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (y * y) (x * x) (y * y))
      (Q'.add_eqv_congr' (Q'.mul_comm_eqv (y * y) (x * x))
        (Q'.eqv_refl ((y * y) * (y * y))))
  have hQ2exp :
      (((x * x + y * y) * (x * x + y * y)).eqv
        (((x * x) * (x * x) + (x * x) * (y * y))
          + ((x * x) * (y * y) + (y * y) * (y * y)))) :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (x * x) (y * y) (x * x + y * y))
      (Q'.add_eqv_congr' (Q'.mul_add_eqv (x * x) (x * x) (y * y)) hQ2second)
  have hSQfirst :
      (((x * x) * (x * x + (-(y * y)))).eqv ((x * x) * (x * x) + (-((x * x) * (y * y))))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (x * x) (x * x) (-(y * y)))
      (Q'.add_eqv_congr' (Q'.eqv_refl ((x * x) * (x * x))) (Q'.mul_neg_eqv (x * x) (y * y)))
  have hnegfirst :
      ((((-(y * y)) * (x * x))).eqv (-((x * x) * (y * y)))) :=
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv (y * y) (x * x))
      (Q'.neg_eqv_congr ((y * y) * (x * x)) ((x * x) * (y * y)) (Q'.mul_comm_eqv (y * y) (x * x)))
  have hneg2 :
      ((((-(y * y)) * (-(y * y)))).eqv ((y * y) * (y * y))) :=
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv (y * y) (-(y * y)))
      (Q'.eqv_trans _ _ _
        (Q'.neg_eqv_congr ((y * y) * (-(y * y))) (-((y * y) * (y * y)))
          (Q'.mul_neg_eqv (y * y) (y * y)))
        (Q'.neg_neg_eqv ((y * y) * (y * y))))
  have hSQsecond :
      ((((-(y * y)) * (x * x + (-(y * y))))).eqv
        ((-((x * x) * (y * y))) + (y * y) * (y * y))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (-(y * y)) (x * x) (-(y * y)))
      (Q'.add_eqv_congr' hnegfirst hneg2)
  have hSQexp :
      (((x * x + (-(y * y))) * (x * x + (-(y * y)))).eqv
        (((x * x) * (x * x) + (-((x * x) * (y * y))))
          + ((-((x * x) * (y * y))) + (y * y) * (y * y)))) :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (x * x) (-(y * y)) (x * x + (-(y * y))))
      (Q'.add_eqv_congr' hSQfirst hSQsecond)
  have hnegFX :
      ((-(((x * x) * (y * y) + (x * x) * (y * y)) + ((x * x) * (y * y) + (x * x) * (y * y)))).eqv
        (((-((x * x) * (y * y))) + (-((x * x) * (y * y))))
          + ((-((x * x) * (y * y))) + (-((x * x) * (y * y)))))) :=
    Q'.eqv_trans _ _ _
      (Q'.neg_add_eqv ((x * x) * (y * y) + (x * x) * (y * y)) ((x * x) * (y * y) + (x * x) * (y * y)))
      (Q'.add_eqv_congr'
        (Q'.neg_add_eqv ((x * x) * (y * y)) ((x * x) * (y * y)))
        (Q'.neg_add_eqv ((x * x) * (y * y)) ((x * x) * (y * y))))
  have hkey :
      ((((x * x + y * y) * (x * x + y * y))
          + (-(((x * x) * (y * y) + (x * x) * (y * y)) + ((x * x) * (y * y) + (x * x) * (y * y))))).eqv
        ((x * x + (-(y * y))) * (x * x + (-(y * y))))) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' hQ2exp hnegFX)
        (hcancel ((x * x) * (x * x)) ((y * y) * (y * y)) ((x * x) * (y * y))))
      (Q'.eqv_symm hSQexp)
  have hSQnn : (0 : Q') ≤ (x * x + (-(y * y))) * (x * x + (-(y * y))) :=
    SumOfSquares.q_mul_self_nonneg (x * x + (-(y * y)))
  have hsub :
      (0 : Q') ≤ (x * x + y * y) * (x * x + y * y)
        + (-(((x * x) * (y * y) + (x * x) * (y * y)) + ((x * x) * (y * y) + (x * x) * (y * y)))) :=
    Q'.le_trans' _ _ _ hSQnn (Q'.ge_of_eqv hkey)
  have hSOS :
      (((x * x) * (y * y) + (x * x) * (y * y)) + ((x * x) * (y * y) + (x * x) * (y * y)))
        ≤ (x * x + y * y) * (x * x + y * y) :=
    Q'.le_of_sub_nonneg hsub
  -- hRest : 0 ≤ FYY + FY3
  have h_yy : (0 : Q') ≤ y * y := Q'.mul_nonneg y y hy0 hy0
  have h_y3 : (0 : Q') ≤ (y * y) * y := Q'.mul_nonneg (y * y) y h_yy hy0
  have hFYYnn : (0 : Q') ≤ (y * y + y * y) + (y * y + y * y) :=
    Q'.zero_le_add _ _ (Q'.zero_le_add _ _ h_yy h_yy) (Q'.zero_le_add _ _ h_yy h_yy)
  have hFY3nn : (0 : Q') ≤ ((y * y) * y + (y * y) * y) + ((y * y) * y + (y * y) * y) :=
    Q'.zero_le_add _ _ (Q'.zero_le_add _ _ h_y3 h_y3) (Q'.zero_le_add _ _ h_y3 h_y3)
  have hRest :
      (0 : Q') ≤ ((y * y + y * y) + (y * y + y * y))
        + (((y * y) * y + (y * y) * y) + ((y * y) * y + (y * y) * y)) :=
    Q'.zero_le_add _ _ hFYYnn hFY3nn
  -- assemble
  have step :
      (((x * x) * (y * y) + (x * x) * (y * y)) + ((x * x) * (y * y) + (x * x) * (y * y)))
        ≤ (x * x + y * y) * (x * x + y * y)
          + (((y * y + y * y) + (y * y + y * y))
            + (((y * y) * y + (y * y) * y) + ((y * y) * y + (y * y) * y))) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_add_zero_eqv _)))
      (Q'.add_le_add hSOS hRest)
  have hmain :
      ((((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
          + (((x * x) * (y * y) + (x * x) * (y * y)) + ((x * x) * (y * y) + (x * x) * (y * y))))
        ≤ (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
          + ((x * x + y * y) * (x * x + y * y)
            + (((y * y + y * y) + (y * y + y * y))
              + (((y * y) * y + (y * y) * y) + ((y * y) * y + (y * y) * y)))) :=
    Q'.add_le_add_left _ _ _ step
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS)
    (Q'.le_trans' _ _ _ hmain (Q'.ge_of_eqv hRHS))

/-! ## polyI0 : the `s = 0` channel inequality. -/

theorem polyI0 (x y : Q') (hx0 : (0 : Q') ≤ x) (hy0 : (0 : Q') ≤ y)
    (hyx : y ≤ x * x) (hx1 : x * x ≤ (1 : Q')) :
    ((1 + x * x) + y * y) * ((y + y) + (x * x + y * y))
      ≤ ((x + x) + (x * y + x * y)) * ((x + x) + (x * y + x * y)) := by
  -- helper nonnegativities and leaf bounds
  have hxxnn : (0 : Q') ≤ x * x := Q'.mul_nonneg _ _ hx0 hx0
  have hyynn : (0 : Q') ≤ y * y := Q'.mul_nonneg _ _ hy0 hy0
  have hyyxx : y * y ≤ x * x := by
    have a1 : y * y ≤ (x * x) * y := Q'.mul_le_mul_of_nonneg_right y (x * x) y hyx hy0
    have a2 : (x * x) * y ≤ (x * x) * (x * x) :=
      Q'.mul_le_mul_of_nonneg_left y (x * x) (x * x) hyx hxxnn
    have a3 : (x * x) * (x * x) ≤ (x * x) * 1 :=
      Q'.mul_le_mul_of_nonneg_left (x * x) 1 (x * x) hx1 hxxnn
    exact Q'.le_trans' _ _ _ a1 (Q'.le_trans' _ _ _ a2
      (Q'.le_trans' _ _ _ a3 (Q'.le_of_eqv (Q'.mul_one_eqv (x * x)))))
  have hx4 : (x * x) * (x * x) ≤ x * x := by
    have a3 : (x * x) * (x * x) ≤ (x * x) * 1 :=
      Q'.mul_le_mul_of_nonneg_left (x * x) 1 (x * x) hx1 hxxnn
    exact Q'.le_trans' _ _ _ a3 (Q'.le_of_eqv (Q'.mul_one_eqv (x * x)))
  have hy2e : y * y ≤ (x * x) * y := Q'.mul_le_mul_of_nonneg_right y (x * x) y hyx hy0
  have hd_e : (y * y) * y ≤ (x * x) * y :=
    Q'.mul_le_mul_of_nonneg_right (y * y) (x * x) y hyyxx hy0
  have hy4t : (y * y) * (y * y) ≤ (x * x) * (y * y) :=
    Q'.mul_le_mul_of_nonneg_right (y * y) (x * x) (y * y) hyyxx hyynn
  have he : (0 : Q') ≤ (x * x) * y := Q'.mul_nonneg _ _ hxxnn hy0
  have ht : (0 : Q') ≤ (x * x) * (y * y) := Q'.mul_nonneg _ _ hxxnn hyynn
  -- LHS expansion to E_LHS
  have hLHSexp :
      (((1 + x * x) + y * y) * ((y + y) + (x * x + y * y))).eqv
        ((((y + y) + (x * x + y * y))
            + (((x * x) * y + (x * x) * y) + ((x * x) * (x * x) + (x * x) * (y * y))))
          + (((y * y) * y + (y * y) * y) + ((x * x) * (y * y) + (y * y) * (y * y)))) :=
    Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (1 + x * x) (y * y) ((y + y) + (x * x + y * y)))
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _
          (Q'.add_mul_eqv 1 (x * x) ((y + y) + (x * x + y * y)))
          (Q'.add_eqv_congr'
            (Q'.one_mul_eqv ((y + y) + (x * x + y * y)))
            (Q'.eqv_trans _ _ _
              (Q'.mul_add_eqv (x * x) (y + y) (x * x + y * y))
              (Q'.add_eqv_congr'
                (Q'.mul_add_eqv (x * x) y y)
                (Q'.mul_add_eqv (x * x) (x * x) (y * y))))))
        (Q'.eqv_trans _ _ _
          (Q'.mul_add_eqv (y * y) (y + y) (x * x + y * y))
          (Q'.add_eqv_congr'
            (Q'.mul_add_eqv (y * y) y y)
            (Q'.eqv_trans _ _ _
              (Q'.mul_add_eqv (y * y) (x * x) (y * y))
              (Q'.add_eqv_congr'
                (Q'.mul_comm_eqv (y * y) (x * x))
                (Q'.eqv_refl ((y * y) * (y * y))))))))
  -- RHS expansion helpers
  have hxhalf2 :
      ((x * (x * y + x * y)).eqv ((x * x) * y + (x * x) * y)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv x (x * y) (x * y))
      (Q'.add_eqv_congr' (Q'.eqv_symm (Q'.mul_assoc_eqv x x y))
        (Q'.eqv_symm (Q'.mul_assoc_eqv x x y)))
  have hxyx : (((x * y) * x).eqv ((x * x) * y)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (x * y) x) (Q'.eqv_symm (Q'.mul_assoc_eqv x x y))
  have hxyhalf2 :
      (((x * y) * (x + x)).eqv ((x * x) * y + (x * x) * y)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (x * y) x x)
      (Q'.add_eqv_congr' hxyx hxyx)
  have hxyhalf3 :
      (((x * y) * (x * y + x * y)).eqv ((x * x) * (y * y) + (x * x) * (y * y))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (x * y) (x * y) (x * y))
      (Q'.add_eqv_congr' (prodsq x y) (prodsq x y))
  -- RHS expansion to E_RHS
  have hRHSexp :
      ((((x + x) + (x * y + x * y)) * ((x + x) + (x * y + x * y))).eqv
        ((((x * x + x * x) + (x * x + x * x))
            + (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y)))
          + ((((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
            + (((x * x) * (y * y) + (x * x) * (y * y)) + ((x * x) * (y * y) + (x * x) * (y * y)))))) :=
    Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (x + x) (x * y + x * y) ((x + x) + (x * y + x * y)))
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _
          (Q'.mul_add_eqv (x + x) (x + x) (x * y + x * y))
          (Q'.add_eqv_congr'
            (Q'.eqv_trans _ _ _
              (Q'.add_mul_eqv x x (x + x))
              (Q'.add_eqv_congr'
                (Q'.mul_add_eqv x x x)
                (Q'.mul_add_eqv x x x)))
            (Q'.eqv_trans _ _ _
              (Q'.add_mul_eqv x x (x * y + x * y))
              (Q'.add_eqv_congr' hxhalf2 hxhalf2))))
        (Q'.eqv_trans _ _ _
          (Q'.mul_add_eqv (x * y + x * y) (x + x) (x * y + x * y))
          (Q'.add_eqv_congr'
            (Q'.eqv_trans _ _ _
              (Q'.add_mul_eqv (x * y) (x * y) (x + x))
              (Q'.add_eqv_congr' hxyhalf2 hxyhalf2))
            (Q'.eqv_trans _ _ _
              (Q'.add_mul_eqv (x * y) (x * y) (x * y + x * y))
              (Q'.add_eqv_congr' hxyhalf3 hxyhalf3)))))
  -- regroup E_LHS to S + NEG
  have hregroupL :
      (((((y + y) + (x * x + y * y))
            + (((x * x) * y + (x * x) * y) + ((x * x) * (x * x) + (x * x) * (y * y))))
          + (((y * y) * y + (y * y) * y) + ((x * x) * (y * y) + (y * y) * (y * y)))).eqv
        ((x * x + (((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y))))
          + (((x * x) * (x * x) + (y + y))
            + (y * y + (((y * y) * y + (y * y) * y) + (y * y) * (y * y)))))) := by
    -- transform PB = ee + (x4 + t) into (ee + t) + x4
    have hPB :
        ((((x * x) * y + (x * x) * y) + ((x * x) * (x * x) + (x * x) * (y * y))).eqv
          ((((x * x) * y + (x * x) * y) + (x * x) * (y * y)) + (x * x) * (x * x))) :=
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left ((x * x) * y + (x * x) * y)
          ((x * x) * (x * x) + (x * x) * (y * y)) ((x * x) * (y * y) + (x * x) * (x * x))
          (Q'.add_comm_eqv ((x * x) * (x * x)) ((x * x) * (y * y))))
        (Q'.eqv_symm (Q'.add_assoc_eqv ((x * x) * y + (x * x) * y) ((x * x) * (y * y))
          ((x * x) * (x * x))))
    -- transform PC = dd + (t + y4) into t + (y4 + dd)
    have hPC :
        ((((y * y) * y + (y * y) * y) + ((x * x) * (y * y) + (y * y) * (y * y))).eqv
          ((x * x) * (y * y) + ((y * y) * (y * y) + ((y * y) * y + (y * y) * y)))) :=
      Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv ((y * y) * y + (y * y) * y)
          ((x * x) * (y * y) + (y * y) * (y * y)))
        (Q'.add_assoc_eqv ((x * x) * (y * y)) ((y * y) * (y * y)) ((y * y) * y + (y * y) * y))
    -- transform PB + PC into (ee + (t + t)) + (x4 + (y4 + dd))
    have hPBPC :
        (((((x * x) * y + (x * x) * y) + ((x * x) * (x * x) + (x * x) * (y * y)))
            + (((y * y) * y + (y * y) * y) + ((x * x) * (y * y) + (y * y) * (y * y)))).eqv
          ((((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))
            + ((x * x) * (x * x)
              + ((y * y) * (y * y) + ((y * y) * y + (y * y) * y))))) :=
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' hPB hPC)
        (Q'.eqv_trans _ _ _
          (QPoly.q_interchange (((x * x) * y + (x * x) * y) + (x * x) * (y * y))
            ((x * x) * (x * x)) ((x * x) * (y * y))
            ((y * y) * (y * y) + ((y * y) * y + (y * y) * y)))
          (Q'.add_eqv_congr_right
            ((((x * x) * y + (x * x) * y) + (x * x) * (y * y)) + (x * x) * (y * y))
            (((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))
            ((x * x) * (x * x) + ((y * y) * (y * y) + ((y * y) * y + (y * y) * y)))
            (Q'.add_assoc_eqv ((x * x) * y + (x * x) * y) ((x * x) * (y * y))
              ((x * x) * (y * y)))))
    -- transform PA = yy + (x2 + y2) into x2 + (y2 + yy)
    have hPA :
        (((y + y) + (x * x + y * y)).eqv (x * x + (y * y + (y + y)))) :=
      Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv (y + y) (x * x + y * y))
        (Q'.add_assoc_eqv (x * x) (y * y) (y + y))
    -- transform NEGcurrent = (y2 + yy) + (x4 + (y4 + dd)) into (x4 + yy) + (y2 + (dd + y4))
    have hNEGc :
        ((((y * y + (y + y)) + ((x * x) * (x * x)
              + ((y * y) * (y * y) + ((y * y) * y + (y * y) * y)))).eqv
          (((x * x) * (x * x) + (y + y))
            + (y * y + (((y * y) * y + (y * y) * y) + (y * y) * (y * y)))))) :=
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (y * y + (y + y)) ((y + y) + y * y)
          ((x * x) * (x * x) + ((y * y) * (y * y) + ((y * y) * y + (y * y) * y)))
          (Q'.add_comm_eqv (y * y) (y + y)))
        (Q'.eqv_trans _ _ _
          (QPoly.q_interchange (y + y) (y * y) ((x * x) * (x * x))
            ((y * y) * (y * y) + ((y * y) * y + (y * y) * y)))
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_right ((y + y) + (x * x) * (x * x))
              ((x * x) * (x * x) + (y + y))
              (y * y + ((y * y) * (y * y) + ((y * y) * y + (y * y) * y)))
              (Q'.add_comm_eqv (y + y) ((x * x) * (x * x))))
            (Q'.add_eqv_congr_left ((x * x) * (x * x) + (y + y))
              (y * y + ((y * y) * (y * y) + ((y * y) * y + (y * y) * y)))
              (y * y + (((y * y) * y + (y * y) * y) + (y * y) * (y * y)))
              (Q'.add_eqv_congr_left (y * y)
                ((y * y) * (y * y) + ((y * y) * y + (y * y) * y))
                (((y * y) * y + (y * y) * y) + (y * y) * (y * y))
                (Q'.add_comm_eqv ((y * y) * (y * y)) ((y * y) * y + (y * y) * y))))))
    -- assemble the regroup
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv ((y + y) + (x * x + y * y))
        (((x * x) * y + (x * x) * y) + ((x * x) * (x * x) + (x * x) * (y * y)))
        (((y * y) * y + (y * y) * y) + ((x * x) * (y * y) + (y * y) * (y * y)))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left ((y + y) + (x * x + y * y)) _ _ hPBPC) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right ((y + y) + (x * x + y * y)) _ _ hPA) ?_
    refine Q'.eqv_trans _ _ _
      (QPoly.q_interchange (x * x) (y * y + (y + y))
        (((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))
        ((x * x) * (x * x) + ((y * y) * (y * y) + ((y * y) * y + (y * y) * y)))) ?_
    exact Q'.add_eqv_congr_left
      (x * x + (((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))) _ _ hNEGc
  -- regroup E_RHS to S + POS
  have hregroupR :
      (((((x * x + x * x) + (x * x + x * x))
            + (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y)))
          + ((((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
            + (((x * x) * (y * y) + (x * x) * (y * y)) + ((x * x) * (y * y) + (x * x) * (y * y))))).eqv
        ((x * x + (((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y))))
          + (((x * x) + ((x * x) + (x * x)))
            + ((((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
              + (((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y))))))) := by
    -- split A = (x2+x2)+(x2+x2) into x2 + (x2 + (x2+x2))
    have hA :
        ((((x * x + x * x) + (x * x + x * x))).eqv
          (x * x + (x * x + (x * x + x * x)))) :=
      Q'.add_assoc_eqv (x * x) (x * x) (x * x + x * x)
    -- right block: B + ((EE+TT)+(EE+TT)) ≃ (EE+TT) + ((EE+TT) + B)
    have hR3 :
        ((((((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
            + ((((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))
                + (((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y))))).eqv
          ((((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))
            + ((((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))
                + (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y)))))) :=
      Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv
          (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
          ((((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))
            + (((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))))
        (Q'.add_assoc_eqv
          (((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))
          (((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))
          (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y)))
    -- POScurrent right block: (EE+TT) + B ≃ B + (EE+TT)  [B = EE+EE]
    have hPOSc :
        ((((x * x) + ((x * x) + (x * x)))
            + ((((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))
                + (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y)))).eqv
          (((x * x) + ((x * x) + (x * x)))
            + ((((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
                + (((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))))) :=
      Q'.add_eqv_congr_left ((x * x) + ((x * x) + (x * x))) _ _
        (Q'.add_comm_eqv
          (((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))
          (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y)))
    -- assemble
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv ((x * x + x * x) + (x * x + x * x))
        (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
        ((((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
          + (((x * x) * (y * y) + (x * x) * (y * y)) + ((x * x) * (y * y) + (x * x) * (y * y))))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hA) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (x * x + (x * x + (x * x + x * x))) _ _
        (Q'.add_eqv_congr_left
          (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y)) _ _
          (QPoly.q_interchange ((x * x) * y + (x * x) * y) ((x * x) * y + (x * x) * y)
            ((x * x) * (y * y) + (x * x) * (y * y)) ((x * x) * (y * y) + (x * x) * (y * y))))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (x * x + (x * x + (x * x + x * x))) _ _ hR3) ?_
    refine Q'.eqv_trans _ _ _
      (QPoly.q_interchange (x * x) (x * x + (x * x + x * x))
        (((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))
        ((((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))
          + (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y)))) ?_
    exact Q'.add_eqv_congr_left
      (x * x + (((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))) _ _ hPOSc
  -- NEG ≤ POS
  have hNEG_le_NB :
      ((((x * x) * (x * x) + (y + y))
          + (y * y + (((y * y) * y + (y * y) * y) + (y * y) * (y * y))))
        ≤ (((x * x) + ((x * x) + (x * x)))
          + ((x * x) * y + ((((x * x) * y + (x * x) * y)) + (x * x) * (y * y))))) :=
    Q'.add_le_add (Q'.add_le_add hx4 (Q'.add_le_add hyx hyx))
      (Q'.add_le_add hy2e (Q'.add_le_add (Q'.add_le_add hd_e hd_e) hy4t))
  have h0_L3et :
      (0 : Q') ≤ (x * x) * y + ((((x * x) * y + (x * x) * y)) + (x * x) * (y * y)) :=
    Q'.zero_le_add _ _ he (Q'.zero_le_add _ _ (Q'.zero_le_add _ _ he he) ht)
  have hR_split :
      (((((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
          + (((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))).eqv
        (((x * x) * y + ((((x * x) * y + (x * x) * y)) + (x * x) * (y * y)))
          + ((x * x) * y + ((((x * x) * y + (x * x) * y)) + (x * x) * (y * y))))) := by
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (QPoly.q_interchange ((x * x) * y)
        (((x * x) * y + (x * x) * y) + (x * x) * (y * y)) ((x * x) * y)
        (((x * x) * y + (x * x) * y) + (x * x) * (y * y))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left ((x * x) * y + (x * x) * y) _ _
        (QPoly.q_interchange ((x * x) * y + (x * x) * y) ((x * x) * (y * y))
          ((x * x) * y + (x * x) * y) ((x * x) * (y * y)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv ((x * x) * y + (x * x) * y)
        (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
        ((x * x) * (y * y) + (x * x) * (y * y)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right
        (((x * x) * y + (x * x) * y)
          + (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y)))
        ((((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
          + ((x * x) * y + (x * x) * y))
        ((x * x) * (y * y) + (x * x) * (y * y))
        (Q'.add_comm_eqv ((x * x) * y + (x * x) * y)
          (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y)))) ?_
    exact Q'.add_assoc_eqv
      (((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
      ((x * x) * y + (x * x) * y)
      ((x * x) * (y * y) + (x * x) * (y * y))
  have hRight :
      ((x * x) * y + ((((x * x) * y + (x * x) * y)) + (x * x) * (y * y))
        ≤ ((((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
          + (((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y))))) :=
    Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_add_zero_eqv
          ((x * x) * y + ((((x * x) * y + (x * x) * y)) + (x * x) * (y * y))))))
        (Q'.add_le_add_left
          ((x * x) * y + ((((x * x) * y + (x * x) * y)) + (x * x) * (y * y))) 0
          ((x * x) * y + ((((x * x) * y + (x * x) * y)) + (x * x) * (y * y))) h0_L3et))
      (Q'.ge_of_eqv hR_split)
  have hNB_le_POS :
      ((((x * x) + ((x * x) + (x * x)))
          + ((x * x) * y + ((((x * x) * y + (x * x) * y)) + (x * x) * (y * y))))
        ≤ (((x * x) + ((x * x) + (x * x)))
          + ((((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
            + (((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))))) :=
    Q'.add_le_add (Q'.le_refl' ((x * x) + ((x * x) + (x * x)))) hRight
  have hNP :
      ((((x * x) * (x * x) + (y + y))
          + (y * y + (((y * y) * y + (y * y) * y) + (y * y) * (y * y))))
        ≤ (((x * x) + ((x * x) + (x * x)))
          + ((((x * x) * y + (x * x) * y) + ((x * x) * y + (x * x) * y))
            + (((x * x) * y + (x * x) * y) + ((x * x) * (y * y) + (x * x) * (y * y)))))) :=
    Q'.le_trans' _ _ _ hNEG_le_NB hNB_le_POS
  -- assemble
  have hLHS := Q'.eqv_trans _ _ _ hLHSexp hregroupL
  have hRHS := Q'.eqv_trans _ _ _ hRHSexp hregroupR
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ hNP) (Q'.ge_of_eqv hRHS))

end YMGap.Continuum.FusionChannelIneq

#print axioms YMGap.Continuum.FusionChannelIneq.polyI2
#print axioms YMGap.Continuum.FusionChannelIneq.polyI1
#print axioms YMGap.Continuum.FusionChannelIneq.polyI0

#print axioms YMGap.Continuum.FusionChannelIneq.polyI2
#print axioms YMGap.Continuum.FusionChannelIneq.polyI1
#print axioms YMGap.Continuum.FusionChannelIneq.polyI0
