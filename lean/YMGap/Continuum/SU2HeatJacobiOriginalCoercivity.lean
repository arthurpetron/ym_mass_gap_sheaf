/-
# A global rational envelope for the original finite SU(2) heat prefix

The factors, differentiated product, and final character prefix are the
original Jacobi objects. A computed block of original amplitudes in [1/4,3/4]
pays one factor `1-(1-x)/8` per undifferentiated factor. The derivative loses
at most one factor. The original uniform floor pays the explicit finite
derivative comparison error, with multiplicative slack three.

This is a scalar estimate, not an interacting partition estimate, an H1
survival estimate, or a continuum / all-group result. No logarithmic or
infinite-product coercivity assumption is used. The evaluated original
polynomial corollary is pointwise; it does not construct a Haar certificate.
-/

import YMGap.Continuum.SU2HeatJacobiActiveFactorCount
import YMGap.Continuum.SU2HeatJacobiProductAmplification
import YMGap.Continuum.JacobiShiftedPositiveCoefficients
import YMGap.Continuum.SU2HeatJacobiFinitePrefixMargin

namespace YMGap.Continuum.SU2HeatJacobiOriginalCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.HKConv (mul_le_mul')
open YMGap.Continuum.ThetaConv (gFac Ppart)
open YMGap.Continuum.JTPFullProductDerivativeNormalization
open YMGap.Continuum.SU2HeatJacobiActiveFactorCount
open YMGap.Continuum.SU2HeatJacobiProductAmplification (retainedCount)
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor (standardPointwiseHeatPartial)

local infix:50 " ≈ " => Q'.eqv

/-- The same-nome global envelope base. -/
def decay (x : Q') : Q' := 1 + -(Q'.mkPos 1 8 (by decide) * (1-x))

theorem decay_bounds {x : Q'} (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q')) :
    Q'.mkPos 3 4 (by decide) ≤ decay x ∧ decay x ≤ (1 : Q') := by
  have hd0 : (0 : Q') ≤ 1-x := Q'.sub_nonneg_of_le hxhi
  have hn : -x ≤ (1 : Q') := Q'.le_trans' _ _ _ (Q'.neg_le_neg hxlo)
    (Q'.le_of_eqv (Q'.neg_neg_eqv 1))
  have hd2 : 1-x ≤ (2 : Q') := Q'.le_trans' _ _ _
    (Q'.add_le_add_left 1 _ _ hn) (Q'.le_of_eqv (by decide))
  have he0 := Q'.mul_nonneg (Q'.mkPos 1 8 (by decide)) (1-x) (by decide) hd0
  have he2 := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.mkPos 1 8 (by decide)) hd2 (by decide)
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide))
      (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg he2))
  · exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg he0)) (Q'.le_of_eqv (by decide))

private theorem swap_first (a b c : Q') : a*(b*c) ≈ b*(a*c) :=
  poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.var 1) (.mul (.var 0) (.var 2)))
    (by decide) (fun | 0 => a | 1 => b | _ => c)

private theorem factor_mono {a x : Q'} (ha : (0 : Q') ≤ a) (hx : x ≤ (1 : Q')) :
    HKPos.factor a x ≤ HKPos.factor a 1 := by
  exact Q'.add_le_add_left 1 _ _ (Q'.add_le_add_right _ _ (a*a)
    (Q'.mul_le_mul_of_nonneg_left _ _ (a+a) hx (Q'.zero_le_add _ _ ha ha)))

private theorem factor_gap (a x e : Q') :
    (1 + -(e*(1-x)))*HKPos.factor a 1 + -(HKPos.factor a x) ≈
      (1-x)*((a+a) + -(e*HKPos.factor a 1)) := by
  exact poly_identity_of_normal_eq
    (.add (.mul (.add (.const 1) (.neg (.mul (.var 2) (.add (.const 1) (.neg (.var 1))))))
      (.add (.const 1) (.add (.mul (.add (.var 0) (.var 0)) (.const 1)) (.mul (.var 0) (.var 0)))))
      (.neg (.add (.const 1) (.add (.mul (.add (.var 0) (.var 0)) (.var 1)) (.mul (.var 0) (.var 0))))))
    (.mul (.add (.const 1) (.neg (.var 1)))
      (.add (.add (.var 0) (.var 0)) (.neg (.mul (.var 2)
        (.add (.const 1) (.add (.mul (.add (.var 0) (.var 0)) (.const 1)) (.mul (.var 0) (.var 0))))))))
    (by decide) (fun | 0 => a | 1 => x | _ => e)

private theorem factor_active {a x : Q'}
    (ha0 : Q'.mkPos 1 4 (by decide) ≤ a) (ha1 : a ≤ Q'.mkPos 3 4 (by decide))
    (hx : x ≤ (1 : Q')) : HKPos.factor a x ≤ decay x * HKPos.factor a 1 := by
  have han : (0 : Q') ≤ a := Q'.le_trans' _ _ _ (by decide) ha0
  have halt : a < (1 : Q') := HKPos.q_lt_of_le_of_lt ha1 (by decide)
  have hfour := ThetaConv.factor_le_four han halt (Q'.le_refl' 1)
  have he : Q'.mkPos 1 8 (by decide)*HKPos.factor a 1 ≤ a+a :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.mkPos 1 8 (by decide)) hfour (by decide))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide)) (Q'.add_le_add ha0 ha0))
  apply Q'.le_of_sub_nonneg
  exact Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hx) (Q'.sub_nonneg_of_le he))
    (Q'.ge_of_eqv (factor_gap a x (Q'.mkPos 1 8 (by decide))))

private theorem gFac_mono {q x : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hx : x ≤ (1 : Q')) (k : Nat) : gFac q x k ≤ gFac q 1 k :=
  Q'.mul_le_mul_of_nonneg_left _ _ _
    (factor_mono (Q'.le_of_lt (HKPos.pow_succ_pos_lt_one hq0 hq1 (2*k)).1) hx)
    (Q'.le_of_lt (HKPos.one_sub_pos (ThetaConv.uAmp_pos_lt_one hq0 hq1 k).2))

private theorem gFac_active {q x : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hx : x ≤ (1 : Q')) (k : Nat)
    (ha0 : Q'.mkPos 1 4 (by decide) ≤ HKPos.geoAmp q k)
    (ha1 : HKPos.geoAmp q k ≤ Q'.mkPos 3 4 (by decide)) :
    gFac q x k ≤ decay x * gFac q 1 k := by
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (factor_active ha0 ha1 hx)
      (Q'.le_of_lt (HKPos.one_sub_pos (ThetaConv.uAmp_pos_lt_one hq0 hq1 k).2)))
    (Q'.le_of_eqv (swap_first _ _ _))

private theorem derivative_nonnegative {q x : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q')) (hx : (-1 : Q') ≤ x) (N : Nat) :
    (0 : Q') ≤ fullProdDx q x N :=
  Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ (ThetaConv.Ppart_nonneg hq0 hq1 hx N)
    (HKConv.Spart_nonneg hq0 hq1 hx N))
    (Q'.ge_of_eqv (fullProdDx_eqv_Ppart_mul_Spart hq0 hq1 hx N))

private theorem partial_envelope {q x : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q')) (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q'))
    (start count : Nat)
    (hblock : ∀ j, j < count → Q'.mkPos 1 4 (by decide) ≤ HKPos.geoAmp q (start+j) ∧
      HKPos.geoAmp q (start+j) ≤ Q'.mkPos 3 4 (by decide)) : ∀ N : Nat,
    Ppart q x N ≤ (decay x)^retainedCount start count N * Ppart q 1 N ∧
    decay x * fullProdDx q x N ≤ (decay x)^retainedCount start count N * fullProdDx q 1 N
  | 0 => by
      simp only [retainedCount, Nat.zero_sub, Nat.min_zero, Q'.pow_zero,
        ThetaConv.Ppart, fullProdDx_zero]
      exact ⟨Q'.ge_of_eqv (Q'.one_mul_eqv 1), Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_zero_eqv _)) (Q'.ge_of_eqv (Q'.mul_zero_eqv _))⟩
  | N+1 => by
      have ih := partial_envelope hq0 hq1 hxlo hxhi start count hblock N
      let r := decay x
      let z := r^retainedCount start count N
      have hr : (0 : Q') ≤ r := Q'.le_trans' _ _ _ (by decide) (decay_bounds hxlo hxhi).1
      have hr1 : r ≤ (1 : Q') := (decay_bounds hxlo hxhi).2
      have hP := ThetaConv.Ppart_nonneg hq0 hq1 hxlo N
      have hD := derivative_nonnegative hq0 hq1 hxlo N
      have hg := ThetaConv.gFac_nonneg (x := (1 : Q')) hq0 hq1 (by decide) N
      have hs := Q'.le_of_lt (JacobiShiftedPositiveCoefficients.slope_pos hq0 hq1 N)
      have inactive (hc : retainedCount start count (N+1)=retainedCount start count N) :
          Ppart q x (N+1) ≤ r^retainedCount start count (N+1)*Ppart q 1 (N+1) ∧
          r*fullProdDx q x (N+1) ≤ r^retainedCount start count (N+1)*fullProdDx q 1 (N+1) := by
        rw [hc, ThetaConv.Ppart_succ, ThetaConv.Ppart_succ, fullProdDx_succ, fullProdDx_succ]
        have hp := mul_le_mul' hP hg ih.1 (gFac_mono hq0 hq1 hxhi N)
        have hd := mul_le_mul' (Q'.mul_nonneg _ _ hr hD) hg ih.2 (gFac_mono hq0 hq1 hxhi N)
        have hrp : r*Ppart q x N ≤ z*Ppart q 1 N := Q'.le_trans' _ _ _
          (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hr1 hP)
            (Q'.le_of_eqv (Q'.one_mul_eqv _))) ih.1
        have hd2 := Q'.mul_le_mul_of_nonneg_right _ _ _ hrp hs
        constructor
        · exact Q'.le_trans' _ _ _ hp (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
        · exact Q'.le_trans' _ _ _
            (Q'.le_of_eqv (poly_identity_of_normal_eq
              (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4))))
              (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.mul (.var 0) (.var 3)) (.var 4)))
              (by decide) (fun | 0 => r | 1 => fullProdDx q x N | 2 => gFac q x N | 3 => Ppart q x N | _ => gFacDx q N)))
            (Q'.le_trans' _ _ _ (Q'.add_le_add hd hd2)
              (Q'.ge_of_eqv (poly_identity_of_normal_eq
                (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4))))
                (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.mul (.var 0) (.var 3)) (.var 4)))
                (by decide) (fun | 0 => z | 1 => fullProdDx q 1 N | 2 => gFac q 1 N | 3 => Ppart q 1 N | _ => gFacDx q N))))
      cases (inferInstance : Decidable (start ≤ N)) with
      | isFalse hstart =>
          exact inactive (by unfold retainedCount; omega)
      | isTrue hstart =>
          cases (inferInstance : Decidable (N < start+count)) with
          | isFalse hstop =>
              exact inactive (by unfold retainedCount; omega)
          | isTrue hstop =>
              have hj : N-start < count := by omega
              have hi : start+(N-start)=N := by omega
              have hb := hblock (N-start) hj
              rw [hi] at hb
              have hc : retainedCount start count (N+1)=retainedCount start count N+1 := by
                unfold retainedCount
                omega
              rw [hc, Q'.pow_succ, ThetaConv.Ppart_succ, ThetaConv.Ppart_succ,
                fullProdDx_succ, fullProdDx_succ]
              have hf := gFac_active hq0 hq1 hxhi N hb.1 hb.2
              have hp := mul_le_mul' hP (Q'.mul_nonneg _ _ hr hg) ih.1 hf
              have hd := mul_le_mul' (Q'.mul_nonneg _ _ hr hD)
                (Q'.mul_nonneg _ _ hr hg) ih.2 hf
              have hd2 := Q'.mul_le_mul_of_nonneg_right _ _ _
                (Q'.mul_le_mul_of_nonneg_left _ _ r ih.1 hr) hs
              constructor
              · exact Q'.le_trans' _ _ _ hp (Q'.le_of_eqv
                  (poly_identity_of_normal_eq
                    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
                    (.mul (.mul (.var 2) (.var 0)) (.mul (.var 1) (.var 3)))
                    (by decide) (fun | 0 => z | 1 => Ppart q 1 N | 2 => r | _ => gFac q 1 N)))
              · exact Q'.le_trans' _ _ _
                  (Q'.le_of_eqv (poly_identity_of_normal_eq
                    (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4))))
                    (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.mul (.var 0) (.var 3)) (.var 4)))
                    (by decide) (fun | 0 => r | 1 => fullProdDx q x N | 2 => gFac q x N | 3 => Ppart q x N | _ => gFacDx q N)))
                  (Q'.le_trans' _ _ _ (Q'.add_le_add hd hd2)
                    (Q'.le_of_eqv (poly_identity_of_normal_eq
                      (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
                        (.mul (.mul (.var 2) (.mul (.var 0) (.var 4))) (.var 5)))
                      (.mul (.mul (.var 2) (.var 0))
                        (.add (.mul (.var 1) (.var 3)) (.mul (.var 4) (.var 5))))
                      (by decide) (fun | 0 => z | 1 => fullProdDx q 1 N | 2 => r | 3 => gFac q 1 N | 4 => Ppart q 1 N | _ => gFacDx q N))))

/-- The complete computed active block, losing exactly at most one factor
under differentiation. No heat-series or limit estimate is assumed. -/
theorem fullProdDx_envelope {q x : Q'} (hq0 : (0 : Q') < q)
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q'))
    (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q'))
    (N : Nat) (hN : activeFactorStart q + activeFactorCount q ≤ N) :
    fullProdDx q x N ≤ (decay x)^(activeFactorCount q-1)*fullProdDx q 1 N := by
  have h := (partial_envelope hq0 hq1 hxlo hxhi (activeFactorStart q) (activeFactorCount q)
    (activeFactor_amplitude_bounds hq hq1) N).2
  have hc : retainedCount (activeFactorStart q) (activeFactorCount q) N=activeFactorCount q := by
    unfold retainedCount
    omega
  rw [hc] at h
  have hn := activeFactorCount_two hq hq1
  have he : activeFactorCount q=activeFactorCount q-1+1 := by omega
  have hr : (0 : Q') < decay x := Q'.pos_of_lt_of_le (by decide) (decay_bounds hxlo hxhi).1
  apply HKConvGen.mul_le_mul_left_cancel hr
  have hp : (decay x)^(activeFactorCount q)*fullProdDx q 1 N ≈
      decay x*((decay x)^(activeFactorCount q-1)*fullProdDx q 1 N) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_of_eq
        (congrArg (fun k => (decay x)^k) he))) (Q'.mul_assoc_eqv _ _ _)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv hp)

private theorem derivative_floor {q x : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q')) (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q'))
    (N : Nat) (hN : 1 ≤ N) :
    2*(q*SU2PointwiseHeatStrictFloor.floor q) ≤ fullProdDx q x N := by
  have h := Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q')
    (SU2PointwiseHeatStrictFloor.nome_floor_le_Rhalf_approx hq0 hq1 hxlo hxhi N hN)
    (by decide)
  have hp : 2*(JTPIdentity.Rhalf hq0 hq1 hxlo hxhi).approx N ≈
      Ppart q x N*HKConv.Spart q x N := by
    change 2*(HalfPow.half*(Ppart q x N*HKConv.Spart q x N)) ≈ _
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (by decide : (2 : Q')*HalfPow.half ≈ 1))
        (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
    (Q'.ge_of_eqv (fullProdDx_eqv_Ppart_mul_Spart hq0 hq1 hxlo N)))

private theorem comparison_slack {D h e : Q'}
    (hc : Q'.abs (D + -h) ≤ e) (hf : 2*e ≤ D) :
    2*h ≤ 3*D ∧ D ≤ 2*h := by
  have hd := ExpNeg.le_add_of_abs_sub_le hc
  have hh := ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (ExpNeg.abs_sub_comm D h)) hc)
  have hf0 := Q'.sub_nonneg_of_le hf
  constructor
  · apply Q'.le_of_sub_nonneg
    have hz := Q'.zero_le_add _ _ hf0
      (Q'.mul_nonneg (2 : Q') _ (by decide) (Q'.sub_nonneg_of_le hh))
    exact Q'.le_trans' _ _ _ hz (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.mul (.const 2) (.var 2))))
        (.mul (.const 2) (.add (.add (.var 0) (.var 2)) (.neg (.var 1)))))
      (.add (.mul (.const 3) (.var 0)) (.neg (.mul (.const 2) (.var 1))))
      (by decide) (fun | 0 => D | 1 => h | _ => e)))
  · apply Q'.le_of_sub_nonneg
    have hz := Q'.zero_le_add _ _ hf0
      (Q'.mul_nonneg (2 : Q') _ (by decide) (Q'.sub_nonneg_of_le hd))
    exact Q'.le_trans' _ _ _ hz (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.mul (.const 2) (.var 2))))
        (.mul (.const 2) (.add (.add (.var 1) (.var 2)) (.neg (.var 0)))))
      (.add (.mul (.const 2) (.var 1)) (.neg (.var 0)))
      (by decide) (fun | 0 => D | 1 => h | _ => e)))

/-- A literal label-count cutoff: the whole computed active block, the
original derivative-error cutoff, and the original finite positive floor. -/
def coercivityCutoff (q : Q') : Nat :=
  max (activeFactorStart q + activeFactorCount q)
    (max (FiniteJacobiDerivativeComparison.derivativeCutoff q
      (q*SU2PointwiseHeatStrictFloor.floor q)) (SU2PointwiseHeatStrictFloor.finiteCutoff q))

private theorem original_comparison {q x : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q')) (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q'))
    (N : Nat) (hN : coercivityCutoff q ≤ N) :
    2*(2*JTPIdentity.dPartial q x N) ≤ 3*fullProdDx q x N ∧
      fullProdDx q x N ≤ 2*(2*JTPIdentity.dPartial q x N) := by
  have hf : SU2PointwiseHeatStrictFloor.finiteCutoff q ≤ N :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hN
  have hN1 : 1 ≤ N := Nat.le_trans (Nat.le_max_left _ _) hf
  have hd : FiniteJacobiDerivativeComparison.derivativeCutoff q
      (q*SU2PointwiseHeatStrictFloor.floor q) ≤ N :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hN
  exact comparison_slack
    (FiniteJacobiDerivativeComparison.fullProdDx_sub_two_dPartial_close hq0 hq1 hxhi hxlo
      (HKPos.q_mul_pos hq0 (SU2PointwiseHeatStrictFloor.floor_pos hq0 hq1)) N hd)
    (derivative_floor hq0 hq1 hxlo hxhi N hN1)

/-- The ORIGINAL signed character prefix, uniformly for every rational
x in [-1,1] and every label count beyond the computed cutoff. -/
theorem standardPointwiseHeatPartial_envelope {q x : Q'}
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q'))
    (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q'))
    (N : Nat) (hN : coercivityCutoff q ≤ N) :
    standardPointwiseHeatPartial q x N ≤
      3*(decay x)^(activeFactorCount q-1)*standardPointwiseHeatPartial q 1 N := by
  have hq0 : (0 : Q') < q := Q'.pos_of_lt_of_le (by decide) hq
  let b := (decay x)^(activeFactorCount q-1)
  have hb : (0 : Q') ≤ b := Q'.pow_nonneg _
    (Q'.le_trans' _ _ _ (by decide) (decay_bounds hxlo hxhi).1) _
  have hx := (original_comparison hq0 hq1 hxlo hxhi N hN).1
  have h1 := (original_comparison (x := (1 : Q')) hq0 hq1 (by decide) (by decide) N hN).2
  have hen := fullProdDx_envelope hq0 hq hq1 hxlo hxhi N
    (Nat.le_trans (Nat.le_max_left _ _) hN)
  have hraw : 2*(2*JTPIdentity.dPartial q x N) ≤
      3*(b*(2*(2*JTPIdentity.dPartial q 1 N))) :=
    Q'.le_trans' _ _ _ hx (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (3 : Q') hen (by decide))
      (Q'.mul_le_mul_of_nonneg_left _ _ (3 : Q')
        (Q'.mul_le_mul_of_nonneg_left _ _ b h1 hb) (by decide)))
  have pinx := SU2PointwiseHeatPositiveCompletion.nome_mul_standardPointwiseHeatPartial_eqv_dPartial q x N
  have pin1 := SU2PointwiseHeatPositiveCompletion.nome_mul_standardPointwiseHeatPartial_eqv_dPartial q 1 N
  have hleft : (4*q)*standardPointwiseHeatPartial q x N ≈ 2*(2*JTPIdentity.dPartial q x N) :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.mul (.mul (.const 4) (.var 0)) (.var 1))
        (.mul (.const 2) (.mul (.const 2) (.mul (.var 0) (.var 1))))
        (by decide) (fun | 0 => q | _ => standardPointwiseHeatPartial q x N))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ pinx))
  have hright : 3*(b*(2*(2*JTPIdentity.dPartial q 1 N))) ≈
      (4*q)*(3*b*standardPointwiseHeatPartial q 1 N) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm pin1)))))
      (poly_identity_of_normal_eq
        (.mul (.const 3) (.mul (.var 0) (.mul (.const 2) (.mul (.const 2) (.mul (.var 1) (.var 2))))))
        (.mul (.mul (.const 4) (.var 1)) (.mul (.mul (.const 3) (.var 0)) (.var 2)))
        (by decide) (fun | 0 => b | 1 => q | _ => standardPointwiseHeatPartial q 1 N))
  exact HKConvGen.mul_le_mul_left_cancel (HKPos.q_mul_pos (by decide) hq0)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) (Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv hright)))

/-- Inclusive original cutoff convention: labels 0,...,K, with the same
computed cutoff independent of x. -/
theorem original_heat_envelope {q x : Q'}
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q'))
    (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q'))
    (K : Nat) (hK : coercivityCutoff q ≤ K+1) :
    standardPointwiseHeatPartial q x (K+1) ≤
      3*(decay x)^(activeFactorCount q-1)*standardPointwiseHeatPartial q 1 (K+1) :=
  standardPointwiseHeatPartial_envelope hq hq1 hxlo hxhi (K+1) hK

/-- The SAME literal original RatPoly heatPrefix at its actual environment.
The scalar interval is supplied explicitly; no Haar order is inferred. -/
theorem original_heatPrefix_eval_envelope {q : Q'}
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q'))
    (K : Nat) (hK : coercivityCutoff q ≤ K+1)
    (X : SU2QuaternionPolynomialHaarCarrier.RatPoly) (rho : Nat → Q')
    (hxlo : (-1 : Q') ≤ SU2QuaternionPolynomialHaarCarrier.evalRatPoly rho X)
    (hxhi : SU2QuaternionPolynomialHaarCarrier.evalRatPoly rho X ≤ (1 : Q')) :
    SU2QuaternionPolynomialHaarCarrier.evalRatPoly rho
      (QuaternionHaarHeatCertificate.heatPrefix q K X) ≤
      3*(decay (SU2QuaternionPolynomialHaarCarrier.evalRatPoly rho X))^
        (activeFactorCount q-1)*standardPointwiseHeatPartial q 1 (K+1) :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (SU2HeatJacobiFinitePrefixMargin.eval_heatPrefix q K X rho))
    (original_heat_envelope hq hq1 hxlo hxhi K hK)

end YMGap.Continuum.SU2HeatJacobiOriginalCoercivity

#print axioms YMGap.Continuum.SU2HeatJacobiOriginalCoercivity.decay
#print axioms YMGap.Continuum.SU2HeatJacobiOriginalCoercivity.decay_bounds
#print axioms YMGap.Continuum.SU2HeatJacobiOriginalCoercivity.fullProdDx_envelope
#print axioms YMGap.Continuum.SU2HeatJacobiOriginalCoercivity.coercivityCutoff
#print axioms YMGap.Continuum.SU2HeatJacobiOriginalCoercivity.standardPointwiseHeatPartial_envelope
#print axioms YMGap.Continuum.SU2HeatJacobiOriginalCoercivity.original_heat_envelope
#print axioms YMGap.Continuum.SU2HeatJacobiOriginalCoercivity.original_heatPrefix_eval_envelope
