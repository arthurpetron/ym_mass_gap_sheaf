/-
# A sharp completed norm bound from approximate dense dual tests

The error vector may depend on the dense test.  A squared-error estimate
relative to that test and an exact pairing identity imply a squared-norm
estimate for the completed target.  No finite-rank map, Gram inverse,
representative selection, or division by a possibly zero norm is used.
-/

import YMGap.Continuum.GNSDenseCompletionLaws
import YMGap.Continuum.GNSPairApproximationError
import YMGap.Continuum.EffMassConvergence
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.GNSDenseDualNormBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSDenseCompletionLaws
open YMGap.Continuum.GNSPairApproximationError
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

local infix:50 " ≈ " => Q'.eqv

private theorem leEv_of_double_le_budget_add {A B : CReal}
    (h : leEv (mul (ofQ' 2) A) (add B A)) : leEv A B := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  refine ⟨N, fun n hn => ?_⟩
  have hstep := hN n hn
  change (2 : Q') * A.approx n ≤ (B.approx n + A.approx n) + epsilon at hstep
  have hshift := Q'.add_le_add_right _ _ (-(A.approx n)) hstep
  have hleft : (2 : Q') * A.approx n + -(A.approx n) ≈ A.approx n :=
    poly_identity_of_normal_eq
      (.add (.mul (.const 2) (.var 0)) (.neg (.var 0)))
      (.var 0) (by decide) (fun _ => A.approx n)
  have hright : ((B.approx n + A.approx n) + epsilon) + -(A.approx n) ≈
      B.approx n + epsilon :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.neg (.var 1)))
      (.add (.var 0) (.var 2)) (by decide)
      (fun | 0 => B.approx n | 1 => A.approx n | _ => epsilon)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hshift (Q'.le_of_eqv hright))

/-- Dense dual inequalities determine a completed squared-norm cap.  The
test sequence is the supplied Cauchy representative of `y`; no quotient
representative is selected by choice. -/
private theorem norm_le_of_dense_quadratic (D : GNSData)
    (y : GNSCompletionSpace D) (B : RC)
    (h : ∀ q : D.V,
      RCle (RCscale 2 (D.cinnerCompl y (embedV D q)))
        (RCadd B (normSq (embedV D q)))) :
    RCle (normSq y) B := by
  revert B h
  refine Quotient.inductionOn y ?_
  intro Y B h
  revert h
  refine Quotient.inductionOn B ?_
  intro b h
  have hleft : ConvergesTo
      (fun n => mul (ofQ' 2) (D.cinnerRep Y (constCauchy D (Y.seq n))))
      (mul (ofQ' 2) (D.cinnerRep Y Y)) :=
    YMGap.Continuum.EffMassConvergence.convergesTo_scale 2
      (fixed_input_converges Y Y)
  have hright : ConvergesTo
      (fun n => add b (ofQ' (D.B (Y.seq n) (Y.seq n))))
      (add b (D.cinnerRep Y Y)) :=
    convergesTo_add (convergesTo_const b)
      (convergesTo_ofQ'CauchySeq (D.cInnerSeq Y Y) (D.cInnerQCauchy Y Y))
  have hterm (n : Nat) :
      leEv (mul (ofQ' 2) (D.cinnerRep Y (constCauchy D (Y.seq n))))
        (add b (ofQ' (D.B (Y.seq n) (Y.seq n)))) := by
    have hn := h (Y.seq n)
    change RCle (RCscale 2
      (D.cinnerCompl (Quotient.mk (cauchySetoid D) Y)
        (embedV D (Y.seq n))))
      (RCadd (Quotient.mk crealSetoid b)
        (D.cinnerCompl (embedV D (Y.seq n)) (embedV D (Y.seq n)))) at hn
    have he : D.cinnerCompl (embedV D (Y.seq n)) (embedV D (Y.seq n)) =
        Quotient.mk crealSetoid (ofQ' (D.B (Y.seq n) (Y.seq n))) :=
      D.cinnerCompl_embed (Y.seq n) (Y.seq n)
    rw [he] at hn
    exact hn
  have hlim := leEv_of_convergesTo_le hleft hright hterm
  exact leEv_of_double_le_budget_add hlim

private theorem norm_smul (S : SmulGNSData) (q : Q')
    (x : GNSCompletionSpace S.toGNSData) :
    normSq (S.cSmul q x) = RCscale (q*q) (normSq x) := by
  unfold normSq
  rw [S.cinnerCompl_cSmul_left, S.cinnerCompl_cSmul_right, RCscale_RCscale]

private theorem scale_cancel_pos (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (a b : RC) (h : RCle (RCscale epsilon a) (RCscale epsilon b)) :
    RCle a b := by
  let r := Q'.recipPos epsilon hepsilon
  have hr : (0 : Q') ≤ r := Q'.le_of_lt (Q'.recipPos_pos epsilon hepsilon)
  have hc : r * epsilon ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv r epsilon)
      (Q'.mul_recipPos_eqv epsilon hepsilon)
  have hh := RCscale_mono hr h
  rw [RCscale_RCscale, RCscale_RCscale,
    scale_congr hc a, scale_congr hc b, RCscale_one, RCscale_one] at hh
  exact hh

/-- If every literal dense test has an exact dual pairing represented by an
error vector with squared norm at most `epsilon` times the test's squared
norm, the completed target obeys the same sharp squared-norm coefficient.
The strictly positive rational epsilon is a supplied tolerance, not an
inverse of a vector norm. -/
theorem norm_le_of_dense_approximate_dual (S : SmulGNSData)
    (x y : GNSCompletionSpace S.toGNSData)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (error : S.toGNSData.V → GNSCompletionSpace S.toGNSData)
    (hpair : ∀ q, S.toGNSData.cinnerCompl y (embedV S.toGNSData q) =
      S.toGNSData.cinnerCompl x (error q))
    (herror : ∀ q, RCle (normSq (error q))
      (RCscale epsilon (normSq (embedV S.toGNSData q)))) :
    RCle (normSq y) (RCscale epsilon (normSq x)) := by
  let D := S.toGNSData
  apply norm_le_of_dense_quadratic D y (RCscale epsilon (normSq x))
  intro q
  have hyoung := pairing_young S (S.cSmul epsilon x) (error q)
    (RCscale (epsilon*epsilon) (normSq x))
    (RCscale epsilon (normSq (embedV D q)))
    (by rw [norm_smul]; exact RCle_refl _) (herror q)
  have hscaled := RCscale_mono (by decide : (0 : Q') ≤ 2) hyoung.1
  rw [RCscale_RCscale,
    scale_congr (by decide : Q'.eqv ((2 : Q') * HalfPow.half) 1) _,
    RCscale_one] at hscaled
  rw [S.cinnerCompl_cSmul_left, RCscale_RCscale] at hscaled
  have hleft : RCscale (2*epsilon) (D.cinnerCompl x (error q)) =
      RCscale epsilon (RCscale 2 (D.cinnerCompl x (error q))) := by
    rw [RCscale_RCscale]
    exact scale_congr (Q'.mul_comm_eqv 2 epsilon) _
  have hright : RCadd (RCscale (epsilon*epsilon) (normSq x))
      (RCscale epsilon (normSq (embedV D q))) =
      RCscale epsilon (RCadd (RCscale epsilon (normSq x))
        (normSq (embedV D q))) := by
    rw [RCscale_RCadd, RCscale_RCscale]
  rw [hleft, hright] at hscaled
  have hbound := scale_cancel_pos epsilon hepsilon _ _ hscaled
  rw [hpair q]
  exact hbound

end YMGap.Continuum.GNSDenseDualNormBound

#print axioms YMGap.Continuum.GNSDenseDualNormBound.norm_le_of_dense_approximate_dual
