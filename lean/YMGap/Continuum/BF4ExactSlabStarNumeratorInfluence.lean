/-
# Numerator-sensitive control of the actual conditional projection

Completing the square in the retained exterior form gives
  L ||p-Jr||_F^2 + ||N p||_G^2 >= L ||p||_F^2
for every original polynomial p and every exterior polynomial r. Passing
this estimate through the ACTUAL conditional Cauchy representative yields
  L ||C p||_F^2 <= ||N p||_G^2.

Applied to the explicitly free-centered input, the numerator retains its
signed cancellations BEFORE taking a squared norm. The full input energy
is not discounted by the coarse ratio L/U. Every complementary original
factor remains in G. There is no assertion that this numerator is small
uniformly over polynomials, links, volume or physical scaling; no global
coercivity or continuum gap is proved here.
-/

import YMGap.Continuum.BF4ExactSlabPolynomialDirichletComparison

namespace YMGap.Continuum.BF4ExactSlabStarNumeratorInfluence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarCompletedInverse
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarFreeCentering
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabPolynomialDirichletComparison
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

private theorem square_expand (D : GNSData) (c : Q') (a b : D.V) :
    D.B (D.sub (D.smul c a) b) (D.sub (D.smul c a) b) ≈
      ((c*c)*D.B a a + -(c*D.B a b)) + (-(c*D.B a b) + D.B b b) := by
  have haa : D.B (D.smul c a) (D.smul c a) ≈ (c*c)*D.B a a :=
    Q'.eqv_trans _ _ _ (D.B_smul_left c a (D.smul c a))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (D.B_smul_right c a a))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
  have hab := Q'.neg_eqv_congr _ _ (D.B_smul_left c a b)
  exact Q'.eqv_trans _ _ _ (D.B_sub_diag_expand (D.smul c a) b)
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' haa hab)
      (Q'.add_eqv_congr' hab (Q'.eqv_refl _)))

/-- Square completion, with no division by a possibly null vector norm. -/
private theorem variational_bound (D : GNSData) (L a m : Q')
    (hL : (0 : Q') ≤ L) (r n : D.V) (hm : L*D.B r r ≤ m) :
    L*a ≤ L*((a + -(D.B r n)) + (-(D.B r n) + m)) + D.B n n := by
  have hs := Q'.le_trans' _ _ _ (D.self_nonneg (D.sub (D.smul L r) n))
    (Q'.le_of_eqv (square_expand D L r n))
  have ht := Q'.mul_nonneg _ _ hL (Q'.sub_nonneg_of_le hm)
  have he :
      (((L*L)*D.B r r + -(L*D.B r n)) + (-(L*D.B r n) + D.B n n)) +
        L*(m + -(L*D.B r r)) ≈
      (L*((a + -(D.B r n)) + (-(D.B r n) + m)) + D.B n n) + -(L*a) :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 1))
        (.neg (.mul (.var 0) (.var 2))))
        (.add (.neg (.mul (.var 0) (.var 2))) (.var 3)))
        (.mul (.var 0) (.add (.var 4) (.neg (.mul (.var 0) (.var 1))))))
      (.add (.add (.mul (.var 0)
        (.add (.add (.var 5) (.neg (.var 2))) (.add (.neg (.var 2)) (.var 4))))
        (.var 3)) (.neg (.mul (.var 0) (.var 5))))
      (by decide) (fun
        | 0 => L | 1 => D.B r r | 2 => D.B r n
        | 3 => D.B n n | 4 => m | _ => a)
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _
      (show (0 : Q') ≤ _ from by simpa only [Q'.zero_add'] using Q'.add_le_add hs ht)
      (Q'.le_of_eqv he))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (i : PhysicalLink extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "G" => exteriorData hw0 hw1 K extent hK i.val i.property
local notation "J" => probeMap hw0 hw1 K extent hK i.val i.property
local notation "M" => normalizerMap hw0 hw1 K extent hK i.val i.property
local notation "N" => numeratorMap hw0 hw1 K extent hK i.val i.property
local notation "Q" => conditionalUpdate hw0 hw1 K extent hK i.val i.property
local notation "P" => projections hw0 hw1 K extent hK
local notation "L" => lowerFactor w

/-- Actual signed numerator, squared only after its finite Haar integration. -/
def numeratorEnergy (p : (F).V) : Q' := (G).B (N p) (N p)

theorem numeratorEnergy_nonnegative (p : (F).V) :
    (0 : Q') ≤ numeratorEnergy hw0 hw1 K extent hK i p := (G).self_nonneg (N p)

/-- The same exterior background controls EVERY finite exterior test. -/
theorem probe_variational_bound (p : (F).V) (r : (G).V) :
    L*(F).B p p ≤ L*(F).distSqQ p (J r) + numeratorEnergy hw0 hw1 K extent hK i p := by
  have hm : L*(G).B r r ≤ (F).B (J r) (J r) :=
    Q'.le_trans' _ _ _ (normalizerMap_form_bounds hw0 hw1 K extent hK i.val i.property r).1
      (Q'.ge_of_eqv (probeMap_pair hw0 hw1 K extent hK i.val i.property r r))
  have hc : (F).B p (J r) ≈ (G).B r (N p) :=
    Q'.eqv_trans _ _ _ ((F).B_symm p (J r))
      (probeMap_test hw0 hw1 K extent hK i.val i.property r p)
  have hd : (F).distSqQ p (J r) ≈
      ((F).B p p + -((G).B r (N p))) + (-((G).B r (N p)) + (F).B (J r) (J r)) :=
    Q'.eqv_trans _ _ _ ((F).B_sub_diag_expand p (J r))
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hc))
        (Q'.add_eqv_congr' (Q'.neg_eqv_congr _ _ hc) (Q'.eqv_refl _)))
  exact Q'.le_trans' _ _ _
    (variational_bound G L ((F).B p p) ((F).B (J r) (J r))
      (Q'.le_of_lt (lowerFactor_positive hw0 hw1)) r (N p) hm)
    (Q'.ge_of_eqv (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ hd) (Q'.eqv_refl _)))

/-- This bound passes through the constructed conditional limit itself. -/
theorem conditional_residual_bound (p : (F).V) :
    RCle (rat (L*(F).B p p))
      (RCadd (RCscale L (normSq ((P).residual i (embedV F p))))
        (rat (numeratorEnergy hw0 hw1 K extent hK i p))) := by
  change RCle _ (RCadd (RCscale L ((F).cinnerCompl
    ((F).cSub (embedV F p)
      (conditionalProjection hw0 hw1 K extent hK i.val i.property (embedV F p)))
    ((F).cSub (embedV F p)
      (conditionalProjection hw0 hw1 K extent hK i.val i.property (embedV F p))))) _)
  rw [conditionalProjection_embed]
  apply leEv_ofQ'_of_approx_ge
  intro n
  exact probe_variational_bound hw0 hw1 K extent hK i p _

private theorem scaled_sub_cancel (c : Q') (a b : RC) :
    RCadd (RCscale c (RCsub a b)) (RCscale c b) = RCscale c a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))) (.mul (.var 0) (.var 2)))
      (.mul (.var 0) (.var 1)) (by decide)
      (fun | 0 => c | 1 => A.approx n | _ => B.approx n)))

private theorem cancel_left {a b c : RC} (h : RCle (RCadd a b) (RCadd a c)) : RCle b c := by
  have he (x y : RC) : RCadd (RCneg x) (RCadd x y) = y := by
    refine Quotient.inductionOn₂ x y ?_
    intro X Y
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.neg (.var 0)) (.add (.var 0) (.var 1))) (.var 1) (by decide)
        (fun | 0 => X.approx n | _ => Y.approx n)))
  have hh := RCadd_le_add (RCle_refl (RCneg a)) h
  rw [he, he] at hh
  exact hh

/-- Numerator-sensitive norm bound on the ACTUAL completed conditional output. -/
theorem conditional_norm_bound (p : (F).V) :
    RCle (RCscale L (normSq ((P).op i (embedV F p))))
      (rat (numeratorEnergy hw0 hw1 K extent hK i p)) := by
  have h := conditional_residual_bound hw0 hw1 K extent hK i p
  have hn : rat (L*(F).B p p) = RCscale L (normSq (embedV F p)) := by
    apply Quotient.sound
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  rw [hn, (P).single_loss] at h
  have hc := scaled_sub_cancel L (normSq (embedV F p)) (normSq ((P).op i (embedV F p)))
  rw [← hc] at h
  exact cancel_left h

/-- The centered numerator is the actual signed difference Np-D*A(p),
in the retained exterior form. No coefficient or pointwise equality is claimed. -/
theorem centered_numerator_energy (p : (F).V) :
    numeratorEnergy hw0 hw1 K extent hK i
      (freeResidual hw0 hw1 K extent hK i.val i.property p) ≈
    (G).distSqQ (N p) (M (freeAverage hw0 hw1 K extent hK i.val i.property p)) := by
  let a := freeAverage hw0 hw1 K extent hK i.val i.property p
  let f := freeResidual hw0 hw1 K extent hK i.val i.property p
  let b := (G).sub (N p) (M a)
  have hpair (r : (G).V) : (G).B r (N f) ≈ (G).B r b := by
    have hp := probeMap_test hw0 hw1 K extent hK i.val i.property r p
    have ha := probeMap_pair hw0 hw1 K extent hK i.val i.property r a
    have hexp : (F).B (J r) f ≈ (G).B r (N p) + -((G).B r (M a)) :=
      Q'.eqv_trans _ _ _ ((F).B_add_right (J r) p ((F).neg (J a)))
        (Q'.add_eqv_congr' hp
          (Q'.eqv_trans _ _ _ ((F).B_neg_right (J r) (J a)) (Q'.neg_eqv_congr _ _ ha)))
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (probeMap_test hw0 hw1 K extent hK i.val i.property r f))
      (Q'.eqv_trans _ _ _ hexp (Q'.eqv_symm
        (Q'.eqv_trans _ _ _ ((G).B_add_right r (N p) ((G).neg (M a)))
          (Q'.add_eqv_congr' (Q'.eqv_refl _) ((G).B_neg_right r (M a))))))
  have hrad : (G).rad (N f) b := by
    let d := (G).sub (N f) b
    exact Q'.eqv_trans _ _ _ ((G).B_add_right d (N f) ((G).neg b))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (hpair d) ((G).B_neg_right d b))
        (Q'.add_neg_self_eqv _))
  exact (G).B_welldef hrad hrad

/-- The numerator of the computed free residual keeps all signed cancellations.
No hypothesis that this explicit quantity is small is supplied or inferred. -/
theorem free_residual_variance_bound (p : (F).V) :
    let f := freeResidual hw0 hw1 K extent hK i.val i.property p
    RCle (rat (L*(F).B f f))
      (RCadd (RCscale L (normSq ((P).residual i (embedV F p))))
        (rat (numeratorEnergy hw0 hw1 K extent hK i f))) := by
  dsimp only
  have h := conditional_residual_bound hw0 hw1 K extent hK i
    (freeResidual hw0 hw1 K extent hK i.val i.property p)
  rw [residual_free_pin hw0 hw1 K extent hK i p] at h
  exact h

#print axioms numeratorEnergy
#print axioms numeratorEnergy_nonnegative
#print axioms probe_variational_bound
#print axioms conditional_residual_bound
#print axioms conditional_norm_bound
#print axioms centered_numerator_energy
#print axioms free_residual_variance_bound

end YMGap.Continuum.BF4ExactSlabStarNumeratorInfluence
