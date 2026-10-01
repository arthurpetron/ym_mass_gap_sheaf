/-
The original sector resolvent preserves the vacuum complement and has the
core-margin norm bound there. This remains at fixed nome and width in the
original lattice-time normalization; no physical OS identification is made.
-/

import YMGap.Continuum.BF4WilsonAllNomeSectorResolvent
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphGap

namespace YMGap.Continuum.BF4WilsonAllNomeSectorResolventGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphForm (graph_symmetric)
open YMGap.Continuum.BF4WilsonAllNomeLogCoreGap (coreMargin coreMargin_positive)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (DomainPoint graph domain_form_gap)
open YMGap.Continuum.BF4WilsonAllNomeSectorResolvent (state domainPoint inverse_right)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "Sector" => BF4WilsonAllNomeTimeSector.State hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "S" => completedSmul hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (X.approx n))))

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (X.approx n))))

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_neg_self_eqv (X.approx n)))

private theorem sub_nonnegative {a b : RC} (h : RCle b a) :
    RCnonneg (RCsub a b) := by
  have hh := RCadd_le_add h (RCle_refl (RCneg b))
  change RCle (RCsub b b) (RCsub a b) at hh
  rwa [rc_sub_self] at hh

private theorem vacuum_output_orthogonal
    (p : DomainPoint hw0 hw1 (width := width)) : B U p.output.val = RCzero := by
  have h := graph_symmetric hw0 hw1
    (graph hw0 hw1 p) (core hw0 hw1 U)
  rw [BF4WilsonAllNomeCompletedTime.completedUnit_fixed hw0 hw1 1,
    BF4WilsonAllNomeDerivativeCore.derivativeAction_unit_zero hw0 hw1,
    completedInner_zero_right] at h
  exact (completedInner_symm hw0 hw1 U p.output.val).trans h

/-- The constructed resolvent maps a vacuum-orthogonal sector input to a
vacuum-orthogonal sector output. -/
theorem state_orthogonal (lambda : Q') (hl : (0 : Q') < lambda)
    (x : Sector) (hx : B U x.val = RCzero) :
    B U (state hw0 hw1 lambda hl x).val = RCzero := by
  let p := domainPoint hw0 hw1 lambda hl x
  have ho : B U p.output.val = RCzero := vacuum_output_orthogonal hw0 hw1 p
  have hi := congrArg (B U) (inverse_right hw0 hw1 lambda hl x)
  change B U (completedAdd hw0 hw1 (S lambda p.input.val) p.output.val) =
    B U x.val at hi
  rw [completedInner_add_right, completedInner_smul_right, ho,
    rc_add_zero, hx] at hi
  have hs := congrArg (RCscale (Q'.recipPos lambda hl)) hi
  have hc : Q'.eqv (Q'.recipPos lambda hl * lambda) 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv lambda hl)
  rw [RCscale_RCscale, RCscale_RCzero, scale_congr hc, RCscale_one] at hs
  exact hs

/-- A square-completion estimate: coercivity of one pairing gives a sharp
inverse norm cap without dividing by the norm of the unknown vector. -/
theorem norm_from_coercivity (a : Q') (ha : (0 : Q') < a)
    (u x : V) (h : RCle (RCscale a (B u u)) (B u x)) :
    RCle (B u u)
      (RCscale (Q'.recipPos a ha * Q'.recipPos a ha) (B x x)) := by
  let E := B (Sub x (S a u)) (Sub x (S a u))
  let L := RCsub (B u x) (RCscale a (B u u))
  have hE : RCnonneg E := completedInner_nonnegative hw0 hw1 _
  have hL : RCnonneg L := sub_nonnegative h
  have hSL : RCnonneg (RCscale (2*a) L) := by
    simpa only [RCscale_RCzero] using
      (RCscale_mono (Q'.le_of_lt (Q'.mul_pos (by decide) ha)) hL)
  have hid : B x x = RCadd E
      (RCadd (RCscale (a*a) (B u u)) (RCscale (2*a) L)) := by
    dsimp [E, L]
    simp only [completedInner_sub_left, completedInner_sub_right,
      completedInner_smul_left, completedInner_smul_right]
    rw [completedInner_symm hw0 hw1 x u]
    refine Quotient.inductionOn₃ (B x x) (B u x) (B u u) ?_
    intro X Y Z
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.var 0)
        (.add
          (.add (.add (.var 0) (.neg (.mul (.var 3) (.var 1))))
            (.neg (.mul (.var 3)
              (.add (.var 1) (.neg (.mul (.var 3) (.var 2)))))))
          (.add (.mul (.mul (.var 3) (.var 3)) (.var 2))
            (.mul (.mul (.const 2) (.var 3))
              (.add (.var 1) (.neg (.mul (.var 3) (.var 2)))))))
        (by decide)
        (fun | 0 => X.approx n | 1 => Y.approx n | 2 => Z.approx n | _ => a)))
  have hbasic : RCle (RCscale (a*a) (B u u)) (B x x) := by
    rw [hid]
    have hh := RCadd_le_add hE
      (RCadd_le_add (RCle_refl (RCscale (a*a) (B u u))) hSL)
    rw [rc_zero_add, rc_add_zero] at hh
    exact hh
  have hr := RCscale_mono
    (Q'.mul_nonneg _ _ (Q'.le_of_lt (Q'.recipPos_pos a ha))
      (Q'.le_of_lt (Q'.recipPos_pos a ha))) hbasic
  rw [RCscale_RCscale] at hr
  have hc : Q'.eqv
      ((Q'.recipPos a ha * Q'.recipPos a ha) * (a*a)) 1 := by
    have hca : Q'.eqv (Q'.recipPos a ha * a) 1 :=
      Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv a ha)
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (by decide) (fun | 0 => Q'.recipPos a ha | _ => a))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hca)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hca)
          (Q'.one_mul_eqv 1)))
  rwa [scale_congr hc, RCscale_one] at hr

private theorem shifted_coercivity (lambda : Q') (hl : (0 : Q') < lambda)
    (x : Sector) (hx : B U x.val = RCzero) :
    RCle (RCscale (lambda + coreMargin hw0 hw1 width)
      (B (state hw0 hw1 lambda hl x).val (state hw0 hw1 lambda hl x).val))
      (B (state hw0 hw1 lambda hl x).val x.val) := by
  let p := domainPoint hw0 hw1 lambda hl x
  have hg := domain_form_gap hw0 hw1 p (state_orthogonal hw0 hw1 lambda hl x hx)
  have hi := congrArg (B p.input.val) (inverse_right hw0 hw1 lambda hl x)
  change B p.input.val
    (completedAdd hw0 hw1 (S lambda p.input.val) p.output.val) =
    B p.input.val x.val at hi
  rw [completedInner_add_right, completedInner_smul_right] at hi
  change RCle (RCscale (lambda + coreMargin hw0 hw1 width)
    (B p.input.val p.input.val)) (B p.input.val x.val)
  rw [← hi]
  have hid : RCscale (lambda + coreMargin hw0 hw1 width)
      (B p.input.val p.input.val) =
      RCadd (RCscale lambda (B p.input.val p.input.val))
        (RCscale (coreMargin hw0 hw1 width) (B p.input.val p.input.val)) := by
    refine Quotient.inductionOn (B p.input.val p.input.val) ?_
    intro X
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.add_mul_eqv lambda (coreMargin hw0 hw1 width) (X.approx n)))
  rw [hid]
  exact RCadd_le_add (RCle_refl _) hg

private theorem margin_coercivity (lambda : Q') (hl : (0 : Q') < lambda)
    (x : Sector) (hx : B U x.val = RCzero) :
    RCle (RCscale (coreMargin hw0 hw1 width)
      (B (state hw0 hw1 lambda hl x).val (state hw0 hw1 lambda hl x).val))
      (B (state hw0 hw1 lambda hl x).val x.val) := by
  have h := shifted_coercivity hw0 hw1 lambda hl x hx
  have hu := completedInner_nonnegative hw0 hw1 (state hw0 hw1 lambda hl x).val
  have hLambda : RCnonneg (RCscale lambda
      (B (state hw0 hw1 lambda hl x).val (state hw0 hw1 lambda hl x).val)) := by
    simpa only [RCscale_RCzero] using (RCscale_mono (Q'.le_of_lt hl) hu)
  have hh := RCadd_le_add hLambda (RCle_refl
    (RCscale (coreMargin hw0 hw1 width)
      (B (state hw0 hw1 lambda hl x).val (state hw0 hw1 lambda hl x).val)))
  rw [rc_zero_add] at hh
  have hsum : RCscale (lambda + coreMargin hw0 hw1 width)
      (B (state hw0 hw1 lambda hl x).val (state hw0 hw1 lambda hl x).val) =
      RCadd (RCscale lambda
        (B (state hw0 hw1 lambda hl x).val (state hw0 hw1 lambda hl x).val))
        (RCscale (coreMargin hw0 hw1 width)
          (B (state hw0 hw1 lambda hl x).val (state hw0 hw1 lambda hl x).val)) := by
    refine Quotient.inductionOn
      (B (state hw0 hw1 lambda hl x).val (state hw0 hw1 lambda hl x).val) ?_
    intro X
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.add_mul_eqv lambda (coreMargin hw0 hw1 width) (X.approx n)))
  exact RCle_trans hh (hsum ▸ h)

/-- The sharp vacuum-complement resolvent norm cap at a positive parameter. -/
theorem norm_bound (lambda : Q') (hl : (0 : Q') < lambda)
    (x : Sector) (hx : B U x.val = RCzero) :
    RCle (B (state hw0 hw1 lambda hl x).val (state hw0 hw1 lambda hl x).val)
      (RCscale
        (Q'.recipPos (lambda + coreMargin hw0 hw1 width)
          (Q'.add_pos hl (coreMargin_positive hw0 hw1)) *
         Q'.recipPos (lambda + coreMargin hw0 hw1 width)
          (Q'.add_pos hl (coreMargin_positive hw0 hw1)))
        (B x.val x.val)) :=
  norm_from_coercivity hw0 hw1 _
    (Q'.add_pos hl (coreMargin_positive hw0 hw1)) _ _
    (shifted_coercivity hw0 hw1 lambda hl x hx)

/-- A lambda-independent ceiling, suitable for a constructive zero-shift
limit. This is still only the fixed-nome original sector. -/
theorem uniform_norm_bound (lambda : Q') (hl : (0 : Q') < lambda)
    (x : Sector) (hx : B U x.val = RCzero) :
    RCle (B (state hw0 hw1 lambda hl x).val (state hw0 hw1 lambda hl x).val)
      (RCscale
        (Q'.recipPos (coreMargin hw0 hw1 width) (coreMargin_positive hw0 hw1) *
         Q'.recipPos (coreMargin hw0 hw1 width) (coreMargin_positive hw0 hw1))
        (B x.val x.val)) :=
  norm_from_coercivity hw0 hw1 _ (coreMargin_positive hw0 hw1) _ _
    (margin_coercivity hw0 hw1 lambda hl x hx)

#print axioms state_orthogonal
#print axioms norm_from_coercivity
#print axioms norm_bound
#print axioms uniform_norm_bound

end YMGap.Continuum.BF4WilsonAllNomeSectorResolventGap
