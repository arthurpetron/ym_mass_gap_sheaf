/-
# Algebraic energy descent for the finite residual generator

All estimates concern the SAME completed GNS form and the explicitly formed
finite generator. The square-energy lower bound is an argument, not assumed
of any Yang--Mills instance here. No spectral theorem or inverse is used.
-/

import YMGap.Continuum.GNSResidualGeneratorStep
import YMGap.Continuum.RCSignedPairBudget
import YMGap.Continuum.ContinuousTransferCalculus

namespace YMGap.Continuum.GNSResidualGeneratorDescent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.GNSResidualGeneratorStep
open YMGap.Continuum.RingNormaliser

variable {Index : Type} (S : SmulGNSData)
  (P : Family S.toGNSData Index) (tests : List Index)

local notation "D" => S.toGNSData

private theorem add_neg_zero (a : RC) : RCadd a (RCneg a) = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem neg_zero : RCneg RCzero = RCzero := by
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => (by decide : Q'.eqv (-(0:Q')) 0)))

private theorem add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n))))

private theorem sub_nonneg_of_le {a b : RC} (h : RCle a b) : RCnonneg (RCsub b a) := by
  have hs := RCadd_le_add (RCle_refl b) (RCSignedPairBudget.neg_mono h)
  rw [add_neg_zero] at hs
  exact hs

private theorem sub_le_self (a b : RC) (hb : RCnonneg b) : RCle (RCsub a b) a := by
  have hs := RCadd_le_add (RCle_refl a) (RCSignedPairBudget.neg_mono hb)
  rw [neg_zero, add_zero] at hs
  exact hs

private theorem sub_antitone_right (a : RC) {b c : RC} (h : RCle b c) :
    RCle (RCsub a c) (RCsub a b) :=
  RCadd_le_add (RCle_refl a) (RCSignedPairBudget.neg_mono h)

private theorem one_sub_scale (s gamma : Q') (a : RC) :
    RCsub a (RCscale (s*gamma) a) = RCscale (1+-(s*gamma)) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 2) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2))))
      (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 1)))) (.var 2))
      (by decide) (fun | 0 => s | 1 => gamma | _ => A.approx n)))

private theorem norm_drop_scalar (s : Q') (a e : RC) :
    RCsub a (RCsub (RCsub a (RCscale s e)) (RCscale s e)) =
      RCscale (2*s) e := by
  refine Quotient.inductionOn₂ a e ?_
  intro A E
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg
        (.add (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))
          (.neg (.mul (.var 1) (.var 2))))))
      (.mul (.mul (.const 2) (.var 1)) (.var 2))
      (by decide) (fun | 0 => A.approx n | 1 => s | _ => E.approx n)))

/-- Under the explicit stable step size, the positive cubic correction in
the exact energy identity is absorbed by the second negative square. -/
theorem energy_step_le (s : Q') (hs : (0 : Q') ≤ s)
    (hstep : s * Q'.ofNat tests.length ≤ (1 : Q'))
    (x : GNSCompletionSpace D) :
    RCle (energy S P tests (gradientStep S P tests s x))
      (RCsub (energy S P tests x)
        (RCscale s (normSq (generator S P tests x)))) := by
  let H := generator S P tests
  let A := normSq (H x)
  let B := energy S P tests (H x)
  have hb : RCle B (RCscale (Q'.ofNat tests.length) A) :=
    energy_le_norm S P tests (H x)
  have hsb : RCle (RCscale s B) A := by
    have h1 := RCscale_mono hs hb
    rw [RCscale_RCscale] at h1
    have h2 := RCscale_scalar_mono hstep ((D).cinner_self_nonneg (H x))
    rw [RCscale_one] at h2
    exact RCle_trans h1 h2
  have hrem : RCnonneg (RCsub A (RCscale s B)) := sub_nonneg_of_le hsb
  have hscaled : RCnonneg (RCscale s (RCsub A (RCscale s B))) := by
    change RCle RCzero (RCscale s (RCsub A (RCscale s B)))
    rw [← RCscale_RCzero s]
    exact RCscale_mono hs hrem
  rw [gradientStep_energy]
  exact sub_le_self _ _ hscaled

/-- A supplied square-energy inequality gives a literal geometric
one-step reduction of the generator's own Dirichlet form. -/
theorem energy_contract (s gamma : Q') (hs : (0 : Q') ≤ s)
    (hstep : s * Q'.ofNat tests.length ≤ (1 : Q'))
    (_hgamma : (0 : Q') ≤ gamma)
    (hsq : ∀ y : GNSCompletionSpace D,
      RCle (RCscale gamma (energy S P tests y))
        (normSq (generator S P tests y)))
    (x : GNSCompletionSpace D) :
    RCle (energy S P tests (gradientStep S P tests s x))
      (RCscale (1+-(s*gamma)) (energy S P tests x)) := by
  have h1 := energy_step_le S P tests s hs hstep x
  have h2 := RCscale_mono hs (hsq x)
  rw [RCscale_RCscale] at h2
  have h3 := sub_antitone_right (energy S P tests x) h2
  rw [one_sub_scale] at h3
  exact RCle_trans h1 h3

/-- The norm lost in one step costs at most twice step size times the
original energy; no sign of a mixed residual was discarded. -/
theorem norm_loss_le (s : Q') (hs : (0 : Q') ≤ s)
    (x : GNSCompletionSpace D) :
    RCle (RCsub (normSq x) (normSq (gradientStep S P tests s x)))
      (RCscale (2*s) (energy S P tests x)) := by
  let H := generator S P tests
  let E := energy S P tests x
  let A := normSq (H x)
  have hA : RCnonneg (RCscale s A) := by
    change RCle RCzero (RCscale s A)
    rw [← RCscale_RCzero s]
    exact RCscale_mono hs ((D).cinner_self_nonneg (H x))
  have hinner : RCle (RCsub E (RCscale s A)) E := sub_le_self E _ hA
  have hscaled := RCscale_mono hs hinner
  have hnorm : RCle
      (RCsub (RCsub (normSq x) (RCscale s E)) (RCscale s E))
      (normSq (gradientStep S P tests s x)) := by
    rw [gradientStep_norm]
    exact sub_antitone_right _ hscaled
  have h := sub_antitone_right (normSq x) hnorm
  rw [norm_drop_scalar] at h
  exact h

private theorem sub_sub_cancel (a b : RC) : RCsub a (RCsub a b) = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 0) (.neg (.var 1)))))
      (.var 1) (by decide)
      (fun | 0 => A.approx n | _ => B.approx n)))

private theorem half_double_coefficient (s gamma : Q') :
    Q'.eqv ((HalfPow.half * gamma) * (2*s)) (s*gamma) := by
  have hr : Q'.eqv ((HalfPow.half * gamma) * (2*s))
      ((HalfPow.half * 2) * (s*gamma)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 2) (.var 0)) (.mul (.const 2) (.var 1)))
      (.mul (.mul (.var 2) (.const 2)) (.mul (.var 1) (.var 0)))
      (by decide) (fun | 0 => gamma | 1 => s | _ => HalfPow.half)
  exact Q'.eqv_trans _ _ _ hr (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.eqv (HalfPow.half * 2) 1))
    (Q'.one_mul_eqv _))

/-- The exact one-step telescoping budget: half the supplied square-energy
coefficient pays for every decrement of completed squared norm. -/
theorem step_telescope (s gamma : Q') (hs : (0 : Q') ≤ s)
    (hstep : s * Q'.ofNat tests.length ≤ (1 : Q'))
    (hgamma : (0 : Q') ≤ gamma)
    (hsq : ∀ y : GNSCompletionSpace D,
      RCle (RCscale gamma (energy S P tests y))
        (normSq (generator S P tests y)))
    (x : GNSCompletionSpace D) :
    RCle
      (RCscale (HalfPow.half*gamma)
        (RCsub (normSq x) (normSq (gradientStep S P tests s x))))
      (RCsub (energy S P tests x)
        (energy S P tests (gradientStep S P tests s x))) := by
  let E := energy S P tests x
  let A := normSq (generator S P tests x)
  have hh : (0 : Q') ≤ HalfPow.half*gamma :=
    Q'.mul_nonneg _ _ HalfPow.half_nonneg hgamma
  have hn := RCscale_mono hh (norm_loss_le S P tests s hs x)
  rw [RCscale_RCscale,
    RCSignedPairBudget.scale_congr (half_double_coefficient s gamma) E] at hn
  have hsquare := RCscale_mono hs (hsq x)
  rw [RCscale_RCscale] at hsquare
  have he := sub_antitone_right E (energy_step_le S P tests s hs hstep x)
  rw [sub_sub_cancel E (RCscale s A)] at he
  exact RCle_trans hn (RCle_trans hsquare he)

#print axioms energy_step_le
#print axioms energy_contract
#print axioms norm_loss_le
#print axioms step_telescope

end YMGap.Continuum.GNSResidualGeneratorDescent
