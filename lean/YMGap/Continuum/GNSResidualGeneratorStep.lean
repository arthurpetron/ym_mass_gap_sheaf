/-
# Finite residual-generator gradient step on one completed GNS carrier

Only algebra of completed orthogonal projections is used here.  No gap,
mixing, spectral theorem, or finite-volume model is assumed.
-/

import YMGap.Continuum.GNSProjectionSignedEnergy
import YMGap.Continuum.GNSFiniteSumEnergy
import YMGap.Continuum.ContinuousFunctionalCalculusForm

namespace YMGap.Continuum.GNSResidualGeneratorStep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSDenseCompletionLaws
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.GNSFiniteSumEnergy
open YMGap.Continuum.HamiltonianScalar

variable {Index : Type} (S : SmulGNSData)
  (P : Family S.toGNSData Index) (tests : List Index)

local notation "D" => S.toGNSData

/-- Sum of actual completed projection residuals, with list multiplicity. -/
def generator (x : GNSCompletionSpace D) : GNSCompletionSpace D :=
  P.residualSum tests x

/-- The quadratic form of that same generator. -/
def energy (x : GNSCompletionSpace D) : RC := P.finalEnergy tests x

/-- A finite rational gradient step, never an inverse or spectral map. -/
def gradientStep (s : Q') (x : GNSCompletionSpace D) : GNSCompletionSpace D :=
  (D).cSub x (S.cSmul s (generator S P tests x))

theorem generator_adjoint (x y : GNSCompletionSpace D) :
    (D).cinnerCompl (generator S P tests x) y =
      (D).cinnerCompl x (generator S P tests y) :=
  P.residualSum_adjoint tests x y

theorem generator_energy (x : GNSCompletionSpace D) :
    (D).cinnerCompl (generator S P tests x) x = energy S P tests x :=
  P.residualSum_self_pairing tests x

theorem energy_nonnegative (x : GNSCompletionSpace D) :
    RCnonneg (energy S P tests x) := by
  unfold energy Family.finalEnergy
  exact sumOn_nonnegative tests _ (fun i _ => (D).cinner_self_nonneg _)

private theorem energy_map (x : GNSCompletionSpace D) :
    GNSFiniteSumEnergy.energy (tests.map (fun i => P.residual i x)) =
      energy S P tests x := by
  induction tests with
  | nil => rfl
  | cons i rest ih =>
      change RCadd (normSq (P.residual i x))
        (GNSFiniteSumEnergy.energy (rest.map (fun j => P.residual j x))) =
        RCadd (normSq (P.residual i x)) (P.finalEnergy rest x)
      exact congrArg (RCadd (normSq (P.residual i x))) ih

/-- The completed Gram bound with the actual list length. -/
theorem generator_norm_le_energy (x : GNSCompletionSpace D) :
    RCle (normSq (generator S P tests x))
      (RCscale (Q'.ofNat tests.length) (energy S P tests x)) := by
  have h := GNSFiniteSumEnergy.norm_vectorSum_le
    (tests.map (fun i => P.residual i x))
  simpa only [generator, Family.residualSum, List.length_map,
    energy_map S P tests x] using h

private theorem scale_succ (n : Nat) (a : RC) :
    RCscale (Q'.ofNat (n+1)) a = RCadd a (RCscale (Q'.ofNat n) a) := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun k =>
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv n 1))
      (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv _))
          (Q'.add_comm_eqv _ _)))))

private theorem sumOn_const (a : RC) :
    sumOn tests (fun _ => a) = RCscale (Q'.ofNat tests.length) a := by
  induction tests with
  | nil =>
      show RCzero = RCscale (Q'.ofNat 0) a
      refine Quotient.inductionOn a ?_
      intro A
      exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
        (fun _ => Q'.eqv_symm (Q'.zero_mul_eqv _)))
  | cons i rest ih =>
      change RCadd a (sumOn rest (fun _ => a)) =
        RCscale (Q'.ofNat (rest.length+1)) a
      rw [ih]
      exact (scale_succ rest.length a).symm

/-- Every residual contracts; summing yields the elementary length bound. -/
theorem energy_le_norm (x : GNSCompletionSpace D) :
    RCle (energy S P tests x)
      (RCscale (Q'.ofNat tests.length) (normSq x)) := by
  have h := sumOn_mono tests (fun i => normSq (P.residual i x))
    (fun _ => normSq x) (fun i _ => P.residual_norm i x)
  rw [sumOn_const tests (normSq x)] at h
  exact h

/-- Additive compatibility follows from the proved adjoint and completed
nondegeneracy; no extra vector-linearity field is postulated. -/
theorem generator_sub (x y : GNSCompletionSpace D) :
    generator S P tests ((D).cSub x y) =
      (D).cSub (generator S P tests x) (generator S P tests y) := by
  apply eq_of_pairings_equal
  intro z
  rw [generator_adjoint, (D).cinnerCompl_cSub_left,
    (D).cinnerCompl_cSub_left, generator_adjoint, generator_adjoint]

/-- Rational homogeneity of the same completed generator. -/
theorem generator_scale (c : Q') (x : GNSCompletionSpace D) :
    generator S P tests (S.cSmul c x) =
      S.cSmul c (generator S P tests x) := by
  apply eq_of_pairings_equal
  intro z
  rw [generator_adjoint, S.cinnerCompl_cSmul_left,
    S.cinnerCompl_cSmul_left, generator_adjoint]

theorem gradientStep_pair (s : Q') (x y : GNSCompletionSpace D) :
    (D).cinnerCompl (gradientStep S P tests s x) y =
      RCsub ((D).cinnerCompl x y)
        (RCscale s ((D).cinnerCompl (generator S P tests x) y)) := by
  unfold gradientStep
  rw [(D).cinnerCompl_cSub_left, S.cinnerCompl_cSmul_left]

/-- Exact square of a finite generator step; both mixed terms remain. -/
theorem gradientStep_norm (s : Q') (x : GNSCompletionSpace D) :
    normSq (gradientStep S P tests s x) =
      RCsub
        (RCsub (normSq x) (RCscale s (energy S P tests x)))
        (RCscale s (RCsub (energy S P tests x)
          (RCscale s (normSq (generator S P tests x))))) := by
  let H := generator S P tests
  let T := gradientStep S P tests s x
  have hleft : (D).cinnerCompl x T =
      RCsub (normSq x) (RCscale s (energy S P tests x)) := by
    rw [(D).cinnerCompl_comm x T, gradientStep_pair, generator_energy]
    rfl
  have hright : (D).cinnerCompl (H x) T =
      RCsub (energy S P tests x) (RCscale s (normSq (H x))) := by
    rw [(D).cinnerCompl_comm (H x) T, gradientStep_pair,
      (D).cinnerCompl_comm x (H x), generator_energy]
    rfl
  change (D).cinnerCompl T T = _
  rw [gradientStep_pair, hleft, hright]

/-- Exact Dirichlet energy after one step. The cubic-looking last term is
the SAME generator energy evaluated on Hx, not a surrogate form. -/
theorem gradientStep_energy (s : Q') (x : GNSCompletionSpace D) :
    energy S P tests (gradientStep S P tests s x) =
      RCsub
        (RCsub (energy S P tests x)
          (RCscale s (normSq (generator S P tests x))))
        (RCscale s (RCsub (normSq (generator S P tests x))
          (RCscale s (energy S P tests (generator S P tests x))))) := by
  let H := generator S P tests
  let T := gradientStep S P tests s x
  have hh : generator S P tests T =
      (D).cSub (H x) (S.cSmul s (H (H x))) := by
    dsimp only [T, H, gradientStep]
    rw [generator_sub, generator_scale]
  have hleft : (D).cinnerCompl (H x) T =
      RCsub (energy S P tests x) (RCscale s (normSq (H x))) := by
    rw [(D).cinnerCompl_comm (H x) T, gradientStep_pair,
      (D).cinnerCompl_comm x (H x), generator_energy]
    rfl
  have hright : (D).cinnerCompl (H (H x)) T =
      RCsub (normSq (H x)) (RCscale s (energy S P tests (H x))) := by
    have h1 : (D).cinnerCompl x (H (H x)) = normSq (H x) := by
      exact (generator_adjoint S P tests x (H x)).symm
    have h2 : (D).cinnerCompl (H x) (H (H x)) = energy S P tests (H x) := by
      rw [(D).cinnerCompl_comm (H x) (H (H x)), generator_energy]
    rw [(D).cinnerCompl_comm (H (H x)) T, gradientStep_pair, h1, h2]
  rw [← generator_energy S P tests T, hh,
    (D).cinnerCompl_cSub_left, S.cinnerCompl_cSmul_left,
    hleft, hright]

#print axioms generator
#print axioms energy
#print axioms gradientStep
#print axioms generator_adjoint
#print axioms generator_energy
#print axioms energy_nonnegative
#print axioms generator_norm_le_energy
#print axioms energy_le_norm
#print axioms generator_sub
#print axioms generator_scale
#print axioms gradientStep_pair
#print axioms gradientStep_norm
#print axioms gradientStep_energy

end YMGap.Continuum.GNSResidualGeneratorStep
