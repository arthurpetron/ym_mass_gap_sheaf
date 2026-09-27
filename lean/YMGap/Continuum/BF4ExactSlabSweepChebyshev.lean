/-
# Coupled polynomial states of the original balanced conditional sweep

The map c*S* S-I is constructed on the existing full-action completion,
using its actual rational scalar action. Arbitrary completed states
orthogonal to the original constant stay centered under both sweep orders
and the coupled recurrence. No strict centered contraction or accelerated decay
rate is supplied here; in particular no contraction of the vacuum is used.
-/

import YMGap.Continuum.BF4ExactSlabFullActionScalar
import YMGap.Continuum.BF4ExactSlabEightLayerCone
import YMGap.Continuum.GNSProjectionSweepAdjoint
import YMGap.Continuum.GNSChebyshevRecurrence
import YMGap.Continuum.ContinuousFunctionalCalculusForm
import YMGap.Continuum.RCScaleClose

namespace YMGap.Continuum.BF4ExactSlabSweepChebyshev

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFullActionScalar
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.QuaternionHaarSquareCertificate

private theorem zero_add : RCadd RCzero RCzero = RCzero :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => show Q'.eqv (0+0) 0 from by decide))

private theorem zero_sub : RCsub RCzero RCzero = RCzero :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => show Q'.eqv (0 + -0) 0 from by decide))

private theorem scale_zero (c : Q') : RCscale c RCzero = RCzero :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_zero_eqv c))

private theorem double_norm_scalar (a b c : RC) :
    RCsub (RCsub (RCscale 2 (RCscale 2 a)) (RCscale 2 b))
      (RCsub (RCscale 2 b) c) = RCsub (RCadd c (RCscale 4 a)) (RCscale 4 b) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.mul (.const 2) (.mul (.const 2) (.var 0)))
        (.neg (.mul (.const 2) (.var 1))))
        (.neg (.add (.mul (.const 2) (.var 1)) (.neg (.var 2)))))
      (.add (.add (.var 2) (.mul (.const 4) (.var 0)))
        (.neg (.mul (.const 4) (.var 1)))) (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

private theorem doubled_sub_norm (S : SmulGNSData)
    (b x : GNSCompletionSpace S.toGNSData) :
    normSq (S.toGNSData.cSub (S.cSmul 2 b) x) =
      RCsub (RCadd (normSq x) (RCscale 4 (normSq b)))
        (RCscale 4 (S.toGNSData.cinnerCompl b x)) := by
  let D := S.toGNSData
  have he (u v : GNSCompletionSpace D) : normSq (D.cSub u v) =
      RCsub (RCsub (normSq u) (D.cinnerCompl u v))
        (RCsub (D.cinnerCompl u v) (normSq v)) := by
    unfold normSq
    rw [D.cinnerCompl_cSub_left, D.cinnerCompl_comm u (D.cSub u v),
      D.cinnerCompl_cSub_left, D.cinnerCompl_comm v (D.cSub u v),
      D.cinnerCompl_cSub_left, D.cinnerCompl_comm v u]
  rw [he]
  unfold normSq
  rw [S.cinnerCompl_cSmul_left, S.cinnerCompl_cSmul_right,
    S.cinnerCompl_cSmul_left]
  exact double_norm_scalar _ _ _

private theorem subtract_four_bound (a b c : RC) (h : RCle a b) :
    RCle (RCsub (RCadd c (RCscale 4 a)) (RCscale 4 b)) c := by
  have hh := RCadd_le_add
    (RCadd_le_add (RCle_refl c) (RCscale_mono (by decide : (0 : Q') ≤ 4) h))
    (RCle_refl (RCneg (RCscale 4 b)))
  have he (u v : RC) : RCsub (RCadd u v) v = u := by
    refine Quotient.inductionOn₂ u v ?_
    intro U V
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0)
        (by decide) (fun | 0 => U.approx n | _ => V.approx n)))
  change RCle _ (RCsub (RCadd c (RCscale 4 b)) (RCscale 4 b)) at hh
  rwa [he] at hh

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "S" => fullScalarData hw0 hw1 K extent hK

/-- The unscaled original constant, not a newly normalized vacuum. -/
def constant : (F).V := ⟨polyOne, supported_one _⟩

local notation "O" => embedV F (constant hw0 hw1 K extent hK)

/-- Orthogonality in the actual full form, for arbitrary COMPLETED states. -/
def Centered (x : GNSCompletionSpace F) : Prop := (F).cinnerCompl x O = RCzero

theorem constant_fixed (i : PhysicalLink extent) : (P).op i O = O :=
  localized_embed hw0 hw1 K extent hK [] (constant hw0 hw1 K extent hK)
    (BlockLocal.one _ _) i List.not_mem_nil

/-- Both orders, repetitions and arbitrary completed centered inputs are covered. -/
theorem sweep_centered (links : List (PhysicalLink extent)) (x : GNSCompletionSpace F)
    (hx : Centered hw0 hw1 K extent hK x) :
    Centered hw0 hw1 K extent hK ((P).sweep links x) := by
  unfold Centered at *
  rw [(P).sweep_pair_fixed links x O
    (fun i _ => constant_fixed hw0 hw1 K extent hK i), hx]

/-- Actual affine rescaling of S* S; c is rational data, not an assumed gap. -/
def affine (c : Q') (x : GNSCompletionSpace F) : GNSCompletionSpace F :=
  (F).cSub ((S).cSmul c ((P).balanced (schedule extent) x)) x

private theorem scalar_pair (c : Q') (x y : GNSCompletionSpace F) :
    (F).cinnerCompl ((S).cSmul c x) y = RCscale c ((F).cinnerCompl x y) :=
  (S).cinnerCompl_cSmul_left c x y

theorem affine_pairing (c : Q') (x y : GNSCompletionSpace F) :
    (F).cinnerCompl (affine hw0 hw1 K extent hK c x) y =
      RCsub (RCscale c ((F).cinnerCompl ((P).sweep (schedule extent) x)
        ((P).sweep (schedule extent) y))) ((F).cinnerCompl x y) := by
  unfold affine
  rw [(F).cinnerCompl_cSub_left, scalar_pair,
    (P).balanced_pairing]

theorem affine_selfAdjoint (c : Q') (x y : GNSCompletionSpace F) :
    (F).cinnerCompl (affine hw0 hw1 K extent hK c x) y =
      (F).cinnerCompl x (affine hw0 hw1 K extent hK c y) := by
  rw [affine_pairing, (F).cinnerCompl_comm x (affine hw0 hw1 K extent hK c y),
    affine_pairing, (F).cinnerCompl_comm ((P).sweep (schedule extent) y),
    (F).cinnerCompl_comm y x]

theorem affine_centered (c : Q') (x : GNSCompletionSpace F)
    (hx : Centered hw0 hw1 K extent hK x) :
    Centered hw0 hw1 K extent hK (affine hw0 hw1 K extent hK c x) := by
  have hb := sweep_centered hw0 hw1 K extent hK (schedule extent).reverse _
    (sweep_centered hw0 hw1 K extent hK (schedule extent) x hx)
  change (F).cinnerCompl ((P).balanced (schedule extent) x) O = RCzero at hb
  change (F).cinnerCompl x O = RCzero at hx
  unfold Centered affine
  rw [(F).cinnerCompl_cSub_left, scalar_pair, hb, hx,
    scale_zero, zero_sub]

/-- The unaccelerated interval map 2*S* S-I contracts on the ENTIRE actual
completion. This is a non-strict bound; it supplies no gap or decay rate. -/
theorem affine_two_norm (x : GNSCompletionSpace F) :
    RCle (normSq (affine hw0 hw1 K extent hK 2 x)) (normSq x) := by
  have hb := (P).sweep_norm (schedule extent).reverse ((P).sweep (schedule extent) x)
  have he := doubled_sub_norm (S) ((P).balanced (schedule extent) x) x
  change normSq (affine hw0 hw1 K extent hK 2 x) =
    RCsub (RCadd (normSq x) (RCscale 4 (normSq ((P).balanced (schedule extent) x))))
      (RCscale 4 ((F).cinnerCompl ((P).balanced (schedule extent) x) x)) at he
  rw [(P).balanced_pairing] at he
  rw [he]
  exact subtract_four_bound _ _ _ hb

def coupled (c : Q') (x : GNSCompletionSpace F) (n : Nat) :
    GNSCompletionSpace F × GNSCompletionSpace F :=
  GNSChebyshevEnergy.state (affine hw0 hw1 K extent hK c) x n

theorem coupled_energy (c : Q') (x : GNSCompletionSpace F) (n : Nat) :
    GNSChebyshevEnergy.energy (affine hw0 hw1 K extent hK c)
      (coupled hw0 hw1 K extent hK c x n).1 (coupled hw0 hw1 K extent hK c x n).2 =
      normSq x :=
  GNSChebyshevEnergy.state_energy _ (affine_selfAdjoint hw0 hw1 K extent hK c) x n

theorem coupled_centered (c : Q') (x : GNSCompletionSpace F)
    (hx : Centered hw0 hw1 K extent hK x) (n : Nat) :
    Centered hw0 hw1 K extent hK (coupled hw0 hw1 K extent hK c x n).1 ∧
    Centered hw0 hw1 K extent hK (coupled hw0 hw1 K extent hK c x n).2 := by
  apply GNSChebyshevEnergy.state_mem _ (Centered hw0 hw1 K extent hK)
    ?_ ?_ ?_ (affine_centered hw0 hw1 K extent hK c) x hx n
  · exact (F).cinnerCompl_embedZero_left O
  · intro a b ha hb
    unfold Centered at *
    rw [(F).cinnerCompl_cAdd_left, ha, hb, zero_add]
  · intro a b ha hb
    unfold Centered at *
    rw [(F).cinnerCompl_cSub_left, ha, hb, zero_sub]

/-- Actual same-carrier polynomial stability at every order, with no gap
input. The interval has not been shrunk and there is no exponential decay. -/
theorem coupled_two_norm (x : GNSCompletionSpace F) (n : Nat) :
    RCle (normSq (coupled hw0 hw1 K extent hK 2 x n).1) (normSq x) :=
  GNSChebyshevEnergy.state_norm_le _ (affine_selfAdjoint hw0 hw1 K extent hK 2) x n
    (affine_two_norm hw0 hw1 K extent hK _)

theorem coupled_first_recurrence (c : Q') (x : GNSCompletionSpace F) (n : Nat) :
    (coupled hw0 hw1 K extent hK c x (n+2)).1 =
      (F).cSub ((F).cAdd
        (affine hw0 hw1 K extent hK c (coupled hw0 hw1 K extent hK c x (n+1)).1)
        (affine hw0 hw1 K extent hK c (coupled hw0 hw1 K extent hK c x (n+1)).1))
        (coupled hw0 hw1 K extent hK c x n).1 :=
  GNSChebyshevRecurrence.first_succ_succ _ (affine_selfAdjoint hw0 hw1 K extent hK c) x n

#print axioms constant_fixed
#print axioms sweep_centered
#print axioms affine
#print axioms affine_pairing
#print axioms affine_selfAdjoint
#print axioms affine_centered
#print axioms affine_two_norm
#print axioms coupled
#print axioms coupled_energy
#print axioms coupled_centered
#print axioms coupled_two_norm
#print axioms coupled_first_recurrence

end YMGap.Continuum.BF4ExactSlabSweepChebyshev
