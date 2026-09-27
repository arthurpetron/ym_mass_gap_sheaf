/-
# The original conditional residual as a finite-test variational limit

The polynomial reciprocal iteration supplies explicit kernel tests whose
dual values approach the squared norm of the actual completed conditional
residual.  This is a fixed-parameter approximation statement, not an
interacting Poincare or scaling-uniform estimate.
-/

import YMGap.Continuum.BF4ExactSlabStarResidualApproximation
import YMGap.Continuum.BF4ExactSlabStarOptimizedPolynomialTest

namespace YMGap.Continuum.BF4ExactSlabStarVariationalApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabStarPolynomialResidual
open YMGap.Continuum.BF4ExactSlabStarResidualApproximation
open YMGap.Continuum.RingNormaliser

private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

private theorem rc_sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (Q'.eqv_of_eq (Q'.add_zero' (A.approx n)))))

private theorem embed_pair (D : GNSData) (a b : D.V) :
    D.cinnerCompl (embedV D a) (embedV D b) = rat (D.B a b) :=
  D.cinnerCompl_embed a b

private theorem dualValue_embed (D : GNSData) (f t : D.V) :
    rat ((D.B f t + D.B f t) + -(D.B t t)) =
      RCsub (RCadd (D.cinnerCompl (embedV D f) (embedV D t))
        (D.cinnerCompl (embedV D f) (embedV D t)))
        (D.cinnerCompl (embedV D t) (embedV D t)) := by
  rw [embed_pair, embed_pair]
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

private theorem dual_sub_identity (a b c : RC) :
    RCsub (RCsub a b) (RCsub b c) =
      RCsub a (RCsub (RCadd b b) c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1)))
        (.neg (.add (.var 1) (.neg (.var 2)))))
      (.add (.var 0) (.neg (.add (.add (.var 1) (.var 1)) (.neg (.var 2)))))
      (by decide) (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

private theorem add_sub_cancel (a b : RC) : RCadd b (RCsub a b) = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 1) (.add (.var 0) (.neg (.var 1)))) (.var 0)
      (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (i : PhysicalLink extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "t" => polynomialResidual hw0 hw1 K extent hK i

/-- Pythagoras for the actual conditional-kernel polynomial, retaining
the exact signed rational dual value. -/
theorem residual_dual_error_identity (seed p : (F).V) :
    normSq ((F).cSub ((P).residual i (embedV F p)) (embedV F (t seed))) =
      RCsub (normSq ((P).residual i (embedV F p)))
        (rat (dualValue hw0 hw1 K extent hK i seed p)) := by
  let x := embedV F p
  let y := embedV F (t seed)
  let v := (P).residual i x
  have ht := polynomialResidual_projection_zero hw0 hw1 K extent hK i seed
  have hv : (F).cinnerCompl v y = (F).cinnerCompl x y := by
    change (F).cinnerCompl ((F).cSub x ((P).op i x)) y = _
    rw [(F).cinnerCompl_cSub_left, (P).adjoint i x y, ht,
      (F).cinnerCompl_embedZero_right, rc_sub_zero]
  have hexp : normSq ((F).cSub v y) =
      RCsub (RCsub (normSq v) ((F).cinnerCompl v y))
        (RCsub ((F).cinnerCompl v y) (normSq y)) := by
    unfold normSq
    rw [(F).cinnerCompl_cSub_left,
      (F).cinnerCompl_comm v ((F).cSub v y),
      (F).cinnerCompl_cSub_left,
      (F).cinnerCompl_comm y ((F).cSub v y),
      (F).cinnerCompl_cSub_left,
      (F).cinnerCompl_comm y v]
  rw [hexp, hv, dual_sub_identity]
  change _ = RCsub (normSq v) (rat (dualValue hw0 hw1 K extent hK i seed p))
  rw [dualValue]
  exact congrArg (RCsub (normSq v))
    (dualValue_embed F p (t seed)).symm

/-- An explicitly computable seed and iteration cutoff give an arbitrarily
close lower approximation to the SAME original completed residual energy. -/
theorem residual_dual_approximation (p : (F).V) (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (n : Nat)
    (hn : residualCutoff hw0 hw1 K extent hK p epsilon ≤ n) :
    RCle (normSq ((P).residual i (embedV F p)))
      (RCadd (rat (dualValue hw0 hw1 K extent hK i
        (approximationSeed hw0 hw1 K extent hK i p n) p)) (rat epsilon)) := by
  let seed := approximationSeed hw0 hw1 K extent hK i p n
  have he := residual_dual_error_identity hw0 hw1 K extent hK i seed p
  have hb := residual_approximation_error_le hw0 hw1 K extent hK i p epsilon hepsilon n hn
  rw [he] at hb
  have hs := RCadd_le_add (RCle_refl
    (rat (dualValue hw0 hw1 K extent hK i seed p))) hb
  rwa [add_sub_cancel] at hs

/-- A computed rational lower value at the returned iteration count. The
test seed and its index remain data; no supremum or witness choice is used. -/
def approximationValue (p : (F).V) (epsilon : Q') : Q' :=
  dualValue hw0 hw1 K extent hK i
    (approximationSeed hw0 hw1 K extent hK i p
      (residualCutoff hw0 hw1 K extent hK p epsilon)) p

/-- The actual original local residual energy lies in the explicitly
computed rational interval of requested width epsilon. -/
theorem residual_energy_bracket (p : (F).V) (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) :
    RCle (rat (approximationValue hw0 hw1 K extent hK i p epsilon))
      (normSq ((P).residual i (embedV F p))) ∧
    RCle (normSq ((P).residual i (embedV F p)))
      (RCadd (rat (approximationValue hw0 hw1 K extent hK i p epsilon))
        (rat epsilon)) :=
  ⟨dualValue_lower hw0 hw1 K extent hK i _ p,
    residual_dual_approximation hw0 hw1 K extent hK i p epsilon hepsilon _ (Nat.le_refl _)⟩

/-- Finite value at the index selected only by nome and relative tolerance. -/
def relativeValue (p : (F).V) (epsilon : Q') : Q' :=
  dualValue hw0 hw1 K extent hK i
    (approximationSeed hw0 hw1 K extent hK i p
      (BF4ExactSlabStarResidualApproximation.relativeCutoff w epsilon)) p

/-- The interval width is epsilon times the SAME original squared norm.
The iteration count is volume/cutoff/link-independent at fixed nome; this
is not a lower coercivity constant for the interacting global form. -/
theorem residual_relative_bracket (p : (F).V) (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) :
    RCle (rat (relativeValue hw0 hw1 K extent hK i p epsilon))
      (normSq ((P).residual i (embedV F p))) ∧
    RCle (normSq ((P).residual i (embedV F p)))
      (RCadd (rat (relativeValue hw0 hw1 K extent hK i p epsilon))
        (rat (epsilon * (F).B p p))) := by
  refine ⟨dualValue_lower hw0 hw1 K extent hK i _ p, ?_⟩
  let seed := approximationSeed hw0 hw1 K extent hK i p
    (BF4ExactSlabStarResidualApproximation.relativeCutoff w epsilon)
  have he := residual_dual_error_identity hw0 hw1 K extent hK i seed p
  have hb := residual_relative_error_le hw0 hw1 K extent hK i p epsilon hepsilon _ (Nat.le_refl _)
  rw [he] at hb
  have hs := RCadd_le_add (RCle_refl
    (rat (dualValue hw0 hw1 K extent hK i seed p))) hb
  rwa [add_sub_cancel] at hs

#print axioms residual_dual_error_identity
#print axioms residual_dual_approximation
#print axioms approximationValue
#print axioms residual_energy_bracket
#print axioms relativeValue
#print axioms residual_relative_bracket

end YMGap.Continuum.BF4ExactSlabStarVariationalApproximation
