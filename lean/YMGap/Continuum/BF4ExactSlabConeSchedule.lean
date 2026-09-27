/-
# Literal pruned words for original-action color-layer cones

The cone computation is the original family of conditional projections
applied to an explicit finite list of physical links. Equality of its
output and loss with the full word requires operational localization.
No strict contraction or analytic lower estimate is asserted.
-/

import YMGap.Continuum.BF4ExactSlabBalancedCone

namespace YMGap.Continuum.BF4ExactSlabConeSchedule

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabBalancedCone
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4LinkEightColor

/-- The literal list of physical links retained by successive cone layers.
The support is expanded once after each color, just as in `coneLayers`. -/
def coneSchedule (extent : Nat) : List Color → List Z4Link →
    List (PhysicalLink extent)
  | [], _ => []
  | c :: rest, support =>
      activeLayer extent c support ++ coneSchedule extent rest (expand extent support)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK

/-- The cone is exactly one sweep of the displayed original physical-link
word, with no localization hypothesis or replacement operator. -/
theorem coneLayers_eq_sweep (cs : List Color) (support : List Z4Link)
    (x : GNSCompletionSpace F) :
    coneLayers hw0 hw1 K extent hK cs support x =
      (P).sweep (coneSchedule extent cs support) x := by
  induction cs generalizing support x with
  | nil => rfl
  | cons c rest ih =>
      change coneLayers hw0 hw1 K extent hK rest (expand extent support)
          ((P).sweep (activeLayer extent c support) x) =
        (P).sweep
          (activeLayer extent c support ++
            coneSchedule extent rest (expand extent support)) x
      rw [(P).sweep_append]
      exact ih (expand extent support) ((P).sweep (activeLayer extent c support) x)

/-- A localized input has exactly the same completed output under the full
color word and its explicitly pruned physical-link word. -/
theorem runLayers_eq_coneSchedule (cs : List Color) (support : List Z4Link)
    (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    runLayers hw0 hw1 K extent hK cs x =
      (P).sweep (coneSchedule extent cs support) x := by
  rw [runLayers_eq_cone hw0 hw1 K extent hK cs support x hx,
    coneLayers_eq_sweep hw0 hw1 K extent hK]

/-- Pruning changes neither the original-action input nor its final norm,
so it changes neither total Pythagorean loss. Summands remain attached to
the actual intermediate states of their respective displayed words. -/
theorem runLayers_loss_eq_coneSchedule (cs : List Color)
    (support : List Z4Link) (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    (P).loss (cs.flatMap (layer extent)) x =
      (P).loss (coneSchedule extent cs support) x := by
  calc
    (P).loss (cs.flatMap (layer extent)) x =
        RCsub (normSq x) (normSq (runLayers hw0 hw1 K extent hK cs x)) :=
      (P).loss_eq _ x
    _ = RCsub (normSq x)
        (normSq ((P).sweep (coneSchedule extent cs support) x)) :=
      congrArg (fun y => RCsub (normSq x) (normSq y))
        (runLayers_eq_coneSchedule hw0 hw1 K extent hK cs support x hx)
    _ = (P).loss (coneSchedule extent cs support) x :=
      ((P).loss_eq _ x).symm

/-- The genuine forward eight-color sweep has the explicit cone word. -/
theorem forward_eq_coneSchedule (support : List Z4Link)
    (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    (P).sweep (schedule extent) x =
      (P).sweep (coneSchedule extent colors support) x := by
  exact runLayers_eq_coneSchedule hw0 hw1 K extent hK colors support x hx

/-- The genuine adjoint sweep is the reversed color-layer sweep, then the
same exact cone pruning applies. The within-color reversal is already
handled by `schedule_reverse_sweep`. -/
theorem reverse_eq_coneSchedule (support : List Z4Link)
    (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    (P).sweep (schedule extent).reverse x =
      (P).sweep (coneSchedule extent colors.reverse support) x := by
  rw [schedule_reverse_sweep hw0 hw1 K extent hK]
  exact runLayers_eq_coneSchedule hw0 hw1 K extent hK colors.reverse support x hx

/-- Total reverse-sweep loss is exactly the loss on the explicit pruned
word, evaluated in the same completed full action. -/
theorem reverse_loss_eq_coneSchedule (support : List Z4Link)
    (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    (P).loss (schedule extent).reverse x =
      (P).loss (coneSchedule extent colors.reverse support) x := by
  calc
    (P).loss (schedule extent).reverse x =
        RCsub (normSq x) (normSq ((P).sweep (schedule extent).reverse x)) :=
      (P).loss_eq _ x
    _ = RCsub (normSq x)
        (normSq ((P).sweep (coneSchedule extent colors.reverse support) x)) :=
      congrArg (fun y => RCsub (normSq x) (normSq y))
        (reverse_eq_coneSchedule hw0 hw1 K extent hK support x hx)
    _ = (P).loss (coneSchedule extent colors.reverse support) x :=
      ((P).loss_eq _ x).symm

#print axioms coneSchedule
#print axioms coneLayers_eq_sweep
#print axioms runLayers_eq_coneSchedule
#print axioms runLayers_loss_eq_coneSchedule
#print axioms forward_eq_coneSchedule
#print axioms reverse_eq_coneSchedule
#print axioms reverse_loss_eq_coneSchedule

end YMGap.Continuum.BF4ExactSlabConeSchedule
