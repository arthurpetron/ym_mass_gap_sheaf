/-
# Balanced original-action sweep has a sixteen-layer cone

The adjoint reverses the order of all physical-link projections.  Within
each color, those projections commute, so reversing their internal order
does not change the completed operator.  Hence the genuine S* S is exactly
the forward eight layers followed by the reverse eight layers.  This gives
finite propagation, not a strict gap or scaling-uniform decay.
-/

import YMGap.Continuum.BF4ExactSlabEightLayerCone
import YMGap.Continuum.GNSProjectionSweepAdjoint

namespace YMGap.Continuum.BF4ExactSlabBalancedCone

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabWardStarGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4LinkEightColor

private theorem sweep_reverse_commuting {D : GNSData} {Index : Type}
    (P : Family D Index) (schedule : List Index)
    (hcomm : ∀ i, i ∈ schedule → ∀ j, j ∈ schedule → ∀ x,
      P.op i (P.op j x) = P.op j (P.op i x))
    (x : GNSCompletionSpace D) :
    P.sweep schedule.reverse x = P.sweep schedule x := by
  induction schedule generalizing x with
  | nil => rfl
  | cons i rest ih =>
    rw [List.reverse_cons, P.sweep_append]
    change P.op i (P.sweep rest.reverse x) = P.sweep rest (P.op i x)
    rw [ih (fun j hj k hk y =>
      hcomm j (List.mem_cons_of_mem i hj) k (List.mem_cons_of_mem i hk) y) x]
    exact P.op_sweep i rest
      (fun j hj y => hcomm i List.mem_cons_self j
        (List.mem_cons_of_mem i hj) y) x

private theorem reverse_flatMap {α β : Type} (cs : List α) (f : α → List β) :
    (cs.flatMap f).reverse = cs.reverse.flatMap (fun c => (f c).reverse) := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    rw [List.flatMap_cons, List.reverse_append, List.reverse_cons,
      List.flatMap_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK

private theorem layer_reverse_sweep (c : Color) (x : GNSCompletionSpace F) :
    (P).sweep (layer extent c).reverse x = (P).sweep (layer extent c) x := by
  apply sweep_reverse_commuting (P) (layer extent c)
  intro i hi j hj y
  exact layer_commute hw0 hw1 K extent hK c i j hi hj y

private theorem reverse_layers_sweep (cs : List Color) (x : GNSCompletionSpace F) :
    (P).sweep (cs.flatMap (fun c => (layer extent c).reverse)) x =
      (P).sweep (cs.flatMap (layer extent)) x := by
  induction cs generalizing x with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.flatMap_cons]
    rw [(P).sweep_append, (P).sweep_append,
      layer_reverse_sweep hw0 hw1 K extent hK c x,
      ih]

/-- Reversing the actual schedule reverses color order; within each color
the conditional projections commute. This also pins the reverse-loss word. -/
theorem schedule_reverse_sweep (x : GNSCompletionSpace F) :
    (P).sweep (schedule extent).reverse x =
      runLayers hw0 hw1 K extent hK colors.reverse x := by
  unfold schedule runLayers
  rw [reverse_flatMap]
  exact reverse_layers_sweep hw0 hw1 K extent hK colors.reverse x

/-- Literal S* S, on the original full-action completion, is exactly the
forward eight physical color layers followed by their reverse order. -/
theorem balanced_runLayers (x : GNSCompletionSpace F) :
    (P).balanced (schedule extent) x =
      runLayers hw0 hw1 K extent hK (colors ++ colors.reverse) x := by
  unfold Family.balanced runLayers
  rw [schedule_reverse_sweep hw0 hw1 K extent hK,
    List.flatMap_append, (P).sweep_append]
  rfl

/-- One true balanced operator has at most sixteen original Ward-star
expansions, independently of the physical slab volume. -/
theorem balanced_localized (support : List Z4Link) (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    Localized hw0 hw1 K extent hK (grow extent 16 support)
      ((P).balanced (schedule extent) x) := by
  rw [balanced_runLayers hw0 hw1 K extent hK x]
  have h := runLayers_localized hw0 hw1 K extent hK
    (colors ++ colors.reverse) support x hx
  have hl : (colors ++ colors.reverse).length = 16 := by
    rw [List.length_append, colors_length, List.length_reverse, colors_length]
  rwa [hl] at h

/-- Until the sixteen-star cone reaches a separated test, the SAME
interacting pairing is unchanged by the genuine balanced operator. -/
theorem balanced_cone_pairing (support testSupport : List Z4Link)
    (x y : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x)
    (hy : Localized hw0 hw1 K extent hK testSupport y)
    (hsep : LinksDisjoint (grow extent 16 support) testSupport) :
    (F).cinnerCompl ((P).balanced (schedule extent) x) y =
      (F).cinnerCompl x y := by
  rw [balanced_runLayers hw0 hw1 K extent hK x]
  apply runLayers_pairing hw0 hw1 K extent hK
    (colors ++ colors.reverse) support testSupport x y hx hy
  have hl : (colors ++ colors.reverse).length = 16 := by
    rw [List.length_append, colors_length, List.length_reverse, colors_length]
  rwa [hl]

/-- A computed schedule of n genuine balanced cycles. -/
def balancedCycles : Nat → List Color
  | 0 => []
  | n+1 => (colors ++ colors.reverse) ++ balancedCycles n

theorem balancedCycles_length (n : Nat) : (balancedCycles n).length = 16*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [balancedCycles, List.length_append, List.length_append,
      colors_length, List.length_reverse, colors_length, ih]
    omega

/-- These are iterates of the SAME completed balanced operator, not a
separate local approximation sequence. -/
theorem balancedCycles_succ (n : Nat) (x : GNSCompletionSpace F) :
    runLayers hw0 hw1 K extent hK (balancedCycles (n+1)) x =
      runLayers hw0 hw1 K extent hK (balancedCycles n)
        ((P).balanced (schedule extent) x) := by
  unfold runLayers
  rw [balancedCycles, List.flatMap_append, (P).sweep_append]
  exact congrArg ((P).sweep ((balancedCycles n).flatMap (layer extent)))
    (balanced_runLayers hw0 hw1 K extent hK x).symm

theorem balancedCycles_localized (n : Nat) (support : List Z4Link)
    (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    Localized hw0 hw1 K extent hK (grow extent (16*n) support)
      (runLayers hw0 hw1 K extent hK (balancedCycles n) x) := by
  have h := runLayers_localized hw0 hw1 K extent hK
    (balancedCycles n) support x hx
  rwa [balancedCycles_length] at h

theorem balancedCycles_pairing (n : Nat) (support testSupport : List Z4Link)
    (x y : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x)
    (hy : Localized hw0 hw1 K extent hK testSupport y)
    (hsep : LinksDisjoint (grow extent (16*n) support) testSupport) :
    (F).cinnerCompl
        (runLayers hw0 hw1 K extent hK (balancedCycles n) x) y =
      (F).cinnerCompl x y := by
  apply runLayers_pairing hw0 hw1 K extent hK
    (balancedCycles n) support testSupport x y hx hy
  rwa [balancedCycles_length]

#print axioms schedule_reverse_sweep
#print axioms balanced_runLayers
#print axioms balanced_localized
#print axioms balanced_cone_pairing
#print axioms balancedCycles_length
#print axioms balancedCycles_succ
#print axioms balancedCycles_localized
#print axioms balancedCycles_pairing

end YMGap.Continuum.BF4ExactSlabBalancedCone
