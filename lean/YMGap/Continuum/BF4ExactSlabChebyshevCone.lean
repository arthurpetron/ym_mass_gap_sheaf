/-
# Degree-by-degree cone of the original balanced-sweep Chebyshev state

The first component of the actual coupled recurrence at degree n depends on
at most 16*n original Ward-star expansions.  This is finite propagation of
the same completed full-action operator, without a strict centered gap.
-/

import YMGap.Continuum.BF4ExactSlabBalancedCone
import YMGap.Continuum.BF4ExactSlabSweepChebyshev

namespace YMGap.Continuum.BF4ExactSlabChebyshevCone

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSDenseCompletionLaws
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFullActionScalar
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabBalancedCone
open YMGap.Continuum.BF4ExactSlabSweepChebyshev
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- Composition of the deduplicated Ward-star support growth. -/
theorem grow_add (extent m n : Nat) (support : List Z4Link) :
    grow extent (m+n) support = grow extent n (grow extent m support) := by
  induction m generalizing support with
  | zero => simp only [Nat.zero_add, grow]
  | succ m ih =>
    calc
      grow extent ((m+1)+n) support =
          grow extent (m+n) (expand extent support) := by
            have hm : (m+1)+n = (m+n)+1 := by omega
            rw [hm, grow]
      _ = grow extent n (grow extent m (expand extent support)) :=
        ih (expand extent support)
      _ = grow extent n (grow extent (m+1) support) := rfl

/-- Every earlier star cone embeds in a later one. -/
theorem grow_mono_steps (extent m n : Nat) (support : List Z4Link)
    (hm : m ≤ n) (i : Z4Link) (hi : i ∈ grow extent m support) :
    i ∈ grow extent n support := by
  have h : m + (n-m) = n := by omega
  rw [← h, grow_add]
  exact mem_grow extent (n-m) (grow extent m support) i hi

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "S" => fullScalarData hw0 hw1 K extent hK

/-- Conditional support is monotone in its declared link list. -/
theorem localized_widen (small large : List Z4Link)
    (x : GNSCompletionSpace F)
    (hsub : ∀ i, i ∈ small → i ∈ large)
    (hx : Localized hw0 hw1 K extent hK small x) :
    Localized hw0 hw1 K extent hK large x := by
  intro i hi
  exact hx i (fun h => hi (hsub i.val h))

theorem localized_add (support : List Z4Link) (x y : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x)
    (hy : Localized hw0 hw1 K extent hK support y) :
    Localized hw0 hw1 K extent hK support ((F).cAdd x y) := by
  intro i hi
  rw [GNSChebyshevRecurrence.X_add ((P).op i) ((P).adjoint i) x y,
    hx i hi, hy i hi]

theorem localized_sub (support : List Z4Link) (x y : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x)
    (hy : Localized hw0 hw1 K extent hK support y) :
    Localized hw0 hw1 K extent hK support ((F).cSub x y) := by
  intro i hi
  rw [(P).op_sub i x y, hx i hi, hy i hi]

/-- Rational completed scaling preserves exact conditional support. -/
theorem localized_smul (support : List Z4Link) (c : Q')
    (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    Localized hw0 hw1 K extent hK support ((S).cSmul c x) := by
  intro i hi
  apply eq_of_pairings_equal
  intro z
  calc
    (F).cinnerCompl ((P).op i ((S).cSmul c x)) z =
        (F).cinnerCompl ((S).cSmul c x) ((P).op i z) :=
      (P).adjoint i _ _
    _ = RCscale c ((F).cinnerCompl x ((P).op i z)) :=
      (S).cinnerCompl_cSmul_left c x _
    _ = RCscale c ((F).cinnerCompl ((P).op i x) z) := by
      rw [(P).adjoint i x z]
    _ = RCscale c ((F).cinnerCompl x z) := by rw [hx i hi]
    _ = (F).cinnerCompl ((S).cSmul c x) z :=
      ((S).cinnerCompl_cSmul_left c x z).symm

/-- The actual affine balanced operator enlarges a localized state by no
more than one sixteen-star balanced cycle. -/
theorem affine_localized (c : Q') (support : List Z4Link)
    (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    Localized hw0 hw1 K extent hK (grow extent 16 support)
      (affine hw0 hw1 K extent hK c x) := by
  unfold affine
  apply localized_sub hw0 hw1 K extent hK
  · exact localized_smul hw0 hw1 K extent hK _ c _
      (balanced_localized hw0 hw1 K extent hK support x hx)
  · exact localized_widen hw0 hw1 K extent hK support
      (grow extent 16 support) x
      (fun i hi => mem_grow extent 16 support i hi) hx

/-- The first component of the LITERAL coupled Chebyshev state has radius
16*n, proportional to polynomial degree rather than to two recurrence steps. -/
theorem coupled_first_localized (c : Q') (n : Nat)
    (support : List Z4Link) (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    Localized hw0 hw1 K extent hK (grow extent (16*n) support)
      (coupled hw0 hw1 K extent hK c x n).1 := by
  have hpair : ∀ m : Nat,
      Localized hw0 hw1 K extent hK (grow extent (16*m) support)
        (coupled hw0 hw1 K extent hK c x m).1 ∧
      Localized hw0 hw1 K extent hK (grow extent (16*(m+1)) support)
        (coupled hw0 hw1 K extent hK c x (m+1)).1 := by
    intro m
    induction m with
    | zero =>
      constructor
      · change Localized hw0 hw1 K extent hK support x
        exact hx
      · have hfirst : (coupled hw0 hw1 K extent hK c x 1).1 =
            affine hw0 hw1 K extent hK c x :=
          GNSChebyshevRecurrence.first_one _
            (affine_selfAdjoint hw0 hw1 K extent hK c) x
        rw [hfirst]
        exact affine_localized hw0 hw1 K extent hK c support x hx
    | succ m ih =>
      constructor
      · exact ih.2
      · have hA0 := affine_localized hw0 hw1 K extent hK c
          (grow extent (16*(m+1)) support)
          (coupled hw0 hw1 K extent hK c x (m+1)).1 ih.2
        have hA : Localized hw0 hw1 K extent hK
            (grow extent (16*(m+2)) support)
            (affine hw0 hw1 K extent hK c
              (coupled hw0 hw1 K extent hK c x (m+1)).1) := by
          have ha : 16*(m+2) = 16*(m+1)+16 := by omega
          rw [ha, grow_add]
          exact hA0
        have hP : Localized hw0 hw1 K extent hK
            (grow extent (16*(m+2)) support)
            (coupled hw0 hw1 K extent hK c x m).1 :=
          localized_widen hw0 hw1 K extent hK _ _ _
            (fun i hi => grow_mono_steps extent (16*m) (16*(m+2)) support
              (by omega) i hi) ih.1
        have hAA := localized_add hw0 hw1 K extent hK _ _ _ hA hA
        rw [coupled_first_recurrence hw0 hw1 K extent hK c x m]
        exact localized_sub hw0 hw1 K extent hK _ _ _ hAA hP
  exact (hpair n).1

#print axioms grow_add
#print axioms grow_mono_steps
#print axioms localized_widen
#print axioms localized_add
#print axioms localized_sub
#print axioms localized_smul
#print axioms affine_localized
#print axioms coupled_first_localized

end YMGap.Continuum.BF4ExactSlabChebyshevCone
