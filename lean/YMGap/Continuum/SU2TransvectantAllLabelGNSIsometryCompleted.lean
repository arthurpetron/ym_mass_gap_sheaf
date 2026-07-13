/-
# Arbitrary-label local transvectant isometries on GNS completions

The all-label diagonal formula supplies a canonical nonnegative GNS line for
every trilinear binary-form map.  This file proves that a bounded trilinear-map
identity automatically identifies those Gram weights.  Consequently every
certified local recoupling identity -- at arbitrary labels -- descends to an
isometry of the constructive GNS completions without a separately assumed
normalization equation.

For a local F move the source can be `triLeft a b c d e`; the target map `R`
may be any exact rational linear combination of right-associated channels.
The only input is the actual coefficient identity

  TriMapEqv a b c d (triLeft a b c d e) R.

The metric compatibility and completion descent are theorems derived here.
This does not construct the general F coefficients; it removes the independent
all-label metric/descent obstruction once such a coefficient certificate is
available.
-/

import YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
import YMGap.Continuum.SU2TransvectantMixedPentagonGNSCompleted

namespace YMGap.Continuum.SU2TransvectantAllLabelGNSIsometryCompleted

set_option maxHeartbeats 1600000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2TransvectantMixedPentagonGNSCompleted

local infix:50 " ≈ " => Q'.eqv

/-! ## The invariant weight respects exact trilinear-map equality -/

private theorem coefficient_square_congr {x y : Q'} (h : x ≈ y) :
    x * x ≈ y * y := by
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right x y x h)
    (Q'.mul_eqv_congr_left y x y h)

/-- Uniform metric compatibility.  Pointwise equality of two trilinear maps on
the complete monomial window implies equality of their fully normalized
invariant diagonal weights. -/
theorem triMapInner_diagonal_congr_all_labels
    (a b c d : Nat)
    (L R : BForm → BForm → BForm → BForm)
    (h : TriMapEqv a b c d L R) :
    triMapInner a b c d L L ≈ triMapInner a b c d R R := by
  unfold triMapInner
  refine finSum_eqv_congr_lt _ _ (a + 1) (fun i hi => ?_)
  refine finSum_eqv_congr_lt _ _ (b + 1) (fun j hj => ?_)
  refine finSum_eqv_congr_lt _ _ (c + 1) (fun k hk => ?_)
  refine finSum_eqv_congr_lt _ _ (d + 1) (fun s hs => ?_)
  have hcoeff := h i hi j hj k hk s hs
  exact Q'.mul_eqv_congr_left
    (tvBinomQ a i * tvBinomQ b j * tvBinomQ c k *
      symMonomialNormSq d s)
    (L (mono i) (mono j) (mono k) s * L (mono i) (mono j) (mono k) s)
    (R (mono i) (mono j) (mono k) s * R (mono i) (mono j) (mono k) s)
    (coefficient_square_congr hcoeff)

/-! ## Canonical arbitrary-label channel GNS lines -/

/-- The canonical weighted GNS line of an arbitrary trilinear map, using its
derived invariant Hilbert--Schmidt weight. -/
abbrev triMapChannelGNS (a b c d : Nat)
    (L : BForm → BForm → BForm → BForm) : GNSData :=
  qWeightGNS (triMapInner a b c d L L)
    (triMapInner_diagonal_nonneg_all a b c d L)

private def qWeightEqvDenseIsometry
    (u v : Q') (hu : (0 : Q') ≤ u) (hv : (0 : Q') ≤ v)
    (h : u ≈ v) :
    DenseGNSIsometry (qWeightGNS u hu) (qWeightGNS v hv) where
  map := fun x => x
  map_veq := fun hab => hab
  map_sub := fun x y => Q'.eqv_refl _
  norm := by
    intro x
    change Q' at x
    unfold qWeightGNS
    change v * (x * x) ≈ u * (x * x)
    exact Q'.mul_eqv_congr_right v u (x * x) (Q'.eqv_symm h)

/-- A trilinear-map identity induces a dense GNS isometry.  No weight equation
is supplied by the caller: it is derived from the all-label Gram formula. -/
def equivalentTriMapDenseIsometry
    (a b c d : Nat)
    (L R : BForm → BForm → BForm → BForm)
    (h : TriMapEqv a b c d L R) :
    DenseGNSIsometry (triMapChannelGNS a b c d L)
      (triMapChannelGNS a b c d R) :=
  qWeightEqvDenseIsometry
    (triMapInner a b c d L L) (triMapInner a b c d R R)
    (triMapInner_diagonal_nonneg_all a b c d L)
    (triMapInner_diagonal_nonneg_all a b c d R)
    (triMapInner_diagonal_congr_all_labels a b c d L R h)

/-- The arbitrary-label dense isometry descended through Cauchy completion. -/
def completedEquivalentTriMapIsometry
    (a b c d : Nat)
    (L R : BForm → BForm → BForm → BForm)
    (h : TriMapEqv a b c d L R) :
    GNSCompletionSpace (triMapChannelGNS a b c d L) →
      GNSCompletionSpace (triMapChannelGNS a b c d R) :=
  (equivalentTriMapDenseIsometry a b c d L R h).completed

theorem completedEquivalentTriMapIsometry_norm
    (a b c d : Nat)
    (L R : BForm → BForm → BForm → BForm)
    (h : TriMapEqv a b c d L R)
    (x : GNSCompletionSpace (triMapChannelGNS a b c d L)) :
    (triMapChannelGNS a b c d R).cinnerCompl
        (completedEquivalentTriMapIsometry a b c d L R h x)
        (completedEquivalentTriMapIsometry a b c d L R h x) =
      (triMapChannelGNS a b c d L).cinnerCompl x x :=
  (equivalentTriMapDenseIsometry a b c d L R h).completed_norm x

/-! ## One arbitrary-label local F-move step -/

/-- A certified arbitrary-label local recoupling of one left-associated
channel to an exact right-associated linear combination, descended to the GNS
completions. -/
def completedAllLabelLocalFMove
    (a b c d e : Nat)
    (R : BForm → BForm → BForm → BForm)
    (h : TriMapEqv a b c d (triLeft a b c d e) R) :
    GNSCompletionSpace
        (triMapChannelGNS a b c d (triLeft a b c d e)) →
      GNSCompletionSpace (triMapChannelGNS a b c d R) :=
  completedEquivalentTriMapIsometry a b c d (triLeft a b c d e) R h

/-- The local F-move step preserves the derived invariant norm for every label
tuple and every exact rational recoupling certificate. -/
theorem completedAllLabelLocalFMove_norm
    (a b c d e : Nat)
    (R : BForm → BForm → BForm → BForm)
    (h : TriMapEqv a b c d (triLeft a b c d e) R)
    (x : GNSCompletionSpace
      (triMapChannelGNS a b c d (triLeft a b c d e))) :
    (triMapChannelGNS a b c d R).cinnerCompl
        (completedAllLabelLocalFMove a b c d e R h x)
        (completedAllLabelLocalFMove a b c d e R h x) =
      (triMapChannelGNS a b c d (triLeft a b c d e)).cinnerCompl x x :=
  completedEquivalentTriMapIsometry_norm a b c d
    (triLeft a b c d e) R h x

end YMGap.Continuum.SU2TransvectantAllLabelGNSIsometryCompleted

#print axioms YMGap.Continuum.SU2TransvectantAllLabelGNSIsometryCompleted.triMapInner_diagonal_congr_all_labels
#print axioms YMGap.Continuum.SU2TransvectantAllLabelGNSIsometryCompleted.triMapChannelGNS
#print axioms YMGap.Continuum.SU2TransvectantAllLabelGNSIsometryCompleted.equivalentTriMapDenseIsometry
#print axioms YMGap.Continuum.SU2TransvectantAllLabelGNSIsometryCompleted.completedEquivalentTriMapIsometry
#print axioms YMGap.Continuum.SU2TransvectantAllLabelGNSIsometryCompleted.completedEquivalentTriMapIsometry_norm
#print axioms YMGap.Continuum.SU2TransvectantAllLabelGNSIsometryCompleted.completedAllLabelLocalFMove
#print axioms YMGap.Continuum.SU2TransvectantAllLabelGNSIsometryCompleted.completedAllLabelLocalFMove_norm
