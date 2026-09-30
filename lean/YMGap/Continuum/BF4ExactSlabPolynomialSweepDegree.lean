/-
# Input-independent degree bounds for the original polynomial prediction sweep

Use the PURE polynomial N_p/D approximants, not p minus an approximate
residual. A selected coordinate is erased exactly. Later updates can
reintroduce it only through their fixed collar/normalizer polynomials.
After the physical schedule covers all links, every block degree is bounded
by computed data independent of the input polynomial and its degree.

This supplies the range bound needed by an all-input finite certificate.
It does not itself provide the sweep approximation error, a finite matrix
gap certificate, cutoff-uniform degree, spatial scaling or physical OS gap.
The original action, coordinates and inverse iterates are unchanged.
-/

import YMGap.Continuum.SU2QuaternionBlockDegreeBound
import YMGap.Continuum.BF4ExactSlabBlockConditionalApproximation
import YMGap.Continuum.BF4ExactSlabPhysicalScheduleIndex

namespace YMGap.Continuum.BF4ExactSlabPolynomialSweepDegree

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockInverseApproximation
open YMGap.Continuum.BF4ExactSlabBlockConditionalApproximation
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabPhysicalScheduleIndex
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockDegreeBound
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK

section Block

variable (links : List Z4Link)
local notation "G" => backgroundData hw0 hw1 K extent hK links

/-- Each inverse iteration adds at most one copy of the ACTUAL normalizer degree. -/
theorem approximateInverse_degree (block d : Nat) (r : (G).V)
    (hr : DegreeLE block d r.val) : ∀ n : Nat,
    DegreeLE block (d + n * degreeBound block (normalizer w K extent links))
      (approximateInverse hw0 hw1 K extent hK links r n).val := by
  intro n
  induction n with
  | zero =>
      exact ((DegreeLE.one block 0).smul 0).mono (Nat.zero_le _)
  | succ n ih =>
      let c := degreeBound block (normalizer w K extent links)
      have ha : DegreeLE block (d+(n+1)*c)
          (approximateInverse hw0 hw1 K extent hK links r n).val :=
        ih.mono (by simp only [c, Nat.add_mul, Nat.one_mul]; omega)
      have hm : DegreeLE block (d+(n+1)*c)
          (polyMul (approximateInverse hw0 hw1 K extent hK links r n).val
            (normalizer w K extent links)) :=
        (ih.mul (bound_spec block (normalizer w K extent links))).mono
          (by simp only [c, Nat.add_mul, Nat.one_mul]; omega)
      exact ha.add (((hr.mono (by omega)).add (hm.smul (-1))).smul _)

/-- The computed per-step cost depends on the original action and iteration,
not the input polynomial. No claim of efficient evaluation is made. -/
def updateDegreeCost (block n : Nat) : Nat :=
  degreeBound block (collarHeat w K extent links) +
    n * degreeBound block (normalizer w K extent links)

/-- Degree growth of a pure original conditional approximant in any coordinate. -/
theorem conditionalApproximation_degree (block d n : Nat) (p : (F).V)
    (hp : DegreeLE block d p.val) :
    DegreeLE block (d + updateDegreeCost (w := w) K extent links block n)
      (conditionalApproximation hw0 hw1 K extent hK links p.val p.property n).val := by
  have hr : DegreeLE block (d+degreeBound block (collarHeat w K extent links))
      (insertedNormalizer w K extent links p.val) :=
    familyProject_degree (slots extent links) block _ _
      (hp.mul (bound_spec block (collarHeat w K extent links)))
  have h := approximateInverse_degree hw0 hw1 K extent hK links block _
    (numeratorVector hw0 hw1 K extent hK links p.val p.property) hr n
  exact h.mono (by simp only [updateDegreeCost]; omega)

end Block

/-- A pure prediction polynomial on the SAME full-action supported carrier. -/
def polynomialUpdate (i : PhysicalLink extent) (n : Nat) (p : (F).V) : (F).V :=
  conditionalApproximation hw0 hw1 K extent hK [i.val] p.val p.property n

/-- Exact erasure, unlike the approximate residual's multiplicative input term. -/
theorem polynomialUpdate_selected_degree_zero (i : PhysicalLink extent)
    (n : Nat) (p : (F).V) :
    DegreeLE ((boundaryCompleteSlabLinks extent).idxOf i.val) 0
      (polynomialUpdate hw0 hw1 K extent hK i n p).val := by
  apply DegreeLE.of_independent
  exact conditionalApproximation_independent hw0 hw1 K extent hK [i.val]
    p.val p.property n _ (List.mem_cons_self)

/-- The list head acts first, exactly as in the existing conditional sweep. -/
def polynomialSweep (n : Nat) : List (PhysicalLink extent) → (F).V → (F).V
  | [], p => p
  | i::rest, p => polynomialSweep n rest (polynomialUpdate hw0 hw1 K extent hK i n p)

/-- A finite sum of original-action costs; no input degree occurs. -/
def sweepDegreeBudget (w : Q') (K extent block n : Nat) : List (PhysicalLink extent) → Nat
  | [] => 0
  | i::rest => updateDegreeCost (w := w) K extent [i.val] block n +
      sweepDegreeBudget w K extent block n rest

/-- A previously bounded coordinate incurs only the computed later-action cost. -/
theorem polynomialSweep_degree (n block d : Nat) (xs : List (PhysicalLink extent))
    (p : (F).V) (hp : DegreeLE block d p.val) :
    DegreeLE block (d+sweepDegreeBudget w K extent block n xs)
      (polynomialSweep hw0 hw1 K extent hK n xs p).val := by
  induction xs generalizing p d with
  | nil => exact hp
  | cons i rest ih =>
      have hu := conditionalApproximation_degree hw0 hw1 K extent hK [i.val]
        block d n p hp
      have h := ih _ _ hu
      exact h.mono (by simp only [sweepDegreeBudget]; omega)

/-- Once a block is selected, the final bound is independent of its INPUT degree. -/
theorem polynomialSweep_selected_degree (n block : Nat)
    (xs : List (PhysicalLink extent))
    (hb : block ∈ xs.map (fun i => (boundaryCompleteSlabLinks extent).idxOf i.val))
    (p : (F).V) :
    DegreeLE block (sweepDegreeBudget w K extent block n xs)
      (polynomialSweep hw0 hw1 K extent hK n xs p).val := by
  induction xs generalizing p with
  | nil => exact False.elim (List.not_mem_nil hb)
  | cons i rest ih =>
      rcases List.mem_cons.mp hb with he | ht
      · subst block
        have h := polynomialSweep_degree hw0 hw1 K extent hK n
          ((boundaryCompleteSlabLinks extent).idxOf i.val) 0 rest
          (polynomialUpdate hw0 hw1 K extent hK i n p)
          (polynomialUpdate_selected_degree_zero hw0 hw1 K extent hK i n p)
        exact h.mono (by simp only [sweepDegreeBudget]; omega)
      · have h := ih ht (polynomialUpdate hw0 hw1 K extent hK i n p)
        exact h.mono (by simp only [sweepDegreeBudget]; omega)

/-- The actual colored physical schedule erases ALL input degrees. The returned
bound depends on nome, finite heat cutoff, extent and iteration, not on p. -/
theorem physicalSweep_degree_bound (n block : Nat)
    (hb : block < (boundaryCompleteSlabLinks extent).length) (p : (F).V) :
    DegreeLE block (sweepDegreeBudget w K extent block n (schedule extent))
      (polynomialSweep hw0 hw1 K extent hK n (schedule extent) p).val :=
  polynomialSweep_selected_degree hw0 hw1 K extent hK n block (schedule extent)
    (physical_schedule_index_covers extent block (List.mem_range.mpr hb)) p

end YMGap.Continuum.BF4ExactSlabPolynomialSweepDegree

#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepDegree.approximateInverse_degree
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepDegree.updateDegreeCost
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepDegree.conditionalApproximation_degree
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepDegree.polynomialUpdate
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepDegree.polynomialUpdate_selected_degree_zero
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepDegree.polynomialSweep
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepDegree.sweepDegreeBudget
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepDegree.polynomialSweep_degree
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepDegree.polynomialSweep_selected_degree
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepDegree.physicalSweep_degree_bound
