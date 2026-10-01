/-
# Dyadic quartic correction in the unchanged original Wilson edge measure

The rational dyadic nome is an analytic diagnostic schedule, not a physical
coupling or lattice-spacing trajectory.  These bounds keep the complete
spatial and terminal source, the original odd partition, and the ordered
word-length factor.  They make no centered-variance or survival claim.
-/

import YMGap.Continuum.SU2HeatQuarticDyadicBudget
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialDyadicQuartic

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (polyMul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (edgeDensity energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRadialIncrement
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement
open YMGap.Continuum.QuaternionHaarWordQuartic (wordFourthFactor)
open YMGap.Continuum.SU2HeatQuarticDyadicSchedule
open YMGap.Continuum.SU2HeatQuarticDyadicBudget

local notation:max "N" width:arg => List.length (baseLinks width)

/-- A cutoff satisfying both the original head and shifted quartic-spin guards. -/
def dyadicCutoff (m stage : Nat) : Nat :=
  max (headCutoff (nome m)) (split m+3) + stage

theorem head_le_cutoff (m stage : Nat) :
    headCutoff (nome m) ≤ dyadicCutoff m stage :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ _)

theorem split_le_cutoff (m stage : Nat) :
    split m+3 ≤ dyadicCutoff m stage :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_add_right _ _)

private theorem word_factor_nonnegative (n : Nat) :
    (0 : Q') ≤ wordFourthFactor n := by
  unfold wordFourthFactor
  exact Q'.mul_nonneg _ _ (by decide)
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (Q'.ofNat_nonneg _) (Q'.ofNat_nonneg _))
      (Q'.mul_nonneg _ _ (Q'.ofNat_nonneg _) (Q'.ofNat_nonneg _)))

/-- Geometric fourth-moment budget for an actual ordered Wilson word.  The
finite cutoff, terminal messages, and original odd partition are unchanged. -/
theorem word_quartic_geometric_bound (m : Nat) (hm : 6 ≤ m)
    (stage width depth : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges →
      (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity (nome m) (dyadicCutoff m stage) width
        (terminalMessage (nome m) (dyadicCutoff m stage) width depth))
        (polyMul (wordChordal width loop) (wordChordal width loop))) ≤
      (wordFourthFactor loop.edges.length *
        (2968 * HalfPow.half^(4*m))) *
        oddMass (nome m) (dyadicCutoff m stage) width depth := by
  have hw0 := nome_pos hm
  have hw1 := nome_lt_one m
  have hK := head_le_cutoff m stage
  have hS := split_ge_one m
  have hshift := split_le_cutoff m stage
  have hbase := word_quartic_bound hw0 hw1 (split m) (dyadicCutoff m stage)
    width depth hS hshift hK (half_guard hm) (tail_le_eighth hm) loop hactive
  have hrate : wordQuarticRate (nome m) (split m) loop ≤
      wordFourthFactor loop.edges.length * (2968 * HalfPow.half^(4*m)) := by
    unfold wordQuarticRate
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ (budget_bound m hm)
      (word_factor_nonnegative _)
  exact Q'.le_trans' _ _ _ hbase
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hrate
      (Q'.le_of_lt (oddMass_positive hw0 hw1 _ _ hK depth)))

/-- A computable epsilon index controls the same original word quartic term
relative to the rational dyadic nome defect; the path-length factor remains. -/
theorem word_quartic_small (e : Q') (he : (0 : Q') < e)
    (m : Nat) (hm : smallModulus e ≤ m) (stage width depth : Nat)
    (loop : SourceLoop width)
    (hactive : ∀ edge, edge ∈ loop.edges →
      (baseLinks width).idxOf edge.link ∈ activeBlocks width) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity (nome m) (dyadicCutoff m stage) width
        (terminalMessage (nome m) (dyadicCutoff m stage) width depth))
        (polyMul (wordChordal width loop) (wordChordal width loop))) ≤
      (wordFourthFactor loop.edges.length * (e * defect m)) *
        oddMass (nome m) (dyadicCutoff m stage) width depth := by
  have hm6 : 6 ≤ m := Nat.le_trans (modulus_ge_six e) hm
  have hw0 := nome_pos hm6
  have hw1 := nome_lt_one m
  have hK := head_le_cutoff m stage
  have hbase := word_quartic_bound hw0 hw1 (split m) (dyadicCutoff m stage)
    width depth (split_ge_one m) (split_le_cutoff m stage) hK
    (half_guard hm6) (tail_le_eighth hm6) loop hactive
  have hrate : wordQuarticRate (nome m) (split m) loop ≤
      wordFourthFactor loop.edges.length * (e * defect m) := by
    unfold wordQuarticRate
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ (budget_small e he m hm)
      (word_factor_nonnegative _)
  exact Q'.le_trans' _ _ _ hbase
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hrate
      (Q'.le_of_lt (oddMass_positive hw0 hw1 _ _ hK depth)))

/-- The quartic contribution to the unchanged original Wilson energy is
small on the diagnostic dyadic schedule. The mixed radial moment remains
under the full edge weight and is not estimated here. -/
theorem wilson_energy_small_quartic (e : Q') (he : (0 : Q') < e)
    (m : Nat) (hm : smallModulus e ≤ m) (stage width depth : Nat)
    (loop : SourceLoop width)
    (hactive : ∀ edge, edge ∈ loop.edges →
      (baseLinks width).idxOf edge.link ∈ activeBlocks width) :
    (2 : Q') * energy (nome m) (dyadicCutoff m stage) width
        (terminalMessage (nome m) (dyadicCutoff m stage) width depth)
        (sourceCharacter width loop.edges 1) ≤
      2 * mixedRadialMoment (nome m) (dyadicCutoff m stage) width depth loop +
        2 * ((wordFourthFactor loop.edges.length * (e * defect m)) *
          oddMass (nome m) (dyadicCutoff m stage) width depth) := by
  have hm6 : 6 ≤ m := Nat.le_trans (modulus_ge_six e) hm
  have hw0 := nome_pos hm6
  have hw1 := nome_lt_one m
  have hK := head_le_cutoff m stage
  exact Q'.le_trans' _ _ _
    (wilson_energy_radial_cleared hw0 hw1 (dyadicCutoff m stage) width hK depth loop)
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (radial_moment_split (nome m) (dyadicCutoff m stage)
        width depth loop))
      (Q'.add_le_add (Q'.le_refl' _)
        (Q'.mul_le_mul_of_nonneg_left _ _ 2
          (word_quartic_small e he m hm stage width depth loop hactive)
          (by decide))))

#print axioms dyadicCutoff
#print axioms head_le_cutoff
#print axioms split_le_cutoff
#print axioms word_quartic_geometric_bound
#print axioms word_quartic_small
#print axioms wilson_energy_small_quartic

end YMGap.Continuum.BF4ExactSlabFixedSpatialDyadicQuartic
