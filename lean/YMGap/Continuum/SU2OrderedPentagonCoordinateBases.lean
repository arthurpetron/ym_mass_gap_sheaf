/-
# Fixed-ordered four-factor coordinate bases and pentagon

The three cyclic charts with reversed vertices are rephased by the exact raw
transvectant signs derived in `SU2OrderedFourChartNormalization`.  The same
involutive channel phases are inserted in synthesis.  This produces five
constructive coordinate bases whose coordinates are the fixed-ordered raw
nested transvectants, and hence a fixed-ordered all-label pentagon.
-/

import YMGap.Continuum.SU2OrderedFourChartNormalization

namespace YMGap.Continuum.SU2OrderedPentagonCoordinateBases

open YMGap.Constructive
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantSwapParity
open YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.SU2GeneralHahnLeftCombFourCoordinateBases
open YMGap.Continuum.SU2GeneralHahnFourCombTreeCoordinateBases
open YMGap.Continuum.SU2GeneralHahnBalancedFourCoordinateBases
open YMGap.Continuum.SU2GeneralHahnCyclicPentagon
open YMGap.Continuum.SU2OrderedRightNormalizationBridge
open YMGap.Continuum.SU2OrderedFourChartNormalization
open YMGap.Continuum.PentagonFromCoordinateBases

local infix:50 " ≈ " => Q'.eqv

private theorem mul_involutions (x y : Q')
    (hx : x * x ≈ 1) (hy : y * y ≈ 1) :
    (x * y) * (x * y) ≈ 1 := by
  have hswap := Q'.mul_eqv_congr_left (x * y) _ _
    (Q'.mul_comm_eqv x y)
  have hgroup := Q'.mul_assoc_eqv x y (y * x)
  have hinner : y * (y * x) ≈ x := by
    exact Q'.eqv_trans _ ((y * y) * x) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv y y x))
      (Q'.eqv_trans _ (1 * x) _
        (Q'.mul_eqv_congr_right _ _ _ hy) (Q'.one_mul_eqv x))
  have hcollapse := Q'.mul_eqv_congr_left x _ _ hinner
  exact Q'.eqv_trans _ _ _ hswap
    (Q'.eqv_trans _ _ _ hgroup
      (Q'.eqv_trans _ _ _ hcollapse hx))

private theorem phase_collapse (q x : Q') (hq : q * q ≈ 1) :
    q * (q * x) ≈ x := by
  exact Q'.eqv_trans _ ((q * q) * x) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv q q x))
    (Q'.eqv_trans _ (1 * x) _
      (Q'.mul_eqv_congr_right _ _ _ hq) (Q'.one_mul_eqv x))

private theorem phase_bridge_converse (q ordered cyclic : Q')
    (hq : q * q ≈ 1) (hbridge : ordered ≈ q * cyclic) :
    q * ordered ≈ cyclic := by
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left q _ _ hbridge)
    (phase_collapse q cyclic hq)

/-- Complete four-factor reconstruction respects pointwise channel
equivalence. -/
theorem leftComb4Reconstruct_congr (a b c d : Nat)
    (u v : LeftComb4Channel a b c d → Q')
    (huv : ∀ q, u q ≈ v q) :
    PhysicalQuadBoxEqv a b c d
      (leftComb4Reconstruct a b c d u)
      (leftComb4Reconstruct a b c d v) := by
  intro i j l r hi hj hl hr
  apply leftNestedReconstruct_congr a b c
  intro q
  apply globalHahnReconstruct_congr
  intro outer
  exact huv
    { k₁ := q.k
      k₁_le := q.k_le
      k₂ := q.outer.k
      k₂_le := q.outer.k_le
      outer := outer }
  · exact q.outer.s_le
  · exact hr
  · exact hi
  · exact hj
  · exact hl

/-- The channelwise phase attached to each fixed-ordered chart. -/
def orderedChartPhase (a b c d : Nat) :
    (T : CyclicPentagonTree) →
      (cyclicPentagonCoordinateBases a b c d).Index T → Q'
  | .p0, _ => 1
  | .p1, q => orderedP1Phase q
  | .p2, q => orderedP2Phase q
  | .p3, q => orderedP3Phase q
  | .p4, _ => 1

/-- Dual synthesis data: only the three affected charts are rephased. -/
def orderedChartPhaseData (a b c d : Nat) :
    (T : CyclicPentagonTree) →
      ((cyclicPentagonCoordinateBases a b c d).Index T → Q') →
      (cyclicPentagonCoordinateBases a b c d).Index T → Q'
  | .p0, u => u
  | .p1, u => fun q => orderedP1Phase q * u q
  | .p2, u => fun q => orderedP2Phase q * u q
  | .p3, u => fun q => orderedP3Phase q * u q
  | .p4, u => u

/-- Fixed-ordered raw coordinates in each of the five charts. -/
def orderedChartCoordinates (a b c d : Nat) :
    (T : CyclicPentagonTree) → QuadForm →
      (cyclicPentagonCoordinateBases a b c d).Index T → Q'
  | .p0, x => leftComb4Coordinates a b c d x
  | .p1, x => orderedP1Coordinates a b c d x
  | .p2, x => orderedP2Coordinates a b c d x
  | .p3, x => orderedP3Coordinates a b c d x
  | .p4, x => balanced4Coordinates a b c d x

/-- Every chart phase is constructively involutive. -/
theorem orderedChartPhase_mul_self (a b c d : Nat)
    (T : CyclicPentagonTree)
    (q : (cyclicPentagonCoordinateBases a b c d).Index T) :
    orderedChartPhase a b c d T q * orderedChartPhase a b c d T q ≈ 1 := by
  cases T with
  | p0 => exact Q'.one_mul_eqv 1
  | p1 => exact swapPhase_mul_self q.k₂
  | p2 => exact swapPhase_mul_self q.outer.k
  | p3 =>
      exact mul_involutions _ _ (swapPhase_mul_self q.outer.k)
        (swapPhase_mul_self q.k₂)
  | p4 => exact Q'.one_mul_eqv 1

/-- Uniform raw ordered/cyclic bridge for all five charts. -/
theorem orderedChartCoordinates_eq_phase_cyclic (a b c d : Nat)
    (T : CyclicPentagonTree) (x : QuadForm)
    (q : (cyclicPentagonCoordinateBases a b c d).Index T) :
    orderedChartCoordinates a b c d T x q ≈
      orderedChartPhase a b c d T q *
        (cyclicPentagonCoordinateBases a b c d).coords T x q := by
  cases T with
  | p0 => exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | p1 => exact orderedP1Coordinates_eq_phase a b c d x q
  | p2 => exact orderedP2Coordinates_eq_phase a b c d x q
  | p3 => exact orderedP3Coordinates_eq_phase a b c d x q
  | p4 => exact Q'.eqv_symm (Q'.one_mul_eqv _)

/-- Fixed-ordered coordinates respect the common physical four-box. -/
theorem orderedChartCoordinates_congr (a b c d : Nat)
    (T : CyclicPentagonTree) (x z : QuadForm)
    (hxz : PhysicalQuadBoxEqv a b c d x z)
    (q : (cyclicPentagonCoordinateBases a b c d).Index T) :
    orderedChartCoordinates a b c d T x q ≈
      orderedChartCoordinates a b c d T z q := by
  have hleft := orderedChartCoordinates_eq_phase_cyclic a b c d T x q
  have hmiddle := Q'.mul_eqv_congr_left
    (orderedChartPhase a b c d T q) _ _
    ((cyclicPentagonCoordinateBases a b c d).coords_congr T hxz q)
  have hright := orderedChartCoordinates_eq_phase_cyclic a b c d T z q
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ hmiddle (Q'.eqv_symm hright))

/-- Fixed-ordered analysis is a right inverse to phase-dual synthesis. -/
theorem orderedChartCoordinates_synth (a b c d : Nat)
    (T : CyclicPentagonTree)
    (u : (cyclicPentagonCoordinateBases a b c d).Index T → Q')
    (q : (cyclicPentagonCoordinateBases a b c d).Index T) :
    orderedChartCoordinates a b c d T
      ((cyclicPentagonCoordinateBases a b c d).synth T
        (orderedChartPhaseData a b c d T u)) q ≈ u q := by
  cases T with
  | p0 => exact leftComb4Coordinates_reconstruct a b c d u q
  | p1 =>
      have hbridge := orderedP1Coordinates_eq_phase a b c d
        (p1Reconstruct a b c d (orderedChartPhaseData a b c d .p1 u)) q
      have hcyclic := p1Coordinates_reconstruct a b c d
        (orderedChartPhaseData a b c d .p1 u) q
      have hmul := Q'.mul_eqv_congr_left (orderedP1Phase q) _ _ hcyclic
      exact Q'.eqv_trans _ _ _ hbridge
        (Q'.eqv_trans _ _ _ hmul
          (phase_collapse (orderedP1Phase q) (u q)
            (swapPhase_mul_self q.k₂)))
  | p2 =>
      have hbridge := orderedP2Coordinates_eq_phase a b c d
        (p2Reconstruct a b c d (orderedChartPhaseData a b c d .p2 u)) q
      have hcyclic := p2Coordinates_reconstruct a b c d
        (orderedChartPhaseData a b c d .p2 u) q
      have hmul := Q'.mul_eqv_congr_left (orderedP2Phase q) _ _ hcyclic
      exact Q'.eqv_trans _ _ _ hbridge
        (Q'.eqv_trans _ _ _ hmul
          (phase_collapse (orderedP2Phase q) (u q)
            (swapPhase_mul_self q.outer.k)))
  | p3 =>
      have hphase := orderedChartPhase_mul_self a b c d .p3 q
      have hbridge := orderedP3Coordinates_eq_phase a b c d
        (p3Reconstruct a b c d (orderedChartPhaseData a b c d .p3 u)) q
      have hcyclic := p3Coordinates_reconstruct a b c d
        (orderedChartPhaseData a b c d .p3 u) q
      have hmul := Q'.mul_eqv_congr_left (orderedP3Phase q) _ _ hcyclic
      exact Q'.eqv_trans _ _ _ hbridge
        (Q'.eqv_trans _ _ _ hmul
          (phase_collapse (orderedP3Phase q) (u q) hphase))
  | p4 => exact balanced4Coordinates_reconstruct a b c d u q

/-- Phase-dual synthesis after fixed-ordered analysis recovers the common
physical four-form. -/
theorem orderedChartSynth_coordinates (a b c d : Nat)
    (T : CyclicPentagonTree) (x : QuadForm) :
    PhysicalQuadBoxEqv a b c d
      ((cyclicPentagonCoordinateBases a b c d).synth T
        (orderedChartPhaseData a b c d T
          (orderedChartCoordinates a b c d T x))) x := by
  cases T with
  | p0 =>
      intro i j l r hi hj hl hr
      exact leftComb4Reconstruct_coordinates a b c d x i j l r hi hj hl hr
  | p1 =>
      have hdata : ∀ q : LeftComb4Channel b c a d,
          orderedChartPhaseData a b c d .p1
              (orderedChartCoordinates a b c d .p1 x) q ≈
            p1Coordinates a b c d x q := by
        intro q
        exact phase_bridge_converse (orderedP1Phase q)
          (orderedP1Coordinates a b c d x q) (p1Coordinates a b c d x q)
          (swapPhase_mul_self q.k₂)
          (orderedP1Coordinates_eq_phase a b c d x q)
      intro i j l r hi hj hl hr
      have hcongr := leftComb4Reconstruct_congr b c a d
        (orderedChartPhaseData a b c d .p1
          (orderedChartCoordinates a b c d .p1 x))
        (p1Coordinates a b c d x) hdata j l i r hj hl hi hr
      exact Q'.eqv_trans _ _ _ hcongr
        (p1Reconstruct_coordinates a b c d x i j l r hi hj hl hr)
  | p2 =>
      have hdata : ∀ q : LeftComb4Channel b c d a,
          orderedChartPhaseData a b c d .p2
              (orderedChartCoordinates a b c d .p2 x) q ≈
            p2Coordinates a b c d x q := by
        intro q
        exact phase_bridge_converse (orderedP2Phase q)
          (orderedP2Coordinates a b c d x q) (p2Coordinates a b c d x q)
          (swapPhase_mul_self q.outer.k)
          (orderedP2Coordinates_eq_phase a b c d x q)
      intro i j l r hi hj hl hr
      have hcongr := leftComb4Reconstruct_congr b c d a
        (orderedChartPhaseData a b c d .p2
          (orderedChartCoordinates a b c d .p2 x))
        (p2Coordinates a b c d x) hdata j l r i hj hl hr hi
      exact Q'.eqv_trans _ _ _ hcongr
        (p2Reconstruct_coordinates a b c d x i j l r hi hj hl hr)
  | p3 =>
      have hdata : ∀ q : LeftComb4Channel c d b a,
          orderedChartPhaseData a b c d .p3
              (orderedChartCoordinates a b c d .p3 x) q ≈
            p3Coordinates a b c d x q := by
        intro q
        exact phase_bridge_converse (orderedP3Phase q)
          (orderedP3Coordinates a b c d x q) (p3Coordinates a b c d x q)
          (orderedChartPhase_mul_self a b c d .p3 q)
          (orderedP3Coordinates_eq_phase a b c d x q)
      intro i j l r hi hj hl hr
      have hcongr := leftComb4Reconstruct_congr c d b a
        (orderedChartPhaseData a b c d .p3
          (orderedChartCoordinates a b c d .p3 x))
        (p3Coordinates a b c d x) hdata l r j i hl hr hj hi
      exact Q'.eqv_trans _ _ _ hcongr
        (p3Reconstruct_coordinates a b c d x i j l r hi hj hl hr)
  | p4 =>
      intro i j l r hi hj hl hr
      exact balanced4Reconstruct_coordinates a b c d x i j l r hi hj hl hr

/-- **All five fixed-ordered raw charts as constructive coordinate bases.** -/
def orderedPentagonCoordinateBases (a b c d : Nat) :
    CoordinateBases CyclicPentagonTree QuadForm where
  Index := (cyclicPentagonCoordinateBases a b c d).Index
  Rel := PhysicalQuadBoxEqv a b c d
  rel_refl := fun x i j l r hi hj hl hr => Q'.eqv_refl _
  rel_symm := fun h i j l r hi hj hl hr =>
    Q'.eqv_symm (h i j l r hi hj hl hr)
  rel_trans := fun h₁ h₂ i j l r hi hj hl hr =>
    Q'.eqv_trans _ _ _ (h₁ i j l r hi hj hl hr)
      (h₂ i j l r hi hj hl hr)
  synth := fun T u => (cyclicPentagonCoordinateBases a b c d).synth T
    (orderedChartPhaseData a b c d T u)
  coords := orderedChartCoordinates a b c d
  coords_congr := by
    intro T x z hxz q
    exact orderedChartCoordinates_congr a b c d T x z hxz q
  synth_coords := by
    intro T x
    exact orderedChartSynth_coordinates a b c d T x
  coords_synth := by
    intro T u q
    exact orderedChartCoordinates_synth a b c d T u q

/-- Every ordered basis change is the corresponding cyclic basis change
conjugated by the explicitly displayed input/output channel phases. -/
theorem orderedBasisChange_eq_rephased_cyclic (a b c d : Nat)
    (A C : CyclicPentagonTree)
    (u : (cyclicPentagonCoordinateBases a b c d).Index A → Q')
    (q : (cyclicPentagonCoordinateBases a b c d).Index C) :
    basisChange (orderedPentagonCoordinateBases a b c d) A C u q ≈
      orderedChartPhase a b c d C q *
        basisChange (cyclicPentagonCoordinateBases a b c d) A C
          (orderedChartPhaseData a b c d A u) q := by
  exact orderedChartCoordinates_eq_phase_cyclic a b c d C
    ((cyclicPentagonCoordinateBases a b c d).synth A
      (orderedChartPhaseData a b c d A u)) q

/-- **Full all-degree, all-dependent-channel pentagon in the fixed ordered
raw transvectant convention.** -/
theorem ordered_allLabel_pentagon (a b c d : Nat)
    (u : LeftComb4Channel a b c d → Q') :
    CoordEqv (orderedPentagonCoordinateBases a b c d) .p3
      (basisChange (orderedPentagonCoordinateBases a b c d) .p2 .p3
        (basisChange (orderedPentagonCoordinateBases a b c d) .p1 .p2
          (basisChange (orderedPentagonCoordinateBases a b c d) .p0 .p1 u)))
      (basisChange (orderedPentagonCoordinateBases a b c d) .p4 .p3
        (basisChange (orderedPentagonCoordinateBases a b c d) .p0 .p4 u)) := by
  exact pentagon_from_coordinate_bases
    (orderedPentagonCoordinateBases a b c d)
    .p0 .p1 .p2 .p3 .p4 u

end YMGap.Continuum.SU2OrderedPentagonCoordinateBases

#print axioms YMGap.Continuum.SU2OrderedPentagonCoordinateBases.leftComb4Reconstruct_congr
#print axioms YMGap.Continuum.SU2OrderedPentagonCoordinateBases.orderedChartPhase_mul_self
#print axioms YMGap.Continuum.SU2OrderedPentagonCoordinateBases.orderedChartCoordinates_eq_phase_cyclic
#print axioms YMGap.Continuum.SU2OrderedPentagonCoordinateBases.orderedChartCoordinates_congr
#print axioms YMGap.Continuum.SU2OrderedPentagonCoordinateBases.orderedChartCoordinates_synth
#print axioms YMGap.Continuum.SU2OrderedPentagonCoordinateBases.orderedChartSynth_coordinates
#print axioms YMGap.Continuum.SU2OrderedPentagonCoordinateBases.orderedPentagonCoordinateBases
#print axioms YMGap.Continuum.SU2OrderedPentagonCoordinateBases.orderedBasisChange_eq_rephased_cyclic
#print axioms YMGap.Continuum.SU2OrderedPentagonCoordinateBases.ordered_allLabel_pentagon
