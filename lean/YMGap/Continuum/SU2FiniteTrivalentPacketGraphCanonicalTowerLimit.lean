/-
# Constructive correlator limits for the canonical refinement tower

The canonical compensated refinement tower has unbounded edge count, exact
finite-level correlator compatibility, and one common support-pruned spectral
separator.  This file packages precisely those three facts in a reusable
limit interface and constructs the pointwise constructive-real correlator
limit.

The limit is explicit: every tower correlator is rationally equivalent to its
seed value, so the lifted sequence converges with stage zero to the constant
constructive real containing that seed value.  No subsequence, compactness
choice, or extracted modulus is used.

This remains a limit of the specially generated one-edge subdivision tower.
It is not a cofinal four-dimensional volume exhaustion, an
Osterwalder--Schrader measure, or a continuum limit.
-/

import YMGap.Constructive.CRealAbs
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalRefinementTower

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalTowerLimit

set_option maxHeartbeats 1000000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphSupportedRefinementPath
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalRefinementTower
open YMGap.Continuum.SU2PeterWeylWilsonBlock

local infix:50 " ≈ " => Q'.eqv

/-! ## A reusable limit-compatible tower interface -/

/-- Finite graph states with unbounded edge count, pointwise constructive-real
correlator limits, and one strictly positive spectral separator valid at every
level.

This interface records limit-compatible finite-volume data only.  It does not
assert geometric cofinality, locality, reflection positivity, or continuum
scaling. -/
structure UniformlyGappedCorrelatorTower (K : Nat) where
  level : Nat → CompensatedGraphState K
  edgeCountUnbounded : ∀ bound : Nat, ∃ n : Nat,
    bound ≤ (level n).edges.length
  correlatorLimit : Nat → CReal
  correlatorsConverge : ∀ t : Nat,
    CReal.ConvergesTo
      (fun n => CReal.ofQ' (supportedGraphCorr (level n) t))
      (correlatorLimit t)
  separator : Q'
  separator_pos : (0 : Q') < separator
  levelGap : ∀ n : Nat,
    SpectralGapBound (supportedGraphSpectralModel (level n)) separator

/-! ## The explicit canonical tower limit -/

/-- The rational correlator sequence at a fixed Euclidean time. -/
def canonicalTowerCorrSeq {K : Nat}
    (P : PointedCompensatedGraphState K) (t n : Nat) : Q' :=
  supportedGraphCorr (canonicalTower P n).state t

/-- Its explicit constructive-real limit is the embedded seed correlator. -/
def canonicalTowerCorrLimit {K : Nat}
    (P : PointedCompensatedGraphState K) (t : Nat) : CReal :=
  CReal.ofQ' (supportedGraphCorr P.state t)

/-- The edge counts in the canonical tower are unbounded. -/
theorem canonicalTower_edgeCountUnbounded {K : Nat}
    (P : PointedCompensatedGraphState K) (bound : Nat) :
    ∃ n : Nat, bound ≤ (canonicalTower P n).state.edges.length := by
  refine ⟨bound, ?_⟩
  rw [canonicalTower_edge_length P bound]
  omega

/-- Exact compatibility gives a stage-zero convergence modulus for every
time-correlator. -/
theorem canonicalTowerCorr_converges {K : Nat}
    (P : PointedCompensatedGraphState K) (t : Nat) :
    CReal.ConvergesTo
      (fun n => CReal.ofQ' (canonicalTowerCorrSeq P t n))
      (canonicalTowerCorrLimit P t) := by
  intro ε hε
  refine ⟨0, fun n _ => ⟨0, fun k _ => ?_⟩⟩
  simp only [canonicalTowerCorrSeq, canonicalTowerCorrLimit,
    CReal.ofQ'_approx]
  have hcorr := canonicalTower_supportedCorr P n t
  have hε0 : (0 : Q') ≤ ε := Q'.le_of_lt hε
  exact
    ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hcorr)
        (Q'.add_le_self_of_nonneg _ _ hε0),
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hcorr))
        (Q'.add_le_self_of_nonneg _ _ hε0)⟩

/-- The constructed limit is pointwise identified with the seed correlator,
not merely obtained as an unspecified compactness limit. -/
theorem canonicalTowerCorrLimit_identified {K : Nat}
    (P : PointedCompensatedGraphState K) (t : Nat) :
    canonicalTowerCorrLimit P t =
      CReal.ofQ' (supportedGraphCorr P.state t) := rfl

/-- An uncompensated pointed seed produces a fully inhabited
`UniformlyGappedCorrelatorTower`: unbounded finite graphs, explicit pointwise
correlator limits, and the common `(1/8)^2` support-pruned separator. -/
def canonicalUniformlyGappedTower {K : Nat}
    (P : PointedCompensatedGraphState K)
    (hcopy : P.state.copiedEdges = []) :
    UniformlyGappedCorrelatorTower K where
  level := fun n => (canonicalTower P n).state
  edgeCountUnbounded := canonicalTower_edgeCountUnbounded P
  correlatorLimit := canonicalTowerCorrLimit P
  correlatorsConverge := canonicalTowerCorr_converges P
  separator := eighth * eighth
  separator_pos := by decide
  levelGap := canonicalTower_uniform_gap P hcopy

theorem canonicalUniformlyGappedTower_separator {K : Nat}
    (P : PointedCompensatedGraphState K)
    (hcopy : P.state.copiedEdges = []) :
    (canonicalUniformlyGappedTower P hcopy).separator =
      eighth * eighth := rfl

theorem canonicalUniformlyGappedTower_limit {K : Nat}
    (P : PointedCompensatedGraphState K)
    (hcopy : P.state.copiedEdges = []) (t : Nat) :
    (canonicalUniformlyGappedTower P hcopy).correlatorLimit t =
      CReal.ofQ' (supportedGraphCorr P.state t) := rfl

/-! ## A closed non-vacuity witness -/

/-- A one-edge, two-label seed with nonzero vacuum and first excited
correlators.  It is used only to certify that the tower interface above has a
closed inhabitant; the general construction remains parametrized by an
arbitrary pointed seed. -/
def concreteSeedState : CompensatedGraphState 1 where
  edges := [0]
  vertices := []
  packet := fun _ =>
    SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude.allOnesPacket 1
  copiedEdges := []
  copied_mem := by
    intro edge h
    cases h

def concretePointedSeed : PointedCompensatedGraphState 1 where
  state := concreteSeedState
  oldEdge := 0
  old_mem := by simp [concreteSeedState]

theorem concretePointedSeed_uncompensated :
    concretePointedSeed.state.copiedEdges = [] := rfl

/-- A closed inhabitant of the complete tower interface. -/
def concreteUniformlyGappedTower : UniformlyGappedCorrelatorTower 1 :=
  canonicalUniformlyGappedTower concretePointedSeed
    concretePointedSeed_uncompensated

/-- The seed correlator at time zero is exactly one. -/
theorem concreteSeedCorr_zero :
    supportedGraphCorr concreteSeedState 0 ≈ (1 : Q') := by decide

/-- The first-time correlator is nonzero and equals the common spectral
separator, so the closed tower witness is not produced by an empty supported
spectrum. -/
theorem concreteSeedCorr_one :
    supportedGraphCorr concreteSeedState 1 ≈ eighth * eighth := by decide

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalTowerLimit

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalTowerLimit.canonicalTower_edgeCountUnbounded
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalTowerLimit.canonicalTowerCorr_converges
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalTowerLimit.canonicalTowerCorrLimit_identified
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalTowerLimit.canonicalUniformlyGappedTower
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalTowerLimit.canonicalUniformlyGappedTower_separator
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalTowerLimit.canonicalUniformlyGappedTower_limit
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalTowerLimit.concreteUniformlyGappedTower
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalTowerLimit.concreteSeedCorr_zero
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalTowerLimit.concreteSeedCorr_one
