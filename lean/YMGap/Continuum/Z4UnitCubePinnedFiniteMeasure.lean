/-
# The elementary cube as a normalized finite-volume packet event

The all-volume cube calculation proves that one gauge-closed local mode has
the same exact amplitude in every finite box and at every character cutoff
`K >= 2`.  This file inserts that mode into the *complete finite packet
support* rather than considering it in isolation.

For box `n` and cutoff `K`, `unitCubeBoxPartition K n` is the finite sum of
all nonnegative **globally nonvacuum** physical modes of the constructed
trivalent packet carrier (the support used by its connected spectral model).
This is not a two-state carrier: it enumerates the complete bounded edge
labelling support, filters every exact fusion guard, and uses the derived
SU(2) heat-kernel coefficient on every plaquette.  The explicit cube mode gives
a derived, volume- and cutoff-independent positive lower bound on this
partition function.  Consequently its normalized one-mode mass is a genuine
positive rational in `(0,1]`.  The exact insertion identity

    cubeProbability * boxPartition  ~=  cubePinnedNumerator

has a right-hand side equal to the same exact six-face weight in every box.
Thus all exterior-volume dependence is isolated in the normalization, not
silently summed into the local numerator.

Honest residual: the packet carrier is concrete exact finite Z4/SU(2) data,
but it has not been identified with the genuine finite-volume Haar/path-integral
Yang--Mills functional.  In particular, `unitCubeBoxPartition` is the total
weight of the constructed *excited packet support*: it omits the vacuum by
definition and is neither the vacuum-inclusive state normalization nor the
physical Haar partition function.  `unitCubeModeProbability` is therefore a
conditional normalization inside this exact excited carrier, not yet a
Yang--Mills event probability.
Moreover no upper bound or Cauchy estimate for this complete packet partition
is proved here.  Positivity of the normalized cube event is pointwise in volume
and does not give a volume-uniform positive probability or a thermodynamic
limit of the full functional.  Those remaining problems require the real
packet-to-Haar identity plus connected-cluster cancellation/local normalization
(or a growing-cutoff construction); the naive additive fixed-cutoff tail is
already refuted by `Z4FixedCutoffNaiveTailFence`.

Constructive contract: Mathlib-free `Q'`/finite-list substrate, with no
nonconstructive imports, trusted compiled decisions, proof holes, or new
postulates.  The only division is `Q'.divPos`, guarded by the explicitly
proved positive finite partition function.
-/

import YMGap.Constructive.RegularCRealArith
import YMGap.Continuum.Z4UnitCubeAllVolumeAmplitude

namespace YMGap.Continuum.Z4UnitCubePinnedFiniteMeasure

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxHeatKernelCutoffPersistence
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4UnitCubeAllVolumeAmplitude

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The complete finite physical packet partition -/

/-- Number of physical packet modes in box `n` at cutoff `K`. -/
def unitCubeBoxModeCount (K n : Nat) : Nat :=
  (physicalEdgeLabellings K (usedResolutionEdges n)
    (resolutionVertices n)).length

/-- The complete finite *excited packet-carrier* weight sum: the sum of every
globally nonvacuum physical mode weight in the constructed heat-kernel packet
state.  The historical `Partition` name means a partition of this connected
spectral support; the vacuum is excluded and this is not yet identified with
the Haar Yang--Mills partition function. -/
def unitCubeBoxPartition (K n : Nat) : Q' :=
  finSum
    (packetGraphModeWeight (usedResolutionEdges n) (resolutionVertices n)
      (gaugeHeatKernelBoxPacketsAtCutoff K n))
    (unitCubeBoxModeCount K n)

/-- Every finite packet partition is nonnegative. -/
theorem unitCubeBoxPartition_nonneg (K n : Nat) :
    (0 : Q') ≤ unitCubeBoxPartition K n := by
  unfold unitCubeBoxPartition
  induction unitCubeBoxModeCount K n with
  | zero => exact Q'.le_refl' 0
  | succ m ih =>
      rw [finSum_succ]
      exact Q'.zero_le_add _ _ ih
        (packetGraphModeWeight_nonneg (usedResolutionEdges n)
          (resolutionVertices n)
          (gaugeHeatKernelBoxPacketsAtCutoff K n) m)

private theorem finSum_nonneg (g : Nat → Q')
    (hg : ∀ i, (0 : Q') ≤ g i) :
    ∀ N : Nat, (0 : Q') ≤ finSum g N
  | 0 => Q'.le_refl' 0
  | N + 1 => by
      rw [finSum_succ]
      exact Q'.zero_le_add _ _ (finSum_nonneg g hg N) (hg N)

private theorem term_le_finSum_nonneg (g : Nat → Q')
    (hg : ∀ i, (0 : Q') ≤ g i) :
    ∀ (i N : Nat), i < N → g i ≤ finSum g N
  | _, 0, hi => absurd hi (Nat.not_lt_zero _)
  | i, N + 1, hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact Q'.le_trans' _ _ _
          (term_le_finSum_nonneg g hg i N hlt)
          (Q'.add_le_self_of_nonneg _ _ (hg N))
      · subst i
        show g N ≤ finSum g N + g N
        have h := Q'.add_le_add_right 0 (finSum g N) (g N)
          (finSum_nonneg g hg N)
        rwa [Q'.zero_add'] at h

/-! ## 2. The actual pinned local numerator -/

/-- The squared projected amplitude of the explicit cube labelling in the
actual box packet state.  Unlike a free constant, this definition samples the
real packets, graph, vertices, and cube label of box `n`. -/
def unitCubePinnedNumerator (K n : Nat) : Q' :=
  let a := packetGraphProjectedAmplitude (usedResolutionEdges n)
    (resolutionVertices n) (gaugeHeatKernelBoxPacketsAtCutoff K n)
    (unitCubeSurfaceLabel n)
  a * a

/-- The pinned numerator is exactly the same derived six-face weight in every
box and at every cutoff at least two. -/
theorem unitCubePinnedNumerator_exact {K n : Nat}
    (hK : 2 ≤ K) (hn : 2 ≤ n) :
    unitCubePinnedNumerator K n ≈
      unitCubeHeatKernelAmplitude * unitCubeHeatKernelAmplitude := by
  unfold unitCubePinnedNumerator
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (unitCube_heatKernel_amplitude_exact_all_volumes_at_cutoff hK hn))
    (Q'.mul_eqv_congr_left _ _ _
      (unitCube_heatKernel_amplitude_exact_all_volumes_at_cutoff hK hn))

/-- The exact local cube numerator is strictly positive. -/
theorem unitCubePinnedNumerator_pos {K n : Nat}
    (hK : 2 ≤ K) (hn : 2 ≤ n) :
    (0 : Q') < unitCubePinnedNumerator K n := by
  have hexact := unitCubePinnedNumerator_exact hK hn
  have hconst : (0 : Q') <
      unitCubeHeatKernelAmplitude * unitCubeHeatKernelAmplitude :=
    Q'.mul_pos unitCubeHeatKernelAmplitude_pos
      unitCubeHeatKernelAmplitude_pos
  exact YMGap.Continuum.CubeRatioBounds.q_lt_of_lt_of_le hconst
    (Q'.ge_of_eqv hexact)

/-- The distinguished cube numerator occurs as an actual term of the complete
finite packet partition, so it is bounded by that partition. -/
theorem unitCubePinnedNumerator_le_partition {K n : Nat}
    (hK : 2 ≤ K) (hn : 2 ≤ n) :
    unitCubePinnedNumerator K n ≤ unitCubeBoxPartition K n := by
  obtain ⟨i, hi, hweight⟩ :=
    unitCube_heatKernel_nonzero_mode_all_volumes_at_cutoff hK hn
  have hpin := unitCubePinnedNumerator_exact hK hn
  have hpinWeight : unitCubePinnedNumerator K n ≈
      packetGraphModeWeight (usedResolutionEdges n) (resolutionVertices n)
        (gaugeHeatKernelBoxPacketsAtCutoff K n) i :=
    Q'.eqv_trans _ _ _ hpin (Q'.eqv_symm hweight)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hpinWeight) ?_
  exact term_le_finSum_nonneg
    (packetGraphModeWeight (usedResolutionEdges n) (resolutionVertices n)
      (gaugeHeatKernelBoxPacketsAtCutoff K n))
    (packetGraphModeWeight_nonneg (usedResolutionEdges n)
      (resolutionVertices n)
      (gaugeHeatKernelBoxPacketsAtCutoff K n))
    i (unitCubeBoxModeCount K n) hi

/-- A cutoff- and volume-independent exact lower bound for the complete packet
partition, supplied by the six-face mode. -/
theorem unitCubeExactWeight_le_partition {K n : Nat}
    (hK : 2 ≤ K) (hn : 2 ≤ n) :
    unitCubeHeatKernelAmplitude * unitCubeHeatKernelAmplitude ≤
      unitCubeBoxPartition K n :=
  Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (unitCubePinnedNumerator_exact hK hn))
    (unitCubePinnedNumerator_le_partition hK hn)

/-- The complete finite packet partition is strictly positive, with positivity
derived from the explicit nonzero cube mode rather than postulated. -/
theorem unitCubeBoxPartition_pos {K n : Nat}
    (hK : 2 ≤ K) (hn : 2 ≤ n) :
    (0 : Q') < unitCubeBoxPartition K n :=
  YMGap.Continuum.CubeRatioBounds.q_lt_of_lt_of_le
    (unitCubePinnedNumerator_pos hK hn)
    (unitCubePinnedNumerator_le_partition hK hn)

/-! ## 3. Normalization and the exact pinned insertion identity -/

/-- The normalized probability mass of the distinguished cube mode *conditional
on the constructed globally nonvacuum packet support*.  This is not yet a
vacuum-inclusive Yang--Mills event probability.  Its denominator proof is the
derived `unitCubeBoxPartition_pos` theorem. -/
def unitCubeModeProbability (K n : Nat) (hK : 2 ≤ K) (hn : 2 ≤ n) : Q' :=
  Q'.divPos (unitCubePinnedNumerator K n) (unitCubeBoxPartition K n)
    (unitCubeBoxPartition_pos hK hn)

/-- The normalized cube-mode mass is strictly positive at every finite volume
and cutoff. -/
theorem unitCubeModeProbability_pos {K n : Nat}
    (hK : 2 ≤ K) (hn : 2 ≤ n) :
    (0 : Q') < unitCubeModeProbability K n hK hn :=
  Q'.divPos_pos _ _ (unitCubeBoxPartition_pos hK hn)
    (unitCubePinnedNumerator_pos hK hn)

/-- The normalized cube-mode mass is at most one. -/
theorem unitCubeModeProbability_le_one {K n : Nat}
    (hK : 2 ≤ K) (hn : 2 ≤ n) :
    unitCubeModeProbability K n hK hn ≤ (1 : Q') := by
  unfold unitCubeModeProbability
  apply Q'.divPos_le_of_le_mul _ _ (unitCubeBoxPartition_pos hK hn)
  exact Q'.le_trans' _ _ _
    (unitCubePinnedNumerator_le_partition hK hn)
    (Q'.ge_of_eqv (Q'.one_mul_eqv (unitCubeBoxPartition K n)))

/-- **Exact finite-box pinned insertion identity.**  Multiplying the normalized
cube event by the complete partition recovers its actual local numerator.
No exterior plaquette count occurs on the right. -/
theorem unitCubeModeProbability_mul_partition {K n : Nat}
    (hK : 2 ≤ K) (hn : 2 ≤ n) :
    (unitCubeModeProbability K n hK hn * unitCubeBoxPartition K n) ≈
      unitCubePinnedNumerator K n := by
  unfold unitCubeModeProbability
  exact Q'.divPos_mul_eqv _ _ (unitCubeBoxPartition_pos hK hn)

/-- Restated with the derived constant: the normalized insertion times its
packet partition is exactly the cutoff- and volume-independent cube weight. -/
theorem unitCubeNormalizedInsertion_exact {K n : Nat}
    (hK : 2 ≤ K) (hn : 2 ≤ n) :
    (unitCubeModeProbability K n hK hn * unitCubeBoxPartition K n) ≈
      unitCubeHeatKernelAmplitude * unitCubeHeatKernelAmplitude :=
  Q'.eqv_trans _ _ _
    (unitCubeModeProbability_mul_partition hK hn)
    (unitCubePinnedNumerator_exact hK hn)

/-- Cross-volume/cutoff local cancellation: after restoring each finite-box
normalization, every cube insertion has exactly the same weight. -/
theorem unitCubeNormalizedInsertion_eqv
    {K K' n n' : Nat} (hK : 2 ≤ K) (hK' : 2 ≤ K')
    (hn : 2 ≤ n) (hn' : 2 ≤ n') :
    (unitCubeModeProbability K n hK hn * unitCubeBoxPartition K n) ≈
      (unitCubeModeProbability K' n' hK' hn' *
        unitCubeBoxPartition K' n') := by
  exact Q'.eqv_trans _
    (unitCubeHeatKernelAmplitude * unitCubeHeatKernelAmplitude) _
    (Q'.eqv_trans _ _ _
      (unitCubeModeProbability_mul_partition hK hn)
      (unitCubePinnedNumerator_exact hK hn))
    (Q'.eqv_symm (Q'.eqv_trans _ _ _
      (unitCubeModeProbability_mul_partition hK' hn')
      (unitCubePinnedNumerator_exact hK' hn')))

end YMGap.Continuum.Z4UnitCubePinnedFiniteMeasure

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.Z4UnitCubePinnedFiniteMeasure.unitCubeBoxPartition_nonneg
#print axioms YMGap.Continuum.Z4UnitCubePinnedFiniteMeasure.unitCubePinnedNumerator_exact
#print axioms YMGap.Continuum.Z4UnitCubePinnedFiniteMeasure.unitCubePinnedNumerator_pos
#print axioms YMGap.Continuum.Z4UnitCubePinnedFiniteMeasure.unitCubePinnedNumerator_le_partition
#print axioms YMGap.Continuum.Z4UnitCubePinnedFiniteMeasure.unitCubeExactWeight_le_partition
#print axioms YMGap.Continuum.Z4UnitCubePinnedFiniteMeasure.unitCubeBoxPartition_pos
#print axioms YMGap.Continuum.Z4UnitCubePinnedFiniteMeasure.unitCubeModeProbability_pos
#print axioms YMGap.Continuum.Z4UnitCubePinnedFiniteMeasure.unitCubeModeProbability_le_one
#print axioms YMGap.Continuum.Z4UnitCubePinnedFiniteMeasure.unitCubeModeProbability_mul_partition
#print axioms YMGap.Continuum.Z4UnitCubePinnedFiniteMeasure.unitCubeNormalizedInsertion_exact
#print axioms YMGap.Continuum.Z4UnitCubePinnedFiniteMeasure.unitCubeNormalizedInsertion_eqv
