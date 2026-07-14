/-
# Support-pruned compensated refinement paths

Compensated graph states preserve complete correlators along certified finite
refinement paths.  Their raw spectral presentations can nevertheless contain
zero-weight modes with irrelevant reciprocal-enhanced eigenvalues.  This
module applies exact support pruning to every state, proves path correlator
compatibility survives unchanged, and exposes weighted gap data as an
ordinary spectral gap of the pruned positive model.

The remaining volume-uniform task is now to transport one common weighted
gap bound along the path and then through an infinite-volume construction.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath
import YMGap.Continuum.SpectralSupportPruning

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphSupportedRefinementPath

set_option maxHeartbeats 600000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SpectralSupportPruning
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath

local infix:50 " ≈ " => Q'.eqv

/-- The positive spectral model obtained by deleting the eigenvalues of
exactly zero-weight modes from a compensated graph state. -/
def supportedGraphSpectralModel {K : Nat}
    (S : CompensatedGraphState K) : SpectralModel :=
  weightPrunedModel S.spectralModel

/-- The correlator of the support-pruned presentation. -/
def supportedGraphCorr {K : Nat}
    (S : CompensatedGraphState K) (n : Nat) : Q' :=
  SpectralGap.corr (supportedGraphSpectralModel S) n

theorem supportedGraphCorr_eq {K : Nat}
    (S : CompensatedGraphState K) (n : Nat) :
    supportedGraphCorr S n ≈ S.corr n :=
  weightPrunedModel_corr S.spectralModel n

/-- A certified move preserves the support-pruned correlator exactly. -/
theorem move_supportedGraphCorr {K : Nat}
    {S : CompensatedGraphState K} (M : IdentityRefinementMove S) (n : Nat) :
    supportedGraphCorr M.next n ≈ supportedGraphCorr S n :=
  Q'.eqv_trans _ (M.next.corr n) _
    (supportedGraphCorr_eq M.next n)
    (Q'.eqv_trans _ (S.corr n) _
      (M.next_corr n) (Q'.eqv_symm (supportedGraphCorr_eq S n)))

/-- Support-pruned correlators are invariant along every certified finite
refinement path. -/
theorem path_supportedGraphCorr_invariant {K : Nat}
    {S T : CompensatedGraphState K}
    (path : CompensatedRefinementPath S T) (n : Nat) :
    supportedGraphCorr T n ≈ supportedGraphCorr S n :=
  Q'.eqv_trans _ (T.corr n) _
    (supportedGraphCorr_eq T n)
    (Q'.eqv_trans _ (S.corr n) _
      (path.corr_invariant n) (Q'.eqv_symm (supportedGraphCorr_eq S n)))

/-- Weighted gap control on the unpruned compensated presentation. -/
def WeightedGraphGap {K : Nat}
    (S : CompensatedGraphState K) (mu : Q') : Prop :=
  WeightedSpectralGapBound S.spectralModel mu

/-- A weighted gap is an ordinary spectral gap of the support-pruned state. -/
theorem supportedGraph_gap {K : Nat}
    (S : CompensatedGraphState K) (mu : Q')
    (hmu : (0 : Q') ≤ mu) (hgap : WeightedGraphGap S mu) :
    SpectralGapBound (supportedGraphSpectralModel S) mu :=
  weightPrunedModel_gap S.spectralModel mu hmu hgap

/-- Weighted gap control yields geometric decay directly for the original
compensated correlator. -/
theorem graph_decay_of_weightedGap {K : Nat}
    (S : CompensatedGraphState K) (mu : Q')
    (hmu : (0 : Q') ≤ mu) (hgap : WeightedGraphGap S mu) (n : Nat) :
    S.corr n ≤
      (YMGap.Constructive.RationalTail.finSum
        S.spectralModel.w S.spectralModel.k) * mu ^ n :=
  decay_of_weightedSpectralGap S.spectralModel mu hmu hgap n

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphSupportedRefinementPath

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphSupportedRefinementPath.move_supportedGraphCorr
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphSupportedRefinementPath.path_supportedGraphCorr_invariant
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphSupportedRefinementPath.supportedGraph_gap
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphSupportedRefinementPath.graph_decay_of_weightedGap
