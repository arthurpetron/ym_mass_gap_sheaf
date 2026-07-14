/-
# Representative-independent staged correlators on a finite packet graph

For a fixed finite graph, character packets at different cutoffs represent
the same finite-support observable when all extended coefficients agree.
This module packages such staged graph packets and proves that every
integer-time spectral correlator is invariant under that staged equivalence.

The proof pads both representatives to their common maximum cutoff.  Exact
all-time cutoff coherence compares each representative with its padding;
coefficientwise congruence at the common stage then identifies the complete
Cartesian correlator sums.

Honest scope: cutoff representatives have been eliminated for one fixed
finite graph.  No graph-size, thermodynamic, or continuum limit is asserted.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance
import YMGap.Continuum.SU2FiniteCharacterPacketColimit

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphStagedCorrelator

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteCharacterPacketColimit
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- A family of edge packets carried at one finite character cutoff. -/
structure StagedGraphPacket where
  cutoff : Nat
  packet : Nat → CharacterPacket cutoff

/-- Two staged graph packets agree when all of their zero-extended exact
character coefficients agree, edge by edge and spin by spin. -/
def StagedGraphPacketEqv (A B : StagedGraphPacket) : Prop :=
  ∀ edge spin, coeffAt (A.packet edge) spin ≈
    coeffAt (B.packet edge) spin

theorem stagedGraphPacketEqv_refl (A : StagedGraphPacket) :
    StagedGraphPacketEqv A A :=
  fun _ _ => Q'.eqv_refl _

theorem stagedGraphPacketEqv_symm {A B : StagedGraphPacket}
    (h : StagedGraphPacketEqv A B) : StagedGraphPacketEqv B A :=
  fun edge spin => Q'.eqv_symm (h edge spin)

theorem stagedGraphPacketEqv_trans {A B C : StagedGraphPacket}
    (hAB : StagedGraphPacketEqv A B)
    (hBC : StagedGraphPacketEqv B C) : StagedGraphPacketEqv A C :=
  fun edge spin => Q'.eqv_trans _ _ _ (hAB edge spin) (hBC edge spin)

def stagedGraphPacketSetoid : Setoid StagedGraphPacket where
  r := StagedGraphPacketEqv
  iseqv := ⟨stagedGraphPacketEqv_refl, stagedGraphPacketEqv_symm,
    stagedGraphPacketEqv_trans⟩

/-- The algebraic cutoff colimit of finite-support packet families on all
edge coordinates.  A fixed graph reads only its finite edge list. -/
def GraphPacketColimit : Type := Quotient stagedGraphPacketSetoid

def stageGraphPacket {K : Nat}
    (P : Nat → CharacterPacket K) : StagedGraphPacket := ⟨K, P⟩

def includeGraphPacket {K : Nat}
    (P : Nat → CharacterPacket K) : GraphPacketColimit :=
  Quotient.mk stagedGraphPacketSetoid (stageGraphPacket P)

/-- Simultaneous cutoff padding of every edge packet is literal equality in
the graph-packet colimit. -/
theorem includeGraphPacket_pad {K L : Nat} (hKL : K ≤ L)
    (P : Nat → CharacterPacket K) :
    includeGraphPacket (fun edge => padPacket hKL (P edge)) =
      includeGraphPacket P := by
  apply Quotient.sound
  intro edge spin
  change coeffAt (padPacket hKL (P edge)) spin ≈ coeffAt (P edge) spin
  rw [coeffAt_padPacket]
  exact Q'.eqv_refl _

/-! ## Edgewise Wilson transfer on the cutoff colimit -/

def stagedGraphTransfer (A : StagedGraphPacket) : StagedGraphPacket :=
  ⟨A.cutoff, fun edge => packetTransfer (A.packet edge)⟩

theorem stagedGraphTransfer_congr {A B : StagedGraphPacket}
    (hAB : StagedGraphPacketEqv A B) :
    StagedGraphPacketEqv (stagedGraphTransfer A)
      (stagedGraphTransfer B) := by
  intro edge spin
  exact Q'.eqv_trans _
    (packetEigen spin * coeffAt (A.packet edge) spin) _
    (coeffAt_packetTransfer (A.packet edge) spin)
    (Q'.eqv_trans _
      (packetEigen spin * coeffAt (B.packet edge) spin) _
      (Q'.mul_eqv_congr_left _ _ _ (hAB edge spin))
      (Q'.eqv_symm
        (coeffAt_packetTransfer (B.packet edge) spin)))

/-- The simultaneous physical Wilson transfer on every edge packet descends
to the graph-packet cutoff colimit. -/
def colimitGraphTransfer : GraphPacketColimit → GraphPacketColimit :=
  Quotient.lift
    (fun A => Quotient.mk stagedGraphPacketSetoid (stagedGraphTransfer A))
    (fun _A _B hAB => Quotient.sound (stagedGraphTransfer_congr hAB))

theorem colimitGraphTransfer_include {K : Nat}
    (P : Nat → CharacterPacket K) :
    colimitGraphTransfer (includeGraphPacket P) =
      includeGraphPacket (fun edge => packetTransfer (P edge)) := rfl

private theorem eliminateLinks_congr
    (f g : Nat → Q') (hfg : ∀ edge, f edge ≈ g edge) :
    ∀ edges, eliminateLinks f edges ≈ eliminateLinks g edges
  | [] => Q'.eqv_refl _
  | edge :: rest =>
      q_mul_congr (hfg edge) (eliminateLinks_congr f g hfg rest)

theorem packetGraphProjectedAmplitude_congr {K : Nat}
    (edges : List Nat) (vertices : List TrivalentVertex)
    (P Q : Nat → CharacterPacket K)
    (hPQ : ∀ edge spin, coeffAt (P edge) spin ≈ coeffAt (Q edge) spin)
    (label : EdgeLabelling) :
    packetGraphProjectedAmplitude edges vertices P label ≈
      packetGraphProjectedAmplitude edges vertices Q label := by
  have hbare : packetGraphBareAmplitude edges P label ≈
      packetGraphBareAmplitude edges Q label := by
    unfold packetGraphBareAmplitude
    exact eliminateLinks_congr _ _
      (fun edge => hPQ edge (label edge)) edges
  unfold packetGraphProjectedAmplitude graphGaugeVacuumProject
  by_cases hp : GraphPhysical edges vertices label
  · rw [if_pos hp, if_pos hp]
    exact hbare
  · rw [if_neg hp, if_neg hp]
    exact Q'.eqv_refl _

theorem projectedCorrTerm_congr {K : Nat}
    (edges : List Nat) (vertices : List TrivalentVertex)
    (P Q : Nat → CharacterPacket K)
    (hPQ : ∀ edge spin, coeffAt (P edge) spin ≈ coeffAt (Q edge) spin)
    (n : Nat) (label : EdgeLabelling) :
    projectedCorrTerm edges vertices P n label ≈
      projectedCorrTerm edges vertices Q n label := by
  unfold projectedCorrTerm projectedSquare
  have ha := packetGraphProjectedAmplitude_congr
    edges vertices P Q hPQ label
  exact q_mul_congr (q_mul_congr ha ha) (Q'.eqv_refl _)

/-- At a common cutoff, coefficientwise-equivalent edge packets have the
same complete spectral correlator at every integer time. -/
theorem packetGraph_corr_congr {K : Nat}
    (edges : List Nat) (vertices : List TrivalentVertex)
    (P Q : Nat → CharacterPacket K)
    (hPQ : ∀ edge spin, coeffAt (P edge) spin ≈ coeffAt (Q edge) spin)
    (n : Nat) :
    corr (packetGraphSpectralModel edges vertices P) n ≈
      corr (packetGraphSpectralModel edges vertices Q) n := by
  exact Q'.eqv_trans _ _ _
    (packetGraph_corr_eq_full edges vertices P n)
    (Q'.eqv_trans _ _ _
      (listQSum_congr
        (projectedCorrTerm_congr edges vertices P Q hPQ n)
        (boundedEdgeLabellings K edges))
      (Q'.eqv_symm
        (packetGraph_corr_eq_full edges vertices Q n)))

/-- The correlator of a staged representative at its own cutoff. -/
def stagedGraphCorr (edges : List Nat) (vertices : List TrivalentVertex)
    (A : StagedGraphPacket) (n : Nat) : Q' :=
  corr (packetGraphSpectralModel edges vertices A.packet) n

/-- The full correlator sequence descends through staged coefficient
equivalence.  `edges.Nodup` is exactly the well-formedness condition used by
the explicit Cartesian cutoff-padding theorem. -/
theorem stagedGraphCorr_congr (edges : List Nat) (hnodup : edges.Nodup)
    (vertices : List TrivalentVertex) {A B : StagedGraphPacket}
    (hAB : StagedGraphPacketEqv A B) (n : Nat) :
    stagedGraphCorr edges vertices A n ≈
      stagedGraphCorr edges vertices B n := by
  let K := Nat.max A.cutoff B.cutoff
  have hAK : A.cutoff ≤ K := Nat.le_max_left _ _
  have hBK : B.cutoff ≤ K := Nat.le_max_right _ _
  let PA : Nat → CharacterPacket K :=
    fun edge => padPacket hAK (A.packet edge)
  let PB : Nat → CharacterPacket K :=
    fun edge => padPacket hBK (B.packet edge)
  have hpad : ∀ edge spin,
      coeffAt (PA edge) spin ≈ coeffAt (PB edge) spin := by
    intro edge spin
    unfold PA PB
    rw [coeffAt_padPacket, coeffAt_padPacket]
    exact hAB edge spin
  unfold stagedGraphCorr
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (packetGraph_corr_pad hAK edges hnodup vertices A.packet n))
    (Q'.eqv_trans _ _ _
      (packetGraph_corr_congr edges vertices PA PB hpad n)
      (packetGraph_corr_pad hBK edges hnodup vertices B.packet n))

def stagedGraphCorrQR (edges : List Nat)
    (vertices : List TrivalentVertex) (n : Nat)
    (A : StagedGraphPacket) : QR :=
  Quotient.mk qSetoid (stagedGraphCorr edges vertices A n)

/-- The representative-independent integer-time correlator on the actual
graph-packet cutoff colimit, valued in exact rationals modulo `Q'.eqv`. -/
def colimitGraphCorr (edges : List Nat) (hnodup : edges.Nodup)
    (vertices : List TrivalentVertex) (n : Nat) :
    GraphPacketColimit → QR :=
  Quotient.lift (stagedGraphCorrQR edges vertices n)
    (fun _A _B hAB => by
      unfold stagedGraphCorrQR
      exact Quotient.sound
        (stagedGraphCorr_congr edges hnodup vertices hAB n))

theorem colimitGraphCorr_include {K : Nat}
    (edges : List Nat) (hnodup : edges.Nodup)
    (vertices : List TrivalentVertex)
    (P : Nat → CharacterPacket K) (n : Nat) :
    colimitGraphCorr edges hnodup vertices n (includeGraphPacket P) =
      Quotient.mk qSetoid
        (corr (packetGraphSpectralModel edges vertices P) n) := rfl

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphStagedCorrelator

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphStagedCorrelator.stagedGraphPacketEqv_refl
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphStagedCorrelator.stagedGraphPacketEqv_trans
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphStagedCorrelator.includeGraphPacket_pad
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphStagedCorrelator.stagedGraphTransfer_congr
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphStagedCorrelator.colimitGraphTransfer
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphStagedCorrelator.colimitGraphTransfer_include
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphStagedCorrelator.packetGraphProjectedAmplitude_congr
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphStagedCorrelator.projectedCorrTerm_congr
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphStagedCorrelator.packetGraph_corr_congr
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphStagedCorrelator.stagedGraphCorr_congr
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphStagedCorrelator.colimitGraphCorr
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphStagedCorrelator.colimitGraphCorr_include
