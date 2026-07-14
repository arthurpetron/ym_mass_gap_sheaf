/-
# Operator-linked projected gap for the completed character-packet colimit

`SpectralGapData` deliberately separates a completed transfer operator from its
finite envelope model.  For the all-character packet colimit that separation is
too weak: the completed carrier contains arbitrarily high character modes.  This
module supplies the missing compatibility certificate instead of pretending the
carrier is finite dimensional.

The certificate records the actual completed linear transfer, the canonical
vacuum/excited projection, its orthogonal decomposition and commutation with the
transfer, and both the norm and quadratic-form bounds at the exact separator
`1/8`.  Thus the one-mode `SpectralModel` below is only a sharp spectral envelope;
the compatibility record is what ties that envelope to the genuine operator.

Honest scope: this is the completed one-link character sector.  No claim is made
that tensoring or gluing these projections already constructs the global vacuum
projection of a four-dimensional finite-volume lattice.
-/

import YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection

namespace YMGap.Continuum.SU2FiniteCharacterPacketColimitProjectedSpectralGap

set_option maxHeartbeats 800000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteCharacterPacketColimit
open YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS
open YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, zero_num_cast, zero_den_cast, one_num_cast,
               one_den_cast, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

private theorem fsum_le_fsum {f g : Nat → Q'}
    (h : ∀ s, f s ≤ g s) : ∀ N, fsum f N ≤ fsum g N
  | 0 => Q'.le_refl' 0
  | N + 1 => Q'.add_le_add (fsum_le_fsum h N) (h N)

/-! ## Exact quadratic-form edge at finite cutoff -/

private theorem vacuumFree_form_term_le {N : Nat}
    (P : CharacterPacket N) (h0 : coeffAt P 0 ≈ 0) (s : Nat) :
    (packetEigen s * packetEigen s) *
        (coeffAt P s * coeffAt P s) ≤
      SU2PeterWeylWilsonBlock.eighth *
        (packetEigen s * (coeffAt P s * coeffAt P s)) := by
  cases s with
  | zero =>
      rw [packetEigen_zero]
      have hc : coeffAt P 0 * coeffAt P 0 ≈ 0 :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ h0) (Q'.zero_mul_eqv _)
      have hl :
          ((1 : Q') * 1) * (coeffAt P 0 * coeffAt P 0) ≈ 0 := by
        exact Q'.eqv_trans _ (coeffAt P 0 * coeffAt P 0) _
          (Q'.one_mul_eqv _) hc
      have hr :
          SU2PeterWeylWilsonBlock.eighth *
              ((1 : Q') * (coeffAt P 0 * coeffAt P 0)) ≈ 0 := by
        refine Q'.eqv_trans _
          (SU2PeterWeylWilsonBlock.eighth *
            (coeffAt P 0 * coeffAt P 0)) _ ?_ ?_
        · exact Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv _)
        · exact Q'.eqv_trans _
            (SU2PeterWeylWilsonBlock.eighth * 0) _
            (Q'.mul_eqv_congr_left _ _ _ hc)
            (Q'.mul_zero_eqv _)
      exact Q'.le_trans' _ 0 _ (Q'.le_of_eqv hl)
        (Q'.le_of_eqv (Q'.eqv_symm hr))
  | succ k =>
      let lam := packetEigen (k + 1)
      let c := coeffAt P (k + 1)
      let base := lam * (c * c)
      have hbase : (0 : Q') ≤ base :=
        Q'.mul_nonneg _ _ (packetEigen_nonneg (k + 1))
          (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg c)
      have hlam : lam ≤ SU2PeterWeylWilsonBlock.eighth :=
        packetEigen_excited_le_eighth (by omega)
      have hm := Q'.mul_le_mul_of_nonneg_right _ _ base hlam hbase
      dsimp [lam, c, base] at hm ⊢
      refine Q'.le_trans' _
        (packetEigen (k + 1) *
          (packetEigen (k + 1) *
            (coeffAt P (k + 1) * coeffAt P (k + 1)))) _
        (Q'.le_of_eqv (by ring_qeqv)) ?_
      exact hm

private theorem packetVacuumFree_form_edge {N : Nat}
    (P : CharacterPacket N) (h0 : coeffAt P 0 ≈ 0) :
    packetWilsonGram (packetTransfer P) P ≤
      SU2PeterWeylWilsonBlock.eighth * packetWilsonGram P P := by
  refine le_of_eqv_le (packet_same_state_compression P P) ?_
  refine Q'.le_trans' _
    (fsum (fun s => SU2PeterWeylWilsonBlock.eighth *
      (packetEigen s * (coeffAt P s * coeffAt P s))) (N + 1)) _
    (fsum_le_fsum (vacuumFree_form_term_le P h0) (N + 1)) ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _
    (SU2PeterWeylWilsonBlock.eighth *
      fsum (fun s => packetEigen s *
        (coeffAt P s * coeffAt P s)) (N + 1)) _
    (Q'.eqv_symm (CubeRatioBounds.fsum_const_mul _ _ _)) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_symm (packetWilsonGram_diagonal P P))

/-- The exact `1/8` quadratic-form edge on every vacuum-free staged packet. -/
theorem stagedVacuumFree_form_edge (A : StagedPacket)
    (hA : StagedVacuumFree A) :
    stagedGram (stagedTransfer A) A ≤
      stagedGram
        (stagedSmul SU2PeterWeylWilsonBlock.eighth A) A := by
  have hrefl : A.cutoff ≤ A.cutoff := Nat.le_refl _
  have hleft : stagedGram (stagedTransfer A) A ≈
      packetWilsonGram
        (packetTransfer (padPacket hrefl A.packet))
        (padPacket hrefl A.packet) := by
    refine Q'.eqv_trans _
      (packetWilsonGram
        (padPacket hrefl (stagedTransfer A).packet)
        (padPacket hrefl A.packet)) _
      (stagedGram_pad_to (stagedTransfer A) A hrefl hrefl) ?_
    exact packetWilsonGram_congr
      (by simpa only [stagedTransfer] using
        padPacket_transfer hrefl A.packet)
      (fun _ => Q'.eqv_refl _)
  have hpad0 : coeffAt (padPacket hrefl A.packet) 0 ≈ 0 := by
    simpa only [coeffAt_padPacket] using hA
  refine le_of_eqv_le hleft ?_
  refine Q'.le_trans' _
    (SU2PeterWeylWilsonBlock.eighth *
      packetWilsonGram (padPacket hrefl A.packet)
        (padPacket hrefl A.packet)) _
    (packetVacuumFree_form_edge (padPacket hrefl A.packet) hpad0) ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _
    (SU2PeterWeylWilsonBlock.eighth * stagedGram A A) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (stagedGram_pad_to A A hrefl hrefl))) ?_
  exact Q'.eqv_symm
    (stagedGram_smul_left SU2PeterWeylWilsonBlock.eighth A A)

/-! ## Descent of the form edge through the explicit completion -/

theorem cinnerRep_vacuumFree_form_edge
    (x : CauchyGNS packetColimitGNS)
    (hx : ∀ n, StagedVacuumFree (x.seq n)) :
    CReal.leEv
      (packetColimitGNS.cinnerRep
        (packetColimitDiagonalSymbol.cDiagCauchy x) x)
      (packetColimitGNS.cinnerRep
        (packetColimitSmulGNS.cSmulCauchy
          SU2PeterWeylWilsonBlock.eighth x) x) := by
  refine CReal.leEv_of_ofQ'_limit_le
    (CReal.convergesTo_ofQ'CauchySeq _ _)
    (CReal.convergesTo_ofQ'CauchySeq _ _) ?_
  intro epsilon hepsilon
  exact ⟨0, fun n _ => Q'.le_trans' _ _ _
    (stagedVacuumFree_form_edge (x.seq n) (hx n))
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))⟩

/-- Canonical projected quadratic-form gap for every completed vector. -/
theorem completedPacketTransfer_projected_form_edge
    (x : GNSCompletionSpace packetColimitGNS) :
    CReal.RCle
      (packetColimitGNS.cinnerCompl
        (completedPacketTransfer (completedRemoveVacuum x))
        (completedRemoveVacuum x))
      (packetColimitGNS.cinnerCompl
        (packetColimitSmulGNS.cSmul SU2PeterWeylWilsonBlock.eighth
          (completedRemoveVacuum x))
        (completedRemoveVacuum x)) := by
  refine Quotient.inductionOn x ?_
  intro u
  exact cinnerRep_vacuumFree_form_edge
    (removeVacuumSymbol.cDiagCauchy u)
    (fun n => stagedRemoveVacuum_vacuumFree (u.seq n))

/-! ## A sharp finite envelope tied to the actual completed operator -/

/-- One envelope mode at the sharp excited edge `1/8`. -/
def packetProjectedEnvelopeModel : SpectralModel where
  k := 1
  w := fun _ => 1
  lam := fun _ => SU2PeterWeylWilsonBlock.eighth
  w_nonneg := fun _ => by decide
  lam_nonneg := fun _ => by decide

def packetProjectedLocatedGap :
    LocatedSpectralGap packetProjectedEnvelopeModel where
  sep := SU2PeterWeylWilsonBlock.eighth
  sep_lt_one := SU2PeterWeylWilsonBlock.eighth_strict_window.2
  bound := fun _ => Q'.le_refl' _

/-- The envelope uses the actual completed physical packet transfer. -/
def packetProjectedSpectralGapData :
    SpectralGapData packetColimitGNS.gnsComplete where
  op := completedPacketLinearTransfer.toTransferOperator
  model := packetProjectedEnvelopeModel
  gap := packetProjectedLocatedGap

/-- Compatibility missing from bare `SpectralGapData`: an explicit orthogonal
projection onto the excited range, linked to the operator and its separator by
both norm and quadratic-form estimates. -/
structure OrthogonalProjectionGapCompatibility (D : SmulGNSData)
    (G : SpectralGapData D.toGNSData.gnsComplete) : Type where
  projection : GNSCompletionSpace D.toGNSData → GNSCompletionSpace D.toGNSData
  complement : GNSCompletionSpace D.toGNSData → GNSCompletionSpace D.toGNSData
  idempotent : ∀ x, projection (projection x) = projection x
  commutes : ∀ x, G.op.T (projection x) = projection (G.op.T x)
  vacuum_killed : projection G.op.vacuum = embedV D.toGNSData D.toGNSData.zero
  complement_fixed : ∀ x, G.op.T (complement x) = complement x
  decomposition : ∀ x,
    D.toGNSData.cAdd (complement x) (projection x) = x
  orthogonal : ∀ x,
    D.toGNSData.cinnerCompl (complement x) (projection x) = CReal.RCzero
  projected_norm_gap : ∀ x,
    CReal.RCle
      (D.toGNSData.cinnerCompl (G.op.T (projection x))
        (G.op.T (projection x)))
      (D.toGNSData.cinnerCompl (D.cSmul G.gap.sep (projection x))
        (D.cSmul G.gap.sep (projection x)))
  projected_form_gap : ∀ x,
    CReal.RCle
      (D.toGNSData.cinnerCompl (G.op.T (projection x)) (projection x))
      (D.toGNSData.cinnerCompl (D.cSmul G.gap.sep (projection x))
        (projection x))

/-- The complete operator/model/projection compatibility certificate for the
all-character packet colimit. -/
def packetProjectedGapCompatibility :
    OrthogonalProjectionGapCompatibility packetColimitSmulGNS
      packetProjectedSpectralGapData where
  projection := completedRemoveVacuum
  complement := completedKeepVacuum
  idempotent := completedRemoveVacuum_idempotent
  commutes := completedRemoveVacuum_transfer_commute
  vacuum_killed := completedRemoveVacuum_vacuum
  complement_fixed := completedKeepVacuum_fixed
  decomposition := completedKeep_add_remove
  orthogonal := completedKeep_remove_orthogonal
  projected_norm_gap := completedPacketTransfer_projected_edge
  projected_form_gap := completedPacketTransfer_projected_form_edge

theorem packetProjected_gapMargin_pos :
    (0 : Q') < packetProjectedSpectralGapData.massGap :=
  packetProjectedSpectralGapData.massGap_pos

end YMGap.Continuum.SU2FiniteCharacterPacketColimitProjectedSpectralGap

#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitProjectedSpectralGap.stagedVacuumFree_form_edge
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitProjectedSpectralGap.cinnerRep_vacuumFree_form_edge
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitProjectedSpectralGap.completedPacketTransfer_projected_form_edge
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitProjectedSpectralGap.packetProjectedLocatedGap
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitProjectedSpectralGap.packetProjectedSpectralGapData
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitProjectedSpectralGap.packetProjectedGapCompatibility
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitProjectedSpectralGap.packetProjected_gapMargin_pos
